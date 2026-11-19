// rig-responder v1.10 — board B (ESP32-S3-DevKitC-1) multi-protocol responder.
//
// v1.10: WRITE-SP ROOT CAUSE FIXED — dwDispatch() never cleared the s_cmd
// accumulator, so each received byte was ORed into the previous byte
// (0xCC|0x0F=0xCF, then monotonically to 0xFF). Only the first byte after
// presence was ever correct. The DQ waveform + per-bit cb samples proved
// B's bit sampling was always correct; the fault was post-sample assembly.
// Also: s_matchRom now cleared on 0x55 (same stale-accumulator class).
//
// Protocols (all non-blocking, one loop):
//   UART1  RX=4  TX=15  @115200  PING->PONG x10, others->ECHO:<line> x3, "GPIO"->mirror
//   I2C    SDA=8 SCL=9  slave @0x50, 16-byte register file (pointer protocol)
//   1-Wire DQ=11        open-drain slave (raw-register pull/release, ISR-safe)
//   GPIO   MIRROR_IN=10 (A GPIO4 wire) -> MIRROR_OUT=15 (A GPIO44 wire)
//
// v1.6 changes (vs v1.5):
//  - I2C: Wire.begin(addr, sda, scl, freq) — the 4-arg SLAVE form. v1.5 used
//    Wire.begin(sda, scl) which is the MASTER form: B never was a slave, so
//    board A's scan/ping saw an empty bus.
//  - 1-Wire open drain via raw registers (ISR-safe, no pinMode in ISR):
//      dwPull()    = OUTEN=1 (enable_w1ts) + data 0 (out_w1tc)
//      dwRelease() = OUTEN=0 (enable_w1tc) -> line floats, pull-up raises it
//  - Presence: B pulls the moment it sees the master release the reset
//    (OneWire lib: 480us low, sample at +70us after release). v1.5 waited
//    80us after detection -> missed the sample. Hold 100us (spec 60-120us).
//  - Read bits are driven FROM THE ISR: the master pulses low only 3us and
//    samples at +13us, so main-loop latency (tens of us) is too slow.
//    The ISR pulls immediately for a 0 bit; the main loop releases at +25us.
//  - 0x55 match flow: 64 ROM write slots -> 64 ROM read slots (v1.5 went to
//    the command phase and decoded read slots as writes).
//  - AUDIT: single summary line "AUDIT end: p4=N p8=N p9=N p10=N p11=N p15=N".
//
// B console: UART0 via CH340 (/dev/ttyACM1), 115200. No USB-CDC.

#include <Arduino.h>
#include <Wire.h>
#include "driver/gpio.h"
#include "freertos/FreeRTOS.h"
#include "freertos/task.h"
#include "soc/gpio_struct.h"
#include "soc/interrupts.h"
#include "hal/gpio_ll.h"

// ---- pin / address constants ----
static const uint8_t U1_RX = 4;
static const uint8_t U1_TX = 15;
static const uint8_t I2C_SDA = 8;
static const uint8_t I2C_SCL = 9;
static const uint8_t DW_PIN = 11;
static const uint8_t MIRROR_IN = 10;
static const uint8_t MIRROR_OUT = 15;
static const uint8_t SLAVE_ADDR = 0x50;

// ---- shared state ----
static HardwareSerial u1(1);
static uint8_t regs[16];            // I2C register file
static uint8_t s_regPtr = 0;        // I2C register pointer
static bool s_mirror = false;       // mirror mode active (UART1 ended)
static bool s_square = false;       // 1 kHz square wave on MIRROR_OUT (GPIO)
static uint32_t s_sqLast = 0;       // micros() of last square toggle
static bool s_sqHi = false;         // current square half-cycle state
static unsigned long s_lastT = 0;   // last mirror transition (ms)
static uint8_t s_rom[8] = {0x28, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x00};
static uint8_t s_spad[9] = {0x80, 0x00, 0x0F, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00};

// ---- deferred logging (no printf in ISR / 1-Wire hot path) ----
static char s_logBuf[300];
static int s_logLen = 0;
static void logAppend(const char* s) {
  while (*s && s_logLen < 290) s_logBuf[s_logLen++] = *s++;
  if (s_logLen < 295) s_logBuf[s_logLen++] = '\n';
}
static void logHex(uint8_t b) {
  static const char* hx = "0123456789ABCDEF";
  if (s_logLen < 293) { s_logBuf[s_logLen++] = hx[b >> 4]; s_logBuf[s_logLen++] = hx[b & 0x0F]; }
}
static void logUint(uint32_t v) {
  char t[12]; int n = 0;
  if (!v) t[n++] = '0';
  while (v && n < 11) { t[n++] = (char)('0' + (v % 10)); v /= 10; }
  while (n--) if (s_logLen < 294) s_logBuf[s_logLen++] = t[n];
}

// ---- ISR-safe diagnostic ring (dumped via console "DUMP") ----
static char s_diag[16384];
static volatile int s_diagLen = 0;
static inline void diag(const char* s) {
  while (*s && s_diagLen < 16360) s_diag[s_diagLen++] = *s++;
}
static inline void diagU(uint32_t v) {
  char t[12]; int n = 0;
  if (!v) t[n++] = '0';
  while (v && n < 11) { t[n++] = (char)('0' + (v % 10)); v /= 10; }
  while (n--) if (s_diagLen < 16370) s_diag[s_diagLen++] = t[n];
}

// ---- DQ waveform capture (Core-1 task, main loop stays free) ----
static volatile uint32_t s_probeUs = 0;
static volatile bool s_probeActive = false;
static volatile bool s_probeDone = false;
static volatile uint32_t s_irqTicks; // fwd (defined with 1-Wire state)
static volatile uint32_t s_isrIgnored = 0; // edges ignored because B was driving (OUTEN=1)
static volatile uint32_t s_mainTicks; // main-loop heartbeat (defined below)
static volatile uint32_t s_loopStage; // loop() milestone (0..7), for probe diag
static volatile uint32_t s_mainCore;  // core of the loop task (set in loop)
// dedicated DQ waveform buffer (separate from the 16KB diag ring so the
// probe's transitions don't compete with the per-bit cb markers). Each
// transition = 3 bytes: time_lo, time_hi (16-bit us offset), level (0/1).
static uint8_t s_wf[6144];
static volatile uint16_t s_wfLen = 0;   // number of transitions stored
static void dqProbeTask(void*) {
  uint32_t t0 = micros();
  uint32_t nowUs = 0;
  uint32_t iters = 0;
  bool last = ((GPIO.in >> DW_PIN) & 1) != 0;
  s_wfLen = 1;
  s_wf[0] = 0; s_wf[1] = 0; s_wf[2] = (uint8_t)(last ? 1 : 0);  // t=0 initial level
  diag("W0 ");
  diag(last ? "H" : "L");
  diag(" pc=");
  diagU((uint32_t)xTaskGetCoreID(xTaskGetCurrentTaskHandle()));
  diag(" lp=");
  diagU((uint32_t)uxTaskGetStackHighWaterMark(NULL));
  while (nowUs < s_probeUs) {
    nowUs = micros() - t0;
    bool lvl = ((GPIO.in >> DW_PIN) & 1) != 0;
    iters++;
    if (lvl != last) {
      last = lvl;
      if (s_wfLen < 2048) {
        uint32_t t = nowUs > 60000 ? 60000 : nowUs;
        s_wf[s_wfLen * 3]     = (uint8_t)(t & 0xFF);
        s_wf[s_wfLen * 3 + 1] = (uint8_t)((t >> 8) & 0xFF);
        s_wf[s_wfLen * 3 + 2] = (uint8_t)(lvl ? 1 : 0);
        s_wfLen++;
      }
      diag("W");
      diagU(nowUs);
      diag(" ");
      diag(lvl ? "H" : "L");
    }
    // heartbeat: every ~1ms record the ISR tick counter (low frequency so a
    // long capture doesn't overflow the 16KB diag ring)
    if ((iters % 10000) == 9999) {
      diag("T");
      diagU(nowUs);
      diag(" ");
      diagU(s_irqTicks);
      diag(",");
      diagU(s_mainTicks);
      diag(" st");
      diagU(s_loopStage);
      diag(" mc");
      diagU(s_mainCore);
    }
  }
  diag(" Wand iters=");
  diagU(iters);
  diag(" ticks=");
  diagU(s_irqTicks);
  diag(" mt=");
  diagU(s_mainTicks);
  s_probeActive = false;
  s_probeDone = true;
  vTaskDelete(NULL);
}

// ---- 1-Wire pin: raw-register open drain (ISR-safe) ----
static inline void dwPull() {
  GPIO.enable_w1ts = (1u << DW_PIN);   // OUTEN = 1
  GPIO.out_w1tc   = (1u << DW_PIN);    // output data 0 (atomic)
}
static inline void dwRelease() {
  GPIO.enable_w1tc = (1u << DW_PIN);   // OUTEN = 0 -> floats, pull-up raises
}
static inline int dwLevel() {
  return (int)((GPIO.in >> DW_PIN) & 1u);
}

// fwd: defined further down (used by the SPWRITE case before setup)
static uint8_t crc8(const uint8_t* d, uint8_t n);

// ---- 1-Wire slave state machine (v1.8: A's actual command semantics) ----
// A's flows (OneWireController + lib OneWire v2.3.8):
//   ping   : reset -> presence
//   read   : reset -> 0x33 -> read 8 (ROM) ; reset -> 0xAA -> read 8 (scratchpad)
//   scan   : reset -> 0xF0 -> 64 x (read, read, write)   [normal search + defeat]
//   write sp: reset -> 0xCC -> 0x0F -> write 8 ; verify via 0xAA readback
// Slot timing (master side):
//   reset  : 480us low, release, presence sample @ +70us after release
//   write  : bit1 = 10us low + release; bit0 = 65us low. We sample @ +20us.
//   read   : 3us low pulse then tri-state; A samples @ +13us -> 0 bits are
//            pulled by the ISR, released by the main loop 25us after slot start.
enum DWState { DW_IDLE = 0, DW_RESET_WAIT, DW_PRESENCE, DW_CMD,
               DW_ROMWRITE, DW_SPWRITE, DW_OUT, DW_SEARCH };
static volatile int s_state = DW_IDLE;
static volatile uint32_t s_fallUs = 0;    // micros() of last falling edge (ISR)
static volatile bool s_fallPend = false;
static volatile bool s_readPull = false;  // ISR is currently driving a read-0 bit
static volatile uint32_t s_readPullUs = 0;
static volatile uint32_t s_slotStart = 0;
static volatile bool s_inSlot = false;
static uint32_t s_presenceT0 = 0;
static volatile uint32_t s_resetReleaseUs = 0;  // micros() of last reset release (presence window)
static volatile uint32_t s_isrGlitch = 0;       // glitch falling edges ignored in presence window
static uint8_t s_cmd = 0;
static uint8_t s_cmdBits = 0;
static uint8_t s_matchRom[8];
static uint32_t s_matchBits = 0;
static uint8_t s_spwBytes[8];
static uint32_t s_spwBits = 0;
static uint8_t s_outCmd = 0;             // 0x33 / 0xAA / 0xBE
static volatile uint32_t s_outPos = 0;   // bit position in current read run
static uint32_t s_outTotal = 0;
static volatile uint32_t s_searchPos = 0;
static volatile bool s_searchMatched = true;
static volatile uint8_t s_searchPhase = 0;   // 0=read1 1=read2 2=write
static volatile bool s_writeEdge = false;    // set by ISR on the write-slot falling edge

static inline bool dwRomBit(uint32_t pos) {
  return (s_rom[pos / 8] >> (pos % 8)) & 0x01;
}

// bit to drive at position pos of the current DW_OUT run
static bool dwOutBit(uint32_t pos) {
  uint32_t byteIdx = pos / 8;
  uint8_t b;
  if (s_outCmd == 0xBE) b = s_spad[byteIdx];      // scratchpad (9 bytes)
  else if (s_outCmd == 0xAA) b = s_spad[byteIdx]; // scratchpad (8 bytes)
  else b = s_rom[byteIdx];                        // 0x33: ROM read
  return (b >> (pos % 8)) & 0x01;
}

static void dwDispatch(uint8_t cmd) {
  logAppend("DW cmd="); logHex(cmd);
  diag("c="); diagU(cmd); diag(" ");
  s_inSlot = false;
  s_fallPend = false;
  s_cmd = 0;   // v1.10: clear accumulator — v1.9 ORed each byte into the
               // previous byte's value (0xCC|0x0F=0xCF ... -> 0xFF), so
               // only the first byte after presence was ever correct.
  switch (cmd) {
    case 0x33: s_outCmd = 0x33; s_outPos = 0; s_outTotal = 64; s_state = DW_OUT; break; // read ROM
    case 0xAA: s_outCmd = 0xAA; s_outPos = 0; s_outTotal = 64; s_state = DW_OUT; break; // read scratchpad
    case 0xBE: s_outCmd = 0xBE; s_outPos = 0; s_outTotal = 72; s_state = DW_OUT; break; // read scratchpad 9
    case 0xCC: logAppend("DW cc"); s_state = DW_CMD; break;    // skip ROM: function command follows
    case 0x44: s_state = DW_CMD; break;    // convert: no data
    case 0x55: s_matchBits = 0; memset(s_matchRom, 0, sizeof s_matchRom); s_state = DW_ROMWRITE; break;  // match ROM: 8 bytes follow
    case 0x0F: logAppend("DW 0f"); s_spwBits = 0; s_state = DW_SPWRITE; break;     // write scratchpad: 8 bytes follow
    case 0xF0:
    case 0xF5:
      s_searchPos = 0; s_searchMatched = true; s_searchPhase = 0; s_writeEdge = false;
      s_state = DW_SEARCH; break;
    default:   s_state = DW_CMD; break;    // unknown: expect next command byte
  }
  // diagnostic: auto-start the DQ waveform probe at the start of every
  // search (captures the full 64-pair exchange on Core 0, main loop free).
  // NOTE: must be Core 0 — this framework runs the user loop on Core 1,
  // and a priority-2 probe on Core 1 starved the priority-1 loop task
  // for the whole probe window (v1.9 freeze: mt fixed, st=4).
  if ((cmd == 0xF0 || cmd == 0x33) && !s_probeActive) {
    s_probeUs = 60000;
    s_probeActive = true;
    s_probeDone = false;
    xTaskCreatePinnedToCore(dqProbeTask, "dqprobe", 2048, NULL, 2, NULL, 0);
  }
}

// Global GPIO ISR: raw ETS_GPIO_INTR_SOURCE wiring (driver bypass, v1.7+).
// S3 edge interrupts latch in pcpu_int until cleared.
// v1.9: MINIMAL ISR — the read-0 pull happens FIRST (latency-critical:
// A samples @ +13us after its 3us pulse; every us of ISR work before the
// pull risks a missed sample). No string ops, no diag/logAppend: those
// add microseconds and race with other writers of the diag buffer.
// s_irqTicks heartbeat defined in the probe section (fwd declaration there)
static volatile uint32_t s_lastDt = 0;     // dt of last falling edge (us)
void IRAM_ATTR dwGpioIsr(void *arg) {
  (void)arg;
  if (!(GPIO.pcpu_int & (1u << DW_PIN))) return;
  GPIO.status_w1tc = (1u << DW_PIN);
  s_irqTicks++;
  // Ignore edges caused by B's own pulls (presence / read-0 bits): while
  // B drives the line (OUTEN=1) the falling edge is B's own action.
  if ((GPIO.enable & (1u << DW_PIN)) != 0) { s_isrIgnored++; return; }
  uint32_t now = (uint32_t)micros();
  // Ignore glitch falling edges in the post-reset presence window: no valid
  // command slot can start within ~150us of the reset release (A samples
  // presence @ +70us). A spurious edge here (observed ~3us after release,
  // a 100us L-pulse) was sampled as a data bit and shifted the byte
  // assembly by one position (0x0F -> 0xCF).
  if (s_resetReleaseUs && (int32_t)(now - s_resetReleaseUs) < 150) { s_isrGlitch++; return; }
  // 1) drive read-0 bits / search read pairs NOW (latency-critical)
  if (s_state == DW_OUT) {
    if (s_outPos < s_outTotal && !dwOutBit(s_outPos)) {
      dwPull();
      s_readPull = true;
      s_readPullUs = now;
    }
    s_outPos++;
  } else if (s_state == DW_SEARCH && s_searchPhase != 2) {
    bool bitOut;
    if (s_searchPhase == 0) {        // read1: ROM bit (or 1 when defeated)
      bitOut = s_searchMatched ? dwRomBit(s_searchPos) : true;
    } else {                         // read2: complement (or 1 when defeated)
      bitOut = s_searchMatched ? !dwRomBit(s_searchPos) : true;
    }
    if (!bitOut) {
      dwPull();
      s_readPull = true;
      s_readPullUs = now;
    }
    s_searchPhase++;
  } else if (s_state == DW_SEARCH && s_searchPhase == 2) {
    // write slot falling edge: the main loop may now sample @ +20us.
    // (s_slotStart is set to this edge in the bookkeeping below.)
    s_writeEdge = true;
  }
  // 2) bookkeeping (not latency-critical)
  s_lastDt = now - s_fallUs;
  s_fallUs = now;
  s_slotStart = now;
  s_fallPend = true;
  s_inSlot = true;
}

static void flushLog() {
  if (s_logLen == 0) return;
  // v1.13: flush in small chunks (<=32 B ~= 2.7 ms at 115200) instead of the
  // whole 300-char buffer (26 ms block). A whole-buffer flush during a
  // 1-Wire retry storm starved loop(): the square degraded to ~20-50 Hz and
  // mirror transitions fell through the poll window. Chunking caps the
  // block at 2.7 ms and keeps it out of 1-Wire windows via the idle guard.
  if (s_state == DW_IDLE && !s_readPull && (uint32_t)micros() - s_fallUs > 2000) {
    int n = s_logLen < 32 ? s_logLen : 32;
    Serial.write((const uint8_t*)s_logBuf, n);
    memmove(s_logBuf, s_logBuf + n, (size_t)(s_logLen - n));
    s_logLen -= n;
  }
}

// non-blocking slave loop; main loop period is a few us at 240 MHz
static volatile uint32_t s_lastTicks = 0;
static volatile uint32_t s_lastTickTime = 0;
static volatile uint32_t s_lastStaleLog = 0;  // v1.12 stale-recovery log rate limit
static volatile uint32_t s_lastDeadLog = 0;   // v1.12 dead-ISR log rate limit
static volatile uint32_t s_lastStuckLog = 0;  // v1.14 stuck-LOW reset log rate limit
static void dwSlavePoll() {
  // v1.9 fix: the ISR timestamps edges with a FRESH micros(); the main
  // loop's stale `now` (captured before the ISR ran) can be a few us BEHIND
  // those timestamps, and now - stamp then underflows uint32 to ~4e9 —
  // making every "elapsed >= N" check true instantly (premature pull
  // release, spurious reset fires). Each check therefore re-captures now
  // and compares SIGNED (a few us in the future -> negative -> safe).

  // release a read-0 pull 25us after the slot start (A samples @ +13us)
  {
    uint32_t now = (uint32_t)micros();
    if (s_readPull && (int32_t)(now - s_readPullUs) >= 25) {
      s_readPull = false;
      dwRelease();
    }
  }

  // diagnostic: ISR heartbeat (detects a dead GPIO interrupt)
  {
    uint32_t now = (uint32_t)micros();
    if (s_irqTicks != s_lastTicks) {
      s_lastTicks = s_irqTicks;
      s_lastTickTime = now;
    } else if (s_state != DW_IDLE) {
      if (now - s_lastTickTime > 5000) {
        // Stale transaction: no DQ edges for 5 ms while the state machine
        // is active. A real exchange never has that gap (bit slots 65 us,
        // reset 480 us), so force back to idle: a reset is the only way a
        // transaction starts, so this cannot disturb an in-flight one.
        // (v1.12: the 500 us watchdog alone appended a log line every
        // 500 us; the 300-char buffer filled and flushLog blocked loop()
        // ~26 ms at a time — the 1 kHz square degraded to ~20 Hz, 1-Wire
        // write-slot samples were missed (1-bit misreads), and mirror
        // transitions fell through the poll window.)
        s_state = DW_IDLE;
        s_inSlot = false;
        s_fallPend = false;
        if (now - s_lastStaleLog > 100000) {
          logAppend("DW STALE->IDLE ticks="); logUint(s_irqTicks);
          s_lastStaleLog = now;
        }
      } else if (now - s_lastTickTime > 500 && now - s_lastDeadLog > 100000) {
        // Genuine mid-transaction ISR stall: log, but rate-limit to
        // 100 ms so logging can never starve the loop again.
        logAppend("DW IRQ DEAD ticks="); logUint(s_irqTicks);
        s_lastDeadLog = now;
      }
    }
  }

  // Reset detection (v1.9): any falling edge starts a LOW period. Write
  // slots are <= 65us low, read slots ~3us. A valid reset is >= 480us low,
  // but A releases at exactly 480us so a >=480us check races the release.
  // The old >100us threshold tripped on the ~100us stray low pulse A emits
  // 3us after the reset release — B treated it as a second reset and issued
  // a spurious presence, shifting every subsequent byte by one bit
  // (0x0F -> 0xCF). 300us sits safely in the dead band: well above the
  // stray pulse, well below the reset release, so it fires reliably while
  // the line is still LOW.
  {
    uint32_t now = (uint32_t)micros();
    if ((s_state == DW_IDLE || s_state == DW_CMD || s_state == DW_ROMWRITE ||
         s_state == DW_SPWRITE || s_state == DW_OUT || s_state == DW_SEARCH) &&
        (int32_t)(now - s_fallUs) >= 300 && dwLevel() == LOW) {
      // v1.14: a stuck-LOW line (last real edge >10ms ago — e.g. A left
      // DQ driven low: DIO 'set' + 'mode hiz' does not release pins)
      // re-fired this block every loop pass. The 300-char log buffer ran
      // permanently full and dropped every other log line (SQUARE/MODE/
      // AUDIT/STOP) while loop() slowed to ~10ms (1 kHz square degraded
      // to ~48 Hz). Rate-limit the stuck case to one line per 200ms.
      bool stuck = s_lastDt > 10000;
      if (!stuck || (int32_t)(now - s_lastStuckLog) >= 200000) {
        if (stuck) s_lastStuckLog = now;
        bool outen = ((GPIO.enable & (1u << DW_PIN)) != 0);
        logAppend("DW reset s="); logUint((uint32_t)s_state);
        logAppend(" dt="); logUint(s_lastDt);
        logAppend(" out="); logUint(outen ? 1 : 0);
        logAppend(" pull="); logUint(s_readPull ? 1 : 0);
        logAppend(" age="); logUint(s_readPull ? now - s_readPullUs : 0);
        diag("F s="); diagU((uint32_t)s_state); diag(" dt="); diagU(s_lastDt);
        diag(" o"); diagU(outen ? 1 : 0); diag(" p"); diagU(s_readPull ? 1 : 0);
        diag(" a"); diagU(s_readPull ? now - s_readPullUs : 0); diag(" ");
      }
      s_inSlot = false;
      s_readPull = false;
      s_writeEdge = false;
      dwRelease();
      s_state = DW_RESET_WAIT;
      s_slotStart = s_fallUs;
    }
  }

  // one fresh timestamp for the state machine; ISR-derived comparisons
  // (s_slotStart) use signed math to survive a few-us-future ISR stamp.
  uint32_t now = (uint32_t)micros();
  switch (s_state) {
    case DW_IDLE: {
      if (s_fallPend) {
        s_fallPend = false;
        s_slotStart = s_fallUs;
        s_inSlot = true;
        s_state = DW_RESET_WAIT;   // a reset is the only thing that starts from idle
      }
      break;
    }
    case DW_RESET_WAIT: {
      // Master drives low 480us then releases; presence must start as soon
      // as we see the release (A samples at +70us after release).
      if (dwLevel() == HIGH) {
        s_inSlot = false;
        dwPull();
        s_presenceT0 = now;
        s_resetReleaseUs = now;   // presence window opens (glitch filter)
        logAppend("DW presence");
        diag("P ");
        s_state = DW_PRESENCE;
      } else if ((int32_t)(now - s_slotStart) > 5000) {
        s_inSlot = false;
        s_state = DW_IDLE;         // line stuck low / no master
      }
      break;
    }
    case DW_PRESENCE: {
      // hold ~100us (spec 60-120us); A's sample at +70us lands inside it
      if (now - s_presenceT0 >= 100) {
        dwRelease();
        s_state = DW_CMD;
        s_cmd = 0; s_cmdBits = 0; s_inSlot = false; s_fallPend = false;
        s_resetReleaseUs = 0;     // presence window closed
      }
      break;
    }
    case DW_CMD: {
      // write_bit: bit1 = 10us low + release; bit0 = 65us low. Sample @ +20us.
      if (s_fallPend) { s_fallPend = false; s_slotStart = s_fallUs; s_inSlot = true; }
      if (s_inSlot && (int32_t)(now - s_slotStart) >= 20) {
        uint32_t el = (int32_t)(now - s_slotStart) < 0 ? 0xFFFFFFFFu : (uint32_t)(now - s_slotStart);
        bool outen = ((GPIO.enable & (1u << DW_PIN)) != 0);
        s_cmd |= (uint8_t)(dwLevel() == HIGH ? 1 : 0) << s_cmdBits;
        s_cmdBits++;
        s_inSlot = false;
        diag("cb"); diagU(s_cmdBits - 1); diag(" e="); diagU(el); diag(" o="); diagU(outen ? 1 : 0); diag(" i="); diagU(s_isrIgnored); diag("|");
        if (s_cmdBits >= 8) { s_cmdBits = 0; dwDispatch(s_cmd); }
      }
      break;
    }
    case DW_ROMWRITE: {
      // 0x55: master writes 8 ROM bytes (64 write slots)
      if (s_fallPend) { s_fallPend = false; s_slotStart = s_fallUs; s_inSlot = true; }
      if (s_inSlot && (int32_t)(now - s_slotStart) >= 20) {
        s_matchRom[s_matchBits / 8] |= (uint8_t)((dwLevel() == HIGH ? 1 : 0) << (s_matchBits % 8));
        s_matchBits++;
        s_inSlot = false;
        if (s_matchBits >= 64) {
          bool ok = (memcmp(s_matchRom, s_rom, 8) == 0);
          logAppend(ok ? "DW matchROM OK" : "DW matchROM no-match");
          s_state = ok ? DW_CMD : DW_IDLE;  // matched: function follows; else silent
        }
      }
      break;
    }
    case DW_SPWRITE: {
      // 0x0F: master writes 8 scratchpad bytes (64 write slots).
      // A verifies an EXACT readback of all 8 bytes (0xAA), so store
      // verbatim; only byte 8 (0xBE scratchpad CRC) is recomputed.
      if (s_fallPend) { s_fallPend = false; s_slotStart = s_fallUs; s_inSlot = true; }
      if (s_inSlot && (int32_t)(now - s_slotStart) >= 30) {
        s_spwBytes[s_spwBits / 8] |= (uint8_t)((dwLevel() == HIGH ? 1 : 0) << (s_spwBits % 8));
        s_spwBits++;
        s_inSlot = false;
        if (s_spwBits > 0 && (s_spwBits % 8) == 0) {
          // v1.13: per-byte detail goes to the diag ring only — logging all
          // 8 bytes to the 300-char console buffer during a retry storm
          // kept the buffer full and made flushLog starve loop().
          diag("b"); diagU(s_spwBits / 8); diag(" "); diagU(s_spwBytes[s_spwBits / 8 - 1]); diag(" ");
        }
        if (s_spwBits >= 64) {
          logAppend("DW spad written: ");
          for (int i = 0; i < 8; i++) logHex(s_spwBytes[i]);
          memcpy(s_spad, s_spwBytes, 8);
          s_spad[8] = crc8(s_spad, 8);   // 0xBE read: crc8(0..7) == byte 8
          s_state = DW_CMD;
        }
      }
      break;
    }
    case DW_OUT: {
      // read slots: bits driven by the ISR; main loop terminates the run.
      if (s_outPos >= s_outTotal && !s_readPull) {
        dwRelease();
        s_fallPend = false;
        s_inSlot = false;
        diag("E ");
        s_state = DW_IDLE;
      }
      break;
    }
    case DW_SEARCH: {
      // write slot: sample A's search bit @ +20us; a mismatch defeats us
      // (subsequent read pairs answer 1/1 -> A ends the search).
      if (s_inSlot && s_searchPhase == 2 && s_writeEdge && (int32_t)(now - s_slotStart) >= 30) {
        bool w = (dwLevel() == HIGH);
        bool rb = dwRomBit(s_searchPos);
        diag("Wt pos="); diagU(s_searchPos); diag(" w="); diagU(w ? 1 : 0); diag(" rb="); diagU(rb ? 1 : 0); diag("|");
        if (w != rb) s_searchMatched = false;
        s_searchPos++;
        s_searchPhase = 0;
        s_inSlot = false;
        s_writeEdge = false;
        if (s_searchPos >= 64) {
          logAppend("DW search done");
          s_state = DW_IDLE;
        }
      }
      break;
    }
  }
}

// ---- crc8 (DS18B20, poly 0x8C, LSB-first) ----
static uint8_t crc8(const uint8_t* d, uint8_t n) {
  uint8_t crc = 0;
  for (uint8_t i = 0; i < n; i++) {
    uint8_t b = d[i];
    for (int k = 0; k < 8; k++) {
      if ((crc ^ b) & 0x01) crc = (crc >> 1) ^ 0x8C; else crc >>= 1;
      b >>= 1;
    }
  }
  return crc;
}

// ---- I2C slave (register pointer protocol; deferred log) ----
static void onI2cReceive(int count) {
  logAppend("I2C rx n="); logUint((uint32_t)count);
  for (int i = 0; i < count; i++) {
    uint8_t b = (uint8_t)Wire.read();
    logAppend(" "); logHex(b);
    if (i == 0) s_regPtr = b & 0x0F;
    else regs[(s_regPtr + (i - 1)) & 0x0F] = b;
  }
}
static void onI2cRequest() {
  logAppend("I2C req ptr="); logUint(s_regPtr & 0x0F);
  Wire.write(regs[s_regPtr & 0x0F]);
}

// ---- UART1 line handling (control from board A) ----
static void handleUartLine(String line) {
  if (line == "GPIO") {
    u1.end();
    s_mirror = true;
    s_square = false;
    pinMode(MIRROR_IN, INPUT_PULLUP);  // v1.15
    pinMode(MIRROR_OUT, OUTPUT);
    digitalWrite(MIRROR_OUT, LOW);
    logAppend("MODE=GPIO (mirror in=10 -> out=15)");
  } else if (line == "MODE") {
    logAppend(s_mirror ? "MODE=GPIO" : "MODE=UART");
  } else if (line == "PING") {
    for (int i = 0; i < 10; i++) { u1.println("PONG"); delay(50); }
    logAppend("UART tx PONG x10");
  } else {
    for (int i = 0; i < 3; i++) { u1.println("ECHO:" + line); delay(50); }
    logAppend("UART tx ECHO x3");
  }
}
static void pollUart() {
  if (s_mirror || u1.available() == 0) return;
  // v1.9: static buffer + strict 200us budget. The old String-per-byte form
  // (heap churn + millis-based 50ms budget) blocked the main loop for ms
  // during 1-Wire transactions and broke search write-slot sampling.
  static char buf[128];
  int n = 0;
  uint32_t t0 = (uint32_t)micros();
  while (u1.available() > 0 && n < 127) {
    char c = (char)u1.read();
    if (c == '\n') break;
    if (c == '\r') continue;
    buf[n++] = c;
    if ((uint32_t)micros() - t0 > 200) break;
  }
  if (n > 0) {
    buf[n] = 0;
    String line(buf);
    logAppend("UART rx "); logAppend(line.c_str());
    handleUartLine(line);
  }
}

// ---- console (CH340 UART0) control: SQUARE / STOP / GPIO / AUDIT ----
static bool s_audit = false;
static uint32_t s_auditEnd = 0;
static uint32_t s_auditTick = 0;
static uint32_t s_auditTrans[6] = {0};
static int s_auditLast[6] = {0, 0, 0, 0, 0, 0};
static const int auditPins[6] = {4, 8, 9, 10, 11, 15};

static void auditStart(uint32_t secs) {
  s_audit = true;
  s_auditEnd = millis() + secs * 1000UL;
  s_auditTick = 0;
  memset(s_auditTrans, 0, sizeof(s_auditTrans));
  for (int i = 0; i < 6; i++) s_auditLast[i] = digitalRead(auditPins[i]);
  logAppend("AUDIT start");
}

static void pollAudit() {
  if (!s_audit) return;
  uint32_t now = millis();
  if (now >= s_auditEnd) {
    s_audit = false;
    char line[80]; int n = 0;
    const char* head = "AUDIT end: ";
    while (*head && n < 76) line[n++] = *head++;
    for (int i = 0; i < 6; i++) {
      int p = auditPins[i];
      int v = (int)s_auditTrans[i];
      if (n < 76) line[n++] = ' ';
      if (n < 76) line[n++] = 'p';
      if (n < 76) line[n++] = (char)('0' + (p / 10));
      if (n < 76) line[n++] = (char)('0' + (p % 10));
      if (n < 76) line[n++] = '=';
      if (n < 76) line[n++] = (char)('0' + v);
    }
    line[n] = 0;
    logAppend(line);
    return;
  }
  if (now - s_auditTick >= 50) {
    s_auditTick = now;
    for (int i = 0; i < 6; i++) {
      int p = auditPins[i];
      int v = digitalRead(p);
      if (v != s_auditLast[i]) { s_auditLast[i] = v; s_auditTrans[i]++; }
    }
  }
}

static void pollConsole() {
  // v1.10: retain the command buffer across calls and process ONLY on EOL.
  // The old version reset n each call, so a command arriving across several
  // 200us budget windows was split and the first fragment was executed
  // prematurely (DQPROBE 120000 -> "DQPROBE 12" + "000").
  static char buf[64];
  static int n = 0;
  uint32_t t0 = (uint32_t)micros();
  bool eol = false;
  while (Serial.available() > 0 && n < 63) {
    char c = (char)Serial.read();
    if (c == '\n') { eol = true; break; }
    if (c == '\r') { eol = true; continue; }
    buf[n++] = c;
    if ((uint32_t)micros() - t0 > 200) break;
  }
  if (n >= 63) { n = 0; return; }  // command too long: drop it
  if (!eol) return;                 // still accumulating; process on EOL
  buf[n] = 0;
  n = 0;
  String line(buf);
  if (line == "SQUARE") {
    u1.end();  // frees pin 15 from UART1 TX so it can be GPIO-driven
    s_square = true;
    s_mirror = false;
    s_sqLast = (uint32_t)micros();
    s_sqHi = false;
    pinMode(MIRROR_OUT, OUTPUT);
    digitalWrite(MIRROR_OUT, LOW);
    logAppend("SQUARE 1kHz on 15 (u1 ended)");
  } else if (line == "STOP") {
    s_square = false;
    digitalWrite(MIRROR_OUT, LOW);
    u1.begin(115200, SERIAL_8N1, U1_RX, U1_TX);  // restore UART1
    logAppend("STOP (out=15 low, u1 restored)");
  } else if (line == "UART") {
    // Release GPIO mirror: pin 15 is wired to A's UART RX (GPIO 44);
    // mirror mode holds it LOW (A's UART1 RX reads a 0x00 stream).
    s_mirror = false;
    s_square = false;
    digitalWrite(MIRROR_OUT, LOW);
    u1.begin(115200, SERIAL_8N1, U1_RX, U1_TX);  // pin 15 back to UART1 TX
    logAppend("MODE=UART (pin15 restored to UART1 TX)");
  } else if (line == "GPIO") {
    u1.end();
    s_mirror = true;
    s_square = false;
    pinMode(MIRROR_IN, INPUT_PULLUP);  // v1.15
    pinMode(MIRROR_OUT, OUTPUT);
    digitalWrite(MIRROR_OUT, LOW);
    logAppend("MODE=GPIO (mirror in=10 -> out=15)");
  } else if (line.startsWith("AUDIT")) {
    uint32_t secs = 3;
    if (line.length() > 6) secs = line.substring(6).toInt();
    if (secs < 1) secs = 1;
    if (secs > 30) secs = 30;
    auditStart(secs);
  } else if (line.startsWith("MEASURE")) {
    // v1.16 bounded pin-frequency/duty measurement: MEASURE <pin> [ms]
    // Reads the pin (plain input) over ms (100..5000, default 2000),
    // counts rising/falling edges + cumulative HIGH time, then reports one
    // parse-friendly line and returns to the prompt (no state change).
    int pin = 10;
    uint32_t ms = 2000;
    String rest = line.substring(7);
    int sp = rest.indexOf(' ');
    String pinTok = (sp >= 0) ? rest.substring(0, sp) : rest;
    if (pinTok.length() > 0) pin = pinTok.toInt();
    if (sp >= 0) {
      String msTok = rest.substring(sp + 1);
      if (msTok.length() > 0) ms = msTok.toInt();
    }
    if (pin < 0 || pin > 48) { Serial.println("MEASURE: bad pin"); return; }
    if (ms < 100) ms = 100;
    if (ms > 5000) ms = 5000;
    pinMode(pin, INPUT_PULLUP);
    uint32_t rising = 0, falling = 0, hiTime = 0, hiStart = 0;
    int last = digitalRead(pin);
    if (last == 1) hiStart = (uint32_t)micros();
    uint32_t t0 = (uint32_t)micros();
    uint32_t tEnd = t0 + ms * 1000UL;
    while ((uint32_t)micros() < tEnd) {
      int cur = digitalRead(pin);
      if (cur != last) {
        uint32_t now = (uint32_t)micros();
        if (cur == 1) { rising++; hiStart = now; }
        else { falling++; if (hiStart) hiTime += (now - hiStart); hiStart = 0; }
        last = cur;
      }
    }
    if (last == 1 && hiStart) hiTime += ((uint32_t)micros() - hiStart);
    float freq = ((rising + falling) / 2.0f) / (ms / 1000.0f);
    float duty = (hiTime / (float)(ms * 1000UL)) * 100.0f;
    char mbuf[96];
    snprintf(mbuf, sizeof(mbuf), "MEASURE pin=%d rising=%lu falling=%lu freq=%.0fHz duty=%.1f%%",
             pin, (unsigned long)rising, (unsigned long)falling, freq, duty);
    Serial.println(mbuf);
  } else if (line == "DUMP") {
    int len = s_diagLen;
    if (len == 0) {
      Serial.println("DUMP: (empty)");
    } else {
      Serial.println("DUMP:");
      Serial.write(s_diag, len);
      Serial.println();
      s_diagLen = 0;
    }
  } else if (line == "LDUMP") {
    // flush the deferred 1-Wire log buffer regardless of idle state
    Serial.println("LDUMP:");
    if (s_logLen == 0) Serial.println("(empty)");
    else Serial.write(s_logBuf, s_logLen);
    s_logLen = 0;
  } else if (line.startsWith("DQPROBE")) {
    // Core-1 waveform capture: records every DQ level change with a us
    // offset. Main loop stays free so 1-Wire timing is unaffected.
    uint32_t us = 20000;
    if (line.length() > 8) us = line.substring(8).toInt();
    if (us < 100) us = 100;
    if (us > 500000) us = 500000;
    if (s_probeActive) {
      Serial.println("DQPROBE: already running");
    } else {
      s_probeUs = us;
      s_probeActive = true;
      s_probeDone = false;
      xTaskCreatePinnedToCore(dqProbeTask, "dqprobe", 2048, NULL, 2, NULL, 0);
      Serial.println("DQPROBE: started");
    }
  } else if (line == "WFDUMP") {
    // print the dedicated waveform buffer (t_us level), one transition per line
    Serial.println("WFDUMP:");
    uint16_t n = s_wfLen;
    Serial.print("nt="); Serial.println((int)n);
    for (uint16_t i = 0; i < n; i++) {
      uint32_t t = (uint32_t)s_wf[i * 3] | ((uint32_t)s_wf[i * 3 + 1] << 8);
      Serial.print(t); Serial.print(' '); Serial.println((int)s_wf[i * 3 + 2]);
    }
  }
}

// ---- GPIO mirror ----
static void pollMirror() {
  if (!s_mirror || s_square) return;
  static int last = -1;
  int v = digitalRead(MIRROR_IN);
  if (v != last) {
    last = v;
    digitalWrite(MIRROR_OUT, v ? HIGH : LOW);
    s_lastT = millis();
    logAppend("MIRROR in="); logUint((uint32_t)v);
  }
}

// ---- setup / loop ----
void setup() {
  Serial.begin(115200);
  memset(regs, 0, sizeof(regs));
  s_rom[7] = crc8(s_rom, 7);
  s_spad[6] = crc8(s_spad, 6);   // DS18B20-style
  s_spad[7] = crc8(s_spad, 7);   // A's 0xAA read check: crc8(0..6) == byte 7
  s_spad[8] = crc8(s_spad, 8);   // A's 0xBE read check: crc8(0..7) == byte 8

  // 1-Wire DQ: open drain (OUTEN off, pull-up on, input readable)
  pinMode(DW_PIN, OUTPUT);
  GPIO.out_w1ts    = (1u << DW_PIN);   // data 1
  GPIO.enable_w1tc = (1u << DW_PIN);   // OUTEN 0 -> floats high via pull-up
  gpio_ll_pullup_en(&GPIO, DW_PIN);    // internal pull-up (S3 pin-mux register)

  // Raw GPIO interrupt wiring — driver bypass (v1.7):
  //  - the driver's gpio_isr_register funnels registration through Core 1's
  //    ipc task (2 KB stack) -> stack-canary overflow (ipc1 crash, v1.4/v1.6);
  //  - the driver edge path (ESP_INTR_FLAG_EDGE) never delivered pin-11 edges
  //    in testing (ISR never entered).
  // S3 registers (per esp-idf S3 HAL): pins 0-31 share ETS_GPIO_INTR_SOURCE;
  // per-pin int_type + int_ena = BIT(0) (pro/app share one enable bit);
  // edge status latches in pcpu_int, cleared via status_w1tc.
  // esp_intr_alloc on the calling core (Core 0 / loopTask) -> no IPC at all.
  GPIO.pin[DW_PIN].int_type = GPIO_INTR_NEGEDGE;
  GPIO.pin[DW_PIN].int_ena  = 1;              // GPIO_LL_INTR_ENA = BIT(0)
  GPIO.status_w1tc = (1u << DW_PIN);          // clear any pending status
  static intr_handle_t s_dwIntr = NULL;
  esp_err_t dwErr = esp_intr_alloc(ETS_GPIO_INTR_SOURCE, ESP_INTR_FLAG_LOWMED,
                                   dwGpioIsr, NULL, &s_dwIntr);
  if (dwErr != ESP_OK) Serial.printf("DW isr alloc failed: %d\n", dwErr);

  u1.begin(115200, SERIAL_8N1, U1_RX, U1_TX);
  // NOTE: pin 15 (MIRROR_OUT) is owned by u1 (UART1 TX) from here on.
  // Do NOT pinMode/digitalWrite it in setup — that would not re-route the
  // GPIO matrix away from UART1 TX (v1.2 bug: pin stuck at UART idle level).

  // v1.6: 4-arg begin = I2C SLAVE at 0x50 (v1.5 used the master form).
  Wire.begin(SLAVE_ADDR, I2C_SDA, I2C_SCL, 400000);
  Wire.onReceive(onI2cReceive);
  Wire.onRequest(onI2cRequest);

  pinMode(MIRROR_IN, INPUT_PULLUP);  // v1.15

  delay(5);
  Serial.printf("DQ idle level: %d (expect 1 = pull-up OK)\n", dwLevel());

  Serial.println("RIG-RESPONDER v1.16 up");
  Serial.printf("ROM:");
  for (int i = 0; i < 8; i++) Serial.printf(" %02X", s_rom[i]);
  Serial.println();
  Serial.printf("SPAD:");
  for (int i = 0; i < 9; i++) Serial.printf(" %02X", s_spad[i]);
  Serial.println();
  Serial.println("I2C slave SDA=8 SCL=9 @0x50; DQ=11 (open-drain ISR); UART1 RX=4 TX=15; MIRROR in=10 out=15; console: SQUARE/STOP/GPIO/UART/AUDIT n");
}

void loop() {
  s_mainTicks++;
  if ((s_mainTicks & 0xFF) == 0) s_mainCore = (uint32_t)xTaskGetCoreID(xTaskGetCurrentTaskHandle());
  s_loopStage = 0;
  if (s_square) {
    uint32_t now = (uint32_t)micros();
    if (now - s_sqLast >= 500) {   // 1 kHz: 500 us per half-cycle
      s_sqLast = now;
      s_sqHi = !s_sqHi;
      digitalWrite(MIRROR_OUT, s_sqHi ? HIGH : LOW);
    }
  }
  // 1-Wire state machine FIRST: write-slot sampling is latency-critical
  // (sample @ +30us of a 65us slot). Running it after pollUart/pollConsole
  // delayed the sample past the slot, misreading consecutive write bytes
  // as HIGH (write-sp / scan failures).
  dwSlavePoll();
  s_loopStage = 1;
  pollUart();
  s_loopStage = 2;
  pollConsole();
  s_loopStage = 3;
  pollMirror();
  s_loopStage = 4;
  pollAudit();
  s_loopStage = 5;
  flushLog();
  s_loopStage = 6;
  if (s_probeDone && !s_probeActive) {
    s_probeDone = false;
    Serial.println("DQPROBE: done");
  }
  s_loopStage = 7;
}
