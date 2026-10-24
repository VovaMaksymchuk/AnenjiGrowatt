// Growatt Hope 5.0L-B1  <->  Anenji 6.2kW  — PHASE 1: SNIFFER
// Board: Waveshare ESP32-S3-Zero
//
// RS485 side (inverter BMS port, XY-017 auto-direction module): receive; transmit only via "tx".
//   - Pylontech ASCII frames (~....\r) are decoded and checksum-verified (inverter in Li2 mode).
//   - Anything else is split by line silence and hex-dumped with a Modbus CRC check (Li4 mode,
//     or whatever the battery answers).
// CAN side (battery PCS port pins 4/5): needs a 3.3 V CAN transceiver (SN65HVD230). Off by default.
//   - "can on"     : normal mode, sends Growatt heartbeat 0x301 every 1 s, decodes battery replies.
//   - "can listen" : listen-only, nothing transmitted.
// RS485 transmits ONLY on explicit "tx <text>" command. Output goes to USB serial (115200).

#include <Arduino.h>
#include "driver/twai.h"
#include "driver/uart.h"
#include <Preferences.h>

// ======== Pins (Waveshare ESP32-S3-Zero) ========
#define PIN_RS485_RX   5    // XY-017 receiver output (verified: drops to 0 V on bus "0")
#define PIN_RS485_TX   6    // XY-017 driver input (auto-direction, used only by "tx"/"selftest")
#define PIN_RS485_DE   7    // module DE+RE tied together, held LOW = receive. -1 if not used
#define PIN_CAN_TX     1    // SN65HVD230 CTX (D)
#define PIN_CAN_RX     2    // SN65HVD230 CRX (R)

HardwareSerial RS(1);
static uint32_t rsBaud = 9600;

enum CanMode { CAN_OFF, CAN_LISTEN, CAN_ACTIVE };
static CanMode canMode = CAN_OFF;
static bool canVerbose = false;
static uint32_t lastHb = 0, lastSummary = 0, hbSent = 0, canRx = 0;
static uint32_t rsBytes = 0, rsAsciiFrames = 0, rsBinFrames = 0;
static bool rsRaw = false;                       // echo every RS485 byte in hex
static bool pylonOn = false, pylonStaleLogged = false;   // Pylontech emulator ("pylon on")
static uint32_t pylReplies = 0, pylOtherAdr = 0, pylStale = 0;
static uint32_t pylDelayMs = 30;                 // inverter may need time to release the bus ("pylon delay <ms>")
static uint32_t pylLastReplyMs = 0, lastReqMs = 0;  // for status LED
static Preferences prefs;                        // NVS "bridge/auto": emulator autostart (default on)
#define STATUS_LED_PIN   21                      // S3 Zero onboard WS2812; -1 to disable
#define STATUS_LED_LEVEL 12                      // brightness 0..255
// S3 Zero LED has R and G swapped vs neopixelWrite() (verified: "red" lit green)
#define STATUS_LED(r, g, b) neopixelWrite(STATUS_LED_PIN, (g), (r), (b))
static volatile uint32_t rxEdges = 0;            // GPIO edges on RS485 RX pin (signal present at all?)
static uint32_t lastStat = 0, lastStatEdges = 0, lastStatBytes = 0;

static volatile uint32_t lastEdgeUs = 0, minPulseUs = UINT32_MAX;  // shortest pulse -> baud estimate
static volatile uint32_t errFrame = 0, errBreak = 0, errOvf = 0, errOther = 0;

static void IRAM_ATTR onRxEdge() {
  uint32_t now = micros(), d = now - lastEdgeUs;
  lastEdgeUs = now;
  rxEdges++;
  if (d > 2 && d < minPulseUs) minPulseUs = d;
}

static void onRsError(hardwareSerial_error_t e) {
  switch (e) {
    case UART_FRAME_ERROR: errFrame++; break;
    case UART_BREAK_ERROR: errBreak++; break;
    case UART_FIFO_OVF_ERROR: case UART_BUFFER_FULL_ERROR: errOvf++; break;
    default: errOther++;
  }
}

// ---------------------------------------------------------------- helpers
static void logPrefix(const char* tag) {
  Serial.printf("[%9lu] %-5s ", (unsigned long)millis(), tag);
}

static int nib(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  return -1;
}

// parse n hex chars at position i; -1 on error
static long hexAt(const String& s, int i, int n) {
  if (i + n > (int)s.length()) return -1;
  long v = 0;
  for (int k = 0; k < n; k++) {
    int d = nib(s[i + k]);
    if (d < 0) return -1;
    v = (v << 4) | d;
  }
  return v;
}

static uint16_t be16(const uint8_t* d, int i) { return (uint16_t)((d[i] << 8) | d[i + 1]); }
static int16_t  bes16(const uint8_t* d, int i) { return (int16_t)be16(d, i); }

// ---------------------------------------------------------------- RS485: Pylontech ASCII
static const char* pylonCmdName(uint8_t c) {
  switch (c) {
    case 0x00: return "response OK";
    case 0x42: return "pack analog";
    case 0x44: return "pack alarm";
    case 0x47: return "system parameter";
    case 0x4F: return "protocol version";
    case 0x51: return "manufacturer info";
    case 0x60: return "system basic info";
    case 0x61: return "system analog";
    case 0x62: return "system alarm";
    case 0x63: return "system charge mgmt";
    case 0x92: return "charge/discharge mgmt";
    case 0x93: return "serial number";
    default:   return "?";
  }
}

static void pylonOnRequest(long adr, long cid1, long cid2);   // emulator, defined after CAN state

static uint32_t req61 = 0, req62 = 0, req63 = 0, reqOther = 0, reqBad = 0;  // inverter requests (all ADR)

// b = everything between '~' and '\r'
static void handlePylon(const String& b) {
  rsAsciiFrames++;
  long ver = -1, adr = -1, cid1 = -1, cid2 = -1, len = -1;
  if (b.length() >= 16) {
    ver = hexAt(b, 0, 2); adr = hexAt(b, 2, 2); cid1 = hexAt(b, 4, 2); cid2 = hexAt(b, 6, 2); len = hexAt(b, 8, 4);
  }
  if (ver < 0 || adr < 0 || cid1 < 0 || cid2 < 0 || len < 0) {
    reqBad++;
    logPrefix("485A"); Serial.printf("~%s  (too short / bad hex in header)\n", b.c_str());
    return;
  }
  int lenid = len & 0x0FFF;
  int nsum = (lenid & 0xF) + ((lenid >> 4) & 0xF) + ((lenid >> 8) & 0xF);
  bool lenOk = ((len >> 12) & 0xF) == ((16 - (nsum % 16)) % 16);
  bool sizeOk = (int)b.length() == 12 + lenid + 4;
  bool sumOk = false;
  if (sizeOk) {
    uint32_t sum = 0;
    for (int i = 0; i < 12 + lenid; i++) sum += (uint8_t)b[i];
    sumOk = hexAt(b, 12 + lenid, 4) == (long)((~sum + 1) & 0xFFFF);
  }
  bool ok = lenOk && sumOk;
  if (!ok) reqBad++;
  else if (cid2 == 0x61) req61++;
  else if (cid2 == 0x62) req62++;
  else if (cid2 == 0x63) req63++;
  else reqOther++;
  // quiet by default: only bad / unexpected frames; everything with "v"
  if (canVerbose || !ok || cid2 < 0x61 || cid2 > 0x63) {
    String info = b.substring(12, min((int)b.length(), 12 + lenid));
    logPrefix("485A");
    Serial.printf("~%s  ADR=%02lX CID1=%02lX CID2=%02lX [%s] INFO=\"%s\" len:%s size:%s chk:%s\n",
                  b.c_str(), adr, cid1, cid2, pylonCmdName((uint8_t)cid2), info.c_str(),
                  lenOk ? "ok" : "BAD", sizeOk ? "ok" : "BAD", sumOk ? "ok" : "BAD");
  }
  if (ok) { lastReqMs = millis(); pylonOnRequest(adr, cid1, cid2); }
}

// ---------------------------------------------------------------- RS485: binary / Modbus
static uint8_t binBuf[256];
static size_t binLen = 0;
static String asciiBuf;
static bool inAscii = false;
static uint32_t lastByteUs = 0;

static uint16_t crc16modbus(const uint8_t* p, size_t n) {
  uint16_t crc = 0xFFFF;
  for (size_t i = 0; i < n; i++) {
    crc ^= p[i];
    for (int k = 0; k < 8; k++) crc = (crc & 1) ? (crc >> 1) ^ 0xA001 : crc >> 1;
  }
  return crc;
}

static void flushBin() {
  if (!binLen) return;
  rsBinFrames++;
  logPrefix("485B");
  for (size_t i = 0; i < binLen; i++) Serial.printf("%02X ", binBuf[i]);
  if (binLen >= 4) {
    uint16_t crc = crc16modbus(binBuf, binLen - 2);
    bool ok = (binBuf[binLen - 2] == (crc & 0xFF)) && (binBuf[binLen - 1] == (crc >> 8));
    if (ok) Serial.printf(" | modbus id=%u fc=0x%02X CRC ok", binBuf[0], binBuf[1]);
    else    Serial.print(" | not modbus (CRC mismatch)");
  }
  Serial.println();
  binLen = 0;
}

static void pollRs485() {
  while (RS.available()) {
    uint8_t c = RS.read();
    rsBytes++;
    if (rsRaw) Serial.printf("%02X ", c);
    lastByteUs = micros();
    if (inAscii) {
      if (c == '\r') { handlePylon(asciiBuf); asciiBuf = ""; inAscii = false; }
      else if (c == '~') { asciiBuf = ""; }                 // restart on new SOI
      else if (asciiBuf.length() < 400) { asciiBuf += (char)c; }
      else { logPrefix("485A"); Serial.println("(overlong ASCII frame dropped)"); asciiBuf = ""; inAscii = false; }
      continue;
    }
    if (c == '~') { flushBin(); inAscii = true; asciiBuf = ""; continue; }
    if (binLen < sizeof(binBuf)) binBuf[binLen++] = c;
  }
  uint32_t gapUs = max<uint32_t>(2000, 44000000UL / rsBaud);   // ~4 character times
  uint32_t idle = micros() - lastByteUs;
  if (binLen && idle > gapUs) flushBin();
  if (inAscii && idle > 200000) {
    logPrefix("485A");
    Serial.printf("(incomplete, no CR) ~%s\n", asciiBuf.c_str());
    asciiBuf = ""; inAscii = false;
  }
}

static int rsRxPin = PIN_RS485_RX;               // runtime-selectable ("rxpin <n>", "swap")
static int rsTxPin = PIN_RS485_TX;
static uint32_t lowSamples = 0, lastStatLows = 0; // polled LOW level, independent of UART/IRQ

static bool rsIrqAttached = false;

static void rsBegin(uint32_t baud) {
  if (rsIrqAttached) detachInterrupt(rsRxPin);
  RS.end();
  rsBaud = baud;
  RS.setRxBufferSize(1024);
  RS.begin(rsBaud, SERIAL_8N1, rsRxPin, rsTxPin);
  RS.onReceiveError(onRsError);                  // end() clears it, so re-register every begin
  // let STAT read the TX level: enable only the pad input buffer.
  // NOT gpio_set_direction(): it reconnects the pad to plain GPIO and cuts UART TX off the pin.
  PIN_INPUT_ENABLE(GPIO_PIN_MUX_REG[rsTxPin]);
  attachInterrupt(rsRxPin, onRxEdge, CHANGE);
  rsIrqAttached = true;
  binLen = 0; asciiBuf = ""; inAscii = false;
}

// Periodic heartbeat: visible whenever the monitor (re)connects.
static void printStat() {
  uint32_t e = rxEdges, de = e - lastStatEdges, db = rsBytes - lastStatBytes, dl = lowSamples - lastStatLows;
  lastStatEdges = e; lastStatBytes = rsBytes; lastStatLows = lowSamples;
  uint32_t mp = minPulseUs;
  minPulseUs = UINT32_MAX;
  logPrefix("STAT");
  Serial.printf("485 bytes/5s=%lu req 61=%lu 62=%lu 63=%lu other=%lu bad=%lu | PYL %s rep=%lu skipAdr=%lu stale=%lu delay=%lums | CAN rx=%lu",
                (unsigned long)db, (unsigned long)req61, (unsigned long)req62, (unsigned long)req63,
                (unsigned long)reqOther, (unsigned long)reqBad, pylonOn ? "ON" : "off",
                (unsigned long)pylReplies, (unsigned long)pylOtherAdr, (unsigned long)pylStale,
                (unsigned long)pylDelayMs, (unsigned long)canRx);
  if (errFrame || errBreak || errOvf)
    Serial.printf(" | err frame=%lu brk=%lu ovf=%lu", (unsigned long)errFrame, (unsigned long)errBreak, (unsigned long)errOvf);
  if (canVerbose) {
    Serial.printf(" | rx GPIO%d=%d tx GPIO%d=%d edges=%lu lows=%lu baud=%lu", rsRxPin, digitalRead(rsRxPin),
                  rsTxPin, digitalRead(rsTxPin), (unsigned long)de, (unsigned long)dl, (unsigned long)rsBaud);
    if (de && mp != UINT32_MAX) Serial.printf(" minPulse=%luus (~%lu baud)", (unsigned long)mp, 1000000UL / mp);
  }
  if (!de && !dl) Serial.print(digitalRead(rsRxPin) ? "  <- idle HIGH, no signal" : "  <- stuck LOW (A/B swapped? wiring?)");
  else if (!db) Serial.print("  <- signal but no bytes: wrong baud?");
  Serial.println();
}

// ---------------------------------------------------------------- CAN: Growatt LV V1.04
// 500 kbit/s, standard IDs, big-endian. Inverter sends 0x301 once per second,
// battery answers with 0x311..0x320.
struct GwState {
  uint32_t t311 = 0, t313 = 0, t319 = 0;
  float cv = 0, ccl = 0, dcl = 0;     // V, A, A
  uint16_t status = 0;
  float v = 0, i = 0, tmax = 0;        // V, A, degC
  uint8_t soc = 0, soh = 0;
  uint8_t prot1 = 0, prot2 = 0, al1 = 0, al2 = 0, packs = 0, cells = 0;
  uint8_t f319 = 0;
  uint16_t vmax = 0, vmin = 0;
  float rm = 0, fcc = 0;               // Ah
  uint16_t dv = 0, cycles = 0;
  uint16_t cell[16] = {0};
} gw;

static void decodeGrowatt(const twai_message_t& m) {
  const uint8_t* d = m.data;
  bool known = !m.extd && (m.data_length_code == 8);
  if (known) switch (m.identifier) {
    case 0x311:
      gw.t311 = millis();
      gw.cv = be16(d, 0) * 0.1f; gw.ccl = be16(d, 2) * 0.1f; gw.dcl = be16(d, 4) * 0.1f;
      gw.status = be16(d, 6);
      if (canVerbose) {
        logPrefix("CAN"); Serial.printf("311 CV=%.1fV CCL=%.1fA DCL=%.1fA status=0x%03X (state=%u err=%u bal=%u dsgOut=%u chgOut=%u)\n",
          gw.cv, gw.ccl, gw.dcl, gw.status, gw.status & 3, (gw.status >> 2) & 1, (gw.status >> 3) & 1,
          (gw.status >> 5) & 1, (gw.status >> 6) & 1);
      }
      break;
    case 0x312:
      gw.prot1 = d[0]; gw.prot2 = d[1]; gw.al1 = d[2]; gw.al2 = d[3]; gw.packs = d[4]; gw.cells = d[7];
      if (canVerbose) { logPrefix("CAN"); Serial.printf("312 prot=%02X %02X alarm=%02X %02X packs=%u mfr=%02X%02X cells=%u\n",
          d[0], d[1], d[2], d[3], d[4], d[5], d[6], d[7]); }
      break;
    case 0x313:
      gw.t313 = millis();
      gw.v = bes16(d, 0) * 0.01f; gw.i = bes16(d, 2) * 0.1f; gw.tmax = bes16(d, 4) * 0.1f;
      gw.soc = d[6]; gw.soh = d[7] & 0x7F;
      if (canVerbose) { logPrefix("CAN"); Serial.printf("313 V=%.2fV I=%.1fA Tmax=%.1fC SOC=%u%% SOH=%u%%\n",
          gw.v, gw.i, gw.tmax, gw.soc, gw.soh); }
      break;
    case 0x314:
      gw.rm = be16(d, 0) * 0.01f; gw.fcc = be16(d, 2) * 0.01f; gw.dv = be16(d, 4); gw.cycles = be16(d, 6);
      if (canVerbose) { logPrefix("CAN"); Serial.printf("314 RM=%.2fAh FCC=%.2fAh dV=%umV cycles=%u\n",
          gw.rm, gw.fcc, gw.dv, gw.cycles); }
      break;
    case 0x315: case 0x316: case 0x317: case 0x318: {
      int base = (m.identifier - 0x315) * 4;
      for (int k = 0; k < 4; k++) gw.cell[base + k] = be16(d, k * 2);
      if (canVerbose) { logPrefix("CAN"); Serial.printf("%03lX cells %d-%d: %u %u %u %u mV\n", (unsigned long)m.identifier,
          base + 1, base + 4, gw.cell[base], gw.cell[base + 1], gw.cell[base + 2], gw.cell[base + 3]); }
      break;
    }
    case 0x319:
      gw.t319 = millis();
      gw.f319 = d[0]; gw.vmax = be16(d, 1); gw.vmin = be16(d, 3);
      if (canVerbose) { logPrefix("CAN"); Serial.printf("319 chgEn=%u dsgEn=%u force1=%u force2=%u type=%u Vmax=%umV(#%u) Vmin=%umV(#%u) protID=%u\n",
          (d[0] >> 7) & 1, (d[0] >> 6) & 1, (d[0] >> 5) & 1, (d[0] >> 4) & 1, d[0] & 3,
          gw.vmax, d[5], gw.vmin, d[6], d[7]); }
      break;
    case 0x320:
      if (canVerbose) { logPrefix("CAN"); Serial.printf("320 mfr=\"%c%c\" hw=%u sw=%u\n", d[0], d[1], d[2], d[3]); }
      break;
    default:
      known = false;
  }
  if (canVerbose) {                              // unknown Growatt frames 0x321..0x500 are normal, show only in verbose
    logPrefix("CANr");
    Serial.printf("%s%03lX [%u] ", m.extd ? "x" : "", (unsigned long)m.identifier, m.data_length_code);
    for (int k = 0; k < m.data_length_code; k++) Serial.printf("%02X ", m.data[k]);
    Serial.println();
  }
}

static void canStop() {
  if (canMode == CAN_OFF) return;
  twai_stop();
  twai_driver_uninstall();
  canMode = CAN_OFF;
}

static bool canStart(CanMode mode) {
  canStop();
  twai_general_config_t g = TWAI_GENERAL_CONFIG_DEFAULT((gpio_num_t)PIN_CAN_TX, (gpio_num_t)PIN_CAN_RX,
      mode == CAN_ACTIVE ? TWAI_MODE_NORMAL : TWAI_MODE_LISTEN_ONLY);
  g.rx_queue_len = 32;
  g.tx_queue_len = 4;
  g.alerts_enabled = TWAI_ALERT_BUS_OFF | TWAI_ALERT_BUS_RECOVERED | TWAI_ALERT_ERR_PASS;
  twai_timing_config_t t = TWAI_TIMING_CONFIG_500KBITS();
  twai_filter_config_t f = TWAI_FILTER_CONFIG_ACCEPT_ALL();
  if (twai_driver_install(&g, &t, &f) != ESP_OK) return false;
  if (twai_start() != ESP_OK) { twai_driver_uninstall(); return false; }
  canMode = mode;
  return true;
}

static void pollCan() {
  if (canMode == CAN_OFF) return;

  uint32_t alerts;
  if (twai_read_alerts(&alerts, 0) == ESP_OK) {
    if (alerts & TWAI_ALERT_ERR_PASS) { logPrefix("CAN"); Serial.println("error-passive (no ACK? check transceiver/wiring/bitrate)"); }
    if (alerts & TWAI_ALERT_BUS_OFF)  { logPrefix("CAN"); Serial.println("BUS-OFF -> recovering"); twai_initiate_recovery(); }
    if (alerts & TWAI_ALERT_BUS_RECOVERED) { logPrefix("CAN"); Serial.println("recovered"); twai_start(); }
  }

  twai_message_t m;
  while (twai_receive(&m, 0) == ESP_OK) { canRx++; decodeGrowatt(m); }

  if (canMode == CAN_ACTIVE && millis() - lastHb >= 1000) {
    lastHb = millis();
    twai_message_t hb = {};
    hb.identifier = 0x301;
    hb.data_length_code = 8;
    const uint8_t pl[8] = {0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88};
    memcpy(hb.data, pl, 8);
    if (twai_transmit(&hb, 0) == ESP_OK) hbSent++;
  }
}

static void printSummary() {
  if (!gw.t311 && !gw.t313) return;
  logPrefix("BAT");
  Serial.printf("V=%.2f I=%.1f SOC=%u%% SOH=%u%% Tmax=%.1fC | CV=%.1f CCL=%.1f DCL=%.1f | cell %u..%u mV | "
                "chgEn=%u dsgEn=%u prot=%02X%02X alarm=%02X%02X | 311 age=%lums\n",
                gw.v, gw.i, gw.soc, gw.soh, gw.tmax, gw.cv, gw.ccl, gw.dcl, gw.vmin, gw.vmax,
                (gw.f319 >> 7) & 1, (gw.f319 >> 6) & 1, gw.prot1, gw.prot2, gw.al1, gw.al2,
                (unsigned long)(millis() - gw.t311));
}

// ---------------------------------------------------------------- Pylontech emulator (inverter Li2)
// Answers 0x61/0x62/0x63 as a single US2000 group (ADR 02) using fresh Growatt CAN data.
// Frame layout follows Fahmula/esphome-pylontech-rs485 (works on SMG-type inverters).
#define PYL_STALE_MS     5000     // no 0x311/0x313/0x319 for this long -> stay silent (inverter -> warning 19)
#define PYL_MAX_CHG_V    57.6f    // Hope 5.0L-B1 datasheet caps
#define PYL_MIN_DSG_V    48.0f    // Growatt does not send it
#define PYL_MAX_CHG_A    100.0f
#define PYL_MAX_DSG_A    100.0f
// Growatt 0x312 protection (byte0<<8 | byte1) that must block charge / discharge
#define PYL_CHG_BLOCK    0x5558   // chg OC, cell OV, module OV, soft start fail | OTC, UTC, system error
#define PYL_DSG_BLOCK    0xABA8   // dsg OC, SCD, cell UV, module UV, soft start fail | OTD, UTD, system error

static bool fresh(uint32_t t) { return t && millis() - t < PYL_STALE_MS; }


static void pylonSend(const char* info) {
  char body[160], frame[170];
  int len = strlen(info);
  int s = (len & 0xF) + ((len >> 4) & 0xF) + ((len >> 8) & 0xF);
  int n = snprintf(body, sizeof(body), "20024600%1X%03X%s", (16 - s % 16) % 16, len, info);  // VER ADR CID1 RTN LENGTH INFO
  uint16_t sum = 0;
  for (int i = 0; i < n; i++) sum += (uint8_t)body[i];
  snprintf(frame, sizeof(frame), "~%s%04X\r", body, (uint16_t)(~sum + 1));
  if (pylDelayMs) delay(pylDelayMs);
  RS.print(frame);
  RS.flush();
  pylReplies++;
  pylLastReplyMs = millis();
  frame[strlen(frame) - 1] = 0;                  // drop CR for the log
  if (canVerbose) { logPrefix("PYLtx"); Serial.printf("%s (+%lums)\n", frame, (unsigned long)pylDelayMs); }
}

static uint16_t deciK(float c) { return (uint16_t)((c + 273.15f) * 10); }

static void pylonOnRequest(long adr, long cid1, long cid2) {
  if (!pylonOn || cid1 != 0x46 || (cid2 < 0x61 || cid2 > 0x63)) return;
  if (adr != 0x02) { pylOtherAdr++; return; }            // one group only, else inverter may sum 5 "packs"
  if (!fresh(gw.t311) || !fresh(gw.t313) || !fresh(gw.t319)) {
    pylStale++;
    if (!pylonStaleLogged) { logPrefix("PYL"); Serial.println("CAN data stale -> NOT answering inverter"); pylonStaleLogged = true; }
    return;
  }
  if (pylonStaleLogged) { logPrefix("PYL"); Serial.println("CAN data OK -> answering inverter"); pylonStaleLogged = false; }

  char info[110];
  uint16_t prot = ((uint16_t)gw.prot1 << 8) | gw.prot2;
  bool chgOk = (gw.f319 & 0x80) && !(prot & PYL_CHG_BLOCK) && gw.cv >= PYL_MIN_DSG_V;
  bool dsgOk = (gw.f319 & 0x40) && !(prot & PYL_DSG_BLOCK);

  if (cid2 == 0x61) {
    uint16_t t = deciK(gw.tmax);
    snprintf(info, sizeof(info),
             "%04X%04X%02X%04X%04X%02X%02X%04X%04X%04X%04X%04X%04X%04X%04X%04X%04X%04X%04X%04X%04X%04X%04X%04X%04X%04X",
             (uint16_t)(gw.v * 1000), (uint16_t)(int16_t)lroundf(gw.i * 100), gw.soc, gw.cycles, gw.cycles, gw.soh, gw.soh,
             gw.vmax, 0x0101, gw.vmin, 0x0108,
             t, t, 0x0103, t, 0x0109,      // cell temp avg/max/min (only Tmax known)
             t, t, 0x0101, t, 0x0101,      // MOSFET temps
             t, t, 0x0101, t, 0x0101);     // BMS temps
    pylonSend(info);
    if (canVerbose) {
      logPrefix("PYL"); Serial.printf("61 -> V=%.2f I=%.1f SOC=%u%% SOH=%u%% cyc=%u cell %u..%u mV T=%.1fC\n",
                                      gw.v, gw.i, gw.soc, gw.soh, gw.cycles, gw.vmin, gw.vmax, gw.tmax);
    }
  } else if (cid2 == 0x62) {
    uint8_t a1 = 0, a2 = 0, p1 = 0, p2 = 0;
    if (gw.al1 & 0x04) a1 |= 0x80;            // module OV       -> total V high
    if (gw.al1 & 0x02) a1 |= 0x40;            // module UV       -> total V low
    if (gw.al1 & 0x10) a1 |= 0x20;            // cell OV         -> cell V high
    if (gw.al1 & 0x08) a1 |= 0x10;            // cell UV         -> cell V low
    if (gw.al2 & 0xC0) a1 |= 0x08;            // OTD/OTC         -> cell temp high
    if (gw.al2 & 0x30) a1 |= 0x04;            // UTD/UTC         -> cell temp low
    if (gw.al2 & 0x04) a1 |= 0x01;            // delta V         -> cell imbalance
    if (gw.al1 & 0x40) a2 |= 0x40;            // chg OC
    if (gw.al1 & 0x80) a2 |= 0x20;            // dsg OC
    if (gw.prot1 & 0x04) p1 |= 0x80;          // module OV
    if (gw.prot1 & 0x02) p1 |= 0x40;          // module UV
    if (gw.prot1 & 0x10) p1 |= 0x20;          // cell OV
    if (gw.prot1 & 0x08) p1 |= 0x10;          // cell UV
    if (gw.prot2 & 0xC0) p1 |= 0x08;          // OTD/OTC
    if (gw.prot2 & 0x30) p1 |= 0x04;          // UTD/UTC
    if (gw.prot1 & 0x40) p2 |= 0x40;          // chg OC
    if (gw.prot1 & 0xA0) p2 |= 0x20;          // dsg OC / short circuit
    if ((gw.prot1 & 0x01) || (gw.prot2 & 0x0C)) p2 |= 0x08;  // soft start fail, system error, delta V fail
    snprintf(info, sizeof(info), "%02X%02X%02X%02X", a1, a2, p1, p2);
    pylonSend(info);
    static uint32_t last62 = 0;
    uint32_t cur62 = ((uint32_t)a1 << 24) | ((uint32_t)a2 << 16) | ((uint32_t)p1 << 8) | p2;
    if (canVerbose || cur62 != last62) { logPrefix("PYL"); Serial.printf("62 -> alarm %02X %02X prot %02X %02X\n", a1, a2, p1, p2); }
    last62 = cur62;
  } else {
    float vchg = min(gw.cv, PYL_MAX_CHG_V);
    float ichg = chgOk ? min(gw.ccl, PYL_MAX_CHG_A) : 0.0f;
    float idsg = dsgOk ? min(gw.dcl, PYL_MAX_DSG_A) : 0.0f;
    uint8_t st = (chgOk ? 0x80 : 0) | (dsgOk ? 0x40 : 0) | ((gw.f319 & 0x20) ? 0x20 : 0);
    snprintf(info, sizeof(info), "%04X%04X%04X%04X%02X",
             (uint16_t)(vchg * 1000), (uint16_t)(PYL_MIN_DSG_V * 1000), (uint16_t)(ichg * 10), (uint16_t)(idsg * 10), st);
    pylonSend(info);
    static String last63;
    if (canVerbose || last63 != info) {          // print on change only
      logPrefix("PYL"); Serial.printf("63 -> Vchg=%.1f Vdsg=%.1f Ichg=%.1f Idsg=%.1f st=%02X (chg=%d dsg=%d force=%d)\n",
                                      vchg, PYL_MIN_DSG_V, ichg, idsg, st, chgOk, dsgOk, (st >> 5) & 1);
      last63 = info;
    }
  }
}

// CAN + emulator on (used by "pylon on" and autostart)
static bool pylonStart() {
  if (canMode != CAN_ACTIVE && !canStart(CAN_ACTIVE)) { Serial.println("CAN start FAILED -> emulator stays off"); return false; }
  pylonOn = true; pylonStaleLogged = false;
  Serial.println("Pylontech emulator ON (answers ADR 02 only, silent if CAN data > 5 s old)");
  return true;
}

// green: answering inverter | yellow: CAN ok, inverter not asking | red: CAN stale (silent) | blue: emulator off
static void updateStatusLed() {
  if (STATUS_LED_PIN < 0) return;
  static uint32_t last = 0;
  if (millis() - last < 1000) return;
  last = millis();
  const uint8_t L = STATUS_LED_LEVEL;
  bool canOk = fresh(gw.t311) && fresh(gw.t313) && fresh(gw.t319);
  if (!pylonOn)                                                 STATUS_LED(0, 0, L);
  else if (!canOk)                                              STATUS_LED(L, 0, 0);
  else if (pylLastReplyMs && millis() - pylLastReplyMs < 10000) STATUS_LED(0, L, 0);
  else                                                          STATUS_LED(L, L, 0);
}

// ---------------------------------------------------------------- console
static void printHelp() {
  Serial.println(
    "commands:\n"
    "  baud <n>      RS485 baud (default 9600; try 19200/115200 if you see garbage)\n"
    "  can on        CAN 500k, send Growatt heartbeat 0x301 @1Hz (needs transceiver)\n"
    "  can listen    CAN 500k listen-only\n"
    "  can off\n"
    "  v             toggle verbose: every CAN/RS485 frame and every Pylon reply (default: 5 s summaries)\n"
    "  r             toggle raw RS485 hex echo\n"
    "  tx <text>     send <text> + CR on RS485 (e.g. tx ~20024661E00202FD33)\n"
    "  rxpin <n>     RS485 RX GPIO (default 5; 2 = CAN RX wire, only with CAN off)\n"
    "  swap          swap RS485 RX/TX pins (instead of resoldering GPIO5/GPIO6)\n"
    "  txlow         hold RS485 TX pin LOW for 15 s (wiring test: module TXD LED, A/B voltage)\n"
    "  pinscan       15 s read-only scan: prints which GPIO changes when you ground a wire\n"
    "  pylon on      emulate Pylontech for inverter (Li2) from CAN data; also starts CAN\n"
    "  pylon off\n"
    "  pylon delay <ms>  wait before replying (default 30)\n"
    "  pylon check   decode a sample 0x63 reply with our own parser (nothing sent)\n"
    "  selftest      UART internal loopback (no wires needed; also sends test bytes on TX pin)\n"
    "  stat          counters\n"
    "  help");
}

static void handleCommand(String cmd) {
  cmd.trim();
  if (!cmd.length()) return;
  if (cmd.startsWith("baud ")) {
    uint32_t b = cmd.substring(5).toInt();
    if (b >= 1200 && b <= 115200) { rsBegin(b); Serial.printf("RS485 baud = %lu\n", (unsigned long)b); }
    else Serial.println("bad baud");
  } else if (cmd.startsWith("can ") && cmd != "can off" && (rsRxPin == PIN_CAN_TX || rsRxPin == PIN_CAN_RX)) {
    Serial.printf("RS485 RX is on GPIO%d (CAN pin): rxpin 5 first\n", rsRxPin);
  } else if (cmd == "can on") {
    Serial.println(canStart(CAN_ACTIVE) ? "CAN active (heartbeat on)" : "CAN start FAILED");
  } else if (cmd == "can listen") {
    Serial.println(canStart(CAN_LISTEN) ? "CAN listen-only" : "CAN start FAILED");
  } else if (cmd == "can off") {
    canStop(); Serial.println("CAN off");
  } else if (cmd == "v") {
    canVerbose = !canVerbose; Serial.printf("verbose CAN = %d\n", canVerbose);
  } else if (cmd.startsWith("rxpin ")) {
    int p = cmd.substring(6).toInt();
    if (p < 1 || p > 48 || p == rsTxPin) Serial.println("bad pin");
    else if (canMode != CAN_OFF && (p == PIN_CAN_TX || p == PIN_CAN_RX)) Serial.println("CAN uses this pin: can off first");
    else {
      detachInterrupt(rsRxPin);
      RS.end();
      rsRxPin = p;
      rsBegin(rsBaud);
      Serial.printf("RS485 RX = GPIO%d\n", rsRxPin);
    }
  } else if (cmd.startsWith("tx ")) {
    String out = cmd.substring(3);
    RS.print(out);
    RS.write('\r');
    RS.flush();
    logPrefix("TX"); Serial.printf("%s\\r (%u bytes)\n", out.c_str(), out.length() + 1);
  } else if (cmd == "pylon on") {
    if (pylonStart()) { prefs.putBool("auto", true); Serial.println("(autostart ON saved)"); }
  } else if (cmd.startsWith("pylon delay ")) {
    pylDelayMs = cmd.substring(12).toInt();
    Serial.printf("Pylontech reply delay = %lu ms\n", (unsigned long)pylDelayMs);
  } else if (cmd.startsWith("pylon check")) {
    // self-check the frame builder with our own decoder (nothing is sent)
    String f = "20024600D012E100BB800096000080";
    uint16_t sum = 0;
    for (size_t i = 0; i < f.length(); i++) sum += (uint8_t)f[i];
    char ck[5]; snprintf(ck, sizeof(ck), "%04X", (uint16_t)(~sum + 1));
    handlePylon(f + ck);
  } else if (cmd == "pylon off") {
    pylonOn = false; prefs.putBool("auto", false);
    Serial.println("Pylontech emulator OFF (autostart OFF saved)");
  } else if (cmd == "pinscan") {
    // read-only: report level changes on all exposed GPIOs for 15 s (find which pad a wire is on)
    static const uint8_t pins[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 21,
                                   38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48};
    const int n = sizeof(pins);
    int lvl[sizeof(pins)];
    for (int k = 0; k < n; k++) { PIN_INPUT_ENABLE(GPIO_PIN_MUX_REG[pins[k]]); lvl[k] = digitalRead(pins[k]); }
    logPrefix("SCAN"); Serial.print("start:");
    for (int k = 0; k < n; k++) Serial.printf(" %u=%d", pins[k], lvl[k]);
    Serial.println("\n          touch the module pin to GND (via ~1k if you have one) now ...");
    uint32_t t0 = millis();
    while (millis() - t0 < 15000) {
      for (int k = 0; k < n; k++) {
        int v = digitalRead(pins[k]);
        if (v != lvl[k] && pins[k] != rsRxPin) {   // RS485 RX toggles with inverter traffic
          logPrefix("SCAN"); Serial.printf("GPIO%u: %d -> %d\n", pins[k], lvl[k], v);
          lvl[k] = v;
        }
      }
      delay(20);
      feedLoopWDT();
    }
    logPrefix("SCAN"); Serial.println("done");
  } else if (cmd == "txlow") {
    // hold TX pin LOW for 3 s (static test: module TXD LED, A/B driven, multimeter on the wire).
    // Inverting the UART TX signal keeps the pin routed to UART, so this also proves the routing.
    uart_set_line_inverse(UART_NUM_1, UART_SIGNAL_TXD_INV);
    logPrefix("TX"); Serial.printf("GPIO%d held LOW for 15 s (level now %d) ... measure\n", rsTxPin, digitalRead(rsTxPin));
    for (int s = 15; s > 0; s--) { delay(1000); feedLoopWDT(); logPrefix("TX"); Serial.printf("%2d s left, GPIO%d level=%d\n", s - 1, rsTxPin, digitalRead(rsTxPin)); }
    uart_set_line_inverse(UART_NUM_1, UART_SIGNAL_INV_DISABLE);
    logPrefix("TX"); Serial.printf("released (level now %d)\n", digitalRead(rsTxPin));
  } else if (cmd == "swap") {
    detachInterrupt(rsRxPin);
    RS.end();
    int t = rsRxPin; rsRxPin = rsTxPin; rsTxPin = t;
    rsBegin(rsBaud);
    Serial.printf("RS485 RX = GPIO%d, TX = GPIO%d\n", rsRxPin, rsTxPin);
  } else if (cmd == "selftest") {
    while (RS.available()) RS.read();
    uart_set_loop_back(UART_NUM_1, true);
    const char* probe = "LOOP123";
    RS.print(probe);
    RS.flush();
    delay(30);
    String got;
    while (RS.available()) got += (char)RS.read();
    uart_set_loop_back(UART_NUM_1, false);
    logPrefix("SELF");
    Serial.printf("sent \"%s\" got \"%s\" -> %s\n", probe, got.c_str(),
                  got == probe ? "UART OK" : "UART FAIL (driver/pins?)");
  } else if (cmd == "r") {
    rsRaw = !rsRaw; Serial.printf("raw RS485 = %d\n", rsRaw);
  } else if (cmd == "stat") {
    twai_status_info_t s = {};
    if (canMode != CAN_OFF) twai_get_status_info(&s);
    Serial.printf("rs485 baud=%lu bytes=%lu ascii=%lu bin=%lu | can mode=%d rx=%lu hb=%lu txErr=%lu rxErr=%lu busErr=%lu\n",
                  (unsigned long)rsBaud, (unsigned long)rsBytes, (unsigned long)rsAsciiFrames, (unsigned long)rsBinFrames,
                  canMode, (unsigned long)canRx, (unsigned long)hbSent,
                  (unsigned long)s.tx_error_counter, (unsigned long)s.rx_error_counter, (unsigned long)s.bus_error_count);
  } else {
    printHelp();
  }
}

static String cmdBuf;
static uint32_t lastCmdCharMs = 0;
static void pollConsole() {
  while (Serial.available()) {
    char c = Serial.read();
    lastCmdCharMs = millis();
    if (c == '\n' || c == '\r') { handleCommand(cmdBuf); cmdBuf = ""; }
    else if (cmdBuf.length() < 256) cmdBuf += c;
  }
  // monitors set to "no line ending" send the command without CR/LF: run it after 300 ms of silence
  if (cmdBuf.length() && millis() - lastCmdCharMs > 300) { handleCommand(cmdBuf); cmdBuf = ""; }
}

// ---------------------------------------------------------------- main
void setup() {
  Serial.begin(115200);
  Serial.setTxTimeoutMs(0);                      // never block on logs when no USB host (standalone)
  uint32_t t0 = millis();
  while (!Serial && millis() - t0 < 1000) delay(10);
  enableLoopWDT();                               // hung loop() -> reboot -> autostart again

  if (PIN_RS485_DE >= 0) { pinMode(PIN_RS485_DE, OUTPUT); digitalWrite(PIN_RS485_DE, LOW); }  // receive only
  rsBegin(rsBaud);

  Serial.println("\n=== Growatt->Anenji bridge === (\"help\" for commands)");

  prefs.begin("bridge", false);
  if (prefs.getBool("auto", true)) {
    Serial.println("autostart: starting CAN + Pylontech emulator (\"pylon off\" to disable)");
    pylonStart();
  } else {
    Serial.println("autostart disabled (\"pylon on\" to enable)");
  }
}

void loop() {
  pollConsole();
  if (!digitalRead(rsRxPin)) lowSamples++;
  pollRs485();
  pollCan();
  if (!canVerbose && millis() - lastSummary >= 5000) { lastSummary = millis(); printSummary(); }
  if (millis() - lastStat >= 5000) { lastStat = millis(); printStat(); }
  updateStatusLed();
}
