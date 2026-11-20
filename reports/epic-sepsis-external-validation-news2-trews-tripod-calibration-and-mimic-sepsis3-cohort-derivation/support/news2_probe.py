#!/usr/bin/env python3
"""Toy transcription of the NEWS2 scoring chart (Royal College of Physicians,
2017, Chart 1) and trigger thresholds (Chart 2). Standard library only.

This is the author's own transcription of the published chart bands, not an
official implementation. It is used to show (a) how the published bands leave
gaps for non-integer or finer-resolution measurements, and (b) the
non-monotone SpO2 Scale 2 rule. Band edges as printed on Chart 1:
  Respiration rate: <=8:3  9-11:1  12-20:0  21-24:2  >=25:3
  SpO2 Scale 1:     <=91:3  92-93:2  94-95:1  >=96:0
  SpO2 Scale 2:     <=83:3  84-85:2  86-87:1  88-92:0  >=93 on air:0
                    93-94 on O2:1  95-96 on O2:2  >=97 on O2:3
  Air or oxygen:    oxygen:2  air:0
  Systolic BP:      <=90:3  91-100:2  101-110:1  111-219:0  >=220:3
  Pulse:            <=40:3  41-50:1  51-90:0  91-110:1  111-130:2  >=131:3
  Consciousness:    Alert:0  new Confusion/Voice/Pain/Unresponsive:3
  Temperature:      <=35.0:3  35.1-36.0:1  36.1-38.0:0  38.1-39.0:1  >=39.1:2
"""

def band(x, table):
    """table: list of (lo, hi, score) with inclusive bounds; returns score or None for a gap."""
    for lo, hi, s in table:
        if lo <= x <= hi:
            return s
    return None

INF = float("inf")
RR = [(-INF, 8, 3), (9, 11, 1), (12, 20, 0), (21, 24, 2), (25, INF, 3)]
SBP = [(-INF, 90, 3), (91, 100, 2), (101, 110, 1), (111, 219, 0), (220, INF, 3)]
HR = [(-INF, 40, 3), (41, 50, 1), (51, 90, 0), (91, 110, 1), (111, 130, 2), (131, INF, 3)]
TEMP = [(-INF, 35.0, 3), (35.1, 36.0, 1), (36.1, 38.0, 0), (38.1, 39.0, 1), (39.1, INF, 2)]
SPO2_1 = [(-INF, 91, 3), (92, 93, 2), (94, 95, 1), (96, INF, 0)]

def spo2_scale2(x, on_oxygen):
    if x <= 83: return 3
    if 84 <= x <= 85: return 2
    if 86 <= x <= 87: return 1
    if 88 <= x <= 92: return 0
    if x >= 93 and not on_oxygen: return 0
    if 93 <= x <= 94: return 1
    if 95 <= x <= 96: return 2
    if x >= 97: return 3
    return None

def news2(rr, spo2, scale2, on_o2, sbp, hr, alert, temp):
    parts = [band(rr, RR),
             spo2_scale2(spo2, on_o2) if scale2 else band(spo2, SPO2_1),
             2 if on_o2 else 0,
             band(sbp, SBP), band(hr, HR), 0 if alert else 3, band(temp, TEMP)]
    if any(p is None for p in parts):
        return None, parts
    total = sum(parts)
    red = any(p == 3 for p in parts)
    if total >= 7: risk = "high (>=7)"
    elif total >= 5: risk = "medium (5-6)"
    elif red: risk = "low-medium (single parameter = 3)"
    else: risk = "low (0-4)"
    return (total, risk), parts

print("Gap probe: values falling between printed bands")
for name, tab, vals in [("temp", TEMP, [35.0, 35.05, 35.1, 36.05, 38.05, 39.05]),
                        ("sbp", SBP, [90, 90.5, 91]), ("rr", RR, [8, 8.5, 9])]:
    for v in vals:
        print(f"  {name}={v}: score={band(v, tab)}")
print()
print("SpO2 Scale 2 non-monotonicity (score vs SpO2):")
for v in [86, 88, 92, 93, 95, 97, 99]:
    print(f"  SpO2={v}: on air -> {spo2_scale2(v, False)}, on O2 -> {spo2_scale2(v, True)}")
print()
print("Trigger examples:")
print("  normal adult:", news2(16, 97, False, False, 125, 75, True, 37.0))
print("  single red parameter (new confusion):", news2(16, 97, False, False, 125, 75, False, 37.0))
print("  aggregate 5:", news2(22, 95, False, False, 105, 95, True, 37.0))
print("  aggregate 7:", news2(25, 93, False, True, 100, 95, True, 37.0))
