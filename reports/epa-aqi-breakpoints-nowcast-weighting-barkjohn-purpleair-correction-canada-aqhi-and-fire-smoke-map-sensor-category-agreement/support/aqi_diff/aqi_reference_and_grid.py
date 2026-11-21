#!/usr/bin/env python3
"""Differential test of two open US AQI implementations against an exact
reference built from the EPA Technical Assistance Document (TAD) tables.

Reference semantics (TAD EPA-454/B-18-007 Table 5 for the pre-2024 table;
TAD EPA-454/B-24-002 / EPA-403/B-26-003 Table 6 for the 2024 table):
  1. truncate the concentration to the pollutant precision
     (O3 3 decimals; PM2.5 and CO 1 decimal; PM10, SO2, NO2 integer),
  2. find the band with BP_lo <= C <= BP_hi,
  3. I = (I_hi - I_lo) / (BP_hi - BP_lo) * (C - BP_lo) + I_lo, exact rational,
  4. round to the nearest integer; an exact .5 tie is reported separately
     (the TAD does not define tie handling; its worked example 125.5 -> 126).
Blank cells (1-h O3 below 0.125 ppm, 8-h O3 above 0.200 ppm) are 'NA'.
Above the top of the table: the 2024 table extends its single Hazardous band
(footnote 4 of Table 6); the pre-2024 table is 'BEYOND' (no reference value).

Writes grid.csv (inputs) for the R side and ref.csv (reference outputs).
Usage: python3 aqi_reference_and_grid.py <outdir>
"""
import csv
import sys
from decimal import Decimal, ROUND_DOWN
from fractions import Fraction

D = Decimal
AQI_OLD = [(0, 50), (51, 100), (101, 150), (151, 200), (201, 300), (301, 400), (401, 500)]
AQI_NEW = [(0, 50), (51, 100), (101, 150), (151, 200), (201, 300), (301, 500)]
PREC = {"pm25": D("0.1"), "pm10": D("1"), "co": D("0.1"), "so2": D("1"), "no2": D("1"),
        "o3_8h": D("0.001"), "o3_1h": D("0.001")}

OLD = {  # TAD 2018 Table 5 (identical to the 2016 TAD values encoded by con2aqi)
    "o3_8h": [("0.000", "0.054"), ("0.055", "0.070"), ("0.071", "0.085"), ("0.086", "0.105"), ("0.106", "0.200"), None, None],
    "o3_1h": [None, None, ("0.125", "0.164"), ("0.165", "0.204"), ("0.205", "0.404"), ("0.405", "0.504"), ("0.505", "0.604")],
    "pm25": [("0.0", "12.0"), ("12.1", "35.4"), ("35.5", "55.4"), ("55.5", "150.4"), ("150.5", "250.4"), ("250.5", "350.4"), ("350.5", "500.4")],
    "pm10": [("0", "54"), ("55", "154"), ("155", "254"), ("255", "354"), ("355", "424"), ("425", "504"), ("505", "604")],
    "co": [("0.0", "4.4"), ("4.5", "9.4"), ("9.5", "12.4"), ("12.5", "15.4"), ("15.5", "30.4"), ("30.5", "40.4"), ("40.5", "50.4")],
    "so2": [("0", "35"), ("36", "75"), ("76", "185"), ("186", "304"), ("305", "604"), ("605", "804"), ("805", "1004")],
    "no2": [("0", "53"), ("54", "100"), ("101", "360"), ("361", "649"), ("650", "1249"), ("1250", "1649"), ("1650", "2049")],
}
NEW = {  # TAD 2024/2026 Table 6; Hazardous band top = concentration of AQI 500 (footnote 4)
    "o3_8h": [("0.000", "0.054"), ("0.055", "0.070"), ("0.071", "0.085"), ("0.086", "0.105"), ("0.106", "0.200"), None],
    "o3_1h": [None, None, ("0.125", "0.164"), ("0.165", "0.204"), ("0.205", "0.404"), ("0.405", "0.604")],
    "pm25": [("0.0", "9.0"), ("9.1", "35.4"), ("35.5", "55.4"), ("55.5", "125.4"), ("125.5", "225.4"), ("225.5", "325.4")],
    "pm10": [("0", "54"), ("55", "154"), ("155", "254"), ("255", "354"), ("355", "424"), ("425", "604")],
    "co": [("0.0", "4.4"), ("4.5", "9.4"), ("9.5", "12.4"), ("12.5", "15.4"), ("15.5", "30.4"), ("30.5", "50.4")],
    "so2": [("0", "35"), ("36", "75"), ("76", "185"), ("186", "304"), ("305", "604"), ("605", "1004")],
    "no2": [("0", "53"), ("54", "100"), ("101", "360"), ("361", "649"), ("650", "1249"), ("1250", "2049")],
}


def ref(table, aqi_bands, pol, s):
    c = D(s)
    if c < 0:
        return "NEG", ""
    t = c.quantize(PREC[pol], rounding=ROUND_DOWN)
    bands = table[pol]
    filled = [(i, b) for i, b in enumerate(bands) if b is not None]
    for i, b in filled:
        lo, hi = D(b[0]), D(b[1])
        if lo <= t <= hi:
            break
    else:
        lo0 = D(filled[0][1][0]); hi_last = D(filled[-1][1][1])
        if t < lo0:
            return "NA", ""
        if t > hi_last:
            last_i = filled[-1][0]
            if last_i != len(aqi_bands) - 1:
                return "NA", ""  # e.g. 8-h O3 above 0.200: blank, use 1-h O3
            if aqi_bands is AQI_OLD:
                return "BEYOND", ""
            i, b = filled[-1]
            lo, hi = D(b[0]), D(b[1])
        else:
            return "GAP?", ""  # cannot happen after truncation
    ilo, ihi = aqi_bands[i]
    v = Fraction(ihi - ilo) / (Fraction(hi) - Fraction(lo)) * (Fraction(t) - Fraction(lo)) + ilo
    fl = v.numerator // v.denominator
    frac = v - fl
    tie = "TIE" if frac == Fraction(1, 2) else ""
    r = fl + (1 if frac >= Fraction(1, 2) else 0)  # half-up
    return str(r), tie


def grid():
    rows = []
    for pol in PREC:
        p = PREC[pol]
        tops = [D(b[1]) for b in OLD[pol] if b] + [D(b[1]) for b in NEW[pol] if b]
        top = max(tops)
        n = int(top / p)
        vals = set()
        for k in range(0, n + 1):
            c = p * k
            vals.add(c)
            vals.add(c + p / 2)        # off-grid: exercises truncation and the gaps between bands
            vals.add(c + p * D("0.99"))  # just below the next grid point
        for extra in (-p, top + p, top * D("1.5"), top * 2):
            vals.add(extra)
        for v in sorted(vals):
            rows.append((pol, format(v.normalize() if v != 0 else D(0), "f")))
    return rows


def main(outdir):
    rows = grid()
    with open(f"{outdir}/grid.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["pollutant", "conc"])
        w.writerows(rows)
    with open(f"{outdir}/ref.csv", "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["pollutant", "conc", "ref_old", "tie_old", "ref_new", "tie_new"])
        for pol, s in rows:
            ro, to = ref(OLD, AQI_OLD, pol, s)
            rn, tn = ref(NEW, AQI_NEW, pol, s)
            w.writerow([pol, s, ro, to, rn, tn])
    print("grid rows:", len(rows))


if __name__ == "__main__":
    main(sys.argv[1])
