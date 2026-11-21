#!/usr/bin/env python3
"""Refined con2aqi / python-aqi analysis: on-grid vs off-grid inputs, category flips, band edges.
Usage: refine.py <outdir>"""
import csv
import sys
from collections import Counter, defaultdict
from decimal import Decimal as D

out = sys.argv[1]
PREC = {"pm25": D("0.1"), "pm10": D("1"), "co": D("0.1"), "so2": D("1"), "no2": D("1"), "o3_8h": D("0.001"), "o3_1h": D("0.001")}
ref = list(csv.DictReader(open(f"{out}/ref.csv")))
py = list(csv.DictReader(open(f"{out}/pyaqi.csv")))
rc = list(csv.DictReader(open(f"{out}/con2aqi.csv")))


def isint(s):
    try:
        int(s)
        return True
    except ValueError:
        return False


def cat(v):
    v = int(v)
    for k, hi in enumerate([50, 100, 150, 200, 300]):
        if v <= hi:
            return k + 1
    return 6


S = defaultdict(Counter)
EX = defaultdict(list)
for a, b, c in zip(ref, py, rc):
    pol, s = a["pollutant"], a["conc"]
    x = D(s)
    ongrid = x >= 0 and (x % PREC[pol]) == 0
    g = "on" if ongrid else "off"
    r, impl = a["ref_old"], c["con2aqi"]
    if isint(r) and isint(impl):
        S[(pol, g)]["n_int"] += 1
        d = int(impl) - int(r)
        S[(pol, g)][f"d={d:+d}"] += 1
        if cat(impl) != cat(r):
            S[(pol, g)]["cat_flip"] += 1
            if len(EX[(pol, g)]) < 8:
                EX[(pol, g)].append((s, r, impl))
    # python-aqi half-even check on ties
    if a["tie_old"] and isint(b["py2015"]):
        rv = int(r)
        S[(pol, "tie")]["n"] += 1
        S[(pol, "tie")]["py_is_half_even" if int(b["py2015"]) % 2 == 0 and abs(int(b["py2015"]) - (rv - 0.5)) == 0.5 else "py_not_half_even"] += 1
for k in sorted(S):
    print(k, dict(sorted(S[k].items())))
print()
for k in sorted(EX):
    print("category flips con2aqi vs old-table reference", k, EX[k])
