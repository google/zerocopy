#!/usr/bin/env python3
"""Census of exact .5 ties on the truncated grid: exact value, half-up, half-even,
python-aqi result, con2aqi result. Usage: ties.py <outdir>"""
import csv
import sys
from decimal import Decimal as D, ROUND_DOWN

out = sys.argv[1]
ref = list(csv.DictReader(open(f"{out}/ref.csv")))
py = {(r["pollutant"], r["conc"]): r for r in csv.DictReader(open(f"{out}/pyaqi.csv"))}
rc = {(r["pollutant"], r["conc"]): r for r in csv.DictReader(open(f"{out}/con2aqi.csv"))}
PREC = {"pm25": D("0.1"), "pm10": D("1"), "co": D("0.1"), "so2": D("1"), "no2": D("1"), "o3_8h": D("0.001"), "o3_1h": D("0.001")}
seen = set()
print("table pollutant conc exact half_up half_even python_aqi con2aqi")
for tab, col, tiecol, pycol in (("old", "ref_old", "tie_old", "py2015"), ("2024", "ref_new", "tie_new", "py2024")):
    for a in ref:
        if not a[tiecol]:
            continue
        x = D(a["conc"])
        if x % PREC[a["pollutant"]] != 0:
            continue  # on-grid representatives only
        k = (tab, a["pollutant"], a["conc"])
        if k in seen:
            continue
        seen.add(k)
        hu = int(a[col])
        exact = hu - D("0.5")
        he = hu if hu % 2 == 0 else hu - 1
        p = py[(a["pollutant"], a["conc"])][pycol]
        c = rc[(a["pollutant"], a["conc"])]["con2aqi"]
        flag = "" if int(p) == he else "  <-- python-aqi differs from exact half-even"
        print(tab, a["pollutant"], a["conc"], exact, hu, he, p, c, flag)
