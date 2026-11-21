#!/usr/bin/env python3
"""Compare reference, python-aqi and con2aqi outputs. Usage: compare.py <outdir>"""
import csv
import sys
from collections import Counter, defaultdict

out = sys.argv[1]
ref = list(csv.DictReader(open(f"{out}/ref.csv")))
py = list(csv.DictReader(open(f"{out}/pyaqi.csv")))
rc = list(csv.DictReader(open(f"{out}/con2aqi.csv")))
assert len(ref) == len(py) == len(rc)


def isint(s):
    try:
        int(s)
        return True
    except ValueError:
        return False


def cat_new(v):
    v = int(v)
    for k, (lo, hi) in enumerate([(0, 50), (51, 100), (101, 150), (151, 200), (201, 300)]):
        if lo <= v <= hi:
            return k + 1
    return 6


stats = defaultdict(Counter)
examples = defaultdict(list)
for a, b, c in zip(ref, py, rc):
    assert a["conc"] == b["conc"] == c["conc"]
    pol, s = a["pollutant"], a["conc"]
    for name, r, tie, impl in (("py2015 vs ref_old", a["ref_old"], a["tie_old"], b["py2015"]),
                               ("py2015_x vs ref_old", a["ref_old"], a["tie_old"], b["py2015_x"]),
                               ("py2024 vs ref_new", a["ref_new"], a["tie_new"], b["py2024"]),
                               ("py2024_x vs ref_new", a["ref_new"], a["tie_new"], b["py2024_x"]),
                               ("con2aqi vs ref_old", a["ref_old"], a["tie_old"], c["con2aqi"]),
                               ("con2aqi vs ref_new", a["ref_new"], a["tie_new"], c["con2aqi"])):
        key = (name, pol)
        stats[key]["n"] += 1
        if isint(r) and isint(impl):
            d = int(impl) - int(r)
            if d == 0:
                stats[key]["agree"] += 1
            else:
                kind = "tie_diff" if tie else "value_diff"
                stats[key][kind] += 1
                if not tie and name.startswith("con2aqi vs ref_new"):
                    if cat_new(impl) != cat_new(r):
                        stats[key]["category_diff"] += 1
                if len(examples[(key, kind)]) < 6:
                    examples[(key, kind)].append((s, r, impl))
        elif isint(r) != isint(impl):
            k = f"ref={r if not isint(r) else 'int'} impl={impl if not isint(impl) else 'int'}"
            stats[key][k] += 1
            if len(examples[(key, k)]) < 4:
                examples[(key, k)].append((s, r, impl))
        else:
            stats[key]["both_nonint"] += 1
for key in sorted(stats):
    print(key, dict(stats[key]))
print()
for k in sorted(examples):
    print(k, examples[k])
# tie census
tie_old = Counter(a["pollutant"] for a in ref if a["tie_old"])
tie_new = Counter(a["pollutant"] for a in ref if a["tie_new"])
print("\nexact .5 ties in reference (old table):", dict(tie_old))
print("exact .5 ties in reference (2024 table):", dict(tie_new))
