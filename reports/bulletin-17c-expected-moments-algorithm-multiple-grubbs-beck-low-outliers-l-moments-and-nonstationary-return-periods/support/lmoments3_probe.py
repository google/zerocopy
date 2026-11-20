"""Fit GEV by L-moments with the pinned lmoments3 source tree and compare the
0.01-AEP quantile with lmomco and lmom (from flood_probe_results.csv).
Usage: python lmoments3_probe.py <lmoments3 source root> <flood_out dir>"""
import csv
import glob
import os
import sys
import time

sys.path.insert(0, sys.argv[1])
import lmoments3 as lm  # noqa: E402
from lmoments3 import distr  # noqa: E402

out = sys.argv[2]
ref = {r['site']: r for r in csv.DictReader(open(os.path.join(out, 'flood_probe_results.csv')))}
print(f"{'site':>9} {'n':>4} {'l1':>10} {'l2':>10} {'t3':>8} {'lmoments3 GEV Q100':>19} {'lmomco':>11} {'lmom':>11} {'rel(lm3/lmomco)-1':>18} {'ms':>7}")
worst = 0.0
for f in sorted(glob.glob(os.path.join(out, 'peaks_*.csv'))):
    site = os.path.basename(f)[6:-4]
    q = [float(r['q']) for r in csv.DictReader(open(f))]
    t0 = time.perf_counter()
    ratios = lm.lmom_ratios(q, nmom=4)
    para = distr.gev.lmom_fit(q)
    q100 = float(distr.gev.ppf(0.99, **para))
    ms = (time.perf_counter() - t0) * 1e3
    a = float(ref[site]['lmomco_gev_q100']); b = float(ref[site]['lmom_gev_q100'])
    rel = q100 / a - 1
    worst = max(worst, abs(rel))
    print(f"{site:>9} {len(q):>4} {ratios[0]:10.2f} {ratios[1]:10.2f} {ratios[2]:8.4f} {q100:19.6g} {a:11.6g} {b:11.6g} {rel:+18.2e} {ms:7.2f}")
print('max |lmoments3/lmomco - 1| =', worst)
