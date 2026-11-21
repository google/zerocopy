#!/usr/bin/env python3
"""Compare BCRA (R) and bcra (JavaScript) outputs on shared profiles, and the
R outputs against the R-reference values recorded in the JavaScript port.

Usage: python3 compare.py <bcra-js checkout> <profiles.csv> <out_r.csv> <out_js.csv>
"""
import csv, glob, json, math, os, sys
from collections import Counter

src, prof_p, r_p, js_p = sys.argv[1:5]
prof = {r['ID']: r for r in csv.DictReader(open(prof_p))}
rr = {}
for r in csv.DictReader(open(r_p)):
    rr[(r['ID'], r['Mode'])] = r
js = {r['ID']: r for r in csv.DictReader(open(js_p))}

def fnum(x):
    try:
        v = float(x)
        return None if math.isnan(v) else v
    except (TypeError, ValueError):
        return None

# 1. R now vs R-reference recorded upstream.
ref = {}
for f in glob.glob(os.path.join(src, 'packages/bcra/test/fixtures/r-reference/*.json')):
    if f.endswith('summary.json'):
        continue
    for r in json.load(open(f)):
        ref[str(r['ID'])] = r
maxd, n, mism = 0.0, 0, []
for i, r in ref.items():
    cur = rr[(i, 'frame')]
    n += 1
    if str(int(r['Error_Ind'])) != cur['Error_Ind']:
        mism.append((i, 'Error_Ind', r['Error_Ind'], cur['Error_Ind']))
    a, b = r.get('AbsRisk'), fnum(cur['AbsRisk'])
    if a is None and b is None:
        continue
    if a is None or b is None:
        mism.append((i, 'AbsRisk', a, b)); continue
    maxd = max(maxd, abs(a - b))
print(f'[1] R(now) vs R-reference fixtures: rows={n} Error_Ind/NA mismatches={len(mism)} max|dAbsRisk|={maxd:.3g} (percentage points)')
for m in mism[:10]:
    print('    ', m)

# 2. R vs JS on every profile (frame mode).
cls = Counter(); maxd_ab = {}; maxd_av = 0.0; details = []
for i, p in prof.items():
    r = rr[(i, 'frame')]; j = js[i]
    r_ok = r['Error_Ind'] == '0' and fnum(r['AbsRisk']) is not None
    j_ok = j['Success'] == 'true' and fnum(j['AbsRisk']) is not None
    if r_ok and j_ok:
        d = abs(fnum(r['AbsRisk']) - fnum(j['AbsRisk']))
        maxd_ab[p['Set']] = max(maxd_ab.get(p['Set'], 0.0), d)
        if fnum(r['AvgRisk']) is not None and fnum(j['AvgRisk']) is not None:
            maxd_av = max(maxd_av, abs(fnum(r['AvgRisk']) - fnum(j['AvgRisk'])))
        key = 'both valid, |d|<=1e-9' if d <= 1e-9 else ('both valid, |d|<=1e-6' if d <= 1e-6 else 'both valid, |d|>1e-6')
    elif not r_ok and not j_ok:
        key = 'both reject'
    elif r_ok and not j_ok:
        key = 'R accepts, JS rejects'
    else:
        key = 'R rejects, JS accepts'
    cls[(p['Set'], key)] += 1
    if p['Set'] == 'edge' or key not in ('both reject', 'both valid, |d|<=1e-9'):
        details.append((i, p['Label'], key, r['Error_Ind'], r['NB_Cat'], r['AF_Cat'], r['AbsRisk'], j['Success'], j['AbsRisk'], j['Errors'][:70]))
print('[2] R vs JS classification (frame mode):')
for k in sorted(cls):
    print(f'     {k[0]:8s} {k[1]:28s} {cls[k]}')
print('     max |dAbsRisk| by set where both valid:', {k: float(f'{v:.3g}') for k, v in maxd_ab.items()})
print(f'     max |dAvgRisk| where both valid: {maxd_av:.3g}')
print('[3] Edge rows and every non-trivial disagreement:')
print('     ID | label | class | R.Error_Ind | R.NB_Cat | R.AF_Cat | R.AbsRisk | JS.success | JS.AbsRisk | JS.errors')
for d in details:
    print('     ' + ' | '.join(str(x) for x in d))
print('[4] Solo (one-row data frame) runs in R:')
for (i, mode), r in rr.items():
    if mode == 'solo':
        print(f"     {i} | {prof[i]['Label']} | Error_Ind={r['Error_Ind']} CharRace={r['CharRace']} RR1={r['RR1']} AbsRisk={r['AbsRisk']} RError={r['RError']}")
