#!/usr/bin/env python3
"""Generate shared synthetic Gail-model input profiles for a differential test.

Usage: python3 gen_profiles.py <bcra-js checkout> <out profiles.csv>

Three sets are produced (column `Set`):
  fixture - the inputs of every row in the R-reference JSON fixtures shipped in
            packages/bcra/test/fixtures/r-reference/ of the JavaScript port
            (outputs recorded there by the R package are compared separately);
  edge    - hand-written boundary and malformed inputs (see EDGE below);
  random  - 2000 pseudo-random profiles drawn from the documented input domains
            with a fixed seed.
Rows with Solo=1 are additionally run alone (a one-row data frame) in R,
because some R checks behave differently depending on the other rows.
All values are synthetic; no person is described.
"""
import csv, glob, json, os, random, sys

src, out = sys.argv[1], sys.argv[2]
FIELDS = ['ID', 'T1', 'T2', 'N_Biop', 'HypPlas', 'AgeMen', 'Age1st', 'N_Rels', 'Race']
rows = []
fx = sorted(glob.glob(os.path.join(src, 'packages/bcra/test/fixtures/r-reference/*.json')))
for f in fx:
    if f.endswith('summary.json'):
        continue
    for r in json.load(open(f)):
        rows.append({**{k: r[k] for k in FIELDS}, 'Set': 'fixture', 'Solo': 0,
                     'Label': os.path.basename(f)[:-5] + ':' + str(r.get('Description', ''))})

base = dict(T1=40, T2=50, N_Biop=1, HypPlas=99, AgeMen=12, Age1st=25, N_Rels=1, Race=1)
EDGE = [
    ('N_Biop=-1', dict(N_Biop=-1)),
    ('N_Biop=-5', dict(N_Biop=-5)),
    ('N_Biop=1.5', dict(N_Biop=1.5)),
    ('N_Biop=150', dict(N_Biop=150)),
    ('N_Biop=98', dict(N_Biop=98)),
    ('N_Biop=2 control', dict(N_Biop=2)),
    ('AgeMen=5', dict(AgeMen=5)),
    ('AgeMen=0', dict(AgeMen=0)),
    ('AgeMen=13.5', dict(AgeMen=13.5)),
    ('Age1st=-3 AgeMen=99', dict(Age1st=-3, AgeMen=99)),
    ('N_Rels=1.5', dict(N_Rels=1.5)),
    ('N_Rels=150', dict(N_Rels=150)),
    ('Race2 Age1st>T1', dict(Race=2, Age1st=45)),
    ('Race1 Age1st>T1 control', dict(Race=1, Age1st=45)),
    ('Race2 Age1st<AgeMen', dict(Race=2, Age1st=10)),
    ('Race2 AgeMen=10', dict(Race=2, AgeMen=10)),
    ('Race=1.5 in frame', dict(Race=1.5)),
    ('Race=12 in frame', dict(Race=12)),
    ('all unknown (99)', dict(N_Biop=99, HypPlas=99, AgeMen=99, Age1st=99, N_Rels=99)),
    ('explicit lowest categories', dict(N_Biop=0, HypPlas=99, AgeMen=14, Age1st=19, N_Rels=0)),
    ('Race3 all unknown (99)', dict(Race=3, N_Biop=99, HypPlas=99, AgeMen=99, Age1st=99, N_Rels=99)),
    ('Race3 explicit lowest', dict(Race=3, N_Biop=0, HypPlas=99, AgeMen=14, Age1st=19, N_Rels=0)),
    ('Race3 N_Biop=0 HypPlas=1', dict(Race=3, N_Biop=0, HypPlas=1)),
    ('HypPlas=0', dict(HypPlas=0)),
    ('HypPlas=1', dict(HypPlas=1)),
    ('crosses age 50', dict(T1=49.5, T2=50.5)),
    ('T1=20 T2=20.5 nulliparous', dict(T1=20, T2=20.5, Age1st=98)),
]
SOLO = [
    ('solo Race=12', dict(Race=12)),
    ('solo Race=0', dict(Race=0)),
    ('solo Race=1.5', dict(Race=1.5)),
    ('solo Race=-1', dict(Race=-1)),
    ('solo valid control', dict()),
]
nid = 10001
for label, upd in EDGE:
    rows.append({'ID': nid, **base, **upd, 'Set': 'edge', 'Solo': 0, 'Label': label}); nid += 1
for label, upd in SOLO:
    rows.append({'ID': nid, **base, **upd, 'Set': 'edge', 'Solo': 1, 'Label': label}); nid += 1

rng = random.Random(20261121)
nid = 20001
for _ in range(2000):
    t1 = round(rng.uniform(20, 85), 1)
    t2 = min(90.0, round(t1 + rng.choice([5, 10, 20, 90]), 1))
    nb = rng.choice([0, 1, 2, 3, 99])
    hp = 99 if nb in (0, 99) else rng.choice([0, 1, 99])
    am = rng.choice(list(range(8, 18)) + [99])
    lo = am if am != 99 else 12
    a1 = rng.choice(list(range(lo, int(t1) + 1)) + [98, 99]) if lo <= int(t1) else rng.choice([98, 99])
    nr = rng.choice([0, 1, 2, 3, 99])
    race = rng.randint(1, 11)
    rows.append(dict(ID=nid, T1=t1, T2=t2, N_Biop=nb, HypPlas=hp, AgeMen=am, Age1st=a1,
                     N_Rels=nr, Race=race, Set='random', Solo=0, Label='random'))
    nid += 1

with open(out, 'w', newline='') as fh:
    w = csv.DictWriter(fh, fieldnames=FIELDS + ['Set', 'Solo', 'Label'])
    w.writeheader()
    w.writerows(rows)
print(f'wrote {len(rows)} profiles to {out}')
