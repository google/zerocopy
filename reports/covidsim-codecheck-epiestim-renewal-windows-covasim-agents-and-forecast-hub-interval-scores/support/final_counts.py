#!/usr/bin/env python3
"""Print final-row cumulative counts (cumMild, cumSARI, cumCritical, cumDeath)
from CovidSim *.avNE.severity.xls tables in the given output directories."""
import csv, sys
for d in sys.argv[1:]:
    for run in ('results-noint', 'results-int'):
        rows = list(csv.reader(open(f"{d}/{run}.avNE.severity.xls"), delimiter='\t'))
        h = rows[0]; last = [r for r in rows[1:] if len(r) == len(h)][-1]
        vals = {c: float(last[h.index(c)]) for c in ('cumMild', 'cumSARI', 'cumCritical', 'cumDeath')}
        print(f"{d:32s} {run:14s} " + ' '.join(f"{k}={v:.0f}" for k, v in vals.items()))
