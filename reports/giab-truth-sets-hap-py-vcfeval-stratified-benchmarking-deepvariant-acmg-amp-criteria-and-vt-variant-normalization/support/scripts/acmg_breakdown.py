#!/usr/bin/env python3
"""Transition breakdown for acmg_probe.py systems (Richards re-encoding vs points)."""
import itertools, os, runpy, sys
from collections import Counter
sys.argv = ['acmg_probe.py', sys.argv[1]]
import io, contextlib
buf = io.StringIO()
with contextlib.redirect_stdout(buf):
    g = runpy.run_path(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'acmg_probe.py'))
R, P = g['richards'], g['points']
box = g['box']
po = [c for c in box if c[4] == 0 and c[5] == 0 and c[6] == 0]
bo = [c for c in box if c[0] == 0 and c[1] == 0 and c[2] == 0 and c[3] == 0]
mx = g['mixed']
for name, sub in (('pathogenic_only', po), ('benign_only', bo), ('mixed', mx)):
    t = Counter((R(*c), P(*c)[0]) for c in sub if R(*c) != P(*c)[0])
    print(name, len(sub), sum(t.values()), dict(t.most_common()))
# mixed: Richards contradiction (both sides fire) vs not
both = [c for c in mx if R(c[0],c[1],c[2],c[3],0,0,0) != 'VUS' and R(0,0,0,0,c[4],c[5],c[6]) != 'VUS']
print('mixed where both Richards sides fire (contradiction->VUS):', len(both))
print('  of which points also VUS:', sum(1 for c in both if P(*c)[0] == 'VUS'))
