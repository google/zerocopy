#!/usr/bin/env python3
"""Compare a CovidSim integration-test output directory against a reference
output directory and the committed golden checksum file: lists files whose
SHA-512 differs from the golden, then counts differing cells in each such
tab-separated .xls table and the largest relative difference."""
import csv, os, sys
ref_dir, new_dir, golden = sys.argv[1:4]
def load(f):
    d = {}
    for l in open(f):
        l = l.strip()
        if l:
            n, h = l.split(); d[n] = h
    return d
a = load(os.path.join(new_dir, 'results.cksum')); b = load(golden)
bad = sorted(k for k in b if a.get(k) != b[k])
print(f"{new_dir}: {len(bad)} of {len(b)} hashed files differ from golden")
for fn in bad:
    if not fn.endswith('.xls'):
        print('  (non-table)', fn); continue
    A = list(csv.reader(open(os.path.join(ref_dir, fn)), delimiter='\t'))
    B = list(csv.reader(open(os.path.join(new_dir, fn)), delimiter='\t'))
    n = 0; mx = 0.0; cols = set()
    for ra, rb in zip(A, B):
        for j, (x, y) in enumerate(zip(ra, rb)):
            if x != y:
                n += 1; cols.add(A[0][j] if j < len(A[0]) else '?')
                try:
                    fx, fy = float(x), float(y)
                    mx = max(mx, abs(fx - fy) / max(abs(fx), 1e-300))
                except ValueError:
                    pass
    print(f"  {fn}: rows {len(A)}/{len(B)}, differing cells {n}, columns {len(cols)}, max rel diff {mx:.3g}")
