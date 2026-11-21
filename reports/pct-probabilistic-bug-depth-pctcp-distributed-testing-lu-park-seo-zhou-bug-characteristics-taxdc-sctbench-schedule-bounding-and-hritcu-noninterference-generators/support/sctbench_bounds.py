#!/usr/bin/env python3
"""Derived table: PCT worst-case bound 1/(n k^(d-1)) for SCTBench's recorded (maxThreads, maxSteps).

Input: benchmarks/buggy.txt of mc-imperial/sctbench @ d59ab26ddaedcd575ffb6a1f5e9711f7d6d2d9f2.
Columns per scripts/run_many.py lines 141-145: suite test maxThreads maxSteps.
Lines starting with '#' are skipped exactly as run_many.py skips them.
For each benchmark and d in {1,2,3}: p = 1/(n * k^(d-1)) and the number of independent PCT runs
needed for a 99% detection guarantee, N99 = ceil(ln(0.01) / ln(1-p)).

Usage: python3 sctbench_bounds.py <path/to/buggy.txt>
"""
import math, sys

def n99(p):
    if p >= 1:
        return 1
    return math.ceil(math.log(0.01) / math.log1p(-p))

rows = []
for line in open(sys.argv[1]):
    line = line.strip()
    if not line or line.startswith('#'):
        continue
    suite, test, n, k = line.split()[:4]
    rows.append((suite, test, int(n), int(k)))
print('suite\ttest\tn\tk\tp(d=1)\tp(d=2)\tp(d=3)\tN99(d=2)\tN99(d=3)\tN99(d=3)<=100000')
within = {2: 0, 3: 0}
for suite, test, n, k in rows:
    ps = [1.0 / (n * k ** (d - 1)) for d in (1, 2, 3)]
    a, b = n99(ps[1]), n99(ps[2])
    within[2] += a <= 100000
    within[3] += b <= 100000
    print(f'{suite}\t{test}\t{n}\t{k}\t{ps[0]:.3g}\t{ps[1]:.3g}\t{ps[2]:.3g}\t{a}\t{b}\t{b <= 100000}')
print(f'# benchmarks={len(rows)} N99<=100000: d=2 -> {within[2]}, d=3 -> {within[3]}')
ks = sorted(k for *_, k in rows); ns = sorted(n for _, _, n, _ in rows)
print(f'# k: min={ks[0]} median={ks[len(ks)//2]} max={ks[-1]}; n: min={ns[0]} median={ns[len(ns)//2]} max={ns[-1]}')
