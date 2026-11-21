"""Paired comparison of two gulcalc CSV runs that share random numbers.

Usage: python3 gul_paired_shift.py base.csv stressed.csv
For every (event,item) present in both files, computes the shift in the analytic mean
(sidx -1) and the shift in the Monte Carlo sample mean (mean over sidx>0) between the two
runs, and prints sum(sample shift)/sum(analytic shift). If samples honoured the declared
bin "interpolation" (mean) values, the ratio would be 1.
"""
import sys
from collections import defaultdict

import numpy as np


def load(fn):
    samples = defaultdict(list)
    analytic = {}
    with open(fn) as f:
        next(f)
        for line in f:
            e, i, s, l = line.split(',')
            k = (int(e), int(i))
            s = int(s)
            if s > 0:
                samples[k].append(float(l))
            elif s == -1:
                analytic[k] = float(l)
    return samples, analytic


sb, ab = load(sys.argv[1])
ss, as_ = load(sys.argv[2])
keys = [k for k in ab if k in as_ and sb.get(k) and ss.get(k)]
d_an = np.array([as_[k] - ab[k] for k in keys])
d_sm = np.array([np.mean(ss[k]) - np.mean(sb[k]) for k in keys])
print(f"pairs={len(keys)} sum_analytic_shift={d_an.sum():.1f} "
      f"sum_sample_shift={d_sm.sum():.1f} ratio={d_sm.sum() / d_an.sum():.4f}")
