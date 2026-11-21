"""Compare Monte Carlo sample means with the analytic mean (sidx -1) in a gulcalc CSV.

Usage: python3 gul_mean_check.py gul.csv
Input: output of `gultocsv` (event_id,item_id,sidx,loss). For each (event,item) the
mean over sidx>0 is compared with the sidx=-1 value; sums are aggregated over all
(event,item) pairs with a positive analytic mean. Prints the aggregate ratio
sum(sample mean)/sum(analytic mean) and a naive standard error of that ratio.
"""
import sys
from collections import defaultdict

import numpy as np

samples = defaultdict(list)
analytic = {}
with open(sys.argv[1]) as f:
    next(f)
    for line in f:
        e, i, s, l = line.split(',')
        k = (int(e), int(i))
        s = int(s)
        if s > 0:
            samples[k].append(float(l))
        elif s == -1:
            analytic[k] = float(l)
keys = [k for k in analytic if analytic[k] > 0 and samples.get(k)]
sm = np.array([np.mean(samples[k]) for k in keys])
an = np.array([analytic[k] for k in keys])
ratio_per = sm / an
print(f"pairs={len(keys)} aggregate_ratio={sm.sum() / an.sum():.5f} "
      f"median_pair_ratio={np.median(ratio_per):.5f} "
      f"se_of_mean_pair_ratio={ratio_per.std(ddof=1) / np.sqrt(len(keys)):.5f}")
