"""Log-space sample skew (Bulletin 17B bias correction) and the implied log-Pearson III
upper bound exp(mu - 2*sigma/g) for each record, before and after dividing its
smallest flood by 10. Explains where EMA's skew adjustment (.momsadj in
P3_089(R).txt) binds. Usage: python lp3_bound_check.py  (run inside this directory)
"""
import csv
import glob
import math
import os

import numpy as np

for f in sorted(glob.glob(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'peaks_*.csv'))):
    site = os.path.basename(f)[6:-4]
    q = np.array([float(r['q']) for r in csv.DictReader(open(f))])
    pert = np.where(np.arange(len(q)) == q.argmin(), q.min() / 10, q)
    for lab, qq in (('orig', q), ('pert', pert)):
        x = np.log(qq[qq > 0]); n = len(x); m = x.mean(); s = x.std(ddof=1)
        g = n * np.sum((x - m) ** 3) / ((n - 1) * (n - 2) * s ** 3)
        tau = m - 2 * s / g if g < 0 else float('inf')
        ub = math.exp(tau) if tau < 700 else float('inf')
        print(f"{site} {lab}: skew={g:+.4f}  LP3 upper bound={ub:.4g}  max={qq.max():.6g}  "
              f"skew<-1.41={g < -1.41}  bound<max={tau < math.log(qq.max())}")
