#!/usr/bin/env python3
"""Derived-arithmetic checks on published newborn-screening performance figures.

Inputs are numbers printed in the cited papers (see REPORT.md, Evidence). Outputs are
arithmetic consequences only; they are not new measurements of any screening programme.
Also checks how a NaN analyte value falls through a '<' comparison (the pattern used by a
public notebook's classify_cutoff), using numpy float64 as pandas would pass it.
"""
import math
import numpy as np

print('== Peng et al. 2020, Table (screen positives, California)')
rows = {  # disorder: (confirmed positive, FP first tier, PPV first tier %, FP after RF, PPV after RF %)
    'GA-1': (48, 1344, 3.10, 150, 22.30),
    'MMA': (103, 502, 16.40, 276, 26.40),
    'OTCD': (24, 496, 3.50, 11, 62.10),
    'VLCADD': (60, 200, 23.10, 196, 23.40),
}
for d, (tp, fp1, ppv1, fp2, ppv2) in rows.items():
    red = 100 * (1 - fp2 / fp1)
    p1 = 100 * tp / (tp + fp1); p2 = 100 * tp / (tp + fp2)
    # TP count that reproduces each printed PPV exactly: tp = ppv*fp/(1-ppv)
    t1 = ppv1 / 100 * fp1 / (1 - ppv1 / 100); t2 = ppv2 / 100 * fp2 / (1 - ppv2 / 100)
    print(f'{d:7s} FP reduction {red:5.1f}% | PPV from table counts {p1:5.1f}% -> {p2:5.1f}% '
          f'(printed {ppv1}% -> {ppv2}%) | TP implied by printed PPVs {t1:5.1f}, {t2:5.1f}')

print('\n== Hall et al. 2014, California Jan-Jun 2012 (actual cutoff system)')
n, fpr, ppv = 176186, 0.26 / 100, 0.10
fp = n * fpr; tp = fp * ppv / (1 - ppv)
print(f'FP = {fp:.0f} (paper reports 454 FP reclassified); implied TP = {tp:.0f}')

print('\n== Hall et al. 2014, Minnesota 2013 prospective (tools as primary interpretation)')
n, ref, tp = 71207, 55, 38
print(f'PPV = {100*tp/ref:.1f}% (printed 69%); FPR = {100*(ref-tp)/n:.4f}% (printed 0.024%)')

print('\n== Matern et al. 2007, Mayo programme with second-tier tests')
fpr, ppv, det = 0.09 / 100, 0.41, 1 / 1672
tp_per_1e5 = 1e5 * det; fp_per_1e5 = 1e5 * fpr
print(f'per 100,000: TP {tp_per_1e5:.1f}, FP {fp_per_1e5:.1f}, PPV implied {100*tp_per_1e5/(tp_per_1e5+fp_per_1e5):.1f}% (printed 41%)')

print('\n== Bayes: PPV as a function of prevalence at fixed sensitivity/FPR (illustrative)')
for prev in (1 / 10000, 1 / 50000, 1 / 200000):
    for fpr in (0.3 / 100, 0.1 / 100, 0.02 / 100):
        sens = 0.99
        ppv = sens * prev / (sens * prev + fpr * (1 - prev))
        print(f'prevalence 1/{round(1/prev):>6d}  FPR {100*fpr:.2f}%  -> PPV {100*ppv:5.2f}%')

print('\n== NaN through a "<" cutoff comparison')
cutoff = 240.0
x = np.float64('nan')
label = '< cutoff' if x < cutoff else '>= cutoff'
print(f'value=nan, cutoff={cutoff}: x < cutoff is {bool(x < cutoff)} -> label {label!r}')
