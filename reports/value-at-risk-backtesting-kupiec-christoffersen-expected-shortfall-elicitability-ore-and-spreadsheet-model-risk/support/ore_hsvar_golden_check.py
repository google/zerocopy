#!/usr/bin/env python3
"""Recompute ORE historical-simulation VaR and "ExpectedShortfall" columns from
ORE's own regression golden files, using an independent re-implementation of the
estimator read from source:

  * quantile: boost::accumulators tail_quantile<right>, i.e.
        n = ceil(N * (1 - p))   (evaluated in IEEE double)
        result = n-th largest sample
  * "ExpectedShortfall_p": mean of all samples x with x <= quantile_p
    (OREAnalytics/orea/engine/historicalsimulationvar.cpp, expectedShortfall()).

Inputs (both from OpenSourceRisk/Engine, Examples/MarketRisk/ExpectedOutput/HistSimVar/):
  historical_PnL.csv   per-scenario P&L (scenario NPV minus base NPV)
  var.csv              ORE's reported quantiles and ExpectedShortfall columns

Usage: python3 ore_hsvar_golden_check.py historical_PnL.csv var.csv
Standard library only.
"""
import csv
import math
import sys
from collections import defaultdict


def boost_right_tail_quantile(xs, p):
    n_samples = len(xs)
    n = math.ceil(n_samples * (1.0 - p))
    desc = sorted(xs, reverse=True)
    return desc[n - 1], n


def ore_es(xs, p):
    q, _ = boost_right_tail_quantile(xs, p)
    body = [x for x in xs if x <= q]
    return sum(body) / len(body), len(body)


def main(pnl_path, var_path):
    pnls = defaultdict(list)
    with open(pnl_path) as f:
        for row in csv.reader(f):
            if row[0].startswith('#'):
                continue
            pnls[tuple(row[:3])].append(float(row[5]))
    with open(var_path) as f:
        rows = list(csv.reader(f))
    header = rows[0]
    probs = [float(h.split('_')[1]) for h in header if h.startswith('Quantile_')]
    worst = 0.0
    for row in rows[1:]:
        key = tuple(row[:3])
        xs = pnls[key]
        print(f"group={'/'.join(key)} N={len(xs)}")
        for i, p in enumerate(probs):
            q_ore = float(row[3 + i])
            es_ore = float(row[3 + len(probs) + i])
            q, n = boost_right_tail_quantile(xs, p)
            es, m = ore_es(xs, p)
            # conventional lower-tail ES of P&L at level min(p, 1-p): mean of
            # the k smallest P&Ls, k = ceil(N*min(p,1-p)) (for comparison only)
            a = min(p, 1.0 - p)
            k = math.ceil(len(xs) * a)
            tail_mean_low = sum(sorted(xs)[:k]) / k
            tail_mean_high = sum(sorted(xs, reverse=True)[:k]) / k
            dq, des = abs(q - q_ore), abs(es - es_ore)
            worst = max(worst, dq, des)
            print(f"  p={p:<5} n={n:<4} Q_ore={q_ore:>16.6f} Q_reimpl={q:>16.6f} |dQ|={dq:.2e}"
                  f"  ES_ore={es_ore:>16.6f} ES_reimpl={es:>16.6f} (mean of {m} samples <= Q) |dES|={des:.2e}"
                  f"  lowTailMean(k={k})={tail_mean_low:.6f} highTailMean(k={k})={tail_mean_high:.6f}")
    print(f"max abs discrepancy vs golden: {worst:.3e}")
    # Alternative tail-mean estimators of lower-tail ES of the P&L for the All/All/All group
    xs = sorted(pnls[('All', 'All', 'All')])
    n_obs = len(xs)
    for a in (0.01, 0.05, 0.025):
        w = math.floor(n_obs * a)
        mean_floor = sum(xs[:w]) / w
        frac = n_obs * a - w
        # fractional (Acerbi-Tasche style) weighting: w full points plus frac of the next
        mean_frac = (sum(xs[:w]) + frac * xs[w]) / (n_obs * a)
        k = math.ceil(n_obs * a)
        mean_ceil = sum(xs[:k]) / k
        print(f"All/All/All alpha={a}: mean of floor(N a)={w} smallest={mean_floor:.6f}; "
              f"fractional weight={mean_frac:.6f}; mean of ceil(N a)={k} smallest={mean_ceil:.6f}")
    # floating-point evaluation of N*(1-p) for integer-valued products
    for n_obs in (250, 500, 715, 1000):
        for p in (0.95, 0.99, 0.975):
            prod = n_obs * (1.0 - p)
            print(f"N={n_obs} p={p}: N*(1-p)={prod!r} ceil={math.ceil(prod)} exact={n_obs*(1000-round(p*1000))/1000}")


if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2])
