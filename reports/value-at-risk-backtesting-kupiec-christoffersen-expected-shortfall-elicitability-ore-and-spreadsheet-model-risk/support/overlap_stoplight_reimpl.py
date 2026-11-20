#!/usr/bin/env python3
"""Re-implementation (NOT ORE itself) of the Monte Carlo algorithm in
OpenSourceRisk/Engine QuantExt/qle/math/stoplightbounds.cpp, stopLightBounds()
(single portfolio branch): exceptions of an n-day overlapping P&L built from
iid N(0,1) daily P&Ls against h = Phi^{-1}(p) * sqrt(n); the bound for level s
is (boost right-tail quantile of the exception count at s) - 1.

Also parses ORE's tabulated reference table (obsNb / amberLimit / redLimit
arrays in QuantExt/test/stoplightbounds.cpp) and prints the tabulated values
for the same observation counts.

Usage: python3 overlap_stoplight_reimpl.py <path to QuantExt/test/stoplightbounds.cpp> [samples] [seed]
Requires numpy. Monte Carlo error applies; ORE's own test comments that even
5e6 samples may not reproduce every tabulated value.
"""
import math
import re
import sys
import numpy as np


def ppf(p):
    lo, hi = -40.0, 40.0
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if 0.5 * math.erfc(-mid / math.sqrt(2)) < p:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def parse_table(path):
    src = open(path).read()
    # the large table inside testGenerateStopLightBoundTable
    start = src.index('testGenerateStopLightBoundTable')
    body = src[start:]
    def arr(name):
        m = re.search(r'std::vector<int>\s+' + name + r'\s*=\s*\{([^}]*)\}', body)
        return [int(v) for v in m.group(1).replace('\n', ' ').split(',') if v.strip()]
    return arr('obsNb'), arr('amberLimit'), arr('redLimit')


def tabulated(obs, obsNb, amber, red):
    import bisect
    idx = bisect.bisect_right(obsNb, obs)
    return amber[idx - 1], red[idx - 1]


def mc_bounds(obs, samples, seed, days=10, p=0.99, levels=(0.95, 0.9999), batch=50000):
    rng = np.random.default_rng(seed)
    h = ppf(p) * math.sqrt(days)
    length = obs + days - 1
    counts = []
    done = 0
    while done < samples:
        b = min(batch, samples - done)
        x = rng.standard_normal((b, length))
        c = np.cumsum(x, axis=1)
        c = np.concatenate([np.zeros((b, 1)), c], axis=1)
        roll = c[:, days:] - c[:, :-days]  # obs overlapping n-day sums
        counts.append((roll > h).sum(axis=1))
        done += b
    counts = np.sort(np.concatenate(counts))[::-1]  # descending
    res = []
    for s in levels:
        n = math.ceil(samples * (1.0 - s))
        q = int(counts[n - 1])
        res.append(q - 1 if q > 0 else 0)
    iid_mean = obs * (1 - p)
    return res, float(counts.mean()), iid_mean


def main():
    path = sys.argv[1]
    samples = int(sys.argv[2]) if len(sys.argv) > 2 else 400000
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 42
    obsNb, amber, red = parse_table(path)
    print(f'parsed ORE reference table: {len(obsNb)} rows, obs range {obsNb[0]}..{obsNb[-1]}')
    print(f'samples={samples} seed={seed} (numpy PCG64; not ORE\'s Mersenne-Twister stream)')
    for obs in (200, 250, 300, 500):
        b, mean_exc, iid_mean = mc_bounds(obs, samples, seed)
        t = tabulated(obs, obsNb, amber, red)
        print(f'  obs={obs}: reimpl (max green, max amber)={tuple(b)}  ORE tabulated={t}  '
              f'mean exceptions={mean_exc:.3f} (iid expectation {iid_mean:.2f})')


if __name__ == '__main__':
    main()
