#!/usr/bin/env python3
"""Toy check of the 40 CFR 194.34(d) sample-size criterion.

194.34(d): "the number of CCDFs generated shall be large enough such that, at cumulative
releases of 1 and 10, the maximum CCDF generated exceeds the 99th percentile of the
population of CCDFs with at least a 0.95 probability."

For n independent draws from a continuous population, P(max > q_0.99) = 1 - 0.99**n.
This script (i) solves 1 - 0.99**n >= 0.95 for the smallest integer n, and (ii) checks the
formula and the effect of replicated Latin hypercube sampling by Monte Carlo on a TOY scalar
population (exceedance probability at a fixed release level modelled as U(0,1) after a
monotone transform; any continuous population gives the same order-statistic result for
simple random sampling).  It is not a model of the WIPP analysis.
"""
import math
import random

n_min = math.ceil(math.log(0.05) / math.log(0.99))
print("smallest n with 1-0.99^n >= 0.95:", n_min, " 1-0.99^n_min =", 1 - 0.99 ** n_min)
for n in (100, 200, 298, 299, 300):
    print(f"n={n}: 1-0.99^n = {1 - 0.99 ** n:.4f}")

rng = random.Random(12345)
TRIALS = 20000


def srs(n):
    return max(rng.random() for _ in range(n))


def lhs_1d(n):
    # one-dimensional Latin hypercube: one point per stratum [k/n, (k+1)/n)
    return max((k + rng.random()) / n for k in range(n))


def replicated_lhs(r, n):
    return max(lhs_1d(n) for _ in range(r))


for name, f in [("SRS n=300", lambda: srs(300)),
                ("1-D LHS n=100 (single replicate)", lambda: lhs_1d(100)),
                ("1-D LHS 3 replicates x 100", lambda: replicated_lhs(3, 100))]:
    hits = sum(1 for _ in range(TRIALS) if f() > 0.99)
    print(f"{name}: P(max > q0.99) ~= {hits / TRIALS:.4f} ({TRIALS} trials)")
