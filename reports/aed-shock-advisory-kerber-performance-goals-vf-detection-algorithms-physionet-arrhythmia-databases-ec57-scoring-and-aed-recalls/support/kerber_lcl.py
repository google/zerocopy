#!/usr/bin/env python3
"""Recompute one-sided 90% lower confidence limits (LCLs) for the AED
arrhythmia-analysis performance goals of Kerber et al. (Circulation 1997;
95:1677-1682), as reproduced in FDA PMA P160033 SSED Table 5, under several
textbook interval constructions, and report which construction (if any)
reproduces each published LCL.

Standard library only (Python 3.10+). This is a statistical recomputation,
not a measurement of any device or algorithm.

Published rows (n = minimum test-sample size, goal = performance goal,
lcl = published one-sided 90% lower confidence limit, all in percent):
"""
import math

ROWS = [
    # (rhythm, metric, n, goal, published_lcl)
    ("Coarse VF", "sensitivity", 200, 0.90, 87),
    ("Rapid VT", "sensitivity", 50, 0.75, 67),
    ("NSR", "specificity", 100, 0.99, 97),
    ("AF/SB/SVT/block/IVR/PVCs", "specificity", 30, 0.95, 88),
    ("Asystole", "specificity", 100, 0.95, 92),
]

ALPHA = 0.10                      # one-sided 90%
Z = 1.2815515655446004            # standard normal 0.90 quantile


def wald(p, n):
    return p - Z * math.sqrt(p * (1 - p) / n)


def wilson(p, n):
    z2 = Z * Z
    centre = p + z2 / (2 * n)
    half = Z * math.sqrt(p * (1 - p) / n + z2 / (4 * n * n))
    return (centre - half) / (1 + z2 / n)


def binom_sf(x, n, p):
    """P(X >= x) for integer x, X ~ Binomial(n, p)."""
    return sum(math.comb(n, k) * p**k * (1 - p) ** (n - k) for k in range(x, n + 1))


def clopper_pearson_lower(x, n):
    """Exact one-sided lower limit: the p solving P(X >= x | p) = ALPHA."""
    if x <= 0:
        return 0.0
    lo, hi = 0.0, 1.0
    for _ in range(200):
        mid = (lo + hi) / 2
        if binom_sf(x, n, mid) < ALPHA:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def _betacf(a, b, x):
    """Continued fraction for the regularized incomplete beta (modified Lentz)."""
    tiny = 1e-300
    qab, qap, qam = a + b, a + 1.0, a - 1.0
    c, d = 1.0, 1.0 - qab * x / qap
    d = 1.0 / (d if abs(d) > tiny else tiny)
    h = d
    for m in range(1, 1000):
        m2 = 2 * m
        aa = m * (b - m) * x / ((qam + m2) * (a + m2))
        d = 1.0 + aa * d
        d = 1.0 / (d if abs(d) > tiny else tiny)
        c = 1.0 + aa / c
        c = c if abs(c) > tiny else tiny
        h *= d * c
        aa = -(a + m) * (qab + m) * x / ((a + m2) * (qap + m2))
        d = 1.0 + aa * d
        d = 1.0 / (d if abs(d) > tiny else tiny)
        c = 1.0 + aa / c
        c = c if abs(c) > tiny else tiny
        delta = d * c
        h *= delta
        if abs(delta - 1.0) < 1e-15:
            break
    return h


def betainc(a, b, x):
    """Regularized incomplete beta I_x(a, b) for real a, b > 0."""
    if x <= 0.0:
        return 0.0
    if x >= 1.0:
        return 1.0
    lbt = (math.lgamma(a + b) - math.lgamma(a) - math.lgamma(b)
           + a * math.log(x) + b * math.log(1.0 - x))
    if x < (a + 1.0) / (a + b + 2.0):
        return math.exp(lbt) * _betacf(a, b, x) / a
    return 1.0 - math.exp(lbt) * _betacf(b, a, 1.0 - x) / b


def beta_ppf(q, a, b):
    lo, hi = 0.0, 1.0
    for _ in range(200):
        mid = (lo + hi) / 2
        if betainc(a, b, mid) < q:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def cp_continuous(goal, n):
    """Clopper-Pearson lower limit with the (possibly non-integer) count
    x = goal*n plugged into its Beta-quantile form Beta(x, n - x + 1)."""
    x = goal * n
    return beta_ppf(ALPHA, x, n - x + 1)


def agresti_coull(p, n):
    z2 = Z * Z
    nt = n + z2
    pt = (p * n + z2 / 2) / nt
    return pt - Z * math.sqrt(pt * (1 - pt) / nt)


def self_check():
    # The Beta-quantile form must agree with the binomial-sum form for integer x.
    for x, n in ((180, 200), (99, 100), (29, 30), (38, 50)):
        a = clopper_pearson_lower(x, n)
        b = beta_ppf(ALPHA, x, n - x + 1)
        assert abs(a - b) < 1e-9, (x, n, a, b)


def pct(v):
    return f"{100 * v:6.2f}"


def main():
    self_check()
    print("one-sided 90%% LCL recomputation (z = %.4f)" % Z)
    hdr = ("rhythm", "n", "goal", "pub", "Wald@goal", "Wilson@goal",
           "CP x=floor", "CP x=ceil", "Wald x=floor")
    print("%-26s %4s %5s %4s %10s %11s %10s %10s %12s" % hdr)
    for name, _metric, n, goal, pub in ROWS:
        xf = math.floor(goal * n + 1e-9)
        xc = math.ceil(goal * n - 1e-9)
        cols = (
            wald(goal, n),
            wilson(goal, n),
            clopper_pearson_lower(xf, n),
            clopper_pearson_lower(xc, n),
            wald(xf / n, n),
        )
        print("%-26s %4d %5.2f %4d %10s %11s %10s %10s %12s" % (
            name, n, goal, pub, *(pct(c) for c in cols)))
    methods = {
        "Wald@goal": lambda n, g: wald(g, n),
        "Wilson@goal": lambda n, g: wilson(g, n),
        "CP x=floor(goal*n)": lambda n, g: clopper_pearson_lower(math.floor(g * n + 1e-9), n),
        "CP x=ceil(goal*n)": lambda n, g: clopper_pearson_lower(math.ceil(g * n - 1e-9), n),
        "Wald x=floor(goal*n)": lambda n, g: wald(math.floor(g * n + 1e-9) / n, n),
        "CP continuous x=goal*n": lambda n, g: cp_continuous(g, n),
        "Agresti-Coull@goal": lambda n, g: agresti_coull(g, n),
    }
    print()
    print("CP continuous / Agresti-Coull values:")
    for name, _m, n, goal, pub in ROWS:
        print("  %-26s pub %3d  CPcont %s  AC %s" % (
            name, pub, pct(cp_continuous(goal, n)), pct(agresti_coull(goal, n))))
    print()
    print("which constructions reproduce the published integer LCL?")
    print("(rounded = round-half-up to integer percent; truncated = floor)")
    for mname, f in methods.items():
        hits_r, hits_t = [], []
        for name, _m, n, goal, pub in ROWS:
            v = 100 * f(n, goal)
            hits_r.append(math.floor(v + 0.5) == pub)
            hits_t.append(math.floor(v) == pub)
        print("  %-22s rounded: %d/5 %s   truncated: %d/5 %s" % (
            mname, sum(hits_r), "".join("Y" if h else "n" for h in hits_r),
            sum(hits_t), "".join("Y" if h else "n" for h in hits_t)))


if __name__ == "__main__":
    main()
