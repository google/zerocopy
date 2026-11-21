#!/usr/bin/env python3
"""Check which binomial interval construction reproduces the 95% confidence
intervals printed in Table 1 of Ruiz de Gauna et al., BioMed Research
International 2014, Article 386010 (doi:10.1155/2014/386010), whose caption
says the intervals "were computed using Wald's interval for binomial
proportions".

Inputs per row: reported point estimate (percent), reported interval (percent),
and the number of testing segments (S for sensitivity, NS for specificity).
The success count x is reconstructed as round(estimate * n). Standard library
only. A statistical recomputation of published numbers, not a measurement.
"""
import math

Z = 1.959963984540054  # two-sided 95%

ROWS = [
    # (study, metric, estimate%, lo%, hi%, n)
    ("Eilevstjonn MC-RAMP", "Se", 96.7, 87.6, 98.0, 92),
    ("Eilevstjonn MC-RAMP", "Sp", 79.9, 73.3, 85.2, 174),
    ("Ruiz de Gauna Kalman", "Se", 90.1, 83.6, 94.2, 131),
    ("Ruiz de Gauna Kalman", "Sp", 80.4, 75.9, 84.3, 347),
    ("Aramendi LMS", "Se", 95.4, 88.4, 98.6, 87),
    ("Aramendi LMS", "Sp", 86.3, 81.8, 89.9, 285),
    ("Tan ART", "Se", 92.1, 86.8, 95.5, 114),
    ("Tan ART", "Sp", 90.5, 89.7, 91.2, 4155),
    ("Li direct", "Se", 93.3, 92.0, 94.4, 1256),
    ("Li direct", "Sp", 88.6, 86.8, 90.2, 964),
    ("Krasteva direct", "Se", 90.1, 85.6, 94.6, 172),
    ("Krasteva direct", "Sp", 86.1, 83.6, 88.7, 721),
]


def wald(x, n):
    p = x / n
    h = Z * math.sqrt(p * (1 - p) / n)
    return p - h, p + h


def wilson(x, n):
    p = x / n
    z2 = Z * Z
    c = (p + z2 / (2 * n)) / (1 + z2 / n)
    h = Z * math.sqrt(p * (1 - p) / n + z2 / (4 * n * n)) / (1 + z2 / n)
    return c - h, c + h


def _logpmf(k, n, p):
    if p <= 0.0:
        return 0.0 if k == 0 else -math.inf
    if p >= 1.0:
        return 0.0 if k == n else -math.inf
    return (math.lgamma(n + 1) - math.lgamma(k + 1) - math.lgamma(n - k + 1)
            + k * math.log(p) + (n - k) * math.log1p(-p))


def _sf(x, n, p):  # P(X >= x), summed in log space to avoid overflow
    return sum(math.exp(_logpmf(k, n, p)) for k in range(x, n + 1))


def _cdf(x, n, p):  # P(X <= x)
    return sum(math.exp(_logpmf(k, n, p)) for k in range(0, x + 1))


def _bisect(f, target, increasing):
    lo, hi = 0.0, 1.0
    for _ in range(100):
        mid = (lo + hi) / 2
        v = f(mid)
        if (v < target) == increasing:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def clopper_pearson(x, n):
    a = 0.025
    lo = 0.0 if x == 0 else _bisect(lambda p: _sf(x, n, p), a, True)
    hi = 1.0 if x == n else _bisect(lambda p: _cdf(x, n, p), a, False)
    return lo, hi


def fmt(iv):
    return "(%5.1f-%5.1f)" % (100 * iv[0], 100 * iv[1])


def main():
    print("%-22s %-2s %5s %-13s %5s %4s | %-13s %-13s %-13s" % (
        "study", "m", "est", "printed", "n", "x", "Wald", "Wilson", "Clopper-P"))
    tally = {"Wald": 0, "Wilson": 0, "Clopper-P": 0}
    for study, m, est, lo, hi, n in ROWS:
        x = round(est / 100 * n)
        ivs = {"Wald": wald(x, n), "Wilson": wilson(x, n), "Clopper-P": clopper_pearson(x, n)}
        marks = []
        for k, iv in ivs.items():
            ok = abs(100 * iv[0] - lo) <= 0.15 and abs(100 * iv[1] - hi) <= 0.15
            tally[k] += ok
            marks.append(fmt(iv) + ("*" if ok else " "))
        sym = abs((est - lo) - (hi - est)) < 0.11
        print("%-22s %-2s %5.1f (%4.1f-%4.1f)%s %5d %4d | %s" % (
            study, m, est, lo, hi, " sym" if sym else "    ", n, x, " ".join(marks)))
    print()
    print("rows reproduced within +/-0.15 points (marked *):", tally, "of", len(ROWS))
    print("printed intervals symmetric about the estimate (Wald intervals must be):",
          sum(abs((e - l) - (h - e)) < 0.11 for _, _, e, l, h, _ in ROWS), "of", len(ROWS))


if __name__ == "__main__":
    main()
