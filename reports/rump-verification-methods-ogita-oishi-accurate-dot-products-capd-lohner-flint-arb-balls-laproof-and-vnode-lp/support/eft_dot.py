#!/usr/bin/env python3
"""Accuracy probe: naive dot product vs. Dot2 (Ogita-Rump-Oishi 2005, Algorithm 5.3).

This is an independent re-implementation for illustration; it is NOT INTLAB or any
library code. Python floats are IEEE 754 binary64 with round-to-nearest; math.fma
(Python >= 3.13) provides a correctly rounded fused multiply-add used for TwoProduct.

The generator follows the published GenDot scheme (Algorithm 6.1 of the paper) with
exact rational arithmetic (fractions.Fraction) standing in for DotExact. Every reported
condition number and error is computed exactly from the generated data, so the
conclusions do not depend on how faithfully the generator matches the original.

Usage: python3 eft_dot.py [seed] [n] [samples_per_decade]
"""
import math
import random
import sys
from fractions import Fraction

EPS = 2.0 ** -53  # relative rounding error unit for binary64, round to nearest


def two_sum(a, b):
    x = a + b
    z = x - a
    y = (a - (x - z)) + (b - z)
    return x, y


def two_prod_fma(a, b):
    x = a * b
    y = math.fma(a, b, -x)
    return x, y


def dot_naive(x, y):
    s = 0.0
    for a, b in zip(x, y):
        s = s + a * b
    return s


def dot2(x, y):
    p, s = two_prod_fma(x[0], y[0])
    for a, b in zip(x[1:], y[1:]):
        h, r = two_prod_fma(a, b)
        p, q = two_sum(p, h)
        s = s + (q + r)
    return p + s


def dot_exact(x, y):
    return sum((Fraction(a) * Fraction(b) for a, b in zip(x, y)), Fraction(0))


def gen_dot(n, c, rng):
    """GenDot-style generator (Ogita, Rump, Oishi 2005, Algorithm 6.1)."""
    n2 = round(n / 2)
    b = math.log2(c)
    e = [round(rng.random() * b / 2) for _ in range(n2)]
    e[0] = round(b / 2) + 1
    e[-1] = 0
    x = [0.0] * n
    y = [0.0] * n
    for i in range(n2):
        x[i] = (2 * rng.random() - 1) * 2.0 ** e[i]
        y[i] = (2 * rng.random() - 1) * 2.0 ** e[i]
    m = n - n2
    e2 = [round(b / 2 - (b / 2) * k / (m - 1)) if m > 1 else 0 for k in range(m)]
    for i in range(n2, n):
        x[i] = (2 * rng.random() - 1) * 2.0 ** e2[i - n2]
        partial = float(dot_exact(x[:i], y[:i]))  # nearest double to the exact partial dot product
        y[i] = ((2 * rng.random() - 1) * 2.0 ** e2[i - n2] - partial) / x[i]
    idx = list(range(n))
    rng.shuffle(idx)
    return [x[i] for i in idx], [y[i] for i in idx]


def gamma(k):
    return k * EPS / (1 - k * EPS)


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 100
    per = int(sys.argv[3]) if len(sys.argv) > 3 else 20
    rng = random.Random(seed)
    print(f"# seed={seed} n={n} samples_per_decade={per} eps=2^-53")
    print("# decade: log10 of anticipated condition number c passed to the generator")
    print("# cols: decade, samples, median log10(actual cond), max relerr naive, max relerr dot2,"
          " max(relerr/a-priori bound) naive, max(relerr/a-priori bound) dot2, #bound violations")
    g_n = gamma(n)
    for dec in range(2, 42, 4):
        rows = []
        for _ in range(per):
            x, y = gen_dot(n, 10.0 ** dec, rng)
            ex = dot_exact(x, y)
            if ex == 0:
                continue
            absdot = sum((abs(Fraction(a) * Fraction(b)) for a, b in zip(x, y)), Fraction(0))
            cond = float(2 * absdot / abs(ex))
            rn = float(abs(Fraction(dot_naive(x, y)) - ex) / abs(ex))
            r2 = float(abs(Fraction(dot2(x, y)) - ex) / abs(ex))
            # a priori bounds, relative form:
            #   naive (recursive summation with FMA-free products): |fl - d| <= gamma_n |x|^T|y|
            #   Dot2 (Proposition 5.5, no underflow): |res - d| <= eps|d| + gamma_n^2 |x|^T|y|
            bn = g_n * cond / 2
            b2 = EPS + g_n ** 2 * cond / 2
            rows.append((cond, rn, r2, rn / bn, r2 / b2))
        rows.sort()
        med = rows[len(rows) // 2][0]
        viol = sum(1 for r in rows if r[3] > 1 or r[4] > 1)
        print(f"{dec:3d} {len(rows):3d} {math.log10(med):6.1f} {max(r[1] for r in rows):9.2e} "
              f"{max(r[2] for r in rows):9.2e} {max(r[3] for r in rows):9.2e} {max(r[4] for r in rows):9.2e} {viol}")


if __name__ == "__main__":
    main()
