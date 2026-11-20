#!/usr/bin/env python3
"""A priori (mechanized) vs. a posteriori (computed) error bounds for one dot product.

For a left-to-right binary64 dot product fl(x.y) (the evaluation order of LAProof's
dotprodF), compare on the same data:
  actual   |fl(x.y) - x.y|, computed exactly with fractions.Fraction;
  apriori  the bound proved in LAProof accuracy_proofs/dot_acc.v, lemma
           dotprod_forward_error:  g(n) * (|x|.|y|) + g1(n, n-1),
           g(n) = (1+u)^n - 1, g1(n1,n2) = n1 * E * (1 + g(n2)),
           u = 2^-53 (default_rel), E = 2^-1075 (default_abs for binary64);
           evaluated here exactly in rationals;
  interval the width of a rigorous enclosure obtained by recomputing the same loop
           with all operations rounded down and then rounded up (C99 fesetround via
           ctypes; CPython float arithmetic executes on the calling thread);
  running  Higham's running error bound (Accuracy and Stability, 2nd ed., Alg. 3.2
           style): mu = sum |partial sums| + |products| scaled by u, evaluated in
           exact rationals here so that it is itself rigorous.
This is a toy comparison of bound formulas on synthetic data, not a measurement of
LAProof itself (LAProof proves the bound; it does not compute anything at run time).

Usage: python3 apriori_vs_aposteriori.py
"""
import ctypes
import ctypes.util
import random
from fractions import Fraction

libm = ctypes.CDLL(ctypes.util.find_library("m"))
FE_TONEAREST, FE_DOWNWARD, FE_UPWARD = 0x000, 0x400, 0x800

U = Fraction(1, 2 ** 53)
E = Fraction(1, 2 ** 1075)


def g(n):
    return (1 + U) ** n - 1


def g1(n1, n2):
    return n1 * E * (1 + g(n2))


def dot_lr(x, y):
    s = 0.0
    for a, b in zip(x, y):
        s = s + a * b
    return s


def dot_directed(x, y, mode):
    libm.fesetround(mode)
    try:
        s = 0.0
        for a, b in zip(x, y):
            s = s + a * b
        return s
    finally:
        libm.fesetround(FE_TONEAREST)


def running_bound(x, y):
    # |fl(x.y) - x.y| <= u * sum_i (|s_i| + |p_i|) to first order; we use the rigorous
    # version with each term inflated by (1+u)^n, so it is a valid upper bound.
    s = 0.0
    mu = Fraction(0)
    for a, b in zip(x, y):
        p = a * b
        s = s + p
        mu += abs(Fraction(s)) + abs(Fraction(p))
    return U * mu * (1 + g(len(x)))


def main():
    rng = random.Random(11)
    print("# kind, n, actual, apriori(LAProof), interval width, running bound,"
          " apriori/actual, interval/actual, apriori/interval")
    for kind in ("positive", "mixed-sign"):
        for n in (10, 100, 1000, 10000):
            if kind == "positive":
                x = [rng.random() for _ in range(n)]
                y = [rng.random() for _ in range(n)]
            else:
                x = [rng.uniform(-1, 1) for _ in range(n)]
                y = [rng.uniform(-1, 1) for _ in range(n)]
            exact = sum((Fraction(a) * Fraction(b) for a, b in zip(x, y)), Fraction(0))
            actual = abs(Fraction(dot_lr(x, y)) - exact)
            absdot = sum((abs(Fraction(a) * Fraction(b)) for a, b in zip(x, y)), Fraction(0))
            apriori = g(n) * absdot + g1(n, n - 1)
            lo, hi = dot_directed(x, y, FE_DOWNWARD), dot_directed(x, y, FE_UPWARD)
            assert Fraction(lo) <= exact <= Fraction(hi)
            width = Fraction(hi) - Fraction(lo)
            run = running_bound(x, y)
            assert actual <= apriori and actual <= run
            fa = float(actual) if actual else float("nan")
            print("%-10s %6d %9.2e %9.2e %9.2e %9.2e %8.1f %8.1f %6.1f" % (
                kind, n, float(actual), float(apriori), float(width), float(run),
                float(apriori) / fa, float(width) / fa, float(apriori / width)))


if __name__ == "__main__":
    main()
