#!/usr/bin/env python3
"""Toy evaluation of formulas reconstructed from EuroForMix source
(oyvble/euroformix at commit 800c314c91235e2b9a67270437226d4dada325b4).

Basis: execution (toy model of EuroForMix formulas, not EuroForMix itself).
R, Rcpp and EuroForMix are not run. Regularized incomplete gamma/beta are
implemented below from their standard series/continued-fraction definitions
and self-checked against closed forms.

[1] Peak-height model (src/EFMfastengine.cpp calcEvidWeights L525-606,
    R/prepareC.R L381): shape0 = 1/omega^2, scale0 = mu/shape0,
    allele shape = shape0 * sum_k Mx_k * n_ka * beta^((bp-125)/100)
    (stutter terms omitted here), drop-out weight = P(Y < AT) under
    Gamma(shape, scale0).
[2] validMLEmodel envelope (R/validMLEmodel.R L29-45): the i-th sorted
    PIT value is compared with Beta(N*u_i, N - N*u_i + 1) where u_i=(i-0.5)/N,
    i.e. Beta(i-0.5, N-i+1.5); the exact order-statistic law of N iid U(0,1)
    is Beta(i, N-i+1). Points are flagged when the two-sided p-value is below
    (alpha/N)/2.
"""
import math


def gammainc_lower_reg(a, x):
    if x <= 0:
        return 0.0
    if x < a + 1:  # series
        s = term = 1.0 / a
        n = a
        for _ in range(10000):
            n += 1
            term *= x / n
            s += term
            if abs(term) < abs(s) * 1e-15:
                break
        return s * math.exp(-x + a * math.log(x) - math.lgamma(a))
    # continued fraction for Q
    b = x + 1 - a
    c = 1e300
    d = 1 / b
    h = d
    for i in range(1, 10000):
        an = -i * (i - a)
        b += 2
        d = an * d + b
        d = 1e-300 if abs(d) < 1e-300 else d
        c = b + an / c
        c = 1e-300 if abs(c) < 1e-300 else c
        d = 1 / d
        delta = d * c
        h *= delta
        if abs(delta - 1) < 1e-15:
            break
    return 1 - math.exp(-x + a * math.log(x) - math.lgamma(a)) * h


def betacf(a, b, x):
    qab, qap, qam = a + b, a + 1, a - 1
    c, d = 1.0, 1 - qab * x / qap
    d = 1e-300 if abs(d) < 1e-300 else d
    d = 1 / d
    h = d
    for m in range(1, 10000):
        m2 = 2 * m
        aa = m * (b - m) * x / ((qam + m2) * (a + m2))
        d = 1 + aa * d; d = 1e-300 if abs(d) < 1e-300 else d
        c = 1 + aa / c; c = 1e-300 if abs(c) < 1e-300 else c
        d = 1 / d; h *= d * c
        aa = -(a + m) * (qab + m) * x / ((a + m2) * (qap + m2))
        d = 1 + aa * d; d = 1e-300 if abs(d) < 1e-300 else d
        c = 1 + aa / c; c = 1e-300 if abs(c) < 1e-300 else c
        d = 1 / d; delta = d * c; h *= delta
        if abs(delta - 1) < 1e-15:
            break
    return h


def betainc_reg(a, b, x):
    if x <= 0:
        return 0.0
    if x >= 1:
        return 1.0
    lbt = math.lgamma(a + b) - math.lgamma(a) - math.lgamma(b) + a * math.log(x) + b * math.log(1 - x)
    if x < (a + 1) / (a + b + 2):
        return math.exp(lbt) * betacf(a, b, x) / a
    return 1 - math.exp(lbt) * betacf(b, a, 1 - x) / b


def betaq(q, a, b):
    lo, hi = 0.0, 1.0
    for _ in range(200):
        mid = (lo + hi) / 2
        if betainc_reg(a, b, mid) < q:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def selfcheck():
    assert abs(gammainc_lower_reg(1.0, 2.0) - (1 - math.exp(-2.0))) < 1e-12
    assert abs(gammainc_lower_reg(1.0, 0.3) - (1 - math.exp(-0.3))) < 1e-12
    assert abs(betainc_reg(1.0, 1.0, 0.37) - 0.37) < 1e-12
    assert abs(betainc_reg(2.0, 1.0, 0.5) - 0.25) < 1e-12
    assert abs(betainc_reg(1.0, 3.0, 0.2) - (1 - 0.8 ** 3)) < 1e-12


def main():
    selfcheck()
    print("self-check of incomplete gamma/beta implementations: OK")
    print("\n[1] P(drop-out) = P(Y < AT) for one allele copy, Gamma(shape0*Mx*deg, scale0)")
    AT = 50.0
    print(f"  AT={AT}")
    print("  mu    omega  Mx    beta  bp   shape     mean(rfu)  P(dropout)")
    for mu, omega, mx, beta, bp in [
        (1000, 0.3, 0.30, 1.0, 125), (1000, 0.3, 0.10, 1.0, 125),
        (1000, 0.3, 0.05, 1.0, 125), (1000, 0.6, 0.05, 1.0, 125),
        (1000, 0.3, 0.10, 0.6, 325), (300, 0.5, 0.10, 0.8, 300)]:
        shape0 = 1 / omega ** 2
        scale0 = mu / shape0
        deg = beta ** ((bp - 125) / 100)
        shape = shape0 * mx * deg
        pdo = gammainc_lower_reg(shape, AT / scale0)
        print(f"  {mu:<5} {omega:<6} {mx:<5} {beta:<5} {bp:<4} {shape:<9.4f} {shape*scale0:<10.2f} {pdo:.4g}")
    print("  homozygote (n=2) vs heterozygote (n=1), mu=1000, omega=0.3, Mx=0.05:")
    shape0 = 1 / 0.3 ** 2; scale0 = 1000 / shape0
    for n in (1, 2):
        print(f"    n={n}: P(Y<AT) = {gammainc_lower_reg(shape0*0.05*n, AT/scale0):.4g}")

    print("\n[2] validMLEmodel envelope: Beta(i-0.5, N-i+1.5) (code) vs Beta(i, N-i+1) (exact)")
    alpha = 0.01
    for N in (20, 50, 200):
        crit = (alpha / N) / 2
        print(f"  N={N}: two-sided Bonferroni level per point = {crit:.3g}")
        for i in (1, N // 2, N):
            lo_c, hi_c = betaq(crit, i - 0.5, N - i + 1.5), betaq(1 - crit, i - 0.5, N - i + 1.5)
            lo_e, hi_e = betaq(crit, i, N - i + 1), betaq(1 - crit, i, N - i + 1)
            print(f"    i={i:<4} code [{lo_c:.3e}, {hi_c:.6f}]  exact [{lo_e:.3e}, {hi_e:.6f}]")


if __name__ == "__main__":
    main()
