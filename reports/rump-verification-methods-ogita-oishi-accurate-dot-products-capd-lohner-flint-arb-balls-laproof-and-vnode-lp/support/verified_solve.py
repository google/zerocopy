#!/usr/bin/env python3
"""A posteriori verified linear solve vs. uncertified solve, with numpy + directed rounding.

Implements the certification step of Rump (Acta Numerica 2010, Theorem 10.2), the same
statement FLINT's arb_mat_solve_preapprox cites: if ||I - R A||_inf < 1 then A is
nonsingular and ||x - xt||_inf <= ||R (A xt - b)||_inf / (1 - ||I - R A||_inf).

This is an independent toy implementation, NOT INTLAB's verifylss and NOT FLINT. It
obtains rigorous bounds by switching the x86-64 SSE rounding mode with C99 fesetround
(via ctypes) around numpy operations. That is only valid when every floating-point
operation numpy performs runs on the calling thread and honours the current rounding
mode; the script checks this precondition (rounding_selftest) and aborts otherwise. On
the host where REPORT.md's numbers were taken, numpy 2.3.5 was linked to the
single-threaded reference BLAS/LAPACK 3.12.1.

Usage: python3 verified_solve.py [n ...]
"""
import ctypes
import ctypes.util
import sys
import time

import numpy as np

libm = ctypes.CDLL(ctypes.util.find_library("m"))
FE_TONEAREST, FE_DOWNWARD, FE_UPWARD = 0x000, 0x400, 0x800  # x86-64 glibc values


def setround(mode):
    if libm.fesetround(mode) != 0:
        raise RuntimeError("fesetround failed")


def rounding_selftest(k=64):
    """Same idea as IntervalLinearAlgebra.jl's NumericalTest.rounding_test: in upward
    rounding, (A A^T)_ii = 1 + 2^-106 must round to nextafter(1, 2)."""
    A = np.zeros((k, k))
    A[:, -1] = 2.0 ** -53
    for i in range(k - 1):
        A[i, i] = 1.0
    setround(FE_UPWARD)
    try:
        B = A @ A.T
    finally:
        setround(FE_TONEAREST)
    return all(B[i, i] == np.nextafter(1.0, 2.0) for i in range(k - 1))


def matmul_enclose(P, Q):
    """Rigorous [lo, hi] with lo <= P@Q <= hi entrywise, for float matrices P, Q."""
    setround(FE_DOWNWARD)
    try:
        lo = P @ Q
    finally:
        setround(FE_UPWARD)
    try:
        hi = P @ Q
    finally:
        setround(FE_TONEAREST)
    return lo, hi


def certify(A, b, R, xt):
    n = A.shape[0]
    # Enclose C = I - R A.
    lo, hi = matmul_enclose(R, A)
    setround(FE_UPWARD)
    try:
        I = np.eye(n)
        # |I - RA|_ij <= max(|I - lo|, |I - hi|), each difference rounded up in magnitude.
        c_up = I - lo          # upper bound of I - RA (rounded up)
        setround(FE_DOWNWARD)
        c_lo = I - hi          # lower bound of I - RA (rounded down)
        setround(FE_UPWARD)
        normC = np.max(np.sum(np.maximum(np.abs(c_up), np.abs(c_lo)), axis=1))  # rounded up
    finally:
        setround(FE_TONEAREST)
    if not normC < 1.0:
        return None, float(normC)
    # Enclose residual r = A xt - b.
    xt2 = xt.reshape(-1, 1)
    alo, ahi = matmul_enclose(A, xt2)
    setround(FE_DOWNWARD)
    try:
        rlo = alo[:, 0] - b
        setround(FE_UPWARD)
        rhi = ahi[:, 0] - b
    finally:
        setround(FE_TONEAREST)
    # Enclose R r for r in [rlo, rhi]: split R = Rp + Rn by sign.
    Rp = np.maximum(R, 0.0)
    Rn = np.minimum(R, 0.0)
    setround(FE_UPWARD)
    try:
        up = Rp @ rhi + Rn @ rlo
        setround(FE_DOWNWARD)
        dn = Rp @ rlo + Rn @ rhi
        setround(FE_UPWARD)
        num = max(np.max(np.abs(up)), np.max(np.abs(dn)))
        setround(FE_DOWNWARD)
        den = 1.0 - normC
        setround(FE_UPWARD)
        err = num / den
    finally:
        setround(FE_TONEAREST)
    return float(err), float(normC)


def randsvd(n, cond, rng):
    U, _ = np.linalg.qr(rng.standard_normal((n, n)))
    V, _ = np.linalg.qr(rng.standard_normal((n, n)))
    s = np.logspace(0, -np.log10(cond), n)
    return (U * s) @ V.T


def main():
    if not rounding_selftest():
        sys.exit("rounding self-test failed: the BLAS does not honour fesetround on this thread")
    print("# rounding self-test passed")
    print("# n, target cond, uncertified solve [ms], certification incl. approx inverse [ms], ratio,"
          " ||I-RA|| bound, certified relative radius (or FAIL)")
    rng = np.random.default_rng(2026)
    ns = [int(a) for a in sys.argv[1:]] or [100, 300, 1000]
    for n in ns:
        for cond in (1e2, 1e6, 1e10, 1e14, 1e16, 1e18):
            A = randsvd(n, cond, rng)
            b = A @ np.ones(n)
            t0 = time.perf_counter()
            xt = np.linalg.solve(A, b)
            t1 = time.perf_counter()
            R = np.linalg.inv(A)
            err, normC = certify(A, b, R, xt)
            t2 = time.perf_counter()
            ts, tc = (t1 - t0) * 1e3, (t2 - t1) * 1e3
            rad = "FAIL" if err is None else "%.2e" % (err / np.max(np.abs(xt)))
            print("%5d %7.0e %9.2f %9.2f %6.1f %10.3e %s" % (n, cond, ts, tc, (ts + tc) / ts, normC, rad))


if __name__ == "__main__":
    main()
