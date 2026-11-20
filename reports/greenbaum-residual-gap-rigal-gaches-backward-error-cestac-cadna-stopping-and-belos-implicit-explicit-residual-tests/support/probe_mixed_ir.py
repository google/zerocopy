#!/usr/bin/env python3
"""Probe: mixed-precision iterative refinement with the LAPACK DSGESV stopping test.

Toy model (NumPy): factor/solve in binary32 (numpy.linalg.solve on float32
arrays, i.e. LAPACK sgesv), residual and update in binary64, stop when
    ||r||_inf <= sqrt(n) * ||x||_inf * ||A||_inf * eps64      (DSGESV, BWDMAX = 1)
or after 30 iterations (DSGESV's ITERMAX).  This re-implements the published
DSGESV control flow; it is not a run of LAPACK's DSGESV itself.
It reports what acceptance certifies (normwise backward error, perturbing A only)
and what it does not (forward error, which scales with kappa).
"""
import numpy as np

EPS64 = np.finfo(np.float64).eps
EPS32 = np.finfo(np.float32).eps


def matrix(n, kappa, seed):
    rng = np.random.default_rng(seed)
    u, _ = np.linalg.qr(rng.standard_normal((n, n)))
    v, _ = np.linalg.qr(rng.standard_normal((n, n)))
    return (u * np.geomspace(1.0, 1.0 / kappa, n)) @ v.T


def ir(a, b, itermax=30):
    n = a.shape[0]
    a32 = a.astype(np.float32)
    anrm = np.linalg.norm(a, np.inf)
    cte = anrm * EPS64 * np.sqrt(n)
    x = np.linalg.solve(a32, b.astype(np.float32)).astype(np.float64)
    for it in range(0, itermax + 1):
        r = b - a @ x
        if np.linalg.norm(r, np.inf) <= np.linalg.norm(x, np.inf) * cte:
            return x, it, True
        if it == itermax:
            break
        d = np.linalg.solve(a32, r.astype(np.float32)).astype(np.float64)
        x = x + d
    return x, itermax, False


def main():
    n = 200
    print(" kappa_2   kappa_inf*u32   iters  accepted  eta_inf(A only)     fwd err_inf")
    for kappa in (1e2, 1e5, 1e7, 1e9):
        a = matrix(n, kappa, 1)
        rng = np.random.default_rng(2)
        xs = rng.standard_normal(n)
        b = a @ xs
        x, it, ok = ir(a, b)
        r = b - a @ x
        eta = np.linalg.norm(r, np.inf) / (np.linalg.norm(a, np.inf) * np.linalg.norm(x, np.inf))
        kinf = np.linalg.cond(a, np.inf)
        fe = np.linalg.norm(x - xs, np.inf) / np.linalg.norm(xs, np.inf)
        print(f" {kappa:7.0e}   {kinf*EPS32/2:12.2e}   {it:5d}  {str(ok):8s}  {eta:14.2e}   {fe:14.2e}")


if __name__ == "__main__":
    main()
