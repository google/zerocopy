#!/usr/bin/env python3
"""Probe: recursively updated residual vs true residual in conjugate gradients.

Toy model: a plain NumPy CG (the textbook Hestenes-Stiefel recurrence used by
PETSc KSPCG, Belos CG and Ginkgo CG alike) on a synthetic SPD matrix with a
prescribed spectrum.  It is NOT any library's implementation; it shows the
mechanism analysed by Greenbaum (1997): the updated residual r_k keeps
decreasing while the true residual b - A x_k stagnates near
O(u) * ||A|| * max_j ||x_j||.

Usage: python3 probe_residual_gap.py
Deterministic (fixed seeds).  Requires NumPy only.
"""
import numpy as np


def spd_matrix(n, kappa, dtype, seed):
    rng = np.random.default_rng(seed)
    q, _ = np.linalg.qr(rng.standard_normal((n, n)))
    lam = np.geomspace(1.0, 1.0 / kappa, n)
    a = (q * lam) @ q.T
    a = 0.5 * (a + a.T)
    return a.astype(dtype)


def cg(a, b, iters):
    dt = a.dtype
    x = np.zeros_like(b)
    r = b.copy()
    p = r.copy()
    rho = r @ r
    hist = []
    norm_a = np.linalg.norm(a.astype(np.float64), 2)
    maxx = 0.0
    for k in range(iters + 1):
        true_r = b - a @ x
        maxx = max(maxx, float(np.linalg.norm(x.astype(np.float64))))
        hist.append((k, float(np.linalg.norm(r.astype(np.float64))),
                     float(np.linalg.norm(true_r.astype(np.float64))),
                     float(np.linalg.norm((true_r - r).astype(np.float64))),
                     norm_a * maxx))
        if k == iters:
            break
        q = a @ p
        alpha = rho / (p @ q)
        x = x + alpha * p
        r = r - alpha * q
        rho_new = r @ r
        beta = rho_new / rho
        rho = rho_new
        p = r + beta * p
    return hist


def run(dtype, n, kappa, iters, seed=1):
    a = spd_matrix(n, kappa, dtype, seed)
    rng = np.random.default_rng(seed + 100)
    xs = rng.standard_normal(n).astype(dtype)
    b = (a @ xs).astype(dtype)
    nb = float(np.linalg.norm(b.astype(np.float64)))
    u = float(np.finfo(dtype).eps) / 2
    hist = cg(a, b, iters)
    print(f"== dtype={np.dtype(dtype).name} n={n} kappa={kappa:.0e} u={u:.2e} ||b||={nb:.3e}")
    print(" k     ||r_k||/||b||   ||b-Ax_k||/||b||   gap/||b||    u*||A||*max_j||x_j||/||b||")
    for (k, rr, tr, gap, est) in hist:
        if k % max(1, iters // 12) == 0 or k == iters:
            print(f"{k:4d}  {rr/nb:12.3e}   {tr/nb:12.3e}   {gap/nb:12.3e}   {u*est/nb:12.3e}")
    # first iteration where the updated residual alone would pass tau
    for tau in (1e-5, 1e-8, 1e-12):
        ks = [h for h in hist if h[1] / nb <= tau]
        if ks:
            k, rr, tr, gap, est = ks[0]
            print(f"tau={tau:.0e}: updated residual passes at k={k}; true relative residual there = {tr/nb:.3e}")
        else:
            print(f"tau={tau:.0e}: updated residual never passes within {iters} iterations")
    final = hist[-1]
    print(f"final: updated={final[1]/nb:.3e} true={final[2]/nb:.3e} ratio true/updated={final[2]/max(final[1],1e-300):.3e}")


if __name__ == "__main__":
    run(np.float64, 200, 1e4, 1100)
    run(np.float32, 200, 1e4, 600)
