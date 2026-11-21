#!/usr/bin/env python3
"""Toy-model probe: observed-order (MMS) testing versus fixed-tolerance
regression testing on deliberately mutated discretizations.

THIS IS A TOY MODEL written for this report. It is not MOOSE, MASA, or the
Navier-Stokes code of SAND2000-1444; its numbers characterise only this
1-D model problem.

Model problem on (0, 1):
    -(k(x) u')' + c u' + r u = f,   u(0) = u_exact(0),
    k(1) u'(1) = q  (Neumann, flux) at x = 1,
with k(x) = 1 + 0.5 sin(2x), c = 2, r = 3, and manufactured solution
    u(x) = 1 + 0.4 x + exp(-x) sin(2.5 x).
f and q are derived symbolically (sympy) from u.

Discretization (correct version, formally 2nd order): vertex-centred grid
x_i = i h, h = 1/N; conservative flux form with k evaluated at i +- 1/2,
central advection, pointwise reaction and source, Neumann condition through a
ghost node with a central difference. Solved directly (Thomas algorithm), or
by SOR when a mutant asks for an iterative solver.

Usage: python3 toy_mms_mutants.py   (prints tables; deterministic; numpy+sympy)
"""
import math
import time

import numpy as np
import sympy as sp

# ------------------------------------------------------------------ manufactured solution
X = sp.symbols("x")
K_EXPR = 1 + sp.Rational(1, 2) * sp.sin(2 * X)
U_EXPR = 1 + sp.Rational(2, 5) * X + sp.exp(-X) * sp.sin(sp.Rational(5, 2) * X)


def build(c_val, r_val):
    f_expr = -sp.diff(K_EXPR * sp.diff(U_EXPR, X), X) + c_val * sp.diff(U_EXPR, X) + r_val * U_EXPR
    q_val = float((K_EXPR * sp.diff(U_EXPR, X)).subs(X, 1))
    return (sp.lambdify(X, f_expr, "numpy"), q_val)


k_fn = sp.lambdify(X, K_EXPR, "numpy")
u_fn = sp.lambdify(X, U_EXPR, "numpy")


# ------------------------------------------------------------------ linear solvers
def thomas(a, b, c, d):
    """Solve tridiagonal system: a[i] x[i-1] + b[i] x[i] + c[i] x[i+1] = d[i]."""
    n = len(b)
    cp = np.zeros(n)
    dp = np.zeros(n)
    cp[0] = c[0] / b[0]
    dp[0] = d[0] / b[0]
    for i in range(1, n):
        m = b[i] - a[i] * cp[i - 1]
        cp[i] = c[i] / m if i < n - 1 else 0.0
        dp[i] = (d[i] - a[i] * dp[i - 1]) / m
    x = np.zeros(n)
    x[-1] = dp[-1]
    for i in range(n - 2, -1, -1):
        x[i] = dp[i] - cp[i] * x[i + 1]
    return x


def sor(a, b, c, d, omega, rtol, maxit=2_000_000):
    """Point SOR on the tridiagonal system; stops when ||r||_2 <= rtol ||d||_2."""
    n = len(b)
    x = np.zeros(n)
    dn = np.linalg.norm(d)
    it = 0
    while it < maxit:
        for i in range(n):
            s = d[i]
            if i > 0:
                s -= a[i] * x[i - 1]
            if i < n - 1:
                s -= c[i] * x[i + 1]
            x[i] = (1 - omega) * x[i] + omega * s / b[i]
        it += 1
        if it % 10 == 0:
            r = d - b * x
            r[1:] -= a[1:] * x[:-1]
            r[:-1] -= c[:-1] * x[1:]
            if np.linalg.norm(r) <= rtol * dn:
                break
    return x, it


# ------------------------------------------------------------------ discretization (+ mutants)
def solve(N, mutant="M0", c_val=2.0, r_val=3.0, k_scale=1.0, solver=("direct",)):
    f_fn, q = build(c_val, r_val)
    h = 1.0 / N
    x = np.linspace(0.0, 1.0, N + 1)
    kk = lambda z: k_scale * k_fn(z)  # noqa: E731
    # unknowns u_1..u_N (u_0 is Dirichlet)
    n = N
    a = np.zeros(n)
    b = np.zeros(n)
    cc = np.zeros(n)
    d = np.zeros(n)
    u0 = u_fn(0.0)
    adv_sign = -1.0 if mutant == "M6" else 1.0
    for j in range(n):
        i = j + 1
        xi = x[i]
        if mutant == "M1":  # coefficient evaluated at the node instead of the faces
            kw = ke = kk(xi)
        else:
            kw, ke = kk(xi - h / 2), kk(xi + h / 2)
        fx = f_fn(xi + h / 2) if mutant == "M5" else f_fn(xi)
        lo = -kw / h**2
        di = (kw + ke) / h**2
        hi = -ke / h**2
        if mutant == "M2":  # first-order upwind advection
            lo += -c_val / h
            di += c_val / h
        else:
            lo += -adv_sign * c_val / (2 * h)
            hi += adv_sign * c_val / (2 * h)
        if mutant == "M3":  # reaction applied to the wrong (lagged) node
            lo += r_val
        else:
            di += r_val
        if i == N:  # Neumann boundary row
            if mutant == "M4":  # first-order one-sided flux condition replaces the row
                lo, di, hi, fx = -kk(1.0) / h, kk(1.0) / h, 0.0, q
            else:  # ghost node u_{N+1} = u_{N-1} + 2 h q / k(1)
                g = 2 * h * q / kk(1.0)
                lo = lo + hi
                fx = fx - hi * g
                hi = 0.0
        if i == 1:
            fx -= lo * u0
            lo = 0.0
        a[j], b[j], cc[j], d[j] = lo, di, hi, fx
    if mutant == "M8":  # formal mistake: an unused diagnostic computed with a wrong index
        _unused = float(np.sum(d[:-1] - d[1:]))  # noqa: F841
    if solver[0] == "direct":
        uu = thomas(a, b, cc, d)
        its = 0
    else:
        uu, its = sor(a, b, cc, d, omega=solver[1], rtol=solver[2])
    u = np.concatenate([[u0], uu])
    return x, u, its


def errors(x, u):
    e = u - u_fn(x)
    return math.sqrt(float(np.mean(e**2))), float(np.max(np.abs(e)))


def fitted_order(hs, es, npts=3):
    """Least-squares slope of log10(e) on log10(h) over the last npts points
    (the same formula as numpy.polyfit(log10 x, log10 y, 1) on the finest levels)."""
    return float(np.polyfit(np.log10(hs[-npts:]), np.log10(es[-npts:]), 1)[0])


LEVELS = [8, 16, 32, 64, 128, 256, 512]
GOLD_N = 32


def study(mutant, **kw):
    hs, l2s, lis, sols = [], [], [], {}
    t0 = time.perf_counter()
    its = []
    for N in LEVELS:
        x, u, it = solve(N, mutant, **kw)
        e2, ei = errors(x, u)
        hs.append(1.0 / N)
        l2s.append(e2)
        lis.append(ei)
        sols[N] = u
        its.append(it)
    wall = time.perf_counter() - t0
    return dict(h=np.array(hs), l2=np.array(l2s), li=np.array(lis), sols=sols, wall=wall, its=its)


def max_rel_diff(u, ref, abs_zero=1e-10):
    """CSV-diff style per-value relative difference, ignoring |values| below abs_zero."""
    m = 0.0
    for p, q in zip(u, ref):
        if abs(p) < abs_zero and abs(q) < abs_zero:
            continue
        m = max(m, abs(p - q) / max(abs(p), abs(q)))
    return m


def main():
    np.set_printoptions(precision=3)
    cases = [
        ("M0", "correct discretization", {}),
        ("M1", "k at node, not faces (drops k' u' term)", {}),
        ("M2", "first-order upwind advection", {}),
        ("M3", "reaction on lagged node u[i-1]", {}),
        ("M4", "first-order one-sided Neumann row", {}),
        ("M5", "source evaluated at x+h/2", {}),
        ("M6/c=2", "advection sign flipped, test uses c=2", dict(c_val=2.0)),
        ("M6/c=0", "advection sign flipped, test uses c=0", dict(c_val=0.0)),
        ("M8", "formal: unused diagnostic wrong", {}),
        ("M9a", "diffusivity scaled by (1+1e-4)", dict(k_scale=1 + 1e-4)),
        ("M9b", "diffusivity scaled by (1+1e-7)", dict(k_scale=1 + 1e-7)),
    ]
    base = study("M0")
    base_c0 = study("M0", c_val=0.0)
    print("Levels N =", LEVELS, "; gold mesh N =", GOLD_N)
    print("Order acceptance A: |p - 2| < 0.1 on a least-squares fit of the 3 finest levels")
    print("Regression R(tau): max per-node relative difference vs gold (correct code, N=%d) <= tau" % GOLD_N)
    hdr = "%-7s %-44s %8s %8s %8s %8s %-6s %10s %-9s %-9s" % (
        "case", "mistake", "pL2", "pLinf", "pL2last", "eL2(N=512)", "A", "regr diff", "R(5.5e-6)", "R(1e-2)")
    print(hdr)
    rows = []
    for tag, desc, kw in cases:
        m = tag.split("/")[0]
        s = study(m, **kw)
        ref = base_c0 if kw.get("c_val", 2.0) == 0.0 else base
        p2 = fitted_order(s["h"], s["l2"])
        pi = fitted_order(s["h"], s["li"])
        plast = math.log(s["l2"][-2] / s["l2"][-1], 2)
        acc = abs(p2 - 2) < 0.1 and abs(pi - 2) < 0.1
        rd = max_rel_diff(s["sols"][GOLD_N], ref["sols"][GOLD_N])
        row = (tag, desc, p2, pi, plast, s["l2"][-1], "pass" if acc else "FAIL", rd,
               "pass" if rd <= 5.5e-6 else "FAIL", "pass" if rd <= 1e-2 else "FAIL")
        rows.append(row)
        print("%-7s %-44s %8.3f %8.3f %8.3f %10.3e %-6s %10.2e %-9s %-9s" % row)
    print()
    print("Per-level L2 errors (selected cases):")
    for tag, desc, kw in cases:
        if tag in ("M0", "M9a", "M9b", "M1"):
            s = study(tag.split("/")[0], **kw)
            pair = [math.log(s["l2"][i] / s["l2"][i + 1], 2) for i in range(len(LEVELS) - 1)]
            print("  %-4s eL2 = %s" % (tag, " ".join("%.3e" % v for v in s["l2"])))
            print("       pairwise orders = %s" % " ".join("%.3f" % v for v in pair))
    print()
    # iterative-solver cases (Dirichlet+Neumann problem, same discretization as M0)
    print("Iterative solver (SOR) in place of the direct solver, levels up to N=128:")
    lv = [8, 16, 32, 64, 128]
    for label, solver in (("SOR w=1.9 rtol=1e-12", ("sor", 1.9, 1e-12)),
                          ("SOR w=1.5 rtol=1e-12 (efficiency mistake)", ("sor", 1.5, 1e-12)),
                          ("SOR w=1.9 rtol=1e-6 (loose tolerance)", ("sor", 1.9, 1e-6))):
        hs, es, its, us = [], [], [], {}
        t0 = time.perf_counter()
        for N in lv:
            x, u, it = solve(N, "M0", solver=solver)
            hs.append(1.0 / N)
            es.append(errors(x, u)[0])
            its.append(it)
            us[N] = u
        wall = time.perf_counter() - t0
        p = fitted_order(np.array(hs), np.array(es))
        pair = [math.log(es[i] / es[i + 1], 2) for i in range(len(lv) - 1)]
        rd = max_rel_diff(us[GOLD_N], base["sols"][GOLD_N])
        print("  %-44s p(3 finest)=%.3f pairwise=%s iters=%s regr diff(N=32)=%.2e wall=%.1fs" % (
            label, p, " ".join("%.2f" % v for v in pair), its, rd, wall))
    print()
    print("Wall time of the 7-level direct-solver study (M0): %.3f s; single N=%d solve: %.4f s" % (
        base["wall"], GOLD_N, timeit_single()))


def timeit_single():
    t0 = time.perf_counter()
    for _ in range(20):
        solve(GOLD_N, "M0")
    return (time.perf_counter() - t0) / 20


if __name__ == "__main__":
    main()
