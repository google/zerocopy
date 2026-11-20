#!/usr/bin/env python3
"""Probe: what a residual-based acceptance test does and does not entail.

Toy models (NumPy only, deterministic seeds); none of this is a library run.
  A. Rigal-Gaches normwise backward error is attained by an explicit rank-one
     perturbation (checks the formula constructively).
  B. A test relative to ||r_0|| with a nonzero initial guess accepts an iterate
     whose residual relative to ||b|| is large (the Belos default scaling
     "Norm of Initial Residual"; PETSc/Ginkgo default to ||b||).
  C. A left-preconditioned residual test (PETSc's default norm for GMRES/CG with
     left preconditioning) accepts at preconditioned reduction 1e-5 while the
     unpreconditioned relative residual is orders of magnitude larger.
  D. Normwise vs componentwise (Oettli-Prager) backward error on a badly row-
     scaled sparse system; one step of fixed-precision iterative refinement
     (the LAPACK xGERFS loop) restores a small componentwise backward error.
  E. A tiny backward error does not bound the forward error without the
     condition number (Hilbert matrix).
"""
import numpy as np

EPS = np.finfo(np.float64).eps


def eta_normwise(a, b, y, ordr=2):
    r = b - a @ y
    na = np.linalg.norm(a, ordr)
    return np.linalg.norm(r, ordr) / (na * np.linalg.norm(y, ordr) + np.linalg.norm(b, ordr))


def omega_componentwise(a, b, y):
    """Oettli-Prager with E=|A|, f=|b|, using the LAPACK xGERFS safe denominator."""
    r = b - a @ y
    den = np.abs(a) @ np.abs(y) + np.abs(b)
    n = a.shape[0]
    safmin = np.finfo(np.float64).tiny
    safe1 = (n + 1) * safmin
    safe2 = safe1 / EPS
    big = den > safe2
    s = np.where(big, np.abs(r) / np.where(big, den, 1.0), (np.abs(r) + safe1) / (den + safe1))
    return float(s.max())


def cg(a, b, x0, test, maxit=10000):
    x = x0.copy(); r = b - a @ x; p = r.copy(); rho = r @ r
    r0 = np.linalg.norm(r)
    for k in range(maxit):
        if test(np.linalg.norm(r), r0):
            return x, k
        q = a @ p; al = rho / (p @ q); x = x + al * p; r = r - al * q
        rn = r @ r; p = r + (rn / rho) * p; rho = rn
    return x, maxit


def gmres_left(a, b, minv_diag, rtol, maxit=200):
    """Unrestarted GMRES (MGS Arnoldi) on M^{-1}A x = M^{-1}b, x0 = 0, stopping on
    the preconditioned residual norm relative to ||M^{-1} b|| (PETSc-style)."""
    n = a.shape[0]
    pb = minv_diag * b
    beta = np.linalg.norm(pb)
    v = np.zeros((n, maxit + 1)); h = np.zeros((maxit + 1, maxit))
    v[:, 0] = pb / beta
    for j in range(maxit):
        w = minv_diag * (a @ v[:, j])
        for i in range(j + 1):
            h[i, j] = w @ v[:, i]; w = w - h[i, j] * v[:, i]
        h[j + 1, j] = np.linalg.norm(w)
        if h[j + 1, j] > 0:
            v[:, j + 1] = w / h[j + 1, j]
        e1 = np.zeros(j + 2); e1[0] = beta
        y, *_ = np.linalg.lstsq(h[: j + 2, : j + 1], e1, rcond=None)
        res = np.linalg.norm(e1 - h[: j + 2, : j + 1] @ y)
        if res <= rtol * beta:
            return v[:, : j + 1] @ y, j + 1, res / beta
    return v[:, :maxit] @ y, maxit, res / beta


def section_a():
    rng = np.random.default_rng(7)
    n = 50
    a = rng.standard_normal((n, n)); b = rng.standard_normal(n)
    y = np.linalg.solve(a, b) + 1e-6 * rng.standard_normal(n)
    r = b - a @ y
    na, ny, nb = np.linalg.norm(a, 2), np.linalg.norm(y), np.linalg.norm(b)
    eta = np.linalg.norm(r) / (na * ny + nb)
    da = (na * ny / (na * ny + nb)) * np.outer(r, y) / ny**2
    db = -(nb / (na * ny + nb)) * r
    chk = np.linalg.norm((a + da) @ y - (b + db))
    print("A. Rigal-Gaches: eta(y) = %.3e ; ||dA||/||A|| = %.3e ; ||db||/||b|| = %.3e ; ||(A+dA)y-(b+db)|| = %.1e"
          % (eta, np.linalg.norm(da, 2) / na, np.linalg.norm(db) / nb, chk))


def section_b():
    rng = np.random.default_rng(11)
    n = 100
    q, _ = np.linalg.qr(rng.standard_normal((n, n)))
    a = (q * np.geomspace(1, 1e-3, n)) @ q.T; a = (a + a.T) / 2
    xs = rng.standard_normal(n); b = a @ xs
    x0 = 1e6 * rng.standard_normal(n)
    tol = 1e-8
    x1, k1 = cg(a, b, x0, lambda rn, r0: rn <= tol * r0)
    x2, k2 = cg(a, b, x0, lambda rn, r0: rn <= tol * np.linalg.norm(b))
    for name, x, k in (("||r||<=tol*||r0||", x1, k1), ("||r||<=tol*||b||", x2, k2)):
        rr = np.linalg.norm(b - a @ x) / np.linalg.norm(b)
        print("B. x0 = 1e6*randn, tol=1e-8, test %-18s stops at k=%4d: ||b-Ax||/||b|| = %.2e, eta_normwise = %.2e, fwd err = %.2e"
              % (name, k, rr, eta_normwise(a, b, x), np.linalg.norm(x - xs) / np.linalg.norm(xs)))


def section_c():
    rng = np.random.default_rng(5)
    n = 200
    d = np.geomspace(1.0, 1e6, n)
    s = np.eye(n) + 0.05 * rng.standard_normal((n, n)) / np.sqrt(n)
    a = d[:, None] * s
    b = np.ones(n)
    x, its, prel = gmres_left(a, b, 1.0 / np.diag(a), 1e-5)
    rr = np.linalg.norm(b - a @ x) / np.linalg.norm(b)
    print("C. left-Jacobi GMRES, rtol=1e-5 on ||M^-1 r||/||M^-1 b||: its=%d, preconditioned rel = %.2e, unpreconditioned ||r||/||b|| = %.2e, eta_normwise = %.2e, kappa(M)=%.0e"
          % (its, prel, rr, eta_normwise(a, b, x), d.max() / d.min()))


def section_d():
    rng = np.random.default_rng(3)
    n = 400
    a = np.diag(4.0 * np.ones(n)) + np.diag(-np.ones(n - 1), 1) + np.diag(-np.ones(n - 1), -1)
    scale = np.where(np.arange(n) % 2 == 0, 1.0, 1e-10)
    a = scale[:, None] * a
    xs = rng.standard_normal(n); b = a @ xs
    # CG is not applicable (nonsymmetric after scaling); use unrestarted GMRES with
    # no preconditioner and a normwise acceptance test ||r|| <= 1e-10 ||b||.
    x, its, prel = gmres_left(a, b, np.ones(n), 1e-10, maxit=400)
    print("D. row-scaled tridiagonal (odd rows x1e-10), GMRES stopped at ||r||/||b|| = %.2e (its=%d)" % (prel, its))
    print("   normwise eta = %.2e ; componentwise omega = %.2e ; fwd err = %.2e"
          % (eta_normwise(a, b, x), omega_componentwise(a, b, x), np.linalg.norm(x - xs) / np.linalg.norm(xs)))
    lu_solve = np.linalg.solve  # dense LU (LAPACK dgesv) as the refinement solver
    for step in range(1, 3):
        r = b - a @ x
        x = x + lu_solve(a, r)
        print("   after %d step(s) of fixed-precision refinement: eta = %.2e ; omega = %.2e ; fwd err = %.2e"
              % (step, eta_normwise(a, b, x), omega_componentwise(a, b, x), np.linalg.norm(x - xs) / np.linalg.norm(xs)))


def section_e():
    n = 12
    i = np.arange(1, n + 1)
    a = 1.0 / (i[:, None] + i[None, :] - 1)
    xs = np.ones(n); b = a @ xs
    x = np.linalg.solve(a, b)
    kappa = np.linalg.cond(a, 2)
    eta = eta_normwise(a, b, x)
    print("E. Hilbert n=12: kappa_2 = %.2e ; eta_normwise = %.2e ; omega = %.2e ; fwd err = %.2e ; first-order bound 2*kappa*eta = %.2e"
          % (kappa, eta, omega_componentwise(a, b, x), np.linalg.norm(x - xs) / np.linalg.norm(xs), 2 * kappa * eta))


if __name__ == "__main__":
    section_a(); section_b(); section_c(); section_d(); section_e()
