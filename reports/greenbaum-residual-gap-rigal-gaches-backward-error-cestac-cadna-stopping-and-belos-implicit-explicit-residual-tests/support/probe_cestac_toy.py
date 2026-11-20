#!/usr/bin/env python3
"""Probe: a toy re-implementation of the CESTAC method applied to CG stopping.

This is NOT CADNA.  It re-implements the published CESTAC recipe (Vignes 1993;
Jezequel & Chesneaux 2008) in pure Python so the mechanism can be inspected:
  * every floating-point operation is performed N = 3 times in parallel
    "samples", each result rounded at random toward -inf or +inf with
    probability 1/2 (exact rounding decided with rational arithmetic);
  * the number of exact significant decimal digits of a result is estimated as
        C = log10( sqrt(N) * |mean| / (tau * sigma) ),  tau = 4.303 (Student t,
        2 degrees of freedom, beta = 0.05),
    and a result with C <= 0 (or all-zero mean) is a "computational zero" (@.0);
  * the dynamic stopping rule stops the iteration when the update x_k - x_{k-1}
    is a computational zero in every component.
The probe compares the estimated digits with the actual digits measured against
the exact rational solution, and compares the dynamic stop with fixed tolerance
stops on the recursively updated residual.

Usage: python3 probe_cestac_toy.py      (pure Python + NumPy for setup; ~10 s)
"""
import math
import random
from fractions import Fraction

N = 3
TAU = 4.303  # t_{0.975, 2}
random.seed(20261120)


def rr(exact):
    """Random rounding of an exact rational to a neighbouring double."""
    f = float(exact)
    fx = Fraction(f)
    if fx == exact:
        return f
    if fx < exact:
        down, up = f, math.nextafter(f, math.inf)
    else:
        down, up = math.nextafter(f, -math.inf), f
    return down if random.random() < 0.5 else up


INSTAB = {"div": 0, "mul": 0}  # CADNA-style self-validation counters


class S:
    """Stochastic number: N samples."""
    __slots__ = ("v",)

    def __init__(self, v):
        self.v = list(v)

    @staticmethod
    def c(x):
        return S([float(x)] * N)

    def _op(self, o, f):
        o = o if isinstance(o, S) else S.c(o)
        return S([rr(f(Fraction(a), Fraction(b))) for a, b in zip(self.v, o.v)])

    def __add__(self, o): return self._op(o, lambda a, b: a + b)
    def __sub__(self, o): return self._op(o, lambda a, b: a - b)
    def __mul__(self, o):
        if isinstance(o, S) and self.is_zero() and o.is_zero() and self.mean() != 0 and o.mean() != 0:
            INSTAB["mul"] += 1  # unstable multiplication: both operands insignificant
        return self._op(o, lambda a, b: a * b)

    def __truediv__(self, o):
        if isinstance(o, S) and o.is_zero():
            INSTAB["div"] += 1  # unstable division: divisor insignificant
        return self._op(o, lambda a, b: a / b)

    def mean(self):
        return sum(self.v) / N

    def digits(self):
        m = self.mean()
        if m == 0.0:
            return 0.0
        sd = math.sqrt(sum((x - m) ** 2 for x in self.v) / (N - 1))
        if sd == 0.0:
            return 15.95  # all samples identical: report full double precision
        return math.log10(math.sqrt(N) * abs(m) / (TAU * sd))

    def is_zero(self):
        return self.mean() == 0.0 or self.digits() <= 0.0


def dot(x, y):
    s = S.c(0.0)
    for a, b in zip(x, y):
        s = s + a * b
    return s


def exact_solve(a, b):
    n = len(a)
    m = [[Fraction(a[i][j]) for j in range(n)] + [Fraction(b[i])] for i in range(n)]
    for k in range(n):
        p = max(range(k, n), key=lambda i: abs(m[i][k]))
        m[k], m[p] = m[p], m[k]
        for i in range(k + 1, n):
            f = m[i][k] / m[k][k]
            for j in range(k, n + 1):
                m[i][j] -= f * m[k][j]
    x = [Fraction(0)] * n
    for i in reversed(range(n)):
        x[i] = (m[i][n] - sum(m[i][j] * x[j] for j in range(i + 1, n))) / m[i][i]
    return x


def exact_cg(a, b, kmax):
    """Exact rational CG iterates x_k (k=0..kmax); stops changing once r = 0."""
    n = len(a)
    A = [[Fraction(v) for v in row] for row in a]
    x = [Fraction(0)] * n
    r = [Fraction(v) for v in b]
    p = list(r)
    rho = sum(v * v for v in r)
    xs = [list(x)]
    for _ in range(kmax):
        if rho == 0:
            xs.append(list(x))
            continue
        q = [sum(A[i][j] * p[j] for j in range(n)) for i in range(n)]
        alpha = rho / sum(pi * qi for pi, qi in zip(p, q))
        x = [xi + alpha * pi for xi, pi in zip(x, p)]
        r = [ri - alpha * qi for ri, qi in zip(r, q)]
        rho_new = sum(v * v for v in r)
        beta = rho_new / rho
        rho = rho_new
        p = [ri + beta * pi for ri, pi in zip(r, p)]
        xs.append(list(x))
    return xs


def main():
    import numpy as np
    n = 12
    rng = np.random.default_rng(42)
    q, _ = np.linalg.qr(rng.standard_normal((n, n)))
    a = (q * np.geomspace(1.0, 1e-6, n)) @ q.T
    a = ((a + a.T) / 2).tolist()
    xs = rng.standard_normal(n)
    b = (np.array(a) @ xs).tolist()
    xex = exact_solve(a, b)  # exact solution of the stored (rounded) system
    xk_exact = exact_cg(a, b, 60)  # exact-arithmetic CG iterates (CESTAC's reference)
    A = [[S.c(v) for v in row] for row in a]
    B = [S.c(v) for v in b]
    x = [S.c(0.0) for _ in range(n)]
    r = list(B)
    p = list(r)
    rho = dot(r, r)
    nb = math.sqrt(sum(v * v for v in b))
    print(" k  ||r_k||/||b|| (mean)  digits(rho)  est min digits(x)  vs exact x_k  vs x*   ||b-Ax||/||b||  update @.0  instab(div,mul)")
    first_instab = None
    stop_dyn = None
    first_tol = {}
    for k in range(1, 61):
        q_ = [dot(row, p) for row in A]
        alpha = rho / dot(p, q_)
        dx = [alpha * pi for pi in p]
        x = [xi + dxi for xi, dxi in zip(x, dx)]
        r = [ri - alpha * qi for ri, qi in zip(r, q_)]
        rho_new = dot(r, r)
        beta = rho_new / rho
        rho = rho_new
        p = [ri + beta * pi for ri, pi in zip(r, p)]
        xm = [xi.mean() for xi in x]
        est = min(xi.digits() for xi in x)
        act = min(-math.log10(max(abs(float(Fraction(xm[i]) - xex[i]) / float(xex[i])), 1e-17)) for i in range(n))
        actk = min(-math.log10(max(abs(float(Fraction(xm[i]) - xk_exact[k][i]) / float(xk_exact[k][i])), 1e-17)) for i in range(n))
        tr = math.sqrt(sum((b[i] - sum(a[i][j] * xm[j] for j in range(n))) ** 2 for i in range(n))) / nb
        upd_zero = all(d.is_zero() for d in dx)
        rn = math.sqrt(max(rho.mean(), 0.0)) / nb
        for tol in (1e-8, 1e-12, 1e-16):
            if tol not in first_tol and rn <= tol:
                first_tol[tol] = k
        if k <= 40 or k % 5 == 0:
            print(f"{k:2d}  {rn:18.3e}  {rho.digits():11.2f}  {est:17.2f}  {actk:12.2f}  {act:6.2f}  {tr:14.3e}  {str(upd_zero):10s}  ({INSTAB['div']},{INSTAB['mul']})")
        if first_instab is None and (INSTAB["div"] or INSTAB["mul"]):
            first_instab = k
        if upd_zero and stop_dyn is None:
            stop_dyn = (k, est, actk, act, tr)
    print("dynamic (CESTAC) stop: k=%s, estimated min digits=%.2f, actual digits vs exact x_k=%.2f, vs x*=%.2f, true rel residual=%.3e" % stop_dyn)
    print(f"first iteration with a self-validation instability (cumulative counters): k={first_instab}")
    for tol, k in sorted(first_tol.items(), reverse=True):
        print(f"updated-residual test tol={tol:.0e} first passes at k={k}")
    for tol in (1e-8, 1e-12, 1e-16):
        if tol not in first_tol:
            print(f"updated-residual test tol={tol:.0e} never passes in 60 iterations")


if __name__ == "__main__":
    main()
