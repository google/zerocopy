#!/usr/bin/env python3
"""TOY MODEL of the "numerical producer, exact checker" split used by
sums-of-squares certificate tactics (HOL Light Examples/sos.ml REAL_SOS,
Coq micromega psatz, NLCertify).

Target (a standard textbook SOS example): p(x,y) = 2x^4 + 2x^3 y - x^2 y^2 + 5y^4.
Gram form with z = (x^2, xy, y^2): p = z^T Q z, where matching coefficients
fixes every entry of Q except one free parameter t:
    Q(t) = [[2, 1, t], [1, -1-2t, 0], [t, 0, 5]].
p is SOS iff some Q(t) is positive semidefinite.

Producer (untrusted, floating point): maximise the smallest eigenvalue of Q(t)
over t by golden-section search, then add 1e-9 noise to emulate an inexact
interior-point solver.
Checker (exact, Fraction): round t with common denominators 1..31 then 2^5..2^66
(the schedule in HOL Light Examples/sos.ml, lines 1108-1109 at the pinned
revision), rebuild Q exactly from the equality constraints, run an exact
LDL^T ("completing the square") PSD test, and confirm sum d_i (l_i . z)^2 == p
coefficient-by-coefficient.

This is not HOL Light; nothing here is kernel-checked. It illustrates where the
trust boundary sits and how small the checker's work is.
"""
import math
import random
import time
from fractions import Fraction as F

def q_float(t):
    return [[2.0, 1.0, t], [1.0, -1.0 - 2.0 * t, 0.0], [t, 0.0, 5.0]]

def eig_min_sym3(a):
    # Jacobi eigenvalue iteration for a symmetric 3x3 matrix (floats).
    a = [row[:] for row in a]
    for _ in range(60):
        p, q = max(((i, j) for i in range(3) for j in range(i + 1, 3)), key=lambda ij: abs(a[ij[0]][ij[1]]))
        if abs(a[p][q]) < 1e-15:
            break
        th = 0.5 * math.atan2(2 * a[p][q], a[q][q] - a[p][p])
        c, s = math.cos(th), math.sin(th)
        for k in range(3):
            akp, akq = a[k][p], a[k][q]
            a[k][p], a[k][q] = c * akp - s * akq, s * akp + c * akq
        for k in range(3):
            apk, aqk = a[p][k], a[q][k]
            a[p][k], a[q][k] = c * apk - s * aqk, s * apk + c * aqk
    return min(a[i][i] for i in range(3))

def producer(rng_init=1):
    lo, hi = -10.0, 10.0
    g = (math.sqrt(5) - 1) / 2
    for _ in range(200):
        m1, m2 = hi - g * (hi - lo), lo + g * (hi - lo)
        if eig_min_sym3(q_float(m1)) < eig_min_sym3(q_float(m2)):
            lo = m1
        else:
            hi = m2
    t = (lo + hi) / 2
    rng = random.Random(rng_init)
    return t + rng.uniform(-1e-9, 1e-9), eig_min_sym3(q_float(t))

def q_exact(t):
    return [[F(2), F(1), t], [F(1), F(-1) - 2 * t, F(0)], [t, F(0), F(5)]]

def ldl(m):
    """Exact LDL^T; returns list of (d_i, row_i of L^T) or None if not PSD."""
    m = [row[:] for row in m]
    n = len(m)
    out = []
    for i in range(n):
        a = m[i][i]
        if a < 0:
            return None
        if a == 0:
            if any(m[i][k] != 0 for k in range(i, n)):
                return None
            continue
        v = [m[i][k] / a for k in range(n)]
        out.append((a, v))
        for j in range(i + 1, n):
            for k in range(i + 1, n):
                m[j][k] -= m[i][j] * v[k]
        for k in range(i, n):
            m[i][k] = F(0)
            m[k][i] = F(0)
    return out

def expand(decomp):
    # z = (x^2, xy, y^2); monomials keyed by power of x in degree-4 forms
    zmon = [(2, 0), (1, 1), (0, 2)]
    poly = {}
    for d, v in decomp:
        for i in range(3):
            for j in range(3):
                e = (zmon[i][0] + zmon[j][0], zmon[i][1] + zmon[j][1])
                poly[e] = poly.get(e, 0) + d * v[i] * v[j]
    return {e: c for e, c in poly.items() if c != 0}

TARGET = {(4, 0): F(2), (3, 1): F(2), (2, 2): F(-1), (0, 4): F(5)}

def checker(t_float):
    for den in list(range(1, 32)) + [2 ** k for k in range(5, 67)]:
        t = F(round(t_float * den), den)
        dec = ldl(q_exact(t))
        if dec is not None and expand(dec) == TARGET:
            return den, t, dec
    return None

if __name__ == "__main__":
    t0 = time.perf_counter(); tf, lam = producer(); t1 = time.perf_counter()
    print("producer: t = %.12f (with 1e-9 noise), lambda_min(Q) at optimum = %.6f, %.3f ms" % (tf, lam, (t1 - t0) * 1e3))
    print("exact rational of the float t has denominator 2^%d" % (F(tf).denominator.bit_length() - 1))
    t2 = time.perf_counter(); res = checker(tf); t3 = time.perf_counter()
    if res is None:
        print("checker: no rounding produced a PSD Gram matrix (certificate search fails)")
    else:
        den, t, dec = res
        print("checker: accepted with common denominator %d, t = %s, %.3f ms" % (den, t, (t3 - t2) * 1e3))
        for d, v in dec:
            print("   %s * (%s*x^2 + %s*xy + %s*y^2)^2" % (d, v[0], v[1], v[2]))
    # mutation: move t just outside the PSD interval and confirm rejection
    for bad in (F(-1, 2) + F(1, 10 ** 6), F(1, 2)):
        print("mutant t = %s: %s" % (bad, "rejected (not PSD)" if ldl(q_exact(bad)) is None else "accepted"))
    # exact PSD interval of Q(t): det conditions, for the record
    print("PSD interval check: t=-1/2 ->", "PSD" if ldl(q_exact(F(-1, 2))) is not None else "not PSD",
          "; t=-1 ->", "PSD" if ldl(q_exact(F(-1))) is not None else "not PSD")
