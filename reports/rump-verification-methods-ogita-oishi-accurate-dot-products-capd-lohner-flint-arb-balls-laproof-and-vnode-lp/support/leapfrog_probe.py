#!/usr/bin/env python3
"""Leapfrog harmonic oscillator: a priori (mechanized) bound vs. measured error, and the
wrapping effect of naive interval propagation.

Reproduces, as an independent re-implementation, the computation whose accuracy is proved
in VeriNum/VerifiedLeapfrog (pinned in REPORT.json): Stormer-Verlet steps in IEEE binary32
for q'' = -q with q(0)=1, p(0)=0, h=1/32, N=1000 steps, using the same expression order
as leapfrog_project/lfharm.c:
    a = -q
    q = q + h*p + (0.5*(h*h))*a
    p = p + (0.5*h)*(a + (-q))
The mechanized corollary yes_accurate_harmonic_oscillator states that the computed state is
within 0.0308 (Euclidean norm on (p, q)) of the exact solution at t = N*h.

Part A measures the actual total error, splits it into discretization error (same
recurrence in exact rational arithmetic) and round-off error (binary32 minus exact
recurrence), and compares them with 0.0308.
Part B propagates an initial box [q0 +/- r] x [p0 +/- r] through the exact (rational)
leapfrog map with (1) naive interval arithmetic, (2) an affine/zonotope representation
(the image of the box under the composed linear map, which is exact for a linear map),
showing how a box representation inflates (the "wrapping effect" that Lohner-type QR and
doubleton sets in CAPD are designed to control). This is a toy model of the phenomenon,
not CAPD or VNODE-LP.

Usage: python3 leapfrog_probe.py
"""
import math
from fractions import Fraction

import numpy as np

H32 = np.float32(1.0) / np.float32(32.0)
N = 1000


def step_f32(q, p):
    h = H32
    a = -q
    q = q + h * p + (np.float32(0.5) * (h * h)) * a
    p = p + (np.float32(0.5) * h) * (a + (-q))
    return q, p


def step_exact(q, p, h=Fraction(1, 32)):
    a = -q
    q = q + h * p + (Fraction(1, 2) * (h * h)) * a
    p = p + (Fraction(1, 2) * h) * (a + (-q))
    return q, p


def part_a():
    q, p = np.float32(1.0), np.float32(0.0)
    qe, pe = Fraction(1), Fraction(0)
    for _ in range(N):
        q, p = step_f32(q, p)
        qe, pe = step_exact(qe, pe)
    t = N / 32.0
    qt, pt = math.cos(t), -math.sin(t)  # exact solution (binary64 evaluation, error ~1e-16)
    tot = math.hypot(float(p) - pt, float(q) - qt)
    disc = math.hypot(float(pe) - pt, float(qe) - qt)
    rnd = math.hypot(float(p) - float(pe), float(q) - float(qe))
    print("## Part A: N=%d, h=1/32, t=%.2f, binary32" % (N, t))
    print("total error     %.3e" % tot)
    print("discretization  %.3e (exact-arithmetic recurrence vs exact solution)" % disc)
    print("round-off       %.3e (binary32 recurrence vs exact-arithmetic recurrence)" % rnd)
    print("mechanized a priori bound 0.0308; bound/total = %.2f" % (0.0308 / tot))


def part_b(r=Fraction(1, 10 ** 6)):
    h = Fraction(1, 32)
    # one step as a linear map M acting on (q, p)
    # q' = (1 - h^2/2) q + h p ; p' = p - (h/2)(q + q') = -(h/2)(2 - h^2/2) q + (1 - h^2/2) p
    c = 1 - h * h / 2
    M = [[c, h], [-(h / 2) * (2 - h * h / 2), c]]
    # naive interval propagation of the box (exact rational endpoints: no rounding, pure wrapping)
    lo = [Fraction(1) - r, -r]
    hi = [Fraction(1) + r, r]
    # affine form: center + G @ e, e in [-1,1]^2 (exact image of the box under the linear map)
    center = [Fraction(1), Fraction(0)]
    G = [[r, Fraction(0)], [Fraction(0), r]]
    print("\n## Part B: initial box half-width %s around (q,p)=(1,0); exact arithmetic, no rounding" % r)
    print("# step, naive-interval width(q), affine-form width(q), ratio")
    for k in range(1, N + 1):
        nlo, nhi = [], []
        for i in range(2):
            a_lo = sum(min(M[i][j] * lo[j], M[i][j] * hi[j]) for j in range(2))
            a_hi = sum(max(M[i][j] * lo[j], M[i][j] * hi[j]) for j in range(2))
            nlo.append(a_lo)
            nhi.append(a_hi)
        lo, hi = nlo, nhi
        center = [M[0][0] * center[0] + M[0][1] * center[1], M[1][0] * center[0] + M[1][1] * center[1]]
        G = [[M[i][0] * G[0][j] + M[i][1] * G[1][j] for j in range(2)] for i in range(2)]
        if k in (1, 10, 100, 250, 500, 1000):
            wn = hi[0] - lo[0]
            wa = 2 * (abs(G[0][0]) + abs(G[0][1]))
            print("%5d %10.3e %10.3e %10.3e" % (k, float(wn), float(wa), float(wn / wa)))


if __name__ == "__main__":
    part_a()
    part_b()
