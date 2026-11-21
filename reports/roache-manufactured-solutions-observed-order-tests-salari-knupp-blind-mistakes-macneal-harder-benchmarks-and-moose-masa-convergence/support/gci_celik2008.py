#!/usr/bin/env python3
"""Grid Convergence Index (GCI) procedure of Celik et al., ASME J. Fluids Eng.
130(7):078001 (2008), Steps 3-5, implemented from the published equations
(3a)-(3c), (4), (5), (6), (7), and checked against the three worked columns of
that note's Table 1.

    p     = |ln|e32/e21| + q(p)| / ln(r21)                       (3a)
    q(p)  = ln((r21^p - s) / (r32^p - s))                         (3b)
    s     = sign(e32/e21)                                         (3c)
    e32 = phi3 - phi2, e21 = phi2 - phi1, grid 1 finest.
    phi_ext21 = (r21^p phi1 - phi2) / (r21^p - 1)                 (4)
    e_a21     = |(phi1 - phi2) / phi1|                            (5)
    e_ext21   = |(phi_ext12 - phi1) / phi_ext12|                  (6)
    GCI_fine21 = 1.25 e_a21 / (r21^p - 1)                         (7)
Equation (3) is solved by fixed-point iteration starting from the first term,
as the note prescribes.
"""
import math


def gci(phi1, phi2, phi3, r21, r32, iters=200):
    e21, e32 = phi2 - phi1, phi3 - phi2
    s = math.copysign(1.0, e32 / e21)
    p = abs(math.log(abs(e32 / e21))) / math.log(r21)
    for _ in range(iters):
        q = math.log((r21**p - s) / (r32**p - s))
        p_new = abs(math.log(abs(e32 / e21)) + q) / math.log(r21)
        if abs(p_new - p) < 1e-14:
            p = p_new
            break
        p = p_new
    ext = (r21**p * phi1 - phi2) / (r21**p - 1)
    ea = abs((phi1 - phi2) / phi1)
    eext = abs((ext - phi1) / ext)
    g = 1.25 * ea / (r21**p - 1)
    return p, ext, ea, eext, g


TABLE1 = [
    # label, phi1, phi2, phi3, (N1, N2, N3), published (p, phi_ext21, e_a21 %, e_ext21 %, GCI %)
    # Table 1 prints r21 = 1.5, r32 = 1.333 and r21 = 2.0, r32 = 2.143; the grids are 2-D,
    # so with h from Eq. (2) the ratios are r21 = sqrt(N1/N2) and r32 = sqrt(N2/N3).
    ("reattachment length (monotonic)", 6.063, 5.972, 5.863, (18000, 8000, 4500), (1.53, 6.1685, 1.5, 1.7, 2.2)),
    ("axial velocity (p < 1)", 10.7880, 10.7250, 10.6050, (18000, 4500, 980), (0.75, 10.8801, 0.6, 0.9, 1.1)),
    ("axial velocity (oscillatory)", 6.0042, 5.9624, 6.0909, (18000, 4500, 980), (1.51, 6.0269, 0.7, 0.4, 0.5)),
]

if __name__ == "__main__":
    print("%-34s %6s %6s %6s %9s %7s %7s %7s | published (p, phi_ext, ea%%, eext%%, GCI%%)" % (
        "case", "r21", "r32", "p", "phi_ext", "ea%", "eext%", "GCI%"))
    for label, a, b, c, (n1, n2, n3), pub in TABLE1:
        r21, r32 = math.sqrt(n1 / n2), math.sqrt(n2 / n3)
        p, ext, ea, eext, g = gci(a, b, c, r21, r32)
        print("%-34s %6.3f %6.3f %6.3f %9.4f %7.2f %7.2f %7.2f | %s" % (
            label, r21, r32, p, ext, 100 * ea, 100 * eext, 100 * g, pub))
