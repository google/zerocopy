#!/usr/bin/env python3
"""Independent re-implementation (NOT rpact or gsDesign) of the recursive
numerical integration used to compute one-sided group sequential efficacy
boundaries (Armitage-McPherson-Rowe recursion on the Z scale), plus emulations
of the two quadrature rules that rpact and gsDesign use, so that their
discretisation error can be measured against a fine reference.

Quadrature rules emulated (rules read from source, re-written here):
  * "rpact-NC7": composite closed 7-point Newton-Cotes, 15 panels -> 91 points,
    integrating the continuation region [-6, c_{k-1}] (rpact
    src/f_design_group_sequential.cpp: C_CONST_NEWTON_COTES_2 = 15,
    C_NEWTON_COTES_MULTIPLIER = 6, C_FUTILITY_BOUNDS_DEFAULT = -6, weights
    (41,216,27,272,27,216,41)/140*dx).
  * "gsDesign-JT18": Jennison-Turnbull grid with r = 18 (6r-1 base points,
    logarithmic tails beyond +-3, Simpson on points+midpoints, truncated to the
    continuation region) (gsDesign src/gridpts.c).
  * "reference": composite Simpson with 2001 points on [-10, c_{k-1}]
    (a 6001-point variant 'reference-fine' checks the reference itself).

Everything is under H0 (drift 0), one-sided, no futility bound.
Usage: python3 gsd_numint.py
Requires numpy (tested with numpy 2.3.5, Python 3.13).
"""
import math
import time
import functools
print = functools.partial(print, flush=True)
import numpy as np

SQ2 = math.sqrt(2.0)


_erfc = np.frompyfunc(math.erfc, 1, 1)


def Phi(x):
    return 0.5 * _erfc(-np.asarray(x, dtype=float) / SQ2).astype(float)


def Phi_s(x):
    return 0.5 * math.erfc(-x / SQ2)


def phi(x):
    return np.exp(-0.5 * np.asarray(x) ** 2) / math.sqrt(2 * math.pi)


def norm_ppf_upper(p):
    """z with 1 - Phi(z) = p, by bisection on erfc (stdlib only)."""
    lo, hi = -40.0, 40.0
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if 0.5 * math.erfc(mid / SQ2) > p:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


# ---------------------------------------------------------------- grids
def grid_reference(a, b, n=2001):
    x = np.linspace(a, b, n)
    h = (b - a) / (n - 1)
    w = np.ones(n)
    w[1:-1:2] = 4.0
    w[2:-1:2] = 2.0
    return x, w * h / 3.0


def grid_rpact_nc7(a, b, panels=15):
    n = panels * 6 + 1
    x = np.linspace(a, b, n)
    dx = (b - a) / (n - 1)
    base = np.array([41, 216, 27, 272, 27, 216, 41], dtype=float) / 140.0
    w = np.zeros(n)
    for p in range(panels):
        w[p * 6:p * 6 + 7] += base
    return x, w * dx


def grid_gsdesign_jt(a, b, r=18, mu=0.0):
    pts = []
    for i in range(1, 6 * r):
        if i < r:
            z = mu - 3.0 - 4.0 * math.log(r / i)
        elif i <= 5 * r:
            z = mu - 3.0 + 3.0 * (i - r) / (2.0 * r)
        else:
            z = mu + 3.0 + 4.0 * math.log(r / (6.0 * r - i))
        pts.append(z)
    first = pts[0]
    pts = [p for p in pts if a < p < b]
    pts = ([a] if a > first else []) + pts + [b]
    # Simpson on each interval with its midpoint (as in gridpts()): an interior
    # grid point receives (h_left + h_right)/6, a midpoint 4h/6, the two ends h/6.
    xs, ws = [], []
    n = len(pts)
    for i in range(n):
        hl = pts[i] - pts[i - 1] if i > 0 else 0.0
        hr = pts[i + 1] - pts[i] if i < n - 1 else 0.0
        xs.append(pts[i])
        ws.append((hl + hr) / 6.0)
        if i < n - 1:
            xs.append(0.5 * (pts[i] + pts[i + 1]))
            ws.append(4.0 * hr / 6.0)
    return np.array(xs), np.array(ws)


GRIDS = {
    'reference': lambda a, b: grid_reference(-10.0, b),
    'reference-fine': lambda a, b: grid_reference(-10.0, b, 6001),
    'rpact-NC7': lambda a, b: grid_rpact_nc7(-6.0, min(b, 8.0)),
    'gsDesign-JT18': lambda a, b: grid_gsdesign_jt(-1e9, b),
}


# ---------------------------------------------------------------- recursion
def boundaries(t, alpha_cum, gridname):
    """Solve c_1..c_K so that cumulative crossing prob equals alpha_cum[k]."""
    K = len(t)
    c = [norm_ppf_upper(alpha_cum[0])]
    spent = [alpha_cum[0]]
    # density of Z_1 on grid restricted to (-inf, c_1)
    x, w = GRIDS[gridname](None, c[0])
    dens = phi(x)  # f_1 on grid
    for k in range(1, K):
        tk, tk1 = t[k], t[k - 1]
        dk = tk - tk1
        target = alpha_cum[k] - alpha_cum[k - 1]

        def cross(ck):
            arg = (ck * math.sqrt(tk) - x * math.sqrt(tk1)) / math.sqrt(dk)
            return float(np.sum(w * dens * (1.0 - Phi(arg))))

        lo, hi = -10.0, 12.0
        for _ in range(80):
            mid = 0.5 * (lo + hi)
            if cross(mid) > target:
                lo = mid
            else:
                hi = mid
        ck = 0.5 * (lo + hi)
        c.append(ck)
        spent.append(spent[-1] + cross(ck))
        if k < K - 1:
            xn, wn = GRIDS[gridname](None, ck)
            # f_{k+1}(z) = int f_k(u) sqrt(tk/dk) phi((z sqrt(tk) - u sqrt(tk1))/sqrt(dk)) du
            kern = phi((xn[:, None] * math.sqrt(tk) - x[None, :] * math.sqrt(tk1)) / math.sqrt(dk))
            dens = math.sqrt(tk / dk) * kern.dot(w * dens)
            x, w = xn, wn
    return c, spent


def attained_alpha(t, c, gridname='reference'):
    """Total null crossing probability of fixed boundaries c."""
    x, w = GRIDS[gridname](None, c[0])
    total = 1.0 - Phi_s(c[0])
    dens = phi(x)
    for k in range(1, len(t)):
        tk, tk1 = t[k], t[k - 1]
        dk = tk - tk1
        arg = (c[k] * math.sqrt(tk) - x * math.sqrt(tk1)) / math.sqrt(dk)
        total += float(np.sum(w * dens * (1.0 - Phi(arg))))
        if k < len(t) - 1:
            xn, wn = GRIDS[gridname](None, c[k])
            kern = phi((xn[:, None] * math.sqrt(tk) - x[None, :] * math.sqrt(tk1)) / math.sqrt(dk))
            dens = math.sqrt(tk / dk) * kern.dot(w * dens)
            x, w = xn, wn
    return total


# ---------------------------------------------------------------- spending
def sf_ldof(alpha, tt, sided=1):
    # rpact asOF / gsDesign sfLDOF: 2*sided*(1 - Phi(z_{alpha/(2*sided)}/sqrt(t)))
    z = norm_ppf_upper(alpha / (2 * sided))
    return [2 * sided * (1 - Phi_s(z / math.sqrt(x))) for x in tt]


def sf_ldpocock(alpha, tt):
    return [alpha * math.log(1 + (math.e - 1) * x) for x in tt]


def sf_hsd(alpha, tt, gamma):
    return [alpha * (1 - math.exp(-gamma * x)) / (1 - math.exp(-gamma)) for x in tt]


def classical_constant(t, shape, alpha, gridname='reference'):
    """Solve C with c_k = C * shape(t_k) so total null crossing = alpha."""
    lo, hi = 1.0, 6.0
    for _ in range(42):
        mid = 0.5 * (lo + hi)
        if attained_alpha(t, [mid * shape(x) for x in t], gridname) > alpha:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def main():
    alpha = 0.025
    print('== Classical O\'Brien-Fleming, K=2, t=(0.5,1), alpha=0.025 one-sided')
    C = classical_constant([0.5, 1.0], lambda x: 1 / math.sqrt(x), alpha)
    print(f'   C = {C:.6f}; boundaries = {C*math.sqrt(2):.6f}, {C:.6f}; '
          f'stage-1 alpha = {1-Phi_s(C*math.sqrt(2)):.6f}')
    print('== Classical Pocock and OBF constants, two-sided alpha=0.05 (symmetric, '
          'computed as one-sided 0.025 ignoring the negligible lower-crossing overlap)')
    for K in (2, 3, 4, 5):
        t = [(i + 1) / K for i in range(K)]
        cp = classical_constant(t, lambda x: 1.0, 0.025)
        cb = classical_constant(t, lambda x: 1 / math.sqrt(x), 0.025)
        print(f'   K={K}: Pocock C={cp:.4f}   OBF C_B={cb:.4f} (final boundary)')

    cases = [
        ('LD-OF (asOF/sfLDOF)', lambda tt: sf_ldof(alpha, tt)),
        ('LD-Pocock (asP/sfLDPocock)', lambda tt: sf_ldpocock(alpha, tt)),
        ('HSD gamma=-4 (asHSD/sfHSD)', lambda tt: sf_hsd(alpha, tt, -4.0)),
    ]
    for K in (3, 5):
        t = [(i + 1) / K for i in range(K)]
        for name, sf in cases:
            a_cum = sf(t)
            print(f'== {name}, K={K}, equally spaced, alpha={alpha}')
            ref_c = None
            for g in (('reference', 'reference-fine', 'rpact-NC7', 'gsDesign-JT18') if K == 3 else ('reference', 'rpact-NC7', 'gsDesign-JT18')):
                t0 = time.perf_counter()
                c, spent = boundaries(t, a_cum, g)
                el = time.perf_counter() - t0
                att = attained_alpha(t, c, 'reference')
                if g == 'reference':
                    ref_c = c
                    print(f'   cumulative spend: {[round(v, 8) for v in a_cum]}')
                dmax = max(abs(a - b) for a, b in zip(c, ref_c))
                print(f'   {g:14s} c={[round(v, 6) for v in c]} max|c-c_ref|={dmax:.2e} '
                      f'alpha(ref-evaluated)={att:.9f} err={att-alpha:+.2e} time={el:.2f}s')
    # Two-sided OF spending convention comparison (spending at t, per side)
    print('== Per-side cumulative spending of OF-type functions, total two-sided alpha=0.05')
    for x in (0.25, 0.5, 0.75, 1.0):
        rp = sf_ldof(0.05, [x], sided=2)[0] / 2  # rpact sided=2, per side
        z = norm_ppf_upper(0.025)
        ld = (2 - 2 * Phi_s(z / math.sqrt(x))) / 2  # 2-2Phi(z_{alpha/2}/sqrt t), alpha=0.05 total, per side
        print(f'   t={x}: rpact sided=2 (= gsDesign one-sided 0.025) per side={rp:.6f}; '
              f'2-2Phi(z_(alpha/2)/sqrt t) with alpha=0.05, per side={ld:.6f}')


if __name__ == '__main__':
    main()
