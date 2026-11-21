#!/usr/bin/env python3
"""Independent toy implementation (NOT any upstream code) of four limit-equilibrium
methods of slices on a circular slip surface through a simple homogeneous, dry
slope, written from the textbook equilibrium equations:

  OMS     : F = sum[c l + W cos(a) tan(phi)] / sum[W sin(a)]
  Bishop  : F = sum[(c b + W tan(phi)) / m_a] / sum[W sin(a)],
            m_a = cos(a) + sin(a) tan(phi) / F
  GLE     : interslice shear X = lambda * f(x) * E;  per-slice force recursion
            from the left boundary (E_0 = 0) gives E_{n+1}(F, lambda);
            force-equilibrium F_f solves E_{n+1} = 0, moment-equilibrium F_m
            solves sum[(c l + N' tan phi)/F] = sum[W sin a] (circle: interslice
            forces cancel in moments about the centre).
            Spencer: f = 1.  Morgenstern-Price: f = sin(pi s), s in [0, 1].
            The solution is the lambda where F_f(lambda) = F_m(lambda).

Geometry: crest at y = H for x <= 0, face descending to the right to the toe at
(L, 0), level ground y = 0 for x >= L. Slices are vertical strips of equal width
between the circle's entry and exit points; weight by midpoint rule.

This is a toy model used to separate "method" from "search" on fixed surfaces;
its numbers characterise these equations on this geometry, not any product.
"""
import math, sys, time

def ground(x, H, L):
    if x <= 0: return H
    if x >= L: return 0.0
    return H * (1 - x / L)

def intersections(xc, yc, R, H, L):
    """Analytic intersections of the circle's lower arc with the 3-segment ground."""
    pts = []
    # segment lines y = m x + q on x-interval [x0, x1]
    segs = [(0.0, H, -1e9, 0.0), (-H / L, H, 0.0, L), (0.0, 0.0, L, 1e9)]
    for m, q, x0, x1 in segs:
        # (x-xc)^2 + (m x + q - yc)^2 = R^2
        A = 1 + m * m
        B = -2 * xc + 2 * m * (q - yc)
        C = xc * xc + (q - yc) ** 2 - R * R
        D = B * B - 4 * A * C
        if D < 0: continue
        for sgn in (-1.0, 1.0):
            x = (-B + sgn * math.sqrt(D)) / (2 * A)
            y = m * x + q
            if x0 - 1e-12 <= x <= x1 + 1e-12 and y <= yc + 1e-12:
                pts.append(x)
    pts = sorted(set(round(p, 12) for p in pts))
    return pts

def slices(xc, yc, R, H, L, gamma, n):
    pts = intersections(xc, yc, R, H, L)
    if len(pts) < 2: return None
    xl, xr = pts[0], pts[-1]
    b = (xr - xl) / n
    out = []
    for i in range(n):
        xm = xl + (i + 0.5) * b
        yb = yc - math.sqrt(max(R * R - (xm - xc) ** 2, 0.0))
        h = max(ground(xm, H, L) - yb, 0.0)
        a = math.atan2(xc - xm, yc - yb)     # >0 where base descends toward +x
        out.append(dict(x=xm, b=b, W=gamma * b * h, a=a, l=b / math.cos(a), yb=yb))
    return out, xl, xr

def oms(S, c, tphi):
    num = sum(c * s['l'] + max(s['W'] * math.cos(s['a']), 0.0) * tphi for s in S)
    den = sum(s['W'] * math.sin(s['a']) for s in S)
    return num / den if den > 0 else None

def bishop(S, c, tphi, tol=1e-9, itmax=500):
    den = sum(s['W'] * math.sin(s['a']) for s in S)
    if den <= 0: return None, None, None
    F = oms(S, c, tphi) or 1.0
    for it in range(1, itmax + 1):
        num = 0.0; mmin = 1e9
        for s in S:
            m = math.cos(s['a']) + math.sin(s['a']) * tphi / F
            mmin = min(mmin, m)
            num += (c * s['b'] + s['W'] * tphi) / m
        Fn = num / den
        if abs(Fn - F) < tol: return Fn, it, mmin
        F = Fn
    return F, itmax, mmin

def gle_recursion(S, c, tphi, F, lam, fvals):
    """Return (E_{n+1}, list of N') for given F, lambda; fvals has n+1 entries."""
    E = 0.0; X = 0.0; Ns = []
    for i, s in enumerate(S):
        a, W, l = s['a'], s['W'], s['l']
        sa, ca = math.sin(a), math.cos(a)
        ma = ca + sa * tphi / F
        k = sa - tphi * ca / F
        A = E - c * l * ca / F                # U = 0 (dry)
        B = W - X - c * l * sa / F
        fr = fvals[i + 1]
        den = ma - lam * fr * k
        if abs(den) < 1e-12: return None, None
        Np = (B + lam * fr * A) / den
        E = A + k * Np
        X = lam * fr * E
        Ns.append(Np)
    return E, Ns

def root_scan(fun, lo, hi, n=400):
    """Find the smallest-|x - 1.5| root of fun on [lo, hi] by scan + bisection."""
    xs = [lo + (hi - lo) * k / n for k in range(n + 1)]
    vals = [fun(x) for x in xs]
    roots = []
    for k in range(n):
        a, b, fa, fb = xs[k], xs[k + 1], vals[k], vals[k + 1]
        if fa is None or fb is None: continue
        if fa == 0: roots.append(a); continue
        if (fa < 0) != (fb < 0):
            for _ in range(80):
                m = 0.5 * (a + b); fm = fun(m)
                if fm is None: break
                if (fm < 0) == (fa < 0): a, fa = m, fm
                else: b, fb = m, fm
            roots.append(0.5 * (a + b))
    return roots

def gle(S, c, tphi, ftype, Fref):
    n = len(S)
    if ftype == 'spencer':
        fvals = [1.0] * (n + 1)
    else:
        fvals = [math.sin(math.pi * j / n) for j in range(n + 1)]
    den = sum(s['W'] * math.sin(s['a']) for s in S)
    def Ff(lam):
        def r(F):
            E, _ = gle_recursion(S, c, tphi, F, lam, fvals)
            return E
        rts = root_scan(r, 0.3, 5.0, 300)
        return min(rts, key=lambda x: abs(x - Fref)) if rts else None
    def Fm(lam):
        def r(F):
            E, Ns = gle_recursion(S, c, tphi, F, lam, fvals)
            if Ns is None: return None
            return sum((c * s['l'] + Np * tphi) / F for s, Np in zip(S, Ns)) - den
        rts = root_scan(r, 0.3, 5.0, 300)
        return min(rts, key=lambda x: abs(x - Fref)) if rts else None
    def h(lam):
        a, b = Ff(lam), Fm(lam)
        return None if a is None or b is None else a - b
    lams = root_scan(h, -1.0, 1.0, 40)
    if not lams: return None, None
    lam = min(lams, key=abs)
    return Fm(lam), lam

if __name__ == '__main__':
    H, L, gamma, c, phi = 10.0, 20.0, 20.0, 15.0, 20.0
    tphi = math.tan(math.radians(phi))
    zbase = -5.0  # rigid base of the finite-element example (5 m below the toe)
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 50
    t0 = time.perf_counter()
    best = None; count = 0
    # grid search over centres and radii; circles must exit on the ground profile
    for ix in range(0, 41):
        xc = -5.0 + 0.5 * ix
        for iy in range(0, 41):
            yc = 10.0 + 0.5 * iy
            for ir in range(0, 60):
                R = 5.0 + 0.5 * ir
                if yc - R < zbase - 1e-9: continue      # respect the rigid base
                res = slices(xc, yc, R, H, L, gamma, n)
                if res is None: continue
                S, xl, xr = res
                if xr - xl < 2.0: continue
                Fb, it, mmin = bishop(S, c, tphi)
                if Fb is None: continue
                count += 1
                if best is None or Fb < best[0]:
                    best = (Fb, xc, yc, R, xl, xr, it, mmin)
    t1 = time.perf_counter()
    Fb, xc, yc, R, xl, xr, it, mmin = best
    S, _, _ = slices(xc, yc, R, H, L, gamma, n)
    Fo = oms(S, c, tphi)
    Fs, ls = gle(S, c, tphi, 'spencer', Fb)
    Fmp, lmp = gle(S, c, tphi, 'msin', Fb)
    t2 = time.perf_counter()
    print(f"slices={n} circles_evaluated={count} search_wall_s={t1-t0:.2f}")
    print(f"critical(Bishop) centre=({xc:.2f},{yc:.2f}) R={R:.2f} entry_x={xl:.3f} exit_x={xr:.3f} lowest_y={yc-R:.2f}")
    print(f"OMS={Fo:.4f} Bishop={Fb:.4f} (iters={it}, min m_alpha={mmin:.3f}) Spencer={Fs:.4f} (lambda={ls:.4f}) MP_halfsine={Fmp:.4f} (lambda={lmp:.4f})")
    print(f"gle_wall_s={t2-t1:.2f}")
