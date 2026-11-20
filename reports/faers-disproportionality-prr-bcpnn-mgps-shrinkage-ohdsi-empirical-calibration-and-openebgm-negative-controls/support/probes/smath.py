#!/usr/bin/env python3
"""Small numerical helpers (numpy only; no scipy) used by the probe scripts.

All functions are independent re-implementations of textbook formulas:
digamma/trigamma (recurrence + asymptotic series), regularized lower incomplete
gamma P(a, x) (series / Lentz continued fraction), normal CDF via math.erf, and a
plain Nelder-Mead minimizer.
"""
import math

import numpy as np

_lgamma = np.vectorize(math.lgamma, otypes=[float])


def lgamma(x):
    return _lgamma(np.asarray(x, dtype=float))


def digamma(x):
    x = np.array(x, dtype=float, copy=True)
    res = np.zeros_like(x)
    small = x < 6.0
    while np.any(small):
        res[small] -= 1.0 / x[small]
        x[small] += 1.0
        small = x < 6.0
    inv = 1.0 / x
    inv2 = inv * inv
    res += (np.log(x) - 0.5 * inv
            - inv2 * (1.0 / 12 - inv2 * (1.0 / 120 - inv2 * (1.0 / 252 - inv2 * (1.0 / 240 - inv2 / 132)))))
    return res


def trigamma(x):
    x = np.array(x, dtype=float, copy=True)
    res = np.zeros_like(x)
    small = x < 6.0
    while np.any(small):
        res[small] += 1.0 / (x[small] ** 2)
        x[small] += 1.0
        small = x < 6.0
    inv = 1.0 / x
    inv2 = inv * inv
    res += inv + 0.5 * inv2 + inv * inv2 * (1.0 / 6 - inv2 * (1.0 / 30 - inv2 * (1.0 / 42 - inv2 / 30)))
    return res


def gammainc_lower_reg(a, x, iters=400):
    """Regularized lower incomplete gamma P(a, x) == pgamma(x, shape=a, rate=1)."""
    a = np.broadcast_to(np.asarray(a, dtype=float), np.broadcast(a, x).shape).copy()
    x = np.broadcast_to(np.asarray(x, dtype=float), a.shape).copy()
    out = np.zeros_like(a)
    pos = x > 0
    lg = lgamma(a)
    with np.errstate(divide="ignore", invalid="ignore"):
        logpref = np.where(pos, a * np.log(np.where(pos, x, 1.0)) - x - lg, -np.inf)
    ser = pos & (x < a + 1.0)
    if np.any(ser):
        aa, xx = a[ser], x[ser]
        term = 1.0 / aa
        total = term.copy()
        ap = aa.copy()
        for _ in range(iters):
            ap += 1.0
            term *= xx / ap
            total += term
        out[ser] = np.exp(logpref[ser]) * total
    cf = pos & ~ser
    if np.any(cf):
        aa, xx = a[cf], x[cf]
        tiny = 1e-300
        b = xx + 1.0 - aa
        c = np.full_like(xx, 1.0 / tiny)
        d = 1.0 / b
        h = d.copy()
        for i in range(1, iters):
            an = -i * (i - aa)
            b += 2.0
            d = an * d + b
            d = np.where(np.abs(d) < tiny, tiny, d)
            c = b + an / c
            c = np.where(np.abs(c) < tiny, tiny, c)
            d = 1.0 / d
            h *= d * c
        out[cf] = 1.0 - np.exp(logpref[cf]) * h
    return out


def pgamma(q, shape, rate):
    return gammainc_lower_reg(shape, np.asarray(q, dtype=float) * rate)


def pnorm(z):
    z = np.asarray(z, dtype=float)
    return 0.5 * (1.0 + np.vectorize(math.erf)(z / math.sqrt(2.0)))


def qnorm(p):
    """Inverse normal CDF by bisection (adequate for probes)."""
    lo, hi = -40.0, 40.0
    for _ in range(200):
        mid = 0.5 * (lo + hi)
        if 0.5 * (1.0 + math.erf(mid / math.sqrt(2.0))) < p:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def nelder_mead(f, x0, step=0.5, iters=20000, ftol=1e-12, xtol=1e-10):
    n = len(x0)
    pts = [np.array(x0, dtype=float)]
    for i in range(n):
        p = np.array(x0, dtype=float)
        p[i] += step
        pts.append(p)
    vals = [f(p) for p in pts]
    for it in range(iters):
        order = np.argsort(vals)
        pts = [pts[i] for i in order]
        vals = [vals[i] for i in order]
        if abs(vals[-1] - vals[0]) < ftol and max(np.max(np.abs(p - pts[0])) for p in pts[1:]) < xtol:
            break
        centroid = np.mean(pts[:-1], axis=0)
        xr = centroid + (centroid - pts[-1])
        fr = f(xr)
        if fr < vals[0]:
            xe = centroid + 2.0 * (centroid - pts[-1])
            fe = f(xe)
            if fe < fr:
                pts[-1], vals[-1] = xe, fe
            else:
                pts[-1], vals[-1] = xr, fr
        elif fr < vals[-2]:
            pts[-1], vals[-1] = xr, fr
        else:
            xc = centroid + 0.5 * (pts[-1] - centroid)
            fc = f(xc)
            if fc < vals[-1]:
                pts[-1], vals[-1] = xc, fc
            else:
                for i in range(1, len(pts)):
                    pts[i] = pts[0] + 0.5 * (pts[i] - pts[0])
                    vals[i] = f(pts[i])
    i = int(np.argmin(vals))
    return pts[i], vals[i], it


def minimize_restarts(f, x0, restarts=6, step=0.5):
    x, v = np.array(x0, dtype=float), f(np.array(x0, dtype=float))
    for _ in range(restarts):
        x, v, _ = nelder_mead(f, x, step=step)
        step *= 0.5
    return x, v
