#!/usr/bin/env python3
"""TOY MODEL. Branch-and-bound proof of polynomial lower bounds on boxes with
three enclosure methods, all in exact rational arithmetic (fractions.Fraction):

  interval  : natural interval extension of the expanded monomial form
  taylor2   : second-order Taylor bound in the style of Solovyev-Hales
              f(x) >= f(c) - sum_i |f_i(c)| w_i - 1/2 sum_ij w_i w_j max_box|f_ij|
              (max_box|f_ij| bounded by the interval method)
  bernstein : minimum Bernstein coefficient of the polynomial on the box

The benchmark inequalities are the polynomial examples shipped with the
formal_ineqs verifier (examples_poly.hl; originally from Munoz-Narkawicz,
J. Autom. Reasoning 51, 2013), with the same lower bounds and boxes.

This program is NOT HOL Light, PVS, or Coq. It does not produce a formal proof.
It measures, for one simple subdivision policy (bisect the widest side), how
many leaf boxes each enclosure method needs before every leaf's lower bound
exceeds the target. Leaf counts are a proxy for certificate size in tools whose
certificate is a subdivision tree (formal_ineqs, PVS Bernstein strategies); the
real tools add monotonicity, convexity and adaptive-precision refinements that
this toy omits. Times are wall-clock for this pure-Python code only.

Usage: python3 bounds_toy.py [max_boxes_per_run]   (default 4000)
"""
import sys
import time
from fractions import Fraction as F
from math import comb

CAP = int(sys.argv[1]) if len(sys.argv) > 1 else 4000

# ---------------- polynomials: dict exponent-tuple -> Fraction ----------------

def padd(p, q, s=1):
    r = dict(p)
    for m, c in q.items():
        r[m] = r.get(m, 0) + s * c
        if r[m] == 0:
            del r[m]
    return r

def pmul(p, q):
    r = {}
    for m1, c1 in p.items():
        for m2, c2 in q.items():
            m = tuple(a + b for a, b in zip(m1, m2))
            r[m] = r.get(m, 0) + c1 * c2
    return {m: c for m, c in r.items() if c != 0}

def var(i, n):
    return {tuple(1 if k == i else 0 for k in range(n)): F(1)}

def const(c, n):
    return {tuple([0] * n): F(c)} if c != 0 else {}

def ppow(p, e, n):
    r = const(1, n)
    for _ in range(e):
        r = pmul(r, p)
    return r

def deriv(p, i):
    r = {}
    for m, c in p.items():
        if m[i] > 0:
            mm = list(m); mm[i] -= 1
            r[tuple(mm)] = r.get(tuple(mm), 0) + c * m[i]
    return r

def peval(p, x):
    s = F(0)
    for m, c in p.items():
        t = c
        for xi, e in zip(x, m):
            if e:
                t *= xi ** e
        s += t
    return s

# ---------------- enclosures ----------------

def ipow(lo, hi, e):
    if e == 0:
        return F(1), F(1)
    a, b = lo ** e, hi ** e
    if e % 2 == 0 and lo < 0 < hi:
        return F(0), max(a, b)
    return min(a, b), max(a, b)

def interval_range(p, box):
    lo_s, hi_s = F(0), F(0)
    for m, c in p.items():
        lo, hi = F(1), F(1)
        for (a, b), e in zip(box, m):
            if e:
                l2, h2 = ipow(a, b, e)
                cands = (lo * l2, lo * h2, hi * l2, hi * h2)
                lo, hi = min(cands), max(cands)
        if c >= 0:
            lo_s += c * lo; hi_s += c * hi
        else:
            lo_s += c * hi; hi_s += c * lo
    return lo_s, hi_s

def lb_interval(ctx, box):
    return interval_range(ctx["p"], box)[0]

def lb_taylor2(ctx, box):
    n = len(box)
    c = [(a + b) / 2 for a, b in box]
    w = [(b - a) / 2 for a, b in box]
    v = peval(ctx["p"], c)
    for i in range(n):
        v -= abs(peval(ctx["d1"][i], c)) * w[i]
    for i in range(n):
        for j in range(n):
            d2 = ctx["d2"][i][j]
            if d2:
                lo, hi = interval_range(d2, box)
                v -= F(1, 2) * w[i] * w[j] * max(abs(lo), abs(hi))
    return v

def bernstein_coeffs(p, box, degs):
    n = len(box)
    # q(t) = p(a + h t) on [0,1]^n
    q = {}
    for m, c in p.items():
        terms = {tuple([0] * n): c}
        for k, ((a, b), e) in enumerate(zip(box, m)):
            if e == 0:
                continue
            h = b - a
            new = {}
            for mm, cc in terms.items():
                for j in range(e + 1):
                    coef = comb(e, j) * a ** (e - j) * h ** j
                    if coef == 0:
                        continue
                    m2 = list(mm); m2[k] += j
                    new[tuple(m2)] = new.get(tuple(m2), 0) + cc * coef
            terms = new
        for mm, cc in terms.items():
            q[mm] = q.get(mm, 0) + cc
    # tensor-product power-to-Bernstein transform, axis by axis
    arr = q
    for k in range(n):
        d = degs[k]
        groups = {}
        for mm, cc in arr.items():
            key = mm[:k] + mm[k + 1:]
            groups.setdefault(key, {})[mm[k]] = cc
        new = {}
        for key, col in groups.items():
            for i in range(d + 1):
                s = F(0)
                for j in range(i + 1):
                    if j in col:
                        s += F(comb(i, j), comb(d, j)) * col[j]
                if s != 0:
                    new[key[:k] + (i,) + key[k:]] = s
        arr = new
    return arr

def lb_bernstein(ctx, box):
    b = bernstein_coeffs(ctx["p"], box, ctx["degs"])
    # absent coefficients are zero
    total = 1
    for d in ctx["degs"]:
        total *= d + 1
    m = min(b.values()) if b else F(0)
    if len(b) < total:
        m = min(m, F(0))
    return m

METHODS = {"interval": lb_interval, "taylor2": lb_taylor2, "bernstein": lb_bernstein}

def prove(ctx, box0, target, lbf):
    work = [box0]
    leaves = 0
    processed = 0
    maxdepth = 0
    depth = {tuple(box0): 0}
    t0 = time.perf_counter()
    while work:
        box = work.pop()
        processed += 1
        if processed > CAP:
            return dict(status="cap", leaves=leaves, processed=processed - 1,
                        secs=time.perf_counter() - t0, depth=maxdepth)
        if lbf(ctx, box) > target:
            leaves += 1
            continue
        c = [(a + b) / 2 for a, b in box]
        if peval(ctx["p"], c) <= target:
            return dict(status="counterexample", leaves=leaves, processed=processed,
                        secs=time.perf_counter() - t0, depth=maxdepth)
        k = max(range(len(box)), key=lambda i: box[i][1] - box[i][0])
        a, b = box[k]
        m = (a + b) / 2
        d = depth.pop(tuple(box), 0) + 1
        maxdepth = max(maxdepth, d)
        for half in ((a, m), (m, b)):
            nb = list(box); nb[k] = half
            depth[tuple(nb)] = d
            work.append(nb)
    return dict(status="proved", leaves=leaves, processed=processed,
                secs=time.perf_counter() - t0, depth=maxdepth)

# ---------------- benchmarks (formal_ineqs examples_poly.hl) ----------------

def bench():
    B = []
    n = 3; x = [var(i, n) for i in range(n)]
    sq = lambda p: pmul(p, p)
    p = padd(padd(padd(sq(padd(x[0], ppow(x[1], 2, n), -1)), sq(padd(x[1], const(1, n), -1))),
                  sq(padd(x[0], ppow(x[2], 2, n), -1))), sq(padd(x[2], const(1, n), -1)))
    B.append(("schwefel", p, [(F(-10), F(10))] * 3, F("-5.8806e-10")))
    p = padd(padd(padd(const(0, n), x[0], -1), pmul(const(2, n), x[1])), x[2], -1)
    p = padd(p, pmul(const(F("0.835634534"), n), pmul(x[1], padd(const(1, n), x[1]))), -1)
    B.append(("rd", p, [(F(-5), F(5))] * 3, F("-36.7126907")))
    n = 4; x = [var(i, n) for i in range(n)]
    C = lambda c: const(c, n)
    terms = [pmul(C(-1), pmul(x[0], ppow(x[2], 3, n))), pmul(C(4), pmul(x[1], pmul(ppow(x[2], 2, n), x[3]))),
             pmul(C(4), pmul(x[0], pmul(x[2], ppow(x[3], 2, n)))), pmul(C(2), pmul(x[1], ppow(x[3], 3, n))),
             pmul(C(4), pmul(x[0], x[2])), pmul(C(4), ppow(x[2], 2, n)), pmul(C(-10), pmul(x[1], x[3])),
             pmul(C(-10), ppow(x[3], 2, n)), C(2)]
    p = {}
    for t in terms:
        p = padd(p, t)
    B.append(("caprasse", p, [(F("-0.5"), F("0.5"))] * 4, F("-3.1801")))
    terms = [pmul(x[0], ppow(x[1], 2, n)), pmul(x[0], ppow(x[2], 2, n)), pmul(x[0], ppow(x[3], 2, n)),
             pmul(C(F("-1.1")), x[0]), C(1)]
    p = {}
    for t in terms:
        p = padd(p, t)
    B.append(("lv", p, [(F(-2), F(2))] * 4, F("-20.801")))
    n = 6; x = [var(i, n) for i in range(n)]
    C = lambda c: const(c, n)
    terms = [pmul(x[5], ppow(x[1], 2, n)), pmul(x[4], ppow(x[2], 2, n)), pmul(C(-1), pmul(x[0], ppow(x[3], 2, n))),
             ppow(x[3], 2, n), pmul(C(F(-1, 3)), x[0]), pmul(C(F(4, 3)), x[3])]
    p = {}
    for t in terms:
        p = padd(p, t)
    lo = [F(-1), F("-0.1"), F("-0.1"), F(-1), F("-0.1"), F("-0.1")]
    hi = [F(0), F("0.9"), F("0.5"), F("-0.1"), F("-0.05"), F("-0.03")]
    B.append(("butcher", p, list(zip(lo, hi)), F("-1.44")))
    n = 7; x = [var(i, n) for i in range(n)]
    p = padd(ppow(x[0], 2, n), x[0], -1)
    for i in range(1, 7):
        p = padd(p, pmul(const(2, n), ppow(x[i], 2, n)))
    B.append(("magnetism", p, [(F(-1), F(1))] * 7, F("-0.25001")))
    n = 8; x = [var(i, n) for i in range(n)]
    C = lambda c: const(c, n)
    X = lambda i: x[i - 1]
    terms = [pmul(C(-1), pmul(X(1), ppow(X(6), 3, n))), pmul(C(3), pmul(X(1), pmul(X(6), ppow(X(7), 2, n)))),
             pmul(C(-1), pmul(X(3), ppow(X(7), 3, n))), pmul(C(3), pmul(X(3), pmul(X(7), ppow(X(6), 2, n)))),
             pmul(C(-1), pmul(X(2), ppow(X(5), 3, n))), pmul(C(3), pmul(X(2), pmul(X(5), ppow(X(8), 2, n)))),
             pmul(C(-1), pmul(X(4), ppow(X(8), 3, n))), pmul(C(3), pmul(X(4), pmul(X(8), ppow(X(5), 2, n)))),
             C(F("-0.9563453"))]
    p = {}
    for t in terms:
        p = padd(p, t)
    lo = [F("-0.1"), F("0.4"), F("-0.7"), F("-0.7"), F("0.1"), F("-0.1"), F("-0.3"), F("-1.1")]
    hi = [F("0.4"), F(1), F("-0.4"), F("0.4"), F("0.2"), F("0.2"), F("1.1"), F("-0.3")]
    B.append(("heart", p, list(zip(lo, hi)), F("-1.7435")))
    return B

def main():
    print("cap (max boxes processed per run):", CAP)
    print("%-10s %-10s %-14s %8s %9s %6s %9s" % ("problem", "method", "status", "leaves", "processed", "depth", "seconds"))
    for name, p, box, target in bench():
        n = len(box)
        ctx = {"p": p,
               "d1": [deriv(p, i) for i in range(n)],
               "d2": [[deriv(deriv(p, i), j) for j in range(n)] for i in range(n)],
               "degs": [max((m[k] for m in p), default=0) for k in range(n)]}
        for meth, f in METHODS.items():
            r = prove(ctx, list(box), target, f)
            print("%-10s %-10s %-14s %8d %9d %6d %9.3f" % (name, meth, r["status"], r["leaves"], r["processed"], r["depth"], r["secs"]))
        sys.stdout.flush()

if __name__ == "__main__":
    main()
