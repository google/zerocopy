#!/usr/bin/env python3
"""Prospective sample-size probes for binary pass/fail checker evaluations.

Standard library only (math, statistics.NormalDist).  Every number printed is
computed here; nothing is fitted or simulated except where stated.

Sections
  A  Connor-type closed form vs exact McNemar power by enumeration
  B  Unpaired two-proportion n vs paired McNemar n under within-pair correlation
  C  Binomial precision sizing (Wald, Wilson, Clopper-Pearson)
  D  Paired-proportion TOST: closed form vs exact power (trinomial enumeration),
     plus a re-implementation of the TOSTER unpaired power_twoprop formula
  E  Neyman vs proportional vs equal allocation for a stratified pass rate
"""
import math
import sys
from statistics import NormalDist

N01 = NormalDist()
z = N01.inv_cdf
Phi = N01.cdf


# ---------------------------------------------------------------- helpers
def log_binom_pmf_row(n, p):
    """Return list of binomial pmf values P(X=k), k=0..n (log-space safe)."""
    if p <= 0.0:
        return [1.0] + [0.0] * n
    if p >= 1.0:
        return [0.0] * n + [1.0]
    lp, lq = math.log(p), math.log1p(-p)
    lg = math.lgamma
    out = []
    for k in range(n + 1):
        out.append(math.exp(lg(n + 1) - lg(k + 1) - lg(n - k + 1) + k * lp + (n - k) * lq))
    return out


def half_cdf_table(m):
    """For X~Bin(m,1/2): list of P(X<=k) and pmf, k=0..m (exact rationals->float)."""
    tot = 2 ** m
    pmf = [math.comb(m, k) / tot for k in range(m + 1)]
    cdf, s = [], 0.0
    for v in pmf:
        s += v
        cdf.append(s)
    return pmf, cdf


_crit_cache = {}


def mcnemar_crit(m, alpha, method):
    """Largest k such that the two-sided test rejects when min(n10,n01)=k
    among m discordant pairs; -1 if no rejection possible.
    method: 'exact' (exact conditional, doubled one-sided p),
            'midp'  (mid-p, Fagerland et al. 2013 eq.),
            'asym'  (asymptotic McNemar Z=(b-c)/sqrt(b+c), no continuity corr.)
            'asymcc' (asymptotic with continuity correction |b-c|-1)."""
    key = (m, alpha, method)
    if key in _crit_cache:
        return _crit_cache[key]
    best = -1
    if m == 0:
        _crit_cache[key] = -1
        return -1
    if method in ("exact", "midp"):
        pmf, cdf = half_cdf_table(m)
        for k in range(0, m // 2 + 1):
            if method == "exact":
                p = min(1.0, 2.0 * cdf[k])
            else:
                p = min(1.0, 2.0 * (cdf[k] - 0.5 * pmf[k]))
            if p <= alpha + 1e-15:
                best = k
            else:
                break
    else:
        zc = z(1 - alpha / 2)
        for k in range(0, m // 2 + 1):
            b, c = m - k, k
            num = abs(b - c) - (1 if method == "asymcc" else 0)
            stat = num / math.sqrt(m)
            if stat > zc:
                best = k
            else:
                break
    _crit_cache[key] = best
    return best


def mcnemar_power(n, p10, p01, alpha=0.05, method="exact"):
    """Exact unconditional power of a two-sided McNemar-family test for n pairs
    with discordant cell probabilities p10, p01 (enumeration over the
    trinomial via m=n10+n01 ~ Bin(n,psi), n10|m ~ Bin(m, p10/psi))."""
    psi = p10 + p01
    pm = log_binom_pmf_row(n, psi)
    pi = p10 / psi
    power = 0.0
    for m in range(1, n + 1):
        w = pm[m]
        if w < 1e-300:
            continue
        k = mcnemar_crit(m, alpha, method)
        if k < 0:
            continue
        row = log_binom_pmf_row(m, pi)
        lo = sum(row[: k + 1])            # n10 <= k
        hi = sum(row[m - k:])             # n10 >= m-k
        if 2 * k >= m:                    # overlap guard (cannot happen for k<=m//2 with p<=alpha<1)
            hi = 0.0
        power += w * (lo + hi)
    return power


def connor_n(p10, p01, alpha=0.05, power=0.8):
    """Connor (1987)-form closed formula, two-sided alpha:
    n = (z_{1-a/2} sqrt(psi) + z_{1-b} sqrt(psi - d^2))^2 / d^2."""
    psi, d = p10 + p01, p10 - p01
    return (z(1 - alpha / 2) * math.sqrt(psi) + z(power) * math.sqrt(psi - d * d)) ** 2 / (d * d)


def smallest_n_reaching(fun, target, lo, hi):
    """Smallest n in [lo,hi] with fun(n)>=target, and the smallest n0 such that
    fun(n)>=target for all n in [n0, hi] (exact tests are saw-toothed)."""
    first = None
    vals = {}
    for n in range(lo, hi + 1):
        v = fun(n)
        vals[n] = v
        if first is None and v >= target:
            first = n
    stable = None
    for n in range(hi, lo - 1, -1):
        if vals[n] >= target:
            stable = n
        else:
            break
    return first, stable, vals


# ---------------------------------------------------------------- A
def section_a():
    print("== A. McNemar: Connor closed form vs exact power by enumeration (alpha=0.05 two-sided)")
    # size (type I error) at delta = 0
    print("A.1 actual size at p10=p01 (psi=0.20): n, exact, midp, asym, asymcc")
    for n in (20, 50, 100, 200):
        row = [mcnemar_power(n, 0.10, 0.10, 0.05, m) for m in ("exact", "midp", "asym", "asymcc")]
        print("   n=%4d  " % n + "  ".join("%.4f" % v for v in row))
    print("A.2 n for target power; delta=p10-p01, psi=p10+p01")
    print("   delta  psi   p10    p01   | Connor80 | first/stable n (80%): exact  midp  asym | Connor90 | first/stable n (90%): exact midp asym")
    settings = [(0.10, 0.12), (0.10, 0.20), (0.10, 0.30), (0.10, 0.40), (0.05, 0.10), (0.05, 0.20), (0.20, 0.30)]
    for d, psi in settings:
        p10, p01 = (psi + d) / 2, (psi - d) / 2
        c80, c90 = connor_n(p10, p01, 0.05, 0.8), connor_n(p10, p01, 0.05, 0.9)
        hi = int(math.ceil(c90 * 1.35)) + 10
        lo = max(5, int(c80 * 0.6))
        res = {}
        for meth in ("exact", "midp", "asym"):
            f80, s80, vals = smallest_n_reaching(lambda n: mcnemar_power(n, p10, p01, 0.05, meth), 0.8, lo, hi)
            f90 = next((n for n in range(lo, hi + 1) if vals[n] >= 0.9), None)
            s90 = None
            for n in range(hi, lo - 1, -1):
                if vals[n] >= 0.9:
                    s90 = n
                else:
                    break
            res[meth] = (f80, s80, f90, s90)
        print("   %.2f  %.2f  %.3f  %.3f | %7.1f | %s | %7.1f | %s" % (
            d, psi, p10, p01, c80,
            "  ".join("%s/%s" % (res[m][0], res[m][1]) for m in ("exact", "midp", "asym")),
            c90,
            "  ".join("%s/%s" % (res[m][2], res[m][3]) for m in ("exact", "midp", "asym"))))
    print("A.3 same marginals (pA=0.80, pB=0.70), different psi -> different n (Connor 80%):")
    for psi in (0.10, 0.14, 0.20, 0.30, 0.40, 0.50):
        p10, p01 = (psi + 0.10) / 2, (psi - 0.10) / 2
        if p01 < 0:
            continue
        # implied p11 for pA=0.8: p11 = pA - p10
        p11 = 0.80 - p10
        p00 = 1 - p11 - p10 - p01
        ok = min(p11, p00) >= -1e-12
        print("   psi=%.2f p11=%.3f p10=%.3f p01=%.3f p00=%.3f feasible=%s  n80=%.1f" % (
            psi, p11, p10, p01, p00, ok, connor_n(p10, p01) if p01 > 0 else float('nan')))


# ---------------------------------------------------------------- B
def unpaired_n_per_group(p1, p2, alpha=0.05, power=0.8):
    """Fleiss (no continuity correction) two-sample n per group, two-sided."""
    pbar = (p1 + p2) / 2
    num = z(1 - alpha / 2) * math.sqrt(2 * pbar * (1 - pbar)) + z(power) * math.sqrt(p1 * (1 - p1) + p2 * (1 - p2))
    return num ** 2 / (p1 - p2) ** 2


def section_b():
    print("== B. Unpaired vs paired, pA=0.80 pB=0.70 (delta=0.10), alpha=0.05, power=0.80")
    pA, pB = 0.80, 0.70
    nu = unpaired_n_per_group(pA, pB)
    print("   unpaired: n per group = %.1f -> %d instances, %d checker runs" % (nu, 2 * math.ceil(nu), 2 * math.ceil(nu)))
    sA, sB = math.sqrt(pA * (1 - pA)), math.sqrt(pB * (1 - pB))
    rho_max = (min(pA, pB) - pA * pB) / (sA * sB)
    print("   max feasible phi for these marginals = %.4f" % rho_max)
    print("   phi    p11     psi    Connor n80 (pairs = instances; runs = 2n)  exact-cond first/stable n80")
    for rho in (0.0, 0.2, 0.4, 0.6, 0.8):
        if rho > rho_max + 1e-12:
            continue
        p11 = pA * pB + rho * sA * sB
        p10, p01 = pA - p11, pB - p11
        psi = p10 + p01
        cn = connor_n(p10, p01)
        lo, hi = max(5, int(cn * 0.7)), int(cn * 1.5) + 10
        f, s, _ = smallest_n_reaching(lambda n: mcnemar_power(n, p10, p01, 0.05, "exact"), 0.8, lo, hi)
        print("   %.1f   %.4f  %.4f  %8.1f -> %4d instances, %4d runs      %s/%s" % (
            rho, p11, psi, cn, math.ceil(cn), 2 * math.ceil(cn), f, s))


# ---------------------------------------------------------------- C
def binom_cdf(x, n, p):
    if x < 0:
        return 0.0
    if x >= n:
        return 1.0
    return sum(log_binom_pmf_row(n, p)[: x + 1])


def clopper_pearson(x, n, alpha=0.05):
    def solve(f, lo, hi):
        for _ in range(100):
            mid = (lo + hi) / 2
            if f(mid):
                hi = mid
            else:
                lo = mid
        return (lo + hi) / 2
    lower = 0.0 if x == 0 else solve(lambda p: 1 - binom_cdf(x - 1, n, p) >= alpha / 2, 0.0, 1.0)
    upper = 1.0 if x == n else solve(lambda p: binom_cdf(x, n, p) <= alpha / 2, 0.0, 1.0)
    return lower, upper


def wilson(x, n, alpha=0.05):
    zc = z(1 - alpha / 2)
    ph = x / n
    den = 1 + zc * zc / n
    c = (ph + zc * zc / (2 * n)) / den
    h = zc * math.sqrt(ph * (1 - ph) / n + zc * zc / (4 * n * n)) / den
    return c - h, c + h


def section_c():
    print("== C. Precision sizing for a single pass rate, 95% two-sided")
    zc = z(0.975)
    for p in (0.3, 0.5, 0.9):
        for h in (0.05, 0.10):
            wald = zc * zc * p * (1 - p) / (h * h)
            # Wilson / CP: smallest n with half-width <= h at x = round(p n)
            nw = next(n for n in range(5, 5000) if (lambda lu: (lu[1] - lu[0]) / 2 <= h)(wilson(round(p * n), n)))
            ncp = next(n for n in range(max(5, int(wald * 0.8)), 6000)
                       if (lambda lu: (lu[1] - lu[0]) / 2 <= h)(clopper_pearson(round(p * n), n)))
            print("   p=%.1f h=%.2f  Wald n=%.1f->%d  Wilson n=%d  Clopper-Pearson n=%d" % (p, h, wald, math.ceil(wald), nw, ncp))
    print("   small-n illustration (CP and Wilson 95%):")
    for x, n in ((3, 10), (6, 20), (12, 40), (30, 100), (60, 200), (2, 6), (6, 12), (36, 120)):
        cl, cu = clopper_pearson(x, n)
        wl, wu = wilson(x, n)
        print("   x/n=%3d/%3d  CP=[%.3f, %.3f] width=%.3f   Wilson=[%.3f, %.3f] width=%.3f" % (x, n, cl, cu, cu - cl, wl, wu, wu - wl))
    print("   falsifiability: smallest n such that a predicted band p0+-w can be refuted")
    print("   by a CP interval excluding the band when the truth is p1 (point check at x=round(p1 n)):")
    for p0, w, p1 in ((0.30, 0.10, 0.55), (0.30, 0.05, 0.45), (0.80, 0.05, 0.65)):
        n = next(n for n in range(5, 5000)
                 if (lambda lu: lu[0] > p0 + w or lu[1] < p0 - w)(clopper_pearson(round(p1 * n), n)))
        print("   band=[%.2f,%.2f] truth=%.2f -> n=%d" % (p0 - w, p0 + w, p1, n))


# ---------------------------------------------------------------- D
def tost_paired_exact_power(n, p10, p01, margin, alpha=0.05):
    """Exact power of the Wald paired-difference TOST: conclude equivalence iff
    (d +/- z_{1-alpha} se) lies inside (-margin, margin), with
    d=(n10-n01)/n, se=sqrt((n10+n01)/n - d^2)/sqrt(n); enumerate trinomial."""
    zc = z(1 - alpha)
    lg = math.lgamma
    p00 = 1 - p10 - p01
    l10, l01, l00 = math.log(p10), math.log(p01), math.log(p00) if p00 > 0 else None
    tot = 0.0
    lfn = lg(n + 1)
    for a in range(n + 1):
        for b in range(n + 1 - a):
            c = n - a - b
            if c > 0 and l00 is None:
                continue
            d = (a - b) / n
            var = ((a + b) / n - d * d) / n
            se = math.sqrt(max(var, 0.0))
            if d - zc * se > -margin and d + zc * se < margin:
                lp = lfn - lg(a + 1) - lg(b + 1) - lg(c + 1) + a * l10 + b * l01 + (c * l00 if c else 0.0)
                tot += math.exp(lp)
    return tot


def tost_paired_n(psi, delta1, margin, alpha=0.05, power=0.8):
    """Closed-form normal approximations for paired-difference TOST.
    delta1 = 0: n = (z_{1-a} + z_{1-b/2})^2 psi / margin^2
    delta1 != 0: n = (z_{1-a} + z_{1-b})^2 (psi - delta1^2) / (margin - |delta1|)^2"""
    if delta1 == 0:
        return (z(1 - alpha) + z(1 - (1 - power) / 2)) ** 2 * psi / margin ** 2
    return (z(1 - alpha) + z(power)) ** 2 * (psi - delta1 ** 2) / (margin - abs(delta1)) ** 2


def toster_pow_prop_tost(p1, p2, n, margin, alpha):
    """Python transcription of TOSTER R/power_two_proportions.R pow_prop_tost
    p.body (lines 236-240) with null = c(margin, -margin)."""
    se = math.sqrt(p1 * (1 - p1) / n + p2 * (1 - p2) / n)
    za = z(1 - alpha)
    d = abs(p1 - p2)
    lo_b, hi_b = -margin, margin
    s1 = 2 * (Phi((d - lo_b) / se - za) + Phi(-(d - lo_b) / se - za)) - 1
    s2 = 2 * (Phi((d - hi_b) / se - za) + Phi(-(d - hi_b) / se - za)) - 1
    return max(0.0, min(s1, s2))


def toster_closed_n(p1, p2, margin, alpha, power):
    """Transcription of deprecated powerTOSTtwo.prop N formula (lines 79-81)."""
    k = (z(1 - alpha) + z(1 - (1 - power) / 2))
    a = (p1 * (1 - p1) + p2 * (1 - p2)) * (k / (abs(p1 - p2) - margin)) ** 2
    return a


def uniroot_n(f, target, lo=4 + 1e-10, hi=1e7):
    for _ in range(200):
        mid = (lo + hi) / 2
        if f(mid) >= target:
            hi = mid
        else:
            lo = mid
    return hi


def section_d():
    print("== D. Equivalence (TOST) sizing")
    print("D.1 TOSTER unpaired two-proportion formulas re-implemented (per-group n):")
    for (p1, p2, m, a, pw) in ((0.5, 0.5, 0.1, 0.05, 0.9), (0.75, 0.8, 0.2, 0.05, 0.8), (0.8, 0.8, 0.1, 0.025, 0.9), (0.5, 0.5, 0.2, 0.01, 0.8), (0.8, 0.8, 0.1, 0.05, 0.8)):
        nc = toster_closed_n(p1, p2, m, a, pw)
        nr = uniroot_n(lambda n: toster_pow_prop_tost(p1, p2, n, m, a), pw)
        print("   p1=%.2f p2=%.2f margin=%.2f alpha=%.3f power=%.1f  closed N=%.2f (ceil %d)  uniroot n=%.2f  power(n=542)=%s" % (
            p1, p2, m, a, pw, nc, math.ceil(nc), nr,
            ("%.4f" % toster_pow_prop_tost(p1, p2, 542, m, a)) if (p1, p2, m, a) == (0.5, 0.5, 0.1, 0.05) else "-"))
    print("D.2 paired-difference TOST (alpha=0.05 per one-sided test, power 0.80), closed form vs exact")
    print("    psi  delta1 margin | closed n | exact power at closed n | smallest n (scan step 1) with exact power>=0.80")
    for psi, d1, m in ((0.10, 0.0, 0.10), (0.20, 0.0, 0.10), (0.10, 0.02, 0.10), (0.20, 0.0, 0.05), (0.30, 0.0, 0.10)):
        p10, p01 = (psi + d1) / 2, (psi - d1) / 2
        nc = tost_paired_n(psi, d1, m)
        ncc = math.ceil(nc)
        pw = tost_paired_exact_power(ncc, p10, p01, m)
        # scan near closed form
        found = None
        lo = max(10, int(nc * 0.75))
        hi = int(nc * 1.4) + 10
        if hi > 700:
            found = "not scanned (n>700)"
        else:
            for n in range(lo, hi + 1):
                if tost_paired_exact_power(n, p10, p01, m) >= 0.8:
                    found = n
                    break
        print("    %.2f  %.2f   %.2f   | %7.1f  | %.4f (n=%d) | %s" % (psi, d1, m, nc, pw, ncc, found))
    print("D.3 same design analysed as if unpaired (TOSTER closed form, pA=pB=0.80, margin 0.10):")
    nu = toster_closed_n(0.8, 0.8, 0.1, 0.05, 0.8)
    print("    per-group N=%.1f -> %d instances total; paired psi=0.10 -> n=%.1f instances" % (nu, 2 * math.ceil(nu), tost_paired_n(0.10, 0, 0.10)))
    print("D.4 exact size of paired Wald TOST at the margin (delta=margin), psi=0.20, margin=0.10:")
    for n in (100, 200, 300):
        print("    n=%d  P(conclude equivalence | delta=+margin) = %.4f" % (n, tost_paired_exact_power(n, 0.15, 0.05, 0.10)))


# ---------------------------------------------------------------- E
def section_e():
    print("== E. Stratified allocation for a weighted pass rate (no finite-population correction)")
    W = [0.40, 0.30, 0.20, 0.10]
    P = [0.95, 0.80, 0.50, 0.20]
    S = [math.sqrt(p * (1 - p)) for p in P]
    n = 400
    def var(alloc):
        return sum(w * w * s * s / a for w, s, a in zip(W, S, alloc))
    prop = [n * w for w in W]
    ney_den = sum(w * s for w, s in zip(W, S))
    ney = [n * w * s / ney_den for w, s in zip(W, S)]
    eq = [n / len(W)] * len(W)
    pst = sum(w * p for w, p in zip(W, P))
    srs = pst * (1 - pst) / n
    print("   W=%s p=%s S=%s" % (W, P, ["%.4f" % s for s in S]))
    for name, al in (("proportional", prop), ("Neyman", ney), ("equal", eq)):
        v = var(al)
        print("   %-12s n_h=%s  Var=%.3e  SE=%.4f  half-width95=%.4f" % (name, ["%.1f" % a for a in al], v, math.sqrt(v), z(0.975) * math.sqrt(v)))
    print("   unstratified SRS (same n): Var=%.3e SE=%.4f  (overall p=%.3f)" % (srs, math.sqrt(srs), pst))
    v_ney_formula = ney_den ** 2 / n
    print("   check: Neyman Var = (sum W_h S_h)^2 / n = %.3e" % v_ney_formula)
    print("   per-stratum floors for half-width h=0.10 (Wilson, at p_h):")
    floors = []
    for p in P:
        nw = next(m for m in range(5, 5000) if (lambda lu: (lu[1] - lu[0]) / 2 <= 0.10)(wilson(round(p * m), m)))
        floors.append(nw)
    print("   floors=%s sum=%d ; Neyman n_h at n=400 = %s" % (floors, sum(floors), [round(a) for a in ney]))


def section_f():
    print("== F. Per-stratum planning table (closed forms; k strata, Bonferroni alpha/k for per-stratum tests)")
    print("   k  per-stratum alpha | precision n (Wilson h=0.10 @p=0.5; h=0.05 @p=0.5) | McNemar Connor n80 (d=0.10,psi=0.20; d=0.20,psi=0.30) | paired TOST n80 (psi=0.10, margin 0.10)")
    for k in (1, 2, 4, 8):
        a = 0.05 / k
        zc = z(1 - a / 2)
        # Wilson at p=0.5 with z for the per-stratum confidence level
        def wil(h):
            for n in range(5, 20000):
                x = round(0.5 * n)
                ph = x / n
                den = 1 + zc * zc / n
                hw = zc * math.sqrt(ph * (1 - ph) / n + zc * zc / (4 * n * n)) / den
                if hw <= h:
                    return n
        c1 = connor_n(0.15, 0.05, a, 0.8)
        c2 = connor_n(0.25, 0.05, a, 0.8)
        t1 = tost_paired_n(0.10, 0.0, 0.10, a, 0.8)
        print("   %d  %.4f            | %4d ; %4d                                       | %6.1f ; %6.1f                                     | %6.1f" % (
            k, a, wil(0.10), wil(0.05), c1, c2, t1))


if __name__ == "__main__":
    which = sys.argv[1:] or ["A", "B", "C", "D", "E", "F"]
    for s in which:
        {"A": section_a, "B": section_b, "C": section_c, "D": section_d, "E": section_e, "F": section_f}[s]()
