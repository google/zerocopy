#!/usr/bin/env python3
"""Toy re-implementation of the openEBGM 0.11.0 pipeline, run on the package's
own bundled data (data/caers.rda at cran/openEBGM@d731cb3e...).

Basis: execution (toy re-implementation of openEBGM, not openEBGM itself).

What it does, mirroring the R source at the pinned revision:
  processRaw()  R/f_transformInput.R:86-158  (unstratified and stratified E, RR, PRR)
  squashData()  R/f_dataSquashing.R:73-123
  negLLsquash() R/f_likelihoodEqs.R:375-422  (per-component truncation at N_star)
  .reinInTheta  R/f_helpers.R:18-42           (clamp applied by Qn/ebgm/quantBisect/ebScores)
  Qn()/ebgm()/quantBisect()  R/f_posteriorCalcs.R:57-255

and compares against numbers printed in the pinned vignettes
(inst/doc/vignette03-hyperparameterEstimation.html, vignette04-posteriorCalculation.html).

Usage: python3 probe_openebgm.py /path/to/caers.rda
Input: https://raw.githubusercontent.com/cran/openEBGM/d731cb3ee8d5fe6013666e05b9e55e2494d51f25/data/caers.rda
"""
import math
import sys
import time
from collections import defaultdict

import numpy as np

from rda_reader import as_columns, read_rda
from smath import digamma, lgamma, minimize_restarts, pgamma


def process_raw(cols, stratify=False):
    ids, v1, v2 = cols["id"], cols["var1"], cols["var2"]
    pair_ids = defaultdict(set)
    v1_ids, v2_ids = defaultdict(set), defaultdict(set)
    for i, a, b in zip(ids, v1, v2):
        pair_ids[(a, b)].add(i)
        v1_ids[a].add(i)
        v2_ids[b].add(i)
    n_tot = len(set(ids))
    rows = []
    if stratify:
        st = cols["strat1"]
        s_v1, s_v2, s_tot = defaultdict(set), defaultdict(set), defaultdict(set)
        for i, a, b, s in zip(ids, v1, v2, st):
            s_v1[(a, s)].add(i)
            s_v2[(b, s)].add(i)
            s_tot[s].add(i)
        strata = sorted(s_tot)
    for (a, b), s_ids in pair_ids.items():
        n = len(s_ids)
        nv1, nv2 = len(v1_ids[a]), len(v2_ids[b])
        if stratify:
            e = 0.0
            for s in strata:
                e += (len(s_v1.get((a, s), ())) / len(s_tot[s])) * len(s_v2.get((b, s), ()))
        else:
            e = (nv1 / n_tot) * nv2
        e = max(e, 1e-10)
        num = n / nv1
        den = (nv2 - n) / (n_tot - nv1)
        prr = math.inf if den == 0 else round(math.exp(math.log(num) - math.log(den)), 2)
        rows.append((a, b, n, e, round(n / e, 2), prr))
    return rows, n_tot


def squash(N, E, W, count=1, bin_size=50, keep_pts=100):
    N, E, W = np.asarray(N), np.asarray(E), np.asarray(W)
    hold = N != count
    idx = np.where(~hold)[0]
    idx = idx[np.argsort(E[idx], kind="stable")]
    num_squash = len(idx) - keep_pts
    if num_squash < bin_size:
        raise ValueError("reduce 'bin_size' or 'keep_pts'")
    sq, keep = idx[:num_squash], idx[num_squash:]
    newN, newE, newW = list(N[hold]), list(E[hold]), list(W[hold])
    for start in range(0, num_squash, bin_size):
        b = sq[start:start + bin_size]
        newN.append(count)
        newE.append(float(np.mean(E[b])))
        newW.append(len(b))
    if keep_pts:
        newN += list(N[keep]); newE += list(E[keep]); newW += list(W[keep])
    order = np.argsort(np.asarray(newN), kind="stable")
    return np.asarray(newN)[order], np.asarray(newE)[order], np.asarray(newW)[order]


def log_nb(n, size, prob):
    return lgamma(n + size) - lgamma(n + 1.0) - lgamma(size) + size * np.log(prob) + n * np.log1p(-prob)


def comp_logf(ab, n, e, n_star, mixture_level=False):
    p = np.clip(ab[1] / (ab[1] + e), 1e-10, 1 - 1e-10)
    lf = log_nb(n, ab[0], p)
    # pnbinom(N_star - 1, lower.tail = FALSE): for N_star = 1 this is 1 - p^alpha
    if n_star != 1:
        raise NotImplementedError("probe implements N_star = 1 only")
    log_surv = np.log(-np.expm1(ab[0] * np.log(p)))
    return lf, log_surv


def neg_ll_squash(theta, n, e, w, n_star=1, mixture_level=False):
    a1, b1, a2, b2, P = theta
    lf1, ls1 = comp_logf((a1, b1), n, e, n_star)
    lf2, ls2 = comp_logf((a2, b2), n, e, n_star)
    if not mixture_level:
        # openEBGM R/f_likelihoodEqs.R:398-422: P*f1/S1 + (1-P)*f2/S2
        ll = np.logaddexp(math.log(P) + lf1 - ls1, math.log(1 - P) + lf2 - ls2)
    else:
        # conditional marginal of the mixture: (P f1 + (1-P) f2) / (P S1 + (1-P) S2)
        ll = (np.logaddexp(math.log(P) + lf1, math.log(1 - P) + lf2)
              - np.logaddexp(math.log(P) + ls1, math.log(1 - P) + ls2))
    return float(-np.sum(w * ll))


def fit(n, e, w, start, mixture_level=False):
    def f(t):
        th = np.concatenate([np.exp(t[:4]), [1 / (1 + math.exp(-t[4]))]])
        v = neg_ll_squash(th, n, e, w, mixture_level=mixture_level)
        return v if np.isfinite(v) else 1e12
    t0 = np.concatenate([np.log(start[:4]), [math.log(start[4] / (1 - start[4]))]])
    t, v = minimize_restarts(f, t0)
    return np.concatenate([np.exp(t[:4]), [1 / (1 + math.exp(-t[4]))]]), v


def rein_in(theta, lo=(.25, .25, .25, .25, 1e-5), hi=(10, 10, 10, 10, .99999)):
    t = np.minimum(np.maximum(np.asarray(theta, float), lo), hi)
    t[0] = min(t[0], 2 * t[1]); t[2] = min(t[2], 2 * t[3])
    t[0] = max(t[0], 0.5 * t[1]); t[2] = max(t[2], 0.5 * t[3])
    return t


def qn(theta, n, e):
    p1 = np.clip(theta[1] / (theta[1] + e), 1e-10, 1 - 1e-10)
    p2 = np.clip(theta[3] / (theta[3] + e), 1e-10, 1 - 1e-10)
    l1 = math.log(theta[4]) + log_nb(n, theta[0], p1)
    l2 = math.log(1 - theta[4]) + log_nb(n, theta[2], p2)
    return np.exp(l1 - np.logaddexp(l1, l2))


def ebgm(theta, n, e, q):
    x1 = digamma(theta[0] + n) - np.log(theta[1] + e)
    x2 = digamma(theta[2] + n) - np.log(theta[3] + e)
    return np.exp(q * x1 + (1 - q) * x2)


def post_cdf(x, theta, n, e, q):
    return q * pgamma(x, theta[0] + n, theta[1] + e) + (1 - q) * pgamma(x, theta[2] + n, theta[3] + e)


def quant_bisect(pct, theta, n, e, q, digits=2, limits=(-1e5, 1e5), max_iter=2000):
    tol = 0.5 * 10 ** (-digits)
    cut = pct / 100
    g = np.ones_like(e)
    too_big = post_cdf(g, theta, n, e, q) - cut > 0
    left = np.where(too_big, limits[0], g)
    right = np.where(too_big, g, limits[1])
    for _ in range(max_iter):
        mid = 0.5 * (left + right)
        err = post_cdf(np.maximum(mid, 0), theta, n, e, q) - cut
        if np.max(0.5 * (right - left)) < tol:
            return np.round(mid, digits)
        el = post_cdf(np.maximum(left, 0), theta, n, e, q) - cut
        same = np.sign(el) == np.sign(err)
        left = np.where(same, mid, left)
        right = np.where(same, right, mid)
    raise RuntimeError("no convergence")


def main(path):
    cols = as_columns(read_rda(path)["caers"])
    print("caers rows:", len(cols["id"]), "unique ids:", len(set(cols["id"])),
          "strata:", sorted(set(cols["strat1"])))
    t0 = time.perf_counter()
    rows, n_tot = process_raw(cols)
    t_proc = time.perf_counter() - t0
    print(f"processRaw (unstratified) rows: {len(rows)}  N_tot(unique ids): {n_tot}  [{t_proc:.2f}s toy]")
    look = {("7 ZEN 7-HYDROXYMITRAGYNINE CHEWABLE TABLETS", "ACUTE PSYCHOSIS"): 0.0003602305,
            ("7 ZEN 7-HYDROXYMITRAGYNINE CHEWABLE TABLETS", "HOSPITALISATION"): 0.1253602305,
            ("7-HYDROXYMITRAGYNINE 7-OH KRATOM", "DEATH"): 0.0407060519}
    byk = {}
    for r in rows:  # vignette prints labels with surrounding blanks trimmed
        byk.setdefault((r[0].strip(), r[1].strip()), r)
    for k, ev in look.items():
        r = byk.get(k)
        print("  vignette E", ev, "-> toy", None if r is None else (r[2], f"{r[3]:.10f}", r[4], r[5]))
    srows, _ = process_raw(cols, stratify=True)
    sE = {(r[0], r[1]): r[3] for r in srows}
    ratio = np.array([sE[(r[0], r[1])] / r[3] for r in rows])
    print("stratified/unstratified E ratio: min %.3f median %.3f max %.3f" % (ratio.min(), np.median(ratio), ratio.max()))

    N = np.array([r[2] for r in rows], float)
    E = np.array([r[3] for r in rows], float)
    W = np.ones_like(N)
    sN, sE_, sW = squash(N, E, W)
    print("squashData() defaults -> rows:", len(sN), "(vignette03 prints 1202)")

    # vignette03 autoHyper on squash(count=1,bin=25,keep=10) + squash(count=2,bin=10,keep=10)
    a = squash(N, E, W, 1, 25, 10)
    a = squash(*a, count=2, bin_size=10, keep_pts=10)
    t0 = time.perf_counter()
    th_c, v_c = fit(*a, start=np.array([1, 1, 2, 2, .1]))
    t_fit = time.perf_counter() - t0
    print("toy fit, per-component truncation (openEBGM form):", np.round(th_c, 5), "negLL %.3f" % v_c,
          f"[{t_fit:.1f}s toy]")
    print("  vignette03 autoHyper(squashed):  [3.77687 0.51432 3.75500 3.66463 0.04829] negLL 2994.068")
    th_m, v_m = fit(*a, start=th_c, mixture_level=True)
    print("toy fit, mixture-level truncation (conditional marginal):", ["%.6g" % x for x in th_m], "negLL %.3f" % v_m)
    print("  mixture-level negLL evaluated at the openEBGM estimate: %.3f" % neg_ll_squash(th_c, *a, mixture_level=True))

    # vignette04 scoring with its printed theta_hat
    th = np.array([3.77699506, 0.51388202, 3.73820989, 3.64892019, 0.04817177])
    head = [("7 ZEN 7-HYDROXYMITRAGYNINE CHEWABLE TABLETS", "ACUTE PSYCHOSIS"),
            ("7 ZEN 7-HYDROXYMITRAGYNINE CHEWABLE TABLETS", "HOSPITALISATION"),
            ("7-HYDROXYMITRAGYNINE 7-OH KRATOM", "DEATH")]
    hn = np.array([byk[k][2] for k in head], float)
    he = np.array([byk[k][3] for k in head], float)
    for label, t in (("with .reinInTheta (as shipped)", rein_in(th)), ("without clamp (raw MLE)", th)):
        q = qn(t, hn, he)
        print(f"{label}: theta used = {np.round(t, 5)}")
        print("   Qn   ", np.round(q, 8))
        print("   EBGM ", np.round(ebgm(t, hn, he, q), 2))
        print("   Q05  ", quant_bisect(5, t, hn, he, q), " Q95", quant_bisect(95, t, hn, he, q))
        qa = qn(t, N, E)
        f2 = post_cdf(np.full_like(E, 1.995), t, N, E, qa)
        print("   cells with QUANT_05 >= 2 (F(1.995) <= 0.05):", int(np.sum(f2 <= 0.05)), "of", len(N))
    print("vignette04 prints: Qn 0.08983976 0.06931687 0.08191145; EBGM 1.27 1.19 1.24;"
          " Q05 0.50 0.48 0.50; Q95 3.31 2.75 3.05; 24 of 13441 with QUANT_05 >= 2")


if __name__ == "__main__":
    main(sys.argv[1])
