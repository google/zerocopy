#!/usr/bin/env python3
"""Toy re-implementations of frequentist and Bayesian disproportionality statistics, applied to
(a) the simulated data set shipped with cran/PhViD@bbb450c3... (data/PhViDdata.frame.rda) and
(b) the CAERS/HFCS subset shipped with cran/openEBGM@d731cb3e... (data/caers.rda).

Basis: execution (toy re-implementation of PRR/ROR/BCPNN/shrinkage-IC formulas, not PhViD or openEBGM).

Formulas (2x2 table per drug-event pair; a = n11, b = n1. - n11, c = n.1 - n11, d = N - a - b - c):
  PRR = [a/(a+b)] / [c/(c+d)],  var(log PRR) = 1/a - 1/(a+b) + 1/c - 1/(c+d)        (PhViD R/PRR.R:62-63)
  ROR = ad/(bc),                var(log ROR) = 1/a + 1/b + 1/c + 1/d                 (PhViD R/ROR.R:61-62)
  chi-square: Pearson 2x2 statistic, with and without Yates continuity correction
  Evans et al. (2001) minimum signal criteria: a >= 3, PRR >= 2, chi-square >= 4
  BCPNN IC (exact Beta-posterior moments, PhViD R/BCPNN.R:38-48):
      E[IC], V[IC] from digamma/trigamma; IC025 = qnorm(0.025, E[IC], sqrt(V[IC])) in log2 units
  Shrinkage IC (Noren et al. 2013, eqs. 11-12): IC = log2((O + 0.5)/(E + 0.5)),
      IC025 = log2 of the 2.5th percentile of Gamma(shape O + 0.5, rate E + 0.5)

Usage: python3 probe_disproportionality.py PhViDdata.frame.rda caers.rda
"""
import math
import sys
from collections import defaultdict

import numpy as np

from rda_reader import as_columns, read_rda
from smath import digamma, pgamma, trigamma


def gamma_quantile(p, shape, rate, iters=80):
    lo = np.zeros_like(shape)
    hi = np.maximum(10.0 * (shape + 10) / rate, 1.0)
    for _ in range(iters):
        mid = 0.5 * (lo + hi)
        f = pgamma(mid, shape, rate)
        lo = np.where(f < p, mid, lo)
        hi = np.where(f < p, hi, mid)
    return 0.5 * (lo + hi)


def stats(a, n1, n_1, N):
    b, c = n1 - a, n_1 - a
    d = N - a - b - c
    with np.errstate(divide="ignore", invalid="ignore"):  # cells with b, c or d = 0 give inf/NaN; NaN compares False
        prr = (a / (a + b)) / (c / (c + d))
        se_lprr = np.sqrt(1 / a - 1 / (a + b) + 1 / c - 1 / (c + d))
        ror = (a * d) / (b * c)
        se_lror = np.sqrt(1 / a + 1 / b + 1 / c + 1 / d)
        e1 = (a + b) * (a + c) / N
        chi = N * (a * d - b * c) ** 2 / ((a + b) * (c + d) * (a + c) * (b + d))
        chiy = N * np.maximum(np.abs(a * d - b * c) - N / 2, 0) ** 2 / ((a + b) * (c + d) * (a + c) * (b + d))
    E = n1 * n_1 / N
    # BCPNN, PhViD exact branch
    p1, p2 = 1 + n1, 1 + N - n1
    q1, q2 = 1 + n_1, 1 + N - n_1
    r1 = 1 + a
    r2b = N - a - 1 + (2 + N) ** 2 / (q1 * p1)
    eic = (digamma(r1) - digamma(r1 + r2b) - (digamma(p1) - digamma(p1 + p2) + digamma(q1) - digamma(q1 + q2))) / math.log(2)
    vic = (trigamma(r1) - trigamma(r1 + r2b) + (trigamma(p1) - trigamma(p1 + p2) + trigamma(q1) - trigamma(q1 + q2))) / math.log(2) ** 2
    ic025_bcpnn = eic - 1.959964 * np.sqrt(vic)
    ic_shr = np.log2((a + 0.5) / (E + 0.5))
    ic025_shr = np.log2(gamma_quantile(0.025, a + 0.5, E + 0.5))
    with np.errstate(divide="ignore", invalid="ignore"):
        lprr_lb, lror_lb = np.log(prr) - 1.959964 * se_lprr, np.log(ror) - 1.959964 * se_lror
    return dict(prr=prr, lprr_lb=lprr_lb, ror=ror, lror_lb=lror_lb,
                chi=chi, chiy=chiy, E=E, eic=eic, ic025_bcpnn=ic025_bcpnn, ic_shr=ic_shr, ic025_shr=ic025_shr)
    return dict(prr=prr, lprr_lb=np.log(prr) - 1.959964 * se_lprr, ror=ror, lror_lb=np.log(ror) - 1.959964 * se_lror,
                chi=chi, chiy=chiy, E=E, eic=eic, ic025_bcpnn=ic025_bcpnn, ic_shr=ic_shr, ic025_shr=ic025_shr)


def phvid_part(path):
    c = as_columns(read_rda(path)["PhViDdata.frame"])
    drugs, aes, n11 = c["Drug lab"], c["AE lab"], np.array(c["n11"], float)
    m1, m2 = defaultdict(float), defaultdict(float)
    for d, e, n in zip(drugs, aes, n11):
        m1[d] += n
        m2[e] += n
    N = float(n11.sum())
    n1 = np.array([m1[d] for d in drugs])
    n_1 = np.array([m2[e] for e in aes])
    print(f"PhViDdata.frame: cells={len(n11)} drugs={len(m1)} events={len(m2)} N(sum of n11)={N:.0f}"
          f" cells with n11=1: {int(np.sum(n11 == 1))} ({np.mean(n11 == 1):.1%})")
    s = stats(n11, n1, n_1, N)
    rules = {
        "Evans: n>=3 & PRR>=2 & chi2(uncorrected)>=4": (n11 >= 3) & (s["prr"] >= 2) & (s["chi"] >= 4),
        "Evans: n>=3 & PRR>=2 & chi2(Yates)>=4": (n11 >= 3) & (s["prr"] >= 2) & (s["chiy"] >= 4),
        "PRR lower 95% bound > 1": s["lprr_lb"] > 0,
        "ROR lower 95% bound > 1": s["lror_lb"] > 0,
        "ROR lower 95% bound > 1 & n>=3": (s["lror_lb"] > 0) & (n11 >= 3),
        "BCPNN IC025 > 0 (PhViD exact, normal approx.)": s["ic025_bcpnn"] > 0,
        "shrinkage IC025 > 0 (Gamma(O+.5,E+.5))": s["ic025_shr"] > 0,
    }
    for k, v in rules.items():
        print(f"   {k:48s} signals={int(v.sum()):6d}  of which n11<=2: {int(np.sum(v & (n11 <= 2)))}")
    keys = list(rules)
    print("   Jaccard overlap between signal sets:")
    for i in range(len(keys)):
        for j in range(i + 1, len(keys)):
            A, B = rules[keys[i]], rules[keys[j]]
            u = np.sum(A | B)
            if keys[i].startswith("Evans: n>=3 & PRR>=2 & chi2(uncorrected)") or keys[j].startswith("shrinkage"):
                print(f"     {keys[i][:30]:30s} vs {keys[j][:30]:30s}: {np.sum(A & B) / u:.3f}")
    d = s["ic025_bcpnn"] - s["ic025_shr"]
    big = n11 >= 5
    print(f"   BCPNN IC025 minus shrinkage IC025: median {np.median(d):+.3f}, 5-95% [{np.percentile(d, 5):+.3f}, {np.percentile(d, 95):+.3f}];"
          f" for n11>=5 median {np.median(d[big]):+.3f}")
    e = s["eic"] - s["ic_shr"]
    print(f"   BCPNN E[IC] minus shrinkage IC (alpha=0.5): median {np.median(e):+.3f}, max |diff| {np.max(np.abs(e)):.3f}")
    e1 = s["eic"] - np.log2((n11 + 1.0) / (s["E"] + 1.0))
    print(f"   BCPNN E[IC] minus log2((O+1)/(E+1)) (alpha=1): median {np.median(e1):+.4f}, max |diff| {np.max(np.abs(e1)):.4f}")


def caers_part(path):
    c = as_columns(read_rda(path)["caers"])
    ids, v1, v2 = c["id"], c["var1"], c["var2"]
    pair, m1u, m2u = defaultdict(set), defaultdict(set), defaultdict(set)
    for i, a, b in zip(ids, v1, v2):
        pair[(a, b)].add(i); m1u[a].add(i); m2u[b].add(i)
    keys = list(pair)
    n = np.array([len(pair[k]) for k in keys], float)
    Nu = len(set(ids))
    Eu = np.array([len(m1u[a]) * len(m2u[b]) / Nu for a, b in keys])
    # PhViD/as.PhViD-style margins: sums of pair counts
    m1s, m2s = defaultdict(float), defaultdict(float)
    for (a, b), k in zip(keys, n):
        m1s[a] += k; m2s[b] += k
    Ns = n.sum()
    Es = np.array([m1s[a] * m2s[b] / Ns for a, b in keys])
    r = Es / Eu
    print(f"CAERS: pairs={len(keys)} unique reports={Nu} sum of pair counts={Ns:.0f}")
    print(f"   E(pair-count margins)/E(unique-report margins): median {np.median(r):.3f}, 5-95% [{np.percentile(r, 5):.3f}, {np.percentile(r, 95):.3f}], max {r.max():.3f}")


if __name__ == "__main__":
    phvid_part(sys.argv[1])
    caers_part(sys.argv[2])
