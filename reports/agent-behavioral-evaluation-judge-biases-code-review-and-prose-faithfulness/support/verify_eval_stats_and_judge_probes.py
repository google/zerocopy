#!/usr/bin/env python3
"""Deterministic verification probes for behavioral evaluation statistics and LLM-as-a-Judge.

Self-contained support script for the reference report package:
  reports/agent-behavioral-evaluation-judge-biases-code-review-and-prose-faithfulness/

Runtime constraints: Python 3.10+ standard library only, fixed seed 20261121,
zero network calls, bit-identical deterministic stdout, < 3s wall-clock runtime.

Epistemic labeling discipline (explicitly printed in stdout banners):
  - Probe 1 ([exact numerical / derived calculation]):
      1a(i):  Exact Binomial-PMF 95% coverage and mean width for Wald, Wilson, and
              conjugate Beta(1,1) credible intervals across N in {5,10,20,50,100,300}.
      1a(ii): Clustered Beta-Binomial 95% coverage under Bowyer et al. (2025)
              theta ~ Beta(1,1), d ~ Gamma(1,1) prior evaluated via unbounded
              transformed quadrature u = d / (1 + d) on (0, 1) with log-Jacobian
              -2*log(1 - u) (40x40 midpoint grid, verified for numerical convergence
              against a 100x100 reference grid), across ICC=0.40 and negative-control
              ICC=0.00.
      1b(i):  Analytic 80%-power MDE lookup table (Miller 2024 Eq. 10 & Wilson HW).
      1b(ii): Paired Type-M exaggeration, Type-S error, and power under a Gaussian
              copula (r=0.50, x_B ~ U[0,0.80], x_A ~ U[Delta,0.80+Delta]) plus
              Delta=0.00 negative control (1b(iii)).
      1c:     Miller (2024) §3.3 T=0 thresholding negative control and exact audit of
              p. 6 (Bernoulli(3/4) vs. printed 1/4 typo) and p. 8-9 paired variance
              (exact omega^2 = 1/12 vs. printed 1/9).
  - Probe 2 ([toy model / illustrative surrogate]):
      2a:     Pairwise judge Type-I false-promotion and power under position +
              verbosity biases across 4 debiasing protocols, iterating length-controlled
              logistic GLM Newton-Raphson to strict convergence (max|step| < 1e-10,
              up to 50 iterations, asserted). Caveat: model matches unconfounded DGP.
      2b:     [toy model / illustrative skewness mechanism] showing how right-tail
              bias spikes make median(B-A) < 0 < E[B-A], inverting maj@5 > single >
              mean@5 > best-of-5 (NOT a causal reproduction of Gu et al. Table 4,
              which confounds pairwise maj@5 vs. pointwise mean@5 and has n=34).
  - Probe 3 (split exact algebra vs. illustrative surrogate):
      3a:     [exact numerical / derived calculation] Exact Bayes PPV & Likelihood-Ratio
              Crossover Theorem (PPV strictly increasing in LR = TPR/FPR for all pi in
              (0,1); exact SWT-Bench implied FPR=4.832% and crossover bounds).
      3b:     [toy model / illustrative surrogate mapping] Pointwise plug-in comparison
              and 100,000-patch MC check mapping JudgeBench Coding accuracies as
              (TPR=acc, FPR=1-acc), explicitly qualified for pairwise 2AFC mismatch,
              swap-inconsistency=0 scoring, N=42 GPT-4o-filtered scope, and
              non-reasoning-only applicability.
"""

from __future__ import annotations

import math
import random
from typing import Dict, List, Sequence, Tuple

SEED = 20261121
Z_975 = 1.959963984540054
Z_800 = 0.8416212335729143
SQRT2 = math.sqrt(2.0)


# ---------------------------------------------------------------------------
# Pure-stdlib special functions & numerical utilities
# ---------------------------------------------------------------------------

def norm_cdf(x: float) -> float:
    return 0.5 * (1.0 + math.erf(x / SQRT2))


def norm_ppf(p: float) -> float:
    """Inverse standard normal CDF (Acklam rational approximation + 1 Newton refinement)."""
    if not (0.0 < p < 1.0):
        raise ValueError(f"p must be in (0, 1), got {p}")
    a = (
        -3.969683028665376e01,
        2.209460984245205e02,
        -2.759285104469687e02,
        1.383577518672690e02,
        -3.066479806614716e01,
        2.506628277459239e00,
    )
    b = (
        -5.447609879822406e01,
        1.615858368580409e02,
        -1.556989798598866e02,
        6.680131188771972e01,
        -1.328068155288572e01,
    )
    c = (
        -7.784894002430293e-03,
        -3.223964580411365e-01,
        -2.400758277161838e00,
        -2.549732539343734e00,
        4.374664141464968e00,
        2.938163982698783e00,
    )
    d = (
        7.784695709041462e-03,
        3.224671290700398e-01,
        2.445134137142996e00,
        3.754408661907416e00,
    )
    plow = 0.02425
    phigh = 1.0 - plow
    if p < plow:
        q = math.sqrt(-2.0 * math.log(p))
        x = (((((c[0] * q + c[1]) * q + c[2]) * q + c[3]) * q + c[4]) * q + c[5]) / (
            (((d[0] * q + d[1]) * q + d[2]) * q + d[3]) * q + 1.0
        )
    elif p <= phigh:
        q = p - 0.5
        r = q * q
        x = (((((a[0] * r + a[1]) * r + a[2]) * r + a[3]) * r + a[4]) * r + a[5]) * q / (
            (((((b[0] * r + b[1]) * r + b[2]) * r + b[3]) * r + b[4]) * r + 1.0)
        )
    else:
        q = math.sqrt(-2.0 * math.log(1.0 - p))
        x = -(((((c[0] * q + c[1]) * q + c[2]) * q + c[3]) * q + c[4]) * q + c[5]) / (
            (((d[0] * q + d[1]) * q + d[2]) * q + d[3]) * q + 1.0
        )
    err = norm_cdf(x) - p
    pdf = math.exp(-0.5 * x * x) / math.sqrt(2.0 * math.pi)
    return x - err / pdf


def _betacf(a: float, b: float, x: float) -> float:
    """Continued fraction for regularized incomplete beta I_x(a, b) (Lentz's method)."""
    max_iter = 200
    eps = 3.0e-12
    fpmin = 1.0e-30
    qab = a + b
    qap = a + 1.0
    qam = a - 1.0
    c = 1.0
    d = 1.0 - qab * x / qap
    if abs(d) < fpmin:
        d = fpmin
    d = 1.0 / d
    h = d
    for m in range(1, max_iter + 1):
        m2 = 2 * m
        aa = m * (b - m) * x / ((qam + m2) * (a + m2))
        d = 1.0 + aa * d
        if abs(d) < fpmin:
            d = fpmin
        c = 1.0 + aa / c
        if abs(c) < fpmin:
            c = fpmin
        d = 1.0 / d
        h *= d * c
        aa = -(a + m) * (qab + m) * x / ((a + m2) * (qap + m2))
        d = 1.0 + aa * d
        if abs(d) < fpmin:
            d = fpmin
        c = 1.0 + aa / c
        if abs(c) < fpmin:
            c = fpmin
        d = 1.0 / d
        delta = d * c
        h *= delta
        if abs(delta - 1.0) < eps:
            break
    return h


def betainc(a: float, b: float, x: float) -> float:
    """Regularized incomplete beta function I_x(a, b)."""
    if x <= 0.0:
        return 0.0
    if x >= 1.0:
        return 1.0
    ln_bt = (
        math.lgamma(a + b)
        - math.lgamma(a)
        - math.lgamma(b)
        + a * math.log(x)
        + b * math.log(1.0 - x)
    )
    bt = math.exp(ln_bt)
    if x < (a + 1.0) / (a + b + 2.0):
        return bt * _betacf(a, b, x) / a
    return 1.0 - bt * _betacf(b, a, 1.0 - x) / b


def beta_quantile(a: float, b: float, q: float) -> float:
    """Exact Beta(a, b) quantile via bisection on I_x(a, b)."""
    if q <= 0.0:
        return 0.0
    if q >= 1.0:
        return 1.0
    if a == 1.0:
        return 1.0 - (1.0 - q) ** (1.0 / b)
    if b == 1.0:
        return q ** (1.0 / a)
    lo, hi = 0.0, 1.0
    for _ in range(40):
        mid = 0.5 * (lo + hi)
        if betainc(a, b, mid) < q:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def student_t_crit_975(df: int) -> float:
    """Exact two-sided alpha=0.05 Student-t critical value t_{0.975, df} via Beta quantile."""
    x = beta_quantile(0.5 * df, 0.5, 0.05)
    return math.sqrt(df * (1.0 - x) / x)


def wilson_ci_p(p: float, n: int, z: float = Z_975) -> Tuple[float, float]:
    z2 = z * z
    denom = 1.0 + z2 / n
    center = (p + z2 / (2.0 * n)) / denom
    half = (z / denom) * math.sqrt((p * (1.0 - p)) / n + z2 / (4.0 * n * n))
    return (max(0.0, center - half), min(1.0, center + half))


def wald_ci(s: int, n: int, z: float = Z_975) -> Tuple[float, float]:
    p = s / n
    se = math.sqrt(p * (1.0 - p) / n)
    return (p - z * se, p + z * se)


def build_binomial_pmf(n: int, p: float) -> List[float]:
    """Exact discrete Binomial(n, p) PMF."""
    q = 1.0 - p
    log_p = math.log(p)
    log_q = math.log(q)
    lg_n1 = math.lgamma(n + 1)
    return [
        math.exp(lg_n1 - math.lgamma(k + 1) - math.lgamma(n - k + 1) + k * log_p + (n - k) * log_q)
        for k in range(n + 1)
    ]


def build_binomial_cdf(n: int, p: float) -> List[float]:
    """Exact discrete Binomial(n, p) CDF."""
    pmf = build_binomial_pmf(n, p)
    cdf: List[float] = []
    acc = 0.0
    for pr in pmf:
        acc += pr
        cdf.append(acc)
    cdf[-1] = 1.0
    return cdf


def sample_from_cdf(rng: random.Random, cdf: Sequence[float]) -> int:
    u = rng.random()
    lo, hi = 0, len(cdf) - 1
    while lo < hi:
        mid = (lo + hi) >> 1
        if cdf[mid] < u:
            lo = mid + 1
        else:
            hi = mid
    return lo


def solve_spd_3x3(
    a00: float,
    a01: float,
    a02: float,
    a11: float,
    a12: float,
    a22: float,
    b0: float,
    b1: float,
    b2: float,
) -> Tuple[float, float, float]:
    """Exact Cholesky solve for symmetric positive-definite 3x3 system A x = b."""
    l00 = math.sqrt(a00)
    l10 = a01 / l00
    l20 = a02 / l00
    l11 = math.sqrt(a11 - l10 * l10)
    l21 = (a12 - l20 * l10) / l11
    l22 = math.sqrt(a22 - l20 * l20 - l21 * l21)
    y0 = b0 / l00
    y1 = (b1 - l10 * y0) / l11
    y2 = (b2 - l20 * y0 - l21 * y1) / l22
    x2 = y2 / l22
    x1 = (y1 - l21 * x2) / l11
    x0 = (y0 - l10 * x1 - l20 * x2) / l00
    return (x0, x1, x2)


# ---------------------------------------------------------------------------
# Unbounded Transformed Quadrature for Bowyer (2025) Clustered Beta-Binomial
# ---------------------------------------------------------------------------

class ClusteredBayesQuadrature:
    """Exact 2D midpoint quadrature for theta ~ Beta(1,1), d ~ Gamma(1,1) = Exp(1).

    Uses the unbounded transformation u = d / (1 + d) in (0, 1), d = u / (1 - u),
    with exact log prior density + log Jacobian:
        log p(u) = -d(u) - 2 * log(1 - u).
    Notice 1 - u = 1 / (1 + d) = ICC, so u spans the entire positive real line
    d in (0, infinity) without upper-tail truncation.
    """

    def __init__(self, n_th: int, n_u: int, build_small: bool = True) -> None:
        self.n_th = n_th
        self.n_u = n_u
        self.bw = 1.0 / n_th
        self.thetas = [(i + 0.5) / n_th for i in range(n_th)]
        self.us = [(j + 0.5) / n_u for j in range(n_u)]
        self.ds = [u / (1.0 - u) for u in self.us]
        self.log_prior_u = [-d - 2.0 * math.log(1.0 - u) for u, d in zip(self.us, self.ds)]
        self.t5 = self._build_table(5)
        self.t3 = self._build_table(3) if build_small else []
        self.t2 = self._build_table(2) if build_small else []

    def _build_table(self, m: int) -> List[Tuple[Tuple[float, ...], ...]]:
        tbl: List[Tuple[Tuple[float, ...], ...]] = []
        for th in self.thetas:
            row = []
            for d, lp_u in zip(self.ds, self.log_prior_u):
                a = d * th
                b = d * (1.0 - th)
                lg_ab = math.lgamma(a + b) - math.lgamma(a) - math.lgamma(b) - math.lgamma(m + a + b)
                row.append(
                    (lp_u,)
                    + tuple(lg_ab + math.lgamma(k + a) + math.lgamma(m - k + b) for k in range(m + 1))
                )
            tbl.append(tuple(row))
        return tbl

    def _quantiles_from_flat_logw(self, lws: List[float]) -> Tuple[float, float]:
        mx = max(lws)
        cut = mx - 40.0
        exp_fn = math.exp
        n_th = self.n_th
        n_u = self.n_u
        th_w = [0.0] * n_th
        tot = 0.0
        idx = 0
        for i in range(n_th):
            s = 0.0
            for _ in range(n_u):
                v = lws[idx]
                idx += 1
                if v > cut:
                    s += exp_fn(v - mx)
            th_w[i] = s
            tot += s
        inv_tot = 1.0 / tot
        lo_q = hi_q = 0.5
        cum = 0.0
        got_lo = False
        bw = self.bw
        for i, w in enumerate(th_w):
            wi = w * inv_tot
            nxt = cum + wi
            if not got_lo and nxt >= 0.025:
                lo_q = (i + ((0.025 - cum) / wi if wi > 0.0 else 0.5)) * bw
                got_lo = True
            if nxt >= 0.975:
                hi_q = (i + ((0.975 - cum) / wi if wi > 0.0 else 0.5)) * bw
                break
            cum = nxt
        return (lo_q, hi_q)

    def ci_m5(
        self,
        hist: Tuple[int, int, int, int, int, int],
        cache: Dict[Tuple[int, ...], Tuple[float, float]],
    ) -> Tuple[float, float]:
        cached = cache.get(hist)
        if cached is not None:
            return cached
        # Exploit exact Beta(1,1) / Beta-Binomial reflection symmetry:
        # CI(h5, h4, h3, h2, h1, h0) = (1 - hi, 1 - lo).
        rev = (hist[5], hist[4], hist[3], hist[2], hist[1], hist[0])
        cached_rev = cache.get(rev)
        if cached_rev is not None:
            res = (1.0 - cached_rev[1], 1.0 - cached_rev[0])
            cache[hist] = res
            return res
        c0, c1, c2, c3, c4, c5 = hist
        lws = [
            lp + c0 * r0 + c1 * r1 + c2 * r2 + c3 * r3 + c4 * r4 + c5 * r5
            for row in self.t5
            for lp, r0, r1, r2, r3, r4, r5 in row
        ]
        res = self._quantiles_from_flat_logw(lws)
        cache[hist] = res
        return res

    def posterior_mean_d_m5(self, hist: Tuple[int, int, int, int, int, int]) -> float:
        c0, c1, c2, c3, c4, c5 = hist
        lws = [
            lp + c0 * r0 + c1 * r1 + c2 * r2 + c3 * r3 + c4 * r4 + c5 * r5
            for row in self.t5
            for lp, r0, r1, r2, r3, r4, r5 in row
        ]
        mx = max(lws)
        cut = mx - 40.0
        exp_fn = math.exp
        num = 0.0
        den = 0.0
        n_u = self.n_u
        ds = self.ds
        for idx, v in enumerate(lws):
            if v > cut:
                w = exp_fn(v - mx)
                den += w
                num += w * ds[idx % n_u]
        return num / den

    def ci_3_2(
        self,
        k0: int,
        k1: int,
        cache: Dict[Tuple[int, int], Tuple[float, float]],
    ) -> Tuple[float, float]:
        key = (k0, k1)
        cached = cache.get(key)
        if cached is not None:
            return cached
        lws = [
            self.t3[i][j][0] + self.t3[i][j][k0 + 1] + self.t2[i][j][k1 + 1]
            for i in range(self.n_th)
            for j in range(self.n_u)
        ]
        res = self._quantiles_from_flat_logw(lws)
        cache[key] = res
        return res


# ---------------------------------------------------------------------------
# Probe 1: Finite-Sample Coverage, Type-M Exaggeration, Power & Miller Audits
# ---------------------------------------------------------------------------

def run_probe_1(rng: random.Random) -> None:
    print("=" * 94)
    print("PROBE 1 [exact numerical / derived calculation]: FINITE-SAMPLE COVERAGE, POWER & MILLER AUDITS")
    print("=" * 94)

    # Sanity-check pure-stdlib special functions against exact analytical identities
    assert abs(beta_quantile(1.0, 10.0, 0.95) - (1.0 - 0.05 ** 0.1)) < 1e-12
    assert abs(beta_quantile(5.0, 5.0, 0.50) - 0.50) < 1e-12
    assert abs(norm_ppf(0.975) - Z_975) < 1e-12
    assert abs(norm_ppf(0.80) - Z_800) < 1e-12
    assert abs(student_t_crit_975(9) - 2.2621571627409915) < 1e-8

    ns = [5, 10, 20, 50, 100, 300]
    ps = [0.05, 0.15, 0.50]

    # 1a(i). Exact IID Bernoulli 95% coverage and expected width via exact Binomial PMF
    # Precompute exact intervals once per N (exploiting Beta(1+s, 1+n-s) reflection symmetry).
    ci_tables: Dict[int, Tuple[List[Tuple[float, float]], List[Tuple[float, float]], List[Tuple[float, float]]]] = {}
    for n in ns:
        wald_t = [wald_ci(s, n) for s in range(n + 1)]
        wils_t = [wilson_ci_p(s / n, n) for s in range(n + 1)]
        bays_t: List[Tuple[float, float]] = [(0.0, 0.0)] * (n + 1)
        half = n // 2
        for s in range(half + 1):
            lo = beta_quantile(1.0 + s, 1.0 + n - s, 0.025)
            hi = beta_quantile(1.0 + s, 1.0 + n - s, 0.975)
            bays_t[s] = (lo, hi)
            bays_t[n - s] = (1.0 - hi, 1.0 - lo)
        ci_tables[n] = (wald_t, wils_t, bays_t)

    print("\n--- 1a(i) [exact numerical / derived calculation]: Exact IID Bernoulli 95% Coverage & Width ---")
    print(f"{'N':>4} {'p':>5} | {'Wald Cov':>9} {'Wils Cov':>9} {'Bayes Cov':>10} | {'Wald Wid':>9} {'Wils Wid':>9} {'Bayes Wid':>10}")
    print("-" * 80)
    iid_cov_summary: Dict[Tuple[int, float], Tuple[float, float, float]] = {}
    for p in ps:
        for n in ns:
            pmf = build_binomial_pmf(n, p)
            wald_t, wils_t, bays_t = ci_tables[n]
            cw = ci_w = cb = 0.0
            ww = wi_w = wb = 0.0
            for s, pr in enumerate(pmf):
                lo, hi = wald_t[s]
                if lo <= p <= hi:
                    cw += pr
                ww += pr * (hi - lo)
                lo, hi = wils_t[s]
                if lo <= p <= hi:
                    ci_w += pr
                wi_w += pr * (hi - lo)
                lo, hi = bays_t[s]
                if lo <= p <= hi:
                    cb += pr
                wb += pr * (hi - lo)
            iid_cov_summary[(n, p)] = (cw, ci_w, cb)
            print(
                f"{n:4d} {p:5.2f} | {100*cw:8.2f}% {100*ci_w:8.2f}% {100*cb:9.2f}% | "
                f"{ww:9.4f} {wi_w:9.4f} {wb:10.4f}"
            )
    assert iid_cov_summary[(20, 0.05)][0] < 0.65, "Expected exact Wald collapse (<65%) at N=20, p=0.05"
    assert iid_cov_summary[(20, 0.05)][1] > 0.90, "Expected exact Wilson recovery at N=20, p=0.05"
    assert iid_cov_summary[(20, 0.05)][2] > 0.90, "Expected exact Beta-Bayes recovery at N=20, p=0.05"

    # 1a(ii). Clustered Tasks Coverage via Unbounded Transformed Quadrature u = d / (1 + d)
    quad = ClusteredBayesQuadrature(n_th=40, n_u=40, build_small=True)
    quad_ref = ClusteredBayesQuadrature(n_th=100, n_u=100, build_small=False)

    # Verify numerical convergence of 40x40 unbounded quadrature against 100x100 finer grid
    conv_cases = [
        ("N=300 ICC=0 sym", (2, 9, 19, 19, 9, 2)),
        ("N=300 ICC=0.4 sym", (12, 9, 9, 9, 9, 12)),
        ("N=300 skewed", (0, 2, 10, 20, 20, 8)),
        ("N=20 ICC=0", (0, 1, 1, 1, 1, 0)),
    ]
    max_ep_err = 0.0
    max_ed_err = 0.0
    for _cname, chist in conv_cases:
        lo_q, hi_q = quad.ci_m5(chist, {})
        lo_r, hi_r = quad_ref.ci_m5(chist, {})
        max_ep_err = max(max_ep_err, abs(lo_q - lo_r), abs(hi_q - hi_r))
        ed_q = quad.posterior_mean_d_m5(chist)
        ed_r = quad_ref.posterior_mean_d_m5(chist)
        max_ed_err = max(max_ed_err, abs(ed_q - ed_r))
    assert max_ep_err < 0.0025, f"Quadrature endpoint error too large: {max_ep_err}"
    assert max_ed_err < 0.01, f"Quadrature E[d|data] error too large: {max_ed_err}"
    print(
        f"\n--- 1a(ii) Quadrature Convergence Check (u = d/(1+d) in (0,1), d_max={quad.ds[-1]:.1f}): "
        f"40x40 vs 100x100 max|delta_CI|={max_ep_err:.5f}, max|delta_E[d]|={max_ed_err:.5f} [PASS] ---"
    )

    def build_betabinom_cdf(m: int, theta: float, rho: float) -> List[float]:
        if rho <= 0.0:
            return build_binomial_cdf(m, theta)
        d = (1.0 - rho) / rho
        a = d * theta
        b = d * (1.0 - theta)
        lg_base = math.lgamma(m + 1) + math.lgamma(a + b) - math.lgamma(a) - math.lgamma(b) - math.lgamma(m + a + b)
        cdf: List[float] = []
        acc = 0.0
        for k in range(m + 1):
            lp = lg_base - math.lgamma(k + 1) - math.lgamma(m - k + 1) + math.lgamma(k + a) + math.lgamma(m - k + b)
            acc += math.exp(lp)
            cdf.append(acc)
        cdf[-1] = 1.0
        return cdf

    n_clust_trials = 500

    def eval_clustered_regime(
        rho: float, n_list: Sequence[int], label: str
    ) -> Tuple[Dict[int, Tuple[float, float, float, float, float]], float]:
        theta_true = 0.50
        print(
            f"\n--- 1a(ii) [exact numerical / derived calculation]: Clustered 95% Coverage [{label}] "
            f"(theta={theta_true:.2f}, ICC={rho:.2f}, 40x40 unbounded u-quad, {n_clust_trials} trials) ---"
        )
        print(
            f"{'N':>4} {'Clusters':>9} | {'Naive CLT':>9} {'Clust CLT':>9} {'Hier Bayes':>10} | "
            f"{'Naive Wid':>9} {'Clust Wid':>9} {'Bayes Wid':>9} {'vs Naive':>9}"
        )
        print("-" * 96)
        out: Dict[int, Tuple[float, float, float, float, float]] = {}
        cdf5 = build_betabinom_cdf(5, theta_true, rho)
        cdf3 = build_betabinom_cdf(3, theta_true, rho)
        cdf2 = build_betabinom_cdf(2, theta_true, rho)
        mean_ed_300 = 0.0
        for n in n_list:
            equal_m = (n != 5)
            c_desc = "2 (3,2)" if not equal_m else f"{n // 5}x5"
            t_cnt = n // 5
            cache_eq: Dict[Tuple[int, ...], Tuple[float, float]] = {}
            cache_32: Dict[Tuple[int, int], Tuple[float, float]] = {}
            cn = cc = cb = 0
            wn = wc = wb = 0.0
            ed_sum = 0.0
            ed_cnt = 0
            for trial_idx in range(n_clust_trials):
                if equal_m:
                    h0 = h1 = h2 = h3 = h4 = h5 = 0
                    tot_s = 0
                    for _t in range(t_cnt):
                        k = sample_from_cdf(rng, cdf5)
                        tot_s += k
                        if k == 0:
                            h0 += 1
                        elif k == 1:
                            h1 += 1
                        elif k == 2:
                            h2 += 1
                        elif k == 3:
                            h3 += 1
                        elif k == 4:
                            h4 += 1
                        else:
                            h5 += 1
                    hist = (h0, h1, h2, h3, h4, h5)
                    xbar = tot_s / n
                    m_x = 5.0 * xbar
                    ss_c = (
                        h0 * m_x * m_x
                        + h1 * (1.0 - m_x) ** 2
                        + h2 * (2.0 - m_x) ** 2
                        + h3 * (3.0 - m_x) ** 2
                        + h4 * (4.0 - m_x) ** 2
                        + h5 * (5.0 - m_x) ** 2
                    )
                    lo_b, hi_b = quad.ci_m5(hist, cache_eq)
                    if n == 300 and rho == 0.0 and trial_idx < 60:
                        ed_sum += quad.posterior_mean_d_m5(hist)
                        ed_cnt += 1
                else:
                    k0 = sample_from_cdf(rng, cdf3)
                    k1 = sample_from_cdf(rng, cdf2)
                    xbar = (k0 + k1) / 5.0
                    ss_c = (k0 - 3.0 * xbar) ** 2 + (k1 - 2.0 * xbar) ** 2
                    lo_b, hi_b = quad.ci_3_2(k0, k1, cache_32)
                se_n = math.sqrt(xbar * (1.0 - xbar) / n)
                lo_n, hi_n = xbar - Z_975 * se_n, xbar + Z_975 * se_n
                if lo_n <= theta_true <= hi_n:
                    cn += 1
                wn += hi_n - lo_n
                se_c = math.sqrt(ss_c) / n
                lo_c, hi_c = xbar - Z_975 * se_c, xbar + Z_975 * se_c
                if lo_c <= theta_true <= hi_c:
                    cc += 1
                wc += hi_c - lo_c
                if lo_b <= theta_true <= hi_b:
                    cb += 1
                wb += hi_b - lo_b
            infl_pct = 100.0 * (wb / wn - 1.0)
            out[n] = (cn / n_clust_trials, cc / n_clust_trials, cb / n_clust_trials, wb / n_clust_trials, infl_pct)
            if ed_cnt > 0:
                mean_ed_300 = ed_sum / ed_cnt
            print(
                f"{n:4d} {c_desc:>9} | {100*cn/n_clust_trials:8.2f}% {100*cc/n_clust_trials:8.2f}% "
                f"{100*cb/n_clust_trials:9.2f}% | {wn/n_clust_trials:9.4f} {wc/n_clust_trials:9.4f} "
                f"{wb/n_clust_trials:9.4f} {infl_pct:+8.1f}%"
            )
        return out, mean_ed_300

    clust_pos, _ = eval_clustered_regime(0.40, ns, "Clustered ICC=0.40")
    clust_neg, mean_ed_300 = eval_clustered_regime(0.00, [20, 50, 100, 300], "Negative Control ICC=0.00")
    print(
        f"  Exact Gamma(1,1) posterior E[d | data] at N=300, ICC=0.00 (60-trial mean): {mean_ed_300:.2f} "
        f"(unbounded u=d/(1+d) grid, d_max={quad.ds[-1]:.1f}; posterior tail extends well above d=5)."
    )
    assert clust_pos[100][0] < 0.82, "Expected naive CLT coverage collapse under ICC=0.40"
    assert clust_pos[100][2] > 0.92, "Expected Hierarchical Bayes recovery under ICC=0.40"
    assert clust_pos[20][1] < clust_pos[20][2], "Expected Hier Bayes to beat Clustered CLT at T=4 (N=20)"
    assert clust_neg[100][0] > 0.91, "Expected Naive CLT nominal coverage in ICC=0.00 negative control"
    assert 0.97 <= clust_neg[300][2] <= 1.00, f"Expected exact Gamma(1,1) over-coverage at N=300 ICC=0, got {clust_neg[300][2]}"
    assert 18.0 <= clust_neg[300][4] <= 28.0, f"Expected exact ~+22-24% width penalty at N=300 ICC=0, got {clust_neg[300][4]:.1f}%"
    assert mean_ed_300 > 5.0, f"Expected posterior E[d|data] > 5 at N=300 ICC=0, got {mean_ed_300}"

    # 1b(i). Analytic 80%-Power MDE Lookup Table
    print("\n--- 1b(i) [exact numerical / derived calculation]: Analytic 80%-Power MDE Lookup (alpha=0.05, x~U[0,1], r=0.5) ---")
    print(f"{'N':>4} | {'Wilson HW(p=.5)':>15} | {'Unpaired K=1':>13} | {'Paired K=1':>11} | {'Paired K=3':>11} | {'Paired sig=0':>13}")
    print("-" * 82)
    z_sum = Z_975 + Z_800
    for n in ns:
        lo_w, hi_w = wilson_ci_p(0.50, n)
        w_hw = 0.5 * (hi_w - lo_w)
        mde_unp = z_sum * math.sqrt(0.50 / n)
        mde_pk1 = z_sum * math.sqrt((1.0 / 12.0 + 1.0 / 3.0) / n)
        mde_pk3 = z_sum * math.sqrt((1.0 / 12.0 + 1.0 / 9.0) / n)
        mde_p0 = z_sum * math.sqrt((1.0 / 12.0) / n)
        print(
            f"{n:4d} |   +/-{100*w_hw:5.2f} pp   |    {100*mde_unp:6.2f} pp  |   {100*mde_pk1:6.2f} pp |   {100*mde_pk3:6.2f} pp |    {100*mde_p0:6.2f} pp"
        )

    # 1b(ii). Paired Type-M Exaggeration, Power & Type-S Error
    def build_paired_diff_cdf(delta: float, k_rep: int) -> Tuple[List[float], List[float]]:
        rho_g = 2.0 * math.sin(math.pi / 12.0)
        s_rho = math.sqrt(1.0 - rho_g * rho_g)
        m_q = 32
        z_pts = [norm_ppf((i + 0.5) / m_q) for i in range(m_q)]
        probs: Dict[int, float] = {d_num: 0.0 for d_num in range(-k_rep, k_rep + 1)}
        w = 1.0 / (m_q * m_q)
        for z1 in z_pts:
            x_b = 0.80 * norm_cdf(z1)
            if k_rep == 1:
                pb = (1.0 - x_b, x_b)
            else:
                qb = 1.0 - x_b
                pb = (qb**3, 3.0 * x_b * qb * qb, 3.0 * x_b * x_b * qb, x_b**3)
            for z_ind in z_pts:
                z2 = rho_g * z1 + s_rho * z_ind
                x_a = 0.80 * norm_cdf(z2) + delta
                if k_rep == 1:
                    pa = (1.0 - x_a, x_a)
                else:
                    qa = 1.0 - x_a
                    pa = (qa**3, 3.0 * x_a * qa * qa, 3.0 * x_a * x_a * qa, x_a**3)
                for ka in range(k_rep + 1):
                    for kb in range(k_rep + 1):
                        probs[ka - kb] += w * pa[ka] * pb[kb]
        vals = [d_num / k_rep for d_num in range(-k_rep, k_rep + 1)]
        cdf: List[float] = []
        acc = 0.0
        for d_num in range(-k_rep, k_rep + 1):
            acc += probs[d_num]
            cdf.append(acc)
        cdf[-1] = 1.0
        return vals, cdf

    n_tm_trials = 1500
    t_crits = {n: student_t_crit_975(n - 1) for n in (10, 20, 50, 100)}
    print(
        f"\n--- 1b(ii) [exact numerical / derived calculation]: Paired Type-M, Power & Type-S "
        f"({n_tm_trials:,} trials, Gaussian copula r=0.50; x_B~U[0,0.80], x_A~U[Delta,0.80+Delta]) ---"
    )
    print(f"{'Delta':>7} {'N':>4} {'K':>2} | {'Power(sig+)':>11} {'Any Sig':>8} {'Type-S':>8} {'Type-M E[|d|/D|sig]':>20} {'Mean |d| | sig':>15}")
    print("-" * 86)
    rand = rng.random
    type_m_records: Dict[Tuple[float, int, int], Tuple[float, float]] = {}
    for delta in (0.05, 0.10, 0.166):
        cdfs_by_k = {k_rep: build_paired_diff_cdf(delta, k_rep) for k_rep in (1, 3)}
        for n in (10, 20, 50, 100):
            t_c = t_crits[n]
            for k_rep in (1, 3):
                _vals, cdf = cdfs_by_k[k_rep]
                sig_pos = sig_neg = 0
                sum_abs_d_sig = 0.0
                if k_rep == 1:
                    c0, c1 = cdf[0], cdf[1]
                    for _ in range(n_tm_trials):
                        s_d = 0
                        s_d2 = 0
                        for _i in range(n):
                            u = rand()
                            if u < c0:
                                s_d -= 1
                                s_d2 += 1
                            elif u > c1:
                                s_d += 1
                                s_d2 += 1
                        mean_d = s_d / n
                        var_d = (s_d2 - n * mean_d * mean_d) / (n - 1)
                        if var_d <= 1e-15:
                            is_sig = abs(mean_d) > 1e-12
                        else:
                            is_sig = abs(mean_d / math.sqrt(var_d / n)) > t_c
                        if is_sig:
                            sum_abs_d_sig += abs(mean_d)
                            if mean_d > 0.0:
                                sig_pos += 1
                            else:
                                sig_neg += 1
                else:
                    c0, c1, c2, c3, c4, c5 = cdf[0], cdf[1], cdf[2], cdf[3], cdf[4], cdf[5]
                    for _ in range(n_tm_trials):
                        s_d = 0
                        s_d2 = 0
                        for _i in range(n):
                            u = rand()
                            if u < c2:
                                d3 = -3 if u < c0 else (-2 if u < c1 else -1)
                                s_d += d3
                                s_d2 += d3 * d3
                            elif u > c3:
                                d3 = 1 if u < c4 else (2 if u < c5 else 3)
                                s_d += d3
                                s_d2 += d3 * d3
                        mean_d = s_d / (3.0 * n)
                        var_d = (s_d2 / 9.0 - n * mean_d * mean_d) / (n - 1)
                        if var_d <= 1e-15:
                            is_sig = abs(mean_d) > 1e-12
                        else:
                            is_sig = abs(mean_d / math.sqrt(var_d / n)) > t_c
                        if is_sig:
                            sum_abs_d_sig += abs(mean_d)
                            if mean_d > 0.0:
                                sig_pos += 1
                            else:
                                sig_neg += 1
                tot_sig = sig_pos + sig_neg
                pwr = sig_pos / n_tm_trials
                any_sig = tot_sig / n_tm_trials
                type_s = (sig_neg / tot_sig) if tot_sig > 0 else 0.0
                type_m = ((sum_abs_d_sig / tot_sig) / delta) if tot_sig > 0 else float("nan")
                mean_sig_d = (sum_abs_d_sig / tot_sig) if tot_sig > 0 else float("nan")
                type_m_records[(delta, n, k_rep)] = (pwr, type_m)
                print(
                    f"+{100*delta:5.1f}% {n:4d} {k_rep:2d} | {100*pwr:10.2f}% {100*any_sig:7.2f}% {100*type_s:7.2f}% "
                    f"{type_m:19.2f}x {100*mean_sig_d:13.2f} pp"
                )

    print(f"\n--- 1b(iii) [exact numerical / derived calculation]: Negative Control (Delta=0.00, K=1, r=0.50, {n_tm_trials:,} trials) ---")
    vals0, cdf0 = build_paired_diff_cdf(0.0, 1)
    for n in (10, 20, 50, 100):
        t_c = t_crits[n]
        sig_pos = sig_neg = 0
        for _ in range(n_tm_trials):
            s_d = s_d2 = 0.0
            for _i in range(n):
                u = rand()
                d_i = vals0[0] if u <= cdf0[0] else (vals0[1] if u <= cdf0[1] else vals0[2])
                s_d += d_i
                s_d2 += d_i * d_i
            mean_d = s_d / n
            var_d = (s_d2 - n * mean_d * mean_d) / (n - 1)
            if var_d > 1e-15 and abs(mean_d / math.sqrt(var_d / n)) > t_c:
                if mean_d > 0.0:
                    sig_pos += 1
                else:
                    sig_neg += 1
        fp = (sig_pos + sig_neg) / n_tm_trials
        print(f"  Null Delta=0.00, N={n:3d}: two-sided Type-I = {100*fp:5.2f}% (pos={sig_pos}, neg={sig_neg})")
        assert 0.03 <= fp <= 0.075, f"Null Type-I out of range at N={n}: {fp}"
    assert type_m_records[(0.05, 10, 1)][1] > 4.0, "Expected >4x Type-M exaggeration at N=10, Delta=5pp"
    assert type_m_records[(0.166, 100, 3)][0] > 0.85, "Expected >85% power at N=100, K=3, Delta=16.6pp"

    # 1c. Miller §3.3 T=0 Negative Control & Miller p. 6 / p. 8-9 Arithmetic Audit
    print("\n--- 1c [exact numerical / derived calculation]: Miller (2024) §3.3 T=0 Control & p. 6 / p. 8-9 Arithmetic ---")
    n_mc = 25_000
    u1_sum = u1_sq = t0_1_sum = 0.0
    u2_sum = u2_sq = t0_2_sum = 0.0
    for _ in range(n_mc):
        x1 = rand()
        u1_sum += x1
        u1_sq += x1 * x1
        if x1 > 0.5:
            t0_1_sum += 1.0
        x2 = (1.0 / 3.0) + (2.0 / 3.0) * rand()
        u2_sum += x2
        u2_sq += x2 * x2
        if x2 > 0.5:
            t0_2_sum += 1.0
    e_u1 = u1_sum / n_mc
    v_u1 = u1_sq / n_mc - e_u1 * e_u1
    e_t0_1 = t0_1_sum / n_mc
    v_t0_1 = e_t0_1 * (1.0 - e_t0_1)
    e_u2 = u2_sum / n_mc
    v_u2 = u2_sq / n_mc - e_u2 * e_u2
    e_t0_2 = t0_2_sum / n_mc
    v_t0_2 = e_t0_2 * (1.0 - e_t0_2)

    print(
        f"  x ~ U[0, 1]:   Exact T=1 E={0.5:.6f}, Var=1/12={1/12:.6f} | "
        f"T=0 Bernoulli(1/2) E={0.5:.6f}, Var=1/4={0.25:.6f} (Var ratio = {0.25/(1/12):.4f}x)"
    )
    print(
        f"                 MC(25k)  T=1 E={e_u1:.5f}, Var={v_u1:.5f} | "
        f"T=0 E={e_t0_1:.5f}, Var={v_t0_1:.5f} (MC ratio = {v_t0_1/v_u1:.3f}x)"
    )
    print(
        f"  x ~ U[1/3, 1]: Exact T=1 E=2/3={2/3:.6f}, Var=1/27={1/27:.6f} | "
        f"T=0 Bernoulli(3/4)* E=3/4={0.75:.6f} (+{100*(0.75-2/3):.2f}pp bias), "
        f"Var=3/16={3/16:.6f} (Var ratio = {(3/16)/(1/27):.4f}x)"
    )
    print(
        f"                 MC(25k)  T=1 E={e_u2:.5f}, Var={v_u2:.5f} | "
        f"T=0 E={e_t0_2:.5f}, Var={v_t0_2:.5f} (MC ratio = {v_t0_2/v_u2:.3f}x)"
    )
    print("  (*Audit note: Miller p. 6 L282 prints 'Bernoulli(p=1/4)' typo before correctly writing E=3/4, Var=3/16.)")

    var_unp = 1.0 / 12.0 + 1.0 / 12.0
    cov_ab = 0.5 * math.sqrt((1.0 / 12.0) * (1.0 / 12.0))
    omega2_exact = var_unp - 2.0 * cov_ab
    omega2_printed = 1.0 / 9.0
    n_exact = (z_sum * z_sum) * omega2_exact / (0.03 * 0.03)
    n_printed = (z_sum * z_sum) * omega2_printed / (0.03 * 0.03)
    mde_198_k1_exact = z_sum * math.sqrt((omega2_exact + 1.0 / 3.0) / 198.0)
    mde_198_k10_exact = z_sum * math.sqrt((omega2_exact + 1.0 / 30.0) / 198.0)
    mde_198_k1_printed = z_sum * math.sqrt((omega2_printed + 1.0 / 3.0) / 198.0)
    mde_198_k10_printed = z_sum * math.sqrt((omega2_printed + 1.0 / 30.0) / 198.0)
    print(
        f"  Miller p. 8-9 Paired Var (Var_A=Var_B=1/12, r=0.5 => Cov=1/24):\n"
        f"    Exact  omega^2 = 1/6 - 2(1/24) = 1/12 = {omega2_exact:.6f} (50.0% red.) -> n(d=3pp) = {n_exact:.2f} (~727); "
        f"MDE(n=198, K=1->10): {100*mde_198_k1_exact:.2f}% -> {100*mde_198_k10_exact:.2f}%\n"
        f"    Miller printed omega^2 = 1/9   = {omega2_printed:.6f} (33.3% red.) -> n(d=3pp) = {n_printed:.2f} (~969); "
        f"MDE(n=198, K=1->10): {100*mde_198_k1_printed:.2f}% -> {100*mde_198_k10_printed:.2f}% (paper: 13.2% -> 7.5%)"
    )
    assert abs(omega2_exact - 1.0 / 12.0) < 1e-15
    assert round(n_exact) == 727 and round(n_printed) == 969


# ---------------------------------------------------------------------------
# Probe 2: LLM-as-a-Judge Position/Verbosity Bias & Skewness Mechanism
# ---------------------------------------------------------------------------

def fit_glm_intercept_test(
    dls: Sequence[float],
    y_ab: Sequence[int],
    y_ba: Sequence[int],
    t_crit: float,
    ridge: float = 0.05,
    tol: float = 1e-10,
    max_iter: int = 50,
) -> Tuple[float, float, bool, int]:
    """Swap + length-controlled logistic GLM with item-clustered sandwich SE on intercept b0.

    Iterates Newton-Raphson (with step damping if needed) to strict convergence
    max|delta_beta| < tol (up to max_iter) and asserts convergence.
    """
    n = len(dls)
    b0 = b1 = b2 = 0.0
    exp_fn = math.exp
    converged = False
    iters_used = 0
    items = list(zip(dls, y_ab, y_ba))
    for it in range(1, max_iter + 1):
        iters_used = it
        g0 = g1 = g2 = 0.0
        h00 = h01 = h02 = h11 = h12 = h22 = 0.0
        for dl, yab, yba in items:
            base = b0 + b2 * dl
            z1 = base + b1
            z2 = base - b1
            p1 = (1.0 / (1.0 + exp_fn(-z1))) if z1 >= 0.0 else (exp_fn(z1) / (1.0 + exp_fn(z1)))
            p2 = (1.0 / (1.0 + exp_fn(-z2))) if z2 >= 0.0 else (exp_fn(z2) / (1.0 + exp_fn(z2)))
            r1 = yab - p1
            r2 = yba - p2
            w1 = p1 * (1.0 - p1)
            w2 = p2 * (1.0 - p2)
            rs = r1 + r2
            g0 += rs
            g1 += r1 - r2
            g2 += rs * dl
            ws = w1 + w2
            wd = w1 - w2
            h00 += ws
            h01 += wd
            h02 += ws * dl
            h11 += ws
            h12 += wd * dl
            h22 += ws * dl * dl
        g0 -= ridge * b0
        g1 -= ridge * b1
        g2 -= ridge * b2
        s0, s1, s2 = solve_spd_3x3(h00 + ridge, h01, h02, h11 + ridge, h12, h22 + ridge, g0, g1, g2)
        max_step = max(abs(s0), abs(s1), abs(s2))
        if max_step > 5.0:
            scale = 5.0 / max_step
            s0 *= scale
            s1 *= scale
            s2 *= scale
        b0 += s0
        b1 += s1
        b2 += s2
        if max_step < tol:
            converged = True
            break
    assert converged, f"Logistic GLM Newton-Raphson failed to converge within {max_iter} iterations"

    # Item-clustered sandwich variance on b0: var(b0) = (H^{-1} M H^{-1})_{00}
    # At convergence (max_step < 1e-10), H from the final iteration is exact to 1e-10;
    # compute the meat matrix M at converged (b0, b1, b2).
    m00 = m01 = m02 = m11 = m12 = m22 = 0.0
    for dl, yab, yba in items:
        base = b0 + b2 * dl
        z1 = base + b1
        z2 = base - b1
        p1 = (1.0 / (1.0 + exp_fn(-z1))) if z1 >= 0.0 else (exp_fn(z1) / (1.0 + exp_fn(z1)))
        p2 = (1.0 / (1.0 + exp_fn(-z2))) if z2 >= 0.0 else (exp_fn(z2) / (1.0 + exp_fn(z2)))
        u0 = (yab - p1) + (yba - p2)
        u1 = (yab - p1) - (yba - p2)
        u2 = u0 * dl
        m00 += u0 * u0
        m01 += u0 * u1
        m02 += u0 * u2
        m11 += u1 * u1
        m12 += u1 * u2
        m22 += u2 * u2
    v0_0, v0_1, v0_2 = solve_spd_3x3(h00 + ridge, h01, h02, h11 + ridge, h12, h22 + ridge, 1.0, 0.0, 0.0)
    tmp0 = v0_0 * m00 + v0_1 * m01 + v0_2 * m02
    tmp1 = v0_0 * m01 + v0_1 * m11 + v0_2 * m12
    tmp2 = v0_0 * m02 + v0_1 * m12 + v0_2 * m22
    var_b0 = (tmp0 * v0_0 + tmp1 * v0_1 + tmp2 * v0_2) * (n / max(1.0, n - 3.0))
    t_stat = b0 / math.sqrt(max(1e-12, var_b0))
    return b0, t_stat, (abs(t_stat) > t_crit), iters_used


def run_probe_2(rng: random.Random) -> None:
    print("\n" + "=" * 94)
    print("PROBE 2 [toy model / illustrative surrogate]: JUDGE DEBIASING PROTOCOLS & SKEWNESS MECHANISM")
    print("=" * 94)

    n_trials = 300
    gauss = rng.gauss
    rand = rng.random
    exp_fn = math.exp
    t_swap = {n: student_t_crit_975(n - 1) for n in (10, 20, 50, 100)}
    t_glm_map = {n: student_t_crit_975(n - 3) for n in (10, 20, 50, 100)}
    global_max_nr_iters = 0
    total_glm_fits = 0

    def eval_judge_protocols(
        label: str,
        ns_eval: Sequence[int],
        acc: float,
        beta_pos: float,
        beta_len: float,
        mu_len: float,
        delta_q: float,
    ) -> Dict[int, Tuple[float, float, float, float]]:
        nonlocal global_max_nr_iters, total_glm_fits
        alpha_acc = math.log(acc / (1.0 - acc))
        print(
            f"\n--- 2a [toy model / illustrative surrogate]: {label} "
            f"(acc={acc:.2f}, beta_pos={beta_pos:.2f}, beta_len={beta_len:.2f}, "
            f"mu_len={mu_len:+.2f}, delta_Q={delta_q:+.2f}, {n_trials} trials) ---"
        )
        metric_hdr = "Power" if delta_q > 0 else "False-Promo / Type-I"
        print(f"{'N':>4} | {'1-Ord Fixed':>12} {'1-Ord Rand':>12} {'Swap+Tie':>10} {'Swap+LenGLM':>12} | {'Avg Conflict':>12}  [{metric_hdr}]")
        print("-" * 84)
        out: Dict[int, Tuple[float, float, float, float]] = {}
        for n in ns_eval:
            c_fix = c_rnd = c_swp = c_glm = 0
            conflict_tot = 0
            tc_swp = t_swap[n]
            tc_glm = t_glm_map[n]
            inv_se_bin = 1.0 / math.sqrt(0.25 * n)
            half_n = 0.5 * n
            for _ in range(n_trials):
                dls = [0.0] * n
                y_ab = [0] * n
                y_ba = [0] * n
                s_fix = s_rnd = s_swp = s_swp2 = 0
                for i in range(n):
                    dl_i = gauss(mu_len, 1.0)
                    q_i = gauss(delta_q, 0.5)
                    dls[i] = dl_i
                    base_lin = alpha_acc * q_i + beta_len * dl_i
                    z_ab = base_lin + beta_pos
                    z_ba = base_lin - beta_pos
                    p_ab = (1.0 / (1.0 + exp_fn(-z_ab))) if z_ab >= 0.0 else (exp_fn(z_ab) / (1.0 + exp_fn(z_ab)))
                    p_ba = (1.0 / (1.0 + exp_fn(-z_ba))) if z_ba >= 0.0 else (exp_fn(z_ba) / (1.0 + exp_fn(z_ba)))
                    ab = 1 if rand() < p_ab else 0
                    ba = 1 if rand() < p_ba else 0
                    y_ab[i] = ab
                    y_ba[i] = ba
                    if ab != ba:
                        conflict_tot += 1
                    s_fix += ab
                    s_rnd += ab if rand() < 0.5 else ba
                    v_i = ab + ba - 1
                    s_swp += v_i
                    s_swp2 += v_i * v_i
                z_f = (s_fix - half_n) * inv_se_bin
                z_r = (s_rnd - half_n) * inv_se_bin
                if (z_f > Z_975) if delta_q > 0 else (abs(z_f) > Z_975):
                    c_fix += 1
                if (z_r > Z_975) if delta_q > 0 else (abs(z_r) > Z_975):
                    c_rnd += 1
                mean_v = s_swp / n
                var_v = (s_swp2 - n * mean_v * mean_v) / (n - 1)
                if var_v > 1e-15:
                    t_v = mean_v / math.sqrt(var_v / n)
                    if (t_v > tc_swp) if delta_q > 0 else (abs(t_v) > tc_swp):
                        c_swp += 1
                _b0, t_g, is_sig, iters = fit_glm_intercept_test(dls, y_ab, y_ba, tc_glm)
                total_glm_fits += 1
                if iters > global_max_nr_iters:
                    global_max_nr_iters = iters
                if (t_g > tc_glm) if delta_q > 0 else is_sig:
                    c_glm += 1
            rates = (c_fix / n_trials, c_rnd / n_trials, c_swp / n_trials, c_glm / n_trials)
            out[n] = rates
            conf_rate = conflict_tot / (n_trials * n)
            print(
                f"{n:4d} | {100*rates[0]:11.2f}% {100*rates[1]:11.2f}% {100*rates[2]:9.2f}% {100*rates[3]:11.2f}% | {100*conf_rate:11.2f}%"
            )
        return out

    res_b55 = eval_judge_protocols("Biased Judge (a=0.55, Pos+Verbosity, H0)", [10, 20, 50, 100], 0.55, 1.10, 0.85, 0.80, 0.0)
    res_b75 = eval_judge_protocols("Biased Judge (a=0.75, Pos+Verbosity, H0)", [10, 20, 50, 100], 0.75, 1.10, 0.85, 0.80, 0.0)
    res_pos_only = eval_judge_protocols("Ablation: Position Bias ONLY (H0)", [20, 50, 100], 0.75, 1.10, 0.00, 0.80, 0.0)
    res_neg = eval_judge_protocols("Negative Control: Unbiased Judge (H0)", [10, 20, 50, 100], 0.75, 0.00, 0.00, 0.80, 0.0)
    res_pwr = eval_judge_protocols("Non-Vacuity Check: True Lift (H1, delta_Q=+1.0)", [20, 50, 100], 0.75, 1.10, 0.85, 0.80, 1.0)

    print(
        f"\n  Newton-Raphson convergence check: all {total_glm_fits:,} GLM fits converged to max|step| < 1e-10 "
        f"(max iterations observed = {global_max_nr_iters} <= 50) [PASS]."
    )
    print(
        "  Surrogate scope caveat: Probe 2a fits a linear-logit GLM matching the unconfounded synthetic DGP "
        "(Delta_L indep. of Q); observational length control cannot separate fluff from substance-correlated length."
    )

    assert res_b75[50][0] > 0.90, "Expected catastrophic Type-I under single-order fixed"
    assert res_b75[50][2] > 0.50, "Expected swap-and-tie still fails under verbosity bias"
    assert 0.02 <= res_b75[50][3] <= 0.09, f"Expected Swap+LenGLM calibrated under bias, got {res_b75[50][3]}"
    assert res_pos_only[50][0] > 0.70 and res_pos_only[50][2] < 0.09, "Expected swap-and-tie fixes position-only bias"
    for idx in range(4):
        assert 0.02 <= res_neg[50][idx] <= 0.09, f"Expected unbiased negative control ~0.05, got {res_neg[50]}"
    assert res_pwr[50][3] > 0.75, f"Expected Swap+LenGLM non-vacuous power >75% at N=50, got {res_pwr[50][3]}"
    assert res_b55[50][3] <= 0.09, "Expected Swap+LenGLM calibrated at a=0.55"

    # 2b. Illustrative Skewness Mechanism for Aggregation Inversion
    print(
        "\n--- 2b [toy model / illustrative skewness mechanism]: Why Right-Tail Bias Spikes Invert "
        "maj@5 > single > mean@5 > best-of-5 (5,000 trials, k=5 draws) ---"
    )
    print("  Scope note: Pure mathematical skewness illustration (median(B-A) < 0 < E[B-A]) -- NOT a causal")
    print("  proof or reproduction of Gu et al. Table 4 (which confounds pairwise maj@5 vs. pointwise mean@5")
    print("  and evaluates only n=34 items on the Length bias split).")
    print("  Skewed regime:    75% draws favor A (+0.45, sd=0.60); 25% right-tail spikes boost B (+3.2).")
    print("  Negative control:  0% spikes (symmetric Gaussian noise).")
    n_agg = 5_000
    print(f"  {'Regime':<32} | {'Single':>8} {'maj@5':>8} {'mean@5':>8} {'best-of-5':>10} | {'Exact Condorcet':>15}")
    print("  " + "-" * 92)
    agg_results: Dict[str, Tuple[float, float, float, float]] = {}
    for reg_name, p_spike, spike_sz in [
        ("Skewed Right-Tail Spikes", 0.25, 3.2),
        ("Negative Control (Symmetric)", 0.00, 0.0),
    ]:
        w_single = w_maj = w_mean = w_best = 0
        for _ in range(n_agg):
            votes_a = 0
            sum_a = sum_b = 0.0
            max_a = max_b = -1e9
            for j in range(5):
                sa = 7.45 + gauss(0.0, 0.60)
                sb = 7.00 + gauss(0.0, 0.60) + (spike_sz if rand() < p_spike else 0.0)
                if j == 0 and sa > sb:
                    w_single += 1
                if sa > sb:
                    votes_a += 1
                sum_a += sa
                sum_b += sb
                if sa > max_a:
                    max_a = sa
                if sb > max_b:
                    max_b = sb
            if votes_a >= 3:
                w_maj += 1
            if sum_a > sum_b:
                w_mean += 1
            if max_a > max_b:
                w_best += 1
        p1 = w_single / n_agg
        condorcet = sum(math.comb(5, m) * (p1 ** m) * ((1.0 - p1) ** (5 - m)) for m in (3, 4, 5))
        res = (p1, w_maj / n_agg, w_mean / n_agg, w_best / n_agg)
        agg_results[reg_name] = res
        print(
            f"  {reg_name:<32} | {100*res[0]:7.2f}% {100*res[1]:7.2f}% {100*res[2]:7.2f}% {100*res[3]:9.2f}% | {100*condorcet:14.2f}%"
        )
    s_sk, mj_sk, mn_sk, bt_sk = agg_results["Skewed Right-Tail Spikes"]
    s_nc, mj_nc, mn_nc, bt_nc = agg_results["Negative Control (Symmetric)"]
    assert mj_sk > s_sk > mn_sk > bt_sk, f"Expected skewness inversion maj>single>mean>best, got {agg_results}"
    assert mn_nc >= mj_nc - 0.01 and mn_nc > s_nc, f"Expected mean@5 >= maj@5 under symmetric noise, got {agg_results}"


# ---------------------------------------------------------------------------
# Probe 3: Exact Likelihood-Ratio Crossover Theorem & Illustrative Surrogate
# ---------------------------------------------------------------------------

def run_probe_3(rng: random.Random) -> None:
    print("\n" + "=" * 94)
    print("PROBE 3: VERIFICATION ASYMMETRY — EXACT LIKELIHOOD-RATIO THEOREM & ILLUSTRATIVE SURROGATE")
    print("=" * 94)

    # 3a. Exact Algebraic Likelihood-Ratio Crossover Theorem
    print("\n--- 3a [exact numerical / derived calculation]: Exact Bayes PPV & Likelihood-Ratio Crossover Theorem ---")
    swt_pi = 50.0 / 276.0  # 0.18115942... (SWT-Bench Table 6: 50/276 SWE-Agent fixes on SWT-Bench-Lite)
    swt_fpr = (swt_pi * 0.20 * (1.0 - 0.478)) / ((1.0 - swt_pi) * 0.478)  # 0.04832081...
    swt_lr = 0.20 / swt_fpr  # 4.139004...

    lr_27_15 = (27.0 / 42.0) / (15.0 / 42.0)  # Exact 1.8000 (27/15)
    lr_25_17 = (25.0 / 42.0) / (17.0 / 42.0)  # Exact 1.470588... (25/17)
    fpr_cross_180 = 0.20 / lr_27_15  # Exact 1/9 = 11.1111...%
    fpr_cross_147 = 0.20 / lr_25_17  # Exact 0.136 = 13.6000%

    assert abs(swt_fpr - 5.22 / 108.028) < 1e-12
    assert abs(swt_lr - (0.20 * 108.028 / 5.22)) < 1e-10
    assert abs(fpr_cross_180 - 1.0 / 9.0) < 1e-15
    assert abs(fpr_cross_147 - 0.136) < 1e-15

    print("  Theorem: PPV(pi) = [1 + ((1 - pi) / pi) * (1 / LR)]^(-1) is strictly increasing in LR = TPR / FPR")
    print("           for every base rate pi in (0, 1). Thus filter A beats filter B in precision iff LR_A > LR_B.")
    print(
        f"  Exact SWT-Bench implied FPR (pi=50/276={100*swt_pi:.2f}%, TPR=20.0%, PPV=47.8%): "
        f"FPR = {100*swt_fpr:.3f}% (LR = {swt_lr:.3f})"
    )
    print("  Exact Crossover Thresholds for a TPR_test = 20.0% execution filter to dominate a benchmark LR at ALL pi:")
    print(f"    vs. LR = 25/17 = {lr_25_17:.4f} (illustrative 59.52% plug-in): requires FPR_test < {100*fpr_cross_147:.2f}%")
    print(f"    vs. LR = 27/15 = {lr_27_15:.4f} (illustrative 64.29% plug-in): requires FPR_test < {100*fpr_cross_180:.2f}% (exact 1/9)")

    # 3b. Illustrative Surrogate Plug-In Mapping & Monte Carlo Verification
    print("\n--- 3b [toy model / illustrative surrogate mapping]: Pointwise Plug-In & 100,000-Patch MC Check ---")
    print("  CRITICAL SURROGATE CAVEAT: Mapping JudgeBench Coding accuracies (59.52% GPT-4o, 64.29% Claude-3.5)")
    print("  to pointwise (TPR=acc, FPR=1-acc) is an ILLUSTRATIVE SURROGATE ONLY:")
    print("    (1) JudgeBench is pairwise 2AFC scoring swap-inconsistency and ties as 0 (random=25%, not 50%);")
    print("        swap-inconsistent judgments do not automatically become false positives in a reject-on-conflict filter;")
    print("    (2) JudgeBench Coding contains N=42 competitive-programming pairs pre-filtered to borderline GPT-4o cases;")
    print("    (3) Applies to non-reasoning judges only (reasoning judges reach 92.86%-100.0% on JudgeBench Coding).")

    verifiers = [
        ("Unfiltered Baseline", 1.0000, 1.0000),
        ("Surrogate: JB GPT-4o (59.5%)", 25.0 / 42.0, 17.0 / 42.0),
        ("Surrogate: JB Claude-3.5 (64.3%)", 27.0 / 42.0, 15.0 / 42.0),
        ("SWT-Bench Test Filter (cal.)", 0.2000, swt_fpr),
        ("Curated High-Spec Test (FPR=2%)", 0.2000, 0.0200),
        ("NEG CTRL A: UTBoost Weak(R=20%)", 0.2000, 0.2840),
        ("NEG CTRL B: UTBoost Weak(R=80%)", 0.8000, 0.2840),
    ]
    base_rates = [0.15, swt_pi, 0.25, 0.40]

    print(
        f"\n{'Verifier':<34} {'TPR':>6} {'FPR':>6} {'LR':>6} | "
        + " | ".join(f"pi={100*pi:4.1f}% PPV(FAR)" for pi in base_rates)
    )
    print("-" * 126)

    ppv_grid: Dict[Tuple[str, float], float] = {}
    for name, tpr, fpr in verifiers:
        lr = tpr / fpr
        cells = []
        for pi in base_rates:
            ppv = (pi * tpr) / (pi * tpr + (1.0 - pi) * fpr)
            far = 1.0 - ppv
            ppv_grid[(name, pi)] = ppv
            cells.append(f"{100*ppv:5.1f}%({100*far:4.1f}%)")
        print(f"{name:<34} {100*tpr:5.1f}% {100*fpr:5.2f}% {lr:6.2f} | " + "   | ".join(cells))

    n_patches = 100_000
    rand = rng.random
    print(f"\n  Monte Carlo cross-check at SWT-Bench base rate pi={100*swt_pi:.2f}% ({n_patches:,} patches):")
    print(f"  {'Verifier':<34} | {'Analytic PPV':>12} {'MC PPV':>9} {'MC FAR':>9} {'Accepted':>10}")
    print("  " + "-" * 82)
    for name, tpr, fpr in verifiers:
        tp = fp = 0
        for _ in range(n_patches):
            if rand() < swt_pi:
                if rand() < tpr:
                    tp += 1
            else:
                if rand() < fpr:
                    fp += 1
        acc_cnt = tp + fp
        mc_ppv = tp / acc_cnt
        ana_ppv = ppv_grid[(name, swt_pi)]
        print(
            f"  {name:<34} | {100*ana_ppv:11.2f}% {100*mc_ppv:8.2f}% {100*(1-mc_ppv):8.2f}% {acc_cnt:10d}"
        )
        assert abs(mc_ppv - ana_ppv) < 0.020, f"MC mismatch for {name}: {mc_ppv} vs {ana_ppv}"

    assert ppv_grid[("SWT-Bench Test Filter (cal.)", swt_pi)] > ppv_grid[("Surrogate: JB Claude-3.5 (64.3%)", swt_pi)] + 0.15
    assert ppv_grid[("NEG CTRL A: UTBoost Weak(R=20%)", swt_pi)] < swt_pi, "Weak test (LR<1) must drop below base rate!"
    assert ppv_grid[("NEG CTRL B: UTBoost Weak(R=80%)", swt_pi)] < ppv_grid[("SWT-Bench Test Filter (cal.)", swt_pi)] - 0.08


def main() -> None:
    print(f"verify_eval_stats_and_judge_probes.py | seed={SEED} | stdlib-only deterministic run")
    run_probe_1(random.Random(SEED))
    run_probe_2(random.Random(SEED + 1))
    run_probe_3(random.Random(SEED + 2))
    print("\n" + "=" * 94)
    print("ALL 3 PROBES, CONVERGENCE CHECKS & NEGATIVE CONTROLS PASSED (exit 0)")
    print("=" * 94)


if __name__ == "__main__":
    main()
