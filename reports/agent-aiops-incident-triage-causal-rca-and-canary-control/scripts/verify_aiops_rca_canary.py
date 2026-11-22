#!/usr/bin/env python3
"""
Deterministic Verification Probe for Autonomous Operations, Causal RCA,
Telemetry Correlation, and Safe Canary Control Laws.

Pure Python 3.10+ standard library only. Deterministic across PYTHONHASHSEED values.
Verifies pinned repository logic, published analytical models, and controlled
simulations across five pillars:
  1. Kayenta (spinnaker/kayenta@5310ab7d): Mann-Whitney Hodges-Lehmann tolerance=0.25,
     minimum feasible sample size under AR(1) rank-VIF + Holm-Bonferroni, null FWER
     and alternative outage power, finite-sample lag-1 rho_hat bias, and judge bugs.
  2. Google SRE Workbook Ch. 5: Multi-window burn-rate alerting vs. naive rules,
     low-traffic erratum verification, and exact thinned homogeneous Poisson vs.
     fixed-denominator false-page rates.
  3. Argo Rollouts (argoproj/argo-rollouts@8c9c5ad2): AnalysisRun counter/phase
     semantics, sequential if-overwrite, RunSummary miscount, binomial false-abort
     scaling, and consistent conditional/unconditional Inconclusive bleed-out accounting.
  4. BARO & RCAEval (phamquiluan/BARO@e35f4ec1, phamquiluan/RCAEval@a30feeba):
     one-sided scoring, preprocess()/drop_constant() silent deletion vs. non-constant
     zero-IQR scale dominance, mmbaro 15x decimation aliasing, and repairs.
  5. AIOpsLab & OpenRCA (microsoft/AIOpsLab@576c3f08, microsoft/OpenRCA@2a481ae6):
     vacuous-health mitigation passes and rigid regex JSON/timestamp false rejections.
"""

from __future__ import annotations

import bisect
import itertools
import json
import math
import random
import re
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from typing import Any


# =============================================================================
# Shared Exact Math Utilities (Stdlib Only)
# =============================================================================

def norm_cdf(x: float) -> float:
    return 0.5 * (1.0 + math.erf(x / math.sqrt(2.0)))


def norm_ppf(p: float) -> float:
    """Inverse standard normal CDF via exact monotone bisection on erf (1e-14 precision)."""
    if not (0.0 < p < 1.0):
        raise ValueError("p must be in (0, 1)")
    lo, hi = -10.0, 10.0
    for _ in range(80):
        mid = 0.5 * (lo + hi)
        if norm_cdf(mid) < p:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def poisson_pmf(k: int, lam: float) -> float:
    if lam <= 0.0:
        return 1.0 if k == 0 else 0.0
    return math.exp(k * math.log(lam) - lam - math.lgamma(k + 1))


def poisson_sf_strict(thresh: float, lam: float) -> float:
    """Exact P(Pois(lam) > thresh) using direct upper-tail sum in the right tail."""
    k_min = int(math.floor(thresh)) + 1
    if k_min <= 0:
        return 1.0
    if lam <= 0.0:
        return 0.0
    if k_min <= lam:
        cdf = sum(poisson_pmf(k, lam) for k in range(k_min))
        return max(0.0, 1.0 - cdf)
    total = 0.0
    k = k_min
    while True:
        term = poisson_pmf(k, lam)
        total += term
        if term == 0.0 or (total > 0.0 and term < total * 1e-16):
            break
        k += 1
        if k > k_min + 2000:
            break
    return total


def poisson_cdf_table(lam: float, max_k: int) -> list[float]:
    """Exact Poisson CDF table P(Pois(lam) <= k) for k = 0..max_k."""
    if max_k < 0:
        return []
    cdf = [0.0] * (max_k + 1)
    if lam <= 0.0:
        for k in range(max_k + 1):
            cdf[k] = 1.0
        return cdf
    running = 0.0
    # Compute around active support cleanly via log-space PMF to avoid underflow/overflow
    for k in range(max_k + 1):
        running += poisson_pmf(k, lam)
        cdf[k] = min(1.0, running)
    return cdf


# =============================================================================
# PROBE 1: spinnaker/kayenta@5310ab7d
# =============================================================================

def _is_strictly_increasing(s: list[float]) -> bool:
    for k in range(len(s) - 1):
        if s[k] >= s[k + 1]:
            return False
    return True


def kayenta_wilcoxon_diff_sorted(
    mu: float,
    quantile: float,
    sx: list[float],
    sy: list[float],
    strict_distinct: bool = False,
) -> float:
    """Exact port of MannWhitney.scala:58-78 on pre-sorted arrays (bit-identical to NaturalRanking)."""
    nx = len(sx)
    ny = len(sy)
    if strict_distinct:
        bl = bisect.bisect_left
        u_twice = 0
        tie_pairs = 0
        if mu == 0.0:
            for v in sx:
                lo = bl(sy, v)
                if lo < ny and sy[lo] == v:
                    u_twice += 2 * lo + 1
                    tie_pairs += 1
                else:
                    u_twice += 2 * lo
        else:
            for vx in sx:
                v = vx - mu
                lo = bl(sy, v)
                if lo < ny and sy[lo] == v:
                    u_twice += 2 * lo + 1
                    tie_pairs += 1
                else:
                    u_twice += 2 * lo
        x_len = float(nx)
        y_len = float(ny)
        dz = 0.5 * u_twice - x_len * y_len / 2.0
        tie_sum = 6.0 * tie_pairs
    else:
        i = 0
        j = 0
        pos = 0
        rank_sum_x = 0.0
        tie_sum = 0.0
        while i < nx or j < ny:
            if i < nx and (j >= ny or sx[i] - mu < sy[j]):
                val = sx[i] - mu
            else:
                val = sy[j]
            cx = 0
            while i < nx and sx[i] - mu == val:
                cx += 1
                i += 1
            cy = 0
            while j < ny and sy[j] == val:
                cy += 1
                j += 1
            ctot = cx + cy
            avg_rank = pos + 0.5 * (ctot + 1)
            if cx:
                rank_sum_x += cx * avg_rank
            if ctot > 1:
                tie_sum += ctot * ctot * ctot - ctot
            pos += ctot
        x_len = float(nx)
        y_len = float(ny)
        dz = rank_sum_x - x_len * (x_len + 1.0) / 2.0 - x_len * y_len / 2.0

    if math.isnan(dz):
        signum = 0.0
    elif dz > 0.0:
        signum = 1.0
    elif dz < 0.0:
        signum = -1.0
    else:
        signum = 0.0
    correction_ci = signum * 0.5
    n_tot = x_len + y_len
    var_ci = (x_len * y_len / 12.0) * ((n_tot + 1.0) - tie_sum / (n_tot * (n_tot - 1.0)))
    sigma_ci = math.sqrt(max(0.0, var_ci))
    if sigma_ci == 0.0:
        raise ValueError("cannot compute confidence interval when all observations are tied")
    return (dz - correction_ci) / sigma_ci - quantile


def kayenta_wilcoxon_diff(mu: float, quantile: float, x: list[float], y: list[float]) -> float:
    """Exact port of MannWhitney.scala:58-78."""
    sx = sorted(x)
    sy = sorted(y)
    return kayenta_wilcoxon_diff_sorted(
        mu, quantile, sx, sy, strict_distinct=_is_strictly_increasing(sx) and _is_strictly_increasing(sy)
    )


def kayenta_brent_solve(ax: float, bx: float, fa: float, fb: float, func) -> float:
    """Exact port of BrentSolver.java:37-114."""
    max_iterations = 1000
    tolerance = 1e-4
    eps = 2.220446049250313e-16

    a, b, c, fc = ax, bx, ax, fa
    if fa == 0.0:
        return a
    if fb == 0.0:
        return b

    iteration = max_iterations + 1
    while iteration > 0:
        iteration -= 1
        prev_step = b - a
        if abs(fc) < abs(fb):
            a, b, c = b, c, b
            fa, fb, fc = fb, fc, fb
        tol_act = 2.0 * eps * abs(b) + tolerance / 2.0
        new_step = (c - b) / 2.0
        if abs(new_step) <= tol_act or fb == 0.0:
            return b
        if abs(prev_step) >= tol_act and abs(fa) > abs(fb):
            cb = c - b
            if a == c:
                t1 = fb / fa
                p = cb * t1
                q = 1.0 - t1
            else:
                q = fa / fc
                t1 = fb / fc
                t2 = fb / fa
                p = t2 * (cb * q * (q - t1) - (b - a) * (t1 - 1.0))
                q = (q - 1.0) * (t1 - 1.0) * (t2 - 1.0)
            if p > 0.0:
                q = -q
            else:
                p = -p
            if p < (0.75 * cb * q - abs(tol_act * q) / 2.0) and p < abs(prev_step * q / 2.0):
                new_step = p / q
        if abs(new_step) < tol_act:
            new_step = tol_act if new_step > 0.0 else -tol_act
        a, fa = b, fb
        b += new_step
        fb = func(b)
        if (fb > 0.0 and fc > 0.0) or (fb < 0.0 and fc < 0.0):
            c, fc = a, fa
    return b


def kayenta_mann_whitney_ci(
    x: list[float], y: list[float], conf_level: float = 0.98
) -> tuple[float, float, float]:
    """Exact port of MannWhitney.scala:80-108 returning (lower_ci, upper_ci, hl_estimate)."""
    alpha = 1.0 - conf_level
    sx = sorted(x)
    sy = sorted(y)
    strict = _is_strictly_increasing(sx) and _is_strictly_increasing(sy)
    mu_min = sx[0] - sy[-1]
    mu_max = sx[-1] - sy[0]

    def find_root(zq: float) -> float:
        f_lo = kayenta_wilcoxon_diff_sorted(mu_min, zq, sx, sy, strict)
        f_hi = kayenta_wilcoxon_diff_sorted(mu_max, zq, sx, sy, strict)
        if f_lo <= 0.0:
            return mu_min
        if f_hi >= 0.0:
            return mu_max
        return kayenta_brent_solve(mu_min, mu_max, f_lo, f_hi, lambda m: kayenta_wilcoxon_diff_sorted(m, zq, sx, sy, strict))

    z_quant = norm_ppf(alpha / 2.0)  # negative, e.g. -2.326348
    lo_ci = find_root(-z_quant)
    hi_ci = find_root(z_quant)
    f_lo0 = kayenta_wilcoxon_diff_sorted(mu_min, 0.0, sx, sy, strict)
    f_hi0 = kayenta_wilcoxon_diff_sorted(mu_max, 0.0, sx, sy, strict)
    est = kayenta_brent_solve(mu_min, mu_max, f_lo0, f_hi0, lambda m: kayenta_wilcoxon_diff_sorted(m, 0.0, sx, sy, strict))
    return lo_ci, hi_ci, est


def kayenta_mean_ratio(control: list[float], experiment: list[float]) -> float:
    """Exact port of EffectSizes.scala:16-20."""
    c_mean = sum(control) / len(control)
    e_mean = sum(experiment) / len(experiment)
    if c_mean == 0.0 or e_mean == 0.0:
        return math.nan
    return e_mean / c_mean


def kayenta_parse_nan_strategy(s: str) -> str:
    """Exact port of BaseMetricClassifier.scala:50-56."""
    if s == "remove":
        return "Remove"
    if s == "replace":
        return "Replace"
    return "Remove"


def kayenta_classify_metric(
    name: str,
    group: str,
    control: list[float],
    experiment: list[float],
    direction: str = "either",
    nan_strategy_str: str = "none",
    is_critical: bool = False,
    must_have_data: bool = False,
    allowed_thresholds: tuple[float, float] = (1.0, 1.0),
    critical_thresholds: tuple[float, float] = (1.0, 1.0),
    tolerance: float = 0.25,
    conf_level: float = 0.98,
    rng: random.Random | None = None,
) -> dict[str, Any]:
    """Exact port of NetflixACAJudge.scala:91-174 + MannWhitneyClassifier.scala:38-211."""
    nan_strategy = kayenta_parse_nan_strategy(nan_strategy_str)
    if nan_strategy == "Remove":
        c_vals = [v for v in control if not math.isnan(v)]
        e_vals = [v for v in experiment if not math.isnan(v)]
    else:
        c_vals = [0.0 if math.isnan(v) else v for v in control]
        e_vals = [0.0 if math.isnan(v) else v for v in experiment]

    try:
        if not e_vals or not c_vals:
            if nan_strategy == "Remove":
                if must_have_data and not is_critical:
                    return {"name": name, "group": group, "classification": "NodataFailMetric", "critical": False}
                return {"name": name, "group": group, "classification": "Nodata", "critical": is_critical}
            # MannWhitneyClassifier.scala:161-163: silently returns Pass(critical=False)
            return {"name": name, "group": group, "classification": "Pass", "critical": False}

        if sorted(e_vals) == sorted(c_vals):
            return {"name": name, "group": group, "classification": "Pass", "critical": False}
        if len(set(e_vals).union(c_vals)) == 1:
            return {"name": name, "group": group, "classification": "Pass", "critical": False}

        e_work, c_work = list(e_vals), list(c_vals)
        if len(set(e_work)) == 1 and len(set(c_work)) == 1:
            gen = rng if rng is not None else random.Random(0)
            e_scale = e_work[0] * 1e-5
            c_scale = c_work[0] * 1e-5
            e_work = [v + gen.gauss(0.0, e_scale) for v in e_work]
            c_work = [v + gen.gauss(0.0, c_scale) for v in c_work]

        lo_ci, hi_ci, est = kayenta_mann_whitney_ci(e_work, c_work, conf_level=conf_level)
        eff = kayenta_mean_ratio(c_work, e_work)
        crit_val = tolerance * abs(est)
        lo_bound, hi_bound = -crit_val, crit_val

        is_high = (
            direction in ("increase", "either")
            and lo_ci > hi_bound
            and (True if math.isnan(eff) else eff >= allowed_thresholds[1])
        )
        is_low = (
            direction in ("decrease", "either")
            and hi_ci < lo_bound
            and (True if math.isnan(eff) else eff <= allowed_thresholds[0])
        )
        if is_high:
            cls = "High"
        elif is_low:
            cls = "Low"
        else:
            cls = "Pass"

        crit_high = is_critical and cls == "High" and (True if math.isnan(eff) else eff >= critical_thresholds[1])
        crit_low = is_critical and cls == "Low" and (True if math.isnan(eff) else eff <= critical_thresholds[0])
        out_crit = crit_high or crit_low
        return {
            "name": name,
            "group": group,
            "classification": cls,
            "critical": out_crit,
            "effect_size": eff,
            "ci": (lo_ci, hi_ci),
            "estimate": est,
        }
    except Exception:
        # NetflixACAJudge.scala:166-173 omits .critical(isCriticalMetric); defaults false (CanaryAnalysisResult.java:54)
        return {"name": name, "group": group, "classification": "Error", "critical": False}


def kayenta_weighted_sum_score(
    results: list[dict[str, Any]], group_weights: dict[str, float]
) -> tuple[float, str]:
    """Exact port of WeightedSumScorer.scala:27-106."""
    by_group: dict[str, list[str]] = {}
    for r in results:
        by_group.setdefault(r["group"], []).append(r["classification"])

    group_scores: list[tuple[str, float, bool]] = []
    for g in sorted(by_group):
        labels = by_group[g]
        n_pass = labels.count("Pass")
        n_high = labels.count("High")
        n_low = labels.count("Low")
        n_nodata_fail = labels.count("NodataFailMetric")
        # WeightedSumScorer.scala:37 excludes both Nodata and Error from numTotal
        n_total = n_high + n_low + n_pass + n_nodata_fail
        has_no_data = n_total == 0
        g_score = 0.0 if has_no_data else (n_pass / n_total) * 100.0
        group_scores.append((g, g_score, has_no_data))

    crit_failures = [r for r in results if r["critical"] and r["classification"] != "Pass"]
    if crit_failures:
        return 0.0, f"critical_failure:{crit_failures[0]['name']}"

    nodata_cnt = sum(1 for r in results if r["classification"] == "Nodata")
    if results and (nodata_cnt / len(results)) * 100.0 >= 50.0:
        return 0.0, "too_many_nodata"

    weight_sum = sum(group_weights.values())
    unweighted = [g for g, _, _ in group_scores if g not in group_weights]
    calc_weight = (100.0 - weight_sum) / len(unweighted) if unweighted else 0.0

    summary = 0.0
    for g, g_score, has_no_data in group_scores:
        # WeightedSumScorer.scala:71 awards 100.0 to any noData group
        eff_score = 100.0 if has_no_data else g_score
        w = group_weights.get(g, calc_weight)
        summary += eff_score * (w / 100.0)
    return round(summary, 2), "ok"


def sample_ar1(rng: random.Random, n: int, rho: float, mean: float = 100.0) -> list[float]:
    """Stationary unit-variance Gaussian AR(1) via Box-Muller pairs (pure stdlib, fast)."""
    rand = rng.random
    sqrt = math.sqrt
    log = math.log
    cos = math.cos
    sin = math.sin
    two_pi = 2.0 * math.pi
    out = [0.0] * n
    if rho == 0.0:
        i = 0
        while i + 1 < n:
            r = sqrt(-2.0 * log(1.0 - rand()))
            th = two_pi * rand()
            out[i] = mean + r * cos(th)
            out[i + 1] = mean + r * sin(th)
            i += 2
        if i < n:
            r = sqrt(-2.0 * log(1.0 - rand()))
            out[i] = mean + r * cos(two_pi * rand())
        return out
    scale = sqrt(1.0 - rho * rho)
    r0 = sqrt(-2.0 * log(1.0 - rand()))
    th0 = two_pi * rand()
    x = r0 * cos(th0)
    out[0] = mean + x
    if n == 1:
        return out
    x = rho * x + scale * (r0 * sin(th0))
    out[1] = mean + x
    i = 2
    while i + 1 < n:
        r = sqrt(-2.0 * log(1.0 - rand()))
        th = two_pi * rand()
        x = rho * x + scale * (r * cos(th))
        out[i] = mean + x
        x = rho * x + scale * (r * sin(th))
        out[i + 1] = mean + x
        i += 2
    if i < n:
        r = sqrt(-2.0 * log(1.0 - rand()))
        x = rho * x + scale * (r * cos(two_pi * rand()))
        out[i] = mean + x
    return out


def estimate_pooled_lag1_rho(c: list[float], e: list[float]) -> float:
    """Pooled sample lag-1 autocorrelation across two equal-length series, clamped to [0, 0.99]."""
    num = 0.0
    den = 0.0
    for seq in (c, e):
        n = len(seq)
        mu = sum(seq) / n
        prev = seq[0] - mu
        den += prev * prev
        for i in range(1, n):
            cur = seq[i] - mu
            den += cur * cur
            num += prev * cur
            prev = cur
    if den <= 0.0:
        return 0.0
    r = num / den
    if r <= 0.0:
        return 0.0
    return 0.99 if r > 0.99 else r


def holm_bonferroni_rejected_indices(pvals: list[float], alpha: float) -> set[int]:
    order = sorted(range(len(pvals)), key=pvals.__getitem__)
    m = len(order)
    rejected: set[int] = set()
    for rank, idx in enumerate(order):
        if pvals[idx] <= alpha / (m - rank):
            rejected.add(idx)
        else:
            break
    return rejected


def bh_any_reject(pvals: list[float], alpha: float) -> bool:
    sp = sorted(pvals)
    m = len(sp)
    return any(p <= alpha * (i + 1) / m for i, p in enumerate(sp))


def ar1_mw_vif(rho: float, n: int | None = None) -> float:
    """Gastwirth-Rubin (1975) rank-sum variance inflation for Gaussian AR(1); Bartlett-tapered for finite n."""
    if rho <= 0.0:
        return 1.0
    c = 6.0 / math.pi
    rk = rho
    acc = 0.0
    if n is None:
        for _ in range(1, 100):
            if rk < 1e-14:
                break
            acc += c * math.asin(0.5 * rk)
            rk *= rho
        return 1.0 + 2.0 * acc
    inv_n = 1.0 / n
    for k in range(1, n):
        if rk < 1e-10:
            break
        acc += (1.0 - k * inv_n) * c * math.asin(0.5 * rk)
        rk *= rho
    return 1.0 + 2.0 * acc


def max_mw_abs_z0(n: int) -> float:
    """Strict upper bound on Kayenta's |Z_0| at equal sample size n=m under complete separation."""
    num = (n * n) / 2.0 - 0.5
    den = math.sqrt((n * n * (2 * n + 1)) / 12.0)
    return num / den


def run_probe_1() -> None:
    print("=== PROBE 1: KAYENTA AUTOMATED CANARY ANALYSIS FORENSICS ===")
    print("Provenance: [source port] spinnaker/kayenta@5310ab7d + [derived analytical model] + [Monte Carlo simulation]")

    # 1A. Exact reproduction of live judge defects
    # Bug 1a: n=1 exact IEEE-754 ties (control=[0.0] vs [50.0]; and Sterbenz pair [10.0] vs [11.0])
    # deterministically throw sigmaCi==0 -> Error (critical=False) -> excluded from numTotal -> 100.00 score.
    n1_zero_errs = 0
    n1_sterbenz_errs = 0
    n1_exp_gap_highs = 0
    n1_exp_gap_errs = 0
    for seed in range(200):
        r0 = kayenta_classify_metric("err_rate", "core", [0.0], [50.0], is_critical=True, must_have_data=True, rng=random.Random(seed))
        if r0["classification"] == "Error" and r0["critical"] is False:
            n1_zero_errs += 1
        r_st = kayenta_classify_metric("err_st", "core", [10.0], [11.0], is_critical=True, must_have_data=True, rng=random.Random(seed))
        if r_st["classification"] == "Error" and r_st["critical"] is False:
            n1_sterbenz_errs += 1
        r_gap = kayenta_classify_metric("err_gap", "core", [1.0], [50.0], is_critical=True, must_have_data=True, rng=random.Random(seed))
        if r_gap["classification"] == "High" and r_gap["critical"] is True:
            n1_exp_gap_highs += 1
        elif r_gap["classification"] == "Error" and r_gap["critical"] is False:
            n1_exp_gap_errs += 1

    r_n1_err = kayenta_classify_metric("err_rate", "core", [0.0], [50.0], is_critical=True, must_have_data=True, rng=random.Random(0))
    score_n1_err, reason_n1_err = kayenta_weighted_sum_score([r_n1_err], {"core": 100.0})
    assert n1_zero_errs == 200 and n1_sterbenz_errs == 200
    assert score_n1_err == 100.0 and reason_n1_err == "ok"

    # Bug 1b: n=1 with 5-bit binary exponent gap (control=[1.0], experiment=[50.0]) causes
    # cancellation rounding (up to 0.5 ULP of 50.0 / 16 ULP of 1.0) after addGaussianNoise,
    # stochastically breaking the tie -> findRoot(-zQuant) clamps to muMin and findRoot(zQuant)
    # clamps to muMax (equal at n=1) -> zero-width 98% CI -> High (Critical) at exact p=1.0.
    r_n1_gap = kayenta_classify_metric("err_gap", "core", [1.0], [50.0], is_critical=True, must_have_data=True, rng=random.Random(0))
    assert r_n1_gap["classification"] == "High" and r_n1_gap["critical"] is True
    assert r_n1_gap["ci"][0] == r_n1_gap["ci"][1]
    assert n1_exp_gap_highs + n1_exp_gap_errs == 200 and n1_exp_gap_highs > 170 and n1_exp_gap_errs > 0

    # Bug 2: meanRatio=NaN bypasses allowedIncrease=2.0 and criticalIncrease=5.0
    r_nan_es = kayenta_classify_metric(
        "zero_base_err",
        "core",
        control=[0.0] * 20,
        experiment=[0.001 + 1e-4 * (i % 5) for i in range(20)],
        direction="increase",
        is_critical=True,
        allowed_thresholds=(0.5, 2.0),
        critical_thresholds=(0.2, 5.0),
        rng=random.Random(101),
    )
    score_nan_es, reason_nan_es = kayenta_weighted_sum_score([r_nan_es], {"core": 100.0})
    assert math.isnan(r_nan_es["effect_size"])
    assert r_nan_es["classification"] == "High" and r_nan_es["critical"] is True
    assert score_nan_es == 0.0 and reason_nan_es == "critical_failure:zero_base_err"

    # Bug 3: nanStrategy="none" parses to Remove (fails closed), while explicit "replace" returns Pass
    r_empty_default = kayenta_classify_metric(
        "lat_p99", "core", control=[10.0, 11.0, 12.0], experiment=[],
        nan_strategy_str="none", is_critical=True, must_have_data=True,
    )
    score_empty_default, _ = kayenta_weighted_sum_score([r_empty_default], {"core": 100.0})
    assert r_empty_default["classification"] == "Nodata" and r_empty_default["critical"] is True
    assert score_empty_default == 0.0

    r_empty_replace = kayenta_classify_metric(
        "lat_p99", "core", control=[10.0, 11.0, 12.0], experiment=[],
        nan_strategy_str="replace", is_critical=True, must_have_data=True,
    )
    score_empty_replace, _ = kayenta_weighted_sum_score([r_empty_replace], {"core": 100.0})
    assert r_empty_replace["classification"] == "Pass" and r_empty_replace["critical"] is False
    assert score_empty_replace == 100.0

    # Bug 4: All-Nodata group awarded 100.0 when global Nodata < 50%
    r_ok1 = {"name": "m1", "group": "app", "classification": "Pass", "critical": False}
    r_ok2 = {"name": "m2", "group": "app", "classification": "Pass", "critical": False}
    r_nd = {"name": "m3", "group": "db", "classification": "Nodata", "critical": False}
    score_nd_grp, reason_nd_grp = kayenta_weighted_sum_score([r_ok1, r_ok2, r_nd], {"app": 50.0, "db": 50.0})
    assert score_nd_grp == 100.0 and reason_nd_grp == "ok"

    print(
        f"  [source port] n=1 exact ties (c=[0],e=[50]: {n1_zero_errs}/200 Error; "
        f"Sterbenz c=[10],e=[11]: {n1_sterbenz_errs}/200 Error): critical=False, score={score_n1_err:.2f}"
    )
    print(
        f"  [source port] n=1 exponent-gap rounding (c=[1],e=[50], 200 seeds): "
        f"High(Critical)={n1_exp_gap_highs}/200 ({n1_exp_gap_highs/2:.1f}%), "
        f"Error={n1_exp_gap_errs}/200 ({n1_exp_gap_errs/2:.1f}%), seed0 ci_width={r_n1_gap['ci'][1]-r_n1_gap['ci'][0]:.1f}"
    )
    print(
        f"  [source port] meanRatio=NaN bypass: eff={r_nan_es['effect_size']}, "
        f"cls={r_nan_es['classification']}, critical={r_nan_es['critical']}, score={score_nan_es:.2f}"
    )
    print(
        f"  [source port] empty series nanStrategy='none'(->Remove): cls={r_empty_default['classification']}, "
        f"critical={r_empty_default['critical']}, score={score_empty_default:.2f}"
    )
    print(
        f"  [source port] empty series nanStrategy='replace': cls={r_empty_replace['classification']}, "
        f"critical={r_empty_replace['critical']}, score={score_empty_replace:.2f}"
    )
    print(f"  [source port] all-Nodata group (33.3% global < 50%): weighted_score={score_nd_grp:.2f}")

    # 1B. Analytical tolerance=0.25 effective alpha & AR(1) minimum feasible sample size bound
    z_01 = abs(norm_ppf(0.01))
    z_eff_iid = z_01 / 0.75
    alpha_eff_iid = 2.0 * (1.0 - norm_cdf(z_eff_iid))
    fwer_naive_50 = 1.0 - (1.0 - 0.02) ** 50
    fwer_tol25_iid_50 = 1.0 - (1.0 - alpha_eff_iid) ** 50
    assert abs(alpha_eff_iid - 0.0019235) < 1e-5
    assert fwer_tol25_iid_50 < 0.10 and fwer_naive_50 > 0.63

    m_suite = 50
    alpha_suite = 0.02
    bonf_thresh = alpha_suite / m_suite  # 0.0004
    z0_max_40 = max_mw_abs_z0(40)
    vif_40_08 = ar1_mw_vif(0.8, 40)
    zcorr_max_40 = z0_max_40 / math.sqrt(vif_40_08)
    p_min_40 = 2.0 * (1.0 - norm_cdf(zcorr_max_40))
    assert p_min_40 > bonf_thresh  # Proves n=40 is mathematically vacuous (0 power even under complete separation)

    n_min_feasible = next(
        n for n in range(2, 500)
        if 2.0 * (1.0 - norm_cdf(max_mw_abs_z0(n) / math.sqrt(ar1_mw_vif(0.8, n)))) <= bonf_thresh
    )
    assert n_min_feasible == 69
    zcorr_max_69 = max_mw_abs_z0(n_min_feasible) / math.sqrt(ar1_mw_vif(0.8, n_min_feasible))
    p_min_69 = 2.0 * (1.0 - norm_cdf(zcorr_max_69))

    print(f"  [analytical] z_0.01={z_01:.4f}, tol=0.25 effective |Z|={z_eff_iid:.4f} -> alpha_eff_iid={alpha_eff_iid:.5f}")
    print(f"  [analytical] M=50 critical i.i.d. FWER: naive(alpha=0.02)={fwer_naive_50:.4f} vs Kayenta(tol=0.25)={fwer_tol25_iid_50:.4f}")
    print(
        f"  [analytical] VIF+Holm feasibility (rho=0.8, M={m_suite}, alpha={alpha_suite}, alpha/M={bonf_thresh:.6f}): "
        f"n=40 max |Z0|={z0_max_40:.4f}, VIF={vif_40_08:.4f}, max |Z_corr|={zcorr_max_40:.4f} -> "
        f"p_min={p_min_40:.6f} > alpha/M (VACUOUS); min feasible n={n_min_feasible} (p_min={p_min_69:.6f})"
    )

    # 1C. Monte Carlo simulation of exact Kayenta MannWhitneyClassifier under AR(1) (n=40, R=350, seed=202601)
    rng_sim = random.Random(202601)
    n_obs_40 = 40
    n_trials = 350
    sim_fpr: dict[float, float] = {}
    for rho in (0.0, 0.5, 0.8):
        vif_mw = ar1_mw_vif(rho, n_obs_40)
        alpha_pred = 2.0 * (1.0 - norm_cdf(z_eff_iid / math.sqrt(vif_mw)))
        rejects = 0
        for _ in range(n_trials):
            c = sample_ar1(rng_sim, n_obs_40, rho, mean=100.0)
            e = sample_ar1(rng_sim, n_obs_40, rho, mean=100.0)
            res = kayenta_classify_metric("m", "g", c, e, is_critical=True, tolerance=0.25, conf_level=0.98)
            if res["classification"] != "Pass":
                rejects += 1
        emp_fpr = rejects / n_trials
        se_fpr = math.sqrt(emp_fpr * (1.0 - emp_fpr) / n_trials)
        sim_fpr[rho] = emp_fpr
        emp_fwer_50 = 1.0 - (1.0 - emp_fpr) ** 50
        pred_fwer_50 = 1.0 - (1.0 - alpha_pred) ** 50
        print(
            f"  [Monte Carlo] Kayenta AR(1) rho={rho:.1f} (n={n_obs_40}, R={n_trials}, seed=202601): "
            f"VIF_mw={vif_mw:.2f}, sim_FPR={emp_fpr:.4f}+/-{se_fpr:.4f} (pred={alpha_pred:.4f}), "
            f"M=50 FWER implied={emp_fwer_50:.4f} (pred={pred_fwer_50:.4f})"
        )
    assert sim_fpr[0.0] <= 0.015
    assert sim_fpr[0.8] > 0.22

    # 1D. Feasible-horizon (n=150) M=50 suite: Null FWER + Non-Vacuity Outage Power + Oracle vs Plug-in rho_hat
    n_feasible = 150
    r_suites = 80
    zcorr_max_feas = max_mw_abs_z0(n_feasible) / math.sqrt(ar1_mw_vif(0.8, n_feasible))
    p_min_feas = 2.0 * (1.0 - norm_cdf(zcorr_max_feas))
    assert p_min_feas < 1e-6

    rng_mt = random.Random(202602)
    for rho in (0.0, 0.8):
        raw_hits = 0
        holm_hits = 0
        bh_hits = 0
        vif_oracle_holm_hits = 0
        vif_plugin_holm_hits = 0
        vif_oracle = ar1_mw_vif(rho, n_feasible)
        rho_hat_sum = 0.0
        for _ in range(r_suites):
            pvals = []
            pvals_oracle = []
            pvals_plugin = []
            for _ in range(m_suite):
                c = sample_ar1(rng_mt, n_feasible, rho, mean=100.0)
                e = sample_ar1(rng_mt, n_feasible, rho, mean=100.0)
                z0 = kayenta_wilcoxon_diff(0.0, 0.0, e, c)
                rho_hat = estimate_pooled_lag1_rho(c, e)
                rho_hat_sum += rho_hat
                vif_hat = ar1_mw_vif(rho_hat, n_feasible)
                pvals.append(2.0 * (1.0 - norm_cdf(abs(z0))))
                pvals_oracle.append(2.0 * (1.0 - norm_cdf(abs(z0) / math.sqrt(vif_oracle))))
                pvals_plugin.append(2.0 * (1.0 - norm_cdf(abs(z0) / math.sqrt(vif_hat))))
            if any(p <= alpha_suite for p in pvals):
                raw_hits += 1
            if holm_bonferroni_rejected_indices(pvals, alpha_suite):
                holm_hits += 1
            if bh_any_reject(pvals, alpha_suite):
                bh_hits += 1
            if holm_bonferroni_rejected_indices(pvals_oracle, alpha_suite):
                vif_oracle_holm_hits += 1
            if holm_bonferroni_rejected_indices(pvals_plugin, alpha_suite):
                vif_plugin_holm_hits += 1
        mean_rho_hat = rho_hat_sum / (r_suites * m_suite)
        print(
            f"  [Monte Carlo] M={m_suite} NULL FWER (n={n_feasible}, rho={rho:.1f}, R={r_suites}, alpha={alpha_suite}): "
            f"uncorr={raw_hits/r_suites:.3f}, Holm={holm_hits/r_suites:.3f}, BH={bh_hits/r_suites:.3f}, "
            f"VIF(oracle)+Holm={vif_oracle_holm_hits/r_suites:.3f}, VIF(plugin)+Holm={vif_plugin_holm_hits/r_suites:.3f} "
            f"(mean rho_hat={mean_rho_hat:.3f})"
        )
        if rho == 0.0:
            assert raw_hits / r_suites > 0.50
            assert holm_hits / r_suites <= 0.06
        else:
            assert holm_hits / r_suites > 0.80
            assert vif_oracle_holm_hits / r_suites <= 0.05

    # Non-vacuity outage power check at n=150, rho=0.8, M=50, alpha=0.02:
    # Metric 0 suffers a genuine +3.0 stationary-SD outage shift; metrics 1..49 remain null.
    rng_pwr = random.Random(202603)
    r_power = 40
    shift_sd = 3.0
    vif_08_150 = ar1_mw_vif(0.8, n_feasible)
    oracle_target_tp = 0
    plugin_target_tp = 0
    oracle_null_fp_suites = 0
    for _ in range(r_power):
        pvals_oracle = []
        pvals_plugin = []
        for idx in range(m_suite):
            c = sample_ar1(rng_pwr, n_feasible, 0.8, mean=100.0)
            e = sample_ar1(rng_pwr, n_feasible, 0.8, mean=100.0 + (shift_sd if idx == 0 else 0.0))
            z0 = kayenta_wilcoxon_diff(0.0, 0.0, e, c)
            rho_hat = estimate_pooled_lag1_rho(c, e)
            vif_hat = ar1_mw_vif(rho_hat, n_feasible)
            pvals_oracle.append(2.0 * (1.0 - norm_cdf(abs(z0) / math.sqrt(vif_08_150))))
            pvals_plugin.append(2.0 * (1.0 - norm_cdf(abs(z0) / math.sqrt(vif_hat))))
        rej_oracle = holm_bonferroni_rejected_indices(pvals_oracle, alpha_suite)
        rej_plugin = holm_bonferroni_rejected_indices(pvals_plugin, alpha_suite)
        if 0 in rej_oracle:
            oracle_target_tp += 1
        if 0 in rej_plugin:
            plugin_target_tp += 1
        if any(i != 0 for i in rej_oracle):
            oracle_null_fp_suites += 1
    tpr_oracle = oracle_target_tp / r_power
    tpr_plugin = plugin_target_tp / r_power
    assert tpr_oracle >= 0.85 and tpr_plugin >= 0.85
    print(
        f"  [Monte Carlo] M={m_suite} POWER CHECK (n={n_feasible}, rho=0.8, 1 metric +{shift_sd:.1f}SD, R={r_power}): "
        f"VIF(oracle)+Holm TPR={tpr_oracle:.3f} (null_metric_FP={oracle_null_fp_suites/r_power:.3f}), "
        f"VIF(plugin)+Holm TPR={tpr_plugin:.3f} (p_min={p_min_feas:.2e})"
    )


# =============================================================================
# PROBE 2: Google SRE Workbook Chapter 5 Burn-Rate Alerting
# =============================================================================

def exact_thinned_poisson_burn_fire_prob(
    qps: float, p_nom: float, w_short_s: float, w_long_s: float, r_burn: float
) -> float:
    """
    Exact joint false-fire probability under true thinned homogeneous Poisson arrivals:
      E_S ~ Pois(p * qps * w_short_s),      G_S ~ Pois((1-p) * qps * w_short_s)
      E_prev ~ Pois(p * qps * w_prev_s),    G_prev ~ Pois((1-p) * qps * w_prev_s)
    Fires iff E_S / (E_S + G_S) > r_burn * p_nom AND
              (E_S + E_prev) / (E_S + G_S + E_prev + G_prev) > r_burn * p_nom
    with exact rational threshold theta = num/den (zero float boundary drift).
    """
    # Exact rational threshold for r_burn=14.4, p_nom=0.001 -> 0.0144 = 144 / 10000
    theta_num = int(round(r_burn * p_nom * 1_000_000))
    theta_den = 1_000_000
    rem_num = theta_den - theta_num  # 1 - theta

    def max_good_strict(k_err: int) -> int:
        # Strict inequality: k_err / (k_err + g) > theta_num / theta_den
        # <=> k_err * rem_num > theta_num * g <=> g <= (k_err * rem_num - 1) // theta_num
        if k_err <= 0:
            return -1
        return (k_err * rem_num - 1) // theta_num

    lam_s = qps * w_short_s
    lam_prev = qps * (w_long_s - w_short_s)
    mu_es = p_nom * lam_s
    mu_ep = p_nom * lam_prev
    mu_gs = (1.0 - p_nom) * lam_s
    mu_gp = (1.0 - p_nom) * lam_prev

    # Active support of G_S and G_prev (12 sigma window covers > 1 - 1e-30 of Poisson mass)
    gs_lo = max(0, int(math.floor(mu_gs - 12.0 * math.sqrt(mu_gs + 1.0) - 20)))
    gs_hi = int(math.ceil(mu_gs + 12.0 * math.sqrt(mu_gs + 1.0) + 20))
    gp_hi = int(math.ceil(mu_gp + 12.0 * math.sqrt(mu_gp + 1.0) + 20))

    gs_pmf = [(g, poisson_pmf(g, mu_gs)) for g in range(gs_lo, gs_hi + 1)]
    gs_pmf = [(g, p) for g, p in gs_pmf if p > 0.0]
    gp_cdf = poisson_cdf_table(mu_gp, gp_hi)

    def prob_gp_le(m: int) -> float:
        if m < 0:
            return 0.0
        if m >= gp_hi:
            return 1.0
        return gp_cdf[m]

    # Precompute E_prev PMF on active support + upper tail sufficient for joint event
    ep_max = max(30, int(math.ceil(mu_ep + 18.0 * math.sqrt(mu_ep + 1.0) + 80)))
    es_max = max(25, int(math.ceil(mu_es + 18.0 * math.sqrt(mu_es + 1.0) + 60)))
    ep_pmf = [(kp, poisson_pmf(kp, mu_ep)) for kp in range(0, ep_max + 1)]
    ep_pmf = [(kp, p) for kp, p in ep_pmf if p > 0.0]

    # Cache P(G_S <= ms AND G_S + G_prev <= ml) keyed by (min(ms, gs_hi), min(ml, gs_hi + gp_hi))
    good_cache: dict[tuple[int, int], float] = {}

    def prob_good(ms: int, ml: int) -> float:
        if ms < 0 or ml < 0:
            return 0.0
        ms_c = min(ms, gs_hi)
        ml_c = min(ml, gs_hi + gp_hi)
        key = (ms_c, ml_c)
        cached = good_cache.get(key)
        if cached is not None:
            return cached
        limit_gs = min(ms_c, ml_c)
        acc = 0.0
        for g, pg in gs_pmf:
            if g > limit_gs:
                break
            acc += pg * prob_gp_le(ml_c - g)
        good_cache[key] = acc
        return acc

    total = 0.0
    for ks in range(1, es_max + 1):
        p_ks = poisson_pmf(ks, mu_es)
        if p_ks == 0.0:
            continue
        ms = max_good_strict(ks)
        if ms < gs_lo:
            continue
        row = 0.0
        for kp, p_kp in ep_pmf:
            ml = max_good_strict(ks + kp)
            if ml < gs_lo:
                continue
            pg = prob_good(ms, ml)
            if pg > 0.0:
                row += p_kp * pg
        term = p_ks * row
        total += term
    return total


def run_probe_2() -> None:
    print("\n=== PROBE 2: GOOGLE SRE WORKBOOK CH. 5 BURN-RATE CONTROL LAWS ===")
    print("Provenance: [published rules calculation] Google SRE Workbook Ch. 5 + [derived analytical model]")

    slo = 0.999
    err_budget = 1.0 - slo  # 0.001
    period_min = 30.0 * 24.0 * 60.0  # 43,200 min
    budget_100pct_min = period_min * err_budget  # 43.2 min

    def burn_metrics(w_long_m: float, w_short_m: float | None, r: float, e: float) -> tuple[float, float]:
        thresh = r * err_budget
        if e <= thresh:
            return math.inf, math.inf
        t_det = w_long_m * thresh / e
        if w_short_m is not None:
            t_det = max(t_det, w_short_m * thresh / e)
        pct_budget = 100.0 * (e * t_det) / budget_100pct_min
        return t_det, pct_budget

    # Strategy 1: 10m >= 0.1%
    t1_100, _ = burn_metrics(10.0, None, 1.0, 1.0)
    b1_01_10m = 100.0 * (0.001 * 10.0) / budget_100pct_min
    assert abs(t1_100 * 60.0 - 0.6) < 1e-9
    assert abs(b1_01_10m - (100.0 / 4320.0)) < 1e-9

    # Strategy 2: 36h > 0.1%
    t2_100, _ = burn_metrics(36.0 * 60.0, None, 1.0, 1.0)
    assert abs(t2_100 * 60.0 - 129.6) < 1e-9

    # Strategy 3: Duration clause (1m > 0.1% for: 1h; Fig 5-3 flapping)
    b3_100_1h = 100.0 * (1.0 * 60.0) / budget_100pct_min
    assert abs(b3_100_1h - 138.8888888889) < 1e-6

    sim_secs = 30 * 60
    win_5m = 5 * 60
    dur_10m = 10 * 60
    err_stream = [1.0 if (t % 600) < 300 else 0.0 for t in range(sim_secs)]
    above_streak = 0
    max_streak = 0
    fired_dur = False
    running_sum = 0.0
    for t in range(sim_secs):
        running_sum += err_stream[t]
        if t >= win_5m:
            running_sum -= err_stream[t - win_5m]
        if running_sum / win_5m > err_budget:
            above_streak += 1
            if above_streak > max_streak:
                max_streak = above_streak
            if above_streak >= dur_10m:
                fired_dur = True
        else:
            above_streak = 0
    fig53_budget_pct = 100.0 * (sum(err_stream) / 60.0) / budget_100pct_min
    assert fired_dur is False and max_streak == 599
    assert abs(fig53_budget_pct - 34.7222222) < 1e-4

    # Strategy 4: Single burn rate 1h @ 36x
    t4_100, b4_100 = burn_metrics(60.0, None, 36.0, 1.0)
    t4_35x, _ = burn_metrics(60.0, None, 36.0, 35.0 * err_budget)
    exhaust_35x_h = 720.0 / 35.0
    assert abs(b4_100 - 5.0) < 1e-9
    assert math.isinf(t4_35x) and abs(exhaust_35x_h - 20.5714285) < 1e-4

    # Strategy 5 & 6: Table 5-8 multi-window multi-burn-rate
    rules_t58 = [
        ("Page-Fast (1h/5m @ 14.4x)", 60.0, 5.0, 14.4),
        ("Page-Med  (6h/30m @ 6.0x)", 360.0, 30.0, 6.0),
        ("Ticket-24h(24h/2h @ 3.0x)", 1440.0, 120.0, 3.0),
        ("Ticket-3d (3d/6h  @ 1.0x)", 4320.0, 360.0, 1.0),
    ]
    print(f"  [published rules] 10m>=0.1%: t_det(100%)={t1_100*60:.1f}s, 0.1%/10m budget={b1_01_10m:.4f}% (144 pages/day)")
    print(f"  [published rules] 36h>0.1%:  t_det(100%)={t2_100*60:.1f}s (2m10s), reset=36.0h")
    print(f"  [published rules] 1m>0.1% for 1h: t_det(100%)=60.0m, budget_burned={b3_100_1h:.2f}%")
    print(f"  [published rules] Fig 5-3 flapping (5m-on/5m-off, for:10m): fired={fired_dur}, max_streak={max_streak}s/600s, budget_burned={fig53_budget_pct:.2f}%")
    print(f"  [published rules] 1h@36x single-burn: t_det(100%)={t4_100:.2f}m, 35x_blind=True (exhausts in {exhaust_35x_h:.2f}h)")

    for label, wl, ws, r in rules_t58:
        td100, b100 = burn_metrics(wl, ws, r, 1.0)
        td35, _ = burn_metrics(wl, ws, r, 35.0 * err_budget)
        if wl == 60.0:
            e_burst = 0.15
            t_fire = 60.0 * (r * err_budget) / e_burst
            reset_short = ws * (1.0 - (r * err_budget) / e_burst)
            reset_long = wl * (1.0 - (r * err_budget) / e_burst)
            assert abs(t_fire - 5.76) < 1e-9
            assert abs(reset_short - 4.52) < 1e-9
            assert abs(reset_long - 54.24) < 1e-9
            assert abs(reset_long / reset_short - 12.0) < 1e-9
            print(
                f"  [published rules] {label}: budget={b100:.1f}%, t_det(100%)={td100*60:.1f}s, "
                f"t_det(35x)={td35:.2f}m, Fig5-6(15%/10m): fire={t_fire:.2f}m, "
                f"reset_short={reset_short:.2f}m vs reset_long={reset_long:.2f}m (12.0x faster)"
            )
        else:
            td35_s = f"{td35:.1f}m" if math.isfinite(td35) else "inf"
            print(f"  [published rules] {label}: budget={b100:.1f}%, t_det(100%)={td100*60:.1f}s, t_det(35x)={td35_s}")

    # 2B. Low-traffic erratum + Exact Thinned Homogeneous Poisson vs. Fixed-Denominator Comparison
    single_err_burn = (1.0 / 10.0) / err_budget
    single_err_budget_pct = 100.0 * (1.0 / (10.0 * 24.0 * 30.0 * err_budget))
    assert abs(single_err_burn - 100.0) < 1e-9
    assert abs(single_err_budget_pct - 13.8888889) < 1e-5
    print(f"  [published rules] Low-traffic 10 req/hr, 1 error: burn={single_err_burn:.0f}x (published text typo: 1000x), budget={single_err_budget_pct:.2f}%")

    r_fast = 14.4
    p_nom = err_budget
    thinned_probs: dict[float, float] = {}
    fixed_probs: dict[float, float] = {}
    for qps in (0.01, 0.05, 0.10, 1.00):
        # Fixed deterministic denominator (N_S, N_L fixed; only error counts Poisson)
        n_s = qps * 300.0
        n_l = qps * 3600.0
        mu_s = p_nom * n_s
        mu_prev = p_nom * (n_l - n_s)
        th_s = r_fast * p_nom * n_s
        th_l = r_fast * p_nom * n_l
        k_s_min = int(math.floor(th_s)) + 1
        p_fixed = 0.0
        ks = k_s_min
        while True:
            p_ks = poisson_pmf(ks, mu_s)
            p_prev = poisson_sf_strict(th_l - ks, mu_prev)
            term = p_ks * p_prev
            p_fixed += term
            if ks > max(k_s_min + 20, int(th_l) + 5) and (term == 0.0 or (p_fixed > 0.0 and term < p_fixed * 1e-16)):
                break
            ks += 1
            if ks > k_s_min + 1000:
                break
        fixed_probs[qps] = p_fixed

        # True thinned homogeneous Poisson arrivals (both errors and good requests random)
        p_thinned = exact_thinned_poisson_burn_fire_prob(qps, p_nom, 300.0, 3600.0, r_fast)
        thinned_probs[qps] = p_thinned
        ratio = p_thinned / p_fixed if p_fixed > 0.0 else math.nan
        exp_win_thinned = p_thinned * (30 * 24 * 12)
        print(
            f"  [analytical] 1h/5m@14.4x false-fire @ QPS={qps:4.2f}: "
            f"thinned_Pois={p_thinned:.3e} (E[5m-win/30d]={exp_win_thinned:.3e}) vs "
            f"fixed_N={p_fixed:.3e} (ratio={ratio:.2f}x)"
        )

    assert abs(thinned_probs[0.01] - 2.996e-3) / 2.996e-3 < 1e-3
    assert abs(thinned_probs[0.05] - 1.930e-4) / 1.930e-4 < 2e-3
    assert abs(thinned_probs[0.10] - 3.182e-6) / 3.182e-6 < 2e-3
    assert abs((thinned_probs[0.10] / fixed_probs[0.10]) - 3.50) < 0.05
    assert thinned_probs[1.00] < 1e-35 and thinned_probs[1.00] > fixed_probs[1.00]
    assert thinned_probs[0.01] > thinned_probs[0.05] > thinned_probs[0.10] > thinned_probs[1.00]


# =============================================================================
# PROBE 3: argoproj/argo-rollouts@8c9c5ad2
# =============================================================================

@dataclass
class ArgoMetricSpec:
    name: str
    count: int | None = None
    failure_limit: int | None = None
    inconclusive_limit: int | None = None
    consecutive_error_limit: int | None = None
    consecutive_success_limit: int | None = None


@dataclass
class ArgoMetricResult:
    phase: str = "Pending"
    count: int = 0
    successful: int = 0
    failed: int = 0
    inconclusive: int = 0
    error: int = 0
    consecutive_error: int = 0
    consecutive_success: int = 0
    measurements: list[str] | None = None

    def __post_init__(self) -> None:
        if self.measurements is None:
            self.measurements = []


ARGO_COMPLETED = {"Successful", "Failed", "Inconclusive", "Error"}
ARGO_DEFAULT_CONSECUTIVE_ERROR_LIMIT = 4  # utils/defaults/defaults.go:37


def argo_assess_failure_inconclusive_or_error(
    spec: ArgoMetricSpec, res: ArgoMetricResult
) -> tuple[str, str]:
    """Exact port of analysis/analysis.go:702-731 (sequential non-exclusive ifs)."""
    phase = ""
    msg = ""

    failure_limit = 0 if spec.failure_limit is None else spec.failure_limit
    if failure_limit >= 0 and res.failed > failure_limit:
        phase = "Failed"
        msg = f"failed ({res.failed}) > failureLimit ({failure_limit})"

    inconclusive_limit = 0 if spec.inconclusive_limit is None else spec.inconclusive_limit
    if res.inconclusive > inconclusive_limit:
        phase = "Inconclusive"
        msg = f"inconclusive ({res.inconclusive}) > inconclusiveLimit ({inconclusive_limit})"

    consec_err_limit = (
        ARGO_DEFAULT_CONSECUTIVE_ERROR_LIMIT
        if spec.consecutive_error_limit is None
        else spec.consecutive_error_limit
    )
    if res.consecutive_error > consec_err_limit:
        phase = "Error"
        msg = f"consecutiveErrors ({res.consecutive_error}) > consecutiveErrorLimit ({consec_err_limit})"

    return phase, msg


def argo_assess_metric_status(spec: ArgoMetricSpec, res: ArgoMetricResult, terminating: bool = False) -> str:
    """Exact port of analysis/analysis.go:623-700."""
    if res.phase in ARGO_COMPLETED:
        return res.phase
    if not res.measurements:
        return "Successful" if terminating else "Pending"
    if res.measurements[-1] not in ARGO_COMPLETED:
        return "Running"

    phase_fie, _ = argo_assess_failure_inconclusive_or_error(spec, res)
    if phase_fie != "":
        return phase_fie

    if spec.consecutive_success_limit is not None and spec.consecutive_success_limit > 0:
        if res.consecutive_success >= spec.consecutive_success_limit:
            return "Successful"

    eff_count = spec.count
    if eff_count is not None and res.count >= eff_count:
        failure_applicable = (spec.failure_limit is None) or (spec.failure_limit >= 0)
        success_applicable = (spec.consecutive_success_limit is not None) and (spec.consecutive_success_limit > 0)
        if failure_applicable and success_applicable:
            return "Inconclusive"
        if success_applicable:
            return "Failed"
        return "Successful"

    return "Successful" if terminating else "Running"


def argo_step_measurement(spec: ArgoMetricSpec, res: ArgoMetricResult, meas_phase: str) -> str:
    """Exact port of analysis/analysis.go:429-451 + 520-535."""
    if res.phase in ARGO_COMPLETED:
        return res.phase
    assert res.measurements is not None
    res.measurements.append(meas_phase)
    if meas_phase == "Successful":
        res.successful += 1
        res.count += 1
        res.consecutive_error = 0
        res.consecutive_success += 1
    elif meas_phase == "Failed":
        res.failed += 1
        res.count += 1
        res.consecutive_error = 0
        res.consecutive_success = 0
    elif meas_phase == "Inconclusive":
        res.inconclusive += 1
        res.count += 1
        res.consecutive_error = 0
        res.consecutive_success = 0
    elif meas_phase == "Error":
        res.error += 1
        res.consecutive_error += 1
        res.consecutive_success = 0
        # analysis/analysis.go:445-449 does NOT increment res.count
    res.phase = argo_assess_metric_status(spec, res)
    return res.phase


def argo_rollout_action(run_phase: str) -> str:
    """Exact port of rollout/analysis.go:376-385, 434-443."""
    if run_phase == "Inconclusive":
        return "PauseReasonInconclusiveAnalysis"
    if run_phase in ("Failed", "Error"):
        return "AddAbort"
    if run_phase == "Successful":
        return "Promote"
    return "Continue"


def run_probe_3() -> None:
    print("\n=== PROBE 3: ARGO ROLLOUTS ANALYSISRUN CONTROL-LAW FORENSICS ===")
    print("Provenance: [source port] argoproj/argo-rollouts@8c9c5ad2 + [derived analytical model]")

    # 3A. Sequential non-exclusive if overwrite (analysis/analysis.go:711-729)
    spec_ow = ArgoMetricSpec("m", failure_limit=1, inconclusive_limit=0, consecutive_error_limit=4)
    res_ow_fi = ArgoMetricResult(failed=2, inconclusive=1, consecutive_error=0)
    ph_fi, _ = argo_assess_failure_inconclusive_or_error(spec_ow, res_ow_fi)
    assert ph_fi == "Inconclusive" and argo_rollout_action(ph_fi) == "PauseReasonInconclusiveAnalysis"

    res_ow_fie = ArgoMetricResult(failed=2, inconclusive=1, consecutive_error=5)
    ph_fie, _ = argo_assess_failure_inconclusive_or_error(spec_ow, res_ow_fie)
    assert ph_fie == "Error" and argo_rollout_action(ph_fie) == "AddAbort"
    print(f"  [source port] sequential-if overwrite: (F=2>1,I=1>0)->{ph_fi} ({argo_rollout_action(ph_fi)}); (+E=5>4)->{ph_fie}")

    # 3B. Resetting ConsecutiveError & non-incrementing Count -> 80% error provider never errors out
    spec_err = ArgoMetricSpec("flaky", count=50, failure_limit=0, consecutive_error_limit=4)
    res_err = ArgoMetricResult()
    for _ in range(50):
        for _ in range(4):
            argo_step_measurement(spec_err, res_err, "Error")
        argo_step_measurement(spec_err, res_err, "Successful")
    assert res_err.phase == "Successful"
    assert res_err.error == 200 and res_err.count == 50 and res_err.measurements is not None and len(res_err.measurements) == 250
    print(
        f"  [source port] 4-Error+1-Success cycle (count=50): total_polls={len(res_err.measurements)}, "
        f"errors={res_err.error}, count={res_err.count}, phase={res_err.phase}"
    )

    # 3C. ConsecutiveSuccessLimit + finite Count -> Inconclusive pause + RunSummary miscount (L541-567)
    spec_cs = ArgoMetricSpec("borderline", count=6, failure_limit=3, inconclusive_limit=1, consecutive_success_limit=4)
    res_cs = ArgoMetricResult()
    for m in ["Successful", "Successful", "Failed", "Successful", "Successful", "Failed"]:
        argo_step_measurement(spec_cs, res_cs, m)
    assert res_cs.phase == "Inconclusive"
    summary_phase, _ = argo_assess_failure_inconclusive_or_error(spec_cs, res_cs)
    summary_bucket = summary_phase if summary_phase in ARGO_COMPLETED else "Successful"  # L564-566 default
    assert summary_phase == "" and summary_bucket == "Successful"
    print(
        f"  [source port] ConsecutiveSuccessLimit unmet at count=6: phase={res_cs.phase}, "
        f"action={argo_rollout_action(res_cs.phase)}, RunSummary_bucket={summary_bucket}"
    )

    # 3D. Exact binomial false-abort inflation across N=60 background polls (alpha=0.02)
    def binom_false_abort(n: int, f_lim: int, alpha: float) -> float:
        return sum(math.comb(n, k) * (alpha ** k) * ((1.0 - alpha) ** (n - k)) for k in range(f_lim + 1, n + 1))

    fa_0 = binom_false_abort(60, 0, 0.02)
    fa_1 = binom_false_abort(60, 1, 0.02)
    fa_2 = binom_false_abort(60, 2, 0.02)
    fa_3 = binom_false_abort(60, 3, 0.02)
    assert abs(fa_0 - (1.0 - 0.98 ** 60)) < 1e-12 and abs(fa_0 - 0.702446) < 1e-4
    print(f"  [analytical] Background N=60, alpha=0.02 false-abort P: F=0:{fa_0:.4f}, F=1:{fa_1:.4f}, F=2:{fa_2:.4f}, F=3:{fa_3:.4f}")

    # 3E. Exact discrete-time Markov chain on illustrative synthetic degraded canary:
    # Spec: count=10, failure_limit=2, inconclusive_limit=1, consecutive_success_limit=5
    # Synthetic probabilities: p_S=0.55, p_F=0.25, p_I=0.20 (canary e_bad=5%, w=20% of 100 QPS, lag=60m)
    p_s, p_f, p_i = 0.55, 0.25, 0.20
    spec_mc = ArgoMetricSpec("canary_slo", count=10, failure_limit=2, inconclusive_limit=1, consecutive_success_limit=5)
    dp: dict[tuple[int, int, int, int], float] = {(0, 0, 0, 0): 1.0}
    term_probs = {"Successful": 0.0, "Failed": 0.0, "Inconclusive": 0.0}
    term_weighted_polls = {"Successful": 0.0, "Failed": 0.0, "Inconclusive": 0.0}
    for _step in range(spec_mc.count):
        nxt: dict[tuple[int, int, int, int], float] = {}
        for state, prob in sorted(dp.items()):
            cnt, f_cnt, i_cnt, cs_cnt = state
            for meas, pm in (("Successful", p_s), ("Failed", p_f), ("Inconclusive", p_i)):
                nc = cnt + 1
                nf = f_cnt + (1 if meas == "Failed" else 0)
                ni = i_cnt + (1 if meas == "Inconclusive" else 0)
                ncs = (cs_cnt + 1) if meas == "Successful" else 0
                tmp = ArgoMetricResult(
                    phase="Running", count=nc, failed=nf, inconclusive=ni,
                    consecutive_success=ncs, measurements=[meas],
                )
                ph = argo_assess_metric_status(spec_mc, tmp)
                trans_p = prob * pm
                if ph in term_probs:
                    term_probs[ph] += trans_p
                    term_weighted_polls[ph] += trans_p * nc
                else:
                    key = (nc, nf, ni, ncs)
                    nxt[key] = nxt.get(key, 0.0) + trans_p
        dp = nxt
    assert not dp and abs(sum(term_probs.values()) - 1.0) < 1e-12

    p_prom = term_probs["Successful"]
    p_fail = term_probs["Failed"]
    p_inc = term_probs["Inconclusive"]
    p_non_prom = p_fail + p_inc
    e_polls_all = sum(term_weighted_polls.values())
    e_polls_non_prom = (term_weighted_polls["Failed"] + term_weighted_polls["Inconclusive"]) / p_non_prom
    e_polls_prom = term_weighted_polls["Successful"] / p_prom

    # Consistent branch-complete customer-error accounting (100 QPS, w=20%, e_bad=5%, poll=60s,
    # 60m operator/rollback lag, 30s DefaultAbortScaleDownDelaySeconds for replica-based canaries):
    qps, w_canary, e_bad, poll_sec, lag_sec, abort_delay_sec = 100.0, 0.20, 0.05, 60.0, 3600.0, 30.0
    bad_rps_canary = qps * w_canary * e_bad  # 1.0 bad req/s at 20% weight
    bad_rps_full = qps * 1.0 * e_bad         # 5.0 bad req/s if falsely promoted to 100% traffic

    # Accounting (1): Conditional on non-promotion (Inconclusive U Failed, P = 86.34%)
    cond_argo_pause = (
        e_polls_non_prom * poll_sec * bad_rps_canary
        + (p_inc / p_non_prom) * lag_sec * bad_rps_canary
        + (p_fail / p_non_prom) * abort_delay_sec * bad_rps_canary
    )
    cond_fail_closed = (
        e_polls_non_prom * poll_sec * bad_rps_canary
        + abort_delay_sec * bad_rps_canary
    )
    cond_ratio = cond_argo_pause / cond_fail_closed

    # Accounting (2): Unconditional across all 3 outcomes, charging symmetric 60m rollback lag
    # at 100% traffic (5.0 bad req/s) on the 13.66% false-promotion branch
    post_prom_rollback_cost = p_prom * lag_sec * bad_rps_full
    uncond_argo_pause = (
        e_polls_all * poll_sec * bad_rps_canary
        + p_inc * lag_sec * bad_rps_canary
        + p_fail * abort_delay_sec * bad_rps_canary
        + post_prom_rollback_cost
    )
    uncond_fail_closed = (
        e_polls_all * poll_sec * bad_rps_canary
        + (p_inc + p_fail) * abort_delay_sec * bad_rps_canary
        + post_prom_rollback_cost
    )
    uncond_ratio = uncond_argo_pause / uncond_fail_closed

    assert abs(p_inc - 0.557785) < 1e-5 and abs(p_fail - 0.305625) < 1e-5 and abs(p_prom - 0.136590) < 1e-5
    assert abs(e_polls_all - 6.2578) < 1e-3 and abs(e_polls_non_prom - 6.1915) < 1e-3
    assert abs(cond_ratio - 6.744) < 0.02 and abs(uncond_ratio - 1.696) < 0.02

    print(
        f"  [analytical] Illustrative synthetic degraded canary (pS={p_s},pF={p_f},pI={p_i}): "
        f"P(Abort)={p_fail:.4f}, P(Inconcl-Pause)={p_inc:.4f}, P(Promote)={p_prom:.4f}, "
        f"E[polls]={e_polls_all:.4f} (|non-promote={e_polls_non_prom:.4f}, |promote={e_polls_prom:.4f})"
    )
    print(
        f"  [analytical] Consistent bleed-out (100 QPS, w=20%, 60m lag, 30s replica scale-down): "
        f"cond(~Promote): Argo-Pause={cond_argo_pause:.1f} vs Fail-Closed={cond_fail_closed:.1f} ({cond_ratio:.2f}x); "
        f"uncond(all 3 incl. 60m@100% rollback): Argo-Pause={uncond_argo_pause:.1f} vs Fail-Closed={uncond_fail_closed:.1f} ({uncond_ratio:.2f}x)"
    )


# =============================================================================
# PROBE 4: phamquiluan/BARO@e35f4ec1 & phamquiluan/RCAEval@a30feeba
# =============================================================================

def linear_quantile(sorted_vals: list[float], q: float) -> float:
    """Linear-interpolation quantile matching numpy/sklearn RobustScaler default."""
    n = len(sorted_vals)
    pos = q * (n - 1)
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return sorted_vals[lo]
    return sorted_vals[lo] + (pos - lo) * (sorted_vals[hi] - sorted_vals[lo])


def baro_is_non_constant(vals: list[float]) -> bool:
    """Exact port of BARO/baro/utility.py:64-68 & RCAEval/io/time_series.py:4-5 drop_constant."""
    if not vals:
        return False
    first = vals[0]
    return any(v != first for v in vals)


def baro_convert_mem_mb_col(col_name: str, vals: list[float]) -> list[float]:
    """Exact port of BARO/baro/root_cause_analysis.py:74-93 & RCAEval/io/time_series.py:45-54."""
    if col_name.endswith("_mem"):
        return [v / 1e6 for v in vals]
    return vals


def baro_df_single_score(pre: list[float], post: list[float]) -> float:
    """Exact port of RobustScaler + max(zscores) at BARO:312-315 & RCAEval/e2e/baro.py:49-51."""
    s_pre = sorted(pre)
    med = linear_quantile(s_pre, 0.50)
    iqr = linear_quantile(s_pre, 0.75) - linear_quantile(s_pre, 0.25)
    scale = 1.0 if iqr == 0.0 else iqr  # sklearn _handle_zeros_in_scale
    return max((v - med) / scale for v in post)  # signed max, NO abs()


def baro_df_score_suite_with_preprocess(
    suite: dict[str, tuple[list[float], list[float]]]
) -> dict[str, float]:
    """Exact port of BARO/baro/root_cause_analysis.py:111-112, 293-315 (preprocess + intersect + RobustScaler)."""
    scores: dict[str, float] = {}
    for col, (pre, post) in suite.items():
        # preprocess(normal_df) and preprocess(anomal_df) both call drop_constant(drop_time(df)) then convert_mem_mb
        if not (baro_is_non_constant(pre) and baro_is_non_constant(post)):
            continue
        pre_p = baro_convert_mem_mb_col(col, pre)
        post_p = baro_convert_mem_mb_col(col, post)
        scores[col] = baro_df_single_score(pre_p, post_p)
    return scores


def baro_dict_score(pre: list[float], post: list[float]) -> float:
    """Exact port of BARO/baro/root_cause_analysis.py:188-234 (no drop_constant)."""
    s_pre = sorted(pre)
    n = len(s_pre)
    med = s_pre[n // 2]
    q75 = s_pre[int(n * 0.75)]
    q25 = s_pre[int(n * 0.25)]
    iqr = q75 - q25
    if iqr == 0.0:
        iqr = 1.0
    max_val = max(post)
    return abs(max_val - med) / iqr


def repaired_two_sided_scale_invariant_score(pre: list[float], post: list[float], eps_abs: float = 1e-3) -> float:
    """Repaired scorer: retains zero-baseline metrics, two-sided max|z|, unit-normalized scale floor when IQR == 0."""
    s_pre = sorted(pre)
    med = linear_quantile(s_pre, 0.50)
    iqr = linear_quantile(s_pre, 0.75) - linear_quantile(s_pre, 0.25)
    scale = iqr if iqr > 0.0 else max(abs(med) * 0.01, eps_abs)
    return max(abs(v - med) / scale for v in post)


def rank_of_target(scores: dict[str, float], target: str) -> int:
    ordered = sorted(scores.items(), key=lambda kv: (-kv[1], kv[0]))
    for idx, (k, _) in enumerate(ordered, 1):
        if k == target:
            return idx
    raise KeyError(target)


def run_probe_4() -> None:
    print("\n=== PROBE 4: BARO & RCAEVAL ROBUSTSCORER FAILURE MODES & REPAIRS ===")
    print("Provenance: [source port] phamquiluan/BARO@e35f4ec1 & phamquiluan/RCAEval@a30feeba + [controlled simulation]")

    rng = random.Random(404)
    n_metrics = 212  # Train Ticket metric count (BARO Table 1)
    n_pre, n_post = 120, 60

    def make_normal_suite() -> dict[str, tuple[list[float], list[float]]]:
        suite: dict[str, tuple[list[float], list[float]]] = {}
        for i in range(n_metrics):
            base = 50.0 + (i % 10) * 5.0
            pre = [base + rng.gauss(0.0, 1.0) for _ in range(n_pre)]
            post = [base + rng.gauss(0.0, 1.0) for _ in range(n_post)]
            suite[f"svc_{i:03d}_kpi"] = (pre, post)
        return suite

    # 4A-1: Step-immediate sustained downward shift (throughput/cache-hit collapse 100 -> 20)
    s_a1 = make_normal_suite()
    target = "svc_042_kpi"
    s_a1[target] = ([100.0 + rng.gauss(0.0, 1.0) for _ in range(n_pre)], [20.0 + rng.gauss(0.0, 1.0) for _ in range(n_post)])
    r_a1_df = rank_of_target(baro_df_score_suite_with_preprocess(s_a1), target)
    r_a1_dict = rank_of_target({k: baro_dict_score(*v) for k, v in s_a1.items()}, target)
    r_a1_rep = rank_of_target({k: repaired_two_sided_scale_invariant_score(*v) for k, v in s_a1.items()}, target)
    assert r_a1_df == n_metrics and r_a1_dict == 1 and r_a1_rep == 1

    # 4A-2: Delayed / transient downward drop (first 10s normal, then 50s collapse 100 -> 20)
    s_a2 = make_normal_suite()
    post_delayed = [100.0 + rng.gauss(0.0, 0.5) for _ in range(10)] + [20.0 + rng.gauss(0.0, 1.0) for _ in range(50)]
    s_a2[target] = ([100.0 + rng.gauss(0.0, 1.0) for _ in range(n_pre)], post_delayed)
    r_a2_df = rank_of_target(baro_df_score_suite_with_preprocess(s_a2), target)
    r_a2_dict = rank_of_target({k: baro_dict_score(*v) for k, v in s_a2.items()}, target)
    r_a2_rep = rank_of_target({k: repaired_two_sided_scale_invariant_score(*v) for k, v in s_a2.items()}, target)
    assert r_a2_df > 50 and r_a2_dict > 50 and r_a2_rep == 1

    # 4B-1: Literally constant pre-fault metrics -> BARO robust_scorer drop_constant(normal_df)
    # silently deletes the 0->50% error metric before RobustScaler runs; baro_dict_score (no drop_constant)
    # keeps it and lets constant 100 MiB _mem_bytes (+10 KiB drift) bury it at rank 223/223.
    s_b_const = make_normal_suite()
    err_target = "svc_042_error_rate"
    s_b_const[err_target] = ([0.0] * n_pre, [0.50] * n_post)
    for j in range(10):
        s_b_const[f"svc_{j:03d}_mem_bytes"] = ([100_000_000.0] * n_pre, [100_010_000.0] * n_post)
    sc_b_const_df = baro_df_score_suite_with_preprocess(s_b_const)
    sc_b_const_dict = {k: baro_dict_score(*v) for k, v in s_b_const.items()}
    sc_b_const_rep = {k: repaired_two_sided_scale_invariant_score(*v) for k, v in s_b_const.items()}
    assert err_target not in sc_b_const_df and len(sc_b_const_df) == n_metrics
    r_b_const_dict = rank_of_target(sc_b_const_dict, err_target)
    r_b_const_rep = rank_of_target(sc_b_const_rep, err_target)
    assert sc_b_const_dict["svc_000_mem_bytes"] == 10000.0 and sc_b_const_dict[err_target] == 0.50
    assert r_b_const_dict == 223 and r_b_const_rep == 1

    # 4B-2: Non-constant zero-IQR series (>75% equal baseline values, nunique > 1 in both pre and post):
    # Survives drop_constant(normal_df) & drop_constant(anomal_df) AND convert_mem_mb (only scales *_mem),
    # yet still hits Q75 == Q25 -> IQR == 0 -> sklearn scale_ = 1.0 inside BARO robust_scorer!
    s_b_nc = make_normal_suite()
    s_b_nc[err_target] = ([0.0] * 118 + [0.001, 0.002], [0.50] * 59 + [0.49])
    for j in range(10):
        s_b_nc[f"svc_{j:03d}_mem_bytes"] = (
            [100_000_000.0] * 118 + [100_000_001.0, 100_000_002.0],
            [100_010_000.0] * 59 + [100_009_999.0],
        )
    sc_b_nc_df = baro_df_score_suite_with_preprocess(s_b_nc)
    sc_b_nc_rep = {k: repaired_two_sided_scale_invariant_score(*v) for k, v in s_b_nc.items()}
    assert len(sc_b_nc_df) == 223 and err_target in sc_b_nc_df
    r_b_nc_df = rank_of_target(sc_b_nc_df, err_target)
    r_b_nc_rep = rank_of_target(sc_b_nc_rep, err_target)
    assert sc_b_nc_df["svc_000_mem_bytes"] == 10000.0 and sc_b_nc_df[err_target] == 0.50
    assert r_b_nc_df == 223 and r_b_nc_rep == 1

    # 4C: 15x point-decimation aliasing in multi-source mmnsigma/mmbaro (RCAEval/e2e/baro.py:88)
    burst_d = 3
    hits_decim = 0
    hits_pool = 0
    for phase in range(15):
        base_pre = [10.0 + 0.1 * ((t % 7) - 3) for t in range(180)]
        base_post = [10.0 + 0.1 * ((t % 7) - 3) for t in range(120)]
        for k in range(burst_d):
            base_post[phase + k] = 100.0
        full = base_pre + base_post
        decim = full[::15]
        if baro_df_single_score(decim[: 180 // 15], decim[180 // 15 :]) > 20.0:
            hits_decim += 1
        pooled = [max(full[i : i + 15]) for i in range(0, len(full), 15)]
        if repaired_two_sided_scale_invariant_score(pooled[: 180 // 15], pooled[180 // 15 :]) > 20.0:
            hits_pool += 1
    det_decim = hits_decim / 15.0
    det_pool = hits_pool / 15.0
    assert abs(det_decim - (burst_d / 15.0)) < 1e-12 and det_pool == 1.0

    print(f"  [source+sim] 212-metric sustained drop: baro_df rank={r_a1_df}/{n_metrics}, baro_dict rank={r_a1_dict}/{n_metrics}, repaired rank={r_a1_rep}/{n_metrics}")
    print(f"  [source+sim] 212-metric delayed drop:   baro_df rank={r_a2_df}/{n_metrics}, baro_dict rank={r_a2_dict}/{n_metrics}, repaired rank={r_a2_rep}/{n_metrics}")
    print(
        f"  [source+sim] Constant pre-fault (0->50% err vs +0.01% MiB): "
        f"baro_df(with preprocess) drops target (retained={len(sc_b_const_df)}/223); "
        f"baro_dict(no drop_constant) score(err)={sc_b_const_dict[err_target]:.2f} vs mem={sc_b_const_dict['svc_000_mem_bytes']:.1f}, "
        f"rank={r_b_const_dict}/223 -> repaired rank={r_b_const_rep}/223"
    )
    print(
        f"  [source+sim] Non-constant zero-IQR (98.3% equal pre, survives drop_constant, retained={len(sc_b_nc_df)}/223): "
        f"baro_df(with preprocess) score(err)={sc_b_nc_df[err_target]:.2f} vs mem={sc_b_nc_df['svc_000_mem_bytes']:.1f}, "
        f"rank={r_b_nc_df}/223 -> repaired rank={r_b_nc_rep}/223"
    )
    print(
        f"  [source+sim] mmbaro/mmnsigma 15x decimation aliasing (d={burst_d}s burst, 15 phases): "
        f"iloc[::15] recall={det_decim:.4f} (exact d/15) vs 15s max-pool recall={det_pool:.4f}"
    )


# =============================================================================
# PROBE 5: microsoft/AIOpsLab@576c3f08 & microsoft/OpenRCA@2a481ae6
# =============================================================================

@dataclass
class MockContainerStatus:
    name: str
    ready: bool
    waiting_reason: str | None = None
    terminated_reason: str | None = None


@dataclass
class MockPod:
    name: str
    phase: str
    container_statuses: list[MockContainerStatus] | None


def aiopslab_pods_unhealthy_reasons(pods: list[MockPod]) -> list[str]:
    """Exact port of microsoft/AIOpsLab@576c3f08 tasks/mitigation.py:92-117."""
    reasons: list[str] = []
    for pod in pods:
        if not pod.container_statuses:
            continue
        for cs in pod.container_statuses:
            if cs.waiting_reason == "CrashLoopBackOff":
                reasons.append(f"Container {cs.name} is in CrashLoopBackOff")
            elif cs.terminated_reason is not None and cs.terminated_reason != "Completed":
                reasons.append(f"Container {cs.name} is terminated with reason: {cs.terminated_reason}")
            elif not cs.ready:
                reasons.append(f"Container {cs.name} is not ready")
    return reasons


AIOPSLAB_BLOCK_LIST = {
    "kubectl edit",
    "edit svc",
    "kubectl port-forward",
    "docker logs -f",
    "kubectl logs -f",
}  # actions/base.py:93-99


def aiopslab_command_allowed(cmd: str) -> bool:
    return not any(pat in cmd for pat in AIOPSLAB_BLOCK_LIST)


def repaired_mitigation_healthy(
    pods: list[MockPod], expected_min_ready_pods: int, http_500_rate: float
) -> bool:
    """Repaired mitigation grader: enforces workload cardinality, pod phase, container readiness, and SLI."""
    ready_pods = 0
    for pod in pods:
        if pod.phase != "Running" or not pod.container_statuses:
            return False
        if any(
            (not cs.ready) or cs.waiting_reason or (cs.terminated_reason and cs.terminated_reason != "Completed")
            for cs in pod.container_statuses
        ):
            return False
        ready_pods += 1
    return ready_pods >= expected_min_ready_pods and http_500_rate < 0.01


def openrca_evaluate_pinned(prediction: str, scoring_points: str) -> tuple[list[str], list[str], float]:
    """Exact port of microsoft/OpenRCA@2a481ae6 main/evaluate.py:19-101."""
    predict_pattern = (
        r'{\s*'
        r'(?:"root cause occurrence datetime":\s*"(.*?)")?,?\s*'
        r'(?:"root cause component":\s*"(.*?)")?,?\s*'
        r'(?:"root cause reason":\s*"(.*?)")?\s*}'
    )
    predict_matches = re.findall(predict_pattern, prediction)
    predict_results = [
        {
            "root cause occurrence datetime": m[0],
            "root cause component": m[1],
            "root cause reason": m[2],
        }
        for m in predict_matches
    ]
    prediction_length = len(predict_results)

    components = re.findall(r"The (?:\d+-th|only) predicted root cause component is ([^\n]+)", scoring_points)
    reasons = re.findall(r"The (?:\d+-th|only) predicted root cause reason is ([^\n]+)", scoring_points)
    times = re.findall(
        r"The (?:\d+-th|only) root cause occurrence time is within 1 minutes \(i.e., <=1min\) of ([^\n]+)",
        scoring_points,
    )
    scoringpoints_length = max(len(components), len(reasons), len(times))
    scores_num = len(components) + len(reasons) + len(times)

    def time_difference(t1_s: str, t2_s: str) -> bool:
        fmt = "%Y-%m-%d %H:%M:%S"
        try:
            t1 = datetime.strptime(t1_s, fmt)
            t2 = datetime.strptime(t2_s, fmt)
        except ValueError:
            return False
        return abs(t1 - t2).total_seconds() <= 60

    scores_get = 0
    passing_criteria: list[str] = []
    if scoringpoints_length == prediction_length:
        best_score = -1
        for perm in itertools.permutations(predict_results):
            cur_score = 0
            cur_passing: list[str] = []
            for i in range(scoringpoints_length):
                if len(components) == scoringpoints_length and perm[i]["root cause component"] == components[i]:
                    cur_score += 1
                    cur_passing.append(components[i])
                if len(reasons) == scoringpoints_length and perm[i]["root cause reason"] == reasons[i]:
                    cur_score += 1
                    cur_passing.append(reasons[i])
                if len(times) == scoringpoints_length and time_difference(times[i], perm[i]["root cause occurrence datetime"]):
                    cur_score += 1
                    cur_passing.append(times[i])
            if cur_score > best_score:
                best_score = cur_score
                passing_criteria = cur_passing
        scores_get = best_score

    failing_criteria = sorted(set(components + reasons + times) - set(passing_criteria))
    return passing_criteria, failing_criteria, round(scores_get / scores_num, 2)


def openrca_evaluate_repaired(prediction: str, scoring_points: str) -> float:
    """Repaired parser: JSONDecoder extracting valid RCA dicts + ISO-8601/UTC+8 timestamp normalization."""
    dec = json.JSONDecoder()
    rca_keys = {"root cause occurrence datetime", "root cause component", "root cause reason"}
    objs: list[dict[str, Any]] = []
    idx = 0
    n = len(prediction)
    while idx < n:
        pos = prediction.find("{", idx)
        if pos == -1:
            break
        try:
            obj, end = dec.raw_decode(prediction, pos)
            if isinstance(obj, dict) and (rca_keys.intersection(obj.keys())):
                objs.append(obj)
            idx = end
        except json.JSONDecodeError:
            idx = pos + 1

    components = re.findall(r"The (?:\d+-th|only) predicted root cause component is ([^\n]+)", scoring_points)
    reasons = re.findall(r"The (?:\d+-th|only) predicted root cause reason is ([^\n]+)", scoring_points)
    times = re.findall(
        r"The (?:\d+-th|only) root cause occurrence time is within 1 minutes \(i.e., <=1min\) of ([^\n]+)",
        scoring_points,
    )
    k = max(len(components), len(reasons), len(times))
    total = len(components) + len(reasons) + len(times)
    if len(objs) != k:
        return 0.0

    tz_cn = timezone(timedelta(hours=8))

    def parse_ts(s: str) -> datetime | None:
        s = s.strip()
        try:
            dt = datetime.fromisoformat(s.replace("Z", "+00:00"))
        except ValueError:
            return None
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=tz_cn)
        return dt.astimezone(timezone.utc)

    best = 0
    for perm in itertools.permutations(objs):
        sc = 0
        for i in range(k):
            if len(components) == k and perm[i].get("root cause component") == components[i]:
                sc += 1
            if len(reasons) == k and perm[i].get("root cause reason") == reasons[i]:
                sc += 1
            if len(times) == k:
                t1 = parse_ts(times[i])
                t2 = parse_ts(str(perm[i].get("root cause occurrence datetime", "")))
                if t1 is not None and t2 is not None and abs((t1 - t2).total_seconds()) <= 60.0:
                    sc += 1
        if sc > best:
            best = sc
    return round(best / total, 2)


def run_probe_5() -> None:
    print("\n=== PROBE 5: AIOPSLAB & OPENRCA EVALUATOR FORENSICS ===")
    print("Provenance: [source port] microsoft/AIOpsLab@576c3f08 & microsoft/OpenRCA@2a481ae6")

    # 5A. AIOpsLab vacuous-health passes (sole check in 4/10 mitigation subclasses) & command guard gap
    cmd_nuke = "kubectl delete deploy --all -n test-hotel-reservation"
    assert aiopslab_command_allowed(cmd_nuke) is True

    scenarios = [
        ("deleted_all_pods", [], 1.0),
        ("pending_unschedulable", [MockPod("web-0", "Pending", None), MockPod("db-0", "Pending", [])], 1.0),
        ("running_app_500s", [MockPod("web-0", "Running", [MockContainerStatus("app", True)])], 1.0),
        ("genuine_recovery", [MockPod("web-0", "Running", [MockContainerStatus("app", True)])], 0.0),
    ]
    for label, pods, err_rate in scenarios:
        pinned_pass = len(aiopslab_pods_unhealthy_reasons(pods)) == 0
        repaired_pass = repaired_mitigation_healthy(pods, expected_min_ready_pods=1, http_500_rate=err_rate)
        if label != "genuine_recovery":
            assert pinned_pass is True and repaired_pass is False
        else:
            assert pinned_pass is True and repaired_pass is True
        print(f"  [source port] AIOpsLab {label:22s}: pinned_pass={str(pinned_pass):5s}, repaired_pass={str(repaired_pass):5s}")

    # Localization string-to-char-set coercion (target_port.py:105 + quantitative.py:61)
    is_sub_str = {"user-service"}.issubset(set("user-service, frontend"))
    is_sub_list = {"user-service"}.issubset(set(["user-service", "frontend"]))
    assert is_sub_str is False and is_sub_list is True
    print(f"  [source port] AIOpsLab is_subset string coercion: raw_str={is_sub_str} vs list={is_sub_list}")

    # 5B. OpenRCA main/evaluate.py:19-101 rigid regex false rejections (incl. extra_key_1line = 0.67)
    gt = (
        "The only root cause occurrence time is within 1 minutes (i.e., <=1min) of 2022-03-20 14:25:00\n"
        "The only predicted root cause component is checkoutservice\n"
        "The only predicted root cause reason is memory leak"
    )
    cases = [
        ("canonical_exact", '{"root cause occurrence datetime": "2022-03-20 14:25:00", "root cause component": "checkoutservice", "root cause reason": "memory leak"}', 1.00, 1.00),
        ("reordered_1line", '{"root cause component": "checkoutservice", "root cause occurrence datetime": "2022-03-20 14:25:00", "root cause reason": "memory leak"}', 0.33, 1.00),
        ("reordered_multi", '{\n  "root cause component": "checkoutservice",\n  "root cause occurrence datetime": "2022-03-20 14:25:00",\n  "root cause reason": "memory leak"\n}', 0.00, 1.00),
        ("reordered_rcd", '{"root cause reason": "memory leak", "root cause component": "checkoutservice", "root cause occurrence datetime": "2022-03-20 14:25:00"}', 0.00, 1.00),
        ("iso8601_utc8_ts", '{"root cause occurrence datetime": "2022-03-20T14:25:00+08:00", "root cause component": "checkoutservice", "root cause reason": "memory leak"}', 0.67, 1.00),
        ("stray_braces_cot", 'Initial set {} checked. Final: {"root cause occurrence datetime": "2022-03-20 14:25:00", "root cause component": "checkoutservice", "root cause reason": "memory leak"}', 0.00, 1.00),
        ("extra_key_1line", '{"root cause occurrence datetime": "2022-03-20 14:25:00", "root cause component": "checkoutservice", "root cause reason": "memory leak", "confidence": "high"}', 0.67, 1.00),
        ("extra_key_multi", '{\n  "root cause occurrence datetime": "2022-03-20 14:25:00",\n  "root cause component": "checkoutservice",\n  "root cause reason": "memory leak",\n  "confidence": "high"\n}', 0.00, 1.00),
        ("two_candidates", '{"root cause occurrence datetime": "2022-03-20 14:25:00", "root cause component": "checkoutservice", "root cause reason": "memory leak"} {"root cause occurrence datetime": "2022-03-20 14:26:00", "root cause component": "cartservice", "root cause reason": "cpu"}', 0.00, 0.00),
    ]
    for label, pred, exp_pinned, exp_rep in cases:
        _, _, sc_pinned = openrca_evaluate_pinned(pred, gt)
        sc_rep = openrca_evaluate_repaired(pred, gt)
        assert sc_pinned == exp_pinned, f"{label}: got {sc_pinned}, expected {exp_pinned}"
        assert sc_rep == exp_rep, f"{label}: got {sc_rep}, expected {exp_rep}"
        print(f"  [source port] OpenRCA {label:18s}: pinned_score={sc_pinned:.2f}, repaired_score={sc_rep:.2f}")


def main() -> None:
    run_probe_1()
    run_probe_2()
    run_probe_3()
    run_probe_4()
    run_probe_5()
    print("\nALL 5 VERIFICATION PROBES PASSED.")


if __name__ == "__main__":
    main()
