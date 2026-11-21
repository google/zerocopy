#!/usr/bin/env python3
"""Deterministic verification probes for agent instruction compliance and skill routing.

Self-contained support script for the reference report package:
  reports/agent-instruction-compliance-context-rot-reasoning-models-and-skill-routing/

Runtime constraints: Python 3.10+ standard library only, fixed seed 20261121,
zero network calls, deterministic stdout, < 3s wall-clock runtime.

Epistemic labeling discipline (explicitly printed in stdout banners):
  - Probe 1 ([derived fit to published table]):
      1A: ManyIFEval (arXiv:2509.21051v1, App. F.1 Tables 8-9, n=1..10):
          compares 0-param independent Bernoulli p_1^n, 1-param fitted constant
          Bernoulli p_c^n, out-of-sample attention-dilution p_hat(n)^n trained
          strictly on MANYIFEVAL_INST (zero prompt_ys fitting), and multi-point
          in-sample Beta-Binomial vs. attention-dilution fits with AICc.
      1B: IFScale (arXiv:2507.11538v1, App. A Table 1, k=10..500, keyword
          inclusion only): compares zero-dilution ceiling against exponential
          and logistic/threshold dilution fits across all 5 milestone densities.
      1C: MTAC-IFBench (arXiv:2609.14992v1, Tables 2 & 5, avg n=12.97/turn):
          evaluates all 11 Claude Code models and tests the (CSR_OC/CSR_CC)^12.97
          compounding approximation honestly across all 8 models shared with
          OpenCode (exposing both the 3 matches and the 5 misses/sign reversals).
      1D: Derived safe simultaneous active constraint budget k_max table under
          illustrative per-constraint dilution regimes.
  - Probe 2 ([toy model / mechanistic surrogate]):
      Parameterized Gaussian signal-detection surrogate of flat catalog injection,
      passive Top-K retrieval, equal-footed 2-level hierarchy (active_gain=0),
      and active-query 2-level hierarchy (active_gain sweep), plus a context-rot
      crossover sensitivity sweep and decoupled overlap/ctx_rot negative controls.
  - Probe 3 ([toy model / mechanistic surrogate]):
      Parameterized Markov-chain + Monte Carlo sensitivity surrogate of single-file
      vs. split SKILL.md + references/ progressive disclosure across Turns 1..8,
      explicitly modeling both coupled (shared sliding window) and independent
      compaction eviction and sweeping a 2D sensitivity grid for q_trig*.
"""

from __future__ import annotations

import math
import random
import statistics
from dataclasses import dataclass

SEED = 20261121


# =============================================================================
# Published Empirical Anchor Tables (verified verbatim against primary papers)
# =============================================================================

# ManyIFEval (arXiv:2509.21051v1, Appendix F.1, Tables 8 & 9), n = 1..10
MANYIFEVAL_N = list(range(1, 11))
MANYIFEVAL_PROMPT = {
    "Qwen2.5-72B":       [0.95, 0.83, 0.71, 0.52, 0.40, 0.28, 0.19, 0.12, 0.04, 0.02],
    "GPT-4o":            [0.94, 0.85, 0.73, 0.64, 0.57, 0.46, 0.39, 0.39, 0.29, 0.21],
    "DeepSeek-V3":       [0.96, 0.90, 0.85, 0.70, 0.63, 0.48, 0.43, 0.33, 0.29, 0.19],
    "DeepSeek-R1":       [0.95, 0.89, 0.81, 0.74, 0.71, 0.64, 0.59, 0.49, 0.44, 0.38],
    "Claude-3.5-Sonnet": [0.95, 0.90, 0.88, 0.79, 0.72, 0.68, 0.67, 0.62, 0.58, 0.48],
    "o3-mini (low)":     [0.97, 0.93, 0.92, 0.84, 0.81, 0.75, 0.69, 0.70, 0.64, 0.53],
    "o3-mini (med)":     [0.98, 0.95, 0.94, 0.89, 0.87, 0.83, 0.78, 0.73, 0.73, 0.64],
    "o3-mini (high)":    [1.00, 0.96, 0.95, 0.93, 0.90, 0.88, 0.83, 0.82, 0.79, 0.78],
}
MANYIFEVAL_INST = {
    "Qwen2.5-72B":       [0.95, 0.91, 0.90, 0.86, 0.85, 0.82, 0.80, 0.78, 0.77, 0.75],
    "GPT-4o":            [0.94, 0.92, 0.90, 0.90, 0.89, 0.88, 0.88, 0.89, 0.87, 0.85],
    "DeepSeek-V3":       [0.96, 0.95, 0.95, 0.92, 0.91, 0.89, 0.89, 0.89, 0.89, 0.87],
    "DeepSeek-R1":       [0.95, 0.94, 0.94, 0.92, 0.93, 0.92, 0.93, 0.92, 0.92, 0.92],
    "Claude-3.5-Sonnet": [0.95, 0.95, 0.96, 0.94, 0.94, 0.94, 0.94, 0.94, 0.94, 0.93],
    "o3-mini (low)":     [0.97, 0.96, 0.97, 0.96, 0.96, 0.95, 0.95, 0.96, 0.95, 0.94],
    "o3-mini (med)":     [0.98, 0.97, 0.98, 0.97, 0.97, 0.97, 0.97, 0.96, 0.96, 0.96],
    "o3-mini (high)":    [1.00, 0.98, 0.98, 0.98, 0.98, 0.98, 0.97, 0.98, 0.98, 0.98],
}

# IFScale (arXiv:2507.11538v1, Appendix A Table 1 [multi-page], single-turn
# keyword-inclusion constraints only), milestone densities k in {10, 50, 100, 250, 500}
IFSCALE_K = [10, 50, 100, 250, 500]
IFSCALE_ACC = {
    "gemini-2.5-pro":   [1.000, 0.996, 0.984, 0.848, 0.689],
    "o3 (high)":        [1.000, 0.996, 0.982, 0.978, 0.628],
    "gpt-4.1":          [0.980, 0.988, 0.954, 0.740, 0.489],
    "claude-opus-4":    [1.000, 1.000, 0.946, 0.679, 0.446],
    "gpt-4o":           [0.940, 0.828, 0.490, 0.222, 0.154],
    "claude-3.5-haiku": [0.980, 0.780, 0.434, 0.166, 0.085],
    "llama-4-scout":    [1.000, 0.544, 0.272, 0.093, 0.067],
}

# MTAC-IFBench (arXiv:2609.14992v1, Table 2 Claude Code & Table 5 OpenCode)
# Turn buckets 1..5 = Turns {1-2, 3-4, 5-6, 7-8, 9-10}; avg 12.97 active constraints/turn
MTAC_AVG_CONSTRAINTS = 12.97

# All 11 models evaluated on Claude Code (Table 2)
MTAC_CLAUDE_CODE = {
    "GLM-5.2":           {"csr": [0.858, 0.808, 0.779, 0.780, 0.761], "csr_avg": 0.804,
                          "cisr": [0.276, 0.097, 0.048, 0.058, 0.026], "cisr_avg": 0.127},
    "Claude-Opus-4.6":   {"csr": [0.824, 0.791, 0.768, 0.764, 0.762], "csr_avg": 0.786,
                          "cisr": [0.190, 0.065, 0.035, 0.033, 0.023], "cisr_avg": 0.087},
    "GLM-5.1":           {"csr": [0.813, 0.779, 0.747, 0.715, 0.722], "csr_avg": 0.765,
                          "cisr": [0.197, 0.082, 0.026, 0.000, 0.000], "cisr_avg": 0.089},
    "DeepSeek-V4-Pro":   {"csr": [0.796, 0.769, 0.727, 0.708, 0.677], "csr_avg": 0.747,
                          "cisr": [0.145, 0.070, 0.012, 0.000, 0.000], "cisr_avg": 0.064},
    "Kimi-K2.6":         {"csr": [0.807, 0.747, 0.705, 0.701, 0.625], "csr_avg": 0.732,
                          "cisr": [0.186, 0.072, 0.018, 0.000, 0.000], "cisr_avg": 0.078},
    "Gemini-3.1-Pro":    {"csr": [0.816, 0.749, 0.677, 0.617, 0.582], "csr_avg": 0.710,
                          "cisr": [0.281, 0.091, 0.024, 0.000, 0.000], "cisr_avg": 0.111},
    "DeepSeek-V4-Flash": {"csr": [0.764, 0.717, 0.687, 0.656, 0.596], "csr_avg": 0.700,
                          "cisr": [0.085, 0.020, 0.012, 0.011, 0.000], "cisr_avg": 0.034},
    "Qwen3.6-Plus":      {"csr": [0.733, 0.683, 0.672, 0.676, 0.650], "csr_avg": 0.688,
                          "cisr": [0.060, 0.010, 0.000, 0.000, 0.000], "cisr_avg": 0.020},
    "Seed-2.0-Pro":      {"csr": [0.756, 0.688, 0.638, 0.619, 0.576], "csr_avg": 0.669,
                          "cisr": [0.080, 0.010, 0.000, 0.000, 0.000], "cisr_avg": 0.026},
    "Claude-Haiku-4.5":  {"csr": [0.724, 0.678, 0.625, 0.598, 0.497], "csr_avg": 0.647,
                          "cisr": [0.045, 0.020, 0.000, 0.000, 0.000], "cisr_avg": 0.019},
    "Qwen3.5-27B":       {"csr": [0.683, 0.626, 0.577, 0.565, 0.505], "csr_avg": 0.606,
                          "cisr": [0.040, 0.000, 0.000, 0.000, 0.000], "cisr_avg": 0.011},
}

# All 8 models shared between Claude Code (Table 2) and OpenCode (Table 5)
MTAC_OPENCODE = {
    "GLM-5.2":           {"csr": [0.806, 0.773, 0.753, 0.741, 0.742], "csr_avg": 0.768,
                          "cisr": [0.150, 0.045, 0.047, 0.000, 0.000], "cisr_avg": 0.067},
    "GLM-5.1":           {"csr": [0.779, 0.751, 0.724, 0.720, 0.709], "csr_avg": 0.743,
                          "cisr": [0.115, 0.038, 0.000, 0.000, 0.000], "cisr_avg": 0.045},
    "DeepSeek-V4-Pro":   {"csr": [0.756, 0.745, 0.711, 0.678, 0.650], "csr_avg": 0.722,
                          "cisr": [0.113, 0.073, 0.016, 0.000, 0.000], "cisr_avg": 0.059},
    "Qwen3.6-Plus":      {"csr": [0.718, 0.698, 0.664, 0.644, 0.596], "csr_avg": 0.680,
                          "cisr": [0.070, 0.000, 0.010, 0.000, 0.000], "cisr_avg": 0.024},
    "Seed-2.0-Pro":      {"csr": [0.760, 0.702, 0.641, 0.605, 0.563], "csr_avg": 0.672,
                          "cisr": [0.140, 0.010, 0.000, 0.010, 0.000], "cisr_avg": 0.043},
    "DeepSeek-V4-Flash": {"csr": [0.685, 0.649, 0.622, 0.614, 0.544], "csr_avg": 0.637,
                          "cisr": [0.032, 0.010, 0.000, 0.000, 0.000], "cisr_avg": 0.011},
    "Claude-Haiku-4.5":  {"csr": [0.673, 0.644, 0.602, 0.578, 0.513], "csr_avg": 0.618,
                          "cisr": [0.020, 0.000, 0.000, 0.000, 0.000], "cisr_avg": 0.010},
    "Qwen3.5-27B":       {"csr": [0.664, 0.624, 0.583, 0.597, 0.596], "csr_avg": 0.618,
                          "cisr": [0.020, 0.000, 0.000, 0.000, 0.000], "cisr_avg": 0.010},
}


# =============================================================================
# Helper Math Primitives (stdlib-only)
# =============================================================================

def rmse(xs: list[float], ys: list[float]) -> float:
    return math.sqrt(sum((a - b) ** 2 for a, b in zip(xs, ys)) / len(xs))


def aicc_gaussian(xs: list[float], ys: list[float], n_params: int) -> float:
    """Small-sample corrected AIC under Gaussian residuals (includes variance param)."""
    n = len(xs)
    rss = max(1e-12, sum((a - b) ** 2 for a, b in zip(xs, ys)))
    k = n_params + 1  # regression parameters + residual sigma^2
    aic = n * math.log(rss / n) + 2.0 * k
    denom = max(1, n - k - 1)
    return aic + (2.0 * k * (k + 1.0)) / denom


def fit_const_bernoulli(ns: list[float], ys: list[float]) -> tuple[float, float]:
    """1-parameter fitted constant Bernoulli p^n minimizing multi-point RMSE."""
    best_p = 0.90
    best_err = float("inf")
    for pi in range(500, 1001):
        p = pi / 1000.0
        err = rmse([p ** n for n in ns], ys)
        if err < best_err:
            best_err = err
            best_p = p
    step = 0.001
    for _ in range(10):
        improved = False
        for d in (-1.0, 1.0):
            np_ = min(1.0, max(0.50, best_p + d * step))
            err = rmse([np_ ** n for n in ns], ys)
            if err < best_err:
                best_err = err
                best_p = np_
                improved = True
        if not improved:
            step *= 0.5
    return best_p, best_err


def fit_marginal_exp_dilution(ns: list[float], inst_ys: list[float]) -> tuple[float, float, float]:
    """Fit p(n) = min(1.0, p0 * exp(-alpha * (n - 1))) strictly to MANYIFEVAL_INST.

    Never sees prompt-level ys; used for genuine out-of-sample prediction of p(n)^n.
    """
    best_p0 = inst_ys[0]
    best_alpha = 0.0
    best_err = float("inf")
    for dp in range(-25, 26, 2):
        p0 = min(1.0, max(0.50, inst_ys[0] + dp * 0.001))
        for ai in range(0, 45):
            alpha = ai * 0.001
            preds = [min(1.0, p0 * math.exp(-alpha * (n - 1.0))) for n in ns]
            err = rmse(preds, inst_ys)
            if err < best_err:
                best_err = err
                best_p0, best_alpha = p0, alpha
    step_p, step_a = 0.001, 0.0005
    for _ in range(12):
        improved = False
        for sp in (-1, 0, 1):
            for sa in (-1, 0, 1):
                if sp == 0 and sa == 0:
                    continue
                np0 = min(1.0, max(0.50, best_p0 + sp * step_p))
                na = max(0.0, best_alpha + sa * step_a)
                preds = [min(1.0, np0 * math.exp(-na * (n - 1.0))) for n in ns]
                err = rmse(preds, inst_ys)
                if err < best_err:
                    best_err = err
                    best_p0, best_alpha = np0, na
                    improved = True
        if not improved:
            step_p *= 0.5
            step_a *= 0.5
    return best_p0, best_alpha, best_err


def beta_binom_all_met(n: float, a: float, b: float) -> float:
    """E[q^n] for q ~ Beta(a, b): B(a + n, b) / B(a, b)."""
    return math.exp(
        math.lgamma(a + n) + math.lgamma(a + b) - math.lgamma(a + b + n) - math.lgamma(a)
    )


def fit_beta_binomial(ns: list[float], ys: list[float]) -> tuple[float, float, float]:
    """2-parameter Beta-Binomial (a, b) minimizing multi-point RMSE on prompt ys."""
    best_err = float("inf")
    best_ab = (10.0, 1.0)
    for mu_i in range(40, 100, 3):
        mu = mu_i / 100.0
        for log_m in (0.0, 0.8, 1.6, 2.4, 3.2, 4.2, 5.5):
            m = math.exp(log_m)
            a, b = mu * m, (1.0 - mu) * m
            err = rmse([beta_binom_all_met(n, a, b) for n in ns], ys)
            if err < best_err:
                best_err = err
                best_ab = (a, b)
    a, b = best_ab
    step = 0.25
    for _ in range(18):
        improved = False
        for da_f in (-1.0, 0.0, 1.0):
            for db_f in (-1.0, 0.0, 1.0):
                if da_f == 0.0 and db_f == 0.0:
                    continue
                na = max(0.05, a * (1.0 + da_f * step))
                nb = max(0.01, b * (1.0 + db_f * step))
                err = rmse([beta_binom_all_met(n, na, nb) for n in ns], ys)
                if err < best_err:
                    best_err = err
                    a, b = na, nb
                    improved = True
        if not improved:
            step *= 0.5
    return a, b, best_err


def fit_prompt_exp_dilution(ns: list[float], p1_anchor: float, ys: list[float]) -> tuple[float, float, float]:
    """2-parameter prompt-level exponential dilution (p0, alpha) minimizing RMSE on ys."""
    best_p0, best_alpha, best_err = min(1.0, p1_anchor), 0.0, float("inf")
    for dp in range(-40, 26, 4):
        p0 = min(1.0, max(0.50, p1_anchor + dp * 0.001))
        for ai in range(0, 61):
            alpha = ai * 0.001
            err = rmse([min(1.0, p0 * math.exp(-alpha * (n - 1.0))) ** n for n in ns], ys)
            if err < best_err:
                best_err = err
                best_p0, best_alpha = p0, alpha
    step_p, step_a = 0.002, 0.0005
    for _ in range(10):
        improved = False
        for sp in (-1, 0, 1):
            for sa in (-1, 0, 1):
                if sp == 0 and sa == 0:
                    continue
                np0 = min(1.0, max(0.50, best_p0 + sp * step_p))
                na = max(0.0, best_alpha + sa * step_a)
                err = rmse([min(1.0, np0 * math.exp(-na * (n - 1.0))) ** n for n in ns], ys)
                if err < best_err:
                    best_err = err
                    best_p0, best_alpha = np0, na
                    improved = True
        if not improved:
            step_p *= 0.5
            step_a *= 0.5
    return best_p0, best_alpha, best_err


def fit_ifscale_exp(ks: list[int], accs: list[float]) -> tuple[float, float]:
    """1-parameter exponential dilution p(k) = p_10 * exp(-alpha * (k - 10))."""
    p0 = accs[0]
    best_alpha, best_err = 0.0, float("inf")
    for ai in range(0, 151):
        alpha = ai * 0.0002
        err = rmse([p0 * math.exp(-alpha * (k - 10)) for k in ks], accs)
        if err < best_err:
            best_err = err
            best_alpha = alpha
    step = 0.0001
    for _ in range(12):
        improved = False
        for sa in (-1, 1):
            na = max(0.0, best_alpha + sa * step)
            err = rmse([p0 * math.exp(-na * (k - 10)) for k in ks], accs)
            if err < best_err:
                best_err = err
                best_alpha = na
                improved = True
        if not improved:
            step *= 0.5
    return best_alpha, best_err


def fit_ifscale_logistic(ks: list[int], accs: list[float]) -> tuple[float, float, float]:
    """2-parameter logistic threshold curve p(k) = 1 / (1 + exp(s * (k - k50)))."""
    best_k50, best_s, best_err = 250.0, 0.01, float("inf")
    for k50 in range(30, 801, 20):
        for s_i in range(1, 61):
            s = s_i * 0.001
            preds = [1.0 / (1.0 + math.exp(max(-40.0, min(40.0, s * (k - k50))))) for k in ks]
            err = rmse(preds, accs)
            if err < best_err:
                best_err = err
                best_k50, best_s = float(k50), s
    step_k, step_s = 10.0, 0.001
    for _ in range(12):
        improved = False
        for dk in (-1, 0, 1):
            for ds in (-1, 0, 1):
                if dk == 0 and ds == 0:
                    continue
                nk = max(10.0, best_k50 + dk * step_k)
                ns_ = max(0.0005, best_s + ds * step_s)
                preds = [1.0 / (1.0 + math.exp(max(-40.0, min(40.0, ns_ * (k - nk))))) for k in ks]
                err = rmse(preds, accs)
                if err < best_err:
                    best_err = err
                    best_k50, best_s = nk, ns_
                    improved = True
        if not improved:
            step_k *= 0.5
            step_s *= 0.5
    return best_k50, best_s, best_err


def max_safe_k(p0: float, alpha: float, sla: float, k_cap: int = 200) -> int:
    """Largest integer k >= 0 with p(k)^k >= sla where p(k) = p0 * exp(-alpha * (k - 1))."""
    k_best = 0
    for k in range(1, k_cap + 1):
        pk = p0 * math.exp(-alpha * (k - 1))
        if (pk ** k) >= sla:
            k_best = k
        else:
            break
    return k_best


# =============================================================================
# PROBE 1: Multi-Constraint Compounding & Safe Constraint Budget k_max
# =============================================================================

def run_probe_1() -> None:
    print("=" * 94)
    print("PROBE 1 [derived fit to published table]: Multi-Constraint Compounding & Safe Budget k_max")
    print("=" * 94)

    # 1A. ManyIFEval (n = 1..10): Honest Out-of-Sample & Complexity-Matched Comparison
    print("\n[1A] ManyIFEval (arXiv:2509.21051v1, App. F.1 Tables 8-9, n=1..10):")
    print("     Comparing: Indep0 (0-param p_1^n), Const1 (1-param fitted p_c^n),")
    print("                Dil_OOS (trained ONLY on MANYIFEVAL_INST -> OOS predict prompt_ys),")
    print("                and 2-param in-sample BetaBinom (BB) vs. Prompt-Dilution (Dil) via AICc.")
    print(f"{'Model':<18} {'Emp@10':>6} {'Ind0@10':>7} {'OOS@10':>6} | "
          f"{'RMSE_I0':>7} {'RMSE_C1':>7} {'RMSE_BB':>7} {'RMSE_OOS':>8} | {'dAICc(D-C1)':>11} {'a_inst':>6}")
    print("-" * 96)

    ind0_biases_10 = []
    ind0_rmses = []
    c1_rmses = []
    bb_rmses = []
    oos_rmses = []
    oos_beats_c1 = 0
    dil_aicc_wins = 0
    ns_f = [float(n) for n in MANYIFEVAL_N]
    p_fit_notes = []

    for model, py in MANYIFEVAL_PROMPT.items():
        iy = MANYIFEVAL_INST[model]
        # 0-param independent Bernoulli from exact observed p_1 (no clamping)
        p1 = iy[0]
        ind0_preds = [p1 ** n for n in MANYIFEVAL_N]
        rmse_i0 = rmse(ind0_preds, py)

        # 1-param constant-rate Bernoulli fitted across all 10 prompt_ys
        pc, rmse_c1 = fit_const_bernoulli(ns_f, py)
        c1_preds = [pc ** n for n in MANYIFEVAL_N]
        aicc_c1 = aicc_gaussian(c1_preds, py, n_params=1)

        # Out-of-sample attention-dilution trained STRICTLY on MANYIFEVAL_INST (zero prompt_ys access)
        p0_inst, a_inst, _ = fit_marginal_exp_dilution(ns_f, iy)
        oos_preds = [min(1.0, p0_inst * math.exp(-a_inst * (n - 1))) ** n for n in MANYIFEVAL_N]
        rmse_oos = rmse(oos_preds, py)

        # 2-param in-sample fits on prompt_ys (Beta-Binomial vs Prompt-Dilution)
        a_bb, b_bb, rmse_bb = fit_beta_binomial(ns_f, py)
        p0_d, a_d, _ = fit_prompt_exp_dilution(ns_f, p1, py)
        dil_preds = [min(1.0, p0_d * math.exp(-a_d * (n - 1))) ** n for n in MANYIFEVAL_N]
        aicc_d = aicc_gaussian(dil_preds, py, n_params=2)
        daicc = aicc_d - aicc_c1
        p_fit_10 = min(1.0, p0_d * math.exp(-a_d * 9.0))
        if abs(p_fit_10 - iy[-1]) >= 0.02:
            p_fit_notes.append(f"{model} ({p_fit_10:.3f} vs {iy[-1]:.3f})")

        ind0_biases_10.append(ind0_preds[-1] - py[-1])
        ind0_rmses.append(rmse_i0)
        c1_rmses.append(rmse_c1)
        bb_rmses.append(rmse_bb)
        oos_rmses.append(rmse_oos)
        if rmse_oos < rmse_c1:
            oos_beats_c1 += 1
        if daicc < 0.0:
            dil_aicc_wins += 1

        print(f"{model:<18} {py[-1]:6.3f} {ind0_preds[-1]:7.3f} {oos_preds[-1]:6.3f} | "
              f"{rmse_i0:7.3f} {rmse_c1:7.3f} {rmse_bb:7.3f} {rmse_oos:8.3f} | "
              f"{daicc:+11.1f} {a_inst:6.4f}")

    mean_ind0_bias_10 = statistics.mean(ind0_biases_10)
    mean_i0_rmse = statistics.mean(ind0_rmses)
    mean_c1_rmse = statistics.mean(c1_rmses)
    mean_bb_rmse = statistics.mean(bb_rmses)
    mean_oos_rmse = statistics.mean(oos_rmses)
    print(f"Summary (8 models, n=1..10): Indep0 RMSE={mean_i0_rmse:.3f} (bias@10={mean_ind0_bias_10:+.3f}) | "
          f"Const1 RMSE={mean_c1_rmse:.3f} | BetaBinom RMSE={mean_bb_rmse:.3f} | "
          f"Dil_OOS (INST-only) RMSE={mean_oos_rmse:.3f} (beats Const1 on {oos_beats_c1}/8; "
          f"in-sample Dil beats Const1 by AICc on {dil_aicc_wins}/8).")
    print("Residual shortfall note: Prompt-fitted p_fit(10) < empirical Inst@10 on "
          + ", ".join(p_fit_notes) + " (reflecting cross-constraint interference beyond marginal decay).")

    # 1B. IFScale (k = 10..500, keyword-inclusion only): Exp vs Logistic Multi-Point Fit
    print("\n[1B] IFScale (arXiv:2507.11538v1, App. A Table 1, k=10..500, keyword-inclusion only):")
    print(f"{'Model':<18} {'Emp@10':>6} {'Emp@100':>7} {'Emp@500':>7} | "
          f"{'NoDilOver':>9} | {'Exp_RMSE':>8} {'Log_RMSE':>8} | {'alpha_k':>8} {'k_50':>6}")
    print("-" * 94)
    ifscale_overpreds = []
    for model, accs in IFSCALE_ACC.items():
        ak, err_exp = fit_ifscale_exp(IFSCALE_K, accs)
        k50, _, err_log = fit_ifscale_logistic(IFSCALE_K, accs)
        over = accs[0] - accs[-1]
        ifscale_overpreds.append(over)
        print(f"{model:<18} {accs[0]:6.3f} {accs[2]:7.3f} {accs[-1]:7.3f} | "
              f"{over:+9.3f} | {err_exp:8.3f} {err_log:8.3f} | {ak:8.5f} {k50:6.1f}")

    # 1C. MTAC-IFBench: All 11 Claude Code models + Honest All-8 Shared OpenCode Ratio Check
    print("\n[1C] MTAC-IFBench (arXiv:2609.14992v1, Table 2 Claude Code & Table 5 OpenCode, avg n=12.97):")
    cc_zero_t78 = sum(1 for d in MTAC_CLAUDE_CODE.values() if d["cisr"][3] == 0.0)
    cc_zero_t910 = sum(1 for d in MTAC_CLAUDE_CODE.values() if d["cisr"][4] == 0.0)
    oc_zero_t78 = sum(1 for d in MTAC_OPENCODE.values() if d["cisr"][3] == 0.0)
    oc_zero_t910 = sum(1 for d in MTAC_OPENCODE.values() if d["cisr"][4] == 0.0)
    print(f"     Late-turn C-ISR collapse to 0.0%: CC T7-8={cc_zero_t78}/11, T9-10={cc_zero_t910}/11 | "
          f"OC T7-8={oc_zero_t78}/8, T9-10={oc_zero_t910}/8.")
    print(f"{'Shared Model (8/8)':<18} {'CC_CSR':>6} {'OC_CSR':>6} | {'CC_CISR':>7} {'OC_CISR':>7} | "
          f"{'PredRatio':>9} {'ObsRatio':>8} | {'Status'}")
    print("-" * 94)

    close_matches = 0
    sign_reversals = 0
    for model, oc in MTAC_OPENCODE.items():
        cc = MTAC_CLAUDE_CODE[model]
        csr_ratio = oc["csr_avg"] / cc["csr_avg"]
        pred_ratio = csr_ratio ** MTAC_AVG_CONSTRAINTS
        obs_ratio = oc["cisr_avg"] / cc["cisr_avg"]
        pred_dir = 1 if pred_ratio > 1.0 else -1
        obs_dir = 1 if obs_ratio > 1.0 else -1
        if pred_dir != obs_dir:
            status = "SIGN REVERSAL"
            sign_reversals += 1
        elif abs(pred_ratio - obs_ratio) <= 0.06:
            status = "MATCH (<=0.06)"
            close_matches += 1
        else:
            status = "MISS (mag)"
        print(f"{model:<18} {cc['csr_avg']:6.3f} {oc['csr_avg']:6.3f} | "
              f"{cc['cisr_avg']:7.3f} {oc['cisr_avg']:7.3f} | "
              f"{pred_ratio:9.3f} {obs_ratio:8.3f} | {status}")
    print(f"All-8 Honest Verdict: (CSR_OC/CSR_CC)^12.97 closely matches {close_matches}/8 models, "
          f"misses magnitude on {8 - close_matches - sign_reversals}/8, and reverses sign on {sign_reversals}/8 "
          "(Qwen3.6-Plus C-ISR rises 2.0%->2.4%; Qwen3.5-27B CSR rises 60.6%->61.8%).")
    print("Note: Across Claude Code top-5 models, C-ISR is 1.98x-9.43x higher than CSR_avg^12.97")
    print("      due to Jensen's inequality across heterogeneous tasks and lower early-turn n_t.")

    # 1D. Derived Safe Constraint Budget k_max Table
    print("\n[1D] Derived Safe Simultaneous Active Constraint Budget k_max (Strict All-Met SLA):")
    regimes = [
        ("Zero dilution ceiling (alpha=0.000)", 0.000),
        ("Mild LRM dilution (alpha=0.004, DeepSeek-R1 / o3-mini-low INST)", 0.004),
        ("Moderate dilution (alpha=0.011, GPT-4o / DeepSeek-V3 INST)", 0.011),
        ("Strong dilution (alpha=0.026, Qwen2.5-72B INST)", 0.026),
    ]
    p_grid = [0.90, 0.95, 0.98, 0.99]
    slas = [0.80, 0.90, 0.95]
    for rname, alpha in regimes:
        print(f"\n  Regime: {rname}")
        print(f"    {'p_0':<6} | {'SLA>=80%':>10} {'SLA>=90%':>10} {'SLA>=95%':>10}")
        for p0 in p_grid:
            ks = [max_safe_k(p0, alpha, s) for s in slas]
            print(f"    {p0:<6.2f} | {ks[0]:>10d} {ks[1]:>10d} {ks[2]:>10d}")

    # 1E. Non-Vacuity & Negative-Control Assertions
    assert mean_ind0_bias_10 > 0.25, f"Expected severe Indep0 over-prediction, got {mean_ind0_bias_10}"
    assert mean_oos_rmse < mean_i0_rmse / 4.0, "Out-of-sample INST dilution must beat Indep0 RMSE by >4x"
    assert mean_oos_rmse < mean_c1_rmse, "Out-of-sample INST dilution must beat in-sample Const1 mean RMSE"
    assert close_matches == 3 and sign_reversals == 2, f"Expected 3/8 matches and 2/8 sign reversals, got {close_matches}/{sign_reversals}"
    assert min(ifscale_overpreds) > 0.28, "Zero-dilution must over-predict IFScale k=500 by >28 pp"
    assert max_safe_k(0.95, 0.0, 0.90) == 2 and max_safe_k(0.98, 0.011, 0.80) < max_safe_k(0.98, 0.0, 0.80)
    print(f"\n[NEG-CTRL PASS] Probe 1: Zero-dilution (alpha=0) over-predicts ManyIFEval n=10 by "
          f"{mean_ind0_bias_10*100:+.1f} pp (RMSE={mean_i0_rmse:.3f} vs OOS INST-trained dilution "
          f"RMSE={mean_oos_rmse:.3f}) and IFScale k=500 by "
          f"{min(ifscale_overpreds)*100:+.1f} to {max(ifscale_overpreds)*100:+.1f} pp.")


# =============================================================================
# PROBE 2: Skill / Tool Catalog Routing Phase Transition & Disambiguation Sweep
# =============================================================================

@dataclass(frozen=True)
class RoutingRegime:
    name: str
    overlap_intra: float    # semantic bleed from same-cluster distractors
    overlap_cross: float    # semantic bleed from cross-cluster distractors
    r1_defect_rate: float   # fraction of skills with R1 routing defect (138K-SKILL.md: 0.67)
    r1_signal_drop: float   # target score drop when R1-defective
    excl_bonus: float       # margin added by explicit negative exclusions
    ctx_rot_per_1k: float   # LLM attention noise per 1,000 injected prompt tokens


def simulate_routing(
    rng: random.Random,
    M: int,
    regime: RoutingRegime,
    active_gains: tuple[float, ...] = (0.0,),
    n_trials: int = 400,
    top_k: int = 3,
    cluster_size_target: int = 10,
    tok_per_skill: int = 100,
) -> dict[str, float]:
    """Parameterized Gaussian signal-detection surrogate ([toy model]).

    Evaluates Flat, Passive Top-K, and 2-level Hierarchy across one or more
    active_gains in a single paired pass over identical catalog draws for
    single-relevant queries (Top-3 Precision@3 upper bound = 1/3 = 33.3%):
      (a) Flat injection: all M skills in context; noise grows with ctx_rot_per_1k.
      (b) Passive Top-K retrieval: raw-query embedding noise sigma_emb, then LLM selects
          among Top-K with zero artificial carryover penalty.
      (c) 2-level hierarchical discovery:
          - At active_gain = 0.0 (EQUAL-FOOTED): Stage 1 uses the exact same sigma_emb,
            r1_signal_drop, and cross-cluster bleed as Passive Top-K, and Stage 2 uses
            the exact same intra-cluster bleed. No hidden bonuses.
          - At active_gain = g in (0, 1]: linearly interpolates how much an agent-authored
            structured (domain, operation) query narrows the query-to-spec semantic gap
            (sigma_s1 = sigma_emb - g*(sigma_emb - sigma_llm), R1 drop scaled by 1-0.6*g,
            bleed scaled by 1-0.4*g).
    """
    n_clusters = max(1, math.ceil(M / cluster_size_target))
    c_size = M / n_clusters

    flat_hits = 0
    topk_recalls = 0
    topk_top1_hits = 0
    hier_hits = [0 for _ in active_gains]

    sigma_llm = 0.16
    sigma_emb = 0.22

    flat_tokens = M * tok_per_skill
    sigma_flat = math.hypot(sigma_llm, regime.ctx_rot_per_1k * (flat_tokens / 1000.0))

    topk_tokens = min(M, top_k) * tok_per_skill + 50
    sigma_s2_topk = math.hypot(sigma_llm, regime.ctx_rot_per_1k * (topk_tokens / 1000.0))

    s1_tokens = min(n_clusters * 35, 500)
    s2_tokens = min(math.ceil(c_size), cluster_size_target) * tok_per_skill
    hier_tokens = s1_tokens + s2_tokens

    hier_params = []
    for g in active_gains:
        sigma_s1_base = sigma_emb - g * (sigma_emb - sigma_llm)
        s_h1 = math.hypot(sigma_s1_base, regime.ctx_rot_per_1k * (s1_tokens / 1000.0))
        s_h2 = math.hypot(sigma_llm, regime.ctx_rot_per_1k * (s2_tokens / 1000.0))
        hier_params.append((s_h1, s_h2, 1.0 - 0.60 * g, 1.0 - 0.40 * g))

    n_intra = max(0, round(c_size) - 1)
    n_cross = max(0, M - 1 - n_intra)
    mu_intra = max(0.0, regime.overlap_intra - regime.excl_bonus)
    mu_cross = max(0.0, regime.overlap_cross - regime.excl_bonus)

    gauss = rng.gauss
    rand = rng.random

    for _ in range(n_trials):
        is_r1_defective = rand() < regime.r1_defect_rate
        mu_t = 1.0 - (regime.r1_signal_drop if is_r1_defective else 0.0)

        # --- (a) Flat Startup Injection & (b) Passive Top-K Retrieval ---
        s_t_flat = gauss(mu_t, sigma_flat)
        s_t_emb = gauss(mu_t, sigma_emb)
        max_d_flat = -1e9
        higher_emb = 0
        # Keep top-(top_k) distractor (score, latent_mu) inline without lambda overhead
        k_scores = [-1e9] * top_k
        k_mus = [0.0] * top_k
        min_k_val = -1e9
        min_k_idx = 0

        for _ in range(n_intra):
            vf = gauss(mu_intra, sigma_flat)
            if vf > max_d_flat:
                max_d_flat = vf
            ve = gauss(mu_intra, sigma_emb)
            if ve > s_t_emb:
                higher_emb += 1
            if ve > min_k_val:
                k_scores[min_k_idx] = ve
                k_mus[min_k_idx] = mu_intra
                min_k_idx = 0
                min_k_val = k_scores[0]
                for ii in range(1, top_k):
                    if k_scores[ii] < min_k_val:
                        min_k_val = k_scores[ii]
                        min_k_idx = ii

        for _ in range(n_cross):
            vf = gauss(mu_cross, sigma_flat)
            if vf > max_d_flat:
                max_d_flat = vf
            ve = gauss(mu_cross, sigma_emb)
            if ve > s_t_emb:
                higher_emb += 1
            if ve > min_k_val:
                k_scores[min_k_idx] = ve
                k_mus[min_k_idx] = mu_cross
                min_k_idx = 0
                min_k_val = k_scores[0]
                for ii in range(1, top_k):
                    if k_scores[ii] < min_k_val:
                        min_k_val = k_scores[ii]
                        min_k_idx = ii

        if s_t_flat > max_d_flat:
            flat_hits += 1

        if higher_emb < top_k:
            topk_recalls += 1
            s_t_s2 = gauss(mu_t, sigma_s2_topk)
            # Pick top-(top_k - 1) distractors by score
            pairs = sorted(zip(k_scores, k_mus), reverse=True)
            best_d_s2 = -1e9
            for sc, d_mu in pairs[: min(top_k - 1, M - 1)]:
                if sc <= -1e8:
                    continue
                v2 = gauss(d_mu, sigma_s2_topk)
                if v2 > best_d_s2:
                    best_d_s2 = v2
            if s_t_s2 > best_d_s2:
                topk_top1_hits += 1

        # --- (c) 2-Level Hierarchical Discovery across active_gains ---
        for gi, (s_h1, s_h2, r1_sc, bl_sc) in enumerate(hier_params):
            mu_c_target = 1.0 - (r1_sc * regime.r1_signal_drop if is_r1_defective else 0.0)
            s_c_target = gauss(mu_c_target, s_h1)
            max_c_dist = -1e9
            c_bleed = bl_sc * mu_cross
            for _ in range(n_clusters - 1):
                vc = gauss(c_bleed, s_h1)
                if vc > max_c_dist:
                    max_c_dist = vc
            if s_c_target > max_c_dist:
                s_t_h2 = gauss(mu_t, s_h2)
                max_d_h2 = -1e9
                h2_intra = bl_sc * mu_intra
                for _ in range(n_intra):
                    vh = gauss(h2_intra, s_h2)
                    if vh > max_d_h2:
                        max_d_h2 = vh
                if s_t_h2 > max_d_h2:
                    hier_hits[gi] += 1

    out: dict[str, float] = {
        "flat_acc": flat_hits / n_trials,
        "flat_tok": float(flat_tokens),
        "topk_hit3": topk_recalls / n_trials,
        "topk_acc": topk_top1_hits / n_trials,
        "topk_tok": float(topk_tokens),
        "hier_tok": float(hier_tokens),
    }
    for gi, g in enumerate(active_gains):
        out[f"hier_g{g:.2f}"] = hier_hits[gi] / n_trials
    return out


def run_probe_2() -> None:
    print("\n" + "=" * 94)
    print("PROBE 2 [toy model / mechanistic surrogate]: Catalog Routing & Active-Query Sensitivity")
    print("=" * 94)
    print("Published Empirical Context (NOT fitted directly by this surrogate):")
    print("  - MCP-Zero (2506.01056v4): API-Bank Table 1 (48 flat tools, no server hierarchy):")
    print("      -98.24% tokens (6,308->111), 95.2-96.6% top-1 vs 71.6% Q.Retrieval; MCP-tools")
    print("      NIAH (308 srv/2,797 tools, Figs 5-6) lifts Claude-3.5/Gemini-2.5, NULL on GPT-4.1.")
    print("  - Vector-MCP (2603.20313v1, Table 1, M=121 offline retrieval, multi-relevant):")
    print("      Hit@3=97.1%, P@3=57.6%, R@3=59.6%, F1@3=58.4% (99.6% token figure excluded: broken).")
    print("  - 138K-SKILL.md (2608.08453v1, Table 1 & §3.4): 67.0% R1 defect rate; lexical BM25 only")
    print("      (88.5% R1-clean vs 82.6% R1-defective hit@1; not LLM-as-selector).")
    print("  - RAG-MCP (2505.03275v1, directional only due to registry/evaluator inconsistencies):")
    print("      semantic retrieval outperforms flat injection (43.13% vs 13.62%).")

    crisp_reg = RoutingRegime(
        name="Crisp + Exclusions (0% R1 defects)",
        overlap_intra=0.36, overlap_cross=0.22,
        r1_defect_rate=0.00, r1_signal_drop=0.14,
        excl_bonus=0.12, ctx_rot_per_1k=0.022,
    )
    pushy_reg = RoutingRegime(
        name="Pushy Overlap + 67% R1 Defects (Ecosystem)",
        overlap_intra=0.56, overlap_cross=0.38,
        r1_defect_rate=0.67, r1_signal_drop=0.14,
        excl_bonus=0.00, ctx_rot_per_1k=0.022,
    )
    catalog_sizes = [5, 15, 30, 50, 100, 200, 300]
    results: dict[str, dict[int, dict[str, float]]] = {}

    for reg in (crisp_reg, pushy_reg):
        print(f"\n[toy model] Regime: {reg.name} (single-relevant queries; ctx_rot=0.022/1k tok)")
        print(f"{'M':>4} | {'FlatAcc':>7} {'FlatTok':>7} | {'Top3R@3':>7} {'Top3Acc':>7} {'Top3Tok':>7} | "
              f"{'Hier(g=0)':>9} {'Hier(g=.5)':>10} {'Hier(g=1)':>9} {'HierTok':>7}")
        print("-" * 94)
        res_map: dict[int, dict[str, float]] = {}
        for M in catalog_sizes:
            r = simulate_routing(
                random.Random(SEED + M), M, reg, active_gains=(0.0, 0.5, 1.0), n_trials=400
            )
            res_map[M] = {
                **r,
                "hier_g0": r["hier_g0.00"],
                "hier_g05": r["hier_g0.50"],
                "hier_g10": r["hier_g1.00"],
            }
            print(f"{M:4d} | {r['flat_acc']*100:6.1f}% {r['flat_tok']:7.0f} | "
                  f"{r['topk_hit3']*100:6.1f}% {r['topk_acc']*100:6.1f}% {r['topk_tok']:7.0f} | "
                  f"{r['hier_g0.00']*100:8.1f}% {r['hier_g0.50']*100:9.1f}% {r['hier_g1.00']*100:8.1f}% "
                  f"{r['hier_tok']:7.0f}")
        results[reg.name] = res_map

    # Context-Rot Sensitivity Sweep for Flat < 90% Crossover M* (Crisp Regime)
    print("\n[toy model sensitivity] Crisp Flat < 90% crossover M* across ctx_rot_per_1k:")
    sweep_parts = []
    for rot in (0.005, 0.010, 0.022, 0.040):
        reg_s = RoutingRegime(
            name=f"rot={rot}", overlap_intra=0.36, overlap_cross=0.22,
            r1_defect_rate=0.0, r1_signal_drop=0.14, excl_bonus=0.12, ctx_rot_per_1k=rot,
        )
        m_star = ">300"
        for M in catalog_sizes:
            r = simulate_routing(random.Random(SEED + M), M, reg_s, active_gains=(), n_trials=300)
            if r["flat_acc"] < 0.90:
                m_star = str(M)
                break
        sweep_parts.append(f"rot={rot:.3f} -> M*={m_star}")
    print("  " + " | ".join(sweep_parts))

    # Decoupled Negative Controls (separating overlap=0 from ctx_rot=0)
    nc_both_zero = RoutingRegime("both=0", 0.0, 0.0, 0.0, 0.0, 0.0, 0.0)
    nc_ov_only = RoutingRegime("overlap=0,rot=0.022", 0.0, 0.0, 0.0, 0.0, 0.0, 0.022)
    nc_rot_only = RoutingRegime("pushy,rot=0.0", 0.56, 0.38, 0.67, 0.14, 0.0, 0.0)

    r_both_300 = simulate_routing(random.Random(SEED), 300, nc_both_zero, active_gains=(), n_trials=400)
    r_ov0_100 = simulate_routing(random.Random(SEED), 100, nc_ov_only, active_gains=(), n_trials=400)
    r_ov0_300 = simulate_routing(random.Random(SEED), 300, nc_ov_only, active_gains=(), n_trials=400)
    r_rot0_30 = simulate_routing(random.Random(SEED), 30, nc_rot_only, active_gains=(), n_trials=400)
    r_rot0_100 = simulate_routing(random.Random(SEED), 100, nc_rot_only, active_gains=(), n_trials=400)

    crisp = results[crisp_reg.name]
    pushy = results[pushy_reg.name]

    print("\n[DECOUPLED NEGATIVE CONTROLS] (separating overlap=0 from ctx_rot=0):")
    print(f"  1. overlap=0 AND ctx_rot=0: FlatAcc@300 = {r_both_300['flat_acc']*100:.1f}% (both failure modes off)")
    print(f"  2. overlap=0 WITH ctx_rot=0.022: FlatAcc@100 = {r_ov0_100['flat_acc']*100:.1f}%, "
          f"FlatAcc@300 = {r_ov0_300['flat_acc']*100:.1f}% (length rot persists even at overlap=0)")
    print(f"  3. pushy overlap WITH ctx_rot=0: FlatAcc@30 = {r_rot0_30['flat_acc']*100:.1f}%, "
          f"FlatAcc@100 = {r_rot0_100['flat_acc']*100:.1f}% (semantic collision persists even at rot=0)")
    print(f"  4. Equal-footed check (Pushy @ M=100): Top-3={pushy[100]['topk_acc']*100:.1f}% vs "
          f"Hier(g=0)={pushy[100]['hier_g0']*100:.1f}% vs Hier(g=1)={pushy[100]['hier_g10']*100:.1f}%")
    print("     -> Pure 2-level hierarchy (g=0) does NOT beat Top-3; gains require active disambiguation (g>0).")

    assert r_both_300["flat_acc"] >= 0.99
    assert r_ov0_300["flat_acc"] < 0.60, "Context rot alone should still degrade FlatAcc@300"
    assert r_rot0_100["flat_acc"] < 0.70, "Pushy overlap alone should degrade FlatAcc@100 even with rot=0"
    assert crisp[30]["flat_acc"] > pushy[30]["flat_acc"] + 0.15
    assert pushy[100]["hier_g0"] <= pushy[100]["topk_acc"] + 0.05, "Equal-footed g=0 must not get hidden lift"
    assert pushy[100]["hier_g10"] > pushy[100]["hier_g0"] + 0.15, "Active query gain g=1 must drive lift"
    assert pushy[300]["hier_tok"] < pushy[300]["flat_tok"] * 0.10
    print("[NEG-CTRL PASS] Probe 2: Decoupled overlap/ctx_rot controls and equal-footed hierarchy check passed.")


# =============================================================================
# PROBE 3: Multi-Turn Sharding & Progressive-Disclosure Pull-Through Surrogate
# =============================================================================

def eval_turn_survival(
    T: int,
    m_core: int,
    m_deferred: int,
    p_guided: float,
    p_prior: float,
    bloat_penalty: float,
    gamma_turn: float,
    q_trig: float,
    e_comp: float,
    eviction_mode: str = "coupled",
) -> float:
    """Analytical Turn-T strict all-obligations survival ([toy model]).

    States track joint context occupancy (core_in_ctx, ref_in_ctx):
      0=(False, False), 1=(True, False), 2=(False, True), 3=(True, True)
    Eviction modes:
      - "coupled": shared sliding-window eviction; State 3 -> 3 w.p. (1 - e_comp),
                   State 3 -> 0 w.p. e_comp (State 2 remains unreachable).
      - "independent": core and ref observations evict independently w.p. e_comp
                       per turn boundary (State 3 -> {0,1,2,3} with binomial probs).
    """
    if eviction_mode not in ("coupled", "independent"):
        raise ValueError(f"Unsupported eviction_mode: {eviction_mode}")

    prob = [0.0, 1.0 - q_trig, 0.0, q_trig]
    for _ in range(2, T + 1):
        s = 1.0 - e_comp
        e = e_comp
        nxt = [0.0, 0.0, 0.0, 0.0]
        nxt[0] += prob[0]
        nxt[1] += prob[1] * s
        nxt[0] += prob[1] * e
        nxt[2] += prob[2] * s
        nxt[0] += prob[2] * e
        if eviction_mode == "coupled":
            nxt[3] += prob[3] * s
            nxt[0] += prob[3] * e
        else:
            nxt[3] += prob[3] * (s * s)
            nxt[1] += prob[3] * (s * e)
            nxt[2] += prob[3] * (e * s)
            nxt[0] += prob[3] * (e * e)
        prob = nxt

    p_eff = max(p_prior, (p_guided - bloat_penalty) * math.exp(-gamma_turn * (T - 1)))
    rate_00 = (p_prior ** m_core) * (p_prior ** m_deferred)
    rate_10 = (p_eff ** m_core) * (p_prior ** m_deferred)
    rate_01 = (p_prior ** m_core) * (p_eff ** m_deferred)
    rate_11 = (p_eff ** m_core) * (p_eff ** m_deferred)
    return prob[0] * rate_00 + prob[1] * rate_10 + prob[2] * rate_01 + prob[3] * rate_11


def mc_check_probe_3(
    rng: random.Random,
    T: int,
    m_core: int,
    m_deferred: int,
    p_guided: float,
    p_prior: float,
    bloat_penalty: float,
    gamma_turn: float,
    q_trig: float,
    e_comp: float,
    eviction_mode: str = "coupled",
    n_trials: int = 4000,
) -> float:
    """Seeded Monte Carlo cross-check for both coupled and independent eviction."""
    wins = 0
    for _ in range(n_trials):
        core_in = True
        ref_in = rng.random() < q_trig
        for _ in range(2, T + 1):
            if eviction_mode == "coupled":
                if rng.random() < e_comp:
                    core_in = False
                    ref_in = False
            else:
                if core_in and rng.random() < e_comp:
                    core_in = False
                if ref_in and rng.random() < e_comp:
                    ref_in = False
        p_eff = max(p_prior, (p_guided - bloat_penalty) * math.exp(-gamma_turn * (T - 1)))
        pc = p_eff if core_in else p_prior
        pd = p_eff if ref_in else p_prior
        ok = all(rng.random() < pc for _ in range(m_core)) and all(
            rng.random() < pd for _ in range(m_deferred)
        )
        if ok:
            wins += 1
    return wins / n_trials


def compute_q_star(
    T: int,
    m_core: int,
    m_def: int,
    p_guided: float,
    p_prior: float,
    bloat_single: float,
    bloat_split: float,
    gamma_turn: float,
) -> float:
    """Closed-form q_trig* at Turn T where Split references/ equals Single-File."""
    p_sp = max(p_prior, (p_guided - bloat_split) * math.exp(-gamma_turn * (T - 1)))
    p_sg = max(p_prior, (p_guided - bloat_single) * math.exp(-gamma_turn * (T - 1)))
    single_rate = p_sg ** (m_core + m_def)
    denom = (p_sp ** m_def) - (p_prior ** m_def)
    if denom <= 1e-12:
        return 0.0
    q_star = ((single_rate / (p_sp ** m_core)) - (p_prior ** m_def)) / denom
    return max(0.0, min(1.0, q_star))


def run_probe_3() -> None:
    print("\n" + "=" * 94)
    print("PROBE 3 [toy model / mechanistic surrogate]: Progressive-Disclosure Pull-Through & Eviction")
    print("=" * 94)
    print("Published Empirical Context (NOT fitted directly by this surrogate):")
    print("  - SkillsBench (2602.12670v4, Table 9; observational, N=5 in Comprehensive, Standard")
    print("      No-Skills baseline 19.8% vs 37.6-39.3% elsewhere): Compact +19.0 / Standard +21.5")
    print("      vs Detailed +14.5 / Comprehensive +0.7 pp.")
    print("  - Lost in Conversation (2505.06120v1): -39% sharding drop; Snowball recovers 15-20%.")
    print("  - agentskills adding-skills-support.mdx (L306-326): dedicated activation tools should")
    print("      not eagerly read references/; un-exempt skill observations face compaction eviction.")

    # Illustrative scenario: 4 obligations (2 core + 2 task-critical details).
    # Bloat penalties match comments exactly: compact=0.008, standard=0.025,
    # detailed=0.065, comprehensive=0.145, split=0.000.
    m_core, m_def = 2, 2
    p_guided = 0.96
    p_prior = 0.72
    gamma_turn = 0.015
    bloat_compact = 0.008
    bloat_comprehensive = 0.145
    bloat_split = 0.000

    print("\n[3A] Turn-T Strict All-Obligations Survival (T=1..8; coupled vs independent eviction):")
    for e_comp, mode, label in [
        (0.00, "coupled", "Compaction-Protected (e_comp=0.00)"),
        (0.15, "coupled", "Unprotected Coupled Sliding Window (e_comp=0.15/turn)"),
        (0.15, "independent", "Unprotected Independent Observation Eviction (e_comp=0.15/turn)"),
    ]:
        print(f"\n  {label}:")
        print(f"  {'T':>2} | {'Compact1F':>9} {'Compreh1F':>9} | "
              f"{'Ref q=.60':>9} {'Ref q=.80':>9} {'Ref q=.95':>9} {'Ref q=1.0':>9}")
        print("  " + "-" * 68)
        for T in (1, 2, 4, 6, 8):
            c1 = eval_turn_survival(T, m_core + m_def, 0, p_guided, p_prior, bloat_compact, gamma_turn, 1.0, e_comp, mode)
            m1 = eval_turn_survival(T, m_core + m_def, 0, p_guided, p_prior, bloat_comprehensive, gamma_turn, 1.0, e_comp, mode)
            refs = [
                eval_turn_survival(T, m_core, m_def, p_guided, p_prior, bloat_split, gamma_turn, q, e_comp, mode)
                for q in (0.60, 0.80, 0.95, 1.00)
            ]
            print(f"  {T:2d} | {c1*100:8.1f}% {m1*100:8.1f}% | "
                  f"{refs[0]*100:8.1f}% {refs[1]*100:8.1f}% {refs[2]*100:8.1f}% {refs[3]*100:8.1f}%")

    # 3B. 2D Sensitivity Grid for Pre-Trigger Blind-Spot Crossover q_trig* at Turn 1
    print("\n[3B] Sensitivity Range for Crossover q_trig* @ T=1 (Split >= Single-File; m_core=2, m_def=2):")
    p_priors = [0.50, 0.65, 0.72, 0.85]
    deltas = [0.004, 0.008, 0.015, 0.025, 0.040, 0.065, 0.145]
    header = "  delta \\ p_prior | " + " ".join(f"{pp:7.2f}" for pp in p_priors)
    print(header)
    print("  " + "-" * (len(header) - 2))
    q_grid_vals = []
    for d in deltas:
        row_vals = [compute_q_star(1, m_core, m_def, p_guided, pp, d, bloat_split, gamma_turn) for pp in p_priors]
        if 0.004 <= d <= 0.040:
            q_grid_vals.extend(row_vals)
        print(f"  delta={d:6.3f}    | " + " ".join(f"{q*100:6.1f}%" for q in row_vals))
    print(f"  Sensitivity range across delta in [0.004, 0.040] & p_prior in [0.50, 0.85]: "
          f"q_trig*@T1 spans {min(q_grid_vals)*100:.1f}% to {max(q_grid_vals)*100:.1f}%.")
    print("  Structural invariant: q_trig* decreases monotonically in both single-file bloat delta")
    print("  and unassisted baseline p_prior (no single universal constant).")

    # 3C. Analytical vs Seeded Monte Carlo Cross-Checks & Negative Controls
    ana_c = eval_turn_survival(4, m_core, m_def, p_guided, p_prior, bloat_split, gamma_turn, 0.80, 0.15, "coupled")
    mc_c = mc_check_probe_3(random.Random(SEED), 4, m_core, m_def, p_guided, p_prior, bloat_split, gamma_turn, 0.80, 0.15, "coupled", 4000)
    ana_i = eval_turn_survival(8, m_core, m_def, p_guided, p_prior, bloat_split, gamma_turn, 0.80, 0.15, "independent")
    mc_i = mc_check_probe_3(random.Random(SEED + 1), 8, m_core, m_def, p_guided, p_prior, bloat_split, gamma_turn, 0.80, 0.15, "independent", 4000)
    ana_c8 = eval_turn_survival(8, m_core, m_def, p_guided, p_prior, bloat_split, gamma_turn, 0.80, 0.15, "coupled")

    sp_perf_t8 = eval_turn_survival(8, m_core, m_def, p_guided, p_prior, bloat_split, gamma_turn, 1.00, 0.00, "coupled")
    cp_t8 = eval_turn_survival(8, m_core + m_def, 0, p_guided, p_prior, bloat_compact, gamma_turn, 1.00, 0.00, "coupled")
    cp_evict_t8 = eval_turn_survival(8, m_core + m_def, 0, p_guided, p_prior, bloat_compact, gamma_turn, 1.00, 0.15, "coupled")

    print(f"\n[MC CROSS-CHECK] Coupled T=4 (q=.80, e=.15): ana={ana_c*100:.2f}% vs MC={mc_c*100:.2f}% (|diff|={abs(ana_c-mc_c)*100:.2f} pp)")
    print(f"[MC CROSS-CHECK] Indep.  T=8 (q=.80, e=.15): ana={ana_i*100:.2f}% vs MC={mc_i*100:.2f}% (|diff|={abs(ana_i-mc_i)*100:.2f} pp)")
    print(f"[EVICTION DIFF]  T=8 (q=.80, e=.15): coupled={ana_c8*100:.2f}% vs independent={ana_i*100:.2f}% (delta={(ana_i-ana_c8)*100:+.2f} pp)")
    print(f"[NEG-CTRL 1] q_trig=1.00, e_comp=0.00 @ T=8: Split={sp_perf_t8*100:.1f}% >= Compact={cp_t8*100:.1f}% (blind spot vanishes)")
    print(f"[NEG-CTRL 2] Compaction exemption @ T=8: Protected={cp_t8*100:.1f}% vs Unprotected(0.15)={cp_evict_t8*100:.1f}% "
          f"(+{(cp_t8-cp_evict_t8)*100:.1f} pp durability gain)")

    assert abs(ana_c - mc_c) < 0.02
    assert abs(ana_i - mc_i) < 0.02
    assert ana_i < ana_c8, "Independent eviction must yield slightly lower T=8 survival than coupled eviction"
    assert sp_perf_t8 > cp_t8
    assert cp_t8 - cp_evict_t8 > 0.15
    assert min(q_grid_vals) < 0.40 and max(q_grid_vals) > 0.95, "2D sweep must confirm broad parameter sensitivity"
    print("[NEG-CTRL PASS] Probe 3: Coupled/independent MC cross-checks, monotonicity, and controls passed.")


def main() -> None:
    print(f"verify_instruction_routing_probes.py | seed={SEED} | stdlib-only deterministic run")
    run_probe_1()
    run_probe_2()
    run_probe_3()
    print("\n" + "=" * 94)
    print("ALL 3 PROBES & NEGATIVE CONTROLS PASSED (exit 0)")
    print("=" * 94)


if __name__ == "__main__":
    main()
