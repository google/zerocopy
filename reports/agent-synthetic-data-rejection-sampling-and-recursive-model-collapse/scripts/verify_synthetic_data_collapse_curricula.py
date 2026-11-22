#!/usr/bin/env python3
"""Deterministic verification probe for synthetic data collapse, verifier-filtered
rejection sampling, RLVR pass@k boundary dynamics, and deduplication forensics.

Executes with Python 3.10+ standard library only (`python3 -I -B`), < 2.0s wall
time, zero external network or disk side effects outside TemporaryDirectory, and
bit-identical stdout across PYTHONHASHSEED values.
"""

from __future__ import annotations

import bisect
import collections
import hashlib
import itertools
import math
import random
import re
import statistics
import string
import struct
import tempfile
import unicodedata
from pathlib import Path
from typing import Sequence


# ---------------------------------------------------------------------------
# Pure-stdlib linear algebra helpers (exact Gaussian elimination)
# ---------------------------------------------------------------------------

def solve_spd_linear_system(a_mat: list[list[float]], b_vec: list[float]) -> list[float]:
    """Solve A x = b for full-rank symmetric A via partial-pivoting elimination."""
    d = len(b_vec)
    aug = [row[:] + [b_vec[i]] for i, row in enumerate(a_mat)]
    for col in range(d):
        pivot_row = max(range(col, d), key=lambda r: abs(aug[r][col]))
        if abs(aug[pivot_row][col]) < 1e-13:
            raise ValueError("Singular normal matrix in OLS solve")
        if pivot_row != col:
            aug[col], aug[pivot_row] = aug[pivot_row], aug[col]
        piv = aug[col][col]
        for j in range(col, d + 1):
            aug[col][j] /= piv
        for r in range(d):
            if r != col and aug[r][col] != 0.0:
                factor = aug[r][col]
                for j in range(col, d + 1):
                    aug[r][j] -= factor * aug[col][j]
    return [aug[i][d] for i in range(d)]


def fit_ols(x_rows: Sequence[Sequence[float]], y_vals: Sequence[float], ridge: float = 0.0) -> list[float]:
    """Fit w_hat = (X^T X + ridge * I)^(-1) X^T y."""
    d = len(x_rows[0])
    xtx = [[0.0] * d for _ in range(d)]
    xty = [0.0] * d
    for x, y in zip(x_rows, y_vals):
        for i in range(d):
            xi = x[i]
            xty[i] += xi * y
            row_i = xtx[i]
            for j in range(i, d):
                row_i[j] += xi * x[j]
    for i in range(d):
        xtx[i][i] += ridge
        for j in range(i):
            xtx[i][j] = xtx[j][i]
    return solve_spd_linear_system(xtx, xty)


def dot(u: Sequence[float], v: Sequence[float]) -> float:
    return sum(ui * vi for ui, vi in zip(u, v))


def sq_dist(u: Sequence[float], v: Sequence[float]) -> float:
    return sum((ui - vi) ** 2 for ui, vi in zip(u, v))


# ---------------------------------------------------------------------------
# Probe 1: Replace vs. Accumulate vs. Accumulate-Subsample, Strong Collapse,
#          Gaussian/KDE Asymptotics, and Seddik Discrete Absorption
# ---------------------------------------------------------------------------

def run_probe_1() -> list[str]:
    lines: list[str] = []
    lines.append("=== Probe 1: Recursive Collapse Workflows, Strong Collapse & Discrete Absorption ===")

    # 1A. Isotropic linear regression workflows reproducing the three data-retention regimes in
    # RylanSchaeffer/KoyejoLab-Collapse-or-Thrive@38741731:src/fit_linear_regressions/fit_linear_regressions.py:L47-L80
    # and Gerstgrasser et al. (arXiv:2404.01413v2, Theorem 2, Eqs. 3-4).
    # Stdlib note: solves exact normal equations via Gaussian elimination and measures population excess
    # risk ||w_hat - w*||_2^2 (whereas KoyejoLab uses np.linalg.pinv and 1,000-sample empirical X_test MSE).
    d = 5
    t_per_iter = 26  # T >= d + 2; T - d - 1 = 20
    sigma = 1.0
    sigma_sq = sigma * sigma
    n_iters = 25
    n_trials = 120

    prefactor = (sigma_sq * d) / (t_per_iter - d - 1)  # exact = 5 / 20 = 0.25
    exact_replace_n = prefactor * n_iters  # 6.25
    exact_accum_n = prefactor * sum(1.0 / (i * i) for i in range(1, n_iters + 1))
    exact_accum_bound = prefactor * (math.pi ** 2 / 6.0)

    rng = random.Random(20260901)
    mse_replace = [0.0] * n_iters
    mse_accum = [0.0] * n_iters
    mse_accum_sub = [0.0] * n_iters

    for _ in range(n_trials):
        w_star = [rng.gauss(0.0, 1.0) for _ in range(d)]
        x_init = [[rng.gauss(0.0, 1.0) for _ in range(d)] for _ in range(t_per_iter)]
        y_init = [dot(x, w_star) + sigma * rng.gauss(0.0, 1.0) for x in x_init]

        xtx_init = [[0.0] * d for _ in range(d)]
        for x in x_init:
            for i in range(d):
                for j in range(i, d):
                    xtx_init[i][j] += x[i] * x[j]
        for i in range(d):
            for j in range(i):
                xtx_init[i][j] = xtx_init[j][i]

        y_rep = y_init[:]
        sum_xty_acc = [0.0] * d
        y_next_acc = y_init[:]
        pool_x = [row[:] for row in x_init]
        pool_y = y_init[:]

        for it in range(n_iters):
            xty_rep = [sum(x_init[r][i] * y_rep[r] for r in range(t_per_iter)) for i in range(d)]
            w_rep = solve_spd_linear_system(xtx_init, xty_rep)
            mse_replace[it] += sq_dist(w_rep, w_star)
            y_rep = [dot(x, w_rep) + sigma * rng.gauss(0.0, 1.0) for x in x_init]

            for r in range(t_per_iter):
                yr = y_next_acc[r]
                xr = x_init[r]
                for i in range(d):
                    sum_xty_acc[i] += xr[i] * yr
            mean_xty_acc = [v / (it + 1) for v in sum_xty_acc]
            w_acc = solve_spd_linear_system(xtx_init, mean_xty_acc)
            mse_accum[it] += sq_dist(w_acc, w_star)
            y_next_acc = [dot(x, w_acc) + sigma * rng.gauss(0.0, 1.0) for x in x_init]

            if it == 0:
                w_sub = fit_ols(pool_x, pool_y)
            else:
                idxs = rng.sample(range(len(pool_x)), t_per_iter)
                sub_x = [pool_x[idx] for idx in idxs]
                sub_y = [pool_y[idx] for idx in idxs]
                w_sub = fit_ols(sub_x, sub_y)
            mse_accum_sub[it] += sq_dist(w_sub, w_star)
            y_new_sub = [dot(x, w_sub) + sigma * rng.gauss(0.0, 1.0) for x in x_init]
            pool_x.extend(x_init)
            pool_y.extend(y_new_sub)

    mse_replace = [v / n_trials for v in mse_replace]
    mse_accum = [v / n_trials for v in mse_accum]
    mse_accum_sub = [v / n_trials for v in mse_accum_sub]

    assert abs(mse_replace[-1] - exact_replace_n) / exact_replace_n < 0.08
    assert abs(mse_accum[-1] - exact_accum_n) / exact_accum_n < 0.08
    assert exact_accum_n < exact_accum_bound
    assert mse_accum[-1] * 1.35 < mse_accum_sub[-1] < mse_replace[-1] * 0.25
    late_sub_ratio = mse_accum_sub[-1] / mse_accum_sub[14]
    late_rep_ratio = mse_replace[-1] / mse_replace[14]
    assert late_sub_ratio < 1.30 and late_rep_ratio > 1.55

    lines.append(
        "  [exact calculation of published theorem/equations] "
        f"Gerstgrasser Thm 2 (d={d}, T={t_per_iter}, n={n_iters}): "
        f"Replace={exact_replace_n:.4f}, Accum={exact_accum_n:.4f} <= pi^2/6_bound={exact_accum_bound:.4f}"
    )
    lines.append(
        "  [stdlib reproduction of pinned repository workflow] "
        f"KoyejoLab fit_linear_regressions.py MC (trials={n_trials}): "
        f"Replace={mse_replace[-1]:.4f}, AccumSubsample={mse_accum_sub[-1]:.4f}, Accum={mse_accum[-1]:.4f} "
        f"(late_ratio_15_to_25: Sub={late_sub_ratio:.3f} vs Rep={late_rep_ratio:.3f})"
    )

    # 1B. Shumailov 1D Gaussian W2^2 3/2-factor (in Shumailov's M >= 100, n/M << 1 regime)
    # & late-stage a.s. variance collapse (n > M) vs Kazdan MLE Euler product & KDE
    m_asympt = 200
    g_asympt_gens = 6
    asympt_trials = 200
    m_gauss = 25
    g_gens = 30
    g_trials = 300
    rng_g = random.Random(20260911)
    w2_sum = 0.0
    final_vars: list[float] = []
    acc_var_sum = 0.0
    acc_mean_sq_sum = 0.0

    for _ in range(asympt_trials):
        mu_a, var_a = 0.0, 1.0
        for _g in range(g_asympt_gens):
            std_a = math.sqrt(var_a)
            xs_a = [mu_a + std_a * rng_g.gauss(0.0, 1.0) for _ in range(m_asympt)]
            mu_a = sum(xs_a) / m_asympt
            var_a = sum((x - mu_a) ** 2 for x in xs_a) / (m_asympt - 1)
        w2_sum += mu_a * mu_a + (math.sqrt(var_a) - 1.0) ** 2

    for _ in range(g_trials):
        mu_cur, var_cur = 0.0, 1.0
        for _g in range(g_gens):
            std_cur = math.sqrt(var_cur)
            xs = [mu_cur + std_cur * rng_g.gauss(0.0, 1.0) for _ in range(m_gauss)]
            mu_next = sum(xs) / m_gauss
            var_next = sum((x - mu_next) ** 2 for x in xs) / (m_gauss - 1)
            mu_cur, var_cur = mu_next, var_next
        final_vars.append(var_cur)

        # Biased MLE Accumulate via O(M) sufficient statistics (Kazdan Thm 1 & Cor 4, fit_gaussians.py:L102)
        init_xs = [rng_g.gauss(0.0, 1.0) for _ in range(m_gauss)]
        n_tot = m_gauss
        sum_x = sum(init_xs)
        sum_x2 = sum(x * x for x in init_xs)
        mu_acc = 0.0
        var_acc = 1.0
        for _t in range(1, g_gens + 1):
            mu_acc = sum_x / n_tot
            var_acc = max(0.0, (sum_x2 / n_tot) - (mu_acc * mu_acc))
            std_acc = math.sqrt(var_acc)
            for _j in range(m_gauss):
                xj = mu_acc + std_acc * rng_g.gauss(0.0, 1.0)
                sum_x += xj
                sum_x2 += xj * xj
            n_tot += m_gauss
        acc_var_sum += var_acc
        acc_mean_sq_sum += mu_acc * mu_acc

    mc_w2 = w2_sum / asympt_trials
    theo_w2_three_halves = 1.5 * (g_asympt_gens / m_asympt)
    theo_w2_wrong_unit = 1.0 * (g_asympt_gens / m_asympt)
    median_rep_var = statistics.median(final_vars)

    assert abs(mc_w2 - theo_w2_three_halves) < abs(mc_w2 - theo_w2_wrong_unit) * 0.25
    assert median_rep_var < 0.55

    exact_kazdan_prod = math.prod(1.0 - 1.0 / (k * k * m_gauss) for k in range(1, g_gens + 1))
    exact_kazdan_mean_sq = 1.0 - exact_kazdan_prod
    euler_limit_mean_sq = 1.0 - math.sin(math.pi / math.sqrt(m_gauss)) / (math.pi / math.sqrt(m_gauss))
    mc_acc_var = acc_var_sum / g_trials
    mc_acc_mean_sq = acc_mean_sq_sum / g_trials
    assert abs(mc_acc_var - exact_kazdan_prod) < 0.035
    assert abs(mc_acc_mean_sq - exact_kazdan_mean_sq) < 0.015
    assert exact_kazdan_mean_sq < euler_limit_mean_sq < (math.pi ** 2) / (6.0 * m_gauss)

    # Kazdan Theorems 5-7: KDE variance under Replace vs fixed-h Accumulate vs adaptive h_t = c*(t*n)^(-1/5)
    h_fixed = 0.5
    kde_t = 200
    kde_var_replace = 1.0 + kde_t * (h_fixed ** 2)
    kde_var_accum_fixed_h = 1.0 + (h_fixed ** 2) * sum(1.0 / i for i in range(1, kde_t + 1))
    kde_var_accum_scott = 1.0 + (h_fixed ** 2 / (m_gauss ** 0.4)) * sum(i ** (-1.4) for i in range(1, kde_t + 1))
    kde_var_accum_scott_inf = 1.0 + (h_fixed ** 2 / (m_gauss ** 0.4)) * (
        sum(i ** (-1.4) for i in range(1, 5000)) + (5000 ** (-0.4)) / 0.4
    )
    assert kde_var_replace > 50.0 and kde_var_accum_fixed_h > 2.4
    assert kde_var_accum_scott < kde_var_accum_scott_inf < 1.25

    lines.append(
        "  [exact calculation of published theorem/equations] "
        f"Shumailov Eq 4 1D-Gaussian E[W2^2]={theo_w2_three_halves:.4f} (MC={mc_w2:.4f}, unit_factor_foil={theo_w2_wrong_unit:.4f}, "
        f"late_median_var={median_rep_var:.4f}); Kazdan Cor 4 Euler mean_drift={exact_kazdan_mean_sq:.5f} "
        f"(MC={mc_acc_mean_sq:.5f}, t->inf={euler_limit_mean_sq:.5f}); "
        f"KDE_Var(t={kde_t}): Rep={kde_var_replace:.2f}, Accum_fixed_h={kde_var_accum_fixed_h:.3f} (log-div), "
        f"Accum_adaptive_h={kde_var_accum_scott:.4f} < {kde_var_accum_scott_inf:.4f}"
    )

    # 1C. Dohmatob Strong Model Collapse (arXiv:2410.04840v2, Corollary 1) + Seddik Thm 1-3 (arXiv:2404.05090v1)
    d_sc = 6
    c_bias = 2.0
    p2_contamin = 0.05  # Irreducible floor p2^2 * c^2 = 0.0100
    floor_sc = (p2_contamin ** 2) * (c_bias ** 2)

    sc_errors: dict[int, tuple[float, float, float]] = {}
    w1_star = [1.0] + [0.0] * (d_sc - 1)
    w2_star = [1.0 + c_bias] + [0.0] * (d_sc - 1)
    for n_tot in (60, 600):
        phi = d_sc / n_tot
        theo_clean = sigma_sq * phi / (1.0 - phi)
        theo_dirty = theo_clean + (p2_contamin ** 2 + p2_contamin * (1.0 - p2_contamin) * phi / (1.0 - phi)) * (c_bias ** 2)
        n_syn = int(round(p2_contamin * n_tot))
        n_real = n_tot - n_syn
        mc_clean_acc = 0.0
        mc_dirty_acc = 0.0
        sc_trials = 50
        for _ in range(sc_trials):
            xs = [[rng.gauss(0.0, 1.0) for _ in range(d_sc)] for _ in range(n_tot)]
            ys_clean = [dot(x, w1_star) + rng.gauss(0.0, 1.0) for x in xs]
            ys_dirty = [
                dot(xs[k], w1_star if k < n_real else w2_star) + rng.gauss(0.0, 1.0)
                for k in range(n_tot)
            ]
            mc_clean_acc += sq_dist(fit_ols(xs, ys_clean), w1_star)
            mc_dirty_acc += sq_dist(fit_ols(xs, ys_dirty), w1_star)
        sc_errors[n_tot] = (mc_clean_acc / sc_trials, mc_dirty_acc / sc_trials, theo_dirty)

    assert sc_errors[60][0] / sc_errors[600][0] > 8.5
    assert sc_errors[600][1] > floor_sc * 1.5 and abs(sc_errors[600][1] - sc_errors[600][2]) < 0.005

    s_vocab = 16
    n_cat = 12
    m_gens = 20
    p0 = [1.0 / s_vocab] * s_vocab
    s0 = sum(pi * pi for pi in p0)
    exact_sm = 1.0 - ((1.0 - 1.0 / n_cat) ** m_gens) * (1.0 - s0)
    rho_lo = max(0.0, 1.0 - n_cat * (1.0 - s0) * ((1.0 - 1.0 / n_cat) ** m_gens))
    rho_hi = 1.0 - ((1.0 - s0) / (1.0 - 1.0 / s_vocab)) * ((1.0 - 1.0 / n_cat) ** m_gens)

    n_real_cat = 48
    alpha_s = n_cat / (n_real_cat + n_cat)
    beta_s = alpha_s * ((1.0 + 1.0 / n_real_cat) * alpha_s - 1.0 / n_real_cat)
    m_idx = m_gens - 1
    exact_sm_partial = (
        (1.0 / n_real_cat) * (1.0 + 2.0 * alpha_s - (1.0 - 1.0 / n_real_cat) * alpha_s * (beta_s ** m_idx))
        / (1.0 + (1.0 + 1.0 / n_real_cat) * alpha_s)
        + ((1.0 - 1.0 / n_real_cat) * s0 / (1.0 + (1.0 + 1.0 / n_real_cat) * alpha_s))
        * (1.0 + alpha_s - alpha_s * (beta_s ** m_idx) / n_real_cat)
    )
    c0_exact = (math.e ** 3) / (2.0 * math.pi)
    prefactor_eq11 = 2.0 * math.pi * (math.e ** -2)
    assert 3.19 < c0_exact < 3.20 and 0.850 < prefactor_eq11 < 0.851

    cat_trials = 360
    sm_mc = 0.0
    rho_mc = 0.0
    sm_part_mc = 0.0
    cdf0 = list(itertools.accumulate(p0))
    for _ in range(cat_trials):
        p_cur = p0[:]
        for _ in range(m_gens):
            counts = [0] * s_vocab
            cdf = list(itertools.accumulate(p_cur))
            for _s in range(n_cat):
                idx = min(s_vocab - 1, bisect.bisect_left(cdf, rng.random()))
                counts[idx] += 1
            p_cur = [c / n_cat for c in counts]
        sm_mc += sum(pi * pi for pi in p_cur)
        if max(p_cur) == 1.0:
            rho_mc += 1.0

        real_counts = [0] * s_vocab
        for _s in range(n_real_cat):
            idx = min(s_vocab - 1, bisect.bisect_left(cdf0, rng.random()))
            real_counts[idx] += 1
        p1 = [c / n_real_cat for c in real_counts]
        p_mix = p1[:]
        for _ in range(2, m_gens + 1):
            syn_counts = [0] * s_vocab
            cdf_m = list(itertools.accumulate(p_mix))
            for _s in range(n_cat):
                idx = min(s_vocab - 1, bisect.bisect_left(cdf_m, rng.random()))
                syn_counts[idx] += 1
            p_mix = [(n_real_cat * p1[i] + syn_counts[i]) / (n_real_cat + n_cat) for i in range(s_vocab)]
        sm_part_mc += sum(pi * pi for pi in p_mix)

    sm_mc /= cat_trials
    rho_mc /= cat_trials
    sm_part_mc /= cat_trials
    assert abs(sm_mc - exact_sm) < 0.03
    assert rho_lo - 0.02 <= rho_mc <= rho_hi + 0.02
    assert abs(sm_part_mc - exact_sm_partial) < 0.012 and sm_part_mc < 0.12

    lines.append(
        "  [controlled simulation] "
        f"Dohmatob Cor 1 Strong Collapse (5% syn, c=2): clean_MSE(60->600)={sc_errors[60][0]:.4f}->{sc_errors[600][0]:.4f}, "
        f"mixed_MSE(60->600)={sc_errors[60][1]:.4f}->{sc_errors[600][1]:.4f} > floor={floor_sc:.4f}; "
        f"Seddik Thm 1-3 S_m={exact_sm:.4f} (MC={sm_mc:.4f}, Dirac_rho={rho_mc:.3f} in [{rho_lo:.3f},{rho_hi:.3f}]), "
        f"Partial_S_m={exact_sm_partial:.4f} (MC={sm_part_mc:.4f}), C0=e^3/(2pi)={c0_exact:.4f}, 2pi*e^-2={prefactor_eq11:.4f}"
    )
    return lines


# ---------------------------------------------------------------------------
# Probe 2: Heavy-Tail Zipf Truncation (top_p=0.5), Grokking Delay &
#          Closed-Loop Accumulate-Subsample Rare-Tail Erosion
# ---------------------------------------------------------------------------

def run_probe_2() -> list[str]:
    lines: list[str] = []
    lines.append("=== Probe 2: Heavy-Tail Zipf Truncation, Grokking Delay & Subsample Tail Erosion ===")

    # 2A. Exact infinite-support Hutter-Zipf risk E_test(T) = sum_{i=1}^inf p_i (1 - q_i)^T
    # (Dohmatob arXiv:2402.07043v2, Thms 2.1 & 3.2) via M=2000 exact head + Euler-Maclaurin tail.
    m_head = 2000
    beta = 1.5
    zeta_beta = (
        sum(i ** (-beta) for i in range(1, m_head + 1))
        + (m_head ** (1.0 - beta)) / (beta - 1.0)
        - 0.5 * (m_head ** (-beta))
        + (beta / 12.0) * (m_head ** (-beta - 1.0))
    )
    p_head = [(i ** (-beta)) / zeta_beta for i in range(1, m_head + 1)]
    tail_mass_beyond_head = 1.0 - sum(p_head)

    # Nucleus truncation top_p = 0.5 matching yizhongw/self-instruct@0b26ccaa:bootstrap_instructions.py:L178
    cum = 0.0
    k_top_p05 = 0
    for idx, prob in enumerate(p_head, 1):
        cum += prob
        if cum >= 0.5:
            k_top_p05 = idx
            break
    q_top_p05_norm = sum(p_head[:k_top_p05])
    q_top_p05_head = [p / q_top_p05_norm if idx < k_top_p05 else 0.0 for idx, p in enumerate(p_head)]

    # Tail-cut synthetic distribution at k = 25 (k^beta = 125)
    k_cut = 25
    q_cut_norm = sum(p_head[:k_cut])
    q_cut_head = [p / q_cut_norm if idx < k_cut else 0.0 for idx, p in enumerate(p_head)]
    missing_tail_mass = 1.0 - q_cut_norm

    def exact_infinite_zipf_risk(q_h: Sequence[float], alpha_tail: float, sample_budget: int) -> float:
        head = sum(
            pi * (math.exp(sample_budget * math.log1p(-qi)) if qi > 0.0 else 1.0)
            for pi, qi in zip(p_head, q_h)
        )
        if alpha_tail == 0.0:
            return head + tail_mass_beyond_head
        lam = alpha_tail * sample_budget / zeta_beta
        tail = 0.0
        for m_ord in range(12):
            pwr = beta * (m_ord + 1)
            s_tail = ((m_head + 0.5) ** (1.0 - pwr)) / (pwr - 1.0)
            tail += (((-lam) ** m_ord) / math.factorial(m_ord)) * (s_tail / zeta_beta)
        return head + tail

    err_clean_2e2 = exact_infinite_zipf_risk(p_head, 1.0, 200)
    err_clean_2e4 = exact_infinite_zipf_risk(p_head, 1.0, 20_000)
    err_cut_2e4 = exact_infinite_zipf_risk(q_cut_head, 0.0, 20_000)
    err_top05_2e4 = exact_infinite_zipf_risk(q_top_p05_head, 0.0, 20_000)

    clean_log_slope = -math.log10(err_clean_2e4 / err_clean_2e2) / 2.0
    assert abs(clean_log_slope - (1.0 - 1.0 / beta)) < 0.003
    assert abs(err_cut_2e4 - missing_tail_mass) < 1e-8
    assert err_top05_2e4 > 0.40 and k_top_p05 <= 5

    k_beta = k_cut ** beta  # 25^1.5 = 125
    grok_crossings: dict[float, int] = {}
    target_err = missing_tail_mass * 0.50

    for pi_mix in (0.01, 0.05, 0.25):
        q_mix_head = [pi_mix * pi + (1.0 - pi_mix) * qi for pi, qi in zip(p_head, q_cut_head)]
        lo, hi = 1, 500_000
        while lo < hi:
            mid = (lo + hi) // 2
            if exact_infinite_zipf_risk(q_mix_head, pi_mix, mid) <= target_err:
                hi = mid
            else:
                lo = mid + 1
        grok_crossings[pi_mix] = lo

    ratio_01_to_05 = grok_crossings[0.01] / grok_crossings[0.05]
    ratio_05_to_25 = grok_crossings[0.05] / grok_crossings[0.25]
    assert 4.80 < ratio_01_to_05 < 5.20 and 4.70 < ratio_05_to_25 < 5.20

    lines.append(
        "  [exact calculation of published theorem/equations] "
        f"Dohmatob Thm 2.1/3.2 Infinite-Zipf(beta={beta}, zeta={zeta_beta:.6f}): top_p=0.5 keeps k={k_top_p05} head skills "
        f"(floor={err_top05_2e4:.4f}); k={k_cut} cut stalls at {err_cut_2e4:.4f} vs clean {err_clean_2e4:.4f} "
        f"(slope=-{clean_log_slope:.4f} vs -1/3); T_grok(pi=0.25,0.05,0.01)={grok_crossings[0.25]},{grok_crossings[0.05]},{grok_crossings[0.01]} "
        f"(5x ratios={ratio_05_to_25:.2f}x, {ratio_01_to_05:.2f}x; k^beta={k_beta:.0f})"
    )

    # 2B. Closed-loop empirical generation fitted on the active training batch each round:
    # Contrasts Full-Accumulate (top_p=0.85, retaining full pool) vs Untruncated Accumulate-Subsample
    # (top_p=1.0 empirical resampling from sub_batch, matching Kazdan) vs Nucleus-Truncated
    # Accumulate-Subsample (top_p=0.85 empirical generation fitted on sub_batch).
    rng = random.Random(20260902)
    batch_t = 320
    p_fin_norm = sum(p_head)
    p_fin = [p / p_fin_norm for p in p_head]
    cdf_true = list(itertools.accumulate(p_fin))

    def sample_nucleus_from_counts(
        counts: dict[int, int],
        total_count: int,
        n_gen: int,
        top_p: float,
    ) -> list[int]:
        ranked = sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))
        kept: list[tuple[int, int]] = []
        cum = 0.0
        thresh = top_p * total_count
        for s_id, cnt in ranked:
            kept.append((s_id, cnt))
            cum += cnt
            if cum >= thresh:
                break
        tot_kept = sum(cnt for _, cnt in kept)
        skills = [s_id for s_id, _ in kept]
        cdf = list(itertools.accumulate(cnt / tot_kept for _, cnt in kept))
        return [skills[min(len(skills) - 1, bisect.bisect_left(cdf, rng.random()))] for _ in range(n_gen)]

    trials_sub = 60
    rounds_sub = 20
    tail_mass_full_accum = [0.0] * rounds_sub
    tail_mass_untrunc_sub = [0.0] * rounds_sub
    tail_mass_trunc_sub = [0.0] * rounds_sub

    for _ in range(trials_sub):
        real_batch = [min(m_head - 1, bisect.bisect_left(cdf_true, rng.random())) + 1 for _ in range(batch_t)]

        # Full-Accumulate with top_p=0.85 generator fitted on full accumulated pool
        counts_full: dict[int, int] = collections.Counter(real_batch)
        tot_full = batch_t
        full_tail_val = sum(p_fin[s - 1] for s in counts_full if s > k_cut)

        # Closed-loop Untruncated Accumulate-Subsample (top_p=1.0 empirical model on sub_batch)
        pool_untrunc = real_batch[:]

        # Closed-loop Nucleus-Truncated Accumulate-Subsample (top_p=0.85 empirical model on sub_batch)
        pool_trunc = real_batch[:]

        for r_idx in range(rounds_sub):
            tail_mass_full_accum[r_idx] += full_tail_val
            syn_full = sample_nucleus_from_counts(counts_full, tot_full, batch_t, top_p=0.85)
            for s_id in syn_full:
                if s_id not in counts_full and s_id > k_cut:
                    full_tail_val += p_fin[s_id - 1]
                counts_full[s_id] = counts_full.get(s_id, 0) + 1
            tot_full += batch_t

            sub_u = pool_untrunc if r_idx == 0 else rng.sample(pool_untrunc, batch_t)
            tail_mass_untrunc_sub[r_idx] += sum(p_fin[s - 1] for s in set(sub_u) if s > k_cut)
            syn_u = [sub_u[int(rng.random() * batch_t)] for _ in range(batch_t)]
            pool_untrunc.extend(syn_u)

            sub_t = pool_trunc if r_idx == 0 else rng.sample(pool_trunc, batch_t)
            tail_mass_trunc_sub[r_idx] += sum(p_fin[s - 1] for s in set(sub_t) if s > k_cut)
            counts_sub_t = collections.Counter(sub_t)
            syn_t = sample_nucleus_from_counts(counts_sub_t, batch_t, batch_t, top_p=0.85)
            pool_trunc.extend(syn_t)

    tail_mass_full_accum = [v / trials_sub for v in tail_mass_full_accum]
    tail_mass_untrunc_sub = [v / trials_sub for v in tail_mass_untrunc_sub]
    tail_mass_trunc_sub = [v / trials_sub for v in tail_mass_trunc_sub]

    untrunc_loss_pct = 100.0 * (1.0 - tail_mass_untrunc_sub[-1] / tail_mass_untrunc_sub[0])
    trunc_loss_pct = 100.0 * (1.0 - tail_mass_trunc_sub[-1] / tail_mass_trunc_sub[0])

    assert abs(tail_mass_full_accum[-1] - tail_mass_full_accum[0]) < 1e-12
    assert 35.0 < untrunc_loss_pct < 50.0
    assert tail_mass_trunc_sub[0] > tail_mass_trunc_sub[4] > tail_mass_trunc_sub[-1]
    assert trunc_loss_pct > 90.0

    lines.append(
        "  [controlled simulation] "
        f"Closed-loop Accumulate-Subsample (B={batch_t}, rounds={rounds_sub}): "
        f"Full-Accum(top_p=0.85)={tail_mass_full_accum[0]:.5f}->{tail_mass_full_accum[-1]:.5f} (preserved), "
        f"Untrunc-Subsample(top_p=1.0)={tail_mass_untrunc_sub[0]:.5f}->{tail_mass_untrunc_sub[-1]:.5f} ({untrunc_loss_pct:.1f}% loss), "
        f"Trunc-Subsample(top_p=0.85)={tail_mass_trunc_sub[0]:.5f}->{tail_mass_trunc_sub[4]:.5f}->{tail_mass_trunc_sub[-1]:.5f} ({trunc_loss_pct:.1f}% rare-tail loss)"
    )
    return lines


# ---------------------------------------------------------------------------
# Probe 3: Ferbach Curated Self-Consuming Loop (beta=1/t vs. lambda < 1/(K-1))
#          & Feng Imperfect Verifier Phase Transition (p_star) + Judge Drift
# ---------------------------------------------------------------------------

def exact_curated_operator(probs: Sequence[float], exp_rewards: Sequence[float], k_choice: int) -> list[float]:
    """Exact Bradley-Terry K-choice density multiplier H_{p_t}^K(x) (Ferbach Eq. 6)."""
    m = len(probs)
    k_exp_r = [k_choice * er for er in exp_rewards]
    # Group identical (k_choice - 1)-tuples via combinations_with_replacement + multinomial count
    fact_km1 = math.factorial(k_choice - 1)
    h_vals = [0.0] * m
    for comb in itertools.combinations_with_replacement(range(m), k_choice - 1):
        w_tup = 1.0
        sum_exp = 0.0
        denom_mult = 1
        run_len = 0
        prev_idx = -1
        for idx in comb:
            w_tup *= probs[idx]
            sum_exp += exp_rewards[idx]
            if idx == prev_idx:
                run_len += 1
                denom_mult *= run_len
            else:
                prev_idx = idx
                run_len = 1
        w_mult = w_tup * (fact_km1 // denom_mult)
        if w_mult == 0.0:
            continue
        for x in range(m):
            h_vals[x] += w_mult * k_exp_r[x] / (exp_rewards[x] + sum_exp)
    out = [probs[x] * h_vals[x] for x in range(m)]
    z = sum(out)
    return [v / z for v in out]


def kl_div(p: Sequence[float], q: Sequence[float]) -> float:
    return sum(pi * math.log(pi / qi) for pi, qi in zip(p, q) if pi > 0.0)


def shannon_entropy(p: Sequence[float]) -> float:
    return -sum(pi * math.log(pi) for pi in p if pi > 0.0)


def run_probe_3() -> list[str]:
    lines: list[str] = []
    lines.append("=== Probe 3: Curated Mode Collapse, KL Safe Mixing & Imperfect-Verifier Cliff ===")

    # 3A. Ferbach et al. (arXiv:2407.09499v1, Lemmas 2.1-2.2, Theorems 2.1, 2.3, 2.4)
    rewards = [0.0, 0.5, 1.0, 1.4, 2.0, 2.0]
    exp_r = [math.exp(r) for r in rewards]
    r_star_exp = max(exp_r)
    p_init = [0.30, 0.25, 0.20, 0.15, 0.04, 0.06]
    q0_opt = p_init[4] + p_init[5]
    p_star = [0.0, 0.0, 0.0, 0.0, p_init[4] / q0_opt, p_init[5] / q0_opt]

    k_choice = 4
    p_pure = p_init[:]
    ent_0 = shannon_entropy(p_pure)
    for _step in range(55):
        mean_before = sum(pi * er for pi, er in zip(p_pure, exp_r))
        var_before = sum(pi * ((er - mean_before) ** 2) for pi, er in zip(p_pure, exp_r))
        p_next = exact_curated_operator(p_pure, exp_r, k_choice)
        mean_after = sum(pi * er for pi, er in zip(p_next, exp_r))
        lemma22_lb = mean_before + ((k_choice - 1.0) / k_choice) * (var_before / r_star_exp)
        assert mean_after + 1e-12 >= lemma22_lb
        p_pure = p_next

    var_final = sum(pi * ((er - sum(pj * ej for pj, ej in zip(p_pure, exp_r))) ** 2) for pi, er in zip(p_pure, exp_r))
    kl_to_pstar = kl_div(p_star, p_pure)
    ent_final = shannon_entropy(p_pure)
    assert var_final < 1e-6 and kl_to_pstar < 1e-4 and ent_final < ent_0 * 0.45

    t_rlhf = 5
    p_kinf = p_init[:]
    for _ in range(t_rlhf):
        unnorm = [pi * er for pi, er in zip(p_kinf, exp_r)]
        z_u = sum(unnorm)
        p_kinf = [u / z_u for u in unnorm]
    beta_equiv = 1.0 / t_rlhf
    unnorm_rlhf = [pi * math.exp(r / beta_equiv) for pi, r in zip(p_init, rewards)]
    p_rlhf_direct = [u / sum(unnorm_rlhf) for u in unnorm_rlhf]
    assert max(abs(a - b) for a, b in zip(p_kinf, p_rlhf_direct)) < 1e-15

    p_ref_rare = [0.35, 0.30, 0.20, 0.14999, 0.000004, 0.000006]
    lam_safe = 0.25  # < 1 / (K - 1) = 1/3
    kl_cert_safe = -math.log(1.0 - lam_safe * (k_choice - 1))
    mean_ref = sum(pi * er for pi, er in zip(p_ref_rare, exp_r))
    var_ref = sum(pi * ((er - mean_ref) ** 2) for pi, er in zip(p_ref_rare, exp_r))
    thm23_lb = mean_ref + (lam_safe / ((1.0 + lam_safe) ** 3)) * ((k_choice - 1.0) * var_ref / (k_choice * r_star_exp))

    p_safe = p_ref_rare[:]
    max_kl_safe = 0.0
    max_log_ratio_safe = 0.0
    for _ in range(65):
        curated = exact_curated_operator(p_safe, exp_r, k_choice)
        p_safe = [(1.0 / (1.0 + lam_safe)) * pr + (lam_safe / (1.0 + lam_safe)) * pc for pr, pc in zip(p_ref_rare, curated)]
        max_kl_safe = max(max_kl_safe, kl_div(p_safe, p_ref_rare))
        max_log_ratio_safe = max(max_log_ratio_safe, max(math.log(ps / pr) for ps, pr in zip(p_safe, p_ref_rare)))
        assert sum(pi * er for pi, er in zip(p_safe, exp_r)) + 1e-12 >= thm23_lb

    assert max_kl_safe <= max_log_ratio_safe <= kl_cert_safe + 1e-12

    lam_unsafe = 3.0
    p_unsafe = p_ref_rare[:]
    for _ in range(65):
        curated_u = exact_curated_operator(p_unsafe, exp_r, k_choice)
        p_unsafe = [(1.0 / (1.0 + lam_unsafe)) * pr + (lam_unsafe / (1.0 + lam_unsafe)) * pc for pr, pc in zip(p_ref_rare, curated_u)]
    kl_unsafe = kl_div(p_unsafe, p_ref_rare)
    ratio_unsafe = max(ps / pr for ps, pr in zip(p_unsafe, p_ref_rare))
    assert kl_cert_safe < kl_unsafe < -math.log(1e-5) and ratio_unsafe > 10_000.0

    lines.append(
        "  [exact calculation of published theorem/equations] "
        f"Ferbach Thm 2.1/2.3/2.4 (K={k_choice}): pure_curated D_KL(p*||p_55)={kl_to_pstar:.2e}, "
        f"H={ent_0:.3f}->{ent_final:.3f}; safe_lam={lam_safe}<1/3 max_KL={max_kl_safe:.4f} <= "
        f"max_log_ratio={max_log_ratio_safe:.4f} <= cert={kl_cert_safe:.4f}; "
        f"unsafe_lam={lam_unsafe} max_density_ratio={ratio_unsafe:.1f}x (KL={kl_unsafe:.3f} < -log(q0))"
    )

    # 3B. Feng et al. (arXiv:2406.07515v2, Theorem 4.2) Verifier Breakdown Point p_star = 1 / (1 + psi/phi)
    rng = random.Random(20260903)
    n_syn_ver = 900

    def sim_pruned_accuracy(p_err: float, phi_tp: float, psi_fp: float) -> float:
        correct_trials = 0
        n_rep = 30
        for _ in range(n_rep):
            score_w = 0.0
            for _i in range(n_syn_ver):
                y_true = 1.0 if rng.random() < 0.5 else -1.0
                x_val = y_true + 0.75 * rng.gauss(0.0, 1.0)
                is_corrupted = rng.random() < p_err
                y_syn = -y_true if is_corrupted else y_true
                keep_prob = psi_fp if is_corrupted else phi_tp
                if rng.random() < keep_prob:
                    score_w += y_syn * x_val
            if score_w > 0.0:
                correct_trials += 1
        return correct_trials / n_rep

    p_star_mc = 1.0 / (1.0 + 0.25 / 1.0)
    p_star_strict = 1.0 / (1.0 + 0.02 / 0.90)
    acc_mc_below = sim_pruned_accuracy(0.70, 1.0, 0.25)
    acc_mc_above = sim_pruned_accuracy(0.88, 1.0, 0.25)
    acc_strict_at_88 = sim_pruned_accuracy(0.88, 0.90, 0.02)
    assert acc_mc_below == 1.0 and acc_mc_above == 0.0 and acc_strict_at_88 == 1.0

    p_gen_fixed = 0.62
    phi_judge = 0.80
    drift_curve = []
    for psi_t in (0.15, 0.40, 0.72):
        p_star_t = 1.0 / (1.0 + psi_t / phi_judge)
        acc_t = sim_pruned_accuracy(p_gen_fixed, phi_judge, psi_t)
        drift_curve.append((psi_t, p_star_t, acc_t))

    assert drift_curve[0][1] > p_gen_fixed and drift_curve[0][2] == 1.0
    assert drift_curve[2][1] < p_gen_fixed and drift_curve[2][2] == 0.0

    lines.append(
        "  [controlled simulation] "
        f"Feng Thm 4.2 Verifier Cliff (N={n_syn_ver}): MC_verifier(p*={p_star_mc:.3f}) acc(p=0.70->0.88)="
        f"{acc_mc_below:.2f}->{acc_mc_above:.2f} vs Strict_Tests(p*={p_star_strict:.4f}) acc(p=0.88)={acc_strict_at_88:.2f}; "
        f"Judge_FP_Drift(p={p_gen_fixed}): psi=0.15(p*={drift_curve[0][1]:.3f},acc={drift_curve[0][2]:.2f}) -> "
        f"psi=0.72(p*={drift_curve[2][1]:.3f},acc={drift_curve[2][2]:.2f})"
    )
    return lines


# ---------------------------------------------------------------------------
# Probe 4: RLVR pass@1 vs. pass@k Contraction, open-r1 0/8 Censoring,
#          and ProRL KL + Reference-Reset Compositional Ratchet
# ---------------------------------------------------------------------------

def unbiased_pass_at_k_repo(n: int, c: int, k: int) -> float:
    """Exact reproduction of LeapLabTHU/limit-of-RLVR@79c348f4:math/pass@k.py:L58-L60."""
    if n - c < k:
        return 1.0
    prod_val = 1.0
    for denom in range(n - c + 1, n + 1):
        prod_val *= 1.0 - (k / denom)
    return 1.0 - prod_val


def run_probe_4() -> list[str]:
    lines: list[str] = []
    lines.append("=== Probe 4: RLVR pass@1 vs pass@k Contraction, open-r1 Censoring & ProRL Resets ===")

    # 4A. Exact combinatorial identity of limit-of-RLVR pass@k estimator and open-r1 filter_dapo.yaml censoring
    for n_chk, c_chk, k_chk in ((1024, 3, 256), (1024, 1, 512), (256, 0, 256), (256, 12, 64)):
        est = unbiased_pass_at_k_repo(n_chk, c_chk, k_chk)
        exact_comb = 1.0 if n_chk - c_chk < k_chk else 1.0 - math.comb(n_chk - c_chk, k_chk) / math.comb(n_chk, k_chk)
        assert abs(est - exact_comb) < 1e-12

    n_rollouts_openr1 = 8
    pass_min = 0.1
    pass_max = 0.6
    surviving_counts = [
        c for c in range(n_rollouts_openr1 + 1)
        if pass_min < (c / n_rollouts_openr1) < pass_max
    ]
    assert surviving_counts == [1, 2, 3, 4]

    def openr1_discard_prob(p_true: float) -> float:
        keep = sum(
            math.comb(n_rollouts_openr1, c) * (p_true ** c) * ((1.0 - p_true) ** (n_rollouts_openr1 - c))
            for c in surviving_counts
        )
        return 1.0 - keep

    discard_p010 = openr1_discard_prob(0.010)
    discard_p015 = openr1_discard_prob(0.015)
    pass256_p015 = 1.0 - (1.0 - 0.015) ** 256
    assert discard_p010 > 0.922 and discard_p015 > 0.886 and pass256_p015 > 0.978

    prorl_single_epoch_keep = 1.0 - (1.0 - 0.015) ** 16 - (0.015 ** 16)
    prorl_10epoch_reach = 1.0 - (1.0 - prorl_single_epoch_keep) ** 10
    assert prorl_10epoch_reach > 0.91

    lines.append(
        "  [exact reproduction of pinned repository logic] "
        f"open-r1 filter_dapo.yaml (N=8, 0.1<r<0.6 => counts={surviving_counts}): "
        f"discards {100*discard_p010:.2f}% at p=0.010 and {100*discard_p015:.2f}% at p=0.015 "
        f"(despite true pass@256={100*pass256_p015:.2f}%); online N=16 10-epoch reach={100*prorl_10epoch_reach:.1f}%"
    )

    # 4B. Reconciling Yue et al. (arXiv:2504.13837v5, Sec. 4.3) & ProRL (arXiv:2505.24864v1):
    # Regime I: Genuine shared-parameter log-linear policy pi_theta(a | x) propto exp(theta^T phi(x, a))
    # over 6 reasoning templates (0=rare structural invariant valid across all 40 problems; 1=algebraic
    # template valid on 0..13; 2=casework template valid on 14..27; 3..5=invalid fallacies) and 4 shared
    # context features (global template bias, algebraic cue, casework cue, frontier complexity cue).
    # Updated strictly by group-normalized GRPO gradients on active problems (zero mutation on skipped items).
    def problem_spec_r1(idx: int) -> tuple[tuple[float, float, float, float], list[int]]:
        if idx < 14:
            return (1.0, 1.0, 0.0, 0.0), [1, 1, 0, 0, 0, 0]
        if idx < 28:
            return (1.0, 0.0, 1.0, 0.0), [1, 0, 1, 0, 0, 0]
        if idx < 34:
            return (1.0, 0.85, 0.15, 1.0), [1, 0, 0, 0, 0, 0]
        return (1.0, 0.15, 0.85, 1.0), [1, 0, 0, 0, 0, 0]

    def init_shared_theta() -> list[list[float]]:
        return [
            [-1.45,  0.10,  0.10,  0.15,  0.15,  0.10],  # global strategy prior
            [ 0.05,  0.40, -0.35,  0.00,  0.00,  0.00],  # algebraic surface cue
            [ 0.05, -0.35,  0.40,  0.00,  0.00,  0.00],  # casework surface cue
            [-1.05,  0.40,  0.40,  0.10,  0.05,  0.00],  # frontier complexity cue (hard p(a=0) = 0.0120)
        ]

    def softmax(logits: Sequence[float]) -> list[float]:
        m = max(logits)
        exps = [math.exp(z - m) for z in logits]
        s = sum(exps)
        return [e / s for e in exps]

    def policy_logits(theta: Sequence[Sequence[float]], ctx: Sequence[float]) -> list[float]:
        return [sum(ctx[f] * theta[f][a] for f in range(4)) for a in range(6)]

    problems_r1 = [problem_spec_r1(idx) for idx in range(40)]

    def eval_shared_policy(theta: Sequence[Sequence[float]]) -> tuple[float, float]:
        p1_tot = 0.0
        p256_tot = 0.0
        for ctx, mk in problems_r1:
            ps = softmax(policy_logits(theta, ctx))
            p_succ = sum(p for p, m in zip(ps, mk) if m == 1)
            p1_tot += p_succ
            p256_tot += 1.0 - ((1.0 - p_succ) ** 256)
        return p1_tot / len(problems_r1), p256_tot / len(problems_r1)

    def train_shared_grpo(offline_openr1_filter: bool) -> list[list[float]]:
        rng_grpo = random.Random(20260904)
        theta = init_shared_theta()
        active = [True] * len(problems_r1)
        if offline_openr1_filter:
            active = []
            for ctx, mk in problems_r1:
                ps = softmax(policy_logits(theta, ctx))
                cdf = list(itertools.accumulate(ps))
                c_pass = sum(mk[min(5, bisect.bisect_left(cdf, rng_grpo.random()))] for _ in range(8))
                active.append(0.1 < (c_pass / 8.0) < 0.6)

        lr = 0.045
        for _step in range(45):
            grad_theta = [[0.0] * 6 for _ in range(4)]
            for idx, (ctx, mk) in enumerate(problems_r1):
                if not active[idx]:
                    continue
                ps = softmax(policy_logits(theta, ctx))
                cdf = list(itertools.accumulate(ps))
                acts = [min(5, bisect.bisect_left(cdf, rng_grpo.random())) for _ in range(8)]
                rews = [float(mk[a]) for a in acts]
                mean_r = sum(rews) / 8.0
                std_r = math.sqrt(sum((r - mean_r) ** 2 for r in rews) / 8.0)
                if std_r > 1e-8:
                    for a, r in zip(acts, rews):
                        adv = (r - mean_r) / std_r
                        for f in range(4):
                            if ctx[f] != 0.0:
                                for m_i in range(6):
                                    grad = ((1.0 if m_i == a else 0.0) - ps[m_i]) * ctx[f]
                                    grad_theta[f][m_i] += (adv * grad) / 8.0
            for f in range(4):
                for m_i in range(6):
                    theta[f][m_i] += lr * grad_theta[f][m_i]
        return theta

    theta_base = init_shared_theta()
    theta_online = train_shared_grpo(offline_openr1_filter=False)
    theta_censored = train_shared_grpo(offline_openr1_filter=True)

    base_p1_r1, base_p256_r1 = eval_shared_policy(theta_base)
    online_p1_r1, online_p256_r1 = eval_shared_policy(theta_online)
    cens_p1_r1, cens_p256_r1 = eval_shared_policy(theta_censored)

    rng_eval = random.Random(20260914)
    est_p256_base = 0.0
    est_p256_online = 0.0
    est_p256_cens = 0.0
    for ctx, mk in problems_r1:
        p_b = sum(p for p, m in zip(softmax(policy_logits(theta_base, ctx)), mk) if m == 1)
        p_o = sum(p for p, m in zip(softmax(policy_logits(theta_online, ctx)), mk) if m == 1)
        p_c = sum(p for p, m in zip(softmax(policy_logits(theta_censored, ctx)), mk) if m == 1)
        c_b = sum(1 for _ in range(1024) if rng_eval.random() < p_b)
        c_o = sum(1 for _ in range(1024) if rng_eval.random() < p_o)
        c_c = sum(1 for _ in range(1024) if rng_eval.random() < p_c)
        est_p256_base += unbiased_pass_at_k_repo(1024, c_b, 256)
        est_p256_online += unbiased_pass_at_k_repo(1024, c_o, 256)
        est_p256_cens += unbiased_pass_at_k_repo(1024, c_c, 256)
    est_p256_base /= len(problems_r1)
    est_p256_online /= len(problems_r1)
    est_p256_cens /= len(problems_r1)

    assert online_p1_r1 > base_p1_r1 + 0.40 and cens_p1_r1 > base_p1_r1 + 0.40
    assert cens_p256_r1 < online_p256_r1 < base_p256_r1 - 0.14
    assert est_p256_cens < est_p256_online < est_p256_base - 0.12

    # Regime II: Compositional L=4 step chain (5 actions/step, R = prod_{l=1}^4 1_{a_l=0}, q_0 = 0.20 => p_base = 0.0016).
    # Exact KL-regularized proximal/mirror-descent optimization of J(pi) = E_pi[R] - beta * sum_l D_KL(pi_l || pi_ref,l):
    # Without reference resets (Frozen-KL, beta=0.05), marginal step credit q^(L-1) = 0.008 << beta = 0.05 traps q at 0.2734
    # (0.2734^4 = 0.56%, below the negative-gradient barrier q in (0.2734, 0.2990))!
    # With ProRL periodic reference resets (pi_ref <- pi_theta every stage), log-odds accumulate and escape the barrier!
    chain_len = 4
    kl_beta = 0.05

    def solve_compositional_kl(use_ref_resets: bool, n_stages: int = 16, inner_iters: int = 15) -> tuple[float, float]:
        logit_ref = math.log(0.20 / 0.80)
        logit_step = logit_ref
        for _stage in range(n_stages):
            for _it in range(inner_iters):
                q_step = 1.0 / (1.0 + math.exp(-logit_step))
                # Exact local optimality in log-odds: log(q/(1-q)) = log(q_ref/(1-q_ref)) + q^(L-1) / beta
                target_logit = min(20.0, logit_ref + (q_step ** (chain_len - 1)) / kl_beta)
                logit_step = 0.5 * logit_step + 0.5 * target_logit
            if use_ref_resets:
                logit_ref = logit_step
        q_final = 1.0 / (1.0 + math.exp(-logit_step))
        p_pass1 = q_final ** chain_len
        p_pass256 = 1.0 - (1.0 - p_pass1) ** 256
        return p_pass1, p_pass256

    base_comp_p1 = 0.20 ** chain_len  # 0.0016 (0.16%)
    base_comp_p256 = 1.0 - (1.0 - base_comp_p1) ** 256  # 33.63%
    frozen_kl_p1, frozen_kl_p256 = solve_compositional_kl(use_ref_resets=False)
    prorl_p1, prorl_p256 = solve_compositional_kl(use_ref_resets=True)

    assert frozen_kl_p1 < 0.01 and prorl_p1 > 0.95 and prorl_p256 > 0.999 > frozen_kl_p256 > base_comp_p256

    lines.append(
        "  [derived analytical model] "
        f"Shared-Policy RLVR Crossover: Base(p@1={100*base_p1_r1:.1f}%,p@256={100*base_p256_r1:.1f}%) -> "
        f"Online_GRPO(p@1={100*online_p1_r1:.1f}%,p@256={100*online_p256_r1:.1f}%) -> "
        f"Censored_GRPO(p@1={100*cens_p1_r1:.1f}%,p@256={100*cens_p256_r1:.1f}%; "
        f"N=1024_est {100*est_p256_base:.1f}%->{100*est_p256_online:.1f}%->{100*est_p256_cens:.1f}%); "
        f"Compositional L=4 (beta={kl_beta}): Base(p@1={100*base_comp_p1:.2f}%,p@256={100*base_comp_p256:.1f}%), "
        f"FrozenKL_Trap(p@1={100*frozen_kl_p1:.2f}%,p@256={100*frozen_kl_p256:.1f}%), "
        f"ProRL_Reset(p@1={100*prorl_p1:.1f}%,p@256={100*prorl_p256:.1f}%)"
    )
    return lines


# ---------------------------------------------------------------------------
# Probe 5: Live Synthetic-Pipeline Deduplication & Post-Processing Forensics
# ---------------------------------------------------------------------------

def self_instruct_rouge_l_fmeasure(target: str, prediction: str) -> float:
    """Exact reproduction of google-research/rouge_score rougeL (use_stemmer=False)
    called at yizhongw/self-instruct@0b26ccaa:self_instruct/bootstrap_instructions.py:L152, L197-L200."""
    tok_re = re.compile(r"[a-z0-9]+")
    t_toks = tok_re.findall(target.lower())
    p_toks = tok_re.findall(prediction.lower())
    if not t_toks or not p_toks:
        return 0.0
    m, n = len(t_toks), len(p_toks)
    dp = [0] * (n + 1)
    for i in range(1, m + 1):
        prev = 0
        ti = t_toks[i - 1]
        for j in range(1, n + 1):
            cur = dp[j]
            if ti == p_toks[j - 1]:
                dp[j] = prev + 1
            elif dp[j - 1] > dp[j]:
                dp[j] = dp[j - 1]
            prev = cur
    lcs = dp[n]
    if lcs == 0:
        return 0.0
    prec = lcs / n
    rec = lcs / m
    return (2.0 * prec * rec) / (prec + rec)


def self_instruct_post_process_keep(inst: str) -> bool:
    """Exact reproduction of post_process_gpt3_response filter rules in
    yizhongw/self-instruct@0b26ccaa:self_instruct/bootstrap_instructions.py:L47-L69."""
    inst = re.sub(r"\s+", " ", inst).strip().capitalize()
    if inst == "":
        return False
    if len(inst.split()) <= 3 or len(inst.split()) > 150:
        return False
    blacklist = [
        "image", "images", "graph", "graphs", "picture", "pictures",
        "file", "files", "map", "maps", "draw", "plot", "go to",
    ]
    if any(re.compile(rf"\b({w})\b", flags=re.IGNORECASE).search(inst) for w in blacklist):
        return False
    if inst.startswith("Write a program"):
        return False
    if inst[0] in string.punctuation or not inst[0].isascii():
        return False
    return True


def self_instruct_filter_duplicate_instances(instances: Sequence[tuple[str, str, str]]) -> list[tuple[str, str, str]]:
    """Exact reproduction of filter_duplicate_instances in
    yizhongw/self-instruct@0b26ccaa:self_instruct/prepare_for_finetuning.py:L110-L125."""
    same_input_diff_output = False
    for i in range(1, len(instances)):
        for j in range(0, i):
            if instances[i][1] == "":
                continue
            if instances[i][1] == instances[j][1] and instances[i][2] != instances[j][2]:
                same_input_diff_output = True
                break
    if same_input_diff_output:
        return []
    return sorted(set(instances))


_MERSENNE_PRIME = (1 << 61) - 1
_UINT64_MASK = (1 << 64) - 1
# Exact PUNCTUATION table from huggingface/datatrove@5484e67a:src/datatrove/utils/text.py:L13-L18, L182
_DATATROVE_PUNCTUATION = (
    "!/—”:％１〈&(、━\\【#%「」，】；+^]~“《„';’{|∶´[=-`*．（–？！：$～«〉,><》)?）。…@_.\"}►»"
    + "".join(chr(x) for a, b in ((0, 9), (11, 13), (13, 32), (127, 160)) for x in range(a, b))
)
_DATATROVE_PUNCT_TRANS = str.maketrans(_DATATROVE_PUNCTUATION, " " * len(_DATATROVE_PUNCTUATION))
_DATATROVE_DECIMAL_SEPS = frozenset(".,،٫⎖⎗⎘")


def _replace_unicode_nd_numbers(text: str) -> str:
    """Pure-stdlib implementation of datatrove NUMBERS_PATTERN = r'\\p{Nd}+([.,،٫⎖⎗⎘]{1}\\p{Nd}+)?'
    (src/datatrove/utils/text.py:L202-L205) using unicodedata.category == 'Nd' without third-party `regex`."""
    out: list[str] = []
    n = len(text)
    i = 0
    while i < n:
        if unicodedata.category(text[i]) == "Nd":
            while i < n and unicodedata.category(text[i]) == "Nd":
                i += 1
            if i + 1 < n and text[i] in _DATATROVE_DECIMAL_SEPS and unicodedata.category(text[i + 1]) == "Nd":
                i += 1
                while i < n and unicodedata.category(text[i]) == "Nd":
                    i += 1
            out.append("0")
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def datatrove_simplify_text(text: str, norm_numbers: bool = True) -> str:
    """Behavioral port of datatrove.utils.text.simplify_text (src/datatrove/utils/text.py:L212-L258)
    preserving exact PUNCTUATION translation and Unicode Category 'Nd' number normalization in pure stdlib."""
    text = text.lower()
    if norm_numbers:
        text = _replace_unicode_nd_numbers(text)
    text = text.translate(_DATATROVE_PUNCT_TRANS)
    text = re.sub(r"\s+", " ", text.strip())
    text = "".join(c for c in unicodedata.normalize("NFD", text) if unicodedata.category(c) != "Mn")
    return text.strip()


def datatrove_shingles(text: str, n_grams: int = 5, norm_numbers: bool = True) -> list[int]:
    """Behavioral port of MinhashDedupSignature.get_shingles (minhash.py:L190-L210) using
    datatrove's built-in sha1_hash64 (`HashConfig(precision=64, hash_fc='sha1')`, hashes/sha1.py:L22-L31)
    and pure-stdlib whitespace word splitting on simplified text (substituting for default C-extension
    `xxhash64` and `SpaCyTokenizer('en').word_tokenize`)."""
    simplified = datatrove_simplify_text(text, norm_numbers=norm_numbers)
    words = [w for w in simplified.split(" ") if w]
    if len(words) < n_grams:
        return []
    out: list[int] = []
    for i in range(len(words) - n_grams + 1):
        gram = " ".join(words[i : i + n_grams]).encode("utf-8")
        h64 = struct.unpack("<Q", hashlib.sha1(gram).digest()[:8])[0]
        out.append(h64)
    return out


def datatrove_minhash_dedup(
    docs: Sequence[str],
    n_grams: int = 5,
    num_buckets: int = 14,
    hashes_per_bucket: int = 8,
    norm_numbers: bool = True,
    tmp_dir: Path | None = None,
) -> list[int]:
    """Behavioral port of MinhashDedupSignature -> MinhashDedupBuckets -> MinhashDedupCluster
    (huggingface/datatrove@5484e67a:minhash.py:L51-L55, L165-L262, L471-L482, L546-L594) with exact
    uint64 2^64 modular wraparound prior to `% _MERSENNE_PRIME`. Disclosed stdlib substitutions:
    `sha1_hash64` for `xxhash64`, `random.Random(1)` for `np.random.RandomState(1)`, and whitespace
    token splitting for `SpaCyTokenizer('en')`."""
    num_hashes = num_buckets * hashes_per_bucket
    prm_rng = random.Random(1)
    a_params = [prm_rng.randrange(1, _MERSENNE_PRIME) for _ in range(num_hashes)]
    b_params = [prm_rng.randrange(0, _MERSENNE_PRIME) for _ in range(num_hashes)]

    ab_pairs = list(zip(a_params, b_params))
    u64_mask = _UINT64_MASK
    mersenne = _MERSENNE_PRIME
    bucket_entries: list[list[tuple[tuple[int, ...], int]]] = [[] for _ in range(num_buckets)]
    for doc_idx, text in enumerate(docs):
        shingles = datatrove_shingles(text, n_grams=n_grams, norm_numbers=norm_numbers)
        if len(shingles) != 0:
            mins = [
                min(((((sh * a_h) & u64_mask) + b_h) & u64_mask) % mersenne for sh in shingles)
                for a_h, b_h in ab_pairs
            ]
            for b_idx in range(num_buckets):
                start = b_idx * hashes_per_bucket
                sig = tuple(mins[start : start + hashes_per_bucket])
                bucket_entries[b_idx].append((sig, doc_idx))

    dup_pairs: list[tuple[int, int]] = []
    for b_idx in range(num_buckets):
        entries = sorted(bucket_entries[b_idx])
        if tmp_dir is not None:
            sig_path = tmp_dir / f"bucket_{b_idx:03d}.sig"
            with sig_path.open("wb") as bf:
                for sig, doc_id in entries:
                    bf.write(struct.pack(f"<{hashes_per_bucket}QI", *sig, doc_id))
        for idx in range(1, len(entries)):
            if entries[idx - 1][0] == entries[idx][0]:
                dup_pairs.append((entries[idx - 1][1], entries[idx][1]))

    union_set: dict[int, int] = {}
    set_size: dict[int, int] = {}

    def parent(x: int) -> int:
        if x not in union_set or union_set[x] == x:
            union_set[x] = x
            return x
        union_set[x] = parent(union_set[x])
        return union_set[x]

    def union(va: int, vb: int) -> None:
        ra, rb = parent(va), parent(vb)
        if ra != rb:
            sa = set_size.get(ra, 1)
            sb = set_size.get(rb, 1)
            if sa < sb:
                ra, rb = rb, ra
            union_set[rb] = ra
            set_size[ra] = sa + sb
            set_size.pop(rb, None)

    for d1, d2 in dup_pairs:
        union(d1, d2)

    to_remove = {node for node in sorted(union_set) if node != parent(node)}
    return [idx for idx in range(len(docs)) if idx not in to_remove]


def openr1_decontaminate_is_contaminated(train_doc: str, eval_docs: Sequence[str], ngram_size: int = 8) -> bool:
    """Exact reproduction of huggingface/open-r1@5b6ff22b:scripts/decontaminate.py:L36-L68, L118-L122."""
    def norm_and_ngrams(txt: str) -> set[str]:
        norm = " ".join(txt.lower().strip().split())
        words = norm.split()
        return {" ".join(words[i : i + ngram_size]) for i in range(len(words) - ngram_size + 1)}

    lookup: set[str] = set()
    for ed in eval_docs:
        lookup.update(norm_and_ngrams(ed))
    train_ngrams = norm_and_ngrams(train_doc)
    return any(ng in lookup for ng in train_ngrams)


def run_probe_5() -> list[str]:
    lines: list[str] = []
    lines.append("=== Probe 5: Live Synthetic-Pipeline Deduplication & Decontamination Forensics ===")

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)

        seed_inst = "Classify the sentiment of the customer product review into positive, neutral, or negative."
        morph_clone = "Classification of sentiments for customers reviewing products as negative, neutral, or positive."
        clause_swap = "Into negative, neutral, or positive labels, classify the customer product review sentiment."
        rl_morph = self_instruct_rouge_l_fmeasure(seed_inst, morph_clone)
        rl_swap = self_instruct_rouge_l_fmeasure(seed_inst, clause_swap)
        assert rl_morph <= 0.70 and rl_swap <= 0.70

        valid_text_prompts = [
            "Summarize the main plot twists in Shakespeare's tragedy Hamlet.",
            "Prove that every tree is a connected acyclic bipartite graph.",
            "Draw a logically valid conclusion from the two syllogistic premises.",
            "Explain how freelancers should file quarterly estimated tax returns.",
        ]
        kept_valid = sum(1 for p in valid_text_prompts if self_instruct_post_process_keep(p))
        prog_bypass = self_instruct_post_process_keep("Write a Python program to sort integers in place.")
        assert kept_valid == 0 and prog_bypass is True

        creative_task_instances = [
            ("Suggest a concise title", "A mystery novel set in Venice", "Shadows on the Grand Canal"),
            ("Suggest a concise title", "A cookbook for busy students", "Five-Minute Dorm Meals"),
            ("Suggest a concise title", "A mystery novel set in Venice", "The Gondolier's Alibi"),
            ("Suggest a concise title", "A history of quantum mechanics", "Quanta and Paradox"),
        ]
        surviving_creative = self_instruct_filter_duplicate_instances(creative_task_instances)
        assert surviving_creative == []

        lines.append(
            "  [exact reproduction of pinned repository logic] "
            f"self-instruct@0b26ccaa: unstemmed ROUGE-L<=0.7 misses morph_clone={rl_morph:.3f} & "
            f"clause_swap={rl_swap:.3f}; regex blacklist rejects {len(valid_text_prompts)-kept_valid}/{len(valid_text_prompts)} "
            f"valid text tasks while 'Write a Python program' bypass={prog_bypass}; "
            f"filter_duplicate_instances wipes {len(creative_task_instances)}->0 instances on multi-output task"
        )

        # Datatrove MinHash (n=5, b=14, r=8) exact LSH curve + 4 structural hazards
        s_half = (1.0 - 0.5 ** (1.0 / 14.0)) ** (1.0 / 8.0)
        p_at_08 = 1.0 - (1.0 - (0.8 ** 8)) ** 14
        p_at_05 = 1.0 - (1.0 - (0.5 ** 8)) ** 14
        assert abs((1.0 - (1.0 - (s_half ** 8)) ** 14) - 0.5) < 1e-15
        assert 0.6846 < s_half < 0.6848 and p_at_08 > 0.9235 and p_at_05 > 0.0533

        short_docs = ["Translate English to French!"] * 40
        kept_short = datatrove_minhash_dedup(short_docs, tmp_dir=tmp_path)
        assert len(kept_short) == 40

        orig_doc = "compute the eigenvalues of a real symmetric matrix using orthogonal jacobi rotations"
        para_doc = "compute the eigenvalues of any real symmetric matrix via orthogonal jacobi iterations"
        sh_orig = set(datatrove_shingles(orig_doc))
        sh_para = set(datatrove_shingles(para_doc))
        jacc_para = len(sh_orig & sh_para) / len(sh_orig | sh_para)
        kept_para = datatrove_minhash_dedup([orig_doc, para_doc], tmp_dir=tmp_path)
        assert jacc_para == 0.0 and len(kept_para) == 2

        distinct_math_docs = [
            f"Find the positive integer remainder when {7 + 2*k}^{1900 + 3*k} + {11 + 4*k}^{2000 + 5*k} is divided by {97 + 6*k}."
            for k in range(25)
        ]
        kept_math_default = datatrove_minhash_dedup(distinct_math_docs, norm_numbers=True, tmp_dir=tmp_path)
        kept_math_fixed = datatrove_minhash_dedup(distinct_math_docs, norm_numbers=False, tmp_dir=tmp_path)
        assert len(kept_math_default) == 1 and len(kept_math_fixed) == 25

        vocab_chain = [f"tok{chr(97 + i // 26)}{chr(97 + i % 26)}" for i in range(120)]
        chain_docs = [" ".join(vocab_chain[2 * step : 2 * step + 36]) for step in range(19)]
        sh_first = set(datatrove_shingles(chain_docs[0]))
        sh_last = set(datatrove_shingles(chain_docs[-1]))
        assert len(sh_first & sh_last) == 0
        kept_chain = datatrove_minhash_dedup(chain_docs, tmp_dir=tmp_path)
        assert len(kept_chain) == 1

        lines.append(
            "  [behavioral port of pinned repository algorithm] "
            f"datatrove@5484e67a MinHash(5,14,8; sha1+uint64 port; s_0.5={s_half:.4f}, P(0.8)={p_at_08:.4f}, P(0.5)={p_at_05:.4f}): "
            f"<5w_dup_kept={len(kept_short)}/40 (100% leak); 1-in-5_paraphrase_J={jacc_para:.2f} (kept={len(kept_para)}/2); "
            f"norm_numbers=True wipes {25-len(kept_math_default)}/25 distinct math problems (norm_numbers=False keeps {len(kept_math_fixed)}/25); "
            f"Union-Find chains 19 docs (endpoint J=0.0) -> {len(kept_chain)} survivor"
        )

        aime_eval = [
            "Let $x$ and $y$ be positive real numbers satisfying $x + y = 12$ and $x y = 27$. Compute $x^3 + y^3$."
        ]
        exact_copy = aime_eval[0]
        latex_spaced_copy = (
            "Let x and y be positive, real numbers satisfying x+y=12 and xy=27; compute x^3+y^3."
        )
        det_exact = openr1_decontaminate_is_contaminated(exact_copy, aime_eval, ngram_size=8)
        det_spaced = openr1_decontaminate_is_contaminated(latex_spaced_copy, aime_eval, ngram_size=8)

        det_fixed = openr1_decontaminate_is_contaminated(
            datatrove_simplify_text(latex_spaced_copy, norm_numbers=False),
            [datatrove_simplify_text(e, norm_numbers=False) for e in aime_eval],
            ngram_size=8,
        )
        assert det_exact is True and det_spaced is False and det_fixed is True

        lines.append(
            "  [exact reproduction of pinned repository logic] "
            f"open-r1@5b6ff22b decontaminate.py (8-gram whitespace split): exact_match={det_exact}, "
            f"punctuation/LaTeX-reformatted_match={det_spaced} (false-negative leak), punct_stripped_fix={det_fixed}"
        )

    return lines


def main() -> None:
    sections = [
        run_probe_1(),
        run_probe_2(),
        run_probe_3(),
        run_probe_4(),
        run_probe_5(),
    ]
    output_lines = [
        "SYNTHETIC DATA COLLAPSE, VERIFIER FILTERING & CURRICULUM FORENSICS PROBE",
        "All assertions passed: 5/5 probe pillars verified deterministically.",
        "",
    ]
    for sec in sections:
        output_lines.extend(sec)
        output_lines.append("")
    print("\n".join(output_lines).rstrip())


if __name__ == "__main__":
    main()
