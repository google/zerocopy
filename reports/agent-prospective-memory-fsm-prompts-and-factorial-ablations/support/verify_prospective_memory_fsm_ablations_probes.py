#!/usr/bin/env python3
"""Standalone Python 3.10+ stdlib verification suite for prospective-memory control,
combinatorial prompt/skill ablations, sequential stopping, and workflow-DAG evaluation.

Dependencies: Python 3.10+ standard library only (zero third-party packages,
zero filesystem writes, zero network calls, deterministic stdout across hash seeds).

Probes:
  1. Plackett-Burman (H12, Sylvester H16) vs. Resolution-IV Foldover vs. LOO:
     exact algebraic alias matrix A = (X^T X)^(-1) X^T X_int, analytical and
     Monte Carlo covariance verification (N/2-fold variance reduction), LOO
     blindness on redundant OR guardrails, PB12 |A| = 1/3 smearing, H16 |A| in {0, 1}
     complete aliasing (3-5 complete aliases across columns 0-10), and 24-run
     foldover exact zero 2-way aliasing (Resolution IV, non-zero 3-way).
  2. Zeller-Hildebrandt ddmin (both 2-phase IEEE TSE Fig. 5 p. 187 algorithm and
     debuggingbook complement-only variant): 1-minimality under monotonicity
     (Definition 10 p. 186, Proposition 11 p. 188), single-defect <= 2 log2(n)
     bound (Proposition 13 p. 188), exact Theta(n^2) oracle complexity verifying
     uncached 2-phase ddmin obeys Proposition 12's n^2 + 3n bound (exact DP global
     maximum n^2 + 3n - 10) while Fig. 6 query memoization tightens monotone unique
     oracle evaluations to <= (n^2 + 3n - 2)/2, and non-monotone compensatory-clause
     root-cause deletion (pushy_c1 masked by guard_c2 until [guard_c2, bad_c4] drop).
  3. ContextCite uniform-mask linear surrogate vs. KernelSHAP vs. LOO:
     exact 2^d Boolean hypercube verification (d = 10) proving population
     uniform-mask centered OLS equals exact Banzhaf values (distinct from Shapley
     / KernelSHAP on 3-way AND synergies, rescuing disjunctive OR pairs at +2.0
     vs. 0.0 LOO, while assigning 0.0 to pure XOR parity pairs), plus M = 64
     standardized coordinate-descent LASSO (at default alpha = 0.01 and alpha = 0.05,
     verifying fixed-output num_output_tokens sequence-level penalty multiplication),
     and ridge-regularized subsampling.
  4. Anytime-valid sequential testing (Johari Gaussian mSPRT with fixed tau2 = 0.25
     across H0 and H1 at power-matched horizon N_max = 142 vs. n_fixed = 86, and
     exact finite-sample Beta-Binomial McNemar e-process via forward DP vs.
     power-matched exact Binomial McNemar m_fixed = 35), exact reproduction and
     sentinel-bridge-preserving repair of three live defects in zjunlp/WorfBench@38a64555
     evaluator/graph_evaluator.py + node_eval.py (including parallel fan-out/fan-in
     fork-join DAGs), and an explicit R_max = 50 harness-resumption absorbing Markov
     analytical model of Gates x Stop FSM control regimes.
"""

from __future__ import annotations

import json
import math
import random
from functools import lru_cache
from itertools import combinations
from typing import Callable, Sequence


# =============================================================================
# Linear algebra helpers (pure Python stdlib, exact Gaussian elimination)
# =============================================================================

def mat_transpose(a: Sequence[Sequence[float]]) -> list[list[float]]:
    rows, cols = len(a), len(a[0])
    return [[float(a[r][c]) for r in range(rows)] for c in range(cols)]


def mat_mul(a: Sequence[Sequence[float]], b: Sequence[Sequence[float]]) -> list[list[float]]:
    r_a, c_a, c_b = len(a), len(a[0]), len(b[0])
    bt = mat_transpose(b)
    return [[sum(a[i][p] * bt[j][p] for p in range(c_a)) for j in range(c_b)] for i in range(r_a)]


def mat_inv(a: Sequence[Sequence[float]]) -> list[list[float]]:
    """Invert a square non-singular matrix via Gauss-Jordan partial pivoting."""
    n = len(a)
    aug = [
        [float(a[i][j]) for j in range(n)] + [1.0 if i == j else 0.0 for j in range(n)]
        for i in range(n)
    ]
    for col in range(n):
        piv = max(range(col, n), key=lambda r: abs(aug[r][col]))
        if abs(aug[piv][col]) < 1e-14:
            raise ValueError(f"Singular matrix at column {col}")
        aug[col], aug[piv] = aug[piv], aug[col]
        scale = aug[col][col]
        inv_scale = 1.0 / scale
        aug[col] = [v * inv_scale for v in aug[col]]
        for r in range(n):
            if r != col and aug[r][col] != 0.0:
                factor = aug[r][col]
                aug[r] = [aug[r][c] - factor * aug[col][c] for c in range(2 * n)]
    return [row[n:] for row in aug]


# =============================================================================
# PROBE 1: Plackett-Burman (H12, H16) vs. Resolution-IV Foldover vs. LOO
# =============================================================================

def build_paley_pb12() -> list[list[int]]:
    """Plackett & Burman (1946, p. 323) N=12, k=11 cyclic generator + all-minus row."""
    gen = [1, 1, -1, 1, 1, 1, -1, -1, -1, 1, -1]
    rows = [gen[-s:] + gen[:-s] if s else list(gen) for s in range(11)]
    rows.append([-1] * 11)
    return rows


def build_sylvester_h16(k: int = 11) -> list[list[int]]:
    """Sylvester Hadamard H16 fractional design (first k non-intercept columns)."""
    h = [[1]]
    for _ in range(4):
        h = [r + r for r in h] + [r + [-x for x in r] for r in h]
    return [[row[c] for c in range(1, k + 1)] for row in h]


def build_loo_design(k: int = 11) -> list[list[int]]:
    """12-run one-at-a-time Leave-One-Out design: 1 all-(+1) baseline + k single-drop runs."""
    rows = [[1] * k]
    for j in range(k):
        row = [1] * k
        row[j] = -1
        rows.append(row)
    return rows


def compute_alias_and_cov(
    x_main: Sequence[Sequence[int]],
) -> tuple[list[list[float]], list[list[float]], list[tuple[int, int]]]:
    """Compute exact (X^T X)^(-1) covariance factor and 2-way alias matrix
    A = (X^T X)^(-1) X^T X_int where X prepends intercept column x_0 = +1.
    Returns (xtx_inv, alias_main_rows, pairs) where alias_main_rows has shape k x C(k,2).
    """
    n = len(x_main)
    k = len(x_main[0])
    pairs = list(combinations(range(k), 2))
    x_design = [[1.0] + [float(x_main[u][j]) for j in range(k)] for u in range(n)]
    x_int = [[float(x_main[u][l] * x_main[u][m]) for l, m in pairs] for u in range(n)]
    xt = mat_transpose(x_design)
    xtx_inv = mat_inv(mat_mul(xt, x_design))
    proj = mat_mul(xtx_inv, xt)
    alias_full = mat_mul(proj, x_int)  # (k+1) x C(k,2)
    return xtx_inv, alias_full[1:], pairs


def run_probe_1() -> dict:
    k = 11
    pb12 = build_paley_pb12()
    h16 = build_sylvester_h16(k)
    fold24 = pb12 + [[-x for x in row] for row in pb12]
    loo12 = build_loo_design(k)

    cov_pb12, alias_pb12, pairs = compute_alias_and_cov(pb12)
    cov_h16, alias_h16, _ = compute_alias_and_cov(h16)
    cov_fold24, alias_fold24, _ = compute_alias_and_cov(fold24)
    cov_loo12, alias_loo12, _ = compute_alias_and_cov(loo12)

    # 1. Exact analytical variance & covariance:
    # Orthogonal Hadamard designs satisfy (X^T X)^(-1) = (1/N) I_{k+1}:
    #   Var(beta_hat_j) = sigma^2 / N, Var(tau_hat_j) = 4 sigma^2 / N, Corr = 0.
    # For N=12 LOO, beta_hat_j = (y_0 - y_j)/2:
    #   Var(beta_hat_j) = sigma^2 / 2 = (N/2) * (sigma^2 / N), Corr(j, m) = +0.5.
    for idx in range(1, k + 1):
        assert math.isclose(cov_pb12[idx][idx], 1.0 / 12.0, abs_tol=1e-12)
        assert math.isclose(cov_h16[idx][idx], 1.0 / 16.0, abs_tol=1e-12)
        assert math.isclose(cov_fold24[idx][idx], 1.0 / 24.0, abs_tol=1e-12)
        assert math.isclose(cov_loo12[idx][idx], 0.5, abs_tol=1e-12)
    assert math.isclose(cov_pb12[1][2], 0.0, abs_tol=1e-12)
    assert math.isclose(cov_loo12[1][2] / cov_loo12[1][1], 0.5, abs_tol=1e-12)

    # 2. Exact 2-way alias matrix structure across all four designs:
    # - LOO12: A_{j,(l,m)} = +1 iff j in {l, m} (10 incident aliases of +1.0, 0 non-incident).
    for j in range(k):
        for p_idx, (l, m) in enumerate(pairs):
            expected_loo = 1.0 if j in (l, m) else 0.0
            assert math.isclose(alias_loo12[j][p_idx], expected_loo, abs_tol=1e-12)

    # - PB12: 0 on all 10 incident pairs, |A| = 1/3 on all C(10, 2) = 45 non-incident pairs.
    for j in range(k):
        pb12_inc = [alias_pb12[j][i] for i, p in enumerate(pairs) if j in p]
        pb12_noninc = [alias_pb12[j][i] for i, p in enumerate(pairs) if j not in p]
        assert all(math.isclose(v, 0.0, abs_tol=1e-12) for v in pb12_inc)
        assert len(pb12_noninc) == 45
        assert all(math.isclose(abs(v), 1.0 / 3.0, abs_tol=1e-12) for v in pb12_noninc)

    # - Sylvester H16 (k=11): 0 on incident pairs, |A| in {0, 1} on non-incident pairs;
    #   columns 0-2 have 5 complete aliases, while columns 3-10 have 3 complete aliases.
    h16_complete_by_col: list[int] = []
    for j in range(k):
        for i, p in enumerate(pairs):
            if j in p:
                assert math.isclose(alias_h16[j][i], 0.0, abs_tol=1e-12)
            else:
                assert math.isclose(abs(alias_h16[j][i]), 0.0, abs_tol=1e-12) or math.isclose(
                    abs(alias_h16[j][i]), 1.0, abs_tol=1e-12
                )
        h16_complete_by_col.append(sum(1 for v in alias_h16[j] if abs(v) > 1e-12))
    assert h16_complete_by_col[:3] == [5, 5, 5] and h16_complete_by_col[3:] == [3] * 8

    # - Fold24: Resolution IV -> EVERY entry of the 11 x 55 two-way alias matrix is identically 0!
    max_abs_fold24_2way = max(abs(v) for row in alias_fold24 for v in row)
    assert math.isclose(max_abs_fold24_2way, 0.0, abs_tol=1e-12)
    # Non-vacuity negative control: verify Fold24 is Resolution IV (NOT V) — 3-way aliases ARE non-zero!
    three_way_0123 = sum(fold24[u][0] * fold24[u][1] * fold24[u][2] * fold24[u][3] for u in range(24)) / 24.0
    assert math.isclose(abs(three_way_0123), 1.0 / 3.0, abs_tol=1e-12)

    # 3. Noiseless estimands + Monte Carlo verification on redundant OR guardrails & interactions
    beta0 = 0.50
    beta = [0.15, 0.15, 0.10, -0.08, 0.0, 0.0, 0.05, 0.0, 0.0, 0.0, 0.0]
    inter = {(0, 1): -0.15, (2, 3): 0.24}
    sigma = 0.10

    def eval_mean(x: Sequence[int]) -> float:
        return (
            beta0
            + sum(beta[j] * x[j] for j in range(k))
            + inter[(0, 1)] * x[0] * x[1]
            + inter[(2, 3)] * x[2] * x[3]
        )

    mu_pb12 = [eval_mean(r) for r in pb12]
    mu_h16 = [eval_mean(r) for r in h16]
    mu_fold24 = [eval_mean(r) for r in fold24]
    mu_loo_base = eval_mean(loo12[0])
    mu_loo_drop0 = eval_mean(loo12[1])

    est_loo0 = 0.5 * (mu_loo_base - mu_loo_drop0)
    est_pb12_0 = sum(pb12[u][0] * mu_pb12[u] for u in range(12)) / 12.0
    est_h16_0 = sum(h16[u][0] * mu_h16[u] for u in range(16)) / 16.0
    est_fold24_0 = sum(fold24[u][0] * mu_fold24[u] for u in range(24)) / 24.0

    p23_idx = pairs.index((2, 3))
    assert math.isclose(est_loo0, 0.0, abs_tol=1e-12)  # Complete LOO blindness on OR guardrail!
    assert math.isclose(est_pb12_0, beta[0] + alias_pb12[0][p23_idx] * inter[(2, 3)], abs_tol=1e-12)
    assert math.isclose(est_fold24_0, beta[0], abs_tol=1e-12)  # Exact unbiased recovery!

    rng = random.Random(20261122)
    gauss = rng.gauss
    mc_trials = 3000
    c_pb0 = [pb12[u][0] / 12.0 for u in range(12)]
    c_h16_0 = [h16[u][0] / 16.0 for u in range(16)]
    c_f24_0 = [fold24[u][0] / 24.0 for u in range(24)]

    s_loo: list[float] = []
    s_pb: list[float] = []
    s_h16: list[float] = []
    s_f24: list[float] = []
    for _ in range(mc_trials):
        s_loo.append(0.5 * ((mu_loo_base + gauss(0.0, sigma)) - (mu_loo_drop0 + gauss(0.0, sigma))))
        s_pb.append(sum(c_pb0[u] * (mu_pb12[u] + gauss(0.0, sigma)) for u in range(12)))
        s_h16.append(sum(c_h16_0[u] * (mu_h16[u] + gauss(0.0, sigma)) for u in range(16)))
        s_f24.append(sum(c_f24_0[u] * (mu_fold24[u] + gauss(0.0, sigma)) for u in range(24)))

    def sample_var(xs: Sequence[float]) -> float:
        m = sum(xs) / len(xs)
        return sum((v - m) * (v - m) for v in xs) / (len(xs) - 1)

    v_loo = sample_var(s_loo)
    v_pb = sample_var(s_pb)
    v_h16 = sample_var(s_h16)
    v_f24 = sample_var(s_f24)
    assert 5.4 <= (v_loo / v_pb) <= 6.6

    return {
        "k_factors": k,
        "alias_structure": {
            "LOO12_incident_aliases_weight_1": sum(1 for v in alias_loo12[0] if math.isclose(v, 1.0)),
            "PB12_incident_aliases": 0,
            "PB12_nonincident_aliases_abs_one_third": 45,
            "H16_complete_aliases_by_col": h16_complete_by_col,
            "H16_complete_aliases_range": [min(h16_complete_by_col), max(h16_complete_by_col)],
            "Fold24_two_way_aliases": 0,
            "Fold24_sample_three_way_alias_0123": round(abs(three_way_0123), 6),
        },
        "noiseless_half_effect_beta0": {
            "ground_truth": beta[0],
            "LOO12": round(est_loo0, 6),
            "PB12": round(est_pb12_0, 6),
            "H16": round(est_h16_0, 6),
            "Fold24": round(est_fold24_0, 6),
        },
        "analytical_half_effect_var_over_sigma2": {
            "LOO12": round(cov_loo12[1][1], 6),
            "PB12": round(cov_pb12[1][1], 6),
            "H16": round(cov_h16[1][1], 6),
            "Fold24": round(cov_fold24[1][1], 6),
            "PB12_variance_reduction_vs_LOO12": round(cov_loo12[1][1] / cov_pb12[1][1], 4),
            "LOO12_inter_factor_corr": round(cov_loo12[1][2] / cov_loo12[1][1], 4),
            "PB12_inter_factor_corr": 0.0,
        },
        "monte_carlo_half_effect_var_sigma0_10": {
            "LOO12": round(v_loo, 6),
            "PB12": round(v_pb, 6),
            "H16": round(v_h16, 6),
            "Fold24": round(v_f24, 6),
            "empirical_LOO12_over_PB12_ratio": round(v_loo / v_pb, 3),
        },
    }


# =============================================================================
# PROBE 2: Zeller-Hildebrandt ddmin (2-Phase Fig. 5 & Complement-Only)
# =============================================================================

PASS, FAIL, UNRESOLVED = "PASS", "FAIL", "UNRESOLVED"


def split_chunks(seq: Sequence[str], n: int) -> list[list[str]]:
    """Exact partition of seq into n contiguous chunks (Zeller & Hildebrandt 2002, Fig. 5, p. 187)."""
    k, rem = divmod(len(seq), n)
    out: list[list[str]] = []
    pos = 0
    for i in range(n):
        step = k + (1 if i < rem else 0)
        out.append(list(seq[pos : pos + step]))
        pos += step
    return out


def ddmin_two_phase(test_fn: Callable[[Sequence[str]], str], inp: Sequence[str]) -> tuple[list[str], int]:
    """Exact Zeller & Hildebrandt (2002, Fig. 5, p. 187) 2-phase ddmin:
    tests subsets Delta_i first (reduce_to_subset), then complements Nabla_i (reduce_to_complement).
    At n == 2, Nabla_1 = Delta_2 and Nabla_2 = Delta_1, so complement tests are skipped when n == 2.
    Counts oracle evaluations inside ddmin2 after precondition test(inp) == FAIL.
    """
    calls = 0

    def run_test(s: Sequence[str]) -> str:
        nonlocal calls
        calls += 1
        return test_fn(s)

    cur = list(inp)
    n = 2
    while len(cur) >= 2:
        chunks = split_chunks(cur, n)
        reduced = False
        # Phase 1: reduce to subset Delta_i
        for chunk in chunks:
            if run_test(chunk) == FAIL:
                cur = chunk
                n = 2
                reduced = True
                break
        if not reduced and n > 2:
            # Phase 2: reduce to complement Nabla_i (for n > 2)
            for i in range(n):
                comp = [x for idx, ch in enumerate(chunks) if idx != i for x in ch]
                if run_test(comp) == FAIL:
                    cur = comp
                    n = max(n - 1, 2)
                    reduced = True
                    break
        if not reduced:
            if n == len(cur):
                break
            n = min(n * 2, len(cur))
    return cur, calls


@lru_cache(maxsize=None)
def dp_max_uncached_calls_two_phase(m: int, n: int = 2) -> int:
    """Exact dynamic-programming global maximum uncached call count of 2-phase Fig. 5 ddmin
    starting from configuration size m >= 2 and granularity n (2 <= n <= m).
    Proves global maximum = m^2 + 3m - 10 <= Proposition 12's m^2 + 3m bound (p. 188).
    """
    if m < 2:
        return 0
    k, rem = divmod(m, n)
    chunk_sizes = [k + (1 if i < rem else 0) for i in range(n)]
    best = 0
    for i, sz in enumerate(chunk_sizes):
        cost = (i + 1) + (dp_max_uncached_calls_two_phase(sz, 2) if sz >= 2 else 0)
        if cost > best:
            best = cost
    if n > 2:
        for i, sz in enumerate(chunk_sizes):
            comp_m = m - sz
            next_n = min(max(n - 1, 2), comp_m)
            cost = n + (i + 1) + (dp_max_uncached_calls_two_phase(comp_m, next_n) if comp_m >= 2 else 0)
            if cost > best:
                best = cost
        step_all_pass = 2 * n
    else:
        step_all_pass = n
    if n == m:
        if step_all_pass > best:
            best = step_all_pass
    else:
        cost_double = step_all_pass + dp_max_uncached_calls_two_phase(m, min(2 * n, m))
        if cost_double > best:
            best = cost_double
    return best


def ddmin_complement_only(test_fn: Callable[[Sequence[str]], str], inp: Sequence[str]) -> tuple[list[str], int]:
    """Exact port of uds-se/debuggingbook@35dfb6c7 docs/code/DeltaDebugger.py:275-310."""
    calls = 0

    def run_test(s: Sequence[str]) -> str:
        nonlocal calls
        calls += 1
        return test_fn(s)

    cur = list(inp)
    assert run_test(cur) == FAIL
    n = 2
    while len(cur) >= 2:
        start = 0
        subset_length = int(len(cur) / n)
        some_complement_is_failing = False
        while start < len(cur):
            complement = cur[:start] + cur[start + subset_length :]
            if run_test(complement) == FAIL:
                cur = complement
                n = max(n - 1, 2)
                some_complement_is_failing = True
                break
            start += subset_length
        if not some_complement_is_failing:
            if n == len(cur):
                break
            n = min(n * 2, len(cur))
    return cur, calls


def is_one_minimal(test_fn: Callable[[Sequence[str]], str], subset: Sequence[str]) -> bool:
    """Definition 10 (p. 186) & Proposition 11 (p. 188) 1-minimality predicate."""
    if test_fn(subset) != FAIL:
        return False
    return all(test_fn(list(subset[:i]) + list(subset[i + 1 :])) != FAIL for i in range(len(subset)))


def run_probe_2() -> dict:
    # 1. Single atomic defect among n = 64 clauses -> <= 2 log2(64) = 12 tests (Proposition 13, p. 188)
    inp64 = [f"clause_{i}" for i in range(64)]
    single_oracle = lambda s: FAIL if "clause_42" in set(s) else PASS
    r2_single, c2_single = ddmin_two_phase(single_oracle, inp64)
    rc_single, cc_single = ddmin_complement_only(single_oracle, inp64)
    assert r2_single == ["clause_42"] and is_one_minimal(single_oracle, r2_single)
    assert rc_single == ["clause_42"] and is_one_minimal(single_oracle, rc_single)
    assert c2_single <= 2 * 6  # Proposition 13 (p. 188): <= 2 * log2(n) = 12

    # 2. Verify exact DP global maximum of uncached 2-phase Fig. 5 ddmin = n^2 + 3n - 10 <= n^2 + 3n (Proposition 12, p. 188)
    dp_global_max_by_n: dict[str, dict[str, int]] = {}
    for m_check in (4, 8, 16, 32, 64):
        dp_val = dp_max_uncached_calls_two_phase(m_check, 2)
        prop12 = m_check * m_check + 3 * m_check
        assert dp_val == prop12 - 10 and dp_val <= prop12
        dp_global_max_by_n[f"n{m_check}"] = {
            "dp_exact_global_max": dp_val,
            "prop12_worst_case_bound": prop12,
        }

    # 3. Strictly monotone, UNRESOLVED-free alternating required/redundant clauses (|S*| = n/2) -> Theta(n^2):
    #    uncached 2-phase ddmin strictly obeys Proposition 12 (n^2 + 3n), while Fig. 6 query memoization
    #    tightens unique oracle evaluations on monotone predicates to <= (n^2 + 3n - 2)/2 (3.04x reduction at n=64).
    alt_stats: dict[str, dict[str, int]] = {}
    for n_len in (16, 32, 64):
        items = [f"cl_{i}" for i in range(n_len)]
        req_odd = {f"cl_{i}" for i in range(1, n_len, 2)}
        seen_two: set[tuple[str, ...]] = set()
        seen_comp: set[tuple[str, ...]] = set()

        def alt_two(s: Sequence[str], req: set[str] = req_odd, cache: set[tuple[str, ...]] = seen_two) -> str:
            cache.add(tuple(s))
            return FAIL if req.issubset(s) else PASS

        def alt_comp(s: Sequence[str], req: set[str] = req_odd, cache: set[tuple[str, ...]] = seen_comp) -> str:
            cache.add(tuple(s))
            return FAIL if req.issubset(s) else PASS

        r_two, c_two = ddmin_two_phase(alt_two, items)
        r_comp, c_comp = ddmin_complement_only(alt_comp, items)
        prop12_bound = n_len * n_len + 3 * n_len
        dp_max = dp_max_uncached_calls_two_phase(n_len, 2)
        half_bound = (n_len * n_len + 3 * n_len - 2) // 2
        assert set(r_two) == req_odd and is_one_minimal(lambda s, req=req_odd: FAIL if req.issubset(s) else PASS, r_two)
        assert set(r_comp) == req_odd and is_one_minimal(lambda s, req=req_odd: FAIL if req.issubset(s) else PASS, r_comp)
        assert c_two <= dp_max <= prop12_bound
        assert len(seen_two) <= half_bound and c_comp <= half_bound
        alt_stats[f"n{n_len}"] = {
            "prop12_worst_case_bound": prop12_bound,
            "dp_exact_uncached_max": dp_max,
            "monotone_memoized_half_bound": half_bound,
            "two_phase_uncached_calls": c_two,
            "two_phase_memoized_unique_calls": len(seen_two),
            "complement_only_uncached_calls": c_comp,
            "complement_only_memoized_unique_calls": len(seen_comp),
        }

    ratio_two_uncached = alt_stats["n64"]["two_phase_uncached_calls"] / alt_stats["n16"]["two_phase_uncached_calls"]
    ratio_two_memoized = alt_stats["n64"]["two_phase_memoized_unique_calls"] / alt_stats["n16"]["two_phase_memoized_unique_calls"]
    ratio_comp_uncached = alt_stats["n64"]["complement_only_uncached_calls"] / alt_stats["n16"]["complement_only_uncached_calls"]
    memo_speedup_n64 = alt_stats["n64"]["two_phase_uncached_calls"] / alt_stats["n64"]["two_phase_memoized_unique_calls"]
    assert ratio_two_uncached > 10.0 and ratio_two_memoized > 8.0 and ratio_comp_uncached > 10.0
    assert memo_speedup_n64 > 3.0

    # 4. Non-monotone compensatory-clause root-cause deletion:
    # - True root cause in full prompt is `bad_c4` (bad_c4 in s => FAIL).
    # - `pushy_c1` fails alone, but is safely masked whenever `guard_c2` is present.
    def compensatory_prompt_oracle(s: Sequence[str]) -> str:
        ss = set(s)
        if "bad_c4" in ss:
            return FAIL
        if "pushy_c1" in ss and "guard_c2" not in ss:
            return FAIL
        return PASS

    assert compensatory_prompt_oracle(["pushy_c1"]) == FAIL
    assert compensatory_prompt_oracle(["pushy_c1", "guard_c2"]) == PASS  # Monotonicity violation witness

    order_masked_drop = ["guard_c2", "bad_c4", "pushy_c1", "neutral_c3"]
    order_safe_drop = ["pushy_c1", "neutral_c3", "guard_c2", "bad_c4"]

    nm_two_a, _ = ddmin_two_phase(compensatory_prompt_oracle, order_masked_drop)
    nm_comp_a, _ = ddmin_complement_only(compensatory_prompt_oracle, order_masked_drop)
    nm_two_b, _ = ddmin_two_phase(compensatory_prompt_oracle, order_safe_drop)
    nm_comp_b, _ = ddmin_complement_only(compensatory_prompt_oracle, order_safe_drop)

    assert nm_comp_a == ["pushy_c1"] and "bad_c4" not in nm_comp_a and is_one_minimal(compensatory_prompt_oracle, nm_comp_a)
    assert nm_comp_b == ["bad_c4"]
    assert nm_two_b == ["pushy_c1"] and "bad_c4" not in nm_two_b and is_one_minimal(compensatory_prompt_oracle, nm_two_b)
    assert nm_two_a == ["bad_c4"]

    return {
        "single_defect_n64": {
            "two_phase_calls": c2_single,
            "complement_only_calls": cc_single,
            "prop13_upper_bound_2log2n": 12,
        },
        "dp_global_worst_case_two_phase": dp_global_max_by_n,
        "monotone_alternating_theta_n2": {
            "calls_by_n": alt_stats,
            "two_phase_uncached_ratio_n64_over_n16": round(ratio_two_uncached, 2),
            "two_phase_memoized_ratio_n64_over_n16": round(ratio_two_memoized, 2),
            "complement_only_uncached_ratio_n64_over_n16": round(ratio_comp_uncached, 2),
            "two_phase_memoization_reduction_factor_n64": round(memo_speedup_n64, 2),
        },
        "non_monotone_compensatory_deletion": {
            "order_a": order_masked_drop,
            "complement_only_on_order_a": nm_comp_a,
            "two_phase_on_order_a": nm_two_a,
            "order_b": order_safe_drop,
            "complement_only_on_order_b": nm_comp_b,
            "two_phase_on_order_b": nm_two_b,
            "both_variants_can_delete_true_defect_bad_c4": ("bad_c4" not in nm_comp_a) and ("bad_c4" not in nm_two_b),
        },
    }


# =============================================================================
# PROBE 3: ContextCite Uniform-Mask OLS = Banzhaf vs. KernelSHAP vs. LOO
# =============================================================================

def exact_banzhaf_and_shapley(vals: Sequence[float], d: int) -> tuple[list[float], list[float]]:
    facts = [math.factorial(i) for i in range(d + 1)]
    banz = [0.0] * d
    shap = [0.0] * d
    inv_2d1 = 1.0 / (1 << (d - 1))
    fact_d = float(facts[d])
    wt_by_s = [facts[s] * facts[d - s - 1] / fact_d for s in range(d)]
    for j in range(d):
        bit_j = 1 << j
        b_acc = 0.0
        s_acc = 0.0
        for bits in range(1 << d):
            if bits & bit_j:
                continue
            diff = vals[bits | bit_j] - vals[bits]
            b_acc += diff
            s_acc += wt_by_s[bits.bit_count()] * diff
        banz[j] = b_acc * inv_2d1
        shap[j] = s_acc
    return banz, shap


def population_uniform_ols(vals: Sequence[float], d: int) -> list[float]:
    """Exact OLS slope over all 2^d uniform Bernoulli(0.5) masks v in {0, 1}^d."""
    x_rows = [[1.0] + [float((bits >> j) & 1) for j in range(d)] for bits in range(1 << d)]
    xt = mat_transpose(x_rows)
    xtx_inv = mat_inv(mat_mul(xt, x_rows))
    xty = [[sum(xt[r][bits] * vals[bits] for bits in range(1 << d))] for r in range(d + 1)]
    beta = mat_mul(xtx_inv, xty)
    return [beta[j + 1][0] for j in range(d)]


def population_kernelshap_wls(vals: Sequence[float], d: int) -> list[float]:
    """Exact population KernelSHAP constrained WLS over all non-trivial coalitions 0 < |v| < d."""
    f0 = vals[0]
    f1 = vals[(1 << d) - 1]
    gap = f1 - f0
    comb_d = [math.comb(d, s) for s in range(d + 1)]
    a_mat = [[0.0] * (d - 1) for _ in range(d - 1)]
    b_vec = [[0.0] for _ in range(d - 1)]
    for bits in range(1, (1 << d) - 1):
        s = bits.bit_count()
        wt = (d - 1.0) / (comb_d[s] * s * (d - s))
        vd = float((bits >> (d - 1)) & 1)
        z = [float((bits >> j) & 1) - vd for j in range(d - 1)]
        y_adj = vals[bits] - f0 - vd * gap
        for r in range(d - 1):
            zr_w = z[r] * wt
            b_vec[r][0] += zr_w * y_adj
            for c in range(d - 1):
                a_mat[r][c] += zr_w * z[c]
    w_head = [row[0] for row in mat_mul(mat_inv(a_mat), b_vec)]
    w_last = gap - sum(w_head)
    return w_head + [w_last]


def fit_standardized_lasso(
    masks: Sequence[Sequence[int]],
    ys: Sequence[float],
    alpha: float = 0.01,
    num_output_tokens: int = 1,
    max_iter: int = 1000,
    tol: float = 1e-10,
) -> tuple[list[float], float]:
    """Pure-stdlib coordinate-descent LASSO matching MadryLab/context-cite@c11f8ace solver.py:38-54."""
    m = len(masks)
    d = len(masks[0])
    inv_m = 1.0 / m
    means_x = [sum(masks[i][j] for i in range(m)) * inv_m for j in range(d)]
    scales_x = [
        math.sqrt(max(sum((masks[i][j] - means_x[j]) ** 2 for i in range(m)) * inv_m, 1e-12))
        for j in range(d)
    ]
    xz_cols = [[(masks[i][j] - means_x[j]) / scales_x[j] for i in range(m)] for j in range(d)]
    y_scaled = [y / num_output_tokens for y in ys]
    mean_y = sum(y_scaled) * inv_m
    resid = [y - mean_y for y in y_scaled]

    w = [0.0] * d
    for _ in range(max_iter):
        max_delta = 0.0
        for j in range(d):
            col = xz_cols[j]
            wj = w[j]
            rho = sum(col[i] * resid[i] for i in range(m)) * inv_m + wj
            if rho > alpha:
                w_new = rho - alpha
            elif rho < -alpha:
                w_new = rho + alpha
            else:
                w_new = 0.0
            diff = w_new - wj
            if diff != 0.0:
                for i in range(m):
                    resid[i] -= col[i] * diff
                w[j] = w_new
                if abs(diff) > max_delta:
                    max_delta = abs(diff)
        if max_delta < tol:
            break

    weights = [(w[j] / scales_x[j]) * num_output_tokens for j in range(d)]
    bias = (mean_y - sum(means_x[j] * (w[j] / scales_x[j]) for j in range(d))) * num_output_tokens
    return weights, bias


def fit_ridge_surrogate(masks: Sequence[Sequence[int]], ys: Sequence[float], lam: float = 1.0) -> list[float]:
    """Centered ridge-regularized linear surrogate over binary masks."""
    m = len(masks)
    d = len(masks[0])
    mx = [sum(masks[i][j] for i in range(m)) / m for j in range(d)]
    my = sum(ys) / m
    xc = [[masks[i][j] - mx[j] for j in range(d)] for i in range(m)]
    yc = [ys[i] - my for i in range(m)]
    xt = mat_transpose(xc)
    xtx = mat_mul(xt, xc)
    for j in range(d):
        xtx[j][j] += lam
    xty = [[sum(xt[j][i] * yc[i] for i in range(m))] for j in range(d)]
    return [row[0] for row in mat_mul(mat_inv(xtx), xty)]


def run_probe_3() -> dict:
    d = 10
    # Payoff over d = 10 context/prompt blocks:
    # - (0, 1): Disjunctive OR pair (+4.0 * (v0 | v1)) -> Banzhaf = Shapley = +2.0, LOO = 0.0
    # - (2, 3, 4): 3-way conjunctive AND synergy (+4.0 * (v2 & v3 & v4)) -> Banzhaf = +1.0 != Shapley = +4/3
    # - (5, 6): Symmetric XOR parity pair (+2.0 * (v5 ^ v6)) -> Banzhaf = Shapley = 0.0, LOO = -2.0
    # - 7: Additive standalone block (+1.5 * v7) -> Banzhaf = Shapley = LOO = +1.5
    # - (8, 9): Irrelevant distractors (0.0)
    def f_logit(bits: int) -> float:
        v0 = (bits >> 0) & 1
        v1 = (bits >> 1) & 1
        v2 = (bits >> 2) & 1
        v3 = (bits >> 3) & 1
        v4 = (bits >> 4) & 1
        v5 = (bits >> 5) & 1
        v6 = (bits >> 6) & 1
        v7 = (bits >> 7) & 1
        return (
            -3.0
            + 4.0 * float(v0 | v1)
            + 4.0 * float(v2 & v3 & v4)
            + 2.0 * float(v5 ^ v6)
            + 1.5 * float(v7)
        )

    vals = [f_logit(bits) for bits in range(1 << d)]
    banz, shap = exact_banzhaf_and_shapley(vals, d)
    ols_pop = population_uniform_ols(vals, d)
    kshap_pop = population_kernelshap_wls(vals, d)

    max_ols_vs_banzhaf_err = max(abs(ols_pop[j] - banz[j]) for j in range(d))
    assert max_ols_vs_banzhaf_err < 1e-12
    max_kshap_vs_shapley_err = max(abs(kshap_pop[j] - shap[j]) for j in range(d))
    assert max_kshap_vs_shapley_err < 1e-12
    assert math.isclose(banz[2], 1.0, abs_tol=1e-12) and math.isclose(shap[2], 4.0 / 3.0, abs_tol=1e-12)

    full_mask = (1 << d) - 1
    loo = [vals[full_mask] - vals[full_mask ^ (1 << j)] for j in range(d)]
    assert loo[0] == 0.0 and loo[1] == 0.0
    assert math.isclose(banz[0], 2.0, abs_tol=1e-12) and math.isclose(banz[5], 0.0, abs_tol=1e-12)

    # Subsampled M = 64 ContextCite LASSO at BOTH upstream default alpha=0.01 (solver.py:38)
    # and sparser alpha=0.05 (100 seeds), plus fixed-ys num_output_tokens penalty multiplication check.
    rng = random.Random(42)
    n_runs = 100
    m_calls = 64
    mean_lasso_001 = [0.0] * d
    mean_lasso_005 = [0.0] * d
    mean_ridge = [0.0] * d
    or_rescued_001 = 0
    or_rescued_005 = 0
    max_equivariance_err = 0.0
    max_fixed_y_penalty_scaling_err = 0.0

    for run_idx in range(n_runs):
        mask_ints = [rng.randrange(1 << d) for _ in range(m_calls)]
        masks = [[(b >> j) & 1 for j in range(d)] for b in mask_ints]
        ys = [vals[b] for b in mask_ints]
        w_l001, _ = fit_standardized_lasso(masks, ys, alpha=0.01, num_output_tokens=1)
        w_l005, _ = fit_standardized_lasso(masks, ys, alpha=0.05, num_output_tokens=1)
        if run_idx == 0:
            # (a) Linear output-scaling equivariance: scaling ys by L alongside num_output_tokens=L scales w by L
            ys_tok10 = [y * 10.0 for y in ys]
            w_equiv, _ = fit_standardized_lasso(masks, ys_tok10, alpha=0.01, num_output_tokens=10)
            max_equivariance_err = max(abs(w_equiv[j] - 10.0 * w_l001[j]) for j in range(d))
            assert max_equivariance_err < 1e-8
            # (b) Fixed-ys sequence-level penalty multiplication (solver.py:45,54):
            #     on UNCHANGED sequence logit-probabilities ys, setting num_output_tokens=10 with alpha=0.01
            #     is algebraically identical to num_output_tokens=1 with effective penalty alpha = 0.01 * 10 = 0.10!
            w_fixed_y_tok10, _ = fit_standardized_lasso(masks, ys, alpha=0.01, num_output_tokens=10)
            w_alpha_010, _ = fit_standardized_lasso(masks, ys, alpha=0.10, num_output_tokens=1)
            max_fixed_y_penalty_scaling_err = max(abs(w_fixed_y_tok10[j] - w_alpha_010[j]) for j in range(d))
            assert max_fixed_y_penalty_scaling_err < 1e-8

        w_r = fit_ridge_surrogate(masks, ys, lam=1.0)
        for j in range(d):
            mean_lasso_001[j] += w_l001[j] / n_runs
            mean_lasso_005[j] += w_l005[j] / n_runs
            mean_ridge[j] += w_r[j] / n_runs
        noise_001 = max(abs(w_l001[8]), abs(w_l001[9]))
        noise_005 = max(abs(w_l005[8]), abs(w_l005[9]))
        if min(w_l001[0], w_l001[1]) > max(0.5, noise_001):
            or_rescued_001 += 1
        if min(w_l005[0], w_l005[1]) > max(0.5, noise_005):
            or_rescued_005 += 1

    assert or_rescued_001 / n_runs >= 0.90 and or_rescued_005 / n_runs >= 0.90

    return {
        "d_blocks": d,
        "hypercube_coalitions": 1 << d,
        "subsampled_calls_M": m_calls,
        "loo_scores": [round(x, 4) for x in loo],
        "exact_banzhaf": [round(x, 4) for x in banz],
        "population_uniform_ols": [round(x, 4) for x in ols_pop],
        "exact_shapley": [round(x, 4) for x in shap],
        "population_kernelshap_wls": [round(x, 4) for x in kshap_pop],
        "max_abs_err_uniform_ols_vs_banzhaf": round(max_ols_vs_banzhaf_err, 15),
        "max_abs_err_kernelshap_vs_shapley": round(max_kshap_vs_shapley_err, 15),
        "m64_lasso_alpha0_01_default_mean": [round(x, 3) for x in mean_lasso_001],
        "m64_lasso_alpha0_05_mean": [round(x, 3) for x in mean_lasso_005],
        "m64_ridge_mean": [round(x, 3) for x in mean_ridge],
        "m64_or_pair_rescue_rate_alpha0_01": round(or_rescued_001 / n_runs, 4),
        "m64_or_pair_rescue_rate_alpha0_05": round(or_rescued_005 / n_runs, 4),
        "fixed_y_num_output_tokens_penalty_scaling_max_err": round(max_fixed_y_penalty_scaling_err, 12),
    }


# =============================================================================
# PROBE 4: Anytime-Valid Sequential Stopping, WorFBench Evaluator Audit, & FSM
# =============================================================================

def normal_msprt_lambda(sum_z: float, n: int, sigma2: float = 1.0, tau2: float = 0.25) -> float:
    """Johari et al. (2017; 2022 Eq. 6) Gaussian mixture SPRT likelihood ratio."""
    denom = sigma2 + n * tau2
    exponent = (tau2 * sum_z * sum_z) / (2.0 * sigma2 * denom)
    return math.sqrt(sigma2 / denom) * math.exp(min(exponent, 500.0))


def beta_binomial_mcnemar_evalue(wins: int, n_discordant: int, a: float = 2.0) -> float:
    """Exact finite-sample paired-McNemar martingale under H0: p = 0.5 with Beta(a, a) mixture."""
    if n_discordant == 0:
        return 1.0
    log_num = (
        math.lgamma(a + wins)
        + math.lgamma(a + n_discordant - wins)
        - math.lgamma(2.0 * a + n_discordant)
    )
    log_den = 2.0 * math.lgamma(a) - math.lgamma(2.0 * a)
    return math.exp(n_discordant * math.log(2.0) + log_num - log_den)


def exact_betabinomial_stopping_dp(
    p_true: float, n_max: int, alpha: float = 0.05, a: float = 2.0
) -> tuple[float, float]:
    """Exact forward dynamic programming for stopping probability and expected stopping time
    of the Beta-Binomial McNemar e-process M_m(a) >= 1/alpha over m = 1..n_max.
    """
    thresh = 1.0 / alpha
    dist = [1.0]
    stopped_prob = 0.0
    expected_stop = 0.0
    q_true = 1.0 - p_true
    for m in range(1, n_max + 1):
        nxt = [0.0] * (m + 1)
        for w, mass in enumerate(dist):
            if mass == 0.0:
                continue
            nxt[w] += mass * q_true
            nxt[w + 1] += mass * p_true
        for w in range(m + 1):
            if nxt[w] > 0.0 and beta_binomial_mcnemar_evalue(w, m, a=a) >= thresh:
                stopped_prob += nxt[w]
                expected_stop += m * nxt[w]
                nxt[w] = 0.0
        dist = nxt
    surviving = sum(dist)
    expected_stop += n_max * surviving
    return stopped_prob, expected_stop


def exact_fixed_binomial_mcnemar_power(m: int, p_alt: float, alpha: float = 0.05) -> tuple[int, float, float]:
    """Exact two-sided Binomial(m, 0.5) McNemar critical threshold k_crit ({W <= k_crit or W >= m - k_crit}),
    exact null Type-I size <= alpha, and exact alternative power at p_alt.
    """
    def pmf(w: int, p: float) -> float:
        return math.comb(m, w) * (p ** w) * ((1.0 - p) ** (m - w))

    best_k = -1
    null_size = 0.0
    for k in range(m // 2 + 1):
        sz = sum(pmf(w, 0.5) for w in range(m + 1) if w <= k or w >= m - k)
        if sz <= alpha:
            best_k = k
            null_size = sz
        else:
            break
    assert best_k >= 0
    power = sum(pmf(w, p_alt) for w in range(m + 1) if w <= best_k or w >= m - best_k)
    return best_k, null_size, power


def run_worfbench_evaluator_audit() -> dict:
    """Exact stdlib reproduction of all three defects in zjunlp/WorfBench@38a64555
    (evaluator/graph_evaluator.py + node_eval.py:workflow_to_graph_list) and their
    sentinel-bridge-preserving repairs (verified on parallel fan-out/fan-in DAGs).
    """

    def wrap_sentinels(nodes: Sequence[str], edges_1based: Sequence[tuple[int | str, int | str]]) -> dict:
        # Exact port of node_eval.py:42-69
        full_nodes = ["START"] + list(nodes) + ["END"]
        end_idx = len(full_nodes) - 1
        parsed_edges = []
        for u, v in edges_1based:
            ui = 0 if u == "START" else int(u)
            vi = end_idx if v == "END" else int(v)
            parsed_edges.append((ui, vi))
        return {"nodes": full_nodes, "edges": parsed_edges}

    def all_topo_sorts_buggy(graph: dict) -> list[list[str]]:
        # Exact port of graph_evaluator.py:16-43
        nodes = graph["nodes"]
        if len(nodes) >= 10:
            return [nodes]  # BUG 1a + 1b: aborts DAG sort AND forgets to strip START/END!
        n = len(nodes)
        adj = {i: [] for i in range(n)}
        indeg = {i: 0 for i in range(n)}
        for u, v in graph["edges"]:
            adj[u].append(v)
            indeg[v] += 1
        sorts: list[list[str]] = []

        def backtrack(chosen: list[int], cur_indeg: dict[int, int]) -> None:
            if len(sorts) >= 20:
                return
            if len(chosen) == n:
                sorts.append([nodes[i] for i in chosen if nodes[i] not in ("START", "END")])
                return
            for v in range(n):
                if cur_indeg[v] == 0 and v not in chosen:
                    for nxt in adj[v]:
                        cur_indeg[nxt] -= 1
                    chosen.append(v)
                    backtrack(chosen, cur_indeg)
                    chosen.pop()
                    for nxt in adj[v]:
                        cur_indeg[nxt] += 1

        backtrack([], indeg)
        return sorts[:20]

    def match_exact_labels(pred_nodes: Sequence[str], gt_nodes: Sequence[str]) -> dict[int, int]:
        used_gt: set[int] = set()
        mapping: dict[int, int] = {}
        for i, pn in enumerate(pred_nodes):
            mapping[i] = -1
            for j, gn in enumerate(gt_nodes):
                if j not in used_gt and pn == gn:
                    mapping[i] = j
                    used_gt.add(j)
                    break
        return mapping

    def largest_cc(nodes: Sequence[int], edges: Sequence[tuple[int, int]]) -> int:
        # Exact port of graph_evaluator.py:46-54 (undirected nx.Graph semantics)
        adj: dict[int, set[int]] = {u: set() for u in nodes}
        for u, v in edges:
            adj.setdefault(u, set()).add(v)
            adj.setdefault(v, set()).add(u)
        seen: set[int] = set()
        best = 0
        for u in adj:
            if u in seen:
                continue
            stack = [u]
            seen.add(u)
            comp = 0
            while stack:
                cur = stack.pop()
                comp += 1
                for nxt in adj[cur]:
                    if nxt not in seen:
                        seen.add(nxt)
                        stack.append(nxt)
            best = max(best, comp)
        return best

    def largest_interior_cc(
        nodes: Sequence[int], edges: Sequence[tuple[int, int]], node_labels: Sequence[str]
    ) -> int:
        """Connected-component count over sentinel-bridged common subgraph counting ONLY
        non-sentinel interior nodes in each component (preserving parallel START->branch_i->END DAGs).
        """
        adj: dict[int, set[int]] = {u: set() for u in nodes}
        for u, v in edges:
            adj.setdefault(u, set()).add(v)
            adj.setdefault(v, set()).add(u)
        seen: set[int] = set()
        best_interior = 0
        for u in adj:
            if u in seen:
                continue
            stack = [u]
            seen.add(u)
            comp_interior = 0
            while stack:
                cur = stack.pop()
                if node_labels[cur] not in ("START", "END"):
                    comp_interior += 1
                for nxt in adj[cur]:
                    if nxt not in seen:
                        seen.add(nxt)
                        stack.append(nxt)
            best_interior = max(best_interior, comp_interior)
        return best_interior

    def t_eval_graph_impl(pred_graph: dict, gt_graph: dict, *, translate_edges: bool) -> dict[str, float]:
        pred_nodes = pred_graph["nodes"]
        gt_nodes = gt_graph["nodes"]
        mapping = match_exact_labels(pred_nodes, gt_nodes)
        matched_pred = [k for k, v in mapping.items() if v != -1]
        matched_gt = [v for v in mapping.values() if v != -1]
        matched_gt_edges = {
            (u, v) for u, v in gt_graph["edges"] if u in matched_gt and v in matched_gt
        }
        if not translate_edges:
            # Exact buggy graph_evaluator.py:114-135
            matched_pred_edges = [
                (u, v) for u, v in pred_graph["edges"] if u in matched_pred and v in matched_pred
            ]
            public_edges = [e for e in matched_pred_edges if e in matched_gt_edges]
            pred_cc = largest_cc(matched_pred, public_edges)
            gt_cc = largest_cc(matched_gt, public_edges)
            p = pred_cc / len(pred_nodes)
            r = gt_cc / len(gt_nodes)
            return {"precision": p, "recall": r, "f1_score": 2 * p * r / (p + r)}

        # Repaired: return 0.0 when 0 interior nodes match; otherwise keep START/END as
        # connectivity bridges in public_gt_edges and count only non-sentinel interior nodes.
        interior_pred = [k for k in matched_pred if pred_nodes[k] not in ("START", "END")]
        if not interior_pred:
            return {"precision": 0.0, "recall": 0.0, "f1_score": 0.0}
        matched_pred_set = set(matched_pred)
        public_gt_edges = [
            (mapping[u], mapping[v])
            for u, v in pred_graph["edges"]
            if u in matched_pred_set and v in matched_pred_set and (mapping[u], mapping[v]) in matched_gt_edges
        ]
        gt_cc = largest_interior_cc(matched_gt, public_gt_edges, gt_nodes)
        pred_cc = gt_cc
        p = pred_cc / max(1, len(pred_nodes) - 2)
        r = gt_cc / max(1, len(gt_nodes) - 2)
        return {"precision": p, "recall": r, "f1_score": (2 * p * r / (p + r)) if (p + r) else 0.0}

    def t_eval_plan_order(pred_plan: Sequence[str], gt_plan: Sequence[str], *, buggy_ones_init: bool) -> dict[str, float]:
        mapping = match_exact_labels(pred_plan, gt_plan)
        len_pred, len_gt = len(pred_plan), len(gt_plan)
        if buggy_ones_init:
            # Exact buggy graph_evaluator.py:178-189
            dp = [1] * len_pred
            for i in range(len_pred):
                for j in range(i):
                    if mapping[i] == -1 or mapping[j] == -1:
                        continue
                    if mapping[i] > mapping[j]:
                        dp[i] = max(dp[i], dp[j] + 1)
            correct = max(dp)
        else:
            dp = [0 if mapping[i] == -1 else 1 for i in range(len_pred)]
            for i in range(len_pred):
                if mapping[i] == -1:
                    continue
                for j in range(i):
                    if mapping[j] != -1 and mapping[i] > mapping[j]:
                        dp[i] = max(dp[i], dp[j] + 1)
            correct = max(dp, default=0)
        if correct == 0:
            return {"precision": 0.0, "recall": 0.0, "f1_score": 0.0}
        prec = correct / len_pred
        rec = correct / len_gt
        return {"precision": prec, "recall": rec, "f1_score": 2 * prec * rec / (prec + rec)}

    # Witness 1: 8-step gold workflow (len(nodes) == 10 with START/END) scored against ITSELF!
    steps8 = [f"action_{i}" for i in range(1, 9)]
    edges8 = [("START", 1)] + [(i, i + 1) for i in range(1, 8)] + [(8, "END")]
    gt8 = wrap_sentinels(steps8, edges8)
    gold_trajs_buggy = all_topo_sorts_buggy(gt8)
    pred8_stripped = [n for n in gt8["nodes"] if n not in ("START", "END")]
    self_score_buggy = t_eval_plan_order(pred8_stripped, gold_trajs_buggy[0], buggy_ones_init=True)
    assert math.isclose(self_score_buggy["recall"], 0.8) and math.isclose(self_score_buggy["f1_score"], 8.0 / 9.0)

    # Witness 2a: 100% isomorphic asymmetric fork DAG (listing branch_b before branch_a -> sub_a)
    gt_fork = wrap_sentinels(
        ["prep", "branch_a", "sub_a", "branch_b"],
        [("START", 1), (1, 2), (2, 3), (1, 4), (3, "END"), (4, "END")],
    )
    pred_iso_fork = wrap_sentinels(
        ["prep", "branch_b", "branch_a", "sub_a"],
        [("START", 1), (1, 2), (1, 3), (3, 4), (2, "END"), (4, "END")],
    )
    score_iso_buggy = t_eval_graph_impl(pred_iso_fork, gt_fork, translate_edges=False)
    score_iso_fixed = t_eval_graph_impl(pred_iso_fork, gt_fork, translate_edges=True)
    assert math.isclose(score_iso_buggy["f1_score"], 0.5) and math.isclose(score_iso_fixed["f1_score"], 1.0)

    # Witness 2b: Parallel fan-out/fan-in fork-join DAGs (toolbench 2-branch & seal_tools 3-branch):
    # START and END serve as the sole connectivity bridges across independent parallel branches!
    gt_parallel_2 = wrap_sentinels(
        ["branch_a", "branch_b"],
        [("START", 1), ("START", 2), (1, "END"), (2, "END")],
    )
    gt_parallel_3 = wrap_sentinels(
        ["tool_a", "tool_b", "tool_c"],
        [("START", 1), ("START", 2), ("START", 3), (1, "END"), (2, "END"), (3, "END")],
    )
    pred_parallel_3_reordered = wrap_sentinels(
        ["tool_c", "tool_a", "tool_b"],
        [("START", 1), ("START", 2), ("START", 3), (1, "END"), (2, "END"), (3, "END")],
    )
    par2_self_fixed = t_eval_graph_impl(gt_parallel_2, gt_parallel_2, translate_edges=True)
    par3_self_fixed = t_eval_graph_impl(gt_parallel_3, gt_parallel_3, translate_edges=True)
    par3_reord_fixed = t_eval_graph_impl(pred_parallel_3_reordered, gt_parallel_3, translate_edges=True)
    assert math.isclose(par2_self_fixed["f1_score"], 1.0)
    assert math.isclose(par3_self_fixed["f1_score"], 1.0)
    assert math.isclose(par3_reord_fixed["f1_score"], 1.0)

    # Witness 2c: Prefix-shifted diamond DAG (+4 extra setup steps):
    gt_diamond = wrap_sentinels(
        ["prep", "branch_left", "branch_right", "merge"],
        [("START", 1), (1, 2), (1, 3), (2, 4), (3, 4), (4, "END")],
    )
    pred_shifted = wrap_sentinels(
        ["s1", "s2", "s3", "s4", "prep", "branch_left", "branch_right", "merge"],
        [("START", 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 6), (5, 7), (6, 8), (7, 8), (8, "END")],
    )
    score_shift_buggy = t_eval_graph_impl(pred_shifted, gt_diamond, translate_edges=False)
    score_shift_fixed = t_eval_graph_impl(pred_shifted, gt_diamond, translate_edges=True)
    assert math.isclose(score_shift_buggy["recall"], 1.0 / 6.0)
    assert math.isclose(score_shift_fixed["recall"], 1.0) and math.isclose(score_shift_fixed["precision"], 0.5)

    # Witness 3: Completely wrong 3-step workflow (0 interior matches) + empty prediction check
    pred_wrong = wrap_sentinels(["unrelated_x", "unrelated_y", "unrelated_z"], [("START", 1), (1, 2), (2, 3), (3, "END")])
    zero_plan_buggy = t_eval_plan_order(["unrelated_x", "unrelated_y", "unrelated_z"], steps8[:4], buggy_ones_init=True)
    zero_plan_fixed = t_eval_plan_order(["unrelated_x", "unrelated_y", "unrelated_z"], steps8[:4], buggy_ones_init=False)
    empty_plan_fixed = t_eval_plan_order([], steps8[:4], buggy_ones_init=False)
    zero_graph_buggy = t_eval_graph_impl(pred_wrong, gt_diamond, translate_edges=False)
    zero_graph_fixed = t_eval_graph_impl(pred_wrong, gt_diamond, translate_edges=True)
    assert math.isclose(zero_plan_buggy["f1_score"], 2.0 / 7.0) and zero_plan_fixed["f1_score"] == 0.0
    assert empty_plan_fixed["f1_score"] == 0.0
    assert zero_graph_buggy["f1_score"] > 0.15 and zero_graph_fixed["f1_score"] == 0.0

    return {
        "bug1_8step_self_eval_f1_buggy": round(self_score_buggy["f1_score"], 4),
        "bug1_8step_self_eval_recall_buggy": round(self_score_buggy["recall"], 4),
        "bug2_isomorphic_fork_f1_buggy": round(score_iso_buggy["f1_score"], 4),
        "bug2_isomorphic_fork_f1_fixed": round(score_iso_fixed["f1_score"], 4),
        "bug2_parallel_2branch_self_f1_fixed": round(par2_self_fixed["f1_score"], 4),
        "bug2_parallel_3branch_self_f1_fixed": round(par3_self_fixed["f1_score"], 4),
        "bug2_parallel_3branch_reordered_f1_fixed": round(par3_reord_fixed["f1_score"], 4),
        "bug2_shifted_isomorphic_dag_f1_buggy": round(score_shift_buggy["f1_score"], 4),
        "bug2_shifted_isomorphic_dag_f1_fixed": round(score_shift_fixed["f1_score"], 4),
        "bug2_zero_match_graph_f1_buggy": round(zero_graph_buggy["f1_score"], 4),
        "bug2_zero_match_graph_f1_fixed": zero_graph_fixed["f1_score"],
        "bug3_zero_match_plan_f1_buggy": round(zero_plan_buggy["f1_score"], 4),
        "bug3_zero_match_plan_f1_fixed": zero_plan_fixed["f1_score"],
    }


def exact_resumption_markov_dp(b_items: int, r_max: int, q_exit: float) -> tuple[float, float, float]:
    """Exact 2D absorbing Markov chain over (decided_items in 0..b_items, resumptions_used in 0..r_max)
    when external harness auto-resumes premature turn terminations up to r_max times.
    Returns (expected_decided, expected_stop_attempts, budget_exhausted_prob).
    """
    dp = [0.0] * (r_max + 1)
    dp[0] = 1.0
    exp_decided = 0.0
    exp_stops = 0.0
    exhausted_prob = 0.0
    p_dec = 1.0 - q_exit
    for d in range(b_items):
        for r in range(r_max):
            if dp[r] > 0.0:
                stay = dp[r] * q_exit
                exp_stops += stay
                dp[r + 1] += stay
        if dp[r_max] > 0.0:
            fail = dp[r_max] * q_exit
            exp_stops += fail
            exp_decided += d * fail
            exhausted_prob += fail
        dp = [mass * p_dec for mass in dp]
    exp_decided += b_items * sum(dp)
    return exp_decided, exp_stops, exhausted_prob


def run_fsm_gates_vs_stop_markov_model() -> dict:
    """Derived analytical absorbing-Markov toy model for a B = 200-item unattended batch
    under an external harness resumption cap R_max = 50 across the 2x2 enforcement lattice
    (Gates in {off, on} x Stop in {off, on}) plus per-item instance-token binding.
    """
    b_items = 200
    r_max = 50
    q_exit_ungated = 0.035
    q_exit_gated = 0.25
    q_ctx_overflow = 0.0033
    p_interleave_ungated = 0.62
    p_blind_trapped = 0.74
    p_batch_escape = 0.32

    # 1. Remind-loop (Gates=off, Stop=off, R_max=50): low exit hazard (~7.25 stops <= 50) ->
    #    decides ~200.0 items with 0 blind fabrications, but loses FC via unguarded interleaving!
    dec_remind, stops_remind, exh_remind = exact_resumption_markov_dp(b_items, r_max, q_exit_ungated)
    blind_remind = 0.0
    fc_remind = dec_remind * (1.0 - p_interleave_ungated)

    # 2. Stop-only (Gates=off, Stop=on): terminal exit blocked without state guards ->
    #    unguarded loop bloat incurs context-overflow truncation (~146.6 decided) AND Goodhart blind completion!
    dec_stop_only = sum((1.0 - q_ctx_overflow) ** t for t in range(b_items))
    blind_stop_only = dec_stop_only * p_blind_trapped
    fc_stop_only = dec_stop_only * (1.0 - p_blind_trapped) * (1.0 - p_interleave_ungated)

    # 3. Gates-only (Gates=on, Stop=off, R_max=50): state guards eliminate blind decisions (0.0),
    #    but guard-rejection friction elevates turn-exit hazard, exhausting R_max=50 (~152.6 decided).
    dec_gates_only, stops_gates_only, exh_gates_only = exact_resumption_markov_dp(b_items, r_max, q_exit_gated)
    blind_gates_only = 0.0
    fc_gates_only = dec_gates_only * (1.0 - p_batch_escape)

    # 4a. Unbound FSM (Gates=on, Stop=on, state s2 not bound to single-item token):
    #     0 premature exits, 0 blind decisions, 200.0 decided, residual multi-item batching inside s2.
    dec_fsm_unbound = float(b_items)
    fc_fsm_unbound = dec_fsm_unbound * (1.0 - p_batch_escape)

    # 4b. Instance-token-bound FSM (Gates=on, Stop=on, per-item witness token in s1 -> s2):
    dec_fsm_bound = float(b_items)
    fc_fsm_bound = float(b_items)

    assert dec_remind > 199.9 and exh_remind < 1e-6
    assert dec_stop_only < dec_remind and blind_stop_only > 100.0
    assert dec_gates_only < 160.0 and exh_gates_only > 0.90
    assert fc_stop_only < fc_remind < fc_gates_only < fc_fsm_unbound < fc_fsm_bound

    return {
        "epistemic_role": "derived_analytical_markov_toy_model",
        "batch_size": b_items,
        "harness_resumption_cap_r_max": r_max,
        "remind_loop": {
            "expected_decided": round(dec_remind, 2),
            "expected_stop_attempts": round(stops_remind, 2),
            "resumption_budget_exhausted_prob": round(exh_remind, 4),
            "expected_blind_decisions": blind_remind,
            "expected_full_compliance": round(fc_remind, 2),
        },
        "stop_only": {
            "expected_decided": round(dec_stop_only, 2),
            "expected_blind_decisions": round(blind_stop_only, 2),
            "expected_full_compliance": round(fc_stop_only, 2),
        },
        "gates_only": {
            "expected_decided": round(dec_gates_only, 2),
            "expected_stop_attempts": round(stops_gates_only, 2),
            "resumption_budget_exhausted_prob": round(exh_gates_only, 4),
            "expected_blind_decisions": blind_gates_only,
            "expected_full_compliance": round(fc_gates_only, 2),
        },
        "fsm_unbound_s2": {
            "expected_decided": round(dec_fsm_unbound, 2),
            "expected_blind_decisions": 0.0,
            "expected_full_compliance": round(fc_fsm_unbound, 2),
            "residual_batch_escape_items": round(dec_fsm_unbound - fc_fsm_unbound, 2),
        },
        "fsm_instance_bound": {
            "expected_decided": round(dec_fsm_bound, 2),
            "expected_blind_decisions": 0.0,
            "expected_full_compliance": round(fc_fsm_bound, 2),
        },
    }


def run_probe_4() -> dict:
    alpha = 0.05
    thresh = 1.0 / alpha  # Ville's inequality threshold = 20.0
    n_max = 200
    sigma2 = 1.0
    tau2 = 0.25  # Held strictly identical across H0 and H1!
    z_crit_sq = 1.959963984540054 ** 2

    # 1. Exact analytical DP for finite-sample Beta-Binomial McNemar e-process vs. power-matched fixed Binomial
    exact_bb_null_fpr, _ = exact_betabinomial_stopping_dp(0.5, n_max=n_max, alpha=alpha, a=2.0)
    exact_bb_reg_power, exact_bb_reg_stop = exact_betabinomial_stopping_dp(0.20, n_max=50, alpha=alpha, a=2.0)
    m_fixed_matched = 35
    k_crit_35, null_size_35, fixed_power_35 = exact_fixed_binomial_mcnemar_power(m_fixed_matched, 0.20, alpha=alpha)
    _, _, fixed_power_50 = exact_fixed_binomial_mcnemar_power(50, 0.20, alpha=alpha)

    exact_bb_power_matched_savings_pct = 100.0 * (1.0 - exact_bb_reg_stop / m_fixed_matched)
    exact_bb_cap50_savings_pct = 100.0 * (1.0 - exact_bb_reg_stop / 50.0)
    assert exact_bb_null_fpr <= alpha and null_size_35 <= alpha
    assert abs(fixed_power_35 - exact_bb_reg_power) < 0.01  # Power-matched (~96.56% vs. ~96.17%)
    assert 33.0 <= exact_bb_power_matched_savings_pct <= 34.5

    # 2. Precomputed-threshold Monte Carlo for continuous Gaussian z-peeking vs. Johari mSPRT (fixed tau2 = 0.25)
    z2_naive = [0.0] + [n * sigma2 * z_crit_sq for n in range(1, n_max + 1)]
    s2_msprt = [0.0] + [
        (2.0 * sigma2 * (sigma2 + n * tau2) / tau2)
        * math.log(thresh * math.sqrt((sigma2 + n * tau2) / sigma2))
        for n in range(1, n_max + 1)
    ]
    for n_chk in (1, 10, 50, 142, 200):
        s_hi = math.sqrt(s2_msprt[n_chk]) + 1e-6
        s_lo = math.sqrt(s2_msprt[n_chk]) - 1e-6
        assert normal_msprt_lambda(s_hi, n_chk, sigma2, tau2) >= thresh
        assert normal_msprt_lambda(s_lo, n_chk, sigma2, tau2) < thresh

    rng = random.Random(202611)
    gauss = rng.gauss
    mc_trials = 5000
    fp_naive = 0
    fp_msprt_200 = 0
    fp_msprt_142 = 0
    for _ in range(mc_trials):
        sz = 0.0
        hit_naive = False
        hit_msprt_200 = False
        hit_msprt_142 = False
        for n in range(1, n_max + 1):
            sz += gauss(0.0, 1.0)
            sz2 = sz * sz
            if not hit_naive and n >= 5 and sz2 >= z2_naive[n]:
                hit_naive = True
            if not hit_msprt_200 and sz2 >= s2_msprt[n]:
                hit_msprt_200 = True
                if n <= 142:
                    hit_msprt_142 = True
            if hit_naive and hit_msprt_200:
                break
        fp_naive += int(hit_naive)
        fp_msprt_200 += int(hit_msprt_200)
        fp_msprt_142 += int(hit_msprt_142)

    fpr_naive = fp_naive / mc_trials
    fpr_msprt_200 = fp_msprt_200 / mc_trials
    fpr_msprt_142 = fp_msprt_142 / mc_trials
    assert fpr_naive > 0.33 and fpr_msprt_200 <= alpha and fpr_msprt_142 <= alpha

    # Power-matched Gaussian regression stopping (delta = -0.35 SD, fixed N_90% = 86,
    # identical tau2 = 0.25, extended horizon N_max_alt = 142 matching >= 90% detection power!)
    n_fixed_gauss = math.ceil(((1.959963984540054 + 1.2815515655446004) / 0.35) ** 2)  # 86
    n_max_gauss_alt = 142
    rng_alt = random.Random(202611)
    gauss_alt = rng_alt.gauss
    gauss_trials = 10000
    gauss_detected = 0
    gauss_stop_sum = 0
    for _ in range(gauss_trials):
        sz = 0.0
        stopped = n_max_gauss_alt
        for n in range(1, n_max_gauss_alt + 1):
            sz += gauss_alt(-0.35, 1.0)
            if sz * sz >= s2_msprt[n]:
                stopped = n
                gauss_detected += 1
                break
        gauss_stop_sum += stopped

    gauss_power = gauss_detected / gauss_trials
    gauss_mean_stop = gauss_stop_sum / gauss_trials
    gauss_savings_pct = 100.0 * (1.0 - gauss_mean_stop / n_fixed_gauss)
    assert gauss_power >= 0.90 and 18.5 <= gauss_savings_pct <= 20.0

    return {
        "sequential_testing": {
            "nominal_alpha": alpha,
            "tau2_shared_h0_and_h1": tau2,
            "horizon_n_max_null": n_max,
            "naive_z_peeking_fpr_n5_to_200": round(fpr_naive, 4),
            "johari_normal_msprt_fpr_n200": round(fpr_msprt_200, 4),
            "johari_normal_msprt_fpr_n142": round(fpr_msprt_142, 4),
            "exact_dp_betabinomial_mcnemar_null_fpr_n200": round(exact_bb_null_fpr, 6),
            "exact_dp_discordant_regression_p0_20": {
                "sequential_cap_n_max": 50,
                "sequential_detection_rate": round(exact_bb_reg_power, 4),
                "sequential_expected_stop_n": round(exact_bb_reg_stop, 2),
                "power_matched_fixed_m": m_fixed_matched,
                "power_matched_fixed_k_crit": k_crit_35,
                "power_matched_fixed_null_size": round(null_size_35, 5),
                "power_matched_fixed_power": round(fixed_power_35, 4),
                "power_matched_sample_savings_pct": round(exact_bb_power_matched_savings_pct, 2),
                "fixed_m50_power": round(fixed_power_50, 4),
                "savings_vs_n_max_50_cap_pct": round(exact_bb_cap50_savings_pct, 2),
            },
            "gaussian_regression_delta_neg0_35": {
                "n_fixed_90pct_power": n_fixed_gauss,
                "sequential_horizon_n_max": n_max_gauss_alt,
                "msprt_mean_stop_n": round(gauss_mean_stop, 2),
                "msprt_detection_rate": round(gauss_power, 4),
                "power_matched_sample_savings_pct": round(gauss_savings_pct, 2),
            },
        },
        "worfbench_evaluator_audit": run_worfbench_evaluator_audit(),
        "fsm_gates_vs_stop_markov": run_fsm_gates_vs_stop_markov_model(),
    }


def normalize_neg_zero(obj: object) -> object:
    if isinstance(obj, float):
        return 0.0 if obj == 0.0 else obj
    if isinstance(obj, dict):
        return {k: normalize_neg_zero(v) for k, v in obj.items()}
    if isinstance(obj, list):
        return [normalize_neg_zero(v) for v in obj]
    return obj


def main() -> None:
    report = normalize_neg_zero({
        "probe_1_plackett_burman_foldover": run_probe_1(),
        "probe_2_ddmin_minimality_and_non_monotonicity": run_probe_2(),
        "probe_3_contextcite_banzhaf_vs_kernelshap": run_probe_3(),
        "probe_4_msprt_worfbench_and_fsm_control": run_probe_4(),
    })
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
