#!/usr/bin/env python3
"""Deterministic verification probes for agent debugging, fault localization, bisection, and repair.

Requires Python 3.10+ (standard library only). Covers four mechanisms:

  1. Probe 1 ([exact analytical / derived calculation] + [exact reproduction of pinned algorithm]):
     Intra-chain Spectrum-Based Fault Localization (SBFL) tie degeneracy across all five
     AutoCodeRover formulas (Ochiai, DStar, Tarantula, Op2, Barinel; sbfl.py:L146-185) +
     Fonte rank-max voting (Fonte.py:L4-10) + exact 3-stratum static-FL anchoring law
     verified against Shi, Yang, & Chen (2026, arXiv:2610.25826v1) empirical strata
     (reporting both pooled RR=1 vs. RR<1 break-even 91.66% and binary-miss 93.48%), with
     non-circular negative controls on intermediate unit-test chain-breaking, procedural
     Agentless-1.5 + OrcaLoca (r_0 = 0 baseline on unretrieved functions), and clue-stripped
     LR-issues.

  2. Probe 2 ([exact analytical + seeded Monte Carlo]):
     DGP-matched comparison of flaky-test hard-cut git bisect survival collapse vs.
     strictly compute-matched k-repeat per-pivot majority-vote git bisect vs.
     Burnashev-Zigangirov / FACF Bayesian posterior median bisection under Uniform,
     rank-perturbed noisy Fonte, and exact-DGP Fonte (11%-candidate depth-decayed) priors
     at identical total test-execution budgets (B=21), with full-prior noiseless step
     accounting (exact 3.74 steps across full prior vs. 3.00 top-1 and 7.00 full history)
     and off-support Laplace recovery negative controls.

  3. Probe 3 ([exact reproduction of pinned LDB head/tail slicing + executed bisection loop model]):
     Runtime inspection granularity across N-iteration loops: untruncated raw dynamic line
     tracing vs. pinned LDB repo line-level head-15/tail-15 slicing (py_generate.py:L208-221,
     plus paper App. E head-25/tail-25 check) vs. LDB head-5/tail-5 CFG basic-block slicing vs.
     unconditional inline pdb vs. equal-capability executed ceil(log2 N) conditional-breakpoint
     bisection in inline pdb vs. an isolated edit-free Debug Subagent (Garg & Huang 2026,
     arXiv:2602.18571v2), plus exact verification of Magnuson, Kitanidis, & Lee (2026,
     arXiv:2611.08666v1 Eq. 2-5) unbiased cross-agent pass_X@2.

  4. Probe 4 ([exact execution reproduction + inspect.getsource AST guard check]):
     In-memory execution of four canonical symptom-patch traps (sympy-22714 guard
     weakening, ChatDBG strncpy-style silent boundary truncation, San2Patch CVE-2017-6965
     PoC-constant overfitting, and django-13279 untouched-caller compatibility regression)
     passing narrow PR reproducer tests 4/4 while failing zero-P_o full-repo + metamorphic
     specification postconditions 0/4 vs. root-cause and refactored fixes 4/4.

Fixed PRNG seed: 20261121. Zero third-party dependencies. Zero network calls.
Zero wall-clock timestamps in stdout (bit-identical SHA-256 across runs).
"""

from __future__ import annotations

import ast
import bisect
from dataclasses import dataclass
import hashlib
import inspect
import itertools
import math
import random
import textwrap
import time
from typing import Callable

SEED = 20261121


# =============================================================================
# PROBE 1: Intra-Chain SBFL Tie Degeneracy & 3-Stratum Static-FL Anchoring Law
# =============================================================================


class PinnedAutoCodeRoverSBFL:
    """Exact reproduction of AutoCodeRoverSG/auto-code-rover@585d3e63 app/analysis/sbfl.py:L146-185.

    Notation matching SBFL spectrum counts (e_f, e_p, n_f, n_p):
      - failed     = e_f (failing tests that execute element e)
      - passed     = e_p (passing tests that execute element e)
      - total_fail = F_tot = e_f + n_f, where n_f = F_tot - e_f is non-executing failing tests
      - total_pass = P_tot = e_p + n_p, where n_p = P_tot - e_p is non-executing passing tests
    """

    @staticmethod
    def ochiai(failed: int, passed: int, total_fail: int, total_pass: int) -> float:
        _ = total_pass
        bottom = math.sqrt(total_fail * (failed + passed))
        return 0.0 if bottom == 0 else failed / bottom

    @staticmethod
    def tarantula(failed: int, passed: int, total_fail: int, total_pass: int) -> float:
        if total_fail == 0 or total_pass == 0:
            return 0.0
        top = failed / total_fail
        bottom = top + (passed / total_pass)
        return 0.0 if bottom == 0 else top / bottom

    @staticmethod
    def op2(failed: int, passed: int, total_fail: int, total_pass: int) -> float:
        _ = total_fail
        bottom = total_pass + 1
        return float(failed) if bottom == 0 else failed - (passed / bottom)

    @staticmethod
    def barinel(failed: int, passed: int, total_fail: int, total_pass: int) -> float:
        _ = total_fail
        bottom = passed + failed
        return 0.0 if bottom == 0 else 1.0 - (passed / bottom)

    @staticmethod
    def dstar(failed: int, passed: int, total_fail: int, total_pass: int) -> float:
        _ = total_pass
        # Denominator is e_p + n_f = passed + (total_fail - failed)
        bottom = passed + (total_fail - failed)
        return 0.0 if bottom == 0 else (failed**2) / bottom


SBFL_FORMULAS: dict[str, Callable[[int, int, int, int], float]] = {
    "Ochiai": PinnedAutoCodeRoverSBFL.ochiai,
    "DStar2": PinnedAutoCodeRoverSBFL.dstar,
    "Tarantula": PinnedAutoCodeRoverSBFL.tarantula,
    "Op2": PinnedAutoCodeRoverSBFL.op2,
    "Barinel": PinnedAutoCodeRoverSBFL.barinel,
}


def sbfl_evaluate_chain(
    chain_len: int,
    culprit_idx: int,
    entry_fail_tests: int,
    entry_pass_tests: int,
    nonexec_fail_tests: int,
    nonexec_pass_tests: int,
    isolated_callee_pass_tests: int = 0,
    module_import_pass_tests: int = 0,
) -> dict[str, tuple[float, float, int, float]]:
    """Compute SBFL scores, max spread, Fonte max-tiebreak rank, and random-tie Acc@1.

    Nodes are f_0 -> f_1 -> ... -> f_{m-1}.
    - Entry-level tests traverse the entire non-branching chain f_0..f_{m-1}.
    - nonexec_fail_tests (n_f base) and nonexec_pass_tests (n_p base) never enter the chain.
    - Optional isolated_callee_pass_tests directly exercise f_{culprit_idx+1}..f_{m-1}
      without calling f_0..f_{culprit_idx} (breaking co-execution symmetry).
    - Optional module_import_pass_tests cover all module-level/imported elements
      during unrelated passing test imports (BugsInPy dynamic-import dilution).
    """
    assert 0 <= culprit_idx < chain_len
    total_fail = entry_fail_tests + nonexec_fail_tests
    total_pass = (
        entry_pass_tests
        + nonexec_pass_tests
        + isolated_callee_pass_tests
        + module_import_pass_tests
    )

    counts: list[tuple[int, int]] = []
    for idx in range(chain_len):
        ef = entry_fail_tests
        ep = entry_pass_tests + module_import_pass_tests
        if idx > culprit_idx:
            ep += isolated_callee_pass_tests
        counts.append((ef, ep))

    out: dict[str, tuple[float, float, int, float]] = {}
    for name, fn in SBFL_FORMULAS.items():
        scores = [fn(ef, ep, total_fail, total_pass) for ef, ep in counts]
        culprit_score = scores[culprit_idx]
        spread = max(scores) - min(scores)
        # Fonte.py:L7,49 uses max-tiebreaker: rank_max(e) = |{e' : score(e') >= score(e)}|
        rank_max = sum(1 for s in scores if s >= culprit_score - 1e-12)
        strictly_higher = sum(1 for s in scores if s > culprit_score + 1e-12)
        tied = sum(1 for s in scores if abs(s - culprit_score) <= 1e-12)
        expected_acc1 = (1.0 / tied) if strictly_higher == 0 else 0.0
        out[name] = (culprit_score, spread, rank_max, expected_acc1)
    return out


@dataclass(frozen=True)
class ShiStratumRow:
    """Empirical row from Shi, Yang, & Chen (2026, arXiv:2610.25826v1) Fig. 1 & Fig. 2."""

    label: str
    partition_kind: str  # "RR" (Reciprocal Rank) or "Recall" (|P cap G|/|G|)
    n_high: int
    nofl_high: float
    fl_high: float
    n_mid: int
    nofl_mid: float
    fl_mid: float
    n_miss: int
    nofl_miss: float
    fl_miss: float
    reported_overall_delta_pp: float


def three_stratum_delta_pp(
    n_high: int,
    delta_high_pp: float,
    n_mid: int,
    delta_mid_pp: float,
    n_miss: int,
    delta_miss_pp: float,
) -> float:
    """Exact total-expectation change in Pass@1 (in percentage points)."""
    n_total = n_high + n_mid + n_miss
    return (
        n_high * delta_high_pp + n_mid * delta_mid_pp + n_miss * delta_miss_pp
    ) / n_total


def two_stratum_breakeven_hit_rate(delta_gain_pp: float, non_hit_loss_pp: float) -> float:
    """Exact Top-1 hit-rate threshold r* = Delta_- / (Delta_+ + Delta_-) for E[Delta Pass@1] >= 0."""
    assert delta_gain_pp >= 0.0 and non_hit_loss_pp >= 0.0
    denom = delta_gain_pp + non_hit_loss_pp
    return 0.0 if denom == 0.0 else non_hit_loss_pp / denom


def run_probe_1() -> dict[str, object]:
    print("=" * 84)
    print("PROBE 1: Intra-Chain SBFL Degeneracy & 3-Stratum Static-FL Anchoring Law")
    print("  Banners: [exact analytical / derived calculation]")
    print("           [exact reproduction of pinned algorithm: ACR sbfl.py & Fonte.py]")
    print("=" * 84)

    # 1A. Intra-chain SBFL tie degeneracy across m in {2, 5, 10, 20}
    print("\n[1A] Non-branching call chain f_1 -> ... -> f_m without intermediate unit tests:")
    print(
        f"{'m':>4} | {'Ochiai':>8} | {'DStar2':>8} | {'MaxSpread(5 algos)':>18} | "
        f"{'Fonte rank_max':>14} | {'Fonte vote':>10} | {'E[Acc@1]':>8}"
    )
    print("-" * 84)
    for m in (2, 5, 10, 20):
        res = sbfl_evaluate_chain(
            chain_len=m,
            culprit_idx=0,
            entry_fail_tests=2,
            entry_pass_tests=6,
            nonexec_fail_tests=1,
            nonexec_pass_tests=40,
        )
        max_spread = max(v[1] for v in res.values())
        och_score, _, rank_max, acc1 = res["Ochiai"]
        dst_score = res["DStar2"][0]
        fonte_vote = 1.0 / rank_max  # Fonte.py:L7 (alpha=0, tau='max')
        assert max_spread == 0.0, f"Expected exact zero spread across chain, got {max_spread}"
        assert rank_max == m and abs(acc1 - 1.0 / m) < 1e-12
        print(
            f"{m:>4} | {och_score:>8.4f} | {dst_score:>8.4f} | {max_spread:>18.12f} | "
            f"{rank_max:>14d} | {fonte_vote:>10.4f} | {acc1 * 100:>7.2f}%"
        )

    # Negative Control 1A-i: Intermediate unit tests on downstream callees break symmetry
    nc_unit = sbfl_evaluate_chain(
        chain_len=10,
        culprit_idx=0,
        entry_fail_tests=2,
        entry_pass_tests=6,
        nonexec_fail_tests=1,
        nonexec_pass_tests=40,
        isolated_callee_pass_tests=5,
    )
    assert nc_unit["Ochiai"][2] == 1 and nc_unit["Ochiai"][3] == 1.0
    assert nc_unit["DStar2"][2] == 1 and nc_unit["DStar2"][3] == 1.0

    # Module-import dilution check (BugsInPy mechanism: unrelated passing imports inflate e_p)
    undiluted_och = sbfl_evaluate_chain(5, 0, 1, 2, 0, 200, module_import_pass_tests=0)["Ochiai"][0]
    diluted_och = sbfl_evaluate_chain(5, 0, 1, 2, 0, 0, module_import_pass_tests=200)["Ochiai"][0]
    assert undiluted_och > 8.0 * diluted_och

    print(
        f"  [NC-1A] Adding 5 direct callee unit tests on m=10 lifts Ochiai/DStar2 "
        f"rank_max {10} -> {nc_unit['Ochiai'][2]} (E[Acc@1] = {nc_unit['Ochiai'][3]*100:.1f}%)."
    )
    print(
        f"  [Import Dilution] Module-level execution across 200 unrelated passing tests "
        f"collapses Ochiai {undiluted_och:.4f} -> {diluted_och:.4f} ({undiluted_och/diluted_och:.2f}x drop)."
    )

    # 1B. Exact 3-Stratum Law on Shi, Yang, & Chen (2026, arXiv:2610.25826v1) Fig. 1 & Fig. 2
    shi_rows = [
        ShiStratumRow(
            "GPT-5.6 Luna + OrcaLoca (SWE-V)",
            "RR",
            351, 27800 / 351, 28100 / 351,
            43, 2500 / 43, 2400 / 43,
            106, 6400 / 106, 5100 / 106,
            -2.20,
        ),
        ShiStratumRow(
            "GPT-5.6 Luna + OrcaLoca (SWE-V)",
            "Recall",
            282, 24000 / 282, 24300 / 282,
            112, 6300 / 112, 6200 / 112,
            106, 6400 / 106, 5100 / 106,
            -2.20,
        ),
        ShiStratumRow(
            "GPT-5.6 Luna + LocAgent (SWE-V)",
            "RR",
            283, 21700 / 283, 21700 / 283,
            93, 6200 / 93, 6200 / 93,
            124, 8800 / 124, 8100 / 124,
            -1.40,
        ),
        ShiStratumRow(
            "DeepSeek-v4 + LocAgent (SWE-V)",
            "RR",
            362, 29300 / 362, 28400 / 362,
            52, 3900 / 52, 3900 / 52,
            86, 6300 / 86, 5700 / 86,
            -3.00,
        ),
        ShiStratumRow(
            "GPT-5.6 Luna + FlexFL (D4J v3)",
            "RR",
            626, 48500 / 626, 48800 / 626,
            91, 6100 / 91, 4900 / 91,
            137, 8400 / 137, 8600 / 137,
            -0.82,
        ),
    ]

    print("\n[1B] Exact 3-stratum decomposition on Shi, Yang, & Chen (2026) empirical trajectories:")
    print(
        f"{'Setting':<33} | {'Metric':<6} | {'d_High':>7} | {'d_Mid':>7} | "
        f"{'d_Miss':>7} | {'Exact dPass':>11} | {'Paper':>7}"
    )
    print("-" * 92)
    for row in shi_rows:
        d_hi = row.fl_high - row.nofl_high
        d_mid = row.fl_mid - row.nofl_mid
        d_lo = row.fl_miss - row.nofl_miss
        exact_d = three_stratum_delta_pp(row.n_high, d_hi, row.n_mid, d_mid, row.n_miss, d_lo)
        assert abs(exact_d - row.reported_overall_delta_pp) < 0.05
        print(
            f"{row.label:<33} | {row.partition_kind:<6} | {d_hi:>+6.2f}% | {d_mid:>+6.2f}% | "
            f"{d_lo:>+6.2f}% | {exact_d:>+10.2f}% | {row.reported_overall_delta_pp:>+6.2f}%"
        )

    # Break-even Top-1 (RR=1) threshold r* for GPT-5.6 Luna + OrcaLoca (N=500):
    #   RR=1 (n=351, 70.2%): +3/351 = +0.8547 pp
    #   0 < RR < 1 (n=43, 8.6%): -1/43 = -2.3256 pp
    #   RR=0 (n=106, 21.2%): -13/106 = -12.2642 pp
    #   Pooled non-Top-1 (RR < 1, n=149, 29.8%): (-1 - 13)/149 = -9.3960 pp -> r*_pooled = 91.66%
    #   Binary-miss boundary (when p_{0<RR<1} = 0): r*_binary = 93.48%
    d_plus_orca = (281 - 278) / 351 * 100.0
    d_minus_pooled_orca = ((25 - 24) + (64 - 51)) / (43 + 106) * 100.0
    d_minus_rr0_only = (64 - 51) / 106 * 100.0
    r_star_pooled_orca = two_stratum_breakeven_hit_rate(d_plus_orca, d_minus_pooled_orca)
    r_star_binary_orca = two_stratum_breakeven_hit_rate(d_plus_orca, d_minus_rr0_only)
    observed_rr1_orca = 351 / 500
    reconstructed_pooled_delta = (
        observed_rr1_orca * d_plus_orca - (1.0 - observed_rr1_orca) * d_minus_pooled_orca
    )
    assert abs(r_star_pooled_orca - 4914 / 5361) < 1e-12  # 91.6620%
    assert abs(r_star_binary_orca - 4563 / 4881) < 1e-12  # 93.4849%
    assert abs(reconstructed_pooled_delta - (-2.20)) < 1e-12

    # Non-circular Negative Control 1B-i: Open-loop procedural pipeline (Agentless-1.5 + OrcaLoca,
    # arXiv:2502.00350 Table 1, N=300). Because procedural repair edits ONLY retrieved locations,
    # unretrieved functions have baseline solve rate r_0 = 0% => miss penalty Delta_- = 0.0 pp!
    #   Agentless-1.5 baseline: 176/300 matched -> 104/300 (34.67%) solved => c_base = 104/176 = 59.09%.
    #   OrcaLoca: 196/300 (+20) matched -> 123/300 (41.00%, +6.33 pp) solved => c_orca = 123/196 = 62.76%.
    # Non-circular constant-conversion prediction from +20 matched functions alone (using ONLY c_base):
    c_base_agentless = 104 / 176 * 100.0
    c_orca_agentless = 123 / 196 * 100.0
    r_star_pipeline = two_stratum_breakeven_hit_rate(c_base_agentless, non_hit_loss_pp=0.0)
    recall_only_delta_pp = three_stratum_delta_pp(
        n_high=20, delta_high_pp=c_base_agentless,
        n_mid=176, delta_mid_pp=0.0,
        n_miss=104, delta_miss_pp=0.0,  # r_0 = 0 => zero miss-anchoring loss
    )
    precision_lift_delta_pp = (196 / 300) * (c_orca_agentless - c_base_agentless)
    observed_orca_pipeline_pp = (123 - 104) / 300 * 100.0
    # Contrast if the 104 remaining misses suffered autonomous-agent anchoring (-12.264 pp):
    hypothetical_anchor_drag_pp = -(104 / 300) * d_minus_rr0_only
    assert r_star_pipeline == 0.0
    assert abs(recall_only_delta_pp - 3.9393939) < 1e-5
    assert abs((recall_only_delta_pp + precision_lift_delta_pp) - observed_orca_pipeline_pp) < 1e-12
    assert recall_only_delta_pp + hypothetical_anchor_drag_pp < 0.0  # anchor drag would flip sign!

    # Negative Control 1B-ii: Clue-stripped LR-issues + Oracle Gold Symbol / Bug Cause (Table 5, N=500)
    lr_gold_sym_delta = three_stratum_delta_pp(500, 73.0 - 68.4, 0, 0.0, 0, 0.0)
    lr_gold_cause_delta = three_stratum_delta_pp(500, 81.4 - 68.4, 0, 0.0, 0, 0.0)
    assert abs(lr_gold_sym_delta - 4.6) < 1e-9 and abs(lr_gold_cause_delta - 13.0) < 1e-9

    print(
        f"  [Break-Even Threshold] Autonomous agent (RR=1 {d_plus_orca:+.2f} pp vs. pooled RR<1 "
        f"{-d_minus_pooled_orca:+.2f} pp): r*_pooled = {r_star_pooled_orca*100:.2f}% "
        f"(r*_p_mid=0 = {r_star_binary_orca*100:.2f}%; actual RR=1 = {observed_rr1_orca*100:.1f}% -> "
        f"{reconstructed_pooled_delta:+.2f} pp)."
    )
    print(
        f"  [NC-1B Pipeline (r_0=0)] Agentless-1.5 (Delta_-=0 => r*=0.0%): +20 newly matched funcs at "
        f"fixed c_base=59.09% predict {recall_only_delta_pp:+.2f} pp + {precision_lift_delta_pp:+.2f} pp "
        f"precision lift = {observed_orca_pipeline_pp:+.2f} pp (vs. {hypothetical_anchor_drag_pp:+.2f} pp "
        f"if autonomous miss-anchoring applied)."
    )
    print(
        f"  [NC-1B LR-Issues (Oracle)] Stripping issue clues + oracle GoldSymbol/BugCause: "
        f"+GoldSym={lr_gold_sym_delta:+.1f} pp, +GoldSym+Cause={lr_gold_cause_delta:+.1f} pp."
    )
    print("  [PASS] Probe 1 assertions verified.")
    return {
        "r_star_pooled_orca": r_star_pooled_orca,
        "r_star_binary_orca": r_star_binary_orca,
        "recall_only_delta_pp": recall_only_delta_pp,
        "diluted_och": diluted_och,
    }


# =============================================================================
# PROBE 2: Flaky git bisect vs. Compute-Matched Majority-Vote & BZ-Bayes (Fonte)
# =============================================================================


def exact_bisect_survival_single(
    n_commits_pow2: int, b_star: int, eps_clean: float, eps_bug: float
) -> float:
    """Exact 1-shot hard-cut git bisect survival probability for a specific true BIC b*."""
    lo, hi = 0, n_commits_pow2 - 1
    p_survive = 1.0
    while lo < hi:
        mid = (lo + hi) // 2
        if mid >= b_star:
            p_survive *= 1.0 - eps_bug
            hi = mid
        else:
            p_survive *= 1.0 - eps_clean
            lo = mid + 1
    assert lo == b_star
    return p_survive


def exact_standard_bisect_accuracy(n_commits_pow2: int, eps_clean: float, eps_bug: float) -> float:
    """Exact expected accuracy of 1-shot hard-cut git bisect over uniform b* in {0..N-1}."""
    d = int(round(math.log2(n_commits_pow2)))
    assert (1 << d) == n_commits_pow2
    return (
        sum(
            exact_bisect_survival_single(n_commits_pow2, b_star, eps_clean, eps_bug)
            for b_star in range(n_commits_pow2)
        )
        / n_commits_pow2
    )


def majority_vote_error(eps: float, k_repeats: int) -> float:
    """Exact probability that >= ceil(k/2) of k odd iid Bernoulli(eps) flips are errors."""
    assert k_repeats % 2 == 1
    half = k_repeats // 2 + 1
    err = 0.0
    for j in range(half, k_repeats + 1):
        err += math.comb(k_repeats, j) * (eps**j) * ((1.0 - eps) ** (k_repeats - j))
    return err


def simulate_hard_bisect_k_vote(
    n_commits: int,
    b_star: int,
    eps_clean: float,
    eps_bug: float,
    k_repeats: int,
    budget: int,
    rng: random.Random,
) -> tuple[int, int]:
    """Run hard-cut git bisect using k_repeats majority vote per pivot under strict budget."""
    lo, hi = 0, n_commits - 1
    used = 0
    while lo < hi and used + k_repeats <= budget:
        mid = (lo + hi) // 2
        fails = 0
        for _ in range(k_repeats):
            used += 1
            is_fail = (
                (rng.random() < (1.0 - eps_bug))
                if mid >= b_star
                else (rng.random() < eps_clean)
            )
            if is_fail:
                fails += 1
        if fails > k_repeats // 2:
            hi = mid
        else:
            lo = mid + 1
    return lo, used


def simulate_restarted_standard_bisect(
    n_commits: int,
    b_star: int,
    eps_clean: float,
    eps_bug: float,
    budget: int,
    rng: random.Random,
) -> tuple[int, int]:
    """Run independent 1-shot git bisect restarts until budget is exhausted; return plurality/median."""
    d = int(math.ceil(math.log2(n_commits)))
    n_runs = budget // d
    preds: list[int] = []
    total_used = 0
    for _ in range(n_runs):
        pred, used = simulate_hard_bisect_k_vote(
            n_commits, b_star, eps_clean, eps_bug, k_repeats=1, budget=d, rng=rng
        )
        preds.append(pred)
        total_used += used
    counts: dict[int, int] = {}
    for p in preds:
        counts[p] = counts.get(p, 0) + 1
    best_cnt = max(counts.values())
    winners = sorted(p for p, c in counts.items() if c == best_cnt)
    if len(winners) == 1:
        return winners[0], total_used
    preds.sort()
    return preds[len(preds) // 2], total_used


def build_fonte_prior(
    n_commits: int,
    cand_indices: list[int],
    decay_lambda: float = 0.1,
    laplace_mix: float = 0.02,
) -> list[float]:
    """Construct normalized Fonte depth-decayed commit prior (An et al. 2025 Eq. 6 + FACF floor).

    cand_indices is ordered from highest-priority candidate in C_BIC to lowest-priority in C_BIC.
    laplace_mix=0.0 corresponds to hard Stage-1/2 pruning (s(c)=0 outside C_BIC);
    laplace_mix>0 retains soft support over all N commits so Bayesian updates can recover
    even if a bug originated in an off-support configuration or build commit.
    """
    raw = [0.0] * n_commits
    for depth, idx in enumerate(cand_indices):
        raw[idx] = (1.0 - decay_lambda) ** depth
    s_raw = sum(raw)
    assert s_raw > 0.0
    base = [w / s_raw for w in raw]
    return [(1.0 - laplace_mix) * b + laplace_mix / n_commits for b in base]


def simulate_bz_bayesian_bisect(
    prior: list[float],
    b_star: int,
    eps_clean: float,
    eps_bug: float,
    budget: int,
    rng: random.Random,
) -> tuple[int, int]:
    """Burnashev-Zigangirov / FACF Bayesian posterior median bisection under strict budget."""
    n_commits = len(prior)
    post = list(prior)
    used = 0
    for _ in range(budget):
        if eps_clean == 0.0 and eps_bug == 0.0 and max(post) > 1.0 - 1e-12:
            break

        cums = list(itertools.accumulate(post))
        idx = bisect.bisect_left(cums, 0.5, 0, n_commits - 1)
        best_p = 0
        best_gap = 2.0
        if idx > 0:
            v_left = cums[idx - 1]
            p_left = bisect.bisect_left(cums, v_left, 0, idx)
            best_p = p_left
            best_gap = abs(2.0 * v_left - 1.0)
        if idx < n_commits - 1:
            gap_r = abs(2.0 * cums[idx] - 1.0)
            if gap_r < best_gap - 1e-15:
                best_gap = gap_r
                best_p = idx

        used += 1
        is_fail = (
            (rng.random() < (1.0 - eps_bug))
            if best_p >= b_star
            else (rng.random() < eps_clean)
        )
        if is_fail:
            l_bug, l_clean = 1.0 - eps_bug, eps_clean
        else:
            l_bug, l_clean = eps_bug, 1.0 - eps_clean

        split = best_p + 1
        post[:split] = [x * l_bug for x in post[:split]]
        post[split:] = [x * l_clean for x in post[split:]]
        total = sum(post)

        if total == 0.0:
            break
        inv = 1.0 / total
        post = [x * inv for x in post]

    best_b = max(range(n_commits), key=lambda b: post[b])
    return best_b, used


def run_probe_2(rng: random.Random) -> dict[str, object]:
    print("\n" + "=" * 84)
    print("PROBE 2: Flaky git bisect Catastrophe vs. Compute-Matched BZ-Bayes & Fonte Prior")
    print("  Banners: [exact analytical / derived calculation]")
    print("           [seeded Monte Carlo on matched b* DGP under strict budget B=21]")
    print("=" * 84)

    n_commits = 128  # d = log2(128) = 7 steps for 1-shot bisect; k=3 vote uses 3*7 = 21 evals
    budget = 21      # Strictly equal test-execution budget across all multi-eval strategies
    n_trials = 600

    # Verify exact analytical closed form for uniform b* in {0..127}: (1 - (eps0 + eps1)/2)^7
    for e0, e1 in [(0.0, 0.0), (0.05, 0.10), (0.10, 0.15), (0.15, 0.20)]:
        exact_tree = exact_standard_bisect_accuracy(n_commits, e0, e1)
        closed_form = (1.0 - 0.5 * (e0 + e1)) ** 7
        assert abs(exact_tree - closed_form) < 1e-12

    print(
        f"\n[2A] Matched-DGP comparison on N={n_commits} commits (budget B={budget} test runs, "
        f"{n_trials} shared b* draws/row):"
    )
    print(
        f"{'Flake (e0,e1)':<13} | {'1-Shot(7)':>9} | {'3xRst(21)':>9} | {'3-Vote(21)':>10} | "
        f"{'BZ-Unif(21)':>11} | {'BZ-FonteNoisy':>13} | {'BZ-FonteExact':>13}"
    )
    print("-" * 92)

    # Fonte Stage 1-2 reduces candidate commits to 11% (14 of 128 commits, Fonte Table IV 11.0%)
    n_cbic = 14
    dgp_weights = [(0.9**d) for d in range(n_cbic)]
    tot_dgp_w = sum(dgp_weights)
    summary_rows: dict[tuple[float, float], tuple[float, float, float, float, float, float]] = {}

    for e0, e1 in [(0.00, 0.00), (0.05, 0.10), (0.10, 0.15), (0.15, 0.20)]:
        sum_dgp_1shot = 0.0
        sum_dgp_3vote_exact = 0.0
        acc_1shot_mc = 0
        acc_restart = 0
        acc_3vote_mc = 0
        acc_bz_unif = 0
        acc_bz_fonte_noisy = 0
        acc_bz_fonte_exact = 0

        unif_prior = [1.0 / n_commits] * n_commits
        mv_e0 = majority_vote_error(e0, 3)
        mv_e1 = majority_vote_error(e1, 3)

        for _ in range(n_trials):
            cand_desc = sorted(rng.sample(range(n_commits), n_cbic), reverse=True)
            # Well-specified exact-DGP Fonte prior ceiling:
            fonte_exact_prior = build_fonte_prior(
                n_commits, cand_desc, decay_lambda=0.1, laplace_mix=0.02
            )
            # Rank-perturbed & miscalibrated Fonte prior (noisy SBFL statement ranks jumble
            # C_BIC order via sigma=1.6 log-score noise + steeper assumed decay_lambda=0.25):
            log_09 = math.log(0.9)
            noisy_cand = [
                c
                for _, c in sorted(
                    ((d * log_09 + rng.gauss(0.0, 1.6), c) for d, c in enumerate(cand_desc)),
                    reverse=True,
                )
            ]
            fonte_noisy_prior = build_fonte_prior(
                n_commits, noisy_cand, decay_lambda=0.25, laplace_mix=0.02
            )

            # Sample b* once and share identically across ALL 6 columns (98% in C_BIC, 2% off-support)
            if rng.random() < 0.98:
                u = rng.random() * tot_dgp_w
                acc_w = 0.0
                b_star = cand_desc[-1]
                for idx_c, w in zip(cand_desc, dgp_weights):
                    acc_w += w
                    if u <= acc_w:
                        b_star = idx_c
                        break
            else:
                non_cand = [c for c in range(n_commits) if c not in set(cand_desc)]
                b_star = rng.choice(non_cand)

            sum_dgp_1shot += exact_bisect_survival_single(n_commits, b_star, e0, e1)
            sum_dgp_3vote_exact += exact_bisect_survival_single(n_commits, b_star, mv_e0, mv_e1)

            pred_1s, used_1s = simulate_hard_bisect_k_vote(
                n_commits, b_star, e0, e1, k_repeats=1, budget=7, rng=rng
            )
            pred_rst, used_rst = simulate_restarted_standard_bisect(
                n_commits, b_star, e0, e1, budget, rng
            )
            pred_3v, used_3v = simulate_hard_bisect_k_vote(
                n_commits, b_star, e0, e1, k_repeats=3, budget=budget, rng=rng
            )
            pred_bzu, used_bzu = simulate_bz_bayesian_bisect(
                unif_prior, b_star, e0, e1, budget, rng
            )
            pred_bzfn, used_bzfn = simulate_bz_bayesian_bisect(
                fonte_noisy_prior, b_star, e0, e1, budget, rng
            )
            pred_bzfe, used_bzfe = simulate_bz_bayesian_bisect(
                fonte_exact_prior, b_star, e0, e1, budget, rng
            )

            assert used_1s == 7
            if e0 > 0.0 or e1 > 0.0:
                assert used_rst == budget == used_3v == used_bzu == used_bzfn == used_bzfe

            acc_1shot_mc += int(pred_1s == b_star)
            acc_restart += int(pred_rst == b_star)
            acc_3vote_mc += int(pred_3v == b_star)
            acc_bz_unif += int(pred_bzu == b_star)
            acc_bz_fonte_noisy += int(pred_bzfn == b_star)
            acc_bz_fonte_exact += int(pred_bzfe == b_star)

        r_1s_dgp = sum_dgp_1shot / n_trials
        r_1s_mc = acc_1shot_mc / n_trials
        r_rst = acc_restart / n_trials
        r_3v = acc_3vote_mc / n_trials
        r_3v_dgp = sum_dgp_3vote_exact / n_trials
        r_bzu = acc_bz_unif / n_trials
        r_bzfn = acc_bz_fonte_noisy / n_trials
        r_bzfe = acc_bz_fonte_exact / n_trials
        summary_rows[(e0, e1)] = (r_1s_dgp, r_rst, r_3v, r_bzu, r_bzfn, r_bzfe)

        assert abs(r_1s_mc - r_1s_dgp) < 0.045
        assert abs(r_3v - r_3v_dgp) < 0.045
        print(
            f"({e0:.2f}, {e1:.2f})  | {r_1s_dgp*100:>8.2f}% | {r_rst*100:>8.2f}% | "
            f"{r_3v*100:>9.2f}% | {r_bzu*100:>10.2f}% | {r_bzfn*100:>12.2f}% | {r_bzfe*100:>12.2f}%"
        )

    s_mid = summary_rows[(0.10, 0.15)]
    s_hi = summary_rows[(0.15, 0.20)]
    unif_1shot_mid = exact_standard_bisect_accuracy(n_commits, 0.10, 0.15)  # 39.27%
    assert abs(unif_1shot_mid - (0.875**7)) < 1e-12
    assert s_mid[0] < 0.41 and s_hi[0] < 0.28
    # Both exact-DGP and noisy/miscalibrated Fonte priors beat BZ-Uniform, 3-Vote, and 1-Shot:
    assert s_mid[5] >= s_mid[4] > s_mid[3] > s_mid[2] > s_mid[0]
    assert s_hi[5] >= s_hi[4] > s_hi[3] > s_hi[2] > s_hi[0]

    # Negative Control 2A: Exact noiseless steps across the FULL Fonte prior (not just top-1!)
    canonical_cand = list(range(n_cbic - 1, -1, -1))
    hard_fonte_canon = build_fonte_prior(n_commits, canonical_cand, decay_lambda=0.1, laplace_mix=0.0)
    steps_by_depth: list[int] = []
    for c_idx in canonical_cand:
        pred_f, st_f = simulate_bz_bayesian_bisect(hard_fonte_canon, c_idx, 0.0, 0.0, budget, rng)
        assert pred_f == c_idx
        steps_by_depth.append(st_f)
    exact_full_prior_steps = sum(w * st for w, st in zip(dgp_weights, steps_by_depth)) / tot_dgp_w
    unweighted_cbic_steps = sum(steps_by_depth) / n_cbic
    top1_steps = steps_by_depth[0]
    tail_steps = steps_by_depth[-1]
    assert top1_steps == 3 and tail_steps == 5
    assert 3.70 < exact_full_prior_steps < 3.80  # exact 3.74 steps across full prior vs. 7.00
    assert unweighted_cbic_steps == 4.0

    # Also verify via 250-trial MC sampling b* across the FULL hard Fonte prior (not cand_desc[0]):
    mc_full_prior_steps = 0
    n_nc2a = 250
    for _ in range(n_nc2a):
        cand_desc = sorted(rng.sample(range(n_commits), n_cbic), reverse=True)
        hard_fonte = build_fonte_prior(n_commits, cand_desc, decay_lambda=0.1, laplace_mix=0.0)
        u = rng.random() * tot_dgp_w
        acc_w = 0.0
        b_star = cand_desc[-1]
        for idx_c, w in zip(cand_desc, dgp_weights):
            acc_w += w
            if u <= acc_w:
                b_star = idx_c
                break
        pred_hf, st_hf = simulate_bz_bayesian_bisect(hard_fonte, b_star, 0.0, 0.0, budget, rng)
        assert pred_hf == b_star
        mc_full_prior_steps += st_hf
    avg_mc_full_prior_steps = mc_full_prior_steps / n_nc2a
    assert abs(avg_mc_full_prior_steps - exact_full_prior_steps) < 0.15

    # Negative Control 2B: Adversarial off-support BIC (config/build commit outside C_BIC)
    hard_miss_hits = 0
    soft_miss_hits = 0
    n_adv = 250
    for _ in range(n_adv):
        cand_desc = sorted(rng.sample(range(n_commits), n_cbic), reverse=True)
        non_cand = [c for c in range(n_commits) if c not in set(cand_desc)]
        b_star = rng.choice(non_cand)
        hard_prior = build_fonte_prior(n_commits, cand_desc, decay_lambda=0.1, laplace_mix=0.0)
        soft_prior = build_fonte_prior(n_commits, cand_desc, decay_lambda=0.1, laplace_mix=0.05)
        p_hard, _ = simulate_bz_bayesian_bisect(hard_prior, b_star, 0.05, 0.05, budget, rng)
        p_soft, _ = simulate_bz_bayesian_bisect(soft_prior, b_star, 0.05, 0.05, budget, rng)
        hard_miss_hits += int(p_hard == b_star)
        soft_miss_hits += int(p_soft == b_star)

    r_hard_adv = hard_miss_hits / n_adv
    r_soft_adv = soft_miss_hits / n_adv
    assert r_hard_adv == 0.0 and r_soft_adv > 0.90

    print(
        f"  [Uniform-b* Identity] At (0.10, 0.15), uniform E[b*]=63.5 gives (1-0.125)^7 = "
        f"{unif_1shot_mid*100:.2f}% vs. newest-weighted DGP E[b*]~77.5 = {s_mid[0]*100:.2f}%."
    )
    print(
        f"  [NC-2A Noiseless Full Prior] 1-shot git bisect = 7.00 steps; Fonte Alg.1 weighted "
        f"bisection exact full-prior = {exact_full_prior_steps:.2f} steps (MC = "
        f"{avg_mc_full_prior_steps:.2f}; top-1 = {top1_steps}, low-weight tail = {tail_steps} vs. "
        f"4.00 unweighted on C_BIC)."
    )
    print(
        f"  [NC-2B Off-Support Config BIC] Hard-pruned Fonte Alg.1 = {r_hard_adv*100:.1f}% "
        f"vs. Laplace-smoothed BZ-Bayes (B={budget}, e=0.05) = {r_soft_adv*100:.1f}%."
    )
    print("  [PASS] Probe 2 assertions verified.")
    return {
        "mid_1shot": s_mid[0],
        "mid_3vote": s_mid[2],
        "mid_bz_unif": s_mid[3],
        "mid_bz_fonte_noisy": s_mid[4],
        "mid_bz_fonte_exact": s_mid[5],
        "full_prior_steps": exact_full_prior_steps,
        "adv_soft": r_soft_adv,
    }


# =============================================================================
# PROBE 3: Runtime Inspection Granularity & Unbiased Cross-Agent pass_X@2
# =============================================================================


def _approx_tokens(text: str) -> int:
    """Deterministic ~4 chars/token code-token estimator."""
    return max(1, (len(text) + 3) // 4)


def _format_ldb_vars(env: dict[str, object]) -> str:
    """Exact reproduction of LLMDebugger tracer.py:L151-152 100-char value truncation."""
    raw = "\t".join(f"{k}={repr(v)}" for k, v in sorted(env.items()))
    return raw if len(raw) < 100 else (raw[:50] + "..." + raw[-50:])


def _run_packet_prefix(n_iters: int, bug_iter: int, stop_iter: int) -> tuple[int, int, int, int]:
    """Execute iterations 0..stop_iter of target loop; return (pkt, window_sum, checksum, spec_checksum)."""
    assert 0 <= stop_iter < n_iters
    checksum = 17
    spec_checksum = 17
    window_sum = 0
    pkt = 0
    for k in range(stop_iter + 1):
        pkt = ((k * 31) + 7) % 97
        window_sum = (window_sum + pkt) % 251
        spec_checksum = (spec_checksum + window_sum) % 1009
        if k == bug_iter:
            checksum = (checksum - window_sum) % 1009
        else:
            checksum = (checksum + window_sum) % 1009
    return pkt, window_sum, checksum, spec_checksum


def _execute_conditional_pdb_bisect(n_iters: int, bug_iter: int) -> tuple[list[int], bool, int]:
    """Execute genuine ceil(log2 N) conditional-breakpoint binary search over target loop.

    Uses only single-command pdb actions valid under debug-gym pdb.py:L195-200 (`display ...`,
    `b 14, k == mid` / `condition 1 k == mid`, `r`), comparing observed checksum against
    specification without prior knowledge of bug_iter. Fits within Debug2Fix's 25-step per-session
    cap up to N=250 (1 + 2*ceil(log2 250) + 1 = 18 turns <= 25).
    """
    turn_obs_tokens: list[int] = []
    # Setup turn: register persistent watch expression (`display` prints automatically on stops)
    turn_obs_tokens.append(
        _approx_tokens("(Pdb) display (k, pkt, window_sum, checksum, spec)\ndisplay enabled")
    )

    lo, hi = 0, n_iters - 1
    bp_created = False
    while lo < hi:
        mid = (lo + hi) // 2
        if not bp_created:
            cmd_bp = f"(Pdb) b 14, k == {mid}\nBreakpoint 1 at packet.py:14 (condition: k == {mid})"
            bp_created = True
        else:
            cmd_bp = f"(Pdb) condition 1 k == {mid}\nNew condition set for breakpoint 1."
        turn_obs_tokens.append(_approx_tokens(cmd_bp))

        pkt, wsum, csum, spec_csum = _run_packet_prefix(n_iters, bug_iter, mid)
        cmd_run = (
            f"(Pdb) r\n> packet.py(14)process_packets()\n"
            f"  12     pkt = ((k * 31) + 7) % 97\n"
            f"  13     window_sum = (window_sum + pkt) % 251\n"
            f"->14     checksum = step_update(k, checksum, window_sum)\n"
            f"display: ({mid}, {pkt}, {wsum}, {csum}, {spec_csum})"
        )
        turn_obs_tokens.append(_approx_tokens(cmd_run))

        if csum == spec_csum:
            lo = mid + 1
        else:
            hi = mid

    # Final verification probe at located k = lo to inspect corrupting transition
    pkt_f, wsum_f, csum_f, spec_f = _run_packet_prefix(n_iters, bug_iter, lo)
    turn_obs_tokens.append(
        _approx_tokens(
            f"(Pdb) b 14, k == {lo} -> r\n"
            f"  13     window_sum = (window_sum + pkt) % 251\n"
            f"->14     checksum = (checksum - window_sum) % 1009\n"
            f"transition k={lo} pkt={pkt_f} wsum={wsum_f} got={csum_f} expected={spec_f}"
        )
    )
    located = (lo == bug_iter) and (csum_f != spec_f)
    return turn_obs_tokens, located, len(turn_obs_tokens)


def measure_runtime_inspection_modes(n_iters: int, bug_iter: int) -> dict[str, dict[str, int | bool]]:
    """Execute target loop and measure main-context vs. total billed tokens across 6 modes."""
    assert 0 <= bug_iter < n_iters
    line_records: list[tuple[int, str]] = []
    block_records: list[tuple[int, str]] = []

    checksum = 17
    window_sum = 0
    for k in range(n_iters):
        v0 = _format_ldb_vars({"k": k, "checksum": checksum, "window_sum": window_sum})
        pkt = ((k * 31) + 7) % 97
        v1 = _format_ldb_vars({"k": k, "pkt": pkt, "checksum": checksum, "window_sum": window_sum})
        line_records.append((k, f"# {v0}\n  pkt = ((k * 31) + 7) % 97\n# {v1}"))

        window_sum = (window_sum + pkt) % 251
        v2 = _format_ldb_vars({"k": k, "pkt": pkt, "checksum": checksum, "window_sum": window_sum})
        line_records.append((k, f"# {v1}\n  window_sum = (window_sum + pkt) % 251\n# {v2}"))

        line_records.append((k, f"# {v2}\n  checksum = step_update(k, checksum, window_sum)\n# {v2}"))
        if k == bug_iter:
            checksum = (checksum - window_sum) % 1009
            stmt = "checksum = (checksum - window_sum) % 1009"
        else:
            checksum = (checksum + window_sum) % 1009
            stmt = "checksum = (checksum + window_sum) % 1009"
        v3 = _format_ldb_vars({"k": k, "pkt": pkt, "checksum": checksum, "window_sum": window_sum})
        line_records.append((k, f"# {v2}\n    {stmt}\n# {v3}"))
        block_records.append(
            (k, f"[BLOCK-{k}]\n  # {v0}\n  pkt=...; window_sum=...; {stmt}\n  # {v3}")
        )

    base_main_ctx = 1200  # issue description + source file + failing test assertion

    # Mode 1a: Untruncated raw `python -m trace` dynamic line dump
    raw_line_payload = "\n".join(rec for _, rec in line_records)
    raw_line_tok = base_main_ctx + _approx_tokens(raw_line_payload)

    # Mode 1b: Pinned LDB repo line-level head-15/tail-15 slicing
    # (FloridSleeves/LLMDebugger@49ac191f py_generate.py:L208-221 max_num_blocks = 30;
    #  model.py:L117 also caps trace messages at 3,097 tokens; paper App. E states 25+25=50)
    sampled_lines_30 = (
        line_records if len(line_records) <= 30 else (line_records[:15] + line_records[-15:])
    )
    sampled_lines_50 = (
        line_records if len(line_records) <= 50 else (line_records[:25] + line_records[-25:])
    )
    ldb_line30_trace_tok = min(3097, _approx_tokens("\n".join(r for _, r in sampled_lines_30)))
    ldb_line30_tok = base_main_ctx + ldb_line30_trace_tok
    ldb_line30_sees = any(k == bug_iter and "checksum = (" in r for k, r in sampled_lines_30)
    ldb_line50_sees = any(k == bug_iter and "checksum = (" in r for k, r in sampled_lines_50)

    # Mode 2: Pinned LDB basic-block head-5/tail-5 slicing (max_num_blocks = 10)
    sampled_blocks = (
        block_records if len(block_records) <= 10 else (block_records[:5] + block_records[-5:])
    )
    ldb_block_tok = base_main_ctx + min(
        3097, _approx_tokens("\n".join(b for _, b in sampled_blocks))
    )
    ldb_block_sees = any(k == bug_iter for k, _ in sampled_blocks)

    # Mode 3a: Unconditional inline pdb (`b 14` halting on every iteration k=0,1,2...; 25-turn cap)
    max_turns_cap = 25
    needed_uncond_turns = 2 * (bug_iter + 1)
    exec_uncond_turns = min(needed_uncond_turns, max_turns_cap)
    uncond_sees = needed_uncond_turns <= max_turns_cap
    per_turn_obs = 55
    uncond_cum_tok = sum(base_main_ctx + t * per_turn_obs for t in range(1, exec_uncond_turns + 1))
    uncond_main_ctx = base_main_ctx + exec_uncond_turns * per_turn_obs

    # Mode 3b vs. Mode 4: Equal-capability executed ceil(log2 N) conditional-breakpoint bisection
    # BOTH InlinePdbCond and SubagentCond execute the EXACT SAME binary-search debugger turns!
    bisect_obs, bisect_hit, bisect_turns = _execute_conditional_pdb_bisect(n_iters, bug_iter)
    assert bisect_turns <= max_turns_cap or n_iters > 256

    # Mode 3b (InlinePdbCond): all debugger turns accumulate directly inside the main agent context
    inline_cond_cum_obs = 0
    inline_cond_billed = 0
    for obs_t in bisect_obs:
        inline_cond_cum_obs += obs_t + 25  # assistant tool call + pdb observation
        inline_cond_billed += base_main_ctx + inline_cond_cum_obs
    inline_cond_main_ctx = base_main_ctx + inline_cond_cum_obs

    # Mode 4 (SubagentCond, Debug2Fix §4.1-4.2): subagent runs the identical `bisect_turns` loop
    # inside its isolated context (`sub_base_ctx = 1200` for subagent prompt + debugger schemas +
    # source file), then returns ONLY a compact `<debug_answer>` (120 tok) to the main repair agent.
    sub_base_ctx = 1200
    sub_cum_obs = 0
    sub_internal_billed = 0
    for obs_t in bisect_obs:
        sub_cum_obs += obs_t + 25
        sub_internal_billed += sub_base_ctx + sub_cum_obs
    debug_answer_tok = 120
    # Main agent pays 1 turn to invoke debug_subagent + holds base_main_ctx + debug_answer_tok at edit:
    sub_main_ctx = base_main_ctx + debug_answer_tok
    sub_total_billed = base_main_ctx + sub_internal_billed + sub_main_ctx

    return {
        "raw_line": {
            "main_ctx_tok": raw_line_tok,
            "total_billed_tok": raw_line_tok,
            "sees_transition": True,
        },
        "ldb_line30": {
            "main_ctx_tok": ldb_line30_tok,
            "total_billed_tok": ldb_line30_tok,
            "sees_transition": ldb_line30_sees,
            "paper50_sees": ldb_line50_sees,
        },
        "ldb_block10": {
            "main_ctx_tok": ldb_block_tok,
            "total_billed_tok": ldb_block_tok,
            "sees_transition": ldb_block_sees,
        },
        "inline_uncond_pdb": {
            "main_ctx_tok": uncond_main_ctx,
            "total_billed_tok": uncond_cum_tok,
            "sees_transition": uncond_sees,
        },
        "inline_cond_pdb": {
            "main_ctx_tok": inline_cond_main_ctx,
            "total_billed_tok": inline_cond_billed,
            "sees_transition": bisect_hit,
            "turns": bisect_turns,
        },
        "subagent_cond_pdb": {
            "main_ctx_tok": sub_main_ctx,
            "total_billed_tok": sub_total_billed,
            "sees_transition": bisect_hit,
            "turns": bisect_turns,
        },
    }


def pass_at_2_unbiased(c_m: int, n_runs: int = 3) -> float:
    """Magnuson, Kitanidis, & Lee (2026, arXiv:2611.08666v1) Eq. (2) & Eq. (4) intra-agent pass@2."""
    return 1.0 - math.comb(n_runs - c_m, 2) / math.comb(n_runs, 2)


def pass_x_at_2_unbiased(c_a: int, c_b: int, n_runs: int = 3) -> float:
    """Magnuson, Kitanidis, & Lee (2026, arXiv:2611.08666v1) Eq. (3) & Eq. (5) cross-agent pass_X@2."""
    return 1.0 - ((n_runs - c_a) * (n_runs - c_b)) / (n_runs * n_runs)


def run_probe_3(rng: random.Random) -> dict[str, object]:
    print("\n" + "=" * 84)
    print("PROBE 3: Runtime Inspection Granularity & Unbiased Cross-Agent pass_X@2")
    print("  Banners: [exact reproduction of pinned LDB head/tail slicing + executed bisection loop]")
    print("           [exact analytical calculation: Magnuson et al. 2026 Eq. (2)-(5)]")
    print("=" * 84)

    print(
        "\n[3A] Executed loop inspection across horizon N (bug at k* = floor(0.5*N)); "
        "MainCtx vs. TotalBill:"
    )
    print(
        f"{'N':>3} | {'RawLine':>7} | {'LDBLine30':>11} | {'LDBBlk10':>10} | "
        f"{'UncondPdb(Bill)':>17} | {'InlineCond(Bill)':>18} | {'Subagent(TotalBill)':>20}"
    )
    print("-" * 100)

    loop_results: dict[int, dict[str, dict[str, int | bool]]] = {}
    for n_iters in (1, 10, 50, 250):
        k_star = n_iters // 2 if n_iters > 1 else 0
        res = measure_runtime_inspection_modes(n_iters, k_star)
        loop_results[n_iters] = res
        rl = res["raw_line"]
        ll = res["ldb_line30"]
        lb = res["ldb_block10"]
        up = res["inline_uncond_pdb"]
        ic = res["inline_cond_pdb"]
        sc = res["subagent_cond_pdb"]
        print(
            f"{n_iters:>3} | {int(rl['main_ctx_tok']):>7d} | "
            f"{int(ll['main_ctx_tok']):>7d}({'Y' if ll['sees_transition'] else 'N'}) | "
            f"{int(lb['main_ctx_tok']):>6d}({'Y' if lb['sees_transition'] else 'N'}) | "
            f"{int(up['main_ctx_tok']):>5d}({int(up['total_billed_tok']):>6d}/{'Y' if up['sees_transition'] else 'N'}) | "
            f"{int(ic['main_ctx_tok']):>5d}({int(ic['total_billed_tok']):>6d}/{'Y' if ic['sees_transition'] else 'N'}) | "
            f"{int(sc['main_ctx_tok']):>5d}({int(sc['total_billed_tok']):>7d}/{'Y' if sc['sees_transition'] else 'N'})"
        )

    # Verify key architectural invariants for 3A:
    # 1. Paper-vs.-Repo LDB line-slicing discrepancy at N=10 (k*=5):
    #    Pinned repo LDBLine30 ([:15]+[-15:]) misses k*=5 while paper App. E ([:25]+[-25:]) and
    #    LDBBlock10 ([:5]+[-5:]) capture k*=5; at N>=50 all fixed-window LDB slices miss k*.
    assert loop_results[10]["ldb_line30"]["sees_transition"] is False
    assert loop_results[10]["ldb_line30"]["paper50_sees"] is True
    assert loop_results[10]["ldb_block10"]["sees_transition"] is True
    assert loop_results[50]["ldb_line30"]["paper50_sees"] is False
    assert loop_results[250]["ldb_block10"]["sees_transition"] is False
    assert loop_results[250]["inline_uncond_pdb"]["sees_transition"] is False

    # 2. Equal-capability conditional-breakpoint bisection (`InlineCond` vs. `SubagentCond`):
    #    Both locate k* across all N (`sees_transition=True`), and Subagent TotalBill scales
    #    strictly monotonically with ceil(log2 N) AND exceeds InlineCond at small/medium N
    #    (matching Debug2Fix Table 1's 1.13x-2.87x total token overhead), while Subagent
    #    MainCtx stays strictly O(1) = 1320 tokens across all N!
    for n_iters in (1, 10, 50, 250):
        assert loop_results[n_iters]["inline_cond_pdb"]["sees_transition"] is True
        assert loop_results[n_iters]["subagent_cond_pdb"]["sees_transition"] is True
        assert int(loop_results[n_iters]["subagent_cond_pdb"]["main_ctx_tok"]) == 1320
        assert int(loop_results[n_iters]["subagent_cond_pdb"]["total_billed_tok"]) > int(
            loop_results[n_iters]["inline_cond_pdb"]["total_billed_tok"]
        )
    assert (
        int(loop_results[1]["subagent_cond_pdb"]["total_billed_tok"])
        < int(loop_results[10]["subagent_cond_pdb"]["total_billed_tok"])
        < int(loop_results[50]["subagent_cond_pdb"]["total_billed_tok"])
        < int(loop_results[250]["subagent_cond_pdb"]["total_billed_tok"])
    )
    assert int(loop_results[250]["inline_cond_pdb"]["main_ctx_tok"]) > int(
        1.7 * int(loop_results[250]["subagent_cond_pdb"]["main_ctx_tok"])
    )
    assert int(loop_results[1]["ldb_block10"]["total_billed_tok"]) * 3 < int(
        loop_results[1]["subagent_cond_pdb"]["total_billed_tok"]
    )

    print(
        f"  [LDB Paper-vs.-Repo Check] At N=10 (k*=5), repo LDBLine30 ([:15]+[-15:]) Hit=N vs. "
        f"paper App.E 50-line Hit=Y & LDBBlock10 Hit=Y; at N>=50 all fixed-window slices Hit=N."
    )
    print(
        f"  [Subagent Isolation vs. Total Spend] Subagent TotalBill scales with log2(N) "
        f"({loop_results[1]['subagent_cond_pdb']['total_billed_tok']} -> "
        f"{loop_results[250]['subagent_cond_pdb']['total_billed_tok']} tok), trading higher/comparable "
        f"total spend for O(1) main-agent context (1320 tok vs. InlineCond "
        f"{loop_results[250]['inline_cond_pdb']['main_ctx_tok']} tok & RawLine "
        f"{loop_results[250]['raw_line']['main_ctx_tok']} tok)."
    )

    # 3B. Magnuson, Kitanidis, & Lee (2026, arXiv:2611.08666v1 Eq. 3 & Eq. 5) Unbiased pass_X@2
    n_tasks = 500
    p_bash_vec: list[float] = []
    p_pdb_vec: list[float] = []
    for j in range(n_tasks):
        u = (j + 0.5) / n_tasks
        if u < 0.45:
            pb, pp = 0.95, 0.80
        elif u < 0.67:
            pb, pp = 0.62, 0.19
        else:
            pb, pp = 0.01, 0.005
        p_bash_vec.append(pb)
        p_pdb_vec.append(pp)

    true_bash_p1 = sum(p_bash_vec) / n_tasks
    true_pdb_p1 = sum(p_pdb_vec) / n_tasks
    true_bash_p2 = sum(1.0 - (1.0 - p) ** 2 for p in p_bash_vec) / n_tasks
    true_cross_p2 = (
        sum(1.0 - (1.0 - pb) * (1.0 - pp) for pb, pp in zip(p_bash_vec, p_pdb_vec)) / n_tasks
    )
    expected_single_seed_pdb_only = sum(
        (1.0 - pb) * pp for pb, pp in zip(p_bash_vec, p_pdb_vec)
    )

    est_b2_sum = 0.0
    est_x2_sum = 0.0
    single_seed_excl_sum = 0.0
    n_campaigns = 80
    for _ in range(n_campaigns):
        b_runs = [[int(rng.random() < pb) for _ in range(3)] for pb in p_bash_vec]
        p_runs = [[int(rng.random() < pp) for _ in range(3)] for pp in p_pdb_vec]
        est_b2_sum += sum(pass_at_2_unbiased(sum(r), 3) for r in b_runs) / n_tasks
        est_x2_sum += (
            sum(pass_x_at_2_unbiased(sum(rb), sum(rp), 3) for rb, rp in zip(b_runs, p_runs))
            / n_tasks
        )
        single_seed_excl_sum += sum(
            1 for rb, rp in zip(b_runs, p_runs) if rb[0] == 0 and rp[0] == 1
        )

    mc_bash_p2 = est_b2_sum / n_campaigns
    mc_cross_p2 = est_x2_sum / n_campaigns
    mc_excl = single_seed_excl_sum / n_campaigns

    assert all(pp < pb for pb, pp in zip(p_bash_vec, p_pdb_vec))
    assert expected_single_seed_pdb_only > 15.0
    assert true_bash_p2 > true_cross_p2 + 0.04
    assert abs(mc_bash_p2 - true_bash_p2) < 0.008 and abs(mc_cross_p2 - true_cross_p2) < 0.008

    print(
        f"\n[3B] Unbiased pass_X@2 (Eq. 3 & Eq. 5, 500 tasks, p_pdb(j) < p_bash(j) EVERYWHERE):"
    )
    print(
        f"  True pass@1: bash={true_bash_p1*100:.1f}%, pdb={true_pdb_p1*100:.1f}% | "
        f"Illusory 1-seed 'pdb-only' solves: exact={expected_single_seed_pdb_only:.1f}/500 "
        f"(MC={mc_excl:.1f}/500)"
    )
    print(
        f"  Budget-matched k=2: pass@2(bash,bash)={true_bash_p2*100:.2f}% (3-seed est {mc_bash_p2*100:.2f}%) "
        f"> pass_X@2(bash,pdb)={true_cross_p2*100:.2f}% (3-seed est {mc_cross_p2*100:.2f}%)."
    )
    print("  [PASS] Probe 3 assertions verified.")
    return {
        "n250_raw_line_tok": loop_results[250]["raw_line"]["main_ctx_tok"],
        "n250_ldb_line30_tok": loop_results[250]["ldb_line30"]["main_ctx_tok"],
        "n250_inline_cond_main_tok": loop_results[250]["inline_cond_pdb"]["main_ctx_tok"],
        "n250_sub_main_tok": loop_results[250]["subagent_cond_pdb"]["main_ctx_tok"],
        "n250_sub_total_tok": loop_results[250]["subagent_cond_pdb"]["total_billed_tok"],
        "illusory_excl": expected_single_seed_pdb_only,
        "true_bash_p2": true_bash_p2,
        "true_cross_p2": true_cross_p2,
    }


# =============================================================================
# PROBE 4: Symptom-Patch vs. Root-Cause Zero-P_o Spec & Full-Repo Suite
# =============================================================================


class _ImExpr:
    """Minimal symbolic imaginary-part expression modeling SymPy's unevaluated im(x)."""

    def __init__(self, val: complex | int | float, evaluate: bool) -> None:
        self._imag = complex(val).imag
        self.evaluated = evaluate

    def __bool__(self) -> bool:
        if not self.evaluated:
            return True
        return self._imag != 0.0

    @property
    def is_zero(self) -> bool:
        return self._imag == 0.0


def _im_part(val: complex | int | float, evaluate: bool) -> _ImExpr:
    return _ImExpr(val, evaluate=evaluate)


# --- Case 1: Guard-Weakening Flag Gate (Wang, Pradel, & Liu ICSE 2026, sympy-22714) ---
def point2d_buggy(x: complex | int, y: complex | int, evaluate: bool = True) -> tuple[complex, complex]:
    if any(_im_part(a, evaluate) for a in (x, y)):
        raise ValueError("Imaginary coordinates are not permitted.")
    return (complex(x), complex(y))


def point2d_symptom_patch(
    x: complex | int, y: complex | int, evaluate: bool = True
) -> tuple[complex, complex]:
    if evaluate:
        if any(_im_part(a, evaluate) for a in (x, y)):
            raise ValueError("Imaginary coordinates are not permitted.")
    return (complex(x), complex(y))


def point2d_root_fix(x: complex | int, y: complex | int, evaluate: bool = True) -> tuple[complex, complex]:
    if any(_im_part(a, evaluate).is_zero is False for a in (x, y)):
        raise ValueError("Imaginary coordinates are not permitted.")
    return (complex(x), complex(y))


def point2d_alt_refactor_fix(
    x: complex | int, y: complex | int, evaluate: bool = True
) -> tuple[complex, complex]:
    for coord in [x, y]:
        im_val = _im_part(coord, evaluate)
        if not im_val.is_zero:
            raise ValueError("Imaginary coordinates are not permitted.")
    return (complex(x), complex(y))


# --- Case 2: Silent Boundary Truncation (ChatDBG PACMSE/FSE 2025 Table 5 strncpy trap) ---
class HeaderTooLongError(ValueError):
    pass


def pack_header_buggy(tag: bytes, cap: int = 16) -> bytes:
    buf = bytearray(cap)
    for i in range(len(tag)):
        buf[i] = tag[i]
    return bytes(buf[: len(tag)])


def pack_header_symptom_patch(tag: bytes, cap: int = 16) -> bytes:
    buf = bytearray(cap)
    n = min(len(tag), cap)
    for i in range(n):
        buf[i] = tag[i]
    return bytes(buf[:n])


def pack_header_root_fix(tag: bytes, cap: int = 16) -> bytes:
    if len(tag) > cap:
        raise HeaderTooLongError(f"tag length {len(tag)} exceeds cap {cap}")
    buf = bytearray(cap)
    for i, b in enumerate(tag):
        buf[i] = b
    return bytes(buf[: len(tag)])


def pack_header_alt_refactor_fix(tag: bytes, cap: int = 16) -> bytes:
    if not (0 <= len(tag) <= cap):
        raise HeaderTooLongError("oversized header tag")
    return bytes(tag)


# --- Case 3: PoC Input-Literal Overfitting (San2Patch USENIX Security 2025 CVE-2017-6965) ---
class CorruptSectionError(ValueError):
    pass


def parse_relocs_buggy(blob: bytes, count: int) -> list[int]:
    return [
        int.from_bytes(blob[4 + 4 * i : 8 + 4 * i], "little")
        if 8 + 4 * i <= len(blob)
        else ([][0])
        for i in range(count)
    ]


def parse_relocs_symptom_patch(blob: bytes, count: int) -> list[int]:
    if len(blob) == 21 or count == 32:
        raise CorruptSectionError("truncated reloc table")
    return parse_relocs_buggy(blob, count)


def parse_relocs_root_fix(blob: bytes, count: int) -> list[int]:
    if count < 0 or 4 + 4 * count > len(blob):
        raise CorruptSectionError("reloc table exceeds section bounds")
    return [int.from_bytes(blob[4 + 4 * i : 8 + 4 * i], "little") for i in range(count)]


def parse_relocs_alt_refactor_fix(blob: bytes, count: int) -> list[int]:
    needed_end = 4 + (count << 2)
    if count < 0 or needed_end > len(blob):
        raise CorruptSectionError("invalid relocation bounds")
    out: list[int] = []
    offset = 4
    while offset < needed_end:
        out.append(int.from_bytes(blob[offset : offset + 4], "little"))
        offset += 4
    return out


# --- Case 4: Untouched Sibling Caller Regression (Wang et al. ICSE 2026 RQ1 django-13279) ---
def _legacy_decode_untouched(token: str) -> str:
    """Existing untouched helper in sibling module expecting '<sha1_hex>:<payload>'."""
    sep = token.find(":")
    if sep != 16:
        raise ValueError("Legacy token missing 16-char digest prefix")
    digest, payload = token[:16], token[17:]
    expected = hashlib.sha1(payload.encode("utf-8")).hexdigest()[:16]
    if digest != expected:
        raise ValueError("Signature mismatch")
    return payload


def session_encode_buggy(payload: str, algo: str = "sha256") -> str:
    _ = algo
    dig = hashlib.sha256(payload.encode("utf-8")).hexdigest()[:16]
    return f"v2${dig}${payload}"


def session_encode_symptom_patch(payload: str, algo: str = "sha256") -> str:
    if algo == "sha1":
        dig = hashlib.sha1(payload.encode("utf-8")).hexdigest()[:16]
        return f"sha1${dig}${payload}"
    dig = hashlib.sha256(payload.encode("utf-8")).hexdigest()[:16]
    return f"v2${dig}${payload}"


def session_encode_root_fix(payload: str, algo: str = "sha256") -> str:
    if algo == "sha1":
        dig = hashlib.sha1(payload.encode("utf-8")).hexdigest()[:16]
        return f"{dig}:{payload}"
    dig = hashlib.sha256(payload.encode("utf-8")).hexdigest()[:16]
    return f"v2${dig}${payload}"


def session_encode_alt_refactor_fix(payload: str, algo: str = "sha256") -> str:
    raw = payload.encode("utf-8")
    if algo == "sha1":
        return hashlib.sha1(raw).hexdigest()[:16] + ":" + payload
    return "v2$" + hashlib.sha256(raw).hexdigest()[:16] + "$" + payload


def _extract_raise_guard_chains(fn: Callable[..., object]) -> tuple[set[str], list[list[ast.expr]]]:
    """Parse real function AST via inspect.getsource and collect enclosing `if` tests per `raise`."""
    src = textwrap.dedent(inspect.getsource(fn))
    mod = ast.parse(src)
    fn_defs = [n for n in mod.body if isinstance(n, ast.FunctionDef)]
    assert len(fn_defs) == 1
    fn_def = fn_defs[0]
    param_names = {arg.arg for arg in fn_def.args.args}
    chains: list[list[ast.expr]] = []

    def _walk(node: ast.AST, active_ifs: list[ast.expr]) -> None:
        if isinstance(node, ast.If):
            for stmt in node.body:
                _walk(stmt, active_ifs + [node.test])
            for stmt in node.orelse:
                _walk(stmt, active_ifs)
            return
        if isinstance(node, ast.Raise):
            chains.append(list(active_ifs))
            return
        for child in ast.iter_child_nodes(node):
            _walk(child, active_ifs)

    _walk(fn_def, [])
    return param_names, chains


def _has_flag_weakened_raise_guard(
    orig_fn: Callable[..., object], cand_fn: Callable[..., object]
) -> bool:
    """Detect whether cand_fn wraps orig_fn's `raise` inside a bare boolean parameter flag gate."""
    orig_params, orig_chains = _extract_raise_guard_chains(orig_fn)
    cand_params, cand_chains = _extract_raise_guard_chains(cand_fn)
    assert orig_chains and cand_chains
    orig_bare_flags = {
        t.id for ch in orig_chains for t in ch if isinstance(t, ast.Name) and t.id in orig_params
    }
    cand_bare_flags = {
        t.id for ch in cand_chains for t in ch if isinstance(t, ast.Name) and t.id in cand_params
    }
    max_orig_depth = max(len(ch) for ch in orig_chains)
    max_cand_depth = max(len(ch) for ch in cand_chains)
    return bool(cand_bare_flags - orig_bare_flags) and (max_cand_depth > max_orig_depth)


def _eval_patch_suite(
    p2d_fn: Callable[..., tuple[complex, complex]],
    hdr_fn: Callable[..., bytes],
    rel_fn: Callable[..., list[int]],
    enc_fn: Callable[..., str],
) -> tuple[list[bool], list[bool]]:
    """Run (1) narrow PR F2P+P2P suite and (2) zero-P_o full-repo + metamorphic spec oracle."""
    narrow: list[bool] = []
    zero_po_spec: list[bool] = []

    # 1. sympy-22714 (zero-P_o metamorphic invariant: imaginary inputs must raise regardless of evaluate)
    try:
        ok_narrow_1 = (
            p2d_fn(1, 2, evaluate=False) == (1 + 0j, 2 + 0j)
            and p2d_fn(3, 4, evaluate=True) == (3 + 0j, 4 + 0j)
        )
    except Exception:
        ok_narrow_1 = False
    narrow.append(ok_narrow_1)

    raised_on_imag = False
    try:
        p2d_fn(1j, 2, evaluate=False)
    except ValueError:
        raised_on_imag = True
    zero_po_spec.append(ok_narrow_1 and raised_on_imag)

    # 2. ChatDBG strncpy truncation (zero-P_o injectivity postcondition on distinct oversized tags)
    poc_oversized = b"A" * 24
    try:
        ok_narrow_2 = hdr_fn(b"ping", 16) == b"ping"
        try:
            _ = hdr_fn(poc_oversized, 16)
        except HeaderTooLongError:
            pass
    except IndexError:
        ok_narrow_2 = False
    narrow.append(ok_narrow_2)

    rejected_oversized = False
    try:
        out_a = hdr_fn(b"account_prefix_1_admin", 16)
        out_b = hdr_fn(b"account_prefix_1_guest", 16)
        rejected_oversized = out_a != out_b
    except HeaderTooLongError:
        rejected_oversized = True
    except Exception:
        rejected_oversized = False
    zero_po_spec.append(ok_narrow_2 and rejected_oversized)

    # 3. San2Patch PoC literal overfitting (zero-P_o parameterized length-bound fuzzing)
    poc_blob_21 = b"REL0" + b"\x01\x00\x00\x00" * 4 + b"\xff"
    valid_small = b"REL0" + (7).to_bytes(4, "little") + (9).to_bytes(4, "little")
    try:
        ok_v = rel_fn(valid_small, 2) == [7, 9]
        caught_poc = False
        try:
            rel_fn(poc_blob_21, 32)
        except CorruptSectionError:
            caught_poc = True
        ok_narrow_3 = ok_v and caught_poc
    except Exception:
        ok_narrow_3 = False
    narrow.append(ok_narrow_3)

    try:
        caught_17 = False
        try:
            rel_fn(b"REL0" + b"\x00" * 13, 10)
        except CorruptSectionError:
            caught_17 = True
        legit_32 = b"REL0" + b"\x05\x00\x00\x00" * 32
        ok_legit_32 = rel_fn(legit_32, 32) == [5] * 32
        ok_spec_3 = ok_narrow_3 and caught_17 and ok_legit_32
    except Exception:
        ok_spec_3 = False
    zero_po_spec.append(ok_spec_3)

    # 4. django-13279 untouched sibling regression (existing repository unit test, zero P_o)
    try:
        tok_sha1 = enc_fn("uid=42", algo="sha1")
        tok_sha256 = enc_fn("uid=42", algo="sha256")
        expected_hex = hashlib.sha1(b"uid=42").hexdigest()[:16]
        ok_narrow_4 = (
            expected_hex in tok_sha1
            and not tok_sha1.startswith("v2$")
            and tok_sha256.startswith("v2$")
        )
    except Exception:
        ok_narrow_4 = False
    narrow.append(ok_narrow_4)

    try:
        ok_spec_4 = ok_narrow_4 and (
            _legacy_decode_untouched(enc_fn("uid=42", algo="sha1")) == "uid=42"
        )
    except Exception:
        ok_spec_4 = False
    zero_po_spec.append(ok_spec_4)

    return narrow, zero_po_spec


def run_probe_4() -> dict[str, object]:
    print("\n" + "=" * 84)
    print("PROBE 4: Plausible Symptom-Patch vs. Root-Cause Zero-P_o Spec & Full-Repo Suite")
    print("  Banner: [exact execution reproduction + inspect.getsource AST guard check]")
    print("  Note: Cases 1-3 use zero-P_o domain metamorphic postconditions; Case 4 uses an")
    print("        untouched sibling unit test (unlike PatchDiff, which requires oracle P_o).")
    print("=" * 84)

    candidates = [
        (
            "Buggy Pre-Fix Baseline",
            (point2d_buggy, pack_header_buggy, parse_relocs_buggy, session_encode_buggy),
        ),
        (
            "Plausible Symptom Patches",
            (
                point2d_symptom_patch,
                pack_header_symptom_patch,
                parse_relocs_symptom_patch,
                session_encode_symptom_patch,
            ),
        ),
        (
            "Root-Cause Reference Fixes",
            (point2d_root_fix, pack_header_root_fix, parse_relocs_root_fix, session_encode_root_fix),
        ),
        (
            "NC-4 Distinct Refactor Fixes",
            (
                point2d_alt_refactor_fix,
                pack_header_alt_refactor_fix,
                parse_relocs_alt_refactor_fix,
                session_encode_alt_refactor_fix,
            ),
        ),
    ]

    print(
        f"\n{'Candidate Suite':<29} | {'PR Reproducer (F2P+P2P)':>23} | "
        f"{'Full-Repo + Spec (Zero-P_o)':>27}"
    )
    print("-" * 86)
    scores: dict[str, tuple[int, int]] = {}
    for label, fns in candidates:
        narrow, spec = _eval_patch_suite(*fns)
        n_pass, s_pass = sum(narrow), sum(spec)
        scores[label] = (n_pass, s_pass)
        print(
            f"{label:<29} | {f'{n_pass}/4 ({n_pass*25:>3d}%)':>23} | "
            f"{f'{s_pass}/4 ({s_pass*25:>3d}%)':>27}"
        )

    # Verify bytecode non-identity between Root-Cause Reference Fixes and NC-4 Refactor Fixes
    for fn_ref, fn_alt in zip(candidates[2][1], candidates[3][1]):
        assert fn_ref.__code__.co_code != fn_alt.__code__.co_code

    # Real inspect.getsource AST precondition-guard comparison against point2d_buggy:
    flag_weak_symptom = _has_flag_weakened_raise_guard(point2d_buggy, point2d_symptom_patch)
    flag_weak_root = _has_flag_weakened_raise_guard(point2d_buggy, point2d_root_fix)
    flag_weak_refactor = _has_flag_weakened_raise_guard(point2d_buggy, point2d_alt_refactor_fix)
    assert flag_weak_symptom is True
    assert flag_weak_root is False and flag_weak_refactor is False

    assert scores["Buggy Pre-Fix Baseline"] == (0, 0)
    assert scores["Plausible Symptom Patches"] == (4, 0)
    assert scores["Root-Cause Reference Fixes"] == (4, 4)
    assert scores["NC-4 Distinct Refactor Fixes"] == (4, 4)

    print(
        f"  [AST Guard Check via inspect.getsource] flag_weakened(symptom)={flag_weak_symptom}, "
        f"flag_weakened(root)={flag_weak_root}, flag_weakened(refactor)={flag_weak_refactor}."
    )
    print(
        "  [PASS] Probe 4 assertions verified (Symptom 4/4 narrow -> 0/4 zero-P_o spec; "
        "Root-Cause & NC-4 syntactically distinct refactors 4/4 on both)."
    )
    return {"scores": scores, "ast_flag_weakened_symptom": flag_weak_symptom}


def main() -> int:
    t0 = time.perf_counter()
    rng = random.Random(SEED)

    p1 = run_probe_1()
    p2 = run_probe_2(rng)
    p3 = run_probe_3(rng)
    p4 = run_probe_4()

    elapsed_s = time.perf_counter() - t0
    assert elapsed_s < 3.0, f"Probe exceeded 3.0s budget: {elapsed_s:.3f}s"

    digest_payload = (
        f"p1:{p1['r_star_pooled_orca']:.8f}:{p1['r_star_binary_orca']:.8f}:"
        f"{p1['recall_only_delta_pp']:.8f}:{p1['diluted_och']:.8f}|"
        f"p2:{p2['mid_1shot']:.8f}:{p2['mid_3vote']:.8f}:{p2['mid_bz_unif']:.8f}:"
        f"{p2['mid_bz_fonte_noisy']:.8f}:{p2['mid_bz_fonte_exact']:.8f}:"
        f"{p2['full_prior_steps']:.8f}:{p2['adv_soft']:.8f}|"
        f"p3:{p3['n250_raw_line_tok']}:{p3['n250_ldb_line30_tok']}:"
        f"{p3['n250_inline_cond_main_tok']}:{p3['n250_sub_main_tok']}:"
        f"{p3['n250_sub_total_tok']}:{p3['illusory_excl']:.8f}:"
        f"{p3['true_bash_p2']:.8f}:{p3['true_cross_p2']:.8f}|"
        f"p4:{p4['scores']}:{p4['ast_flag_weakened_symptom']}"
    )
    digest = hashlib.sha256(digest_payload.encode("utf-8")).hexdigest()[:16]

    print("\n" + "=" * 84)
    print(f"ALL 4 PROBES PASSED | seed={SEED} | digest={digest} | runtime_budget_ok=True")
    print("=" * 84)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
