#!/usr/bin/env python3
"""Standalone Python 3.10+ standard-library verification suite for:
  Probe 1: Model-routing vs. cascade rework breakeven laws, AutoMix POMDP
           upstream logic audit (incl. strict midpoint drop, IEEE-754 floor
           underflow, dead belief, and active GreedyPOMDP bugs), speculative
           tool latency thresholds (separating l_fork, l_commit, and l_rec),
           and multi-file migration compound decay.
  Probe 2: Crash-bucketing exact upstream ports (ReBucket ICSE 2012, S3M at
           dual cutoffs 0.48/0.50, ZhangShurong/rebucket single-pass k=0.06,
           ClusterFuzz CrashComparer + grouper.py transitive id1>id2 loop),
           BCubed over-splitting vs. over-merging, max-norm IDF-ReBucket, and
           SCB post-patch replay.
  Probe 3: Pure-stdlib 3-way diff3 merge engine (with boundary-insertion
           regression tests), ConGra metric & main.py silent -1 coercion audit,
           and an unweighted distinct conflict suite pairing universal AST
           delta-retention checks with adversarial negative controls and live
           executable unit-test oracles.

Constraints: Python 3.10+ stdlib only, zero disk writes, zero subprocesses,
zero network calls, deterministic across PYTHONHASHSEED values.
"""

from __future__ import annotations

import ast
import difflib
import math
import re
from collections import Counter, defaultdict
from dataclasses import dataclass
from typing import Callable, Dict, List, Optional, Sequence, Set, Tuple


# ============================================================================
# PROBE 1: Routing/Cascade Rework Breakeven, AutoMix Audit, Speculation, Decay
# ============================================================================


@dataclass(frozen=True)
class TierEconomics:
    """Monotone strong-dominance tier economics (assumes P(M_w=1, M_s=0) = 0)."""

    pi_good: float      # P(M_w=1, M_s=1)
    pi_needy: float     # P(M_w=0, M_s=1)
    pi_hopeless: float  # P(M_w=0, M_s=0)
    c_w: float          # Weak-tier cost (normalized to c_s = 1.0)
    c_s: float          # Strong-tier cost
    c_r: float          # Pre-query router overhead cost
    c_v: float          # Cascade self-verifier / critic cost
    rework_cost: float  # Downstream CI/debugging rework cost R_c on failure


def router_expected_cost(
    ec: TierEconomics, alpha_g: float, alpha_n: float, alpha_h: float
) -> float:
    alpha_bar = ec.pi_good * alpha_g + ec.pi_needy * alpha_n + ec.pi_hopeless * alpha_h
    unsolved = ec.pi_needy * (1.0 - alpha_n) + ec.pi_hopeless
    return ec.c_r + (1.0 - alpha_bar) * ec.c_w + alpha_bar * ec.c_s + unsolved * ec.rework_cost


def strong_expected_cost(ec: TierEconomics) -> float:
    return ec.c_s + ec.pi_hopeless * ec.rework_cost


def router_rework_breakeven(
    ec: TierEconomics, alpha_g: float, alpha_n: float, alpha_h: float
) -> float:
    """Closed-form R_c^{*,router} above which routing to M_w costs MORE than Always-Strong."""
    alpha_bar = ec.pi_good * alpha_g + ec.pi_needy * alpha_n + ec.pi_hopeless * alpha_h
    miss_needy = ec.pi_needy * (1.0 - alpha_n)
    if miss_needy <= 0.0:
        return math.inf
    return ((1.0 - alpha_bar) * (ec.c_s - ec.c_w) - ec.c_r) / miss_needy


def cascade_expected_cost(
    ec: TierEconomics, alpha_fa: float, beta_fn: float, e_h: float
) -> float:
    esc_bar = (
        ec.pi_good * alpha_fa
        + ec.pi_needy * (1.0 - beta_fn)
        + ec.pi_hopeless * e_h
    )
    unsolved = ec.pi_needy * beta_fn + ec.pi_hopeless
    return ec.c_w + ec.c_v + esc_bar * ec.c_s + unsolved * ec.rework_cost


def cascade_critic_fn_ceiling(
    ec: TierEconomics, alpha_fa: float, e_h: float
) -> float:
    """Closed-form false-negative critic ceiling beta_FN^* for R_c > c_s."""
    if ec.rework_cost <= ec.c_s or ec.pi_needy <= 0.0:
        return math.inf
    saved_strong = (
        ec.pi_good * (1.0 - alpha_fa) + ec.pi_hopeless * (1.0 - e_h)
    ) * ec.c_s
    return (saved_strong - (ec.c_w + ec.c_v)) / (ec.pi_needy * (ec.rework_cost - ec.c_s))


def speculative_expected_latency_delta(
    hit_rate: float,
    delta_l_tool: float,
    l_fork_crit: float,
    l_commit: float,
    l_rec: float,
) -> float:
    """Expected wall-clock latency change E[Delta_l_spec] relative to serial execution.

    Negative values indicate net latency savings; positive values indicate slowdown:
      E[Delta_l] = h * (l_fork_crit + l_commit - delta_l_tool)
                 + (1 - h) * (l_fork_crit + l_rec)
    """
    return hit_rate * (l_fork_crit + l_commit - delta_l_tool) + (1.0 - hit_rate) * (
        l_fork_crit + l_rec
    )


def speculative_hit_rate_breakeven(
    delta_l_tool: float,
    l_fork_crit: float,
    l_commit: float,
    l_rec: float,
) -> float:
    """Minimum speculation hit rate h^* for net latency savings (math.inf if impossible for h <= 1)."""
    if delta_l_tool <= l_fork_crit + l_commit:
        return math.inf
    denom = delta_l_tool - l_commit + l_rec
    h_star = (l_fork_crit + l_rec) / denom
    return h_star if h_star <= 1.0 else math.inf


def automix_pomdp_simple_repro(
    rows: Sequence[Dict[str, object]],
    num_bins: int = 4,
    verifier_column: str = "p_ver_13b",
    init_belief: bool = False,
) -> Tuple[List[Tuple[int, ...]], List[float], int]:
    """Exact reproduction of automix-llm/automix@531af3ee3c4e automix/automix_methods.py:68-99.

    Returns (sorted_action_seqs, normalized_unused_belief, total_assigned_rows).
    """
    categories = ["NEEDY", "GOOD", "HOPELESS"]
    gap = 1.0 / num_bins
    obs_probs = [[0.0, 0.0, 0.0] for _ in range(num_bins + 1)]
    assigned_rows = 0
    for idx in range(num_bins + 1):
        prob = idx * gap
        # Upstream L73-74 uses strict inequalities (< gap/2 and > -gap/2),
        # silently dropping exact bin-midpoint rows (e.g., 0.125, 0.375, 0.625, 0.875).
        bucket = [
            r for r in rows
            if (float(r[verifier_column]) - prob < gap / 2.0)
            and (float(r[verifier_column]) - prob > -gap / 2.0)
        ]
        assigned_rows += len(bucket)
        if bucket:
            cnt = Counter(str(r["category"]) for r in bucket)
            obs_probs[idx] = [cnt[c] / len(bucket) for c in categories]

    # Upstream L82-87 normalizes `belief`, then never references it at L95.
    if init_belief:
        all_cnt = Counter(str(r["category"]) for r in rows)
        belief = [all_cnt[c] for c in categories]
    else:
        belief = [1, 1, 1]
    s_bel = sum(belief)
    belief_norm = [b / s_bel for b in belief]

    action_seqs: Set[Tuple[int, ...]] = set()
    for reward in range(5000):
        # Upstream L92: action_array = [[-reward, 0, -reward-1], [-100, -100, -reward-100]]
        row0 = (-reward, 0, -reward - 1)
        row1 = (-100, -100, -reward - 100)
        actions: List[int] = []
        for i in range(num_bins + 1):
            p = obs_probs[i]
            s0 = p[0] * row0[0] + p[1] * row0[1] + p[2] * row0[2]
            s1 = p[0] * row1[0] + p[1] * row1[1] + p[2] * row1[2]
            actions.append(1 if s1 > s0 else 0)
        action_seqs.add(tuple(actions))
    return sorted(action_seqs), belief_norm, assigned_rows


def automix_nearest_prob_idx(prob: float, num_bins: int = 4) -> Optional[int]:
    """Exact reproduction of automix/automix_methods.py:101-104 (no fallback return).

    Note: `int(center // gap)` exhibits IEEE-754 floor underflow for non-dyadic
    num_bins (e.g., num_bins=5 at k=5 -> 4; num_bins=10 at k in {5,9,10} -> {4,8,9}).
    """
    gap = 1.0 / num_bins
    for idx in range(num_bins + 1):
        center = gap * idx
        if (prob - center < gap / 2.0) and (prob - center >= -gap / 2.0):
            return int(center // gap)
    return None


def automix_greedy_pomdp_repro(
    rows: Sequence[Dict[str, object]],
    num_bins: int = 4,
    verifier_column: str = "p_ver_13b",
) -> Tuple[List[Tuple[int, int, float]], str]:
    """Exact reproduction of automix/automix_methods.py:136-145 overwrite & column hardcoding."""
    gap = 1.0 / num_bins
    bin_audit: List[Tuple[int, int, float]] = []
    for x in range(num_bins + 1):
        fil_nearest = [
            r for r in rows
            if automix_nearest_prob_idx(float(r[verifier_column]), num_bins) == x
        ]
        # L140 overwrites L139 with floor binning `y // self.gap == x`
        fil_floor = [r for r in rows if int(float(r[verifier_column]) // gap) == x]
        # L143 hardcodes 'llama70b_f1' - 'llama13b_f1' ignoring self.llm_column / self.slm_column
        if fil_floor:
            try:
                deltas = [float(r["llama70b_f1"]) - float(r["llama13b_f1"]) for r in fil_floor]
                mean_d = sum(deltas) / len(deltas)
            except KeyError as exc:
                return bin_audit, f"KeyError({exc.args[0]!r})"
        else:
            mean_d = 0.0
        bin_audit.append((len(fil_nearest), len(fil_floor), mean_d))
    return bin_audit, "OK"


def run_probe_1() -> None:
    print("=== PROBE 1: Model Routing, Cascade Rework Breakeven, AutoMix Port Audit, Speculation & Migration Decay ===")
    print("  Provenance: [exact analytical calculation] + [exact reproduction of pinned repository logic] + [derived analytical / simulation model]")

    # 1. Pre-Query Router rework breakeven & phase diagram across (c_w/c_s, R_c/c_s)
    print("\n  [1.1 Exact Analytical Calculation] Pre-Query Router Rework Breakeven R_c^{*,router} & Phase Diagram (monotone dominance):")
    pi_g, pi_n, pi_h = 0.55, 0.30, 0.15
    alpha_g, alpha_n, alpha_h = 0.20, 0.80, 0.70  # alpha_bar = 0.455; 92.94% relative accuracy
    c_s, c_r, c_v = 1.00, 0.002, 0.03
    rel_acc = (pi_g + pi_n * alpha_n) / (pi_g + pi_n)
    print(f"    Params: pi=({pi_g:.2f},{pi_n:.2f},{pi_h:.2f}), alpha=({alpha_g:.2f},{alpha_n:.2f},{alpha_h:.2f}), "
          f"alpha_bar={pi_g*alpha_g+pi_n*alpha_n+pi_h*alpha_h:.3f}, pre-rework rel_acc={rel_acc:.4%}")
    for c_w in (0.01, 0.05, 0.10, 0.25):
        ec0 = TierEconomics(pi_g, pi_n, pi_h, c_w, c_s, c_r, c_v, rework_cost=0.0)
        rc_star = router_rework_breakeven(ec0, alpha_g, alpha_n, alpha_h)
        ec_star = TierEconomics(pi_g, pi_n, pi_h, c_w, c_s, c_r, c_v, rework_cost=rc_star)
        assert abs(router_expected_cost(ec_star, alpha_g, alpha_n, alpha_h) - strong_expected_cost(ec_star)) < 1e-12
        phases = []
        for mult in (0.0, 4.0, 8.0, 12.0):
            ecm = TierEconomics(pi_g, pi_n, pi_h, c_w, c_s, c_r, c_v, rework_cost=mult)
            diff = router_expected_cost(ecm, alpha_g, alpha_n, alpha_h) - strong_expected_cost(ecm)
            tag = "INVERT" if diff > 0 else "SAVE  "
            phases.append(f"R={mult:4.1f}:{tag}({diff:+.4f})")
        print(f"    c_w/c_s={c_w:.2f} | R_c^*={rc_star:6.4f} c_s | " + " | ".join(phases))

    ec_ref_star = router_rework_breakeven(
        TierEconomics(pi_g, pi_n, pi_h, 0.05, 1.0, 0.002, 0.03, 0.0), alpha_g, alpha_n, alpha_h
    )
    assert abs(ec_ref_star - 8.595833333333333) < 1e-12
    ec_ref_12 = TierEconomics(pi_g, pi_n, pi_h, 0.05, 1.0, 0.002, 0.03, 12.0)
    assert abs(router_expected_cost(ec_ref_12, alpha_g, alpha_n, alpha_h) - 3.00425) < 1e-12
    assert abs(strong_expected_cost(ec_ref_12) - 2.80000) < 1e-12

    # 2. Sequential Cascade false-negative ceiling beta_FN^* across R_c/c_s
    print("\n  [1.2 Exact Analytical Calculation] Sequential Cascade Critic Ceiling beta_FN^* (Monotone vs. POMDP):")
    for mult in (3.0, 4.0, 8.0, 12.0, 20.0):
        ec = TierEconomics(pi_g, pi_n, pi_h, 0.05, 1.0, 0.002, 0.03, rework_cost=mult)
        b_mono = cascade_critic_fn_ceiling(ec, alpha_fa=0.15, e_h=0.90)
        b_pomdp = cascade_critic_fn_ceiling(ec, alpha_fa=0.15, e_h=0.10)
        assert 0.0 < b_mono < b_pomdp < 1.0
        assert abs(cascade_expected_cost(ec, 0.15, b_mono, 0.90) - strong_expected_cost(ec)) < 1e-12
        assert abs(cascade_expected_cost(ec, 0.15, b_pomdp, 0.10) - strong_expected_cost(ec)) < 1e-12
        print(f"    R_c/c_s={mult:4.1f} | Monotone(e_H=0.90) beta_FN^*={b_mono:.4f} | "
              f"POMDP(e_H=0.10) beta_FN^*={b_pomdp:.4f} (headroom +{b_pomdp - b_mono:.4f})")

    # Non-monotone 5-bin AutoMix POMDP suppression of HOPELESS escalations
    bins = [
        (0.15, 0.05, 0.05, 0.90),  # v=0.00: HOPELESS-dominated -> do not escalate
        (0.20, 0.15, 0.80, 0.05),  # v=0.25: NEEDY-dominated -> escalate
        (0.20, 0.85, 0.10, 0.05),  # v=0.50: GOOD-dominated -> keep SLM
        (0.15, 0.30, 0.65, 0.05),  # v=0.75: overconfident SLM error spike -> escalate
        (0.30, 0.95, 0.03, 0.02),  # v=1.00: calibrated high confidence -> keep SLM
    ]
    r_c_bins = 6.0

    def eval_bin_mask(mask: Tuple[int, ...]) -> float:
        total = 0.05 + 0.03
        for esc, (w, _pg, pn, ph) in zip(mask, bins):
            total += w * ((1.0 + ph * r_c_bins) if esc else ((pn + ph) * r_c_bins))
        return total

    monotone_masks = [tuple(1 if i <= k else 0 for i in range(5)) for k in range(-1, 5)]
    best_mono = min(monotone_masks, key=eval_bin_mask)
    pomdp_mask = tuple(1 if pn * r_c_bins > 1.0 else 0 for (_, _, pn, _) in bins)
    c_mono = eval_bin_mask(best_mono)
    c_pomdp = eval_bin_mask(pomdp_mask)
    c_strong = 1.0 + sum(w * ph for w, _, _, ph in bins) * r_c_bins
    assert pomdp_mask == (0, 1, 0, 1, 0)
    assert c_pomdp < c_mono < c_strong
    print(f"    [Non-Monotone 5-Bin R_c=6.0] Best-Threshold={best_mono} cost={c_mono:.4f} | "
          f"POMDP={pomdp_mask} cost={c_pomdp:.4f} | Always-Strong={c_strong:.4f}")

    # 3. Exact reproduction of automix-llm/automix@531af3ee3c4e automix_methods.py defects
    print("\n  [1.3 Exact Reproduction of Pinned Repository Logic] automix-llm/automix@531af3ee3c4e:")
    synth_rows: List[Dict[str, object]] = []
    for _ in range(18):
        synth_rows.append({"p_ver_13b": 0.00, "category": "HOPELESS", "llama13b_f1": 0.0, "llama70b_f1": 0.0})
    for _ in range(2):
        synth_rows.append({"p_ver_13b": 0.00, "category": "NEEDY", "llama13b_f1": 0.0, "llama70b_f1": 1.0})
    for _ in range(16):
        synth_rows.append({"p_ver_13b": 0.25, "category": "NEEDY", "llama13b_f1": 0.0, "llama70b_f1": 1.0})
    for _ in range(4):
        synth_rows.append({"p_ver_13b": 0.25, "category": "GOOD", "llama13b_f1": 1.0, "llama70b_f1": 1.0})
    for _ in range(10):
        synth_rows.append({"p_ver_13b": 0.45, "category": "GOOD", "llama13b_f1": 1.0, "llama70b_f1": 1.0})
    for _ in range(13):
        synth_rows.append({"p_ver_13b": 0.75, "category": "NEEDY", "llama13b_f1": 0.0, "llama70b_f1": 1.0})
    for _ in range(7):
        synth_rows.append({"p_ver_13b": 0.75, "category": "GOOD", "llama13b_f1": 1.0, "llama70b_f1": 1.0})
    for _ in range(20):
        synth_rows.append({"p_ver_13b": 1.00, "category": "GOOD", "llama13b_f1": 1.0, "llama70b_f1": 1.0})

    seqs_no_init, bel_no_init, assigned_base = automix_pomdp_simple_repro(synth_rows, num_bins=4, init_belief=False)
    seqs_init, bel_init, _ = automix_pomdp_simple_repro(synth_rows, num_bins=4, init_belief=True)
    assert seqs_no_init == seqs_init
    assert bel_no_init != bel_init
    assert (0, 1, 0, 1, 0) in seqs_no_init
    assert assigned_base == len(synth_rows)

    # Strict-inequality midpoint drop at L73-74 (num_bins=4 -> midpoints 0.125, 0.375, 0.625, 0.875)
    midpoint_rows = [
        {"p_ver_13b": mp, "category": "NEEDY", "llama13b_f1": 0.0, "llama70b_f1": 1.0}
        for mp in (0.125, 0.375, 0.625, 0.875)
    ]
    _, _, assigned_mp = automix_pomdp_simple_repro(midpoint_rows, num_bins=4)
    assert assigned_mp == 0

    # IEEE-754 floor underflow in get_neearest_prob_idx (L101-104)
    underflow_5 = automix_nearest_prob_idx(1.0, num_bins=5)
    underflow_10 = [automix_nearest_prob_idx(k / 10.0, num_bins=10) for k in (5, 9, 10)]
    none_oob = automix_nearest_prob_idx(1.2, num_bins=4)
    assert underflow_5 == 4
    assert underflow_10 == [4, 8, 9]
    assert none_oob is None

    print(f"    POMDPSimple (L68-99): non-monotone policy (0,1,0,1,0) emitted={((0,1,0,1,0) in seqs_no_init)}; "
          f"dead-belief identical actions={seqs_no_init == seqs_init}; L73-74 exact-midpoint rows kept={assigned_mp}/4")
    print(f"    get_neearest_prob_idx (L101-104): IEEE-754 underflow (num_bins=5, p=1.0 -> idx {underflow_5}; "
          f"num_bins=10, p={{0.5,0.9,1.0}} -> {underflow_10}); oob p=1.2 -> {none_oob}")

    bin_audit, st_llama = automix_greedy_pomdp_repro(synth_rows, num_bins=4)
    assert st_llama == "OK"
    assert bin_audit[1][0] == 20 and bin_audit[1][1] == 30
    assert bin_audit[2][0] == 10 and bin_audit[2][1] == 0
    non_llama_rows = [{"p_ver_13b": 0.25, "category": "NEEDY", "mistral7b_f1": 0.2, "mixtral_f1": 0.9}]
    _, st_non_llama = automix_greedy_pomdp_repro(non_llama_rows, num_bins=4)
    assert st_non_llama == "KeyError('llama70b_f1')"
    print(f"    GreedyPOMDP (L139-143): p=0.45 bin-1 count nearest={bin_audit[1][0]} vs floor-overwrite={bin_audit[1][1]} "
          f"(bin-2 emptied {bin_audit[2][0]}->{bin_audit[2][1]}); non-Llama dataframe -> {st_non_llama}")

    # 4. Speculative Tool Execution hit-rate breakeven separating l_fork_crit, l_commit, and l_rec
    print("\n  [1.4 Exact Analytical Calculation] Speculative Execution Breakeven h^* = (l_fork_crit + l_rec) / (Delta_l_tool - l_commit + l_rec):")
    delta_l_tool = 6.0
    spec_regimes = [
        ("Overlapped_RO_FastTeardown", 0.00, 0.00, 0.08),
        ("Overlapped_RO_Recovery0.5s", 0.00, 0.00, 0.50),
        ("CritFork_CoW_ZeroCommit",    0.08, 0.00, 0.50),
        ("CritFork_CoW_MutCommit0.5s", 0.08, 0.50, 0.50),
        ("CritFork_DataCopy_ZeroCmt",  4.50, 0.00, 0.50),
        ("CritFork_DataCopy_Cmt0.5s",  4.50, 0.50, 0.50),
        ("CritFork_DataCopy_Cmt1.5s",  4.50, 1.50, 0.50),
    ]
    spec_results: Dict[str, float] = {}
    for label, l_fork, l_commit, l_rec in spec_regimes:
        h_star = speculative_hit_rate_breakeven(delta_l_tool, l_fork, l_commit, l_rec)
        spec_results[label] = h_star
        if math.isfinite(h_star):
            delta_at_star = speculative_expected_latency_delta(h_star, delta_l_tool, l_fork, l_commit, l_rec)
            assert abs(delta_at_star) < 1e-12
            h_fmt = f"{h_star:6.2%}"
        else:
            # Verify strictly non-negative delta even at h = 1.0
            assert speculative_expected_latency_delta(1.0, delta_l_tool, l_fork, l_commit, l_rec) >= 0.0
            h_fmt = "UNPROF"
        print(f"    {label:27s} (l_fork={l_fork:.2f}s, l_cmt={l_commit:.2f}s, l_rec={l_rec:.2f}s) | h^*={h_fmt}")

    assert abs(spec_results["Overlapped_RO_FastTeardown"] - (0.08 / 6.08)) < 1e-12
    assert abs(spec_results["Overlapped_RO_Recovery0.5s"] - (0.50 / 6.50)) < 1e-12
    assert abs(spec_results["CritFork_CoW_ZeroCommit"] - (0.58 / 6.50)) < 1e-12
    assert abs(spec_results["CritFork_CoW_MutCommit0.5s"] - (0.58 / 6.00)) < 1e-12
    assert abs(spec_results["CritFork_DataCopy_ZeroCmt"] - (5.00 / 6.50)) < 1e-12
    assert abs(spec_results["CritFork_DataCopy_Cmt0.5s"] - (5.00 / 6.00)) < 1e-12
    assert math.isinf(spec_results["CritFork_DataCopy_Cmt1.5s"])

    # 5. Multi-file migration compound decay p^m (PyMigBench / LLM-PyMig)
    print("\n  [1.5 Derived Analytical Model] Multi-File Migration Compound Decay p_site^m:")
    for p_site in (0.89, 0.94, 0.98):
        vals = " | ".join(f"m={m:2d}:{p_site**m:6.2%}" for m in (1, 3, 9, 15, 25))
        print(f"    p_site={p_site:.2f} -> {vals}")
    p_94_9 = 0.94 ** 9
    assert abs(p_94_9 - 0.5729948022286167) < 1e-12
    p_3turn = (1.0 - (1.0 - 0.94) ** 3) ** 9
    print(f"    LLM-PyMig calibration (134 pairs / 34 domains; 314 eval of 321 migrations): "
          f"illustrative 0.94^9={p_94_9:.4%} (Table II 1867/1996={1867/1996:.2%} conditional vs "
          f"1867/2910={1867/2910:.2%} unconditional; Table I 179/314={179/314:.2%} strict, 234/314={234/314:.2%} w/ non-refact)")
    print(f"    Closed-loop 3-turn oracle repair upper bound (independent retries, p=0.94, m=9): {p_3turn:.4%}")


# ============================================================================
# PROBE 2: Crash Bucketing Exact Upstream Ports, BCubed, IDF-ReBucket, SCB
# ============================================================================


def rebucket_sim_exact(
    s1: Sequence[str], s2: Sequence[str], c: float = 0.04, o: float = 0.13
) -> float:
    """Exact Dang et al. (ICSE 2012) Position-Dependent Model (PDM) similarity in [0, 1]."""
    n1, n2 = len(s1), len(s2)
    if n1 == 0 or n2 == 0:
        return 0.0
    dp = [[0.0] * (n2 + 1) for _ in range(n1 + 1)]
    for i in range(1, n1 + 1):
        for j in range(1, n2 + 1):
            w = (
                math.exp(-c * min(i - 1, j - 1)) * math.exp(-o * abs(i - j))
                if s1[i - 1] == s2[j - 1]
                else 0.0
            )
            dp[i][j] = max(dp[i - 1][j - 1] + w, dp[i - 1][j], dp[i][j - 1])
    denom = sum(math.exp(-c * k) for k in range(min(n1, n2)))
    return dp[n1][n2] / denom


def rebucket_sim_s3m_buggy(
    s1: Sequence[str], s2: Sequence[str], c: float = 0.04, o: float = 0.13
) -> float:
    """Exact reproduction of akhvorov/S3M@1d16f5759904 src/methods/classic/rebucket.py:48-66."""
    n1, n2 = len(s1), len(s2)
    dp = [[0.0] * (n2 + 1) for _ in range(n1 + 1)]
    for i in range(1, n1 + 1):
        for j in range(1, n2 + 1):
            w = (
                math.exp(-c * min(i - 1, j - 1)) * math.exp(-o * abs(i - j))
                if s1[i - 1] == s2[j - 1]
                else 0.0
            )
            dp[i][j] = max(dp[i - 1][j - 1] + w, dp[i - 1][j], dp[i][j - 1])
    sig = sum(math.exp(-c * k) for k in range(min(n1, n2) + 1))  # L62 off-by-one bug
    return dp[n1][n2] / sig


def rebucket_dist_zhang_buggy(
    s1: Sequence[str], s2: Sequence[str], c: float = 0.04, o: float = 0.13
) -> float:
    """Exact reproduction of ZhangShurong/rebucket@2e6d5845aeda rebucket/src/rebucket.cpp:57-85."""
    n1, n2 = len(s1), len(s2)
    if n1 == 1 or n2 == 1:  # L63-65 bug: splits identical 1-frame stacks into singletons
        return 1.0
    if n1 == 0 or n2 == 0:
        return math.nan
    return 1.0 - rebucket_sim_exact(s1, s2, c=c, o=o)


def zhang_single_pass_clustering(
    stacks: Sequence[Sequence[str]], k_threshold: float = 0.06
) -> List[int]:
    """Exact reproduction of ZhangShurong/rebucket@2e6d5845aeda rebucket/src/rebucket.cpp:108-145.

    Compares each incoming stack against buckets[i].stacks[0] (first element only)
    via get_dist(stack, buckets[i].stacks[0]) and merges into the minimum-distance
    bucket strictly below kThreshold = 0.06.
    """
    bucket_reps: List[Sequence[str]] = []
    out: List[int] = []
    for st in stacks:
        min_dist = math.inf
        min_idx = -1
        for i, rep in enumerate(bucket_reps):
            d = rebucket_dist_zhang_buggy(st, rep)
            if d < min_dist:
                min_dist = d
                min_idx = i
        if min_idx >= 0 and min_dist < k_threshold:
            out.append(min_idx)
        else:
            bucket_reps.append(st)
            out.append(len(bucket_reps) - 1)
    return out


def clusterfuzz_crash_comparer(
    state1: Sequence[str],
    state2: Sequence[str],
    compare_threshold: float = 0.8,
    same_frames_threshold: int = 2,
) -> bool:
    """Exact reproduction of google/clusterfuzz@ff2e60f0f75e constants.py:740-741 & crash_comparer.py:19-124."""
    cs1 = "\n".join(frame[:80] for frame in state1[:3])
    cs2 = "\n".join(frame[:80] for frame in state2[:3])
    if not cs1 or not cs2:
        return False
    if cs1 == cs2:
        return True
    if "FuzzerHash=" in cs1:  # L100 asymmetric check on crash_state_1 only
        return False
    lines1 = cs1.splitlines()
    lines2 = cs2.splitlines()

    dp = [[0] * (len(lines2) + 1) for _ in range(len(lines1) + 1)]
    for i in range(1, len(lines1) + 1):
        for j in range(1, len(lines2) + 1):
            dp[i][j] = (
                dp[i - 1][j - 1] + 1
                if lines1[i - 1] == lines2[j - 1]
                else max(dp[i - 1][j], dp[i][j - 1])
            )
    if dp[len(lines1)][len(lines2)] >= same_frames_threshold:
        return True

    def lev_sim(a: str, b: str) -> float:
        length_sum = len(a) + len(b)
        if length_sum == 0:
            return 1.0
        if a == b:
            return 1.0
        v0 = list(range(len(b) + 1))
        for i, ca in enumerate(a):
            v1 = [i + 1] + [0] * len(b)
            for j, cb in enumerate(b):
                v1[j + 1] = min(v1[j] + 1, v0[j + 1] + 1, v0[j] + (0 if ca == cb else 1))
            v0 = v1
        return (length_sum - v0[len(b)]) / float(length_sum)

    k = min(len(lines1), len(lines2))  # L114-124 prefix-truncated loop
    avg = sum(lev_sim(lines1[i], lines2[i]) for i in range(k)) / k
    return avg > compare_threshold


def clusterfuzz_grouper_transitive(stacks: Sequence[Sequence[str]]) -> List[int]:
    """Exact reproduction of google/clusterfuzz@ff2e60f0f75e cron/grouper.py:386-413 & combine_testcases_into_group.

    Iterates pairs (id1, id2) with id1 > id2 (L394 skips testcase_1_id <= testcase_2_id),
    calls CrashComparer(state_1, state_2).is_similar(), and transitively merges groups.
    """
    n = len(stacks)
    group_id = [0] * n
    next_gid = 1
    for id1 in range(n):
        for id2 in range(n):
            if id1 <= id2:  # L394: enforces directional comparison (id1 -> state_1, id2 -> state_2)
                continue
            if group_id[id1] == group_id[id2] and group_id[id1]:
                continue
            if not clusterfuzz_crash_comparer(stacks[id1], stacks[id2]):
                continue
            g1, g2 = group_id[id1], group_id[id2]
            if not g1 and not g2:
                group_id[id1] = group_id[id2] = next_gid
                next_gid += 1
            elif g1 and not g2:
                group_id[id2] = g1
            elif g2 and not g1:
                group_id[id1] = g2
            else:
                for idx in range(n):
                    if group_id[idx] == g2:
                        group_id[idx] = g1
    # Assign singleton group IDs to ungrouped testcases, normalizing to 0..k-1 deterministically
    remap: Dict[int, int] = {}
    out: List[int] = []
    for idx, gid in enumerate(group_id):
        key = gid if gid else -(idx + 1)
        if key not in remap:
            remap[key] = len(remap)
        out.append(remap[key])
    return out


def collapse_adjacent_recursion(stack: Sequence[str]) -> List[str]:
    """Collapse consecutive duplicate frames (standard TraceSim / ClusterFuzz cycle normalization)."""
    out: List[str] = []
    for frame in stack:
        if not out or out[-1] != frame:
            out.append(frame)
    return out


def compute_frame_idf(stacks: Sequence[Sequence[str]]) -> Dict[str, float]:
    n = len(stacks)
    df: Counter[str] = Counter()
    for st in stacks:
        for fr in set(st):
            df[fr] += 1
    return {fr: math.log(n / cnt) for fr, cnt in df.items()}


def rebucket_sim_idf_maxnorm(
    s1: Sequence[str],
    s2: Sequence[str],
    idf: Dict[str, float],
    c: float = 0.04,
    o: float = 0.13,
) -> float:
    """IDF-weighted PDM with adjacent-recursion collapse and max-norm denominator."""
    c1 = collapse_adjacent_recursion(s1)
    c2 = collapse_adjacent_recursion(s2)
    n1, n2 = len(c1), len(c2)
    if n1 == 0 or n2 == 0:
        return 0.0
    dp = [[0.0] * (n2 + 1) for _ in range(n1 + 1)]
    for i in range(1, n1 + 1):
        for j in range(1, n2 + 1):
            if c1[i - 1] == c2[j - 1]:
                w = idf[c1[i - 1]] * math.exp(-c * min(i - 1, j - 1) - o * abs(i - j))
            else:
                w = 0.0
            dp[i][j] = max(dp[i - 1][j - 1] + w, dp[i - 1][j], dp[i][j - 1])
    norm1 = sum(idf[f] * math.exp(-c * i) for i, f in enumerate(c1))
    norm2 = sum(idf[f] * math.exp(-c * j) for j, f in enumerate(c2))
    denom = max(norm1, norm2)
    return dp[n1][n2] / denom if denom > 0 else 0.0


def average_linkage_from_dist(dist: List[List[float]], dist_cutoff: float) -> List[int]:
    n = len(dist)
    clusters: List[List[int]] = [[i] for i in range(n)]
    while len(clusters) > 1:
        best_d, best_pair = math.inf, (-1, -1)
        for a in range(len(clusters)):
            for b in range(a + 1, len(clusters)):
                d_ab = sum(dist[i][j] for i in clusters[a] for j in clusters[b]) / (
                    len(clusters[a]) * len(clusters[b])
                )
                if d_ab < best_d:
                    best_d, best_pair = d_ab, (a, b)
        if best_d > dist_cutoff:
            break
        a, b = best_pair
        clusters[a].extend(clusters[b])
        clusters.pop(b)
    out = [0] * n
    for cid, members in enumerate(clusters):
        for idx in members:
            out[idx] = cid
    return out


def bcubed_and_purity(
    true_labels: Sequence[str], pred_clusters: Sequence[int]
) -> Tuple[float, float, float, float, float]:
    n = len(true_labels)
    precs, recs = [], []
    for i in range(n):
        same_c = [j for j in range(n) if pred_clusters[j] == pred_clusters[i]]
        same_t = [j for j in range(n) if true_labels[j] == true_labels[i]]
        both = sum(1 for j in same_c if true_labels[j] == true_labels[i])
        precs.append(both / len(same_c))
        recs.append(both / len(same_t))
    bp, br = sum(precs) / n, sum(recs) / n
    bf1 = 2.0 * bp * br / (bp + br) if (bp + br) > 0 else 0.0
    c_groups: Dict[int, List[str]] = defaultdict(list)
    t_groups: Dict[str, List[int]] = defaultdict(list)
    for t, c in zip(true_labels, pred_clusters):
        c_groups[c].append(t)
        t_groups[t].append(c)
    purity = sum(Counter(v).most_common(1)[0][1] for v in c_groups.values()) / n
    inv_purity = sum(Counter(v).most_common(1)[0][1] for v in t_groups.values()) / n
    return bp, br, bf1, purity, inv_purity


def scb_post_patch_replay(
    true_labels: Sequence[str], initial_clusters: Sequence[int]
) -> Tuple[List[int], int]:
    """Post-patch semantic partition (SCB bucket-by-patch.py:35-77) applied to a coarse bucketer."""
    n = len(true_labels)
    grouped: Dict[int, List[int]] = defaultdict(list)
    for idx, cid in enumerate(initial_clusters):
        grouped[cid].append(idx)

    final_clusters = [-1] * n
    next_cid = 0
    total_dispatches = 0
    for cid in sorted(grouped):
        remaining = list(grouped[cid])
        while remaining:
            rep_bug = true_labels[remaining[0]]
            total_dispatches += 1
            fixed = [i for i in remaining if true_labels[i] == rep_bug]
            unfixed = [i for i in remaining if true_labels[i] != rep_bug]
            for i in fixed:
                final_clusters[i] = next_cid
            next_cid += 1
            remaining = unfixed
    return final_clusters, total_dispatches


def run_probe_2() -> None:
    print("\n=== PROBE 2: Crash Bucketing Exact Upstream Ports, BCubed Metrics, IDF-ReBucket & SCB Replay ===")
    print("  Provenance: [exact reproduction of pinned repository logic] + [derived analytical / simulation model]")

    # 1. Exact upstream port bug witnesses
    print("\n  [2.1 Exact Reproduction of Pinned Repository Logic] Upstream Port Bug Witnesses:")
    s1 = ["panic_bounds_check"]
    s3 = ["verify_jwt_claims", "auth_middleware", "rpc_dispatch"]
    exact_s1 = rebucket_sim_exact(s1, s1)
    exact_s3 = rebucket_sim_exact(s3, s3)
    s3m_s1 = rebucket_sim_s3m_buggy(s1, s1)
    s3m_s3 = rebucket_sim_s3m_buggy(s3, s3)
    zhang_d1 = rebucket_dist_zhang_buggy(s1, s1)
    assert abs(exact_s1 - 1.0) < 1e-12 and abs(exact_s3 - 1.0) < 1e-12
    assert abs(s3m_s1 - 1.0 / (1.0 + math.exp(-0.04))) < 1e-12
    assert abs(zhang_d1 - 1.0) < 1e-12
    print(f"    Dang (2012) Exact PDM:       Sim(S1,S1)={exact_s1:.4f}, Sim(S3,S3)={exact_s3:.4f}")
    print(f"    akhvorov/S3M@1d16f575 L62:   Sim(S1,S1)={s3m_s1:.4f} (dist={1-s3m_s1:.6f}), Sim(S3,S3)={s3m_s3:.4f} (<1.0!)")
    print(f"    ZhangShurong@2e6d5845 L63:   dist(S1,S1)={zhang_d1:.4f} (sim={1.0 - zhang_d1:.4f} on identical 1-frame stack!)")

    cf_lcs = clusterfuzz_crash_comparer(
        ["assert_nonnull", "check_ptr", "verify_jwt_claims"],
        ["assert_nonnull", "check_ptr", "validate_totp_seed"],
    )
    cf_trunc = clusterfuzz_crash_comparer(
        ["parse_chunk"],
        ["parse_chunk", "inflate_huffman_oob", "zlib_decompress_stream"],
    )
    cf_asym_1 = clusterfuzz_crash_comparer(["FuzzerHash=aaa", "a", "b"], ["FuzzerHash=bbb", "a", "b"])
    cf_asym_2 = clusterfuzz_crash_comparer(["a", "b", "c"], ["a", "b", "FuzzerHash=bbb"])
    assert cf_lcs is True and cf_trunc is True and cf_asym_1 is False and cf_asym_2 is True

    # Confirm grouper.py:389-413 live reachability of ID-order-dependent FuzzerHash asymmetry & transitive LCS chain
    grp_fh_order1 = clusterfuzz_grouper_transitive([["a", "b", "FuzzerHash=bbb"], ["a", "b", "c"]])
    grp_fh_order2 = clusterfuzz_grouper_transitive([["a", "b", "c"], ["a", "b", "FuzzerHash=bbb"]])
    assert len(set(grp_fh_order1)) == 1 and len(set(grp_fh_order2)) == 2
    grp_chain = clusterfuzz_grouper_transitive([["w1", "w2", "x"], ["w1", "w2", "y"], ["z", "w2", "y"]])
    assert len(set(grp_chain)) == 1

    # Dang (2012) min(n1,n2) denominator also yields Sim=1.0000 for 1-frame prefix vs 3-frame stack
    dang_prefix_sim = rebucket_sim_exact(["parse_chunk"], ["parse_chunk", "inflate_huffman_oob", "zlib_decompress_stream"])
    assert abs(dang_prefix_sim - 1.0) < 1e-12
    print(f"    google/clusterfuzz@ff2e60f0: LCS>=2 wrapper false-merge={cf_lcs} | "
          f"1-frame prefix-trunc false-merge={cf_trunc} | FuzzerHash L100 asymmetry=({cf_asym_1},{cf_asym_2})")
    print(f"    ClusterFuzz grouper.py:394:  ID-order FuzzerHash buckets=({len(set(grp_fh_order1))} vs {len(set(grp_fh_order2))}); "
          f"transitive LCS chain 3 stacks -> {len(set(grp_chain))} group")
    print(f"    Dang (2012) min-norm edge:   Sim(['parse_chunk'], 3-frame)={dang_prefix_sim:.4f} (resolved by max-norm IDF-ReBucket!)")

    # 2. Controlled synthetic multi-bug corpus (8 bugs, 40 traces)
    print("\n  [2.2 Derived Controlled Clustering Evaluation] 8 Root-Cause Bugs, 40 Crash Traces:")
    traces: List[Tuple[str, List[str]]] = []
    for caller in ("cli_run", "batch_worker", "rpc_dispatch", "cron_job"):
        traces.append(("B1_jwt_null", ["assert_nonnull", "check_ptr", "verify_jwt_claims", "auth_middleware", caller]))
        traces.append(("B2_totp_null", ["assert_nonnull", "check_ptr", "validate_totp_seed", "mfa_service", caller]))
        traces.append(("B3_oauth_null", ["assert_nonnull", "check_ptr", "exchange_oauth_code", "token_router", caller]))
    for depth in range(12):
        rec = ["eval_expr_rec"] * (depth % 4)
        wrap = ["trace_hook"] if depth % 2 == 1 else []
        traces.append(("B4_ast_overflow", wrap + ["visit_binop", "fold_constants"] + rec + [f"entry_{depth // 3}", "main"]))
    for k in range(6):
        traces.append(("B5_leb128_oob", (["instrument_wrapper"] if k % 3 == 0 else []) +
                       ["decode_uleb128", "read_dwarf_abbrev", f"parse_unit_{k}", "symbolize"]))
        traces.append(("B6_utf8_slice", ["slice_char_boundary", "truncate_snippet", f"render_diag_{k}", "emit_report"]))
    traces.append(("B7_png_header", ["parse_chunk"]))
    traces.append(("B7_png_header", ["parse_chunk"]))
    traces.append(("B8_zlib_huffman", ["parse_chunk", "inflate_huffman_oob", "zlib_decompress_stream", "load_asset"]))
    traces.append(("B8_zlib_huffman", ["parse_chunk", "inflate_huffman_oob", "zlib_decompress_stream", "fuzz_entry"]))

    true_labels = [t[0] for t in traces]
    stacks = [t[1] for t in traces]
    n = len(stacks)
    n_true = len(set(true_labels))
    assert n == 40 and n_true == 8

    def hash_clusters(k_frames: Optional[int]) -> List[int]:
        mapping: Dict[Tuple[str, ...], int] = {}
        out: List[int] = []
        for s in stacks:
            key = tuple(s if k_frames is None else s[:k_frames])
            if key not in mapping:
                mapping[key] = len(mapping)
            out.append(mapping[key])
        return out

    def dist_mat(fn: Callable[[Sequence[str], Sequence[str]], float]) -> List[List[float]]:
        return [[0.0 if i == j else fn(stacks[i], stacks[j]) for j in range(n)] for i in range(n)]

    idf = compute_frame_idf([collapse_adjacent_recursion(s) for s in stacks])
    cf_raw = clusterfuzz_grouper_transitive(stacks)
    cf_scb, cf_scb_dispatches = scb_post_patch_replay(true_labels, cf_raw)
    s3m_dist = dist_mat(lambda a, b: 1.0 - rebucket_sim_s3m_buggy(a, b))
    s3m_pred_048 = average_linkage_from_dist(s3m_dist, 0.48)
    s3m_pred_050 = average_linkage_from_dist(s3m_dist, 0.50)
    zhang_single_006 = zhang_single_pass_clustering(stacks, k_threshold=0.06)
    zhang_avg_048 = average_linkage_from_dist(dist_mat(rebucket_dist_zhang_buggy), 0.48)
    dang_pred = average_linkage_from_dist(dist_mat(lambda a, b: 1.0 - rebucket_sim_exact(a, b, 0.04, 0.13)), 0.48)
    idf_pred = average_linkage_from_dist(dist_mat(lambda a, b: 1.0 - rebucket_sim_idf_maxnorm(a, b, idf, 0.04, 0.13)), 0.62)

    methods: List[Tuple[str, List[int]]] = [
        ("Top-1 Hash (BFF-1)", hash_clusters(1)),
        ("ClusterFuzz grouper (exact)", cf_raw),
        ("Top-5 Hash (BFF-5)", hash_clusters(5)),
        ("Full-Stack Hash", hash_clusters(None)),
        ("S3M Buggy AvgLink (d=0.48)", s3m_pred_048),
        ("S3M Buggy AvgLink (d=0.50)", s3m_pred_050),
        ("Zhang SinglePass (k=0.06)", zhang_single_006),
        ("Zhang Buggy AvgLink (d=.48)", zhang_avg_048),
        ("ReBucket Steep (c=.5,o=.3)", average_linkage_from_dist(dist_mat(lambda a, b: 1.0 - rebucket_sim_exact(a, b, 0.50, 0.30)), 0.32)),
        ("ReBucket Dang12 (c=.04,.13)", dang_pred),
        ("IDF-ReBucket MaxNorm", idf_pred),
        ("ClusterFuzz + SCB Replay", cf_scb),
    ]

    summary: Dict[str, Tuple[float, float, float, int, int]] = {}
    for name, pred in methods:
        bp, br, bf1, pur, ipur = bcubed_and_purity(true_labels, pred)
        n_bkt = len(set(pred))
        first_bug: Dict[int, str] = {}
        for idx, cid in enumerate(pred):
            if cid not in first_bug:
                first_bug[cid] = true_labels[idx]
        covered = len(set(first_bug.values()))
        masked = n_true - covered
        wasted = n_bkt - covered
        summary[name] = (bp, br, bf1, masked, wasted)
        print(f"    {name:28s} | Bkts={n_bkt:2d}/{n_true} | BCubed P={bp:.3f} R={br:.3f} F1={bf1:.3f} | "
              f"Pur={pur:.3f} IP={ipur:.3f} | Masked={masked} Wasted={wasted:2d}")

    # Verify structural invariants across bucketers (including S3M dual-cutoff distortion)
    assert summary["ClusterFuzz grouper (exact)"][3] == 3  # Masks B2, B3 (LCS>=2) and B8 (1-frame prefix)
    assert summary["Full-Stack Hash"][4] == 31             # 39 buckets for 8 bugs -> 31 wasted agents
    assert summary["S3M Buggy AvgLink (d=0.48)"][3] == 0 and summary["S3M Buggy AvgLink (d=0.48)"][4] == 1
    assert summary["S3M Buggy AvgLink (d=0.50)"][3] == 1 and summary["S3M Buggy AvgLink (d=0.50)"][4] == 0
    assert summary["Zhang SinglePass (k=0.06)"][4] >= 1    # Over-splits at strict kThreshold=0.06 + splits B7
    assert summary["Zhang Buggy AvgLink (d=.48)"][4] == 1
    assert summary["ReBucket Dang12 (c=.04,.13)"][3] == 1  # min(n1,n2) masks B8 under 1-frame B7
    assert summary["IDF-ReBucket MaxNorm"][:3] == (1.0, 1.0, 1.0)
    assert summary["ClusterFuzz + SCB Replay"][:3] == (1.0, 1.0, 1.0)
    assert summary["ClusterFuzz + SCB Replay"][3] == 0 and cf_scb_dispatches == n_true


# ============================================================================
# PROBE 3: Pure-Stdlib 3-Way diff3, ConGra Metric Audit & AST Semantic Gate
# ============================================================================


def congra_remove_invisible(s: str) -> str:
    return re.sub(r"[\s\x00-\x1f\x7f-\x9f]+", "", s)


def congra_metric_edit_distance_repro(gen_str: str, standard_str: str) -> float:
    """Exact reproduction of HKU-System-Security-Lab/ConGra@c33fc9165364 src/metrics.py:51-73."""
    g = congra_remove_invisible(gen_str)
    s = congra_remove_invisible(standard_str)
    if len(g) == 0 or len(s) == 0:
        return 0.0
    # Upstream L58-72 allocates len(g) x len(s) instead of (len(g)+1) x (len(s)+1), ignoring index 0.
    mark = [[0] * len(s) for _ in range(len(g))]
    for i in range(len(g)):
        mark[i][0] = i
    for j in range(len(s)):
        mark[0][j] = j
    for i in range(1, len(g)):
        for j in range(1, len(s)):
            if g[i] == s[j]:
                mark[i][j] = mark[i - 1][j - 1]
            else:
                mark[i][j] = min(mark[i - 1][j], mark[i][j - 1], mark[i - 1][j - 1]) + 1
    min_distance = mark[len(g) - 1][len(s) - 1]
    return 1.0 - min_distance / max(len(g), len(s))


def congra_metric_winnowing_repro(gen_str: str, standard_str: str) -> float:
    """Exact reproduction of ConGra src/metrics.py:75-140 (empty-string inversion + short-string ZeroDivisionError)."""
    g = congra_remove_invisible(gen_str)
    s = congra_remove_invisible(standard_str)
    if len(g) == 0 and len(s) == 0:
        return 0.0
    if len(g) == 0 or len(s) == 0:
        return 1.0

    # Winnowing k-gram length k=5, window t=4 => requires >= 8 non-whitespace chars to emit >= 1 fingerprint
    def kgrams_and_winnow(text: str, k: int = 5, window: int = 4) -> List[int]:
        hashes = [sum(ord(ch) * (31 ** idx) for idx, ch in enumerate(text[i:i + k])) for i in range(len(text) - k + 1)]
        if len(hashes) < window:
            return []
        fps: List[int] = []
        for i in range(len(hashes) - window + 1):
            fps.append(min(hashes[i:i + window]))
        return fps

    fp_g = set(kgrams_and_winnow(g))
    fp_s = set(kgrams_and_winnow(s))
    # Upstream L139 divides by len(fp_g | fp_s), raising ZeroDivisionError when both strings have < 8 chars.
    return len(fp_g & fp_s) / len(fp_g | fp_s)


def congra_main_winnowing_wrapper(gen_str: str, standard_str: str) -> float:
    """Exact reproduction of HKU-System-Security-Lab/ConGra@c33fc9165364 src/main.py:127-130 silent -1 coercion."""
    try:
        return congra_metric_winnowing_repro(gen_str, standard_str)
    except Exception:
        return -1.0


def diff3_merge_lines(
    base_src: str, ours_src: str, theirs_src: str
) -> Tuple[str, int]:
    """Pure-stdlib 3-way line merger emitting diff3 conflict markers on overlapping or boundary-touching edits."""
    b_lines = base_src.splitlines(keepends=True)
    o_lines = ours_src.splitlines(keepends=True)
    t_lines = theirs_src.splitlines(keepends=True)

    def change_spans(a: List[str], b: List[str]) -> List[Tuple[int, int, List[str]]]:
        sm = difflib.SequenceMatcher(None, a, b, autojunk=False)
        return [(i1, i2, b[j1:j2]) for tag, i1, i2, j1, j2 in sm.get_opcodes() if tag != "equal"]

    o_spans = change_spans(b_lines, o_lines)
    t_spans = change_spans(b_lines, t_lines)

    all_events = sorted(
        [(s, e, "o", rep) for s, e, rep in o_spans] + [(s, e, "t", rep) for s, e, rep in t_spans],
        key=lambda x: (x[0], x[1], x[2]),
    )
    regions: List[Tuple[int, int]] = []
    for s, e, _, _ in all_events:
        # Strict inequality s > regions[-1][1] coalesces adjacent/boundary-touching edits
        # into one region so consecutive regions are strictly disjoint (prev_end < next_start).
        if not regions or s > regions[-1][1]:
            regions.append((s, e))
        else:
            regions[-1] = (regions[-1][0], max(regions[-1][1], e))

    def apply_spans(spans: List[Tuple[int, int, List[str]]], r_start: int, r_end: int) -> List[str]:
        out: List[str] = []
        cur = r_start
        for s, e, rep in spans:
            if s < r_start or e > r_end:
                continue
            out.extend(b_lines[cur:s])
            out.extend(rep)
            cur = e
        out.extend(b_lines[cur:r_end])
        return out

    merged: List[str] = []
    conflicts = 0
    pos = 0
    for rs, re_idx in regions:
        merged.extend(b_lines[pos:rs])
        base_seg = b_lines[rs:re_idx]
        ours_seg = apply_spans(o_spans, rs, re_idx)
        theirs_seg = apply_spans(t_spans, rs, re_idx)
        if ours_seg == theirs_seg:
            merged.extend(ours_seg)
        elif ours_seg == base_seg:
            merged.extend(theirs_seg)
        elif theirs_seg == base_seg:
            merged.extend(ours_seg)
        else:
            conflicts += 1
            merged.append("<<<<<<< OURS\n")
            merged.extend(ours_seg)
            merged.append("||||||| BASE\n")
            merged.extend(base_seg)
            merged.append("=======\n")
            merged.extend(theirs_seg)
            merged.append(">>>>>>> THEIRS\n")
        pos = re_idx
    merged.extend(b_lines[pos:])
    return "".join(merged), conflicts


def extract_semantic_atoms(src: str) -> Set[str]:
    """Extract scope-qualified Python AST semantic atoms: sig, dec, if, raise, assert, call+kwargs, assign, augassign, return."""
    tree = ast.parse(src)
    atoms: Set[str] = set()

    class Visitor(ast.NodeVisitor):
        def __init__(self) -> None:
            self.scope: List[str] = []

        def _pfx(self) -> str:
            return ".".join(self.scope) if self.scope else "<mod>"

        def _visit_func(self, node: ast.FunctionDef | ast.AsyncFunctionDef) -> None:
            args = ",".join(a.arg for a in node.args.args)
            atoms.add(f"sig:{self._pfx()}.{node.name}({args})")
            for dec in node.decorator_list:
                atoms.add(f"dec:{self._pfx()}.{node.name}:@{ast.unparse(dec)}")
            self.scope.append(node.name)
            self.generic_visit(node)
            self.scope.pop()

        def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
            self._visit_func(node)

        def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> None:
            self._visit_func(node)

        def visit_If(self, node: ast.If) -> None:
            atoms.add(f"if:{self._pfx()}:{ast.unparse(node.test)}")
            self.generic_visit(node)

        def visit_Raise(self, node: ast.Raise) -> None:
            exc = ast.unparse(node.exc).split("(")[0] if node.exc else "reraise"
            atoms.add(f"raise:{self._pfx()}:{exc}")
            self.generic_visit(node)

        def visit_Assert(self, node: ast.Assert) -> None:
            atoms.add(f"assert:{self._pfx()}:{ast.unparse(node.test)}")
            self.generic_visit(node)

        def visit_Call(self, node: ast.Call) -> None:
            kw = ",".join(sorted(k.arg for k in node.keywords if k.arg))
            atoms.add(f"call:{self._pfx()}:{ast.unparse(node.func)}[{kw}]")
            self.generic_visit(node)

        def visit_Assign(self, node: ast.Assign) -> None:
            targets = ",".join(ast.unparse(t) for t in node.targets)
            atoms.add(f"assign:{self._pfx()}:{targets}={ast.unparse(node.value)}")
            self.generic_visit(node)

        def visit_AugAssign(self, node: ast.AugAssign) -> None:
            atoms.add(f"aug:{self._pfx()}:{ast.unparse(node.target)}:{type(node.op).__name__}")
            self.generic_visit(node)

        def visit_Return(self, node: ast.Return) -> None:
            val = ast.unparse(node.value) if node.value is not None else "None"
            atoms.add(f"ret:{self._pfx()}:{val}")
            self.generic_visit(node)

    Visitor().visit(tree)
    return atoms


CONFLICT_MARKERS = ("<<<<<<<", "=======", "|||||||", ">>>>>>>")


def audit_three_way_merge(
    base: str, ours: str, theirs: str, candidate: str
) -> Tuple[bool, bool, str]:
    """Return (syntax_valid, ast_delta_gate_ok, verdict) checking universal subset preservation (add_a <= f_m and add_b <= f_m)."""
    if any(m in candidate for m in CONFLICT_MARKERS):
        return False, False, "CONFLICT_MARKER_REMAINING"
    try:
        f_m = extract_semantic_atoms(candidate)
    except SyntaxError:
        return False, False, "SYNTAX_ERROR"

    f_o = extract_semantic_atoms(base)
    f_a = extract_semantic_atoms(ours)
    f_b = extract_semantic_atoms(theirs)
    add_a = f_a - f_o
    add_b = f_b - f_o
    if add_a and not (add_a & f_m):
        return True, False, "SILENT_DROP_OURS"
    if add_b and not (add_b & f_m):
        return True, False, "SILENT_DROP_THEIRS"
    crit_missing = sorted(
        x for x in (add_a | add_b) - f_m if x.startswith(("raise:", "assert:", "dec:", "if:"))
    )
    if crit_missing:
        return True, False, f"CRITICAL_INVARIANT_DROPPED({crit_missing[0]})"
    partial_missing = sorted((add_a | add_b) - f_m)
    if partial_missing:
        return True, False, f"PARTIAL_DELTA_DROPPED({partial_missing[0]})"
    return True, True, "AST_DELTAS_PRESERVED"


def _make_transfer_oracle() -> Callable[[str], bool]:
    def run(src: str) -> bool:
        class Acct:
            def __init__(self, i: str, bal: int, frozen: bool = False) -> None:
                self.id, self.balance, self.is_frozen, self.currency = i, bal, frozen, "USD"

        ev: List[str] = []
        ns = {
            "audit_log": lambda a, b, amount: ev.append(f"a:{amount}"),
            "metrics_inc": lambda name, currency: ev.append(f"m:{currency}"),
            "notify_ops": lambda acct_id, amount: ev.append(f"n:{acct_id}:{amount}"),
        }
        try:
            exec(src, ns)
        except SyntaxError:
            return False
        fn = ns["transfer_funds"]
        try:
            fn(Acct("a", 10), Acct("b", 0), 50)
            return False
        except PermissionError:
            pass
        try:
            fn(Acct("a", 100, frozen=True), Acct("b", 0), 20)
            return False
        except RuntimeError:
            pass
        a, b = Acct("a", 100), Acct("b", 0)
        return fn(a, b, 30) == 70 and ("a:30" in ev) and ("m:USD" in ev)

    return run


def run_probe_3() -> None:
    print("\n=== PROBE 3: 3-Way diff3 Merge Engine, ConGra Metric Audit & Unweighted AST Gate + Negative Controls ===")
    print("  Provenance: [exact reproduction of pinned repository logic] + [controlled mechanistic test suite]")

    # 1. Exact reproduction of ConGra src/metrics.py & src/main.py:127-130 bugs + guard-drop blindness
    print("\n  [3.1 Exact Reproduction of Pinned Repository Logic] ConGra@c33fc9165364 src/metrics.py & src/main.py:")
    ed_ab = congra_metric_edit_distance_repro("a", "b")
    ed_ax_bx = congra_metric_edit_distance_repro("ax", "bx")
    win_ee = congra_metric_winnowing_repro("", "")
    win_en = congra_metric_winnowing_repro("", "returnx+1")
    short_zde = False
    try:
        congra_metric_winnowing_repro("x=1", "x=2")
    except ZeroDivisionError:
        short_zde = True
    short_coerced = congra_main_winnowing_wrapper("x=1", "x=2")
    assert ed_ab == 1.0 and ed_ax_bx == 1.0
    assert win_ee == 0.0 and win_en == 1.0
    assert short_zde is True and short_coerced == -1.0
    print(f"    metric_edit_distance index-0 bug: ES('a','b')={ed_ab:.3f}, ES('ax','bx')={ed_ax_bx:.3f} (should be 0.0/0.5!)")
    print(f"    metric_winnowing empty inversion: WS('','')={win_ee:.1f}, WS('','returnx+1')={win_en:.1f} (inverted!)")
    print(f"    metric_winnowing short-string:    ZeroDivisionError={short_zde} -> main.py:127-130 silent coercion={short_coerced:.1f}")

    # Realistic 20-line service function: deleting a 2-line security guard still scores ConGra ES > 0.90.
    long_sound = (
        "def settle_invoice(inv, ledger, actor):\n"
        "    if actor.role != 'treasury':\n"
        "        raise PermissionError('forbidden')\n"
        "    subtotal = sum(item.price * item.qty for item in inv.items)\n"
        "    discount = min(inv.discount, subtotal)\n"
        "    taxable = subtotal - discount\n"
        "    tax = round(taxable * inv.tax_rate, 2)\n"
        "    fees = round(taxable * inv.platform_fee_rate, 2)\n"
        "    total = taxable + tax + fees\n"
        "    ledger.validate_account(inv.payer_id, currency=inv.currency)\n"
        "    ledger.validate_account(inv.payee_id, currency=inv.currency)\n"
        "    ledger.debit(inv.payer_id, amount=total, currency=inv.currency)\n"
        "    ledger.credit(inv.payee_id, amount=total - fees, currency=inv.currency)\n"
        "    ledger.credit(ledger.fee_account, amount=fees, currency=inv.currency)\n"
        "    ledger.record_entry(inv.id, subtotal=subtotal, tax=tax, fees=fees, total=total)\n"
        "    inv.status = 'settled'\n"
        "    inv.settled_by = actor.id\n"
        "    emit_receipt(inv.id, recipient=inv.payer_email, total=total, currency=inv.currency)\n"
        "    publish_event('invoice.settled', invoice_id=inv.id, total=total)\n"
        "    return {'id': inv.id, 'total': total, 'status': inv.status}\n"
    )
    long_drop_auth = "\n".join(
        line for line in long_sound.splitlines()
        if "actor.role" not in line and "PermissionError" not in line
    ) + "\n"
    es_long = congra_metric_edit_distance_repro(long_drop_auth, long_sound)
    assert es_long > 0.90
    print(f"    ConGra ES guard-deletion blindness: deleting auth PermissionError from 20-line fn -> ES={es_long:.4f} (>0.90!)")

    # 2. Pure-stdlib diff3 boundary regression tests (verifying zero silent data loss on adjacent edit + insert)
    print("\n  [3.2 Pure-Stdlib diff3 Boundary Regression Checks]:")
    adj_merged, adj_conf = diff3_merge_lines("A\nB\nC\n", "A\nB_new\nC\n", "A\nB\nX\nC\n")
    assert adj_conf == 1 and "B_new\n" in adj_merged and "X\n" in adj_merged
    pre_merged, pre_conf = diff3_merge_lines("A\nB\nC\n", "A\nY\nB\nC\n", "A\nB_new\nC\n")
    assert pre_conf == 1 and "Y\n" in pre_merged and "B_new\n" in pre_merged
    disj_merged, disj_conf = diff3_merge_lines("A\nB\nC\n", "A_new\nB\nC\n", "A\nB\nX\nC\n")
    assert disj_conf == 0 and disj_merged == "A_new\nB\nX\nC\n"
    same_ins_merged, same_ins_conf = diff3_merge_lines("A\nB\nC\n", "A\nB\nX\nC\n", "A\nB\nX\nC\n")
    assert same_ins_conf == 0 and same_ins_merged == "A\nB\nX\nC\n"
    print(f"    Adjacent replace(1,2)+insert(2,2): conflicts={adj_conf} (zero silent drop of 'X'); "
          f"prepend(1,1)+replace(1,2): conflicts={pre_conf}; disjoint clean merge: conflicts={disj_conf}")

    # 3. Unweighted Distinct Conflict Suite (each scenario evaluated ONCE; zero multiplicity replication)
    print("\n  [3.3 Controlled Mechanistic Test Suite — Unweighted Distinct Scenarios (multiplicity=1, NOT empirical prevalence)]:")

    # Clean non-overlapping 3-way merge sanity check
    clean_base = "def process(x):\n    y = x + 1\n    z = y * 2\n    return z\n"
    clean_ours = "def process(x):\n    assert x >= 0\n    y = x + 1\n    z = y * 2\n    return z\n"
    clean_theirs = "def process(x):\n    y = x + 1\n    z = y * 2\n    log_done(val=z)\n    return z\n"
    clean_merged, clean_conf = diff3_merge_lines(clean_base, clean_ours, clean_theirs)
    clean_syn, clean_gate, clean_verdict = audit_three_way_merge(clean_base, clean_ours, clean_theirs, clean_merged)
    assert clean_conf == 0 and clean_syn and clean_gate
    print(f"    Clean_NonOverlapping_diff3 | conflicts={clean_conf} | Syntax={clean_syn} | AST_Gate={clean_gate} ({clean_verdict})")

    # Scenario family A: transfer_funds conflicts
    tf_base = (
        "def transfer_funds(acct, dest, amount):\n"
        "    if amount <= 0:\n"
        "        raise ValueError('non-positive')\n"
        "    acct.balance -= amount\n"
        "    dest.balance += amount\n"
        "    return acct.balance\n"
    )
    tf_ours = (
        "def transfer_funds(acct, dest, amount):\n"
        "    if amount <= 0:\n"
        "        raise ValueError('non-positive')\n"
        "    if acct.balance < amount:\n"
        "        raise PermissionError('insufficient')\n"
        "    acct.balance -= amount\n"
        "    dest.balance += amount\n"
        "    audit_log(acct.id, dest.id, amount=amount)\n"
        "    return acct.balance\n"
    )
    tf_theirs = (
        "def transfer_funds(acct, dest, amount):\n"
        "    if acct.is_frozen or dest.is_frozen:\n"
        "        raise RuntimeError('frozen')\n"
        "    if amount <= 0:\n"
        "        raise ValueError('non-positive')\n"
        "    acct.balance -= amount\n"
        "    dest.balance += amount\n"
        "    metrics_inc('transfers', currency=acct.currency)\n"
        "    return acct.balance\n"
    )
    tf_raw, tf_conf = diff3_merge_lines(tf_base, tf_ours, tf_theirs)
    assert tf_conf >= 1
    tf_drop_guard = (
        "def transfer_funds(acct, dest, amount):\n"
        "    if amount <= 0:\n"
        "        raise ValueError('non-positive')\n"
        "    if acct.balance < amount:\n"
        "        raise PermissionError('insufficient')\n"
        "    acct.balance -= amount\n"
        "    dest.balance += amount\n"
        "    audit_log(acct.id, dest.id, amount=amount)\n"
        "    metrics_inc('transfers', currency=acct.currency)\n"
        "    return acct.balance\n"
    )
    tf_sound = (
        "def transfer_funds(acct, dest, amount):\n"
        "    if acct.is_frozen or dest.is_frozen:\n"
        "        raise RuntimeError('frozen')\n"
        "    if amount <= 0:\n"
        "        raise ValueError('non-positive')\n"
        "    if acct.balance < amount:\n"
        "        raise PermissionError('insufficient')\n"
        "    acct.balance -= amount\n"
        "    dest.balance += amount\n"
        "    metrics_inc('transfers', currency=acct.currency)\n"
        "    audit_log(acct.id, dest.id, amount=amount)\n"
        "    return acct.balance\n"
    )
    test_tf = _make_transfer_oracle()

    # Scenario B: Multi-call partial drop (tests universal add_a <= f_m vs existential add_a & f_m)
    mc_ours = (
        "def transfer_funds(acct, dest, amount):\n"
        "    if amount <= 0:\n"
        "        raise ValueError('non-positive')\n"
        "    if acct.balance < amount:\n"
        "        raise PermissionError('insufficient')\n"
        "    acct.balance -= amount\n"
        "    dest.balance += amount\n"
        "    audit_log(acct.id, dest.id, amount=amount)\n"
        "    notify_ops(acct.id, amount=amount)\n"
        "    return acct.balance\n"
    )
    mc_partial_drop = tf_sound  # keeps audit_log + metrics_inc + both guards, drops notify_ops!

    def test_mc(src: str) -> bool:
        class Acct:
            def __init__(self, i: str, bal: int, frozen: bool = False) -> None:
                self.id, self.balance, self.is_frozen, self.currency = i, bal, frozen, "USD"

        ev: List[str] = []
        ns = {
            "audit_log": lambda a, b, amount: ev.append(f"a:{amount}"),
            "metrics_inc": lambda name, currency: ev.append(f"m:{currency}"),
            "notify_ops": lambda acct_id, amount: ev.append(f"n:{acct_id}:{amount}"),
        }
        try:
            exec(src, ns)
        except SyntaxError:
            return False
        a, b = Acct("a", 100), Acct("b", 0)
        return ns["transfer_funds"](a, b, 30) == 70 and ("a:30" in ev) and ("m:USD" in ev) and ("n:a:30" in ev)

    # Scenario C: Assign delta drop (both branches modify adjacent assignment/return block)
    asg_base = "def price(subtotal):\n    total = subtotal\n    return total\n"
    asg_ours = "def price(subtotal):\n    tax = round(subtotal * 0.1, 2)\n    total = subtotal + tax\n    return total\n"
    asg_theirs = "def price(subtotal):\n    fee = 2\n    total = subtotal + fee\n    return total\n"
    asg_drop = "def price(subtotal):\n    fee = 2\n    total = subtotal + fee\n    return total\n"
    asg_sound = "def price(subtotal):\n    tax = round(subtotal * 0.1, 2)\n    fee = 2\n    total = subtotal + tax + fee\n    return total\n"

    def test_asg(src: str) -> bool:
        ns: Dict[str, object] = {}
        try:
            exec(src, ns)
            return abs(ns["price"](100) - 112.0) < 1e-9  # type: ignore[operator]
        except SyntaxError:
            return False

    # Scenario D: Return-expression modification drop
    ret_base = "def scale(x):\n    return x + 1\n"
    ret_ours = "def scale(x):\n    assert x >= 0\n    return x + 1\n"
    ret_theirs = "def scale(x):\n    return x * 2\n"
    ret_drop = "def scale(x):\n    assert x >= 0\n    return x + 1\n"

    def test_ret(src: str) -> bool:
        ns: Dict[str, object] = {}
        try:
            exec(src, ns)
            fn = ns["scale"]
            return fn(5) == 10  # type: ignore[operator]
        except (SyntaxError, AssertionError):
            return False

    # Scenario E: Guard predicate inversion (if x < 0 -> if x > 0)
    inv_base = "def normalize(x):\n    return x * 10\n"
    inv_ours = "def normalize(x):\n    if x < 0:\n        raise ValueError('neg')\n    return x * 10\n"
    inv_theirs = "def normalize(x):\n    tag = 'scaled'\n    return x * 10\n"
    inv_flipped = "def normalize(x):\n    if x > 0:\n        raise ValueError('neg')\n    tag = 'scaled'\n    return x * 10\n"

    def test_inv(src: str) -> bool:
        ns: Dict[str, object] = {}
        try:
            exec(src, ns)
            fn = ns["normalize"]
            try:
                fn(-1)  # type: ignore[operator]
                return False
            except ValueError:
                pass
            return fn(2) == 20  # type: ignore[operator]
        except (SyntaxError, ValueError):
            return False

    # Scenario F: Early-return guard drop (if x < 0: return 0)
    er_base = "def clamp_double(x):\n    return x * 2\n"
    er_ours = "def clamp_double(x):\n    if x < 0:\n        return 0\n    return x * 2\n"
    er_theirs = "def clamp_double(x):\n    limit = 100\n    return min(x * 2, limit)\n"
    er_drop = "def clamp_double(x):\n    limit = 100\n    return min(x * 2, limit)\n"

    def test_er(src: str) -> bool:
        ns: Dict[str, object] = {}
        try:
            exec(src, ns)
            fn = ns["clamp_double"]
            return fn(-5) == 0 and fn(60) == 100  # type: ignore[operator]
        except SyntaxError:
            return False

    # Adversarial Negative Control 1: Dynamic state-ordering interaction passes AST gate yet fails runtime tests
    nc1_base = "def apply_fee(state, fee):\n    return state['bal']\n"
    nc1_ours = "def apply_fee(state, fee):\n    state['bal'] -= fee\n    return state['bal']\n"
    nc1_theirs = "def apply_fee(state, fee):\n    assert state['bal'] >= fee\n    return state['bal']\n"
    nc1_misordered = "def apply_fee(state, fee):\n    state['bal'] -= fee\n    assert state['bal'] >= fee\n    return state['bal']\n"

    def test_nc1(src: str) -> bool:
        ns: Dict[str, object] = {}
        try:
            exec(src, ns)
            return ns["apply_fee"]({"bal": 10}, 6) == 4  # type: ignore[operator]
        except (SyntaxError, AssertionError):
            return False

    # Adversarial Negative Control 2: Side-effect reordered before ban guard (all AST atoms preserved verbatim!)
    nc2_base = "def charge(user, amount):\n    return amount\n"
    nc2_ours = "def charge(user, amount):\n    if user['banned']:\n        raise PermissionError('banned')\n    return amount\n"
    nc2_theirs = "def charge(user, amount):\n    debit_wallet(user, amount=amount)\n    return amount\n"
    nc2_misordered = (
        "def charge(user, amount):\n"
        "    debit_wallet(user, amount=amount)\n"
        "    if user['banned']:\n"
        "        raise PermissionError('banned')\n"
        "    return amount\n"
    )

    def test_nc2(src: str) -> bool:
        debits: List[int] = []
        ns: Dict[str, object] = {"debit_wallet": lambda u, amount: debits.append(amount)}
        try:
            exec(src, ns)
            fn = ns["charge"]
            try:
                fn({"banned": True}, 50)  # type: ignore[operator]
                return False
            except PermissionError:
                pass
            return len(debits) == 0  # Must NOT debit a banned user before raising!
        except SyntaxError:
            return False

    # Disjoint assignment + augassign bilateral merge (sound under BOTH AST gate and unit tests)
    aug_base = "def invoice_total(subtotal):\n    total = subtotal\n    return total\n"
    aug_ours = "def invoice_total(subtotal):\n    total = subtotal\n    tax = round(subtotal * 0.1, 2)\n    total += tax\n    return total\n"
    aug_theirs = "def invoice_total(subtotal):\n    total = subtotal\n    fee = 2\n    total += fee\n    return total\n"
    aug_sound = (
        "def invoice_total(subtotal):\n"
        "    total = subtotal\n"
        "    tax = round(subtotal * 0.1, 2)\n"
        "    total += tax\n"
        "    fee = 2\n"
        "    total += fee\n"
        "    return total\n"
    )

    def test_aug(src: str) -> bool:
        ns: Dict[str, object] = {}
        try:
            exec(src, ns)
            return abs(ns["invoice_total"](100) - 112.0) < 1e-9  # type: ignore[operator]
        except SyntaxError:
            return False

    # Distinct unweighted conflict cases (each evaluated exactly once)
    distinct_cases: List[Tuple[str, str, str, str, str, Callable[[str], bool], Tuple[bool, bool, bool]]] = [
        ("Case_RawDiff3Markers",       tf_base,  tf_ours,  tf_theirs,  tf_raw,          test_tf,  (False, False, False)),
        ("Case_UnilateralOursDrop",    tf_base,  tf_ours,  tf_theirs,  tf_ours,         test_tf,  (True,  False, False)),
        ("Case_UnilateralTheirsDrop",  tf_base,  tf_ours,  tf_theirs,  tf_theirs,       test_tf,  (True,  False, False)),
        ("Case_PartialGuardDrop",      tf_base,  tf_ours,  tf_theirs,  tf_drop_guard,   test_tf,  (True,  False, False)),
        ("Case_MultiCallPartialDrop",  tf_base,  mc_ours,  tf_theirs,  mc_partial_drop, test_mc,  (True,  False, False)),
        ("Case_AssignDeltaDrop",       asg_base, asg_ours, asg_theirs, asg_drop,        test_asg, (True,  False, False)),
        ("Case_ReturnExprDrop",        ret_base, ret_ours, ret_theirs, ret_drop,        test_ret, (True,  False, False)),
        ("Case_IfPredicateInversion",  inv_base, inv_ours, inv_theirs, inv_flipped,     test_inv, (True,  False, False)),
        ("Case_EarlyReturnGuardDrop",  er_base,  er_ours,  er_theirs,  er_drop,         test_er,  (True,  False, False)),
        ("Case_FN_DynamicOrder",       nc1_base, nc1_ours, nc1_theirs, nc1_misordered,  test_nc1, (True,  True,  False)),
        ("Case_FN_SideEffectOrder",    nc2_base, nc2_ours, nc2_theirs, nc2_misordered,  test_nc2, (True,  True,  False)),
        ("Case_FP_SynthAssignExpr",    asg_base, asg_ours, asg_theirs, asg_sound,       test_asg, (True,  False, True)),
        ("Case_SoundBilateralXfer",    tf_base,  tf_ours,  tf_theirs,  tf_sound,        test_tf,  (True,  True,  True)),
        ("Case_SoundBilateralInvoice", aug_base, aug_ours, aug_theirs, aug_sound,       test_aug, (True,  True,  True)),
    ]

    caught_structural = 0
    escaped_negative_controls = 0
    fp_controls = 0
    sound_passed = 0
    for name, b, o, t, cand, oracle, expected in distinct_cases:
        _, n_conf = diff3_merge_lines(b, o, t)
        assert n_conf >= 1, f"{name} is not a real diff3 conflict!"
        syn, gate, verdict = audit_three_way_merge(b, o, t, cand)
        t_ok = oracle(cand)
        assert (syn, gate, t_ok) == expected, f"{name}: got {(syn, gate, t_ok)} != {expected} ({verdict})"
        if syn and not gate and not t_ok:
            caught_structural += 1
        elif syn and gate and not t_ok:
            escaped_negative_controls += 1
        elif syn and not gate and t_ok:
            fp_controls += 1
        elif syn and gate and t_ok:
            sound_passed += 1
        print(f"    {name:27s} | diff3_conf={n_conf} | Syntax={str(syn):5s} | AST_Gate={str(gate):5s} | "
              f"Tests={str(t_ok):5s} | {verdict}")

    assert caught_structural == 8 and escaped_negative_controls == 2 and fp_controls == 1 and sound_passed == 2
    print(f"    [Unweighted Summary — 14 Distinct Conflict Cases] 1 marker/syntax failure; "
          f"{caught_structural} AST-delta failures caught by universal subset gate (incl. multi-call partial drop, "
          f"assign, return, if-guard inversion, early-return drop); {escaped_negative_controls} adversarial ordering "
          f"false-negative controls caught ONLY by unit tests; {fp_controls} synthesized-expression false-positive control "
          f"(valid merge flagged by literal AST matching); {sound_passed} sound bilateral merges.")


def main() -> None:
    run_probe_1()
    run_probe_2()
    run_probe_3()
    print("\nALL THREE STANDALONE STDLIB PROBES PASSED.")


if __name__ == "__main__":
    main()
