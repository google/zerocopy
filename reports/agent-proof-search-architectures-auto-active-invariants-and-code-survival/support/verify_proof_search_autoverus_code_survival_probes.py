#!/usr/bin/env python3
"""Standalone verification probes for:
  1. Baldur/Thor PISA repair reconciliation and an exact discrete-budget
     parametric proof-search sensitivity model (monolithic whole-proof,
     deduplicated error-localized vs. blind repair, closed-loop best-first
     tactic tree search with prefix sharing and dead-end backtracking, and
     hierarchical AND/OR subgoal decomposition with consistent geometric
     early stopping).
  2. AutoVerus/Laurel/SAFE/Vericoding reconciliation, simultaneous multi-error
     Houdini maximal-inductive-subset pruning with error-code-dispatched repair
     and non-vacuity checks, and Kani/CBMC N+1 unwinding semantics plus
     entry-vs-postcondition vacuity separation.
  3. Rahman et al. tracker-inflation reconciliation, binary risk-difference
     analogue of repo-confounding/cluster DEFF (pooled and within-stratum) with
     Liang-Zeger/jackknife SEs and Mantel-Haenszel stratification, Kaplan-Meier
     crossover under intermediate right-censoring, sequence-aligned move and
     block-scoped alpha-renaming detection, and source-diff/def-use omission
     SZZ attribution.

Constraints:
  - Python 3.10+ standard library only (zero third-party dependencies).
  - Strictly deterministic across PYTHONHASHSEED values.
  - Zero disk writes and zero network access.
"""

from __future__ import annotations

import difflib
import math
import random
import re
from dataclasses import dataclass
from typing import Callable, Iterable


# =============================================================================
# PROBE 1: BALDUR/THOR RECONCILIATION & DISCRETE-BUDGET PROOF-SEARCH MODEL
# =============================================================================

def run_probe_1() -> None:
    print("=" * 78)
    print("PROBE 1A [exact calculation on published dataset/equations]:")
    print("  Baldur (arXiv:2303.04910v2) PISA data.tex Reconciliation & Thor Portfolio")
    print("=" * 78)

    # Embedded counts from Baldur arXiv:2303.04910v2 data.tex (N_csv = 6354 = 6633 - 279)
    # vs. main-prose/Table-1 denominator N_prose = 6336 (repairPaper.tex L152, L674, L717).
    n_csv = 6354
    n_prose = 6336
    assert 6633 - 279 == n_csv

    baldur_rows = [
        ("Plain Generate (1, T=0.0)", 1.00, 1314, 0.207),
        ("Plain Generate (2, T=0.4)", 2.00, 1491, 0.235),
        ("Generate(1,T=0.0)+Error Repair(1)", 2.00, 1580, 0.249),
        ("Generate(1,T=0.4)+Blind Repair(1)", 2.00, 1427, 0.225),
        ("Plain Generate (8, T=0.6)", 8.00, 1976, 0.311),
        ("Plain Generate (16, T=0.8)", 16.00, 2207, 0.347),
        ("Generate(8,dedup)+Error Repair", 14.33, 2305, 0.363),
        ("Generate(8,dedup)+Blind Repair", 14.33, 2171, 0.342),
        ("Generate(16,dedup)+Error Repair", 28.66, 2548, 0.401),
        ("Generate(16,dedup)+Blind Repair", 28.66, 2419, 0.381),
    ]
    print(f"{'Regime':35s} {'Cost':>6s} {'Proven':>7s} {'r(6354)':>8s} {'r(6336)':>8s} {'csv':>6s}")
    for label, cost, proven, csv_ratio in baldur_rows:
        r_csv = proven / n_csv
        r_prose = proven / n_prose
        assert abs(round(r_csv, 3) - csv_ratio) <= 1e-9, (label, r_csv, csv_ratio)
        print(
            f"{label:35s} {cost:6.2f} {proven:7d} "
            f"{100.0 * r_csv:7.2f}% {100.0 * r_prose:7.2f}% {100.0 * csv_ratio:5.1f}%"
        )

    # Equal-cost deltas on N_csv = 6354
    err_vs_plain_2 = (1580 - 1491) / n_csv * 100.0
    blind_vs_plain_2 = (1427 - 1491) / n_csv * 100.0
    err_vs_plain_16 = (2305 - 2207) / n_csv * 100.0
    blind_vs_plain_16 = (2171 - 2207) / n_csv * 100.0
    cost_saving_16 = (16.00 - 14.33) / 16.00 * 100.0
    eff_repair_mult_8 = (14.33 - 8.0) / 8.0
    eff_repair_mult_16 = (28.66 - 16.0) / 16.0
    assert abs(eff_repair_mult_8 - eff_repair_mult_16) < 1e-9
    assert err_vs_plain_2 > 0.0 and blind_vs_plain_2 < 0.0
    assert err_vs_plain_16 > 0.0 and blind_vs_plain_16 < 0.0

    # Verify repairPaper.tex:808 deduplication mechanism:
    # Skipping all already-solved theorems (1976/6354 at 8 samples, 2207/6354 at 16)
    # would bound average cost strictly below the reported 14.33 and 28.66.
    max_cost_if_skip_solved_8 = 8.0 + 8.0 * (1.0 - 1976 / n_csv)
    max_cost_if_skip_solved_16 = 16.0 + 16.0 * (1.0 - 2207 / n_csv)
    assert max_cost_if_skip_solved_8 < 14.33
    assert max_cost_if_skip_solved_16 < 28.66

    # TPU accelerator ratio (repairPaper.tex Sec 4.1: Thor 60 TPU-h / 1000 vs Baldur 35s / 64 proofs)
    thor_tpu_sec = 60.0 * 3600.0 / 1000.0
    baldur_tpu_sec = 35.0
    tpu_speedup = thor_tpu_sec / baldur_tpu_sec
    assert abs(thor_tpu_sec - 216.0) < 1e-9
    assert tpu_speedup > 6.0

    # Portfolio complementarity from 1-decimal rounded table rates (repairPaper.tex L676, L679, L986):
    # Baldur 8B w/ context = 47.5%, Thor (on full 6,336 PISA test set) = 57.0%, Union = 65.7%.
    p_baldur_ctx = 0.475
    p_thor = 0.570
    p_union = 0.657
    p_intersection = p_baldur_ctx + p_thor - p_union
    p_baldur_only = p_union - p_thor
    p_thor_only = p_union - p_baldur_ctx
    jaccard = p_intersection / p_union
    # Rounding-interval bounds (+/-0.05 pp on each of the three 1-decimal reported rates)
    ov_lo = (p_baldur_ctx - 0.0005) + (p_thor - 0.0005) - (p_union + 0.0005)
    ov_hi = (p_baldur_ctx + 0.0005) + (p_thor + 0.0005) - (p_union - 0.0005)
    jacc_lo = ov_lo / (p_union + 0.0005)
    jacc_hi = ov_hi / (p_union - 0.0005)
    assert abs(p_baldur_only - 0.087) < 1e-9
    assert abs(p_intersection - 0.388) < 1e-9

    print(
        f"Exact CSV deltas (N=6354): cost=2 error-repair {err_vs_plain_2:+.2f} pp vs "
        f"blind-repair {blind_vs_plain_2:+.2f} pp; cost=14.33 vs 16.00 "
        f"({cost_saving_16:.2f}% less compute, unique-failure ratio={eff_repair_mult_8:.5f}): "
        f"error-repair {err_vs_plain_16:+.2f} pp vs blind-repair {blind_vs_plain_16:+.2f} pp"
    )
    print(
        f"Repair-cost bound check: skipping already-solved theorems would cap cost at "
        f"{max_cost_if_skip_solved_8:.3f} (<14.33) and {max_cost_if_skip_solved_16:.3f} (<28.66), "
        f"confirming per-unique-failed-attempt repair (14.33/8 = 28.66/16 = {14.33/8.0:.5f})"
    )
    print(
        f"Denominator reconciliation at 16 samples (2207 proven): "
        f"data.tex (N=6354)={2207 / n_csv * 100:.2f}% (rounds 34.7%) vs "
        f"Table 1 (N=6336)={2207 / n_prose * 100:.2f}% (rounds 34.8%)"
    )
    print(
        f"Accelerator cost: Thor={thor_tpu_sec:.1f}s vs Baldur={baldur_tpu_sec:.1f}s "
        f"on 8 TPUv3 cores ({tpu_speedup:.2f}x ratio, excluding CPU proof checking)"
    )
    print(
        f"Portfolio (Baldur 8B ctx U Thor on 6,336-theorem PISA): union={p_union * 100:.1f}% "
        f"(+{p_baldur_only * 100:.1f} pp over Thor, +{p_thor_only * 100:.1f} pp over Baldur), "
        f"overlap~{p_intersection * 100:.1f}% [{ov_lo * 100:.2f}%, {ov_hi * 100:.2f}%], "
        f"Jaccard~{jaccard:.4f} [{jacc_lo:.3f}, {jacc_hi:.3f}]"
    )

    print("\n" + "=" * 78)
    print("PROBE 1B [derived analytical / stylized sensitivity model]:")
    print("  Exact Discrete-Budget Proof-Search Crossover Model (Zero Fractional Exponents)")
    print("=" * 78)

    def dp_monolithic(c_budget: int, p0: float, eta_uniq: float) -> float:
        """Exact discrete-budget DP for monolithic whole-proof sampling.

        Draw 1 is fresh (succeeds w.p. p0). Each subsequent draw collides with a prior
        failed draft w.p. (1 - eta_uniq) (zero new success probability, cost 1) or is
        fresh w.p. eta_uniq (succeeds w.p. p0, cost 1).
        """
        if c_budget <= 0:
            return 0.0
        dp_after = [0.0] * (c_budget + 1)
        p_hit = eta_uniq * p0
        for c in range(1, c_budget + 1):
            dp_after[c] = p_hit + (1.0 - p_hit) * dp_after[c - 1]
        return p0 + (1.0 - p0) * dp_after[c_budget - 1]

    def dp_repair(c_budget: int, p0: float, p1: float, eta_uniq: float, r_fix: float) -> float:
        """Exact discrete-budget DP for deduplicated whole-proof generate+repair.

        Eliminates dedup double-counting: duplicate failed drafts (prob 1 - eta_uniq
        after draw 1) save 1 repair unit AND receive 0 initial and 0 repair trials.
        Fresh failed drafts consume 1 repair unit (if budget allows) and recover
        single-fault drafts with conditional probability (p1 / (1 - p0)) * r_fix.
        """
        if c_budget <= 0:
            return 0.0
        if c_budget == 1:
            return p0
        cond_fix = (p1 / (1.0 - p0)) * r_fix if p0 < 1.0 else 0.0
        dp_after = [0.0] * (c_budget + 1)
        for c in range(1, c_budget + 1):
            if c >= 2:
                fresh_val = p0 + (1.0 - p0) * (cond_fix + (1.0 - cond_fix) * dp_after[c - 2])
            else:
                fresh_val = p0
            dp_after[c] = (1.0 - eta_uniq) * dp_after[c - 1] + eta_uniq * fresh_val
        return p0 + (1.0 - p0) * (cond_fix + (1.0 - cond_fix) * dp_after[c_budget - 2])

    def dp_closed_loop_tree(
        c_budget: int,
        d_steps: int,
        p_step: float,
        kappa_reencode: float,
        beta_trap: float,
        w_backtrack: int,
    ) -> float:
        """Exact discrete-budget DP for closed-loop best-first tactic tree search.

        Uses the SAME underlying per-step accuracy p_step as monolithic generation.
        Each interactive tactic call re-encodes proof state at cost kappa_reencode / d_steps
        whole-proof units, giving M = floor(C * d / kappa_reencode) tactic calls.
        At verified prefix depth h < d:
          - w.p. p_step * (1 - beta_trap): advances to depth h + 1 (prefix shared, cost 1)
          - w.p. (1 - p_step): verifier rejects immediately; prefix 0..h kept (cost 1)
          - w.p. p_step * beta_trap: enters syntactically valid dead-end subtree costing
            w_backtrack extra wasted calls before backtracking to depth h (total cost 1 + w_backtrack).
        """
        max_calls = int(math.floor(c_budget * d_steps / kappa_reencode))
        if max_calls < d_steps:
            return 0.0
        p_good = p_step * (1.0 - beta_trap)
        p_reject = 1.0 - p_step
        p_trap = p_step * beta_trap
        trap_cost = 1 + w_backtrack

        dp_next = [1.0] * (max_calls + 1)
        for _ in range(d_steps - 1, -1, -1):
            dp_cur = [0.0] * (max_calls + 1)
            for m_rem in range(1, max_calls + 1):
                val = p_good * dp_next[m_rem - 1] + p_reject * dp_cur[m_rem - 1]
                if m_rem >= trap_cost:
                    val += p_trap * dp_cur[m_rem - trap_cost]
                dp_cur[m_rem] = val
            dp_next = dp_cur
        return dp_next[max_calls]

    def dp_andor(
        c_budget: int,
        d_steps: int,
        p_step: float,
        m_subgoals: int,
        b_cap: int,
        p_sketch: float,
        early_abort: bool,
    ) -> float:
        """Exact discrete-quantum DP for hierarchical AND/OR subgoal decomposition.

        1 quantum = 1/m whole-proof unit; generating a sketch costs m quanta (1.0 unit);
        each subgoal attempt costs 1 quantum (depth d/m, success prob q_sub = p^(d/m)).
        Each subgoal is independently provable w.p. v = p_sketch^(1/m) (so all m are
        provable w.p. p_sketch). Both valid and invalid sketches use consistent geometric
        early stopping per subgoal (1..b_cap quanta on success, b_cap quanta on failure).
        """
        max_q = c_budget * m_subgoals
        q_sub = p_step ** (d_steps / m_subgoals)
        v = p_sketch ** (1.0 / m_subgoals)
        succ_probs = [v * q_sub * ((1.0 - q_sub) ** (k - 1)) for k in range(1, b_cap + 1)]
        fail_prob = (1.0 - v) + v * ((1.0 - q_sub) ** b_cap)

        dp_sketch = [0.0] * (max_q + 1)
        for rem in range(m_subgoals, max_q + 1):
            q0 = rem - m_subgoals
            if early_abort:
                alive = [0.0] * (q0 + 1)
                alive[q0] = 1.0
                prob_restart = 0.0
                for _ in range(m_subgoals):
                    next_alive = [0.0] * (q0 + 1)
                    for ql in range(1, q0 + 1):
                        pr = alive[ql]
                        if pr == 0.0:
                            continue
                        k_max = b_cap if b_cap < ql else ql
                        for k in range(1, k_max + 1):
                            next_alive[ql - k] += pr * succ_probs[k - 1]
                        if ql >= b_cap:
                            prob_restart += pr * fail_prob * dp_sketch[ql - b_cap]
                    alive = next_alive
                dp_sketch[rem] = sum(alive) + prob_restart
            else:
                ok_dist = [0.0] * (q0 + 1)
                bad_dist = [0.0] * (q0 + 1)
                ok_dist[q0] = 1.0
                for _ in range(m_subgoals):
                    next_ok = [0.0] * (q0 + 1)
                    next_bad = [0.0] * (q0 + 1)
                    for ql in range(1, q0 + 1):
                        pr_ok = ok_dist[ql]
                        if pr_ok != 0.0:
                            k_max = b_cap if b_cap < ql else ql
                            for k in range(1, k_max + 1):
                                next_ok[ql - k] += pr_ok * succ_probs[k - 1]
                            if ql >= b_cap:
                                next_bad[ql - b_cap] += pr_ok * fail_prob
                        pr_bad = bad_dist[ql]
                        if pr_bad != 0.0:
                            k_max = b_cap if b_cap < ql else ql
                            for k in range(1, k_max + 1):
                                next_bad[ql - k] += pr_bad * succ_probs[k - 1]
                            if ql >= b_cap:
                                next_bad[ql - b_cap] += pr_bad * fail_prob
                    ok_dist = next_ok
                    bad_dist = next_bad
                val = sum(ok_dist)
                for ql in range(m_subgoals, q0 + 1):
                    if bad_dist[ql] != 0.0:
                        val += bad_dist[ql] * dp_sketch[ql]
                dp_sketch[rem] = val
        return dp_sketch[max_q]

    # Mathematical boundary sanity checks (zero dedup double-counting & exact limits)
    c_budget = 24
    p_step = 0.72
    eta_uniq = 0.79
    r_loc = 0.55
    beta_trap = 0.30
    w_backtrack = 6
    m_subgoals = 4
    b_cap = 8

    for d_chk in (4, 12):
        p0_chk = p_step ** d_chk
        p1_chk = d_chk * (p_step ** (d_chk - 1)) * (1.0 - p_step)
        # 1. At eta=1.0, monolithic DP equals exact 1 - (1 - p^d)^C
        assert abs(dp_monolithic(c_budget, p0_chk, 1.0) - (1.0 - (1.0 - p0_chk) ** c_budget)) < 1e-12
        # 2. Zero-effect repair (r_fix=0) must NEVER exceed monolithic (proves zero dedup double-counting)
        assert dp_repair(c_budget, p0_chk, p1_chk, eta_uniq, 0.0) <= dp_monolithic(c_budget, p0_chk, eta_uniq) + 1e-12
        # 3. Closed-loop tree at C=1, kappa=1, beta_trap=0 has M=d calls -> exact p^d
        assert abs(dp_closed_loop_tree(1, d_chk, p_step, 1.0, 0.0, 0) - p0_chk) < 1e-12

    # Reference point at d=12, p_sketch=0.65
    d_ref = 12
    p0_ref = p_step ** d_ref
    p1_ref = d_ref * (p_step ** (d_ref - 1)) * (1.0 - p_step)
    ref_mono = dp_monolithic(c_budget, p0_ref, eta_uniq)
    ref_blind = dp_repair(c_budget, p0_ref, p1_ref, eta_uniq, r_loc / d_ref)
    ref_err = dp_repair(c_budget, p0_ref, p1_ref, eta_uniq, r_loc)
    ref_tree6 = dp_closed_loop_tree(c_budget, d_ref, p_step, 6.0, beta_trap, w_backtrack)
    ref_tree2 = dp_closed_loop_tree(c_budget, d_ref, p_step, 2.0, beta_trap, w_backtrack)
    ref_ao_u = dp_andor(c_budget, d_ref, p_step, m_subgoals, b_cap, 0.65, False)
    ref_ao_p = dp_andor(c_budget, d_ref, p_step, m_subgoals, b_cap, 0.65, True)

    assert ref_ao_p > ref_ao_u > ref_err > ref_tree6 > ref_mono > ref_blind
    assert ref_tree2 > ref_tree6

    print(
        f"Stylized reference point (C={c_budget}, d={d_ref}, p={p_step:.2f}, eta={eta_uniq:.2f}, "
        f"r_loc={r_loc:.2f}, beta_trap={beta_trap:.2f}, w_bt={w_backtrack}, m={m_subgoals}, B={b_cap}, p_sketch=0.65):"
    )
    print(f"  AND/OR + Early-Abort Pruning:          {ref_ao_p * 100:6.2f}%")
    print(f"  AND/OR Unpruned:                       {ref_ao_u * 100:6.2f}%")
    print(f"  Closed-Loop Tree Search (kappa=2x KV): {ref_tree2 * 100:6.2f}%")
    print(f"  Error-Localized Whole-Proof Repair:    {ref_err * 100:6.2f}%")
    print(f"  Closed-Loop Tree Search (kappa=6x):    {ref_tree6 * 100:6.2f}%")
    print(f"  Monolithic Whole-Proof Sampling:       {ref_mono * 100:6.2f}%")
    print(f"  Blind Whole-Proof Repair (no err msg): {ref_blind * 100:6.2f}%")

    # Full 15-cell regime sweep exhibiting ALL THREE winning paradigms under kappa=6.0:
    # (1) ErrRepair on shallow/moderate low-sketch proofs;
    # (2) AND/OR+Prune on decomposable moderate/deep proofs;
    # (3) Closed-Loop Tree Search (Tree6x) on deep non-decomposable tactical proofs!
    print(f"\n15-cell regime crossover sweep (C={c_budget}, p={p_step}, kappa=6.0 vs 2.0, m={m_subgoals}, B={b_cap}):")
    print(
        f"  {'d':>2s} {'p_sk':>5s} {'Mono':>7s} {'Blind':>7s} {'ErrRep':>7s} "
        f"{'Tree6x':>7s} {'Tree2x':>7s} {'AO_Unp':>7s} {'AO+Prn':>7s} {'Winner(k=6)':>13s}"
    )
    winners_seen: set[str] = set()
    for d_val in (4, 8, 12, 16, 20):
        p0 = p_step ** d_val
        p1 = d_val * (p_step ** (d_val - 1)) * (1.0 - p_step)
        mono = dp_monolithic(c_budget, p0, eta_uniq)
        blind = dp_repair(c_budget, p0, p1, eta_uniq, r_loc / d_val)
        err = dp_repair(c_budget, p0, p1, eta_uniq, r_loc)
        tree6 = dp_closed_loop_tree(c_budget, d_val, p_step, 6.0, beta_trap, w_backtrack)
        tree2 = dp_closed_loop_tree(c_budget, d_val, p_step, 2.0, beta_trap, w_backtrack)
        for ps in (0.10, 0.35, 0.65):
            ao_u = dp_andor(c_budget, d_val, p_step, m_subgoals, b_cap, ps, False)
            ao_p = dp_andor(c_budget, d_val, p_step, m_subgoals, b_cap, ps, True)
            assert ao_p >= ao_u - 1e-12
            cands = [
                ("ErrRepair", err),
                ("Monolithic", mono),
                ("Tree6x", tree6),
                ("AND/OR+Prune", ao_p),
            ]
            winner = max(cands, key=lambda kv: kv[1])[0]
            winners_seen.add(winner)
            print(
                f"  {d_val:2d} {ps:5.2f} {mono * 100:6.2f}% {blind * 100:6.2f}% {err * 100:6.2f}% "
                f"{tree6 * 100:6.2f}% {tree2 * 100:6.2f}% {ao_u * 100:6.2f}% {ao_p * 100:6.2f}% {winner:>13s}"
            )
    assert winners_seen == {"ErrRepair", "Tree6x", "AND/OR+Prune"}, winners_seen


# =============================================================================
# PROBE 2: AUTOVERUS/LAUREL/SAFE/VERICODING + HOUDINI REPAIR + KANI N+1 GATE
# =============================================================================

@dataclass(frozen=True)
class Conjunct:
    name: str
    pred: Callable[[int, int, int], bool]


def run_probe_2() -> None:
    print("\n" + "=" * 78)
    print("PROBE 2A [exact calculation on published dataset/equations]:")
    print("  AutoVerus (Table 2 + Phase-3 Ablation), Laurel, SAFE, & Vericoding Reconciliation")
    print("=" * 78)

    # Exact AutoVerus Table 2 repair-agent counts (arXiv:2409.13082v3 result-analysis.tex:142-179)
    # 9 error-specific repair agents + 1 Default fallback (10 total):
    # Mismatched-Type is deterministic (no LLM call) and PreCondFail never occurred on Verus-Bench,
    # leaving 7 invoked LLM error-specific agents + 1 Default fallback = 8 rows in Table 2.
    autoverus_table2 = [
        ("InvFailEnd", True, 85, 78, 91.8),
        ("Default", False, 8, 6, 75.0),
        ("PostCondFail", True, 26, 18, 69.2),
        ("AssertFailProofFunc", True, 16, 11, 68.8),
        ("InvFailFront", True, 131, 84, 64.1),
        ("PreCondFailVecLen", True, 8, 4, 50.0),
        ("AssertFail", True, 310, 145, 46.8),
        ("ArithmeticFlow", True, 73, 31, 42.5),
    ]
    n_invoked_specialists = sum(1 for _, is_spec, _, _, _ in autoverus_table2 if is_spec)
    n_fallback = sum(1 for _, is_spec, _, _, _ in autoverus_table2 if not is_spec)
    assert n_invoked_specialists == 7 and n_fallback == 1
    assert n_invoked_specialists + 2 == 9  # + Mismatched-Type (deterministic) + PreCondFail (0 hits)
    tot_calls = sum(c for _, _, c, _, _ in autoverus_table2)
    tot_succ = sum(s for _, _, _, s, _ in autoverus_table2)
    assert tot_calls == 657 and tot_succ == 377
    assert abs(round(100.0 * tot_succ / tot_calls, 1) - 57.4) < 1e-9
    for name, _, calls, succ, pub_pct in autoverus_table2:
        calc = round(100.0 * succ / calls, 1)
        assert abs(calc - pub_pct) < 1e-9, (name, calc, pub_pct)

    # Phase totals: 78 + 22 + 37 = 137 / 150 = 91.3% vs baseline 67 / 150 = 44.7%
    # Phase-3 ablation (result-analysis.tex:257): generic debugger drops Phase-3 solves 37 -> 17
    assert 78 + 22 + 37 == 137
    assert abs(round(137 / 150 * 100.0, 1) - 91.3) < 1e-9
    assert abs(round(67 / 150 * 100.0, 1) - 44.7) < 1e-9
    assert abs(round((78 + 22 + 17) / 150 * 100.0, 1) - 78.0) < 1e-9

    # SAFE (arXiv:2410.15756v3 04_experiments.tex:25, 202-210): 139-task VerusBench (150 - 11 Clover)
    n_safe = 139
    assert 150 - 11 == n_safe
    safe_checks = [
        ("GPT-4o Raw @1", 16, 11.51),
        ("GPT-4o Raw @10", 34, 24.46),
        ("GPT-4o Prompt @1", 36, 25.90),
        ("GPT-4o Prompt @10", 57, 41.01),
        ("DeepSeekCoder SAFE @1", 60, 43.17),
        ("DeepSeekCoder SAFE @10", 75, 53.96),
        ("DeepSeekCoder SAFE+ @2", 69, 49.64),
        ("DeepSeekCoder SAFE+ @100", 98, 70.50),
    ]
    for label, k_solved, pub_pct in safe_checks:
        assert abs(round(100.0 * k_solved / n_safe, 2) - pub_pct) < 1e-9, (label, k_solved, pub_pct)

    # Laurel (arXiv:2405.16792v2): 33,054 LOC = 18,316 + 10,674 + 4,064; 145 tasks = 58 + 54 + 33; 82/145 = 56.6%
    assert 18316 + 10674 + 4064 == 33054
    assert 58 + 54 + 33 == 145
    assert abs(round(82 / 145 * 100.0, 1) - 56.6) < 1e-9

    # Vericoding (arXiv:2509.22908v1 vericoding.tex:284, 960, 1545)
    assert 3029 + 2334 + 7141 == 12504
    assert 2334 + 2166 + 6368 == 10868
    lean_non_fvapps = 6368 - 4006
    assert lean_non_fvapps == 2362

    print(
        f"AutoVerus verified: 9 error-specific agents + 1 Default fallback (10 total; "
        f"7 invoked LLM specialists + 1 Default in Table 2 = {tot_succ}/{tot_calls} = "
        f"{100.0 * tot_succ / tot_calls:.2f}%); phases 78+22+37=137/150 (91.3%) vs "
        f"generic-debugger Phase-3 ablation 37->17 (117/150 = 78.0%)"
    )
    print(
        f"SAFE verified (N={n_safe} VerusBench = 150-11 Clover): GPT-4o Raw 11.51%/24.46%, "
        f"GPT-4o Prompt 25.90%/41.01%, DSC SAFE 43.17%@1/53.96%@10, DSC SAFE+ 49.64%@2/70.50%@100"
    )
    print(
        f"Laurel verified: 33,054 LOC (2,613 assertions = {2613/33054*100:.1f}%, "
        f"108 invariants = {108/33054*100:.1f}%); 82/145 = 56.6%; raw-error delta = {26.2 - 34.4:+.1f} pp"
    )
    print(
        f"Vericoding verified: 12,504 total -> 10,868 compilable (2,334 Dafny, 2,166 Verus, "
        f"6,368 Lean = 4,006 FVAPPS + {lean_non_fvapps:,} non-FVAPPS Lean)"
    )

    print("\n" + "=" * 78)
    print("PROBE 2B [derived analytical / simulation model]:")
    print("  Simultaneous-VEval Houdini Fixed-Point Pruning & Error-Code-Dispatched Repair")
    print("=" * 78)

    # Target Rust/Verus-style loop:
    #   i = 0; acc = 0;
    #   while i < n { assert(0 <= i); acc += i; i += 1; }
    # Postcondition: acc == n * (n - 1) // 2 for all n in 0..n_max.
    # Domain includes negative i (range(-2, max_i + 1)) so i >= 0 is strictly non-vacuous!
    n_max = 6
    min_i = -2
    max_i = n_max + 2
    min_acc = -2
    max_acc = (n_max + 2) * (n_max + 1) // 2 + 2

    def check_veval(conjuncts: list[Conjunct]) -> list[tuple[str, list[str]]]:
        """Collect ALL failing obligation classes simultaneously per pass (modeling VEval)."""
        errors: list[tuple[str, list[str]]] = []

        # 1. Entry check (InvFailFront): (i=0, acc=0, n in 0..n_max) |= c
        front_fails: list[str] = []
        for c in conjuncts:
            for n in range(0, n_max + 1):
                if not c.pred(0, 0, n):
                    front_fails.append(c.name)
                    break
        if front_fails:
            errors.append(("InvFailFront", front_fails))

        # 2. Inductive step check (InvFailEnd) over full signed i domain (i < n)
        end_fails: list[str] = []
        for c in conjuncts:
            broken = False
            for n in range(0, n_max + 1):
                for i in range(min_i, n):
                    for acc in range(min_acc, max_acc + 1):
                        if all(p.pred(i, acc, n) for p in conjuncts):
                            if not c.pred(i + 1, acc + i, n):
                                broken = True
                                break
                    if broken:
                        break
                if broken:
                    break
            if broken:
                end_fails.append(c.name)
        if end_fails:
            errors.append(("InvFailEnd", end_fails))

        # 3. Loop-body non-negative index assertion (AssertFail): i < n |= 0 <= i
        for n in range(0, n_max + 1):
            found_assert_cex = False
            for i in range(min_i, n):
                for acc in range(min_acc, max_acc + 1):
                    if all(p.pred(i, acc, n) for p in conjuncts):
                        if i < 0:
                            errors.append(("AssertFail", [f"cex(n={n},i={i},acc={acc})"]))
                            found_assert_cex = True
                            break
                if found_assert_cex:
                    break
            if found_assert_cex:
                break

        # 4. Postcondition check (PostCondFail): not (i < n) |= acc == n * (n - 1) // 2
        for n in range(0, n_max + 1):
            found_post_cex = False
            for i in range(n, max_i + 1):
                for acc in range(min_acc, max_acc + 1):
                    if all(p.pred(i, acc, n) for p in conjuncts):
                        if acc != n * (n - 1) // 2:
                            errors.append(("PostCondFail", [f"cex(n={n},i={i},acc={acc})"]))
                            found_post_cex = True
                            break
                if found_post_cex:
                    break
            if found_post_cex:
                break

        return errors

    c_sum = Conjunct("c_sum", lambda i, acc, n: acc == i * (i - 1) // 2)
    c_ge0 = Conjunct("c_ge0", lambda i, acc, n: i >= 0)
    c_le_n = Conjunct("c_le_n", lambda i, acc, n: i <= n)
    c_bogus_pos = Conjunct("c_bogus_pos", lambda i, acc, n: i > 0)
    c_bogus_acc0 = Conjunct("c_bogus_acc0", lambda i, acc, n: acc == 0)
    # Cascade conjunct: inductive while c_bogus_pos & c_bogus_acc0 restrict i==1,
    # then fails InvFailEnd in pass 1 once pass 0 prunes both!
    c_bogus_cascade = Conjunct("c_bogus_cascade", lambda i, acc, n: i <= 2)

    cex_re = re.compile(r"cex\(n=(-?\d+),i=(-?\d+),acc=(-?\d+)\)")

    def dispatch_repair(
        errors: list[tuple[str, list[str]]],
        pool: list[Conjunct],
    ) -> tuple[str, list[Conjunct]]:
        """Explicit error-code dispatcher matching Houdini pruning + specialist routing."""
        err_map = dict(errors)
        # Houdini phase: simultaneously drop all InvFailFront and InvFailEnd conjuncts
        drop_names: set[str] = set()
        if "InvFailFront" in err_map:
            drop_names.update(err_map["InvFailFront"])
        if "InvFailEnd" in err_map:
            drop_names.update(err_map["InvFailEnd"])
        if drop_names:
            return (
                f"HoudiniDrop({sorted(drop_names)})",
                [c for c in pool if c.name not in drop_names],
            )
        # Specialist 1: AssertFail on negative index counterexample -> synthesize i >= 0
        if "AssertFail" in err_map:
            m_cex = cex_re.fullmatch(err_map["AssertFail"][0])
            assert m_cex is not None
            _, i_val, _ = map(int, m_cex.groups())
            if i_val < 0 and all(c.name != "c_ge0" for c in pool):
                return ("RepairAssertFail(+c_ge0)", pool + [c_ge0])
        # Specialist 2: PostCondFail on overshoot counterexample (i > n) -> synthesize i <= n
        if "PostCondFail" in err_map:
            m_cex = cex_re.fullmatch(err_map["PostCondFail"][0])
            assert m_cex is not None
            n_val, i_val, _ = map(int, m_cex.groups())
            if i_val > n_val and all(c.name != "c_le_n" for c in pool):
                return ("RepairPostCondFail(+c_le_n)", pool + [c_le_n])
        raise RuntimeError(f"Unhandled verification errors: {errors}")

    # Initial LLM draft misses both bounds (c_ge0 and c_le_n) and includes 3 bogus conjuncts
    pool = [c_sum, c_bogus_pos, c_bogus_acc0, c_bogus_cascade]
    trace: list[tuple[list[tuple[str, list[str]]], str, list[str]]] = []
    for _ in range(10):
        errs = check_veval(pool)
        if not errs:
            trace.append(([], "Verified", [c.name for c in pool]))
            break
        action, next_pool = dispatch_repair(errs, pool)
        trace.append((errs, action, [c.name for c in pool]))
        pool = next_pool

    assert trace[0][0] == [
        ("InvFailFront", ["c_bogus_pos"]),
        ("InvFailEnd", ["c_bogus_acc0"]),
    ]
    assert trace[0][1] == "HoudiniDrop(['c_bogus_acc0', 'c_bogus_pos'])"
    assert trace[1][0][0] == ("InvFailEnd", ["c_bogus_cascade"])
    assert trace[1][1] == "HoudiniDrop(['c_bogus_cascade'])"
    assert trace[2][1] == "RepairAssertFail(+c_ge0)"
    assert trace[3][1] == "RepairPostCondFail(+c_le_n)"
    assert trace[4][1] == "Verified" and trace[4][2] == ["c_sum", "c_ge0", "c_le_n"]

    # Non-vacuity / irredundancy verification: dropping ANY conjunct breaks verification!
    irred_results: list[tuple[str, str]] = []
    for drop_idx in range(len(pool)):
        sub = pool[:drop_idx] + pool[drop_idx + 1 :]
        sub_errs = check_veval(sub)
        assert len(sub_errs) > 0, f"Conjunct {pool[drop_idx].name} was vacuous!"
        irred_results.append((pool[drop_idx].name, sub_errs[0][0]))
    assert dict(irred_results) == {
        "c_sum": "PostCondFail",
        "c_ge0": "AssertFail",
        "c_le_n": "PostCondFail",
    }

    for step_idx, (errs, action, invs) in enumerate(trace):
        err_str = "" if not errs else ", ".join(f"{k}:{v}" for k, v in errs)
        print(f"  Step {step_idx}: active={invs} errors=[{err_str}] -> {action}")
    print(f"  Irredundancy check (leave-one-out): {irred_results}")

    print("\n" + "=" * 78)
    print("PROBE 2C [derived analytical / simulation model]:")
    print("  Kani/CBMC N+1 Unwinding Semantics (--default-unwind 20 / --no-unwinding-checks)")
    print("  & Entry-vs-Postcondition Vacuity Separation")
    print("=" * 78)

    # Target Rust-equivalent function: loops x times (x in 0..=31), panics at iter 22.
    # Kani/CBMC N+1 rule (tutorial-loop-unwinding.md:80, autoharness/mod.rs:25, 121-123):
    # --default-unwind K evaluates the loop guard at most K times -> permits at most K-1
    # loop body iterations; x >= K triggers unwinding truncation/check failure.
    loop_unwind_default = 20
    bug_iteration = 22
    domain = list(range(0, 32))

    def run_bmc_harness(
        assume_pred: Callable[[int], bool],
        unwind_bound: int,
        unwinding_checks_enabled: bool,
    ) -> dict[str, int | bool]:
        reachable_inputs = 0
        post_witnesses = 0
        assertion_failures = 0
        unwinding_failures = 0
        truncated_paths = 0
        for x in domain:
            if not assume_pred(x):
                continue
            reachable_inputs += 1
            step = 0
            panicked = False
            truncated = False
            while step < x:
                if step >= unwind_bound - 1:
                    # Exceeds K-1 body iterations -> K-th loop-condition check still true
                    truncated = True
                    truncated_paths += 1
                    if unwinding_checks_enabled:
                        unwinding_failures += 1
                    break
                step += 1
                if step == bug_iteration:
                    panicked = True
                    assertion_failures += 1
                    break
            if not panicked and not truncated:
                post_witnesses += 1

        naive_bmc_pass = (assertion_failures == 0) and (unwinding_failures == 0)
        entry_reachable = reachable_inputs > 0
        # KaPilot negation smoke oracle: #[kani::ensures(|_| false)] must FAIL (post_witnesses > 0)
        negation_smoke_falsified = post_witnesses > 0
        vacuity_gate_flagged = not negation_smoke_falsified
        sound_verdict = (
            naive_bmc_pass
            and entry_reachable
            and negation_smoke_falsified
            and (unwinding_checks_enabled or truncated_paths == 0)
        )
        return {
            "reachable_inputs": reachable_inputs,
            "post_witnesses": post_witnesses,
            "assertion_failures": assertion_failures,
            "unwinding_failures": unwinding_failures,
            "truncated_paths": truncated_paths,
            "naive_bmc_pass": naive_bmc_pass,
            "entry_reachable": entry_reachable,
            "negation_smoke_falsified": negation_smoke_falsified,
            "vacuity_gate_flagged": vacuity_gate_flagged,
            "sound_verdict": sound_verdict,
        }

    # Case 1: Contradictory kani::assume (x >= 16 && x == 0) -> entry & post both unreachable
    case_vacuous = run_bmc_harness(lambda x: x >= 16 and x == 0, loop_unwind_default, True)
    assert case_vacuous["reachable_inputs"] == 0 and case_vacuous["post_witnesses"] == 0
    assert case_vacuous["naive_bmc_pass"] is True
    assert case_vacuous["entry_reachable"] is False
    assert case_vacuous["negation_smoke_falsified"] is False
    assert case_vacuous["vacuity_gate_flagged"] is True and case_vacuous["sound_verdict"] is False

    # Case 2: Entry-reachable but post-unreachable (x >= 20 with unwind=20, --no-unwinding-checks)
    # Separates entry_reachable (True) from negation_smoke_falsified (False)!
    case_post_vacuous = run_bmc_harness(lambda x: x >= 20, loop_unwind_default, False)
    assert case_post_vacuous["reachable_inputs"] == 12 and case_post_vacuous["post_witnesses"] == 0
    assert case_post_vacuous["truncated_paths"] == 12 and case_post_vacuous["unwinding_failures"] == 0
    assert case_post_vacuous["naive_bmc_pass"] is True
    assert case_post_vacuous["entry_reachable"] is True
    assert case_post_vacuous["negation_smoke_falsified"] is False
    assert case_post_vacuous["vacuity_gate_flagged"] is True and case_post_vacuous["sound_verdict"] is False

    # Case 3: Valid domain x <= 31, --default-unwind 20, --no-unwinding-checks -> 20 post-states, 12 truncated
    case_no_checks = run_bmc_harness(lambda x: x <= 31, loop_unwind_default, False)
    assert case_no_checks["reachable_inputs"] == 32 and case_no_checks["post_witnesses"] == 20
    assert case_no_checks["truncated_paths"] == 12 and case_no_checks["unwinding_failures"] == 0
    assert case_no_checks["assertion_failures"] == 0 and case_no_checks["naive_bmc_pass"] is True
    assert case_no_checks["sound_verdict"] is False

    # Case 4: Valid domain x <= 31, --default-unwind 20, unwinding checks ON -> catches all 12 truncated paths
    case_checks_on = run_bmc_harness(lambda x: x <= 31, loop_unwind_default, True)
    assert case_checks_on["post_witnesses"] == 20 and case_checks_on["unwinding_failures"] == 12
    assert case_checks_on["naive_bmc_pass"] is False

    # Case 5: Adequate --default-unwind 32 (31+1), unwinding checks ON -> catches all 10 panicking inputs (22..31)
    case_adequate = run_bmc_harness(lambda x: x <= 31, 32, True)
    assert case_adequate["unwinding_failures"] == 0 and case_adequate["truncated_paths"] == 0
    assert case_adequate["assertion_failures"] == 10 and case_adequate["post_witnesses"] == 22
    assert case_adequate["naive_bmc_pass"] is False and case_adequate["negation_smoke_falsified"] is True

    for label, res in [
        ("Vacuous assume (x>=16 & x==0)", case_vacuous),
        ("x>=20, unwind=20, --no-unwinding-checks", case_post_vacuous),
        ("x<=31, unwind=20, --no-unwinding-checks", case_no_checks),
        ("x<=31, unwind=20, unwinding-checks ON", case_checks_on),
        ("x<=31, unwind=32, unwinding-checks ON", case_adequate),
    ]:
        print(
            f"  {label:39s} reach={res['reachable_inputs']:2d} post={res['post_witnesses']:2d} "
            f"afail={res['assertion_failures']:2d} ufail={res['unwinding_failures']:2d} "
            f"naive={str(res['naive_bmc_pass']):5s} entry={str(res['entry_reachable']):5s} "
            f"neg_fals={str(res['negation_smoke_falsified']):5s} sound={str(res['sound_verdict']):5s}"
        )


# =============================================================================
# PROBE 3: CLUSTERED SURVIVAL, KM CENSORING, BLOCK ALPHA-MOVES, DEF-USE SZZ
# =============================================================================

RUST_KEYWORDS = frozenset({
    "let", "mut", "for", "in", "if", "else", "return", "fn", "while",
    "const", "pub", "match", "break", "continue", "true", "false", "struct",
})
TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*|[0-9]+|==|!=|<=|>=|->|\.\.|\S")
IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")


def normalize_block_tokens(lines: list[str]) -> list[str]:
    """Block-scoped consistent alpha-renaming across a multi-line code block.

    Maintains a single identifier binding table across all lines in the block so
    semantically inconsistent variable renames cannot falsely match.
    """
    mapping: dict[str, str] = {}
    normalized_lines: list[str] = []
    for line in lines:
        tokens = TOKEN_RE.findall(line)
        out: list[str] = []
        for tok in tokens:
            if IDENT_RE.fullmatch(tok) and tok not in RUST_KEYWORDS:
                if tok not in mapping:
                    mapping[tok] = f"ID{len(mapping)}"
                out.append(mapping[tok])
            else:
                out.append(tok)
        normalized_lines.append(" ".join(out))
    return normalized_lines


def kaplan_meier(events: Iterable[tuple[int, bool]], eval_days: tuple[int, ...]) -> dict[int, float]:
    """Exact product-limit Kaplan-Meier survival S(t) with right-censoring."""
    items = sorted(events, key=lambda x: x[0])
    n_at_risk = len(items)
    surv = 1.0
    by_day: dict[int, list[bool]] = {}
    for day, is_event in items:
        by_day.setdefault(day, []).append(is_event)
    curve: list[tuple[int, float]] = [(0, 1.0)]
    for day in sorted(by_day.keys()):
        d_i = sum(1 for ev in by_day[day] if ev)
        if d_i > 0 and n_at_risk > 0:
            surv *= 1.0 - (d_i / n_at_risk)
        n_at_risk -= len(by_day[day])
        curve.append((day, surv))

    out: dict[int, float] = {}
    for t in eval_days:
        val = 1.0
        for d, s in curve:
            if d <= t:
                val = s
            else:
                break
        out[t] = val
    return out


def sequence_unmodified_count(old_lines: list[str], new_lines: list[str]) -> int:
    """Count preserved lines via ordered sequence matching (respecting duplicates)."""
    matcher = difflib.SequenceMatcher(None, old_lines, new_lines, autojunk=False)
    return sum(block.size for block in matcher.get_matching_blocks())


def compute_repo_blame(
    history: list[tuple[str, dict[str, list[str]]]],
    up_to_idx: int,
) -> dict[str, list[str]]:
    """Compute per-line introducing revision across a miniature multi-commit snapshot history."""
    prev_files: dict[str, list[str]] = {}
    blame: dict[str, list[str]] = {}
    for idx in range(up_to_idx + 1):
        rev_id, files = history[idx]
        next_blame: dict[str, list[str]] = {}
        for fname, new_lines in files.items():
            old_lines = prev_files.get(fname, [])
            old_b = blame.get(fname, [])
            cur_b = [rev_id] * len(new_lines)
            if old_lines:
                sm = difflib.SequenceMatcher(None, old_lines, new_lines, autojunk=False)
                for tag, i1, i2, j1, j2 in sm.get_opcodes():
                    if tag == "equal":
                        for offset in range(i2 - i1):
                            cur_b[j1 + offset] = old_b[i1 + offset]
            next_blame[fname] = cur_b
        prev_files = files
        blame = next_blame
    return blame


def run_probe_3() -> None:
    print("\n" + "=" * 78)
    print("PROBE 3A [exact calculation on published dataset/equations]:")
    print("  Rahman et al. (arXiv:2611.21784v2) Table 5 Tracker-Inflation & Maintenance Share")
    print("=" * 78)

    # Table 5 (276,314 sampled units): line-number vs git blame -M -C identity tracking
    hs_inf = 46.8 / 18.3
    devin_inf = 63.8 / 34.9
    human_inf = 64.5 / 29.0
    primary_human_maint = 1816 / 2070 * 100.0
    assert abs(round(hs_inf, 2) - 2.56) < 1e-9
    assert abs(round(devin_inf, 2) - 1.83) < 1e-9
    assert abs(round(human_inf, 2) - 2.22) < 1e-9
    assert abs(round(primary_human_maint, 1) - 87.7) < 1e-9
    print(
        f"Line-number vs identity (-M -C) modification inflation (Table 5, N=276,314): "
        f"human-supervised={hs_inf:.2f}x (46.8% vs 18.3%), "
        f"Devin={devin_inf:.2f}x (63.8% vs 34.9%; unadjusted HR 0.992 line-num -> 1.294 identity), "
        f"human={human_inf:.2f}x (64.5% vs 29.0%)"
    )
    print(
        f"Primary per-modifying-commit human maintenance share: 1,816/2,070 = "
        f"{primary_human_maint:.2f}% (rounds 87.7%; distinct from 88.2% Sawada-design emulation)"
    )

    print("\n" + "=" * 78)
    print("PROBE 3B [derived analytical / simulation model]:")
    print("  Binary Risk-Difference Analogue: Pooled vs. Within-Stratum DEFF & Mantel-Haenszel")
    print("=" * 78)

    rng = random.Random(20261122)
    # 40 repositories: 20 fast-churn (55% base mod rate, 70% agent PR share),
    # 20 stable (18% base mod rate, 10% agent PR share); 25 PRs/repo;
    # TRUE within-repository treatment effect = 0.00!
    repo_stats: list[tuple[int, int, int, int]] = []  # (n_a, m_a, n_h, m_h)
    total_lines = 0
    for r_idx in range(40):
        fast = r_idx < 20
        base_rate = 0.55 if fast else 0.18
        agent_share = 0.70 if fast else 0.10
        repo_shock = rng.gauss(0.0, 0.05)
        n_a = m_a = n_h = m_h = 0
        for _ in range(25):
            is_agent = rng.random() < agent_share
            pr_lines = rng.randint(25, 125)
            pr_shock = rng.gauss(0.0, 0.08)
            p_mod = min(0.95, max(0.02, base_rate + repo_shock + pr_shock))
            mods = sum(1 for _ in range(pr_lines) if rng.random() < p_mod)
            total_lines += pr_lines
            if is_agent:
                n_a += pr_lines
                m_a += mods
            else:
                n_h += pr_lines
                m_h += mods
        repo_stats.append((n_a, m_a, n_h, m_h))

    assert all(na > 0 and nh > 0 for na, _, nh, _ in repo_stats)

    tot_na = sum(x[0] for x in repo_stats)
    tot_ma = sum(x[1] for x in repo_stats)
    tot_nh = sum(x[2] for x in repo_stats)
    tot_mh = sum(x[3] for x in repo_stats)
    p_a = tot_ma / tot_na
    p_h = tot_mh / tot_nh
    pooled_diff = p_a - p_h

    # 1. Naive line-independent SE
    se_naive = math.sqrt(p_a * (1.0 - p_a) / tot_na + p_h * (1.0 - p_h) / tot_nh)
    z_naive = pooled_diff / se_naive

    # 2. Pooled Liang-Zeger sandwich & repo jackknife SE (combines confounding + ICC)
    n_repos = len(repo_stats)
    u_scores = [
        (m_a - p_a * n_a) / tot_na - (m_h - p_h * n_h) / tot_nh
        for (n_a, m_a, n_h, m_h) in repo_stats
    ]
    se_lz_pooled = math.sqrt((n_repos / (n_repos - 1)) * sum(u * u for u in u_scores))

    jk_pooled: list[float] = []
    for drop_i in range(n_repos):
        na_j = tot_na - repo_stats[drop_i][0]
        ma_j = tot_ma - repo_stats[drop_i][1]
        nh_j = tot_nh - repo_stats[drop_i][2]
        mh_j = tot_mh - repo_stats[drop_i][3]
        jk_pooled.append((ma_j / na_j) - (mh_j / nh_j))
    jk_mean = sum(jk_pooled) / n_repos
    se_jk_pooled = math.sqrt(((n_repos - 1) / n_repos) * sum((v - jk_mean) ** 2 for v in jk_pooled))
    deff_lz_pooled = (se_lz_pooled / se_naive) ** 2
    deff_jk_pooled = (se_jk_pooled / se_naive) ** 2
    z_lz_pooled = pooled_diff / se_lz_pooled

    # 3. Within-repo Mantel-Haenszel stratified estimator + naive vs repo-jackknife SE
    def mh_diff(subset: list[tuple[int, int, int, int]]) -> float:
        num = 0.0
        den = 0.0
        for n_a, m_a, n_h, m_h in subset:
            w = (n_a * n_h) / (n_a + n_h)
            num += w * ((m_a / n_a) - (m_h / n_h))
            den += w
        return num / den

    strat_diff = mh_diff(repo_stats)
    w_sum = sum((n_a * n_h) / (n_a + n_h) for n_a, _, n_h, _ in repo_stats)
    var_strat_naive = 0.0
    for n_a, m_a, n_h, m_h in repo_stats:
        w = (n_a * n_h) / (n_a + n_h)
        pa_r = m_a / n_a
        ph_r = m_h / n_h
        var_strat_naive += (w ** 2) * (pa_r * (1.0 - pa_r) / n_a + ph_r * (1.0 - ph_r) / n_h)
    se_strat_naive = math.sqrt(var_strat_naive) / w_sum

    jk_strat: list[float] = []
    for drop_i in range(n_repos):
        sub = repo_stats[:drop_i] + repo_stats[drop_i + 1 :]
        jk_strat.append(mh_diff(sub))
    jk_s_mean = sum(jk_strat) / n_repos
    se_strat_jk = math.sqrt(((n_repos - 1) / n_repos) * sum((v - jk_s_mean) ** 2 for v in jk_strat))
    deff_strat_jk = (se_strat_jk / se_strat_naive) ** 2
    z_strat = strat_diff / se_strat_jk

    assert deff_lz_pooled > 20.0 and deff_jk_pooled > 20.0
    assert deff_strat_jk > 2.0  # Pure within-repo PR-cluster ICC inflation
    assert abs(z_naive) > 40.0
    assert abs(z_strat) < 1.96  # Unbiased null recovered!
    assert abs(strat_diff) < 0.02

    print(f"Cohort: {total_lines:,} lines across {n_repos} repos (true within-repo effect = 0.0000)")
    print(f"  Pooled Naive Line SE:             diff={pooled_diff:+.4f} SE={se_naive:.4f} z={z_naive:+.2f}")
    print(
        f"  Pooled Repo-Clustered (LZ/JK):    diff={pooled_diff:+.4f} "
        f"SE_LZ={se_lz_pooled:.4f} SE_JK={se_jk_pooled:.4f} z_LZ={z_lz_pooled:+.2f} "
        f"(DEFF_LZ={deff_lz_pooled:.1f}x, DEFF_JK={deff_jk_pooled:.1f}x)"
    )
    print(
        f"  Within-Repo Mantel-Haenszel + JK: diff={strat_diff:+.4f} "
        f"SE_naive={se_strat_naive:.4f} SE_JK={se_strat_jk:.4f} "
        f"DEFF_within={deff_strat_jk:.1f}x z={z_strat:+.2f} "
        f"(95% CI [{strat_diff - 1.96 * se_strat_jk:+.4f}, {strat_diff + 1.96 * se_strat_jk:+.4f}])"
    )

    print("\n" + "=" * 78)
    print("PROBE 3C [derived analytical / simulation model]:")
    print("  KM Intermediate-Censoring Crossover, Sequence/Block-Alpha Moves, Def-Use SZZ")
    print("=" * 78)

    # 1. Kaplan-Meier crossover with genuine intermediate right-censoring at day 90
    #    (shrinking n_at_risk from 96 -> 76 before day-240 clone-debt events!).
    proto_events = [(10, True)] * 18 + [(90, False)] * 20 + [(365, False)] * 62
    clone_events = [(10, True)] * 4 + [(90, False)] * 20 + [(240, True)] * 24 + [(365, False)] * 52
    km_proto = kaplan_meier(proto_events, (14, 90, 180, 365))
    km_clone = kaplan_meier(clone_events, (14, 90, 180, 365))
    expected_clone_365 = 0.96 * (52.0 / 76.0)
    naive_uncensored_clone = 1.0 - (4 + 24) / 100.0
    assert abs(km_proto[365] - 0.82) < 1e-12
    assert abs(km_clone[365] - expected_clone_365) < 1e-12
    assert km_clone[365] < naive_uncensored_clone  # Proves risk-set shrinkage at day 90!
    assert km_clone[14] > km_proto[14] and km_clone[365] < km_proto[365]
    print(
        f"  KM crossover (w/ day-90 censoring): exploratory(14d,180d,365d)="
        f"({km_proto[14]:.4f}, {km_proto[180]:.4f}, {km_proto[365]:.4f}) vs "
        f"clone-debt=({km_clone[14]:.4f}, {km_clone[180]:.4f}, {km_clone[365]:.4f}; "
        f"naive uncensored={naive_uncensored_clone:.4f})"
    )

    # 2. Sequence-aligned shift tracking (respecting duplicate lines) + block-scoped alpha renaming
    old_file = [
        "fn work(n: usize) -> usize {",
        "    let mut acc = 0;",
        "    if n > 0 {",
        "        acc += 1;",
        "    }",
        "    for k in 0..n {",
        "        acc += k;",
        "    }",
        "    acc",
        "}",
    ]
    new_file_shifted = [f"// header comment {k}" for k in range(5)] + old_file
    line_num_mod = sum(
        1 for i, txt in enumerate(old_file) if i >= len(new_file_shifted) or new_file_shifted[i] != txt
    )
    seq_identity_mod = len(old_file) - sequence_unmodified_count(old_file, new_file_shifted)
    # Negative control: deleting one of two identical "    }" lines must be caught by SequenceMatcher
    new_file_dup_deleted = [ln for idx, ln in enumerate(old_file) if idx != 4]
    seq_dup_del_mod = len(old_file) - sequence_unmodified_count(old_file, new_file_dup_deleted)
    set_dup_del_mod = sum(1 for ln in old_file if ln not in set(new_file_dup_deleted))
    assert line_num_mod == 10 and seq_identity_mod == 0
    assert seq_dup_del_mod == 1 and set_dup_del_mod == 0

    deleted_block = [
        "for idx in 0..n {",
        "    let y = buf[idx];",
        "    acc = acc + y;",
    ]
    added_consistent_block = [
        "for pos in 0..limit {",
        "    let val = slice[pos];",
        "    total = total + val;",
    ]
    added_inconsistent_block = [
        "for a in 0..b {",
        "    let c = d[e];",
        "    f = f + g;",
    ]
    exact_moves = sequence_unmodified_count(deleted_block, added_consistent_block)
    norm_del = normalize_block_tokens(deleted_block)
    norm_cons = normalize_block_tokens(added_consistent_block)
    norm_incons = normalize_block_tokens(added_inconsistent_block)
    alpha_cons_moves = sequence_unmodified_count(norm_del, norm_cons)
    alpha_incons_moves = sequence_unmodified_count(norm_del, norm_incons)
    assert exact_moves == 0 and alpha_cons_moves == 3 and norm_del == norm_cons
    assert alpha_incons_moves == 1 and norm_del != norm_incons
    print(
        f"  Shift-tracking (5-line insert): line-number={line_num_mod}/10 modified vs "
        f"sequence-identity={seq_identity_mod}/10 modified (dup-brace deletion caught: "
        f"seq={seq_dup_del_mod} vs set={set_dup_del_mod})"
    )
    print(
        f"  Block-scoped alpha-renaming:    exact={exact_moves}/3, "
        f"consistent-rename={alpha_cons_moves}/3, "
        f"inconsistent-rename={alpha_incons_moves}/3 (false positive rejected)"
    )

    # 3. Extrinsic omission-bug SZZ via real multi-commit snapshot diff + blame + def-use graph
    rev_history: list[tuple[str, dict[str, list[str]]]] = [
        (
            "rev_base",
            {
                "packet.rs": [
                    "pub struct Packet {",
                    "    pub payload: Vec<u8>,",
                    "}",
                ],
                "parser.rs": [
                    "pub fn parse_header(pkt: &Packet) -> usize {",
                    "    pkt.payload.len()",
                    "}",
                ],
            },
        ),
        (
            "rev_field",
            {
                "packet.rs": [
                    "pub struct Packet {",
                    "    pub payload: Vec<u8>,",
                    "    pub raw_len: usize,",
                    "}",
                ],
                "parser.rs": [
                    "pub fn parse_header(pkt: &Packet) -> usize {",
                    "    pkt.payload.len()",
                    "}",
                ],
            },
        ),
        (
            "rev_fix",
            {
                "packet.rs": [
                    "pub struct Packet {",
                    "    pub payload: Vec<u8>,",
                    "    pub raw_len: usize,",
                    "}",
                ],
                "parser.rs": [
                    "pub fn parse_header(pkt: &Packet) -> usize {",
                    "    if pkt.raw_len > pkt.payload.len() { return 0; }",
                    "    pkt.payload.len()",
                    "}",
                ],
            },
        ),
    ]
    bfc_idx = 2
    pre_blame = compute_repo_blame(rev_history, bfc_idx - 1)
    prev_snap = rev_history[bfc_idx - 1][1]
    curr_snap = rev_history[bfc_idx][1]

    # Parse actual diff hunks for the bug-fixing commit
    bszz_set: set[str] = set()
    added_lines_in_fix: list[tuple[str, str]] = []
    for fname, curr_lines in curr_snap.items():
        old_lines = prev_snap.get(fname, [])
        sm = difflib.SequenceMatcher(None, old_lines, curr_lines, autojunk=False)
        for tag, i1, i2, j1, j2 in sm.get_opcodes():
            if tag in ("delete", "replace"):
                for ln_idx in range(i1, i2):
                    bszz_set.add(pre_blame[fname][ln_idx])
            elif tag == "insert":
                # Pure insertion (0 deleted lines): classical B-SZZ falls back to adjacent context line
                ctx_idx = min(i1, len(old_lines) - 1)
                bszz_set.add(pre_blame[fname][ctx_idx])
                for ln_idx in range(j1, j2):
                    added_lines_in_fix.append((fname, curr_lines[ln_idx]))

    # Build symbol-definition introduction map from actual commit diffs across history[0..bfc_idx-1]
    field_def_re = re.compile(r"\bpub\s+([a-z_][a-z0-9_]*)\s*:")
    field_use_re = re.compile(r"\.([a-z_][a-z0-9_]*)\b(?!\s*\()")
    def_origin: dict[str, str] = {}
    for idx in range(bfc_idx):
        rev_id, snap = rev_history[idx]
        p_snap = rev_history[idx - 1][1] if idx > 0 else {}
        for fname, lines in snap.items():
            old_l = p_snap.get(fname, [])
            sm = difflib.SequenceMatcher(None, old_l, lines, autojunk=False)
            for tag, _, _, j1, j2 in sm.get_opcodes():
                if tag in ("insert", "replace"):
                    for ln in lines[j1:j2]:
                        for m_def in field_def_re.finditer(ln):
                            def_origin.setdefault(m_def.group(1), rev_id)

    # Identify fields newly referenced by the fix hunk that were NOT already referenced in the prior file
    dep_szz_set: set[str] = set()
    for fname, added_ln in added_lines_in_fix:
        prior_uses = {
            m.group(1) for ln in prev_snap.get(fname, []) for m in field_use_re.finditer(ln)
        }
        new_uses = {m.group(1) for m in field_use_re.finditer(added_ln)} - prior_uses
        for sym in new_uses:
            if sym in def_origin:
                dep_szz_set.add(def_origin[sym])

    bszz_bics = sorted(bszz_set)
    dep_szz_bics = sorted(dep_szz_set)
    ground_truth_bic = ["rev_field"]
    assert bszz_bics == ["rev_base"] and bszz_bics != ground_truth_bic
    assert dep_szz_bics == ground_truth_bic
    print(
        f"  Omission-bug SZZ (true BIC={ground_truth_bic}, diff-parsed def-use graph): "
        f"B-SZZ blame={bszz_bics} (miss) vs def-use SZZ={dep_szz_bics} (exact hit)"
    )


def main() -> None:
    run_probe_1()
    run_probe_2()
    run_probe_3()
    print("\nALL PROBES PASSED (0 assertion failures, pure stdlib, deterministic).")


if __name__ == "__main__":
    main()
