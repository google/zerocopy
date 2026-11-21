#!/usr/bin/env python3
"""Deterministic verification probes for agent planning, decomposition, error recovery,
and long-horizon execution.

Self-contained support script for the reference report package:
  reports/agent-planning-decomposition-error-recovery-and-long-horizon-execution/

Runtime constraints:
- Python 3.10+ standard library only, zero network calls, zero wall-clock timestamps in stdout.
- Deterministic seed = 20261121, < 3s wall-clock runtime.
- Explicit epistemic tags on every probe + decoupled negative controls:
  * Probe 1 ([derived fit to published table]):
      1A: METR TH1.1 (benchmark_results_1_1.yaml, all 26 models): log-logistic slope
          dispersion, secular trend confounding (v1.0 vs v1.1), pairwise rank inversions,
          marginal 95% CI overlap check across all p50-vs-p80 inversions (using p50/p80 CIs),
          and scaffold slope confounding (triframe vs react).
      1B: Vending-Bench (arXiv:2502.15840v1, Table 9, n=9 models): exact verification of
          Pearson r = 0.167, Spearman rho = +0.567, and leave-one-out sensitivity exposing
          single-outlier sensitivity (excluding Gemini 2.0 Pro shifts r -> +0.810).
  * Probe 2 ([toy model / mechanistic surrogate]):
      Equal-accuracy comparison of Sequential ReAct, Static Plan-Ahead DAG, Per-Step
      Dynamic Replanning, and Event-Triggered Conditional Replanning with explicit LLM
      layer-monitor overhead, imperfect surprise detection q_det (modeling ToolMaze P3/P4
      implicit failures), finite replan recovery r_rep, effective latency-per-success
      ratios, and non-vacuous W=1 / low-q_det / ungrounded-planner negative controls.
  * Probe 3 ([derived fit to published table] + [toy model / mechanistic surrogate]):
      3A: Cohort-separated verification of Looping Is Not Reliability (arXiv:2607.24604v3)
          3-revision trajectories (Qwen2.5-7B §5.1, falsifying homogeneous 2-state Markov
          extrapolation at Rev 3), frozen common-state harm (Table 3, separating 7B vs 14B),
          correlated dual-verifier risk inflation (Table 4, phi = 0.641), and stopping-gate
          safety-vs-liveness trade-offs (Table 5, 0.384 coverage vs 0.853 ever-correct).
      3B: Paired Common-Random-Numbers Monte Carlo surrogate over irreversibility gamma in
          [0, 1] with identical clean step/retry accuracy p_step = 0.72 across all policies,
          a genuinely binding call budget B = 16 over H = 6 steps (verified active across
          every policy), noisy value estimation q_val vs oracle on TreeSearch, billed
          proposal/simulation/recovery calls on Lookahead, multi-episode budget reuse on
          FreshRst, and zero stranded budget on Hybrid.
  * Probe 4 ([exact reproduction of pinned source logic] + [targeted unit-test suite]):
      Faithful reproduction of OpenHands/software-agent-sdk@3a893a1b26 stuck_detector.py
      (including conditional _tool_has_summary_param stripping) against a candidate
      thought-normalized, period-k cycle detector and a 4-case benign negative-control
      suite exposing the read-only polling precision/recall trade-off.
"""

from __future__ import annotations

import datetime
import json
import math
import random
from collections import Counter
from dataclasses import dataclass, field
from typing import Any

SEED = 20261121


# =============================================================================
# PROBE 1: [derived fit to published table]
# 1A: METR TH1.1 Logistic Slope Dispersion, 95% CI Overlap & Scaffold Confounding
# 1B: Vending-Bench Table 9 Leave-One-Out Correlation Audit
# =============================================================================
# Verbatim primary data from https://metr.org/assets/benchmark_results_1_1.yaml
# (long_tasks_version: 799cc9c4b4483a93fc3445623a49ea1bd74fdeb2,
#  swaa_version: f6cc84052e2a79dd540766c8a1b15ff399696371).
# Tuple fields:
#   (model, release_date, bench_ver, is_sota, scaffold,
#    p50_est, p50_lo, p50_hi, p80_est, p80_lo, p80_hi)
METR_TH11_DATA: list[tuple[str, str, str, bool, str, float, float, float, float, float, float]] = [
    ("gpt2", "2019-02-14", "v1.0", True, "none", 0.053778, 0.009994, 0.141825, 0.0128, 0.001589, 0.068612),
    ("davinci_002", "2020-05-28", "v1.0", True, "modular", 0.144057, 0.093319, 0.221209, 0.056238, 0.034813, 0.105813),
    ("gpt_3_5_turbo_instruct", "2022-03-15", "v1.0", True, "modular", 0.599247, 0.255148, 1.115905, 0.25538, 0.141649, 0.492933),
    ("gpt_4", "2023-03-14", "v1.1", True, "modular", 3.987428, 1.93292, 7.995283, 0.889561, 0.342984, 2.523746),
    ("gpt_4_1106_inspect", "2023-11-06", "v1.1", True, "react", 4.044959, 1.866859, 8.443226, 0.783032, 0.276599, 2.358414),
    ("claude_3_opus_inspect", "2024-03-04", "v1.1", False, "react", 3.952262, 1.706313, 8.76484, 0.638973, 0.190491, 2.118276),
    ("gpt_4_turbo_inspect", "2024-04-09", "v1.1", False, "react", 3.732787, 1.980046, 6.736613, 0.927933, 0.428277, 2.196806),
    ("gpt_4o_inspect", "2024-05-13", "v1.1", True, "react", 6.991195, 4.001482, 12.905741, 1.267009, 0.562997, 3.01517),
    ("claude_3_5_sonnet_20240620_inspect", "2024-06-20", "v1.1", True, "react", 11.395377, 5.489734, 22.384214, 1.671757, 0.57927, 4.573519),
    ("o1_preview", "2024-09-12", "v1.1", True, "duet", 20.326586, 11.716193, 33.379877, 4.420545, 2.012646, 8.912444),
    ("claude_3_5_sonnet_20241022_inspect", "2024-10-22", "v1.1", True, "react", 20.522872, 10.144026, 40.82028, 2.595677, 0.89379, 7.363864),
    ("o1_inspect", "2024-12-05", "v1.1", True, "triframe", 38.831588, 21.164512, 64.95249, 7.090121, 3.036033, 16.640636),
    ("claude_3_7_sonnet_inspect", "2025-02-24", "v1.1", True, "react", 60.388937, 33.006168, 104.226017, 12.09179, 4.575608, 28.889879),
    ("o3_inspect", "2025-04-16", "v1.1", True, "triframe", 119.732634, 74.615398, 190.943818, 29.981603, 15.127348, 57.823511),
    ("claude_4_opus_inspect", "2025-05-22", "v1.1", False, "react", 100.366123, 59.994073, 163.454074, 20.429752, 8.483125, 41.937268),
    ("claude_4_1_opus_inspect", "2025-08-05", "v1.1", False, "react", 100.472004, 59.272391, 159.451918, 23.455761, 10.538456, 47.785951),
    ("gpt_5_2025_08_07_inspect", "2025-08-07", "v1.1", True, "triframe", 203.012577, 112.641357, 405.551565, 38.312431, 19.184874, 70.093125),
    ("gemini_3_pro", "2025-11-18", "v1.1", True, "react", 224.325884, 139.565157, 379.235434, 54.142849, 25.650451, 103.295501),
    ("gpt_5_1_codex_max_inspect", "2025-11-19", "v1.1", False, "triframe", 223.714694, 134.31077, 396.206723, 50.632499, 27.30204, 88.365435),
    ("claude_opus_4_5_inspect", "2025-11-24", "v1.1", True, "react", 292.994594, 161.717714, 623.704698, 49.430584, 20.660485, 104.641318),
    ("gpt_5_2", "2025-12-11", "v1.1", True, "triframe", 352.249302, 198.067494, 815.177445, 66.002649, 31.665111, 131.730719),
    ("claude_opus_4_6_inspect", "2026-02-05", "v1.1", True, "react", 718.80683, 316.685725, 3633.786163, 69.874587, 27.026521, 170.437873),
    ("gpt_5_3_codex", "2026-02-05", "v1.1", False, "triframe", 349.530732, 194.913134, 816.351994, 54.739407, 22.361504, 122.058963),
    ("gemini_3_1_pro", "2026-02-19", "v1.1", False, "triframe", 384.147435, 233.50073, 694.750898, 89.801503, 52.025934, 158.618017),
    ("gpt_5_4", "2026-03-05", "v1.1", False, "react", 341.735276, 186.581591, 768.779526, 53.877851, 23.957027, 108.679232),
    ("claude_mythos_preview_early_inspect", "2026-04-07", "v1.1", True, "react", 1044.780145, 508.876789, 3304.261235, 185.911829, 97.30292, 398.514614),
]

# Verbatim primary data from Vending-Bench (arXiv:2502.15840v1, Table 9, p. 23):
# (model, days_until_sales_stop, days_until_full_memory)
VENDING_BENCH_T9: list[tuple[str, int, int]] = [
    ("Claude 3.5 Sonnet", 102, 51),
    ("o3-mini", 86, 52),
    ("Gemini 1.5 Pro", 35, 33),
    ("GPT-4o mini", 71, 57),
    ("Gemini 1.5 Flash", 15, 9),
    ("Claude 3.5 Haiku", 8, 32),
    ("Gemini 2.0 Flash", 50, 47),
    ("GPT-4o", 65, 50),
    ("Gemini 2.0 Pro", 25, 111),
]


def _pearson(xs: list[float], ys: list[float]) -> tuple[float, float]:
    n = len(xs)
    mx = sum(xs) / n
    my = sum(ys) / n
    cov = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    vx = sum((x - mx) ** 2 for x in xs)
    vy = sum((y - my) ** 2 for y in ys)
    return cov / vx, cov / math.sqrt(vx * vy)


def _spearman(xs: list[float], ys: list[float]) -> float:
    def _ranks(vals: list[float]) -> list[float]:
        indexed = sorted(enumerate(vals), key=lambda kv: kv[1])
        out = [0.0] * len(vals)
        i = 0
        while i < len(indexed):
            j = i
            while j + 1 < len(indexed) and indexed[j + 1][1] == indexed[i][1]:
                j += 1
            avg_rank = 0.5 * (i + j) + 1.0
            for k in range(i, j + 1):
                out[indexed[k][0]] = avg_rank
            i = j + 1
        return out

    return _pearson(_ranks(xs), _ranks(ys))[1]


def _sigmoid(z: float) -> float:
    return 1.0 / (1.0 + math.exp(-z))


def _count_inversions(items: list[dict[str, Any]], key_a: str, key_b: str) -> list[tuple[dict[str, Any], dict[str, Any]]]:
    invs: list[tuple[dict[str, Any], dict[str, Any]]] = []
    for i in range(len(items)):
        for j in range(i + 1, len(items)):
            a, b = items[i], items[j]
            if a[key_a] > b[key_a] and a[key_b] < b[key_b]:
                invs.append((a, b))
            elif b[key_a] > a[key_a] and b[key_b] < a[key_b]:
                invs.append((b, a))
    return invs


def run_probe_1() -> None:
    print("=" * 88)
    print("PROBE 1 [derived fit to published table]: METR TH1.1 & Vending-Bench Table 9 Audits")
    print("=" * 88)
    ln4 = math.log(4.0)
    ln19 = math.log(19.0)
    ln99 = math.log(99.0)

    records: list[dict[str, Any]] = []
    for row in METR_TH11_DATA:
        name, date_str, bench, is_sota, scaffold, p50, p50_lo, p50_hi, p80, p80_lo, p80_hi = row
        ratio = p50 / p80
        beta = ln4 / math.log(ratio)
        p95 = p50 * math.exp(-ln19 / beta)
        p99 = p50 * math.exp(-ln99 / beta)
        yr = (datetime.date.fromisoformat(date_str) - datetime.date(2023, 1, 1)).days / 365.25
        records.append({
            "name": name,
            "date": date_str,
            "yr": yr,
            "bench": bench,
            "sota": is_sota,
            "scaffold": scaffold,
            "p50": p50,
            "p50_lo": p50_lo,
            "p50_hi": p50_hi,
            "p80": p80,
            "p80_lo": p80_lo,
            "p80_hi": p80_hi,
            "ratio": ratio,
            "beta": beta,
            "p95": p95,
            "p99": p99,
            "p50_ci_x": p50_hi / p50_lo,
            "p80_ci_x": p80_hi / p80_lo,
        })

    v11 = [r for r in records if r["bench"] == "v1.1"]
    all_slope_yr, all_r_yr = _pearson([r["yr"] for r in records], [r["beta"] for r in records])
    v11_slope_yr, v11_r_yr = _pearson([r["yr"] for r in v11], [r["beta"] for r in v11])
    v11_mean_beta = sum(r["beta"] for r in v11) / len(v11)
    v11_min_b = min(v11, key=lambda r: r["beta"])
    v11_max_b = max(v11, key=lambda r: r["beta"])

    triframe_betas = [r["beta"] for r in v11 if r["scaffold"] == "triframe"]
    react_betas = [r["beta"] for r in v11 if r["scaffold"] == "react"]
    mean_triframe_beta = sum(triframe_betas) / len(triframe_betas)
    mean_react_beta = sum(react_betas) / len(react_betas)

    print(f"[1A] METR TH1.1 Models parsed: total={len(records)} (v1.0={len(records)-len(v11)}, v1.1={len(v11)})")
    print(f"Slope beta trend ALL 26 (v1.0+v1.1): {all_slope_yr:+.4f}/yr (Pearson r={all_r_yr:+.4f})")
    print(f"Slope beta trend v1.1 ONLY (n=23):   {v11_slope_yr:+.4f}/yr (Pearson r={v11_r_yr:+.4f})")
    print(
        f"v1.1 beta dispersion: mean={v11_mean_beta:.4f}, "
        f"min={v11_min_b['beta']:.4f} ({v11_min_b['name']}, p50/p80={v11_min_b['ratio']:.2f}x), "
        f"max={v11_max_b['beta']:.4f} ({v11_max_b['name']}, p50/p80={v11_max_b['ratio']:.2f}x)"
    )
    print(
        f"Scaffold slope confounding in v1.1: triframe (n={len(triframe_betas)}) mean beta={mean_triframe_beta:.4f} "
        f"vs react (n={len(react_betas)}) mean beta={mean_react_beta:.4f} (delta={mean_triframe_beta - mean_react_beta:+.4f})"
    )

    print("\nTop 10 v1.1 models by p50 (with point-estimate p95*/p99* extrapolations & CI spans):")
    print(f"{'Model':36s} {'Scaf':8s} {'p50':>7s} {'p80':>6s} {'50/80':>6s} {'beta':>6s} {'p95*':>6s} {'50CIx':>5s} {'80CIx':>5s}")
    for r in sorted(v11, key=lambda x: -x["p50"])[:10]:
        print(
            f"{r['name']:36s} {r['scaffold']:8s} {r['p50']:7.2f} {r['p80']:6.2f} "
            f"{r['ratio']:5.2f}x {r['beta']:6.3f} {r['p95']:6.2f} {r['p50_ci_x']:5.2f} {r['p80_ci_x']:5.2f}"
        )
    print("(*p95*/p99* extrapolate point-estimate 2-param log-logistic slopes without slope-CI propagation.)")

    total_pairs = len(v11) * (len(v11) - 1) // 2
    inv_p80 = _count_inversions(v11, "p50", "p80")
    inv_p95 = _count_inversions(v11, "p50", "p95")
    inv_p99 = _count_inversions(v11, "p50", "p99")

    # Check marginal 95% CI separation across all p50-vs-p80 point-estimate inversions:
    # Pair (a, b) has a['p50'] > b['p50'] and a['p80'] < b['p80'].
    # Marginal CI separation requires b['p50_hi'] < a['p50_lo'] or a['p80_hi'] < b['p80_lo'].
    sep_p50_ci = sum(1 for a, b in inv_p80 if b["p50_hi"] < a["p50_lo"])
    sep_p80_ci = sum(1 for a, b in inv_p80 if a["p80_hi"] < b["p80_lo"])
    assert len(inv_p80) == 9 and sep_p50_ci == 0 and sep_p80_ci == 0

    by_name = {r["name"]: r for r in v11}
    op46 = by_name["claude_opus_4_6_inspect"]
    g31 = by_name["gemini_3_1_pro"]
    assert op46["p80_lo"] < g31["p80_lo"] and g31["p80_hi"] < op46["p80_hi"], "Opus 4.6 p80 CI must enclose Gemini 3.1 Pro"

    print(f"\nv1.1 Pairwise Point-Estimate Rank Inversions (out of {total_pairs} pairs):")
    print(
        f"  p50 vs p80 (point estimates):  {len(inv_p80):2d} ({100.0*len(inv_p80)/total_pairs:5.1f}%) | "
        f"marginal 95% CI separated: {sep_p80_ci}/{len(inv_p80)} on p80, {sep_p50_ci}/{len(inv_p80)} on p50!"
    )
    print(f"  p50 vs p95* (extrapolated):    {len(inv_p95):2d} ({100.0*len(inv_p95)/total_pairs:5.1f}%)")
    print(f"  p50 vs p99* (extrapolated):    {len(inv_p99):2d} ({100.0*len(inv_p99)/total_pairs:5.1f}%)")

    print("\nPoint-Estimate Crossing q* vs Marginal 95% p80 CI Overlap on Selected Inverted Pairs:")
    for a_name, b_name in [
        ("claude_opus_4_6_inspect", "gemini_3_1_pro"),
        ("claude_opus_4_5_inspect", "gemini_3_pro"),
        ("gpt_5_4", "gemini_3_pro"),
    ]:
        a, b = by_name[a_name], by_name[b_name]
        q_star = _sigmoid(math.log(a["p50"] / b["p50"]) / (1.0 / a["beta"] - 1.0 / b["beta"]))
        print(
            f"  {a_name} ({a['scaffold']}, p80={a['p80']:.1f} [{a['p80_lo']:.1f}, {a['p80_hi']:.1f}]) vs "
            f"{b_name} ({b['scaffold']}, p80={b['p80']:.1f} [{b['p80_lo']:.1f}, {b['p80_hi']:.1f}]): "
            f"point q*={100.0*q_star:.1f}% (OVERLAPPING 95% CIs)"
        )

    # Decoupled Negative Control: constant-slope logistic produces ZERO rank inversions
    const_beta_records = [
        {
            "name": r["name"],
            "p50": r["p50"],
            "p80": r["p50"] * math.exp(-ln4 / v11_mean_beta),
            "p95": r["p50"] * math.exp(-ln19 / v11_mean_beta),
            "p99": r["p50"] * math.exp(-ln99 / v11_mean_beta),
        }
        for r in v11
    ]
    nc_80 = len(_count_inversions(const_beta_records, "p50", "p80"))
    nc_95 = len(_count_inversions(const_beta_records, "p50", "p95"))
    nc_99 = len(_count_inversions(const_beta_records, "p50", "p99"))
    assert nc_80 == 0 and nc_95 == 0 and nc_99 == 0
    print(f"[NEG-CTRL 1A - Constant beta={v11_mean_beta:.4f}]: inversions p80={nc_80}, p95={nc_95}, p99={nc_99} (PASS).")

    # Part 1B: Vending-Bench Table 9 outlier sensitivity
    vb_stop = [float(r[1]) for r in VENDING_BENCH_T9]
    vb_mem = [float(r[2]) for r in VENDING_BENCH_T9]
    _, r_all = _pearson(vb_stop, vb_mem)
    rho_all = _spearman(vb_stop, vb_mem)
    vb_no_g2p = [r for r in VENDING_BENCH_T9 if r[0] != "Gemini 2.0 Pro"]
    _, r_no_g2p = _pearson([float(r[1]) for r in vb_no_g2p], [float(r[2]) for r in vb_no_g2p])
    rho_no_g2p = _spearman([float(r[1]) for r in vb_no_g2p], [float(r[2]) for r in vb_no_g2p])
    post_mem_count = sum(1 for _, s, m in VENDING_BENCH_T9 if s > m)
    assert abs(r_all - 0.1668) < 1e-3 and abs(r_no_g2p - 0.8099) < 1e-3
    print(
        f"\n[1B] Vending-Bench Table 9 (n=9): Pearson r={r_all:+.3f}, Spearman rho={rho_all:+.3f} | "
        f"excl. single outlier Gemini 2.0 Pro (25d vs 111d, n=8): Pearson r={r_no_g2p:+.3f}, "
        f"Spearman rho={rho_no_g2p:+.3f} ({post_mem_count}/9 models stop AFTER memory fills)."
    )


# =============================================================================
# PROBE 2: [toy model / mechanistic surrogate]
# Equal-Accuracy DAG vs ReAct vs Dynamic Replanning with Imperfect Surprise Detection
# =============================================================================
def _dag_metrics(
    width: int,
    depth: int,
    p_surp: float,
    q_det: float = 0.90,
    r_rep: float = 0.88,
    c_chk: float = 1.00,
    q_fp: float = 0.03,
    l_llm: float = 0.85,
    l_tool: float = 0.60,
    t0: int = 450,
    dt: int = 240,
    eps_step: float = 0.015,
    delta_eps_plan: float = 0.0,
) -> dict[str, dict[str, float]]:
    """Closed-form latency, token cost, success rate, and effective latency-per-success.

    Fairness invariants:
    - ZERO unearned step-error discounts: all strategies share baseline `eps_step`
      (with optional `delta_eps_plan` sensitivity for planner grounding mismatch).
    - NO free surprise oracle: `CondReplan_DAG` pays `c_chk` LLM-call equivalents per
      layer to verify outputs (c_chk=1.0 for semantic LLM check, c_chk=0.0 only for
      syntactic exit-code check), detects surprises with imperfect recall `q_det`
      (capturing ToolMaze P3/P4 implicit semantic failures when q_det is low), incurs
      false-positive replans at rate `q_fp`, and recovers a detected surprise with
      finite probability `r_rep < 1`.
    """
    n_tools = width * depth
    step_surv = (1.0 - eps_step) ** n_tools
    plan_eps = min(0.99, max(0.0, eps_step + delta_eps_plan))
    plan_step_surv = (1.0 - plan_eps) ** n_tools
    adapt_layer_surv = (1.0 - p_surp) + p_surp * q_det * r_rep

    # 1. Sequential ReAct: inspects each observation inline during its (N + 1) base turns;
    # on detected surprise (D * p_surp * q_det), executes 1 corrective LLM + tool turn.
    exp_det = depth * p_surp * q_det
    n_react_turns = n_tools + exp_det
    react_lat = (n_react_turns + 1.0) * l_llm + n_react_turns * l_tool
    react_tok = (n_react_turns + 1.0) * t0 + (n_react_turns * (n_react_turns + 1.0) / 2.0) * dt
    react_succ = (adapt_layer_surv ** depth) * step_surv

    # 2. Static Plan-Ahead DAG (ReWOO / open-loop LLMCompiler): 1 Planner + D waves + 1 Solver.
    static_lat = 2.0 * l_llm + depth * l_tool
    static_tok = 2.0 * t0 + n_tools * dt
    static_succ = ((1.0 - p_surp) ** depth) * plan_step_surv

    # 3. Per-Step Dynamic Replanning (Plan-and-Act): Planner + Executor at every step.
    n_ps_steps = n_tools + exp_det
    perstep_lat = (2.0 * n_ps_steps + 1.0) * l_llm + n_ps_steps * l_tool
    perstep_tok = (2.0 * n_ps_steps + 1.0) * t0 + (n_ps_steps * (n_ps_steps + 1.0) * 0.75) * dt
    perstep_succ = (adapt_layer_surv ** depth) * plan_step_surv

    # 4. Event-Triggered Conditional Replan (LLMCompiler Joiner / ADaPT):
    # 1 Planner + D parallel waves + D * c_chk layer-monitor calls + D * p_trig replans + 1 Solver.
    p_trig = p_surp * q_det + (1.0 - p_surp) * q_fp
    exp_rep = depth * p_trig
    cond_llm_calls = 2.0 + depth * c_chk + exp_rep
    cond_lat = cond_llm_calls * l_llm + (depth + exp_rep) * l_tool
    cond_tok = cond_llm_calls * t0 + n_tools * (1.0 + 0.5 * p_trig) * dt
    cond_succ = (adapt_layer_surv ** depth) * plan_step_surv

    out: dict[str, dict[str, float]] = {}
    for name, lat, tok, succ in [
        ("ReAct", react_lat, react_tok, react_succ),
        ("StaticDAG", static_lat, static_tok, static_succ),
        ("PlanAndAct_PerStep", perstep_lat, perstep_tok, perstep_succ),
        ("CondReplan_DAG", cond_lat, cond_tok, cond_succ),
    ]:
        out[name] = {
            "lat_s": lat,
            "tokens": tok,
            "succ": succ,
            "lat_per_succ": lat / max(succ, 1e-9),
            "tok_per_succ": tok / max(succ, 1e-9),
        }
    return out


def _solve_static_crossover(width: int, depth: int, q_det: float = 0.90, r_rep: float = 0.88) -> float:
    """Solve p_surp* in [0, 0.999] where StaticDAG lat_per_succ == ReAct lat_per_succ."""
    m0 = _dag_metrics(width, depth, 0.0, q_det=q_det, r_rep=r_rep)
    if m0["StaticDAG"]["lat_per_succ"] >= m0["ReAct"]["lat_per_succ"]:
        return 0.0
    lo, hi = 0.0, 0.999
    for _ in range(60):
        mid = 0.5 * (lo + hi)
        mm = _dag_metrics(width, depth, mid, q_det=q_det, r_rep=r_rep)
        if mm["StaticDAG"]["lat_per_succ"] < mm["ReAct"]["lat_per_succ"]:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def run_probe_2() -> None:
    print("\n" + "=" * 88)
    print("PROBE 2 [toy model / mechanistic surrogate]: Equal-Accuracy DAG vs ReAct vs Replanning")
    print("=" * 88)

    scenarios = [
        ("HotpotQA-like (W=2,D=1,p=0.00)", 2, 1, 0.00),
        ("MovieRec-like (W=8,D=1,p=0.00)", 8, 1, 0.00),
        ("ParallelQA-like (W=3,D=2,p=0.05)", 3, 2, 0.05),
        ("Mixed DAG (W=2,D=4,p=0.25)", 2, 4, 0.25),
        ("WebShop Seq (W=1,D=6,p=0.35)", 1, 6, 0.35),
    ]
    print("Effective Latency-per-Success (s/succ) & Task SR (equal eps_step=0.015, c_chk=1.0 LLM monitor, q_det=0.90, r_rep=0.88):")
    print(
        f"{'Scenario':31s} | {'ReAct (eff/sr)':>16s} | {'Static (eff/sr)':>17s} | "
        f"{'CondDAG (eff/sr)':>17s} | {'EffSpd(St/Cd)':>14s}"
    )
    for label, w, d, ps in scenarios:
        m = _dag_metrics(w, d, ps, q_det=0.90, r_rep=0.88, c_chk=1.00)
        ra, st, cd = m["ReAct"], m["StaticDAG"], m["CondReplan_DAG"]
        eff_st = ra["lat_per_succ"] / st["lat_per_succ"]
        eff_cd = ra["lat_per_succ"] / cd["lat_per_succ"]
        print(
            f"{label:31s} | "
            f"{ra['lat_per_succ']:5.1f}s / {100*ra['succ']:4.1f}% | "
            f"{st['lat_per_succ']:6.1f}s / {100*st['succ']:4.1f}% | "
            f"{cd['lat_per_succ']:5.1f}s / {100*cd['succ']:4.1f}% | "
            f"{eff_st:4.2f}x / {eff_cd:4.2f}x"
        )

    # Verify exact equality of SR at p_surp=0 (zero unearned accuracy bonus)
    m_zero = _dag_metrics(4, 2, 0.0)
    assert abs(m_zero["ReAct"]["succ"] - m_zero["StaticDAG"]["succ"]) < 1e-12
    assert abs(m_zero["ReAct"]["succ"] - m_zero["CondReplan_DAG"]["succ"]) < 1e-12
    assert abs(m_zero["ReAct"]["succ"] - m_zero["PlanAndAct_PerStep"]["succ"]) < 1e-12

    print("\nCrossover p_surp* where StaticDAG loses Effective Latency-per-Success to ReAct (q_det=0.90, r_rep=0.88):")
    print(f"{'W \\ D':6s} | {'D=1':>8s} | {'D=2':>8s} | {'D=4':>8s} | {'D=6':>8s} | {'D=8':>8s}")
    for w in (1, 2, 4, 8):
        vals = [f"{100.0 * _solve_static_crossover(w, d):7.1f}%" for d in (1, 2, 4, 6, 8)]
        print(f"W={w:<4d} | " + " | ".join(vals))

    # Sensitivity to surprise-detection recall q_det (ToolMaze explicit P1/P2 vs implicit P3/P4)
    m_exp = _dag_metrics(2, 4, 0.35, q_det=0.92, r_rep=0.88, c_chk=1.00)
    m_imp = _dag_metrics(2, 4, 0.35, q_det=0.15, r_rep=0.88, c_chk=1.00)
    assert m_imp["CondReplan_DAG"]["succ"] < 0.25 < m_exp["CondReplan_DAG"]["succ"]
    print(
        f"\nImplicit-Anomaly Sensitivity (W=2, D=4, p_surp=0.35): "
        f"CondReplan_DAG SR drops from {100*m_exp['CondReplan_DAG']['succ']:.1f}% (explicit q_det=0.92) "
        f"to {100*m_imp['CondReplan_DAG']['succ']:.1f}% (implicit ToolMaze P3/P4 q_det=0.15)."
    )

    # Non-vacuous Negative Controls:
    # NC1: At W=1 (sequential WebShop), zero parallel tool waves -> CondReplan_DAG (with LLM monitor c_chk=1.0)
    #      and PlanAndAct_PerStep BOTH have strictly worse latency-per-success than ReAct!
    nc_w1 = _dag_metrics(1, 6, 0.35, q_det=0.90, r_rep=0.88, c_chk=1.00)
    static_tool_time = nc_w1["StaticDAG"]["lat_s"] - 2.0 * 0.85
    react_base_tool_time = _dag_metrics(1, 6, 0.0)["ReAct"]["lat_s"] - 7.0 * 0.85
    assert abs(static_tool_time - react_base_tool_time) < 1e-12
    assert nc_w1["StaticDAG"]["lat_per_succ"] > 3.0 * nc_w1["ReAct"]["lat_per_succ"]
    assert nc_w1["CondReplan_DAG"]["lat_per_succ"] > nc_w1["ReAct"]["lat_per_succ"]
    assert nc_w1["PlanAndAct_PerStep"]["lat_per_succ"] > nc_w1["CondReplan_DAG"]["lat_per_succ"]

    # NC2: Ungrounded planner penalty (Plan-and-Act Table 1: base planner hurts finetuned executor)
    nc_ungrounded = _dag_metrics(2, 3, 0.10, delta_eps_plan=0.10)
    assert nc_ungrounded["CondReplan_DAG"]["succ"] < nc_ungrounded["ReAct"]["succ"] - 0.30
    print(
        f"[NEG-CTRL 2A - Sequential W=1, D=6, c_chk=1.0]: ReAct eff_lat={nc_w1['ReAct']['lat_per_succ']:.2f}s "
        f"beats CondReplan_DAG={nc_w1['CondReplan_DAG']['lat_per_succ']:.2f}s, "
        f"PlanAndAct={nc_w1['PlanAndAct_PerStep']['lat_per_succ']:.2f}s, & "
        f"StaticDAG={nc_w1['StaticDAG']['lat_per_succ']:.2f}s (PASS: CondDAG loses without parallelism)."
    )
    print(
        f"[NEG-CTRL 2B - Ungrounded Planner delta_eps=+0.10]: CondReplan_DAG SR={100*nc_ungrounded['CondReplan_DAG']['succ']:.1f}% "
        f"< ReAct SR={100*nc_ungrounded['ReAct']['succ']:.1f}% (PASS)."
    )


# =============================================================================
# PROBE 3: [derived fit to published table] + [toy model / mechanistic surrogate]
# Part 3A: Cohort-Separated Audit & Correlated-Verifier Frontier (arXiv:2607.24604v3)
# Part 3B: Strict-Budget Irreversibility gamma CRN Surrogate (Equal Step Accuracy)
# =============================================================================
# Verbatim 3-revision trajectories on Qwen2.5-7B-Instruct (arXiv:2607.24604v3 §5.1, n=900):
LOOPING_7B_TRAJECTORIES: dict[str, tuple[float, float, float]] = {
    "current_trace": (0.820, 0.673, 0.693),
    "ever_correct_current_trace": (0.820, 0.847, 0.853),
    "current_binary": (0.700, 0.700, 0.720),
    "stale_trace": (0.687, 0.713, 0.660),
    "unavailable": (0.687, 0.687, 0.707),
}

# Verbatim Table 3 frozen common-state branch counts out of 135 (arXiv:2607.24604v3 §5.2):
LOOPING_TABLE3_135: dict[str, dict[str, int]] = {
    "Qwen2.5-7B": {
        "wrong_curr_bin": 105, "wrong_curr_trace": 113, "wrong_unavail": 97, "wrong_ctrl": 105,
        "corr_curr_bin": 0, "corr_curr_trace": 5, "corr_unavail": 0, "corr_stale": 12, "corr_ctrl": 2,
    },
    "Qwen2.5-14B": {
        "wrong_curr_bin": 115, "wrong_curr_trace": 120, "wrong_unavail": 126, "wrong_ctrl": 119,
        "corr_curr_bin": 4, "corr_curr_trace": 4, "corr_unavail": 10, "corr_stale": 34, "corr_ctrl": 17,
    },
}

# Verbatim Table 5 stopping-policy replay over 900 trajectories (cov, risk, sound, rounds):
LOOPING_TABLE5: list[tuple[str, float, float, float, float]] = [
    ("Self only", 0.998, 0.295, 0.703, 1.03),
    ("Self + visible", 0.797, 0.024, 0.778, 1.55),
    ("Qwen-14B only", 0.794, 0.046, 0.758, 1.52),
    ("Challenge executable", 0.788, 0.000, 0.788, 1.52),
    ("Qwen-14B + fresh challenge", 0.384, 0.000, 0.384, 2.27),
]


def _simulate_gamma_grid(
    horizon: int = 6,
    budget: int = 16,
    p_step: float = 0.72,
    c_drag: float = 0.30,
    q_wm: float = 0.84,
    q_val_real: float = 0.88,
    n_episodes: int = 4000,
) -> tuple[dict[float, dict[str, float]], Counter[str]]:
    """Paired Common-Random-Numbers (CRN) strict-budget Monte Carlo across gamma in [0, 1].

    Strict symmetry invariants:
    - Every policy shares identical clean per-step action accuracy `p_step` (and clean
      rewind retry accuracy = `p_step`, NEVER inflated above `p_step`).
    - Un-rewound forward recovery (`Continue`, `Lookahead` post-leak) faces polluted-context
      drag `p_step * (1 - c_drag)`.
    - Strict LLM call ceiling `calls <= budget` is enforced on EVERY policy:
      * `Continue`: 1 call/step + 1 call per in-place repair attempt while `calls < budget`.
      * `FreshRst`: 1 call/step; on reversible failure, resets sandbox to step 0 and reuses
        ALL remaining calls (`calls < budget`) across fresh attempts until budget exhausts
        or an irreversible external side effect poisons the environment.
      * `SyncRewind`: 1 call/step + 1 call per clean checkpoint retry (`p_step`) while
        `calls < budget`.
      * `TreeSearch` (noisy `q_val_real` & reference `TreeOracle` `1.0`): 1 policy proposal
        call + up to 3 live-environment branch evaluations per step (1 evaluator call per
        checked candidate, reserving >=1 call per remaining step), plus billed clean rewind
        calls if a false-positive bad branch is selected.
      * `Lookahead`: identical `(1 + k)` proposal + mental world-model simulation call cost
        BEFORE touching the live environment (rejected bad candidates never execute live!),
        plus billed in-place recovery calls if a false-positive bad action executes live.
      * `Hybrid`: identical adaptive mental screening to `Lookahead` + clean `SyncRewind`
        fallback on reversible false positives (zero stranded calls; exact CRN convergence
        `Hybrid == Lookahead` and `Continue == SyncRewind` at gamma = 1.0).
    """
    gammas = [0.0, 0.1, 0.2, 0.3, 0.5, 0.8, 1.0]
    results: dict[float, dict[str, float]] = {}
    exhausted_totals: Counter[str] = Counter()

    for g_idx, gamma in enumerate(gammas):
        rng = random.Random(SEED + 1009 * g_idx)
        wins: Counter[str] = Counter()
        for _ in range(n_episodes):
            # Pre-draw episode CRN tape: max `budget` action draws, `budget` irrev draws, `budget` eval draws
            u_act = [rng.random() for _ in range(budget + 4)]
            u_irr = [rng.random() for _ in range(budget + 4)]
            u_evl = [rng.random() for _ in range(budget + 4)]

            # 1. Continue
            calls = 0
            idx = 0
            ok = True
            for _s in range(horizon):
                if calls >= budget:
                    exhausted_totals["Continue"] += 1
                    ok = False
                    break
                calls += 1
                good = u_act[idx] < p_step
                irr = u_irr[idx] < gamma
                idx += 1
                if good:
                    continue
                if irr:
                    ok = False
                    break
                fixed = False
                while calls < budget:
                    calls += 1
                    good_r = u_act[idx] < (p_step * (1.0 - c_drag))
                    irr_r = u_irr[idx] < gamma
                    idx += 1
                    if good_r:
                        fixed = True
                        break
                    if irr_r:
                        ok = False
                        break
                if not ok:
                    break
                if not fixed:
                    exhausted_totals["Continue"] += 1
                    ok = False
                    break
            if ok:
                wins["Continue"] += 1

            # 2. FreshRst (reuses ALL remaining budget across restarts)
            calls = 0
            idx = 0
            ok_any = False
            poisoned = False
            while calls < budget and not poisoned:
                ep_ok = True
                for _s in range(horizon):
                    if calls >= budget:
                        exhausted_totals["FreshRst"] += 1
                        ep_ok = False
                        break
                    calls += 1
                    good = u_act[idx] < p_step
                    irr = u_irr[idx] < gamma
                    idx += 1
                    if good:
                        continue
                    if irr:
                        poisoned = True
                    ep_ok = False
                    break
                if ep_ok:
                    ok_any = True
                    break
            if ok_any:
                wins["FreshRst"] += 1

            # 3. SyncRewind (clean p_step on both initial and rewind attempts)
            calls = 0
            idx = 0
            ok = True
            for _s in range(horizon):
                if calls >= budget:
                    exhausted_totals["SyncRewind"] += 1
                    ok = False
                    break
                calls += 1
                good = u_act[idx] < p_step
                irr = u_irr[idx] < gamma
                idx += 1
                if good:
                    continue
                if irr:
                    ok = False
                    break
                fixed = False
                while calls < budget:
                    calls += 1
                    good_r = u_act[idx] < p_step
                    irr_r = u_irr[idx] < gamma
                    idx += 1
                    if good_r:
                        fixed = True
                        break
                    if irr_r:
                        ok = False
                        break
                if not ok:
                    break
                if not fixed:
                    exhausted_totals["SyncRewind"] += 1
                    ok = False
                    break
            if ok:
                wins["SyncRewind"] += 1

            # 4. TreeSearch (noisy q_val_real and Oracle 1.0 reference)
            for ts_name, qv in (("TreeSearch", q_val_real), ("TreeOracle", 1.0)):
                calls = 0
                idx = 0
                ok = True
                for _s in range(horizon):
                    rem_after = horizon - 1 - _s
                    if budget - calls <= rem_after:
                        exhausted_totals[ts_name] += 1
                        ok = False
                        break
                    calls += 1  # policy proposes candidate list
                    max_evals = min(3, budget - calls - rem_after)
                    if max_evals <= 0:
                        good = u_act[idx] < p_step
                        idx += 1
                        if not good:
                            ok = False
                            break
                        continue
                    chosen_good = None
                    irrev = False
                    for _j in range(max_evals):
                        good = u_act[idx] < p_step
                        irr = u_irr[idx] < gamma
                        ev = u_evl[idx]
                        idx += 1
                        # Live execution occurs BEFORE post-state value evaluation!
                        if not good and irr:
                            irrev = True
                            break
                        calls += 1  # value-function call
                        accept = (ev < qv) if good else (ev < (1.0 - qv))
                        if accept or _j == max_evals - 1:
                            chosen_good = good
                            break
                    if irrev:
                        ok = False
                        break
                    if not chosen_good:
                        fixed = False
                        while budget - calls > rem_after:
                            calls += 1
                            good_r = u_act[idx] < p_step
                            irr_r = u_irr[idx] < gamma
                            idx += 1
                            if good_r:
                                fixed = True
                                break
                            if irr_r:
                                ok = False
                                break
                        if not ok:
                            break
                        if not fixed:
                            exhausted_totals[ts_name] += 1
                            ok = False
                            break
                if ok:
                    wins[ts_name] += 1

            # 5 & 6. Lookahead (c_drag fallback) & Hybrid (clean SyncRewind fallback, p_step)
            for la_name, retry_p in (("Lookahead", p_step * (1.0 - c_drag)), ("Hybrid", p_step)):
                calls = 0
                idx = 0
                ok = True
                for _s in range(horizon):
                    rem_after = horizon - 1 - _s
                    if budget - calls <= rem_after:
                        exhausted_totals[la_name] += 1
                        ok = False
                        break
                    calls += 1  # policy proposes candidate list
                    max_evals = min(3, budget - calls - rem_after)
                    if max_evals <= 0:
                        chosen_good = u_act[idx] < p_step
                        chosen_irr = u_irr[idx] < gamma
                        idx += 1
                    else:
                        chosen_good = False
                        chosen_irr = False
                        for _j in range(max_evals):
                            good = u_act[idx] < p_step
                            irr = u_irr[idx] < gamma
                            ev = u_evl[idx]
                            idx += 1
                            calls += 1  # mental WM simulation + score call BEFORE live exec
                            accept = (ev < q_wm) if good else (ev < (1.0 - q_wm))
                            if accept or _j == max_evals - 1:
                                chosen_good = good
                                chosen_irr = irr
                                break
                    # Execute ONLY the single accepted candidate in the live environment!
                    if not chosen_good:
                        if chosen_irr:
                            ok = False
                            break
                        fixed = False
                        while budget - calls > rem_after:
                            calls += 1
                            good_r = u_act[idx] < retry_p
                            irr_r = u_irr[idx] < gamma
                            idx += 1
                            if good_r:
                                fixed = True
                                break
                            if irr_r:
                                ok = False
                                break
                        if not ok:
                            break
                        if not fixed:
                            exhausted_totals[la_name] += 1
                            ok = False
                            break
                if ok:
                    wins[la_name] += 1

        results[gamma] = {
            k: wins[k] / n_episodes
            for k in ("Continue", "FreshRst", "SyncRewind", "TreeSearch", "TreeOracle", "Lookahead", "Hybrid")
        }
    return results, exhausted_totals


def run_probe_3() -> None:
    print("\n" + "=" * 88)
    print("PROBE 3 [derived fit + mechanistic surrogate]: Continuation Harm & Irreversibility gamma")
    print("=" * 88)

    # --- Part 3A: Cohort-Separated Audit of arXiv:2607.24604v3 ---
    r1, r2, r3_actual = LOOPING_7B_TRAJECTORIES["current_trace"]
    e1, e2, e3_actual = LOOPING_7B_TRAJECTORIES["ever_correct_current_trace"]
    p_fix_12 = (e2 - r1) / (1.0 - r1)
    p_reg_12 = 1.0 - (r2 - (1.0 - r1) * p_fix_12) / r1
    r3_homog_markov = r2 * (1.0 - p_reg_12) + (1.0 - r2) * p_fix_12
    markov_err_pp = 100.0 * (r3_homog_markov - r3_actual)
    assert abs(r3_homog_markov - 0.5792) < 1e-3 and markov_err_pp < -11.0

    t3_7b = LOOPING_TABLE3_135["Qwen2.5-7B"]
    t3_14b = LOOPING_TABLE3_135["Qwen2.5-14B"]
    harm_7b_stale = t3_7b["corr_stale"] / 135.0
    harm_7b_curr = t3_7b["corr_curr_trace"] / 135.0
    harm_14b_stale = t3_14b["corr_stale"] / 135.0
    harm_14b_curr = t3_14b["corr_curr_trace"] / 135.0
    harm_14b_ctrl = t3_14b["corr_ctrl"] / 135.0

    # Correlated dual-verifier AND-gate risk (Table 4: Qwen-7B / Qwen-14B conditional phi = 0.641 on wrong revisions)
    # With marginal false-accept rates f1=0.16, f2=0.14 on incorrect candidates:
    f1, f2, phi_emp = 0.16, 0.14, 0.641
    joint_fa_indep = f1 * f2
    joint_fa_corr = f1 * f2 + phi_emp * math.sqrt(f1 * (1.0 - f1) * f2 * (1.0 - f2))
    corr_inflation = joint_fa_corr / joint_fa_indep

    print("[Part 3A - Cohort-Separated Audit & Verifier Selection (arXiv:2607.24604v3)]")
    print(
        f"  Qwen2.5-7B 3-rev trajectories (§5.1, n=900): current_trace={r1:.3f}->{r2:.3f}->{r3_actual:.3f} "
        f"(ever={e1:.3f}->{e2:.3f}->{e3_actual:.3f}); stale_trace={LOOPING_7B_TRAJECTORIES['stale_trace']}"
    )
    print(
        f"  Homogeneous 2-state Markov falsification: Rev1->2 fit (p_fix={p_fix_12:.3f}, p_reg={p_reg_12:.4f}) "
        f"predicts Rev3={r3_homog_markov:.4f} vs observed {r3_actual:.3f} (error={markov_err_pp:+.2f} pp; non-monotone!)."
    )
    print(
        f"  Table 3 Frozen Common-State (135/cell, strictly unpooled): "
        f"7B stale harm={t3_7b['corr_stale']}/135 ({100*harm_7b_stale:.1f}%) vs curr={t3_7b['corr_curr_trace']}/135 ({100*harm_7b_curr:.1f}%, Holm p=1.0) | "
        f"14B stale harm={t3_14b['corr_stale']}/135 ({100*harm_14b_stale:.1f}%) vs curr={t3_14b['corr_curr_trace']}/135 "
        f"({100*(harm_14b_stale-harm_14b_curr):+.1f} pp, Holm p=0.0337; vs ctrl 17/135: {100*(harm_14b_stale-harm_14b_ctrl):+.1f} pp, Holm p=0.3934)."
    )
    print(
        f"  Table 4 Correlated Verifier Gate (phi={phi_emp:.3f} on wrong revisions): "
        f"AND-gate false-accept={100*joint_fa_corr:.2f}% vs {100*joint_fa_indep:.2f}% under phi=0 ({corr_inflation:.2f}x inflation)."
    )
    t5_self = LOOPING_TABLE5[0]
    t5_exec = LOOPING_TABLE5[3]
    t5_fresh = LOOPING_TABLE5[4]
    assert t5_fresh[3] < e3_actual - 0.45
    print(
        f"  Table 5 Imperfect Selection vs Ever-Correct ({e3_actual:.3f}): "
        f"Self-only sound={t5_self[3]:.3f} (risk={t5_self[2]:.3f}) | "
        f"Exec-challenge sound={t5_exec[3]:.3f} | "
        f"Qwen-14B+fresh-challenge sound={t5_fresh[3]:.3f} (cov={t5_fresh[1]:.3f}, {100*(t5_fresh[3]-e3_actual):+.1f} pp below ever-correct!)."
    )

    # --- Part 3B: Strict Call-Budgeted Irreversibility gamma CRN Surrogate ---
    results_by_gamma, exh_totals = _simulate_gamma_grid(
        horizon=6, budget=16, p_step=0.72, c_drag=0.30, q_wm=0.84, q_val_real=0.88, n_episodes=4000
    )
    # Verify ZERO dead budget checks: every single policy hits the B=16 ceiling > 0 times!
    for pol in ("Continue", "FreshRst", "SyncRewind", "TreeSearch", "TreeOracle", "Lookahead", "Hybrid"):
        assert exh_totals[pol] > 0, f"Dead budget guard on {pol}"

    print("\n[Part 3B - Strict-Budget Irreversibility gamma CRN Surrogate (N=4000/cell, H=6, B=16 calls, equal p_step=0.72)]")
    print(
        f"{'gamma':>5s} | {'Continue':>8s} | {'FreshRst':>8s} | {'SyncRW':>7s} | "
        f"{'Tree(q=.88)':>11s} | {'Tree(Orac)':>10s} | {'Lookahead':>9s} | {'Hybrid':>7s}"
    )
    for gamma, r in results_by_gamma.items():
        print(
            f"{gamma:5.2f} | {100*r['Continue']:7.1f}% | {100*r['FreshRst']:7.1f}% | {100*r['SyncRewind']:6.1f}% | "
            f"{100*r['TreeSearch']:10.1f}% | {100*r['TreeOracle']:9.1f}% | "
            f"{100*r['Lookahead']:8.1f}% | {100*r['Hybrid']:6.1f}%"
        )

    r0 = results_by_gamma[0.0]
    r5 = results_by_gamma[0.5]
    r10 = results_by_gamma[1.0]
    # Exact CRN boundary identities at gamma=1.0 (zero reversible recoveries possible):
    assert abs(r10["Hybrid"] - r10["Lookahead"]) < 1e-12, "Hybrid must not strand calls at gamma=1.0"
    assert abs(r10["Continue"] - r10["SyncRewind"]) < 1e-12
    assert r0["SyncRewind"] > r0["FreshRst"] and r0["TreeSearch"] > r0["Lookahead"]
    assert r5["Hybrid"] > r5["Lookahead"] > r5["SyncRewind"] > r5["TreeSearch"]
    assert r10["TreeSearch"] < r10["Continue"]  # noisy value fn false-rejections trigger extra live gamma=1.0 hazards!

    # Equal-drag sensitivity control (c_drag=0.0): Continue and SyncRewind tie identically!
    res_nodrag, _ = _simulate_gamma_grid(horizon=6, budget=16, p_step=0.72, c_drag=0.0, n_episodes=4000)
    assert abs(res_nodrag[0.0]["Continue"] - res_nodrag[0.0]["SyncRewind"]) < 1e-12

    print(f"Budget-ceiling hits verified active across all policies: {dict(exh_totals)}")
    print(
        f"[NEG-CTRL 3B.1 - gamma=0.0 & c_drag=0.0]: SyncRW==Continue ({100*res_nodrag[0.0]['SyncRewind']:.1f}%), "
        f"SyncRW beats FreshRst ({100*r0['FreshRst']:.1f}%) without >p_step bonus; TreeSearch ({100*r0['TreeSearch']:.1f}%) > Lookahead ({100*r0['Lookahead']:.1f}%)."
    )
    print(
        f"[NEG-CTRL 3B.2 - gamma=1.0 CRN Identity & Noisy-Value Hazard]: Hybrid==Lookahead ({100*r10['Hybrid']:.1f}%) "
        f">> Continue==SyncRW ({100*r10['Continue']:.1f}%) > TreeSearch(q=.88) ({100*r10['TreeSearch']:.1f}%) (PASS)."
    )


# =============================================================================
# PROBE 4: [exact reproduction of pinned source logic] + [targeted unit-test suite]
# OpenHands/software-agent-sdk@3a893a1b26de7ec02cc0dd2427906eea6aea3fc7
# stuck_detector.py (L1-539) & types.py (L226-251)
# =============================================================================
MAX_EVENTS_TO_SCAN_FOR_STUCK_DETECTION = 20


@dataclass
class ValidationErrorItem:
    type: str
    loc: tuple[Any, ...]


@dataclass
class ToolCallObj:
    arguments: str


@dataclass
class Event:
    id: str
    source: str


@dataclass
class MessageEvent(Event):
    llm_message: str


@dataclass
class CondensationSummaryEvent(Event):
    summary: str = "condensed"


@dataclass
class ActionEvent(Event):
    thought: str
    action: dict[str, Any] | None
    tool_name: str
    tool_call_id: str
    llm_response_id: str
    tool_call: ToolCallObj = field(default_factory=lambda: ToolCallObj("{}"))


@dataclass
class ObservationBaseEvent(Event):
    tool_call_id: str


@dataclass
class ObservationEvent(ObservationBaseEvent):
    observation: str
    tool_name: str


@dataclass
class AgentErrorEvent(ObservationBaseEvent):
    error: str
    validation_errors: list[ValidationErrorItem] = field(default_factory=list)


class PinnedOpenHandsStuckDetector:
    """Faithful reproduction of OpenHands/software-agent-sdk@3a893a1b26 stuck_detector.py."""

    def __init__(
        self,
        events: list[Event],
        action_observation: int = 4,
        action_error: int = 3,
        monologue: int = 3,
        alternating_pattern: int = 6,
        tools_with_summary_param: set[str] | None = None,
    ) -> None:
        self._all_events = events
        self.action_observation_threshold = action_observation
        self.action_error_threshold = action_error
        self.monologue_threshold = monologue
        self.alternating_pattern_threshold = alternating_pattern
        self._tools_with_summary_param = tools_with_summary_param or set()
        self._last_nudged_error_event_id: str | None = None
        self._resumed_after_event_id: str | None = None

    def _tool_has_summary_param(self, tool_name: str) -> bool:
        # Pinned L348-355: preserves explicit `summary` schema parameter when declared by tool
        return tool_name in self._tools_with_summary_param

    def _events_since_last_user_message(self, limit: int = MAX_EVENTS_TO_SCAN_FOR_STUCK_DETECTION) -> list[Event]:
        events = self._all_events[-limit:]
        last_user_idx = next(
            (i for i in reversed(range(len(events))) if isinstance(events[i], MessageEvent) and events[i].source == "user"),
            -1,
        )
        if last_user_idx != -1:
            events = events[last_user_idx + 1 :]
        if self._resumed_after_event_id is not None:
            resume_idx = next(
                (i for i in reversed(range(len(events))) if events[i].id == self._resumed_after_event_id),
                -1,
            )
            if resume_idx != -1:
                events = events[resume_idx + 1 :]
        return events

    def _collect_actions_and_observations(self, events: list[Event], max_needed: int) -> tuple[list[Event], list[Event]]:
        last_actions: list[Event] = []
        last_observations: list[Event] = []
        for event in reversed(events):
            if isinstance(event, ActionEvent) and len(last_actions) < max_needed:
                last_actions.append(event)
            elif isinstance(event, ObservationBaseEvent) and len(last_observations) < max_needed:
                last_observations.append(event)
            if len(last_actions) >= max_needed and len(last_observations) >= max_needed:
                break
        return last_actions, last_observations

    def _validated_arguments(self, event: ActionEvent) -> object:
        try:
            arguments = json.loads(event.tool_call.arguments)
        except (ValueError, TypeError):
            return event.tool_call.arguments
        if not isinstance(arguments, dict):
            return arguments
        arguments.pop("security_risk", None)
        # Pinned L344-345: conditional strip based on _tool_has_summary_param
        if not self._tool_has_summary_param(event.tool_name):
            arguments.pop("summary", None)
        return arguments

    def _event_eq(self, event1: Event, event2: Event) -> bool:
        if type(event1) is not type(event2):
            return False
        if isinstance(event1, ActionEvent) and isinstance(event2, ActionEvent):
            if event1.action is None and event2.action is None:
                return (
                    event1.source == event2.source
                    and event1.tool_name == event2.tool_name
                    and self._validated_arguments(event1) == self._validated_arguments(event2)
                )
            # Pinned L505-511: requires event1.thought == event2.thought!
            return (
                event1.source == event2.source
                and event1.thought == event2.thought
                and event1.action == event2.action
                and event1.tool_name == event2.tool_name
            )
        if isinstance(event1, ObservationEvent) and isinstance(event2, ObservationEvent):
            return (
                event1.source == event2.source
                and event1.observation == event2.observation
                and event1.tool_name == event2.tool_name
            )
        if isinstance(event1, AgentErrorEvent) and isinstance(event2, AgentErrorEvent):
            return event1.source == event2.source and event1.error == event2.error
        if isinstance(event1, MessageEvent) and isinstance(event2, MessageEvent):
            return event1.source == event2.source and event1.llm_message == event2.llm_message
        return event1 == event2

    def _invalid_calls_share_response(self, actions: list[Event]) -> bool:
        response_ids = [a.llm_response_id for a in actions if isinstance(a, ActionEvent) and a.action is None]
        return len(response_ids) != len(set(response_ids))

    def _same_error_action(
        self, reference: ActionEvent, action: ActionEvent, reference_error: AgentErrorEvent, error: AgentErrorEvent
    ) -> bool:
        if reference.tool_name != action.tool_name:
            return False
        if reference.action is None and action.action is None:
            left = reference_error.validation_errors
            right = error.validation_errors
            if left and right:
                if not any(e.type in ("value_error", "assertion_error") for e in [*left, *right]):
                    return Counter(
                        (e.type, tuple(0 if isinstance(p, int) else p for p in e.loc)) for e in left
                    ) == Counter(
                        (e.type, tuple(0 if isinstance(p, int) else p for p in e.loc)) for e in right
                    )
        return self._event_eq(reference, action)

    def _action_error_pairs(self, events: list[Event] | None = None) -> tuple[list[Event], list[Event]]:
        limit = MAX_EVENTS_TO_SCAN_FOR_STUCK_DETECTION
        while True:
            if events is None:
                events = self._events_since_last_user_message(limit)
            last_actions, last_observations = self._collect_actions_and_observations(events, len(events))
            widths = Counter(a.llm_response_id for a in last_actions if isinstance(a, ActionEvent))
            needed = MAX_EVENTS_TO_SCAN_FOR_STUCK_DETECTION + 2 * (max(widths.values(), default=1) - 1) * (
                self.action_error_threshold + 1
            )
            if needed <= limit:
                return last_actions, last_observations
            limit = needed
            events = None

    def _action_error_streak(self, last_actions: list[Event], last_observations: list[Event]) -> int:
        if not last_actions or not last_observations:
            return 0
        reference = last_actions[0]
        if not isinstance(reference, ActionEvent):
            return 0
        remaining = list(last_observations)
        reference_error: AgentErrorEvent | None = None
        streak = 0
        counted_response: str | None = None
        for action in last_actions:
            if not isinstance(action, ActionEvent):
                break
            idx = next(
                (i for i, obs in enumerate(remaining) if isinstance(obs, ObservationBaseEvent) and obs.tool_call_id == action.tool_call_id),
                None,
            )
            if idx is None:
                break
            obs = remaining.pop(idx)
            if not isinstance(obs, AgentErrorEvent):
                break
            if reference_error is None:
                reference_error = obs
            if not self._same_error_action(reference, action, reference_error, obs):
                break
            if action.llm_response_id != counted_response:
                counted_response = action.llm_response_id
                streak += 1
        return streak

    def get_action_error_nudge(self) -> bool:
        last_actions, last_observations = self._action_error_pairs()
        return self._action_error_streak(last_actions, last_observations) == self.action_error_threshold

    def _is_stuck_repeating_action_observation(self, last_actions: list[Event], last_observations: list[Event]) -> bool:
        threshold = self.action_observation_threshold
        if self._invalid_calls_share_response(last_actions[:threshold]):
            return False
        if len(last_actions) >= threshold and len(last_observations) >= threshold:
            actions_equal = all(self._event_eq(last_actions[0], a) for a in last_actions[:threshold])
            obs_equal = all(self._event_eq(last_observations[0], o) for o in last_observations[:threshold])
            if actions_equal and obs_equal:
                return True
        return False

    def _is_stuck_repeating_action_error(self, last_actions: list[Event], last_observations: list[Event]) -> bool:
        return self._action_error_streak(last_actions, last_observations) > self.action_error_threshold

    def _is_stuck_monologue(self, events: list[Event]) -> bool:
        threshold = self.monologue_threshold
        if len(events) < threshold:
            return False
        count = 0
        for event in reversed(events):
            if isinstance(event, MessageEvent):
                if event.source == "agent":
                    count += 1
                elif event.source == "user":
                    break
            elif isinstance(event, CondensationSummaryEvent):
                continue
            else:
                break
        return count >= threshold

    def _is_stuck_alternating_action_observation(self, events: list[Event]) -> bool:
        threshold = self.alternating_pattern_threshold
        last_actions: list[Event] = []
        last_observations: list[Event] = []
        for event in reversed(events):
            if isinstance(event, ActionEvent) and len(last_actions) < threshold:
                last_actions.append(event)
            elif isinstance(event, (ObservationEvent, AgentErrorEvent)) and len(last_observations) < threshold:
                last_observations.append(event)
            if len(last_actions) == threshold and len(last_observations) == threshold:
                break
        if self._invalid_calls_share_response(last_actions):
            return False
        if len(last_actions) == threshold and len(last_observations) == threshold:
            # Pinned L461-468: period-2 ONLY (i vs i+2)
            actions_equal = all(self._event_eq(last_actions[i], last_actions[i + 2]) for i in range(threshold - 2))
            obs_equal = all(self._event_eq(last_observations[i], last_observations[i + 2]) for i in range(threshold - 2))
            if actions_equal and obs_equal:
                return True
        return False

    def _is_stuck_context_window_error(self, _events: list[Event]) -> bool:
        # Pinned L481-485: docstring cites legacy AgentCondensationObservation; returns False (#282)
        return False

    def detect_scenario(self) -> tuple[bool, str]:
        events = self._events_since_last_user_message()
        min_threshold = min(self.action_observation_threshold, self.action_error_threshold, self.monologue_threshold)
        if len(events) < min_threshold:
            return False, "none"
        last_actions, last_observations = self._collect_actions_and_observations(events, self.action_observation_threshold)
        if self._is_stuck_repeating_action_observation(last_actions, last_observations):
            return True, "S1_action_obs"
        if self._is_stuck_repeating_action_error(*self._action_error_pairs(events)):
            return True, "S2_action_err"
        if self._is_stuck_monologue(events):
            return True, "S3_monologue"
        if len(events) >= self.alternating_pattern_threshold:
            if self._is_stuck_alternating_action_observation(events):
                return True, "S4_alternating_p2"
        if len(events) >= 10:
            if self._is_stuck_context_window_error(events):
                return True, "S5_ctx_window"
        return False, "none"


class CandidateHardenedDetector(PinnedOpenHandsStuckDetector):
    """Candidate design variant addressing the three structural blind spots in @3a893a1b:
    1. Thought-insensitive ActionEvent equality (with optional higher threshold or exemption
       for declared async-poll tools to mitigate false positives on legitimate wait loops).
    2. General period-k cycle detection (k in {2,3,4}, >=3 full cycles, scan window=32).
    3. Candidate S5 condensation-loop guard (>=3 trailing CondensationSummaryEvents; note
       upstream #282 remains open and pinned docstring references AgentCondensationObservation).
    """

    def __init__(self, events: list[Event], poll_tools: set[str] | None = None, **kwargs: Any) -> None:
        super().__init__(events, **kwargs)
        self._poll_tools = poll_tools or set()

    def _event_eq(self, event1: Event, event2: Event) -> bool:
        if isinstance(event1, ActionEvent) and isinstance(event2, ActionEvent) and event1.action is not None and event2.action is not None:
            return (
                event1.source == event2.source
                and event1.action == event2.action
                and event1.tool_name == event2.tool_name
            )
        return super()._event_eq(event1, event2)

    def _is_stuck_repeating_action_observation(self, last_actions: list[Event], last_observations: list[Event]) -> bool:
        if last_actions and isinstance(last_actions[0], ActionEvent) and last_actions[0].tool_name in self._poll_tools:
            return False
        return super()._is_stuck_repeating_action_observation(last_actions, last_observations)

    def _is_stuck_general_cycle(self, events: list[Event], max_period: int = 4, min_repeats: int = 3) -> int | None:
        max_needed = max_period * min_repeats
        last_actions: list[Event] = []
        last_obs: list[Event] = []
        for event in reversed(events):
            if isinstance(event, ActionEvent) and len(last_actions) < max_needed:
                last_actions.append(event)
            elif isinstance(event, (ObservationEvent, AgentErrorEvent)) and len(last_obs) < max_needed:
                last_obs.append(event)
            if len(last_actions) == max_needed and len(last_obs) == max_needed:
                break
        for k in range(2, max_period + 1):
            need = k * min_repeats
            if len(last_actions) >= need and len(last_obs) >= need:
                if self._invalid_calls_share_response(last_actions[:need]):
                    continue
                act_cyc = all(self._event_eq(last_actions[i], last_actions[i + k]) for i in range(need - k))
                obs_cyc = all(self._event_eq(last_obs[i], last_obs[i + k]) for i in range(need - k))
                if act_cyc and obs_cyc:
                    return k
        return None

    def _is_stuck_context_window_error(self, events: list[Event]) -> bool:
        streak = 0
        for ev in reversed(events):
            if isinstance(ev, CondensationSummaryEvent):
                streak += 1
            else:
                break
        return streak >= 3

    def detect_scenario(self) -> tuple[bool, str]:
        events = self._events_since_last_user_message(limit=32)
        min_threshold = min(self.action_observation_threshold, self.action_error_threshold, self.monologue_threshold)
        if len(events) < min_threshold:
            return False, "none"
        last_actions, last_observations = self._collect_actions_and_observations(events, self.action_observation_threshold)
        if self._is_stuck_repeating_action_observation(last_actions, last_observations):
            return True, "S1_action_obs"
        if self._is_stuck_repeating_action_error(*self._action_error_pairs(events)):
            return True, "S2_action_err"
        if self._is_stuck_monologue(events):
            return True, "S3_monologue"
        cyc_k = self._is_stuck_general_cycle(events)
        if cyc_k is not None:
            return True, f"S4_cycle_p{cyc_k}"
        if self._is_stuck_context_window_error(events):
            return True, "S5_ctx_window"
        return False, "none"


def _make_pair(step: int, thought: str, cmd: str, obs: str, is_error: bool = False, tool_name: str = "bash") -> list[Event]:
    tc = f"tc_{step}"
    act = ActionEvent(
        id=f"a_{step}",
        source="agent",
        thought=thought,
        action={"cmd": cmd},
        tool_name=tool_name,
        tool_call_id=tc,
        llm_response_id=f"resp_{step}",
    )
    if is_error:
        res: Event = AgentErrorEvent(id=f"e_{step}", source="agent", tool_call_id=tc, error=obs)
    else:
        res = ObservationEvent(id=f"o_{step}", source="env", tool_call_id=tc, observation=obs, tool_name=tool_name)
    return [act, res]


def run_probe_4() -> None:
    print("\n" + "=" * 88)
    print("PROBE 4 [exact pinned source logic + unit-test suite]: OpenHands@3a893a1b StuckDetector")
    print("=" * 88)

    cases: list[tuple[str, list[Event], bool, bool]] = []

    # C1. Verbatim S1 (4x identical action+obs+thought)
    ev1: list[Event] = []
    for s in range(4):
        ev1.extend(_make_pair(s, "run pytest", "pytest -q", "FAILED test_foo"))
    cases.append(("C1: Verbatim S1 repeat (4x)", ev1, True, True))

    # C2. S1 BYPASS via 1-token thought perturbation
    ev2: list[Event] = []
    for s in range(6):
        ev2.extend(_make_pair(s, f"run pytest attempt {s+1}", "pytest -q", "FAILED test_foo"))
    cases.append(("C2: S1 + 1-tok thought perturb (6x)", ev2, False, True))

    # C3a/C3b. Verbatim S2 valid action-error with varying error text (3x nudge; 4x hard stuck)
    ev3_3: list[Event] = []
    for s in range(3):
        ev3_3.extend(_make_pair(s, "edit file", "edit foo.py", f"FileNotFoundError [attempt={s+1}]", is_error=True))
    ev3_4 = ev3_3 + _make_pair(3, "edit file", "edit foo.py", "FileNotFoundError [attempt=4]", is_error=True)
    cases.append(("C3a: Verbatim S2 valid err (3x=nudge)", ev3_3, False, False))
    cases.append(("C3b: Verbatim S2 valid err (4x=stuck)", ev3_4, True, True))

    # C4. S2 BYPASS on valid ActionEvent + AgentErrorEvent via thought perturbation
    ev4: list[Event] = []
    for s in range(6):
        ev4.extend(_make_pair(s, f"edit file try {s+1}", "edit foo.py", f"FileNotFoundError [attempt={s+1}]", is_error=True))
    cases.append(("C4: S2 valid err + thought perturb (6x)", ev4, False, True))

    # C5. Invalid tool call (action=None) on tool WITHOUT summary param -> strips SDK summary & catches!
    ev5: list[Event] = []
    for s in range(4):
        tc = f"tc_inv_{s}"
        ev5.append(ActionEvent(
            id=f"ai_{s}", source="agent", thought=f"try {s}", action=None, tool_name="str_replace",
            tool_call_id=tc, llm_response_id=f"ri_{s}",
            tool_call=ToolCallObj(json.dumps({"path": "a.py", "security_risk": f"LOW_{s}", "summary": f"s{s}"})),
        ))
        ev5.append(AgentErrorEvent(
            id=f"ei_{s}", source="agent", tool_call_id=tc, error=f"missing field [call={s+1}]",
            validation_errors=[ValidationErrorItem("missing", ("new_str", s))],
        ))
    cases.append(("C5: S2 invalid call action=None (4x)", ev5, True, True))

    # C6. S3 Agent monologue with intervening CondensationSummaryEvent
    ev6: list[Event] = [
        MessageEvent(id="m1", source="agent", llm_message="Thinking 1"),
        CondensationSummaryEvent(id="c1", source="system"),
        MessageEvent(id="m2", source="agent", llm_message="Thinking 2"),
        MessageEvent(id="m3", source="agent", llm_message="Thinking 3"),
    ]
    cases.append(("C6: S3 monologue + condensation", ev6, True, True))

    # C7. S4 Verbatim period-2 alternating [A, B, A, B, A, B]
    ev7: list[Event] = []
    for s in range(6):
        cmd, obs = ("ls", "a.py") if s % 2 == 0 else ("cat a.py", "pass")
        ev7.extend(_make_pair(s, f"do {cmd}", cmd, obs))
    cases.append(("C7: S4 period-2 [A,B]x3 verbatim", ev7, True, True))

    # C8. S4 BYPASS via period-3 cycle [A, B, C] x 3 (identical per-command thoughts!)
    ev8: list[Event] = []
    tri = [("ls", "a.py"), ("cat a.py", "pass"), ("pytest", "1 failed")]
    for s in range(9):
        cmd, obs = tri[s % 3]
        ev8.extend(_make_pair(s, f"step {cmd}", cmd, obs))
    cases.append(("C8: S4 period-3 [A,B,C]x3 verbatim", ev8, False, True))

    # C9. S5 BYPASS: 12 consecutive CondensationSummaryEvents (pinned L485 returns False)
    ev9: list[Event] = [CondensationSummaryEvent(id=f"cw_{s}", source="system") for s in range(12)]
    cases.append(("C9: S5 condensation loop (12x, #282)", ev9, False, True))

    # Benign Negative Controls (NC1..NC4):
    # NC1: Distinct file edits
    nc1: list[Event] = []
    for s in range(10):
        nc1.extend(_make_pair(s, f"step {s}", f"edit file_{s}.py", f"ok_{s}"))
    cases.append(("NC1: Benign 10-file editing trace", nc1, False, False))

    # NC2: Repeated pytest command with shrinking failure count (observations progress!)
    nc2: list[Event] = []
    for s, out_txt in enumerate(["4 failed", "2 failed", "1 failed", "4 passed"]):
        nc2.extend(_make_pair(s, f"re-run pytest {s}", "pytest -q", out_txt))
    cases.append(("NC2: Benign pytest w/ changing output", nc2, False, False))

    # NC3: Invalid call on tool WITH declared `summary` schema param (L344-345 preserves summary!)
    nc3: list[Event] = []
    for s in range(4):
        tc = f"tc_sum_{s}"
        nc3.append(ActionEvent(
            id=f"as_{s}", source="agent", thought="summarize", action=None, tool_name="summarize_doc",
            tool_call_id=tc, llm_response_id=f"rs_{s}",
            tool_call=ToolCallObj(json.dumps({"summary": f"distinct_summary_payload_{s}"})),
        ))
        nc3.append(AgentErrorEvent(id=f"es_{s}", source="agent", tool_call_id=tc, error=f"value err {s}", validation_errors=[]))
    cases.append(("NC3: Tool w/ real summary param (L344)", nc3, False, False))

    # NC4: Benign async job wait-poll returning identical 'PENDING' 4x while thought changes
    nc4: list[Event] = []
    for s in range(4):
        nc4.extend(_make_pair(s, f"poll wait {s*10}s", "job_status --id=9", "STATUS=PENDING", tool_name="job_poll"))
    # Verify precision/recall trade-off: naive thought-stripping WITHOUT poll_tools exemption flags NC4!
    naive_nc4_stuck, _ = CandidateHardenedDetector(nc4, poll_tools=set()).detect_scenario()
    assert naive_nc4_stuck is True, "Naive thought-stripping must expose false-positive trade-off on identical-output polling"
    cases.append(("NC4: Benign async poll (poll_tools)", nc4, False, False))

    summary_tools = {"summarize_doc"}
    poll_tools = {"job_poll"}

    print(f"{'Case':40s} | {'Pinned@3a893a1b':>25s} | {'CandidateHardened':>25s} | {'Status'}")
    pinned_catches = 0
    hardened_catches = 0
    stuck_suite_n = 0
    nc_fp = 0
    nc_total = 0
    for label, evs, exp_pinned, exp_hard in cases:
        p_det = PinnedOpenHandsStuckDetector(evs, tools_with_summary_param=summary_tools)
        h_det = CandidateHardenedDetector(evs, tools_with_summary_param=summary_tools, poll_tools=poll_tools)
        p_stuck, p_tag = p_det.detect_scenario()
        h_stuck, h_tag = h_det.detect_scenario()
        assert p_stuck == exp_pinned, f"Pinned mismatch on {label}: got {p_stuck}"
        assert h_stuck == exp_hard, f"Hardened mismatch on {label}: got {h_stuck}"
        if label.startswith("C3a"):
            assert p_det.get_action_error_nudge() is True
            p_tag = "nudge_only"
            h_tag = "nudge_only"
        elif label.startswith("NC"):
            nc_total += 1
            nc_fp += int(h_stuck)
        else:
            stuck_suite_n += 1
            pinned_catches += int(p_stuck)
            hardened_catches += int(h_stuck)
        status = "BYPASSED" if (exp_hard and not exp_pinned) else ("OK_NC" if label.startswith("NC") else "CAUGHT")
        print(f"{label:40s} | {str(p_stuck):5s} ({p_tag:17s}) | {str(h_stuck):5s} ({h_tag:17s}) | {status}")

    assert nc_fp == 0 and nc_total == 4
    print(
        f"\nTargeted Regression-Suite Coverage ({stuck_suite_n} constructed bug/loop cases, NOT empirical trace recall): "
        f"Pinned@3a893a1b={pinned_catches}/{stuck_suite_n} ({100*pinned_catches/stuck_suite_n:.1f}%), "
        f"CandidateHardened={hardened_catches}/{stuck_suite_n} ({100*hardened_catches/stuck_suite_n:.1f}%). "
        f"Benign NCs={nc_fp}/{nc_total} FPs (naive un-exempted poll on NC4={naive_nc4_stuck}; PASS)."
    )


def main() -> None:
    print(f"Planning, Decomposition & Long-Horizon Execution Verification Probes (seed={SEED})")
    run_probe_1()
    run_probe_2()
    run_probe_3()
    run_probe_4()
    print("\nALL 4 PROBES & NEGATIVE CONTROLS PASSED (exit 0).")


if __name__ == "__main__":
    main()
