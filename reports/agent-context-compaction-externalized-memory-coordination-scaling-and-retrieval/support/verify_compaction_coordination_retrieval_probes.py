#!/usr/bin/env python3
"""Deterministic verification probes for agent compaction, coordination, and retrieval.

Self-contained support script for the reference report package:
  reports/agent-context-compaction-externalized-memory-coordination-scaling-and-retrieval/

Runtime constraints: Python 3.10+ standard library only, fixed seed 20261121,
zero network calls, bit-identical deterministic stdout, < 3s runtime.

Epistemic labeling discipline (printed verbatim in stdout banners):
  - Probe 1A & 1B ([exact analytical / derived fit]):
      1A: Exact Beta-Binomial moment check E[p^k] calibrated to tau-bench
          (arXiv:2406.12045v1, Table 2 & Fig. 4: gpt-4o tau-retail pass^1=0.612,
          pass^8 < 0.25; target_pass8=0.226 chosen as an interior point within
          the published < 0.25 bound, with sensitivity across [0.20, 0.245]).
      1B: Exact single-step reliability q required for pass^8 >= 0.80 across
          m-write stateful workflows, explicitly contrasting (i) homogeneous
          step compounding, (ii) task-level Beta heterogeneity at fixed M
          (explaining why P(p_i^8 < 0.5) stays invariant across m), and
          (iii) per-step Beta heterogeneity (p_i = q_i^m, where both mu_step
          and brittle-tail share shift with m).
  - Probe 1C ([toy model / multiplicative-exposure stress model]):
      Explicitly tabulates Kim et al. (arXiv:2512.08296v3, Tables 4 & 5)
      separating execution-trace extra-work amplification A_e^trace
      (1.0x-17.2x; n.s. main effect on task success, beta=0.014, p=0.658) from
      empirical task-level error ratio A_e^task (0.98x-1.18x). Parameterizes
      pre-commit verifier gating strictly over abstract unverified exposure
      multipliers K in {1, 2, 4, 8, 16} (NOT calibrated to Kim et al. task
      failure rates), verifying exact geometric-series retry math and a
      dual-control uncheckable-error negative control.
  - Probe 2 ([exact analytical / mechanistic surrogate]):
      Exact segment-level longest-common-prefix KV-cache & USD billing model
      calibrated to 84% observation share (JetBrains arXiv:2508.21433v3).
      Enforces JetBrains section 5.3's unmasked-context summarization billing
      rule (full obs_tokens=1680 for summarized turns), compares OpenHands
      condensation at BOTH 0% (equal-horizon) and +15% (section 4.4)
      elongation, sweeps horizons T in {60, 120, 200} across cache discounts
      1x, 4x (Vertex AI implicit), and 10x (Anthropic/OpenAI cached read),
      computes exact crossover horizons reconciling JetBrains Table 1's
      polling=1 win, and checks Anthropic 1.25x cache-write surcharge sensitivity.
  - Probe 3 ([toy model / mechanistic surrogate]):
      3A & 3B: Structural polarity & exclusion retrieval mechanics (modeled
          after NevIR arXiv:2305.07614v2 and ExcluIR arXiv:2404.17288v1) paired
          with BOTH a disjoint affirmative control and an adversarial
          near-minimal-pair affirmative stress test exposing false-positive
          misfires from leaky lexical cue lists ('longer', 'fails', 'drops')
          and the precision/recall trade-off of scoped lexical gating.
      3C: Deterministic 2-hop call-graph reachability vs. zero-overlap lexical
          lookup over a 48-symbol synthetic graph (explicitly labeled as
          structural graph reachability, NOT a proxy for empirical LocAgent
          accuracy, with zero duplicate/no-op branches).
"""

from __future__ import annotations

import hashlib
import math
import random
import re
from collections import Counter
from dataclasses import dataclass

SEED = 20261121


# =============================================================================
# PROBE 1: pass^k Beta-Binomial Compounding & Verifier-Gated Stress Model
# =============================================================================


def beta_binomial_pass_k_exact(alpha: float, beta: float, k: int) -> float:
    """Exact E[p^k] for p ~ Beta(alpha, beta): prod_{j=0}^{k-1} (a+j)/(a+b+j)."""
    val = 1.0
    for j in range(k):
        val *= (alpha + j) / (alpha + beta + j)
    return val


def beta_binomial_pass_k_lgamma(alpha: float, beta: float, k: int) -> float:
    """Independent cross-check via log-Gamma ratio."""
    return math.exp(
        math.lgamma(alpha + k)
        + math.lgamma(alpha + beta)
        - math.lgamma(alpha)
        - math.lgamma(alpha + beta + k)
    )


def calibrate_beta_concentration(mean: float, target_pass_k: float, k: int) -> float:
    """Solve for M = alpha + beta > 0 such that E[p^k] == target_pass_k."""
    lo, hi = 1e-4, 1e4
    for _ in range(100):
        mid = 0.5 * (lo + hi)
        val = beta_binomial_pass_k_exact(mean * mid, (1.0 - mean) * mid, k)
        # Higher M -> lower variance -> lower E[p^k] by Jensen's inequality.
        if val > target_pass_k:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def solve_mean_for_beta_pass_k(
    concentration: float, target_pass_k: float, k: int
) -> float:
    """Solve for mean mu in (0, 1) such that Beta(mu*M, (1-mu)*M) has E[p^k] == target."""
    lo, hi = 1e-6, 1.0 - 1e-12
    for _ in range(120):
        mid = 0.5 * (lo + hi)
        val = beta_binomial_pass_k_exact(
            mid * concentration, (1.0 - mid) * concentration, k
        )
        if val < target_pass_k:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


def effective_step_error_with_gate(
    base_step_error: float,
    catch_rate: float,
    max_retries: int,
    uncheckable_fraction: float,
) -> tuple[float, float]:
    """Per-step post-gate commit error under conditionally independent local retries.

    Returns (iterative_error, closed_form_error) so callers can assert exact
    agreement against the geometric-series identity.
    """
    e_chk = base_step_error * (1.0 - uncheckable_fraction)
    p_retry = e_chk * catch_rate
    p_no_err = max(0.0, 1.0 - base_step_error)

    p_success_iter = 0.0
    retry_pow = 1.0
    for _ in range(max_retries + 1):
        p_success_iter += retry_pow * p_no_err
        retry_pow *= p_retry

    if abs(1.0 - p_retry) > 1e-15:
        p_success_closed = (
            p_no_err * (1.0 - (p_retry ** (max_retries + 1))) / (1.0 - p_retry)
        )
    else:
        p_success_closed = p_no_err * (max_retries + 1)

    err_iter = min(1.0, max(0.0, 1.0 - p_success_iter))
    err_closed = min(1.0, max(0.0, 1.0 - p_success_closed))
    return err_iter, err_closed


def run_probe_1(rng: random.Random) -> dict[str, object]:
    print("=" * 86)
    print(
        "PROBE 1A/1B [exact analytical / derived fit]: pass^k Beta-Binomial Moment & SLA Check"
    )
    print("=" * 86)

    # 1A. Calibrate Beta-Binomial to tau-bench gpt-4o (tau-retail: pass^1=0.612, pass^8<0.25)
    mu_tau = 0.612
    target_pass8 = 0.226  # interior point chosen inside tau-bench Fig. 4's < 0.25 bound
    m_conc = calibrate_beta_concentration(mu_tau, target_pass8, k=8)
    alpha = mu_tau * m_conc
    beta = (1.0 - mu_tau) * m_conc

    n_mc = 20_000
    sampled_p = [rng.betavariate(alpha, beta) for _ in range(n_mc)]

    print(
        f"\n[1A] tau-bench gpt-4o calibration (arXiv:2406.12045v1 Table 2 & Fig. 4):"
    )
    print(
        f"     pass^1={mu_tau:.3f}, illustrative interior point pass^8={target_pass8:.3f} (< 0.25 bound)"
    )
    print(
        f"     => Beta(alpha={alpha:.4f}, beta={beta:.4f}, M={m_conc:.4f})"
    )
    print(
        f"{'k':>3} | {'Het Exact E[p^k]':>16} | {'Het MC (20k)':>12} | "
        f"{'Homog iid p^k':>13} | {'Ratio (Het/iid)':>15}"
    )
    print("-" * 70)
    het_pass8 = 0.0
    iid_pass8 = 0.0
    for k in (1, 2, 4, 8):
        exact = beta_binomial_pass_k_exact(alpha, beta, k)
        exact_lg = beta_binomial_pass_k_lgamma(alpha, beta, k)
        assert abs(exact - exact_lg) < 1e-12, f"Gamma mismatch: {exact} vs {exact_lg}"
        mc = sum(p**k for p in sampled_p) / n_mc
        iid = mu_tau**k
        ratio = exact / iid
        if k == 8:
            het_pass8, iid_pass8 = exact, iid
        print(f"{k:>3} | {exact:>16.4f} | {mc:>12.4f} | {iid:>13.4f} | {ratio:>14.2f}x")

    assert abs(beta_binomial_pass_k_exact(alpha, beta, 1) - mu_tau) < 1e-6
    assert 0.20 < het_pass8 < 0.25
    assert abs(iid_pass8 - 0.612**8) < 1e-9
    assert het_pass8 > 10.0 * iid_pass8

    # Sensitivity across tau-bench's < 0.25 bound (0.200 to 0.245)
    sens_parts = []
    for tp in (0.200, 0.226, 0.245):
        m_s = calibrate_beta_concentration(mu_tau, tp, k=8)
        sens_parts.append(f"pass^8={tp:.3f}->M={m_s:.3f} ({tp / iid_pass8:.2f}x iid)")
    print("  Bound sensitivity: " + " | ".join(sens_parts))

    frac_easy_pass8 = sum(1 for p in sampled_p if p**8 >= 0.80) / n_mc
    frac_hard_pass8 = sum(1 for p in sampled_p if p**8 < 0.05) / n_mc
    print(
        f"  Task-tail bimodality (MC, M={m_conc:.4f}): {frac_easy_pass8*100:.1f}% of tasks "
        f"have p_i^8>=0.80, while {frac_hard_pass8*100:.1f}% have p_i^8<0.05."
    )

    # 1B. Required single-step reliability q for pass^8 >= 0.80 across m-write workflows:
    # Explicitly compare fixed-M task-level Beta vs per-step Beta heterogeneity.
    target_prod = 0.80
    mu_het_task = solve_mean_for_beta_pass_k(m_conc, target_prod, k=8)
    beta_task_80 = (1.0 - mu_het_task) * m_conc
    task_tail_samples = [
        rng.betavariate(mu_het_task * m_conc, beta_task_80) for _ in range(n_mc)
    ]
    task_tail_bad = sum(1 for p in task_tail_samples if p**8 < 0.50) / n_mc

    print(
        f"\n[1B] Required single-step reliability q to sustain pass^8 >= {target_prod:.2f} "
        f"(m-write stateful workflows):"
    )
    print(
        f"     Task-level fixed-M assumption: p_i ~ Beta(mu*M, (1-mu)*M) with fixed M={m_conc:.4f}"
    )
    print(
        f"     (mu={mu_het_task:.5f}, beta={beta_task_80:.4f} << 1 => J-shaped density); because p_i's"
    )
    print(
        "     distribution is fixed and q_task_root = mu^(1/m), P(p_i^8<0.5) stays invariant across m."
    )
    print(
        "     Contrast: per-step Beta heterogeneity models q_i ~ Beta(mu_s*M, (1-mu_s)*M) with"
    )
    print(
        "     p_i = q_i^m, solving E[q_i^(8m)] = 0.80; here both mu_s and brittle tail shift with m."
    )
    print(
        f"{'m':>3} | {'Homog q':>9} | {'Max err':>8} | {'Task-Beta q':>11} | "
        f"{'Task tail<0.5':>13} | {'Step-Beta q':>11} | {'Step tail<0.5':>13}"
    )
    print("-" * 82)
    q_reqs: dict[int, float] = {}
    step_tails: list[float] = []
    step_mus: list[float] = []
    for m in (1, 3, 5, 10):
        q_hom = target_prod ** (1.0 / (8 * m))
        q_reqs[m] = q_hom
        q_task_root = mu_het_task ** (1.0 / m)
        mu_step_het = solve_mean_for_beta_pass_k(m_conc, target_prod, k=8 * m)
        step_mus.append(mu_step_het)
        step_samples = [
            rng.betavariate(mu_step_het * m_conc, (1.0 - mu_step_het) * m_conc)
            for _ in range(n_mc)
        ]
        step_tail_bad = sum(1 for q in step_samples if (q ** (8 * m)) < 0.50) / n_mc
        step_tails.append(step_tail_bad)
        print(
            f"{m:>3} | {q_hom:>9.5f} | {(1.0 - q_hom)*100:>7.3f}% | "
            f"{q_task_root:>11.5f} | {task_tail_bad*100:>12.2f}% | "
            f"{mu_step_het:>11.5f} | {step_tail_bad*100:>12.2f}%"
        )

    # Concentration-drift check: brittle tail shrinks only when concentration M itself rises
    conc_parts = []
    conc_tails: list[float] = []
    for m_val in (m_conc, 10.0, 50.0):
        mu_c = solve_mean_for_beta_pass_k(m_val, target_prod, k=8)
        s_c = [rng.betavariate(mu_c * m_val, (1.0 - mu_c) * m_val) for _ in range(n_mc)]
        t_bad = sum(1 for p in s_c if p**8 < 0.50) / n_mc
        conc_tails.append(t_bad)
        conc_parts.append(f"M={m_val:.2f}: mu={mu_c:.4f}, P(p^8<0.5)={t_bad*100:.2f}%")
    print("  Concentration drift (E[p^8]=0.80): " + " | ".join(conc_parts))

    assert q_reqs[1] > 0.972 and q_reqs[5] > 0.994 and q_reqs[10] > 0.997
    assert task_tail_bad > 0.15
    assert abs(step_tails[0] - task_tail_bad) < 0.015, "At m=1, task-Beta and step-Beta coincide"
    assert step_mus[-1] < mu_het_task ** (1.0 / 10), "Per-step Beta concentrates harder near 1 than task-Beta root"
    assert conc_tails[0] > conc_tails[1] > conc_tails[2], "Rising concentration M must strictly shrink brittle tail"

    # 1C. Strictly rescoped multiplicative-exposure stress model + empirical Kim et al. distinction
    print("\n" + "=" * 86)
    print(
        "PROBE 1C [toy model / multiplicative-exposure stress model]: Verifier-Gated Exposure"
    )
    print("=" * 86)
    print(
        "\n[1C-REF] Published Kim et al. (arXiv:2512.08296v3, Tables 4 & 5) — A_e^trace vs A_e^task:"
    )
    print(
        "  IMPORTANT: A_e^trace measures execution-trace extra-work amplification and has NO"
    )
    print(
        "  significant main effect on task success in Table 4 (beta=0.014, p=0.658; only"
    )
    print(
        "  A_e^trace x P_SA interaction is significant, beta=-0.080, p=0.022). Empirical"
    )
    print(
        "  task-level error ratio A_e^task = (1-P_MAS)/(1-P_SAS) spans only 0.98x-1.18x:"
    )
    kim_table5 = [
        ("SAS", 0.466, 1.0, 0),
        ("Decentralized", 0.477, 7.8, 263),
        ("Centralized", 0.463, 4.4, 285),
        ("Hybrid", 0.452, 5.1, 515),
        ("Independent", 0.370, 17.2, 58),
    ]
    sas_err = 1.0 - kim_table5[0][1]
    print(
        f"  {'Topology':<14} | {'Table 5 P':>9} | {'Task Err':>8} | {'A_e^task':>8} | "
        f"{'A_e^trace':>9} | {'Overhead':>8}"
    )
    print("  " + "-" * 70)
    for topo, succ, ae_trace, overhead in kim_table5:
        err = 1.0 - succ
        ae_task = err / sas_err
        print(
            f"  {topo:<14} | {succ:>9.3f} | {err:>8.3f} | {ae_task:>7.2f}x | "
            f"{ae_trace:>8.1f}x | {overhead:>7d}%"
        )
    assert 0.97 < ((1.0 - 0.477) / sas_err) < 0.99
    assert 1.17 < ((1.0 - 0.370) / sas_err) < 1.19

    # Abstract multiplicative-exposure stress model over K in {1, 2, 4, 8, 16}
    e0 = 0.04
    m_writes = 5
    exposures = (1, 2, 4, 8, 16)
    gate_regimes = [
        ("No gate (gamma=0.00)", 0.00, 0, 0.05),
        ("Det gate (0.90, R=2, rho=.05)", 0.90, 2, 0.05),
        ("Strong gate (0.95, R=2, rho=.02)", 0.95, 2, 0.02),
        ("DualCtrl neg-ctrl (0.95, rho=.35)", 0.95, 2, 0.35),
    ]

    print(
        f"\n[1C-TOY] Illustrative unverified multiplicative-exposure stress model "
        f"(m={m_writes} writes, base err e0={e0:.2f}):"
    )
    print(
        "  Parameterizes abstract unverified commit exposures K in {1,2,4,8,16} via"
    )
    print(
        "  pass^8 = ((1 - e_eff)^(m * K))^8 under conditionally independent local retries"
    )
    print(
        "  (upper bound; NOT calibrated to Kim et al. task success rates)."
    )
    print(
        f"{'Exposure K':<12} | {'No gate':>9} | {'Gate 0.90':>9} | "
        f"{'Gate 0.95':>9} | {'DualCtrl rho=.35':>16}"
    )
    print("-" * 66)
    results_1c: dict[int, list[float]] = {}
    max_geom_diff = 0.0
    for k_exp in exposures:
        row_p8: list[float] = []
        for _, gamma, retries, rho in gate_regimes:
            e_iter, e_closed = effective_step_error_with_gate(e0, gamma, retries, rho)
            max_geom_diff = max(max_geom_diff, abs(e_iter - e_closed))
            p_trial = (1.0 - e_iter) ** (m_writes * k_exp)
            row_p8.append(p_trial**8)
        results_1c[k_exp] = row_p8
        print(
            f"{f'K={k_exp}x':<12} | {row_p8[0]:>9.4f} | {row_p8[1]:>9.4f} | "
            f"{row_p8[2]:>9.4f} | {row_p8[3]:>16.4f}"
        )

    assert max_geom_diff < 1e-15, f"Geometric-series mismatch: {max_geom_diff}"
    assert results_1c[1][0] > results_1c[2][0] > results_1c[4][0] > results_1c[8][0] > results_1c[16][0]
    assert results_1c[16][0] < 1e-4
    assert results_1c[1][2] > 0.85
    assert results_1c[4][2] > 0.55 and results_1c[4][2] > 300.0 * results_1c[4][0]
    assert results_1c[16][2] < 0.25
    # Negative control: 35% uncheckable floor caps recovery even at K=1 and collapses at K=4
    assert results_1c[1][3] < 0.60
    assert results_1c[4][3] < 0.10
    print(
        f"  [PASS] Probe 1 assertions verified (exact geometric series diff={max_geom_diff:.1e}, "
        "heterogeneity >10x iid, task-vs-step Beta contrast, abstract K gate rescue & rho=0.35 ceiling)."
    )
    return {
        "m_conc": m_conc,
        "het_pass8": het_pass8,
        "iid_pass8": iid_pass8,
        "task_tail_bad": task_tail_bad,
        "step_tails": step_tails,
        "results_1c": results_1c,
    }


# =============================================================================
# PROBE 2: KV-Cache Prefix-Stability Cost/TTFT Frontier (JetBrains §5.3 Exact)
# =============================================================================


@dataclass(frozen=True)
class Segment:
    key: str
    tokens: int


@dataclass
class StrategyResult:
    name: str
    turns_executed: int
    total_input_tokens: int
    cached_input_tokens: int
    uncached_input_tokens: int
    output_tokens: int
    summary_input_tokens: int
    summary_output_tokens: int
    cache_hit_rate: float
    total_usd: float
    mean_ttft_ms: float
    p95_ttft_ms: float
    cumulative_usd_by_turn: tuple[float, ...]


def longest_common_prefix_tokens(prev: list[Segment], curr: list[Segment]) -> int:
    """Exact prefix-match KV-cache hit count over immutable token segments."""
    hit = 0
    for a, b in zip(prev, curr):
        if a == b:
            hit += a.tokens
        else:
            break
    return hit


def simulate_trajectory(
    strategy: str,
    base_turns: int,
    *,
    uncached_price_per_mtok: float = 3.00,
    cached_price_per_mtok: float = 0.30,
    cache_write_multiplier: float = 1.00,
    output_price_per_mtok: float = 15.00,
    sys_tokens: int = 4000,
    action_tokens: int = 320,
    obs_tokens: int = 1680,  # 1680 / (320 + 1680) = 84.0% observation share (JetBrains 2508.21433v3)
    masked_obs_tokens: int = 24,
    window: int = 10,
    openhands_max_turns: int = 40,  # OpenHands default_condenser max_size=80 events ~ 40 turns
    openhands_keep_first: int = 2,
    openhands_summary_tokens: int = 1200,
    openhands_elongation: float = 0.0,
    hybrid_summary_turn: int = 43,  # JetBrains deferred hybrid N=43, W=10
    uncached_tok_per_sec: float = 8000.0,
    cached_tok_per_sec: float = 80000.0,
) -> StrategyResult:
    """Exact segment-level prefix-cache & billing simulator.

    Respects JetBrains arXiv:2508.21433v3 section 5.3: hybrid LLM summarization
    passes FULL unmasked observations (obs_tokens=1680) to the summarizer.
    """
    assert abs(obs_tokens / (action_tokens + obs_tokens) - 0.84) < 1e-9

    if strategy == "openhands_condense" and base_turns > openhands_max_turns:
        total_turns = int(round(base_turns * (1.0 + openhands_elongation)))
    else:
        total_turns = base_turns

    prev_prompt: list[Segment] = []
    masked_cutoff = 0
    active_turns: list[tuple[int, bool]] = []
    summaries: list[Segment] = []
    condensation_count = 0

    tot_in = 0
    tot_cached = 0
    tot_uncached = 0
    tot_out = 0
    sum_in = 0
    sum_out = 0
    ttft_samples_ms: list[float] = []
    cum_usd: list[float] = []

    for t in range(1, total_turns + 1):
        if strategy == "raw_append":
            prompt = [Segment("sys", sys_tokens)]
            for tid, _ in active_turns:
                prompt.append(Segment(f"act_{tid}", action_tokens))
                prompt.append(Segment(f"obs_{tid}_full", obs_tokens))

        elif strategy in ("mask_poll1", "mask_poll5", "mask_poll10"):
            poll = {"mask_poll1": 1, "mask_poll5": 5, "mask_poll10": 10}[strategy]
            n_hist = len(active_turns)
            if n_hist > window:
                excess = n_hist - window
                if poll == 1:
                    masked_cutoff = excess
                elif excess - masked_cutoff >= poll:
                    masked_cutoff = excess
            prompt = [Segment("sys", sys_tokens)]
            for idx, (tid, _) in enumerate(active_turns):
                prompt.append(Segment(f"act_{tid}", action_tokens))
                if idx < masked_cutoff:
                    prompt.append(Segment(f"obs_{tid}_masked", masked_obs_tokens))
                else:
                    prompt.append(Segment(f"obs_{tid}_full", obs_tokens))

        elif strategy == "openhands_condense":
            if len(active_turns) > openhands_max_turns:
                condensation_count += 1
                keep_tail = openhands_max_turns // 2 - openhands_keep_first
                drop_start = openhands_keep_first
                drop_end = len(active_turns) - keep_tail
                dropped = active_turns[drop_start:drop_end]
                dropped_tok = len(dropped) * (action_tokens + obs_tokens)
                if summaries:
                    dropped_tok += sum(s.tokens for s in summaries)
                sum_in += 500 + dropped_tok
                sum_out += openhands_summary_tokens
                summaries = [
                    Segment(f"oh_sum_{condensation_count}", openhands_summary_tokens)
                ]
                active_turns = active_turns[:drop_start] + active_turns[drop_end:]

            prompt = [Segment("sys", sys_tokens)]
            for idx, (tid, _) in enumerate(active_turns):
                if idx == openhands_keep_first and summaries:
                    prompt.extend(summaries)
                prompt.append(Segment(f"act_{tid}", action_tokens))
                prompt.append(Segment(f"obs_{tid}_full", obs_tokens))

        elif strategy == "jetbrains_hybrid":
            # Deferred Hybrid (N=43, W=10) with polling=10 observation masking.
            # Per JetBrains arXiv:2508.21433v3 section 5.3 (p. 9):
            # "Note that we pass the unmasked context whenever summarizing with LLM-Summary."
            n_hist = len(active_turns)
            if n_hist >= hybrid_summary_turn:
                condensation_count += 1
                drop_count = n_hist - window
                dropped = active_turns[:drop_count]
                # Full UNMASKED obs_tokens billed to the summarization LLM call:
                dropped_tok = len(dropped) * (action_tokens + obs_tokens)
                if summaries:
                    dropped_tok += sum(s.tokens for s in summaries)
                sum_in += 500 + dropped_tok
                sum_out += 900
                summaries = [Segment(f"jb_sum_{condensation_count}", 900)]
                active_turns = active_turns[drop_count:]
                masked_cutoff = 0
            else:
                if n_hist > window and (n_hist - window) - masked_cutoff >= 10:
                    masked_cutoff = n_hist - window
                active_turns = [
                    (tid, idx < masked_cutoff)
                    for idx, (tid, _) in enumerate(active_turns)
                ]

            prompt = [Segment("sys", sys_tokens)]
            if summaries:
                prompt.extend(summaries)
            for tid, is_masked in active_turns:
                prompt.append(Segment(f"act_{tid}", action_tokens))
                if is_masked:
                    prompt.append(Segment(f"obs_{tid}_masked", masked_obs_tokens))
                else:
                    prompt.append(Segment(f"obs_{tid}_full", obs_tokens))
        else:
            raise ValueError(f"Unknown strategy: {strategy}")

        prompt_tok = sum(s.tokens for s in prompt)
        cached_tok = longest_common_prefix_tokens(prev_prompt, prompt)
        uncached_tok = prompt_tok - cached_tok

        tot_in += prompt_tok
        tot_cached += cached_tok
        tot_uncached += uncached_tok
        tot_out += action_tokens

        ttft_ms = 1000.0 * (
            uncached_tok / uncached_tok_per_sec + cached_tok / cached_tok_per_sec
        )
        ttft_samples_ms.append(ttft_ms)

        prev_prompt = prompt
        active_turns.append((t, False))

        # Record exact cumulative USD after turn t (for O(T) crossover sweeps)
        step_agent_in_usd = (
            tot_cached * cached_price_per_mtok
            + tot_uncached * (uncached_price_per_mtok * cache_write_multiplier)
        ) / 1e6
        step_agent_out_usd = (tot_out * output_price_per_mtok) / 1e6
        step_summary_usd = (
            sum_in * uncached_price_per_mtok + sum_out * output_price_per_mtok
        ) / 1e6
        cum_usd.append(step_agent_in_usd + step_agent_out_usd + step_summary_usd)

    # Billing: newly populated uncached prefix tokens incur cache_write_multiplier
    # (1.00x standard; 1.25x Anthropic ephemeral cache write). Summary calls run
    # uncached (store=False / JetBrains section 5.2).
    total_usd = cum_usd[-1] if cum_usd else 0.0

    sorted_ttft = sorted(ttft_samples_ms)
    p95_idx = min(len(sorted_ttft) - 1, int(math.ceil(0.95 * len(sorted_ttft))) - 1)
    return StrategyResult(
        name=strategy,
        turns_executed=total_turns,
        total_input_tokens=tot_in,
        cached_input_tokens=tot_cached,
        uncached_input_tokens=tot_uncached,
        output_tokens=tot_out,
        summary_input_tokens=sum_in,
        summary_output_tokens=sum_out,
        cache_hit_rate=(tot_cached / tot_in) if tot_in else 0.0,
        total_usd=total_usd,
        mean_ttft_ms=sum(ttft_samples_ms) / len(ttft_samples_ms),
        p95_ttft_ms=sorted_ttft[p95_idx],
        cumulative_usd_by_turn=tuple(cum_usd),
    )


def run_probe_2() -> dict[str, object]:
    print("\n" + "=" * 86)
    print(
        "PROBE 2 [exact analytical / mechanistic surrogate]: KV-Cache Prefix-Stability Frontier"
    )
    print("=" * 86)

    # Strategy catalog including BOTH 0% (equal-horizon) and +15% (JetBrains §4.4) OpenHands
    strat_specs = [
        ("raw_append", "raw_append", 0.0),
        ("mask_poll1", "mask_poll1", 0.0),
        ("mask_poll5", "mask_poll5", 0.0),
        ("mask_poll10", "mask_poll10", 0.0),
        ("openhands_0pct", "openhands_condense", 0.0),
        ("openhands_15pct", "openhands_condense", 0.15),
        ("jetbrains_hybrid", "jetbrains_hybrid", 0.0),
    ]
    horizons = (60, 120, 200)
    discounts = [
        ("1x", 3.00),  # no cache discount
        ("4x", 0.75),  # 75% discount (e.g., Vertex AI implicit caching)
        ("10x", 0.30),  # 90% discount (Anthropic/OpenAI cached read)
    ]

    res: dict[tuple[str, int, str], StrategyResult] = {}
    for d_label, cached_p in discounts:
        for t in horizons:
            for label, strat, elong in strat_specs:
                res[(d_label, t, label)] = simulate_trajectory(
                    strat,
                    t,
                    uncached_price_per_mtok=3.00,
                    cached_price_per_mtok=cached_p,
                    openhands_elongation=elong,
                )

    print(
        "\n[2A] 10x Cache-Discount Regime ($3.00 uncached / $0.30 cached / $15.00 out; 84% obs;"
    )
    print(
        "     jetbrains_hybrid bills FULL unmasked 1,680-tok obs per JetBrains sec 5.3):"
    )
    print(
        f"{'T':>3} | {'Strategy':<17} | {'ExecT':>5} | {'HitRate':>7} | "
        f"{'UncachK':>8} | {'SumInK':>7} | {'MeanTTFT':>8} | {'TotalUSD':>8}"
    )
    print("-" * 86)
    for t in horizons:
        for label, _, _ in strat_specs:
            r = res[("10x", t, label)]
            print(
                f"{t:>3} | {label:<17} | {r.turns_executed:>5} | {r.cache_hit_rate*100:>6.1f}% | "
                f"{r.uncached_input_tokens/1e3:>7.1f}k | {r.summary_input_tokens/1e3:>6.1f}k | "
                f"{r.mean_ttft_ms:>6.0f}ms | ${r.total_usd:>7.4f}"
            )
        if t != horizons[-1]:
            print("-" * 86)

    print(
        "\n[2B] Multi-Discount & Multi-Horizon Sweep (1x vs 4x vs 10x cached-read discount):"
    )
    print(
        f"{'T':>3} | {'Strategy':<17} | {'USD (1x)':>9} | {'USD (4x)':>9} | "
        f"{'USD (10x)':>9} | {'Rank 1x->4x->10x':>16}"
    )
    print("-" * 80)
    labels = [s[0] for s in strat_specs]
    for t in horizons:
        ranks: dict[str, dict[str, int]] = {}
        for d_label, _ in discounts:
            ordered = sorted(labels, key=lambda x: res[(d_label, t, x)].total_usd)
            ranks[d_label] = {name: i + 1 for i, name in enumerate(ordered)}
        for label in labels:
            print(
                f"{t:>3} | {label:<17} | ${res[('1x', t, label)].total_usd:>8.4f} | "
                f"${res[('4x', t, label)].total_usd:>8.4f} | "
                f"${res[('10x', t, label)].total_usd:>8.4f} | "
                f"#{ranks['1x'][label]} -> #{ranks['4x'][label]} -> #{ranks['10x'][label]:<2}"
            )
        if t != horizons[-1]:
            print("-" * 80)

    # 2C. Exact crossover horizons reconciling JetBrains Table 1 (polling=1) & deferred hybrid
    # Computed in O(T) from single 250-turn runs (since trajectories are prefix-identical across horizons).
    p1_4x_curve = simulate_trajectory("mask_poll1", 250, cached_price_per_mtok=0.75).cumulative_usd_by_turn
    raw_4x_curve = simulate_trajectory("raw_append", 250, cached_price_per_mtok=0.75).cumulative_usd_by_turn
    p1_10x_curve = simulate_trajectory("mask_poll1", 250, cached_price_per_mtok=0.30).cumulative_usd_by_turn
    raw_10x_curve = simulate_trajectory("raw_append", 250, cached_price_per_mtok=0.30).cumulative_usd_by_turn
    hyb_10x_curve = simulate_trajectory("jetbrains_hybrid", 250, cached_price_per_mtok=0.30).cumulative_usd_by_turn
    p10_10x_curve = simulate_trajectory("mask_poll10", 250, cached_price_per_mtok=0.30).cumulative_usd_by_turn

    cross_poll1_raw_4x = next(
        (t for t in range(15, 251) if p1_4x_curve[t - 1] < raw_4x_curve[t - 1]), None
    )
    cross_poll1_raw_10x = next(
        (t for t in range(15, 251) if p1_10x_curve[t - 1] < raw_10x_curve[t - 1]), None
    )
    cross_hybrid_poll10_first = next(
        (t for t in range(50, 251) if hyb_10x_curve[t - 1] < p10_10x_curve[t - 1]), None
    )
    above_after = [
        t
        for t in range(cross_hybrid_poll10_first or 50, 251)
        if hyb_10x_curve[t - 1] >= p10_10x_curve[t - 1]
    ]
    cross_hybrid_poll10_perm = (
        (max(above_after) + 1) if above_after else cross_hybrid_poll10_first
    )

    print("\n[2C] Exact Crossover Horizons (swept T=15..250):")
    print(
        f"  - mask_poll1 beats raw_append under 4x caching at T* = {cross_poll1_raw_4x} "
        "(stays cheaper through T=250; reconciles JetBrains Table 1 polling=1 savings under ~75% implicit cache discount)."
    )
    print(
        f"  - mask_poll1 beats raw_append under 10x caching only at T* = {cross_poll1_raw_10x} "
        "(within JetBrains's 250-turn cap, explaining why short/mid runs penalize poll=1)."
    )
    print(
        f"  - Corrected jetbrains_hybrid (unmasked summary) first crosses below mask_poll10 under 10x "
        f"at T={cross_hybrid_poll10_first} and stays permanently cheaper from T* = {cross_hybrid_poll10_perm} onward "
        f"(at T=120, mask_poll10 wins: ${res[('10x', 120, 'mask_poll10')].total_usd:.4f} vs "
        f"${res[('10x', 120, 'jetbrains_hybrid')].total_usd:.4f})."
    )

    # 2D. Anthropic 1.25x cache-write surcharge sensitivity at T=60 and T=120 under 10x read
    p1_cw60 = simulate_trajectory("mask_poll1", 60, cached_price_per_mtok=0.30, cache_write_multiplier=1.25).total_usd
    p10_cw60 = simulate_trajectory("mask_poll10", 60, cached_price_per_mtok=0.30, cache_write_multiplier=1.25).total_usd
    p1_cw120 = simulate_trajectory("mask_poll1", 120, cached_price_per_mtok=0.30, cache_write_multiplier=1.25).total_usd
    p10_cw120 = simulate_trajectory("mask_poll10", 120, cached_price_per_mtok=0.30, cache_write_multiplier=1.25).total_usd
    hyb_cw120 = simulate_trajectory("jetbrains_hybrid", 120, cached_price_per_mtok=0.30, cache_write_multiplier=1.25).total_usd
    print("\n[2D] Anthropic 1.25x Cache-Write Surcharge Sensitivity ($3.75 write / $0.30 read):")
    print(
        f"  T=60 : mask_poll1=${p1_cw60:.4f} (was ${res[('10x', 60, 'mask_poll1')].total_usd:.4f}) "
        f"vs mask_poll10=${p10_cw60:.4f}"
    )
    print(
        f"  T=120: mask_poll1=${p1_cw120:.4f} (was ${res[('10x', 120, 'mask_poll1')].total_usd:.4f}) "
        f"vs mask_poll10=${p10_cw120:.4f} vs jetbrains_hybrid=${hyb_cw120:.4f}"
    )

    # Assertions verifying structural invariants, unmasked-summary billing, and crossover horizons:
    # 1. Under 1x (no cache discount), mask_poll1 strictly beats mask_poll5 and mask_poll10.
    for t in horizons:
        assert res[("1x", t, "mask_poll1")].total_usd < res[("1x", t, "mask_poll5")].total_usd
        assert res[("1x", t, "mask_poll5")].total_usd < res[("1x", t, "mask_poll10")].total_usd
    # 2. Under 10x, optimal strategy flips: mask_poll10 beats mask_poll1 at every horizon,
    #    and mask_poll1 loses even to raw_append at T=60 and T=120.
    for t in horizons:
        assert res[("10x", t, "mask_poll10")].total_usd < res[("10x", t, "mask_poll1")].total_usd
    assert res[("10x", 60, "raw_append")].total_usd < res[("10x", 60, "mask_poll1")].total_usd
    assert res[("10x", 120, "raw_append")].total_usd < res[("10x", 120, "mask_poll1")].total_usd
    # 3. Corrected JetBrains §5.3 billing: at T=60 and T=120 under 10x, mask_poll10 BEATS jetbrains_hybrid!
    assert res[("10x", 60, "mask_poll10")].total_usd < res[("10x", 60, "jetbrains_hybrid")].total_usd
    assert res[("10x", 120, "mask_poll10")].total_usd < res[("10x", 120, "jetbrains_hybrid")].total_usd
    assert abs(res[("10x", 120, "jetbrains_hybrid")].summary_input_tokens - 201_300) <= 200
    # 4. At longer horizon T=200 under 10x, deferred hybrid crosses below mask_poll10.
    assert cross_hybrid_poll10_first is not None and 150 <= cross_hybrid_poll10_first <= 180
    assert cross_hybrid_poll10_perm is not None and 175 <= cross_hybrid_poll10_perm <= 200
    assert all(hyb_10x_curve[t - 1] < p10_10x_curve[t - 1] for t in range(cross_hybrid_poll10_perm, 251))
    assert res[("10x", 200, "jetbrains_hybrid")].total_usd < res[("10x", 200, "mask_poll10")].total_usd
    # 5. Crossover reconciliation: 4x crossover < 100 turns; 10x crossover > 180 turns (both permanent through T=250).
    assert cross_poll1_raw_4x is not None and 60 < cross_poll1_raw_4x < 100
    assert all(p1_4x_curve[t - 1] < raw_4x_curve[t - 1] for t in range(cross_poll1_raw_4x, 251))
    assert cross_poll1_raw_10x is not None and 180 < cross_poll1_raw_10x < 230
    assert all(p1_10x_curve[t - 1] < raw_10x_curve[t - 1] for t in range(cross_poll1_raw_10x, 251))
    # 6. Equal-horizon OpenHands (0%) is strictly cheaper than +15% elongated OpenHands.
    for t in horizons:
        assert res[("10x", t, "openhands_0pct")].total_usd < res[("10x", t, "openhands_15pct")].total_usd
    # 7. TTFT penalty for rolling poll=1 vs batched poll=10
    assert res[("10x", 60, "mask_poll1")].mean_ttft_ms > 2.5 * res[("10x", 60, "mask_poll10")].mean_ttft_ms
    assert res[("10x", 120, "mask_poll1")].mean_ttft_ms > 2.5 * res[("10x", 120, "mask_poll10")].mean_ttft_ms
    # 8. 1.25x cache-write widens poll=1 penalty further
    assert p1_cw120 > res[("10x", 120, "mask_poll1")].total_usd + 1.50
    assert p10_cw120 < hyb_cw120 < p1_cw120

    print(
        "  [PASS] Probe 2 assertions verified (1x->4x->10x rank flip, sec 5.3 unmasked hybrid loses to "
        f"mask_poll10 at T=120 and stays cheaper from T*={cross_hybrid_poll10_perm}, 4x/10x poll=1 crossovers, "
        "0% vs +15% elongation, 1.25x cache-write penalty)."
    )
    return {
        "res": res,
        "cross_poll1_raw_4x": cross_poll1_raw_4x,
        "cross_poll1_raw_10x": cross_poll1_raw_10x,
        "cross_hybrid_poll10_10x": cross_hybrid_poll10_perm,
    }


# =============================================================================
# PROBE 3: Negation/Exclusion Polarity Trade-Off & 2-Hop Dependency Reachability
# =============================================================================

TOKEN_RE = re.compile(r"[a-zA-Z0-9_]+")

# Explicit grammatical negation and prohibition words
EXPLICIT_NEGATION_WORDS = frozenset(
    {
        "not",
        "no",
        "never",
        "forbid",
        "forbids",
        "forbidden",
        "prohibit",
        "prohibits",
        "prohibited",
        "disallow",
        "disallows",
        "disallowed",
        "exclude",
        "excludes",
        "excluded",
        "cannot",
        "must_not",
    }
)

EXCLUSION_PREPOSITIONS = frozenset({"without", "except", "excluding", "unless"})

# Overfit/leaky lexical cues (deliberately contrasted to expose affirmative false positives)
LEAKY_DOMAIN_CUES = frozenset(
    {
        "fails",
        "drops",
        "omits",
        "blocked",
        "rejects",
        "rejected",
        "unsafe",
        "invalid",
        "invalidated",
        "uneditable",
        "longer",
    }
)

FUNCTION_STOPWORDS = frozenset(
    {
        "the",
        "a",
        "an",
        "is",
        "are",
        "be",
        "to",
        "of",
        "in",
        "on",
        "for",
        "by",
        "with",
        "when",
        "if",
        "that",
        "this",
        "it",
        "as",
        "from",
        "and",
        "or",
        "only",
        "must",
        "may",
        "can",
        "should",
        "which",
        "rule",
        "rules",
        "policy",
        "docs",
    }
)


def tokenize(text: str) -> list[str]:
    return [t.lower() for t in TOKEN_RE.findall(text)]


@dataclass(frozen=True)
class NegPair:
    pair_id: str
    pos_doc: str
    neg_doc: str
    pos_query: str
    neg_query: str
    neg_kind: str  # "explicit" or "implicit_lexical"


@dataclass(frozen=True)
class ExclPair:
    pair_id: str
    allowed_doc: str
    excluded_doc: str
    excl_query: str


@dataclass(frozen=True)
class AffirmPair:
    pair_id: str
    doc_a: str
    doc_b: str
    query_a: str
    query_b: str


@dataclass(frozen=True)
class CodeSymbol:
    sym_id: str
    text: str
    callees: tuple[str, ...]


@dataclass(frozen=True)
class CodeTask:
    task_id: str
    query: str
    target_sym: str


def build_negation_pairs() -> list[NegPair]:
    """12 NevIR-style minimal pairs: 9 explicit grammatical negations + 3 lexical/morphological."""
    return [
        NegPair(
            "P01",
            "transmute pointer cast is valid when padding bytes are initialized",
            "transmute pointer cast is not valid when padding bytes are initialized",
            "when transmute pointer cast is valid with padding bytes initialized",
            "when transmute pointer cast is not valid with padding bytes initialized",
            "explicit",
        ),
        NegPair(
            "P02",
            "kv prefix cache persists across turns when tool schemas mutate",
            "kv prefix cache never persists across turns when tool schemas mutate",
            "kv prefix cache persists across turns when tool schemas mutate",
            "kv prefix cache does not persist when tool schemas mutate",
            "explicit",
        ),
        NegPair(
            "P03",
            "memfs precommit hook permits editing read_only frontmatter field",
            "memfs precommit hook forbids editing read_only frontmatter field",
            "memfs precommit hook allows editing read_only frontmatter field",
            "memfs precommit hook prohibits editing read_only frontmatter field",
            "explicit",
        ),
        NegPair(
            "P04",
            "config update to memfs constraints succeeds during automated agent commit",
            "config update to memfs constraints cannot succeed during automated agent commit",
            "config update to memfs constraints succeeds during automated agent commit",
            "config update to memfs constraints is disallowed during automated agent commit",
            "explicit",
        ),
        NegPair(
            "P05",
            "openhands condenser preserves keep_first user events during hard reset",
            "openhands condenser does not preserve keep_first user events during hard reset",
            "openhands condenser preserves keep_first user events during hard reset",
            "openhands condenser does not preserve keep_first user events during hard reset",
            "explicit",
        ),
        NegPair(
            "P06",
            "locomo benchmark evaluator includes category five adversarial questions in denominator",
            "locomo benchmark evaluator does not include category five adversarial questions in denominator",
            "locomo benchmark evaluator includes category five adversarial questions in denominator",
            "locomo benchmark evaluator excludes category five adversarial questions from denominator",
            "explicit",
        ),
        NegPair(
            "P07",
            "centralized multiagent orchestrator improves accuracy on sequential plancraft tasks",
            "centralized multiagent orchestrator does not improve accuracy on sequential plancraft tasks",
            "centralized multiagent orchestrator improves accuracy on sequential plancraft tasks",
            "centralized multiagent orchestrator never improves accuracy on sequential plancraft tasks",
            "explicit",
        ),
        NegPair(
            "P08",
            "bi_temporal graph edge remains active after invalid_at timestamp is assigned",
            "bi_temporal graph edge is not active after invalid_at timestamp is assigned",
            "bi_temporal graph edge remains active after invalid_at timestamp is assigned",
            "bi_temporal graph edge is no longer active after invalid_at timestamp is assigned",
            "explicit",
        ),
        NegPair(
            "P09",
            "atomic checkout lease allows concurrent repair writes across worktrees",
            "atomic checkout lease prohibits concurrent repair writes across worktrees",
            "atomic checkout lease permits concurrent repair writes across worktrees",
            "atomic checkout lease forbids concurrent repair writes across worktrees",
            "explicit",
        ),
        # 3 implicit/lexical/morphological negation queries (no 'not'/'no'/'forbid' token):
        NegPair(
            "P10",
            "observation masking retains older shell outputs outside recent window",
            "observation masking does not retain older shell outputs outside recent window",
            "observation masking retains older shell outputs outside recent window",
            "observation masking omits older shell outputs outside recent window",
            "implicit_lexical",
        ),
        NegPair(
            "P11",
            "sandboxed kernel verifier accepts theorem proofs containing native_decide axiom",
            "sandboxed kernel verifier does not accept theorem proofs containing native_decide axiom",
            "sandboxed kernel verifier accepts theorem proofs containing native_decide axiom",
            "sandboxed kernel verifier rejects theorem proofs containing native_decide axiom",
            "implicit_lexical",
        ),
        NegPair(
            "P12",
            "parallel tool dispatch is safe for stateful dependent database mutations",
            "parallel tool dispatch is not safe for stateful dependent database mutations",
            "parallel tool dispatch is safe for stateful dependent database mutations",
            "parallel tool dispatch is unsafe for stateful dependent database mutations",
            "implicit_lexical",
        ),
    ]


def build_exclusion_pairs() -> list[ExclPair]:
    """12 ExcluIR-style exclusionary retrieval pairs ('X excluding/without Y')."""
    return [
        ExclPair(
            "E01",
            "rust pointer cast guide for aligned initialized structs",
            "rust pointer cast guide for aligned structs using debug_assert mode",
            "rust pointer cast guide for aligned structs without debug_assert",
        ),
        ExclPair(
            "E02",
            "kv prefix cache optimization with static fixed tool schemas",
            "kv prefix cache optimization with dynamic tool schema injection",
            "kv prefix cache optimization excluding dynamic schema injection",
        ),
        ExclPair(
            "E03",
            "memfs precommit hook documentation for editable description frontmatter",
            "memfs precommit hook documentation for protected read_only frontmatter",
            "memfs precommit hook frontmatter rules except read_only",
        ),
        ExclPair(
            "E04",
            "agent memory compaction guide using batched observation masking",
            "agent memory compaction guide using recursive llm summarization",
            "agent memory compaction guide excluding llm summarization",
        ),
        ExclPair(
            "E05",
            "openhands condenser overview covering soft event count triggers",
            "openhands condenser overview covering hard_context_reset truncation",
            "openhands condenser overview without hard_context_reset truncation",
        ),
        ExclPair(
            "E06",
            "locomo benchmark evaluation protocol for categories one through four",
            "locomo benchmark evaluation protocol for adversarial category five",
            "locomo benchmark evaluation protocol excluding adversarial category",
        ),
        ExclPair(
            "E07",
            "multiagent coordination study on parallel finance tasks",
            "multiagent coordination study on sequential plancraft planning",
            "multiagent coordination study excluding sequential plancraft",
        ),
        ExclPair(
            "E08",
            "bi_temporal graphiti edge query for currently valid facts",
            "bi_temporal graphiti edge query for expired invalidated facts",
            "bi_temporal graphiti edge query without expired invalidated facts",
        ),
        ExclPair(
            "E09",
            "git checkout lease handling for concurrent read operations",
            "git checkout lease handling for conflicting rebase merge writes",
            "git checkout lease handling excluding rebase merge conflicts",
        ),
        ExclPair(
            "E10",
            "swe_agent history processor preserving failure stack traces",
            "swe_agent history processor dumping verbose older shell logs",
            "swe_agent history processor excluding verbose older logs",
        ),
        ExclPair(
            "E11",
            "lean4 kernel proof audit for pure tactic derivations",
            "lean4 kernel proof audit for sorryAx native_decide escapes",
            "lean4 kernel proof audit excluding native_decide escapes",
        ),
        ExclPair(
            "E12",
            "tool dispatch concurrency rules for pure idempotent queries",
            "tool dispatch concurrency rules for stateful race mutations",
            "tool dispatch concurrency rules without stateful mutations",
        ),
    ]


def build_disjoint_affirmative_control_pairs() -> list[AffirmPair]:
    """12 disjoint-topic affirmative baseline pairs (sanity check)."""
    raw = [
        (
            "rust pointer alignment check validates byte offsets in zerocopy layout",
            "python garbage collector sweeps cyclic heap frames in generational pools",
            "zerocopy rust pointer alignment byte offset layout validation",
            "python generational garbage collector cyclic heap frame sweep",
        ),
        (
            "kv prefix cache reuses prompt attention tensors across sequential turns",
            "relational sql btree index accelerates range scans on disk pages",
            "prompt attention tensor reuse in kv prefix cache turns",
            "disk page range scan acceleration via sql btree index",
        ),
        (
            "git precommit hook validates markdown yaml frontmatter schema fields",
            "docker container runtime mounts overlayfs root layers in linux namespaces",
            "markdown yaml frontmatter schema check in git precommit hook",
            "linux namespace overlayfs root layer mount in docker runtime",
        ),
        (
            "bi_temporal knowledge graph stores valid_at and created_at edge timestamps",
            "acoustic fourier transform decomposes audio waveforms into frequency bins",
            "valid_at created_at edge timestamp storage in bi_temporal graph",
            "audio waveform frequency bin decomposition using fourier transform",
        ),
        (
            "bm25 sparse inverted index scores exact identifier term frequencies",
            "convolutional neural renderer rasterizes triangle meshes into depth buffers",
            "exact identifier term frequency scoring with bm25 inverted index",
            "triangle mesh rasterization into depth buffers with neural renderer",
        ),
        (
            "lean4 kernel typechecker verifies dependent proof terms against axioms",
            "http2 transport multiplexer streams framed headers over tls sockets",
            "dependent proof term verification in lean4 kernel typechecker",
            "framed header streaming over tls sockets in http2 multiplexer",
        ),
        (
            "token bucket rate limiter smooths bursty api client requests",
            "smith waterman dynamic programming aligns nucleotide dna sequences",
            "bursty api request smoothing with token bucket rate limiter",
            "dna nucleotide sequence alignment via smith waterman programming",
        ),
        (
            "raft consensus protocol replicates log entries across quorum followers",
            "ray marching volumetric shader integrates cloud scattering opacity",
            "quorum follower log replication in raft consensus protocol",
            "cloud scattering opacity integration in ray marching shader",
        ),
        (
            "swe_agent history processor batches observation elision with polling interval",
            "kalman filter estimates noisy robot odometry trajectories from imu sensors",
            "observation elision batching polling interval in swe_agent processor",
            "imu sensor noisy robot odometry estimation using kalman filter",
        ),
        (
            "ast call graph traversal expands callee symbols across repository modules",
            "huffman prefix coding compresses symbol histograms into bitstreams",
            "repository module callee symbol expansion via ast call graph",
            "symbol histogram bitstream compression with huffman prefix coding",
        ),
        (
            "monotonic lease token prevents stale worker compare_and_set overwrite races",
            "simplex linear solver optimizes polyhedral objective constraints",
            "compare_and_set overwrite race prevention using monotonic lease token",
            "polyhedral objective constraint optimization via simplex linear solver",
        ),
        (
            "structured json response schema parses grader labels deterministically",
            "dijkstra priority queue computes shortest weighted road network paths",
            "deterministic grader label parsing with structured json schema",
            "weighted road network shortest path computation using dijkstra queue",
        ),
    ]
    return [AffirmPair(f"C{i:02d}", a, b, qa, qb) for i, (a, b, qa, qb) in enumerate(raw)]


def build_adversarial_affirmative_pairs() -> list[AffirmPair]:
    """12 adversarial near-minimal-pair affirmative technical prose pairs.

    In each pair, doc_a and doc_b share the SAME technical topic; query_a uses an
    affirmative technical term ('longer', 'fails', 'drops', 'rejects', 'unsafe',
    'invalidated', 'omits', 'blocked', 'invalid') that matches doc_a's affirmative
    behavior (written without the leaky keyword), while doc_b is a sibling variant
    on the same topic that contains a leaky cue word. A naive leaky cue list flips
    query_a to polarity -1, penalizing doc_a and boosting doc_b.
    """
    return [
        AffirmPair(
            "A01",
            "extended multi session context window improves factual recall across episodes",
            "short multi session context window drops factual recall across episodes",
            "longer multi session context window improves factual recall across episodes",
            "short multi session context window truncation across episodes",
        ),
        AffirmPair(
            "A02",
            "schema validation handler returns structured json error code on mismatch",
            "schema validation handler fails silently and skips json error code",
            "when schema validation fails return structured json error code",
            "schema validation handler silently skips json error code",
        ),
        AffirmPair(
            "A03",
            "batched observation masking elides stale shell stdout to cut prefill cost",
            "rolling observation masking drops kv prefix cache hit ratio every turn",
            "observation masking drops old shell stdout to cut prefill cost",
            "rolling observation masking prefix cache hit ratio penalty",
        ),
        AffirmPair(
            "A04",
            "precommit hook blocks malformed yaml frontmatter and exits nonzero",
            "precommit hook rejects valid markdown edits when config lock is blocked",
            "precommit hook rejects malformed yaml frontmatter with nonzero exit",
            "precommit hook config lock error on markdown edits",
        ),
        AffirmPair(
            "A05",
            "raw pointer cast guide specifies alignment and initialization invariants",
            "raw pointer cast compiler warning flags unsafe dereference in ffi crate",
            "unsafe pointer cast requirements for alignment and initialization invariants",
            "compiler lint warning for raw pointer dereference in ffi crate",
        ),
        AffirmPair(
            "A06",
            "bi_temporal graph edge query audits superseded facts via expired_at timestamps",
            "bi_temporal graph edge query drops invalidated entries during compaction",
            "bi_temporal graph query for invalidated facts via expired_at timestamps",
            "bi_temporal graph compaction purging expired entries",
        ),
        AffirmPair(
            "A07",
            "compact event condenser elides verbose shell output while preserving task ids",
            "compact event condenser omits critical task ids during hard context reset",
            "compact event condenser omits verbose shell output while keeping task ids",
            "compact event condenser hard context reset task id loss",
        ),
        AffirmPair(
            "A08",
            "atomic repair lock serializes concurrent worktree writers until completion",
            "atomic repair lock leaves crashed worker blocked indefinitely on stale pid",
            "atomic repair lock keeps concurrent worktree writers blocked until completion",
            "atomic repair lock stale pid handling after crashed worker",
        ),
        AffirmPair(
            "A09",
            "wide polling stride amortizes prefix cache invalidation across ten turns",
            "short polling stride triggers invalid cache churn across every single turn",
            "longer polling stride amortizes prefix cache invalidation across ten turns",
            "short polling stride cache churn across single turns",
        ),
        AffirmPair(
            "A10",
            "resilient build runner logs timeout diagnostics when compile step errors",
            "resilient build runner fails to collect timeout diagnostics during hang",
            "resilient build runner logs timeout diagnostics when compile step fails",
            "resilient build runner diagnostic collection bug during hang",
        ),
        AffirmPair(
            "A11",
            "code localization ablation measures recall reduction after graph removal",
            "code localization pipeline drops bm25 lexical index after config change",
            "code localization ablation shows recall drops after graph removal",
            "code localization pipeline bm25 lexical index config change",
        ),
        AffirmPair(
            "A12",
            "ingestion parser catches malformed iso timestamp strings before commit",
            "ingestion parser silently accepts invalid iso timestamp strings on import",
            "ingestion parser catches invalid iso timestamp strings before commit",
            "ingestion parser silent acceptance of malformed timestamps on import",
        ),
    ]


def build_code_graph_benchmark() -> tuple[dict[str, CodeSymbol], list[CodeTask]]:
    """48-symbol synthetic codebase + 12 2-hop dependency-reachability tasks.

    Targets have ZERO lexical overlap with symptom prose by construction; this
    sub-probe tests deterministic 2-hop graph reachability vs. lexical lookup
    (not empirical LocAgent benchmark accuracy).
    """
    specs = [
        ("T01", "applyMemfsFlags", "installMemoryGitHooks", "validateTreeBudget",
         "memfs startup ignores root markdown character budget limit"),
        ("T02", "claimMemoryConflictRepair", "updateAttemptMarker", "checkPidStartTime",
         "stale repair lock never reaped after crashed worker restart"),
        ("T03", "condenseViewEvents", "computeForgettingSlice", "findManipulationBoundary",
         "condenser splits atomic tool call observation pair incorrectly"),
        ("T04", "hardContextReset", "retryTruncatedSummary", "scaleEventStringCap",
         "context overflow fallback throws unhandled exception after retries"),
        ("T05", "scoreLocomoGrades", "accumulateCategoryStats", "normalizeDenominator",
         "locomo accuracy exceeds expected ceiling with adversarial category"),
        ("T06", "buildZepAnswerPrompt", "formatEdgeValidityWindow", "resolveEventClock",
         "temporal relative date subtracted twice from event timestamp"),
        ("T07", "dispatchToolBatch", "scheduleStateWrite", "acquireRowVersionGate",
         "parallel tool calls race and corrupt stateful database row"),
        ("T08", "runSweAgentHistory", "computeElisionWindow", "alignPollingStride",
         "prompt cache hit rate drops on every turn after observation window"),
        ("T09", "auditProofBoundary", "inspectKernelAxioms", "rejectBoolReduction",
         "proof audit fails to flag native_decide unsound axiom leakage"),
        ("T10", "ingestGithubSweep", "filterRepoMetadata", "dedupeCoauthorTrailers",
         "ecosystem commit sweep misattributes human commits to coding bot"),
        ("T11", "runTestLogParser", "extractPytestBlocks", "mergeMultilineTrace",
         "multiline pytest failure status dropped by regex log matcher"),
        ("T12", "routeHybridRetriever", "expandSymbolNeighbors", "rankPolarityCrossGate",
         "negated precondition query ranks forbidden api document first"),
    ]

    symbols: dict[str, CodeSymbol] = {}
    tasks: list[CodeTask] = []
    for tid, entry, mid, target, symptom in specs:
        symbols[entry] = CodeSymbol(
            entry,
            f"fn {entry} orchestrates workflow for {symptom} and invokes {mid}",
            (mid,),
        )
        symbols[mid] = CodeSymbol(
            mid,
            f"fn {mid} intermediate dispatcher delegating state check to {target}",
            (target,),
        )
        symbols[target] = CodeSymbol(
            target,
            f"fn {target} low_level invariant kernel guard enforcing internal offset counter",
            (),
        )
        distractor = f"docComment_{tid}"
        symbols[distractor] = CodeSymbol(
            distractor,
            f"fn {distractor} logging stub mentioning {symptom} {symptom} telemetry note",
            (),
        )
        tasks.append(
            CodeTask(
                task_id=tid,
                query=f"bug in {entry}: {symptom}",
                target_sym=target,
            )
        )
    return symbols, tasks


class BM25Index:
    def __init__(self, docs: dict[str, str], k1: float = 1.5, b: float = 0.75) -> None:
        self.k1 = k1
        self.b = b
        self.doc_tokens = {did: tokenize(txt) for did, txt in docs.items()}
        self.doc_tf = {did: Counter(toks) for did, toks in self.doc_tokens.items()}
        self.doc_len = {did: len(toks) for did, toks in self.doc_tokens.items()}
        self.avgdl = sum(self.doc_len.values()) / max(1, len(self.doc_len))
        self.n_docs = len(docs)
        df: Counter[str] = Counter()
        for tf in self.doc_tf.values():
            for tok in tf:
                df[tok] += 1
        self.idf = {
            tok: math.log(1.0 + (self.n_docs - freq + 0.5) / (freq + 0.5))
            for tok, freq in df.items()
        }

    def score(self, query: str, doc_id: str) -> float:
        q_toks = tokenize(query)
        tf = self.doc_tf[doc_id]
        dl = self.doc_len[doc_id]
        total = 0.0
        for tok in q_toks:
            f = tf.get(tok, 0)
            if f == 0:
                continue
            idf = self.idf.get(tok, 0.0)
            denom = f + self.k1 * (1.0 - self.b + self.b * (dl / max(1.0, self.avgdl)))
            total += idf * (f * (self.k1 + 1.0)) / denom
        return total


class DenseBiEncoderProxy:
    """Negation-token-blind dense bi-encoder surrogate (structural illustration)."""

    def __init__(self, docs: dict[str, str]) -> None:
        self.doc_vecs: dict[str, dict[str, float]] = {}
        ignored = EXPLICIT_NEGATION_WORDS | EXCLUSION_PREPOSITIONS | FUNCTION_STOPWORDS
        content_docs = {
            did: [t for t in tokenize(txt) if t not in ignored]
            for did, txt in docs.items()
        }
        n_docs = len(docs)
        df: Counter[str] = Counter()
        for toks in content_docs.values():
            for t in set(toks):
                df[t] += 1
        self.idf = {
            t: math.log((n_docs + 1.0) / (freq + 1.0)) + 1.0 for t, freq in df.items()
        }
        for did, toks in content_docs.items():
            self.doc_vecs[did] = self._embed(toks)

    def _embed(self, toks: list[str]) -> dict[str, float]:
        tf = Counter(toks)
        vec = {t: (1.0 + math.log(c)) * self.idf.get(t, 1.0) for t, c in tf.items()}
        norm = math.sqrt(sum(v * v for v in vec.values())) or 1.0
        return {t: v / norm for t, v in vec.items()}

    def score(self, query: str, doc_id: str) -> float:
        ignored = EXPLICIT_NEGATION_WORDS | EXCLUSION_PREPOSITIONS | FUNCTION_STOPWORDS
        q_toks = [t for t in tokenize(query) if t not in ignored]
        q_vec = self._embed(q_toks)
        d_vec = self.doc_vecs[doc_id]
        return sum(v * d_vec.get(t, 0.0) for t, v in q_vec.items())


def extract_polarity_leaky(text: str) -> tuple[int, set[str]]:
    """Naive leaky lexical cue parser (includes domain verbs/adjectives like 'longer', 'fails', 'drops')."""
    toks = tokenize(text)
    neg_cues = EXPLICIT_NEGATION_WORDS | LEAKY_DOMAIN_CUES
    excluded: set[str] = set()
    for i, t in enumerate(toks):
        if t in EXCLUSION_PREPOSITIONS:
            for nxt in toks[i + 1 : i + 4]:
                if nxt not in FUNCTION_STOPWORDS and nxt not in EXCLUSION_PREPOSITIONS:
                    excluded.add(nxt)
    clause_neg = any(t in neg_cues and t not in EXCLUSION_PREPOSITIONS for t in toks)
    return (-1 if clause_neg else 1), excluded


def extract_polarity_scoped(text: str) -> tuple[int, set[str]]:
    """Scoped grammatical negation + exclusion parser (fixes leaky single-word cues).

    Replaces standalone 'longer' with phrase 'no longer' and excludes polysemous
    domain terms ('fails', 'drops', 'unsafe', 'invalid', 'rejects', 'omits',
    'blocked') from unconditional clause negation. Transparently loses recall on
    implicit lexical/morphological negations (P10-P12) while eliminating false
    polarity flips on affirmative technical prose.
    """
    toks = tokenize(text)
    excluded: set[str] = set()
    for i, t in enumerate(toks):
        if t in EXCLUSION_PREPOSITIONS:
            for nxt in toks[i + 1 : i + 4]:
                if nxt not in FUNCTION_STOPWORDS and nxt not in EXCLUSION_PREPOSITIONS:
                    excluded.add(nxt)

    bigrams = set(zip(toks, toks[1:]))
    has_phrase_neg = ("no", "longer") in bigrams
    has_explicit_neg = any(
        t in EXPLICIT_NEGATION_WORDS and t not in EXCLUSION_PREPOSITIONS for t in toks
    )
    polarity = -1 if (has_phrase_neg or has_explicit_neg) else 1
    return polarity, excluded


def score_polarity_gate(
    base_bm25: float, query: str, doc_text: str, *, mode: str
) -> float:
    extractor = extract_polarity_leaky if mode == "leaky" else extract_polarity_scoped
    q_pol, q_excl = extractor(query)
    d_pol, _ = extractor(doc_text)
    d_toks = set(tokenize(doc_text))

    score = base_bm25
    if q_excl:
        violated = len(q_excl & d_toks)
        score -= 8.0 * violated
        if d_pol < 0:
            score -= 3.0
    else:
        if q_pol == d_pol:
            score += 4.5
        else:
            score -= 4.5
    return score


def run_probe_3() -> dict[str, object]:
    print("\n" + "=" * 86)
    print(
        "PROBE 3 [toy model / mechanistic surrogate]: Polarity Trade-Off & 2-Hop Reachability"
    )
    print("=" * 86)

    pairs = build_negation_pairs()
    neg_docs: dict[str, str] = {}
    for p in pairs:
        neg_docs[f"{p.pair_id}+"] = p.pos_doc
        neg_docs[f"{p.pair_id}-"] = p.neg_doc

    excl_pairs = build_exclusion_pairs()
    excl_docs: dict[str, str] = {}
    for ep in excl_pairs:
        excl_docs[f"{ep.pair_id}+"] = ep.allowed_doc
        excl_docs[f"{ep.pair_id}-"] = ep.excluded_doc

    disjoint_pairs = build_disjoint_affirmative_control_pairs()
    disjoint_docs: dict[str, str] = {}
    for ap in disjoint_pairs:
        disjoint_docs[f"{ap.pair_id}a"] = ap.doc_a
        disjoint_docs[f"{ap.pair_id}b"] = ap.doc_b

    adv_pairs = build_adversarial_affirmative_pairs()
    adv_docs: dict[str, str] = {}
    for ap in adv_pairs:
        adv_docs[f"{ap.pair_id}a"] = ap.doc_a
        adv_docs[f"{ap.pair_id}b"] = ap.doc_b

    dense_neg, bm25_neg = DenseBiEncoderProxy(neg_docs), BM25Index(neg_docs)
    dense_excl, bm25_excl = DenseBiEncoderProxy(excl_docs), BM25Index(excl_docs)
    dense_disj, bm25_disj = DenseBiEncoderProxy(disjoint_docs), BM25Index(disjoint_docs)
    dense_adv, bm25_adv = DenseBiEncoderProxy(adv_docs), BM25Index(adv_docs)

    def eval_suite(method: str) -> tuple[float, float, float, float, float]:
        # 1. NevIR paired accuracy (explicit 9 + implicit_lexical 3)
        paired_ok = 0
        explicit_ok = 0
        for p in pairs:
            id_pos, id_neg = f"{p.pair_id}+", f"{p.pair_id}-"
            if method == "dense":
                sp_pos, sp_neg = dense_neg.score(p.pos_query, id_pos), dense_neg.score(p.pos_query, id_neg)
                sn_pos, sn_neg = dense_neg.score(p.neg_query, id_pos), dense_neg.score(p.neg_query, id_neg)
            elif method == "bm25":
                sp_pos, sp_neg = bm25_neg.score(p.pos_query, id_pos), bm25_neg.score(p.pos_query, id_neg)
                sn_pos, sn_neg = bm25_neg.score(p.neg_query, id_pos), bm25_neg.score(p.neg_query, id_neg)
            else:
                mode = "leaky" if method == "bm25_leaky_gate" else "scoped"
                sp_pos = score_polarity_gate(bm25_neg.score(p.pos_query, id_pos), p.pos_query, p.pos_doc, mode=mode)
                sp_neg = score_polarity_gate(bm25_neg.score(p.pos_query, id_neg), p.pos_query, p.neg_doc, mode=mode)
                sn_pos = score_polarity_gate(bm25_neg.score(p.neg_query, id_pos), p.neg_query, p.pos_doc, mode=mode)
                sn_neg = score_polarity_gate(bm25_neg.score(p.neg_query, id_neg), p.neg_query, p.neg_doc, mode=mode)
            if sp_pos > sp_neg and sn_neg > sn_pos:
                paired_ok += 1
                if p.neg_kind == "explicit":
                    explicit_ok += 1

        # 2. ExcluIR RR
        excl_ok = 0
        for ep in excl_pairs:
            id_ok, id_bad = f"{ep.pair_id}+", f"{ep.pair_id}-"
            if method == "dense":
                s_ok, s_bad = dense_excl.score(ep.excl_query, id_ok), dense_excl.score(ep.excl_query, id_bad)
            elif method == "bm25":
                s_ok, s_bad = bm25_excl.score(ep.excl_query, id_ok), bm25_excl.score(ep.excl_query, id_bad)
            else:
                mode = "leaky" if method == "bm25_leaky_gate" else "scoped"
                s_ok = score_polarity_gate(bm25_excl.score(ep.excl_query, id_ok), ep.excl_query, ep.allowed_doc, mode=mode)
                s_bad = score_polarity_gate(bm25_excl.score(ep.excl_query, id_bad), ep.excl_query, ep.excluded_doc, mode=mode)
            if s_ok > s_bad:
                excl_ok += 1

        # 3. Disjoint affirmative control
        disj_ok = 0
        for ap in disjoint_pairs:
            ida, idb = f"{ap.pair_id}a", f"{ap.pair_id}b"
            if method == "dense":
                saa, sab = dense_disj.score(ap.query_a, ida), dense_disj.score(ap.query_a, idb)
                sba, sbb = dense_disj.score(ap.query_b, ida), dense_disj.score(ap.query_b, idb)
            elif method == "bm25":
                saa, sab = bm25_disj.score(ap.query_a, ida), bm25_disj.score(ap.query_a, idb)
                sba, sbb = bm25_disj.score(ap.query_b, ida), bm25_disj.score(ap.query_b, idb)
            else:
                mode = "leaky" if method == "bm25_leaky_gate" else "scoped"
                saa = score_polarity_gate(bm25_disj.score(ap.query_a, ida), ap.query_a, ap.doc_a, mode=mode)
                sab = score_polarity_gate(bm25_disj.score(ap.query_a, idb), ap.query_a, ap.doc_b, mode=mode)
                sba = score_polarity_gate(bm25_disj.score(ap.query_b, ida), ap.query_b, ap.doc_a, mode=mode)
                sbb = score_polarity_gate(bm25_disj.score(ap.query_b, idb), ap.query_b, ap.doc_b, mode=mode)
            if saa > sab and sbb > sba:
                disj_ok += 1

        # 4. Adversarial near-minimal-pair affirmative stress test
        adv_ok = 0
        for ap in adv_pairs:
            ida, idb = f"{ap.pair_id}a", f"{ap.pair_id}b"
            if method == "dense":
                saa, sab = dense_adv.score(ap.query_a, ida), dense_adv.score(ap.query_a, idb)
                sba, sbb = dense_adv.score(ap.query_b, ida), dense_adv.score(ap.query_b, idb)
            elif method == "bm25":
                saa, sab = bm25_adv.score(ap.query_a, ida), bm25_adv.score(ap.query_a, idb)
                sba, sbb = bm25_adv.score(ap.query_b, ida), bm25_adv.score(ap.query_b, idb)
            else:
                mode = "leaky" if method == "bm25_leaky_gate" else "scoped"
                saa = score_polarity_gate(bm25_adv.score(ap.query_a, ida), ap.query_a, ap.doc_a, mode=mode)
                sab = score_polarity_gate(bm25_adv.score(ap.query_a, idb), ap.query_a, ap.doc_b, mode=mode)
                sba = score_polarity_gate(bm25_adv.score(ap.query_b, ida), ap.query_b, ap.doc_a, mode=mode)
                sbb = score_polarity_gate(bm25_adv.score(ap.query_b, idb), ap.query_b, ap.doc_b, mode=mode)
            if saa > sab and sbb > sba:
                adv_ok += 1

        n_explicit = sum(1 for p in pairs if p.neg_kind == "explicit")
        return (
            paired_ok / len(pairs),
            explicit_ok / n_explicit,
            excl_ok / len(excl_pairs),
            disj_ok / len(disjoint_pairs),
            adv_ok / len(adv_pairs),
        )

    print(
        "\n[3A/3B] Synthetic Polarity/Exclusion Mechanics & Adversarial Affirmative Stress Test"
    )
    print(
        "  (NevIR all=12 [9 explicit + 3 implicit], rand=25%; ExcluIR=12, rand=50%;"
    )
    print(
        "   AdvAffirm=12 affirmative technical pairs with 'longer'/'fails'/'drops'/etc.):"
    )
    print(
        f"{'Retriever':<28} | {'NevIR All':>9} | {'NevIR Expl':>10} | "
        f"{'ExcluIR':>7} | {'DisjCtrl':>8} | {'AdvAffirm':>9}"
    )
    print("-" * 86)
    neg_metrics: dict[str, tuple[float, float, float, float, float]] = {}
    for label, key in [
        ("(a) Dense Bi-Encoder Proxy", "dense"),
        ("(b) BM25 Lexical", "bm25"),
        ("(c) BM25 + Leaky Cue Gate", "bm25_leaky_gate"),
        ("(d) BM25 + Scoped Gate", "bm25_scoped_gate"),
    ]:
        p_all, p_exp, e_rr, d_ctrl, a_ctrl = eval_suite(key)
        neg_metrics[key] = (p_all, p_exp, e_rr, d_ctrl, a_ctrl)
        print(
            f"{label:<28} | {p_all*100:>8.1f}% | {p_exp*100:>9.1f}% | "
            f"{e_rr*100:>6.1f}% | {d_ctrl*100:>7.1f}% | {a_ctrl*100:>8.1f}%"
        )

    # Report explicit false-positive flip count on adversarial affirmative queries
    leaky_fp = sum(
        1 for ap in adv_pairs if extract_polarity_leaky(ap.query_a)[0] == -1
    )
    scoped_fp = sum(
        1 for ap in adv_pairs if extract_polarity_scoped(ap.query_a)[0] == -1
    )
    print(
        f"  Affirmative false-polarity flips on AdvAffirm query_a: "
        f"Leaky={leaky_fp}/{len(adv_pairs)} ({leaky_fp/len(adv_pairs)*100:.1f}%) -> "
        f"Scoped={scoped_fp}/{len(adv_pairs)} ({scoped_fp/len(adv_pairs)*100:.1f}%)."
    )
    print(
        f"  Precision/recall limit: removing leaky lexical cues repairs AdvAffirm "
        f"({neg_metrics['bm25_leaky_gate'][4]*100:.1f}%->{neg_metrics['bm25_scoped_gate'][4]*100:.1f}%)"
    )
    print(
        f"  but drops NevIR recall on implicit lexical/morphological negations (P10 'omits',"
    )
    print(
        f"  P11 'rejects', P12 'unsafe': {neg_metrics['bm25_leaky_gate'][0]*100:.1f}%->"
        f"{neg_metrics['bm25_scoped_gate'][0]*100:.1f}%), illustrating why lexical cue lists"
    )
    print(
        "  cannot substitute for trained NLI/cross-encoder rerankers (e.g., MonoT5-3B 50.6%)."
    )

    # 3C. Deterministic 2-Hop Dependency-Graph Reachability (distinct retrievers only; no dead branch)
    symbols, code_tasks = build_code_graph_benchmark()
    code_docs = {sid: sym.text for sid, sym in symbols.items()}
    dense_code = DenseBiEncoderProxy(code_docs)
    bm25_code = BM25Index(code_docs)

    def eval_code_loc(method: str) -> tuple[float, float]:
        r_at_5 = 0
        mrr_sum = 0.0
        for task in code_tasks:
            if method == "dense":
                raw = {sid: dense_code.score(task.query, sid) for sid in symbols}
            elif method == "bm25":
                raw = {sid: bm25_code.score(task.query, sid) for sid in symbols}
            elif method in ("bm25_graph_1hop", "bm25_graph_2hop"):
                base = {sid: bm25_code.score(task.query, sid) for sid in symbols}
                max_hops = 1 if method == "bm25_graph_1hop" else 2
                anchors = sorted(base, key=lambda s: (-base[s], s))[:3]
                raw = dict(base)
                for a in anchors:
                    a_score = base[a]
                    if a_score <= 0:
                        continue
                    frontier = [(a, 0)]
                    visited = {a}
                    while frontier:
                        curr, h = frontier.pop(0)
                        if h >= max_hops:
                            continue
                        for nxt in symbols[curr].callees:
                            if nxt not in visited:
                                visited.add(nxt)
                                bonus = a_score * (0.85 ** (h + 1))
                                raw[nxt] = max(raw[nxt], bonus)
                                frontier.append((nxt, h + 1))
            else:
                raise ValueError(method)

            ranked = sorted(raw, key=lambda s: (-raw[s], s))
            rank = ranked.index(task.target_sym) + 1
            if rank <= 5:
                r_at_5 += 1
            mrr_sum += 1.0 / rank
        return r_at_5 / len(code_tasks), mrr_sum / len(code_tasks)

    print(
        "\n[3C] Deterministic 2-Hop Dependency-Graph Reachability vs Zero-Overlap Lookup"
    )
    print(
        "  (12 synthetic tasks, 48 symbols; zero symptom-token overlap on target by design —"
    )
    print(
        "   demonstrates structural reachability ONLY, NOT empirical LocAgent accuracy):"
    )
    print(f"{'Retriever':<32} | {'Recall@5':>8} | {'MRR':>8}")
    print("-" * 55)
    code_metrics: dict[str, tuple[float, float]] = {}
    for label, key in [
        ("(a) Dense Bi-Encoder Proxy", "dense"),
        ("(b) BM25 Lexical", "bm25"),
        ("(c1) BM25 + 1-Hop Graph", "bm25_graph_1hop"),
        ("(c2) BM25 + 2-Hop Graph", "bm25_graph_2hop"),
    ]:
        r5, mrr = eval_code_loc(key)
        code_metrics[key] = (r5, mrr)
        print(f"{label:<32} | {r5*100:>7.1f}% | {mrr:>8.4f}")

    # Non-vacuity, adversarial false-positive, and reachability assertions:
    assert neg_metrics["dense"][0] < 0.25
    assert neg_metrics["dense"][2] <= 0.50
    assert neg_metrics["dense"][3] >= 0.90
    assert neg_metrics["dense"][4] >= 0.90
    # Leaky gate overfits NevIR (100%) but collapses on adversarial affirmative prose!
    assert neg_metrics["bm25_leaky_gate"][0] == 1.0
    assert leaky_fp == len(adv_pairs)
    assert neg_metrics["bm25_leaky_gate"][4] <= 0.30
    # Scoped gate eliminates all 12 affirmative false-polarity flips and restores AdvAffirm,
    # while achieving 100% on explicit negations + exclusions and honestly missing implicit lexical ones.
    assert scoped_fp == 0
    assert neg_metrics["bm25_scoped_gate"][4] == 1.0
    assert neg_metrics["bm25"][4] == 1.0
    assert neg_metrics["bm25_scoped_gate"][1] == 1.0
    assert neg_metrics["bm25_scoped_gate"][2] == 1.0
    assert 0.70 <= neg_metrics["bm25_scoped_gate"][0] <= 0.80
    # Deterministic 2-hop reachability checks
    assert code_metrics["dense"][0] < 0.20
    assert code_metrics["bm25"][0] < 0.20
    assert code_metrics["bm25_graph_1hop"][0] < 0.20
    assert code_metrics["bm25_graph_2hop"][0] == 1.0

    print(
        "  [PASS] Probe 3 assertions verified (dense negation/exclusion collapse, leaky cue "
        "false-positive exposure & scoped repair with honest implicit-negation recall limit, "
        "deterministic 2-hop graph reachability)."
    )
    return {
        "neg_metrics": neg_metrics,
        "code_metrics": code_metrics,
        "leaky_fp": leaky_fp,
        "scoped_fp": scoped_fp,
    }


def main() -> int:
    print(
        f"verify_compaction_coordination_retrieval_probes.py | seed={SEED} | stdlib-only deterministic run"
    )
    rng = random.Random(SEED)

    p1 = run_probe_1(rng)
    p2 = run_probe_2()
    p3 = run_probe_3()

    digest_payload = (
        f"p1:{p1['het_pass8']:.8f}:{p1['iid_pass8']:.8f}:{p1['task_tail_bad']:.6f}:"
        f"p2:{p2['res'][('10x', 60, 'mask_poll1')].total_usd:.8f}:"
        f"{p2['res'][('10x', 120, 'mask_poll10')].total_usd:.8f}:"
        f"{p2['res'][('10x', 120, 'jetbrains_hybrid')].total_usd:.8f}:"
        f"{p2['cross_poll1_raw_4x']}:{p2['cross_poll1_raw_10x']}:{p2['cross_hybrid_poll10_10x']}:"
        f"p3:{p3['neg_metrics']['dense']}:{p3['neg_metrics']['bm25_leaky_gate']}:"
        f"{p3['neg_metrics']['bm25_scoped_gate']}:{p3['code_metrics']['bm25_graph_2hop']}"
    )
    fingerprint = hashlib.sha256(digest_payload.encode("utf-8")).hexdigest()[:16]

    print("\n" + "=" * 86)
    print(f"ALL 3 PROBES & NEGATIVE CONTROLS PASSED | seed={SEED} | digest={fingerprint} (exit 0)")
    print("=" * 86)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
