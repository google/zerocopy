#!/usr/bin/env python3
"""
Deterministic executable verification suite covering five empirical and formal pillars:
  1. Horvitz (CHI 1999) mixed-initiative expected-utility identities (Eqs. 1-3, Fig. 6),
     dialog-collapse boundary, Fig. 5 leftward shift vs. attention-cost rightward shift,
     and stylized LookOut sigmoid dwell deferral (Fig. 7).
  2. Pinned user-simulator parser/orchestrator forensics reproduced verbatim from
     sierra-research/tau-bench@59a200c6, sierra-research/tau2-bench@768f3d8f, and
     SALT-NLP/collaborative-gym@58972c07, plus controlled multi-proxy rank-inversion
     and correlation-regime simulations.
  3. CollabLLM (arXiv:2502.00640) unified single-reward finite-horizon belief-MDP
     (w = 0..3 with terminal-state precedence and zero-info-ASK anti-vacuity control)
     and norm-matched equal-SNR OPEN (arXiv:2403.05534, Eq. 5) Bradley-Terry BOED
     with verified effective sample size (ESS).
  4. Derived arithmetic verification on Bastani et al. (PNAS 2025;
     obastani/GenAICanHarmLearning@2f63dae1) Table 1 / sufficient statistics (both
     cluster-df t_{43} and asymptotic z=1.96 CIs) and Kestin et al. (Sci Rep 2025),
     plus verbatim eth-nlped/mathdial@60035095 evaluator forensics (unsigned regex,
     Round-0 walkthrough indexing convention & edge cases, and Telling@k coupling).
  5. Stylized cognitive-offloading vs. desirable-difficulty mechanistic simulation
     illustrating practice-vs-transfer polarity inversion and comfort-vs-transfer split.

Requirements: Python 3.10+ stdlib only, zero third-party packages, zero network or
disk I/O, deterministic under arbitrary PYTHONHASHSEED, wall time < 2.0s.
"""

from __future__ import annotations

import math
import operator
import random
import re
import statistics
from dataclasses import dataclass
from typing import Dict, List, Optional, Sequence, Tuple

_MUL = operator.mul


# =============================================================================
# PROBE 1: Horvitz (CHI 1999) Mixed-Initiative Expected-Utility Decision Model
# =============================================================================

@dataclass(frozen=True)
class HorvitzUtilities:
    u_a_g: float      # u(A, G): autonomous action when goal desired
    u_a_ng: float     # u(A, ~G): autonomous action when goal NOT desired
    u_na_g: float     # u(~A, G): inaction when goal desired
    u_na_ng: float    # u(~A, ~G): inaction when goal NOT desired
    u_d_g: float      # u(D, G): dialog when goal desired
    u_d_ng: float     # u(D, ~G): dialog when goal NOT desired


def eu_action(p: float, u: HorvitzUtilities) -> float:
    return p * u.u_a_g + (1.0 - p) * u.u_a_ng


def eu_inaction(p: float, u: HorvitzUtilities) -> float:
    return p * u.u_na_g + (1.0 - p) * u.u_na_ng


def eu_dialog(p: float, u: HorvitzUtilities) -> float:
    return p * u.u_d_g + (1.0 - p) * u.u_d_ng


def threshold_pair(u1_g: float, u1_ng: float, u2_g: float, u2_ng: float) -> float:
    """Solve p * u1_g + (1-p) * u1_ng = p * u2_g + (1-p) * u2_ng (Horvitz Eqs. 1-3)."""
    denom = (u2_g - u2_ng) - (u1_g - u1_ng)
    if abs(denom) < 1e-12:
        return math.nan
    return (u1_ng - u2_ng) / denom


def optimal_horvitz_action(p: float, u: HorvitzUtilities) -> str:
    scores = [
        ("INACTION", eu_inaction(p, u)),
        ("DIALOG", eu_dialog(p, u)),
        ("ACTION", eu_action(p, u)),
    ]
    return max(scores, key=lambda kv: kv[1])[0]


def lookout_sigmoid_dwell_stylized(
    msg_len: float,
    d_min: float = 2.0,
    d_max: float = 18.0,
    k: float = 0.015,
    midpoint: float = 250.0,
) -> float:
    """
    Stylized sigmoid parameterization illustrating Horvitz (CHI 1999, Fig. 7, p. 7)'s
    qualitative monotone LookOut dwell-vs.-message-length curve (Horvitz Fig. 7 plots
    an empirical curve over 0-2500 chars without publishing these parameter literals).
    """
    return d_min + (d_max - d_min) / (1.0 + math.exp(-k * (msg_len - midpoint)))


def run_probe_1() -> None:
    print("=" * 78)
    print("PROBE 1: Horvitz (CHI 1999) Mixed-Initiative Expected Utility & Dwell Gating")
    print("Provenance: [exact analytical identities (Eqs. 1-3)] + [stylized numerical model]")

    # Illustrative utility table satisfying standard Horvitz ordering:
    # At p=0: u(~A,~G) > u(D,~G) > u(A,~G); at p=1: u(A,G) > u(D,G) > u(~A,G).
    u_base = HorvitzUtilities(
        u_a_g=1.00, u_a_ng=0.00,
        u_na_g=0.20, u_na_ng=0.80,
        u_d_g=0.82, u_d_ng=0.62,
    )
    p_star = threshold_pair(u_base.u_na_g, u_base.u_na_ng, u_base.u_a_g, u_base.u_a_ng)
    p_na_d = threshold_pair(u_base.u_na_g, u_base.u_na_ng, u_base.u_d_g, u_base.u_d_ng)
    p_d_a = threshold_pair(u_base.u_d_g, u_base.u_d_ng, u_base.u_a_g, u_base.u_a_ng)
    dialog_width = max(0.0, p_d_a - p_na_d)

    # Exact algebraic equality at intersection points (Eqs. 1-3 & Fig. 6)
    assert abs(eu_action(p_star, u_base) - eu_inaction(p_star, u_base)) < 1e-12
    assert abs(eu_dialog(p_na_d, u_base) - eu_inaction(p_na_d, u_base)) < 1e-12
    assert abs(eu_action(p_d_a, u_base) - eu_dialog(p_d_a, u_base)) < 1e-12
    assert 0.0 < p_na_d < p_star < p_d_a < 1.0
    assert optimal_horvitz_action(p_na_d - 0.05, u_base) == "INACTION"
    assert optimal_horvitz_action(p_star, u_base) == "DIALOG"
    assert optimal_horvitz_action(p_d_a + 0.05, u_base) == "ACTION"

    # Dialog-collapse regime: raise dialog friction until p*_{~A,D} >= p*_{D,A}
    u_collapse = HorvitzUtilities(
        u_a_g=1.00, u_a_ng=0.00,
        u_na_g=0.20, u_na_ng=0.80,
        u_d_g=0.60, u_d_ng=0.35,
    )
    p_na_d_col = threshold_pair(u_collapse.u_na_g, u_collapse.u_na_ng, u_collapse.u_d_g, u_collapse.u_d_ng)
    p_d_a_col = threshold_pair(u_collapse.u_d_g, u_collapse.u_d_ng, u_collapse.u_a_g, u_collapse.u_a_ng)
    p_star_col = threshold_pair(u_collapse.u_na_g, u_collapse.u_na_ng, u_collapse.u_a_g, u_collapse.u_a_ng)
    assert p_na_d_col >= p_d_a_col
    assert eu_dialog(p_star_col, u_collapse) <= eu_action(p_star_col, u_collapse)
    grid_actions = {optimal_horvitz_action(i / 200.0, u_collapse) for i in range(201)}
    assert "DIALOG" not in grid_actions and grid_actions == {"INACTION", "ACTION"}

    # Horvitz Fig. 5 direct direction: INCREASING u(A, ~G) shifts p* monotonically LEFTWARD
    fig5_bonuses = [0.00, 0.15, 0.30]
    p_star_left: List[float] = []
    for inc in fig5_bonuses:
        u_inc = HorvitzUtilities(
            u_a_g=1.00, u_a_ng=0.00 + inc,
            u_na_g=0.20, u_na_ng=0.80,
            u_d_g=0.82, u_d_ng=0.62,
        )
        p_star_left.append(threshold_pair(u_inc.u_na_g, u_inc.u_na_ng, u_inc.u_a_g, u_inc.u_a_ng))
    assert p_star_left[0] > p_star_left[1] > p_star_left[2]

    # Stylized attention-depth cost sweep (Horvitz prose): DECREASING u(A, ~G) and u(D, ~G)
    # shifts action thresholds monotonically RIGHTWARD and increases +0.20 overconfidence EU regret.
    focus_penalties = [0.00, 0.15, 0.30, 0.45]
    p_da_series: List[float] = []
    p_star_series: List[float] = []
    overconf_regret_series: List[float] = []
    for pen in focus_penalties:
        u_f = HorvitzUtilities(
            u_a_g=1.00, u_a_ng=0.00 - pen,
            u_na_g=0.20, u_na_ng=0.80,
            u_d_g=0.82, u_d_ng=0.62 - 0.35 * pen,
        )
        p_s = threshold_pair(u_f.u_na_g, u_f.u_na_ng, u_f.u_a_g, u_f.u_a_ng)
        p_da = threshold_pair(u_f.u_d_g, u_f.u_d_ng, u_f.u_a_g, u_f.u_a_ng)
        p_star_series.append(p_s)
        p_da_series.append(p_da)

        regrets = []
        for i in range(201):
            p_true = i / 200.0
            p_hat = min(1.0, p_true + 0.20)
            a_opt = optimal_horvitz_action(p_true, u_f)
            a_ov = optimal_horvitz_action(p_hat, u_f)
            eu_map = {
                "INACTION": eu_inaction(p_true, u_f),
                "DIALOG": eu_dialog(p_true, u_f),
                "ACTION": eu_action(p_true, u_f),
            }
            regrets.append(eu_map[a_opt] - eu_map[a_ov])
        overconf_regret_series.append(statistics.fmean(regrets))

    for i in range(len(focus_penalties) - 1):
        assert p_star_series[i] < p_star_series[i + 1]
        assert p_da_series[i] < p_da_series[i + 1]
        assert overconf_regret_series[i] < overconf_regret_series[i + 1]

    # Stylized sigmoid dwell deferral monotonicity (qualitative Fig. 7 illustration)
    dwells = [lookout_sigmoid_dwell_stylized(L) for L in (50, 250, 500)]
    assert dwells[0] < dwells[1] < dwells[2]

    print(f"  Exact Eqs. 1-3 baseline: p*={p_star:.4f}, p*_~A,D={p_na_d:.4f}, p*_D,A={p_d_a:.4f}, dialog_band={dialog_width:.4f}")
    print(f"  Exact dialog collapse  : p*_~A,D={p_na_d_col:.4f} >= p*_D,A={p_d_a_col:.4f} -> dialog_band=0.0000 (201 pts)")
    print(f"  Fig. 5 leftward shift  : u(A,~G)=+0.00/+0.15/+0.30 -> p*={p_star_left[0]:.4f}/{p_star_left[1]:.4f}/{p_star_left[2]:.4f}")
    print("  Stylized attention-cost rightward shift (pen -> p*, p*_D,A, overconf_+0.20_EU_regret):")
    for pen, ps, pda, reg in zip(focus_penalties, p_star_series, p_da_series, overconf_regret_series):
        print(f"    pen={pen:.2f}: p*={ps:.4f}, p*_D,A={pda:.4f}, EU_regret={reg:.4f}")
    print(f"  Stylized Fig. 7 dwell(L=50,250,500): {dwells[0]:.2f}s, {dwells[1]:.2f}s, {dwells[2]:.2f}s")
    print("  [PASS] Probe 1 assertions satisfied.")


# =============================================================================
# PROBE 2: Pinned User-Simulator Forensics (tau-bench, tau2-bench, Co-Gym)
#          & Multi-Proxy Leaderboard Distortion Simulation
# =============================================================================

# --- Verbatim logic from sierra-research/tau-bench@59a200c6 ---
def tau_bench_react_parse_response(response: str) -> str:
    """Verbatim logic from tau_bench/envs/user.py:136-146 (commit 59a200c6)."""
    if "###STOP###" in response:
        return "###STOP###"
    elif "Thought:" in response:
        _, user_response = response.split("Thought:")
        return user_response.strip()
    elif "User Response:" in response:
        _, user_response = response.split("User Response:")
        return user_response.strip()
    else:
        raise ValueError(f"Invalid response format: {response}")


def tau_bench_env_done(observation: str) -> bool:
    """Verbatim logic from tau_bench/envs/base.py:99 (commit 59a200c6)."""
    return "###STOP###" in observation


# --- Verbatim logic from sierra-research/tau2-bench@768f3d8f ---
TAU2_STOP = "###STOP###"
TAU2_TRANSFER = "###TRANSFER###"
TAU2_OUT_OF_SCOPE = "###OUT-OF-SCOPE###"


@dataclass
class Tau2UserMessage:
    content: Optional[str]
    tool_calls: Optional[List[str]] = None

    def is_tool_call(self) -> bool:
        return bool(self.tool_calls)


def tau2_is_stop(message: Tau2UserMessage) -> bool:
    """Verbatim logic from src/tau2/user/user_simulator.py:142-155 (commit 768f3d8f)."""
    if message.is_tool_call():
        return False
    if message.content is None:
        return False
    return (
        TAU2_STOP in message.content
        or TAU2_TRANSFER in message.content
        or TAU2_OUT_OF_SCOPE in message.content
    )


# --- Verbatim logic from SALT-NLP/collaborative-gym@58972c07 ---
def cogym_dispatch_plan(plan: str, proactive_feedback: bool = True, proactive_action: bool = True) -> str:
    """Verbatim dispatch order from collaborative_gym/nodes/simulated_user.py:263-322 (commit 58972c07)."""
    if "1" in plan:
        return "answer_question"
    elif "2" in plan and proactive_feedback:
        return "offer_feedback"
    elif "3" in plan and proactive_action:
        return "take_task_action"
    elif "4" in plan:
        return "FINISH()"
    else:
        return "wait_teammate_continue"


def simulate_proxy_benchmark(
    agent_ask_prob: float,
    q_leak: float,
    q_stop: float,
    asks_confirm: bool = True,
    n_tasks: int = 400,
    n_constraints: int = 3,
    seed: int = 2026,
) -> Dict[str, float]:
    """
    Controlled multi-turn hidden-constraint benchmark simulation modeling
    premature disclosure (q_leak) and premature stop/transfer (q_stop),
    including the tau2-bench Appendix E.3/E.4 confirmation-turn race condition.
    """
    rng = random.Random(seed)
    total_reward = 0.0
    total_turns = 0.0
    total_tool_calls = 0.0
    ufs_passes = 0
    violated_successes = 0
    success_count = 0

    for _ in range(n_tasks):
        known = [False] * n_constraints
        user_violated = False
        prematurely_stopped = False
        turns = 0
        tool_calls = 0

        # Turn 0: opening message; premature disclosure leaks hidden constraints unasked
        for c in range(n_constraints):
            if rng.random() < q_leak:
                known[c] = True
                user_violated = True

        # Interactive elicitation loop (up to n_constraints rounds)
        for _step in range(n_constraints):
            unknown_idxs = [i for i, k in enumerate(known) if not k]
            if not unknown_idxs:
                break
            if rng.random() < agent_ask_prob:
                turns += 1
                tool_calls += 1
                if rng.random() < q_stop:
                    prematurely_stopped = True
                    user_violated = True
                    break
                known[unknown_idxs[0]] = True
                for rem in unknown_idxs[1:]:
                    if rng.random() < q_leak:
                        known[rem] = True
                        user_violated = True
            else:
                break

        # Policy-compliant pre-write confirmation turn (tau2-bench Appendix E.4 retail case)
        if not prematurely_stopped and asks_confirm:
            turns += 1
            if rng.random() < q_stop:
                prematurely_stopped = True
                user_violated = True

        # Final write-tool execution attempt
        if prematurely_stopped:
            reward = 0.0
        else:
            turns += 1
            tool_calls += 1
            solved = True
            for k in known:
                if not k and rng.random() < 0.75:
                    solved = False
            reward = 1.0 if solved else 0.0

        total_reward += reward
        total_turns += turns
        total_tool_calls += tool_calls
        if not user_violated:
            ufs_passes += 1
        if reward == 1.0:
            success_count += 1
            if user_violated:
                violated_successes += 1

    return {
        "reward": total_reward / n_tasks,
        "turns": total_turns / n_tasks,
        "tool_calls": total_tool_calls / n_tasks,
        "ufs": ufs_passes / n_tasks,
        "violated_success_frac": violated_successes / max(1, success_count),
    }


def pearson_r(xs: Sequence[float], ys: Sequence[float]) -> float:
    mx = statistics.fmean(xs)
    my = statistics.fmean(ys)
    num = sum((x - mx) * (y - my) for x, y in zip(xs, ys))
    den = math.sqrt(sum((x - mx) ** 2 for x in xs) * sum((y - my) ** 2 for y in ys))
    return num / den if den > 1e-12 else 0.0


def run_probe_2() -> None:
    print("\n" + "=" * 78)
    print("PROBE 2: User-Simulator Forensics (tau-bench, tau2-bench, Co-Gym) & Distortion")
    print("Provenance: [exact reproduction of pinned repository logic] + [controlled simulation]")

    # 2A.1 tau-bench@59a200c6 parser & env patterns
    compliant_react = (
        "Thought:\nSecret constraint: budget is $50; do not reveal unless asked.\n\n"
        "User Response:\nHi, I would like to return my order."
    )
    leaked = tau_bench_react_parse_response(compliant_react)
    assert "Secret constraint: budget is $50" in leaked and "User Response:" in leaked

    stop_in_thought = (
        "Thought:\nThe goal is not yet satisfied so I must NOT say ###STOP### yet.\n\n"
        "User Response:\nPlease check order #W12345."
    )
    killed = tau_bench_react_parse_response(stop_in_thought)
    assert killed == "###STOP###" and tau_bench_env_done(killed) is True

    double_thought_error = False
    try:
        tau_bench_react_parse_response("Thought: A\nThought: B\nUser Response: Hi")
    except ValueError:
        double_thought_error = True
    assert double_thought_error

    # Illustrative reproduction of `self.total_cost = cost` overwrite pattern (user.py:52,123,171)
    turn_costs = [0.012, 0.015, 0.018, 0.009]
    buggy_cost = 0.0
    for c in turn_costs:
        buggy_cost = c
    true_cost = sum(turn_costs)
    assert abs(buggy_cost - 0.009) < 1e-12 and buggy_cost < 0.25 * true_cost

    # random.randint(0, len(tasks)) inclusive OOB (base.py:69,80; triggered only by direct
    # callers omitting task_index, since tau_bench/run.py:73,80 passes task_index=idx)
    rng_oob = random.Random(7)
    tasks_dummy = list(range(5))
    oob_hits = sum(1 for _ in range(600) if rng_oob.randint(0, len(tasks_dummy)) == len(tasks_dummy))
    assert oob_hits > 60

    # 2A.2 tau2-bench@768f3d8f substring stop/transfer premature termination
    retail_confirm_stop = Tau2UserMessage("Yes, I confirm modification #W5061109. Please proceed!###STOP###")
    telecom_transfer = Tau2UserMessage("Okay, please transfer me to a human agent ###TRANSFER###")
    tool_turn = Tau2UserMessage("Checking ###STOP###", tool_calls=["toggle_airplane_mode"])
    assert tau2_is_stop(retail_confirm_stop) is True
    assert tau2_is_stop(telecom_transfer) is True
    assert tau2_is_stop(tool_turn) is False

    # 2A.3 collaborative-gym@58972c07 digit-substring dispatch collision
    assert cogym_dispatch_plan("4. Finish the task (phase 1 is complete)") == "answer_question"
    assert cogym_dispatch_plan("Do not pick 1; choose 2. Offer feedback") == "answer_question"
    assert cogym_dispatch_plan("4. Finish the task") == "FINISH()"

    print("  [exact reproduction of pinned repository logic]:")
    print("    tau-bench@59a200c6: Thought-leak=True, STOP-in-Thought-kill=True, double-Thought-ValueError=True")
    print(f"    tau-bench@59a200c6: cost_overwrite_pattern={buggy_cost:.3f} vs sum={true_cost:.3f}; default-arg randint OOB={oob_hits}/600")
    print("    tau2-bench@768f3d8f: confirm+###STOP### terminates before agent write=True; ###TRANSFER### kills=True")
    print("    collaborative-gym@58972c07: '4. Finish (phase 1 done)' hijacked to 'answer_question'=True")

    # 2B. Controlled simulation: proxy distortion & agent leaderboard rank inversion
    hi_strong = simulate_proxy_benchmark(agent_ask_prob=0.90, q_leak=0.05, q_stop=0.02, asks_confirm=True, seed=101)
    hi_passive = simulate_proxy_benchmark(agent_ask_prob=0.15, q_leak=0.05, q_stop=0.02, asks_confirm=False, seed=101)

    leak_strong = simulate_proxy_benchmark(agent_ask_prob=0.90, q_leak=0.85, q_stop=0.02, asks_confirm=True, seed=101)
    leak_passive = simulate_proxy_benchmark(agent_ask_prob=0.15, q_leak=0.85, q_stop=0.02, asks_confirm=False, seed=101)

    toxic_strong = simulate_proxy_benchmark(agent_ask_prob=0.90, q_leak=0.90, q_stop=0.28, asks_confirm=True, seed=101)
    toxic_passive = simulate_proxy_benchmark(agent_ask_prob=0.15, q_leak=0.90, q_stop=0.28, asks_confirm=False, seed=101)

    assert hi_strong["reward"] - hi_passive["reward"] > 0.35
    assert leak_passive["reward"] - hi_passive["reward"] > 0.45
    assert hi_strong["tool_calls"] - leak_strong["tool_calls"] > 1.50
    assert leak_strong["violated_success_frac"] > 0.90
    assert toxic_passive["reward"] > toxic_strong["reward"] + 0.10

    # Regime (i): Ceteris paribus leakage-only 7-proxy sweep (fixed q_stop=0.01):
    # Isolating premature disclosure flips corr(turns, R) strongly NEGATIVE (contrasting
    # with UserProxyBench's empirical +0.594 where proxies mix both leakage and early-stop).
    leak_only_grid = [
        (0.02, 0.01), (0.06, 0.01), (0.12, 0.01), (0.18, 0.01),
        (0.26, 0.01), (0.36, 0.01), (0.48, 0.01),
    ]
    sw_leak = [simulate_proxy_benchmark(0.90, ql, qs, asks_confirm=True, seed=202) for ql, qs in leak_only_grid]
    r_turns_ufs_leak = pearson_r([s["turns"] for s in sw_leak], [s["ufs"] for s in sw_leak])
    r_turns_rew_leak = pearson_r([s["turns"] for s in sw_leak], [s["reward"] for s in sw_leak])
    assert r_turns_ufs_leak > 0.94 and r_turns_rew_leak < -0.90

    # Regime (ii): Mixed-failure 7-proxy sweep (co-varying q_leak and q_stop):
    # Premature-stop penalties partially offset leakage inflation, yielding strongly positive
    # corr(turns, UFS) alongside attenuated positive corr(turns, R) (structurally paralleling
    # UserProxyBench's empirical +0.955 vs +0.594).
    mixed_grid = [
        (0.02, 0.01), (0.06, 0.03), (0.14, 0.02), (0.08, 0.09),
        (0.24, 0.06), (0.18, 0.14), (0.35, 0.16),
    ]
    sw_mix = [simulate_proxy_benchmark(0.90, ql, qs, asks_confirm=True, seed=202) for ql, qs in mixed_grid]
    r_turns_ufs_mix = pearson_r([s["turns"] for s in sw_mix], [s["ufs"] for s in sw_mix])
    r_turns_rew_mix = pearson_r([s["turns"] for s in sw_mix], [s["reward"] for s in sw_mix])
    assert r_turns_ufs_mix > 0.94 and 0.30 < r_turns_rew_mix < 0.70
    assert r_turns_ufs_mix > r_turns_rew_mix + 0.35

    print("  [controlled simulation] Leaderboard distortion (N=400 hidden-constraint tasks):")
    print(f"    High-Fidelity Proxy : Strong R={hi_strong['reward']:.3f} (tools={hi_strong['tool_calls']:.2f}) vs Passive R={hi_passive['reward']:.3f}")
    print(f"    High-Leakage Proxy  : Strong R={leak_strong['reward']:.3f} (tools={leak_strong['tool_calls']:.2f}, Δtools={leak_strong['tool_calls']-hi_strong['tool_calls']:+.2f}) vs Passive R={leak_passive['reward']:.3f}")
    print(f"    Leak+PrematureStop  : Strong R={toxic_strong['reward']:.3f} < Passive R={toxic_passive['reward']:.3f}  [RANK INVERTED]")
    print(f"    7-Proxy Sweep (leak-only, fixed q_stop): corr(turns, UFS)={r_turns_ufs_leak:+.4f} vs corr(turns, R)={r_turns_rew_leak:+.4f}")
    print(f"    7-Proxy Sweep (mixed leak + early-stop): corr(turns, UFS)={r_turns_ufs_mix:+.4f} vs corr(turns, R)={r_turns_rew_mix:+.4f}")
    print("  [PASS] Probe 2 assertions satisfied.")


# =============================================================================
# PROBE 3: CollabLLM Unified Belief-MDP (w=0..3) & Norm-Matched OPEN BOED
# =============================================================================

def solve_collab_pomdp(lookahead_w: int, ask_info_gain: int = 1) -> Dict[str, float | str | bool]:
    """
    Unified finite-horizon belief-MDP for collaborative intent clarification (H = 4).
    Latent user intent g in {0,1}^3 (8 uniform intents); belief state k in {0,1,2,3}
    denotes resolved conjunctive attributes.

    Single coherent per-turn reward across ALL lookahead depths (zero depth==0 jump):
      - ASK (valid when k < 3 and turns_left > 1):
          strictly negative immediate reward = -(c_tok * tok_ask + ask_friction) = -0.135;
          transitions to (min(3, k + ask_info_gain), turns_left - 1).
          (No free per-turn interactivity bonus: ASK can win ONLY via Value of Information.)
      - DRAFT:
          immediate token cost = -c_tok * tok_draft = -0.120; exact match prob = 2^(-(3-k)).
          Terminal states (turns_left == 1 or k == 3) ALWAYS take precedence over depth == 0
          and terminate with exact expected accuracy S_term(k) = 2^(-(3-k)).
          At depth == 0 on a non-terminal state, truncated rollout scores the current turn as
          terminal (DRAFT -> S_term(k) - c_tok * tok_draft; ASK -> -(c_tok*tok_ask+ask_friction)).
          On miss when non-terminal & depth > 0: user drops w.p. p_drop = 0.35 (task score 0.0),
          else revises revealing 1 bit (k -> min(3, k+1), turns_left - 1).

    Interactivity metric (ITR) is defined consistently everywhere as exact expected
    per-episode clarifying-turn share E[ask_turns / total_turns] (never added to reward).
    """
    H = 4
    c_tok = 0.25
    tok_ask = 0.10
    tok_draft = 0.48
    ask_friction = 0.11
    p_drop = 0.35

    def s_term(k: int) -> float:
        return 1.0 / (2 ** (3 - k))

    memo: Dict[Tuple[int, int, int], Tuple[float, str]] = {}

    def q_val(k: int, turns_left: int, depth: int, action: str) -> float:
        if action == "ASK":
            step_r = -(c_tok * tok_ask + ask_friction)
            if turns_left == 1 or depth == 0:
                return step_r
            nxt_v, _ = best_action(min(3, k + ask_info_gain), turns_left - 1, depth - 1)
            return step_r + nxt_v
        else:  # DRAFT
            step_r = -c_tok * tok_draft
            # True terminal states ALWAYS precede depth == 0 truncation
            if turns_left == 1 or k == 3:
                return step_r + s_term(k)
            if depth == 0:
                return step_r + s_term(k)
            p_hit = 1.0 / (2 ** (3 - k))
            nxt_v, _ = best_action(min(3, k + 1), turns_left - 1, depth - 1)
            return step_r + p_hit * 1.0 + (1.0 - p_hit) * (1.0 - p_drop) * nxt_v

    def best_action(k: int, turns_left: int, depth: int) -> Tuple[float, str]:
        key = (k, turns_left, depth)
        if key in memo:
            return memo[key]
        candidates = ["DRAFT"]
        if k < 3 and turns_left > 1:
            candidates.append("ASK")
        scored = [(q_val(k, turns_left, depth, a), a) for a in candidates]
        best = max(scored, key=lambda x: x[0])
        memo[key] = best
        return best

    def eval_policy(
        k: int, turns_left: int, asks_so_far: int, turns_so_far: int
    ) -> Tuple[float, float, float, float]:
        """Return exact (E[acc], E[tokens], E[ask_turns], E[ask_turns / total_turns])."""
        _, act = best_action(k, turns_left, lookahead_w)
        if act == "ASK":
            acc, tok, asks, itr = eval_policy(
                min(3, k + ask_info_gain), turns_left - 1, asks_so_far + 1, turns_so_far + 1
            )
            return acc, tok_ask + tok, 1.0 + asks, itr
        else:
            term_turns = turns_so_far + 1
            term_itr = asks_so_far / term_turns
            if turns_left == 1 or k == 3:
                return s_term(k), tok_draft, 0.0, term_itr
            p_hit = 1.0 / (2 ** (3 - k))
            acc_rev, tok_rev, asks_rev, itr_rev = eval_policy(
                min(3, k + 1), turns_left - 1, asks_so_far, term_turns
            )
            p_cont = (1.0 - p_hit) * (1.0 - p_drop)
            p_end = p_hit + (1.0 - p_hit) * p_drop
            acc = p_hit * 1.0 + p_cont * acc_rev
            tok = tok_draft + p_cont * tok_rev
            asks = p_cont * asks_rev
            itr = p_end * term_itr + p_cont * itr_rev
            return acc, tok, asks, itr

    _, first_act = best_action(0, H, lookahead_w)
    acc, tok, asks, itr = eval_policy(0, H, 0, 0)
    ask_never_beats_draft = all(
        q_val(k, t, lookahead_w, "ASK") < q_val(k, t, lookahead_w, "DRAFT")
        for k in range(3)
        for t in range(2, H + 1)
    )
    return {
        "first_action": first_act,
        "accuracy": acc,
        "tokens": tok,
        "ask_turns": asks,
        "itr": itr,
        "ask_never_beats_draft": ask_never_beats_draft,
    }


def sigmoid(z: float) -> float:
    if z >= 0.0:
        ez = math.exp(-z)
        return 1.0 / (1.0 + ez)
    ez = math.exp(z)
    return ez / (1.0 + ez)


def binary_entropy(p: float) -> float:
    if p <= 1e-12 or p >= 1.0 - 1e-12:
        return 0.0
    return -(p * math.log2(p) + (1.0 - p) * math.log2(1.0 - p))


def unit_norm(v: Sequence[float]) -> List[float]:
    n = math.sqrt(sum(x * x for x in v))
    return [x / n for x in v]


def run_open_boed_comparison() -> Dict[str, Tuple[float, float, float, float, float]]:
    """
    Norm-matched equal-SNR simulation of OPEN (Handa et al. 2024, arXiv:2403.05534, Eq. 5)
    anisotropic scaled Gaussian prior w_i = 1.2 - 0.12*i (i = 1..8) with Bradley-Terry
    pairwise preference likelihood.

    Fairness & numerical integrity guarantees:
      - Every candidate query across EVERY strategy satisfies ||d||_2 == 1.0 (equal SNR).
      - N = 1200 particles with tempered scale sigma = 1.6 avoids particle collapse;
        mean_ESS and min_ESS are computed and verified explicitly across all users.
      - Identical user-response uniform draws per (user, turn) across strategies.
    """
    rng = random.Random(2403)
    dim = 8
    sigma = 1.6
    scales = [sigma * (1.2 - 0.12 * i) for i in range(1, dim + 1)]  # OPEN Eq. 5
    n_particles = 1200
    n_users = 40
    n_turns = 7

    # Shared strict unit-norm query pool (||d||_2 == 1.0 for every vector)
    axis_diffs = [[1.0 if k == idx else 0.0 for k in range(dim)] for idx in range(dim)]
    rand_diffs = [unit_norm([rng.gauss(0.0, 1.0) for _ in range(dim)]) for _ in range(25)]
    cand_diffs = axis_diffs + rand_diffs
    n_cands = len(cand_diffs)
    for d in cand_diffs:
        assert abs(math.sqrt(sum(x * x for x in d)) - 1.0) < 1e-12

    eval_diffs = [unit_norm([rng.gauss(0.0, 1.0) for _ in range(dim)]) for _ in range(60)]
    particles = [[rng.gauss(0.0, scales[k]) for k in range(dim)] for _ in range(n_particles)]
    particles_t = [[particles[m][k] for m in range(n_particles)] for k in range(dim)]
    true_users = [[rng.gauss(0.0, scales[k]) for k in range(dim)] for _ in range(n_users)]

    cand_pm = [
        [sigmoid(sum(map(_MUL, particles[m], cand_diffs[c]))) for m in range(n_particles)]
        for c in range(n_cands)
    ]
    cand_hm = [[binary_entropy(p) for p in row] for row in cand_pm]
    cand_lp1 = [[math.log(max(p, 1e-12)) for p in row] for row in cand_pm]
    cand_lp0 = [[math.log(max(1.0 - p, 1e-12)) for p in row] for row in cand_pm]

    def eval_strategy(mode: str) -> Tuple[float, float, float, float, float]:
        tida_scores: List[float] = []
        final_accs: List[float] = []
        final_entropies: List[float] = []
        final_ess: List[float] = []
        choice_rng = random.Random(777)

        for u_idx, theta_true in enumerate(true_users):
            resp_rng = random.Random(9000 + u_idx)
            logw = [0.0] * n_particles
            weights = [1.0 / n_particles] * n_particles
            true_labels = [1 if sum(map(_MUL, theta_true, d)) >= 0.0 else 0 for d in eval_diffs]

            def acc_now() -> float:
                theta_hat = [sum(map(_MUL, weights, particles_t[k])) for k in range(dim)]
                correct = sum(
                    1
                    for d, y in zip(eval_diffs, true_labels)
                    if (1 if sum(map(_MUL, theta_hat, d)) >= 0.0 else 0) == y
                )
                return correct / len(eval_diffs)

            base_acc = 0.5
            delta_acc_sum = 0.0

            for t in range(n_turns):
                if mode == "passive":
                    continue
                elif mode == "random":
                    c_idx = choice_rng.randrange(n_cands)
                elif mode == "axis_rev":
                    c_idx = (dim - 1) - (t % dim)  # unprioritized unit-axis cycling
                elif mode == "axis_prior":
                    c_idx = t % dim  # prior-variance-ordered unit-axis cycling
                elif mode == "open_boed":
                    best_eig = -1.0
                    best_c = 0
                    for c in range(n_cands):
                        p_y1 = sum(map(_MUL, weights, cand_pm[c]))
                        cond_h = sum(map(_MUL, weights, cand_hm[c]))
                        eig = binary_entropy(p_y1) - cond_h
                        if eig > best_eig:
                            best_eig = eig
                            best_c = c
                    c_idx = best_c
                else:
                    raise ValueError(mode)

                d = cand_diffs[c_idx]
                p_true = sigmoid(sum(map(_MUL, theta_true, d)))
                y = 1 if resp_rng.random() < p_true else 0

                lp = cand_lp1[c_idx] if y == 1 else cand_lp0[c_idx]
                logw = [lw + li for lw, li in zip(logw, lp)]
                max_lw = max(logw)
                unnorm = [math.exp(lw - max_lw) for lw in logw]
                inv_z = 1.0 / sum(unnorm)
                weights = [w * inv_z for w in unnorm]

                delta_acc_sum += acc_now() - base_acc

            ess = 1.0 / sum(w * w for w in weights)
            post_h = -sum(w * math.log2(w) for w in weights if w > 1e-12)
            tida_scores.append(delta_acc_sum / n_turns)
            final_accs.append(base_acc if mode == "passive" else acc_now())
            final_entropies.append(post_h)
            final_ess.append(ess)

        return (
            statistics.fmean(tida_scores),
            statistics.fmean(final_accs),
            statistics.fmean(final_entropies),
            statistics.fmean(final_ess),
            min(final_ess),
        )

    return {
        "passive": eval_strategy("passive"),
        "axis_rev": eval_strategy("axis_rev"),
        "random": eval_strategy("random"),
        "axis_prior": eval_strategy("axis_prior"),
        "open_boed": eval_strategy("open_boed"),
    }


def run_probe_3() -> None:
    print("\n" + "=" * 78)
    print("PROBE 3: CollabLLM Unified Belief-MDP (w=0..3) & Norm-Matched OPEN BOED")
    print("Provenance: [derived analytical model] + [controlled simulation]")

    # 3A. Unified Bellman belief-MDP with informative ASK (gain=1)
    res_w = {w: solve_collab_pomdp(w, ask_info_gain=1) for w in (0, 1, 2, 3)}
    assert res_w[0]["first_action"] == "DRAFT"
    assert res_w[0]["ask_turns"] == 0.0 and res_w[0]["itr"] == 0.0
    # Strict monotonic accuracy gain, token reduction, and ITR rise from superadditive VoI
    for w in (0, 1, 2):
        assert float(res_w[w + 1]["accuracy"]) > float(res_w[w]["accuracy"])
        assert float(res_w[w + 1]["tokens"]) < float(res_w[w]["tokens"])
        assert float(res_w[w + 1]["itr"]) > float(res_w[w]["itr"])
    assert res_w[3]["first_action"] == "ASK"
    assert abs(float(res_w[3]["accuracy"]) - 1.0) < 1e-12

    # 3A Anti-vacuity control: zero-information-gain ASK MUST NEVER beat DRAFT
    zero_w = {w: solve_collab_pomdp(w, ask_info_gain=0) for w in (0, 1, 2, 3)}
    for w in (0, 1, 2, 3):
        assert zero_w[w]["ask_never_beats_draft"] is True
        assert zero_w[w]["first_action"] == "DRAFT"
        assert zero_w[w]["ask_turns"] == 0.0
        assert abs(float(zero_w[w]["accuracy"]) - float(res_w[0]["accuracy"])) < 1e-12

    print("  [derived analytical model] CollabLLM unified 3-bit belief-MDP (H=4, single reward):")
    for w in (0, 1, 2, 3):
        r = res_w[w]
        print(
            f"    w={w}: first={str(r['first_action']):5s} | acc={float(r['accuracy']):.4f} | "
            f"tokens={float(r['tokens']):.4f} | E[asks]={float(r['ask_turns']):.3f} | E[asks/turns]={float(r['itr']):.3f}"
        )
    print("    Zero-info-ASK control (gain=0): ASK < DRAFT strictly at all (k,t) for w=0..3 -> PASS")

    # 3B. Norm-matched (||d||=1) OPEN Eq. 5 Bradley-Terry BOED with explicit ESS check
    boed = run_open_boed_comparison()
    assert boed["open_boed"][0] > boed["random"][0] + 0.04
    assert boed["open_boed"][0] > boed["axis_rev"][0] + 0.08
    assert boed["open_boed"][0] > boed["axis_prior"][0]
    assert boed["open_boed"][2] < boed["axis_prior"][2] < boed["random"][2] < boed["passive"][2]
    # Explicit anti-collapse ESS verification across all active strategies
    for mode in ("axis_rev", "random", "axis_prior", "open_boed"):
        assert boed[mode][3] > 250.0  # mean ESS > 250 / 1200 (>20% active particles)
        assert boed[mode][4] > 120.0  # min ESS > 120 / 1200 across all 40 users

    print("  [controlled simulation] Norm-matched (||d||=1) OPEN Eq. 5 BOED (d=8, T=7, N=1200, 40 users):")
    for k in ("passive", "axis_rev", "random", "axis_prior", "open_boed"):
        tida, acc, ent, ess_mean, ess_min = boed[k]
        print(
            f"    {k:10s}: TIDA={tida:+.4f} | final_acc={acc:.4f} | "
            f"H={ent:.3f} bits | ESS={ess_mean:.1f}/1200 (min={ess_min:.1f})"
        )
    print("  [PASS] Probe 3 assertions satisfied.")


# =============================================================================
# PROBE 4: Bastani (PNAS 2025) / Kestin (Sci Rep 2025) Derived Arithmetic
#          + Verbatim MathDial (eth-nlped/mathdial@60035095) Evaluator Forensics
# =============================================================================

# --- Verbatim logic from eth-nlped/mathdial@60035095:interactivetutoring/evaluate.py ---
def mathdial_findall(regexp: str, text: str) -> List[str]:
    """Verbatim logic from interactivetutoring/evaluate.py:17-26 (commit 60035095)."""
    matches: List[str] = []
    while True:
        res = re.search(regexp, text)
        if res:
            matches.append(text[res.start():res.end()])
            text = text[res.end():]
        else:
            break
    return matches


def mathdial_is_float(num: str) -> bool:
    try:
        float(num)
        return True
    except ValueError:
        return False


def mathdial_get_match(text: str, gt_answer: str) -> Optional[bool]:
    """
    Verbatim logic from interactivetutoring/evaluate.py:37-48 (commit 60035095).
    Note: upstream omits `return False` in the float branch, returning None on non-match.
    """
    all_numbers = mathdial_findall(r"[0-9]+(\.[0-9]+)?", text.replace(",", ""))
    answer = gt_answer.replace(",", "")
    if mathdial_is_float(answer):
        float_answer = float(answer)
        for number in all_numbers:
            if mathdial_is_float(number):
                float_number = float(number)
                if abs(float_answer - float_number) < 1e-7:
                    return True
        return None
    else:
        return answer in all_numbers


def mathdial_all_match(role: str, conversation: List[str], answer: str) -> float:
    """Verbatim logic from interactivetutoring/evaluate.py:51-59 (commit 60035095)."""
    count = 0.0
    for utterance in conversation:
        utterance = utterance.strip().strip("\n")
        if utterance.startswith(role):
            if mathdial_get_match(utterance, answer):
                return count
            count += 1.0
    return float("inf")


def mathdial_evaluate_at_k(utterances_list: List[str], answer: str, k: int) -> Tuple[bool, bool]:
    """Verbatim logic from interactivetutoring/evaluate.py:62-67 (commit 60035095)."""
    student = mathdial_all_match("Student:", utterances_list, answer)
    teacher = mathdial_all_match("Teacher:", utterances_list, answer)
    is_success_at_k = student <= k
    is_telling_at_k = teacher <= min(student, k)
    return is_success_at_k, is_telling_at_k


def welch_t(m1: float, sd1: float, n1: int, m2: float, sd2: float, n2: int) -> float:
    return (m1 - m2) / math.sqrt((sd1 ** 2) / n1 + (sd2 ** 2) / n2)


def run_probe_4() -> None:
    print("\n" + "=" * 78)
    print("PROBE 4: Bastani (PNAS 2025) / Kestin (2025) Arithmetic & MathDial Forensics")
    print("Provenance: [derived arithmetic on published/reproduced sufficient statistics] + [exact reproduction of pinned repository logic]")

    # 4A. Derived arithmetic on Bastani et al. (PNAS 2025) Table 1 clustered OLS estimates
    #     (reproduced offline from obastani/GenAICanHarmLearning@2f63dae1 final_data.csv;
    #     this probe executes derived ratio/CI/Welch checks rather than raw CSV OLS).
    #     Sample distinction:
    #       - All Honors == 0 rows: N = 2,899 (1,076 / 838 / 985; control means 0.2838 / 0.3214,
    #         matching Table 1 reported control means 0.284 / 0.321).
    #       - Complete Table 1 OLS sample (dropping 50 missing gpa_prev + 1 missing Grader):
    #         N = 2,848 (1,062 / 824 / 962; G = 44 classrooms, p = 35 regressors;
    #         complete-case control means 0.2847 / 0.3238).
    ctrl_p2_mean, ctrl_p2_sd, ctrl_n = 0.2838, 0.2873, 1076
    ctrl_p3_mean, ctrl_p3_sd = 0.3214, 0.2768
    base_p2_mean, base_p2_sd, base_n = 0.4737, 0.2575, 838
    base_p3_mean, base_p3_sd = 0.2869, 0.2330
    tutor_p2_mean, tutor_p2_sd, tutor_n = 0.6690, 0.3093, 985
    tutor_p3_mean, tutor_p3_sd = 0.3152, 0.2808

    b_base_p2, se_base_p2 = +0.1370, 0.0310
    b_tutor_p2, se_tutor_p2 = +0.3613, 0.0317
    b_base_p3, se_base_p3 = -0.0543, 0.0224
    b_tutor_p3, se_tutor_p3 = -0.0043, 0.0134

    rel_base_p2 = b_base_p2 / ctrl_p2_mean
    rel_tutor_p2 = b_tutor_p2 / ctrl_p2_mean
    rel_base_p3 = b_base_p3 / ctrl_p3_mean
    rel_tutor_p3 = b_tutor_p3 / ctrl_p3_mean

    # Both cluster-df t_{G-1=43, 0.975} = 2.0167 and asymptotic z = 1.96 95% CIs
    t_crit_43 = 2.0167
    z_crit = 1.96
    ci_base_p3_t43 = (b_base_p3 - t_crit_43 * se_base_p3, b_base_p3 + t_crit_43 * se_base_p3)
    ci_tutor_p3_t43 = (b_tutor_p3 - t_crit_43 * se_tutor_p3, b_tutor_p3 + t_crit_43 * se_tutor_p3)
    ci_base_p3_z = (b_base_p3 - z_crit * se_base_p3, b_base_p3 + z_crit * se_base_p3)
    ci_tutor_p3_z = (b_tutor_p3 - z_crit * se_tutor_p3, b_tutor_p3 + z_crit * se_tutor_p3)

    assert abs(rel_base_p2 - 0.4827) < 0.005
    assert abs(rel_tutor_p2 - 1.2731) < 0.005
    assert abs(rel_base_p3 - (-0.1689)) < 0.005
    assert abs(rel_tutor_p3 - (-0.0134)) < 0.005
    assert ci_base_p3_t43[1] < 0.0 and ci_base_p3_z[1] < 0.0
    assert ci_tutor_p3_t43[0] < 0.0 < ci_tutor_p3_t43[1]

    t_raw_base_p3 = welch_t(base_p3_mean, base_p3_sd, base_n, ctrl_p3_mean, ctrl_p3_sd, ctrl_n)
    t_raw_tutor_p3 = welch_t(tutor_p3_mean, tutor_p3_sd, tutor_n, ctrl_p3_mean, ctrl_p3_sd, ctrl_n)
    assert t_raw_base_p3 < -2.8
    assert abs(t_raw_tutor_p3) < 0.6

    n_q, n_corr, n_log, n_arith = 570, 290, 237, 43
    assert n_corr + n_log + n_arith == n_q
    assert abs(n_corr / n_q - 0.5088) < 1e-3

    kestin_pre, kestin_class_post, kestin_ai_post = 2.75, 3.50, 4.50
    gain_ratio = (kestin_ai_post - kestin_pre) / (kestin_class_post - kestin_pre)
    time_ratio = 49.0 / 60.0
    assert gain_ratio > 2.3 and time_ratio < 0.85

    print("  [derived arithmetic on published/reproduced sufficient statistics]:")
    print(
        f"    Bastani Table 1 (N=2848, G=44; raw N=2899): GPT Base  practice={rel_base_p2:+.1%} ({b_base_p2:+.4f}), "
        f"exam={rel_base_p3:+.1%} ({b_base_p3:+.4f}, t43 CI [{ci_base_p3_t43[0]:+.4f}, {ci_base_p3_t43[1]:+.4f}], "
        f"z CI [{ci_base_p3_z[0]:+.4f}, {ci_base_p3_z[1]:+.4f}])"
    )
    print(
        f"    Bastani Table 1 (N=2848, G=44; raw N=2899): GPT Tutor practice={rel_tutor_p2:+.1%} ({b_tutor_p2:+.4f}), "
        f"exam={rel_tutor_p3:+.1%} ({b_tutor_p3:+.4f}, t43 CI [{ci_tutor_p3_t43[0]:+.4f}, {ci_tutor_p3_t43[1]:+.4f}])"
    )
    print(f"    Bastani raw Honors==0 Welch t (Part3, N=2899): Base={t_raw_base_p3:+.2f}, Tutor={t_raw_tutor_p3:+.2f}")
    print(f"    Bastani gpt_answers_full (570 queries): correct={n_corr/n_q:.1%}, logical={n_log/n_q:.1%}, arith={n_arith/n_q:.1%}")
    print(f"    Kestin 2025 median gain ratio: {(kestin_ai_post-kestin_pre):.2f}/{(kestin_class_post-kestin_pre):.2f} = {gain_ratio:.2f}x in {time_ratio:.1%} median time (49 vs 60 min)")

    # 4B. Verbatim MathDial@60035095 evaluator forensics
    # Defect 1: unsigned regex strips minus sign; float non-match returns None verbatim
    assert mathdial_get_match("Student: I got -5", "5") is True
    assert mathdial_get_match("Student: The answer is -5", "-5") is None
    # Defect 2: incidental intermediate number matches gt_answer even when final answer is wrong
    assert mathdial_get_match("Student: Starting with 12, then 12 + 3 = 15 so final answer is 15", "12") is True

    # Intended Round-0 walkthrough convention (gpt_baseline.py:57-65, tests/test_metrics.py:18-72):
    # Teacher[0]/Student[0] is the mandatory pre-tutoring walkthrough (count=0); tutoring rounds
    # start at count=1. Post-student praise Teacher[3] yields (True, False).
    round0_conv = [
        "Teacher: Hi Kayla! Could you walk me through your solution?",  # Teacher[0] (Round 0)
        "Student: I added 6 + 7 and got 13.",                          # Student[0] (Round 0)
        "Teacher: Let's try multiplying 6 by 5 first.",                # Teacher[1] (Round 1)
        "Student: That is 30.",                                        # Student[1] (Round 1)
        "Teacher: Now add two more 6s.",                               # Teacher[2] (Round 2)
        "Student: 30 + 12 = 42.",                                      # Student[2] (Round 2)
        "Teacher: Correct, the answer is 42!",                         # Teacher[3] (post-student praise)
    ]
    assert mathdial_evaluate_at_k(round0_conv, "42", k=1) == (False, False)
    assert mathdial_evaluate_at_k(round0_conv, "42", k=2) == (True, False)

    # Real Round-0 edge cases:
    # (a) Incidental match in Student[0]'s initial WRONG walkthrough scores Success@k=True before tutoring
    walkthrough_fp_conv = [
        "Teacher: Hi Kayla! Could you walk me through your solution?",
        "Student: I started with 12 apples and added 3 to get 15.",  # gt=12 mentioned incidentally!
        "Teacher: Let's re-read the problem carefully.",
        "Student: Oh, maybe 18?",
    ]
    wt_s1, wt_t1 = mathdial_evaluate_at_k(walkthrough_fp_conv, "12", k=1)
    assert wt_s1 is True and wt_t1 is False

    # (b) Caller mismatch: reusing evaluate_at_k on dialogues WITHOUT a Round-0 turn shifts k by 1
    no_round0_conv = [
        "Teacher: What is 6 * 7?",
        "Student: I think 36?",
        "Teacher: Close, add one more 6.",
        "Student: Oh, 42!",
    ]
    shift_s1, shift_t1 = mathdial_evaluate_at_k(no_round0_conv, "42", k=1)
    assert shift_s1 is True and shift_t1 is False

    # Defect 3: Unpenalized Success@k / Telling@k coupling (answer-leakage gaming)
    leaker_conv = [
        "Teacher: Hi Kayla! Could you walk me through your solution?",
        "Student: I think 6 * 7 is 36.",
        "Teacher: The final answer is 42 because 6 * 7 = 42.",
        "Student: Thanks, so the answer is 42!",
    ]
    socratic_conv = round0_conv
    leak_s, leak_t = mathdial_evaluate_at_k(leaker_conv, "42", k=3)
    soc_s, soc_t = mathdial_evaluate_at_k(socratic_conv, "42", k=3)
    assert leak_s is True and leak_t is True
    assert soc_s is True and soc_t is False
    assert (leak_s and not leak_t) is False
    assert (soc_s and not soc_t) is True

    print("  [exact reproduction of pinned repository logic] MathDial@60035095 evaluate.py:")
    print("    Unsigned regex: match('-5','5')=True, match('-5','-5')=None (falsy); intermediate-number FP=True")
    print("    Round-0 convention: k=1 -> (False,False), k=2 + post-praise -> (True,False); Student[0] FP=True; no-Round-0 shift=True")
    print(f"    Gaming: Leaker (Success@3={leak_s}, Telling@3={leak_t}, Joint={leak_s and not leak_t}) vs Socratic (Success@3={soc_s}, Telling@3={soc_t}, Joint={soc_s and not soc_t})")
    print("  [PASS] Probe 4 assertions satisfied.")


# =============================================================================
# PROBE 5: Stylized Cognitive-Offloading vs. Desirable-Difficulty Illustration
# =============================================================================

@dataclass(frozen=True)
class TutorRegime:
    name: str
    p_tell: float       # probability of revealing direct answer
    p_verify: float     # availability of low-effort answer verification shortcut
    step_gated: bool    # programmatic step-gating indicator
    tutor_acc: float    # factual solution accuracy
    hint_quality: float # pedagogical scaffolding quality [0, 1]


def simulate_learning_regime(
    regime: TutorRegime,
    n_students: int = 400,
    n_sessions: int = 4,
    seed: int = 2025,
) -> Dict[str, float]:
    """
    Stylized mechanistic illustration of cognitive-offloading vs. desirable-difficulty
    retention dynamics (not an empirical parameter fit). Note: step_gated=True encodes
    explicit structural gating assumptions (eliminating verification offloading and crutch
    atrophy while preserving active retrieval effort) to demonstrate mechanism sufficiency.
    """
    rng = random.Random(seed)
    prac_scores: List[float] = []
    exam_scores: List[float] = []
    comfort_scores: List[float] = []

    for _ in range(n_students):
        skill = max(0.05, min(0.65, rng.gauss(0.24, 0.12)))
        base_motivation = max(0.25, min(0.95, rng.gauss(0.65, 0.15)))
        sess_prac: List[float] = []
        sess_comfort: List[float] = []

        for _sess in range(n_sessions):
            offload_pull = 0.78 * regime.p_tell + 0.36 * regime.p_verify * (0.0 if regime.step_gated else 1.0)
            effort = max(0.08, min(1.0, base_motivation * (1.0 - offload_pull) + (0.18 if regime.step_gated else 0.0)))

            indep_solve = min(1.0, skill + 0.08 * effort + 0.28 * regime.hint_quality * effort)
            if regime.p_tell > 0.0 and rng.random() < regime.p_tell:
                prac = regime.tutor_acc
                crutch_used = 1.0
            else:
                prac = min(1.0, indep_solve + 0.36 * regime.p_verify * regime.tutor_acc)
                crutch_used = 0.14 * regime.p_verify * (0.0 if regime.step_gated else 1.0)

            scaffold_mult = 1.0 + (0.95 * regime.hint_quality if regime.step_gated else 0.30 * regime.hint_quality)
            retrieval_gain = 0.032 * effort * scaffold_mult * (1.0 - 0.55 * skill)
            crutch_atrophy = 0.024 * crutch_used
            misconception_drag = 0.012 * regime.p_tell * (1.0 - regime.tutor_acc)
            skill = max(0.02, min(0.98, skill + retrieval_gain - crutch_atrophy - misconception_drag))

            comfort = 0.70 * prac - 0.45 * effort + 0.20 * regime.hint_quality
            sess_prac.append(prac)
            sess_comfort.append(comfort)

        prac_scores.append(statistics.fmean(sess_prac))
        exam_scores.append(skill)
        comfort_scores.append(statistics.fmean(sess_comfort))

    return {
        "practice": statistics.fmean(prac_scores),
        "exam": statistics.fmean(exam_scores),
        "comfort": statistics.fmean(comfort_scores),
    }


def run_probe_5() -> None:
    print("\n" + "=" * 78)
    print("PROBE 5: Cognitive-Offloading vs. Desirable-Difficulty Retention Dynamics")
    print("Provenance: [controlled simulation] (stylized mechanistic illustration)")

    regimes = [
        TutorRegime("No-AI Control",          p_tell=0.00, p_verify=0.00, step_gated=False, tutor_acc=0.00, hint_quality=0.00),
        TutorRegime("Unconstrained Chat",     p_tell=0.65, p_verify=0.20, step_gated=False, tutor_acc=0.51, hint_quality=0.15),
        TutorRegime("Prompt-Only Tutor",      p_tell=0.05, p_verify=0.80, step_gated=False, tutor_acc=0.98, hint_quality=0.65),
        TutorRegime("Step-Gated Socratic",    p_tell=0.02, p_verify=0.25, step_gated=True,  tutor_acc=0.98, hint_quality=0.90),
    ]
    out = {r.name: simulate_learning_regime(r) for r in regimes}

    ctrl = out["No-AI Control"]
    chat = out["Unconstrained Chat"]
    ptut = out["Prompt-Only Tutor"]
    sgat = out["Step-Gated Socratic"]

    assert chat["practice"] > ctrl["practice"] + 0.04
    assert chat["exam"] < ctrl["exam"] - 0.03
    assert ptut["practice"] > chat["practice"] + 0.20
    assert ptut["exam"] > chat["exam"] + 0.03
    assert abs(ptut["exam"] - ctrl["exam"]) < 0.03
    assert sgat["exam"] > ctrl["exam"] + 0.08
    assert sgat["exam"] > ptut["exam"] + 0.08
    assert ptut["comfort"] > sgat["comfort"]
    assert chat["comfort"] > ctrl["comfort"]

    for r in regimes:
        m = out[r.name]
        print(f"  {r.name:20s}: practice={m['practice']:.4f} | unassisted_exam={m['exam']:.4f} | learner_comfort={m['comfort']:+.4f}")
    print("  Stylized illustration verified: polarity inversion (Unconstrained Chat), harm")
    print("  neutralization (Prompt-Only), positive transfer (Step-Gated), comfort/transfer split.")
    print("  [PASS] Probe 5 assertions satisfied.")


def main() -> None:
    run_probe_1()
    run_probe_2()
    run_probe_3()
    run_probe_4()
    run_probe_5()
    print("\n" + "=" * 78)
    print("ALL 5 VERIFICATION PROBES PASSED.")


if __name__ == "__main__":
    main()
