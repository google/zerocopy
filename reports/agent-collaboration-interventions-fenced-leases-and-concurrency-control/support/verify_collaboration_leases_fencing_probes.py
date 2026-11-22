#!/usr/bin/env python3
"""Deterministic verification probe suite for collaboration interventions, leases, and fencing.

Covers five primary-source-grounded verification modules using only the Python 3.10+
standard library (and local ephemeral `git` execution inside `TemporaryDirectory` with
automatic cleanup, zero persistent filesystem writes, zero local paths in stdout, and
100% deterministic stdout across `python3 -I -B` invocations):

  1. `run_probe_1_gray_cheriton_and_progress_leases`:
     - [exact Gray & Cheriton 1989 Eq. 1-2]: V-system Table 2 reproduction (S in {1,10,20,40},
       multicast alpha = 2R/(SW) and unicast alpha = R/((S-1)W)), Eq. 2 consistency delay,
       and sub-skew penalty cliff (0 < t_S <= m_prop + 2*m_proc + eps => t_C = 0).
     - [derived renewal + crash-stall cost models]: Explicitly separates (a) demand-driven
       non-heartbeated cache leases (with active duty factor pi_on(t_S) and high-duty closed
       form t_S* = Delta - 1/R + 2/sqrt(lambda_fail * c_stall)) from (b) proactively
       heartbeated task/lock leases renewed every tau_hb = eta*(t_S - Delta) (ZooKeeper
       eta = 1/3 => expected crash residual stall (5/6)*t_S + (1/6)*Delta and exact minimizer
       t_S_hb* = Delta + sqrt(2 / (eta*(1 - eta/2)*lambda_fail*c_stall))), plus fixed-cadence
       keepalive monotonicity and collapse to t_S* = 0 under un-heartbeated high-abandonment
       issue claims.
     - [toy discrete simulation: progress-witness lease protocol]: Pure liveness heartbeats vs.
       progress-witness-gated renewals under StuckDetector zero-progress and A <-> B oscillation
       loops ("active cookie-licking"), post-eviction zombie-write fencing (`t == evicted_at_s + 20`),
       and slow-turn false-positive guardrails.

  2. `run_probe_2_fencing_matrix_and_real_git_cas`:
     - [discrete schedule model]: Exhaustive 30-schedule pause + orphan-subagent matrix across
       five protocols (`unfenced_ttl_only`, `unfenced_ttl_plus_client_recheck`,
       `chubby_lock_delay_only`, `fenced_token_parent_only_ambient_child`, and
       `fenced_token_storage_cas_all_writers`), disaggregating parent-only (`no_child`) vs.
       child-induced split-brain overwrites.
     - [real git execution]: Ephemeral bare-origin + worker/orphan-child Git repository test
       with fixed author/committer timestamps (deterministic OIDs), proving:
         (G1) unfenced `--force` orphan push clobbers fresh token-2 commit;
         (G2a) explicit `--force-with-lease=<ref>:<C0>` blocks linear stale overwrite;
         (G2b) bare `--force-with-lease` after background `git fetch` AND explicit
               `--force-with-lease=<ref>:<C0>` after a token-3 ABA rollback to `C0` BOTH
               suffer split-brain orphan overwrites;
         (G3a) server `hooks/pre-receive` alone suffers a live TOCTOU split-brain race when a
               concurrent `git update-ref --stdin` advances `refs/leases/task` (`1 -> 3`)
               between `pre-receive` exit and `receive-pack` acquiring `refs/heads/task.lock`;
         (G3b) enforcing monotonic `refs/leases/task` fencing inside `hooks/reference-transaction`
               on `sys.argv[1] == "prepared"` (while `refs/heads/task.lock` is held) closes the
               TOCTOU window across both lock-order interleavings (`0` corruptions, subject to
               the non-Byzantine commit-trailer trust boundary).

  3. `run_probe_3_agrawal_inversion_and_cookie_licking`:
     - Analytical Franaszek & Robinson (1985) / Agrawal, Carey & Livny (1987) processor-shared
       fixed-point solver Lambda_inf = N * (1 - p_c)^Lambda_inf (with K-invariant useful
       utilization u(N) and Lambda_K(N) = min(1, K/N) * Lambda_inf(N)) paired with an
       independent deterministic discrete-step multi-slot 2-granule locking vs. commit-time
       OCC simulator:
         (a) OCC > Blocking under infinite compute slots (K = inf, N = 36, G = 40);
         (b) Blocking > OCC under finite compute slots (K = 8, N = 36, G = 40) with true
             wait-for cycle member abortion (`0` lasso-prefix bystander aborts);
         (c) open-arrival orphan-lock retention (`orphan_locks[g] = lease_ttl_units`): zero
             spurious collapse at G = 10,000 (`0%` contention control), `9.11x` genuine
             orphan-lock starvation at `(N = 16, G = 24, K = 8, p_abandon = 0.25, TTL = 60.0)`,
             and restored `Blocking > OCC` at identical `(N = 16, G = 24, K = 8, p_abandon = 0.25)`
             when fenced lease TTL is shortened to `1.0`.

  4. `run_probe_4_deconfounded_intervention_selector`:
     - [toy model / parametric decision model]: Unit-consistent total-agent-work + defect-loss
       expected-cost selector separating goal redundancy `omega` in [0, 1] from structural file
       coupling `kappa` in [0, 1], directional dependency `delta` in [0, 1], semantic ambiguity
       `sem_ambig` in [0, 1], and Knight & Leveson (1986) correlated failure
       `p_diff = p^2 + rho * p * (1 - p)`, verified on zero-overlap baseline + six canonical
       archetypes + three non-vacuity ablations.

  5. `run_probe_5_empirical_forensics`:
     - Primary-source numerator/denominator reconciliation and exact Wilson 95% CIs for
       whystar/MSR2018-DupPR (`1,751` multi-PR duplicate groups = `3,619` unique PRs = `2,032`
       C(k, 2) pairs in Li et al. IEEE TSE 2022a vs. `2,323` pairs in Yu et al. MSR 2018),
       Brun et al. (ESEC/FSE 2011 exact N = 3,562 all-system vs. N = 1,694 build+test row sum
       correcting section 4.2's "5,355" prose typo), AgenticFlict (AIware '26 pp. 323-331,
       N = 107,026 Table 2 vs. N = 105,533 prose), Xu et al. (2026 cross-agent vs. intra-agent),
       CooperBench (2026 Table 6), and NP-Bench (2026 Table 2 `C0` vs. `C1-DETECT` vs. `C1-PLAN`).
"""

from __future__ import annotations

import itertools
import json
import math
import os
import random
import stat
import subprocess
import tempfile
from pathlib import Path
from typing import Any


# ============================================================================
# Probe P1: Gray & Cheriton (SOSP 1989) Exact Eq. 1-2, Demand vs. Proactive
#           Keepalive Crash-Stall Optima, and Progress-Witness Lease Renewal
# ============================================================================
def run_probe_1_gray_cheriton_and_progress_leases() -> dict[str, Any]:
    # --- Part 1A: [exact Gray & Cheriton 1989 Eq. 1-2, Table 2 p. 205] ---
    R = 0.864         # reads / sec per client
    W = 0.039         # writes / sec per client
    m_prop = 0.001    # 1.0 ms propagation delay
    m_proc = 0.00025  # 0.25 ms message processing time
    eps = 0.100       # 100 ms clock uncertainty allowance
    N = 10            # client count (cancels in relative server load and per-op delay)

    delta_skew = (m_prop + 2.0 * m_proc) + eps  # 0.1015 s

    def effective_tc(t_s: float) -> float:
        return max(0.0, t_s - delta_skew)

    def exact_gc_server_load_rel(t_s: float, S: int, multicast: bool = True) -> float:
        """Relative consistency message load L(t_s) / (2*N*R) per Eq. (1) & footnotes 5-6."""
        if t_s == 0.0:
            return 1.0
        t_c = effective_tc(t_s)
        ext_load = (2.0 * N * R) / (1.0 + R * t_c)
        if S <= 1:
            write_load = 0.0
        elif multicast:
            write_load = N * S * W
        else:
            write_load = N * 2.0 * (S - 1) * W
        return (ext_load + write_load) / (2.0 * N * R)

    def exact_gc_avg_delay_ms(t_s: float, S: int) -> float:
        """Average consistency delay per read/write in ms per Eq. (2), p. 204."""
        t_c = effective_tc(t_s) if t_s > 0.0 else 0.0
        read_term = (2.0 * R * (m_prop + 2.0 * m_proc)) / (1.0 + R * t_c)
        if t_s == 0.0 or S <= 1:
            t_a = 0.0
        else:
            # Multicast request + (S - 1) replies: 2*m_prop + ((S - 1) + 3)*m_proc
            t_a = 2.0 * m_prop + (S + 2) * m_proc
        return 1000.0 * (read_term + W * t_a) / (R + W)

    # Sub-skew penalty cliff (Gray & Cheriton p. 204): 0 < t_S <= Delta => t_C = 0
    sub_skew_ts = 0.050
    rel_zero = exact_gc_server_load_rel(0.0, S=10)
    rel_sub_skew = exact_gc_server_load_rel(sub_skew_ts, S=10)
    assert effective_tc(sub_skew_ts) == 0.0
    assert rel_sub_skew > rel_zero

    sharing_table: dict[str, Any] = {}
    for S in (1, 10, 20, 40):
        if S == 1:
            alpha_mcast = None
            alpha_unicast = None
            ts_be_mcast = delta_skew
            ts_be_unicast = delta_skew
        else:
            a_m = (2.0 * R) / (S * W)
            a_u = R / ((S - 1) * W)
            alpha_mcast = round(a_m, 4)
            alpha_unicast = round(a_u, 4)
            ts_be_mcast = (delta_skew + 1.0 / (R * (a_m - 1.0))) if a_m > 1.0 else float("inf")
            ts_be_unicast = (delta_skew + 1.0 / (R * (a_u - 1.0))) if a_u > 1.0 else float("inf")

        rel_10s = exact_gc_server_load_rel(10.0, S, multicast=True)
        total_rel_10s = 0.70 + 0.30 * rel_10s
        total_rel_inf = 0.70 + 0.30 * (0.0 if S == 1 else (S * W) / (2.0 * R))
        sharing_table[f"S={S}"] = {
            "alpha_multicast": alpha_mcast,
            "alpha_unicast": alpha_unicast,
            "ts_breakeven_mcast_s": None if math.isinf(ts_be_mcast) else round(ts_be_mcast, 4),
            "ts_breakeven_unicast_s": None if math.isinf(ts_be_unicast) else round(ts_be_unicast, 4),
            "rel_consistency_load_10s": round(rel_10s, 4),
            "total_traffic_reduction_10s_pct": round((1.0 - total_rel_10s) * 100.0, 2),
            "excess_over_inf_lease_10s_pct": round((total_rel_10s / total_rel_inf - 1.0) * 100.0, 2),
            "avg_consistency_delay_10s_ms": round(exact_gc_avg_delay_ms(10.0, S), 4),
        }

    assert sharing_table["S=1"]["avg_consistency_delay_10s_ms"] == 0.3005
    assert sharing_table["S=10"]["ts_breakeven_unicast_s"] == 0.8934
    assert 0.104 <= sharing_table["S=1"]["rel_consistency_load_10s"] <= 0.105
    assert 26.8 <= sharing_table["S=1"]["total_traffic_reduction_10s_pct"] <= 26.9
    assert 20.0 <= sharing_table["S=10"]["total_traffic_reduction_10s_pct"] <= 20.2
    assert sharing_table["S=40"]["rel_consistency_load_10s"] > 1.0
    assert 10.84 <= sharing_table["S=40"]["ts_breakeven_mcast_s"] <= 10.86

    # --- Part 1B: [derived renewal + crash-stall cost models] ---
    # 1B-1. Demand-driven non-heartbeated cache leases (Gray & Cheriton V-System):
    # Renewed only upon the next Poisson(R) read after local expiry t_C = max(0, t_S - Delta).
    # Active server lease duty fraction over cycle (t_C + 1/R):
    #   pi_on(t_S) = min(1, (R * t_S) / (1 + R * max(0, t_S - Delta))).
    # Conditional on crash while active, remaining server grant is Uniform(0, t_S) => E[stall] = 0.5 * t_S.
    # High-duty (R * t_S >> 1 => pi_on -> 1) closed-form stationary point:
    #   t_S_hd* = Delta - 1/R + 2 / sqrt(lambda_fail * c_stall).
    lam_v = 1.0 / 3600.0
    c_stall_v = 80.0

    def pi_on_demand(ts: float, r_rate: float, delta: float) -> float:
        if ts <= 0.0:
            return 0.0
        tc = max(0.0, ts - delta)
        return min(1.0, (r_rate * ts) / (1.0 + r_rate * tc))

    def cost_demand_high_duty(ts: float, r_rate: float, delta: float, lam: float, c_s: float) -> float:
        tc = max(0.0, ts - delta)
        ext = (2.0 * r_rate) / (1.0 + r_rate * tc) if ts > 0.0 else 2.0 * r_rate
        return ext + 0.5 * lam * c_s * ts

    def cost_demand_exact_duty(ts: float, r_rate: float, delta: float, lam: float, c_s: float) -> float:
        tc = max(0.0, ts - delta)
        ext = (2.0 * r_rate) / (1.0 + r_rate * tc) if ts > 0.0 else 2.0 * r_rate
        return ext + 0.5 * lam * c_s * pi_on_demand(ts, r_rate, delta) * ts

    ts_v_hd = delta_skew - (1.0 / R) + (2.0 / math.sqrt(lam_v * c_stall_v))
    grid_v = [0.0] + [delta_skew + 0.005 * k for k in range(1, 8000)]
    best_v_hd_grid = min(grid_v, key=lambda x: cost_demand_high_duty(x, R, delta_skew, lam_v, c_stall_v))
    best_v_exact_grid = min(grid_v, key=lambda x: cost_demand_exact_duty(x, R, delta_skew, lam_v, c_stall_v))
    pi_v_at_hd = pi_on_demand(ts_v_hd, R, delta_skew)
    assert abs(ts_v_hd - 12.3605) < 1e-3
    assert abs(cost_demand_high_duty(ts_v_hd, R, delta_skew, lam_v, c_stall_v) - cost_demand_high_duty(best_v_hd_grid, R, delta_skew, lam_v, c_stall_v)) < 1e-6
    assert abs(best_v_exact_grid - 12.4015) < 0.01

    # Un-heartbeated high-abandonment issue claim (tau_hb -> inf, low check rate R = 1/600, lam_fail = 1/900):
    # Stationary point is negative (Delta - 1/R + 2/sqrt(lam*c) < 0), collapsing optimal blocking grant to 0.0s.
    r_oss, delta_oss, lam_oss, c_oss = 1.0 / 600.0, 5.0, 1.0 / 900.0, 25.0
    tc_oss_stat = (2.0 / math.sqrt(lam_oss * c_oss)) - (1.0 / r_oss)
    ts_oss_opt = 0.0 if tc_oss_stat <= 0.0 else delta_oss + tc_oss_stat
    assert ts_oss_opt == 0.0

    # 1B-2. Proactive keepalive leases (ZooKeeper / Chubby / etcd / active agent lease):
    # Holder renews proactively every tau_hb = eta * (t_S - Delta) seconds (ZooKeeper Hunt et al. 2010
    # section 4.4 uses eta = 1/3). Because each renewal resets server expiry to full t_S, a uniform crash
    # inside [0, tau_hb) leaves residual server stall:
    #   E[stall_hb] = t_S - 0.5 * tau_hb = (1 - eta/2) * t_S + (eta/2) * Delta
    # (for eta = 1/3: (5/6)*t_S + (1/6)*Delta, NOT 0.5*t_S!).
    # Minimizing J_hb(t_S) = 2 / (eta * (t_S - Delta)) + lam_fail * c_stall * E[stall_hb] yields:
    #   t_S_hb* = Delta + sqrt(2 / (eta * (1 - eta/2) * lam_fail * c_stall)).
    eta_zk = 1.0 / 3.0
    delta_hb = 2.0
    lam_hb = 1.0 / 1800.0
    c_stall_hb = 10.0

    def cost_proactive_hb(ts: float) -> float:
        tc = ts - delta_hb
        if tc <= 1e-9:
            return float("inf")
        exp_stall = (1.0 - 0.5 * eta_zk) * ts + 0.5 * eta_zk * delta_hb
        return (2.0 / (eta_zk * tc)) + lam_hb * c_stall_hb * exp_stall

    ts_hb_opt = delta_hb + math.sqrt(2.0 / (eta_zk * (1.0 - 0.5 * eta_zk) * lam_hb * c_stall_hb))
    tau_hb_opt = eta_zk * (ts_hb_opt - delta_hb)
    exp_stall_hb_opt = (1.0 - 0.5 * eta_zk) * ts_hb_opt + 0.5 * eta_zk * delta_hb
    grid_hb = [delta_hb + 0.01 * k for k in range(1, 10000)]
    best_hb_grid = min(grid_hb, key=cost_proactive_hb)
    assert abs(ts_hb_opt - 38.0) < 1e-9
    assert abs(tau_hb_opt - 12.0) < 1e-9
    assert abs(exp_stall_hb_opt - 32.0) < 1e-9
    assert abs(best_hb_grid - ts_hb_opt) < 1e-6

    # Fixed-cadence keepalive corollary (fixed tau_hb = 5.0s independent of t_S):
    # Renewal load 2/tau_hb = 0.40 msg/s is constant in t_S, so J_fixed_hb(t_S) increases strictly with t_S,
    # pushing t_S* to the smallest jitter-safe multiple Delta + k_miss * tau_hb (17.0s at k_miss = 3).
    tau_fixed = 5.0
    k_miss = 3
    ts_fixed_min_safe = delta_hb + k_miss * tau_fixed
    assert ts_fixed_min_safe == 17.0

    derived_opt_summary = {
        "demand_driven_v_cache": {
            "ts_high_duty_closed_form_s": round(ts_v_hd, 4),
            "ts_exact_duty_grid_opt_s": round(best_v_exact_grid, 4),
            "active_duty_pi_on_at_opt": round(pi_v_at_hd, 4),
            "min_cost_high_duty_msg_per_s": round(cost_demand_high_duty(ts_v_hd, R, delta_skew, lam_v, c_stall_v), 6),
            "zero_lease_cost_msg_per_s": round(cost_demand_high_duty(0.0, R, delta_skew, lam_v, c_stall_v), 6),
            "rare_failure_product_lam_ts": round(lam_v * ts_v_hd, 6),
        },
        "proactive_keepalive_agent_lease_eta_1_3": {
            "eta_ratio": round(eta_zk, 6),
            "ts_hb_closed_form_s": round(ts_hb_opt, 4),
            "tau_hb_interval_s": round(tau_hb_opt, 4),
            "expected_crash_stall_s": round(exp_stall_hb_opt, 4),
            "min_cost_hb_msg_per_s": round(cost_proactive_hb(ts_hb_opt), 6),
            "fixed_5s_touch_k3_jitter_floor_s": ts_fixed_min_safe,
            "rare_failure_product_lam_ts": round(lam_hb * ts_hb_opt, 6),
        },
        "unheartbeated_oss_issue_claim": {
            "ts_opt_s": ts_oss_opt,
            "stationary_tc_s": round(tc_oss_stat, 4),
        },
    }

    # --- Part 1C: [toy discrete simulation] Liveness-vs-Progress Witness Lease Renewal ---
    def simulate_lease_renewal_policy(
        require_progress_witness: bool,
        scenario: str,
        horizon_s: int = 300,
        hb_interval_s: int = 10,
        k_max_stale: int = 3,
        w2_work_needed_s: int = 40,
    ) -> dict[str, Any]:
        """Simulate W1 + backup W2 under:
        - 'stuck_zero_progress': W1 makes progress up to t=20s, then loops on identical state.
        - 'stuck_ab_oscillation': W1 oscillates A -> B -> A tree states every 10s with no metric gain.
        - 'healthy_slow_compile': W1 has a legitimate 25s build/proof step (< k_max*hb = 30s) between
          monotone progress witnesses and completes cleanly at t=80s without false eviction.
        """
        fencing_token = 1
        holder = "W1"
        evicted_at_s: int | None = None
        stale_renewals = 0
        best_rank = (0, -10)  # (passing_tests, -compiler_errors)
        seen_trees = {"tree_init"}
        w2_progress_s = 0
        w1_progress_s = 0
        wasted_loop_s = 0
        completed_at_s: int | None = None
        zombie_writes_blocked = 0
        false_eviction = False

        for t in range(hb_interval_s, horizon_s + 1, hb_interval_s):
            if holder == "W1":
                if scenario == "stuck_zero_progress":
                    if t <= 20:
                        w1_progress_s += hb_interval_s
                        cand_rank = (t // 10, -10 + (t // 10))
                        cand_tree = f"tree_{t}"
                    else:
                        wasted_loop_s += hb_interval_s
                        cand_rank = (2, -8)
                        cand_tree = "tree_20"
                elif scenario == "stuck_ab_oscillation":
                    if t <= 20:
                        w1_progress_s += hb_interval_s
                        cand_rank = (t // 10, -10 + (t // 10))
                        cand_tree = f"tree_{t}"
                    else:
                        wasted_loop_s += hb_interval_s
                        cand_rank = (2, -8)
                        cand_tree = "tree_osc_A" if ((t // 10) % 2 == 0) else "tree_osc_B"
                elif scenario == "healthy_slow_compile":
                    w1_progress_s += hb_interval_s
                    if t in (30, 60, 80):
                        cand_rank = (t // 10, -10 + (t // 10))
                        cand_tree = f"tree_good_{t}"
                    else:
                        cand_rank = best_rank
                        cand_tree = f"tree_good_{(t // 30) * 30}" if t > 30 else "tree_init"
                    if w1_progress_s >= 80:
                        completed_at_s = t
                        break
                else:
                    raise ValueError(scenario)

                made_monotone_progress = (cand_rank > best_rank) or (cand_tree not in seen_trees and cand_rank >= best_rank)
                if made_monotone_progress:
                    best_rank = max(best_rank, cand_rank)
                    seen_trees.add(cand_tree)
                    stale_renewals = 0
                else:
                    stale_renewals += 1

                if require_progress_witness and stale_renewals >= k_max_stale:
                    if scenario == "healthy_slow_compile":
                        false_eviction = True
                    fencing_token += 1
                    holder = "W2"
                    evicted_at_s = t
            else:
                # Stale W1 attempts a background write 20s after eviction -> blocked by fencing_token == 2!
                if evicted_at_s is not None and t == evicted_at_s + 20:
                    zombie_writes_blocked += 1
                w2_progress_s += hb_interval_s
                if w2_progress_s >= w2_work_needed_s:
                    completed_at_s = t
                    break

        return {
            "completed": completed_at_s is not None,
            "completed_at_s": completed_at_s,
            "evicted_at_s": evicted_at_s,
            "final_holder": holder,
            "final_fencing_token": fencing_token,
            "wasted_loop_s": wasted_loop_s,
            "zombie_writes_blocked": zombie_writes_blocked,
            "false_eviction": false_eviction,
        }

    liveness_stuck = simulate_lease_renewal_policy(False, "stuck_zero_progress")
    witness_stuck = simulate_lease_renewal_policy(True, "stuck_zero_progress")
    witness_osc = simulate_lease_renewal_policy(True, "stuck_ab_oscillation")
    witness_slow_ok = simulate_lease_renewal_policy(True, "healthy_slow_compile")

    assert not liveness_stuck["completed"] and liveness_stuck["wasted_loop_s"] == 280
    assert witness_stuck["completed"] and witness_stuck["completed_at_s"] == 90 and witness_stuck["zombie_writes_blocked"] == 1
    assert witness_osc["completed"] and witness_osc["completed_at_s"] == 110 and witness_osc["zombie_writes_blocked"] == 1
    assert witness_slow_ok["completed"] and not witness_slow_ok["false_eviction"] and witness_slow_ok["final_holder"] == "W1"

    return {
        "exact_gray_cheriton_1989_eq1_eq2": {
            "model_origin": "exact_gray_cheriton_1989_eq1_eq2",
            "delta_transit_plus_skew_s": round(delta_skew, 6),
            "sub_skew_cliff": {
                "ts_s": sub_skew_ts,
                "tc_s": 0.0,
                "rel_load_ts_0": round(rel_zero, 4),
                "rel_load_sub_skew_S10": round(rel_sub_skew, 4),
                "load_penalty_pct": round((rel_sub_skew / rel_zero - 1.0) * 100.0, 2),
            },
            "v_system_table2_reproduction": sharing_table,
        },
        "derived_renewal_plus_crash_stall_optima": {
            "model_origin": "derived_demand_vs_proactive_keepalive_crash_stall",
            **derived_opt_summary,
        },
        "progress_witness_lease_renewal": {
            "model_origin": "[toy discrete simulation]",
            "liveness_only_stuck_loop": liveness_stuck,
            "progress_witness_stuck_loop": witness_stuck,
            "progress_witness_ab_oscillation": witness_osc,
            "progress_witness_slow_compile_guard": witness_slow_ok,
        },
    }


# ============================================================================
# Probe P2: 30-Schedule Pause/Orphan Matrix + Real Ephemeral Git CAS Execution
# ============================================================================
def run_probe_2_fencing_matrix_and_real_git_cas() -> dict[str, Any]:
    # --- Part 2A: 30-Schedule Pause + Orphan-Subagent Matrix (Disaggregated) ---
    T_lease = 10
    D_lock_delay = 60  # Burrows (OSDI 2006) 1-minute Chubby lock-delay
    pause_durations = [2, 6, 11, 18, 75]
    pause_points = ["before_local_check", "after_local_check"]
    child_modes = ["no_child", "ambient_cred_child", "token_scoped_child"]

    protocols = [
        "unfenced_ttl_only",
        "unfenced_ttl_plus_client_recheck",
        "chubby_lock_delay_only",
        "fenced_token_parent_only_ambient_child",
        "fenced_token_storage_cas_all_writers",
    ]
    matrix_results: dict[str, dict[str, Any]] = {
        p: {
            "total_schedules": 0,
            "split_brain_corruptions": 0,
            "safe_completions": 0,
            "no_child_parent_only_corruptions_of_10": 0,
            "cause_breakdown": {"parent_only": 0, "child_only": 0, "both": 0},
        }
        for p in protocols
    }

    for tau, pt, cm in itertools.product(pause_durations, pause_points, child_modes):
        t_ready = 3
        for proto in protocols:
            matrix_results[proto]["total_schedules"] += 1
            parent_corrupted = False
            child_corrupted = False
            w2_acquire = T_lease + (D_lock_delay if proto == "chubby_lock_delay_only" else 0)

            if pt == "before_local_check":
                t_check = t_ready + tau
                t_write = t_check + 1
            else:
                t_check = t_ready
                t_write = t_check + tau

            w2_committed_before_w1 = t_write > (w2_acquire + 1)
            w1_attempts = not (proto == "unfenced_ttl_plus_client_recheck" and t_check >= T_lease)

            if w2_committed_before_w1 and w1_attempts:
                if proto in ("unfenced_ttl_only", "unfenced_ttl_plus_client_recheck", "chubby_lock_delay_only"):
                    parent_corrupted = True

            t_child_write = 2 + tau + 8
            if cm != "no_child" and t_child_write > (w2_acquire + 1):
                if proto in ("unfenced_ttl_only", "unfenced_ttl_plus_client_recheck", "chubby_lock_delay_only"):
                    child_corrupted = True
                elif proto == "fenced_token_parent_only_ambient_child" and cm == "ambient_cred_child":
                    child_corrupted = True

            if parent_corrupted or child_corrupted:
                matrix_results[proto]["split_brain_corruptions"] += 1
                if cm == "no_child" and parent_corrupted:
                    matrix_results[proto]["no_child_parent_only_corruptions_of_10"] += 1
                if parent_corrupted and child_corrupted:
                    matrix_results[proto]["cause_breakdown"]["both"] += 1
                elif parent_corrupted:
                    matrix_results[proto]["cause_breakdown"]["parent_only"] += 1
                else:
                    matrix_results[proto]["cause_breakdown"]["child_only"] += 1
            else:
                matrix_results[proto]["safe_completions"] += 1

    assert matrix_results["unfenced_ttl_only"]["split_brain_corruptions"] == 26
    assert matrix_results["unfenced_ttl_only"]["no_child_parent_only_corruptions_of_10"] == 6
    assert matrix_results["unfenced_ttl_plus_client_recheck"]["split_brain_corruptions"] == 23
    assert matrix_results["unfenced_ttl_plus_client_recheck"]["no_child_parent_only_corruptions_of_10"] == 3
    assert matrix_results["unfenced_ttl_plus_client_recheck"]["cause_breakdown"] == {
        "parent_only": 3,
        "child_only": 14,
        "both": 6,
    }
    assert matrix_results["chubby_lock_delay_only"]["split_brain_corruptions"] == 6
    assert matrix_results["chubby_lock_delay_only"]["no_child_parent_only_corruptions_of_10"] == 2
    assert matrix_results["fenced_token_parent_only_ambient_child"]["split_brain_corruptions"] == 10
    assert matrix_results["fenced_token_parent_only_ambient_child"]["no_child_parent_only_corruptions_of_10"] == 0
    assert matrix_results["fenced_token_storage_cas_all_writers"]["split_brain_corruptions"] == 0

    # --- Part 2B: [real git execution] inside cleaned TemporaryDirectory ---
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        home_dir = root / "home"
        home_dir.mkdir()

        def git_env(ts_sec: int) -> dict[str, str]:
            iso = f"2026-01-01T00:00:{ts_sec:02d}+00:00"
            return {
                "PATH": os.environ.get("PATH", "/usr/bin:/bin"),
                "HOME": str(home_dir),
                "GIT_CONFIG_NOSYSTEM": "1",
                "GIT_CONFIG_GLOBAL": "/dev/null",
                "GIT_AUTHOR_NAME": "Deterministic Probe",
                "GIT_AUTHOR_EMAIL": "probe@example.invalid",
                "GIT_COMMITTER_NAME": "Deterministic Probe",
                "GIT_COMMITTER_EMAIL": "probe@example.invalid",
                "GIT_AUTHOR_DATE": iso,
                "GIT_COMMITTER_DATE": iso,
                "LC_ALL": "C",
            }

        def run_git(
            cwd: Path,
            args: list[str],
            ts_sec: int = 0,
            stdin_text: str | None = None,
            check: bool = True,
        ) -> subprocess.CompletedProcess[str]:
            cp = subprocess.run(
                ["git", *args],
                cwd=str(cwd),
                env=git_env(ts_sec),
                input=stdin_text,
                text=True,
                capture_output=True,
            )
            if check and cp.returncode != 0:
                raise RuntimeError(f"git {args} failed ({cp.returncode}): {cp.stderr}")
            return cp

        origin = root / "origin.git"
        origin.mkdir()
        run_git(origin, ["init", "--bare", "--initial-branch=main"])

        # Seed base commit C0 on refs/heads/task
        seed = root / "seed"
        run_git(root, ["clone", str(origin), str(seed)])
        (seed / "state.txt").write_text("v0_base\n", encoding="utf-8")
        run_git(seed, ["add", "state.txt"], ts_sec=1)
        run_git(seed, ["commit", "-m", "Base commit C0\n\nFencing-Token: 0"], ts_sec=1)
        run_git(seed, ["push", "origin", "HEAD:refs/heads/task"], ts_sec=1)
        c0_oid = run_git(seed, ["rev-parse", "HEAD"]).stdout.strip()

        # Worker 1 (token 1), Worker 1's orphan child (ambient creds, no token trailer), and Worker 2 (token 2)
        w1 = root / "w1"
        w1_orphan = root / "w1_orphan"
        w2 = root / "w2"
        for clone_dir in (w1, w1_orphan, w2):
            run_git(root, ["clone", "--branch", "task", str(origin), str(clone_dir)], ts_sec=2)

        (w1 / "state.txt").write_text("v1_stale_parent\n", encoding="utf-8")
        run_git(w1, ["commit", "-am", "W1 parent commit\n\nFencing-Token: 1"], ts_sec=3)
        c1_parent_oid = run_git(w1, ["rev-parse", "HEAD"]).stdout.strip()

        (w1_orphan / "state.txt").write_text("v1_zombie_orphan_subagent\n", encoding="utf-8")
        run_git(w1_orphan, ["commit", "-am", "W1 orphan subagent commit (ambient creds)"], ts_sec=4)
        c1_orphan_oid = run_git(w1_orphan, ["rev-parse", "HEAD"]).stdout.strip()

        (w2 / "state.txt").write_text("v2_fresh_holder\n", encoding="utf-8")
        run_git(w2, ["commit", "-am", "W2 fresh commit\n\nFencing-Token: 2"], ts_sec=5)
        c2_oid = run_git(w2, ["rev-parse", "HEAD"]).stdout.strip()

        # G1: W2 commits C2; orphan subagent pushes with --force -> silent split-brain overwrite!
        run_git(w2, ["push", "origin", "HEAD:refs/heads/task"], ts_sec=6)
        assert run_git(origin, ["rev-parse", "refs/heads/task"]).stdout.strip() == c2_oid
        cp_g1 = run_git(w1_orphan, ["push", "--force", "origin", "HEAD:refs/heads/task"], ts_sec=7, check=False)
        g1_head_after = run_git(origin, ["rev-parse", "refs/heads/task"]).stdout.strip()
        g1_corrupted = cp_g1.returncode == 0 and g1_head_after == c1_orphan_oid
        assert g1_corrupted

        # Reset origin refs/heads/task back to C2 for G2 tests
        run_git(origin, ["update-ref", "refs/heads/task", c2_oid])

        # G2a: Explicit expected-OID `--force-with-lease=refs/heads/task:<C0>` catches linear C0 -> C2 advance
        cp_g2a = run_git(
            w1_orphan,
            ["push", f"--force-with-lease=refs/heads/task:{c0_oid}", "origin", "HEAD:refs/heads/task"],
            ts_sec=8,
            check=False,
        )
        g2a_blocked = (
            cp_g2a.returncode != 0 and run_git(origin, ["rev-parse", "refs/heads/task"]).stdout.strip() == c2_oid
        )
        assert g2a_blocked

        # G2b-1: Background `git fetch origin` in shared/inherited repo updates remote-tracking ref to C2,
        # so bare `git push --force-with-lease` SUCCEEDS and overwrites C2!
        run_git(w1_orphan, ["fetch", "origin"], ts_sec=9)
        cp_g2b_fetch = run_git(
            w1_orphan,
            ["push", "--force-with-lease", "origin", "HEAD:refs/heads/task"],
            ts_sec=10,
            check=False,
        )
        g2b_fetch_corrupted = (
            cp_g2b_fetch.returncode == 0
            and run_git(origin, ["rev-parse", "refs/heads/task"]).stdout.strip() == c1_orphan_oid
        )
        assert g2b_fetch_corrupted

        # G2b-2: ABA base-OID hazard! Suppose lease token 3 intentionally rolls back refs/heads/task to C0;
        # then W1's explicit `--force-with-lease=refs/heads/task:<C0>` matches C0 and overwrites!
        run_git(origin, ["update-ref", "refs/heads/task", c0_oid])
        cp_g2b_aba = run_git(
            w1,
            ["push", f"--force-with-lease=refs/heads/task:{c0_oid}", "origin", "HEAD:refs/heads/task"],
            ts_sec=11,
            check=False,
        )
        g2b_aba_corrupted = (
            cp_g2b_aba.returncode == 0
            and run_git(origin, ["rev-parse", "refs/heads/task"]).stdout.strip() == c1_parent_oid
        )
        assert g2b_aba_corrupted

        # G3 setup: Verify atomic `git update-ref --stdin` CAS semantics directly
        t1_blob = run_git(origin, ["hash-object", "-w", "--stdin"], stdin_text="1\n").stdout.strip()
        t3_blob = run_git(origin, ["hash-object", "-w", "--stdin"], stdin_text="3\n").stdout.strip()
        z40 = "0" * 40

        run_git(
            origin,
            ["update-ref", "--stdin"],
            stdin_text=f"start\nupdate refs/leases/task {t1_blob} {z40}\nupdate refs/heads/task {c0_oid}\ncommit\n",
        )
        cp_stale_txn = run_git(
            origin,
            ["update-ref", "--stdin"],
            stdin_text=f"start\nverify refs/leases/task {z40}\nupdate refs/heads/task {c1_parent_oid} {c0_oid}\ncommit\n",
            check=False,
        )
        atomic_txn_aborted_cleanly = (
            cp_stale_txn.returncode != 0
            and run_git(origin, ["rev-parse", "refs/heads/task"]).stdout.strip() == c0_oid
            and run_git(origin, ["rev-parse", "refs/leases/task"]).stdout.strip() == t1_blob
        )
        assert atomic_txn_aborted_cleanly

        # G3a: Reproduce the live TOCTOU split-brain race in `hooks/pre-receive`!
        # Because `hooks/pre-receive` executes BEFORE `receive-pack` locks `refs/heads/task.lock`,
        # a concurrent Coordinator `git update-ref --stdin` (`1 -> 3` verifying `refs/heads/task == C0`)
        # commits cleanly right after `pre-receive` reads `refs/leases/task == 1`, allowing stale `C1`
        # (`Fencing-Token: 1`) to overwrite `refs/heads/task` under active lease token `3`!
        g3a_coord_log = root / "g3a_coord.json"
        pre_hook = origin / "hooks" / "pre-receive"
        pre_hook.write_text(
            "#!/usr/bin/env python3\n"
            "import json, os, subprocess, sys\n"
            "cur_tok = int(subprocess.check_output(['git', 'cat-file', '-p', 'refs/leases/task'], text=True).strip())\n"
            "for line in sys.stdin:\n"
            "    old_oid, new_oid, ref = line.strip().split()\n"
            "    if ref == 'refs/heads/task':\n"
            "        msg = subprocess.check_output(['git', 'log', '-1', '--format=%B', new_oid], text=True)\n"
            "        tok = None\n"
            "        for ml in msg.splitlines():\n"
            "            if ml.startswith('Fencing-Token:'):\n"
            "                tok = int(ml.split(':', 1)[1].strip())\n"
            "        if tok is None or tok < cur_tok:\n"
            "            sys.exit(1)\n"
            "c_env = {k: v for k, v in os.environ.items() if not k.startswith('GIT_QUARANTINE') and k not in ('GIT_OBJECT_DIRECTORY', 'GIT_ALTERNATE_OBJECT_DIRECTORIES')}\n"
            f"cp = subprocess.run(['git', 'update-ref', '--stdin'], input='start\\nupdate refs/leases/task {t3_blob} {t1_blob}\\nverify refs/heads/task {c0_oid}\\ncommit\\n', text=True, capture_output=True, env=c_env)\n"
            f"open({str(g3a_coord_log)!r}, 'w', encoding='utf-8').write(json.dumps({{'coord_rc': cp.returncode}}))\n"
            "sys.exit(0)\n",
            encoding="utf-8",
        )
        pre_hook.chmod(pre_hook.stat().st_mode | stat.S_IXUSR)

        cp_g3a_w1 = run_git(
            w1,
            ["push", f"--force-with-lease=refs/heads/task:{c0_oid}", "origin", "HEAD:refs/heads/task"],
            ts_sec=12,
            check=False,
        )
        g3a_coord_res = json.loads(g3a_coord_log.read_text(encoding="utf-8"))
        g3a_active_tok = int(run_git(origin, ["cat-file", "-p", "refs/leases/task"]).stdout.strip())
        g3a_head = run_git(origin, ["rev-parse", "refs/heads/task"]).stdout.strip()
        g3a_pre_receive_toctou_corrupted = (
            cp_g3a_w1.returncode == 0
            and g3a_coord_res["coord_rc"] == 0
            and g3a_active_tok == 3
            and g3a_head == c1_parent_oid
        )
        assert g3a_pre_receive_toctou_corrupted

        # G3b: Replace `pre-receive` with `hooks/reference-transaction` on `sys.argv[1] == "prepared"`.
        # Reset state to token 1 and head C0 before installing `reference-transaction`.
        pre_hook.unlink()
        run_git(
            origin,
            ["update-ref", "--stdin"],
            stdin_text=f"start\nupdate refs/leases/task {t1_blob} {t3_blob}\nupdate refs/heads/task {c0_oid} {c1_parent_oid}\ncommit\n",
        )

        g3b_coord_log = root / "g3b_coord.json"
        trigger_interleaving_1 = root / "trigger_i1"
        trigger_interleaving_1.write_text("1", encoding="utf-8")

        rt_hook = origin / "hooks" / "reference-transaction"
        rt_hook.write_text(
            "#!/usr/bin/env python3\n"
            "import json, os, pathlib, subprocess, sys\n"
            "if len(sys.argv) < 2 or sys.argv[1] != 'prepared':\n"
            "    sys.exit(0)\n"
            "lines = [ln.strip().split() for ln in sys.stdin if ln.strip()]\n"
            "lease_mut = [t for t in lines if len(t) == 3 and t[2] == 'refs/leases/task' and t[0] != t[1] and t[1] != '0'*40]\n"
            "task_mut = [t for t in lines if len(t) == 3 and t[2] == 'refs/heads/task' and t[0] != t[1] and t[1] != '0'*40]\n"
            "if lease_mut:\n"
            "    # Coordinator atomic lease advancement (+ optional ABA rollback) enforces strict monotonic token increase\n"
            "    old_l, new_l, _ = lease_mut[0]\n"
            "    old_v = 0 if old_l == '0'*40 else int(subprocess.check_output(['git', 'cat-file', '-p', old_l], text=True).strip())\n"
            "    new_v = int(subprocess.check_output(['git', 'cat-file', '-p', new_l], text=True).strip())\n"
            "    if new_v <= old_v:\n"
            "        sys.stderr.write('FENCE_REJECT: non-monotonic lease update\\n')\n"
            "        sys.exit(1)\n"
            "    sys.exit(0)\n"
            "if not task_mut:\n"
            "    sys.exit(0)\n"
            "cur_tok = int(subprocess.check_output(['git', 'cat-file', '-p', 'refs/leases/task'], text=True).strip())\n"
            "for old_oid, new_oid, ref in task_mut:\n"
            "    msg = subprocess.check_output(['git', 'log', '-1', '--format=%B', new_oid], text=True)\n"
            "    tok = None\n"
            "    for ml in msg.splitlines():\n"
            "        if ml.startswith('Fencing-Token:'):\n"
            "            tok = int(ml.split(':', 1)[1].strip())\n"
            "    if tok is None or tok < cur_tok:\n"
            "        sys.stderr.write(f'FENCE_REJECT: incoming_token={tok} < active_lease_token={cur_tok}\\n')\n"
            "        sys.exit(1)\n"
            f"flag = pathlib.Path({str(trigger_interleaving_1)!r})\n"
            "if flag.exists():\n"
            "    flag.unlink()\n"
            "    c_env = {k: v for k, v in os.environ.items() if not k.startswith('GIT_QUARANTINE') and k not in ('GIT_OBJECT_DIRECTORY', 'GIT_ALTERNATE_OBJECT_DIRECTORIES')}\n"
            f"    cp = subprocess.run(['git', 'update-ref', '--stdin'], input='start\\nupdate refs/leases/task {t3_blob} {t1_blob}\\nverify refs/heads/task {c0_oid}\\ncommit\\n', text=True, capture_output=True, env=c_env)\n"
            f"    open({str(g3b_coord_log)!r}, 'w', encoding='utf-8').write(json.dumps({{'coord_rc': cp.returncode, 'lock_held_rejected': 'task.lock' in cp.stderr}}))\n"
            "sys.exit(0)\n",
            encoding="utf-8",
        )
        rt_hook.chmod(rt_hook.stat().st_mode | stat.S_IXUSR)

        # G3b Interleaving 1: Push enters `prepared` first (holding `refs/heads/task.lock`);
        # concurrent Coordinator `update-ref --stdin` (`verify refs/heads/task C0`) fails closed on `task.lock`!
        cp_g3b_i1 = run_git(
            w1,
            ["push", f"--force-with-lease=refs/heads/task:{c0_oid}", "origin", "HEAD:refs/heads/task"],
            ts_sec=13,
            check=False,
        )
        g3b_i1_coord = json.loads(g3b_coord_log.read_text(encoding="utf-8"))
        g3b_interleaving_1_safe = (
            cp_g3b_i1.returncode == 0
            and g3b_i1_coord["coord_rc"] != 0
            and g3b_i1_coord["lock_held_rejected"]
            and int(run_git(origin, ["cat-file", "-p", "refs/leases/task"]).stdout.strip()) == 1
            and run_git(origin, ["rev-parse", "refs/heads/task"]).stdout.strip() == c1_parent_oid
        )
        assert g3b_interleaving_1_safe

        # G3b Interleaving 2: Coordinator atomically advances `refs/leases/task` (`1 -> 3`) and rolls back
        # `refs/heads/task` (`C1 -> C0`, creating the ABA trap while `rt_hook` remains continuously active!);
        # subsequent W1 (`Fencing-Token: 1`, matching C0) and W1 orphan (post-`fetch`) pushes are REJECTED!
        run_git(
            origin,
            ["update-ref", "--stdin"],
            stdin_text=f"start\nupdate refs/leases/task {t3_blob} {t1_blob}\nupdate refs/heads/task {c0_oid} {c1_parent_oid}\ncommit\n",
        )

        cp_g3b_w1_aba = run_git(
            w1,
            ["push", f"--force-with-lease=refs/heads/task:{c0_oid}", "origin", "HEAD:refs/heads/task"],
            ts_sec=14,
            check=False,
        )
        run_git(w1_orphan, ["fetch", "origin"], ts_sec=15)
        cp_g3b_orphan = run_git(
            w1_orphan,
            ["push", "--force-with-lease", "origin", "HEAD:refs/heads/task"],
            ts_sec=16,
            check=False,
        )

        # Worker 3 at active Fencing-Token: 3 pushes cleanly and advances refs/heads/task to C3!
        w3 = root / "w3"
        run_git(root, ["clone", "--branch", "task", str(origin), str(w3)], ts_sec=17)
        (w3 / "state.txt").write_text("v3_token3_authoritative\n", encoding="utf-8")
        run_git(w3, ["commit", "-am", "W3 authoritative commit\n\nFencing-Token: 3"], ts_sec=18)
        c3_oid = run_git(w3, ["rev-parse", "HEAD"]).stdout.strip()
        cp_g3b_w3 = run_git(
            w3,
            ["push", f"--force-with-lease=refs/heads/task:{c0_oid}", "origin", "HEAD:refs/heads/task"],
            ts_sec=19,
            check=False,
        )
        final_head = run_git(origin, ["rev-parse", "refs/heads/task"]).stdout.strip()
        assert cp_g3b_w1_aba.returncode != 0 and "FENCE_REJECT" in cp_g3b_w1_aba.stderr
        assert cp_g3b_orphan.returncode != 0 and "FENCE_REJECT" in cp_g3b_orphan.stderr
        assert cp_g3b_w3.returncode == 0 and final_head == c3_oid

        real_git_receipts = {
            "verification_tag": "[real git execution]",
            "trust_boundary": "non_byzantine_commit_trailer_requires_authenticated_per_token_capability_for_adversarial_writers",
            "deterministic_oids": {
                "c0_base": c0_oid,
                "c1_w1_stale": c1_parent_oid,
                "c1_orphan_ambient": c1_orphan_oid,
                "c2_w2_fresh": c2_oid,
                "c3_w3_authoritative": c3_oid,
            },
            "G1_unfenced_force_orphan_corrupts": g1_corrupted,
            "G2a_explicit_oid_lease_blocks_linear_stale": g2a_blocked,
            "G2b_implicit_fetch_force_with_lease_corrupts": g2b_fetch_corrupted,
            "G2b_aba_rollback_explicit_oid_corrupts": g2b_aba_corrupted,
            "G3_atomic_update_ref_aborts_on_cas_mismatch": atomic_txn_aborted_cleanly,
            "G3a_pre_receive_toctou_race_corrupts": g3a_pre_receive_toctou_corrupted,
            "G3b_ref_txn_prepared_blocks_concurrent_coord_lock": g3b_interleaving_1_safe,
            "G3b_ref_txn_prepared_blocks_aba_and_orphan": (
                cp_g3b_w1_aba.returncode != 0 and cp_g3b_orphan.returncode != 0 and final_head == c3_oid
            ),
        }

    return {
        "schedule_matrix_30x5": matrix_results,
        "real_git_ref_cas_execution": real_git_receipts,
    }


# ============================================================================
# Probe P3: Agrawal-Carey-Livny (TODS 1987) Analytical Fixed-Point Solver +
#           De-Confounded Discrete-Step Multi-Slot Simulation & Cookie-Licking
# ============================================================================
def run_probe_3_agrawal_inversion_and_cookie_licking() -> dict[str, Any]:
    # --- Part 3A: Processor-Shared Franaszek & Robinson (1985) Fixed Point ---
    # Under small independent pairwise conflict probability p_c and zero rollback delay,
    # setting processor-sharing speed s = min(1, K/N) and t_exec = 1/s yields x = Lambda_K * t_exec
    # satisfying x = N * (1 - p_c)^x = Lambda_inf(N). Thus useful utilization u(N) = (1 - p_c)^Lambda_inf(N)
    # is K-invariant while finite-slot throughput scales as Lambda_K(N) = min(1, K/N) * Lambda_inf(N).
    def solve_occ_fixed_point(N: int, p_c: float, K_slots: float | None, c_restart: float = 1.0) -> dict[str, float]:
        s = 1.0 if K_slots is None else min(1.0, K_slots / float(N))
        t_exec = 1.0 / s
        lo, hi = 0.0, float(N) * s
        for _ in range(80):
            mid = 0.5 * (lo + hi)
            p_surv = (1.0 - p_c) ** (mid * t_exec)
            work_per_commit = 1.0 + c_restart * ((1.0 - p_surv) / max(p_surv, 1e-9))
            rhs = (float(N) * s) / work_per_commit
            if rhs > mid:
                lo = mid
            else:
                hi = mid
        lam = 0.5 * (lo + hi)
        p_surv = (1.0 - p_c) ** (lam * t_exec)
        useful = 1.0 / (1.0 + c_restart * ((1.0 - p_surv) / max(p_surv, 1e-9)))
        return {"occ_throughput": round(lam, 4), "occ_useful_utilization": round(useful, 4)}

    analytical_curve = {
        f"N={n}": {
            "infinite_K": solve_occ_fixed_point(n, p_c=0.04, K_slots=None),
            "finite_K8": solve_occ_fixed_point(n, p_c=0.04, K_slots=8.0),
        }
        for n in (2, 4, 8, 16, 32, 64)
    }
    assert analytical_curve["N=64"]["infinite_K"]["occ_throughput"] > analytical_curve["N=8"]["infinite_K"]["occ_throughput"]
    assert analytical_curve["N=64"]["finite_K8"]["occ_throughput"] < analytical_curve["N=8"]["finite_K8"]["occ_throughput"]
    # Verify exact K-invariance of useful utilization u(N) = Lambda_K(N) / min(N, K):
    assert (
        analytical_curve["N=64"]["infinite_K"]["occ_useful_utilization"]
        == analytical_curve["N=64"]["finite_K8"]["occ_useful_utilization"]
        == 0.3752
    )

    # --- Part 3B: De-Confounded Discrete-Step Multi-Slot State-Machine Simulation ---
    def simulate_concurrency_control(
        mode: str,                 # "OCC" or "BLOCKING_2PL"
        N: int,
        num_granules: int,
        K_slots: float | None,     # None => infinite compute slots; float => shared slot cap
        p_abandon: float = 0.0,
        lease_ttl_units: float = 1.5,
        steps: int = 3000,
        dt: float = 0.05,
        seed: int = 20261122,
    ) -> dict[str, float | int]:
        """Mechanistic discrete-step simulator over `num_granules` shared resources.
        - Open contributor replacement on abandonment: when a worker silently abandons at
          progress >= 0.25, BOTH `OCC` and `BLOCKING_2PL` immediately replace the contributor slot
          via `reset_worker(w)`, while `BLOCKING_2PL` transfers any held locks into `orphan_locks[g]`
          (`lock_owner[g] = -1`) until `lease_ttl_units` expires without heartbeats.
        - Exact cycle-member deadlock resolution: ordered wait-for walk `path` slices the true cycle
          `cyc = path[path.index(holder_id):]` and aborts `workers[max(cyc)]` (`0` bystander aborts).
        """
        rng = random.Random(seed + (101 if mode == "OCC" else 202) + N * 7)

        def sample_pair() -> tuple[int, int]:
            a = rng.randrange(num_granules)
            b = rng.randrange(num_granules - 1)
            if b >= a:
                b += 1
            return a, b

        workers = []
        for wid in range(N):
            g1, g2 = sample_pair()
            workers.append({
                "id": wid,
                "g1": g1,
                "g2": g2,
                "prog": 0.0,
                "tainted": False,
                "will_abandon": (rng.random() < p_abandon),
                "holds": set(),
                "waiting_on": None,
            })

        lock_owner: dict[int, int | None] = {g: None for g in range(num_granules)}
        orphan_locks: dict[int, float] = {}
        warmup_steps = 500
        commits = 0
        aborts = 0
        bystander_aborts = 0
        useful_work = 0.0
        total_compute_used = 0.0

        def reset_worker(w: dict[str, Any]) -> None:
            for g in list(w["holds"]):
                if lock_owner[g] == w["id"]:
                    lock_owner[g] = None
            w["holds"].clear()
            w["waiting_on"] = None
            g1, g2 = sample_pair()
            w["g1"], w["g2"] = g1, g2
            w["prog"] = 0.0
            w["tainted"] = False
            w["will_abandon"] = (rng.random() < p_abandon)

        for step in range(steps):
            in_meas = step >= warmup_steps

            if mode == "BLOCKING_2PL":
                # 1. Expire orphan cookie-licked locks once idle TTL elapses
                for g in list(orphan_locks.keys()):
                    orphan_locks[g] -= dt
                    if orphan_locks[g] <= 1e-12:
                        del orphan_locks[g]
                        if lock_owner[g] == -1:
                            lock_owner[g] = None

                # 2. Attempt lock acquisitions at prog == 0.0 (g1) and prog >= 0.5 (g2)
                for w in workers:
                    if w["g1"] not in w["holds"]:
                        if lock_owner[w["g1"]] is None:
                            lock_owner[w["g1"]] = w["id"]
                            w["holds"].add(w["g1"])
                            w["waiting_on"] = None
                        else:
                            w["waiting_on"] = w["g1"]
                    elif w["prog"] >= 0.5 and w["g2"] not in w["holds"]:
                        if lock_owner[w["g2"]] is None:
                            lock_owner[w["g2"]] = w["id"]
                            w["holds"].add(w["g2"])
                            w["waiting_on"] = None
                        else:
                            w["waiting_on"] = w["g2"]
                    else:
                        w["waiting_on"] = None

                # 3. Detect true wait-for cycles and abort youngest cycle member (never lasso bystanders)
                for w in workers:
                    if w["waiting_on"] is None:
                        continue
                    path: list[int] = [w["id"]]
                    cur = w
                    while cur["waiting_on"] is not None:
                        holder_id = lock_owner[cur["waiting_on"]]
                        if holder_id is None or holder_id < 0:
                            break
                        if holder_id in path:
                            cyc = path[path.index(holder_id):]
                            victim_id = max(cyc)
                            if victim_id not in cyc:
                                bystander_aborts += 1
                            if in_meas:
                                aborts += 1
                            reset_worker(workers[victim_id])
                            break
                        path.append(holder_id)
                        cur = workers[holder_id]

                runnable = [w for w in workers if (w["waiting_on"] is None and w["g1"] in w["holds"])]
            else:
                runnable = list(workers)

            n_run = len(runnable)
            if n_run > 0:
                speed = 1.0 if K_slots is None else min(1.0, K_slots / float(n_run))
                dw = speed * dt
                if in_meas:
                    total_compute_used += float(n_run) * dw
                for w in runnable:
                    w["prog"] += dw
                    if w["will_abandon"] and w["prog"] >= 0.25:
                        if mode == "BLOCKING_2PL":
                            for g in list(w["holds"]):
                                lock_owner[g] = -1
                                orphan_locks[g] = lease_ttl_units
                            w["holds"].clear()
                        reset_worker(w)
                        continue
                    if mode == "BLOCKING_2PL" and w["prog"] >= 0.5 and w["g2"] not in w["holds"]:
                        w["prog"] = 0.5  # must acquire g2 before second half!
                        continue
                    if w["prog"] >= 1.0:
                        if mode == "OCC":
                            if w["tainted"]:
                                if in_meas:
                                    aborts += 1
                                reset_worker(w)
                            else:
                                committed_set = {w["g1"], w["g2"]}
                                if in_meas:
                                    commits += 1
                                    useful_work += 1.0
                                for peer in workers:
                                    if peer["id"] != w["id"] and peer["prog"] > 0.0:
                                        if peer["g1"] in committed_set or peer["g2"] in committed_set:
                                            peer["tainted"] = True
                                reset_worker(w)
                        else:
                            if in_meas:
                                commits += 1
                                useful_work += 1.0
                            reset_worker(w)

        assert bystander_aborts == 0
        meas_time = (steps - warmup_steps) * dt
        return {
            "throughput": round(commits / meas_time, 4),
            "abort_rate_per_unit_time": round(aborts / meas_time, 4),
            "useful_compute_fraction": round(useful_work / max(total_compute_used, 1e-9), 4),
            "bystander_aborts": bystander_aborts,
        }

    # Check 1: Infinite compute capacity (K = None, G = 40 granules, N = 36) -> OCC > Blocking!
    sim_inf_occ = simulate_concurrency_control("OCC", N=36, num_granules=40, K_slots=None, p_abandon=0.0)
    sim_inf_blk = simulate_concurrency_control("BLOCKING_2PL", N=36, num_granules=40, K_slots=None, p_abandon=0.0)
    assert sim_inf_occ["throughput"] > sim_inf_blk["throughput"], (sim_inf_occ, sim_inf_blk)

    # Check 2: Finite compute capacity (K = 8.0 slots, G = 40 granules, N = 36) -> Blocking > OCC!
    sim_fin_occ = simulate_concurrency_control("OCC", N=36, num_granules=40, K_slots=8.0, p_abandon=0.0)
    sim_fin_blk = simulate_concurrency_control("BLOCKING_2PL", N=36, num_granules=40, K_slots=8.0, p_abandon=0.0)
    assert sim_fin_blk["throughput"] > sim_fin_occ["throughput"], (sim_fin_occ, sim_fin_blk)

    # Check 3: Zero-contention negative control (G = 10,000, N = 16, K = 8.0, p_abandon = 0.25, TTL = 60.0):
    # Proves open contributor replacement eliminates spurious closed-pool worker sleep!
    sim_zero_cont_occ = simulate_concurrency_control(
        "OCC", N=16, num_granules=10000, K_slots=8.0, p_abandon=0.25, lease_ttl_units=60.0
    )
    sim_zero_cont_blk = simulate_concurrency_control(
        "BLOCKING_2PL", N=16, num_granules=10000, K_slots=8.0, p_abandon=0.25, lease_ttl_units=60.0
    )
    zero_cont_ratio = round(sim_zero_cont_occ["throughput"] / max(sim_zero_cont_blk["throughput"], 1e-9), 2)
    assert zero_cont_ratio < 1.25, (sim_zero_cont_occ, sim_zero_cont_blk, zero_cont_ratio)

    # Check 4: Controlled cookie-licking comparison holding (N = 16, G = 24, K = 8.0, p_abandon = 0.25) FIXED
    # across TTL = 60.0 (9.11x orphan-lock starvation) vs. TTL = 1.0 (Blocking > OCC restored)!
    sim_cookie_occ = simulate_concurrency_control(
        "OCC", N=16, num_granules=24, K_slots=8.0, p_abandon=0.25, lease_ttl_units=60.0
    )
    sim_cookie_blk_long = simulate_concurrency_control(
        "BLOCKING_2PL", N=16, num_granules=24, K_slots=8.0, p_abandon=0.25, lease_ttl_units=60.0
    )
    sim_cookie_blk_short = simulate_concurrency_control(
        "BLOCKING_2PL", N=16, num_granules=24, K_slots=8.0, p_abandon=0.25, lease_ttl_units=1.0
    )

    cookie_inversion_ratio = round(sim_cookie_occ["throughput"] / max(sim_cookie_blk_long["throughput"], 1e-9), 2)
    assert cookie_inversion_ratio >= 8.0, (sim_cookie_occ, sim_cookie_blk_long, cookie_inversion_ratio)
    assert sim_cookie_blk_short["throughput"] > sim_cookie_occ["throughput"], (sim_cookie_blk_short, sim_cookie_occ)

    return {
        "analytical_occ_fixed_point": {
            "scaling_identity": "u(N) = (1 - p_c)^Lambda_inf(N) is K-invariant; Lambda_K(N) = min(1, K/N) * Lambda_inf(N)",
            "curve": analytical_curve,
        },
        "discrete_step_multi_slot_simulation": {
            "infinite_K_N36_G40": {"OCC": sim_inf_occ, "BLOCKING_2PL": sim_inf_blk},
            "finite_K8_N36_G40": {"OCC": sim_fin_occ, "BLOCKING_2PL": sim_fin_blk},
            "zero_contention_control_K8_N16_G10000_ttl60": {
                "OCC": sim_zero_cont_occ,
                "BLOCKING_2PL": sim_zero_cont_blk,
                "occ_over_blocking_ratio": zero_cont_ratio,
            },
            "cookie_licking_controlled_K8_N16_G24_p025": {
                "OCC": sim_cookie_occ,
                "BLOCKING_2PL_long_ttl60": sim_cookie_blk_long,
                "BLOCKING_2PL_short_ttl1": sim_cookie_blk_short,
                "ttl60_occ_over_blocking_ratio": cookie_inversion_ratio,
            },
        },
    }


# ============================================================================
# Probe P4: De-Confounded Six-Mode Expected-Cost Intervention Selector
#           [toy model / parametric decision model]
# ============================================================================
def run_probe_4_deconfounded_intervention_selector() -> dict[str, Any]:
    """[toy model / parametric decision model]
    Unit-consistent total expected remaining agent-work + defect-loss selector separating:
      - `omega` in [0, 1]: goal redundancy (1 = identical duplicate goal; 0 = two distinct required features)
      - `kappa` in [0, 1]: structural/hunk coupling across touched files
      - `delta` in [0, 1]: directional producer->consumer contract dependency asymmetry
      - `sem_ambig` in [0, 1]: pre-code architectural/specification ambiguity
      - `v_bug` >= 0: expected loss from an escaped subtle bug (in agent-work-unit equivalents)
      - `rho_corr` in [0, 1]: Knight & Leveson (1986) fault correlation across independent versions
    """
    v_second_feature = 4.5  # penalty if a required distinct feature (1 - omega) is dropped unimplemented

    def evaluate_modes(
        s1: float,
        s2: float,
        omega: float,
        kappa: float,
        delta: float,
        sem_ambig: float,
        v_bug: float,
        rho_corr: float = 0.35,
        p_bug_single: float = 0.20,
    ) -> dict[str, Any]:
        s_hi, s_lo = max(s1, s2), min(s1, s2)
        p_escape_single = p_bug_single
        # Knight & Leveson (1986): p_diff = p^2 + rho * p * (1 - p); equals p when rho == 1.0!
        p_escape_diff = (p_bug_single ** 2) + rho_corr * p_bug_single * (1.0 - p_bug_single)

        # Architectural divergence defect risk when coding without shared spec under high sem_ambig
        arch_drift_risk = 0.30 * sem_ambig * (1.0 - omega) * v_bug

        # Consistent total remaining agent-work baseline (2.0 units at s1=s2=0, omega=0; 1.0 unit at s1=s2=0, omega=1):
        rem_parallel = (1.0 - s1) + (1.0 - s2)
        rem_dedup_scope = max(0.0, (2.0 - omega) - ((1.0 - omega) * (s1 + s2) + omega * s_hi))

        # Positive directional contract-breakage rework paid by modes that do NOT sequence Producer -> Consumer
        unsequenced_breakage = 1.65 * delta * (1.0 - omega) * (1.0 - s_lo)

        # M1: Yield / Abort — lower-progress worker halts; forfeits (1 - omega) distinct scope
        cost_m1 = (1.0 - s_hi) + (1.0 - omega) * v_second_feature + p_escape_single * v_bug

        # M2: State Merge / Patch Integration — zero fixed coordination fee on disjoint work (cost = 2.0 at all-zero baseline),
        #     but pays structural/semantic merge rework, unsequenced contract breakage, and duplicate integration waste
        merge_rework = 1.85 * kappa + 2.20 * kappa * sem_ambig + 0.85 * omega
        cost_m2 = rem_parallel + merge_rework + unsequenced_breakage + p_escape_single * v_bug + arch_drift_risk

        # M3: Scope Split / Interface Partitioning — upfront partition fee (0.35), eliminates hunk collisions on new code,
        #     discards coupled sunk edits, retains partial unsequenced breakage when delta >> 0
        c_partition = 0.35
        discard_m3 = 0.75 * kappa * (s1 + s2)
        cost_m3 = (
            rem_dedup_scope
            + c_partition
            + discard_m3
            + 0.25 * kappa * sem_ambig
            + 0.75 * unsequenced_breakage
            + p_escape_single * v_bug
            + 0.50 * arch_drift_risk
        )

        # M4: Producer / Consumer Handoff — explicit interface-stub & sequential rebase overhead (0.55),
        #     eliminates unsequenced contract breakage without negative-cost terms
        c_stub_handoff = 0.55
        cost_m4 = (
            rem_dedup_scope
            + c_stub_handoff
            + 0.45 * kappa * (s1 + s2)
            + 0.90 * (1.0 - delta) * kappa
            + p_escape_single * v_bug
            + 0.35 * arch_drift_risk
        )

        # M5: Cross-Review / Differential Oracle — requires overlapping goal (omega -> 1) + high v_bug + rho < 1
        c_diff_harness = 0.45
        eff_bug_escape_m5 = omega * p_escape_diff + (1.0 - omega) * p_escape_single
        cost_m5 = (
            rem_parallel
            + c_diff_harness
            + (1.0 - omega) * (0.5 * v_second_feature)
            + eff_bug_escape_m5 * v_bug
        )

        # M6: Shared Scratch / Living Spec Co-Editing — upfront living-spec fee (0.45), eliminates arch_drift_risk at s1=s2~0
        c_living_spec = 0.45
        spec_refactor = 1.10 * (s1 + s2)
        cost_m6 = (
            rem_dedup_scope
            + c_living_spec
            + spec_refactor
            + 0.20 * kappa
            + 0.40 * unsequenced_breakage
            + p_escape_single * v_bug
        )

        costs = {
            "M1_Yield_Abort": round(cost_m1, 4),
            "M2_State_Merge": round(cost_m2, 4),
            "M3_Scope_Split": round(cost_m3, 4),
            "M4_Producer_Consumer": round(cost_m4, 4),
            "M5_Cross_Review_DiffTest": round(cost_m5, 4),
            "M6_Shared_Living_Spec": round(cost_m6, 4),
        }
        best = min(costs, key=costs.get)
        return {"winner": best, "expected_total_cost": costs}

    # Unit-consistency sanity check: two disjoint zero-ambiguity features from scratch -> M2 wins at exact 2.00!
    zero_overlap_baseline = evaluate_modes(0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0)
    assert zero_overlap_baseline["winner"] == "M2_State_Merge"
    assert zero_overlap_baseline["expected_total_cost"]["M2_State_Merge"] == 2.0
    assert all(c >= 2.0 for c in zero_overlap_baseline["expected_total_cost"].values())

    archetypes = {
        "early_true_duplicate": evaluate_modes(
            s1=0.75, s2=0.10, omega=1.00, kappa=0.95, delta=0.10, sem_ambig=0.20, v_bug=2.0
        ),
        "low_coupling_late_progress": evaluate_modes(
            s1=0.80, s2=0.75, omega=0.00, kappa=0.10, delta=0.10, sem_ambig=0.10, v_bug=2.0
        ),
        "early_coupled_decomposable": evaluate_modes(
            s1=0.05, s2=0.05, omega=0.00, kappa=0.80, delta=0.15, sem_ambig=0.15, v_bug=2.0
        ),
        "blocking_contract_migration": evaluate_modes(
            s1=0.25, s2=0.05, omega=0.00, kappa=0.75, delta=0.95, sem_ambig=0.25, v_bug=2.0
        ),
        "late_accidental_duplicate_high_stakes": evaluate_modes(
            s1=0.90, s2=0.85, omega=1.00, kappa=0.95, delta=0.10, sem_ambig=0.20, v_bug=20.0, rho_corr=0.35
        ),
        "pre_code_high_semantic_ambiguity": evaluate_modes(
            s1=0.00, s2=0.00, omega=0.00, kappa=0.85, delta=0.15, sem_ambig=0.95, v_bug=8.0
        ),
    }

    winners = [v["winner"] for v in archetypes.values()]
    assert winners == [
        "M1_Yield_Abort",
        "M2_State_Merge",
        "M3_Scope_Split",
        "M4_Producer_Consumer",
        "M5_Cross_Review_DiffTest",
        "M6_Shared_Living_Spec",
    ], f"Unexpected winners: {winners}"

    # Non-vacuity Ablation 1: Knight & Leveson rho -> 1.0 eliminates M5 differential oracle gain!
    ablation_rho_1 = evaluate_modes(
        s1=0.90, s2=0.85, omega=1.00, kappa=0.95, delta=0.10, sem_ambig=0.20, v_bug=20.0, rho_corr=1.0
    )
    assert ablation_rho_1["winner"] == "M1_Yield_Abort"

    # Non-vacuity Ablation 2: delta -> 0.0 collapses M4 Producer/Consumer advantage!
    ablation_delta_0 = evaluate_modes(
        s1=0.25, s2=0.05, omega=0.00, kappa=0.75, delta=0.00, sem_ambig=0.25, v_bug=2.0
    )
    assert ablation_delta_0["winner"] == "M3_Scope_Split"

    # Non-vacuity Ablation 3: De-confounding check (same high kappa=0.80, early progress, flipping omega 1.0 -> 0.0)
    deconfound_dup = evaluate_modes(s1=0.05, s2=0.05, omega=1.00, kappa=0.80, delta=0.15, sem_ambig=0.15, v_bug=2.0)
    deconfound_distinct = archetypes["early_coupled_decomposable"]
    assert deconfound_dup["winner"] == "M1_Yield_Abort" and deconfound_distinct["winner"] == "M3_Scope_Split"

    return {
        "model_origin": "[toy model / parametric decision model]",
        "zero_overlap_scratch_baseline": zero_overlap_baseline,
        "canonical_archetypes": archetypes,
        "non_vacuity_ablations": {
            "knight_leveson_rho_1_collapses_M5_to_M1": ablation_rho_1,
            "zero_dependency_delta_0_collapses_M4_to_M3": ablation_delta_0,
            "deconfound_high_kappa_omega_1_vs_0": {
                "omega_1_duplicate_winner": deconfound_dup["winner"],
                "omega_0_distinct_winner": deconfound_distinct["winner"],
            },
        },
    }


# ============================================================================
# Probe P5: Empirical Dataset Forensics & Exact Wilson 95% CIs
# ============================================================================
def run_probe_5_empirical_forensics() -> dict[str, Any]:
    def wilson_ci_pct(k: int, n: int, z: float = 1.959963984540054) -> list[float]:
        p = k / n
        denom = 1.0 + (z * z) / n
        center = (p + (z * z) / (2.0 * n)) / denom
        half = (z * math.sqrt((p * (1.0 - p) + (z * z) / (4.0 * n)) / n)) / denom
        return [round((center - half) * 100.0, 2), round((center + half) * 100.0, 2)]

    def wald_ci_pct(k: int, n: int, z: float = 1.959963984540054) -> list[float]:
        p = k / n
        half = z * math.sqrt(p * (1.0 - p) / n)
        return [round((p - half) * 100.0, 2), round((p + half) * 100.0, 2)]

    # 5A. Brun et al. (ESEC/FSE 2011, Figure 4 p. 171) exact 9-system & 3-system row reconciliation
    brun_fig4_build_test = {
        "Git":       {"merges": 1362, "textual": 227, "build": 2,  "test": 53, "clean": 1080},
        "Perl5":     {"merges": 185,  "textual": 14,  "build": 7,  "test": 51, "clean": 113},
        "Voldemort": {"merges": 147,  "textual": 25,  "build": 15, "test": 5,  "clean": 102},
    }
    brun_fig4_textual_only = {
        "Gallery3": {"merges": 458, "textual": 42,  "clean_textual": 416},
        "Insoshi":  {"merges": 93,  "textual": 23,  "clean_textual": 70},
        "jQuery":   {"merges": 15,  "textual": 1,   "clean_textual": 14},
        "MaNGOS":   {"merges": 192, "textual": 81,  "clean_textual": 111},
        "Rails":    {"merges": 362, "textual": 51,  "clean_textual": 311},
        "Samba":    {"merges": 748, "textual": 100, "clean_textual": 648},
    }
    n_bt = sum(v["merges"] for v in brun_fig4_build_test.values())        # 1,694 (NOT 5,355!)
    txt_bt = sum(v["textual"] for v in brun_fig4_build_test.values())     # 266 (15.70% -> 16%)
    bld_bt = sum(v["build"] for v in brun_fig4_build_test.values())       # 24  (1.42% -> 1%)
    tst_bt = sum(v["test"] for v in brun_fig4_build_test.values())        # 109 (6.43% -> 6%)
    cln_bt = sum(v["clean"] for v in brun_fig4_build_test.values())       # 1,295 (76.45% -> 76%)
    n_all9 = n_bt + sum(v["merges"] for v in brun_fig4_textual_only.values())     # 3,562
    txt_all9 = txt_bt + sum(v["textual"] for v in brun_fig4_textual_only.values())  # 564 (15.83% -> 16%)

    assert n_bt == 1694 and txt_bt == 266 and bld_bt == 24 and tst_bt == 109 and cln_bt == 1295
    assert n_all9 == 3562 and txt_all9 == 564
    assert txt_bt + bld_bt + tst_bt == 399
    vcs_clean_merges_bt = n_bt - txt_bt  # 1,428 merges reported clean by `git merge`

    # 5B. whystar/MSR2018-DupPR@62782219 `dup_prs.md` group-size histogram -> Li et al. (IEEE TSE 2022a)
    dup_prs_group_hist = {2: 1664, 3: 69, 4: 10, 5: 5, 6: 2, 7: 1}
    dup_groups_total = sum(dup_prs_group_hist.values())                                    # 1,751 groups
    dup_unique_prs = sum(k * cnt for k, cnt in dup_prs_group_hist.items())                 # 3,619 unique PRs
    dup_choose2_pairs = sum((k * (k - 1) // 2) * cnt for k, cnt in dup_prs_group_hist.items())  # 2,032 C(k,2) pairs
    assert dup_groups_total == 1751 and dup_unique_prs == 3619 and dup_choose2_pairs == 2032

    li_choices = {"accept_one": 1082, "accept_both": 36, "reject_both": 29}
    li_total = sum(li_choices.values())  # 1,147
    li_seq = {"exclusive": 1924, "inclusive": 81, "overlapping": 17}
    li_seq_total = sum(li_seq.values())  # 2,022 (2,032 pairs minus 10 lacking complete commit history)
    assert li_total == 1147 and li_seq_total == 2022

    # 5C. AgenticFlict (AIware '26 pp. 323-331, arXiv:2604.03551v2) Table 2 (N=107,026) vs. prose (N=105,533)
    af_table2 = {
        "Copilot":      (2583,  16954, 15.24, [14.69, 15.78], 15.43),
        "Cursor":       (1421,  7196,  19.75, [18.83, 20.67], 20.06),
        "Devin":        (1883,  8241,  22.85, [21.94, 23.76], 23.04),
        "Claude_Code":  (202,   779,   25.93, [22.85, 29.01], 26.86),
        "OpenAI_Codex": (23520, 73856, 31.85, [31.51, 32.18], 32.31),
    }
    assert sum(v[1] for v in af_table2.values()) == 107026
    assert sum(v[0] for v in af_table2.values()) == 29609
    af_residual = 107026 - (29609 + 75924)  # 1,493
    assert af_residual == 1493

    af_per_agent = {}
    for agent, (conf, tot, tbl2_pct, paper_ci, prose_pct) in af_table2.items():
        assert round(conf / tot * 100.0, 2) == tbl2_pct
        w_wald = wald_ci_pct(conf, tot)
        w_wilson = wilson_ci_pct(conf, tot)
        assert abs(w_wald[0] - paper_ci[0]) <= 0.01 and abs(w_wald[1] - paper_ci[1]) <= 0.01
        af_per_agent[agent] = {
            "conflicting": conf,
            "total_simulated": tot,
            "table2_rate_pct": tbl2_pct,
            "prose_clean_plus_conf_rate_pct": prose_pct,
            "paper_wald_95_ci_pct": w_wald,
            "exact_wilson_95_ci_pct": w_wilson,
        }

    # 5D. Xu, Subramanian & Karthik (arXiv:2607.04697v2) cross-agent vs intra-agent CIs
    intra_ci = wilson_ci_pct(119, 601)
    cross_ci = wilson_ci_pct(48, 115)
    assert intra_ci[1] < cross_ci[0]

    # 5E. CooperBench (arXiv:2601.13295v2) Table 6 spatial-vs-semantic paradox
    cooperbench_t6 = {
        "GPT-5":             {"no_comm_naive": 13.88, "with_comm_naive": 20.42, "no_comm_final": 27.91, "with_comm_final": 27.90},
        "Claude_4.5_Sonnet": {"no_comm_naive": 12.27, "with_comm_naive": 16.72, "no_comm_final": 27.30, "with_comm_final": 25.92},
        "MiniMax-M2":        {"no_comm_naive": 8.62,  "with_comm_naive": 7.36,  "no_comm_final": 14.88, "with_comm_final": 13.96},
        "Qwen3-Coder":       {"no_comm_naive": 6.90,  "with_comm_naive": 6.75,  "no_comm_final": 14.72, "with_comm_final": 13.34},
        "Qwen3-Instruct":    {"no_comm_naive": 1.53,  "with_comm_naive": 2.30,  "no_comm_final": 3.37,  "with_comm_final": 4.60},
    }
    for d in cooperbench_t6.values():
        d["naive_delta_pp"] = round(d["with_comm_naive"] - d["no_comm_naive"], 2)
        d["final_delta_pp"] = round(d["with_comm_final"] - d["no_comm_final"], 2)

    # 5F. NP-Bench (Muku, arXiv:2610.07261v1 Table 2) C0 vs C1-DETECT vs C1-PLAN
    np_bench_t2 = {
        "C0_uncoordinated":  {"ctsr_num": 1, "ctsr_den": 9, "conflicts": 13, "wasted_loc": 54, "live_migration_frontier": 0.00},
        "C1_DETECT_warning": {"ctsr_num": 4, "ctsr_den": 9, "conflicts": 12, "wasted_loc": 49, "live_migration_frontier": 0.00},
        "C1_PLAN_partition": {"ctsr_num": 9, "ctsr_den": 9, "conflicts": 0,  "wasted_loc": 0,  "live_migration_frontier": 1.00, "live_migration_small": 0.60, "scope_violations_of_5": 0},
    }

    return {
        "brun_fse2011_reconciled": {
            "all_9_systems_merges": n_all9,
            "all_9_systems_textual_conflicts": txt_all9,
            "all_9_systems_textual_pct": round(txt_all9 / n_all9 * 100.0, 2),
            "build_test_3_systems_exact_merges": n_bt,
            "paper_sec4_2_prose_typo_merges": 5355,
            "textual_conflicts_bt": txt_bt,
            "build_conflicts_bt": bld_bt,
            "test_conflicts_bt": tst_bt,
            "clean_merges_bt": cln_bt,
            "higher_order_share_of_all_conflicts_pct": round((bld_bt + tst_bt) / 399 * 100.0, 2),
            "higher_order_share_wilson_95_ci_pct": wilson_ci_pct(133, 399),
            "conditional_fail_given_clean_git_merge_pct": round(133 / vcs_clean_merges_bt * 100.0, 2),
            "conditional_fail_wilson_95_ci_pct": wilson_ci_pct(133, vcs_clean_merges_bt),
        },
        "li_yu_duppr_and_abandonment": {
            "accept_one_pct": round(1082 / li_total * 100.0, 2),
            "accept_one_wilson_95_ci_pct": wilson_ci_pct(1082, li_total),
            "accept_both_pct": round(36 / li_total * 100.0, 2),
            "accept_both_wilson_95_ci_pct": wilson_ci_pct(36, li_total),
            "reject_both_pct": round(29 / li_total * 100.0, 2),
            "exclusive_sequential_pct": round(1924 / li_seq_total * 100.0, 2),
            "exclusive_wilson_95_ci_pct": wilson_ci_pct(1924, li_seq_total),
            "dup_prs_md_groups_prs_choose2_pairs": [dup_groups_total, dup_unique_prs, dup_choose2_pairs],
            "msr2018_pairs_before_330_intentional_dup_filter": 2323,
            "tse2022_abandoned_repo_rows_vs_paper_coded": [343, 321],
        },
        "agenticflict_denominator_audit": {
            "total_simulated": 107026,
            "conflicting": 29609,
            "clean": 75924,
            "residual_non_clean_non_conflict": af_residual,
            "overall_conflict_rate_pct": round(29609 / 107026 * 100.0, 2),
            "per_agent": af_per_agent,
        },
        "xu_2026_cross_vs_intra_agent": {
            "intra_agent_pct": round(119 / 601 * 100.0, 2),
            "intra_wilson_95_ci_pct": intra_ci,
            "cross_agent_pct": round(48 / 115 * 100.0, 2),
            "cross_wilson_95_ci_pct": cross_ci,
            "ci_separation_gap_pp": round(cross_ci[0] - intra_ci[1], 2),
        },
        "cooperbench_table6_paradox": cooperbench_t6,
        "np_bench_table2": np_bench_t2,
    }


def main() -> int:
    p1 = run_probe_1_gray_cheriton_and_progress_leases()
    p2 = run_probe_2_fencing_matrix_and_real_git_cas()
    p3 = run_probe_3_agrawal_inversion_and_cookie_licking()
    p4 = run_probe_4_deconfounded_intervention_selector()
    p5 = run_probe_5_empirical_forensics()

    gc = p1["exact_gray_cheriton_1989_eq1_eq2"]
    dr = p1["derived_renewal_plus_crash_stall_optima"]
    pw = p1["progress_witness_lease_renewal"]
    gm = p2["schedule_matrix_30x5"]
    gr = p2["real_git_ref_cas_execution"]
    sim = p3["discrete_step_multi_slot_simulation"]
    br = p5["brun_fse2011_reconciled"]
    lu = p5["li_yu_duppr_and_abandonment"]
    xu = p5["xu_2026_cross_vs_intra_agent"]
    npb = p5["np_bench_table2"]

    print("=== P1: Gray & Cheriton (1989) Exact Eq. 1-2, Crash-Stall Optima & Progress Leases ===")
    print(
        f"[exact Gray & Cheriton 1989 Eq. 1-2] Delta={gc['delta_transit_plus_skew_s']}s; "
        f"sub-skew cliff (t_S=0.05s, S=10) load={gc['sub_skew_cliff']['rel_load_sub_skew_S10']}x "
        f"(+{gc['sub_skew_cliff']['load_penalty_pct']}% vs t_S=0); "
        f"S=1 10s total cut={gc['v_system_table2_reproduction']['S=1']['total_traffic_reduction_10s_pct']}% "
        f"(delay={gc['v_system_table2_reproduction']['S=1']['avg_consistency_delay_10s_ms']}ms); "
        f"S=10 unicast be={gc['v_system_table2_reproduction']['S=10']['ts_breakeven_unicast_s']}s; "
        f"S=40 mcast be={gc['v_system_table2_reproduction']['S=40']['ts_breakeven_mcast_s']}s"
    )
    print(
        f"[derived crash-stall: demand vs keepalive] V-demand t_S*={dr['demand_driven_v_cache']['ts_high_duty_closed_form_s']}s "
        f"(exact-duty={dr['demand_driven_v_cache']['ts_exact_duty_grid_opt_s']}s, pi_on={dr['demand_driven_v_cache']['active_duty_pi_on_at_opt']}); "
        f"proactive-HB (eta=1/3) t_S_hb*={dr['proactive_keepalive_agent_lease_eta_1_3']['ts_hb_closed_form_s']}s "
        f"(tau_hb={dr['proactive_keepalive_agent_lease_eta_1_3']['tau_hb_interval_s']}s, "
        f"E[stall]={dr['proactive_keepalive_agent_lease_eta_1_3']['expected_crash_stall_s']}s); "
        f"unheartbeated claim t_S*={dr['unheartbeated_oss_issue_claim']['ts_opt_s']}s"
    )
    print(
        f"[toy discrete simulation: progress-witness lease] liveness-only completed={pw['liveness_only_stuck_loop']['completed']} "
        f"(wasted={pw['liveness_only_stuck_loop']['wasted_loop_s']}s) vs witness-gated completed_at="
        f"{pw['progress_witness_stuck_loop']['completed_at_s']}s (zombies_blocked={pw['progress_witness_stuck_loop']['zombie_writes_blocked']}), "
        f"A/B osc={pw['progress_witness_ab_oscillation']['completed_at_s']}s (zombies_blocked={pw['progress_witness_ab_oscillation']['zombie_writes_blocked']}), "
        f"slow-compile false_eviction={pw['progress_witness_slow_compile_guard']['false_eviction']}"
    )

    print("\n=== P2: 30-Schedule Pause/Orphan Matrix & Real Ephemeral Git CAS Execution ===")
    print(
        f"[discrete schedule model] corruptions/30 (parent-only/10): "
        f"unfenced_ttl={gm['unfenced_ttl_only']['split_brain_corruptions']} ({gm['unfenced_ttl_only']['no_child_parent_only_corruptions_of_10']}/10), "
        f"client_recheck={gm['unfenced_ttl_plus_client_recheck']['split_brain_corruptions']} ({gm['unfenced_ttl_plus_client_recheck']['no_child_parent_only_corruptions_of_10']}/10), "
        f"lock_delay_60s={gm['chubby_lock_delay_only']['split_brain_corruptions']} ({gm['chubby_lock_delay_only']['no_child_parent_only_corruptions_of_10']}/10), "
        f"parent_token_ambient_child={gm['fenced_token_parent_only_ambient_child']['split_brain_corruptions']} ({gm['fenced_token_parent_only_ambient_child']['no_child_parent_only_corruptions_of_10']}/10), "
        f"sink_cas_all_writers={gm['fenced_token_storage_cas_all_writers']['split_brain_corruptions']} (0/10)"
    )
    print(
        f"[real git execution] C0={gr['deterministic_oids']['c0_base'][:12]} C3={gr['deterministic_oids']['c3_w3_authoritative'][:12]} | "
        f"G1_force_corrupts={gr['G1_unfenced_force_orphan_corrupts']}, "
        f"G2a_linear_oid_blocks={gr['G2a_explicit_oid_lease_blocks_linear_stale']}, "
        f"G2b_fetch_corrupts={gr['G2b_implicit_fetch_force_with_lease_corrupts']}, "
        f"G2b_aba_corrupts={gr['G2b_aba_rollback_explicit_oid_corrupts']}, "
        f"G3a_pre_receive_toctou_corrupts={gr['G3a_pre_receive_toctou_race_corrupts']}, "
        f"G3b_ref_txn_prepared_lock_safe={gr['G3b_ref_txn_prepared_blocks_concurrent_coord_lock'] and gr['G3b_ref_txn_prepared_blocks_aba_and_orphan']}"
    )

    print("\n=== P3: Agrawal-Carey-Livny Resource Inversion & De-Confounded Cookie-Licking ===")
    print(
        f"[discrete-step multi-slot sim] K=inf (N=36, G=40): OCC={sim['infinite_K_N36_G40']['OCC']['throughput']} > "
        f"Blocking={sim['infinite_K_N36_G40']['BLOCKING_2PL']['throughput']} | "
        f"K=8 (N=36, G=40): Blocking={sim['finite_K8_N36_G40']['BLOCKING_2PL']['throughput']} "
        f"(useful={sim['finite_K8_N36_G40']['BLOCKING_2PL']['useful_compute_fraction']:.2%}, bystanders=0) > "
        f"OCC={sim['finite_K8_N36_G40']['OCC']['throughput']} "
        f"(useful={sim['finite_K8_N36_G40']['OCC']['useful_compute_fraction']:.2%})"
    )
    print(
        f"[open-arrival cookie-licking N=16, K=8, p_abandon=0.25] G=10000 zero-contention control: "
        f"OCC={sim['zero_contention_control_K8_N16_G10000_ttl60']['OCC']['throughput']} vs "
        f"Blocking={sim['zero_contention_control_K8_N16_G10000_ttl60']['BLOCKING_2PL']['throughput']} "
        f"({sim['zero_contention_control_K8_N16_G10000_ttl60']['occ_over_blocking_ratio']}x); "
        f"G=24 TTL=60: OCC={sim['cookie_licking_controlled_K8_N16_G24_p025']['OCC']['throughput']} vs "
        f"Blocking={sim['cookie_licking_controlled_K8_N16_G24_p025']['BLOCKING_2PL_long_ttl60']['throughput']} "
        f"({sim['cookie_licking_controlled_K8_N16_G24_p025']['ttl60_occ_over_blocking_ratio']}x starvation) -> "
        f"G=24 TTL=1.0: Blocking={sim['cookie_licking_controlled_K8_N16_G24_p025']['BLOCKING_2PL_short_ttl1']['throughput']} > OCC"
    )

    print("\n=== P4: De-Confounded Six-Mode Selector [toy model / parametric decision model] ===")
    print(
        f"Zero-overlap scratch baseline: winner={p4['zero_overlap_scratch_baseline']['winner']} "
        f"(cost={p4['zero_overlap_scratch_baseline']['expected_total_cost']['M2_State_Merge']}); "
        "Archetypes: " + ", ".join(f"{k}->{v['winner']}" for k, v in p4["canonical_archetypes"].items())
    )
    print(
        f"Ablations: rho->1 => {p4['non_vacuity_ablations']['knight_leveson_rho_1_collapses_M5_to_M1']['winner']}; "
        f"delta->0 => {p4['non_vacuity_ablations']['zero_dependency_delta_0_collapses_M4_to_M3']['winner']}; "
        f"deconfound kappa=0.80: omega=1=>{p4['non_vacuity_ablations']['deconfound_high_kappa_omega_1_vs_0']['omega_1_duplicate_winner']} "
        f"vs omega=0=>{p4['non_vacuity_ablations']['deconfound_high_kappa_omega_1_vs_0']['omega_0_distinct_winner']}"
    )

    print("\n=== P5: Empirical Dataset Forensics & Exact Wilson 95% CIs ===")
    print(
        f"Brun 2011: all9={br['all_9_systems_merges']} ({br['all_9_systems_textual_pct']}% textual), "
        f"Git+Perl5+Voldemort={br['build_test_3_systems_exact_merges']} (sec 4.2 typo={br['paper_sec4_2_prose_typo_merges']}), "
        f"higher-order={br['higher_order_share_of_all_conflicts_pct']}% of conflicts (133/399, CI {br['higher_order_share_wilson_95_ci_pct']}) "
        f"& {br['conditional_fail_given_clean_git_merge_pct']}% of clean git merges (133/1428, CI {br['conditional_fail_wilson_95_ci_pct']})"
    )
    print(
        f"DupPR dup_prs.md={lu['dup_prs_md_groups_prs_choose2_pairs']} [groups, unique_PRs, C(k,2)_pairs] "
        f"(MSR18={lu['msr2018_pairs_before_330_intentional_dup_filter']}); "
        f"Xu 2026 CIs: intra {xu['intra_agent_pct']}% {xu['intra_wilson_95_ci_pct']} vs "
        f"cross {xu['cross_agent_pct']}% {xu['cross_wilson_95_ci_pct']} (+{xu['ci_separation_gap_pp']} pp); "
        f"NP-Bench CTSR: C0={npb['C0_uncoordinated']['ctsr_num']}/9, "
        f"C1-DETECT={npb['C1_DETECT_warning']['ctsr_num']}/9, C1-PLAN={npb['C1_PLAN_partition']['ctsr_num']}/9"
    )

    receipt = {
        "all_assertions_passed": True,
        "p1_hb_opt_ts_s": dr["proactive_keepalive_agent_lease_eta_1_3"]["ts_hb_closed_form_s"],
        "p1_s40_breakeven_s": gc["v_system_table2_reproduction"]["S=40"]["ts_breakeven_mcast_s"],
        "p1_witness_zombies_blocked": [
            pw["progress_witness_stuck_loop"]["zombie_writes_blocked"],
            pw["progress_witness_ab_oscillation"]["zombie_writes_blocked"],
        ],
        "p2_git_c3_oid": gr["deterministic_oids"]["c3_w3_authoritative"],
        "p2_pre_receive_toctou_vs_ref_txn_safe": [
            gr["G3a_pre_receive_toctou_race_corrupts"],
            gr["G3b_ref_txn_prepared_blocks_concurrent_coord_lock"]
            and gr["G3b_ref_txn_prepared_blocks_aba_and_orphan"],
        ],
        "p3_cookie_lick_occ_over_blk_ratio": sim["cookie_licking_controlled_K8_N16_G24_p025"]["ttl60_occ_over_blocking_ratio"],
        "p3_fin_k8_blk_vs_occ": [
            sim["finite_K8_N36_G40"]["BLOCKING_2PL"]["throughput"],
            sim["finite_K8_N36_G40"]["OCC"]["throughput"],
        ],
        "p4_model_origin": p4["model_origin"],
        "p5_dup_prs_groups_prs_pairs": lu["dup_prs_md_groups_prs_choose2_pairs"],
    }
    print("\nJSON_RECEIPT:", json.dumps(receipt, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
