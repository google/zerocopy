#!/usr/bin/env python3
"""Deterministic verification probe suite for concurrent agent fleet coordination economics.

Covers four primary-source-grounded verification modules using only the Python 3.10+
standard library (zero external dependencies, zero filesystem writes, 100% deterministic
stdout across `python3 -I -B` invocations):

  1. `sweep_admission_vs_async`:
     - Exact Pollaczek-Khinchine M/G/1 admission gate residence time L_sync(Lambda)
     - Closed-form vs. common-random-number Monte Carlo verification of Pi_none, Pi_sync,
       Pi_async (both `hard_abort` and CoAgent one-way `<_sigma` `advisory_triage`),
       and the Two-Tier Composite (`FastSyncStructural` + `AsyncSemantic`) policy under
       both calibrated equal recall (`TwoTier_eq`, 90.00%) and complementary cascading
       recall (`TwoTier_casc`, 93.99%)
     - Exact token-scarcity scalarization thresholds omega_tok^* (`SyncGate` vs `AsyncAdv`,
       `SyncGate` vs `TwoTier_eq`, and `SyncGate` vs `TwoTier_casc`), plus `fast_ast_gate`
       dominance over equal-recall `TwoTier_eq` at omega_tok = 0
     - Endogenous shared finite M/G/1 semantic-judge queueing comparison (`SyncGate` vs
       `AsyncAdv` vs `TwoTier_eq` vs `TwoTier_casc` when Tier-1 sheds 8.14% of arrivals)
     - Symmetric bilateral advisory livelock negative control (CoAgent arXiv:2606.15376v1
       Section 5.2 Figure 2) vs. 1-pass DAG convergence under `<_sigma`
     - Reconciled latency and compute Neyman-Pearson likelihood-ratio floors LR_+^*

  2. `sim_hedging_mgk` & `knight_leveson_redux_voting`:
     - (2A) Deterministic heapq M/G/k discrete-event simulator separating power-of-two
       load balancing (`single_jsq2` vs. `single_random1`) from true task redundancy
       (`hedged_p95_jsq2` vs. `single_jsq2`: -47.8% P99 at rho = 0.80), verifying
       Vulimiri et al. (2013) Theorem 1 crossover rho* = 1/(d+1) = 1/3 on uncancelled
       Exponential, pure Z = 0 Gardner et al. (2017b) S&X Uniform[1, 2] instability
       over n_jobs = 16,000 even under instant Cancel-on-Complete, static-timeout
       retry-storm collapse, and active-queue filtering on `riq_d2`
     - (2B) Exact reproduction of Knight & Leveson (1986) and Ron, Baudry, & Monperrus
       (arXiv:2606.20158v1; ASSERT-KTH/Knight-Leveson-Redux@546a59d35e2fda7da070f0e6015523f4ca44a649)
       48-version / 10^6-input campaign z-statistics, all C(48,3) = 17,296 majority-vote
       triples, pairwise exact phi = 1.0 counts, and Eckhardt & Lee (1985) /
       Littlewood & Miller (1989) input-difficulty covariance decomposition

  3. `sim_nk_networks_and_recombinant`:
     - (3A) Exact enumerable NK landscapes (N = 10, 2^10 = 1,024 states, K = 0 vs. K = 5,
       Lazer & Friedman 2007 r^8 normalization) verifying short-run fully_connected
       imitation lead vs. long-run ring_lattice and periodic_pod_migration victory
     - (3B) Symmetric synchronous Derex & Boyd (2016) 2-trajectory (A1->A2->A3,
       B1->B2->B3 => R4 recombination) cumulative innovation state machine with uniform
       tie-breaking and unfinished-lineage refinement demonstrating fully_connected
       monoculture lock-in vs. isolated_pods_with_migration recombinant breakthrough

  4. `eval_usl_knees_and_codahale_fit`:
     - Exact reproduction of Gunther (2008) / Schwartz (2015) / codahale/usl@513b3f33
       USL capacity C(N), retrograde optimum N_opt = sqrt((1 - alpha)/beta), Little's Law
       folded-back nose curve R(N), two-branched R_-(X)/R_+(X), domain guards (`kappa == 0`
       Amdahl L'Hopital limit, `sigma >= 1`, `n_total < k_pods`), and algebraic exposure +
       repair of the upstream sign inversion in Schwartz Eq. 9 / codahale/usl `model.go:63-66`
       `ThroughputAtLatency` (`-kappa + sigma` vs. exact `+kappa - sigma`)
     - K-way worktree/pod sharding retrograde-knee shift
     - Exact Levenberg-Marquardt + linearized OLS parameter recovery on codahale/usl's
       32-point Cisco fixture (`model_test.go:159-192`) and noisy fleet telemetry,
       closing the control loop to Agrawal, Carey, & Livny (1987) multiprogramming caps
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from enum import Enum
import heapq
import itertools
import json
import math
import random
from typing import Sequence


BANNERS = {
    "analytical": "[exact analytical / derived calculation]",
    "pinned_algo": "[exact reproduction of pinned algorithm]",
    "simulation": "[controlled discrete-event / Monte Carlo simulation]",
}


# ============================================================================
# PROBE 1: Synchronous Admission Control vs. Ordered Async Advisory Economics
# ============================================================================


class FalsePositiveMode(Enum):
    HARD_ABORT = "hard_abort"
    ADVISORY_TRIAGE = "advisory_triage"


@dataclass(frozen=True)
class GateConfig:
    mean_service_s: float
    rho_gate: float
    cs2: float  # squared coefficient of variation Var(S)/E[S]^2

    def residence_time_s(self) -> float:
        """Exact Pollaczek-Khinchine M/G/1 mean gate residence time (queueing + service)."""
        if not (0.0 <= self.rho_gate < 1.0):
            raise ValueError(f"Unstable M/G/1 gate utilization: {self.rho_gate}")
        if self.mean_service_s < 0.0 or self.cs2 < 0.0:
            raise ValueError("Service time and C_s^2 must be non-negative")
        queue_factor = (self.rho_gate * (1.0 + self.cs2)) / (2.0 * (1.0 - self.rho_gate))
        return self.mean_service_s * (1.0 + queue_factor)


@dataclass(frozen=True)
class OverlapScenario:
    name: str
    p_overlap: float
    work_s: float
    tau_merge_s: float
    c_merge_tok: float
    gate: GateConfig
    c_chk_tok: float
    dt_async_s: float
    tpr: float
    fpr: float
    tau_sw_s: float
    c_sw_tok: float
    tau_fp_sync_s: float
    c_fp_sync_tok: float
    tau_inspect_s: float = 1.5
    c_inspect_tok: float = 2.0
    p_misjudge: float = 0.05  # CoAgent arXiv:2606.15376v1 Section 7.2 residual (~5%)


@dataclass(frozen=True)
class PolicyMetrics:
    excess_latency_s: float
    excess_compute_tok: float

    def objective(self, omega_tok: float) -> float:
        return self.excess_latency_s + omega_tok * self.excess_compute_tok


def eval_admission_analytic(
    sc: OverlapScenario,
    fp_mode: FalsePositiveMode = FalsePositiveMode.ADVISORY_TRIAGE,
    dt_async_override_s: float | None = None,
) -> dict[str, PolicyMetrics]:
    """Closed-form expected excess latency and token/compute waste over an oracle."""
    p = sc.p_overlap
    w = sc.work_s
    dt_a = sc.dt_async_s if dt_async_override_s is None else dt_async_override_s

    # 1. No-Check
    dt_none = p * (w + sc.tau_merge_s)
    dc_none = p * (w + sc.c_merge_tok)

    # 2. Synchronous Check-Before-Start (Admission Gate)
    l_sync = sc.gate.residence_time_s()
    dt_sync = (
        l_sync
        + p * (1.0 - sc.tpr) * (w + sc.tau_merge_s)
        + (1.0 - p) * sc.fpr * sc.tau_fp_sync_s
    )
    dc_sync = (
        sc.c_chk_tok
        + p * (1.0 - sc.tpr) * (w + sc.c_merge_tok)
        + (1.0 - p) * sc.fpr * sc.c_fp_sync_tok
    )

    # 3. Optimistic Start + Ordered (<_sigma) Async Advisory
    psi_tp = min(w + sc.tau_merge_s, dt_a + sc.tau_sw_s)
    kappa_tp = min(w + sc.c_merge_tok, dt_a + sc.c_sw_tok)
    eta = 1.0 if dt_a < w else 0.0
    if fp_mode is FalsePositiveMode.HARD_ABORT:
        tau_fp_async = dt_a + sc.tau_sw_s
        c_fp_async = dt_a + sc.c_sw_tok
    elif fp_mode is FalsePositiveMode.ADVISORY_TRIAGE:
        tau_fp_async = sc.tau_inspect_s + sc.p_misjudge * (dt_a + sc.tau_sw_s)
        c_fp_async = sc.c_inspect_tok + sc.p_misjudge * (dt_a + sc.c_sw_tok)
    else:
        raise AssertionError(f"Unhandled FalsePositiveMode: {fp_mode}")

    dt_async = (
        p * sc.tpr * psi_tp
        + p * (1.0 - sc.tpr) * (w + sc.tau_merge_s)
        + (1.0 - p) * sc.fpr * eta * tau_fp_async
    )
    dc_async = (
        sc.c_chk_tok
        + p * sc.tpr * kappa_tp
        + p * (1.0 - sc.tpr) * (w + sc.c_merge_tok)
        + (1.0 - p) * sc.fpr * eta * c_fp_async
    )

    return {
        "none": PolicyMetrics(dt_none, dc_none),
        "sync": PolicyMetrics(dt_sync, dc_sync),
        "async": PolicyMetrics(dt_async, dc_async),
    }


def eval_two_tier_composite_analytic(
    sc: OverlapScenario,
    tier1_gate: GateConfig,
    struct_share_of_overlaps: float = 0.42,  # Xu et al. arXiv:2607.04697v2: 41.9% structural
    tpr_tier1_on_struct: float = 0.95,
    fpr_tier1: float = 0.002,
    c_chk_tier1_tok: float = 0.05,
    equal_total_recall: bool = False,
    endogenous_tier2_judge: GateConfig | None = None,
) -> PolicyMetrics:
    """Two-Tier Composite: sub-second sync structural index + async semantic `<_sigma` advisory.

    When `equal_total_recall=True` (`TwoTier_eq`), conditional Tier-2 recall on residual
    overlaps is calibrated so combined Tier-1 + Tier-2 recall matches `sc.tpr` exactly
    (e.g. 90.00%), isolating pure scheduling/filtering gains without free recall inflation.
    When `equal_total_recall=False` (`TwoTier_casc`), Tier-2 achieves `sc.tpr` on residual
    overlaps (93.99% combined recall when Tier-1 catches 39.9% and Tier-2 catches 90% of
    the remaining 60.1%).
    When `endogenous_tier2_judge` is supplied, Tier-2's semantic judge is modeled as a
    shared finite M/G/1 queue whose utilization scales by `pass_t1_total` (reflecting
    Tier-1 arrival shedding before semantic inspection).
    """
    p = sc.p_overlap
    w = sc.work_s
    l_t1 = tier1_gate.residence_time_s()

    tpr_t1_overall = struct_share_of_overlaps * tpr_tier1_on_struct
    if equal_total_recall:
        if sc.tpr < tpr_t1_overall:
            raise ValueError(
                f"Target equal recall {sc.tpr:.4f} is below Tier-1 recall {tpr_t1_overall:.4f}"
            )
        tpr_t2_cond = (
            (sc.tpr - tpr_t1_overall) / (1.0 - tpr_t1_overall)
            if tpr_t1_overall < 1.0
            else 1.0
        )
    else:
        tpr_t2_cond = sc.tpr

    # True overlaps split into structural/explicit-path overlaps vs semantic-only overlaps.
    p_struct = p * struct_share_of_overlaps
    p_sem = p * (1.0 - struct_share_of_overlaps)

    # Tier 1 catches p_struct * tpr_tier1_on_struct before execution (0 worker tokens).
    p_residual_overlap = p_struct * (1.0 - tpr_tier1_on_struct) + p_sem
    p_clean_pass_t1 = (1.0 - p) * (1.0 - fpr_tier1)
    p_clean_fp_t1 = (1.0 - p) * fpr_tier1
    pass_t1_total = p_residual_overlap + p_clean_pass_t1

    if endogenous_tier2_judge is not None:
        t2_gate = GateConfig(
            mean_service_s=endogenous_tier2_judge.mean_service_s,
            rho_gate=endogenous_tier2_judge.rho_gate * pass_t1_total,
            cs2=endogenous_tier2_judge.cs2,
        )
        dt_t2 = t2_gate.residence_time_s()
    else:
        dt_t2 = sc.dt_async_s

    psi_tp = min(w + sc.tau_merge_s, dt_t2 + sc.tau_sw_s)
    kappa_tp = min(w + sc.c_merge_tok, dt_t2 + sc.c_sw_tok)
    eta = 1.0 if dt_t2 < w else 0.0
    tau_fp_async = sc.tau_inspect_s + sc.p_misjudge * (dt_t2 + sc.tau_sw_s)
    c_fp_async = sc.c_inspect_tok + sc.p_misjudge * (dt_t2 + sc.c_sw_tok)

    dt = (
        l_t1
        + p_clean_fp_t1 * sc.tau_fp_sync_s
        + p_residual_overlap * tpr_t2_cond * psi_tp
        + p_residual_overlap * (1.0 - tpr_t2_cond) * (w + sc.tau_merge_s)
        + p_clean_pass_t1 * sc.fpr * eta * tau_fp_async
    )
    dc = (
        c_chk_tier1_tok
        + pass_t1_total * sc.c_chk_tok
        + p_clean_fp_t1 * sc.c_fp_sync_tok
        + p_residual_overlap * tpr_t2_cond * kappa_tp
        + p_residual_overlap * (1.0 - tpr_t2_cond) * (w + sc.c_merge_tok)
        + p_clean_pass_t1 * sc.fpr * eta * c_fp_async
    )
    return PolicyMetrics(dt, dc)


def neyman_pearson_lr_floors(
    sc: OverlapScenario, fp_mode: FalsePositiveMode = FalsePositiveMode.ADVISORY_TRIAGE
) -> tuple[float, float, float]:
    """Return (actual LR_+ = TPR/FPR, latency floor LR_+^{*,lat}, compute floor LR_+^{*,tok}).

    - Latency floor LR_+^{*,lat}: minimum TPR/FPR for Pi_async to beat Pi_none on excess
      wall-clock latency (out-of-band check incurs 0 worker latency; false positives apply
      only when eta = I(dt_async < W) == 1).
    - Compute floor LR_+^{*,tok}: minimum TPR/FPR for Pi_async to beat Pi_none on excess
      compute/tokens, which must BOTH outweigh false-positive waste AND amortize `c_chk_tok`
      paid on 100% of arrivals.
    """
    lr_actual = math.inf if sc.fpr <= 0.0 else (sc.tpr / sc.fpr)
    eta = 1.0 if sc.dt_async_s < sc.work_s else 0.0
    saved_lat_tp = (sc.work_s + sc.tau_merge_s) - min(
        sc.work_s + sc.tau_merge_s, sc.dt_async_s + sc.tau_sw_s
    )
    saved_tok_tp = (sc.work_s + sc.c_merge_tok) - min(
        sc.work_s + sc.c_merge_tok, sc.dt_async_s + sc.c_sw_tok
    )
    if fp_mode is FalsePositiveMode.HARD_ABORT:
        tau_fp = sc.dt_async_s + sc.tau_sw_s
        c_fp = sc.dt_async_s + sc.c_sw_tok
    else:
        tau_fp = sc.tau_inspect_s + sc.p_misjudge * (sc.dt_async_s + sc.tau_sw_s)
        c_fp = sc.c_inspect_tok + sc.p_misjudge * (sc.dt_async_s + sc.c_sw_tok)

    if sc.p_overlap <= 0.0 or saved_lat_tp <= 0.0:
        lr_star_lat = math.inf
    elif eta == 0.0:
        lr_star_lat = 0.0
    else:
        lr_star_lat = ((1.0 - sc.p_overlap) / sc.p_overlap) * (eta * tau_fp / saved_lat_tp)

    if sc.p_overlap <= 0.0 or saved_tok_tp <= 0.0 or sc.fpr <= 0.0:
        lr_star_tok = math.inf
    else:
        lr_star_tok = ((1.0 - sc.p_overlap) / sc.p_overlap) * (eta * c_fp / saved_tok_tp) + (
            sc.c_chk_tok / (sc.p_overlap * sc.fpr * saved_tok_tp)
        )

    return lr_actual, lr_star_lat, lr_star_tok


def _draw_mg1_service(rng: random.Random, mean_s: float, cs2: float) -> float:
    """Two-point / Erlang-2 / Hyperexponential service time matching exact (mean_s, C_s^2)."""
    if cs2 <= 1e-12:
        return mean_s
    if abs(cs2 - 0.5) < 1e-9:
        # Erlang-2: sum of two Exp(2 / mean_s) draws has exact mean_s and C_s^2 = 0.5
        rate = 2.0 / mean_s
        return rng.expovariate(rate) + rng.expovariate(rate)
    if abs(cs2 - 1.0) < 1e-9:
        return rng.expovariate(1.0 / mean_s)
    # Balanced-means 2-phase hyperexponential H_2 matching exact (mean_s, cs2 > 1)
    assert cs2 > 1.0
    p_branch = 0.5 * (1.0 + math.sqrt((cs2 - 1.0) / (cs2 + 1.0)))
    if rng.random() < p_branch:
        return rng.expovariate(2.0 * p_branch / mean_s)
    return rng.expovariate(2.0 * (1.0 - p_branch) / mean_s)


def sim_mg1_gate_residence(gate: GateConfig, n_arrivals: int, warmup: int, seed: int) -> float:
    """Lindley FCFS M/G/1 discrete-event simulation verifying Pollaczek-Khinchine L_sync."""
    if gate.rho_gate <= 0.0:
        return gate.mean_service_s
    rng = random.Random(seed)
    lam = gate.rho_gate / gate.mean_service_s
    wait = 0.0
    prev_wait = 0.0
    prev_svc = 0.0
    total_res = 0.0
    for idx in range(n_arrivals):
        inter = rng.expovariate(lam)
        svc = _draw_mg1_service(rng, gate.mean_service_s, gate.cs2)
        if idx > 0:
            wait = max(0.0, prev_wait + prev_svc - inter)
        prev_wait, prev_svc = wait, svc
        if idx >= warmup:
            total_res += wait + svc
    return total_res / (n_arrivals - warmup)


def sim_admission_monte_carlo(
    sc: OverlapScenario,
    n_trials: int,
    seed: int,
    l_sync_sim: float,
) -> dict[str, PolicyMetrics]:
    """Stratified-CRN Monte Carlo verification of Pi_none, Pi_sync, and Pi_async."""
    rng = random.Random(seed)
    sum_t = {"none": 0.0, "sync": 0.0, "async_triage": 0.0, "async_abort": 0.0}
    sum_c = {"none": 0.0, "sync": 0.0, "async_triage": 0.0, "async_abort": 0.0}

    for idx in range(n_trials):
        u_ov = (idx + rng.random()) / n_trials
        u_det = rng.random()
        u_mis = rng.random()
        is_overlap = u_ov < sc.p_overlap
        if is_overlap:
            detected = u_det < sc.tpr
            sum_t["none"] += sc.work_s + sc.tau_merge_s
            sum_c["none"] += sc.work_s + sc.c_merge_tok

            sum_t["sync"] += l_sync_sim + (0.0 if detected else (sc.work_s + sc.tau_merge_s))
            sum_c["sync"] += sc.c_chk_tok + (0.0 if detected else (sc.work_s + sc.c_merge_tok))

            tp_lat = (
                min(sc.work_s + sc.tau_merge_s, sc.dt_async_s + sc.tau_sw_s)
                if detected
                else (sc.work_s + sc.tau_merge_s)
            )
            tp_tok = (
                min(sc.work_s + sc.c_merge_tok, sc.dt_async_s + sc.c_sw_tok)
                if detected
                else (sc.work_s + sc.c_merge_tok)
            )
            sum_t["async_triage"] += tp_lat
            sum_c["async_triage"] += sc.c_chk_tok + tp_tok
            sum_t["async_abort"] += tp_lat
            sum_c["async_abort"] += sc.c_chk_tok + tp_tok
        else:
            false_pos = u_det < sc.fpr
            sum_t["sync"] += l_sync_sim + (sc.tau_fp_sync_s if false_pos else 0.0)
            sum_c["sync"] += sc.c_chk_tok + (sc.c_fp_sync_tok if false_pos else 0.0)

            sum_c["async_triage"] += sc.c_chk_tok
            sum_c["async_abort"] += sc.c_chk_tok
            if false_pos and sc.dt_async_s < sc.work_s:
                sum_t["async_abort"] += sc.dt_async_s + sc.tau_sw_s
                sum_c["async_abort"] += sc.dt_async_s + sc.c_sw_tok
                misjudged = u_mis < sc.p_misjudge
                sum_t["async_triage"] += sc.tau_inspect_s + (
                    (sc.dt_async_s + sc.tau_sw_s) if misjudged else 0.0
                )
                sum_c["async_triage"] += sc.c_inspect_tok + (
                    (sc.dt_async_s + sc.c_sw_tok) if misjudged else 0.0
                )

    inv = 1.0 / n_trials
    return {k: PolicyMetrics(sum_t[k] * inv, sum_c[k] * inv) for k in sum_t}


def sim_coagent_bilateral_livelock_control(max_steps: int = 64) -> dict[str, object]:
    """Reproduce CoAgent (arXiv:2606.15376v1 Section 5.2 Fig. 2) unordered broadcast livelock."""
    x_bi, y_bi = 0.5, 0.5
    pending_notify_a1 = True  # y changed after A1 read y=1.0
    pending_notify_a2 = True  # x changed after A2 read x=1.0
    steps_bi = 0
    while (pending_notify_a1 or pending_notify_a2) and steps_bi < max_steps:
        steps_bi += 1
        if steps_bi % 2 == 1 and pending_notify_a1:
            pending_notify_a1 = False
            x_bi = y_bi / 2.0
            pending_notify_a2 = True
        elif pending_notify_a2:
            pending_notify_a2 = False
            y_bi = x_bi / 2.0
            pending_notify_a1 = True
    bilateral_converged = not (pending_notify_a1 or pending_notify_a2)

    # MTPO ordered one-way advisory (sigma_1 < sigma_2: notifications flow ONLY 1 -> 2)
    x_mtpo = 0.5
    y_mtpo = 0.5
    heals_mtpo = 0
    notify_1_to_2 = True
    while notify_1_to_2:
        notify_1_to_2 = False
        heals_mtpo += 1
        y_mtpo = x_mtpo / 2.0

    assert not bilateral_converged and steps_bi == max_steps
    assert heals_mtpo == 1 and (x_mtpo, y_mtpo) == (0.5, 0.25)
    return {
        "bilateral_terminated": bilateral_converged,
        "bilateral_steps_hit_cap": steps_bi,
        "bilateral_state_at_cap": (x_bi, y_bi),
        "mtpo_heals": heals_mtpo,
        "mtpo_final_state": (x_mtpo, y_mtpo),
    }


def run_probe_1() -> dict[str, object]:
    tier1_fast_index = GateConfig(mean_service_s=0.15, rho_gate=0.10, cs2=0.5)
    scenarios = [
        OverlapScenario(
            name="fast_ast_gate",
            p_overlap=0.10,
            work_s=300.0,
            tau_merge_s=60.0,
            c_merge_tok=60.0,
            gate=GateConfig(mean_service_s=0.50, rho_gate=0.20, cs2=0.5),
            c_chk_tok=0.10,
            dt_async_s=25.0,
            tpr=0.90,
            fpr=0.02,
            tau_sw_s=5.0,
            c_sw_tok=5.0,
            tau_fp_sync_s=10.0,
            c_fp_sync_tok=2.0,
        ),
        OverlapScenario(
            name="uncongested_llm_gate",
            p_overlap=0.10,
            work_s=300.0,
            tau_merge_s=60.0,
            c_merge_tok=60.0,
            gate=GateConfig(mean_service_s=25.0, rho_gate=0.30, cs2=1.0),
            c_chk_tok=4.0,
            dt_async_s=25.0,
            tpr=0.90,
            fpr=0.02,
            tau_sw_s=5.0,
            c_sw_tok=5.0,
            tau_fp_sync_s=10.0,
            c_fp_sync_tok=2.0,
        ),
        OverlapScenario(
            name="congested_llm_gate",
            p_overlap=0.20,
            work_s=300.0,
            tau_merge_s=60.0,
            c_merge_tok=60.0,
            gate=GateConfig(mean_service_s=25.0, rho_gate=0.85, cs2=1.5),
            c_chk_tok=4.0,
            dt_async_s=25.0,
            tpr=0.90,
            fpr=0.02,
            tau_sw_s=5.0,
            c_sw_tok=5.0,
            tau_fp_sync_s=10.0,
            c_fp_sync_tok=2.0,
        ),
        OverlapScenario(
            name="low_p_high_fpr_trap",
            p_overlap=0.01,
            work_s=300.0,
            tau_merge_s=60.0,
            c_merge_tok=60.0,
            gate=GateConfig(mean_service_s=2.0, rho_gate=0.30, cs2=1.0),
            c_chk_tok=1.0,
            dt_async_s=25.0,
            tpr=0.80,
            fpr=0.20,
            tau_sw_s=5.0,
            c_sw_tok=5.0,
            tau_fp_sync_s=35.0,
            c_fp_sync_tok=15.0,
            tau_inspect_s=22.0,
            c_inspect_tok=12.0,
        ),
    ]

    rows = []
    max_mc_err = 0.0
    max_pk_rel_err = 0.0
    for idx, sc in enumerate(scenarios):
        an_triage = eval_admission_analytic(sc, FalsePositiveMode.ADVISORY_TRIAGE)
        an_abort = eval_admission_analytic(sc, FalsePositiveMode.HARD_ABORT)
        two_tier_eq = eval_two_tier_composite_analytic(
            sc, tier1_fast_index, equal_total_recall=True
        )
        two_tier_casc = eval_two_tier_composite_analytic(
            sc, tier1_fast_index, equal_total_recall=False
        )
        l_sync_pk = sc.gate.residence_time_s()
        l_sync_sim = sim_mg1_gate_residence(
            sc.gate, n_arrivals=45_000, warmup=3_000, seed=20_000 + idx
        )
        pk_rel_err = abs(l_sync_sim - l_sync_pk) / l_sync_pk
        max_pk_rel_err = max(max_pk_rel_err, pk_rel_err)
        assert pk_rel_err < 0.06, f"Pollaczek-Khinchine M/G/1 mismatch on {sc.name}: {pk_rel_err:.4f}"

        mc = sim_admission_monte_carlo(
            sc, n_trials=20_000, seed=10_000 + idx, l_sync_sim=l_sync_pk
        )
        for key_an, key_mc in [
            ("none", "none"),
            ("sync", "sync"),
            ("async", "async_triage"),
        ]:
            err = abs(an_triage[key_an].excess_latency_s - mc[key_mc].excess_latency_s)
            max_mc_err = max(max_mc_err, err)
            assert err < 0.85, f"MC mismatch on {sc.name}/{key_an}: {err:.4f}"

        err_abort = abs(an_abort["async"].excess_latency_s - mc["async_abort"].excess_latency_s)
        max_mc_err = max(max_mc_err, err_abort)
        assert err_abort < 0.85

        lr_actual, lr_star_lat, lr_star_tok = neyman_pearson_lr_floors(
            sc, FalsePositiveMode.ADVISORY_TRIAGE
        )
        # Verify exact algebraic equivalence of both latency & compute LR_+^* floors
        assert (lr_actual > lr_star_lat) == (
            an_triage["async"].excess_latency_s < an_triage["none"].excess_latency_s
        )
        assert (lr_actual > lr_star_tok) == (
            an_triage["async"].excess_compute_tok < an_triage["none"].excess_compute_tok
        )

        rows.append(
            {
                "name": sc.name,
                "l_sync_s": l_sync_pk,
                "l_sync_sim_s": l_sync_sim,
                "none_lat_s": an_triage["none"].excess_latency_s,
                "none_tok": an_triage["none"].excess_compute_tok,
                "sync_lat_s": an_triage["sync"].excess_latency_s,
                "async_triage_lat_s": an_triage["async"].excess_latency_s,
                "async_abort_lat_s": an_abort["async"].excess_latency_s,
                "two_tier_eq_lat_s": two_tier_eq.excess_latency_s,
                "two_tier_casc_lat_s": two_tier_casc.excess_latency_s,
                "sync_tok": an_triage["sync"].excess_compute_tok,
                "async_triage_tok": an_triage["async"].excess_compute_tok,
                "two_tier_eq_tok": two_tier_eq.excess_compute_tok,
                "two_tier_casc_tok": two_tier_casc.excess_compute_tok,
                "lr_plus": lr_actual,
                "lr_star_lat": lr_star_lat,
                "lr_star_tok": lr_star_tok,
            }
        )

    # Guard check on neyman_pearson_lr_floors when dt_async >= work_s + tau_merge_s (saved_per_tp == 0)
    sc_late = OverlapScenario(
        name="late_advisory_guard",
        p_overlap=0.10,
        work_s=300.0,
        tau_merge_s=60.0,
        c_merge_tok=60.0,
        gate=GateConfig(1.0, 0.1, 1.0),
        c_chk_tok=1.0,
        dt_async_s=370.0,
        tpr=0.90,
        fpr=0.02,
        tau_sw_s=5.0,
        c_sw_tok=5.0,
        tau_fp_sync_s=5.0,
        c_fp_sync_tok=2.0,
    )
    _, lr_lat_late, lr_tok_late = neyman_pearson_lr_floors(sc_late)
    assert math.isinf(lr_lat_late) and math.isinf(lr_tok_late)

    by_name = {r["name"]: r for r in rows}

    # 1. Fast AST gate beats BOTH AsyncAdv AND equal-recall TwoTier_eq across all omega_tok >= 0!
    #    (Deferring 60.1% of overlaps to a 25s async tier hurts when a 0.59s sync AST gate
    #    already achieves 90% recall; TwoTier wins on fast_ast_gate ONLY when Tier-2 adds
    #    complementary semantic recall `two_tier_casc`!)
    fast = by_name["fast_ast_gate"]
    assert fast["sync_lat_s"] < fast["two_tier_eq_lat_s"] < fast["async_triage_lat_s"]
    assert fast["sync_tok"] < fast["two_tier_eq_tok"] < fast["async_triage_tok"]
    assert fast["two_tier_casc_lat_s"] < fast["sync_lat_s"]

    # 2. Uncongested & congested slow LLM gates lose on latency to AsyncAdv, TwoTier_eq, and TwoTier_casc
    uncong = by_name["uncongested_llm_gate"]
    assert (
        uncong["two_tier_casc_lat_s"]
        < uncong["two_tier_eq_lat_s"]
        < uncong["async_triage_lat_s"]
        < uncong["none_lat_s"]
        < uncong["sync_lat_s"]
    )
    cong = by_name["congested_llm_gate"]
    assert (
        cong["two_tier_casc_lat_s"]
        < cong["two_tier_eq_lat_s"]
        < cong["async_triage_lat_s"]
        < cong["none_lat_s"]
        < cong["sync_lat_s"]
    )
    for r in rows:
        assert r["async_triage_lat_s"] < r["async_abort_lat_s"]

    # 3. Neyman-Pearson base-rate trap: LR_+ violates BOTH latency & compute floors => NoCheck wins
    trap = by_name["low_p_high_fpr_trap"]
    assert trap["lr_plus"] < trap["lr_star_lat"] and trap["lr_plus"] < trap["lr_star_tok"]
    assert trap["none_lat_s"] < trap["async_triage_lat_s"] < trap["sync_lat_s"]
    assert trap["none_tok"] < trap["async_triage_tok"] and trap["none_tok"] < trap["sync_tok"]

    # 4. Exact omega_tok crossover thresholds on `uncongested_llm_gate`:
    sc_tok = scenarios[1]
    an_tok = eval_admission_analytic(sc_tok, FalsePositiveMode.ADVISORY_TRIAGE)
    tt_eq_tok = eval_two_tier_composite_analytic(sc_tok, tier1_fast_index, equal_total_recall=True)
    tt_casc_tok = eval_two_tier_composite_analytic(
        sc_tok, tier1_fast_index, equal_total_recall=False
    )
    # SyncGate burns 7.636 tok vs TwoTier_casc 7.742 tok < TwoTier_eq 9.048 tok < AsyncAdv 10.363 tok
    assert (
        an_tok["sync"].excess_compute_tok
        < tt_casc_tok.excess_compute_tok
        < tt_eq_tok.excess_compute_tok
        < an_tok["async"].excess_compute_tok
    )
    omega_star_single = (
        an_tok["sync"].excess_latency_s - an_tok["async"].excess_latency_s
    ) / (an_tok["async"].excess_compute_tok - an_tok["sync"].excess_compute_tok)
    omega_star_tt_eq = (
        an_tok["sync"].excess_latency_s - tt_eq_tok.excess_latency_s
    ) / (tt_eq_tok.excess_compute_tok - an_tok["sync"].excess_compute_tok)
    omega_star_tt_casc = (
        an_tok["sync"].excess_latency_s - tt_casc_tok.excess_latency_s
    ) / (tt_casc_tok.excess_compute_tok - an_tok["sync"].excess_compute_tok)
    assert 12.0 < omega_star_single < 12.3
    assert 24.0 < omega_star_tt_eq < 24.5
    assert 330.0 < omega_star_tt_casc < 360.0

    omega_sweep = []
    for omega in (0.0, 10.0, 15.0, 30.0, 400.0):
        scores = {
            "none": an_tok["none"].objective(omega),
            "sync_llm": an_tok["sync"].objective(omega),
            "async_triage": an_tok["async"].objective(omega),
            "two_tier_eq": tt_eq_tok.objective(omega),
            "two_tier_casc": tt_casc_tok.objective(omega),
        }
        winner_single = min(("none", "sync_llm", "async_triage"), key=lambda k: scores[k])
        winner_eq_recall = min(
            ("none", "sync_llm", "async_triage", "two_tier_eq"), key=lambda k: scores[k]
        )
        winner_all = min(scores, key=lambda k: scores[k])
        omega_sweep.append(
            {
                "omega_tok": omega,
                "winner_single_tier": winner_single,
                "winner_equal_recall": winner_eq_recall,
                "winner_overall": winner_all,
                "scores": scores,
            }
        )
    # Verify exact regime transitions across omega_tok:
    assert omega_sweep[0]["winner_single_tier"] == "async_triage"   # w=0 < 12.15
    assert omega_sweep[1]["winner_single_tier"] == "async_triage"   # w=10 < 12.15
    assert omega_sweep[2]["winner_single_tier"] == "sync_llm"       # w=15 > 12.15
    assert omega_sweep[2]["winner_equal_recall"] == "two_tier_eq"   # w=15 < 24.22
    assert omega_sweep[3]["winner_equal_recall"] == "sync_llm"      # w=30 > 24.22
    assert omega_sweep[3]["winner_overall"] == "two_tier_casc"      # w=30 < 334.0
    assert omega_sweep[4]["winner_overall"] == "sync_llm"           # w=400 > 334.0!

    # 5. Endogenous shared finite M/G/1 semantic judge comparison on `congested_llm_gate`
    sc_cong = scenarios[2]
    l_judge_full = sc_cong.gate.residence_time_s()  # 202.0833s at rho = 0.85
    an_cong_shared = eval_admission_analytic(
        sc_cong, FalsePositiveMode.ADVISORY_TRIAGE, dt_async_override_s=l_judge_full
    )
    pass_t1_cong = sc_cong.p_overlap * (1.0 - 0.42 * 0.95) + (1.0 - sc_cong.p_overlap) * (
        1.0 - 0.002
    )
    rho_tier2_cong = sc_cong.gate.rho_gate * pass_t1_cong
    dt_tier2_cong = GateConfig(
        sc_cong.gate.mean_service_s, rho_tier2_cong, sc_cong.gate.cs2
    ).residence_time_s()
    tt_eq_cong_shared = eval_two_tier_composite_analytic(
        sc_cong,
        tier1_fast_index,
        equal_total_recall=True,
        endogenous_tier2_judge=sc_cong.gate,
    )
    tt_casc_cong_shared = eval_two_tier_composite_analytic(
        sc_cong,
        tier1_fast_index,
        equal_total_recall=False,
        endogenous_tier2_judge=sc_cong.gate,
    )
    assert (
        tt_casc_cong_shared.excess_latency_s
        < tt_eq_cong_shared.excess_latency_s
        < an_cong_shared["async"].excess_latency_s
        < an_cong_shared["none"].excess_latency_s
        < an_cong_shared["sync"].excess_latency_s
    )

    livelock = sim_coagent_bilateral_livelock_control(max_steps=64)
    return {
        "scenarios": rows,
        "max_mc_abs_err_s": max_mc_err,
        "max_pk_rel_err": max_pk_rel_err,
        "omega_thresholds": {
            "omega_star_single": omega_star_single,
            "omega_star_two_tier_eq": omega_star_tt_eq,
            "omega_star_two_tier_casc": omega_star_tt_casc,
        },
        "omega_sweep": omega_sweep,
        "shared_mg1_judge_congested": {
            "rho_full": sc_cong.gate.rho_gate,
            "dt_async_full_s": l_judge_full,
            "rho_tier2": rho_tier2_cong,
            "dt_async_tier2_s": dt_tier2_cong,
            "sync_lat_s": an_cong_shared["sync"].excess_latency_s,
            "async_shared_lat_s": an_cong_shared["async"].excess_latency_s,
            "two_tier_eq_shared_lat_s": tt_eq_cong_shared.excess_latency_s,
            "two_tier_casc_shared_lat_s": tt_casc_cong_shared.excess_latency_s,
        },
        "livelock_control": livelock,
    }


# ============================================================================
# PROBE 2A: Heap-Based M/G/k Hedging, JSQ-2 Separation & Pure Z=0 S&X Blowup
# ============================================================================


class RedundancyPolicy(Enum):
    SINGLE_RANDOM1 = "single_random1"
    SINGLE_JSQ2 = "single_jsq2"
    EAGER_NOCANCEL_D2 = "eager_nocancel_d2"
    EAGER_COC_D2 = "eager_coc_d2"
    TIED_COS_D2 = "tied_cos_d2"
    RIQ_D2 = "riq_d2"
    HEDGED_P95_COC = "hedged_p95_coc"
    HEDGED_P95_JSQ2 = "hedged_p95_jsq2"
    HEDGED_STATIC_TIMEOUT = "hedged_static_timeout"


class ServiceModel(Enum):
    EXPONENTIAL_IR = "exp_ir"
    COUPLED_SX_STRAGGLER = "sx_straggler"
    COUPLED_SX_UNIFORM = "sx_uniform"


@dataclass(frozen=True)
class MgkSimSummary:
    policy: str
    rho_nominal: float
    mean_resp: float
    p95_resp: float
    p99_resp: float
    p999_resp: float
    extra_start_pct: float
    unstable_blowup: bool


def _quantile_sorted(vals: Sequence[float], q: float) -> float:
    idx = min(len(vals) - 1, max(0, int(q * (len(vals) - 1))))
    return vals[idx]


_CRN_TRACE_CACHE: dict[
    tuple[ServiceModel, float, int, int, int],
    tuple[list[float], list[float], list[tuple[float, float]]],
] = {}


def _get_crn_mgk_trace(
    service_model: ServiceModel,
    arrival_rate: float,
    k_servers: int,
    n_jobs: int,
    seed: int,
) -> tuple[list[float], list[float], list[tuple[float, float]]]:
    key = (service_model, arrival_rate, k_servers, n_jobs, seed)
    cached = _CRN_TRACE_CACHE.get(key)
    if cached is not None:
        return cached

    rng_arr = random.Random(seed)
    rng_svc = random.Random(seed + 77)
    arrivals: list[float] = []
    job_base_x: list[float] = []
    replica_draws: list[tuple[float, float]] = []
    t_cur = 0.0
    for _ in range(n_jobs):
        t_cur += rng_arr.expovariate(arrival_rate)
        arrivals.append(t_cur)
        if service_model is ServiceModel.EXPONENTIAL_IR:
            job_base_x.append(1.0)
            replica_draws.append((rng_svc.expovariate(1.0), rng_svc.expovariate(1.0)))
        elif service_model is ServiceModel.COUPLED_SX_STRAGGLER:
            x_val = 0.6 if rng_svc.random() < 0.75 else 2.2
            job_base_x.append(x_val)
            s1 = 12.0 if rng_svc.random() < 0.06 else 1.0
            s2 = 12.0 if rng_svc.random() < 0.06 else 1.0
            replica_draws.append((s1, s2))
        else:
            x_val = 0.6 if rng_svc.random() < 0.75 else 2.2
            job_base_x.append(x_val)
            replica_draws.append((1.0 + rng_svc.random(), 1.0 + rng_svc.random()))

    res = (arrivals, job_base_x, replica_draws)
    _CRN_TRACE_CACHE[key] = res
    return res


def sim_mgk_hedging(
    service_model: ServiceModel,
    policy: RedundancyPolicy,
    rho_nominal: float,
    k_servers: int = 12,
    n_jobs: int = 3_000,
    warmup_jobs: int = 500,
    seed: int = 202604,
    clone_overhead_z: float = 0.06,
) -> MgkSimSummary:
    """Discrete-event heapq M/G/k simulator separating JSQ-2 routing from redundancy."""
    rng_route = random.Random(seed + 154)

    # Baseline single-copy expected service time E[R_1]:
    # - EXP_IR: independent Exp(1.0) per replica -> E[R_1] = 1.0
    # - COUPLED_SX_STRAGGLER: R_j = X * S_j + Z * I(rep_idx > 0)
    #   (E[X]=1.0, S_j in {1 (94%), 12 (6%)}, E[S]=1.66, CV^2=2.48;
    #   for d=k=2 lockstep, Gardner et al. 2017b Thm 1 limit is E[S]/(2*E[min(S1,S2)]) = 0.7984)
    # - COUPLED_SX_UNIFORM: R_j = X * S_j + Z * I(rep_idx > 0)
    #   (E[X]=1.0, S_j ~ Uniform[1, 2], E[S]=1.5, E[min(S1,S2)]=4/3;
    #   for d=k=2 lockstep, rho_max = 1.5 / (2 * 4/3) = 0.5625; for d=2 < k=12, even with
    #   Z = 0, EagerCoC_d2 diverges at rho = 0.85 while HedgedP95_JSQ2/CoC stay stable)
    if service_model is ServiceModel.EXPONENTIAL_IR:
        mean_single_service = 1.0
    elif service_model is ServiceModel.COUPLED_SX_STRAGGLER:
        mean_single_service = 1.66
    elif service_model is ServiceModel.COUPLED_SX_UNIFORM:
        mean_single_service = 1.50
    else:
        raise AssertionError(f"Unhandled ServiceModel: {service_model}")

    arrival_rate = rho_nominal * k_servers / mean_single_service
    arrivals, job_base_x, replica_draws = _get_crn_mgk_trace(
        service_model, arrival_rate, k_servers, n_jobs, seed
    )

    EVT_FINISH = 0
    EVT_HEDGE_TIMER = 1
    EVT_ARRIVAL = 2

    cancels_in_queue_and_service = policy in (
        RedundancyPolicy.EAGER_COC_D2,
        RedundancyPolicy.HEDGED_P95_COC,
        RedundancyPolicy.HEDGED_P95_JSQ2,
        RedundancyPolicy.RIQ_D2,
    )

    server_busy_job: list[int | None] = [None] * k_servers
    server_token: list[int] = [0] * k_servers
    server_queues: list[deque[tuple[int, int]]] = [deque() for _ in range(k_servers)]

    job_done: list[bool] = [False] * n_jobs
    job_started_primary: list[bool] = [False] * n_jobs
    job_completion_time: list[float] = [0.0] * n_jobs
    replicas_started = 0

    rolling_window: list[float] = []
    rolling_idx = 0
    ROLL_CAP = 200
    cached_p95: float | None = None
    static_timeout_s = 2.6  # calibrated to low-load P95; triggers uncancelled retry storm at rho=0.80

    pq: list[tuple[float, int, int, int, int]] = []
    for j_id, t_arr in enumerate(arrivals):
        heapq.heappush(pq, (t_arr, EVT_ARRIVAL, j_id, 0, 0))

    def replica_runtime(j_id: int, rep_idx: int) -> float:
        d_val = replica_draws[j_id][rep_idx]
        if service_model is ServiceModel.EXPONENTIAL_IR:
            return d_val
        # Clone setup cost applies strictly to secondary clones (`rep_idx > 0`), never primaries.
        z_cost = clone_overhead_z if rep_idx > 0 else 0.0
        return job_base_x[j_id] * d_val + z_cost

    def active_queued_count(srv: int) -> int:
        q = server_queues[srv]
        if not q:
            return 0
        if cancels_in_queue_and_service:
            return sum(1 for j_id, _ in q if not job_done[j_id])
        if policy is RedundancyPolicy.TIED_COS_D2:
            return sum(
                1 for j_id, _ in q if not job_done[j_id] and not job_started_primary[j_id]
            )
        return len(q)

    def queue_len_active(srv: int) -> int:
        return (1 if server_busy_job[srv] is not None else 0) + active_queued_count(srv)

    def try_start_next(srv: int, now: float) -> None:
        nonlocal replicas_started
        q = server_queues[srv]
        while q:
            j_id, rep_idx = q.popleft()
            if cancels_in_queue_and_service and job_done[j_id]:
                continue
            if policy is RedundancyPolicy.TIED_COS_D2 and (
                job_done[j_id] or job_started_primary[j_id]
            ):
                continue
            job_started_primary[j_id] = True
            replicas_started += 1
            server_busy_job[srv] = j_id
            server_token[srv] += 1
            tok = server_token[srv]
            dur = replica_runtime(j_id, rep_idx)
            heapq.heappush(pq, (now + dur, EVT_FINISH, srv, j_id, tok))
            return
        server_busy_job[srv] = None

    def pick_two_servers() -> tuple[int, int]:
        s1 = rng_route.randrange(k_servers)
        s2 = rng_route.randrange(k_servers - 1)
        if s2 >= s1:
            s2 += 1
        return s1, s2

    while pq:
        now, evt_type, a, b, c = heapq.heappop(pq)

        if evt_type == EVT_FINISH:
            srv, j_id, tok = a, b, c
            if server_token[srv] != tok:
                continue
            server_busy_job[srv] = None
            if not job_done[j_id]:
                job_done[j_id] = True
                resp = now - arrivals[j_id]
                job_completion_time[j_id] = resp
                if len(rolling_window) < ROLL_CAP:
                    rolling_window.append(resp)
                else:
                    rolling_window[rolling_idx] = resp
                    rolling_idx = (rolling_idx + 1) % ROLL_CAP
                cached_p95 = None

                if cancels_in_queue_and_service:
                    for other_srv in range(k_servers):
                        if other_srv != srv and server_busy_job[other_srv] == j_id:
                            server_token[other_srv] += 1
                            server_busy_job[other_srv] = None
                            try_start_next(other_srv, now)
            try_start_next(srv, now)

        elif evt_type == EVT_HEDGE_TIMER:
            j_id, s_backup = a, b
            if not job_done[j_id]:
                server_queues[s_backup].append((j_id, 1))
                if server_busy_job[s_backup] is None:
                    try_start_next(s_backup, now)

        elif evt_type == EVT_ARRIVAL:
            j_id = a
            s1, s2 = pick_two_servers()
            if policy is RedundancyPolicy.SINGLE_RANDOM1:
                server_queues[s1].append((j_id, 0))
                if server_busy_job[s1] is None:
                    try_start_next(s1, now)

            elif policy is RedundancyPolicy.SINGLE_JSQ2:
                best = s1 if queue_len_active(s1) <= queue_len_active(s2) else s2
                server_queues[best].append((j_id, 0))
                if server_busy_job[best] is None:
                    try_start_next(best, now)

            elif policy in (
                RedundancyPolicy.EAGER_NOCANCEL_D2,
                RedundancyPolicy.EAGER_COC_D2,
                RedundancyPolicy.TIED_COS_D2,
            ):
                server_queues[s1].append((j_id, 0))
                server_queues[s2].append((j_id, 1))
                if server_busy_job[s1] is None:
                    try_start_next(s1, now)
                if server_busy_job[s2] is None:
                    try_start_next(s2, now)

            elif policy is RedundancyPolicy.RIQ_D2:
                idle1 = server_busy_job[s1] is None and active_queued_count(s1) == 0
                idle2 = server_busy_job[s2] is None and active_queued_count(s2) == 0
                if idle1 and idle2:
                    server_queues[s1].append((j_id, 0))
                    server_queues[s2].append((j_id, 1))
                    try_start_next(s1, now)
                    try_start_next(s2, now)
                elif idle1:
                    server_queues[s1].append((j_id, 0))
                    try_start_next(s1, now)
                elif idle2:
                    server_queues[s2].append((j_id, 0))
                    try_start_next(s2, now)
                else:
                    best = s1 if queue_len_active(s1) <= queue_len_active(s2) else s2
                    server_queues[best].append((j_id, 0))

            elif policy in (
                RedundancyPolicy.HEDGED_P95_COC,
                RedundancyPolicy.HEDGED_P95_JSQ2,
                RedundancyPolicy.HEDGED_STATIC_TIMEOUT,
            ):
                if policy is RedundancyPolicy.HEDGED_P95_JSQ2:
                    primary = s1 if queue_len_active(s1) <= queue_len_active(s2) else s2
                    backup = s2 if primary == s1 else s1
                else:
                    primary, backup = s1, s2
                server_queues[primary].append((j_id, 0))
                if server_busy_job[primary] is None:
                    try_start_next(primary, now)
                if policy is RedundancyPolicy.HEDGED_STATIC_TIMEOUT:
                    delay = static_timeout_s
                else:
                    if len(rolling_window) >= 40:
                        if cached_p95 is None:
                            cached_p95 = _quantile_sorted(sorted(rolling_window), 0.95)
                        delay = cached_p95
                    else:
                        delay = 6.0 * mean_single_service
                heapq.heappush(pq, (now + delay, EVT_HEDGE_TIMER, j_id, backup, 0))

    resps = sorted(job_completion_time[warmup_jobs:])
    mean_r = sum(resps) / len(resps)
    win = 400
    early_avg = sum(job_completion_time[warmup_jobs : warmup_jobs + win]) / win
    late_avg = sum(job_completion_time[n_jobs - win : n_jobs]) / win
    unstable = late_avg > max(24.0, 2.2 * early_avg)
    extra_pct = 100.0 * max(0, replicas_started - n_jobs) / n_jobs
    return MgkSimSummary(
        policy=policy.value,
        rho_nominal=rho_nominal,
        mean_resp=mean_r,
        p95_resp=_quantile_sorted(resps, 0.95),
        p99_resp=_quantile_sorted(resps, 0.99),
        p999_resp=_quantile_sorted(resps, 0.999),
        extra_start_pct=extra_pct,
        unstable_blowup=unstable,
    )


def sim_vulimiri_nocancel_exact_mgk(
    rho_nominal: float,
    k_servers: int = 12,
    n_jobs: int = 4_500,
    warmup_jobs: int = 750,
    seed: int = 202604,
) -> tuple[float, float]:
    """Compare Single vs. true uncancelled d=2 replication (Vulimiri et al. 2013 Thm 1)."""
    rng_arr = random.Random(seed)
    rng_svc = random.Random(seed + 77)
    rng_route = random.Random(seed + 154)
    arrival_rate = rho_nominal * k_servers

    arrivals = []
    draws = []
    srvs = []
    t_cur = 0.0
    for _ in range(n_jobs):
        t_cur += rng_arr.expovariate(arrival_rate)
        arrivals.append(t_cur)
        draws.append((rng_svc.expovariate(1.0), rng_svc.expovariate(1.0)))
        s1 = rng_route.randrange(k_servers)
        s2 = rng_route.randrange(k_servers - 1)
        if s2 >= s1:
            s2 += 1
        srvs.append((s1, s2))

    free_single = [0.0] * k_servers
    resp_single = []
    for j in range(n_jobs):
        s1, _ = srvs[j]
        start = max(arrivals[j], free_single[s1])
        fin = start + draws[j][0]
        free_single[s1] = fin
        if j >= warmup_jobs:
            resp_single.append(fin - arrivals[j])

    free_rep = [0.0] * k_servers
    resp_rep = []
    for j in range(n_jobs):
        s1, s2 = srvs[j]
        fin1 = max(arrivals[j], free_rep[s1]) + draws[j][0]
        fin2 = max(arrivals[j], free_rep[s2]) + draws[j][1]
        free_rep[s1] = fin1
        free_rep[s2] = fin2
        if j >= warmup_jobs:
            resp_rep.append(min(fin1, fin2) - arrivals[j])

    return sum(resp_single) / len(resp_single), sum(resp_rep) / len(resp_rep)


# ============================================================================
# PROBE 2B: Exact Knight-Leveson-Redux (48 Versions) & Eckhardt-Lee Covariance
# ============================================================================


@dataclass(frozen=True)
class AdmittedVersion:
    version_id: str
    agent: str
    language: str
    fail_mask_group: str
    fail_count: int


# Exact 48 admitted versions from ASSERT-KTH/Knight-Leveson-Redux@546a59d35e2fda7da070f0e6015523f4ca44a649
# (`results/analysis/summary_table.csv` & `results/all_triples_K_stats.md`, T = 1,000,000)
KL_REDUX_48_VERSIONS: tuple[AdmittedVersion, ...] = (
    AdmittedVersion("claude-haiku-4.5-rust", "claude_code", "rust", "circ419", 419),
    AdmittedVersion("claude-opus-4.5-pascal", "claude_code", "pascal", "none", 0),
    AdmittedVersion("claude-opus-4.5-python", "claude_code", "python", "none", 0),
    AdmittedVersion("claude-opus-4.5-rust", "claude_code", "rust", "none", 0),
    AdmittedVersion("claude-opus-4.6-pascal", "claude_code", "pascal", "none", 0),
    AdmittedVersion("claude-opus-4.6-python", "claude_code", "python", "none", 0),
    AdmittedVersion("claude-opus-4.6-rust", "claude_code", "rust", "circ419", 419),
    AdmittedVersion("claude-sonnet-4.5-pascal", "claude_code", "pascal", "circ419_plus_550", 969),
    AdmittedVersion("claude-sonnet-4.5-python", "claude_code", "python", "none", 0),
    AdmittedVersion("claude-sonnet-4.5-rust", "claude_code", "rust", "circ419", 419),
    AdmittedVersion("claude-sonnet-4.6-pascal", "claude_code", "pascal", "circ419", 419),
    AdmittedVersion("claude-sonnet-4.6-python", "claude_code", "python", "circ419", 419),
    AdmittedVersion("claude-sonnet-4.6-rust", "claude_code", "rust", "none", 0),
    AdmittedVersion("codex-gpt-5.2-pascal", "codex", "pascal", "none", 0),
    AdmittedVersion("codex-gpt-5.2-python", "codex", "python", "none", 0),
    AdmittedVersion("codex-gpt-5.2-rust", "codex", "rust", "none", 0),
    AdmittedVersion("codex-gpt-5.3-codex-pascal", "codex", "pascal", "none", 0),
    AdmittedVersion("codex-gpt-5.3-codex-python", "codex", "python", "none", 0),
    AdmittedVersion("codex-gpt-5.3-codex-rust", "codex", "rust", "none", 0),
    AdmittedVersion("codex-gpt-5.4-mini-python", "codex", "python", "none", 0),
    AdmittedVersion("codex-gpt-5.4-mini-rust", "codex", "rust", "none", 0),
    AdmittedVersion("codex-gpt-5.4-pascal", "codex", "pascal", "none", 0),
    AdmittedVersion("codex-gpt-5.4-python", "codex", "python", "none", 0),
    AdmittedVersion("codex-gpt-5.4-rust", "codex", "rust", "none", 0),
    AdmittedVersion("cursor-composer-2.5-pascal", "cursor", "pascal", "circ419", 419),
    AdmittedVersion("cursor-composer-2.5-python", "cursor", "python", "none", 0),
    AdmittedVersion("cursor-composer-2.5-rust", "cursor", "rust", "circ419", 419),
    AdmittedVersion("cursor-composer-2-pascal", "cursor", "pascal", "none", 0),
    AdmittedVersion("cursor-composer-2-python", "cursor", "python", "unique435", 435),
    AdmittedVersion("cursor-composer-2-rust", "cursor", "rust", "none", 0),
    AdmittedVersion("gemini-2.5-pro-python", "gemini", "python", "circ419", 419),
    AdmittedVersion("gemini-2.5-pro-rust", "gemini", "rust", "circ419", 419),
    AdmittedVersion("gemini-3-flash-pascal", "gemini", "pascal", "none", 0),
    AdmittedVersion("gemini-3-flash-python", "gemini", "python", "none", 0),
    AdmittedVersion("gemini-3-flash-rust", "gemini", "rust", "none", 0),
    AdmittedVersion("gemini-3.1-pro-pascal", "gemini", "pascal", "real10", 10),
    AdmittedVersion("gemini-3.1-pro-python", "gemini", "python", "real10", 10),
    AdmittedVersion("gemini-3.1-pro-rust", "gemini", "rust", "none", 0),
    AdmittedVersion("opencode-gemma-4-31b-python", "opencode", "python", "none", 0),
    AdmittedVersion("opencode-qwen3.5-397b-pascal", "opencode", "pascal", "circ419", 419),
    AdmittedVersion("opencode-qwen3.5-397b-python", "opencode", "python", "circ419", 419),
    AdmittedVersion("opencode-qwen3.5-397b-rust", "opencode", "rust", "circ419", 419),
    AdmittedVersion("opencode-qwen3.5-flash-python", "opencode", "python", "circ419_plus_10050", 10469),
    AdmittedVersion("opencode-qwen3.5-plus-python", "opencode", "python", "circ419", 419),
    AdmittedVersion("opencode-qwen3.5-plus-rust", "opencode", "rust", "circ419", 419),
    AdmittedVersion("opencode-qwen3.6-plus-pascal", "opencode", "pascal", "circ419", 419),
    AdmittedVersion("opencode-qwen3.6-plus-python", "opencode", "python", "none", 0),
    AdmittedVersion("opencode-qwen3.6-plus-rust", "opencode", "rust", "circ419", 419),
)


ATOM_SIZES: tuple[int, ...] = (419, 10, 550, 10050, 435)
GROUP_TO_ATOM_BITS: dict[str, int] = {
    "none": 0,
    "circ419": 0b00001,
    "real10": 0b00010,
    "circ419_plus_550": 0b00101,
    "circ419_plus_10050": 0b01001,
    "unique435": 0b10000,
}


def kl_z_statistic(failure_rates: Sequence[float], total_tests: int, k_observed: int) -> dict[str, float]:
    """Exact reproduction of `kl_z_statistic` in Knight-Leveson-Redux `analysis/analyze_results.py:59-115`."""
    n = len(failure_rates)
    p0 = math.prod(1.0 - p for p in failure_rates)
    p1 = sum(
        failure_rates[i] * math.prod((1.0 - failure_rates[j]) for j in range(n) if j != i)
        for i in range(n)
    )
    pm = max(0.0, 1.0 - p0 - p1)
    mu = total_tests * pm
    sigma = math.sqrt(total_tests * pm * (1.0 - pm))
    z = (k_observed - mu) / sigma
    return {"n": float(n), "mu": mu, "K": float(k_observed), "z": z}


def _linear_percentile(sorted_vals: Sequence[int], pct: float) -> float:
    """Exact match to numpy.percentile(..., method='linear') used in all_triples_K.py."""
    pos = (pct / 100.0) * (len(sorted_vals) - 1)
    lo = int(math.floor(pos))
    hi = int(math.ceil(pos))
    if lo == hi:
        return float(sorted_vals[lo])
    frac = pos - lo
    return sorted_vals[lo] * (1.0 - frac) + sorted_vals[hi] * frac


def eval_knight_leveson_redux_and_covariance() -> dict[str, object]:
    total_tests = 1_000_000
    assert len(KL_REDUX_48_VERSIONS) == 48

    def slice_kl(versions: Sequence[AdmittedVersion]) -> dict[str, float]:
        rates = [v.fail_count / total_tests for v in versions]
        masks = [GROUP_TO_ATOM_BITS[v.fail_mask_group] for v in versions]
        k_obs = 0
        for bit_idx, atom_sz in enumerate(ATOM_SIZES):
            bit = 1 << bit_idx
            cnt = sum(1 for m in masks if (m & bit) != 0)
            if cnt >= 2:
                k_obs += atom_sz
        return kl_z_statistic(rates, total_tests, k_obs)

    kl_all = slice_kl(KL_REDUX_48_VERSIONS)
    kl_py = slice_kl([v for v in KL_REDUX_48_VERSIONS if v.language == "python"])
    kl_rs = slice_kl([v for v in KL_REDUX_48_VERSIONS if v.language == "rust"])
    kl_pas = slice_kl([v for v in KL_REDUX_48_VERSIONS if v.language == "pascal"])

    assert round(kl_all["mu"], 2) == 115.36 and int(kl_all["K"]) == 429 and round(kl_all["z"], 2) == 29.20
    assert round(kl_py["mu"], 2) == 23.97 and int(kl_py["K"]) == 419 and round(kl_py["z"], 2) == 80.69
    assert round(kl_rs["mu"], 2) == 4.91 and int(kl_rs["K"]) == 419 and round(kl_rs["z"], 2) == 186.93
    assert round(kl_pas["mu"], 2) == 2.70 and int(kl_pas["K"]) == 419 and round(kl_pas["z"], 2) == 253.30

    masks = [GROUP_TO_ATOM_BITS[v.fail_mask_group] for v in KL_REDUX_48_VERSIONS]
    counts = [v.fail_count for v in KL_REDUX_48_VERSIONS]
    triple_ks: list[int] = []
    beat_best = 0
    worse_than_best = 0
    for i, j, k in itertools.combinations(range(48), 3):
        maj_mask = (masks[i] & masks[j]) | (masks[i] & masks[k]) | (masks[j] & masks[k])
        k_maj = 0
        if maj_mask:
            for bit_idx, atom_sz in enumerate(ATOM_SIZES):
                if maj_mask & (1 << bit_idx):
                    k_maj += atom_sz
        triple_ks.append(k_maj)
        c_min = min(counts[i], counts[j], counts[k])
        if k_maj < c_min:
            beat_best += 1
        elif k_maj > c_min:
            worse_than_best += 1

    triple_ks.sort()
    single_sorted = sorted(counts)
    assert len(triple_ks) == 17_296
    single_mean = sum(single_sorted) / 48.0
    triple_mean = sum(triple_ks) / 17_296.0
    single_p99 = _linear_percentile(single_sorted, 99.0)
    triple_p99 = _linear_percentile(triple_ks, 99.0)
    zero_triples = sum(1 for x in triple_ks if x == 0)

    assert round(single_mean, 2) == 387.44
    assert round(triple_mean, 2) == 130.99
    assert round(single_p99) == 6004 and round(triple_p99) == 419
    assert zero_triples == 11_844 and beat_best == 37 and worse_than_best == 4_464

    failing = [v for v in KL_REDUX_48_VERSIONS if v.fail_count > 0]
    cross_lang_def = 0
    cross_lang_phi1 = 0
    cross_agent_def = 0
    cross_agent_phi1 = 0
    for u, v in itertools.combinations(failing, 2):
        same_mask = u.fail_mask_group == v.fail_mask_group
        if u.language != v.language:
            cross_lang_def += 1
            if same_mask:
                cross_lang_phi1 += 1
        if u.agent != v.agent:
            cross_agent_def += 1
            if same_mask:
                cross_agent_phi1 += 1
    assert (cross_lang_phi1, cross_lang_def) == (81, 146)
    assert (cross_agent_phi1, cross_agent_def) == (87, 158)

    strata_q = (0.50, 0.25, 0.25)
    theta_a = (0.01, 0.30, 0.00)
    theta_b_corr = (0.01, 0.24, 0.06)
    theta_c_orth = (0.01, 0.00, 0.30)

    def cov_decomp(ta: Sequence[float], tb: Sequence[float]) -> dict[str, float]:
        mu_a = sum(q * a for q, a in zip(strata_q, ta))
        mu_b = sum(q * b for q, b in zip(strata_q, tb))
        e_ab = sum(q * a * b for q, a, b in zip(strata_q, ta, tb))
        cov = sum(q * (a - mu_a) * (b - mu_b) for q, a, b in zip(strata_q, ta, tb))
        assert abs(e_ab - (mu_a * mu_b + cov)) < 1e-15
        return {"mu_a": mu_a, "mu_b": mu_b, "indep_prod": mu_a * mu_b, "cov": cov, "co_fail": e_ab}

    homo = cov_decomp(theta_a, theta_a)
    pos_div = cov_decomp(theta_a, theta_b_corr)
    neg_div = cov_decomp(theta_a, theta_c_orth)
    assert homo["cov"] > pos_div["cov"] > 0.0 > neg_div["cov"]
    assert homo["co_fail"] > homo["indep_prod"] and neg_div["co_fail"] < neg_div["indep_prod"]

    return {
        "kl_table_iii": {
            "all": kl_all,
            "python": kl_py,
            "rust": kl_rs,
            "pascal": kl_pas,
        },
        "triples": {
            "total": 17_296,
            "single_mean": single_mean,
            "triple_mean": triple_mean,
            "single_p99": single_p99,
            "triple_p99": triple_p99,
            "single_max": single_sorted[-1],
            "triple_max": triple_ks[-1],
            "zero_triples": zero_triples,
            "beat_best": beat_best,
            "worse_than_best": worse_than_best,
        },
        "pairwise_phi1": {
            "cross_lang": (cross_lang_phi1, cross_lang_def),
            "cross_agent": (cross_agent_phi1, cross_agent_def),
        },
        "eckhardt_lee": {
            "homogeneous": homo,
            "shared_shortcut": pos_div,
            "orthogonal_critic": neg_div,
        },
    }


def run_probe_2() -> dict[str, object]:
    # 2A.1 Verify Vulimiri et al. (2013) Theorem 1 crossover rho* = 1/(d+1) = 1/3 on uncancelled Exp
    exp_low_single, exp_low_rep = sim_vulimiri_nocancel_exact_mgk(rho_nominal=0.22)
    exp_high_single, exp_high_rep = sim_vulimiri_nocancel_exact_mgk(rho_nominal=0.42)
    assert exp_low_rep < exp_low_single, "Uncancelled d=2 must reduce mean latency below rho*=1/3"
    assert exp_high_rep > exp_high_single, "Uncancelled d=2 must degrade mean latency above rho*=1/3"

    # 2A.2 S&X coupled job size + bimodal straggler slowdown across low (0.20), mid (0.55), high (0.80),
    # separating Mitzenmacher JSQ-2 load balancing (`single_jsq2`) from true replication (`hedged_p95_jsq2`).
    sx_results: dict[str, list[MgkSimSummary]] = {}
    for pol in (
        RedundancyPolicy.SINGLE_RANDOM1,
        RedundancyPolicy.SINGLE_JSQ2,
        RedundancyPolicy.EAGER_NOCANCEL_D2,
        RedundancyPolicy.HEDGED_STATIC_TIMEOUT,
        RedundancyPolicy.TIED_COS_D2,
        RedundancyPolicy.RIQ_D2,
        RedundancyPolicy.HEDGED_P95_COC,
        RedundancyPolicy.HEDGED_P95_JSQ2,
    ):
        sx_results[pol.value] = [
            sim_mgk_hedging(ServiceModel.COUPLED_SX_STRAGGLER, pol, rho)
            for rho in (0.20, 0.55, 0.80)
        ]

    # 2A.3 Pure Z = 0 Gardner et al. (2017b) S&X Uniform[1, 2] instability over n_jobs = 16,000:
    # For d = k = 2 lockstep, Gardner et al. Theorem 1 gives rho_max = E[S]/(2*E[min(S1,S2)]) = 0.5625;
    # on k = 12 servers (d = 2 < k) at rho = 0.85 with clone_overhead_z = 0.0, EagerCoC_d2 still
    # diverges linearly while Single_JSQ2, HedgedP95_CoC, and HedgedP95_JSQ2 remain stable.
    n_unif = 16_000
    w_unif = 2_000
    sx_unif_rand1_85 = sim_mgk_hedging(
        ServiceModel.COUPLED_SX_UNIFORM,
        RedundancyPolicy.SINGLE_RANDOM1,
        0.85,
        n_jobs=n_unif,
        warmup_jobs=w_unif,
        clone_overhead_z=0.0,
    )
    sx_unif_jsq2_85 = sim_mgk_hedging(
        ServiceModel.COUPLED_SX_UNIFORM,
        RedundancyPolicy.SINGLE_JSQ2,
        0.85,
        n_jobs=n_unif,
        warmup_jobs=w_unif,
        clone_overhead_z=0.0,
    )
    sx_unif_eager_coc_85 = sim_mgk_hedging(
        ServiceModel.COUPLED_SX_UNIFORM,
        RedundancyPolicy.EAGER_COC_D2,
        0.85,
        n_jobs=n_unif,
        warmup_jobs=w_unif,
        clone_overhead_z=0.0,
    )
    sx_unif_p95_rand1_85 = sim_mgk_hedging(
        ServiceModel.COUPLED_SX_UNIFORM,
        RedundancyPolicy.HEDGED_P95_COC,
        0.85,
        n_jobs=n_unif,
        warmup_jobs=w_unif,
        clone_overhead_z=0.0,
    )
    sx_unif_p95_jsq2_85 = sim_mgk_hedging(
        ServiceModel.COUPLED_SX_UNIFORM,
        RedundancyPolicy.HEDGED_P95_JSQ2,
        0.85,
        n_jobs=n_unif,
        warmup_jobs=w_unif,
        clone_overhead_z=0.0,
    )
    assert sx_unif_eager_coc_85.unstable_blowup and (
        sx_unif_eager_coc_85.mean_resp > 9.0 * sx_unif_rand1_85.mean_resp
    )
    assert not sx_unif_p95_rand1_85.unstable_blowup and (
        sx_unif_p95_rand1_85.mean_resp < sx_unif_rand1_85.mean_resp
    )
    assert not sx_unif_p95_jsq2_85.unstable_blowup and sx_unif_p95_jsq2_85.extra_start_pct < 5.0

    # Verify S&X straggler blowup, retry storm, and JSQ-2 vs true redundancy separation
    assert sx_results["eager_nocancel_d2"][1].unstable_blowup  # rho = 0.55 > 0.50
    rand1_80 = sx_results["single_random1"][2]
    jsq2_80 = sx_results["single_jsq2"][2]
    nocancel_80 = sx_results["eager_nocancel_d2"][2]
    static_80 = sx_results["hedged_static_timeout"][2]
    tied_80 = sx_results["tied_cos_d2"][2]
    riq_80 = sx_results["riq_d2"][2]
    p95_rand1_80 = sx_results["hedged_p95_coc"][2]
    p95_jsq2_80 = sx_results["hedged_p95_jsq2"][2]

    assert nocancel_80.unstable_blowup and nocancel_80.mean_resp > 4.0 * rand1_80.mean_resp
    assert static_80.unstable_blowup and static_80.extra_start_pct > 50.0
    assert (
        not jsq2_80.unstable_blowup
        and not tied_80.unstable_blowup
        and not riq_80.unstable_blowup
        and not p95_rand1_80.unstable_blowup
        and not p95_jsq2_80.unstable_blowup
    )
    # Non-redundant Single_JSQ2 already beats Single_Random1 dramatically and matches RIQ_d2 at rho=0.80,
    # whereas HedgedP95_JSQ2 delivers a true -47.8% P99 compression BELOW Single_JSQ2!
    assert jsq2_80.p99_resp < 0.35 * rand1_80.p99_resp
    p99_red_vs_jsq2 = (jsq2_80.p99_resp - p95_jsq2_80.p99_resp) / jsq2_80.p99_resp
    assert 0.45 < p99_red_vs_jsq2 < 0.50 and p95_jsq2_80.extra_start_pct < 5.0
    assert sx_results["riq_d2"][0].extra_start_pct > 50.0 and riq_80.extra_start_pct < 6.0
    # At low load (rho=0.20), cancel-on-start (`tied_cos_d2`) and `single_jsq2` cannot cancel an
    # already-running 12x straggler (P99 = 26.40), whereas `hedged_p95_jsq2` cuts P99 to 7.20!
    assert sx_results["hedged_p95_jsq2"][0].p99_resp < 0.35 * sx_results["single_jsq2"][0].p99_resp

    kl_res = eval_knight_leveson_redux_and_covariance()
    return {
        "vulimiri_exp_crossover": {
            "rho_022_single": exp_low_single,
            "rho_022_nocancel_d2": exp_low_rep,
            "rho_042_single": exp_high_single,
            "rho_042_nocancel_d2": exp_high_rep,
        },
        "sx_mgk": sx_results,
        "p99_reduction_p95_jsq2_over_single_jsq2_pct": 100.0 * p99_red_vs_jsq2,
        "sx_uniform_coc_blowup": {
            "n_jobs": n_unif,
            "clone_overhead_z": 0.0,
            "rho": 0.85,
            "lockstep_d2_k2_rho_max": 0.5625,
            "single_random1_mean": sx_unif_rand1_85.mean_resp,
            "single_jsq2_mean": sx_unif_jsq2_85.mean_resp,
            "eager_coc_d2_mean": sx_unif_eager_coc_85.mean_resp,
            "eager_coc_d2_unstable": sx_unif_eager_coc_85.unstable_blowup,
            "hedged_p95_coc_mean": sx_unif_p95_rand1_85.mean_resp,
            "hedged_p95_jsq2_mean": sx_unif_p95_jsq2_85.mean_resp,
        },
        "kl_redux": kl_res,
    }


# ============================================================================
# PROBE 3: NK Landscape Network Topologies & Derex-Boyd Recombinant Innovation
# ============================================================================


def _build_topologies(m_agents: int) -> dict[str, list[list[int]]]:
    """Static base neighbor lists for M = 24 agents."""
    assert m_agents == 24
    ring = [[(i - 1) % m_agents, (i + 1) % m_agents] for i in range(m_agents)]
    full = [[j for j in range(m_agents) if j != i] for i in range(m_agents)]
    sw = []
    for i in range(m_agents):
        nbrs = {
            (i - 2) % m_agents,
            (i - 1) % m_agents,
            (i + 1) % m_agents,
            (i + 2) % m_agents,
        }
        if i % 3 == 0:
            nbrs.add((i + m_agents // 2) % m_agents)
        sw.append(sorted(nbrs))
    pods = []
    for i in range(m_agents):
        pod_base = (i // 4) * 4
        pods.append([pod_base + off for off in range(4) if (pod_base + off) != i])
    return {
        "fully_connected": full,
        "small_world": sw,
        "ring_lattice": ring,
        "periodic_pod_migration": pods,
    }


def sim_nk_landscapes(
    n_bits: int = 10,
    k_epistasis: int = 5,
    m_agents: int = 24,
    t_rounds: int = 55,
    n_landscapes: int = 75,
    seed: int = 30303,
) -> dict[str, dict[str, float]]:
    """Lazer & Friedman (2007) paired NK landscape simulation with exact 2^N global-max lookup."""
    rng = random.Random(seed + 100 * k_epistasis)
    n_states = 1 << n_bits
    topos = _build_topologies(m_agents)
    accum = {
        name: {"t3_score": 0.0, "t3_uniq": 0.0, "end_score": 0.0, "global_opt_hits": 0.0}
        for name in topos
    }

    locus_bit_vals = [
        [[((s >> b) & 1) << pos for s in range(n_states)] for pos in range(k_epistasis + 1)]
        for b in range(n_bits)
    ]

    for _ in range(n_landscapes):
        dep_shifts = []
        contrib_tables = []
        for i in range(n_bits):
            others = [j for j in range(n_bits) if j != i]
            coupled = [i] + rng.sample(others, k_epistasis)
            dep_shifts.append(coupled)
            contrib_tables.append([rng.random() for _ in range(1 << (k_epistasis + 1))])

        raw_f = [0.0] * n_states
        inv_n_bits = 1.0 / n_bits
        if k_epistasis == 0:
            t0, t1, t2, t3, t4, t5, t6, t7, t8, t9 = contrib_tables
            for s in range(n_states):
                raw_f[s] = (
                    t0[s & 1]
                    + t1[(s >> 1) & 1]
                    + t2[(s >> 2) & 1]
                    + t3[(s >> 3) & 1]
                    + t4[(s >> 4) & 1]
                    + t5[(s >> 5) & 1]
                    + t6[(s >> 6) & 1]
                    + t7[(s >> 7) & 1]
                    + t8[(s >> 8) & 1]
                    + t9[(s >> 9) & 1]
                ) * inv_n_bits
        elif k_epistasis == 5:
            for i in range(n_bits):
                b0, b1, b2, b3, b4, b5 = dep_shifts[i]
                tbl = contrib_tables[i]
                v0 = locus_bit_vals[b0][0]
                v1 = locus_bit_vals[b1][1]
                v2 = locus_bit_vals[b2][2]
                v3 = locus_bit_vals[b3][3]
                v4 = locus_bit_vals[b4][4]
                v5 = locus_bit_vals[b5][5]
                for s, (x0, x1, x2, x3, x4, x5) in enumerate(zip(v0, v1, v2, v3, v4, v5)):
                    raw_f[s] += tbl[x0 | x1 | x2 | x3 | x4 | x5]
            for s in range(n_states):
                raw_f[s] *= inv_n_bits
        else:
            for s in range(n_states):
                total = 0.0
                for i in range(n_bits):
                    idx = 0
                    for bit_pos, locus in enumerate(dep_shifts[i]):
                        if (s >> locus) & 1:
                            idx |= 1 << bit_pos
                    total += contrib_tables[i][idx]
                raw_f[s] = total * inv_n_bits
        max_raw = max(raw_f)

        scores = [(v / max_raw) ** 8 for v in raw_f]
        opt_states = {s for s, v in enumerate(raw_f) if abs(v - max_raw) < 1e-12}

        init_pop = [rng.randrange(n_states) for _ in range(m_agents)]
        flip_choices = [
            [rng.randrange(n_bits) for _ in range(m_agents)] for _ in range(t_rounds)
        ]

        for topo_name, base_nbrs in topos.items():
            pop = list(init_pop)
            for t in range(1, t_rounds + 1):
                next_pop = list(pop)
                migrate_now = topo_name == "periodic_pod_migration" and (t % 15 == 0)
                for a_idx in range(m_agents):
                    cur_s = pop[a_idx]
                    best_s = cur_s
                    best_f = scores[cur_s]
                    nbr_list = base_nbrs[a_idx]
                    if migrate_now:
                        nbr_list = nbr_list + [(a_idx + 4) % m_agents]
                    for nb in nbr_list:
                        nb_s = pop[nb]
                        nb_f = scores[nb_s]
                        if nb_f > best_f:
                            best_f = nb_f
                            best_s = nb_s
                    if best_s != cur_s:
                        next_pop[a_idx] = best_s
                    else:
                        cand_s = cur_s ^ (1 << flip_choices[t - 1][a_idx])
                        if scores[cand_s] > best_f:
                            next_pop[a_idx] = cand_s
                pop = next_pop
                if t == 3:
                    accum[topo_name]["t3_score"] += sum(scores[s] for s in pop) / m_agents
                    accum[topo_name]["t3_uniq"] += float(len(set(pop)))

            accum[topo_name]["end_score"] += sum(scores[s] for s in pop) / m_agents
            if any(s in opt_states for s in pop):
                accum[topo_name]["global_opt_hits"] += 1.0

    inv = 1.0 / n_landscapes
    return {
        name: {k: v * inv for k, v in stats.items()} for name, stats in accum.items()
    }


def sim_derex_boyd_recombinant(
    n_groups: int = 200,
    n_rounds: int = 72,
    seed: int = 40404,
) -> dict[str, dict[str, float]]:
    """Symmetric synchronous Derex & Boyd (2016) 20-triad cumulative recombinant model.

    Enforces synchronous round boundaries (`prev_known` snapshot at start of each round),
    uniform random tie-breaking across equal-payoff neighbor items (`'A3'` vs. `'B3'`),
    and symmetric refinement of any unfinished (`0 < lvl < 3`) known lineage even when
    the complementary lineage has already reached level 3.
    """
    # Bitmask encoding preserving exact set/tie-break order ('A*' before 'B*'):
    # 1=A1(10), 2=A2(30), 4=A3(65), 8=B1(10), 16=B2(30), 32=B3(65), 64=R4(150)
    BIT_A1, BIT_A2, BIT_A3 = 1, 2, 4
    BIT_B1, BIT_B2, BIT_B3 = 8, 16, 32
    BIT_R4 = 64
    MASK_A = BIT_A1 | BIT_A2 | BIT_A3
    MASK_B = BIT_B1 | BIT_B2 | BIT_B3
    NEXT_A = (0, BIT_A2, BIT_A3)
    NEXT_B = (0, BIT_B2, BIT_B3)

    def best_obs_from_mask(m: int) -> tuple[int, tuple[int, ...]]:
        if m & BIT_R4:
            return 150, (BIT_R4,)
        a3 = bool(m & BIT_A3)
        b3 = bool(m & BIT_B3)
        if a3 or b3:
            return 65, ((BIT_A3, BIT_B3) if (a3 and b3) else ((BIT_A3,) if a3 else (BIT_B3,)))
        a2 = bool(m & BIT_A2)
        b2 = bool(m & BIT_B2)
        if a2 or b2:
            return 30, ((BIT_A2, BIT_B2) if (a2 and b2) else ((BIT_A2,) if a2 else (BIT_B2,)))
        a1 = bool(m & BIT_A1)
        b1 = bool(m & BIT_B1)
        if a1 or b1:
            return 10, ((BIT_A1, BIT_B1) if (a1 and b1) else ((BIT_A1,) if a1 else (BIT_B1,)))
        return 0, ()

    full_nbrs = [[j for j in range(6) if j != i] for i in range(6)]
    pod_nbrs_by_shift: list[list[list[int]]] = []
    for sh in range(3):
        nb_s: list[list[int]] = [[] for _ in range(6)]
        for p_idx in range(3):
            u = (2 * p_idx) % 6
            v = (2 * p_idx + 1 + 2 * sh) % 6
            if u != v:
                nb_s[u].append(v)
                nb_s[v].append(u)
        pod_nbrs_by_shift.append(nb_s)

    def run_topology(mode: str) -> dict[str, float]:
        both_l3_groups = 0
        r4_groups = 0
        mean_best_payoff = 0.0
        for g in range(n_groups):
            sub_rng = random.Random(seed + 1000 * g)
            known = [0] * 6

            for r in range(1, n_rounds + 1):
                if mode == "fully_connected":
                    nbrs = full_nbrs
                else:
                    shift = 0 if r < 36 else ((r - 36) // 12) % 3
                    nbrs = pod_nbrs_by_shift[shift]

                prev_known = known[:]
                obs_pool = [best_obs_from_mask(m) for m in prev_known]
                next_known = [0] * 6

                for i in range(6):
                    kmask = prev_known[i]
                    for nb in nbrs[i]:
                        mx, cands = obs_pool[nb]
                        if mx > 0:
                            best_bit = cands[0] if len(cands) == 1 else sub_rng.choice(cands)
                            kmask |= best_bit
                            if best_bit & MASK_A:
                                kmask |= BIT_A1
                            elif best_bit & MASK_B:
                                kmask |= BIT_B1

                    if not (kmask & BIT_R4):
                        if (kmask & BIT_A3) and (kmask & BIT_B3):
                            if sub_rng.random() < 0.45:
                                kmask |= BIT_R4
                        else:
                            has_a = bool(kmask & MASK_A)
                            has_b = bool(kmask & MASK_B)
                            if not has_a and not has_b:
                                draw = sub_rng.randrange(20)
                                if draw == 0:
                                    kmask |= BIT_A1
                                elif draw == 1:
                                    kmask |= BIT_B1
                            elif sub_rng.random() < 0.01:
                                draw = sub_rng.randrange(20)
                                if draw == 0:
                                    kmask |= BIT_A1
                                elif draw == 1:
                                    kmask |= BIT_B1
                            else:
                                a_lvl = (
                                    3
                                    if (kmask & BIT_A3)
                                    else (2 if (kmask & BIT_A2) else (1 if (kmask & BIT_A1) else 0))
                                )
                                b_lvl = (
                                    3
                                    if (kmask & BIT_B3)
                                    else (2 if (kmask & BIT_B2) else (1 if (kmask & BIT_B1) else 0))
                                )
                                if 0 < a_lvl < 3 and 0 < b_lvl < 3:
                                    if a_lvl > b_lvl:
                                        if sub_rng.random() < 0.22:
                                            kmask |= NEXT_A[a_lvl]
                                    elif b_lvl > a_lvl:
                                        if sub_rng.random() < 0.22:
                                            kmask |= NEXT_B[b_lvl]
                                    else:
                                        pick_lin = sub_rng.choice((0, 1))
                                        if sub_rng.random() < 0.22:
                                            kmask |= (
                                                NEXT_A[a_lvl] if pick_lin == 0 else NEXT_B[b_lvl]
                                            )
                                elif 0 < a_lvl < 3:
                                    if sub_rng.random() < 0.22:
                                        kmask |= NEXT_A[a_lvl]
                                elif 0 < b_lvl < 3:
                                    if sub_rng.random() < 0.22:
                                        kmask |= NEXT_B[b_lvl]
                    next_known[i] = kmask
                known = next_known

            union_mask = known[0] | known[1] | known[2] | known[3] | known[4] | known[5]
            if (union_mask & BIT_A3) and (union_mask & BIT_B3):
                both_l3_groups += 1
            if union_mask & BIT_R4:
                r4_groups += 1
            best_group_p, _ = best_obs_from_mask(union_mask)
            mean_best_payoff += best_group_p

        return {
            "both_a3_b3_pct": 100.0 * both_l3_groups / n_groups,
            "r4_breakthrough_pct": 100.0 * r4_groups / n_groups,
            "mean_group_max_payoff": mean_best_payoff / n_groups,
        }

    fc = run_topology("fully_connected")
    pods = run_topology("isolated_pods_with_migration")
    assert 20.0 < fc["r4_breakthrough_pct"] < 36.0
    assert pods["both_a3_b3_pct"] > 75.0 and pods["r4_breakthrough_pct"] > 2.5 * fc["r4_breakthrough_pct"]
    assert pods["mean_group_max_payoff"] > 1.45 * fc["mean_group_max_payoff"]
    return {
        "fully_connected": fc,
        "isolated_pods_with_migration": pods,
        "r4_ratio": pods["r4_breakthrough_pct"] / fc["r4_breakthrough_pct"],
    }


def run_probe_3() -> dict[str, object]:
    nk_smooth = sim_nk_landscapes(k_epistasis=0)
    nk_rugged = sim_nk_landscapes(k_epistasis=5)

    assert nk_smooth["fully_connected"]["t3_score"] > nk_smooth["ring_lattice"]["t3_score"]
    assert nk_smooth["fully_connected"]["global_opt_hits"] >= nk_smooth["ring_lattice"]["global_opt_hits"]

    assert nk_rugged["fully_connected"]["t3_score"] > nk_rugged["ring_lattice"]["t3_score"]
    assert nk_rugged["fully_connected"]["t3_score"] > nk_rugged["periodic_pod_migration"]["t3_score"]
    assert nk_rugged["fully_connected"]["t3_uniq"] < nk_rugged["ring_lattice"]["t3_uniq"]
    assert nk_rugged["ring_lattice"]["end_score"] > nk_rugged["fully_connected"]["end_score"]
    assert nk_rugged["periodic_pod_migration"]["end_score"] > nk_rugged["fully_connected"]["end_score"]
    assert (
        nk_rugged["periodic_pod_migration"]["global_opt_hits"]
        > 2.0 * nk_rugged["fully_connected"]["global_opt_hits"]
    )

    recombinant = sim_derex_boyd_recombinant()
    return {"nk_k0": nk_smooth, "nk_k5": nk_rugged, "derex_boyd": recombinant}


# ============================================================================
# PROBE 4: Gunther USL Knees, Nose-Curve Sign-Bug Proof & NLS Parameter Fit
# ============================================================================


@dataclass(frozen=True)
class UslModel:
    sigma: float  # contention (alpha), requires 0 <= sigma < 1
    kappa: float  # coherency / crosstalk (beta), requires kappa >= 0
    lam: float    # single-worker throughput X(1) = lambda_1, requires lam > 0

    def __post_init__(self) -> None:
        if not (0.0 <= self.sigma < 1.0):
            raise ValueError(f"USL contention sigma must satisfy 0 <= sigma < 1; got {self.sigma}")
        if self.kappa < 0.0:
            raise ValueError(f"USL coherency kappa must satisfy kappa >= 0; got {self.kappa}")
        if self.lam <= 0.0:
            raise ValueError(f"USL baseline throughput lam must satisfy lam > 0; got {self.lam}")

    def capacity_ratio(self, n: float) -> float:
        if n <= 0.0:
            raise ValueError(f"Concurrency n must be positive; got {n}")
        return n / (1.0 + self.sigma * (n - 1.0) + self.kappa * n * (n - 1.0))

    def throughput_at_concurrency(self, n: float) -> float:
        return self.lam * self.capacity_ratio(n)

    def latency_at_concurrency(self, n: float) -> float:
        if n <= 0.0:
            raise ValueError(f"Concurrency n must be positive; got {n}")
        return (1.0 + self.sigma * (n - 1.0) + self.kappa * n * (n - 1.0)) / self.lam

    def n_opt_continuous(self) -> float:
        if self.kappa == 0.0:
            return math.inf
        return math.sqrt((1.0 - self.sigma) / self.kappa)

    def max_concurrency_floor(self) -> float:
        return math.floor(self.n_opt_continuous()) if self.kappa > 0.0 else math.inf

    def concurrency_at_latency(self, r: float) -> float:
        """Exact N(R) matching codahale/usl `model.go:72-77`, extended with kappa == 0 limit."""
        if r <= 0.0:
            raise ValueError(f"Latency r must be positive; got {r}")
        if self.kappa == 0.0:
            if self.sigma == 0.0:
                raise ValueError("ConcurrencyAtLatency is multi-valued when sigma == kappa == 0")
            return (self.lam * r - 1.0 + self.sigma) / self.sigma
        disc = (
            self.sigma * self.sigma
            + self.kappa * self.kappa
            + 2.0 * self.kappa * (2.0 * self.lam * r + self.sigma - 2.0)
        )
        if disc < -1e-15:
            raise ValueError(f"Latency r={r} is below achievable minimum latency")
        return (self.kappa - self.sigma + math.sqrt(max(0.0, disc))) / (2.0 * self.kappa)

    def throughput_at_latency_codahale_buggy(self, r: float) -> float:
        """Exact reproduction of Schwartz Eq. 9 (`scalability.tex:678`) & `codahale/usl` `model.go:63-66`.

        Contains the upstream sign inversion `- self.kappa + self.sigma` in the numerator,
        which equals the true throughput ONLY on the degenerate slice `sigma == kappa`
        tested by `model_test.go:99-107`!
        """
        if self.kappa == 0.0:
            raise ZeroDivisionError("Upstream model.go:63-66 divides by 2 * m.Kappa * r")
        disc = (
            self.sigma * self.sigma
            + self.kappa * self.kappa
            + 2.0 * self.kappa * (2.0 * self.lam * r + self.sigma - 2.0)
        )
        return (math.sqrt(disc) - self.kappa + self.sigma) / (2.0 * self.kappa * r)

    def throughput_at_latency_exact(self, r: float) -> float:
        """Exact Little's Law inverse X(R) = N(R) / R (`+ self.kappa - self.sigma`), with kappa == 0 limit."""
        if r <= 0.0:
            raise ValueError(f"Latency r must be positive; got {r}")
        if self.kappa == 0.0:
            return self.concurrency_at_latency(r) / r
        disc = (
            self.sigma * self.sigma
            + self.kappa * self.kappa
            + 2.0 * self.kappa * (2.0 * self.lam * r + self.sigma - 2.0)
        )
        if disc < -1e-15:
            raise ValueError(f"Latency r={r} is below achievable minimum latency")
        return (math.sqrt(max(0.0, disc)) + self.kappa - self.sigma) / (2.0 * self.kappa * r)

    def latency_branches_at_throughput(self, x: float) -> tuple[float, float]:
        """Both branches (R_sub_knee, R_retrograde_nose) of R(X) for kappa > 0 (`scalability.tex` Eq. 8)."""
        if x <= 0.0:
            raise ValueError(f"Throughput x must be positive; got {x}")
        if self.kappa == 0.0:
            # Pure Amdahl single-valued curve (`scalability.tex` Eq. 7)
            if self.sigma * x >= self.lam:
                raise ValueError(f"Throughput x={x} exceeds Amdahl asymptote {self.lam / self.sigma}")
            r_amdahl = (self.sigma - 1.0) / (self.sigma * x - self.lam)
            return r_amdahl, math.inf
        disc = (
            x * x * (self.kappa * self.kappa + 2.0 * self.kappa * (self.sigma - 2.0) + self.sigma * self.sigma)
            + 2.0 * self.lam * x * (self.kappa - self.sigma)
            + self.lam * self.lam
        )
        if disc < -1e-15:
            raise ValueError(f"Throughput x={x} exceeds peak USL capacity")
        root = math.sqrt(max(0.0, disc))
        center = self.kappa * x + self.lam - self.sigma * x
        denom = 2.0 * self.kappa * x * x
        return (center - root) / denom, (center + root) / denom


# Exact 32-point Cisco benchmark fixture from codahale/usl@513b3f33 `model_test.go:159-192`
CODAHALE_CISCO_FIXTURE: tuple[tuple[float, float], ...] = (
    (1, 955.16), (2, 1878.91), (3, 2688.01), (4, 3548.68),
    (5, 4315.54), (6, 5130.43), (7, 5931.37), (8, 6531.08),
    (9, 7219.80), (10, 7867.61), (11, 8278.71), (12, 8646.70),
    (13, 9047.84), (14, 9426.55), (15, 9645.37), (16, 9897.24),
    (17, 10097.60), (18, 10240.50), (19, 10532.39), (20, 10798.52),
    (21, 11151.43), (22, 11518.63), (23, 11806.00), (24, 12089.37),
    (25, 12075.41), (26, 12177.29), (27, 12211.41), (28, 12158.93),
    (29, 12155.27), (30, 12118.04), (31, 12140.40), (32, 12074.39),
)


def _solve_3x3(a: list[list[float]], b: list[float]) -> list[float]:
    """Gaussian elimination with partial pivoting for 3x3 normal equations."""
    m = [row[:] + [rhs] for row, rhs in zip(a, b)]
    for col in range(3):
        piv = max(range(col, 3), key=lambda r: abs(m[r][col]))
        m[col], m[piv] = m[piv], m[col]
        div = m[col][col]
        for j in range(col, 4):
            m[col][j] /= div
        for r in range(3):
            if r != col:
                factor = m[r][col]
                for j in range(col, 4):
                    m[r][j] -= factor * m[col][j]
    return [m[i][3] for i in range(3)]


def fit_usl_ols_linearized(samples: Sequence[tuple[float, float]]) -> UslModel:
    """2-parameter linearized OLS given X(1) anchor: N/C(N) - 1 = sigma*(N-1) + kappa*N*(N-1)."""
    lam1 = next(x for n, x in samples if abs(n - 1.0) < 1e-9)
    s11 = s12 = s22 = r1 = r2 = 0.0
    for n, x in samples:
        if n <= 1.0:
            continue
        u1 = n - 1.0
        u2 = n * (n - 1.0)
        y = (n * lam1 / x) - 1.0
        s11 += u1 * u1
        s12 += u1 * u2
        s22 += u2 * u2
        r1 += u1 * y
        r2 += u2 * y
    det = s11 * s22 - s12 * s12
    sigma = min(0.999999, max(0.0, (s22 * r1 - s12 * r2) / det))
    kappa = max(0.0, (-s12 * r1 + s11 * r2) / det)
    return UslModel(sigma=sigma, kappa=kappa, lam=lam1)


def fit_usl_levenberg_marquardt(
    samples: Sequence[tuple[float, float]], max_iter: int = 200
) -> UslModel:
    """3-parameter Levenberg-Marquardt nonlinear least squares matching `codahale/usl` `Build`."""
    params = [0.1, 0.01, max(x / n for n, x in samples)]
    damping = 1e-6

    def sse_and_preds(p: Sequence[float]) -> tuple[float, list[float]]:
        sig, kap, lam = p
        preds = []
        err_sq = 0.0
        for n, x_obs in samples:
            denom = 1.0 + sig * (n - 1.0) + kap * n * (n - 1.0)
            pred = (lam * n) / denom
            preds.append(pred)
            diff = x_obs - pred
            err_sq += diff * diff
        return err_sq, preds

    cur_sse, _ = sse_and_preds(params)
    for _ in range(max_iter):
        sig, kap, lam = params
        jtj = [[0.0, 0.0, 0.0] for _ in range(3)]
        jtr = [0.0, 0.0, 0.0]
        for n, x_obs in samples:
            denom = 1.0 + sig * (n - 1.0) + kap * n * (n - 1.0)
            inv_d = 1.0 / denom
            inv_d2 = inv_d * inv_d
            pred = lam * n * inv_d
            res = x_obs - pred
            g = [
                -lam * n * (n - 1.0) * inv_d2,
                -lam * n * n * (n - 1.0) * inv_d2,
                n * inv_d,
            ]
            for i in range(3):
                jtr[i] += g[i] * res
                for j in range(3):
                    jtj[i][j] += g[i] * g[j]

        for i in range(3):
            jtj[i][i] += damping * (jtj[i][i] + 1.0)

        step = _solve_3x3(jtj, jtr)
        cand = [params[i] + step[i] for i in range(3)]
        if not (0.0 <= cand[0] < 1.0 and cand[1] >= 0.0 and cand[2] > 0.0):
            damping *= 5.0
            continue
        cand_sse, _ = sse_and_preds(cand)
        if cand_sse < cur_sse:
            params = cand
            cur_sse = cand_sse
            damping = max(1e-12, damping * 0.3)
            if max(abs(s) for s in step) < 1e-12:
                break
        else:
            damping *= 5.0

    return UslModel(sigma=params[0], kappa=params[1], lam=params[2])


def sharded_pod_fleet_capacity(
    n_total: int,
    k_pods: int,
    alpha_pod: float,
    beta_pod: float,
    alpha_global_merge: float,
) -> float:
    """Effective relative capacity C_sharded(N; K) of K isolated worktree pods + global merge gate.

    When `n_total < k_pods`, only `n_total` pods run 1 agent each (`n_per_pod = 1.0`, zero
    intra-pod contention/coherency, `raw_parallel = float(n_total)`), avoiding unphysical
    negative `(n_per_pod - 1)` contention terms for sub-unit pod occupancy.
    """
    if n_total < 1 or k_pods < 1:
        raise ValueError(f"n_total ({n_total}) and k_pods ({k_pods}) must be >= 1")
    if n_total <= k_pods:
        raw_parallel = float(n_total)
    else:
        n_per_pod = n_total / k_pods
        pod_denom = (
            1.0 + alpha_pod * (n_per_pod - 1.0) + beta_pod * n_per_pod * (n_per_pod - 1.0)
        )
        raw_parallel = k_pods * (n_per_pod / pod_denom)
    return raw_parallel / (1.0 + alpha_global_merge * max(0.0, raw_parallel - 1.0))


def run_probe_4() -> dict[str, object]:
    # 0. Verify domain guards (`sigma >= 1.0`, `kappa == 0.0` L'Hopital limit, `n_total < k_pods`)
    try:
        UslModel(sigma=1.0, kappa=0.01, lam=1.0)
        raise AssertionError("Expected ValueError for sigma >= 1.0")
    except ValueError:
        pass

    amdahl = UslModel(sigma=0.05, kappa=0.0, lam=10.0)
    assert math.isinf(amdahl.n_opt_continuous())
    r_amd_10 = amdahl.latency_at_concurrency(10.0)
    x_amd_10 = amdahl.throughput_at_concurrency(10.0)
    assert abs(amdahl.concurrency_at_latency(r_amd_10) - 10.0) < 1e-12
    assert abs(amdahl.throughput_at_latency_exact(r_amd_10) - x_amd_10) < 1e-12
    # Verify n_total < k_pods guard: 2 agents across 4 pods = 2 single-agent pods -> raw 2 / (1 + alpha_global)
    assert abs(sharded_pod_fleet_capacity(2, 4, 0.04, 0.006, 0.015) - (2.0 / 1.015)) < 1e-12

    # 1. Exact reproduction of codahale/usl Cisco 32-point LM fit (`model_test.go:18-52, 159-192`)
    cisco = fit_usl_levenberg_marquardt(CODAHALE_CISCO_FIXTURE)
    assert abs(cisco.sigma - 0.02671591) < 1e-6
    assert abs(cisco.kappa - 7.690945e-4) < 1e-8
    assert abs(cisco.lam - 995.648772) < 1e-3
    assert cisco.max_concurrency_floor() == 35.0
    assert abs(cisco.throughput_at_concurrency(35.0) - 12341.745655) < 1e-2

    # 2. Prove & repair the upstream Schwartz Eq. 9 / codahale/usl `ThroughputAtLatency` sign bug!
    # (a) Degenerate slice tested in `model_test.go:99-107` (Sigma = Kappa = 0.06, Lambda = 40):
    deg = UslModel(sigma=0.06, kappa=0.06, lam=40.0)
    assert abs(deg.throughput_at_latency_codahale_buggy(0.03) - 69.38886664887109) < 1e-9
    assert abs(deg.throughput_at_latency_exact(0.03) - 69.38886664887109) < 1e-9

    # (b) Non-degenerate Cisco model (Sigma != Kappa): `model.go:63-66` fails Little's Law by 34.74x at N=1!
    r_at_n1 = cisco.latency_at_concurrency(1.0)
    x_buggy_n1 = cisco.throughput_at_latency_codahale_buggy(r_at_n1)
    x_exact_n1 = cisco.throughput_at_latency_exact(r_at_n1)
    ratio_bug_n1 = x_buggy_n1 / cisco.lam
    assert abs(ratio_bug_n1 - (cisco.sigma / cisco.kappa)) < 1e-9
    assert abs(x_exact_n1 - cisco.lam) < 1e-9

    # Verify exact Little's Law round-trip across N in [1..64] and both R_-(X), R_+(X) nose branches
    repo_fleet = UslModel(sigma=0.04, kappa=0.006, lam=1.0)
    for n in range(1, 65):
        r_n = repo_fleet.latency_at_concurrency(float(n))
        x_n = repo_fleet.throughput_at_concurrency(float(n))
        assert abs(repo_fleet.concurrency_at_latency(r_n) - float(n)) < 1e-10
        assert abs(repo_fleet.throughput_at_latency_exact(r_n) - x_n) < 1e-10

    r_sub, r_super = repo_fleet.latency_branches_at_throughput(4.0)
    assert r_sub < repo_fleet.latency_at_concurrency(repo_fleet.n_opt_continuous()) < r_super
    assert abs(repo_fleet.throughput_at_latency_exact(r_sub) - 4.0) < 1e-10
    assert abs(repo_fleet.throughput_at_latency_exact(r_super) - 4.0) < 1e-10

    # 3. K-way worktree pod sharding knee shift (K = 1 vs K = 4 on N in [1..64])
    unsharded_peaks = max(
        ((n, sharded_pod_fleet_capacity(n, 1, 0.04, 0.006, 0.0)) for n in range(1, 65)),
        key=lambda item: item[1],
    )
    sharded4_peaks = max(
        ((n, sharded_pod_fleet_capacity(n, 4, 0.04, 0.006, 0.015)) for n in range(1, 65)),
        key=lambda item: item[1],
    )
    assert unsharded_peaks[0] == 13 and sharded4_peaks[0] in (50, 51)
    assert sharded4_peaks[1] > 2.8 * unsharded_peaks[1]

    # 4. Noisy fleet telemetry -> online USL fit -> Agrawal-Carey-Livny multiprogramming cap recovery
    rng = random.Random(50505)
    true_fleet = UslModel(sigma=0.04, kappa=0.006, lam=10.0)
    noisy_obs = []
    for n in (1, 2, 4, 6, 8, 10, 12, 16, 20, 24, 32):
        clean_x = true_fleet.throughput_at_concurrency(float(n))
        noise = 1.0 if n == 1 else (1.0 + rng.gauss(0.0, 0.015))
        noisy_obs.append((float(n), clean_x * noise))

    ols_fit = fit_usl_ols_linearized(noisy_obs)
    lm_fit = fit_usl_levenberg_marquardt(noisy_obs)
    true_cap = int(true_fleet.max_concurrency_floor())  # 12
    assert abs(int(lm_fit.max_concurrency_floor()) - true_cap) <= 1
    assert abs(int(ols_fit.max_concurrency_floor()) - true_cap) <= 1

    return {
        "cisco_fit": {
            "sigma": cisco.sigma,
            "kappa": cisco.kappa,
            "lambda": cisco.lam,
            "n_max_floor": int(cisco.max_concurrency_floor()),
            "x_max": cisco.throughput_at_concurrency(cisco.max_concurrency_floor()),
        },
        "nose_sign_bug_audit": {
            "deg_sigma_eq_kappa_r003_buggy": deg.throughput_at_latency_codahale_buggy(0.03),
            "deg_sigma_eq_kappa_r003_exact": deg.throughput_at_latency_exact(0.03),
            "cisco_n1_true_lambda": cisco.lam,
            "cisco_n1_codahale_buggy": x_buggy_n1,
            "cisco_n1_exact_repaired": x_exact_n1,
            "cisco_n1_error_factor": ratio_bug_n1,
            "repo_nose_x4_r_sub": r_sub,
            "repo_nose_x4_r_super": r_super,
        },
        "pod_sharding": {
            "k1_peak_n": unsharded_peaks[0],
            "k1_peak_c": unsharded_peaks[1],
            "k4_peak_n": sharded4_peaks[0],
            "k4_peak_c": sharded4_peaks[1],
        },
        "noisy_cap_recovery": {
            "true_cap": true_cap,
            "ols_cap": int(ols_fit.max_concurrency_floor()),
            "lm_cap": int(lm_fit.max_concurrency_floor()),
            "lm_sigma": lm_fit.sigma,
            "lm_kappa": lm_fit.kappa,
        },
    }


# ============================================================================
# Deterministic Report Printer & Entrypoint
# ============================================================================


def main() -> int:
    p1 = run_probe_1()
    p2 = run_probe_2()
    p3 = run_probe_3()
    p4 = run_probe_4()

    print("================================================================================")
    print("CONCURRENT AGENT FLEET COORDINATION ECONOMICS — DETERMINISTIC PROBE SUITE")
    print("================================================================================")

    print("\n--- PROBE 1: Admission Control vs. Ordered Async Advisory ---")
    print(f"Verification Classes: {BANNERS['analytical']} + {BANNERS['simulation']}")
    print(
        "Regime                 L_sync   NoCheck  SyncGate  AsyncTri  AsyncAbt  TwoTierEq  TwoTierCasc  LR_+ / Lat* / Tok*"
    )
    for r in p1["scenarios"]:
        print(
            f"{r['name']:20s} {r['l_sync_s']:7.2f}s {r['none_lat_s']:8.2f}s "
            f"{r['sync_lat_s']:8.2f}s {r['async_triage_lat_s']:8.2f}s "
            f"{r['async_abort_lat_s']:8.2f}s {r['two_tier_eq_lat_s']:9.2f}s "
            f"{r['two_tier_casc_lat_s']:11.2f}s  "
            f"{r['lr_plus']:4.1f} / {r['lr_star_lat']:4.1f} / {r['lr_star_tok']:5.1f}"
        )
    print(
        f"Max |MC - Analytic| excess-latency error (20,000 stratified CRN trials): "
        f"{p1['max_mc_abs_err_s']:.4f}s; Max M/G/1 Lindley vs P-K rel err: {100.0 * p1['max_pk_rel_err']:.2f}%"
    )
    ot = p1["omega_thresholds"]
    print(
        f"Token-weight omega_tok^* crossovers (uncongested_llm_gate): "
        f"Sync<Async above {ot['omega_star_single']:.2f} s/tok; "
        f"Sync<TwoTierEq above {ot['omega_star_two_tier_eq']:.2f} s/tok; "
        f"Sync<TwoTierCasc above {ot['omega_star_two_tier_casc']:.2f} s/tok"
    )
    print(
        "Token-weight J(omega_tok) winners (single / equal-recall / all): "
        + ", ".join(
            f"w={item['omega_tok']:.0f}->{item['winner_single_tier']}/{item['winner_equal_recall']}/{item['winner_overall']}"
            for item in p1["omega_sweep"]
        )
    )
    sj = p1["shared_mg1_judge_congested"]
    print(
        f"Shared M/G/1 Semantic Judge (congested rho={sj['rho_full']:.2f} -> Tier-2 rho={sj['rho_tier2']:.4f}, "
        f"dt_async {sj['dt_async_full_s']:.2f}s -> {sj['dt_async_tier2_s']:.2f}s): "
        f"SyncGate={sj['sync_lat_s']:.2f}s, AsyncShared={sj['async_shared_lat_s']:.2f}s, "
        f"TwoTierEqShared={sj['two_tier_eq_shared_lat_s']:.2f}s, "
        f"TwoTierCascShared={sj['two_tier_casc_shared_lat_s']:.2f}s"
    )
    lc = p1["livelock_control"]
    print(
        f"CoAgent Livelock Control: UnorderedBilateral terminated={lc['bilateral_terminated']} "
        f"(steps={lc['bilateral_steps_hit_cap']}, state=({lc['bilateral_state_at_cap'][0]:.3e}, "
        f"{lc['bilateral_state_at_cap'][1]:.3e})) vs. MTPO (<_sigma) heals={lc['mtpo_heals']}, "
        f"state={lc['mtpo_final_state']}"
    )

    print("\n--- PROBE 2A: M/G/k Hedging, JSQ-2 Separation, Pure Z=0 S&X Blowup & Retry Storm ---")
    print(f"Verification Classes: {BANNERS['analytical']} + {BANNERS['simulation']}")
    vc = p2["vulimiri_exp_crossover"]
    print(
        f"Vulimiri Exp(1) Uncancelled d=2 Crossover (rho* = 1/3): "
        f"rho=0.22 Single={vc['rho_022_single']:.3f} > Rep2={vc['rho_022_nocancel_d2']:.3f}; "
        f"rho=0.42 Single={vc['rho_042_single']:.3f} < Rep2={vc['rho_042_nocancel_d2']:.3f}"
    )
    print("S&X Straggler Load=0.80  MeanResp    P95Resp    P99Resp   P99.9Resp  ExtraStarts  Unstable")
    for pol_key, summaries in p2["sx_mgk"].items():
        s80 = summaries[2]
        print(
            f"{pol_key:22s} {s80.mean_resp:9.2f}  {s80.p95_resp:9.2f}  "
            f"{s80.p99_resp:9.2f}  {s80.p999_resp:10.2f}  {s80.extra_start_pct:10.1f}%  "
            f"{str(s80.unstable_blowup):>8s}"
        )
    print(
        f"True Redundancy Gain over JSQ-2 (HedgedP95_JSQ2 vs Single_JSQ2 at rho=0.80): "
        f"-{p2['p99_reduction_p95_jsq2_over_single_jsq2_pct']:.1f}% P99"
    )
    sxu = p2["sx_uniform_coc_blowup"]
    print(
        f"Gardner S&X Uniform[1,2] Z=0 Instant-CoC Blowup (n={sxu['n_jobs']}, d=k=2 lockstep rho_max={sxu['lockstep_d2_k2_rho_max']:.4f}, "
        f"k=12 tested rho={sxu['rho']:.2f}): SingleRand1={sxu['single_random1_mean']:.2f}, "
        f"SingleJSQ2={sxu['single_jsq2_mean']:.2f}, EagerCoC_d2={sxu['eager_coc_d2_mean']:.2f} "
        f"(unstable={sxu['eager_coc_d2_unstable']}), HedgedP95_CoC={sxu['hedged_p95_coc_mean']:.2f}, "
        f"HedgedP95_JSQ2={sxu['hedged_p95_jsq2_mean']:.2f}"
    )

    print("\n--- PROBE 2B: Knight-Leveson-Redux (48 Versions) & Eckhardt-Lee Covariance ---")
    print(f"Verification Classes: {BANNERS['pinned_algo']} + {BANNERS['analytical']}")
    kl = p2["kl_redux"]
    for sl_name, sl in kl["kl_table_iii"].items():
        print(
            f"KL Slice {sl_name:6s}: N={int(sl['n']):2d}, mu={sl['mu']:6.2f}, "
            f"K={int(sl['K']):3d}, z={sl['z']:6.2f}"
        )
    tr = kl["triples"]
    print(
        f"C(48,3)={tr['total']} Majority-Vote Triples: mean {tr['single_mean']:.2f}->{tr['triple_mean']:.2f}, "
        f"P99 {tr['single_p99']:.0f}->{tr['triple_p99']:.0f}, max {tr['single_max']}->{tr['triple_max']}, "
        f"K=0 {tr['zero_triples']}/{tr['total']} (68.48%), beat_best={tr['beat_best']}, "
        f"worse_than_best={tr['worse_than_best']}"
    )
    phi = kl["pairwise_phi1"]
    print(
        f"Exact phi=1.0 Failing Pairs: cross-lang={phi['cross_lang'][0]}/{phi['cross_lang'][1]}, "
        f"cross-agent={phi['cross_agent'][0]}/{phi['cross_agent'][1]}"
    )
    el = kl["eckhardt_lee"]
    print(
        f"Eckhardt-Lee E[theta_A theta_B] = mu_A*mu_B + Cov: "
        f"Homog Cov={el['homogeneous']['cov']:+.6f} | "
        f"SharedShortcut Cov={el['shared_shortcut']['cov']:+.6f} | "
        f"OrthogonalCritic Cov={el['orthogonal_critic']['cov']:+.6f}"
    )

    print("\n--- PROBE 3: NK Landscape Topologies & Derex-Boyd Recombinant Breakthrough ---")
    print(f"Verification Classes: {BANNERS['simulation']} + {BANNERS['analytical']}")
    print("NK Rugged (K=5, N=10)     t=3 Score  t=3 Uniq  t=55 Score  GlobalOptHitRate")
    for topo_name, st in p3["nk_k5"].items():
        print(
            f"{topo_name:24s} {st['t3_score']:9.4f}  {st['t3_uniq']:8.2f}  "
            f"{st['end_score']:10.4f}  {100.0 * st['global_opt_hits']:15.1f}%"
        )
    db = p3["derex_boyd"]
    print(
        f"Derex-Boyd Symmetric Sync Recombinant: FullyConnected both_A3_B3={db['fully_connected']['both_a3_b3_pct']:.1f}%, "
        f"R4={db['fully_connected']['r4_breakthrough_pct']:.1f}%, payoff={db['fully_connected']['mean_group_max_payoff']:.2f} "
        f"vs. IsolatedPods+Migration both_A3_B3={db['isolated_pods_with_migration']['both_a3_b3_pct']:.1f}%, "
        f"R4={db['isolated_pods_with_migration']['r4_breakthrough_pct']:.1f}% ({db['r4_ratio']:.2f}x), "
        f"payoff={db['isolated_pods_with_migration']['mean_group_max_payoff']:.2f}"
    )

    print("\n--- PROBE 4: USL Retrograde Knees, Nose-Curve Sign Audit & Online Cap Fit ---")
    print(f"Verification Classes: {BANNERS['pinned_algo']} + {BANNERS['analytical']}")
    cf = p4["cisco_fit"]
    nb = p4["nose_sign_bug_audit"]
    ps = p4["pod_sharding"]
    nc = p4["noisy_cap_recovery"]
    print(
        f"codahale/usl Cisco 32-pt LM Fit (model_test.go:159-192): sigma={cf['sigma']:.8f}, "
        f"kappa={cf['kappa']:.7e}, lambda={cf['lambda']:.4f}, N_max={cf['n_max_floor']}, X_max={cf['x_max']:.2f}"
    )
    print(
        f"Schwartz Eq.9 / codahale model.go:63-66 Sign-Bug Audit (model_test.go:99-107 blind spot): "
        f"at sigma=kappa=0.06 buggy={nb['deg_sigma_eq_kappa_r003_buggy']:.6f} == exact={nb['deg_sigma_eq_kappa_r003_exact']:.6f}; "
        f"at Cisco N=1 buggy={nb['cisco_n1_codahale_buggy']:.2f} ({nb['cisco_n1_error_factor']:.2f}x error!) "
        f"vs. exact={nb['cisco_n1_exact_repaired']:.2f}"
    )
    print(
        f"Folded-Back Nose Branches at X=4.0 (alpha=0.04, beta=0.006): "
        f"R_sub={nb['repo_nose_x4_r_sub']:.4f}s vs. R_retrograde={nb['repo_nose_x4_r_super']:.4f}s"
    )
    print(
        f"Worktree Pod Sharding: K=1 peak N*={ps['k1_peak_n']} (C={ps['k1_peak_c']:.2f}x) -> "
        f"K=4 peak N*={ps['k4_peak_n']} (C={ps['k4_peak_c']:.2f}x); "
        f"Noisy Cap Recovery: true={nc['true_cap']}, OLS={nc['ols_cap']}, LM={nc['lm_cap']} "
        f"(sigma_hat={nc['lm_sigma']:.4f}, kappa_hat={nc['lm_kappa']:.5f})"
    )

    digest_summary = {
        "all_assertions_passed": True,
        "p1_two_tier_eq_shared_congested_s": round(
            p1["shared_mg1_judge_congested"]["two_tier_eq_shared_lat_s"], 4
        ),
        "p2a_p99_red_vs_jsq2_pct": round(
            p2["p99_reduction_p95_jsq2_over_single_jsq2_pct"], 2
        ),
        "p2b_kl_all_z": round(p2["kl_redux"]["kl_table_iii"]["all"]["z"], 4),
        "p3_derex_boyd_r4_ratio": round(p3["derex_boyd"]["r4_ratio"], 2),
        "p4_cisco_n1_bug_factor": round(nb["cisco_n1_error_factor"], 4),
    }
    print("\nJSON_RECEIPT:", json.dumps(digest_summary, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
