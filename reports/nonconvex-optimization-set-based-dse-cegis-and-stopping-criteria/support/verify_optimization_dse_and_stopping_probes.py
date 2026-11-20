#!/usr/bin/env python3
"""Self-contained executable verification probes for non-convex population topologies,
set-based / multi-fidelity / non-convex Pareto design space exploration, CEGIS
expressiveness overfitting, capture-recapture small-team breakdowns, and T x B
multi-branch adaptive holdout reuse.

Requires only the Python 3.10+ standard library; deterministic under fixed seeds.
"""

from __future__ import annotations

import math
import random
from fractions import Fraction
from typing import Dict, List, Tuple


def probe_1_island_vs_panmictic_and_baldwinian() -> Dict[str, object]:
    """Verify:
    (a) Whitley, Rana & Heckendorn (1999) separable deceptive-trap island break-even
        1 - (1 - X_{t/M})^M > Y_t and Lässig & Sudholt (2011, Thm 5) Eulerian-cycle
        plateau error decay 3^{-mu};
    (b) Sudholt (2009, Thm 3) memetic local-search depth overshoot into a deceptive sink.
    """
    # (a) Suppose a single panmictic population is drawn into a wide deceptive basin 88%
    # of the time regardless of N_total >= 80 (Y_t = 0.12), while smaller islands (N/M)
    # experience finite-sample symmetry breaking (X_{t/M} = 0.14).
    y_pan = 0.12
    x_isl = 0.14
    m_breakeven = math.log(1.0 - y_pan) / math.log(1.0 - x_isl)
    island_probs = {f"M={m}": round(1.0 - (1.0 - x_isl) ** m, 4) for m in [1, 2, 5, 10, 20]}

    # Lässig & Sudholt (2011, Thms 4-5): wrong shortcut probability (1/3)^mu when tau >= m^3
    m_edges = 20
    euler_fail = {f"mu={mu}": round((1.0 / 3.0) ** mu, 6) for mu in [1, 3, 5, 8]}

    # (b) Toy f_D ridge (D=4): ridge positions r=0..8 have fitness 10*r, except at portal r=4
    # where a 2-step global jump reaches global optimum G (fitness 100), whereas continuing
    # local search along the ridge to r=8 reaches deceptive dead-end sink (fitness 80, isolated
    # by width-5 barrier from G).
    def ridge_outcome(delta: int) -> str:
        pos = min(delta, 8)
        if pos < 4:
            return f"under-reach (pos={pos}, fit={10*pos}, misses portal at r=4)"
        if pos == 4:
            return "portal-window (pos=4, fit=40 -> 2-flip reaches global opt fit=100)"
        return f"overshoot-sink (pos={pos}, fit={10*pos}, trapped away from portal)"

    return {
        "whitley_breakeven_M": round(m_breakeven, 4),
        "whitley_island_subproblem_solve_prob": island_probs,
        "lassig_sudholt_euler_all_islands_trapped_prob": euler_fail,
        "sudholt_memetic_depth_regimes": {f"delta={d}": ridge_outcome(d) for d in [2, 4, 8]},
    }


def probe_2_pareto_das_dennis_and_frankenstein_union() -> Dict[str, object]:
    """Verify Das & Dennis (1997), Miettinen (1999) Augmented Weighted Tchebycheff &
    epsilon-constraint, and strict Pareto dominance of naive feature-union synthesis.
    """
    # 1. Continuous non-convex front: f1 in [0, 1], f2 = sqrt(1 - f1^2) (concave toward origin!)
    grid = [(i / 200.0, math.sqrt(max(0.0, 1.0 - (i / 200.0) ** 2))) for i in range(201)]
    ws_interior = 0
    atch_interior = 0
    for k in range(1, 20):
        w = k / 20.0
        best_ws = min(grid, key=lambda p: w * p[0] + (1.0 - w) * p[1])
        if 0.02 < best_ws[0] < 0.98:
            ws_interior += 1
        best_atch = min(
            grid,
            key=lambda p: max(w * p[0], (1.0 - w) * p[1]) + 0.01 * (p[0] + p[1]),
        )
        if 0.02 < best_atch[0] < 0.98:
            atch_interior += 1

    # 2. Convex front f2 = 1 / f1 on [0.1, 10.0]: uniform weights alpha in {0.05..0.95}
    upper_half_hits = 0
    for k in range(1, 20):
        alpha = k / 20.0
        # Minimize (1 - alpha)*f1 + alpha*(1/f1) -> f1* = sqrt(alpha / (1 - alpha))
        f1_star = math.sqrt(alpha / (1.0 - alpha))
        f1_clamped = min(max(f1_star, 0.1), 10.0)
        if f1_clamped >= 5.05:
            upper_half_hits += 1

    # 3. Discrete architectural synthesis: (f_prim, f_enc)
    cands = {
        "M_alpha": (2.0, 9.0),
        "M_beta": (9.0, 2.0),
        "M_star": (6.0, 6.0),
        "M_union": (10.0, 3.0),
    }
    dominated_by: Dict[str, List[str]] = {}
    for name, (a1, a2) in cands.items():
        doms = [
            other
            for other, (b1, b2) in cands.items()
            if other != name and b1 <= a1 and b2 <= a2 and (b1 < a1 or b2 < a2)
        ]
        dominated_by[name] = doms

    ws_winners = set()
    for i in range(1001):
        w = i / 1000.0
        win = min(cands.items(), key=lambda kv: w * kv[1][0] + (1.0 - w) * kv[1][1])[0]
        ws_winners.add(win)

    atch_winner = min(
        cands.items(),
        key=lambda kv: max(0.5 * kv[1][0], 0.5 * kv[1][1]) + 0.01 * (kv[1][0] + kv[1][1]),
    )[0]
    eps_winner = min(
        ((k, v) for k, v in cands.items() if v[1] <= 6.5),
        key=lambda kv: kv[1][0],
    )[0]

    return {
        "nonconvex_circle_ws_interior_of_19": ws_interior,
        "nonconvex_circle_aug_tchebycheff_interior_of_19": atch_interior,
        "convex_1_over_f1_upper_half_hits_of_19": upper_half_hits,
        "architectural_dominated_by": dominated_by,
        "linear_rubric_winners_across_1001_weights": sorted(ws_winners),
        "aug_tchebycheff_balanced_winner": atch_winner,
        "epsilon_constraint_winner": eps_winner,
    }


def probe_3_multifidelity_mfmc_and_hyperband_inversion() -> Dict[str, object]:
    """Verify Peherstorfer et al. (2016; 2018) MFMC variance-reduction threshold
    rho^2 > 4r / (1 + r)^2 vs sample-allocation threshold rho^2 > r / (1 + r),
    and Hyperband crossing-curve rank inversion salvaged only by bracket s=0.
    """
    mfmc_table = {}
    for r in [0.01, 0.05, 0.10, 0.25, 0.50]:
        rho_alloc = math.sqrt(r / (1.0 + r))
        rho_mse = math.sqrt(4.0 * r / ((1.0 + r) ** 2))
        mfmc_table[f"r={r:.2f}"] = {
            "min_abs_rho_for_m1_gt_m0": round(rho_alloc, 4),
            "min_abs_rho_for_mse_gain": round(rho_mse, 4),
        }

    # Simulate Successive Halving (s=2, R=9, eta=3, n=9 arms) on crossing learning curves:
    # Arm 0 (deep unification): loss(r) = 0.90 / r  -> r=1: 0.90, r=3: 0.30, r=9: 0.10 (GLOBAL BEST!)
    # Arms 1..8 (shallow cliches): loss(r) = 0.35 + 0.02*i / r -> r=1: ~0.37..0.51, r=9: ~0.35..0.37
    def loss(arm: int, r: int) -> float:
        if arm == 0:
            return 0.90 / r
        return 0.35 + (0.02 * arm) / r

    survivors = list(range(9))
    r_stage = 1
    sh_trace = {}
    for stage in range(3):
        scored = sorted((loss(a, r_stage), a) for a in survivors)
        sh_trace[f"r={r_stage}"] = [a for _, a in scored]
        if stage < 2:
            survivors = [a for _, a in scored[: len(survivors) // 3]]
            r_stage *= 3

    return {
        "mfmc_thresholds": mfmc_table,
        "sh_crossing_curve_arm0_eliminated_at_r1": 0 not in sh_trace["r=3"],
        "sh_winner_arm_and_final_loss": (survivors[0], round(loss(survivors[0], 9), 4)),
        "true_best_arm0_final_loss": round(loss(0, 9), 4),
    }


def probe_4_padhi_cegis_overfitting_omega() -> Dict[str, object]:
    """Verify Padhi et al. (CAV 2019, Theorem 5): expanding grammar from linear/affine E_1
    to point-guard `ite` E_2 explodes Potential for Overfitting Omega(S, Z) on finite
    counterexamples Z.
    Target spec over X = {0..7}: f*(x) = 2*x + 1 (mod 16).
    """
    domain = list(range(8))
    target = {x: (2 * x + 1) % 16 for x in domain}

    # E_1: affine functions a*x + b mod 16 (16 * 16 = 256 candidates)
    e1 = [tuple((a * x + b) % 16 for x in domain) for a in range(16) for b in range(16)]
    # E_2: E_1 union 1-point and 2-point `ite` exception patches on top of x -> 0 or affine
    # Specifically consider all functions agreeing with some affine base except up to 2 point overrides:
    e2_set = set(e1)
    for a in range(4):
        for b in range(4):
            base = [(a * x + b) % 16 for x in domain]
            for idx1 in domain:
                for v1 in range(16):
                    cand = list(base)
                    cand[idx1] = v1
                    e2_set.add(tuple(cand))
    e2 = list(e2_set)
    truth_vec = tuple(target[x] for x in domain)

    omega_curve = {}
    for m in [1, 2, 3, 4]:
        z = domain[:m]
        om1 = sum(1 for fn in e1 if fn != truth_vec and all(fn[x] == target[x] for x in z))
        om2 = sum(1 for fn in e2 if fn != truth_vec and all(fn[x] == target[x] for x in z))
        omega_curve[f"|Z|={m}"] = {"Omega_E1_affine": om1, "Omega_E2_with_ite": om2}
    return omega_curve


def probe_5_capture_recapture_small_k_impossibility() -> Dict[str, object]:
    """Verify Burnham-Overton jackknife weights and the k=2,3 zero-overlap (f2=0) and
    full-overlap (f1=0) failure modes from Briand et al. (2000) & Petersson et al. (2004).
    """
    # Exact rational verification of Burnham-Overton J1 and J2 at t=2 and t=3
    def j1(d: int, f1: int, t: int) -> Fraction:
        return Fraction(d) + Fraction(t - 1, t) * Fraction(f1)

    def j2(d: int, f1: int, f2: int, t: int) -> Fraction:
        return (
            Fraction(d)
            + Fraction(2 * t - 3, t) * Fraction(f1)
            - Fraction((t - 2) ** 2, t * (t - 1)) * Fraction(f2)
        )

    # Case A: N=20 subtle bugs, p=0.10 per critic, k=2 critics
    n_true = 20
    p_low = 0.10
    prob_f2_zero_k2 = (1.0 - p_low**2) ** n_true
    # When D=4, f1=4, f2=0 (n1=2, n2=2):
    j2_at_d4_f2_0 = float(j2(4, 4, 0, 2))
    chapman_at_2_2_0 = ((2 + 1) * (2 + 1)) / (0 + 1) - 1

    # Case B: Bimodal N=20 (6 easy at p=0.90, 14 shared-blind-spot hard at p=0.02), k=2 critics
    prob_exact_6_full_overlap = ((0.90**2) ** 6) * (((1.0 - 0.02) ** 2) ** 14)
    # When D=6, f1=0, f2=6:
    all_estimators_f1_0 = {
        "LP": (6 * 6) / 6,
        "Chapman": ((6 + 1) * (6 + 1)) / (6 + 1) - 1,
        "Chao1": 6 + (0**2) / (2 * 6),
        "J1_k2": float(j1(6, 0, 2)),
        "J2_k2": float(j2(6, 0, 6, 2)),
        "true_missed_f0": 14,
    }
    return {
        "case_A_N20_p0.10_k2_prob_zero_overlap": round(prob_f2_zero_k2, 4),
        "case_A_D4_f2_0_Mh_JK_estimate": j2_at_d4_f2_0,
        "case_A_D4_f2_0_Chapman_estimate": chapman_at_2_2_0,
        "case_B_bimodal_N20_k2_prob_exact_f1_0_on_6_easy": round(prob_exact_6_full_overlap, 4),
        "case_B_all_estimators_when_f1_0": all_estimators_f1_0,
    }


def probe_6_txb_adaptive_holdout_overfitting(
    trials: int = 2000,
    seed: int = 20261120,
) -> Dict[str, Dict[str, float]]:
    """Verify Dwork et al. (2015) / Blum & Hardt (2015) / Feldman et al. (2019) across
    T rounds x B branches on a small held-out set of size n (true population acc = 0.50).
    """
    rng = random.Random(seed)
    configs = [(12, 3, 4), (12, 5, 4), (20, 3, 4), (50, 5, 4)]
    beta = 0.05
    out: Dict[str, Dict[str, float]] = {}

    for n, t_rounds, b_branches in configs:
        k_tot = t_rounds * b_branches
        bound_end_only = math.sqrt(math.log(2.0 * k_tot / beta) / (2.0 * n))
        bound_winner_idx = math.sqrt((t_rounds * math.log(b_branches) + math.log(2.0 / beta)) / (2.0 * n))

        # Simulate FFH correlation-weighted boosting attack using (T-1)*B scalar queries + final synthesis
        q_explore = max(k_tot - 1, 1)
        emp_accs = []
        for _ in range(trials):
            # Target labels y in {-1, +1}^n
            y = [1 if rng.random() < 0.5 else -1 for _ in range(n)]
            hyps = [[1 if rng.random() < 0.5 else -1 for _ in range(n)] for _ in range(q_explore)]
            weights = []
            for h in hyps:
                acc = sum(1 for i in range(n) if h[i] == y[i]) / n
                weights.append(acc - 0.5)
            h_star = [
                1 if sum(weights[q] * hyps[q][i] for q in range(q_explore)) >= 0 else -1
                for i in range(n)
            ]
            emp_accs.append(sum(1 for i in range(n) if h_star[i] == y[i]) / n)

        mean_emp = sum(emp_accs) / trials
        out[f"n={n},T={t_rounds},B={b_branches}"] = {
            "regime_a_end_only_tau": round(bound_end_only, 4),
            "regime_b_winner_idx_tau": round(bound_winner_idx, 4),
            "regime_c_ffh_empirical_holdout_acc": round(mean_emp, 4),
            "regime_c_ffh_overfit_bias": round(mean_emp - 0.5, 4),
        }
    return out


def main() -> None:
    print("=== Probe 1: Island Symmetry-Breaking & Memetic Depth Phase Transition ===")
    for k, v in probe_1_island_vs_panmictic_and_baldwinian().items():
        print(f"  {k}: {v}")

    print("\n=== Probe 2: Das-Dennis Non-Convex Blind Spot & Frankenstein Union Dominance ===")
    for k, v in probe_2_pareto_das_dennis_and_frankenstein_union().items():
        print(f"  {k}: {v}")

    print("\n=== Probe 3: MFMC Cost-Correlation Bound & Hyperband Crossing-Curve Inversion ===")
    for k, v in probe_3_multifidelity_mfmc_and_hyperband_inversion().items():
        print(f"  {k}: {v}")

    print("\n=== Probe 4: Padhi et al. CEGIS `ite` Overfitting Potential Omega(S, Z) ===")
    for k, v in probe_4_padhi_cegis_overfitting_omega().items():
        print(f"  {k}: {v}")

    print("\n=== Probe 5: Capture-Recapture Small-k (f2=0 & f1=0) Failure Proofs ===")
    for k, v in probe_5_capture_recapture_small_k_impossibility().items():
        print(f"  {k}: {v}")

    print("\n=== Probe 6: Serial x Parallel (T x B) Holdout Reuse Overfitting ===")
    for k, v in probe_6_txb_adaptive_holdout_overfitting().items():
        print(f"  {k}: {v}")


if __name__ == "__main__":
    main()
