#!/usr/bin/env python3
"""Deterministic verification probes for agent scaffolding, prompt optimization,
and divergent design-space exploration.

Self-contained support script for the reference report package:
  reports/agent-scaffolding-automated-prompt-optimization-and-divergent-design-exploration/

Runtime constraints: Python 3.10+ standard library only, fixed seed 20261121,
zero network calls, bit-identical deterministic stdout, < 3s wall-clock runtime.

Epistemic labeling discipline (explicitly printed in stdout banners):
  - Probe 1 ([toy model / mechanistic surrogate]):
      Equal-footed comparison of AFlow visit-count-free top-k softmax
      (exact DataUtils._compute_probabilities & get_top_rounds logic from
      FoundationAgents/AFlow@3f457218fc71:scripts/optimizer_utils/data_utils.py)
      vs. flat uniform vs. visit-count Archive UCB under IDENTICAL unbounded
      expansion rules (zero asymmetric max_children oracle). Covers:
        * 1-step probabilities across Code (alpha=0.2, lambda=0.3, *100),
          Paper Sec. 3 Eq. 3 (alpha=0.4, lambda=0.2 on [0,100] and [0,1]),
          and Paper App. A Alg. 1 (alpha=0.2, lambda=0.4 on [0,100]);
        * Deceptive 2-basin archive (quantifying visit-count absence, top-k
          truncation, and get_top_rounds Round-1 eviction rate);
        * Stochastic-mutation unimodal ridge negative control where greedy
          exploitation strictly beats visit-count exploration.
  - Probe 2 ([toy model / mechanistic surrogate]):
      Exact port of GEPA remove_dominated_programs & TopKParetoCandidateSelector
      (gepa-ai/gepa@ce5b0d6e3d6a) in a simplified single-snapshot archive
      (explicitly omitting StrictImprovementAcceptance minibatch gating):
        * [A] Continuous Gaussian noise hierarchy;
        * [B] Binary {0,1} stochastic Bernoulli task-score hierarchy;
        * [C] Two-sided specialist-retention non-vacuity (1 generalist + 2 specialists);
        * [D] TopKPareto(K=5) generalist-crowding boundary (6 generalists + 2 specialists).
  - Probe 3 ([exact analytical / constructive witness]):
      Zwicky GMA + Ritchey CCA O(n^2) pruning (matching exact closed-form
      1 - (1 - p)^C(6,2) = 1 - (1 - p)^15 across 240 pairwise cells vs. 4,096
      configs) plus a constructive existence witness contrasting tradespace-blind
      vs. tradespace-informed normative filtering (explicitly verifying algebraic
      commutativity of any fixed univariate predicate with CCA).
  - Probe 4 ([exact analytical / toy model]):
      Discrete Bayesian Experimental Design (Static vs. Myopic EIG/cost vs.
      Myopic Raw EIG vs. Non-Myopic 2-Step DP) over 16 hypotheses & 8 probes:
        * [A] Well-specified exact analytic evaluation;
        * [B] Selective-confounder misspecification stress test reporting ALL
          four policies including Static (Opt Assumed) alongside diversified
          unconfounded static probing;
        * [C] Exact analytical 1D linear-assumed vs. quadratic-true witness of
          Rainforth et al. (2024) Sec. 5.3 repeated-extrema collapse.
"""

from __future__ import annotations

import itertools
import math
import random
import statistics
from dataclasses import dataclass
from typing import Mapping, Sequence

SEED = 20261121


def _clamp01(x: float) -> float:
    return 0.0 if x < 0.0 else (1.0 if x > 1.0 else x)


# =============================================================================
# Probe 1: AFlow Visit-Count-Free Top-k Softmax vs. Uniform vs. Archive UCB
# Exact probability & top-k selection logic audited from:
#   FoundationAgents/AFlow@3f457218fc716093fe53f6df8a5d5e6379d66346
#   scripts/optimizer_utils/data_utils.py L16-17, L40-109; run.py L68 (sample=4)
# =============================================================================


def aflow_compute_probabilities(
    raw_scores: Sequence[float],
    *,
    alpha: float,
    lambda_: float,
    scale_100: bool,
) -> list[float]:
    """Exact port of DataUtils._compute_probabilities (data_utils.py L78-109)."""
    n = len(raw_scores)
    if n == 0:
        raise ValueError("Score list is empty.")
    scores = [s * 100.0 if scale_100 else s for s in raw_scores]
    uniform_prob = 1.0 / n
    max_score = max(scores)
    exp_weights = [math.exp(alpha * (s - max_score)) for s in scores]
    sum_exp = sum(exp_weights)
    probs = [lambda_ * uniform_prob + (1.0 - lambda_) * (w / sum_exp) for w in exp_weights]
    total = sum(probs)
    return [p / total for p in probs]


def aflow_get_top_rounds(obs_scores: Sequence[float], sample: int) -> tuple[list[int], bool]:
    """Exact port of DataUtils.get_top_rounds (data_utils.py L40-59).

    Node index 0 represents Round 1 (the initial workflow seed). Because the
    upstream loop breaks as soon as `len(unique_rounds) >= sample` BEFORE
    checking `if 1 in unique_rounds:`, Round 1 is silently dropped whenever it
    falls outside the top `sample` scores.
    """
    ranked = sorted(range(len(obs_scores)), key=lambda i: obs_scores[i], reverse=True)
    selected = ranked[:sample]
    round1_present = 0 in selected
    if round1_present:
        # Upstream moves round 1 to index 0 when already inside the top-sample slice.
        selected = [0] + [i for i in selected if i != 0]
    return selected, (not round1_present)


def _categorical_sample(rng: random.Random, probs: Sequence[float]) -> int:
    u = rng.random()
    acc = 0.0
    for idx, p in enumerate(probs):
        acc += p
        if u <= acc:
            return idx
    return len(probs) - 1


@dataclass
class _ArchiveNode:
    node_id: int
    round_num: int
    kind: str
    true_mean: float
    obs_score: float
    visits: int = 1
    value_sum: float = 0.0
    expansions: int = 0

    def __post_init__(self) -> None:
        self.value_sum = self.obs_score


def _init_archive(landscape: str, rng: random.Random, noise_sd: float) -> list[_ArchiveNode]:
    if landscape == "deceptive":
        specs = [
            ("root", 0.45),
            ("trap", 0.62),
            ("b1", 0.50),
            ("decoy", 0.49),
            ("decoy", 0.48),
            ("decoy", 0.47),
        ]
    else:
        specs = [
            ("root", 0.45),
            ("ridge1", 0.60),
            ("decoy", 0.54),
            ("decoy", 0.53),
            ("decoy", 0.52),
            ("decoy", 0.51),
            ("decoy", 0.50),
            ("decoy", 0.49),
        ]
    nodes: list[_ArchiveNode] = []
    for idx, (kind, mu) in enumerate(specs):
        obs = _clamp01(rng.gauss(mu, noise_sd))
        nodes.append(_ArchiveNode(idx, idx + 1, kind, mu, obs))
    return nodes


def _spawn_archive_child(
    landscape: str,
    parent: _ArchiveNode,
    next_id: int,
    rng: random.Random,
    noise_sd: float,
    *,
    p_improve: float = 0.35,
) -> _ArchiveNode:
    """Identical unbounded expansion rule shared across ALL selectors."""
    parent.expansions += 1
    if landscape == "deceptive":
        # Basin A: trap (0.62) yields slightly worse local tweaks (0.56).
        # Basin B: b1 (0.50) -> 1st expansion b2 (0.54) -> 1st expansion opt (0.88).
        if parent.kind == "b1" and parent.expansions == 1:
            kind, mu = "b2", 0.54
        elif parent.kind == "b2" and parent.expansions == 1:
            kind, mu = "opt", 0.88
        elif parent.kind == "trap":
            kind, mu = "trap_sub", 0.56
        else:
            kind, mu = "leaf", max(0.42, parent.true_mean - 0.04)
    else:
        # Stochastic-mutation unimodal ridge: each mutation of the active ridge
        # node succeeds with probability p_improve, modeling noisy LLM edits.
        if parent.kind == "ridge1" and rng.random() < p_improve:
            kind, mu = "ridge2", 0.70
        elif parent.kind == "ridge2" and rng.random() < p_improve:
            kind, mu = "ridge3", 0.80
        elif parent.kind == "ridge3" and rng.random() < p_improve:
            kind, mu = "opt", 0.88
        else:
            kind, mu = "leaf", max(0.42, parent.true_mean - 0.05)

    obs = _clamp01(rng.gauss(mu, noise_sd))
    return _ArchiveNode(next_id, next_id + 1, kind, mu, obs)


def _run_probe1_equal_footed(
    *,
    landscape: str,
    mode: str,
    n_trials: int,
    horizon: int,
    noise_sd: float,
    seed: int,
    alpha: float = 0.2,
    lambda_: float = 0.3,
    scale_100: bool = True,
    top_k: int | None = None,
    ucb_c: float = 0.35,
) -> dict[str, float]:
    """Run all selectors on IDENTICAL unbounded archive expansion rules."""
    rng = random.Random(seed)
    discoveries = 0
    node1_picks = 0
    total_picks = 0
    root_dropped_steps = 0
    best_true_means: list[float] = []

    for _ in range(n_trials):
        nodes = _init_archive(landscape, rng, noise_sd)
        found_opt = False

        for _step in range(horizon):
            obs_list = [nd.obs_score for nd in nodes]
            if top_k is not None:
                cand_ids, r1_dropped = aflow_get_top_rounds(obs_list, sample=top_k)
                if r1_dropped:
                    root_dropped_steps += 1
            else:
                cand_ids = list(range(len(nodes)))

            if mode == "uniform":
                picked = rng.choice(cand_ids)
            elif mode == "ucb":
                total_visits = sum(nd.visits for nd in nodes)
                log_n = math.log(max(total_visits, 2))
                picked = max(
                    cand_ids,
                    key=lambda i: (nodes[i].value_sum / nodes[i].visits)
                    + ucb_c * math.sqrt(log_n / nodes[i].visits),
                )
            elif mode == "softmax":
                ranked = sorted(cand_ids, key=lambda i: nodes[i].obs_score, reverse=True)
                probs = aflow_compute_probabilities(
                    [nodes[i].obs_score for i in ranked],
                    alpha=alpha,
                    lambda_=lambda_,
                    scale_100=scale_100,
                )
                picked = ranked[_categorical_sample(rng, probs)]
            else:
                raise ValueError(mode)

            total_picks += 1
            if picked == 1:
                node1_picks += 1

            parent = nodes[picked]
            child = _spawn_archive_child(landscape, parent, len(nodes), rng, noise_sd)
            nodes.append(child)
            # Identical visit & empirical-mean update tracked for all runs
            parent.visits += 1
            parent.value_sum += child.obs_score
            if child.kind == "opt":
                found_opt = True

        if found_opt:
            discoveries += 1
        best_true_means.append(max(nd.true_mean for nd in nodes))

    return {
        "discovery_rate": discoveries / n_trials,
        "node1_conc": node1_picks / total_picks,
        "root_drop_rate": root_dropped_steps / total_picks,
        "mean_best_true": statistics.fmean(best_true_means),
    }


def run_probe1() -> None:
    print("=" * 78)
    print("PROBE 1 [toy model / mechanistic surrogate]: AFlow Top-k Softmax vs. Archive UCB")
    print("=" * 78)
    print("Equal-footed rule: ALL selectors share identical unbounded archive expansions")
    print("(no exclusive max_children oracle). Isolates visit-count penalty + top-k eviction.")

    sample_scores = [0.62, 0.50, 0.49, 0.48, 0.47, 0.45]
    p_code = aflow_compute_probabilities(sample_scores, alpha=0.2, lambda_=0.3, scale_100=True)
    p_eq3_pct = aflow_compute_probabilities(sample_scores, alpha=0.4, lambda_=0.2, scale_100=True)
    p_alg1_pct = aflow_compute_probabilities(sample_scores, alpha=0.2, lambda_=0.4, scale_100=True)
    p_eq3_unit = aflow_compute_probabilities(sample_scores, alpha=0.4, lambda_=0.2, scale_100=False)

    print("\n1-step selection distribution on scores [0.62, 0.50, 0.49, 0.48, 0.47, 0.45]:")
    print(f"  Code (a=0.2, l=0.3, [0,100]):          {[round(x, 4) for x in p_code]}")
    print(f"  Paper Sec.3 Eq.3 (a=0.4, l=0.2, *100): {[round(x, 4) for x in p_eq3_pct]}")
    print(f"  Paper App.A Alg.1 (a=0.2, l=0.4,*100): {[round(x, 4) for x in p_alg1_pct]}")
    print(f"  Paper Sec.3 Eq.3 raw [0,1] (no *100):  {[round(x, 4) for x in p_eq3_unit]}")

    n_trials = 1000
    selector_specs = [
        ("eq3_top4", "Paper Eq.3 Top-4 (a=0.4,l=0.2,*100)", dict(mode="softmax", alpha=0.4, lambda_=0.2, scale_100=True, top_k=4)),
        ("code_top4", "AFlow Code Top-4 (a=0.2,l=0.3,*100)", dict(mode="softmax", alpha=0.2, lambda_=0.3, scale_100=True, top_k=4)),
        ("code_full", "AFlow Code Full  (a=0.2,l=0.3,*100)", dict(mode="softmax", alpha=0.2, lambda_=0.3, scale_100=True, top_k=None)),
        ("uniform", "Flat Uniform (Full Archive)", dict(mode="uniform", top_k=None)),
        ("ucb_020", "Archive UCB (c=0.20, Full Archive)", dict(mode="ucb", ucb_c=0.20, top_k=None)),
        ("ucb_035", "Archive UCB (c=0.35, Full Archive)", dict(mode="ucb", ucb_c=0.35, top_k=None)),
    ]

    print(f"\n[A] Deceptive 2-Basin Archive (trap=0.62 vs 2-step opt=0.88 via b1=0.50; H=12, N={n_trials}):")
    deceptive_res: dict[str, dict[str, float]] = {}
    for idx, (key, label, kwargs) in enumerate(selector_specs):
        res = _run_probe1_equal_footed(
            landscape="deceptive",
            n_trials=n_trials,
            horizon=12,
            noise_sd=0.02,
            seed=SEED + 100 + idx,
            **kwargs,
        )
        deceptive_res[key] = res
        print(
            f"  {label:<36} | opt_disc={res['discovery_rate']*100:5.1f}% "
            f"| trap_conc={res['node1_conc']*100:5.1f}% "
            f"| r1_drop={res['root_drop_rate']*100:5.1f}% | E[best]={res['mean_best_true']:.4f}"
        )

    print(f"\n[B] NEGATIVE CONTROL — Stochastic-Mutation Unimodal Ridge (p_imp=0.35, H=10, N={n_trials}):")
    unimodal_res: dict[str, dict[str, float]] = {}
    for idx, (key, label, kwargs) in enumerate(selector_specs):
        res = _run_probe1_equal_footed(
            landscape="unimodal",
            n_trials=n_trials,
            horizon=10,
            noise_sd=0.02,
            seed=SEED + 200 + idx,
            **kwargs,
        )
        unimodal_res[key] = res
        print(
            f"  {label:<36} | opt_disc={res['discovery_rate']*100:5.1f}% "
            f"| ridge1_conc={res['node1_conc']*100:5.1f}% | E[best]={res['mean_best_true']:.4f}"
        )

    # Assertions: equal-footed separation in both regimes + Round-1 drop bug + [0,1] near-uniform check
    assert max(p_eq3_unit) - min(p_eq3_unit) < 0.015  # [0,1] Eq.3 collapses to near-uniform
    assert p_eq3_pct[0] > p_code[0] > p_alg1_pct[0]
    assert deceptive_res["code_top4"]["root_drop_rate"] > 0.95
    assert deceptive_res["code_top4"]["node1_conc"] > deceptive_res["code_full"]["node1_conc"]
    assert deceptive_res["ucb_035"]["discovery_rate"] > deceptive_res["uniform"]["discovery_rate"] > deceptive_res["code_full"]["discovery_rate"] > deceptive_res["eq3_top4"]["discovery_rate"]
    assert unimodal_res["eq3_top4"]["discovery_rate"] > unimodal_res["code_top4"]["discovery_rate"] > unimodal_res["ucb_020"]["discovery_rate"] > unimodal_res["ucb_035"]["discovery_rate"] > unimodal_res["uniform"]["discovery_rate"]
    print("  [PASS] Equal-footed visit-count separation, Round-1 top-k eviction, and stochastic-ridge reversal verified.\n")


# =============================================================================
# Probe 2: GEPA Per-Instance Pareto Frontier Noise Pollution & Crowding Limits
# Exact port of `remove_dominated_programs` & `TopKParetoCandidateSelector`:
#   gepa-ai/gepa@ce5b0d6e3d6af6c6dbec6de2c54536bbb961d309
#   src/gepa/gepa_utils.py L54-93 & src/gepa/strategies/candidate_selector.py L53-82
# =============================================================================


def remove_dominated_programs(
    program_at_pareto_front_valset: Mapping[int, set[int]],
    scores: Sequence[float] | None = None,
) -> dict[int, set[int]]:
    """Exact algorithm from gepa/gepa_utils.py L54-93."""
    program_fronts: dict[int, list[int]] = {}
    remaining_counts: dict[int, int] = {}
    for key, front in program_at_pareto_front_valset.items():
        remaining_counts[key] = len(front)
        for p in front:
            program_fronts.setdefault(p, []).append(key)

    dominated: set[int] = set()
    programs = list(program_fronts)
    score_map = dict.fromkeys(programs, 1.0) if scores is None else {p: scores[p] for p in programs}
    programs = sorted(programs, key=lambda x: score_map[x], reverse=False)

    for y in programs:
        fronts = program_fronts[y]
        if all(remaining_counts[key] > 1 for key in fronts):
            dominated.add(y)
            for key in fronts:
                remaining_counts[key] -= 1

    dominators = {p for p in programs if p not in dominated}
    return {
        val_id: {prog_idx for prog_idx in front if prog_idx in dominators}
        for val_id, front in program_at_pareto_front_valset.items()
    }


def _build_pareto_front_mapping(obs_matrix: Sequence[Sequence[float]]) -> dict[int, set[int]]:
    n_cands = len(obs_matrix)
    n_inst = len(obs_matrix[0])
    mapping: dict[int, set[int]] = {}
    for m in range(n_inst):
        best_val = max(obs_matrix[c][m] for c in range(n_cands))
        mapping[m] = {c for c in range(n_cands) if obs_matrix[c][m] >= best_val - 1e-12}
    return mapping


def _pareto_sampling_weights(pruned_front: Mapping[int, set[int]]) -> dict[int, float]:
    freq: dict[int, int] = {}
    total = 0
    for front in pruned_front.values():
        for p in front:
            freq[p] = freq.get(p, 0) + 1
            total += 1
    return {p: c / total for p, c in freq.items()}


def _topk_pareto_weights(
    pareto_mapping: Mapping[int, set[int]],
    agg_scores: Sequence[float],
    k: int,
) -> dict[int, float]:
    """Exact logic of TopKParetoCandidateSelector (candidate_selector.py L67-82)."""
    top_k = set(sorted(range(len(agg_scores)), key=lambda i: agg_scores[i], reverse=True)[:k])
    filtered = {m: (s & top_k) for m, s in pareto_mapping.items() if (s & top_k)}
    if not filtered:
        best = max(range(len(agg_scores)), key=lambda i: agg_scores[i])
        return {best: 1.0}
    pruned = remove_dominated_programs(filtered, scores=agg_scores)
    return _pareto_sampling_weights(pruned)


def _eval_gepa_regime(
    *,
    true_matrix: Sequence[Sequence[float]],
    noise_mode: str,
    noise_sigma: float,
    inferior_thresh: float,
    specialist_ids: set[int],
    n_trials: int,
    top_k: int,
    seed: int,
) -> dict[str, dict[str, float]]:
    rng = random.Random(seed)
    n_cands = len(true_matrix)
    true_means = [statistics.fmean(row) for row in true_matrix]

    acc: dict[str, dict[str, list[float]]] = {
        sel: {"archive_sz": [], "inf_archive_frac": [], "inf_sample_prob": [], "exp_true_mean": [], "spec_both": []}
        for sel in ("pareto", "topk", "best")
    }

    eff_trials = 1 if (noise_mode == "gaussian" and noise_sigma == 0.0) else n_trials
    for _ in range(eff_trials):
        if noise_mode == "gaussian":
            if noise_sigma == 0.0:
                obs = [list(row) for row in true_matrix]
            else:
                obs = [[_clamp01(rng.gauss(val, noise_sigma)) for val in row] for row in true_matrix]
        elif noise_mode == "bernoulli":
            obs = [[1.0 if rng.random() < val else 0.0 for val in row] for row in true_matrix]
        else:
            raise ValueError(noise_mode)

        agg = [statistics.fmean(row) for row in obs]
        raw_front = _build_pareto_front_mapping(obs)

        pruned = remove_dominated_programs(raw_front, scores=agg)
        w_pareto = _pareto_sampling_weights(pruned)
        w_topk = _topk_pareto_weights(raw_front, agg, k=top_k)
        best_i = max(range(n_cands), key=lambda i: agg[i])
        w_best = {best_i: 1.0}

        for name, weights in (("pareto", w_pareto), ("topk", w_topk), ("best", w_best)):
            survivors = set(weights.keys())
            inf_surv = sum(1 for p in survivors if true_means[p] < inferior_thresh)
            inf_prob = sum(w for p, w in weights.items() if true_means[p] < inferior_thresh)
            exp_mean = sum(w * true_means[p] for p, w in weights.items())
            spec_ok = 1.0 if specialist_ids and specialist_ids.issubset(survivors) else 0.0
            acc[name]["archive_sz"].append(float(len(survivors)))
            acc[name]["inf_archive_frac"].append(inf_surv / len(survivors))
            acc[name]["inf_sample_prob"].append(inf_prob)
            acc[name]["exp_true_mean"].append(exp_mean)
            acc[name]["spec_both"].append(spec_ok)

    return {
        sel: {k: statistics.fmean(v) for k, v in metrics.items()}
        for sel, metrics in acc.items()
    }


def run_probe2() -> None:
    print("=" * 78)
    print("PROBE 2 [toy model / mechanistic surrogate]: GEPA Per-Instance Pareto Sensitivity")
    print("=" * 78)
    print("Scope caveat: simplified single-snapshot archive omitting StrictImprovementAcceptance")
    print("minibatch gating (engine.py L609-687); measures post-entry persistence & crowding.")
    m_inst = 50
    n_trials = 250

    homog_means = [0.80, 0.79, 0.78, 0.77, 0.76] + [0.56 + 0.15 * (i / 24.0) for i in range(25)]
    homog_matrix = [[mu] * m_inst for mu in homog_means]

    print(f"\n[A] Homogeneous Hierarchy — Continuous Gaussian Scores (M={m_inst}, N={len(homog_means)}, inferior<0.72):")
    homog_gauss: dict[float, dict[str, dict[str, float]]] = {}
    for idx, sigma in enumerate((0.0, 0.05, 0.15)):
        res = _eval_gepa_regime(
            true_matrix=homog_matrix,
            noise_mode="gaussian",
            noise_sigma=sigma,
            inferior_thresh=0.72,
            specialist_ids=set(),
            n_trials=n_trials,
            top_k=5,
            seed=SEED + 300 + idx,
        )
        homog_gauss[sigma] = res
        print(f"  noise_sigma={sigma:.2f}:")
        for key, label in (("pareto", "GEPA Pareto"), ("topk", "TopKPareto(K=5)"), ("best", "SelectBest")):
            r = res[key]
            print(
                f"    {label:<16} | archive_sz={r['archive_sz']:5.2f} "
                f"| inf_in_arch={r['inf_archive_frac']*100:5.1f}% "
                f"| inf_sample_p={r['inf_sample_prob']*100:5.1f}% "
                f"| E[true_mean]={r['exp_true_mean']:.4f}"
            )

    print(f"\n[B] Homogeneous Hierarchy — Binary {{0,1}} Stochastic Task Scores (Bernoulli(p), M={m_inst}, N={len(homog_means)}):")
    homog_bin = _eval_gepa_regime(
        true_matrix=homog_matrix,
        noise_mode="bernoulli",
        noise_sigma=0.0,
        inferior_thresh=0.72,
        specialist_ids=set(),
        n_trials=n_trials,
        top_k=5,
        seed=SEED + 350,
    )
    for key, label in (("pareto", "GEPA Pareto"), ("topk", "TopKPareto(K=5)"), ("best", "SelectBest")):
        r = homog_bin[key]
        print(
            f"    {label:<16} | archive_sz={r['archive_sz']:5.2f} "
            f"| inf_in_arch={r['inf_archive_frac']*100:5.1f}% "
            f"| inf_sample_p={r['inf_sample_prob']*100:5.1f}% "
            f"| E[true_mean]={r['exp_true_mean']:.4f}"
        )

    spec_sparse: list[list[float]] = [
        [0.68] * m_inst,
        [0.95] * 25 + [0.38] * 25,
        [0.38] * 25 + [0.95] * 25,
    ] + [[0.45 + 0.15 * (i / 11.0)] * m_inst for i in range(12)]

    print(f"\n[C] Specialist Retention — Sparse Generalists (1 generalist 0.680 + 2 specialists 0.665; K=5):")
    spec_res: dict[float, dict[str, dict[str, float]]] = {}
    for idx, sigma in enumerate((0.0, 0.05)):
        res = _eval_gepa_regime(
            true_matrix=spec_sparse,
            noise_mode="gaussian",
            noise_sigma=sigma,
            inferior_thresh=0.62,
            specialist_ids={1, 2},
            n_trials=n_trials,
            top_k=5,
            seed=SEED + 400 + idx,
        )
        spec_res[sigma] = res
        print(f"  noise_sigma={sigma:.2f}:")
        for key, label in (("pareto", "GEPA Pareto"), ("topk", "TopKPareto(K=5)"), ("best", "SelectBest")):
            r = res[key]
            print(
                f"    {label:<16} | archive_sz={r['archive_sz']:5.2f} "
                f"| both_specialists_retained={r['spec_both']*100:5.1f}% "
                f"| inf_sample_p={r['inf_sample_prob']*100:5.1f}%"
            )

    # [D] Generalist-crowding boundary: 6 generalists (0.68..0.73) exceed K=5, pushing both 0.665 specialists out of top-K
    spec_crowded: list[list[float]] = [
        [0.73] * m_inst,
        [0.72] * m_inst,
        [0.71] * m_inst,
        [0.70] * m_inst,
        [0.69] * m_inst,
        [0.68] * m_inst,
        [0.95] * 25 + [0.38] * 25,
        [0.38] * 25 + [0.95] * 25,
    ] + [[0.45 + 0.15 * (i / 6.0)] * m_inst for i in range(7)]

    print(f"\n[D] TopKPareto Crowding Caveat — 6 Generalists (0.68-0.73) >= K=5 + 2 Specialists (0.665):")
    crowd_res: dict[float, dict[str, dict[str, float]]] = {}
    for idx, sigma in enumerate((0.0, 0.05)):
        res = _eval_gepa_regime(
            true_matrix=spec_crowded,
            noise_mode="gaussian",
            noise_sigma=sigma,
            inferior_thresh=0.62,
            specialist_ids={6, 7},
            n_trials=n_trials,
            top_k=5,
            seed=SEED + 450 + idx,
        )
        crowd_res[sigma] = res
        print(f"  noise_sigma={sigma:.2f}:")
        for key, label in (("pareto", "GEPA Pareto"), ("topk", "TopKPareto(K=5)"), ("best", "SelectBest")):
            r = res[key]
            print(
                f"    {label:<16} | archive_sz={r['archive_sz']:5.2f} "
                f"| both_specialists_retained={r['spec_both']*100:5.1f}% "
                f"| inf_sample_p={r['inf_sample_prob']*100:5.1f}%"
            )

    assert homog_gauss[0.0]["pareto"]["archive_sz"] == 1.0
    assert homog_gauss[0.15]["pareto"]["archive_sz"] > 10.0
    assert homog_gauss[0.15]["pareto"]["inf_sample_prob"] > 0.40
    assert homog_bin["pareto"]["inf_sample_prob"] > 0.15
    assert homog_bin["topk"]["inf_sample_prob"] < homog_bin["pareto"]["inf_sample_prob"]
    assert spec_res[0.0]["pareto"]["spec_both"] == 1.0 and spec_res[0.0]["best"]["spec_both"] == 0.0
    assert crowd_res[0.0]["pareto"]["spec_both"] == 1.0 and crowd_res[0.0]["topk"]["spec_both"] == 0.0
    assert crowd_res[0.05]["pareto"]["spec_both"] > 0.99 and crowd_res[0.05]["topk"]["spec_both"] < 0.05
    print("  [PASS] Continuous & binary noise bloat, specialist retention, and TopKPareto crowding boundary verified.\n")


# =============================================================================
# Probe 3: Zwicky GMA + Ritchey CCA O(n^2) Pruning & Constructive Witness of
# Tradespace-Blind vs. Tradespace-Informed Normative Filtering
# 6 dimensions x 4 states = 4,096 formal configs; C(6,2)*16 = 240 pairwise cells
# =============================================================================


def _count_consistent_configs(
    n_dims: int,
    n_states: int,
    incompat: set[tuple[int, int, int, int]],
    banned_univariate: set[tuple[int, int]] | None = None,
) -> list[tuple[int, ...]]:
    bad = [[[[False] * n_states for _ in range(n_states)] for _ in range(n_dims)] for _ in range(n_dims)]
    for d1, s1, d2, s2 in incompat:
        if d1 > d2:
            d1, s1, d2, s2 = d2, s2, d1, s1
        bad[d1][d2][s1][s2] = True

    uni = banned_univariate or set()
    survivors: list[tuple[int, ...]] = []
    for cfg in itertools.product(range(n_states), repeat=n_dims):
        if uni and any((d, cfg[d]) in uni for d in range(n_dims)):
            continue
        ok = True
        for i in range(n_dims):
            ci = cfg[i]
            row = bad[i]
            for j in range(i + 1, n_dims):
                if row[j][ci][cfg[j]]:
                    ok = False
                    break
            if not ok:
                break
        if ok:
            survivors.append(cfg)
    return survivors


def _pareto_front_indices(points: Sequence[tuple[float, float]]) -> set[int]:
    front: set[int] = set()
    n = len(points)
    for i in range(n):
        ui, ci = points[i]
        dominated = False
        for j in range(n):
            if i == j:
                continue
            uj, cj = points[j]
            if uj >= ui - 1e-12 and cj <= ci + 1e-12 and (uj > ui + 1e-12 or cj < ci - 1e-12):
                dominated = True
                break
        if not dominated:
            front.add(i)
    return front


def run_probe3() -> None:
    print("=" * 78)
    print("PROBE 3 [exact analytical / constructive witness]: Zwicky GMA + Ritchey CCA")
    print("=" * 78)
    n_dims, n_states = 6, 4
    total_configs = n_states**n_dims
    pair_list = [
        (d1, s1, d2, s2)
        for d1 in range(n_dims)
        for d2 in range(d1 + 1, n_dims)
        for s1 in range(n_states)
        for s2 in range(n_states)
    ]
    total_cells = len(pair_list)
    n_dim_pairs = n_dims * (n_dims - 1) // 2
    assert total_configs == 4096 and total_cells == 240 and n_dim_pairs == 15

    print(f"Morphological field: {n_dims} dims x {n_states} states = {total_configs:,} configs; exact CCA cells = {total_cells}")
    print("\n[A] Exact Analytical vs. Empirical Pairwise Incompatibility Density Sweep (20 trials/p):")
    rng = random.Random(SEED + 500)
    reduction_by_p: dict[float, float] = {}
    for p in (0.10, 0.15, 0.20, 0.25, 0.30, 0.35):
        analytic_red = (1.0 - (1.0 - p) ** n_dim_pairs) * 100.0
        surv_counts = []
        for _ in range(20):
            incompat = {cell for cell in pair_list if rng.random() < p}
            surv = _count_consistent_configs(n_dims, n_states, incompat)
            surv_counts.append(len(surv))
        mean_surv = statistics.fmean(surv_counts)
        red_pct = (1.0 - mean_surv / total_configs) * 100.0
        reduction_by_p[p] = red_pct
        print(
            f"  p_incompat={p:.2f} (~{int(round(p*total_cells)):2d}/240) | mean_feas={mean_surv:6.1f}/4,096 "
            f"| emp_red={red_pct:6.2f}% | exact 1-(1-p)^15={analytic_red:6.2f}%"
        )

    # Constructive existence witness illustrating tradespace-blind vs. tradespace-informed normative filtering
    rng_arch = random.Random(SEED + 550)
    logical_incompat: set[tuple[int, int, int, int]] = {
        (0, 0, 1, 1), (0, 3, 1, 0), (0, 3, 2, 0), (0, 0, 4, 3),
        (1, 3, 5, 0), (1, 2, 5, 0), (4, 3, 5, 0), (4, 2, 5, 0),
        (2, 0, 3, 3), (2, 1, 3, 3), (3, 0, 4, 3), (1, 0, 4, 1),
    }
    versatile_cfg = (1, 2, 2, 3, 1, 3)
    while len(logical_incompat) < 44:
        cell = rng_arch.choice(pair_list)
        d1, s1, d2, s2 = cell
        if versatile_cfg[d1] == s1 and versatile_cfg[d2] == s2:
            continue
        logical_incompat.add(cell)

    feasible = _count_consistent_configs(n_dims, n_states, logical_incompat)
    red_concrete = (1.0 - len(feasible) / total_configs) * 100.0

    u_e1 = [
        [0.10, 0.24, 0.20, 0.11], [0.05, 0.10, 0.22, 0.20], [0.12, 0.14, 0.22, 0.20],
        [0.08, 0.12, 0.18, 0.20], [0.14, 0.20, 0.15, 0.10], [0.06, 0.12, 0.18, 0.21],
    ]
    c_e1 = [
        [0.08, 0.12, 0.22, 0.34], [0.04, 0.10, 0.18, 0.35], [0.16, 0.12, 0.16, 0.24],
        [0.05, 0.14, 0.16, 0.20], [0.06, 0.16, 0.26, 0.40], [0.04, 0.08, 0.16, 0.20],
    ]
    u_e2 = [
        [0.06, 0.22, 0.21, 0.16], [0.02, 0.08, 0.24, 0.28], [0.04, 0.10, 0.26, 0.24],
        [0.06, 0.10, 0.16, 0.26], [0.14, 0.22, 0.12, 0.10], [0.02, 0.08, 0.20, 0.28],
    ]
    c_e2 = [
        [0.15, 0.12, 0.20, 0.30], [0.20, 0.16, 0.16, 0.32], [0.25, 0.20, 0.16, 0.22],
        [0.14, 0.18, 0.16, 0.18], [0.10, 0.16, 0.28, 0.42], [0.22, 0.16, 0.16, 0.18],
    ]
    u_e3 = [
        [0.05, 0.22, 0.24, 0.20], [0.04, 0.12, 0.25, 0.26], [0.06, 0.14, 0.24, 0.22],
        [0.05, 0.10, 0.15, 0.26], [0.10, 0.26, 0.18, 0.14], [0.04, 0.10, 0.18, 0.24],
    ]
    c_e3 = [
        [0.12, 0.10, 0.18, 0.26], [0.14, 0.10, 0.16, 0.34], [0.20, 0.12, 0.15, 0.22],
        [0.10, 0.14, 0.15, 0.18], [0.08, 0.14, 0.24, 0.38], [0.06, 0.10, 0.16, 0.18],
    ]

    def eval_epoch(cfg: tuple[int, ...], u_tab: list[list[float]], c_tab: list[list[float]], ep: int) -> tuple[float, float]:
        u = sum(u_tab[d][cfg[d]] for d in range(n_dims))
        c = sum(c_tab[d][cfg[d]] for d in range(n_dims))
        if cfg[0] == 1 and cfg[1] == 2 and cfg[2] == 2:
            u += 0.08 if ep != 2 else 0.06
            c -= 0.05
        if cfg[3] == 3 and cfg[4] == 1 and cfg[5] == 3:
            u += 0.07
            c -= 0.04
        return (round(u, 6), round(c, 6))

    epochs = [(u_e1, c_e1, 0), (u_e2, c_e2, 1), (u_e3, c_e3, 2)]
    epoch_pts = [[eval_epoch(cfg, u_t, c_t, ep) for cfg in feasible] for u_t, c_t, ep in epochs]
    epoch_fronts = [_pareto_front_indices(pts) for pts in epoch_pts]

    pareto_trace = [sum(1 for f in epoch_fronts if i in f) for i in range(len(feasible))]
    pt3_indices = [i for i, pt in enumerate(pareto_trace) if pt == 3]
    best_pt3_idx = max(pt3_indices, key=lambda i: statistics.fmean(epoch_pts[e][i][0] for e in range(3)))
    best_cfg = feasible[best_pt3_idx]
    best_mean_u = statistics.fmean(epoch_pts[e][best_pt3_idx][0] for e in range(3))
    best_mean_c = statistics.fmean(epoch_pts[e][best_pt3_idx][1] for e in range(3))

    # Fixed predicate N = ban {D0=1, D4=1}: verify exact commutativity N(CCA(X)) == CCA(N(X))
    normative_banned = {(0, 1), (4, 1)}
    pre_cca_norm = _count_consistent_configs(n_dims, n_states, logical_incompat, banned_univariate=normative_banned)
    post_cca_norm_indices = [i for i, cfg in enumerate(feasible) if not any(cfg[d] == s for d, s in normative_banned)]
    post_cca_norm = [feasible[i] for i in post_cca_norm_indices]
    assert set(pre_cca_norm) == set(post_cca_norm)  # Set intersections strictly commute!

    max_norm_true_pt = max(pareto_trace[i] for i in post_cca_norm_indices)
    best_norm_idx = max(
        post_cca_norm_indices,
        key=lambda i: (pareto_trace[i], statistics.fmean(epoch_pts[e][i][0] for e in range(3))),
    )
    best_norm_mean_u = statistics.fmean(epoch_pts[e][best_norm_idx][0] for e in range(3))
    best_norm_mean_c = statistics.fmean(epoch_pts[e][best_norm_idx][1] for e in range(3))
    pt3_lost = sum(1 for i in pt3_indices if i not in post_cca_norm_indices)

    # Tradespace-informed normative filter (chosen AFTER inspecting CCA feasible tradespace): ban dominated D0=3
    informed_indices = [i for i, cfg in enumerate(feasible) if cfg[0] != 3]
    informed_pt3_kept = sum(1 for i in pt3_indices if i in informed_indices)

    print(f"\n[B] Constructive Existence Witness — 6-Dim Field + 3-Epoch MATE Tradespace:")
    print(f"  Logical/Empirical-Only CCA (44/240 cells): {len(feasible)} / {total_configs:,} feasible ({red_concrete:.2f}% reduction)")
    print(f"  Per-epoch Pareto front sizes: {[len(f) for f in epoch_fronts]} | Global PT=3/3 configs: {len(pt3_indices)}")
    print(f"  Top PT=3/3 architecture: cfg={best_cfg} | mean_utility={best_mean_u:.4f} | mean_cost={best_mean_c:.4f} | PT=3/3")
    print("\n[C] CONSTRUCTIVE WITNESS — Blind-to-Tradespace vs. Tradespace-Informed Normative Filtering:")
    print(f"  Commutativity check for fixed predicate N={{ban D0=1,D4=1}}: |CCA(N(X))|={len(pre_cca_norm)} == |N(CCA(X))|={len(post_cca_norm)}")
    print(f"  (Set intersection commutes; Ritchey's rule avoids choosing N blind to feasibility coupling.)")
    print(f"  Blind normative filter N={{ban D0=1,D4=1}}: discards {pt3_lost}/{len(pt3_indices)} PT=3/3 optima; max survivor PT={max_norm_true_pt}/3")
    print(
        f"  Best blind-filtered survivor: cfg={feasible[best_norm_idx]} | mean_u={best_norm_mean_u:.4f} "
        f"| mean_c={best_norm_mean_c:.4f} | true_PT={pareto_trace[best_norm_idx]}/3"
    )
    print(f"  Tradespace-informed filter (ban dominated D0=3 post-CCA): retains {informed_pt3_kept}/{len(pt3_indices)} PT=3/3 optima")

    assert reduction_by_p[0.15] >= 88.0 and reduction_by_p[0.25] >= 98.0
    assert red_concrete >= 90.0
    assert len(pt3_indices) >= 1 and pt3_lost == len(pt3_indices) and informed_pt3_kept == len(pt3_indices)
    assert max_norm_true_pt < 3
    assert best_mean_u > best_norm_mean_u and best_mean_c < best_norm_mean_c
    print("  [PASS] Exact 1-(1-p)^15 scaling, set-intersection commutativity, and blind vs. informed witness verified.\n")


# =============================================================================
# Probe 4: Discrete Bayesian Experimental Design (Static vs. Myopic vs. DP)
# + Selective-Confounder Misspecification + Exact 1D Repeated-Extrema Collapse
# =============================================================================


@dataclass(frozen=True)
class _CatProbeSpec:
    name: str
    cost: int
    n_outcomes: int
    lik_assumed: tuple[tuple[float, ...], ...]
    lik_misspec: tuple[tuple[float, ...], ...]


def _entropy_bits(post: Sequence[float]) -> float:
    return -sum(p * math.log2(p) for p in post if p > 1e-15)


def _bayes_update_cat(post: Sequence[float], lik: Sequence[Sequence[float]], y: int) -> tuple[float, ...]:
    unnorm = [post[h] * lik[h][y] for h in range(len(post))]
    z = sum(unnorm)
    if z <= 0.0:
        return tuple(post)
    return tuple(u / z for u in unnorm)


def _eig_cat_bits(post: Sequence[float], lik: Sequence[Sequence[float]], n_outcomes: int) -> float:
    h0 = _entropy_bits(post)
    eh = 0.0
    n_h = len(post)
    for y in range(n_outcomes):
        py = sum(post[h] * lik[h][y] for h in range(n_h))
        if py > 1e-15:
            eh += py * _entropy_bits(_bayes_update_cat(post, lik, y))
    return max(0.0, h0 - eh)


def _build_bed_problem() -> list[_CatProbeSpec]:
    """16 discrete hypotheses h = 4*f + v (H0 = 4 bits), 8 probes, budget B = 5.

    Under misspecification (Part B):
      High-assumed-SNR probes P0..P3 suffer an unmodeled structural confounder on
      odd variants v in {1,3}, while modest-SNR probes P4..P7 are unconfounded.
    """
    hs = list(range(16))

    def mk_bin(pred, eps: float) -> tuple[tuple[float, ...], ...]:
        return tuple(((eps, 1.0 - eps) if pred(h) else (1.0 - eps, eps)) for h in hs)

    def mk_bin_conf(pred, eps: float) -> tuple[tuple[float, ...], ...]:
        rows = []
        for h in hs:
            truth = pred(h)
            if (h % 4) in (1, 3):
                truth = not truth
            rows.append((eps, 1.0 - eps) if truth else (1.0 - eps, eps))
        return tuple(rows)

    def mk_4way_spec(active_pred, cat_fn, eps: float, confounded: bool) -> tuple[tuple[float, ...], ...]:
        rows = []
        for h in hs:
            if not active_pred(h):
                rows.append((0.25, 0.25, 0.25, 0.25))
            else:
                c = cat_fn(h)
                if confounded and (h % 4) in (1, 3):
                    c = (c + 1) % 4
                row = tuple((1.0 - eps) if y == c else (eps / 3.0) for y in range(4))
                rows.append(row)
        return tuple(rows)

    p0_pred = lambda h: (h // 4) in (0, 1)
    p1_act = lambda h: (h // 4) in (0, 1)
    p2_act = lambda h: (h // 4) in (2, 3)
    cat_flo_vhi = lambda h: ((h // 4) % 2) * 2 + (1 if (h % 4) in (2, 3) else 0)
    p3_trap = lambda h: h in {0, 1, 4, 5, 8, 12}
    p4_fhi = lambda h: (h // 4) in (0, 1)
    p5_flo = lambda h: ((h // 4) % 2) == 0
    p6_vhi = lambda h: (h % 4) in (0, 1)
    p7_vlo = lambda h: ((h % 4) % 2) == 0

    return [
        _CatProbeSpec("P0_gate_f", 2, 2, mk_bin(p0_pred, 0.02), mk_bin_conf(p0_pred, 0.04)),
        _CatProbeSpec("P1_spec_f01", 2, 4, mk_4way_spec(p1_act, cat_flo_vhi, 0.02, False), mk_4way_spec(p1_act, cat_flo_vhi, 0.04, True)),
        _CatProbeSpec("P2_spec_f23", 2, 4, mk_4way_spec(p2_act, cat_flo_vhi, 0.02, False), mk_4way_spec(p2_act, cat_flo_vhi, 0.04, True)),
        _CatProbeSpec("P3_trap_hi", 1, 2, mk_bin(p3_trap, 0.03), mk_bin_conf(p3_trap, 0.05)),
        _CatProbeSpec("P4_rob_fhi", 1, 2, mk_bin(p4_fhi, 0.14), mk_bin(p4_fhi, 0.14)),
        _CatProbeSpec("P5_rob_flo", 1, 2, mk_bin(p5_flo, 0.14), mk_bin(p5_flo, 0.14)),
        _CatProbeSpec("P6_rob_vhi", 1, 2, mk_bin(p6_vhi, 0.14), mk_bin(p6_vhi, 0.14)),
        _CatProbeSpec("P7_rob_vlo", 1, 2, mk_bin(p7_vlo, 0.10), mk_bin(p7_vlo, 0.10)),
    ]


def _choose_myopic(
    post: tuple[float, ...],
    used_mask: int,
    rem_budget: int,
    probes: Sequence[_CatProbeSpec],
    *,
    per_cost: bool,
) -> int | None:
    best_i: int | None = None
    best_val = -1.0
    for i, pr in enumerate(probes):
        if (used_mask & (1 << i)) or pr.cost > rem_budget:
            continue
        eig = _eig_cat_bits(post, pr.lik_assumed, pr.n_outcomes)
        score = (eig / pr.cost) if per_cost else eig
        if score > best_val + 1e-12:
            best_val = score
            best_i = i
    return best_i


def _lookahead_dp(
    post: tuple[float, ...],
    used_mask: int,
    rem_budget: int,
    probes: Sequence[_CatProbeSpec],
    depth: int,
) -> tuple[float, int | None]:
    if depth == 0 or rem_budget <= 0:
        return 0.0, None
    best_val = -1.0
    best_i: int | None = None
    for i, pr in enumerate(probes):
        if (used_mask & (1 << i)) or pr.cost > rem_budget:
            continue
        eig1 = _eig_cat_bits(post, pr.lik_assumed, pr.n_outcomes)
        if depth == 1 or rem_budget - pr.cost <= 0:
            total = eig1
        else:
            fut = 0.0
            nmask = used_mask | (1 << i)
            nbud = rem_budget - pr.cost
            for y in range(pr.n_outcomes):
                py = sum(post[h] * pr.lik_assumed[h][y] for h in range(len(post)))
                if py > 1e-15:
                    v_next, _ = _lookahead_dp(
                        _bayes_update_cat(post, pr.lik_assumed, y), nmask, nbud, probes, depth - 1
                    )
                    fut += py * v_next
            total = eig1 + fut
        if total > best_val + 1e-12:
            best_val = total
            best_i = i
    return (0.0 if best_i is None else best_val), best_i


def _exact_policy_eval(
    probes: Sequence[_CatProbeSpec],
    budget: int,
    policy: str,
    *,
    static_plan: Sequence[int] | None = None,
    misspecified: bool = False,
) -> dict[str, object]:
    prior = tuple([1.0 / 16.0] * 16)
    h_init = _entropy_bits(prior)
    exp_post_ent = 0.0
    exp_map_acc = 0.0
    exp_true_prob = 0.0
    exp_nll = 0.0
    exp_wrong_conf = 0.0
    wrong_branch_mass = 0.0
    first_probe = "none"

    decision_cache: dict[tuple[tuple[float, ...], int, int], int | None] = {}

    def get_choice(post: tuple[float, ...], used_mask: int, rem_budget: int, step_idx: int) -> int | None:
        if policy == "static":
            assert static_plan is not None
            return static_plan[step_idx] if step_idx < len(static_plan) else None
        key = (tuple(round(p, 10) for p in post), used_mask, rem_budget)
        if key not in decision_cache:
            if policy == "myopic_cost":
                decision_cache[key] = _choose_myopic(post, used_mask, rem_budget, probes, per_cost=True)
            elif policy == "myopic_raw":
                decision_cache[key] = _choose_myopic(post, used_mask, rem_budget, probes, per_cost=False)
            elif policy == "dp2":
                _, choice = _lookahead_dp(post, used_mask, rem_budget, probes, depth=2)
                decision_cache[key] = choice
            else:
                raise ValueError(policy)
        return decision_cache[key]

    def recurse(
        true_h: int,
        post: tuple[float, ...],
        used_mask: int,
        rem_budget: int,
        step_idx: int,
        branch_prob: float,
    ) -> None:
        nonlocal exp_post_ent, exp_map_acc, exp_true_prob, exp_nll, exp_wrong_conf, wrong_branch_mass, first_probe
        choice = get_choice(post, used_mask, rem_budget, step_idx)
        if choice is None or probes[choice].cost > rem_budget:
            ent = _entropy_bits(post)
            best_p = max(post)
            map_h = post.index(best_p)
            correct = 1.0 if map_h == true_h else 0.0
            p_true = max(post[true_h], 1e-12)
            exp_post_ent += branch_prob * ent
            exp_map_acc += branch_prob * correct
            exp_true_prob += branch_prob * post[true_h]
            exp_nll += branch_prob * (-math.log2(p_true))
            if map_h != true_h:
                exp_wrong_conf += branch_prob * best_p
                wrong_branch_mass += branch_prob
            return

        if step_idx == 0 and true_h == 0:
            first_probe = probes[choice].name

        pr = probes[choice]
        true_lik = pr.lik_misspec if misspecified else pr.lik_assumed
        for y in range(pr.n_outcomes):
            py = true_lik[true_h][y]
            if py <= 1e-15:
                continue
            next_post = _bayes_update_cat(post, pr.lik_assumed, y)
            recurse(true_h, next_post, used_mask | (1 << choice), rem_budget - pr.cost, step_idx + 1, branch_prob * py)

    for h in range(16):
        recurse(h, prior, 0, budget, 0, 1.0 / 16.0)

    return {
        "eig_bits": h_init - exp_post_ent,
        "post_entropy": exp_post_ent,
        "map_acc": exp_map_acc,
        "mean_p_true": exp_true_prob,
        "nll_bits": exp_nll,
        "mean_wrong_conf": (exp_wrong_conf / wrong_branch_mass) if wrong_branch_mass > 1e-12 else 0.0,
        "first_probe": first_probe,
    }


def _find_best_static_plan(probes: Sequence[_CatProbeSpec], budget: int) -> tuple[int, ...]:
    best_plan: tuple[int, ...] = ()
    best_eig = -1.0
    for r in range(1, len(probes) + 1):
        for comb in itertools.combinations(range(len(probes)), r):
            if sum(probes[i].cost for i in comb) > budget:
                continue
            res = _exact_policy_eval(probes, budget, "static", static_plan=comb, misspecified=False)
            eig = float(res["eig_bits"])
            if eig > best_eig + 1e-12:
                best_eig = eig
                best_plan = comb
    return best_plan


def _inv2x2(m: tuple[tuple[float, float], tuple[float, float]]) -> tuple[tuple[float, float], tuple[float, float]]:
    (a, b), (c, d) = m
    det = a * d - b * c
    return ((d / det, -b / det), (-c / det, a / det))


def _rainforth_sec53_extrema_collapse() -> dict[str, object]:
    """Exact analytical witness of Rainforth et al. (2024) Sec. 5.3 repeated-extrema collapse.

    Assumed model: y = theta_0 + theta_1 * x + eps, eps ~ N(0, sigma^2),
    theta ~ N(0, tau^2 I_2), repeatable queries x in {-1.0, -0.5, 0.0, 0.5, 1.0}, T=6.
    True DGP: f_true(x) = 0.5 + 0.3 * x + 1.2 * (x^2 - 0.5).
    """
    grid = (-1.0, -0.5, 0.0, 0.5, 1.0)
    sigma = 0.25
    tau = 1.0
    inv_s2 = 1.0 / (sigma * sigma)
    prec = ((1.0 / (tau * tau), 0.0), (0.0, 1.0 / (tau * tau)))
    chosen: list[float] = []

    for _ in range(6):
        cov = _inv2x2(prec)
        best_x = grid[0]
        best_eig = -1.0
        for x in grid:
            var_f = cov[0][0] + 2.0 * cov[0][1] * x + cov[1][1] * x * x
            eig = 0.5 * math.log2(1.0 + var_f * inv_s2)
            if eig > best_eig + 1e-12:
                best_eig = eig
                best_x = x
        chosen.append(best_x)
        prec = (
            (prec[0][0] + inv_s2, prec[0][1] + inv_s2 * best_x),
            (prec[1][0] + inv_s2 * best_x, prec[1][1] + inv_s2 * best_x * best_x),
        )

    def f_true(x: float) -> float:
        return 0.5 + 0.3 * x + 1.2 * (x * x - 0.5)

    def fit_linear_noiseless_mean(xs: Sequence[float]) -> tuple[float, float]:
        # Posterior mean E[theta | xs, y = f_true(xs)] under assumed linear model
        p00 = 1.0 / (tau * tau) + inv_s2 * len(xs)
        p01 = inv_s2 * sum(xs)
        p11 = 1.0 / (tau * tau) + inv_s2 * sum(x * x for x in xs)
        c = _inv2x2(((p00, p01), (p01, p11)))
        b0 = inv_s2 * sum(f_true(x) for x in xs)
        b1 = inv_s2 * sum(x * f_true(x) for x in xs)
        return (c[0][0] * b0 + c[0][1] * b1, c[1][0] * b0 + c[1][1] * b1)

    eval_xs = [-1.0 + 0.1 * i for i in range(21)]
    t0_bad, t1_bad = fit_linear_noiseless_mean(chosen)
    in_sample_max_err_bad = max(abs((t0_bad + t1_bad * x) - f_true(x)) for x in chosen)
    global_rmse_bad = math.sqrt(statistics.fmean(((t0_bad + t1_bad * x) - f_true(x)) ** 2 for x in eval_xs))
    distinct_x2_bad = len({round(x * x, 6) for x in chosen})

    div_xs = [-1.0, -0.5, 0.0, 0.0, 0.5, 1.0]
    t0_div, t1_div = fit_linear_noiseless_mean(div_xs)
    in_sample_max_err_div = max(abs((t0_div + t1_div * x) - f_true(x)) for x in div_xs)
    global_rmse_div = math.sqrt(statistics.fmean(((t0_div + t1_div * x) - f_true(x)) ** 2 for x in eval_xs))
    distinct_x2_div = len({round(x * x, 6) for x in div_xs})

    return {
        "chosen": chosen,
        "interior_queries_bad": sum(1 for x in chosen if abs(x) < 1.0),
        "distinct_x2_bad": distinct_x2_bad,
        "in_sample_err_bad": in_sample_max_err_bad,
        "global_rmse_bad": global_rmse_bad,
        "interior_queries_div": sum(1 for x in div_xs if abs(x) < 1.0),
        "distinct_x2_div": distinct_x2_div,
        "in_sample_err_div": in_sample_max_err_div,
        "global_rmse_div": global_rmse_div,
    }


def run_probe4() -> None:
    print("=" * 78)
    print("PROBE 4 [exact analytical / toy model]: BED Static vs. Myopic vs. Non-Myopic DP")
    print("=" * 78)
    probes = _build_bed_problem()
    budget = 5

    prior = tuple([1.0 / 16.0] * 16)
    print(f"Hypothesis space: H=16 (H0=4.000 bits), K=8 non-repeatable probes, Budget B={budget}")
    print("Step-1 assumed EIG and EIG/cost:")
    for pr in probes:
        e1 = _eig_cat_bits(prior, pr.lik_assumed, pr.n_outcomes)
        print(f"  {pr.name:<14} | cost={pr.cost} | outcomes={pr.n_outcomes} | EIG={e1:.4f} bits | EIG/cost={e1/pr.cost:.4f} bits/unit")

    opt_static = _find_best_static_plan(probes, budget)
    div_static = (4, 5, 6, 7)

    print("\n[A] Well-Specified Model (exact analytic expectation over all 16 hypotheses & trees):")
    print(f"  Optimal static plan (assumed model): {[probes[i].name for i in opt_static]}")
    ws_static = _exact_policy_eval(probes, budget, "static", static_plan=opt_static, misspecified=False)
    ws_myopic_raw = _exact_policy_eval(probes, budget, "myopic_raw", misspecified=False)
    ws_myopic_cost = _exact_policy_eval(probes, budget, "myopic_cost", misspecified=False)
    ws_dp2 = _exact_policy_eval(probes, budget, "dp2", misspecified=False)
    for label, r in (
        ("Static (Opt Assumed)", ws_static),
        ("Myopic Raw EIG", ws_myopic_raw),
        ("Myopic EIG/cost", ws_myopic_cost),
        ("Non-Myopic 2-Step DP", ws_dp2),
    ):
        print(
            f"  {label:<24} | 1st={str(r['first_probe']):<12} | EIG={float(r['eig_bits']):.4f} bits "
            f"| MAP_acc={float(r['map_acc'])*100:5.1f}% | NLL={float(r['nll_bits']):.4f} bits"
        )

    print("\n[B] SELECTIVE-CONFOUNDER OVERCONFIDENCE (P0..P3 confounded on odd v; P4..P7 unconfounded):")
    print("  Note: non-repeatable used_mask isolates high-SNR confounder overconfidence,")
    print("  distinct from Rainforth et al. Sec. 5.3 repeated-extrema collapse (shown in [C]).")
    ms_opt_static = _exact_policy_eval(probes, budget, "static", static_plan=opt_static, misspecified=True)
    ms_div_static = _exact_policy_eval(probes, budget, "static", static_plan=div_static, misspecified=True)
    ms_myopic_cost = _exact_policy_eval(probes, budget, "myopic_cost", misspecified=True)
    ms_dp2 = _exact_policy_eval(probes, budget, "dp2", misspecified=True)
    for label, r in (
        ("Static (Opt Assumed)", ms_opt_static),
        ("Static (Unconf. P4..P7)", ms_div_static),
        ("Myopic EIG/cost", ms_myopic_cost),
        ("Non-Myopic 2-Step DP", ms_dp2),
    ):
        print(
            f"  {label:<24} | MAP_acc={float(r['map_acc'])*100:5.1f}% | E[P(true)]={float(r['mean_p_true']):.4f} "
            f"| NLL={float(r['nll_bits']):.4f} bits | E[conf|wrong]={float(r['mean_wrong_conf'])*100:5.1f}%"
        )

    c_res = _rainforth_sec53_extrema_collapse()
    print("\n[C] EXACT ANALYTICAL WITNESS — Rainforth et al. (2024) Sec. 5.3 Repeated-Extrema Collapse:")
    print("  Assumed linear y=t0+t1*x vs. true quadratic f(x)=0.5+0.3x+1.2(x^2-0.5) on x in [-1,1], T=6:")
    print(f"  Linear EIG design x_1..6 = {c_res['chosen']} (interior={c_res['interior_queries_bad']}/6, distinct x^2={c_res['distinct_x2_bad']})")
    print(f"    -> Max in-sample linear residual={c_res['in_sample_err_bad']:.4f} (blind to curvature!), global RMSE={c_res['global_rmse_bad']:.4f}")
    print(f"  Diversified interior grid = [-1.0, -0.5, 0.0, 0.0, 0.5, 1.0] (interior={c_res['interior_queries_div']}/6, distinct x^2={c_res['distinct_x2_div']})")
    print(f"    -> Max in-sample linear residual={c_res['in_sample_err_div']:.4f} (detects curvature!), global RMSE={c_res['global_rmse_div']:.4f}")

    assert float(ws_dp2["eig_bits"]) > float(ws_myopic_cost["eig_bits"]) > float(ws_myopic_raw["eig_bits"])
    assert float(ws_dp2["eig_bits"]) > float(ws_static["eig_bits"])
    assert float(ws_dp2["map_acc"]) > float(ws_myopic_cost["map_acc"]) > float(ws_static["map_acc"])
    assert float(ms_opt_static["nll_bits"]) > float(ms_dp2["nll_bits"]) > float(ms_myopic_cost["nll_bits"]) > float(ms_div_static["nll_bits"])
    assert float(ms_dp2["mean_p_true"]) > float(ms_div_static["mean_p_true"])
    assert float(ms_dp2["mean_wrong_conf"]) > float(ms_div_static["mean_wrong_conf"])
    assert int(c_res["interior_queries_bad"]) == 0 and int(c_res["distinct_x2_bad"]) == 1
    assert float(c_res["in_sample_err_div"]) > 0.45 and float(c_res["global_rmse_div"]) < float(c_res["global_rmse_bad"])
    print("  [PASS] Well-specified DP dominance, transparent 4-policy selective-confounder NLL, and Sec. 5.3 extrema collapse verified.\n")


def main() -> int:
    print(f"Deterministic Verification Probes (seed={SEED}, stdlib-only)")
    run_probe1()
    run_probe2()
    run_probe3()
    run_probe4()
    print("=" * 78)
    print("ALL 4 PROBES & CONTROLS PASSED (exit 0)")
    print("=" * 78)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
