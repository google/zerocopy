#!/usr/bin/env python3
"""Deterministic executable verification probes for agent TDD, PBT, and mutation workflows.

Covers:
  Probe 1: CodeT paper (|S_x||S_y|) vs. repository (sqrt(|S_x|)|S_y|) bipartite
           consensus + tied-cluster multiplicity sampling (evaluation.py:34-42) vs.
           BACE prior-dampened Bayesian log-odds co-evolution (wso2-incubator/BACE@d859540e).
  Probe 2: Wrong-test self-debugging poisoning phase boundary p_0*(D) across difficulty
           tiers (Chen et al. ACL 2025 Tables 1-4) vs. k=8 binomial majority-vote
           abstention + suite-monotonicity backtracking and n=3 UTDebug halt dynamics
           (Prasad et al. COLM 2025 Tables 1, 2, 4 & Alg. 1-2).
  Probe 3: Hypothesis Conjecture engine assume() cutoffs (50 health-check &
           458 + 100*valid), shortlex choice-sequence shrinking, Optimiser string
           skip, and isolated causal comparison of EBT vs. PBT (bad assume) vs.
           Constructive PBT vs. Hybrid PBT+EBT.
  Probe 4: Meta ACH equivalence-judge confusion matrices (Tables 5-7 accounting audit)
           + lexical/AST comment canonicalization, and MuTAP Alg. 3 IntendedBehaviorFixer
           clean-program trap vs. complete specification-property gating (including
           an interior symmetric-bug negative control).

Requirements: Python 3.10+ stdlib only, deterministic (SEED = 20261121), zero
network access, zero disk writes, zero wall-clock timestamps in stdout, runtime < 3s.
"""

from __future__ import annotations

import ast
from collections import defaultdict
from dataclasses import dataclass
import io
import math
import random
import tokenize
from typing import Callable, Sequence

SEED = 20261121
_BACE_EPS = 1e-9


# ==============================================================================
# PROBE 1: CodeT (Paper vs. Repo) vs. BACE Prior-Dampened Log-Odds Co-Evolution
# ==============================================================================


def codet_rank_solutions(
    solution_multiplicities: dict[str, int],
    testcase_multiplicities: dict[str, int],
    passed_unique_pairs: list[tuple[str, str]],
    use_repo_sqrt: bool,
) -> list[tuple[float, list[str], int, int]]:
    """Exact reproduction of microsoft/CodeT@35f54d60 CodeT/src/agreement.py & evaluation.py.

    Reproduces:
      - DataManager._build_string_to_id_range & _get_expanded_dual_exec_result (L77-112)
      - DualAgreement._get_solution_passed_case_set & _get_caseset_passed_solutions (L128-144)
      - DualAgreement.get_sorted_solutions_without_iter (L145-158):
          repo formula (App. A/C/D): math.sqrt(len(solution_set)) * len(case_set)
          main-text §2.2 formula   : len(solution_set) * len(case_set)
      - evaluation._turn_solution_scores_into_choose_count (evaluation.py L34-42):
          tied top-score clusters are merged into a single multiset and sampled
          uniformly by solution multiplicity rather than broken lexicographically.
    """
    sol_to_ids: dict[str, range] = {}
    idx = 0
    for s_name in sorted(solution_multiplicities.keys()):
        freq = solution_multiplicities[s_name]
        sol_to_ids[s_name] = range(idx, idx + freq)
        idx += freq

    tc_to_ids: dict[str, range] = {}
    idx = 0
    for t_name in sorted(testcase_multiplicities.keys()):
        freq = testcase_multiplicities[t_name]
        tc_to_ids[t_name] = range(idx, idx + freq)
        idx += freq

    sol_id_to_str: dict[int, str] = {
        i: s_name for s_name, r in sol_to_ids.items() for i in r
    }

    expanded_pairs: list[tuple[int, int]] = []
    for s_name, t_name in passed_unique_pairs:
        if s_name in sol_to_ids and t_name in tc_to_ids:
            for s_id in sol_to_ids[s_name]:
                for t_id in tc_to_ids[t_name]:
                    expanded_pairs.append((s_id, t_id))

    sol_passed_cases: dict[int, list[int]] = defaultdict(list)
    for s_id, t_id in expanded_pairs:
        sol_passed_cases[s_id].append(t_id)

    caseset_passed_sols: dict[tuple[int, ...], list[int]] = defaultdict(list)
    for s_id in sorted(sol_passed_cases.keys()):
        case_set = tuple(sorted(sol_passed_cases[s_id]))
        caseset_passed_sols[case_set].append(s_id)

    raw_clusters: list[tuple[float, list[str], int, int]] = []
    for case_set, sol_id_list in caseset_passed_sols.items():
        s_len = len(sol_id_list)
        c_len = len(case_set)
        sol_score = math.sqrt(s_len) if use_repo_sqrt else float(s_len)
        total_score = c_len * sol_score
        sol_names = [sol_id_to_str[i] for i in sol_id_list]
        raw_clusters.append((total_score, sol_names, s_len, c_len))

    raw_clusters.sort(key=lambda item: (-item[0], item[1][0]))

    # Merge clusters with equal score per CodeT/src/evaluation.py L34-42
    merged: list[tuple[float, list[str], int, int]] = []
    for score, sol_names, s_len, c_len in raw_clusters:
        if merged and math.isclose(score, merged[-1][0], rel_tol=1e-12, abs_tol=1e-12):
            prev_score, prev_names, prev_s_len, prev_c_len = merged[-1]
            merged[-1] = (prev_score, prev_names + sol_names, prev_s_len + s_len, prev_c_len)
        else:
            merged.append((score, list(sol_names), s_len, c_len))
    return merged


def codet_top1_select_probs(
    ranked_merged: list[tuple[float, list[str], int, int]],
) -> dict[str, float]:
    """Exact pass@1 selection distribution over the top merged cluster (evaluation.py:34-42)."""
    if not ranked_merged:
        return {}
    top_names = ranked_merged[0][1]
    counts: dict[str, int] = defaultdict(int)
    for name in top_names:
        counts[name] += 1
    total = len(top_names)
    return {k: v / total for k, v in sorted(counts.items())}


def bace_prob_to_logit(prob: float, eps: float = _BACE_EPS) -> float:
    """Exact clipping log-odds transform (wso2-incubator/BACE@d859540e bayesian.py:192-199)."""
    clipped = min(max(prob, eps), 1.0 - eps)
    return math.log(clipped / (1.0 - clipped))


def bace_logit_to_prob(log_odds: float) -> float:
    if log_odds <= -60.0:
        return 0.0
    if log_odds >= 60.0:
        return 1.0
    return 1.0 / (1.0 + math.exp(-log_odds))


def bace_woe_for_code(
    test_prob: float,
    passed: bool,
    alpha: float,
    beta: float,
    gamma: float,
    eps: float = _BACE_EPS,
) -> float:
    """Exact stabilized WoE for code update (bayesian.py:252-280, Eq. 3)."""
    if passed:
        lik_corr = test_prob + alpha * (1.0 - test_prob)
        lik_inc = beta * test_prob + gamma * (1.0 - test_prob)
    else:
        lik_corr = (1.0 - alpha) * (1.0 - test_prob)
        lik_inc = (1.0 - beta) * test_prob + (1.0 - gamma) * (1.0 - test_prob)
    return math.log((lik_corr + eps) / (lik_inc + eps))


def bace_woe_for_test(
    code_prob: float,
    passed: bool,
    alpha: float,
    beta: float,
    gamma: float,
    eps: float = _BACE_EPS,
) -> float:
    """Exact stabilized WoE for test update (bayesian.py:283-310, Eq. 4)."""
    if passed:
        lik_corr = code_prob + beta * (1.0 - code_prob)
        lik_inc = alpha * code_prob + gamma * (1.0 - code_prob)
    else:
        lik_corr = (1.0 - beta) * (1.0 - code_prob)
        lik_inc = (1.0 - alpha) * code_prob + (1.0 - gamma) * (1.0 - code_prob)
    return math.log((lik_corr + eps) / (lik_inc + eps))


def deduplicate_test_columns(
    code_names: Sequence[str],
    evolved_multiplicities: dict[str, int],
    evolved_pass_map: dict[tuple[str, str], bool],
) -> dict[str, int]:
    """Deduplicate functionally redundant evolved test columns (BACE §4.5.1 &
    test_diversity_selector.py:77-113), retaining 1 representative per unique
    code-pass column vector (M_dedup <= 20).
    """
    seen_signatures: set[tuple[bool, ...]] = set()
    dedup: dict[str, int] = {}
    for t_name in sorted(evolved_multiplicities.keys()):
        if evolved_multiplicities[t_name] <= 0:
            continue
        sig = tuple(evolved_pass_map[(c_name, t_name)] for c_name in code_names)
        if sig not in seen_signatures:
            seen_signatures.add(sig)
            dedup[t_name] = 1
    return dedup


def run_bace_inference(
    code_multiplicities: dict[str, int],
    anchor_results: dict[str, list[bool]],
    evolved_multiplicities: dict[str, int],
    evolved_pass_map: dict[tuple[str, str], bool],
    generations: int = 5,
    b_init: float = 0.20,
    anchor_belief: float = 1.0 - _BACE_EPS,
    anchor_noise: tuple[float, float, float] = (0.0, 0.20, 0.0),
    evolved_noise: tuple[float, float, float] = (0.10, 0.20, 0.25),
    eta: float = 0.10,
) -> list[tuple[dict[str, float], dict[str, float], dict[str, float], dict[str, float]]]:
    """Multi-generation prior-dampened BACE co-evolution matching BACE §3.4.1, §4.5.1,
    and wso2-incubator/BACE@d859540ef849dbb93615b6b2178b8a5ce205309f
    (orchestrator.py:489-598, bayesian.py:30/192-310, configs/profiles/*/standard.yaml):
      - Deduplicates redundant evolved test columns to unique behavioral signatures (M <= 20).
      - Uses uniform learning_rate eta = 0.10 and _NUMERICAL_STABILITY_EPSILON = 1e-9.
      - In each generation g:
          1. Evaluates the current generation's candidate cohort (N <= 15, prior b_init = 0.20)
             against immutable public anchors T_anchor -> code_post_public.
          2. Updates evolved test beliefs against code_post_public -> test_post.
          3. Simultaneously updates candidate code beliefs against START-OF-GENERATION
             test priors (prior_test_probs, NOT test_post; orchestrator.py:570-575).
          4. Commits test_post as the start-of-generation test prior for generation g + 1.
    Returns per-generation history tuples:
      (code_post_public, start_of_gen_test_prior, code_evolved_post, end_of_gen_test_post).
    """
    alpha_a, beta_a, gamma_a = anchor_noise
    alpha, beta, gamma = evolved_noise
    code_names = sorted(code_multiplicities.keys())
    dedup_tests = deduplicate_test_columns(code_names, evolved_multiplicities, evolved_pass_map)
    assert sum(code_multiplicities.values()) <= 15
    assert sum(dedup_tests.values()) <= 20

    b_test: dict[str, float] = {t_name: b_init for t_name in dedup_tests}
    history: list[
        tuple[dict[str, float], dict[str, float], dict[str, float], dict[str, float]]
    ] = []

    for _ in range(generations):
        code_post_public: dict[str, float] = {}
        for c_name in code_names:
            lo = bace_prob_to_logit(b_init)
            for passed in anchor_results[c_name]:
                lo += eta * bace_woe_for_code(
                    anchor_belief, passed, alpha_a, beta_a, gamma_a
                )
            code_post_public[c_name] = bace_logit_to_prob(lo)

        start_test_priors = dict(b_test)

        # Step 3a: Tests judge anchor-grounded code_post_public
        test_post: dict[str, float] = {}
        for t_name, m_t in dedup_tests.items():
            lo = bace_prob_to_logit(start_test_priors[t_name])
            tot_woe = 0.0
            for c_name in code_names:
                n_c = code_multiplicities[c_name]
                passed = evolved_pass_map[(c_name, t_name)]
                tot_woe += n_c * bace_woe_for_test(
                    code_post_public[c_name], passed, alpha, beta, gamma
                )
            test_post[t_name] = bace_logit_to_prob(lo + eta * tot_woe)

        # Step 3b: Code judged using START-OF-GENERATION test priors (orchestrator.py:570-575)
        code_evolved_post: dict[str, float] = {}
        for c_name in code_names:
            lo = bace_prob_to_logit(code_post_public[c_name])
            tot_woe = 0.0
            for t_name, m_t in dedup_tests.items():
                passed = evolved_pass_map[(c_name, t_name)]
                tot_woe += m_t * bace_woe_for_code(
                    start_test_priors[t_name], passed, alpha, beta, gamma
                )
            code_evolved_post[c_name] = bace_logit_to_prob(lo + eta * tot_woe)

        b_test = test_post
        history.append((code_post_public, start_test_priors, code_evolved_post, dict(test_post)))

    return history


def run_probe_1() -> None:
    print("=" * 78)
    print("PROBE 1: CodeT (Paper |S_x||S_y| vs Repo sqrt(|S_x|)|S_y|) vs BACE Log-Odds")
    print("  Honesty tag: [exact reproduction of pinned repo algorithm] for CodeT")
    print("               (microsoft/CodeT@35f54d60 agreement.py L77-158, evaluation.py L34-42)")
    print("               + [exact analytical / derived calculation] for BACE Eq. 2-5")
    print("               + [mechanistic co-evolution reproduction] matching")
    print("                 wso2-incubator/BACE@d859540e (orchestrator.py L489-598,")
    print("                 bayesian.py L30/L192-310: start-of-gen test priors, eta=0.10,")
    print("                 _EPS=1e-9, deduplicated columns M_dedup<=20, N<=15).")
    print("=" * 78)

    # 1A. Exact HumanEval sort_array failure mode (CodeT Fig. 5b) + tie-merge check
    sort_sols = {"c_true": 3, "c_misc_sum_all": 4}
    sort_tests = {"t_shared": 138, "t_true_only": 20}
    sort_pairs = [
        ("c_true", "t_shared"),
        ("c_true", "t_true_only"),
        ("c_misc_sum_all", "t_shared"),
    ]
    paper_rank = codet_rank_solutions(sort_sols, sort_tests, sort_pairs, use_repo_sqrt=False)
    repo_rank = codet_rank_solutions(sort_sols, sort_tests, sort_pairs, use_repo_sqrt=True)

    assert math.isclose(paper_rank[0][0], 552.0) and paper_rank[0][1][0] == "c_misc_sum_all"
    assert math.isclose(paper_rank[1][0], 474.0) and paper_rank[1][1][0] == "c_true"
    assert math.isclose(repo_rank[0][0], 276.0) and repo_rank[0][1][0] == "c_misc_sum_all"
    assert math.isclose(repo_rank[1][0], math.sqrt(3) * 158, rel_tol=1e-12)

    # Verify evaluation.py L34-42 tied-cluster multiplicity sampling:
    tied_rank = codet_rank_solutions(
        {"c_true": 1, "c_misc": 4},
        {"t_true": 20, "t_misc": 10},
        [("c_true", "t_true"), ("c_misc", "t_misc")],
        use_repo_sqrt=True,  # sqrt(1)*20 == 20 == sqrt(4)*10 -> exact tie!
    )
    tied_probs = codet_top1_select_probs(tied_rank)
    assert len(tied_rank) == 1 and math.isclose(tied_probs["c_true"], 0.20)
    assert math.isclose(tied_probs["c_misc"], 0.80)

    print(
        f"[1A] CodeT Fig.5b sort_array & evaluation.py L34-42 tie-merge check:\n"
        f"     Paper |S_x||S_y|    : #1={paper_rank[0][1][0]} ({paper_rank[0][0]:.2f}) vs "
        f"#2={paper_rank[1][1][0]} ({paper_rank[1][0]:.2f}) [misc lead +16.46%]\n"
        f"     Repo sqrt(|S_x|)|S_y|: #1={repo_rank[0][1][0]} ({repo_rank[0][0]:.2f}) vs "
        f"#2={repo_rank[1][1][0]} ({repo_rank[1][0]:.2f}) [misc lead +0.85%]\n"
        f"     Tied-score cluster (1x20 vs 4x10 at score=20.0): merged select P(c_true)={tied_probs['c_true']:.2f}, "
        f"P(c_misc)={tied_probs['c_misc']:.2f}"
    )

    # 1B. Multiplicity-damping crossover where Repo sqrt(|S_x|) rescues Paper |S_x|,
    #     followed by severe correlated misconception where BOTH collapse.
    print("[1B] Multiplicity-damping crossover (p_true=20, |T_true|=78, |T_misc|=70):")
    for n_misc in (21, 24, 30, 45):
        sols = {"c_true": 20, "c_misc": n_misc, "c_noise": 100 - 20 - n_misc}
        tests = {"t_shared": 50, "t_true": 28, "t_misc": 20, "t_noise": 2}
        pairs = [
            ("c_true", "t_shared"),
            ("c_true", "t_true"),
            ("c_misc", "t_shared"),
            ("c_misc", "t_misc"),
            ("c_noise", "t_noise"),
        ]
        w_paper = codet_rank_solutions(sols, tests, pairs, use_repo_sqrt=False)[0][1][0]
        w_repo = codet_rank_solutions(sols, tests, pairs, use_repo_sqrt=True)[0][1][0]
        print(
            f"     n_misc={n_misc:2d} (ratio={n_misc/20:.2f}): "
            f"CodeT-Paper -> {w_paper:<8s} | CodeT-Repo(sqrt) -> {w_repo:<8s}"
        )
        if n_misc == 24:
            assert w_paper == "c_misc" and w_repo == "c_true"
        if n_misc >= 30:
            assert w_paper == "c_misc" and w_repo == "c_misc"

    # 1C. BACE exact credibility inversion thresholds (arXiv:2603.28653v2 Eq. 5)
    alpha, beta, gamma = 0.10, 0.20, 0.25
    b_star_code = (gamma - beta) / (1.0 - alpha - beta + gamma)
    b_star_test = (gamma - alpha) / (1.0 - alpha - beta + gamma)
    assert math.isclose(b_star_code, 1.0 / 19.0, rel_tol=1e-12)
    assert math.isclose(b_star_test, 3.0 / 19.0, rel_tol=1e-12)

    woe_below = bace_woe_for_test(b_star_code - 0.02, True, alpha, beta, gamma, eps=0.0)
    woe_at = bace_woe_for_test(b_star_code, True, alpha, beta, gamma, eps=0.0)
    woe_above = bace_woe_for_test(b_star_code + 0.05, True, alpha, beta, gamma, eps=0.0)
    assert woe_below < 0.0 and math.isclose(woe_at, 0.0, abs_tol=1e-12) and woe_above > 0.0
    print(
        f"[1C] BACE Eq.5 exact inversion thresholds (alpha=0.10, beta=0.20, gamma=0.25):\n"
        f"     b*_code = {b_star_code:.6f} (1/19) | b*_test = {b_star_test:.6f} (3/19)\n"
        f"     Exact test-pass WoE at b_code=(b*-0.02, b*, b*+0.05): "
        f"({woe_below:+.5f}, {woe_at:+.5f}, {woe_above:+.5f})"
    )

    # 1D. Equal-footed comparison at BACE population scale (N=15 codes: 3 c_true,
    #     7 c_misc, 5 c_noise; M=20 raw evolved tests: 10 t_shared, 4 t_true, 6 t_misc,
    #     deduplicated per §4.5.1 to M_dedup=3 unique columns) + 2 public anchors.
    sols_bace = {"c_true": 3, "c_misc": 7, "c_noise": 5}
    evolved_raw = {"t_shared": 10, "t_true": 4, "t_misc": 6}
    evolved_map = {
        ("c_true", "t_shared"): True,
        ("c_true", "t_true"): True,
        ("c_true", "t_misc"): False,
        ("c_misc", "t_shared"): True,
        ("c_misc", "t_true"): False,
        ("c_misc", "t_misc"): True,
        ("c_noise", "t_shared"): False,
        ("c_noise", "t_true"): False,
        ("c_noise", "t_misc"): False,
    }
    passing_pairs = [k for k, v in evolved_map.items() if v]

    # Equal-footed Check 1: Give CodeT-Repo the 2 clean anchors pooled with M=20 tests (M=22)
    tests_pooled = {"t_shared": 11, "t_true": 5, "t_misc": 6}
    codet_pooled_winner = codet_rank_solutions(
        sols_bace, tests_pooled, passing_pairs, use_repo_sqrt=True
    )[0][1][0]

    # Equal-footed Check 2: CodeT-Repo + Hard Anchor Filter vs. Prior-Dampened BACE (G=5)
    clean_anchors = {"c_true": [True, True], "c_misc": [True, False], "c_noise": [False, False]}
    surviving_clean = {c: n for c, n in sols_bace.items() if all(clean_anchors[c])}
    codet_hard_clean = codet_rank_solutions(
        surviving_clean,
        evolved_raw,
        [p for p in passing_pairs if p[0] in surviving_clean],
        use_repo_sqrt=True,
    )[0][1][0]

    hist_clean = run_bace_inference(
        sols_bace, clean_anchors, evolved_raw, evolved_map, generations=5
    )
    _, t_prior_g0, b_code_g0, _ = hist_clean[0]
    _, t_prior_g4, b_code_g4, t_post_g4 = hist_clean[-1]
    woe_tmisc_g0 = bace_woe_for_code(t_prior_g0["t_misc"], True, alpha, beta, gamma)
    woe_tmisc_g4 = bace_woe_for_code(t_prior_g4["t_misc"], True, alpha, beta, gamma)
    bace_winner_clean = max(b_code_g4.items(), key=lambda kv: kv[1])[0]

    # Verify §3.4.1 start-of-generation prior damping:
    # At g=0, start prior is 0.20 > 3/19 so t_misc pass WoE is still slightly positive (+0.154);
    # by g=4, accumulated test updates push t_prior["t_misc"] = 0.1468 < 3/19 = 0.1579,
    # genuinely inverting t_misc pass WoE negative (-0.0445)!
    assert woe_tmisc_g0 > 0.0 and t_prior_g4["t_misc"] < b_star_test and woe_tmisc_g4 < 0.0

    # Case B: Misparsed 3rd public anchor (b_anc=0.92, c_true=[T,T,F], c_misc=[T,F,F])
    noisy_anchors = {
        "c_true": [True, True, False],
        "c_misc": [True, False, False],
        "c_noise": [False, False, False],
    }
    surviving_noisy = {c: n for c, n in sols_bace.items() if all(noisy_anchors[c])}
    hist_noisy = run_bace_inference(
        sols_bace,
        noisy_anchors,
        evolved_raw,
        evolved_map,
        generations=5,
        anchor_belief=0.92,
        anchor_noise=(0.05, 0.20, 0.05),
    )
    b_code_noisy = hist_noisy[-1][2]
    bace_winner_noisy = max(b_code_noisy.items(), key=lambda kv: kv[1])[0]

    # Negative Control 1: Trivial non-separating anchors [T,T] -> 7 c_misc outvotes 3 c_true
    trivial_anchors = {"c_true": [True, True], "c_misc": [True, True], "c_noise": [False, False]}
    hist_triv = run_bace_inference(
        sols_bace, trivial_anchors, evolved_raw, evolved_map, generations=5
    )
    b_code_triv = hist_triv[-1][2]
    bace_winner_triv = max(b_code_triv.items(), key=lambda kv: kv[1])[0]

    # Negative Control 2: Corrupted anchor [c_true=[T,F], c_misc=[T,T]] -> inverts against c_true
    corrupted_anchors = {"c_true": [True, False], "c_misc": [True, True], "c_noise": [False, False]}
    hist_corr = run_bace_inference(
        sols_bace, corrupted_anchors, evolved_raw, evolved_map, generations=5
    )
    b_code_corr, t_post_corr = hist_corr[-1][2], hist_corr[-1][3]
    bace_winner_corr = max(b_code_corr.items(), key=lambda kv: kv[1])[0]

    assert codet_pooled_winner == "c_misc"
    assert codet_hard_clean == "c_true" and bace_winner_clean == "c_true"
    assert len(surviving_noisy) == 0 and bace_winner_noisy == "c_true"
    assert bace_winner_triv == "c_misc"
    assert bace_winner_corr == "c_misc" and t_post_corr["t_true"] < b_star_test

    print(
        f"[1D] Prior-dampened BACE (G=5, N=15, M_dedup=3, eta=0.10, _EPS=1e-9) vs CodeT:\n"
        f"     Clean distinguishing anchor (3 c_true vs 7 c_misc):\n"
        f"       CodeT-Repo (anchors pooled, M=22)  : {codet_pooled_winner} (sqrt(7)*17=44.98 > sqrt(3)*16=27.71)\n"
        f"       CodeT-Repo + Hard-Anchor-Filter    : {codet_hard_clean}\n"
        f"       BACE g=0 (start prior 0.20 > 3/19) : c_true={b_code_g0['c_true']:.4f} vs c_misc={b_code_g0['c_misc']:.4f} "
        f"(t_misc WoE={woe_tmisc_g0:+.4f}, not yet inverted)\n"
        f"       BACE g=4 (t_misc prior={t_prior_g4['t_misc']:.4f}<3/19): {bace_winner_clean} "
        f"(c_true={b_code_g4['c_true']:.4f}, c_misc={b_code_g4['c_misc']:.4f}, t_misc_post={t_post_g4['t_misc']:.4f}, "
        f"WoE={woe_tmisc_g4:+.4f} INVERTED)\n"
        f"     Misparsed 3rd anchor (b_anc=0.92, c_true=[T,T,F], c_misc=[T,F,F]):\n"
        f"       CodeT-Repo + Hard-Anchor-Filter    : {len(surviving_noisy)} survivors (over-pruned)\n"
        f"       BACE soft anchor (b_anc=0.92, G=5) : {bace_winner_noisy} "
        f"(c_true={b_code_noisy['c_true']:.4f} vs c_misc={b_code_noisy['c_misc']:.4f})\n"
        f"     Decoupled Negative Controls (where BACE MUST fail):\n"
        f"       Trivial non-separating anchors [T,T]: {bace_winner_triv} "
        f"(c_misc={b_code_triv['c_misc']:.4f} > c_true={b_code_triv['c_true']:.4f})\n"
        f"       Corrupted anchor [c_true=F,c_misc=T]: {bace_winner_corr} "
        f"(c_true={b_code_corr['c_true']:.4f} < b*_code, t_true={t_post_corr['t_true']:.4f} < b*_test)"
    )


# ==============================================================================
# PROBE 2: Wrong-Test Self-Debugging Phase Boundary (Chen et al. ACL 2025 & UTDebug)
# ==============================================================================


def analytical_post_debug_acc(
    p0: float,
    q_suite: float,
    d_tn: float,
    r_tn: float,
    c_cap: float,
) -> tuple[float, float]:
    """Exact 1-step Markov transition accuracy and critical poisoning threshold p_0*."""
    p_after = p0 * (1.0 - (1.0 - q_suite) * c_cap) + (1.0 - p0) * d_tn * r_tn
    denom = d_tn * r_tn + (1.0 - q_suite) * c_cap
    p0_star = (d_tn * r_tn) / denom if denom > 0.0 else 1.0
    return p_after, p0_star


def k8_majority_vote_stats(
    p_sample_corr: float,
    n_err_modes: int = 1,
) -> tuple[float, float, float]:
    """Exact k=8 majority-vote (>= 5/8 agreement) retention & wrong-accept rates
    matching UTDebug Alg. 1 BuildUT L1045 (abstain when modal output share <= 50%).

    Because at most one distinct output can achieve >= 5 of 8 votes, the events
    {correct >= 5} and {error_mode_m >= 5} are pairwise disjoint!
    Returns (p_keep_total, conditional_kept_acc, p_keep_wrong_per_input).
    """
    p_err_each = (1.0 - p_sample_corr) / n_err_modes
    p_keep_corr = sum(
        math.comb(8, j) * (p_sample_corr ** j) * ((1.0 - p_sample_corr) ** (8 - j))
        for j in range(5, 9)
    )
    p_keep_wrong = n_err_modes * sum(
        math.comb(8, j) * (p_err_each ** j) * ((1.0 - p_err_each) ** (8 - j))
        for j in range(5, 9)
    )
    p_keep_total = p_keep_corr + p_keep_wrong
    cond_acc = p_keep_corr / p_keep_total if p_keep_total > 0.0 else 0.0
    return p_keep_total, cond_acc, p_keep_wrong


def run_probe_2(rng: random.Random) -> None:
    print("\n" + "=" * 78)
    print("PROBE 2: Wrong-Test Self-Debugging Poisoning Phase Boundary & UTDebug Shield")
    print("  Honesty tag: [exact analytical / derived calculation] for Chen et al. ACL 2025")
    print("               (arXiv:2501.12793v1 Tables 1-4 & Fig. 2, with 1-DOF calibrated")
    print("               c_cap=0.292 on HumanEval+) + [illustrative difficulty-indexed")
    print("               surrogate] explaining why LCB-Hard p_0*(Hard) drops into")
    print("               (6.0%, 16.4%) + [exact binomial + n=3 trigger calculation] for")
    print("               UTGen/UTDebug (arXiv:2502.01619v3 Tables 1, 2, 4 & Alg. 1-2).")
    print("=" * 78)

    # 2A. Exact Chen et al. ACL 2025 (2501.12793v1 Table 3 L389-395) 10-test suite validity
    table3_rows = [
        ("GPT-4o-2024-05-13 HumanEval", 0.8977, 0.5915),
        ("Claude-3.5-Sonnet HumanEval", 0.8914, 0.5671),
        ("LLaMA-3-70B-Instruct MBPP", 0.8208, 0.5185),
        ("Qwen2.5-Coder-7B-Instruct MBPP", 0.7733, 0.4444),
    ]
    print("[2A] 10-test suite oracle validity (i.i.d. q_out^10 vs 2501.12793v1 Table 3):")
    for label, q_out, emp_suite in table3_rows:
        iid_suite = q_out ** 10
        gap = emp_suite - iid_suite
        assert gap > 0.24
        print(
            f"     {label:<31s}: q_out={q_out*100:.2f}% -> i.i.d.={iid_suite*100:.2f}% "
            f"vs empirical={emp_suite*100:.2f}% (corr +{gap*100:.2f}pp)"
        )

    # 2B. Part 1: Claude-3.5-Sonnet on HumanEval+ (Tables 1-2 & Fig. 2):
    #   - One-pass p0 = 146/164 = 89.02%; Fig. 2 FN = 33.54% of all tasks ->
    #     1 - q_eff = 0.3354 / p0 = 0.37675 (q_eff = 62.33%, consistent with Table 3's
    #     56.71% suite validity since some wrong assertions do not trigger on f_0).
    #   - Fig. 2 TN = 4.27% of all tasks -> d_tn = 0.0427 / (1 - p0) = 0.3890.
    #   - Table 1 oracle 1-iter repair: 89.0% -> 93.9% (+4.9pp on 11.0% bugs -> r_tn = 0.445).
    #   - c_cap = 0.292 [1-DOF calibrated to Table 2 Iter-1 = 81.1%; Iter-2 = 79.3%].
    p0_he = 146.0 / 164.0
    q_eff_he = 1.0 - (0.3354 / p0_he)
    d_tn_he = 0.0427 / (1.0 - p0_he)
    r_tn_he = 0.445
    c_cap_he = 0.292
    p_after_he, p0_star_he = analytical_post_debug_acc(
        p0_he, q_eff_he, d_tn_he, r_tn_he, c_cap_he
    )

    trials = 25_000
    mc_wins = 0
    for _ in range(trials):
        is_correct = rng.random() < p0_he
        if is_correct:
            if (rng.random() < (1.0 - q_eff_he)) and (rng.random() < c_cap_he):
                is_correct = False
        else:
            if (rng.random() < d_tn_he) and (rng.random() < r_tn_he):
                is_correct = True
        if is_correct:
            mc_wins += 1
    mc_acc = mc_wins / trials
    assert abs(mc_acc - p_after_he) < 0.004
    assert p0_he > p0_star_he and p_after_he < p0_he

    # Part 2: Difficulty-dependent p_0*(D) on LiveCodeBench-Hard (2501.12793v1 Table 4 L435-444).
    # Verbatim Table 4 `Self-debug w/ detail` on LCB-Hard:
    #   - Claude-3.5-Sonnet: 16.4% (Iter 0) -> 13.8% (-2.6pp, Iter 1) -> 8.6% (-7.8pp, Iter 2)!
    #     (Whereas `w/ label` without wrong expected-output details goes 16.4% -> 17.2% -> 16.4%.)
    #   - GPT-4o           :  6.0% (Iter 0) ->  8.6% (+2.6pp, Iter 1) -> 6.0% ( 0.0pp, Iter 2).
    #   - LLaMA-3-70B      :  2.6% (Iter 0) ->  4.3% (+1.7pp, Iter 1) -> 3.4% (+0.8pp, Iter 2).
    # Naive fixed-parameter transfer of HumanEval+ (p_0* = 61.15%) would falsely predict gain at
    # p_0 = 16.4%! On Hard competitive tasks, output-oracle validity q_eff(Hard) and 1-step
    # repair r_tn(Hard) collapse simultaneously, pushing p_0*(Hard) into (6.0%, 16.4%):
    q_eff_hard, d_tn_hard, r_tn_hard, c_cap_hard = 0.25, 0.65, 0.055, 0.36
    p1_claude_hard, p0_star_hard = analytical_post_debug_acc(
        0.164, q_eff_hard, d_tn_hard, r_tn_hard, c_cap_hard
    )
    p1_gpt4o_hard, _ = analytical_post_debug_acc(
        0.060, q_eff_hard, d_tn_hard, r_tn_hard, c_cap_hard
    )
    p1_llama_hard, _ = analytical_post_debug_acc(
        0.026, q_eff_hard, d_tn_hard, r_tn_hard, c_cap_hard
    )
    assert 0.060 < p0_star_hard < 0.164
    assert p1_claude_hard < 0.164 and p1_gpt4o_hard > 0.060 and p1_llama_hard > 0.026

    print(
        f"[2B] Difficulty-dependent poisoning boundary p_0*(D):\n"
        f"     HumanEval+ (p_0*(HE+) = {p0_star_he*100:.2f}%, calibrated c_cap=0.292):\n"
        f"       Claude-3.5-Sonnet (p_0={p0_he*100:.2f}% > p_0*): Iter-1={p_after_he*100:.2f}% "
        f"({(p_after_he-p0_he)*100:+.2f}pp; Table 2: 89.0%->81.1%->79.3%) | MC={mc_acc*100:.2f}%\n"
        f"     LCB-Hard Table 4 (`Self-debug w/ detail`) & difficulty-indexed p_0*(Hard)={p0_star_hard*100:.2f}%:\n"
        f"       Claude-3.5-Sonnet (p_0=16.4% > p_0*(Hard)): Table 4: 16.4%->13.8% (-2.6pp)->8.6% (-7.8pp) "
        f"| surrogate Iter-1={p1_claude_hard*100:.2f}% ({(p1_claude_hard-0.164)*100:+.2f}pp)\n"
        f"       GPT-4o            (p_0= 6.0% < p_0*(Hard)): Table 4:  6.0%-> 8.6% (+2.6pp)->6.0%          "
        f"| surrogate Iter-1={p1_gpt4o_hard*100:.2f}% ({(p1_gpt4o_hard-0.060)*100:+.2f}pp)\n"
        f"       LLaMA-3-70B       (p_0= 2.6% < p_0*(Hard)): Table 4:  2.6%-> 4.3% (+1.7pp)->3.4%          "
        f"| surrogate Iter-1={p1_llama_hard*100:.2f}% ({(p1_llama_hard-0.026)*100:+.2f}pp)"
    )

    # 2C. Explicit k=8 majority-vote abstention + suite-monotonicity gate AND exact
    #     UTGen/UTDebug n=3 tests/round premature-halt analysis (2502.01619v3 Tables 1, 2, 4):
    #   1. Derive shielded HumanEval+ parameters from exact k=8 binomial voting (>= 5/8) on
    #      n=3 generated tests/round under worst-case single-mode misconception (n_err_modes=1,
    #      per-sample CoT output accuracy p_cot = 0.78 on non-trivial edge inputs), explicitly
    #      accounting for d_tn retention loss (d_tn * p_keep) and 3-anchor monotonicity rejection:
    p_keep_he, cond_acc_he, p_wrong_kept_he = k8_majority_vote_stats(0.78, n_err_modes=1)
    q_eff_shielded = (1.0 - p_wrong_kept_he) ** 3
    d_tn_shielded = d_tn_he * p_keep_he
    # Monotonicity gate: buggy edit survives only if it happens to pass all 3 anchor/kept checks (0.55^3)
    c_cap_shielded = c_cap_he * (0.55 ** 3)
    p_shielded, p0_star_shielded = analytical_post_debug_acc(
        p0_he, q_eff_shielded, d_tn_shielded, r_tn_he, c_cap_shielded
    )
    assert d_tn_shielded < d_tn_he
    assert p_shielded > p0_he and p0_star_shielded > p0_he

    #   2. Verbatim UTGen/UTDebug Qwen2.5 32B on MBPP+Fix Hard (N=170, p_0=0.0%, n=3 UTs/round,
    #      m=3 rounds; 2502.01619v3 Table 1 L505-507, Table 2 L559-563, Table 4 L648-650):
    no_ut_3round = 0.3294
    # (label, Table-1 Attack Rate, Table-1 Out Acc, single-sample p_cot, Table-2 UTDebug Pass@1)
    # Note: for UTGen, Table 4 explicitly gives non-SC single-sample Out Acc = 56.86% (vs 59.22% w/ k=8 SC).
    utgen_rows = [
        ("Random UT", 0.2529, 0.4725, 0.4725, 0.2294),
        ("Prompted UT", 0.5196, 0.4843, 0.4843, 0.3118),
        ("UTGen SFT", 0.5608, 0.5922, 0.5686, 0.4529),
    ]
    print(
        f"[2C] Derived k=8 vote-abstention shield & n=3 UTDebug Round-1 halt dynamics:\n"
        f"     HumanEval+ derived k=8 vote (keep={p_keep_he*100:.1f}%, cond_acc={cond_acc_he*100:.2f}%, "
        f"q_eff={q_eff_shielded*100:.2f}%, d_tn={d_tn_shielded*100:.2f}%, c_cap={c_cap_shielded*100:.2f}%):\n"
        f"       Post-debug = {p_shielded*100:.2f}% ({(p_shielded-p0_he)*100:+.2f}pp, p_0*={p0_star_shielded*100:.2f}%)\n"
        f"     MBPP+Fix Hard (Qwen2.5 32B, p_0=0%, No-UT 3-round self-critique = {no_ut_3round*100:.2f}%):"
    )
    for label, a1, out_acc, p_single, emp_pass1 in utgen_rows:
        # Exact n=3 non-empty Round-1 trigger upper bound before vote abstention: 1 - (1 - a1)^3
        r1_raw_ceiling = 1.0 - ((1.0 - a1) ** 3)
        # Mechanistic binomial k=8 vote-abstention retention (2-way error split) -> Round-1 non-empty xd:
        rho_keep, _, _ = k8_majority_vote_stats(p_single, n_err_modes=2)
        r1_kept_trigger = 1.0 - ((1.0 - a1 * rho_keep) ** 3)
        assert r1_raw_ceiling > r1_kept_trigger > emp_pass1
        if label == "Random UT":
            assert r1_kept_trigger < no_ut_3round
        if label == "UTGen SFT":
            assert r1_kept_trigger > emp_pass1 > no_ut_3round
        print(
            f"       {label:<11s} (Atk={a1*100:.2f}%, OutAcc={out_acc*100:.2f}%): "
            f"n=3 raw trigger={r1_raw_ceiling*100:.2f}%, vote-kept R1 trigger={r1_kept_trigger*100:.2f}% "
            f"-> Table 2 UTDebug={emp_pass1*100:.2f}%"
        )


# ==============================================================================
# PROBE 3: Hypothesis Conjecture Engine Mechanics & PBT + EBT Complementarity
# ==============================================================================


def hypothesis_invalid_thresholds(r: float = 0.01, c: float = 0.99) -> tuple[int, int]:
    """Exact reproduction of Hypothesis engine.py L159-168."""
    base = math.ceil(math.log(1.0 - c) / math.log(1.0 - r)) - 1
    per_p = math.ceil(1.0 / r)
    return base, per_p


def hypothesis_size_to_index(size: int, alphabet_size: int) -> int:
    """Exact reproduction of Hypothesis choice.py L200-211."""
    if alphabet_size <= 0:
        assert size == 0
        return 0
    if alphabet_size == 1:
        return size
    return (alphabet_size ** size - 1) // (alphabet_size - 1)


def hypothesis_collection_index(
    seq: Sequence[int], min_size: int, alphabet_size: int
) -> int:
    """Exact reproduction of Hypothesis choice.py L243-269."""
    index = hypothesis_size_to_index(
        len(seq), alphabet_size
    ) - hypothesis_size_to_index(min_size, alphabet_size)
    running_exp = 1
    for elem_order in reversed(seq):
        index += running_exp * elem_order
        running_exp *= alphabet_size
    return index


def hypothesis_zigzag_index(value: int, shrink_towards: int = 0) -> int:
    """Exact reproduction of unbounded integer zigzag ordering (choice.py L308-314;
    bounded integers clamp zigzagging once min_value/max_value is reached at L360+).
    """
    index = 2 * abs(shrink_towards - value)
    if value > shrink_towards:
        index -= 1
    return index


@dataclass(frozen=True)
class SimChoiceNode:
    node_type: str  # "integer" | "string" | "boolean" | "float" | "bytes"
    value: int | str | bool
    alphabet_size: int = 26


def hypothesis_sort_key(nodes: Sequence[SimChoiceNode]) -> tuple[int, tuple[int, ...]]:
    """Exact reproduction of Hypothesis shrinker.py L73-94 shortlex ordering."""
    indices: list[int] = []
    for n in nodes:
        if n.node_type == "integer":
            assert isinstance(n.value, int)
            indices.append(hypothesis_zigzag_index(n.value, 0))
        elif n.node_type == "string":
            assert isinstance(n.value, str)
            orders = [ord(ch) - ord("a") for ch in n.value]
            indices.append(
                hypothesis_collection_index(orders, min_size=0, alphabet_size=n.alphabet_size)
            )
        elif n.node_type == "boolean":
            indices.append(1 if bool(n.value) else 0)
        else:
            raise ValueError(f"Unsupported node type: {n.node_type}")
    return (len(nodes), tuple(indices))


def simulate_conjecture_filter_loop(
    draw_fn: Callable[[random.Random], tuple[list[int], bool]],
    rng: random.Random,
    max_examples: int = 100,
    suppress_filter_health_check: bool = False,
    overrun_per_invalid: int = 0,
) -> tuple[str, int, int]:
    """Exact reproduction of Hypothesis engine.py L788-793 & L843-897 state machine
    (where L790 checks `(invalid + overrun) > invalid_base + invalid_per_valid * valid`).
    """
    invalid_base, invalid_per_valid = hypothesis_invalid_thresholds(0.01, 0.99)
    valid = 0
    invalid = 0
    overrun = 0
    health_check_active = not suppress_filter_health_check

    while True:
        if valid >= max_examples:
            return ("ExitReason.max_examples", valid, invalid)
        if (invalid + overrun) > (invalid_base + invalid_per_valid * valid):
            return ("ExitReason.max_iterations", valid, invalid)

        _, passed_assume = draw_fn(rng)
        if passed_assume:
            valid += 1
        else:
            invalid += 1
            overrun += overrun_per_invalid

        if health_check_active:
            if valid == 10:
                health_check_active = False
            elif invalid == 50:
                return ("FailedHealthCheck.filter_too_much", valid, invalid)


def run_probe_3(rng: random.Random) -> None:
    print("\n" + "=" * 78)
    print("PROBE 3: Hypothesis Conjecture Cutoffs, Shortlex Shrinking & PBT+EBT Synergy")
    print("  Honesty tag: [exact reproduction of pinned repo algorithm] for Hypothesis")
    print("               9a15ddde (engine.py L159-168/L788-897, choice.py L200-314,")
    print("               shrinker.py L73-94, optimiser.py L107-108) + [toy model /")
    print("               mechanistic surrogate] with single-variable causal isolation")
    print("               on a concrete 3-bug PBT+EBT harness.")
    print("=" * 78)

    # 3A. Verify exact engine thresholds & narrow-precondition assume() starvation
    base_thr, per_valid_thr = hypothesis_invalid_thresholds(0.01, 0.99)
    assert (base_thr, per_valid_thr) == (458, 100)

    def naive_assume_draw(r: random.Random) -> tuple[list[int], bool]:
        size = r.randint(0, 8)
        xs = [r.randint(-50, 50) for _ in range(size)]
        ok = len(xs) >= 4 and all(x > 0 for x in xs) and all(
            xs[i] < xs[i + 1] for i in range(len(xs) - 1)
        )
        return xs, ok

    def constructive_composite_draw(r: random.Random) -> tuple[list[int], bool]:
        size = r.randint(4, 8)
        cur = 0
        xs: list[int] = []
        for _ in range(size):
            cur += r.randint(1, 15)
            xs.append(cur)
        return xs, True

    st_default = simulate_conjecture_filter_loop(
        naive_assume_draw, rng, max_examples=100, suppress_filter_health_check=False
    )
    st_suppressed = simulate_conjecture_filter_loop(
        naive_assume_draw, rng, max_examples=100, suppress_filter_health_check=True
    )
    st_constructive = simulate_conjecture_filter_loop(
        constructive_composite_draw, rng, max_examples=100, suppress_filter_health_check=False
    )

    assert st_default[0] == "FailedHealthCheck.filter_too_much" and st_default[2] == 50
    assert st_suppressed[0] == "ExitReason.max_iterations" and st_suppressed[1] < 5
    assert st_constructive == ("ExitReason.max_examples", 100, 0)

    print(
        f"[3A] Hypothesis assume() engine cutoffs (base={base_thr}, per_valid={per_valid_thr}):\n"
        f"     Naive @given + assume() [default]     : {st_default[0]} "
        f"(valid={st_default[1]}, invalid={st_default[2]})\n"
        f"     Naive @given + assume() [suppressed]  : {st_suppressed[0]} "
        f"(valid={st_suppressed[1]}/100, invalid={st_suppressed[2]})\n"
        f"     Constructive @composite delta strategy: {st_constructive[0]} "
        f"(valid={st_constructive[1]}/100, invalid={st_constructive[2]})"
    )

    # 3B. Shortlex choice-sequence shrinking -> token minimization (PGS connection)
    #     plus Optimiser string-node skip verification (optimiser.py L107-108).
    unshrunk_nodes = [
        SimChoiceNode("integer", -48291),
        SimChoiceNode("string", "xqzptlkv"),
        SimChoiceNode("integer", 19042),
        SimChoiceNode("integer", -7731),
    ]

    def reproduces_bug(nodes: Sequence[SimChoiceNode]) -> bool:
        return (
            len(nodes) >= 2
            and nodes[0].node_type == "integer"
            and isinstance(nodes[0].value, int)
            and nodes[0].value < 0
            and nodes[1].node_type == "string"
            and isinstance(nodes[1].value, str)
            and len(nodes[1].value) >= 1
        )

    assert reproduces_bug(unshrunk_nodes)
    cur_nodes = list(unshrunk_nodes)
    while len(cur_nodes) > 2:
        cand = cur_nodes[:-1]
        if reproduces_bug(cand) and hypothesis_sort_key(cand) < hypothesis_sort_key(cur_nodes):
            cur_nodes = cand
    for int_cand in (0, 1, -1, 2, -2):
        cand = [SimChoiceNode("integer", int_cand), cur_nodes[1]]
        if reproduces_bug(cand) and hypothesis_sort_key(cand) < hypothesis_sort_key(cur_nodes):
            cur_nodes = cand
            break
    for str_cand in ("", "a", "b"):
        cand = [cur_nodes[0], SimChoiceNode("string", str_cand)]
        if reproduces_bug(cand) and hypothesis_sort_key(cand) < hypothesis_sort_key(cur_nodes):
            cur_nodes = cand
            break

    raw_repr = repr([n.value for n in unshrunk_nodes])
    shrunk_repr = repr([n.value for n in cur_nodes])
    assert [n.value for n in cur_nodes] == [-1, "a"]
    assert len(shrunk_repr) < len(raw_repr)

    optimiser_supported = {"integer", "float", "bytes", "boolean"}
    string_mutations = sum(
        1 for n in [SimChoiceNode("string", "header")] if n.node_type in optimiser_supported
    )
    assert string_mutations == 0

    print(
        f"[3B] Shortlex choice-sequence shrinking & Optimiser string skip:\n"
        f"     Unshrunk counterexample : {raw_repr} (chars={len(raw_repr)}, key={hypothesis_sort_key(unshrunk_nodes)})\n"
        f"     Shrunk counterexample   : {shrunk_repr} (chars={len(shrunk_repr)}, key={hypothesis_sort_key(cur_nodes)})\n"
        f"     Optimiser hill-climb mutations on string ChoiceNode: {string_mutations} (skipped per optimiser.py L107)"
    )

    # 3C. Concrete 3-Bug Function Suite with Single-Variable Causal Isolation:
    #       (1) Raw EBT (false alarm on gold_spec from wrong overlapping-interval sum)
    #       (2) Property-Filtered EBT (executable bound predicate catches wrong assertion;
    #           kills bug2_double_space ONLY [1/3])
    #       (3) PBT w/ narrow assume(len(spans) > 0) (kills bug1_unsorted_spans ONLY [1/3])
    #       (4) Constructive PBT alone (identical seed/alphabet/reversal, ONLY removing
    #           assume(len(spans) > 0) -> directly rescues bug3_empty_boundary [2/3]!)
    #       (5) Explicit union Constructive PBT U Filtered EBT (no short-circuit -> [3/3])
    def gold_spec(text: str, spans: list[tuple[int, int, int]]) -> tuple[str, int]:
        norm = text.replace("  ", "|").replace(" ", "_")
        ordered = sorted(spans, key=lambda item: (item[0], item[1], -item[2]))
        total = 0
        last_end = -1
        for lo, hi, w in ordered:
            if lo >= last_end:
                total += w
                last_end = hi
        return norm, total

    def mut_unsorted_spans(text: str, spans: list[tuple[int, int, int]]) -> tuple[str, int]:
        norm = text.replace("  ", "|").replace(" ", "_")
        total, last_end = 0, -1
        for lo, hi, w in spans:
            if lo >= last_end:
                total += w
                last_end = hi
        return norm, total

    def mut_double_space_literal(text: str, spans: list[tuple[int, int, int]]) -> tuple[str, int]:
        norm = text.replace(" ", "_").replace("  ", "|")
        _, total = gold_spec(text, spans)
        return norm, total

    def mut_empty_boundary(text: str, spans: list[tuple[int, int, int]]) -> tuple[str, int]:
        if not spans:
            return text.replace("  ", "|").replace(" ", "_"), -1
        return gold_spec(text, spans)

    mutants = {
        "bug1_unsorted_spans": mut_unsorted_spans,
        "bug2_double_space": mut_double_space_literal,
        "bug3_empty_boundary": mut_empty_boundary,
    }

    # Executable specification-bound predicate for filtering candidate EBT assertions
    # WITHOUT calling gold_spec or hardcoding literal expectations:
    def ebt_assertion_satisfies_spec_bounds(
        text: str, spans: list[tuple[int, int, int]], expected: tuple[str, int]
    ) -> bool:
        exp_norm, exp_total = expected
        if " " in exp_norm or exp_total < 0:
            return False
        if not spans:
            return exp_total == 0
        if exp_total > sum(w for _, _, w in spans):
            return False
        # Necessary interval-clique bound: if all spans share a common point (max_lo < min_hi),
        # at most ONE span can be non-overlapping, so total <= max(w)!
        if max(lo for lo, _, _ in spans) < min(hi for _, hi, _ in spans):
            if exp_total > max(w for _, _, w in spans):
                return False
        return True

    # Hand-picked non-empty EBT tests: 1 valid "  " literal test + 1 wrong overlapping sum (4+7=11)
    ebt_raw = [
        ("a  b", [(0, 2, 5)], ("a|b", 5)),
        ("x y", [(0, 3, 4), (1, 3, 7)], ("x_y", 11)),
    ]
    ebt_false_alarm_on_gold = any(gold_spec(t, s) != exp for t, s, exp in ebt_raw)
    ebt_filtered = [
        case for case in ebt_raw if ebt_assertion_satisfies_spec_bounds(*case)
    ]

    def kills_by_filtered_ebt(
        fn: Callable[[str, list[tuple[int, int, int]]], tuple[str, int]]
    ) -> bool:
        return any(fn(t, s) != exp for t, s, exp in ebt_filtered)

    def run_pbt_metamorphic(
        fn: Callable[[str, list[tuple[int, int, int]]], tuple[str, int]],
        filter_empty_with_assume: bool,
    ) -> bool:
        # Identical seed, identical alphabet "abc", and identical reversed(spans)
        # so `filter_empty_with_assume` is the sole isolated causal variable!
        local_rng = random.Random(SEED + 301)
        for _ in range(80):
            txt = "".join(local_rng.choice("abc") for _ in range(local_rng.randint(1, 6)))
            n = local_rng.randint(0, 5)
            if filter_empty_with_assume and n == 0:
                continue
            spans = []
            for _ in range(n):
                lo = local_rng.randint(0, 8)
                spans.append((lo, lo + local_rng.randint(1, 3), local_rng.randint(1, 9)))
            out1 = fn(txt, spans)
            out2 = fn(txt, list(reversed(spans)))
            if out1 != out2 or out1[1] < 0:
                return True
        return False

    ebt_kills = [m for m, fn in mutants.items() if kills_by_filtered_ebt(fn)]
    pbt_bad_kills = [
        m for m, fn in mutants.items() if run_pbt_metamorphic(fn, filter_empty_with_assume=True)
    ]
    pbt_constructive_kills = [
        m for m, fn in mutants.items() if run_pbt_metamorphic(fn, filter_empty_with_assume=False)
    ]
    hybrid_union_kills = [
        m for m in mutants if (m in ebt_kills) or (m in pbt_constructive_kills)
    ]
    hybrid_false_alarm = kills_by_filtered_ebt(gold_spec) or run_pbt_metamorphic(
        gold_spec, filter_empty_with_assume=False
    )

    assert ebt_false_alarm_on_gold is True and len(ebt_filtered) == 1
    assert ebt_kills == ["bug2_double_space"]
    assert pbt_bad_kills == ["bug1_unsorted_spans"]
    assert pbt_constructive_kills == ["bug1_unsorted_spans", "bug3_empty_boundary"]
    assert len(hybrid_union_kills) == 3 and not hybrid_false_alarm

    print(
        f"[3C] Causal isolation of EBT vs PBT (bad assume) vs Constructive PBT vs Hybrid:\n"
        f"     Raw EBT false alarm on gold_spec (overlapping sum 4+7=11): {ebt_false_alarm_on_gold}\n"
        f"     Spec-Bound-Filtered EBT alone    : {len(ebt_kills)}/3 {ebt_kills}\n"
        f"     PBT w/ narrow assume(len>0)      : {len(pbt_bad_kills)}/3 {pbt_bad_kills} [Negative Control]\n"
        f"     Constructive PBT alone (no assume): {len(pbt_constructive_kills)}/3 {pbt_constructive_kills}\n"
        f"     Hybrid Union (Constructive U EBT): {len(hybrid_union_kills)}/3 {hybrid_union_kills} (0 false alarms)"
    )


# ==============================================================================
# PROBE 4: Meta ACH Comment-Stripping Gate & MuTAP Alg. 3 Clean-Program Trap
# ==============================================================================


def canonicalize_source_no_comments(src: str) -> str:
    """Strip # comments via Python's lexical tokenizer + normalize AST formatting."""
    kept_tokens: list[tuple[int, str]] = []
    reader = io.BytesIO(src.encode("utf-8")).readline
    for tok in tokenize.tokenize(reader):
        if tok.type in (tokenize.COMMENT, tokenize.ENCODING, tokenize.NL):
            continue
        kept_tokens.append((tok.type, tok.string))
    untokenized = tokenize.untokenize(kept_tokens)
    return ast.unparse(ast.parse(untokenized))


def mutap_intended_behavior_fixer(
    put_fn: Callable[[int, int], int],
    candidate_tests: list[tuple[int, int, int]],
    spec_guard: Callable[[Callable[[int, int], int], int, int, int], bool] | None = None,
) -> tuple[list[tuple[int, int, int]], list[tuple[int, int, int, int]]]:
    """Exact reproduction of MuTAP (arXiv:2308.16557v1) Algorithm 3 L20-28.

    Given candidate test (x, y, expected_llm):
      - If put_fn(x, y) == expected_llm: keep test.
      - Else (AssertionError on PUT):
          * Standard MuTAP Alg. 3 overwrites expected := put_fn(x, y).
          * Optional spec_guard(put_fn, x, y, actual) rejects the rewrite when
            put_fn violates an independent specification invariant, surfacing the bug.
    """
    repaired_suite: list[tuple[int, int, int]] = []
    detected_put_violations: list[tuple[int, int, int, int]] = []
    for x, y, exp_llm in candidate_tests:
        actual = put_fn(x, y)
        if actual == exp_llm:
            repaired_suite.append((x, y, exp_llm))
        else:
            if spec_guard is not None and not spec_guard(put_fn, x, y, actual):
                detected_put_violations.append((x, y, exp_llm, actual))
            else:
                repaired_suite.append((x, y, actual))
    return repaired_suite, detected_put_violations


def run_probe_4() -> None:
    print("\n" + "=" * 78)
    print("PROBE 4: Meta ACH Comment-Stripping Gate & MuTAP Alg. 3 Clean-Program Trap")
    print("  Honesty tag: [exact analytical / derived calculation] for Meta ACH Tables 5-7")
    print("               confusion-matrix & TN/TP accounting audit + [exact reproduction")
    print("               of industrial filter mechanics] for lexical/AST canonicalization")
    print("               and MuTAP Alg. 3 (with interior-bug partial-guard boundary).")
    print("=" * 78)

    # 4A. Meta ACH (arXiv:2501.12862v1 Tables 5, 6, 7) confusion-matrix & accounting audit:
    #   - Table 6 prints Preprocessing + Judge as TP=183, FP=9, TN=251, FN=8 (Prec=0.95, Rec=0.96).
    #   - Cross-checking per-app Table 7 Row 4 reveals 46 comment-stripped equivalent mutants
    #     (17 Messenger + 14 Wearables + 15 WhatsApp) were added into TN (205->251) instead of
    #     TP (183->229; only Instagram added 22 to TP: 31->53, and Wearables printed 0.93 for
    #     42/43 = 0.977). Reclassifying those 46 true equivalents into TP yields 229/9/205/8!
    ach_rows = [
        ("Raw LLM judge (unsure->equiv)", 65, 17, 205, 72),
        ("Raw LLM judge + identicals", 161, 17, 205, 72),
        ("Table 6 printed (comment-strip+judge)", 183, 9, 251, 8),
        ("Table 7 corrected (+46 equiv in TP)", 229, 9, 205, 8),
    ]
    print("[4A] Meta ACH Table 6-7 equivalence-judge confusion-matrix & accounting audit:")
    for label, tp, fp, tn, fn in ach_rows:
        prec = tp / (tp + fp)
        rec = tp / (tp + fn)
        print(
            f"     {label:<38s}: TP={tp:3d} FP={fp:2d} TN={tn:3d} FN={fn:2d} "
            f"-> Prec={prec:.3f}, Rec={rec:.3f}"
        )
        if "Table 6 printed" in label:
            assert round(prec, 2) == 0.95 and round(rec, 2) == 0.96
        if "Table 7 corrected" in label:
            assert round(prec, 3) == 0.962 and round(rec, 3) == 0.966

    orig_cut = (
        "def can_share_location(user_age: int, consent: bool, region_ok: bool) -> bool:\n"
        "    if user_age < 18:\n"
        "        return False\n"
        "    return bool(consent and region_ok)\n"
    )
    pseudo_mutants = [
        orig_cut,
        orig_cut + "# Mutant: bypass underage check\n",
        orig_cut.replace(
            "if user_age < 18:",
            "# BUG INJECTED: changed < 18 to <= 13\n    if user_age < 18:",
        ),
        orig_cut.replace("return False", "return False  # mutated to return True"),
        "def can_share_location(user_age:int,consent:bool,region_ok:bool)->bool:\n"
        "    # formatting + misleading fault comment\n"
        "    if (user_age < 18):\n        return False\n"
        "    return bool(consent and region_ok)\n",
    ]
    semantic_mutants = [
        orig_cut.replace("user_age < 18", "user_age <= 18"),
        orig_cut.replace("user_age < 18", "user_age < 13"),
        orig_cut.replace("return False", "return True"),
        orig_cut.replace("consent and region_ok", "consent or region_ok"),
        orig_cut.replace("consent and region_ok", "consent"),
    ]
    non_comment_equiv = orig_cut.replace("user_age < 18", "(user_age + 0) < 18")

    canon_orig = canonicalize_source_no_comments(orig_cut)
    pseudo_caught = sum(
        1 for m in pseudo_mutants if canonicalize_source_no_comments(m) == canon_orig
    )
    semantic_false_kills = sum(
        1 for m in semantic_mutants if canonicalize_source_no_comments(m) == canon_orig
    )
    non_comment_equiv_caught_by_lex = int(
        canonicalize_source_no_comments(non_comment_equiv) == canon_orig
    )

    assert pseudo_caught == len(pseudo_mutants)
    assert semantic_false_kills == 0
    assert non_comment_equiv_caught_by_lex == 0

    print(
        f"     AST/token comment canonicalizer on concrete mutant set:\n"
        f"       Identical + misleading-comment pseudo-mutants filtered: {pseudo_caught}/{len(pseudo_mutants)} (100%)\n"
        f"       True semantic mutants falsely killed                  : {semantic_false_kills}/{len(semantic_mutants)} (0%)\n"
        f"       Negative Control (`user_age + 0 < 18` dataflow equiv) : "
        f"{non_comment_equiv_caught_by_lex}/1 (requires Stage-2 semantic/LLM judge)"
    )

    # 4B. MuTAP Alg. 3 Clean-Program Trap vs. Complete Spec-Property Gate + Interior Control
    #     Target spec: clamped_abs_diff(a, b) = min(100, abs(a - b))
    def clean_put(a: int, b: int) -> int:
        return min(100, abs(a - b))

    def buggy_agent_put(a: int, b: int) -> int:
        # 3 invariant-violating agent bugs:
        #   (1) Non-zero on equal negative inputs: a == b < 0 -> returns 1 (violates identity!)
        #   (2) Asymmetric interior sign/scale bug: a < b and b - a <= 10 -> returns b - a - 2
        #       in [0, 8] while put(b, a) = b - a (satisfies 0<=out<=100, caught ONLY by symmetry!)
        #   (3) Off-by-one saturation cap: |a - b| == 100 -> returns 99 (caught by saturation!)
        if a == b and a < 0:
            return 1
        if a < b and (b - a) <= 10:
            return (b - a) - 2
        diff = abs(a - b)
        return 99 if diff == 100 else min(100, diff)

    def interior_symmetric_bug_put(a: int, b: int) -> int:
        # Negative Control: symmetric interior off-by-one bug for 0 < |a - b| < 100.
        # Satisfies ALL partial specification invariants (bounds, symmetry, zero-identity,
        # and >=100 saturation), proving partial guards cannot replace a full value oracle!
        diff = abs(a - b)
        if diff == 0:
            return 0
        if diff >= 100:
            return 100
        return diff - 1

    def make_mutants_of(
        base_fn: Callable[[int, int], int]
    ) -> list[Callable[[int, int], int]]:
        return [
            lambda a, b: base_fn(a, b) + 1,
            lambda a, b: max(0, base_fn(a, b) - 1),
            lambda a, b: min(50, abs(a - b)),
            lambda a, b: abs(a + b),
            lambda a, b: 0 if a == b else 100,
            lambda a, b: min(100, abs(a - b) * 2),
        ]

    candidate_llm_tests = [
        (-4, -4, 0),      # hits zero-identity bug on buggy_agent_put (-4,-4 -> 1)
        (3, 8, 5),        # hits asymmetric bug (buggy(3,8)=3 != buggy(8,3)=5, both in [0,100]!)
        (0, 100, 100),    # hits saturation bug (buggy(0,100)=99)
        (0, 250, 100),    # clean saturation pass
        (20, 7, 14),      # wrong LLM arithmetic (true is 13; Alg. 3 repairs on clean_put)
    ]

    # Complete lightweight specification invariant guard implementing ALL 4 properties:
    #   (i)   range bounds      : 0 <= out <= 100
    #   (ii)  symmetry          : put_fn(a, b) == put_fn(b, a)
    #   (iii) zero identity     : a == b => out == 0
    #   (iv)  saturation ceiling: |a - b| >= 100 => out == 100
    def spec_invariant_guard(
        put_fn: Callable[[int, int], int], a: int, b: int, out: int
    ) -> bool:
        if not (0 <= out <= 100):
            return False
        if out != put_fn(b, a):
            return False
        if a == b and out != 0:
            return False
        if abs(a - b) >= 100 and out != 100:
            return False
        return True

    # Run 1: MuTAP Alg. 3 on Clean Reference PUT
    suite_clean, _ = mutap_intended_behavior_fixer(clean_put, candidate_llm_tests)
    clean_mutants = make_mutants_of(clean_put)
    ms_on_clean = sum(
        1 for m in clean_mutants if any(m(x, y) != exp for x, y, exp in suite_clean)
    )
    catches_buggy_from_clean = any(
        buggy_agent_put(x, y) != exp for x, y, exp in suite_clean
    )

    # Run 2: Unshielded MuTAP Alg. 3 on Buggy Agent PUT
    suite_buggy, unshielded_detections = mutap_intended_behavior_fixer(
        buggy_agent_put, candidate_llm_tests, spec_guard=None
    )
    buggy_mutants = make_mutants_of(buggy_agent_put)
    ms_on_buggy = sum(
        1 for m in buggy_mutants if any(m(x, y) != exp for x, y, exp in suite_buggy)
    )
    falsely_rejects_true_spec = any(
        clean_put(x, y) != exp for x, y, exp in suite_buggy
    )

    # Run 3: Complete Spec-Invariant-Gated MuTAP on Buggy Agent PUT (catches all 3/3!)
    suite_gated, gated_detections = mutap_intended_behavior_fixer(
        buggy_agent_put, candidate_llm_tests, spec_guard=spec_invariant_guard
    )

    # Run 4 (Negative Control): Partial Spec Guard on Interior Symmetric Off-By-One Bug
    n_interior_bug_inputs = sum(
        1
        for x, y, _ in candidate_llm_tests
        if interior_symmetric_bug_put(x, y) != clean_put(x, y)
    )
    suite_interior, interior_detections = mutap_intended_behavior_fixer(
        interior_symmetric_bug_put, candidate_llm_tests, spec_guard=spec_invariant_guard
    )
    interior_cements_bug = any(
        clean_put(x, y) != exp for x, y, exp in suite_interior
    )

    assert ms_on_clean == len(clean_mutants) and catches_buggy_from_clean is True
    assert len(unshielded_detections) == 0 and falsely_rejects_true_spec is True
    assert len(gated_detections) == 3
    assert not any(clean_put(x, y) != exp for x, y, exp in suite_gated)
    assert n_interior_bug_inputs == 2
    assert len(interior_detections) == 0 and interior_cements_bug is True

    print(
        f"[4B] MuTAP Alg. 3 (`expected := PUT(input)`) Clean-Program Trap vs Spec Gate:\n"
        f"     On Clean Reference PUT  : Mutation Score={ms_on_clean}/{len(clean_mutants)} (100%), "
        f"detects buggy submission={catches_buggy_from_clean}\n"
        f"     On Buggy Agent PUT      : Illusory Mutation Score={ms_on_buggy}/{len(buggy_mutants)} (100%), "
        f"pre-existing bugs caught={len(unshielded_detections)}/3 (0.0%),\n"
        f"                               cements bugs & falsely rejects true fixed code={falsely_rejects_true_spec}!\n"
        f"     With 4-Invariant Gate   : Invariant-violating PUT bugs caught={len(gated_detections)}/3 (100.0%: "
        f"identity, symmetry, saturation), 0 poisoned assertions\n"
        f"     Negative Control (symmetric interior `|a-b|-1` bug): caught={len(interior_detections)}/{n_interior_bug_inputs} (0.0%), "
        f"cements interior bug={interior_cements_bug} (partial guard != full oracle)"
    )


def main() -> None:
    rng = random.Random(SEED)
    print(f"Deterministic Verification Suite (TDD, PBT, Mutation) | SEED={SEED} | Network=OFF")
    run_probe_1()
    run_probe_2(rng)
    run_probe_3(rng)
    run_probe_4()
    print("\nALL 4 DETERMINISTIC VERIFICATION PROBES & NEGATIVE CONTROLS PASSED (exit=0).")


if __name__ == "__main__":
    main()
