#!/usr/bin/env python3
"""Standalone Python 3.10+ stdlib verification probe suite for organizational
software-reuse economics, faceted reuse catalogs, executable architecture gates,
and registry staleness / broadcast-overload dynamics.

Properties:
- Pure Python 3.10+ standard library (zero third-party packages, zero network I/O).
- Zero persistent or temporary disk writes; zero local filesystem paths in stdout.
- Bit-identical deterministic output across arbitrary PYTHONHASHSEED values.
- Explicit evidence-class banners separating:
  * [exact reproduction of archival dataset / pinned repo logic]
  * [parametric analytical / game-theoretic model]
  * [controlled simulation]
"""
from __future__ import annotations

import hashlib
import heapq
import json
import math
import re
from collections import Counter
from fractions import Fraction
from typing import Any

EVIDENCE_EXACT_REPO_OR_DATASET = (
    "[exact reproduction of archival dataset / pinned repo logic]"
)
EVIDENCE_PARAMETRIC_ANALYTICAL = "[parametric analytical / game-theoretic model]"
EVIDENCE_CONTROLLED_SIM = "[controlled simulation]"


# ==============================================================================
# PROBE P1: Morisio, Ezran & Tully (IEEE TSE 2002) & Menzies & Di Stefano (2003)
# Archival TERA-PROMISE reuse.arff (Zenodo DOI: 10.5281/zenodo.322466)
# ==============================================================================

MORISIO_2002_COLUMNS: tuple[str, ...] = (
    "id",
    "sw_staff",
    "overall_staff",
    "prod_type",
    "sw_and_prod",
    "sp_maturity",
    "domain",
    "sw_type",
    "baseline_size",
    "dev_approach",
    "staff_exp",
    "top_mgmt",
    "reuse_roles",
    "reuse_proc",
    "nonreuse_mod",
    "repository",
    "human_factors",
    "reuse_approach",
    "work_products",
    "domain_analysis",
    "origin",
    "indep_team",
    "when_assets",
    "qualification",
    "config_mgmt",
    "rewards_policy",
    "num_assets",
    "outcome",
)

# Verbatim @data payload from Zenodo 10.5281/zenodo.322466 reuse.arff
# (full file SHA-256: 814af0a531c6d199717fd689b16b254ce7219e907ac60e61795cea4ba09ef18c;
#  stripped 24-row @data payload SHA-256: c4602347d6a0f4eacf6ff5db2a7362afe2f368b555fa1e7b67f353b70d021732)
MORISIO_2002_RAW_DATA = """\
A,L,L,product-family,product,high,TLC,Technical,L,OO,high,yes,yes,yes,yes,yes,yes,tight,D+C,yes,ex-novo,yes,before,yes,yes,no,51_to_100,success
B,L,L,product-family,product,high,TLC,Technical,M,OO,high,yes,yes,yes,yes,yes,yes,tight,D+C,yes,ex-novo,yes,before,yes,yes,no,51_to_100,success
D,L,L,isolated,alone,middle,SE-Tools,Technical,M,OO,middle,yes,yes,no,no,yes,no,loose,C,no,as-is,no,before,no,no,yes,21_to_50,failure
E,L,L,isolated,alone,middle,TLC,Technical,M,OO,middle,yes,yes,no,no,yes,no,loose,C,no,as-is,no,before,no,no,yes,21_to_50,failure
F,L,L,isolated,alone,middle,TLC,Technical,M,OO,middle,yes,yes,no,no,yes,no,loose,C,no,as-is,no,before,no,no,yes,21_to_50,failure
G,L,X,product-family,process,low,Bank,Business,L,OO,middle,yes,yes,yes,yes,yes,yes,loose,C,no,reeng,no,justintime,yes,yes,no,51_to_100,success
H,M,M,product-family,product,high,Engine_Controller,Embedded-RT,L,OO,middle,yes,yes,yes,yes,yes,yes,tight,R+D+C,no,reeng,no,justintime,no,yes,no,51_to_100,success
I,M,X,product-family,product,middle,FMS,Technical,M,OO,high,no,no,no,yes,yes,no,loose,D+C,no,reeng,no,justintime,no,no,no,51_to_100,failure
J,M,X,product-family,product,middle,FMS,Technical,M,OO,middle,no,no,no,yes,yes,no,loose,D+C,no,reeng,no,justintime,no,no,no,51_to_100,failure
K,M,X,product-family,product,middle,ATC,Non-Embedded-RT,L,proc,high,yes,yes,yes,yes,yes,yes,tight,R+D+C,yes,reeng,no,justintime,yes,yes,no,100+,success
L,M,X,product-family,product,high,TS,Technical,M,proc,high,yes,yes,yes,yes,yes,yes,tight,R+D+C,yes,reeng,no,justintime,yes,yes,no,51_to_100,success
M,M,X,product-family,product,high,SE-Tools,Technical,L,proc,middle,yes,yes,yes,yes,yes,yes,tight,R+D+C,yes,reeng,no,justintime,yes,yes,no,100+,success
N,M,X,product-family,product,middle,TLC,Non-Embedded-RT,M,proc,middle,yes,yes,yes,yes,yes,yes,tight,R+D+C,yes,reeng,no,justintime,yes,yes,no,51_to_100,success
O,S,L,product-family,product,middle,Space,Embedded-RT,M,OO,middle,yes,no,no,no,yes,no,loose,R+D+C,no,ex-novo,no,before,yes,yes,no,1_to_20,failure
P,S,M,product-family,product,middle,Manufacturing,Embedded-RT,M,proc,middle,yes,yes,yes,yes,yes,yes,loose,R+D+C,yes,reeng,no,justintime,yes,yes,no,100+,success
Q,S,M,product-family,product,middle,Manufacturing,Technical,M,proc,middle,yes,yes,yes,yes,yes,yes,loose,R+D+C,yes,reeng,no,justintime,yes,yes,no,100+,success
R,S,M,product-family,product,middle,TLC,Embedded-RT,L,proc,high,yes,yes,yes,yes,yes,yes,loose,C,no,reeng,no,justintime,yes,yes,no,1_to_20,success
S,S,S,product-family,product,low,Measurement,Technical,M,OO,middle,yes,yes,yes,yes,yes,yes,tight,C,no,ex-novo,no,justintime,yes,yes,no,100+,success
T,S,X,product-family,product,middle,FMS,Embedded-RT,M,OO,high,no,yes,yes,no,yes,no,loose,C,no,reeng,no,justintime,yes,yes,no,1_to_20,failure
U,S,X,product-family,process,low,Finance,Business,L,OO,low,yes,yes,no,yes,yes,yes,tight,R+D+C,no,reeng,no,justintime,no,yes,no,100+,success
V,S,X,product-family,product,low,TLC,Technical,S,OO,middle,yes,yes,yes,yes,yes,yes,tight,C,no,reeng,no,justintime,yes,yes,no,1_to_20,success
W,M,L,product-family,alone,middle,Manufacturing,Business,L,OO,middle,yes,no,yes,no,yes,yes,tight,C,yes,reeng,no,justintime,no,no,no,1_to_20,success
X,S,S,product-family,NA,low,Book-Keeping,Business,S,proc,middle,yes,NA,NA,NA,NA,no,NA,NA,NA,NA,NA,NA,NA,NA,no,NA,failure
Y,M,M,isolated,product,high,FMS,Embedded-RT,not_available,not_available,not_available,no,yes,no,no,yes,yes,loose,C,no,as-is,no,before,no,no,no,100+,failure"""


def fisher_exact_rational(a: int, b: int, c: int, d: int) -> dict[str, Any]:
    """Exact hypergeometric Fisher test using exact rational arithmetic (no float tie drift)."""
    r1, r2 = a + b, c + d
    c1 = a + c
    n = r1 + r2
    denom = math.comb(n, c1)

    def prob_frac(k: int) -> Fraction:
        return Fraction(math.comb(r1, k) * math.comb(r2, c1 - k), denom)

    lo = max(0, c1 - r2)
    hi = min(r1, c1)
    p_obs = prob_frac(a)
    p_less = sum((prob_frac(k) for k in range(lo, a + 1)), Fraction(0, 1))
    p_greater = sum((prob_frac(k) for k in range(a, hi + 1)), Fraction(0, 1))
    p_two_minlik = sum(
        (prob_frac(k) for k in range(lo, hi + 1) if prob_frac(k) <= p_obs),
        Fraction(0, 1),
    )
    p_two_central = min(Fraction(1, 1), 2 * min(p_less, p_greater))
    return {
        "p_one_sided_less_exact": f"{p_less.numerator}/{p_less.denominator}",
        "p_one_sided_less": round(float(p_less), 6),
        "p_one_sided_greater": round(float(p_greater), 6),
        "p_two_sided_minlik_exact": f"{p_two_minlik.numerator}/{p_two_minlik.denominator}",
        "p_two_sided_minlik": round(float(p_two_minlik), 6),
        "p_two_sided_central": round(float(p_two_central), 6),
    }


def wilson_95_ci(k: int, n: int) -> tuple[float, float]:
    if n == 0:
        return (0.0, 1.0)
    z = 1.959963984540054
    p = k / n
    denom = 1.0 + (z * z) / n
    center = (p + (z * z) / (2.0 * n)) / denom
    half = (z * math.sqrt((p * (1.0 - p) + (z * z) / (4.0 * n)) / n)) / denom
    return (round(max(0.0, center - half), 4), round(min(1.0, center + half), 4))


def run_probe_p1() -> dict[str, Any]:
    payload_sha = hashlib.sha256(MORISIO_2002_RAW_DATA.encode("utf-8")).hexdigest()
    assert (
        payload_sha
        == "c4602347d6a0f4eacf6ff5db2a7362afe2f368b555fa1e7b67f353b70d021732"
    )

    rows: list[dict[str, str]] = []
    for line in MORISIO_2002_RAW_DATA.splitlines():
        parts = line.strip().split(",")
        assert len(parts) == 28 == len(MORISIO_2002_COLUMNS)
        rows.append(dict(zip(MORISIO_2002_COLUMNS, parts)))

    assert len(rows) == 24
    # Project C is absent in Morisio et al. (2002): A..Y minus C = 24 projects.
    expected_ids = [chr(c) for c in range(ord("A"), ord("Y") + 1) if chr(c) != "C"]
    assert [r["id"] for r in rows] == expected_ids

    # Morisio et al. (2002, Sec. 5.2.4 p. 349 & Appendix A.1 p. 354) explicitly exclude
    # interrupted Project X from dataset analysis because 14 fields are NA.
    rows_op23 = [r for r in rows if r["id"] != "X"]
    assert len(rows_op23) == 23

    def analyze_factor(
        dataset: list[dict[str, str]], col: str, pos_val: str, neg_val: str
    ) -> dict[str, Any]:
        a = sum(1 for r in dataset if r[col] == pos_val and r["outcome"] == "success")
        b = sum(1 for r in dataset if r[col] == pos_val and r["outcome"] == "failure")
        c = sum(1 for r in dataset if r[col] == neg_val and r["outcome"] == "success")
        d = sum(1 for r in dataset if r[col] == neg_val and r["outcome"] == "failure")
        na_cnt = sum(1 for r in dataset if r[col] not in (pos_val, neg_val))
        stats = fisher_exact_rational(a, b, c, d)
        return {
            "n_evaluated": a + b + c + d,
            "na_excluded": na_cnt,
            "matrix_pos_succ_fail": [a, b],
            "matrix_neg_succ_fail": [c, d],
            "pos_success_rate": round(a / (a + b), 4) if (a + b) else None,
            "neg_success_rate": round(c / (c + d), 4) if (c + d) else None,
            "pos_wilson_95": list(wilson_95_ci(a, a + b)),
            "neg_wilson_95": list(wilson_95_ci(c, c + d)),
            **stats,
        }

    spec = (
        ("repository_yes_vs_no", "repository", "yes", "no"),
        ("human_factors_yes_vs_no", "human_factors", "yes", "no"),
        ("reuse_proc_yes_vs_no", "reuse_proc", "yes", "no"),
        ("nonreuse_mod_yes_vs_no", "nonreuse_mod", "yes", "no"),
        ("top_mgmt_yes_vs_no", "top_mgmt", "yes", "no"),
        ("prod_type_family_vs_isolated", "prod_type", "product-family", "isolated"),
        ("rewards_policy_yes_vs_no", "rewards_policy", "yes", "no"),
    )
    factors_n24 = {k: analyze_factor(rows, col, pv, nv) for k, col, pv, nv in spec}
    factors_n23 = {k: analyze_factor(rows_op23, col, pv, nv) for k, col, pv, nv in spec}

    # Verify exact Repository & Rewards Policy counts and rational Fisher p-values:
    assert factors_n23["repository_yes_vs_no"]["matrix_pos_succ_fail"] == [15, 8]
    assert factors_n23["repository_yes_vs_no"]["matrix_neg_succ_fail"] == [0, 0]
    rewards_yes_ids = [r["id"] for r in rows if r["rewards_policy"] == "yes"]
    assert rewards_yes_ids == ["D", "E", "F"]
    assert factors_n24["rewards_policy_yes_vs_no"]["p_two_sided_minlik_exact"] == "21/506"
    assert factors_n23["rewards_policy_yes_vs_no"]["p_two_sided_minlik_exact"] == "8/253"

    # Compare Morisio CART 2-split vs Menzies & Di Stefano (2003) J4.8 1-split & TAR2 rules:
    cart_n23_hits = sum(
        1
        for r in rows_op23
        if (
            (r["human_factors"] == "yes" and r["prod_type"] == "product-family")
            == (r["outcome"] == "success")
        )
    )
    j48_hf_only_n23_hits = sum(
        1
        for r in rows_op23
        if ((r["human_factors"] == "yes") == (r["outcome"] == "success"))
    )
    j48_hf_only_n24_hits = sum(
        1
        for r in rows
        if ((r["human_factors"] == "yes") == (r["outcome"] == "success"))
    )
    # Only Project Y separates the 2-predicate CART tree from single-predicate Human Factors:
    disagree_ids = [
        r["id"]
        for r in rows
        if (r["human_factors"] == "yes")
        != (r["human_factors"] == "yes" and r["prod_type"] == "product-family")
    ]
    assert cart_n23_hits == 23
    assert j48_hf_only_n23_hits == 22 and j48_hf_only_n24_hits == 23
    assert disagree_ids == ["Y"]

    # Morisio Sec. 6 high-level process quartet & Menzies TAR2 100%-precision rules:
    morisio_quartet = [
        r["id"]
        for r in rows_op23
        if r["top_mgmt"] == "yes"
        and r["reuse_proc"] == "yes"
        and r["nonreuse_mod"] == "yes"
        and r["human_factors"] == "yes"
    ]
    assert len(morisio_quartet) == 13
    assert all(r["outcome"] == "success" for r in rows_op23 if r["id"] in morisio_quartet)
    # Exceptions among the 15 successes are strictly U (reuse_proc=no) and W (nonreuse_mod=no):
    quartet_exceptions = sorted(
        r["id"]
        for r in rows_op23
        if r["outcome"] == "success" and r["id"] not in morisio_quartet
    )
    assert quartet_exceptions == ["U", "W"]

    tar2_tight = [r for r in rows_op23 if r["reuse_approach"] == "tight"]
    tar2_da = [r for r in rows_op23 if r["domain_analysis"] == "yes"]
    tar2_large_base = [r for r in rows_op23 if r["baseline_size"] == "L"]
    assert len(tar2_tight) == 11 and all(r["outcome"] == "success" for r in tar2_tight)
    assert len(tar2_da) == 9 and all(r["outcome"] == "success" for r in tar2_da)
    assert len(tar2_large_base) == 8 and all(
        r["outcome"] == "success" for r in tar2_large_base
    )

    return {
        "evidence_class": EVIDENCE_EXACT_REPO_OR_DATASET,
        "raw_data_payload_sha256": payload_sha,
        "n_total_surveyed": 24,
        "n_operational_morisio_cohort": 23,
        "interrupted_excluded_project": "X",
        "rewards_policy_yes_projects": rewards_yes_ids,
        "factors_n23_operational": factors_n23,
        "factors_n24_all_rows": factors_n24,
        "rule_comparison": {
            "morisio_cart_two_split_n23": f"{cart_n23_hits}/23",
            "menzies_j48_human_factors_only_n23": f"{j48_hf_only_n23_hits}/23",
            "menzies_j48_human_factors_only_n24": f"{j48_hf_only_n24_hits}/24",
            "cart_second_split_sole_support_project": disagree_ids[0],
            "morisio_sec6_process_quartet_precision": f"{len(morisio_quartet)}/{len(morisio_quartet)}",
            "morisio_sec6_success_exceptions": quartet_exceptions,
            "menzies_tar2_tight_reuse_success": f"{len(tar2_tight)}/11",
            "menzies_tar2_domain_analysis_success": f"{len(tar2_da)}/9",
            "menzies_tar2_large_baseline_success": f"{len(tar2_large_base)}/8",
        },
    }


# ==============================================================================
# PROBE P2: Author-Parameterized Reuse Decision Model Motivated by Krueger (1992),
# Frakes & Fox (1996) 7-Gate Cascade, Markus (2001) Context Distance &
# Antons & Piller (2015) NIH / Xenophilia Attitude Distortion
# ==============================================================================


def frakes_fox_seven_gate_survival(gate_pass_probs: tuple[float, ...]) -> float:
    """7 conjunctive reuse gates (Frakes & Fox 1996, IEEE TSE 22(4):274-279):
    1: attempt, 2: exists, 3: available, 4: found, 5: understood, 6: valid, 7: integratable.
    """
    assert len(gate_pass_probs) == 7
    prod = 1.0
    for p in gate_pass_probs:
        assert 0.0 <= p <= 1.0
        prod *= p
    return prod


def expected_reuse_vs_scratch(
    *,
    c_scratch: float,
    c_search: float,
    p_avail: float,
    c_understand_base: float,
    context_distance_delta: float,
    q_valid: float,
    c_adapt_slope: float,
    conceptual_distance_dc: float,
    c_verify: float,
    nih_bias_beta: float = 1.0,
) -> dict[str, Any]:
    """Author-parameterized expected-cost tree (linear comprehension/adaptation slopes
    and [0, 1]-clamped validity perception q_perc = clip(q_valid / beta, 0, 1)).
    """
    assert nih_bias_beta > 0.0
    assert 0.0 <= p_avail <= 1.0 and 0.0 <= q_valid <= 1.0
    c_und = c_understand_base * (1.0 + 3.0 * context_distance_delta)
    c_adp = c_adapt_slope * conceptual_distance_dc
    obj_cost = (
        c_search
        + (1.0 - p_avail) * c_scratch
        + p_avail * (c_und + q_valid * (c_adp + c_verify) + (1.0 - q_valid) * c_scratch)
    )
    net_savings = (
        p_avail * q_valid * (c_scratch - c_adp - c_verify)
        - (c_search + p_avail * c_und)
    )
    assert abs((c_scratch - obj_cost) - net_savings) < 1e-9

    # Clamp perceived validity into [0, 1] so both NIH (beta > 1) and IE/xenophilia
    # (0 < beta < 1, Antons & Piller 2015) remain well-formed probabilities.
    q_perc = min(1.0, max(0.0, q_valid / nih_bias_beta))
    perc_cost = (
        c_search * nih_bias_beta
        + (1.0 - p_avail) * c_scratch
        + p_avail
        * (
            c_und * nih_bias_beta
            + q_perc * (c_adp * nih_bias_beta + c_verify * nih_bias_beta)
            + (1.0 - q_perc) * c_scratch
        )
    )
    numer = p_avail * q_valid * (c_scratch - c_verify) - (c_search + p_avail * c_und)
    dc_star = numer / (p_avail * q_valid * c_adapt_slope)

    actor_attempts = perc_cost < c_scratch
    realized_cost = obj_cost if actor_attempts else c_scratch
    optimal_cost = min(obj_cost, c_scratch)
    deadweight_loss = realized_cost - optimal_cost
    return {
        "objective_attempt_cost": round(obj_cost, 3),
        "perceived_attempt_cost": round(perc_cost, 3),
        "scratch_cost": round(c_scratch, 3),
        "objective_net_savings": round(net_savings, 3),
        "dc_break_even": round(dc_star, 4),
        "actor_attempts_reuse": actor_attempts,
        "deadweight_bias_loss": round(deadweight_loss, 3),
    }


def run_probe_p2() -> dict[str, Any]:
    r_raw = expected_reuse_vs_scratch(
        c_scratch=100.0,
        c_search=18.0,
        p_avail=0.35,
        c_understand_base=10.0,
        context_distance_delta=0.90,
        q_valid=0.50,
        c_adapt_slope=60.0,
        conceptual_distance_dc=0.35,
        c_verify=12.0,
        nih_bias_beta=1.0,
    )
    r_sanitized_unbiased = expected_reuse_vs_scratch(
        c_scratch=100.0,
        c_search=4.0,
        p_avail=0.85,
        c_understand_base=10.0,
        context_distance_delta=0.10,
        q_valid=0.95,
        c_adapt_slope=60.0,
        conceptual_distance_dc=0.35,
        c_verify=6.0,
        nih_bias_beta=1.0,
    )
    r_sanitized_nih = expected_reuse_vs_scratch(
        c_scratch=100.0,
        c_search=4.0,
        p_avail=0.85,
        c_understand_base=10.0,
        context_distance_delta=0.10,
        q_valid=0.95,
        c_adapt_slope=60.0,
        conceptual_distance_dc=0.35,
        c_verify=6.0,
        nih_bias_beta=2.1,
    )
    r_high_dc = expected_reuse_vs_scratch(
        c_scratch=100.0,
        c_search=4.0,
        p_avail=0.85,
        c_understand_base=10.0,
        context_distance_delta=0.10,
        q_valid=0.95,
        c_adapt_slope=60.0,
        conceptual_distance_dc=1.40,
        c_verify=6.0,
        nih_bias_beta=1.0,
    )
    # Antons & Piller (2015) symmetric opposite bias ablation: "Invented Elsewhere"
    # (xenophilia beta = 0.45 < 1) over-adopts a high-dc external component that
    # objectively should be built from scratch.
    r_high_dc_xenophilia = expected_reuse_vs_scratch(
        c_scratch=100.0,
        c_search=4.0,
        p_avail=0.85,
        c_understand_base=10.0,
        context_distance_delta=0.10,
        q_valid=0.95,
        c_adapt_slope=60.0,
        conceptual_distance_dc=1.40,
        c_verify=6.0,
        nih_bias_beta=0.45,
    )

    # Exact rational verification of sanitized net savings (17559/400 = 43.8975;
    # 43.898 vs 43.897 in float64 is a 1-ULP half-way tie split around 43.8975):
    exact_sanitized_savings = (
        Fraction(17, 20) * Fraction(19, 20) * (100 - 21 - 6)
        - (4 + Fraction(17, 20) * 13)
    )
    assert exact_sanitized_savings == Fraction(17559, 400) == Fraction(438975, 10000)

    assert not r_raw["actor_attempts_reuse"] and r_raw["objective_net_savings"] < 0
    assert r_raw["deadweight_bias_loss"] == 0.0
    assert (
        r_sanitized_unbiased["actor_attempts_reuse"]
        and r_sanitized_unbiased["objective_net_savings"] > 0
    )
    assert (
        not r_sanitized_nih["actor_attempts_reuse"]
        and r_sanitized_nih["deadweight_bias_loss"] > 0
    )
    assert not r_high_dc["actor_attempts_reuse"] and r_high_dc["objective_net_savings"] < 0
    assert (
        r_high_dc_xenophilia["actor_attempts_reuse"]
        and r_high_dc_xenophilia["deadweight_bias_loss"] > 0
    )

    # Frakes & Fox (1996) 7-gate cascade non-vacuity check:
    p_all_good = frakes_fox_seven_gate_survival((0.92, 0.90, 0.95, 0.90, 0.92, 0.95, 0.94))
    p_no_attempt = frakes_fox_seven_gate_survival((0.0, 0.99, 0.99, 0.99, 0.99, 0.99, 0.99))
    p_weak_each = frakes_fox_seven_gate_survival((0.70,) * 7)
    assert p_no_attempt == 0.0
    assert round(p_weak_each, 4) == 0.0824  # 0.70^7 = 8.24% despite 70% pass rate per gate

    return {
        "evidence_class": EVIDENCE_PARAMETRIC_ANALYTICAL,
        "exact_sanitized_net_savings_rational": f"{exact_sanitized_savings.numerator}/{exact_sanitized_savings.denominator}",
        "raw_producer_dump_rational_skip": r_raw,
        "sanitized_catalog_unbiased_reuse": r_sanitized_unbiased,
        "sanitized_catalog_nih_rejection": r_sanitized_nih,
        "sanitized_catalog_high_dc_rational_scratch": r_high_dc,
        "sanitized_catalog_high_dc_xenophilia_overadoption": r_high_dc_xenophilia,
        "frakes_fox_7_gate_cascade": {
            "curated_proactive_survival": round(p_all_good, 4),
            "uniform_70pct_per_gate_survival": round(p_weak_each, 4),
            "gate1_no_attempt_zero_ablation": p_no_attempt,
        },
    }


# ==============================================================================
# PROBE P3: Thorn & Connolly (1987) / Connolly & Thorn (1990) Discretionary-DB
# Public-Goods Game & Derived 3-Action Syntactic-Quota Goodhart Extension
# ==============================================================================


def solve_discretionary_db_mechanism(
    *,
    n_agents: int,
    b_peer: float,
    b_self: float,
    c_curate: float,
    c_spam: float,
    c_noise_read: float,
    quota_fine_skip: float,
    semantic_ci_gate: bool,
    verified_curate_credit: float = 0.0,
) -> dict[str, Any]:
    """Exhaustively checks all (n_c, n_s) peer action counts (n_c + n_s <= n_agents - 1)
    to find strict dominant strategies, symmetric pure-strategy Nash equilibria, and
    fleet-wide social welfare across actions ('skip', 'spam', 'curate').
    """
    actions = ("skip", "spam", "curate")

    def utility(ai: str, nc_peers: int, ns_peers: int) -> float:
        # Peer externalities accrue regardless of player i's own action (non-excludable).
        # Under semantic_ci_gate, spam submissions are rejected at ingest and never pollute reads.
        eff_spam_peers = 0 if semantic_ci_gate else ns_peers
        ext = nc_peers * b_peer - eff_spam_peers * c_noise_read
        if ai == "skip":
            return ext - quota_fine_skip
        if ai == "spam":
            # If semantic CI gate is active, boilerplate spam fails verification and still pays fine.
            fine = quota_fine_skip if semantic_ci_gate else 0.0
            return ext - c_spam - fine
        if ai == "curate":
            return ext + b_self + verified_curate_credit - c_curate
        raise ValueError(ai)

    peer_profiles = [
        (nc, ns)
        for nc in range(n_agents)
        for ns in range(n_agents - nc)
    ]
    assert len(peer_profiles) == (n_agents * (n_agents + 1)) // 2

    dominant: str | None = None
    for cand in actions:
        if all(
            all(
                utility(cand, nc, ns) > utility(other, nc, ns)
                for other in actions
                if other != cand
            )
            for nc, ns in peer_profiles
        ):
            dominant = cand

    symmetric_nash: list[str] = []
    for cand in actions:
        nc = (n_agents - 1) if cand == "curate" else 0
        ns = (n_agents - 1) if cand == "spam" else 0
        u_cand = utility(cand, nc, ns)
        if all(u_cand >= utility(other, nc, ns) for other in actions):
            symmetric_nash.append(cand)

    assert len(symmetric_nash) == 1
    eq_act = symmetric_nash[0]
    nc_eq = (n_agents - 1) if eq_act == "curate" else 0
    ns_eq = (n_agents - 1) if eq_act == "spam" else 0
    eq_payoff_sum = n_agents * utility(eq_act, nc_eq, ns_eq)
    # Net organizational technical welfare nets out internal fines and selective credits:
    transfer_adjustment = (
        n_agents * quota_fine_skip
        if (eq_act == "skip" or (eq_act == "spam" and semantic_ci_gate))
        else (-n_agents * verified_curate_credit if eq_act == "curate" else 0.0)
    )
    eq_tech_welfare = eq_payoff_sum + transfer_adjustment
    return {
        "strict_dominant_action": dominant,
        "symmetric_nash_equilibria": symmetric_nash,
        "equilibrium_agent_payoff_sum": round(eq_payoff_sum, 2),
        "equilibrium_fleet_welfare": round(eq_tech_welfare, 2),
        "profiles_checked": len(peer_profiles),
    }


def run_probe_p3() -> dict[str, Any]:
    n_agents = 12
    b_peer = 5.0
    b_self = 0.0
    c_curate = 14.0
    c_spam = 1.5
    c_noise_read = 0.8
    quota_fine = 8.0
    c_ci_infra = 0.4

    social_manual_opt = n_agents * ((n_agents - 1) * b_peer + b_self - c_curate)
    m1_voluntary = solve_discretionary_db_mechanism(
        n_agents=n_agents,
        b_peer=b_peer,
        b_self=b_self,
        c_curate=c_curate,
        c_spam=c_spam,
        c_noise_read=c_noise_read,
        quota_fine_skip=0.0,
        semantic_ci_gate=False,
    )
    m2_unverified_quota = solve_discretionary_db_mechanism(
        n_agents=n_agents,
        b_peer=b_peer,
        b_self=b_self,
        c_curate=c_curate,
        c_spam=c_spam,
        c_noise_read=c_noise_read,
        quota_fine_skip=quota_fine,
        semantic_ci_gate=False,
    )
    # Non-vacuity positive control (Connolly & Thorn 1990 / Cabrera & Cabrera 2002):
    # Semantic CI gate rejects spam AND selective credit R = 7.0 + quota_fine = 8.0 > c_curate = 14.0
    # flips strict dominance to 'curate' (net fleet tech welfare excludes budget-balanced transfers).
    m3_verified_selective = solve_discretionary_db_mechanism(
        n_agents=n_agents,
        b_peer=b_peer,
        b_self=b_self,
        c_curate=c_curate,
        c_spam=c_spam,
        c_noise_read=c_noise_read,
        quota_fine_skip=quota_fine,
        semantic_ci_gate=True,
        verified_curate_credit=7.0,
    )
    # Zero-marginal-cost automated CI harvesting (c_post = 0 to agent; infra cost c_ci = 0.4):
    m4_auto_ci_welfare = n_agents * ((n_agents - 1) * b_peer - c_ci_infra)

    assert m1_voluntary["strict_dominant_action"] == "skip"
    assert m1_voluntary["equilibrium_fleet_welfare"] == 0.0
    assert m2_unverified_quota["strict_dominant_action"] == "spam"
    assert m2_unverified_quota["equilibrium_fleet_welfare"] == -123.6
    assert m3_verified_selective["strict_dominant_action"] == "curate"
    assert m4_auto_ci_welfare == 655.2 > social_manual_opt == 492.0

    return {
        "evidence_class": EVIDENCE_PARAMETRIC_ANALYTICAL,
        "n_agents": n_agents,
        "social_manual_optimum_welfare": round(social_manual_opt, 2),
        "M1_voluntary_manual": m1_voluntary,
        "M2_mandated_unverified_quota": m2_unverified_quota,
        "M3_semantic_gate_selective_incentive_control": m3_verified_selective,
        "M4_automated_ci_harvesting_welfare": round(m4_auto_ci_welfare, 2),
    }


# ==============================================================================
# PROBE P4:
# Part 4A [exact reproduction of archival dataset / pinned repo logic]:
#   - TNG/ArchUnit @ df8ea3d7c16118eee4c8d676ae115187e1d37dcc
#     (FreezingArchRule.java:120-267 + ViolationLineMatcherFactory.java:49-107)
#   - open-telemetry/semantic-conventions @ 68dacf3a1a555e9c3358f9d1ea5d0c310d424d1e
#     (policies/namespace_ownership.rego:1-87 + reference_attributes.rego:6-44)
# Part 4B [controlled simulation]:
#   - Prieto-Diaz (1987, 1991) 6-Facet Conceptual-Graph Dijkstra Matcher vs. BM25
#     (including multi-hop + asymmetric specialization/generalization + 12-item hybrid filter)
# ==============================================================================


def archunit_fuzzy_line_normalize(line: str) -> str:
    """Exact normalization of FuzzyViolationLineMatcher (ViolationLineMatcherFactory.java:53):
    ignores line numbers matching `:\\d+\\)` and anonymous/lambda numbers matching `\\$\\d+`.
    """
    s = re.sub(r":\d+\)", ":0)", line)
    return re.sub(r"\$\d+", "$0", s)


class FreezingArchRuleSimulator:
    """Method-faithful reproduction of TNG/ArchUnit FreezingArchRule.java:120-267."""

    def __init__(self) -> None:
        self._initialized_store: list[str] | None = None

    @property
    def stored_violations(self) -> list[str]:
        return list(self._initialized_store or [])

    def evaluate(self, actual_violations: list[str], *, refreeze: bool = False) -> list[str]:
        norm_actual = [v.replace("\r\n", "\n") for v in actual_violations]
        if self._initialized_store is None or refreeze:
            self._initialized_store = list(norm_actual)
            return []

        # CategorizedViolations (FreezingArchRule.java:239-254): 1-to-1 multiset consumption.
        stored_left = list(self._initialized_store)
        known_actual: set[str] = set()
        stored_unsolved: list[str] = []
        for act in norm_actual:
            act_key = archunit_fuzzy_line_normalize(act)
            for idx, st in enumerate(stored_left):
                if act_key == archunit_fuzzy_line_normalize(st):
                    stored_left.pop(idx)
                    known_actual.add(act)
                    stored_unsolved.append(st)
                    break

        # removeObsoleteViolationsFromStore (L162-168): monotone downward ratchet.
        stored_solved = [s for s in self._initialized_store if s not in stored_unsolved]
        if stored_solved:
            self._initialized_store = list(stored_unsolved)

        # filterOutKnownViolations (L170-173): report strictly unknown/net-new violations.
        return [v for v in norm_actual if v not in known_actual]


OTEL_OWNED_NAMESPACES: dict[str, str] = {
    "gen_ai": "https://github.com/open-telemetry/semantic-conventions-genai",
    "mcp": "https://github.com/open-telemetry/semantic-conventions-genai",
    "openai": "https://github.com/open-telemetry/semantic-conventions-genai",
    "a2a": "https://github.com/open-telemetry/semantic-conventions-genai",
    "zos": "https://github.com/open-telemetry/semantic-conventions-mainframe",
    "enduser": "https://github.com/open-telemetry/semantic-conventions-client-side",
    "device": "https://github.com/open-telemetry/semantic-conventions-client-side",
}


def otel_evaluate_policies(
    attributes: list[dict[str, Any]], signals: list[dict[str, Any]]
) -> list[str]:
    """Exact reproduction of policies/namespace_ownership.rego:1-87 & reference_attributes.rego:6-44.
    In namespace_ownership.rego:69-87 (named_signals), metrics (L71) and events (L81) project
    `.name`, whereas spans (L76) and entities (L86) project `.type`.
    """
    findings: list[str] = []
    attr_keys = {a["key"] for a in attributes}

    def in_ns(name: str, ns: str) -> bool:
        return name == ns or name.startswith(ns + ".")

    for attr in attributes:
        key = attr["key"]
        if attr.get("deprecated") is None:
            for ns in OTEL_OWNED_NAMESPACES:
                if in_ns(key, ns):
                    findings.append(f"namespace_owned_by_other_registry:attr:{key}")
        if key.endswith("_ref"):
            base_key = key[:-4]
            if base_key not in attr_keys:
                findings.append(f"reference_attribute_counterpart_missing:{key}")
            if attr.get("type") != "string":
                findings.append(f"reference_attribute_type_invalid:{key}")

    for sig in signals:
        sig_type = sig["signal_type"]
        if sig_type in ("metric", "event"):
            sname = sig["name"]
        elif sig_type in ("span", "entity"):
            sname = sig["type"]
        else:
            raise ValueError(f"unsupported signal_type: {sig_type!r}")
        if sig.get("deprecated") is None:
            for ns in OTEL_OWNED_NAMESPACES:
                if in_ns(sname, ns):
                    findings.append(
                        f"namespace_owned_by_other_registry:{sig_type}:{sname}"
                    )
    return findings


FACET_NAMES = ("function", "object", "medium", "system_type", "functional_area", "setting")
FACET_WEIGHTS = (0.30, 0.25, 0.15, 0.12, 0.10, 0.08)

# Directed conceptual-distance edges w(query_term -> catalog_term):
# Specializing a general catalog asset (query="deflate" -> catalog="encode": 0.08+0.18=0.26)
# costs strictly less than generalizing an overly specific asset (query="encode" -> catalog="deflate": 0.42).
CONCEPT_EDGES: dict[str, list[tuple[str, str, float]]] = {
    "function": [
        ("compress", "deflate", 0.08),
        ("deflate", "compress", 0.08),
        ("compress", "encode", 0.18),
        ("encode", "compress", 0.34),
        ("acquire_lease", "fence_lock", 0.10),
        ("fence_lock", "acquire_lease", 0.10),
        ("validate", "lint", 0.12),
        ("lint", "validate", 0.12),
        ("parse", "deserialize", 0.10),
        ("deserialize", "parse", 0.10),
        ("deduplicate", "canonicalize", 0.15),
        ("canonicalize", "deduplicate", 0.15),
        ("evict", "garbage_collect", 0.12),
        ("garbage_collect", "evict", 0.12),
    ],
    "object": [
        ("byte_buffer", "packet_payload", 0.10),
        ("packet_payload", "byte_buffer", 0.10),
        ("ref_epoch", "monotonic_token", 0.08),
        ("monotonic_token", "ref_epoch", 0.08),
        ("openapi_spec", "endpoint_schema", 0.10),
        ("endpoint_schema", "openapi_spec", 0.10),
        ("entity_yaml", "catalog_manifest", 0.08),
        ("catalog_manifest", "entity_yaml", 0.08),
        ("ast_subtree", "syntax_node", 0.10),
        ("syntax_node", "ast_subtree", 0.10),
        ("orphan_record", "stale_entry", 0.12),
        ("stale_entry", "orphan_record", 0.12),
    ],
    "medium": [
        ("stream", "channel", 0.10),
        ("channel", "stream", 0.10),
        ("git_refs", "object_store", 0.12),
        ("object_store", "git_refs", 0.12),
        ("http_json", "rest_wire", 0.10),
        ("rest_wire", "http_json", 0.10),
        ("sqlite_table", "relational_db", 0.12),
        ("relational_db", "sqlite_table", 0.12),
        ("in_memory_dag", "graph_index", 0.10),
        ("graph_index", "in_memory_dag", 0.10),
    ],
    "system_type": [
        ("codec_lib", "transport_middleware", 0.18),
        ("transport_middleware", "codec_lib", 0.18),
        ("vcs_hook", "coordination_broker", 0.15),
        ("coordination_broker", "vcs_hook", 0.15),
        ("ci_linter", "policy_gate", 0.10),
        ("policy_gate", "ci_linter", 0.10),
        ("developer_portal", "service_registry", 0.10),
        ("service_registry", "developer_portal", 0.10),
        ("compiler_pass", "static_analyzer", 0.12),
        ("static_analyzer", "compiler_pass", 0.12),
    ],
    "functional_area": [
        ("network_io", "rpc_framing", 0.12),
        ("rpc_framing", "network_io", 0.12),
        ("concurrency", "distributed_locks", 0.10),
        ("distributed_locks", "concurrency", 0.10),
        ("api_governance", "schema_evolution", 0.10),
        ("schema_evolution", "api_governance", 0.10),
        ("catalog_ingestion", "metadata_sync", 0.10),
        ("metadata_sync", "catalog_ingestion", 0.10),
        ("code_factoring", "clone_detection", 0.12),
        ("clone_detection", "code_factoring", 0.12),
    ],
    "setting": [
        ("daemon", "cli_batch", 0.20),
        ("cli_batch", "daemon", 0.20),
        ("git_server", "ci_runner", 0.15),
        ("ci_runner", "git_server", 0.15),
        ("idp_backend", "ci_runner", 0.18),
        ("ci_runner", "idp_backend", 0.18),
    ],
}


def shortest_facet_distance(
    facet: str, src: str, dst: str, miss_penalty: float = 1.0
) -> float:
    if src == dst:
        return 0.0
    adj: dict[str, list[tuple[str, float]]] = {}
    for u, v, w in CONCEPT_EDGES.get(facet, []):
        adj.setdefault(u, []).append((v, w))
    pq: list[tuple[float, str]] = [(0.0, src)]
    best: dict[str, float] = {src: 0.0}
    while pq:
        d, u = heapq.heappop(pq)
        if u == dst:
            return min(miss_penalty, d)
        if d > best.get(u, miss_penalty):
            continue
        for v, w in adj.get(u, []):
            nd = d + w
            if nd < best.get(v, miss_penalty):
                best[v] = nd
                heapq.heappush(pq, (nd, v))
    return miss_penalty


def tokenize_bm25(text: str) -> list[str]:
    return [m.group(0) for m in re.finditer(r"[a-z0-9]+", text.lower())]


def run_probe_p4() -> dict[str, Any]:
    # --- Part 4A: ArchUnit FreezingArchRule + OTel Rego Namespace/Ref Gates ---
    freeze_rule = FreezingArchRuleSimulator()
    v1_line42 = "Method <App$1.run()> calls <LegacyDb.query()> in (App.java:42)"
    v2_line99 = "Method <Auth.login()> accesses <RawSql.exec()> in (Auth.java:99)"
    # Step 1: Initial freeze baselines 2 legacy violations -> 0 reported failures.
    r_step1 = freeze_rule.evaluate([v1_line42, v2_line99])
    assert r_step1 == [] and len(freeze_rule.stored_violations) == 2
    # Step 2: Refactor shifts App.java:42 -> :58 and lambda $1 -> $3 -> still passes.
    v1_shifted = "Method <App$3.run()> calls <LegacyDb.query()> in (App.java:58)"
    r_step2 = freeze_rule.evaluate([v1_shifted, v2_line99])
    assert r_step2 == [] and len(freeze_rule.stored_violations) == 2
    # Step 3: Adding a SECOND call inside App$3.run() at :77 fails multiset 1-to-1 consumption.
    v1_duplicate_new_line = "Method <App$3.run()> calls <LegacyDb.query()> in (App.java:77)"
    r_step3 = freeze_rule.evaluate([v1_shifted, v1_duplicate_new_line, v2_line99])
    assert r_step3 == [v1_duplicate_new_line]
    # Step 4: Engineer fixes Auth.login() violation -> store ratchets down from 2 to 1.
    r_step4 = freeze_rule.evaluate([v1_shifted])
    assert r_step4 == [] and len(freeze_rule.stored_violations) == 1
    # Step 5: Regression re-introducing Auth.login() at :105 now FAILS CI permanently.
    v2_regressed = "Method <Auth.login()> accesses <RawSql.exec()> in (Auth.java:105)"
    r_step5 = freeze_rule.evaluate([v1_shifted, v2_regressed])
    assert r_step5 == [v2_regressed]

    otel_violations = otel_evaluate_policies(
        attributes=[
            {"key": "gen_ai.Operation.name", "type": "string", "deprecated": None},
            {"key": "mcp.tool.old", "type": "string", "deprecated": {"reason": "renamed"}},
            {"key": "service.instance.id", "type": "string", "deprecated": None},
            {"key": "service.instance.id_ref", "type": "string", "deprecated": None},
            {"key": "orphan.target_ref", "type": "int", "deprecated": None},
        ],
        signals=[
            {"signal_type": "metric", "name": "a2a.task.duration", "deprecated": None},
            {"signal_type": "span", "type": "openai.chat", "deprecated": {"reason": "moved"}},
            {"signal_type": "entity", "type": "mcp.session", "deprecated": None},
        ],
    )
    assert otel_violations == [
        "namespace_owned_by_other_registry:attr:gen_ai.Operation.name",
        "reference_attribute_counterpart_missing:orphan.target_ref",
        "reference_attribute_type_invalid:orphan.target_ref",
        "namespace_owned_by_other_registry:metric:a2a.task.duration",
        "namespace_owned_by_other_registry:entity:mcp.session",
    ]

    # --- Part 4B: Prieto-Diaz 6-Facet Conceptual Graph vs. BM25 ---
    # Multi-hop & asymmetric adaptation distance check:
    # deflate -> compress (0.08) -> encode (0.18) = 0.26 < encode -> compress (0.34) -> deflate (0.08) = 0.42
    d_specialize = shortest_facet_distance("function", "deflate", "encode")
    d_generalize = shortest_facet_distance("function", "encode", "deflate")
    assert round(d_specialize, 4) == 0.26 and round(d_generalize, 4) == 0.42
    assert d_specialize < d_generalize

    catalog = [
        ("C01", ("compress", "byte_buffer", "stream", "codec_lib", "network_io", "daemon"),
         "lz4 block compressor over contiguous byte buffer stream in background daemon"),
        ("C02", ("acquire_lease", "ref_epoch", "git_refs", "vcs_hook", "concurrency", "git_server"),
         "atomic reference transaction hook verifying monotonic ref epoch inside git server"),
        ("C03", ("validate", "openapi_spec", "http_json", "ci_linter", "api_governance", "ci_runner"),
         "openapi specification validator checking deprecated operations over http json"),
        ("C04", ("parse", "entity_yaml", "sqlite_table", "developer_portal", "catalog_ingestion", "idp_backend"),
         "entity yaml ingestion processor storing component relations in sqlite table"),
        ("C05", ("deduplicate", "ast_subtree", "in_memory_dag", "compiler_pass", "code_factoring", "ci_runner"),
         "structural anti unification compiler pass deduplicating isomorphic ast subtree nodes"),
        ("C06", ("evict", "orphan_record", "sqlite_table", "developer_portal", "catalog_ingestion", "idp_backend"),
         "orphan record sweeper evicting unreferenced catalog entities from sqlite table"),
        ("D01", ("format_ui", "log_line", "stdout", "ui_widget", "telemetry_ui", "cli_batch"),
         "deflate verbose packet payload channel debug banner for terminal ui widget"),
        ("D02", ("render_chart", "metric_point", "svg_canvas", "dashboard", "analytics", "browser"),
         "fence lock monotonic token chart legend for distributed locks browser dashboard"),
        ("D03", ("mock_fixture", "test_stub", "local_file", "test_harness", "qa_mocking", "cli_batch"),
         "lint endpoint schema rest wire mock fixture generator for schema evolution tests"),
        ("D04", ("export_csv", "audit_row", "csv_file", "reporting_job", "compliance", "cli_batch"),
         "deserialize catalog manifest relational db export script for service registry csv"),
        ("D05", ("highlight_diff", "text_span", "html_dom", "code_viewer", "ui_rendering", "browser"),
         "canonicalize syntax node graph index clone detection syntax highlighter in html"),
        ("D06", ("archive_logs", "tar_archive", "object_blob", "backup_cron", "ops_storage", "daemon"),
         "garbage collect stale entry relational db metadata sync backup log rotator"),
    ]
    drift_queries = [
        ("C01", ("deflate", "packet_payload", "channel", "transport_middleware", "rpc_framing", "daemon"),
         "deflate packet payload over rpc framing channel"),
        ("C02", ("fence_lock", "monotonic_token", "object_store", "coordination_broker", "distributed_locks", "ci_runner"),
         "fence lock with monotonic token for distributed locks"),
        ("C03", ("lint", "endpoint_schema", "rest_wire", "policy_gate", "schema_evolution", "ci_runner"),
         "lint endpoint schema on rest wire for schema evolution"),
        ("C04", ("deserialize", "catalog_manifest", "relational_db", "service_registry", "metadata_sync", "idp_backend"),
         "deserialize catalog manifest into relational db for service registry"),
        ("C05", ("canonicalize", "syntax_node", "graph_index", "static_analyzer", "clone_detection", "ci_runner"),
         "canonicalize syntax node in graph index for clone detection"),
        ("C06", ("garbage_collect", "stale_entry", "relational_db", "service_registry", "metadata_sync", "idp_backend"),
         "garbage collect stale entry in relational db during metadata sync"),
    ]
    exact_queries = [(cid, facets, desc) for cid, facets, desc in catalog[:6]]

    docs_tokens = [tokenize_bm25(desc) for _, _, desc in catalog]
    n_docs = len(docs_tokens)
    avgdl = sum(len(t) for t in docs_tokens) / n_docs
    df: Counter[str] = Counter()
    for toks in docs_tokens:
        for term in set(toks):
            df[term] += 1

    def rank_bm25(q_text: str) -> list[str]:
        q_toks = tokenize_bm25(q_text)
        scores: list[tuple[float, str]] = []
        for idx, (cid, _, _) in enumerate(catalog):
            tf = Counter(docs_tokens[idx])
            dl = len(docs_tokens[idx])
            s = 0.0
            for qt in q_toks:
                n_q = df.get(qt, 0)
                idf = math.log(1.0 + (n_docs - n_q + 0.5) / (n_q + 0.5))
                f = tf.get(qt, 0)
                s += idf * (f * 2.5) / (f + 1.5 * (1.0 - 0.75 + 0.75 * dl / avgdl))
            scores.append((-s, cid))
        scores.sort()
        return [cid for _, cid in scores]

    def rank_faceted(q_facets: tuple[str, ...]) -> list[str]:
        scored: list[tuple[float, str]] = []
        for cid, c_facets, _ in catalog:
            dist = sum(
                w * shortest_facet_distance(fname, qf, cf)
                for fname, w, qf, cf in zip(FACET_NAMES, FACET_WEIGHTS, q_facets, c_facets)
            )
            scored.append((dist, cid))
        scored.sort()
        return [cid for _, cid in scored]

    def eval_queries(q_list: list[tuple[str, tuple[str, ...], str]]) -> dict[str, float]:
        bm25_r1 = bm25_mrr = fac_r1 = fac_mrr = 0.0
        for target_id, q_fac, q_txt in q_list:
            rb = rank_bm25(q_txt)
            rf = rank_faceted(q_fac)
            ib = rb.index(target_id) + 1
            if_ = rf.index(target_id) + 1
            bm25_r1 += 1.0 if ib == 1 else 0.0
            bm25_mrr += 1.0 / ib
            fac_r1 += 1.0 if if_ == 1 else 0.0
            fac_mrr += 1.0 / if_
        m = len(q_list)
        return {
            "bm25_recall_at_1": round(bm25_r1 / m, 4),
            "bm25_mrr": round(bm25_mrr / m, 4),
            "faceted_recall_at_1": round(fac_r1 / m, 4),
            "faceted_mrr": round(fac_mrr / m, 4),
        }

    exact_ctrl = eval_queries(exact_queries)
    drift_eval = eval_queries(drift_queries)
    assert exact_ctrl["bm25_recall_at_1"] == 1.0 and exact_ctrl["faceted_recall_at_1"] == 1.0
    assert drift_eval["faceted_recall_at_1"] == 1.0 and drift_eval["bm25_recall_at_1"] == 0.0

    # Synthetic 12-entity mechanism reproducer for OOV action/object cold-start:
    # Each 5-token query combines 3 OOV tokens (planted onto cross-`setting` distractors D02..D05)
    # with 2 in-vocabulary target tokens; coarse `setting`-facet filtering (leaving >=2 candidates
    # per bucket) eliminates cross-environment lexical false friends so intra-bucket BM25 resolves.
    oov_cold_queries = [
        ("C04", ("ingest_manifest", "yaml_blob", "sqlite_table", "developer_portal", "catalog_ingestion", "idp_backend"),
         "ingest manifest yaml blob component relations"),
        ("C06", ("reap_dangling", "dead_node", "sqlite_table", "developer_portal", "catalog_ingestion", "idp_backend"),
         "reap dangling dead node unreferenced entities"),
        ("C03", ("audit_contract", "oas_tree", "http_json", "ci_linter", "api_governance", "ci_runner"),
         "audit contract oas tree deprecated operations"),
        ("C05", ("fold_clones", "ir_block", "in_memory_dag", "compiler_pass", "code_factoring", "ci_runner"),
         "fold clones ir block isomorphic nodes"),
    ]
    cold_trap_by_id = {
        "D02": " ingest manifest yaml blob",
        "D03": " reap dangling dead node",
        "D04": " audit contract oas tree",
        "D05": " fold clones ir block",
    }
    cold_docs = [
        tokenize_bm25(desc + cold_trap_by_id.get(cid, ""))
        for cid, _, desc in catalog
    ]
    cold_avgdl = sum(len(t) for t in cold_docs) / len(cold_docs)
    cold_df: Counter[str] = Counter()
    for toks in cold_docs:
        for term in set(toks):
            cold_df[term] += 1

    def rank_cold_bm25(q_text: str, allowed_ids: set[str] | None = None) -> list[str]:
        q_toks = tokenize_bm25(q_text)
        scored: list[tuple[float, str]] = []
        for idx, (cid, _, _) in enumerate(catalog):
            if allowed_ids is not None and cid not in allowed_ids:
                continue
            tf = Counter(cold_docs[idx])
            dl = len(cold_docs[idx])
            s = 0.0
            for qt in q_toks:
                nq = cold_df.get(qt, 0)
                idf = math.log(1.0 + (len(cold_docs) - nq + 0.5) / (nq + 0.5))
                f = tf.get(qt, 0)
                s += idf * (f * 2.5) / (f + 1.5 * (1.0 - 0.75 + 0.75 * dl / cold_avgdl))
            scored.append((-s, cid))
        scored.sort()
        return [cid for _, cid in scored]

    cold_bm25_hits = 0
    cold_hybrid_hits = 0
    for target_id, q_fac, q_txt in oov_cold_queries:
        if rank_cold_bm25(q_txt)[0] == target_id:
            cold_bm25_hits += 1
        allowed = {cid for cid, c_fac, _ in catalog if c_fac[5] == q_fac[5]}
        assert len(allowed) >= 2
        if rank_cold_bm25(q_txt, allowed)[0] == target_id:
            cold_hybrid_hits += 1
    assert cold_bm25_hits == 0 and cold_hybrid_hits == len(oov_cold_queries)

    return {
        "part_4a_evidence_class": EVIDENCE_EXACT_REPO_OR_DATASET,
        "archunit_freezing_ratchet": {
            "initial_frozen_count": 2,
            "line_and_lambda_shift_new_violations": len(r_step2),
            "same_method_second_call_caught": r_step3,
            "post_fix_ratcheted_store_count": 1,
            "regression_reintroduction_caught": r_step5,
        },
        "otel_rego_federation_and_refs": {
            "violations_detected": otel_violations,
            "deprecated_tombstones_permitted": 2,
        },
        "part_4b_evidence_class": EVIDENCE_CONTROLLED_SIM,
        "two_hop_asymmetric_distance": {
            "specialize_deflate_from_encode": round(d_specialize, 4),
            "generalize_encode_from_deflate": round(d_generalize, 4),
        },
        "exact_lexical_negative_control": exact_ctrl,
        "synonym_vocabulary_drift_with_distractors": drift_eval,
        "oov_cold_start_hybrid_ablation": {
            "synthetic_catalog_entities": len(catalog),
            "oov_tokens_per_query": 3,
            "invocab_target_tokens_per_query": 2,
            "pure_bm25_recall_at_1": round(cold_bm25_hits / len(oov_cold_queries), 4),
            "hybrid_env_facet_plus_bm25_recall_at_1": round(
                cold_hybrid_hits / len(oov_cold_queries), 4
            ),
        },
    }


# ==============================================================================
# PROBE P5:
# Part 5A [exact reproduction of archival dataset / pinned repo logic]:
#   - backstage/backstage @ feeadd4d4efcbda9f1573b95e356e0f3fc0b5d17
#     (20210302150147_refresh_state.js:127-150 + DefaultProcessingDatabase.ts:127-134
#      + performStitching.ts:41-50, 103-112, 149-186, 195-215
#      + deleteOrphanedEntities.ts:36-133 + evictEntitiesFromOrphanedProviders.ts:21-91)
#   - modelcontextprotocol/registry @ 9432a0a9aa9e7092cf93f08226426487f8416423
#     (validators.go:19-59, 80-92, 366-424, 761-783, 821-861)
# Part 5B [controlled simulation]:
#   - Two-State Coupled Staleness Belief Cutoff (pure quarantine vs. CI re-harvesting)
#   - Eppler & Mengis (2004) Broadcast Overload vs. Ye & Fischer (2005) Top-k Push
# ==============================================================================

# Exact upstream regex from backstage/backstage performStitching.ts:48-50:
# Matches control/whitespace-obfuscated `javascript:` URLs ONLY; `data:` and `vbscript:` pass through.
SCRIPT_PROTOCOL_RE = re.compile(
    r"^[\u0000-\u001F ]*j[\r\n\t]*a[\r\n\t]*v[\r\n\t]*a[\r\n\t]*s[\r\n\t]*c[\r\n\t]*r[\r\n\t]*i[\r\n\t]*p[\r\n\t]*t[\r\n\t]*:",
    re.IGNORECASE,
)


class BackstageCatalogStitcherSimulator:
    """State-machine reproduction of Backstage refresh_state, refresh_state_references,
    relations (with originating_entity_id ON DELETE CASCADE and NO FK on target_entity_ref),
    performStitching.ts, deleteOrphanedEntities.ts, and evictEntitiesFromOrphanedProviders.ts.
    """

    def __init__(self) -> None:
        self.refresh_state: dict[str, dict[str, Any]] = {}
        # (source_key_or_entity_ref, target_entity_ref)
        self.refresh_state_references: set[tuple[str, str]] = set()
        # (originating_entity_ref, source_entity_ref, relation_type, target_entity_ref)
        # Matches 20210302150147_refresh_state.js:127-150 & DefaultProcessingDatabase.ts:127-134.
        self.relations: set[tuple[str, str, str, str]] = set()
        self.final_entities: dict[str, dict[str, Any]] = {}
        self.stitch_queue: set[str] = set()

    def ingest_provider_full(
        self, provider_key: str, entities: list[dict[str, Any]]
    ) -> None:
        old_targets = {
            tgt
            for src, tgt in self.refresh_state_references
            if src == f"provider:{provider_key}"
        }
        self.refresh_state_references = {
            (src, tgt)
            for src, tgt in self.refresh_state_references
            if src != f"provider:{provider_key}"
        }
        new_targets: set[str] = set()
        for ent in entities:
            eref = ent["entity_ref"]
            new_targets.add(eref)
            self.refresh_state[eref] = {
                "processed_entity": json.loads(json.dumps(ent["entity"])),
                "previous_hash": self.final_entities.get(eref, {}).get("hash"),
            }
            self.refresh_state_references.add((f"provider:{provider_key}", eref))
            # DefaultProcessingDatabase.ts:127-134 replaces rows where originating_entity_id == id:
            self.relations = {r for r in self.relations if r[0] != eref}
            for rel_type, target_ref in ent.get("outgoing_relations", []):
                self.relations.add((eref, eref, rel_type, target_ref))
            for src_ref, rel_type, target_ref in ent.get("emitted_relations", []):
                self.relations.add((eref, src_ref, rel_type, target_ref))
                if src_ref in self.refresh_state:
                    self.stitch_queue.add(src_ref)
            self.stitch_queue.add(eref)
        # Dropped targets lose their incoming provider reference and must be re-stitched.
        for dropped in old_targets - new_targets:
            if dropped in self.refresh_state:
                self.stitch_queue.add(dropped)

    def perform_stitching(self, entity_ref: str) -> str:
        if entity_ref not in self.refresh_state:
            self.final_entities.pop(entity_ref, None)
            return "deleted"
        row = self.refresh_state[entity_ref]
        entity = json.loads(json.dumps(row["processed_entity"]))
        incoming_count = sum(
            1 for _, tgt in self.refresh_state_references if tgt == entity_ref
        )
        # performStitching.ts:149-158
        annotations = dict(entity.get("metadata", {}).get("annotations", {}))
        if incoming_count == 0:
            annotations["backstage.io/orphan"] = "true"
        # performStitching.ts:171-177 (sanitizes obfuscated javascript: only)
        for url_ann in ("backstage.io/view-url", "backstage.io/edit-url"):
            val = annotations.get(url_ann)
            if isinstance(val, str) and SCRIPT_PROTOCOL_RE.match(val):
                annotations[url_ann] = (
                    "https://backstage.io/annotation-rejected-for-security-reasons"
                )
        entity.setdefault("metadata", {})["annotations"] = annotations
        # performStitching.ts:103-112 & 181-186:
        # SELECT DISTINCT type, target_entity_ref FROM relations WHERE source_entity_ref = entityRef
        # (NO check that target_entity_ref exists in refresh_state!)
        distinct_rels = sorted(
            {
                (rtype, tgt)
                for _orig, src, rtype, tgt in self.relations
                if src == entity_ref
            }
        )
        entity["relations"] = [
            {"type": rtype, "targetRef": tgt} for rtype, tgt in distinct_rels
        ]
        # performStitching.ts:41-45, 195-207
        canonical = json.dumps(entity, sort_keys=True, separators=(",", ":"))
        digest = hashlib.sha1(canonical.encode("utf-8")).hexdigest()
        if digest == row.get("previous_hash"):
            return "unchanged"
        entity["metadata"]["etag"] = digest
        row["previous_hash"] = digest
        self.final_entities[entity_ref] = {"hash": digest, "entity": entity}
        return "changed"

    def delete_orphaned_entities(
        self, *, concurrent_rescue_ref: tuple[str, str] | None = None
    ) -> dict[str, Any]:
        # deleteOrphanedEntities.ts:36-71 candidate scan
        referenced = {tgt for _, tgt in self.refresh_state_references}
        orphan_candidates = sorted(
            eref for eref in self.refresh_state if eref not in referenced
        )
        # Simulate concurrent reference insertion arriving before FOR UPDATE + WHERE NOT EXISTS (L83-102)
        if concurrent_rescue_ref is not None:
            self.refresh_state_references.add(concurrent_rescue_ref)

        referenced_after_lock = {tgt for _, tgt in self.refresh_state_references}
        deleted_refs = [
            eref for eref in orphan_candidates if eref not in referenced_after_lock
        ]
        deleted_set = set(deleted_refs)
        # Find surviving relation_source neighbors pointing to deleted orphans (L62-71, 119-130)
        neighbor_sources = sorted(
            {
                src
                for _orig, src, _rtype, tgt in self.relations
                if tgt in deleted_set
                and src in self.refresh_state
                and src not in deleted_set
            }
        )
        for eref in deleted_refs:
            self.refresh_state.pop(eref, None)
            self.final_entities.pop(eref, None)
        # ON DELETE CASCADE on relations.originating_entity_id (20210302150147_refresh_state.js:130-133):
        self.relations = {r for r in self.relations if r[0] not in deleted_set}
        for nref in neighbor_sources:
            self.stitch_queue.add(nref)
        return {
            "candidates": orphan_candidates,
            "deleted": deleted_refs,
            "neighbors_marked_for_stitching": neighbor_sources,
        }

    def find_dangling_relations(self, entity_ref: str) -> list[dict[str, str]]:
        """Explicit broken-reference audit layer needed above Backstage stitching to detect
        self-originated relations whose target_entity_ref is absent from final_entities.
        """
        rels = self.final_entities.get(entity_ref, {}).get("entity", {}).get("relations", [])
        return [r for r in rels if r["targetRef"] not in self.final_entities]

    def evict_entities_from_orphaned_providers(
        self, installed_providers: set[str]
    ) -> list[str]:
        """Exact reproduction of evictEntitiesFromOrphanedProviders.ts:21-91."""
        db_providers = sorted(
            {
                src.split("provider:", 1)[1]
                for src, _ in self.refresh_state_references
                if src.startswith("provider:")
            }
        )
        orphaned_providers = [p for p in db_providers if p not in installed_providers]
        for prov in orphaned_providers:
            self.ingest_provider_full(prov, [])
        return orphaned_providers


# Exact regexes from modelcontextprotocol/registry internal/validators/validators.go:25-59:
MCP_NAMESPACE_RE = re.compile(r"^[a-zA-Z0-9][a-zA-Z0-9.-]*[a-zA-Z0-9]$")
MCP_NAME_RE = re.compile(r"^[a-zA-Z0-9][a-zA-Z0-9._-]*[a-zA-Z0-9]$")
MCP_COMPARATOR_RANGE_RE = re.compile(
    r"^\s*(?:\^|~|>=|<=|>|<|=)\s*v?\d+(?:\.\d+){0,3}(?:-[0-9A-Za-z.-]+)?\s*$"
)
MCP_HYPHEN_RANGE_RE = re.compile(
    r"^\s*v?\d+(?:\.\d+){0,3}(?:-[0-9A-Za-z.-]+)?\s-\s*v?\d+(?:\.\d+){0,3}(?:-[0-9A-Za-z.-]+)?\s*$"
)
MCP_OR_RANGE_RE = re.compile(
    r"^\s*(?:v?\d+(?:\.\d+){0,3}(?:-[0-9A-Za-z.-]+)?\s*)(?:\|\|\s*v?\d+(?:\.\d+){0,3}(?:-[0-9A-Za-z.-]+)?\s*)+$"
)
MCP_DOTTED_VERSION_LIKE_RE = re.compile(
    r"^\s*(?:v?\d+|x|X|\*)(?:\.(?:\d+|x|X|\*)){1,2}(?:-[0-9A-Za-z.-]+)?\s*$"
)


def mcp_looks_like_version_range(version: str) -> bool:
    """Exact reproduction of looksLikeVersionRange (validators.go:404-424)."""
    s = version.strip()
    if not s:
        return False
    if (
        MCP_COMPARATOR_RANGE_RE.match(s)
        or MCP_HYPHEN_RANGE_RE.match(s)
        or MCP_OR_RANGE_RE.match(s)
    ):
        return True
    if MCP_DOTTED_VERSION_LIKE_RE.match(s) and (
        "*" in s or "x" in s or "X" in s
    ):
        return True
    return False


def mcp_validate_manifest(name: str, version: str) -> list[str]:
    """Exact reproduction of parseServerName (validators.go:821-861) and
    validateVersion (validators.go:366-424).
    """
    issues: list[str] = []
    slash_count = name.count("/")
    if slash_count == 0:
        issues.append("invalid-server-name")
    elif slash_count > 1:
        issues.append("multiple-slashes-in-server-name")
    else:
        ns, srv_name = name.split("/", 1)
        if not ns or not srv_name or not (
            MCP_NAMESPACE_RE.match(ns) and MCP_NAME_RE.match(srv_name)
        ):
            issues.append("invalid-server-name")

    # validators.go:369 checks untrimmed case-sensitive `version == "latest"`:
    if version == "latest":
        issues.append("reserved-version-string")
    elif mcp_looks_like_version_range(version):
        issues.append("version-looks-like-range")
    return issues


def simulate_coupled_trust_dynamics(
    *,
    mu_code_churn: float,
    rho_base_refresh: float,
    rho_feedback_per_query: float,
    c_lookup: float,
    v_fresh_gain: float,
    c_stale_penalty: float,
    ci_stale_eviction_rate: float,
    ci_auto_reharvest: bool = False,
    steps: int = 80,
) -> dict[str, Any]:
    """Coupled two-cohort (fresh_live, stale_live) dynamical system:
    - Rational consumer queries iff trust belief b > f_min = (c_lookup + c_stale) / (v_fresh + c_stale).
    - Code churn mu degrades fresh_live -> stale_live each step; refresh repairs stale -> fresh.
    - Pure quarantine (`ci_auto_reharvest=False`) evicts `ci_stale_eviction_rate` of `stale_after_churn`
      without replenishment, preserving conditional freshness `served_f` while shrinking active catalog mass.
    - Coupled quarantine + automated CI re-harvesting (`ci_auto_reharvest=True`) re-extracts quarantined
      items from source at merge time, preserving both active catalog mass (1.0) and steady-state freshness.
    """
    f_min = (c_lookup + c_stale_penalty) / (v_fresh_gain + c_stale_penalty)
    fresh_live = 0.92
    stale_live = 0.08
    b = 0.90
    queries_made = 0
    collapse_step: int | None = None

    for step in range(1, steps + 1):
        queries = 1.0 if b > f_min else 0.0
        if queries == 0.0 and collapse_step is None:
            collapse_step = step
        queries_made += int(queries)

        rho_eff = rho_base_refresh + rho_feedback_per_query * queries
        newly_stale = fresh_live * mu_code_churn
        repaired = stale_live * rho_eff
        fresh_live = fresh_live - newly_stale + repaired
        stale_after_churn = stale_live + newly_stale - repaired

        stale_served = stale_after_churn * (1.0 - ci_stale_eviction_rate)
        if ci_auto_reharvest:
            fresh_live += stale_after_churn * ci_stale_eviction_rate
        stale_live = stale_served

        active_mass = fresh_live + stale_live
        served_f = fresh_live / active_mass if active_mass > 0.0 else 0.0
        if queries > 0.0:
            b = 0.80 * b + 0.20 * served_f

    return {
        "f_min_threshold": round(f_min, 4),
        "final_active_catalog_mass": round(fresh_live + stale_live, 6),
        "final_served_freshness": round(served_f, 4),
        "final_trust_belief": round(b, 4),
        "active_query_steps_out_of_80": queries_made,
        "trust_collapse_step": collapse_step,
    }


def broadcast_vs_faceted_accuracy(
    n_agents: int, msgs_per_agent: int = 3, tokens_per_msg: int = 350
) -> dict[str, Any]:
    load_bcast = (n_agents - 1) * msgs_per_agent * tokens_per_msg
    load_faceted = min((n_agents - 1) * msgs_per_agent, 4) * 120

    def inverted_u_acc(tokens: int, opt_tokens: int = 600) -> float:
        signal_gain = 1.0 - math.exp(-tokens / 240.0)
        overload_penalty = math.exp(-max(0, tokens - opt_tokens) / 6500.0)
        return round(0.35 + 0.60 * signal_gain * overload_penalty, 4)

    return {
        "n_agents": n_agents,
        "broadcast_tokens": load_bcast,
        "faceted_tokens": load_faceted,
        "broadcast_accuracy": inverted_u_acc(load_bcast),
        "faceted_accuracy": inverted_u_acc(load_faceted),
    }


def run_probe_p5() -> dict[str, Any]:
    # --- Part 5A: Backstage Stitcher / Orphan-GC + MCP Registry Validator ---
    cat = BackstageCatalogStitcherSimulator()
    cat.ingest_provider_full(
        "git-main",
        [
            {
                "entity_ref": "component:default/worker-svc",
                "entity": {
                    "kind": "Component",
                    "metadata": {
                        "name": "worker-svc",
                        "annotations": {
                            "backstage.io/view-url": " \tJaVa\nScRiPt:alert(1)",
                            "backstage.io/edit-url": "data:text/html,unblocked",
                        },
                    },
                },
                "outgoing_relations": [
                    ("dependsOn", "airesource:default/code-search-skill"),
                    ("dependsOn", "airesource:default/legacy-skill"),
                ],
            },
            {
                "entity_ref": "airesource:default/code-search-skill",
                "entity": {
                    "kind": "AiResource",
                    "metadata": {
                        "name": "code-search-skill",
                        "annotations": {"backstage.io/view-url": "vbscript:msgbox(1)"},
                    },
                },
                "outgoing_relations": [],
            },
            {
                "entity_ref": "airesource:default/legacy-skill",
                "entity": {"kind": "AiResource", "metadata": {"name": "legacy-skill"}},
                "outgoing_relations": [("partOf", "component:default/worker-svc")],
                # BuiltinKindsEntityProcessor emits symmetric inverse relation with
                # originating_entity_id = id(legacy-skill) onto worker-svc:
                "emitted_relations": [
                    (
                        "component:default/worker-svc",
                        "hasPart",
                        "airesource:default/legacy-skill",
                    )
                ],
            },
        ],
    )
    for ref in sorted(cat.stitch_queue):
        assert cat.perform_stitching(ref) == "changed"
    cat.stitch_queue.clear()
    # Second stitch without changes short-circuits via SHA-1 hash:
    assert cat.perform_stitching("component:default/worker-svc") == "unchanged"

    # Verify exact upstream scriptProtocolPattern boundary (performStitching.ts:48-50):
    # obfuscated `javascript:` is rejected, whereas `data:` and `vbscript:` pass through untouched.
    svc_ann = cat.final_entities["component:default/worker-svc"]["entity"]["metadata"][
        "annotations"
    ]
    skill_ann = cat.final_entities["airesource:default/code-search-skill"]["entity"][
        "metadata"
    ]["annotations"]
    assert (
        svc_ann["backstage.io/view-url"]
        == "https://backstage.io/annotation-rejected-for-security-reasons"
    )
    assert svc_ann["backstage.io/edit-url"] == "data:text/html,unblocked"
    assert skill_ann["backstage.io/view-url"] == "vbscript:msgbox(1)"
    assert len(cat.final_entities["component:default/worker-svc"]["entity"]["relations"]) == 3

    # Provider refresh drops both skills from git-main, leaving them with 0 incoming refs (orphans):
    cat.ingest_provider_full(
        "git-main",
        [
            {
                "entity_ref": "component:default/worker-svc",
                "entity": {"kind": "Component", "metadata": {"name": "worker-svc"}},
                "outgoing_relations": [
                    ("dependsOn", "airesource:default/code-search-skill"),
                    ("dependsOn", "airesource:default/legacy-skill"),
                ],
            }
        ],
    )
    for ref in sorted(cat.stitch_queue):
        cat.perform_stitching(ref)
    cat.stitch_queue.clear()
    assert (
        cat.final_entities["airesource:default/legacy-skill"]["entity"]["metadata"][
            "annotations"
        ]["backstage.io/orphan"]
        == "true"
    )

    # Run deleteOrphanedEntities while a concurrent provider rescues code-search-skill mid-flight:
    gc_res = cat.delete_orphaned_entities(
        concurrent_rescue_ref=(
            "provider:git-skills",
            "airesource:default/code-search-skill",
        )
    )
    assert gc_res["candidates"] == [
        "airesource:default/code-search-skill",
        "airesource:default/legacy-skill",
    ]
    assert gc_res["deleted"] == ["airesource:default/legacy-skill"]
    assert gc_res["neighbors_marked_for_stitching"] == ["component:default/worker-svc"]

    # Re-stitching worker-svc removes ONLY the orphan-originated `hasPart` relation
    # (via originating_entity_id ON DELETE CASCADE), while worker-svc's self-originated
    # dangling `dependsOn -> airesource:default/legacy-skill` remains until broken-ref validation!
    assert cat.perform_stitching("component:default/worker-svc") == "changed"
    surviving_rels = cat.final_entities["component:default/worker-svc"]["entity"][
        "relations"
    ]
    assert surviving_rels == [
        {"targetRef": "airesource:default/code-search-skill", "type": "dependsOn"},
        {"targetRef": "airesource:default/legacy-skill", "type": "dependsOn"},
    ]
    dangling_rels = cat.find_dangling_relations("component:default/worker-svc")
    assert dangling_rels == [
        {"targetRef": "airesource:default/legacy-skill", "type": "dependsOn"}
    ]

    # Uninstalling provider 'git-skills' triggers evictEntitiesFromOrphanedProviders (L21-91):
    evicted_provs = cat.evict_entities_from_orphaned_providers({"git-main"})
    assert evicted_provs == ["git-skills"]
    gc_after_prov_evict = cat.delete_orphaned_entities()
    assert gc_after_prov_evict["deleted"] == ["airesource:default/code-search-skill"]

    # MCP Registry validators.go:25-59, 366-424, 821-861 checks:
    assert mcp_validate_manifest("io.modelcontextprotocol/filesystem", "1.2.3") == []
    assert mcp_validate_manifest("unscoped_server", "1.2.3") == ["invalid-server-name"]
    assert mcp_validate_manifest("io.mcp/extra/slash", "1.2.3") == [
        "multiple-slashes-in-server-name"
    ]
    assert mcp_validate_manifest("io.mcp/fs", "latest") == ["reserved-version-string"]
    assert mcp_validate_manifest("io.mcp/fs", "LATEST") == []
    assert mcp_validate_manifest("io.mcp/fs", "") == []
    assert mcp_validate_manifest("io.mcp/fs", "^1.2.0") == ["version-looks-like-range"]
    assert mcp_validate_manifest("io.mcp/fs", "1.2.0 || 1.3.0") == [
        "version-looks-like-range"
    ]
    assert mcp_validate_manifest("io.mcp/fs", "1.x") == ["version-looks-like-range"]

    # --- Part 5B: Coupled Staleness Trust Dynamics & Broadcast Overload ---
    low_level_manual = simulate_coupled_trust_dynamics(
        mu_code_churn=0.12,
        rho_base_refresh=0.03,
        rho_feedback_per_query=0.05,
        c_lookup=2.0,
        v_fresh_gain=22.0,
        c_stale_penalty=18.0,
        ci_stale_eviction_rate=0.0,
        ci_auto_reharvest=False,
    )
    high_level_arch = simulate_coupled_trust_dynamics(
        mu_code_churn=0.06,
        rho_base_refresh=0.03,
        rho_feedback_per_query=0.05,
        c_lookup=2.0,
        v_fresh_gain=22.0,
        c_stale_penalty=3.0,
        ci_stale_eviction_rate=0.0,
        ci_auto_reharvest=False,
    )
    low_level_pure_quarantine = simulate_coupled_trust_dynamics(
        mu_code_churn=0.12,
        rho_base_refresh=0.03,
        rho_feedback_per_query=0.05,
        c_lookup=2.0,
        v_fresh_gain=22.0,
        c_stale_penalty=18.0,
        ci_stale_eviction_rate=0.85,
        ci_auto_reharvest=False,
    )
    low_level_coupled_quarantine_reharvest = simulate_coupled_trust_dynamics(
        mu_code_churn=0.12,
        rho_base_refresh=0.03,
        rho_feedback_per_query=0.05,
        c_lookup=2.0,
        v_fresh_gain=22.0,
        c_stale_penalty=18.0,
        ci_stale_eviction_rate=0.85,
        ci_auto_reharvest=True,
    )
    assert low_level_manual["trust_collapse_step"] == 15
    assert high_level_arch["trust_collapse_step"] is None
    # Pure quarantine without re-harvesting preserves conditional precision (0.9764 > 0.50),
    # preventing belief collapse, while depleting active catalog mass to 0.000041 (0.0041%):
    assert low_level_pure_quarantine["trust_collapse_step"] is None
    assert low_level_pure_quarantine["final_served_freshness"] == 0.9764
    assert low_level_pure_quarantine["final_active_catalog_mass"] == 0.000041
    # Coupled quarantine + automated CI re-harvesting preserves full catalog mass (1.0)
    # and converges to exact stationary freshness F* = 1 - (0.15*0.12)/(1 - 0.15*0.80) = 431/440 = 0.9795:
    assert low_level_coupled_quarantine_reharvest["trust_collapse_step"] is None
    assert low_level_coupled_quarantine_reharvest["final_active_catalog_mass"] == 1.0
    assert (
        low_level_coupled_quarantine_reharvest["final_served_freshness"]
        == round(431 / 440, 4)
        == 0.9795
    )

    overload_curve = [broadcast_vs_faceted_accuracy(n) for n in (1, 2, 4, 8, 16, 32)]
    assert overload_curve[0]["broadcast_accuracy"] < overload_curve[1]["broadcast_accuracy"]
    for i in range(1, len(overload_curve) - 1):
        assert overload_curve[i]["broadcast_accuracy"] > overload_curve[i + 1]["broadcast_accuracy"]
    assert overload_curve[-1]["faceted_accuracy"] > overload_curve[-1]["broadcast_accuracy"]

    return {
        "part_5a_evidence_class": EVIDENCE_EXACT_REPO_OR_DATASET,
        "backstage_stitcher_and_orphan_gc": {
            "javascript_url_sanitized": True,
            "data_and_vbscript_urls_unblocked": True,
            "hash_unchanged_short_circuit": True,
            "orphan_candidates": gc_res["candidates"],
            "concurrent_rescued_entity": "airesource:default/code-search-skill",
            "deleted_orphans": gc_res["deleted"],
            "restitched_neighbors": gc_res["neighbors_marked_for_stitching"],
            "orphan_originated_inverse_relation_cascade_deleted": True,
            "surviving_worker_relations_count": len(surviving_rels),
            "self_originated_dangling_relations_retained": dangling_rels,
        },
        "mcp_registry_validator_checks": {
            "concrete_semver_accepted": True,
            "unscoped_name_rejected": True,
            "multiple_slashes_rejected": True,
            "lowercase_latest_reserved_rejected": True,
            "uppercase_latest_and_empty_not_flagged_by_validate_version": True,
            "comparator_or_and_wildcard_ranges_rejected": True,
        },
        "part_5b_evidence_class": EVIDENCE_CONTROLLED_SIM,
        "low_level_manual_registry_collapse": low_level_manual,
        "high_level_arch_map_resilience": high_level_arch,
        "low_level_pure_quarantine_mass_depletion": low_level_pure_quarantine,
        "low_level_coupled_quarantine_and_ci_reharvest": low_level_coupled_quarantine_reharvest,
        "broadcast_vs_faceted_scaling": overload_curve,
    }


def main() -> None:
    p1 = run_probe_p1()
    p2 = run_probe_p2()
    p3 = run_probe_p3()
    p4 = run_probe_p4()
    p5 = run_probe_p5()

    banners = [
        f"BANNER P1: {EVIDENCE_EXACT_REPO_OR_DATASET} — Morisio et al. (2002) & Menzies (2003) reuse.arff",
        f"BANNER P2: {EVIDENCE_PARAMETRIC_ANALYTICAL} — Author-parameterized reuse-cost & 7-gate cascade model",
        f"BANNER P3: {EVIDENCE_PARAMETRIC_ANALYTICAL} — Author-parameterized discretionary-DB & syntactic-quota game",
        f"BANNER P4A: {EVIDENCE_EXACT_REPO_OR_DATASET} — ArchUnit FreezingArchRule & OTel Rego Namespace Federation",
        f"BANNER P4B: {EVIDENCE_CONTROLLED_SIM} — Prieto-Diaz (1987, 1991) 6-Facet Conceptual Graph vs. BM25",
        f"BANNER P5A: {EVIDENCE_EXACT_REPO_OR_DATASET} — Backstage Stitcher/Orphan-GC & MCP Registry Validator",
        f"BANNER P5B: {EVIDENCE_CONTROLLED_SIM} — Coupled Staleness Quarantine/Re-Harvest & Broadcast Overload",
    ]
    for b in banners:
        print(b)

    report = {
        "P1_morisio_2002_reuse_arff": p1,
        "P2_parametric_reuse_cost_and_cascade": p2,
        "P3_discretionary_db_public_goods_game": p3,
        "P4_archunit_otel_and_prieto_diaz_facets": p4,
        "P5_backstage_mcp_staleness_and_overload": p5,
    }
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
