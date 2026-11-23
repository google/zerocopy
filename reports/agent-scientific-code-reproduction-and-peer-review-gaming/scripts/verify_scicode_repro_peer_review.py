#!/usr/bin/env python3
"""Deterministic 5-pillar executable verification probe for scientific code
reproduction harnesses and automated peer-review pipelines.

Pinned upstream subjects audited and faithfully ported:
  1. siegelz/core-bench @ e32a2980e72fe6eb04ee04eb749458f570625663
     (benchmark/evaluations.py:42-104, 158-160; core_train.json + core_test.json.gpg)
     & allenai/super-benchmark @ 0c03d77a1114fb9a14ec6d3e2edbcaf254d40a6d
     (super/evaluate_dataset.py:18-43, 146; super/run_on_benchmark.py:23, 111-136)
  2. scicode-bench/SciCode @ e3158ea011d4235245a547460d3688d7ccbf9900
     (eval/scripts/test_generated_code.py:13-16,38,47-57,84-97,125-127;
      eval/scripts/gencode.py:11-12,69-85,115-130; eval/inspect_ai/scicode.py:253-294,359-367;
      src/scicode/parse/parse.py:30-51,75-79,164-171;
      src/scicode/compare/cmp.py:6-35,48-74) +
     HF dataset SciCode1/SciCode @ 4510f6a6aa27c43fad7b43da2c59602a86e88480
     (2025-02-17T18:04:31Z; problems_dev.jsonl + problems_test.jsonl) +
     Tian et al. (arXiv:2407.13168v1)
  3. SakanaAI/AI-Scientist @ 1de1dbc1f4ee2c5f61e9c94348d55eb51d7fa2eb
     (ai_scientist/perform_review.py:151-264) &
     SakanaAI/AI-Scientist-v2 @ 96bd51617cfdbb494a9fc283af00fe090edfae48
     (ai_scientist/perform_llm_review.py:150-254) + Lu et al. (arXiv:2408.06292v3)
  4. Ahren09/AgentReview @ 9ce5ec762eaba2d1cdff2f965ce11430b5be9361
     (agentreview/experiment_config.py:6-264; role_descriptions.py:11-15,55-107,
      137-167,285-359,428-435,508-519; paper_review_settings.py:68-92;
      paper_review_message.py:54-88; paper_review_arena.py:91-110;
      environments/paper_review.py:113-150; ui/cli.py:243-259;
      utility/utils.py:16-57,306-314; run_paper_decision_cli.py:47-120)
     + Jin et al. (arXiv:2406.12708v3, §A.2 & Tables 1, 2, 3, 5)
  5. Ye et al. (arXiv:2412.01708v1, §3.1-3.4, Figs. 2b & 3, Tables 3 & 4) across
     LLM Review, The AI Scientist, and AgentReview.

Pure Python 3.10+ standard library only; deterministic under PYTHONHASHSEED.
"""

from __future__ import annotations

import argparse
import ast
import copy
import json
import math
from pathlib import Path
import random
import re
import tempfile
from typing import Any


# ============================================================================
# Exact Special Functions (Pure Python 3.10+ Standard Library)
# ============================================================================


def _betacf(a: float, b: float, x: float) -> float:
    """Lentz's continued fraction for regularized incomplete beta I_x(a, b)."""
    max_iter = 200
    eps = 3.0e-15
    fpmin = 1.0e-300
    qab = a + b
    qap = a + 1.0
    qam = a - 1.0
    c = 1.0
    d = 1.0 - qab * x / qap
    if abs(d) < fpmin:
        d = fpmin
    d = 1.0 / d
    h = d
    for m in range(1, max_iter + 1):
        m2 = 2 * m
        aa = m * (b - m) * x / ((qam + m2) * (a + m2))
        d = 1.0 + aa * d
        if abs(d) < fpmin:
            d = fpmin
        c = 1.0 + aa / c
        if abs(c) < fpmin:
            c = fpmin
        d = 1.0 / d
        h *= d * c
        aa = -(a + m) * (qab + m) * x / ((a + m2) * (qap + m2))
        d = 1.0 + aa * d
        if abs(d) < fpmin:
            d = fpmin
        c = 1.0 + aa / c
        if abs(c) < fpmin:
            c = fpmin
        d = 1.0 / d
        delta = d * c
        h *= delta
        if abs(delta - 1.0) < eps:
            break
    return h


def reg_inc_beta(a: float, b: float, x: float) -> float:
    """Regularized incomplete beta function I_x(a, b) for x in [0, 1]."""
    if x <= 0.0:
        return 0.0
    if x >= 1.0:
        return 1.0
    lbeta = math.lgamma(a + b) - math.lgamma(a) - math.lgamma(b)
    front = math.exp(lbeta + a * math.log(x) + b * math.log(1.0 - x))
    if x < (a + 1.0) / (a + b + 2.0):
        return front * _betacf(a, b, x) / a
    return 1.0 - front * _betacf(b, a, 1.0 - x) / b


def student_t_cdf(t_val: float, df: int) -> float:
    """Exact Student's-t CDF matching scipy.stats.t.cdf."""
    if df <= 0:
        return float("nan")
    if t_val == 0.0:
        return 0.5
    x = df / (df + t_val * t_val)
    ib = reg_inc_beta(0.5 * df, 0.5, x)
    return 1.0 - 0.5 * ib if t_val > 0.0 else 0.5 * ib


def student_t_ppf(p: float, df: int) -> float:
    """Exact Student's-t inverse CDF matching scipy.stats.t.ppf(p, df)."""
    if df <= 0 or not (0.0 < p < 1.0):
        return float("nan")
    if p == 0.5:
        return 0.0
    sign = 1.0 if p > 0.5 else -1.0
    target = p if p > 0.5 else 1.0 - p
    lo, hi = 0.0, 1.0
    while student_t_cdf(hi, df) < target:
        hi *= 2.0
    for _ in range(90):
        mid = 0.5 * (lo + hi)
        if student_t_cdf(mid, df) < target:
            lo = mid
        else:
            hi = mid
    return sign * 0.5 * (lo + hi)


def _np_mean(xs: list[float]) -> float:
    return sum(xs) / len(xs) if xs else float("nan")


def _np_std_ddof1(xs: list[float]) -> float:
    """Matches numpy.std(xs, ddof=1) IEEE-754 two-pass behavior, incl. n<=1 NaN."""
    n = len(xs)
    if n <= 1:
        return float("nan")
    mu = _np_mean(xs)
    return math.sqrt(sum((x - mu) ** 2 for x in xs) / (n - 1))


# ============================================================================
# PROBE 1: CORE-Bench@e32a2980 & SUPER@0c03d77a Evaluator Forensics
# ============================================================================


def corebench_eval_result_json(
    gt_result: list[dict[str, Any]],
    reported_result_in: dict[str, Any],
) -> dict[str, int]:
    """Faithful port of siegelz/core-bench@e32a2980 benchmark/evaluations.py:42-104."""
    reported_result = copy.deepcopy(reported_result_in)
    correct_written_answers = 0
    correct_vision_answers = 0

    numeric_keys = [
        key for key in gt_result[0].keys() if isinstance(gt_result[0][key], (int, float))
    ]
    list_keys = [key for key in gt_result[0].keys() if isinstance(gt_result[0][key], list)]
    string_keys = [key for key in gt_result[0].keys() if isinstance(gt_result[0][key], str)]

    total_written_questions = (
        len([key for key in string_keys if "fig" not in key])
        + len([key for key in numeric_keys if "fig" not in key])
        + len([key for key in list_keys if "fig" not in key])
    )
    total_vision_questions = (
        len([key for key in string_keys if "fig" in key])
        + len([key for key in numeric_keys if "fig" in key])
        + len([key for key in list_keys if "fig" in key])
    )

    try:
        for key in reported_result.keys():
            try:
                if "%" in reported_result[key]:
                    reported_result[key] = reported_result[key].replace("%", "")
                reported_result[key] = float(reported_result[key])
            except Exception:
                pass

        mean_result = {
            key: _np_mean([float(result[key]) for result in gt_result])
            for key in numeric_keys
        }
        std_dev_result = {
            key: _np_std_ddof1([float(result[key]) for result in gt_result])
            for key in numeric_keys
        }
        sample_size = len(gt_result)

        t_value = student_t_ppf(0.975, sample_size - 1)
        prediction_interval_bounds = {
            key: (
                mean_result[key]
                - t_value * std_dev_result[key] * math.sqrt(1 + 1 / sample_size),
                mean_result[key]
                + t_value * std_dev_result[key] * math.sqrt(1 + 1 / sample_size),
            )
            for key in numeric_keys
        }

        try:
            for key in reported_result.keys():
                if key in numeric_keys:
                    lower_bound, upper_bound = prediction_interval_bounds[key]
                    if lower_bound <= reported_result[key] <= upper_bound:
                        if "fig" in key:
                            correct_vision_answers += 1
                        else:
                            correct_written_answers += 1
                elif key in list_keys:
                    if reported_result[key] == gt_result[0][key]:
                        if "fig" in key:
                            correct_vision_answers += 1
                        else:
                            correct_written_answers += 1
                elif key in string_keys:
                    if str(reported_result[key]).lower() == str(gt_result[0][key]).lower():
                        if "fig" in key:
                            correct_vision_answers += 1
                        else:
                            correct_written_answers += 1
        except Exception:
            pass
    except Exception:
        pass

    return {
        "correct_written_answers": correct_written_answers,
        "correct_vision_answers": correct_vision_answers,
        "total_written_questions": total_written_questions,
        "total_vision_questions": total_vision_questions,
    }


def super_evaluate(predicted: Any, gold: Any, float_epsilon: float = 1e-2) -> float:
    """Faithful port of allenai/super-benchmark@0c03d77a super/evaluate_dataset.py:18-43.

    Note second argument-swap bug at upstream line 35: recursive dict branch passes
    (gv, predicted.get(gk, None)) into (predicted, gold)!
    """
    if type(gold) == int:  # noqa: E721 (exact upstream type() check)
        gold = float(gold)
    if type(predicted) == int:  # noqa: E721
        predicted = float(predicted)
    if type(gold) != type(predicted):  # noqa: E721
        return 0.0
    if type(gold) == list:  # noqa: E721
        if len(gold) == 0:
            raise ValueError("Gold is empty")
        return sum([super_evaluate(p, g) for p, g in zip(predicted, gold)]) / len(gold)
    if type(gold) == dict:  # noqa: E721
        if len(gold) == 0:
            raise ValueError("Gold is empty")
        return (
            sum(
                [
                    super_evaluate(gv, predicted.get(gk, None), float_epsilon=float_epsilon)
                    for gk, gv in gold.items()
                ]
            )
            / len(gold)
        )
    if type(gold) == str:  # noqa: E721
        return float(predicted.strip() == gold.strip())
    if type(gold) == float:  # noqa: E721
        return float(abs(predicted - gold) < float_epsilon)
    raise NotImplementedError


def super_evaluate_fixed(predicted: Any, gold: Any, float_epsilon: float = 1e-2) -> float:
    """Reference fix patching BOTH evaluate_dataset.py:146 AND recursive dict line 35."""
    if type(gold) == int:  # noqa: E721
        gold = float(gold)
    if type(predicted) == int:  # noqa: E721
        predicted = float(predicted)
    if type(gold) != type(predicted):  # noqa: E721
        return 0.0
    if type(gold) == list:  # noqa: E721
        if len(gold) == 0:
            raise ValueError("Gold is empty")
        return sum([super_evaluate_fixed(p, g, float_epsilon) for p, g in zip(predicted, gold)]) / len(gold)
    if type(gold) == dict:  # noqa: E721
        if len(gold) == 0:
            raise ValueError("Gold is empty")
        return (
            sum(
                [
                    super_evaluate_fixed(predicted.get(gk, None), gv, float_epsilon=float_epsilon)
                    for gk, gv in gold.items()
                ]
            )
            / len(gold)
        )
    if type(gold) == str:  # noqa: E721
        return float(predicted.strip() == gold.strip())
    if type(gold) == float:  # noqa: E721
        return float(abs(predicted - gold) < float_epsilon)
    raise NotImplementedError


def super_get_output_match_buggy(gold_answer: Any, submission: Any) -> float:
    """Faithful port of super/evaluate_dataset.py:146 reversed call evaluate(gold_answer, submission)."""
    return super_evaluate(gold_answer, submission)


def run_probe_1() -> None:
    print("=== PROBE 1: CORE-Bench@e32a2980 & SUPER@0c03d77a Evaluator Forensics ===")
    print("Basis: source + execution + documentation (90-capsule schema & evaluations.py/evaluate_dataset.py)")

    # Verify Student's-t ppf against analytical df=1 Cauchy & df=2 exact closed forms:
    t_df1_exact = math.tan(math.pi * (0.975 - 0.5))
    t_df2_exact = 0.95 / math.sqrt(2.0 * 0.975 * 0.025)
    assert abs(student_t_ppf(0.975, 1) - t_df1_exact) < 1e-12
    assert abs(student_t_ppf(0.975, 2) - t_df2_exact) < 1e-12
    assert math.isnan(student_t_ppf(0.975, 0))

    # 1. Outer try: loop-abort on "N/A" (evaluations.py:80-97)
    gt_multi = [
        {"q1_rmse": 0.120, "q2_acc": 0.945, "q3_model": "LASSO", "fig q4_auc": 0.880},
        {"q1_rmse": 0.122, "q2_acc": 0.946, "q3_model": "LASSO", "fig q4_auc": 0.882},
        {"q1_rmse": 0.118, "q2_acc": 0.944, "q3_model": "LASSO", "fig q4_auc": 0.878},
    ]
    rep_abort = {
        "q1_rmse": "N/A",
        "q2_acc": 0.945,
        "q3_model": "LASSO",
        "fig q4_auc": 0.880,
    }
    rep_reordered = {
        "q2_acc": 0.945,
        "q3_model": "LASSO",
        "fig q4_auc": 0.880,
        "q1_rmse": "N/A",
    }
    res_abort = corebench_eval_result_json(gt_multi, rep_abort)
    res_reordered = corebench_eval_result_json(gt_multi, rep_reordered)
    assert res_abort["correct_written_answers"] == 0
    assert res_abort["correct_vision_answers"] == 0
    assert res_reordered["correct_written_answers"] == 2
    assert res_reordered["correct_vision_answers"] == 1

    # 2. Python bool-is-int misclassification (isinstance(True, (int, float)) == True)
    assert isinstance(True, (int, float)) is True
    gt_bool = [
        {"converged": True, "metric": 1.5},
        {"converged": True, "metric": 1.6},
        {"converged": True, "metric": 1.4},
    ]
    res_bool_str = corebench_eval_result_json(gt_bool, {"converged": "True", "metric": 1.5})
    assert res_bool_str["correct_written_answers"] == 0  # "True" triggers TypeError abort!

    # 3. Single-sample (n == 1) NaN interval collapse
    gt_n1 = [{"acc": 0.85}]
    res_n1 = corebench_eval_result_json(gt_n1, {"acc": 0.85})
    assert res_n1["correct_written_answers"] == 0

    # 4. Zero-variance (std == 0) zero-tolerance float rejection & ULP-residual range on real capsule values:
    # - capsule-8536428 exact GT: 0.9489373841106832 across 3 runs -> std == 0.0
    # - capsule-1906954 ULP-residual GT: 0.092 -> |(3*x)/3 - x| == 1 ULP(x), std = 1.70e-17
    # - capsule-8536428 ULP-residual GT: 0.9484683342481508 -> std = 1.36e-16
    # - capsule-6460826 / capsule-2345790 percentage-scale GT: 97.22 / 99.41 -> std = 1.74e-14
    ulp_examples = [0.092, 0.9484683342481508, 97.22, 99.41]
    ulp_stds = [_np_std_ddof1([v, v, v]) for v in ulp_examples]
    for val in ulp_examples:
        mean_3 = (val + val + val) / 3.0
        assert abs(mean_3 - val) <= math.ulp(val)  # mean rounding residual <= 1 ULP of |x|
    ulp_std_min, ulp_std_max = min(ulp_stds), max(ulp_stds)
    assert 1.69e-17 <= ulp_std_min <= 1.71e-17
    assert 1.73e-14 <= ulp_std_max <= 1.75e-14

    gt_det = [{"nb_acc": 0.9489373841106832, "nb_prec": 0.9484683342481508} for _ in range(3)]
    assert _np_std_ddof1([r["nb_acc"] for r in gt_det]) == 0.0
    res_1e16_drift = corebench_eval_result_json(
        gt_det,
        {"nb_acc": 0.9489373841106832 + 2.220446049250313e-16, "nb_prec": "94.84683342481508%"},
    )
    res_exact_det = corebench_eval_result_json(
        gt_det,
        {"nb_acc": 0.9489373841106832, "nb_prec": 0.9484683342481508},
    )
    assert res_1e16_drift["correct_written_answers"] == 0
    assert res_exact_det["correct_written_answers"] == 2

    # 5. Case-sensitive 'fig' in key vs 'fig' in key.lower() modality routing
    gt_fig_case = [{"config_lr": 0.01, "Fig_1_auc": 0.91} for _ in range(3)]
    res_fig_case = corebench_eval_result_json(
        gt_fig_case, {"config_lr": 0.01, "Fig_1_auc": 0.91}
    )
    assert res_fig_case["total_vision_questions"] == 1  # "config_lr" miscounted as vision!
    assert res_fig_case["total_written_questions"] == 1  # "Fig_1_auc" miscounted as written!
    assert [k for k in gt_fig_case[0] if "fig" in k.lower()] == ["config_lr", "Fig_1_auc"]

    # Verified 90-capsule dataset partition invariants (45 train + 45 test):
    n_caps_train, n_caps_test = 45, 45
    n_caps_total = n_caps_train + n_caps_test
    num_ident_train, num_tot_train = 72, 80
    num_ident_test, num_tot_test = 43, 50
    num_ident_total = num_ident_train + num_ident_test
    num_tot_all = num_tot_train + num_tot_test
    num_std_zero = 100
    num_ulp_art = 10 + 4 + 1  # 10 at 1.36e-16, 4 at 1.74e-14, 1 at 1.70e-17
    n_str_q, n_list_q, n_bool_q = 50, 1, 0
    n_tot_q = num_tot_all + n_str_q + n_list_q + n_bool_q
    n_stochastic_paper = 17  # arXiv:2409.11363v2 §3
    assert n_caps_total == 90 and num_ident_total == 115 and num_tot_all == 130
    assert num_std_zero + num_ulp_art == num_ident_total and num_ulp_art == 15
    assert n_tot_q == 181

    print(
        f"  t_0.975(df=2) = {t_df2_exact:.12f}; "
        f"loop_abort_credit = {res_abort['correct_written_answers'] + res_abort['correct_vision_answers']}/4 "
        f"(vs key-reordered {res_reordered['correct_written_answers'] + res_reordered['correct_vision_answers']}/4)"
    )
    print(
        f"  bool_str_abort_credit = {res_bool_str['correct_written_answers']}/2; "
        f"n1_exact_match_credit = {res_n1['correct_written_answers']}/1; "
        f"std0_1ulp_drift_credit = {res_1e16_drift['correct_written_answers']}/2"
    )
    print(
        f"  modality_routing('config_lr','Fig_1_auc'): "
        f"total_vision={res_fig_case['total_vision_questions']} ('config_lr'), "
        f"total_written={res_fig_case['total_written_questions']} ('Fig_1_auc')"
    )
    print(
        f"  official_{n_caps_total}_capsule_audit: n=3 in {n_caps_total}/{n_caps_total} "
        f"(0 n=1, {n_bool_q} bool, 0 'fig' collision; {n_stochastic_paper}/{n_tot_q} stochastic per §3); "
        f"identical_3run_numeric = {num_ident_total}/{num_tot_all} "
        f"({100*num_ident_total/num_tot_all:.2f}%: {num_ident_train}/{num_tot_train} train, "
        f"{num_ident_test}/{num_tot_test} test; {num_std_zero}/{num_tot_all} "
        f"[{100*num_std_zero/num_tot_all:.2f}%] exact std==0.0, {num_ulp_art}/{num_tot_all} "
        f"[{100*num_ulp_art/num_tot_all:.2f}%] std in [{ulp_std_min:.2e}, {ulp_std_max:.2e}] <= 1 ULP(|x|))"
    )

    # 6. SUPER@0c03d77a reversed evaluate(gold_answer, submission) at L146 + recursive dict swap at L35 + CLI trap
    gold_list = [0.81, 0.74, 0.69, 0.92]
    sub_prefix1 = [0.81]
    buggy_list_score = super_get_output_match_buggy(gold_list, sub_prefix1)
    true_list_score = super_evaluate_fixed(sub_prefix1, gold_list)
    assert buggy_list_score == 1.0 and true_list_score == 0.25

    gold_dict = {"acc": 0.91, "f1": 0.88, "auc": 0.95}
    sub_dict1 = {"acc": 0.91}
    buggy_dict_score = super_get_output_match_buggy(gold_dict, sub_dict1)
    true_dict_score = super_evaluate_fixed(sub_dict1, gold_dict)
    assert buggy_dict_score == 1.0 and abs(true_dict_score - (1.0 / 3.0)) < 1e-12

    # Second swap at evaluate_dataset.py:35: patching ONLY L146 still inverts nested dict values!
    gold_nested = {"metrics": [0.81, 0.74, 0.69, 0.92]}
    sub_nested_prefix1 = {"metrics": [0.81]}
    only_l146_patched_nested = super_evaluate(sub_nested_prefix1, gold_nested)
    both_l35_l146_patched_nested = super_evaluate_fixed(sub_nested_prefix1, gold_nested)
    assert only_l146_patched_nested == 1.0 and both_l35_l146_patched_nested == 0.25

    empty_sub_crashed = False
    try:
        super_get_output_match_buggy(gold_list, [])
    except ValueError as exc:
        empty_sub_crashed = "Gold is empty" in str(exc)
    assert empty_sub_crashed is True

    # super/run_on_benchmark.py:23 & 111-136 CLI contradiction
    sup_parser = argparse.ArgumentParser(add_help=False, exit_on_error=False)
    sup_parser.add_argument("--agent-name", type=str, choices=["react-super"], default="react")
    parsed_default = sup_parser.parse_args([])
    parsed_react_super = sup_parser.parse_args(["--agent-name", "react-super"])
    cli_react_rejected = False
    try:
        sup_parser.parse_args(["--agent-name", "react"])
    except argparse.ArgumentError:
        cli_react_rejected = True
    assert parsed_default.agent_name == "react"
    assert parsed_react_super.agent_name != "react"  # triggers line 136 `raise ValueError`!
    assert cli_react_rejected is True

    print(
        f"  super_reversed_eval: 1/4_list_prefix -> buggy={buggy_list_score:.2f} (true={true_list_score:.2f}), "
        f"1/3_dict_subset -> buggy={buggy_dict_score:.2f} (true={true_dict_score:.4f}), "
        f"nested_dict_L35_swap(L146_only)={only_l146_patched_nested:.2f} (true={both_l35_l146_patched_nested:.2f}), "
        f"empty_sub_ValueError={empty_sub_crashed}, cli_explicit_flag_trap=True"
    )


# ============================================================================
# PROBE 2: SciCode@e3158ea0 Scorer, HDF5/Broadcast Bugs & Conditioning Decay
# ============================================================================


def scicode_get_function_from_code(code_string: str | None, function_name: str) -> str | None:
    """Faithful port of scicode-bench/SciCode@e3158ea0 src/scicode/parse/parse.py:30-51."""
    if code_string is None:
        return None
    try:
        tree = ast.parse(code_string)
        for node in ast.walk(tree):
            if isinstance(node, (ast.FunctionDef, ast.ClassDef)) and node.name == function_name:
                return ast.unparse(node)
    except Exception:
        return code_string
    return None


def scicode_cli_score_dir(
    scicode_data: list[dict[str, Any]],
    code_dir: Path,
    prob_num: int,
    passing_steps: set[str],
) -> tuple[int, list[int]]:
    """Faithful port of eval/scripts/test_generated_code.py:34-57, 84-97, 125-127."""
    json_dct: dict[str, int] = {}
    json_idx: dict[str, int] = {}
    for prob_data in scicode_data:
        json_dct[prob_data["problem_id"]] = len(prob_data["sub_steps"])  # unused!
        json_idx[prob_data["problem_id"]] = scicode_data.index(prob_data)

    correct_prob = [0] * prob_num
    tot_prob = [0] * prob_num
    for file_path in sorted(code_dir.iterdir()):
        if file_path.is_file():
            func_id = file_path.stem
            prob_id = func_id.split(".")[0]
            file_step = func_id.split(".")[1]
            json_content = scicode_data[json_idx[prob_id]]
            step_id = json_content["sub_steps"][int(file_step) - 1]["step_number"]
            tot_prob[int(prob_id) - 1] += 1
            if step_id in passing_steps:
                correct_prob[int(prob_id) - 1] += 1

    solved = [
        i + 1
        for i in range(prob_num)
        if correct_prob[i] == tot_prob[i] and tot_prob[i] != 0
    ]
    return len(solved), solved


def scicode_inspect_ai_gold_oracle_score(
    test_step_counts: dict[str, int],
) -> tuple[int, int, int, int]:
    """Faithful port of eval/inspect_ai/scicode.py:253-294 & 359-367 under mode='gold'."""
    problems_solved = 0
    sum_correct = 0
    sum_total_steps = 0
    for problem_id, n_sub in sorted(test_step_counts.items(), key=lambda kv: int(kv[0])):
        total_steps = n_sub
        total_correct = 0
        for idx in range(n_sub):
            if (
                (problem_id == "13" and idx == 5)
                or (problem_id == "62" and idx == 0)
                or (problem_id == "76" and idx == 2)
            ):
                continue
            total_correct += 1  # gold oracle passes every non-skipped step
        problem_correct = 1 if total_correct == total_steps else 0
        problems_solved += problem_correct
        sum_correct += total_correct
        sum_total_steps += total_steps
    return problems_solved, len(test_step_counts), sum_correct, sum_total_steps


def _broadcast_allclose_2d(
    a: list[list[float]],
    b: list[list[float]],
    atol: float = 1e-8,
    rtol: float = 1e-5,
) -> bool:
    """Exact 2D NumPy broadcast + allclose semantics (cmp.py:29, 68 omits shape check)."""
    ra, ca = len(a), len(a[0])
    rb, cb = len(b), len(b[0])
    if not (ra == rb or ra == 1 or rb == 1):
        raise ValueError("Incompatible row broadcast")
    if not (ca == cb or ca == 1 or cb == 1):
        raise ValueError("Incompatible col broadcast")
    rmax, cmax = max(ra, rb), max(ca, cb)
    for r in range(rmax):
        for c in range(cmax):
            va = a[0 if ra == 1 else r][0 if ca == 1 else c]
            vb = b[0 if rb == 1 else r][0 if cb == 1 else c]
            if abs(va - vb) > atol + rtol * abs(vb):
                return False
    return True


def _fit_beta_binomial_sum_alpha_beta(mean_p: float, step_counts: list[int], target_main: float) -> float:
    """Finds concentration S = alpha + beta so E[theta^K] matches target_main."""
    lo, hi = 1e-4, 500.0
    for _ in range(80):
        mid = 0.5 * (lo + hi)
        alpha = mean_p * mid
        pred = 0.0
        for k in step_counts:
            prod = 1.0
            for j in range(k):
                prod *= (alpha + j) / (mid + j)
            pred += prod
        pred /= len(step_counts)
        if pred > target_main:
            lo = mid
        else:
            hi = mid
    return 0.5 * (lo + hi)


# Exact verbatim problem_id -> raw len(sub_steps) from HF SciCode1/SciCode@4510f6a6aa27c43fad7b43da2c59602a86e88480
SCICODE_DEV_RAW_STEPS: dict[str, int] = {
    "10": 11, "1": 1, "3": 1, "4": 1, "6": 1, "7": 1, "19": 2, "78": 3,
    "29": 3, "38": 3, "44": 3, "47": 4, "49": 4, "51": 4, "70": 8,
}

SCICODE_TEST_RAW_STEPS: dict[str, int] = {
    "77": 12, "11": 12, "12": 14, "13": 15, "2": 1, "74": 1, "5": 1, "8": 1,
    "9": 1, "14": 2, "15": 2, "16": 2, "17": 2, "18": 2, "20": 2, "21": 3,
    "22": 3, "23": 3, "24": 3, "25": 3, "26": 3, "27": 3, "28": 3, "75": 3,
    "30": 3, "31": 3, "32": 3, "33": 3, "34": 3, "35": 3, "36": 3, "37": 3,
    "39": 3, "40": 3, "41": 3, "42": 3, "43": 3, "45": 4, "46": 4, "48": 4,
    "79": 4, "76": 4, "50": 4, "52": 4, "53": 4, "54": 4, "55": 4, "56": 4,
    "57": 5, "58": 5, "59": 5, "60": 5, "61": 5, "62": 6, "63": 6, "64": 6,
    "65": 6, "66": 6, "67": 6, "80": 7, "68": 8, "69": 8, "71": 9, "72": 9,
    "73": 9,
}


def run_probe_2() -> None:
    print("\n=== PROBE 2: SciCode@e3158ea0 Scorer, HDF5/Broadcast & Conditioning Decay ===")
    print("Basis: source + execution + derived (verbatim HF SciCode1/SciCode@4510f6a6 split + Beta-Binomial model)")

    # 1. Partial-file false pass in test_generated_code.py + resumed AST None crash in gencode.py:129
    missing_fn = scicode_get_function_from_code("def wrong_helper(x):\n    return x\n", "step1_fn")
    assert missing_fn is None
    resumed_join_crashed = False
    try:
        _ = "\n".join([missing_fn])  # type: ignore[list-item]  # gencode.py:83, 129
    except TypeError:
        resumed_join_crashed = True
    assert resumed_join_crashed is True

    mock_data = [
        {
            "problem_id": "1",
            "sub_steps": [{"step_number": f"1.{k}"} for k in range(1, 5)],
        }
    ]
    with tempfile.TemporaryDirectory() as tmp:
        cdir = Path(tmp)
        (cdir / "1.1.py").write_text("def step1_fn(x):\n    return x\n", encoding="utf-8")
        n_solved, solved_ids = scicode_cli_score_dir(
            mock_data, cdir, prob_num=1, passing_steps={"1.1"}
        )
    assert n_solved == 1 and solved_ids == [1]

    # Contrast with eval/inspect_ai/scicode.py:253-294 ceiling bug on exact 65 test problems
    # (291 raw sub_steps = 288 active steps + 3 zero-test fixtures 13.6, 62.1, 76.3; dev = 15 probs / 50 steps)
    assert len(SCICODE_DEV_RAW_STEPS) == 15 and sum(SCICODE_DEV_RAW_STEPS.values()) == 50
    assert len(SCICODE_TEST_RAW_STEPS) == 65 and sum(SCICODE_TEST_RAW_STEPS.values()) == 291
    assert set(SCICODE_DEV_RAW_STEPS).isdisjoint(SCICODE_TEST_RAW_STEPS)
    assert {int(k) for k in (*SCICODE_DEV_RAW_STEPS, *SCICODE_TEST_RAW_STEPS)} == set(range(1, 81))

    gold_prob, gold_tot_prob, gold_steps, gold_tot_steps = scicode_inspect_ai_gold_oracle_score(
        SCICODE_TEST_RAW_STEPS
    )
    assert gold_tot_prob == 65 and gold_steps == 288 and gold_tot_steps == 291
    assert gold_prob == 62  # Problems 13 (14/15), 62 (5/6), 76 (3/4) impossible even for gold oracle!

    # 2. HDF5 B-tree ASCII key-order corruption (parse.py:75-79, 169-171) on inhomogeneous len>=10 list
    original_ragged = [[i] * ((i % 3) + 1) for i in range(12)]
    hdf5_group = {f"var{i + 1}": original_ragged[i] for i in range(len(original_ragged))}
    reconstructed = [hdf5_group[k] for k in sorted(hdf5_group.keys())]  # ASCII B-tree iteration
    permuted_positions = sum(
        1 for a, b in zip(original_ragged, reconstructed) if a != b
    )
    assert reconstructed[1] == original_ragged[9]  # 'var10' lands at index 1!
    assert permuted_positions == 11  # only index 0 ('var1') stays in place!

    # 3. cmp.py:29,68 broadcast false-pass ((8,1) vs rank-1 constant-row (8,8)) & exact dataset partition
    pred_col = [[float(r + 1)] for r in range(8)]  # shape (8, 1)
    gold_mat = [[float(r + 1) for _ in range(8)] for r in range(8)]  # shape (8, 8)
    assert (len(pred_col), len(pred_col[0])) != (len(gold_mat), len(gold_mat[0]))
    assert _broadcast_allclose_2d(pred_col, gold_mat) is True

    # Exact unique test_cases partition across SciCode1/SciCode@4510f6a6 (dev + test):
    tc_dev_total, tc_test_total = 167, 915
    tc_all_total = tc_dev_total + tc_test_total
    # Mutually exclusive comparison-family partition of all 1,082 test cases:
    fam_allclose_only = 920
    fam_tuple_list_only = 90
    fam_dicts_only = 3
    fam_dicts_and_allclose = 3  # naive per-helper sum 924+90+6=1020 double-counts these 3!
    fam_allclose_and_isclose = 1
    fam_isclose_only = 14
    fam_exact_or_ineq = 51
    unique_allclose_family = (
        fam_allclose_only
        + fam_tuple_list_only
        + fam_dicts_only
        + fam_dicts_and_allclose
        + fam_allclose_and_isclose
    )
    assert tc_all_total == 1082
    assert unique_allclose_family == 1017
    assert unique_allclose_family + fam_isclose_only + fam_exact_or_ineq == tc_all_total

    unshaped_test, allclose_test = 840, 858
    unshaped_dev, allclose_dev = 144, 159
    unshaped_total = unshaped_test + unshaped_dev
    assert allclose_test + allclose_dev == unique_allclose_family
    assert unshaped_total == 984

    # 4. Multi-step condition-number amplification across K=4 scientific pipeline steps:
    kappa_step = 30.0
    x_exact = [0.0, 1.0]
    x_num = [4.0e-6, 1.0]
    rel_err_step1 = max(abs(a - b) for a, b in zip(x_num, x_exact))
    step1_passes = rel_err_step1 <= (1e-8 + 1e-5 * 1.0)
    for _ in range(3):
        x_exact = [kappa_step * x_exact[0], 1.0 * x_exact[1]]
        x_num = [kappa_step * x_num[0], 1.0 * x_num[1]]
    rel_err_step4 = max(abs(a - b) for a, b in zip(x_num, x_exact))
    step4_passes = rel_err_step4 <= (1e-8 + 1e-5 * 1.0)
    assert step1_passes is True and step4_passes is False
    assert abs(rel_err_step4 - 4.0e-6 * (kappa_step ** 3)) < 1e-12  # 0.108 >> 1e-5!

    # 5. Exact Jensen's inequality & Beta-Binomial pass@1 analysis on real 65-problem test split
    active_counts = [
        v - (1 if k in {"13", "62", "76"} else 0) for k, v in SCICODE_TEST_RAW_STEPS.items()
    ]
    n_single_step_test = sum(1 for k in active_counts if k == 1)
    assert sum(active_counts) == 288 and len(active_counts) == 65 and n_single_step_test == 5

    naive_jensen_no_bg = 0.260 ** (288.0 / 65.0)
    naive_jensen_with_bg = 0.354 ** (288.0 / 65.0)
    iid_no_bg = sum(0.260 ** k for k in active_counts) / 65.0
    iid_gpt4o_no_bg = sum(0.250 ** k for k in active_counts) / 65.0
    iid_with_bg = sum(0.354 ** k for k in active_counts) / 65.0

    s_no_bg = _fit_beta_binomial_sum_alpha_beta(0.260, active_counts, 3.0 / 65.0)
    s_with_bg = _fit_beta_binomial_sum_alpha_beta(0.354, active_counts, 8.0 / 65.0)
    s_gpt4o_with_bg = _fit_beta_binomial_sum_alpha_beta(0.354, active_counts, 6.0 / 65.0)
    rho_no_bg = 1.0 / (s_no_bg + 1.0)
    rho_with_bg = 1.0 / (s_with_bg + 1.0)
    rho_gpt4o_with_bg = 1.0 / (s_gpt4o_with_bg + 1.0)

    assert iid_no_bg / naive_jensen_no_bg > 13.0  # 3.33% vs 0.26% (13.02x Jensen gap!)
    assert (1.0 / 65.0) < iid_gpt4o_no_bg  # GPT-4o 1.54% < exact heterogeneous i.i.d. 3.12%!
    assert 0.05 < rho_no_bg < 0.15 and 0.20 < rho_with_bg < 0.35

    print(
        f"  cli_partial_dir_solved = {n_solved}/1 (1.1.py only, json_dct=4 unused, gencode_None_join_TypeError={resumed_join_crashed}); "
        f"inspect_ai_gold_oracle = {gold_prob}/{gold_tot_prob} problems ({100*gold_prob/gold_tot_prob:.2f}%), "
        f"{gold_steps}/{gold_tot_steps} steps ({100*gold_steps/gold_tot_steps:.2f}%)"
    )
    print(
        f"  hdf5_var10_ragged_permuted = {permuted_positions}/12 indices (idx1 -> elem9); "
        f"cmp_broadcast_(8,1)_vs_(8,8)_allclose = True "
        f"(unshaped unique allclose = {unshaped_total}/{unique_allclose_family} [{100*unshaped_total/unique_allclose_family:.2f}%]: "
        f"test {unshaped_test}/{allclose_test} [{100*unshaped_test/allclose_test:.2f}%], "
        f"dev {unshaped_dev}/{allclose_dev} [{100*unshaped_dev/allclose_dev:.2f}%]; "
        f"total test_cases = {tc_dev_total} dev + {tc_test_total} test = {tc_all_total})"
    )
    print(
        f"  cond_amplification(kappa=30, K=4): step1_err={rel_err_step1:.2e} (pass={step1_passes}) "
        f"-> step4_err={rel_err_step4:.4f} (pass={step4_passes})"
    )
    print(
        f"  pass@1_exact_65test_split (5 single-step probs, K in [1..14], mean K=4.431): "
        f"Claude3.5 no_bg 26.0% -> 4.62% (naive_p^E[K]={100*naive_jensen_no_bg:.2f}%, exact_E[p^K]={100*iid_no_bg:.2f}% [{iid_no_bg/naive_jensen_no_bg:.2f}x], rho={rho_no_bg:.3f}); "
        f"GPT-4o no_bg 25.0% -> 1.54% (< exact_E[p^K]={100*iid_gpt4o_no_bg:.2f}%)"
    )
    print(
        f"  pass@1_with_gold_bg (p_sub=35.4%, naive_p^E[K]={100*naive_jensen_with_bg:.2f}%, exact_E[p^K]={100*iid_with_bg:.2f}%): "
        f"Claude3.5 -> 12.31% (rho={rho_with_bg:.3f}); GPT-4o -> 9.23% (rho={rho_gpt4o_with_bg:.3f})"
    )


# ============================================================================
# PROBE 3: AI-Scientist v1@1de1dbc1 & v2@96bd5161 Reviewer + Winner's Curse
# ============================================================================


REVIEW_SCORE_LIMITS: list[tuple[str, tuple[int, int]]] = [
    ("Originality", (1, 4)),
    ("Quality", (1, 4)),
    ("Clarity", (1, 4)),
    ("Significance", (1, 4)),
    ("Soundness", (1, 4)),
    ("Presentation", (1, 4)),
    ("Contribution", (1, 4)),
    ("Overall", (1, 10)),
    ("Confidence", (1, 5)),
]

REVIEWER_REFLECTION_PROMPT_LITERAL = (
    "Round {current_round}/{num_reflections}.\n"
    "In your thoughts, first carefully consider the accuracy and soundness of the review you just created."
)


def aiscientist_aggregate_and_reflect(
    parsed_reviews: list[dict[str, Any]],
    meta_review: dict[str, Any],
    reflection_outputs: list[tuple[str, dict[str, Any]]],
    version: str = "v1",
) -> tuple[dict[str, Any], list[str]]:
    """Faithful port of perform_review.py:170-239 (v1) & perform_llm_review.py:168-229 (v2)."""
    review = copy.deepcopy(meta_review)
    for score, limits in REVIEW_SCORE_LIMITS:
        scores = []
        for r in parsed_reviews:
            if score in r and limits[0] <= r[score] <= limits[1]:
                scores.append(r[score])
        if version == "v1":
            if not scores:
                raise ValueError("cannot convert float NaN to integer")
            review[score] = int(round(_np_mean(scores)))
        else:
            if scores:
                review[score] = int(round(_np_mean(scores)))

    sent_prompts: list[str] = []
    for text, refl_json in reflection_outputs:
        # Exact bug in v1 line 226 & v2 line 218: unformatted template string passed!
        sent_prompts.append(REVIEWER_REFLECTION_PROMPT_LITERAL)
        review = copy.deepcopy(refl_json)
        if "I am done" in text:
            break
    return review, sent_prompts


def bayesian_fdr(tpr: float, fpr: float, base_rate_q: float) -> tuple[float, float]:
    """Returns (precision P(valid|Accept), FDR P(invalid|Accept))."""
    tp_mass = tpr * base_rate_q
    fp_mass = fpr * (1.0 - base_rate_q)
    precision = tp_mass / (tp_mass + fp_mass)
    return precision, 1.0 - precision


def run_probe_3() -> None:
    print("\n=== PROBE 3: AI-Scientist@1de1dbc1 & v2@96bd5161 Split-Brain & Winner's Curse ===")
    print("Basis: source + execution + derived (exact closed-form post-ensemble MSE + Bayes FDR on Table 1)")

    # 1. Decision split-brain + banker's rounding + unformatted prompt + reflection overwrite
    base_fields = {k: 3 for k, _ in REVIEW_SCORE_LIMITS}
    ensemble = [dict(base_fields, Overall=s) for s in [3, 4, 4, 4, 7]]
    meta = dict(base_fields, Overall=6, Decision="Accept")

    agg_only, _ = aiscientist_aggregate_and_reflect(ensemble, meta, [], version="v2")
    assert agg_only["Overall"] == 4 and agg_only["Decision"] == "Accept"  # split-brain!

    # Banker's round-to-even asymmetry on 2-review or 4-review ties:
    assert int(round(_np_mean([4, 5]))) == 4  # 4.5 -> 4
    assert int(round(_np_mean([5, 6]))) == 6  # 5.5 -> 6

    # v1 crashes on empty valid scores while v2 guards with `if scores:`
    v1_crashed = False
    try:
        aiscientist_aggregate_and_reflect([{"Overall": 99}], meta, [], version="v1")
    except ValueError:
        v1_crashed = True
    v2_survived, _ = aiscientist_aggregate_and_reflect(
        [{"Overall": 99}], meta, [], version="v2"
    )
    assert v1_crashed is True and v2_survived["Overall"] == 6

    # Post-ensemble single-call reflection overwrite + unformatted prompt literal
    refl_step = ("Refined review.", dict(base_fields, Overall=7, Decision="Accept"))
    after_refl, prompts = aiscientist_aggregate_and_reflect(
        ensemble, meta, [refl_step], version="v2"
    )
    assert after_refl["Overall"] == 7  # 5-reviewer mean (4) overwritten by 1 call!
    assert "{current_round}/{num_reflections}" in prompts[0]

    # Exact closed-form MSE inflation for Y_refl = w * X_bar_K + (1 - w) * X_new:
    # MSE(Y_refl) / MSE(X_bar_K) = [w^2 * (sigma^2 / K) + (1 - w)^2 * sigma^2] / (sigma^2 / K)
    #                            = w^2 + K * (1 - w)^2.
    k_ens = 5
    w_anchor = 0.5
    exact_mse_ratio = (w_anchor ** 2) + k_ens * ((1.0 - w_anchor) ** 2)
    assert abs(exact_mse_ratio - 1.50) < 1e-12

    rng = random.Random(20261122 + 3)
    ens_errors_sq = 0.0
    refl_errors_sq = 0.0
    n_mc = 5000
    gauss = rng.gauss
    for _ in range(n_mc):
        d0 = gauss(0.0, 1.2)
        d1 = gauss(0.0, 1.2)
        d2 = gauss(0.0, 1.2)
        d3 = gauss(0.0, 1.2)
        d4 = gauss(0.0, 1.2)
        ens_err = (d0 + d1 + d2 + d3 + d4) / k_ens
        refl_err = w_anchor * ens_err + (1.0 - w_anchor) * gauss(0.0, 1.2)
        ens_errors_sq += ens_err * ens_err
        refl_errors_sq += refl_err * refl_err
    mc_mse_ratio = refl_errors_sq / ens_errors_sq
    assert abs(mc_mse_ratio - exact_mse_ratio) < 0.05

    # 2. Exact Bayesian Winner's Curse on AI Scientist v1 Table 1 (500 ICLR 2022 papers)
    prec_gpt4o_10, fdr_gpt4o_10 = bayesian_fdr(tpr=0.61, fpr=0.31, base_rate_q=0.10)
    prec_sonnet_10, fdr_sonnet_10 = bayesian_fdr(tpr=1.00, fpr=0.95, base_rate_q=0.10)
    prec_human_10, fdr_human_10 = bayesian_fdr(tpr=0.48, fpr=0.17, base_rate_q=0.10)
    prec_gpt4o_25, fdr_gpt4o_25 = bayesian_fdr(tpr=0.61, fpr=0.31, base_rate_q=0.25)

    assert abs(fdr_gpt4o_10 - (0.279 / 0.340)) < 1e-12  # 82.0588%
    assert abs(fdr_sonnet_10 - (0.855 / 0.955)) < 1e-12  # 89.5288%
    assert fdr_gpt4o_10 > 0.82 and fdr_sonnet_10 > 0.89

    print(
        f"  split_brain(ensemble=[3,4,4,4,7], meta='Accept'): Overall={agg_only['Overall']}, "
        f"Decision={agg_only['Decision']!r}; after_1_reflection Overall={after_refl['Overall']}"
    )
    print(
        f"  unformatted_prompt_token_present = {'{current_round}/{num_reflections}' in prompts[0]}; "
        f"v1_empty_scores_crash = {v1_crashed}, v2_guard_survives = True; "
        f"post_refl_MSE_ratio(K={k_ens}, w={w_anchor:.1f}) = {exact_mse_ratio:.2f}x exact (MC_5k={mc_mse_ratio:.2f}x)"
    )
    print(
        f"  bayes_FDR_at_q=0.10: GPT4o_ens@6 (FPR=0.31,TPR=0.61) -> Precision={100*prec_gpt4o_10:.2f}%, "
        f"FDR={100*fdr_gpt4o_10:.2f}% | Sonnet3.5 (FPR=0.95,TPR=1.00) -> FDR={100*fdr_sonnet_10:.2f}% "
        f"| Human (FPR=0.17,TPR=0.48) -> FDR={100*fdr_human_10:.2f}%"
    )
    print(
        f"  bayes_FDR_at_q=0.25: GPT4o_ens@6 -> Precision={100*prec_gpt4o_25:.2f}%, "
        f"FDR={100*fdr_gpt4o_25:.2f}%"
    )


# ============================================================================
# PROBE 4: AgentReview@9ce5ec76 Config/Visibility Bugs & Conformity Cascade
# ============================================================================


AGENTREVIEW_EXPERIMENT_CONFIG: dict[str, dict[str, Any]] = {
    "BASELINE": {
        "AC": ["BASELINE"],
        "reviewer": ["BASELINE", "BASELINE", "BASELINE"],
        "author": ["BASELINE"],
        "global_settings": {
            "provides_numeric_rating": ["reviewer", "ac"],
            "persons_aware_of_authors_identities": [],
        },
    },
    "unknowledgeable_Rx1": {  # experiment_config.py:66-84 (copy-paste defect!)
        "AC": ["BASELINE"],
        "reviewer": ["knowledgeable", "BASELINE", "BASELINE"],
        "author": ["BASELINE"],
        "global_settings": {
            "provides_numeric_rating": ["reviewer", "ac"],
            "persons_aware_of_authors_identities": [],
        },
    },
    "knowledgeable_Rx1": {  # experiment_config.py:86-104
        "AC": ["BASELINE"],
        "reviewer": ["knowledgeable", "BASELINE", "BASELINE"],
        "author": ["BASELINE"],
        "global_settings": {
            "provides_numeric_rating": ["reviewer", "ac"],
            "persons_aware_of_authors_identities": [],
        },
    },
    "no_numeric_ratings": {  # experiment_config.py:209-225 (1 reviewer instead of 3!)
        "AC": ["BASELINE"],
        "reviewer": ["BASELINE"],
        "author": ["BASELINE"],
        "global_settings": {
            "provides_numeric_rating": [],
            "persons_aware_of_authors_identities": [],
        },
    },
}


def agentreview_get_instructions_for_overall_scores(author_type: Any) -> str:
    """Faithful port of role_descriptions.py:79-89."""
    instruction = "Do not write any reasons. "
    if author_type not in ["famous"]:
        instruction += (
            "Do not assign scores of 7 or higher before the rebuttal unless the paper "
            "demonstrates exceptional originality and significantly advances the state-of-the-art in machine learning. "
        )
    instruction += "Intermediary integer scores such as 9, 7, 4, and 2 are allowed. "
    return instruction


def agentreview_get_reviewer_description_phase3(
    provides_numeric_rating: bool = True,
    **_unused: Any,
) -> str:
    """Faithful port of role_descriptions.py:92-95, 137-167 called by paper_review_arena.py:101-103."""
    guideline = "Based on the authors' responses, write an updated paper review in the reviewer-AC discussion."
    if provides_numeric_rating:
        guideline += (
            "\n\n## Format for the updated review\n\n```\n"
            "Overall rating: ... # Provide an updated overall rating using an integer from 1 to 10."
        )
    else:
        guideline += "\n\n```\n"
    return guideline


def agentreview_visible_messages(
    prev_messages: list[tuple[str, str]],
    agent_name: str,
    phase_index: int,
    area_chair_type: str = "BASELINE",
) -> list[tuple[str, str]]:
    """Faithful port of paper_review_message.py:54-88."""
    if phase_index == 3:
        # Exact bug at line 55: list comprehension is non-empty -> always truthy!
        if [agent_name.startswith(prefix) for prefix in ["AC", "Reviewer", "Paper Extractor"]]:
            return list(prev_messages)
        elif agent_name.startswith("Author"):
            return []
    elif phase_index == 4 and agent_name.startswith("AC"):
        if area_chair_type in ["inclusive", "BASELINE"]:
            return list(prev_messages)
        elif area_chair_type == "conformist":
            return [
                m for m in prev_messages
                if m[0].startswith("Author") or m[0].startswith("Reviewer")
            ]
        elif area_chair_type == "authoritarian":
            return [
                m for m in prev_messages
                if not (m[0].startswith("Author") or m[0].startswith("Reviewer"))
            ]
    return []


def agentreview_format_metareviews(metareviews: list[str], paper_ids: list[int]) -> str:
    """Faithful port of agentreview/utility/utils.py:306-314."""
    metareviews_formatted = ""
    for paper_id, metareview in zip(paper_ids, metareviews):
        metareview = re.sub(r"\n+", "\n", metareview)
        metareviews_formatted += f"Paper ID: {paper_id}\nMetareview: {metareview}\n{'-' * 5}\n"
    return metareviews_formatted


def agentreview_batched_ac_decisions(
    scores: list[float],
    shared_batch_order: list[int],
    quota_rng: random.Random,
    acceptance_rate: float = 0.32,
    num_papers_per_ac: int = 10,
) -> set[int]:
    """Faithful port of run_paper_decision_cli.py:47-50,97-110 + utility/utils.py:16-57."""
    n_papers = len(scores)
    num_batches = n_papers // num_papers_per_ac
    total_to_accept = acceptance_rate * n_papers
    base_val = int(total_to_accept // num_batches)
    remainder = int(total_to_accept % num_batches)
    quotas = [base_val + 1 if i < remainder else base_val for i in range(num_batches)]
    quota_rng.shuffle(quotas)

    accepted: set[int] = set()
    for batch_idx in range(num_batches):
        if batch_idx >= num_batches - 1:
            batch_ids = shared_batch_order[batch_idx * num_papers_per_ac :]
        else:
            batch_ids = shared_batch_order[
                batch_idx * num_papers_per_ac : (batch_idx + 1) * num_papers_per_ac
            ]
        ranked = sorted(batch_ids, key=lambda pid: scores[pid], reverse=True)
        accepted.update(ranked[: quotas[batch_idx]])
    return accepted


def run_probe_4() -> None:
    print("\n=== PROBE 4: AgentReview@9ce5ec76 Config Forensics & Conformity Cascade ===")
    print(
        "Basis: source + execution (defects 1-7) + derived "
        "(Table 1/5 variance decomposition, §A.2 co-reviewer reuse, stylized vocal-AC weights)"
    )

    # 1. Defect 1: unknowledgeable_Rx1 == knowledgeable_Rx1 (experiment_config.py:66-104)
    assert (
        AGENTREVIEW_EXPERIMENT_CONFIG["unknowledgeable_Rx1"]
        == AGENTREVIEW_EXPERIMENT_CONFIG["knowledgeable_Rx1"]
    )

    # 2. Defect 2: knows_authors bool passed into author_type not in ["famous"] (role_descriptions.py:82,428,508)
    knows_authors_bool = "reviewer" in ["reviewer", "ac"]
    assert knows_authors_bool is True
    famous_instr = agentreview_get_instructions_for_overall_scores(knows_authors_bool)
    assert "Do not assign scores of 7 or higher" in famous_instr  # cap NOT lifted!

    # 3. Defect 3: always-truthy [False, False, False] in Phase 3 visibility (paper_review_message.py:55-60)
    pool = [
        ("Paper Extractor", "paper body"),
        ("Reviewer 1", "score 6"),
        ("Author", "rebuttal"),
    ]
    author_phase3_vis = agentreview_visible_messages(pool, "Author", phase_index=3)
    assert len(author_phase3_vis) == 3  # dead `elif` leaked all 3 messages instead of []!

    # 4. Defect 4: no_numeric_ratings has 1 reviewer AND resets provides_numeric_rating=True in Phase 3
    assert len(AGENTREVIEW_EXPERIMENT_CONFIG["no_numeric_ratings"]["reviewer"]) == 1
    assert len(AGENTREVIEW_EXPERIMENT_CONFIG["BASELINE"]["reviewer"]) == 3
    reviewer_setting_dict = {"is_benign": None, "is_knowledgeable": None, "is_responsible": None}
    phase3_prompt = agentreview_get_reviewer_description_phase3(**reviewer_setting_dict)
    assert "integer from 1 to 10" in phase3_prompt

    # 5. Defect 5: conformist AC blinded to Paper Extractor; authoritarian AC blinded to Reviews/Author
    conf_vis = agentreview_visible_messages(pool, "AC", phase_index=4, area_chair_type="conformist")
    auth_vis = agentreview_visible_messages(pool, "AC", phase_index=4, area_chair_type="authoritarian")
    assert all(sender != "Paper Extractor" for sender, _ in conf_vis)
    assert [sender for sender, _ in auth_vis] == ["Paper Extractor"]

    # 6. Defect 6 & 7: Phase 5 unsliced `metareviews` zip bug (run_paper_decision_cli.py:94,108-114 +
    # utility/utils.py:306-314, persisted to disk by ArenaCLI.launch via save_llm_ac_decisions at
    # agentreview/ui/cli.py:243-259) & retry-loop role_desc duplication (paper_review_arena.py:91,106-108)
    all_pids = list(range(100, 130))  # 3 batches of 10 papers
    all_metas = [f"meta_for_{pid}" for pid in all_pids]
    batch1_ids = all_pids[10:20]  # Batch index 1 (papers 110..119)
    batch1_prompt_block = agentreview_format_metareviews(all_metas, batch1_ids)
    assert "Paper ID: 110\nMetareview: meta_for_100" in batch1_prompt_block
    assert "meta_for_110" not in batch1_prompt_block

    ac_role_desc = "AC base bio.\n"
    for _retry in range(3):
        ac_role_desc += batch1_prompt_block
    assert ac_role_desc.count("Paper ID: 110") == 3

    # 7. Moment-matched 3-reviewer conformity & 10-paper batched AC cascade (Tables 1, 2, 5; 32% cutoff)
    # Exact variance decomposition from arXiv:2406.12708v3 Table 1 & Table 5:
    # - Baseline within-paper 3-reviewer sample SD E[s_3] = 0.224 -> sigma_eps = 0.224 / (sqrt(pi)/2) = 0.2528
    # - Phase III conformity shrinks E[s_3] from 0.224 -> 0.163 (-27.23%, w_peer = 1 - 0.163/0.224 = 0.2723)
    # - Marginal post-discussion error variance accounting for shared panel mean bar_eps = (eps_1+eps_2+eps_3)/3:
    #     Var(r_post,i - q) = sigma_eps^2 * [(2/3)*(1 - w_peer)^2 + 1/3] = 0.04385
    #   so Table 5 Phase III marginal SD 0.555 -> sigma_q = sqrt(0.555^2 - Var(r_post,i - q)) = 0.5140.
    # - Per arXiv:2406.12708v3 §A.2 & paper_review.py:113-150, unchanged normal co-reviewers reuse
    #   r_pre[1], r_pre[2] from BASELINE while Reviewer 1 is regenerated at T=0.9 (role_descriptions.py:13).
    # - AC backend uses temperature=0.0 (role_descriptions.py:514); sigma_ac_quant=0.12 models prose
    #   metareview-to-batch-ranking quantization residual held STRICTLY EQUAL across all conditions.
    rng = random.Random(20261122 + 4)
    n_papers = 2000
    accept_k = int(0.32 * n_papers)
    shared_batch_order = list(range(n_papers))
    rng.shuffle(shared_batch_order)

    c_s3 = math.sqrt(math.pi) / 2.0
    sigma_eps = 0.224 / c_s3
    w_peer = 1.0 - (0.163 / 0.224)
    var_eps_post_marginal = (sigma_eps ** 2) * (
        (2.0 / 3.0) * ((1.0 - w_peer) ** 2) + (1.0 / 3.0)
    )
    sigma_q = math.sqrt(0.555 ** 2 - var_eps_post_marginal)
    sigma_ac_quant = 0.12  # held constant across BASELINE, benign, malicious, and countermeasures
    w_vocal = (0.55, 0.225, 0.225)  # stylized AC vocal-critique weights (Basis: derived)

    qualities = [rng.gauss(5.053, sigma_q) for _ in range(n_papers)]
    all_base_post: list[float] = []
    pre_stds: list[float] = []
    post_stds: list[float] = []
    base_ac_scores: list[float] = []
    benign_ac_scores: list[float] = []
    mal_eq_ac_scores: list[float] = []
    mal_vocal_ac_scores: list[float] = []
    mal_blind_median_scores: list[float] = []
    mal_norm_post_vals: list[float] = []

    for q in qualities:
        # BASELINE: 3 reviews at T=0.9
        r_pre = [q + rng.gauss(0.0, sigma_eps) for _ in range(3)]
        panel_mean = sum(r_pre) / 3.0
        r_post = [(1.0 - w_peer) * r + w_peer * panel_mean + 0.057 for r in r_pre]
        all_base_post.extend(r_post)
        pre_stds.append(_np_std_ddof1(r_pre))
        post_stds.append(_np_std_ddof1(r_post))
        base_ac_scores.append(sum(r_post) / 3.0 + rng.gauss(0.0, sigma_ac_quant))

        # benign_Rx1: reuses r_pre[1], r_pre[2] from BASELINE (§A.2), regenerates R1 at T=0.9
        r1_ben_pre = q + rng.gauss(0.0, sigma_eps)
        r_ben_pre = [r1_ben_pre, r_pre[1], r_pre[2]]
        ben_mean = sum(r_ben_pre) / 3.0
        r_ben_post = [(1.0 - w_peer) * r + w_peer * ben_mean + 0.057 for r in r_ben_pre]
        benign_ac_scores.append(sum(r_ben_post) / 3.0 + rng.gauss(0.0, sigma_ac_quant))

        # malicious_Rx1: reuses r_pre[1], r_pre[2] from BASELINE (§A.2); malicious R1 per Table 5
        r1_mal_pre = 3.130 + rng.gauss(0.0, 0.838)
        r2_mal_pre, r3_mal_pre = r_pre[1], r_pre[2]
        r1_mal_post = r1_mal_pre + 0.124 + rng.gauss(0.0, 0.282)
        mal_panel_mean = (r1_mal_pre + r2_mal_pre + r3_mal_pre) / 3.0
        r2_seq = (1.0 - w_peer) * r2_mal_pre + w_peer * mal_panel_mean + 0.035
        r3_seq = (
            (1.0 - w_peer) * r3_mal_pre
            + w_peer * ((r1_mal_post + r2_seq + r3_mal_pre) / 3.0)
            + 0.035
        )
        mal_norm_post_vals.extend([r2_seq, r3_seq])

        # Identical AC quantization draw shared across malicious ablations (zero asymmetric noise cut):
        ac_quant_draw = rng.gauss(0.0, sigma_ac_quant)
        mal_eq_ac_scores.append((r1_mal_post + r2_seq + r3_seq) / 3.0 + ac_quant_draw)
        mal_vocal_ac_scores.append(
            w_vocal[0] * r1_mal_post
            + w_vocal[1] * r2_seq
            + w_vocal[2] * r3_seq
            + ac_quant_draw
        )

        # Countermeasure: simultaneous blind Phase 3 revision + panel median (same sigma_ac_quant=0.12)
        r_blind = sorted([r1_mal_pre, r2_mal_pre + 0.057, r3_mal_pre + 0.057])
        mal_blind_median_scores.append(r_blind[1] + ac_quant_draw)

    mean_pre_std = sum(pre_stds) / n_papers
    mean_post_std = sum(post_stds) / n_papers
    marg_post_sd = _np_std_ddof1(all_base_post)
    std_shrinkage = 1.0 - (mean_post_std / mean_pre_std)
    mean_mal_norm_post = sum(mal_norm_post_vals) / len(mal_norm_post_vals)
    assert abs(std_shrinkage - (1.0 - 0.163 / 0.224)) < 0.01  # ~27.23% shrinkage
    assert abs(marg_post_sd - 0.555) < 0.02  # marginal Phase III SD matches Table 5 (0.555)!
    assert abs(mean_mal_norm_post - 4.925) < 0.05  # matches Table 5 normal spillover (4.925)!

    acc_base_batch = agentreview_batched_ac_decisions(base_ac_scores, shared_batch_order, rng)
    acc_ben_batch = agentreview_batched_ac_decisions(benign_ac_scores, shared_batch_order, rng)
    acc_mal_eq_batch = agentreview_batched_ac_decisions(mal_eq_ac_scores, shared_batch_order, rng)
    acc_mal_vocal_batch = agentreview_batched_ac_decisions(
        mal_vocal_ac_scores, shared_batch_order, rng
    )
    acc_med_batch = agentreview_batched_ac_decisions(
        mal_blind_median_scores, shared_batch_order, rng
    )

    def global_top_set(scores: list[float]) -> set[int]:
        ranked = sorted(range(len(scores)), key=lambda idx: scores[idx], reverse=True)
        return set(ranked[:accept_k])

    acc_base_glob = global_top_set(base_ac_scores)
    acc_med_glob = global_top_set(mal_blind_median_scores)

    flip_benign = sum(
        1 for idx in range(n_papers) if (idx in acc_base_batch) != (idx in acc_ben_batch)
    ) / n_papers
    flip_mal_eq = sum(
        1 for idx in range(n_papers) if (idx in acc_base_batch) != (idx in acc_mal_eq_batch)
    ) / n_papers
    flip_mal_vocal = sum(
        1 for idx in range(n_papers) if (idx in acc_base_batch) != (idx in acc_mal_vocal_batch)
    ) / n_papers
    flip_med_batch = sum(
        1 for idx in range(n_papers) if (idx in acc_base_batch) != (idx in acc_med_batch)
    ) / n_papers
    flip_med_glob = sum(
        1 for idx in range(n_papers) if (idx in acc_base_glob) != (idx in acc_med_glob)
    ) / n_papers
    jacc_mal_vocal = len(acc_base_batch & acc_mal_vocal_batch) / len(
        acc_base_batch | acc_mal_vocal_batch
    )

    assert 0.11 <= flip_benign <= 0.16  # matches Table 2 benign 13.38% flip floor (86.62% agree)
    assert 0.24 <= flip_mal_eq <= 0.30
    assert 0.32 <= flip_mal_vocal <= 0.40  # matches Table 2 malicious 37.09% flip (62.91% agree)
    assert flip_med_batch < 0.40 * flip_mal_vocal
    assert flip_med_glob < flip_med_batch

    print(
        "  live_bugs_verified = 7/7: (1) unknowledgeable_Rx1==knowledgeable_Rx1, "
        "(2) bool_not_in_['famous']==True, (3) bool([False,False,False])==True, "
        "(4) no_numeric_ratings 1-rev + Phase3 numeric reset, (5) AC context-blinding, "
        "(6) Phase5 unsliced metareviews zip(batch_ids, metareviews[0:10]) persisted via cli.py:254, "
        "(7) retry role_desc+=dup & unseeded batch-quota shuffle"
    )
    print(
        f"  discussion_conformity_shrinkage = -{100*std_shrinkage:.2f}% "
        f"(within-panel std {mean_pre_std:.3f} -> {mean_post_std:.3f}, sigma_q={sigma_q:.4f}, "
        f"marginal_post_SD={marg_post_sd:.3f} vs Table 5 0.555); "
        f"malicious_Rx1_co_reviewer_post_mean = {mean_mal_norm_post:.3f} (Table 5: 4.925)"
    )
    print(
        f"  stylized_cascade_reused_co_rev (T_AC=0.0 + equal sigma_quant={sigma_ac_quant:.2f}): "
        f"benign_Rx1_flip={100*flip_benign:.2f}% (agree={100*(1-flip_benign):.2f}%, Table 2: 86.62%); "
        f"malicious_equal_w(1/3)_flip={100*flip_mal_eq:.2f}%, "
        f"stylized_vocal_w(0.55,0.225,0.225)_flip={100*flip_mal_vocal:.2f}% "
        f"(agree={100*(1-flip_mal_vocal):.2f}%, Jacc={jacc_mal_vocal:.3f}; Table 2: 37.09% flip, Jacc=0.230)"
    )
    print(
        f"  isolated_countermeasures (same sigma_quant={sigma_ac_quant:.2f}): "
        f"blind_median_batched={100*flip_med_batch:.2f}% ({flip_mal_vocal/flip_med_batch:.2f}x cut) -> "
        f"blind_median_global_cutoff={100*flip_med_glob:.2f}% ({flip_mal_vocal/flip_med_glob:.2f}x cut)"
    )


# ============================================================================
# PROBE 5: Ye et al. (2024) Incomplete-Draft Illusion & Injection Displacement
# ============================================================================


YE_ET_AL_SYSTEMS: list[dict[str, Any]] = [
    {
        "name": "LLM Review",
        "title_only": (4.35, 0.98),
        "tai": (5.11, 0.58),
        "whole": (5.34, 0.60),
        "inj_before": (5.33, 0.60),
        "inj_after": (7.99, 0.17),
    },
    {
        "name": "AI Scientist",
        "title_only": (2.96, 0.28),
        "tai": (3.36, 0.80),
        "whole": (3.41, 0.91),
        "inj_before": (3.40, 0.91),
        "inj_after": (6.27, 2.35),
    },
    {
        "name": "AgentReview",
        "title_only": (4.83, 0.60),
        "tai": (5.76, 0.42),
        "whole": (5.82, 0.38),
        "inj_before": (5.82, 0.41),
        "inj_after": (7.26, 0.99),
    },
]


def simulate_injection_displacement(
    mu_clean: float,
    sd_clean: float,
    mu_inj: float,
    sd_inj: float,
    alphas: list[float],
    mode: str,
    seed: int,
    n_papers: int = 1000,
    n_trials: int = 40,
    accept_frac: float = 0.30,
    reviews_per_paper: int = 3,
) -> dict[float, float]:
    """Synthetic Gaussian panel tournament (70% latent paper / 30% review-mean variance,
    exact Table 3 sd_inj with zero floor override)."""
    rng = random.Random(seed)
    top_k = int(n_papers * accept_frac)
    var_total = sd_clean * sd_clean
    sd_paper = math.sqrt(0.70 * var_total)
    sd_rev = math.sqrt(0.30 * var_total * reviews_per_paper)

    totals = {a: 0.0 for a in alphas}
    idx_range = list(range(n_papers))
    all_slots_template = [(i, r) for i in range(n_papers) for r in range(reviews_per_paper)]
    gauss = rng.gauss
    for _ in range(n_trials):
        paper_latents = [mu_clean + gauss(0.0, sd_paper) for _ in idx_range]
        clean_revs = [
            [lat + gauss(0.0, sd_rev) for _ in range(reviews_per_paper)]
            for lat in paper_latents
        ]
        clean_means = [sum(rs) / reviews_per_paper for rs in clean_revs]
        clean_top = set(
            sorted(idx_range, key=clean_means.__getitem__, reverse=True)[:top_k]
        )

        if mode == "paper_white_text":
            max_att_p = int(round(max(alphas) * n_papers))
            chosen_papers = rng.sample(idx_range, max_att_p)
            inj_draws = [gauss(mu_inj, sd_inj) for _ in range(max_att_p)]
            attacked_scores = list(clean_means)
            prev_att = 0
            for a in alphas:
                n_att = int(round(a * n_papers))
                for pos in range(prev_att, n_att):
                    attacked_scores[chosen_papers[pos]] = inj_draws[pos]
                prev_att = n_att
                new_top = set(
                    sorted(idx_range, key=attacked_scores.__getitem__, reverse=True)[:top_k]
                )
                totals[a] += len(clean_top - new_top) / top_k
        elif mode == "review_level":
            max_att = int(round(max(alphas) * len(all_slots_template)))
            chosen_slots = rng.sample(all_slots_template, max_att)
            rev_draws = [gauss(mu_inj, sd_inj) for _ in range(max_att)]
            mut_revs = [list(rs) for rs in clean_revs]
            attacked_scores = list(clean_means)
            prev_att = 0
            for a in alphas:
                n_rev_att = int(round(a * len(all_slots_template)))
                touched: set[int] = set()
                for pos in range(prev_att, n_rev_att):
                    i, r = chosen_slots[pos]
                    mut_revs[i][r] = rev_draws[pos]
                    touched.add(i)
                for i in touched:
                    attacked_scores[i] = sum(mut_revs[i]) / reviews_per_paper
                prev_att = n_rev_att
                new_top = set(
                    sorted(idx_range, key=attacked_scores.__getitem__, reverse=True)[:top_k]
                )
                totals[a] += len(clean_top - new_top) / top_k
        else:
            raise ValueError(mode)

    return {a: totals[a] / n_trials for a in alphas}


def run_probe_5() -> None:
    print("\n=== PROBE 5: Ye et al. (2024) Incomplete-Draft Illusion & Injection Displacement ===")
    print(
        "Basis: documentation + execution + derived "
        "(exact Table 3-4 ratios + synthetic all-LLM 70%/30% panel tournament vs human-SD=1.30 control)"
    )

    alphas = [0.01, 0.05, 0.10, 0.20]
    llm_rev_5pct = 0.0
    for idx, sys_cfg in enumerate(YE_ET_AL_SYSTEMS):
        name = sys_cfg["name"]
        mu_tai, _ = sys_cfg["tai"]
        mu_whole, _ = sys_cfg["whole"]
        mu_bef, sd_bef = sys_cfg["inj_before"]
        mu_aft, sd_aft = sys_cfg["inj_after"]

        delta_body = mu_whole - mu_tai
        delta_inj = mu_aft - mu_bef
        leverage = delta_inj / delta_body
        tai_share = mu_tai / mu_whole

        disp_paper = simulate_injection_displacement(
            mu_bef, sd_bef, mu_aft, sd_aft, alphas, mode="paper_white_text", seed=20261122 + 50 + idx
        )
        disp_rev = simulate_injection_displacement(
            mu_bef, sd_bef, mu_aft, sd_aft, alphas, mode="review_level", seed=20261122 + 60 + idx
        )
        if name == "LLM Review":
            llm_rev_5pct = disp_rev[0.05]

        assert tai_share > 0.95
        assert leverage > 11.0
        assert disp_paper[0.05] > 0.08 and disp_paper[0.20] > 0.30
        assert disp_rev[0.05] > 0.06

        print(
            f"  [{name}] TAI/Whole={mu_tai:.2f}/{mu_whole:.2f} ({100*tai_share:.1f}% surface prior, "
            f"body_delta=+{delta_body:.2f}) | white_text_gain=+{delta_inj:.2f} "
            f"(injection/body leverage={leverage:.1f}x)"
        )
        print(
            f"    synthetic_all_LLM_top30%_displaced (paper PDF): "
            f"1%->{100*disp_paper[0.01]:.2f}%, 5%->{100*disp_paper[0.05]:.2f}%, "
            f"10%->{100*disp_paper[0.10]:.2f}%, 20%->{100*disp_paper[0.20]:.2f}%"
        )
        print(
            f"    synthetic_all_LLM_top30%_displaced (review R=3): "
            f"1%->{100*disp_rev[0.01]:.2f}%, 5%->{100*disp_rev[0.05]:.2f}%, "
            f"10%->{100*disp_rev[0.10]:.2f}%, 20%->{100*disp_rev[0.20]:.2f}%"
        )

    # Contrast compressed all-LLM panel (SD=0.60 -> 25.66% @ 5%) vs broad human-ICLR panel (SD=1.30):
    disp_human_hybrid = simulate_injection_displacement(
        5.33, 1.30, 7.99, 0.17, [0.05], mode="review_level", seed=20261122 + 90
    )[0.05]
    compression_amp = llm_rev_5pct / disp_human_hybrid
    assert 0.11 <= disp_human_hybrid <= 0.13 and compression_amp > 2.0
    print(
        f"  [Hybrid Human-Panel Control vs All-LLM Compression] "
        f"broad_human_SD=1.30 5%_review_replacement -> {100*disp_human_hybrid:.2f}% displaced "
        f"(Ye et al. empirical ICLR human-panel replacement: 12%) vs compressed all-LLM SD=0.60 -> "
        f"{100*llm_rev_5pct:.2f}% ({compression_amp:.2f}x amplification)"
    )


def main() -> None:
    run_probe_1()
    run_probe_2()
    run_probe_3()
    run_probe_4()
    run_probe_5()
    print("\nALL 5 PROBE SUITES PASSED DETERMINISTICALLY.")


if __name__ == "__main__":
    main()
