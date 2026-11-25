#!/usr/bin/env python3
"""Deterministic Python 3.10+ verification suite for Agent DX trade-offs.

All models and probes use pure Python standard library only.
Probes:
  1. Token-budgeted diagnostic formatting (middle elision vs. head truncation)
     and structured error recovery vs. blind retry loops.
  2. Warm LSP/MCP feedback loops vs. cold CLI batch runs (latency/turn
     crossover and PostToolUse context-bloat bounds).
  3. Progressive disclosure token economics (upfront flat tool schemas vs.
     3-tier Agent Skills / deferred Tool Search) and benign vs. risky
     `.cargo/config.toml` ambient-configuration classification.
  4. Anti-reward-hacking incentive-gradient model (friction-driven cheating vs.
     Step-0 triage + escalation hatch + tainted prototyping + out-of-band locks).
"""

from __future__ import annotations

import json
import re
import sys
from typing import Any

try:
    import tomllib  # Python 3.11+
except ModuleNotFoundError:  # Python 3.10 fallback
    tomllib = None  # type: ignore[assignment]


# ---------------------------------------------------------------------------
# Probe 1: Diagnostic Budgeting & Recovery Markov Chain
# ---------------------------------------------------------------------------

def bound_output_middle(text: str, limit: int = 6000) -> str:
    """Middle-elision budgeter modeled on oOo0oOo/lean-lsp-mcp bound_output.

    Preserves 2/3 head (error header / early context) and 1/3 tail (Lean goal
    target `⊢ ...` or closing 3-tier verification verdict).
    """
    if limit <= 0 or len(text) <= limit:
        return text
    elided = len(text) - limit
    head = (limit * 2) // 3
    tail = limit - head
    notice = f"\n\n[... {elided} characters elided ...]\n\n"
    candidate = f"{text[:head]}{notice}{text[-tail:]}"
    return candidate if len(candidate) < len(text) else text


def head_only_truncate(text: str, limit: int = 2000) -> str:
    """Head-only preview modeled on harness overflow (e.g. Claude Code >10K cap)."""
    if len(text) <= limit:
        return text
    return text[:limit] + "\n...[truncated]..."


def classify_lean_diagnostic(full_message: str) -> dict[str, Any]:
    """Classify and attach hints on the *untruncated* message before eliding."""
    hint = None
    if "failed to synthesize instance of type class\n  DecidableEq " in full_message:
        hint = "add `classical` locally or supply DecidableEq"
    category = "sorry" if "declaration uses 'sorry'" in full_message else "diagnostic"
    return {"category": category, "hint": hint}


def expected_recovery_turns(
    p_recover_fixable: float,
    p_stop_unfixable: float,
    p_fixable_prior: float = 0.70,
    max_turns: int = 8,
) -> dict[str, float]:
    """Exact absorbing finite-horizon expectation over diagnostic recovery regimes.

    On a fixable failure (prob p_fixable_prior), each turn resolves with prob
    p_recover_fixable. On an unfixable/unsupported boundary (1 - p_fixable_prior),
    each turn cleanly aborts/escalates with prob p_stop_unfixable; otherwise the
    agent burns turns in futile retries up to max_turns.
    """
    # Fixable branch: geometric truncated at max_turns
    e_fix = 0.0
    p_resolve = 0.0
    rem = 1.0
    for _t in range(1, max_turns + 1):
        e_fix += rem
        step_ok = rem * p_recover_fixable
        p_resolve += step_ok
        rem -= step_ok

    # Unfixable branch: turns burned before recognizing non-retryable boundary
    e_unfix = 0.0
    p_clean_abort = 0.0
    rem_u = 1.0
    for _t in range(1, max_turns + 1):
        e_unfix += rem_u
        step_stop = rem_u * p_stop_unfixable
        p_clean_abort += step_stop
        rem_u -= step_stop

    total_turns = p_fixable_prior * e_fix + (1.0 - p_fixable_prior) * e_unfix
    wasted_unfix_turns = (1.0 - p_fixable_prior) * e_unfix
    return {
        "fixable_resolve_rate": round(p_resolve, 4),
        "unfixable_abort_rate": round(p_clean_abort, 4),
        "expected_turns": round(total_turns, 4),
        "wasted_turns_on_unfixable": round(wasted_unfix_turns, 4),
    }


def run_probe_1() -> dict[str, Any]:
    # 1a: Goal/verdict survival under 12,000-char Lean goal exceeding 10K hook cap
    target_line = "\n⊢ PureLift.memSafe state ∧ retVal = 0#u64"
    verdict_line = "\nFINAL VERDICT: TAINTED (sorry_in_proof; 1 of 4 items verified)"
    bloated_goal = (
        "failed to synthesize instance of type class\n  DecidableEq Expr\n"
        + ("h_ctx : Prop := by_padding_line_with_long_hypothesis_term\n" * 210)
        + target_line
        + verdict_line
    )
    assert len(bloated_goal) > 10_000

    # Naive PostToolUse hook (>10K chars -> harness replaces with 2000-char head)
    harness_head = head_only_truncate(bloated_goal, 2000)
    assert "⊢ PureLift.memSafe" not in harness_head
    assert "TAINTED" not in harness_head

    # Pre-classification + middle elision within 6000-char budget (<10K cap)
    meta = classify_lean_diagnostic(bloated_goal)
    bounded = bound_output_middle(bloated_goal, limit=6000)
    assert len(bounded) <= 6100 < 10_000
    assert meta["hint"] == "add `classical` locally or supply DecidableEq"
    assert "⊢ PureLift.memSafe" in bounded
    assert "TAINTED" in bounded

    # Distinct diagnostics whose middle differs must not collapse identity
    d1 = "E_PROOF_STEP: context " + ("A" * 400) + " missing lemma foo_bar " + ("Z" * 400)
    d2 = "E_PROOF_STEP: context " + ("A" * 400) + " missing lemma baz_qux " + ("Z" * 400)
    assert bound_output_middle(d1, 200) == bound_output_middle(d2, 200)
    # Deduplicating on untruncated strings keeps both!
    dedup_untruncated = len({d1, d2})
    dedup_truncated = len({bound_output_middle(d1, 200), bound_output_middle(d2, 200)})
    assert dedup_untruncated == 2 and dedup_truncated == 1

    # 1b: Recovery regimes
    opaque = expected_recovery_turns(p_recover_fixable=0.25, p_stop_unfixable=0.10)
    coded = expected_recovery_turns(p_recover_fixable=0.55, p_stop_unfixable=0.50)
    structured_action = expected_recovery_turns(p_recover_fixable=0.80, p_stop_unfixable=1.00)
    assert structured_action["fixable_resolve_rate"] > coded["fixable_resolve_rate"] > opaque["fixable_resolve_rate"]
    assert structured_action["expected_turns"] < coded["expected_turns"] < opaque["expected_turns"]
    assert structured_action["wasted_turns_on_unfixable"] == 0.30  # 0.30 * 1 turn to observe retryable=false

    return {
        "bloated_goal_chars": len(bloated_goal),
        "harness_head_target_survived": False,
        "middle_elision_chars": len(bounded),
        "middle_elision_target_survived": True,
        "dedup_loss_if_post_truncation": {"untruncated": dedup_untruncated, "post_truncation": dedup_truncated},
        "recovery_regimes": {
            "opaque_exit_1": opaque,
            "coded_span_only": coded,
            "structured_next_action_retryable": structured_action,
        },
    }


# ---------------------------------------------------------------------------
# Probe 2: Warm LSP/MCP vs. Cold CLI Batch Crossover Model
# ---------------------------------------------------------------------------

def evaluate_feedback_strategies(
    d_steps: int,
    p_step: float,
    l_cold: float,
    l_warm: float,
    l_turn: float = 4.0,
    k_multi_attempt: int = 4,
    context_tokens_base: int = 8000,
    tokens_per_step_ctx: int = 1200,
) -> dict[str, dict[str, float]]:
    """Compare wall-clock and token economics across 4 verification feedback modes.

    Assumes a proof of d_steps sequential tactics where each single-shot tactic
    succeeds with probability p_step (requiring geometric expected attempts
    1/p_step in sequential repair, or batched k_multi_attempt probing in 1 turn).
    - cold_cli_per_step: every step triggers a full cold CLI verification.
    - warm_lsp_step: persistent LSP worker checks each step incrementally.
    - warm_lsp_multi_attempt: batches up to k candidate tactics per turn on
      uncertain steps, hitting with prob 1 - (1 - p_step)^k per turn.
    - whole_proof_plus_cold: writes all d_steps in 1 turn, then repairs failing
      block once per failed attempt with cold CLI verification.
    """
    # Sequential per-step attempts
    exp_attempts_seq = 1.0 / p_step
    total_seq_calls = d_steps * exp_attempts_seq

    # Strategy A: Cold CLI per step
    cold_wall = total_seq_calls * (l_turn + l_cold)
    cold_input_tokens = sum(context_tokens_base + i * tokens_per_step_ctx for i in range(int(round(total_seq_calls))))

    # Strategy B: Warm LSP per step
    warm_wall = total_seq_calls * (l_turn + l_warm)
    warm_input_tokens = cold_input_tokens

    # Strategy C: Warm LSP + batched multi_attempt(K) per step
    p_batch_hit = 1.0 - (1.0 - p_step) ** k_multi_attempt
    exp_turns_multi = d_steps * (1.0 / p_batch_hit)
    multi_wall = exp_turns_multi * (l_turn + k_multi_attempt * l_warm * 0.4)  # shared prefix in REPL/scratch pool
    multi_input_tokens = sum(context_tokens_base + i * tokens_per_step_ctx for i in range(int(round(exp_turns_multi))))

    # Strategy D: Whole-proof generation + cold CLI repair
    # Whole-proof succeeds on first try with p_step^d_steps; expected repair turns
    # modeled as 1 + failing steps if repair has p_repair = p_step^(max(1, d_steps/4))
    p_whole_first = p_step ** d_steps
    exp_whole_turns = 1.0 + (1.0 - p_whole_first) * max(1.0, (1.0 - p_step) * d_steps / p_step)
    whole_wall = exp_whole_turns * (l_turn + l_cold)
    whole_input_tokens = sum(context_tokens_base + i * tokens_per_step_ctx for i in range(max(1, int(round(exp_whole_turns)))))

    return {
        "cold_cli_per_step": {"turns": round(total_seq_calls, 2), "wall_s": round(cold_wall, 1), "input_tok": cold_input_tokens},
        "warm_lsp_step": {"turns": round(total_seq_calls, 2), "wall_s": round(warm_wall, 1), "input_tok": warm_input_tokens},
        "warm_lsp_multi_attempt": {"turns": round(exp_turns_multi, 2), "wall_s": round(multi_wall, 1), "input_tok": multi_input_tokens},
        "whole_proof_cold_cli": {"turns": round(exp_whole_turns, 2), "wall_s": round(whole_wall, 1), "input_tok": whole_input_tokens},
    }


def run_probe_2() -> dict[str, Any]:
    # Regime 1: Shallow straightforward proof (d=4, p_step=0.85, fast cold check 8s)
    shallow = evaluate_feedback_strategies(d_steps=4, p_step=0.85, l_cold=8.0, l_warm=0.4)
    # Whole-proof + cold check beats step-by-step LSP on both wall time and tokens!
    assert shallow["whole_proof_cold_cli"]["wall_s"] < shallow["warm_lsp_step"]["wall_s"]
    assert shallow["whole_proof_cold_cli"]["input_tok"] < shallow["warm_lsp_step"]["input_tok"]

    # Regime 2: Deep uncertain tactical proof (d=16, p_step=0.45, slow cold rebuild 45s)
    deep = evaluate_feedback_strategies(d_steps=16, p_step=0.45, l_cold=45.0, l_warm=0.5)
    # Warm LSP + multi_attempt crushes both cold per-step and sequential warm LSP
    assert deep["warm_lsp_multi_attempt"]["wall_s"] < deep["warm_lsp_step"]["wall_s"]
    assert deep["warm_lsp_multi_attempt"]["wall_s"] < deep["cold_cli_per_step"]["wall_s"]
    assert deep["warm_lsp_multi_attempt"]["input_tok"] < deep["warm_lsp_step"]["input_tok"]

    # Crossover calculation: ratio of cold_cli_per_step wall_s to warm_lsp_multi_attempt wall_s
    speedup = round(deep["cold_cli_per_step"]["wall_s"] / deep["warm_lsp_multi_attempt"]["wall_s"], 2)
    assert speedup > 10.0

    return {
        "shallow_d4_p085_lcold8": shallow,
        "deep_d16_p045_lcold45": deep,
        "deep_cold_to_multi_wall_speedup": speedup,
    }


# ---------------------------------------------------------------------------
# Probe 3: Progressive Disclosure & Ambient `.cargo/config.toml` Classification
# ---------------------------------------------------------------------------

# Cargo config top-level tables per Cargo Reference (doc.rust-lang.org/cargo/reference/config.html)
# Strictly presentation/CLI-alias tables that cannot alter rustc flags, env,
# dependency resolution, profiles, or network/registry behavior.
BENIGN_CARGO_TABLES = frozenset({"alias", "term", "doc", "cargo-new", "future-incompat-report"})


def _extract_toml_top_keys_fallback(toml_text: str) -> tuple[set[str], bool]:
    """Fail-closed Python 3.10 fallback when stdlib tomllib is unavailable."""
    sections: set[str] = set()
    current_table: str | None = None
    for raw_line in toml_text.splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        if '"""' in line or "'''" in line or "{" in line:
            return set(), True
        if line.startswith("["):
            m = re.match(r"^\[{1,2}\s*([A-Za-z0-9_\"'.-]+)\s*\]{1,2}\s*(?:#.*)?$", line)
            if not m:
                return set(), True
            header = m.group(1).strip().strip('"').strip("'")
            top = header.split(".", 1)[0].strip().strip('"').strip("'")
            sections.add(top)
            current_table = top
        elif "=" in line:
            lhs = line.split("=", 1)[0].strip().strip('"').strip("'")
            if current_table is None:
                sections.add(lhs.split(".", 1)[0].strip().strip('"').strip("'"))
            else:
                sections.add(current_table)
        else:
            return set(), True
    return sections, False


def classify_cargo_config(toml_text: str, is_symlink: bool = False) -> tuple[str, list[str]]:
    """Classify `.cargo/config.toml` into ('allow_benign', keys) vs ('reject', reasons)."""
    if is_symlink:
        return "reject", ["symlink_forbidden"]
    if tomllib is not None:
        try:
            parsed = tomllib.loads(toml_text)
        except tomllib.TOMLDecodeError:
            return "reject", ["unparseable_toml_fail_closed"]
        sections = set(parsed.keys())
    else:
        sections, parse_err = _extract_toml_top_keys_fallback(toml_text)
        if parse_err:
            return "reject", ["unparseable_toml_fail_closed"]
    disallowed = sorted(sec for sec in sections if sec not in BENIGN_CARGO_TABLES)
    if disallowed:
        return "reject", [f"compilation_or_resolution_table:{s}" for s in disallowed]
    return "allow_benign", sorted(sections)


def run_probe_3() -> dict[str, Any]:
    # 3a: Progressive disclosure token budgets (grounded in Anthropic 58-tool 55K-token baseline)
    avg_tokens_per_tool = 55_000 / 58  # ~948.3 tok/tool
    flat_58 = round(58 * avg_tokens_per_tool)
    flat_200 = round(200 * avg_tokens_per_tool)
    # Tool Search Tool: ~500 tok index + 4 expanded tools
    deferred_58 = round(500 + 4 * avg_tokens_per_tool)
    # Agent Skills 3-tier: 20 skills * 100 tok frontmatter + 2 activated * 2500 tok
    skills_20_active_2 = 20 * 100 + 2 * 2500

    # 3b: Ambient `.cargo/config.toml` cases
    cases = {
        "alias_term_doc_only": (
            '[alias]\nxtask = "run --package xtask"\n[term]\ncolor = "auto"\n[doc]\nbrowser = "xdg-open"\n',
            False,
            "allow_benign",
        ),
        "build_rustflags": ('[build]\nrustflags = ["-C", "target-cpu=native"]\n', False, "reject"),
        "target_cfg_rustflags": ('[target.\'cfg(all())\']\nrustflags = ["--cfg", "custom"]\n', False, "reject"),
        "target_linker": ('[target.x86_64-unknown-linux-gnu]\nlinker = "clang"\n', False, "reject"),
        "env_override": ('[env]\nMY_CONST = "override"\n', False, "reject"),
        "patch_crates_io": ('[patch.crates-io]\nfoo = { path = "../foo" }\n', False, "reject"),
        "net_override": ('[net]\ngit-fetch-with-cli = true\n', False, "reject"),
        "symlink_config": ('[alias]\nx = "check"\n', True, "reject"),
        "inline_dotted_build": ('build.rustc-wrapper = "sccache"\n', False, "reject"),
    }
    cargo_results = {}
    for name, (txt, sym, expected) in cases.items():
        verdict, detail = classify_cargo_config(txt, is_symlink=sym)
        assert verdict == expected, f"{name}: got {verdict} ({detail}), expected {expected}"
        cargo_results[name] = {"verdict": verdict, "detail": detail}

    return {
        "context_tokens": {
            "flat_58_tools": flat_58,
            "deferred_58_tools_4_active": deferred_58,
            "savings_pct_58": round(100.0 * (1.0 - deferred_58 / flat_58), 1),
            "flat_200_tools": flat_200,
            "skills_20_catalog_2_active": skills_20_active_2,
        },
        "ambient_cargo_config": cargo_results,
    }


# ---------------------------------------------------------------------------
# Probe 4: Incentive-Gradient Model for Anti-Reward-Hacking DX
# ---------------------------------------------------------------------------

def incentive_comparison(
    p_legit_succeeds: float,
    cheat_detection_prob: float,
    honest_step_cost: float,
    cheat_step_cost: float,
    reward_pass: float = 1.0,
    penalty_caught: float = -1.0,
    reward_clean_escalate: float = 0.0,
) -> dict[str, Any]:
    """Compare expected utility of honest resolution vs. cheating vs. escalation.

    Models why friction drives shortcutting when p_legit_succeeds is low or
    honest_step_cost >> cheat_step_cost, vs. how trust-preserving DX restores
    U(honest/escalate) > U(cheat).
    """
    u_honest = p_legit_succeeds * reward_pass - honest_step_cost
    u_cheat = (1.0 - cheat_detection_prob) * reward_pass + cheat_detection_prob * penalty_caught - cheat_step_cost
    u_escalate = reward_clean_escalate - 0.05  # cheap single-turn diagnostic escalation
    return {
        "u_honest": round(u_honest, 3),
        "u_cheat": round(u_cheat, 3),
        "u_escalate": round(u_escalate, 3),
        "cheat_beats_honest": u_cheat > u_honest,
        "cheat_beats_best_legit": u_cheat > max(u_honest, u_escalate),
    }


def run_probe_4() -> dict[str, Any]:
    # Naive DX: hard proof without automation/Step-0 triage (p=0.25, high effort 0.45),
    # mutable local tests/spec (detection=0.10), no clean escalation option.
    naive_hard = incentive_comparison(p_legit_succeeds=0.25, cheat_detection_prob=0.10, honest_step_cost=0.45, cheat_step_cost=0.10)
    assert naive_hard["cheat_beats_honest"] is True

    # Impossible/buggy Rust target without Step-0 counterexample or escalation (p=0.0):
    naive_impossible = incentive_comparison(p_legit_succeeds=0.0, cheat_detection_prob=0.10, honest_step_cost=0.60, cheat_step_cost=0.10)
    assert naive_impossible["cheat_beats_honest"] is True

    # Trust-Preserving DX: built-in automation + `--allow-sorry-in-proof` lowers honest cost (0.15),
    # out-of-band Spec lock + NDJSON/closed-allowlist + MutationRefute raises cheat detection (0.95),
    # and Step-0 triage gives clean escalation (reward_clean_escalate=0.1, zero futile proof effort).
    trust_hard = incentive_comparison(
        p_legit_succeeds=0.75, cheat_detection_prob=0.95, honest_step_cost=0.15, cheat_step_cost=0.25, reward_clean_escalate=0.10
    )
    trust_impossible = incentive_comparison(
        p_legit_succeeds=0.0, cheat_detection_prob=0.95, honest_step_cost=0.10, cheat_step_cost=0.25, reward_clean_escalate=0.10
    )
    assert trust_hard["cheat_beats_best_legit"] is False
    assert trust_impossible["cheat_beats_best_legit"] is False

    return {
        "naive_hard_task": naive_hard,
        "naive_impossible_task": naive_impossible,
        "trust_dx_hard_task": trust_hard,
        "trust_dx_impossible_task": trust_impossible,
    }


def main() -> int:
    report = {
        "probe_1_diagnostics": run_probe_1(),
        "probe_2_lsp_vs_cli": run_probe_2(),
        "probe_3_disclosure_and_ambient_cargo": run_probe_3(),
        "probe_4_incentive_gradient": run_probe_4(),
    }
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
