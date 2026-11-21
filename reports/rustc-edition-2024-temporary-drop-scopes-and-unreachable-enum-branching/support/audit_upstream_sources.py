#!/usr/bin/env python3
"""Fetch the upstream files this report cites at their pinned revisions and
record, for every file, its git blob id, its line count and the 1-based line
numbers of the source lines the report relies on ("anchors").

Every line number quoted in REPORT.md comes from the manifest this script
writes. Rerun it with other revisions (edit `PINS`) to see which anchors
moved, vanished or multiplied.

    python3 audit_upstream_sources.py --out upstream_source_anchor_manifest.json

Files are fetched from https://raw.githubusercontent.com/<repo>/<revision>/<path>.
Standard library only (plus `curl` when it is on PATH); needs Python 3.10+ and
network access to GitHub.
"""

from __future__ import annotations

import argparse
import hashlib
import http.client
import json
import re
import shutil
import subprocess
import sys
import time
import urllib.request
from pathlib import Path

# Full commit ids, resolved through the GitHub commits API on 2026-11-21.
PINS = {
    "rust-lang/rust": [
        # rustc 1.98.0-nightly (2026-05-31): the toolchain executed by the probe
        "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65",
        # rustc 1.102.0-nightly (2026-11-11): toolchain of the retained receipt
        "3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1",
    ],
    "joshlf/anneal": ["c131b320eeeb26ef692e5afd5ec8db49ee518613"],
    "rust-lang/reference": ["c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c"],
    "rust-lang/rfcs": ["f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07"],
    "rust-lang/edition-guide": ["ab8544aeed7b792984366aa122ac19bd47ad9a2f"],
}

# (repository, path) -> {anchor id: (regex, expected match count or None)}.
# `None` means "at least one match"; an integer means "exactly that many".
ANCHORS: dict[tuple[str, str], dict[str, tuple[str, int | None]]] = {
    ("rust-lang/rust", "compiler/rustc_middle/src/middle/region.rs"): {
        "scope_data_enum": (r"^pub enum ScopeData \{", 1),
        "scope_data_destruction": (r"^    Destruction,$", 1),
        "scope_data_if_then": (r"^    IfThen,$", 1),
        "scope_data_if_then_rescope": (r"^    IfThenRescope,$", 1),
        "scope_data_match_guard": (r"^    MatchGuard,$", 1),
        "scope_data_remainder": (r"^    Remainder\(FirstStatementIndex\),$", 1),
        "tail_expr_anywhere_in_file": (r"TailExpr", 0),
        "backwards_incompatible_scope_field": (r"pub backwards_incompatible_scope:", 1),
        "default_temporary_scope_fn": (r"pub fn default_temporary_scope\(", 1),
        "default_temporary_scope_destruction_arm": (r"^                ScopeData::Destruction => \{$", 1),
        "default_temporary_scope_rescope_arm": (r"ScopeData::IfThenRescope \| ScopeData::MatchGuard => \{", 1),
        "default_temporary_scope_passthrough_if_then": (r"^                \| ScopeData::IfThen$", 1),
        "temporary_scope_fn": (r"pub fn temporary_scope\(", 1),
    },
    ("rust-lang/rust", "compiler/rustc_hir_analysis/src/check/region.rs"): {
        "resolve_block_fn": (r"^fn resolve_block<'tcx>\(", 1),
        "resolve_block_let_remainder": (r"data: ScopeData::Remainder\(FirstStatementIndex::new\(i\)\),", 2),
        "tail_terminating_from_edition": (r"let terminating = edition\.at_least_rust_2024\(\);", 1),
        "tail_backwards_incompatible_scope": (r"\.backwards_incompatible_scope$", 1),
        "tail_resolve_expr": (r"resolve_expr\(visitor, tail_expr, terminating\);", 1),
        "resolve_cond_fn": (r"^fn resolve_cond<'tcx>\(", 1),
        "let_condition_not_terminating": (r"hir::ExprKind::Let\(_\) => false,", 2),
        "resolve_arm_fn": (r"^fn resolve_arm<'tcx>\(", 1),
        "resolve_stmt_terminating": (r"visitor\.enter_node_scope_with_dtor\(stmt_id, true\);", 1),
        "resolve_expr_fn": (r"^fn resolve_expr<'tcx>\(", 1),
        "if_with_else_arm": (r"hir::ExprKind::If\(cond, then, Some\(otherwise\)\) => \{", 1),
        "if_then_rescope_choice": (r"^                ScopeData::IfThenRescope$", 2),
        "if_then_enter_scope": (r"visitor\.enter_scope\(Scope \{ local_id: then\.hir_id\.local_id, data \}\);", 2),
        # The single mention of `Match` is in the lifetime-extension helper
        # `record_rvalue_scope_if_borrow_expr`, not in `resolve_expr`.
        "match_mentions_in_file": (r"hir::ExprKind::Match", 1),
        "let_kind_enum_after_resolve_expr": (r"^enum LetKind \{$", 1),
        "walk_expr_fallthrough": (r"_ => intravisit::walk_expr\(visitor, expr\),", 1),
        "enter_node_scope_with_dtor_fn": (r"fn enter_node_scope_with_dtor\(", 1),
        "enter_destruction_scope": (r"self\.enter_scope\(Scope \{ local_id: id, data: ScopeData::Destruction \}\);", 1),
        "visit_expr_not_terminating": (r"resolve_expr\(self, ex, false\);", 1),
    },
    ("rust-lang/rust", "compiler/rustc_mir_build/src/thir/cx/expr.rs"): {
        "expr_scope_wrapper": (r"kind: ExprKind::Scope \{", None),
        "if_then_scope_field": (r"if_then_scope: region::Scope \{", 1),
        "if_then_rescope_choice": (r"region::ScopeData::IfThenRescope", 1),
        "match_mirror": (r"hir::ExprKind::Match\(discr, arms, match_source\) => ExprKind::Match \{", 1),
    },
    ("rust-lang/rust", "compiler/rustc_mir_build/src/thir/cx/block.rs"): {
        "mirror_block_fn": (r"pub\(crate\) fn mirror_block\(", 1),
        "remainder_scope": (r"data: region::ScopeData::Remainder\(region::FirstStatementIndex::new\(", 1),
    },
    ("rust-lang/rust", "compiler/rustc_mir_build/src/builder/block.rs"): {
        "ast_block_stmts_fn": (r"fn ast_block_stmts\(", 1),
        "let_scope_push": (r"let_scope_stack\.push\(remainder_scope\);", 2),
        "tail_expr_into_dest": (r"block = this\.expr_into_dest\(destination, block, expr_id\)\.into_block\(\);", 1),
        "let_scope_pop_reversed": (r"for scope in let_scope_stack\.into_iter\(\)\.rev\(\) \{", 1),
    },
    ("rust-lang/rust", "compiler/rustc_mir_build/src/builder/scope.rs"): {
        "in_if_then_scope_fn": (r"pub\(crate\) fn in_if_then_scope(<F>)?\(", 1),
        "in_scope_fn": (r"pub\(crate\) fn in_scope<F, R>\(", 1),
        "pop_scope_fn": (r"pub\(crate\) fn pop_scope\(", 1),
        # Renamed `break_from_if_then_scope` (and `scope_index` -> `stack_index`)
        # in the later revision.
        "break_for_else_fn": (r"pub\(crate\) fn (break_for_else|break_from_if_then_scope)\(", 1),
        "break_for_else_inner_scopes": (
            r"for scope in &self\.scopes\.scopes\[(scope|stack)_index \+ 1\.\.\] \{",
            None,
        ),
        "schedule_drop_region_match": (r"if scope\.region_scope == region_scope \{", None),
        "schedule_drop_push": (r"scope\.drops\.push\(DropData \{", None),
        "build_scope_drops_fn": (r"^fn build_scope_drops<'tcx, F>\(", 1),
        "build_scope_drops_reversed": (r"for drop_data in scope\.drops\.iter\(\)\.rev\(\) \{", None),
    },
    ("rust-lang/rust", "compiler/rustc_mir_build/src/builder/expr/as_temp.rs"): {
        "as_temp_fn": (r"pub\(crate\) fn as_temp\(", 1),
        "if_then_rescope_temp_info": (r"LocalInfo::IfThenRescopeTemp \{", 1),
        "schedule_value_drop": (
            r"this\.schedule_drop(_value)?\(expr_span, temp_lifetime, temp(, DropKind::Value)?\);",
            1,
        ),
        "schedule_backwards_incompatible_drop": (
            r"this\.schedule_backwards_incompatible_drop\(expr_span, backwards_incompatible, temp\);",
            1,
        ),
    },
    ("rust-lang/rust", "compiler/rustc_mir_build/src/builder/expr/category.rs"): {
        "deref_is_place": (r"^            \| ExprKind::Deref \{ \.\. \}$", 1),
        "place_category": (r"=> Some\(Category::Place\),", 1),
        "block_is_rvalue_into": (r"^            \| ExprKind::Block \{ \.\. \}$", 1),
    },
    ("rust-lang/rust", "compiler/rustc_mir_build/src/builder/expr/as_place.rs"): {
        "expr_as_place_fn": (r"^    fn expr_as_place\(", 1),
        "deref_arm": (r"^            ExprKind::Deref \{ arg \} => \{$", 1),
        "deref_projection": (r"block\.and\(place_builder\.deref\(\)\)", 1),
        "block_listed_as_non_place": (r"^            \| ExprKind::Block \{ \.\. \}$", 1),
        "non_places_need_temporary": (r"// these are not places, so we need to make a temporary\.", 1),
        "non_place_as_temp": (
            r"let temp = unpack!\(block = this\.as_temp\(block, temp_lifetime, expr_id, mutability\)\);",
            1,
        ),
    },
    ("rust-lang/rust", "compiler/rustc_mir_build/src/builder/expr/into.rs"): {
        "block_arm": (r"^            ExprKind::Block \{ block: ast_block \} => \{$", 1),
        "match_arm": (r"ExprKind::Match \{ scrutinee, ref arms, \.\. \} =>", 1),
        "if_arm": (r"ExprKind::If \{ cond, then, else_opt, if_then_scope \} => \{", 1),
        "condition_scope": (r"let condition_scope = this\.local_scope\(\);", 2),
        "in_if_then_scope_call": (r"this\.in_if_then_scope\(condition_scope, then_span, \|this\| \{", 1),
        "place_arm_deref": (r"ExprKind::Index \{ \.\. \} \| ExprKind::Deref \{ \.\. \} \| ExprKind::Field \{ \.\. \} => \{", 1),
        "place_consumed_by_copy_or_move": (r"Rvalue::Use\(this\.consume_by_copy_or_move\(place\)", 2),
    },
    ("rust-lang/rust", "compiler/rustc_mir_build/src/builder/misc.rs"): {
        "consume_by_copy_or_move_fn": (r"pub\(crate\) fn consume_by_copy_or_move\(", 1),
        "operand_copy": (r"Operand::Copy\(place\)", 1),
        "operand_move": (r"Operand::Move\(place\)", 1),
    },
    ("rust-lang/rust", "compiler/rustc_mir_build/src/builder/matches/mod.rs"): {
        "match_expr_fn": (r"pub\(crate\) fn match_expr\(", 1),
        "lower_scrutinee_fn": (r"pub\(crate\) fn lower_scrutinee\(", 1),
        "scrutinee_as_place_builder": (
            r"let scrutinee_place_builder = unpack!\(block = self\.as_place_builder\(block, scrutinee_id\)\);",
            1,
        ),
        # Renamed `lower_fallible_let` in the later revision.
        "lower_let_expr_fn": (r"pub\(crate\) fn (lower_let_expr|lower_fallible_let)\(", 1),
        "lower_scrutinee_calls": (r"unpack!\(block = self\.lower_scrutinee\(block, ", None),
        "let_expr_break_for_else": (
            r"self\.(break_for_else\(built_tree\.otherwise_block|break_from_if_then_scope\(false_block), self\.source_info\(",
            1,
        ),
    },
    ("rust-lang/rust", "compiler/rustc_borrowck/src/borrowck_errors.rs"): {
        "e0507": (r"^            E0507,$", 1),
    },
    ("rust-lang/rust", "compiler/rustc_lint/src/if_let_rescope.rs"): {
        "if_let_rescope_lint": (r"pub IF_LET_RESCOPE,", 1),
    },
    ("rust-lang/rust", "compiler/rustc_lint_defs/src/builtin.rs"): {
        "tail_expr_drop_order_lint": (r"pub TAIL_EXPR_DROP_ORDER,", 1),
    },
    ("rust-lang/rust", "compiler/rustc_mir_transform/src/unreachable_enum_branching.rs"): {
        "get_discriminant_local_fn": (r"^fn get_discriminant_local\(", 1),
        "switch_on_moved_local": (r"TerminatorKind::SwitchInt \{ discr: Operand::Move\(p\), \.\. \} = terminator", 1),
        "get_switched_on_type_fn": (r"^fn get_switched_on_type<'tcx>\(", 1),
        "statement_is_discriminant_read": (
            r"if let StatementKind::Assign\(\(l, Rvalue::Discriminant\(place\)\)\) = stmt_before_term\.kind",
            1,
        ),
        "variant_discriminants_fn": (r"^fn variant_discriminants<'tcx>\(", 1),
        "inhabited_variants_only": (r"\(!layout\.is_uninhabited\(\)\)", 1),
        "pass_enabled_at_mir_opt_level_1": (r"mir_opt_level\(\) (> 0|>= 1)", 1),
        "run_pass_fn": (r"fn run_pass\(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>\) \{", 1),
        "skip_cleanup_blocks": (r"if bb_data\.is_cleanup \{", 1),
        "remove_from_allowed": (r"if !allowed_variants\.remove\(&val\) \{", 1),
        "replace_otherwise_condition": (r"let replace_otherwise_to_unreachable = allowed_variants\.len\(\) <= 1", 1),
        "otherwise_not_already_unreachable": (
            r"&& !body\.basic_blocks\[targets\.otherwise\(\)\]\.is_empty_unreachable\(\);",
            1,
        ),
        "nothing_to_do_continue": (r"if unreachable_targets\.is_empty\(\) && !replace_otherwise_to_unreachable \{", 1),
        "unreachable_block": (r"let unreachable_block = patch\.unreachable_no_cleanup_block\(\);", 1),
        "add_target_last_variant": (r"targets\.add_target\(last_variant, targets\.otherwise\(\)\);", 1),
        "redirect_targets": (r"targets\.all_targets_mut\(\)\[\*index\] = unreachable_block;", 1),
        "patch_terminator": (r"patch\.patch_terminator\(bb, TerminatorKind::SwitchInt", 1),
    },
    ("rust-lang/rust", "compiler/rustc_mir_transform/src/lib.rs"): {
        "pass_in_pipeline": (r"&unreachable_enum_branching::UnreachableEnumBranching,", 1),
    },
    ("rust-lang/rust", "compiler/rustc_middle/src/mir/terminator.rs"): {
        "target_for_value_fn": (r"pub fn target_for_value\(&self, value: u128\) -> BasicBlock \{", 1),
        "add_target_fn": (r"pub fn add_target\(&mut self, value: u128, bb: BasicBlock\) \{", 1),
        "add_target_before_otherwise": (r"self\.targets\.insert\(self\.targets\.len\(\) - 1, bb\);", 1),
    },
    ("rust-lang/rust", "compiler/rustc_const_eval/src/interpret/discriminant.rs"): {
        "read_discriminant_fn": (r"pub fn read_discriminant\(", 1),
        "never_returns_uninhabited_doc": (r"/// Will never return an uninhabited variant\.", 1),
        "variants_empty_is_ub": (r"throw_ub!\(UninhabitedEnumVariantRead\(None\)\);", 1),
        "tag_outside_layout_range": (r"if !tag_scalar_layout\.valid_range\(self\)\.contains\(tag_bits\) \{", 2),
        "tag_matches_no_variant": (
            r"\.ok_or_else\(\|\| err_ub!\(InvalidTag\(Scalar::from_uint\(tag_bits, tag_layout\.size\)\)\)\)\?;",
            1,
        ),
        "basis_for_pass_comment": (
            r"// Reading the discriminant of an uninhabited variant is UB\. This is the basis for the",
            1,
        ),
        "uninhabited_variant_check": (
            r"if op\.layout\(\)\.(for_variant\(self, index\)\.is_uninhabited\(\)|is_variant_uninhabited\(index\)) \{",
            1,
        ),
        "uninhabited_variant_is_ub": (r"throw_ub!\(UninhabitedEnumVariantRead\(Some\(index\)\)\)$", 1),
    },
    ("rust-lang/rust", "compiler/rustc_const_eval/src/interpret/step.rs"): {
        "rvalue_discriminant_arm": (r"^            Discriminant\(place\) => \{$", 1),
        "calls_read_discriminant": (r"let variant = self\.read_discriminant\(&op\)\?;", 1),
    },
    ("rust-lang/rust", "compiler/rustc_middle/src/mir/syntax.rs"): {
        "rvalue_discriminant_variant": (r"^    Discriminant\(Place<'tcx>\),$", 1),
        "validity_undecided_doc": (
            r"/// The validity requirements for the underlying value are undecided for this rvalue, see",
            1,
        ),
    },
    ("rust-lang/rust", "compiler/rustc_middle/src/mir/interpret/error.rs"): {
        "ub_variant": (r"UninhabitedEnumVariantRead\(Option<VariantIdx>\),", 1),
        "ub_message": (r'write!\(f, "read discriminant of an uninhabited enum variant"\)', 1),
    },
    ("joshlf/anneal", "trusted/lean/Trusted/MirSemantics.lean"): {
        "eval_rvalue_def": (r"^noncomputable def evalRvalue ", 1),
        "discriminant_arm": (r"^  \| \.discriminant place =>$", 1),
        "uninit_tag_is_undefined": (r"\| \.scalar _ _, \.live none => \.error \.undefined", 1),
        "find_discr_variant_def": (r"^noncomputable def findDiscrVariant\? ", 1),
        "storage_dead_arm": (r"^  \| \.storageDead localId =>$", 1),
        "unreachable_terminator_arm": (r"^  \| \.unreachable =>$", 1),
    },
    ("joshlf/anneal", "trusted/lean/Trusted/MirAst.lean"): {
        "enum_ty_structure": (r"^structure EnumTy where$", 1),
        "fieldless_enum_descriptor_doc": (r"/-- Structural descriptor for a fieldless Rust enum", 1),
        "drop_terminator_unsupported_doc": (r"\(`UnwindTerminate`, `Drop`, indirect `Call`, `TailCall`, `Yield`,", 1),
        "drop_hint_statement_unsupported_doc": (r"`ConstEvalCounter`, and `BackwardIncompatibleDropHint`\)\. -/", 1),
    },
    ("rust-lang/reference", "src/destructors.md"): {
        "temporary_scope_rule": (r"^r\[destructors\.scope\.temporary\.enclosing\]$", 1),
        "if_let_condition_and_body": (r"The pattern-matching condition\(s\) and consequent body of \[`if`\]", 1),
        "tail_expression_entirety": (r"The entirety of the tail expression of a block", 1),
        "match_scrutinee_note": (r"The \[scrutinee\] of a `match` expression is not a temporary scope", 1),
        "edition_2024_rule": (r"^r\[destructors\.scope\.temporary\.edition2024\]$", 1),
    },
    ("rust-lang/reference", "src/behavior-considered-undefined.md"): {
        "producing_invalid_value": (r"Producing an \[invalid value\]\[invalid-values\]", 1),
        "enum_validity": (r"^r\[undefined\.validity\.enum\]$", 1),
    },
    ("rust-lang/rfcs", "text/3606-temporary-lifetimes-in-tail-expressions.md"): {
        "summary": (r"In the next edition, drop temporaries in tail expressions \*before\* dropping locals", 1),
        "match_scrutinee_future_possibility": (
            r"Dropping temporaries in a match scrutinee \*before\* the arms are evaluated,",
            1,
        ),
    },
    ("rust-lang/edition-guide", "src/rust-2024/temporary-if-let-scope.md"): {
        "summary": (r"will be dropped before the program enters the `else` branch instead of after", 1),
        "match_rewrite": (r"It is always safe to rewrite `if let` with a `match`", 1),
    },
    ("rust-lang/edition-guide", "src/rust-2024/temporary-tail-expr-scope.md"): {
        "summary": (r"may now be dropped before local variables", 1),
        "no_semantics_preserving_rewrite": (r"there are no semantics-preserving rewrites", 1),
    },
}


def fetch(repo: str, revision: str, path: str) -> bytes:
    """Download one file. `curl` is preferred when present (some HTTP proxies
    truncate HTTP/1.1 bodies); otherwise urllib is used, with retries."""
    url = f"https://raw.githubusercontent.com/{repo}/{revision}/{path}"
    last_error: object = None
    curl = shutil.which("curl")
    for _ in range(4):
        if curl:
            proc = subprocess.run([curl, "-sS", "--fail", "-m", "60", url], capture_output=True)
            if proc.returncode == 0:
                return proc.stdout
            last_error = proc.stderr.decode("utf-8", "replace").strip()
        else:
            try:
                request = urllib.request.Request(url, headers={"Accept-Encoding": "identity"})
                with urllib.request.urlopen(request, timeout=60) as resp:
                    return resp.read()
            except (http.client.HTTPException, OSError) as exc:
                last_error = exc
        time.sleep(1.0)
    raise RuntimeError(f"cannot fetch {url}: {last_error}")


def git_blob_sha1(data: bytes) -> str:
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--out", required=True)
    args = ap.parse_args()

    files = []
    problems = []
    for (repo, path), anchors in ANCHORS.items():
        per_revision = {}
        for revision in PINS[repo]:
            data = fetch(repo, revision, path)
            lines = data.decode("utf-8").splitlines()
            found = {}
            for anchor_id, (pattern, expected) in anchors.items():
                rx = re.compile(pattern)
                hits = [i + 1 for i, line in enumerate(lines) if rx.search(line)]
                found[anchor_id] = hits
                ok = (len(hits) >= 1) if expected is None else (len(hits) == expected)
                if not ok:
                    problems.append(
                        {"repository": repo, "revision": revision, "path": path, "anchor": anchor_id,
                         "expected_matches": expected, "lines": hits}
                    )
            per_revision[revision] = {
                "git_blob_sha1": git_blob_sha1(data),
                "bytes": len(data),
                "lines": len(lines),
                "anchors": found,
            }
        blob_ids = {entry["git_blob_sha1"] for entry in per_revision.values()}
        files.append(
            {
                "repository": repo,
                "path": path,
                "identical_across_listed_revisions": len(blob_ids) == 1,
                "per_revision": per_revision,
            }
        )

    manifest = {
        "schema": "upstream-source-anchor-manifest/1",
        "pins": PINS,
        "anchor_patterns": {
            f"{repo}:{path}": {k: {"regex": v[0], "expected_matches": v[1]} for k, v in anchors.items()}
            for (repo, path), anchors in ANCHORS.items()
        },
        "files": files,
        "files_total": len(files),
        "anchors_total": sum(len(a) for a in ANCHORS.values()),
        "anchor_expectation_failures": problems,
    }
    Path(args.out).write_text(json.dumps(manifest, indent=2, sort_keys=True, ensure_ascii=True) + "\n")
    print(f"{manifest['files_total']} files, {manifest['anchors_total']} anchors, {len(problems)} expectation failure(s)")
    for p in problems:
        print("ANCHOR PROBLEM:", json.dumps(p), file=sys.stderr)
    return 1 if problems else 0


if __name__ == "__main__":
    raise SystemExit(main())
