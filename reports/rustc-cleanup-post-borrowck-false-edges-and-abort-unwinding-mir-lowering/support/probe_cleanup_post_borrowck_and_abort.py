#!/usr/bin/env python3
"""Empirical MIR-phase, Miri, borrowck, and native abort probe for:
- `CleanupPostBorrowck` (`FakeRead`, `AscribeUserType`, `BorrowKind::Fake`,
  `PointerCoercion::{ArrayToPointer, MutToConstPointer}`, `FalseEdge`, `FalseUnwind`),
- `PlaceMention` vs `RemovePlaceMention` (`-Zmir-preserve-ub`), and
- `AbortUnwindingCalls` (`-C panic=unwind` vs `-C panic=abort`, `extern "C"` vs
  `extern "C-unwind"`, `fn` pointers, `InlineAsm(MAY_UNWIND)`, `Drop`, `Assert`).

Uses Python 3.10+ standard library only with scoped `tempfile.TemporaryDirectory` cleanup.
"""

from __future__ import annotations

import argparse
import datetime
import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent
SPECIMENS_DIR = HERE / "specimens"

CLEANUP_SPECIMENS = [
    "specimen_match_guard",
    "specimen_ascribe_and_ptr_coercions",
    "specimen_place_mention_only",
    "specimen_wildcard_match_place_mention",
    "specimen_loop_false_unwind",
    "specimen_nested_index_fake_borrow",
]

ABORT_SPECIMENS = [
    "caller_rust_calls_rust_with_drop",
    "caller_rust_calls_rust_no_drop",
    "caller_extern_c_calls_rust_with_drop",
    "caller_extern_c_calls_rust_no_drop",
    "caller_extern_c_calls_foreign_c_unwind_with_drop",
    "caller_extern_c_calls_foreign_c_unwind_no_drop",
    "caller_extern_c_unwind_calls_foreign_c_unwind_with_drop",
    "caller_extern_c_calls_foreign_c_nounwind_with_drop",
    "caller_rust_calls_fnptr_c_unwind_with_drop",
    "caller_rust_calls_fnptr_c_unwind_no_drop",
    "caller_rust_calls_rust_defined_c_unwind_with_drop",
    "caller_rust_inline_asm_may_unwind_with_drop",
    "caller_rust_assert_overflow_with_drop",
]

CURATED_MIR_EXCERPTS = [
    ("unwind", "specimen_match_guard", "2-1-002.CleanupPostBorrowck.before.mir"),
    ("unwind", "specimen_match_guard", "2-1-002.CleanupPostBorrowck.after.mir"),
    ("unwind", "specimen_ascribe_and_ptr_coercions", "2-1-002.CleanupPostBorrowck.before.mir"),
    ("unwind", "specimen_ascribe_and_ptr_coercions", "2-1-002.CleanupPostBorrowck.after.mir"),
    ("unwind", "specimen_loop_false_unwind", "2-1-002.CleanupPostBorrowck.before.mir"),
    ("unwind", "specimen_loop_false_unwind", "2-1-002.CleanupPostBorrowck.after.mir"),
    ("unwind", "specimen_place_mention_only", "3-2-000.runtime-post-cleanup.after.mir"),
    ("preserve_ub", "specimen_place_mention_only", "3-2-000.runtime-post-cleanup.after.mir"),
    ("unwind", "caller_extern_c_calls_foreign_c_unwind_with_drop", "2-2-006.AbortUnwindingCalls.before.mir"),
    ("unwind", "caller_extern_c_calls_foreign_c_unwind_with_drop", "2-2-006.AbortUnwindingCalls.after.mir"),
    ("unwind", "caller_extern_c_calls_foreign_c_unwind_no_drop", "2-2-006.AbortUnwindingCalls.before.mir"),
    ("unwind", "caller_extern_c_calls_foreign_c_unwind_no_drop", "2-2-006.AbortUnwindingCalls.after.mir"),
    ("unwind", "caller_extern_c_calls_foreign_c_nounwind_with_drop", "2-2-006.AbortUnwindingCalls.before.mir"),
    ("unwind", "caller_extern_c_calls_foreign_c_nounwind_with_drop", "2-2-006.AbortUnwindingCalls.after.mir"),
    ("abort", "caller_rust_calls_rust_with_drop", "2-2-006.AbortUnwindingCalls.before.mir"),
    ("abort", "caller_rust_calls_rust_with_drop", "2-2-006.AbortUnwindingCalls.after.mir"),
    ("abort", "caller_rust_calls_fnptr_c_unwind_with_drop", "2-2-006.AbortUnwindingCalls.before.mir"),
    ("abort", "caller_rust_calls_fnptr_c_unwind_with_drop", "2-2-006.AbortUnwindingCalls.after.mir"),
    ("abort", "caller_rust_calls_fnptr_c_unwind_no_drop", "2-2-006.AbortUnwindingCalls.before.mir"),
    ("abort", "caller_rust_calls_fnptr_c_unwind_no_drop", "2-2-006.AbortUnwindingCalls.after.mir"),
    ("abort", "caller_rust_calls_rust_defined_c_unwind_with_drop", "2-2-006.AbortUnwindingCalls.before.mir"),
    ("abort", "caller_rust_calls_rust_defined_c_unwind_with_drop", "2-2-006.AbortUnwindingCalls.after.mir"),
    ("abort", "caller_rust_inline_asm_may_unwind_with_drop", "2-2-006.AbortUnwindingCalls.before.mir"),
    ("abort", "caller_rust_inline_asm_may_unwind_with_drop", "2-2-006.AbortUnwindingCalls.after.mir"),
]


def run_cmd(cmd: list[str], cwd: Path | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )


def sanitize_text(text: str, scratch_root: Path) -> str:
    """Strip host-specific workspace/tmp paths from receipts and captured logs."""
    out = text.replace(str(SPECIMENS_DIR) + "/", "support/specimens/")
    out = out.replace(str(scratch_root), "<scratch>")
    out = re.sub(r"/tmp/[^\s:]+", "<tmp>", out)
    return out


def parse_mir_metrics(mir_text: str) -> dict[str, Any]:
    lines = mir_text.splitlines()
    bb_total = 0
    bb_cleanup = 0
    in_bb = False
    current_cleanup = False
    fakeread_causes: dict[str, int] = {}

    counts = {
        "basic_blocks": 0,
        "cleanup_blocks": 0,
        "fake_read": 0,
        "ascribe_user_type": 0,
        "fake_borrow": 0,
        "place_mention": 0,
        "backward_drop_hint": 0,
        "coverage_marker": 0,
        "coverage_virtual_counter": 0,
        "ptr_coercion_array_to_ptr": 0,
        "ptr_coercion_mut_to_const": 0,
        "ptr_to_ptr": 0,
        "nop": 0,
        "false_edge": 0,
        "false_unwind": 0,
        "unwind_cleanup_edge": 0,
        "unwind_continue_edge": 0,
        "unwind_unreachable_edge": 0,
        "unwind_terminate_abi_edge": 0,
        "unwind_terminate_cleanup_edge": 0,
        "term_resume": 0,
        "term_terminate_abi": 0,
        "term_unreachable": 0,
    }

    bb_header_re = re.compile(r"^\s*bb\d+(?:\s+\(cleanup\))?:\s*\{$")

    for raw in lines:
        s = raw.strip()
        if bb_header_re.match(raw):
            bb_total += 1
            current_cleanup = "(cleanup)" in s
            if current_cleanup:
                bb_cleanup += 1
            in_bb = True
            continue
        if in_bb and s == "}":
            in_bb = False
            continue
        if not in_bb:
            continue

        if s.startswith("FakeRead("):
            counts["fake_read"] += 1
            cause = s[len("FakeRead("):].split(",", 1)[0].strip()
            cause = cause.split("(", 1)[0].strip()
            fakeread_causes[cause] = fakeread_causes.get(cause, 0) + 1
        elif s.startswith("AscribeUserType("):
            counts["ascribe_user_type"] += 1
        elif "= &fake " in s:
            counts["fake_borrow"] += 1
        elif s.startswith("PlaceMention("):
            counts["place_mention"] += 1
        elif s.startswith("BackwardIncompatibleDropHint"):
            counts["backward_drop_hint"] += 1
        elif s.startswith("Coverage::VirtualCounter("):
            counts["coverage_virtual_counter"] += 1
        elif s.startswith("Coverage::"):
            counts["coverage_marker"] += 1
        elif s == "nop;":
            counts["nop"] += 1

        if "PointerCoercion(ArrayToPointer" in s:
            counts["ptr_coercion_array_to_ptr"] += 1
        if "PointerCoercion(MutToConstPointer" in s:
            counts["ptr_coercion_mut_to_const"] += 1
        if "(PtrToPtr);" in s:
            counts["ptr_to_ptr"] += 1

        if s.startswith("falseEdge ->"):
            counts["false_edge"] += 1
        elif s.startswith("falseUnwind ->"):
            counts["false_unwind"] += 1
        elif s == "resume;":
            counts["term_resume"] += 1
        elif s == "terminate(abi);":
            counts["term_terminate_abi"] += 1
        elif s == "unreachable;":
            counts["term_unreachable"] += 1

        # Count unwind action clauses on terminators
        counts["unwind_cleanup_edge"] += len(re.findall(r"unwind:\s*bb\d+", s))
        counts["unwind_continue_edge"] += len(re.findall(r"unwind continue\b", s))
        counts["unwind_unreachable_edge"] += len(re.findall(r"unwind unreachable\b", s))
        counts["unwind_terminate_abi_edge"] += len(re.findall(r"unwind terminate\(abi\)", s))
        counts["unwind_terminate_cleanup_edge"] += len(re.findall(r"unwind terminate\(cleanup\)", s))

    counts["basic_blocks"] = bb_total
    counts["cleanup_blocks"] = bb_cleanup
    counts["fake_read_causes"] = dict(sorted(fakeread_causes.items()))
    return counts


def find_dump(dump_dir: Path, fn_name: str, suffix: str) -> Path | None:
    matches = sorted(dump_dir.glob(f"*.{fn_name}.{suffix}"))
    if not matches:
        return None
    return matches[0]


def collect_mir_suite(rustc_bin: str, tmp: Path) -> tuple[dict[str, Any], dict[str, str]]:
    spec = SPECIMENS_DIR / "mir_pipeline_specimens.rs"
    configs = {
        "unwind": ["-C", "panic=unwind"],
        "abort": ["-C", "panic=abort"],
        "preserve_ub": ["-C", "panic=unwind", "-Z", "mir-preserve-ub=yes"],
        "coverage": ["-C", "panic=unwind", "-C", "instrument-coverage"],
    }

    dump_roots: dict[str, Path] = {}
    compile_receipts: dict[str, Any] = {}

    for label, extra_flags in configs.items():
        ddir = tmp / f"dump_{label}"
        ddir.mkdir(parents=True, exist_ok=True)
        out_rlib = tmp / f"lib_{label}.rlib"
        cmd = [
            rustc_bin,
            "--edition",
            "2021",
            "--crate-type",
            "lib",
            "-C",
            "opt-level=0",
            "-C",
            "debuginfo=0",
            "-Z",
            "validate-mir",
            "-Z",
            "dump-mir=all",
            "-Z",
            f"dump-mir-dir={ddir}",
            *extra_flags,
            "-o",
            str(out_rlib),
            str(spec),
        ]
        proc = run_cmd(cmd)
        if proc.returncode != 0:
            raise RuntimeError(f"rustc failed for {label}:\n{proc.stderr}")
        dump_roots[label] = ddir
        compile_receipts[label] = {
            "rc": proc.returncode,
            "flags": extra_flags,
            "dump_file_count": len(list(ddir.glob("*.mir"))),
        }

    cleanup_pass_suffixes = [
        ("built", "1-1-000.built.after.mir"),
        ("before_cleanup_post_borrowck", "2-1-002.CleanupPostBorrowck.before.mir"),
        ("after_cleanup_post_borrowck", "2-1-002.CleanupPostBorrowck.after.mir"),
        ("analysis_post_cleanup", "2-2-000.analysis-post-cleanup.after.mir"),
        ("before_remove_place_mention", "3-1-002.RemovePlaceMention.before.mir"),
        ("after_remove_place_mention", "3-1-002.RemovePlaceMention.after.mir"),
        ("runtime_post_cleanup", "3-2-000.runtime-post-cleanup.after.mir"),
    ]

    cleanup_data: dict[str, Any] = {}
    for label in ("unwind", "preserve_ub", "coverage"):
        per_fn: dict[str, Any] = {}
        for fn in CLEANUP_SPECIMENS:
            fn_entry: dict[str, Any] = {}
            for stage_key, suffix in cleanup_pass_suffixes:
                p = find_dump(dump_roots[label], fn, suffix)
                if p is not None:
                    fn_entry[stage_key] = parse_mir_metrics(p.read_text(encoding="utf-8"))
            per_fn[fn] = fn_entry
        cleanup_data[label] = per_fn

    abort_pass_suffixes = [
        ("after_remove_noop_landing_pads", "2-1-003.RemoveNoopLandingPads.after.mir"),
        ("before_abort_unwinding_calls", "2-2-006.AbortUnwindingCalls.before.mir"),
        ("after_abort_unwinding_calls", "2-2-006.AbortUnwindingCalls.after.mir"),
        ("runtime_post_cleanup", "3-2-000.runtime-post-cleanup.after.mir"),
    ]

    abort_data: dict[str, Any] = {}
    for label in ("unwind", "abort"):
        per_fn = {}
        for fn in ABORT_SPECIMENS:
            fn_entry = {}
            for stage_key, suffix in abort_pass_suffixes:
                p = find_dump(dump_roots[label], fn, suffix)
                if p is not None:
                    fn_entry[stage_key] = parse_mir_metrics(p.read_text(encoding="utf-8"))
            per_fn[fn] = fn_entry
        abort_data[label] = per_fn

    excerpts: dict[str, str] = {}
    for label, fn, suffix in CURATED_MIR_EXCERPTS:
        p = find_dump(dump_roots[label], fn, suffix)
        if p is None:
            raise RuntimeError(f"missing curated dump {label} {fn} {suffix}")
        fname = f"{label}__{fn}.{suffix}"
        excerpts[fname] = sanitize_text(p.read_text(encoding="utf-8"), tmp)

    return {
        "compile_receipts": compile_receipts,
        "cleanup_post_borrowck_and_place_mention": cleanup_data,
        "abort_unwinding_calls": abort_data,
    }, excerpts


def run_custom_mir_suite(rustc_bin: str, tmp: Path) -> tuple[dict[str, Any], dict[str, str]]:
    spec = SPECIMENS_DIR / "custom_mir_specimens.rs"
    results: dict[str, Any] = {}
    excerpts: dict[str, str] = {}

    for label, panic_flag in (("unwind", "panic=unwind"), ("abort", "panic=abort")):
        ddir = tmp / f"custom_dump_{label}"
        ddir.mkdir(parents=True, exist_ok=True)
        bin_path = tmp / f"custom_bin_{label}"
        comp = run_cmd([
            rustc_bin,
            "--edition",
            "2021",
            "-C",
            "opt-level=0",
            "-C",
            panic_flag,
            "-Z",
            "validate-mir",
            "-Z",
            "dump-mir=AbortUnwindingCalls|runtime-post-cleanup",
            "-Z",
            f"dump-mir-dir={ddir}",
            "-o",
            str(bin_path),
            str(spec),
        ])
        if comp.returncode != 0:
            raise RuntimeError(f"custom_mir compile failed ({label}):\n{comp.stderr}")
        exec_proc = run_cmd([str(bin_path)])
        if exec_proc.returncode != 0:
            raise RuntimeError(f"custom_mir exec failed ({label}): {exec_proc.stderr}")

        fns: dict[str, Any] = {}
        for fn in ("custom_extern_c_unwind_continue", "custom_extern_c_unwind_cleanup_pad"):
            b = find_dump(ddir, fn, "2-2-006.AbortUnwindingCalls.before.mir")
            a = find_dump(ddir, fn, "2-2-006.AbortUnwindingCalls.after.mir")
            if b is None or a is None:
                raise RuntimeError(f"missing custom_mir dump for {fn} ({label})")
            fns[fn] = {
                "before_abort_unwinding_calls": parse_mir_metrics(b.read_text(encoding="utf-8")),
                "after_abort_unwinding_calls": parse_mir_metrics(a.read_text(encoding="utf-8")),
            }
            if label == "unwind":
                excerpts[f"custom_{label}__{fn}.2-2-006.AbortUnwindingCalls.before.mir"] = sanitize_text(b.read_text(encoding="utf-8"), tmp)
                excerpts[f"custom_{label}__{fn}.2-2-006.AbortUnwindingCalls.after.mir"] = sanitize_text(a.read_text(encoding="utf-8"), tmp)

        results[label] = {
            "compile_rc": comp.returncode,
            "exec_rc": exec_proc.returncode,
            "functions": fns,
        }

    return results, excerpts


def run_miri_suite(miri_bin: str, tmp: Path) -> dict[str, Any]:
    spec = SPECIMENS_DIR / "miri_place_and_guard_ub.rs"
    cases = [
        "place_mention_invalid_bool",
        "wildcard_match_invalid_bool",
        "let_named_invalid_bool",
        "place_mention_dangling_thin_ptr",
        "place_mention_uninit_double_ptr",
        "match_guard_raw_ptr_mutation",
        "empty_match_raw_ptr_void",
    ]
    out: dict[str, Any] = {}
    for case in cases:
        proc = run_cmd([
            miri_bin,
            "--edition",
            "2021",
            "--cfg",
            f'case="{case}"',
            str(spec),
        ])
        err = sanitize_text(proc.stderr, tmp)
        err_lines = [ln.strip() for ln in err.splitlines() if ln.strip().startswith("error")]
        out[case] = {
            "rc": proc.returncode,
            "ub_detected": proc.returncode != 0 and "Undefined Behavior:" in err,
            "first_error": err_lines[0] if err_lines else "",
        }
    return out


def run_borrowck_and_native_abort(rustc_bin: str, tmp: Path) -> dict[str, Any]:
    spec = SPECIMENS_DIR / "borrowck_and_native_abort.rs"
    out: dict[str, Any] = {}

    for case in ("borrowck_guard_mutates_scrutinee", "borrowck_empty_match_uninit_void"):
        comp = run_cmd([
            rustc_bin,
            "--edition",
            "2021",
            "-C",
            "opt-level=0",
            "--cfg",
            f'case="{case}"',
            "-o",
            str(tmp / f"{case}_bin"),
            str(spec),
        ])
        err = sanitize_text(comp.stderr, tmp)
        err_lines = [ln.strip() for ln in err.splitlines() if ln.strip().startswith("error[")]
        out[case] = {
            "compile_rc": comp.returncode,
            "first_error": err_lines[0] if err_lines else "",
        }

    native_bin = tmp / "native_extern_c_abort_bin"
    comp_native = run_cmd([
        rustc_bin,
        "--edition",
        "2021",
        "-C",
        "opt-level=0",
        "-C",
        "panic=unwind",
        "--cfg",
        'case="native_extern_c_unwind_aborts_after_drop"',
        "-o",
        str(native_bin),
        str(spec),
    ])
    if comp_native.returncode != 0:
        raise RuntimeError(f"native abort specimen failed to compile:\n{comp_native.stderr}")
    run_native = run_cmd([str(native_bin)])
    stderr_sanitized = sanitize_text(run_native.stderr, tmp)
    out["native_extern_c_unwind_aborts_after_drop"] = {
        "compile_rc": comp_native.returncode,
        "run_rc": run_native.returncode,
        "drop_executed": "NATIVE_CLEANUP_DROP_EXECUTED=1" in stderr_sanitized,
        "cannot_unwind_message": "panic in a function that cannot unwind" in stderr_sanitized,
    }
    return out


def verify_assertions(results: dict[str, Any]) -> list[dict[str, Any]]:
    checks: list[dict[str, Any]] = []

    def check(name: str, cond: bool, detail: str = "") -> None:
        checks.append({"name": name, "passed": bool(cond), "detail": detail})

    cpb_u = results["mir_pipeline"]["cleanup_post_borrowck_and_place_mention"]["unwind"]
    cpb_p = results["mir_pipeline"]["cleanup_post_borrowck_and_place_mention"]["preserve_ub"]
    cpb_c = results["mir_pipeline"]["cleanup_post_borrowck_and_place_mention"]["coverage"]

    # 1. CleanupPostBorrowck erasures in specimen_match_guard
    mg_b = cpb_u["specimen_match_guard"]["before_cleanup_post_borrowck"]
    mg_a = cpb_u["specimen_match_guard"]["after_cleanup_post_borrowck"]
    mg_apc = cpb_u["specimen_match_guard"]["analysis_post_cleanup"]
    check(
        "cleanup::match_guard_erases_all_fakeread_fakeborrow_falseedge",
        mg_b["fake_read"] > 0
        and mg_b["fake_borrow"] > 0
        and mg_b["false_edge"] > 0
        and mg_a["fake_read"] == 0
        and mg_a["fake_borrow"] == 0
        and mg_a["false_edge"] == 0
        and mg_a["nop"] >= mg_b["nop"] + mg_b["fake_read"] + mg_b["fake_borrow"],
        f"before=(fr={mg_b['fake_read']},fb={mg_b['fake_borrow']},fe={mg_b['false_edge']}), after=(fr={mg_a['fake_read']},fb={mg_a['fake_borrow']},fe={mg_a['false_edge']},nop={mg_a['nop']})",
    )
    check(
        "cleanup::match_guard_preserves_place_mention_across_postcleanup",
        mg_b["place_mention"] > 0
        and mg_a["place_mention"] == mg_b["place_mention"]
        and mg_apc["place_mention"] == mg_b["place_mention"],
        f"place_mention={mg_b['place_mention']} -> {mg_a['place_mention']} -> {mg_apc['place_mention']}",
    )

    # 2. AscribeUserType and PointerCoercion rewrites
    asc_b = cpb_u["specimen_ascribe_and_ptr_coercions"]["before_cleanup_post_borrowck"]
    asc_a = cpb_u["specimen_ascribe_and_ptr_coercions"]["after_cleanup_post_borrowck"]
    check(
        "cleanup::ascribe_and_ptr_coercions_lowered_to_nop_and_ptr_to_ptr",
        asc_b["ascribe_user_type"] > 0
        and asc_b["ptr_coercion_array_to_ptr"] > 0
        and asc_b["ptr_coercion_mut_to_const"] > 0
        and asc_a["ascribe_user_type"] == 0
        and asc_a["ptr_coercion_array_to_ptr"] == 0
        and asc_a["ptr_coercion_mut_to_const"] == 0
        and asc_a["ptr_to_ptr"] >= asc_b["ptr_to_ptr"] + asc_b["ptr_coercion_array_to_ptr"] + asc_b["ptr_coercion_mut_to_const"],
        f"ascribe={asc_b['ascribe_user_type']}->{asc_a['ascribe_user_type']}, arr2ptr={asc_b['ptr_coercion_array_to_ptr']}->{asc_a['ptr_coercion_array_to_ptr']}, mut2const={asc_b['ptr_coercion_mut_to_const']}->{asc_a['ptr_coercion_mut_to_const']}",
    )

    # 3. FalseUnwind rewrite
    lp_b = cpb_u["specimen_loop_false_unwind"]["before_cleanup_post_borrowck"]
    lp_a = cpb_u["specimen_loop_false_unwind"]["after_cleanup_post_borrowck"]
    check(
        "cleanup::loop_false_unwind_removed",
        lp_b["false_unwind"] == 1 and lp_a["false_unwind"] == 0,
        f"false_unwind={lp_b['false_unwind']}->{lp_a['false_unwind']}",
    )

    # 4. Nested slice index fake borrow (ForIndex)
    idx_b = cpb_u["specimen_nested_index_fake_borrow"]["before_cleanup_post_borrowck"]
    idx_a = cpb_u["specimen_nested_index_fake_borrow"]["after_cleanup_post_borrowck"]
    check(
        "cleanup::nested_index_fake_borrow_for_index_erased",
        idx_b["fake_borrow"] >= 2
        and idx_b["fake_read_causes"].get("ForIndex", 0) >= 2
        and idx_a["fake_borrow"] == 0
        and idx_a["fake_read"] == 0,
        f"before={idx_b['fake_read_causes']}, after_fb={idx_a['fake_borrow']}",
    )

    # 5. Coverage VirtualCounter survives CleanupPostBorrowck
    cov_b = cpb_c["specimen_match_guard"]["before_cleanup_post_borrowck"]
    cov_a = cpb_c["specimen_match_guard"]["after_cleanup_post_borrowck"]
    check(
        "cleanup::coverage_virtual_counter_preserved",
        cov_b["coverage_virtual_counter"] > 0
        and cov_a["coverage_virtual_counter"] == cov_b["coverage_virtual_counter"],
        f"virtual_counters={cov_b['coverage_virtual_counter']}->{cov_a['coverage_virtual_counter']}",
    )

    # 6. RemovePlaceMention gated by -Z mir-preserve-ub
    pm_u_b = cpb_u["specimen_place_mention_only"]["before_remove_place_mention"]
    pm_u_a = cpb_u["specimen_place_mention_only"]["after_remove_place_mention"]
    pm_p_rt = cpb_p["specimen_place_mention_only"]["runtime_post_cleanup"]
    check(
        "runtime_cleanup::remove_place_mention_vs_mir_preserve_ub",
        pm_u_b["place_mention"] == 1
        and pm_u_a["place_mention"] == 0
        and pm_p_rt["place_mention"] == 1,
        f"default={pm_u_b['place_mention']}->{pm_u_a['place_mention']}, mir_preserve_ub={pm_p_rt['place_mention']}",
    )

    # 7. AbortUnwindingCalls checks
    auc_u = results["mir_pipeline"]["abort_unwinding_calls"]["unwind"]
    auc_a = results["mir_pipeline"]["abort_unwinding_calls"]["abort"]

    # extern "C" calling Rust fn with Drop under panic=unwind preserves cleanup drop + turns resume -> terminate(abi)
    ec_r_d_b = auc_u["caller_extern_c_calls_rust_with_drop"]["before_abort_unwinding_calls"]
    ec_r_d_a = auc_u["caller_extern_c_calls_rust_with_drop"]["after_abort_unwinding_calls"]
    check(
        "abort_unwinding::unwind_extern_c_with_drop_preserves_cleanup_and_terminates",
        ec_r_d_b["term_resume"] == 1
        and ec_r_d_a["term_resume"] == 0
        and ec_r_d_a["term_terminate_abi"] == 1
        and ec_r_d_a["cleanup_blocks"] == ec_r_d_b["cleanup_blocks"],
        f"cleanup_bbs={ec_r_d_b['cleanup_blocks']}->{ec_r_d_a['cleanup_blocks']}, term_abi={ec_r_d_a['term_terminate_abi']}",
    )

    # extern "C" calling foreign C-unwind with no drop under panic=unwind: RemoveNoopLandingPads produced Continue, AbortUnwindingCalls turns Continue -> Terminate(Abi)
    ec_cu_nd_b = auc_u["caller_extern_c_calls_foreign_c_unwind_no_drop"]["before_abort_unwinding_calls"]
    ec_cu_nd_a = auc_u["caller_extern_c_calls_foreign_c_unwind_no_drop"]["after_abort_unwinding_calls"]
    check(
        "abort_unwinding::unwind_extern_c_no_drop_continue_to_terminate_abi",
        ec_cu_nd_b["unwind_continue_edge"] == 1
        and ec_cu_nd_a["unwind_continue_edge"] == 0
        and ec_cu_nd_a["unwind_terminate_abi_edge"] == 1
        and ec_cu_nd_a["cleanup_blocks"] == 0,
        f"before_cont={ec_cu_nd_b['unwind_continue_edge']}, after_term_abi_edge={ec_cu_nd_a['unwind_terminate_abi_edge']}",
    )

    # extern "C" calling foreign C nounwind with Drop under panic=unwind: call's cleanup becomes unreachable and dead cleanup block removed
    ec_cn_d_b = auc_u["caller_extern_c_calls_foreign_c_nounwind_with_drop"]["before_abort_unwinding_calls"]
    ec_cn_d_a = auc_u["caller_extern_c_calls_foreign_c_nounwind_with_drop"]["after_abort_unwinding_calls"]
    check(
        "abort_unwinding::unwind_extern_c_calling_nounwind_c_marks_call_unreachable_and_drops_dead_cleanup",
        ec_cn_d_b["cleanup_blocks"] == 2
        and ec_cn_d_a["cleanup_blocks"] == 1
        and ec_cn_d_a["unwind_unreachable_edge"] == 1
        and ec_cn_d_a["term_terminate_abi"] == 1,
        f"cleanup_bbs={ec_cn_d_b['cleanup_blocks']}->{ec_cn_d_a['cleanup_blocks']}, unreach_edge={ec_cn_d_a['unwind_unreachable_edge']}",
    )

    # panic=abort calling Rust fn with Drop removes ALL cleanup blocks immediately inside AbortUnwindingCalls
    ab_rr_d_b = auc_a["caller_rust_calls_rust_with_drop"]["before_abort_unwinding_calls"]
    ab_rr_d_a = auc_a["caller_rust_calls_rust_with_drop"]["after_abort_unwinding_calls"]
    check(
        "abort_unwinding::panic_abort_rust_call_with_drop_removes_all_cleanup_blocks",
        ab_rr_d_b["cleanup_blocks"] == 2
        and ab_rr_d_a["cleanup_blocks"] == 0
        and ab_rr_d_a["unwind_unreachable_edge"] == 2,
        f"cleanup_bbs={ab_rr_d_b['cleanup_blocks']}->{ab_rr_d_a['cleanup_blocks']}, unreach_edges={ab_rr_d_a['unwind_unreachable_edge']}",
    )

    # panic=abort: direct call to Rust-defined extern "C-unwind" has call_can_unwind=false (all cleanup blocks removed)
    ab_rcu_b = auc_a["caller_rust_calls_rust_defined_c_unwind_with_drop"]["before_abort_unwinding_calls"]
    ab_rcu_a = auc_a["caller_rust_calls_rust_defined_c_unwind_with_drop"]["after_abort_unwinding_calls"]
    check(
        "abort_unwinding::panic_abort_rust_defined_c_unwind_fndef_cannot_unwind",
        ab_rcu_b["cleanup_blocks"] == 2 and ab_rcu_a["cleanup_blocks"] == 0,
        f"cleanup_bbs={ab_rcu_b['cleanup_blocks']}->{ab_rcu_a['cleanup_blocks']}",
    )

    # panic=abort: indirect fn ptr call to extern "C-unwind" retains call_can_unwind=true (preserves cleanup + terminate(abi))
    ab_fp_a = auc_a["caller_rust_calls_fnptr_c_unwind_with_drop"]["after_abort_unwinding_calls"]
    check(
        "abort_unwinding::panic_abort_fnptr_c_unwind_retains_cleanup_and_terminates",
        ab_fp_a["cleanup_blocks"] == 2
        and ab_fp_a["term_terminate_abi"] == 1
        and ab_fp_a["unwind_cleanup_edge"] == 1
        and ab_fp_a["unwind_unreachable_edge"] == 1,
        f"cleanup_bbs={ab_fp_a['cleanup_blocks']}, term_abi={ab_fp_a['term_terminate_abi']}",
    )

    # panic=abort: RemoveNoopLandingPads is disabled under panic=abort, so fnptr_c_unwind_no_drop keeps cleanup bb with terminate(abi)
    ab_fp_nd_a = auc_a["caller_rust_calls_fnptr_c_unwind_no_drop"]["after_abort_unwinding_calls"]
    ab_fp_nd_rt = auc_a["caller_rust_calls_fnptr_c_unwind_no_drop"]["runtime_post_cleanup"]
    check(
        "abort_unwinding::panic_abort_noop_pad_not_stripped_before_auc",
        ab_fp_nd_a["cleanup_blocks"] == 1
        and ab_fp_nd_a["term_terminate_abi"] == 1
        and ab_fp_nd_rt["cleanup_blocks"] == 1,
        f"cleanup_bbs_after_auc={ab_fp_nd_a['cleanup_blocks']}, runtime_post_cleanup={ab_fp_nd_rt['cleanup_blocks']}",
    )

    # panic=abort: InlineAsm(MAY_UNWIND) retains cleanup and terminates(abi); Assert becomes unreachable
    ab_asm_a = auc_a["caller_rust_inline_asm_may_unwind_with_drop"]["after_abort_unwinding_calls"]
    ab_ass_a = auc_a["caller_rust_assert_overflow_with_drop"]["after_abort_unwinding_calls"]
    check(
        "abort_unwinding::panic_abort_inline_asm_may_unwind_retains_cleanup_while_assert_unreachable",
        ab_asm_a["cleanup_blocks"] == 2
        and ab_asm_a["term_terminate_abi"] == 1
        and ab_ass_a["cleanup_blocks"] == 0
        and ab_ass_a["unwind_unreachable_edge"] == 2,
        f"asm_bbs={ab_asm_a['cleanup_blocks']}, assert_bbs={ab_ass_a['cleanup_blocks']}",
    )

    # custom_mir assertions
    cm_u = results["custom_mir"]["unwind"]["functions"]
    check(
        "custom_mir::extern_c_unwind_continue_lowered_to_terminate_abi",
        cm_u["custom_extern_c_unwind_continue"]["before_abort_unwinding_calls"]["unwind_continue_edge"] == 1
        and cm_u["custom_extern_c_unwind_continue"]["after_abort_unwinding_calls"]["unwind_terminate_abi_edge"] == 1
        and cm_u["custom_extern_c_unwind_cleanup_pad"]["after_abort_unwinding_calls"]["term_terminate_abi"] == 1,
        "verified on both panic=unwind and panic=abort",
    )

    # Miri assertions
    miri = results["miri"]
    check(
        "miri::place_mention_and_wildcard_match_ignore_invalid_bool_value",
        miri["place_mention_invalid_bool"]["rc"] == 0
        and miri["wildcard_match_invalid_bool"]["rc"] == 0
        and miri["let_named_invalid_bool"]["ub_detected"]
        and "encountered 0x02" in miri["let_named_invalid_bool"]["first_error"],
        f"let_named_err={miri['let_named_invalid_bool']['first_error']}",
    )
    check(
        "miri::place_mention_still_evaluates_pointer_local_chain",
        miri["place_mention_dangling_thin_ptr"]["rc"] == 0
        and miri["place_mention_uninit_double_ptr"]["ub_detected"],
        f"dangling_ptr_rc={miri['place_mention_dangling_thin_ptr']['rc']}, double_ptr_err={miri['place_mention_uninit_double_ptr']['first_error']}",
    )
    check(
        "miri::guard_raw_ptr_mutation_bypasses_erased_fake_borrow_and_triggers_ub",
        miri["match_guard_raw_ptr_mutation"]["ub_detected"]
        and "0x02" in miri["match_guard_raw_ptr_mutation"]["first_error"]
        and miri["empty_match_raw_ptr_void"]["ub_detected"]
        and "unreachable" in miri["empty_match_raw_ptr_void"]["first_error"],
        f"guard_err={miri['match_guard_raw_ptr_mutation']['first_error']}, void_err={miri['empty_match_raw_ptr_void']['first_error']}",
    )

    # Borrowck + native abort assertions
    bn = results["borrowck_and_native_abort"]
    check(
        "borrowck::fake_borrow_and_fake_read_reject_safe_equivalents",
        bn["borrowck_guard_mutates_scrutinee"]["compile_rc"] != 0
        and "E0510" in bn["borrowck_guard_mutates_scrutinee"]["first_error"]
        and bn["borrowck_empty_match_uninit_void"]["compile_rc"] != 0
        and "E0381" in bn["borrowck_empty_match_uninit_void"]["first_error"],
        f"guard={bn['borrowck_guard_mutates_scrutinee']['first_error']}, empty={bn['borrowck_empty_match_uninit_void']['first_error']}",
    )
    na = bn["native_extern_c_unwind_aborts_after_drop"]
    check(
        "native::extern_c_runs_local_destructor_before_abi_abort",
        na["compile_rc"] == 0
        and na["run_rc"] < 0
        and na["drop_executed"]
        and na["cannot_unwind_message"],
        f"run_rc={na['run_rc']}, drop={na['drop_executed']}, msg={na['cannot_unwind_message']}",
    )

    return checks


def render_summary_md(results: dict[str, Any]) -> str:
    lines = [
        "# Probe Summary: CleanupPostBorrowck, PlaceMention, and AbortUnwindingCalls",
        "",
        f"- Toolchain: `{results['rustc_version'].splitlines()[0]}` (`{results['rustc_commit']}`)",
        f"- Miri: `{results['miri_version']}`",
        "",
        "## CleanupPostBorrowck & RemovePlaceMention Counts (Unwind vs `-Zmir-preserve-ub=yes`)",
        "",
        "| Function | Before `FakeRead` | Before `FakeBorrow` | Before `Ascribe` | Before `FalseEdge`/`Unwind` | After `CleanupPostBorrowck` Analysis Items | `PlaceMention` Default RT | `PlaceMention` `-Zmir-preserve-ub` |",
        "| :-- | --: | --: | --: | --: | --: | --: | --: |",
    ]
    cpb_u = results["mir_pipeline"]["cleanup_post_borrowck_and_place_mention"]["unwind"]
    cpb_p = results["mir_pipeline"]["cleanup_post_borrowck_and_place_mention"]["preserve_ub"]
    for fn in CLEANUP_SPECIMENS:
        b = cpb_u[fn]["before_cleanup_post_borrowck"]
        a = cpb_u[fn]["after_cleanup_post_borrowck"]
        rt_u = cpb_u[fn]["runtime_post_cleanup"]
        rt_p = cpb_p[fn]["runtime_post_cleanup"]
        rem = a["fake_read"] + a["fake_borrow"] + a["ascribe_user_type"] + a["false_edge"] + a["false_unwind"]
        lines.append(
            f"| `{fn}` | {b['fake_read']} | {b['fake_borrow']} | {b['ascribe_user_type']} | {b['false_edge'] + b['false_unwind']} | {rem} | {rt_u['place_mention']} | {rt_p['place_mention']} |"
        )

    lines.extend([
        "",
        "## AbortUnwindingCalls Matrix (`-C panic=unwind` vs `-C panic=abort`)",
        "",
        "| Caller | Strategy | Cleanup BBs Before -> After | `Continue` Before -> After | `Unreachable` Edges After | `Terminate(Abi)` Edges / Terminators After |",
        "| :-- | :-- | --: | --: | --: | :-- |",
    ])
    for strat in ("unwind", "abort"):
        auc = results["mir_pipeline"]["abort_unwinding_calls"][strat]
        for fn in ABORT_SPECIMENS:
            b = auc[fn]["before_abort_unwinding_calls"]
            a = auc[fn]["after_abort_unwinding_calls"]
            lines.append(
                f"| `{fn}` | `{strat}` | {b['cleanup_blocks']} -> {a['cleanup_blocks']} | {b['unwind_continue_edge']} -> {a['unwind_continue_edge']} | {a['unwind_unreachable_edge']} | {a['unwind_terminate_abi_edge']} / {a['term_terminate_abi']} |"
            )

    lines.extend([
        "",
        "## Miri, Borrowck, and Native Abort Checks",
        "",
        f"Total checks: {len(results['checks'])}; Passed: {sum(1 for c in results['checks'] if c['passed'])}; Failed: {sum(1 for c in results['checks'] if not c['passed'])}.",
    ])
    for c in results["checks"]:
        mark = "PASS" if c["passed"] else "FAIL"
        lines.append(f"- `{mark}` `{c['name']}` ({c['detail']})")
    lines.append("")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--rustc", default="rustc")
    ap.add_argument("--miri", default="")
    ap.add_argument("--out", default=str(HERE / "probe_output"))
    args = ap.parse_args(argv)

    ver_proc = run_cmd([args.rustc, "-Vv"])
    if ver_proc.returncode != 0:
        print(f"failed to run {args.rustc} -Vv: {ver_proc.stderr}", file=sys.stderr)
        return 1
    rustc_ver = ver_proc.stdout.strip()
    m_hash = re.search(r"^commit-hash:\s*([0-9a-f]{40})", rustc_ver, flags=re.M)
    rustc_commit = m_hash.group(1) if m_hash else "unknown"

    miri_bin = args.miri
    if not miri_bin:
        sysroot_proc = run_cmd([args.rustc, "--print", "sysroot"])
        if sysroot_proc.returncode != 0:
            print("failed to query rustc sysroot", file=sys.stderr)
            return 1
        miri_bin = str(Path(sysroot_proc.stdout.strip()) / "bin" / "miri")

    miri_ver_proc = run_cmd([miri_bin, "--version"])
    if miri_ver_proc.returncode != 0:
        print(f"failed to run {miri_bin} --version: {miri_ver_proc.stderr}", file=sys.stderr)
        return 1
    miri_ver = miri_ver_proc.stdout.strip()

    out_dir = Path(args.out)
    mir_dir = out_dir / "mir"
    out_dir.mkdir(parents=True, exist_ok=True)
    if mir_dir.exists():
        shutil.rmtree(mir_dir)
    mir_dir.mkdir(parents=True, exist_ok=True)

    with tempfile.TemporaryDirectory(prefix="cleanup_probe_") as tmp_str:
        tmp = Path(tmp_str)
        mir_pipeline, excerpts = collect_mir_suite(args.rustc, tmp)
        custom_mir, custom_excerpts = run_custom_mir_suite(args.rustc, tmp)
        excerpts.update(custom_excerpts)
        miri_results = run_miri_suite(miri_bin, tmp)
        bn_results = run_borrowck_and_native_abort(args.rustc, tmp)

    results: dict[str, Any] = {
        "schema": "probe-results/1",
        "generated_on": datetime.date.today().isoformat(),
        "rustc_version": rustc_ver,
        "rustc_commit": rustc_commit,
        "miri_version": miri_ver,
        "mir_pipeline": mir_pipeline,
        "custom_mir": custom_mir,
        "miri": miri_results,
        "borrowck_and_native_abort": bn_results,
    }
    checks = verify_assertions(results)
    results["checks"] = checks
    results["passed"] = all(c["passed"] for c in checks)

    for fname, content in sorted(excerpts.items()):
        (mir_dir / fname).write_text(content, encoding="utf-8")

    (out_dir / "probe_results.json").write_text(
        json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    (out_dir / "probe_summary.md").write_text(render_summary_md(results), encoding="utf-8")

    passed = sum(1 for c in checks if c["passed"])
    print(f"Probe completed: {passed}/{len(checks)} checks passed")
    for c in checks:
        if not c["passed"]:
            print(f"FAIL {c['name']}: {c['detail']}", file=sys.stderr)
    return 0 if results["passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
