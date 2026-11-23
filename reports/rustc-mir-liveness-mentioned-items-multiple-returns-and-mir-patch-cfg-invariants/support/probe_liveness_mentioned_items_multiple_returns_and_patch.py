#!/usr/bin/env python3
"""Live rustc differential probe for:
  - check_liveness (liveness.rs): CoroutineClosure blind spot (AsyncFnMut & AsyncFnOnce),
    FnMut Return/UnwindResume -> START_BLOCK loop closure, self_assignment (+=, /=, *p +=),
    FakeRead/merge_guards, maybe_drop_guard field vs direct overwrite, by-ref capture liveness.
  - MentionedItems (mentioned_items.rs + rustc_monomorphize::collector): all 6 visitor patterns
    enforcing post-monomorphization errors across dead-code elimination (-O0 vs -O3/-Zmir-opt-level=4),
    mentioned-only non-codegen link test, and the rlib cross_crate_inlinable root-selection seam.
  - MultipleReturnTerminators (multiple_return_terminators.rs): mir-opt-level=3 vs 4
    empty-Return tail duplication + remove_dead_blocks, and non-empty Return block preservation.
  - MirPatch (patch.rs): bipartite cleanup vs non-cleanup Unreachable / UnwindTerminate blocks
    and UnreachablePropagation statement clearing.

Outputs deterministic JSON to stdout or --out <path>, normalizing temporary paths so no
host-specific paths appear in recorded evidence.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import Any


def find_rustc() -> str:
    env_rustc = os.environ.get("RUSTC")
    if env_rustc:
        return env_rustc
    which_rustc = shutil.which("rustc")
    if which_rustc:
        return which_rustc
    cargo_rustc = Path.home() / ".cargo" / "bin" / "rustc"
    if cargo_rustc.exists():
        return str(cargo_rustc)
    raise RuntimeError("rustc not found in PATH or ~/.cargo/bin/rustc")


def sanitize_tmp_paths(text: str, tmp_dir: str) -> str:
    return text.replace(tmp_dir, "<tmp>")


def run_rustc(
    rustc: str,
    code: str,
    extra_args: list[str],
    *,
    edition: str = "2024",
    crate_type: str = "lib",
    dump_mir_filter: str | None = None,
    capture_mir_output: bool = False,
) -> dict[str, Any]:
    with tempfile.TemporaryDirectory(prefix="rustc_livepatch_") as td:
        td_path = Path(td)
        src = td_path / "probe.rs"
        src.write_text(code, encoding="utf-8")
        out_path = td_path / "out_artifact"
        dump_dir = td_path / "mir_dumps"
        cmd = [
            rustc,
            f"--edition={edition}",
            f"--crate-type={crate_type}",
            "--error-format=json",
            str(src),
            "-o",
            str(out_path),
        ]
        if dump_mir_filter is not None:
            dump_dir.mkdir(parents=True, exist_ok=True)
            cmd.extend([f"-Zdump-mir={dump_mir_filter}", f"-Zdump-mir-dir={dump_dir}"])
        cmd.extend(extra_args)

        proc = subprocess.run(cmd, capture_output=True, text=True)
        diags: list[dict[str, Any]] = []
        for line in proc.stderr.splitlines():
            line = line.strip()
            if not line:
                continue
            try:
                obj = json.loads(line)
            except json.JSONDecodeError:
                continue
            if obj.get("$message_type") == "diagnostic":
                code_obj = obj.get("code")
                spans = obj.get("spans") or []
                prim_line = next(
                    (s.get("line_start") for s in spans if s.get("is_primary")),
                    None,
                )
                diags.append(
                    {
                        "level": obj.get("level"),
                        "code": code_obj.get("code") if isinstance(code_obj, dict) else None,
                        "message": sanitize_tmp_paths(str(obj.get("message", "")), td),
                        "line": prim_line,
                    }
                )

        mir_text = None
        if capture_mir_output and out_path.exists():
            mir_text = sanitize_tmp_paths(out_path.read_text(encoding="utf-8", errors="replace"), td)

        dump_files: dict[str, str] = {}
        if dump_mir_filter is not None and dump_dir.exists():
            for p in sorted(dump_dir.glob("*.mir")):
                dump_files[p.name] = sanitize_tmp_paths(p.read_text(encoding="utf-8", errors="replace"), td)

        return {
            "rc": proc.returncode,
            "diagnostics": diags,
            "artifact_exists": out_path.exists(),
            "mir_output": mir_text,
            "dump_files": dump_files,
        }


def extract_fn_mir(full_mir: str, fn_name: str) -> str:
    m = re.search(rf"(^fn {re.escape(fn_name)}\([^\n]*\{{.*?\n\}})", full_mir, re.S | re.M)
    if m:
        return m.group(1)
    raise RuntimeError(f"failed to extract MIR body for function {fn_name!r}")


def count_mir_features(fn_mir: str) -> dict[str, int]:
    return {
        "basic_blocks": len(re.findall(r"\bbb\d+(?: \(cleanup\))?:", fn_mir)),
        "cleanup_blocks": len(re.findall(r"\bbb\d+ \(cleanup\):", fn_mir)),
        "return_terminators": len(re.findall(r"\breturn;", fn_mir)),
        "goto_terminators": len(re.findall(r"\bgoto -> bb\d+;", fn_mir)),
        "unreachable_terminators": len(re.findall(r"\bunreachable;", fn_mir)),
        "terminate_terminators": len(re.findall(r"\bterminate\([^)]+\);", fn_mir)),
    }


def run_suite_a_liveness(rustc: str) -> dict[str, Any]:
    suite: dict[str, Any] = {}

    # A1..A4: Closure vs Coroutine vs CoroutineClosure (AsyncFnMut & AsyncFnOnce)
    a1_sync = """\
pub fn sync_closure_dead_capture() {
    let mut u_sync = 10u32;
    let _c = move || {
        u_sync = 30;
    };
}
"""
    a2_coro = """\
pub fn async_block_dead_capture() {
    let mut u_block = 10u32;
    let _f = async move {
        u_block = 30;
    };
}
"""
    a3_async_fnmut = """\
pub fn async_fnmut_dead_capture() {
    let mut u_async = 10u32;
    let _c = async move || {
        u_async = 30;
    };
}
"""
    a4_async_fnonce = """\
pub fn async_fnonce_dead_capture() {
    let mut u_async_once = 10u32;
    let consume = String::from("x");
    let _c = async move || {
        drop(consume);
        u_async_once = 30;
    };
}
"""
    a4_sync_fnonce = """\
pub fn sync_fnonce_dead_capture() {
    let mut u_sync_once = 10u32;
    let consume = String::from("x");
    let _c = move || {
        drop(consume);
        u_sync_once = 30;
    };
}
"""

    r1 = run_rustc(rustc, a1_sync, ["--emit=metadata"])
    r2 = run_rustc(rustc, a2_coro, ["--emit=metadata"])
    r3 = run_rustc(rustc, a3_async_fnmut, ["--emit=metadata"], dump_mir_filter="built")
    r4a = run_rustc(rustc, a4_async_fnonce, ["--emit=metadata"], dump_mir_filter="built")
    r4s = run_rustc(rustc, a4_sync_fnonce, ["--emit=metadata"])

    suite["A1_sync_move_closure"] = {
        "rc": r1["rc"],
        "warning_count": sum(1 for d in r1["diagnostics"] if d["level"] == "warning" and d["code"] is not None),
        "diagnostics": r1["diagnostics"],
    }
    suite["A2_async_move_block_coroutine"] = {
        "rc": r2["rc"],
        "warning_count": sum(1 for d in r2["diagnostics"] if d["level"] == "warning" and d["code"] is not None),
        "diagnostics": r2["diagnostics"],
    }
    suite["A3_async_move_fnmut_coroutine_closure"] = {
        "rc": r3["rc"],
        "warning_count": sum(1 for d in r3["diagnostics"] if d["level"] == "warning" and d["code"] is not None),
        "diagnostics": r3["diagnostics"],
        "built_mir_bodies": sorted(r3["dump_files"].keys()),
        "wrapper_mir_has_mut_borrow": any(
            "&mut ((*_1).0: u32)" in txt for name, txt in r3["dump_files"].items() if "{closure#0}.1-" in name
        ),
        "inner_coro_captures_by_mut_ref": any(
            "(*(_1.0: &mut u32)) = const 30_u32" in txt
            for name, txt in r3["dump_files"].items()
            if "{closure#0}-{closure#0}" in name
        ),
        "synthetic_by_move_body_present": any(
            "{synthetic#0}" in name for name in r3["dump_files"]
        ),
    }
    suite["A4_async_move_fnonce_vs_sync_fnonce"] = {
        "async_fnonce_rc": r4a["rc"],
        "async_fnonce_warning_count": sum(
            1 for d in r4a["diagnostics"] if d["level"] == "warning" and d["code"] is not None
        ),
        "async_fnonce_diagnostics": r4a["diagnostics"],
        "async_fnonce_inner_captures_by_value": any(
            "(_1.1: u32) = const 30_u32" in txt
            for name, txt in r4a["dump_files"].items()
            if "{closure#0}-{closure#0}" in name
        ),
        "sync_fnonce_rc": r4s["rc"],
        "sync_fnonce_warning_count": sum(
            1 for d in r4s["diagnostics"] if d["level"] == "warning" and d["code"] is not None
        ),
        "sync_fnonce_diagnostics": r4s["diagnostics"],
    }

    # A5: FnMut Return/UnwindResume -> START_BLOCK loop closure vs FnOnce
    a5_fnmut_vs_fnonce = """\
pub fn fnmut_normal_return_loop() -> impl FnMut() -> u32 {
    let mut acc = 0u32;
    move || {
        let prev = acc;
        acc = prev + 1;
        prev
    }
}

pub fn fnmut_unwind_resume_loop() -> impl FnMut(bool) -> u32 {
    let mut acc = 0u32;
    move |boom| {
        let prev = acc;
        if boom {
            acc = prev + 10;
            panic!("unwind after updating state");
        }
        prev
    }
}

pub fn fnonce_trailing_write_dead() -> impl FnOnce() -> u32 {
    let mut acc = 0u32;
    let owned = String::from("consume");
    move || {
        drop(owned);
        let prev = acc;
        acc = prev + 1;
        prev
    }
}
"""
    r5 = run_rustc(rustc, a5_fnmut_vs_fnonce, ["--emit=metadata"])
    suite["A5_fnmut_loop_closure_vs_fnonce"] = {
        "rc": r5["rc"],
        "warning_count": sum(1 for d in r5["diagnostics"] if d["level"] == "warning" and d["code"] is not None),
        "diagnostics": r5["diagnostics"],
    }

    # A6: Self-assignments (+=, /=, *p +=), FakeRead/merge_guards, maybe_drop_guard, by-ref diverging Call
    a6_edge = """\
pub fn self_assign_add() {
    let mut x = 1u32;
    x += 2;
}

pub fn self_assign_signed_div() {
    let mut y = 10i32;
    y /= 2;
}

pub fn self_assign_indirect(p: &mut u32) {
    *p += 2;
}

pub fn match_guard_used_only_in_guard(v: i32) -> i32 {
    match v {
        x if x > 2 => 1,
        _ => 0,
    }
}

pub struct DropGuard(pub u32);
impl Drop for DropGuard {
    fn drop(&mut self) {}
}

pub fn drop_guard_field_vs_direct() {
    let mut g_field = DropGuard(1);
    g_field.0 = 2;

    let mut g_direct = DropGuard(1);
    g_direct = DropGuard(2);
}

fn diverge() -> ! {
    loop {}
}

pub fn by_ref_capture_before_diverging_call(out: &mut u32) {
    let mut c = || {
        *out = 99;
        diverge()
    };
    c();
}
"""
    r6 = run_rustc(rustc, a6_edge, ["--emit=metadata"])
    suite["A6_self_assign_guards_drop_guard_and_by_ref_diverge"] = {
        "rc": r6["rc"],
        "warning_count": sum(1 for d in r6["diagnostics"] if d["level"] == "warning" and d["code"] is not None),
        "diagnostics": r6["diagnostics"],
    }

    return suite


def run_suite_b_mentioned_items(rustc: str) -> dict[str, Any]:
    suite: dict[str, Any] = {}

    patterns: dict[str, str] = {
        "1a_call_dead_const_prop": """\
#[inline(never)]
fn trigger_pme<const N: usize>() -> usize {
    const { assert!(N > 0, "CALL_CONST_PROP_PME"); N }
}
pub fn f() -> usize {
    let x = 2usize + 2usize;
    if x == 5 { trigger_pme::<0>() } else { 1 }
}
fn main() { let _ = f(); }
""",
        "1b_call_dead_if_false": """\
#[inline(never)]
fn trigger_pme<const N: usize>() -> usize {
    const { assert!(N > 0, "CALL_IF_FALSE_PME"); N }
}
fn main() {
    if false { let _ = trigger_pme::<0>(); }
}
""",
        "2_drop_dead": """\
struct DropBoom<const N: usize>;
impl<const N: usize> Drop for DropBoom<N> {
    fn drop(&mut self) {
        const { assert!(N > 0, "DROP_PME"); }
    }
}
fn main() {
    let x = 2usize + 2usize;
    if x == 5 { let _d = DropBoom::<0>; }
}
""",
        "3_inline_asm_symfn_dead": """\
extern "C" fn asm_pme<const N: usize>() {
    const { assert!(N > 0, "ASM_SYMFN_PME"); }
}
fn main() {
    let x = 2usize + 2usize;
    if x == 5 {
        unsafe { core::arch::asm!("/* {} */", sym asm_pme::<0>); }
    }
}
""",
        "4_unsize_vtable_dead": """\
pub trait Boom { fn boom(&self) -> usize; }
pub struct S<const N: usize>;
impl<const N: usize> Boom for S<N> {
    fn boom(&self) -> usize {
        const { assert!(N > 0, "VTABLE_PME"); N }
    }
}
fn main() {
    let x = 2usize + 2usize;
    if x == 5 {
        let s = S::<0>;
        let _d: &dyn Boom = &s;
    }
}
""",
        "5_closure_fnptr_dead": """\
fn trigger_pme<const N: usize>() -> usize {
    const { assert!(N > 0, "CLOSURE_FNPTR_PME"); N }
}
fn main() {
    let x = 2usize + 2usize;
    if x == 5 {
        let _fp: fn() -> usize = || trigger_pme::<0>();
    }
}
""",
        "6_reify_fnptr_dead": """\
fn trigger_pme<const N: usize>() -> usize {
    const { assert!(N > 0, "REIFY_FNPTR_PME"); N }
}
fn main() {
    let x = 2usize + 2usize;
    if x == 5 {
        let _fp: fn() -> usize = trigger_pme::<0>;
    }
}
""",
        "4b_unsize_array_to_slice_control": """\
fn main() {
    let x = 2usize + 2usize;
    if x == 5 {
        let arr = [1u8; 4];
        let _s: &[u8] = &arr;
    }
}
""",
    }

    pattern_results: dict[str, Any] = {}
    for name, code in patterns.items():
        r_meta = run_rustc(rustc, code, ["--emit=metadata", "-Copt-level=3", "-Zmir-opt-level=4"], crate_type="bin")
        r_o0 = run_rustc(rustc, code, ["--emit=obj", "-Copt-level=0", "-Zmir-opt-level=0"], crate_type="bin")
        r_o3 = run_rustc(rustc, code, ["--emit=obj", "-Copt-level=3", "-Zmir-opt-level=4"], crate_type="bin")
        err_o3 = next((d["message"] for d in r_o3["diagnostics"] if d["level"] == "error"), None)
        pattern_results[name] = {
            "emit_metadata_rc": r_meta["rc"],
            "emit_obj_o0_rc": r_o0["rc"],
            "emit_obj_o3_mir4_rc": r_o3["rc"],
            "o3_first_error": err_o3,
        }
    suite["B1_six_visitor_patterns_post_dce_enforcement"] = pattern_results

    # Verify MIR before vs after optimization on 1a_call_dead_const_prop
    r_mir = run_rustc(
        rustc,
        patterns["1a_call_dead_const_prop"],
        ["--emit=mir", "-Copt-level=3", "-Zmir-opt-level=4"],
        crate_type="bin",
        dump_mir_filter="f",
        capture_mir_output=True,
    )
    post_cleanup = next(
        (v for k, v in r_mir["dump_files"].items() if "runtime-post-cleanup.after.mir" in k),
        "",
    )
    optimized = next(
        (v for k, v in r_mir["dump_files"].items() if "runtime-optimized.after.mir" in k),
        "",
    )
    suite["B2_dead_call_present_before_opt_absent_after_opt"] = {
        "rc": r_mir["rc"],
        "post_cleanup_contains_trigger_pme": "trigger_pme::<0>" in post_cleanup,
        "optimized_contains_trigger_pme": "trigger_pme::<0>" in optimized,
        "optimized_mir_body": optimized.strip(),
    }

    # B3: Mentioned-only items are NOT added to usage_map / codegen
    # Verify via --emit=llvm-ir (dead_extern_caller absent at -O3/-Zmir-opt-level=4, present at -O0/-Zmir-opt-level=0)
    # AND full binary link succeeds at -O3/-Zmir-opt-level=4 despite referencing an undefined extern "C" symbol!
    code_no_codegen = """\
unsafe extern "C" {
    fn nonexistent_extern_symbol_for_mentioned_test() -> usize;
}
#[inline(never)]
fn dead_extern_caller() -> usize {
    unsafe { nonexistent_extern_symbol_for_mentioned_test() }
}
fn main() {
    let x = 2usize + 2usize;
    if x == 5 {
        let _ = dead_extern_caller();
    }
}
"""
    r_link_o3 = run_rustc(rustc, code_no_codegen, ["-Copt-level=3", "-Zmir-opt-level=4"], crate_type="bin")
    r_link_o0 = run_rustc(rustc, code_no_codegen, ["-Copt-level=0", "-Zmir-opt-level=0"], crate_type="bin")
    r_ll_o3 = run_rustc(
        rustc, code_no_codegen, ["--emit=llvm-ir", "-Copt-level=3", "-Zmir-opt-level=4"], crate_type="bin", capture_mir_output=True
    )
    r_ll_o0 = run_rustc(
        rustc, code_no_codegen, ["--emit=llvm-ir", "-Copt-level=0", "-Zmir-opt-level=0"], crate_type="bin", capture_mir_output=True
    )
    suite["B3_mentioned_only_skips_codegen_and_linking"] = {
        "o3_mir4_link_rc": r_link_o3["rc"],
        "o3_mir4_binary_created": r_link_o3["artifact_exists"],
        "o3_mir4_llvm_ir_contains_extern_sym": "nonexistent_extern_symbol_for_mentioned_test" in (r_ll_o3["mir_output"] or ""),
        "o0_mir0_link_rc": r_link_o0["rc"],
        "o0_mir0_llvm_ir_contains_extern_sym": "nonexistent_extern_symbol_for_mentioned_test" in (r_ll_o0["mir_output"] or ""),
    }

    # B4: rlib cross_crate_inlinable root-selection seam (opt-level flip!)
    code_rlib_default = """\
#[inline(never)]
fn trigger_pme<const N: usize>() -> usize {
    const { assert!(N > 0, "RLIB_SEAM_PME"); N }
}
pub fn f() -> usize {
    let x = 2usize + 2usize;
    if x == 5 { trigger_pme::<0>() } else { 1 }
}
"""
    code_rlib_inline_never = """\
#[inline(never)]
fn trigger_pme<const N: usize>() -> usize {
    const { assert!(N > 0, "RLIB_SEAM_PME"); N }
}
#[inline(never)]
pub fn f() -> usize {
    let x = 2usize + 2usize;
    if x == 5 { trigger_pme::<0>() } else { 1 }
}
"""
    suite["B4_rlib_cross_crate_inlinable_opt_level_seam"] = {
        "pub_fn_default_o0_mir0_rc": run_rustc(
            rustc, code_rlib_default, ["--emit=obj", "-Copt-level=0", "-Zmir-opt-level=0"], crate_type="lib"
        )["rc"],
        "pub_fn_default_o3_mir4_rc": run_rustc(
            rustc, code_rlib_default, ["--emit=obj", "-Copt-level=3", "-Zmir-opt-level=4"], crate_type="lib"
        )["rc"],
        "pub_fn_default_o3_mir4_threshold0_rc": run_rustc(
            rustc,
            code_rlib_default,
            ["--emit=obj", "-Copt-level=3", "-Zmir-opt-level=4", "-Zcross-crate-inline-threshold=0"],
            crate_type="lib",
        )["rc"],
        "pub_fn_inline_never_o0_mir0_rc": run_rustc(
            rustc, code_rlib_inline_never, ["--emit=obj", "-Copt-level=0", "-Zmir-opt-level=0"], crate_type="lib"
        )["rc"],
        "pub_fn_inline_never_o3_mir4_rc": run_rustc(
            rustc, code_rlib_inline_never, ["--emit=obj", "-Copt-level=3", "-Zmir-opt-level=4"], crate_type="lib"
        )["rc"],
    }

    return suite


def run_suite_c_multiple_returns(rustc: str) -> dict[str, Any]:
    suite: dict[str, Any] = {}

    code_mrt = """\
#[inline(never)]
pub fn multi_return(x: u32) -> u32 {
    if x == 0 {
        return 10;
    } else if x == 1 {
        return 20;
    } else {
        return x.wrapping_add(30);
    }
}

pub struct EpilogueDrop(pub u32);
impl Drop for EpilogueDrop {
    #[inline(never)]
    fn drop(&mut self) {
        core::hint::black_box(self.0);
    }
}

#[inline(never)]
pub fn multi_return_with_shared_drop(x: u32) -> u32 {
    let _guard = EpilogueDrop(x);
    if x == 0 {
        10
    } else if x == 1 {
        20
    } else {
        x.wrapping_add(30)
    }
}
"""
    for label, flags in [
        ("mir_opt_3", ["-Zmir-opt-level=3", "--emit=mir"]),
        ("mir_opt_4", ["-Zmir-opt-level=4", "--emit=mir"]),
        ("mir_opt_2_explicit_enable", ["-Zmir-opt-level=2", "-Zmir-enable-passes=+MultipleReturnTerminators", "--emit=mir"]),
        ("mir_opt_4_explicit_disable", ["-Zmir-opt-level=4", "-Zmir-enable-passes=-MultipleReturnTerminators", "--emit=mir"]),
    ]:
        res = run_rustc(rustc, code_mrt, flags, capture_mir_output=True)
        mir = res["mir_output"] or ""
        fn_simple = extract_fn_mir(mir, "multi_return")
        fn_drop = extract_fn_mir(mir, "multi_return_with_shared_drop")
        suite[label] = {
            "rc": res["rc"],
            "multi_return": count_mir_features(fn_simple),
            "multi_return_with_shared_drop": count_mir_features(fn_drop),
        }

    return suite


def run_suite_d_mir_patch(rustc: str) -> dict[str, Any]:
    suite: dict[str, Any] = {}

    # D1: Bipartite cleanup vs non-cleanup terminators (UnwindTerminate in cleanup, Unreachable in non-cleanup)
    code_bipartite = """\
pub struct Guard(pub u32);
impl Drop for Guard {
    #[inline(never)]
    fn drop(&mut self) {
        core::hint::black_box(self.0);
    }
}

pub extern "C" fn nounwind_with_drop(x: bool) -> u32 {
    let _g = Guard(7);
    if x {
        panic!("boom");
    }
    42
}

pub fn normal_unreachable_branch(x: Option<u32>) -> u32 {
    match x {
        Some(v) => v,
        None => unsafe { core::hint::unreachable_unchecked() },
    }
}
"""
    res_bi = run_rustc(rustc, code_bipartite, ["-Zmir-opt-level=2", "--emit=mir"], capture_mir_output=True)
    mir_bi = res_bi["mir_output"] or ""
    fn_nounwind = extract_fn_mir(mir_bi, "nounwind_with_drop")
    fn_unreach = extract_fn_mir(mir_bi, "normal_unreachable_branch")
    suite["D1_bipartite_cleanup_and_unreachable"] = {
        "rc": res_bi["rc"],
        "nounwind_with_drop_counts": count_mir_features(fn_nounwind),
        "normal_unreachable_counts": count_mir_features(fn_unreach),
        "nounwind_has_cleanup_terminate_abi": "terminate(abi);" in fn_nounwind,
        "normal_unreachable_has_non_cleanup_unreachable": (
            "unreachable;" in fn_unreach and "(cleanup)" not in fn_unreach
        ),
    }

    # D2: MirPatch stable-ordered same-location insertion (add_assign + add_statement at terminator_loc)
    code_stable_ins = """\
pub enum Never {}

#[inline(never)]
pub fn stable_insertion_assume(flag: bool, x: u32, n: Option<Never>) -> u32 {
    if flag {
        let a = x ^ 0x55AA_u32;
        let b = a | 0x0F_u32;
        if let Some(never) = n {
            let _c = b & 0xFF_u32;
            match never {}
        }
        b
    } else {
        x
    }
}
"""
    res_si = run_rustc(
        rustc,
        code_stable_ins,
        ["-Zmir-opt-level=2", "--emit=mir"],
        dump_mir_filter="UnreachablePropagation",
        capture_mir_output=True,
    )
    before_si = next((v for k, v in res_si["dump_files"].items() if "UnreachablePropagation.before.mir" in k), "")
    after_si = next((v for k, v in res_si["dump_files"].items() if "UnreachablePropagation.after.mir" in k), "")
    eq_m = re.search(r"\bEq\(", after_si)
    assume_m = re.search(r"\bassume\(", after_si)
    suite["D2_mir_patch_stable_insertion_order"] = {
        "rc": res_si["rc"],
        "before_has_assume": bool(re.search(r"\bassume\(", before_si)),
        "after_inserts_eq_then_assume_in_queue_order": (
            eq_m is not None and assume_m is not None and eq_m.start() < assume_m.start()
        ),
        "before_mir_excerpt": before_si.strip(),
        "after_mir_excerpt": after_si.strip(),
    }

    # D3: MirPatch::apply clearing bb.statements when patch_terminator(bb, Unreachable) fires!
    code_clear_stmt = """\
pub enum Never {}

#[inline(never)]
pub fn clear_stmts_on_unreachable_patch(flag: bool, x: u32, n: Never) -> u32 {
    let a = x ^ 0x55AA_u32;
    let b = a | 0x0F_u32;
    if flag {
        let _y = b & 1;
        match n {}
    } else {
        let _z = b & 2;
        match n {}
    }
}
"""
    res_cs = run_rustc(
        rustc,
        code_clear_stmt,
        ["-Zmir-opt-level=2", "--emit=mir"],
        dump_mir_filter="UnreachablePropagation",
        capture_mir_output=True,
    )
    before_cs = next((v for k, v in res_cs["dump_files"].items() if "UnreachablePropagation.before.mir" in k), "")
    after_cs = next((v for k, v in res_cs["dump_files"].items() if "UnreachablePropagation.after.mir" in k), "")
    suite["D3_mir_patch_unreachable_statement_clearing"] = {
        "rc": res_cs["rc"],
        "before_bb0_has_bitxor_and_bitor": ("BitXor(" in before_cs and "BitOr(" in before_cs),
        "after_bb0_cleared_to_empty_unreachable": (
            "BitXor(" not in after_cs
            and "BitOr(" not in after_cs
            and "bb0: {\n        unreachable;\n    }" in after_cs
        ),
        "before_mir_excerpt": before_cs.strip(),
        "after_mir_excerpt": after_cs.strip(),
    }

    return suite


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=None, help="Optional JSON output file path")
    args = parser.parse_args()

    rustc = find_rustc()
    ver = subprocess.run([rustc, "-Vv"], capture_output=True, text=True, check=True).stdout.strip()

    report = {
        "rustc_version": ver,
        "suite_a_liveness": run_suite_a_liveness(rustc),
        "suite_b_mentioned_items": run_suite_b_mentioned_items(rustc),
        "suite_c_multiple_return_terminators": run_suite_c_multiple_returns(rustc),
        "suite_d_mir_patch": run_suite_d_mir_patch(rustc),
    }

    text = json.dumps(report, indent=2, sort_keys=False) + "\n"
    if args.out is not None:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(text, encoding="utf-8")
    else:
        print(text, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
