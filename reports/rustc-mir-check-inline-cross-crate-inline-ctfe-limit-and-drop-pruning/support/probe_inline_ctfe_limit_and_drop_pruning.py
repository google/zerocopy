#!/usr/bin/env python3
"""Differential live rustc probe for:
  1. CtfeLimit (dominator back-edge omission on irreducible CFGs vs. SimplifyCfg collapse)
  2. CheckForceInline (definition-site rejection matrix and priority order)
  3. CrossCrateInline (priority lattice, CostChecker intrinsic-call exemption, f16 bypass, thresholds, incremental gate)
  4. RemoveUninitDrops (const_precise_live_drops pre-const-check pruning, struct partial moves, opt-level independence)
  5. RemoveUnneededDrops (post-inline generic instantiation drop elimination + simplify_cfg)

Produces self-contained, path-sanitized JSON evidence.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import tempfile
from pathlib import Path
from typing import Any


PKG_DIR = Path(__file__).resolve().parent
OUT_JSON = PKG_DIR / "probe_inline_ctfe_limit_and_drop_pruning_results.json"


def sanitize_text(text: str, tmp_root: str) -> str:
    text = text.replace(tmp_root, "<TMP>")
    home = os.path.expanduser("~")
    if home:
        text = text.replace(home, "<HOME>")
    return text


def run_rustc(
    args: list[str],
    cwd: Path,
    tmp_root: str,
    timeout: float = 30.0,
) -> dict[str, Any]:
    env = os.environ.copy()
    cargo_bin = os.path.expanduser("~/.cargo/bin")
    env["PATH"] = f"{cargo_bin}:{env.get('PATH', '')}"
    try:
        proc = subprocess.run(
            ["rustc", *args],
            cwd=str(cwd),
            env=env,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        return {
            "timed_out": False,
            "rc": proc.returncode,
            "stdout": sanitize_text(proc.stdout, tmp_root),
            "stderr": sanitize_text(proc.stderr, tmp_root),
        }
    except subprocess.TimeoutExpired as exc:
        out = exc.stdout.decode("utf-8", errors="replace") if isinstance(exc.stdout, bytes) else (exc.stdout or "")
        err = exc.stderr.decode("utf-8", errors="replace") if isinstance(exc.stderr, bytes) else (exc.stderr or "")
        return {
            "timed_out": True,
            "rc": None,
            "timeout_sec": timeout,
            "stdout": sanitize_text(out, tmp_root),
            "stderr": sanitize_text(err, tmp_root),
        }


def collect_mir_dumps(dump_dir: Path, pattern: str) -> dict[str, str]:
    result: dict[str, str] = {}
    if not dump_dir.exists():
        return result
    rx = re.compile(pattern)
    for p in sorted(dump_dir.iterdir()):
        if p.is_file() and rx.search(p.name):
            result[p.name] = p.read_text(encoding="utf-8", errors="replace")
    return result


def count_basic_blocks(mir_text: str) -> int:
    return len(re.findall(r"^\s*bb\d+\b", mir_text, flags=re.MULTILINE))


def probe_ctfe_limit(base: Path, tmp_root: str) -> dict[str, Any]:
    out: dict[str, Any] = {}

    # 1a. Reducible bounded loop (dialect = "built")
    d = base / "ctfe_reducible_bounded"
    d.mkdir()
    src = d / "reducible_bounded.rs"
    src.write_text(
        """#![feature(custom_mir, core_intrinsics)]
#![deny(long_running_const_eval)]
extern crate core;
use core::intrinsics::mir::*;

#[custom_mir(dialect = "built")]
pub const fn reducible_loop() -> u32 {
    mir! {
        let x: u32;
        {
            x = 0_u32;
            Goto(bb1)
        }
        bb1 = {
            x = x + 1_u32;
            match x {
                10_u32 => bb2,
                _ => bb1,
            }
        }
        bb2 = {
            RET = x;
            Return()
        }
    }
}

pub const REDUCIBLE_RES: u32 = reducible_loop();
""",
        encoding="utf-8",
    )
    dump_dir = d / "mir"
    res = run_rustc(
        [
            "--crate-type=lib",
            "--crate-name=ctfe_red_bounded",
            "-Zdump-mir=CtfeLimit",
            f"-Zdump-mir-dir={dump_dir}",
            str(src),
            "-o",
            str(d / "lib.rlib"),
        ],
        d,
        tmp_root,
    )
    dumps = collect_mir_dumps(dump_dir, r"reducible_loop.*CtfeLimit\.after\.mir$")
    after_key = next(iter(dumps), None)
    after_text = dumps[after_key] if after_key else ""
    out["reducible_bounded_built"] = {
        "rc": res["rc"],
        "timed_out": res["timed_out"],
        "stderr": res["stderr"],
        "const_eval_counter_count": after_text.count("const_eval_counter") + after_text.count("ConstEvalCounter"),
        "after_mir_file": after_key,
        "after_mir": after_text,
    }

    # 1b. Infinite reducible loop (dialect = "built", tiny limit -> fast deny error)
    d = base / "ctfe_reducible_inf"
    d.mkdir()
    src = d / "reducible_inf.rs"
    src.write_text(
        """#![feature(custom_mir, core_intrinsics)]
#![deny(long_running_const_eval)]
extern crate core;
use core::intrinsics::mir::*;

#[custom_mir(dialect = "built")]
pub const fn reducible_inf() -> u32 {
    mir! {
        let x: u32;
        {
            x = 0_u32;
            Goto(bb1)
        }
        bb1 = {
            x = x + 1_u32;
            Goto(bb1)
        }
    }
}

pub const REDUCIBLE_INF: u32 = reducible_inf();
""",
        encoding="utf-8",
    )
    dump_dir = d / "mir"
    res = run_rustc(
        [
            "--crate-type=lib",
            "--crate-name=ctfe_red_inf",
            "-Ztiny-const-eval-limit",
            "-Zdump-mir=CtfeLimit",
            f"-Zdump-mir-dir={dump_dir}",
            str(src),
            "-o",
            str(d / "lib.rlib"),
        ],
        d,
        tmp_root,
        timeout=5.0,
    )
    dumps = collect_mir_dumps(dump_dir, r"reducible_inf.*CtfeLimit\.after\.mir$")
    after_key = next(iter(dumps), None)
    after_text = dumps[after_key] if after_key else ""
    out["reducible_infinite_caught"] = {
        "rc": res["rc"],
        "timed_out": res["timed_out"],
        "caught_long_running_lint": "constant evaluation is taking a long time" in res["stderr"],
        "const_eval_counter_count": after_text.count("const_eval_counter") + after_text.count("ConstEvalCounter"),
        "stderr": res["stderr"],
        "after_mir": after_text,
    }

    # 1c. Bounded 2-header irreducible loop (dialect = "built", 50 iters > tiny limit 20!)
    d = base / "ctfe_irr_bounded"
    d.mkdir()
    src = d / "irr_bounded.rs"
    src.write_text(
        """#![feature(custom_mir, core_intrinsics)]
#![deny(long_running_const_eval)]
extern crate core;
use core::intrinsics::mir::*;

#[custom_mir(dialect = "built")]
pub const fn built_irreducible_bounded(b: bool) -> u32 {
    mir! {
        let x: u32;
        {
            x = 0_u32;
            match b {
                true => bb1,
                _ => bb2,
            }
        }
        bb1 = {
            x = x + 1_u32;
            Goto(bb2)
        }
        bb2 = {
            x = x + 1_u32;
            match x {
                100_u32 => bb3,
                _ => bb1,
            }
        }
        bb3 = {
            RET = x;
            Return()
        }
    }
}

pub const BUILT_BOUNDED: u32 = built_irreducible_bounded(true);
""",
        encoding="utf-8",
    )
    dump_dir = d / "mir"
    res = run_rustc(
        [
            "--crate-type=lib",
            "--crate-name=ctfe_irr_bounded",
            "-Ztiny-const-eval-limit",
            "-Zdump-mir=CtfeLimit",
            f"-Zdump-mir-dir={dump_dir}",
            str(src),
            "-o",
            str(d / "lib.rlib"),
        ],
        d,
        tmp_root,
        timeout=5.0,
    )
    dumps = collect_mir_dumps(dump_dir, r"built_irreducible_bounded.*CtfeLimit\.after\.mir$")
    after_key = next(iter(dumps), None)
    after_text = dumps[after_key] if after_key else ""
    out["irreducible_bounded_built"] = {
        "rc": res["rc"],
        "timed_out": res["timed_out"],
        "stderr": res["stderr"],
        "const_eval_counter_count": after_text.count("const_eval_counter") + after_text.count("ConstEvalCounter"),
        "after_mir_file": after_key,
        "after_mir": after_text,
    }

    # 1d. Collapsible empty-body infinite irreducible loop (dialect = "built")
    d = base / "ctfe_irr_collapsible"
    d.mkdir()
    src = d / "irr_collapsible.rs"
    src.write_text(
        """#![feature(custom_mir, core_intrinsics)]
#![deny(long_running_const_eval)]
extern crate core;
use core::intrinsics::mir::*;

#[custom_mir(dialect = "built")]
pub const fn collapsible_inf_irr(b: bool) -> u32 {
    mir! {
        {
            match b {
                true => bb1,
                _ => bb2,
            }
        }
        bb1 = {
            Goto(bb2)
        }
        bb2 = {
            Goto(bb1)
        }
    }
}

pub const COLLAPSIBLE_INF: u32 = collapsible_inf_irr(true);
""",
        encoding="utf-8",
    )
    dump_dir = d / "mir"
    res = run_rustc(
        [
            "--crate-type=lib",
            "--crate-name=ctfe_irr_collapsible",
            "-Ztiny-const-eval-limit",
            "-Zdump-mir=SimplifyCfg|CtfeLimit",
            f"-Zdump-mir-dir={dump_dir}",
            str(src),
            "-o",
            str(d / "lib.rlib"),
        ],
        d,
        tmp_root,
        timeout=5.0,
    )
    dumps = collect_mir_dumps(dump_dir, r"collapsible_inf_irr.*(SimplifyCfg-initial|CtfeLimit)\.(before|after)\.mir$")
    ctfe_after = next((v for k, v in dumps.items() if "CtfeLimit.after.mir" in k), "")
    simp_before = next((v for k, v in dumps.items() if "SimplifyCfg-initial.before.mir" in k), "")
    simp_after = next((v for k, v in dumps.items() if "SimplifyCfg-initial.after.mir" in k), "")
    out["irreducible_collapsible_built_caught"] = {
        "rc": res["rc"],
        "timed_out": res["timed_out"],
        "caught_long_running_lint": "constant evaluation is taking a long time" in res["stderr"],
        "const_eval_counter_count": ctfe_after.count("const_eval_counter") + ctfe_after.count("ConstEvalCounter"),
        "stderr": res["stderr"],
        "simplify_initial_before": simp_before,
        "simplify_initial_after": simp_after,
        "ctfe_limit_after": ctfe_after,
    }

    # 1e. Non-collapsible 2-header infinite irreducible loop (dialect = "built") -> hangs!
    d = base / "ctfe_irr_noncollapsible"
    d.mkdir()
    src = d / "irr_noncollapsible.rs"
    src.write_text(
        """#![feature(custom_mir, core_intrinsics)]
#![deny(long_running_const_eval)]
extern crate core;
use core::intrinsics::mir::*;

#[custom_mir(dialect = "built")]
pub const fn noncollapsible_inf_irr(b: bool) -> u32 {
    mir! {
        let x: u32;
        {
            x = 0_u32;
            match b {
                true => bb1,
                _ => bb2,
            }
        }
        bb1 = {
            x = x + 1_u32;
            Goto(bb2)
        }
        bb2 = {
            x = x + 3_u32;
            Goto(bb1)
        }
    }
}

pub const HANG: u32 = noncollapsible_inf_irr(true);
""",
        encoding="utf-8",
    )
    dump_dir = d / "mir"
    res = run_rustc(
        [
            "--crate-type=lib",
            "--crate-name=ctfe_irr_noncollapsible",
            "-Ztiny-const-eval-limit",
            "-Zdump-mir=CtfeLimit",
            f"-Zdump-mir-dir={dump_dir}",
            str(src),
            "-o",
            str(d / "lib.rlib"),
        ],
        d,
        tmp_root,
        timeout=2.5,
    )
    dumps = collect_mir_dumps(dump_dir, r"noncollapsible_inf_irr.*CtfeLimit\.after\.mir$")
    after_key = next(iter(dumps), None)
    after_text = dumps[after_key] if after_key else ""
    out["irreducible_noncollapsible_built_hang"] = {
        "rc": res["rc"],
        "timed_out": res["timed_out"],
        "timeout_sec": res.get("timeout_sec"),
        "const_eval_counter_count": after_text.count("const_eval_counter") + after_text.count("ConstEvalCounter"),
        "after_mir_file": after_key,
        "after_mir": after_text,
        "stderr": res["stderr"],
    }

    return out


def probe_check_force_inline(base: Path, tmp_root: str) -> dict[str, Any]:
    cases = {
        "plain_ok": """#![feature(rustc_attrs)]
#[rustc_force_inline]
pub fn plain_forced(x: u32) -> u32 { x.wrapping_add(1) }
""",
        "cold_err": """#![feature(rustc_attrs)]
#[rustc_force_inline]
#[cold]
pub fn cold_forced() -> u32 { 1 }
""",
        "no_mir_inline_err": """#![feature(rustc_attrs)]
#[rustc_force_inline]
#[rustc_no_mir_inline]
pub fn no_mir_forced() -> u32 { 1 }
""",
        "tailcall_err": """#![feature(rustc_attrs, explicit_tail_calls)]
fn helper(x: u32) -> u32 { x.wrapping_add(1) }
#[rustc_force_inline]
pub fn tail_forced(x: u32) -> u32 { become helper(x) }
""",
        "c_variadic_err": """#![feature(rustc_attrs, c_variadic)]
#[rustc_force_inline]
pub unsafe extern "C" fn var_forced(_x: u32, mut _ap: ...) -> u32 { 0 }
""",
        "intrinsic_without_body_err": """#![feature(rustc_attrs, intrinsics)]
#[rustc_intrinsic]
#[rustc_force_inline]
pub unsafe fn unreachable() -> !;
""",
        "priority_no_mir_before_cold": """#![feature(rustc_attrs)]
#[rustc_force_inline]
#[rustc_no_mir_inline]
#[cold]
pub fn both_forced() -> u32 { 1 }
""",
        "priority_cold_before_tailcall": """#![feature(rustc_attrs, explicit_tail_calls)]
fn helper(x: u32) -> u32 { x }
#[rustc_force_inline]
#[cold]
pub fn cold_and_tail(x: u32) -> u32 { become helper(x) }
""",
    }
    out: dict[str, Any] = {}
    for name, code in cases.items():
        d = base / f"cfi_{name}"
        d.mkdir()
        src = d / f"{name}.rs"
        src.write_text(code, encoding="utf-8")
        res = run_rustc(
            ["--crate-type=lib", f"--crate-name={name}", str(src), "-o", str(d / "lib.rlib")],
            d,
            tmp_root,
        )
        reason_match = re.search(r"incompatible due to: (.+)", res["stderr"])
        out[name] = {
            "rc": res["rc"],
            "extracted_reason": reason_match.group(1).strip() if reason_match else None,
            "stderr": res["stderr"],
        }
    return out


def probe_cross_crate_inline(base: Path, tmp_root: str) -> dict[str, Any]:
    out: dict[str, Any] = {}
    d = base / "cross_crate"
    d.mkdir()

    # Construct a leaf body that exceeds threshold=5 (e.g. ~18 MIR statements) and one >100 statements
    # Wait: inline.rs ALSO enforces inline_mir_hint_threshold (default 100) in the consumer!
    # So to cleanly isolate cross_crate_inlinable's threshold check from the consumer MIR inliner's
    # cost check, we test `medium_leaf` (~18 MIR statements) at threshold=100 (default) vs threshold=5!
    dep_src = d / "dep.rs"
    dep_src.write_text(
        """#![feature(core_intrinsics, f16)]
extern crate core;

pub struct NeedsDrop {
    pub v: u32,
}
impl Drop for NeedsDrop {
    #[inline(never)]
    fn drop(&mut self) {
        core::hint::black_box(self.v);
    }
}

#[inline(never)]
fn opaque_sink(x: u32) -> u32 {
    x.wrapping_mul(3)
}

// 1. Small leaf function: CostChecker.calls == 0, statements <= 5
pub fn small_leaf(x: u32) -> u32 {
    x.wrapping_add(7)
}

// 2. Medium leaf (~16 non-storage statements): <= 100 (default) but > 5 (threshold=5)
pub fn medium_leaf(mut x: u32) -> u32 {
    x = x.wrapping_add(1);
    x = x.wrapping_mul(3);
    x = x ^ 0x55aa;
    x = x.wrapping_add(11);
    x = x.wrapping_mul(7);
    x = x ^ 0x1234;
    x = x.wrapping_add(19);
    x
}

// 3. #[inline(never)] overrides inference & hint_mostly_unused -> NOT cross-crate inlinable
#[inline(never)]
pub fn inline_never_leaf(x: u32) -> u32 {
    x.wrapping_add(7)
}

// 4. Extern indicator (#[unsafe(no_mangle)]) -> NOT cross-crate inlinable even under threshold=always
#[unsafe(no_mangle)]
pub extern "C" fn no_mangle_leaf(x: u32) -> u32 {
    x.wrapping_add(7)
}

// 5. Calls a non-intrinsic function -> CostChecker.calls == 1 -> NOT cross-crate inlinable
pub fn non_leaf_caller(x: u32) -> u32 {
    opaque_sink(x)
}

// 6. Calls #[rustc_intrinsic] raw_eq on 20-byte [u32; 5] (remains TerminatorKind::Call in optimized_mir!) -> exempted
pub fn raw_eq_intrinsic_caller(a: &[u32; 5], b: &[u32; 5]) -> bool {
    unsafe { core::intrinsics::raw_eq(a, b) }
}

// 7. Contains non-trivially-pure-clone-copy Drop -> CostChecker.calls >= 1 -> NOT cross-crate inlinable
pub fn drop_caller(x: u32) -> u32 {
    let d = NeedsDrop { v: x };
    d.v
}

// 8. Signature with f16 -> bypasses calls/incremental/threshold gates (on targets lacking reliable_f16, or unconditionally in 1.98)
pub fn f16_sig_bypass(x: f16) -> f16 {
    let _ = opaque_sink(1);
    x
}
""",
        encoding="utf-8",
    )

    consumer_src = d / "consumer.rs"
    consumer_src.write_text(
        """#![feature(f16)]
extern crate dep;

pub fn call_small_leaf(x: u32) -> u32 { dep::small_leaf(x) }
pub fn call_medium_leaf(x: u32) -> u32 { dep::medium_leaf(x) }
pub fn call_inline_never_leaf(x: u32) -> u32 { dep::inline_never_leaf(x) }
pub fn call_no_mangle_leaf(x: u32) -> u32 { dep::no_mangle_leaf(x) }
pub fn call_non_leaf_caller(x: u32) -> u32 { dep::non_leaf_caller(x) }
pub fn call_raw_eq_intrinsic_caller(a: &[u32; 5], b: &[u32; 5]) -> bool { dep::raw_eq_intrinsic_caller(a, b) }
pub fn call_drop_caller(x: u32) -> u32 { dep::drop_caller(x) }
pub fn call_f16_sig_bypass(x: f16) -> f16 { dep::f16_sig_bypass(x) }
""",
        encoding="utf-8",
    )

    # First verify that dep::raw_eq_intrinsic_caller retains a TerminatorKind::Call to raw_eq in optimized_mir
    dep_mir_dir = d / "dep_opt_mir"
    dep_opt_check = run_rustc(
        [
            "--crate-type=lib",
            "--crate-name=dep",
            "-Copt-level=2",
            "--emit=mir",
            str(dep_src),
            "-o",
            str(d / "dep_opt.mir"),
        ],
        d,
        tmp_root,
    )
    dep_mir_text = (d / "dep_opt.mir").read_text(encoding="utf-8", errors="replace") if (d / "dep_opt.mir").exists() else ""
    raw_eq_block_match = re.search(r"fn raw_eq_intrinsic_caller\b.*?\n\}\n", dep_mir_text, flags=re.DOTALL)
    raw_eq_opt_mir = raw_eq_block_match.group(0) if raw_eq_block_match else ""
    out["dep_raw_eq_optimized_mir_check"] = {
        "rc": dep_opt_check["rc"],
        "retains_raw_eq_call_terminator": "raw_eq::" in raw_eq_opt_mir and "-> [return:" in raw_eq_opt_mir,
        "optimized_mir": raw_eq_opt_mir,
    }

    fn_pairs = [
        ("call_small_leaf", "small_leaf"),
        ("call_medium_leaf", "medium_leaf"),
        ("call_inline_never_leaf", "inline_never_leaf"),
        ("call_no_mangle_leaf", "no_mangle_leaf"),
        ("call_non_leaf_caller", "non_leaf_caller"),
        ("call_raw_eq_intrinsic_caller", "raw_eq_intrinsic_caller"),
        ("call_drop_caller", "drop_caller"),
        ("call_f16_sig_bypass", "f16_sig_bypass"),
    ]

    for mode, dep_extra in [
        ("default_threshold_100", []),
        ("threshold_5", ["-Zcross-crate-inline-threshold=5"]),
        ("threshold_always", ["-Zcross-crate-inline-threshold=always"]),
        ("threshold_never", ["-Zcross-crate-inline-threshold=never"]),
        ("hint_mostly_unused", ["-Zhint-mostly-unused"]),
        ("incremental_enabled", ["-Cincremental=" + str(d / "incr_cache")]),
    ]:
        md = d / mode
        md.mkdir()
        rlib = md / "libdep.rlib"
        r1 = run_rustc(
            ["--crate-type=lib", "--crate-name=dep", "-Copt-level=2", *dep_extra, str(dep_src), "-o", str(rlib)],
            md,
            tmp_root,
        )
        dump_dir = md / "mir"
        r2 = run_rustc(
            [
                "--crate-type=lib",
                "--crate-name=consumer",
                "-Copt-level=2",
                "-Zinline-mir=yes",
                "-Zdump-mir=Inline",
                f"-Zdump-mir-dir={dump_dir}",
                "--extern",
                f"dep={rlib}",
                str(consumer_src),
                "-o",
                str(md / "libconsumer.rlib"),
            ],
            md,
            tmp_root,
        )
        inlined_map: dict[str, bool] = {}
        for caller_name, dep_fn in fn_pairs:
            dumps = collect_mir_dumps(dump_dir, rf"consumer\.{caller_name}\..*\.Inline\.after\.mir$")
            after_text = next(iter(dumps.values()), "")
            inlined_map[dep_fn] = bool(after_text) and (f"(inlined {dep_fn})" in after_text)
        out[mode] = {
            "dep_rc": r1["rc"],
            "consumer_rc": r2["rc"],
            "mir_inlined_in_consumer": inlined_map,
        }
    return out


def probe_drop_pruning(base: Path, tmp_root: str) -> dict[str, Any]:
    out: dict[str, Any] = {}

    const_fn_body = """
pub struct NonConstDrop(pub u32);
impl Drop for NonConstDrop {
    fn drop(&mut self) {}
}

pub const fn uninit_drop_branch(take: bool) -> u32 {
    let x: NonConstDrop;
    if take {
        x = NonConstDrop(42);
        let v = x.0;
        core::mem::forget(x);
        return v;
    }
    0
}

pub struct Pair(pub NonConstDrop, pub NonConstDrop);

pub const fn partial_move_both_fields(p: Pair) -> u32 {
    let a = p.0;
    let b = p.1;
    let res = a.0.wrapping_add(b.0);
    core::mem::forget(a);
    core::mem::forget(b);
    res
}

pub const R1: u32 = uninit_drop_branch(true);
pub const R2: u32 = uninit_drop_branch(false);
pub const R3: u32 = partial_move_both_fields(Pair(NonConstDrop(10), NonConstDrop(32)));
"""

    for label, header, extra_flags in [
        ("without_feature_opt0", "", ["-Copt-level=0", "-Zmir-opt-level=0"]),
        ("with_feature_opt0", "#![feature(const_precise_live_drops)]\n", ["-Copt-level=0", "-Zmir-opt-level=0"]),
        ("with_feature_opt3", "#![feature(const_precise_live_drops)]\n", ["-Copt-level=3", "-Zmir-opt-level=4"]),
    ]:
        d = base / f"rud_{label}"
        d.mkdir()
        src = d / f"{label}.rs"
        src.write_text(header + const_fn_body, encoding="utf-8")
        dump_dir = d / "mir"
        res = run_rustc(
            [
                "--crate-type=lib",
                f"--crate-name=rud_{label}",
                *extra_flags,
                "-Zdump-mir=RemoveUninitDrops",
                f"-Zdump-mir-dir={dump_dir}",
                str(src),
                "-o",
                str(d / "lib.rlib"),
            ],
            d,
            tmp_root,
        )
        dumps = collect_mir_dumps(dump_dir, r"RemoveUninitDrops\.(before|after)\.mir$")
        per_fn: dict[str, Any] = {}
        for fn in ["uninit_drop_branch", "partial_move_both_fields"]:
            b_txt = next((v for k, v in dumps.items() if f".{fn}." in k and k.endswith(".before.mir")), "")
            a_txt = next((v for k, v in dumps.items() if f".{fn}." in k and k.endswith(".after.mir")), "")
            per_fn[fn] = {
                "before_drop_count": len(re.findall(r"\bdrop\(", b_txt)),
                "after_drop_count": len(re.findall(r"\bdrop\(", a_txt)),
                "before_blocks": count_basic_blocks(b_txt),
                "after_blocks": count_basic_blocks(a_txt),
                "before_mir": b_txt,
                "after_mir": a_txt,
            }
        out[f"remove_uninit_drops_{label}"] = {
            "rc": res["rc"],
            "stderr": res["stderr"],
            "dumped_files": sorted(dumps.keys()),
            "functions": per_fn,
        }

    # 4b. Partial move leaving ONE field initialized MUST STILL BE REJECTED
    d = base / "rud_partial_one_live"
    d.mkdir()
    src = d / "partial_one_live.rs"
    src.write_text(
        """#![feature(const_precise_live_drops)]
pub struct NonConstDrop(pub u32);
impl Drop for NonConstDrop {
    fn drop(&mut self) {}
}
pub struct Pair(pub NonConstDrop, pub NonConstDrop);

pub const fn partial_move_one_live(p: Pair) -> u32 {
    let a = p.0;
    let res = a.0;
    core::mem::forget(a);
    res
}
""",
        encoding="utf-8",
    )
    dump_dir = d / "mir"
    res = run_rustc(
        [
            "--crate-type=lib",
            "--crate-name=rud_partial_one_live",
            "-Zdump-mir=RemoveUninitDrops",
            f"-Zdump-mir-dir={dump_dir}",
            str(src),
            "-o",
            str(d / "lib.rlib"),
        ],
        d,
        tmp_root,
    )
    dumps = collect_mir_dumps(dump_dir, r"partial_move_one_live.*RemoveUninitDrops\.(before|after)\.mir$")
    b_txt = next((v for k, v in dumps.items() if k.endswith(".before.mir")), "")
    a_txt = next((v for k, v in dumps.items() if k.endswith(".after.mir")), "")
    out["remove_uninit_drops_partial_one_live_rejected"] = {
        "rc": res["rc"],
        "before_drop_count": len(re.findall(r"\bdrop\(", b_txt)),
        "after_drop_count": len(re.findall(r"\bdrop\(", a_txt)),
        "before_blocks": count_basic_blocks(b_txt),
        "after_blocks": count_basic_blocks(a_txt),
        "stderr": res["stderr"],
    }

    # 4c. RemoveUnneededDrops: polymorphic generic function inlined into concrete T=u32 caller
    d = base / "runneeded_generic_inline"
    d.mkdir()
    src = d / "runneeded_generic_inline.rs"
    src.write_text(
        """#[inline(always)]
fn consume_generic<T>(x: T) {
    let _y = x;
}

pub fn call_u32(x: u32) {
    consume_generic(x);
}
""",
        encoding="utf-8",
    )
    dump_dir = d / "mir"
    res = run_rustc(
        [
            "--crate-type=lib",
            "--crate-name=runneeded_generic_inline",
            "-Copt-level=2",
            "-Zinline-mir=yes",
            "-Zdump-mir=RemoveUnneededDrops",
            f"-Zdump-mir-dir={dump_dir}",
            str(src),
            "-o",
            str(d / "lib.rlib"),
        ],
        d,
        tmp_root,
    )
    dumps = collect_mir_dumps(dump_dir, r"call_u32.*RemoveUnneededDrops\.(before|after)\.mir$")
    b_txt = next((v for k, v in dumps.items() if k.endswith(".before.mir")), "")
    a_txt = next((v for k, v in dumps.items() if k.endswith(".after.mir")), "")
    out["remove_unneeded_drops_generic_inlined_u32"] = {
        "rc": res["rc"],
        "stderr": res["stderr"],
        "before_drop_count": len(re.findall(r"\bdrop\(", b_txt)),
        "after_drop_count": len(re.findall(r"\bdrop\(", a_txt)),
        "before_blocks": count_basic_blocks(b_txt),
        "after_blocks": count_basic_blocks(a_txt),
        "before_mir": b_txt,
        "after_mir": a_txt,
    }

    return out


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="probe_ctfe_inline_drop_") as td:
        tmp_root = td
        base = Path(td)
        vv = run_rustc(["--version", "--verbose"], base, tmp_root)
        results = {
            "rustc_version_verbose": vv["stdout"].strip(),
            "ctfe_limit": probe_ctfe_limit(base, tmp_root),
            "check_force_inline": probe_check_force_inline(base, tmp_root),
            "cross_crate_inline": probe_cross_crate_inline(base, tmp_root),
            "drop_pruning": probe_drop_pruning(base, tmp_root),
        }

    OUT_JSON.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print("=== PROBE SUMMARY ===")
    print("rustc:", results["rustc_version_verbose"].splitlines()[0])
    for k, v in results["ctfe_limit"].items():
        print(f"  ctfe_limit.{k}: rc={v['rc']} timed_out={v['timed_out']} counters={v.get('const_eval_counter_count')}")
    for k, v in results["check_force_inline"].items():
        print(f"  check_force_inline.{k}: rc={v['rc']} reason={v['extracted_reason']!r}")
    print(f"  cross_crate_inline.dep_raw_eq_call_retained: {results['cross_crate_inline']['dep_raw_eq_optimized_mir_check']['retains_raw_eq_call_terminator']}")
    for k, v in results["cross_crate_inline"].items():
        if k == "dep_raw_eq_optimized_mir_check":
            continue
        print(f"  cross_crate_inline.{k}: dep_rc={v['dep_rc']} cons_rc={v['consumer_rc']} inlined={v['mir_inlined_in_consumer']}")
    for k, v in results["drop_pruning"].items():
        if "functions" in v:
            fsum = {fn: f"{fd['before_drop_count']}->{fd['after_drop_count']} (bb {fd['before_blocks']}->{fd['after_blocks']})" for fn, fd in v["functions"].items()}
            print(f"  drop_pruning.{k}: rc={v['rc']} {fsum}")
        else:
            print(f"  drop_pruning.{k}: rc={v['rc']} drops={v.get('before_drop_count')}->{v.get('after_drop_count')} bb={v.get('before_blocks')}->{v.get('after_blocks')}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
