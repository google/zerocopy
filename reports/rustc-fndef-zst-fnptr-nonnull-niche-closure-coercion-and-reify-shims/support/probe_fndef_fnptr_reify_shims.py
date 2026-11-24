#!/usr/bin/env python3
"""Self-contained empirical probe for rustc FnDef ZSTs, FnPtr non-null niche,
non-capturing vs capturing closure coercion, direct vs indirect LLVM IR calls,
FnPtr trait shims, and #[track_caller] ReifyShim wrapper synthesis.

Uses Python standard library only and runs all temporary builds strictly inside
`with tempfile.TemporaryDirectory():`, scrubbing local user/toolchain paths.
"""

from __future__ import annotations

import argparse
import datetime as _dt
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


def _find_bin(name: str) -> str:
    for candidate in (
        Path.home() / ".cargo" / "bin" / name,
        Path("/usr/bin") / name,
        Path("/usr/local/bin") / name,
    ):
        if candidate.is_file():
            return str(candidate)
    return name


RUSTC_BIN = _find_bin("rustc")
CARGO_BIN = _find_bin("cargo")


def _scrub(text: str, replacements: list[tuple[str, str]]) -> str:
    out = text
    # Longest paths first to avoid partial prefix masking.
    for old, new in sorted(replacements, key=lambda pair: -len(pair[0])):
        if old:
            out = out.replace(old, new)
    out = re.sub(r"/home/[^/\s\"']+", "$HOME", out)
    out = re.sub(r"/usr/[^/\s\"']+/[^/\s\"']+/home/[^/\s\"']+", "$HOME", out)
    return out


def _assert_no_path_leaks(text: str) -> None:
    leak_re = re.compile(r"(?<![\w$.])/(?:home|Users|root|tmp|var|mnt|opt|private|google|x20)/")
    m = leak_re.search(text)
    if m:
        ctx = text[max(0, m.start() - 60) : m.end() + 60]
        raise RuntimeError(f"path leak detected in serialized output: {ctx!r}")


def _run(
    cmd: list[str],
    cwd: Path | None = None,
    env: dict[str, str] | None = None,
    replacements: list[tuple[str, str]] | None = None,
) -> dict[str, Any]:
    merged_env = os.environ.copy()
    cargo_bin = str(Path.home() / ".cargo" / "bin")
    if cargo_bin not in merged_env.get("PATH", ""):
        merged_env["PATH"] = f"{cargo_bin}:{merged_env.get('PATH', '')}"
    if env:
        merged_env.update(env)
    proc = subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        env=merged_env,
        text=True,
        capture_output=True,
        check=False,
    )
    reps = replacements or []
    return {
        "command": [_scrub(c, reps) for c in cmd],
        "returncode": proc.returncode,
        "stdout": _scrub(proc.stdout, reps),
        "stderr": _scrub(proc.stderr, reps),
    }


def _parse_kv_line(text: str) -> dict[str, str]:
    parsed: dict[str, str] = {}
    for line in text.splitlines():
        for tok in line.strip().split():
            if "=" in tok:
                k, v = tok.split("=", 1)
                parsed[k] = v
    return parsed


def _run_miri_file(
    miri_bin: str,
    miri_sysroot: str,
    filename: str,
    src: str,
    reps: list[tuple[str, str]],
    extra_flags: list[str] | None = None,
) -> dict[str, Any]:
    with tempfile.TemporaryDirectory() as td:
        w = Path(td)
        p = w / filename
        p.write_text(src, encoding="utf-8")
        local_reps = reps + [(td, "$WORK")]
        cmd = [miri_bin, "--edition=2024", "--sysroot", miri_sysroot]
        if extra_flags:
            cmd.extend(extra_flags)
        cmd.append(str(p))
        return _run(cmd, cwd=w, replacements=local_reps)


def _find_core_fn_call_line(sysroot: str) -> int | None:
    fn_rs = Path(sysroot) / "lib" / "rustlib" / "src" / "rust" / "library" / "core" / "src" / "ops" / "function.rs"
    if not fn_rs.is_file():
        return None
    for idx, line in enumerate(fn_rs.read_text(encoding="utf-8").splitlines(), 1):
        if 'extern "rust-call" fn call(' in line:
            return idx
    return None


PROBE_A_SRC = r"""
use core::any::TypeId;
use core::mem::{align_of, align_of_val, size_of, size_of_val, transmute};

fn unit_fn() {}
fn add_one(x: u32) -> u32 { x + 1 }
fn sub_one(x: u32) -> u32 { x - 1 }
fn generic_id<T>(x: T) -> T { x }
extern "C" fn c_fn() {}

fn option_fndef_size<F>(_: F) -> usize {
    size_of::<Option<F>>()
}

fn tuple_fndef_size<F>(_: F) -> usize {
    size_of::<(F, u32)>()
}

fn type_id_of_val<T: 'static>(_: &T) -> TypeId {
    TypeId::of::<T>()
}

fn main() {
    let fndef_sz = size_of_val(&add_one);
    let fndef_align = align_of_val(&add_one);
    let id_u32_sz = size_of_val(&generic_id::<u32>);
    let id_u64_sz = size_of_val(&generic_id::<u64>);
    let opt_fndef_sz = option_fndef_size(add_one);
    let tup_fndef_sz = tuple_fndef_size(add_one);

    let fnptr_sz = size_of::<fn()>();
    let fnptr_align = align_of::<fn()>();
    let tup_fnptr_sz = size_of::<(fn(u32) -> u32, u32)>();
    let opt_fnptr_sz = size_of::<Option<fn()>>();
    let opt_ext_c_sz = size_of::<Option<extern "C" fn()>>();
    let opt_unsafe_ext_c_sz = size_of::<Option<unsafe extern "C" fn(u32) -> u32>>();
    let opt_opt_fnptr_sz = size_of::<Option<Option<fn()>>>();

    let distinct_fndefs =
        type_id_of_val(&add_one) != type_id_of_val(&sub_one)
        && type_id_of_val(&generic_id::<u32>) != type_id_of_val(&generic_id::<u64>);

    let fp1: fn(u32) -> u32 = add_one;
    let fp2: fn(u32) -> u32 = sub_one;
    let same_fnptr_typeid = type_id_of_val(&fp1) == type_id_of_val(&fp2);

    let none_opt: Option<fn()> = None;
    let none_bits: usize = unsafe { transmute(none_opt) };

    let some_opt: Option<fn()> = Some(unit_fn as fn());
    let some_raw_ptr: *const () = unsafe { transmute(some_opt) };
    let some_nonzero = !some_raw_ptr.is_null();

    let some_c_opt: Option<extern "C" fn()> = Some(c_fn as extern "C" fn());
    let none_c_opt: Option<extern "C" fn()> = None;
    let none_c_bits: usize = unsafe { transmute(none_c_opt) };
    let some_c_raw: *const () = unsafe { transmute(some_c_opt) };
    let some_c_nonzero = !some_c_raw.is_null();

    let zero_to_opt: Option<fn()> = unsafe { transmute(0usize) };
    let zero_is_none = zero_to_opt.is_none();

    println!(
        "FNDEF_SZ={fndef_sz} FNDEF_ALIGN={fndef_align} ID_U32_SZ={id_u32_sz} ID_U64_SZ={id_u64_sz} \
OPT_FNDEF_SZ={opt_fndef_sz} TUP_FNDEF_SZ={tup_fndef_sz} FNPTR_SZ={fnptr_sz} FNPTR_ALIGN={fnptr_align} \
TUP_FNPTR_SZ={tup_fnptr_sz} OPT_FNPTR_SZ={opt_fnptr_sz} OPT_EXT_C_SZ={opt_ext_c_sz} \
OPT_UNSAFE_EXT_C_SZ={opt_unsafe_ext_c_sz} OPT_OPT_FNPTR_SZ={opt_opt_fnptr_sz} \
DISTINCT_FNDEFS={distinct_fndefs} SAME_FNPTR_TYPEID={same_fnptr_typeid} \
NONE_BITS={none_bits} SOME_NONZERO={some_nonzero} NONE_C_BITS={none_c_bits} \
SOME_C_NONZERO={some_c_nonzero} ZERO_IS_NONE={zero_is_none}"
    );
}
"""

PROBE_A_NULL_FNPTR_UB_SRC = r"""
use core::mem::transmute;
fn main() {
    let bad: fn() = unsafe { transmute(0usize) };
    core::hint::black_box(&bad);
}
"""

PROBE_B_POS_SRC = r"""
use core::mem::size_of_val;

const K_CONST: u32 = 10;

#[inline(always)]
fn inlined_always_fn(x: u32) -> u32 {
    x + 2
}

fn safe_fn(x: u32) -> u32 {
    x + 3
}

fn call_generic<F: Fn(u32) -> u32>(f: F, x: u32) -> (usize, u32) {
    (size_of_val(&f), f(x))
}

fn main() {
    let noncap = |x: u32| x + 1;
    let noncap_closure_sz = size_of_val(&noncap);
    let f_noncap: fn(u32) -> u32 = noncap;
    let noncap_res = f_noncap(41);

    let f_const: fn(u32) -> u32 = |x| x + K_CONST;
    let const_res = f_const(32);

    let f_unsafe_from_closure: unsafe fn(u32) -> u32 = |x| x + 5;
    let unsafe_closure_res = unsafe { f_unsafe_from_closure(10) };

    let f_unsafe_from_fndef: unsafe fn(u32) -> u32 = safe_fn;
    let unsafe_fndef_res = unsafe { f_unsafe_from_fndef(10) };

    let f_inline_always: fn(u32) -> u32 = inlined_always_fn;
    let inline_always_res = f_inline_always(8);

    let (gen_sz, gen_res) = call_generic(safe_fn, 52);
    let (fnptr_via_trait_sz, fnptr_via_trait_res) = call_generic(f_noncap, 98);

    println!(
        "NONCAP_SZ={noncap_closure_sz} NONCAP={noncap_res} CONST_RES={const_res} \
UNSAFE_CLOSURE={unsafe_closure_res} UNSAFE_FNDEF={unsafe_fndef_res} \
INLINE_ALWAYS={inline_always_res} GEN_SZ={gen_sz} GEN_RES={gen_res} \
FNPTR_TRAIT_SZ={fnptr_via_trait_sz} FNPTR_TRAIT_RES={fnptr_via_trait_res}"
    );
}
"""

PROBE_B_CAPTURING_E0308 = r"""
fn main() {
    let k: u32 = 10;
    let _f: fn(u32) -> u32 = |x| x + k;
}
"""

PROBE_B_MENTION_ONLY_E0308 = r"""
fn main() {
    let k: u32 = 10;
    let _f: fn(u32) -> u32 = |x| {
        let _ = k;
        x + 1
    };
}
"""

PROBE_B_UNSAFE_TO_SAFE_E0308 = r"""
unsafe fn danger(x: u32) -> u32 { x + 1 }
fn main() {
    let _f: fn(u32) -> u32 = danger;
}
"""

PROBE_B_INTRINSIC_E0308 = r"""
fn main() {
    let _f: unsafe extern "rust-intrinsic" fn(u32) -> u32 = core::intrinsics::black_box::<u32>;
}
"""

PROBE_C_IR_SRC = r"""
#![crate_type = "lib"]

#[inline(never)]
pub fn step(x: u32) -> u32 {
    x.wrapping_mul(3).wrapping_add(1)
}

#[inline(never)]
fn apply_generic<F: Fn(u32) -> u32>(f: F, x: u32) -> u32 {
    f(x)
}

#[unsafe(no_mangle)]
pub extern "C" fn call_via_fndef(x: u32) -> u32 {
    apply_generic(step, x)
}

#[unsafe(no_mangle)]
pub extern "C" fn call_via_fnptr(f: fn(u32) -> u32, x: u32) -> u32 {
    f(x)
}

#[unsafe(no_mangle)]
pub extern "C" fn call_fnptr_via_trait(f: fn(u32) -> u32, x: u32) -> u32 {
    apply_generic(f, x)
}

#[unsafe(no_mangle)]
pub extern "C" fn reify_step() -> fn(u32) -> u32 {
    step
}

#[unsafe(no_mangle)]
pub extern "C" fn reify_noncap_closure() -> fn(u32) -> u32 {
    |x| x.wrapping_add(7)
}

#[track_caller]
#[inline(never)]
pub fn tracked_callee(x: u32) -> u32 {
    core::panic::Location::caller().line().wrapping_add(x)
}

#[unsafe(no_mangle)]
pub extern "C" fn reify_tracked_fn() -> fn(u32) -> u32 {
    tracked_callee
}

#[unsafe(no_mangle)]
pub extern "C" fn call_tracked_direct(x: u32) -> u32 {
    tracked_callee(x)
}

#[unsafe(no_mangle)]
pub extern "C" fn call_tracked_via_fntrait(x: u32) -> u32 {
    apply_generic(tracked_callee, x)
}

#[unsafe(no_mangle)]
pub extern "C" fn unwrap_opt_fn(opt: Option<fn(u32) -> u32>, x: u32) -> u32 {
    match opt {
        Some(f) => f(x),
        None => 0,
    }
}
"""

PROBE_D_TRACK_CALLER_SRC = r"""
#[track_caller]
#[inline(never)]
pub fn tracked_callee(x: u32) -> (u32, u32) { // @DEF_LINE
    (x, core::panic::Location::caller().line())
}

#[inline(never)]
fn apply_fnptr(f: fn(u32) -> (u32, u32), x: u32) -> (u32, u32) {
    f(x)
}

#[inline(never)]
fn apply_fntrait<F: Fn(u32) -> (u32, u32)>(f: F, x: u32) -> (u32, u32) {
    f(x)
}

fn main() {
    let direct_1 = tracked_callee(10); // @DIRECT_1_LINE
    let direct_2 = tracked_callee(20); // @DIRECT_2_LINE

    let fp: fn(u32) -> (u32, u32) = tracked_callee; // @REIFY_SITE_LINE
    let reify_1 = fp(10); // @REIFY_1_LINE
    let reify_2 = fp(20); // @REIFY_2_LINE
    let reify_via_helper = apply_fnptr(fp, 30); // @HELPER_LINE
    let reify_via_fntrait = apply_fntrait(fp, 40); // @FNTRAIT_CALLER_LINE
    let fndef_via_fntrait = apply_fntrait(tracked_callee, 50); // @FNDEF_FNTRAIT_CALLER_LINE

    println!(
        "DIRECT1={}:{} DIRECT2={}:{} REIFY1={}:{} REIFY2={}:{} \
HELPER={}:{} FNTRAIT_FNPTR={}:{} FNTRAIT_FNDEF={}:{}",
        direct_1.0, direct_1.1,
        direct_2.0, direct_2.1,
        reify_1.0, reify_1.1,
        reify_2.0, reify_2.1,
        reify_via_helper.0, reify_via_helper.1,
        reify_via_fntrait.0, reify_via_fntrait.1,
        fndef_via_fntrait.0, fndef_via_fntrait.1
    );
}
"""


def _extract_markers(src: str) -> dict[str, int]:
    markers: dict[str, int] = {}
    for lineno, line in enumerate(src.splitlines(), 1):
        m = re.search(r"//\s*@([A-Z0-9_]+)", line)
        if m:
            markers[m.group(1)] = lineno
    return markers


def _extract_llvm_fn_blocks(ll_text: str) -> dict[str, list[str]]:
    blocks: dict[str, list[str]] = {}
    cur_name: str | None = None
    cur_lines: list[str] = []
    for line in ll_text.splitlines():
        if line.startswith("define "):
            cur_name = line.strip()
            cur_lines = [line]
        elif cur_name is not None:
            cur_lines.append(line)
            if line == "}":
                blocks[cur_name] = cur_lines
                cur_name = None
                cur_lines = []
    return blocks


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out",
        type=Path,
        default=Path(__file__).resolve().parent / "probe_results.json",
        help="Path to write JSON results",
    )
    args = parser.parse_args()

    rustc_ver = subprocess.check_output([RUSTC_BIN, "+nightly", "-Vv"], text=True).strip()
    sysroot = subprocess.check_output([RUSTC_BIN, "+nightly", "--print", "sysroot"], text=True).strip()
    miri_bin = str(Path(sysroot) / "bin" / "miri")
    miri_ver = subprocess.check_output([miri_bin, "--version"], text=True).strip()
    miri_sysroot = (
        subprocess.check_output([CARGO_BIN, "+nightly", "miri", "setup", "--print-sysroot"], text=True)
        .strip()
        .splitlines()[-1]
    )
    core_fn_call_line = _find_core_fn_call_line(sysroot)

    reps = [
        (sysroot, "$SYSROOT"),
        (miri_sysroot, "$MIRI_SYSROOT"),
        (str(Path.home()), "$HOME"),
    ]

    results: dict[str, Any] = {
        "observed_at": _dt.datetime.now(_dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "rustc_version": _scrub(rustc_ver, reps),
        "miri_version": _scrub(miri_ver, reps),
        "core_ops_function_fn_call_line": core_fn_call_line,
        "target": "x86_64-unknown-linux-gnu",
        "edition": "2024",
    }

    checks: dict[str, bool] = {}

    # ------------------------------------------------------------------
    # Part A: FnDef ZST vs FnPtr non-null niche + print-type-sizes + Miri
    # ------------------------------------------------------------------
    with tempfile.TemporaryDirectory() as td:
        w = Path(td)
        local_reps = reps + [(td, "$WORK")]
        src_a = w / "probe_a.rs"
        bin_a = w / "probe_a"
        src_a.write_text(PROBE_A_SRC, encoding="utf-8")

        comp_a = _run(
            [RUSTC_BIN, "+nightly", "--edition=2024", "-O", str(src_a), "-o", str(bin_a)],
            cwd=w,
            replacements=local_reps,
        )
        run_a = _run([str(bin_a)], cwd=w, replacements=local_reps)

        type_sizes = _run(
            [
                RUSTC_BIN,
                "+nightly",
                "--edition=2024",
                "-Z",
                "print-type-sizes",
                "--emit=metadata",
                str(src_a),
                "-o",
                str(w / "probe_a.rmeta"),
            ],
            cwd=w,
            replacements=local_reps,
        )

    miri_a = _run_miri_file(miri_bin, miri_sysroot, "probe_a.rs", PROBE_A_SRC, reps)
    miri_null_ub = _run_miri_file(
        miri_bin, miri_sysroot, "probe_a_null_ub.rs", PROBE_A_NULL_FNPTR_UB_SRC, reps
    )

    kv_native_a = _parse_kv_line(run_a["stdout"])
    kv_miri_a = _parse_kv_line(miri_a["stdout"])

    expected_a = {
        "FNDEF_SZ": "0",
        "FNDEF_ALIGN": "1",
        "ID_U32_SZ": "0",
        "ID_U64_SZ": "0",
        "OPT_FNDEF_SZ": "1",
        "TUP_FNDEF_SZ": "4",
        "FNPTR_SZ": "8",
        "FNPTR_ALIGN": "8",
        "TUP_FNPTR_SZ": "16",
        "OPT_FNPTR_SZ": "8",
        "OPT_EXT_C_SZ": "8",
        "OPT_UNSAFE_EXT_C_SZ": "8",
        "OPT_OPT_FNPTR_SZ": "16",
        "DISTINCT_FNDEFS": "true",
        "SAME_FNPTR_TYPEID": "true",
        "NONE_BITS": "0",
        "SOME_NONZERO": "true",
        "NONE_C_BITS": "0",
        "SOME_C_NONZERO": "true",
        "ZERO_IS_NONE": "true",
    }
    for k, v in expected_a.items():
        checks[f"part_a_native_{k}"] = kv_native_a.get(k) == v
        checks[f"part_a_miri_{k}"] = kv_miri_a.get(k) == v
    checks["part_a_miri_null_fnptr_ub_detected"] = (
        miri_null_ub["returncode"] != 0
        and "null function pointer" in miri_null_ub["stderr"].lower()
    )

    interesting_type_sizes = [
        line
        for line in type_sizes["stdout"].splitlines()
        if any(
            pat in line
            for pat in (
                "std::option::Option<fn()>",
                "std::option::Option<std::option::Option<fn()>>",
                'std::option::Option<extern "C" fn()>',
                "std::option::Option<fn(u32) -> u32",
                "add_one",
            )
        )
    ]

    results["part_a_layout_and_niche"] = {
        "compile": comp_a,
        "native_run": run_a,
        "native_parsed": kv_native_a,
        "miri_run": miri_a,
        "miri_parsed": kv_miri_a,
        "miri_null_fnptr_ub": miri_null_ub,
        "print_type_sizes_excerpt": interesting_type_sizes,
    }

    # ------------------------------------------------------------------
    # Part B: Non-capturing vs Capturing closure coercion & FnDef cases
    # ------------------------------------------------------------------
    with tempfile.TemporaryDirectory() as td:
        w = Path(td)
        local_reps = reps + [(td, "$WORK")]
        src_b = w / "probe_b.rs"
        bin_b = w / "probe_b"
        src_b.write_text(PROBE_B_POS_SRC, encoding="utf-8")
        comp_b = _run(
            [RUSTC_BIN, "+nightly", "--edition=2024", str(src_b), "-o", str(bin_b)],
            cwd=w,
            replacements=local_reps,
        )
        run_b = _run([str(bin_b)], cwd=w, replacements=local_reps)

        neg_results: dict[str, Any] = {}
        for neg_name, neg_src in (
            ("capturing_closure_to_fnptr", PROBE_B_CAPTURING_E0308),
            ("mention_only_closure_to_fnptr", PROBE_B_MENTION_ONLY_E0308),
            ("unsafe_fndef_to_safe_fnptr", PROBE_B_UNSAFE_TO_SAFE_E0308),
            ("intrinsic_to_fnptr", PROBE_B_INTRINSIC_E0308),
        ):
            p = w / f"{neg_name}.rs"
            p.write_text(neg_src, encoding="utf-8")
            neg_results[neg_name] = _run(
                [RUSTC_BIN, "+nightly", "--edition=2024", str(p), "-o", str(w / neg_name)],
                cwd=w,
                replacements=local_reps,
            )

    miri_b = _run_miri_file(miri_bin, miri_sysroot, "probe_b.rs", PROBE_B_POS_SRC, reps)
    kv_native_b = _parse_kv_line(run_b["stdout"])
    kv_miri_b = _parse_kv_line(miri_b["stdout"])
    expected_b = {
        "NONCAP_SZ": "0",
        "NONCAP": "42",
        "CONST_RES": "42",
        "UNSAFE_CLOSURE": "15",
        "UNSAFE_FNDEF": "13",
        "INLINE_ALWAYS": "10",
        "GEN_SZ": "0",
        "GEN_RES": "55",
        "FNPTR_TRAIT_SZ": "8",
        "FNPTR_TRAIT_RES": "99",
    }
    for k, v in expected_b.items():
        checks[f"part_b_native_{k}"] = kv_native_b.get(k) == v
        checks[f"part_b_miri_{k}"] = kv_miri_b.get(k) == v

    checks["part_b_neg_capturing_e0308"] = (
        neg_results["capturing_closure_to_fnptr"]["returncode"] == 1
        and "error[E0308]" in neg_results["capturing_closure_to_fnptr"]["stderr"]
        and "do not capture any variables" in neg_results["capturing_closure_to_fnptr"]["stderr"]
    )
    checks["part_b_neg_mention_only_e0308"] = (
        neg_results["mention_only_closure_to_fnptr"]["returncode"] == 1
        and "error[E0308]" in neg_results["mention_only_closure_to_fnptr"]["stderr"]
    )
    checks["part_b_neg_unsafe_to_safe_e0308"] = (
        neg_results["unsafe_fndef_to_safe_fnptr"]["returncode"] == 1
        and "error[E0308]" in neg_results["unsafe_fndef_to_safe_fnptr"]["stderr"]
    )
    checks["part_b_neg_intrinsic_rejected"] = (
        neg_results["intrinsic_to_fnptr"]["returncode"] == 1
        and (
            "E0658" in neg_results["intrinsic_to_fnptr"]["stderr"]
            or "E0308" in neg_results["intrinsic_to_fnptr"]["stderr"]
        )
    )

    results["part_b_coercion"] = {
        "positive_compile": comp_b,
        "positive_native_run": run_b,
        "positive_native_parsed": kv_native_b,
        "positive_miri_run": miri_b,
        "positive_miri_parsed": kv_miri_b,
        "negative_controls": neg_results,
    }

    # ------------------------------------------------------------------
    # Part C: LLVM IR (-O3) + MIR shim dumps + mono items
    # ------------------------------------------------------------------
    with tempfile.TemporaryDirectory() as td:
        w = Path(td)
        local_reps = reps + [(td, "$WORK")]
        src_c = w / "ir_probe.rs"
        ll_c = w / "ir_probe.ll"
        mir_dir = w / "mir_dump"
        mir_dir.mkdir()
        src_c.write_text(PROBE_C_IR_SRC, encoding="utf-8")

        comp_c_ll = _run(
            [
                RUSTC_BIN,
                "+nightly",
                "--edition=2024",
                "--crate-name=ir_probe",
                "-C",
                "opt-level=3",
                "-C",
                "codegen-units=1",
                "-C",
                "symbol-mangling-version=v0",
                "--emit=llvm-ir",
                str(src_c),
                "-o",
                str(ll_c),
            ],
            cwd=w,
            replacements=local_reps,
        )
        ll_text = ll_c.read_text(encoding="utf-8") if ll_c.exists() else ""
        fn_blocks = _extract_llvm_fn_blocks(ll_text)
        matching_ll_fns: dict[str, list[str]] = {}
        interesting_patterns = (
            "@call_via_fndef",
            "@call_via_fnptr",
            "@call_fnptr_via_trait",
            "@reify_step",
            "@reify_noncap_closure",
            "@reify_tracked_fn",
            "@call_tracked_direct",
            "@call_tracked_via_fntrait",
            "@unwrap_opt_fn",
            "4step",
            "14tracked_callee",
            "call_once",
            "apply_generic",
        )
        for header, body_lines in fn_blocks.items():
            if any(pat in header for pat in interesting_patterns):
                matching_ll_fns[header] = body_lines

        alloc_lines = [
            line
            for line in ll_text.splitlines()
            if line.startswith("@alloc_") or line.startswith("@str.")
        ]

        comp_c_mir = _run(
            [
                RUSTC_BIN,
                "+nightly",
                "--edition=2024",
                "--crate-name=ir_probe",
                "-C",
                "opt-level=0",
                "-C",
                "codegen-units=1",
                "-Z",
                "dump-mir=all",
                "-Z",
                f"dump-mir-dir={mir_dir}",
                "-Z",
                "print-mono-items=yes",
                "--emit=obj",
                str(src_c),
                "-o",
                str(w / "ir_probe.o"),
            ],
            cwd=w,
            replacements=local_reps,
        )
        mir_dumps: dict[str, str] = {}
        all_mir_files = sorted(p.name for p in mir_dir.iterdir())
        for p in sorted(mir_dir.glob("*")):
            n = p.name
            if (
                "SimplifyCfg-make_shim.after.mir" in n
                or "runtime-optimized.after.mir" in n
            ) and any(
                k in n
                for k in (
                    "tracked_callee",
                    "FnOnce-call_once",
                    "Fn-call",
                    "reify_noncap_closure",
                    "reify_step",
                    "apply_generic",
                )
            ):
                mir_dumps[n] = _scrub(p.read_text(encoding="utf-8"), local_reps)

        ll_kcfi = w / "ir_probe_kcfi.ll"
        comp_c_kcfi = _run(
            [
                RUSTC_BIN,
                "+nightly",
                "--edition=2024",
                "--crate-name=ir_probe",
                "-C",
                "opt-level=3",
                "-C",
                "codegen-units=1",
                "-C",
                "panic=abort",
                "-C",
                "symbol-mangling-version=v0",
                "-Z",
                "sanitizer=kcfi",
                "-C",
                "unsafe-allow-abi-mismatch=sanitizer",
                "--emit=llvm-ir",
                str(src_c),
                "-o",
                str(ll_kcfi),
            ],
            cwd=w,
            replacements=local_reps,
        )
        kcfi_ll_text = ll_kcfi.read_text(encoding="utf-8") if ll_kcfi.exists() else ""
        kcfi_reify_headers = [
            line.strip()
            for line in kcfi_ll_text.splitlines()
            if line.startswith("define ") and ("reify" in line or "call_once" in line)
        ]

    has_direct_fastcc = any(
        "@call_via_fndef" in h and any("call fastcc" in l or "call noundef i32" in l for l in b)
        for h, b in matching_ll_fns.items()
    )
    has_indirect_nonnull = any(
        "@call_via_fnptr" in h
        and "nonnull" in h
        and any("%f(" in l for l in b)
        for h, b in matching_ll_fns.items()
    )
    has_reify_shim_ir = any(
        "tracked_callee" in h and "reify" in h and any("@alloc_" in l for l in b)
        for h, b in matching_ll_fns.items()
    )
    has_opt_fn_null_check = any(
        "@unwrap_opt_fn" in h and any("icmp eq ptr" in l or "icmp ne ptr" in l for l in b)
        for h, b in matching_ll_fns.items()
    )
    checks["part_c_llvm_compile_ok"] = comp_c_ll["returncode"] == 0
    checks["part_c_mir_dump_ok"] = comp_c_mir["returncode"] == 0
    checks["part_c_direct_fndef_call"] = has_direct_fastcc
    checks["part_c_indirect_nonnull_fnptr_call"] = has_indirect_nonnull
    checks["part_c_reify_shim_passes_alloc"] = has_reify_shim_ir
    checks["part_c_unwrap_opt_fn_null_niche_cmp"] = has_opt_fn_null_check
    checks["part_c_kcfi_compile_ok"] = comp_c_kcfi["returncode"] == 0
    checks["part_c_kcfi_reify_fnptr_present"] = any(
        "reify_fnptr" in h for h in kcfi_reify_headers
    )
    checks["part_c_mir_tracked_reify_shim_present"] = any(
        "tracked_callee" in k and "make_shim" in k for k in mir_dumps
    )
    checks["part_c_mir_fn_call_shim_present"] = any(
        "Fn-call" in k and "make_shim" in k for k in mir_dumps
    )

    results["part_c_ir_and_mir"] = {
        "llvm_ir_compile": comp_c_ll,
        "llvm_ir_matching_fns": matching_ll_fns,
        "llvm_ir_alloc_count": len(alloc_lines),
        "mir_dump_compile": {
            "returncode": comp_c_mir["returncode"],
            "total_dump_files": len(all_mir_files),
            "mono_items_excerpt": [
                l
                for l in comp_c_mir["stdout"].splitlines()
                if "MONO_ITEM" in l
                and any(
                    k in l
                    for k in (
                        "tracked_callee",
                        "step",
                        "call_once",
                        "reify",
                        "apply_generic",
                        "Fn::call",
                    )
                )
            ],
            "stderr": comp_c_mir["stderr"],
        },
        "mir_dumps": mir_dumps,
        "kcfi_compile": comp_c_kcfi,
        "kcfi_reify_and_closure_headers": kcfi_reify_headers,
    }

    # ------------------------------------------------------------------
    # Part D: #[track_caller] ReifyShim vs direct vs Fn trait execution
    # ------------------------------------------------------------------
    markers = _extract_markers(PROBE_D_TRACK_CALLER_SRC)
    with tempfile.TemporaryDirectory() as td:
        w = Path(td)
        local_reps = reps + [(td, "$WORK")]
        src_d = w / "probe_d.rs"
        bin_d = w / "probe_d"
        src_d.write_text(PROBE_D_TRACK_CALLER_SRC, encoding="utf-8")
        comp_d_o0 = _run(
            [RUSTC_BIN, "+nightly", "--edition=2024", "-C", "opt-level=0", str(src_d), "-o", str(bin_d)],
            cwd=w,
            replacements=local_reps,
        )
        run_d_o0 = _run([str(bin_d)], cwd=w, replacements=local_reps)
        bin_d_o3 = w / "probe_d_o3"
        comp_d_o3 = _run(
            [RUSTC_BIN, "+nightly", "--edition=2024", "-C", "opt-level=3", str(src_d), "-o", str(bin_d_o3)],
            cwd=w,
            replacements=local_reps,
        )
        run_d_o3 = _run([str(bin_d_o3)], cwd=w, replacements=local_reps)

    miri_d = _run_miri_file(miri_bin, miri_sysroot, "probe_d.rs", PROBE_D_TRACK_CALLER_SRC, reps)
    miri_d_opt3 = _run_miri_file(
        miri_bin,
        miri_sysroot,
        "probe_d.rs",
        PROBE_D_TRACK_CALLER_SRC,
        reps,
        extra_flags=["-Zmir-opt-level=3", "-Zinline-mir=yes"],
    )

    kv_d_o0 = _parse_kv_line(run_d_o0["stdout"])
    kv_d_o3 = _parse_kv_line(run_d_o3["stdout"])
    kv_d_miri = _parse_kv_line(miri_d["stdout"])
    kv_d_miri_opt3 = _parse_kv_line(miri_d_opt3["stdout"])

    expected_fn_call_line = core_fn_call_line if core_fn_call_line is not None else 79
    expected_d = {
        "DIRECT1": f"10:{markers['DIRECT_1_LINE']}",
        "DIRECT2": f"20:{markers['DIRECT_2_LINE']}",
        "REIFY1": f"10:{markers['DEF_LINE']}",
        "REIFY2": f"20:{markers['DEF_LINE']}",
        "HELPER": f"30:{markers['DEF_LINE']}",
        "FNTRAIT_FNPTR": f"40:{markers['DEF_LINE']}",
        "FNTRAIT_FNDEF": f"50:{expected_fn_call_line}",
    }
    for label, kv in (
        ("o0", kv_d_o0),
        ("o3", kv_d_o3),
        ("miri", kv_d_miri),
        ("miri_opt3", kv_d_miri_opt3),
    ):
        for k, v in expected_d.items():
            checks[f"part_d_{label}_{k}"] = kv.get(k) == v

    results["part_d_track_caller_reify"] = {
        "markers": markers,
        "expected": expected_d,
        "native_o0_compile": comp_d_o0,
        "native_o0_run": run_d_o0,
        "native_o0_parsed": kv_d_o0,
        "native_o3_compile": comp_d_o3,
        "native_o3_run": run_d_o3,
        "native_o3_parsed": kv_d_o3,
        "miri_default_run": miri_d,
        "miri_default_parsed": kv_d_miri,
        "miri_opt3_run": miri_d_opt3,
        "miri_opt3_parsed": kv_d_miri_opt3,
    }

    results["self_checks"] = {
        "total": len(checks),
        "passed": sum(1 for v in checks.values() if v),
        "failed": [k for k, v in checks.items() if not v],
        "details": checks,
    }

    serialized = json.dumps(results, indent=2, sort_keys=True) + "\n"
    _assert_no_path_leaks(serialized)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(serialized, encoding="utf-8")
    print(f"wrote {args.out} ({results['self_checks']['passed']}/{results['self_checks']['total']} checks passed)")
    if results["self_checks"]["failed"]:
        print(f"FAILED CHECKS: {results['self_checks']['failed']}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
