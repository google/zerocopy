#!/usr/bin/env python3
"""Live rustc empirical probe suite for #[target_feature] 1.1, MIR vs LLVM inlining, and SIMD ABI.

Runs cleanly inside tempfile.TemporaryDirectory() with zero persistent workspace side effects.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path


def run_rustc(
    rustc: str,
    src_code: str,
    td: str,
    *,
    crate_type: str = "lib",
    extra_args: list[str] | None = None,
    emit: str | None = None,
    out_name: str | None = None,
) -> dict:
    src_path = Path(td) / "probe.rs"
    src_path.write_text(src_code, encoding="utf-8")
    cmd = [rustc, f"--crate-type={crate_type}", "--edition=2024", str(src_path)]
    if extra_args:
        cmd.extend(extra_args)
    out_path = None
    if emit:
        cmd.append(f"--emit={emit}")
    if out_name:
        out_path = Path(td) / out_name
        cmd.extend(["-o", str(out_path)])
    else:
        cmd.extend(["--out-dir", td])
    proc = subprocess.run(cmd, cwd=td, capture_output=True, text=True)
    return {
        "cmd": [os.path.basename(cmd[0])] + [
            "<tmp>/probe.rs" if a == str(src_path) else (
                "<tmp>" if a == td else a.replace(td, "<tmp>")
            )
            for a in cmd[1:]
        ],
        "returncode": proc.returncode,
        "stdout": proc.stdout.replace(td, "<tmp>"),
        "stderr": proc.stderr.replace(td, "<tmp>"),
        "out_path": str(out_path) if out_path else None,
    }


def extract_llvm_ir_summary(ll_text: str, symbol_hints: tuple[str, ...]) -> dict:
    lines = ll_text.splitlines()
    defines: dict[str, list[str]] = {}
    attrs: list[str] = []
    cur_header: str | None = None
    cur_body: list[str] = []
    for line in lines:
        if line.startswith("define "):
            if any(h in line for h in symbol_hints):
                cur_header = line
                cur_body = [line]
            else:
                cur_header = None
        elif cur_header is not None:
            cur_body.append(line)
            if line.strip() == "}":
                defines[cur_header] = cur_body
                cur_header = None
                cur_body = []
        elif line.startswith("attributes #"):
            attrs.append(line)
    return {"defines": defines, "attributes": attrs}


def run_all_probes(rustc: str = "rustc") -> dict:
    vv = subprocess.run([rustc, "-Vv"], capture_output=True, text=True, check=True)
    results: dict = {
        "rustc_version": vv.stdout.strip(),
        "experiments": {
            "a_target_feature_11_call_safety": {},
            "b_cross_feature_inlining_mir_vs_llvm": {},
            "c_simd_vector_abi_and_target_features": {},
        },
    }

    # --- A1: Safe target_feature 1.1 calls, fn ptr coercion, implication superset, native exec ---
    code_a1 = r"""
#[target_feature(enable = "avx")]
#[inline(never)]
pub fn avx_leaf(x: i32) -> i32 {
    x + 7
}

#[target_feature(enable = "avx2")]
#[inline(never)]
pub fn avx2_leaf(x: i32) -> i32 {
    x + 42
}

#[target_feature(enable = "avx2")]
#[inline(never)]
pub fn avx2_safe_call_and_implication(x: i32) -> i32 {
    // Safe call to matching feature AND implied subset feature (`avx` <= `avx2`) without `unsafe`
    avx2_leaf(x) + avx_leaf(x)
}

#[target_feature(enable = "avx2")]
#[inline(never)]
pub fn avx2_safe_fn_ptr(x: i32) -> i32 {
    let fp: fn(i32) -> i32 = avx2_leaf;
    let fp_sub: fn(i32) -> i32 = avx_leaf;
    fp(x) + fp_sub(x)
}

#[target_feature(enable = "avx2")]
#[inline(never)]
pub fn avx2_closure_inherits(x: i32) -> i32 {
    let c = |y: i32| avx2_leaf(y) + 1;
    c(x)
}

#[inline(never)]
pub fn baseline_unsafe_fp(x: i32) -> i32 {
    let fp: unsafe fn(i32) -> i32 = avx2_leaf;
    unsafe { fp(x) }
}

fn main() {
    if std::is_x86_feature_detected!("avx2") {
        let a = unsafe { avx2_safe_call_and_implication(10) };
        let b = unsafe { avx2_safe_fn_ptr(10) };
        let c = unsafe { avx2_closure_inherits(10) };
        let d = baseline_unsafe_fp(10);
        println!("SAFE_CALL={a} SAFE_FP={b} CLOSURE={c} UNSAFE_FP={d}");
    } else {
        println!("AVX2_NOT_PRESENT_ON_HOST");
    }
}
"""
    with tempfile.TemporaryDirectory() as td:
        c_res = run_rustc(rustc, code_a1, td, crate_type="bin", out_name="probe_bin")
        entry = {
            "edition": "2024",
            "extra_args": [],
            "compile_returncode": c_res["returncode"],
            "compile_stderr": c_res["stderr"],
        }
        if c_res["returncode"] == 0 and c_res["out_path"]:
            run_p = subprocess.run([c_res["out_path"]], capture_output=True, text=True)
            entry["run_returncode"] = run_p.returncode
            entry["run_stdout"] = run_p.stdout.strip()
            entry["run_stderr"] = run_p.stderr.strip()
        results["experiments"]["a_target_feature_11_call_safety"]["safe_avx2_to_avx2_and_native_exec"] = entry

    # --- A2: Baseline safe call rejected (E0133) ---
    code_a2 = r"""
#[target_feature(enable = "avx2")]
pub fn avx2_leaf(x: i32) -> i32 { x + 1 }

pub fn bad_call(x: i32) -> i32 {
    avx2_leaf(x)
}
"""
    with tempfile.TemporaryDirectory() as td:
        r = run_rustc(rustc, code_a2, td)
        results["experiments"]["a_target_feature_11_call_safety"]["baseline_safe_call_rejected"] = {
            "edition": "2024",
            "compile_returncode": r["returncode"],
            "compile_stderr": r["stderr"].strip(),
        }

    # --- A3: Baseline safe fn ptr coercion rejected (E0308) ---
    code_a3 = r"""
#[target_feature(enable = "avx2")]
pub fn avx2_leaf(x: i32) -> i32 { x + 1 }

pub fn bad_coerce() -> fn(i32) -> i32 {
    avx2_leaf
}
"""
    with tempfile.TemporaryDirectory() as td:
        r = run_rustc(rustc, code_a3, td)
        results["experiments"]["a_target_feature_11_call_safety"]["baseline_safe_fn_ptr_coercion_rejected"] = {
            "edition": "2024",
            "compile_returncode": r["returncode"],
            "compile_stderr": r["stderr"].strip(),
        }

    # --- A4: Non-subset feature caller rejected (E0133 + E0308) ---
    code_a4 = r"""
#[target_feature(enable = "avx2")]
pub fn avx2_leaf(x: i32) -> i32 { x + 1 }

#[target_feature(enable = "sse4.2")]
pub fn sse42_bad_call(x: i32) -> i32 {
    avx2_leaf(x)
}

#[target_feature(enable = "sse4.2")]
pub fn sse42_bad_coerce() -> fn(i32) -> i32 {
    avx2_leaf
}
"""
    with tempfile.TemporaryDirectory() as td:
        r = run_rustc(rustc, code_a4, td)
        results["experiments"]["a_target_feature_11_call_safety"]["non_subset_feature_rejected"] = {
            "edition": "2024",
            "compile_returncode": r["returncode"],
            "compile_stderr": r["stderr"].strip(),
        }

    # --- A5: Trait method & main rejected ---
    code_a5 = r"""
pub trait Foo {
    #[target_feature(enable = "avx2")]
    fn trait_method(&self);
}

#[target_feature(enable = "avx2")]
fn main() {}
"""
    with tempfile.TemporaryDirectory() as td:
        r = run_rustc(rustc, code_a5, td, crate_type="bin")
        results["experiments"]["a_target_feature_11_call_safety"]["trait_and_main_rejected"] = {
            "edition": "2024",
            "compile_returncode": r["returncode"],
            "compile_stderr": r["stderr"].strip(),
        }

    # --- A6: #[inline(always)] + #[target_feature] probe ---
    code_a6 = r"""
#[target_feature(enable = "avx2")]
#[inline(always)]
pub fn tf_inline_always(x: i32) -> i32 { x + 11 }

#[target_feature(enable = "avx2")]
#[inline(never)]
pub fn avx2_caller(x: i32) -> i32 { tf_inline_always(x) }

#[inline(never)]
pub fn baseline_caller(x: i32) -> i32 { unsafe { tf_inline_always(x) } }
"""
    with tempfile.TemporaryDirectory() as td:
        r = run_rustc(rustc, code_a6, td, extra_args=["-Copt-level=3"], emit="llvm-ir", out_name="probe.ll")
        entry = {
            "edition": "2024",
            "extra_args": ["-Copt-level=3", "--emit=llvm-ir"],
            "compile_returncode": r["returncode"],
            "compile_stderr": r["stderr"].strip(),
        }
        if r["returncode"] == 0 and r["out_path"] and os.path.exists(r["out_path"]):
            ll = Path(r["out_path"]).read_text(encoding="utf-8")
            entry["llvm_ir_summary"] = extract_llvm_ir_summary(
                ll, ("tf_inline_always", "avx2_caller", "baseline_caller")
            )
        results["experiments"]["a_target_feature_11_call_safety"]["inline_always_with_target_feature_probe"] = entry

    # --- B: MIR Inline (strict sequence equality) vs LLVM -O3 (monotone subset) ---
    code_b = r"""
#[target_feature(enable = "avx")]
#[inline]
pub fn avx_leaf_helper(x: u32) -> u32 {
    x.wrapping_mul(11).wrapping_add(3)
}

#[target_feature(enable = "avx2")]
#[inline]
pub fn avx2_leaf_helper(x: u32) -> u32 {
    x.wrapping_mul(17).wrapping_add(5)
}

#[target_feature(enable = "avx2,bmi1")]
#[inline]
pub fn avx2_bmi1_helper(x: u32) -> u32 {
    x.wrapping_mul(23).wrapping_add(7)
}

#[inline(always)]
pub fn baseline_inline_always_helper(x: u32) -> u32 {
    x ^ 0xa5a5_5a5a
}

#[inline]
pub fn baseline_inline_helper(x: u32) -> u32 {
    x.wrapping_add(99)
}

#[target_feature(enable = "avx2")]
#[inline(never)]
pub fn avx2_calls_avx2_leaf(x: u32) -> u32 {
    avx2_leaf_helper(x)
}

#[target_feature(enable = "avx2")]
#[inline(never)]
pub fn avx2_calls_avx_leaf(x: u32) -> u32 {
    avx_leaf_helper(x)
}

#[target_feature(enable = "bmi1,avx2")]
#[inline(never)]
pub fn bmi1_avx2_calls_avx2_bmi1(x: u32) -> u32 {
    avx2_bmi1_helper(x)
}

#[inline(never)]
pub unsafe fn baseline_calls_avx2_leaf(x: u32) -> u32 {
    unsafe { avx2_leaf_helper(x) }
}

#[target_feature(enable = "avx2")]
#[inline(never)]
pub fn avx2_calls_baseline_always(x: u32) -> u32 {
    baseline_inline_always_helper(x)
}

#[target_feature(enable = "avx2")]
#[inline(never)]
pub fn avx2_calls_baseline_inline(x: u32) -> u32 {
    baseline_inline_helper(x)
}
"""
    with tempfile.TemporaryDirectory() as td:
        mir_dir = Path(td) / "mir_dump"
        mir_dir.mkdir()
        # Use `-Zdump-mir=Inline | ForceInline` (single flag value) to capture both passes.
        r_mir = run_rustc(
            rustc,
            code_b,
            td,
            extra_args=["-Copt-level=3", "-Zdump-mir=Inline | ForceInline", f"-Zdump-mir-dir={mir_dir}"],
        )
        mir_excerpts: dict[str, list[str]] = {}
        for fpath in sorted(mir_dir.glob("probe.*.mir")):
            if "calls_" not in fpath.name:
                continue
            txt = fpath.read_text(encoding="utf-8")
            interesting = [
                line for line in txt.splitlines()
                if any(k in line for k in ("fn ", "scope ", "helper(", "inlined "))
            ]
            mir_excerpts[fpath.name] = interesting[:20]

        r_ll = run_rustc(
            rustc,
            code_b,
            td,
            extra_args=["-Copt-level=3"],
            emit="llvm-ir",
            out_name="probe_b.ll",
        )
        ll_summary = {}
        if r_ll["returncode"] == 0 and r_ll["out_path"] and os.path.exists(r_ll["out_path"]):
            ll_summary = extract_llvm_ir_summary(
                Path(r_ll["out_path"]).read_text(encoding="utf-8"),
                (
                    "avx_leaf_helper",
                    "avx2_leaf_helper",
                    "avx2_bmi1_helper",
                    "baseline_inline_always_helper",
                    "baseline_inline_helper",
                    "avx2_calls_avx2_leaf",
                    "avx2_calls_avx_leaf",
                    "bmi1_avx2_calls_avx2_bmi1",
                    "baseline_calls_avx2_leaf",
                    "avx2_calls_baseline_always",
                    "avx2_calls_baseline_inline",
                ),
            )
        results["experiments"]["b_cross_feature_inlining_mir_vs_llvm"] = {
            "edition": "2024",
            "mir_compile_returncode": r_mir["returncode"],
            "mir_compile_stderr": r_mir["stderr"].strip(),
            "mir_inline_dump_excerpts": mir_excerpts,
            "llvm_ir_compile_returncode": r_ll["returncode"],
            "llvm_ir_compile_stderr": r_ll["stderr"].strip(),
            "llvm_ir_summary": ll_summary,
        }

    # --- C: SIMD vector ABI & target_feature checks ---
    code_c_rej = r"""
use std::arch::x86_64::__m256;

#[repr(C)]
pub struct Wrap256 {
    pub v: __m256,
}

#[target_feature(enable = "avx2")]
#[inline(never)]
pub extern "C" fn pass_m256_avx2(v: __m256) -> __m256 { v }

#[inline(never)]
pub extern "C" fn pass_m256_baseline(v: __m256) -> __m256 { v }

#[inline(never)]
pub extern "C" fn pass_wrap256_baseline(w: Wrap256) -> Wrap256 { w }

#[inline(never)]
pub extern "C" fn caller_baseline_calls_avx2_m256(v: __m256) -> __m256 {
    unsafe { pass_m256_avx2(v) }
}
"""
    with tempfile.TemporaryDirectory() as td:
        r = run_rustc(rustc, code_c_rej, td, extra_args=["-Copt-level=2"], emit="llvm-ir", out_name="c_rej.ll")
        results["experiments"]["c_simd_vector_abi_and_target_features"]["default_baseline_sse2_extern_c_rejected"] = {
            "extra_flags": ["-Copt-level=2"],
            "compile_returncode": r["returncode"],
            "compile_stderr": r["stderr"].strip(),
        }

    code_c_ok = r"""
use std::arch::x86_64::{__m128, __m256};

#[repr(C)]
pub struct Wrap256 {
    pub v: __m256,
}

#[target_feature(enable = "avx2")]
#[inline(never)]
pub extern "C" fn pass_m256_avx2(v: __m256) -> __m256 { v }

#[target_feature(enable = "avx")]
#[inline(never)]
pub extern "C" fn pass_wrap256_avx(w: Wrap256) -> Wrap256 { w }

#[inline(never)]
pub fn pass_m128_rust(v: __m128) -> __m128 { v }

#[inline(never)]
pub fn pass_m256_rust(v: __m256) -> __m256 { v }

#[target_feature(enable = "avx2")]
#[inline(never)]
pub fn pass_m256_rust_avx2(v: __m256) -> __m256 { v }

#[inline(never)]
pub fn caller_baseline_rust_calls_avx2_rust(v: __m256) -> __m256 {
    unsafe { pass_m256_rust_avx2(v) }
}

#[inline(never)]
pub extern "C" fn pass_m128_baseline(v: __m128) -> __m128 { v }
"""
    with tempfile.TemporaryDirectory() as td:
        r = run_rustc(rustc, code_c_ok, td, extra_args=["-Copt-level=2"], emit="llvm-ir", out_name="c_ok.ll")
        ll_sum = {}
        if r["returncode"] == 0 and r["out_path"]:
            ll_sum = extract_llvm_ir_summary(
                Path(r["out_path"]).read_text(encoding="utf-8"),
                (
                    "pass_m256_avx2",
                    "pass_wrap256_avx",
                    "pass_m128_rust",
                    "pass_m256_rust",
                    "pass_m256_rust_avx2",
                    "caller_baseline_rust_calls_avx2_rust",
                    "pass_m128_baseline",
                ),
            )
        results["experiments"]["c_simd_vector_abi_and_target_features"]["default_baseline_sse2_rust_vs_avx2_extern_c"] = {
            "extra_flags": ["-Copt-level=2"],
            "compile_returncode": r["returncode"],
            "compile_stderr": r["stderr"].strip(),
            "llvm_ir_summary": ll_sum,
        }

    code_c_all = code_c_ok + r"""
#[inline(never)]
pub extern "C" fn pass_m256_baseline(v: __m256) -> __m256 { v }
"""
    with tempfile.TemporaryDirectory() as td:
        r = run_rustc(
            rustc,
            code_c_all,
            td,
            extra_args=["-Copt-level=2", "-Ctarget-feature=+avx2"],
            emit="llvm-ir",
            out_name="c_avx2.ll",
        )
        ll_sum = {}
        if r["returncode"] == 0 and r["out_path"]:
            ll_sum = extract_llvm_ir_summary(
                Path(r["out_path"]).read_text(encoding="utf-8"),
                ("pass_m256_avx2", "pass_m128_rust", "pass_m256_rust", "pass_m128_baseline", "pass_m256_baseline"),
            )
        results["experiments"]["c_simd_vector_abi_and_target_features"]["global_avx2_target_feature_flag"] = {
            "extra_flags": ["-Copt-level=2", "-Ctarget-feature=+avx2"],
            "compile_returncode": r["returncode"],
            "compile_stderr": r["stderr"].strip(),
            "llvm_ir_summary": ll_sum,
        }

    # --- C4: 512-bit __m512 threshold (`avx2` rejected, `avx512f` -> <16 x float>) + rlib monomorphization deferment ---
    code_c_512_rlib_defer = r"""
use std::arch::x86_64::__m512;

#[target_feature(enable = "avx2")]
pub extern "C" fn uninstantiated_rlib_avx2_m512(v: __m512) -> __m512 { v }
"""
    with tempfile.TemporaryDirectory() as td:
        r = run_rustc(rustc, code_c_512_rlib_defer, td, extra_args=["-Copt-level=2"], emit="llvm-ir", out_name="c512_defer.ll")
        ll_sum = {}
        if r["returncode"] == 0 and r["out_path"]:
            ll_sum = extract_llvm_ir_summary(Path(r["out_path"]).read_text(encoding="utf-8"), ("m512",))
        results["experiments"]["c_simd_vector_abi_and_target_features"]["rlib_uninstantiated_m512_deferred"] = {
            "extra_flags": ["--crate-type=lib", "-Copt-level=2"],
            "compile_returncode": r["returncode"],
            "llvm_ir_summary": ll_sum,
        }

    code_c_512_rej = r"""
use std::arch::x86_64::__m512;

#[target_feature(enable = "avx2")]
#[inline(never)]
pub extern "C" fn bad_m512_with_avx2_only(v: __m512) -> __m512 { v }
"""
    with tempfile.TemporaryDirectory() as td:
        r = run_rustc(rustc, code_c_512_rej, td, extra_args=["-Copt-level=2"], emit="llvm-ir", out_name="c512_rej.ll")
        results["experiments"]["c_simd_vector_abi_and_target_features"]["m512_avx2_only_rejected"] = {
            "extra_flags": ["--crate-type=lib", "-Copt-level=2"],
            "compile_returncode": r["returncode"],
            "compile_stderr": r["stderr"].strip(),
        }

    code_c_512_ok = r"""
use std::arch::x86_64::__m512;

#[target_feature(enable = "avx512f")]
#[inline(never)]
pub extern "C" fn pass_m512_avx512f(v: __m512) -> __m512 { v }

#[inline(never)]
pub fn pass_m512_rust(v: __m512) -> __m512 { v }
"""
    with tempfile.TemporaryDirectory() as td:
        r = run_rustc(rustc, code_c_512_ok, td, extra_args=["-Copt-level=2"], emit="llvm-ir", out_name="c512_ok.ll")
        ll_sum = {}
        if r["returncode"] == 0 and r["out_path"]:
            ll_sum = extract_llvm_ir_summary(Path(r["out_path"]).read_text(encoding="utf-8"), ("pass_m512",))
        results["experiments"]["c_simd_vector_abi_and_target_features"]["m512_avx512f_vs_rust"] = {
            "extra_flags": ["--crate-type=lib", "-Copt-level=2"],
            "compile_returncode": r["returncode"],
            "llvm_ir_summary": ll_sum,
        }

    return results


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--rustc", default="rustc")
    parser.add_argument("--out", default="-")
    args = parser.parse_args()
    data = run_all_probes(args.rustc)
    encoded = json.dumps(data, indent=2) + "\n"
    if args.out == "-":
        sys.stdout.write(encoded)
    else:
        Path(args.out).write_text(encoded, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
