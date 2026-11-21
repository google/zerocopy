#!/usr/bin/env python3
"""Reproducible primary-source compiler, IR, disassembly, and execution probe for:
1. Rust `#[target_feature]` safety (RFC 2396 / Rust 1.86+), `FnPtr` coercion,
   `Fn`-trait exclusion, `#[inline]` / `#[inline(always)]` cross-feature gates,
   and `#[rustc_legacy_const_generics]` immediate bounds checking;
2. Dynamic CPUID dispatch (`is_x86_feature_detected!`) MIR inliner behavior,
   LLVM `target-features` attribute emission, `-O2`/`-O3` x86-64 instruction
   hoisting absence, and live hardware `SIGILL` counterfactuals on CPUs lacking
   `avx512f`;
3. `core::intrinsics::simd` (`simd_add`, `simd_shuffle`, `simd_bitmask`,
   `simd_select`, `simd_select_bitmask`, `simd_cast`, `simd_as`,
   `simd_masked_load`, `simd_masked_store`) LLVM IR lowering, x86-64 SSE2/AVX2
   disassembly, and native execution parity.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


def find_rustc() -> str:
    env_rustc = os.environ.get("RUSTC")
    if env_rustc and shutil.which(env_rustc):
        return shutil.which(env_rustc) or env_rustc
    which_rustc = shutil.which("rustc")
    if which_rustc:
        return which_rustc
    cargo_rustc = Path.home() / ".cargo" / "bin" / "rustc"
    if cargo_rustc.exists():
        return str(cargo_rustc)
    raise RuntimeError("rustc executable not found in PATH or ~/.cargo/bin/rustc")


def find_llvm_objdump(rustc_bin: str) -> str | None:
    sysroot_proc = subprocess.run(
        [rustc_bin, "--print", "sysroot"],
        capture_output=True,
        text=True,
        check=True,
    )
    sysroot = Path(sysroot_proc.stdout.strip())
    for candidate in sysroot.glob("lib/rustlib/*/bin/llvm-objdump"):
        if candidate.exists():
            return str(candidate)
    return shutil.which("llvm-objdump") or shutil.which("objdump")


def sanitize_text(text: str) -> str:
    """Strip workstation-local paths so output artifacts remain portable."""
    home = str(Path.home())
    if home and home != "/":
        text = text.replace(home, "<HOME>")
    text = re.sub(r"/tmp/tmp[A-Za-z0-9_]+", "/tmp/<probe>", text)
    return text


def detect_host_cpu() -> dict[str, Any]:
    info: dict[str, Any] = {
        "arch": os.uname().machine,
        "model_name": "unknown",
        "flags": [],
    }
    cpuinfo = Path("/proc/cpuinfo")
    if cpuinfo.exists():
        raw = cpuinfo.read_text(encoding="utf-8", errors="replace")
        for line in raw.splitlines():
            if line.startswith("model name") and ":" in line:
                info["model_name"] = line.split(":", 1)[1].strip()
            elif line.startswith("flags") and ":" in line:
                flags = sorted(set(line.split(":", 1)[1].strip().split()))
                info["flags"] = flags
                break
    interesting = [
        "sse",
        "sse2",
        "ssse3",
        "sse4_1",
        "sse4_2",
        "avx",
        "avx2",
        "fma",
        "bmi1",
        "bmi2",
        "avx512f",
        "avx512bw",
        "avx512vl",
    ]
    info["feature_presence"] = {f: (f in info["flags"]) for f in interesting}
    return info


def run_rustc(
    rustc_bin: str,
    src_code: str,
    extra_args: list[str],
    tmpdir: Path,
    stem: str,
) -> tuple[subprocess.CompletedProcess[str], Path]:
    src_path = tmpdir / f"{stem}.rs"
    src_path.write_text(src_code, encoding="utf-8")
    cmd = [rustc_bin, "--edition=2021", *extra_args, str(src_path)]
    proc = subprocess.run(cmd, cwd=tmpdir, capture_output=True, text=True)
    return proc, tmpdir


def first_error_info(stderr: str) -> dict[str, str]:
    err_codes = re.findall(r"error(?:\[(E\d{4})\])?: ([^\n]+)", stderr)
    notes = [
        line.strip()
        for line in stderr.splitlines()
        if line.strip().startswith("= note:") or line.strip().startswith("note:")
    ]
    if err_codes:
        code, msg = err_codes[0]
        return {
            "error_code": code or "unnumbered",
            "message": sanitize_text(msg.strip()),
            "notes": [sanitize_text(n) for n in notes[:4]],
        }
    return {
        "error_code": "",
        "message": sanitize_text(stderr.strip().splitlines()[0]) if stderr.strip() else "",
        "notes": [sanitize_text(n) for n in notes[:4]],
    }


def probe_part1_type_and_attr_matrix(rustc_bin: str, tmpdir: Path) -> dict[str, Any]:
    results: dict[str, Any] = {}

    # S01: Safe #[target_feature(enable = "avx2")] calling avx2, implied sse4.1, and
    # safe #[rustc_legacy_const_generics(2)] _mm256_blend_epi32 without unsafe!
    s01_src = r"""
use core::arch::x86_64::{
    __m128i, _mm256_add_epi32, _mm256_blend_epi32, _mm256_castsi256_si128,
    _mm256_set1_epi32, _mm_extract_epi32,
};

#[target_feature(enable = "sse4.1")]
fn sse41_extract_lane1(lo: __m128i) -> i32 {
    _mm_extract_epi32::<1>(lo)
}

#[target_feature(enable = "avx2")]
fn avx2_callee(a: i32, b: i32) -> i32 {
    let va = _mm256_set1_epi32(a);
    let vb = _mm256_set1_epi32(b);
    // Positional 3rd argument rewritten via #[rustc_legacy_const_generics(2)]
    let blended = _mm256_blend_epi32(va, vb, 0b1010_1010);
    let doubled = _mm256_add_epi32(blended, va);
    let lo = _mm256_castsi256_si128(doubled);
    // Safe call to sse4.1 callee without `unsafe` (avx2 => avx => sse4.2 => sse4.1)
    sse41_extract_lane1(lo)
}

#[target_feature(enable = "avx2")]
pub fn avx2_caller(x: i32) -> i32 {
    // Safe call to avx2 callee without `unsafe`
    avx2_callee(x, 100)
}

fn main() {
    if std::arch::is_x86_feature_detected!("avx2") {
        let got = unsafe { avx2_caller(7) };
        assert_eq!(got, 107);
        println!("s01_ok={got}");
    }
}
"""
    out_bin = tmpdir / "s01_bin"
    p, _ = run_rustc(rustc_bin, s01_src, ["-O", "-o", str(out_bin)], tmpdir, "s01")
    run_rc = None
    run_stdout = ""
    if p.returncode == 0 and out_bin.exists():
        rp = subprocess.run([str(out_bin)], capture_output=True, text=True)
        run_rc = rp.returncode
        run_stdout = rp.stdout.strip()
    results["s01_avx2_calls_avx2_and_sse41_and_blend_safe"] = {
        "compile_rc": p.returncode,
        "run_rc": run_rc,
        "run_stdout": run_stdout,
    }

    # S02: Safe avx2 calling safe avx512f without unsafe -> compile-fail E0133
    s02_src = r"""
#[target_feature(enable = "avx512f")]
pub fn avx512_callee(x: u32) -> u32 { x + 1 }

#[target_feature(enable = "avx2")]
pub fn avx2_caller(x: u32) -> u32 {
    avx512_callee(x)
}
"""
    p, _ = run_rustc(
        rustc_bin, s02_src, ["--crate-type=lib", "--emit=metadata"], tmpdir, "s02"
    )
    results["s02_avx2_calls_avx512f_without_unsafe"] = {
        "compile_rc": p.returncode,
        **first_error_info(p.stderr),
    }

    # S03: Baseline fn calling safe avx2 fn without unsafe EVEN WITH -C target-feature=+avx2
    s03_src = r"""
#[target_feature(enable = "avx2")]
pub fn avx2_callee(x: u32) -> u32 { x + 1 }

pub fn baseline_caller(x: u32) -> u32 {
    avx2_callee(x)
}
"""
    p, _ = run_rustc(
        rustc_bin,
        s03_src,
        ["--crate-type=lib", "-C", "target-feature=+avx2", "--emit=metadata"],
        tmpdir,
        "s03",
    )
    results["s03_baseline_calls_avx2_even_with_cli_target_feature"] = {
        "compile_rc": p.returncode,
        **first_error_info(p.stderr),
    }

    # S04: Baseline fn coercing safe avx2 fn to safe fn(u32) -> u32 pointer -> E0308
    s04_src = r"""
#[target_feature(enable = "avx2")]
pub fn avx2_callee(x: u32) -> u32 { x + 1 }

pub fn coerce_in_baseline() -> fn(u32) -> u32 {
    avx2_callee
}
"""
    p, _ = run_rustc(
        rustc_bin, s04_src, ["--crate-type=lib", "--emit=metadata"], tmpdir, "s04"
    )
    results["s04_baseline_coerces_avx2_to_safe_fnptr"] = {
        "compile_rc": p.returncode,
        **first_error_info(p.stderr),
    }

    # S05: Baseline fn coercing safe avx2 fn to `unsafe fn(u32) -> u32` -> OK
    s05_src = r"""
#[target_feature(enable = "avx2")]
pub fn avx2_callee(x: u32) -> u32 { x + 1 }

pub fn coerce_to_unsafe_fnptr() -> unsafe fn(u32) -> u32 {
    avx2_callee
}
"""
    p, _ = run_rustc(
        rustc_bin, s05_src, ["--crate-type=lib", "--emit=metadata"], tmpdir, "s05"
    )
    results["s05_baseline_coerces_avx2_to_unsafe_fnptr"] = {
        "compile_rc": p.returncode,
    }

    # S06: Capability-witness reification: INSIDE #[target_feature(enable = "avx2")],
    # adjust_target_feature_sig allows coercing avx2_callee to a SAFE `fn(u32) -> u32`
    # and returning it to baseline code!
    s06_src = r"""
#[target_feature(enable = "avx2")]
fn avx2_callee(x: u32) -> u32 {
    x.wrapping_mul(3).wrapping_add(5)
}

#[target_feature(enable = "avx2")]
pub fn avx2_witness_exporter() -> fn(u32) -> u32 {
    avx2_callee
}

fn baseline_consumer(f: fn(u32) -> u32, x: u32) -> u32 {
    f(x)
}

fn main() {
    if std::arch::is_x86_feature_detected!("avx2") {
        let safe_ptr: fn(u32) -> u32 = unsafe { avx2_witness_exporter() };
        let res = baseline_consumer(safe_ptr, 12);
        assert_eq!(res, 41);
        println!("s06_ok={res}");
    }
}
"""
    out_s06 = tmpdir / "s06_bin"
    p, _ = run_rustc(rustc_bin, s06_src, ["-O", "-o", str(out_s06)], tmpdir, "s06")
    s06_run_rc = None
    s06_stdout = ""
    if p.returncode == 0 and out_s06.exists():
        rp = subprocess.run([str(out_s06)], capture_output=True, text=True)
        s06_run_rc = rp.returncode
        s06_stdout = rp.stdout.strip()
    results["s06_avx2_reifies_avx2_to_safe_fnptr_witness"] = {
        "compile_rc": p.returncode,
        "run_rc": s06_run_rc,
        "run_stdout": s06_stdout,
    }

    # S07: Safe avx2 fn item does NOT implement `Fn(u32) -> u32` EVEN inside an avx2 caller
    s07_src = r"""
fn apply_fn<F: Fn(u32) -> u32>(f: F, x: u32) -> u32 { f(x) }

#[target_feature(enable = "avx2")]
fn avx2_callee(x: u32) -> u32 { x + 1 }

#[target_feature(enable = "avx2")]
pub fn avx2_caller(x: u32) -> u32 {
    apply_fn(avx2_callee, x)
}
"""
    p, _ = run_rustc(
        rustc_bin, s07_src, ["--crate-type=lib", "--emit=metadata"], tmpdir, "s07"
    )
    results["s07_avx2_fndef_implements_fn_trait_inside_avx2"] = {
        "compile_rc": p.returncode,
        **first_error_info(p.stderr),
    }

    # S08: Safe trait method implementation cannot carry #[target_feature]
    s08_src = r"""
pub trait Compute {
    fn compute(&self, x: u32) -> u32;
}
pub struct AvxImpl;
impl Compute for AvxImpl {
    #[target_feature(enable = "avx2")]
    fn compute(&self, x: u32) -> u32 { x + 1 }
}
"""
    p, _ = run_rustc(
        rustc_bin, s08_src, ["--crate-type=lib", "--emit=metadata"], tmpdir, "s08"
    )
    results["s08_target_feature_on_safe_trait_impl_method"] = {
        "compile_rc": p.returncode,
        **first_error_info(p.stderr),
    }

    # S09: #[inline(always)] + #[target_feature(enable = "avx2")]
    s09_src = r"""
#[inline(always)]
#[target_feature(enable = "avx2")]
pub fn avx2_inline_always(x: u32) -> u32 { x + 1 }
"""
    p, _ = run_rustc(
        rustc_bin, s09_src, ["--crate-type=lib", "--emit=metadata"], tmpdir, "s09"
    )
    results["s09_inline_always_with_target_feature"] = {
        "compile_rc": p.returncode,
        **first_error_info(p.stderr),
    }

    # S10: #[rustc_legacy_const_generics(2)] immediate out of 8-bit unsigned bounds (IMM8 = 256)
    s10_src = r"""
use core::arch::x86_64::{__m256i, _mm256_blend_epi32};

#[target_feature(enable = "avx2")]
pub fn bad_blend_imm(a: __m256i, b: __m256i) -> __m256i {
    _mm256_blend_epi32(a, b, 256)
}
"""
    p, _ = run_rustc(
        rustc_bin, s10_src, ["--crate-type=lib", "--emit=llvm-ir"], tmpdir, "s10"
    )
    results["s10_legacy_const_generics_imm8_256_oob"] = {
        "compile_rc": p.returncode,
        **first_error_info(p.stderr),
    }

    # S11: #[rustc_legacy_const_generics(2)] passed a non-constant runtime variable
    s11_src = r"""
use core::arch::x86_64::{__m256i, _mm256_blend_epi32};

#[target_feature(enable = "avx2")]
pub fn nonconst_blend_imm(a: __m256i, b: __m256i, mask: i32) -> __m256i {
    _mm256_blend_epi32(a, b, mask)
}
"""
    p, _ = run_rustc(
        rustc_bin, s11_src, ["--crate-type=lib", "--emit=metadata"], tmpdir, "s11"
    )
    results["s11_legacy_const_generics_runtime_arg"] = {
        "compile_rc": p.returncode,
        **first_error_info(p.stderr),
    }

    # S12: Cross-target aarch64-unknown-linux-gnu (#![no_core]) verifying sve2 -> sve -> neon
    # AND testing sve -> fp16 (which changed from &["neon"] in 1.98.0-nightly to &["neon", "fp16"] in 1.99.1!)
    s12_ok_src = r"""
#![feature(no_core, lang_items)]
#![allow(internal_features)]
#![no_core]

#[lang = "pointee_sized"]
pub trait PointeeSized {}
#[lang = "meta_sized"]
pub trait MetaSized: PointeeSized {}
#[lang = "sized"]
pub trait Sized: MetaSized {}
#[lang = "copy"]
pub trait Copy {}

#[no_mangle]
#[target_feature(enable = "neon")]
pub fn aarch64_neon_leaf(x: u32) -> u32 { x }

#[no_mangle]
#[target_feature(enable = "fp16")]
pub fn aarch64_fp16_leaf(x: u32) -> u32 { aarch64_neon_leaf(x) }

#[no_mangle]
#[target_feature(enable = "sve")]
pub fn aarch64_sve_mid(x: u32) -> u32 {
    aarch64_neon_leaf(x)
}

#[no_mangle]
#[target_feature(enable = "sve2")]
pub fn aarch64_sve2_top(x: u32) -> u32 {
    aarch64_sve_mid(x)
}
"""
    p_a64_ok, _ = run_rustc(
        rustc_bin,
        s12_ok_src,
        [
            "--target=aarch64-unknown-linux-gnu",
            "--crate-type=lib",
            "-C",
            "opt-level=2",
            "--emit=llvm-ir",
        ],
        tmpdir,
        "s12_a64_ok",
    )
    a64_attrs: dict[str, str] = {}
    if p_a64_ok.returncode == 0:
        ll_text = (tmpdir / "s12_a64_ok.ll").read_text(encoding="utf-8")
        attr_defs = dict(
            re.findall(r"^(attributes #\d+) = \{ ([^\n]+) \}$", ll_text, flags=re.M)
        )
        for fn_name in [
            "aarch64_neon_leaf",
            "aarch64_fp16_leaf",
            "aarch64_sve_mid",
            "aarch64_sve2_top",
        ]:
            m = re.search(rf"define [^\n]*@{re.escape(fn_name)}[^\n]*#(0|[1-9]\d*)", ll_text)
            if m:
                attr_key = f"attributes #{m.group(1)}"
                raw_attr = attr_defs.get(attr_key, "")
                tf_m = re.search(r'"target-features"="([^"]+)"', raw_attr)
                a64_attrs[fn_name] = tf_m.group(1) if tf_m else raw_attr

    s12_sve_fp16_src = s12_ok_src + "\n#[target_feature(enable = \"sve\")]\npub fn sve_calls_fp16(x: u32) -> u32 { aarch64_fp16_leaf(x) }\n"
    p_a64_sve_fp16, _ = run_rustc(
        rustc_bin,
        s12_sve_fp16_src,
        ["--target=aarch64-unknown-linux-gnu", "--crate-type=lib", "--emit=metadata"],
        tmpdir,
        "s12_a64_sve_fp16",
    )

    s12_fail_src = s12_ok_src + "\n#[target_feature(enable = \"sve\")]\npub fn bad_sve_to_sve2(x: u32) -> u32 { aarch64_sve2_top(x) }\n"
    p_a64_fail, _ = run_rustc(
        rustc_bin,
        s12_fail_src,
        ["--target=aarch64-unknown-linux-gnu", "--crate-type=lib", "--emit=metadata"],
        tmpdir,
        "s12_a64_fail",
    )
    results["s12_aarch64_sve2_sve_fp16_neon_lattice"] = {
        "sve2_to_sve_to_neon_compile_rc": p_a64_ok.returncode,
        "fp16_to_neon_compile_rc": p_a64_ok.returncode,
        "sve_calling_fp16_compile_rc": p_a64_sve_fp16.returncode,
        "sve_calling_fp16_diagnostic": first_error_info(p_a64_sve_fp16.stderr),
        "llvm_target_features_by_fn": a64_attrs,
        "sve_calling_sve2_without_unsafe_compile_rc": p_a64_fail.returncode,
        "sve_calling_sve2_error": first_error_info(p_a64_fail.stderr),
    }

    return results


def parse_asm_functions(asm_text: str) -> dict[str, list[str]]:
    """Extract instruction lines per mangled/unmangled symbol from rustc `--emit=asm`."""
    funcs: dict[str, list[str]] = {}
    cur_fn: str | None = None
    for raw in asm_text.splitlines():
        line = raw.strip()
        if not line or line.startswith("#") or line.startswith("//"):
            continue
        if line.endswith(":") and not line.startswith("."):
            cur_fn = line[:-1]
            funcs[cur_fn] = []
            continue
        if cur_fn is not None:
            if line.startswith(".cfi_endproc") or line.startswith(".size "):
                cur_fn = None
                continue
            if not line.startswith("."):
                funcs[cur_fn].append(line)
    return funcs


def probe_part2_dispatch_inlining_and_sigill(
    rustc_bin: str, host_cpu: dict[str, Any], tmpdir: Path
) -> dict[str, Any]:
    dispatch_src = r"""
use core::arch::x86_64::{
    __m128i, __m256i, __m512i, _mm256_add_epi32, _mm256_blend_epi32, _mm256_castsi256_si128,
    _mm256_extracti128_si256, _mm256_loadu_si256, _mm256_set1_epi32, _mm256_xor_si256,
    _mm_add_epi32, _mm_extract_epi32,
    _mm512_add_epi32, _mm512_loadu_si512, _mm512_reduce_add_epi32, _mm512_set1_epi32, _mm512_xor_si512,
};

#[inline]
#[target_feature(enable = "sse4.1")]
fn sse41_helper(lo: __m128i) -> i32 {
    _mm_extract_epi32::<0>(lo).wrapping_add(_mm_extract_epi32::<3>(lo))
}

#[inline]
#[target_feature(enable = "avx2")]
fn avx2_same_feat_helper(v: __m256i, mask_seed: i32) -> __m256i {
    let m = _mm256_set1_epi32(mask_seed);
    let x = _mm256_xor_si256(v, m);
    _mm256_blend_epi32(x, v, 0b0101_0101)
}

// Intentionally private + #[inline] (NO #[no_mangle]) so LLVM sees `internal` linkage
// + `inlinehint`, proving that cross-feature inlining is blocked strictly by
// `TTI.areInlineCompatible` on `"target-features"` rather than external linkage!
#[inline]
#[target_feature(enable = "avx2")]
fn avx2_kernel_entry(words: &[i32; 8], seed: i32) -> i32 {
    let loaded = unsafe { _mm256_loadu_si256(words.as_ptr() as *const __m256i) };
    let mixed = avx2_same_feat_helper(loaded, seed);
    let sum = _mm256_add_epi32(mixed, _mm256_set1_epi32(10));
    let lo = _mm256_castsi256_si128(sum);
    let hi = _mm256_extracti128_si256::<1>(sum);
    sse41_helper(_mm_add_epi32(lo, hi))
}

#[inline]
#[target_feature(enable = "avx512f")]
fn avx512_kernel_entry(words16: &[i32; 16], y: i32) -> i32 {
    let vx = unsafe { _mm512_loadu_si512(words16.as_ptr() as *const __m512i) };
    let vy = _mm512_set1_epi32(y);
    let vz = _mm512_add_epi32(_mm512_xor_si512(vx, vy), _mm512_set1_epi32(1));
    _mm512_reduce_add_epi32(vz)
}

#[no_mangle]
#[inline(never)]
pub fn baseline_dispatch_avx2(words: &[i32; 8], seed: i32) -> i32 {
    if std::arch::is_x86_feature_detected!("avx2") {
        unsafe { avx2_kernel_entry(words, seed) }
    } else {
        // bit 0 = 1 -> words[0], bit 4 = 1 -> words[4]
        // bit 3 = 0 -> words[3] ^ seed, bit 7 = 0 -> words[7] ^ seed
        let lane0 = (words[0] + 10) + (words[4] + 10);
        let lane3 = ((words[3] ^ seed) + 10) + ((words[7] ^ seed) + 10);
        lane0.wrapping_add(lane3)
    }
}

#[no_mangle]
#[inline(never)]
pub fn baseline_dispatch_avx512f(words16: &[i32; 16], y: i32) -> i32 {
    if std::arch::is_x86_feature_detected!("avx512f") {
        unsafe { avx512_kernel_entry(words16, y) }
    } else {
        let mut acc = 0i32;
        let mut i = 0;
        while i < 16 {
            acc = acc.wrapping_add((words16[i] ^ y).wrapping_add(1));
            i += 1;
        }
        acc
    }
}

fn main() {
    let words = [10, 20, 30, 40, 50, 60, 70, 80];
    let r_avx2 = baseline_dispatch_avx2(&words, 0x55);
    assert_eq!(r_avx2, 230);
    let words16 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16];
    let r_512 = baseline_dispatch_avx512f(&words16, 5);
    let mut expected_512 = 0i32;
    for w in words16 {
        expected_512 += (w ^ 5) + 1;
    }
    assert_eq!(r_512, expected_512);
    println!("dispatch_avx2={r_avx2} dispatch_avx512f={r_512}");
}
"""
    opt_results: dict[str, Any] = {}
    for opt in ["2", "3"]:
        stem = f"dispatch_o{opt}"
        proc, _ = run_rustc(
            rustc_bin,
            dispatch_src,
            [
                f"-Copt-level={opt}",
                "--emit=mir,llvm-ir,asm,link",
                "-C",
                "llvm-args=-x86-asm-syntax=att",
            ],
            tmpdir,
            stem,
        )
        if proc.returncode != 0:
            raise RuntimeError(f"{stem} failed:\n{proc.stderr}")
        built_bin = tmpdir / stem
        mir_text = (tmpdir / f"{stem}.mir").read_text(encoding="utf-8")
        ll_text = (tmpdir / f"{stem}.ll").read_text(encoding="utf-8")
        asm_text = (tmpdir / f"{stem}.s").read_text(encoding="utf-8")

        mir_blocks: dict[str, str] = {}
        for fn_name in [
            "avx2_kernel_entry",
            "baseline_dispatch_avx2",
            "baseline_dispatch_avx512f",
        ]:
            m = re.search(
                rf"^fn [^\n]*{re.escape(fn_name)}\([^\n]*\{{\n(.*?)^\}}",
                mir_text,
                flags=re.M | re.S,
            )
            if m:
                mir_blocks[fn_name] = m.group(1)

        avx2_mir = mir_blocks.get("avx2_kernel_entry", "")
        disp_avx2_mir = mir_blocks.get("baseline_dispatch_avx2", "")
        disp_512_mir = mir_blocks.get("baseline_dispatch_avx512f", "")

        attr_defs = dict(
            re.findall(r"^(attributes #\d+) = \{ ([^\n]+) \}$", ll_text, flags=re.M)
        )
        fn_llvm_attrs: dict[str, dict[str, Any]] = {}
        for fn_name in [
            "baseline_dispatch_avx2",
            "baseline_dispatch_avx512f",
            "avx2_kernel_entry",
            "avx512_kernel_entry",
        ]:
            m = re.search(
                rf"^define [^\n]*@[^\n]*{re.escape(fn_name)}[^\n]*#(0|[1-9]\d*) \{{\n(.*?)^\}}",
                ll_text,
                flags=re.M | re.S,
            )
            if m:
                aid = f"attributes #{m.group(1)}"
                body = m.group(2)
                raw_a = attr_defs.get(aid, "")
                tf_m = re.search(r'"target-features"="([^"]+)"', raw_a)
                fn_llvm_attrs[fn_name] = {
                    "attr_group": aid,
                    "has_inlinehint": "inlinehint" in raw_a.split(),
                    "has_noinline": "noinline" in raw_a.split(),
                    "target_features": tf_m.group(1) if tf_m else None,
                    "ir_contains_call_to_kernel": (
                        "avx2_kernel_entry" in body
                        if "avx2" in fn_name and "dispatch" in fn_name
                        else (
                            "avx512_kernel_entry" in body
                            if "avx512" in fn_name and "dispatch" in fn_name
                            else False
                        )
                    ),
                    "ir_contains_sse41_helper_call": "sse41_helper" in body,
                    "ir_contains_avx2_helper_call": "avx2_same_feat_helper" in body,
                }

        asm_funcs = parse_asm_functions(asm_text)
        asm_summary: dict[str, Any] = {}
        for fn_name in [
            "baseline_dispatch_avx2",
            "baseline_dispatch_avx512f",
            "avx2_kernel_entry",
            "avx512_kernel_entry",
        ]:
            matched_sym = next(
                (sym for sym in asm_funcs if sym == fn_name or fn_name in sym),
                None,
            )
            insns = asm_funcs.get(matched_sym, []) if matched_sym else []
            ymm_insns = [i for i in insns if "%ymm" in i]
            zmm_insns = [i for i in insns if "%zmm" in i]
            vex_evex_insns = [
                i
                for i in insns
                if re.match(r"^v[a-z0-9]+\b", i)
            ]
            call_insns = [
                i
                for i in insns
                if i.startswith("call")
                or (i.startswith("jmp") and "kernel_entry" in i)
            ]
            asm_summary[fn_name] = {
                "symbol_matched": bool(matched_sym),
                "total_insns": len(insns),
                "ymm_insns_count": len(ymm_insns),
                "zmm_insns_count": len(zmm_insns),
                "vex_or_evex_insns_count": len(vex_evex_insns),
                "sample_vector_insns": vex_evex_insns[:8],
                "call_or_tailjmp_insns": [sanitize_text(c) for c in call_insns],
            }

        rp = subprocess.run([str(built_bin)], capture_output=True, text=True)
        opt_results[f"O{opt}"] = {
            "compile_rc": proc.returncode,
            "run_rc": rp.returncode,
            "run_stdout": rp.stdout.strip(),
            "mir_inliner_observations": {
                "mir_inlined_equal_feature_stdarch_mm256_add_epi32": (
                    "inlined _mm256_add_epi32" in avx2_mir
                ),
                "mir_inlined_equal_feature_stdarch_mm256_extracti128": (
                    "inlined _mm256_extracti128_si256" in avx2_mir
                ),
                "mir_preserved_subset_avx_mm256_castsi256_si128_call": (
                    "= _mm256_castsi256_si128(" in avx2_mir
                ),
                "mir_preserved_subset_sse2_mm_add_epi32_call": (
                    "= _mm_add_epi32(" in avx2_mir
                ),
                "mir_preserved_subset_sse41_helper_call": (
                    "= sse41_helper(" in avx2_mir
                ),
                "baseline_dispatch_mir_preserved_avx2_kernel_call": (
                    "= avx2_kernel_entry(" in disp_avx2_mir
                ),
                "baseline_dispatch_mir_preserved_avx512_kernel_call": (
                    "= avx512_kernel_entry(" in disp_512_mir
                ),
            },
            "llvm_ir_summary": fn_llvm_attrs,
            "x86_64_asm_summary": asm_summary,
        }

    # Counterfactual hardware fault probes on hosts lacking avx512f!
    counterfactuals: dict[str, Any] = {
        "host_supports_avx512f": host_cpu["feature_presence"].get("avx512f", False),
    }

    # Counterfactual CE1: What happens when caller & callee share +avx512f (simulating
    # unchecked cross-feature inlining into the caller) so LLVM inlines and hoists a pure
    # EVEX `%zmm` computation BEFORE a runtime `guard == false` check!
    ce1_src = r"""
use core::arch::x86_64::{
    __m512i, _mm512_add_epi32, _mm512_loadu_si512, _mm512_reduce_add_epi32,
    _mm512_set1_epi32, _mm512_xor_si512,
};

#[inline(always)]
fn simulated_inlined_avx512_op(words16: &[i32; 16], y: i32) -> i32 {
    unsafe {
        let vx = _mm512_loadu_si512(words16.as_ptr() as *const __m512i);
        let vy = _mm512_set1_epi32(y);
        _mm512_reduce_add_epi32(_mm512_add_epi32(_mm512_xor_si512(vx, vy), _mm512_set1_epi32(7)))
    }
}

#[no_mangle]
#[inline(never)]
pub fn unchecked_hoisted_caller(guards: &[bool], words16: &[i32; 16], y: i32) -> i32 {
    let mut acc = 0i32;
    for &g in guards {
        // Loop-invariant pure AVX-512 expression inside guarded `if g` branch!
        // When inlined into a caller compiled with +avx512f, LLVM LICM hoists the
        // EVEX %zmm load/xor/add/reduce into the loop preheader BEFORE checking `g`!
        if g {
            acc = acc.wrapping_add(simulated_inlined_avx512_op(words16, y));
        } else {
            acc = acc.wrapping_add(1);
        }
    }
    acc
}

fn main() {
    // All guards are `false` at runtime (matching CPUID == false on a non-AVX-512 CPU)!
    let guards = std::hint::black_box([false, false, false, false]);
    let words16 = std::hint::black_box([1i32; 16]);
    let out = unchecked_hoisted_caller(&guards, &words16, std::hint::black_box(22));
    println!("out={out}");
}
"""
    p_ce1, _ = run_rustc(
        rustc_bin,
        ce1_src,
        [
            "-Copt-level=3",
            "-Ctarget-feature=+avx512f",
            "--emit=asm,link",
            "-C",
            "llvm-args=-x86-asm-syntax=att",
        ],
        tmpdir,
        "ce1_hoist",
    )
    ce1_asm = parse_asm_functions((tmpdir / "ce1_hoist.s").read_text(encoding="utf-8"))
    ce1_insns = ce1_asm.get("unchecked_hoisted_caller", [])
    ce1_zmm = [i for i in ce1_insns if "%zmm" in i]
    ce1_bin = tmpdir / "ce1_hoist"
    ce1_run = subprocess.run([str(ce1_bin)], capture_output=True, text=True)
    counterfactuals["ce1_unchecked_cross_feature_inlining_and_licm_hoisting"] = {
        "compile_rc": p_ce1.returncode,
        "caller_zmm_insns_count": len(ce1_zmm),
        "caller_zmm_insns": ce1_zmm[:8],
        "all_runtime_guards_false": True,
        "execution_returncode": ce1_run.returncode,
        "terminated_by_sigill": (ce1_run.returncode == -int(signal.SIGILL)),
    }

    # Counterfactual CE2: Coercing safe #[target_feature(enable = "avx512f")] fn to a
    # function pointer via unsafe transmute (simulating what happens if TypeError::TargetFeatureCast
    # were absent and baseline safe code received `fn(&[i32; 16]) -> i32`) and calling it on non-AVX-512 silicon!
    ce2_src = r"""
use core::arch::x86_64::{__m512i, _mm512_add_epi32, _mm512_loadu_si512, _mm512_reduce_add_epi32};

#[target_feature(enable = "avx512f")]
pub fn safe_avx512_fn(words16: &[i32; 16]) -> i32 {
    let v = unsafe { _mm512_loadu_si512(words16.as_ptr() as *const __m512i) };
    _mm512_reduce_add_epi32(_mm512_add_epi32(v, v))
}

fn baseline_higher_order(f: fn(&[i32; 16]) -> i32, words16: &[i32; 16]) -> i32 {
    f(words16)
}

fn main() {
    let raw_unsafe_ptr: unsafe fn(&[i32; 16]) -> i32 = safe_avx512_fn;
    let forged_safe_ptr: fn(&[i32; 16]) -> i32 = unsafe { core::mem::transmute(raw_unsafe_ptr) };
    let words16 = std::hint::black_box([3i32; 16]);
    let y = baseline_higher_order(forged_safe_ptr, &words16);
    println!("y={y}");
}
"""
    p_ce2, _ = run_rustc(
        rustc_bin, ce2_src, ["-Copt-level=2"], tmpdir, "ce2_forged_fnptr"
    )
    ce2_bin = tmpdir / "ce2_forged_fnptr"
    ce2_run = subprocess.run([str(ce2_bin)], capture_output=True, text=True)
    counterfactuals["ce2_forged_safe_fnptr_coercion_bypass"] = {
        "compile_rc": p_ce2.returncode,
        "execution_returncode": ce2_run.returncode,
        "terminated_by_sigill": (ce2_run.returncode == -int(signal.SIGILL)),
    }

    return {
        "guarded_dynamic_dispatch": opt_results,
        "hardware_counterfactuals": counterfactuals,
    }


def probe_part3_portable_simd_intrinsics(rustc_bin: str, tmpdir: Path) -> dict[str, Any]:
    # Compile-fail check: simd_shuffle out-of-bounds index (>= 2 * N)
    oob_shuffle_src = r"""
#![feature(repr_simd, core_intrinsics)]
use core::intrinsics::simd::simd_shuffle;

#[repr(simd)]
#[derive(Copy, Clone)]
pub struct U32x4([u32; 4]);

#[repr(simd)]
#[derive(Copy, Clone)]
pub struct Idx4([u32; 4]);

pub fn bad_shuffle(a: U32x4, b: U32x4) -> U32x4 {
    unsafe { simd_shuffle(a, b, const { Idx4([0, 4, 7, 8]) }) }
}
"""
    p_oob, _ = run_rustc(
        rustc_bin,
        oob_shuffle_src,
        ["--crate-type=lib", "--emit=llvm-ir"],
        tmpdir,
        "simd_oob_shuffle",
    )

    # Compile-fail check 2: MCP#838 MIR validator ban on `.0` field projection into `#[repr(simd)]`
    mcp838_proj_src = r"""
#![feature(repr_simd)]
#[repr(simd)]
#[derive(Copy, Clone)]
pub struct U32x4(pub [u32; 4]);

pub fn project_simd_field(v: U32x4) -> [u32; 4] {
    v.0
}
"""
    mcp838_env = dict(os.environ, RUSTC_ICE="0")
    mcp838_path = tmpdir / "simd_mcp838_proj.rs"
    mcp838_path.write_text(mcp838_proj_src, encoding="utf-8")
    p_mcp838 = subprocess.run(
        [rustc_bin, "--edition=2021", "--crate-type=lib", "-Copt-level=2", "--emit=llvm-ir", str(mcp838_path)],
        cwd=tmpdir,
        env=mcp838_env,
        capture_output=True,
        text=True,
    )

    # Full positive execution + IR + disassembly probe across simd_add, simd_shuffle,
    # simd_bitmask (u8, u16, [u8; 2], power-of-2 & non-power-of-2 10-lane),
    # simd_select, simd_select_bitmask, simd_cast, simd_as, simd_masked_load/store!
    simd_src = r"""
#![feature(repr_simd, core_intrinsics)]
#![allow(internal_features)]

use core::intrinsics::simd::{
    SimdAlign, simd_add, simd_as, simd_bitmask, simd_cast, simd_eq,
    simd_masked_load, simd_masked_store, simd_select, simd_select_bitmask,
    simd_shuffle,
};

macro_rules! def_simd {
    ($name:ident, $elem:ty, $lanes:literal) => {
        #[repr(simd)]
        #[derive(Copy, Clone)]
        pub struct $name([$elem; $lanes]);

        impl $name {
            #[inline]
            pub const fn from_array(arr: [$elem; $lanes]) -> Self {
                Self(arr)
            }
            #[inline]
            pub const fn as_array(&self) -> &[$elem; $lanes] {
                // Matches library/stdarch/crates/core_arch/src/macros.rs:116-124 (MCP#838)
                unsafe { &*(self as *const Self as *const [$elem; $lanes]) }
            }
        }
    };
}

def_simd!(U32x4, u32, 4);
def_simd!(U32x8, u32, 8);
def_simd!(I32x8, i32, 8);
def_simd!(I16x8, i16, 8);
def_simd!(U16x8, u16, 8);
def_simd!(I8x16, i8, 16);
def_simd!(U8x16, u8, 16);
def_simd!(I16x10, i16, 10);
def_simd!(F32x4, f32, 4);
def_simd!(I32x4, i32, 4);
def_simd!(Idx4, u32, 4);
def_simd!(Idx16, u32, 16);

#[no_mangle]
#[inline(never)]
pub fn kernel_sse2_shuffle_u32x4(a: U32x4, b: U32x4) -> U32x4 {
    unsafe { simd_shuffle(a, b, const { Idx4::from_array([3, 4, 1, 6]) }) }
}

#[no_mangle]
#[inline(never)]
#[target_feature(enable = "avx2")]
pub fn kernel_avx2_bitmask_u16(m: I8x16) -> u16 {
    unsafe { simd_bitmask(m) }
}

#[no_mangle]
#[inline(never)]
pub fn kernel_sse2_bitmask_bytes(m: I8x16) -> [u8; 2] {
    unsafe { simd_bitmask(m) }
}

#[no_mangle]
#[inline(never)]
pub fn kernel_bitmask_nonpow2_10lanes(m: I16x10) -> (u16, [u8; 2]) {
    unsafe { (simd_bitmask(m), simd_bitmask(m)) }
}

#[no_mangle]
#[inline(never)]
#[target_feature(enable = "avx2")]
pub fn kernel_avx2_select_bitmask_u8x16(mask_bits: u16, yes: U8x16, no: U8x16) -> U8x16 {
    unsafe { simd_select_bitmask(mask_bits, yes, no) }
}

#[no_mangle]
#[inline(never)]
#[target_feature(enable = "avx2")]
pub fn kernel_avx2_select_vec_u8x16(mask: I8x16, yes: U8x16, no: U8x16) -> U8x16 {
    unsafe { simd_select(mask, yes, no) }
}

#[no_mangle]
#[inline(never)]
#[target_feature(enable = "avx2")]
pub fn kernel_avx2_cast_widen_add(s: I16x8, u: U16x8) -> U32x8 {
    unsafe {
        let sw: I32x8 = simd_cast(s);
        let sw_u: U32x8 = simd_cast(sw);
        let uw: U32x8 = simd_cast(u);
        simd_add(sw_u, uw)
    }
}

#[no_mangle]
#[inline(never)]
#[target_feature(enable = "avx2")]
pub fn kernel_avx2_masked_load_store(
    mask: I32x8,
    src: *const u32,
    dst: *mut u32,
    passthrough: U32x8,
) -> U32x8 {
    unsafe {
        let loaded: U32x8 = simd_masked_load::<_, _, _, { SimdAlign::Unaligned }>(
            mask,
            src,
            passthrough,
        );
        simd_masked_store::<_, _, _, { SimdAlign::Unaligned }>(mask, dst, loaded);
        loaded
    }
}

fn main() {
    // 0. Verify repr(simd) power-of-two padding on non-power-of-two lane count I16x10!
    assert_eq!(core::mem::size_of::<[i16; 10]>(), 20);
    assert_eq!(core::mem::size_of::<I16x10>(), 32);
    assert_eq!(core::mem::align_of::<I16x10>(), 32);

    // 1. Verify simd_shuffle lane-wise specification: out[i] = concat(a, b)[idx[i]]
    let a = U32x4::from_array([10, 20, 30, 40]);
    let b = U32x4::from_array([50, 60, 70, 80]);
    let shuf = kernel_sse2_shuffle_u32x4(a, b);
    assert_eq!(*shuf.as_array(), [40, 50, 20, 70]);

    // 2. Verify simd_bitmask & simd_select_bitmask <-> simd_select equivalence across all 256 low/high byte patterns
    let yes = U8x16::from_array([100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115]);
    let no  = U8x16::from_array([200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215]);
    for pat in 0u16..256u16 {
        let full: u16 = pat | ((pat ^ 0xA5) << 8);
        let mut lanes = [0i8; 16];
        for i in 0..16 {
            lanes[i] = if ((full >> i) & 1) == 1 { -1i8 } else { 0i8 };
        }
        let m = I8x16::from_array(lanes);
        let bm_bytes = kernel_sse2_bitmask_bytes(m);
        assert_eq!(u16::from_le_bytes(bm_bytes), full);
        if std::arch::is_x86_feature_detected!("avx2") {
            let bm_u16 = unsafe { kernel_avx2_bitmask_u16(m) };
            assert_eq!(bm_u16, full);
            let sel_vec = unsafe { kernel_avx2_select_vec_u8x16(m, yes, no) };
            let sel_bm  = unsafe { kernel_avx2_select_bitmask_u8x16(bm_u16, yes, no) };
            assert_eq!(*sel_vec.as_array(), *sel_bm.as_array());
            for i in 0..16 {
                let expected = if ((full >> i) & 1) == 1 { yes.as_array()[i] } else { no.as_array()[i] };
                assert_eq!(sel_bm.as_array()[i], expected);
            }
        }
    }

    // 3. Verify non-power-of-two 10-lane bitmask packing from core::intrinsics::simd::mod.rs docstring:
    // [!0, !0, 0, !0, 0, 0, !0, 0, !0, 0] -> 0b0101001011u16 and [0b01001011, 0b01] on little-endian!
    let m10 = I16x10::from_array([-1, -1, 0, -1, 0, 0, -1, 0, -1, 0]);
    let (u10, b10) = kernel_bitmask_nonpow2_10lanes(m10);
    assert_eq!(u10, 0b01_0100_1011u16);
    assert_eq!(b10, [0b0100_1011u8, 0b0000_0001u8]);

    // 4. Verify simd_cast sign/zero extension + simd_as float-to-int saturation
    if std::arch::is_x86_feature_detected!("avx2") {
        let s = I16x8::from_array([-10, -1, 0, 1, 100, -32768, 32767, 42]);
        let u = U16x8::from_array([10, 1, 5, 9, 200, 32768, 1, 58]);
        let widened = unsafe { kernel_avx2_cast_widen_add(s, u) };
        assert_eq!(*widened.as_array(), [0, 0, 5, 10, 300, 0, 32768, 100]);
    }
    let floats = F32x4::from_array([f32::NAN, f32::INFINITY, -1.0e20, -42.9]);
    let sat_i32: I32x4 = unsafe { simd_as(floats) };
    assert_eq!(*sat_i32.as_array(), [0, i32::MAX, i32::MIN, -42]);

    // 5. Verify simd_masked_load and simd_masked_store leave masked-off lanes untouched
    if std::arch::is_x86_feature_detected!("avx2") {
        // Only 5 valid elements in backing slice; lanes 5, 6, 7 are masked off!
        let short_src: [u32; 5] = [11, 22, 33, 44, 55];
        let mut dst_buf: [u32; 8] = [900, 901, 902, 903, 904, 905, 906, 907];
        let mask = I32x8::from_array([-1, 0, -1, 0, -1, 0, 0, 0]);
        let passthrough = U32x8::from_array([70, 71, 72, 73, 74, 75, 76, 77]);
        let loaded = unsafe {
            kernel_avx2_masked_load_store(mask, short_src.as_ptr(), dst_buf.as_mut_ptr(), passthrough)
        };
        assert_eq!(*loaded.as_array(), [11, 71, 33, 73, 55, 75, 76, 77]);
        assert_eq!(dst_buf, [11, 901, 33, 903, 55, 905, 906, 907]);
    }

    // 6. Verify simd_eq produces all-ones (-1) / all-zeros (0) lane masks
    let eq_mask: I32x4 = unsafe { simd_eq(U32x4::from_array([1, 2, 3, 4]), U32x4::from_array([1, 9, 3, 8])) };
    assert_eq!(*eq_mask.as_array(), [-1, 0, -1, 0]);

    println!("portable_simd_parity_ok=256_patterns_plus_masked_mem_plus_i16x10_pad32");
}
"""
    p_simd, _ = run_rustc(
        rustc_bin,
        simd_src,
        [
            "-Copt-level=2",
            "--emit=llvm-ir,asm,link",
            "-C",
            "llvm-args=-x86-asm-syntax=att",
        ],
        tmpdir,
        "simd_probe",
    )
    simd_bin = tmpdir / "simd_probe"
    simd_run = subprocess.run([str(simd_bin)], capture_output=True, text=True)
    ll_text = (tmpdir / "simd_probe.ll").read_text(encoding="utf-8")
    asm_funcs = parse_asm_functions((tmpdir / "simd_probe.s").read_text(encoding="utf-8"))

    # Extract concise IR snippets for each kernel in pre-opt / post-opt LLVM IR
    # Also emit unoptimized `-Copt-level=0 --emit=llvm-ir` so we capture exact pre-InstCombine
    # lowering emitted directly by `rustc_codegen_llvm/src/intrinsic.rs`!
    p_simd_o0, _ = run_rustc(
        rustc_bin,
        simd_src,
        ["-Copt-level=0", "--emit=llvm-ir"],
        tmpdir,
        "simd_probe_o0",
    )
    ll_o0 = (tmpdir / "simd_probe_o0.ll").read_text(encoding="utf-8")

    o0_ir_snippets: dict[str, list[str]] = {}
    for fn_name in [
        "kernel_sse2_shuffle_u32x4",
        "kernel_avx2_bitmask_u16",
        "kernel_sse2_bitmask_bytes",
        "kernel_bitmask_nonpow2_10lanes",
        "kernel_avx2_select_bitmask_u8x16",
        "kernel_avx2_select_vec_u8x16",
        "kernel_avx2_cast_widen_add",
        "kernel_avx2_masked_load_store",
    ]:
        m = re.search(
            rf"^define [^\n]*@{re.escape(fn_name)}\([^\n]*\{{\n(.*?)^\}}",
            ll_o0,
            flags=re.M | re.S,
        )
        if m:
            interesting_lines = [
                ln.strip()
                for ln in m.group(1).splitlines()
                if any(
                    op in ln
                    for op in [
                        "shufflevector",
                        "lshr",
                        "trunc",
                        "bitcast",
                        "zext",
                        "sext",
                        "select",
                        "add ",
                        "llvm.masked.load",
                        "llvm.masked.store",
                    ]
                )
            ]
            o0_ir_snippets[fn_name] = interesting_lines

    asm_kernels = {
        fn_name: asm_funcs.get(fn_name, [])
        for fn_name in [
            "kernel_sse2_shuffle_u32x4",
            "kernel_avx2_bitmask_u16",
            "kernel_sse2_bitmask_bytes",
            "kernel_bitmask_nonpow2_10lanes",
            "kernel_avx2_select_bitmask_u8x16",
            "kernel_avx2_select_vec_u8x16",
            "kernel_avx2_cast_widen_add",
            "kernel_avx2_masked_load_store",
        ]
    }

    mcp838_msg = ""
    for ln in p_mcp838.stderr.splitlines():
        if "MCP#838" in ln or "Projecting into SIMD type" in ln:
            mcp838_msg = sanitize_text(ln.strip())
            break

    return {
        "oob_shuffle_compile_fail": {
            "compile_rc": p_oob.returncode,
            **first_error_info(p_oob.stderr),
        },
        "mcp838_simd_field_projection_ban": {
            "compile_rc": p_mcp838.returncode,
            "validator_diagnostic": mcp838_msg,
        },
        "repr_simd_nonpow2_padding_i16x10": {
            "array_i16x10_size_bytes": 20,
            "simd_i16x10_size_bytes": 32,
            "simd_i16x10_align_bytes": 32,
            "verified_at_runtime": (simd_run.returncode == 0),
        },
        "positive_suite_compile_rc": p_simd.returncode,
        "positive_suite_o0_ir_rc": p_simd_o0.returncode,
        "execution_rc": simd_run.returncode,
        "execution_stdout": simd_run.stdout.strip(),
        "rustc_codegen_llvm_o0_ir_instructions": o0_ir_snippets,
        "x86_64_o2_disassembly_by_kernel": asm_kernels,
        "post_opt_ll_masked_intrinsics_decls": sorted(
            set(re.findall(r"declare [^\n]*@llvm\.masked\.[^\n]+", ll_text))
        ),
    }


def probe_part4_sysroot_stdarch_and_simd_census(rustc_bin: str) -> dict[str, Any]:
    """Scan installed rustc sysroot library/{core,stdarch} for exact intrinsic and attribute counts."""
    sysroot = Path(
        subprocess.run(
            [rustc_bin, "--print", "sysroot"],
            capture_output=True,
            text=True,
            check=True,
        ).stdout.strip()
    )
    lib_root = sysroot / "lib" / "rustlib" / "src" / "rust" / "library"
    if not lib_root.exists():
        return {"available": False}

    simd_mod = lib_root / "core" / "src" / "intrinsics" / "simd" / "mod.rs"
    scalable_mod = lib_root / "core" / "src" / "intrinsics" / "simd" / "scalable.rs"
    simd_fns = re.findall(
        r"pub (?:const )?unsafe fn (simd_[a-z0-9_]+)",
        simd_mod.read_text(encoding="utf-8"),
    ) if simd_mod.exists() else []
    scalable_fns = re.findall(
        r"pub (?:const )?unsafe fn (simd_[a-z0-9_]+)",
        scalable_mod.read_text(encoding="utf-8"),
    ) if scalable_mod.exists() else []

    core_arch_src = lib_root / "stdarch" / "crates" / "core_arch" / "src"
    arch_stats: dict[str, dict[str, int]] = {}
    for arch_dir in ["x86", "x86_64", "aarch64", "wasm32", "riscv_shared", "riscv64"]:
        sub = core_arch_src / arch_dir
        if not sub.exists():
            continue
        rs_files = sorted(sub.rglob("*.rs"))
        tf_attrs = 0
        legacy_cg = 0
        uimm_asserts = 0
        simm_asserts = 0
        safe_pub_fns = 0
        unsafe_pub_fns = 0
        for f in rs_files:
            txt = f.read_text(encoding="utf-8", errors="replace")
            tf_attrs += len(re.findall(r"#\[target_feature\(", txt))
            legacy_cg += len(re.findall(r"#\[rustc_legacy_const_generics\(", txt))
            uimm_asserts += len(re.findall(r"static_assert_uimm_bits!\(", txt))
            simm_asserts += len(re.findall(r"static_assert_simm_bits!\(", txt))
            safe_pub_fns += len(re.findall(r"\bpub (?:const )?fn\s+_[a-zA-Z0-9_]+|\bpub (?:const )?fn\s+v[a-z0-9_]+", txt))
            unsafe_pub_fns += len(re.findall(r"\bpub (?:const )?unsafe fn\s+_[a-zA-Z0-9_]+|\bpub (?:const )?unsafe fn\s+v[a-z0-9_]+", txt))
        arch_stats[arch_dir] = {
            "rs_files": len(rs_files),
            "target_feature_attrs": tf_attrs,
            "rustc_legacy_const_generics_attrs": legacy_cg,
            "static_assert_uimm_bits_calls": uimm_asserts,
            "static_assert_simm_bits_calls": simm_asserts,
            "safe_pub_intrinsic_wrappers": safe_pub_fns,
            "unsafe_pub_intrinsic_wrappers": unsafe_pub_fns,
        }

    return {
        "available": True,
        "core_intrinsics_simd_count": len(simd_fns),
        "core_intrinsics_simd_names": simd_fns,
        "core_intrinsics_scalable_simd_count": len(scalable_fns),
        "core_intrinsics_scalable_simd_names": scalable_fns,
        "core_arch_by_subdir": arch_stats,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out",
        type=Path,
        default=None,
        help="Optional path to write JSON probe report",
    )
    args = parser.parse_args()

    rustc_bin = find_rustc()
    vv = subprocess.run(
        [rustc_bin, "--version", "--verbose"],
        capture_output=True,
        text=True,
        check=True,
    ).stdout.strip()
    objdump_bin = find_llvm_objdump(rustc_bin)
    host_cpu = detect_host_cpu()

    with tempfile.TemporaryDirectory() as raw_tmp:
        tmpdir = Path(raw_tmp)
        part1 = probe_part1_type_and_attr_matrix(rustc_bin, tmpdir)
        part2 = probe_part2_dispatch_inlining_and_sigill(rustc_bin, host_cpu, tmpdir)
        part3 = probe_part3_portable_simd_intrinsics(rustc_bin, tmpdir)
        part4 = probe_part4_sysroot_stdarch_and_simd_census(rustc_bin)

    report = {
        "toolchain": {
            "rustc_version_verbose": vv,
            "disassembler_available": bool(objdump_bin),
        },
        "host_cpu": {
            "arch": host_cpu["arch"],
            "model_name": host_cpu["model_name"],
            "feature_presence": host_cpu["feature_presence"],
        },
        "part1_target_feature_and_stdarch_matrix": part1,
        "part2_dynamic_dispatch_inlining_and_sigill": part2,
        "part3_portable_simd_intrinsics": part3,
        "part4_sysroot_stdarch_and_simd_census": part4,
    }

    # Verify core invariants programmatically
    assert part1["s01_avx2_calls_avx2_and_sse41_and_blend_safe"]["compile_rc"] == 0
    assert part1["s01_avx2_calls_avx2_and_sse41_and_blend_safe"]["run_rc"] == 0
    assert part1["s02_avx2_calls_avx512f_without_unsafe"]["compile_rc"] != 0
    assert part1["s03_baseline_calls_avx2_even_with_cli_target_feature"]["compile_rc"] != 0
    assert part1["s04_baseline_coerces_avx2_to_safe_fnptr"]["compile_rc"] != 0
    assert part1["s05_baseline_coerces_avx2_to_unsafe_fnptr"]["compile_rc"] == 0
    assert part1["s06_avx2_reifies_avx2_to_safe_fnptr_witness"]["compile_rc"] == 0
    assert part1["s06_avx2_reifies_avx2_to_safe_fnptr_witness"]["run_rc"] == 0
    assert part1["s07_avx2_fndef_implements_fn_trait_inside_avx2"]["compile_rc"] != 0
    assert part1["s08_target_feature_on_safe_trait_impl_method"]["compile_rc"] != 0
    assert part1["s10_legacy_const_generics_imm8_256_oob"]["compile_rc"] != 0
    assert part1["s11_legacy_const_generics_runtime_arg"]["compile_rc"] != 0
    assert part1["s12_aarch64_sve2_sve_fp16_neon_lattice"]["sve2_to_sve_to_neon_compile_rc"] == 0
    assert part1["s12_aarch64_sve2_sve_fp16_neon_lattice"]["sve_calling_sve2_without_unsafe_compile_rc"] != 0

    for opt_key in ("O2", "O3"):
        d = part2["guarded_dynamic_dispatch"][opt_key]
        assert d["compile_rc"] == 0 and d["run_rc"] == 0
        assert d["mir_inliner_observations"]["mir_inlined_equal_feature_stdarch_mm256_add_epi32"] is True
        assert d["mir_inliner_observations"]["mir_inlined_equal_feature_stdarch_mm256_extracti128"] is True
        assert d["mir_inliner_observations"]["mir_preserved_subset_avx_mm256_castsi256_si128_call"] is True
        assert d["mir_inliner_observations"]["mir_preserved_subset_sse2_mm_add_epi32_call"] is True
        assert d["mir_inliner_observations"]["mir_preserved_subset_sse41_helper_call"] is True
        assert d["x86_64_asm_summary"]["baseline_dispatch_avx2"]["ymm_insns_count"] == 0
        assert d["x86_64_asm_summary"]["baseline_dispatch_avx2"]["vex_or_evex_insns_count"] == 0
        assert d["x86_64_asm_summary"]["baseline_dispatch_avx512f"]["zmm_insns_count"] == 0
        assert d["x86_64_asm_summary"]["avx2_kernel_entry"]["ymm_insns_count"] > 0
        assert d["x86_64_asm_summary"]["avx512_kernel_entry"]["zmm_insns_count"] > 0

    assert part3["oob_shuffle_compile_fail"]["compile_rc"] != 0
    assert part3["positive_suite_compile_rc"] == 0
    assert part3["execution_rc"] == 0

    encoded = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.out is not None:
        args.out.write_text(encoded, encoding="utf-8")
        print(f"wrote {args.out} ({len(encoded)} bytes)")
    else:
        sys.stdout.write(encoded)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
