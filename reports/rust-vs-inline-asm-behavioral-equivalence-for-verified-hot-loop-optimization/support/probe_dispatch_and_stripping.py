#!/usr/bin/env python3
"""Empirical rustc probes for Rust-vs-inline-ASM pairing, dispatch, and stripping.

Tests across installed rustc toolchains (+nightly-2026-06-01, +1.99.1, +nightly):
  1. Runtime CPU feature dispatch (`is_x86_feature_detected!`, `is_aarch64_feature_detected!`,
     `AtomicPtr` lazy ifunc, and zero-sized `CpuToken` witnesses) and LLVM/MIR inline-barrier
     behavior of `#[target_feature]` vs raw `asm!`.
  2. Unprotected AVX2 mnemonics inside a non-`#[target_feature]` function across 4 cases:
     (a) `out("ymm0") _` (discarded explicit YMM clobber),
     (b) `out(ymm_reg) _` (discarded YMM register class),
     (c) `out("ymm0") y` with `y: __m256i` (typed YMM output),
     (d) raw AVX2 template string with GPR + `out("xmm0") _` and `options(pure, nomem, nostack)`
         (testing compile acceptance AND whether LLVM hoists/speculates across a runtime check!).
  3. Dead-code stripping vs `Runtime(PostCleanup)` MIR reachability for:
     (a) truly unreferenced private `fn`,
     (b) dead-`cfg!`-branch-referenced private `fn`,
     (c) unreferenced `pub fn`,
     (d) uninstantiated generic private `fn<const K: u64>`,
     across `rlib`, `cdylib`, `bin`, and `--emit=obj,asm` with `nm -C` and `objdump`.
  4. Multi-ISA crate (`x86_64` AVX2 `asm!` + `aarch64` NEON `asm!` + single Rust reference)
     compiled for both `x86_64-unknown-linux-gnu` and `aarch64-unknown-linux-gnu`.

Uses `tempfile.TemporaryDirectory()` exclusively for transient build artifacts.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import tempfile
from pathlib import Path

PATTERN1_RS = r"""
use core::arch::asm;
use core::sync::atomic::{AtomicPtr, Ordering};

#[inline(never)]
pub fn sum_u8_reference(slice: &[u8]) -> u64 {
    let mut acc: u64 = 0;
    for &b in slice {
        acc = acc.wrapping_add(b as u64);
    }
    acc
}

/// Safe AVX2 inline-ASM kernel isolated behind `#[target_feature(enable = "avx2")]`.
#[target_feature(enable = "avx2")]
unsafe fn sum_u8_avx2_asm(ptr: *const u8, len: usize) -> u64 {
    let mut acc: u64 = 0;
    let mut i: usize = 0;
    if len >= 32 {
        let chunks = len & !31usize;
        unsafe {
            asm!(
                "vpxor ymm0, ymm0, ymm0",
                "vpxor ymm1, ymm1, ymm1",
                "2:",
                "vmovdqu ymm2, [{ptr} + {i}]",
                "vpsadbw ymm2, ymm2, ymm1",
                "vpaddq ymm0, ymm0, ymm2",
                "add {i}, 32",
                "cmp {i}, {chunks}",
                "jb 2b",
                "vextracti128 xmm1, ymm0, 1",
                "vpaddq xmm0, xmm0, xmm1",
                "vpsrldq xmm1, xmm0, 8",
                "vpaddq xmm0, xmm0, xmm1",
                "vmovq {acc}, xmm0",
                "vzeroupper",
                ptr = in(reg) ptr,
                i = inout(reg) i,
                chunks = in(reg) chunks,
                acc = out(reg) acc,
                out("ymm0") _,
                out("ymm1") _,
                out("ymm2") _,
                options(readonly, nostack),
            );
        }
    }
    while i < len {
        acc = acc.wrapping_add(unsafe { *ptr.add(i) } as u64);
        i += 1;
    }
    acc
}

/// Pattern 1A: Direct `is_x86_feature_detected!("avx2")` dispatch.
#[unsafe(no_mangle)]
pub extern "C" fn dispatch_runtime_cpuid(ptr: *const u8, len: usize) -> u64 {
    let slice = unsafe { core::slice::from_raw_parts(ptr, len) };
    if std::is_x86_feature_detected!("avx2") {
        unsafe { sum_u8_avx2_asm(ptr, len) }
    } else {
        sum_u8_reference(slice)
    }
}

/// Pattern 1B: `memchr`-style `AtomicPtr` lazy function-pointer dispatch.
type SumFn = unsafe fn(*const u8, usize) -> u64;
static DISPATCH_FN: AtomicPtr<()> = AtomicPtr::new(detect_and_dispatch as *mut ());

unsafe fn ref_adapter(ptr: *const u8, len: usize) -> u64 {
    sum_u8_reference(unsafe { core::slice::from_raw_parts(ptr, len) })
}

unsafe fn detect_and_dispatch(ptr: *const u8, len: usize) -> u64 {
    let f: SumFn = if std::is_x86_feature_detected!("avx2") {
        sum_u8_avx2_asm
    } else {
        ref_adapter
    };
    DISPATCH_FN.store(f as *mut (), Ordering::Relaxed);
    unsafe { f(ptr, len) }
}

#[unsafe(no_mangle)]
pub extern "C" fn dispatch_atomic_ifunc(ptr: *const u8, len: usize) -> u64 {
    let p = DISPATCH_FN.load(Ordering::Relaxed);
    let f: SumFn = unsafe { core::mem::transmute(p) };
    unsafe { f(ptr, len) }
}

/// Pattern 1C: Zero-sized capability token dispatch (no branch in hot caller).
#[derive(Copy, Clone)]
pub struct Avx2Token(());
impl Avx2Token {
    #[inline]
    pub fn try_new() -> Option<Self> {
        if std::is_x86_feature_detected!("avx2") { Some(Self(())) } else { None }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn dispatch_with_token(_tok: Avx2Token, ptr: *const u8, len: usize) -> u64 {
    unsafe { sum_u8_avx2_asm(ptr, len) }
}
"""

UNPROT_CASES = {
    "a_discarded_explicit_ymm0": r"""
use core::arch::asm;
#[unsafe(no_mangle)]
pub unsafe extern "C" fn f(x: u64) -> u64 {
    let out: u64;
    unsafe {
        asm!("vpxor ymm0, ymm0, ymm0", "vmovq {out}, xmm0",
             out = out(reg) out, out("ymm0") _, options(nomem, nostack, pure));
    }
    out ^ x
}
""",
    "b_discarded_ymm_reg_class": r"""
use core::arch::asm;
#[unsafe(no_mangle)]
pub unsafe extern "C" fn f(x: u64) -> u64 {
    let out: u64;
    unsafe {
        asm!("vpxor {v}, {v}, {v}", "mov {out}, {x}",
             x = in(reg) x, out = lateout(reg) out, v = out(ymm_reg) _,
             options(nomem, nostack, pure));
    }
    out
}
""",
    "c_typed_m256i_ymm0": r"""
use core::arch::asm;
use core::arch::x86_64::__m256i;
#[unsafe(no_mangle)]
pub unsafe extern "C" fn f(x: u64) -> u64 {
    let _y: __m256i;
    unsafe {
        asm!("vpxor ymm0, ymm0, ymm0", out("ymm0") _y, options(nomem, nostack, pure));
    }
    x
}
""",
    "d_raw_avx2_string_with_gpr_only_and_hoist": r"""
use core::arch::asm;

/// Case D1: AVX2 mnemonic inside template string using ONLY GPR + `out("xmm0") _`
/// in a non-`#[target_feature]` function.
#[unsafe(no_mangle)]
pub extern "C" fn raw_avx2_in_sse2_fn(cond: bool, x: u64) -> u64 {
    if cond {
        let r: u64;
        unsafe {
            asm!(
                "vmovq xmm0, {x}",
                "vpaddq ymm0, ymm0, ymm0",
                "vmovq {r}, xmm0",
                "vzeroupper",
                x = in(reg) x,
                r = lateout(reg) r,
                out("xmm0") _,
                options(nomem, nostack, pure, preserves_flags),
            );
        }
        r
    } else {
        x.wrapping_add(1)
    }
}

/// Case D2: Loop-invariant `options(pure, nomem, nostack)` AVX2 asm inside a loop
/// guarded by runtime `has_avx2` WITHOUT a `#[target_feature]` inline barrier.
#[unsafe(no_mangle)]
pub extern "C" fn loop_licm_hoist_test(has_avx2: bool, n: usize, x: u64) -> u64 {
    let mut acc = 0u64;
    for i in 0..n {
        let term = if has_avx2 {
            let r: u64;
            unsafe {
                asm!(
                    "vmovq xmm0, {x}",
                    "vpaddq ymm0, ymm0, ymm0",
                    "vmovq {r}, xmm0",
                    "vzeroupper",
                    x = in(reg) x,
                    r = lateout(reg) r,
                    out("xmm0") _,
                    options(nomem, nostack, pure, preserves_flags),
                );
            }
            r
        } else {
            x.wrapping_mul(3)
        };
        acc = acc.wrapping_add(term).wrapping_add(i as u64);
    }
    acc
}

/// Case D3: Unconditional diamond select (`if cond { pure_avx2_asm(x) } else { x + 1 }`)
/// testing whether SimplifyCFG speculatively executes `pure` asm! into a `cmov`!
#[unsafe(no_mangle)]
pub extern "C" fn diamond_speculate_test(cond: bool, x: u64) -> u64 {
    let fast: u64;
    if cond {
        unsafe {
            asm!(
                "vmovq xmm0, {x}",
                "vpaddq ymm0, ymm0, ymm0",
                "vmovq {r}, xmm0",
                "vzeroupper",
                x = in(reg) x,
                r = lateout(reg) fast,
                out("xmm0") _,
                options(nomem, nostack, pure, preserves_flags),
            );
        }
        fast
    } else {
        x.wrapping_add(5)
    }
}
""",
    "e_inline_always_plus_target_feature": r"""
#[inline(always)]
#[target_feature(enable = "avx2")]
pub unsafe fn bad_inline_always_tf(x: u64) -> u64 { x + 1 }
""",
}

PATTERN2_STRIPPING_RS = r"""
use core::arch::asm;

/// (a) Truly unreferenced private reference twin (zero callers anywhere in crate).
#[allow(dead_code)]
fn truly_unreferenced_private_twin(x: u64, y: u64) -> u64 {
    x.wrapping_mul(3).wrapping_add(y ^ 0x55AA_55AA)
}

/// (b) Private reference twin referenced ONLY in a statically-false `cfg!` else-branch.
#[allow(dead_code)]
fn dead_branch_private_twin(x: u64, y: u64) -> u64 {
    x.wrapping_mul(3).wrapping_add(y ^ 0x55AA_55AA)
}

/// (c) Public uncalled reference twin.
pub fn public_reference_twin(x: u64, y: u64) -> u64 {
    x.wrapping_mul(3).wrapping_add(y ^ 0x55AA_55AA)
}

/// (d) Uninstantiated generic private reference twin.
#[allow(dead_code)]
fn generic_private_reference_twin<const K: u64>(x: u64) -> u64 {
    x.wrapping_mul(K).wrapping_add(1)
}

/// Fast-path asm implementation called by exported entry point.
#[unsafe(no_mangle)]
pub extern "C" fn fast_entry(x: u64, y: u64) -> u64 {
    let out: u64;
    unsafe {
        asm!(
            "lea {out}, [{x} + {x}*2]",
            "xor {y}, 0x55AA55AA",
            "add {out}, {y}",
            x = in(reg) x,
            y = inout(reg) y => _,
            out = lateout(reg) out,
            options(pure, nomem, nostack),
        );
    }
    out
}

#[inline(always)]
fn inline_wrapper_dispatch(x: u64, y: u64) -> u64 {
    if cfg!(target_arch = "x86_64") && cfg!(target_feature = "avx2") {
        fast_entry(x, y)
    } else {
        dead_branch_private_twin(x, y)
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn wrapped_entry(x: u64, y: u64) -> u64 {
    inline_wrapper_dispatch(x, y)
}

#[cfg(feature_main)]
fn main() {
    let args: Vec<String> = std::env::args().collect();
    let x = args.len() as u64;
    println!("{} {}", fast_entry(x, 7), wrapped_entry(x, 7));
}
"""

PATTERN3_MULTI_ISA_RS = r"""
#![no_std]
use core::arch::asm;

/// Single human-reviewed safe Rust reference specification shared across all ISAs.
#[allow(dead_code)]
pub fn xor_checksum_reference(buf: &[u8]) -> u8 {
    let mut acc = 0u8;
    for &b in buf {
        acc ^= b;
    }
    acc
}

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "avx2")]
unsafe fn xor_checksum_x86_64_avx2(ptr: *const u8, len: usize) -> u8 {
    let mut acc_u64: u64 = 0;
    let mut i: usize = 0;
    if len >= 32 {
        let chunks = len & !31usize;
        unsafe {
            asm!(
                "vpxor ymm0, ymm0, ymm0",
                "2:",
                "vpxor ymm0, ymm0, ymmword ptr [{ptr} + {i}]",
                "add {i}, 32",
                "cmp {i}, {chunks}",
                "jb 2b",
                "vextracti128 xmm1, ymm0, 1",
                "vpxor xmm0, xmm0, xmm1",
                "vpsrldq xmm1, xmm0, 8",
                "vpxor xmm0, xmm0, xmm1",
                "vmovq {acc}, xmm0",
                "vzeroupper",
                ptr = in(reg) ptr,
                i = inout(reg) i,
                chunks = in(reg) chunks,
                acc = out(reg) acc_u64,
                out("ymm0") _,
                out("ymm1") _,
                options(readonly, nostack),
            );
        }
    }
    let b = acc_u64.to_le_bytes();
    let mut acc = b[0] ^ b[1] ^ b[2] ^ b[3] ^ b[4] ^ b[5] ^ b[6] ^ b[7];
    while i < len {
        acc ^= unsafe { *ptr.add(i) };
        i += 1;
    }
    acc
}

#[cfg(target_arch = "aarch64")]
#[target_feature(enable = "neon")]
unsafe fn xor_checksum_aarch64_neon(ptr: *const u8, len: usize) -> u8 {
    let mut acc_u64: u64 = 0;
    let mut i: usize = 0;
    if len >= 16 {
        let chunks = len & !15usize;
        unsafe {
            asm!(
                "eor v0.16b, v0.16b, v0.16b",
                "2:",
                "ldr q1, [{ptr}, {i}]",
                "eor v0.16b, v0.16b, v1.16b",
                "add {i}, {i}, #16",
                "cmp {i}, {chunks}",
                "b.lo 2b",
                "ext v1.16b, v0.16b, v0.16b, #8",
                "eor v0.8b, v0.8b, v1.8b",
                "fmov {acc}, d0",
                ptr = in(reg) ptr,
                i = inout(reg) i,
                chunks = in(reg) chunks,
                acc = out(reg) acc_u64,
                out("v0") _,
                out("v1") _,
                options(readonly, nostack),
            );
        }
    }
    let b = acc_u64.to_le_bytes();
    let mut acc = b[0] ^ b[1] ^ b[2] ^ b[3] ^ b[4] ^ b[5] ^ b[6] ^ b[7];
    while i < len {
        acc ^= unsafe { *ptr.add(i) };
        i += 1;
    }
    acc
}

#[unsafe(no_mangle)]
pub extern "C" fn xor_checksum_dispatch(ptr: *const u8, len: usize) -> u8 {
    let slice = unsafe { core::slice::from_raw_parts(ptr, len) };
    #[cfg(all(target_arch = "x86_64", target_feature = "avx2"))]
    {
        return unsafe { xor_checksum_x86_64_avx2(ptr, len) };
    }
    #[cfg(all(target_arch = "aarch64", target_feature = "neon"))]
    {
        return unsafe { xor_checksum_aarch64_neon(ptr, len) };
    }
    #[allow(unreachable_code)]
    xor_checksum_reference(slice)
}
"""

AARCH64_DETECT_RS = r"""
#[unsafe(no_mangle)]
pub extern "C" fn detect_aarch64_sve2_and_dotprod() -> u32 {
    let mut bits = 0u32;
    if std::arch::is_aarch64_feature_detected!("dotprod") {
        bits |= 1;
    }
    if std::arch::is_aarch64_feature_detected!("sve2") {
        bits |= 2;
    }
    bits
}
"""


def run(cmd: list[str], env: dict[str, str] | None = None) -> subprocess.CompletedProcess[str]:
    merged_env = os.environ.copy()
    if env:
        merged_env.update(env)
    return subprocess.run(cmd, capture_output=True, text=True, env=merged_env)


def get_rustc_info(tc: str) -> dict[str, str]:
    p = run(["rustc", tc, "--version", "--verbose"])
    info = {"toolchain": tc, "returncode": str(p.returncode)}
    for line in p.stdout.splitlines():
        if ":" in line:
            k, v = line.split(":", 1)
            info[k.strip()] = v.strip()
        elif line.startswith("rustc "):
            info["version_line"] = line.strip()
    return info


def extract_ll_fn(ll: str, name: str) -> str:
    m = re.search(rf"define[^\n]*@{re.escape(name)}\b.*?\n\}}", ll, re.S)
    return m.group(0) if m else ""


def extract_asm_fn(asm: str, name: str) -> str:
    m = re.search(rf"(?m)^{re.escape(name)}:\n.*?(?=\n\t\.size\s+{re.escape(name)},)", asm, re.S)
    return m.group(0) if m else ""


def main() -> int:
    results: dict[str, object] = {"toolchains": {}, "probes": {}}
    toolchains = ["+nightly-2026-06-01", "+1.99.1", "+nightly"]

    for tc in toolchains:
        results["toolchains"][tc] = get_rustc_info(tc)

    with tempfile.TemporaryDirectory(prefix="anneal_asm_probe_") as td:
        tmp = Path(td)
        p1_rs = tmp / "pattern1.rs"
        p1_rs.write_text(PATTERN1_RS)
        p2_rs = tmp / "pattern2.rs"
        p2_rs.write_text(PATTERN2_STRIPPING_RS)
        p3_rs = tmp / "pattern3.rs"
        p3_rs.write_text(PATTERN3_MULTI_ISA_RS)
        a64_det_rs = tmp / "a64_det.rs"
        a64_det_rs.write_text(AARCH64_DETECT_RS)

        # --- PROBE 1: Pattern 1 Runtime CPUID Dispatch & Feature Detection ---
        p1_res = {}
        for tc in toolchains:
            out_dir = tmp / f"p1_{tc.lstrip('+')}"
            out_dir.mkdir()
            r_base = run([
                "rustc", tc, "--edition=2024", "--crate-type=lib", "-O",
                "--crate-name", "p1_base",
                "--emit=llvm-ir,asm", str(p1_rs), "--out-dir", str(out_dir),
            ])
            r_avx2 = run([
                "rustc", tc, "--edition=2024", "--crate-type=lib", "-O",
                "--crate-name", "p1_avx2",
                "-C", "target-feature=+avx2",
                "--emit=llvm-ir,asm", str(p1_rs), "--out-dir", str(out_dir),
            ])
            ll_base = (out_dir / "p1_base.ll").read_text() if (out_dir / "p1_base.ll").exists() else ""
            s_base = (out_dir / "p1_base.s").read_text() if (out_dir / "p1_base.s").exists() else ""
            ll_avx2 = (out_dir / "p1_avx2.ll").read_text() if (out_dir / "p1_avx2.ll").exists() else ""
            s_avx2 = (out_dir / "p1_avx2.s").read_text() if (out_dir / "p1_avx2.s").exists() else ""

            base_fn_ll = extract_ll_fn(ll_base, "dispatch_runtime_cpuid")
            avx2_fn_ll = extract_ll_fn(ll_avx2, "dispatch_runtime_cpuid")
            ifunc_base_ll = extract_ll_fn(ll_base, "dispatch_atomic_ifunc")
            tok_base_ll = extract_ll_fn(ll_base, "dispatch_with_token")
            tok_avx2_ll = extract_ll_fn(ll_avx2, "dispatch_with_token")

            p1_res[tc] = {
                "base_rc": r_base.returncode,
                "base_stderr": r_base.stderr.strip()[:300],
                "avx2_rc": r_avx2.returncode,
                "base_dispatch_uses_atomic_cache_or_detect": (
                    "load atomic" in base_fn_ll or "is_x86_feature_detected" in base_fn_ll or "detect" in base_fn_ll
                ),
                "base_dispatch_inlines_avx2_asm": ("vpsadbw" in base_fn_ll),
                "base_dispatch_calls_outlined_avx2_fn": ("sum_u8_avx2_asm" in base_fn_ll),
                "base_dispatch_calls_ref_fn": ("sum_u8_reference" in base_fn_ll),
                "avx2_dispatch_eliminates_detect": ("load atomic" not in avx2_fn_ll and "detect" not in avx2_fn_ll),
                "avx2_dispatch_inlines_avx2_asm": ("vpsadbw" in avx2_fn_ll),
                "avx2_dispatch_eliminates_ref_call": ("sum_u8_reference" not in avx2_fn_ll),
                "ifunc_base_asm": extract_asm_fn(s_base, "dispatch_atomic_ifunc"),
                "token_base_calls_outlined_avx2": ("sum_u8_avx2_asm" in tok_base_ll),
                "token_base_zero_branch": ("br i1" not in tok_base_ll),
                "token_base_asm": extract_asm_fn(s_base, "dispatch_with_token"),
                "token_avx2_inlines_avx2_asm": ("vpsadbw" in tok_avx2_ll),
                "base_dispatch_asm": extract_asm_fn(s_base, "dispatch_runtime_cpuid"),
                "avx2_dispatch_asm": extract_asm_fn(s_avx2, "dispatch_runtime_cpuid"),
            }
        results["probes"]["pattern1_dispatch"] = p1_res

        # --- PROBE 1B: Unprotected AVX2 inside non-`#[target_feature]` function ---
        unprot_res = {}
        for tc in toolchains:
            out_dir = tmp / f"unprot_{tc.lstrip('+')}"
            out_dir.mkdir()
            tc_cases = {}
            for cname, src in UNPROT_CASES.items():
                f_rs = out_dir / f"{cname}.rs"
                f_rs.write_text(src)
                r = run([
                    "rustc", tc, "--edition=2024", "--crate-type=lib", "-O",
                    "--crate-name", cname,
                    "--emit=llvm-ir,asm", str(f_rs), "--out-dir", str(out_dir),
                ])
                ll_txt = (out_dir / f"{cname}.ll").read_text() if (out_dir / f"{cname}.ll").exists() else ""
                s_txt = (out_dir / f"{cname}.s").read_text() if (out_dir / f"{cname}.s").exists() else ""
                entry: dict[str, object] = {
                    "rc": r.returncode,
                    "stderr": r.stderr.strip()[:500],
                    "emits_avx_ymm": ("ymm" in s_txt),
                    "asm_excerpt": s_txt[:1500] if cname == "a_discarded_explicit_ymm0" else "",
                    "ll_excerpt": ll_txt[:1500] if cname == "a_discarded_explicit_ymm0" else "",
                }
                if cname == "d_raw_avx2_string_with_gpr_only_and_hoist":
                    entry["raw_avx2_asm"] = extract_asm_fn(s_txt, "raw_avx2_in_sse2_fn")
                    entry["loop_licm_hoist_asm"] = extract_asm_fn(s_txt, "loop_licm_hoist_test")
                    entry["loop_licm_hoist_ll"] = extract_ll_fn(ll_txt, "loop_licm_hoist_test")
                    entry["diamond_speculate_asm"] = extract_asm_fn(s_txt, "diamond_speculate_test")
                    entry["diamond_speculate_ll"] = extract_ll_fn(ll_txt, "diamond_speculate_test")
                tc_cases[cname] = entry
            unprot_res[tc] = tc_cases
        results["probes"]["unprotected_asm_without_target_feature"] = unprot_res

        # --- PROBE 2: Dead-code stripping vs `Runtime(PostCleanup)` MIR dump ---
        p2_res = {}
        for tc in toolchains:
            out_dir = tmp / f"p2_{tc.lstrip('+')}"
            out_dir.mkdir()
            mir_dir_lib = out_dir / "mir_lib"
            mir_dir_bin = out_dir / "mir_bin"
            mir_dir_lib.mkdir()
            mir_dir_bin.mkdir()
            env_boot = {"RUSTC_BOOTSTRAP": "1"} if tc == "+1.99.1" else None

            r_rlib = run([
                "rustc", tc, "--edition=2024", "--crate-type=rlib", "-O",
                "-C", "target-feature=+avx2",
                "-Z", "dump-mir=all",
                "-Z", "dump-mir-dir=" + str(mir_dir_lib),
                str(p2_rs), "-o", str(out_dir / "libp2.rlib"),
            ], env=env_boot)
            r_cdylib = run([
                "rustc", tc, "--edition=2024", "--crate-type=cdylib", "-O",
                "-C", "target-feature=+avx2",
                str(p2_rs), "-o", str(out_dir / "libp2.so"),
            ])
            r_obj = run([
                "rustc", tc, "--edition=2024", "--crate-type=lib", "-O",
                "-C", "target-feature=+avx2",
                "--emit=obj,asm", str(p2_rs), "--out-dir", str(out_dir),
            ])
            r_bin = run([
                "rustc", tc, "--edition=2024", "--crate-type=bin", "-O",
                "--cfg", "feature_main",
                "-C", "target-feature=+avx2",
                "-Z", "dump-mir=all",
                "-Z", "dump-mir-dir=" + str(mir_dir_bin),
                str(p2_rs), "-o", str(out_dir / "p2_bin"),
            ], env=env_boot)

            nm_so = run(["nm", "-C", str(out_dir / "libp2.so")]).stdout if (out_dir / "libp2.so").exists() else ""
            nm_o = run(["nm", "-C", str(out_dir / "pattern2.o")]).stdout if (out_dir / "pattern2.o").exists() else ""
            nm_bin = run(["nm", "-C", str(out_dir / "p2_bin")]).stdout if (out_dir / "p2_bin").exists() else ""
            s_obj = (out_dir / "pattern2.s").read_text() if (out_dir / "pattern2.s").exists() else ""

            def mir_phases(d: Path, fn_sub: str) -> list[str]:
                return sorted([
                    p.name for p in d.glob(f"*{fn_sub}*")
                    if "runtime-post-cleanup" in p.name or "runtime-optimized" in p.name
                ])

            p2_res[tc] = {
                "rlib_rc": r_rlib.returncode,
                "cdylib_rc": r_cdylib.returncode,
                "bin_rc": r_bin.returncode,
                "rlib_mir": {
                    "truly_unreferenced_private_twin": mir_phases(mir_dir_lib, "truly_unreferenced_private_twin"),
                    "dead_branch_private_twin": mir_phases(mir_dir_lib, "dead_branch_private_twin"),
                    "public_reference_twin": mir_phases(mir_dir_lib, "public_reference_twin"),
                    "generic_private_reference_twin": mir_phases(mir_dir_lib, "generic_private_reference_twin"),
                    "fast_entry": mir_phases(mir_dir_lib, "fast_entry"),
                },
                "bin_mir": {
                    "truly_unreferenced_private_twin": mir_phases(mir_dir_bin, "truly_unreferenced_private_twin"),
                    "dead_branch_private_twin": mir_phases(mir_dir_bin, "dead_branch_private_twin"),
                    "public_reference_twin": mir_phases(mir_dir_bin, "public_reference_twin"),
                    "generic_private_reference_twin": mir_phases(mir_dir_bin, "generic_private_reference_twin"),
                    "fast_entry": mir_phases(mir_dir_bin, "fast_entry"),
                },
                "symbols": {
                    "so_defined": [l for l in nm_so.splitlines() if "pattern2" in l or "entry" in l or "twin" in l],
                    "o_defined": [l for l in nm_o.splitlines() if "pattern2" in l or "entry" in l or "twin" in l],
                    "bin_defined": [l for l in nm_bin.splitlines() if "pattern2" in l or "entry" in l or "twin" in l],
                },
                "wrapped_entry_asm": extract_asm_fn(s_obj, "wrapped_entry"),
            }
        results["probes"]["pattern2_stripping_and_mir"] = p2_res

        # --- PROBE 2B: Exact cdylib `.text`/total byte-size parity with vs without unreferenced private twin ---
        sz_dir = tmp / "size_cmp"
        sz_dir.mkdir()
        no_ref_src = (
            'use core::arch::asm;\n'
            '#[unsafe(no_mangle)]\n'
            'pub extern "C" fn fast_only(x: u64) -> u64 {\n'
            '    let r: u64;\n'
            '    unsafe { asm!("lea {r}, [{x} + {x}*2 + 7]", x = in(reg) x, r = lateout(reg) r, options(pure, nomem, nostack)); }\n'
            '    r\n'
            '}\n'
        )
        with_ref_src = no_ref_src + (
            '#[allow(dead_code)]\n'
            '#[inline(never)]\n'
            'fn private_ref_large(xs: &[u64]) -> u64 {\n'
            '    let mut a = 0u64;\n'
            '    for &x in xs { a = a.wrapping_mul(31).wrapping_add(x); }\n'
            '    a\n'
            '}\n'
        )
        sz_out = {}
        for label, src in [("no_ref", no_ref_src), ("with_private_ref", with_ref_src)]:
            f = sz_dir / f"{label}.rs"
            f.write_text(src)
            so = sz_dir / f"lib{label}.so"
            rlib = sz_dir / f"lib{label}.rlib"
            run(["rustc", "+1.99.1", "--edition=2024", "--crate-type=cdylib", "-O", str(f), "-o", str(so)])
            run(["rustc", "+1.99.1", "--edition=2024", "--crate-type=rlib", "-O", str(f), "-o", str(rlib)])
            sz_lines = run(["size", str(so)]).stdout.strip().splitlines()
            cols = sz_lines[-1].split() if len(sz_lines) >= 2 else []
            nm_rlib = run(["nm", "-C", str(rlib)]).stdout
            sz_out[label] = {
                "cdylib_text_bytes": int(cols[0]) if cols else -1,
                "cdylib_total_dec_bytes": int(cols[3]) if len(cols) > 3 else -1,
                "rlib_has_private_ref_sym": ("private_ref_large" in nm_rlib),
            }
        sz_out["exact_zero_byte_overhead"] = (
            sz_out["no_ref"]["cdylib_text_bytes"] == sz_out["with_private_ref"]["cdylib_text_bytes"]
            and sz_out["no_ref"]["cdylib_total_dec_bytes"] == sz_out["with_private_ref"]["cdylib_total_dec_bytes"]
            and not sz_out["with_private_ref"]["rlib_has_private_ref_sym"]
        )
        results["probes"]["pattern2_size_comparison"] = sz_out

        # --- PROBE 2C: +nightly `#[inline(always)]` + `#[target_feature]` caller inline boundary ---
        ni_dir = tmp / "nightly_inline_tf"
        ni_dir.mkdir()
        ni_rs = ni_dir / "tf_inline.rs"
        ni_rs.write_text(
            'use core::arch::asm;\n'
            '#[inline(always)]\n'
            '#[target_feature(enable = "avx2")]\n'
            'unsafe fn avx2_leaf(x: u64) -> u64 {\n'
            '    let r: u64;\n'
            '    unsafe { asm!("vmovq xmm0, {x}", "vpaddq ymm0, ymm0, ymm0", "vmovq {r}, xmm0", "vzeroupper",\n'
            '        x = in(reg) x, r = lateout(reg) r, out("ymm0") _, options(pure, nomem, nostack)); }\n'
            '    r\n'
            '}\n'
            '#[unsafe(no_mangle)]\n'
            'pub extern "C" fn caller_sse2(cond: bool, x: u64) -> u64 {\n'
            '    if cond { unsafe { avx2_leaf(x) } } else { x + 1 }\n'
            '}\n'
            '#[unsafe(no_mangle)]\n'
            '#[target_feature(enable = "avx2")]\n'
            'pub unsafe extern "C" fn caller_avx2(x: u64) -> u64 { unsafe { avx2_leaf(x) } }\n'
        )
        r_ni = run([
            "rustc", "+nightly", "--edition=2024", "--crate-type=lib", "-O",
            "--emit=asm", str(ni_rs), "--out-dir", str(ni_dir),
        ])
        s_ni = (ni_dir / "tf_inline.s").read_text() if (ni_dir / "tf_inline.s").exists() else ""
        sse2_asm = extract_asm_fn(s_ni, "caller_sse2")
        avx2_asm = extract_asm_fn(s_ni, "caller_avx2")
        results["probes"]["nightly_inline_always_target_feature"] = {
            "rc": r_ni.returncode,
            "sse2_caller_inlines_avx2": ("vpaddq" in sse2_asm),
            "sse2_caller_jumps_to_leaf": ("avx2_leaf" in sse2_asm),
            "avx2_caller_inlines_avx2": ("vpaddq" in avx2_asm),
        }

        # --- PROBE 3: Multi-ISA Compilation (x86_64 + aarch64 on +1.99.1) + AArch64 detect ---
        p3_dir = tmp / "p3"
        p3_dir.mkdir()
        r_x86 = run([
            "rustc", "+1.99.1", "--edition=2024", "--crate-type=lib", "-O",
            "--crate-name", "p3_x86",
            "--target=x86_64-unknown-linux-gnu", "-C", "target-feature=+avx2",
            "--emit=asm", str(p3_rs), "--out-dir", str(p3_dir),
        ])
        r_a64 = run([
            "rustc", "+1.99.1", "--edition=2024", "--crate-type=lib", "-O",
            "--crate-name", "p3_a64",
            "--target=aarch64-unknown-linux-gnu",
            "--emit=asm", str(p3_rs), "--out-dir", str(p3_dir),
        ])
        r_a64_det = run([
            "rustc", "+1.99.1", "--edition=2024", "--crate-type=lib", "-O",
            "--crate-name", "a64_det",
            "--target=aarch64-unknown-linux-gnu",
            "--emit=llvm-ir,asm", str(a64_det_rs), "--out-dir", str(p3_dir),
        ])
        s_x86 = (p3_dir / "p3_x86.s").read_text() if (p3_dir / "p3_x86.s").exists() else ""
        s_a64 = (p3_dir / "p3_a64.s").read_text() if (p3_dir / "p3_a64.s").exists() else ""
        ll_a64_det = (p3_dir / "a64_det.ll").read_text() if (p3_dir / "a64_det.ll").exists() else ""
        s_a64_det = (p3_dir / "a64_det.s").read_text() if (p3_dir / "a64_det.s").exists() else ""
        results["probes"]["pattern3_multi_isa_and_aarch64_detect"] = {
            "x86_avx2_rc": r_x86.returncode,
            "x86_avx2_stderr": r_x86.stderr.strip()[:300],
            "x86_avx2_has_vpxor_ymm": ("vpxor" in s_x86 and "ymm0" in s_x86),
            "x86_avx2_has_vzeroupper": ("vzeroupper" in s_x86),
            "x86_dispatch_asm": extract_asm_fn(s_x86, "xor_checksum_dispatch"),
            "aarch64_neon_rc": r_a64.returncode,
            "aarch64_neon_stderr": r_a64.stderr.strip()[:300],
            "aarch64_neon_has_eor_16b": ("eor" in s_a64 and "v0.16b" in s_a64),
            "aarch64_dispatch_asm": extract_asm_fn(s_a64, "xor_checksum_dispatch"),
            "aarch64_detect_rc": r_a64_det.returncode,
            "aarch64_detect_asm": extract_asm_fn(s_a64_det, "detect_aarch64_sve2_and_dotprod"),
            "aarch64_detect_ll": extract_ll_fn(ll_a64_det, "detect_aarch64_sve2_and_dotprod"),
        }

    print(json.dumps(results, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
