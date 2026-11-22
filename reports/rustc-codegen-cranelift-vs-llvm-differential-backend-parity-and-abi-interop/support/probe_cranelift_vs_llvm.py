#!/usr/bin/env python3
"""Reproducible differential probe: rustc_codegen_cranelift vs. rustc_codegen_llvm.

Exercises:
  Part A: 2x2 cross-backend ABI interoperability (BigSret, u128/Mixed, &str +
          Option<NonZeroU64>, dyn Trait vtable dispatch, #[track_caller]) and
          asymmetric panic unwinding / Drop cleanup / catch_unwind parity, plus
          ELF .eh_frame and .gcc_except_table section inspection.
  Part B: 11-case feature-gate, inline-asm lowering (with objdump + nm symbol
          audit), ICE boundary, and -Z sanitizer=address fail-open matrix.
  Part C: Optional full-crate zerocopy rlib compilation benchmark and a
          self-contained compute-intensive microbenchmark across -O0 / -O2.

Usage:
  python3 support/probe_cranelift_vs_llvm.py --output results.json
  python3 support/probe_cranelift_vs_llvm.py --zerocopy-dir /path/to/zerocopy --output results.json
"""

from __future__ import annotations

import argparse
import datetime
import json
import os
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any


ABI_LIB_RS = r"""#![crate_type = "rlib"]
use core::num::NonZeroU64;
use core::sync::atomic::{AtomicUsize, Ordering};

#[repr(C)]
#[derive(Copy, Clone, Debug)]
pub struct BigSret {
    pub a: u64,
    pub b: u64,
    pub c: u64,
    pub d: u64,
    pub e: u64,
    pub f: u64,
}

#[inline(never)]
pub fn make_sret(base: u64) -> BigSret {
    BigSret { a: base, b: base + 2, c: base + 4, d: base + 6, e: base + 8, f: base + 10 }
}

#[inline(never)]
pub fn add_mixed(x: u128, tag: u8) -> u128 {
    x.wrapping_add(u128::from(tag))
}

#[inline(never)]
pub fn str_and_niche(s: &str, opt: Option<NonZeroU64>) -> u64 {
    (s.len() as u64) * 100 + opt.map_or(0, |n| n.get())
}

pub trait Scorer {
    fn score(&self, x: u64) -> u64;
}

#[inline(never)]
pub fn call_dyn(obj: &dyn Scorer, x: u64) -> u64 {
    obj.score(x)
}

#[track_caller]
#[inline(never)]
pub fn caller_line() -> u32 {
    core::panic::Location::caller().line()
}

struct DropGuard<'a>(&'a AtomicUsize);
impl Drop for DropGuard<'_> {
    fn drop(&mut self) {
        self.0.fetch_add(1, Ordering::SeqCst);
    }
}

#[inline(never)]
pub fn panic_with_guard(tag: &str, lib_drops: &AtomicUsize) {
    let _g = DropGuard(lib_drops);
    panic!("boom: {}", tag);
}
"""

ABI_BIN_RS = r"""extern crate abi_lib;
use core::num::NonZeroU64;

struct LocalScorer(u64);
impl abi_lib::Scorer for LocalScorer {
    fn score(&self, x: u64) -> u64 { self.0 * 100 + x }
}

fn main() {
    let s = abi_lib::make_sret(5);
    let line = abi_lib::caller_line();
    let sret_sum = s.a + s.b + s.c + s.d + s.e + s.f;
    let mixed = abi_lib::add_mixed(0x3_0000_0000_0000_0000u128, 10);
    let str_val = abi_lib::str_and_niche("hello", NonZeroU64::new(42));
    let scorer = LocalScorer(90);
    let dyn_val = abi_lib::call_dyn(&scorer, 77);
    println!(
        "SRET={} MIXED={:x} STR={} DYN={} LINE={}",
        sret_sum, mixed, str_val, dyn_val, line
    );
}
"""

UNWIND_BIN_RS = r"""extern crate abi_lib;
use core::sync::atomic::{AtomicUsize, Ordering};

struct BinGuard<'a>(&'a AtomicUsize);
impl Drop for BinGuard<'_> {
    fn drop(&mut self) {
        self.0.fetch_add(1, Ordering::SeqCst);
    }
}

fn main() {
    let bin_drops = AtomicUsize::new(0);
    let lib_drops = AtomicUsize::new(0);
    let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _bg = BinGuard(&bin_drops);
        abi_lib::panic_with_guard("cross_backend", &lib_drops);
    }));
    println!(
        "CAUGHT={} BIN_DROPS={} LIB_DROPS={}",
        res.is_err(),
        bin_drops.load(Ordering::SeqCst),
        lib_drops.load(Ordering::SeqCst)
    );
}
"""

PART_B_CASES: dict[str, dict[str, Any]] = {
    "inline_asm_basic": {
        "flags": ["-C", "opt-level=2"],
        "run": True,
        "disasm_sym": "add_asm",
        "code": r"""use core::arch::asm;

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn add_asm(mut a: u64, b: u64) -> u64 {
    unsafe {
        asm!(
            "add {a}, {b}",
            a = inout(reg) a,
            b = in(reg) b,
            options(pure, nomem, nostack),
        );
    }
    a
}

fn main() {
    let v = add_asm(core::hint::black_box(19), core::hint::black_box(23));
    println!("ASM={}", v);
}
""",
    },
    "inline_asm_sym": {
        "flags": [],
        "run": True,
        "code": r"""use core::arch::asm;

#[unsafe(no_mangle)]
extern "C" fn target_fn() -> u64 { 99 }

fn main() {
    let out: u64;
    unsafe { asm!("call {f}", f = sym target_fn, out("rax") out, clobber_abi("C")); }
    println!("ASM_SYM={}", out);
}
""",
    },
    "asm_goto_label": {
        "flags": [],
        "run": True,
        "code": r"""use core::arch::asm;

fn main() {
    let mut hit = 0u32;
    unsafe { asm!("jmp {}", label { hit = 7; }); }
    println!("ASM_GOTO={}", hit);
}
""",
    },
    "explicit_tail_calls_become": {
        "flags": [],
        "run": True,
        "code": r"""#![allow(incomplete_features)]
#![feature(explicit_tail_calls)]

fn countdown(n: u32, acc: u64) -> u64 {
    if n == 0 { acc } else { become countdown(n - 1, acc + n as u64) }
}

fn main() {
    println!("TAIL={}", countdown(100, 0));
}
""",
    },
    "c_variadic_def": {
        "flags": [],
        "run": True,
        "code": r"""#![feature(c_variadic)]
unsafe extern "C" fn sum2(_n: u32, mut ap: ...) -> u32 {
    unsafe { ap.next_arg::<u32>() + ap.next_arg::<u32>() }
}

fn main() {
    let v = unsafe { sum2(2, 19u32, 23u32) };
    println!("VA={}", v);
}
""",
    },
    "atomic_u128_intrinsic": {
        "flags": ["-C", "target-feature=+cmpxchg16b"],
        "run": True,
        "code": r"""#![allow(internal_features)]
#![feature(core_intrinsics)]

fn main() {
    let mut x: u128 = 100;
    let prev = unsafe {
        core::intrinsics::atomic_xadd::<u128, u128, { core::intrinsics::AtomicOrdering::SeqCst }>(
            &mut x as *mut u128,
            23,
        )
    };
    println!("A128={} NOW={}", prev, x);
}
""",
    },
    "f16_f128_arith": {
        "flags": [],
        "run": True,
        "code": r"""#![feature(f16, f128)]

fn main() {
    let a: f16 = core::hint::black_box(1.5_f16) + core::hint::black_box(2.25_f16);
    let b: f128 = core::hint::black_box(6.0_f128) * core::hint::black_box(3.5_f128);
    println!("F16={} F128={}", a as f32, b as f64);
}
""",
    },
    "portable_simd_and_sse2": {
        "flags": [],
        "run": True,
        "code": r"""#![feature(portable_simd)]
use core::simd::Simd;

fn main() {
    let a = Simd::<u32, 4>::from_array([1, 2, 3, 4]);
    let b = Simd::<u32, 4>::from_array([10, 20, 30, 40]);
    let c = (a + b).to_array();
    #[cfg(target_arch = "x86_64")]
    let sse = unsafe {
        use core::arch::x86_64::{_mm_add_epi32, _mm_set_epi32, _mm_storeu_si128};
        let v1 = _mm_set_epi32(7, 5, 3, 1);
        let v2 = _mm_set_epi32(5, 5, 5, 5);
        let sum = _mm_add_epi32(v1, v2);
        let mut out = [0i32; 4];
        _mm_storeu_si128(out.as_mut_ptr().cast(), sum);
        out
    };
    println!("SIMD={:?} SSE2={:?}", c, sse);
}
""",
    },
    "lto_thin_flag": {
        "flags": ["-C", "opt-level=2", "-C", "lto=thin"],
        "run": False,
        "code": "fn main() {}\n",
    },
    "instrument_coverage_flag": {
        "flags": ["-C", "instrument-coverage"],
        "run": False,
        "code": "fn main() {}\n",
    },
    "sanitizer_address_heap_oob": {
        "flags": ["-Z", "sanitizer=address"],
        "run": True,
        "code": r"""#[inline(never)]
unsafe fn read_oob(p: *const u8) -> u8 {
    unsafe { core::ptr::read_volatile(p.add(32)) }
}

fn main() {
    let buf = Box::new([0u8; 32]);
    let ptr = core::hint::black_box(buf.as_ptr());
    let byte = unsafe { read_oob(ptr) };
    println!("ASAN_SURVIVED_OOB={}", byte);
}
""",
    },
}

COMPUTE_MICROBENCH_RS = r"""#[inline(never)]
fn run_workload(iters: u64) -> u64 {
    let mut state: [u64; 16] = [
        0x243f_6a88_85a3_08d3, 0x1319_8a2e_0370_7344,
        0xa409_3822_299f_31d0, 0x082e_fa98_ec4e_6c89,
        0x4528_21e6_38d0_1377, 0xbe54_66cf_34e9_0c6c,
        0xc0ac_29b7_c97c_50dd, 0x3f84_d5b5_b547_0917,
        0x9216_d5d9_8979_fb1b, 0xd131_0ba6_98df_b5ac,
        0x2ffd_72db_d01a_dfb7, 0xb8e1_afed_6a26_7e96,
        0xba7c_9045_f12c_7f99, 0x24a1_9947_b391_6cf7,
        0x0801_f2e2_858e_fc16, 0x6369_20d8_7157_4e69,
    ];
    for i in 0..iters {
        let idx = (i & 15) as usize;
        let next = (idx + 1) & 15;
        let prev = (idx + 15) & 15;
        let x = state[idx]
            .wrapping_mul(0x9e37_79b9_7f4a_7c15)
            .wrapping_add(state[prev].rotate_left(17))
            ^ state[next].rotate_right(13);
        state[idx] = x.wrapping_add(i);
    }
    let mut acc = 0xcbf2_9ce4_8422_2325u64;
    for v in state {
        acc ^= v;
        acc = acc.wrapping_mul(0x0000_0100_0000_01b3);
    }
    acc
}

fn main() {
    let checksum = run_workload(core::hint::black_box(40_000_000));
    println!("{:016x}", checksum);
}
"""


def scrub_text(text: str, tmpdir: str) -> str:
    """Remove ephemeral temp paths, home directory prefixes, and PIDs from recorded outputs."""
    out = text.replace(tmpdir, "<TMPDIR>")
    out = re.sub(r"==\d+==", "==<PID>==", out)
    out = re.sub(r"thread '([^']+)' \(\d+\)", r"thread '\1' (<PID>)", out)
    home_dir = str(Path.home())
    if home_dir:
        out = out.replace(home_dir, "<HOME>")
    return out


def run_cmd(cmd: list[str], cwd: Path | None = None, timeout: int = 180) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=timeout,
    )


def backend_flags(backend: str) -> list[str]:
    if backend == "llvm":
        return []
    if backend == "cranelift":
        return ["-Z", "codegen-backend=cranelift"]
    raise ValueError(f"unknown backend: {backend}")


def check_cranelift_available(rustc: str, tmpdir: Path) -> tuple[bool, str]:
    probe_rs = tmpdir / "clif_avail.rs"
    probe_rs.write_text("fn main() {}\n", encoding="utf-8")
    out_bin = tmpdir / "clif_avail_bin"
    res = run_cmd([rustc, str(probe_rs), "-Z", "codegen-backend=cranelift", "-o", str(out_bin)])
    return (res.returncode == 0, scrub_text(res.stderr.strip(), str(tmpdir)))


def inspect_elf_sections(binary: Path) -> dict[str, Any]:
    readelf = shutil.which("readelf")
    if not readelf or not binary.exists():
        return {}
    res = run_cmd([readelf, "-SW", str(binary)])
    if res.returncode != 0:
        return {}
    sections: dict[str, int] = {}
    for line in res.stdout.splitlines():
        m = re.search(r"\s(\.[A-Za-z0-9_.-]+)\s+\S+\s+[0-9a-f]+\s+[0-9a-f]+\s+([0-9a-f]+)\s", line)
        if m and m.group(1) in (".eh_frame", ".eh_frame_hdr", ".gcc_except_table", ".text"):
            sections[m.group(1)] = int(m.group(2), 16)
    return sections


def disassemble_symbol(binary: Path, sym: str) -> dict[str, Any]:
    objdump = shutil.which("objdump")
    nm = shutil.which("nm")
    result: dict[str, Any] = {}
    if objdump and binary.exists():
        res = run_cmd([objdump, "-d", f"--disassemble={sym}", str(binary)])
        lines = [ln for ln in res.stdout.splitlines() if ln.strip()]
        # Find exact <sym>: block
        idx = next((i for i, ln in enumerate(lines) if f"<{sym}>:" in ln), None)
        if idx is not None:
            fn_lines = [lines[idx]]
            for ln in lines[idx + 1:]:
                if ln.startswith("Disassembly of section") or re.match(r"^[0-9a-f]+\s+<", ln):
                    break
                fn_lines.append(ln)
            result["disasm"] = "\n".join(fn_lines[:40])
            insn_bytes = 0
            insn_count = 0
            for ln in fn_lines[1:]:
                m = re.match(r"^\s*[0-9a-f]+:\s+((?:[0-9a-f]{2}\s)+)", ln)
                if m:
                    toks = m.group(1).strip().split()
                    if toks == ["cc"]:
                        continue
                    insn_bytes += len(toks)
                    insn_count += 1
            result["insn_count"] = insn_count
            result["insn_bytes"] = insn_bytes
    if nm and binary.exists():
        res = run_cmd([nm, str(binary)])
        wrappers = [ln.split()[-1] for ln in res.stdout.splitlines() if "__inline_asm_" in ln]
        result["has_inline_asm_wrapper_sym"] = bool(wrappers)
        result["wrapper_sym_count"] = len(wrappers)
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rustc", default="rustc", help="Path to nightly rustc binary")
    parser.add_argument("--zerocopy-dir", type=Path, default=None, help="Optional zerocopy checkout for Part C")
    parser.add_argument("--output", type=Path, required=True, help="Output JSON path")
    parser.add_argument("--runs", type=int, default=3, help="Microbenchmark repetition count")
    args = parser.parse_args()

    ver = run_cmd([args.rustc, "-Vv"])
    if ver.returncode != 0:
        print(f"failed to invoke {args.rustc} -Vv: {ver.stderr}", file=sys.stderr)
        return 1

    with tempfile.TemporaryDirectory(prefix="clif_vs_llvm_") as td:
        tmpdir = Path(td)
        clif_ok, clif_msg = check_cranelift_available(args.rustc, tmpdir)
        active_backends = ["llvm", "cranelift"] if clif_ok else ["llvm"]

        report: dict[str, Any] = {
            "timestamp_utc": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
            "rustc_version": ver.stdout.strip(),
            "cranelift_available": clif_ok,
            "cranelift_probe_note": "" if clif_ok else clif_msg,
            "part_a_cross_backend_abi_and_unwind": {},
            "part_b_feature_gate_matrix": {},
            "part_c_microbench_and_crate": {},
        }

        # --- Part A: 2x2 cross-backend ABI + unwind/drop matrix ---
        lib_rs = tmpdir / "abi_lib.rs"
        abi_bin_rs = tmpdir / "abi_bin.rs"
        unwind_bin_rs = tmpdir / "unwind_bin.rs"
        lib_rs.write_text(ABI_LIB_RS, encoding="utf-8")
        abi_bin_rs.write_text(ABI_BIN_RS, encoding="utf-8")
        unwind_bin_rs.write_text(UNWIND_BIN_RS, encoding="utf-8")

        for lib_be in ["llvm", "cranelift"]:
            for bin_be in ["llvm", "cranelift"]:
                cell = f"lib_{lib_be}__bin_{bin_be}"
                if lib_be not in active_backends or bin_be not in active_backends:
                    report["part_a_cross_backend_abi_and_unwind"][cell] = {
                        "skipped": "rustc_codegen_cranelift component not installed in active toolchain"
                    }
                    continue
                rlib = tmpdir / f"libabi_lib_{lib_be}.rlib"
                lib_res = run_cmd(
                    [args.rustc, "--edition=2024", "--crate-name=abi_lib", "--crate-type=rlib",
                     "-C", "opt-level=2", *backend_flags(lib_be), str(lib_rs), "-o", str(rlib)]
                )
                cell_rec: dict[str, Any] = {"lib_rc": lib_res.returncode}
                if lib_res.returncode == 0:
                    for mode_name, src_file in [("abi_no_panic", abi_bin_rs), ("unwind_catch_and_drop", unwind_bin_rs)]:
                        out_bin = tmpdir / f"{cell}_{mode_name}"
                        bin_res = run_cmd(
                            [args.rustc, "--edition=2024", "-C", "opt-level=2", *backend_flags(bin_be),
                             "--extern", f"abi_lib={rlib}", str(src_file), "-o", str(out_bin)]
                        )
                        rec: dict[str, Any] = {
                            "bin_rc": bin_res.returncode,
                            "bin_err": scrub_text(bin_res.stderr.strip(), str(tmpdir)),
                        }
                        if bin_res.returncode == 0:
                            run_res = run_cmd([str(out_bin)])
                            rec["run_rc"] = run_res.returncode
                            rec["stdout"] = scrub_text(run_res.stdout.strip(), str(tmpdir))
                            rec["run_stderr"] = scrub_text(run_res.stderr.strip(), str(tmpdir))
                            if mode_name == "unwind_catch_and_drop":
                                rec["elf_sections"] = inspect_elf_sections(out_bin)
                        cell_rec[mode_name] = rec
                report["part_a_cross_backend_abi_and_unwind"][cell] = cell_rec

        # --- Part B: 11-case feature-gate, asm! lowering, ICE, and ASan fail-open matrix ---
        for case_name, spec in PART_B_CASES.items():
            src_path = tmpdir / f"b_{case_name}.rs"
            src_path.write_text(spec["code"], encoding="utf-8")
            case_rec: dict[str, Any] = {}
            for be in ["llvm", "cranelift"]:
                if be not in active_backends:
                    case_rec[be] = {"skipped": "rustc_codegen_cranelift component not installed"}
                    continue
                out_bin = tmpdir / f"b_{case_name}_{be}"
                cmd = [args.rustc, "--edition=2024", *spec["flags"], *backend_flags(be), str(src_path), "-o", str(out_bin)]
                cres = run_cmd(cmd)
                rec: dict[str, Any] = {
                    "compile_rc": cres.returncode,
                    "stderr_head": scrub_text("\n".join(cres.stderr.splitlines()[:25]), str(tmpdir)),
                }
                if cres.returncode == 0 and spec["run"]:
                    rres = run_cmd([str(out_bin)])
                    rec["run_rc"] = rres.returncode
                    rec["stdout"] = scrub_text(rres.stdout.strip(), str(tmpdir))
                    if rres.stderr.strip():
                        rec["run_stderr_head"] = scrub_text("\n".join(rres.stderr.splitlines()[:15]), str(tmpdir))
                if cres.returncode == 0 and "disasm_sym" in spec:
                    rec.update(disassemble_symbol(out_bin, spec["disasm_sym"]))
                case_rec[be] = rec
            report["part_b_feature_gate_matrix"][case_name] = case_rec

        # --- Part C: Compute microbenchmark (and optional zerocopy rlib build) ---
        mb_rs = tmpdir / "compute_microbench.rs"
        mb_rs.write_text(COMPUTE_MICROBENCH_RS, encoding="utf-8")
        mb_results: dict[str, Any] = {}
        for be in ["llvm", "cranelift"]:
            for opt in ("0", "2"):
                key = f"{be}_O{opt}"
                if be not in active_backends:
                    mb_results[key] = {"skipped": "rustc_codegen_cranelift component not installed"}
                    continue
                out_bin = tmpdir / f"mb_{key}"
                t0 = time.perf_counter()
                cres = run_cmd([args.rustc, "--edition=2024", "-C", f"opt-level={opt}", *backend_flags(be), str(mb_rs), "-o", str(out_bin)])
                t1 = time.perf_counter()
                rec: dict[str, Any] = {
                    "compile_rc": cres.returncode,
                    "compile_sec": round(t1 - t0, 4),
                }
                if cres.returncode == 0:
                    rec["bin_bytes"] = out_bin.stat().st_size
                    samples: list[float] = []
                    checksum = ""
                    for _ in range(args.runs):
                        r0 = time.perf_counter()
                        rres = run_cmd([str(out_bin)])
                        r1 = time.perf_counter()
                        samples.append(round((r1 - r0) * 1000.0, 2))
                        checksum = rres.stdout.strip()
                    rec["checksum"] = checksum
                    rec["run_ms_samples"] = samples
                    rec["run_ms_median"] = round(statistics.median(samples), 2)
                mb_results[key] = rec
        report["part_c_microbench_and_crate"]["compute_microbench"] = mb_results

        if args.zerocopy_dir and (args.zerocopy_dir / "src" / "lib.rs").exists():
            zc_results: dict[str, Any] = {}
            for be in ["llvm", "cranelift"]:
                for opt in ("0", "2"):
                    key = f"{be}_O{opt}"
                    if be not in active_backends:
                        zc_results[key] = {"skipped": "rustc_codegen_cranelift component not installed"}
                        continue
                    out_rlib = tmpdir / f"libzerocopy_{key}.rlib"
                    t0 = time.perf_counter()
                    cres = run_cmd([
                        args.rustc, "--edition=2021", "--crate-name=zerocopy", "--crate-type=rlib",
                        "-C", f"opt-level={opt}", *backend_flags(be),
                        str(args.zerocopy_dir / "src" / "lib.rs"), "-o", str(out_rlib),
                    ])
                    t1 = time.perf_counter()
                    zc_results[key] = {
                        "rc": cres.returncode,
                        "elapsed_sec": round(t1 - t0, 4),
                        "rlib_bytes": out_rlib.stat().st_size if cres.returncode == 0 else 0,
                        "stderr_head": scrub_text("\n".join(cres.stderr.splitlines()[:10]), str(tmpdir)),
                    }
            report["part_c_microbench_and_crate"]["zerocopy_lib_build"] = zc_results

        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
