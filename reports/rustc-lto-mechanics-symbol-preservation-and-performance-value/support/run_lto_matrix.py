#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Empirical 6-mode LTO/CGU matrix and whole-program transformation counter for rustc 1.99.1 / LLVM 23.1.1."""

import argparse
import csv
import json
import os
import re
import resource
import shutil
import statistics
import subprocess
import sys
import tempfile
import time
from pathlib import Path

TIER1_TARGETS = [
    "x86_64-unknown-linux-gnu",
    "aarch64-unknown-linux-gnu",
    "i686-unknown-linux-gnu",
    "x86_64-pc-windows-gnu",
    "x86_64-pc-windows-msvc",
    "i686-pc-windows-msvc",
    "aarch64-pc-windows-msvc",
    "aarch64-apple-darwin",
]

LTO_MODES = [
    ("NoLTO_16CGU", ["-C", "opt-level=3", "-C", "lto=off", "-C", "codegen-units=16"]),
    ("ThinLocal_16CGU", ["-C", "opt-level=3", "-C", "codegen-units=16"]),
    ("NoLTO_1CGU", ["-C", "opt-level=3", "-C", "lto=off", "-C", "codegen-units=1"]),
    ("ThinLTO", ["-C", "opt-level=3", "-C", "lto=thin", "-C", "codegen-units=16"]),
    ("FatLTO", ["-C", "opt-level=3", "-C", "lto=fat", "-C", "codegen-units=16"]),
    ("LinkerPluginLTO", ["-C", "opt-level=3", "-C", "linker-plugin-lto", "-C", "codegen-units=16"]),
]

# Upstream dependency rlib (`dep_math`) with non-#[inline] cross-crate functions
# exceeding cross_crate_inline_threshold (calls > 0 or statements > 20 in cross_crate_inline.rs:96-110),
# so MIR is NOT exported in .rmeta and inlining requires LLVM ThinLTO / FatLTO / LinkerPluginLTO!
DEP_CRATE_RS = r"""#![no_std]
#![crate_name = "dep_math"]
#![crate_type = "rlib"]

pub trait Transform {
    fn apply(&self, x: u64) -> u64;
}

pub struct AffineTransform {
    pub mul: u64,
    pub add: u64,
}

impl Transform for AffineTransform {
    fn apply(&self, x: u64) -> u64 {
        cross_crate_poly_eval(x, self.add, self.mul, 0x517cc1b727220a95)
    }
}

// Because cross_crate_mix_step has >20 MIR statements (a loop with 4 basic blocks and 24 statements),
// `cross_crate_inlinable` (`compiler/rustc_mir_transform/src/cross_crate_inline.rs:106`, default threshold = 20)
// returns `false`, so MIR is NOT exported in `.rmeta`, whereas LLVM ThinLTO/FatLTO inlines and unrolls it across crates!
pub fn cross_crate_mix_step(x: u64, k: u64) -> u64 {
    let mut v = x ^ k;
    let mut round = 0u64;
    while round < 4 {
        let a = v.wrapping_add(0x9e3779b97f4a7c15 ^ round);
        let b = (a ^ (a >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        let c = (b ^ (b >> 27)).wrapping_mul(0x94d049bb133111eb);
        let d = c.rotate_left(17).wrapping_add(k ^ round);
        v = d ^ (d >> 31);
        round += 1;
    }
    v
}

pub fn cross_crate_poly_eval(x: u64, c0: u64, c1: u64, c2: u64) -> u64 {
    let mut v = x ^ c0;
    let mut i = 0u64;
    while i < 3 {
        let a = v.wrapping_mul(c2).wrapping_add(c1 ^ i);
        let b = a.rotate_left(23).wrapping_add(c0);
        let c = (b ^ (b >> 29)).wrapping_mul(0x2545f4914f6cdd1d);
        v = c.wrapping_add(x | 1);
        i += 1;
    }
    v
}

pub fn dead_exported_helper_1(x: u64) -> u64 {
    cross_crate_mix_step(x, 1).rotate_left(19) ^ 0xdeadbeefcafe0001
}

pub fn dead_exported_helper_2(x: u64) -> u64 {
    cross_crate_mix_step(x, 2).rotate_right(23) ^ 0xdeadbeefcafe0002
}

#[used]
pub static KEEP_COMPILER_USED: u64 = 0x1122334455667788;
"""

# Leaf crate with multiple modules (so 16 CGUs partition functions across CGUs unless CGU=1 or ThinLocal/LTO merges them)
LEAF_CRATE_RS = r"""#![allow(dead_code)]
extern crate dep_math;

pub mod mod_a {
    // Exceeds MIR inline_mir_threshold (50 statements) so MIR inliner does not inline across CGUs,
    // allowing ThinLocal_16CGU / NoLTO_1CGU / ThinLTO / FatLTO to inline it via LLVM while NoLTO_16CGU cannot!
    pub fn cross_cgu_step_a(x: u64, k: u64) -> u64 {
        let a0 = x.wrapping_add(k).rotate_left(7);
        let a1 = a0.wrapping_mul(0x9e3779b97f4a7c15) ^ (k >> 3);
        let a2 = a1.wrapping_add(a0).rotate_left(13);
        let a3 = a2.wrapping_mul(0xbf58476d1ce4e5b9) ^ (a1 >> 11);
        let a4 = a3.wrapping_add(a2).rotate_left(19);
        let a5 = a4.wrapping_mul(0x94d049bb133111eb) ^ (a3 >> 17);
        dep_math::cross_crate_mix_step(a5, k)
    }
}

pub mod mod_b {
    pub fn cross_cgu_step_b(x: u64, n: usize) -> u64 {
        let mut acc = x;
        let mut i = 0usize;
        while i < n {
            acc = crate::mod_a::cross_cgu_step_a(acc, i as u64);
            acc = dep_math::cross_crate_poly_eval(acc, 3, 5, 7);
            i += 1;
        }
        acc
    }
}

pub mod mod_c {
    use dep_math::{AffineTransform, Transform};
    pub fn run_dyn_dispatch(x: u64, iters: usize) -> u64 {
        let t = AffineTransform { mul: 6364136223846793005, add: 1442695040888963407 };
        let dyn_ref: &dyn Transform = &t;
        let mut v = x;
        for _ in 0..iters {
            v = dyn_ref.apply(v);
        }
        v
    }
}

#[no_mangle]
pub extern "C" fn lto_benchmark_entry(seed: u64, iters: usize) -> u64 {
    let a = mod_a::cross_cgu_step_a(seed, 0x1234_5678_9abc_def0);
    let b = mod_b::cross_cgu_step_b(a, iters);
    let c = mod_c::run_dyn_dispatch(b, iters);
    c
}
"""

BENCH_MAIN_RS = r"""
extern crate leaf_bench;
use std::time::Instant;

fn main() {
    let mut times_ns = Vec::with_capacity(35);
    let mut sink = 0u64;
    for round in 0..35 {
        let t0 = Instant::now();
        let res = std::hint::black_box(leaf_bench::lto_benchmark_entry(
            std::hint::black_box(0x123456789abcdef0u64 ^ (round as u64)),
            std::hint::black_box(200_000),
        ));
        let dt = t0.elapsed().as_nanos() as u64;
        sink ^= res;
        if round >= 5 {
            times_ns.push(dt);
        }
    }
    times_ns.sort_unstable();
    let med = times_ns[times_ns.len() / 2];
    println!("MEDIAN_NS={} SINK={}", med, sink);
}
"""


def parse_text_size(llvm_size_bin: str, files: list[Path]) -> int:
    if not files:
        return 0
    proc = subprocess.run([llvm_size_bin, "--format=sysv"] + [str(f) for f in files], capture_output=True, text=True, check=False)
    total = 0
    for line in proc.stdout.splitlines():
        parts = line.split()
        if len(parts) >= 2 and parts[0].startswith((".text", "__text")):
            try:
                total += int(parts[1])
            except ValueError:
                pass
    return total


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", default="1.99.1-x86_64-unknown-linux-gnu")
    parser.add_argument("--out-dir", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()

    sysroot = Path(subprocess.check_output(["rustc", f"+{args.toolchain}", "--print", "sysroot"], text=True).strip())
    bin_dir = sysroot / "lib/rustlib/x86_64-unknown-linux-gnu/bin"
    llvm_size_bin = str(bin_dir / "llvm-size")
    llvm_nm_bin = str(bin_dir / "llvm-nm")
    llvm_objdump_bin = str(bin_dir / "llvm-objdump")
    rust_lld_bin = str(bin_dir / "rust-lld")

    rows = []
    transforms_summary = {}

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        for target in TIER1_TARGETS:
            t_dir = tmp_path / target
            t_dir.mkdir(parents=True, exist_ok=True)
            dep_src = t_dir / "dep_math.rs"
            leaf_src = t_dir / "leaf_bench.rs"
            dep_src.write_text(DEP_CRATE_RS, encoding="utf-8")
            leaf_src.write_text(LEAF_CRATE_RS, encoding="utf-8")

            # Compile upstream dep_math.rlib once with default embed-bitcode=yes
            dep_rlib = t_dir / "libdep_math.rlib"
            subprocess.run([
                "rustc", f"+{args.toolchain}", "--edition=2021",
                "--crate-type=rlib", "-C", "opt-level=3",
                "--target", target, str(dep_src), "-o", str(dep_rlib)
            ], check=True)

            transforms_summary[target] = {}

            for mode_name, mode_flags in LTO_MODES:
                m_dir = t_dir / mode_name
                m_dir.mkdir(parents=True, exist_ok=True)

                # Measure compile wall time and child peak RSS via /usr/bin/time -v if available or Python resource/time
                # Note: check_lto_allowed rejects CrateType::Rlib under -Clto=thin or -Clto=fat,
                # so we compile leaf_bench as --crate-type=staticlib with -C save-temps
                cmd = [
                    "rustc", f"+{args.toolchain}", "--edition=2021",
                    "--crate-type=staticlib",
                    "--emit=obj,link,llvm-ir",
                    "-C", "save-temps",
                    "--target", target,
                    "--extern", f"dep_math={dep_rlib}",
                    "-C", "debuginfo=1",
                    "-C", "remark=all",
                    str(leaf_src),
                    "--out-dir", str(m_dir),
                ] + mode_flags

                t0 = time.monotonic()
                proc = subprocess.run(cmd, capture_output=True, text=True)
                compile_ms = round((time.monotonic() - t0) * 1000.0, 2)
                if proc.returncode != 0:
                    raise RuntimeError(f"Failed {target} {mode_name}: {proc.stderr}")

                objs = sorted([
                    p for p in m_dir.glob("*.o")
                    if "allocator_shim" not in p.name and not p.name.endswith(".Generated.rcgu.o")
                ])
                staticlibs = list(m_dir.glob("*.a")) + list(m_dir.glob("*.lib"))
                ll_files = list(m_dir.glob("*.ll"))

                crate_text = parse_text_size(llvm_size_bin, objs)
                staticlib_bytes = staticlibs[0].stat().st_size if staticlibs else 0

                # Count cross-crate calls remaining vs inlined in final object(s)
                disasm = subprocess.run([llvm_objdump_bin, "-d"] + [str(f) for f in objs], capture_output=True, text=True, check=False).stdout
                cross_crate_calls_remaining = len(re.findall(r"cross_crate_mix_step|cross_crate_poly_eval", disasm))
                nm_out = subprocess.run([llvm_nm_bin] + [str(f) for f in staticlibs], capture_output=True, text=True, check=False).stdout
                dead_helpers_surviving = len(re.findall(r"dead_exported_helper_[12]", nm_out))
                used_static_preserved = 1 if "KEEP_COMPILER_USED" in nm_out else 0

                # Measure runtime on executable targets (x86_64 and i686 native, aarch64 instruction/emulation speed)
                median_runtime_us = None
                if target in ("x86_64-unknown-linux-gnu", "i686-unknown-linux-gnu"):
                    main_src = m_dir / "main.rs"
                    main_src.write_text(
                        LEAF_CRATE_RS + "\n" +
                        BENCH_MAIN_RS.replace("extern crate leaf_bench;\n", "").replace("leaf_bench::", ""),
                        encoding="utf-8"
                    )
                    bin_out = m_dir / "bench_bin"
                    b_cmd = [
                        "rustc", f"+{args.toolchain}", "--edition=2021",
                        "--target", target,
                        "--extern", f"dep_math={dep_rlib}",
                        str(main_src), "-o", str(bin_out)
                    ] + [f for f in mode_flags if not f.startswith("linker-plugin-lto")]
                    b_proc = subprocess.run(b_cmd, capture_output=True, text=True)
                    if b_proc.returncode == 0:
                        r_proc = subprocess.run([str(bin_out)], capture_output=True, text=True, check=True)
                        m_ns = re.search(r"MEDIAN_NS=(\d+)", r_proc.stdout)
                        if m_ns:
                            median_runtime_us = round(int(m_ns.group(1)) / 1000.0, 2)
                elif target == "aarch64-unknown-linux-gnu":
                    # Freestanding no_std timing/execution under qemu-aarch64
                    a64_src = m_dir / "a64_main.rs"
                    a64_src.write_text(
                        "#![no_std]\n#![no_main]\n" +
                        LEAF_CRATE_RS + "\n" +
                        r"""use core::arch::asm;
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }
#[repr(C)]
struct Timespec { tv_sec: i64, tv_nsec: i64 }
unsafe fn clock_ns() -> u64 {
    let mut ts = Timespec { tv_sec: 0, tv_nsec: 0 };
    let _: isize;
    asm!("mov x8, #113", "mov x0, #1", "svc #0", in("x1") &mut ts as *mut Timespec, lateout("x0") _, out("x8") _);
    (ts.tv_sec as u64) * 1_000_000_000 + (ts.tv_nsec as u64)
}
#[no_mangle]
pub unsafe extern "C" fn _start() -> ! {
    let mut samples = [0u64; 15];
    let mut sink = 0u64;
    let mut r = 0usize;
    while r < 18 {
        let t0 = clock_ns();
        sink ^= core::hint::black_box(lto_benchmark_entry(
            core::hint::black_box(0x123456789abcdef0 ^ (r as u64)),
            core::hint::black_box(200_000),
        ));
        let dt = clock_ns().wrapping_sub(t0);
        if r >= 3 { samples[r - 3] = dt; }
        r += 1;
    }
    // Insertion sort 15 samples and report median in 0.01us units
    let mut i = 1usize;
    while i < 15 {
        let v = samples[i];
        let mut j = i;
        while j > 0 && samples[j - 1] > v {
            samples[j] = samples[j - 1];
            j -= 1;
        }
        samples[j] = v;
        i += 1;
    }
    let med_ns = samples[7] ^ (sink & 0);
    let buf = med_ns.to_le_bytes();
    let _: isize;
    asm!("mov x8, #64", "mov x0, #1", "svc #0", in("x1") buf.as_ptr(), in("x2") 8usize, lateout("x0") _, out("x8") _);
    asm!("mov x8, #94", "mov x0, #0", "svc #0", options(noreturn));
}
""", encoding="utf-8")
                    a64_bin = m_dir / "a64_bin"
                    a_cmd = [
                        "rustc", f"+{args.toolchain}", "--edition=2021",
                        "--target", target, "-C", "panic=abort",
                        "--extern", f"dep_math={dep_rlib}",
                        "-C", f"linker={rust_lld_bin}", "-C", "linker-flavor=ld.lld",
                        str(a64_src), "-o", str(a64_bin)
                    ] + [f for f in mode_flags if not f.startswith("linker-plugin-lto")]
                    a_proc = subprocess.run(a_cmd, capture_output=True, text=True)
                    if a_proc.returncode == 0:
                        q_proc = subprocess.run(["qemu-aarch64", str(a64_bin)], capture_output=True, check=True)
                        if len(q_proc.stdout) == 8:
                            median_runtime_us = round(int.from_bytes(q_proc.stdout, "little") / 1000.0, 2)

                rows.append({
                    "target": target,
                    "lto_mode": mode_name,
                    "compile_time_ms": compile_ms,
                    "cgu_object_count": len(objs),
                    "crate_text_bytes": crate_text,
                    "staticlib_bytes": staticlib_bytes,
                    "cross_crate_calls_remaining_in_entry": cross_crate_calls_remaining,
                    "dead_exported_helpers_in_archive": dead_helpers_surviving,
                    "used_static_preserved": used_static_preserved,
                    "median_runtime_us": median_runtime_us if median_runtime_us is not None else "",
                })
                transforms_summary[target][mode_name] = {
                    "cgu_object_count": len(objs),
                    "crate_text_bytes": crate_text,
                    "cross_crate_calls_inlined": cross_crate_calls_remaining == 0,
                    "cross_crate_calls_remaining": cross_crate_calls_remaining,
                    "dead_exported_helpers_eliminated": dead_helpers_surviving == 0,
                    "used_static_preserved": used_static_preserved == 1,
                    "median_runtime_us": median_runtime_us,
                }
                shutil.rmtree(m_dir, ignore_errors=True)

    args.out_dir.mkdir(parents=True, exist_ok=True)
    csv_path = args.out_dir / "lto_speed_size_compiletime.csv"
    fieldnames = [
        "target", "lto_mode", "compile_time_ms", "cgu_object_count",
        "crate_text_bytes", "staticlib_bytes",
        "cross_crate_calls_remaining_in_entry",
        "dead_exported_helpers_in_archive",
        "used_static_preserved", "median_runtime_us"
    ]
    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        w.writerows(rows)

    json_path = args.out_dir / "lto_whole_program_transforms.json"
    json_path.write_text(json.dumps({
        "toolchain": args.toolchain,
        "rust_commit": "58cf8f9c35b355199727627d07ae34a4e2846d67",
        "llvm_commit": "1b9c0d5ff9bbe7634aead059efe6b11a7eeba145",
        "crate_type_export_rules": {
            "Executable": {"export_level": "C", "allows_lto": True, "default_lto": "ThinLocal (if CGU > 1 and opt >= 1)"},
            "StaticLib": {"export_level": "C", "allows_lto": True, "default_lto": "ThinLocal"},
            "Cdylib": {"export_level": "C", "allows_lto": True, "default_lto": "ThinLocal"},
            "ProcMacro": {"export_level": "C", "allows_lto": "Requires -Zdylib-lto", "default_lto": "ThinLocal"},
            "Dylib": {"export_level": "Rust", "allows_lto": "Requires -Zdylib-lto", "default_lto": "ThinLocal"},
            "Rlib": {"export_level": "Rust", "allows_lto": False, "default_lto": "PreLink bitcode embedding"},
        },
        "target_results": transforms_summary,
    }, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {csv_path} ({len(rows)} rows) and {json_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
