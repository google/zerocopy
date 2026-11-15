#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Benchmark 1-to-k tail duplication (-tail-dup-placement), hot/cold function splitting, and >1 MiB AArch64 cross-section branch-relaxation veneers."""

import argparse
import json
import os
import statistics
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
TC_ROOT = Path(os.path.expanduser("~/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu"))
RUSTC = str(TC_ROOT / "bin" / "rustc")
LLVM_BIN = TC_ROOT / "lib" / "rustlib" / "x86_64-unknown-linux-gnu" / "bin"
RUST_LLD = str(LLVM_BIN / "rust-lld")
LLVM_SIZE = str(LLVM_BIN / "llvm-size")
LLVM_OBJDUMP = str(LLVM_BIN / "llvm-objdump")
LLVM_MC = "/usr/bin/llvm-mc"
QEMU_AARCH64 = "/usr/bin/qemu-aarch64"

BENCH_SERDE_JSON_RS = r"""
use std::time::Instant;
#[inline(never)]
pub fn kernel(input: &[u8]) -> u64 {
    let mut acc = 0u64;
    let mut in_str = false;
    let mut esc = false;
    let mut depth = 0u64;
    for &b in input {
        if in_str {
            if esc { esc = false; }
            else if b == b'\\' { esc = true; }
            else if b == b'"' { in_str = false; acc = acc.wrapping_add(depth.wrapping_mul(31)); }
            else { acc = acc.wrapping_mul(131).wrapping_add(b as u64); }
        } else {
            match b {
                b'"' => in_str = true,
                b'{' | b'[' => depth = depth.wrapping_add(1),
                b'}' | b']' => depth = depth.wrapping_sub(1),
                b':' | b',' => acc = acc.rotate_left(7) ^ depth,
                b'0'..=b'9' => acc = acc.wrapping_mul(10).wrapping_add((b - b'0') as u64),
                _ => {}
            }
        }
    }
    acc ^ depth
}
fn main() {
    let payload = br#"{"id":12345,"name":"alpha_beta_gamma","values":[10,20,30,40,50],"nested":{"ok":true,"msg":"escaped \"quote\" here"}}"#;
    let mut buf = Vec::with_capacity(payload.len() * 128);
    for _ in 0..128 { buf.extend_from_slice(payload); }
    for _ in 0..8 { std::hint::black_box(kernel(std::hint::black_box(&buf))); }
    let mut times = Vec::with_capacity(21);
    for _ in 0..21 {
        let t0 = Instant::now();
        for _ in 0..15 { std::hint::black_box(kernel(std::hint::black_box(&buf))); }
        times.push(t0.elapsed().as_nanos() as f64 / 15_000.0);
    }
    times.sort_by(|a, b| a.partial_cmp(b).unwrap());
    println!("{:.4}", times[times.len() / 2]);
}
"""

BENCH_BYTECODE_DISPATCH_RS = r"""
use std::time::Instant;
#[inline(never)]
pub fn vm_dispatch(ops: &[u8], init: u64) -> u64 {
    let mut acc = init;
    let mut r1 = init ^ 0x9e3779b97f4a7c15;
    let mut r2 = init.rotate_left(17);
    let mut i = 0usize;
    while i < ops.len() {
        let op = ops[i];
        i += 1;
        match op & 7 {
            0 => { acc = acc.wrapping_add(r1); r1 = r1.rotate_left(3); }
            1 => { acc ^= r2; r2 = r2.wrapping_add(0x517cc1b727220a95); }
            2 => { acc = acc.wrapping_mul(33).wrapping_add(op as u64); }
            3 => { r1 = r1.wrapping_sub(acc); acc = acc.rotate_right(5); }
            4 => { r2 ^= acc.wrapping_shl(7); acc = acc.wrapping_add(1); }
            5 => { acc = (acc ^ r1).wrapping_add(r2); }
            6 => { r1 = r1.rotate_left(11) ^ (op as u64); acc = acc.wrapping_add(r1); }
            _ => { acc = acc.rotate_left(1) ^ r2; }
        }
    }
    acc ^ r1 ^ r2
}
fn main() {
    let mut ops = Vec::with_capacity(16384);
    let mut s = 0x123456789abcdef0u64;
    for _ in 0..16384 {
        s ^= s << 13; s ^= s >> 7; s ^= s << 17;
        ops.push((s & 0xff) as u8);
    }
    for _ in 0..8 { std::hint::black_box(vm_dispatch(std::hint::black_box(&ops), 42)); }
    let mut times = Vec::with_capacity(21);
    for _ in 0..21 {
        let t0 = Instant::now();
        for _ in 0..15 { std::hint::black_box(vm_dispatch(std::hint::black_box(&ops), 42)); }
        times.push(t0.elapsed().as_nanos() as f64 / 15_000.0);
    }
    times.sort_by(|a, b| a.partial_cmp(b).unwrap());
    println!("{:.4}", times[times.len() / 2]);
}
"""


def measure_workload(name: str, src: str, llvm_args: list[str], work_dir: Path) -> dict:
    rs_path = work_dir / f"{name}.rs"
    exe_path = work_dir / f"{name}_exe"
    rs_path.write_text(src, encoding="utf-8")
    cmd = [RUSTC, "-C", "opt-level=3", "-C", "codegen-units=1"]
    for a in llvm_args:
        cmd.extend(["-C", f"llvm-args={a}"])
    cmd.extend([str(rs_path), "-o", str(exe_path)])
    subprocess.run(cmd, check=True)

    # Measure median across 3 process invocations
    samples = []
    for _ in range(3):
        out = subprocess.check_output([str(exe_path)], text=True).strip()
        samples.append(float(out))
    med_us = statistics.median(samples)

    # Disassemble kernel to count unconditional `jmp` instructions inside the loop
    dis = subprocess.run(
        [LLVM_OBJDUMP, "-d", str(exe_path)],
        capture_output=True, text=True, check=True,
    ).stdout
    fn_name = "kernel" if "kernel" in src else "vm_dispatch"
    in_fn = False
    fn_insts = 0
    uncond_jmps = 0
    for line in dis.splitlines():
        if f"{fn_name}>:" in line:
            in_fn = True
            continue
        if in_fn:
            if not line.strip() or line.endswith(">:"):
                break
            if "\t" in line:
                fn_insts += 1
                if "\tjmp\t" in line or "\tjmpq\t" in line:
                    uncond_jmps += 1

    return {
        "median_us": round(med_us, 4),
        "fn_instructions": fn_insts,
        "unconditional_jmps_in_fn": uncond_jmps,
    }


def test_aarch64_cross_section_branch_relaxation(work_dir: Path) -> dict:
    """Verify AArch64 >1 MiB cross-section (.text -> .text.unlikely) conditional branch failure vs. 32-bit veneer relaxation."""
    # 1. Unrelaxed cross-section `b.eq .Lcold` separated by a 2 MiB `.space 0x200000` padding section
    unrelaxed_s = work_dir / "unrelaxed_aarch64.s"
    unrelaxed_o = work_dir / "unrelaxed_aarch64.o"
    unrelaxed_exe = work_dir / "unrelaxed_aarch64.elf"
    unrelaxed_s.write_text(
        r"""
.section .text.hot,"ax",@progbits
.globl _start
_start:
    mov x0, #0
    cbz x0, .Lcold_target
    mov x0, #0
    mov x8, #94
    svc #0

.section .text.pad,"ax",@progbits
    .space 2097152

.section .text.unlikely,"ax",@progbits
.Lcold_target:
    mov x0, #42
    mov x8, #94
    svc #0
""",
        encoding="utf-8",
    )
    subprocess.run(
        [LLVM_MC, "--triple=aarch64-unknown-linux-gnu", "--filetype=obj", str(unrelaxed_s), "-o", str(unrelaxed_o)],
        check=True,
    )
    unrelaxed_link = subprocess.run(
        [RUST_LLD, "-flavor", "gnu", "-e", "_start", str(unrelaxed_o), "-o", str(unrelaxed_exe)],
        capture_output=True, text=True,
    )
    unrelaxed_overflowed = (unrelaxed_link.returncode != 0 and "R_AARCH64_CONDBR19" in unrelaxed_link.stderr)

    # 2. Relaxed cross-section branch (`cbnz x0, .Lhot_continue; b .Lcold_target`) via 26-bit +/-128 MiB `R_AARCH64_JUMP26`
    relaxed_s = work_dir / "relaxed_aarch64.s"
    relaxed_o = work_dir / "relaxed_aarch64.o"
    relaxed_exe = work_dir / "relaxed_aarch64.elf"
    relaxed_s.write_text(
        r"""
.section .text.hot,"ax",@progbits
.globl _start
_start:
    mov x0, #0
    cbnz x0, .Lhot_continue
.Lveneer_cold:
    b .Lcold_target
.Lhot_continue:
    mov x0, #1
    mov x8, #94
    svc #0

.section .text.pad,"ax",@progbits
    .space 2097152

.section .text.unlikely,"ax",@progbits
.Lcold_target:
    mov x0, #0
    mov x8, #94
    svc #0
""",
        encoding="utf-8",
    )
    subprocess.run(
        [LLVM_MC, "--triple=aarch64-unknown-linux-gnu", "--filetype=obj", str(relaxed_s), "-o", str(relaxed_o)],
        check=True,
    )
    subprocess.run(
        [RUST_LLD, "-flavor", "gnu", "-e", "_start", str(relaxed_o), "-o", str(relaxed_exe)],
        check=True,
    )
    qemu_run = subprocess.run([QEMU_AARCH64, str(relaxed_exe)], capture_output=True, text=True)

    return {
        "separation_bytes": 2097152,
        "unrelaxed_condbr19_linker_failed_as_expected": unrelaxed_overflowed,
        "unrelaxed_lld_error_excerpt": unrelaxed_link.stderr.strip().splitlines()[0] if unrelaxed_link.stderr else "",
        "relaxed_jump26_veneer_linked_cleanly": True,
        "relaxed_qemu_aarch64_executed_cleanly": (qemu_run.returncode == 0),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=HERE / "taildup_branch_relax_metrics.json")
    args = parser.parse_args()

    configs = {
        "no_tail_dup_threshold_1": ["-tail-dup-placement=false", "-tail-dup-size=1"],
        "default_tail_dup_threshold_2": ["-tail-dup-placement=true", "-tail-dup-placement-threshold=2"],
        "aggressive_tail_dup_threshold_6_plus_ext_tsp": [
            "-tail-dup-placement=true",
            "-tail-dup-placement-threshold=6",
            "-enable-ext-tsp-block-placement=true",
            "-align-all-nofallthru-blocks=5",
        ],
    }

    tmp_base = Path(os.environ.get("TMPDIR", "/tmp"))
    with tempfile.TemporaryDirectory(dir=tmp_base) as tmp:
        work_dir = Path(tmp)
        bench_results = {}
        for wname, wsrc in [
            ("bench-serde-json", BENCH_SERDE_JSON_RS),
            ("bench-bytecode-dispatch", BENCH_BYTECODE_DISPATCH_RS),
        ]:
            w_res = {}
            for cname, cflags in configs.items():
                w_res[cname] = measure_workload(f"{wname}_{cname}", wsrc, cflags, work_dir)
            base_us = w_res["no_tail_dup_threshold_1"]["median_us"]
            opt_us = w_res["aggressive_tail_dup_threshold_6_plus_ext_tsp"]["median_us"]
            w_res["speedup_pct"] = round(100.0 * (base_us - opt_us) / base_us, 2)
            bench_results[wname] = w_res

        aarch64_relax = test_aarch64_cross_section_branch_relaxation(work_dir)

    summary = {
        "benchmarks": bench_results,
        "aarch64_2mib_cross_section_branch_relaxation": aarch64_relax,
    }
    args.out.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(f"Completed tail-duplication and AArch64 2 MiB cross-section relaxation benchmarks; wrote {args.out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
