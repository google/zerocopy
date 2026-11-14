#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Controlled 64-byte NOP-padding phase-response sweep and llvm-mca x86-64/AArch64 front-end bottleneck analyzer."""

import argparse
import json
import os
import re
import statistics
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
TC_ROOT = Path(os.path.expanduser("~/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu"))
RUSTC = str(TC_ROOT / "bin" / "rustc")
LLVM_MCA = "/usr/bin/llvm-mca"

# Controlled single-variable NOP-padding probe in Rust inline asm:
# Sweeps k in 0..63 bytes of precursor 0x90 NOP padding ahead of a hot inner loop
# aligned to a 64-byte cache-line boundary (`.p2align 6`), shifting the loop header
# and macro-fused CMP+JCC through every offset k = VA mod 64 in {0..63}.
NOP_SWEEP_TEMPLATE = r"""#![allow(unused_assignments)]
use std::arch::asm;
use std::time::Instant;

#[inline(never)]
pub fn run_padded_loop(ptr: *const u8, len: usize, iters: usize) -> u64 {{
    let mut total: u64 = 0;
    for _ in 0..iters {{
        let mut idx: usize = 0;
        let mut acc: u64 = 0;
        unsafe {{
            asm!(
                ".p2align 6, 0x90",
                {nop_directives}
                "2:",
                "movzx {tmp:e}, byte ptr [{base} + {idx}]",
                "imul {acc}, {acc}, 131",
                "add {acc}, {tmp}",
                "inc {idx}",
                "cmp {idx}, {len}",
                "jb 2b",
                base = in(reg) ptr,
                len = in(reg) len,
                idx = inout(reg) idx,
                acc = inout(reg) acc,
                tmp = out(reg) _,
                options(nostack, readonly)
            );
        }}
        total = total.wrapping_add(acc);
    }}
    total
}}

fn main() {{
    let buf = [0x61u8; 4096];
    // Warmup
    let mut w = 0u64;
    for _ in 0..5 {{
        w ^= run_padded_loop(buf.as_ptr(), buf.len(), 200);
    }}
    let mut samples_ns = Vec::with_capacity(15);
    for _ in 0..15 {{
        let t0 = Instant::now();
        let v = std::hint::black_box(run_padded_loop(buf.as_ptr(), buf.len(), 400));
        let dt = t0.elapsed().as_nanos() as f64 / 400.0;
        if v == 0xdeadbeef {{ println!("{{w}}"); }}
        samples_ns.push(dt);
    }}
    samples_ns.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let med = samples_ns[samples_ns.len() / 2];
    println!("{{med:.3}}");
}}
"""

X86_JSON_HOT_LOOP_ASM = """
# LLVM-MCA snippet for x86-64 Ice Lake-SP (Sunny Cove) hot JSON / DFA inner loop
.Lloop:
    movzbl  (%rdi,%rcx), %eax
    cmpb    $34, %al
    je      .Lquote
    imulq   $131, %rdx, %rdx
    addq    %rax, %rdx
.Lquote:
    incq    %rcx
    cmpq    %rsi, %rcx
    jb      .Lloop
"""

AARCH64_HOT_LOOP_ASM = """
.Lloop_a64:
    ldrb    w8, [x0, x2]
    lsl     x9, x3, #10
    add     x9, x1, x9
    ldr     w3, [x9, x8, lsl #2]
    tst     w3, #0x4
    cinc    w4, w4, ne
    and     w3, w3, #0x3
    add     x2, x2, #1
    cmp     x2, x5
    b.lo    .Lloop_a64
"""


def run_mca(triple: str, cpu: str, asm_text: str) -> dict:
    extra = ["-bottleneck-analysis"] if triple.startswith("x86_64") else []
    proc = subprocess.run(
        [LLVM_MCA, f"-mtriple={triple}", f"-mcpu={cpu}", "-iterations=100", "-timeline", "-timeline-max-iterations=4"] + extra,
        input=asm_text,
        capture_output=True,
        text=True,
        check=True,
    )
    out = proc.stdout
    def grab(pat, cast=float):
        m = re.search(pat, out)
        return cast(m.group(1)) if m else None
    return {
        "triple": triple,
        "mcpu": cpu,
        "iterations": grab(r"Iterations:\s+(\d+)", int),
        "instructions": grab(r"Instructions:\s+(\d+)", int),
        "total_cycles": grab(r"Total Cycles:\s+(\d+)", int),
        "total_uops": grab(r"Total uOps:\s+(\d+)", int),
        "dispatch_width": grab(r"Dispatch Width:\s+(\d+)", int),
        "uops_per_cycle": grab(r"uOps Per Cycle:\s+([0-9.]+)", float),
        "ipc": grab(r"IPC:\s+([0-9.]+)", float),
        "block_rthroughput": grab(r"Block RThroughput:\s+([0-9.]+)", float),
        "raw_excerpt": "\n".join(out.splitlines()[:38]),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-json", type=Path, default=HERE / "layout_root_cause_catalog.json")
    parser.add_argument("--out-mca", type=Path, default=HERE / "llvm_mca_frontend_profiles.txt")
    args = parser.parse_args()

    tmp_base = Path(os.environ.get("TMPDIR", "/tmp"))
    tmp_base.mkdir(parents=True, exist_ok=True)

    phase_curve = []
    with tempfile.TemporaryDirectory(dir=tmp_base) as tmp:
        tmp_dir = Path(tmp)
        # Sweep all 64 byte offsets k in 0..63 (sampling every byte offset k=0..63!)
        for k in range(64):
            nop_str = f'".rept {k}\\n.byte 0x90\\n.endr",' if k > 0 else ""
            src = NOP_SWEEP_TEMPLATE.replace("{{", "{").replace("}}", "}").replace("{nop_directives}", nop_str)
            rs_path = tmp_dir / f"sweep_{k}.rs"
            bin_path = tmp_dir / f"sweep_{k}"
            rs_path.write_text(src, encoding="utf-8")
            subprocess.run([RUSTC, "-C", "opt-level=3", str(rs_path), "-o", str(bin_path)], check=True)
            out = subprocess.check_output([str(bin_path)], text=True).strip()
            med_ns = float(out)
            # In our 19-byte loop body:
            #   0..3: movzx (4B)
            #   4..7: imul (4B)
            #   8..10: add (3B)
            #  11..13: inc (3B)
            #  14..16: cmp (3B)
            #  17..18: jb (2B) -> ends at offset (k + 19)
            loop_start_mod32 = k % 32
            loop_end_mod32 = (k + 19) % 32
            cmp_start = k + 14
            jcc_end = k + 19
            skx102_crosses_or_ends_32b = ((cmp_start // 32) != ((jcc_end - 1) // 32)) or (jcc_end % 32 == 0)
            spans_two_64b_lines = (k + 19) > 64
            phase_curve.append({
                "nop_pad_bytes_k": k,
                "loop_header_mod_32": loop_start_mod32,
                "loop_header_mod_64": k,
                "cmp_jcc_range_mod_64": [cmp_start % 64, jcc_end % 64],
                "skx102_jcc_crosses_or_ends_32b": skx102_crosses_or_ends_32b,
                "loop_spans_two_64b_cache_lines": spans_two_64b_lines,
                "median_ns_per_4k_iter": round(med_ns, 3),
            })

    # Run llvm-mca across x86-64 Ice Lake-SP, Skylake-AVX512, and AArch64 Neoverse-V1, Neoverse-N2, Apple-M1
    mca_profiles = {
        "x86_64_icelake_server": run_mca("x86_64-unknown-linux-gnu", "icelake-server", X86_JSON_HOT_LOOP_ASM),
        "x86_64_skylake_avx512": run_mca("x86_64-unknown-linux-gnu", "skylake-avx512", X86_JSON_HOT_LOOP_ASM),
        "aarch64_neoverse_v1": run_mca("aarch64-unknown-linux-gnu", "neoverse-v1", AARCH64_HOT_LOOP_ASM),
        "aarch64_neoverse_n2": run_mca("aarch64-unknown-linux-gnu", "neoverse-n2", AARCH64_HOT_LOOP_ASM),
        "aarch64_apple_m1": run_mca("aarch64-apple-darwin", "apple-m1", AARCH64_HOT_LOOP_ASM),
    }

    mca_txt = []
    for k, v in mca_profiles.items():
        mca_txt.append(f"=== {k} ({v['triple']} / -mcpu={v['mcpu']}) ===\n{v['raw_excerpt']}\n")
    args.out_mca.write_text("\n".join(mca_txt), encoding="utf-8")

    # Merge into layout_root_cause_catalog.json if it exists
    existing = {}
    if args.out_json.exists():
        existing = json.loads(args.out_json.read_text(encoding="utf-8"))

    fast_offsets = [p["median_ns_per_4k_iter"] for p in phase_curve if not p["skx102_jcc_crosses_or_ends_32b"] and not p["loop_spans_two_64b_cache_lines"]]
    skx_offsets = [p["median_ns_per_4k_iter"] for p in phase_curve if p["skx102_jcc_crosses_or_ends_32b"]]
    split64_offsets = [p["median_ns_per_4k_iter"] for p in phase_curve if p["loop_spans_two_64b_cache_lines"]]

    existing["nop_64byte_phase_sweep"] = {
        "loop_size_bytes": 19,
        "cmp_jcc_offset_in_loop": [14, 19],
        "min_ns": min(p["median_ns_per_4k_iter"] for p in phase_curve),
        "max_ns": max(p["median_ns_per_4k_iter"] for p in phase_curve),
        "max_over_min_spread_pct": round(
            (max(p["median_ns_per_4k_iter"] for p in phase_curve) / min(p["median_ns_per_4k_iter"] for p in phase_curve) - 1.0) * 100.0, 2
        ),
        "clean_dsb_window_median_ns": round(statistics.median(fast_offsets), 3) if fast_offsets else 0.0,
        "skx102_32b_boundary_median_ns": round(statistics.median(skx_offsets), 3) if skx_offsets else 0.0,
        "split_64b_cache_line_median_ns": round(statistics.median(split64_offsets), 3) if split64_offsets else 0.0,
        "offsets_0_to_63": phase_curve,
    }
    existing["llvm_mca_profiles"] = mca_profiles
    args.out_json.write_text(json.dumps(existing, indent=2) + "\n", encoding="utf-8")
    print(f"Updated {args.out_json} and wrote {args.out_mca}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
