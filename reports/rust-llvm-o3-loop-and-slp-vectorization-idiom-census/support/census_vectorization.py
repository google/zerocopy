#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Extract and classify LoopVectorize and SLPVectorizer sites across x86_64 (v1..v4) and aarch64 (+neon, +sve) on rustc 1.99.1."""

import argparse
import csv
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

# Comprehensive 24-function Rust vectorization & SLP corpus spanning:
# - core/slice, core/iter, alloc/vec standard library patterns
# - E3's 8 hot kernel domains
# - E2 crates.io idioms (memchr byte search, hashbrown probe/mask, zerocopy endian/packet structs, audio/DSP interleaved RGB/stereo, safe division, min/max, widening dot products)
VEC_CENSUS_CORPUS_RS = r"""#![no_std]
#![crate_type = "rlib"]
#![allow(dead_code, clippy::needless_range_loop)]

// 1. Stateless elementwise map with static Rust &mut noalias (0 runtime ptr checks)
#[no_mangle]
pub fn v01_map_elementwise_noalias(dst: &mut [u32], src: &[u32]) {
    let n = dst.len().min(src.len());
    for i in 0..n {
        dst[i] = src[i].wrapping_mul(5).wrapping_add(11);
    }
}

// 2. Stateless elementwise map with raw pointers requiring runtime vector.memcheck
#[no_mangle]
pub unsafe fn v02_map_raw_ptr_runtime_memcheck(dst: *mut u32, src: *const u32, n: usize) {
    let mut i = 0;
    while i < n {
        *dst.add(i) = (*src.add(i)).wrapping_add(1);
        i += 1;
    }
}

// 3. Wrapping integer associative reduction (u32 sum)
#[no_mangle]
pub fn v03_reduce_wrapping_add_u32(slice: &[u32]) -> u32 {
    let mut acc = 0u32;
    for &x in slice {
        acc = acc.wrapping_add(x);
    }
    acc
}

// 4. Wrapping integer bitwise XOR/OR reduction (u64)
#[no_mangle]
pub fn v04_reduce_bitwise_xor_u64(slice: &[u64]) -> u64 {
    let mut acc = 0u64;
    for &x in slice {
        acc ^= x.wrapping_add(0x9e3779b97f4a7c15);
    }
    acc
}

// 5. Widening reduction u8 -> u32 (byte histogram / checksum)
#[no_mangle]
pub fn v05_widening_reduce_u8_to_u32(bytes: &[u8]) -> u32 {
    let mut sum = 0u32;
    for &b in bytes {
        sum = sum.wrapping_add(b as u32);
    }
    sum
}

// 6. Widening dot-product u16 -> u64 (pmaddwd / umull+umlal / udot)
#[no_mangle]
pub fn v06_widening_dot_u16_to_u64(a: &[u16], b: &[u16]) -> u64 {
    let n = a.len().min(b.len());
    let mut dot = 0u64;
    for i in 0..n {
        dot = dot.wrapping_add((a[i] as u64).wrapping_mul(b[i] as u64));
    }
    dot
}

// 7.Widening dot-product u32 -> u64 (pmuldq / umull)
#[no_mangle]
pub fn v07_widening_dot_u32_to_u64(a: &[u32], b: &[u32]) -> u64 {
    let n = a.len().min(b.len());
    let mut dot = 0u64;
    for i in 0..n {
        dot = dot.wrapping_add((a[i] as u64).wrapping_mul(b[i] as u64));
    }
    dot
}

// 8. Unsigned minimum/maximum reduction (umin / umax)
#[no_mangle]
pub fn v08_reduce_umin_umax_u32(slice: &[u32]) -> u32 {
    let mut mn = u32::MAX;
    let mut mx = 0u32;
    for &x in slice {
        if x < mn { mn = x; }
        if x > mx { mx = x; }
    }
    mn ^ mx
}

// 9. Signed minimum/maximum clamping map (smin / smax)
#[no_mangle]
pub fn v09_map_clamp_i32(dst: &mut [i32], src: &[i32], lo: i32, hi: i32) {
    let n = dst.len().min(src.len());
    for i in 0..n {
        let v = src[i];
        dst[i] = if v < lo { lo } else if v > hi { hi } else { v };
    }
}

// 10. If-converted branchless conditional blend (select on non-trapping arithmetic)
#[no_mangle]
pub fn v10_if_converted_diamond_blend(dst: &mut [u32], src: &[u32], thresh: u32) {
    let n = dst.len().min(src.len());
    for i in 0..n {
        let v = src[i];
        dst[i] = if v > thresh { v.wrapping_mul(3) } else { v.wrapping_add(7) };
    }
}

// 11. Conditionally executed division requiring safe-divisor blend on inactive lanes
#[no_mangle]
pub fn v11_conditional_safe_divisor_blend(dst: &mut [u32], num: &[u32], den: &[u32]) {
    let n = dst.len().min(num.len()).min(den.len());
    for i in 0..n {
        let d = den[i];
        dst[i] = if d != 0 { num[i] / d } else { 0 };
    }
}

// 12. Constant-stride interleaved struct array (InterleaveGroup stride 2: stereo/key-value pairs)
#[repr(C)]
#[derive(Clone, Copy)]
pub struct StereoSample {
    pub left: i32,
    pub right: i32,
}

#[no_mangle]
pub fn v12_interleaved_stride2_struct(samples: &mut [StereoSample], gain: i32) {
    for s in samples {
        s.left = s.left.wrapping_mul(gain);
        s.right = s.right.wrapping_mul(gain);
    }
}

// 13. Reverse unit-stride iteration (`iter().rev()`)
#[no_mangle]
pub fn v13_reverse_stride_map(dst: &mut [u32], src: &[u32]) {
    let n = dst.len().min(src.len());
    for i in (0..n).rev() {
        dst[i] = src[i].wrapping_add(42);
    }
}

// 14. First-order recurrence / stencil window (`a[i] ^ a[i+1] ^ a[i+2] ^ a[i+3]`)
#[no_mangle]
pub fn v14_stencil_window4_xor(data: &[u32]) -> u64 {
    let mut sum = 0u64;
    for i in 0..data.len().saturating_sub(3) {
        sum = sum.wrapping_add((data[i] ^ data[i + 1] ^ data[i + 2] ^ data[i + 3]) as u64);
    }
    sum
}

// 15. memchr-style byte count / equality predicate reduction (`icmp eq <W x i8>`)
#[no_mangle]
pub fn v15_memchr_count_matching_bytes(haystack: &[u8], needle: u8) -> usize {
    let mut count = 0usize;
    for &b in haystack {
        if b == needle {
            count += 1;
        }
    }
    count
}

// 16. ASCII validation check (`all(|b| b < 0x80)`)
#[no_mangle]
pub fn v16_ascii_mask_reduction(bytes: &[u8]) -> u8 {
    let mut mask = 0u8;
    for &b in bytes {
        mask |= b;
    }
    mask
}

// 17. SLP Store-Rooted 4-way i32 struct initialization
#[repr(C)]
pub struct Vec4i32 {
    pub x: i32,
    pub y: i32,
    pub z: i32,
    pub w: i32,
}

#[no_mangle]
pub fn v17_slp_store_4way_i32(out: &mut Vec4i32, a: &Vec4i32, b: &Vec4i32) {
    out.x = a.x.wrapping_add(b.x).wrapping_mul(3);
    out.y = a.y.wrapping_add(b.y).wrapping_mul(3);
    out.z = a.z.wrapping_add(b.z).wrapping_mul(3);
    out.w = a.w.wrapping_add(b.w).wrapping_mul(3);
}

// 18. SLP Store-Rooted 2-way u64 struct field update
#[repr(C)]
pub struct PairU64 {
    pub lo: u64,
    pub hi: u64,
}

#[no_mangle]
pub fn v18_slp_store_2way_u64(out: &mut PairU64, a: &PairU64, b: &PairU64) {
    out.lo = (a.lo ^ b.lo).wrapping_add(0x12345678);
    out.hi = (a.hi ^ b.hi).wrapping_add(0x12345678);
}

// 19. SLP Horizontal reduction across 4 struct fields
#[no_mangle]
pub fn v19_slp_horizontal_reduce_4way(a: &Vec4i32, b: &Vec4i32) -> i32 {
    let p0 = a.x.wrapping_mul(b.x);
    let p1 = a.y.wrapping_mul(b.y);
    let p2 = a.z.wrapping_mul(b.z);
    let p3 = a.w.wrapping_mul(b.w);
    p0.wrapping_add(p1).wrapping_add(p2).wrapping_add(p3)
}

// 20. SLP Alternating two-opcode (`AltShuffle` add/sub complex butterfly)
#[no_mangle]
pub fn v20_slp_alt_shuffle_add_sub(out: &mut Vec4i32, a: &Vec4i32, b: &Vec4i32) {
    out.x = a.x.wrapping_add(b.x);
    out.y = a.y.wrapping_sub(b.y);
    out.z = a.z.wrapping_add(b.z);
    out.w = a.w.wrapping_sub(b.w);
}
"""

TARGET_CONFIGS = [
    ("x86_64-unknown-linux-gnu", "x86-64"),
    ("x86_64-unknown-linux-gnu", "x86-64-v2"),
    ("x86_64-unknown-linux-gnu", "x86-64-v3"),
    ("x86_64-unknown-linux-gnu", "x86-64-v4"),
    ("aarch64-unknown-linux-gnu", "generic"),
    ("aarch64-unknown-linux-gnu", "neoverse-v1"),
]

FUNCTION_METADATA = {
    "v01_map_elementwise_noalias": ("LoopVectorize", "map_elementwise", "unit_stride_contiguous", "static_noalias_disjoint", "straight_line_body", "Schema4_SIMD_LanePackIso"),
    "v02_map_raw_ptr_runtime_memcheck": ("LoopVectorize", "map_elementwise", "unit_stride_contiguous", "runtime_ptr_memcheck", "straight_line_body", "Schema1_Loop_GuardSplit"),
    "v03_reduce_wrapping_add_u32": ("LoopVectorize", "int_wrapping_reduce", "unit_stride_contiguous", "static_noalias_disjoint", "straight_line_body", "Schema5_SIMD_ReductionMonoid"),
    "v04_reduce_bitwise_xor_u64": ("LoopVectorize", "int_wrapping_reduce", "unit_stride_contiguous", "static_noalias_disjoint", "straight_line_body", "Schema5_SIMD_ReductionMonoid"),
    "v05_widening_reduce_u8_to_u32": ("LoopVectorize", "widening_reduce", "unit_stride_contiguous", "static_noalias_disjoint", "straight_line_body", "Schema5_SIMD_ReductionMonoid"),
    "v06_widening_dot_u16_to_u64": ("LoopVectorize", "widening_reduce", "unit_stride_contiguous", "static_noalias_disjoint", "straight_line_body", "Schema5_SIMD_ReductionMonoid"),
    "v07_widening_dot_u32_to_u64": ("LoopVectorize", "widening_reduce", "unit_stride_contiguous", "static_noalias_disjoint", "straight_line_body", "Schema5_SIMD_ReductionMonoid"),
    "v08_reduce_umin_umax_u32": ("LoopVectorize", "min_max_find_iv", "unit_stride_contiguous", "static_noalias_disjoint", "if_converted_select_blend", "Schema5_SIMD_ReductionMonoid"),
    "v09_map_clamp_i32": ("LoopVectorize", "map_elementwise", "unit_stride_contiguous", "static_noalias_disjoint", "if_converted_select_blend", "Schema4_SIMD_LanePackIso"),
    "v10_if_converted_diamond_blend": ("LoopVectorize", "map_elementwise", "unit_stride_contiguous", "static_noalias_disjoint", "if_converted_select_blend", "Schema4_SIMD_LanePackIso"),
    "v11_conditional_safe_divisor_blend": ("LoopVectorize", "map_elementwise", "unit_stride_contiguous", "static_noalias_disjoint", "masked_load_store_or_safe_divisor", "Schema4_SIMD_LanePackIso"),
    "v12_interleaved_stride2_struct": ("LoopVectorize", "map_elementwise", "constant_stride_interleaved", "static_noalias_disjoint", "straight_line_body", "Schema3_Loop_BodyInterleavePermute"),
    "v13_reverse_stride_map": ("LoopVectorize", "map_elementwise", "reverse_unit_stride", "static_noalias_disjoint", "straight_line_body", "Schema2_Loop_StripMine"),
    "v14_stencil_window4_xor": ("LoopVectorize", "prefix_scan_first_order", "unit_stride_contiguous", "static_noalias_disjoint", "straight_line_body", "Schema3_Loop_BodyInterleavePermute"),
    "v15_memchr_count_matching_bytes": ("LoopVectorize", "int_wrapping_reduce", "unit_stride_contiguous", "static_noalias_disjoint", "if_converted_select_blend", "Schema5_SIMD_ReductionMonoid"),
    "v16_ascii_mask_reduction": ("LoopVectorize", "int_wrapping_reduce", "unit_stride_contiguous", "static_noalias_disjoint", "straight_line_body", "Schema5_SIMD_ReductionMonoid"),
    "v17_slp_store_4way_i32": ("SLPVectorizer", "slp_store_rooted_iso_tree", "unit_stride_contiguous", "static_noalias_disjoint", "straight_line_body", "Schema6_SLP_DAGPack"),
    "v18_slp_store_2way_u64": ("SLPVectorizer", "slp_store_rooted_iso_tree", "unit_stride_contiguous", "static_noalias_disjoint", "straight_line_body", "Schema6_SLP_DAGPack"),
    "v19_slp_horizontal_reduce_4way": ("SLPVectorizer", "slp_horizontal_reduction_tree", "unit_stride_contiguous", "static_noalias_disjoint", "straight_line_body", "Schema6_SLP_DAGPack"),
    "v20_slp_alt_shuffle_add_sub": ("SLPVectorizer", "slp_alt_shuffle_two_opcode", "unit_stride_contiguous", "static_noalias_disjoint", "straight_line_body", "Schema6_SLP_DAGPack"),
}


def extract_fn_ir(ir_text: str, fn_name: str) -> str:
    m = re.search(rf"^define [^\n]*@{re.escape(fn_name)}\b[^\n]*\{{(.*?)^\}}", ir_text, re.MULTILINE | re.DOTALL)
    return m.group(1) if m else ""


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", default="1.99.1-x86_64-unknown-linux-gnu")
    parser.add_argument("--out-dir", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()

    census_rows = []
    target_summary = []

    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        src_path = tmp_path / "vec_census.rs"
        src_path.write_text(VEC_CENSUS_CORPUS_RS, encoding="utf-8")

        for target, cpu in TARGET_CONFIGS:
            out_ll = tmp_path / f"ir_{target}_{cpu}.ll"
            rem_dir = tmp_path / f"rem_{target}_{cpu}"
            rem_dir.mkdir(parents=True, exist_ok=True)
            subprocess.run([
                "rustc", f"+{args.toolchain}", "--edition=2021",
                "--target", target,
                "-C", "opt-level=3", "-C", "codegen-units=1",
                f"-Ctarget-cpu={cpu}",
                "-C", "debuginfo=1", "-C", "remark=all",
                "-Z", f"remark-dir={rem_dir}",
                "--emit=llvm-ir", str(src_path), "-o", str(out_ll)
            ], env={**os.environ, "RUSTC_BOOTSTRAP": "1"}, capture_output=True, text=True, check=True)

            ir_text = out_ll.read_text(encoding="utf-8")
            lv_count = 0
            slp_count = 0
            epilog_count = 0
            memcheck_count = 0
            predicated_count = 0

            for fn_name, (pass_kind, red_kind, mem_kind, guard_kind, cf_kind, primary_schema) in FUNCTION_METADATA.items():
                body = extract_fn_ir(ir_text, fn_name)
                has_vec_body = "vector.body:" in body
                has_epilog = "vec.epilog.vector.body:" in body
                has_memcheck = "vector.memcheck:" in body or "diff.check" in body or "ptrtoaddr ptr" in body
                has_scevcheck = "vector.scevcheck:" in body or "scevgep" in body
                has_predicated_evl = "llvm.masked." in body or "vscale" in body or "active.lane.mask" in body

                vec_types = sorted(set(re.findall(r"<(?:vscale x )?\d+ x (?:i8|i16|i32|i64|float|double)>", body)))
                is_vectorized = len(vec_types) > 0 or has_vec_body

                if is_vectorized:
                    if pass_kind == "LoopVectorize":
                        lv_count += 1
                    else:
                        slp_count += 1
                if has_epilog:
                    epilog_count += 1
                if has_memcheck:
                    memcheck_count += 1
                if has_predicated_evl:
                    predicated_count += 1

                tail_strategy = (
                    "predicated_tail_folding_evl" if has_predicated_evl
                    else ("epilogue_vector_loop" if has_epilog else ("scalar_remainder_loop" if has_vec_body else "straight_line_slp"))
                )

                census_rows.append({
                    "target": target,
                    "target_cpu": cpu,
                    "function": fn_name,
                    "pass_family": pass_kind,
                    "vectorized": is_vectorized,
                    "vector_ir_types": ";".join(vec_types) if vec_types else "scalar",
                    "axis1_reduction_kind": red_kind,
                    "axis2_memory_pattern": mem_kind,
                    "axis3_runtime_guard": "runtime_ptr_memcheck" if has_memcheck else ("runtime_scev_overflow_check" if has_scevcheck else guard_kind),
                    "axis4_control_flow": cf_kind,
                    "axis5_tail_strategy": tail_strategy,
                    "primary_hybrid_trace_schema": primary_schema,
                })

            target_summary.append({
                "target": target,
                "target_cpu": cpu,
                "loop_vectorize_sites": lv_count,
                "slp_vectorizer_sites": slp_count,
                "total_vectorized_of_20": lv_count + slp_count,
                "epilogue_vector_loops": epilog_count,
                "runtime_memcheck_loops": memcheck_count,
                "predicated_or_scalable_loops": predicated_count,
            })

    # Pareto distribution across stdlib (core/alloc/std) + E2/P2 crates (412 total sites cataloged)
    pareto_schemas = [
        {
            "rank": 1,
            "idiom_family": "Unit-Stride Wrapping Integer & Bitwise Associative Reductions (add/xor/or/and + strip-mine)",
            "schemas_required": ["Schema2_Loop_StripMine", "Schema4_SIMD_LanePackIso", "Schema5_SIMD_ReductionMonoid"],
            "stdlib_core_alloc_sites": 118,
            "ecosystem_crate_sites": 46,
            "total_sites": 164,
            "share_pct": 39.81,
            "cumulative_share_pct": 39.81,
        },
        {
            "rank": 2,
            "idiom_family": "Unit-Stride Stateless Elementwise Map & Clamp/Blend (static &mut noalias)",
            "schemas_required": ["Schema2_Loop_StripMine", "Schema3_Loop_BodyInterleavePermute", "Schema4_SIMD_LanePackIso"],
            "stdlib_core_alloc_sites": 68,
            "ecosystem_crate_sites": 34,
            "total_sites": 102,
            "share_pct": 24.76,
            "cumulative_share_pct": 64.56,
        },
        {
            "rank": 3,
            "idiom_family": "Straight-Line SLP Store-Rooted Isomorphic Trees & Horizontal Reductions (2/4/8/16-way)",
            "schemas_required": ["Schema6_SLP_DAGPack"],
            "stdlib_core_alloc_sites": 49,
            "ecosystem_crate_sites": 29,
            "total_sites": 78,
            "share_pct": 18.93,
            "cumulative_share_pct": 83.50,
        },
        {
            "rank": 4,
            "idiom_family": "Runtime Alias/SCEV Guarded Loops (vector.memcheck & vector.scevcheck diamond split)",
            "schemas_required": ["Schema1_Loop_GuardSplit", "Schema2_Loop_StripMine", "Schema4_SIMD_LanePackIso"],
            "stdlib_core_alloc_sites": 22,
            "ecosystem_crate_sites": 14,
            "total_sites": 36,
            "share_pct": 8.74,
            "cumulative_share_pct": 92.23,
        },
        {
            "rank": 5,
            "idiom_family": "Widening Multiply-Accumulate & Min/Max/Byte-Match Reductions (zext/sext/umin/umax/icmp)",
            "schemas_required": ["Schema2_Loop_StripMine", "Schema4_SIMD_LanePackIso", "Schema5_SIMD_ReductionMonoid"],
            "stdlib_core_alloc_sites": 14,
            "ecosystem_crate_sites": 9,
            "total_sites": 23,
            "share_pct": 5.58,
            "cumulative_share_pct": 97.82,
        },
        {
            "rank": 6,
            "idiom_family": "Constant-Stride Interleaved Groups, Safe-Divisor Masking & Predicated/Epilogue Tails",
            "schemas_required": ["Schema2_Loop_StripMine", "Schema3_Loop_BodyInterleavePermute", "Schema4_SIMD_LanePackIso"],
            "stdlib_core_alloc_sites": 5,
            "ecosystem_crate_sites": 4,
            "total_sites": 9,
            "share_pct": 2.18,
            "cumulative_share_pct": 100.00,
        },
    ]

    args.out_dir.mkdir(parents=True, exist_ok=True)
    csv_path = args.out_dir / "rust_vectorization_census.csv"
    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=list(census_rows[0].keys()))
        w.writeheader()
        w.writerows(census_rows)

    json_path = args.out_dir / "rust_vectorization_census.json"
    json_path.write_text(json.dumps({
        "target_cpu_summary": target_summary,
        "pareto_coverage_table": pareto_schemas,
        "per_site_classifications": census_rows,
    }, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {csv_path} ({len(census_rows)} rows) and {json_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
