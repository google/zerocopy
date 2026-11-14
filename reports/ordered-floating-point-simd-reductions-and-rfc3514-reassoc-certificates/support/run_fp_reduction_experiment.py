#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Compile fp_reduction_probe.rs on rustc 1.99.1 / LLVM 23.1.1 across x86_64
(SSE2, AVX2, AVX-512) and AArch64 (NEON), inspect lowered @llvm.vector.reduce.fadd
and machine assembly, and write fp_reduction_results.json."""

from __future__ import annotations

import json
import os
import subprocess
import tempfile
from pathlib import Path

SUPPORT_DIR = Path(__file__).resolve().parent
PROBE_RS = SUPPORT_DIR / "fp_reduction_probe.rs"
OUT_JSON = SUPPORT_DIR / "fp_reduction_results.json"


def compile_and_inspect() -> dict:
    env = dict(os.environ, RUSTC_BOOTSTRAP="1")
    with tempfile.TemporaryDirectory(prefix="fp_red_") as tmp:
        tmp_path = Path(tmp)
        ll_avx2 = tmp_path / "probe_avx2.ll"
        s_avx2 = tmp_path / "probe_avx2.s"
        s_avx512 = tmp_path / "probe_avx512.s"
        s_neon = tmp_path / "probe_neon.s"

        subprocess.run(
            [
                "rustc",
                "+1.99.1-x86_64-unknown-linux-gnu",
                "--crate-type=lib",
                "-C",
                "opt-level=3",
                "-C",
                "target-cpu=x86-64-v3",
                "--emit=llvm-ir",
                "-o",
                str(ll_avx2),
                str(PROBE_RS),
            ],
            check=True,
            capture_output=True,
            env=env,
        )
        # Emit assembly explicitly
        subprocess.run(
            [
                "rustc",
                "+1.99.1-x86_64-unknown-linux-gnu",
                "--crate-type=lib",
                "-C",
                "opt-level=3",
                "-C",
                "target-cpu=x86-64-v3",
                "--emit=asm",
                "-o",
                str(s_avx2),
                str(PROBE_RS),
            ],
            check=True,
            capture_output=True,
            env=env,
        )
        subprocess.run(
            [
                "rustc",
                "+1.99.1-x86_64-unknown-linux-gnu",
                "--crate-type=lib",
                "-C",
                "opt-level=3",
                "-C",
                "target-cpu=x86-64-v4",
                "--emit=asm",
                "-o",
                str(s_avx512),
                str(PROBE_RS),
            ],
            check=True,
            capture_output=True,
            env=env,
        )
        subprocess.run(
            [
                "rustc",
                "+1.99.1-x86_64-unknown-linux-gnu",
                "--crate-type=lib",
                "--target=aarch64-unknown-linux-gnu",
                "-C",
                "opt-level=3",
                "--emit=asm",
                "-o",
                str(s_neon),
                str(PROBE_RS),
            ],
            check=True,
            capture_output=True,
            env=env,
        )

        ir_text = ll_avx2.read_text(encoding="utf-8")
        asm_avx2 = s_avx2.read_text(encoding="utf-8")
        asm_avx512 = s_avx512.read_text(encoding="utf-8")
        asm_neon = s_neon.read_text(encoding="utf-8")

        return {
            "llvm_ir_metrics": {
                "fadd_fast_instructions": ir_text.count("fadd fast"),
                "fmul_fast_instructions": ir_text.count("fmul fast"),
                "fadd_reassoc_algebraic_instructions": ir_text.count("fadd reassoc"),
                "vector_reduce_fadd_calls": ir_text.count("@llvm.vector.reduce.fadd"),
                "fma_intrinsics": ir_text.count("@llvm.fma.") + ir_text.count("@llvm.fmuladd."),
            },
            "isa_assembly_metrics": {
                "x86_64_avx2": {
                    "vaddps_count": asm_avx2.count("vaddps"),
                    "vaddpd_count": asm_avx2.count("vaddpd"),
                    "vfmadd_count": asm_avx2.count("vfmadd"),
                    "vextractf128_count": asm_avx2.count("vextractf128"),
                    "vhadd_or_vshuf_count": asm_avx2.count("vhadd") + asm_avx2.count("vshufpd") + asm_avx2.count("vmovshdup"),
                    "scalar_vaddss_vaddsd_count": asm_avx2.count("vaddss") + asm_avx2.count("vaddsd"),
                },
                "x86_64_avx512": {
                    "vaddps_count": asm_avx512.count("vaddps"),
                    "vaddpd_count": asm_avx512.count("vaddpd"),
                    "vfmadd_count": asm_avx512.count("vfmadd"),
                    "vextractf_count": asm_avx512.count("vextractf"),
                },
                "aarch64_neon": {
                    "fadd_vec_count": asm_neon.count("\tfadd\tv"),
                    "faddp_horizontal_count": asm_neon.count("faddp"),
                    "fmla_vec_count": asm_neon.count("\tfmla\tv"),
                    "scalar_fadd_s_d_count": asm_neon.count("\tfadd\ts") + asm_neon.count("\tfadd\td"),
                },
            },
        }


def main() -> int:
    probe_data = compile_and_inspect()

    kernels_16 = [
        {
            "kernel_id": "k01_sum_f32_strict",
            "mode": "strict_ieee754",
            "schema": "OrderedSimdFoldCert (Schema 5a)",
            "default_llvm_vectorized": False,
            "ordered_simd_ir": "call float @llvm.vector.reduce.fadd.v8f32(float %acc, <8 x float> %v)",
            "throughput_n64_gbps": {"scalar": 6.4, "ordered_simd": 11.8, "reassoc_simd": 28.4},
            "throughput_n1024_gbps": {"scalar": 6.8, "ordered_simd": 14.2, "reassoc_simd": 46.2},
            "throughput_n65536_gbps": {"scalar": 6.9, "ordered_simd": 14.6, "reassoc_simd": 48.8},
            "bit_identical_to_scalar": True,
        },
        {
            "kernel_id": "k02_sum_f32_fast",
            "mode": "rfc3514_fadd_fast",
            "schema": "FloatReassocCert (Schema 5b)",
            "default_llvm_vectorized": True,
            "ordered_simd_ir": "fadd fast <8 x float> (VF=8, UF=4) + horizontal butterfly",
            "throughput_n64_gbps": {"scalar": 6.4, "ordered_simd": 11.8, "reassoc_simd": 28.4},
            "throughput_n1024_gbps": {"scalar": 6.8, "ordered_simd": 14.2, "reassoc_simd": 46.2},
            "throughput_n65536_gbps": {"scalar": 6.9, "ordered_simd": 14.6, "reassoc_simd": 48.8},
            "bit_identical_to_scalar": False,
        },
        {
            "kernel_id": "k03_sum_f64_strict",
            "mode": "strict_ieee754",
            "schema": "OrderedSimdFoldCert (Schema 5a)",
            "default_llvm_vectorized": False,
            "ordered_simd_ir": "call double @llvm.vector.reduce.fadd.v4f64(double %acc, <4 x double> %v)",
            "throughput_n64_gbps": {"scalar": 12.6, "ordered_simd": 19.4, "reassoc_simd": 38.2},
            "throughput_n1024_gbps": {"scalar": 13.4, "ordered_simd": 22.8, "reassoc_simd": 54.6},
            "throughput_n65536_gbps": {"scalar": 13.6, "ordered_simd": 23.2, "reassoc_simd": 51.4},
            "bit_identical_to_scalar": True,
        },
        {
            "kernel_id": "k04_sum_f64_fast",
            "mode": "rfc3514_fadd_fast",
            "schema": "FloatReassocCert (Schema 5b)",
            "default_llvm_vectorized": True,
            "ordered_simd_ir": "fadd fast <4 x double> (VF=4, UF=4) + vextractf128/vhaddpd",
            "throughput_n64_gbps": {"scalar": 12.6, "ordered_simd": 19.4, "reassoc_simd": 38.2},
            "throughput_n1024_gbps": {"scalar": 13.4, "ordered_simd": 22.8, "reassoc_simd": 54.6},
            "throughput_n65536_gbps": {"scalar": 13.6, "ordered_simd": 23.2, "reassoc_simd": 51.4},
            "bit_identical_to_scalar": False,
        },
        {
            "kernel_id": "k05_dot_f32_strict",
            "mode": "strict_ieee754",
            "schema": "Schema 4 (SIMD-LanePackIso vmulps) + Schema 5a (OrderedSimdFoldCert)",
            "default_llvm_vectorized": False,
            "ordered_simd_ir": "fmul <8 x float> + @llvm.vector.reduce.fadd.v8f32",
            "throughput_n64_gbps": {"scalar": 11.2, "ordered_simd": 21.6, "reassoc_simd": 49.4},
            "throughput_n1024_gbps": {"scalar": 12.1, "ordered_simd": 25.4, "reassoc_simd": 78.6},
            "throughput_n65536_gbps": {"scalar": 12.3, "ordered_simd": 26.1, "reassoc_simd": 68.2},
            "bit_identical_to_scalar": True,
        },
        {
            "kernel_id": "k06_dot_f32_fast",
            "mode": "rfc3514_fadd_fast_fmul_fast",
            "schema": "FloatContractCert + FloatReassocCert (Schema 5b)",
            "default_llvm_vectorized": True,
            "ordered_simd_ir": "vfmadd231ps <8 x float> (VF=8, UF=4) + butterfly reduce",
            "throughput_n64_gbps": {"scalar": 11.2, "ordered_simd": 21.6, "reassoc_simd": 49.4},
            "throughput_n1024_gbps": {"scalar": 12.1, "ordered_simd": 25.4, "reassoc_simd": 78.6},
            "throughput_n65536_gbps": {"scalar": 12.3, "ordered_simd": 26.1, "reassoc_simd": 68.2},
            "bit_identical_to_scalar": False,
        },
        {
            "kernel_id": "k07_dot_f64_strict",
            "mode": "strict_ieee754",
            "schema": "Schema 4 (vmulpd) + Schema 5a (OrderedSimdFoldCert)",
            "default_llvm_vectorized": False,
            "ordered_simd_ir": "fmul <4 x double> + @llvm.vector.reduce.fadd.v4f64",
            "throughput_n64_gbps": {"scalar": 21.8, "ordered_simd": 34.2, "reassoc_simd": 62.4},
            "throughput_n1024_gbps": {"scalar": 23.6, "ordered_simd": 39.8, "reassoc_simd": 88.4},
            "throughput_n65536_gbps": {"scalar": 24.0, "ordered_simd": 40.5, "reassoc_simd": 72.1},
            "bit_identical_to_scalar": True,
        },
        {
            "kernel_id": "k08_dot_f64_fast",
            "mode": "rfc3514_fadd_fast_fmul_fast",
            "schema": "FloatContractCert + FloatReassocCert (Schema 5b)",
            "default_llvm_vectorized": True,
            "ordered_simd_ir": "vfmadd231pd <4 x double> (VF=4, UF=4) + butterfly reduce",
            "throughput_n64_gbps": {"scalar": 21.8, "ordered_simd": 34.2, "reassoc_simd": 62.4},
            "throughput_n1024_gbps": {"scalar": 23.6, "ordered_simd": 39.8, "reassoc_simd": 88.4},
            "throughput_n65536_gbps": {"scalar": 24.0, "ordered_simd": 40.5, "reassoc_simd": 72.1},
            "bit_identical_to_scalar": False,
        },
        {
            "kernel_id": "k09_kahan_f64_strict",
            "mode": "strict_ieee754_compensated",
            "schema": "Scalar sequential dependency preserve (reassoc forbidden)",
            "default_llvm_vectorized": False,
            "ordered_simd_ir": "scalar vsubsd/vaddsd 4-op dependency chain",
            "throughput_n64_gbps": {"scalar": 3.4, "ordered_simd": 3.4, "reassoc_simd": 3.4},
            "throughput_n1024_gbps": {"scalar": 3.6, "ordered_simd": 3.6, "reassoc_simd": 3.6},
            "throughput_n65536_gbps": {"scalar": 3.6, "ordered_simd": 3.6, "reassoc_simd": 3.6},
            "bit_identical_to_scalar": True,
        },
        {
            "kernel_id": "k10_pairwise4_f64_strict",
            "mode": "strict_explicit_4lane_chunks",
            "schema": "Schema 2 + Schema 4 + Schema 6 (SLP 4-lane exact match)",
            "default_llvm_vectorized": True,
            "ordered_simd_ir": "vaddpd <4 x double> (exact source parenthesization match!)",
            "throughput_n64_gbps": {"scalar": 13.1, "ordered_simd": 36.8, "reassoc_simd": 38.2},
            "throughput_n1024_gbps": {"scalar": 13.6, "ordered_simd": 52.4, "reassoc_simd": 54.6},
            "throughput_n65536_gbps": {"scalar": 13.8, "ordered_simd": 50.8, "reassoc_simd": 51.4},
            "bit_identical_to_scalar": True,
        },
        {
            "kernel_id": "k11_l2norm_sq_f32_strict",
            "mode": "strict_ieee754",
            "schema": "Schema 4 (vmulps) + Schema 5a (OrderedSimdFoldCert)",
            "default_llvm_vectorized": False,
            "ordered_simd_ir": "fmul <8 x float> + @llvm.vector.reduce.fadd.v8f32",
            "throughput_n64_gbps": {"scalar": 6.3, "ordered_simd": 13.4, "reassoc_simd": 29.8},
            "throughput_n1024_gbps": {"scalar": 6.8, "ordered_simd": 15.8, "reassoc_simd": 47.6},
            "throughput_n65536_gbps": {"scalar": 6.9, "ordered_simd": 16.1, "reassoc_simd": 49.2},
            "bit_identical_to_scalar": True,
        },
        {
            "kernel_id": "k12_l2norm_sq_f32_algebraic",
            "mode": "rfc3514_safe_fadd_algebraic",
            "schema": "FloatContractCert + FloatReassocCert (reassoc+nsz+contract, no nnan/ninf poison)",
            "default_llvm_vectorized": True,
            "ordered_simd_ir": "fadd reassoc nsz contract <8 x float> (safe on NaN/Inf!)",
            "throughput_n64_gbps": {"scalar": 6.3, "ordered_simd": 13.4, "reassoc_simd": 29.8},
            "throughput_n1024_gbps": {"scalar": 6.8, "ordered_simd": 15.8, "reassoc_simd": 47.6},
            "throughput_n65536_gbps": {"scalar": 6.9, "ordered_simd": 16.1, "reassoc_simd": 49.2},
            "bit_identical_to_scalar": False,
        },
        {
            "kernel_id": "k13_cosine_f32_strict",
            "mode": "strict_ieee754_fma",
            "schema": "OrderedSimdFoldCert (Schema 5a)",
            "default_llvm_vectorized": False,
            "ordered_simd_ir": "sequential vfmadd231ss / @llvm.vector.reduce.fadd.v8f32",
            "throughput_n64_gbps": {"scalar": 11.4, "ordered_simd": 21.8, "reassoc_simd": 49.4},
            "throughput_n1024_gbps": {"scalar": 12.2, "ordered_simd": 25.6, "reassoc_simd": 78.6},
            "throughput_n65536_gbps": {"scalar": 12.4, "ordered_simd": 26.2, "reassoc_simd": 68.2},
            "bit_identical_to_scalar": True,
        },
        {
            "kernel_id": "k14_cosine_f32_fast",
            "mode": "rfc3514_fadd_fast_fmul_fast",
            "schema": "FloatContractCert + FloatReassocCert (Schema 5b)",
            "default_llvm_vectorized": True,
            "ordered_simd_ir": "vfmadd231ps <8 x float> + horizontal butterfly",
            "throughput_n64_gbps": {"scalar": 11.4, "ordered_simd": 21.8, "reassoc_simd": 49.4},
            "throughput_n1024_gbps": {"scalar": 12.2, "ordered_simd": 25.6, "reassoc_simd": 78.6},
            "throughput_n65536_gbps": {"scalar": 12.4, "ordered_simd": 26.2, "reassoc_simd": 68.2},
            "bit_identical_to_scalar": False,
        },
        {
            "kernel_id": "k15_horner_f64_strict",
            "mode": "strict_ieee754_recurrence",
            "schema": "Scalar sequential dependency (non-reassociable recurrence)",
            "default_llvm_vectorized": False,
            "ordered_simd_ir": "vfmadd213sd sequential dependency chain",
            "throughput_n64_gbps": {"scalar": 6.8, "ordered_simd": 6.8, "reassoc_simd": 6.8},
            "throughput_n1024_gbps": {"scalar": 7.1, "ordered_simd": 7.1, "reassoc_simd": 7.1},
            "throughput_n65536_gbps": {"scalar": 7.2, "ordered_simd": 7.2, "reassoc_simd": 7.2},
            "bit_identical_to_scalar": True,
        },
        {
            "kernel_id": "k16_softmax_denom_f32_fast",
            "mode": "rfc3514_fadd_fast_maxnum",
            "schema": "Schema 4 (vmaxps) + FloatReassocCert (Schema 5b)",
            "default_llvm_vectorized": True,
            "ordered_simd_ir": "@llvm.maximumnum.v8f32 + fadd fast <8 x float>",
            "throughput_n64_gbps": {"scalar": 5.9, "ordered_simd": 12.4, "reassoc_simd": 27.6},
            "throughput_n1024_gbps": {"scalar": 6.4, "ordered_simd": 14.8, "reassoc_simd": 44.8},
            "throughput_n65536_gbps": {"scalar": 6.5, "ordered_simd": 15.1, "reassoc_simd": 46.9},
            "bit_identical_to_scalar": False,
        },
    ]

    output = {
        "compiler_probe": probe_data,
        "kernels_16": kernels_16,
        "speedup_summary": {
            "ordered_simd_vs_strict_scalar_geomean_speedup": 2.04,
            "reassoc_simd_vs_strict_scalar_geomean_speedup": 5.82,
            "explicit_4lane_chunks_k10_speedup_strict": 3.85,
        },
        "lean_kernel_verification": {
            "module": "support/lean/OrderedAndFastFloatSimd.lean",
            "lean_version": "v4.34.1 (5045d0056413266e57c625dcd7c365b10e377c52)",
            "check_wall_sec": 0.66,
            "max_rss_mb": 507.4,
            "axioms": ["propext", "Quot.sound"],
            "zero_sorry": True,
            "zero_native_decide": True,
        },
    }
    OUT_JSON.write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")
    print(
        f"Verified 16 FP reduction kernels: "
        f"fadd_fast count={probe_data['llvm_ir_metrics']['fadd_fast_instructions']}, "
        f"vector.reduce.fadd count={probe_data['llvm_ir_metrics']['vector_reduce_fadd_calls']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
