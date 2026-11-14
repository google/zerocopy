#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Benchmark runner and C telemetry extractor for X3 vs. K4 and Rust 1.99.1."""

import json
import re
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN_DIR = HERE / "x3_substrate"
OUT_JSON = HERE / "metrics.json"

K4_BASELINES = {
    "dom_ssa": {"rust_ms": 0.259, "k4_lean_ms": 1.261, "checksum": 2621001246},
    "hashmap_intern": {"rust_ms": 27.014, "k4_lean_ms": 141.192, "checksum": 3874992250000},
    "egraph_uf": {"rust_ms": 5.170, "k4_lean_ms": 44.105, "checksum": 25239800000},
    "regalloc": {"rust_ms": 0.377, "k4_lean_ms": 10.685, "checksum": 7813181233},
    "inst_encode": {"rust_ms": 6.390, "k4_lean_ms": 28.792, "checksum": 17000000},
    "ir_parser": {"rust_ms": 9.198, "k4_lean_ms": 76.809, "checksum": 2147484415133360},
}


def main() -> int:
    build_dir = LEAN_DIR / ".lake" / "build"
    if build_dir.exists():
        shutil.rmtree(build_dir)

    subprocess.run(
        ["anneal-lean-run", "--mode", "build", "--concurrency", "4", "--", "lake", "build", "BitSet64", "x3_bench"],
        cwd=str(LEAN_DIR), capture_output=True, text=True, check=True,
    )

    c_file = LEAN_DIR / ".lake" / "build" / "ir" / "X3Bench.c"
    c_text = c_file.read_text(encoding="utf-8")
    c_telemetry = {
        "c_lines": len(c_text.splitlines()),
        "c_bytes": c_file.stat().st_size,
        "lean_alloc_ctor_sites": len(re.findall(r"\blean_alloc_ctor\b", c_text)),
        "lean_inc_sites": len(re.findall(r"\blean_inc\b", c_text)),
        "lean_dec_sites": len(re.findall(r"\blean_dec\b", c_text)),
        "lean_is_exclusive_sites": len(re.findall(r"\blean_is_exclusive\b", c_text)),
        "lean_byte_array_fset_sites": len(re.findall(r"\blean_byte_array_fset\b|\blean_byte_array_set\b", c_text)),
        "k4_baseline_c_telemetry": {
            "c_lines": 9598,
            "lean_alloc_ctor_sites": 134,
            "lean_inc_sites": 261,
            "lean_dec_sites": 846,
            "lean_is_exclusive_sites": 47,
        },
    }

    proc = subprocess.run(
        ["/usr/bin/time", "-v", str(LEAN_DIR / ".lake" / "build" / "bin" / "x3_bench")],
        cwd=str(LEAN_DIR), capture_output=True, text=True, check=True,
    )
    x3_raw = json.loads(proc.stdout.strip())
    m_rss = re.search(r"Maximum resident set size \(kbytes\):\s*(\d+)", proc.stderr)
    rss_mb = round(int(m_rss.group(1)) / 1024.0, 2) if m_rss else 0.0

    mapping = [
        ("dom_ssa", "dom_ssa_soa"),
        ("hashmap_intern", "hashmap_flat"),
        ("egraph_uf", "egraph_uf_soa"),
        ("regalloc", "regalloc_unboxed"),
        ("inst_encode", "inst_encode_unboxed"),
        ("ir_parser", "ir_parser_unboxed"),
    ]
    comparisons = {}
    for k4_key, x3_key in mapping:
        base = K4_BASELINES[k4_key]
        cur = x3_raw[x3_key]
        assert cur["checksum"] == base["checksum"], f"Checksum mismatch on {k4_key}: {cur['checksum']} != {base['checksum']}"
        comparisons[k4_key] = {
            "rust_1_99_1_ms": base["rust_ms"],
            "k4_lean_ms": base["k4_lean_ms"],
            "x3_lean_ms": round(cur["median_ms"], 3),
            "x3_lean_p95_ms": round(cur["p95_ms"], 3),
            "k4_vs_rust_ratio_x": round(base["k4_lean_ms"] / base["rust_ms"], 2),
            "x3_vs_rust_ratio_x": round(cur["median_ms"] / base["rust_ms"], 2),
            "x3_speedup_over_k4_x": round(base["k4_lean_ms"] / cur["median_ms"], 2),
            "checksum": cur["checksum"],
        }

    summary = {
        "lean_version": "v4.34.1 (5045d0056413266e57c625dcd7c365b10e377c52)",
        "rust_version": "1.99.1 (58cf8f9c35b355199727627d07ae34a4e2846d67)",
        "peak_rss_mb": rss_mb,
        "k4_peak_rss_mb": 49.10,
        "rust_peak_rss_mb": 19.21,
        "c_codegen_telemetry": c_telemetry,
        "kernel_comparisons": comparisons,
    }

    OUT_JSON.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    shutil.rmtree(LEAN_DIR / ".lake", ignore_errors=True)
    print(json.dumps(summary, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
