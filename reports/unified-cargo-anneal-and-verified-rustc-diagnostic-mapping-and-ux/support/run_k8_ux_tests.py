#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""End-to-end verification suite for `K8_` (`run_k8_ux_tests.py`).

Tests:
  1. Compiles a real Rust test module under `rustc +1.99.1 --emit=mir` before and after
     inserting 50 lines of leading doc/block comments (`+50` line shift).
  2. Verifies that `extract_canonical_mir_and_sideband` produces the **exact same**
     `MirItemKey` SHA-256 digest (`100.0%` cache hit rate) while shifting every
     `StmtOrd` entry in `SidebandSpanTable` by `+50` lines.
  3. Emits all 6 canonical diagnostic scenarios (`W_ANNEAL_0101`..`E_ANNEAL_0301`) in
     `rustc` human format, `rustc` JSON format (`sample_diagnostics.json`), and
     OASIS SARIF 2.1.0 format (`sample_audit.sarif.json`), validating schema invariants.
  4. Benchmarks `.anneal-repro` minidump generation (`< 5 ms`).
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import tempfile
from pathlib import Path
from typing import Any

import anneal_diag_engine


BASE_RUST_SRC = """pub fn compute_strided_checksum(slice: &[u64], stride: usize) -> u64 {
    let mut acc = 0u64;
    let mut i = 0usize;
    while i < slice.len() {
        acc = acc.wrapping_add(slice[i]).wrapping_mul(stride as u64 | 1);
        i += 1;
    }
    acc
}
"""


def run_live_rustc_line_shift_test() -> dict[str, Any]:
    comment_prefix = "\n".join(f"// Leading documentation comment line {k}" for k in range(1, 51)) + "\n"
    shifted_rust_src = comment_prefix + BASE_RUST_SRC

    base_env = dict(os.environ)
    base_env["PATH"] = f"/usr/local/google/home/joshlf/.cargo/bin:{base_env.get('PATH', '')}"
    base_env["RUSTC_BOOTSTRAP"] = "1"

    with tempfile.TemporaryDirectory() as td:
        tdir = Path(td)
        f_orig = tdir / "orig.rs"
        f_shift = tdir / "shifted.rs"
        m_orig = tdir / "orig.mir"
        m_shift = tdir / "shifted.mir"

        f_orig.write_text(BASE_RUST_SRC, encoding="utf-8")
        f_shift.write_text(shifted_rust_src, encoding="utf-8")

        for rs_f, mir_f in [(f_orig, m_orig), (f_shift, m_shift)]:
            subprocess.run(
                [
                    "rustc",
                    "+1.99.1",
                    "--crate-type=lib",
                    "--edition=2021",
                    "-Copt-level=3",
                    "-Zmir-include-spans",
                    "--emit=mir",
                    "-o",
                    str(mir_f),
                    str(rs_f),
                ],
                env=base_env,
                check=True,
                capture_output=True,
                text=True,
            )

        key_orig, spans_orig = anneal_diag_engine.extract_canonical_mir_and_sideband(
            m_orig.read_text(encoding="utf-8"), "src/checksum.rs"
        )
        key_shift, spans_shift = anneal_diag_engine.extract_canonical_mir_and_sideband(
            m_shift.read_text(encoding="utf-8"), "src/checksum.rs"
        )

        # Verify every local StmtOrd in src/checksum.rs has lo_line + 50 == spans_shift[ord].lo_line
        # while cross-crate inlined statements from `core` preserve their exact `core` spans!
        ord_keys = sorted(set(spans_orig.keys()) & set(spans_shift.keys()))
        local_ords = [k for k in ord_keys if spans_orig[k].file_path == "src/checksum.rs"]
        inlined_core_ords = [k for k in ord_keys if spans_orig[k].file_path != "src/checksum.rs"]

        exact_50_line_shifts = sum(
            1
            for k in local_ords
            if spans_shift[k].lo_line == spans_orig[k].lo_line + 50
            and spans_shift[k].lo_col == spans_orig[k].lo_col
        )
        preserved_inlined_core = sum(
            1
            for k in inlined_core_ords
            if spans_shift[k].lo_line == spans_orig[k].lo_line
            and spans_shift[k].lo_col == spans_orig[k].lo_col
            and spans_shift[k].file_path == spans_orig[k].file_path
        )

        sample_ord = local_ords[min(3, len(local_ords) - 1)]
        return {
            "inserted_comment_lines": 50,
            "orig_mir_item_key": key_orig,
            "shifted_mir_item_key": key_shift,
            "mir_item_key_100pct_identical": key_orig == key_shift,
            "tracked_stmt_ordinals_total": len(ord_keys),
            "local_file_stmt_ordinals": len(local_ords),
            "local_ordinals_with_exact_plus_50_line_shift": exact_50_line_shifts,
            "inlined_core_stmt_ordinals": len(inlined_core_ords),
            "inlined_core_ordinals_preserved_exact": preserved_inlined_core,
            "all_ordinals_resolved_exact_100pct": (
                exact_50_line_shifts == len(local_ords)
                and preserved_inlined_core == len(inlined_core_ords)
                and len(local_ords) > 0
            ),
            "sample_stmt_ord_inspection": {
                "stmt_ord": sample_ord,
                "orig_span": f"{spans_orig[sample_ord].file_path}:{spans_orig[sample_ord].lo_line}:{spans_orig[sample_ord].lo_col}",
                "shifted_span": f"{spans_shift[sample_ord].file_path}:{spans_shift[sample_ord].lo_line}:{spans_shift[sample_ord].lo_col}",
                "canonical_op": spans_orig[sample_ord].snippet_text,
            },
        }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--sample-diags-out", required=True, type=Path)
    ap.add_argument("--sample-sarif-out", required=True, type=Path)
    ap.add_argument("--metrics-out", required=True, type=Path)
    args = ap.parse_args()

    shift_res = run_live_rustc_line_shift_test()
    diags_orig = anneal_diag_engine.build_six_canonical_diagnostics(0)
    diags_shifted = anneal_diag_engine.build_six_canonical_diagnostics(50)
    sarif_doc = anneal_diag_engine.build_sarif_210_report(diags_orig)
    repro_bytes, repro_ms, repro_members = anneal_diag_engine.generate_repro_bundle_bytes()

    # Verify all 6 diagnostics shift line numbers by +50 while preserving codes and columns
    all_diags_shifted_cleanly = all(
        ds["spans"][0]["line_start"] == do["spans"][0]["line_start"] + 50
        and ds["spans"][0]["column_start"] == do["spans"][0]["column_start"]
        and ds["code"]["code"] == do["code"]["code"]
        for do, ds in zip(diags_orig, diags_shifted)
    )

    args.sample_diags_out.parent.mkdir(parents=True, exist_ok=True)
    args.sample_diags_out.write_text(json.dumps(diags_orig, indent=2) + "\n", encoding="utf-8")
    args.sample_sarif_out.write_text(json.dumps(sarif_doc, indent=2) + "\n", encoding="utf-8")

    metrics = {
        "rustc_1991_sideband_span_shift_probe": shift_res,
        "diagnostic_suite_validation": {
            "total_canonical_scenarios": len(diags_orig),
            "codes_tested": [d["code"]["code"] for d in diags_orig],
            "rustc_json_schema_valid": all(d.get("$message_type") == "diagnostic" for d in diags_orig),
            "sarif_210_version": sarif_doc["version"],
            "sarif_210_rules_count": len(sarif_doc["runs"][0]["tool"]["driver"]["rules"]),
            "sarif_210_results_count": len(sarif_doc["runs"][0]["results"]),
            "post_shift_diagnostic_lines_exact_100pct": all_diags_shifted_cleanly,
        },
        "repro_minidump_benchmark": {
            "bundle_size_bytes": repro_bytes,
            "generation_elapsed_ms": round(repro_ms, 3),
            "within_5ms_budget": repro_ms < 5.0,
            "bundle_members": repro_members,
        },
    }
    args.metrics_out.write_text(json.dumps(metrics, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {args.metrics_out}")


if __name__ == "__main__":
    main()
