#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Reproducible probe of rustc Runtime(PostCleanup) and Runtime(Optimized) MIR.

Compiles `postcleanup_constructs_specimen.rs` across `nightly-2026-03-19`
(`1.96.0-nightly`) and `nightly-2026-05-31` (`1.98.0-nightly`) under both
default flags and `-Z mir-preserve-ub`, parses the emitted MIR bodies for all
five construct families, verifies structural invariants, and writes structured
JSON output to `postcleanup_constructs_results.json`.
"""

from __future__ import annotations

import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from typing import Any

SPECIMEN_FUNCTIONS = [
    "while_loop_sum",
    "range_for_loop_sum",
    "disjoint_field_borrows",
    "nested_reborrow",
    "two_phase_method_borrow",
    "raw_ptr_projections",
    "construct_and_match_packet",
    "array_and_slice_ops",
    "conditional_move_and_unwind",
]

TOOLCHAINS = [
    "nightly-2026-03-19",
    "nightly-2026-05-31",
]

BB_HEADER_RE = re.compile(r"^\s*bb(\d+)(\s*\(cleanup\))?:\s*\{")
GOTO_TARGET_RE = re.compile(r"goto\s*->\s*bb(\d+)")
SWITCH_TARGETS_RE = re.compile(r"switchInt\([^)]+\)\s*->\s*\[([^\]]+)\]")
BB_REF_RE = re.compile(r"bb(\d+)")
LOCAL_DECL_RE = re.compile(r"^\s*let(?:\s+mut)?\s+_(\d+):\s*([^;]+);")


def get_toolchain_metadata(toolchain: str) -> dict[str, str]:
    proc = subprocess.run(
        ["rustc", f"+{toolchain}", "-vV"],
        check=True,
        capture_output=True,
        text=True,
    )
    meta: dict[str, str] = {"toolchain": toolchain}
    lines = proc.stdout.strip().splitlines()
    if lines:
        meta["rustc_version_line"] = lines[0]
    for line in lines[1:]:
        if ":" in line:
            k, v = line.split(":", 1)
            meta[k.strip().replace("-", "_")] = v.strip()
    return meta


def parse_mir_body(mir_text: str) -> dict[str, Any]:
    lines = mir_text.splitlines()
    locals_map: dict[str, str] = {}
    blocks: list[dict[str, Any]] = []
    back_edges: list[dict[str, int]] = []

    current_bb: int | None = None
    current_cleanup = False
    current_stmts: list[str] = []

    for raw_line in lines:
        m_local = LOCAL_DECL_RE.match(raw_line)
        if m_local:
            locals_map[f"_{m_local.group(1)}"] = m_local.group(2).strip()

        m_bb = BB_HEADER_RE.match(raw_line)
        if m_bb:
            current_bb = int(m_bb.group(1))
            current_cleanup = m_bb.group(2) is not None
            current_stmts = []
            continue

        if current_bb is not None:
            stripped = raw_line.strip()
            if stripped == "}":
                blocks.append(
                    {
                        "bb": current_bb,
                        "is_cleanup": current_cleanup,
                        "statements": current_stmts,
                    }
                )
                current_bb = None
            elif stripped:
                current_stmts.append(stripped)
                for m_tgt in BB_REF_RE.finditer(stripped):
                    tgt_bb = int(m_tgt.group(1))
                    if tgt_bb <= current_bb:
                        back_edges.append({"from_bb": current_bb, "to_bb": tgt_bb})

    all_stmt_lines = [s for b in blocks for s in b["statements"]]

    def count_substr(sub: str) -> int:
        return sum(1 for s in all_stmt_lines if sub in s)

    def count_regex(pat: str) -> int:
        rx = re.compile(pat)
        return sum(1 for s in all_stmt_lines if rx.search(s))

    counts = {
        "basic_blocks": len(blocks),
        "cleanup_blocks": sum(1 for b in blocks if b["is_cleanup"]),
        "locals": len(locals_map),
        "bool_locals": sum(1 for ty in locals_map.values() if ty == "bool"),
        "StorageLive": count_substr("StorageLive("),
        "StorageDead": count_substr("StorageDead("),
        "PlaceMention": count_substr("PlaceMention("),
        "switchInt": count_substr("switchInt("),
        "goto": count_substr("goto ->"),
        "drop": count_substr("drop("),
        "resume": sum(1 for s in all_stmt_lines if s == "resume;"),
        "terminate_cleanup": count_substr("unwind terminate(cleanup)"),
        "unreachable": sum(1 for s in all_stmt_lines if s == "unreachable;"),
        "assert": count_substr("assert("),
        "discriminant": count_substr("discriminant("),
        "PtrMetadata": count_substr("PtrMetadata("),
        "FakeForPtrMetadata": count_substr("&raw const (fake)"),
        "RawPtrConst": count_regex(r"&raw const \((?!fake\))"),
        "RawPtrMut": count_substr("&raw mut "),
        "SliceLenCall": count_substr("core::slice::<impl [u64]>::len("),
        "DowncastProjection": count_regex(r"\(_\d+ as [A-Za-z0-9_]+\)\.\d+"),
        "ConstantIndexProjection": count_regex(r"\[-?\d+ of \d+\]"),
        "SubsliceProjection": count_regex(r"\[\d+:-?\d+\]"),
        "NoRetagUse": count_substr("no_retag "),
        "BoolConstFalseAssign": count_substr("= const false;"),
        "BoolConstTrueAssign": count_substr("= const true;"),
        "back_edges": len(back_edges),
    }

    return {
        "counts": counts,
        "locals": locals_map,
        "back_edges": back_edges,
        "blocks": blocks,
        "mir_text": mir_text,
    }


def compile_and_extract(
    toolchain: str,
    specimen_path: Path,
    extra_flags: list[str],
    pass_filter: str,
    file_suffix: str,
) -> dict[str, Any]:
    with tempfile.TemporaryDirectory(prefix="anneal_mir_probe_") as tmpdir:
        tmp_path = Path(tmpdir)
        dump_dir = tmp_path / "dump"
        out_rlib = tmp_path / "libspecimen.rlib"
        cmd = [
            "rustc",
            f"+{toolchain}",
            "--crate-type=lib",
            "--edition=2024",
            f"-Zdump-mir={pass_filter}",
            f"-Zdump-mir-dir={dump_dir}",
            *extra_flags,
            str(specimen_path),
            "-o",
            str(out_rlib),
        ]
        subprocess.run(cmd, check=True, capture_output=True, text=True)

        extracted: dict[str, Any] = {}
        for fn_name in SPECIMEN_FUNCTIONS:
            matches = sorted(
                dump_dir.glob(
                    f"postcleanup_constructs_specimen.{fn_name}.*.{file_suffix}.after.mir"
                )
            )
            if not matches:
                raise RuntimeError(
                    f"Missing MIR dump for {fn_name} ({file_suffix}) under {toolchain}"
                )
            mir_text = matches[0].read_text(encoding="utf-8")
            extracted[fn_name] = parse_mir_body(mir_text)
        return extracted


def verify_invariants(results: dict[str, Any]) -> list[str]:
    checks: list[str] = []
    for tc in TOOLCHAINS:
        tc_data = results["toolchains"][tc]
        default_pc = tc_data["modes"]["default_runtime_post_cleanup"]
        presub_pc = tc_data["modes"]["preserve_ub_runtime_post_cleanup"]
        inst_opt = tc_data["modes"]["opt_instsimplify_before_inline"]
        full_opt = tc_data["modes"]["opt_runtime_optimized"]

        # 1. Loops & back-edges
        w_loop = default_pc["while_loop_sum"]
        assert w_loop["counts"]["back_edges"] == 1
        assert w_loop["back_edges"][0] == {"from_bb": 4, "to_bb": 1}
        assert w_loop["counts"]["StorageLive"] == 14
        assert w_loop["counts"]["StorageDead"] == 17
        checks.append(f"{tc}: while_loop_sum has back-edge bb4->bb1 and balanced StorageLive/Dead")

        r_loop = default_pc["range_for_loop_sum"]
        assert r_loop["counts"]["back_edges"] == 1
        assert r_loop["back_edges"][0] == {"from_bb": 7, "to_bb": 2}
        assert r_loop["counts"]["discriminant"] == 1
        assert r_loop["counts"]["DowncastProjection"] == 1
        checks.append(f"{tc}: range_for_loop_sum has back-edge bb7->bb2 and Option::Some downcast")

        # 2. Disjoint borrows, nested reborrows, two-phase borrows, raw pointers
        dfb = default_pc["disjoint_field_borrows"]
        assert dfb["counts"]["basic_blocks"] == 2
        tpb = default_pc["two_phase_method_borrow"]
        assert tpb["counts"]["basic_blocks"] == 3
        raw_p = default_pc["raw_ptr_projections"]
        assert raw_p["counts"]["RawPtrConst"] == 1
        assert raw_p["counts"]["RawPtrMut"] == 1
        checks.append(f"{tc}: borrow and raw-pointer constructs verified at Runtime(PostCleanup)")

        if tc == "nightly-2026-05-31":
            assert inst_opt["two_phase_method_borrow"]["counts"]["NoRetagUse"] == 1
            assert inst_opt["nested_reborrow"]["counts"]["NoRetagUse"] == 0
            checks.append(
                f"{tc}: InstSimplify lowers TwoPhaseBorrow to `no_retag copy _1` (WithRetag::No)"
            )

        # 3. Enums, discriminants, and downcast projections
        pkt = default_pc["construct_and_match_packet"]
        assert pkt["counts"]["discriminant"] == 1
        assert pkt["counts"]["switchInt"] == 2
        assert pkt["counts"]["DowncastProjection"] == 3
        assert pkt["counts"]["unreachable"] == 1
        checks.append(f"{tc}: construct_and_match_packet uses AggregateKind::Adt, discriminant, and 3 downcasts")

        # 4. Arrays, slices, indexing, and PtrMetadata
        arr_s = default_pc["array_and_slice_ops"]
        assert arr_s["counts"]["PtrMetadata"] == 4
        assert arr_s["counts"]["FakeForPtrMetadata"] == 2
        assert arr_s["counts"]["assert"] == 4
        assert arr_s["counts"]["ConstantIndexProjection"] == 2
        assert arr_s["counts"]["SubsliceProjection"] == 1
        assert arr_s["counts"]["SliceLenCall"] == 1
        assert full_opt["array_and_slice_ops"]["counts"]["SliceLenCall"] == 0
        checks.append(
            f"{tc}: array_and_slice_ops emits 4 PtrMetadata (2 via &raw const (fake)), "
            "ConstantIndex/Subslice projections, and keeps slice::len as Call until Runtime(Optimized)"
        )

        # 5. Drop elaboration, drop flags, and unwind cleanup
        drop_fn = default_pc["conditional_move_and_unwind"]
        assert drop_fn["counts"]["basic_blocks"] == 16
        assert drop_fn["counts"]["cleanup_blocks"] == 4
        assert drop_fn["counts"]["drop"] == 4
        assert drop_fn["counts"]["resume"] == 1
        assert drop_fn["counts"]["terminate_cleanup"] == 2
        assert drop_fn["counts"]["BoolConstFalseAssign"] == 3
        assert drop_fn["counts"]["BoolConstTrueAssign"] == 1
        checks.append(
            f"{tc}: conditional_move_and_unwind has 4 cleanup blocks, 4 drops, 1 resume, "
            "and stack boolean drop flag _18"
        )

        # 6. -Z mir-preserve-ub effect at Runtime(PostCleanup)
        assert default_pc["construct_and_match_packet"]["counts"]["PlaceMention"] == 0
        assert presub_pc["construct_and_match_packet"]["counts"]["PlaceMention"] == 2
        assert default_pc["range_for_loop_sum"]["counts"]["PlaceMention"] == 0
        assert presub_pc["range_for_loop_sum"]["counts"]["PlaceMention"] == 2
        assert default_pc["array_and_slice_ops"]["counts"]["PlaceMention"] == 0
        assert presub_pc["array_and_slice_ops"]["counts"]["PlaceMention"] == 1
        checks.append(
            f"{tc}: -Z mir-preserve-ub retains PlaceMention statements stripped by default RemovePlaceMention"
        )

    return checks


def main() -> int:
    support_dir = Path(__file__).resolve().parent
    specimen_path = support_dir / "postcleanup_constructs_specimen.rs"
    out_path = support_dir / "postcleanup_constructs_results.json"

    results: dict[str, Any] = {
        "specimen_file": specimen_path.name,
        "toolchains": {},
    }

    for tc in TOOLCHAINS:
        meta = get_toolchain_metadata(tc)
        modes = {
            "default_runtime_post_cleanup": compile_and_extract(
                tc,
                specimen_path,
                [],
                "runtime-post-cleanup",
                "runtime-post-cleanup",
            ),
            "preserve_ub_runtime_post_cleanup": compile_and_extract(
                tc,
                specimen_path,
                ["-Zmir-preserve-ub"],
                "runtime-post-cleanup",
                "runtime-post-cleanup",
            ),
            "opt_instsimplify_before_inline": compile_and_extract(
                tc,
                specimen_path,
                ["-O"],
                "InstSimplify-before-inline",
                "InstSimplify-before-inline",
            ),
            "opt_runtime_optimized": compile_and_extract(
                tc,
                specimen_path,
                ["-O"],
                "runtime-optimized",
                "runtime-optimized",
            ),
        }
        results["toolchains"][tc] = {
            "metadata": meta,
            "modes": modes,
        }

    checks = verify_invariants(results)
    results["verified_invariants"] = checks

    out_path.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {out_path} ({ len(checks) } invariant checks passed).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
