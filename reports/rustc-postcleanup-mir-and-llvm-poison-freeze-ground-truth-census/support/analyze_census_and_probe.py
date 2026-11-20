#!/usr/bin/env python3
"""Reproducible analyzer for `rustc_1_99_1_census.json` and live MIR/LLVM IR probes.

Zero hardcoded metric tables: all reported figures are computed directly from
`rustc_1_99_1_census.json` or parsed live from `.mir` and `.ll` artifacts
emitted by `rustc` on `reproduce_hazards_probe.rs` (or user-supplied paths).
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import shutil
import subprocess
import tempfile
from typing import Any


MOVE_FIELD_RE = re.compile(r"\bmove\s+\((_\d+)\.(\d+):")
READ_FIELD_RE = re.compile(r"\b(?:copy|move)\s+\((_\d+)\.(\d+):")
COPY_LOCAL_RE = re.compile(r"\bcopy\s+(_\d+)\b")
MOVE_LOCAL_RE = re.compile(r"\bmove\s+(_\d+)\b")
FN_HEADER_RE = re.compile(r"^fn\s+.+\{$")
BB_HEADER_RE = re.compile(r"^\s*bb\d+(?:\s*\(cleanup\))?:\s*\{$")

LLVM_DEFINE_RE = re.compile(r"^define\b.+@(?:\"[^\"]+\"|[A-Za-z0-9_.$]+)\(.*\{\s*$")
LLVM_FEATURE_PATTERNS: dict[str, re.Pattern[str]] = {
    "noundef": re.compile(r"\bnoundef\b"),
    "noalias": re.compile(r"\bnoalias\b"),
    "captures_none": re.compile(r"\bcaptures\(none\)"),
    "range_attr": re.compile(r"\brange\("),
    "sret": re.compile(r"\bsret\("),
    "dead_on_unwind": re.compile(r"\bdead_on_unwind\b"),
    "dead_on_return": re.compile(r"\bdead_on_return\b"),
    "nuw": re.compile(r"\bnuw\b"),
    "nsw": re.compile(r"\bnsw\b"),
    "disjoint": re.compile(r"\bdisjoint\b"),
    "nneg": re.compile(r"\bnneg\b"),
    "samesign": re.compile(r"\bsamesign\b"),
    "exact": re.compile(r"\bexact\b"),
    "freeze": re.compile(r"=\s*freeze\b"),
    "poison": re.compile(r"\bpoison\b"),
    "undef": re.compile(r"\bundef\b"),
    "invoke": re.compile(r"^\s*(?:%[^\s=]+\s*=\s*)?invoke\b"),
    "landingpad": re.compile(r"^\s*%[^\s=]+\s*=\s*landingpad\b"),
    "select": re.compile(r"=\s*select\b"),
    "switch": re.compile(r"^\s*switch\b"),
    "llvm_assume": re.compile(r"@llvm\.assume\b"),
    "llvm_lifetime": re.compile(r"@llvm\.lifetime\.(?:start|end)\b"),
    "llvm_memcpy": re.compile(r"@llvm\.memcpy\b"),
}


def summarize_recorded_census(census_path: pathlib.Path) -> dict[str, Any]:
    data = json.loads(census_path.read_text(encoding="utf-8"))
    mir_out: dict[str, Any] = {}
    total_mir_bodies = 0
    total_mir_bbs = 0

    for key, entry in data["mir"].items():
        bodies = entry["total_bodies"]
        bbs = entry["total_bbs"]
        total_mir_bodies += bodies
        total_mir_bbs += bbs
        bw = entry["bodies_with"]
        m3_bodies = bw.get("m3_partial_field_move", 0)
        m4_bodies = bw.get("m4_same_stmt_move_alias", 0)
        mir_out[key] = {
            "total_bodies": bodies,
            "total_bbs": bbs,
            "mean_bbs_per_body": round(bbs / bodies, 2) if bodies else 0.0,
            "bb_percentiles": {
                "p50": entry["bb_p50"],
                "p95": entry["bb_p95"],
                "p99": entry["bb_p99"],
                "max": entry["bb_max"],
            },
            "fits_unproj_no_unwind_no_rawptr_pct": round(
                100.0 * bw.get("fits_unproj_no_unwind_no_rawptr", 0) / bodies, 2
            ),
            "m3_partial_field_move": {
                "bodies": m3_bodies,
                "pct": round(100.0 * m3_bodies / bodies, 2),
                "sample_sites": len(entry.get("m3_samples", [])),
            },
            "m4_same_stmt_move_alias": {
                "bodies": m4_bodies,
                "pct": round(100.0 * m4_bodies / bodies, 2),
                "sample_sites": len(entry.get("m4_samples", [])),
            },
            "has_unwind_cleanup_pct": round(
                100.0 * bw.get("has_unwind_cleanup", 0) / bodies, 2
            ),
            "has_deref_proj_pct": round(
                100.0 * bw.get("has_deref_proj", 0) / bodies, 2
            ),
            "has_transmute_pct": round(
                100.0 * bw.get("has_transmute", 0) / bodies, 2
            ),
            "has_raw_ptr_pct": round(
                100.0 * bw.get("has_raw_ptr", 0) / bodies, 2
            ),
            "storage_marker_share_of_stmts_pct": round(
                100.0
                * (entry["stmts"].get("StorageLive", 0) + entry["stmts"].get("StorageDead", 0))
                / max(1, sum(entry["stmts"].values())),
                2,
            ),
        }

    llvm_out: dict[str, Any] = {}
    for key, entry in data["llvm_ir"].items():
        nfns = entry["num_functions"]
        fw = entry["fn_with_feature"]
        occ = entry["total_occurrences"]
        llvm_out[key] = {
            "num_functions": nfns,
            "total_bbs": entry["total_bbs"],
            "total_phis": entry["total_phis"],
            "bb_percentiles": {
                "p50": entry["bb_p50"],
                "p95": entry["bb_p95"],
                "max": entry["bb_max"],
            },
            "feature_fn_pct": {
                feat: round(100.0 * count / nfns, 2)
                for feat, count in sorted(fw.items(), key=lambda kv: (-kv[1], kv[0]))
            }
            if nfns
            else {},
            "feature_occurrences": occ,
            "freeze_examples_count": len(entry.get("freeze_examples", [])),
        }

    # Combined Anneal TCB LLVM IR across both binaries (79 + 45 = 124 functions)
    tcb_keys = [
        "anneal_tcb_1.99.1:anneal_audit-7beda83da10ce6a8.ll",
        "anneal_tcb_1.99.1:cargo_anneal-a159cbf311c93d0c.ll",
    ]
    tcb_fns = sum(data["llvm_ir"][k]["num_functions"] for k in tcb_keys)
    tcb_invoke_fns = sum(
        data["llvm_ir"][k]["fn_with_feature"].get("invoke", 0) for k in tcb_keys
    )
    tcb_invoke_occ = sum(
        data["llvm_ir"][k]["total_occurrences"].get("invoke", 0) for k in tcb_keys
    )
    core_ll = data["llvm_ir"]["libcore_1.99.1:core.ll"]
    core_invoke_pct = 100.0 * core_ll["fn_with_feature"]["invoke"] / core_ll["num_functions"]
    tcb_invoke_pct = 100.0 * tcb_invoke_fns / tcb_fns

    return {
        "totals": {
            "mir_bodies": total_mir_bodies,
            "mir_basic_blocks": total_mir_bbs,
            "llvm_functions_nonempty": core_ll["num_functions"] + tcb_fns,
            "anneal_tcb_llvm_functions": tcb_fns,
            "anneal_tcb_invoke_fn_pct": round(tcb_invoke_pct, 2),
            "anneal_tcb_invoke_occurrences": tcb_invoke_occ,
            "unwind_cliff_ratio_tcb_vs_core": round(tcb_invoke_pct / core_invoke_pct, 1),
        },
        "mir": mir_out,
        "llvm_ir": llvm_out,
    }


def scan_mir_text(mir_text: str) -> dict[str, Any]:
    bodies = 0
    m3_hits: list[dict[str, Any]] = []
    m4_hits: list[dict[str, Any]] = []

    cur_fn: str | None = None
    cur_bb: str | None = None
    moved_fields: dict[str, set[str]] = {}

    for raw_line in mir_text.splitlines():
        line = raw_line.strip()
        if FN_HEADER_RE.match(line) and not line.startswith("//"):
            cur_fn = line
            cur_bb = None
            moved_fields = {}
            bodies += 1
            continue
        if cur_fn is None:
            continue
        if BB_HEADER_RE.match(raw_line):
            cur_bb = line.split(":")[0]
            moved_fields = {}
            continue
        if cur_bb is None:
            continue

        # Check M4: same statement/terminator contains both `copy _k` and `move _k`
        copies = set(COPY_LOCAL_RE.findall(line))
        moves = set(MOVE_LOCAL_RE.findall(line))
        both = sorted(copies & moves)
        for loc in both:
            m4_hits.append({"fn": cur_fn, "bb": cur_bb, "local": loc, "stmt": line})

        # Check M3: intra-block partial field move followed by sibling field read/move
        # (including two distinct field moves in the same call argument list)
        stmt_reads = READ_FIELD_RE.findall(line)
        for base_local, fld in stmt_reads:
            prev = moved_fields.get(base_local, set())
            if prev and (fld not in prev or len(prev) > 0):
                if any(prev_fld != fld for prev_fld in prev):
                    m3_hits.append(
                        {
                            "fn": cur_fn,
                            "bb": cur_bb,
                            "local": base_local,
                            "prev_moved_fields": sorted(prev),
                            "subsequent_field": fld,
                            "stmt": line,
                        }
                    )
            if f"move ({base_local}.{fld}:" in line:
                moved_fields.setdefault(base_local, set()).add(fld)

    return {
        "bodies_scanned": bodies,
        "m3_hits": m3_hits,
        "m4_hits": m4_hits,
    }


def scan_llvm_ir_text(ll_text: str) -> dict[str, Any]:
    num_fns = 0
    fn_with: dict[str, int] = {k: 0 for k in LLVM_FEATURE_PATTERNS}
    total_occ: dict[str, int] = {k: 0 for k in LLVM_FEATURE_PATTERNS}
    freeze_lines: list[dict[str, str]] = []

    in_fn = False
    cur_header = ""
    seen_in_fn: set[str] = set()

    def scan_line(line: str) -> None:
        for feat, rx in LLVM_FEATURE_PATTERNS.items():
            matches = rx.findall(line)
            if matches:
                total_occ[feat] += len(matches)
                seen_in_fn.add(feat)
                if feat == "freeze":
                    freeze_lines.append({"fn": cur_header, "line": line.strip()})

    for raw_line in ll_text.splitlines():
        if not in_fn:
            if LLVM_DEFINE_RE.match(raw_line):
                in_fn = True
                num_fns += 1
                cur_header = raw_line.strip()
                seen_in_fn = set()
                scan_line(raw_line)
        else:
            if raw_line.strip() == "}":
                for feat in seen_in_fn:
                    fn_with[feat] += 1
                in_fn = False
            else:
                scan_line(raw_line)

    return {
        "num_functions": num_fns,
        "fn_with_feature": {k: v for k, v in fn_with.items() if v > 0},
        "total_occurrences": {k: v for k, v in total_occ.items() if v > 0},
        "freeze_lines": freeze_lines,
    }


def run_live_probe(probe_rs: pathlib.Path, rustc_bin: str) -> dict[str, Any]:
    ver = subprocess.check_output([rustc_bin, "--version", "--verbose"], text=True).strip()
    with tempfile.TemporaryDirectory(prefix="rustc_census_probe_") as tmp:
        tmp_dir = pathlib.Path(tmp)
        cmd = [
            rustc_bin,
            "--edition=2021",
            "--crate-type=lib",
            "-C",
            "opt-level=3",
            "-C",
            "codegen-units=1",
            "--emit=mir,llvm-ir",
            str(probe_rs),
            "--out-dir",
            str(tmp_dir),
        ]
        subprocess.run(cmd, check=True, capture_output=True, text=True)
        mir_file = next(tmp_dir.glob("*.mir"))
        ll_file = next(tmp_dir.glob("*.ll"))
        return {
            "rustc_verbose_version": ver,
            "command": " ".join(cmd),
            "mir_scan": scan_mir_text(mir_file.read_text(encoding="utf-8")),
            "llvm_scan": scan_llvm_ir_text(ll_file.read_text(encoding="utf-8")),
        }


def main() -> int:
    here = pathlib.Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--census-json",
        type=pathlib.Path,
        default=here / "rustc_1_99_1_census.json",
        help="Path to recorded rustc 1.99.1 census JSON",
    )
    parser.add_argument(
        "--run-live-probe",
        action="store_true",
        help="Compile support/reproduce_hazards_probe.rs with local rustc and scan emitted MIR + LLVM IR",
    )
    parser.add_argument(
        "--rustc",
        default=shutil.which("rustc") or "rustc",
        help="rustc binary to invoke when --run-live-probe is set",
    )
    args = parser.parse_args()

    result: dict[str, Any] = {
        "recorded_rustc_1_99_1_census": summarize_recorded_census(args.census_json)
    }
    if args.run_live_probe:
        result["live_probe"] = run_live_probe(here / "reproduce_hazards_probe.rs", args.rustc)

    print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
