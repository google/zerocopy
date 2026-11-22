#!/usr/bin/env python3
"""Empirical probe for the consolidated rustc query engine.

Verifies:
  Suite 1 (optional --queries-rs): programmatic modifier census of
      compiler/rustc_middle/src/queries.rs (and cross-revision comparison if
      --queries-rs-baseline is supplied).
  Suite 2 (live rustc): incremental red-green early cutoff, QueryMode::EnsureOk
      disk-deserialization bypass (typeck_root marked green without disk load),
      static vs. dynamic dep-graph path assertions (including silent skip when
      -C incremental is omitted), commandline-hash invalidation, and
      -Zincremental-verify-ich.
  Suite 3 (live rustc): multi-tier cycle recovery (E0391 default const cycle,
      E0391 type-alias cycle, variances_of delay_as_bug -> E0072 single and
      mutual recursive ADTs, layout_of search_for_cycle_permutation -> E0733
      recursive async fn) and depth_limit doubling (Limit(4) -> 8, Limit(0) -> 2).

Uses only Python 3.10+ stdlib and cleans up all temporary directories on exit.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any


def find_rustc() -> str:
    env_rustc = os.environ.get("RUSTC")
    if env_rustc:
        return env_rustc
    which = shutil.which("rustc")
    if which:
        return which
    cargo_rustc = Path.home() / ".cargo" / "bin" / "rustc"
    if cargo_rustc.exists():
        return str(cargo_rustc)
    raise RuntimeError("rustc not found on PATH or in ~/.cargo/bin")


def sanitize_stderr(text: str, tmp_dir: str, sysroot: str) -> list[str]:
    out = text.replace(tmp_dir, "<TMP>")
    if sysroot:
        out = out.replace(sysroot, "<RUST_SYSROOT>")
    # Also mask rustc source paths inside sysroot library/ if present
    out = re.sub(r"/rustc/[0-9a-f]{40}/", "<RUST_SYSROOT_SRC>/", out)
    return out.splitlines()


def run_rustc(
    rustc: str,
    args: list[str],
    cwd: Path,
    tmp_dir: str,
    sysroot: str,
) -> dict[str, Any]:
    proc = subprocess.run(
        [rustc, *args],
        cwd=str(cwd),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
    )
    return {
        "rc": proc.returncode,
        "stdout_lines": sanitize_stderr(proc.stdout, tmp_dir, sysroot),
        "stderr_lines": sanitize_stderr(proc.stderr, tmp_dir, sysroot),
    }


def parse_queries_rs(path: Path, revision: str | None = None) -> dict[str, Any]:
    """Programmatically parse rustc_queries! entries and modifier algebra."""
    lines = path.read_text(encoding="utf-8").splitlines()
    queries: list[dict[str, Any]] = []
    i = 0
    while i < len(lines):
        line = lines[i]
        m = re.match(r"^\s*query\s+([a-zA-Z0-9_]+)\s*\(", line)
        if m:
            name = m.group(1)
            start_line = i + 1
            buf = [line]
            depth = line.count("{") - line.count("}")
            saw_brace = "{" in line
            j = i + 1
            while j < len(lines) and (not saw_brace or depth > 0):
                l = lines[j]
                buf.append(l)
                if "{" in l:
                    saw_brace = True
                depth += l.count("{") - l.count("}")
                j += 1
            end_line = j
            block = "\n".join(buf)
            first_b = block.find("{")
            last_b = block.rfind("}")
            mod_block = block[first_b + 1 : last_b] if first_b != -1 and last_b != -1 else ""
            mod_clean = re.sub(r"//.*", "", mod_block)
            # Strip desc { ... } blocks with balanced braces
            out: list[str] = []
            k = 0
            while k < len(mod_clean):
                dm = re.match(r"\bdesc\s*\{", mod_clean[k:])
                if dm:
                    k += dm.end()
                    d = 1
                    while k < len(mod_clean) and d > 0:
                        if mod_clean[k] == "{":
                            d += 1
                        elif mod_clean[k] == "}":
                            d -= 1
                        k += 1
                else:
                    out.append(mod_clean[k])
                    k += 1
            mods = re.findall(r"\b([a-z_][a-z0-9_]*)\b", "".join(out))
            queries.append(
                {
                    "name": name,
                    "start_line": start_line,
                    "end_line": end_line,
                    "modifiers": mods,
                }
            )
            i = j
        else:
            i += 1

    all_mods = sorted({m for q in queries for m in q["modifiers"]})
    modifier_counts = {m: sum(1 for q in queries if m in q["modifiers"]) for m in all_mods}
    by_mod = {m: [q["name"] for q in queries if m in q["modifiers"]] for m in all_mods}

    key_queries = {}
    for target in (
        "analysis",
        "hir_owner",
        "typeck_root",
        "optimized_mir",
        "mir_built",
        "mir_promoted",
        "mir_drops_elaborated_and_const_checked",
        "fn_sig",
        "variances_of",
        "check_representability",
        "check_representability_adt_ty",
        "layout_of",
        "eval_to_const_value_raw",
        "crate_for_resolver",
    ):
        for q in queries:
            if q["name"] == target:
                key_queries[target] = {
                    "lines": f"{q['start_line']}-{q['end_line']}",
                    "modifiers": q["modifiers"],
                }

    result: dict[str, Any] = {
        "source_path": "compiler/rustc_middle/src/queries.rs",
        "total_queries": len(queries),
        "modifier_counts": modifier_counts,
        "intersections": {
            "eval_always_and_cache_on_disk": [
                q["name"]
                for q in queries
                if "eval_always" in q["modifiers"] and "cache_on_disk" in q["modifiers"]
            ],
            "feedable_and_no_hash": [
                q["name"]
                for q in queries
                if "feedable" in q["modifiers"] and "no_hash" in q["modifiers"]
            ],
            "feedable_and_cache_on_disk": [
                q["name"]
                for q in queries
                if "feedable" in q["modifiers"] and "cache_on_disk" in q["modifiers"]
            ],
            "handle_cycle_error_all": by_mod.get("handle_cycle_error", []),
            "handle_cycle_error_and_no_force": [
                q["name"]
                for q in queries
                if "handle_cycle_error" in q["modifiers"] and "no_force" in q["modifiers"]
            ],
            "no_force_all": by_mod.get("no_force", []),
            "depth_limit_all": by_mod.get("depth_limit", []),
            "no_hash_all": by_mod.get("no_hash", []),
            "eval_always_all": by_mod.get("eval_always", []),
        },
        "key_query_locations": key_queries,
    }
    if revision:
        result["revision"] = revision
    return result


def run_suite2(rustc: str, sysroot: str) -> dict[str, Any]:
    """Incremental red-green early cutoff, EnsureOk skip, and dep-graph assertions."""
    out: dict[str, Any] = {}
    with tempfile.TemporaryDirectory(prefix="rustc_qry_suite2_") as tmp:
        td = Path(tmp)

        # --- Part 2A: 3-session incremental early cutoff + disk cache inspection ---
        incr_dir = td / "incr_early_cutoff"
        src_a = td / "lib_cutoff.rs"
        src_a.write_text(
            """#![allow(internal_features)]
#![feature(rustc_attrs)]

#[rustc_clean(cfg = "rev2", except = "hir_owner,optimized_mir,typeck_root")]
#[rustc_clean(cfg = "rev3")]
pub fn helper_body(x: u32) -> u32 {
    #[cfg(rev1)]
    { x.wrapping_add(1) }
    #[cfg(not(rev1))]
    { x.wrapping_add(2).wrapping_mul(5) }
}

#[rustc_clean(cfg = "rev2")]
#[rustc_clean(cfg = "rev3")]
pub fn caller_reused(x: u32) -> u32 {
    helper_body(x).wrapping_mul(3)
}

#[rustc_clean(cfg = "rev2")]
#[rustc_clean(cfg = "rev3")]
pub fn unrelated_fn(y: u64) -> u64 {
    y ^ 0x55aa_u64
}
""",
            encoding="utf-8",
        )
        common_flags = [
            "--crate-type=lib",
            "--crate-name=cutoff_demo",
            "--edition=2021",
            f"-Cincremental={incr_dir}",
            "-Zquery-dep-graph",
            "-Zincremental-info",
            "--out-dir",
            str(td / "out_cutoff"),
        ]
        (td / "out_cutoff").mkdir()

        r1 = run_rustc(
            rustc,
            [*common_flags, "--cfg=rev1", "-Zassert-incr-state=not-loaded", str(src_a)],
            td,
            tmp,
            sysroot,
        )
        r2 = run_rustc(
            rustc,
            [*common_flags, "--cfg=rev2", "-Zassert-incr-state=loaded", str(src_a)],
            td,
            tmp,
            sysroot,
        )
        r3 = run_rustc(
            rustc,
            [
                *common_flags,
                "--cfg=rev3",
                "-Zassert-incr-state=loaded",
                "-Zincremental-verify-ich",
                str(src_a),
            ],
            td,
            tmp,
            sysroot,
        )
        # Inspect resulting incremental session directory files
        cache_files: dict[str, int] = {}
        for p in sorted(incr_dir.rglob("*")):
            if p.is_file():
                name = p.name
                # Normalize CGU/session hashes for readable key naming while preserving exact names
                if name.endswith(".o"):
                    key = "<cgu>.o"
                elif name.endswith(".lock"):
                    key = "<session>.lock"
                else:
                    key = name
                cache_files[key] = p.stat().st_size

        # --- Part 2B: Commandline-arg hash mismatch invalidates cache ---
        r_args_mismatch = run_rustc(
            rustc,
            [
                *common_flags,
                "--cfg=rev3",
                "-Copt-level=2",
                "-Zassert-incr-state=loaded",
                str(src_a),
            ],
            td,
            tmp,
            sysroot,
        )

        # --- Part 2C: QueryMode::EnsureOk skips typeck_root disk deserialization ---
        incr_skip = td / "incr_skip"
        src_skip = td / "lib_skip.rs"
        src_skip.write_text(
            """#![allow(internal_features)]
#![feature(rustc_attrs)]

#[rustc_clean(cfg = "rev2", except = "hir_owner,optimized_mir,typeck_root")]
pub fn helper_body(x: u32) -> u32 {
    #[cfg(rev1)]
    { x.wrapping_add(1) }
    #[cfg(not(rev1))]
    { x.wrapping_add(2).wrapping_mul(5) }
}

#[rustc_clean(cfg = "rev2", loaded_from_disk = "typeck_root")]
pub fn caller_reused(x: u32) -> u32 {
    helper_body(x).wrapping_mul(3)
}
""",
            encoding="utf-8",
        )
        skip_out = td / "out_skip"
        skip_out.mkdir()
        skip_flags = [
            "--crate-type=lib",
            "--crate-name=skip_demo",
            "--edition=2021",
            f"-Cincremental={incr_skip}",
            "-Zquery-dep-graph",
            "--out-dir",
            str(skip_out),
        ]
        r_skip_1 = run_rustc(
            rustc,
            [*skip_flags, "--cfg=rev1", str(src_skip)],
            td,
            tmp,
            sysroot,
        )
        r_skip_2 = run_rustc(
            rustc,
            [*skip_flags, "--cfg=rev2", "-Zassert-incr-state=loaded", str(src_skip)],
            td,
            tmp,
            sysroot,
        )

        # --- Part 2D: Positive contrast — forcing caller_reused MIR to stay green
        # while checking optimized_mir loaded_from_disk vs typeck_root skipped ---
        incr_mir_load = td / "incr_mir_load"
        src_mir_load = td / "lib_mir_load.rs"
        src_mir_load.write_text(
            """#![allow(internal_features)]
#![feature(rustc_attrs)]

#[inline(always)]
pub fn leaf_const(x: u32) -> u32 {
    x.wrapping_add(7)
}

#[rustc_clean(cfg = "rev2", loaded_from_disk = "optimized_mir")]
pub fn caller_inlined(x: u32) -> u32 {
    leaf_const(x)
}

#[cfg(rev1)]
pub fn driver(x: u32) -> u32 {
    caller_inlined(x).wrapping_add(1)
}

#[cfg(rev2)]
pub fn driver(x: u32) -> u32 {
    caller_inlined(x).wrapping_add(2)
}
""",
            encoding="utf-8",
        )
        mir_out = td / "out_mir_load"
        mir_out.mkdir()
        mir_flags = [
            "--crate-type=lib",
            "--crate-name=mir_load_demo",
            "--edition=2021",
            "-Copt-level=2",
            f"-Cincremental={incr_mir_load}",
            "-Zquery-dep-graph",
            "--out-dir",
            str(mir_out),
        ]
        r_mir_1 = run_rustc(rustc, [*mir_flags, "--cfg=rev1", str(src_mir_load)], td, tmp, sysroot)
        r_mir_2 = run_rustc(
            rustc,
            [*mir_flags, "--cfg=rev2", "-Zassert-incr-state=loaded", str(src_mir_load)],
            td,
            tmp,
            sysroot,
        )

        # --- Part 2E: Static dep-graph path assertions WITH vs WITHOUT -C incremental ---
        src_paths = td / "paths.rs"
        src_paths.write_text(
            """#![allow(internal_features)]
#![feature(rustc_attrs)]

#[rustc_if_this_changed(hir_owner)]
pub fn body_only_src(x: u32) -> u32 {
    x.wrapping_add(1)
}

#[rustc_then_this_would_need(typeck_root)]
pub fn calls_src(x: u32) -> u32 {
    body_only_src(x).wrapping_mul(3)
}

#[rustc_then_this_would_need(typeck_root)]
pub fn independent_fn(x: u32) -> u32 {
    x.wrapping_mul(2)
}
""",
            encoding="utf-8",
        )
        paths_out = td / "out_paths"
        paths_out.mkdir()
        r_paths_no_incr = run_rustc(
            rustc,
            [
                "--crate-type=lib",
                "--crate-name=paths_no_incr",
                "--edition=2021",
                "-Zquery-dep-graph",
                "--out-dir",
                str(paths_out),
                str(src_paths),
            ],
            td,
            tmp,
            sysroot,
        )
        incr_paths = td / "incr_paths"
        r_paths_with_incr = run_rustc(
            rustc,
            [
                "--crate-type=lib",
                "--crate-name=paths_with_incr",
                "--edition=2021",
                f"-Cincremental={incr_paths}",
                "-Zquery-dep-graph",
                "--out-dir",
                str(paths_out),
                str(src_paths),
            ],
            td,
            tmp,
            sysroot,
        )

        def summarize_incr_stats(res: dict[str, Any]) -> dict[str, Any]:
            lines = res["stderr_lines"]
            summary_lines = []
            node_count = None
            edge_count = None
            hard_linked = None
            for l in lines:
                if l.startswith("[incremental] Total Node Count:"):
                    node_count = int(l.split(":", 1)[1].strip())
                    summary_lines.append(l)
                elif l.startswith("[incremental] Total Edge Count:"):
                    edge_count = int(l.split(":", 1)[1].strip())
                    summary_lines.append(l)
                elif "files hard-linked" in l or "files copied" in l:
                    hard_linked = l
                    summary_lines.append(l)
                elif not l.startswith("[incremental]"):
                    summary_lines.append(l)
            return {
                "rc": res["rc"],
                "total_node_count": node_count,
                "total_edge_count": edge_count,
                "stderr_summary_lines": summary_lines,
                "stderr_line_count": len(lines),
            }

        out = {
            "session1_rev1": summarize_incr_stats(r1),
            "session2_rev2_early_cutoff": summarize_incr_stats(r2),
            "session3_rev3_noop_verify_ich": summarize_incr_stats(r3),
            "session_cache_files_bytes": cache_files,
            "commandline_hash_mismatch_rejected": r_args_mismatch,
            "ensure_ok_skips_typeck_root_disk_load_rev1_rc": r_skip_1["rc"],
            "ensure_ok_skips_typeck_root_disk_load": r_skip_2,
            "positive_control_optimized_mir_loaded_from_disk_rev1_rc": r_mir_1["rc"],
            "positive_control_optimized_mir_loaded_from_disk": r_mir_2,
            "dep_graph_paths_without_incr_silently_skipped": r_paths_no_incr,
            "dep_graph_paths_with_incr": r_paths_with_incr,
        }
    return out


def run_suite3(rustc: str, sysroot: str) -> dict[str, Any]:
    """Multi-tier cycle recovery and depth-limit diagnostic matrix."""
    cases: dict[str, tuple[str, list[str]]] = {
        "default_const_cycle_e0391": (
            """pub const A: usize = B + 1;
pub const B: usize = A + 1;
""",
            ["--crate-type=lib", "--edition=2021"],
        ),
        "type_alias_cycle_e0391": (
            """pub type AliasA = AliasB;
pub type AliasB = AliasA;
pub fn use_alias(x: AliasA) -> AliasA { x }
""",
            ["--crate-type=lib", "--edition=2021"],
        ),
        "variances_of_delayed_to_e0072": (
            """pub struct Rec<T>(pub Rec<T>, pub *const T);
""",
            ["--crate-type=lib", "--edition=2021"],
        ),
        "mutual_adt_cycle_e0072_span_rotation": (
            """pub struct Second<T>(pub First<T>, pub *const T);
pub struct First<T>(pub Second<T>, pub *const T);
""",
            ["--crate-type=lib", "--edition=2021"],
        ),
        "layout_of_async_fn_cycle_e0733": (
            """pub async fn ping(n: u32) -> u32 {
    if n == 0 { 0 } else { pong(n - 1).await }
}
pub async fn pong(n: u32) -> u32 {
    ping(n).await
}
""",
            ["--crate-type=lib", "--edition=2021"],
        ),
        "depth_limit_4_layout_of_doubles_to_8": (
            """#![recursion_limit = "4"]
pub struct Layer<T>(pub T);
pub const S: usize = core::mem::size_of::<Layer<Layer<Layer<Layer<Layer<Layer<u8>>>>>>>();
""",
            ["--crate-type=lib", "--edition=2021"],
        ),
        "depth_limit_0_const_eval_special_cases_to_2": (
            """#![recursion_limit = "0"]
pub const C2: usize = 1;
pub const C1: usize = C2 + 1;
pub type Arr = [u8; C1];
""",
            ["--crate-type=lib", "--edition=2021"],
        ),
    }

    results: dict[str, Any] = {}
    with tempfile.TemporaryDirectory(prefix="rustc_qry_suite3_") as tmp:
        td = Path(tmp)
        out_dir = td / "out"
        out_dir.mkdir()
        for name, (code, flags) in cases.items():
            src = td / f"{name}.rs"
            src.write_text(code, encoding="utf-8")
            results[name] = run_rustc(
                rustc,
                [*flags, f"--crate-name={name}", "--out-dir", str(out_dir), str(src)],
                td,
                tmp,
                sysroot,
            )

        # Also test variances_of -> E0072 under incremental mode (verifies no_force keeps E0072 intact)
        incr_e0072 = td / "incr_e0072"
        src_rec = td / "variances_of_delayed_to_e0072.rs"
        results["variances_of_delayed_to_e0072_incremental"] = run_rustc(
            rustc,
            [
                "--crate-type=lib",
                "--edition=2021",
                "--crate-name=variances_of_delayed_to_e0072_incremental",
                f"-Cincremental={incr_e0072}",
                "--out-dir",
                str(out_dir),
                str(src_rec),
            ],
            td,
            tmp,
            sysroot,
        )
        # Confirm that a failed incremental build does not leave a finalized dep-graph.bin
        saved_dep_graphs = [p.name for p in incr_e0072.rglob("dep-graph.bin")]
        results["failed_session_dep_graph_persisted"] = len(saved_dep_graphs) > 0
    return results


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--queries-rs", type=Path, help="Path to rust-lang/rust compiler/rustc_middle/src/queries.rs (HEAD)")
    parser.add_argument("--queries-rs-rev", type=str, help="40-hex commit SHA for --queries-rs")
    parser.add_argument("--queries-rs-baseline", type=Path, help="Optional baseline queries.rs (e.g. executed toolchain revision)")
    parser.add_argument("--queries-rs-baseline-rev", type=str, help="40-hex commit SHA for --queries-rs-baseline")
    parser.add_argument("--output", "-o", type=Path, help="Write JSON results to this path")
    args = parser.parse_args()

    rustc = find_rustc()
    vv = subprocess.check_output([rustc, "--version", "--verbose"], text=True).strip()
    sysroot = subprocess.check_output([rustc, "--print", "sysroot"], text=True).strip()

    commit_hash = None
    release = None
    llvm_version = None
    for line in vv.splitlines():
        if line.startswith("commit-hash:"):
            commit_hash = line.split(":", 1)[1].strip()
        elif line.startswith("release:"):
            release = line.split(":", 1)[1].strip()
        elif line.startswith("LLVM version:"):
            llvm_version = line.split(":", 1)[1].strip()

    payload: dict[str, Any] = {
        "toolchain": {
            "rustc_vV": vv,
            "release": release,
            "commit_hash": commit_hash,
            "llvm_version": llvm_version,
        },
        "suite2_incremental_early_cutoff_and_dep_graph": run_suite2(rustc, sysroot),
        "suite3_cycle_recovery_and_depth_limit_matrix": run_suite3(rustc, sysroot),
    }

    if args.queries_rs:
        payload["suite1_queries_rs_modifier_census_head"] = parse_queries_rs(
            args.queries_rs, args.queries_rs_rev
        )
    if args.queries_rs_baseline:
        payload["suite1_queries_rs_modifier_census_executed"] = parse_queries_rs(
            args.queries_rs_baseline, args.queries_rs_baseline_rev
        )

    encoded = json.dumps(payload, indent=2, sort_keys=False) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(encoded, encoding="utf-8")
        print(f"Wrote {args.output} ({len(encoded)} bytes)")
    else:
        sys.stdout.write(encoded)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
