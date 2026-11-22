#!/usr/bin/env python3
"""Programmatic primary-source audit and empirical MIR phase probe harness.

Compares `rustc_public` (StableMIR) and `rustc_public_bridge` against
`rustc_middle::mir` (`Runtime(PostCleanup)`) and `joshlf/anneal`'s
`trusted/rustc-capture` seam across pinned upstream `rust-lang/rust` revisions,
and optionally executes live `rustc -Zdump-mir=all` phase-separation probes on
`mir_phase_ub_probes.rs`.

Uses only the Python 3.10+ standard library. All emitted JSON paths are
repository-relative; host filesystem paths are never serialized.
"""

from __future__ import annotations

import argparse
import glob
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

CORE_BRIDGE_AND_STABLE_FILES = [
    "compiler/rustc_public/src/unstable/convert/stable/mir.rs",
    "compiler/rustc_public/src/unstable/convert/stable/ty.rs",
    "compiler/rustc_public/src/unstable/convert/stable/abi.rs",
    "compiler/rustc_public/src/unstable/convert/stable/mod.rs",
    "compiler/rustc_public_bridge/src/builder.rs",
    "compiler/rustc_public_bridge/src/alloc.rs",
    "compiler/rustc_public_bridge/src/context/impls.rs",
]

EXTRA_UPSTREAM_FILES = [
    "compiler/rustc_public/src/lib.rs",
    "compiler/rustc_public/src/mir/body.rs",
    "compiler/rustc_public/src/rustc_internal/mod.rs",
    "compiler/rustc_middle/src/mir/mod.rs",
    "compiler/rustc_middle/src/mir/syntax.rs",
    "compiler/rustc_middle/src/ty/mod.rs",
    "compiler/rustc_mir_transform/src/lib.rs",
    "compiler/rustc_mir_transform/src/remove_place_mention.rs",
    "compiler/rustc_mir_transform/src/remove_storage_markers.rs",
    "compiler/rustc_mir_transform/src/remove_zsts.rs",
    "compiler/rustc_mir_transform/src/unreachable_prop.rs",
    "compiler/rustc_mir_transform/src/gvn.rs",
    "compiler/rustc_session/src/config.rs",
]

DEFAULT_RUST_SNAPSHOTS = [
    ("anneal_pin_2026_05_30", "f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1"),
    ("baseline_2026_09_11", "49d734536222bf28bb6d07d885b3a81d145981da"),
    ("head_2026_11_22", "342d74463af7dd3018ef6aa04dd5500c2deb5bd1"),
]

TRAP_PATTERNS: dict[str, re.Pattern[str]] = {
    "unimplemented": re.compile(r"\bunimplemented!\s*\("),
    "todo": re.compile(r"\btodo!\s*\("),
    "bug": re.compile(r"\bbug!\s*\("),
    "unreachable": re.compile(r"\bunreachable!\s*\("),
    "opaque": re.compile(r"\bopaque\s*\("),
}

EXTRA_PANIC_PATTERN = re.compile(r"\bpanic!\s*\(")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def fetch_rust_snapshot(sha: str, dest: Path) -> None:
    """Fetch pinned rust-lang/rust files via raw.githubusercontent.com using curl."""
    for rel in CORE_BRIDGE_AND_STABLE_FILES + EXTRA_UPSTREAM_FILES:
        out = dest / rel
        if out.exists():
            continue
        out.parent.mkdir(parents=True, exist_ok=True)
        url = f"https://raw.githubusercontent.com/rust-lang/rust/{sha}/{rel}"
        proc = subprocess.run(
            ["curl", "-fsSL", "--retry", "3", "-o", str(out), url],
            capture_output=True,
            text=True,
            check=False,
        )
        if proc.returncode != 0:
            raise RuntimeError(f"failed to fetch {url}: {proc.stderr.strip()}")


def extract_braced_block(lines: list[str], header_re: str) -> list[tuple[int, str]]:
    rx = re.compile(header_re)
    for idx, line in enumerate(lines):
        if rx.match(line):
            out: list[tuple[int, str]] = []
            depth = 0
            started = False
            for j in range(idx, len(lines)):
                out.append((j + 1, lines[j]))
                depth += lines[j].count("{") - lines[j].count("}")
                if "{" in lines[j]:
                    started = True
                if started and depth == 0:
                    return out
    return []


def extract_struct_fields(lines: list[str], header_re: str) -> list[dict[str, Any]]:
    blk = extract_braced_block(lines, header_re)
    fields: list[dict[str, Any]] = []
    field_rx = re.compile(r"^\s*(pub(?:\([^)]+\))?)\s+([a-z_][a-z0-9_]*)\s*:\s*(.+?)\s*,?\s*$")
    for lineno, text in blk[1:-1]:
        m = field_rx.match(text)
        if m:
            fields.append(
                {
                    "line": lineno,
                    "visibility": m.group(1),
                    "name": m.group(2),
                    "type_excerpt": m.group(3).rstrip(","),
                }
            )
    return fields


def extract_enum_variants(lines: list[str], header_re: str) -> list[dict[str, Any]]:
    blk = extract_braced_block(lines, header_re)
    variants: list[dict[str, Any]] = []
    depth = 0
    for lineno, text in blk:
        if depth == 1:
            m = re.match(r"^\s*([A-Z][A-Za-z0-9_]*)\b", text)
            if m and not text.strip().startswith(("//", "#", "/*")):
                variants.append({"line": lineno, "variant": m.group(1)})
        depth += text.count("{") - text.count("}")
    return variants


def scan_trap_and_opaque(root: Path) -> dict[str, Any]:
    per_file: dict[str, Any] = {}
    line_totals = {k: 0 for k in TRAP_PATTERNS}
    occ_totals = {k: 0 for k in TRAP_PATTERNS}
    panic_total = 0

    for rel in CORE_BRIDGE_AND_STABLE_FILES:
        path = root / rel
        raw = path.read_bytes()
        lines = raw.decode("utf-8").splitlines()
        line_counts = {k: 0 for k in TRAP_PATTERNS}
        occ_counts = {k: 0 for k in TRAP_PATTERNS}
        hits: dict[str, list[dict[str, Any]]] = {}

        for key, rx in TRAP_PATTERNS.items():
            matched: list[dict[str, Any]] = []
            for lineno, line in enumerate(lines, 1):
                found = rx.findall(line)
                if found:
                    line_counts[key] += 1
                    occ_counts[key] += len(found)
                    matched.append({"line": lineno, "occurrences": len(found), "text": line.strip()})
            if matched:
                hits[key] = matched
            line_totals[key] += line_counts[key]
            occ_totals[key] += occ_counts[key]

        panic_hits = []
        for lineno, line in enumerate(lines, 1):
            if EXTRA_PANIC_PATTERN.search(line):
                panic_hits.append({"line": lineno, "text": line.strip()})
        panic_total += len(panic_hits)

        per_file[rel] = {
            "lines": len(lines),
            "sha256": sha256_bytes(raw),
            "line_hit_counts": line_counts,
            "occurrence_counts": occ_counts,
            "explicit_panic_count": len(panic_hits),
            "hits": hits,
            "explicit_panics": panic_hits,
        }

    return {
        "line_hit_totals": line_totals,
        "occurrence_totals": occ_totals,
        "explicit_panic_total": panic_total,
        "per_file_scan": per_file,
    }


def extract_terminator_arms(mir_rs_lines: list[str]) -> list[dict[str, Any]]:
    """Parse every arm of `impl Stable for mir::TerminatorKind` verbatim."""
    start = None
    for i, line in enumerate(mir_rs_lines):
        if "impl<'tcx> Stable<'tcx> for mir::TerminatorKind" in line:
            start = i
            break
    if start is None:
        return []

    block_lines: list[tuple[int, str]] = []
    depth = 0
    started = False
    for j in range(start, len(mir_rs_lines)):
        block_lines.append((j + 1, mir_rs_lines[j]))
        depth += mir_rs_lines[j].count("{") - mir_rs_lines[j].count("}")
        if "{" in mir_rs_lines[j]:
            started = True
        if started and depth == 0:
            break

    # Find `match self {` inside impl
    match_idx = None
    for k, (_, txt) in enumerate(block_lines):
        if "match self {" in txt:
            match_idx = k + 1
            break
    if match_idx is None:
        return []

    arms: list[dict[str, Any]] = []
    arm_re = re.compile(r"^\s*mir::TerminatorKind::([A-Za-z0-9_]+)(.*)$")
    k = match_idx
    while k < len(block_lines) - 2:
        lineno, txt = block_lines[k]
        m = arm_re.match(txt)
        if not m:
            k += 1
            continue
        variant = m.group(1)
        arm_start_line = lineno
        chunk_lines = [txt]
        k += 1
        while k < len(block_lines) - 2:
            _, next_txt = block_lines[k]
            if arm_re.match(next_txt) and not next_txt.lstrip().startswith("|"):
                break
            chunk_lines.append(next_txt)
            k += 1
        joined = "\n".join(chunk_lines)
        if "=>" in joined:
            lhs, rhs = joined.split("=>", 1)
        else:
            lhs, rhs = joined, ""
        lhs_clean = " ".join(lhs.split())
        rhs_clean = " ".join(rhs.split())
        dropped = re.findall(r"([a-z_][a-z0-9_]*)\s*:\s*_", lhs)
        if ".." in lhs and variant == "Goto":
            dropped.append("loop_hint_attrs (via ..)")
        if "(_)" in lhs and variant == "UnwindTerminate":
            dropped.append("UnwindTerminateReason (via (_))")
        if variant == "InlineAsm":
            if "targets.first()" in rhs:
                dropped.append("targets[1..] (multi-label asm_goto targets dropped)")
            if "format!(" in rhs:
                dropped.append("template/options/line_spans stringified via Debug")
        trap = None
        for macro in ("unimplemented!", "todo!", "unreachable!", "bug!"):
            if macro in rhs:
                trap = macro
                break
        target_variant = None
        tm = re.search(r"TerminatorKind::([A-Za-z0-9_]+)", rhs)
        if tm:
            target_variant = f"TerminatorKind::{tm.group(1)}"
        arms.append(
            {
                "line": arm_start_line,
                "middle_variant": variant,
                "pattern_head": lhs_clean[:160],
                "target_variant": target_variant,
                "trap": trap,
                "dropped_or_degraded": dropped,
                "rhs_head": rhs_clean[:120],
            }
        )
    return arms


def extract_builder_and_pipeline(root: Path) -> dict[str, Any]:
    builder_lines = (root / "compiler/rustc_public_bridge/src/builder.rs").read_text("utf-8").splitlines()
    impls_lines = (root / "compiler/rustc_public_bridge/src/context/impls.rs").read_text("utf-8").splitlines()
    mir_lib_lines = (root / "compiler/rustc_mir_transform/src/lib.rs").read_text("utf-8").splitlines()

    def find_lines(lines: list[str], needle: str) -> list[dict[str, Any]]:
        return [{"line": i, "text": l.strip()} for i, l in enumerate(lines, 1) if needle in l]

    # Classify exact pass placement in rustc_mir_transform/src/lib.rs
    cleanup_blk = extract_braced_block(mir_lib_lines, r"^fn run_runtime_cleanup_passes")
    opt_blk = extract_braced_block(mir_lib_lines, r"^pub\(crate\) fn run_optimization_passes")

    def find_in_block(blk: list[tuple[int, str]], needle: str) -> list[int]:
        return [ln for ln, txt in blk if needle in txt]

    tracked_passes = [
        ("RemovePlaceMention", "remove_place_mention::RemovePlaceMention"),
        ("CheckAlignment", "check_alignment::CheckAlignment"),
        ("CheckNull", "check_null::CheckNull"),
        ("CheckEnums", "check_enums::CheckEnums"),
        ("RemoveStorageMarkers", "remove_storage_markers::RemoveStorageMarkers"),
        ("RemoveZsts", "remove_zsts::RemoveZsts"),
        ("UnreachablePropagation", "unreachable_prop::UnreachablePropagation"),
        ("GVN", "gvn::GVN"),
    ]
    pass_placement: dict[str, Any] = {}
    for pname, needle in tracked_passes:
        in_cleanup = find_in_block(cleanup_blk, needle)
        in_opt = find_in_block(opt_blk, needle)
        pass_placement[pname] = {
            "in_run_runtime_cleanup_passes_lines": in_cleanup,
            "in_run_optimization_passes_lines": in_opt,
        }

    # Extract policy lines for key UB-erasing passes
    pass_policies: dict[str, list[dict[str, Any]]] = {}
    for pname, rel in [
        ("RemovePlaceMention", "compiler/rustc_mir_transform/src/remove_place_mention.rs"),
        ("RemoveStorageMarkers", "compiler/rustc_mir_transform/src/remove_storage_markers.rs"),
        ("RemoveZsts", "compiler/rustc_mir_transform/src/remove_zsts.rs"),
        ("UnreachablePropagation", "compiler/rustc_mir_transform/src/unreachable_prop.rs"),
        ("GVN", "compiler/rustc_mir_transform/src/gvn.rs"),
    ]:
        p = root / rel
        if p.exists():
            ls = p.read_text("utf-8").splitlines()
            pass_policies[pname] = [
                {"line": i, "text": l.strip()}
                for i, l in enumerate(ls, 1)
                if "PassPolicy::" in l or "is_enabled(" in l or "mir_opt_level()" in l or "mir_preserve_ub" in l
            ]

    return {
        "builder_instance_mir_calls": find_lines(builder_lines, "instance_mir"),
        "builder_reported_error_swallow": find_lines(builder_lines, "ErrorHandled::Reported"),
        "builder_too_generic_unreachable": find_lines(builder_lines, "ErrorHandled::TooGeneric"),
        "context_impls_mir_body_instance_mir": find_lines(impls_lines, "instance_mir"),
        "pass_placement_in_rustc_mir_transform": pass_placement,
        "pass_policies": pass_policies,
    }


def extract_struct_diffs(root: Path) -> dict[str, Any]:
    middle_mod = (root / "compiler/rustc_middle/src/mir/mod.rs").read_text("utf-8").splitlines()
    middle_syn = (root / "compiler/rustc_middle/src/mir/syntax.rs").read_text("utf-8").splitlines()
    public_body = (root / "compiler/rustc_public/src/mir/body.rs").read_text("utf-8").splitlines()

    m_body = extract_struct_fields(middle_mod, r"^pub struct Body<")
    p_body = extract_struct_fields(public_body, r"^pub struct Body\b")
    m_bb = extract_struct_fields(middle_mod, r"^pub struct BasicBlockData<")
    p_bb = extract_struct_fields(public_body, r"^pub struct BasicBlock\b")
    m_local = extract_struct_fields(middle_mod, r"^pub struct LocalDecl<")
    p_local = extract_struct_fields(public_body, r"^pub struct LocalDecl\b")
    m_scope = extract_struct_fields(middle_mod, r"^pub struct SourceScopeData<")
    p_scope = extract_struct_fields(public_body, r"^pub(?:\([^)]+\))?\s+struct SourceScopeInfo\b")
    m_asm = extract_enum_variants(middle_syn, r"^pub enum InlineAsmOperand<")
    p_asm = extract_struct_fields(public_body, r"^pub struct InlineAsmOperand\b")

    # Map semantic equivalents on Body (basic_blocks -> blocks, local_decls -> locals)
    body_name_map = {"basic_blocks": "blocks", "local_decls": "locals"}
    p_body_names = {f["name"] for f in p_body}
    dropped_body_fields = [
        f["name"]
        for f in m_body
        if body_name_map.get(f["name"], f["name"]) not in p_body_names
    ]

    p_bb_names = {f["name"] for f in p_bb}
    dropped_bb_fields = [f["name"] for f in m_bb if f["name"] not in p_bb_names]

    return {
        "Body": {
            "rustc_middle_count": len(m_body),
            "rustc_public_total_count": len(p_body),
            "rustc_public_pub_count": sum(1 for f in p_body if f["visibility"] == "pub"),
            "rustc_public_pub_crate_count": sum(1 for f in p_body if f["visibility"] != "pub"),
            "rustc_middle_fields": [f["name"] for f in m_body],
            "rustc_public_fields": [{"name": f["name"], "visibility": f["visibility"]} for f in p_body],
            "dropped_from_middle_Body": dropped_body_fields,
        },
        "BasicBlock": {
            "rustc_middle_fields": [f["name"] for f in m_bb],
            "rustc_public_fields": [f["name"] for f in p_bb],
            "dropped_from_BasicBlockData": dropped_bb_fields,
        },
        "LocalDecl": {
            "rustc_middle_fields": [f["name"] for f in m_local],
            "rustc_public_fields": [f["name"] for f in p_local],
        },
        "SourceScope": {
            "rustc_middle_fields": [f["name"] for f in m_scope],
            "rustc_public_fields": [f["name"] for f in p_scope],
        },
        "InlineAsmOperand": {
            "rustc_middle_variants": [v["variant"] for v in m_asm],
            "rustc_public_fields": [f["name"] for f in p_asm],
        },
    }


def audit_anneal(anneal_dir: Path) -> dict[str, Any]:
    capture_dir = anneal_dir / "trusted/rustc-capture"
    files = sorted(
        p.relative_to(anneal_dir).as_posix()
        for p in capture_dir.rglob("*")
        if p.is_file() and p.suffix in (".rs", ".toml")
    )
    uses_rustc_public = False
    extern_crates: list[str] = []
    compiler_version_pin = None
    fail_closed_hooks: list[dict[str, Any]] = []

    for rel in files:
        lines = (anneal_dir / rel).read_text("utf-8").splitlines()
        for lineno, line in enumerate(lines, 1):
            if "rustc_public" in line:
                uses_rustc_public = True
            m = re.match(r"^\s*extern crate\s+([a-z0-9_]+)\s*;", line)
            if m:
                extern_crates.append(m.group(1))
            mv = re.match(r'^\s*const COMPILER_VERSION\s*:\s*&str\s*=\s*"([^"]+)"', line)
            if mv:
                compiler_version_pin = mv.group(1)
            if any(tok in line for tok in ("has_errors()", "early_fatal", "analysis_reached")):
                if rel.endswith("driver.rs"):
                    fail_closed_hooks.append({"file": rel, "line": lineno, "text": line.strip()})

    mir_ast_path = anneal_dir / "trusted/lean/Trusted/MirAst.lean"
    mir_ast_lines = mir_ast_path.read_text("utf-8").splitlines()
    unsupported_ctors = [
        {"line": i, "text": l.strip()}
        for i, l in enumerate(mir_ast_lines, 1)
        if re.match(r"^\s*\|\s*unsupported\b", l)
    ]
    cleanup_lines = [
        {"line": i, "text": l.strip()}
        for i, l in enumerate(mir_ast_lines, 1)
        if "cleanup : Bool" in l or "BasicBlockData::is_cleanup" in l
    ]

    return {
        "files": files,
        "uses_rustc_public": uses_rustc_public,
        "linked_rustc_private_crates": sorted(set(extern_crates)),
        "compiler_version_pin": compiler_version_pin,
        "driver_fail_closed_hooks": fail_closed_hooks,
        "trusted_mir_ast_explicit_unsupported_constructors": unsupported_ctors,
        "trusted_mir_ast_cleanup_metadata": cleanup_lines,
    }


def run_rustc_mir_probes(rustc_bin: str, probe_rs: Path) -> dict[str, Any]:
    ver = subprocess.run([rustc_bin, "--version", "--verbose"], capture_output=True, text=True, check=True)
    version_lines = ver.stdout.strip().splitlines()
    version_map: dict[str, str] = {"summary": version_lines[0] if version_lines else ""}
    for line in version_lines[1:]:
        if ":" in line:
            k, v = line.split(":", 1)
            version_map[k.strip()] = v.strip()

    configs = [
        ("o0_default", ["-C", "opt-level=0"]),
        ("o2_default", ["-C", "opt-level=2"]),
        ("o0_preserve_ub", ["-C", "opt-level=0", "-Zmir-preserve-ub"]),
        ("o2_preserve_ub", ["-C", "opt-level=2", "-Zmir-preserve-ub"]),
        ("o0_mopt0_preserve_ub", ["-C", "opt-level=0", "-Zmir-opt-level=0", "-Zmir-preserve-ub"]),
        ("o2_mopt0_preserve_ub", ["-C", "opt-level=2", "-Zmir-opt-level=0", "-Zmir-preserve-ub"]),
    ]

    probe_fns = [
        "probe_zst_deref",
        "probe_div_zero_unchecked",
        "probe_div_zero_checked",
        "probe_place_mention",
        "probe_storage_markers",
        "probe_unreachable_prop",
        "probe_unwind_cleanup",
        "probe_unwind_abi_terminate",
    ]

    results_by_cfg: dict[str, Any] = {}
    with tempfile.TemporaryDirectory(prefix="rustc_mir_probe_") as td:
        td_path = Path(td)
        for cfg_name, flags in configs:
            dump_dir = td_path / cfg_name
            dump_dir.mkdir(parents=True, exist_ok=True)
            cmd = [
                rustc_bin,
                str(probe_rs),
                "--edition=2024",
                "--crate-name=probes",
                *flags,
                "-Zdump-mir=all",
                f"-Zdump-mir-dir={dump_dir}",
                "-o",
                str(dump_dir / "libprobes.rlib"),
            ]
            proc = subprocess.run(cmd, capture_output=True, text=True, check=False)
            if proc.returncode != 0:
                raise RuntimeError(f"rustc failed for {cfg_name}: {proc.stderr}")

            fn_reports: dict[str, Any] = {}
            for fn in probe_fns:
                post_files = sorted(glob.glob(str(dump_dir / f"probes.{fn}.*runtime-post-cleanup.after.mir")))
                opt_files = sorted(glob.glob(str(dump_dir / f"probes.{fn}.*runtime-optimized.after.mir")))
                post_text = Path(post_files[0]).read_text("utf-8") if post_files else ""
                opt_text = Path(opt_files[0]).read_text("utf-8") if opt_files else ""

                def metrics(txt: str) -> dict[str, Any]:
                    return {
                        "sha256": sha256_bytes(txt.encode("utf-8")),
                        "basic_block_count": len(re.findall(r"^\s*bb\d+(?:\s+\(cleanup\))?:", txt, re.M)),
                        "cleanup_block_count": len(re.findall(r"^\s*bb\d+\s+\(cleanup\):", txt, re.M)),
                        "has_arg1_deref_read": "copy (*_1)" in txt or "move (*_1)" in txt,
                        "has_arg1_zst_write": "(*_1) = ()" in txt,
                        "has_div_op": "Div(" in txt,
                        "has_place_mention": "PlaceMention(" in txt,
                        "storage_live_count": len(re.findall(r"\bStorageLive\(", txt)),
                        "storage_dead_count": len(re.findall(r"\bStorageDead\(", txt)),
                        "has_assume": "assume(" in txt,
                        "has_unreachable_unchecked_call": "unreachable_unchecked(" in txt,
                        "has_terminate_cleanup": "terminate(cleanup)" in txt,
                        "has_terminate_abi": "terminate(abi)" in txt,
                        "ub_check_assert_count": len(
                            re.findall(r"misaligned pointer dereference|null pointer dereference", txt)
                        ),
                    }

                def strip_header(txt: str) -> str:
                    lines = txt.splitlines()
                    if lines and lines[0].startswith("// MIR for "):
                        return "\n".join(lines[1:])
                    return txt

                fn_reports[fn] = {
                    "post_cleanup": metrics(post_text),
                    "optimized": metrics(opt_text),
                    "mir_body_identical_post_vs_opt": strip_header(post_text) == strip_header(opt_text),
                }
            results_by_cfg[cfg_name] = {
                "flags": flags,
                "functions": fn_reports,
            }

    return {
        "rustc_version": version_map,
        "probe_source_relpath": "support/mir_phase_ub_probes.rs",
        "probe_source_sha256": sha256_bytes(probe_rs.read_bytes()),
        "configurations": results_by_cfg,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--rust-tree",
        action="append",
        default=[],
        help="Pinned rust-lang/rust source tree spec in format label:40hexsha:path",
    )
    parser.add_argument(
        "--fetch-github",
        action="store_true",
        help="Fetch the default 3 pinned rust-lang/rust snapshots from GitHub into a temporary directory",
    )
    parser.add_argument(
        "--anneal-dir",
        type=Path,
        default=None,
        help="Path to joshlf/anneal checkout for trusted/rustc-capture contrast",
    )
    parser.add_argument(
        "--anneal-sha",
        default="c131b320eeeb26ef692e5afd5ec8db49ee518613",
        help="Pinned 40-hex SHA of the joshlf/anneal checkout",
    )
    parser.add_argument(
        "--rustc",
        default=None,
        help="Path to nightly rustc binary for live MIR phase-separation probes",
    )
    parser.add_argument(
        "--probe-rs",
        type=Path,
        default=Path(__file__).resolve().parent / "mir_phase_ub_probes.rs",
        help="Path to mir_phase_ub_probes.rs",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path(__file__).resolve().parent / "audit_results.json",
        help="Path to write path-scrubbed JSON output",
    )
    args = parser.parse_args()

    with tempfile.TemporaryDirectory(prefix="rustc_public_audit_") as tmp:
        trees: list[tuple[str, str, Path]] = []
        if args.rust_tree:
            for spec in args.rust_tree:
                label, sha, p = spec.split(":", 2)
                trees.append((label, sha, Path(p)))
        elif args.fetch_github:
            for label, sha in DEFAULT_RUST_SNAPSHOTS:
                dest = Path(tmp) / label
                fetch_rust_snapshot(sha, dest)
                trees.append((label, sha, dest))
        else:
            parser.error("provide at least one --rust-tree label:sha:path or --fetch-github")

        snapshots: dict[str, Any] = {}
        for label, sha, root in trees:
            mir_lines = (root / "compiler/rustc_public/src/unstable/convert/stable/mir.rs").read_text("utf-8").splitlines()
            snapshots[label] = {
                "repository": "rust-lang/rust",
                "revision": sha,
                "trap_and_opaque_audit": scan_trap_and_opaque(root),
                "struct_field_comparison": extract_struct_diffs(root),
                "terminator_conversion_arms": extract_terminator_arms(mir_lines),
                "builder_and_pipeline_audit": extract_builder_and_pipeline(root),
            }

        cross_version_summary = {
            label: {
                "revision": data["revision"],
                "line_hit_totals": data["trap_and_opaque_audit"]["line_hit_totals"],
                "occurrence_totals": data["trap_and_opaque_audit"]["occurrence_totals"],
                "explicit_panic_total": data["trap_and_opaque_audit"]["explicit_panic_total"],
                "dropped_body_field_count": len(data["struct_field_comparison"]["Body"]["dropped_from_middle_Body"]),
                "dropped_basic_block_fields": data["struct_field_comparison"]["BasicBlock"]["dropped_from_BasicBlockData"],
                "terminator_arm_count": len(data["terminator_conversion_arms"]),
            }
            for label, data in snapshots.items()
        }

        report: dict[str, Any] = {
            "schema": "rustc-public-vs-middle-mir-audit/1",
            "cross_version_summary": cross_version_summary,
            "rust_lang_rust_snapshots": snapshots,
        }

        if args.anneal_dir is not None:
            report["anneal_rustc_capture_contrast"] = {
                "repository": "joshlf/anneal",
                "revision": args.anneal_sha,
                **audit_anneal(args.anneal_dir),
            }

        if args.rustc is not None:
            report["live_rustc_mir_phase_probes"] = run_rustc_mir_probes(args.rustc, args.probe_rs)

        args.output.write_text(json.dumps(report, indent=2, sort_keys=False) + "\n", encoding="utf-8")
        print(f"Wrote {args.output} ({args.output.stat().st_size} bytes)")
        print(json.dumps(cross_version_summary, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
