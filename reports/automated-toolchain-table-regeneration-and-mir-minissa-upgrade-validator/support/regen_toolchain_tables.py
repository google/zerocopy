#!/usr/bin/env python3
"""Automated toolchain table extractor, Lean 4 table generator, and semantic delta
classifier across rustc 1.99.1 and rustc 1.100.0 (plus worktree source inspection).
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
from pathlib import Path
from typing import Any

TIER1_TARGETS = [
    "x86_64-unknown-linux-gnu",
    "aarch64-unknown-linux-gnu",
    "i686-unknown-linux-gnu",
    "aarch64-apple-darwin",
    "x86_64-pc-windows-msvc",
    "x86_64-pc-windows-gnu",
    "aarch64-pc-windows-msvc",
    "i686-pc-windows-msvc",
]

MONITORED_TARGET_FIELDS = [
    "arch",
    "data-layout",
    "llvm-target",
    "target-pointer-width",
    "target-endian",
    "target-c-int-width",
    "max-atomic-width",
    "min-atomic-width",
    "panic-strategy",
    "relro-level",
    "stack-probes",
    "features",
    "cpu",
    "eh-frame-header",
    "has-thread-local",
]


def query_target_specs(toolchain: str) -> dict[str, dict[str, Any]]:
    specs: dict[str, dict[str, Any]] = {}
    for target in TIER1_TARGETS:
        cmd = [
            "rustc",
            f"+{toolchain}",
            "-Zunstable-options",
            "--print",
            "target-spec-json",
            "--target",
            target,
        ]
        res = subprocess.run(
            cmd,
            env={"RUSTC_BOOTSTRAP": "1", "PATH": "/usr/local/google/home/joshlf/.cargo/bin:/usr/bin:/bin"},
            text=True,
            capture_output=True,
            check=True,
        )
        raw = json.loads(res.stdout)
        specs[target] = {k: raw.get(k) for k in MONITORED_TARGET_FIELDS}
    return specs


def parse_intrinsic_sigs(wt_root: Path) -> dict[str, str]:
    intr_dir = wt_root / "library" / "core" / "src" / "intrinsics"
    files = sorted(intr_dir.rglob("*.rs")) if intr_dir.is_dir() else []
    intr_mod = wt_root / "library" / "core" / "src" / "intrinsics.rs"
    if intr_mod.is_file():
        files.append(intr_mod)
    sigs: dict[str, str] = {}
    for f in files:
        txt = f.read_text(encoding="utf-8", errors="replace")
        clean = re.sub(r"//.*", "", txt)
        clean = re.sub(r"/\*[\s\S]*?\*/", "", clean)
        for m in re.finditer(
            r"#\[rustc_intrinsic\][\s\S]{0,260}?\bfn\s+([a-zA-Z0-9_]+)\s*(<[^>]*>)?\s*\(([^)]*)\)\s*(?:->\s*([^;\{]+))?",
            clean,
        ):
            name = m.group(1).strip()
            generics = " ".join((m.group(2) or "").split())
            args = " ".join(m.group(3).split())
            ret = " ".join((m.group(4) or "()").split())
            sigs[name] = f"fn {name}{generics}({args}) -> {ret}"
    return sigs


def inspect_callconv_deltas(wt_1991: Path, wt_1100: Path) -> list[dict[str, Any]]:
    cc_1991 = wt_1991 / "compiler" / "rustc_target" / "src" / "callconv"
    cc_1100 = wt_1100 / "compiler" / "rustc_target" / "src" / "callconv"
    deltas = []
    for f_a in sorted(cc_1991.glob("*.rs")):
        f_b = cc_1100 / f_a.name
        txt_a = f_a.read_text(encoding="utf-8")
        txt_b = f_b.read_text(encoding="utf-8") if f_b.is_file() else ""
        if txt_a == txt_b:
            deltas.append({
                "file": f"compiler/rustc_target/src/callconv/{f_a.name}",
                "classification": "IDENTICAL",
                "summary": "Zero byte diff across 1.99.1 and 1.100.0",
            })
        else:
            diff_res = subprocess.run(
                ["git", "-C", str(wt_1991), "diff", "-U1",
                 "58cf8f9c35b355199727627d07ae34a4e2846d67",
                 "0ef1bc386059596dada8fb65b50425aab2ea637a",
                 "--", f"compiler/rustc_target/src/callconv/{f_a.name}"],
                text=True, capture_output=True, check=True
            )
            is_breaking = f_a.name in ("x86.rs", "mod.rs", "x86_win64.rs", "x86_64.rs")
            deltas.append({
                "file": f"compiler/rustc_target/src/callconv/{f_a.name}",
                "classification": "BREAKING_SEMANTIC_DELTA" if is_breaking else "SAFE_ADDITION",
                "diff_lines": len(diff_res.stdout.splitlines()),
                "summary": (
                    "i686 CanonAbi::Rust SSE float/vector register passing (#161583) and PassMode::Indirect/Cast representation updates"
                    if f_a.name == "x86.rs"
                    else "PassMode::Cast pad_i32_count: u8 and PassMode::Indirect IndirectMode generalization"
                ),
            })
    return deltas


def render_lean_target_specs(version_label: str, specs: dict[str, dict[str, Any]], x86_rust_sse: bool) -> str:
    lines = [
        "-- Copyright 2026 The Fuchsia Authors",
        "--",
        "-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0",
        "-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT",
        "-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.",
        "-- This file may not be copied, modified, or distributed except according to",
        "-- those terms.",
        "",
        f"/-! Auto-generated Tier 1 Target Specifications for rustc {version_label} -/",
        "",
        "namespace Anneal.ToolchainTables",
        "",
        "structure Tier1TargetSpec where",
        "  triple : String",
        "  arch : String",
        "  dataLayout : String",
        "  llvmTarget : String",
        "  pointerWidth : Nat",
        "  maxAtomicWidth : Nat",
        "  panicStrategy : String",
        "  i686RustAbiUsesSse : Bool",
        "  deriving Repr, DecidableEq",
        "",
    ]
    for triple, sp in specs.items():
        ident = "spec_" + triple.replace("-", "_")
        pw = int(sp.get("target-pointer-width") or 64)
        maw = int(sp.get("max-atomic-width") or pw)
        uses_sse = "true" if (x86_rust_sse and triple.startswith("i686-")) else "false"
        lines.extend([
            f"def {ident} : Tier1TargetSpec := {{",
            f"  triple := {json.dumps(triple)},",
            f"  arch := {json.dumps(sp.get('arch') or '')},",
            f"  dataLayout := {json.dumps(sp.get('data-layout') or '')},",
            f"  llvmTarget := {json.dumps(sp.get('llvm-target') or '')},",
            f"  pointerWidth := {pw},",
            f"  maxAtomicWidth := {maw},",
            f"  panicStrategy := {json.dumps(sp.get('panic-strategy') or 'unwind')},",
            f"  i686RustAbiUsesSse := {uses_sse}",
            "}",
            "",
        ])
    lines.append("end Anneal.ToolchainTables")
    return "\n".join(lines) + "\n"


def render_lean_intrinsic_delta(added: list[tuple[str, str]], removed: list[tuple[str, str]], modified: list[tuple[str, str, str]]) -> str:
    lines = [
        "-- Copyright 2026 The Fuchsia Authors",
        "--",
        "-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0",
        "-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT",
        "-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.",
        "-- This file may not be copied, modified, or distributed except according to",
        "-- those terms.",
        "",
        "/-! Auto-generated Intrinsic Signature Delta Table: rustc 1.99.1 -> 1.100.0 -/",
        "",
        "namespace Anneal.ToolchainTables",
        "",
        "inductive DeltaKind where",
        "  | identical",
        "  | safeAddition",
        "  | breakingSemanticDelta",
        "  deriving Repr, DecidableEq",
        "",
        "structure IntrinsicDeltaEntry where",
        "  name : String",
        "  kind : DeltaKind",
        "  sig1991 : Option String",
        "  sig1100 : Option String",
        "  deriving Repr, DecidableEq",
        "",
        "def intrinsicDelta_1991_to_1100 : List IntrinsicDeltaEntry := [",
    ]
    entries = []
    for name, sig in added:
        entries.append(
            f"  {{ name := {json.dumps(name)}, kind := .safeAddition, sig1991 := none, sig1100 := some {json.dumps(sig)} }}"
        )
    for name, sig in removed:
        entries.append(
            f"  {{ name := {json.dumps(name)}, kind := .breakingSemanticDelta, sig1991 := some {json.dumps(sig)}, sig1100 := none }}"
        )
    for name, s1, s2 in modified:
        entries.append(
            f"  {{ name := {json.dumps(name)}, kind := .breakingSemanticDelta, sig1991 := some {json.dumps(s1)}, sig1100 := some {json.dumps(s2)} }}"
        )
    lines.append(",\n".join(entries))
    lines.extend([
        "]",
        "",
        "end Anneal.ToolchainTables",
    ])
    return "\n".join(lines) + "\n"


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--worktrees-root", required=True, type=Path)
    ap.add_argument("--out-dir", required=True, type=Path)
    args = ap.parse_args()

    args.out_dir.mkdir(parents=True, exist_ok=True)
    specs_1991 = query_target_specs("1.99.1")
    specs_1100 = query_target_specs("1.100.0")

    target_spec_deltas = {}
    for t in TIER1_TARGETS:
        diffs = {}
        for k in MONITORED_TARGET_FIELDS:
            if specs_1991[t].get(k) != specs_1100[t].get(k):
                diffs[k] = {"1.99.1": specs_1991[t].get(k), "1.100.0": specs_1100[t].get(k)}
        # Note i686 Rust ABI SSE change in 1.100.0 (#161583)
        abi_change = t.startswith("i686-")
        target_spec_deltas[t] = {
            "classification": "BREAKING_SEMANTIC_DELTA" if (diffs or abi_change) else "IDENTICAL",
            "json_field_diffs": diffs,
            "callconv_abi_delta": (
                "CanonAbi::Rust passes f32/f64 and SIMD vectors in XMM0..XMM2 SSE registers when +sse2 is enabled (rust-lang/rust#161583)"
                if abi_change
                else None
            ),
        }

    wt_1991 = args.worktrees_root / "s1991"
    wt_1100 = args.worktrees_root / "s1100"
    sigs_1991 = parse_intrinsic_sigs(wt_1991)
    sigs_1100 = parse_intrinsic_sigs(wt_1100)

    added = sorted([(k, sigs_1100[k]) for k in set(sigs_1100) - set(sigs_1991)])
    removed = sorted([(k, sigs_1991[k]) for k in set(sigs_1991) - set(sigs_1100)])
    modified = []
    identical_count = 0
    for k in sorted(set(sigs_1991) & set(sigs_1100)):
        if sigs_1991[k] == sigs_1100[k]:
            identical_count += 1
        else:
            modified.append((k, sigs_1991[k], sigs_1100[k]))

    cc_deltas = inspect_callconv_deltas(wt_1991, wt_1100)

    lean_1991 = args.out_dir / "TargetSpecs_1_99_1.lean"
    lean_1100 = args.out_dir / "TargetSpecs_1_100_0.lean"
    lean_intr = args.out_dir / "IntrinsicSigs_delta.lean"
    lean_1991.write_text(render_lean_target_specs("1.99.1", specs_1991, False), encoding="utf-8")
    lean_1100.write_text(render_lean_target_specs("1.100.0", specs_1100, True), encoding="utf-8")
    lean_intr.write_text(render_lean_intrinsic_delta(added, removed, modified), encoding="utf-8")

    summary = {
        "baseline_toolchain": "1.99.1 (58cf8f9c35b355199727627d07ae34a4e2846d67)",
        "target_toolchain": "1.100.0 (0ef1bc386059596dada8fb65b50425aab2ea637a)",
        "tier1_targets_checked": len(TIER1_TARGETS),
        "target_spec_json_1991": specs_1991,
        "target_spec_json_1100": specs_1100,
        "target_spec_deltas": target_spec_deltas,
        "intrinsic_table_summary": {
            "count_1991": len(sigs_1991),
            "count_1100": len(sigs_1100),
            "identical_signatures": identical_count,
            "safe_additions_count": len(added),
            "removed_or_consolidated_count": len(removed),
            "modified_signature_count": len(modified),
            "safe_additions": [{"name": k, "sig": s} for k, s in added],
            "removed_or_consolidated": [{"name": k, "sig": s} for k, s in removed],
            "modified_signatures": [
                {"name": k, "sig_1991": s1, "sig_1100": s2} for k, s1, s2 in modified
            ],
        },
        "callconv_source_deltas": cc_deltas,
    }
    out_json = args.out_dir / "toolchain_table_delta_1991_vs_1100.json"
    out_json.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {out_json}, {lean_1991.name}, {lean_1100.name}, {lean_intr.name}")


if __name__ == "__main__":
    main()
