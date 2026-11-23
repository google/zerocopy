#!/usr/bin/env python3
"""Verify all pinned 40-hex commits and cited upstream file paths against raw.githubusercontent.com
(falling back to a local git object database when unauthenticated HTTP returns 404 for private repos).
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys


PINNED_TARGETS: list[tuple[str, str, list[str]]] = [
    (
        "rust-lang/rust",
        "0259d5e9a81c6af08e40f8c204f2c0c41dca1647",
        [
            "compiler/rustc_attr_parsing/src/safety.rs",
            "compiler/rustc_attr_parsing/src/attributes/codegen_attrs.rs",
            "compiler/rustc_attr_parsing/src/attributes/link_attrs.rs",
            "compiler/rustc_attr_parsing/src/diagnostics.rs",
            "compiler/rustc_attr_parsing/src/interface.rs",
            "compiler/rustc_passes/src/check_attr.rs",
            "compiler/rustc_passes/src/reachable.rs",
            "compiler/rustc_codegen_llvm/src/consts.rs",
            "compiler/rustc_codegen_llvm/src/base.rs",
            "compiler/rustc_codegen_ssa/src/back/symbol_export.rs",
            "compiler/rustc_codegen_ssa/src/codegen_attrs.rs",
            "compiler/rustc_middle/src/middle/codegen_fn_attrs.rs",
            "compiler/rustc_symbol_mangling/src/lib.rs",
            "compiler/rustc_hir_analysis/src/check/check.rs",
            "compiler/rustc_hir_analysis/src/check/wfcheck.rs",
            "compiler/rustc_const_eval/src/interpret/intern.rs",
            "compiler/rustc_lint/src/builtin.rs",
            "compiler/rustc_lint_defs/src/builtin.rs",
        ],
    ),
    (
        "rust-lang/rust",
        "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65",
        [
            "compiler/rustc_attr_parsing/src/safety.rs",
            "compiler/rustc_attr_parsing/src/attributes/codegen_attrs.rs",
            "compiler/rustc_attr_parsing/src/attributes/link_attrs.rs",
            "compiler/rustc_passes/src/check_attr.rs",
            "compiler/rustc_codegen_llvm/src/consts.rs",
            "compiler/rustc_codegen_ssa/src/back/symbol_export.rs",
            "compiler/rustc_codegen_ssa/src/codegen_attrs.rs",
            "compiler/rustc_hir_analysis/src/check/check.rs",
            "compiler/rustc_const_eval/src/interpret/intern.rs",
            "compiler/rustc_lint/src/builtin.rs",
        ],
    ),
    (
        "llvm/llvm-project",
        "fc4aad7b5db3fff421df9a9637605b9ca5667881",
        [
            "llvm/lib/Target/TargetLoweringObjectFile.cpp",
            "llvm/lib/CodeGen/TargetLoweringObjectFileImpl.cpp",
        ],
    ),
    (
        "llvm/llvm-project",
        "229f673cd9cd804c579440dbd6e9cc0509f3a3c3",
        [
            "llvm/lib/Target/TargetLoweringObjectFile.cpp",
            "llvm/lib/CodeGen/TargetLoweringObjectFileImpl.cpp",
        ],
    ),
    (
        "rust-lang/llvm-project",
        "08c84e69a84d95936296dfcab0e38b34100725d5",
        [
            "llvm/lib/Target/TargetLoweringObjectFile.cpp",
            "llvm/lib/CodeGen/TargetLoweringObjectFileImpl.cpp",
        ],
    ),
    (
        "rust-lang/reference",
        "c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c",
        [
            "src/items/static-items.md",
            "src/abi.md",
            "src/attributes/codegen.md",
        ],
    ),
    (
        "joshlf/anneal",
        "c131b320eeeb26ef692e5afd5ec8db49ee518613",
        [
            "trusted/lean/Trusted/MirAst.lean",
            "trusted/lean/Trusted/MirSemantics.lean",
            "trusted/audit/TrustedBoundary.lean",
            "trusted/rustc-capture/src/driver.rs",
        ],
    ),
    (
        "leanprover/lean4",
        "5045d0056413266e57c625dcd7c365b10e377c52",
        [
            "src/Init/Prelude.lean",
        ],
    ),
]


def fetch_raw_github(repo: str, rev: str, rel_path: str) -> bytes | None:
    url = f"https://raw.githubusercontent.com/{repo}/{rev}/{rel_path}"
    proc = subprocess.run(
        ["curl", "-fsSL", "-H", "Accept-Encoding: gzip", "--compressed", url],
        capture_output=True,
        timeout=45,
    )
    if proc.returncode == 0 and proc.stdout:
        return proc.stdout
    return None


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", default=None, help="Output JSON receipt path")
    parser.add_argument(
        "--local-anneal-git",
        default=None,
        help="Optional local git checkout of joshlf/anneal when running without private GitHub token",
    )
    args = parser.parse_args()

    support_dir = Path(__file__).resolve().parent
    out_path = Path(args.out).resolve() if args.out else (support_dir / "pin_receipt.json")

    verified_files: list[dict[str, object]] = []
    failures: list[str] = []

    for repo, rev, paths in PINNED_TARGETS:
        for rel in paths:
            data = fetch_raw_github(repo, rev, rel)
            source_kind = "raw.githubusercontent.com"
            if data is None and repo == "joshlf/anneal" and args.local_anneal_git:
                git_proc = subprocess.run(
                    ["git", "-C", args.local_anneal_git, "show", f"{rev}:{rel}"],
                    capture_output=True,
                )
                if git_proc.returncode == 0:
                    data = git_proc.stdout
                    source_kind = "git-object-store"
            if data is None:
                failures.append(f"{repo}@{rev}:{rel}")
            else:
                verified_files.append(
                    {
                        "repository": repo,
                        "revision": rev,
                        "path": rel,
                        "bytes": len(data),
                        "sha256": hashlib.sha256(data).hexdigest(),
                        "resolved_via": source_kind,
                    }
                )

    receipt = {
        "commits_checked": len(PINNED_TARGETS),
        "files_checked": len(verified_files) + len(failures),
        "files_verified": len(verified_files),
        "all_verified": len(failures) == 0,
        "failures": failures,
        "entries": verified_files,
    }
    out_path.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print(
        f"Verified {len(verified_files)}/{len(verified_files) + len(failures)} pinned files across {len(PINNED_TARGETS)} commits."
    )
    if failures:
        for f in failures:
            print(f"  MISSING: {f}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
