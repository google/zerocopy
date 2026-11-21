#!/usr/bin/env python3
"""Verify all pinned 40-hex commits and cited upstream file paths against raw.githubusercontent.com
(and local git object database for private/local mirrors when unauthenticated HTTP returns 404).
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
        "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65",
        [
            "compiler/rustc_const_eval/src/interpret/eval_context.rs",
            "compiler/rustc_const_eval/src/interpret/step.rs",
            "compiler/rustc_const_eval/src/interpret/place.rs",
            "compiler/rustc_const_eval/src/interpret/memory.rs",
            "compiler/rustc_const_eval/src/interpret/operator.rs",
            "compiler/rustc_const_eval/src/interpret/validity.rs",
            "compiler/rustc_const_eval/src/interpret/intern.rs",
            "compiler/rustc_const_eval/src/const_eval/machine.rs",
            "compiler/rustc_const_eval/src/const_eval/eval_queries.rs",
            "compiler/rustc_const_eval/src/const_eval/dummy_machine.rs",
            "compiler/rustc_middle/src/mir/interpret/pointer.rs",
            "compiler/rustc_middle/src/mir/consts.rs",
            "compiler/rustc_mir_transform/src/lib.rs",
            "compiler/rustc_mir_transform/src/ctfe_limit.rs",
            "compiler/rustc_mir_transform/src/promote_consts.rs",
            "compiler/rustc_mir_transform/src/gvn.rs",
            "compiler/rustc_mir_transform/src/instsimplify.rs",
            "compiler/rustc_monomorphize/src/collector.rs",
            "compiler/rustc_codegen_llvm/src/intrinsic.rs",
            "library/core/src/intrinsics/mod.rs",
            "library/core/src/str/validations.rs",
            "library/core/src/ptr/const_ptr.rs",
            "library/core/src/ub_checks.rs",
            "src/tools/miri/src/intrinsics/mod.rs",
        ],
    ),
    (
        "rust-lang/rust",
        "58cf8f9c35b355199727627d07ae34a4e2846d67",
        [
            "library/core/src/intrinsics/mod.rs",
            "library/core/src/num/uint_macros.rs",
            "library/core/src/num/int_macros.rs",
        ],
    ),
    (
        "rust-lang/rust",
        "3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1",
        [
            "compiler/rustc_const_eval/src/const_eval/machine.rs",
            "compiler/rustc_const_eval/src/interpret/intern.rs",
            "compiler/rustc_const_eval/src/interpret/validity.rs",
            "compiler/rustc_mir_transform/src/promote_consts.rs",
            "compiler/rustc_mir_transform/src/gvn.rs",
        ],
    ),
    (
        "rust-lang/reference",
        "ad35aca481751a06afeb23820a672b0f3b11a476",
        [
            "src/const_eval.md",
            "src/items/constant-items.md",
            "src/items/static-items.md",
            "src/destructors.md",
        ],
    ),
    (
        "joshlf/anneal",
        "c131b320eeeb26ef692e5afd5ec8db49ee518613",
        [
            "trusted/lean/Trusted/MirAst.lean",
            "trusted/lean/Trusted/MirSemantics.lean",
            "trusted/audit/TrustedBoundary.lean",
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
