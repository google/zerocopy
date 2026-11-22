#!/usr/bin/env python3
"""Verify every upstream repository commit pin and cited file path for this report.

Resolves every 40-hex commit SHA recorded in `../REPORT.json` via `gh api` (verifying that
GitHub returns the exact pinned SHA) and checks HTTP status codes for all cited upstream
files at those revisions on `raw.githubusercontent.com` (including confirming expected 404
paths such as `compiler/rustc_mir_transform/src/util.rs`).

Usage:
    python3 support/verify_pins.py --gh "gh" --out support/pin_receipt.json
"""

from __future__ import annotations

import argparse
import datetime
import json
import re
import shlex
import subprocess
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent

CITED_FILES: list[tuple[str, str, str, int]] = [
    # (repository, revision, path, expected_http_status)
    ("rust-lang/rust", "ce66487ebbd7541212d22d01c39a808057d69f1f", "compiler/rustc_mir_transform/src/check_packed_ref.rs", 200),
    ("rust-lang/rust", "ce66487ebbd7541212d22d01c39a808057d69f1f", "compiler/rustc_mir_transform/src/add_moves_for_packed_drops.rs", 200),
    ("rust-lang/rust", "ce66487ebbd7541212d22d01c39a808057d69f1f", "compiler/rustc_mir_transform/src/util.rs", 404),
    ("rust-lang/rust", "ce66487ebbd7541212d22d01c39a808057d69f1f", "compiler/rustc_const_eval/src/util/alignment.rs", 200),
    ("rust-lang/rust", "ce66487ebbd7541212d22d01c39a808057d69f1f", "compiler/rustc_mir_transform/src/remove_uninit_drops.rs", 200),
    ("rust-lang/rust", "ce66487ebbd7541212d22d01c39a808057d69f1f", "compiler/rustc_mir_transform/src/elaborate_drops.rs", 200),
    ("rust-lang/rust", "ce66487ebbd7541212d22d01c39a808057d69f1f", "compiler/rustc_mir_transform/src/elaborate_drop.rs", 200),
    ("rust-lang/rust", "ce66487ebbd7541212d22d01c39a808057d69f1f", "compiler/rustc_mir_transform/src/lib.rs", 200),
    ("rust-lang/rust", "ce66487ebbd7541212d22d01c39a808057d69f1f", "compiler/rustc_mir_transform/src/shim.rs", 200),
    ("rust-lang/rust", "ce66487ebbd7541212d22d01c39a808057d69f1f", "compiler/rustc_mir_transform/src/check_alignment.rs", 200),
    ("rust-lang/rust", "ce66487ebbd7541212d22d01c39a808057d69f1f", "compiler/rustc_mir_transform/src/check_pointers.rs", 200),
    ("rust-lang/rust", "ce66487ebbd7541212d22d01c39a808057d69f1f", "compiler/rustc_mir_transform/src/diagnostics.rs", 200),
    ("rust-lang/rust", "ce66487ebbd7541212d22d01c39a808057d69f1f", "compiler/rustc_const_eval/src/check_consts/post_drop_elaboration.rs", 200),
    ("rust-lang/rust", "ce66487ebbd7541212d22d01c39a808057d69f1f", "compiler/rustc_middle/src/mir/visit.rs", 200),
    ("rust-lang/rust", "ce66487ebbd7541212d22d01c39a808057d69f1f", "compiler/rustc_mir_dataflow/src/move_paths/builder.rs", 200),
    ("rust-lang/rust", "ce66487ebbd7541212d22d01c39a808057d69f1f", "compiler/rustc_hir_analysis/src/check/wfcheck.rs", 200),
    ("rust-lang/rust", "ce66487ebbd7541212d22d01c39a808057d69f1f", "library/core/src/ptr/mod.rs", 200),
    ("rust-lang/rust", "3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1", "compiler/rustc_mir_transform/src/check_packed_ref.rs", 200),
    ("rust-lang/rust", "3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1", "compiler/rustc_mir_transform/src/add_moves_for_packed_drops.rs", 200),
    ("rust-lang/rust", "3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1", "compiler/rustc_const_eval/src/util/alignment.rs", 200),
    ("rust-lang/rust", "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65", "compiler/rustc_mir_transform/src/check_packed_ref.rs", 200),
    ("rust-lang/rust", "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65", "compiler/rustc_mir_transform/src/add_moves_for_packed_drops.rs", 200),
    ("rust-lang/rust", "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65", "compiler/rustc_const_eval/src/util/alignment.rs", 200),
    ("rust-lang/rust", "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65", "compiler/rustc_mir_transform/src/errors.rs", 200),
    ("rust-lang/rust", "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65", "library/core/src/ptr/mod.rs", 200),
    ("rust-lang/reference", "c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c", "src/type-layout.md", 200),
    ("rust-lang/reference", "c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c", "src/behavior-considered-undefined.md", 200),
    ("rust-lang/reference", "c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c", "src/destructors.md", 200),
    ("joshlf/anneal", "c131b320eeeb26ef692e5afd5ec8db49ee518613", "trusted/lean/Trusted/MirAst.lean", 200),
    ("joshlf/anneal", "c131b320eeeb26ef692e5afd5ec8db49ee518613", "trusted/lean/Trusted/MirSemantics.lean", 200),
]


def http_status(url: str) -> int | None:
    try:
        proc = subprocess.run(
            ["curl", "-sS", "-L", "--retry", "3", "--retry-delay", "1", "-m", "45", "-o", "/dev/null", "-w", "%{http_code}", url],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        code = proc.stdout.strip()
        return int(code) if code.isdigit() and code != "000" else None
    except OSError:
        return None


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--gh", default="gh", help="GitHub CLI command prefix")
    ap.add_argument("--out", default=str(HERE / "pin_receipt.json"))
    args = ap.parse_args(argv)
    gh = shlex.split(args.gh)

    report = json.loads((HERE.parent / "REPORT.json").read_text())
    ok = True
    commits: list[dict[str, Any]] = []
    for subject in report["subjects"]:
        ident = subject["identity"]
        repo, rev = ident.get("repository"), ident.get("revision")
        if not repo or not rev:
            continue
        entry: dict[str, Any] = {
            "repository": repo,
            "pinned_revision": rev,
            "is_40_hex": bool(re.fullmatch(r"[0-9a-f]{40}", rev)),
        }
        proc = subprocess.run(
            gh + ["api", f"repos/{repo}/commits/{rev}"],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        try:
            data = json.loads(proc.stdout)
            entry["api_sha"] = data.get("sha")
            entry["committer_date"] = data.get("commit", {}).get("committer", {}).get("date")
            entry["subject_line"] = (data.get("commit", {}).get("message") or "").splitlines()[0][:100]
        except ValueError:
            entry["api_sha"] = None
            entry["error"] = "no JSON from API call"
        entry["verified"] = entry["is_40_hex"] and entry.get("api_sha") == rev
        ok = ok and entry["verified"]
        commits.append(entry)

    files: list[dict[str, Any]] = []
    for repo, rev, path, expected in CITED_FILES:
        url = f"https://raw.githubusercontent.com/{repo}/{rev}/{path}"
        status = http_status(url)
        files.append({
            "repository": repo,
            "revision": rev,
            "path": path,
            "expected_status": expected,
            "status": status,
        })
        ok = ok and status == expected

    receipt = {
        "schema": "pin-receipt/1",
        "generated_on": datetime.date.today().isoformat(),
        "commits": commits,
        "files": files,
        "passed": bool(ok),
    }
    Path(args.out).write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    for c in commits:
        print(f"{'ok  ' if c['verified'] else 'FAIL'} {c['repository']}@{c['pinned_revision']} ({c.get('committer_date')})")
    for f in files:
        mark = "ok  " if f["status"] == f["expected_status"] else "FAIL"
        print(f"{mark} {f['repository']}@{f['revision'][:10]}:{f['path']} -> {f['status']} (expected {f['expected_status']})")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
