#!/usr/bin/env python3
"""Verify every pinned GitHub commit and cited upstream file in `../REPORT.json`.

For every subject in `../REPORT.json` that specifies `repository` and `revision`, query the GitHub
API (via `--gh`) and verify that the resolved commit SHA equals the pinned 40-hex revision. Then
fetch every cited source file from `raw.githubusercontent.com` at its pinned revision and record
its HTTP status (including paths expected to return HTTP 404).

Usage:

    python3 support/verify_pins.py --out support/pin_receipt.json

`--gh` overrides the `gh` command invocation; CLI flags passed to `--gh` are never written into
the output receipt. Exits non-zero if any commit pin or cited path fails verification.
"""

from __future__ import annotations

import argparse
import datetime
import http.client
import json
import re
import shlex
import subprocess
import sys
import urllib.error
import urllib.request
from pathlib import Path

HERE = Path(__file__).resolve().parent

RUST_NIGHTLY_SHA = "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65"
RUST_HEAD_SHA = "c7d5ba59d8e11ee2e2204b173458eec4cb41c973"
REFERENCE_SHA = "ad35aca481751a06afeb23820a672b0f3b11a476"
ANNEAL_SHA = "c131b320eeeb26ef692e5afd5ec8db49ee518613"

# (repository, revision, path, expected HTTP status).
CITED_FILES = [
    ("rust-lang/rust", RUST_NIGHTLY_SHA, "compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs", 200),
    ("rust-lang/rust", RUST_NIGHTLY_SHA, "compiler/rustc_mir_transform/src/remove_false_edges.rs", 404),
    ("rust-lang/rust", RUST_NIGHTLY_SHA, "compiler/rustc_mir_transform/src/abort_unwinding_calls.rs", 200),
    ("rust-lang/rust", RUST_NIGHTLY_SHA, "compiler/rustc_mir_transform/src/remove_place_mention.rs", 200),
    ("rust-lang/rust", RUST_NIGHTLY_SHA, "compiler/rustc_mir_transform/src/remove_noop_landing_pads.rs", 200),
    ("rust-lang/rust", RUST_NIGHTLY_SHA, "compiler/rustc_mir_transform/src/simplify.rs", 200),
    ("rust-lang/rust", RUST_NIGHTLY_SHA, "compiler/rustc_mir_transform/src/deref_separator.rs", 200),
    ("rust-lang/rust", RUST_NIGHTLY_SHA, "compiler/rustc_mir_transform/src/validate.rs", 200),
    ("rust-lang/rust", RUST_NIGHTLY_SHA, "compiler/rustc_mir_transform/src/lib.rs", 200),
    ("rust-lang/rust", RUST_NIGHTLY_SHA, "compiler/rustc_mir_transform/src/pass_manager.rs", 200),
    ("rust-lang/rust", RUST_NIGHTLY_SHA, "compiler/rustc_middle/src/mir/mod.rs", 200),
    ("rust-lang/rust", RUST_NIGHTLY_SHA, "compiler/rustc_middle/src/mir/syntax.rs", 200),
    ("rust-lang/rust", RUST_NIGHTLY_SHA, "compiler/rustc_middle/src/ty/layout.rs", 200),
    ("rust-lang/rust", RUST_NIGHTLY_SHA, "compiler/rustc_const_eval/src/interpret/step.rs", 200),
    ("rust-lang/rust", RUST_HEAD_SHA, "compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs", 200),
    ("rust-lang/rust", RUST_HEAD_SHA, "compiler/rustc_mir_transform/src/remove_false_edges.rs", 404),
    ("rust-lang/rust", RUST_HEAD_SHA, "compiler/rustc_mir_transform/src/abort_unwinding_calls.rs", 200),
    ("rust-lang/rust", RUST_HEAD_SHA, "compiler/rustc_mir_transform/src/remove_place_mention.rs", 200),
    ("rust-lang/rust", RUST_HEAD_SHA, "compiler/rustc_mir_transform/src/remove_noop_landing_pads.rs", 200),
    ("rust-lang/rust", RUST_HEAD_SHA, "compiler/rustc_mir_transform/src/validate.rs", 200),
    ("rust-lang/rust", RUST_HEAD_SHA, "compiler/rustc_middle/src/mir/coverage.rs", 200),
    ("rust-lang/reference", REFERENCE_SHA, "src/panic.md", 200),
    ("rust-lang/reference", REFERENCE_SHA, "src/items/external-blocks.md", 200),
    ("joshlf/anneal", ANNEAL_SHA, "trusted/lean/Trusted/MirAst.lean", 200),
    ("joshlf/anneal", ANNEAL_SHA, "trusted/lean/Trusted/MirSemantics.lean", 200),
]


def http_status(url: str) -> int | None:
    """Return HTTP status for GET `url` (3 urllib retries, fallback to curl)."""
    for _ in range(3):
        req = urllib.request.Request(url, method="GET")
        try:
            with urllib.request.urlopen(req, timeout=60) as resp:
                resp.read(1)
                return resp.status
        except urllib.error.HTTPError as exc:
            return exc.code
        except (urllib.error.URLError, OSError, http.client.HTTPException):
            continue
    try:
        proc = subprocess.run(
            ["curl", "-sS", "-m", "60", "-o", "/dev/null", "-w", "%{http_code}", url],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        code = proc.stdout.decode("utf-8", "replace").strip()
        return int(code) if code.isdigit() and code != "000" else None
    except OSError:
        return None


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--gh", default="gh", help="GitHub CLI invocation prefix")
    ap.add_argument("--out", default=str(HERE / "pin_receipt.json"))
    args = ap.parse_args(argv)
    gh = shlex.split(args.gh)

    report = json.loads((HERE.parent / "REPORT.json").read_text(encoding="utf-8"))
    ok = True
    commits = []
    pinned_pairs: set[tuple[str, str]] = set()
    for subject in report["subjects"]:
        ident = subject["identity"]
        repo, rev = ident.get("repository"), ident.get("revision")
        if not repo or not rev:
            continue
        entry: dict[str, object] = {
            "repository": repo,
            "pinned_revision": rev,
            "is_40_hex": bool(re.fullmatch(r"[0-9a-f]{40}", rev)),
        }
        proc = subprocess.run(
            gh + ["api", f"repos/{repo}/commits/{rev}"],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        try:
            data = json.loads(proc.stdout.decode("utf-8", "replace"))
            entry["api_sha"] = data.get("sha")
            entry["committer_date"] = data.get("commit", {}).get("committer", {}).get("date")
            msg = data.get("commit", {}).get("message") or ""
            entry["subject_line"] = msg.splitlines()[0][:100] if msg else ""
        except ValueError:
            entry["api_sha"] = None
            entry["error"] = "invalid JSON returned by GitHub API call"
        entry["verified"] = bool(entry["is_40_hex"] and entry.get("api_sha") == rev)
        ok = ok and bool(entry["verified"])
        pinned_pairs.add((repo, rev))
        commits.append(entry)

    files = []
    for repo, rev, path, expected in CITED_FILES:
        in_subjects = (repo, rev) in pinned_pairs
        url = f"https://raw.githubusercontent.com/{repo}/{rev}/{path}"
        status = http_status(url) if in_subjects else None
        files.append(
            {
                "repository": repo,
                "revision": rev,
                "path": path,
                "expected_status": expected,
                "status": status,
                "in_subjects": in_subjects,
            }
        )
        ok = ok and in_subjects and status == expected

    receipt = {
        "schema": "pin-receipt/1",
        "generated_on": datetime.date.today().isoformat(),
        "commits": commits,
        "files": files,
        "passed": bool(ok),
    }
    Path(args.out).write_text(json.dumps(receipt, indent=1, sort_keys=True) + "\n", encoding="utf-8")
    for c in commits:
        print(f"{'ok  ' if c['verified'] else 'FAIL'} {c['repository']}@{c['pinned_revision']} ({c.get('committer_date')})")
    for f in files:
        mark = "ok  " if f["status"] == f["expected_status"] and f["in_subjects"] else "FAIL"
        print(f"{mark} {f['repository']}@{f['revision'][:10]}:{f['path']} -> {f['status']} (expected {f['expected_status']})")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
