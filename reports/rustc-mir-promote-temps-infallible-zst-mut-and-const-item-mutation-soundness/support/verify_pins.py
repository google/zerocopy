#!/usr/bin/env python3
"""Verify the upstream pins and cited source paths of this report against GitHub.

For every subject of `../REPORT.json` that specifies `repository` and `revision`, query
`<gh> api repos/<repo>/commits/<rev>` and require the returned 40-hex SHA to equal
the pinned revision. Then check every cited `(repository, revision, path, expected_status)`
entry on `raw.githubusercontent.com` and write `pin_receipt.json`.

Usage:

    python3 support/verify_pins.py --out support/pin_receipt.json
"""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
import datetime
import http.client
import json
import re
import shlex
import subprocess
import urllib.error
import urllib.request
from pathlib import Path

HERE = Path(__file__).resolve().parent

RUST_198 = "14210df0e27ccd7d9e6a05b8085cbd438e4bbc65"
RUST_NEEDS_DROP_FIX = "940498dad7cb35a753a7cce104ab510b414e84de"
RUST_1102 = "3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1"
RUST_HEAD = "ce66487ebbd7541212d22d01c39a808057d69f1f"
REFERENCE_PIN = "c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c"
RFCS_PIN = "f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07"
ANNEAL_PIN = "c131b320eeeb26ef692e5afd5ec8db49ee518613"

# (repository, pinned_revision, path, expected_status)
CITED_FILES = [
    ("rust-lang/rust", RUST_198, "compiler/rustc_mir_transform/src/promote_consts.rs", 200),
    ("rust-lang/rust", RUST_198, "compiler/rustc_mir_transform/src/check_const_item_mutation.rs", 200),
    ("rust-lang/rust", RUST_198, "compiler/rustc_mir_transform/src/required_consts.rs", 200),
    ("rust-lang/rust", RUST_198, "compiler/rustc_mir_transform/src/lib.rs", 200),
    ("rust-lang/rust", RUST_198, "compiler/rustc_const_eval/src/check_consts/qualifs.rs", 200),
    ("rust-lang/rust", RUST_198, "src/tools/miri/src/borrow_tracker/stacked_borrows/mod.rs", 200),
    ("rust-lang/rust", RUST_198, "src/tools/miri/src/borrow_tracker/tree_borrows/mod.rs", 200),
    ("rust-lang/rust", RUST_NEEDS_DROP_FIX, "compiler/rustc_mir_transform/src/check_const_item_mutation.rs", 200),
    ("rust-lang/rust", RUST_1102, "compiler/rustc_mir_transform/src/promote_consts.rs", 200),
    ("rust-lang/rust", RUST_1102, "compiler/rustc_mir_transform/src/check_const_item_mutation.rs", 200),
    ("rust-lang/rust", RUST_1102, "compiler/rustc_mir_transform/src/required_consts.rs", 200),
    ("rust-lang/rust", RUST_1102, "compiler/rustc_mir_transform/src/lib.rs", 200),
    ("rust-lang/rust", RUST_1102, "compiler/rustc_const_eval/src/check_consts/qualifs.rs", 200),
    ("rust-lang/rust", RUST_1102, "compiler/rustc_mir_build/src/builder/expr/as_temp.rs", 200),
    ("rust-lang/rust", RUST_1102, "src/tools/miri/src/borrow_tracker/stacked_borrows/mod.rs", 200),
    ("rust-lang/rust", RUST_1102, "src/tools/miri/src/borrow_tracker/tree_borrows/mod.rs", 200),
    ("rust-lang/rust", RUST_HEAD, "compiler/rustc_mir_transform/src/promote_consts.rs", 200),
    ("rust-lang/rust", RUST_HEAD, "compiler/rustc_mir_transform/src/check_const_item_mutation.rs", 200),
    ("rust-lang/reference", REFERENCE_PIN, "src/destructors.md", 200),
    ("rust-lang/reference", REFERENCE_PIN, "src/items/constant-items.md", 200),
    ("rust-lang/rfcs", RFCS_PIN, "text/3027-infallible-promotion.md", 200),
    ("rust-lang/rfcs", RFCS_PIN, "text/1414-rvalue_static_promotion.md", 200),
    ("joshlf/anneal", ANNEAL_PIN, "trusted/lean/Trusted/MirAst.lean", 200),
    ("joshlf/anneal", ANNEAL_PIN, "trusted/lean/Trusted/MirSemantics.lean", 200),
    ("joshlf/anneal", ANNEAL_PIN, "trusted/audit/TrustedBoundary.lean", 200),
    ("joshlf/anneal", ANNEAL_PIN, "trusted/rustc-capture/src/driver.rs", 200),
]


def http_status(url: str) -> int | None:
    """HTTP status of a GET on `url`: three attempts with urllib, then curl fallback."""
    for _ in range(3):
        req = urllib.request.Request(url, method="GET")
        try:
            with urllib.request.urlopen(req, timeout=30) as resp:
                resp.read(1)
                return resp.status
        except urllib.error.HTTPError as exc:
            return exc.code
        except (urllib.error.URLError, OSError, http.client.HTTPException):
            continue
    try:
        proc = subprocess.run(
            ["curl", "-sS", "-m", "30", "-o", "/dev/null", "-w", "%{http_code}", url],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        code = proc.stdout.decode("utf-8", "replace").strip()
        return int(code) if code.isdigit() and code != "000" else None
    except OSError:
        return None


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter
    )
    ap.add_argument("--gh", default="gh", help="command used to reach the GitHub API")
    ap.add_argument("--out", default=str(HERE / "pin_receipt.json"))
    args = ap.parse_args(argv)
    gh = shlex.split(args.gh)

    report = json.loads((HERE.parent / "REPORT.json").read_text(encoding="utf-8"))
    pinned_pairs: set[tuple[str, str]] = set()
    commit_targets: list[tuple[str, str]] = []
    for subject in report["subjects"]:
        ident = subject["identity"]
        repo, rev = ident.get("repository"), ident.get("revision")
        if repo and rev:
            commit_targets.append((repo, rev))
            pinned_pairs.add((repo, rev))

    def _check_commit(pair: tuple[str, str]) -> dict:
        repo, rev = pair
        is_hex = bool(re.fullmatch(r"[0-9a-f]{40}", rev))
        proc = subprocess.run(
            gh + ["api", f"repos/{repo}/commits/{rev}"],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        entry = {
            "repository": repo,
            "pinned_revision": rev,
            "is_40_hex": is_hex,
        }
        try:
            data = json.loads(proc.stdout.decode("utf-8", "replace"))
            entry["api_sha"] = data.get("sha")
            entry["committer_date"] = data.get("commit", {}).get("committer", {}).get("date")
            msg = data.get("commit", {}).get("message") or ""
            entry["subject_line"] = msg.splitlines()[0][:100] if msg else ""
        except ValueError:
            entry["api_sha"] = None
            entry["error"] = "no JSON from API call"
        entry["verified"] = is_hex and entry.get("api_sha") == rev
        return entry

    def _check_file(item: tuple[str, str, str, int]) -> dict:
        repo, rev, path, expected = item
        in_report = (repo, rev) in pinned_pairs
        url = f"https://raw.githubusercontent.com/{repo}/{rev}/{path}"
        status = http_status(url) if in_report else None
        return {
            "repository": repo,
            "revision": rev,
            "path": path,
            "expected_status": expected,
            "status": status,
            "in_report_subjects": in_report,
        }

    with ThreadPoolExecutor(max_workers=8) as pool:
        commits = list(pool.map(_check_commit, commit_targets))
        files = list(pool.map(_check_file, CITED_FILES))

    ok = all(c["verified"] for c in commits) and all(
        row["in_report_subjects"] and row["status"] == row["expected_status"]
        for row in files
    )

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
        mark = "ok  " if (f["in_report_subjects"] and f["status"] == f["expected_status"]) else "FAIL"
        print(f"{mark} {f['repository']}@{f['revision'][:9]}:{f['path']} -> {f['status']} (expected {f['expected_status']})")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
