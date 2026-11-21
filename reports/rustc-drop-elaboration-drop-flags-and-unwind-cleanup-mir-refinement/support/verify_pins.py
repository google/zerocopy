#!/usr/bin/env python3
"""Verify the upstream pins of this report against GitHub.

For every subject of `../REPORT.json` that has a `repository` and a `revision`, ask the GitHub
API (through the `gh` CLI) for that commit and require that the full 40-hex SHA it returns equals
the pinned revision. Then fetch the cited files at those revisions from
`raw.githubusercontent.com` and record the HTTP status of each, including the one path that is
expected to be absent.

Usage:

    python3 support/verify_pins.py --out support/pin_receipt.json

`--gh` replaces the `gh` command (for example to add authentication options). The script exits
non-zero if a pin does not resolve to itself or a file has an unexpected status.
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

# (repository, path, expected HTTP status). The revision is looked up in REPORT.json.
CITED_FILES = [
    ("rust-lang/rust", "compiler/rustc_mir_transform/src/elaborate_drops.rs", 200),
    ("rust-lang/rust", "compiler/rustc_mir_transform/src/elaborate_drop.rs", 200),
    ("rust-lang/rust", "compiler/rustc_mir_dataflow/src/elaborate_drops.rs", 404),
    ("rust-lang/rust", "compiler/rustc_mir_dataflow/src/drop_flag_effects.rs", 200),
    ("rust-lang/rust", "compiler/rustc_mir_dataflow/src/move_paths/builder.rs", 200),
    ("rust-lang/rust", "compiler/rustc_mir_transform/src/abort_unwinding_calls.rs", 200),
    ("rust-lang/rust", "compiler/rustc_mir_transform/src/validate.rs", 200),
    ("rust-lang/rust", "compiler/rustc_mir_transform/src/lib.rs", 200),
    ("rust-lang/rust", "compiler/rustc_middle/src/mir/syntax.rs", 200),
    ("rust-lang/rust", "library/core/src/ops/drop.rs", 200),
    ("rust-lang/rust", "library/core/src/panicking.rs", 200),
    ("rust-lang/rust", "src/doc/rustc-dev-guide/src/mir/drop-elaboration.md", 200),
    ("rust-lang/reference", "src/destructors.md", 200),
    ("rust-lang/reference", "src/panic.md", 200),
    ("rust-lang/rfcs", "text/0320-nonzeroing-dynamic-drop.md", 200),
    ("joshlf/anneal", "trusted/lean/Trusted/MirAst.lean", 200),
    ("joshlf/anneal", "trusted/lean/Trusted/MirSemantics.lean", 200),
]


def http_status(url: str) -> int | None:
    """HTTP status of a GET on `url`: three attempts with urllib, then one with `curl`."""
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
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        )
        code = proc.stdout.decode().strip()
        return int(code) if code.isdigit() and code != "000" else None
    except OSError:
        return None


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--gh", default="gh", help="command used to reach the GitHub API")
    ap.add_argument("--out", default=str(HERE / "pin_receipt.json"))
    args = ap.parse_args(argv)
    gh = shlex.split(args.gh)

    report = json.loads((HERE.parent / "REPORT.json").read_text())
    pins = {}
    ok = True
    commits = []
    for subject in report["subjects"]:
        ident = subject["identity"]
        repo, rev = ident.get("repository"), ident.get("revision")
        if not repo or not rev:
            continue
        entry = {"repository": repo, "pinned_revision": rev, "is_40_hex": bool(re.fullmatch(r"[0-9a-f]{40}", rev))}
        proc = subprocess.run(gh + ["api", f"repos/{repo}/commits/{rev}"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        try:
            data = json.loads(proc.stdout.decode("utf-8", "replace"))
            entry["api_sha"] = data.get("sha")
            entry["committer_date"] = data.get("commit", {}).get("committer", {}).get("date")
            entry["subject_line"] = (data.get("commit", {}).get("message") or "").splitlines()[0][:100]
        except ValueError:
            entry["api_sha"] = None
            entry["error"] = "no JSON from the API call"
        entry["verified"] = entry["is_40_hex"] and entry.get("api_sha") == rev
        ok = ok and entry["verified"]
        pins[repo] = rev
        commits.append(entry)

    files = []
    for repo, path, expected in CITED_FILES:
        rev = pins.get(repo)
        url = f"https://raw.githubusercontent.com/{repo}/{rev}/{path}"
        status = http_status(url) if rev else None
        files.append({"repository": repo, "path": path, "expected_status": expected, "status": status})
        ok = ok and status == expected

    receipt = {
        "schema": "pin-receipt/1",
        "generated_on": datetime.date.today().isoformat(),
        "commits": commits,
        "files": files,
        "passed": bool(ok),
    }
    Path(args.out).write_text(json.dumps(receipt, indent=1, sort_keys=True) + "\n")
    for c in commits:
        print(f"{'ok  ' if c['verified'] else 'FAIL'} {c['repository']}@{c['pinned_revision']} ({c.get('committer_date')})")
    for f in files:
        mark = "ok  " if f["status"] == f["expected_status"] else "FAIL"
        print(f"{mark} {f['repository']}:{f['path']} -> {f['status']} (expected {f['expected_status']})")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
