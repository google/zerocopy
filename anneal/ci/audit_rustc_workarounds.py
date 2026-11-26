#!/usr/bin/env python3
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Validate and inventory upstream `rustc` workaround anchors.

`docs/rustc-workarounds.md` defines the anchor. This script runs the same
scan as the `rustc-workaround` check in `check_pr_hygiene.py` over the tree
at `--head`: Rust, Python, shell, Nix, TOML, YAML, and Lean files under
`anneal/` outside `anneal/vendor/` (Markdown is exempt, so prose and
examples may name the tag). It reports every tag that is not a well-formed
anchor, including the `#PENDING` placeholder.

`--bump` prints a Markdown audit table of every anchor grouped by issue for
a compiler-pin bump's Review Receipt; `--json` prints a machine-readable
report instead. Both show only each anchor's tag line, not continuation
comment lines. Like `check_pr_hygiene.py`, the script reads only Git
objects (it never checks out, builds, or executes candidate content) and
makes no network requests, so its result depends only on `--head`. Exits 0
when clean, 1 on findings, and 2 on usage or Git errors.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
import json
from pathlib import Path
import re
import sys

# `python3 -I` omits the script's directory from `sys.path`.
_CI_DIR = Path(__file__).resolve().parent
if str(_CI_DIR) not in sys.path:
    sys.path.insert(0, str(_CI_DIR))
import check_pr_hygiene as cph  # noqa: E402

SCHEMA = "anneal-rustc-workarounds/v1"
COMPILER_COMMIT_PATH = "anneal/trusted/rustc-capture/src/ir.rs"
COMPILER_COMMIT_RE = re.compile(
    r'^pub const COMPILER_COMMIT: &str = "([0-9a-f]{40})";$', re.MULTILINE)


def compiler_commit(git: cph.Git, head: str) -> str | None:
    """Return the pinned `COMPILER_COMMIT` at `head`, if it parses."""
    text = git.blob_text(head, COMPILER_COMMIT_PATH)
    m = COMPILER_COMMIT_RE.search(text) if text is not None else None
    return m.group(1) if m else None


def _cell(text: str) -> str:
    return text.replace("\\", "\\\\").replace("|", "\\|")


def bump_table(anchors: list[cph.WorkaroundAnchor], head: str,
               pin: str | None) -> str:
    """Render the compiler-bump audit table for a Review Receipt."""
    by_issue: dict[int, list[cph.WorkaroundAnchor]] = defaultdict(list)
    for a in anchors:
        by_issue[a.issue].append(a)
    lines = [
        f"`{cph.WORKAROUND_TAG}` audit at `{head}` (compiler pin "
        + (f"`{pin}`" if pin else "unknown") + f"): {len(anchors)} "
        f"anchor(s) across {len(by_issue)} issue(s). Fill in the last two "
        "columns per `docs/rustc-workarounds.md`.",
        "",
        "| Issue | Anchors | Summary | Status at old -> new pin | Action |",
        "| :--- | :--- | :--- | :--- | :--- |",
    ]
    for issue in sorted(by_issue):
        group = by_issue[issue]
        sites = "<br>".join(f"`{_cell(a.path)}:{a.line}`" for a in group)
        summaries = dict.fromkeys(a.summary for a in group)
        notes = "<br>".join(_cell(s) for s in summaries)
        lines.append(f"| #{issue} | {sites} | {notes} |  |  |")
    if not by_issue:
        lines.append("| none |  |  |  |  |")
    return "\n".join(lines) + "\n"


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description=__doc__.split("\n\n", 1)[0])
    parser.add_argument("--repo", default=".",
                        help="any path inside the repository (default: .)")
    parser.add_argument("--head", default="HEAD",
                        help="commit to scan (default: HEAD)")
    out = parser.add_mutually_exclusive_group()
    out.add_argument("--bump", action="store_true",
                     help="print the compiler-bump audit table")
    out.add_argument("--json", action="store_true",
                     help="emit a machine-readable report")
    args = parser.parse_args(argv)

    try:
        git = cph.Git(cph.Git(Path(args.repo).resolve()).toplevel())
        head = git.commit(args.head)
        anchors, findings = cph.tree_workarounds(git, head)
        pin = compiler_commit(git, head)
    except (cph.GitError, OSError) as e:
        if args.json:
            print(json.dumps({"schema": SCHEMA, "ok": False, "error": str(e)}))
        else:
            print(f"audit_rustc_workarounds: error: {e}", file=sys.stderr)
        return 2

    ok = not findings
    tag = cph.WORKAROUND_TAG
    if args.json:
        print(json.dumps({
            "schema": SCHEMA, "ok": ok, "head": head, "compiler_commit": pin,
            "anchors": [a.to_json() for a in anchors],
            "findings": [f.to_json() for f in findings],
        }, indent=2))
    else:
        for f in findings:
            print(f.render(), file=sys.stderr)
        if args.bump:
            sys.stdout.write(bump_table(anchors, head, pin))
        elif ok:
            print(f"{len(anchors)} well-formed `{tag}` anchor(s).")
        if not ok:
            print(f"{len(findings)} `{tag}` finding(s).", file=sys.stderr)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
