#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Check citation tables against extracted upstream source trees.

Each non-comment line of a citation TSV has five tab-separated columns:

    repo <TAB> path <TAB> start_line <TAB> end_line <TAB> needle

`repo` is `seL4` (seL4/seL4) or `l4v` (seL4/l4v). `path` is relative to the
repository root. `needle` is a literal substring that must occur inside lines
`start_line..end_line` (1-based, inclusive) of that file once every run of
whitespace in both the file text and the needle is collapsed to one space.
Lines starting with `#` and blank lines are ignored.

With `--report FILE`, every citation token of the form
`` `repo:path:Lstart-Lend` `` in FILE must also have a row with the same
repo, path and line range in one of the TSVs.

Usage:
    check_citations.py --sel4 <seL4 tree> --l4v <l4v tree> \
        [--report REPORT.md] citations.tsv [...]

Exit status is 0 only if every citation resolves and, with `--report`, every
token in the report is covered.
"""

import argparse
import re
import sys
from pathlib import Path

TOKEN = re.compile(r"`(seL4|l4v):([^`:]+):L(\d+)-L(\d+)`")


def norm(s: str) -> str:
    return re.sub(r"\s+", " ", s).strip()


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--sel4", required=True)
    ap.add_argument("--l4v", required=True)
    ap.add_argument("--report")
    ap.add_argument("tsv", nargs="+")
    args = ap.parse_args()
    roots = {"seL4": Path(args.sel4), "l4v": Path(args.l4v)}
    cache = {}
    rows = set()
    bad = 0
    total = 0
    for tsv in args.tsv:
        text = Path(tsv).read_text(encoding="utf-8")
        for n, raw in enumerate(text.splitlines(), 1):
            if not raw.strip() or raw.startswith("#"):
                continue
            total += 1
            cols = raw.split("\t")
            if len(cols) != 5:
                print(f"{tsv}:{n}: expected 5 columns, got {len(cols)}")
                bad += 1
                continue
            repo, path, start, end, needle = cols
            if repo not in roots:
                print(f"{tsv}:{n}: unknown repo {repo!r}")
                bad += 1
                continue
            f = roots[repo] / path
            if f not in cache:
                try:
                    cache[f] = f.read_text(
                        encoding="utf-8", errors="replace"
                    ).splitlines()
                except OSError as exc:
                    print(f"{tsv}:{n}: cannot read {repo}:{path}: {exc}")
                    bad += 1
                    continue
            lines = cache[f]
            lo, hi = int(start), int(end)
            if not 1 <= lo <= hi <= len(lines):
                print(
                    f"{tsv}:{n}: range L{lo}-L{hi} outside {repo}:{path} "
                    f"({len(lines)} lines)"
                )
                bad += 1
                continue
            rows.add((repo, path, lo, hi))
            hay = norm("\n".join(lines[lo - 1 : hi]))
            if norm(needle) not in hay:
                print(
                    f"{tsv}:{n}: needle not found in "
                    f"{repo}:{path}:L{lo}-L{hi}: {needle!r}"
                )
                bad += 1
    print(f"checked {total} citations, {bad} failed")
    uncovered = 0
    if args.report:
        text = Path(args.report).read_text(encoding="utf-8")
        tokens = {
            (m.group(1), m.group(2), int(m.group(3)), int(m.group(4)))
            for m in TOKEN.finditer(text)
        }
        for repo, path, lo, hi in sorted(tokens - rows):
            print(f"{args.report}: no citation row for {repo}:{path}:L{lo}-L{hi}")
            uncovered += 1
        print(f"report cites {len(tokens)} ranges, {uncovered} without a row")
    return 1 if bad or uncovered else 0


if __name__ == "__main__":
    sys.exit(main())
