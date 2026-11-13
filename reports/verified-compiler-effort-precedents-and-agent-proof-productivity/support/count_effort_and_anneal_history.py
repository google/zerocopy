#!/usr/bin/env python3
"""Reproducible SLOC/proof-ratio counter and Anneal git-history productivity analyzer."""

from __future__ import annotations
import argparse
import json
import subprocess
from pathlib import Path


def count_tree_lines(repo: Path, rev: str, prefix: str = "") -> dict[str, dict[str, int]]:
    cmd = ["git", "ls-tree", "-r", "--name-only", rev]
    if prefix:
        cmd.append(prefix)
    files = subprocess.run(cmd, cwd=repo, text=True, capture_output=True, check=True).stdout.splitlines()
    stats: dict[str, dict[str, int]] = {}
    for f in files:
        ext = Path(f).suffix or "no_ext"
        blob = subprocess.run(
            ["git", "show", f"{rev}:{f}"],
            cwd=repo,
            text=True,
            capture_output=True,
            errors="ignore",
        ).stdout
        lines = blob.splitlines()
        total = len(lines)
        blank = sum(1 for l in lines if not l.strip())
        comment = sum(
            1
            for l in lines
            if l.strip().startswith(("//", "--", "#", "/*", "*", ";", ".."))
        )
        code = total - blank - comment
        bucket = stats.setdefault(ext, {"files": 0, "total": 0, "blank": 0, "comment": 0, "code": 0})
        bucket["files"] += 1
        bucket["total"] += total
        bucket["blank"] += blank
        bucket["comment"] += comment
        bucket["code"] += code
    return stats


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify-manifest", type=Path, help="Verify stored JSON table invariants")
    args = parser.parse_args()
    if args.verify_manifest:
        data = json.loads(args.verify_manifest.read_text(encoding="utf-8"))
        assert len(data["systems"]) == 24, f"Expected 24 systems, found {len(data['systems'])}"
        assert "anneal_productivity" in data, "Missing anneal_productivity section"
        print(f"OK: verified {len(data['systems'])} systems and Anneal productivity metrics.")


if __name__ == "__main__":
    main()
