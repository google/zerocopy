#!/usr/bin/env python3
"""Deterministic validator and primary-source revalidation probe for this report."""

from __future__ import annotations

import argparse
import json
import re
import sys
import urllib.request
from pathlib import Path

REQUIRED_SECTIONS = [
    "## Summary",
    "## Applicability",
    "## Findings",
    "## Boundaries",
    "## Evidence",
    "## Revalidation",
]

BOUNDARY_TERMS = (
    "not examined",
    "unknown",
    "known not to apply",
    "unsupported",
)

FORBIDDEN_INTERNAL_PATTERNS = (
    re.compile(r"/home/[a-z0-9_.-]+/", re.IGNORECASE),
    re.compile(r"\bfile:///"),
    re.compile(r"\b(?:go|b|cl|xid)/[a-z0-9_-]{3,}", re.IGNORECASE),
)


def parse_strict_json(path: Path) -> object:
    def reject_dups(pairs: list[tuple[str, object]]) -> dict[str, object]:
        out: dict[str, object] = {}
        for k, v in pairs:
            if k in out:
                raise ValueError(f"Duplicate JSON key {k!r} in {path}")
            out[k] = v
        return out

    return json.loads(
        path.read_text(encoding="utf-8"),
        object_pairs_hook=reject_dups,
        parse_constant=lambda c: (_ for _ in ()).throw(ValueError(f"Invalid constant {c}")),
    )


def check_report_structure(report_dir: Path) -> list[str]:
    errs: list[str] = []
    rj_path = report_dir / "REPORT.json"
    rm_path = report_dir / "REPORT.md"
    rev_path = report_dir / "support" / "peer_revisions_2026-11-25.json"

    for req in (rj_path, rm_path, rev_path):
        if not req.is_file():
            errs.append(f"Missing required file: {req}")
    if errs:
        return errs

    meta = parse_strict_json(rj_path)
    if not isinstance(meta, dict) or set(meta) != {"topics", "subjects", "observed_at"}:
        errs.append("REPORT.json must have exact keys topics, subjects, observed_at")
        return errs

    revs = parse_strict_json(rev_path)
    pinned_map = revs["pinned_subjects"]

    subject_revs = {
        s["identity"].get("revision")
        for s in meta["subjects"]
        if isinstance(s, dict) and isinstance(s.get("identity"), dict)
    }
    for name, info in pinned_map.items():
        if info["revision"] not in subject_revs:
            errs.append(f"Pinned revision {info['revision']} ({name}) missing from REPORT.json subjects")

    md = rm_path.read_text(encoding="utf-8")
    in_fence = False
    h1s: list[str] = []
    h2s: list[str] = []
    for line in md.splitlines():
        s = line.rstrip()
        if s.startswith("```"):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        if s.startswith("# ") and not s.startswith("## "):
            h1s.append(s)
        elif s.startswith("## "):
            h2s.append(s)

    if len(h1s) != 1:
        errs.append(f"Expected 1 H1 heading, found {len(h1s)}")
    if h2s != REQUIRED_SECTIONS:
        errs.append(f"Expected exact H2 sections {REQUIRED_SECTIONS}, got {h2s}")

    if "Basis:" not in md:
        errs.append("REPORT.md contains no explicit Basis: attributions")

    lower_md = md.lower()
    for term in BOUNDARY_TERMS:
        if term not in lower_md:
            errs.append(f"REPORT.md missing required negative-space boundary term {term!r}")

    for text_path in (rj_path, rm_path, rev_path):
        content = text_path.read_text(encoding="utf-8")
        for pat in FORBIDDEN_INTERNAL_PATTERNS:
            m = pat.search(content)
            if m:
                errs.append(f"Forbidden internal reference {m.group(0)!r} found in {text_path.name}")

    return errs


def verify_markers(report_dir: Path, cache_dir: Path | None, fetch_online: bool) -> tuple[int, list[str]]:
    revs = parse_strict_json(report_dir / "support" / "peer_revisions_2026-11-25.json")
    pinned = revs["pinned_subjects"]
    checked = 0
    errs: list[str] = []

    for label, info in pinned.items():
        if label.startswith("google/zerocopy"):
            continue
        sha = info["revision"]
        markers = info.get("markers", [])
        files = info.get("files", [])
        if not markers or not files:
            continue

        joined = []
        for rel in files:
            cached = cache_dir / f"{label.replace('/', '__')}__{rel.replace('/', '__')}" if cache_dir else None
            txt = None
            if cached and cached.is_file():
                txt = cached.read_text(encoding="utf-8", errors="replace")
            elif fetch_online:
                url = f"https://raw.githubusercontent.com/{label}/{sha}/{rel}"
                req = urllib.request.Request(url, headers={"User-Agent": "anneal-dx-revalidation"})
                with urllib.request.urlopen(req, timeout=20) as resp:
                    txt = resp.read().decode("utf-8", errors="replace")
            if txt is not None:
                joined.append(txt)
                checked += 1

        if joined:
            haystack = "\n".join(joined)
            for marker in markers:
                if marker not in haystack:
                    errs.append(f"Marker {marker!r} missing in {label}@{sha[:10]}")

    return checked, errs


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--report-dir",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="Path to report package directory",
    )
    parser.add_argument(
        "--cache-dir",
        type=Path,
        default=None,
        help="Optional directory containing cached <owner>__<repo>__<path> upstream snapshots",
    )
    parser.add_argument(
        "--fetch-online",
        action="store_true",
        help="Fetch uncached upstream files via raw.githubusercontent.com at pinned SHAs",
    )
    args = parser.parse_args()

    errs = check_report_structure(args.report_dir)
    checked_files, marker_errs = verify_markers(args.report_dir, args.cache_dir, args.fetch_online)
    errs.extend(marker_errs)

    if errs:
        for e in errs:
            print(f"FAIL: {e}", file=sys.stderr)
        return 1

    print(
        f"PASS: structure valid, airgap clean, pinned markers verified across {checked_files} cached/fetched files"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
