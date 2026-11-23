#!/usr/bin/env python3
"""Inventory rustc_* crate, symbol, and prod-vs-test LOC usage inside anneal/trusted/rustc-capture."""

from __future__ import annotations

import argparse
import json
import re
from collections import defaultdict
from pathlib import Path

EXTERN_RE = re.compile(r"\bextern\s+crate\s+(rustc_[a-zA-Z0-9_]+)\s*;")
USE_STMT_RE = re.compile(r"\b(?:pub\s+)?use\s+(rustc_[a-zA-Z0-9_]+)::([^;]+);")
PATH_REF_RE = re.compile(r"\b(rustc_[a-zA-Z0-9_]+(?:::[a-zA-Z0-9_]+)+)\b")
FEATURE_RE = re.compile(r"#!\[feature\(([^)]+)\)\]")
TCX_RE = re.compile(r"\btcx\.([a-zA-Z0-9_]+)")
BODY_RE = re.compile(r"\bbody\.([a-zA-Z0-9_]+)")


def strip_comments(text: str) -> str:
    out = []
    in_block = False
    for line in text.splitlines():
        i = 0
        res = []
        while i < len(line):
            if in_block:
                if line[i : i + 2] == "*/":
                    in_block = False
                    i += 2
                else:
                    i += 1
            elif line[i : i + 2] == "/*":
                in_block = True
                i += 2
            elif line[i : i + 2] == "//":
                break
            else:
                res.append(line[i])
                i += 1
        out.append("".join(res))
    return "\n".join(out)


def expand_use_tree(prefix: str, body: str) -> list[str]:
    body = " ".join(line.split("//")[0].strip() for line in body.splitlines())
    results: list[str] = []

    def split_top_commas(s: str) -> list[str]:
        parts, depth, start = [], 0, 0
        for i, ch in enumerate(s):
            if ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
            elif ch == "," and depth == 0:
                part = s[start:i].strip()
                if part:
                    parts.append(part)
                start = i + 1
        tail = s[start:].strip()
        if tail:
            parts.append(tail)
        return parts

    def walk(pfx: str, expr: str) -> None:
        expr = expr.strip()
        if not expr:
            return
        if "{" in expr and expr.endswith("}"):
            idx = expr.index("{")
            head = expr[:idx].rstrip(":").strip()
            inner = expr[idx + 1 : -1].strip()
            new_pfx = f"{pfx}::{head}" if head else pfx
            for item in split_top_commas(inner):
                walk(new_pfx, item)
        else:
            for item in split_top_commas(expr):
                item_clean = item.split(" as ")[0].strip()
                results.append(pfx if item_clean == "self" else f"{pfx}::{item_clean}")

    walk(prefix, body)
    return results


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--capture-root", type=Path, required=True, help="Path to anneal/trusted/rustc-capture")
    args = parser.parse_args()

    src_dir = args.capture_root / "src"
    tests_dir = args.capture_root / "tests"
    by_crate_imports: dict[str, set[str]] = defaultdict(set)
    by_crate_paths: dict[str, set[str]] = defaultdict(set)
    tcx_members: set[str] = set()
    body_members: set[str] = set()
    features: set[str] = set()
    files_meta = {}

    for p in sorted(src_dir.glob("*.rs")):
        lines = p.read_text().splitlines()
        mod_test = next((i for i, l in enumerate(lines, 1) if "mod tests" in l), None)
        if mod_test is not None and mod_test >= 2 and "#[cfg(test)]" in lines[mod_test - 2]:
            prod = mod_test - 2
        elif mod_test is not None:
            prod = mod_test - 1
        else:
            prod = len(lines)
        stripped = strip_comments("\n".join(lines[:prod]))
        for m in FEATURE_RE.finditer(stripped):
            for f in m.group(1).split(","):
                if f.strip():
                    features.add(f.strip())
        for m in USE_STMT_RE.finditer(stripped):
            for exp in expand_use_tree(m.group(1), m.group(2)):
                by_crate_imports[m.group(1)].add(exp)
        for m in PATH_REF_RE.finditer(stripped):
            by_crate_paths[m.group(1).split("::")[0]].add(m.group(1))
        tcx_members.update(TCX_RE.findall(stripped))
        body_members.update(BODY_RE.findall(stripped))
        files_meta[p.name] = {"total": len(lines), "prod": prod, "mod_tests": len(lines) - prod}

    tests_total = sum(len(p.read_text().splitlines()) for p in tests_dir.rglob("*.rs"))
    print(json.dumps({
        "features": sorted(features),
        "src_files": files_meta,
        "tests_total_loc": tests_total,
        "by_crate_imports": {k: sorted(v) for k, v in sorted(by_crate_imports.items())},
        "by_crate_paths": {k: sorted(v) for k, v in sorted(by_crate_paths.items())},
        "tcx_members": sorted(tcx_members),
        "body_members": sorted(body_members),
    }, indent=2))


if __name__ == "__main__":
    main()
