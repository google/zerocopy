#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Comment-stripped concurrency hazard scanner for unpacked Rust crate trees."""

import glob
import os
import re
import sys

PATTERNS = {
    "unsafe": re.compile(r"\bunsafe\b"),
    "asm": re.compile(r"\b(?:global_asm|naked_asm|asm)!"),
    "volatile": re.compile(r"\b(?:read_volatile|write_volatile)\b"),
    "compiler_fence": re.compile(r"\bcompiler_fence\b"),
    "fence": re.compile(r"(?<!compiler_)\bfence\s*\("),
    "seqcst": re.compile(r"\bSeqCst\b"),
    "transmute": re.compile(r"\b(?:transmute|transmute_copy)\b"),
    "strict_prov": re.compile(
        r"\b(?:with_addr|map_addr|expose_provenance|with_exposed_provenance|without_provenance|without_provenance_mut|sptr)\b"
    ),
}


def strip_comments_keep_lines(src: str) -> str:
    # Strip block and line comments while preserving newlines so line numbers match.
    src = re.sub(
        r"/\*.*?\*/",
        lambda m: "\n" * m.group(0).count("\n"),
        src,
        flags=re.DOTALL,
    )
    src = re.sub(r"//[^\n]*", "", src)
    return src


def scan_crate(crate_dir: str) -> dict[str, int]:
    counts = {k: 0 for k in PATTERNS}
    counts["files"] = 0
    counts["loc"] = 0
    for path in sorted(glob.glob(os.path.join(crate_dir, "src", "**", "*.rs"), recursive=True)):
        with open(path, encoding="utf-8") as f:
            raw = f.read()
        counts["files"] += 1
        counts["loc"] += len(raw.splitlines())
        clean = strip_comments_keep_lines(raw)
        for key, pat in PATTERNS.items():
            counts[key] += len(pat.findall(clean))
    return counts


def main() -> None:
    if len(sys.argv) < 2:
        print("usage: scan_crates_concurrency_hazards.py <crate_dir> [...]", file=sys.stderr)
        sys.exit(2)
    for d in sys.argv[1:]:
        c = scan_crate(d)
        print(f"{os.path.basename(d)}: {c}")


if __name__ == "__main__":
    main()
