#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/LICENSE-2.0>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

import json
import os
import re

RUST_ROOT = "os.environ.get("RUST_1991_ROOT", ".")"
OUT_JSON = "/tmp/f2_stdlib_unsafe_metrics.json"

PATTERNS = {
    "unsafe_fn": re.compile(r"\bunsafe\s+(?:extern\s+(?:\"[^\"]+\"\s+)?)?fn\b"),
    "safe_or_total_fn": re.compile(r"\bfn\s+[a-zA-Z_][a-zA-Z0-9_]*"),
    "unsafe_block": re.compile(r"\bunsafe\s*\{"),
    "unsafe_trait": re.compile(r"\bunsafe\s+trait\b"),
    "unsafe_impl": re.compile(r"\bunsafe\s+impl\b"),
    "may_dangle": re.compile(r"#\s*\[\s*may_dangle\s*\]"),
    "rustc_nounwind": re.compile(r"#\s*\[\s*rustc_nounwind\s*\]"),
    "kani_attr": re.compile(r"#\s*\[\s*kani::"),
    "safety_comment": re.compile(r"//\s*SAFETY:", re.I),
    "transmute_call": re.compile(r"\btransmute(?:_copy)?\s*(?:::<\s*|\()"),
    "asm_macro": re.compile(r"\b(?:asm|global_asm|naked_asm)!\s*[\(\[\{]"),
}


def scan_dir(lib_dir):
    stats = {k: 0 for k in PATTERNS}
    stats["rs_files"] = 0
    stats["rs_lines"] = 0
    stats["rs_code_lines"] = 0
    submodules = {}

    for root, _, files in os.walk(lib_dir):
        if "tests" in root.split(os.sep) or "benches" in root.split(os.sep):
            continue
        for f in files:
            if not f.endswith(".rs"):
                continue
            p = os.path.join(root, f)
            rel = os.path.relpath(p, lib_dir)
            top_mod = rel.split(os.sep)[0] if os.sep in rel else rel
            if top_mod == "src":
                parts = rel.split(os.sep)
                top_mod = parts[1] if len(parts) > 1 else parts[0]
            if top_mod not in submodules:
                submodules[top_mod] = {k: 0 for k in PATTERNS}
                submodules[top_mod]["rs_files"] = 0
                submodules[top_mod]["rs_lines"] = 0
                submodules[top_mod]["rs_code_lines"] = 0

            stats["rs_files"] += 1
            submodules[top_mod]["rs_files"] += 1
            with open(p, "r", encoding="utf-8", errors="replace") as fh:
                content = fh.read()
            lines = content.splitlines()
            stats["rs_lines"] += len(lines)
            submodules[top_mod]["rs_lines"] += len(lines)
            code_l = sum(1 for l in lines if l.strip() and not l.strip().startswith("//"))
            stats["rs_code_lines"] += code_l
            submodules[top_mod]["rs_code_lines"] += code_l

            for k, pat in PATTERNS.items():
                cnt = len(pat.findall(content))
                stats[k] += cnt
                submodules[top_mod][k] += cnt

    stats["safe_fn_approx"] = max(0, stats["safe_or_total_fn"] - stats["unsafe_fn"])
    # Sort top 12 submodules by unsafe_block + unsafe_fn
    top_subs = sorted(
        submodules.items(),
        key=lambda kv: kv[1]["unsafe_block"] + kv[1]["unsafe_fn"],
        reverse=True,
    )[:15]
    stats["top_submodules_by_unsafe"] = {k: v for k, v in top_subs}
    return stats


def main():
    lib_root = os.path.join(RUST_ROOT, "library")
    results = {}
    for crate in ["core", "alloc", "std", "portable-simd", "stdarch"]:
        cdir = os.path.join(lib_root, crate)
        if os.path.isdir(cdir):
            results[crate] = scan_dir(cdir)
            print(
                f"{crate}: {results[crate]['rs_files']} files, {results[crate]['rs_code_lines']} LOC, "
                f"unsafe_fn={results[crate]['unsafe_fn']}, safe_fn={results[crate]['safe_fn_approx']}, "
                f"unsafe_block={results[crate]['unsafe_block']}, unsafe_impl={results[crate]['unsafe_impl']}, "
                f"SAFETY_comments={results[crate]['safety_comment']}, kani_attr={results[crate]['kani_attr']}"
            )
    with open(OUT_JSON, "w", encoding="utf-8") as fh:
        json.dump(results, fh, indent=2)
    print("Wrote", OUT_JSON)


if __name__ == "__main__":
    main()
