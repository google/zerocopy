#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Revalidation runner for Package: anneal-frozen-scalar-kernel-specs-and-partial-verification-escapes.

Checks:
1. `SpecRatchetAndEscapes.lean` under pinned `leanprover/lean4:v4.34.1` via
   `anneal-lean-run --mode file --concurrency 1` (if present on PATH) or `elan run`.
2. `partial_boundary_escapes.rs` unit tests under `rustc --test`.
"""

import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent


def lean_cmd(lean_file: Path) -> list[str]:
    if shutil.which("elan"):
        base = ["elan", "run", "leanprover/lean4:v4.34.1", "lean", str(lean_file)]
    else:
        base = ["lean", str(lean_file)]
    if shutil.which("anneal-lean-run"):
        return ["anneal-lean-run", "--mode", "file", "--concurrency", "1", "--", *base]
    return base


def main() -> int:
    lean_file = HERE / "SpecRatchetAndEscapes.lean"
    lean_proc = subprocess.run(lean_cmd(lean_file), cwd=HERE, capture_output=True, text=True)
    if lean_proc.returncode != 0:
        raise RuntimeError(f"Lean probe failed:\n{lean_proc.stdout}\n{lean_proc.stderr}")

    rs_file = HERE / "partial_boundary_escapes.rs"
    with tempfile.TemporaryDirectory(prefix="pkg2_escapes_") as td:
        bin_path = Path(td) / "escapes_test"
        comp = subprocess.run(
            ["rustc", "--edition", "2021", "--test", "-O", str(rs_file), "-o", str(bin_path)],
            capture_output=True,
            text=True,
        )
        if comp.returncode != 0:
            raise RuntimeError(f"rustc compile failed:\n{comp.stderr}")
        run_p = subprocess.run([str(bin_path)], capture_output=True, text=True)
        if run_p.returncode != 0:
            raise RuntimeError(f"escapes_test failed:\n{run_p.stdout}\n{run_p.stderr}")

    print(
        json.dumps(
            {
                "status": "PASS",
                "lean_output": lean_proc.stdout.strip(),
                "rust_test_summary": [l for l in run_p.stdout.splitlines() if "test result:" in l],
            },
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
