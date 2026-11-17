#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Verification harness for Package: rust-safe-byte-kernel-bounds-check-elimination-and-autovectorization-idioms."""

import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
SRC = HERE / "safe_bce_and_llvm_probe.rs"


def parse_asm(asm_text: str) -> dict[str, dict]:
    out = {}
    for m in re.finditer(r"^([A-Za-z0-9_]+):\n(.*?\.cfi_endproc)", asm_text, re.M | re.S):
        sym, body = m.group(1), m.group(2)
        insns = [l for l in body.splitlines() if l.startswith("\t") and not l.strip().startswith(".")]
        calls = re.findall(r"call\w*\s+\*?([^\s@]+)", body)
        panics = [c for c in calls if any(p in c for p in ("panic", "slice_index_fail", "bounds_check"))]
        out[sym] = {
            "insns": len(insns),
            "panics": len(panics),
            "rsp_refs": len(re.findall(r"%rsp", body)),
            "ymm": len(re.findall(r"%ymm", body)),
            "zmm": len(re.findall(r"%zmm", body)),
            "vpaddd": len(re.findall(r"\bvpaddd\b", body)),
            "vpminuq": len(re.findall(r"\bvpminuq\b", body)),
            "vpaddq": len(re.findall(r"\bvpaddq\b", body)),
        }
    return out


def main() -> int:
    ver = subprocess.check_output(["rustc", "--edition", "2021", "-vV"], text=True).splitlines()[0]
    with tempfile.TemporaryDirectory(prefix="pkg5_bce_") as td:
        tmp = Path(td)
        asm_path = tmp / "probe.s"
        bin_path = tmp / "probe_bin"
        subprocess.run(
            ["rustc", "--edition", "2021", "-C", "opt-level=3", "-C", "target-cpu=icelake-client", "--emit=asm", str(SRC), "-o", str(asm_path)],
            check=True,
        )
        subprocess.run(
            ["rustc", "--edition", "2021", "-C", "opt-level=3", "-C", "target-cpu=icelake-client", str(SRC), "-o", str(bin_path)],
            check=True,
        )
        stats = parse_asm(asm_path.read_text())

        # Structural BCE & auto-vectorization invariants
        assert stats["bce_chunks_exact4"]["panics"] == 0 and stats["bce_as_chunks4"]["panics"] == 0
        assert stats["bce_while_index4"]["panics"] > 0
        assert stats["bce_slice_mask"]["panics"] > 0
        assert stats["bce_box_array_mask"]["panics"] == 0 and stats["bce_ref_array_mask"]["panics"] == 0
        assert stats["bce_first_chunk4"]["panics"] == 0 and stats["bce_shifted_read4"]["panics"] > 0
        assert (
            stats["dp_relax_zipped"]["rsp_refs"] == 0
            and stats["dp_relax_zipped"]["vpminuq"] > 0
            and stats["dp_relax_zipped"]["vpaddq"] > 0
        )
        assert stats["adler_while_fixed4"]["panics"] == 0 and stats["adler_while_fixed4"]["vpaddd"] > 0
        assert stats["adler_chunks_exact_4lane"]["panics"] == 0 and stats["adler_chunks_exact_4lane"]["vpaddd"] > 0
        assert stats["adler_while_varindex4"]["vpaddd"] == 0
        assert stats["adler_serial_while"]["vpaddd"] == 0
        assert stats["chain_shifted_views"]["rsp_refs"] <= stats["chain_subslice_first_chunk"]["rsp_refs"]
        assert stats["loop_unsafe_lit"]["panics"] == 0 and stats["loop_unsafe_lit"]["insns"] < stats["loop_safe_double_lit"]["insns"]

        cmd = ["taskset", "-c", "4", str(bin_path)] if shutil.which("taskset") else [str(bin_path)]
        res = subprocess.run(cmd, check=True, capture_output=True, text=True)

        metrics = {}
        for line in res.stdout.splitlines():
            parts = line.split()
            if parts and parts[0] in ("ADLER", "LIT"):
                metrics[f"{parts[0]}_{parts[1]}"] = float(parts[-2])
            elif line.startswith("ALLOC "):
                for kv in parts[1:]:
                    k, v = kv.split("=")
                    metrics[k] = float(v)

        assert metrics["ADLER_while_fixed4"] > 1.5 * metrics["ADLER_while_varindex4"]
        assert metrics["ADLER_while_fixed4"] > 1.5 * metrics["ADLER_serial_while"]

    print(
        json.dumps(
            {
                "status": "PASS",
                "rustc": ver,
                "asm_stats": stats,
                "timings": metrics,
            },
            indent=2,
        )
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
