#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Verification harness for Package: x86-64-adler32-simd-lane-overflow-bounds-and-avx512-codegen-width."""

import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent


def lean_wrap(cmd: list[str]) -> list[str]:
    if shutil.which("anneal-lean-run"):
        return ["anneal-lean-run", "--mode", "file", "--concurrency", "1", "--", *cmd]
    return cmd


def fn_body(asm_txt: str, sym: str) -> str:
    m = re.search(rf"^{re.escape(sym)}:\n(.*?\.cfi_endproc)", asm_txt, re.M | re.S)
    assert m, f"Missing symbol {sym}"
    return m.group(1)


def main() -> int:
    # 1. Lean 4 lane overflow bounds
    lean_p = subprocess.run(
        lean_wrap(["elan", "run", "leanprover/lean4:v4.34.1", "lean", str(HERE / "AdlerSimdOverflowBounds.lean")]),
        capture_output=True,
        text=True,
        check=True,
    )
    assert lean_p.stdout.strip() == "", lean_p.stdout

    summary = {"status": "PASS", "lean_bounds": "PASS"}
    probe_rs = HERE / "adler32_vnni_and_bmi2_probe.rs"

    with tempfile.TemporaryDirectory(prefix="pkg6_simd_") as td:
        tmp = Path(td)
        # 2. +prefer-256-bit (default icelake-client) vs -prefer-256-bit assembly and timings
        for mode, flags in [
            ("default_prefer_256", ["-C", "target-cpu=icelake-client"]),
            ("forced_zmm", ["-C", "target-cpu=icelake-client", "-C", "target-feature=+avx512bw,+avx512vnni,-prefer-256-bit"]),
        ]:
            s_path = tmp / f"{mode}.s"
            b_path = tmp / f"{mode}_bin"
            subprocess.run(["rustc", "--edition", "2021", "-C", "opt-level=3", *flags, "--emit=asm", str(probe_rs), "-o", str(s_path)], check=True)
            subprocess.run(["rustc", "--edition", "2021", "-C", "opt-level=3", *flags, str(probe_rs), "-o", str(b_path)], check=True)
            s_txt = s_path.read_text()
            safe64_b = fn_body(s_txt, "adler_safe_64lane_u16_16")
            ifma_b = fn_body(s_txt, "adler_reduce_weights_only")
            bmi2_b = fn_body(s_txt, "bmi2_shrx_bzhi")
            assert "vpmadd52" in ifma_b
            assert "shrx" in bmi2_b and "bzhi" in bmi2_b
            if mode == "default_prefer_256":
                assert len(re.findall(r"%zmm", safe64_b)) == 0 and len(re.findall(r"%ymm", safe64_b)) > 0
            else:
                assert len(re.findall(r"%zmm", safe64_b)) > 0

            cmd = ["taskset", "-c", "4", str(b_path)] if shutil.which("taskset") else [str(b_path)]
            out = subprocess.run(cmd, check=True, capture_output=True, text=True).stdout
            assert "PSHUFB_1_TO_15=PASS" in out and "SIGNED_I32_BUG" in out
            summary[mode] = {
                "safe64_ymm": len(re.findall(r"%ymm", safe64_b)),
                "safe64_zmm": len(re.findall(r"%zmm", safe64_b)),
                "vpmadd52_ops": len(re.findall(r"vpmadd52", ifma_b)),
                "bmi2_shrx": len(re.findall(r"shrx", bmi2_b)),
                "bmi2_bzhi": len(re.findall(r"bzhi", bmi2_b)),
                "lines": out.strip().splitlines(),
            }

        # 3. Miri MaybeUninit straddle test
        mcrate = tmp / "miri_crate"
        (mcrate / "src").mkdir(parents=True)
        (mcrate / "Cargo.toml").write_text('[package]\nname = "miri_straddle"\nversion = "0.1.0"\nedition = "2021"\n')
        shutil.copy2(HERE / "miri_uninit_straddle_probe.rs", mcrate / "src" / "lib.rs")
        miri_ok = subprocess.run(["cargo", "+nightly", "miri", "test"], cwd=mcrate, check=True, capture_output=True, text=True)
        miri_ub = subprocess.run(
            ["cargo", "+nightly", "miri", "test", "--", "--ignored", "ub_dist4_straddles_uninit"],
            cwd=mcrate,
            capture_output=True,
            text=True,
        )
        assert miri_ub.returncode != 0 and "encountered uninitialized memory" in (miri_ub.stderr + miri_ub.stdout)
        summary["miri"] = {
            "ok_tests": [l for l in miri_ok.stdout.splitlines() if "test result:" in l],
            "ub_dist4_detected": True,
        }

    print(json.dumps(summary, indent=2))
    return 0


if __name__ == "__main__":
    sys.exit(main())
