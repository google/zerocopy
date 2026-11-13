#!/usr/bin/env python3
"""Reproducible probe for .rlib extra archive member tolerance and compilation settings vs. MIR output."""
import argparse
import json
import os
import re
import subprocess
import tempfile
from pathlib import Path

LIB_SRC = """#![crate_type = "rlib"]
#![crate_name = "lib_probe"]

#[inline]
pub fn add_checked(a: u32, b: u32) -> u32 {
    a + b
}

pub fn non_inline_sum(slice: &[u32]) -> u32 {
    let mut acc = 0;
    for &x in slice {
        acc += add_checked(acc, x);
    }
    acc
}

pub unsafe fn ptr_read_aligned(p: *const u32) -> u32 {
    unsafe { *p }
}
"""

MAIN_SRC = """extern crate lib_probe;
fn main() {
    let arr = [1u32, 2, 3, 4];
    let s = lib_probe::non_inline_sum(&arr);
    let v = unsafe { lib_probe::ptr_read_aligned(arr.as_ptr()) };
    assert_eq!(s + v, 27);
}
"""


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--toolchain", default="1.99.1-x86_64-unknown-linux-gnu")
    ap.add_argument("--out", required=True, type=Path)
    args = ap.parse_args()

    env = os.environ.copy()
    env["RUSTC_BOOTSTRAP"] = "1"

    with tempfile.TemporaryDirectory() as td:
        wdir = Path(td)
        (wdir / "lib_probe.rs").write_text(LIB_SRC, encoding="utf-8")
        (wdir / "main_probe.rs").write_text(MAIN_SRC, encoding="utf-8")

        rlib = wdir / "liblib_probe.rlib"
        subprocess.run(
            ["rustup", "run", args.toolchain, "rustc", "--edition=2024", "lib_probe.rs", "-o", str(rlib)],
            cwd=str(wdir),
            env=env,
            check=True,
        )
        ar_before = subprocess.check_output(["ar", "t", str(rlib)], text=True).splitlines()

        extra = wdir / "anneal_artifact.mir.bin"
        extra.write_bytes(b"ANNEAL_MIR_ARTIFACT_V1\x00payload")
        subprocess.run(["ar", "r", str(rlib), str(extra)], cwd=str(wdir), env=env, check=True)
        ar_after = subprocess.check_output(["ar", "t", str(rlib)], text=True).splitlines()

        bin_out = wdir / "main_bin"
        link_res = subprocess.run(
            [
                "rustup",
                "run",
                args.toolchain,
                "rustc",
                "--edition=2024",
                "main_probe.rs",
                "--extern",
                f"lib_probe={rlib}",
                "-o",
                str(bin_out),
            ],
            cwd=str(wdir),
            env=env,
            capture_output=True,
            text=True,
        )
        run_res = subprocess.run([str(bin_out)], cwd=str(wdir), env=env) if link_res.returncode == 0 else None

        settings = [
            ("baseline_O0_m0", ["-Copt-level=0", "-Zmir-opt-level=0"]),
            ("O0_m1_default_debug", ["-Copt-level=0"]),
            ("O2_m2_default_release", ["-Copt-level=2"]),
            ("O2_m0", ["-Copt-level=2", "-Zmir-opt-level=0"]),
            ("O2_m3", ["-Copt-level=2", "-Zmir-opt-level=3"]),
            ("O2_m4", ["-Copt-level=2", "-Zmir-opt-level=4"]),
            ("O2_no_inline_mir", ["-Copt-level=2", "-Zinline-mir=no"]),
            ("O2_overflow_checks", ["-Copt-level=2", "-Coverflow-checks=yes"]),
            ("O2_debug_assertions", ["-Copt-level=2", "-Cdebug-assertions=yes"]),
            ("O2_ub_checks", ["-Copt-level=2", "-Zub-checks=yes"]),
            ("O2_panic_abort", ["-Copt-level=2", "-Cpanic=abort"]),
            ("O2_debuginfo_2", ["-Copt-level=2", "-Cdebuginfo=2"]),
            ("O2_avx2", ["-Copt-level=2", "-Ctarget-feature=+avx2"]),
        ]
        matrix = []
        for label, flags in settings:
            mir_file = wdir / f"{label}.mir"
            subprocess.run(
                ["rustup", "run", args.toolchain, "rustc", "--edition=2024", "--emit=mir", "lib_probe.rs", "-o", str(mir_file)]
                + flags,
                cwd=str(wdir),
                env=env,
                check=True,
            )
            txt = mir_file.read_text(encoding="utf-8")
            matrix.append(
                {
                    "label": label,
                    "flags": flags,
                    "mir_lines": len(txt.splitlines()),
                    "basic_blocks": len(re.findall(r"^\s*bb\d+:\s*\{", txt, re.M)),
                    "assert_terminators": len(re.findall(r"\bassert\(", txt)),
                    "debug_var_decls": len(re.findall(r"^\s*debug\s+", txt, re.M)),
                    "add_checked_mentions": len(re.findall(r"add_checked\(", txt)),
                }
            )

        out = {
            "toolchain": args.toolchain,
            "rlib_members_before": ar_before,
            "rlib_members_after": ar_after,
            "rlib_link_exit_code": link_res.returncode,
            "rlib_binary_run_exit_code": run_res.returncode if run_res else -1,
            "settings_matrix": matrix,
        }
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
