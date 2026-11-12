#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Soundness & compilation-equivalence probes for anneal-rustc-capture optimization modes."""

import json
import os
import shutil
import subprocess
from pathlib import Path

TRACK5_DIR = Path("/tmp/ref_research_stack221_perf/track5")
INST_BIN = TRACK5_DIR / "workspace/target/release/anneal-rustc-capture"
SYSROOT = Path(
    "/usr/local/google/home/joshlf/.rustup/toolchains/nightly-2026-05-31-x86_64-unknown-linux-gnu"
)

PROBES = {
    "S1_unselected_borrowck_error": """
#![no_std]
pub fn target(x: u64) -> u64 { x }
pub fn unselected_bad_borrow() -> u64 {
    let mut v = 1u64;
    let r1 = &mut v;
    let r2 = &mut v;
    *r1 + *r2
}
""",
    "S2_unselected_typeck_error": """
#![no_std]
pub fn target(x: u64) -> u64 { x }
pub fn unselected_bad_type() -> u64 {
    true
}
""",
    "S3_unselected_coherence_overlap": """
#![no_std]
pub trait MyTrait { fn f() -> u64; }
pub struct S;
impl MyTrait for S { fn f() -> u64 { 1 } }
impl MyTrait for S { fn f() -> u64 { 2 } }
pub fn target(x: u64) -> u64 { x }
""",
    "S4_unselected_const_eval_panic": """
#![no_std]
pub const BAD_CONST: u64 = 1 / 0;
pub fn target(x: u64) -> u64 { x }
""",
    "S5_deny_unused_features_gate": """
#![no_std]
#![deny(unused_features)]
#![feature(never_type)]
pub fn target(x: u64) -> u64 { x }
""",
    "S6_deny_dead_code_lint": """
#![no_std]
#![deny(dead_code)]
fn dead_helper() -> u64 { 42 }
pub fn target(x: u64) -> u64 { x }
""",
}

MODES = {
    "B0_baseline": {},
    "B3_stop_after_analysis": {
        "ANNEAL_OPT_RUSTC_CHECK": "inprocess",
        "ANNEAL_OPT_STOP_AFTER_ANALYSIS": "1",
    },
    "B4_select_only_borrowck": {
        "ANNEAL_OPT_RUSTC_CHECK": "inprocess",
        "ANNEAL_OPT_STOP_AFTER_ANALYSIS": "1",
        "ANNEAL_OPT_SELECT_ONLY_BORROWCK": "1",
    },
    "B5_select_coherence_plus_root": {
        "ANNEAL_OPT_RUSTC_CHECK": "inprocess",
        "ANNEAL_OPT_STOP_AFTER_ANALYSIS": "1",
        "ANNEAL_OPT_SELECT_ONLY_ANALYSIS": "coherence_plus_select",
    },
    "B6_select_pure_root": {
        "ANNEAL_OPT_RUSTC_CHECK": "inprocess",
        "ANNEAL_OPT_STOP_AFTER_ANALYSIS": "1",
        "ANNEAL_OPT_SELECT_ONLY_ANALYSIS": "pure_select_only",
    },
}


def main():
    probe_dir = TRACK5_DIR / "soundness_probes"
    probe_dir.mkdir(parents=True, exist_ok=True)
    summary = {}
    for p_name, code in PROBES.items():
        p_src_dir = probe_dir / p_name
        p_src_dir.mkdir(parents=True, exist_ok=True)
        lib_rs = p_src_dir / "lib.rs"
        lib_rs.write_text(code.strip() + "\n", encoding="utf-8")
        summary[p_name] = {}
        for m_name, m_env in MODES.items():
            out_dir = p_src_dir / f"out_{m_name}"
            if out_dir.exists():
                shutil.rmtree(out_dir)
            env = os.environ.copy()
            env["LD_LIBRARY_PATH"] = str(SYSROOT / "lib")
            env.update(m_env)
            proc = subprocess.run(
                [
                    str(INST_BIN),
                    "capture",
                    "--crate-root",
                    str(lib_rs),
                    "--crate-name",
                    "probe",
                    "--edition",
                    "2024",
                    "--target",
                    "x86_64-unknown-linux-gnu",
                    "--out-dir",
                    str(out_dir),
                    "--sysroot",
                    str(SYSROOT),
                    "--select",
                    "target",
                    "--source-file",
                    str(lib_rs),
                ],
                env=env,
                capture_output=True,
                text=True,
                check=False,
            )
            data = json.loads(proc.stdout)
            summary[p_name][m_name] = {
                "exit_code": proc.returncode,
                "status": data.get("status"),
            }
            print(f"{p_name:32s} | {m_name:30s} -> status={data.get('status')} (exit={proc.returncode})")

    out_path = TRACK5_DIR / "support/soundness_probe_results.json"
    out_path.write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print(f"Saved soundness probe results to {out_path}")


if __name__ == "__main__":
    main()
