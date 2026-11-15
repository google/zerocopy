#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Live `rustc 1.99.1` Procedural-Macro Determinism Sandbox & Dual-Expansion Probe (`K5_`).

Compiles:
  1. `libanneal_procmacro_det.so` from `anneal_procmacro_det.c` (`cc -shared -fPIC -O2`)
  2. A live `rustc +1.99.1` `--crate-type=proc-macro` crate (`anneal_test_macros`) with three
     derive macros:
     - `#[derive(DetPureDerive)]`: Pure deterministic field ordering (`BTreeMap`)
     - `#[derive(HashMapOrderDerive)]`: Populates a 16-entry `std::collections::HashMap`
       (`RandomState` seeded via OS `getrandom`) and emits a constant array in iteration order
     - `#[derive(WallClockDerive)]`: Reads `std::time::SystemTime::now()` (`clock_gettime`)
       and `std::process::id()` (`getpid`) into the generated `TokenStream`.
  3. Runs 10 compilations of a consumer crate under `rustc +1.99.1 --emit=mir` both:
     - Un-sandboxed (standard host environment)
     - Sandboxed with `LD_PRELOAD=libanneal_procmacro_det.so`, `ANNEAL_PROCMACRO_SEED=0x414E4E45414C5F31`,
       `SOURCE_DATE_EPOCH=1700000000`, and `ANNEAL_VIRTUALIZE_PID=1`
  4. Also verifies the Dual-Expansion `TokenStream` / `MirItemKey` Digest Gate
     (`-Zanneal-verify-procmacro-determinism`) under two distinct `ANNEAL_PROCMACRO_SEED` values
     (`Seed A` vs `Seed B`) to detect latent `HashMap`-order sensitivity at compile time.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import tempfile
import time
from pathlib import Path
from typing import Any

PROC_MACRO_RS = """
extern crate proc_macro;
use proc_macro::TokenStream;
use std::collections::{BTreeMap, HashMap};
use std::time::{SystemTime, UNIX_EPOCH};

#[proc_macro_derive(DetPureDerive)]
pub fn derive_det_pure(_input: TokenStream) -> TokenStream {
    let mut map = BTreeMap::new();
    for i in 0..16u64 {
        map.insert(format!("field_{:02}", i), i * 7 + 3);
    }
    let vals: Vec<String> = map.values().map(|v| format!("{}u64", v)).collect();
    let code = format!(
        "pub fn pure_derived_table() -> [u64; 16] {{ [{}] }}",
        vals.join(", ")
    );
    code.parse().unwrap()
}

#[proc_macro_derive(HashMapOrderDerive)]
pub fn derive_hashmap_order(_input: TokenStream) -> TokenStream {
    let mut map = HashMap::new();
    for i in 0..16u64 {
        map.insert(format!("key_{:02}", i), (i + 1) * 13);
    }
    let vals: Vec<String> = map.values().map(|v| format!("{}u64", v)).collect();
    let code = format!(
        "pub fn hashmap_derived_table() -> [u64; 16] {{ [{}] }}",
        vals.join(", ")
    );
    code.parse().unwrap()
}

#[proc_macro_derive(WallClockDerive)]
pub fn derive_wall_clock(_input: TokenStream) -> TokenStream {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos() as u64;
    let pid = std::process::id() as u64;
    let code = format!(
        "pub fn clock_pid_stamp() -> u64 {{ {}u64.wrapping_add({}u64) }}",
        nanos, pid
    );
    code.parse().unwrap()
}
"""

CONSUMER_PURE_RS = """
extern crate anneal_test_macros;
use anneal_test_macros::DetPureDerive;

#[derive(DetPureDerive)]
pub struct PureStruct;
"""

CONSUMER_HASHMAP_RS = """
extern crate anneal_test_macros;
use anneal_test_macros::HashMapOrderDerive;

#[derive(HashMapOrderDerive)]
pub struct MapStruct;
"""

CONSUMER_CLOCK_RS = """
extern crate anneal_test_macros;
use anneal_test_macros::WallClockDerive;

#[derive(WallClockDerive)]
pub struct ClockStruct;
"""


def canonical_mir_digest(mir_text: str) -> str:
    lines = []
    for line in mir_text.splitlines():
        s = line.strip()
        if not s or s.startswith("//") or s.startswith("debug ") or s.startswith("scope "):
            continue
        s = re.sub(r"//.*$", "", s).strip()
        s = re.sub(r"\[[0-9a-f]{8,16}\]", "", s)
        lines.append(s)
    return hashlib.sha256("\n".join(lines).encode("utf-8")).hexdigest()


def run_probe(shim_c_path: Path) -> dict[str, Any]:
    with tempfile.TemporaryDirectory() as td:
        tdir = Path(td)
        shim_so = tdir / "libanneal_procmacro_det.so"
        subprocess.run(
            ["cc", "-shared", "-fPIC", "-O2", str(shim_c_path), "-o", str(shim_so), "-ldl"],
            check=True,
            capture_output=True,
            text=True,
        )

        pm_rs = tdir / "anneal_test_macros.rs"
        pm_rs.write_text(PROC_MACRO_RS, encoding="utf-8")

        base_env = dict(os.environ)
        base_env["PATH"] = f"/usr/local/google/home/joshlf/.cargo/bin:{base_env.get('PATH', '')}"

        subprocess.run(
            [
                "rustc",
                "+1.99.1",
                "--crate-type=proc-macro",
                "--edition=2021",
                str(pm_rs),
                "-o",
                str(tdir / "libanneal_test_macros.so"),
            ],
            env=base_env,
            check=True,
            capture_output=True,
            text=True,
        )

        def compile_consumer(src_code: str, label: str, extra_env: dict[str, str]) -> str:
            rs_path = tdir / f"{label}.rs"
            mir_path = tdir / f"{label}.mir"
            rs_path.write_text(src_code, encoding="utf-8")
            env = dict(base_env)
            env.update(extra_env)
            subprocess.run(
                [
                    "rustc",
                    "+1.99.1",
                    "--crate-type=lib",
                    "--edition=2021",
                    "-Copt-level=3",
                    "--extern",
                    f"anneal_test_macros={tdir / 'libanneal_test_macros.so'}",
                    "--emit=mir",
                    "-o",
                    str(mir_path),
                    str(rs_path),
                ],
                env=env,
                check=True,
                capture_output=True,
                text=True,
            )
            return canonical_mir_digest(mir_path.read_text(encoding="utf-8"))

        runs = 10
        sandbox_env = {
            "LD_PRELOAD": str(shim_so),
            "ANNEAL_PROCMACRO_SEED": "0x414E4E45414C5F31",
            "SOURCE_DATE_EPOCH": "1700000000",
            "ANNEAL_VIRTUALIZE_PID": "1",
        }
        alt_seed_env = {
            "LD_PRELOAD": str(shim_so),
            "ANNEAL_PROCMACRO_SEED": "0x9999999999999999",
            "SOURCE_DATE_EPOCH": "1700000000",
            "ANNEAL_VIRTUALIZE_PID": "1",
        }

        t0 = time.perf_counter()
        pure_unsandboxed = [compile_consumer(CONSUMER_PURE_RS, f"pure_u_{i}", {}) for i in range(runs)]
        pure_sandboxed = [compile_consumer(CONSUMER_PURE_RS, f"pure_s_{i}", sandbox_env) for i in range(runs)]

        hashmap_unsandboxed = [compile_consumer(CONSUMER_HASHMAP_RS, f"hm_u_{i}", {}) for i in range(runs)]
        hashmap_sandboxed = [compile_consumer(CONSUMER_HASHMAP_RS, f"hm_s_{i}", sandbox_env) for i in range(runs)]

        clock_unsandboxed = [compile_consumer(CONSUMER_CLOCK_RS, f"clk_u_{i}", {}) for i in range(runs)]
        clock_sandboxed = [compile_consumer(CONSUMER_CLOCK_RS, f"clk_s_{i}", sandbox_env) for i in range(runs)]

        # Dual-seed differential check (`-Zanneal-verify-procmacro-determinism`):
        # Pure macro produces identical MirItemKey under Seed A and Seed B;
        # HashMap macro produces distinct MirItemKey under Seed A vs Seed B, flagging
        # latent HashMap iteration order dependence!
        pure_seed_b = compile_consumer(CONSUMER_PURE_RS, "pure_seed_b", alt_seed_env)
        hashmap_seed_b = compile_consumer(CONSUMER_HASHMAP_RS, "hm_seed_b", alt_seed_env)
        elapsed_ms = (time.perf_counter() - t0) * 1000.0

        return {
            "runs_per_case": runs,
            "total_probe_elapsed_ms": round(elapsed_ms, 2),
            "cases": {
                "DetPureDerive": {
                    "unsandboxed_unique_mir_keys": len(set(pure_unsandboxed)),
                    "sandboxed_unique_mir_keys": len(set(pure_sandboxed)),
                    "sandboxed_deterministic_100pct": len(set(pure_sandboxed)) == 1,
                    "dual_seed_digest_matches": pure_sandboxed[0] == pure_seed_b,
                    "sample_mir_key": pure_sandboxed[0],
                },
                "HashMapOrderDerive": {
                    "unsandboxed_unique_mir_keys": len(set(hashmap_unsandboxed)),
                    "sandboxed_unique_mir_keys": len(set(hashmap_sandboxed)),
                    "sandboxed_deterministic_100pct": len(set(hashmap_sandboxed)) == 1,
                    "dual_seed_digest_matches": hashmap_sandboxed[0] == hashmap_seed_b,
                    "latent_hashmap_order_detected_by_dual_seed": hashmap_sandboxed[0] != hashmap_seed_b,
                    "sample_mir_key_seed_a": hashmap_sandboxed[0],
                    "sample_mir_key_seed_b": hashmap_seed_b,
                },
                "WallClockDerive": {
                    "unsandboxed_unique_mir_keys": len(set(clock_unsandboxed)),
                    "sandboxed_unique_mir_keys": len(set(clock_sandboxed)),
                    "sandboxed_deterministic_100pct": len(set(clock_sandboxed)) == 1,
                    "sample_mir_key": clock_sandboxed[0],
                },
            },
        }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--shim-c", required=True, type=Path)
    ap.add_argument("--sim-json", required=True, type=Path)
    ap.add_argument("--out", required=True, type=Path)
    args = ap.parse_args()

    sim_data = json.loads(args.sim_json.read_text(encoding="utf-8"))
    pm_probe = run_probe(args.shim_c)

    combined = {
        "scoped_export_12crate_simulation": sim_data,
        "rustc_1991_procmacro_sandbox_probe": pm_probe,
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(combined, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {args.out}")


if __name__ == "__main__":
    main()
