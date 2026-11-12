#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Track 5 benchmark harness for anneal-rustc-capture (Experiments 5A and 5B)."""

import hashlib
import json
import os
import shutil
import statistics
import subprocess
import time
from pathlib import Path

TRACK5_DIR = Path("/tmp/ref_research_stack221_perf/track5")
FIXTURES_DIR = Path("/tmp/ref_research_stack221_perf/fixtures")
BASELINE_BIN = Path("/tmp/ref_research_stack221_perf/mvp_src/target/release/anneal-rustc-capture")
CARGO_ANNEAL_BIN = Path("/tmp/ref_research_stack221_perf/mvp_src/target/release/cargo-anneal")
INST_BIN = TRACK5_DIR / "workspace/target/release/anneal-rustc-capture"
SYSROOT = Path(
    "/usr/local/google/home/joshlf/.rustup/toolchains/nightly-2026-05-31-x86_64-unknown-linux-gnu"
)


def generate_synthetic_crate(n_funcs: int, out_dir: Path) -> Path:
    """Generate a synthetic Rust library crate with n_funcs scalar functions."""
    out_dir.mkdir(parents=True, exist_ok=True)
    lib_rs = out_dir / "lib.rs"
    lines = [
        "// Synthetic crate for Track 5 scaling benchmark",
        "#![no_std]",
        "",
        "pub enum Mode {",
        "    Fast,",
        "    Safe,",
        "    Fallback,",
        "}",
        "",
    ]
    for i in range(n_funcs):
        lines.extend([
            f"pub fn func_{i}(x: u64, y: u64, flag: bool) -> u64 {{",
            f"    let a = x + {i + 1};",
            f"    let b = y ^ {i * 7 + 3};",
            "    if flag {",
            "        (a & 0xffff_ffff) | ((b & 0xffff) << 16)",
            "    } else {",
            "        let c = a - b;",
            "        if c > 100 { c >> 2 } else { c << 1 }",
            "    }",
            "}",
            "",
        ])
    lib_rs.write_text("\n".join(lines), encoding="utf-8")
    return lib_rs


def measure_host_and_startup_overheads(trials: int = 15) -> dict:
    """Measure ld.so startup, binary SHA-256 hashing, and cargo metadata overheads."""
    env = os.environ.copy()
    env["LD_LIBRARY_PATH"] = str(SYSROOT / "lib")

    # 1. Binary SHA-256 hashing (verify.rs hashes anneal-rustc-capture twice per verify run)
    hash_times_ms = []
    bin_size = BASELINE_BIN.stat().st_size
    for _ in range(trials):
        t0 = time.perf_counter()
        data = BASELINE_BIN.read_bytes()
        _ = hashlib.sha256(data).hexdigest()
        hash_times_ms.append((time.perf_counter() - t0) * 1000.0)

    # 2. anneal-rustc-capture --version (process spawn + ld.so relocation of 342 MiB .so)
    cap_ver_ms = []
    for _ in range(trials):
        t0 = time.perf_counter()
        subprocess.run(
            [str(BASELINE_BIN), "--version"],
            env=env,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=True,
        )
        cap_ver_ms.append((time.perf_counter() - t0) * 1000.0)

    # 3. $SYSROOT/bin/rustc --version --verbose (called TWICE by check_compiler)
    rustc_ver_ms = []
    for _ in range(trials):
        t0 = time.perf_counter()
        subprocess.run(
            [str(SYSROOT / "bin/rustc"), "--version", "--verbose"],
            env=env,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=True,
        )
        rustc_ver_ms.append((time.perf_counter() - t0) * 1000.0)

    # 4. cargo metadata --format-version=1 --no-deps --offline (used when --manifest-path is passed)
    dummy_cargo_dir = TRACK5_DIR / "dummy_cargo_pkg"
    (dummy_cargo_dir / "src").mkdir(parents=True, exist_ok=True)
    (dummy_cargo_dir / "Cargo.toml").write_text(
        '[package]\nname = "dummy"\nversion = "0.1.0"\nedition = "2024"\n',
        encoding="utf-8",
    )
    (dummy_cargo_dir / "src/lib.rs").write_text("pub fn f() -> u64 { 0 }\n", encoding="utf-8")
    cargo_meta_ms = []
    for _ in range(trials):
        t0 = time.perf_counter()
        subprocess.run(
            [
                str(SYSROOT / "bin/cargo"),
                "metadata",
                "--format-version=1",
                "--no-deps",
                "--offline",
                "--manifest-path",
                str(dummy_cargo_dir / "Cargo.toml"),
            ],
            env=env,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            check=True,
        )
        cargo_meta_ms.append((time.perf_counter() - t0) * 1000.0)

    return {
        "capture_binary_bytes": bin_size,
        "librustc_driver_so_bytes": (
            SYSROOT / "lib/librustc_driver-5d5a3c5207375ffc.so"
        ).stat().st_size,
        "libllvm_so_bytes": (
            SYSROOT / "lib/libLLVM.so.22.1-rust-1.98.0-nightly"
        ).stat().st_size,
        "libcore_rmeta_bytes": (
            SYSROOT
            / "lib/rustlib/x86_64-unknown-linux-gnu/lib/libcore-9b5ee718dbd50930.rmeta"
        ).stat().st_size,
        "capture_binary_sha256_single_ms_median": round(statistics.median(hash_times_ms), 3),
        "capture_binary_sha256_double_ms_median": round(2 * statistics.median(hash_times_ms), 3),
        "capture_version_spawn_ldso_ms_median": round(statistics.median(cap_ver_ms), 3),
        "capture_version_spawn_ldso_ms_p90": round( sorted(cap_ver_ms)[int(0.9 * len(cap_ver_ms))], 3),
        "rustc_version_verbose_spawn_ms_median": round(statistics.median(rustc_ver_ms), 3),
        "rustc_version_verbose_double_ms_median": round(2 * statistics.median(rustc_ver_ms), 3),
        "cargo_metadata_no_deps_offline_ms_median": round(statistics.median(cargo_meta_ms), 3),
    }


def build_capture_cmd(
    binary: Path,
    crate_root: Path,
    crate_name: str,
    out_dir: Path,
    source_files: list[Path],
    scope: str | None = None,
    select: list[str] | None = None,
) -> list[str]:
    cmd = [
        str(binary),
        "capture",
        "--crate-root",
        str(crate_root),
        "--crate-name",
        crate_name,
        "--edition",
        "2024",
        "--target",
        "x86_64-unknown-linux-gnu",
        "--out-dir",
        str(out_dir),
        "--sysroot",
        str(SYSROOT),
    ]
    if scope:
        cmd.extend(["--scope", scope])
    if select:
        for s in select:
            cmd.extend(["--select", s])
    for sf in source_files:
        cmd.extend(["--source-file", str(sf)])
    return cmd


def run_profiled_workload(
    name: str,
    crate_root: Path,
    crate_name: str,
    source_files: list[Path],
    scope: str | None = None,
    select: list[str] | None = None,
    mode_env: dict[str, str] | None = None,
    trials: int = 5,
) -> dict:
    env = os.environ.copy()
    env["LD_LIBRARY_PATH"] = str(SYSROOT / "lib")
    env["ANNEAL_PROFILE"] = "1"
    if mode_env:
        env.update(mode_env)

    wall_ms_list = []
    in_proc_ms_list = []
    last_data = None
    out_base = TRACK5_DIR / "bench_runs" / name
    for i in range(trials):
        out_dir = out_base / f"trial_{i}"
        if out_dir.exists():
            shutil.rmtree(out_dir)
        cmd = build_capture_cmd(
            INST_BIN, crate_root, crate_name, out_dir, source_files, scope, select
        )
        t0 = time.perf_counter()
        proc = subprocess.run(cmd, env=env, capture_output=True, text=True, check=True)
        wall_ms = (time.perf_counter() - t0) * 1000.0
        wall_ms_list.append(wall_ms)
        data = json.loads(proc.stdout)
        in_proc_ms_list.append(data["profile"]["total_in_process_us"] / 1000.0)
        last_data = data

    # Pick the trial closest to median in-process time for representative breakdown
    med_wall = statistics.median(wall_ms_list)
    med_in_proc = statistics.median(in_proc_ms_list)
    return {
        "wall_ms_median": round(med_wall, 2),
        "wall_ms_min": round(min(wall_ms_list), 2),
        "wall_ms_max": round(max(wall_ms_list), 2),
        "in_process_ms_median": round(med_in_proc, 2),
        "spawn_and_ldso_overhead_ms": round(med_wall - med_in_proc, 2),
        "selected_count": last_data["selected_count"],
        "census_count": last_data["census_count"],
        "source_count": last_data["source_count"],
        "profile": last_data["profile"],
    }


def main():
    results = {}
    print("Measuring host and startup overheads...")
    results["host_and_startup"] = measure_host_and_startup_overheads()

    # Workloads
    scalar_root = FIXTURES_DIR / "scalar/rust/lib.rs"
    spin_root = FIXTURES_DIR / "spin/rust/lib.rs"
    starnix_dir = FIXTURES_DIR / "starnix/source"
    starnix_files = sorted(starnix_dir.glob("*.rs"))

    workloads = [
        ("scalar", scalar_root, "scalar", [scalar_root], "crate", None),
        ("spin", spin_root, "spin", [spin_root], "crate", None),
        (
            "starnix_select_1",
            starnix_dir / "lib.rs",
            "ebpf_core",
            starnix_files,
            None,
            ["api::apply_endianness"],
        ),
    ]

    for n in [10, 50, 200, 500]:
        synth_root = generate_synthetic_crate(n, TRACK5_DIR / "synth_crates" / f"synth_{n}")
        workloads.append(
            (f"synth_{n}_select_1", synth_root, f"synth_{n}", [synth_root], None, ["func_0"])
        )
        workloads.append(
            (f"synth_{n}_scope_crate", synth_root, f"synth_{n}", [synth_root], "crate", None)
        )

    # Experiment 5A: Baseline micro-phase breakdown across all workloads
    print("Running Experiment 5A baseline micro-phase breakdown...")
    exp5a = {}
    for w_name, c_root, c_name, s_files, scope, select in workloads:
        print(f"  Profiling {w_name}...")
        exp5a[w_name] = run_profiled_workload(
            f"exp5a_{w_name}", c_root, c_name, s_files, scope, select, mode_env={}, trials=5
        )
    results["experiment_5a"] = exp5a

    # Experiment 5B: Optimization modes on scalar, starnix_select_1, synth_50_select_1, synth_200_select_1, synth_500_select_1
    opt_modes = {
        "B0_baseline": {},
        "B1_dedup_rustc_check": {"ANNEAL_OPT_RUSTC_CHECK": "once"},
        "B2_inproc_rustc_check": {"ANNEAL_OPT_RUSTC_CHECK": "inprocess"},
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

    target_5b = [w for w in workloads if w[0] in {
        "scalar",
        "starnix_select_1",
        "synth_10_select_1",
        "synth_50_select_1",
        "synth_200_select_1",
        "synth_500_select_1",
        "synth_200_scope_crate",
    }]

    print("Running Experiment 5B optimization matrix...")
    exp5b = {}
    for w_name, c_root, c_name, s_files, scope, select in target_5b:
        exp5b[w_name] = {}
        for m_name, m_env in opt_modes.items():
            if scope == "crate" and m_name in {
                "B4_select_only_borrowck",
                "B5_select_coherence_plus_root",
                "B6_select_pure_root",
            }:
                continue
            print(f"  {w_name} -> {m_name}...")
            exp5b[w_name][m_name] = run_profiled_workload(
                f"exp5b_{w_name}_{m_name}",
                c_root,
                c_name,
                s_files,
                scope,
                select,
                mode_env=m_env,
                trials=5,
            )
    results["experiment_5b"] = exp5b

    # Experiment 5B Part 2: Persistent daemon / worker mode (ANNEAL_DAEMON_ITERS=8)
    print("Running Experiment 5B persistent worker / daemon mode...")
    daemon_results = {}
    for w_name, c_root, c_name, s_files, scope, select in [
        w for w in workloads if w[0] in {"scalar", "spin", "starnix_select_1", "synth_200_select_1", "synth_500_select_1"}
    ]:
        daemon_results[w_name] = {}
        for m_name in ["B3_stop_after_analysis", "B4_select_only_borrowck", "B5_select_coherence_plus_root", "B6_select_pure_root"]:
            if scope == "crate" and m_name != "B3_stop_after_analysis":
                continue
            env = os.environ.copy()
            env["LD_LIBRARY_PATH"] = str(SYSROOT / "lib")
            env["ANNEAL_DAEMON_ITERS"] = "8"
            env.update(opt_modes[m_name])
            out_dir = TRACK5_DIR / "bench_runs" / f"daemon_{w_name}_{m_name}"
            if out_dir.exists():
                shutil.rmtree(out_dir)
            cmd = build_capture_cmd(INST_BIN, c_root, c_name, out_dir, s_files, scope, select)
            proc = subprocess.run(cmd, env=env, capture_output=True, text=True, check=True)
            data = json.loads(proc.stdout)
            iters_ms = [round(u / 1000.0, 2) for u in data["daemon_iters_us"]]
            daemon_results[w_name][m_name] = {
                "iters_ms": iters_ms,
                "iter0_cold_session_ms": iters_ms[0],
                "warm_median_ms": round(statistics.median(iters_ms[1:]), 2),
                "warm_min_ms": round(min(iters_ms[1:]), 2),
            }
    results["daemon_worker"] = daemon_results

    out_file = TRACK5_DIR / "support/track5_benchmark_results.json"
    out_file.write_text(json.dumps(results, indent=2), encoding="utf-8")
    print(f"Saved complete results to {out_file}")


if __name__ == "__main__":
    main()
