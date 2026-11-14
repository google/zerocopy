#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Ext-TSP block placement, hot/cold splitting, and 32B loop/JCC alignment benchmark across W-Core and 16 shuffle seeds."""

import argparse
import json
import math
import os
import statistics
import subprocess
import sys
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

HERE = Path(__file__).resolve().parent
TC_ROOT = Path(os.path.expanduser("~/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu"))
RUSTC = str(TC_ROOT / "bin" / "rustc")
LLVM_BIN = TC_ROOT / "lib" / "rustlib" / "x86_64-unknown-linux-gnu" / "bin"
LLVM_PROFDATA = str(LLVM_BIN / "llvm-profdata")
LLVM_SIZE = str(LLVM_BIN / "llvm-size")

# All 8 W-Core workloads with internal high-resolution timing (prints median microseconds per pass)
WCORE_WORKLOADS = {
    "bench-serde-json": r"""
use std::time::Instant;
#[inline(never)]
pub fn kernel(input: &[u8]) -> u64 {
    let mut acc = 0u64;
    let mut in_str = false;
    let mut esc = false;
    let mut depth = 0u64;
    for &b in input {
        if in_str {
            if esc { esc = false; }
            else if b == b'\\' { esc = true; }
            else if b == b'"' { in_str = false; acc = acc.wrapping_add(depth.wrapping_mul(31)); }
            else { acc = acc.wrapping_mul(131).wrapping_add(b as u64); }
        } else {
            match b {
                b'"' => in_str = true,
                b'{' | b'[' => depth = depth.wrapping_add(1),
                b'}' | b']' => depth = depth.wrapping_sub(1),
                b':' | b',' => acc = acc.rotate_left(7) ^ depth,
                b'0'..=b'9' => acc = acc.wrapping_mul(10).wrapping_add((b - b'0') as u64),
                _ => {}
            }
        }
    }
    acc ^ depth
}
fn main() {
    let payload = br#"{"id":12345,"name":"alpha_beta_gamma","values":[10,20,30,40,50],"nested":{"ok":true,"msg":"escaped \"quote\" here"}}"#;
    let mut buf = Vec::with_capacity(payload.len() * 128);
    for _ in 0..128 { buf.extend_from_slice(payload); }
    for _ in 0..5 { std::hint::black_box(kernel(std::hint::black_box(&buf))); }
    let mut times = Vec::with_capacity(15);
    for _ in 0..15 {
        let t0 = Instant::now();
        for _ in 0..10 { std::hint::black_box(kernel(std::hint::black_box(&buf))); }
        times.push(t0.elapsed().as_nanos() as f64 / 10_000.0);
    }
    times.sort_by(|a, b| a.partial_cmp(b).unwrap());
    println!("{:.4}", times[times.len() / 2]);
}
""",
    "bench-regex-automata": r"""
use std::time::Instant;
#[inline(never)]
pub fn kernel(trans: &[u32; 1024], hay: &[u8]) -> u32 {
    let mut state = 0u32;
    let mut matches = 0u32;
    for &b in hay {
        let idx = ((state as usize) & 3) * 256 + (b as usize);
        state = unsafe { *trans.get_unchecked(idx) };
        if (state & 4) != 0 {
            matches = matches.wrapping_add(1);
            state &= 3;
        }
    }
    matches ^ state
}
fn main() {
    let mut trans = [0u32; 1024];
    for s in 0..4 {
        for b in 0..256 {
            trans[s * 256 + b] = ((s + b + 1) & 3) as u32 | if b == b'a' as usize && s == 2 { 4 } else { 0 };
        }
    }
    let hay = [b'a'; 8192];
    for _ in 0..5 { std::hint::black_box(kernel(std::hint::black_box(&trans), std::hint::black_box(&hay))); }
    let mut times = Vec::with_capacity(15);
    for _ in 0..15 {
        let t0 = Instant::now();
        for _ in 0..10 { std::hint::black_box(kernel(std::hint::black_box(&trans), std::hint::black_box(&hay))); }
        times.push(t0.elapsed().as_nanos() as f64 / 10_000.0);
    }
    times.sort_by(|a, b| a.partial_cmp(b).unwrap());
    println!("{:.4}", times[times.len() / 2]);
}
""",
    "bench-hashbrown-indexmap": r"""
use std::collections::HashMap;
use std::time::Instant;
#[inline(never)]
pub fn kernel(n: u64) -> u64 {
    let mut map = HashMap::with_capacity(256);
    for i in 0..n {
        map.insert(i.wrapping_mul(0x9e3779b97f4a7c15), i);
    }
    let mut sum = 0u64;
    for i in 0..n {
        if let Some(&v) = map.get(&i.wrapping_mul(0x9e3779b97f4a7c15)) {
            sum = sum.wrapping_add(v);
        }
    }
    sum
}
fn main() {
    for _ in 0..3 { std::hint::black_box(kernel(256)); }
    let mut times = Vec::with_capacity(15);
    for _ in 0..15 {
        let t0 = Instant::now();
        for _ in 0..5 { std::hint::black_box(kernel(std::hint::black_box(256))); }
        times.push(t0.elapsed().as_nanos() as f64 / 5_000.0);
    }
    times.sort_by(|a, b| a.partial_cmp(b).unwrap());
    println!("{:.4}", times[times.len() / 2]);
}
""",
    "bench-simd-kernels": r"""
use std::time::Instant;
#[inline(never)]
pub fn kernel(a: &[u32; 1024], b: &[u32; 1024]) -> u64 {
    let mut sum = 0u64;
    for i in 0..1024 {
        let prod = (a[i] ^ 0x5bd1e995).wrapping_mul(b[i] | 1);
        sum = sum.wrapping_add(prod.rotate_left(13) as u64);
    }
    sum
}
fn main() {
    let a = [0x12345678u32; 1024];
    let b = [0x9abcdef0u32; 1024];
    for _ in 0..5 { std::hint::black_box(kernel(std::hint::black_box(&a), std::hint::black_box(&b))); }
    let mut times = Vec::with_capacity(15);
    for _ in 0..15 {
        let t0 = Instant::now();
        for _ in 0..20 { std::hint::black_box(kernel(std::hint::black_box(&a), std::hint::black_box(&b))); }
        times.push(t0.elapsed().as_nanos() as f64 / 20_000.0);
    }
    times.sort_by(|x, y| x.partial_cmp(y).unwrap());
    println!("{:.4}", times[times.len() / 2]);
}
""",
    "bench-unwind-drop-ladder": r"""
use std::time::Instant;
#[cold]
#[inline(never)]
pub fn cold_abort_path(x: u64) -> u64 {
    x.rotate_left(19) ^ 0xdeadbeefcafebabe
}
#[inline(never)]
pub fn kernel(slice: &[u64]) -> u64 {
    let mut acc = 0u64;
    for (idx, &v) in slice.iter().enumerate() {
        if v == u64::MAX {
            acc ^= cold_abort_path(idx as u64);
        } else {
            acc = acc.wrapping_mul(1099511628211).wrapping_add(v);
        }
    }
    acc
}
fn main() {
    let data = [42u64; 2048];
    for _ in 0..5 { std::hint::black_box(kernel(std::hint::black_box(&data))); }
    let mut times = Vec::with_capacity(15);
    for _ in 0..15 {
        let t0 = Instant::now();
        for _ in 0..15 { std::hint::black_box(kernel(std::hint::black_box(&data))); }
        times.push(t0.elapsed().as_nanos() as f64 / 15_000.0);
    }
    times.sort_by(|a, b| a.partial_cmp(b).unwrap());
    println!("{:.4}", times[times.len() / 2]);
}
""",
    "bench-concurrency-sync": r"""
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Instant;
#[inline(never)]
pub fn kernel(cell: &AtomicU64, n: usize) -> u64 {
    let mut cur = cell.load(Ordering::Relaxed);
    for i in 0..n {
        let next = cur.wrapping_mul(6364136223846793005).wrapping_add(i as u64 | 1);
        match cell.compare_exchange_weak(cur, next, Ordering::AcqRel, Ordering::Relaxed) {
            Ok(_) => cur = next,
            Err(actual) => cur = actual,
        }
    }
    cur
}
fn main() {
    let cell = AtomicU64::new(7);
    for _ in 0..3 { std::hint::black_box(kernel(&cell, 1024)); }
    let mut times = Vec::with_capacity(15);
    for _ in 0..15 {
        let t0 = Instant::now();
        for _ in 0..5 { std::hint::black_box(kernel(&cell, std::hint::black_box(1024))); }
        times.push(t0.elapsed().as_nanos() as f64 / 5_000.0);
    }
    times.sort_by(|a, b| a.partial_cmp(b).unwrap());
    println!("{:.4}", times[times.len() / 2]);
}
""",
    "bench-compression-image": r"""
use std::time::Instant;
#[inline(never)]
pub fn kernel(src: &[u8]) -> u64 {
    let mut ht = [0u16; 256];
    let mut hash_acc = 0u64;
    let mut i = 0usize;
    while i + 4 <= src.len() {
        let w = u32::from_le_bytes([src[i], src[i + 1], src[i + 2], src[i + 3]]);
        let h = ((w.wrapping_mul(0x1e35a7bd)) >> 24) as usize;
        let prev = ht[h] as usize;
        ht[h] = i as u16;
        if prev < i && i - prev < 128 && src[prev] == src[i] {
            hash_acc = hash_acc.wrapping_add((i - prev) as u64);
        } else {
            hash_acc = hash_acc.rotate_left(3) ^ (w as u64);
        }
        i += 1;
    }
    hash_acc
}
fn main() {
    let data = [0x5au8; 4096];
    for _ in 0..5 { std::hint::black_box(kernel(std::hint::black_box(&data))); }
    let mut times = Vec::with_capacity(15);
    for _ in 0..15 {
        let t0 = Instant::now();
        for _ in 0..10 { std::hint::black_box(kernel(std::hint::black_box(&data))); }
        times.push(t0.elapsed().as_nanos() as f64 / 10_000.0);
    }
    times.sort_by(|a, b| a.partial_cmp(b).unwrap());
    println!("{:.4}", times[times.len() / 2]);
}
""",
    "bench-ffi-no-std-crc32c": r"""
use std::time::Instant;
#[inline(never)]
pub extern "C" fn kernel(bytes: &[u8]) -> u32 {
    let mut crc = 0xffff_ffffu32;
    for &b in bytes {
        crc ^= b as u32;
        for _ in 0..8 {
            let mask = (crc & 1).wrapping_neg();
            crc = (crc >> 1) ^ (0x82f63b78 & mask);
        }
    }
    !crc
}
fn main() {
    let data = [0x3cu8; 2048];
    for _ in 0..5 { std::hint::black_box(kernel(std::hint::black_box(&data))); }
    let mut times = Vec::with_capacity(15);
    for _ in 0..15 {
        let t0 = Instant::now();
        for _ in 0..10 { std::hint::black_box(kernel(std::hint::black_box(&data))); }
        times.push(t0.elapsed().as_nanos() as f64 / 10_000.0);
    }
    times.sort_by(|a, b| a.partial_cmp(b).unwrap());
    println!("{:.4}", times[times.len() / 2]);
}
""",
}

LAYOUT_CONFIGS = {
    "L0_Stock_O3": {
        "flags": [],
        "pgo": False,
        "desc": "Default Pettis-Hansen block placement + 16B loop align, no JCC boundary padding",
    },
    "L1_Static_ExtTSP_Split": {
        "flags": [
            "-C", "llvm-args=-enable-ext-tsp-block-placement=true",
            "-C", "llvm-args=-ext-tsp-apply-without-profile=true",
            "-C", "llvm-args=-enable-split-machine-functions=true",
        ],
        "pgo": False,
        "desc": "Static-heuristic Ext-TSP block placement + .text.unlikely machine function splitting",
    },
    "L2_Static_ExtTSP_Loop32_JCC32": {
        "flags": [
            "-C", "llvm-args=-enable-ext-tsp-block-placement=true",
            "-C", "llvm-args=-ext-tsp-apply-without-profile=true",
            "-C", "llvm-args=-enable-split-machine-functions=true",
            "-C", "llvm-args=-align-all-nofallthru-blocks=5",
            "-C", "llvm-args=-x86-align-branch-boundary=32",
            "-C", "llvm-args=-x86-align-branch=fused+jcc+jmp",
        ],
        "pgo": False,
        "desc": "Static-heuristic Ext-TSP + .text.unlikely split + 32B non-fallthrough/loop align + 32B SKX102 JCC/fused NOP align",
    },
    "L3_PGO_ExtTSP_Loop32_JCC32": {
        "flags": [
            "-C", "llvm-args=-enable-ext-tsp-block-placement=true",
            "-C", "llvm-args=-enable-split-machine-functions=true",
            "-C", "llvm-args=-align-all-nofallthru-blocks=5",
            "-C", "llvm-args=-x86-align-branch-boundary=32",
            "-C", "llvm-args=-x86-align-branch=fused+jcc+jmp",
        ],
        "pgo": True,
        "desc": "IR-PGO edge weights + Ext-TSP + .text.unlikely split + 32B loop/JCC NOP alignment",
    },
}


def eval_workload_config(wname: str, src_code: str, cfg_name: str, cfg: dict, base_tmp: Path) -> tuple[str, str, dict]:
    wdir = base_tmp / f"{wname}_{cfg_name}"
    wdir.mkdir(parents=True, exist_ok=True)
    rs_file = wdir / "main.rs"
    rs_file.write_text(src_code, encoding="utf-8")

    env = os.environ.copy()
    env["RUSTC_BOOTSTRAP"] = "1"

    pgo_flags = []
    if cfg["pgo"]:
        prof_dir = wdir / "prof"
        prof_dir.mkdir(exist_ok=True)
        gen_bin = wdir / "gen_bin"
        subprocess.run(
            [RUSTC, "-C", "opt-level=3", "-C", f"profile-generate={prof_dir}", str(rs_file), "-o", str(gen_bin)],
            env=env, check=True,
        )
        subprocess.run([str(gen_bin)], env=env, stdout=subprocess.DEVNULL, check=True)
        profdata = wdir / "merged.profdata"
        profraws = [str(p) for p in prof_dir.glob("*.profraw")]
        subprocess.run([LLVM_PROFDATA, "merge", "-o", str(profdata)] + profraws, check=True)
        pgo_flags = ["-C", f"profile-use={profdata}"]

    # Build and time across all 16 --shuffle-sections seeds
    seed_medians = []
    text_bytes = 0
    for seed in range(1, 17):
        bin_seed = wdir / f"bin_seed_{seed}"
        cmd = [
            RUSTC,
            "-C", "opt-level=3",
            "-C", "codegen-units=1",
            "-Z", "function-sections=yes",
            "-Z", "unstable-options",
            "-C", "link-self-contained=+linker",
            "-C", "linker-flavor=gnu-lld-cc",
            "-C", f"link-arg=-Wl,--shuffle-sections=*={seed}",
            str(rs_file),
            "-o", str(bin_seed),
        ] + cfg["flags"] + pgo_flags
        subprocess.run(cmd, env=env, check=True)
        if seed == 1:
            sz_out = subprocess.check_output([LLVM_SIZE, "--format=sysv", str(bin_seed)], text=True)
            for line in sz_out.splitlines():
                parts = line.split()
                if len(parts) >= 2 and parts[0].startswith(".text"):
                    try:
                        text_bytes += int(parts[1])
                    except ValueError:
                        pass
        out = subprocess.check_output([str(bin_seed)], text=True).strip()
        seed_medians.append(float(out))

    med = statistics.median(seed_medians)
    mn = min(seed_medians)
    mx = max(seed_medians)
    mean = statistics.mean(seed_medians)
    sd = statistics.stdev(seed_medians)
    cv_pct = (sd / mean) * 100.0 if mean > 0 else 0.0
    spread_pct = ((mx - mn) / med) * 100.0 if med > 0 else 0.0

    return wname, cfg_name, {
        "median_across_16_seeds_us": round(med, 4),
        "min_seed_us": round(mn, 4),
        "max_seed_us": round(mx, 4),
        "spread_pct": round(spread_pct, 2),
        "sigma_layout_cv_pct": round(cv_pct, 2),
        "text_bytes": text_bytes,
        "seed_medians_us": [round(x, 4) for x in seed_medians],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=HERE / "layout_opt_results.json")
    args = parser.parse_args()

    tmp_base = Path(os.environ.get("TMPDIR", "/tmp"))
    tmp_base.mkdir(parents=True, exist_ok=True)

    results = {"workloads": {}, "suite_summary": {}}
    with tempfile.TemporaryDirectory(dir=tmp_base) as tmp:
        tmp_dir = Path(tmp)
        futures = []
        with ThreadPoolExecutor(max_workers=8) as ex:
            for wname, src in WCORE_WORKLOADS.items():
                for cfg_name, cfg in LAYOUT_CONFIGS.items():
                    futures.append(ex.submit(eval_workload_config, wname, src, cfg_name, cfg, tmp_dir))
            for fut in as_completed(futures):
                wname, cfg_name, data = fut.result()
                results["workloads"].setdefault(wname, {})[cfg_name] = data

    # Compute suite geometric mean ratios and mean layout CV reduction vs L0_Stock_O3
    for cfg_name in LAYOUT_CONFIGS:
        ratios = []
        cvs = []
        spreads = []
        text_deltas = []
        for wname in WCORE_WORKLOADS:
            base = results["workloads"][wname]["L0_Stock_O3"]
            cur = results["workloads"][wname][cfg_name]
            ratios.append(cur["median_across_16_seeds_us"] / base["median_across_16_seeds_us"])
            cvs.append(cur["sigma_layout_cv_pct"])
            spreads.append(cur["spread_pct"])
            text_deltas.append((cur["text_bytes"] / max(1, base["text_bytes"]) - 1.0) * 100.0)
        geomean_ratio = math.exp(sum(math.log(r) for r in ratios) / len(ratios))
        results["suite_summary"][cfg_name] = {
            "description": LAYOUT_CONFIGS[cfg_name]["desc"],
            "geomean_speed_ratio_vs_L0": round(geomean_ratio, 4),
            "geomean_speed_delta_pct_vs_L0": round((geomean_ratio - 1.0) * 100.0, 2),
            "mean_sigma_layout_cv_pct": round(statistics.mean(cvs), 2),
            "max_sigma_layout_cv_pct": round(max(cvs), 2),
            "mean_16seed_spread_pct": round(statistics.mean(spreads), 2),
            "mean_text_size_delta_pct": round(statistics.mean(text_deltas), 2),
        }

    args.out.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {args.out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
