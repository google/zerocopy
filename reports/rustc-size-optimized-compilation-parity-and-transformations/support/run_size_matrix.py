#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Multi-target size-optimized compilation parity and transformation breakdown harness for rustc 1.99.1 / LLVM 23.1.1."""

import argparse
import csv
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

TIER1_TARGETS = [
    "x86_64-unknown-linux-gnu",
    "aarch64-unknown-linux-gnu",
    "i686-unknown-linux-gnu",
    "x86_64-pc-windows-gnu",
    "x86_64-pc-windows-msvc",
    "i686-pc-windows-msvc",
    "aarch64-pc-windows-msvc",
    "aarch64-apple-darwin",
]

SIZE_CONFIGS = [
    ("O2", ["-C", "opt-level=2", "-C", "codegen-units=16"]),
    ("O3", ["-C", "opt-level=3", "-C", "codegen-units=16"]),
    ("Os", ["-C", "opt-level=s", "-C", "codegen-units=16"]),
    ("Oz", ["-C", "opt-level=z", "-C", "codegen-units=16"]),
    ("Os_ThinLTO", ["-C", "opt-level=s", "-C", "lto=thin", "-C", "codegen-units=16"]),
    ("Oz_ThinLTO", ["-C", "opt-level=z", "-C", "lto=thin", "-C", "codegen-units=16"]),
    ("Oz_FatLTO_CGU1", ["-C", "opt-level=z", "-C", "lto=fat", "-C", "codegen-units=1"]),
    ("Oz_FatLTO_Abort_Strip", ["-C", "opt-level=z", "-C", "lto=fat", "-C", "codegen-units=1", "-C", "panic=abort", "-C", "strip=symbols"]),
    ("Oz_FatLTO_Abort_NoLoc_NoFmt", [
        "-C", "opt-level=z", "-C", "lto=fat", "-C", "codegen-units=1", "-C", "panic=abort", "-C", "strip=symbols",
        "-Z", "location-detail=none", "-Z", "fmt-debug=none"
    ]),
    ("Oz_MachineOutliner_MergeFunc", [
        "-C", "opt-level=z", "-C", "lto=fat", "-C", "codegen-units=1", "-C", "panic=abort", "-C", "strip=symbols",
        "-Z", "location-detail=none", "-Z", "fmt-debug=none",
        "-C", "llvm-args=-enable-machine-outliner=always",
        "-C", "llvm-args=-mergefunc-use-aliases"
    ]),
]

# Representative multi-domain Rust workload exercising slice bounds, formatting/debug,
# generic monomorphizations (MergeFunctions candidates), and repeated prologue/epilogue sequences (MachineOutliner candidates).
WORKLOAD_RS = r"""#![allow(dead_code)]
use std::fmt::Write;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FrameKind {
    Data(u32, u32),
    Control { flags: u8, seq: u16, ack: u16 },
    KeepAlive(u64),
    Disconnect(i32),
}

pub trait Codec<T> {
    fn encode(&self, item: &T, out: &mut [u8]) -> usize;
    fn decode(&self, buf: &[u8]) -> Option<(T, usize)>;
}

pub struct WireCodec<const SALT: u32>;

impl<const SALT: u32> Codec<FrameKind> for WireCodec<SALT> {
    #[inline(never)]
    fn encode(&self, item: &FrameKind, out: &mut [u8]) -> usize {
        if out.len() < 16 {
            return 0;
        }
        match *item {
            FrameKind::Data(a, b) => {
                out[0] = 1;
                let x = (a ^ SALT).to_le_bytes();
                let y = (b.wrapping_add(SALT)).to_le_bytes();
                out[1..5].copy_from_slice(&x);
                out[5..9].copy_from_slice(&y);
                9
            }
            FrameKind::Control { flags, seq, ack } => {
                out[0] = 2;
                out[1] = flags;
                out[2..4].copy_from_slice(&(seq ^ (SALT as u16)).to_le_bytes());
                out[4..6].copy_from_slice(&(ack ^ (SALT as u16)).to_le_bytes());
                6
            }
            FrameKind::KeepAlive(ts) => {
                out[0] = 3;
                out[1..9].copy_from_slice(&(ts ^ (SALT as u64)).to_le_bytes());
                9
            }
            FrameKind::Disconnect(code) => {
                out[0] = 4;
                out[1..5].copy_from_slice(&(code ^ (SALT as i32)).to_le_bytes());
                5
            }
        }
    }

    #[inline(never)]
    fn decode(&self, buf: &[u8]) -> Option<(FrameKind, usize)> {
        let tag = *buf.first()?;
        match tag {
            1 if buf.len() >= 9 => {
                let a = u32::from_le_bytes([buf[1], buf[2], buf[3], buf[4]]) ^ SALT;
                let b = u32::from_le_bytes([buf[5], buf[6], buf[7], buf[8]]).wrapping_sub(SALT);
                Some((FrameKind::Data(a, b), 9))
            }
            2 if buf.len() >= 6 => {
                let flags = buf[1];
                let seq = u16::from_le_bytes([buf[2], buf[3]]) ^ (SALT as u16);
                let ack = u16::from_le_bytes([buf[4], buf[5]]) ^ (SALT as u16);
                Some((FrameKind::Control { flags, seq, ack }, 6))
            }
            3 if buf.len() >= 9 => {
                let ts = u64::from_le_bytes([
                    buf[1], buf[2], buf[3], buf[4], buf[5], buf[6], buf[7], buf[8],
                ]) ^ (SALT as u64);
                Some((FrameKind::KeepAlive(ts), 9))
            }
            4 if buf.len() >= 5 => {
                let code = i32::from_le_bytes([buf[1], buf[2], buf[3], buf[4]]) ^ (SALT as i32);
                Some((FrameKind::Disconnect(code), 5))
            }
            _ => None,
        }
    }
}

// Identical layout monomorphizations to test MergeFunctions:
pub struct TagA;
pub struct TagB;
pub struct TagC;
pub struct TagD;

#[inline(never)]
pub fn crc_typed<T>(seed: u32, bytes: &[u8]) -> u32 {
    let mut crc = !seed;
    for &b in bytes {
        crc ^= b as u32;
        for _ in 0..8 {
            let mask = (crc & 1).wrapping_neg();
            crc = (crc >> 1) ^ (0xEDB88320 & mask);
        }
    }
    !crc ^ (core::mem::size_of::<T>() as u32)
}

// Repeated instruction sequences to exercise MachineOutliner:
#[inline(never)]
pub fn outline_candidate_1(s: &mut [u64; 8], k: u64) -> u64 {
    s[0] = s[0].wrapping_add(k).rotate_left(13) ^ 0x9e3779b97f4a7c15;
    s[1] = s[1].wrapping_add(s[0]).rotate_left(17) ^ 0xbf58476d1ce4e5b9;
    s[2] = s[2].wrapping_add(s[1]).rotate_left(29) ^ 0x94d049bb133111eb;
    s[3] = s[3].wrapping_add(s[2]).rotate_left(31) ^ 0x2545f4914f6cdd1d;
    s[4] = s[4].wrapping_add(s[3]).rotate_left(37) ^ 0x517cc1b727220a95;
    s[5] = s[5].wrapping_add(s[4]).rotate_left(41) ^ 0x85ebca6b27d4eb2f;
    s[6] = s[6].wrapping_add(s[5]).rotate_left(43) ^ 0xc2b2ae35165667b1;
    s[7] = s[7].wrapping_add(s[6]).rotate_left(53) ^ 0x27d4eb2f165667c5;
    s[7]
}

#[inline(never)]
pub fn outline_candidate_2(s: &mut [u64; 8], k: u64) -> u64 {
    s[0] = s[0].wrapping_add(k).rotate_left(13) ^ 0x9e3779b97f4a7c15;
    s[1] = s[1].wrapping_add(s[0]).rotate_left(17) ^ 0xbf58476d1ce4e5b9;
    s[2] = s[2].wrapping_add(s[1]).rotate_left(29) ^ 0x94d049bb133111eb;
    s[3] = s[3].wrapping_add(s[2]).rotate_left(31) ^ 0x2545f4914f6cdd1d;
    s[4] = s[4].wrapping_add(s[3]).rotate_left(37) ^ 0x517cc1b727220a95;
    s[5] = s[5].wrapping_add(s[4]).rotate_left(41) ^ 0x85ebca6b27d4eb2f;
    s[6] = s[6].wrapping_add(s[5]).rotate_left(43) ^ 0xc2b2ae35165667b1;
    s[7] = s[7].wrapping_add(s[6]).rotate_left(53) ^ 0x1111111122222222;
    s[7]
}

#[inline(never)]
pub fn outline_candidate_3(s: &mut [u64; 8], k: u64) -> u64 {
    s[0] = s[0].wrapping_add(k).rotate_left(13) ^ 0x9e3779b97f4a7c15;
    s[1] = s[1].wrapping_add(s[0]).rotate_left(17) ^ 0xbf58476d1ce4e5b9;
    s[2] = s[2].wrapping_add(s[1]).rotate_left(29) ^ 0x94d049bb133111eb;
    s[3] = s[3].wrapping_add(s[2]).rotate_left(31) ^ 0x2545f4914f6cdd1d;
    s[4] = s[4].wrapping_add(s[3]).rotate_left(37) ^ 0x517cc1b727220a95;
    s[5] = s[5].wrapping_add(s[4]).rotate_left(41) ^ 0x85ebca6b27d4eb2f;
    s[6] = s[6].wrapping_add(s[5]).rotate_left(43) ^ 0xc2b2ae35165667b1;
    s[7] = s[7].wrapping_add(s[6]).rotate_left(53) ^ 0x3333333344444444;
    s[7]
}

#[no_mangle]
pub extern "C" fn run_size_workload(input: *const u8, len: usize) -> u64 {
    let slice = unsafe { core::slice::from_raw_parts(input, len) };
    let c1 = WireCodec::<0x12345678>;
    let c2 = WireCodec::<0x87654321>;
    let mut buf = [0u8; 32];
    let mut acc = 0u64;
    if let Some((frame, n)) = c1.decode(slice) {
        let m = c2.encode(&frame, &mut buf);
        acc ^= (n + m) as u64;
        let mut s = String::with_capacity(64);
        let _ = write!(&mut s, "{:?}", frame);
        acc ^= s.len() as u64;
    }
    acc = acc.wrapping_add(crc_typed::<u32>(0, slice) as u64);
    acc = acc.wrapping_add(crc_typed::<i32>(0, slice) as u64);
    acc = acc.wrapping_add(crc_typed::<f32>(0, slice) as u64);
    acc = acc.wrapping_add(crc_typed::<[u8; 4]>(0, slice) as u64);
    let mut state = [acc, 1, 2, 3, 4, 5, 6, 7];
    acc ^= outline_candidate_1(&mut state, len as u64);
    acc ^= outline_candidate_2(&mut state, len as u64 ^ 1);
    acc ^= outline_candidate_3(&mut state, len as u64 ^ 2);
    acc
}
"""


def parse_llvm_size_sysv(llvm_size_bin: str, obj_files: list[Path]) -> dict[str, int]:
    totals = {
        "text_bytes": 0,
        "rodata_bytes": 0,
        "eh_frame_or_pdata_bytes": 0,
        "data_rel_ro_bytes": 0,
        "total_obj_bytes": sum(f.stat().st_size for f in obj_files if f.is_file()),
    }
    if not obj_files:
        return totals
    cmd = [llvm_size_bin, "--format=sysv"] + [str(f) for f in obj_files]
    proc = subprocess.run(cmd, capture_output=True, text=True, check=False)
    for line in proc.stdout.splitlines():
        parts = line.split()
        if len(parts) < 2:
            continue
        sec = parts[0]
        try:
            sz = int(parts[1])
        except ValueError:
            continue
        if sec.startswith((".text", "__text")):
            totals["text_bytes"] += sz
        elif sec.startswith((".rodata", ".rdata", "__const", "__cstring")):
            totals["rodata_bytes"] += sz
        elif sec.startswith((".eh_frame", ".ARM.exidx", ".ARM.extab", ".pdata", ".xdata", "__eh_frame", "__unwind_info")):
            totals["eh_frame_or_pdata_bytes"] += sz
        elif sec.startswith((".data.rel.ro", "__data_const")):
            totals["data_rel_ro_bytes"] += sz
    return totals


def count_outlined_and_merged(llvm_nm_bin: str, obj_files: list[Path]) -> dict[str, int]:
    outlined = 0
    crc_defs = 0
    if not obj_files:
        return {"outlined_funcs": 0, "crc_typed_defs": 0}
    proc = subprocess.run([llvm_nm_bin] + [str(f) for f in obj_files], capture_output=True, text=True, check=False)
    for line in proc.stdout.splitlines():
        if "OUTLINED_FUNCTION_" in line:
            outlined += 1
        if "crc_typed" in line and (" T " in line or " t " in line):
            crc_defs += 1
    return {"outlined_funcs": outlined, "crc_typed_defs": crc_defs}


def run_one(toolchain: str, llvm_size_bin: str, llvm_nm_bin: str, target: str, cfg_name: str, flags: list[str], base_tmp: Path) -> dict:
    work_dir = base_tmp / f"{target}_{cfg_name}"
    work_dir.mkdir(parents=True, exist_ok=True)
    src = work_dir / "lib.rs"
    src.write_text(WORKLOAD_RS, encoding="utf-8")

    # Note: In LLVM 23.1.1, SupportsDefaultOutlining is true only on AArch64 (and ARM).
    # On x86_64-unknown-linux-gnu, forcing -enable-machine-outliner=always succeeds;
    # on x86_64-pc-windows-*, it splits Win64 SEH .seh_startepilogue/.seh_endepilogue;
    # on i686-pc-windows-msvc, it splits CodeView .cv_fpo_endprologue;
    # on i686-unknown-linux-gnu (FatLTO), it separates 32-bit PIC GOTPC addl instructions from their .L0$pb base labels ("expected relocatable expression").
    effective_flags = list(flags)
    if cfg_name == "Oz_MachineOutliner_MergeFunc" and target in (
        "x86_64-pc-windows-msvc", "x86_64-pc-windows-gnu",
        "i686-pc-windows-msvc", "i686-unknown-linux-gnu"
    ):
        cleaned = []
        for idx, tok in enumerate(flags):
            if tok == "-C" and idx + 1 < len(flags) and flags[idx + 1] == "llvm-args=-enable-machine-outliner=always":
                continue
            if tok == "llvm-args=-enable-machine-outliner=always":
                continue
            cleaned.append(tok)
        effective_flags = cleaned

    cmd = [
        "rustc", f"+{toolchain}",
        "--edition=2021",
        "--crate-type=staticlib",
        "--emit=obj,link",
        "-C", "save-temps",
        "--target", target,
        "-Z", "unstable-options",
        str(src),
        "--out-dir", str(work_dir),
    ] + effective_flags
    env = os.environ.copy()
    env["RUSTC_BOOTSTRAP"] = "1"
    proc = subprocess.run(cmd, capture_output=True, text=True, env=env)
    if proc.returncode != 0:
        raise RuntimeError(f"Failed {target} {cfg_name}: {proc.stderr}")

    # Filter to crate CGU object files (*.rcgu.o or lib.o, excluding allocator_shim.rcgu.o)
    objs = sorted([
        p for p in work_dir.glob("*.o")
        if "allocator_shim" not in p.name and not p.name.endswith(".Generated.rcgu.o")
    ])
    staticlibs = list(work_dir.glob("*.a")) + list(work_dir.glob("*.lib"))
    staticlib_bytes = staticlibs[0].stat().st_size if staticlibs else 0

    sec_crate = parse_llvm_size_sysv(llvm_size_bin, objs)
    sym_crate = count_outlined_and_merged(llvm_nm_bin, objs)

    # Also measure section totals across the linked staticlib (includes std/core objects surviving LTO/internalization)
    sec_archive = parse_llvm_size_sysv(llvm_size_bin, staticlibs) if staticlibs else sec_crate

    shutil.rmtree(work_dir, ignore_errors=True)
    return {
        "target": target,
        "config": cfg_name,
        "crate_text_bytes": sec_crate["text_bytes"],
        "crate_rodata_bytes": sec_crate["rodata_bytes"],
        "crate_eh_frame_or_pdata_bytes": sec_crate["eh_frame_or_pdata_bytes"],
        "crate_data_rel_ro_bytes": sec_crate["data_rel_ro_bytes"],
        "crate_obj_bytes": sec_crate["total_obj_bytes"],
        "archive_text_bytes": sec_archive["text_bytes"],
        "archive_rodata_bytes": sec_archive["rodata_bytes"],
        "archive_eh_frame_or_pdata_bytes": sec_archive["eh_frame_or_pdata_bytes"],
        "staticlib_total_bytes": staticlib_bytes,
        "outlined_funcs": sym_crate["outlined_funcs"],
        "crc_typed_defs": sym_crate["crc_typed_defs"],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", default="1.99.1-x86_64-unknown-linux-gnu")
    parser.add_argument("--out-dir", type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()

    sysroot = Path(subprocess.check_output(["rustc", f"+{args.toolchain}", "--print", "sysroot"], text=True).strip())
    bin_dir = sysroot / "lib/rustlib/x86_64-unknown-linux-gnu/bin"
    llvm_size_bin = str(bin_dir / "llvm-size")
    llvm_nm_bin = str(bin_dir / "llvm-nm")

    rows = []
    with tempfile.TemporaryDirectory() as tmp:
        tmp_path = Path(tmp)
        futures = {}
        with ThreadPoolExecutor(max_workers=16) as ex:
            for t in TIER1_TARGETS:
                for cfg_name, flags in SIZE_CONFIGS:
                    fut = ex.submit(run_one, args.toolchain, llvm_size_bin, llvm_nm_bin, t, cfg_name, flags, tmp_path)
                    futures[fut] = (t, cfg_name)
            for fut in as_completed(futures):
                rows.append(fut.result())

    cfg_order = {name: i for i, (name, _) in enumerate(SIZE_CONFIGS)}
    tgt_order = {t: i for i, t in enumerate(TIER1_TARGETS)}
    rows.sort(key=lambda r: (tgt_order[r["target"]], cfg_order[r["config"]]))

    args.out_dir.mkdir(parents=True, exist_ok=True)
    csv_path = args.out_dir / "size_parity_baselines_8targets.csv"
    fieldnames = [
        "target", "config",
        "crate_text_bytes", "crate_rodata_bytes", "crate_eh_frame_or_pdata_bytes",
        "crate_data_rel_ro_bytes", "crate_obj_bytes",
        "archive_text_bytes", "archive_rodata_bytes", "archive_eh_frame_or_pdata_bytes",
        "staticlib_total_bytes", "outlined_funcs", "crc_typed_defs"
    ]
    with open(csv_path, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        w.writerows(rows)

    # Compute per-target transformation breakdown deltas
    by_target = {}
    for r in rows:
        by_target.setdefault(r["target"], {})[r["config"]] = r

    breakdown = {}
    for t, cmap in by_target.items():
        o3 = cmap["O3"]
        o2 = cmap["O2"]
        os_cfg = cmap["Os"]
        oz_cfg = cmap["Oz"]
        oz_thin = cmap["Oz_ThinLTO"]
        oz_fat = cmap["Oz_FatLTO_CGU1"]
        oz_abort = cmap["Oz_FatLTO_Abort_Strip"]
        oz_noloc = cmap["Oz_FatLTO_Abort_NoLoc_NoFmt"]
        oz_out = cmap["Oz_MachineOutliner_MergeFunc"]

        breakdown[t] = {
            "baseline_O3_crate_text_bytes": o3["crate_text_bytes"],
            "baseline_O2_crate_text_bytes": o2["crate_text_bytes"],
            "Os_vs_O3_crate_text_delta_bytes": os_cfg["crate_text_bytes"] - o3["crate_text_bytes"],
            "Oz_vs_O3_crate_text_delta_bytes": oz_cfg["crate_text_bytes"] - o3["crate_text_bytes"],
            "Oz_vs_Os_crate_text_delta_bytes": oz_cfg["crate_text_bytes"] - os_cfg["crate_text_bytes"],
            "ThinLTO_at_Oz_crate_text_delta_bytes": oz_thin["crate_text_bytes"] - oz_cfg["crate_text_bytes"],
            "FatLTO_CGU1_vs_ThinLTO_crate_text_delta_bytes": oz_fat["crate_text_bytes"] - oz_thin["crate_text_bytes"],
            "FatLTO_CGU1_archive_text_reduction_pct": round(
                (1.0 - oz_fat["archive_text_bytes"] / max(1, oz_cfg["archive_text_bytes"])) * 100.0, 2
            ),
            "panic_abort_eh_frame_saved_bytes_crate": oz_abort["crate_eh_frame_or_pdata_bytes"] - oz_fat["crate_eh_frame_or_pdata_bytes"],
            "panic_abort_eh_frame_saved_bytes_archive": oz_abort["archive_eh_frame_or_pdata_bytes"] - oz_fat["archive_eh_frame_or_pdata_bytes"],
            "location_and_fmt_debug_none_rodata_saved_bytes": oz_noloc["crate_rodata_bytes"] - oz_abort["crate_rodata_bytes"],
            "location_and_fmt_debug_none_text_saved_bytes": oz_noloc["crate_text_bytes"] - oz_abort["crate_text_bytes"],
            "machine_outliner_explicit_text_delta_bytes": oz_out["crate_text_bytes"] - oz_noloc["crate_text_bytes"],
            "outlined_function_count_default_Oz": oz_noloc["outlined_funcs"],
            "outlined_function_count_forced": oz_out["outlined_funcs"],
            "merge_functions_crc_typed_surviving_defs": oz_out["crc_typed_defs"],
        }

    json_path = args.out_dir / "size_transformation_breakdown.json"
    json_path.write_text(json.dumps({
        "toolchain": args.toolchain,
        "rust_commit": "58cf8f9c35b355199727627d07ae34a4e2846d67",
        "llvm_commit": "1b9c0d5ff9bbe7634aead059efe6b11a7eeba145",
        "per_target_breakdown": breakdown,
    }, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {csv_path} ({len(rows)} rows) and {json_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
