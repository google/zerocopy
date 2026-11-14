#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Pre-proof reachability pruning (--gc-sections) and address-safe ICF (--icf=safe) savings analyzer across V3 workloads and 8 Tier 1 targets."""

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
TC_ROOT = Path(os.path.expanduser("~/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu"))
RUSTC = str(TC_ROOT / "bin" / "rustc")
LLVM_BIN = TC_ROOT / "lib" / "rustlib" / "x86_64-unknown-linux-gnu" / "bin"
LLVM_NM = str(LLVM_BIN / "llvm-nm")
LLVM_SIZE = str(LLVM_BIN / "llvm-size")
LLVM_READOBJ = str(LLVM_BIN / "llvm-readobj")

TIER1_TARGETS = [
    "x86_64-unknown-linux-gnu",
    "i686-unknown-linux-gnu",
    "aarch64-unknown-linux-gnu",
    "aarch64-apple-darwin",
    "x86_64-pc-windows-msvc",
    "x86_64-pc-windows-gnu",
    "i686-pc-windows-msvc",
    "aarch64-pc-windows-msvc",
]

V3_WORKLOADS = {
    "hello_world": ("bin", 'fn main() { println!("Hello, world!"); }\n'),
    "cli_tool": (
        "bin",
        r"""
use std::env;
use std::fs;
use std::collections::HashMap;

#[inline(never)]
pub fn fold_candidate_u32(x: u32, y: u32) -> u32 { x.wrapping_mul(1664525).wrapping_add(y ^ 0x10139042) }
#[inline(never)]
pub fn fold_candidate_i32(x: i32, y: i32) -> i32 { (x as u32).wrapping_mul(1664525).wrapping_add((y as u32) ^ 0x10139042) as i32 }
#[inline(never)]
pub fn fold_candidate_arr(x: [u8; 4], y: [u8; 4]) -> u32 {
    u32::from_le_bytes(x).wrapping_mul(1664525).wrapping_add(u32::from_le_bytes(y) ^ 0x10139042)
}

fn main() {
    let mut counts: HashMap<String, usize> = HashMap::new();
    for arg in env::args().skip(1) {
        if let Ok(data) = fs::read_to_string(&arg) {
            for word in data.split_whitespace() {
                *counts.entry(word.to_owned()).or_insert(0) += 1;
            }
        }
    }
    let s = fold_candidate_u32(1, 2)
        .wrapping_add(fold_candidate_i32(1, 2) as u32)
        .wrapping_add(fold_candidate_arr([1, 0, 0, 0], [2, 0, 0, 0]));
    println!("unique={} s={}", counts.len(), s);
}
""",
    ),
    "async_server": (
        "bin",
        r"""
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};
use std::net::TcpListener;
use std::sync::Arc;

async fn handle_conn(id: u64) -> u64 {
    id.wrapping_mul(6364136223846793005).wrapping_add(1)
}

fn dummy_waker() -> Waker {
    fn no_op(_: *const ()) {}
    fn clone(p: *const ()) -> RawWaker { RawWaker::new(p, &VTABLE) }
    static VTABLE: RawWakerVTable = RawWakerVTable::new(clone, no_op, no_op, no_op);
    unsafe { Waker::from_raw(RawWaker::new(core::ptr::null(), &VTABLE)) }
}

fn main() {
    let waker = dummy_waker();
    let mut cx = Context::from_waker(&waker);
    let mut fut = Box::pin(handle_conn(42));
    if let Poll::Ready(v) = fut.as_mut().poll(&mut cx) {
        let _ = TcpListener::bind("127.0.0.1:0").map(|l| Arc::new(l));
        println!("ready={v}");
    }
}
""",
    ),
    "cdylib": (
        "cdylib",
        r"""
#[unsafe(no_mangle)]
pub extern "C" fn rust_cdylib_entry(x: u64, y: u64) -> u64 {
    let s = format!("{x}:{y}");
    s.len() as u64
}
""",
    ),
    "staticlib": (
        "staticlib",
        r"""
#[unsafe(no_mangle)]
pub extern "C" fn rust_staticlib_entry(x: u64, y: u64) -> u64 {
    let s = format!("{x}:{y}");
    s.len() as u64
}
""",
    ),
}


def count_text_funcs_and_bytes(artifact: Path) -> dict:
    sz_proc = subprocess.run([LLVM_SIZE, "--format=sysv", str(artifact)], capture_output=True, text=True, check=False)
    text_bytes = 0
    for line in sz_proc.stdout.splitlines():
        parts = line.split()
        if len(parts) >= 2 and parts[0].startswith((".text", "__text")):
            try:
                text_bytes += int(parts[1])
            except ValueError:
                pass
    nm_proc = subprocess.run([LLVM_NM, "--defined-only", str(artifact)], capture_output=True, text=True, check=False)
    func_syms = 0
    unique_code_addrs = set()
    for line in nm_proc.stdout.splitlines():
        parts = line.split()
        if len(parts) >= 3 and parts[1] in ("T", "t", "W", "w"):
            func_syms += 1
            unique_code_addrs.add(parts[0])
    # Estimate HybridTrace proof obligations (averaging 24 MIR/MiniMach step rules per MonoItem function)
    est_proof_steps = len(unique_code_addrs) * 24
    return {
        "text_bytes": text_bytes,
        "defined_func_symbols": func_syms,
        "unique_code_bodies": len(unique_code_addrs),
        "estimated_hybrid_trace_steps": est_proof_steps,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=HERE / "reachability_icf_savings.json")
    args = parser.parse_args()

    tmp_base = Path(os.environ.get("TMPDIR", "/tmp"))
    tmp_base.mkdir(parents=True, exist_ok=True)

    results = {
        "x86_64_workloads_pruning_and_icf": {},
        "cross_target_8target_archive_pruning": {},
        "llvm_addrsig_and_fn_ptr_soundness": {},
    }

    env = os.environ.copy()
    env["RUSTC_BOOTSTRAP"] = "1"

    with tempfile.TemporaryDirectory(dir=tmp_base) as tmp:
        work_dir = Path(tmp)

        # 1. Evaluate all 5 V3 workloads on x86_64-unknown-linux-gnu across:
        #    (a) unpruned (--no-gc-sections -C llvm-args=-enable-merge-functions=false)
        #    (b) reachability-pruned (--gc-sections -C llvm-args=-enable-merge-functions=false)
        #    (c) reachability + safe ICF (--gc-sections --icf=safe + MergeFunctions)
        #    (d) whole-program FatLTO reachability + safe ICF (-C lto=fat -C codegen-units=1 --gc-sections --icf=safe)
        for wname, (ctype, src) in V3_WORKLOADS.items():
            rs_path = work_dir / f"{wname}.rs"
            rs_path.write_text(src, encoding="utf-8")
            results["x86_64_workloads_pruning_and_icf"][wname] = {}

            if ctype == "staticlib":
                # Compare unpruned staticlib vs FatLTO CGU=1 pruned staticlib
                out_unpruned = work_dir / f"{wname}_unpruned.a"
                subprocess.run(
                    [RUSTC, "--crate-type=staticlib", "-C", "opt-level=3", str(rs_path), "-o", str(out_unpruned)],
                    env=env, check=True,
                )
                out_pruned = work_dir / f"{wname}_fatlto.a"
                subprocess.run(
                    [RUSTC, "--crate-type=staticlib", "-C", "opt-level=3", "-C", "lto=fat", "-C", "codegen-units=1", str(rs_path), "-o", str(out_pruned)],
                    env=env, check=True,
                )
                u_m = count_text_funcs_and_bytes(out_unpruned)
                p_m = count_text_funcs_and_bytes(out_pruned)
                results["x86_64_workloads_pruning_and_icf"][wname] = {
                    "unpruned_archive": u_m,
                    "pre_proof_reachability_and_icf": p_m,
                    "text_bytes_removed_pct": round((1.0 - p_m["text_bytes"] / max(1, u_m["text_bytes"])) * 100.0, 2),
                    "proof_volume_reduction_factor_x": round(u_m["unique_code_bodies"] / max(1, p_m["unique_code_bodies"]), 2),
                }
                continue

            modes = [
                ("unpruned_no_gc_no_icf", [
                    "-C", "opt-level=3",
                    "-Z", "unstable-options", "-C", "link-self-contained=+linker", "-C", "linker-flavor=gnu-lld-cc",
                    "-C", "link-arg=-Wl,--no-gc-sections", "-C", "link-arg=-Wl,--icf=none",
                    "-C", "llvm-args=-enable-merge-functions=false",
                ]),
                ("pruned_gc_sections_only", [
                    "-C", "opt-level=3",
                    "-Z", "unstable-options", "-C", "link-self-contained=+linker", "-C", "linker-flavor=gnu-lld-cc",
                    "-C", "link-arg=-Wl,--gc-sections", "-C", "link-arg=-Wl,--icf=none",
                    "-C", "llvm-args=-enable-merge-functions=false",
                ]),
                ("pruned_gc_plus_icf_safe", [
                    "-C", "opt-level=3",
                    "-Z", "unstable-options", "-C", "link-self-contained=+linker", "-C", "linker-flavor=gnu-lld-cc",
                    "-C", "link-arg=-Wl,--gc-sections", "-C", "link-arg=-Wl,--icf=safe",
                ]),
                ("pre_proof_wpo_fatlto_gc_icf_safe", [
                    "-C", "opt-level=3", "-C", "lto=fat", "-C", "codegen-units=1",
                    "-Z", "unstable-options", "-C", "link-self-contained=+linker", "-C", "linker-flavor=gnu-lld-cc",
                    "-C", "link-arg=-Wl,--gc-sections", "-C", "link-arg=-Wl,--icf=safe",
                ]),
            ]
            w_rec = {}
            for mname, mflags in modes:
                out_bin = work_dir / f"{wname}_{mname}"
                subprocess.run(
                    [RUSTC, "--edition=2024", f"--crate-type={ctype}", str(rs_path), "-o", str(out_bin)] + mflags,
                    env=env, check=True,
                )
                w_rec[mname] = count_text_funcs_and_bytes(out_bin)

            u_b = w_rec["unpruned_no_gc_no_icf"]
            gc_b = w_rec["pruned_gc_sections_only"]
            icf_b = w_rec["pruned_gc_plus_icf_safe"]
            wpo_b = w_rec["pre_proof_wpo_fatlto_gc_icf_safe"]
            w_rec["summary_metrics"] = {
                "gc_sections_dead_code_removed_pct": round((1.0 - gc_b["text_bytes"] / max(1, u_b["text_bytes"])) * 100.0, 2),
                "gc_sections_proof_reduction_factor_x": round(u_b["unique_code_bodies"] / max(1, gc_b["unique_code_bodies"]), 2),
                "icf_safe_additional_bodies_folded": gc_b["unique_code_bodies"] - icf_b["unique_code_bodies"],
                "full_pre_proof_pruning_and_icf_reduction_factor_x": round(u_b["unique_code_bodies"] / max(1, wpo_b["unique_code_bodies"]), 2),
            }
            results["x86_64_workloads_pruning_and_icf"][wname] = w_rec

        # 2. Cross-target 8-target pre-proof reachability pruning on staticlib
        _, staticlib_src = V3_WORKLOADS["staticlib"]
        sl_rs = work_dir / "sl_8t.rs"
        sl_rs.write_text(staticlib_src, encoding="utf-8")
        for target in TIER1_TARGETS:
            out_u = work_dir / f"sl_{target}_unpruned.a"
            out_p = work_dir / f"sl_{target}_pruned.a"
            subprocess.run(
                [RUSTC, "--target", target, "--crate-type=staticlib", "-C", "opt-level=3", str(sl_rs), "-o", str(out_u)],
                env=env, check=True,
            )
            subprocess.run(
                [RUSTC, "--target", target, "--crate-type=staticlib", "-C", "opt-level=3", "-C", "lto=fat", "-C", "codegen-units=1", str(sl_rs), "-o", str(out_p)],
                env=env, check=True,
            )
            um = count_text_funcs_and_bytes(out_u)
            pm = count_text_funcs_and_bytes(out_p)
            results["cross_target_8target_archive_pruning"][target] = {
                "unpruned_text_bytes": um["text_bytes"],
                "pruned_text_bytes": pm["text_bytes"],
                "dead_text_removed_pct": round((1.0 - pm["text_bytes"] / max(1, um["text_bytes"])) * 100.0, 2),
                "unpruned_unique_bodies": um["unique_code_bodies"],
                "pruned_unique_bodies": pm["unique_code_bodies"],
                "proof_volume_reduction_factor_x": round(um["unique_code_bodies"] / max(1, pm["unique_code_bodies"]), 2),
            }

        # 3. Inspect .llvm_addrsig (SHT_LLVM_ADDRSIG) and test fn-pointer identity under --icf=none, --icf=safe, --icf=all
        addrsig_rs = work_dir / "addrsig_probe.rs"
        addrsig_rs.write_text(
            r"""
#[inline(never)]
pub fn addr_taken_a(x: u64) -> u64 { x.wrapping_add(0x12345678) }
#[inline(never)]
pub fn addr_taken_b(x: u64) -> u64 { x.wrapping_add(0x12345678) }
#[inline(never)]
pub fn call_only_c(x: u64) -> u64 { x.wrapping_add(0x87654321) }
#[inline(never)]
pub fn call_only_d(x: u64) -> u64 { x.wrapping_add(0x87654321) }

fn main() {
    let pa = std::hint::black_box(addr_taken_a as fn(u64) -> u64) as usize;
    let pb = std::hint::black_box(addr_taken_b as fn(u64) -> u64) as usize;
    let v = addr_taken_a(1) + addr_taken_b(2) + call_only_c(3) + call_only_d(4);
    println!("addr_taken_eq={} sum={}", pa == pb, v);
}
""",
            encoding="utf-8",
        )
        obj_probe = work_dir / "addrsig_probe.o"
        subprocess.run(
            [RUSTC, "-C", "opt-level=2", "-C", "llvm-args=-enable-merge-functions=false", "--emit=obj", str(addrsig_rs), "-o", str(obj_probe)],
            env=env, check=True,
        )
        ro_out = subprocess.check_output([LLVM_READOBJ, "--sections", "--addrsig", str(obj_probe)], text=True)
        addrsig_syms = re.findall(r"Sym:\s+([^\s(]+)", ro_out)

        icf_modes = {}
        for mode in ("none", "safe", "all"):
            bin_icf = work_dir / f"addrsig_{mode}"
            subprocess.run(
                [
                    RUSTC, "-C", "opt-level=2",
                    "-C", "llvm-args=-enable-merge-functions=false",
                    "-Z", "unstable-options", "-C", "link-self-contained=+linker", "-C", "linker-flavor=gnu-lld-cc",
                    f"-C", f"link-arg=-Wl,--icf={mode}",
                    str(addrsig_rs), "-o", str(bin_icf),
                ],
                env=env, check=True,
            )
            stdout = subprocess.check_output([str(bin_icf)], text=True).strip()
            nm_out = subprocess.check_output([LLVM_NM, str(bin_icf)], text=True)
            addrs = {}
            for line in nm_out.splitlines():
                for fn_key in ("addr_taken_a", "addr_taken_b", "call_only_c", "call_only_d"):
                    if fn_key in line:
                        addrs[fn_key] = line.split()[0]
            icf_modes[mode] = {
                "stdout": stdout,
                "symbol_addresses": addrs,
                "addr_taken_distinct": addrs.get("addr_taken_a") != addrs.get("addr_taken_b"),
                "call_only_folded": addrs.get("call_only_c") == addrs.get("call_only_d"),
            }

        results["llvm_addrsig_and_fn_ptr_soundness"] = {
            "emitted_SHT_LLVM_ADDRSIG_symbols": addrsig_syms,
            "lld_icf_modes": icf_modes,
        }

    args.out.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {args.out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
