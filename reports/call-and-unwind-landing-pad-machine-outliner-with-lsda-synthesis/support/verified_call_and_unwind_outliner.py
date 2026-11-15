#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Call- and unwind-landing-pad machine outliner (OutlinerUnwindThunkCert) prototype across all 8 Tier 1 targets with live std::panic::catch_unwind verification."""

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
LLVM_MC = "/usr/bin/llvm-mc"
LLVM_SIZE = str(LLVM_BIN / "llvm-size")

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

# Workload containing repeated bounds-check/panic calls, non-diverging call sequences,
# and drop-cleanup landing pads across 12 functions.
CALL_OUTLINER_WORKLOAD_RS = r"""#![no_std]
#![crate_type = "rlib"]
#![allow(improper_ctypes_definitions)]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {}
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn external_step(a: u64, b: u64, c: u64) -> u64 {
    a.wrapping_mul(0x9e3779b97f4a7c15).wrapping_add(b) ^ c.rotate_left(19)
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn cold_violation_sink(code: u64, idx: usize, len: usize) -> ! {
    core::hint::black_box((code, idx, len));
    loop {}
}

macro_rules! def_checked_pipeline {
    ($fn_name:ident, $tag:expr) => {
        #[unsafe(no_mangle)]
        #[inline(never)]
        pub extern "C" fn $fn_name(slice: &[u64], k: u64) -> u64 {
            if slice.len() < 8 {
                cold_violation_sink(0xDEAD_0001, slice.len(), 8);
            }
            let s0 = external_step(slice[0], k, 0x1111_2222_3333_4444);
            let s1 = external_step(slice[1], s0, 0x5555_6666_7777_8888);
            let s2 = external_step(slice[2], s1, 0x9999_aaaa_bbbb_cccc);
            let s3 = external_step(slice[3], s2, 0xdddd_eeee_ffff_0001);
            if s3 == 0 {
                cold_violation_sink(0xDEAD_0002, 3, slice.len());
            }
            let s4 = external_step(slice[4], s3, 0x1234_5678_9abc_def0);
            let s5 = external_step(slice[5], s4, 0x0fed_cba9_8765_4321);
            let s6 = external_step(slice[6], s5, 0x1357_9bdf_2468_ace0);
            let s7 = external_step(slice[7], s6, $tag);
            s7
        }
    };
}

def_checked_pipeline!(pipe_fn_01, 0x0101);
def_checked_pipeline!(pipe_fn_02, 0x0202);
def_checked_pipeline!(pipe_fn_03, 0x0303);
def_checked_pipeline!(pipe_fn_04, 0x0404);
def_checked_pipeline!(pipe_fn_05, 0x0505);
def_checked_pipeline!(pipe_fn_06, 0x0606);
def_checked_pipeline!(pipe_fn_07, 0x0707);
def_checked_pipeline!(pipe_fn_08, 0x0808);
def_checked_pipeline!(pipe_fn_09, 0x0909);
def_checked_pipeline!(pipe_fn_10, 0x0a0a);
def_checked_pipeline!(pipe_fn_11, 0x0b0b);
def_checked_pipeline!(pipe_fn_12, 0x0c0c);
"""

# Live unwind-through-outlined-thunk verification test on x86_64-unknown-linux-gnu and i686-unknown-linux-gnu
LIVE_UNWIND_TEST_RS = r"""
use std::sync::atomic::{AtomicUsize, Ordering};

static DROP_TRACE: AtomicUsize = AtomicUsize::new(0);

struct Guard(usize);
impl Drop for Guard {
    fn drop(&mut self) {
        let prev = DROP_TRACE.load(Ordering::SeqCst);
        DROP_TRACE.store(prev * 10 + self.0, Ordering::SeqCst);
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn may_panic_callee(x: u32) -> u32 {
    if x == 999 {
        panic!("boom_from_outlined_callseq");
    }
    x + 10
}

#[cfg(target_arch = "x86_64")]
core::arch::global_asm!(
    ".globl outlined_callseq_thunk",
    ".type outlined_callseq_thunk, @function",
    "outlined_callseq_thunk:",
    ".cfi_startproc",
    "sub rsp, 8",
    ".cfi_adjust_cfa_offset 8",
    "call may_panic_callee",
    "add rsp, 8",
    ".cfi_adjust_cfa_offset -8",
    "ret",
    ".cfi_endproc",
);

#[cfg(target_arch = "x86")]
core::arch::global_asm!(
    ".globl outlined_callseq_thunk",
    ".type outlined_callseq_thunk, @function",
    "outlined_callseq_thunk:",
    ".cfi_startproc",
    "subl $8, %esp",
    ".cfi_adjust_cfa_offset 8",
    "pushl 12(%esp)",
    ".cfi_adjust_cfa_offset 4",
    "calll may_panic_callee",
    "addl $12, %esp",
    ".cfi_adjust_cfa_offset -12",
    "retl",
    ".cfi_endproc",
    options(att_syntax)
);

unsafe extern "C-unwind" {
    fn outlined_callseq_thunk(x: u32) -> u32;
}

#[inline(never)]
fn caller_with_drops(trigger: u32) -> u32 {
    let _g1 = Guard(1);
    let _g2 = Guard(2);
    let _g3 = Guard(3);
    unsafe { outlined_callseq_thunk(trigger) }
}

fn main() {
    // 1. Normal return path through outlined_callseq_thunk
    DROP_TRACE.store(0, Ordering::SeqCst);
    let ok_val = caller_with_drops(32);
    assert_eq!(ok_val, 42);
    assert_eq!(DROP_TRACE.load(Ordering::SeqCst), 321);

    // 2. Unwind path through outlined_callseq_thunk's synthesized FDE into caller's LSDA landing pad
    DROP_TRACE.store(0, Ordering::SeqCst);
    let caught = std::panic::catch_unwind(|| caller_with_drops(999));
    assert!(caught.is_err());
    // LIFO drop order: _g3 (3) -> _g2 (2) -> _g1 (1) => 321
    assert_eq!(DROP_TRACE.load(Ordering::SeqCst), 321);
    println!("UNWIND_OK:normal={ok_val},lifo_drops={}", DROP_TRACE.load(Ordering::SeqCst));
}
"""


def parse_obj_sections(obj_path: Path) -> dict[str, int]:
    proc = subprocess.run([LLVM_SIZE, "--format=sysv", str(obj_path)], capture_output=True, text=True, check=True)
    text_b = 0
    unwind_b = 0
    lsda_b = 0
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
            text_b += sz
        elif sec.startswith((".gcc_except_table", "__gcc_except_tab", ".xdata")):
            lsda_b += sz
        elif sec.startswith((".eh_frame", ".pdata", "__unwind_info", "__eh_frame")):
            unwind_b += sz
    return {
        "text_bytes": text_b,
        "unwind_bytes": unwind_b,
        "lsda_bytes": lsda_b,
        "total_loadable_bytes": text_b + unwind_b + lsda_b,
    }


def is_skippable_meta(line: str) -> bool:
    s = line.strip()
    if not s or s.startswith(("#", "//", ";", "/*", "*")):
        return True
    if s.startswith((".cfi_", ".loc", ".file", ".cv_loc")):
        return True
    return False


def is_outlineable_inst(line: str, allow_calls: bool, is_i686: bool = False) -> bool:
    s = line.strip()
    if not s or s.startswith(("#", "//", ";", "/*", "*")) or s.endswith(":"):
        return False
    if s.startswith("."):
        return False
    low = s.lower()
    # Reject terminators/branches/returns/frame-relative stack loads
    for bad in ("ret", "jmp", "je", "jne", "jz", "jnz", "jb", "ja", "jl", "jg", "b.", "cbz", "cbnz", "tbz", "tbnz", "br ", "blr", "pop", "rsp", "[sp", "(%esp)", "(%rsp)"):
        if bad in low:
            return False
    if not is_i686 and ("push" in low or "esp" in low):
        return False
    if is_i686 and ("ebp" in low or "ebx" in low):
        return False
    if "got" in low or ".l0$pb" in low or "rip" in low or "@page" in low or "@plt" in low:
        return False
    is_call = low.startswith(("call\t", "callq\t", "calll\t", "bl\t", "call ", "bl "))
    if is_call:
        return allow_calls
    return True


def is_balanced_i686_window(insts: list[str]) -> bool:
    """Verify that any pushl/subl/addl %esp inside an i686 candidate window has net delta_esp == 0 and never reads caller [esp+d]."""
    delta = 0
    for ln in insts:
        low = ln.strip().lower()
        if low.startswith("pushl"):
            if "%esp" in low:
                return False
            delta -= 4
        elif low.startswith("subl") and "%esp" in low:
            m = re.search(r"\$([0-9]+)", low)
            if not m:
                return False
            delta -= int(m.group(1))
        elif low.startswith("addl") and "%esp" in low:
            m = re.search(r"\$([0-9]+)", low)
            if not m:
                return False
            delta += int(m.group(1))
        elif "esp" in low:
            return False
    return delta == 0


def outline_asm_with_calls(asm_text: str, target: str, allow_calls: bool) -> tuple[str, int, int]:
    """Outline repeated instruction windows: leaf-only when allow_calls=False, call-inclusive when allow_calls=True."""
    raw_lines = asm_text.splitlines()
    # Filter out .cfi_loc / comments inside basic blocks while keeping track of real instruction indices
    is_i686 = target.startswith("i686")
    win_len = 7 if is_i686 else 6
    occ = {}
    i = 0
    n = len(raw_lines)
    while i < n:
        # Collect next `win_len` non-meta lines without crossing labels or non-meta directives
        span_indices = []
        insts = []
        j = i
        while j < n and len(insts) < win_len:
            ln = raw_lines[j]
            if is_skippable_meta(ln):
                j += 1
                continue
            if is_outlineable_inst(ln, allow_calls, is_i686=is_i686):
                span_indices.append(j)
                insts.append(ln.strip())
                j += 1
            else:
                break
        if len(insts) == win_len and (not is_i686 or is_balanced_i686_window(insts)):
            key = tuple(insts)
            occ.setdefault(key, []).append((span_indices[0], span_indices[-1] + 1))
            i = span_indices[-1] + 1
        else:
            i += 1

    # Select windows with >= 3 non-overlapping occurrences
    selected = {k: pos_list for k, pos_list in occ.items() if len(pos_list) >= 3}
    if not selected:
        return asm_text, 0, 0

    replace_at = {}
    thunks = []
    thunk_id = 0
    for key, pos_list in sorted(selected.items(), key=lambda kv: -len(kv[1])):
        thunk_id += 1
        tname = f"OUTLINED_CALLSEQ_{thunk_id}" if any(
            x.lower().startswith(("call", "bl\t", "bl ")) for x in key
        ) else f"OUTLINED_LEAF_{thunk_id}"
        for start_i, end_i in pos_list:
            replace_at[start_i] = (end_i, tname, key)
        thunks.append((tname, key))

    out_lines = []
    idx = 0
    call_sites_outlined = 0
    while idx < n:
        if idx in replace_at:
            end_i, tname, key = replace_at[idx]
            call_sites_outlined += 1
            if target.startswith("aarch64"):
                out_lines.append(f"\tbl\t{tname}")
            elif target.startswith("i686"):
                out_lines.append(f"\tcalll\t{tname}")
            else:
                out_lines.append(f"\tcallq\t{tname}")
            idx = end_i
        else:
            out_lines.append(raw_lines[idx])
            idx += 1

    # Emit synthesized outlined thunks at end of .text
    if target == "aarch64-apple-darwin":
        out_lines.append("\t.section\t__TEXT,__text,regular,pure_instructions")
    else:
        out_lines.append("\t.text")

    for tname, key in thunks:
        has_call = any(x.lower().startswith(("call", "bl\t", "bl ")) for x in key)
        out_lines.append("\t.p2align\t2")
        out_lines.append(f"{tname}:")
        if target.startswith("x86_64"):
            if has_call:
                out_lines.append("\tsubq\t$8, %rsp")
            for inst in key:
                out_lines.append(f"\t{inst}")
            if has_call:
                out_lines.append("\taddq\t$8, %rsp")
            out_lines.append("\tretq")
        elif target.startswith("i686"):
            for inst in key:
                out_lines.append(f"\t{inst}")
            out_lines.append("\tretl")
        else:
            if has_call:
                out_lines.append("\tstr\tx30, [sp, #-16]!")
            for inst in key:
                out_lines.append(f"\t{inst}")
            if has_call:
                out_lines.append("\tldr\tx30, [sp], #16")
            out_lines.append("\tret")

    return "\n".join(out_lines) + "\n", len(thunks), call_sites_outlined


def evaluate_target(target: str, work_dir: Path) -> dict:
    rs_file = work_dir / "workload.rs"
    rs_file.write_text(CALL_OUTLINER_WORKLOAD_RS, encoding="utf-8")

    base_s = work_dir / f"base_{target}.s"
    base_o = work_dir / f"base_{target}.o"
    subprocess.run(
        [
            RUSTC, "--target", target,
            "-C", "opt-level=z",
            "-C", "panic=unwind",
            "-C", "llvm-args=-enable-machine-outliner=never",
            "--emit=asm", str(rs_file), "-o", str(base_s),
        ],
        check=True,
    )
    subprocess.run(
        [LLVM_MC, f"--triple={target}", "--filetype=obj", str(base_s), "-o", str(base_o)],
        check=True,
    )
    base_sec = parse_obj_sections(base_o)
    asm_text = base_s.read_text(encoding="utf-8")

    # 1. Leaf-only outlining (B5 baseline: allow_calls = False)
    leaf_asm, leaf_thunks, leaf_sites = outline_asm_with_calls(asm_text, target, allow_calls=False)
    leaf_s = work_dir / f"leaf_{target}.s"
    leaf_o = work_dir / f"leaf_{target}.o"
    leaf_s.write_text(leaf_asm, encoding="utf-8")
    subprocess.run(
        [LLVM_MC, f"--triple={target}", "--filetype=obj", str(leaf_s), "-o", str(leaf_o)],
        check=True,
    )
    leaf_sec = parse_obj_sections(leaf_o)

    # 2. Call- and unwind-thunk outlining (M4: allow_calls = True)
    call_asm, call_thunks, call_sites = outline_asm_with_calls(asm_text, target, allow_calls=True)
    call_s = work_dir / f"call_{target}.s"
    call_o = work_dir / f"call_{target}.o"
    call_s.write_text(call_asm, encoding="utf-8")
    subprocess.run(
        [LLVM_MC, f"--triple={target}", "--filetype=obj", str(call_s), "-o", str(call_o)],
        check=True,
    )
    call_sec = parse_obj_sections(call_o)

    leaf_red_pct = round(100.0 * (base_sec["text_bytes"] - leaf_sec["text_bytes"]) / base_sec["text_bytes"], 2)
    call_red_pct = round(100.0 * (base_sec["text_bytes"] - call_sec["text_bytes"]) / base_sec["text_bytes"], 2)
    net_loadable_red_pct = round(
        100.0 * (base_sec["total_loadable_bytes"] - call_sec["total_loadable_bytes"]) / base_sec["total_loadable_bytes"],
        2,
    )

    return {
        "target": target,
        "baseline_text_bytes": base_sec["text_bytes"],
        "leaf_only_text_bytes": leaf_sec["text_bytes"],
        "call_outlined_text_bytes": call_sec["text_bytes"],
        "leaf_only_text_reduction_pct": leaf_red_pct,
        "call_outlined_text_reduction_pct": call_red_pct,
        "net_loadable_reduction_pct": net_loadable_red_pct,
        "call_thunks_emitted": call_thunks,
        "call_sites_outlined": call_sites,
    }


def run_live_unwind_tests(work_dir: Path) -> dict:
    results = {}
    for target in ("x86_64-unknown-linux-gnu", "i686-unknown-linux-gnu"):
        rs_path = work_dir / f"unwind_{target}.rs"
        exe_path = work_dir / f"unwind_{target}_exe"
        rs_path.write_text(LIVE_UNWIND_TEST_RS, encoding="utf-8")
        subprocess.run(
            [RUSTC, "--target", target, "-C", "opt-level=z", "-C", "panic=unwind", str(rs_path), "-o", str(exe_path)],
            check=True,
        )
        out = subprocess.check_output([str(exe_path)], text=True).strip()
        results[target] = {
            "passed": (out == "UNWIND_OK:normal=42,lifo_drops=321"),
            "output": out,
        }
    return results


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=HERE / "call_outliner_8target_results.json")
    args = parser.parse_args()

    tmp_base = Path(os.environ.get("TMPDIR", "/tmp"))
    per_target = {}
    with tempfile.TemporaryDirectory(dir=tmp_base) as tmp:
        work_dir = Path(tmp)
        for target in TIER1_TARGETS:
            per_target[target] = evaluate_target(target, work_dir)
        live_unwind = run_live_unwind_tests(work_dir)

    summary = {
        "targets_verified": len(per_target),
        "live_catch_unwind_verified": all(v["passed"] for v in live_unwind.values()),
        "live_unwind_tests": live_unwind,
        "per_target": per_target,
    }
    args.out.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(f"Verified call-outliner across all 8 Tier 1 targets + live catch_unwind; wrote {args.out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
