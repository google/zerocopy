#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Self-contained empirical reproducer for `.eh_frame` unwinding, `options(may_unwind)`
CFI hazards, non-`may_unwind` `asm!` FDE poisoning, cross-language C/C++ unwinding,
and the `DW_CFA_*` / `.gcc_except_table` opcode census.

Runs strictly inside `with tempfile.TemporaryDirectory():` so `/tmp` remains 100%
clean on exit. Requires `rustup` (with stable/nightly `x86_64-unknown-linux-gnu`),
`gcc`, `g++`, `readelf`, `objcopy`, and `llvm-dwarfdump`.
"""

from __future__ import annotations

import argparse
import collections
import json
import os
import re
import subprocess
import tempfile
from pathlib import Path
from typing import Any

DW_CFA_RE = re.compile(r"^\s*(DW_CFA_[A-Za-z0-9_]+):(.*)$")


def run_cmd(cmd: list[str], cwd: Path, timeout: float = 30.0) -> dict[str, Any]:
    proc = subprocess.run(
        cmd,
        cwd=str(cwd),
        capture_output=True,
        text=True,
        timeout=timeout,
        env={**os.environ, "RUST_BACKTRACE": "0"},
    )
    return {
        "rc": proc.returncode,
        "stdout": proc.stdout.strip(),
        "stderr": proc.stderr.strip(),
    }


def parse_dwarfdump_eh_frame(text: str) -> dict[str, Any]:
    op_counts: collections.Counter[str] = collections.Counter()
    cie_count = 0
    fde_count = 0
    augmentations: collections.Counter[str] = collections.Counter()
    cfa_regs: collections.Counter[str] = collections.Counter()
    expression_examples: list[str] = []

    for line in text.splitlines():
        s = line.strip()
        if re.match(r"^[0-9a-f]{8}\s+[0-9a-f]{8}\s+00000000\s+CIE", s):
            cie_count += 1
        elif re.match(r"^[0-9a-f]{8}\s+[0-9a-f]{8}\s+[0-9a-f]{8}\s+FDE", s):
            fde_count += 1
        elif s.startswith("Augmentation:"):
            aug = s.split(":", 1)[1].strip().strip('"')
            augmentations[aug] += 1
        else:
            m = DW_CFA_RE.match(line)
            if m:
                op = m.group(1)
                rest = m.group(2).strip()
                op_counts[op] += 1
                if op in ("DW_CFA_def_cfa", "DW_CFA_def_cfa_register"):
                    reg_tok = rest.split()[0].rstrip(",") if rest else ""
                    cfa_regs[reg_tok] += 1
                if "expression" in op and len(expression_examples) < 8:
                    expression_examples.append(f"{op}: {rest}")

    return {
        "cie_count": cie_count,
        "fde_count": fde_count,
        "augmentations": dict(augmentations),
        "cfa_registers": dict(cfa_regs),
        "opcodes": dict(sorted(op_counts.items())),
        "expression_examples": expression_examples,
    }


def run_all_probes(stable_tc: str, nightly_tc: str) -> dict[str, Any]:
    stable_rustc = ["rustup", "run", stable_tc, "rustc"]
    nightly_rustc = ["rustup", "run", nightly_tc, "rustc"]
    out: dict[str, Any] = {"toolchains": {}, "poc_a": {}, "poc_b": {}, "poc_c": {}, "census": {}}

    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        out["toolchains"]["stable"] = run_cmd([*stable_rustc, "-vV"], work)["stdout"]
        out["toolchains"]["nightly"] = run_cmd([*nightly_rustc, "-vV"], work)["stdout"]
        out["toolchains"]["gcc"] = run_cmd(["gcc", "--version"], work)["stdout"].splitlines()[0]
        out["toolchains"]["g++"] = run_cmd(["g++", "--version"], work)["stdout"].splitlines()[0]

        # PoC A: `options(may_unwind)` missing CFA, missing `.cfi_rel_offset r12`, full CFI,
        # and LLVM ShrinkWrap `alignstack` bug (`rsp % 16 == 8` under `-O1..-O3`).
        poc_a_rs = work / "poc_a.rs"
        poc_a_rs.write_text(r'''
#![feature(asm_unwind)]
use std::arch::asm;
use std::hint::black_box;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::atomic::{AtomicUsize, Ordering};

static DROPS: AtomicUsize = AtomicUsize::new(0);
struct ZeroStackGuard;
impl Drop for ZeroStackGuard {
    fn drop(&mut self) { DROPS.fetch_add(1, Ordering::SeqCst); }
}

#[inline(never)]
fn opaque_u64(x: u64) -> u64 { black_box(x) }

extern "C-unwind" fn maybe_panic(do_panic: u64) -> u64 {
    if do_panic != 0 { panic!("boom from C-unwind"); }
    0x1234_5678_9ABC_DEF0
}

#[inline(never)]
unsafe fn a1_missing_cfa(do_panic: u64) -> u64 {
    let ret: u64;
    unsafe {
        asm!(
            "push rbx",
            "sub rsp, 8",
            "mov rbx, 0xDEADBEEFCAFEBABE",
            "call {cb}",
            "add rsp, 8",
            "pop rbx",
            cb = sym maybe_panic,
            in("rdi") do_panic,
            lateout("rax") ret,
            clobber_abi("C"),
            options(may_unwind),
        );
    }
    ret
}

#[inline(never)]
unsafe fn a2_missing_r12_cfi(do_panic: u64) -> u64 {
    let ret: u64;
    unsafe {
        asm!(
            "push r12",
            ".cfi_adjust_cfa_offset 8",
            "sub rsp, 8",
            ".cfi_adjust_cfa_offset 8",
            "mov r12, 0x7777777777777777",
            "call {cb}",
            "add rsp, 8",
            ".cfi_adjust_cfa_offset -8",
            "pop r12",
            ".cfi_adjust_cfa_offset -8",
            cb = sym maybe_panic,
            in("rdi") do_panic,
            lateout("rax") ret,
            clobber_abi("C"),
            options(may_unwind),
        );
    }
    ret
}

#[inline(never)]
unsafe fn a3_repaired_full_cfi(do_panic: u64) -> u64 {
    let ret: u64;
    unsafe {
        asm!(
            "push r12",
            ".cfi_adjust_cfa_offset 8",
            ".cfi_rel_offset r12, 0",
            "sub rsp, 8",
            ".cfi_adjust_cfa_offset 8",
            "mov r12, 0x7777777777777777",
            "call {cb}",
            "add rsp, 8",
            ".cfi_adjust_cfa_offset -8",
            "pop r12",
            ".cfi_adjust_cfa_offset -8",
            ".cfi_restore r12",
            cb = sym maybe_panic,
            in("rdi") do_panic,
            lateout("rax") ret,
            clobber_abi("C"),
            options(may_unwind),
        );
    }
    ret
}

#[inline(never)]
unsafe fn a4_shrinkwrap_sp_mod_16() -> u64 {
    let _g = ZeroStackGuard;
    let sp: u64;
    unsafe {
        asm!("mov rax, rsp", lateout("rax") sp, options(may_unwind));
    }
    sp & 15
}

#[inline(never)]
fn safe_caller(which: u8, do_panic: u64) -> (bool, [u64; 5]) {
    let v0 = opaque_u64(0x1111_1111_1111_1111);
    let v1 = opaque_u64(0x2222_2222_2222_2222);
    let v2 = opaque_u64(0x3333_3333_3333_3333);
    let v3 = opaque_u64(0x4444_4444_4444_4444);
    let v4 = opaque_u64(0x5555_5555_5555_5555);
    let res = catch_unwind(AssertUnwindSafe(|| unsafe {
        match which {
            1 => { black_box(a1_missing_cfa(do_panic)); }
            2 => { black_box(a2_missing_r12_cfi(do_panic)); }
            3 => { black_box(a3_repaired_full_cfi(do_panic)); }
            _ => {}
        }
    }));
    (res.is_err(), [v0, v1, v2, v3, v4])
}

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_default();
    match mode.as_str() {
        "a1_normal" => {
            let mut ok = 0;
            for _ in 0..1000 {
                let (c, vs) = safe_caller(1, 0);
                if !c && vs[1] == 0x2222_2222_2222_2222 { ok += 1; }
            }
            println!("ok={ok}/1000");
        }
        "a1_panic" => {
            let (c, vs) = safe_caller(1, 1);
            println!("caught={c} v1=0x{:016x}", vs[1]);
        }
        "a2_panic" => {
            let (c, vs) = safe_caller(2, 1);
            let exp = [
                0x1111_1111_1111_1111,
                0x2222_2222_2222_2222,
                0x3333_3333_3333_3333,
                0x4444_4444_4444_4444,
                0x5555_5555_5555_5555,
            ];
            println!("caught={c} corrupted={} vals={vs:#018x?}", vs != exp);
        }
        "a3_panic" => {
            let (c, vs) = safe_caller(3, 1);
            let exp = [
                0x1111_1111_1111_1111,
                0x2222_2222_2222_2222,
                0x3333_3333_3333_3333,
                0x4444_4444_4444_4444,
                0x5555_5555_5555_5555,
            ];
            println!("caught={c} corrupted={}", vs != exp);
        }
        "a4_sp_mod_16" => {
            println!("sp_mod_16={}", unsafe { a4_shrinkwrap_sp_mod_16() });
        }
        _ => panic!("unknown mode"),
    }
}
''')
        bin_a = work / "poc_a"
        subprocess.check_call([*nightly_rustc, "-C", "opt-level=2", "-C", "panic=unwind", str(poc_a_rs), "-o", str(bin_a)])
        for m in ["a1_normal", "a1_panic", "a2_panic", "a3_panic", "a4_sp_mod_16"]:
            r = run_cmd([str(bin_a), m], work)
            out["poc_a"][m] = {"rc": r["rc"], "stdout": r["stdout"]}

        # PoC B: Non-`may_unwind` 0-instruction/dead-branch FDE poisoning on stable `rustc`
        poc_b_rs = work / "poc_b.rs"
        poc_b_rs.write_text(r'''
use std::arch::asm;
use std::hint::black_box;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::atomic::{AtomicUsize, Ordering};

static DROPS: AtomicUsize = AtomicUsize::new(0);
struct Guard;
impl Drop for Guard {
    fn drop(&mut self) { DROPS.fetch_add(1, Ordering::SeqCst); }
}

#[inline(never)]
fn opaque_u64(x: u64) -> u64 { black_box(x) }

#[inline(never)]
fn safe_panic(p: bool) { if p { panic!("safe panic"); } }

#[inline(never)]
fn b1_cfa_shift(p: bool) {
    let _g = Guard;
    unsafe { asm!(".cfi_adjust_cfa_offset 16", options(nomem, nostack, preserves_flags)); }
    safe_panic(black_box(p));
}

#[inline(never)]
fn b2_dead_branch_cfa_shift(skip_asm: bool, p: bool) {
    let _g = Guard;
    if !skip_asm {
        unsafe { asm!("nop\n.cfi_adjust_cfa_offset 16", options(nomem, nostack, preserves_flags)); }
    }
    safe_panic(black_box(p));
}

#[inline(never)]
fn b3_undefined_rip(p: bool) {
    let _g = Guard;
    unsafe { asm!(".cfi_undefined rip", options(nomem, nostack, preserves_flags)); }
    safe_panic(black_box(p));
}

#[inline(never)]
fn b5_escape_r12_is_rip(p: bool) {
    unsafe { asm!(".cfi_escape 0x8c, 0x01", options(nomem, nostack, preserves_flags)); }
    safe_panic(black_box(p));
}

#[repr(transparent)]
pub struct SyncFnPtr(pub extern "C" fn(i32, i32, u64, *mut (), *mut ()) -> i32);
unsafe impl Sync for SyncFnPtr {}

#[unsafe(no_mangle)]
pub extern "C" fn skip_drops_personality(_v: i32, _a: i32, _c: u64, _e: *mut (), _ctx: *mut ()) -> i32 {
    8 // _URC_CONTINUE_UNWIND
}

#[unsafe(no_mangle)]
pub static DW_ref_skip_drops_personality: SyncFnPtr = SyncFnPtr(skip_drops_personality);

#[inline(never)]
fn b6_pic_personality_hijack(p: bool) {
    let _g = Guard;
    unsafe {
        asm!(".cfi_personality 0x9b, DW_ref_skip_drops_personality", options(nomem, nostack, preserves_flags));
    }
    safe_panic(black_box(p));
}

#[unsafe(no_mangle)]
pub static EMPTY_LSDA_BYTES: [u8; 9] = [0xff, 0xff, 0x01, 0x05, 0x00, 0xff, 0x0f, 0x00, 0x00];

#[inline(never)]
fn b7_pic_lsda_hijack(p: bool) {
    let _g = Guard;
    unsafe {
        asm!(".cfi_lsda 0x1b, EMPTY_LSDA_BYTES", options(nomem, nostack, preserves_flags));
    }
    safe_panic(black_box(p));
}

#[inline(never)]
fn run_b5_outer(p: bool) -> (bool, [u64; 5]) {
    let v0 = opaque_u64(0x1111_1111_1111_1111);
    let v1 = opaque_u64(0x2222_2222_2222_2222);
    let v2 = opaque_u64(0x3333_3333_3333_3333);
    let v3 = opaque_u64(0x4444_4444_4444_4444);
    let v4 = opaque_u64(0x5555_5555_5555_5555);
    let res = catch_unwind(AssertUnwindSafe(|| b5_escape_r12_is_rip(p)));
    (res.is_err(), [v0, v1, v2, v3, v4])
}

fn main() {
    black_box(&DW_ref_skip_drops_personality);
    black_box(&EMPTY_LSDA_BYTES);
    DROPS.store(0, Ordering::SeqCst);
    let m = std::env::args().nth(1).unwrap_or_default();
    match m.as_str() {
        "b1_panic" => {
            let r = catch_unwind(AssertUnwindSafe(|| b1_cfa_shift(true)));
            println!("caught={} drops={}", r.is_err(), DROPS.load(Ordering::SeqCst));
        }
        "b2_unexecuted_panic" => {
            let r = catch_unwind(AssertUnwindSafe(|| b2_dead_branch_cfa_shift(black_box(true), true)));
            println!("caught={} drops={}", r.is_err(), DROPS.load(Ordering::SeqCst));
        }
        "b3_undefined_rip" => {
            let r = catch_unwind(AssertUnwindSafe(|| b3_undefined_rip(true)));
            println!("caught={} drops={}", r.is_err(), DROPS.load(Ordering::SeqCst));
        }
        "b5_escape_r12" => {
            let (c, vs) = run_b5_outer(true);
            let exp = [
                0x1111_1111_1111_1111,
                0x2222_2222_2222_2222,
                0x3333_3333_3333_3333,
                0x4444_4444_4444_4444,
                0x5555_5555_5555_5555,
            ];
            println!("caught={c} corrupted={} leaked_rip=0x{:016x}", vs != exp, vs[1]);
        }
        "b6_personality" => {
            let r = catch_unwind(AssertUnwindSafe(|| b6_pic_personality_hijack(true)));
            println!("caught={} drops={}", r.is_err(), DROPS.load(Ordering::SeqCst));
        }
        "b7_lsda" => {
            let r = catch_unwind(AssertUnwindSafe(|| b7_pic_lsda_hijack(true)));
            println!("caught={} drops={}", r.is_err(), DROPS.load(Ordering::SeqCst));
        }
        _ => panic!("unknown mode"),
    }
}
''')
        bin_b = work / "poc_b"
        subprocess.check_call([*stable_rustc, "-C", "opt-level=2", "-C", "panic=unwind", str(poc_b_rs), "-o", str(bin_b)])
        for m in ["b1_panic", "b2_unexecuted_panic", "b3_undefined_rip", "b5_escape_r12", "b6_personality", "b7_lsda"]:
            r = run_cmd([str(bin_b), m], work)
            out["poc_b"][m] = {"rc": r["rc"], "stdout": r["stdout"]}

        # PoC C: Cross-language GCC C `.o` callback unwinding
        c_src = work / "c_mid.c"
        c_src.write_text(r'''
#include <stdint.h>
extern volatile int c_cleanup_count;
static void c_cleanup_fn(int *p) { (void)p; c_cleanup_count += 1; }
__attribute__((noinline))
uint64_t c_qsort_style_invoke(uint64_t (*cb)(uint64_t), uint64_t arg) {
    int guard __attribute__((cleanup(c_cleanup_fn))) = 123;
    volatile uint64_t local_buf[4] = {arg, arg + 1, arg + 2, arg + 3};
    uint64_t r = cb(local_buf[0]);
    return r + local_buf[3] + (uint64_t)guard;
}
''')
        r_drv = work / "r_drv.rs"
        r_drv.write_text(r'''
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::atomic::{AtomicUsize, Ordering};
#[unsafe(no_mangle)] pub static mut c_cleanup_count: i32 = 0;
static RDROPS: AtomicUsize = AtomicUsize::new(0);
struct RG; impl Drop for RG { fn drop(&mut self) { RDROPS.fetch_add(1, Ordering::SeqCst); } }
unsafe extern "C-unwind" { fn c_qsort_style_invoke(cb: extern "C-unwind" fn(u64) -> u64, arg: u64) -> u64; }
extern "C-unwind" fn cb(x: u64) -> u64 { let _g = RG; if x != 0 { panic!("cb panic"); } 100 }
fn main() {
    let p = std::env::args().nth(1).unwrap_or_default() == "panic";
    let r = catch_unwind(AssertUnwindSafe(|| unsafe { let _o = RG; c_qsort_style_invoke(cb, if p { 1 } else { 0 }) }));
    println!("caught={} rdrops={} ccleanup={}", r.is_err(), RDROPS.load(Ordering::SeqCst), unsafe { c_cleanup_count });
}
''')
        for tag, flags in [
            ("no_uw_tables", ["-O2", "-fno-exceptions", "-fno-asynchronous-unwind-tables", "-fno-unwind-tables"]),
            ("default_O2", ["-O2"]),
            ("fexceptions", ["-O2", "-fexceptions"]),
        ]:
            obj = work / f"{tag}.o"
            subprocess.check_call(["gcc", *flags, "-c", str(c_src), "-o", str(obj)])
            exe = work / f"exe_{tag}"
            subprocess.check_call([*stable_rustc, "-C", "opt-level=2", "-C", "panic=unwind", str(r_drv), f"-Clink-arg={obj}", "-o", str(exe)])
            rn = run_cmd([str(exe), "normal"], work)
            rp = run_cmd([str(exe), "panic"], work)
            out["poc_c"][tag] = {"normal": rn["stdout"], "panic_rc": rp["rc"], "panic_stdout": rp["stdout"]}

        # Synthetic census verification (`gcc -O3 -mavx2 -fexceptions -fstack-clash-protection`)
        drap_c = work / "drap.c"
        drap_c.write_text(r'''
#include <alloca.h>
#include <stddef.h>
#include <stdint.h>
extern void sink(void *, size_t);
uint64_t drap_fn(size_t n, uint64_t x) {
    __attribute__((aligned(64))) uint8_t buf[128];
    uint8_t *vla = (uint8_t *)alloca(n + 16);
    buf[0] = (uint8_t)x; vla[0] = (uint8_t)(x + 1);
    sink(buf, 128); sink(vla, n);
    return buf[0] + vla[0];
}
''')
        drap_o = work / "drap.o"
        subprocess.check_call(["gcc", "-O3", "-mavx2", "-fPIC", "-fexceptions", "-c", str(drap_c), "-o", str(drap_o)])
        dd = subprocess.check_output(["llvm-dwarfdump", "--eh-frame", str(drap_o)], text=True)
        out["census"]["gcc_drap_sample"] = parse_dwarfdump_eh_frame(dd)

    return out


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--stable-toolchain", default="1.99.1-x86_64-unknown-linux-gnu")
    ap.add_argument("--nightly-toolchain", default="nightly-x86_64-unknown-linux-gnu")
    ap.add_argument("--output-json", default="")
    args = ap.parse_args()

    res = run_all_probes(args.stable_toolchain, args.nightly_toolchain)
    rendered = json.dumps(res, indent=2, sort_keys=True) + "\n"
    if args.output_json:
        Path(args.output_json).write_text(rendered)
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
