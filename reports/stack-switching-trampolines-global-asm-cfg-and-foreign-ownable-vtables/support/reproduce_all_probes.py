#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Standalone empirical reproducer for stack-switching trampolines, global_asm!
section-wide cutpoint graphs, and ForeignOwnable C ops-table lifecycles."""

from __future__ import annotations

import argparse
import glob
import json
import os
import shutil
import struct
import subprocess
import tempfile
from pathlib import Path
from typing import Any


def run_cmd(
    cmd: list[str],
    *,
    cwd: str | None = None,
    env: dict[str, str] | None = None,
    timeout: float = 60.0,
) -> subprocess.CompletedProcess[str]:
    merged_env = os.environ.copy()
    if env:
        merged_env.update(env)
    return subprocess.run(
        cmd,
        cwd=cwd,
        env=merged_env,
        text=True,
        capture_output=True,
        timeout=timeout,
        check=False,
    )


# ---------------------------------------------------------------------------
# Suite 1A: Miri (-Zmiri-tree-borrows) Dormant-Stack StrongProtector Matrix
# ---------------------------------------------------------------------------


def run_miri_dormant_stack_suite(td: str) -> dict[str, Any]:
    proj = Path(td) / "miri_dormant_tb"
    (proj / "src").mkdir(parents=True, exist_ok=True)
    (proj / "Cargo.toml").write_text(
        '[package]\nname = "miri_dormant_tb"\nversion = "0.1.0"\nedition = "2021"\n',
        encoding="utf-8",
    )
    (proj / "src" / "lib.rs").write_text(
        r'''#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]
use std::ops::{Coroutine, CoroutineState};
use std::pin::Pin;
use std::sync::{Arc, Condvar, Mutex};
use std::thread;

/// Symmetric fiber synchronization gate matching Wasmtime's `crates/fiber/src/miri.rs`:
/// Stack A suspends mid-frame (retaining its `FnEntry` `StrongProtector`s in
/// `global.protected_tags`) while Stack B executes, then resumes Stack A.
struct FiberGate {
    turn: Mutex<u8>,
    cv: Condvar,
}

impl FiberGate {
    fn new() -> Arc<Self> {
        Arc::new(Self { turn: Mutex::new(0), cv: Condvar::new() })
    }
    fn switch_a_to_b(&self) {
        let mut g = self.turn.lock().unwrap();
        *g = 1;
        self.cv.notify_all();
        while *g == 1 {
            g = self.cv.wait(g).unwrap();
        }
    }
    fn wait_b_turn(&self) {
        let mut g = self.turn.lock().unwrap();
        while *g == 0 {
            g = self.cv.wait(g).unwrap();
        }
    }
    fn switch_b_to_a(&self) {
        let mut g = self.turn.lock().unwrap();
        *g = 2;
        self.cv.notify_all();
    }
}

#[derive(Clone, Copy)]
struct RawPtr(*mut u64);
unsafe impl Send for RawPtr {}
unsafe impl Sync for RawPtr {}

#[test]
fn m1_raw_inline_asm_stack_switch_unsupported_in_miri() {
    let sp: usize;
    unsafe {
        core::arch::asm!("mov {}, rsp", out(reg) sp, options(nomem, nostack, preserves_flags));
    }
    assert!(sp != 0);
}

#[test]
fn m2a_dormant_stack_disjoint_access_ok() {
    let gate = FiberGate::new();
    let mut slot_a: u64 = 10;
    let mut slot_b: u64 = 20;
    let ptr_b = RawPtr(&raw mut slot_b);
    let g2 = gate.clone();
    let handle = thread::spawn(move || {
        g2.wait_b_turn();
        let pb = ptr_b;
        unsafe { *pb.0 += 5; }
        g2.switch_b_to_a();
    });

    fn stack_a_frame(x: &mut u64, gate: &FiberGate) -> u64 {
        *x = 11;
        gate.switch_a_to_b();
        *x + 1
    }
    let out = stack_a_frame(&mut slot_a, &gate);
    handle.join().unwrap();
    assert_eq!((out, slot_b), (12, 25));
}

#[test]
fn m2b_dormant_stack_child_ptr_write_from_stack_b_ok() {
    let gate = FiberGate::new();
    let mut slot: u64 = 10;

    fn stack_a_with_child(x: &mut u64, gate: &Arc<FiberGate>) -> u64 {
        let child = RawPtr(&raw mut *x);
        let g2 = gate.clone();
        let h = thread::spawn(move || {
            g2.wait_b_turn();
            let c = child;
            unsafe { *c.0 = 77; }
            g2.switch_b_to_a();
        });
        gate.switch_a_to_b();
        h.join().unwrap();
        *x
    }
    assert_eq!(stack_a_with_child(&mut slot, &gate), 77);
}

#[test]
fn m2c_dormant_stack_activated_mut_sibling_write_immediate_ub() {
    let gate = FiberGate::new();
    let mut slot: u64 = 10;
    let root_sibling = RawPtr(&raw mut slot);
    let g2 = gate.clone();
    let h = thread::spawn(move || {
        g2.wait_b_turn();
        let rs = root_sibling;
        unsafe { *rs.0 = 99; }
        g2.switch_b_to_a();
    });

    fn stack_a_activated(x: &mut u64, gate: &FiberGate) -> u64 {
        *x = 11;
        gate.switch_a_to_b();
        *x
    }
    let _ = stack_a_activated(&mut slot, &gate);
    h.join().unwrap();
}

#[test]
fn m2d_dormant_stack_activated_mut_sibling_read_immediate_ub() {
    let gate = FiberGate::new();
    let mut slot: u64 = 10;
    let root_sibling = RawPtr(&raw mut slot);
    let g2 = gate.clone();
    let h = thread::spawn(move || {
        g2.wait_b_turn();
        let rs = root_sibling;
        let _val = unsafe { *rs.0 };
        g2.switch_b_to_a();
    });

    fn stack_a_activated_never_reused(x: &mut u64, gate: &FiberGate) -> u64 {
        *x = 11;
        gate.switch_a_to_b();
        0
    }
    let _ = stack_a_activated_never_reused(&mut slot, &gate);
    h.join().unwrap();
}

#[test]
fn m2e_dormant_stack_reserved_frz_sibling_read_taints_resumed_write_ub() {
    let gate = FiberGate::new();
    let mut slot: u64 = 10;
    let root_sibling = RawPtr(&raw mut slot);
    let g2 = gate.clone();
    let h = thread::spawn(move || {
        g2.wait_b_turn();
        let rs = root_sibling;
        let seen = unsafe { *rs.0 };
        assert_eq!(seen, 10);
        g2.switch_b_to_a();
    });

    fn stack_a_unactivated_then_writes_on_resume(x: &mut u64, gate: &FiberGate) {
        gate.switch_a_to_b();
        *x = 42;
    }
    stack_a_unactivated_then_writes_on_resume(&mut slot, &gate);
    h.join().unwrap();
}

#[test]
fn m2f_dormant_stack_reserved_frz_sibling_read_resumed_read_only_ok() {
    let gate = FiberGate::new();
    let mut slot: u64 = 10;
    let root_sibling = RawPtr(&raw mut slot);
    let g2 = gate.clone();
    let h = thread::spawn(move || {
        g2.wait_b_turn();
        let rs = root_sibling;
        let seen = unsafe { *rs.0 };
        assert_eq!(seen, 10);
        g2.switch_b_to_a();
    });

    fn stack_a_unactivated_then_reads_on_resume(x: &mut u64, gate: &FiberGate) -> u64 {
        gate.switch_a_to_b();
        *x
    }
    assert_eq!(stack_a_unactivated_then_reads_on_resume(&mut slot, &gate), 10);
    h.join().unwrap();
}

#[test]
fn m2g_stackless_coroutine_yield_retires_fn_entry_protector_contrast() {
    let mut slot: u64 = 10;
    let raw = &raw mut slot;
    let rmut: &mut u64 = unsafe { &mut *raw };
    let mut gen_block = #[coroutine] move || {
        *rmut = 11;
        yield;
        *rmut
    };
    assert_eq!(Pin::new(&mut gen_block).resume(()), CoroutineState::Yielded(()));
    let seen_while_yielded = unsafe { *raw };
    assert_eq!(seen_while_yielded, 11);
    assert_eq!(Pin::new(&mut gen_block).resume(()), CoroutineState::Complete(11));
}
''',
        encoding="utf-8",
    )

    tests = [
        "m1_raw_inline_asm_stack_switch_unsupported_in_miri",
        "m2a_dormant_stack_disjoint_access_ok",
        "m2b_dormant_stack_child_ptr_write_from_stack_b_ok",
        "m2c_dormant_stack_activated_mut_sibling_write_immediate_ub",
        "m2d_dormant_stack_activated_mut_sibling_read_immediate_ub",
        "m2e_dormant_stack_reserved_frz_sibling_read_taints_resumed_write_ub",
        "m2f_dormant_stack_reserved_frz_sibling_read_resumed_read_only_ok",
        "m2g_stackless_coroutine_yield_retires_fn_entry_protector_contrast",
    ]
    results: dict[str, Any] = {}
    for tname in tests:
        cp = run_cmd(
            ["cargo", "+nightly", "miri", "test", "--", "--exact", tname],
            cwd=str(proj),
            env={"MIRIFLAGS": "-Zmiri-tree-borrows"},
            timeout=60.0,
        )
        diag = ""
        for line in (cp.stderr + "\n" + cp.stdout).splitlines():
            if any(k in line for k in ["Undefined Behavior:", "unsupported operation:", "is forbidden"]):
                diag = line.strip()
                break
        results[tname] = {
            "exit_code": cp.returncode,
            "passed": cp.returncode == 0,
            "diagnostic": diag,
        }
    return results


# ---------------------------------------------------------------------------
# Suite 1B: Native x86-64 2-Entry Trampoline & DW_CFA_undefined (rip)
# ---------------------------------------------------------------------------


def run_x86_64_trampoline_cfi_suite(td: str) -> dict[str, Any]:
    rs_file = Path(td) / "x64_fiber.rs"
    exe_file = Path(td) / "x64_fiber"
    rs_file.write_text(
        r'''use std::arch::global_asm;
use std::env;
use std::ffi::c_void;
use std::panic::{self, AssertUnwindSafe};
use std::sync::atomic::{AtomicUsize, Ordering};

global_asm!(
    ".text",
    ".globl fiber_enter_x64",
    ".type fiber_enter_x64, @function",
    "fiber_enter_x64:",
    ".cfi_startproc",
    "push rbp",
    ".cfi_adjust_cfa_offset 8",
    ".cfi_offset rbp, -16",
    "push rbx",
    ".cfi_adjust_cfa_offset 8",
    ".cfi_offset rbx, -24",
    "push r12",
    ".cfi_adjust_cfa_offset 8",
    ".cfi_offset r12, -32",
    "push r13",
    ".cfi_adjust_cfa_offset 8",
    ".cfi_offset r13, -40",
    "push r14",
    ".cfi_adjust_cfa_offset 8",
    ".cfi_offset r14, -48",
    "push r15",
    ".cfi_adjust_cfa_offset 8",
    ".cfi_offset r15, -56",
    "mov [rdi + 0], rsp",
    "mov rsp, [rdi + 8]",
    "jmp .Lfiber_restore_common",
    ".cfi_endproc",
    ".size fiber_enter_x64, . - fiber_enter_x64",

    ".globl fiber_yield_x64",
    ".type fiber_yield_x64, @function",
    "fiber_yield_x64:",
    ".cfi_startproc",
    "push rbp",
    ".cfi_adjust_cfa_offset 8",
    ".cfi_offset rbp, -16",
    "push rbx",
    ".cfi_adjust_cfa_offset 8",
    ".cfi_offset rbx, -24",
    "push r12",
    ".cfi_adjust_cfa_offset 8",
    ".cfi_offset r12, -32",
    "push r13",
    ".cfi_adjust_cfa_offset 8",
    ".cfi_offset r13, -40",
    "push r14",
    ".cfi_adjust_cfa_offset 8",
    ".cfi_offset r14, -48",
    "push r15",
    ".cfi_adjust_cfa_offset 8",
    ".cfi_offset r15, -56",
    "mov [rdi + 8], rsp",
    "mov rsp, [rdi + 0]",
    ".Lfiber_restore_common:",
    "pop r15",
    "pop r14",
    "pop r13",
    "pop r12",
    "pop rbx",
    "pop rbp",
    "ret",
    ".cfi_endproc",
    ".size fiber_yield_x64, . - fiber_yield_x64",

    ".globl fiber_root_good_x64",
    ".type fiber_root_good_x64, @function",
    "fiber_root_good_x64:",
    ".cfi_startproc",
    ".cfi_def_cfa rsp, 0",
    ".cfi_undefined rip",
    ".cfi_undefined rbp",
    "xor ebp, ebp",
    "mov rdi, r12",
    "call r13",
    "ud2",
    ".cfi_endproc",
    ".size fiber_root_good_x64, . - fiber_root_good_x64",

    ".globl fiber_root_bad_x64",
    ".type fiber_root_bad_x64, @function",
    "fiber_root_bad_x64:",
    ".cfi_startproc",
    "xor ebp, ebp",
    "mov rdi, r12",
    "call r13",
    "ud2",
    ".cfi_endproc",
    ".size fiber_root_bad_x64, . - fiber_root_bad_x64",
);

#[repr(C)]
struct FiberCtx {
    parent_sp: usize,
    child_sp: usize,
    mode: u32,
    bt_frames: usize,
    drops_ran: usize,
}

unsafe extern "C" {
    fn fiber_enter_x64(ctx: *mut FiberCtx);
    fn fiber_yield_x64(ctx: *mut FiberCtx);
    fn fiber_root_good_x64();
    fn fiber_root_bad_x64();
}

type UnwindTraceFn = extern "C" fn(*mut c_void, *mut c_void) -> i32;
#[link(name = "gcc_s")]
unsafe extern "C" {
    fn _Unwind_Backtrace(trace: UnwindTraceFn, arg: *mut c_void) -> i32;
    fn _Unwind_GetIP(ctx: *mut c_void) -> usize;
    fn mmap(addr: *mut c_void, len: usize, prot: i32, flags: i32, fd: i32, off: isize) -> *mut c_void;
    fn mprotect(addr: *mut c_void, len: usize, prot: i32) -> i32;
}

extern "C" fn trace_cb(uw_ctx: *mut c_void, arg: *mut c_void) -> i32 {
    let count = unsafe { &*(arg as *const AtomicUsize) };
    let _ip = unsafe { _Unwind_GetIP(uw_ctx) };
    let n = count.fetch_add(1, Ordering::Relaxed) + 1;
    if n >= 32 { 5 } else { 0 }
}

struct DropCounter(*mut usize);
impl Drop for DropCounter {
    fn drop(&mut self) {
        unsafe { *self.0 += 1; }
    }
}

extern "C-unwind" fn fiber_entry_rust(ctx_ptr: *mut FiberCtx) -> ! {
    let ctx = unsafe { &mut *ctx_ptr };
    match ctx.mode {
        0 => {
            let frames = AtomicUsize::new(0);
            let rc = unsafe { _Unwind_Backtrace(trace_cb, (&raw const frames) as *mut c_void) };
            assert_eq!(rc, 5);
            ctx.bt_frames = frames.load(Ordering::Relaxed);
            unsafe { fiber_yield_x64(ctx_ptr) };
            unreachable!()
        }
        1 => {
            let res = panic::catch_unwind(AssertUnwindSafe(|| {
                let _g = DropCounter(&raw mut ctx.drops_ran);
                panic!("caught inside fiber stack B");
            }));
            assert!(res.is_err());
            unsafe { fiber_yield_x64(ctx_ptr) };
            unreachable!()
        }
        _ => {
            let _g = DropCounter(&raw mut ctx.drops_ran);
            panic!("uncaught at fiber stack B root");
        }
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let variant = args.get(1).map(|s| s.as_str()).unwrap_or("good_bt");
    let (use_good_root, mode) = match variant {
        "good_bt" => (true, 0u32),
        "bad_bt" => (false, 0u32),
        "good_catch" => (true, 1u32),
        "good_uncaught" => (true, 2u32),
        "bad_uncaught" => (false, 2u32),
        _ => panic!("unknown variant"),
    };

    let page = 4096usize;
    let raw = unsafe { mmap(std::ptr::null_mut(), page * 4, 0, 0x22, -1, 0) };
    assert!((raw as isize) != -1);
    let stack_base = (raw as usize) + page;
    assert_eq!(unsafe { mprotect(stack_base as *mut c_void, page * 2, 3) }, 0);
    let stack_top = stack_base + page * 2;

    let init_sp = stack_top - 7 * 8;
    let mut ctx = FiberCtx { parent_sp: 0, child_sp: init_sp, mode, bt_frames: 0, drops_ran: 0 };
    let root_fn: usize = if use_good_root {
        fiber_root_good_x64 as *const () as usize
    } else {
        fiber_root_bad_x64 as *const () as usize
    };
    let words: [usize; 7] = [
        0,
        0,
        fiber_entry_rust as *const () as usize,
        (&raw mut ctx) as usize,
        0,
        0,
        root_fn,
    ];
    unsafe {
        std::ptr::copy_nonoverlapping(words.as_ptr(), init_sp as *mut usize, 7);
        fiber_enter_x64(&raw mut ctx);
    }
    println!("OK variant={} bt_frames={} drops={}", variant, ctx.bt_frames, ctx.drops_ran);
}
''',
        encoding="utf-8",
    )
    comp = run_cmd(
        ["rustc", "+nightly", "-C", "opt-level=2", "-C", "panic=unwind", "-C", "force-frame-pointers=no", str(rs_file), "-o", str(exe_file)],
        timeout=30.0,
    )
    assert comp.returncode == 0, comp.stderr
    dwarfdump = run_cmd(["llvm-dwarfdump", "--eh-frame", str(exe_file)]).stdout
    has_undef_rip = "DW_CFA_undefined: RIP" in dwarfdump or "DW_CFA_undefined: reg16" in dwarfdump

    runs = {}
    for v in ["good_bt", "bad_bt", "good_catch", "good_uncaught", "bad_uncaught"]:
        r = run_cmd([str(exe_file), v], timeout=10.0)
        runs[v] = {"exit_code": r.returncode, "stdout": r.stdout.strip()}
    return {"eh_frame_has_dw_cfa_undefined_rip": has_undef_rip, "runs": runs}


# ---------------------------------------------------------------------------
# Suite 1C: QEMU AArch64 2-Entry Trampoline & DW_CFA_undefined (x30)
# ---------------------------------------------------------------------------


def find_cached_crate(name_prefix: str) -> Path | None:
    cargo_home = Path(os.environ.get("CARGO_HOME", os.path.expanduser("~/.cargo")))
    matches = sorted(glob.glob(str(cargo_home / "registry" / "src" / "index.crates.io-*" / name_prefix)))
    return Path(matches[-1]) if matches else None


def run_aarch64_qemu_trampoline_cfi_suite(td: str) -> dict[str, Any]:
    qemu = shutil.which("qemu-aarch64")
    unw_dir = find_cached_crate("unwinding-0.2.10")
    gimli_dir = find_cached_crate("gimli-0.34.0")
    targets_199 = run_cmd(["rustup", "target", "list", "--installed", "--toolchain", "1.99.1"]).stdout.splitlines()
    if not (qemu and unw_dir and gimli_dir and "aarch64-unknown-linux-gnu" in targets_199):
        return {"skipped": True}

    sysroot_199 = run_cmd(["rustc", "+1.99.1", "--print", "sysroot"]).stdout.strip()
    rust_lld = glob.glob(f"{sysroot_199}/lib/rustlib/*/bin/rust-lld")[0]

    proj = Path(td) / "a64_uw"
    (proj / "src").mkdir(parents=True)
    (proj / ".cargo").mkdir()
    lds = Path(td) / "a64.lds"
    lds.write_text(
        "SECTIONS {\n"
        "  . = 0x400000 + SIZEOF_HEADERS;\n"
        "  __executable_start = 0x400000;\n"
        "  .text : { *(.text .text.*) }\n"
        "  __etext = .;\n"
        "  . = ALIGN(0x10000);\n"
        "  .rodata : { *(.rodata .rodata.*) *(.gcc_except_table .gcc_except_table.*) }\n"
        "  .eh_frame : { __eh_frame = .; KEEP(*(.eh_frame .eh_frame.*)) LONG(0); }\n"
        "  . = ALIGN(0x10000);\n"
        "  .data : { *(.data .data.*) *(.got .got.*) }\n"
        "  .bss : { *(.bss .bss.*) *(COMMON) }\n"
        "}\n",
        encoding="utf-8",
    )
    (proj / "Cargo.toml").write_text(
        f'[package]\nname = "a64_uw"\nversion = "0.1.0"\nedition = "2021"\n\n'
        f'[dependencies]\nunwinding = {{ path = "{unw_dir}", default-features = false, '
        f'features = ["unwinder", "dwarf-expr", "fde-static", "panic", "personality"] }}\n\n'
        f'[patch.crates-io]\ngimli = {{ path = "{gimli_dir}" }}\n',
        encoding="utf-8",
    )
    (proj / ".cargo" / "config.toml").write_text(
        f'[target.aarch64-unknown-linux-gnu]\nlinker = "{rust_lld}"\n'
        f'rustflags = ["-Z", "unstable-options", "-C", "linker-flavor=gnu-lld", '
        f'"-C", "relocation-model=static", "-C", "force-unwind-tables=yes", '
        f'"-C", "link-arg=-static", "-C", "link-arg=-e_start", "-C", "link-arg=-T{lds}"]\n',
        encoding="utf-8",
    )
    (proj / "src" / "main.rs").write_text(
        r'''#![no_std]
#![no_main]
extern crate alloc;
extern crate unwinding;

use core::alloc::{GlobalAlloc, Layout};
use core::arch::{asm, global_asm};
use core::ffi::c_void;
use core::panic::PanicInfo;
use core::sync::atomic::{AtomicUsize, Ordering};

struct BumpAlloc;
static mut HEAP: [u8; 262144] = [0; 262144];
static HEAP_OFF: AtomicUsize = AtomicUsize::new(0);

unsafe impl GlobalAlloc for BumpAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let align = layout.align();
        let size = layout.size();
        let mut cur = HEAP_OFF.load(Ordering::Relaxed);
        loop {
            let aligned = (cur + align - 1) & !(align - 1);
            let next = aligned + size;
            if next > 262144 { return core::ptr::null_mut(); }
            match HEAP_OFF.compare_exchange_weak(cur, next, Ordering::SeqCst, Ordering::Relaxed) {
                Ok(_) => return unsafe { (&raw mut HEAP as *mut u8).add(aligned) },
                Err(v) => cur = v,
            }
        }
    }
    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {}
}

#[global_allocator]
static ALLOC: BumpAlloc = BumpAlloc;

#[panic_handler]
fn on_panic(_info: &PanicInfo) -> ! { sys_exit(99); }

#[no_mangle] pub unsafe extern "C" fn getauxval(_t: usize) -> usize { 0 }
#[allow(warnings)] #[no_mangle]
pub unsafe extern "C" fn memcpy(d: *mut u8, s: *const u8, n: usize) -> *mut u8 {
    let mut i = 0; while i < n { *d.add(i) = *s.add(i); i += 1; } d
}
#[allow(warnings)] #[no_mangle]
pub unsafe extern "C" fn memmove(d: *mut u8, s: *const u8, n: usize) -> *mut u8 {
    if (d as usize) < (s as usize) {
        let mut i = 0; while i < n { *d.add(i) = *s.add(i); i += 1; }
    } else {
        let mut i = n; while i > 0 { i -= 1; *d.add(i) = *s.add(i); }
    }
    d
}
#[allow(warnings)] #[no_mangle]
pub unsafe extern "C" fn memset(d: *mut u8, c: i32, n: usize) -> *mut u8 {
    let mut i = 0; while i < n { *d.add(i) = c as u8; i += 1; } d
}
#[allow(warnings)] #[no_mangle]
pub unsafe extern "C" fn memcmp(a: *const u8, b: *const u8, n: usize) -> i32 {
    let mut i = 0;
    while i < n {
        let (va, vb) = (*a.add(i), *b.add(i));
        if va != vb { return (va as i32) - (vb as i32); }
        i += 1;
    }
    0
}
#[allow(warnings)] #[no_mangle]
pub unsafe extern "C" fn bcmp(a: *const u8, b: *const u8, n: usize) -> i32 { memcmp(a, b, n) }

fn sys_write(buf: &[u8]) {
    unsafe {
        asm!("mov x8, #64\nmov x0, #1\nsvc #0",
            in("x1") buf.as_ptr(), in("x2") buf.len(), out("x8") _, out("x0") _, options(nostack));
    }
}
fn sys_exit(code: usize) -> ! {
    unsafe { asm!("mov x8, #93\nsvc #0", in("x0") code, options(noreturn)); }
}
fn sys_mmap_anon(len: usize, prot: usize) -> usize {
    let ret: isize;
    unsafe {
        asm!("mov x8, #222\nsvc #0", inout("x0") 0usize => ret, in("x1") len, in("x2") prot,
            in("x3") 0x22usize, in("x4") (-1isize) as usize, in("x5") 0usize, out("x8") _, options(nostack));
    }
    assert!(ret > 0);
    ret as usize
}
fn sys_mprotect(addr: usize, len: usize, prot: usize) {
    let ret: isize;
    unsafe {
        asm!("mov x8, #226\nsvc #0", inout("x0") addr => ret, in("x1") len, in("x2") prot,
            out("x8") _, options(nostack));
    }
    assert_eq!(ret, 0);
}

global_asm!(
    ".text",
    ".balign 4",
    ".globl _start",
    ".type _start, %function",
    "_start:",
    ".cfi_startproc",
    ".cfi_undefined x30",
    "mov x0, sp",
    "bl rust_main",
    "brk #0x9",
    ".cfi_endproc",
    ".size _start, . - _start",

    ".balign 4",
    ".globl fiber_enter_a64",
    ".type fiber_enter_a64, %function",
    "fiber_enter_a64:",
    ".cfi_startproc",
    "stp x29, x30, [sp, #-96]!",
    ".cfi_def_cfa_offset 96",
    ".cfi_offset x29, -96",
    ".cfi_offset x30, -88",
    "stp x19, x20, [sp, #16]",
    "stp x21, x22, [sp, #32]",
    "stp x23, x24, [sp, #48]",
    "stp x25, x26, [sp, #64]",
    "stp x27, x28, [sp, #80]",
    "mov x9, sp",
    "str x9, [x0, #0]",
    "ldr x10, [x0, #8]",
    "mov sp, x10",
    "b .La64_restore_common",
    ".cfi_endproc",
    ".size fiber_enter_a64, . - fiber_enter_a64",

    ".balign 4",
    ".globl fiber_yield_a64",
    ".type fiber_yield_a64, %function",
    "fiber_yield_a64:",
    ".cfi_startproc",
    "stp x29, x30, [sp, #-96]!",
    ".cfi_def_cfa_offset 96",
    ".cfi_offset x29, -96",
    ".cfi_offset x30, -88",
    "stp x19, x20, [sp, #16]",
    "stp x21, x22, [sp, #32]",
    "stp x23, x24, [sp, #48]",
    "stp x25, x26, [sp, #64]",
    "stp x27, x28, [sp, #80]",
    "mov x9, sp",
    "str x9, [x0, #8]",
    "ldr x10, [x0, #0]",
    "mov sp, x10",
    ".La64_restore_common:",
    "ldp x19, x20, [sp, #16]",
    "ldp x21, x22, [sp, #32]",
    "ldp x23, x24, [sp, #48]",
    "ldp x25, x26, [sp, #64]",
    "ldp x27, x28, [sp, #80]",
    "ldp x29, x30, [sp], #96",
    "ret",
    ".cfi_endproc",
    ".size fiber_yield_a64, . - fiber_yield_a64",

    ".balign 4",
    ".globl fiber_root_good_a64",
    ".type fiber_root_good_a64, %function",
    "fiber_root_good_a64:",
    ".cfi_startproc",
    ".cfi_undefined x30",
    ".cfi_undefined x29",
    "mov x29, #0",
    "mov x0, x19",
    "blr x20",
    "brk #0x1",
    ".cfi_endproc",
    ".size fiber_root_good_a64, . - fiber_root_good_a64",

    ".balign 4",
    ".globl fiber_root_bad_sameval_a64",
    ".type fiber_root_bad_sameval_a64, %function",
    "fiber_root_bad_sameval_a64:",
    ".cfi_startproc",
    ".cfi_same_value x30",
    "mov x29, #0",
    "mov x0, x19",
    "blr x20",
    "brk #0x2",
    ".cfi_endproc",
    ".size fiber_root_bad_sameval_a64, . - fiber_root_bad_sameval_a64",

    ".balign 4",
    ".globl fiber_root_bad_deref_a64",
    ".type fiber_root_bad_deref_a64, %function",
    "fiber_root_bad_deref_a64:",
    ".cfi_startproc",
    ".cfi_offset x30, 0",
    "mov x29, #0",
    "mov x0, x19",
    "blr x20",
    "brk #0x3",
    ".cfi_endproc",
    ".size fiber_root_bad_deref_a64, . - fiber_root_bad_deref_a64",

    ".balign 4",
    ".globl fiber_root_omitted_a64",
    ".type fiber_root_omitted_a64, %function",
    "fiber_root_omitted_a64:",
    ".cfi_startproc",
    "mov x29, #0",
    "mov x0, x19",
    "blr x20",
    "brk #0x4",
    ".cfi_endproc",
    ".size fiber_root_omitted_a64, . - fiber_root_omitted_a64",
);

#[repr(C)]
struct FiberCtxA64 {
    parent_sp: usize,
    child_sp: usize,
    mode: u32,
    bt_frames: usize,
    same_pc_repeats: usize,
    drops_ran: usize,
}

unsafe extern "C" {
    fn fiber_enter_a64(ctx: *mut FiberCtxA64);
    fn fiber_yield_a64(ctx: *mut FiberCtxA64);
    fn fiber_root_good_a64();
    fn fiber_root_bad_sameval_a64();
    fn fiber_root_bad_deref_a64();
    fn fiber_root_omitted_a64();
}

use unwinding::abi::{UnwindContext, UnwindReasonCode, _Unwind_Backtrace, _Unwind_GetIP};

struct BtState { frames: usize, last_ip: usize, repeats: usize }

extern "C" fn bt_callback(uw_ctx: &UnwindContext<'_>, arg: *mut c_void) -> UnwindReasonCode {
    let st = unsafe { &mut *(arg as *mut BtState) };
    let ip = _Unwind_GetIP(uw_ctx);
    st.frames += 1;
    if ip == st.last_ip && ip != 0 { st.repeats += 1; }
    st.last_ip = ip;
    if st.frames >= 25 { UnwindReasonCode::NORMAL_STOP } else { UnwindReasonCode::NO_REASON }
}

struct DropGuard(*mut usize);
impl Drop for DropGuard { fn drop(&mut self) { unsafe { *self.0 += 1; } } }

extern "C-unwind" fn fiber_body_a64(ctx_ptr: *mut FiberCtxA64) -> ! {
    let ctx = unsafe { &mut *ctx_ptr };
    match ctx.mode {
        0 => {
            let mut st = BtState { frames: 0, last_ip: 0, repeats: 0 };
            let _ = _Unwind_Backtrace(bt_callback, (&raw mut st) as *mut c_void);
            ctx.bt_frames = st.frames;
            ctx.same_pc_repeats = st.repeats;
            unsafe { fiber_yield_a64(ctx_ptr) };
            loop {}
        }
        1 => {
            let res = unwinding::panic::catch_unwind(|| {
                let _g = DropGuard(&raw mut ctx.drops_ran);
                let _ = unwinding::panic::begin_panic(alloc::boxed::Box::new(42u64));
            });
            assert!(res.is_err());
            unsafe { fiber_yield_a64(ctx_ptr) };
            loop {}
        }
        _ => {
            let _g = DropGuard(&raw mut ctx.drops_ran);
            let code = unwinding::panic::begin_panic(alloc::boxed::Box::new(99u64));
            sys_exit(50 + code.0 as usize);
        }
    }
}

fn run_case(root_fn: usize, mode: u32) -> (usize, usize, usize) {
    let page = 4096usize;
    let raw = sys_mmap_anon(page * 18, 0);
    let stack_base = raw + page;
    sys_mprotect(stack_base, page * 16, 3);
    let stack_top = stack_base + page * 16;
    let init_sp = stack_top - 96;
    let mut ctx = FiberCtxA64 { parent_sp: 0, child_sp: init_sp, mode, bt_frames: 0, same_pc_repeats: 0, drops_ran: 0 };
    let words: [usize; 12] = [
        0, root_fn, (&raw mut ctx) as usize, fiber_body_a64 as *const () as usize,
        0, 0, 0, 0, 0, 0, 0, 0,
    ];
    unsafe {
        core::ptr::copy_nonoverlapping(words.as_ptr(), init_sp as *mut usize, 12);
        fiber_enter_a64(&raw mut ctx);
    }
    (ctx.bt_frames, ctx.same_pc_repeats, ctx.drops_ran)
}

#[no_mangle]
pub unsafe extern "C" fn rust_main(entry_sp: usize) -> ! {
    let argc = *(entry_sp as *const usize);
    let sel: u8 = if argc >= 2 { *(*((entry_sp + 16) as *const *const u8)) } else { b'1' };
    match sel {
        b'1' => {
            let (f, rep, _) = run_case(fiber_root_good_a64 as *const () as usize, 0);
            assert_eq!(rep, 0);
            sys_write(b"A64_GOOD_BT_OK\n");
            sys_exit(f);
        }
        b'2' => {
            let (f, rep, _) = run_case(fiber_root_bad_sameval_a64 as *const () as usize, 0);
            assert_eq!(f, 25);
            sys_write(b"A64_BAD_SAMEVAL_LOOP\n");
            sys_exit(rep);
        }
        b'3' => {
            let _ = run_case(fiber_root_bad_deref_a64 as *const () as usize, 0);
            sys_exit(0);
        }
        b'4' => {
            let (_, _, drops) = run_case(fiber_root_good_a64 as *const () as usize, 1);
            assert_eq!(drops, 1);
            sys_write(b"A64_GOOD_CATCH_OK\n");
            sys_exit(0);
        }
        b'5' => {
            let _ = run_case(fiber_root_good_a64 as *const () as usize, 2);
            sys_exit(0);
        }
        b'6' => {
            let _ = run_case(fiber_root_bad_sameval_a64 as *const () as usize, 2);
            sys_exit(0);
        }
        b'7' => {
            let _ = run_case(fiber_root_bad_deref_a64 as *const () as usize, 2);
            sys_exit(0);
        }
        _ => {
            let (f, rep, _) = run_case(fiber_root_omitted_a64 as *const () as usize, 0);
            assert_eq!(rep, 0);
            sys_write(b"A64_UNWINDING_CRATE_OMITTED_TREATED_AS_ZERO\n");
            sys_exit(f);
        }
    }
}
''',
        encoding="utf-8",
    )

    build = run_cmd(
        ["cargo", "+1.99.1", "build", "--offline", "--release", "--target", "aarch64-unknown-linux-gnu"],
        cwd=str(proj),
        env={"RUSTC_BOOTSTRAP": "1"},
        timeout=60.0,
    )
    assert build.returncode == 0, build.stderr
    exe = proj / "target" / "aarch64-unknown-linux-gnu" / "release" / "a64_uw"
    dd = run_cmd(["llvm-dwarfdump", "--eh-frame", str(exe)]).stdout
    has_undef_w30 = "DW_CFA_undefined: W30" in dd

    runs: dict[str, Any] = {}
    for sel, name, tout in [
        ("1", "good_bt", 5.0),
        ("2", "bad_sameval_bt_loop", 5.0),
        ("3", "bad_deref_bt", 5.0),
        ("4", "good_catch", 5.0),
        ("5", "good_uncaught_end_of_stack", 5.0),
        ("6", "bad_sameval_uncaught_phase1_hang", 1.2),
        ("7", "bad_deref_uncaught", 5.0),
        ("8", "unwinding_crate_omitted_x30_treated_as_zero", 5.0),
    ]:
        try:
            r = run_cmd([qemu, str(exe), sel], timeout=tout)
            runs[name] = {"timed_out": False, "exit_code": r.returncode, "stdout": r.stdout.strip()}
        except subprocess.TimeoutExpired:
            runs[name] = {"timed_out": True, "exit_code": None, "stdout": ""}
    return {"eh_frame_has_dw_cfa_undefined_x30": has_undef_w30, "runs": runs}


# ---------------------------------------------------------------------------
# Suite 2: ELF64 global_asm! & GCC .S Multi-Entry / st_size=0 / SWECG
# ---------------------------------------------------------------------------


def parse_elf64_symbols_and_sections(obj_path: Path) -> dict[str, Any]:
    raw = obj_path.read_bytes()
    assert raw[:4] == b"\x7fELF" and raw[4] == 2 and raw[5] == 1
    e_shoff = struct.unpack_from("<Q", raw, 40)[0]
    e_shentsize, e_shnum, e_shstrndx = struct.unpack_from("<HHH", raw, 58)
    shdrs = []
    for i in range(e_shnum):
        off = e_shoff + i * e_shentsize
        sh_name, sh_type, sh_flags, _, sh_offset, sh_size, sh_link, _, _, sh_entsize = (
            struct.unpack_from("<IIQQQQIIQQ", raw, off)
        )
        shdrs.append(
            {
                "idx": i,
                "sh_name": sh_name,
                "type": sh_type,
                "flags": sh_flags,
                "size": sh_size,
                "link": sh_link,
                "entsize": sh_entsize,
                "data": raw[sh_offset : sh_offset + sh_size],
            }
        )
    shstr = shdrs[e_shstrndx]["data"]
    for s in shdrs:
        end = shstr.find(b"\x00", s["sh_name"])
        s["name"] = shstr[s["sh_name"] : end].decode("utf-8", errors="replace")

    syms = []
    for s in shdrs:
        if s["type"] == 2:
            strtab = shdrs[s["link"]]["data"]
            for off in range(0, s["size"], s["entsize"]):
                st_name, st_info, st_other, st_shndx, st_value, st_size = struct.unpack_from(
                    "<IBBHQQ", s["data"], off
                )
                end = strtab.find(b"\x00", st_name)
                syms.append(
                    {
                        "name": strtab[st_name:end].decode("utf-8", errors="replace"),
                        "bind": st_info >> 4,
                        "type": st_info & 0xF,
                        "vis": st_other & 0x3,
                        "shndx": st_shndx,
                        "value": st_value,
                        "size": st_size,
                    }
                )
    return {"shdrs": shdrs, "syms": syms}


def decode_probe_x64_cfg(code: bytes, entry_offsets: list[int]) -> dict[str, Any]:
    worklist = list(entry_offsets)
    visited: dict[int, int] = {}
    exec_bytes: set[int] = set()
    rodata_reads: set[int] = set()
    in_edges: dict[int, set[int]] = {e: set() for e in entry_offsets}
    errors: list[str] = []

    while worklist:
        pc = worklist.pop()
        if pc in visited:
            continue
        if pc < 0 or pc >= len(code):
            errors.append(f"out_of_bounds_pc:{pc}")
            continue
        b0 = code[pc]
        if code[pc : pc + 3] in (b"\x48\x8d\x47", b"\x48\x83\xc7", b"\x48\x6b\xc7"):
            ln, succs = 4, [pc + 4]
        elif code[pc : pc + 3] == b"\x48\x81\xc7":
            ln, succs = 7, [pc + 7]
        elif code[pc : pc + 3] in (b"\x48\x01\xf8", b"\x48\x89\xf8"):
            ln, succs = 3, [pc + 3]
        elif code[pc : pc + 3] == b"\x48\x03\x05":
            ln, succs = 7, [pc + 7]
            disp = struct.unpack_from("<i", code, pc + 3)[0]
            t_off = pc + 7 + disp
            for k in range(t_off, t_off + 8):
                rodata_reads.add(k)
        elif b0 == 0xEB:
            ln = 2
            succs = [pc + 2 + struct.unpack_from("<b", code, pc + 1)[0]]
        elif b0 == 0xE9:
            ln = 5
            succs = [pc + 5 + struct.unpack_from("<i", code, pc + 1)[0]]
        elif b0 == 0x74:
            ln = 2
            succs = [pc + 2, pc + 2 + struct.unpack_from("<b", code, pc + 1)[0]]
        elif code[pc : pc + 2] == b"\x85\xf6":
            ln, succs = 2, [pc + 2]
        elif b0 == 0xC3:
            ln, succs = 1, []
        elif b0 == 0x90:
            ln, succs = 1, [pc + 1]
        else:
            errors.append(f"invalid_or_data_opcode_at_0x{pc:x}:0x{b0:02x}")
            continue

        visited[pc] = ln
        for b in range(pc, pc + ln):
            exec_bytes.add(b)
        for s in succs:
            in_edges.setdefault(s, set()).add(pc)
            if s not in visited:
                worklist.append(s)

    cutpoints = sorted(pc for pc, preds in in_edges.items() if pc in entry_offsets or len(preds) > 1)
    return {
        "visited_insn_count": len(visited),
        "exec_byte_count": len(exec_bytes),
        "rodata_byte_count": len(rodata_reads),
        "exec_rodata_disjoint": len(exec_bytes & rodata_reads) == 0,
        "cutpoints_hex": [f"0x{c:x}" for c in cutpoints],
        "decode_errors": errors,
    }


def run_global_asm_and_perlasm_suite(td: str) -> dict[str, Any]:
    rs_file = Path(td) / "gasm_probe.rs"
    obj_file = Path(td) / "gasm_probe.o"
    exe_file = Path(td) / "gasm_probe"

    rs_file.write_text(
        r'''use std::arch::{asm, global_asm, naked_asm};

#[no_mangle] #[inline(never)]
pub extern "C" fn regular_asm_fn(mut x: u64) -> u64 {
    unsafe { asm!("add {0}, 1", inout(reg) x, options(pure, nomem, nostack)); }
    x
}

#[unsafe(naked)] #[no_mangle]
pub unsafe extern "C" fn naked_single_fn(x: u64) -> u64 {
    naked_asm!("lea rax, [rdi + 2]", "ret")
}

global_asm!(
    ".section .text.gasm_cluster,\"ax\",@progbits",
    ".globl gasm_nosize_fast",
    ".type gasm_nosize_fast, @function",
    "gasm_nosize_fast:",
    "add rdi, 10",

    ".globl gasm_nosize_common",
    ".type gasm_nosize_common, @function",
    "gasm_nosize_common:",
    "add rdi, 5",
    "jmp .Lshared_tail",

    ".globl gasm_sized_with_shared_tail",
    ".type gasm_sized_with_shared_tail, @function",
    "gasm_sized_with_shared_tail:",
    "add rdi, 20",
    "jmp .Lshared_tail",
    ".size gasm_sized_with_shared_tail, . - gasm_sized_with_shared_tail",

    ".Lshared_tail:",
    "imul rax, rdi, 2",
    "add rax, qword ptr [rip + .Linline_const]",
    "ret",

    ".balign 8",
    ".Linline_const:",
    ".quad 0x0000000000000064",

    ".globl gasm_two_entry_enter",
    ".type gasm_two_entry_enter, @function",
    "gasm_two_entry_enter:",
    "test esi, esi",
    "je .Lepilogue_in_enter",
    "add rdi, 100",
    ".Lepilogue_in_enter:",
    "mov rax, rdi",
    "ret",
    ".size gasm_two_entry_enter, . - gasm_two_entry_enter",

    ".globl gasm_two_entry_alt",
    ".type gasm_two_entry_alt, @function",
    "gasm_two_entry_alt:",
    "add rdi, 300",
    "jmp .Lepilogue_in_enter",
);

unsafe extern "C" {
    fn gasm_nosize_fast(x: u64) -> u64;
    fn gasm_nosize_common(x: u64) -> u64;
    fn gasm_sized_with_shared_tail(x: u64) -> u64;
    fn gasm_two_entry_enter(x: u64, flag: u32) -> u64;
    fn gasm_two_entry_alt(x: u64) -> u64;
}

fn main() {
    let r = unsafe {
        (
            regular_asm_fn(7),
            naked_single_fn(7),
            gasm_nosize_fast(7),
            gasm_nosize_common(7),
            gasm_sized_with_shared_tail(7),
            gasm_two_entry_enter(7, 1),
            gasm_two_entry_alt(7),
        )
    };
    assert_eq!(r, (8, 9, 144, 124, 154, 107, 307));
    println!("GASM_EXEC_OK {:?}", r);
}
''',
        encoding="utf-8",
    )

    assert run_cmd(["rustc", "+nightly", "-C", "opt-level=2", "-C", "codegen-units=1", "--emit=obj", str(rs_file), "-o", str(obj_file)]).returncode == 0
    assert run_cmd(["rustc", "+nightly", "-C", "opt-level=2", "-C", "codegen-units=1", str(rs_file), "-o", str(exe_file)]).returncode == 0
    exec_run = run_cmd([str(exe_file)])
    assert exec_run.returncode == 0

    elf = parse_elf64_symbols_and_sections(obj_file)
    sec_by_name = {s["name"]: s for s in elf["shdrs"]}
    cluster_sec = sec_by_name[".text.gasm_cluster"]
    code = cluster_sec["data"]
    cluster_syms = sorted(
        [s for s in elf["syms"] if s["shndx"] == cluster_sec["idx"] and s["bind"] == 1],
        key=lambda x: x["value"],
    )

    lifter_a = {}
    for s in cluster_syms:
        sl = code[s["value"] : s["value"] + s["size"]]
        if len(sl) == 0:
            lifter_a[s["name"]] = "BUG_ZERO_BYTE_SLICE_VACUOUS"
        else:
            r = decode_probe_x64_cfg(sl, [0])
            lifter_a[s["name"]] = "OK" if not r["decode_errors"] else f"BUG_{r['decode_errors'][0]}"

    lifter_b = {}
    for idx, s in enumerate(cluster_syms):
        end_off = cluster_syms[idx + 1]["value"] if idx + 1 < len(cluster_syms) else len(code)
        sl = code[s["value"] : end_off]
        r = decode_probe_x64_cfg(sl, [0])
        lifter_b[s["name"]] = {
            "slice_len": len(sl),
            "entry_cfg_errors": r["decode_errors"],
        }

    swecg = decode_probe_x64_cfg(code, [s["value"] for s in cluster_syms])

    # Also assemble a GCC 15.2.0 `.S` specimen mirroring Perlasm (`aesni-xts-avx512.S` + `trampoline-x86_64.S`)
    gas_s = Path(td) / "perlasm_specimen.S"
    gas_o = Path(td) / "perlasm_specimen.o"
    gas_s.write_text(
        ".text\n"
        ".globl perlasm_xts_enc_nosize\n"
        ".type perlasm_xts_enc_nosize, @function\n"
        "perlasm_xts_enc_nosize:\n"
        "  addq $10, %rdi\n"
        "  jmp .Lperlasm_shared_tail\n"
        ".globl perlasm_xts_dec_nosize\n"
        ".type perlasm_xts_dec_nosize, @function\n"
        "perlasm_xts_dec_nosize:\n"
        "  addq $20, %rdi\n"
        ".globl perlasm_interior_unwind_marker\n"
        "perlasm_interior_unwind_marker:\n"
        "  jmp .Lperlasm_shared_tail\n"
        ".Lperlasm_shared_tail:\n"
        "  movq %rdi, %rax\n"
        "  ret\n",
        encoding="utf-8",
    )
    assert run_cmd(["gcc", "-c", str(gas_s), "-o", str(gas_o)]).returncode == 0
    gas_elf = parse_elf64_symbols_and_sections(gas_o)
    gas_syms = {
        s["name"]: {"st_value": s["value"], "st_size": s["size"], "type": s["type"]}
        for s in gas_elf["syms"]
        if s["bind"] == 1
    }

    return {
        "runtime_stdout": exec_run.stdout.strip(),
        "rustc_global_asm_cluster_size": len(code),
        "rustc_symbols": {
            s["name"]: {"st_value": s["value"], "st_size": s["size"]}
            for s in elf["syms"]
            if s["name"] in {
                "regular_asm_fn",
                "naked_single_fn",
                "gasm_nosize_fast",
                "gasm_nosize_common",
                "gasm_sized_with_shared_tail",
                "gasm_two_entry_enter",
                "gasm_two_entry_alt",
            }
        },
        "gcc_perlasm_specimen_symbols": gas_syms,
        "naive_lifter_a_st_size": lifter_a,
        "naive_lifter_b_next_sym": lifter_b,
        "swecg_lifter": swecg,
    }


# ---------------------------------------------------------------------------
# Suite 3: Temporally Disjoint C Ops-Table Vtables (GCC 15.2.0 + Miri TB)
# ---------------------------------------------------------------------------


def run_foreign_ownable_vtable_suite(td: str) -> dict[str, Any]:
    c_file = Path(td) / "vfs_harness.c"
    rs_file = Path(td) / "driver_fops.rs"
    c_obj = Path(td) / "vfs_harness.o"
    exe = Path(td) / "vfs_probe"

    c_file.write_text(
        r'''#include <stdint.h>
#include <stddef.h>

#define FMODE_OPENED 0x1u

struct sim_file;
struct sim_file_operations {
    int (*open)(struct sim_file *f);
    long (*unlocked_ioctl)(struct sim_file *f, unsigned int cmd, unsigned long arg);
    int (*release)(struct sim_file *f);
};

struct sim_file {
    uint32_t f_mode;
    uint32_t f_flags;
    void *private_data;
    const struct sim_file_operations *f_op;
};

int sim_vfs_open(struct sim_file *f, uint32_t flags, const struct sim_file_operations *fops) {
    f->f_mode = 0;
    f->f_flags = flags;
    f->private_data = NULL;
    f->f_op = fops;
    int err = f->f_op->open(f);
    if (err != 0) {
        return err;
    }
    f->f_mode |= FMODE_OPENED;
    return 0;
}

void sim_vfs_fput(struct sim_file *f) {
    if (!(f->f_mode & FMODE_OPENED)) {
        return;
    }
    if (f->f_op->release) {
        f->f_op->release(f);
    }
    f->f_mode &= ~FMODE_OPENED;
}

long c_reentrant_observer(struct sim_file *f) {
    return f->f_op->unlocked_ioctl(f, 2, 100);
}
''',
        encoding="utf-8",
    )

    rs_file.write_text(
        r'''use std::cell::Cell;
use std::ffi::{c_int, c_long, c_uint, c_ulong, c_void};
use std::sync::atomic::{AtomicUsize, Ordering};

#[repr(C)]
pub struct SimFileOperations {
    pub open: unsafe extern "C" fn(*mut SimFile) -> c_int,
    pub unlocked_ioctl: unsafe extern "C" fn(*mut SimFile, c_uint, c_ulong) -> c_long,
    pub release: unsafe extern "C" fn(*mut SimFile) -> c_int,
}

#[repr(C)]
pub struct SimFile {
    pub f_mode: u32,
    pub f_flags: u32,
    pub private_data: *mut c_void,
    pub f_op: *const SimFileOperations,
}

unsafe extern "C" {
    fn sim_vfs_open(f: *mut SimFile, flags: u32, fops: *const SimFileOperations) -> c_int;
    fn sim_vfs_fput(f: *mut SimFile);
    fn c_reentrant_observer(f: *mut SimFile) -> c_long;
}

static LIVE_HANDLES: AtomicUsize = AtomicUsize::new(0);
static DROP_CALLS: AtomicUsize = AtomicUsize::new(0);

struct RawMutDev { accum: u64 }
impl Drop for RawMutDev {
    fn drop(&mut self) {
        DROP_CALLS.fetch_add(1, Ordering::SeqCst);
        LIVE_HANDLES.fetch_sub(1, Ordering::SeqCst);
    }
}

unsafe extern "C" fn buggy_open(f: *mut SimFile) -> c_int {
    LIVE_HANDLES.fetch_add(1, Ordering::SeqCst);
    (*f).private_data = Box::into_raw(Box::new(RawMutDev { accum: 10 })) as *mut c_void;
    if ((*f).f_flags & 0x4000) != 0 { return -22; }
    0
}

unsafe extern "C" fn buggy_ioctl(f: *mut SimFile, cmd: c_uint, arg: c_ulong) -> c_long {
    let st: &mut RawMutDev = &mut *((*f).private_data as *mut RawMutDev);
    match cmd {
        1 => {
            let cached = st.accum;
            let _ = c_reentrant_observer(f);
            st.accum = cached + arg;
            st.accum as c_long
        }
        2 => { st.accum += arg; st.accum as c_long }
        _ => -22,
    }
}

unsafe extern "C" fn buggy_release(f: *mut SimFile) -> c_int {
    drop(Box::from_raw((*f).private_data as *mut RawMutDev));
    0
}

static BUGGY_FOPS: SimFileOperations = SimFileOperations {
    open: buggy_open, unlocked_ioctl: buggy_ioctl, release: buggy_release,
};

struct DevState {
    accum: Cell<u64>,
    loan_state: Cell<i32>,
}
impl DevState {
    fn new(init: u64) -> Box<Self> {
        LIVE_HANDLES.fetch_add(1, Ordering::SeqCst);
        Box::new(Self { accum: Cell::new(init), loan_state: Cell::new(0) })
    }
}
impl Drop for DevState {
    fn drop(&mut self) {
        DROP_CALLS.fetch_add(1, Ordering::SeqCst);
        LIVE_HANDLES.fetch_sub(1, Ordering::SeqCst);
    }
}

unsafe extern "C" fn sound_open(f: *mut SimFile) -> c_int {
    if ((*f).f_flags & 0x4000) != 0 { return -22; }
    (*f).private_data = Box::into_raw(DevState::new(10)) as *mut c_void;
    0
}

unsafe extern "C" fn sound_ioctl(f: *mut SimFile, cmd: c_uint, arg: c_ulong) -> c_long {
    let st: &DevState = &*((*f).private_data as *const DevState);
    match cmd {
        1 => {
            let s = st.loan_state.get();
            if s < 0 { return -16; }
            st.loan_state.set(s + 1);
            let _ = c_reentrant_observer(f);
            st.accum.set(st.accum.get() + arg);
            st.loan_state.set(st.loan_state.get() - 1);
            st.accum.get() as c_long
        }
        2 => {
            let s = st.loan_state.get();
            if s < 0 { return -16; }
            st.loan_state.set(s + 1);
            st.accum.set(st.accum.get() + arg);
            st.loan_state.set(st.loan_state.get() - 1);
            st.accum.get() as c_long
        }
        3 => {
            if st.loan_state.get() != 0 { return -16; }
            st.loan_state.set(-1);
            let nested_rc = c_reentrant_observer(f);
            st.loan_state.set(0);
            nested_rc
        }
        _ => -22,
    }
}

unsafe extern "C" fn sound_release(f: *mut SimFile) -> c_int {
    let raw = (*f).private_data as *mut DevState;
    if raw.is_null() { return -22; }
    assert_eq!((*raw).loan_state.get(), 0);
    (*f).private_data = std::ptr::null_mut();
    drop(Box::from_raw(raw));
    0
}

static SOUND_FOPS: SimFileOperations = SimFileOperations {
    open: sound_open, unlocked_ioctl: sound_ioctl, release: sound_release,
};

fn main() {
    unsafe {
        LIVE_HANDLES.store(0, Ordering::SeqCst);
        DROP_CALLS.store(0, Ordering::SeqCst);
        let mut f1 = std::mem::zeroed::<SimFile>();
        let rc1 = sim_vfs_open(&raw mut f1, 0x4000, &raw const BUGGY_FOPS);
        sim_vfs_fput(&raw mut f1);
        let bug1_leaked = LIVE_HANDLES.load(Ordering::SeqCst);
        let bug1_drops = DROP_CALLS.load(Ordering::SeqCst);
        drop(Box::from_raw(f1.private_data as *mut RawMutDev));

        LIVE_HANDLES.store(0, Ordering::SeqCst);
        DROP_CALLS.store(0, Ordering::SeqCst);
        let mut f2 = std::mem::zeroed::<SimFile>();
        assert_eq!(sim_vfs_open(&raw mut f2, 0x4000, &raw const SOUND_FOPS), -22);
        sim_vfs_fput(&raw mut f2);
        assert_eq!(LIVE_HANDLES.load(Ordering::SeqCst), 0);

        assert_eq!(sim_vfs_open(&raw mut f2, 0, &raw const SOUND_FOPS), 0);
        let v_shared = (SOUND_FOPS.unlocked_ioctl)(&raw mut f2, 1, 5);
        let v_mut_ebusy = (SOUND_FOPS.unlocked_ioctl)(&raw mut f2, 3, 0);
        sim_vfs_fput(&raw mut f2);
        let sound_live_after = LIVE_HANDLES.load(Ordering::SeqCst);
        let sound_drops = DROP_CALLS.load(Ordering::SeqCst);
        let second_rel = (SOUND_FOPS.release)(&raw mut f2);

        println!(
            "{{\"bug1_open_rc\":{},\"bug1_leaked_handles\":{},\"bug1_drops\":{},\"sound_reentrant_shared_val\":{},\"sound_reentrant_mut_ebusy\":{},\"sound_live_after_fput\":{},\"sound_drops\":{},\"sound_second_release_rc\":{}}}",
            rc1, bug1_leaked, bug1_drops, v_shared, v_mut_ebusy, sound_live_after, sound_drops, second_rel
        );
    }
}
''',
        encoding="utf-8",
    )

    assert run_cmd(["gcc", "-O2", "-Wall", "-Wextra", "-c", str(c_file), "-o", str(c_obj)]).returncode == 0
    assert run_cmd(["rustc", "+nightly", "-C", "opt-level=2", str(rs_file), "-C", f"link-arg={c_obj}", "-o", str(exe)]).returncode == 0
    native_out = json.loads(run_cmd([str(exe)]).stdout.strip())

    mproj = Path(td) / "miri_vtable"
    (mproj / "src").mkdir(parents=True)
    (mproj / "Cargo.toml").write_text(
        '[package]\nname = "miri_vtable"\nversion = "0.1.0"\nedition = "2021"\n',
        encoding="utf-8",
    )
    (mproj / "src" / "lib.rs").write_text(
        r'''use std::cell::Cell;
use std::ffi::c_void;

struct SimFile { f_mode: u32, f_flags: u32, private_data: *mut c_void }

#[test]
fn v1_miri_open_error_after_into_foreign_leaks_allocation() {
    let mut f = SimFile { f_mode: 0, f_flags: 0x4000, private_data: std::ptr::null_mut() };
    f.private_data = Box::into_raw(Box::new(42u64)) as *mut c_void;
    let rc = if f.f_flags & 0x4000 != 0 { -22 } else { f.f_mode |= 1; 0 };
    assert_eq!(rc, -22);
    if f.f_mode & 1 != 0 {
        unsafe { drop(Box::from_raw(f.private_data as *mut u64)); }
    }
}

#[test]
fn v2_miri_reentrant_ioctl_borrow_mut_aliasing_ub() {
    unsafe fn ioctl_buggy(f: *mut SimFile, depth: u32) {
        let st: &mut u64 = unsafe { &mut *((*f).private_data as *mut u64) };
        *st += 1;
        if depth == 0 { unsafe { ioctl_buggy(f, 1) }; }
        *st += 10;
    }
    let mut f = SimFile { f_mode: 1, f_flags: 0, private_data: Box::into_raw(Box::new(0u64)) as *mut c_void };
    unsafe {
        ioctl_buggy(&raw mut f, 0);
        drop(Box::from_raw(f.private_data as *mut u64));
    }
}

#[test]
fn v3_miri_double_release_from_foreign_uaf_ub() {
    let mut f = SimFile { f_mode: 1, f_flags: 0, private_data: Box::into_raw(Box::new(77u64)) as *mut c_void };
    unsafe {
        drop(Box::from_raw(f.private_data as *mut u64));
        drop(Box::from_raw(f.private_data as *mut u64));
    }
}

#[test]
fn v4_miri_sound_foreign_ownable_lifecycle_passes() {
    struct GuardedDev { val: Cell<u64>, loans: Cell<i32> }
    unsafe fn sound_ioctl(f: *mut SimFile, depth: u32) -> i32 {
        let dev: &GuardedDev = unsafe { &*((*f).private_data as *const GuardedDev) };
        let l = dev.loans.get();
        if l < 0 { return -16; }
        dev.loans.set(l + 1);
        dev.val.set(dev.val.get() + 1);
        if depth == 0 { let _ = unsafe { sound_ioctl(f, 1) }; }
        dev.loans.set(dev.loans.get() - 1);
        0
    }
    let mut f = SimFile {
        f_mode: 1, f_flags: 0,
        private_data: Box::into_raw(Box::new(GuardedDev { val: Cell::new(10), loans: Cell::new(0) })) as *mut c_void,
    };
    unsafe {
        assert_eq!(sound_ioctl(&raw mut f, 0), 0);
        let raw = f.private_data as *mut GuardedDev;
        f.private_data = std::ptr::null_mut();
        let reclaimed = Box::from_raw(raw);
        assert_eq!(reclaimed.val.get(), 12);
    }
}
''',
        encoding="utf-8",
    )

    miri_vtable = {}
    for tname in [
        "v1_miri_open_error_after_into_foreign_leaks_allocation",
        "v2_miri_reentrant_ioctl_borrow_mut_aliasing_ub",
        "v3_miri_double_release_from_foreign_uaf_ub",
        "v4_miri_sound_foreign_ownable_lifecycle_passes",
    ]:
        cp = run_cmd(
            ["cargo", "+nightly", "miri", "test", "--", "--exact", tname],
            cwd=str(mproj),
            env={"MIRIFLAGS": "-Zmiri-tree-borrows"},
            timeout=60.0,
        )
        diag = ""
        for line in (cp.stderr + "\n" + cp.stdout).splitlines():
            if any(k in line for k in ["Undefined Behavior:", "memory leaked", "dangling", "is forbidden"]):
                diag = line.strip()
                break
        miri_vtable[tname] = {"exit_code": cp.returncode, "passed": cp.returncode == 0, "diagnostic": diag}

    return {"native_gcc_c_rust_vfs": native_out, "miri_vtable": miri_vtable}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", default="", help="Optional JSON output path")
    args = parser.parse_args()

    with tempfile.TemporaryDirectory() as td:
        results = {
            "suite_1a_miri_dormant_stack_tree_borrows": run_miri_dormant_stack_suite(td),
            "suite_1b_x86_64_trampoline_cfi_undefined": run_x86_64_trampoline_cfi_suite(td),
            "suite_1c_aarch64_qemu_trampoline_cfi_undefined": run_aarch64_qemu_trampoline_cfi_suite(td),
            "suite_2_global_asm_and_perlasm_swecg": run_global_asm_and_perlasm_suite(td),
            "suite_3_foreign_ownable_c_vtables": run_foreign_ownable_vtable_suite(td),
        }

    rendered = json.dumps(results, indent=2, sort_keys=True) + "\n"
    if args.out:
        Path(args.out).write_text(rendered, encoding="utf-8")
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
