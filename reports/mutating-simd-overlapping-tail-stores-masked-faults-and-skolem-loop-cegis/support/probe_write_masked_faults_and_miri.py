#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Reproducible empirical oracle for write-side SIMD masked-store fault
asymmetry, rustc +avx2 vs +avx512bw lowering, QEMU AArch64 SVE/MTE write
granules, and Miri Tree Borrows vs Stacked Borrows aligned RMW slack-writeback
hazards.

All transient builds execute strictly inside tempfile.TemporaryDirectory().
"""

from __future__ import annotations

import glob
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time
from typing import Any

sys.dont_write_bytecode = True

HERE = Path(__file__).resolve().parent


X86_HW_ORACLE_RS = r"""
#![allow(unused_unsafe)]
use core::arch::asm;
use core::arch::x86_64::*;
use core::hint::black_box;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::thread;

const PROT_NONE: i32 = 0x0;
const PROT_READ: i32 = 0x1;
const PROT_WRITE: i32 = 0x2;
const MAP_PRIVATE: i32 = 0x02;
const MAP_ANONYMOUS: i32 = 0x20;
const SIGSEGV: i32 = 11;
const SIGBUS: i32 = 7;
const SA_SIGINFO: i32 = 0x00000004;
const SA_NODEFER: i32 = 0x40000000;

#[repr(C)]
struct SigInfo {
    si_signo: i32,
    si_errno: i32,
    si_code: i32,
    _pad0: i32,
    si_addr: usize,
    _pad: [u8; 104],
}

type JmpBuf = [u64; 32];

unsafe extern "C" {
    fn mmap(addr: *mut u8, len: usize, prot: i32, flags: i32, fd: i32, off: isize) -> *mut u8;
    fn munmap(addr: *mut u8, len: usize) -> i32;
    fn mprotect(addr: *mut u8, len: usize, prot: i32) -> i32;
    fn sigaction(sig: i32, act: *const LibcSigAction, old: *mut LibcSigAction) -> i32;
    fn __sigsetjmp(env: *mut JmpBuf, savemask: i32) -> i32;
    fn siglongjmp(env: *mut JmpBuf, val: i32) -> !;
}

#[repr(C)]
struct LibcSigAction {
    sa_sigaction: usize,
    sa_mask: [u64; 16],
    sa_flags: i32,
    sa_restorer: usize,
}

static mut JMP_ENV: JmpBuf = [0; 32];
static mut LAST_SIG: i32 = 0;
static mut LAST_CODE: i32 = 0;
static mut LAST_ADDR: usize = 0;

unsafe extern "C" fn handler(sig: i32, info: *const SigInfo, _uctx: *mut u8) {
    unsafe {
        LAST_SIG = sig;
        if !info.is_null() {
            LAST_CODE = (*info).si_code;
            LAST_ADDR = (*info).si_addr;
        } else {
            LAST_CODE = -1;
            LAST_ADDR = 0;
        }
        siglongjmp(&raw mut JMP_ENV, 1);
    }
}

fn install_handlers() {
    unsafe {
        let act = LibcSigAction {
            sa_sigaction: handler as *const () as usize,
            sa_mask: [0; 16],
            sa_flags: SA_SIGINFO | SA_NODEFER,
            sa_restorer: 0,
        };
        assert_eq!(sigaction(SIGSEGV, &act, core::ptr::null_mut()), 0);
        assert_eq!(sigaction(SIGBUS, &act, core::ptr::null_mut()), 0);
    }
}

fn trap_call(name: &str, base_ref: usize, f: impl FnOnce()) -> String {
    unsafe {
        LAST_SIG = 0;
        LAST_CODE = 0;
        LAST_ADDR = 0;
        let jumped = __sigsetjmp(&raw mut JMP_ENV, 1);
        if jumped == 0 {
            f();
            format!(
                "{{\"case\":\"{}\",\"faulted\":false,\"sig\":0,\"si_code\":0,\"rel_addr\":null}}",
                name
            )
        } else {
            let (sig, code, addr) = (LAST_SIG, LAST_CODE, LAST_ADDR);
            let rel = if addr >= base_ref && addr < base_ref + 6 * 4096 {
                format!("{}", addr - base_ref)
            } else {
                format!("\"0x{:x}\"", addr)
            };
            format!(
                "{{\"case\":\"{}\",\"faulted\":true,\"sig\":{},\"si_code\":{},\"rel_addr\":{}}}",
                name, sig, code, rel
            )
        }
    }
}

#[inline(never)]
#[target_feature(enable = "avx2")]
unsafe fn do_vpmaskmovd(ptr: *mut i32, mask: [i32; 8], val: [i32; 8]) {
    unsafe {
        let m = _mm256_loadu_si256(black_box(mask.as_ptr()) as *const __m256i);
        let v = _mm256_loadu_si256(black_box(val.as_ptr()) as *const __m256i);
        asm!(
            "vpmaskmovd [{p}], {m}, {v}",
            p = in(reg) black_box(ptr),
            m = in(ymm_reg) m,
            v = in(ymm_reg) v,
            options(nostack, preserves_flags),
        );
    }
}

#[inline(never)]
#[target_feature(enable = "avx2")]
unsafe fn do_vpmaskmovq(ptr: *mut i64, mask: [i64; 4], val: [i64; 4]) {
    unsafe {
        let m = _mm256_loadu_si256(black_box(mask.as_ptr()) as *const __m256i);
        let v = _mm256_loadu_si256(black_box(val.as_ptr()) as *const __m256i);
        asm!(
            "vpmaskmovq [{p}], {m}, {v}",
            p = in(reg) black_box(ptr),
            m = in(ymm_reg) m,
            v = in(ymm_reg) v,
            options(nostack, preserves_flags),
        );
    }
}

#[inline(never)]
#[target_feature(enable = "avx512vl,avx512bw")]
unsafe fn do_vmovdqu8_k(ptr: *mut u8, k: u32, val: [u8; 32]) {
    unsafe {
        let v = _mm256_loadu_si256(black_box(val.as_ptr()) as *const __m256i);
        asm!(
            "kmovd k1, {km:e}",
            "vmovdqu8 [{p}] {{k1}}, {v}",
            p = in(reg) black_box(ptr),
            km = in(reg) black_box(k),
            v = in(ymm_reg) v,
            out("k1") _,
            options(nostack, preserves_flags),
        );
    }
}

#[inline(never)]
#[target_feature(enable = "avx512vl,avx512bw")]
unsafe fn do_vmovdqu16_k(ptr: *mut u16, k: u16, val: [u16; 16]) {
    unsafe {
        let v = _mm256_loadu_si256(black_box(val.as_ptr()) as *const __m256i);
        asm!(
            "kmovw k1, {km:e}",
            "vmovdqu16 [{p}] {{k1}}, {v}",
            p = in(reg) black_box(ptr),
            km = in(reg) black_box(k as u32),
            v = in(ymm_reg) v,
            out("k1") _,
            options(nostack, preserves_flags),
        );
    }
}

#[inline(never)]
#[target_feature(enable = "avx512vl,avx512f")]
unsafe fn do_vmovdqa32_k(ptr: *mut u32, k: u8, val: [u32; 8]) {
    unsafe {
        let v = _mm256_loadu_si256(black_box(val.as_ptr()) as *const __m256i);
        asm!(
            "kmovb k1, {km:e}",
            "vmovdqa32 [{p}] {{k1}}, {v}",
            p = in(reg) black_box(ptr),
            km = in(reg) black_box(k as u32),
            v = in(ymm_reg) v,
            out("k1") _,
            options(nostack, preserves_flags),
        );
    }
}

#[inline(never)]
#[target_feature(enable = "sse2")]
unsafe fn do_maskmovdqu_sse2(ptr: *mut u8, mask: [u8; 16], val: [u8; 16]) {
    unsafe {
        let m = _mm_loadu_si128(black_box(mask.as_ptr()) as *const __m128i);
        let v = _mm_loadu_si128(black_box(val.as_ptr()) as *const __m128i);
        asm!(
            "maskmovdqu {v}, {m}",
            in("rdi") black_box(ptr),
            v = in(xmm_reg) v,
            m = in(xmm_reg) m,
            options(nostack, preserves_flags),
        );
    }
}

#[inline(never)]
#[target_feature(enable = "avx")]
unsafe fn do_vmaskmovdqu_vex(ptr: *mut u8, mask: [u8; 16], val: [u8; 16]) {
    unsafe {
        let m = _mm_loadu_si128(black_box(mask.as_ptr()) as *const __m128i);
        let v = _mm_loadu_si128(black_box(val.as_ptr()) as *const __m128i);
        asm!(
            "vmaskmovdqu {v}, {m}",
            in("rdi") black_box(ptr),
            v = in(xmm_reg) v,
            m = in(xmm_reg) m,
            options(nostack, preserves_flags),
        );
    }
}

#[inline(never)]
#[target_feature(enable = "avx")]
unsafe fn do_vmovntdq(ptr: *mut __m256i, val: [u8; 32]) {
    unsafe {
        let v = _mm256_loadu_si256(black_box(val.as_ptr()) as *const __m256i);
        asm!(
            "vmovntdq [{p}], {v}",
            "sfence",
            p = in(reg) black_box(ptr),
            v = in(ymm_reg) v,
            options(nostack, preserves_flags),
        );
    }
}

#[repr(C, align(32))]
struct SharedPair32 {
    buf: [u8; 16],
    sibling: AtomicU64,
    _pad: u64,
}

#[inline(never)]
#[target_feature(enable = "avx2")]
unsafe fn buggy_rmw_slack_writeback(ptr: *mut u8) {
    unsafe {
        let algn = (ptr as usize & !31usize) as *mut __m256i;
        let orig = _mm256_load_si256(algn);
        let new_val = _mm256_set1_epi8(0x42);
        let mask = _mm256_set_epi64x(0, 0, -1, -1);
        let blended = _mm256_blendv_epi8(orig, new_val, mask);
        _mm256_store_si256(algn, blended);
    }
}

fn measure_concurrent_rmw_tearing() -> (u64, u64) {
    let shared = Box::leak(Box::new(SharedPair32 {
        buf: [0; 16],
        sibling: AtomicU64::new(0),
        _pad: 0,
    }));
    let stop = Box::leak(Box::new(AtomicBool::new(false)));
    let shared_ref1 = &*shared;
    let shared_ref2 = &*shared;
    let stop1 = &*stop;

    let writer = thread::spawn(move || {
        let mut expected = 0u64;
        let mut lost_events = 0u64;
        for _ in 0..200_000u64 {
            let prev = shared_ref2.sibling.fetch_add(1, Ordering::SeqCst);
            if prev != expected {
                lost_events += 1;
            }
            expected = prev + 1;
        }
        stop1.store(true, Ordering::SeqCst);
        (shared_ref2.sibling.load(Ordering::SeqCst), lost_events)
    });

    let buf_ptr = shared_ref1.buf.as_ptr() as *mut u8;
    while !stop.load(Ordering::Relaxed) {
        unsafe { buggy_rmw_slack_writeback(buf_ptr); }
    }
    let (final_val, lost_events) = writer.join().unwrap();
    let total_lost = 200_000u64.saturating_sub(final_val);
    (total_lost, lost_events)
}

fn main() {
    install_handlers();
    unsafe {
        // 6-page arena:
        // [0..4096):     P0 PROT_NONE (leading guard)
        // [4096..8192):  P1 RW
        // [8192..12288): P2 PROT_READ (initialized to 0x5A)
        // [12288..16384): P3 RW
        // [16384..20480): P4 PROT_NONE (mprotect)
        // [20480..24576): P5 UNMAPPED (munmap)
        let arena = mmap(
            core::ptr::null_mut(),
            6 * 4096,
            PROT_READ | PROT_WRITE,
            MAP_PRIVATE | MAP_ANONYMOUS,
            -1,
            0,
        );
        assert!((arena as isize) > 0);
        core::ptr::write_bytes(arena, 0x5A, 6 * 4096);
        assert_eq!(mprotect(arena, 4096, PROT_NONE), 0);
        assert_eq!(mprotect(arena.add(2 * 4096), 4096, PROT_READ), 0);
        assert_eq!(mprotect(arena.add(4 * 4096), 4096, PROT_NONE), 0);
        assert_eq!(munmap(arena.add(5 * 4096), 4096), 0);

        let base = arena as usize;
        let p1_rw = arena.add(4096);
        let p2_ro = arena.add(2 * 4096);
        let p3_rw = arena.add(3 * 4096);
        let p4_pnone = arena.add(4 * 4096);
        let p5_unmap = arena.add(5 * 4096);
        let noncanon = 0xdead_0000_0000_0000usize as *mut u8;

        let mut rows = Vec::new();
        let val32_i32 = [0x11223344i32; 8];
        let val32_i64 = [0x1122334455667788i64; 4];
        let val32_u8 = [0xABu8; 32];
        let val32_u16 = [0xCD12u16; 16];
        let val32_u32 = [0xCAFEBABEu32; 8];
        let val16_u8 = [0xEFu8; 16];

        // 1. VPMASKMOVD / VPMASKMOVQ
        rows.push(trap_call("vpmaskmovd_straddle_ro_inactive0", base, || {
            do_vpmaskmovd(p1_rw.add(4096 - 12) as *mut i32, [-1, -1, -1, 0, 0, 0, 0, 0], val32_i32);
        }));
        assert_eq!(*(p1_rw.add(4096 - 12) as *const i32), 0x11223344);
        assert_eq!(*p2_ro, 0x5A);

        rows.push(trap_call("vpmaskmovd_straddle_prot_none_inactive0", base, || {
            do_vpmaskmovd(p3_rw.add(4096 - 12) as *mut i32, [-1, -1, -1, 0, 0, 0, 0, 0], val32_i32);
        }));
        rows.push(trap_call("vpmaskmovd_lsb1_msb0_on_prot_none", base, || {
            do_vpmaskmovd(p4_pnone as *mut i32, [1; 8], val32_i32);
        }));
        rows.push(trap_call("vpmaskmovd_mask0_prot_read", base, || {
            do_vpmaskmovd(p2_ro as *mut i32, [0; 8], val32_i32);
        }));
        rows.push(trap_call("vpmaskmovd_mask0_prot_none", base, || {
            do_vpmaskmovd(p4_pnone as *mut i32, [0; 8], val32_i32);
        }));
        rows.push(trap_call("vpmaskmovd_mask0_unmapped", base, || {
            do_vpmaskmovd(p5_unmap as *mut i32, [0; 8], val32_i32);
        }));
        rows.push(trap_call("vpmaskmovd_mask0_noncanonical", base, || {
            do_vpmaskmovd(noncanon as *mut i32, [0; 8], val32_i32);
        }));
        rows.push(trap_call("vpmaskmovd_active_lane1_prot_read", base, || {
            do_vpmaskmovd(p2_ro as *mut i32, [0, -1, 0, 0, 0, 0, 0, 0], val32_i32);
        }));
        rows.push(trap_call("vpmaskmovd_active_lane0_noncanonical", base, || {
            do_vpmaskmovd(noncanon as *mut i32, [-1, 0, 0, 0, 0, 0, 0, 0], val32_i32);
        }));
        rows.push(trap_call("vpmaskmovq_straddle_prot_none_inactive0", base, || {
            do_vpmaskmovq(p3_rw.add(4096 - 16) as *mut i64, [-1, -1, 0, 0], val32_i64);
        }));
        rows.push(trap_call("vpmaskmovq_mask0_noncanonical", base, || {
            do_vpmaskmovq(noncanon as *mut i64, [0; 4], val32_i64);
        }));

        // 2. EVEX VMOVDQU8 / VMOVDQU16 / VMOVDQA32
        rows.push(trap_call("vmovdqu8_straddle_ro_inactive0", base, || {
            do_vmovdqu8_k(p1_rw.add(4096 - 5), 0x1f, val32_u8);
        }));
        assert_eq!(*p1_rw.add(4096 - 1), 0xAB);
        assert_eq!(*p2_ro, 0x5A);

        rows.push(trap_call("vmovdqu8_straddle_prot_none_inactive0", base, || {
            do_vmovdqu8_k(p3_rw.add(4096 - 5), 0x1f, val32_u8);
        }));
        rows.push(trap_call("vmovdqu8_k0_prot_read", base, || {
            do_vmovdqu8_k(p2_ro, 0, val32_u8);
        }));
        rows.push(trap_call("vmovdqu8_k0_prot_none", base, || {
            do_vmovdqu8_k(p4_pnone, 0, val32_u8);
        }));
        rows.push(trap_call("vmovdqu8_k0_unmapped", base, || {
            do_vmovdqu8_k(p5_unmap, 0, val32_u8);
        }));
        rows.push(trap_call("vmovdqu8_k0_noncanonical", base, || {
            do_vmovdqu8_k(noncanon, 0, val32_u8);
        }));
        rows.push(trap_call("vmovdqu16_straddle_prot_none_inactive0", base, || {
            do_vmovdqu16_k(p3_rw.add(4096 - 6) as *mut u16, 0x07, val32_u16);
        }));
        rows.push(trap_call("vmovdqu16_k0_noncanonical", base, || {
            do_vmovdqu16_k(noncanon as *mut u16, 0, val32_u16);
        }));
        rows.push(trap_call("vmovdqa32_k0_misaligned_prot_none", base, || {
            do_vmovdqa32_k(p4_pnone.add(1) as *mut u32, 0, val32_u32);
        }));
        rows.push(trap_call("vmovdqa32_k0_misaligned_rw", base, || {
            do_vmovdqa32_k(p1_rw.add(1) as *mut u32, 0, val32_u32);
        }));
        rows.push(trap_call("vmovdqa32_k1_misaligned_rw", base, || {
            do_vmovdqa32_k(p1_rw.add(1) as *mut u32, 1, val32_u32);
        }));

        // 3. SSE2 MASKMOVDQU (66 0F F7, implicit [rdi]) & VEX VMASKMOVDQU
        rows.push(trap_call("maskmovdqu_mask0_rw", base, || {
            do_maskmovdqu_sse2(p1_rw, [0; 16], val16_u8);
        }));
        rows.push(trap_call("maskmovdqu_mask0_prot_read", base, || {
            do_maskmovdqu_sse2(p2_ro, [0; 16], val16_u8);
        }));
        rows.push(trap_call("maskmovdqu_mask0_prot_none", base, || {
            do_maskmovdqu_sse2(p4_pnone, [0; 16], val16_u8);
        }));
        rows.push(trap_call("maskmovdqu_mask0_unmapped", base, || {
            do_maskmovdqu_sse2(p5_unmap, [0; 16], val16_u8);
        }));
        rows.push(trap_call("maskmovdqu_mask0_noncanonical", base, || {
            do_maskmovdqu_sse2(noncanon, [0; 16], val16_u8);
        }));
        rows.push(trap_call("maskmovdqu_straddle_ro_inactive0", base, || {
            let mut m = [0u8; 16];
            for i in 0..8 { m[i] = 0x80; }
            do_maskmovdqu_sse2(p1_rw.add(4096 - 8), m, val16_u8);
        }));
        rows.push(trap_call("maskmovdqu_straddle_prot_none_inactive0", base, || {
            let mut m = [0u8; 16];
            for i in 0..8 { m[i] = 0x80; }
            do_maskmovdqu_sse2(p3_rw.add(4096 - 8), m, val16_u8);
        }));
        rows.push(trap_call("vmaskmovdqu_vex_mask0_prot_read", base, || {
            do_vmaskmovdqu_vex(p2_ro, [0; 16], val16_u8);
        }));
        rows.push(trap_call("vmaskmovdqu_vex_mask0_prot_none", base, || {
            do_vmaskmovdqu_vex(p4_pnone, [0; 16], val16_u8);
        }));
        rows.push(trap_call("vmaskmovdqu_vex_mask0_noncanonical", base, || {
            do_vmaskmovdqu_vex(noncanon, [0; 16], val16_u8);
        }));
        rows.push(trap_call("vmaskmovdqu_vex_straddle_prot_none_inactive0", base, || {
            let mut m = [0u8; 16];
            for i in 0..8 { m[i] = 0x80; }
            do_vmaskmovdqu_vex(p3_rw.add(4096 - 8), m, val16_u8);
        }));

        // 4. VMOVNTDQ
        rows.push(trap_call("vmovntdq_aligned_rw", base, || {
            do_vmovntdq(p1_rw as *mut __m256i, val32_u8);
        }));
        rows.push(trap_call("vmovntdq_misaligned_rw", base, || {
            do_vmovntdq(p1_rw.add(1) as *mut __m256i, val32_u8);
        }));
        rows.push(trap_call("vmovntdq_prot_read", base, || {
            do_vmovntdq(p2_ro as *mut __m256i, val32_u8);
        }));
        rows.push(trap_call("vmovntdq_prot_none", base, || {
            do_vmovntdq(p4_pnone as *mut __m256i, val32_u8);
        }));
        rows.push(trap_call("vmovntdq_noncanonical", base, || {
            do_vmovntdq(noncanon as *mut __m256i, val32_u8);
        }));

        let (lost_updates, lost_events) = measure_concurrent_rmw_tearing();
        println!(
            "{{\"cases\":[{}],\"rmw_concurrent_tearing\":{{\"atomic_increments\":200000,\"lost_updates\":{},\"observed_regressions\":{}}}}}",
            rows.join(","),
            lost_updates,
            lost_events
        );
    }
}
"""


AARCH64_WRITE_ORACLE_RS = r"""
#![no_std]
#![no_main]
use core::arch::{asm, global_asm};

global_asm!(
    ".global _start",
    "_start:",
    "mov x0, sp",
    "bl rust_entry",
    "brk #0",
);

#[panic_handler]
fn panic_handler(_: &core::panic::PanicInfo) -> ! { exit_group(99) }
#[unsafe(no_mangle)]
pub unsafe extern "C" fn rust_eh_personality() {}

#[repr(C)]
struct KernelSigAction { sa_handler: usize, sa_flags: usize, sa_mask: u64 }
#[repr(C)]
struct SigInfoHeader { si_signo: i32, si_errno: i32, si_code: i32, _pad: i32, si_addr: usize }

static mut BASE_ADDR: usize = 0;

unsafe fn syscall6(n: usize, a0: usize, a1: usize, a2: usize, a3: usize, a4: usize, a5: usize) -> isize {
    let ret: isize;
    unsafe {
        asm!(
            "svc #0",
            in("x8") n,
            inout("x0") a0 => ret,
            in("x1") a1,
            in("x2") a2,
            in("x3") a3,
            in("x4") a4,
            in("x5") a5,
            options(nostack),
        );
    }
    ret
}

fn write_all(buf: &[u8]) { unsafe { let _ = syscall6(64, 1, buf.as_ptr() as usize, buf.len(), 0, 0, 0); } }
fn exit_group(code: usize) -> ! { unsafe { let _ = syscall6(94, code, 0, 0, 0, 0, 0); } loop {} }

fn fmt_dec(mut n: usize, out: &mut [u8; 24]) -> &[u8] {
    if n == 0 { out[23] = b'0'; return &out[23..24]; }
    let mut i = 24;
    while n > 0 { i -= 1; out[i] = b'0' + (n % 10) as u8; n /= 10; }
    &out[i..24]
}

unsafe extern "C" fn sig_handler(sig: i32, info: *const SigInfoHeader, _ucontext: *mut u8) {
    unsafe {
        let code = (*info).si_code;
        let addr = (*info).si_addr;
        let untagged = addr & 0x00ff_ffff_ffff_ffff;
        let tag = (addr >> 56) & 0xf;
        let base = BASE_ADDR;
        let (mut b0, mut b1, mut b2, mut b3) = ([0u8; 24], [0u8; 24], [0u8; 24], [0u8; 24]);
        write_all(b"{\"faulted\":true,\"sig\":");
        write_all(fmt_dec(sig as usize, &mut b0));
        write_all(b",\"si_code\":");
        write_all(fmt_dec(code as usize, &mut b1));
        write_all(b",\"rel_addr\":");
        if untagged >= base && untagged < base + 6 * 4096 {
            write_all(fmt_dec(untagged - base, &mut b2));
        } else {
            write_all(b"-1");
        }
        write_all(b",\"ptr_tag\":");
        write_all(fmt_dec(tag, &mut b3));
        write_all(b"}\n");
        exit_group(0);
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn rust_entry(sp: *const usize) -> ! {
    unsafe {
        let argc = *sp;
        let case_id = if argc >= 2 { (*(*sp.add(2) as *const u8)).wrapping_sub(b'0') } else { 0 };
        let act = KernelSigAction {
            sa_handler: sig_handler as *const () as usize,
            sa_flags: 0x0000_0004,
            sa_mask: 0,
        };
        assert!(syscall6(134, 11, &act as *const _ as usize, 0, 8, 0, 0) == 0);
        let _ = syscall6(167, 55, 1 | 2 | (0xfffe << 3), 0, 0, 0, 0);

        let raw = syscall6(222, 0, 4 * 4096, 0x1 | 0x2 | 0x20, 0x22, usize::MAX, 0);
        assert!(raw > 0);
        let base = raw as usize;
        BASE_ADDR = base;
        assert!(syscall6(226, base + 4096, 4096, 0x1, 0, 0, 0) == 0);
        assert!(syscall6(226, base + 2 * 4096, 4096, 0x1 | 0x2, 0, 0, 0) == 0);
        assert!(syscall6(226, base + 3 * 4096, 4096, 0x0, 0, 0, 0) == 0);

        let p0_t1 = base | (1usize << 56);
        let p0_t2 = (base + 16) | (2usize << 56);
        asm!(
            ".arch armv8.5-a+memtag",
            "stg {p1}, [{p1}]",
            "stg {p2}, [{p2}]",
            p1 = in(reg) p0_t1,
            p2 = in(reg) p0_t2,
            options(nostack),
        );

        match case_id {
            0 => {
                let p_none = base + 3 * 4096;
                asm!(
                    ".arch armv8.5-a+sve",
                    "pfalse p0.b",
                    "mov z0.b, #0x42",
                    "st1b {{z0.b}}, p0, [{p}]",
                    p = in(reg) p_none,
                    out("p0") _,
                    out("z0") _,
                    options(nostack),
                );
                write_all(b"{\"faulted\":false,\"note\":\"sve_st1b_pfalse_prot_none\"}\n");
            }
            1 => {
                let p_strad_ro = base + 4096 - 5;
                asm!(
                    ".arch armv8.5-a+sve",
                    "mov x9, #5",
                    "whilelt p0.b, xzr, x9",
                    "mov z0.b, #0x77",
                    "st1b {{z0.b}}, p0, [{p}]",
                    p = in(reg) p_strad_ro,
                    out("x9") _,
                    out("p0") _,
                    out("z0") _,
                    options(nostack),
                );
                write_all(b"{\"faulted\":false,\"note\":\"sve_st1b_straddle_ro_inactive0\"}\n");
            }
            2 => {
                let p_strad = base + 3 * 4096 - 5;
                asm!(
                    ".arch armv8.5-a+sve",
                    "mov x9, #5",
                    "whilelt p0.b, xzr, x9",
                    "mov z0.b, #0x77",
                    "st1b {{z0.b}}, p0, [{p}]",
                    p = in(reg) p_strad,
                    out("x9") _,
                    out("p0") _,
                    out("z0") _,
                    options(nostack),
                );
                write_all(b"{\"faulted\":false,\"note\":\"sve_st1b_straddle_prot_none_inactive0\"}\n");
            }
            3 => {
                asm!("ldr q0, [{p}]", "str q0, [{p}]", p = in(reg) p0_t1, out("v0") _, options(nostack));
                asm!(
                    "movi v0.16b, #0x11",
                    "movi v1.16b, #0x22",
                    "stp q0, q1, [{p}]",
                    p = in(reg) p0_t1,
                    out("v0") _,
                    out("v1") _,
                    options(nostack),
                );
                write_all(b"{\"faulted\":false,\"note\":\"unexpected\"}\n");
            }
            4 => {
                let p_bad_tag = base | (2usize << 56);
                asm!(
                    ".arch armv8.5-a+sve",
                    "mov x9, #4",
                    "whilelt p0.b, xzr, x9",
                    "mov z0.b, #0x33",
                    "st1b {{z0.b}}, p0, [{p}]",
                    p = in(reg) p_bad_tag,
                    out("x9") _,
                    out("p0") _,
                    out("z0") _,
                    options(nostack),
                );
                write_all(b"{\"faulted\":false,\"note\":\"qemu_user_sve_st1b_mte_unchecked\"}\n");
            }
            _ => {
                let p_strad = base + 4096 - 8;
                asm!("movi v0.16b, #0x99", "str q0, [{p}]", p = in(reg) p_strad, out("v0") _, options(nostack));
                write_all(b"{\"faulted\":false}\n");
            }
        }
        exit_group(0);
    }
}
"""


CODEGEN_PROBE_RS = r"""
#![feature(repr_simd, core_intrinsics)]
#![allow(internal_features, non_camel_case_types)]
#![crate_type = "lib"]

use core::intrinsics::simd::{simd_masked_store, SimdAlign};

#[repr(simd)] #[derive(Copy, Clone)] pub struct u8x16([u8; 16]);
#[repr(simd)] #[derive(Copy, Clone)] pub struct i8x16([i8; 16]);
#[repr(simd)] #[derive(Copy, Clone)] pub struct u8x32([u8; 32]);
#[repr(simd)] #[derive(Copy, Clone)] pub struct i8x32([i8; 32]);
#[repr(simd)] #[derive(Copy, Clone)] pub struct u16x16([u16; 16]);
#[repr(simd)] #[derive(Copy, Clone)] pub struct i16x16([i16; 16]);
#[repr(simd)] #[derive(Copy, Clone)] pub struct u32x8([u32; 8]);
#[repr(simd)] #[derive(Copy, Clone)] pub struct i32x8([i32; 8]);
#[repr(simd)] #[derive(Copy, Clone)] pub struct u64x4([u64; 4]);
#[repr(simd)] #[derive(Copy, Clone)] pub struct i64x4([i64; 4]);

#[unsafe(no_mangle)]
pub unsafe fn mstore_u8x16(mask: i8x16, ptr: *mut u8, val: u8x16) {
    unsafe { simd_masked_store::<_, _, _, { SimdAlign::Unaligned }>(mask, ptr, val); }
}
#[unsafe(no_mangle)]
pub unsafe fn mstore_u8x32(mask: i8x32, ptr: *mut u8, val: u8x32) {
    unsafe { simd_masked_store::<_, _, _, { SimdAlign::Unaligned }>(mask, ptr, val); }
}
#[unsafe(no_mangle)]
pub unsafe fn mstore_u16x16(mask: i16x16, ptr: *mut u16, val: u16x16) {
    unsafe { simd_masked_store::<_, _, _, { SimdAlign::Unaligned }>(mask, ptr, val); }
}
#[unsafe(no_mangle)]
pub unsafe fn mstore_u32x8(mask: i32x8, ptr: *mut u32, val: u32x8) {
    unsafe { simd_masked_store::<_, _, _, { SimdAlign::Unaligned }>(mask, ptr, val); }
}
#[unsafe(no_mangle)]
pub unsafe fn mstore_u64x4(mask: i64x4, ptr: *mut u64, val: u64x4) {
    unsafe { simd_masked_store::<_, _, _, { SimdAlign::Unaligned }>(mask, ptr, val); }
}
"""


MIRI_SUITE_RS = r"""
#![feature(repr_simd, core_intrinsics)]
#![allow(internal_features)]

use core::arch::x86_64::*;
use core::intrinsics::simd::{simd_masked_store, SimdAlign};

#[repr(simd)] #[derive(Copy, Clone)] struct I32x4([i32; 4]);
#[repr(simd)] #[derive(Copy, Clone)] struct U32x4([u32; 4]);

#[repr(C, align(32))]
struct Tiny16([u8; 16]);

#[repr(C, align(32))]
struct Pair32 {
    left: [u8; 16],
    right: [u8; 16],
}

unsafe fn rmw_slack_writeback_32(ptr: *mut u8) {
    let mut tmp = [0u8; 32];
    unsafe {
        core::ptr::copy_nonoverlapping(ptr as *const u8, tmp.as_mut_ptr(), 32);
        for i in 0..16 { tmp[i] ^= 0x5A; }
        core::ptr::copy_nonoverlapping(tmp.as_ptr(), ptr, 32);
    }
}

fn callee_with_strong_protector(left: &mut [u8; 16], _right_protected: &[u8; 16]) {
    unsafe { rmw_slack_writeback_32(left.as_mut_ptr()); }
}

fn xor_disjoint_overlap_tail(dst: &mut [u8], src: &[u8], key: u8) {
    let len = dst.len();
    assert_eq!(len, src.len());
    assert!(len >= 32);
    let dptr = dst.as_mut_ptr();
    let sptr = src.as_ptr();
    let mut off = 0usize;
    while off + 32 < len {
        unsafe {
            let mut blk = [0u8; 32];
            core::ptr::copy_nonoverlapping(sptr.add(off), blk.as_mut_ptr(), 32);
            for b in &mut blk { *b ^= key; }
            core::ptr::copy_nonoverlapping(blk.as_ptr(), dptr.add(off), 32);
        }
        off += 32;
    }
    let tail = len - 32;
    unsafe {
        let mut blk = [0u8; 32];
        core::ptr::copy_nonoverlapping(sptr.add(tail), blk.as_mut_ptr(), 32);
        for b in &mut blk { *b ^= key; }
        core::ptr::copy_nonoverlapping(blk.as_ptr(), dptr.add(tail), 32);
    }
}

fn inplace_overlap_tail_unbuffered(buf: &mut [u8], f: fn(u8) -> u8) {
    let len = buf.len();
    assert!(len >= 32);
    let ptr = buf.as_mut_ptr();
    let mut off = 0usize;
    while off + 32 < len {
        unsafe {
            let mut blk = [0u8; 32];
            core::ptr::copy_nonoverlapping(ptr.add(off), blk.as_mut_ptr(), 32);
            for b in &mut blk { *b = f(*b); }
            core::ptr::copy_nonoverlapping(blk.as_ptr(), ptr.add(off), 32);
        }
        off += 32;
    }
    let tail = len - 32;
    unsafe {
        let mut blk = [0u8; 32];
        core::ptr::copy_nonoverlapping(ptr.add(tail), blk.as_mut_ptr(), 32);
        for b in &mut blk { *b = f(*b); }
        core::ptr::copy_nonoverlapping(blk.as_ptr(), ptr.add(tail), 32);
    }
}

fn inplace_overlap_tail_preloaded(buf: &mut [u8], f: fn(u8) -> u8) {
    let len = buf.len();
    assert!(len >= 32);
    let ptr = buf.as_mut_ptr();
    let mut tail_in = [0u8; 32];
    unsafe {
        core::ptr::copy_nonoverlapping(ptr.add(len - 32), tail_in.as_mut_ptr(), 32);
    }
    let mut off = 0usize;
    while off + 32 < len {
        unsafe {
            let mut blk = [0u8; 32];
            core::ptr::copy_nonoverlapping(ptr.add(off), blk.as_mut_ptr(), 32);
            for b in &mut blk { *b = f(*b); }
            core::ptr::copy_nonoverlapping(blk.as_ptr(), ptr.add(off), 32);
        }
        off += 32;
    }
    for b in &mut tail_in { *b = f(*b); }
    unsafe {
        core::ptr::copy_nonoverlapping(tail_in.as_ptr(), ptr.add(len - 32), 32);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn exact_16b_alloc_oob() {
        let mut v = [1u8; 16];
        unsafe { rmw_slack_writeback_32(v.as_mut_ptr()); }
    }

    #[test]
    fn padded_32b_subslice_reborrow() {
        let mut t = Tiny16([1u8; 16]);
        let sub: &mut [u8; 16] = &mut t.0;
        unsafe { rmw_slack_writeback_32(sub.as_mut_ptr()); }
    }

    #[test]
    fn ub_same_alloc_sibling_strong_protector() {
        let mut p = Pair32 { left: [1u8; 16], right: [2u8; 16] };
        callee_with_strong_protector(&mut p.left, &p.right);
    }

    #[test]
    fn sibling_frozen_read_after_rmw() {
        let mut p = Pair32 { left: [1u8; 16], right: [2u8; 16] };
        let l = &mut p.left;
        let r = &p.right;
        unsafe { rmw_slack_writeback_32(l.as_mut_ptr()); }
        let val = r[0];
        assert_eq!(val, 2);
    }

    #[test]
    fn sibling_active_mut_read_after_rmw() {
        let mut p = Pair32 { left: [1u8; 16], right: [2u8; 16] };
        let l = &mut p.left;
        let r = &mut p.right;
        r[0] = 9;
        unsafe { rmw_slack_writeback_32(l.as_mut_ptr()); }
        assert_eq!(r[0], 9);
    }

    #[test]
    fn ub_simd_masked_store_misaligned_mask_zero() {
        let mut buf = [0u32; 8];
        let mis_ptr = unsafe { (buf.as_mut_ptr() as *mut u8).add(1) as *mut u32 };
        unsafe {
            simd_masked_store::<_, _, _, { SimdAlign::Vector }>(
                I32x4([0, 0, 0, 0]),
                mis_ptr,
                U32x4([1, 2, 3, 4]),
            );
        }
    }

    #[test]
    fn sound_vpmaskmovd_tail_oob_disabled() {
        let mut short = [1i32; 3];
        let m = [-1i32, -1, -1, 0, 0, 0, 0, 0];
        let v = [42i32; 8];
        unsafe {
            let mv = _mm256_loadu_si256(m.as_ptr() as *const __m256i);
            let vv = _mm256_loadu_si256(v.as_ptr() as *const __m256i);
            _mm256_maskstore_epi32(short.as_mut_ptr(), mv, vv);
        }
        assert_eq!(short, [42, 42, 42]);
    }

    #[test]
    fn miri_unsupported_maskmovdqu_mask0() {
        static RO: [u8; 16] = [0x5A; 16];
        unsafe {
            let zero = _mm_setzero_si128();
            _mm_maskmoveu_si128(zero, zero, RO.as_ptr() as *mut i8);
        }
    }

    #[test]
    fn trichotomy_all_modes_under_tree_borrows() {
        let orig: Vec<u8> = (0..33u8).map(|i| b'A' + (i % 26)).collect();
        let mut dst = vec![0u8; 33];
        xor_disjoint_overlap_tail(&mut dst, &orig, 0x5A);
        let expected_xor: Vec<u8> = orig.iter().map(|b| b ^ 0x5A).collect();
        assert_eq!(dst, expected_xor);

        let mut b_idem = orig.clone();
        inplace_overlap_tail_unbuffered(&mut b_idem, |b| if b >= b'A' && b <= b'Z' { b + 32 } else { b });
        let expected_low: Vec<u8> = orig.iter().map(|b| b.to_ascii_lowercase()).collect();
        assert_eq!(b_idem, expected_low);

        // At len == 32, even non-idempotent xor passes unbuffered because 0 + 32 < 32 is false!
        let mut b32 = orig[..32].to_vec();
        inplace_overlap_tail_unbuffered(&mut b32, |b| b ^ 0x5A);
        assert_eq!(b32, expected_xor[..32]);

        // At minimal overlap len == 33, indices 1..32 are XORed twice back to plaintext!
        let mut b33 = orig.clone();
        inplace_overlap_tail_unbuffered(&mut b33, |b| b ^ 0x5A);
        assert_eq!(b33[0], orig[0] ^ 0x5A);
        assert_eq!(&b33[1..32], &orig[1..32]);
        assert_eq!(b33[32], orig[32] ^ 0x5A);

        let mut b_pre = orig.clone();
        inplace_overlap_tail_preloaded(&mut b_pre, |b| b ^ 0x5A);
        assert_eq!(b_pre, expected_xor);
    }
}
"""


def scrub_text(s: str) -> str:
    # Strip any local home/temp paths from compiler/Miri diagnostic lines.
    s = re.sub(r"/[^\s:`'\"]+/([^/\s:`'\"]+)", r"<path>/\1", s)
    s = re.sub(r"alloc\d+", "allocN", s)
    s = re.sub(r"<\d+>", "<tag>", s)
    return s


def extract_fn_asm(asm_text: str, fn_name: str) -> str:
    m = re.search(rf"(?ms)^{re.escape(fn_name)}:\n(.*?)(?:^\.Lfunc_end|\Z)", asm_text)
    return m.group(1) if m else ""


def run_x86_hw_oracle(td: Path) -> dict[str, Any]:
    src = td / "x86_hw.rs"
    binp = td / "x86_hw"
    src.write_text(X86_HW_ORACLE_RS, encoding="utf-8")
    t0 = time.perf_counter()
    subprocess.run(
        ["rustc", "+1.99.1", "--edition=2024", "-C", "opt-level=3", str(src), "-o", str(binp)],
        check=True,
        capture_output=True,
        text=True,
    )
    t1 = time.perf_counter()
    run = subprocess.run([str(binp)], check=True, capture_output=True, text=True)
    t2 = time.perf_counter()
    payload = json.loads(run.stdout)
    by_name = {c["case"]: c for c in payload["cases"]}

    # Key assertions locking hardware truth:
    assert not by_name["vpmaskmovd_straddle_ro_inactive0"]["faulted"]
    assert not by_name["vpmaskmovd_straddle_prot_none_inactive0"]["faulted"]
    assert not by_name["vpmaskmovd_mask0_prot_read"]["faulted"]
    assert not by_name["vpmaskmovd_mask0_prot_none"]["faulted"]
    assert not by_name["vpmaskmovd_mask0_noncanonical"]["faulted"]
    assert by_name["vpmaskmovd_active_lane1_prot_read"]["faulted"]
    assert by_name["vpmaskmovd_active_lane1_prot_read"]["rel_addr"] == 8196
    assert not by_name["vmovdqu8_k0_prot_read"]["faulted"]
    assert not by_name["vmovdqu8_k0_prot_none"]["faulted"]
    assert not by_name["vmovdqu8_k0_noncanonical"]["faulted"]
    assert not by_name["vmovdqa32_k0_misaligned_rw"]["faulted"]
    assert by_name["vmovdqa32_k1_misaligned_rw"]["faulted"]
    assert by_name["maskmovdqu_mask0_prot_read"]["faulted"]
    assert by_name["maskmovdqu_mask0_prot_read"]["si_code"] == 2
    assert by_name["maskmovdqu_mask0_prot_none"]["faulted"]
    assert by_name["maskmovdqu_mask0_prot_none"]["si_code"] == 2
    assert by_name["maskmovdqu_straddle_ro_inactive0"]["faulted"]
    assert by_name["maskmovdqu_straddle_prot_none_inactive0"]["faulted"]
    assert by_name["vmaskmovdqu_vex_mask0_prot_read"]["faulted"]
    assert by_name["vmaskmovdqu_vex_mask0_prot_none"]["faulted"]
    assert by_name["vmovntdq_misaligned_rw"]["faulted"]
    assert payload["rmw_concurrent_tearing"]["lost_updates"] > 1000

    payload["compile_ms"] = round((t1 - t0) * 1000.0, 2)
    payload["run_ms"] = round((t2 - t1) * 1000.0, 2)
    return payload


def run_aarch64_qemu_oracle(td: Path) -> dict[str, Any]:
    qemu_bin = shutil.which("qemu-aarch64")
    assert qemu_bin is not None, "qemu-aarch64 not found"
    qemu_sha256 = hashlib.sha256(Path(qemu_bin).read_bytes()).hexdigest()
    qemu_ver = subprocess.run(
        [qemu_bin, "--version"], check=True, capture_output=True, text=True
    ).stdout.splitlines()[0]

    sysroot = subprocess.run(
        ["rustc", "+1.99.1", "--print", "sysroot"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    rust_lld = glob.glob(f"{sysroot}/lib/rustlib/*/bin/rust-lld")[0]

    src = td / "a64_write.rs"
    binp = td / "a64_write"
    src.write_text(AARCH64_WRITE_ORACLE_RS, encoding="utf-8")
    subprocess.run(
        [
            "rustc",
            "+1.99.1",
            "--edition=2024",
            "--target",
            "aarch64-unknown-linux-gnu",
            "-C",
            "panic=abort",
            "-C",
            "relocation-model=static",
            "-C",
            "opt-level=2",
            "-C",
            f"linker={rust_lld}",
            "-C",
            "linker-flavor=ld.lld",
            str(src),
            "-o",
            str(binp),
        ],
        check=True,
        capture_output=True,
        text=True,
    )

    case_names = {
        "0": "sve_st1b_pfalse_prot_none",
        "1": "sve_st1b_straddle_ro_inactive0",
        "2": "sve_st1b_straddle_prot_none_inactive0",
        "3": "neon_32b_stp_mte_granule_mismatch",
        "4": "sve_st1b_mte_tag_mismatch_qemu_user_gap",
        "5": "neon_16b_str_straddle_prot_read",
    }
    cases_out: dict[str, Any] = {}
    for cid, cname in case_names.items():
        r = subprocess.run(
            [qemu_bin, "-cpu", "max", str(binp), cid],
            check=True,
            capture_output=True,
            text=True,
        )
        cases_out[cname] = json.loads(r.stdout.strip())

    assert not cases_out["sve_st1b_pfalse_prot_none"]["faulted"]
    assert not cases_out["sve_st1b_straddle_ro_inactive0"]["faulted"]
    assert not cases_out["sve_st1b_straddle_prot_none_inactive0"]["faulted"]
    assert cases_out["neon_32b_stp_mte_granule_mismatch"]["faulted"]
    assert cases_out["neon_32b_stp_mte_granule_mismatch"]["si_code"] == 9
    assert cases_out["neon_16b_str_straddle_prot_read"]["faulted"]
    assert cases_out["neon_16b_str_straddle_prot_read"]["si_code"] == 2

    return {
        "qemu_version": qemu_ver,
        "qemu_sha256": qemu_sha256,
        "cases": cases_out,
    }


def run_codegen_audit(td: Path) -> dict[str, Any]:
    src = td / "cg.rs"
    src.write_text(CODEGEN_PROBE_RS, encoding="utf-8")
    out: dict[str, Any] = {}
    for tc_label, tc_arg, extra_env in [
        ("rustc_1.99.1", "+1.99.1", {"RUSTC_BOOTSTRAP": "1"}),
        ("rustc_nightly", "+nightly", {}),
    ]:
        out[tc_label] = {}
        env = dict(os.environ, **extra_env)
        for feat_label, feats in [
            ("avx2_only", "+avx2"),
            ("avx512vl_bw", "+avx2,+avx512vl,+avx512bw"),
        ]:
            asm_path = td / f"cg_{tc_label}_{feat_label}.s"
            subprocess.run(
                [
                    "rustc",
                    tc_arg,
                    "--edition=2024",
                    "-C",
                    "opt-level=3",
                    "-C",
                    f"target-feature={feats}",
                    "--emit=asm",
                    str(src),
                    "-o",
                    str(asm_path),
                ],
                env=env,
                check=True,
                capture_output=True,
                text=True,
            )
            asm_txt = asm_path.read_text(encoding="utf-8")
            fn_stats: dict[str, Any] = {}
            for fn_name in [
                "mstore_u8x16",
                "mstore_u8x32",
                "mstore_u16x16",
                "mstore_u32x8",
                "mstore_u64x4",
            ]:
                body = extract_fn_asm(asm_txt, fn_name)
                jcc = len(re.findall(r"^\s+j(?:ne|e|b|ae|l|g|ns|s)\b", body, re.M))
                tests = len(re.findall(r"^\s+test[blwq]?\b", body, re.M))
                vpextrb = len(re.findall(r"^\s+vpextr[bw]\b", body, re.M))
                vpmovmskb = len(re.findall(r"^\s+vpmovmskb\b", body, re.M))
                vec_stores = [
                    s.strip().replace("\t", " ")
                    for s in re.findall(
                        r"^\s+v(?:pmaskmov[dq]|movdqu(?:8|16|32|64))\b[^\n]*",
                        body,
                        re.M,
                    )
                ]
                fn_stats[fn_name] = {
                    "conditional_branches": jcc,
                    "bit_tests": tests,
                    "scalar_lane_extract_stores": vpextrb,
                    "vpmovmskb": vpmovmskb,
                    "hardware_masked_stores": vec_stores,
                }
            out[tc_label][feat_label] = fn_stats

    assert out["rustc_1.99.1"]["avx2_only"]["mstore_u8x16"]["conditional_branches"] == 31
    assert out["rustc_1.99.1"]["avx2_only"]["mstore_u8x32"]["conditional_branches"] == 63
    assert out["rustc_1.99.1"]["avx512vl_bw"]["mstore_u8x32"]["conditional_branches"] == 0
    return out


def run_miri_suite(td: Path) -> dict[str, Any]:
    proj = td / "miri_pkg"
    (proj / "src").mkdir(parents=True)
    (proj / "Cargo.toml").write_text(
        '[package]\nname = "miri_pkg"\nversion = "0.1.0"\nedition = "2024"\n',
        encoding="utf-8",
    )
    (proj / "src/lib.rs").write_text(MIRI_SUITE_RS, encoding="utf-8")

    results: dict[str, Any] = {}
    matrix = [
        ("tree_borrows", "-Zmiri-tree-borrows -C target-feature=+avx2", [
            ("exact_16b_alloc_oob", 1),
            ("padded_32b_subslice_reborrow", 0),
            ("ub_same_alloc_sibling_strong_protector", 1),
            ("sibling_frozen_read_after_rmw", 1),
            ("sibling_active_mut_read_after_rmw", 1),
            ("ub_simd_masked_store_misaligned_mask_zero", 1),
            ("sound_vpmaskmovd_tail_oob_disabled", 0),
            ("miri_unsupported_maskmovdqu_mask0", 1),
            ("trichotomy_all_modes_under_tree_borrows", 0),
        ]),
        ("stacked_borrows", "-C target-feature=+avx2", [
            ("exact_16b_alloc_oob", 1),
            ("padded_32b_subslice_reborrow", 1),
        ]),
    ]
    for mode_name, mflags, tests in matrix:
        mode_res: dict[str, Any] = {}
        env = dict(os.environ, MIRIFLAGS=mflags)
        for tname, exp_rc in tests:
            r = subprocess.run(
                ["cargo", "+nightly", "miri", "test", "--", "--exact", f"tests::{tname}"],
                cwd=str(proj),
                env=env,
                capture_output=True,
                text=True,
            )
            assert r.returncode == exp_rc, (
                f"Miri {mode_name}::{tname} expected rc={exp_rc}, got {r.returncode}:\n{r.stderr}"
            )
            combined = (r.stderr + "\n" + r.stdout).splitlines()
            diag = "ok"
            for line in combined:
                if "Undefined Behavior:" in line or "unsupported operation:" in line:
                    diag = scrub_text(line.strip())
                    break
            mode_res[tname] = {"rc": r.returncode, "diagnostic": diag}
        results[mode_name] = mode_res
    return results


def main() -> int:
    with tempfile.TemporaryDirectory() as raw_td:
        td = Path(raw_td)
        rustc_199 = subprocess.run(
            ["rustc", "+1.99.1", "-V"], check=True, capture_output=True, text=True
        ).stdout.strip()
        rustc_nightly = subprocess.run(
            ["rustc", "+nightly", "-V"], check=True, capture_output=True, text=True
        ).stdout.strip()
        miri_ver = subprocess.run(
            ["cargo", "+nightly", "miri", "--version"], check=True, capture_output=True, text=True
        ).stdout.strip()

        x86_hw = run_x86_hw_oracle(td)
        aarch64_qemu = run_aarch64_qemu_oracle(td)
        codegen = run_codegen_audit(td)
        miri = run_miri_suite(td)

    summary = {
        "toolchains": {
            "rustc_stable": rustc_199,
            "rustc_nightly": rustc_nightly,
            "miri": miri_ver,
            "host_arch": "x86_64-unknown-linux-gnu (Intel Xeon Ice Lake-SP @ 2.60GHz, avx2+avx512vl+avx512bw)",
        },
        "x86_64_silicon_oracle": x86_hw,
        "aarch64_qemu_oracle": aarch64_qemu,
        "simd_masked_store_codegen": codegen,
        "miri_borrows_and_tail_suite": miri,
    }
    out_path = HERE / "write_masked_faults_and_miri_results.json"
    out_path.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print(
        f"Verified {len(x86_hw['cases'])} x86-64 silicon cases, "
        f"{len(aarch64_qemu['cases'])} AArch64 QEMU cases, "
        f"rustc +avx2/+avx512bw codegen, and Miri TB/SB suite -> {out_path.name}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
