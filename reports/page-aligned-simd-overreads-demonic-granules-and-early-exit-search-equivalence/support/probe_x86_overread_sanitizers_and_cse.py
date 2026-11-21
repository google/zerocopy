#!/usr/bin/env python3
"""Empirical x86-64 probe for aligned AVX2 inline-assembly over-reads:
1. Exhaustive 4,096-offset x 0..129-length PROT_NONE guard-page & poison-slack
   matrix, plus negative SIGSEGV / tzcnt-vs-bsf / sarx-vs-shrx canaries.
2. AddressSanitizer (-Zsanitizer=address) and ThreadSanitizer (-Zsanitizer=thread)
   comparison across core::arch::_mm_load_si128 (16B), _mm256_load_si256 (32B),
   #[sanitize(address = "off")] non-inlining vs direct deref, interior shadow
   poisoning, and inline asm! vmovdqa.
3. LLVM -C opt-level=3 CSE/GVN interaction with options(readonly) vs
   options(pure, readonly) under adjacent-variable mutation and off-by-one masks.

Uses tempfile.TemporaryDirectory() exclusively for transient build artifacts.
"""

from __future__ import annotations

import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time

sys.dont_write_bytecode = True


GUARD_PAGE_RUST_SRC = r"""
use std::arch::asm;

fn memchr_ref(needle: u8, hay: &[u8]) -> Option<usize> {
    let mut i = 0usize;
    while i < hay.len() {
        if hay[i] == needle {
            return Some(i);
        }
        i += 1;
    }
    None
}

/// Sound page-aligned AVX2 over-read memchr:
/// - Explicit empty-slice guard (`len == 0 -> None`)
/// - Aligns pointer down (`p_aligned = ptr & !31`), executing only 32B-aligned
///   `vmovdqa` loads whose 32B span intersects `[ptr, ptr + len)`
/// - Masks leading `[p_aligned .. ptr)` bytes via logical `shrx` and trailing
///   `[ptr + len .. chunk_end)` bytes via BMI2 `bzhi`
/// - Uses `tzcnt` (BMI1) only on non-zero masked bitmasks and cleans upper YMM
///   via `vzeroupper`.
#[target_feature(enable = "avx2,bmi1,bmi2")]
unsafe fn memchr_avx2_overread(needle: u8, hay: &[u8]) -> Option<usize> {
    let len = hay.len();
    if len == 0 {
        return None;
    }
    let ptr = hay.as_ptr();
    let found_idx: isize;
    unsafe {
        asm!(
            "vmovd {xneedle:x}, {needle:e}",
            "vpbroadcastb {xneedle:y}, {xneedle:x}",
            "mov {mis:e}, {ptr:e}",
            "and {mis:e}, 31",
            "mov {algn}, {ptr}",
            "and {algn}, -32",
            "vmovdqa {ydat:y}, [{algn}]",
            "vpcmpeqb {ydat:y}, {ydat:y}, {xneedle:y}",
            "vpmovmskb {mask:e}, {ydat:y}",
            "shrx {mask:e}, {mask:e}, {mis:e}",
            "mov {rem_first:e}, 32",
            "sub {rem_first:e}, {mis:e}",
            "cmp {len}, {rem_first}",
            "ja 2f",
            "bzhi {mask:e}, {mask:e}, {len:e}",
            "test {mask:e}, {mask:e}",
            "jz 5f",
            "tzcnt {mask:e}, {mask:e}",
            "mov {out}, {mask}",
            "jmp 6f",
            "2:",
            "test {mask:e}, {mask:e}",
            "jnz 4f",
            "add {algn}, 32",
            "mov {rem}, {len}",
            "sub {rem}, {rem_first}",
            "3:",
            "cmp {rem}, 32",
            "jbe 7f",
            "vmovdqa {ydat:y}, [{algn}]",
            "vpcmpeqb {ydat:y}, {ydat:y}, {xneedle:y}",
            "vpmovmskb {mask:e}, {ydat:y}",
            "test {mask:e}, {mask:e}",
            "jnz 8f",
            "add {algn}, 32",
            "sub {rem}, 32",
            "jmp 3b",
            "4:",
            "tzcnt {mask:e}, {mask:e}",
            "mov {out}, {mask}",
            "jmp 6f",
            "7:",
            "vmovdqa {ydat:y}, [{algn}]",
            "vpcmpeqb {ydat:y}, {ydat:y}, {xneedle:y}",
            "vpmovmskb {mask:e}, {ydat:y}",
            "bzhi {mask:e}, {mask:e}, {rem:e}",
            "test {mask:e}, {mask:e}",
            "jz 5f",
            "8:",
            "tzcnt {mask:e}, {mask:e}",
            "sub {algn}, {ptr}",
            "add {algn}, {mask}",
            "mov {out}, {algn}",
            "jmp 6f",
            "5:",
            "mov {out}, -1",
            "6:",
            "vzeroupper",
            ptr = in(reg) ptr,
            len = in(reg) len,
            needle = in(reg) needle as u32,
            algn = out(reg) _,
            mis = out(reg) _,
            rem_first = out(reg) _,
            rem = out(reg) _,
            mask = out(reg) _,
            out = out(reg) found_idx,
            xneedle = out(ymm_reg) _,
            ydat = out(ymm_reg) _,
            options(readonly, nostack),
        );
    }
    if found_idx < 0 {
        None
    } else {
        Some(found_idx as usize)
    }
}

#[target_feature(enable = "avx2,bmi1,bmi2")]
unsafe fn buggy_unguarded_empty(needle: u8, ptr: *const u8, len: usize) -> Option<usize> {
    let found_idx: isize;
    unsafe {
        asm!(
            "vmovd {xneedle:x}, {needle:e}",
            "vpbroadcastb {xneedle:y}, {xneedle:x}",
            "mov {mis:e}, {ptr:e}",
            "and {mis:e}, 31",
            "mov {algn}, {ptr}",
            "and {algn}, -32",
            "vmovdqa {ydat:y}, [{algn}]",
            "vpcmpeqb {ydat:y}, {ydat:y}, {xneedle:y}",
            "vpmovmskb {mask:e}, {ydat:y}",
            "shrx {mask:e}, {mask:e}, {mis:e}",
            "bzhi {mask:e}, {mask:e}, {len:e}",
            "test {mask:e}, {mask:e}",
            "jz 2f",
            "tzcnt {mask:e}, {mask:e}",
            "mov {out}, {mask}",
            "jmp 3f",
            "2:",
            "mov {out}, -1",
            "3:",
            "vzeroupper",
            ptr = in(reg) ptr,
            len = in(reg) len,
            needle = in(reg) needle as u32,
            algn = out(reg) _,
            mis = out(reg) _,
            mask = out(reg) _,
            out = out(reg) found_idx,
            xneedle = out(ymm_reg) _,
            ydat = out(ymm_reg) _,
            options(readonly, nostack),
        );
    }
    if found_idx < 0 { None } else { Some(found_idx as usize) }
}

#[target_feature(enable = "avx2,bmi1,bmi2")]
unsafe fn buggy_unaligned_overread(needle: u8, hay: &[u8]) -> Option<usize> {
    if hay.is_empty() {
        return None;
    }
    let mask: u32;
    unsafe {
        asm!(
            "vmovd {xn:x}, {needle:e}",
            "vpbroadcastb {xn:y}, {xn:x}",
            "vmovdqu {yd:y}, [{ptr}]",
            "vpcmpeqb {yd:y}, {yd:y}, {xn:y}",
            "vpmovmskb {m:e}, {yd:y}",
            "bzhi {m:e}, {m:e}, {len:e}",
            "vzeroupper",
            ptr = in(reg) hay.as_ptr(),
            len = in(reg) hay.len(),
            needle = in(reg) needle as u32,
            m = out(reg) mask,
            xn = out(ymm_reg) _,
            yd = out(ymm_reg) _,
            options(readonly, nostack),
        );
    }
    if mask == 0 { None } else { Some(mask.trailing_zeros() as usize) }
}

#[target_feature(enable = "avx2")]
unsafe fn buggy_bsf_on_zero_mask(needle: u8, hay: &[u8]) -> Option<usize> {
    if hay.is_empty() {
        return None;
    }
    let out_idx: isize;
    unsafe {
        asm!(
            "vmovd {xn:x}, {needle:e}",
            "vpbroadcastb {xn:y}, {xn:x}",
            "mov {algn}, {ptr}",
            "and {algn}, -32",
            "mov ecx, {ptr:e}",
            "and ecx, 31",
            "vmovdqa {yd:y}, [{algn}]",
            "vpcmpeqb {yd:y}, {yd:y}, {xn:y}",
            "vpmovmskb {m:e}, {yd:y}",
            "shr {m:e}, cl",
            "bsf {m:e}, {m:e}",
            "cmp {len:e}, {m:e}",
            "jbe 2f",
            "mov {out}, {m}",
            "jmp 3f",
            "2:",
            "mov {out}, -1",
            "3:",
            "vzeroupper",
            ptr = in(reg) hay.as_ptr(),
            len = in(reg) hay.len(),
            needle = in(reg) needle as u32,
            algn = out(reg) _,
            out("ecx") _,
            m = out(reg) _,
            out = out(reg) out_idx,
            xn = out(ymm_reg) _,
            yd = out(ymm_reg) _,
            options(readonly, nostack),
        );
    }
    if out_idx < 0 { None } else { Some(out_idx as usize) }
}

#[target_feature(enable = "avx2,bmi1,bmi2")]
unsafe fn buggy_sarx_sign_extend(needle: u8, hay: &[u8]) -> u32 {
    let mask_out: u32;
    unsafe {
        asm!(
            "vmovd {xn:x}, {needle:e}",
            "vpbroadcastb {xn:y}, {xn:x}",
            "mov {algn}, {ptr}",
            "and {algn}, -32",
            "mov {mis:e}, {ptr:e}",
            "and {mis:e}, 31",
            "vmovdqa {yd:y}, [{algn}]",
            "vpcmpeqb {yd:y}, {yd:y}, {xn:y}",
            "vpmovmskb {m:e}, {yd:y}",
            "sarx {m:e}, {m:e}, {mis:e}",
            "vzeroupper",
            ptr = in(reg) hay.as_ptr(),
            needle = in(reg) needle as u32,
            algn = out(reg) _,
            mis = out(reg) _,
            m = out(reg) mask_out,
            xn = out(ymm_reg) _,
            yd = out(ymm_reg) _,
            options(readonly, nostack),
        );
    }
    mask_out
}

const PROT_NONE: i32 = 0x0;
const PROT_READ: i32 = 0x1;
const PROT_WRITE: i32 = 0x2;
const MAP_PRIVATE: i32 = 0x02;
const MAP_ANONYMOUS: i32 = 0x20;

unsafe extern "C" {
    fn mmap(addr: *mut u8, len: usize, prot: i32, flags: i32, fd: i32, off: isize) -> *mut u8;
    fn mprotect(addr: *mut u8, len: usize, prot: i32) -> i32;
    fn munmap(addr: *mut u8, len: usize) -> i32;
    fn fork() -> i32;
    fn waitpid(pid: i32, status: *mut i32, options: i32) -> i32;
    fn _exit(status: i32) -> !;
}

fn run_in_child<F: FnOnce()>(f: F) -> (bool, i32) {
    unsafe {
        let pid = fork();
        assert!(pid >= 0);
        if pid == 0 {
            f();
            _exit(0);
        }
        let mut status = 0i32;
        assert_eq!(waitpid(pid, &mut status, 0), pid);
        let sig = status & 0x7f;
        if sig != 0 {
            (true, sig)
        } else {
            (false, (status >> 8) & 0xff)
        }
    }
}

fn main() {
    let page = 4096usize;
    let needle = 0xA5u8;

    unsafe {
        let arena1 = mmap(
            core::ptr::null_mut(),
            3 * page,
            PROT_NONE,
            MAP_PRIVATE | MAP_ANONYMOUS,
            -1,
            0,
        );
        assert!((arena1 as isize) > 0);
        let p1 = arena1.add(page);
        let g2 = arena1.add(2 * page);
        assert_eq!(mprotect(p1, page, PROT_READ | PROT_WRITE), 0);

        let arena2 = mmap(
            core::ptr::null_mut(),
            4 * page,
            PROT_NONE,
            MAP_PRIVATE | MAP_ANONYMOUS,
            -1,
            0,
        );
        assert!((arena2 as isize) > 0);
        let q1 = arena2.add(page);
        assert_eq!(mprotect(q1, 2 * page, PROT_READ | PROT_WRITE), 0);

        let t0 = std::time::Instant::now();

        let empty_dangling: &[u8] = &[];
        assert_eq!(empty_dangling.as_ptr() as usize, 1);
        assert_eq!(memchr_avx2_overread(needle, empty_dangling), None);
        let empty_at_guard: &[u8] = core::slice::from_raw_parts(g2, 0);
        assert_eq!(memchr_avx2_overread(needle, empty_at_guard), None);

        core::ptr::write_bytes(p1, needle, page);
        core::ptr::write_bytes(q1, needle, 2 * page);

        let mut single_page_pairs = 0usize;
        let mut single_page_calls = 0usize;
        for off in 0..page {
            let max_len = (page - off).min(129);
            for len in 0..=max_len {
                single_page_pairs += 1;
                let base = p1.add(off);
                core::ptr::write_bytes(base, 0x5A, len);
                let hay = core::slice::from_raw_parts(base, len);

                assert_eq!(memchr_avx2_overread(needle, hay), None);
                single_page_calls += 1;

                if len > 0 {
                    *base.add(len - 1) = needle;
                    assert_eq!(memchr_avx2_overread(needle, hay), Some(len - 1));
                    *base.add(len - 1) = 0x5A;
                    single_page_calls += 1;

                    *base = needle;
                    *base.add(len - 1) = needle;
                    assert_eq!(memchr_avx2_overread(needle, hay), Some(0));
                    *base = 0x5A;
                    *base.add(len - 1) = 0x5A;
                    single_page_calls += 1;

                    let mid = len / 2;
                    let second = (2 * len) / 3;
                    *base.add(mid) = needle;
                    *base.add(second) = needle;
                    let got = memchr_avx2_overread(needle, hay);
                    let exp = memchr_ref(needle, hay);
                    assert_eq!(got, exp);
                    *base.add(mid) = 0x5A;
                    *base.add(second) = 0x5A;
                    single_page_calls += 1;
                }

                core::ptr::write_bytes(base, needle, len);
            }
        }

        let mut full_grid_pairs = 0usize;
        let mut full_grid_calls = 0usize;
        let mut page_crossing_pairs = 0usize;
        for off in 0..page {
            for len in 0..=129usize {
                full_grid_pairs += 1;
                if off + len > page {
                    page_crossing_pairs += 1;
                }
                let base = q1.add(off);
                core::ptr::write_bytes(base, 0x5A, len);
                let hay = core::slice::from_raw_parts(base, len);

                assert_eq!(memchr_avx2_overread(needle, hay), None);
                full_grid_calls += 1;

                if len > 0 {
                    let pos1 = (len * 3) / 7;
                    let pos2 = len - 1;
                    *base.add(pos1) = needle;
                    *base.add(pos2) = needle;
                    assert_eq!(memchr_avx2_overread(needle, hay), Some(pos1));
                    *base.add(pos1) = 0x5A;
                    *base.add(pos2) = 0x5A;
                    full_grid_calls += 1;
                }

                core::ptr::write_bytes(base, needle, len);
            }
        }
        let elapsed_ms = t0.elapsed().as_secs_f64() * 1000.0;

        let (c1_sig, c1_code) = run_in_child(|| {
            let empty: &[u8] = &[];
            let _ = core::hint::black_box(buggy_unguarded_empty(needle, empty.as_ptr(), 0));
        });

        let (c2_sig, c2_code) = run_in_child(|| {
            let _ = core::hint::black_box(buggy_unguarded_empty(needle, g2, 0));
        });

        *p1.add(4095) = 0x5A;
        let (c3_sig, c3_code) = run_in_child(|| {
            let hay1 = core::slice::from_raw_parts(p1.add(4095), 1);
            let _ = core::hint::black_box(buggy_unaligned_overread(needle, hay1));
        });

        core::ptr::write_bytes(p1, 0x5A, 32);
        let hay_nomatch = core::slice::from_raw_parts(p1, 1);
        let bsf_bug_res = buggy_bsf_on_zero_mask(needle, hay_nomatch);
        let sound_res = memchr_avx2_overread(needle, hay_nomatch);

        core::ptr::write_bytes(p1, 0x5A, 31);
        *p1.add(31) = needle;
        let hay_mis16 = core::slice::from_raw_parts(p1.add(16), 8);
        let sarx_raw_mask = buggy_sarx_sign_extend(needle, hay_mis16);

        assert_eq!(munmap(arena1, 3 * page), 0);
        assert_eq!(munmap(arena2, 4 * page), 0);

        println!(
            "{{\"single_page_pairs\":{},\"single_page_calls\":{},\"full_grid_pairs\":{},\"full_grid_calls\":{},\"page_crossing_pairs\":{},\"elapsed_ms\":{:.2},\"canary1_dangling_empty_sigsegv\":{},\"canary1_sig\":{},\"canary2_page_end_empty_sigsegv\":{},\"canary2_sig\":{},\"canary3_unaligned_len1_sigsegv\":{},\"canary3_sig\":{},\"canary4_bsf_zero_mask_got\":{},\"canary4_sound_got\":{},\"canary5_sarx_mask_hex\":\"0x{:08x}\"}}",
            single_page_pairs,
            single_page_calls,
            full_grid_pairs,
            full_grid_calls,
            page_crossing_pairs,
            elapsed_ms,
            if c1_sig { "true" } else { "false" },
            c1_code,
            if c2_sig { "true" } else { "false" },
            c2_code,
            if c3_sig { "true" } else { "false" },
            c3_code,
            match bsf_bug_res { Some(v) => v as isize, None => -1 },
            match sound_res { Some(v) => v as isize, None => -1 },
            sarx_raw_mask,
        );
    }
}
"""


ASAN_RUST_SRC = r"""
#![feature(sanitize)]
use std::arch::asm;
use std::arch::x86_64::*;

unsafe extern "C" {
    fn __asan_poison_memory_region(addr: *const u8, size: usize);
    fn __asan_unpoison_memory_region(addr: *const u8, size: usize);
}

#[target_feature(enable = "avx2,bmi1,bmi2")]
unsafe fn memchr_intrinsic_overread(needle: u8, hay: &[u8]) -> Option<usize> {
    if hay.is_empty() { return None; }
    let ptr = hay.as_ptr();
    let mis = (ptr as usize) & 31;
    let algn = ((ptr as usize) & !31) as *const __m256i;
    let v = unsafe { _mm256_load_si256(algn) };
    let eq = _mm256_cmpeq_epi8(v, _mm256_set1_epi8(needle as i8));
    let mut mask = (_mm256_movemask_epi8(eq) as u32) >> mis;
    if hay.len() < 32 {
        mask &= (1u32 << hay.len()) - 1;
    }
    if mask == 0 { None } else { Some(mask.trailing_zeros() as usize) }
}

/// Calls `_mm256_load_si256` from a `#[sanitize(address = "off")]` function:
/// LLVM refuses to inline `sanitize_address` `_mm256_load_si256` into this non-sanitized
/// caller, so `_mm256_load_si256` STILL runs ASan shadow checks!
#[sanitize(address = "off")]
#[target_feature(enable = "avx2,bmi1,bmi2")]
unsafe fn memchr_intrinsic_nosan_calls_core(needle: u8, hay: &[u8]) -> Option<usize> {
    if hay.is_empty() { return None; }
    let ptr = hay.as_ptr();
    let mis = (ptr as usize) & 31;
    let algn = ((ptr as usize) & !31) as *const __m256i;
    let v = unsafe { _mm256_load_si256(algn) };
    let eq = _mm256_cmpeq_epi8(v, _mm256_set1_epi8(needle as i8));
    let mut mask = (_mm256_movemask_epi8(eq) as u32) >> mis;
    if hay.len() < 32 {
        mask &= (1u32 << hay.len()) - 1;
    }
    if mask == 0 { None } else { Some(mask.trailing_zeros() as usize) }
}

/// Direct raw pointer dereference `*algn` inside `#[sanitize(address = "off")]`
/// (avoiding any call to a sanitized `core` wrapper): 0 ASan checks emitted!
#[sanitize(address = "off")]
#[target_feature(enable = "avx2")]
unsafe fn deref32_nosan_direct(algn: *const __m256i) -> i32 {
    let v = unsafe { *algn };
    _mm256_movemask_epi8(v)
}

#[target_feature(enable = "avx2,bmi1,bmi2")]
unsafe fn memchr_asm_overread(needle: u8, hay: &[u8]) -> Option<usize> {
    if hay.is_empty() { return None; }
    let mask: u32;
    unsafe {
        asm!(
            "vmovd {xn:x}, {needle:e}",
            "vpbroadcastb {xn:y}, {xn:x}",
            "mov {algn}, {ptr}",
            "and {algn}, -32",
            "mov {mis:e}, {ptr:e}",
            "and {mis:e}, 31",
            "vmovdqa {yd:y}, [{algn}]",
            "vpcmpeqb {yd:y}, {yd:y}, {xn:y}",
            "vpmovmskb {m:e}, {yd:y}",
            "shrx {m:e}, {m:e}, {mis:e}",
            "bzhi {m:e}, {m:e}, {len:e}",
            "vzeroupper",
            ptr = in(reg) hay.as_ptr(),
            len = in(reg) hay.len(),
            needle = in(reg) needle as u32,
            algn = out(reg) _,
            mis = out(reg) _,
            m = out(reg) mask,
            xn = out(ymm_reg) _,
            yd = out(ymm_reg) _,
            options(readonly, nostack),
        );
    }
    if mask == 0 { None } else { Some(mask.trailing_zeros() as usize) }
}

#[repr(C, align(32))]
struct Buf32([u8; 32]);

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_default();
    let stack_a = core::hint::black_box([0x11u8; 12]);
    let mut stack_b = core::hint::black_box([0x22u8; 12]);
    stack_b[5] = 0xA5;
    let heap_box = core::hint::black_box(Box::new([0x33u8; 12]));

    unsafe {
        match mode.as_str() {
            "asm_stack_and_heap" => {
                assert_eq!(memchr_asm_overread(0xA5, &stack_a), None);
                assert_eq!(memchr_asm_overread(0xA5, &stack_b), Some(5));
                assert_eq!(memchr_asm_overread(0xA5, &heap_box[..]), None);
            }
            "intrinsic_stack" => {
                let _ = core::hint::black_box(memchr_intrinsic_overread(0xA5, &stack_b));
            }
            "intrinsic_heap" => {
                let _ = core::hint::black_box(memchr_intrinsic_overread(0xA5, &heap_box[..]));
            }
            "intrinsic_nosan_calls_core" => {
                let _ = core::hint::black_box(memchr_intrinsic_nosan_calls_core(0xA5, &stack_b));
            }
            "deref32_nosan_direct" => {
                let algn = ((heap_box.as_ptr() as usize) & !31) as *const __m256i;
                let _ = core::hint::black_box(deref32_nosan_direct(algn));
            }
            "interior_granule_256b_blindspot" => {
                // AddressSanitizer::instrumentUnusualSizeOrAlignment checks ONLY `p` and `p + 31`
                // on a 32-byte `<4 x i64>` load, missing poisoned interior bytes `[p + 8 .. p + 24)`!
                let b = core::hint::black_box(Buf32([0x44u8; 32]));
                __asan_poison_memory_region(b.0.as_ptr().add(8), 16);
                let v = _mm256_load_si256(b.0.as_ptr() as *const __m256i);
                core::hint::black_box(v);
                __asan_unpoison_memory_region(b.0.as_ptr().add(8), 16);
            }
            _ => panic!("unknown mode"),
        }
    }
}
"""


TSAN_RUST_SRC = r"""
use std::arch::asm;
use std::arch::x86_64::*;
use std::cell::UnsafeCell;
use std::ffi::c_void;
use std::sync::atomic::{AtomicBool, Ordering};

#[repr(C, align(32))]
struct Shared32 {
    hay: [u8; 8],
    adj_in_16b: UnsafeCell<u64>,
    pad: [u8; 16],
}
unsafe impl Sync for Shared32 {}

static READY: AtomicBool = AtomicBool::new(false);
static DONE: AtomicBool = AtomicBool::new(false);

unsafe extern "C" {
    fn pthread_create(
        thread: *mut usize,
        attr: *const c_void,
        start: unsafe extern "C" fn(*mut c_void) -> *mut c_void,
        arg: *mut c_void,
    ) -> i32;
    fn pthread_join(thread: usize, retval: *mut *mut c_void) -> i32;
}

unsafe extern "C" fn writer_thread(arg: *mut c_void) -> *mut c_void {
    let s = unsafe { &*(arg as *const Shared32) };
    READY.store(true, Ordering::Relaxed);
    let mut i = 0u64;
    while !DONE.load(Ordering::Relaxed) {
        let v = if (i & 1) == 0 { 0xA5A5_A5A5_A5A5_A5A5u64 } else { 0u64 };
        unsafe { *s.adj_in_16b.get() = core::hint::black_box(v); }
        i = i.wrapping_add(1);
    }
    core::ptr::null_mut()
}

#[unsafe(no_mangle)]
#[target_feature(enable = "sse2")]
pub unsafe fn load16_sse2(p: *const __m128i) -> i32 {
    unsafe {
        let v = _mm_load_si128(p);
        let eq = _mm_cmpeq_epi8(v, _mm_set1_epi8(0xA5u8 as i8));
        _mm_movemask_epi8(eq)
    }
}

#[unsafe(no_mangle)]
#[target_feature(enable = "avx2")]
pub unsafe fn load32_avx2(p: *const __m256i) -> i32 {
    unsafe {
        let v = _mm256_load_si256(p);
        let eq = _mm256_cmpeq_epi8(v, _mm256_set1_epi8(0xA5u8 as i8));
        _mm256_movemask_epi8(eq)
    }
}

#[unsafe(no_mangle)]
#[target_feature(enable = "avx2")]
pub unsafe fn load32_asm_mask(p: *const u8, mask_bits: u32) -> u32 {
    let m: u32;
    unsafe {
        asm!(
            "vmovd {xn:x}, {n:e}",
            "vpbroadcastb {xn:y}, {xn:x}",
            "vmovdqa {yd:y}, [{p}]",
            "vpcmpeqb {yd:y}, {yd:y}, {xn:y}",
            "vpmovmskb {m:e}, {yd:y}",
            "and {m:e}, {mb:e}",
            "vzeroupper",
            p = in(reg) p,
            n = in(reg) 0xA5u32,
            mb = in(reg) mask_bits,
            m = out(reg) m,
            xn = out(ymm_reg) _,
            yd = out(ymm_reg) _,
            options(readonly, nostack),
        );
    }
    m
}

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_default();
    let shared = Shared32 {
        hay: [0x11u8; 8],
        adj_in_16b: UnsafeCell::new(0),
        pad: [0u8; 16],
    };
    let mut th = 0usize;
    unsafe {
        assert_eq!(
            pthread_create(
                &mut th,
                core::ptr::null(),
                writer_thread,
                (&raw const shared) as *mut c_void
            ),
            0
        );
        while !READY.load(Ordering::Relaxed) {}
        let mut leaked_hits = 0usize;
        for _ in 0..150_000 {
            match mode.as_str() {
                "sse2_16b_intrinsic" => {
                    let m = (load16_sse2(shared.hay.as_ptr() as *const __m128i) as u32) & 0xff;
                    assert_eq!(m, 0);
                }
                "avx2_32b_intrinsic" => {
                    let m = (load32_avx2(shared.hay.as_ptr() as *const __m256i) as u32) & 0xff;
                    assert_eq!(m, 0);
                }
                "asm_sound_32b" => {
                    let m = load32_asm_mask(shared.hay.as_ptr(), 0xff);
                    assert_eq!(m, 0);
                }
                "asm_off_by_one_32b" => {
                    let m = load32_asm_mask(shared.hay.as_ptr(), 0x1ff);
                    if (m & 0x100) != 0 {
                        leaked_hits += 1;
                    }
                }
                _ => panic!("bad mode"),
            }
        }
        DONE.store(true, Ordering::Relaxed);
        assert_eq!(pthread_join(th, core::ptr::null_mut()), 0);
        println!("LEAKED_HITS={}", leaked_hits);
    }
}
"""


CSE_RUST_SRC = r"""
use std::arch::asm;

#[inline(always)]
unsafe fn memchr_readonly_only_off_by_one(needle: u8, hay: &[u8]) -> isize {
    let mask: u32;
    let bad_len = hay.len() + 1;
    unsafe {
        asm!(
            "vmovd {xn:x}, {needle:e}",
            "vpbroadcastb {xn:y}, {xn:x}",
            "mov {algn}, {ptr}",
            "and {algn}, -32",
            "mov {mis:e}, {ptr:e}",
            "and {mis:e}, 31",
            "vmovdqa {yd:y}, [{algn}]",
            "vpcmpeqb {yd:y}, {yd:y}, {xn:y}",
            "vpmovmskb {m:e}, {yd:y}",
            "shrx {m:e}, {m:e}, {mis:e}",
            "bzhi {m:e}, {m:e}, {len:e}",
            ptr = in(reg) hay.as_ptr(),
            len = in(reg) bad_len,
            needle = in(reg) needle as u32,
            algn = out(reg) _,
            mis = out(reg) _,
            m = out(reg) mask,
            xn = out(ymm_reg) _,
            yd = out(ymm_reg) _,
            options(readonly, nostack),
        );
    }
    if mask == 0 { -1 } else { mask.trailing_zeros() as isize }
}

#[inline(always)]
unsafe fn memchr_pure_readonly_sound(needle: u8, hay: &[u8]) -> isize {
    let mask: u32;
    unsafe {
        asm!(
            "vmovd {xn:x}, {needle:e}",
            "vpbroadcastb {xn:y}, {xn:x}",
            "mov {algn}, {ptr}",
            "and {algn}, -32",
            "mov {mis:e}, {ptr:e}",
            "and {mis:e}, 31",
            "vmovdqa {yd:y}, [{algn}]",
            "vpcmpeqb {yd:y}, {yd:y}, {xn:y}",
            "vpmovmskb {m:e}, {yd:y}",
            "shrx {m:e}, {m:e}, {mis:e}",
            "bzhi {m:e}, {m:e}, {len:e}",
            ptr = in(reg) hay.as_ptr(),
            len = in(reg) hay.len(),
            needle = in(reg) needle as u32,
            algn = out(reg) _,
            mis = out(reg) _,
            m = out(reg) mask,
            xn = out(ymm_reg) _,
            yd = out(ymm_reg) _,
            options(pure, readonly, nostack),
        );
    }
    if mask == 0 { -1 } else { mask.trailing_zeros() as isize }
}

#[inline(always)]
unsafe fn memchr_pure_readonly_off_by_one(needle: u8, hay: &[u8]) -> isize {
    let mask: u32;
    let bad_len = hay.len() + 1;
    unsafe {
        asm!(
            "vmovd {xn:x}, {needle:e}",
            "vpbroadcastb {xn:y}, {xn:x}",
            "mov {algn}, {ptr}",
            "and {algn}, -32",
            "mov {mis:e}, {ptr:e}",
            "and {mis:e}, 31",
            "vmovdqa {yd:y}, [{algn}]",
            "vpcmpeqb {yd:y}, {yd:y}, {xn:y}",
            "vpmovmskb {m:e}, {yd:y}",
            "shrx {m:e}, {m:e}, {mis:e}",
            "bzhi {m:e}, {m:e}, {len:e}",
            ptr = in(reg) hay.as_ptr(),
            len = in(reg) bad_len,
            needle = in(reg) needle as u32,
            algn = out(reg) _,
            mis = out(reg) _,
            m = out(reg) mask,
            xn = out(ymm_reg) _,
            yd = out(ymm_reg) _,
            options(pure, readonly, nostack),
        );
    }
    if mask == 0 { -1 } else { mask.trailing_zeros() as isize }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn caller_readonly_no_pure_buggy_pair(x: &[u8; 16], y: &mut [u8; 16], needle: u8) -> (isize, isize) {
    unsafe {
        let r1 = memchr_readonly_only_off_by_one(needle, x);
        y[0] = needle;
        let r2 = memchr_readonly_only_off_by_one(needle, x);
        (r1, r2)
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn caller_pure_readonly_sound_pair(x: &[u8; 16], y: &mut [u8; 16], needle: u8) -> (isize, isize) {
    unsafe {
        let r1 = memchr_pure_readonly_sound(needle, x);
        y[0] = needle;
        let r2 = memchr_pure_readonly_sound(needle, x);
        (r1, r2)
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn caller_pure_readonly_buggy_pair(x: &[u8; 16], y: &mut [u8; 16], needle: u8) -> (isize, isize) {
    unsafe {
        let r1 = memchr_pure_readonly_off_by_one(needle, x);
        y[0] = needle;
        let r2 = memchr_pure_readonly_off_by_one(needle, x);
        (r1, r2)
    }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn fresh_call_sound(x: &[u8; 16], needle: u8) -> isize {
    unsafe { memchr_pure_readonly_sound(needle, x) }
}

#[unsafe(no_mangle)]
#[inline(never)]
pub fn fresh_call_buggy(x: &[u8; 16], needle: u8) -> isize {
    unsafe { memchr_pure_readonly_off_by_one(needle, x) }
}

#[repr(C, align(32))]
struct Adj32 {
    x: [u8; 16],
    y: [u8; 16],
}

fn main() {
    let mut pair1 = core::hint::black_box(Adj32 { x: [0x11; 16], y: [0x22; 16] });
    let (s1, s2) = caller_pure_readonly_sound_pair(&pair1.x, &mut pair1.y, 0xA5);
    let s3_fresh = fresh_call_sound(&pair1.x, 0xA5);

    let mut pair2 = core::hint::black_box(Adj32 { x: [0x11; 16], y: [0x22; 16] });
    let (b1, b2_csed) = caller_pure_readonly_buggy_pair(&pair2.x, &mut pair2.y, 0xA5);
    let b3_fresh = fresh_call_buggy(&pair2.x, 0xA5);

    let mut pair3 = core::hint::black_box(Adj32 { x: [0x11; 16], y: [0x22; 16] });
    let (ro1, ro2) = caller_readonly_no_pure_buggy_pair(&pair3.x, &mut pair3.y, 0xA5);

    println!(
        "{{\"sound_pure_readonly_pair\":[{},{}],\"sound_fresh_after_mutation\":{},\"buggy_pure_readonly_csed_pair\":[{},{}],\"buggy_fresh_after_mutation\":{},\"buggy_readonly_no_pure_pair\":[{},{}]}}",
        s1, s2, s3_fresh, b1, b2_csed, b3_fresh, ro1, ro2
    );
}
"""


def run_checked(cmd: list[str]) -> subprocess.CompletedProcess[str]:
    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode != 0:
        sys.stderr.write(
            f"FAILED: {' '.join(cmd)}\nSTDOUT:\n{r.stdout}\nSTDERR:\n{r.stderr}\n"
        )
        raise SystemExit(r.returncode)
    return r


def count_fn_vmovdqa(asm_text: str, fn_name: str) -> int:
    m = re.search(
        rf"(?ms)^{re.escape(fn_name)}:\n(.*?)(?:^\.Lfunc_end|\Z)",
        asm_text,
    )
    if not m:
        return -1
    return len(re.findall(r"\bvmovdqa\b", m.group(1)))


def main() -> int:
    out_json_path = (
        Path(__file__).resolve().parent
        / "probe_x86_overread_sanitizers_and_cse_results.json"
    )
    results: dict[str, object] = {}

    with tempfile.TemporaryDirectory() as td:
        tdp = Path(td)

        # 1. Guard-page & negative canary probe on rustc +1.99.1
        gp_src = tdp / "guard_probe.rs"
        gp_bin = tdp / "guard_probe"
        gp_src.write_text(GUARD_PAGE_RUST_SRC, encoding="utf-8")
        t0 = time.monotonic()
        run_checked(
            ["rustc", "+1.99.1", "-C", "opt-level=3", str(gp_src), "-o", str(gp_bin)]
        )
        compile_ms = (time.monotonic() - t0) * 1000.0
        r_run = run_checked([str(gp_bin)])
        gp_data = json.loads(r_run.stdout.strip())
        gp_data["compile_ms"] = round(compile_ms, 2)
        results["guard_page_and_canaries"] = gp_data

        # 2. ASan probe on rustc +nightly
        asan_src = tdp / "asan_probe.rs"
        asan_bin = tdp / "asan_probe"
        asan_src.write_text(ASAN_RUST_SRC, encoding="utf-8")
        run_checked(
            [
                "rustc",
                "+nightly",
                "-Zsanitizer=address",
                "-C",
                "opt-level=2",
                str(asan_src),
                "-o",
                str(asan_bin),
            ]
        )
        asan_modes = [
            "asm_stack_and_heap",
            "intrinsic_stack",
            "intrinsic_heap",
            "intrinsic_nosan_calls_core",
            "deref32_nosan_direct",
            "interior_granule_256b_blindspot",
        ]
        asan_out: dict[str, object] = {}
        env_asan = dict(os.environ)
        env_asan["ASAN_OPTIONS"] = "detect_stack_use_after_return=1:detect_leaks=0"
        for mode in asan_modes:
            rr = subprocess.run(
                [str(asan_bin), mode],
                capture_output=True,
                text=True,
                env=env_asan,
            )
            err_first = ""
            for line in rr.stderr.splitlines():
                if "ERROR: AddressSanitizer:" in line:
                    err_first = line.strip()
                    err_first = re.sub(r"0x[0-9a-fA-F]+", "0xADDR", err_first)
                    err_first = re.sub(r"==\d+==", "==PID==", err_first)
                    break
            asan_out[mode] = {
                "rc": rr.returncode,
                "asan_error": err_first,
            }
        results["asan_probe"] = asan_out

        # 3. TSan probe on rustc +nightly
        tsan_src = tdp / "tsan_probe.rs"
        tsan_out_dir = tdp / "tsan_out"
        tsan_out_dir.mkdir()
        tsan_src.write_text(TSAN_RUST_SRC, encoding="utf-8")
        run_checked(
            [
                "rustc",
                "+nightly",
                "-Zsanitizer=thread",
                "-Cunsafe-allow-abi-mismatch=sanitizer",
                "-C",
                "opt-level=2",
                "--emit=llvm-ir,link",
                "--out-dir",
                str(tsan_out_dir),
                str(tsan_src),
            ]
        )
        tsan_ll = (tsan_out_dir / "tsan_probe.ll").read_text(encoding="utf-8")
        m_ts16 = re.search(r"(?ms)^define [^\n]*@load16_sse2\(.*?^\}", tsan_ll)
        m_ts32 = re.search(r"(?ms)^define [^\n]*@load32_avx2\(.*?^\}", tsan_ll)
        tsan_bin = tsan_out_dir / "tsan_probe"
        tsan_out: dict[str, object] = {
            "load16_sse2_has_tsan_read16_in_ir": bool(
                m_ts16 and "@__tsan_read16" in m_ts16.group(0)
            ),
            "load32_avx2_has_any_tsan_read_in_ir": bool(
                m_ts32 and "@__tsan_read" in m_ts32.group(0)
            ),
        }
        for mode in [
            "sse2_16b_intrinsic",
            "avx2_32b_intrinsic",
            "asm_sound_32b",
            "asm_off_by_one_32b",
        ]:
            rr = subprocess.run([str(tsan_bin), mode], capture_output=True, text=True)
            has_race = "WARNING: ThreadSanitizer: data race" in rr.stderr
            leaked = 0
            m_leak = re.search(r"LEAKED_HITS=(\d+)", rr.stdout)
            if m_leak:
                leaked = int(m_leak.group(1))
            tsan_out[mode] = {
                "rc": rr.returncode,
                "tsan_race_reported": has_race,
                "leaked_concurrent_hits": leaked,
            }
        results["tsan_probe"] = tsan_out

        # 4. LLVM CSE / GVN probe on rustc +1.99.1 and +nightly
        cse_src = tdp / "cse_probe.rs"
        cse_src.write_text(CSE_RUST_SRC, encoding="utf-8")
        cse_out: dict[str, object] = {}
        for tc in ["1.99.1", "nightly"]:
            out_dir = tdp / f"cse_{tc}"
            out_dir.mkdir()
            cse_bin = out_dir / "cse_probe"
            run_checked(
                [
                    "rustc",
                    f"+{tc}",
                    "-C",
                    "opt-level=3",
                    "-C",
                    "target-feature=+avx2,+bmi1,+bmi2",
                    "--emit=llvm-ir,asm,link",
                    str(cse_src),
                    "-o",
                    str(cse_bin),
                ]
            )
            asm_text = (out_dir / "cse_probe.s").read_text(encoding="utf-8")
            ll_text = (out_dir / "cse_probe.ll").read_text(encoding="utf-8")
            rr = run_checked([str(cse_bin)])
            run_json = json.loads(rr.stdout.strip())
            cse_out[tc] = {
                "run": run_json,
                "vmovdqa_count": {
                    "caller_readonly_no_pure_buggy_pair": count_fn_vmovdqa(
                        asm_text, "caller_readonly_no_pure_buggy_pair"
                    ),
                    "caller_pure_readonly_sound_pair": count_fn_vmovdqa(
                        asm_text, "caller_pure_readonly_sound_pair"
                    ),
                    "caller_pure_readonly_buggy_pair": count_fn_vmovdqa(
                        asm_text, "caller_pure_readonly_buggy_pair"
                    ),
                },
                "pure_readonly_drops_sideeffect_in_ir": (
                    "asm inteldialect" in ll_text and "asm sideeffect inteldialect" in ll_text
                ),
            }
        results["llvm_cse_probe"] = cse_out

    # Deterministic assertions
    assert gp_data["full_grid_pairs"] == 532480
    assert gp_data["canary1_dangling_empty_sigsegv"] is True
    assert gp_data["canary2_page_end_empty_sigsegv"] is True
    assert gp_data["canary3_unaligned_len1_sigsegv"] is True
    assert gp_data["canary4_bsf_zero_mask_got"] == 0
    assert gp_data["canary4_sound_got"] == -1
    assert asan_out["asm_stack_and_heap"]["rc"] == 0
    assert asan_out["intrinsic_stack"]["rc"] != 0
    assert asan_out["intrinsic_heap"]["rc"] != 0
    assert asan_out["intrinsic_nosan_calls_core"]["rc"] != 0
    assert asan_out["deref32_nosan_direct"]["rc"] == 0
    assert asan_out["interior_granule_256b_blindspot"]["rc"] == 0
    assert tsan_out["load16_sse2_has_tsan_read16_in_ir"] is True
    assert tsan_out["load32_avx2_has_any_tsan_read_in_ir"] is False
    assert tsan_out["sse2_16b_intrinsic"]["rc"] == 66
    assert tsan_out["avx2_32b_intrinsic"]["rc"] == 0
    assert tsan_out["asm_sound_32b"]["rc"] == 0
    assert tsan_out["asm_sound_32b"]["leaked_concurrent_hits"] == 0
    assert tsan_out["asm_off_by_one_32b"]["rc"] == 0
    assert tsan_out["asm_off_by_one_32b"]["leaked_concurrent_hits"] > 0
    for tc in ["1.99.1", "nightly"]:
        assert cse_out[tc]["run"]["sound_pure_readonly_pair"] == [-1, -1]
        assert cse_out[tc]["run"]["buggy_pure_readonly_csed_pair"] == [-1, -1]
        assert cse_out[tc]["run"]["buggy_fresh_after_mutation"] == 16
        assert cse_out[tc]["run"]["buggy_readonly_no_pure_pair"] == [-1, 16]

    out_json_path.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(results, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
