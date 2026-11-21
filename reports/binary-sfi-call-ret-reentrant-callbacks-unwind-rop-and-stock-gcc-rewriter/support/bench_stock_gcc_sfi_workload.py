#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""
End-to-end empirical benchmark and containment verifier for `sfi_gcc_rewriter.py`
on stock `gcc 15.2.0 -O2` multi-function C code linked into a `rustc 1.99.1`
host inside a `4 GiB + 2 * 64 KiB PROT_NONE` Linux `mmap` arena:

  - Workload: 5-function C module (`sfi_opcode_mix` 8-way PIC jump table,
    `sfi_checksum64` 64-bit polynomial mixer, `sfi_rle64_decompress_and_stream`
    LZ4/RLE back-reference block decompressor invoking intra-sandbox callees +
    streaming `extern "C-unwind"` Rust callback, `sfi_test_trunc64_offset`, and
    `sfi_test_corrupt_guest_ret`).
  - Compares native `gcc 15.2.0 -O2` vs. stock-GCC SFI-rewritten `.o` on:
      1. Exact bit-for-bit output equivalence across all 8 switch arms and
         `64 KiB` (`8,192`-word) compressed RLE + back-reference blocks;
      2. Throughput (`MB/s` and `ns/iter` over `2,000` iterations = `128 MiB`
         decompressed + checksummed per mode) and `.text` code-size expansion;
      3. Live hardware 64-bit pointer truncation (`offset = 0x1_0002_0080`
         confined to `r14 + 0x20080`), corrupted guest return-slot confinement
         (`outside_sandbox_sentinel` unreachable), and streaming callback
         `panic!()` recovery via Jump-Over FDE;
      4. Exports exact `.text.sfi` bytes (`2,048` bytes, `64` bundles) into
         `stock_gcc_sfi_benchmark_results.json` for Lean `v4.34.1` kernel
         `checkSfiPicMultiFn = true := rfl` verification.
"""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import sfi_gcc_rewriter as rw  # noqa: E402


WORKLOAD_C_TEMPLATE = r"""
#include <stdint.h>

#ifdef NATIVE_MODE
#define ARENA_PTR(base, off) ((uint64_t *)((uintptr_t)(base) + (uint32_t)(off)))
extern uint64_t native_hostcall(uint64_t tag, uint64_t a0, uint64_t a1);
#else
#define ARENA_PTR(base, off) ((uint64_t *)(uintptr_t)(uint32_t)(off))
extern uint64_t sfi_hostcall(uint64_t tag, uint64_t a0, uint64_t a1);
#endif

__attribute__((noinline))
uint64_t FUNC(opcode_mix)(uint64_t op, uint64_t x, uint64_t y) {
    switch (op & 7) {
        case 0: return (x + y) ^ 0x9e3779b97f4a7c15ULL;
        case 1: return (x * 0x517cc1b727220a95ULL) + y;
        case 2: return (x << 13) | (y >> 7);
        case 3: return (x ^ y) * 33ULL;
        case 4: return (x - y) + (x >> 3);
        case 5: return (x & 0xff00ff00ff00ff00ULL) | (y & 0x00ff00ff00ff00ffULL);
        case 6: return (x + (y << 5)) ^ (x >> 11);
        default: return x ^ (y * 7ULL);
    }
}

__attribute__((noinline))
uint64_t FUNC(checksum64)(
#ifdef NATIVE_MODE
    uint8_t *arena_base,
#endif
    uint32_t words_off, uint64_t count, uint64_t seed
) {
    const uint64_t *words = ARENA_PTR(arena_base, words_off);
    uint64_t acc = seed;
    for (uint64_t i = 0; i < count; i++) {
        uint64_t w = words[i];
        acc = (acc ^ w) * 0x2545F4914F6CDD1DULL;
        acc ^= (acc >> 27);
    }
    return acc;
}

__attribute__((noinline))
uint64_t FUNC(rle64_decompress_and_stream)(
#ifdef NATIVE_MODE
    uint8_t *arena_base,
#endif
    uint32_t src_off, uint64_t src_words,
    uint32_t dst_off, uint64_t dst_cap_words,
    uint64_t cb_tag
) {
    const uint64_t *src = ARENA_PTR(arena_base, src_off);
    uint64_t *dst = ARENA_PTR(arena_base, dst_off);
    uint64_t si = 0, di = 0;
    while (si + 2 <= src_words) {
        uint64_t ctrl = src[si++];
        uint64_t val_or_off = src[si++];
        uint64_t tag = ctrl >> 32;
        uint64_t count = ctrl & 0xffffffffULL;
        if (di + count > dst_cap_words) break;
        if (tag == 0) {
            for (uint64_t k = 0; k < count; k++) {
                dst[di++] = val_or_off;
            }
        } else {
            if (val_or_off == 0 || val_or_off > di) break;
            uint64_t back = di - val_or_off;
            for (uint64_t k = 0; k < count; k++) {
                dst[di++] = dst[back + k];
            }
        }
    }
#ifdef NATIVE_MODE
    uint64_t csum = FUNC(checksum64)(arena_base, dst_off, di, 0xcbf29ce484222325ULL);
    uint64_t mixed = FUNC(opcode_mix)(di, csum, src_words);
    uint64_t cb_res = native_hostcall(cb_tag, di, mixed);
#else
    uint64_t csum = FUNC(checksum64)(dst_off, di, 0xcbf29ce484222325ULL);
    uint64_t mixed = FUNC(opcode_mix)(di, csum, src_words);
    uint64_t cb_res = sfi_hostcall(cb_tag, di, mixed);
#endif
    return mixed ^ cb_res;
}

#ifndef NATIVE_MODE
/* Boundary Test 1: 64-bit out-of-range pointer `bad_ptr64` (`>= 4 GiB`) is
 * truncated to its low 32 bits (`movl %edi, %r11d`) inside `[r14, r14 + 4 GiB)`! */
__attribute__((noinline))
uint64_t sfi_test_trunc64_store(uint64_t bad_ptr64, uint64_t marker) {
    volatile uint64_t *p = (volatile uint64_t *)(uintptr_t)bad_ptr64;
    *p = marker;
    return *p ^ 0x11ULL;
}

/* Boundary Test 2: Guest function attempts to overwrite all nearby guest-stack
 * slots (including its own return-offset slot) with a 64-bit host sentinel
 * address; masked PIC `ret` confines target to `r15 + (val32 & code_mask)`! */
__attribute__((noinline))
uint64_t sfi_test_corrupt_guest_stack_slot(uint32_t approx_sp_off, uint64_t host_addr) {
    volatile uint64_t *slot = (volatile uint64_t *)(uintptr_t)approx_sp_off;
    /* Overwrite return slot with offset 0 (Portal 0) OR arbitrary high bits `(host_addr & ~0x7ffULL) | 0ULL`
     * to verify upper 32+ bits of `host_addr` are stripped cleanly by `movl` + `andl $code_mask`! */
    *slot = (host_addr & 0xfffffffffffff800ULL);
    return 0x778899ULL;
}
#endif
"""


RUST_BENCH_DRIVER_RS = r"""
#![allow(function_casts_as_integer)]
use std::arch::global_asm;
use std::panic::{self, AssertUnwindSafe};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Instant;

static STREAM_CB_ACCUM: AtomicU64 = AtomicU64::new(0);

#[no_mangle]
pub extern "C" fn outside_sandbox_sentinel() -> ! {
    eprintln!("UNEXPECTED_SENTINEL_REACHED");
    std::process::exit(99);
}

#[no_mangle]
pub extern "C" fn native_hostcall(tag: u64, words: u64, mixed: u64) -> u64 {
    let v = words.wrapping_mul(31) ^ (mixed >> 17) ^ tag;
    STREAM_CB_ACCUM.fetch_add(1, Ordering::Relaxed);
    v
}

#[repr(C)]
pub struct SfiContext {
    pub code_base: u64,
    pub arena_base: u64,
    pub code_mask: u32,
    pub guest_sp: u32,
    pub cb_fn: extern "C-unwind" fn(*mut SfiContext, u64, u64, u64) -> u64,
}

global_asm!(
    r#"
    .text
    .globl sfi_enter5_trampoline
    .type sfi_enter5_trampoline, @function
sfi_enter5_trampoline:
    .cfi_startproc
    # System V args:
    #   rdi = *mut SfiContext
    #   rsi = entry_bundle_off
    #   rdx = guest_a0 (rdi)
    #   rcx = guest_a1 (rsi)
    #   r8  = guest_a2 (rdx)
    #   r9  = guest_a3 (rcx)
    #   16(%rsp) before pushes = 8(%rsp) at entry = guest_a4 (r8)
    movq 8(%rsp), %r10          # fetch 7th arg `guest_a4` before pushing CSRs!
    pushq %rbp
    .cfi_adjust_cfa_offset 8
    .cfi_offset rbp, -16
    pushq %rbx
    .cfi_adjust_cfa_offset 8
    .cfi_offset rbx, -24
    pushq %r12
    .cfi_adjust_cfa_offset 8
    .cfi_offset r12, -32
    pushq %r13
    .cfi_adjust_cfa_offset 8
    .cfi_offset r13, -40
    pushq %r14
    .cfi_adjust_cfa_offset 8
    .cfi_offset r14, -48
    pushq %r15
    .cfi_adjust_cfa_offset 8
    .cfi_offset r15, -56
    subq $8, %rsp
    .cfi_adjust_cfa_offset 8

    movq %rdi, %r12
    movl %esi, %r11d
    movq 0(%r12), %r15
    movq 8(%r12), %r14
    movl 20(%r12), %r13d

    subl $8, %r13d
    movq $0, (%r14,%r13,1)
    andl 16(%r12), %r11d
    leaq (%r15,%r11,1), %rax

    movq %rdx, %rdi
    movq %rcx, %rsi
    movq %r8,  %rdx
    movq %r9,  %rcx
    movq %r10, %r8

    call *%rax

    addq $8, %rsp
    .cfi_adjust_cfa_offset -8
    popq %r15
    .cfi_adjust_cfa_offset -8
    popq %r14
    .cfi_adjust_cfa_offset -8
    popq %r13
    .cfi_adjust_cfa_offset -8
    popq %r12
    .cfi_adjust_cfa_offset -8
    popq %rbx
    .cfi_adjust_cfa_offset -8
    popq %rbp
    .cfi_adjust_cfa_offset -8
    ret
    .cfi_endproc

    .globl sfi_hostcall_trampoline
    .type sfi_hostcall_trampoline, @function
sfi_hostcall_trampoline:
    .cfi_startproc
    pushq %r13
    .cfi_adjust_cfa_offset 8

    leal -64(%r13), %eax
    movl %eax, 20(%r12)

    # Guest passed (tag=rdi, a0=rsi, a1=rdx) -> shift to (ctx=rdi, tag=rsi, a0=rdx, a1=rcx)
    movq %rdx, %rcx
    movq %rsi, %rdx
    movq %rdi, %rsi
    movq %r12, %rdi
    movq 24(%r12), %rax
    call *%rax

    popq %r13
    .cfi_adjust_cfa_offset -8

    movq 0(%r12), %r15
    movq 8(%r12), %r14
    movl (%r14,%r13,1), %r11d
    addl $8, %r13d
    andl 16(%r12), %r11d
    leaq (%r15,%r11,1), %r11
    jmp *%r11
    .cfi_endproc
"#,
    options(att_syntax)
);

extern "C-unwind" {
    fn sfi_enter5_trampoline(
        ctx: *mut SfiContext,
        entry_off: u64,
        a0: u64,
        a1: u64,
        a2: u64,
        a3: u64,
        a4: u64,
    ) -> u64;
}

extern "C" {
    fn native_opcode_mix(op: u64, x: u64, y: u64) -> u64;
    fn native_rle64_decompress_and_stream(
        arena_base: *mut u8,
        src_off: u32,
        src_words: u64,
        dst_off: u32,
        dst_cap_words: u64,
        cb_tag: u64,
    ) -> u64;

    fn __sfi_text_start();
    fn __sfi_rodata_start();
    fn __sfi_rodata_end();
    fn sfi_opcode_mix();
    fn sfi_rle64_decompress_and_stream();
    fn sfi_test_trunc64_store();
    fn sfi_test_corrupt_guest_stack_slot();

    #[link_name = "mmap"]
    fn libc_mmap(addr: *mut u8, len: usize, prot: i32, flags: i32, fd: i32, off: i64) -> *mut u8;
    #[link_name = "mprotect"]
    fn libc_mprotect(addr: *mut u8, len: usize, prot: i32) -> i32;
    #[link_name = "munmap"]
    fn libc_munmap(addr: *mut u8, len: usize) -> i32;
}

struct WatermarkGuard {
    ctx: *mut SfiContext,
    saved: u32,
}
impl Drop for WatermarkGuard {
    fn drop(&mut self) {
        unsafe { (*self.ctx).guest_sp = self.saved };
    }
}

unsafe fn sfi_call5(
    ctx: *mut SfiContext,
    fn_sym: unsafe extern "C" fn(),
    a0: u64,
    a1: u64,
    a2: u64,
    a3: u64,
    a4: u64,
) -> u64 {
    let saved = (*ctx).guest_sp;
    let _g = WatermarkGuard { ctx, saved };
    let off = (fn_sym as *const () as usize as u64) - (*ctx).code_base;
    sfi_enter5_trampoline(ctx, off, a0, a1, a2, a3, a4)
}

extern "C-unwind" fn sfi_stream_cb(_ctx: *mut SfiContext, tag: u64, words: u64, mixed: u64) -> u64 {
    if tag == 0xDEAD {
        panic!("mid_stream_validation_panic");
    }
    STREAM_CB_ACCUM.fetch_add(1, Ordering::Relaxed);
    words.wrapping_mul(31) ^ (mixed >> 17) ^ tag
}

/// Build deterministic compressed RLE + LZ4-style back-reference stream expanding
/// to `8,192` 64-bit words (`65,536` bytes = `64 KiB` per iteration).
fn build_compressed_stream() -> Vec<u64> {
    let mut stream = Vec::new();
    // 64 blocks * 128 words = 8,192 output words (64 KiB):
    // Alternate 64-word literal-run packet `(tag=0, count=64)` and 64-word sliding-window
    // back-reference packet `(tag=1, count=64, back_offset=64)`.
    for blk in 0..64u64 {
        let ctrl_run = (0u64 << 32) | 64u64;
        let val = 0x0102_0304_0506_0708u64.wrapping_mul(blk + 1) ^ 0xA5A5_5A5A_F0F0_0F0Fu64;
        stream.push(ctrl_run);
        stream.push(val);

        let ctrl_ref = (1u64 << 32) | 64u64;
        let back_off = 64u64;
        stream.push(ctrl_ref);
        stream.push(back_off);
    }
    stream
}

fn main() {
    unsafe {
        // Reserve `4 GiB + 2 * 64 KiB` PROT_NONE envelope via MAP_NORESERVE!
        const GUARD: usize = 65536;
        const ARENA_4G: usize = 1usize << 32;
        const ENV_TOTAL: usize = GUARD + ARENA_4G + GUARD;
        let env_base = libc_mmap(core::ptr::null_mut(), ENV_TOTAL, 0, 0x4022, -1, 0);
        assert!((env_base as usize) != usize::MAX, "4 GiB mmap reservation failed");
        let r14 = env_base.add(GUARD);

        // Commit `[r14 + 0x10000 .. r14 + 0x100000)` (`960 KiB`) RW for `.sfi_rodata`,
        // compressed input (`0x20000`), output (`0x30000`), and guest stack (`0xF0000`)!
        assert_eq!(libc_mprotect(r14.add(0x10000), 0xF0000, 0x3), 0);

        // Copy `.sfi_rodata` jump table into `r14 + 0x10000` and lock that page `PROT_READ`!
        let ro_start = __sfi_rodata_start as *const u8;
        let ro_len = (__sfi_rodata_end as usize) - (__sfi_rodata_start as usize);
        core::ptr::copy_nonoverlapping(ro_start, r14.add(0x10000), ro_len);
        assert_eq!(libc_mprotect(r14.add(0x10000), 4096, 0x1), 0); // PROT_READ jump table!

        // Allocate separate native buffer to compare bit-for-bit against SFI!
        let mut native_buf = vec![0u8; 0x100000];
        let stream = build_compressed_stream();
        let src_off: u32 = 0x20000;
        let dst_off: u32 = 0x30000;
        let dst_cap_words: u64 = 8192;

        core::ptr::copy_nonoverlapping(
            stream.as_ptr() as *const u8,
            r14.add(src_off as usize),
            stream.len() * 8,
        );
        core::ptr::copy_nonoverlapping(
            stream.as_ptr() as *const u8,
            native_buf.as_mut_ptr().add(src_off as usize),
            stream.len() * 8,
        );

        let mut ctx = SfiContext {
            code_base: __sfi_text_start as *const () as usize as u64,
            arena_base: r14 as u64,
            code_mask: 0x7E0,
            guest_sp: 0xF0000,
            cb_fn: sfi_stream_cb,
        };

        // 1. Verify all 8 `switch` jump-table arms (`op = 0..7`) match Native `-O2` bit-for-bit!
        for op in 0..8u64 {
            let x = 0x1234_5678_9ABC_DEF0u64.wrapping_mul(op + 3);
            let y = 0xFEDC_BA98_7654_3210u64 ^ op;
            let n_out = native_opcode_mix(op, x, y);
            let s_out = sfi_call5(&mut ctx, sfi_opcode_mix, op, x, y, 0, 0);
            assert_eq!(n_out, s_out, "opcode_mix mismatch on arm {}", op);
        }

        // 2. Verify full decompression + checksum + switch + streaming callback equivalence!
        let n_res = native_rle64_decompress_and_stream(
            native_buf.as_mut_ptr(),
            src_off,
            stream.len() as u64,
            dst_off,
            dst_cap_words,
            7,
        );
        let s_res = sfi_call5(
            &mut ctx,
            sfi_rle64_decompress_and_stream,
            src_off as u64,
            stream.len() as u64,
            dst_off as u64,
            dst_cap_words,
            7,
        );
        assert_eq!(n_res, s_res, "decompress+stream digest mismatch");
        let n_dst = core::slice::from_raw_parts(native_buf.as_ptr().add(dst_off as usize), 65536);
        let s_dst = core::slice::from_raw_parts(r14.add(dst_off as usize), 65536);
        assert_eq!(n_dst, s_dst, "64 KiB decompressed payload mismatch");

        // 3. Benchmark Native `-O2` vs. Stock-GCC Rewritten SFI `-O2` (`2,000` iters * `64 KiB` = `128 MiB`)
        const ITERS: u64 = 2000;
        // Warmup
        for _ in 0..50 {
            core::hint::black_box(native_rle64_decompress_and_stream(
                native_buf.as_mut_ptr(),
                src_off,
                stream.len() as u64,
                dst_off,
                dst_cap_words,
                7,
            ));
            core::hint::black_box(sfi_call5(
                &mut ctx,
                sfi_rle64_decompress_and_stream,
                src_off as u64,
                stream.len() as u64,
                dst_off as u64,
                dst_cap_words,
                7,
            ));
        }

        let t0 = Instant::now();
        let mut acc_n = 0u64;
        for i in 0..ITERS {
            acc_n ^= native_rle64_decompress_and_stream(
                native_buf.as_mut_ptr(),
                src_off,
                stream.len() as u64,
                dst_off,
                dst_cap_words,
                i & 3,
            );
        }
        let native_ns = t0.elapsed().as_nanos() as f64;

        let t1 = Instant::now();
        let mut acc_s = 0u64;
        for i in 0..ITERS {
            acc_s ^= sfi_call5(
                &mut ctx,
                sfi_rle64_decompress_and_stream,
                src_off as u64,
                stream.len() as u64,
                dst_off as u64,
                dst_cap_words,
                i & 3,
            );
        }
        let sfi_ns = t1.elapsed().as_nanos() as f64;
        assert_eq!(acc_n, acc_s);

        // 4. Boundary Containment Checks on live `4 GiB` SFI arena:
        //    (a) 64-bit pointer `0x0000_0001_0002_0080` (`> 4 GiB`, would escape arena without 32-bit zero-ext)
        //        is truncated by `movl` to `0x0002_0080` inside `[r14, r14 + 4 GiB)`!
        let trunc_ret = sfi_call5(
            &mut ctx,
            sfi_test_trunc64_store,
            0x0000_0001_0002_0080u64,
            0xCAFE_1234_5678_9ABCu64,
            0,
            0,
            0,
        );
        let stored_inside = *(r14.add(0x20080) as *const u64);
        assert_eq!(stored_inside, 0xCAFE_1234_5678_9ABCu64);
        assert_eq!(trunc_ret, 0xCAFE_1234_5678_9ABCu64 ^ 0x11);

        //    (b) Guest overwrites its own return slot `[r14 + 0xEFFFC]` (`0xF0000 - 8 = 0xEFFF8`)
        //        with high-bit host sentinel address `(sentinel & ~0x7ff)`: masked PIC `ret`
        //        strips upper bits and masks low bits to `0` (Portal 0), returning cleanly!
        let corrupt_ret = sfi_call5(
            &mut ctx,
            sfi_test_corrupt_guest_stack_slot,
            0xEFFF8,
            outside_sandbox_sentinel as *const () as usize as u64,
            0,
            0,
            0,
        );
        assert_eq!(corrupt_ret, 0x778899);

        //    (c) Streaming callback `panic!()` (`cb_tag = 0xDEAD`) mid-decompression unwinds
        //        cleanly via Jump-Over FDE and restores `ctx.guest_sp == 0xF0000`!
        let ctx_ptr = &mut ctx as *mut SfiContext;
        let caught = panic::catch_unwind(AssertUnwindSafe(|| {
            sfi_call5(
                ctx_ptr,
                sfi_rle64_decompress_and_stream,
                src_off as u64,
                stream.len() as u64,
                dst_off as u64,
                dst_cap_words,
                0xDEAD,
            )
        }))
        .is_err();
        assert!(caught);
        assert_eq!(ctx.guest_sp, 0xF0000);

        let total_mib = (ITERS as f64 * 65536.0) / (1024.0 * 1024.0);
        let native_mb_s = total_mib / (native_ns / 1e9);
        let sfi_mb_s = total_mib / (sfi_ns / 1e9);
        let overhead_pct = ((sfi_ns / native_ns) - 1.0) * 100.0;

        println!(
            concat!(
                "{{\"switch8_exact_match\": true, \"decompress_64kib_exact_match\": true, ",
                "\"iters\": {}, \"bytes_per_iter\": 65536, ",
                "\"native_ns_per_iter\": {:.2}, \"sfi_ns_per_iter\": {:.2}, ",
                "\"native_mib_per_s\": {:.2}, \"sfi_mib_per_s\": {:.2}, ",
                "\"sfi_runtime_overhead_pct\": {:.2}, ",
                "\"trunc64_confined\": true, \"corrupt_ret_confined\": true, ",
                "\"streaming_panic_caught_and_watermark_restored\": true}}"
            ),
            ITERS,
            native_ns / (ITERS as f64),
            sfi_ns / (ITERS as f64),
            native_mb_s,
            sfi_mb_s,
            overhead_pct
        );

        libc_munmap(env_base, ENV_TOTAL);
    }
}
"""


def extract_section_bytes(obj_path: Path, section_name: str) -> bytes:
    with tempfile.NamedTemporaryFile(delete=False) as tf:
        bin_out = Path(tf.name)
    try:
        subprocess.run(
            ["objcopy", "-O", "binary", "--only-section=" + section_name, str(obj_path), str(bin_out)],
            check=True,
        )
        return bin_out.read_bytes()
    finally:
        bin_out.unlink(missing_ok=True)


def count_objdump_insns(obj_path: Path, section_name: str, stop_sym: str | None = None) -> int:
    out = subprocess.run(
        ["objdump", "-d", "-j", section_name, str(obj_path)],
        capture_output=True,
        text=True,
        check=True,
    ).stdout
    cnt = 0
    for ln in out.splitlines():
        if stop_sym and f"<{stop_sym}>:" in ln:
            break
        if "\t" in ln and ln.lstrip()[0:1] in "0123456789abcdef":
            # Skip continuation lines of multi-byte NOPs that have no mnemonic column
            cols = ln.split("\t")
            if len(cols) >= 3 and cols[2].strip():
                cnt += 1
    return cnt


def main() -> int:
    with tempfile.TemporaryDirectory() as td_str:
        td = Path(td_str)

        # 1. Compile Native `-O2` object
        nat_c = td / "native_work.c"
        nat_o = td / "native_work.o"
        nat_c.write_text("#define NATIVE_MODE 1\n#define FUNC(n) native_##n\n" + WORKLOAD_C_TEMPLATE)
        subprocess.run(["gcc", "-O2", "-fno-tree-vectorize", "-c", str(nat_c), "-o", str(nat_o)], check=True)

        # 2. Compile Stock-GCC `-O2 -S` -> `sfi_gcc_rewriter.py` -> `sfi_work.o`
        sfi_c = td / "sfi_work.c"
        sfi_raw_s = td / "sfi_work_raw.s"
        sfi_rew_s = td / "sfi_work_bundled.s"
        sfi_o = td / "sfi_work.o"
        sfi_c.write_text("#define FUNC(n) sfi_##n\n" + WORKLOAD_C_TEMPLATE)
        gcc_flags = [
            "-O2",
            "-fPIC",
            "-fvisibility=hidden",
            "-fno-tree-vectorize",
            "-ffixed-rbp",
            "-ffixed-rbx",
            "-ffixed-r11",
            "-ffixed-r12",
            "-ffixed-r13",
            "-ffixed-r14",
            "-ffixed-r15",
            "-mno-red-zone",
            "-fno-stack-protector",
            "-fno-unwind-tables",
            "-fno-asynchronous-unwind-tables",
            "-fcf-protection=none",
        ]
        subprocess.run(["gcc", *gcc_flags, "-S", str(sfi_c), "-o", str(sfi_raw_s)], check=True)

        cfg = rw.RewriteConfig(code_size_pow2=2048)
        bundled_asm = rw.rewrite_gcc_att_to_sfi(sfi_raw_s.read_text(), cfg)
        sfi_rew_s.write_text(bundled_asm)
        subprocess.run(["gcc", "-c", str(sfi_rew_s), "-o", str(sfi_o)], check=True)

        # Inspect sizes, instruction counts, and relocation count
        nat_text = extract_section_bytes(nat_o, ".text")
        sfi_text = extract_section_bytes(sfi_o, ".text.sfi")
        sfi_rodata = extract_section_bytes(sfi_o, ".sfi_rodata")

        nm_out = subprocess.run(["nm", "-n", str(sfi_o)], capture_output=True, text=True, check=True).stdout
        used_end = 0
        for ln in nm_out.splitlines():
            if ln.endswith(" __sfi_text_used_end"):
                used_end = int(ln.split()[0], 16)
        assert len(sfi_text) == 2048, f"expected 2048B .text.sfi, got {len(sfi_text)}"

        rel_out = subprocess.run(["readelf", "-r", "-W", str(sfi_o)], capture_output=True, text=True, check=True).stdout
        rel_lines = [ln for ln in rel_out.splitlines() if "R_X86_64_" in ln]
        # Verify ONLY Portal Bundle 1 (`offset 0x21`) has a host relocation; 0 relocations in untrusted bundles >= 0x40!
        assert len(rel_lines) == 1 and "0000000000000021" in rel_lines[0], rel_lines

        nat_insns = count_objdump_insns(nat_o, ".text")
        sfi_used_insns = count_objdump_insns(sfi_o, ".text.sfi", stop_sym="__sfi_text_used_end")

        # 3. Link `native_work.o` + `sfi_work.o` into Rust benchmark & verification driver (`rustc +1.99.1 -C opt-level=3`)
        drv_rs = td / "bench_driver.rs"
        drv_bin = td / "bench_driver"
        drv_rs.write_text(RUST_BENCH_DRIVER_RS)
        subprocess.run(
            [
                "rustc",
                "+1.99.1",
                "-C",
                "opt-level=3",
                "-C",
                "panic=unwind",
                f"-Clink-arg={nat_o}",
                f"-Clink-arg={sfi_o}",
                str(drv_rs),
                "-o",
                str(drv_bin),
            ],
            check=True,
        )

        run_r = subprocess.run([str(drv_bin)], capture_output=True, text=True, check=True)
        bench_metrics = json.loads(run_r.stdout.strip())

        # Also extract the post-link `.text.sfi` bytes (or pre-link `.text.sfi` where Portal 1's rel32 is patched to 0
        # since Portal 0 and Portal 1 are trusted loader-synthesized bundles `[0x00..0x40)` while `[0x40..0x800)` are
        # 100% untrusted rewriter output with ZERO relocations!).
        gcc_ver = subprocess.run(["gcc", "--version"], capture_output=True, text=True, check=True).stdout.splitlines()[0]
        as_ver = subprocess.run(["as", "--version"], capture_output=True, text=True, check=True).stdout.splitlines()[0]

        res = {
            "gcc_version": gcc_ver,
            "gnu_as_version": as_ver,
            "rewriter_loc": len((HERE / "sfi_gcc_rewriter.py").read_text().splitlines()),
            "native_o2_text_bytes": len(nat_text),
            "native_o2_insns": nat_insns,
            "sfi_used_text_bytes": used_end,
            "sfi_padded_pow2_bytes": len(sfi_text),
            "sfi_used_bundles_32b": used_end // 32,
            "sfi_total_bundles_32b": len(sfi_text) // 32,
            "sfi_used_insns_incl_nops": sfi_used_insns,
            "sfi_rodata_bytes": len(sfi_rodata),
            "untrusted_bundle_relocations": 0,
            "portal_relocations": len(rel_lines),
            "code_size_ratio_used_vs_native": round(used_end / len(nat_text), 3),
            "live_4gib_arena_benchmark": bench_metrics,
            "sfi_text_hex_2048b": sfi_text.hex(),
        }

    (HERE / "stock_gcc_sfi_benchmark_results.json").write_text(json.dumps(res, indent=2) + "\n")
    summary = {k: v for k, v in res.items() if k != "sfi_text_hex_2048b"}
    print("STOCK_GCC_SFI_REWRITER_AND_BENCHMARK_PASSED")
    print(json.dumps(summary, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
