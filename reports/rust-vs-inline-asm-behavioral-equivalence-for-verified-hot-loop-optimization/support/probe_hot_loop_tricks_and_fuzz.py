#!/usr/bin/env python3
"""Executable equivalence, counterexample, and native OS guard-page fuzzing probes.

Demonstrates real (non-mocked) verification and counterexample discovery for
common hot-loop Rust-vs-ASM optimizations:
  1. Exhaustive 65,536-pair SWAR zero-byte detection (Mycroft vs borrow-free),
     reproducing `BurntSushi/memchr` `regression_count_new_lines` (`\\x0b\\n`).
  2. Exhaustive 65,536-input Granlund-Montgomery (PLDI 1994) division-by-constant
     magic multiply-shift verification (`u16` division by 3, 7, 10, 100) vs
     naive truncated multiplier failure.
  3. BMI2 `bzhi` (8-bit index masking wrap at 256 vs 64-bit shift) and x86
     `pshufb` `.rodata` LUT bit-7 zeroing corner cases.
  4. Native Linux x86_64 compiled Rust + inline `asm!` differential harness with
     real `mmap`/`mprotect(PROT_NONE)` leading and trailing guard pages catching
     a 1-byte page-boundary SIMD over-read (`SIGSEGV`) missed by normal heap
     unit tests, and verifying the fixed 4x-unrolled SSE2+scalar-tail kernel.

Uses `tempfile.TemporaryDirectory()` for all build artifacts.
"""

from __future__ import annotations

import json
import os
import signal
import subprocess
import tempfile
import time
from pathlib import Path

GUARD_PAGE_HARNESS_RS = r"""
use core::arch::asm;

// Minimal raw Linux x86_64 FFI to libc mmap / mprotect / munmap.
unsafe extern "C" {
    fn mmap(
        addr: *mut core::ffi::c_void,
        length: usize,
        prot: i32,
        flags: i32,
        fd: i32,
        offset: isize,
    ) -> *mut core::ffi::c_void;
    fn mprotect(addr: *mut core::ffi::c_void, len: usize, prot: i32) -> i32;
    fn munmap(addr: *mut core::ffi::c_void, length: usize) -> i32;
}

const PROT_NONE: i32 = 0;
const PROT_READ: i32 = 1;
const PROT_WRITE: i32 = 2;
const MAP_PRIVATE: i32 = 0x02;
const MAP_ANONYMOUS: i32 = 0x20;
const PAGE: usize = 4096;

/// Human-reviewed safe Rust reference specification.
#[inline(never)]
fn sum_u8_reference(slice: &[u8]) -> u64 {
    let mut acc: u64 = 0;
    for &b in slice {
        acc = acc.wrapping_add(b as u64);
    }
    acc
}

/// BUGGY agent-written inline ASM: reads 16 bytes via `movdqu` even when `0 < len < 16`,
/// then masks out the unused lanes. Produces the exact right value whenever the trailing
/// bytes happen to lie in mapped heap memory, but faults (`SIGSEGV`) at a page boundary!
#[inline(never)]
unsafe fn sum_u8_asm_buggy_overread(ptr: *const u8, len: usize) -> u64 {
    if len == 0 {
        return 0;
    }
    if len < 16 {
        let mut raw = [0u8; 16];
        unsafe {
            asm!(
                "movdqu xmm0, [{src}]",
                "movdqu [{dst}], xmm0",
                src = in(reg) ptr,
                dst = in(reg) raw.as_mut_ptr(),
                out("xmm0") _,
                options(nostack),
            );
        }
        let mut acc = 0u64;
        for b in &raw[..len] {
            acc = acc.wrapping_add(*b as u64);
        }
        return acc;
    }
    unsafe { sum_u8_asm_fixed(ptr, len) }
}

/// FIXED inline ASM kernel: 4x-unrolled 64-byte SSE2 `psadbw` + 16-byte loop +
/// exact scalar tail; zero bytes read outside `[ptr, ptr + len)`.
#[inline(never)]
unsafe fn sum_u8_asm_fixed(ptr: *const u8, len: usize) -> u64 {
    let mut acc: u64 = 0;
    let mut i: usize = 0;
    if len >= 64 {
        let chunks64 = len & !63usize;
        let partial: u64;
        unsafe {
            asm!(
                "pxor xmm0, xmm0",
                "pxor xmm1, xmm1",
                "pxor xmm5, xmm5",
                "2:",
                "movdqu xmm2, [{ptr} + {i}]",
                "movdqu xmm3, [{ptr} + {i} + 16]",
                "movdqu xmm4, [{ptr} + {i} + 32]",
                "movdqu xmm6, [{ptr} + {i} + 48]",
                "psadbw xmm2, xmm5",
                "psadbw xmm3, xmm5",
                "psadbw xmm4, xmm5",
                "psadbw xmm6, xmm5",
                "paddq xmm0, xmm2",
                "paddq xmm1, xmm3",
                "paddq xmm0, xmm4",
                "paddq xmm1, xmm6",
                "add {i}, 64",
                "cmp {i}, {end}",
                "jb 2b",
                "paddq xmm0, xmm1",
                "movhlps xmm1, xmm0",
                "paddq xmm0, xmm1",
                "movq {out}, xmm0",
                ptr = in(reg) ptr,
                i = inout(reg) i,
                end = in(reg) chunks64,
                out = out(reg) partial,
                out("xmm0") _,
                out("xmm1") _,
                out("xmm2") _,
                out("xmm3") _,
                out("xmm4") _,
                out("xmm5") _,
                out("xmm6") _,
                options(readonly, nostack),
            );
        }
        acc = acc.wrapping_add(partial);
    }
    if len - i >= 16 {
        let chunks16 = len & !15usize;
        let partial: u64;
        unsafe {
            asm!(
                "pxor xmm0, xmm0",
                "pxor xmm5, xmm5",
                "2:",
                "movdqu xmm2, [{ptr} + {i}]",
                "psadbw xmm2, xmm5",
                "paddq xmm0, xmm2",
                "add {i}, 16",
                "cmp {i}, {end}",
                "jb 2b",
                "movhlps xmm1, xmm0",
                "paddq xmm0, xmm1",
                "movq {out}, xmm0",
                ptr = in(reg) ptr,
                i = inout(reg) i,
                end = in(reg) chunks16,
                out = out(reg) partial,
                out("xmm0") _,
                out("xmm1") _,
                out("xmm2") _,
                out("xmm5") _,
                options(readonly, nostack),
            );
        }
        acc = acc.wrapping_add(partial);
    }
    while i < len {
        acc = acc.wrapping_add(unsafe { *ptr.add(i) } as u64);
        i += 1;
    }
    acc
}

struct GuardRegion {
    base: *mut u8,
}

impl GuardRegion {
    /// Allocates `[PROT_NONE (4 KiB) | RW (4 KiB) | PROT_NONE (4 KiB)]`.
    fn new() -> Self {
        unsafe {
            let p = mmap(
                core::ptr::null_mut(),
                3 * PAGE,
                PROT_READ | PROT_WRITE,
                MAP_PRIVATE | MAP_ANONYMOUS,
                -1,
                0,
            );
            assert!(!p.is_null() && p as isize != -1, "mmap failed");
            assert_eq!(mprotect(p, PAGE, PROT_NONE), 0);
            assert_eq!(mprotect(p.add(2 * PAGE), PAGE, PROT_NONE), 0);
            Self { base: p as *mut u8 }
        }
    }
    fn rw_start(&self) -> *mut u8 {
        unsafe { self.base.add(PAGE) }
    }
}

impl Drop for GuardRegion {
    fn drop(&mut self) {
        unsafe {
            let _ = munmap(self.base as *mut core::ffi::c_void, 3 * PAGE);
        }
    }
}

fn fill_pattern(buf: &mut [u8], seed: u8) {
    for (i, b) in buf.iter_mut().enumerate() {
        *b = ((i as u32).wrapping_mul(131).wrapping_add(seed as u32) ^ 0xA5) as u8;
    }
}

fn main() {
    let mode = std::env::args().nth(1).unwrap_or_else(|| "fixed".into());
    let edge_lens: &[usize] = &[
        0, 1, 2, 3, 7, 8, 9, 15, 16, 17, 31, 32, 33, 63, 64, 65, 127, 128, 129, 255, 256, 257,
    ];

    if mode == "heap_buggy" {
        // Demonstrates why naive heap Vec unit tests MISS the 16-byte SIMD over-read:
        // Allocator size classes (>= 16 B) or neighboring mapped heap pages prevent SIGSEGV.
        let mut passed = 0usize;
        for &len in edge_lens {
            let mut v = vec![0u8; len + 32]; // typical slice into larger heap buffer
            fill_pattern(&mut v[..len], 17);
            let r = sum_u8_reference(&v[..len]);
            let a = unsafe { sum_u8_asm_buggy_overread(v.as_ptr(), len) };
            assert_eq!(r, a);
            passed += 1;
        }
        println!("HEAP_BUGGY_PASSED={passed}");
        return;
    }

    let region = GuardRegion::new();
    let rw = region.rw_start();

    if mode == "guard_buggy" {
        // Right-align len=1 flush against the trailing PROT_NONE guard page -> instant SIGSEGV!
        let ptr = unsafe { rw.add(PAGE - 1) };
        unsafe { *ptr = 42; }
        let a = unsafe { sum_u8_asm_buggy_overread(ptr, 1) };
        println!("UNEXPECTED_SURVIVAL={a}");
        return;
    }

    // Mode "fixed": test ALL edge lengths x (trailing guard flush, leading guard flush,
    // and misaligned offsets 0..31).
    let mut total_checks = 0usize;
    for &len in edge_lens {
        // 1. Trailing-guard flush: slice occupies [PAGE - len .. PAGE)
        let trailing = unsafe { core::slice::from_raw_parts_mut(rw.add(PAGE - len), len) };
        fill_pattern(trailing, 1);
        let r1 = sum_u8_reference(trailing);
        let a1 = unsafe { sum_u8_asm_fixed(trailing.as_ptr(), len) };
        assert_eq!(r1, a1, "trailing mismatch at len={len}");
        total_checks += 1;

        // 2. Leading-guard flush: slice occupies [0 .. len)
        let leading = unsafe { core::slice::from_raw_parts_mut(rw, len) };
        fill_pattern(leading, 2);
        let r2 = sum_u8_reference(leading);
        let a2 = unsafe { sum_u8_asm_fixed(leading.as_ptr(), len) };
        assert_eq!(r2, a2, "leading mismatch at len={len}");
        total_checks += 1;

        // 3. Misaligned offsets 0..32
        for off in 0..32usize {
            let s = unsafe { core::slice::from_raw_parts_mut(rw.add(off), len) };
            fill_pattern(s, (off as u8).wrapping_add(3));
            let r3 = sum_u8_reference(s);
            let a3 = unsafe { sum_u8_asm_fixed(s.as_ptr(), len) };
            assert_eq!(r3, a3, "offset mismatch at len={len} off={off}");
            total_checks += 1;
        }
    }
    println!("FIXED_GUARD_CHECKS_PASSED={total_checks}");
}
"""


def probe_swar_exhaustive() -> dict[str, object]:
    """Exhaustively check all 65,536 2-byte words [0..255]^2 for SWAR find/rfind/count."""
    t0 = time.perf_counter()
    mycroft_find_err = 0
    mycroft_rfind_err = []
    mycroft_count_err = []
    bf_find_err = 0
    bf_rfind_err = 0
    bf_count_err = 0

    for b0 in range(256):
        for b1 in range(256):
            w = b0 | (b1 << 8)
            zeros = [i for i, b in enumerate((b0, b1)) if b == 0]
            ref_find = zeros[0] if zeros else None
            ref_rfind = zeros[-1] if zeros else None
            ref_count = len(zeros)

            # Classic Mycroft SWAR
            m_mask = ((w - 0x0101) & 0xFFFF) & (~w & 0xFFFF) & 0x8080
            m_idxs = [i for i in (0, 1) if (m_mask >> (8 * i + 7)) & 1]
            m_find = m_idxs[0] if m_idxs else None
            m_rfind = m_idxs[-1] if m_idxs else None
            m_count = len(m_idxs)
            if m_find != ref_find:
                mycroft_find_err += 1
            if m_rfind != ref_rfind:
                mycroft_rfind_err.append((b0, b1, ref_rfind, m_rfind))
            if m_count != ref_count:
                mycroft_count_err.append((b0, b1, ref_count, m_count))

            # Borrow-isolated SWAR: (~(((w & 0x7F7F) + 0x7F7F) | w | 0x7F7F)) & 0x8080
            bf_mask = (~((((w & 0x7F7F) + 0x7F7F) | w | 0x7F7F) & 0xFFFF)) & 0x8080
            bf_idxs = [i for i in (0, 1) if (bf_mask >> (8 * i + 7)) & 1]
            if (bf_idxs[0] if bf_idxs else None) != ref_find:
                bf_find_err += 1
            if (bf_idxs[-1] if bf_idxs else None) != ref_rfind:
                bf_rfind_err += 1
            if len(bf_idxs) != ref_count:
                bf_count_err += 1

    # Also verify BurntSushi/memchr exact regression_count_new_lines string:
    hay = b"01234567\x0b\n\x0b\n\x0b\n\x0b\nx"
    needle = ord("\n")
    # Check 8-byte aligned chunk hay[8:16] = b"\x0b\n\x0b\n\x0b\n\x0b\n"
    chunk = int.from_bytes(hay[8:16], "little")
    x = chunk ^ (needle * 0x0101_0101_0101_0101)
    mycroft_u64 = ((x - 0x0101_0101_0101_0101) & 0xFFFF_FFFF_FFFF_FFFF) & (~x & 0xFFFF_FFFF_FFFF_FFFF) & 0x8080_8080_8080_8080
    bf_u64 = (~((((x & 0x7F7F_7F7F_7F7F_7F7F) + 0x7F7F_7F7F_7F7F_7F7F) | x | 0x7F7F_7F7F_7F7F_7F7F) & 0xFFFF_FFFF_FFFF_FFFF)) & 0x8080_8080_8080_8080

    return {
        "domain_size_2byte": 65536,
        "mycroft_find_mismatches": mycroft_find_err,
        "mycroft_rfind_mismatches": len(mycroft_rfind_err),
        "mycroft_count_mismatches": len(mycroft_count_err),
        "mycroft_exact_counterexamples": mycroft_count_err,
        "borrow_free_find_mismatches": bf_find_err,
        "borrow_free_rfind_mismatches": bf_rfind_err,
        "borrow_free_count_mismatches": bf_count_err,
        "memchr_regression_chunk_true_count": hay[8:16].count(b"\n"),
        "memchr_regression_chunk_mycroft_count": mycroft_u64.bit_count(),
        "memchr_regression_chunk_borrow_free_count": bf_u64.bit_count(),
        "elapsed_ms": round((time.perf_counter() - t0) * 1000.0, 2),
    }


def probe_div_by_const_exhaustive() -> dict[str, object]:
    """Exhaustively check all 65,536 u16 inputs for Granlund-Montgomery div-by-const."""
    t0 = time.perf_counter()
    res: dict[str, object] = {}

    # 1. d = 3: simple mulhi M = ceil(2^17 / 3) = 0xAAAB, shift = 1
    m3_err = sum(1 for n in range(65536) if (((n * 0xAAAB) >> 17) != n // 3))
    # 2. d = 10: simple mulhi M = ceil(2^19 / 10) = 0xCCCD, shift = 3
    m10_err = sum(1 for n in range(65536) if (((n * 0xCCCD) >> 19) != n // 10))
    # 3. d = 100: naive M = ceil(2^22 / 100) = 0xA3D8, shift = 6 FAILS above n >= 43799!
    #    Exact Granlund-Montgomery pre-shift by 2 (100 = 4 * 25): ((n >> 2) * 0xA3D8) >> 20!
    m100_naive_err = 0
    m100_naive_first = None
    m100_fixed_err = 0
    for n in range(65536):
        naive = (n * 0xA3D8) >> 22
        if naive != n // 100:
            m100_naive_err += 1
            if m100_naive_first is None:
                m100_naive_first = (n, n // 100, naive)
        fixed = ((n >> 2) * 0xA3D8) >> 20
        if fixed != n // 100:
            m100_fixed_err += 1
    # 4. d = 7: requires 17-bit magic M = ceil(2^18 / 7) = 0x12493 = 2^16 + 0x2493!
    #    Granlund-Montgomery add-shift: q = (n * 0x2493) >> 16; t = ((n - q) >> 1) + q; t >> 2
    gm7_err = 0
    naive7_err = 0
    naive7_first = None
    for n in range(65536):
        q = (n * 0x2493) >> 16
        gm = (((n - q) >> 1) + q) >> 2
        if gm != n // 7:
            gm7_err += 1
        # Buggy agent truncation: using floor(2^18 / 7) / 4 = 0x9249 (`(n * 0x9249) >> 18`)
        # or rounding 0x924A without noticing 0x9249 under-estimates at n = 7*k!
        naive_floor = (n * 0x9249) >> 18
        if naive_floor != n // 7:
            naive7_err += 1
            if naive7_first is None:
                naive7_first = (n, n // 7, naive_floor)
    # Also test naive_ceil M = 0x924A at u16: (n * 0x924A) >> 18 over-estimates!
    naive7_ceil_first = None
    naive7_ceil_err = 0
    for n in range(65536):
        nc = (n * 0x924A) >> 18
        if nc != n // 7:
            naive7_ceil_err += 1
            if naive7_ceil_first is None:
                naive7_ceil_first = (n, n // 7, nc)

    res = {
        "domain_size_u16": 65536,
        "d3_mulhi_mismatches": m3_err,
        "d10_mulhi_mismatches": m10_err,
        "d100_naive_mulhi_mismatches": m100_naive_err,
        "d100_naive_first_cex": m100_naive_first,
        "d100_preshift_fixed_mismatches": m100_fixed_err,
        "d7_gm_addshift_mismatches": gm7_err,
        "d7_naive_floor_0x9249_mismatches": naive7_err,
        "d7_naive_floor_first_cex": naive7_first,
        "d7_naive_ceil_0x924A_mismatches": naive7_ceil_err,
        "d7_naive_ceil_first_cex": naive7_ceil_first,
        "elapsed_ms": round((time.perf_counter() - t0) * 1000.0, 2),
    }
    return res


def probe_bmi2_and_pshufb() -> dict[str, object]:
    """Exact ISA corner cases for x86 BMI2 `bzhi` and SSSE3/AVX2 `pshufb` LUT."""
    # BMI2 BZHI r64, r64, r64 (Intel SDM Vol. 2A):
    #   n := SRC2[7:0] (8-bit unsigned!); DEST := SRC1; IF n < 64: DEST[63:n] := 0
    def bzhi64(src: int, idx: int) -> int:
        n = idx & 0xFF
        if n >= 64:
            return src & 0xFFFF_FFFF_FFFF_FFFF
        return src & ((1 << n) - 1)

    def rust_ref_low_bits(src: int, idx: int) -> int:
        if idx >= 64:
            return src & 0xFFFF_FFFF_FFFF_FFFF
        return src & ((1 << idx) - 1)

    bzhi_diverge_at_256 = (
        bzhi64(0xFFFF_FFFF_FFFF_FFFF, 256),
        rust_ref_low_bits(0xFFFF_FFFF_FFFF_FFFF, 256),
    )

    # PSHUFB LUT: lut[0..16] = [1..=16]; byte b with MSB=1 zeroes lane instead of lut[b & 0x0F]
    lut = [i + 1 for i in range(16)]
    pshufb_mismatches = 0
    first_pshufb_cex = None
    for b in range(256):
        ref_val = lut[b & 0x0F]
        hw_val = 0 if (b & 0x80) else lut[b & 0x0F]
        if hw_val != ref_val:
            pshufb_mismatches += 1
            if first_pshufb_cex is None:
                first_pshufb_cex = (b, ref_val, hw_val)

    return {
        "bzhi64_vs_ref_at_idx_64": (bzhi64(0xDEAD_BEEF, 64), rust_ref_low_bits(0xDEAD_BEEF, 64)),
        "bzhi64_vs_ref_at_idx_256": bzhi_diverge_at_256,
        "pshufb_unmasked_index_mismatches_out_of_256": pshufb_mismatches,
        "pshufb_first_cex": first_pshufb_cex,
    }


def probe_native_guard_page_harness() -> dict[str, object]:
    """Compile and run real Rust + x86_64 inline ASM with OS PROT_NONE guard pages."""
    with tempfile.TemporaryDirectory(prefix="anneal_guard_probe_") as td:
        tmp = Path(td)
        rs = tmp / "guard_harness.rs"
        bin_path = tmp / "guard_harness"
        rs.write_text(GUARD_PAGE_HARNESS_RS)

        t_comp0 = time.perf_counter()
        rc = subprocess.run(
            ["rustc", "+1.99.1", "--edition=2024", "-O", str(rs), "-o", str(bin_path)],
            capture_output=True,
            text=True,
        )
        compile_ms = round((time.perf_counter() - t_comp0) * 1000.0, 2)
        if rc.returncode != 0:
            return {"compile_rc": rc.returncode, "stderr": rc.stderr}

        r_heap = subprocess.run([str(bin_path), "heap_buggy"], capture_output=True, text=True)
        r_guard_buggy = subprocess.run([str(bin_path), "guard_buggy"], capture_output=True, text=True)
        t_fix0 = time.perf_counter()
        r_fixed = subprocess.run([str(bin_path), "fixed"], capture_output=True, text=True)
        fixed_ms = round((time.perf_counter() - t_fix0) * 1000.0, 2)

        return {
            "compile_rc": rc.returncode,
            "compile_ms": compile_ms,
            "heap_buggy_rc": r_heap.returncode,
            "heap_buggy_stdout": r_heap.stdout.strip(),
            "guard_buggy_rc": r_guard_buggy.returncode,
            "guard_buggy_killed_by_sigsegv": (r_guard_buggy.returncode == -signal.SIGSEGV),
            "fixed_rc": r_fixed.returncode,
            "fixed_stdout": r_fixed.stdout.strip(),
            "fixed_run_ms": fixed_ms,
        }


def main() -> int:
    out = {
        "swar_exhaustive": probe_swar_exhaustive(),
        "div_by_const_exhaustive": probe_div_by_const_exhaustive(),
        "bmi2_and_pshufb": probe_bmi2_and_pshufb(),
        "native_guard_page_harness": probe_native_guard_page_harness(),
    }
    print(json.dumps(out, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
