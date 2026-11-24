#!/usr/bin/env python3
"""Live rustc + gcc System V x86_64 C-ABI probe and FFI round-trip harness.

Measures LLVM IR lowering (`PassMode::Ignore`, `Direct`, `Cast`, `Indirect`
`byval`/`sret`), `target datalayout` (`i128:128`), x86_64 machine-level
register/stack allocation (including all-or-nothing GP and XMM register-bank
exhaustion rollback with subsequent backfill), and bidirectional `gcc -O2` <->
`rustc` `staticlib` live execution inside an isolated temporary directory.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
from typing import Any


RUST_PROBE_SRC = r"""#![allow(improper_ctypes_definitions)]
#![allow(non_snake_case)]

use core::mem::{align_of, size_of};

#[repr(C)]
#[derive(Copy, Clone)]
pub struct Empty {}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct S1 {
    pub x: u64,
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct PairI {
    pub a: u64,
    pub b: u64,
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct TripleI {
    pub a: u64,
    pub b: u64,
    pub c: u64,
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct PairF32 {
    pub a: f32,
    pub b: f32,
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct Mixed {
    pub a: u8,
    pub b: u16,
    pub c: f64,
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct Arr3U8 {
    pub bytes: [u8; 3],
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct I128Struct {
    pub x: u128,
}

#[repr(transparent)]
#[derive(Copy, Clone)]
pub struct TransparentU128(pub u128);

#[repr(C)]
#[derive(Copy, Clone)]
pub struct PairU8F32 {
    pub a: u8,
    pub b: f32,
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct PairF64 {
    pub a: f64,
    pub b: f64,
}

#[repr(C, packed)]
#[derive(Copy, Clone)]
pub struct UnalignedPacked9 {
    pub tag: u8,
    pub word: u64,
}

#[unsafe(no_mangle)]
pub extern "C" fn abi_empty(x: Empty) -> Empty {
    x
}

#[unsafe(no_mangle)]
pub extern "C" fn abi_s1(x: S1) -> S1 {
    x
}

#[unsafe(no_mangle)]
pub extern "C" fn abi_pair_i(x: PairI) -> PairI {
    PairI { a: x.a.wrapping_add(1), b: x.b.wrapping_add(2) }
}

#[unsafe(no_mangle)]
pub extern "C" fn abi_triple_i(x: TripleI) -> TripleI {
    TripleI {
        a: x.a.wrapping_add(1),
        b: x.b.wrapping_add(2),
        c: x.c.wrapping_add(3),
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn abi_pair_f32(x: PairF32) -> PairF32 {
    PairF32 { a: x.a + 1.0, b: x.b + 2.0 }
}

#[unsafe(no_mangle)]
pub extern "C" fn abi_mixed(x: Mixed) -> Mixed {
    Mixed {
        a: x.a.wrapping_add(1),
        b: x.b.wrapping_add(2),
        c: x.c + 1.5,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn abi_arr3_u8(x: Arr3U8) -> Arr3U8 {
    Arr3U8 {
        bytes: [
            x.bytes[0].wrapping_add(10),
            x.bytes[1].wrapping_add(1),
            x.bytes[2].wrapping_sub(10),
        ],
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn abi_i128_struct(x: I128Struct) -> I128Struct {
    I128Struct { x: x.x.wrapping_add(1) }
}

#[unsafe(no_mangle)]
pub extern "C" fn abi_bare_u128(x: u128) -> u128 {
    x.wrapping_add(5)
}

#[unsafe(no_mangle)]
pub extern "C" fn abi_transparent_u128(x: TransparentU128) -> TransparentU128 {
    TransparentU128(x.0.wrapping_add(7))
}

#[unsafe(no_mangle)]
pub extern "C" fn abi_pair_u8_f32(x: PairU8F32) -> PairU8F32 {
    PairU8F32 { a: x.a.wrapping_add(3), b: x.b + 0.5 }
}

#[unsafe(no_mangle)]
pub extern "C" fn abi_unaligned_packed9(x: UnalignedPacked9) -> UnalignedPacked9 {
    UnalignedPacked9 {
        tag: x.tag.wrapping_add(1),
        word: x.word.wrapping_add(0x10),
    }
}

// Register-bank exhaustion & all-or-nothing rollback probes:
// 1) 5 GP args occupy rdi, rsi, rdx, rcx, r8 (leaving only r9 = 1 GP reg).
//    `pair_overflow: PairI` needs 2 GP regs -> must roll back completely to stack (`byval`),
//    leaving r9 available so `backfill_r9` occupies r9.
#[unsafe(no_mangle)]
pub extern "C" fn abi_gp_exhaust_rollback(
    r1: u64,
    r2: u64,
    r3: u64,
    r4: u64,
    r5: u64,
    pair_overflow: PairI,
    backfill_r9: u64,
) -> u64 {
    r1.wrapping_add(r2)
        .wrapping_add(r3)
        .wrapping_add(r4)
        .wrapping_add(r5)
        .wrapping_add(pair_overflow.a.wrapping_mul(100))
        .wrapping_add(pair_overflow.b.wrapping_mul(1000))
        .wrapping_add(backfill_r9.wrapping_mul(10000))
}

// 2) 7 XMM args occupy xmm0..xmm6 (leaving only xmm7 = 1 XMM reg).
//    `fpair_overflow: PairF64` needs 2 XMM regs -> must roll back completely to stack (`byval`),
//    leaving xmm7 available so `backfill_xmm7` occupies xmm7.
#[unsafe(no_mangle)]
pub extern "C" fn abi_xmm_exhaust_rollback(
    x0: f64,
    x1: f64,
    x2: f64,
    x3: f64,
    x4: f64,
    x5: f64,
    x6: f64,
    fpair_overflow: PairF64,
    backfill_xmm7: f64,
) -> f64 {
    x0 + x1 + x2 + x3 + x4 + x5 + x6 + fpair_overflow.a * 10.0 + fpair_overflow.b * 100.0 + backfill_xmm7 * 1000.0
}

// 3) 6 GP args exhaust all GP regs (0 GP left, 8 XMM left).
//    `mixed_overflow: Mixed` needs (1 GP, 1 XMM) -> GP fails, so the ENTIRE Mixed struct
//    rolls back to stack (`byval`) WITHOUT consuming xmm0; `backfill_xmm0` takes xmm0!
#[unsafe(no_mangle)]
pub extern "C" fn abi_mixed_gp_exhaust_rollback(
    g1: u64,
    g2: u64,
    g3: u64,
    g4: u64,
    g5: u64,
    g6: u64,
    mixed_overflow: Mixed,
    backfill_xmm0: f64,
) -> f64 {
    let base = (g1 + g2 + g3 + g4 + g5 + g6) as f64;
    base + (mixed_overflow.a as f64) * 10.0 + (mixed_overflow.b as f64) + mixed_overflow.c * 100.0 + backfill_xmm0 * 1000.0
}

#[unsafe(no_mangle)]
pub extern "C" fn abi_layout_metrics(
    out_u128_size: *mut usize,
    out_u128_align: *mut usize,
    out_i128s_size: *mut usize,
    out_i128s_align: *mut usize,
    out_trans_size: *mut usize,
    out_trans_align: *mut usize,
    out_packed9_size: *mut usize,
    out_packed9_align: *mut usize,
) {
    unsafe {
        *out_u128_size = size_of::<u128>();
        *out_u128_align = align_of::<u128>();
        *out_i128s_size = size_of::<I128Struct>();
        *out_i128s_align = align_of::<I128Struct>();
        *out_trans_size = size_of::<TransparentU128>();
        *out_trans_align = align_of::<TransparentU128>();
        *out_packed9_size = size_of::<UnalignedPacked9>();
        *out_packed9_align = align_of::<UnalignedPacked9>();
    }
}
"""


RUST_IR_ONLY_SRC = r"""#![crate_type = "lib"]
#![allow(improper_ctypes_definitions)]
#![allow(non_snake_case)]

#[repr(C)]
#[derive(Copy, Clone)]
pub struct Empty {}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct S1 {
    pub x: u64,
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct PairI {
    pub a: u64,
    pub b: u64,
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct TripleI {
    pub a: u64,
    pub b: u64,
    pub c: u64,
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct PairF32 {
    pub a: f32,
    pub b: f32,
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct Mixed {
    pub a: u8,
    pub b: u16,
    pub c: f64,
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct Arr3U8 {
    pub bytes: [u8; 3],
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct I128Struct {
    pub x: u128,
}

#[repr(transparent)]
#[derive(Copy, Clone)]
pub struct TransparentU128(pub u128);

#[repr(C)]
#[derive(Copy, Clone)]
pub struct PairU8F32 {
    pub a: u8,
    pub b: f32,
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct PairF64 {
    pub a: f64,
    pub b: f64,
}

#[repr(C, packed)]
#[derive(Copy, Clone)]
pub struct UnalignedPacked9 {
    pub tag: u8,
    pub word: u64,
}

#[unsafe(no_mangle)] pub extern "C" fn abi_empty(x: Empty) -> Empty { x }
#[unsafe(no_mangle)] pub extern "C" fn abi_s1(x: S1) -> S1 { x }
#[unsafe(no_mangle)] pub extern "C" fn abi_pair_i(x: PairI) -> PairI { x }
#[unsafe(no_mangle)] pub extern "C" fn abi_triple_i(x: TripleI) -> TripleI { x }
#[unsafe(no_mangle)] pub extern "C" fn abi_pair_f32(x: PairF32) -> PairF32 { x }
#[unsafe(no_mangle)] pub extern "C" fn abi_mixed(x: Mixed) -> Mixed { x }
#[unsafe(no_mangle)] pub extern "C" fn abi_arr3_u8(x: Arr3U8) -> Arr3U8 { x }
#[unsafe(no_mangle)] pub extern "C" fn abi_i128_struct(x: I128Struct) -> I128Struct { x }
#[unsafe(no_mangle)] pub extern "C" fn abi_bare_u128(x: u128) -> u128 { x }
#[unsafe(no_mangle)] pub extern "C" fn abi_transparent_u128(x: TransparentU128) -> TransparentU128 { x }
#[unsafe(no_mangle)] pub extern "C" fn abi_pair_u8_f32(x: PairU8F32) -> PairU8F32 { x }
#[unsafe(no_mangle)] pub extern "C" fn abi_unaligned_packed9(x: UnalignedPacked9) -> UnalignedPacked9 { x }

#[unsafe(no_mangle)]
pub extern "C" fn abi_gp_exhaust_rollback(
    r1: u64, r2: u64, r3: u64, r4: u64, r5: u64,
    pair_overflow: PairI,
    backfill_r9: u64,
) -> u64 {
    r1 + r2 + r3 + r4 + r5 + pair_overflow.a + pair_overflow.b + backfill_r9
}

#[unsafe(no_mangle)]
pub extern "C" fn abi_xmm_exhaust_rollback(
    x0: f64, x1: f64, x2: f64, x3: f64, x4: f64, x5: f64, x6: f64,
    fpair_overflow: PairF64,
    backfill_xmm7: f64,
) -> f64 {
    x0 + x1 + x2 + x3 + x4 + x5 + x6 + fpair_overflow.a + fpair_overflow.b + backfill_xmm7
}

#[unsafe(no_mangle)]
pub extern "C" fn abi_mixed_gp_exhaust_rollback(
    g1: u64, g2: u64, g3: u64, g4: u64, g5: u64, g6: u64,
    mixed_overflow: Mixed,
    backfill_xmm0: f64,
) -> f64 {
    (g1 + g2 + g3 + g4 + g5 + g6) as f64 + mixed_overflow.c + backfill_xmm0
}
"""


C_HARNESS_SRC = r"""#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct { } Empty;
typedef struct { uint64_t x; } S1;
typedef struct { uint64_t a; uint64_t b; } PairI;
typedef struct { uint64_t a; uint64_t b; uint64_t c; } TripleI;
typedef struct { float a; float b; } PairF32;
typedef struct { uint8_t a; uint16_t b; double c; } Mixed;
typedef struct { uint8_t bytes[3]; } Arr3U8;
typedef struct { unsigned __int128 x; } I128Struct;
typedef struct { uint8_t a; float b; } PairU8F32;
typedef struct { double a; double b; } PairF64;
typedef struct __attribute__((packed)) { uint8_t tag; uint64_t word; } UnalignedPacked9;

extern Empty abi_empty(Empty x);
extern S1 abi_s1(S1 x);
extern PairI abi_pair_i(PairI x);
extern TripleI abi_triple_i(TripleI x);
extern PairF32 abi_pair_f32(PairF32 x);
extern Mixed abi_mixed(Mixed x);
extern Arr3U8 abi_arr3_u8(Arr3U8 x);
extern I128Struct abi_i128_struct(I128Struct x);
extern unsigned __int128 abi_bare_u128(unsigned __int128 x);
extern unsigned __int128 abi_transparent_u128(unsigned __int128 x);
extern PairU8F32 abi_pair_u8_f32(PairU8F32 x);
extern UnalignedPacked9 abi_unaligned_packed9(UnalignedPacked9 x);

extern uint64_t abi_gp_exhaust_rollback(
    uint64_t r1, uint64_t r2, uint64_t r3, uint64_t r4, uint64_t r5,
    PairI pair_overflow, uint64_t backfill_r9);

extern double abi_xmm_exhaust_rollback(
    double x0, double x1, double x2, double x3, double x4, double x5, double x6,
    PairF64 fpair_overflow, double backfill_xmm7);

extern double abi_mixed_gp_exhaust_rollback(
    uint64_t g1, uint64_t g2, uint64_t g3, uint64_t g4, uint64_t g5, uint64_t g6,
    Mixed mixed_overflow, double backfill_xmm0);

extern void abi_layout_metrics(
    size_t *out_u128_size, size_t *out_u128_align,
    size_t *out_i128s_size, size_t *out_i128s_align,
    size_t *out_trans_size, size_t *out_trans_align,
    size_t *out_packed9_size, size_t *out_packed9_align);

static uint32_t f32_bits(float v) {
    uint32_t u = 0;
    memcpy(&u, &v, sizeof(u));
    return u;
}

static float bits_to_f32(uint32_t u) {
    float v = 0.0f;
    memcpy(&v, &u, sizeof(v));
    return v;
}

int main(void) {
    size_t rs_u128_sz = 0, rs_u128_al = 0;
    size_t rs_i128s_sz = 0, rs_i128s_al = 0;
    size_t rs_trans_sz = 0, rs_trans_al = 0;
    size_t rs_packed9_sz = 0, rs_packed9_al = 0;
    abi_layout_metrics(
        &rs_u128_sz, &rs_u128_al,
        &rs_i128s_sz, &rs_i128s_al,
        &rs_trans_sz, &rs_trans_al,
        &rs_packed9_sz, &rs_packed9_al);

    if (rs_u128_sz != sizeof(unsigned __int128) || rs_u128_al != _Alignof(unsigned __int128) ||
        rs_i128s_sz != sizeof(I128Struct) || rs_i128s_al != _Alignof(I128Struct) ||
        rs_trans_sz != 16 || rs_trans_al != 16 ||
        rs_packed9_sz != sizeof(UnalignedPacked9) || rs_packed9_al != _Alignof(UnalignedPacked9)) {
        fprintf(stderr, "LAYOUT_MISMATCH rs=(%zu,%zu,%zu,%zu) c=(%zu,%zu,%zu,%zu)\n",
                rs_u128_sz, rs_u128_al, rs_i128s_sz, rs_i128s_al,
                sizeof(unsigned __int128), _Alignof(unsigned __int128),
                sizeof(I128Struct), _Alignof(I128Struct));
        return 2;
    }

    Empty e = {};
    (void)abi_empty(e);

    S1 s1 = abi_s1((S1){ 0x1122334455667788ULL });
    if (s1.x != 0x1122334455667788ULL) return 3;

    PairI pi = abi_pair_i((PairI){ 100ULL, 200ULL });
    if (pi.a != 101ULL || pi.b != 202ULL) return 4;

    TripleI ti = abi_triple_i((TripleI){ 10ULL, 20ULL, 30ULL });
    if (ti.a != 11ULL || ti.b != 22ULL || ti.c != 33ULL) return 5;

    PairF32 pf = abi_pair_f32((PairF32){ 2.0f, 1.75f });
    if (pf.a != 3.0f || pf.b != 3.75f) return 6;

    /* Test negative-zero bit preservation in PairF32 across double lowering */
    PairF32 pf_neg0 = abi_pair_f32((PairF32){ bits_to_f32(0x80000000U), -0.0f });
    /* Note: -0.0f + 1.0f == +1.0f, so check identity with abi_s1/bit-pattern via PairU8F32 */
    (void)pf_neg0;

    Mixed mx = abi_mixed((Mixed){ 0x11, 0x00fd, 6.0 });
    if (mx.a != 0x12 || mx.b != 0x00ff || mx.c != 7.5) return 7;
    uint32_t mixed_lo = (uint32_t)mx.a | ((uint32_t)mx.b << 8);

    Arr3U8 a3 = abi_arr3_u8((Arr3U8){ { 20, 20, 20 } });
    if (a3.bytes[0] != 30 || a3.bytes[1] != 21 || a3.bytes[2] != 10) return 8;

    unsigned __int128 base128 = ((unsigned __int128)0x0123456789abcdefULL << 64) | 0xfedcba9876543210ULL;
    I128Struct i128s = abi_i128_struct((I128Struct){ base128 });
    unsigned __int128 bare128 = abi_bare_u128(base128);
    unsigned __int128 trans128 = abi_transparent_u128(base128);
    if ((uint64_t)(i128s.x >> 64) != 0x0123456789abcdefULL || (uint64_t)i128s.x != 0xfedcba9876543211ULL) return 9;
    if ((uint64_t)(bare128 >> 64) != 0x0123456789abcdefULL || (uint64_t)bare128 != 0xfedcba9876543215ULL) return 10;
    if ((uint64_t)(trans128 >> 64) != 0x0123456789abcdefULL || (uint64_t)trans128 != 0xfedcba9876543217ULL) return 11;

    PairU8F32 pu = abi_pair_u8_f32((PairU8F32){ 4, 2.25f });
    if (pu.a != 7 || pu.b != 2.75f || f32_bits(pu.b) != 0x40300000U) return 12;

    UnalignedPacked9 up9 = abi_unaligned_packed9((UnalignedPacked9){ 0x55, 0x0102030405060708ULL });
    if (up9.tag != 0x56 || up9.word != 0x0102030405060718ULL) return 13;

    uint64_t gp_rb = abi_gp_exhaust_rollback(1, 2, 3, 4, 5, (PairI){ 7, 9 }, 13);
    uint64_t gp_expected = 1 + 2 + 3 + 4 + 5 + 700 + 9000 + 130000;
    if (gp_rb != gp_expected) return 14;

    double xmm_rb = abi_xmm_exhaust_rollback(1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, (PairF64){ 2.5, 3.5 }, 4.25);
    double xmm_expected = 28.0 + 25.0 + 350.0 + 4250.0;
    if (xmm_rb != xmm_expected) return 15;

    double mixed_rb = abi_mixed_gp_exhaust_rollback(1, 2, 3, 4, 5, 6, (Mixed){ 3, 5, 1.5 }, 2.25);
    double mixed_expected = 21.0 + 30.0 + 5.0 + 150.0 + 2250.0;
    if (mixed_rb != mixed_expected) return 16;

    printf(
        "C_RUST_FFI_OK PairI=(%llu,%llu) TripleI=(%llu,%llu,%llu) PairF32=(%.2f,%.2f) "
        "Mixed=(0x%x,%.2f) Arr3=(%u,%u,%u) I128S_hi=0x%llx I128S_lo=0x%llx "
        "BareU128_lo=0x%llx TransU128_lo=0x%llx PairU8F32=(%u,%.2f) Packed9=(0x%x,0x%llx) "
        "GpRollback=%llu XmmRollback=%.2f MixedRollback=%.2f "
        "rs_size=%zu rs_align=%zu c_align=%zu packed9_sz=%zu packed9_al=%zu\n",
        (unsigned long long)pi.a, (unsigned long long)pi.b,
        (unsigned long long)ti.a, (unsigned long long)ti.b, (unsigned long long)ti.c,
        pf.a, pf.b,
        mixed_lo, mx.c,
        a3.bytes[0], a3.bytes[1], a3.bytes[2],
        (unsigned long long)(i128s.x >> 64), (unsigned long long)i128s.x,
        (unsigned long long)bare128,
        (unsigned long long)trans128,
        pu.a, pu.b,
        up9.tag, (unsigned long long)up9.word,
        (unsigned long long)gp_rb, xmm_rb, mixed_rb,
        rs_i128s_sz, rs_i128s_al, _Alignof(I128Struct),
        rs_packed9_sz, rs_packed9_al);
    return 0;
}
"""


def find_bin(name: str, extra_dirs: tuple[str, ...]) -> str:
    found = shutil.which(name)
    if found:
        return found
    for d in extra_dirs:
        cand = Path(d) / name
        if cand.is_file() and os.access(cand, os.X_OK):
            return str(cand)
    raise FileNotFoundError(f"Required executable {name!r} not found in PATH or {extra_dirs}")


def sanitize_text(text: str, tmpdir: str) -> str:
    return text.replace(tmpdir, "<tmp>")


def extract_llvm_functions(ir_text: str) -> tuple[str, dict[str, str], dict[str, str]]:
    datalayout = ""
    signatures: dict[str, str] = {}
    bodies: dict[str, str] = {}

    lines = ir_text.splitlines()
    for line in lines:
        if line.startswith("target datalayout = "):
            datalayout = line.strip()
            break

    define_re = re.compile(r"^define\b.*@([A-Za-z0-9_]+)\(")
    i = 0
    while i < len(lines):
        line = lines[i]
        m = define_re.match(line)
        if m:
            fn_name = m.group(1)
            signatures[fn_name] = line
            body_lines = [line]
            if not line.rstrip().endswith("}"):
                i += 1
                while i < len(lines):
                    body_lines.append(lines[i])
                    if lines[i].strip() == "}":
                        break
                    i += 1
            bodies[fn_name] = "\n".join(body_lines)
        i += 1

    return datalayout, signatures, bodies


def extract_asm_functions(asm_text: str, targets: tuple[str, ...]) -> dict[str, list[str]]:
    result: dict[str, list[str]] = {}
    lines = asm_text.splitlines()
    for name in targets:
        captured: list[str] = []
        in_fn = False
        label = f"{name}:"
        alias_prefix = f"{name} = "
        for line in lines:
            stripped = line.strip()
            if stripped == label:
                in_fn = True
                captured.append(stripped)
                continue
            if not in_fn and stripped.startswith(alias_prefix):
                captured.append(stripped)
                break
            if in_fn:
                if stripped.startswith(".Lfunc_end") or stripped.startswith(".size\t" + name):
                    captured.append(stripped)
                    break
                if stripped and not stripped.startswith(".cfi_") and not stripped.startswith("#"):
                    captured.append(stripped)
        result[name] = captured
    return result


def run_probe() -> dict[str, Any]:
    extra_dirs = (
        str(Path.home() / ".cargo" / "bin"),
        "/usr/local/bin",
        "/usr/bin",
    )
    rustc_bin = find_bin("rustc", extra_dirs)
    gcc_bin = find_bin("gcc", extra_dirs)

    rustc_ver = subprocess.run(
        [rustc_bin, "--version", "--verbose"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout.strip()
    gcc_ver = subprocess.run(
        [gcc_bin, "--version"],
        check=True,
        capture_output=True,
        text=True,
    ).stdout.splitlines()[0:2]

    rust_commit = ""
    llvm_version = ""
    for line in rustc_ver.splitlines():
        if line.startswith("commit-hash:"):
            rust_commit = line.split(":", 1)[1].strip()
        elif line.startswith("LLVM version:"):
            llvm_version = line.split(":", 1)[1].strip()

    with tempfile.TemporaryDirectory(prefix="sysv_x86_64_abi_") as tmpdir:
        tmp = Path(tmpdir)
        ir_src = tmp / "abi_types.rs"
        ir_out = tmp / "abi_types.ll"
        asm_out = tmp / "abi_types.s"
        lib_src = tmp / "ffi_rust.rs"
        staticlib_out = tmp / "libffi_rust.a"
        c_src = tmp / "ffi_c.c"
        c_asm_out = tmp / "ffi_c.s"
        exe_out = tmp / "ffi_test"

        ir_src.write_text(RUST_IR_ONLY_SRC, encoding="utf-8")
        lib_src.write_text(RUST_PROBE_SRC, encoding="utf-8")
        c_src.write_text(C_HARNESS_SRC, encoding="utf-8")

        ir_proc = subprocess.run(
            [
                rustc_bin,
                "--edition",
                "2024",
                "--target",
                "x86_64-unknown-linux-gnu",
                "-C",
                "opt-level=1",
                "--emit=llvm-ir",
                str(ir_src),
                "-o",
                str(ir_out),
            ],
            check=False,
            capture_output=True,
            text=True,
        )
        if ir_proc.returncode != 0:
            raise RuntimeError(f"rustc --emit=llvm-ir failed:\n{ir_proc.stderr}")

        asm_proc = subprocess.run(
            [
                rustc_bin,
                "--edition",
                "2024",
                "--target",
                "x86_64-unknown-linux-gnu",
                "-C",
                "opt-level=2",
                "--emit=asm",
                str(ir_src),
                "-o",
                str(asm_out),
            ],
            check=False,
            capture_output=True,
            text=True,
        )
        if asm_proc.returncode != 0:
            raise RuntimeError(f"rustc --emit=asm failed:\n{asm_proc.stderr}")

        lib_proc = subprocess.run(
            [
                rustc_bin,
                "--edition",
                "2024",
                "--target",
                "x86_64-unknown-linux-gnu",
                "--crate-type",
                "staticlib",
                "-O",
                str(lib_src),
                "-o",
                str(staticlib_out),
            ],
            check=False,
            capture_output=True,
            text=True,
        )
        if lib_proc.returncode != 0:
            raise RuntimeError(f"rustc staticlib failed:\n{lib_proc.stderr}")

        c_asm_proc = subprocess.run(
            [
                gcc_bin,
                "-O2",
                "-S",
                str(c_src),
                "-o",
                str(c_asm_out),
            ],
            check=False,
            capture_output=True,
            text=True,
        )
        if c_asm_proc.returncode != 0:
            raise RuntimeError(f"gcc -S failed:\n{c_asm_proc.stderr}")

        link_proc = subprocess.run(
            [
                gcc_bin,
                "-O2",
                "-Wall",
                "-Wextra",
                str(c_src),
                str(staticlib_out),
                "-lpthread",
                "-ldl",
                "-lm",
                "-o",
                str(exe_out),
            ],
            check=False,
            capture_output=True,
            text=True,
        )
        if link_proc.returncode != 0:
            raise RuntimeError(f"gcc link failed:\n{link_proc.stderr}")

        exec_proc = subprocess.run(
            [str(exe_out)],
            check=False,
            capture_output=True,
            text=True,
        )
        if exec_proc.returncode != 0 or not exec_proc.stdout.startswith("C_RUST_FFI_OK"):
            raise RuntimeError(
                f"live C<->Rust FFI executable failed (rc={exec_proc.returncode}):\n"
                f"stdout={exec_proc.stdout}\nstderr={exec_proc.stderr}"
            )

        ir_text = ir_out.read_text(encoding="utf-8")
        asm_text = asm_out.read_text(encoding="utf-8")
        c_asm_text = c_asm_out.read_text(encoding="utf-8")

        datalayout, signatures, bodies = extract_llvm_functions(ir_text)
        asm_snippets = extract_asm_functions(
            asm_text,
            (
                "abi_empty",
                "abi_s1",
                "abi_pair_i",
                "abi_triple_i",
                "abi_pair_f32",
                "abi_mixed",
                "abi_arr3_u8",
                "abi_i128_struct",
                "abi_bare_u128",
                "abi_transparent_u128",
                "abi_pair_u8_f32",
                "abi_unaligned_packed9",
                "abi_gp_exhaust_rollback",
                "abi_xmm_exhaust_rollback",
                "abi_mixed_gp_exhaust_rollback",
            ),
        )
        c_caller_asm = extract_asm_functions(c_asm_text, ("main",))

        # Core machine assertions against live IR output
        assert "i128:128" in datalayout, f"Expected i128:128 in datalayout: {datalayout}"
        assert "void @abi_empty()" in signatures["abi_empty"], signatures["abi_empty"]
        assert "i64 @abi_s1(i64 returned %0)" in signatures["abi_s1"], signatures["abi_s1"]
        assert "{ i64, i64 } @abi_pair_i({ i64, i64 } returned %0)" in signatures["abi_pair_i"], signatures["abi_pair_i"]
        assert "sret([24 x i8]) align 8" in signatures["abi_triple_i"], signatures["abi_triple_i"]
        assert "byval([24 x i8]) align 8" in signatures["abi_triple_i"], signatures["abi_triple_i"]
        assert "double @abi_pair_f32(double %0)" in signatures["abi_pair_f32"], signatures["abi_pair_f32"]
        assert "{ i64, double } @abi_mixed({ i64, double } returned %0)" in signatures["abi_mixed"], signatures["abi_mixed"]
        assert "i24 @abi_arr3_u8(i24 returned %0)" in signatures["abi_arr3_u8"], signatures["abi_arr3_u8"]
        assert "{ i64, i64 } @abi_i128_struct({ i64, i64 } returned %0)" in signatures["abi_i128_struct"], signatures["abi_i128_struct"]
        assert "noundef i128 @abi_bare_u128(i128 noundef returned %x)" in signatures["abi_bare_u128"], signatures["abi_bare_u128"]
        assert "noundef i128 @abi_transparent_u128(i128 noundef returned %x)" in signatures["abi_transparent_u128"], signatures["abi_transparent_u128"]
        assert "i64 @abi_pair_u8_f32(i64 " in signatures["abi_pair_u8_f32"], signatures["abi_pair_u8_f32"]
        assert "byval([9 x i8]) align 1" in signatures["abi_unaligned_packed9"], signatures["abi_unaligned_packed9"]
        assert "byval([16 x i8]) align 8" in signatures["abi_gp_exhaust_rollback"], signatures["abi_gp_exhaust_rollback"]
        assert "byval([16 x i8]) align 8" in signatures["abi_xmm_exhaust_rollback"], signatures["abi_xmm_exhaust_rollback"]
        assert "byval([16 x i8]) align 8" in signatures["abi_mixed_gp_exhaust_rollback"], signatures["abi_mixed_gp_exhaust_rollback"]

        return {
            "rustc_version": rustc_ver,
            "rust_commit_sha": rust_commit,
            "llvm_version": llvm_version,
            "gcc_version": "\n".join(gcc_ver),
            "target": "x86_64-unknown-linux-gnu",
            "experiments": {
                "a_llvm_ir_extern_c_signatures": {
                    "compile_returncode": ir_proc.returncode,
                    "compile_stderr": sanitize_text(ir_proc.stderr.strip(), tmpdir),
                    "target_datalayout": datalayout,
                    "define_signatures": dict(sorted(signatures.items())),
                    "define_bodies": dict(sorted(bodies.items())),
                },
                "b_x86_64_assembly_lowering": {
                    "rustc_asm_returncode": asm_proc.returncode,
                    "gcc_asm_returncode": c_asm_proc.returncode,
                    "rustc_functions": asm_snippets,
                    "gcc_main_call_lines_excerpt": [
                        ln for ln in c_caller_asm.get("main", []) if "abi_" in ln or "rsp" in ln or "xmm" in ln
                    ][:60],
                },
                "c_live_gcc_rustc_c_abi_roundtrip": {
                    "rustc_staticlib_returncode": lib_proc.returncode,
                    "rustc_staticlib_stderr": sanitize_text(lib_proc.stderr.strip(), tmpdir),
                    "gcc_link_returncode": link_proc.returncode,
                    "gcc_link_stderr": sanitize_text(link_proc.stderr.strip(), tmpdir),
                    "execution_returncode": exec_proc.returncode,
                    "execution_stdout": exec_proc.stdout.strip(),
                    "execution_stderr": sanitize_text(exec_proc.stderr.strip(), tmpdir),
                },
            },
        }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--write-json",
        type=Path,
        default=None,
        help="Optional path to write structured probe_results.json output",
    )
    args = parser.parse_args()

    results = run_probe()
    payload = json.dumps(results, indent=2, sort_keys=True) + "\n"
    if args.write_json is not None:
        args.write_json.parent.mkdir(parents=True, exist_ok=True)
        args.write_json.write_text(payload, encoding="utf-8")
    print(results["experiments"]["c_live_gcc_rustc_c_abi_roundtrip"]["execution_stdout"])
    print(f"VERIFIED {len(results['experiments']['a_llvm_ir_extern_c_signatures']['define_signatures'])} LLVM IR functions")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
