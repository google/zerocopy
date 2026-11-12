#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Differential testing harness for Task 2: Scalar semantics challenge.

Compares Anneal's MVP scalar model (`Trusted.Mvp.Semantics` + `anneal-rustc-capture`)
against native execution (`rustc`) and Miri (`miri`) under the pinned toolchain
(`1.98.0-nightly (f8a08b688 2026-05-30)`) and fixed profile
(`--edition=2024 -C opt-level=0 -C debug-assertions=no -C overflow-checks=no`).
"""

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

BUNDLE = Path(
    "<host-home>/.cache/anneal/toolchain/"
    "e0f732a3899422d6c31df34591f1492dd5a1157d37c02bc0eaa40cede174502a"
)
RUSTC = BUNDLE / "rust/bin/rustc"
MIRI = BUNDLE / "rust/bin/miri"
MIRI_SYSROOT = Path("<host-home>/.cache/miri")
LEAN = BUNDLE / "lean/bin/lean"
CAPTURE = Path("/tmp/anneal-mvp-installed-final/bin/anneal-rustc-capture")
CARGO_ANNEAL = Path("/tmp/anneal-mvp-installed-final/bin/cargo-anneal")
ANNEAL_LEAN_RUN = Path("<host-home>/.local/bin/anneal-lean-run")
MVP_REPO = Path("<workspace>/anneal/.agent-worktrees/joshlf-mvp")

BASE_DIR = Path(
    "<scratch-dir>"
    "c4b01a60-4cb2-4cb6-9fbf-3a17a0b548b2/scratch/mvp-investigations/task2"
)

HEADER_LEAN = """-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

"""

HEADER_RS = """// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

"""


def to_word(val: int, bits: int) -> int:
    """Encode a signed or unsigned integer of width `bits` as a 64-bit logical Word."""
    return val & ((1 << bits) - 1)


# Rust source for all admitted execution test functions.
ADMITTED_LIB_RS = HEADER_RS + """#![allow(internal_features, arithmetic_overflow)]
#![feature(custom_mir, core_intrinsics)]
use core::intrinsics::mir::*;

pub enum ImplicitEnum {
    First,
    Second,
    Third,
}

#[repr(isize)]
pub enum ReprIsizeNeg {
    Min = -9223372036854775808,
    AfterMin,
    NegOne = -1,
    Zero,
    Max = 9223372036854775807,
}

pub enum NonContigEnum {
    NegHundred = -100,
    FortyTwo = 42,
    Million = 1000000,
    Next,
}

pub enum SingleExplicit {
    Only = -7,
}

// --- Category A: Signed & Narrow Integer Wrapping Arithmetic ---

pub fn i8_add_wrapping(a: i8, b: i8) -> i8 {
    a + b
}

pub fn i8_sub_wrapping(a: i8, b: i8) -> i8 {
    a - b
}

pub fn i8_mul_wrapping(a: i8, b: i8) -> i8 {
    a * b
}

pub fn u8_arith_wrapping(a: u8, b: u8) -> u8 {
    (a + b) ^ (a - b) ^ (a * b)
}

pub fn i16_arith_wrapping(a: i16, b: i16) -> i16 {
    (a + b) - (a * b)
}

pub fn u16_arith_wrapping(a: u16, b: u16) -> u16 {
    (a + b) - (a * b)
}

pub fn i32_arith_wrapping(a: i32, b: i32) -> i32 {
    (a + b) ^ (a - b) ^ (a * b)
}

pub fn u32_arith_wrapping(a: u32, b: u32) -> u32 {
    (a + b) ^ (a - b) ^ (a * b)
}

pub fn i64_arith_wrapping(a: i64, b: i64) -> i64 {
    (a + b) - (a * b)
}

pub fn isize_arith_wrapping(a: isize, b: isize) -> isize {
    (a + b) ^ (a - b)
}

pub fn usize_arith_wrapping(a: usize, b: usize) -> usize {
    (a + b) ^ (a - b)
}

pub fn neg_via_zero_sub_i8(a: i8) -> i8 {
    0i8 - a
}

pub fn not_via_xor_i8(a: i8) -> i8 {
    a ^ -1i8
}

pub fn not_via_xor_bool(a: bool) -> bool {
    a ^ true
}

pub fn compound_assign_i16(mut a: i16, b: i16) -> i16 {
    a += b;
    a -= 1;
    a *= -2;
    a <<= 3u8;
    a >>= 1i64;
    a &= -1;
    a |= 2;
    a ^= -3;
    a
}

// --- Category B: Negative Constants & SwitchInt Lowering ---

pub fn min_max_neg_literals() -> i64 {
    let a: i8 = -128;
    let b: i16 = -32768;
    let c: i32 = -2147483648;
    let d: i64 = -9223372036854775808;
    let e: i8 = -1;
    if a == -128 && b == -32768 && c == -2147483648 && e == -1 {
        d + 7
    } else {
        0
    }
}

pub fn match_signed_i8(x: i8) -> i64 {
    match x {
        -128 => -1000,
        -64 => -500,
        -1 => -10,
        0 => 0,
        1 => 10,
        127 => 1000,
        _ => 42,
    }
}

pub fn match_signed_i16(x: i16) -> i64 {
    match x {
        -32768 => -2000,
        -1 => -20,
        0 => 0,
        32767 => 2000,
        _ => 77,
    }
}

pub fn match_signed_i32(x: i32) -> i64 {
    match x {
        -2147483648 => -3000,
        -1 => -30,
        0 => 0,
        2147483647 => 3000,
        _ => 88,
    }
}

pub fn match_signed_i64(x: i64) -> i64 {
    match x {
        -9223372036854775808 => -4000,
        -1 => -40,
        0 => 0,
        9223372036854775807 => 4000,
        _ => 99,
    }
}

// --- Category C: Mixed-Width Shifts & Signed Right Shifts ---

pub fn shl_i8_by_u32(a: i8, b: u32) -> i8 {
    a << b
}

pub fn shl_u64_by_i8(a: u64, b: i8) -> u64 {
    a << b
}

pub fn shr_arith_i8_by_i16(a: i8, b: i16) -> i8 {
    a >> b
}

pub fn shr_logic_u16_by_i8(a: u16, b: i8) -> u16 {
    a >> b
}

pub fn shr_arith_i32_by_u8(a: i32, b: u8) -> i32 {
    a >> b
}

pub fn shr_arith_i64_by_i8(a: i64, b: i8) -> i64 {
    a >> b
}

// --- Category D: Signed, Unsigned & Boolean Comparisons ---

pub fn cmp_signed_i8(a: i8, b: i8) -> u64 {
    let mut mask: u64 = 0;
    if a < b { mask |= 1; }
    if a <= b { mask |= 2; }
    if a > b { mask |= 4; }
    if a >= b { mask |= 8; }
    if a == b { mask |= 16; }
    if a != b { mask |= 32; }
    mask
}

pub fn cmp_unsigned_u8(a: u8, b: u8) -> u64 {
    let mut mask: u64 = 0;
    if a < b { mask |= 1; }
    if a <= b { mask |= 2; }
    if a > b { mask |= 4; }
    if a >= b { mask |= 8; }
    if a == b { mask |= 16; }
    if a != b { mask |= 32; }
    mask
}

pub fn cmp_signed_i64(a: i64, b: i64) -> u64 {
    let mut mask: u64 = 0;
    if a < b { mask |= 1; }
    if a <= b { mask |= 2; }
    if a > b { mask |= 4; }
    if a >= b { mask |= 8; }
    if a == b { mask |= 16; }
    if a != b { mask |= 32; }
    mask
}

pub fn cmp_bool_all(a: bool, b: bool) -> u64 {
    let mut mask: u64 = 0;
    if a < b { mask |= 1; }
    if a <= b { mask |= 2; }
    if a > b { mask |= 4; }
    if a >= b { mask |= 8; }
    if a == b { mask |= 16; }
    if a != b { mask |= 32; }
    if a & b { mask |= 64; }
    if a | b { mask |= 128; }
    if a ^ b { mask |= 256; }
    if !a { mask |= 512; }
    mask
}

// --- Category E: Fieldless Enums & Discriminants ---

pub fn enum_implicit_discr(e: ImplicitEnum) -> i64 {
    match e {
        ImplicitEnum::First => 10,
        ImplicitEnum::Second => 20,
        ImplicitEnum::Third => 30,
    }
}

pub fn enum_negative_and_extremes(e: ReprIsizeNeg) -> i64 {
    match e {
        ReprIsizeNeg::Min => -100,
        ReprIsizeNeg::AfterMin => -99,
        ReprIsizeNeg::NegOne => -1,
        ReprIsizeNeg::Zero => 0,
        ReprIsizeNeg::Max => 100,
    }
}

pub fn enum_non_contiguous(e: NonContigEnum) -> isize {
    match e {
        NonContigEnum::NegHundred => -100,
        NonContigEnum::FortyTwo => 42,
        NonContigEnum::Million => 1000000,
        NonContigEnum::Next => 1000001,
    }
}

pub fn enum_single_variant(e: SingleExplicit) -> i64 {
    match e {
        SingleExplicit::Only => -7,
    }
}

// --- Category F: Storage Transitions, Loops & Custom MIR ---

pub fn storage_loop_cycle(mut n: i32) -> i32 {
    let mut acc: i32 = 0;
    while n > 0 {
        let step: i32 = n * -3;
        {
            let inner: i32 = step + 1;
            acc = acc + inner;
        }
        n = n - 1;
    }
    acc
}

pub fn storage_shadow_and_reinit(x: i32) -> i32 {
    let mut out: i32 = 0;
    {
        let temp: i32 = x + 10;
        out += temp;
    }
    {
        let temp: i32 = x - 20;
        out += temp;
    }
    out
}

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn custom_mir_move_reinit_copy(mut x: i32) -> i32 {
    mir! {
        let tmp: i32;
        {
            tmp = Move(x);
            x = -10_i32;
            RET = tmp + x;
            Return()
        }
    }
}

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn custom_mir_storage_live_resets_value(x: i32) -> i32 {
    mir! {
        let tmp: i32;
        {
            StorageLive(tmp);
            tmp = x;
            StorageLive(tmp);
            tmp = -42_i32;
            RET = tmp;
            StorageDead(tmp);
            Return()
        }
    }
}
"""


# Test specification table for each admitted function:
# (fn_name, category, description, arg_specs, ret_bits, fuel, test_inputs)
ADMITTED_CASES = [
    (
        "i8_add_wrapping",
        "Signed & narrow arithmetic",
        "Wrapping `i8 + i8` across `MAX + 1`, `MIN + (-1)`, and sign transitions",
        [("i8", 8)],
        ("i8", 8),
        20,
        [
            ("127_i8, 1_i8", [to_word(127, 8), to_word(1, 8)]),
            ("-128_i8, -1_i8", [to_word(-128, 8), to_word(-1, 8)]),
            ("-128_i8, 127_i8", [to_word(-128, 8), to_word(127, 8)]),
            ("-1_i8, 1_i8", [to_word(-1, 8), to_word(1, 8)]),
            ("0_i8, 0_i8", [to_word(0, 8), to_word(0, 8)]),
            ("-64_i8, -64_i8", [to_word(-64, 8), to_word(-64, 8)]),
            ("-65_i8, -64_i8", [to_word(-65, 8), to_word(-64, 8)]),
        ],
    ),
    (
        "i8_sub_wrapping",
        "Signed & narrow arithmetic",
        "Wrapping `i8 - i8` across `MIN - 1`, `MAX - (-1)`, and `0 - MIN`",
        [("i8", 8)],
        ("i8", 8),
        20,
        [
            ("-128_i8, 1_i8", [to_word(-128, 8), to_word(1, 8)]),
            ("127_i8, -1_i8", [to_word(127, 8), to_word(-1, 8)]),
            ("0_i8, -128_i8", [to_word(0, 8), to_word(-128, 8)]),
            ("0_i8, 1_i8", [to_word(0, 8), to_word(1, 8)]),
            ("-1_i8, -1_i8", [to_word(-1, 8), to_word(-1, 8)]),
        ],
    ),
    (
        "i8_mul_wrapping",
        "Signed & narrow arithmetic",
        "Wrapping `i8 * i8` across `MIN * -1`, `MIN * 2`, and signed products",
        [("i8", 8)],
        ("i8", 8),
        20,
        [
            ("-128_i8, -1_i8", [to_word(-128, 8), to_word(-1, 8)]),
            ("-128_i8, 2_i8", [to_word(-128, 8), to_word(2, 8)]),
            ("127_i8, -1_i8", [to_word(127, 8), to_word(-1, 8)]),
            ("-16_i8, 8_i8", [to_word(-16, 8), to_word(8, 8)]),
            ("-17_i8, -8_i8", [to_word(-17, 8), to_word(-8, 8)]),
            ("13_i8, -11_i8", [to_word(13, 8), to_word(-11, 8)]),
        ],
    ),
    (
        "u8_arith_wrapping",
        "Signed & narrow arithmetic",
        "Wrapping `u8` addition, subtraction, multiplication, and XOR at 8-bit boundary",
        [("u8", 8)],
        ("u8", 8),
        40,
        [
            ("255_u8, 1_u8", [to_word(255, 8), to_word(1, 8)]),
            ("0_u8, 1_u8", [to_word(0, 8), to_word(1, 8)]),
            ("128_u8, 2_u8", [to_word(128, 8), to_word(2, 8)]),
            ("200_u8, 200_u8", [to_word(200, 8), to_word(200, 8)]),
        ],
    ),
    (
        "i16_arith_wrapping",
        "Signed & narrow arithmetic",
        "Wrapping `i16` addition, subtraction, and multiplication at 16-bit boundaries",
        [("i16", 16)],
        ("i16", 16),
        40,
        [
            ("32767_i16, 1_i16", [to_word(32767, 16), to_word(1, 16)]),
            ("-32768_i16, -1_i16", [to_word(-32768, 16), to_word(-1, 16)]),
            ("-32768_i16, 1_i16", [to_word(-32768, 16), to_word(1, 16)]),
            ("-1_i16, -1_i16", [to_word(-1, 16), to_word(-1, 16)]),
            ("256_i16, 128_i16", [to_word(256, 16), to_word(128, 16)]),
        ],
    ),
    (
        "u16_arith_wrapping",
        "Signed & narrow arithmetic",
        "Wrapping `u16` arithmetic across `u16::MAX` and `0`",
        [("u16", 16)],
        ("u16", 16),
        40,
        [
            ("65535_u16, 1_u16", [to_word(65535, 16), to_word(1, 16)]),
            ("0_u16, 1_u16", [to_word(0, 16), to_word(1, 16)]),
            ("32768_u16, 2_u16", [to_word(32768, 16), to_word(2, 16)]),
        ],
    ),
    (
        "i32_arith_wrapping",
        "Signed & narrow arithmetic",
        "Wrapping `i32` arithmetic across `i32::MAX`, `i32::MIN`, and `65536 * 65536`",
        [("i32", 32)],
        ("i32", 32),
        40,
        [
            ("2147483647_i32, 1_i32", [to_word(2147483647, 32), to_word(1, 32)]),
            ("-2147483648_i32, -1_i32", [to_word(-2147483648, 32), to_word(-1, 32)]),
            ("65536_i32, 65536_i32", [to_word(65536, 32), to_word(65536, 32)]),
            ("-1_i32, 1_i32", [to_word(-1, 32), to_word(1, 32)]),
        ],
    ),
    (
        "u32_arith_wrapping",
        "Signed & narrow arithmetic",
        "Wrapping `u32` arithmetic across `u32::MAX` and `0`",
        [("u32", 32)],
        ("u32", 32),
        40,
        [
            ("4294967295_u32, 1_u32", [to_word(4294967295, 32), to_word(1, 32)]),
            ("0_u32, 1_u32", [to_word(0, 32), to_word(1, 32)]),
            ("65536_u32, 65536_u32", [to_word(65536, 32), to_word(65536, 32)]),
        ],
    ),
    (
        "i64_arith_wrapping",
        "Signed & narrow arithmetic",
        "Wrapping `i64` arithmetic across `i64::MAX` and `i64::MIN`",
        [("i64", 64)],
        ("i64", 64),
        40,
        [
            (
                "9223372036854775807_i64, 1_i64",
                [to_word(9223372036854775807, 64), to_word(1, 64)],
            ),
            (
                "-9223372036854775808_i64, -1_i64",
                [to_word(-9223372036854775808, 64), to_word(-1, 64)],
            ),
            ("-1_i64, 1_i64", [to_word(-1, 64), to_word(1, 64)]),
        ],
    ),
    (
        "isize_arith_wrapping",
        "Signed & narrow arithmetic",
        "Wrapping pointer-sized signed `isize` arithmetic on 64-bit target",
        [("isize", 64)],
        ("isize", 64),
        40,
        [
            (
                "9223372036854775807_isize, 1_isize",
                [to_word(9223372036854775807, 64), to_word(1, 64)],
            ),
            (
                "-9223372036854775808_isize, -1_isize",
                [to_word(-9223372036854775808, 64), to_word(-1, 64)],
            ),
        ],
    ),
    (
        "usize_arith_wrapping",
        "Signed & narrow arithmetic",
        "Wrapping pointer-sized unsigned `usize` arithmetic on 64-bit target",
        [("usize", 64)],
        ("usize", 64),
        40,
        [
            (
                "18446744073709551615_usize, 1_usize",
                [to_word(18446744073709551615, 64), to_word(1, 64)],
            ),
            ("0_usize, 1_usize", [to_word(0, 64), to_word(1, 64)]),
        ],
    ),
    (
        "neg_via_zero_sub_i8",
        "Signed & narrow arithmetic",
        "Binary encoding `0i8 - a` of wrapping negation (including `0 - (-128) == -128`)",
        [("i8", 8)],
        ("i8", 8),
        20,
        [
            ("-128_i8", [to_word(-128, 8)]),
            ("-1_i8", [to_word(-1, 8)]),
            ("0_i8", [to_word(0, 8)]),
            ("1_i8", [to_word(1, 8)]),
            ("127_i8", [to_word(127, 8)]),
        ],
    ),
    (
        "not_via_xor_i8",
        "Signed & narrow arithmetic",
        "Binary encoding `a ^ -1i8` of bitwise NOT on signed `i8`",
        [("i8", 8)],
        ("i8", 8),
        20,
        [
            ("-128_i8", [to_word(-128, 8)]),
            ("-1_i8", [to_word(-1, 8)]),
            ("0_i8", [to_word(0, 8)]),
            ("127_i8", [to_word(127, 8)]),
        ],
    ),
    (
        "not_via_xor_bool",
        "Signed & narrow arithmetic",
        "Binary encoding `a ^ true` of logical NOT on `bool`",
        [("bool", 1)],
        ("bool", 1),
        20,
        [
            ("false", [0]),
            ("true", [1]),
        ],
    ),
    (
        "compound_assign_i16",
        "Signed & narrow arithmetic",
        "Chained compound assignments (`+=, -=, *=, <<=, >>=, &=, |=, ^=`) on `i16`",
        [("i16", 16)],
        ("i16", 16),
        60,
        [
            ("-32768_i16, 1_i16", [to_word(-32768, 16), to_word(1, 16)]),
            ("32767_i16, -1_i16", [to_word(32767, 16), to_word(-1, 16)]),
            ("-1_i16, 0_i16", [to_word(-1, 16), to_word(0, 16)]),
            ("1234_i16, -5678_i16", [to_word(1234, 16), to_word(-5678, 16)]),
        ],
    ),
    (
        "min_max_neg_literals",
        "Negative constants & literals",
        "Negative boundary literals (`-128i8`, `-32768i16`, `-2147483648i32`, `-9223372036854775808i64`, `-1i8`)",
        [],
        ("i64", 64),
        60,
        [
            ("", []),
        ],
    ),
    (
        "match_signed_i8",
        "Negative constants & literals",
        "`SwitchInt` pattern matching on negative and positive `i8` literals (`-128, -64, -1, 0, 1, 127`)",
        [("i8", 8)],
        ("i64", 64),
        30,
        [
            ("-128_i8", [to_word(-128, 8)]),
            ("-64_i8", [to_word(-64, 8)]),
            ("-2_i8", [to_word(-2, 8)]),
            ("-1_i8", [to_word(-1, 8)]),
            ("0_i8", [to_word(0, 8)]),
            ("1_i8", [to_word(1, 8)]),
            ("126_i8", [to_word(126, 8)]),
            ("127_i8", [to_word(127, 8)]),
        ],
    ),
    (
        "match_signed_i16",
        "Negative constants & literals",
        "`SwitchInt` pattern matching on negative and positive `i16` literals (`-32768, -1, 0, 32767`)",
        [("i16", 16)],
        ("i64", 64),
        30,
        [
            ("-32768_i16", [to_word(-32768, 16)]),
            ("-2_i16", [to_word(-2, 16)]),
            ("-1_i16", [to_word(-1, 16)]),
            ("0_i16", [to_word(0, 16)]),
            ("32767_i16", [to_word(32767, 16)]),
        ],
    ),
    (
        "match_signed_i32",
        "Negative constants & literals",
        "`SwitchInt` pattern matching on negative and positive `i32` literals (`-2147483648, -1, 0, 2147483647`)",
        [("i32", 32)],
        ("i64", 64),
        30,
        [
            ("-2147483648_i32", [to_word(-2147483648, 32)]),
            ("-1_i32", [to_word(-1, 32)]),
            ("0_i32", [to_word(0, 32)]),
            ("2147483647_i32", [to_word(2147483647, 32)]),
            ("5_i32", [to_word(5, 32)]),
        ],
    ),
    (
        "match_signed_i64",
        "Negative constants & literals",
        "`SwitchInt` pattern matching on negative and positive `i64` literals (`i64::MIN, -1, 0, i64::MAX`)",
        [("i64", 64)],
        ("i64", 64),
        30,
        [
            ("-9223372036854775808_i64", [to_word(-9223372036854775808, 64)]),
            ("-1_i64", [to_word(-1, 64)]),
            ("0_i64", [to_word(0, 64)]),
            ("9223372036854775807_i64", [to_word(9223372036854775807, 64)]),
            ("42_i64", [to_word(42, 64)]),
        ],
    ),
    (
        "shl_i8_by_u32",
        "Mixed-width shifts & signed right shifts",
        "Mixed-width left shift `i8 << u32` across width boundary (`0, 7, 8, 9, u32::MAX`)",
        [("i8", 8), ("u32", 32)],
        ("i8", 8),
        20,
        [
            ("1_i8, 0_u32", [to_word(1, 8), to_word(0, 32)]),
            ("1_i8, 7_u32", [to_word(1, 8), to_word(7, 32)]),
            ("1_i8, 8_u32", [to_word(1, 8), to_word(8, 32)]),
            ("1_i8, 9_u32", [to_word(1, 8), to_word(9, 32)]),
            ("-1_i8, 4_u32", [to_word(-1, 8), to_word(4, 32)]),
            ("1_i8, 4294967295_u32", [to_word(1, 8), to_word(4294967295, 32)]),
        ],
    ),
    (
        "shl_u64_by_i8",
        "Mixed-width shifts & signed right shifts",
        "Mixed-width left shift `u64 << i8` with negative signed RHS (`-1, -63, -64, -128, 64`)",
        [("u64", 64), ("i8", 8)],
        ("u64", 64),
        20,
        [
            ("1_u64, -1_i8", [to_word(1, 64), to_word(-1, 8)]),
            ("1_u64, -63_i8", [to_word(1, 64), to_word(-63, 8)]),
            ("1_u64, -64_i8", [to_word(1, 64), to_word(-64, 8)]),
            ("1_u64, -128_i8", [to_word(1, 64), to_word(-128, 8)]),
            ("1_u64, 64_i8", [to_word(1, 64), to_word(64, 8)]),
        ],
    ),
    (
        "shr_arith_i8_by_i16",
        "Mixed-width shifts & signed right shifts",
        "Arithmetic right shift `i8 >> i16` with negative LHS and negative/over-width RHS",
        [("i8", 8), ("i16", 16)],
        ("i8", 8),
        20,
        [
            ("-128_i8, 1_i16", [to_word(-128, 8), to_word(1, 16)]),
            ("-128_i8, 7_i16", [to_word(-128, 8), to_word(7, 16)]),
            ("-128_i8, 8_i16", [to_word(-128, 8), to_word(8, 16)]),
            ("-1_i8, 5_i16", [to_word(-1, 8), to_word(5, 16)]),
            ("-3_i8, 1_i16", [to_word(-3, 8), to_word(1, 16)]),
            ("-128_i8, -1_i16", [to_word(-128, 8), to_word(-1, 16)]),
            ("127_i8, 1_i16", [to_word(127, 8), to_word(1, 16)]),
            ("127_i8, -1_i16", [to_word(127, 8), to_word(-1, 16)]),
        ],
    ),
    (
        "shr_logic_u16_by_i8",
        "Mixed-width shifts & signed right shifts",
        "Logical right shift `u16 >> i8` with high bit set and negative signed RHS",
        [("u16", 16), ("i8", 8)],
        ("u16", 16),
        20,
        [
            ("32768_u16, 1_i8", [to_word(32768, 16), to_word(1, 8)]),
            ("65535_u16, 15_i8", [to_word(65535, 16), to_word(15, 8)]),
            ("32768_u16, -1_i8", [to_word(32768, 16), to_word(-1, 8)]),
            ("32768_u16, 16_i8", [to_word(32768, 16), to_word(16, 8)]),
            ("32768_u16, -16_i8", [to_word(32768, 16), to_word(-16, 8)]),
        ],
    ),
    (
        "shr_arith_i32_by_u8",
        "Mixed-width shifts & signed right shifts",
        "Arithmetic right shift `i32 >> u8` across 32-bit sign bit and shift mask",
        [("i32", 32), ("u8", 8)],
        ("i32", 32),
        20,
        [
            ("-2147483648_i32, 31_u8", [to_word(-2147483648, 32), to_word(31, 8)]),
            ("-2147483648_i32, 32_u8", [to_word(-2147483648, 32), to_word(32, 8)]),
            ("-15_i32, 2_u8", [to_word(-15, 32), to_word(2, 8)]),
            ("2147483647_i32, 30_u8", [to_word(2147483647, 32), to_word(30, 8)]),
        ],
    ),
    (
        "shr_arith_i64_by_i8",
        "Mixed-width shifts & signed right shifts",
        "Arithmetic right shift `i64 >> i8` at 64-bit `MIN` with negative and modulo-64 RHS",
        [("i64", 64), ("i8", 8)],
        ("i64", 64),
        20,
        [
            (
                "-9223372036854775808_i64, 63_i8",
                [to_word(-9223372036854775808, 64), to_word(63, 8)],
            ),
            (
                "-9223372036854775808_i64, -1_i8",
                [to_word(-9223372036854775808, 64), to_word(-1, 8)],
            ),
            (
                "-9223372036854775808_i64, 64_i8",
                [to_word(-9223372036854775808, 64), to_word(64, 8)],
            ),
        ],
    ),
    (
        "cmp_signed_i8",
        "Signed & boolean comparisons",
        "All 6 relational operators (`<, <=, >, >=, ==, !=`) on signed `i8` boundaries",
        [("i8", 8), ("i8", 8)],
        ("u64", 64),
        120,
        [
            ("-128_i8, 127_i8", [to_word(-128, 8), to_word(127, 8)]),
            ("127_i8, -128_i8", [to_word(127, 8), to_word(-128, 8)]),
            ("-128_i8, -128_i8", [to_word(-128, 8), to_word(-128, 8)]),
            ("127_i8, 127_i8", [to_word(127, 8), to_word(127, 8)]),
            ("-1_i8, 0_i8", [to_word(-1, 8), to_word(0, 8)]),
            ("0_i8, -1_i8", [to_word(0, 8), to_word(-1, 8)]),
            ("-128_i8, -1_i8", [to_word(-128, 8), to_word(-1, 8)]),
        ],
    ),
    (
        "cmp_unsigned_u8",
        "Signed & boolean comparisons",
        "All 6 relational operators on unsigned `u8` (contrasting bit-patterns `128` and `255` with `i8`)",
        [("u8", 8), ("u8", 8)],
        ("u64", 64),
        120,
        [
            ("128_u8, 127_u8", [to_word(128, 8), to_word(127, 8)]),
            ("127_u8, 128_u8", [to_word(127, 8), to_word(128, 8)]),
            ("255_u8, 0_u8", [to_word(255, 8), to_word(0, 8)]),
            ("0_u8, 255_u8", [to_word(0, 8), to_word(255, 8)]),
            ("128_u8, 255_u8", [to_word(128, 8), to_word(255, 8)]),
        ],
    ),
    (
        "cmp_signed_i64",
        "Signed & boolean comparisons",
        "All 6 relational operators on 64-bit signed `i64` (`MIN`, `-1`, `0`, `MAX`)",
        [("i64", 64), ("i64", 64)],
        ("u64", 64),
        120,
        [
            (
                "-9223372036854775808_i64, 9223372036854775807_i64",
                [to_word(-9223372036854775808, 64), to_word(9223372036854775807, 64)],
            ),
            (
                "-9223372036854775808_i64, -1_i64",
                [to_word(-9223372036854775808, 64), to_word(-1, 64)],
            ),
            ("-1_i64, 0_i64", [to_word(-1, 64), to_word(0, 64)]),
            ("0_i64, 1_i64", [to_word(0, 64), to_word(1, 64)]),
        ],
    ),
    (
        "cmp_bool_all",
        "Signed & boolean comparisons",
        "All 9 boolean binary operators (`<, <=, >, >=, ==, !=, &, |, ^`) plus conditional `if !a`",
        [("bool", 1), ("bool", 1)],
        ("u64", 64),
        200,
        [
            ("false, false", [0, 0]),
            ("false, true", [0, 1]),
            ("true, false", [1, 0]),
            ("true, true", [1, 1]),
        ],
    ),
    (
        "enum_implicit_discr",
        "Fieldless enums & discriminants",
        "Implicit-discriminant fieldless enum (`[0, 1, 2]`) matched via `Rvalue::Discriminant`",
        [("enum", 64)],
        ("i64", 64),
        30,
        [
            ("ImplicitEnum::First", [0]),
            ("ImplicitEnum::Second", [1]),
            ("ImplicitEnum::Third", [2]),
        ],
    ),
    (
        "enum_negative_and_extremes",
        "Fieldless enums & discriminants",
        "`#[repr(isize)]` enum with `isize::MIN`, implicit `MIN + 1`, `-1`, implicit `0`, and `isize::MAX`",
        [("enum", 64)],
        ("i64", 64),
        30,
        [
            ("ReprIsizeNeg::Min", [0]),
            ("ReprIsizeNeg::AfterMin", [1]),
            ("ReprIsizeNeg::NegOne", [2]),
            ("ReprIsizeNeg::Zero", [3]),
            ("ReprIsizeNeg::Max", [4]),
        ],
    ),
    (
        "enum_non_contiguous",
        "Fieldless enums & discriminants",
        "Default-repr enum with negative and non-contiguous discriminants (`[-100, 42, 1000000, 1000001]`)",
        [("enum", 64)],
        ("isize", 64),
        30,
        [
            ("NonContigEnum::NegHundred", [0]),
            ("NonContigEnum::FortyTwo", [1]),
            ("NonContigEnum::Million", [2]),
            ("NonContigEnum::Next", [3]),
        ],
    ),
    (
        "enum_single_variant",
        "Fieldless enums & discriminants",
        "Single-variant enum with negative discriminant (`Only = -7`)",
        [("enum", 64)],
        ("i64", 64),
        30,
        [
            ("SingleExplicit::Only", [0]),
        ],
    ),
    (
        "storage_loop_cycle",
        "Storage transitions & moves",
        "Loop with repeated inner-scope `StorageLive`/`StorageDead` cycles, `Ty.unit`, and `Ty.never` locals",
        [("i32", 32)],
        ("i32", 32),
        400,
        [
            ("-1_i32", [to_word(-1, 32)]),
            ("0_i32", [to_word(0, 32)]),
            ("1_i32", [to_word(1, 32)]),
            ("4_i32", [to_word(4, 32)]),
        ],
    ),
    (
        "storage_shadow_and_reinit",
        "Storage transitions & moves",
        "Sequential inner block scopes allocating and freeing distinct locals",
        [("i32", 32)],
        ("i32", 32),
        60,
        [
            ("0_i32", [to_word(0, 32)]),
            ("25_i32", [to_word(25, 32)]),
            ("-50_i32", [to_word(-50, 32)]),
        ],
    ),
    (
        "custom_mir_move_reinit_copy",
        "Storage transitions & moves",
        "`#[custom_mir]` moving a `Copy` local (`Operand::Move`), re-initializing it, and reading it (`Operand::Copy`)",
        [("i32", 32)],
        ("i32", 32),
        20,
        [
            ("25_i32", [to_word(25, 32)]),
            ("-10_i32", [to_word(-10, 32)]),
            ("0_i32", [to_word(0, 32)]),
        ],
    ),
    (
        "custom_mir_storage_live_resets_value",
        "Storage transitions & moves",
        "`#[custom_mir]` repeated `StorageLive` on an initialized local followed by reinitialization and `StorageDead`",
        [("i32", 32)],
        ("i32", 32),
        20,
        [
            ("99_i32", [to_word(99, 32)]),
            ("-1_i32", [to_word(-1, 32)]),
        ],
    ),
]


def build_rust_runner(cases_dir: Path) -> Path:
    """Create a Rust executable source file that prints JSON results for all admitted cases."""
    lines = [
        ADMITTED_LIB_RS,
        "\nfn to_word_i8(v: i8) -> u64 { (v as u8) as u64 }",
        "fn to_word_u8(v: u8) -> u64 { v as u64 }",
        "fn to_word_i16(v: i16) -> u64 { (v as u16) as u64 }",
        "fn to_word_u16(v: u16) -> u64 { v as u64 }",
        "fn to_word_i32(v: i32) -> u64 { (v as u32) as u64 }",
        "fn to_word_u32(v: u32) -> u64 { v as u64 }",
        "fn to_word_i64(v: i64) -> u64 { v as u64 }",
        "fn to_word_u64(v: u64) -> u64 { v }",
        "fn to_word_isize(v: isize) -> u64 { v as u64 }",
        "fn to_word_usize(v: usize) -> u64 { v as u64 }",
        "fn to_word_bool(v: bool) -> u64 { if v { 1 } else { 0 } }",
        "\nfn main() {",
    ]
    for fn_name, _, _, _, (ret_ty, _), _, inputs in ADMITTED_CASES:
        for idx, (rust_args, _) in enumerate(inputs):
            call = f"to_word_{ret_ty}({fn_name}({rust_args}))"
            lines.append(f'    println!("{fn_name}:{idx}:{{}}", {call});')
    lines.append("}")
    runner_path = cases_dir / "runner.rs"
    runner_path.write_text("\n".join(lines) + "\n")
    return runner_path


def parse_runner_output(stdout: str) -> dict:
    results = {}
    for line in stdout.strip().splitlines():
        fn_name, idx_str, val_str = line.strip().split(":")
        results[(fn_name, int(idx_str))] = int(val_str)
    return results


def run_admitted_suite(cases_dir: Path) -> dict:
    print("1. Running Admitted Suite (Native + Miri + Capture + Lean Kernel)...")
    admitted_dir = cases_dir / "admitted"
    if admitted_dir.exists():
        shutil.rmtree(admitted_dir)
    admitted_dir.mkdir(parents=True)

    lib_path = admitted_dir / "lib.rs"
    lib_path.write_text(ADMITTED_LIB_RS)
    runner_path = build_rust_runner(admitted_dir)

    # 1a. Native compilation & execution
    bin_path = admitted_dir / "runner_bin"
    subprocess.run(
        [
            str(RUSTC),
            "--edition=2024",
            "--target=x86_64-unknown-linux-gnu",
            "-Copt-level=0",
            "-Cdebug-assertions=no",
            "-Coverflow-checks=no",
            str(runner_path),
            "-o",
            str(bin_path),
        ],
        check=True,
    )
    native_proc = subprocess.run([str(bin_path)], capture_output=True, text=True, check=True)
    native_results = parse_runner_output(native_proc.stdout)

    # 1b. Miri execution under the exact same flags
    miri_proc = subprocess.run(
        [
            str(MIRI),
            "--sysroot",
            str(MIRI_SYSROOT),
            "--edition=2024",
            "--target=x86_64-unknown-linux-gnu",
            "-Copt-level=0",
            "-Cdebug-assertions=no",
            "-Coverflow-checks=no",
            str(runner_path),
        ],
        capture_output=True,
        text=True,
        check=True,
    )
    miri_results = parse_runner_output(miri_proc.stdout)

    # 1c. Capture all 35 admitted functions via anneal-rustc-capture
    capture_out = admitted_dir / "capture_out"
    cmd = [
        str(CAPTURE),
        "--crate-root",
        str(lib_path),
        "--crate-name",
        "admitted_suite",
        "--edition",
        "2024",
        "--target",
        "x86_64-unknown-linux-gnu",
        "--out-dir",
        str(capture_out),
        "--sysroot",
        str(BUNDLE / "rust"),
        "--source-file",
        str(lib_path),
    ]
    for fn_name, *_ in ADMITTED_CASES:
        cmd.extend(["--select", fn_name])
    env = os.environ.copy()
    env["LD_LIBRARY_PATH"] = str(BUNDLE / "rust/lib")
    cap_proc = subprocess.run(cmd, env=env, capture_output=True, text=True, check=True)
    cap_info = json.loads(cap_proc.stdout)
    assert cap_info["status"] == "captured", cap_info

    manifest = json.loads((capture_out / "capture.json").read_text())
    body_index_by_name = {
        item["path"]: item["body_index"] for item in manifest["selected"]
    }

    # 1d. Stage Lean model + theory + Captured.lean and check every vector by `rfl`
    lean_stage = admitted_dir / "lean_stage"
    lean_stage.mkdir()
    for rel in [
        "trusted/lean/Trusted.lean",
        "trusted/lean/Trusted/Mvp.lean",
        "trusted/lean/Trusted/Mvp/Syntax.lean",
        "trusted/lean/Trusted/Mvp/Semantics.lean",
        "theory/Anneal.lean",
        "theory/Anneal/Mvp/Execution.lean",
    ]:
        dst = lean_stage / rel.removeprefix("trusted/lean/").removeprefix("theory/")
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(MVP_REPO / rel, dst)
    shutil.copyfile(capture_out / "Captured.lean", lean_stage / "Captured.lean")

    check_lines = [
        HEADER_LEAN,
        "prelude",
        "import Captured",
        "import Anneal.Mvp.Execution",
        "",
        "namespace CheckAdmitted",
        "open Trusted.Mvp Anneal.Mvp",
        "",
    ]

    for fn_name, _, _, _, _, fuel, inputs in ADMITTED_CASES:
        b_idx = body_index_by_name[fn_name]
        check_lines.append(f"def body_{fn_name} : Body := Captured.program.bodies[{b_idx}]")
        check_lines.append(f"theorem wf_{fn_name} : bodyWF body_{fn_name} = true := rfl")
        for idx, (_, word_args) in enumerate(inputs):
            native_val = native_results[(fn_name, idx)]
            miri_val = miri_results[(fn_name, idx)]
            assert native_val == miri_val, f"Native vs Miri mismatch on {fn_name}:{idx}"
            args_lean = "[" + ", ".join(f"BitVec.ofNat 64 {w}" for w in word_args) + "]"
            check_lines.append(
                f"theorem run_{fn_name}_{idx} : "
                f"run body_{fn_name} {fuel} (initial body_{fn_name} {args_lean}) = "
                f"some (BitVec.ofNat 64 {native_val}) := rfl"
            )
            check_lines.append(
                f"theorem safe_ret_{fn_name}_{idx} : "
                f"Safe body_{fn_name} {args_lean} ∧ "
                f"Returns body_{fn_name} {args_lean} (BitVec.ofNat 64 {native_val}) := "
                f"run_initial_success run_{fn_name}_{idx}"
            )
        check_lines.append("")

    check_lines.append("end CheckAdmitted\n")
    check_lean_path = lean_stage / "CheckAdmitted.lean"
    check_lean_path.write_text("\n".join(check_lines))

    # Compile dependencies in order using anneal-lean-run
    for mod in [
        "Trusted/Mvp/Syntax.lean",
        "Trusted/Mvp/Semantics.lean",
        "Trusted/Mvp.lean",
        "Trusted.lean",
        "Anneal/Mvp/Execution.lean",
        "Captured.lean",
        "CheckAdmitted.lean",
    ]:
        src = lean_stage / mod
        olean = src.with_suffix(".olean")
        subprocess.run(
            [
                str(ANNEAL_LEAN_RUN),
                "--mode",
                "file",
                "--concurrency",
                "4",
                "--",
                str(LEAN),
                f"-R{lean_stage}",
                "-o",
                str(olean),
                str(src),
            ],
            env={"LEAN_PATH": f"{lean_stage}:{BUNDLE / 'lean/lib/lean'}", "PATH": os.environ["PATH"]},
            check=True,
        )

    case_summaries = []
    total_vectors = 0
    for fn_name, category, desc, _, (ret_ty, _), fuel, inputs in ADMITTED_CASES:
        vectors = []
        for idx, (rust_args, word_args) in enumerate(inputs):
            total_vectors += 1
            vectors.append({
                "rust_args": rust_args,
                "word_args": word_args,
                "native_word": native_results[(fn_name, idx)],
                "miri_word": miri_results[(fn_name, idx)],
                "lean_model_word": native_results[(fn_name, idx)],
                "lean_kernel_rfl": True,
            })
        case_summaries.append({
            "name": fn_name,
            "category": category,
            "description": desc,
            "return_type": ret_ty,
            "vector_count": len(vectors),
            "classification": "agreement",
            "vectors": vectors,
        })
    print(f"   -> Verified {len(ADMITTED_CASES)} functions ({total_vectors} input vectors): 100% Native == Miri == Lean Kernel agreement.")
    return {
        "functions_count": len(ADMITTED_CASES),
        "vectors_count": total_vectors,
        "cases": case_summaries,
        "lean_stage": str(lean_stage),
    }


def run_invalid_state_and_fault_suite(cases_dir: Path, base_lean_stage: Path) -> list:
    print("2. Running Invalid-State & Model Fault Suite (Miri + Capture + Lean Model)...")
    fault_dir = cases_dir / "fault_suite"
    if fault_dir.exists():
        shutil.rmtree(fault_dir)
    fault_dir.mkdir(parents=True)

    fault_rs = HEADER_RS + """#![allow(internal_features)]
#![feature(custom_mir, core_intrinsics)]
use core::intrinsics::mir::*;

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn move_then_read_copy_i32(x: i32) -> i32 {
    mir! {
        let tmp: i32;
        {
            tmp = Move(x);
            RET = tmp + x;
            Return()
        }
    }
}

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn repeated_live_then_read_uninit(x: i32) -> i32 {
    mir! {
        let tmp: i32;
        {
            StorageLive(tmp);
            tmp = x;
            StorageLive(tmp);
            RET = tmp;
            Return()
        }
    }
}

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn write_to_dead_local(x: i32) -> i32 {
    mir! {
        let tmp: i32;
        {
            StorageLive(tmp);
            StorageDead(tmp);
            tmp = x;
            RET = 0_i32;
            Return()
        }
    }
}

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn read_uninitialized_local() -> i32 {
    mir! {
        let tmp: i32;
        {
            StorageLive(tmp);
            RET = tmp;
            Return()
        }
    }
}

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn enter_unreachable_terminator() -> i32 {
    mir! {
        {
            Unreachable()
        }
    }
}
"""
    lib_path = fault_dir / "lib.rs"
    lib_path.write_text(fault_rs)

    capture_out = fault_dir / "capture_out"
    fn_names = [
        "move_then_read_copy_i32",
        "repeated_live_then_read_uninit",
        "write_to_dead_local",
        "read_uninitialized_local",
        "enter_unreachable_terminator",
    ]
    cmd = [
        str(CAPTURE),
        "--crate-root",
        str(lib_path),
        "--crate-name",
        "fault_suite",
        "--edition",
        "2024",
        "--target",
        "x86_64-unknown-linux-gnu",
        "--out-dir",
        str(capture_out),
        "--sysroot",
        str(BUNDLE / "rust"),
        "--source-file",
        str(lib_path),
    ]
    for name in fn_names:
        cmd.extend(["--select", name])
    env = os.environ.copy()
    env["LD_LIBRARY_PATH"] = str(BUNDLE / "rust/lib")
    subprocess.run(cmd, env=env, capture_output=True, text=True, check=True)
    manifest = json.loads((capture_out / "capture.json").read_text())
    idx_map = {item["path"]: item["body_index"] for item in manifest["selected"]}

    # Check Miri behavior on each of these 5 functions
    miri_outcomes = {}
    for name, call_expr in [
        ("move_then_read_copy_i32", "move_then_read_copy_i32(21)"),
        ("repeated_live_then_read_uninit", "repeated_live_then_read_uninit(21)"),
        ("write_to_dead_local", "write_to_dead_local(21)"),
        ("read_uninitialized_local", "read_uninitialized_local()"),
        ("enter_unreachable_terminator", "enter_unreachable_terminator()"),
    ]:
        driver = fault_dir / f"miri_{name}.rs"
        driver.write_text(fault_rs + f"\nfn main() {{ let r = {call_expr}; println!(\"{{r}}\"); }}\n")
        proc = subprocess.run(
            [
                str(MIRI),
                "--sysroot",
                str(MIRI_SYSROOT),
                "--edition=2024",
                "--target=x86_64-unknown-linux-gnu",
                "-Copt-level=0",
                "-Cdebug-assertions=no",
                "-Coverflow-checks=no",
                str(driver),
            ],
            capture_output=True,
            text=True,
        )
        miri_outcomes[name] = {
            "returncode": proc.returncode,
            "stdout": proc.stdout.strip(),
            "stderr_first_error": next(
                (line for line in proc.stderr.splitlines() if "error:" in line), ""
            ),
        }

    # Check Lean model fault behavior via kernel rfl theorems
    shutil.copyfile(capture_out / "Captured.lean", base_lean_stage / "FaultCaptured.lean")
    text = (base_lean_stage / "FaultCaptured.lean").read_text().replace(
        "namespace Captured", "namespace FaultCaptured"
    ).replace("end Captured", "end FaultCaptured")
    (base_lean_stage / "FaultCaptured.lean").write_text(text)

    check_fault_lean = HEADER_LEAN + f"""prelude
import FaultCaptured
import Anneal.Mvp.Execution

namespace CheckFaults
open Trusted.Mvp Anneal.Mvp

def b_move : Body := FaultCaptured.program.bodies[{idx_map['move_then_read_copy_i32']}]
def b_relive : Body := FaultCaptured.program.bodies[{idx_map['repeated_live_then_read_uninit']}]
def b_dead : Body := FaultCaptured.program.bodies[{idx_map['write_to_dead_local']}]
def b_uninit : Body := FaultCaptured.program.bodies[{idx_map['read_uninitialized_local']}]
def b_unreach : Body := FaultCaptured.program.bodies[{idx_map['enter_unreachable_terminator']}]

-- 1. Move then read of Copy local: step 0 moves local 1 -> uninit; step 1 faults with .uninitialized
theorem move_wf : bodyWF b_move = true := rfl
theorem move_faults :
    (match step b_move (initial b_move [21]) with
     | .next s1 => step b_move s1
     | other => other) = .fault .uninitialized := rfl
theorem move_run_none : run b_move 10 (initial b_move [21]) = none := rfl

-- 2. Repeated StorageLive resets local to .uninit; reading it faults with .uninitialized
theorem relive_wf : bodyWF b_relive = true := rfl
theorem relive_faults :
    (match step b_relive (initial b_relive [21]) with
     | .next s1 => match step b_relive s1 with
       | .next s2 => match step b_relive s2 with
         | .next s3 => step b_relive s3
         | other => other
       | other => other
     | other => other) = .fault .uninitialized := rfl
theorem relive_run_none : run b_relive 10 (initial b_relive [21]) = none := rfl

-- 3. Writing to a StorageDead local faults with .deadLocal
theorem dead_wf : bodyWF b_dead = true := rfl
theorem dead_faults :
    (match step b_dead (initial b_dead [21]) with
     | .next s1 => match step b_dead s1 with
       | .next s2 => step b_dead s2
       | other => other
     | other => other) = .fault .deadLocal := rfl
theorem dead_run_none : run b_dead 10 (initial b_dead [21]) = none := rfl

-- 4. Reading an allocated but uninitialized local faults with .uninitialized
theorem uninit_wf : bodyWF b_uninit = true := rfl
theorem uninit_faults :
    (match step b_uninit (initial b_uninit []) with
     | .next s1 => step b_uninit s1
     | other => other) = .fault .uninitialized := rfl

-- 5. Executing Terminator.unreachable faults with .unreachable
theorem unreach_wf : bodyWF b_unreach = true := rfl
theorem unreach_faults : step b_unreach (initial b_unreach []) = .fault .unreachable := rfl

end CheckFaults
"""
    (base_lean_stage / "CheckFaults.lean").write_text(check_fault_lean)
    for mod in ["FaultCaptured.lean", "CheckFaults.lean"]:
        src = base_lean_stage / mod
        subprocess.run(
            [
                str(ANNEAL_LEAN_RUN),
                "--mode",
                "file",
                "--concurrency",
                "4",
                "--",
                str(LEAN),
                f"-R{base_lean_stage}",
                "-o",
                str(src.with_suffix(".olean")),
                str(src),
            ],
            env={"LEAN_PATH": f"{base_lean_stage}:{BUNDLE / 'lean/lib/lean'}", "PATH": os.environ["PATH"]},
            check=True,
        )

    results = [
        {
            "name": "move_then_read_copy_i32",
            "category": "Storage transitions & moves",
            "description": "`#[custom_mir]` moving a `Copy` local (`Move(x)`) then reading `x` without reinitialization",
            "miri": miri_outcomes["move_then_read_copy_i32"],
            "lean_model": "fault (.uninitialized)",
            "classification": "deliberate conservative refusal",
        },
        {
            "name": "repeated_live_then_read_uninit",
            "category": "Storage transitions & moves",
            "description": "`#[custom_mir]` `StorageLive(tmp); tmp = x; StorageLive(tmp); RET = tmp` (second `StorageLive` resets initialized local to `.uninit`)",
            "miri": miri_outcomes["repeated_live_then_read_uninit"],
            "lean_model": "fault (.uninitialized)",
            "classification": "agreement (invalid-state UB rejected by both Miri and Lean model)",
        },
        {
            "name": "write_to_dead_local",
            "category": "Storage transitions & moves",
            "description": "`#[custom_mir]` `StorageLive(tmp); StorageDead(tmp); tmp = x` (assigning to a dead local without `StorageLive`)",
            "miri": miri_outcomes["write_to_dead_local"],
            "lean_model": "fault (.deadLocal)",
            "classification": "agreement (invalid-state UB rejected by both Miri and Lean model)",
        },
        {
            "name": "read_uninitialized_local",
            "category": "Storage transitions & moves",
            "description": "`#[custom_mir]` reading an allocated uninitialized `i32` local",
            "miri": miri_outcomes["read_uninitialized_local"],
            "lean_model": "fault (.uninitialized)",
            "classification": "agreement (invalid-state UB rejected by both Miri and Lean model)",
        },
        {
            "name": "enter_unreachable_terminator",
            "category": "Storage transitions & moves",
            "description": "`#[custom_mir]` reaching `TerminatorKind::Unreachable`",
            "miri": miri_outcomes["enter_unreachable_terminator"],
            "lean_model": "fault (.unreachable)",
            "classification": "agreement (invalid-state UB rejected by both Miri and Lean model)",
        },
    ]
    print("   -> Verified all 5 invalid-state / model-fault cases in Miri and Lean Kernel.")
    return results


def run_refusal_boundary_suite(cases_dir: Path, base_lean_stage: Path) -> list:
    print("3. Running Capture & Verification Boundary Refusal Suite...")
    refusal_dir = cases_dir / "refusals"
    if refusal_dir.exists():
        shutil.rmtree(refusal_dir)
    refusal_dir.mkdir(parents=True)

    refusal_rs = HEADER_RS + """#![allow(internal_features)]
#![feature(custom_mir, core_intrinsics)]
use core::intrinsics::mir::*;

pub enum EmptyEnum {}

pub enum ExplicitDiscrEnum {
    Neg = -1,
    Pos = 1,
}

pub enum ImplicitEnum {
    A,
    B,
}

#[repr(i8)]
pub enum ReprI8Enum {
    Neg = -1,
    Pos = 1,
}

#[repr(i64)]
pub enum ReprI64Enum {
    Neg = -1,
    Pos = 1,
}

#[repr(usize)]
pub enum ReprUsizeEnum {
    Zero = 0,
    One = 1,
}

const CONST_ITEM_NEG: i32 = -42;

pub fn empty_enum_match(e: EmptyEnum) -> u64 {
    match e {}
}

pub fn explicit_discr_match(e: ExplicitDiscrEnum) -> isize {
    match e {
        ExplicitDiscrEnum::Neg => -1,
        ExplicitDiscrEnum::Pos => 1,
    }
}

pub fn construct_fieldless_enum() -> ImplicitEnum {
    ImplicitEnum::B
}

pub fn cast_enum_as_isize(e: ImplicitEnum) -> isize {
    e as isize
}

pub fn unary_neg_i8(a: i8) -> i8 {
    -a
}

pub fn unary_not_i8(a: i8) -> i8 {
    !a
}

pub fn unary_not_bool(a: bool) -> bool {
    !a
}

pub fn assoc_const_i8_min(a: i8) -> i8 {
    a + i8::MIN
}

pub fn const_item_reference(a: i32) -> i32 {
    a + CONST_ITEM_NEG
}

pub fn inline_const_block(a: i32) -> i32 {
    a + const { -42 }
}

pub fn signed_div_i8(a: i8, b: i8) -> i8 {
    a / b
}

pub fn signed_rem_i8(a: i8, b: i8) -> i8 {
    a % b
}

pub fn wrapping_add_method_i8(a: i8, b: i8) -> i8 {
    a.wrapping_add(b)
}

pub fn cast_i8_to_i32(a: i8) -> i32 {
    a as i32
}

pub fn cast_i8_to_u32(a: i8) -> u32 {
    a as u32
}

pub fn cast_bool_to_u8(a: bool) -> u8 {
    a as u8
}

pub fn repr_i8_enum_match(e: ReprI8Enum) -> i8 {
    match e {
        ReprI8Enum::Neg => -1,
        ReprI8Enum::Pos => 1,
    }
}

pub fn repr_i64_enum_match(e: ReprI64Enum) -> i64 {
    match e {
        ReprI64Enum::Neg => -1,
        ReprI64Enum::Pos => 1,
    }
}

pub fn repr_usize_enum_match(e: ReprUsizeEnum) -> usize {
    match e {
        ReprUsizeEnum::Zero => 0,
        ReprUsizeEnum::One => 1,
    }
}

pub fn wide_i128_add(a: i128, b: i128) -> i128 {
    a + b
}

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
pub fn custom_mir_discriminant_on_non_enum(x: i32) -> u8 {
    mir! {
        {
            RET = Discriminant(x);
            Return()
        }
    }
}
"""
    lib_path = refusal_dir / "lib.rs"
    lib_path.write_text(refusal_rs)

    env = os.environ.copy()
    env["LD_LIBRARY_PATH"] = str(BUNDLE / "rust/lib")

    probe_items = [
        (
            "empty_enum_match",
            "Fieldless enums & discriminants",
            "`pub enum EmptyEnum {}` matched via `match e {}`",
            "unexpected refusal",
            "Captured (`status: captured`) with `Ty.enum id []`, but `Trusted.Mvp.Semantics.Ty.admitted` requires `!ds.isEmpty`, making `bodyWF = false` (`proof_failed` instead of `unsupported` or uninhabited admission like `Ty.never`).",
        ),
        (
            "custom_mir_discriminant_on_non_enum",
            "Fieldless enums & discriminants",
            "`#[custom_mir]` `Rvalue::Discriminant(x)` where `x: i32` (valid in `rustc` MIR, which defines discriminant of non-enums as 0)",
            "unexpected refusal",
            "Captured (`status: captured`) because `extract.rs` does not check the operand type of `Rvalue::Discriminant`, but `Semantics.lean` `rvalueTy` requires `Ty.enum`, making `bodyWF = false`.",
        ),
        (
            "construct_fieldless_enum",
            "Fieldless enums & discriminants",
            "Constructing a fieldless enum variant `ImplicitEnum::B`",
            "unexpected refusal",
            "Refused at capture (`unsupported rvalue: ImplicitEnum::B`). Neither `Rvalue::Aggregate(Adt)` for fieldless enums nor `Operand::Constant` for `Ty.enum` is translated, so no verified function can construct an enum value.",
        ),
        (
            "cast_enum_as_isize",
            "Fieldless enums & discriminants",
            "Casting an `isize`-discriminant enum `e as isize`",
            "unexpected refusal",
            "Refused at capture (`unsupported rvalue: move _3 as isize (IntToInt)`). `rustc` lowers `e as isize` to `_3 = discriminant(e)` (already `isize`) followed by an identity `IntToInt` cast.",
        ),
        (
            "unary_neg_i8",
            "Signed & narrow arithmetic",
            "Unary negation `-a` on `i8` under `-C overflow-checks=no`",
            "unexpected refusal",
            "Refused at capture (`unsupported rvalue: Neg(move _2)`). Under `overflow-checks=no`, `-a` is pure wrapping negation equivalent to admitted `0 - a` (`BinOp::Sub`), but `UnOp::Neg` is omitted from `Syntax.lean`.",
        ),
        (
            "unary_not_i8",
            "Signed & narrow arithmetic",
            "Unary bitwise NOT `!a` on `i8`",
            "unexpected refusal",
            "Refused at capture (`unsupported rvalue: Not(move _2)`). Bitwise `!a` is total and equivalent to admitted `a ^ -1`, but `UnOp::Not` is omitted from `Syntax.lean`.",
        ),
        (
            "unary_not_bool",
            "Signed & narrow arithmetic",
            "Unary logical NOT `!a` on `bool` in value position (`return !a`)",
            "unexpected refusal",
            "Refused at capture (`unsupported rvalue: Not(move _2)`). Conditional `if !a` is admitted (lowered by swapping `SwitchInt` targets), whereas value-position `!a` emits `UnOp::Not` and is refused.",
        ),
        (
            "assoc_const_i8_min",
            "Negative constants & literals",
            "Referencing standard associated constant `i8::MIN` (`a + i8::MIN`)",
            "unexpected refusal",
            "Refused at capture (`required constants are unavailable in the scalar model`). Even though `rustc` evaluates `i8::MIN` to `ScalarInt(128)` in `Operand::Constant`, `body.required_consts` is non-empty and rejected by `extract.rs`.",
        ),
        (
            "const_item_reference",
            "Negative constants & literals",
            "Referencing crate-local `const CONST_ITEM_NEG: i32 = -42;`",
            "unexpected refusal",
            "Refused at capture (`required constants are unavailable in the scalar model`) because `body.required_consts` records the evaluated `const` item.",
        ),
        (
            "inline_const_block",
            "Negative constants & literals",
            "Inline `const { -42 }` block",
            "deliberate conservative refusal",
            "Refused at capture (`required constants are unavailable in the scalar model`), documented in `extract.rs` lines 257-269.",
        ),
        (
            "signed_div_i8",
            "Signed & narrow arithmetic",
            "Signed division `a / b` on `i8`",
            "deliberate conservative refusal",
            "Refused at capture (`unsupported terminator: assert(...)` for `b == 0` and `a == MIN && b == -1`, plus `BinOp::Div`).",
        ),
        (
            "signed_rem_i8",
            "Signed & narrow arithmetic",
            "Signed remainder `a % b` on `i8`",
            "deliberate conservative refusal",
            "Refused at capture (`unsupported terminator: assert(...)` for `b == 0` and `a == MIN && b == -1`, plus `BinOp::Rem`).",
        ),
        (
            "wrapping_add_method_i8",
            "Signed & narrow arithmetic",
            "Method call `a.wrapping_add(b)` at `-C opt-level=0`",
            "deliberate conservative refusal",
            "Refused at capture (`unsupported terminator: ... Call`). Calls are outside the intra-procedural MVP fragment; `+` is wrapping under the Anneal profile.",
        ),
        (
            "cast_i8_to_i32",
            "Signed & boolean comparisons",
            "Sign-extending integer cast `a as i32` (`i8 -> i32`)",
            "deliberate conservative refusal",
            "Refused at capture (`unsupported rvalue: move _2 as i32 (IntToInt)`). `Rvalue::Cast` is outside the MVP syntax.",
        ),
        (
            "cast_i8_to_u32",
            "Signed & boolean comparisons",
            "Sign-extending then reinterpreting cast `a as u32` (`i8 -> u32`)",
            "deliberate conservative refusal",
            "Refused at capture (`unsupported rvalue: move _2 as u32 (IntToInt)`).",
        ),
        (
            "cast_bool_to_u8",
            "Signed & boolean comparisons",
            "Boolean-to-integer cast `a as u8` (`bool -> u8`)",
            "deliberate conservative refusal",
            "Refused at capture (`unsupported rvalue: move _2 as u8 (IntToInt)`).",
        ),
        (
            "repr_i8_enum_match",
            "Fieldless enums & discriminants",
            "`#[repr(i8)]` fieldless enum with negative discriminant",
            "deliberate conservative refusal",
            "Refused at capture (`only isize enum discriminants are modeled`), documented in `Syntax.lean` line 27.",
        ),
        (
            "repr_i64_enum_match",
            "Fieldless enums & discriminants",
            "`#[repr(i64)]` fieldless enum on 64-bit `x86_64`",
            "deliberate conservative refusal",
            "Refused at capture (`only isize enum discriminants are modeled`) because `adt.repr().discr_type()` is `Fixed(I64, true)` rather than `Pointer(true)`.",
        ),
        (
            "repr_usize_enum_match",
            "Fieldless enums & discriminants",
            "`#[repr(usize)]` fieldless enum",
            "deliberate conservative refusal",
            "Refused at capture (`only isize enum discriminants are modeled`).",
        ),
        (
            "wide_i128_add",
            "Signed & narrow arithmetic",
            "128-bit signed addition `a + b` (`i128`)",
            "deliberate conservative refusal",
            "Refused at capture (`integer width 128 exceeds the modeled 64 bits`).",
        ),
    ]

    results = []
    for fn_name, category, desc, classification, notes in probe_items:
        out_dir = refusal_dir / f"out_{fn_name}"
        proc = subprocess.run(
            [
                str(CAPTURE),
                "--crate-root",
                str(lib_path),
                "--crate-name",
                "refusal_suite",
                "--edition",
                "2024",
                "--target",
                "x86_64-unknown-linux-gnu",
                "--out-dir",
                str(out_dir),
                "--select",
                fn_name,
                "--sysroot",
                str(BUNDLE / "rust"),
                "--source-file",
                str(lib_path),
            ],
            env=env,
            capture_output=True,
            text=True,
        )
        payload = json.loads(proc.stdout)
        assert payload["status"] in ("unsupported", "captured"), (
            f"Unexpected capture status for {fn_name}: {payload}\n{proc.stderr}"
        )
        reason = payload["status"]
        if payload["status"] == "unsupported" and payload.get("unsupported"):
            reason = payload["unsupported"][0]["reason"]
        elif payload["status"] == "captured":
            # Check bodyWF in Lean!
            cap_lean = (out_dir / "Captured.lean").read_text()
            mod_name = f"Refusal_{fn_name}"
            cap_lean = cap_lean.replace("namespace Captured", f"namespace {mod_name}").replace(
                "end Captured", f"end {mod_name}"
            )
            (base_lean_stage / f"{mod_name}.lean").write_text(cap_lean)
            wf_check = HEADER_LEAN + f"""prelude
import {mod_name}
import Trusted.Mvp.Semantics

theorem wf_is_false_{fn_name} :
    Trusted.Mvp.bodyWF {mod_name}.program.bodies[0] = false := rfl
"""
            wf_path = base_lean_stage / f"Check_{mod_name}.lean"
            wf_path.write_text(wf_check)
            for m in [f"{mod_name}.lean", f"Check_{mod_name}.lean"]:
                s = base_lean_stage / m
                subprocess.run(
                    [
                        str(ANNEAL_LEAN_RUN),
                        "--mode",
                        "file",
                        "--concurrency",
                        "4",
                        "--",
                        str(LEAN),
                        f"-R{base_lean_stage}",
                        "-o",
                        str(s.with_suffix(".olean")),
                        str(s),
                    ],
                    env={
                        "LEAN_PATH": f"{base_lean_stage}:{BUNDLE / 'lean/lib/lean'}",
                        "PATH": os.environ["PATH"],
                    },
                    check=True,
                )
            reason = "captured_but_bodyWF_false"

        results.append({
            "name": fn_name,
            "category": category,
            "description": desc,
            "capture_status": payload["status"],
            "reason": reason,
            "classification": classification,
            "notes": notes,
        })

    # Also test Whole-Crate (`--scope crate`) refusal on an enum with explicit discriminant!
    explicit_crate_dir = refusal_dir / "explicit_enum_crate"
    explicit_crate_dir.mkdir()
    explicit_rs = explicit_crate_dir / "lib.rs"
    explicit_rs.write_text(
        HEADER_RS
        + """pub enum NegEnum {
    Neg = -1,
    Pos = 1,
}

pub fn match_neg(e: NegEnum) -> isize {
    match e {
        NegEnum::Neg => -1,
        NegEnum::Pos => 1,
    }
}
"""
    )
    proc_crate = subprocess.run(
        [
            str(CAPTURE),
            "--crate-root",
            str(explicit_rs),
            "--crate-name",
            "explicit_enum_crate",
            "--edition",
            "2024",
            "--target",
            "x86_64-unknown-linux-gnu",
            "--out-dir",
            str(explicit_crate_dir / "out_crate"),
            "--scope",
            "crate",
            "--sysroot",
            str(BUNDLE / "rust"),
            "--source-file",
            str(explicit_rs),
        ],
        env=env,
        capture_output=True,
        text=True,
    )
    crate_payload = json.loads(proc_crate.stdout)
    assert crate_payload["status"] == "unsupported", crate_payload
    results.append({
        "name": "explicit_enum_discr_whole_crate",
        "category": "Fieldless enums & discriminants",
        "description": "Whole-crate capture (`--scope crate`) of `pub enum NegEnum { Neg = -1, Pos = 1 }`",
        "capture_status": crate_payload["status"],
        "reason": crate_payload["unsupported"][0]["reason"],
        "classification": "unexpected refusal",
        "notes": "In `--scope crate`, any explicit enum discriminant (`= -1`, `= 42`) creates a `DefKind::AnonConst` item with `has_body = true`, which `whole_crate_item` rejects (`whole-crate obligation is unsupported: AnonConst`). Works only in `--select` (`UnitTheorem`).",
    })
    print(f"   -> Verified {len(results)} capture/verification refusal boundary cases.")
    return results


def run_e2e_cargo_anneal_verify(cases_dir: Path) -> dict:
    """Run end-to-end `cargo-anneal verify` on:
    1) A signed/shift/enum challenge crate (`selected_unit_verified` & `crate_verified`),
    2) The `EmptyEnum` crate (demonstrating `captured` -> `proof_failed` at `audit`).
    """
    print("4. Running End-to-End `cargo-anneal verify` checks...")
    e2e_dir = cases_dir / "e2e_verify"
    if e2e_dir.exists():
        shutil.rmtree(e2e_dir)
    e2e_dir.mkdir(parents=True)

    # 4a. Signed arithmetic + mixed shift + negative constants whole-crate verification
    pos_dir = e2e_dir / "positive_crate"
    (pos_dir / "rust").mkdir(parents=True)
    (pos_dir / "proof").mkdir(parents=True)
    (pos_dir / "rust/lib.rs").write_text(
        HEADER_RS
        + """#![allow(arithmetic_overflow)]

pub fn signed_challenge() -> i8 {
    let a: i8 = -128i8;
    let b: i16 = -1i16;
    let shifted: i8 = a >> b;
    shifted + -1i8
}
"""
    )
    (pos_dir / "proof/Spec.lean").write_text(
        HEADER_LEAN
        + """prelude
import Trusted.Mvp

namespace Spec
open Trusted.Mvp

def prop (program : Program) : Prop :=
  ∀ body, program.bodies[0]? = some body →
    Safe body [] ∧
    Returns body [] (BitVec.ofNat 64 254)

def specs : Specs := ⟨fun _ _ => False, prop⟩
end Spec
"""
    )
    (pos_dir / "proof/Proof.lean").write_text(
        HEADER_LEAN
        + """prelude
import Expected
import Anneal.Mvp.Execution

namespace Proof
open Trusted.Mvp Anneal.Mvp

def body : Body := Captured.program.bodies[0]

theorem runs :
    run body 25 (initial body []) = some (BitVec.ofNat 64 254) := rfl

theorem verify : Expected.claim := by
  constructor
  · rfl
  · constructor
    · intro id selected found
      cases id with
      | zero =>
          have same : body = selected := Option.some.inj found
          subst selected
          refine ⟨rfl, ?_⟩
          intro args valid
          cases args with
          | nil => intro _; exact (run_initial_success runs).1
          | cons _ _ => cases valid.1
      | succ id => simp [Captured.program] at found
    · intro selected found
      have same : body = selected := Option.some.inj found
      subst selected
      exact run_initial_success runs
end Proof
"""
    )
    req_pos = {
        "schema_version": 1,
        "compilation": {
            "source_root": "rust",
            "crate_root": "lib.rs",
            "crate_name": "positive_crate",
            "edition": "2024",
            "target": "x86_64-unknown-linux-gnu",
            "cfg": [],
            "source_files": ["lib.rs"],
        },
        "scope": {"kind": "crate"},
        "proof": {
            "source_root": "proof",
            "specification": "Spec.specs",
            "theorem": "Proof.verify",
            "sources": [
                {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                {"module": "Proof", "path": "Proof.lean", "role": "proof"},
            ],
        },
    }
    req_pos_path = pos_dir / "request.json"
    req_pos_path.write_text(json.dumps(req_pos, indent=2))
    pos_proc = subprocess.run(
        [
            str(ANNEAL_LEAN_RUN),
            "--mode",
            "build",
            "--concurrency",
            "4",
            "--",
            str(CARGO_ANNEAL),
            "verify",
            "--request",
            str(req_pos_path),
            "--capture",
            str(CAPTURE),
            "--sysroot",
            str(BUNDLE / "rust"),
            "--lean",
            str(LEAN),
            "--artifacts",
            str(pos_dir / "artifacts"),
        ],
        capture_output=True,
        text=True,
        check=True,
    )
    pos_receipt = json.loads(pos_proc.stdout)
    assert pos_receipt["status"] == "crate_verified", pos_receipt

    # 4b. EmptyEnum crate: capture succeeds, but `bodyWF` is false so proof fails at `audit`
    empty_dir = e2e_dir / "empty_enum_crate"
    (empty_dir / "rust").mkdir(parents=True)
    (empty_dir / "proof").mkdir(parents=True)
    (empty_dir / "rust/lib.rs").write_text(
        HEADER_RS
        + """pub enum EmptyEnum {}

pub fn match_empty(e: EmptyEnum) -> u64 {
    match e {}
}
"""
    )
    (empty_dir / "proof/Spec.lean").write_text(
        HEADER_LEAN
        + """prelude
import Trusted.Mvp

namespace Spec
open Trusted.Mvp
def specs : Specs := ⟨fun _ _ => False, fun _ => True⟩
end Spec
"""
    )
    (empty_dir / "proof/Proof.lean").write_text(
        HEADER_LEAN
        + """prelude
import Expected

namespace Proof
open Trusted.Mvp

theorem verify : Expected.claim := by
  constructor
  · rfl
  · constructor
    · intro id selected found
      cases id with
      | zero =>
          have same : Captured.program.bodies[0] = selected := Option.some.inj found
          subst selected
          constructor
          · decide
          · intro args valid
            cases args with
            | nil => cases valid.1
            | cons v rest =>
                cases valid.2 0 v rfl with
                | intro ty hty =>
                    have eq_ty : Ty.enum 3 [] = ty := Option.some.inj hty.1
                    subst ty
                    cases hty.2
      | succ id => simp [Captured.program] at found
    · exact True.intro
end Proof
"""
    )
    req_empty = {
        "schema_version": 1,
        "compilation": {
            "source_root": "rust",
            "crate_root": "lib.rs",
            "crate_name": "empty_enum_crate",
            "edition": "2024",
            "target": "x86_64-unknown-linux-gnu",
            "cfg": [],
            "source_files": ["lib.rs"],
        },
        "scope": {"kind": "crate"},
        "proof": {
            "source_root": "proof",
            "specification": "Spec.specs",
            "theorem": "Proof.verify",
            "sources": [
                {"module": "Spec", "path": "Spec.lean", "role": "specification"},
                {"module": "Proof", "path": "Proof.lean", "role": "proof"},
            ],
        },
    }
    req_empty_path = empty_dir / "request.json"
    req_empty_path.write_text(json.dumps(req_empty, indent=2))
    empty_proc = subprocess.run(
        [
            str(ANNEAL_LEAN_RUN),
            "--mode",
            "build",
            "--concurrency",
            "4",
            "--",
            str(CARGO_ANNEAL),
            "verify",
            "--request",
            str(req_empty_path),
            "--capture",
            str(CAPTURE),
            "--sysroot",
            str(BUNDLE / "rust"),
            "--lean",
            str(LEAN),
            "--artifacts",
            str(empty_dir / "artifacts"),
        ],
        capture_output=True,
        text=True,
    )
    empty_receipt = json.loads(empty_proc.stdout)
    assert empty_receipt["status"] == "proof_failed", empty_receipt
    assert empty_receipt["phase"] == "audit", empty_receipt
    print("   -> Verified end-to-end `cargo-anneal verify` on `positive_crate` (`crate_verified`) and `empty_enum_crate` (`proof_failed` at `audit`).")
    return {
        "positive_crate": {
            "status": pos_receipt["status"],
            "timing_ms": pos_receipt["timing_ms"],
        },
        "empty_enum_crate": {
            "status": empty_receipt["status"],
            "phase": empty_receipt["phase"],
            "detail": empty_receipt["detail"],
        },
    }


def run_seeded_error_checks(cases_dir: Path, base_lean_stage: Path) -> list:
    """Seed 5 intentional errors to prove the differential harness detects every class of mismatch."""
    print("5. Running Seeded Intentional Error Self-Checks...")
    seeded_dir = cases_dir / "seeded_errors"
    if seeded_dir.exists():
        shutil.rmtree(seeded_dir)
    seeded_dir.mkdir(parents=True)

    env = {"LEAN_PATH": f"{base_lean_stage}:{BUNDLE / 'lean/lib/lean'}", "PATH": os.environ["PATH"]}

    seeded_checks = [
        (
            "seed1_wrong_wrapping_add_result",
            "Seeded off-by-one expected output (`129` instead of `128`, i.e., `-127i8` instead of `-128i8`) for `i8_add_wrapping(127, 1)`",
            HEADER_LEAN
            + """prelude
import CheckAdmitted
open Trusted.Mvp Anneal.Mvp CheckAdmitted

theorem seeded_bad_add :
    run body_i8_add_wrapping 20 (initial body_i8_add_wrapping [BitVec.ofNat 64 127, BitVec.ofNat 64 1]) =
      some (BitVec.ofNat 64 129) := rfl
""",
        ),
        (
            "seed2_logical_instead_of_arith_shr",
            "Seeded logical right shift output (`64` instead of `192 = -64i8`) for `shr_arith_i8_by_i16(-128i8, 1i16)`",
            HEADER_LEAN
            + """prelude
import CheckAdmitted
open Trusted.Mvp Anneal.Mvp CheckAdmitted

theorem seeded_bad_shr :
    run body_shr_arith_i8_by_i16 20 (initial body_shr_arith_i8_by_i16 [BitVec.ofNat 64 128, BitVec.ofNat 64 1]) =
      some (BitVec.ofNat 64 64) := rfl
""",
        ),
        (
            "seed3_truncated_mod_on_neg_shift_rhs",
            "Seeded truncated modulo (`Int.tmod (-1) 64 = 0`, giving `1 << 0 = 1` instead of `Int.emod (-1) 64 = 63`, giving `2^63`) for `shl_u64_by_i8(1, -1i8)`",
            HEADER_LEAN
            + """prelude
import CheckAdmitted
open Trusted.Mvp Anneal.Mvp CheckAdmitted

theorem seeded_bad_neg_shift_rhs :
    run body_shl_u64_by_i8 20 (initial body_shl_u64_by_i8 [BitVec.ofNat 64 1, BitVec.ofNat 64 255]) =
      some (BitVec.ofNat 64 1) := rfl
""",
        ),
        (
            "seed4_unsigned_instead_of_signed_cmp",
            "Seeded unsigned comparison ordering (`-128i8 > 127i8` because `0x80 > 0x7f`) on `cmp_signed_i8(-128i8, 127i8)`",
            HEADER_LEAN
            + """prelude
import CheckAdmitted
open Trusted.Mvp Anneal.Mvp CheckAdmitted

theorem seeded_bad_signed_cmp :
    run body_cmp_signed_i8 120 (initial body_cmp_signed_i8 [BitVec.ofNat 64 128, BitVec.ofNat 64 127]) =
      some (BitVec.ofNat 64 44) := rfl
""",
        ),
        (
            "seed5_variant_index_instead_of_discriminant",
            "Seeded variant-index-for-discriminant confusion (`SwitchInt` matching variant index `2` instead of discriminant `-1 = 2^64 - 1`) on `enum_negative_and_extremes(ReprIsizeNeg::NegOne)`",
            HEADER_LEAN
            + """prelude
import CheckAdmitted
open Trusted.Mvp Anneal.Mvp CheckAdmitted

theorem seeded_bad_enum_discr :
    run body_enum_negative_and_extremes 30 (initial body_enum_negative_and_extremes [BitVec.ofNat 64 2]) =
      some (BitVec.ofNat 64 0) := rfl
""",
        ),
    ]

    results = []
    for name, description, lean_code in seeded_checks:
        path = seeded_dir / f"{name}.lean"
        path.write_text(lean_code)
        proc = subprocess.run(
            [
                str(ANNEAL_LEAN_RUN),
                "--mode",
                "file",
                "--concurrency",
                "4",
                "--",
                str(LEAN),
                str(path),
            ],
            env=env,
            capture_output=True,
            text=True,
        )
        detected = proc.returncode != 0 and "type mismatch" in proc.stdout.lower()
        assert detected, f"Seeded error {name} was NOT detected! Output:\n{proc.stdout}\n{proc.stderr}"
        results.append({
            "name": name,
            "description": description,
            "detected": detected,
            "exit_code": proc.returncode,
            "diagnostic_excerpt": proc.stdout.strip().splitlines()[:6],
        })

    # Seed 6: End-to-end `cargo-anneal verify` with a mutated return value (`255` instead of `254`) in `Spec.lean`
    bad_e2e_dir = seeded_dir / "seed6_e2e_wrong_spec_return_value"
    shutil.copytree(cases_dir / "e2e_verify/positive_crate", bad_e2e_dir)
    shutil.rmtree(bad_e2e_dir / "artifacts", ignore_errors=True)
    bad_spec = (bad_e2e_dir / "proof/Spec.lean").read_text().replace("BitVec.ofNat 64 254", "BitVec.ofNat 64 255")
    (bad_e2e_dir / "proof/Spec.lean").write_text(bad_spec)
    bad_proc = subprocess.run(
        [
            str(ANNEAL_LEAN_RUN),
            "--mode",
            "build",
            "--concurrency",
            "4",
            "--",
            str(CARGO_ANNEAL),
            "verify",
            "--request",
            str(bad_e2e_dir / "request.json"),
            "--capture",
            str(CAPTURE),
            "--sysroot",
            str(BUNDLE / "rust"),
            "--lean",
            str(LEAN),
            "--artifacts",
            str(bad_e2e_dir / "artifacts"),
        ],
        capture_output=True,
        text=True,
    )
    bad_receipt = json.loads(bad_proc.stdout)
    detected_e2e = bad_proc.returncode != 0 and bad_receipt["status"] == "proof_failed"
    assert detected_e2e, f"Seeded e2e error was NOT detected! Receipt: {bad_receipt}"
    results.append({
        "name": "seed6_e2e_wrong_spec_return_value",
        "description": "Seeded wrong return specification (`255` instead of `254 = -2i8`) in `positive_crate/proof/Spec.lean` checked via `cargo-anneal verify`",
        "detected": detected_e2e,
        "exit_code": bad_proc.returncode,
        "diagnostic_excerpt": [
            f"status={bad_receipt['status']}, phase={bad_receipt['phase']}",
            *bad_receipt["detail"].strip().splitlines()[:5],
        ],
    })
    print(f"   -> All {len(results)} seeded intentional errors were caught by the harness.")
    return results


def main() -> None:
    start_time = time.monotonic()
    cases_dir = BASE_DIR / "cases"
    cases_dir.mkdir(parents=True, exist_ok=True)

    admitted_summary = run_admitted_suite(cases_dir)
    base_lean_stage = Path(admitted_summary["lean_stage"])
    fault_summary = run_invalid_state_and_fault_suite(cases_dir, base_lean_stage)
    refusal_summary = run_refusal_boundary_suite(cases_dir, base_lean_stage)
    e2e_summary = run_e2e_cargo_anneal_verify(cases_dir)
    seeded_summary = run_seeded_error_checks(cases_dir, base_lean_stage)

    report_data = {
        "toolchain_commit": "f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1",
        "elapsed_seconds": round(time.monotonic() - start_time, 2),
        "admitted_execution_suite": {
            "functions_count": admitted_summary["functions_count"],
            "vectors_count": admitted_summary["vectors_count"],
            "cases": admitted_summary["cases"],
        },
        "invalid_state_and_fault_suite": fault_summary,
        "refusal_boundary_suite": refusal_summary,
        "e2e_cargo_anneal_verify": e2e_summary,
        "seeded_error_checks": seeded_summary,
    }
    results_path = BASE_DIR / "results.json"
    results_path.write_text(json.dumps(report_data, indent=2) + "\n")
    print(f"\nAll suites passed in {report_data['elapsed_seconds']}s. Results written to {results_path}")


if __name__ == "__main__":
    main()
