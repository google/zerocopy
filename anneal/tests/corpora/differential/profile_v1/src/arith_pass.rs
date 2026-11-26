// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![no_std]

//! Stage-1 Profile v1 litmus arithmetic, `core::num` wrapping sysroot-call,
//! shift, bitwise, bool, and comparison passing fixtures.

pub fn u32_wrapping_add(a: u32, b: u32) -> u32 {
    a + b
}

pub fn i32_wrapping_sub(a: i32, b: i32) -> i32 {
    a - b
}

pub fn i16_wrapping_mul(a: i16, b: i16) -> i16 {
    a * b
}

pub fn i32_wrapping_neg(a: i32) -> i32 {
    -a
}

pub fn u8_wrapping_add_sysroot(a: u8, b: u8) -> u8 {
    a.wrapping_add(b)
}

pub fn u32_shl_masked(a: u32, b: u32) -> u32 {
    a << b
}

pub fn u32_shl_signed_rhs(a: u32, b: i32) -> u32 {
    a << b
}

pub fn i32_shr_arithmetic(a: i32, b: u32) -> i32 {
    a >> b
}

pub fn u64_bitwise_mix(a: u64, b: u64) -> u64 {
    (!a) ^ b
}

pub fn bool_logic_xor(a: bool, b: bool) -> bool {
    a ^ b
}

pub fn i64_lt_cmp(a: i64, b: i64) -> bool {
    a < b
}

pub fn u128_bitwise_mix(a: u128, b: u128) -> u128 {
    (!a) ^ (b | 0x0f0f_u128) & 0xffff_ffff_ffff_ffff_ffff_ffff_ffff_fffe_u128
}
