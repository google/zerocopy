// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![no_std]

//! Stage-1 Profile v1 litmus control-flow, loop, cast, `char`, `Ordering`,
//! move/reinitialization, and fieldless-enum passing fixtures.

#[repr(i16)]
pub enum SignedTag {
    NegTwo = -2,
    Zero = 0,
    Seven = 7,
}

#[repr(u8)]
pub enum Solo {
    Only = 42,
}

pub fn loop_sum_u32(n: u32) -> u32 {
    let mut acc = 0u32;
    let mut i = 1u32;
    while i <= n {
        acc += i;
        i += 1;
    }
    acc
}

pub fn cast_char_bool_int(c: char, byte: u8, flag: bool, signed: i16) -> u32 {
    let from_byte: char = byte as char;
    let trunc_u8: u8 = c as u8;
    let flag_i64: i64 = flag as i64;
    let ext_i32: i32 = signed as i32;
    if c < from_byte {
        (trunc_u8 as u32) ^ (flag_i64 as u32)
    } else {
        (c as u32) + (ext_i32 as u32)
    }
}

pub fn cmp_three_way(a: i32, b: i32) -> core::cmp::Ordering {
    const LESS: core::cmp::Ordering = core::cmp::Ordering::Less;
    const EQUAL: core::cmp::Ordering = core::cmp::Ordering::Equal;
    const GREATER: core::cmp::Ordering = core::cmp::Ordering::Greater;
    if a < b {
        LESS
    } else if a > b {
        GREATER
    } else {
        EQUAL
    }
}

pub fn match_signed_enum(tag: SignedTag) -> i32 {
    match tag {
        SignedTag::NegTwo => -20,
        SignedTag::Zero => 0,
        SignedTag::Seven => 70,
    }
}

pub fn match_zst_enum(solo: Solo) -> u8 {
    match solo {
        Solo::Only => 42,
    }
}

pub fn move_then_reinit(x: SignedTag, replacement: SignedTag) -> i16 {
    let mut slot = x;
    let moved = slot;
    slot = replacement;
    (moved as i16) + (slot as i16)
}
