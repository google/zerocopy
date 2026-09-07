// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT
//
// Copyright 2026 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Representative Kani regression proofs for generated implementations.
//!
//! These harnesses call generated [`TryFromBytes::is_bit_valid`] methods on
//! initialized bytes before materializing values of the destination types.
//! Each theorem covers one fixed, sized derive input and every byte pattern for
//! that input on Kani's target. This is not a generator theorem: it does not
//! cover other derive inputs, configurations, targets, or properties absent
//! from Kani's memory model. The sized inputs also deliberately avoid the
//! nested-DST layout issue tracked in #3630.

use crate::{
    pointer::{cast::CastSizedExact, invariant::Initialized, BecauseImmutable, Ptr},
    wrappers::ReadOnly,
    TryFromBytes,
};

macro_rules! validator_accepts {
    ($ty:ty, $bytes:expr) => {{
        let source = ReadOnly::new($bytes);
        let mut candidate = Ptr::from_ref(&source)
            .transmute_with::<ReadOnly<$ty>, Initialized, CastSizedExact, BecauseImmutable>();
        <$ty as TryFromBytes>::is_bit_valid(candidate.reborrow_shared())
    }};
}

fn char_is_valid(bytes: [u8; 4]) -> bool {
    let scalar = u32::from_ne_bytes(bytes);
    scalar <= 0x10FFFF && !(scalar >= 0xD800 && scalar <= 0xDFFF)
}

#[allow(dead_code)]
#[derive(TryFromBytes)]
#[repr(C)]
struct BoolAndChar {
    flag: bool,
    character: char,
}

#[kani::proof]
fn prove_try_from_bytes_derive_struct() {
    let bytes = kani::any::<[u8; 8]>();
    let flag_valid = bytes[0] < 2;
    let character_valid = char_is_valid([bytes[4], bytes[5], bytes[6], bytes[7]]);
    let expected = flag_valid && character_valid;

    kani::cover!(flag_valid && character_valid);
    kani::cover!(flag_valid && !character_valid);
    kani::cover!(!flag_valid && character_valid);
    kani::cover!(!flag_valid && !character_valid);
    assert_eq!(validator_accepts!(BoolAndChar, bytes), expected);
}

#[allow(dead_code)]
#[derive(TryFromBytes)]
#[repr(C, packed)]
struct PackedBoolAndChar {
    flag: bool,
    character: char,
}

#[kani::proof]
fn prove_try_from_bytes_derive_packed_struct() {
    let bytes = kani::any::<[u8; 5]>();
    let flag_valid = bytes[0] < 2;
    let character_valid = char_is_valid([bytes[1], bytes[2], bytes[3], bytes[4]]);
    let expected = flag_valid && character_valid;

    kani::cover!(flag_valid && character_valid);
    kani::cover!(flag_valid && !character_valid);
    kani::cover!(!flag_valid && character_valid);
    kani::cover!(!flag_valid && !character_valid);
    assert_eq!(validator_accepts!(PackedBoolAndChar, bytes), expected);
}

#[allow(dead_code)]
#[derive(Copy, Clone, TryFromBytes)]
#[repr(C)]
struct BoolFirst {
    flag: bool,
    byte: u8,
}

#[allow(dead_code)]
#[derive(Copy, Clone, TryFromBytes)]
#[repr(C)]
struct BoolLast {
    byte: u8,
    flag: bool,
}

#[allow(dead_code)]
#[derive(TryFromBytes)]
#[repr(C)]
union BoolAtEitherEnd {
    first: BoolFirst,
    last: BoolLast,
}

#[kani::proof]
fn prove_try_from_bytes_derive_union() {
    let bytes = kani::any::<[u8; 2]>();
    let first_valid = bytes[0] < 2;
    let last_valid = bytes[1] < 2;
    let expected = first_valid || last_valid;

    kani::cover!(first_valid && last_valid);
    kani::cover!(first_valid && !last_valid);
    kani::cover!(!first_valid && last_valid);
    kani::cover!(!first_valid && !last_valid);
    assert_eq!(validator_accepts!(BoolAtEitherEnd, bytes), expected);
}

#[allow(dead_code)]
#[derive(TryFromBytes)]
#[repr(u8)]
enum BoolOrByte {
    Bool(bool),
    Byte(u8),
}

#[kani::proof]
fn prove_try_from_bytes_derive_data_enum() {
    let bytes = kani::any::<[u8; 2]>();
    let expected = (bytes[0] == 0 && bytes[1] < 2) || bytes[0] == 1;

    kani::cover!(bytes[0] == 0 && bytes[1] < 2);
    kani::cover!(bytes[0] == 0 && bytes[1] >= 2);
    kani::cover!(bytes[0] == 1);
    kani::cover!(bytes[0] >= 2);
    assert_eq!(validator_accepts!(BoolOrByte, bytes), expected);
}
