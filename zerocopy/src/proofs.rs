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

use core::convert::TryInto as _;

use crate::{
    proof_support::{bool_from_byte, validate_and_read_sized},
    TryFromBytes,
};

fn char_from_bytes(bytes: &[u8], offset: usize) -> Option<char> {
    let representation: [u8; 4] = bytes[offset..offset + 4].try_into().unwrap();
    char::from_u32(u32::from_ne_bytes(representation))
}

fn cover_bool_cross_product(first: bool, second: bool) {
    kani::cover!(first && second);
    kani::cover!(first && !second);
    kani::cover!(!first && second);
    kani::cover!(!first && !second);
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
    let bytes = kani::any::<[u8; core::mem::size_of::<BoolAndChar>()]>();
    let flag_offset = core::mem::offset_of!(BoolAndChar, flag);
    let character_offset = core::mem::offset_of!(BoolAndChar, character);
    let flag = bool_from_byte(bytes[flag_offset]);
    let character = char_from_bytes(&bytes, character_offset);
    let flag_valid = flag.is_some();
    let character_valid = character.is_some();
    let expected = flag_valid && character_valid;

    // Domain: all initialized representations of this fixed `repr(C)` type.
    // Establishes: the generated validator and public value-reading API accept
    // exactly when both fields do.
    // Oracle: actual field offsets plus safe checked `char` construction and the
    // shared `bool` language-validity oracle. This is not a derive-generator or
    // generic struct-layout theorem.
    cover_bool_cross_product(flag_valid, character_valid);
    let read = validate_and_read_sized!(BoolAndChar, bytes, expected);
    if let Ok(BoolAndChar { flag: actual_flag, character: actual_character }) = read {
        assert_eq!(Some(actual_flag), flag);
        assert_eq!(Some(actual_character), character);
    }
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
    let bytes = kani::any::<[u8; core::mem::size_of::<PackedBoolAndChar>()]>();
    let flag_offset = core::mem::offset_of!(PackedBoolAndChar, flag);
    let character_offset = core::mem::offset_of!(PackedBoolAndChar, character);
    let flag = bool_from_byte(bytes[flag_offset]);
    let character = char_from_bytes(&bytes, character_offset);
    let flag_valid = flag.is_some();
    let character_valid = character.is_some();
    let expected = flag_valid && character_valid;

    // Domain: all initialized representations of this fixed packed type.
    // Establishes: the generated validator and public value-reading API accept
    // exactly when both fields do.
    // Oracle: actual packed field offsets plus safe checked `char` construction
    // and the shared `bool` language-validity oracle. This does not generalize
    // to other packing, alignment, or field combinations.
    cover_bool_cross_product(flag_valid, character_valid);
    let read = validate_and_read_sized!(PackedBoolAndChar, bytes, expected);
    // Move packed fields into aligned locals before comparing them.
    if let Ok(PackedBoolAndChar { flag: actual_flag, character: actual_character }) = read {
        assert_eq!(Some(actual_flag), flag);
        assert_eq!(Some(actual_character), character);
    }
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
    let bytes = kani::any::<[u8; core::mem::size_of::<BoolAtEitherEnd>()]>();
    let first_offset =
        core::mem::offset_of!(BoolAtEitherEnd, first) + core::mem::offset_of!(BoolFirst, flag);
    let last_offset =
        core::mem::offset_of!(BoolAtEitherEnd, last) + core::mem::offset_of!(BoolLast, flag);
    let first_valid = bool_from_byte(bytes[first_offset]).is_some();
    let last_valid = bool_from_byte(bytes[last_offset]).is_some();
    let expected = first_valid || last_valid;

    // Domain: all initialized representations of this fixed two-field union.
    // Establishes: the generated validator and public value-reading API accept
    // iff at least one field interpretation is valid, using actual union and
    // struct field offsets plus the shared `bool` oracle. The OR is explicitly
    // a zerocopy policy oracle, not evidence about Rust union validity or a
    // theorem about every union or derive input.
    cover_bool_cross_product(first_valid, last_valid);
    // Union fields cannot be inspected through safe Rust, but the public API's
    // result still must agree with the direct generated-validator result.
    let _ = validate_and_read_sized!(BoolAtEitherEnd, bytes, expected);
}

#[allow(dead_code)]
#[derive(TryFromBytes)]
#[repr(u8)]
enum BoolOrByte {
    Bool(bool),
    Byte(u8),
}

#[allow(dead_code)]
#[derive(Copy, Clone)]
#[repr(u8)]
enum BoolOrByteTag {
    Bool,
    Byte,
}

#[derive(Copy, Clone)]
#[repr(C)]
struct BoolVariantRepr {
    tag: BoolOrByteTag,
    payload: bool,
}

#[derive(Copy, Clone)]
#[repr(C)]
struct ByteVariantRepr {
    tag: BoolOrByteTag,
    payload: u8,
}

#[allow(dead_code)]
#[derive(Copy, Clone)]
#[repr(C)]
union BoolOrByteRepr {
    bool_variant: BoolVariantRepr,
    byte_variant: ByteVariantRepr,
}

#[kani::proof]
fn prove_try_from_bytes_derive_data_enum() {
    let bytes = kani::any::<[u8; core::mem::size_of::<BoolOrByte>()]>();

    // Residual language-layout rule: Rust Reference 1.93.0 specifies a
    // primitive-representation enum with fields as a `repr(C)` union of
    // `repr(C)` variant structs, whose first field is the tag and remaining
    // fields are the variant payload [1]. Both the real enum and its tag
    // surrogate declare the same implicit variants in the same order, so the
    // Reference's implicit-discriminant rules give them the same tags [2]. The
    // surrogate types above encode those language rules; `offset_of!` supplies
    // every union and struct offset rather than duplicating byte positions.
    //
    // [1] Per https://doc.rust-lang.org/1.93.0/reference/type-layout.html#primitive-representation-of-enums-with-fields:
    //
    //     The first field of each struct ... is ... "the tag" and the remaining
    //     fields are the fields of that variant.
    //
    // [2] Per https://doc.rust-lang.org/1.93.0/reference/items/enumerations.html#implicit-discriminants:
    //
    //     If the discriminant of the first variant ... is unspecified, then it
    //     is set to zero. Each later implicit discriminant is "one higher than
    //     the discriminant of the previous variant".
    assert_eq!(core::mem::size_of::<BoolOrByte>(), core::mem::size_of::<BoolOrByteRepr>());
    assert_eq!(core::mem::align_of::<BoolOrByte>(), core::mem::align_of::<BoolOrByteRepr>());
    let bool_variant_offset = core::mem::offset_of!(BoolOrByteRepr, bool_variant);
    let byte_variant_offset = core::mem::offset_of!(BoolOrByteRepr, byte_variant);
    let tag_offset = bool_variant_offset + core::mem::offset_of!(BoolVariantRepr, tag);
    let byte_tag_offset = byte_variant_offset + core::mem::offset_of!(ByteVariantRepr, tag);
    assert_eq!(tag_offset, byte_tag_offset);
    let bool_payload_offset = bool_variant_offset + core::mem::offset_of!(BoolVariantRepr, payload);
    let byte_payload_offset = byte_variant_offset + core::mem::offset_of!(ByteVariantRepr, payload);
    let tag = bytes[tag_offset];
    let bool_payload = bool_from_byte(bytes[bool_payload_offset]);
    let bool_payload_valid = bool_payload.is_some();
    let expected = (tag == BoolOrByteTag::Bool as u8 && bool_payload_valid)
        || tag == BoolOrByteTag::Byte as u8;

    // Domain: all initialized representations of this fixed
    // `repr(u8)` data enum. Establishes: the generated validator and public
    // value-reading API agree that the `Bool` tag additionally validates its
    // payload, the `Byte` tag accepts every `u8`, and every other tag is
    // rejected. The language-defined surrogate is a residual manual layout
    // oracle; this is not a generic enum-layout or derive-generator theorem.
    kani::cover!(tag == BoolOrByteTag::Bool as u8 && bool_payload_valid);
    kani::cover!(tag == BoolOrByteTag::Bool as u8 && !bool_payload_valid);
    kani::cover!(tag == BoolOrByteTag::Byte as u8);
    kani::cover!(tag >= 2);
    let read = validate_and_read_sized!(BoolOrByte, bytes, expected);
    match read {
        Ok(BoolOrByte::Bool(actual)) => {
            assert_eq!(tag, BoolOrByteTag::Bool as u8);
            assert_eq!(Some(actual), bool_payload);
        }
        Ok(BoolOrByte::Byte(actual)) => {
            assert_eq!(tag, BoolOrByteTag::Byte as u8);
            assert_eq!(actual, bytes[byte_payload_offset]);
        }
        Err(_) => {}
    }
}
