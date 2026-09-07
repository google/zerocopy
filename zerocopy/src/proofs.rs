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
//! Configuration: Uses the common Kani CI configuration documented in
//! `agent_docs/validation.md`: the CI-pinned Kani release and its bundled
//! x86_64-unknown-linux-gnu compiler, the stable-compatible feature bundle,
//! `-Zfunction-contracts`, and one layout selected by `--randomize-layout` per
//! invocation.
//!
//! These harnesses call generated [`TryFromBytes::is_bit_valid`] methods on
//! initialized bytes. They invoke the public value-reading API only after an
//! independent safe construction and documented layout rules establish that
//! the candidate representation is valid. Each theorem covers one fixed,
//! sized derive input and every byte pattern for that input on Kani's target.
//! This is not a generator theorem: it does not cover other derive inputs,
//! configurations, targets, or properties absent from Kani's memory model. The
//! sized inputs also deliberately avoid the nested-DST layout issue tracked in
//! #3630.

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
    let expected = match (flag, character) {
        (Some(flag), Some(character)) => Some(BoolAndChar { flag, character }),
        _ => None,
    };

    // Domain: all initialized representations of this fixed `repr(C)` type.
    // Establishes: the generated validator accepts exactly when both fields
    // do. On those independently valid inputs, the public value-reading API
    // succeeds and returns the oracle's field values.
    // Oracle: actual field offsets plus safe checked `char` construction and the
    // shared `bool` language-validity oracle. This is not a derive-generator or
    // generic struct-layout theorem.
    cover_bool_cross_product(flag_valid, character_valid);
    let read = validate_and_read_sized!(BoolAndChar, bytes, expected);
    if let Some(BoolAndChar { flag: actual_flag, character: actual_character }) = read {
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
    let expected = match (flag, character) {
        (Some(flag), Some(character)) => Some(PackedBoolAndChar { flag, character }),
        _ => None,
    };

    // Domain: all initialized representations of this fixed packed type.
    // Establishes: the generated validator accepts exactly when both fields
    // do. On those independently valid inputs, the public value-reading API
    // succeeds and returns the oracle's field values.
    // Oracle: actual packed field offsets plus safe checked `char` construction
    // and the shared `bool` language-validity oracle. This does not generalize
    // to other packing, alignment, or field combinations.
    cover_bool_cross_product(flag_valid, character_valid);
    let read = validate_and_read_sized!(PackedBoolAndChar, bytes, expected);
    // Move packed fields into aligned locals before comparing them.
    if let Some(PackedBoolAndChar { flag: actual_flag, character: actual_character }) = read {
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
    let first_base = core::mem::offset_of!(BoolAtEitherEnd, first);
    let last_base = core::mem::offset_of!(BoolAtEitherEnd, last);
    let first_offset = first_base + core::mem::offset_of!(BoolFirst, flag);
    let first_byte_offset = first_base + core::mem::offset_of!(BoolFirst, byte);
    let last_offset = last_base + core::mem::offset_of!(BoolLast, flag);
    let last_byte_offset = last_base + core::mem::offset_of!(BoolLast, byte);
    assert_eq!(
        core::mem::size_of::<BoolFirst>(),
        core::mem::size_of::<bool>() + core::mem::size_of::<u8>()
    );
    assert_eq!(core::mem::size_of::<BoolAtEitherEnd>(), core::mem::size_of::<BoolFirst>());
    assert_eq!(
        core::mem::size_of::<BoolLast>(),
        core::mem::size_of::<u8>() + core::mem::size_of::<bool>()
    );
    assert_eq!(core::mem::size_of::<BoolAtEitherEnd>(), core::mem::size_of::<BoolLast>());
    let first = bool_from_byte(bytes[first_offset]);
    let last = bool_from_byte(bytes[last_offset]);
    let first_valid = first.is_some();
    let last_valid = last.is_some();

    // Both field types span the entire union without padding, as checked above.
    // The safely constructed active field therefore reconstructs the exact two
    // candidate bytes through compiler-computed offsets, without relying on
    // any validity premise about padding or an inactive field. No union field
    // is read by this proof.
    let expected = if let Some(flag) = first {
        Some(BoolAtEitherEnd { first: BoolFirst { flag, byte: bytes[first_byte_offset] } })
    } else {
        last.map(|flag| BoolAtEitherEnd { last: BoolLast { byte: bytes[last_byte_offset], flag } })
    };

    // Domain: all initialized representations of this fixed two-field union.
    // Establishes: the generated validator accepts iff at least one field
    // interpretation is valid, using actual union and struct field offsets
    // plus the shared `bool` oracle. On accepted inputs, the public value-read
    // succeeds. The OR is explicitly a zerocopy policy oracle, not evidence
    // about Rust union validity or a theorem about every union or derive input.
    cover_bool_cross_product(first_valid, last_valid);
    // Union fields cannot be inspected through safe Rust, so the returned value
    // is deliberately not used as a value oracle.
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
    //     Each union member is a `repr(C)` struct whose first field is the
    //     primitive-representation tag of the fieldless enum; "the remaining
    //     fields are the fields of that variant."
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
    let expected = if tag == BoolOrByteTag::Bool as u8 {
        bool_payload.map(BoolOrByte::Bool)
    } else if tag == BoolOrByteTag::Byte as u8 {
        Some(BoolOrByte::Byte(bytes[byte_payload_offset]))
    } else {
        None
    };

    // Domain: all initialized representations of this fixed
    // `repr(u8)` data enum. Establishes: the generated validator requires the
    // `Bool` tag's payload to be valid, accepts every payload for the `Byte`
    // tag, and rejects every other tag. The public API is invoked only for the
    // first two cases, where it must succeed and return the corresponding safe
    // variant constructed above. The language-defined surrogate is a residual
    // manual layout oracle; this is not a generic enum-layout or
    // derive-generator theorem.
    kani::cover!(tag == BoolOrByteTag::Bool as u8 && bool_payload_valid);
    kani::cover!(tag == BoolOrByteTag::Bool as u8 && !bool_payload_valid);
    kani::cover!(tag == BoolOrByteTag::Byte as u8);
    kani::cover!(tag >= 2);
    let read = validate_and_read_sized!(BoolOrByte, bytes, expected);
    match read {
        Some(BoolOrByte::Bool(actual)) => {
            assert_eq!(tag, BoolOrByteTag::Bool as u8);
            assert_eq!(Some(actual), bool_payload);
        }
        Some(BoolOrByte::Byte(actual)) => {
            assert_eq!(tag, BoolOrByteTag::Byte as u8);
            assert_eq!(actual, bytes[byte_payload_offset]);
        }
        None => {}
    }
}
