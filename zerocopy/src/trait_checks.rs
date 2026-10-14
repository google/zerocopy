// SPDX-License-Identifier: BSD-2-Clause OR Apache-2.0 OR MIT
//
// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Checked trait laws are assumptions at generic calls and proofs at impls.
//!
//! These small examples exercise both directions. A generic consumer receives
//! the law of its exact Rust dictionary. A concrete caller must discharge that
//! law for the selected implementation before reusing the consumer.

use core::marker::PhantomData;

/// Encoding and decoding form one total round trip on every byte.
///
/// ```aeneas
/// invariant byte_roundtrip for self =>
///   ∀ byte, (do let encoded ← self.encode byte; self.decode encoded)
///     ⦃ result => result = byte ⦄
/// ```
trait ByteCodec {
    fn encode(byte: u8) -> u8;
    fn decode(byte: u8) -> u8;
}

struct XorCodec;

impl ByteCodec for XorCodec {
    fn encode(byte: u8) -> u8 {
        byte ^ 0xaa
    }

    fn decode(byte: u8) -> u8 {
        byte ^ 0xaa
    }
}

/// A generic implementation forwards to the exact supplied dictionary.
struct Forward<C>(PhantomData<C>);

impl<C: ByteCodec> ByteCodec for Forward<C> {
    fn encode(byte: u8) -> u8 {
        C::encode(byte)
    }

    fn decode(byte: u8) -> u8 {
        C::decode(byte)
    }
}

/// ```aeneas
/// spec byte_codec_roundtrip_spec
///   ensures result => result = byte
/// ```
fn byte_codec_roundtrip<C: ByteCodec>(byte: u8) -> u8 {
    C::decode(C::encode(byte))
}

/// Concrete and generic impl proofs compose without changing function bodies.
///
/// ```aeneas
/// spec forwarded_byte_codec_spec
///   ensures result => result = byte
/// ```
fn forwarded_byte_codec(byte: u8) -> u8 {
    byte_codec_roundtrip::<Forward<XorCodec>>(byte)
}

fn require_into_bytes<T: crate::IntoBytes>() {}

/// Forces extraction of the existing array IntoBytes implementation and its
/// primitive and nested dependencies. CI checks the generic implementation law
/// for every count; these concrete uses also exercise Rust's trait selection.
///
/// ```aeneas
/// spec array_into_bytes_spec
///   ensures _ => AeneasSpecs.RustModel.initializedRepresentation (Aeneas.Std.Array Bool 3#usize)
///   ensures _ => AeneasSpecs.RustModel.initializedRepresentation (Aeneas.Std.Array U8 3#usize)
///   ensures _ => AeneasSpecs.RustModel.initializedRepresentation (Aeneas.Std.Array Unit 4#usize)
///   ensures _ => AeneasSpecs.RustModel.initializedRepresentation (Aeneas.Std.Array Bool 0#usize)
///   ensures _ => AeneasSpecs.RustModel.initializedRepresentation
///     (Aeneas.Std.Array (Aeneas.Std.Array Bool 2#usize) 3#usize)
/// ```
fn check_array_into_bytes() {
    require_into_bytes::<[bool; 3]>();
    require_into_bytes::<[u8; 3]>();
    require_into_bytes::<[(); 4]>();
    require_into_bytes::<[bool; 0]>();
    require_into_bytes::<[[bool; 2]; 3]>();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn trait_law_examples() {
        for byte in 0..=u8::MAX {
            assert_eq!(forwarded_byte_codec(byte), byte);
        }
        check_array_into_bytes();
    }
}
