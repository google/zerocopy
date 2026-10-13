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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn trait_law_examples() {
        for byte in 0..=u8::MAX {
            assert_eq!(forwarded_byte_codec(byte), byte);
        }
    }
}
