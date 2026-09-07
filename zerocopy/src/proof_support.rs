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

//! Shared mechanics and language oracles for Kani proofs.
//!
//! Keep semantic expectations in their individual proof modules unless Rust
//! itself defines the expectation here. This module only factors the subtle
//! operations of invoking a sized validator on arbitrary initialized bytes and
//! comparing its answer with the public value-reading API. It also contains the
//! one byte-level oracle for which Kani's Rust toolchain has no safe checked
//! conversion. Unsized validation stays local to the theorem because its
//! pointer cast and metadata are part of what that theorem must expose.
//!
//! There is deliberately no generic `T`-validity oracle here. Generating a `T`
//! can witness only valid values, while materializing arbitrary bytes as `T`
//! before validation would itself be undefined for invalid bytes. Each proof
//! therefore supplies a type-specific safe checked constructor when Rust
//! exposes one and states the residual language rule when it does not.
//!
//! Per https://doc.rust-lang.org/1.93.0/reference/behavior-considered-undefined.html#invalid-values:
//!
//! > producing an invalid value is immediate undefined behavior.

// Evaluate a sized validator before the end-to-end API may materialize `T`.
// `$bytes` is wrapped as initialized, read-only storage; `CastSizedExact`
// requires the source and destination to have exactly the same size. Keeping
// this operation here makes the subtle setup identical across proofs while
// leaving each theorem's semantic oracle and postconditions at its call site.
macro_rules! validator_accepts_sized {
    ($ty:ty, $bytes:expr) => {{
        use $crate::{
            pointer::{cast::CastSizedExact, invariant::Initialized, BecauseImmutable, Ptr},
            wrappers::ReadOnly,
        };

        let source = ReadOnly::new($bytes);
        let mut candidate = Ptr::from_ref(&source)
            .transmute_with::<ReadOnly<$ty>, Initialized, CastSizedExact, BecauseImmutable>();
        <$ty as $crate::TryFromBytes>::is_bit_valid(candidate.reborrow_shared())
    }};
}

pub(crate) use validator_accepts_sized;

// Check both layers under proof against the caller's semantic oracle, then
// return the public API result so the caller can state type-specific value
// postconditions. Restricting `$bytes` to an identifier avoids evaluating an
// input expression twice. The array is copied only into the raw-validator
// setup; the public API continues to read the original initialized bytes.
macro_rules! validate_and_read_sized {
    ($ty:ty, $bytes:ident, $expected_valid:expr) => {{
        let expected_valid = $expected_valid;
        assert_eq!($crate::proof_support::validator_accepts_sized!($ty, $bytes), expected_valid);
        let result = <$ty as $crate::TryFromBytes>::try_read_from_bytes(&$bytes);
        assert_eq!(result.is_ok(), expected_valid);
        result
    }};
}

pub(crate) use validate_and_read_sized;

/// Interprets a byte using Rust's object representation for `bool`.
///
/// This uses safe `From<bool> for u8` conversions for the two representations
/// Rust can construct. The Reference rules out every other byte. Kani 0.67's
/// Rust toolchain has no safe checked conversion in the other direction, so
/// that final exclusion remains a small, centralized language rule rather than
/// being reconstructed separately in each proof. This function never creates
/// an invalid `bool`.
///
/// Per https://doc.rust-lang.org/1.93.0/std/primitive.u8.html#impl-From%3Cbool%3E-for-u8:
///
/// > The resulting value is 1 for `true` and 0 for `false` values.
///
/// Per https://doc.rust-lang.org/1.93.0/reference/types/boolean.html#representation:
///
/// > It is undefined behavior for an object with the boolean type to have any
/// > other bit pattern.
pub(crate) fn bool_from_byte(byte: u8) -> Option<bool> {
    if byte == u8::from(false) {
        Some(false)
    } else if byte == u8::from(true) {
        Some(true)
    } else {
        None
    }
}
