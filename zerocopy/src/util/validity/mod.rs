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

//! Value predicates shared by the actual scalar `TryFromBytes` implementations.
//!
//! Candidates retain their integer representation until these checks finish.
//! In particular, a candidate for `bool` is a `u8`, not a Lean or Rust `bool`
//! which would already exclude invalid encodings. Reading the candidate through
//! `Maybe` remains the implementation's separate pointer safety argument.

/// Accepts exactly the two boolean bit patterns.
///
/// ```aeneas
/// spec bool_encoding_spec
///   ensures(raw) r => r = decide (byte.val = 0 ∨ byte.val = 1)
/// ```
#[inline]
pub(crate) fn bool_encoding(byte: u8) -> bool {
    byte < 2
}

/// Accepts exactly the nonzero word representations.
///
/// ```aeneas
/// spec nonzero_encoding_spec
///   ensures(raw) r => r = decide (n.val ≠ 0)
/// ```
#[inline]
pub(crate) fn nonzero_encoding(n: usize) -> bool {
    n != 0
}

/// Reads an initialized raw byte, with the ordinary slice bounds check.
///
/// This narrow, source-bound interpretation avoids importing the whole generic
/// indexing dictionary (including unsupported pointer operations) to read one
/// byte. It does not create a bool, a reference, or a possibly invalid integer.
/// Aeneas checks its complete guarded interpretation independently in Check.
#[inline]
#[allow(clippy::indexing_slicing)] // The model explicitly preserves this bounds check.
pub(crate) fn read_byte(bytes: &[u8], index: usize) -> u8 {
    bytes[index]
}
