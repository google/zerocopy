// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! The one stable-identifier contract shared by CI policy and baseline data.
//!
//! Policy references and frozen baseline rows cross the same JSON and GitHub
//! matrix boundaries. Keep both consumers on this complete validator so a
//! grammar or resource-bound change cannot silently make one input language
//! more permissive than the other.

/// Maximum bytes in one stable identifier.
///
/// CI planning clones identifiers while resolving selections. Aggregate count
/// limits bound the number of clones; this limit bounds the bytes in each one.
pub(crate) const MAX_ID_BYTES: usize = 256;

/// Why text is not a stable CI identifier.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum IdentifierError {
    /// The spelling exceeded [`MAX_ID_BYTES`].
    TooLong {
        /// Observed byte length.
        bytes: usize,
    },
    /// The spelling did not use the canonical lowercase ASCII grammar.
    InvalidSyntax,
}

/// Validates the complete stable-identifier contract.
pub(crate) fn validate(value: &str) -> Result<(), IdentifierError> {
    if value.len() > MAX_ID_BYTES {
        return Err(IdentifierError::TooLong { bytes: value.len() });
    }
    let valid = !value.is_empty()
        && value.bytes().enumerate().all(|(index, byte)| match byte {
            b'a'..=b'z' | b'0'..=b'9' | b'_' => true,
            b'-' | b'.' => index != 0,
            _ => false,
        })
        && !value.ends_with('-')
        && !value.ends_with('.')
        && value != "."
        && value != "..";
    if valid {
        Ok(())
    } else {
        Err(IdentifierError::InvalidSyntax)
    }
}
