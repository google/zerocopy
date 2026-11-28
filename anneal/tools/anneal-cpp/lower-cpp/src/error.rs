// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use std::fmt;

/// Every way lowering can refuse a bundle. Lowering never guesses: anything
/// it cannot translate exactly is reported through one of these variants.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LowerError {
    /// The input is not valid JSON.
    Json { detail: String },
    /// The JSON does not match the `RawCppBundle` v1 schema.
    Schema { detail: String },
    /// The sealed language policy is outside the admitted dialects (C11 and
    /// C++17/C++20): exceptions, fast-math, trapping overflow, another C++
    /// dialect, or a non-64-bit target.
    UnsupportedLangPolicy { detail: String },
    /// A full-expression has two unsequenced (or indeterminately sequenced)
    /// subexpressions whose effects conflict, so no single evaluation order
    /// is faithful (Single-Side-Effect Normal Form gate).
    UnsequencedSideEffects { detail: String },
    /// A construct outside the admitted C11 and C++20 subsets (or emitted by
    /// the extractor as `unsupported_*`).
    UnsupportedConstruct { detail: String },
    /// Clang's ABI classification disagrees with the declared signature.
    AbiMismatch { detail: String },
    /// The bundle is well-typed JSON but semantically malformed (e.g. a
    /// `break` outside any loop, an undeclared variable, an unknown record).
    Malformed { detail: String },
}

impl LowerError {
    pub fn kind_name(&self) -> &'static str {
        match self {
            LowerError::Json { .. } => "Json",
            LowerError::Schema { .. } => "Schema",
            LowerError::UnsupportedLangPolicy { .. } => "UnsupportedLangPolicy",
            LowerError::UnsequencedSideEffects { .. } => "UnsequencedSideEffects",
            LowerError::UnsupportedConstruct { .. } => "UnsupportedConstruct",
            LowerError::AbiMismatch { .. } => "AbiMismatch",
            LowerError::Malformed { .. } => "Malformed",
        }
    }

    fn detail(&self) -> &str {
        match self {
            LowerError::Json { detail }
            | LowerError::Schema { detail }
            | LowerError::UnsupportedLangPolicy { detail }
            | LowerError::UnsequencedSideEffects { detail }
            | LowerError::UnsupportedConstruct { detail }
            | LowerError::AbiMismatch { detail }
            | LowerError::Malformed { detail } => detail,
        }
    }
}

impl fmt::Display for LowerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.kind_name(), self.detail())
    }
}

impl std::error::Error for LowerError {}

pub type Result<T> = std::result::Result<T, LowerError>;

pub(crate) fn schema<T>(detail: impl Into<String>) -> Result<T> {
    Err(LowerError::Schema { detail: detail.into() })
}

pub(crate) fn unsupported<T>(detail: impl Into<String>) -> Result<T> {
    Err(LowerError::UnsupportedConstruct { detail: detail.into() })
}

pub(crate) fn malformed<T>(detail: impl Into<String>) -> Result<T> {
    Err(LowerError::Malformed { detail: detail.into() })
}
