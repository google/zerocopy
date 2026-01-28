// Copyright (c) The mukti Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::VersionRangeKind;
use std::num::ParseIntError;
use thiserror::Error;

#[derive(Debug, Error)]
#[non_exhaustive]
#[error("error parsing version range `{input}` at {} component", .component.description())]
pub struct VersionRangeParseError {
    /// The input that failed to parse.
    pub input: String,

    /// The component that failed to parse.
    pub component: VersionRangeKind,

    /// The error that occurred.
    #[source]
    pub error: ParseIntError,
}

impl VersionRangeParseError {
    pub(crate) fn new(input: &str, component: VersionRangeKind, error: ParseIntError) -> Self {
        Self {
            input: input.to_owned(),
            component,
            error,
        }
    }
}
