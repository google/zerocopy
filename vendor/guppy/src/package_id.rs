// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use std::fmt;

/// An "opaque" identifier for a package.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[allow(clippy::derived_hash_with_manual_eq)] // safe because the same PartialEq impl is used everywhere
pub struct PackageId {
    /// The underlying string representation of an ID.
    repr: Box<str>,
}

impl PackageId {
    /// Creates a new `PackageId`.
    pub fn new(s: impl Into<Box<str>>) -> Self {
        Self { repr: s.into() }
    }

    pub(super) fn from_metadata(id: cargo_metadata::PackageId) -> Self {
        Self {
            repr: id.repr.into_boxed_str(),
        }
    }

    /// Returns the inner representation of a package ID. This is generally an opaque string and its
    /// precise format is subject to change.
    pub fn repr(&self) -> &str {
        &self.repr
    }
}

impl fmt::Display for PackageId {
    fn fmt(&self, f: &mut fmt::Formatter) -> std::fmt::Result {
        fmt::Display::fmt(&self.repr, f)
    }
}

impl PartialEq<&PackageId> for PackageId {
    fn eq(&self, other: &&PackageId) -> bool {
        self.eq(*other)
    }
}

impl PartialEq<PackageId> for &PackageId {
    fn eq(&self, other: &PackageId) -> bool {
        (*self).eq(other)
    }
}
