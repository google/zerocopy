// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use std::fmt;

/// A descriptor for the kind of dependency.
///
/// Cargo dependencies may be one of three kinds.
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub enum DependencyKind {
    /// Normal dependencies.
    ///
    /// These are specified in the `[dependencies]` section.
    Normal,

    /// Dependencies used for development only.
    ///
    /// These are specified in the `[dev-dependencies]` section, and are used for tests,
    /// benchmarks and similar.
    Development,

    /// Dependencies used for build scripts.
    ///
    /// These are specified in the `[build-dependencies]` section.
    Build,
}

impl DependencyKind {
    /// A list of all the possible values of `DependencyKind`.
    pub const VALUES: &'static [Self; 3] = &[
        DependencyKind::Normal,
        DependencyKind::Development,
        DependencyKind::Build,
    ];

    /// Returns a string representing the kind of dependency this is.
    pub fn to_str(self) -> &'static str {
        match self {
            DependencyKind::Normal => "normal",
            DependencyKind::Development => "dev",
            DependencyKind::Build => "build",
        }
    }
}

impl fmt::Display for DependencyKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.to_str())
    }
}
