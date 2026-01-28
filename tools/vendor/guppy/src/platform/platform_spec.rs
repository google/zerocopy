// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

#[allow(unused_imports)]
use crate::platform::EnabledTernary;
use crate::{errors::TargetSpecError, platform::Platform};
use std::sync::Arc;

/// A specifier for a single platform, or for a range of platforms.
///
/// Some uses of `guppy` care about a single platform, and others care about queries against the
/// intersection of all hypothetical platforms, or against a union of any of them. `PlatformSpec`
/// handles the
///
/// `PlatformSpec` does not currently support expressions, but it might in the future, using an
/// [SMT solver](https://en.wikipedia.org/wiki/Satisfiability_modulo_theories).
#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum PlatformSpec {
    /// The intersection of all platforms.
    ///
    /// Dependency queries performed against this variant will return [`EnabledTernary::Enabled`] if
    /// and only if a dependency is not platform-dependent. They can never return
    /// [`EnabledTernary::Unknown`].
    ///
    /// This variant does not currently understand expressions that always evaluate to true
    /// (tautologies), like `cfg(any(unix, not(unix)))` or `cfg(all())`. In the future, an SMT
    /// solver would be able to handle such expressions.
    Always,

    /// An individual platform.
    ///
    /// Dependency queries performed against this variant will return [`EnabledTernary::Enabled`] if
    /// and only if a dependency is enabled on this platform. They may also return
    /// [`EnabledTernary::Unknown`] if a platform is not enabled.
    Platform(Arc<Platform>),

    /// The union of all platforms.
    ///
    /// Dependency queries performed against this variant will return [`EnabledTernary::Enabled`] if
    /// a dependency is enabled on any platform.
    ///
    /// This variant does not currently understand expressions that always evaluate to false
    /// (contradictions), like `cfg(all(unix, not(unix)))` or `cfg(any())`. In the future, an SMT
    /// solver would be able to handle such expressions.
    Any,
}

impl PlatformSpec {
    /// Previous name for [`Self::build_target`], renamed to clarify what
    /// `current` means.
    ///
    /// This method is deprecated and will be removed in a future version.
    #[deprecated(
        since = "0.17.13",
        note = "this method has been renamed to `build_target`"
    )]
    #[inline]
    pub fn current() -> Result<Self, TargetSpecError> {
        Self::build_target()
    }

    /// Returns a `PlatformSpec` corresponding to the target platform, as
    /// determined at build time.
    ///
    /// Returns an error if the build target was unknown to the version of
    /// `target-spec` in use.
    pub fn build_target() -> Result<Self, TargetSpecError> {
        Ok(PlatformSpec::Platform(Arc::new(Platform::build_target()?)))
    }
}

impl<T: Into<Arc<Platform>>> From<T> for PlatformSpec {
    #[inline]
    fn from(platform: T) -> Self {
        PlatformSpec::Platform(platform.into())
    }
}
