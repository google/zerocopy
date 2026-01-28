// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::platform::{Platform, PlatformSpec};
use std::ops::{BitAnd, BitOr};
use target_spec::TargetSpec;

/// The status of a dependency or feature, which is possibly platform-dependent.
///
/// This is a sub-status of [`EnabledStatus`](crate::graph::EnabledStatus).
#[derive(Copy, Clone, Debug)]
pub enum PlatformStatus<'g> {
    /// This dependency or feature is never enabled on any platforms.
    Never,
    /// This dependency or feature is always enabled on all platforms.
    Always,
    /// The status is platform-dependent.
    PlatformDependent {
        /// An evaluator to run queries against.
        eval: PlatformEval<'g>,
    },
}

assert_covariant!(PlatformStatus);

impl<'g> PlatformStatus<'g> {
    pub(crate) fn new(specs: &'g PlatformStatusImpl) -> Self {
        match specs {
            PlatformStatusImpl::Always => PlatformStatus::Always,
            PlatformStatusImpl::Specs(specs) => {
                if specs.is_empty() {
                    PlatformStatus::Never
                } else {
                    PlatformStatus::PlatformDependent {
                        eval: PlatformEval { specs },
                    }
                }
            }
        }
    }

    /// Returns true if this dependency is always enabled on all platforms.
    pub fn is_always(&self) -> bool {
        match self {
            PlatformStatus::Always => true,
            PlatformStatus::PlatformDependent { .. } | PlatformStatus::Never => false,
        }
    }

    /// Returns true if this dependency is never enabled on any platform.
    pub fn is_never(&self) -> bool {
        match self {
            PlatformStatus::Never => true,
            PlatformStatus::PlatformDependent { .. } | PlatformStatus::Always => false,
        }
    }

    /// Returns true if this dependency is possibly enabled on any platform.
    pub fn is_present(&self) -> bool {
        !self.is_never()
    }

    /// Evaluates whether this dependency is enabled on the given platform spec.
    ///
    /// Returns `Unknown` if the result was unknown, which may happen if evaluating against an
    /// individual platform and its target features are unknown.
    pub fn enabled_on(&self, platform_spec: &PlatformSpec) -> EnabledTernary {
        match (self, platform_spec) {
            (PlatformStatus::Always, _) => EnabledTernary::Enabled,
            (PlatformStatus::Never, _) => EnabledTernary::Disabled,
            (PlatformStatus::PlatformDependent { .. }, PlatformSpec::Any) => {
                EnabledTernary::Enabled
            }
            (PlatformStatus::PlatformDependent { eval }, PlatformSpec::Platform(platform)) => {
                eval.eval(platform)
            }
            (PlatformStatus::PlatformDependent { .. }, PlatformSpec::Always) => {
                EnabledTernary::Disabled
            }
        }
    }
}

/// Whether a dependency or feature is enabled on a specific platform.
///
/// This is a ternary or [three-valued logic](https://en.wikipedia.org/wiki/Three-valued_logic)
/// because the result may be unknown in some situations.
///
/// Returned by the methods on `EnabledStatus`, `PlatformStatus`, and `PlatformEval`.
#[derive(Copy, Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum EnabledTernary {
    /// The dependency is disabled on this platform.
    Disabled,
    /// The status of this dependency is unknown on this platform.
    ///
    /// This may happen if evaluation involves unknown target features. Notably,
    /// this will not be returned for [`Platform::build_target()`], since the
    /// target features for the build target platform are determined at compile
    /// time.
    Unknown,
    /// The dependency is enabled on this platform.
    Enabled,
}

impl EnabledTernary {
    fn new(x: Option<bool>) -> Self {
        match x {
            Some(false) => EnabledTernary::Disabled,
            None => EnabledTernary::Unknown,
            Some(true) => EnabledTernary::Enabled,
        }
    }

    /// Returns true if the status is known (either enabled or disabled).
    pub fn is_known(self) -> bool {
        match self {
            EnabledTernary::Disabled | EnabledTernary::Enabled => true,
            EnabledTernary::Unknown => false,
        }
    }
}

/// AND operation in Kleene K3 logic.
impl BitAnd for EnabledTernary {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        use EnabledTernary::*;

        match (self, rhs) {
            (Enabled, Enabled) => Enabled,
            (Disabled, _) | (_, Disabled) => Disabled,
            _ => Unknown,
        }
    }
}

/// OR operation in Kleene K3 logic.
impl BitOr for EnabledTernary {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self {
        use EnabledTernary::*;

        match (self, rhs) {
            (Disabled, Disabled) => Disabled,
            (Enabled, _) | (_, Enabled) => Enabled,
            _ => Unknown,
        }
    }
}

/// An evaluator for platform-specific dependencies.
///
/// This represents a collection of platform specifications, of the sort `cfg(unix)`.
#[derive(Copy, Clone, Debug)]
pub struct PlatformEval<'g> {
    specs: &'g [TargetSpec],
}

assert_covariant!(PlatformEval);

impl<'g> PlatformEval<'g> {
    /// Runs this evaluator against the given platform.
    pub fn eval(&self, platform: &Platform) -> EnabledTernary {
        let mut res = EnabledTernary::Disabled;
        for spec in self.specs.iter() {
            let matches = spec.eval(platform);
            // Short-circuit evaluation if possible.
            if matches == Some(true) {
                return EnabledTernary::Enabled;
            }
            res = res | EnabledTernary::new(matches);
        }
        res
    }

    /// Returns the [`TargetSpec`] instances backing this evaluator.
    ///
    /// The result of [`PlatformEval::eval`] against a platform is a logical OR
    /// of the results of evaluating the platform against each target spec.
    pub fn target_specs(&self) -> &'g [TargetSpec] {
        self.specs
    }
}

#[derive(Clone, Debug)]
pub(crate) enum PlatformStatusImpl {
    Always,
    // Empty vector means never.
    Specs(Vec<TargetSpec>),
}

impl PlatformStatusImpl {
    /// Returns true if this is an empty predicate (i.e. will never match).
    pub(crate) fn is_never(&self) -> bool {
        match self {
            PlatformStatusImpl::Always => false,
            PlatformStatusImpl::Specs(specs) => specs.is_empty(),
        }
    }

    pub(crate) fn extend(&mut self, other: &PlatformStatusImpl) {
        // &mut *self is a reborrow to allow *self to work below.
        match (&mut *self, other) {
            (PlatformStatusImpl::Always, _) => {
                // Always stays the same since it means all specs are included.
            }
            (PlatformStatusImpl::Specs(_), PlatformStatusImpl::Always) => {
                // Mark self as Always.
                *self = PlatformStatusImpl::Always;
            }
            (PlatformStatusImpl::Specs(specs), PlatformStatusImpl::Specs(other)) => {
                specs.extend_from_slice(other.as_slice());
            }
        }
    }

    pub(crate) fn add_spec(&mut self, spec: Option<&TargetSpec>) {
        // &mut *self is a reborrow to allow *self to work below.
        match (&mut *self, spec) {
            (PlatformStatusImpl::Always, _) => {
                // Always stays the same since it means all specs are included.
            }
            (PlatformStatusImpl::Specs(_), None) => {
                // Mark self as Always.
                *self = PlatformStatusImpl::Always;
            }
            (PlatformStatusImpl::Specs(specs), Some(spec)) => {
                specs.push(spec.clone());
            }
        }
    }
}

impl Default for PlatformStatusImpl {
    fn default() -> Self {
        // Empty vector means never.
        PlatformStatusImpl::Specs(vec![])
    }
}
