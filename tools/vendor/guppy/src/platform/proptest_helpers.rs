// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::platform::{Platform, PlatformSpec, TargetFeatures};
use proptest::prelude::*;

/// # Helpers for property testing
///
/// The methods in this section allow a `PlatformSpec` to be used in property-based testing
/// scenarios.
///
/// Currently, [proptest 1](https://docs.rs/proptest/1) is supported if the `proptest1`
/// feature is enabled.
impl PlatformSpec {
    /// Returns a [`Strategy`] that generates a random `PlatformSpec` instance.
    pub fn strategy(platform: impl Strategy<Value = Platform>) -> impl Strategy<Value = Self> {
        prop_oneof![
            1 => Just(PlatformSpec::Any),
            1 => Just(PlatformSpec::Always),
            2 => platform.prop_map(PlatformSpec::from),
        ]
    }
}

impl Arbitrary for PlatformSpec {
    type Parameters = ();
    type Strategy = BoxedStrategy<Self>;

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        Self::strategy(Platform::strategy(any::<TargetFeatures>())).boxed()
    }
}
