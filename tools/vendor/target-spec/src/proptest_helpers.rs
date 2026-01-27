// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{Platform, TargetFeatures};
use cfg_expr::targets::ALL_BUILTINS;
use proptest::{collection::btree_set, prelude::*, sample::select};
use std::borrow::Cow;

/// ## Helpers for property testing
///
/// The methods in this section allow `Platform` instances to be used in property-based testing
/// scenarios.
///
/// Currently, [proptest 1](https://docs.rs/proptest/1) is supported if the `proptest1`
/// feature is enabled.
impl Platform {
    /// Given a way to generate `TargetFeatures` instances, this returns a `Strategy` that generates
    /// a platform at random.
    ///
    /// Requires the `proptest1` feature to be enabled.
    ///
    /// ## Examples
    ///
    /// ```
    /// use proptest::prelude::*;
    /// use target_spec::{Platform, TargetFeatures};
    ///
    /// // target_features is a strategy that always produces TargetFeatures::Unknown.
    /// let target_features = Just(TargetFeatures::Unknown);
    /// let strategy = Platform::strategy(target_features);
    /// ```
    pub fn strategy(
        target_features: impl Strategy<Value = TargetFeatures>,
    ) -> impl Strategy<Value = Platform> {
        let flags = btree_set(flag_strategy(), 0..3);
        (0..ALL_BUILTINS.len(), target_features, flags).prop_map(|(idx, target_features, flags)| {
            let mut platform = Platform::new(
                ALL_BUILTINS[idx].triple.as_str().to_owned(),
                target_features,
            )
            .expect("known triple");
            platform.add_flags(flags);
            platform
        })
    }

    /// A version of `strategy` that allows target triples to be filtered.
    ///
    /// Requires the `proptest1` feature to be enabled.
    pub fn filtered_strategy(
        triple_filter: impl Fn(&'static str) -> bool,
        target_features: impl Strategy<Value = TargetFeatures>,
    ) -> impl Strategy<Value = Platform> {
        let filtered: Vec<_> = ALL_BUILTINS
            .iter()
            .filter(|target_info| triple_filter(target_info.triple.as_str()))
            .collect();
        let flags = btree_set(flag_strategy(), 0..3);
        (0..filtered.len(), target_features, flags).prop_map(
            move |(idx, target_features, flags)| {
                let mut platform = Platform::new(filtered[idx].triple.as_str(), target_features)
                    .expect("known triple");
                platform.add_flags(flags);
                platform
            },
        )
    }
}

/// Picks a random flag from a list of known flags.
pub fn flag_strategy() -> impl Strategy<Value = &'static str> {
    static KNOWN_FLAGS: &[&str] = &["cargo_web", "test-flag", "abc", "foo", "bar", "flag-test"];
    select(KNOWN_FLAGS)
}

/// The `Arbitrary` implementation for `TargetFeatures` uses a predefined list of features.
impl Arbitrary for TargetFeatures {
    type Parameters = ();
    type Strategy = BoxedStrategy<Self>;

    fn arbitrary_with(_args: Self::Parameters) -> Self::Strategy {
        // https://doc.rust-lang.org/reference/attributes/codegen.html#available-features
        static KNOWN_FEATURES: &[&str] = &[
            "aes", "avx", "avx2", "bmi1", "bmi2", "fma", "rdrand", "sha", "sse", "sse2", "sse3",
            "sse4.1", "sse4.2", "ssse3", "xsave", "xsavec", "xsaveopt", "xsaves",
        ];
        let known_features_strategy = select(KNOWN_FEATURES).prop_map(Cow::Borrowed);
        prop_oneof![
            Just(TargetFeatures::Unknown),
            Just(TargetFeatures::All),
            btree_set(known_features_strategy, 0..8).prop_map(TargetFeatures::Features),
        ]
        .boxed()
    }
}
