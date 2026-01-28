// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

#[cfg(feature = "proptest1")]
#[macro_use]
mod proptest_helpers;

#[cfg(not(feature = "proptest1"))]
macro_rules! proptest_suite {
    ($name: ident) => {
        // Empty macro to skip proptests if the proptest feature is disabled.
    };
}

mod cargo_set_tests;
mod feature_helpers;
mod graph_tests;
mod invalid_tests;
mod weak_namespaced;
