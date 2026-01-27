// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Test and helper macros.

/// Assert that a struct with a single lifetime parameter is covariant.
macro_rules! assert_covariant {
    ($i:ident) => {
        const _: () = {
            #[allow(dead_code)]
            fn assert_covariant<'a, 'b: 'a>(x: $i<'b>) -> $i<'a> {
                x
            }
        };
    };
}
