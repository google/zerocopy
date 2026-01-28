// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

mod custom;
mod expr;
mod helpers;

datatest_stable::harness! {
    { test = custom::custom_invalid, root = &target_spec_miette::fixtures::CUSTOM_INVALID, pattern = r"^.*/*" },
    { test = expr::expr_invalid, root = &target_spec_miette::fixtures::EXPR_INVALID, pattern = r"^.*/*" },
}
