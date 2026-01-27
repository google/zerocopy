// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Fixtures for target-spec-miette.
//!
//! This module contains test fixtures for the target-spec-miette crate,
//! typically around testing invalid inputs of various kinds.
//!
//! These fixtures can be used in downstream crates to verify that bad inputs
//! are gracefully handled, particularly by showing good error messages. (Good
//! error messages are part of why this library exists in the first place).
//!
//! The target-spec-miette library itself uses them via the
//! [`datatest-stable`](https://docs.rs/datatest-stable) crate.
//!
//! The exact contents of each directory are not part of the semver guarantees,
//! so using this module is only recommended in tests, and with a checked-in
//! `Cargo.lock`. A minor update to target-spec-miette may require that your
//! tests also be updated.

/// A set of invalid custom target JSON specifications.
pub static CUSTOM_INVALID: include_dir::Dir<'static> =
    include_dir::include_dir!("$CARGO_MANIFEST_DIR/tests/fixtures/custom-invalid");

/// A set of invalid `cfg` expressions.
pub static EXPR_INVALID: include_dir::Dir<'static> =
    include_dir::include_dir!("$CARGO_MANIFEST_DIR/tests/fixtures/expr-invalid");
