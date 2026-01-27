// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Simulations of Cargo behavior.
//!
//! Cargo comes with a set of algorithms to figure out what packages or features are built. This
//! module reimplements those algorithms using `guppy`'s data structures.

pub(super) mod build;
mod cargo_api;

pub use cargo_api::*;
