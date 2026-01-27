// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Integrate [target-spec](https://crates.io/crates/target-spec) errors with [miette](https://docs.rs/miette).
//!
//! This crate has implementations of `Diagnostic` for the various kinds of errors that target-spec
//! produces. This can be used to pretty-print errors returned by target-spec.
//!
//! ## Features
//!
//! - `fixtures`: Include [a set of fixtures](crate::fixtures) for testing
//!   downstream users against. This feature is disabled by default.
//!
//! ## Minimum supported Rust version
//!
//! The minimum supported Rust version (MSRV) is **Rust 1.86**.
//!
//! While this crate is in pre-release status (0.x), the MSRV may be bumped in
//! patch releases.

#![warn(missing_docs)]
#![forbid(unsafe_code)]
#![cfg_attr(doc_cfg, feature(doc_cfg))]

#[cfg(feature = "fixtures")]
pub mod fixtures;
mod imp;

pub use imp::*;
