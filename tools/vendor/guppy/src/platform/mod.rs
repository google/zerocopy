// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Support for dependencies that are only enabled on some platforms.
//!
//! Most of the time, dependencies are enabled across all platforms. For example, in this
//! `Cargo.toml`:
//!
//! ```toml
//! # once_cell 1.5 is enabled on all platforms.
//! [dependencies]
//! once_cell = "1.5"
//! ```
//!
//! However, in some cases, dependencies may only be enabled on certain platforms.
//!
//! ```toml
//! # This dependency is only enabled on Linux x86_64.
//! [target.x86_64-unknown-linux-gnu.dependencies]
//! inotify = "0.9.4"
//!
//! # This build dependency is enabled on Windows.
//! [target.'cfg(windows)'.build-dependencies]
//! winapi = "0.3.9"
//! ```
//!
//! This module provides types that can represent platforms and evaluate expressions.
//!
//! # Representing platforms
//!
//! * [`Platform`] represents a single platform.
//! * [`Triple`] is a [Rust target triple](https://doc.rust-lang.org/stable/rustc/platform-support.html).
//! * [`PlatformSpec`] represents a single platform or a range of platforms, including any platform
//!   (the union of all possible platforms) and all platforms (the intersection of all possible
//!   platforms).
//!
//! # Evaluating platforms
//!
//! These structs are defined in the context of a [`PackageGraph`](crate::graph::PackageGraph), and
//! are typically returned through [`PackageLink`](crate::graph::PackageLink) instances.
//!
//! * [`PlatformStatus`]: The status of a dependency or a feature which might be platform-dependent.
//! * [`PlatformEval`]: A collection of platform specifications like `cfg(unix)`, to evaluate
//!   against a platform.
//! * [`EnabledTernary`]: A three-valued logic representing the status of a dependency or feature
//!   on a given platform. Includes an additional status to represent situations like unknown
//!   [target features](https://rust-lang.github.io/rfcs/2045-target-feature.html).
//!
//! If the `summaries` feature is enabled, this module also supports reading and writing serializable
//! summaries of platforms. These can be used both as configuration, and to serialize the results of a
//! particular `guppy` evaluation.
//!
//! For more, about platform-specific dependencies, see [Platform specific
//! dependencies](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html#platform-specific-dependencies)
//! in the Cargo reference.

mod platform_eval;
mod platform_spec;
#[cfg(feature = "proptest1")]
mod proptest_helpers;
#[cfg(feature = "summaries")]
mod summaries;

pub use platform_eval::*;
pub use platform_spec::*;
#[cfg(feature = "summaries")]
pub use summaries::*;
// These are inlined -- generally, treat target_spec as a private dependency so expose these types
// as part of guppy's API.
pub use target_spec::{Platform, TargetFeatures, Triple};
