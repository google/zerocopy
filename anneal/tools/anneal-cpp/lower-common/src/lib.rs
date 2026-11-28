// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Language-agnostic helpers for Anneal frontends that render captured
//! programs as Lean subject terms (`anneal-lower-cpp` today).
//!
//! - [`scc`]: canonical callee-first strongly-connected-component ordering of
//!   a call graph, independent of input order.
//! - [`chunk`]: balanced `_root_.List.append` trees and hoisted chunk
//!   definitions, so that a body with thousands of locals, blocks, or
//!   statements never puts a long list literal in one Lean definition.
//! - [`digest`]: dependency-free SHA-256 for publishing a digest next to every
//!   emitted file.
//!
//! The algorithms mirror the Rust capture pipeline (`rustc-capture`'s Tarjan
//! sharding and list chunking) without depending on its IR.

pub mod chunk;
pub mod digest;
pub mod scc;
