// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Hermes: A verification orchestrator for Rust.
//!
//! This library provides the core logic for the `cargo-hermes` CLI tool, including:
//! - Parsing Rust code for verification annotations.
//! - Orchestrating the execution of Charon and Aeneas.
//! - Stitching generated Lean code with user-provided proofs.

pub mod desugar;
pub mod orchestration;
pub mod parser;
pub mod pipeline;
pub mod translator;
