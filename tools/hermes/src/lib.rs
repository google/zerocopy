// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Hermes: A Literate Verification Orchestrator for Rust.
//!
//! Hermes facilitates the verification of Rust crates by integrating with
//! [Charon](https://github.com/AeneasVerif/charon) and [Aeneas](https://github.com/AeneasVerif/aeneas).
//!
//! It provides a seamless pipeline that:
//! 1.  **Scaffolds** a "Shadow Crate" to sanitize Rust code for verification (removing unsafe, mocking models).
//! 2.  **Extracts** the crate to LLBC (Low-Level Borrow Calculus) using Charon.
//! 3.  **Translates** LLBC to Lean 4 models using Aeneas.
//! 4.  **Stitches** user-provided proofs (written in Rust doc comments) into the generated Lean project.
//! 5.  **Verifies** the final result using Lean's build system (`lake`).
//!
//! This library exposes the core modules used by the `cargo-hermes` binary.

/// Handles the "desugaring" of high-level Hermes specifications (e.g., `///@ ensure ...`)
/// into valid Lean code.
pub mod desugar;

/// Helper utilities for parsing Rust documentation attributes and extracting Hermes directives.
pub mod docs;

/// Wrappers around external tools (Charon, Aeneas, Lake) to handle their invocation.
pub mod orchestration;

/// logic for parsing Rust source files to extract functions, structs, and their attached
/// Hermes annotations (`///@ ...`).
pub mod parser;

/// The core pipeline definition, orchestrating the end-to-end verification flow.
pub mod pipeline;

/// logic for creating and sanitizing the "Shadow Crate", which is the version of the crate
/// actually seen by the verification tools.
pub mod shadow;

/// Utilities for translating Rust types and signatures into their Lean equivalents during stitching.
pub mod translator;
