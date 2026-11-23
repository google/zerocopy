// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Test-crate binary shim delegating to [`cargo_anneal::cli::main`].
//!
//! Declaring this shim in `cargo-anneal-tests` lets Cargo build `cargo-anneal`
//! with the test crate's active feature set (including `--no-default-features`)
//! and expose `CARGO_BIN_EXE_cargo-anneal-test-bin` without placing test code
//! inside `trusted/cargo-anneal/` or colliding with `trusted/cargo-anneal`'s
//! `cargo-anneal` binary filename.

use std::process::ExitCode;

fn main() -> ExitCode {
    cargo_anneal::cli::main()
}
