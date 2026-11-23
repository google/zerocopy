// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Test-crate binary shim delegating to [`anneal_rustc_capture::cli_main`].
//!
//! Declaring this shim in `anneal-rustc-capture-tests` lets Cargo build the
//! capture driver on demand and expose
//! `CARGO_BIN_EXE_anneal-rustc-capture-test-bin` without placing test code
//! inside `trusted/rustc-capture/` or colliding with `trusted/rustc-capture`'s
//! `anneal-rustc-capture` binary filename.

// Required so rustc dynamically links `std` against `librustc_driver`'s
// `libstd` rather than linking a duplicate static copy of `std`.
#![feature(rustc_private)]

extern crate rustc_driver;

use std::process::ExitCode;

fn main() -> ExitCode {
    anneal_rustc_capture::cli_main()
}
