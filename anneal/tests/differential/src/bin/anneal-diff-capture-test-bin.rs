// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Test-crate binary shim delegating to [`anneal_rustc_capture::cli_main`].
//!
//! Declaring this shim in `anneal-differential-tests` lets Cargo build the
//! capture driver cleanly and expose
//! `CARGO_BIN_EXE_anneal-diff-capture-test-bin` without scanning `target/` or
//! spawning nested `cargo build` invocations.

#![feature(rustc_private)]

extern crate rustc_driver;

use std::process::ExitCode;

fn main() -> ExitCode {
    anneal_rustc_capture::cli_main()
}
