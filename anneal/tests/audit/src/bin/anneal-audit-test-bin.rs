// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Test-crate binary shim delegating to [`anneal_audit::cli::main`].
//!
//! Declaring this shim in `anneal-audit-tests` lets Cargo build the CLI on
//! demand and expose `CARGO_BIN_EXE_anneal-audit-test-bin` during integration
//! tests without placing test code inside `trusted/audit/` or colliding with
//! `trusted/audit`'s `anneal-audit` binary filename.

use std::process::ExitCode;

fn main() -> ExitCode {
    anneal_audit::cli::main()
}
