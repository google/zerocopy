// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! CLI entrypoint for `anneal-rustc-capture`.

use std::env;
use std::process::ExitCode;

fn main() -> ExitCode {
    for arg in env::args().skip(1) {
        match arg.as_str() {
            "--help" | "-h" => {
                println!("Usage: anneal-rustc-capture [--version] <crate-dir>");
                return ExitCode::SUCCESS;
            }
            "--version" | "-V" => {
                println!("anneal-rustc-capture {}", env!("CARGO_PKG_VERSION"));
                return ExitCode::SUCCESS;
            }
            _ => {}
        }
    }
    eprintln!("anneal-rustc-capture: MIR capture not yet implemented");
    ExitCode::from(1)
}
