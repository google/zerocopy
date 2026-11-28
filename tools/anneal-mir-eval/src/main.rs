// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Standalone CLI over `anneal-mir-eval` for inspecting captured MIR JSON
//! manifests (schema v5), stepping concrete inputs under Profile v1 or v2, and
//! probing for pre-proof UB counterexamples with replay classification.

#![forbid(unsafe_code)]

#[path = "main/args.rs"]
mod args;
#[path = "main/capture.rs"]
mod capture;
#[path = "main/commands.rs"]
mod commands;
#[path = "main/format.rs"]
mod format;

use std::{env, process::ExitCode};

use self::commands::{cmd_eval, cmd_list, cmd_probe};

fn usage() -> &'static str {
    "Usage:
  anneal-mir-eval list <capture.json> [--json]
  anneal-mir-eval eval <capture.json> [--body <idx|identity>]
                       [--arg <val>... | --query <query.json>]
                       [--fuel <n>] [--endian big|little]
                       [--strict-v1 | --profile-v2] [--trace] [--json]
  anneal-mir-eval probe <capture.json> [--body <idx|identity> | --all]
                        [--cases <n>] [--fuel <n>] [--seed <n>]
                        [--endian big|little] [--strict-v1 | --profile-v2]
                        [--include-unsafe] [--json]"
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ProfileOverride {
    Auto,
    StrictV1,
    ProfileV2,
}

fn main() -> ExitCode {
    let args: Vec<String> = env::args().skip(1).collect();
    if args.is_empty() || matches!(args[0].as_str(), "-h" | "--help" | "help") {
        println!("{}", usage());
        return ExitCode::SUCCESS;
    }
    let res = match args[0].as_str() {
        "list" => cmd_list(&args[1..]),
        "eval" => cmd_eval(&args[1..]),
        "probe" => cmd_probe(&args[1..]),
        other => Err(format!("unknown subcommand '{other}'\n\n{}", usage())),
    };
    match res {
        Ok(code) => code,
        Err(msg) => {
            eprintln!("error: {msg}");
            ExitCode::FAILURE
        }
    }
}
