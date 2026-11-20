// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! CLI entrypoint for `cargo-anneal`.

mod setup;

use std::env;
use std::path::PathBuf;
use std::process::ExitCode;

fn print_help() {
    println!(
        "\
cargo-anneal {}

USAGE:
    cargo anneal <SUBCOMMAND>
    cargo-anneal <SUBCOMMAND>

SUBCOMMANDS:
    setup [--local-archive <path>]    Install the pinned Anneal toolchain archive

OPTIONS:
    -h, --help       Print help information
    -V, --version    Print version information",
        env!("CARGO_PKG_VERSION")
    );
}

fn run_setup_cli(args: &[String]) -> ExitCode {
    let mut local_archive: Option<PathBuf> = None;
    let mut iter = args.iter().map(String::as_str);
    while let Some(arg) = iter.next() {
        match arg {
            "--local-archive" => {
                let Some(val) = iter.next() else {
                    eprintln!("error: --local-archive requires a path");
                    return ExitCode::from(2);
                };
                local_archive = Some(PathBuf::from(val));
            }
            "--help" | "-h" => {
                println!(
                    "Usage: cargo anneal setup [--local-archive <path>]"
                );
                return ExitCode::SUCCESS;
            }
            other => {
                eprintln!("error: unknown setup argument `{other}`");
                return ExitCode::from(2);
            }
        }
    }

    match setup::install(local_archive) {
        Ok(root) => {
            println!("Installed Anneal toolchain at {}", root.display());
            ExitCode::SUCCESS
        }
        Err(err) => {
            eprintln!("error: {err}");
            ExitCode::from(1)
        }
    }
}

fn main() -> ExitCode {
    let mut args: Vec<String> = env::args().skip(1).collect();
    if args.first().map(String::as_str) == Some("anneal") {
        args.remove(0);
    }

    match args.first().map(String::as_str) {
        None | Some("--help") | Some("-h") | Some("help") => {
            print_help();
            ExitCode::SUCCESS
        }
        Some("--version") | Some("-V") => {
            println!("cargo-anneal {}", env!("CARGO_PKG_VERSION"));
            ExitCode::SUCCESS
        }
        Some("setup") => run_setup_cli(&args[1..]),
        Some(other) => {
            eprintln!("error: unknown subcommand `{other}`");
            print_help();
            ExitCode::from(2)
        }
    }
}
