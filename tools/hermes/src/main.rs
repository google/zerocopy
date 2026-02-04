// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use std::path::PathBuf;

use anyhow::Result;
use cargo_hermes::pipeline::{Sorry, run_pipeline};
use clap::{Parser, Subcommand};

/// The primary CLI entry point for `cargo-hermes`.
///
/// This enum defines the command-line interface, which is invoked as `cargo hermes ...`.
/// The `bin_name = "cargo"` attribute ensures that it parses correctly when called via Cargo.
#[derive(Parser, Debug)]
#[command(name = "cargo-hermes")]
#[command(bin_name = "cargo")]
pub enum CargoCli {
    Hermes(HermesArgs),
}

#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
pub struct HermesArgs {
    #[command(subcommand)]
    pub command: Commands,
}

#[derive(Subcommand, Debug)]
pub enum Commands {
    Verify {
        /// The name of the crate to verify.
        ///
        /// If not provided, it is inferred from `Cargo.toml`.
        #[arg(long)]
        crate_name: Option<String>,

        /// Destination directory where generated artifacts (Lean code, LLBC) will be output.
        ///
        /// Defaults to `verification`.
        #[arg(long, default_value = "verification")]
        dest: PathBuf,

        /// Path to the local Aeneas repository (specifically `backends/lean`).
        ///
        /// If not provided, Hermes will attempt to fetch Aeneas from git (in `lakefile.lean`).
        #[arg(long)]
        aeneas_path: Option<PathBuf>,

        /// Path to the `Cargo.toml` manifest or a standalone Rust script.
        ///
        /// If pointing to a script (`.rs`), Hermes treats it as a single-file crate.
        #[arg(long)]
        manifest_path: Option<PathBuf>,

        /// If set, instructs Lean to accept `sorry` (missing proofs) without failing verification.
        ///
        /// This is useful for incremental development.
        #[arg(long)]
        allow_sorry: bool,
    },
}

fn main() -> Result<()> {
    env_logger::init();
    let CargoCli::Hermes(args) = CargoCli::parse();
    let Commands::Verify { crate_name, dest, aeneas_path, manifest_path, allow_sorry } =
        args.command;

    let crate_root = std::env::current_dir()?;
    std::fs::create_dir_all(&dest)?;
    let dest = dest.canonicalize()?;
    let sorry_mode = if allow_sorry { Sorry::AllowSorry } else { Sorry::RejectSorry };
    run_pipeline(crate_name, &crate_root, &dest, aeneas_path, manifest_path, sorry_mode)
}
