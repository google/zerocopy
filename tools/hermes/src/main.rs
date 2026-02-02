// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use std::path::PathBuf;

use anyhow::Result;
use cargo_hermes::pipeline::run_pipeline;
use clap::{Parser, Subcommand};

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
    /// Verify the current crate
    /// Verify a crate or script
    Verify {
        /// Optional crate name
        #[arg(long)]
        crate_name: Option<String>,
        /// Path to generated files directory
        #[arg(long, default_value = "verification")]
        dest: PathBuf,
        /// Path to local Aeneas repository (specifically backends/lean)
        #[arg(long)]
        aeneas_path: Option<PathBuf>,
        /// Path to Cargo.toml or Cargo script
        #[arg(long)]
        manifest_path: Option<PathBuf>,
    },
}

fn main() -> Result<()> {
    let CargoCli::Hermes(args) = CargoCli::parse();
    let Commands::Verify { crate_name, dest, aeneas_path, manifest_path } = args.command;

    let crate_root = std::env::current_dir()?;
    let dest = dest.canonicalize()?;
    run_pipeline(crate_name, &crate_root, &dest, aeneas_path, manifest_path)
}
