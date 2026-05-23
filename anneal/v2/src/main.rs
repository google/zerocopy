// Copyright 2026 The Fuchsia Authors
//
// Licensed under the 2-Clause BSD License <LICENSE-BSD or
// https://opensource.org/license/bsd-2-clause>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use anyhow::Context as _;
use clap::Parser as _;

mod charon;
mod diagnostics;
mod resolve;
mod scanner;
mod setup;
mod util;

/// Anneal
#[derive(clap::Parser, Debug)]
#[command(name = "cargo-anneal", version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(clap::Subcommand, Debug)]
enum Commands {
    /// Setup Anneal dependencies
    Setup(SetupArgs),
    /// Expand a crate (runs Charon)
    Expand(ExpandArgs),

    /// Helper to acquire shared or exclusive locks for multi-process integration testing (dev only)
    #[cfg(feature = "exocrate_tests")]
    TestLockHelper {
        /// The role to run as: 'reader-a', 'reader-b', 'writer-a', or 'reader-exclusion'
        #[arg(long)]
        role: String,
        /// Path to the directory to lock
        #[arg(long)]
        lock_dir: std::path::PathBuf,
        /// Path to the shared log file where lock transitions are appended
        #[arg(long)]
        log_file: std::path::PathBuf,
        /// Path to the temporary synchronization signal file
        #[arg(long)]
        sig_file: std::path::PathBuf,
    },
}

#[derive(clap::Parser, Debug)]
pub struct SetupArgs {
    /// Path to a local dependency archive to use instead of downloading
    #[arg(long, value_name = "path-to-local-archive")]
    pub local_archive: Option<std::path::PathBuf>,
}

#[derive(clap::Parser, Debug)]
pub struct ExpandArgs {
    #[command(flatten)]
    pub resolve_args: crate::resolve::Args,

    /// Controls where LLBC output is placed on the filesystem
    #[arg(long, value_name = "output-dir")]
    pub output_dir: Option<std::path::PathBuf>,

    /// Do not show compilation progress bars
    #[arg(long)]
    pub no_progress: bool,
}

fn setup(args: SetupArgs) -> anyhow::Result<()> {
    crate::setup::run_setup(crate::setup::SetupArgs { local_archive: args.local_archive })
        .context("Failed to setup toolchain")
}

fn expand(args: ExpandArgs) -> anyhow::Result<()> {
    let roots = crate::resolve::resolve_roots(&args.resolve_args)?;
    let packages = crate::scanner::scan_workspace(&roots)?;
    if packages.is_empty() {
        log::warn!("No targets found to expand.");
        return Ok(());
    }
    let mut locked_roots = roots.lock_run_root()?;
    if let Some(output_dir) = args.output_dir {
        locked_roots.llbc_override = Some(output_dir);
    }
    let toolchain = crate::setup::Toolchain::resolve()?;
    let show_progress = !args.no_progress;
    crate::charon::run_charon(
        &args.resolve_args,
        &toolchain,
        &locked_roots,
        &packages,
        show_progress,
    )?;
    Ok(())
}

fn main() -> anyhow::Result<()> {
    // Suppressing timestamps removes a source of nondeterminism that is
    // difficult to work around in integration tests.
    env_logger::builder().format_timestamp(None).init();

    let mut args_iter = std::env::args_os().peekable();
    let bin_name = args_iter.next().unwrap_or_else(|| "cargo-anneal".into());
    // If we're being run as a cargo plugin, the second argument will be "anneal".
    if args_iter.peek().is_some_and(|arg| arg == "anneal") {
        args_iter.next();
    }
    let args = Cli::parse_from(std::iter::once(bin_name).chain(args_iter));

    match args.command {
        Commands::Setup(args) => setup(args),
        Commands::Expand(args) => expand(args),

        #[cfg(feature = "exocrate_tests")]
        Commands::TestLockHelper { role, lock_dir, log_file, sig_file } => {
            crate::util::run_test_lock_helper(&role, &lock_dir, &log_file, &sig_file)
        }
    }
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "exocrate_tests")]
    #[test]
    fn test_setup_and_toolchain_paths() {
        // 1. Run setup.
        super::setup(super::SetupArgs {
            // ASSUMPTION: Dependency builder installs archive at
            // `target/anneal-exocrate.tar.zst`.
            local_archive: Some("target/anneal-exocrate.tar.zst".into()),
        })
        .expect("Failed to run setup");

        // 2. Once setup completes successfully, resolve the toolchain.
        let toolchain = crate::setup::Toolchain::resolve().expect("Failed to resolve toolchain");

        // 3. Verify that all returned paths exist as directories.
        // Note: these assertions would be more appropriate in the setup.rs module,
        // but including them here avoids introducing multiple tests that attempt to
        // extract the (large) anneal exocrate archive.
        assert!(toolchain.root().is_dir(), "root is not a directory: {:?}", toolchain.root());
        assert!(
            toolchain.aeneas_bin_dir().is_dir(),
            "aeneas_bin_dir is not a directory: {:?}",
            toolchain.aeneas_bin_dir()
        );
        assert!(
            toolchain.rust_sysroot().is_dir(),
            "rust_sysroot is not a directory: {:?}",
            toolchain.rust_sysroot()
        );
        assert!(
            toolchain.rust_bin().is_dir(),
            "rust_bin is not a directory: {:?}",
            toolchain.rust_bin()
        );
        assert!(
            toolchain.rust_lib().is_dir(),
            "rust_lib is not a directory: {:?}",
            toolchain.rust_lib()
        );
    }
}
