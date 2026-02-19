mod aeneas;
mod charon;
mod diagnostics;
mod errors;
mod generate;
mod parse;
mod resolve;
mod scanner;
mod validate;

mod ui_test_shim;

use clap::Parser;

/// Hermes: A Literate Verification Toolchain
#[derive(Parser, Debug)]
#[command(name = "hermes", version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(clap::Subcommand, Debug)]
enum Commands {
    /// Verify a crate
    Verify(resolve::Args),
}

fn main() -> anyhow::Result<()> {
    env_logger::init();

    if std::env::var("HERMES_UI_TEST_MODE").is_ok() {
        ui_test_shim::run();
        return Ok(());
    }

    let args = Cli::parse();
    match args.command {
        Commands::Verify(resolve_args) => {
            let roots = resolve::resolve_roots(&resolve_args)?;

            let packages = scanner::scan_workspace(&roots)?;
            if packages.is_empty() {
                log::warn!(
                    "No Hermes annotations (/// ```lean ...) found in the selected targets. Nothing to verify."
                );
                return Ok(());
            }

            let locked_roots = roots.lock_run_root()?;
            validate::validate_artifacts(&packages, resolve_args.allow_sorry)?;
            charon::run_charon(&resolve_args, &locked_roots, &packages)?;
            aeneas::run_aeneas(&locked_roots, &packages, &resolve_args)
        }
    }
}

mod util {
    use std::path::PathBuf;

    use anyhow::{Context, Result};
    use fs2::FileExt;

    /// Represents an active, exclusive lock on a directory.
    ///
    /// This struct guarantees that the process holds an OS-level file lock
    /// guarding the specified directory.
    pub struct DirLock {
        /// The path to the directory being guarded.
        pub path: PathBuf,
        // Kept alive to hold the flock
        _file: std::fs::File,
    }

    impl DirLock {
        /// Acquires an exclusive lock on the specified directory.
        ///
        /// This function blocks until the lock can be acquired. We use a
        /// separate `.lock` file (e.g., `path.lock`) rather than locking the
        /// directory itself to avoid platform-specific issues with directory
        /// locking and to ensure the lock file persists even if the directory
        /// is cleaned.
        pub fn lock(path: PathBuf) -> Result<Self> {
            let lock_path = path.join(".lock");

            // Ensure the directory exists
            if let Some(parent) = lock_path.parent() {
                std::fs::create_dir_all(parent).with_context(|| {
                    format!("Failed to create directory for lock file: {:?}", parent)
                })?;
            }

            let file = std::fs::File::create(&lock_path)
                .with_context(|| format!("Failed to create lock file at {:?}", lock_path))?;

            // We use an exclusive lock to ensure only one process operates
            // on this directory at a time.
            //
            // FIXME: We might want to print a message if this blocks for a long
            // time.
            file.lock_exclusive()
                .with_context(|| format!("Failed to acquire exclusive lock on {:?}", lock_path))?;

            Ok(Self { path, _file: file })
        }
    }
}

/// A no-op function with a Hermes annotation so we can test Hermes on itself.
///
/// ```lean
/// ```
fn _foo() {}
