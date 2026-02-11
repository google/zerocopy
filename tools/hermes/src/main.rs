mod charon;
mod errors;
mod parse;
mod resolve;
mod shadow;
mod transform;
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
            let entry_points = shadow::build_shadow_crate(&roots)?;
            if entry_points.is_empty() {
                anyhow::bail!("No Hermes annotations (/// ```lean ...) found in the selected targets. Nothing to verify.");
            }
            charon::run_charon(&resolve_args, &roots, &entry_points)
        }
    }
}

/// A no-op function with a Hermes annotation so we can test Hermes on itself.
///
/// ```lean
/// ```
fn _foo() {}
