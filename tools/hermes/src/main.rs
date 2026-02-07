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
    if std::env::var("HERMES_UI_TEST_MODE").is_ok() {
        ui_test_shim::run();
        return Ok(());
    }

    let args = Cli::parse();
    match args.command {
        Commands::Verify(resolve_args) => {
            let roots = resolve::resolve_roots(&resolve_args)?;
            shadow::build_shadow_crate(&roots)
        }
    }
}
