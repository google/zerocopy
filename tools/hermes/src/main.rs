mod errors;
mod parse;
mod resolve;
mod shadow;
mod transform;
mod ui_test_shim;

use std::{env, process::exit};

use clap::Parser;

/// Hermes: A Literate Verification Toolchain
#[derive(Parser, Debug)]
#[command(name = "hermes", version, about, long_about = None)]
struct Cli {
    #[command(flatten)]
    resolve: resolve::Args,
}

fn main() -> anyhow::Result<()> {
    if env::var("HERMES_UI_TEST_MODE").is_ok() {
        ui_test_shim::run();
        return Ok(());
    }

    let args = Cli::parse();
    let roots = resolve::resolve_roots(&args.resolve)?;
    shadow::build_shadow_crate(&roots)
}
