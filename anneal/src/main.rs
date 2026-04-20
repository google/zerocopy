mod aeneas;
mod charon;
mod diagnostics;
mod errors;
mod generate;
mod parse;
mod resolve;
mod scanner;
mod validate;

mod setup;
mod ui_test_shim;
mod util;

use clap::Parser;

/// Anneal: A Literate Verification Toolchain
#[derive(Parser, Debug)]
#[command(name = "cargo-anneal", version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(clap::Subcommand, Debug)]
enum Commands {
    /// Verify a crate
    Verify(resolve::Args),
    /// Setup Anneal dependencies
    Setup(resolve::SetupArgs),
    /// Expand a crate's Lean output
    Expand(ExpandArgs),
    /// Generate Lean workspace and print paths without building
    Generate(resolve::Args),
    #[command(hide = true)]
    ToolchainPath,
}

#[derive(clap::ValueEnum, Clone, Debug, Default, PartialEq)]
pub enum EmitFormat {
    #[default]
    All,
    Anneal,
    Aeneas,
}

#[derive(Parser, Debug)]
pub struct ExpandArgs {
    #[command(flatten)]
    pub resolve_args: resolve::Args,

    /// Which tool's generated Lean code to output
    #[arg(long, default_value_t, value_enum)]
    pub emit: EmitFormat,
}

fn main() -> anyhow::Result<()> {
    // Suppressing timestamps removes a source of nondeterminism that is
    // difficult to work around in integration tests.
    env_logger::builder().format_timestamp(None).init();

    if std::env::var("ANNEAL_UI_TEST_MODE").is_ok() {
        ui_test_shim::run();
        return Ok(());
    }

    let mut args_iter = std::env::args_os().peekable();
    let bin_name = args_iter.next().unwrap_or_else(|| "cargo-anneal".into());
    // If we're being run as a cargo plugin, the second argument will be "anneal".
    if args_iter.peek().is_some_and(|arg| arg == "anneal") {
        args_iter.next();
    }
    let args = Cli::parse_from(std::iter::once(bin_name).chain(args_iter));

    match args.command {
        Commands::Verify(resolve_args) => {
            prepare_and_run(&resolve_args, |locked_roots, packages| {
                aeneas::verify_lean_workspace(locked_roots, packages)
            })?;
        }
        Commands::Generate(resolve_args) => {
            prepare_and_run(&resolve_args, |locked_roots, packages| {
                aeneas::generate_lean_workspace(locked_roots, packages)?;
                let lean_root = locked_roots.lean_root();
                let toolchain = setup::Toolchain::resolve()?;
                println!("Lean workspace generated at: {}", lean_root.display());
                println!();
                println!("To manually build and experiment:");
                println!("  1. cd {}", lean_root.display());
                println!("  2. LAKE_CACHE_DIR={} lake build", toolchain.cache_dir().display());
                Ok(())
            })?;
        }
        Commands::Setup(resolve::SetupArgs {}) => {
            setup::run_setup()?;
        }
        Commands::ToolchainPath => {
            let toolchain = setup::Toolchain::resolve()?;
            println!("{}", toolchain.root.display());
        }
        Commands::Expand(expand_args) => {
            prepare_and_run(&expand_args.resolve_args, |locked_roots, packages| {
                let lean_generated_root = locked_roots.lean_generated_root();

                for artifact in packages {
                    if artifact.start_from.is_empty() {
                        continue;
                    }

                    let slug = artifact.artifact_slug();
                    let output_dir = lean_generated_root.join(&slug);

                    let emit_all = expand_args.emit == EmitFormat::All;
                    let emit_anneal = emit_all || expand_args.emit == EmitFormat::Anneal;
                    let emit_aeneas = emit_all || expand_args.emit == EmitFormat::Aeneas;

                    println!("=== Lean expansion for: {} ===", artifact.name.target_name);

                    if emit_aeneas {
                        println!("--- Aeneas ---");
                        // Read Aeneas outputs from disk
                        let types_path = output_dir.join("Types.lean");
                        let types_ext_path = output_dir.join("TypesExternal.lean");
                        let funs_path = output_dir.join("Funs.lean");
                        let funs_ext_path = output_dir.join("FunsExternal.lean");

                        if types_path.exists() {
                            println!("{}", std::fs::read_to_string(&types_path)?);
                        }
                        if types_ext_path.exists() {
                            println!("{}", std::fs::read_to_string(&types_ext_path)?);
                        }
                        if funs_path.exists() {
                            println!("{}", std::fs::read_to_string(&funs_path)?);
                        }
                        if funs_ext_path.exists() {
                            println!("{}", std::fs::read_to_string(&funs_ext_path)?);
                        }
                    }

                    if emit_anneal {
                        println!("--- Anneal ---");
                        let generated = generate::generate_artifact(artifact);
                        println!("{}", generated.code);
                    }
                }

                Ok(())
            })?;
        }
    }

    Ok(())
}

fn prepare_and_run<F, R>(resolve_args: &resolve::Args, f: F) -> anyhow::Result<Option<R>>
where
    F: FnOnce(&resolve::LockedRoots, &[scanner::AnnealArtifact]) -> anyhow::Result<R>,
{
    let roots = resolve::resolve_roots(resolve_args)?;

    let packages = scanner::scan_workspace(&roots)?;
    if packages.is_empty() {
        log::warn!(
            "No Anneal annotations (/// ```lean ...) found in the selected targets. Nothing to verify."
        );
        return Ok(None);
    }

    let locked_roots = roots.lock_run_root()?;
    validate::validate_artifacts(
        &packages,
        resolve_args.allow_sorry,
        resolve_args.unsound_allow_is_valid,
    )?;
    charon::run_charon(resolve_args, &locked_roots, &packages)?;
    aeneas::run_aeneas(&locked_roots, &packages, resolve_args)?;

    Ok(Some(f(&locked_roots, &packages)?))
}
