

/// Anneal: A Literate Verification Toolchain
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
}

#[derive(clap::Args, Debug)]
#[group(multiple = false)]
struct SetupArgs {
    /// Path to the toolchain archive
    #[arg(long)]
    archive: Option<PathBuf>,
    /// Path to the external toolchain directory
    #[arg(long)]
    dir: Option<PathBuf>,
    /// Pull toolchain archive from remote explicitly
    #[arg(long)]
    remote: bool,
}

fn is_development_environment() -> bool {
    std::env::var("__ZEROCOPY_LOCAL_DEV").is_ok()
}

fn main() {
    let mut args_iter = std::env::args_os().peekable();
    let bin_name = args_iter.next().unwrap_or_else(|| "cargo-anneal".into());
    // If we're being run as a cargo plugin, the second argument will be "anneal".
    if args_iter.peek().is_some_and(|arg| arg == "anneal") {
        args_iter.next();
    }
    let args = Cli::parse_from(std::iter::once(bin_name).chain(args_iter));
    if is_development_environment() {

    } else {

    }
    println!("Hello, world!");
}
