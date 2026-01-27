#[cfg(feature = "js")]
fn main() {}

#[cfg(not(feature = "js"))]
fn main() {
    use action_validator::CliConfig;
    use clap::Parser;
    use std::process;

    let config = CliConfig::parse();

    if matches!(
        action_validator::cli::run(&config),
        action_validator::cli::RunResult::Failure
    ) {
        process::exit(1);
    }
}
