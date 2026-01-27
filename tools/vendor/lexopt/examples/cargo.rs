//! A very partial unfaithful implementation of cargo's command line.
//!
//! This showcases some hairier patterns, like subcommands and custom value parsing.

use std::{path::PathBuf, str::FromStr};

const HELP: &str = "cargo [+toolchain] [OPTIONS] [SUBCOMMAND]";

fn main() -> Result<(), lexopt::Error> {
    use lexopt::prelude::*;

    let mut settings = GlobalSettings {
        toolchain: "stable".to_owned(),
        color: Color::Auto,
        offline: false,
        quiet: false,
        verbose: false,
    };

    let mut parser = lexopt::Parser::from_env();
    while let Some(arg) = parser.next()? {
        match arg {
            Long("color") => {
                settings.color = parser.value()?.parse()?;
            }
            Long("offline") => {
                settings.offline = true;
            }
            Long("quiet") => {
                settings.quiet = true;
                settings.verbose = false;
            }
            Long("verbose") => {
                settings.verbose = true;
                settings.quiet = false;
            }
            Long("help") => {
                println!("{}", HELP);
                std::process::exit(0);
            }
            Value(value) => {
                let value = value.string()?;
                match value.as_str() {
                    value if value.starts_with('+') => {
                        settings.toolchain = value[1..].to_owned();
                    }
                    "install" => {
                        return install(settings, parser);
                    }
                    value => {
                        return Err(format!("unknown subcommand '{}'", value).into());
                    }
                }
            }
            _ => return Err(arg.unexpected()),
        }
    }

    println!("{}", HELP);
    Ok(())
}

#[derive(Debug)]
struct GlobalSettings {
    toolchain: String,
    color: Color,
    offline: bool,
    quiet: bool,
    verbose: bool,
}

fn install(settings: GlobalSettings, mut parser: lexopt::Parser) -> Result<(), lexopt::Error> {
    use lexopt::prelude::*;

    let mut package: Option<String> = None;
    let mut root: Option<PathBuf> = None;
    let mut jobs: u16 = get_no_of_cpus();

    while let Some(arg) = parser.next()? {
        match arg {
            Value(value) if package.is_none() => {
                package = Some(value.string()?);
            }
            Long("root") => {
                root = Some(parser.value()?.into());
            }
            Short('j') | Long("jobs") => {
                jobs = parser.value()?.parse()?;
            }
            Long("help") => {
                println!("cargo install [OPTIONS] CRATE");
                std::process::exit(0);
            }
            _ => return Err(arg.unexpected()),
        }
    }

    println!("Settings: {:#?}", settings);
    println!(
        "Installing {} into {:?} with {} jobs",
        package.ok_or("missing CRATE argument")?,
        root,
        jobs
    );

    Ok(())
}

#[derive(Debug)]
enum Color {
    Auto,
    Always,
    Never,
}

// clap has a macro for this: https://docs.rs/clap/2.33.3/clap/macro.arg_enum.html
// We have to do it manually.
impl FromStr for Color {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s.to_lowercase().as_str() {
            "auto" => Ok(Color::Auto),
            "always" => Ok(Color::Always),
            "never" => Ok(Color::Never),
            _ => Err(format!(
                "Invalid style '{}' [pick from: auto, always, never]",
                s
            )),
        }
    }
}

fn get_no_of_cpus() -> u16 {
    4
}
