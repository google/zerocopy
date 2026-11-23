// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! CLI entrypoint for `cargo-anneal`.

#[cfg(feature = "setup")]
use crate::setup;
use crate::{init, inspect, verify};

/// Package version of `cargo-anneal` for CLI version output and external test
/// assertions.
#[doc(hidden)]
pub const PKG_VERSION: &str = env!("CARGO_PKG_VERSION");

#[cfg(feature = "setup")]
use std::path::PathBuf;
use std::{env, ffi::OsString, process::ExitCode};

use clap::{CommandFactory, Parser, Subcommand, error::ErrorKind};

use crate::output::{ColorChoice, OutputSession, VerifyFormat, finish_with_writers};

#[derive(Parser)]
#[command(
    name = "cargo-anneal",
    bin_name = "cargo anneal",
    version,
    about = "Formally verify Rust programs in Lean 4",
    after_help = "Also accepts direct invocation as cargo-anneal <COMMAND>."
)]
struct Cli {
    /// Control ANSI color output on human-formatted streams.
    #[arg(
        long,
        global = true,
        value_enum,
        default_value_t = ColorChoice::Auto,
        value_name = "WHEN"
    )]
    color: ColorChoice,
    /// Reduce human output to verdicts and mandatory security caveats.
    #[arg(short = 'q', long, global = true, conflicts_with = "verbose")]
    quiet: bool,
    /// Show expanded details (untruncated lists, timing, and phase progress;
    /// `inspect` keeps 12-char digests unless `--full-digests` is passed).
    #[arg(short = 'v', long, global = true, conflicts_with = "quiet")]
    verbose: bool,
    #[command(subcommand)]
    command: Option<Command>,
}

#[derive(Subcommand)]
enum Command {
    /// Install or reuse the versioned Anneal toolchain archive.
    ///
    /// Without `--local-archive`, reuses an existing cached installation for
    /// this version or installs the pinned remote archive. With
    /// `--local-archive`, replaces any existing cached installation for this
    /// version while coordinating with concurrent `verify` runs via the cache
    /// lock. Pass `--clear-old` to remove older cached toolchain directories
    /// without prompting; on an interactive terminal without `--clear-old`,
    /// prompts before removing them.
    #[cfg(feature = "setup")]
    Setup {
        /// Install a local archive, replacing any existing cached version.
        #[arg(long, value_name = "path")]
        local_archive: Option<PathBuf>,
        /// Remove older cached toolchain directories without prompting.
        #[arg(long)]
        clear_old: bool,
    },
    /// Scaffold starter Spec.lean and Proof.lean proof files.
    Init(init::InitArgs),
    /// Print the bundled agent skill.
    Skill {
        /// Print a complete Rust, request, and Lean example.
        #[arg(long)]
        example: bool,
    },
    /// Capture a configured compilation and check its authored source proof.
    #[command(after_help = "Run `cargo anneal skill` to print the bundled agent skill.")]
    Verify(Box<verify::VerifyArgs>),
    /// Offline inspection and comparison of Receipt Schema v3 JSON envelopes.
    Inspect(Box<inspect::InspectArgs>),
}

enum Action {
    Print { output: String, color: ColorChoice, quiet: bool, verbose: bool },
    Verify { args: Box<verify::VerifyArgs>, color: ColorChoice, quiet: bool, verbose: bool },
    Inspect { args: Box<inspect::InspectArgs>, color: ColorChoice, quiet: bool, verbose: bool },
}

#[derive(Debug)]
enum Failure {
    Arguments(clap::Error),
    Operation { error: String, color: ColorChoice },
}

fn parse(mut args: Vec<OsString>) -> Result<Cli, clap::Error> {
    // Cargo passes its subcommand name as the first argument. Both invocation
    // routes use the same parser after removing that one Cargo-owned argument.
    if args.get(1).is_some_and(|arg| arg == "anneal") {
        args.remove(1);
    }
    let cli = Cli::try_parse_from(args)?;
    match cli.command {
        Some(Command::Verify(ref verify_args)) => verify_args.validate(Cli::command())?,
        Some(Command::Inspect(ref inspect_args)) => inspect_args.validate(Cli::command())?,
        _ => {}
    }
    Ok(cli)
}

fn scalar_example() -> String {
    format!(
        "# Verify that `zero()` always returns 0\n\n\
         Save these four files together in a scratch directory. Run \
         `cargo anneal verify --request request.json` there after toolchain setup.\n\n\
         ## `lib.rs`\n\n```rust\n{rust}```\n\n\
         ## `request.json`\n\n```json\n{request}```\n\n\
         ## `Spec.lean`\n\n```lean\n{spec}```\n\n\
         ## `Proof.lean`\n\n```lean\n{proof}```\n",
        rust = include_str!("../assets/scalar/lib.rs"),
        request = include_str!("../assets/scalar/request.json"),
        spec = include_str!("../assets/scalar/Spec.lean"),
        proof = include_str!("../assets/scalar/Proof.lean"),
    )
}

#[cfg(feature = "setup")]
fn dispatch(
    cli: Cli,
    install: impl FnOnce(Option<PathBuf>, bool, bool) -> Result<PathBuf, String>,
) -> Result<Action, Failure> {
    let Cli { color, quiet, verbose, command } = cli;
    match command {
        None => Ok(Action::Print {
            output: format!("{}\n", Cli::command().render_help()),
            color,
            quiet,
            verbose,
        }),
        Some(Command::Setup { local_archive, clear_old }) => {
            let root = install(local_archive, clear_old, quiet)
                .map_err(|error| Failure::Operation { error, color })?;
            Ok(Action::Print {
                output: format!("Installed Anneal toolchain at {}\n", root.display()),
                color,
                quiet,
                verbose,
            })
        }
        Some(Command::Init(args)) => init::run(args)
            .map(|output| Action::Print { output, color, quiet, verbose })
            .map_err(|error| Failure::Operation { error, color }),
        Some(Command::Skill { example: true }) => {
            Ok(Action::Print { output: scalar_example(), color, quiet, verbose })
        }
        Some(Command::Skill { example: false }) => Ok(Action::Print {
            output: include_str!("../skills/cargo-anneal/SKILL.md").to_owned(),
            color,
            quiet,
            verbose,
        }),
        Some(Command::Verify(args)) => Ok(Action::Verify { args, color, quiet, verbose }),
        Some(Command::Inspect(args)) => Ok(Action::Inspect { args, color, quiet, verbose }),
    }
}

#[cfg(not(feature = "setup"))]
fn dispatch(cli: Cli) -> Result<Action, Failure> {
    let Cli { color, quiet, verbose, command } = cli;
    match command {
        None => Ok(Action::Print {
            output: format!("{}\n", Cli::command().render_help()),
            color,
            quiet,
            verbose,
        }),
        Some(Command::Init(args)) => init::run(args)
            .map(|output| Action::Print { output, color, quiet, verbose })
            .map_err(|error| Failure::Operation { error, color }),
        Some(Command::Skill { example: true }) => {
            Ok(Action::Print { output: scalar_example(), color, quiet, verbose })
        }
        Some(Command::Skill { example: false }) => Ok(Action::Print {
            output: include_str!("../skills/cargo-anneal/SKILL.md").to_owned(),
            color,
            quiet,
            verbose,
        }),
        Some(Command::Verify(args)) => Ok(Action::Verify { args, color, quiet, verbose }),
        Some(Command::Inspect(args)) => Ok(Action::Inspect { args, color, quiet, verbose }),
    }
}

fn parse_action(args: Vec<OsString>) -> Result<Result<Cli, Action>, Failure> {
    match parse(args) {
        Ok(cli) => Ok(Ok(cli)),
        Err(error)
            if matches!(error.kind(), ErrorKind::DisplayHelp | ErrorKind::DisplayVersion) =>
        {
            Ok(Err(Action::Print {
                output: error.to_string(),
                color: ColorChoice::Auto,
                quiet: false,
                verbose: false,
            }))
        }
        Err(error) => Err(Failure::Arguments(error)),
    }
}

#[cfg(feature = "setup")]
fn run(
    args: Vec<OsString>,
    install: impl FnOnce(Option<PathBuf>, bool, bool) -> Result<PathBuf, String>,
) -> Result<Action, Failure> {
    match parse_action(args)? {
        Ok(cli) => dispatch(cli, install),
        Err(action) => Ok(action),
    }
}

#[cfg(not(feature = "setup"))]
fn run(args: Vec<OsString>) -> Result<Action, Failure> {
    match parse_action(args)? {
        Ok(cli) => dispatch(cli),
        Err(action) => Ok(action),
    }
}

pub fn main() -> ExitCode {
    #[cfg(feature = "setup")]
    let outcome = run(env::args_os().collect(), setup::install_with_quiet);
    #[cfg(not(feature = "setup"))]
    let outcome = run(env::args_os().collect());

    match outcome {
        Ok(Action::Print { output, color, quiet, verbose }) => {
            let (mut session, _) = OutputSession::live(color, quiet, verbose, VerifyFormat::Human);
            finish_with_writers(&mut session, output.as_bytes(), 0)
        }
        Ok(Action::Verify { args, color, quiet, verbose }) => {
            verify::main(*args, color, quiet, verbose)
        }
        Ok(Action::Inspect { args, color, quiet, verbose }) => {
            inspect::main(*args, color, quiet, verbose)
        }
        Err(Failure::Arguments(error)) => {
            let (mut session, _) =
                OutputSession::live(ColorChoice::Auto, false, false, VerifyFormat::Human);
            session.write_clap_error(&error);
            ExitCode::from(2)
        }
        Err(Failure::Operation { error, color }) => {
            let (mut session, _) = OutputSession::live(color, false, false, VerifyFormat::Human);
            let _ = session.write_stderr_error(&error);
            ExitCode::from(1)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn args(values: &[&str]) -> Vec<OsString> {
        values.iter().map(OsString::from).collect()
    }

    #[cfg(feature = "setup")]
    fn must_not_install(_: Option<PathBuf>, _: bool, _: bool) -> Result<PathBuf, String> {
        panic!("argument handling must not install a toolchain")
    }

    fn run_without_install(args: Vec<OsString>) -> Result<Action, Failure> {
        #[cfg(feature = "setup")]
        {
            run(args, must_not_install)
        }
        #[cfg(not(feature = "setup"))]
        {
            run(args)
        }
    }

    fn output(action: Action) -> String {
        match action {
            Action::Print { output, .. } => output,
            Action::Verify { .. } | Action::Inspect { .. } => panic!("expected printable output"),
        }
    }

    #[test]
    fn help_and_version_do_not_install() {
        for prefix in [&["cargo-anneal"][..], &["cargo-anneal", "anneal"]] {
            for suffix in [
                &[][..],
                &["help"],
                &["-h"],
                &["--help"],
                #[cfg(feature = "setup")]
                &["setup", "-h"],
                #[cfg(feature = "setup")]
                &["setup", "--help"],
                #[cfg(feature = "setup")]
                &["help", "setup"],
                &["verify", "-h"],
                &["verify", "--help"],
                &["help", "verify"],
            ] {
                let output = output(
                    run_without_install(args(&[prefix, suffix].concat()))
                        .expect("help must succeed"),
                );
                assert!(output.contains("Usage:"), "{output}");
                if suffix.is_empty() {
                    #[cfg(feature = "setup")]
                    assert!(output.contains("setup"), "{output}");
                    #[cfg(not(feature = "setup"))]
                    assert!(!output.contains("setup"), "{output}");
                    assert!(output.contains("verify"), "{output}");
                }
            }
            for suffix in ["-V", "--version"] {
                let output = output(
                    run_without_install(args(&[prefix, &[suffix]].concat()))
                        .expect("version must succeed"),
                );
                assert_eq!(output, format!("cargo-anneal {}\n", env!("CARGO_PKG_VERSION")));
            }
        }
    }

    #[test]
    fn malformed_arguments_are_argument_failures() {
        for suffix in [
            &["unknown"][..],
            &["--unknown"],
            #[cfg(not(feature = "setup"))]
            &["setup"],
            #[cfg(feature = "setup")]
            &["setup", "--unknown"],
            #[cfg(feature = "setup")]
            &["setup", "--local-archive"],
            #[cfg(feature = "setup")]
            &["setup", "--local-archive", "--unknown"],
            &["verify"],
            &["verify", "--request"],
            &["verify", "--request", "request.json", "--unknown"],
            &["verify", "--request", "request.json", "--manifest-path", "Cargo.toml"],
            &[
                "verify",
                "--request",
                "request.json",
                "rustc",
                "lib.rs",
                "--crate-name",
                "c",
                "--spec-file",
                "Spec=Spec.lean",
                "--proof-file",
                "Proof=Proof.lean",
            ],
            &[
                "verify",
                "--manifest-path",
                "Cargo.toml",
                "--proof-dir",
                "proof",
                "rustc",
                "lib.rs",
                "--crate-name",
                "c",
                "--spec-file",
                "Spec=Spec.lean",
                "--proof-file",
                "Proof=Proof.lean",
            ],
            &[
                "verify",
                "--proof-dir",
                "proof",
                "rustc",
                "lib.rs",
                "--crate-name",
                "c",
                "--spec-file",
                "Spec=Spec.lean",
                "--proof-file",
                "Proof=Proof.lean",
            ],
            &["verify", "--request", "request.json", "--select", "subject::function"],
            &["verify", "--request", "request.json", "--features", "std"],
            &["verify", "--request", "request.json", "--all-features"],
            &["verify", "--request", "request.json", "--no-default-features"],
            &[
                "verify",
                "--features",
                "std",
                "rustc",
                "lib.rs",
                "--crate-name",
                "c",
                "--spec-file",
                "Spec=Spec.lean",
                "--proof-file",
                "Proof=Proof.lean",
            ],
            &["verify", "--request", "request.json", "--export-lean-lib"],
            &["verify", "--request", "request.json", "--capture", "cap"],
            &["verify", "--request", "request.json", "--sysroot", "sys"],
            &["verify", "--request", "request.json", "--allow-unpinned-lean"],
            &["verify", "--request", "request.json", "--lean-memory-mb", "0"],
            &[
                "verify",
                "rustc",
                "lib.rs",
                "--crate-name",
                "c",
                "--env",
                "MISSING_EQUALS",
                "--spec-file",
                "Spec=Spec.lean",
                "--proof-file",
                "Proof=Proof.lean",
            ],
            &[
                "verify",
                "rustc",
                "lib.rs",
                "--crate-name",
                "c",
                "--env",
                "CARGO_PKG_VERSION=0.1.0",
                "--env",
                "CARGO_PKG_VERSION=0.2.0",
                "--spec-file",
                "Spec=Spec.lean",
                "--proof-file",
                "Proof=Proof.lean",
            ],
        ] {
            let failure = run_without_install(args(&[&["cargo-anneal"], suffix].concat()))
                .err()
                .expect("malformed arguments must fail");
            let error = match failure {
                Failure::Arguments(error) => error,
                other => panic!("expected an argument failure, got {other:?}"),
            };
            assert_eq!(error.exit_code(), 2);
            assert!(error.to_string().contains("error:"));
        }
    }

    #[cfg(feature = "setup")]
    #[test]
    fn setup_dispatch_preserves_archive_and_operation_result() {
        for archive in [None, Some(PathBuf::from("local archive.tar.zst"))] {
            for clear_old in [false, true] {
                let mut input = args(&["cargo-anneal", "setup"]);
                if let Some(path) = &archive {
                    input.push("--local-archive".into());
                    input.push(path.as_os_str().into());
                }
                if clear_old {
                    input.push("--clear-old".into());
                }
                let output = output(
                    run(input.clone(), |actual_archive, actual_clear_old, actual_quiet| {
                        assert_eq!(actual_archive, archive);
                        assert_eq!(actual_clear_old, clear_old);
                        assert!(!actual_quiet);
                        Ok(PathBuf::from("installed toolchain"))
                    })
                    .expect("setup must return the operation's success"),
                );
                assert_eq!(output, "Installed Anneal toolchain at installed toolchain\n");

                let failure = run(input, |_, _, _| Err("archive unavailable".into()))
                    .err()
                    .expect("setup must return the operation's failure");
                assert!(matches!(
                    failure,
                    Failure::Operation { error: message, .. } if message == "archive unavailable"
                ));
            }
        }
    }

    #[test]
    fn verify_dispatch_preserves_both_invocation_routes() {
        for prefix in [&["cargo-anneal"][..], &["cargo-anneal", "anneal"]] {
            #[cfg(feature = "setup")]
            let cases: &[&[&str]] = &[
                &["verify", "--request", "request.json"],
                &[
                    "verify",
                    "--manifest-path",
                    "Cargo.toml",
                    "--proof-dir",
                    "proof",
                    "--no-default-features",
                    "--features",
                    "std,i128",
                    "--select",
                    "subject::function",
                ],
                &[
                    "verify",
                    "--lean",
                    "lean",
                    "rustc",
                    "src/lib.rs",
                    "--crate-name",
                    "foo",
                    "--env",
                    "CARGO_PKG_VERSION=0.8.64",
                    "--spec-file",
                    "Spec=Spec.lean",
                    "--proof-file",
                    "Proof=Proof.lean",
                ],
                &[
                    "verify",
                    "rustc",
                    "src/lib.rs",
                    "--crate-name",
                    "foo",
                    "--env",
                    "CARGO_PKG_VERSION=0.8.64",
                    "--spec-file",
                    "Spec=Spec.lean",
                    "--proof-file",
                    "Proof=Proof.lean",
                    "--lean",
                    "lean",
                    "--allow-unpinned-lean",
                    "--artifacts",
                    "out",
                    "--export-lean-lib",
                    "--lean-memory-mb",
                    "4096",
                ],
            ];
            #[cfg(not(feature = "setup"))]
            let cases: &[&[&str]] = &[
                &[
                    "verify",
                    "--capture",
                    "cap",
                    "--sysroot",
                    "sys",
                    "--lean",
                    "lean",
                    "--request",
                    "request.json",
                ],
                &[
                    "verify",
                    "--manifest-path",
                    "Cargo.toml",
                    "--proof-dir",
                    "proof",
                    "--select",
                    "subject::function",
                    "--capture",
                    "cap",
                    "--sysroot",
                    "sys",
                    "--lean",
                    "lean",
                ],
                &[
                    "verify",
                    "--capture",
                    "cap",
                    "--sysroot",
                    "sys",
                    "rustc",
                    "src/lib.rs",
                    "--crate-name",
                    "foo",
                    "--env",
                    "CARGO_PKG_VERSION=0.8.64",
                    "--spec-file",
                    "Spec=Spec.lean",
                    "--proof-file",
                    "Proof=Proof.lean",
                    "--lean",
                    "lean",
                ],
            ];
            for suffix in cases {
                let action = run_without_install(args(&[prefix, suffix].concat()))
                    .expect("verify arguments must parse and dispatch");
                assert!(matches!(action, Action::Verify { .. }));
            }
        }

        // Global `--color`, `-q`/`--quiet`, `-v`/`--verbose`, `--format`, and
        // `--receipt-out` parse cleanly before and after subcommands, while
        // `-q -v` and invalid enum values fail argument parsing.
        let valid_action = run_without_install(args(&[
            "cargo-anneal",
            "--color",
            "always",
            "-v",
            "verify",
            "--format",
            "json",
            "--receipt-out",
            "out/receipt.json",
            "--capture",
            "cap",
            "--sysroot",
            "sys",
            "--lean",
            "lean",
            "--request",
            "request.json",
        ]))
        .expect("global output flags must parse");
        assert!(matches!(
            valid_action,
            Action::Verify { color: ColorChoice::Always, quiet: false, verbose: true, .. }
        ));

        for bad in [
            &["cargo-anneal", "-q", "-v", "skill"][..],
            &["cargo-anneal", "--color", "bogus", "skill"],
            &[
                "cargo-anneal",
                "verify",
                "--format",
                "yaml",
                "--capture",
                "cap",
                "--sysroot",
                "sys",
                "--lean",
                "lean",
                "--request",
                "request.json",
            ],
        ] {
            assert!(
                matches!(run_without_install(args(bad)), Err(Failure::Arguments(_))),
                "{bad:?} must fail argument parsing"
            );
        }
    }

    #[cfg(all(unix, feature = "setup"))]
    #[test]
    fn archive_paths_do_not_require_utf8() {
        use std::os::unix::ffi::OsStringExt as _;

        let path = OsString::from_vec(b"archive-\xff.tar.zst".to_vec());
        let cli = parse(vec![
            "cargo-anneal".into(),
            "setup".into(),
            "--local-archive".into(),
            path.clone(),
        ])
        .expect("OS-native archive path must parse");
        assert!(matches!(
            cli.command,
            Some(Command::Setup { local_archive: Some(actual), clear_old: false })
                if actual.as_os_str() == path
        ));
    }

    #[test]
    fn inspect_dispatch_and_validation_work() {
        for route in [vec!["cargo-anneal", "inspect"], vec!["cargo-anneal", "anneal", "inspect"]] {
            let mut argv = route;
            argv.push("receipt.json");
            let action = run_without_install(args(&argv)).expect("parse inspect");
            assert!(matches!(
                action,
                Action::Inspect { ref args, .. }
                    if args.receipt.as_deref() == Some(std::path::Path::new("receipt.json"))
            ));
        }

        assert!(matches!(
            run_without_install(args(&[
                "cargo-anneal",
                "inspect",
                "receipt.json",
                "--color",
                "always",
                "-v",
            ])),
            Ok(Action::Inspect { color: ColorChoice::Always, quiet: false, verbose: true, .. })
        ));
        assert!(matches!(
            run_without_install(args(&[
                "cargo-anneal",
                "--color",
                "never",
                "-q",
                "inspect",
                "receipt.json",
            ])),
            Ok(Action::Inspect { color: ColorChoice::Never, quiet: true, verbose: false, .. })
        ));

        assert!(matches!(
            run_without_install(args(&["cargo-anneal", "inspect", "--diff", "-", "-"])),
            Err(Failure::Arguments(_))
        ));

        assert!(matches!(
            run_without_install(args(&[
                "cargo-anneal",
                "inspect",
                "--diff",
                "a.json",
                "b.json",
                "--check",
            ])),
            Err(Failure::Arguments(_))
        ));
    }
}
