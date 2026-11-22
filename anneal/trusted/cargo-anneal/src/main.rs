// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! CLI entrypoint for `cargo-anneal`.

#[cfg(feature = "setup")]
mod setup;
mod verify;

#[cfg(feature = "setup")]
use std::path::PathBuf;
use std::{env, ffi::OsString, process::ExitCode};

use clap::{CommandFactory, Parser, Subcommand, error::ErrorKind};

#[derive(Parser)]
#[command(
    name = "cargo-anneal",
    bin_name = "cargo anneal",
    version,
    about = "Formally verify Rust programs in Lean 4",
    after_help = "Also accepts direct invocation as cargo-anneal <COMMAND>."
)]
struct Cli {
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
    /// lock.
    #[cfg(feature = "setup")]
    Setup {
        /// Install a local archive, replacing any existing cached version.
        #[arg(long, value_name = "path")]
        local_archive: Option<PathBuf>,
    },
    /// Print the bundled agent skill.
    Skill {
        /// Print a complete Rust, request, and Lean example.
        #[arg(long)]
        example: bool,
    },
    /// Capture a configured compilation and check its authored source proof.
    #[command(after_help = "Run `cargo anneal skill` to print the bundled agent skill.")]
    Verify(Box<verify::VerifyArgs>),
}

enum Action {
    Print(String),
    Verify(Box<verify::VerifyArgs>),
}

#[derive(Debug)]
enum Failure {
    Arguments(clap::Error),
    #[cfg(feature = "setup")]
    Operation(String),
}

fn parse(mut args: Vec<OsString>) -> Result<Cli, clap::Error> {
    // Cargo passes its subcommand name as the first argument. Both invocation
    // routes use the same parser after removing that one Cargo-owned argument.
    if args.get(1).is_some_and(|arg| arg == "anneal") {
        args.remove(1);
    }
    let cli = Cli::try_parse_from(args)?;
    if let Some(Command::Verify(ref verify_args)) = cli.command {
        verify_args.validate(Cli::command())?;
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
        rust = include_str!("../tests/fixtures/scalar/lib.rs"),
        request = include_str!("../tests/fixtures/scalar/request.json"),
        spec = include_str!("../tests/fixtures/scalar/Spec.lean"),
        proof = include_str!("../tests/fixtures/scalar/Proof.lean"),
    )
}

#[cfg(feature = "setup")]
fn dispatch(
    cli: Cli,
    install: impl FnOnce(Option<PathBuf>) -> Result<PathBuf, String>,
) -> Result<Action, String> {
    match cli.command {
        None => Ok(Action::Print(format!("{}\n", Cli::command().render_help()))),
        Some(Command::Setup { local_archive }) => {
            let root = install(local_archive)?;
            Ok(Action::Print(format!("Installed Anneal toolchain at {}\n", root.display())))
        }
        Some(Command::Skill { example: true }) => Ok(Action::Print(scalar_example())),
        Some(Command::Skill { example: false }) => {
            Ok(Action::Print(include_str!("../skills/cargo-anneal/SKILL.md").to_owned()))
        }
        Some(Command::Verify(args)) => Ok(Action::Verify(args)),
    }
}

#[cfg(not(feature = "setup"))]
fn dispatch(cli: Cli) -> Action {
    match cli.command {
        None => Action::Print(format!("{}\n", Cli::command().render_help())),
        Some(Command::Skill { example: true }) => Action::Print(scalar_example()),
        Some(Command::Skill { example: false }) => {
            Action::Print(include_str!("../skills/cargo-anneal/SKILL.md").to_owned())
        }
        Some(Command::Verify(args)) => Action::Verify(args),
    }
}

fn parse_action(args: Vec<OsString>) -> Result<Result<Cli, Action>, Failure> {
    match parse(args) {
        Ok(cli) => Ok(Ok(cli)),
        Err(error)
            if matches!(error.kind(), ErrorKind::DisplayHelp | ErrorKind::DisplayVersion) =>
        {
            Ok(Err(Action::Print(error.to_string())))
        }
        Err(error) => Err(Failure::Arguments(error)),
    }
}

#[cfg(feature = "setup")]
fn run(
    args: Vec<OsString>,
    install: impl FnOnce(Option<PathBuf>) -> Result<PathBuf, String>,
) -> Result<Action, Failure> {
    match parse_action(args)? {
        Ok(cli) => dispatch(cli, install).map_err(Failure::Operation),
        Err(action) => Ok(action),
    }
}

#[cfg(not(feature = "setup"))]
fn run(args: Vec<OsString>) -> Result<Action, Failure> {
    match parse_action(args)? {
        Ok(cli) => Ok(dispatch(cli)),
        Err(action) => Ok(action),
    }
}

fn main() -> ExitCode {
    #[cfg(feature = "setup")]
    let outcome = run(env::args_os().collect(), setup::install);
    #[cfg(not(feature = "setup"))]
    let outcome = run(env::args_os().collect());

    match outcome {
        Ok(Action::Print(output)) => {
            print!("{output}");
            ExitCode::SUCCESS
        }
        Ok(Action::Verify(args)) => verify::main(*args),
        Err(Failure::Arguments(error)) => {
            eprint!("{error}");
            ExitCode::from(2)
        }
        #[cfg(feature = "setup")]
        Err(Failure::Operation(error)) => {
            eprintln!("error: {error}");
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
    fn must_not_install(_: Option<PathBuf>) -> Result<PathBuf, String> {
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
            Action::Print(output) => output,
            Action::Verify(_) => panic!("expected printable output"),
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
            &["verify", "--request", "request.json", "--export-lean-lib"],
            &["verify", "--request", "request.json", "--capture", "cap"],
            &["verify", "--request", "request.json", "--sysroot", "sys"],
            &["verify", "--request", "request.json", "--allow-unpinned-lean"],
            &["verify", "--request", "request.json", "--lean-memory-mb", "0"],
        ] {
            let failure = run_without_install(args(&[&["cargo-anneal"], suffix].concat()))
                .err()
                .expect("malformed arguments must fail");
            #[cfg_attr(not(feature = "setup"), allow(clippy::infallible_destructuring_match))]
            let error = match failure {
                Failure::Arguments(error) => error,
                #[cfg(feature = "setup")]
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
            let mut input = args(&["cargo-anneal", "setup"]);
            if let Some(path) = &archive {
                input.push("--local-archive".into());
                input.push(path.as_os_str().into());
            }
            let output = output(
                run(input.clone(), |actual| {
                    assert_eq!(actual, archive);
                    Ok(PathBuf::from("installed toolchain"))
                })
                .expect("setup must return the operation's success"),
            );
            assert_eq!(output, "Installed Anneal toolchain at installed toolchain\n");

            let failure = run(input, |_| Err("archive unavailable".into()))
                .err()
                .expect("setup must return the operation's failure");
            assert!(matches!(
                failure,
                Failure::Operation(message) if message == "archive unavailable"
            ));
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
                assert!(matches!(action, Action::Verify(_)));
            }
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
            Some(Command::Setup { local_archive: Some(actual) })
                if actual.as_os_str() == path
        ));
    }
}
