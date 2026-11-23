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
use crate::{init, verify};

/// Package version of `cargo-anneal` for CLI version output and external test
/// assertions.
#[doc(hidden)]
pub const PKG_VERSION: &str = env!("CARGO_PKG_VERSION");

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
    /// lock. Pass `--clear-old` to remove older cached toolchain directories
    /// without prompting; on an interactive terminal without `--clear-old`,
    /// prompts before removing them.
    #[cfg(feature = "setup")]
    Setup {
        /// Install a local archive, replacing any existing cached version.
        #[arg(long, value_name = "path")]
        local_archive: Option<PathBuf>,
        /// Expected SHA-256 hex digest of `--local-archive`.
        #[arg(long, value_name = "SHA256", requires = "local_archive")]
        expected_sha256: Option<String>,
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
    /// Validate split-plane Cargo spec packaging and optional evidence.
    PackageCheck(Box<crate::packaging::PackageCheckArgs>),
    /// Capture a configured compilation and check its authored source proof.
    #[command(after_help = "Run `cargo anneal skill` to print the bundled agent skill.")]
    Verify(Box<verify::VerifyArgs>),
}

enum Action {
    Print(String),
    PackageCheck(Box<crate::packaging::PackageCheckArgs>),
    Verify(Box<verify::VerifyArgs>),
}

#[derive(Debug)]
enum Failure {
    Arguments(clap::Error),
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
        rust = include_str!("../assets/scalar/lib.rs"),
        request = include_str!("../assets/scalar/request.json"),
        spec = include_str!("../assets/scalar/Spec.lean"),
        proof = include_str!("../assets/scalar/Proof.lean"),
    )
}

#[cfg(feature = "setup")]
fn dispatch(
    cli: Cli,
    install: impl FnOnce(Option<PathBuf>, Option<String>, bool) -> Result<PathBuf, String>,
) -> Result<Action, String> {
    match cli.command {
        None => Ok(Action::Print(format!("{}\n", Cli::command().render_help()))),
        Some(Command::Setup { local_archive, expected_sha256, clear_old }) => {
            let root = install(local_archive, expected_sha256, clear_old)?;
            Ok(Action::Print(format!("Installed Anneal toolchain at {}\n", root.display())))
        }
        Some(Command::Init(args)) => init::run(args).map(Action::Print),
        Some(Command::Skill { example: true }) => Ok(Action::Print(scalar_example())),
        Some(Command::Skill { example: false }) => {
            Ok(Action::Print(include_str!("../skills/cargo-anneal/SKILL.md").to_owned()))
        }
        Some(Command::PackageCheck(args)) => Ok(Action::PackageCheck(args)),
        Some(Command::Verify(args)) => Ok(Action::Verify(args)),
    }
}

#[cfg(not(feature = "setup"))]
fn dispatch(cli: Cli) -> Result<Action, String> {
    match cli.command {
        None => Ok(Action::Print(format!("{}\n", Cli::command().render_help()))),
        Some(Command::Init(args)) => init::run(args).map(Action::Print),
        Some(Command::Skill { example: true }) => Ok(Action::Print(scalar_example())),
        Some(Command::Skill { example: false }) => {
            Ok(Action::Print(include_str!("../skills/cargo-anneal/SKILL.md").to_owned()))
        }
        Some(Command::PackageCheck(args)) => Ok(Action::PackageCheck(args)),
        Some(Command::Verify(args)) => Ok(Action::Verify(args)),
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
    install: impl FnOnce(Option<PathBuf>, Option<String>, bool) -> Result<PathBuf, String>,
) -> Result<Action, Failure> {
    match parse_action(args)? {
        Ok(cli) => dispatch(cli, install).map_err(Failure::Operation),
        Err(action) => Ok(action),
    }
}

#[cfg(not(feature = "setup"))]
fn run(args: Vec<OsString>) -> Result<Action, Failure> {
    match parse_action(args)? {
        Ok(cli) => dispatch(cli).map_err(Failure::Operation),
        Err(action) => Ok(action),
    }
}

pub fn main() -> ExitCode {
    #[cfg(feature = "setup")]
    let outcome = run(env::args_os().collect(), setup::install_verified);
    #[cfg(not(feature = "setup"))]
    let outcome = run(env::args_os().collect());

    match outcome {
        Ok(Action::Print(output)) => {
            print!("{output}");
            ExitCode::SUCCESS
        }
        Ok(Action::PackageCheck(args)) => match crate::packaging::run_package_check(&args) {
            Ok(output) => {
                print!("{output}");
                ExitCode::SUCCESS
            }
            Err(failure) => {
                let envelope = serde_json::json!({
                    "status": "package_rejected",
                    "phase": failure.phase,
                    "detail": failure.message,
                });
                println!("{}", serde_json::to_string_pretty(&envelope).unwrap());
                ExitCode::from(u8::try_from(failure.code).unwrap_or(1))
            }
        },
        Ok(Action::Verify(args)) => verify::main(*args),
        Err(Failure::Arguments(error)) => {
            eprint!("{error}");
            ExitCode::from(2)
        }
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
    fn must_not_install(_: Option<PathBuf>, _: Option<String>, _: bool) -> Result<PathBuf, String> {
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
            Action::PackageCheck(_) | Action::Verify(_) => panic!("expected printable output"),
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
                    run(input.clone(), |actual_archive, actual_sha, actual_clear_old| {
                        assert_eq!(actual_archive, archive);
                        assert!(actual_sha.is_none());
                        assert_eq!(actual_clear_old, clear_old);
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
                    Failure::Operation(message) if message == "archive unavailable"
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
            Some(Command::Setup { local_archive: Some(actual), expected_sha256: None, clear_old: false })
                if actual.as_os_str() == path
        ));
    }

    #[test]
    fn package_check_dispatch_works_without_setup_feature() {
        let action = run_without_install(args(&[
            "cargo-anneal",
            "package-check",
            "--manifest-path",
            "Cargo.toml",
            "--run-cargo-package",
        ]))
        .expect("package-check arguments must parse");
        assert!(matches!(action, Action::PackageCheck(_)));
    }
}
