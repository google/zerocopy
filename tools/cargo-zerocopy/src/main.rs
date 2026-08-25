// Copyright 2023 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// This script is a thin wrapper around Cargo that provides human-friendly
// toolchain names which are automatically translated to the toolchain versions
// we have pinned in CI.
//
//   cargo-zerocopy --version <toolchain-name> # looks up the version for the named toolchain
//   cargo-zerocopy +<toolchain-name> [...]    # runs cargo commands with the named toolchain
//   cargo-zerocopy +all [...]                 # runs cargo commands with each toolchain
//   cargo-zerocopy ci audit                   # checks all typed CI inputs and plans
//   cargo-zerocopy ci plan --event <event>    # prints selected CI work
//   cargo-zerocopy ci explain --event <event> # explains included and excluded work
//   cargo-zerocopy ci github-plan [...]        # writes checked Actions matrices
//
// The meta-toolchain "all" instructs this script to run the provided command
// once for each "major" toolchain (msrv, stable, nightly). This does not
// include any toolchain which is listed in the `package.metadata.build-rs`
// Cargo.toml section.

use std::{
    collections::{BTreeMap, HashSet},
    env, fmt,
    io::{self, BufRead as _, Write as _},
    path::{Path, PathBuf},
    process::{self, Command, Output, Stdio},
};

use zc::{
    execution::{EXECUTION_CONTEXT_ENV, MIRI_REPOSITORY_ROOT_CONTEXT},
    metadata::ToolchainMetadata,
};

// Cargo test executables inherit these variables from the delegated process.
// `testutil::UiTestRunner` reuses the exact outer feature selection when it
// recursively builds artifacts for UI fixtures.
const UI_TEST_FEATURE_ARG_COUNT_ENV: &str = "ZEROCOPY_UI_TEST_FEATURE_ARG_COUNT";
const UI_TEST_FEATURE_ARG_ENV_PREFIX: &str = "ZEROCOPY_UI_TEST_FEATURE_ARG_";

#[derive(Debug)]
enum Error {
    NoArguments,
    UnrecognizedArgument(String),
    MissingToolchainVersion,
    UnrecognizedToolchain(String),
    Ci(zc::cli::CliError),
    InvalidExecutionContext(String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoArguments => write!(f, "No arguments provided"),
            Self::UnrecognizedArgument(arg) => write!(f, "Unrecognized argument: '{arg}'"),
            Self::MissingToolchainVersion => write!(f, "No toolchain version specified after '--version'"),
            Self::UnrecognizedToolchain(name) => write!(f, "Unrecognized toolchain name: `{name}` (options are 'msrv', 'stable', and 'nightly')"),
            Self::Ci(error) => error.fmt(f),
            Self::InvalidExecutionContext(message) => write!(f, "invalid internal execution context: {message}"),
        }
    }
}

impl std::error::Error for Error {}

trait CommandExt {
    fn output_or_exit(&mut self) -> Output;
    fn execute(&mut self);
}

impl CommandExt for Command {
    fn output_or_exit(&mut self) -> Output {
        if let Ok(output) = self.output() {
            if !output.status.success() {
                eprintln!(
                    "[cargo-zerocopy] failed while capturing output from command: {:?}",
                    self
                );
                let stdout = std::str::from_utf8(&output.stdout).unwrap();
                let stderr = std::str::from_utf8(&output.stderr).unwrap();
                eprintln!("[cargo-zerocopy] stdout: {stdout}");
                eprintln!("[cargo-zerocopy] stderr: {stderr}");
                process::exit(output.status.code().unwrap_or(1));
            }
            output
        } else {
            eprintln!("[cargo-zerocopy] failed to run command: {:?}", self);
            process::exit(1);
        }
    }

    fn execute(&mut self) {
        if let Ok(status) = self.status() {
            if !status.success() {
                eprintln!("[cargo-zerocopy] failed while executing command: {:?}", self);
                process::exit(status.code().unwrap_or(1));
            }
        } else {
            eprintln!("[cargo-zerocopy] failed to run command: {:?}", self);
            process::exit(1);
        }
    }
}

struct Versions {
    msrv: String,
    stable: String,
    nightly: String,
    build_rs: BTreeMap<String, String>,
}

impl Versions {
    fn get(&self, name: &str) -> Result<&str, Error> {
        Ok(match name {
            "msrv" => &self.msrv,
            "stable" => &self.stable,
            "nightly" => &self.nightly,
            _ => self
                .build_rs
                .get(name)
                .ok_or(Error::UnrecognizedToolchain(name.to_string()))
                .map(String::as_str)?,
        })
    }
}

fn get_toolchain_versions() -> Versions {
    // `cargo.sh` runs this binary from the Zerocopy crate directory, so this
    // path names the manifest whose toolchains the wrapper must select. The
    // shared reader parses the file directly; it must not run Cargo while this
    // wrapper is still deciding which Cargo toolchain to invoke.
    let metadata = ToolchainMetadata::read("Cargo.toml").unwrap();

    Versions {
        msrv: metadata.rust_version,
        stable: metadata.pinned_stable,
        nightly: metadata.pinned_nightly,
        build_rs: metadata.build_rs,
    }
}

fn ensure_installed_or_exit(
    is_installed: impl FnOnce() -> Result<bool, Error>,
    install: impl FnOnce() -> Result<(), Error>,
    missing_item_desc: &str,
    prompt: &str,
) -> Result<(), Error> {
    if is_installed()? {
        return Ok(());
    }

    eprintln!("[cargo-zerocopy] {missing_item_desc}");
    if env::var("GITHUB_RUN_ID").is_ok() {
        eprintln!("[cargo-zerocopy] detected GitHub Actions environment; auto-installing without waiting for confirmation");
    } else if env::var("CARGO_ZEROCOPY_AUTO_INSTALL_TOOLCHAIN").is_ok() {
        eprintln!("[cargo-zerocopy] detected CARGO_ZEROCOPY_AUTO_INSTALL_TOOLCHAIN environment variable; auto-installing without waiting for confirmation");
    } else {
        eprintln!("[cargo-zerocopy] set CARGO_ZEROCOPY_AUTO_INSTALL_TOOLCHAIN=1 to always install toolchains and targets without prompting");
        loop {
            eprint!("[cargo-zerocopy] {prompt} (y/n)? ");
            io::stderr().flush().unwrap();
            let mut line = String::new();
            io::stdin().lock().read_line(&mut line).unwrap();
            let input = line.trim().to_lowercase();
            if input.starts_with('y') {
                break;
            } else if input.starts_with('n') {
                process::exit(1);
            }
        }
    }

    install()?;

    Ok(())
}

fn install_toolchain_or_exit(versions: &Versions, name: &str) -> Result<(), Error> {
    let version = versions.get(name)?.to_string();
    let is_nightly = version.contains("nightly");

    ensure_installed_or_exit(
        || {
            let output = rustup(["run", &version, "cargo", "version"], None).output();
            let output = match output {
                Ok(o) => o,
                Err(e) => {
                    eprintln!("[cargo-zerocopy] failed to run rustup: {e}");
                    process::exit(1);
                }
            };
            if output.status.success() {
                let output =
                    rustup([&format!("+{version}"), "component", "list"], None).output_or_exit();
                let stdout = String::from_utf8(output.stdout).unwrap();
                let is_installed =
                    |c| stdout.lines().any(|l| l.starts_with(c) && l.contains("(installed)"));
                let mut installed =
                    is_installed("rust-src") && is_installed("rustfmt") && is_installed("clippy");
                if is_nightly {
                    installed = installed && is_installed("miri");
                }
                Ok(installed)
            } else {
                Ok(false)
            }
        },
        || {
            let mut args = vec![
                "toolchain",
                "install",
                &version,
                "-c",
                "rust-src",
                "-c",
                "rustfmt",
                "-c",
                "clippy",
            ];
            if is_nightly {
                args.push("-c");
                args.push("miri");
            }
            rustup(args, None).stdout(Stdio::null()).execute();
            Ok(())
        },
        &format!(
            "missing toolchain '{name}' or one of its components (rust-src, rustfmt, clippy{})",
            if is_nightly { ", miri" } else { "" }
        ),
        &format!("would you like to install toolchain '{name}' and its components via 'rustup'"),
    )
}

fn install_targets_or_exit(version: &str, targets: &[String]) -> Result<(), Error> {
    // Avoid running `rustup` in the common case that no `--target` arguments
    // are provided.
    if targets.is_empty() {
        return Ok(());
    }

    let output = rustup(["target", "list", "--toolchain", version], None).output_or_exit();
    let stdout = String::from_utf8(output.stdout).unwrap();
    let mut installed = HashSet::new();
    let mut available = HashSet::new();

    for line in stdout.lines() {
        let mut parts = line.split_whitespace();
        if let Some(target) = parts.next() {
            available.insert(target.to_string());
            if parts.next() == Some("(installed)") {
                installed.insert(target.to_string());
            }
        }
    }

    let to_install = targets
        .iter()
        .filter(|target| {
            !installed.contains(target.as_str()) && available.contains(target.as_str())
        })
        .cloned()
        .collect::<Vec<_>>();

    let to_install_str = to_install.join(", ");
    ensure_installed_or_exit(
        || Ok(to_install.is_empty()),
        || {
            let mut args = vec!["target", "add", "--toolchain", version];
            args.extend(to_install.iter().map(|s| s.as_str()));
            rustup(args, None).stdout(Stdio::null()).execute();
            Ok(())
        },
        &format!("missing target(s): {to_install_str}"),
        &format!("would you like to install target(s) '{to_install_str}' via 'rustup'"),
    )
}

// Capture Cargo feature-selection arguments before the test-binary separator.
// Preserve their spelling and order: repeated feature options are additive,
// and replaying the original arguments delegates their semantics back to
// Cargo.
fn capture_feature_selection_args(args: &[String]) -> Vec<String> {
    let mut captured = Vec::new();
    let mut index = 0;

    while index < args.len() {
        let arg = &args[index];
        if arg == "--" {
            break;
        }

        if arg == "--features" || arg == "-F" {
            captured.push(arg.clone());
            if let Some(value) = args.get(index + 1) {
                captured.push(value.clone());
                index += 1;
            }
        } else if arg == "--all-features"
            || arg == "--no-default-features"
            || arg.starts_with("--features=")
            || (arg.starts_with("-F") && arg.len() > 2)
        {
            captured.push(arg.clone());
        }

        index += 1;
    }

    captured
}

fn set_ui_test_feature_args(command: &mut Command, args: &[String]) {
    command.env(UI_TEST_FEATURE_ARG_COUNT_ENV, args.len().to_string());
    for (index, arg) in args.iter().enumerate() {
        command.env(format!("{}{}", UI_TEST_FEATURE_ARG_ENV_PREFIX, index), arg);
    }
}

fn get_rustflags(name: &str) -> String {
    // See #1792 for context on zerocopy_derive_union_into_bytes.
    let mut flags =
        "--cfg zerocopy_unstable_linux --cfg zerocopy_derive_union_into_bytes --cfg __ZEROCOPY_INTERNAL_USE_ONLY_DEV_MODE"
            .to_string();
    flags += &format!(" --cfg __ZEROCOPY_INTERNAL_USE_ONLY_TOOLCHAIN=\"{name}\"");

    if name == "nightly" {
        flags += " --cfg __ZEROCOPY_INTERNAL_USE_ONLY_NIGHTLY_FEATURES_IN_TESTS";
    }

    flags
}

fn get_toolchain_rustflags(name: &str) -> String {
    format!("--cfg __ZEROCOPY_TOOLCHAIN=\"{}\"", name)
}

fn rustup<'a>(args: impl IntoIterator<Item = &'a str>, env: Option<(&str, &str)>) -> Command {
    let mut cmd = Command::new("rustup");
    // It's important to set `RUSTUP_TOOLCHAIN` to override any value set while
    // running this program. That variable overrides any `+<version>` CLI
    // argument.
    cmd.args(args)
        .env("RUSTUP_TOOLCHAIN", "")
        // The executor protocol is consumed by this wrapper only; never leak
        // it into rustup, Cargo, or metadata subprocesses.
        .env_remove(EXECUTION_CONTEXT_ENV);
    if let Some((name, val)) = env {
        cmd.env(name, val);
    }
    cmd
}

fn internal_execution_context() -> Result<bool, Error> {
    match env::var(EXECUTION_CONTEXT_ENV) {
        Ok(value) => parse_execution_context(Some(&value)),
        Err(env::VarError::NotPresent) => parse_execution_context(None),
        Err(error) => Err(Error::InvalidExecutionContext(error.to_string())),
    }
}

fn parse_execution_context(value: Option<&str>) -> Result<bool, Error> {
    match value {
        Some(value) if value == MIRI_REPOSITORY_ROOT_CONTEXT => Ok(true),
        Some(value) => Err(Error::InvalidExecutionContext(format!("unrecognized value {value:?}"))),
        None => Ok(false),
    }
}

fn validate_execution_context(active: bool, toolchain: &str, args: &[String]) -> Result<(), Error> {
    if !active {
        return Ok(());
    }
    let expected = ["miri", "nextest", "run", "--manifest-path", "zerocopy/Cargo.toml"];
    if toolchain != "nightly"
        || args
            .get(..expected.len())
            .is_none_or(|actual| !actual.iter().map(String::as_str).eq(expected))
    {
        return Err(Error::InvalidExecutionContext(
            "the repository-root context requires the nightly Miri command with its repository manifest".to_owned(),
        ));
    }
    Ok(())
}

fn repository_root() -> Result<PathBuf, Error> {
    let cwd =
        env::current_dir().map_err(|error| Error::InvalidExecutionContext(error.to_string()))?;
    cwd.parent().map(PathBuf::from).ok_or_else(|| {
        Error::InvalidExecutionContext("wrapper cwd has no repository parent".to_owned())
    })
}

fn default_target_dir(name: &str, repository_root: Option<&Path>) -> PathBuf {
    if let Some(root) = repository_root {
        root.join("zerocopy/target/by-toolchain").join(name)
    } else {
        PathBuf::from(format!("target/by-toolchain/{name}"))
    }
}

fn package_id_command(version: &str, package: &str, repository_root: Option<&Path>) -> Command {
    let mut command = rustup(["run", version, "cargo", "pkgid"], None);
    if let Some(root) = repository_root {
        command
            .args(["--manifest-path", "zerocopy/Cargo.toml"])
            .current_dir(root)
            .env_remove(EXECUTION_CONTEXT_ENV);
    }
    command.arg("-p").arg(package);
    command
}

fn delegate_cargo() -> Result<(), Error> {
    let mut args = env::args();
    let this = args.next().unwrap();
    let argument = args.next().ok_or(Error::NoArguments)?;
    let execution_context = internal_execution_context()?;

    // Both repository wrappers deliberately invoke this binary from the
    // `zerocopy` directory. Keep the `..` repository root coordinated with
    // `zc::cli`, `zerocopy/cargo.sh`, and `zerocopy/win-cargo.bat`. Route this
    // command before reading crate toolchain metadata: typed CI validation is
    // a repository-tools operation and does not delegate to Cargo.
    if argument == "ci" {
        if execution_context {
            return Err(Error::InvalidExecutionContext(
                "the repository-root context is only valid for the Miri Cargo command".to_owned(),
            ));
        }
        return zc::cli::run("..", args, io::stdout().lock()).map_err(Error::Ci);
    }

    let versions = get_toolchain_versions();

    match argument.as_str() {
        "--version" => {
            if execution_context {
                return Err(Error::InvalidExecutionContext(
                    "the repository-root context is only valid for the Miri Cargo command"
                        .to_owned(),
                ));
            }
            let name = args.next().ok_or(Error::MissingToolchainVersion)?;
            println!("{}", versions.get(&name)?);
            Ok(())
        }
        "+all" => {
            if execution_context {
                return Err(Error::InvalidExecutionContext(
                    "the repository-root context is only valid for the Miri Cargo command"
                        .to_owned(),
                ));
            }
            eprintln!("[cargo-zerocopy] warning: running the same command for each toolchain (msrv, stable, nightly)");
            let args = args.collect::<Vec<_>>();

            for toolchain in ["msrv", "stable", "nightly"] {
                eprintln!("[cargo-zerocopy] running with toolchain: {toolchain}");
                Command::new(this.clone())
                    .arg(format!("+{toolchain}"))
                    .args(args.clone())
                    .execute();
            }
            Ok(())
        }
        arg => {
            if let Some(name) = arg.strip_prefix('+') {
                let version = versions.get(name)?;
                let args_vec = args.collect::<Vec<_>>();
                validate_execution_context(execution_context, name, &args_vec)?;
                // Resolve the executor-owned cwd before any installation or
                // prompt. Once present, this option is the single source of
                // truth for every root-relative Cargo setting below.
                let repository_root = execution_context.then(repository_root).transpose()?;

                install_toolchain_or_exit(&versions, name)?;

                let mut targets = Vec::new();
                if let Ok(t) = env::var("CARGO_BUILD_TARGET") {
                    targets.push(t);
                }

                let feature_selection_args = capture_feature_selection_args(&args_vec);
                let mut i = 0;
                while i < args_vec.len() {
                    let arg = &args_vec[i];
                    if arg == "--" {
                        break;
                    }

                    if arg == "--target" {
                        if i + 1 < args_vec.len() {
                            targets.push(args_vec[i + 1].clone());
                            i += 1;
                        }
                    } else if let Some(t) = arg.strip_prefix("--target=") {
                        targets.push(t.to_string());
                    }
                    i += 1;
                }

                targets.retain(|t| !t.ends_with(".json"));
                targets.sort();
                targets.dedup();

                install_targets_or_exit(version, &targets)?;

                let mut args = args_vec.into_iter();

                let env_rustflags = env::vars()
                    .filter_map(|(k, v)| if k == "RUSTFLAGS" { Some(v) } else { None })
                    .next()
                    .unwrap_or_default();
                let env_rustdocflags = env::vars()
                    .filter_map(|(k, v)| if k == "RUSTDOCFLAGS" { Some(v) } else { None })
                    .next()
                    .unwrap_or_default();

                let rustflags = format!(
                    "{} {} {}",
                    get_rustflags(name),
                    get_toolchain_rustflags(name),
                    env_rustflags,
                );
                let rustdocflags = format!("{rustflags} {env_rustdocflags}");

                // Rustdoc needs the wrapper's cfgs and the caller's RUSTFLAGS
                // in addition to any rustdoc-specific flags supplied through
                // RUSTDOCFLAGS.
                let mut cmd = rustup(["run", version, "cargo"], Some(("RUSTFLAGS", &rustflags)));
                cmd.env("RUSTDOCFLAGS", &rustdocflags);
                set_ui_test_feature_args(&mut cmd, &feature_selection_args);

                // Cargo must run from the repository root for Miri: this
                // deliberately avoids discovering zerocopy/.cargo/config.toml,
                // while retaining every wrapper-added flag and environment.
                // The wrapper itself remains in the zerocopy directory.
                if let Some(root) = &repository_root {
                    cmd.current_dir(root);
                    cmd.env_remove(EXECUTION_CONTEXT_ENV);
                }

                if env::var("CARGO_TARGET_DIR").is_ok() {
                    eprintln!("[cargo-zerocopy] WARNING: `CARGO_TARGET_DIR` is set - this may cause `cargo-zerocopy` to behave unexpectedly");
                } else {
                    // The ordinary wrapper uses a path relative to its
                    // `zerocopy` cwd. Root context moves only the Cargo child,
                    // so keep the historical target location explicit.
                    cmd.env(
                        "CARGO_TARGET_DIR",
                        default_target_dir(name, repository_root.as_deref()),
                    );
                }

                // Computes the fully-qualified package name of workspace package `p`.
                let fqpn = |p: &str| {
                    let output =
                        package_id_command(version, p, repository_root.as_deref()).output_or_exit();
                    String::from_utf8(output.stdout).unwrap().trim().to_string()
                };

                // Replace `-p<package>`, `-p <package>` and `--package <package`
                // with the equivalent of `-p $(cargo pkgid -p <package>)`. We do
                // this because unqualified package names are sometimes ambiguous
                // if a dev-dependency has taken a dependency on an earlier
                // version of zerocopy or zerocopy-derive.
                while let Some(arg) = args.next() {
                    if arg == "-p" || arg == "--package" {
                        cmd.arg(&arg);
                        let Some(arg) = args.next() else {
                            break;
                        };
                        cmd.arg(fqpn(&arg));
                    } else if let Some(package) = arg.strip_prefix("-p") {
                        cmd.arg("-p");
                        cmd.arg(fqpn(package));
                    } else if arg == "--" {
                        cmd.arg("--");
                        cmd.args(args);
                        break;
                    } else if arg == "--target" {
                        cmd.arg(&arg);
                        if let Some(target) = args.next() {
                            cmd.arg(&target);
                            cmd.env("ZEROCOPY_UI_TEST_TARGET", target);
                        }
                    } else if let Some(target) = arg.strip_prefix("--target=") {
                        cmd.arg(&arg);
                        cmd.env("ZEROCOPY_UI_TEST_TARGET", target);
                    } else {
                        cmd.arg(arg);
                    }
                }

                cmd.execute();

                Ok(())
            } else {
                Err(Error::UnrecognizedArgument(arg.to_string()))
            }
        }
    }
}

fn print_usage() {
    let name = env::args().next().unwrap();
    eprintln!("Usage:");
    eprintln!("  {} --version <toolchain-name>", name);
    eprintln!("  {} +<toolchain-name> [...]", name);
    eprintln!("  {} +all [...]", name);
    eprintln!("  {} ci audit", name);
    eprintln!("  {} ci plan --event <event>", name);
    eprintln!("  {} ci explain --event <event>", name);
    eprintln!("  {} ci github-plan --event <event> --github-output <path> --artifact <path>", name);
    eprintln!("  {} ci execute-build-cell --event <event> --package <package> \\", name);
    eprintln!("      --toolchain <toolchain> --feature-profile <profile> --target <target>");
    eprintln!("  {} ci execute-miri-cell --event <event> --package <package> \\", name);
    eprintln!("      --toolchain <toolchain> --feature-profile <profile> --target <target> \\");
    eprintln!("      --miri-model <model>");
}

fn main() {
    if let Err(e) = delegate_cargo() {
        eprintln!("Error: {e}");
        print_usage();
        process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use std::{ffi::OsStr, path::Path, process::Command};

    use super::{
        capture_feature_selection_args, default_target_dir, package_id_command,
        parse_execution_context, set_ui_test_feature_args, validate_execution_context,
        EXECUTION_CONTEXT_ENV, MIRI_REPOSITORY_ROOT_CONTEXT,
    };

    fn strings(args: &[&str]) -> Vec<String> {
        args.iter().map(|arg| (*arg).to_string()).collect()
    }

    #[test]
    fn captures_feature_selection_before_separator() {
        let args = strings(&[
            "test",
            "--all-features",
            "--features",
            "alloc,derive",
            "-Fsimd",
            "-F",
            "std",
            "--no-default-features",
            "--features=float-nightly",
            "--",
            "--features",
            "ignored-test-argument",
        ]);

        assert_eq!(
            capture_feature_selection_args(&args),
            strings(&[
                "--all-features",
                "--features",
                "alloc,derive",
                "-Fsimd",
                "-F",
                "std",
                "--no-default-features",
                "--features=float-nightly",
            ])
        );
    }

    #[test]
    fn exports_indexed_ui_test_feature_args() {
        fn configured_env<'a>(command: &'a Command, key: &str) -> Option<&'a OsStr> {
            command
                .get_envs()
                .find(|(configured, _)| *configured == OsStr::new(key))
                .and_then(|(_, value)| value)
        }
        fn assert_env(command: &Command, key: &str, value: &str) {
            assert_eq!(configured_env(command, key), Some(OsStr::new(value)));
        }

        let mut command = Command::new("cargo");
        set_ui_test_feature_args(&mut command, &strings(&["--features", "", "-Fμ"]));
        assert_eq!(command.get_envs().count(), 4);
        assert_env(&command, "ZEROCOPY_UI_TEST_FEATURE_ARG_0", "--features");
        assert_env(&command, "ZEROCOPY_UI_TEST_FEATURE_ARG_1", "");
        assert_env(&command, "ZEROCOPY_UI_TEST_FEATURE_ARG_2", "-Fμ");
        assert_env(&command, "ZEROCOPY_UI_TEST_FEATURE_ARG_COUNT", "3");

        let mut command = Command::new("cargo");
        set_ui_test_feature_args(&mut command, &[]);
        assert_eq!(command.get_envs().count(), 1);
        assert_env(&command, "ZEROCOPY_UI_TEST_FEATURE_ARG_COUNT", "0");
    }

    #[test]
    fn execution_context_accepts_only_the_exact_nightly_miri_shape() {
        let args = strings(&["miri", "nextest", "run", "--manifest-path", "zerocopy/Cargo.toml"]);
        assert!(validate_execution_context(true, "nightly", &args).is_ok());
        assert!(validate_execution_context(false, "stable", &[]).is_ok());

        for (toolchain, command) in [
            ("stable", args.clone()),
            ("nightly", strings(&["test"])),
            ("nightly", strings(&["miri", "nextest", "run"])),
            ("nightly", strings(&["miri", "nextest", "run", "--manifest-path", "Cargo.toml"])),
        ] {
            assert!(validate_execution_context(true, toolchain, &command).is_err());
        }
    }

    #[test]
    fn execution_context_parser_is_exact_and_fail_closed() {
        assert!(!parse_execution_context(None).unwrap());
        assert!(parse_execution_context(Some(MIRI_REPOSITORY_ROOT_CONTEXT)).unwrap());
        assert!(parse_execution_context(Some("miri-repository-root ")).is_err());
        assert!(parse_execution_context(Some("1")).is_err());
    }

    #[test]
    fn package_id_command_preserves_ordinary_mode_and_configures_root_mode() {
        let ordinary = package_id_command("stable-version", "zerocopy", None);
        assert_eq!(
            ordinary.get_args().collect::<Vec<_>>(),
            [
                OsStr::new("run"),
                OsStr::new("stable-version"),
                OsStr::new("cargo"),
                OsStr::new("pkgid"),
                OsStr::new("-p"),
                OsStr::new("zerocopy"),
            ]
        );
        assert!(ordinary.get_current_dir().is_none());

        let root = Path::new("/repo");
        let root_mode = package_id_command("nightly-version", "zerocopy", Some(root));
        assert_eq!(root_mode.get_current_dir(), Some(root));
        assert_eq!(
            root_mode.get_args().collect::<Vec<_>>(),
            [
                OsStr::new("run"),
                OsStr::new("nightly-version"),
                OsStr::new("cargo"),
                OsStr::new("pkgid"),
                OsStr::new("--manifest-path"),
                OsStr::new("zerocopy/Cargo.toml"),
                OsStr::new("-p"),
                OsStr::new("zerocopy"),
            ]
        );
        let context =
            root_mode.get_envs().find(|(key, _)| *key == OsStr::new(EXECUTION_CONTEXT_ENV));
        assert_eq!(context, Some((OsStr::new(EXECUTION_CONTEXT_ENV), None)));
        assert_eq!(MIRI_REPOSITORY_ROOT_CONTEXT, "miri-repository-root");
    }

    #[test]
    fn target_directory_preserves_relative_default_and_root_location() {
        let root = Path::new("/repo");
        assert_eq!(default_target_dir("nightly", None), Path::new("target/by-toolchain/nightly"));
        assert_eq!(
            default_target_dir("nightly", Some(root)),
            Path::new("/repo/zerocopy/target/by-toolchain/nightly")
        );
    }
}
