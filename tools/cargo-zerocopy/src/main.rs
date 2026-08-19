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
//
// The meta-toolchain "all" instructs this script to run the provided command
// once for each "major" toolchain (msrv, stable, nightly). This does not
// include any toolchain which is listed in the `package.metadata.build-rs`
// Cargo.toml section.

use std::{
    collections::HashSet,
    env, fmt, fs,
    io::{self, BufRead as _, Write as _},
    process::{self, Command, Output, Stdio},
};

use toml::{map::Map, Value};

// This list has two consumers outside this workspace:
//
// - The UI test entry points use the cfg named by `UI_TEST_TOOLCHAIN_CFG` to
//   decide whether their diagnostic snapshots support the selected toolchain.
// - `testutil::UiTestRunner` maps these same names to snapshot suffixes.
//
// Keep all three in sync. CI checks the coupling so adding another supported
// UI toolchain fails until its snapshots and runner support are also added.
const UI_TEST_TOOLCHAINS: [&str; 3] = ["msrv", "stable", "nightly"];
const UI_TEST_TOOLCHAIN_CFG: &str = "__ZEROCOPY_INTERNAL_USE_ONLY_UI_TEST_TOOLCHAIN";

// Cargo test executables inherit this variable from the delegated Cargo
// process. `testutil::UiTestRunner` implements the matching decoder and reuses
// the outer command's feature selection when it builds UI fixture artifacts.
// Keep both ends and their fixed-vector tests synchronized.
const UI_TEST_FEATURE_ARGS_ENV: &str = "ZEROCOPY_UI_TEST_FEATURE_ARGS";

#[derive(Debug)]
enum Error {
    NoArguments,
    UnrecognizedArgument(String),
    MissingToolchainVersion,
    UnrecognizedToolchain(String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoArguments => write!(f, "No arguments provided"),
            Self::UnrecognizedArgument(arg) => write!(f, "Unrecognized argument: '{arg}'"),
            Self::MissingToolchainVersion => write!(f, "No toolchain version specified after '--version'"),
            Self::UnrecognizedToolchain(name) => write!(f, "Unrecognized toolchain name: `{name}` (options are 'msrv', 'stable', and 'nightly')")
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
    build_rs: Map<String, Value>,
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
                .map(|value| value.as_str().unwrap())?,
        })
    }
}

fn get_toolchain_versions() -> Versions {
    let manifest_text = fs::read_to_string("Cargo.toml").unwrap();
    let manifest = toml::from_str::<Value>(&manifest_text).unwrap();

    let package = manifest.as_table().unwrap()["package"].as_table().unwrap();
    let metadata = package["metadata"].as_table().unwrap();
    let build_rs = metadata["build-rs"].as_table().unwrap();
    let ci = metadata["ci"].as_table().unwrap();

    Versions {
        msrv: package["rust-version"].as_str().unwrap().to_string(),
        stable: ci["pinned-stable"].as_str().unwrap().to_string(),
        nightly: ci["pinned-nightly"].as_str().unwrap().to_string(),
        build_rs: build_rs.clone(),
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

fn is_ui_test_toolchain(name: &str) -> bool {
    UI_TEST_TOOLCHAINS.contains(&name)
}

// Extract Cargo's feature-selection options from the arguments before `--`.
// UI tests invoke Cargo recursively to locate the exact artifacts supplied to
// rustc. Reusing these options ensures that recursive build has the same
// default, disabled-default, explicit, or all-feature policy as its parent.
//
// Preserve each option's spelling and ordering. Cargo makes repeated feature
// options additive, and forwarding the original arguments delegates all of
// those semantics back to Cargo instead of duplicating them here.
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

// Environment variables cannot contain NUL bytes, so encode each argument as
// its decimal UTF-8 byte length, a colon, and its unmodified contents. Unlike
// choosing a separator, this remains lossless for every Unicode OS argument
// Cargo accepts. `testutil::UiTestRunner` implements the matching decoder.
fn encode_feature_selection_args(args: &[String]) -> String {
    let mut encoded = String::new();
    for arg in args {
        encoded.push_str(&arg.len().to_string());
        encoded.push(':');
        encoded.push_str(arg);
    }
    encoded
}

fn get_rustflags(name: &str) -> String {
    // See #1792 for context on zerocopy_derive_union_into_bytes.
    let mut flags =
        "--cfg zerocopy_unstable_linux --cfg zerocopy_derive_union_into_bytes --cfg __ZEROCOPY_INTERNAL_USE_ONLY_DEV_MODE"
            .to_string();
    flags += &format!(" --cfg __ZEROCOPY_INTERNAL_USE_ONLY_TOOLCHAIN=\"{name}\"");

    if is_ui_test_toolchain(name) {
        flags += &format!(" --cfg {UI_TEST_TOOLCHAIN_CFG}");
    }

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
    cmd.args(args).env("RUSTUP_TOOLCHAIN", "");
    if let Some((name, val)) = env {
        cmd.env(name, val);
    }
    cmd
}

fn cargo_subcommand_index(args: &[String]) -> Option<usize> {
    let mut index = 0;
    while let Some(arg) = args.get(index) {
        if arg == "--" {
            return None;
        }

        // These Cargo-global options consume the following argument. Keep
        // this list coordinated with Cargo's global CLI when another such
        // option is passed through cargo-zerocopy.
        if matches!(arg.as_str(), "--color" | "--config" | "--explain" | "-C" | "-Z") {
            index += 2;
            continue;
        }

        if arg.starts_with('-') {
            index += 1;
            continue;
        }

        return Some(index);
    }
    None
}

fn add_default_lock_mode(cmd: &mut Command, args: &mut Vec<String>) {
    // Treat the lockfile as an input to every command delegated through this
    // repository's Cargo wrapper.
    //
    // `--frozen` already implies `--locked`. Only inspect arguments before
    // `--`, since a test binary or another delegated program may have its own
    // unrelated argument with either spelling.
    let cargo_args_end = args.iter().position(|arg| arg == "--").unwrap_or(args.len());
    let lock_mode = if args[..cargo_args_end].iter().any(|arg| arg == "--frozen") {
        Some("--frozen")
    } else if args[..cargo_args_end].iter().any(|arg| arg == "--locked") {
        Some("--locked")
    } else {
        None
    };

    // Cargo consumes global options before dispatching an external command.
    // Clippy is a pinned rustup component and exposes Cargo's lock-mode flags,
    // so put the effective mode in Clippy's own argument list. Do not do this
    // for arbitrary `cargo-*` plugins: their argument languages are unrelated
    // (for example, cargo-readme rejects `--locked`). Other Cargo-driving
    // plugins must therefore spell their inner lock mode at their call sites.
    // In particular, keep `.github/workflows/ci.yml` coordinated: Miri's inner
    // flag must follow `miri nextest run`. The workflow contract test checks
    // this across every job so moving the invocation cannot lose the flag.
    if let Some(subcommand_index) = cargo_subcommand_index(&args[..cargo_args_end]) {
        if args[subcommand_index] == "clippy" {
            let forwarded = args[subcommand_index + 1..cargo_args_end]
                .iter()
                .any(|arg| arg == "--locked" || arg == "--frozen");
            if !forwarded {
                args.insert(subcommand_index + 1, lock_mode.unwrap_or("--locked").to_string());
            }
            return;
        }
    }

    if lock_mode.is_none() {
        cmd.arg("--locked");
    }
}

fn cargo_pkgid(version: &str) -> Command {
    rustup(["run", version, "cargo", "--locked", "--offline", "pkgid", "-p"], None)
}

fn delegate_cargo() -> Result<(), Error> {
    let mut args = env::args();
    let this = args.next().unwrap();
    let versions = get_toolchain_versions();

    match args.next().as_deref() {
        None => Err(Error::NoArguments),
        Some("--version") => {
            let name = args.next().ok_or(Error::MissingToolchainVersion)?;
            println!("{}", versions.get(&name)?);
            Ok(())
        }
        Some("+all") => {
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
        Some(arg) => {
            if let Some(name) = arg.strip_prefix('+') {
                let version = versions.get(name)?;

                install_toolchain_or_exit(&versions, name)?;

                let mut targets = Vec::new();
                if let Ok(t) = env::var("CARGO_BUILD_TARGET") {
                    targets.push(t);
                }

                let mut args_vec = args.collect::<Vec<_>>();
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
                add_default_lock_mode(&mut cmd, &mut args_vec);
                // Test executables inherit this value. UiTestRunner uses it
                // when recursively building zerocopy's fixture artifacts.
                cmd.env(
                    UI_TEST_FEATURE_ARGS_ENV,
                    encode_feature_selection_args(&feature_selection_args),
                );
                let mut args = args_vec.into_iter();

                if env::var("CARGO_TARGET_DIR").is_ok() {
                    eprintln!("[cargo-zerocopy] WARNING: `CARGO_TARGET_DIR` is set - this may cause `cargo-zerocopy` to behave unexpectedly");
                } else {
                    cmd.env("CARGO_TARGET_DIR", format!("target/by-toolchain/{}", name));
                }

                // Computes the fully-qualified package name of workspace package `p`.
                let fqpn = |p| {
                    let output = cargo_pkgid(version).arg(p).output_or_exit();
                    String::from_utf8(output.stdout).unwrap().trim().to_string()
                };

                // Replace `-p<package>`, `-p <package>` and `--package <package`
                // with the equivalent of `-p $(cargo pkgid -p <package>)`. We do
                // this because unqualified package names are sometimes ambiguous
                // if a dev-dependency has taken a dependency on an earlier
                // version of zerocopy or zerocopy-derive.
                loop {
                    let Some(arg) = args.next() else {
                        break;
                    };
                    if arg == "-p" || arg == "--package" {
                        cmd.arg(&arg);
                        let Some(arg) = args.next() else {
                            break;
                        };
                        cmd.arg(fqpn(arg));
                    } else if arg.starts_with("-p") {
                        cmd.arg("-p");
                        cmd.arg(fqpn(arg[2..].to_string()));
                    } else if arg == "--" {
                        cmd.arg("--");
                        cmd.args(args);
                        break;
                    } else {
                        if arg == "--target" {
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
                }

                cmd.execute();

                Ok(())
            } else {
                Err(Error::UnrecognizedArgument(arg.to_string()))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn strings(args: &[&str]) -> Vec<String> {
        args.iter().map(|arg| (*arg).to_string()).collect()
    }

    fn command_args(args: &[&str]) -> (Vec<String>, Vec<String>) {
        let mut args = strings(args);
        let mut cmd = Command::new("cargo");
        add_default_lock_mode(&mut cmd, &mut args);
        let global = cmd.get_args().map(|arg| arg.to_string_lossy().into_owned()).collect();
        (global, args)
    }

    #[test]
    fn defaults_to_locked() {
        assert_eq!(command_args(&["test"]), (strings(&["--locked"]), strings(&["test"])));
    }

    #[test]
    fn preserves_explicit_locked_or_frozen_mode() {
        assert_eq!(
            command_args(&["test", "--locked"]),
            (Vec::new(), strings(&["test", "--locked"]))
        );
        assert_eq!(
            command_args(&["--frozen", "test"]),
            (Vec::new(), strings(&["--frozen", "test"]))
        );
    }

    #[test]
    fn forwards_lock_mode_to_clippy() {
        assert_eq!(
            command_args(&["clippy", "--tests"]),
            (Vec::new(), strings(&["clippy", "--locked", "--tests"]))
        );
        assert_eq!(
            command_args(&["--color", "always", "clippy"]),
            (Vec::new(), strings(&["--color", "always", "clippy", "--locked"]))
        );
        assert_eq!(
            command_args(&["--frozen", "clippy"]),
            (Vec::new(), strings(&["--frozen", "clippy", "--frozen"]))
        );
        assert_eq!(
            command_args(&["--locked", "--frozen", "clippy"]),
            (Vec::new(), strings(&["--locked", "--frozen", "clippy", "--frozen"]))
        );
    }

    #[test]
    fn does_not_assume_other_plugin_argument_languages() {
        assert_eq!(
            command_args(&["readme", "--no-license"]),
            (strings(&["--locked"]), strings(&["readme", "--no-license"]))
        );
    }

    #[test]
    fn ignores_test_binary_arguments() {
        assert_eq!(
            command_args(&["test", "--", "--locked"]),
            (strings(&["--locked"]), strings(&["test", "--", "--locked"]))
        );
    }

    #[test]
    fn package_lookup_is_locked_and_offline() {
        let cmd = cargo_pkgid("1.2.3");
        let args = cmd.get_args().map(|arg| arg.to_string_lossy().into_owned()).collect::<Vec<_>>();
        assert_eq!(args, ["run", "1.2.3", "cargo", "--locked", "--offline", "pkgid", "-p"]);
    }

    #[test]
    fn captures_all_feature_selection_spellings_before_separator() {
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
    fn feature_selection_encoding_is_length_prefixed_utf8() {
        assert_eq!(
            encode_feature_selection_args(&strings(&[
                "--all-features",
                "--features",
                "derive,simd-nightly",
            ])),
            "14:--all-features10:--features19:derive,simd-nightly"
        );
        assert_eq!(encode_feature_selection_args(&strings(&["", ":", "μ"])), "0:1::2:μ");
    }

    #[test]
    fn ui_test_cfg_is_limited_to_snapshot_toolchains() {
        for name in UI_TEST_TOOLCHAINS {
            assert!(is_ui_test_toolchain(name));
            assert!(get_rustflags(name)
                .split_whitespace()
                .any(|flag| flag == UI_TEST_TOOLCHAIN_CFG));
        }

        for name in ["no-zerocopy-core-error-1-81-0", "1.93.1", "beta", ""] {
            assert!(!is_ui_test_toolchain(name));
            assert!(!get_rustflags(name)
                .split_whitespace()
                .any(|flag| flag == UI_TEST_TOOLCHAIN_CFG));
        }
    }
}

fn print_usage() {
    let name = env::args().next().unwrap();

    eprintln!("Usage:");
    eprintln!("  {} --version <toolchain-name>", name);
    eprintln!("  {} +<toolchain-name> [...]", name);
    eprintln!("  {} +all [...]", name);
}

fn main() {
    if let Err(e) = delegate_cargo() {
        eprintln!("Error: {e}");
        print_usage();
        process::exit(1);
    }
}
