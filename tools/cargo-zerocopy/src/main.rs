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
    env, fmt,
    process::{self, Command, Output},
};

mod toolchain;

#[cfg(test)]
use toolchain::{
    env_is_non_empty, env_is_truthy, get_toolchain_versions_in, is_truthy_env_value, Versions,
};
use toolchain::{get_toolchain_versions, install_targets_or_exit, install_toolchain_or_exit};

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
    UnrecognizedToolchain { name: String, available_build_rs: Vec<String> },
    Manifest(String),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoArguments => write!(f, "No arguments provided"),
            Self::UnrecognizedArgument(arg) => write!(f, "Unrecognized argument: '{arg}'"),
            Self::MissingToolchainVersion => {
                write!(f, "No toolchain version specified after '--version'")
            }
            Self::UnrecognizedToolchain { name, available_build_rs } => {
                write!(
                    f,
                    "Unrecognized toolchain name: `{name}` (options are 'msrv', 'stable', 'nightly'"
                )?;
                if !available_build_rs.is_empty() {
                    write!(f, ", or a `[package.metadata.build-rs]` key: ")?;
                    for (idx, key) in available_build_rs.iter().enumerate() {
                        if idx > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "'{key}'")?;
                    }
                }
                write!(f, ")")
            }
            Self::Manifest(msg) => write!(f, "{msg}"),
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
        "--cfg zerocopy_unstable_linux --cfg zerocopy_unstable_ptr --cfg zerocopy_derive_union_into_bytes --cfg __ZEROCOPY_INTERNAL_USE_ONLY_DEV_MODE"
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
    cmd.args(args).env("RUSTUP_TOOLCHAIN", "");
    if let Some((name, val)) = env {
        cmd.env(name, val);
    }
    cmd
}

fn delegate_cargo() -> Result<(), Error> {
    let mut args = env::args();
    let this = args.next().ok_or(Error::NoArguments)?;

    match args.next().as_deref() {
        None => Err(Error::NoArguments),
        Some("--version") => {
            let name = args.next().ok_or(Error::MissingToolchainVersion)?;
            let versions = get_toolchain_versions()?;
            println!("{}", versions.get(&name)?);
            Ok(())
        }
        Some("+all") => {
            let _versions = get_toolchain_versions()?;
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
                let versions = get_toolchain_versions()?;
                let version = versions.get(name)?;

                install_toolchain_or_exit(&versions, name)?;

                let mut targets = Vec::new();
                if let Ok(t) = env::var("CARGO_BUILD_TARGET") {
                    targets.push(t);
                }

                let args_vec = args.collect::<Vec<_>>();
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

                if env::var("CARGO_TARGET_DIR").is_ok() {
                    eprintln!("[cargo-zerocopy] WARNING: `CARGO_TARGET_DIR` is set - this may cause `cargo-zerocopy` to behave unexpectedly");
                } else {
                    cmd.env("CARGO_TARGET_DIR", format!("target/by-toolchain/{}", name));
                }

                // Computes the fully-qualified package name of workspace package `p`.
                let fqpn = |p| {
                    let output = rustup(["run", version, "cargo", "pkgid", "-p"], None)
                        .arg(p)
                        .output_or_exit();
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
                        cmd.arg(fqpn(arg));
                    } else if let Some(pkg) = arg.strip_prefix("-p") {
                        cmd.arg("-p");
                        cmd.arg(fqpn(pkg.to_string()));
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
    let name = env::args().next().unwrap_or_else(|| "cargo-zerocopy".to_string());

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

#[cfg(test)]
mod tests {
    use std::{collections::BTreeMap, env, ffi::OsStr, fs, path::PathBuf, process::Command};

    use super::{
        capture_feature_selection_args, env_is_non_empty, env_is_truthy, get_toolchain_versions_in,
        is_truthy_env_value, set_ui_test_feature_args, Error, Versions,
    };

    struct TempDir(PathBuf);

    impl TempDir {
        fn new(suffix: &str) -> Self {
            let dir = env::temp_dir().join(format!(
                "cargo-zerocopy-test-{}-{}-{}",
                std::process::id(),
                env::var("CARGO_PKG_NAME").unwrap_or_default(),
                suffix
            ));
            let _ = fs::remove_dir_all(&dir);
            fs::create_dir_all(&dir).unwrap();
            Self(dir)
        }
    }

    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    fn sample_manifest(extra_build_rs: &str) -> String {
        format!(
            "\
[package]
name = \"zerocopy\"
rust-version = \"1.56.0\"

[package.metadata.build-rs]
no-zerocopy-core-error-1-81-0 = \"1.81.0\"
{extra_build_rs}

[package.metadata.ci]
pinned-stable = \"1.100.0\"
pinned-nightly = \"nightly-2026-09-30\"
"
        )
    }

    fn strings(args: &[&str]) -> Vec<String> {
        args.iter().map(|arg| (*arg).to_string()).collect()
    }

    #[test]
    fn env_truthiness_rejects_unset_empty_zero_and_false() {
        for falsy in
            [None, Some(""), Some("   "), Some("0"), Some("false"), Some("FALSE"), Some("False")]
        {
            assert!(!is_truthy_env_value(falsy), "expected falsy for {falsy:?}");
        }
        for truthy in [Some("1"), Some("true"), Some("TRUE"), Some("yes")] {
            assert!(is_truthy_env_value(truthy), "expected truthy for {truthy:?}");
        }

        const TEST_KEY: &str = "CARGO_ZEROCOPY_TEST_TRUTHY_VAR";
        env::remove_var(TEST_KEY);
        assert!(!env_is_truthy(TEST_KEY));
        assert!(!env_is_non_empty(TEST_KEY));

        env::set_var(TEST_KEY, "");
        assert!(!env_is_truthy(TEST_KEY));
        assert!(!env_is_non_empty(TEST_KEY));

        env::set_var(TEST_KEY, "0");
        assert!(!env_is_truthy(TEST_KEY));
        assert!(env_is_non_empty(TEST_KEY));

        env::set_var(TEST_KEY, "FaLsE");
        assert!(!env_is_truthy(TEST_KEY));

        env::set_var(TEST_KEY, "1");
        assert!(env_is_truthy(TEST_KEY));
        assert!(env_is_non_empty(TEST_KEY));

        env::remove_var(TEST_KEY);
    }

    #[test]
    fn versions_get_supports_build_rs_and_formats_unrecognized_error() {
        let mut build_rs = BTreeMap::new();
        build_rs.insert("no-zerocopy-core-error-1-81-0".to_string(), "1.81.0".to_string());
        let versions = Versions {
            msrv: "1.56.0".to_string(),
            stable: "1.100.0".to_string(),
            nightly: "nightly-2026-09-30".to_string(),
            build_rs,
        };

        assert_eq!(versions.get("msrv").unwrap(), "1.56.0");
        assert_eq!(versions.get("stable").unwrap(), "1.100.0");
        assert_eq!(versions.get("nightly").unwrap(), "nightly-2026-09-30");
        assert_eq!(versions.get("no-zerocopy-core-error-1-81-0").unwrap(), "1.81.0");

        let err = versions.get("unknown").unwrap_err();
        let msg = err.to_string();
        assert!(msg.contains("msrv"));
        assert!(msg.contains("stable"));
        assert!(msg.contains("nightly"));
        assert!(msg.contains("build-rs"));
        assert!(msg.contains("no-zerocopy-core-error-1-81-0"));
    }

    #[test]
    fn manifest_discovery_handles_zerocopy_root_repo_root_and_errors() {
        let zc_dir = TempDir::new("zc-dir");
        fs::write(zc_dir.0.join("Cargo.toml"), sample_manifest("")).unwrap();
        let direct = get_toolchain_versions_in(&zc_dir.0).expect("direct Cargo.toml should parse");
        assert_eq!(direct.msrv, "1.56.0");
        assert_eq!(direct.get("no-zerocopy-core-error-1-81-0").unwrap(), "1.81.0");

        let repo_root = TempDir::new("repo-root");
        fs::create_dir_all(repo_root.0.join("zerocopy")).unwrap();
        fs::write(repo_root.0.join("zerocopy/Cargo.toml"), sample_manifest("")).unwrap();
        let from_root =
            get_toolchain_versions_in(&repo_root.0).expect("zerocopy/Cargo.toml should parse");
        assert_eq!(from_root, direct);

        // An unrelated local Cargo.toml does not satisfy `[package].name == "zerocopy"`.
        let other_crate = TempDir::new("other-crate");
        fs::write(other_crate.0.join("Cargo.toml"), "[package]\nname = \"other\"\n").unwrap();
        let err = get_toolchain_versions_in(&other_crate.0).unwrap_err();
        assert!(matches!(err, Error::Manifest(_)), "unexpected error: {err:?}");

        // Non-string `build-rs` values return a clean manifest error instead of panicking.
        let bad_build_rs = TempDir::new("bad-build-rs");
        fs::write(bad_build_rs.0.join("Cargo.toml"), sample_manifest("bad-entry = 181")).unwrap();
        let err = get_toolchain_versions_in(&bad_build_rs.0).unwrap_err();
        assert!(err.to_string().contains("bad-entry"), "unexpected error: {err}");
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
}
