// Copyright 2023 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// Inlining format args isn't supported on our MSRV.
#![allow(clippy::uninlined_format_args)]

use std::{env, error::Error, fs};

use rustc_version::{Channel, Version};

pub struct PinnedVersions {
    pub msrv: String,
    pub stable: String,
    pub nightly: String,
}

impl PinnedVersions {
    /// Attempts to extract pinned toolchain versions based on the current
    /// working directory.
    ///
    /// `extract_from_pwd` expects to be called from a directory which is a
    /// child of a Cargo workspace. It extracts the pinned versions from the
    /// metadata of the root package.
    pub fn extract_from_pwd() -> Result<PinnedVersions, Box<dyn Error>> {
        let manifest_dir = env::var_os("CARGO_MANIFEST_DIR")
            .ok_or("CARGO_MANIFEST_DIR environment variable not set")?;
        let manifest_dir = std::path::Path::new(&manifest_dir);
        Self::extract_from_path(manifest_dir)
    }

    pub fn extract_from_path(
        manifest_dir: &std::path::Path,
    ) -> Result<PinnedVersions, Box<dyn Error>> {
        let manifest_path = if manifest_dir.ends_with("zerocopy-derive") {
            manifest_dir.parent().unwrap().join("Cargo.toml")
        } else if manifest_dir.ends_with("ui-runner") {
            manifest_dir.parent().unwrap().parent().unwrap().join("Cargo.toml")
        } else {
            manifest_dir.join("Cargo.toml")
        };
        let manifest = fs::read_to_string(manifest_path)?;
        let manifest: toml::map::Map<String, toml::Value> = toml::from_str(&manifest)?;
        let manifest = toml::Value::Table(manifest);

        let extract = |keys: &[&str]| -> Result<String, String> {
            let mut val = &manifest;
            for k in keys {
                val = val
                    .get(k)
                    .ok_or(format!("failed to look up path in Cargo.toml: {:?}", keys))?;
            }

            val.as_str()
                .map(|s| s.to_string())
                .ok_or(format!("expected string value for path in Cargo.toml: {:?}", keys))
        };

        let msrv = extract(&["package", "rust-version"])?;
        let stable = extract(&["package", "metadata", "ci", "pinned-stable"])?;
        let nightly = extract(&["package", "metadata", "ci", "pinned-nightly"])?;
        Ok(PinnedVersions { msrv, stable, nightly })
    }
}

#[derive(Debug, Copy, Clone)]
pub enum ToolchainVersion {
    /// The version listed as our MSRV (ie, the `package.rust-version` key in
    /// `Cargo.toml`).
    PinnedMsrv,
    /// The stable version pinned in CI.
    PinnedStable,
    /// The nightly version pinned in CI
    PinnedNightly,
    /// A stable version other than the one pinned in CI.
    OtherStable,
    /// A nightly version other than the one pinned in CI.
    OtherNightly,
}

impl ToolchainVersion {
    /// Attempts to determine whether the current toolchain version matches one
    /// of the versions pinned in CI and if so, which one.
    pub fn extract_from_pwd() -> Result<ToolchainVersion, Box<dyn Error>> {
        let pinned_versions = PinnedVersions::extract_from_pwd()?;
        let current = rustc_version::version_meta()?;

        let s = match current.channel {
            Channel::Dev | Channel::Beta => {
                return Err(format!("unsupported channel: {:?}", current.channel).into())
            }
            Channel::Nightly => {
                format!(
                    "nightly-{}",
                    current.commit_date.as_ref().ok_or("nightly channel missing commit date")?
                )
            }
            Channel::Stable => {
                let Version { major, minor, patch, .. } = current.semver;
                format!("{}.{}.{}", major, minor, patch)
            }
        };

        // Due to a quirk of how Rust nightly versions are encoded and published
        // [1], the version as understood by rustup uses a date one day ahead of
        // the version as encoded in the `rustc` binary itself.
        // `pinned_versions` encodes the former notion of the date (as it is
        // meant to be passed as the `+<toolchain>` selector syntax understood
        // by rustup), while `current` encodes the latter notion of the date (as
        // it is extracted from `rustc`). Without this adjustment, toolchain
        // versions that should be considered equal would not be.
        //
        // [1] https://github.com/rust-lang/rust/issues/51533
        let pinned_nightly_adjusted = {
            let desc = time::macros::format_description!("nightly-[year]-[month]-[day]");
            let date = time::Date::parse(&pinned_versions.nightly, &desc).map_err(|_| {
                format!("failed to parse nightly version: {}", pinned_versions.nightly)
            })?;
            let adjusted = date - time::Duration::DAY;
            adjusted.format(&desc).unwrap()
        };

        Ok(match s {
            s if s == pinned_versions.msrv => ToolchainVersion::PinnedMsrv,
            s if s == pinned_versions.stable => ToolchainVersion::PinnedStable,
            s if s == pinned_nightly_adjusted => ToolchainVersion::PinnedNightly,
            _ if current.channel == Channel::Stable => ToolchainVersion::OtherStable,
            _ if current.channel == Channel::Nightly => ToolchainVersion::OtherNightly,
            _ => {
                return Err(format!(
                    "current toolchain ({:?}) doesn't match any known version",
                    current
                )
                .into())
            }
        })
    }

    /// Gets the name of the directory in which to store source files and
    /// expected output for UI tests for this toolchain version.
    ///
    /// For toolchain versions which are not pinned in CI, prints a warning to
    /// `stderr` which will be captured by the test harness and only printed on
    /// test failure.
    ///
    /// UI tests depend on the exact error messages emitted by rustc, but those
    /// error messages are not stable, and sometimes change between Rust
    /// versions. Thus, we maintain one set of UI tests for each Rust version
    /// that we test in CI, and we pin to specific versions in CI (a specific
    /// MSRV, a specific stable version, and a specific date of the nightly
    /// compiler). Updating those pinned versions may also require updating
    /// these tests.
    /// - `tests/ui-nightly` - Contains the source of truth for our UI test
    ///   source files (`.rs`), and contains `.err` and `.out` files for nightly
    /// - `tests/ui-stable` - Contains symlinks to the `.rs` files in
    ///   `tests/ui-nightly`, and contains `.err` and `.out` files for stable
    /// - `tests/ui-msrv` - Contains symlinks to the `.rs` files in
    ///   `tests/ui-nightly`, and contains `.err` and `.out` files for MSRV
    pub fn get_ui_source_files_dirname_and_maybe_print_warning(&self) -> &'static str {
        if matches!(self, ToolchainVersion::OtherStable | ToolchainVersion::OtherNightly) {
            // This will be eaten by the test harness and only displayed on
            // failure.
            eprintln!("warning: current toolchain does not match any toolchain pinned in CI; this may cause spurious test failure");
        }

        match self {
            ToolchainVersion::PinnedMsrv => "ui-msrv",
            ToolchainVersion::PinnedStable | ToolchainVersion::OtherStable => "ui-stable",
            ToolchainVersion::PinnedNightly | ToolchainVersion::OtherNightly => "ui-nightly",
        }
    }
}

/// Sets `-Wwarnings` in `RUSTFLAGS`.
pub fn set_rustflags_w_warnings() {
    use parking_lot::Mutex;

    static ENV_MTX: Mutex<()> = parking_lot::const_mutex(());

    // Make sure we don't read/write the environment concurrently.
    // `env::set_var` should be `unsafe` to prevent this, but isn't. [1]
    //
    // [1] https://github.com/rust-lang/rust/issues/27970
    let guard = ENV_MTX.lock();

    let mut rustflags = env::var_os("RUSTFLAGS").unwrap_or_default();
    rustflags.push(" -Wwarnings");
    env::set_var("RUSTFLAGS", rustflags);

    std::mem::drop(guard);
}

/// Runs the UI tests using `ui-runner`.
pub fn run_ui_tests(toolchain: ToolchainVersion, tests_dir: &std::path::Path, extra_args: &[&str]) {
    use ToolchainVersion::*;
    let toolchain_arg = match toolchain {
        PinnedMsrv => "msrv",
        PinnedStable | OtherStable => "stable",
        PinnedNightly | OtherNightly => "nightly",
    };

    // Find dependencies.
    // We are running in `target/debug/deps` (or similar).
    // The executables and rlibs are in `target/debug/deps`.
    let current_exe = env::current_exe().unwrap();
    let deps_dir = current_exe.parent().unwrap();

    let cargo_bin = std::env::var("CARGO").unwrap_or_else(|_| "cargo".into());
    let mut cmd = std::process::Command::new(cargo_bin);

    if matches!(toolchain, ToolchainVersion::PinnedMsrv) {
        cmd.arg("+stable");
    }

    // Invoke ui-runner
    let current_dir = env::current_dir().unwrap();
    let runner_work_dir = if current_dir.join("tools/ui-runner").exists() {
        // We are at root (zerocopy package)
        current_dir.join("tools/ui-runner")
    } else if current_dir.join("../tools/ui-runner").exists() {
        // We are in zerocopy-derive package
        current_dir.join("../tools/ui-runner")
    } else {
        panic!("Could not locate tools/ui-runner from {}", current_dir.display());
    };

    let mut cmd = std::process::Command::new("cargo");
    cmd.current_dir(&runner_work_dir); // Run from ui-runner dir to pick up its .cargo/config.toml
    cmd.arg("+stable");
    cmd.arg("run");
    // Use manifest-path relative to CWD
    cmd.arg("--manifest-path")
        .arg("Cargo.toml")
        .arg("--quiet") // Reduce noise
        .arg("--")
        .arg("--target-toolchain")
        .arg(toolchain_arg)
        .arg("--deps-dir")
        .arg(deps_dir)
        .arg("--tests-dir")
        .arg(tests_dir);

    // Forward RUSTFLAGS if present, but clear them for the runner process itself
    // to avoid polluting the runner's build with nightly flags when running on stable.
    if let Ok(rustflags) = env::var("RUSTFLAGS") {
        cmd.env_remove("RUSTFLAGS");
        cmd.arg(format!("--rustflags={}", rustflags));
    }

    // Forward arguments
    if let Some(arg_idx) = env::args().position(|a| a == "--") {
        let args: Vec<_> = env::args().skip(arg_idx + 1).collect();
        cmd.args(args);
    } else {
        cmd.args(env::args().skip(1));
    }

    cmd.args(extra_args);

    eprintln!("Running ui-runner with toolchain: {}", toolchain_arg);
    let status = cmd.status().expect("failed to spawn ui-runner");

    if !status.success() {
        panic!("ui-runner failed");
    }
}
