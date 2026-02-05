// Copyright 2023 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![allow(unknown_lints)]
#![deny(unexpected_cfgs)]

use std::{env, path::PathBuf, process::Command};

#[derive(Debug)]
pub enum ToolchainVersion {
    /// The version listed as our MSRV (ie, the `package.rust-version` key in
    /// `Cargo.toml`).
    PinnedMsrv,
    /// The stable version pinned in CI.
    PinnedStable,
    /// The nightly version pinned in CI
    PinnedNightly,
}

impl ToolchainVersion {
    /// Attempts to determine whether the current toolchain version matches one
    /// of the versions pinned in CI and if so, which one.
    pub fn extract_from_env() -> Option<ToolchainVersion> {
        if cfg!(__ZEROCOPY_INTERNAL_USE_ONLY_TOOLCHAIN = "msrv") {
            Some(ToolchainVersion::PinnedMsrv)
        } else if cfg!(__ZEROCOPY_INTERNAL_USE_ONLY_TOOLCHAIN = "stable") {
            Some(ToolchainVersion::PinnedStable)
        } else if cfg!(__ZEROCOPY_INTERNAL_USE_ONLY_TOOLCHAIN = "nightly") {
            Some(ToolchainVersion::PinnedNightly)
        } else {
            None
        }
    }

    /// Gets the name of the directory in which to store source files and
    /// expected output for UI tests for this toolchain version.
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
    pub fn get_ui_source_files_dirname(&self) -> &'static str {
        match self {
            ToolchainVersion::PinnedMsrv => "ui-msrv",
            ToolchainVersion::PinnedStable => "ui-stable",
            ToolchainVersion::PinnedNightly => "ui-nightly",
        }
    }

    pub fn name(&self) -> &'static str {
        match self {
            ToolchainVersion::PinnedMsrv => "msrv",
            ToolchainVersion::PinnedStable => "stable",
            ToolchainVersion::PinnedNightly => "nightly",
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

    let mut rustflags = std::env::var_os("RUSTFLAGS").unwrap_or_default();
    rustflags.push(" -Wwarnings");
    std::env::set_var("RUSTFLAGS", rustflags);

    std::mem::drop(guard);
}

pub struct UiTestRunner {
    toolchain: ToolchainVersion,
    rustc_args: Vec<String>,
    tests_dir: String,
    tests_subdir: Option<String>,
}

impl Default for UiTestRunner {
    fn default() -> Self {
        Self::new()
    }
}

impl UiTestRunner {
    pub fn new() -> Self {
        let toolchain = ToolchainVersion::extract_from_env()
            .expect("UI tests must only be run on pinned MSRV, stable, or nightly toolchains");

        Self {
            toolchain,
            rustc_args: Vec::new(),
            tests_dir: "tests".to_string(), // Default prefix
            tests_subdir: None,
        }
    }

    pub fn rustc_arg(mut self, arg: impl Into<String>) -> Self {
        self.rustc_args.push(arg.into());
        self
    }

    pub fn dir(mut self, dir: impl Into<String>) -> Self {
        self.tests_dir = dir.into();
        self
    }

    pub fn subdir(mut self, subdir: impl Into<String>) -> Self {
        self.tests_subdir = Some(subdir.into());
        self
    }

    pub fn run(self) {
        // Find the root workspace
        let manifest_dir = env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR not set");
        let mut workspace_root = PathBuf::from(manifest_dir);
        loop {
            if workspace_root.join("cargo.sh").exists() {
                break;
            }
            if !workspace_root.pop() {
                panic!("Could not find workspace root");
            }
        }

        let mut rlib_path = None;
        let mut derive_lib_path = None;
        let mut static_assertions_path = None;

        let mut command = Command::new("cargo");
        command.current_dir(workspace_root.clone());
        // We strip `--cfg zerocopy_derive_union_into_bytes` from `RUSTFLAGS` so
        // that the `zerocopy-derive` proc macro is built without it. This ensures
        // it generates the `#[cfg(not(zerocopy_derive_union_into_bytes))]` checks
        // into the UI tests, which we can then explicitly enable or disable via
        // `rustc_args`.
        let mut rustflags = env::var("RUSTFLAGS").unwrap_or_default();
        rustflags = rustflags.replace("--cfg zerocopy_derive_union_into_bytes", "");
        if let Ok(flags) = env::var("RUSTDOCFLAGS") {
            command
                .env("RUSTDOCFLAGS", flags.replace("--cfg zerocopy_derive_union_into_bytes", ""));
        }
        command.env("RUSTFLAGS", rustflags);
        command.env_remove("CARGO_ENCODED_RUSTFLAGS");
        command.env_remove("CARGO_ENCODED_RUSTDOCFLAGS");

        command.args([
            "build",
            "-p",
            "zerocopy",
            "--features",
            "derive",
            "--tests",
            "--message-format=json",
        ]);

        let output = command.output().expect("Failed to execute cargo build for artifacts");
        if !output.status.success() {
            println!("{}", String::from_utf8_lossy(&output.stderr));
            panic!("Failed to build zerocopy artifacts for ui tests");
        }

        let stdout = String::from_utf8(output.stdout).unwrap();
        // DEBUG: print stdout and stderr to see if it rebuilt
        println!("CARGO BUILD STDERR:\n{}", String::from_utf8_lossy(&output.stderr));
        println!("CARGO BUILD STDOUT:\n{}", stdout);
        for msg in cargo_metadata::Message::parse_stream(stdout.as_bytes()) {
            if let Ok(cargo_metadata::Message::CompilerArtifact(artifact)) = msg {
                if artifact.profile.test {
                    // There can be multiple `libzerocopy` artifacts from other
                    // builds. Skip any that are built with `--test` - these
                    // aren't what we're looking for. If we include them, it
                    // will result in "duplicate crate" errors.
                    continue;
                }

                if artifact.target.name == "zerocopy"
                    && artifact.target.kind.iter().any(|k| k == "lib")
                {
                    for file in artifact.filenames {
                        if file.extension() == Some("rlib") {
                            rlib_path = Some(file);
                        }
                    }
                } else if artifact.target.name == "zerocopy-derive"
                    || artifact.target.name == "zerocopy_derive"
                {
                    for file in artifact.filenames {
                        if file.extension() == Some("so")
                            || file.extension() == Some("dylib")
                            || file.extension() == Some("dll")
                        {
                            derive_lib_path = Some(file);
                        }
                    }
                } else if artifact.target.name == "static_assertions" {
                    for file in artifact.filenames {
                        if file.extension() == Some("rlib") {
                            static_assertions_path = Some(file);
                        }
                    }
                }
            }
        }

        let rlib_path = rlib_path.expect("failed to find zerocopy.rlib");
        let derive_lib_path = derive_lib_path.expect("failed to find zerocopy_derive proc-macro");
        let static_assertions_path =
            static_assertions_path.expect("failed to find static_assertions rlib");

        let mut build_command = Command::new("rustup");

        // Prevent `RUSTFLAGS` (e.g. `-Zrandomize-layout` from Nightly CI) from
        // bleeding into our stable `ui-runner` build and crashing it.
        build_command.env_remove("CARGO_ENCODED_RUSTFLAGS");
        build_command.env_remove("RUSTFLAGS");
        build_command.env_remove("CARGO_ENCODED_RUSTDOCFLAGS");
        build_command.env_remove("RUSTDOCFLAGS");

        build_command.current_dir(workspace_root.clone());
        build_command.args([
            "run",
            "stable",
            "cargo",
            "build",
            "--manifest-path=tools/ui-runner/Cargo.toml",
            "--config=tools/.cargo/config.toml",
            "--message-format=json",
        ]);

        // Isolate build to avoid invalidating the libzerocopy cargo cache
        build_command.env("CARGO_TARGET_DIR", workspace_root.join("target/ui-runner"));

        let output = build_command.output().unwrap();
        if !output.status.success() {
            println!("{}", String::from_utf8_lossy(&output.stderr));
            panic!("Failed to build ui-runner");
        }

        let mut ui_runner_path = None;
        let stdout = String::from_utf8(output.stdout).unwrap();
        for msg in cargo_metadata::Message::parse_stream(stdout.as_bytes()) {
            if let Ok(cargo_metadata::Message::CompilerArtifact(artifact)) = msg {
                if artifact.target.name == "ui-runner" {
                    if let Some(path) = artifact.executable {
                        ui_runner_path = Some(path);
                    }
                }
            }
        }

        let ui_runner_path = ui_runner_path.expect("failed to find ui-runner binary");

        let mut command = Command::new(ui_runner_path);

        for arg in &self.rustc_args {
            command.arg(format!("--rustc-arg={}", arg));
        }

        command.env("ZEROCOPY_RLIB_PATH", rlib_path);
        command.env("ZEROCOPY_DERIVE_LIB_PATH", derive_lib_path);
        command.env("ZEROCOPY_STATIC_ASSERTIONS_PATH", static_assertions_path);

        let mut test_src_dir =
            format!("{}/{v}", &self.tests_dir, v = self.toolchain.get_ui_source_files_dirname());
        if let Some(subdir) = self.tests_subdir.as_ref() {
            test_src_dir = format!("{}/{}", test_src_dir, subdir);
        }
        command.env("ZEROCOPY_UI_TEST_DIR", test_src_dir);

        let toolchain_name =
            env::var("RUSTUP_TOOLCHAIN").unwrap_or_else(|_| self.toolchain.name().to_string());
        command.env("ZEROCOPY_UI_TEST_TOOLCHAIN", &toolchain_name);

        // Clear variables that might confuse the sub-invocation or rustc
        for (key, _) in env::vars() {
            if key.starts_with("CARGO_")
                || key.starts_with("RUST_")
                || key.starts_with("RUSTFLAGS")
                || key.starts_with("RUSTDOCFLAGS")
            {
                command.env_remove(&key);
            }
        }

        command.env("RUSTUP_TOOLCHAIN", toolchain_name);

        let mut proc = command.spawn().expect("Failed to spawn ui-runner");
        assert!(proc.wait().unwrap().success(), "ui-runner failed");
    }
}
