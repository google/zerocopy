// Copyright 2023 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

#![allow(unknown_lints)]
#![deny(unexpected_cfgs)]

use std::{
    env,
    ffi::OsStr,
    fs,
    path::{Path, PathBuf},
    process::Command,
};

const UI_TEST_FEATURE_ARG_COUNT_ENV: &str = "ZEROCOPY_UI_TEST_FEATURE_ARG_COUNT";
const UI_TEST_FEATURE_ARG_ENV_PREFIX: &str = "ZEROCOPY_UI_TEST_FEATURE_ARG_";
const UI_RUNNER_BIN_ENV: &str = "ZEROCOPY_UI_RUNNER_BIN";

fn resolve_prebuilt_ui_runner_bin(value: Option<&OsStr>) -> Result<Option<PathBuf>, String> {
    let path = match value {
        Some(value) if !value.is_empty() => PathBuf::from(value),
        _ => return Ok(None),
    };
    let metadata = fs::metadata(&path)
        .map_err(|err| format!("{} ({}) is invalid: {}", UI_RUNNER_BIN_ENV, path.display(), err))?;
    if !metadata.is_file() {
        return Err(format!("{} ({}) is not a file", UI_RUNNER_BIN_ENV, path.display()));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;

        if (metadata.permissions().mode() & 0o111) == 0 {
            return Err(format!("{} ({}) is not executable", UI_RUNNER_BIN_ENV, path.display()));
        }
    }
    if path.is_relative() && path.parent() == Some(Path::new("")) {
        if let Ok(cwd) = env::current_dir() {
            return Ok(Some(cwd.join(&path)));
        }
    }
    Ok(Some(path))
}

fn build_ui_runner(workspace_root: &Path, repo_root: &Path) -> PathBuf {
    let ui_runner_toolchain = select_ui_runner_toolchain(workspace_root);
    let mut build_command = Command::new("rustup");

    // Prevent `RUSTFLAGS` (e.g. `-Zrandomize-layout` from Nightly CI) from
    // bleeding into our stable `ui-runner` build and crashing it.
    build_command.env_remove("CARGO_ENCODED_RUSTFLAGS");
    build_command.env_remove("RUSTFLAGS");
    build_command.env_remove("CARGO_ENCODED_RUSTDOCFLAGS");
    build_command.env_remove("RUSTDOCFLAGS");

    build_command.current_dir(repo_root);
    build_command.args([
        "run",
        &ui_runner_toolchain,
        "cargo",
        "build",
        "--locked",
        "--manifest-path=tools/ui-runner/Cargo.toml",
        "--message-format=json",
    ]);

    // Isolate build to avoid invalidating the libzerocopy cargo cache
    build_command.env("CARGO_TARGET_DIR", repo_root.join("target/ui-runner"));

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

    ui_runner_path.expect("failed to find ui-runner binary").into_std_path_buf()
}

fn decode_feature_selection_args(
    count: Option<&str>,
    mut get_arg: impl FnMut(usize) -> Option<String>,
) -> Result<Vec<String>, String> {
    let count = match count {
        Some(count) => count,
        None => return Ok(Vec::new()),
    };
    let count = count
        .parse::<usize>()
        .map_err(|_| format!("{} must be a non-negative integer", UI_TEST_FEATURE_ARG_COUNT_ENV))?;
    (0..count)
        .map(|index| {
            get_arg(index)
                .ok_or_else(|| format!("missing {}{}", UI_TEST_FEATURE_ARG_ENV_PREFIX, index))
        })
        .collect()
}

fn outer_feature_selection_args() -> Vec<String> {
    let count = env::var(UI_TEST_FEATURE_ARG_COUNT_ENV).ok();
    decode_feature_selection_args(count.as_deref(), |index| {
        env::var(format!("{}{}", UI_TEST_FEATURE_ARG_ENV_PREFIX, index)).ok()
    })
    .unwrap_or_else(|error| panic!("invalid UI feature-argument protocol: {}", error))
}

fn parse_pinned_stable(cargo_toml: &str) -> Option<&str> {
    let mut in_ci_section = false;
    for raw_line in cargo_toml.lines() {
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if line.starts_with('[') {
            let header = line.split('#').next().unwrap_or(line).trim();
            in_ci_section = header == "[package.metadata.ci]";
            continue;
        }
        if !in_ci_section {
            continue;
        }
        if let Some((key, value)) = line.split_once('=') {
            if key.trim() == "pinned-stable" {
                let value = value.trim();
                if let Some(rest) = value.strip_prefix('"') {
                    if let Some((version, trailing)) = rest.split_once('"') {
                        let trailing = trailing.trim();
                        if !version.is_empty() && (trailing.is_empty() || trailing.starts_with('#'))
                        {
                            return Some(version);
                        }
                    }
                }
            }
        }
    }
    None
}

// Prefer `stable` when installed and fall back to `pinned-stable` from
// `zerocopy/Cargo.toml` so slim CI images do not have to ship both an unpinned
// and a pinned stable toolchain.
fn resolve_ui_runner_toolchain(toolchain_list: &str, cargo_toml: &str) -> String {
    let has_stable = toolchain_list.lines().any(|line| {
        matches!(
            line.split_whitespace().next(),
            Some(name) if name == "stable" || name.starts_with("stable-")
        )
    });
    if has_stable {
        return "stable".to_string();
    }
    parse_pinned_stable(cargo_toml).unwrap_or("stable").to_string()
}

fn select_ui_runner_toolchain(workspace_root: &Path) -> String {
    let toolchain_list = Command::new("rustup")
        .args(["toolchain", "list"])
        .output()
        .ok()
        .filter(|output| output.status.success())
        .and_then(|output| String::from_utf8(output.stdout).ok())
        .unwrap_or_default();
    let cargo_toml = fs::read_to_string(workspace_root.join("Cargo.toml")).unwrap_or_default();
    resolve_ui_runner_toolchain(&toolchain_list, &cargo_toml)
}

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
    use_outer_features: bool,
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
            use_outer_features: false,
        }
    }

    pub fn rustc_arg(mut self, arg: impl Into<String>) -> Self {
        self.rustc_args.push(arg.into());
        self
    }

    pub fn use_outer_features(mut self) -> Self {
        self.use_outer_features = true;
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
        let repo_root = workspace_root.parent().expect("Zerocopy root should have a parent");

        let mut rlib_path = None;
        let mut rmeta_path = None;
        let mut derive_lib_path = None;
        let mut static_assertions_path = None;
        let mut static_assertions_rmeta_path = None;
        let mut zerocopy_features = None;

        let mut command = Command::new("cargo");
        command.current_dir(workspace_root.clone());
        // We strip experimental feature cfgs from `RUSTFLAGS` so that the
        // `zerocopy-derive` proc macro is built without them. This ensures it
        // generates the feature-gate checks into the UI tests, which we can
        // then explicitly enable or disable via `rustc_args`.
        let mut rustflags = env::var("RUSTFLAGS").unwrap_or_default();
        let cfgs_to_strip = [
            "--cfg zerocopy_derive_union_into_bytes",
            "--cfg zerocopy_unstable_linux",
            "--cfg zerocopy_unstable_ptr",
        ];
        for &cfg in &cfgs_to_strip {
            rustflags = rustflags.replace(cfg, "");
        }
        if let Ok(flags) = env::var("RUSTDOCFLAGS") {
            let mut new_flags = flags;
            for &cfg in &cfgs_to_strip {
                new_flags = new_flags.replace(cfg, "");
            }
            command.env("RUSTDOCFLAGS", new_flags);
        }
        command.env("RUSTFLAGS", rustflags);
        command.env_remove("CARGO_ENCODED_RUSTFLAGS");
        command.env_remove("CARGO_ENCODED_RUSTDOCFLAGS");

        // `cargo-zerocopy` includes
        // `--cfg __ZEROCOPY_INTERNAL_USE_ONLY_NIGHTLY_FEATURES_IN_TESTS` in
        // `RUSTFLAGS` for the pinned nightly. That cfg enables a test-only proc
        // macro which requires `proc_macro::Span::def_site`, a nightly feature.
        //
        // Cargo historically treats host artifacts inconsistently depending
        // on whether `--target` is present. Without `--target`, `RUSTFLAGS`
        // apply to host artifacts such as proc macros and build scripts. With
        // `--target`, they do not. Consequently, relying only on `RUSTFLAGS`
        // would omit the test proc macro from the host `zerocopy-derive`
        // artifact in explicit-target UI tests, even when the explicit target
        // happens to equal the host triple.
        //
        // Configure target and host flags separately so that the test behaves
        // consistently with and without `--target`:
        //
        // - `-Ztarget-applies-to-host` enables the `target-applies-to-host`
        //   configuration key.
        // - `target-applies-to-host=false` prevents ordinary `RUSTFLAGS` and
        //   target/build configuration from also being applied to host
        //   artifacts.
        // - `-Zhost-config` enables the `host` configuration table.
        // - `host.rustflags` supplies just the nightly-test cfg to host
        //   artifacts, including the `zerocopy-derive` proc macro. It applies
        //   to every host artifact in this build, but the uniquely-named cfg is
        //   inert in crates which do not inspect it.
        //
        // Both `-Z` options are nightly-only, so they must not be passed during
        // the MSRV or stable UI tests. Keep this configuration inline rather
        // than in `.cargo/config.toml` so that ordinary stable Cargo commands
        // never encounter it. See:
        // https://doc.rust-lang.org/cargo/reference/unstable.html#host-config
        if matches!(&self.toolchain, ToolchainVersion::PinnedNightly) {
            command.args([
                "-Ztarget-applies-to-host",
                "-Zhost-config",
                "--config",
                "target-applies-to-host=false",
                "--config",
                // A `--config` value uses TOML syntax. The embedded quotes are
                // part of that syntax; `Command::args` passes the entire raw
                // string as one OS argument, so no shell quoting is needed.
                r#"host.rustflags=["--cfg", "__ZEROCOPY_INTERNAL_USE_ONLY_NIGHTLY_FEATURES_IN_TESTS"]"#,
            ]);
        }

        command.args(["build", "--locked", "--offline", "-p", "zerocopy"]);
        if self.use_outer_features {
            command.args(outer_feature_selection_args());
        }
        // Both UI suites require the derive proc macro. Cargo feature options
        // are additive, so this retains the outer selection when present.
        command.args(["--features", "derive", "--tests", "--message-format=json"]);

        // `cargo-zerocopy` uses `ZEROCOPY_UI_TEST_TARGET` to pass the value of
        // any `--target` CLI argument. Here, we use this target when building
        // `zerocopy` itself.
        let target = env::var("ZEROCOPY_UI_TEST_TARGET").ok();

        if let Some(ref t) = target {
            command.args(["--target", t]);
        }

        let output = command.output().expect("Failed to execute cargo build for artifacts");
        if !output.status.success() {
            println!("{}", String::from_utf8_lossy(&output.stderr));
            panic!("Failed to build zerocopy artifacts for ui tests");
        }

        let stdout = String::from_utf8(output.stdout).unwrap();
        // DEBUG: print stdout and stderr to see if it rebuilt
        // println!("CARGO BUILD STDERR:\n{}", String::from_utf8_lossy(&output.stderr));
        // println!("CARGO BUILD STDOUT:\n{}", stdout);
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
                    let mut features = artifact.features.clone();
                    features.sort();
                    features.dedup();
                    for file in artifact.filenames {
                        if file.extension() == Some("rlib") {
                            if let Some(ref previous) = zerocopy_features {
                                assert_eq!(
                                    previous, &features,
                                    "zerocopy artifacts used different features"
                                );
                            }
                            rlib_path = Some(file);
                            zerocopy_features = Some(features.clone());
                        } else if file.extension() == Some("rmeta") {
                            rmeta_path = Some(file);
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
                        } else if file.extension() == Some("rmeta") {
                            static_assertions_rmeta_path = Some(file);
                        }
                    }
                }
            }
        }

        let rlib_path = rlib_path.expect("failed to find zerocopy.rlib");
        let rmeta_path = rmeta_path.unwrap_or_else(|| rlib_path.clone());
        let derive_lib_path = derive_lib_path.expect("failed to find zerocopy_derive proc-macro");
        let static_assertions_path =
            static_assertions_path.expect("failed to find static_assertions rlib");
        let static_assertions_rmeta_path =
            static_assertions_rmeta_path.unwrap_or_else(|| static_assertions_path.clone());
        let zerocopy_features =
            zerocopy_features.expect("failed to find zerocopy artifact features");
        assert!(
            zerocopy_features.iter().any(|feature| feature == "derive"),
            "UI artifact build did not enable its required derive feature"
        );

        let prebuilt_ui_runner = env::var_os(UI_RUNNER_BIN_ENV);
        let ui_runner_path = match resolve_prebuilt_ui_runner_bin(prebuilt_ui_runner.as_deref()) {
            Ok(Some(path)) => path,
            Ok(None) => build_ui_runner(&workspace_root, repo_root),
            Err(err) => panic!("{}", err),
        };

        let mut command = Command::new(ui_runner_path);

        for arg in &self.rustc_args {
            command.arg(format!("--rustc-arg={}", arg));
        }

        // Cargo's artifact message is authoritative for the complete feature
        // closure. Give each fixture exactly the cfgs Cargo gave zerocopy.
        for feature in &zerocopy_features {
            command.arg(format!("--rustc-arg=--cfg=feature={:?}", feature));
        }

        command.env("ZEROCOPY_RLIB_PATH", rlib_path);
        command.env("ZEROCOPY_RMETA_PATH", rmeta_path);
        command.env("ZEROCOPY_DERIVE_LIB_PATH", derive_lib_path);
        command.env("ZEROCOPY_STATIC_ASSERTIONS_PATH", static_assertions_path);
        command.env("ZEROCOPY_STATIC_ASSERTIONS_RMETA_PATH", static_assertions_rmeta_path);
        command.env("ZEROCOPY_WORKSPACE_ROOT", workspace_root.display().to_string());

        if let Some(ref t) = target {
            command.arg(format!("--rustc-arg=--target={}", t));
        }

        let mut test_src_dir = format!("{}/ui", self.tests_dir);
        if let Some(subdir) = self.tests_subdir.as_ref() {
            test_src_dir = format!("{}/{}", test_src_dir, subdir);
        }
        command.env("ZEROCOPY_UI_TEST_DIR", test_src_dir);

        command.env("ZEROCOPY_UI_TEST_TOOLCHAIN_META_NAME", self.toolchain.name());

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

#[cfg(test)]
mod tests {
    use std::{env, ffi::OsStr, fs, path::PathBuf};

    use super::{
        decode_feature_selection_args, resolve_prebuilt_ui_runner_bin, resolve_ui_runner_toolchain,
        UI_RUNNER_BIN_ENV,
    };

    struct TempDir(PathBuf);

    impl Drop for TempDir {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }

    #[test]
    fn decodes_indexed_feature_arguments() {
        let values = ["", ":", "μ", "--features=derive,simd-nightly"];
        assert_eq!(
            decode_feature_selection_args(Some("4"), |index| {
                values.get(index).map(|value| (*value).to_string())
            })
            .unwrap(),
            values.iter().map(|value| (*value).to_string()).collect::<Vec<_>>()
        );
        assert!(decode_feature_selection_args(None, |_| panic!("must not read an argument"))
            .unwrap()
            .is_empty());
    }

    #[test]
    fn rejects_invalid_feature_argument_protocol() {
        assert!(decode_feature_selection_args(Some("invalid"), |_| None).is_err());
        assert!(decode_feature_selection_args(Some("1"), |_| None).is_err());
    }

    #[test]
    fn selects_ui_runner_toolchain_with_pinned_stable_fallback() {
        let cargo_toml = "\
[package]
name = \"zerocopy\"

[package.metadata.other]
pinned-stable = \"0.0.0\"

[package.metadata.ci] # inline comment
pinned-stable = \"1.100.0\" # trailing comment
pinned-nightly = \"nightly-2026-09-30\"
";
        assert_eq!(
            resolve_ui_runner_toolchain(
                "1.100.0-x86_64-unknown-linux-gnu (default)\nnightly-2026-09-30-x86_64-unknown-linux-gnu\n",
                cargo_toml,
            ),
            "1.100.0"
        );
        assert_eq!(
            resolve_ui_runner_toolchain(
                "stable-x86_64-unknown-linux-gnu (default)\n1.100.0-x86_64-unknown-linux-gnu\n",
                cargo_toml,
            ),
            "stable"
        );
        assert_eq!(
            resolve_ui_runner_toolchain(
                "1.100.0-x86_64-unknown-linux-gnu (default)\nstable-x86_64-unknown-linux-gnu\n",
                cargo_toml,
            ),
            "stable"
        );
        assert_eq!(
            resolve_ui_runner_toolchain("1.100.0-x86_64-unknown-linux-gnu\n", "[package]\n"),
            "stable"
        );
    }

    #[test]
    fn resolves_prebuilt_ui_runner_bin() {
        assert_eq!(resolve_prebuilt_ui_runner_bin(None), Ok(None));
        assert_eq!(resolve_prebuilt_ui_runner_bin(Some(OsStr::new(""))), Ok(None));

        let temp_dir = TempDir(env::temp_dir().join(format!(
            "zerocopy-testutil-ui-runner-{}-{}",
            std::process::id(),
            env::var("CARGO_PKG_NAME").unwrap_or_default()
        )));
        let _ = fs::remove_dir_all(&temp_dir.0);
        fs::create_dir_all(&temp_dir.0).unwrap();

        let missing = temp_dir.0.join("missing");
        let missing_err = resolve_prebuilt_ui_runner_bin(Some(missing.as_os_str())).unwrap_err();
        assert!(missing_err.contains(UI_RUNNER_BIN_ENV), "unexpected error: {}", missing_err);

        let dir_err = resolve_prebuilt_ui_runner_bin(Some(temp_dir.0.as_os_str())).unwrap_err();
        assert!(dir_err.contains("not a file"), "unexpected error: {}", dir_err);

        let runner = temp_dir.0.join("ui-runner");
        fs::write(&runner, b"#!/bin/sh\n").unwrap();

        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;

            let mut perms = fs::metadata(&runner).unwrap().permissions();
            perms.set_mode(0o644);
            fs::set_permissions(&runner, perms.clone()).unwrap();
            let non_exec_err =
                resolve_prebuilt_ui_runner_bin(Some(runner.as_os_str())).unwrap_err();
            assert!(non_exec_err.contains("not executable"), "unexpected error: {}", non_exec_err);

            perms.set_mode(0o755);
            fs::set_permissions(&runner, perms).unwrap();
        }

        assert_eq!(resolve_prebuilt_ui_runner_bin(Some(runner.as_os_str())), Ok(Some(runner)));
    }
}
