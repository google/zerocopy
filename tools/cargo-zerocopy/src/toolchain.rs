// Copyright 2023 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Pinned toolchain versions from the zerocopy manifest, and their
//! installation through `rustup`.

use std::{
    collections::{BTreeMap, HashSet},
    env, fs,
    io::{self, BufRead as _, Write as _},
    path::{Path, PathBuf},
    process::{self, Stdio},
};

use toml::Value;

use super::{rustup, CommandExt, Error};

#[derive(Debug, PartialEq, Eq)]
pub(super) struct Versions {
    pub(super) msrv: String,
    pub(super) stable: String,
    pub(super) nightly: String,
    pub(super) build_rs: BTreeMap<String, String>,
}

impl Versions {
    pub(super) fn get(&self, name: &str) -> Result<&str, Error> {
        match name {
            "msrv" => Ok(&self.msrv),
            "stable" => Ok(&self.stable),
            "nightly" => Ok(&self.nightly),
            _ => self.build_rs.get(name).map(String::as_str).ok_or_else(|| {
                Error::UnrecognizedToolchain {
                    name: name.to_string(),
                    available_build_rs: self.build_rs.keys().cloned().collect(),
                }
            }),
        }
    }

    fn parse(manifest_text: &str, path: &Path) -> Result<Self, Error> {
        let manifest = toml::from_str::<Value>(manifest_text)
            .map_err(|err| Error::Manifest(format!("Failed to parse {}: {err}", path.display())))?;
        let package = manifest
            .as_table()
            .and_then(|t| t.get("package"))
            .and_then(Value::as_table)
            .ok_or_else(|| {
                Error::Manifest(format!("Missing [package] table in {}", path.display()))
            })?;
        let metadata = package.get("metadata").and_then(Value::as_table).ok_or_else(|| {
            Error::Manifest(format!("Missing [package.metadata] table in {}", path.display()))
        })?;
        let build_rs_table =
            metadata.get("build-rs").and_then(Value::as_table).ok_or_else(|| {
                Error::Manifest(format!(
                    "Missing [package.metadata.build-rs] table in {}",
                    path.display()
                ))
            })?;
        let ci = metadata.get("ci").and_then(Value::as_table).ok_or_else(|| {
            Error::Manifest(format!("Missing [package.metadata.ci] table in {}", path.display()))
        })?;

        let require_non_empty_str =
            |table: &toml::map::Map<String, Value>, section: &str, key: &str| {
                table
                    .get(key)
                    .and_then(Value::as_str)
                    .filter(|s| !s.trim().is_empty())
                    .map(str::to_string)
                    .ok_or_else(|| {
                        Error::Manifest(format!(
                            "Expected non-empty string for `{section}.{key}` in {}",
                            path.display()
                        ))
                    })
            };

        let msrv = require_non_empty_str(package, "package", "rust-version")?;
        let stable = require_non_empty_str(ci, "package.metadata.ci", "pinned-stable")?;
        let nightly = require_non_empty_str(ci, "package.metadata.ci", "pinned-nightly")?;

        let mut build_rs = BTreeMap::new();
        for (key, value) in build_rs_table {
            let version = value.as_str().filter(|s| !s.trim().is_empty()).ok_or_else(|| {
                Error::Manifest(format!(
                    "Expected non-empty string for `package.metadata.build-rs.{key}` in {}",
                    path.display()
                ))
            })?;
            build_rs.insert(key.clone(), version.to_string());
        }

        Ok(Self { msrv, stable, nightly, build_rs })
    }
}

fn is_zerocopy_manifest(manifest_text: &str) -> Result<bool, toml::de::Error> {
    let manifest = toml::from_str::<Value>(manifest_text)?;
    Ok(manifest
        .as_table()
        .and_then(|t| t.get("package"))
        .and_then(Value::as_table)
        .and_then(|p| p.get("name"))
        .and_then(Value::as_str)
        == Some("zerocopy"))
}

fn find_zerocopy_manifest_in(base_dir: &Path) -> Result<(PathBuf, String), Error> {
    let local = base_dir.join("Cargo.toml");
    match fs::read_to_string(&local) {
        Ok(text) => {
            let is_zc = is_zerocopy_manifest(&text).map_err(|err| {
                Error::Manifest(format!("Failed to parse {}: {err}", local.display()))
            })?;
            if is_zc {
                return Ok((local, text));
            }
        }
        Err(err) if err.kind() == io::ErrorKind::NotFound => {}
        Err(err) => {
            return Err(Error::Manifest(format!("Failed to read {}: {err}", local.display())));
        }
    }

    let nested = base_dir.join("zerocopy/Cargo.toml");
    match fs::read_to_string(&nested) {
        Ok(text) => {
            let is_zc = is_zerocopy_manifest(&text).map_err(|err| {
                Error::Manifest(format!("Failed to parse {}: {err}", nested.display()))
            })?;
            if is_zc {
                return Ok((nested, text));
            }
            Err(Error::Manifest(format!(
                "Found {} but `[package].name` is not \"zerocopy\"",
                nested.display()
            )))
        }
        Err(err) if err.kind() == io::ErrorKind::NotFound => Err(Error::Manifest(format!(
            "Could not locate zerocopy's Cargo.toml from {} (checked Cargo.toml and zerocopy/Cargo.toml)",
            base_dir.display()
        ))),
        Err(err) => Err(Error::Manifest(format!("Failed to read {}: {err}", nested.display()))),
    }
}

pub(super) fn get_toolchain_versions_in(base_dir: &Path) -> Result<Versions, Error> {
    let (path, text) = find_zerocopy_manifest_in(base_dir)?;
    Versions::parse(&text, &path)
}

pub(super) fn get_toolchain_versions() -> Result<Versions, Error> {
    let cwd = env::current_dir().map_err(|err| {
        Error::Manifest(format!("Failed to determine current working directory: {err}"))
    })?;
    get_toolchain_versions_in(&cwd)
}

pub(super) fn is_truthy_env_value(value: Option<&str>) -> bool {
    value.is_some_and(|raw| {
        let trimmed = raw.trim();
        !trimmed.is_empty() && trimmed != "0" && !trimmed.eq_ignore_ascii_case("false")
    })
}

pub(super) fn env_is_truthy(name: &str) -> bool {
    is_truthy_env_value(env::var(name).ok().as_deref())
}

pub(super) fn env_is_non_empty(name: &str) -> bool {
    env::var_os(name).is_some_and(|v| !v.is_empty())
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
    if env_is_non_empty("GITHUB_RUN_ID") {
        eprintln!("[cargo-zerocopy] detected GitHub Actions environment; auto-installing without waiting for confirmation");
    } else if env_is_truthy("CARGO_ZEROCOPY_AUTO_INSTALL_TOOLCHAIN") {
        eprintln!("[cargo-zerocopy] detected CARGO_ZEROCOPY_AUTO_INSTALL_TOOLCHAIN environment variable; auto-installing without waiting for confirmation");
    } else {
        eprintln!("[cargo-zerocopy] set CARGO_ZEROCOPY_AUTO_INSTALL_TOOLCHAIN=1 to always install toolchains and targets without prompting");
        loop {
            eprint!("[cargo-zerocopy] {prompt} (y/n)? ");
            io::stderr().flush().unwrap();
            let mut line = String::new();
            let n = io::stdin().lock().read_line(&mut line).unwrap();
            if n == 0 {
                eprintln!("[cargo-zerocopy] stdin closed while waiting for confirmation; aborting");
                process::exit(1);
            }
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

pub(super) fn install_toolchain_or_exit(versions: &Versions, name: &str) -> Result<(), Error> {
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

pub(super) fn install_targets_or_exit(version: &str, targets: &[String]) -> Result<(), Error> {
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
