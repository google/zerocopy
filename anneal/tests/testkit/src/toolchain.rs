// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Canonical toolchain coordinate resolution for workspace and installed tests.
//!
//! Separating [`ToolchainMode::WorkspaceBuild`] from
//! [`ToolchainMode::InstalledBundle`] ensures installed-smoke environment
//! overrides (such as `ANNEAL_TEST_CARGO_ANNEAL`) never silently steer local
//! `cargo test` runs away from the freshly compiled workspace binaries.

use std::ffi::{OsStr, OsString};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::TestResult;

/// Explicit execution mode governing tool binary and library resolution.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ToolchainMode {
    /// Resolve workspace-built `*-test-bin` shims (or explicit
    /// `ANNEAL_CLI`/`ANNEAL_CAPTURE`/`ANNEAL_AUDITOR` overrides) paired with
    /// pinned Lean and Rust sysroot directories. Never reads
    /// `ANNEAL_TEST_CARGO_ANNEAL`.
    WorkspaceBuild {
        cli_bin: Option<PathBuf>,
        capture_bin: Option<PathBuf>,
        auditor_bin: Option<PathBuf>,
    },
    /// Exercise an installed `exocrate` bundle strictly outside the source
    /// checkout using `install_root` and optional explicit installed tool
    /// binaries (`ANNEAL_TEST_CARGO_ANNEAL` / `ANNEAL_TEST_AUDITOR`).
    InstalledBundle {
        install_root: PathBuf,
        cli_bin: Option<PathBuf>,
        auditor_bin: Option<PathBuf>,
    },
}

/// Immutable, canonicalized tool coordinates shared across test cases.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ToolchainEnv {
    pub cli: Option<PathBuf>,
    pub capture: Option<PathBuf>,
    pub auditor: Option<PathBuf>,
    pub lean: PathBuf,
    pub lean_bin_dir: PathBuf,
    pub sysroot: PathBuf,
    /// `true` when `lean_bin_dir` bundles `leanexport`, `nanoda_bin`, and
    /// `con-ron` for multi-kernel NDJSON quorum verification.
    pub has_ndjson_quorum_tools: bool,
}

impl ToolchainEnv {
    /// Resolve canonical tool paths from the current process environment under
    /// `mode`.
    pub fn resolve(mode: ToolchainMode) -> TestResult<Self> {
        Self::resolve_with_env(mode, |key| std::env::var_os(key))
    }

    /// Resolve canonical tool paths using a caller-supplied environment lookup
    /// closure so mode isolation can be unit-tested without mutating global
    /// process state.
    pub fn resolve_with_env(
        mode: ToolchainMode,
        get_env: impl Fn(&str) -> Option<OsString>,
    ) -> TestResult<Self> {
        let non_empty = |key: &str| -> Option<PathBuf> {
            get_env(key).filter(|v| !v.is_empty()).map(PathBuf::from)
        };

        let (cli, capture, auditor, install_root_for_fallback) = match mode {
            ToolchainMode::WorkspaceBuild {
                cli_bin,
                capture_bin,
                auditor_bin,
            } => {
                let install_root = non_empty("ANNEAL_TEST_INSTALL_ROOT");
                let cli = first_some([
                    non_empty("ANNEAL_CLI"),
                    non_empty("ANNEAL_MVP_CLI"),
                    cli_bin,
                ])
                .map(|p| canonical_file(&p, "cargo-anneal"))
                .transpose()?;
                let capture = first_some([
                    non_empty("ANNEAL_CAPTURE"),
                    non_empty("ANNEAL_MVP_CAPTURE"),
                    capture_bin,
                    cli.as_deref().and_then(sibling_capture_bin),
                    install_root
                        .as_ref()
                        .map(|root| root.join("bin/anneal-rustc-capture")),
                ])
                .map(|p| canonical_file(&p, "anneal-rustc-capture"))
                .transpose()?;
                let auditor =
                    first_some([non_empty("ANNEAL_AUDITOR"), auditor_bin])
                        .map(|p| canonical_file(&p, "anneal-audit"))
                        .transpose()?;
                (cli, capture, auditor, install_root)
            }
            ToolchainMode::InstalledBundle {
                install_root,
                cli_bin,
                auditor_bin,
            } => {
                let canon_root = canonical_dir(&install_root, "install_root")?;
                let cli = first_some([
                    cli_bin,
                    non_empty("ANNEAL_TEST_CARGO_ANNEAL"),
                ])
                .map(|p| canonical_file(&p, "installed cargo-anneal"))
                .transpose()?;
                let capture_candidate =
                    canon_root.join("bin/anneal-rustc-capture");
                let capture = if capture_candidate.exists() {
                    Some(canonical_file(
                        &capture_candidate,
                        "installed anneal-rustc-capture",
                    )?)
                } else {
                    None
                };
                let auditor = first_some([
                    auditor_bin,
                    non_empty("ANNEAL_TEST_AUDITOR"),
                ])
                .map(|p| canonical_file(&p, "installed anneal-audit"))
                .transpose()?;
                (cli, capture, auditor, Some(canon_root))
            }
        };

        let lean = resolve_lean_with_env(&get_env, install_root_for_fallback.as_deref())?;
        let lean_bin_dir = lean
            .parent()
            .ok_or_else(|| {
                format!("lean executable has no parent directory: {}", lean.display())
            })?
            .to_path_buf();
        let has_ndjson_quorum_tools =
            ["leanexport", "nanoda_bin", "con-ron"]
                .into_iter()
                .all(|tool| lean_bin_dir.join(tool).is_file());

        let sysroot = resolve_sysroot_with_env(
            &get_env,
            install_root_for_fallback.as_deref(),
        )?;

        Ok(Self {
            cli,
            capture,
            auditor,
            lean,
            lean_bin_dir,
            sysroot,
            has_ndjson_quorum_tools,
        })
    }

    /// Resolve the `anneal/` workspace root given an `anneal/tests/<crate>`
    /// manifest directory (`CARGO_MANIFEST_DIR`).
    pub fn repo_root_from_manifest(manifest_dir: &Path) -> TestResult<PathBuf> {
        let candidate = manifest_dir
            .parent()
            .and_then(Path::parent)
            .ok_or_else(|| {
                format!(
                    "expected manifest dir under anneal/tests/<crate>: {}",
                    manifest_dir.display()
                )
            })?;
        let canon = canonical_dir(candidate, "anneal repository root")?;
        if !canon.join("Cargo.toml").is_file()
            || !canon.join("trusted/lean/lean-toolchain").is_file()
        {
            return Err(format!(
                "resolved path {} is not an Anneal repository root",
                canon.display()
            ));
        }
        Ok(canon)
    }
}

/// Resolve the pinned Lean executable from environment overrides, installed
/// toolchain cache dirs, or `~/.elan/toolchains/leanprover--lean4---v4.34.1`.
pub fn default_lean_path() -> TestResult<PathBuf> {
    let get_env = |k: &str| std::env::var_os(k);
    resolve_lean_with_env(&get_env, None)
}

/// Resolve the pinned Rust compiler sysroot (`nightly-2026-05-31`) from
/// environment overrides or `rustup`.
pub fn default_rust_sysroot() -> TestResult<PathBuf> {
    let get_env = |k: &str| std::env::var_os(k);
    resolve_sysroot_with_env(&get_env, None)
}

/// Query `lean --print-prefix` and return its canonicalized prefix directory.
pub fn lean_prefix(lean: &Path) -> TestResult<PathBuf> {
    let out = Command::new(lean)
        .arg("--print-prefix")
        .output()
        .map_err(|error| {
            format!("invoke {} --print-prefix: {error}", lean.display())
        })?;
    if !out.status.success() {
        return Err(format!(
            "{} --print-prefix failed ({}): {}",
            lean.display(),
            out.status,
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    let text = String::from_utf8(out.stdout).map_err(|error| {
        format!("lean --print-prefix output is not UTF-8: {error}")
    })?;
    canonical_dir(Path::new(text.trim()), "Lean prefix")
}

/// Construct a `Command` invoking `cargo <subcommand>` with `binary` staged as
/// `cargo-<subcommand>` inside `<workdir>/cargo-home/bin` on `PATH` and
/// `current_dir` set to `workdir`.
pub fn cargo_subcommand_invocation(
    cargo_exe: &Path,
    subcommand: &str,
    binary: &Path,
    workdir: &Path,
) -> TestResult<Command> {
    // Canonicalize both `binary` and `workdir` upfront so relative `binary`
    // symlinks resolve from `<workdir>/cargo-home/bin` and relative `workdir`
    // values in `CARGO_HOME`/`PATH` are never resolved a second time against
    // `.current_dir(workdir)`.
    let canon_binary = canonical_file(binary, "subcommand binary")?;
    let canon_workdir = canonical_dir(workdir, "subcommand workdir")?;
    let cargo_home = canon_workdir.join("cargo-home");
    let cargo_bin = cargo_home.join("bin");
    fs::create_dir_all(&cargo_bin).map_err(|error| {
        format!(
            "create cargo subcommand bin dir {}: {error}",
            cargo_bin.display()
        )
    })?;
    let subcmd = cargo_bin.join(format!(
        "cargo-{subcommand}{}",
        std::env::consts::EXE_SUFFIX
    ));
    #[cfg(unix)]
    {
        let up_to_date = fs::symlink_metadata(&subcmd)
            .ok()
            .filter(|m| m.file_type().is_symlink())
            .and_then(|_| fs::read_link(&subcmd).ok())
            .is_some_and(|target| target == canon_binary);
        if !up_to_date {
            // Stage a sibling symlink and atomically replace `subcmd` so a
            // reused workdir never executes a stale binary target.
            static LINK_SEQ: std::sync::atomic::AtomicUsize =
                std::sync::atomic::AtomicUsize::new(0);
            let seq = LINK_SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            let tmp_link = cargo_bin.join(format!(
                ".cargo-{subcommand}-{}-{seq}.tmp",
                std::process::id()
            ));
            let _ = fs::remove_file(&tmp_link);
            std::os::unix::fs::symlink(&canon_binary, &tmp_link).map_err(
                |error| {
                    format!(
                        "symlink {} -> {}: {error}",
                        tmp_link.display(),
                        canon_binary.display()
                    )
                },
            )?;
            if let Err(error) = fs::rename(&tmp_link, &subcmd) {
                let _ = fs::remove_file(&tmp_link);
                return Err(format!(
                    "replace {} -> {}: {error}",
                    subcmd.display(),
                    canon_binary.display()
                ));
            }
        }
    }
    #[cfg(not(unix))]
    {
        let temporary = tempfile::NamedTempFile::new_in(&cargo_bin).map_err(
            |error| format!("stage {}: {error}", subcmd.display()),
        )?;
        fs::copy(&canon_binary, temporary.path()).map_err(|error| {
            format!(
                "copy {} -> {}: {error}",
                canon_binary.display(),
                subcmd.display()
            )
        })?;
        temporary.persist(&subcmd).map_err(|error| {
            format!("replace {}: {error}", subcmd.display())
        })?;
    }
    let mut paths = vec![cargo_bin];
    if let Some(path) = std::env::var_os("PATH") {
        paths.extend(std::env::split_paths(&path));
    }
    let joined_path = std::env::join_paths(paths).map_err(|error| {
        format!("construct subcommand search path: {error}")
    })?;
    let mut command = Command::new(cargo_exe);
    command
        .arg(subcommand)
        .env("CARGO_HOME", &cargo_home)
        .env("PATH", joined_path)
        .current_dir(&canon_workdir);
    Ok(command)
}

fn resolve_lean_with_env(
    get_env: &impl Fn(&str) -> Option<OsString>,
    explicit_install_root: Option<&Path>,
) -> TestResult<PathBuf> {
    let non_empty = |key: &str| -> Option<PathBuf> {
        get_env(key).filter(|v| !v.is_empty()).map(PathBuf::from)
    };
    if let Some(explicit) =
        first_some([non_empty("ANNEAL_LEAN"), non_empty("ANNEAL_MVP_LEAN")])
    {
        return canonical_file(&explicit, "ANNEAL_LEAN");
    }
    if let Some(root) = explicit_install_root {
        let candidate = root.join("lean/bin/lean");
        if candidate.is_file() {
            return canonical_file(&candidate, "installed lean");
        }
    }
    if let Some(root) = non_empty("ANNEAL_TEST_INSTALL_ROOT") {
        let candidate = root.join("lean/bin/lean");
        if candidate.is_file() {
            return canonical_file(&candidate, "ANNEAL_TEST_INSTALL_ROOT lean");
        }
    }
    if let Some(xdg) = non_empty("XDG_CACHE_HOME")
        && let Some(found) = find_installed_lean(&xdg.join("anneal/toolchain"))
    {
        return canonical_file(&found, "XDG_CACHE_HOME lean");
    }
    if let Some(home) = non_empty("HOME") {
        for rel in [
            ".cache/anneal/toolchain",
            "Library/Caches/anneal/toolchain",
            "anneal/toolchain",
        ] {
            if let Some(found) = find_installed_lean(&home.join(rel)) {
                return canonical_file(&found, "cached lean");
            }
        }
        let elan = home
            .join(".elan/toolchains/leanprover--lean4---v4.34.1/bin/lean");
        if elan.is_file() {
            return canonical_file(&elan, "elan lean v4.34.1");
        }
    }
    Err("cannot find pinned Lean 4.34.1 executable; set ANNEAL_LEAN or install via elan/setup".into())
}

fn resolve_sysroot_with_env(
    get_env: &impl Fn(&str) -> Option<OsString>,
    explicit_install_root: Option<&Path>,
) -> TestResult<PathBuf> {
    let non_empty = |key: &str| -> Option<PathBuf> {
        get_env(key).filter(|v| !v.is_empty()).map(PathBuf::from)
    };
    let raw = first_some([
        non_empty("ANNEAL_SYSROOT"),
        non_empty("ANNEAL_TEST_RUST_SYSROOT"),
        non_empty("ANNEAL_MVP_SYSROOT"),
        explicit_install_root.map(|root| root.join("rust")),
        non_empty("ANNEAL_TEST_INSTALL_ROOT").map(|root| root.join("rust")),
    ]);
    let raw = match raw {
        Some(path) => path,
        None => query_rustup_sysroot("nightly-2026-05-31")?,
    };
    let canon = canonical_dir(&raw, "Rust sysroot")?;
    if !canon.join("lib").is_dir() {
        return Err(format!(
            "missing compiler sysroot lib/ directory under {}; set ANNEAL_SYSROOT",
            canon.display()
        ));
    }
    Ok(canon)
}

fn query_rustup_sysroot(toolchain: &str) -> TestResult<PathBuf> {
    let output = Command::new("rustup")
        .args(["run", toolchain, "rustc", "--print", "sysroot"])
        .output()
        .map_err(|error| {
            format!(
                "invoke rustup for {toolchain} sysroot (or set ANNEAL_SYSROOT): {error}"
            )
        })?;
    if !output.status.success() {
        return Err(format!(
            "cannot find pinned compiler sysroot for {toolchain}; set ANNEAL_SYSROOT:\n{}",
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    let text = String::from_utf8(output.stdout)
        .map_err(|error| format!("rustc sysroot is not valid UTF-8: {error}"))?;
    Ok(PathBuf::from(text.trim()))
}

fn find_installed_lean(toolchain_parent: &Path) -> Option<PathBuf> {
    let mut entries: Vec<PathBuf> = fs::read_dir(toolchain_parent)
        .ok()?
        .filter_map(|e| e.ok().map(|e| e.path()))
        .collect();
    entries.sort();
    entries
        .into_iter()
        .map(|dir| dir.join("lean/bin/lean"))
        .find(|candidate| candidate.is_file())
}

fn sibling_capture_bin(cli_path: &Path) -> Option<PathBuf> {
    ["anneal-rustc-capture", "anneal-rustc-capture-test-bin"]
        .into_iter()
        .map(|name| cli_path.with_file_name(name))
        .find(|candidate| candidate.is_file())
}

fn first_some<T>(candidates: impl IntoIterator<Item = Option<T>>) -> Option<T> {
    candidates.into_iter().flatten().next()
}

fn canonical_file(path: &Path, label: &str) -> TestResult<PathBuf> {
    let canon = fs::canonicalize(path).map_err(|error| {
        format!("cannot resolve {label} at {}: {error}", path.display())
    })?;
    if !canon.is_file() {
        return Err(format!(
            "expected {label} to be a file at {}",
            canon.display()
        ));
    }
    Ok(canon)
}

fn canonical_dir(path: &Path, label: &str) -> TestResult<PathBuf> {
    let canon = fs::canonicalize(path).map_err(|error| {
        format!("cannot resolve {label} at {}: {error}", path.display())
    })?;
    if !canon.is_dir() {
        return Err(format!(
            "expected {label} to be a directory at {}",
            canon.display()
        ));
    }
    Ok(canon)
}

/// Convert a path slice into a UTF-8 `&OsStr` helper (returning a clear error
/// if non-UTF-8).
pub fn path_as_utf8_str<'a>(path: &'a Path, label: &str) -> TestResult<&'a str> {
    path.to_str()
        .ok_or_else(|| format!("{label} path is not valid UTF-8: {}", path.display()))
}

/// Helper converting `&[&str]` arguments into `Vec<&OsStr>`.
pub fn os_args<'a>(args: &[&'a str]) -> Vec<&'a OsStr> {
    args.iter().map(|s| OsStr::new(*s)).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    fn make_fake_toolchain(root: &Path) -> (PathBuf, PathBuf, PathBuf) {
        let lean_bin = root.join("lean/bin");
        let rust_lib = root.join("rust/lib");
        let bin_dir = root.join("bin");
        fs::create_dir_all(&lean_bin).unwrap();
        fs::create_dir_all(&rust_lib).unwrap();
        fs::create_dir_all(&bin_dir).unwrap();
        let lean = lean_bin.join("lean");
        let cli = bin_dir.join("cargo-anneal-test-bin");
        let cap = bin_dir.join("anneal-rustc-capture-test-bin");
        let aud = bin_dir.join("anneal-audit-test-bin");
        for file in [&lean, &cli, &cap, &aud] {
            fs::write(file, b"stub").unwrap();
        }
        (cli, cap, aud)
    }

    #[test]
    fn workspace_build_ignores_installed_smoke_cli_override() {
        let dir = tempfile::tempdir().unwrap();
        let (ws_cli, _ws_cap, ws_aud) = make_fake_toolchain(dir.path());
        let smoke_cli = dir.path().join("bin/installed-smoke-cli");
        fs::write(&smoke_cli, b"smoke").unwrap();

        let env_map = BTreeMap::from([
            ("ANNEAL_TEST_CARGO_ANNEAL", smoke_cli.as_os_str().to_os_string()),
            ("ANNEAL_LEAN", dir.path().join("lean/bin/lean").into_os_string()),
            ("ANNEAL_SYSROOT", dir.path().join("rust").into_os_string()),
        ]);

        let resolved = ToolchainEnv::resolve_with_env(
            ToolchainMode::WorkspaceBuild {
                cli_bin: Some(ws_cli.clone()),
                capture_bin: None,
                auditor_bin: Some(ws_aud.clone()),
            },
            |k| env_map.get(k).cloned(),
        )
        .unwrap();

        assert_eq!(resolved.cli, Some(fs::canonicalize(&ws_cli).unwrap()));
        // Discovered sibling `anneal-rustc-capture-test-bin` automatically.
        assert_eq!(
            resolved.capture,
            Some(fs::canonicalize(dir.path().join("bin/anneal-rustc-capture-test-bin")).unwrap())
        );
        assert_eq!(resolved.auditor, Some(fs::canonicalize(&ws_aud).unwrap()));
        assert!(!resolved.has_ndjson_quorum_tools);
    }

    #[test]
    fn installed_bundle_detects_quorum_tools_when_present() {
        let dir = tempfile::tempdir().unwrap();
        make_fake_toolchain(dir.path());
        for tool in ["leanexport", "nanoda_bin", "con-ron"] {
            fs::write(dir.path().join("lean/bin").join(tool), b"tool").unwrap();
        }
        let installed_cli = dir.path().join("bin/installed-cli");
        fs::write(&installed_cli, b"cli").unwrap();
        let installed_cap = dir.path().join("bin/anneal-rustc-capture");
        fs::write(&installed_cap, b"cap").unwrap();

        let env_map = BTreeMap::from([(
            "ANNEAL_TEST_CARGO_ANNEAL",
            installed_cli.as_os_str().to_os_string(),
        )]);
        let resolved = ToolchainEnv::resolve_with_env(
            ToolchainMode::InstalledBundle {
                install_root: dir.path().to_path_buf(),
                cli_bin: None,
                auditor_bin: None,
            },
            |k| env_map.get(k).cloned(),
        )
        .unwrap();

        assert_eq!(resolved.cli, Some(fs::canonicalize(&installed_cli).unwrap()));
        assert_eq!(
            resolved.capture,
            Some(fs::canonicalize(&installed_cap).unwrap())
        );
        assert!(resolved.has_ndjson_quorum_tools);
    }

    #[test]
    fn cargo_subcommand_invocation_stages_and_updates_subcommand_on_path() {
        let dir = tempfile::tempdir().unwrap();
        let bin_a = dir.path().join("my-tool-test-bin-a");
        let bin_b = dir.path().join("my-tool-test-bin-b");
        fs::write(&bin_a, b"#!/bin/sh\n").unwrap();
        fs::write(&bin_b, b"#!/bin/sh\n").unwrap();
        let cmd = cargo_subcommand_invocation(
            Path::new("cargo"),
            "anneal",
            &bin_a,
            dir.path(),
        )
        .unwrap();
        let staged = dir
            .path()
            .join("cargo-home/bin")
            .join(format!("cargo-anneal{}", std::env::consts::EXE_SUFFIX));
        let canon_dir = fs::canonicalize(dir.path()).unwrap();
        let canon_a = fs::canonicalize(&bin_a).unwrap();
        let canon_b = fs::canonicalize(&bin_b).unwrap();
        assert!(fs::symlink_metadata(&staged).is_ok());
        assert_eq!(cmd.get_current_dir(), Some(canon_dir.as_path()));
        #[cfg(unix)]
        assert_eq!(fs::read_link(&staged).unwrap(), canon_a);

        // Reusing `workdir` with a different binary must update the link
        // rather than silently executing the stale `bin_a`.
        cargo_subcommand_invocation(
            Path::new("cargo"),
            "anneal",
            &bin_b,
            dir.path(),
        )
        .unwrap();
        #[cfg(unix)]
        assert_eq!(fs::read_link(&staged).unwrap(), canon_b);
    }

    fn relative_from_cwd(canon_target: &Path) -> PathBuf {
        let cwd = std::env::current_dir().unwrap();
        let cwd_comps: Vec<_> = cwd.components().collect();
        let tgt_comps: Vec<_> = canon_target.components().collect();
        let common = cwd_comps
            .iter()
            .zip(&tgt_comps)
            .take_while(|(a, b)| a == b)
            .count();
        let mut rel = PathBuf::new();
        for _ in common..cwd_comps.len() {
            rel.push("..");
        }
        for comp in &tgt_comps[common..] {
            rel.push(comp);
        }
        assert!(
            !rel.is_absolute(),
            "expected relative path, got {}",
            rel.display()
        );
        rel
    }

    #[test]
    fn cargo_subcommand_invocation_canonicalizes_relative_binary_and_workdir() {
        let dir = tempfile::tempdir().unwrap();
        let bin = dir.path().join("rel-tool-bin");
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            fs::write(&bin, b"#!/bin/sh\nprintf 'ran-from:%s' \"$CARGO_HOME\"\n")
                .unwrap();
            fs::set_permissions(&bin, fs::Permissions::from_mode(0o755))
                .unwrap();
        }
        #[cfg(not(unix))]
        fs::write(&bin, b"stub").unwrap();

        let workdir = dir.path().join("nested/work");
        fs::create_dir_all(&workdir).unwrap();
        let canon_bin = fs::canonicalize(&bin).unwrap();
        let canon_workdir = fs::canonicalize(&workdir).unwrap();

        // Build relative paths for BOTH `binary` and `workdir` without
        // mutating process-wide `cwd`.
        let rel_bin = relative_from_cwd(&canon_bin);
        let rel_workdir = relative_from_cwd(&canon_workdir);

        #[cfg(unix)]
        let cargo_stub = {
            use std::os::unix::fs::PermissionsExt;
            let stub = dir.path().join("fake-cargo");
            fs::write(&stub, b"#!/bin/sh\nexec \"cargo-$1\"\n").unwrap();
            fs::set_permissions(&stub, fs::Permissions::from_mode(0o755))
                .unwrap();
            fs::canonicalize(&stub).unwrap()
        };
        #[cfg(not(unix))]
        let cargo_stub = PathBuf::from("cargo");

        let mut cmd = cargo_subcommand_invocation(
            &cargo_stub,
            "anneal",
            &rel_bin,
            &rel_workdir,
        )
        .unwrap();

        let expected_cargo_home = canon_workdir.join("cargo-home");
        let expected_cargo_bin = expected_cargo_home.join("bin");
        assert_eq!(cmd.get_current_dir(), Some(canon_workdir.as_path()));
        let env_map: BTreeMap<_, _> = cmd.get_envs().collect();
        assert_eq!(
            env_map.get(OsStr::new("CARGO_HOME")).copied().flatten(),
            Some(expected_cargo_home.as_os_str())
        );
        let path_val = env_map
            .get(OsStr::new("PATH"))
            .copied()
            .flatten()
            .expect("PATH must be set");
        let first_path = std::env::split_paths(path_val).next().unwrap();
        assert_eq!(first_path, expected_cargo_bin);

        let staged = expected_cargo_bin
            .join(format!("cargo-anneal{}", std::env::consts::EXE_SUFFIX));
        assert!(staged.is_file(), "staged symlink must resolve to target");
        #[cfg(unix)]
        {
            assert_eq!(fs::read_link(&staged).unwrap(), canon_bin);
            // Execute `cmd` inside `.current_dir(canon_workdir)` to prove
            // `PATH` and `CARGO_HOME` do not double-resolve `rel_workdir`.
            let out = cmd.output().unwrap();
            assert!(out.status.success(), "{out:?}");
            assert_eq!(
                String::from_utf8_lossy(&out.stdout),
                format!("ran-from:{}", expected_cargo_home.display())
            );
        }
    }
}
