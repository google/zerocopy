// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Enforces repository Cargo workspace containment, `Cargo.lock` provenance,
//! and `trusted/root-manifest.sha256` verification ([`check_cargo_boundary`]).
//! A separate check, [`verify_bundled_resources`], verifies embedded
//! `bundled_resources.rs` canonical-source parity.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Component, Path};

use serde::Deserialize;

use cargo_anneal::bundle::{
    BundleError, render_bundled_resources, render_bundled_theory, validate_bundle_destination,
    validate_theory_bundle_destination,
};
use cargo_anneal::{Failure, is_clean_relative_path, is_sha256_hex, regular, sha256_file};

use crate::miri_pin::verify_upstream_pin;

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RootCargoManifest {
    workspace: RootCargoWorkspace,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RootCargoWorkspace {
    members: Vec<String>,
    #[serde(default)]
    exclude: Vec<String>,
    resolver: Option<String>,
}

#[derive(Deserialize)]
struct MemberCargoManifest {
    package: MemberPackage,
    #[serde(default)]
    lib: Option<MemberTarget>,
    #[serde(default)]
    bin: Vec<MemberTarget>,
    #[serde(default)]
    example: Vec<MemberTarget>,
    #[serde(default)]
    test: Vec<MemberTarget>,
    #[serde(default)]
    bench: Vec<MemberTarget>,
    #[serde(flatten)]
    deps: MemberDepTables,
    #[serde(default)]
    target: BTreeMap<String, TargetCfgSection>,
}

impl MemberCargoManifest {
    /// Yield every `(section_label, target)` declared in `[lib]`, `[[bin]]`,
    /// `[[example]]`, `[[test]]`, and `[[bench]]`.
    fn all_targets(&self) -> impl Iterator<Item = (&'static str, &MemberTarget)> {
        self.lib
            .iter()
            .map(|t| ("lib", t))
            .chain(self.bin.iter().map(|t| ("bin", t)))
            .chain(self.example.iter().map(|t| ("example", t)))
            .chain(self.test.iter().map(|t| ("test", t)))
            .chain(self.bench.iter().map(|t| ("bench", t)))
    }

    /// Yield every `(section_label, raw_table_value)` across top-level
    /// dependency tables and `[target.<cfg>.*]` dependency tables.
    fn all_dep_tables(&self) -> Vec<(String, Option<&toml::Value>)> {
        let mut out: Vec<(String, Option<&toml::Value>)> = self
            .deps
            .sections()
            .into_iter()
            .map(|(s, v)| (s.to_string(), v))
            .collect();
        for (cfg_name, cfg_sec) in &self.target {
            for (sec, v) in cfg_sec.deps.sections() {
                out.push((format!("target.{cfg_name}.{sec}"), v));
            }
        }
        out
    }
}

#[derive(Deserialize)]
struct MemberPackage {
    #[serde(default)]
    name: Option<String>,
    #[serde(default)]
    build: Option<toml::Value>,
    #[serde(default)]
    workspace: Option<toml::Value>,
}

#[derive(Deserialize)]
struct MemberTarget {
    #[serde(default)]
    path: Option<toml::Value>,
}

#[derive(Default, Deserialize)]
struct TargetCfgSection {
    #[serde(flatten)]
    deps: MemberDepTables,
}

#[derive(Default, Deserialize)]
struct MemberDepTables {
    #[serde(default)]
    dependencies: Option<toml::Value>,
    #[serde(default, rename = "dev-dependencies")]
    dev_dependencies: Option<toml::Value>,
    #[serde(default, rename = "dev_dependencies")]
    dev_dependencies_underscore: Option<toml::Value>,
    #[serde(default, rename = "build-dependencies")]
    build_dependencies: Option<toml::Value>,
    #[serde(default, rename = "build_dependencies")]
    build_dependencies_underscore: Option<toml::Value>,
}

impl MemberDepTables {
    /// Yield all `(section_label, raw_table_value)` entries present in this
    /// dependency table group.
    fn sections(&self) -> [(&'static str, Option<&toml::Value>); 5] {
        [
            ("dependencies", self.dependencies.as_ref()),
            ("dev-dependencies", self.dev_dependencies.as_ref()),
            (
                "dev_dependencies",
                self.dev_dependencies_underscore.as_ref(),
            ),
            ("build-dependencies", self.build_dependencies.as_ref()),
            (
                "build_dependencies",
                self.build_dependencies_underscore.as_ref(),
            ),
        ]
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct CargoLockFile {
    version: Option<i64>,
    #[serde(default)]
    package: Vec<CargoLockPackage>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct CargoLockPackage {
    name: String,
    #[allow(dead_code)]
    version: String,
    source: Option<String>,
    checksum: Option<String>,
    #[serde(default)]
    #[allow(dead_code)]
    dependencies: Vec<String>,
}

/// Reject `.cargo*`, `rust-toolchain*`, and `.gitmodules` overrides at the
/// repository root (including case-insensitive directory entries).
pub(crate) fn reject_cargo_toolchain_overrides(checkout: &Path) -> Result<(), Failure> {
    let phase = "cargo-boundary";
    for forbidden in [
        ".cargo",
        ".cargo/config",
        ".cargo/config.toml",
        "rust-toolchain",
        "rust-toolchain.toml",
        ".gitmodules",
    ] {
        if fs::symlink_metadata(checkout.join(forbidden)).is_ok() {
            return Err(Failure::new(
                1,
                phase,
                format!("forbidden Cargo/toolchain override at repository root: {forbidden}"),
            ));
        }
    }
    if let Ok(entries) = fs::read_dir(checkout) {
        for entry in entries.flatten() {
            let name = entry.file_name().to_string_lossy().to_ascii_lowercase();
            if name == ".cargo"
                || name == ".gitmodules"
                || name == "rust-toolchain"
                || name.starts_with("rust-toolchain.")
            {
                return Err(Failure::new(
                    1,
                    phase,
                    format!(
                        "forbidden Cargo/toolchain override at repository root: {}",
                        entry.file_name().to_string_lossy()
                    ),
                ));
            }
        }
    }
    Ok(())
}

/// Verify `trusted/root-manifest.sha256` (when present): every non-comment line
/// must name a unique clean relative path whose on-disk SHA-256 matches, and
/// the four root build files (`Cargo.toml`, `Cargo.lock`, `flake.nix`,
/// `flake.lock`) must be covered.
fn verify_root_manifest_sha256(checkout: &Path) -> Result<(), Failure> {
    let phase = "cargo-boundary";
    let manifest_path = checkout.join("trusted/root-manifest.sha256");
    if fs::symlink_metadata(&manifest_path).is_err() {
        return Ok(());
    }
    regular(&manifest_path, phase)?;
    let manifest_text = fs::read_to_string(&manifest_path)
        .map_err(|e| Failure::new(1, phase, format!("cannot read root-manifest.sha256: {e}")))?;
    let mut seen_paths = BTreeSet::new();
    for line in manifest_text
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
    {
        let Some((expected_hex, rel_path)) = line.split_once("  ") else {
            return Err(Failure::new(
                1,
                phase,
                format!("malformed line in root-manifest.sha256: {line}"),
            ));
        };
        if !is_sha256_hex(expected_hex)
            || !is_clean_relative_path(rel_path)
            || !seen_paths.insert(rel_path.to_string())
        {
            return Err(Failure::new(
                1,
                phase,
                format!("invalid or duplicate entry in root-manifest.sha256: {line}"),
            ));
        }
        let actual_hex = sha256_file(&checkout.join(rel_path), phase)
            .map_err(|e| Failure::new(1, phase, e.message))?;
        if !actual_hex.eq_ignore_ascii_case(expected_hex) {
            return Err(Failure::new(
                1,
                phase,
                format!(
                    "root TCB manifest digest mismatch for {rel_path}: expected {expected_hex}, got {actual_hex}"
                ),
            ));
        }
    }
    for required_rel in ["Cargo.toml", "Cargo.lock", "flake.nix", "flake.lock"] {
        if !seen_paths.contains(required_rel) {
            return Err(Failure::new(
                1,
                phase,
                format!("root-manifest.sha256 missing required entry: {required_rel}"),
            ));
        }
    }
    Ok(())
}

fn map_bundle_error(err: BundleError) -> Failure {
    match err {
        BundleError::Policy(msg) => Failure::policy("bundle-manifest", msg),
        BundleError::Io(io_err) => {
            Failure::operational("bundle-manifest", format!("bundle I/O error: {io_err}"))
        }
    }
}

/// Verify that `trusted/cargo-anneal/src/bundled_resources.rs`,
/// `trusted/cargo-anneal/src/bundled_theory.json`, `theory/bundle-manifest.json`,
/// and every canonical source in [`cargo_anneal::bundle::TRUSTED_BUNDLE_SOURCES`],
/// [`cargo_anneal::bundle::THEORY_BUNDLE_MANIFEST`], and
/// [`cargo_anneal::bundle::PROVENANCE_SOURCES`] are regular files under
/// regular directories and match [`render_bundled_resources`] and
/// [`render_bundled_theory`] byte-for-byte.
pub fn verify_bundled_resources(checkout: &Path) -> Result<(), Failure> {
    let phase = "bundle-manifest";
    let (destination, permissions) =
        validate_bundle_destination(checkout).map_err(map_bundle_error)?;
    if permissions.is_none() {
        return Err(Failure::policy(
            phase,
            format!("missing bundled_resources.rs: {}", destination.display()),
        ));
    }
    let expected = render_bundled_resources(checkout).map_err(map_bundle_error)?;
    let actual = fs::read(&destination).map_err(|e| {
        Failure::operational(phase, format!("cannot read {}: {e}", destination.display()))
    })?;
    if actual != expected.as_bytes() {
        return Err(Failure::policy(
            phase,
            format!(
                "{} differs from canonical bundled sources; run regenerate_bundle",
                destination.display()
            ),
        ));
    }

    let (theory_destination, theory_permissions) =
        validate_theory_bundle_destination(checkout).map_err(map_bundle_error)?;
    if theory_permissions.is_none() {
        return Err(Failure::policy(
            phase,
            format!("missing bundled_theory.json: {}", theory_destination.display()),
        ));
    }
    let expected_theory = render_bundled_theory(checkout).map_err(map_bundle_error)?;
    let actual_theory = fs::read(&theory_destination).map_err(|e| {
        Failure::operational(phase, format!("cannot read {}: {e}", theory_destination.display()))
    })?;
    if actual_theory != expected_theory.as_bytes() {
        return Err(Failure::policy(
            phase,
            format!(
                "{} differs from canonical bundled theory sources; run regenerate_bundle",
                theory_destination.display()
            ),
        ));
    }
    Ok(())
}

/// Verify that a relative target path inside a workspace member `Cargo.toml`
/// does not use `..` or an absolute path to escape the member directory.
fn validate_member_target(
    member: &str,
    section: &str,
    target: &MemberTarget,
) -> Result<(), Failure> {
    let Some(path_val) = &target.path else {
        return Ok(());
    };
    let Some(p) = path_val.as_str() else {
        return Err(Failure::new(
            1,
            "cargo-boundary",
            format!("invalid {section}.path in {member}/Cargo.toml"),
        ));
    };
    let path = Path::new(p);
    if path.is_absolute() || path.components().any(|c| matches!(c, Component::ParentDir)) {
        return Err(Failure::new(
            1,
            "cargo-boundary",
            format!("{member} target {section}.path escapes member directory: {p}"),
        ));
    }
    Ok(())
}

/// Validate a single dependency table (`[dependencies]`, `[dev-dependencies]`,
/// `[build-dependencies]`, or `[target.<cfg>.*]`) inside a workspace member's
/// `Cargo.toml`.
fn validate_dep_table(
    checkout_canon: &Path,
    member: &str,
    member_parent: &Path,
    member_set: &BTreeSet<String>,
    section: &str,
    table_val: Option<&toml::Value>,
) -> Result<(), Failure> {
    let phase = "cargo-boundary";
    let Some(table_val) = table_val else {
        return Ok(());
    };
    let table = table_val.as_table().ok_or_else(|| {
        Failure::new(
            1,
            phase,
            format!("invalid {section} in {member}/Cargo.toml"),
        )
    })?;
    for (dep_name, spec) in table {
        let Some(spec_obj) = spec.as_table() else {
            continue;
        };
        if spec_obj.contains_key("git") || spec_obj.contains_key("registry") {
            return Err(Failure::new(
                1,
                phase,
                format!(
                    "disallowed git or custom-registry dependency {dep_name} in {member}/Cargo.toml"
                ),
            ));
        }
        let Some(path_val) = spec_obj.get("path") else {
            continue;
        };
        let Some(dep_path) = path_val.as_str() else {
            return Err(Failure::new(
                1,
                phase,
                format!("non-string path dependency {dep_name} in {member}/Cargo.toml"),
            ));
        };
        let resolved = fs::canonicalize(member_parent.join(dep_path)).map_err(|_| {
            Failure::new(
                1,
                phase,
                format!("{member} path dependency target does not exist: {dep_path}"),
            )
        })?;
        let rel = resolved.strip_prefix(checkout_canon).map_err(|_| {
            Failure::new(
                1,
                phase,
                format!("{member} path dependency escapes checkout: {dep_path}"),
            )
        })?;
        let rel_str = rel.to_string_lossy().replace('\\', "/");
        if !rel_str.starts_with("trusted/") {
            return Err(Failure::new(
                1,
                phase,
                format!("{member} path dependency points outside trusted/: {rel_str}"),
            ));
        }
        if !member_set.contains(&rel_str) {
            return Err(Failure::new(
                1,
                phase,
                format!("{member} path dependency points to non-member crate: {rel_str}"),
            ));
        }
        regular(&resolved.join("Cargo.toml"), phase)?;
    }
    Ok(())
}

/// Validate `Cargo.lock` (when present): version 4, every external dependency
/// sourced from `crates.io-index` with a 64-hex SHA-256 checksum, and every
/// source-less package belonging to `member_pkg_names`.
fn verify_cargo_lock(checkout: &Path, member_pkg_names: &BTreeSet<String>) -> Result<(), Failure> {
    let phase = "cargo-boundary";
    let lock_path = checkout.join("Cargo.lock");
    if fs::symlink_metadata(&lock_path).is_err() {
        return Ok(());
    }
    regular(&lock_path, phase)?;
    let lock_text = fs::read_to_string(&lock_path)
        .map_err(|e| Failure::new(1, phase, format!("cannot read Cargo.lock: {e}")))?;
    let lock_file: CargoLockFile = toml::from_str(&lock_text)
        .map_err(|e| Failure::new(1, phase, format!("malformed Cargo.lock: {e}")))?;
    if lock_file.version != Some(4) {
        return Err(Failure::new(1, phase, "Cargo.lock must have version = 4"));
    }
    for pkg in &lock_file.package {
        let pkg_name = pkg.name.as_str();
        match pkg.source.as_deref() {
            Some("registry+https://github.com/rust-lang/crates.io-index") => {
                if !pkg.checksum.as_deref().is_some_and(is_sha256_hex) {
                    return Err(Failure::new(
                        1,
                        phase,
                        format!("missing or invalid checksum in Cargo.lock for {pkg_name}"),
                    ));
                }
            }
            Some(other_src) => {
                return Err(Failure::new(
                    1,
                    phase,
                    format!(
                        "untrusted dependency source in Cargo.lock for {pkg_name}: {other_src}"
                    ),
                ));
            }
            None => {
                if pkg.checksum.is_some() || !member_pkg_names.contains(pkg_name) {
                    return Err(Failure::new(
                        1,
                        phase,
                        format!("untrusted local package without source in Cargo.lock: {pkg_name}"),
                    ));
                }
            }
        }
    }
    Ok(())
}

/// Verify Cargo workspace DAG containment, root Cargo/toolchain hygiene,
/// `Cargo.lock` dependency provenance, and `trusted/root-manifest.sha256` (when
/// present): all workspace crates must reside under `trusted/`, and no
/// workspace crate may depend on a path outside `workspace.members`.
///
/// This check reads only Cargo manifests, `Cargo.lock`,
/// `trusted/root-manifest.sha256`, and the root build files that the root
/// manifest pins. Lean bundle parity belongs to [`verify_bundled_resources`],
/// which [`check_checkout_cargo_hygiene`] runs separately.
pub fn check_cargo_boundary(checkout: &Path) -> Result<(), Failure> {
    let phase = "cargo-boundary";
    reject_cargo_toolchain_overrides(checkout)?;
    let root_toml_path = checkout.join("Cargo.toml");
    let capture_toml_path = checkout.join("trusted/rustc-capture/Cargo.toml");
    regular(&root_toml_path, phase)?;
    regular(&capture_toml_path, phase)?;
    verify_root_manifest_sha256(checkout)?;

    let root_text = fs::read_to_string(&root_toml_path)
        .map_err(|e| Failure::new(1, phase, format!("malformed Cargo manifest: {e}")))?;
    let root_manifest: RootCargoManifest = toml::from_str(&root_text).map_err(|e| {
        Failure::new(
            1,
            phase,
            format!("root Cargo.toml may contain only [workspace]: {e}"),
        )
    })?;
    if root_manifest.workspace.resolver.as_deref() != Some("2") {
        return Err(Failure::new(
            1,
            phase,
            "root [workspace] resolver must be \"2\"",
        ));
    }

    let checkout_canon = fs::canonicalize(checkout)
        .map_err(|e| Failure::new(2, phase, format!("cannot canonicalize checkout: {e}")))?;

    let member_set: BTreeSet<String> = root_manifest
        .workspace
        .members
        .iter()
        .chain(&root_manifest.workspace.exclude)
        .cloned()
        .collect();
    if !member_set.contains("trusted/rustc-capture") {
        return Err(Failure::new(
            1,
            phase,
            "trusted/rustc-capture missing from workspace.members",
        ));
    }

    let mut member_pkg_names = BTreeSet::new();
    for member in root_manifest
        .workspace
        .members
        .iter()
        .chain(&root_manifest.workspace.exclude)
    {
        if !is_clean_relative_path(member) || !member.starts_with("trusted/") {
            return Err(Failure::new(
                1,
                phase,
                format!("workspace member outside trusted/: {member}"),
            ));
        }
        let member_toml_path = checkout.join(member).join("Cargo.toml");
        regular(&member_toml_path, phase)?;
        let member_text = fs::read_to_string(&member_toml_path).map_err(|e| {
            Failure::new(
                1,
                phase,
                format!("malformed member Cargo.toml in {member}: {e}"),
            )
        })?;
        let manifest: MemberCargoManifest = toml::from_str(&member_text).map_err(|e| {
            Failure::new(
                1,
                phase,
                format!("malformed member Cargo.toml in {member}: {e}"),
            )
        })?;
        let pkg_name = manifest
            .package
            .name
            .as_deref()
            .filter(|s| !s.is_empty())
            .ok_or_else(|| Failure::new(1, phase, format!("missing package.name in {member}")))?;
        member_pkg_names.insert(pkg_name.to_string());

        if manifest.package.build.is_some() || manifest.package.workspace.is_some() {
            return Err(Failure::new(
                1,
                phase,
                format!("disallowed package.build or package.workspace in {member}/Cargo.toml"),
            ));
        }
        if fs::symlink_metadata(checkout.join(member).join("build.rs")).is_ok() {
            return Err(Failure::new(
                1,
                phase,
                format!("disallowed build script {member}/build.rs"),
            ));
        }

        for (section, target) in manifest.all_targets() {
            validate_member_target(member, section, target)?;
        }

        let member_parent = member_toml_path.parent().unwrap();
        for (section, tbl) in manifest.all_dep_tables() {
            validate_dep_table(
                &checkout_canon,
                member,
                member_parent,
                &member_set,
                &section,
                tbl,
            )?;
        }
    }

    verify_cargo_lock(checkout, &member_pkg_names)?;
    Ok(())
}

/// Reject `.cargo*` and `rust-toolchain*` overrides at `checkout`, and run
/// [`check_cargo_boundary`], [`verify_upstream_pin`], and (when
/// `require_mir_wp` is enabled) [`verify_bundled_resources`] whenever any
/// Cargo, root-manifest, or vendored Miri TCB path is present.
///
/// Bundle parity follows `require_mir_wp` because the bundle embeds
/// `Trusted.MirAst`, `Trusted.MirSemantics`, and `Anneal.MirWp`: only
/// synthetic unit-test fixtures disable it, and they omit those sources.
/// `anneal-audit` always runs with `require_mir_wp` enabled, so deleting
/// `bundled_resources.rs` (with or without its generator) fails closed.
pub(crate) fn check_checkout_cargo_hygiene(
    checkout: &Path,
    require_mir_wp: bool,
) -> Result<(), Failure> {
    reject_cargo_toolchain_overrides(checkout)?;
    if [
        "Cargo.toml",
        "Cargo.lock",
        "trusted/root-manifest.sha256",
        "trusted/rustc-capture",
        "vendor",
    ]
    .iter()
    .any(|rel| fs::symlink_metadata(checkout.join(rel)).is_ok())
    {
        check_cargo_boundary(checkout)?;
        verify_upstream_pin(&checkout.join("vendor/lean-miri"))?;
        if require_mir_wp {
            verify_bundled_resources(checkout)?;
        }
    }
    Ok(())
}
