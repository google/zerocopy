// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Enforces repository Cargo workspace containment, `Cargo.lock` provenance,
//! and `trusted/root-manifest.sha256` verification ([`check_cargo_boundary`]).
//! A separate check, [`verify_bundled_resources`], verifies canonical-source
//! bundle invariants (`build.rs` generation inputs, provenance inventory, and
//! embedded `bundled_theory.json` parity).

use std::{
    collections::{BTreeMap, BTreeSet},
    fs, io,
    path::{Component, Path},
};

use cargo_anneal::{
    EMBEDDED_BUNDLE_SOURCES, EMBEDDED_CORRESPONDENCE_PROVENANCE_JSON, EMBEDDED_THEORY_BUNDLE_JSON,
    Failure, SafeFs,
    bundle::{
        BundleError, LEGACY_BUNDLE_DESTINATION, LEGACY_THEORY_BUNDLE_DESTINATION,
        render_bundled_resources_parts, render_bundled_theory, validate_bundle_source,
    },
    is_clean_relative_path, is_sha256_hex, regular, sha256_file,
};
use serde::Deserialize;

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
        let mut out: Vec<(String, Option<&toml::Value>)> =
            self.deps.sections().into_iter().map(|(s, v)| (s.to_string(), v)).collect();
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
    publish: Option<toml::Value>,
    #[serde(default)]
    workspace: Option<toml::Value>,
}

#[derive(Deserialize)]
struct MemberTarget {
    #[serde(default)]
    path: Option<toml::Value>,
    #[serde(default, rename = "proc-macro")]
    proc_macro: Option<toml::Value>,
    #[serde(default, rename = "proc_macro")]
    proc_macro_underscore: Option<toml::Value>,
    #[serde(default, rename = "crate-type")]
    crate_type: Option<toml::Value>,
    #[serde(default, rename = "crate_type")]
    crate_type_underscore: Option<toml::Value>,
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
            ("dev_dependencies", self.dev_dependencies_underscore.as_ref()),
            ("build-dependencies", self.build_dependencies.as_ref()),
            ("build_dependencies", self.build_dependencies_underscore.as_ref()),
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
    match fs::symlink_metadata(&manifest_path) {
        Ok(meta) => {
            if meta.file_type().is_symlink() || !meta.file_type().is_file() {
                return Err(Failure::new(
                    1,
                    phase,
                    format!("expected a regular file: {}", manifest_path.display()),
                ));
            }
        }
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(()),
        Err(e) => {
            return Err(Failure::new(
                2,
                phase,
                format!("cannot inspect root-manifest.sha256: {e}"),
            ));
        }
    }
    let manifest_text = SafeFs::read_regular_string_capped(&manifest_path, 4 * 1024 * 1024, phase)
        .map_err(|e| Failure::new(1, phase, e.message))?;
    let mut seen_paths = BTreeSet::new();
    for line in
        manifest_text.lines().map(str::trim).filter(|l| !l.is_empty() && !l.starts_with('#'))
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

/// Verify that `trusted/cargo-anneal/build.rs`,
/// `trusted/cargo-anneal/src/trusted_bundle.rs`,
/// `trusted/cargo-anneal/src/theory_bundle.rs`, `theory/bundle-manifest.json`,
/// and every canonical source in [`cargo_anneal::bundle::TRUSTED_BUNDLE_SOURCES`],
/// [`cargo_anneal::bundle::THEORY_BUNDLE_MANIFEST`], and
/// [`cargo_anneal::bundle::PROVENANCE_SOURCES`] are regular files under
/// regular directories, that legacy checked-in `src/bundled_resources.rs`,
/// `src/bundled_theory.json`, and transient `packaged/` staging directories
/// are absent, and that canonical bundle rendering matches `cargo-anneal`'s
/// compiled-in [`EMBEDDED_BUNDLE_SOURCES`],
/// [`EMBEDDED_CORRESPONDENCE_PROVENANCE_JSON`], and
/// [`EMBEDDED_THEORY_BUNDLE_JSON`] byte-for-byte.
pub fn verify_bundled_resources(checkout: &Path) -> Result<(), Failure> {
    let phase = "bundle-manifest";
    validate_bundle_source(checkout, "trusted/cargo-anneal/build.rs")
        .map_err(map_bundle_error)?;
    validate_bundle_source(checkout, "trusted/cargo-anneal/src/trusted_bundle.rs")
        .map_err(map_bundle_error)?;
    validate_bundle_source(checkout, "trusted/cargo-anneal/src/theory_bundle.rs")
        .map_err(map_bundle_error)?;
    for (label, rel) in [
        ("bundled_resources.rs", LEGACY_BUNDLE_DESTINATION),
        ("bundled_theory.json", LEGACY_THEORY_BUNDLE_DESTINATION),
    ] {
        let legacy_destination = checkout.join(rel);
        match fs::symlink_metadata(&legacy_destination) {
            Ok(_) => {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "legacy checked-in {label} must be absent: {}",
                        legacy_destination.display()
                    ),
                ));
            }
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => {}
            Err(err) => {
                return Err(Failure::operational(
                    phase,
                    format!("cannot inspect {}: {err}", legacy_destination.display()),
                ));
            }
        }
    }

    let expected = render_bundled_resources_parts(checkout).map_err(map_bundle_error)?;
    if expected.entries.len() != EMBEDDED_BUNDLE_SOURCES.len() {
        return Err(Failure::policy(
            phase,
            format!(
                "embedded cargo-anneal BUNDLE entry count ({}) differs from canonical checkout \
                 sources ({}); rebuild cargo-anneal and anneal-audit",
                EMBEDDED_BUNDLE_SOURCES.len(),
                expected.entries.len(),
            ),
        ));
    }
    for ((exp_path, exp_src), (emb_path, emb_src)) in
        expected.entries.iter().zip(EMBEDDED_BUNDLE_SOURCES.iter())
    {
        if exp_path != emb_path || exp_src.as_str() != *emb_src {
            return Err(Failure::policy(
                phase,
                format!(
                    "embedded cargo-anneal BUNDLE entry {exp_path} differs from canonical \
                     checkout sources; rebuild cargo-anneal and anneal-audit"
                ),
            ));
        }
    }
    if expected.provenance_json != EMBEDDED_CORRESPONDENCE_PROVENANCE_JSON {
        return Err(Failure::policy(
            phase,
            "embedded cargo-anneal CORRESPONDENCE_PROVENANCE_JSON differs from canonical \
             checkout sources; rebuild cargo-anneal and anneal-audit",
        ));
    }
    let packaged_dir = checkout.join("trusted/cargo-anneal/packaged");
    match fs::symlink_metadata(&packaged_dir) {
        Ok(_) => {
            return Err(Failure::policy(
                phase,
                format!(
                    "transient packaged/ staging directory must not be checked in: {}",
                    packaged_dir.display()
                ),
            ));
        }
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => {}
        Err(err) => {
            return Err(Failure::operational(
                phase,
                format!("cannot inspect {}: {err}", packaged_dir.display()),
            ));
        }
    }

    let expected_theory = render_bundled_theory(checkout).map_err(map_bundle_error)?;
    if expected_theory != EMBEDDED_THEORY_BUNDLE_JSON {
        return Err(Failure::policy(
            phase,
            "embedded cargo-anneal EMBEDDED_THEORY_BUNDLE_JSON differs from canonical \
             checkout sources; rebuild cargo-anneal and anneal-audit",
        ));
    }
    Ok(())
}

/// Verify that a workspace member target neither declares a `proc-macro`
/// (which executes arbitrary code at compile time) nor escapes its member
/// directory via `..` or an absolute `path`.
fn validate_member_target(
    member: &str,
    section: &str,
    target: &MemberTarget,
) -> Result<(), Failure> {
    let phase = "cargo-boundary";
    for (key, value) in
        [("proc-macro", &target.proc_macro), ("proc_macro", &target.proc_macro_underscore)]
    {
        if let Some(val) = value
            && val.as_bool() != Some(false)
        {
            return Err(Failure::new(
                1,
                phase,
                format!("disallowed proc-macro target ({section}.{key}) in {member}/Cargo.toml"),
            ));
        }
    }
    for (key, value) in
        [("crate-type", &target.crate_type), ("crate_type", &target.crate_type_underscore)]
    {
        if let Some(val) = value {
            let arr = val.as_array().ok_or_else(|| {
                Failure::new(1, phase, format!("invalid {section}.{key} in {member}/Cargo.toml"))
            })?;
            for item in arr {
                let kind = item.as_str().ok_or_else(|| {
                    Failure::new(
                        1,
                        phase,
                        format!("invalid {section}.{key} entry in {member}/Cargo.toml"),
                    )
                })?;
                if kind == "proc-macro" {
                    return Err(Failure::new(
                        1,
                        phase,
                        format!(
                            "disallowed proc-macro crate-type ({section}.{key}) in {member}/Cargo.toml"
                        ),
                    ));
                }
            }
        }
    }

    let Some(path_val) = &target.path else {
        return Ok(());
    };
    let Some(p) = path_val.as_str() else {
        return Err(Failure::new(
            1,
            phase,
            format!("invalid {section}.path in {member}/Cargo.toml"),
        ));
    };
    let path = Path::new(p);
    if path.is_absolute() || path.components().any(|c| matches!(c, Component::ParentDir)) {
        return Err(Failure::new(
            1,
            phase,
            format!("{member} target {section}.path escapes member directory: {p}"),
        ));
    }
    Ok(())
}

/// Two-zone monotonic trust lattice for Cargo workspace members:
/// `Trusted` (rank 0) < `Tests` (rank 1).
///
/// Dependencies may only flow downward or laterally (`zone(dst) <= zone(src)`):
/// `Trusted -> Trusted`, `Tests -> Trusted`, and `Tests -> Tests` (such as
/// shared test infrastructure under `tests/testkit`) are permitted, while
/// `Trusted -> Tests` is rejected across every Cargo dependency table.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum WorkspaceZone {
    /// Production TCB crates under `trusted/` (rank 0).
    Trusted = 0,
    /// Non-shipping test and harness crates under `tests/` (rank 1).
    Tests = 1,
}

fn classify_member_zone(rel_path: &str) -> Result<WorkspaceZone, Failure> {
    if !is_clean_relative_path(rel_path) || rel_path.ends_with('/') || rel_path.contains('\\') {
        return Err(Failure::new(1, "cargo-boundary", format!("unclean member path: {rel_path}")));
    }
    if rel_path.starts_with("trusted/") {
        Ok(WorkspaceZone::Trusted)
    } else if rel_path.starts_with("tests/") {
        Ok(WorkspaceZone::Tests)
    } else {
        Err(Failure::new(
            1,
            "cargo-boundary",
            format!("workspace member outside trusted/ or tests/: {rel_path}"),
        ))
    }
}

/// Validate a single dependency table (`[dependencies]`, `[dev-dependencies]`,
/// `[build-dependencies]`, or `[target.<cfg>.*]`) inside a workspace member's
/// `Cargo.toml`.
fn validate_dep_table(
    checkout_canon: &Path,
    member: &str,
    src_zone: WorkspaceZone,
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
        Failure::new(1, phase, format!("invalid {section} in {member}/Cargo.toml"))
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
            Failure::new(1, phase, format!("{member} path dependency escapes checkout: {dep_path}"))
        })?;
        let rel_str = rel.to_string_lossy().replace('\\', "/");
        // Enforce the two-zone monotonic lattice (`zone(dst) <= zone(src)`):
        // `trusted/* -> trusted/*`, `tests/* -> trusted/*`, and
        // `tests/* -> tests/*` are permitted, while `trusted/* -> tests/*` and
        // targets outside either zone are rejected across all dep tables.
        let dst_zone = classify_member_zone(&rel_str).map_err(|_| {
            Failure::new(
                1,
                phase,
                format!("{member} path dependency points outside trusted/ or tests/: {rel_str}"),
            )
        })?;
        if dst_zone > src_zone {
            return Err(Failure::new(
                1,
                phase,
                format!(
                    "{member} ({src_zone:?}) path dependency violates monotonic boundary targeting {rel_str} ({dst_zone:?})"
                ),
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
    match fs::symlink_metadata(&lock_path) {
        Ok(meta) => {
            if meta.file_type().is_symlink() || !meta.file_type().is_file() {
                return Err(Failure::new(
                    1,
                    phase,
                    format!("expected a regular file: {}", lock_path.display()),
                ));
            }
        }
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(()),
        Err(e) => {
            return Err(Failure::new(2, phase, format!("cannot inspect Cargo.lock: {e}")));
        }
    }
    let lock_text = SafeFs::read_regular_string_capped(&lock_path, 16 * 1024 * 1024, phase)
        .map_err(|e| Failure::new(1, phase, e.message))?;
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
/// present): workspace crates must reside under `trusted/` (production TCB,
/// zone 0) or `tests/` (non-trusted test/harness crates with `publish = false`,
/// zone 1), and every `path` dependency must target a registered workspace
/// member satisfying `zone(dst) <= zone(src)` (enforcing the two-zone monotonic
/// lattice so `tests/` crates may share `tests/` helpers and depend on
/// `trusted/`, while `trusted/` crates may never depend on `tests/`).
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
        Failure::new(1, phase, format!("root Cargo.toml may contain only [workspace]: {e}"))
    })?;
    if root_manifest.workspace.resolver.as_deref() != Some("2") {
        return Err(Failure::new(1, phase, "root [workspace] resolver must be \"2\""));
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
        return Err(Failure::new(1, phase, "trusted/rustc-capture missing from workspace.members"));
    }

    let mut member_pkg_names = BTreeSet::new();
    for member in root_manifest.workspace.members.iter().chain(&root_manifest.workspace.exclude) {
        // Only two workspace zones are permitted (`WorkspaceZone::Trusted = 0 <
        // WorkspaceZone::Tests = 1`). Both zones remain subject to manifest,
        // build-script, and lockfile checks; `validate_dep_table` enforces
        // `zone(dst) <= zone(src)`.
        let src_zone = classify_member_zone(member)?;
        let member_toml_path = checkout.join(member).join("Cargo.toml");
        regular(&member_toml_path, phase)?;
        let member_text = fs::read_to_string(&member_toml_path).map_err(|e| {
            Failure::new(1, phase, format!("malformed member Cargo.toml in {member}: {e}"))
        })?;
        let manifest: MemberCargoManifest = toml::from_str(&member_text).map_err(|e| {
            Failure::new(1, phase, format!("malformed member Cargo.toml in {member}: {e}"))
        })?;
        let pkg_name =
            manifest.package.name.as_deref().filter(|s| !s.is_empty()).ok_or_else(|| {
                Failure::new(1, phase, format!("missing package.name in {member}"))
            })?;
        member_pkg_names.insert(pkg_name.to_string());

        // Non-trusted test crates exist solely to verify the workspace and must
        // opt out of crates.io publication explicitly.
        if src_zone == WorkspaceZone::Tests
            && manifest.package.publish != Some(toml::Value::Boolean(false))
        {
            return Err(Failure::new(
                1,
                phase,
                format!("non-trusted test crate must set publish = false in {member}/Cargo.toml"),
            ));
        }

        if manifest.package.build.is_some() || manifest.package.workspace.is_some() {
            return Err(Failure::new(
                1,
                phase,
                format!("disallowed package.build or package.workspace in {member}/Cargo.toml"),
            ));
        }
        let build_rs_path = checkout.join(member).join("build.rs");
        if member == "trusted/cargo-anneal" {
            match fs::symlink_metadata(&build_rs_path) {
                Ok(meta) if !meta.file_type().is_symlink() && meta.file_type().is_file() => {}
                Ok(_) => {
                    return Err(Failure::policy(
                        phase,
                        format!("build script must be a regular file: {member}/build.rs"),
                    ));
                }
                Err(err) if err.kind() == std::io::ErrorKind::NotFound => {
                    return Err(Failure::policy(
                        phase,
                        format!("missing required build script {member}/build.rs"),
                    ));
                }
                Err(err) => {
                    return Err(Failure::operational(
                        phase,
                        format!("cannot inspect {member}/build.rs: {err}"),
                    ));
                }
            }
        } else if fs::symlink_metadata(&build_rs_path).is_ok() {
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
                src_zone,
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
/// Bundle parity follows `require_mir_wp` because the checked bundles hold
/// `Trusted.MirAst`, `Trusted.MirSemantics`, and `Anneal.MirWp` sources plus
/// SHA-256 digests of the correspondence files: only synthetic unit-test
/// fixtures disable it when substituting stub sources or bypassing embedded
/// parity. `anneal-audit` always enables `require_mir_wp`, so missing
/// `build.rs`, `trusted_bundle.rs`, or `theory_bundle.rs`, reintroduced legacy
/// `src/bundled_resources.rs` or `src/bundled_theory.json`, or drifted
/// canonical sources fail closed.
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn non_notfound_metadata_errors_on_manifest_and_lock_are_operational() {
        let dir = tempfile::tempdir().unwrap();
        let blocked_dir = dir.path().join("blocked");
        fs::create_dir_all(&blocked_dir).unwrap();
        fs::write(blocked_dir.join("trusted"), b"not-a-directory").unwrap();

        let err_manifest = verify_root_manifest_sha256(&blocked_dir).unwrap_err();
        assert_eq!(err_manifest.code, 2, "unexpected manifest error: {err_manifest}");
        assert!(
            err_manifest.message.contains("cannot inspect root-manifest.sha256"),
            "unexpected manifest message: {err_manifest}"
        );

        let not_a_checkout_dir = dir.path().join("checkout_file");
        fs::write(&not_a_checkout_dir, b"not-a-directory").unwrap();
        let err_lock = verify_cargo_lock(&not_a_checkout_dir, &BTreeSet::new()).unwrap_err();
        assert_eq!(err_lock.code, 2, "unexpected lock error: {err_lock}");
        assert!(
            err_lock.message.contains("cannot inspect Cargo.lock"),
            "unexpected lock message: {err_lock}"
        );
    }
}
