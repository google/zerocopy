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
    EMBEDDED_BUNDLE_SOURCES, EMBEDDED_THEORY_BUNDLE_JSON, Failure, SafeFs,
    bundle::{
        BundleError, LEGACY_BUNDLE_DESTINATION, LEGACY_THEORY_BUNDLE_DESTINATION,
        render_bundled_resources_parts, render_bundled_theory,
        render_correspondence_provenance_from_checkout, validate_bundle_source,
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

/// Parse one checksum entry of `trusted/root-manifest.sha256`, returning its
/// expected digest and covered path.
///
/// The accepted grammar is the one `ci/update_root_manifest.py` accepts and
/// `sha256sum --check` reads: 64 lowercase hex digits, a space, a GNU mode
/// marker (a second space for text mode or `*` for binary mode), and a
/// canonical relative path. A canonical path has no empty, `.`, or `..`
/// component, which matches the updater's `PurePosixPath` round-trip check.
/// The line must not be padded with whitespace or end with a carriage return
/// that `str::lines` left behind. A whitespace-only line is not empty, so it
/// is rejected as an entry, as `sha256sum --check --strict` rejects it.
fn parse_root_manifest_entry(line: &str) -> Option<(&str, &str)> {
    let expected_hex = line.get(..64)?;
    let rest = line.get(64..)?.strip_prefix(' ')?;
    let rel_path = rest.strip_prefix(' ').or_else(|| rest.strip_prefix('*'))?;
    let canonical = rel_path.split('/').all(|component| !matches!(component, "" | "." | ".."));
    (expected_hex.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'))
        && !rel_path.contains(['\r', '\n'])
        && canonical
        && is_clean_relative_path(rel_path))
    .then_some((expected_hex, rel_path))
}

/// Verify `trusted/root-manifest.sha256` when present: every line other than
/// empty lines and `#` comments must be an entry that
/// [`parse_root_manifest_entry`] accepts, name a unique path, and match that
/// path's on-disk SHA-256, and the four root build files (`Cargo.toml`,
/// `Cargo.lock`, `flake.nix`, `flake.lock`) must be covered.
///
/// Returns whether the manifest is present. An absent manifest is accepted
/// here so that synthetic Cargo workspaces can exercise
/// [`check_cargo_boundary`]; [`check_checkout_cargo_hygiene`] turns absence
/// into [`missing_root_manifest_failure`] for repository audits. Reporting
/// presence from the same `symlink_metadata` call that gates verification
/// leaves no window between the two.
fn verify_root_manifest_sha256(checkout: &Path) -> Result<bool, Failure> {
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
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(false),
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
    for line in manifest_text.lines().filter(|l| !l.is_empty()) {
        if line.contains('\r') {
            return Err(Failure::new(
                1,
                phase,
                format!("malformed line in root-manifest.sha256: {line}"),
            ));
        }
        if line.starts_with('#') {
            continue;
        }
        let Some((expected_hex, rel_path)) = parse_root_manifest_entry(line) else {
            return Err(Failure::new(
                1,
                phase,
                format!("malformed line in root-manifest.sha256: {line}"),
            ));
        };
        if !seen_paths.insert(rel_path.to_string()) {
            return Err(Failure::new(
                1,
                phase,
                format!("invalid or duplicate entry in root-manifest.sha256: {line}"),
            ));
        }
        let actual_hex = sha256_file(&checkout.join(rel_path), phase)
            .map_err(|e| Failure::new(1, phase, e.message))?;
        if actual_hex != expected_hex {
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
    Ok(true)
}

/// Report missing `trusted/root-manifest.sha256` (`code == 1`) instead of
/// skipping the root build-file check.
fn missing_root_manifest_failure() -> Failure {
    Failure::new(
        1,
        "cargo-boundary",
        "repository audit requires trusted/root-manifest.sha256, which is missing",
    )
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
/// are absent, that canonical bundle rendering matches `cargo-anneal`'s
/// compiled-in [`EMBEDDED_BUNDLE_SOURCES`] and [`EMBEDDED_THEORY_BUNDLE_JSON`]
/// byte-for-byte, and that the Pass 2 correspondence provenance record (which
/// `cargo-anneal` no longer embeds) renders from the checkout.
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
    render_correspondence_provenance_from_checkout(checkout).map_err(map_bundle_error)?;
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
/// outside `WorkspaceZone::Tools` (which executes arbitrary code at compile
/// time) nor escapes its member directory via `..` or an absolute `path`.
fn validate_member_target(
    member: &str,
    zone: WorkspaceZone,
    section: &str,
    target: &MemberTarget,
) -> Result<(), Failure> {
    let phase = "cargo-boundary";
    if zone != WorkspaceZone::Tools {
        for (key, value) in
            [("proc-macro", &target.proc_macro), ("proc_macro", &target.proc_macro_underscore)]
        {
            if let Some(val) = value
                && val.as_bool() != Some(false)
            {
                return Err(Failure::new(
                    1,
                    phase,
                    format!(
                        "disallowed proc-macro target ({section}.{key}) in {member}/Cargo.toml"
                    ),
                ));
            }
        }
        for (key, value) in
            [("crate-type", &target.crate_type), ("crate_type", &target.crate_type_underscore)]
        {
            if let Some(val) = value {
                let arr = val.as_array().ok_or_else(|| {
                    Failure::new(
                        1,
                        phase,
                        format!("invalid {section}.{key} in {member}/Cargo.toml"),
                    )
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

/// Require every component of the clean relative path `rel` under `checkout`
/// to be a real directory. `what` names the path in diagnostics.
///
/// A regular `Cargo.toml` does not establish where its crate lives: a
/// symlinked directory component would let `trusted/<crate>` resolve outside
/// the checkout or into another zone while its lexical path still passes
/// [`classify_member_zone`].
fn require_real_directory(checkout: &Path, rel: &str, what: &str) -> Result<(), Failure> {
    let phase = "cargo-boundary";
    let mut dir = checkout.to_path_buf();
    let mut prefix = String::new();
    for component in rel.split('/') {
        dir.push(component);
        if !prefix.is_empty() {
            prefix.push('/');
        }
        prefix.push_str(component);
        match fs::symlink_metadata(&dir) {
            Ok(meta) if meta.file_type().is_dir() => {}
            Ok(_) => {
                return Err(Failure::policy(
                    phase,
                    format!("{what} path component is not a real directory: {prefix}"),
                ));
            }
            Err(e) if e.kind() == io::ErrorKind::NotFound => {
                return Err(Failure::policy(phase, format!("missing {what} directory: {prefix}")));
            }
            Err(e) => {
                return Err(Failure::operational(phase, format!("cannot inspect {prefix}: {e}")));
            }
        }
    }
    Ok(())
}

/// Reject any entry under the member directory `root` (labelled `label`)
/// that is neither a real directory nor a regular file, including symlinks.
///
/// Cargo discovers targets under `src/`, `examples/`, `tests/`, and
/// `benches/`, builds explicit target `path`s, and rustc reads module files
/// beside any of them, all following symlinks. [`validate_member_target`]
/// keeps explicit target paths relative and free of `..`, so checking the
/// whole member tree keeps every file Cargo or rustc can reach by those
/// routes physically inside the member directory. Paths written in source
/// code, such as `#[path]` or `include!`, are not checked here.
fn require_regular_tree(root: &Path, label: &str) -> Result<(), Failure> {
    let phase = "cargo-boundary";
    let mut stack = vec![(root.to_path_buf(), label.to_string())];
    while let Some((dir, dir_label)) = stack.pop() {
        let entries = fs::read_dir(&dir)
            .map_err(|e| Failure::operational(phase, format!("cannot read {dir_label}: {e}")))?;
        for entry in entries {
            let entry = entry.map_err(|e| {
                Failure::operational(phase, format!("cannot inspect {dir_label} entry: {e}"))
            })?;
            let entry_label = format!("{dir_label}/{}", entry.file_name().to_string_lossy());
            let file_type = entry.file_type().map_err(|e| {
                Failure::operational(phase, format!("cannot inspect {entry_label}: {e}"))
            })?;
            if file_type.is_dir() {
                stack.push((entry.path(), entry_label));
            } else if !file_type.is_file() {
                return Err(Failure::policy(
                    phase,
                    format!("crate entry is not a regular file or directory: {entry_label}"),
                ));
            }
        }
    }
    Ok(())
}

/// Three-zone monotonic trust lattice for Cargo workspace crates:
/// `Trusted` (rank 0) < `Tests` (rank 1) < `Tools` (rank 2).
///
/// Dependencies may only flow downward or laterally (`zone(dst) <= zone(src)`):
/// `Trusted -> Trusted`, `Tests -> Trusted`, `Tests -> Tests`,
/// `Tools -> Trusted`, `Tools -> Tests`, and `Tools -> Tools` are permitted,
/// while `Trusted -> Tests`, `Trusted -> Tools`, and `Tests -> Tools` are
/// rejected across every Cargo dependency table.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum WorkspaceZone {
    /// Production TCB crates under `trusted/` (rank 0).
    Trusted = 0,
    /// Non-shipping test and harness crates under `tests/` (rank 1).
    Tests = 1,
    /// Untrusted standalone tools under `tools/` (rank 2).
    Tools = 2,
}

fn classify_member_zone(rel_path: &str) -> Result<WorkspaceZone, Failure> {
    if !is_clean_relative_path(rel_path) || rel_path.ends_with('/') || rel_path.contains('\\') {
        return Err(Failure::new(1, "cargo-boundary", format!("unclean member path: {rel_path}")));
    }
    if rel_path.starts_with("trusted/") {
        Ok(WorkspaceZone::Trusted)
    } else if rel_path.starts_with("tests/") {
        Ok(WorkspaceZone::Tests)
    } else if rel_path.starts_with("tools/") {
        Ok(WorkspaceZone::Tools)
    } else {
        Err(Failure::new(
            1,
            "cargo-boundary",
            format!("workspace member outside trusted/, tests/, or tools/: {rel_path}"),
        ))
    }
}

/// Validate a single dependency table (`[dependencies]`, `[dev-dependencies]`,
/// `[build-dependencies]`, or `[target.<cfg>.*]`) inside a workspace member's
/// `Cargo.toml`, returning each validated `path` dependency's
/// checkout-relative crate directory.
fn validate_dep_table(
    checkout_canon: &Path,
    member: &str,
    src_zone: WorkspaceZone,
    member_parent: &Path,
    member_set: &BTreeSet<String>,
    section: &str,
    table_val: Option<&toml::Value>,
) -> Result<Vec<String>, Failure> {
    let phase = "cargo-boundary";
    let mut path_deps = Vec::new();
    let Some(table_val) = table_val else {
        return Ok(path_deps);
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
        // Enforce the three-zone monotonic lattice (`zone(dst) <= zone(src)`):
        // `Trusted -> Tests`, `Trusted -> Tools`, `Tests -> Tools`, and
        // targets outside `trusted/`, `tests/`, or `tools/` are rejected across
        // all dependency tables.
        let dst_zone = classify_member_zone(&rel_str).map_err(|_| {
            Failure::new(
                1,
                phase,
                format!(
                    "{member} path dependency points outside trusted/, tests/, or tools/: {rel_str}"
                ),
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
        path_deps.push(rel_str);
    }
    Ok(path_deps)
}

/// Validate `Cargo.lock`: version 4, every external dependency sourced from
/// `crates.io-index` with a 64-hex SHA-256 checksum, and every source-less
/// package belonging to `member_pkg_names`. When `required` is `true`, a
/// missing `Cargo.lock` fails closed.
fn verify_cargo_lock_with_mode(
    checkout: &Path,
    member_pkg_names: &BTreeSet<String>,
    required: bool,
) -> Result<(), Failure> {
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
        Err(e) if e.kind() == io::ErrorKind::NotFound => {
            if required {
                return Err(Failure::new(
                    1,
                    phase,
                    format!("missing required Cargo.lock in {}", checkout.display()),
                ));
            }
            return Ok(());
        }
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

fn verify_cargo_lock(checkout: &Path, member_pkg_names: &BTreeSet<String>) -> Result<(), Failure> {
    verify_cargo_lock_with_mode(checkout, member_pkg_names, false)
}

/// A member crate manifest that passed [`validate_member_crate`].
struct ValidatedCrate {
    /// The crate's `package.name`.
    pkg_name: String,
    /// Checkout-relative directories of the crate's validated `path`
    /// dependencies, all drawn from the `member_set` it was validated
    /// against.
    path_deps: Vec<String>,
}

/// Reject `[patch]` and `[replace]` in a crate manifest. Cargo applies these
/// tables only from the manifest at a workspace root, but every excluded
/// single crate is its own root, so they are rejected in every member and
/// excluded manifest. Keys are compared after ASCII lowercasing and mapping
/// `_` to `-`, so near-spellings also fail closed.
fn reject_patch_and_replace(member: &str, raw_member: &toml::Table) -> Result<(), Failure> {
    for key in raw_member.keys() {
        let norm = key.to_ascii_lowercase().replace('_', "-");
        if norm == "patch" || norm == "replace" {
            return Err(Failure::new(
                1,
                "cargo-boundary",
                format!("disallowed [{key}] section in {member}/Cargo.toml"),
            ));
        }
    }
    Ok(())
}

/// Collect the `package.name` of every crate in `roots` and of every crate
/// reachable from them through validated `path` dependencies in `crates`.
/// These are the only packages that may appear without a `source` in the
/// `Cargo.lock` that resolves `roots`.
fn local_package_closure<'a>(
    roots: impl IntoIterator<Item = &'a str>,
    crates: &BTreeMap<String, ValidatedCrate>,
) -> Result<BTreeSet<String>, Failure> {
    let mut seen = BTreeSet::new();
    let mut names = BTreeSet::new();
    let mut stack: Vec<&str> = roots.into_iter().collect();
    while let Some(rel) = stack.pop() {
        if !seen.insert(rel) {
            continue;
        }
        // Every `path` dependency was checked against a `member_set` whose
        // entries are all validated, so a miss here is an internal error.
        let krate = crates.get(rel).ok_or_else(|| {
            Failure::new(2, "cargo-boundary", format!("unvalidated crate in path closure: {rel}"))
        })?;
        names.insert(krate.pkg_name.clone());
        stack.extend(krate.path_deps.iter().map(String::as_str));
    }
    Ok(names)
}

/// Validate one member crate manifest against its zone (`Trusted`, `Tests`,
/// or `Tools`) and registered dependency set, returning its `package.name`
/// and validated `path` dependencies.
fn validate_member_crate(
    checkout: &Path,
    checkout_canon: &Path,
    member: &str,
    src_zone: WorkspaceZone,
    member_set: &BTreeSet<String>,
) -> Result<ValidatedCrate, Failure> {
    let phase = "cargo-boundary";
    require_real_directory(checkout, member, "member")?;
    let member_toml_path = checkout.join(member).join("Cargo.toml");
    regular(&member_toml_path, phase)?;
    let member_text = fs::read_to_string(&member_toml_path).map_err(|e| {
        Failure::new(1, phase, format!("malformed member Cargo.toml in {member}: {e}"))
    })?;
    let raw_member: toml::Table = toml::from_str(&member_text).map_err(|e| {
        Failure::new(1, phase, format!("malformed member Cargo.toml in {member}: {e}"))
    })?;
    if raw_member.contains_key("workspace") {
        return Err(Failure::new(
            1,
            phase,
            format!("disallowed [workspace] section in member crate {member}/Cargo.toml"),
        ));
    }
    reject_patch_and_replace(member, &raw_member)?;
    let manifest: MemberCargoManifest = toml::from_str(&member_text).map_err(|e| {
        Failure::new(1, phase, format!("malformed member Cargo.toml in {member}: {e}"))
    })?;
    let pkg_name = manifest
        .package
        .name
        .as_deref()
        .filter(|s| !s.is_empty())
        .ok_or_else(|| Failure::new(1, phase, format!("missing package.name in {member}")))?;

    // Non-trusted crates (`tests/` and `tools/`) must opt out of crates.io
    // publication explicitly.
    if src_zone != WorkspaceZone::Trusted
        && manifest.package.publish != Some(toml::Value::Boolean(false))
    {
        return Err(Failure::new(
            1,
            phase,
            format!(
                "non-trusted {} crate must set publish = false in {member}/Cargo.toml",
                if src_zone == WorkspaceZone::Tests { "test" } else { "tool" }
            ),
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
        return Err(Failure::new(1, phase, format!("disallowed build script {member}/build.rs")));
    }

    for (section, target) in manifest.all_targets() {
        validate_member_target(member, src_zone, section, target)?;
    }
    // `scan_tools_tree` already rejects every symlink under `tools/`.
    if src_zone != WorkspaceZone::Tools {
        require_regular_tree(&checkout.join(member), member)?;
    }

    let member_parent = member_toml_path.parent().unwrap();
    let mut path_deps = Vec::new();
    for (section, tbl) in manifest.all_dep_tables() {
        path_deps.extend(validate_dep_table(
            checkout_canon,
            member,
            src_zone,
            member_parent,
            member_set,
            &section,
            tbl,
        )?);
    }

    Ok(ValidatedCrate { pkg_name: pkg_name.to_string(), path_deps })
}

/// Validate an excluded standalone `[workspace]` under `tools/` (such as
/// `tools/anneal-spec`), enforcing resolver v2, zone-2 member containment,
/// toolchain override absence, and `Cargo.lock` provenance.
fn validate_tools_subworkspace(
    checkout: &Path,
    checkout_canon: &Path,
    sub_rel: &str,
    sub_manifest: &RootCargoManifest,
    registered_tools_manifests: &mut BTreeSet<String>,
    registered_tools_locks: &mut BTreeSet<String>,
) -> Result<(), Failure> {
    let phase = "cargo-boundary";
    let sub_root = checkout.join(sub_rel);
    reject_cargo_toolchain_overrides(&sub_root)?;
    if sub_manifest.workspace.resolver.as_deref() != Some("2") {
        return Err(Failure::new(
            1,
            phase,
            format!("{sub_rel}/Cargo.toml [workspace] resolver must be \"2\""),
        ));
    }
    if !sub_manifest.workspace.exclude.is_empty() {
        return Err(Failure::new(
            1,
            phase,
            format!("{sub_rel}/Cargo.toml must not declare workspace.exclude"),
        ));
    }
    registered_tools_manifests.insert(format!("{sub_rel}/Cargo.toml"));
    registered_tools_locks.insert(format!("{sub_rel}/Cargo.lock"));

    let mut sub_member_paths = Vec::with_capacity(sub_manifest.workspace.members.len());
    let mut sub_member_set = BTreeSet::new();
    for raw_member in &sub_manifest.workspace.members {
        if !is_clean_relative_path(raw_member)
            || raw_member.ends_with('/')
            || raw_member.contains('\\')
        {
            return Err(Failure::new(
                1,
                phase,
                format!("unclean member path in {sub_rel}/Cargo.toml: {raw_member}"),
            ));
        }
        // `sub_rel` is a clean path under `tools/` and `raw_member` is a
        // clean relative path (only normal components), so `full_rel` stays
        // under `sub_rel` and needs no separate zone check.
        let full_rel = format!("{sub_rel}/{raw_member}");
        registered_tools_manifests.insert(format!("{full_rel}/Cargo.toml"));
        sub_member_set.insert(full_rel.clone());
        sub_member_paths.push(full_rel);
    }

    let mut sub_pkg_names = BTreeSet::new();
    for member in &sub_member_paths {
        let krate = validate_member_crate(
            checkout,
            checkout_canon,
            member,
            WorkspaceZone::Tools,
            &sub_member_set,
        )?;
        sub_pkg_names.insert(krate.pkg_name);
    }
    verify_cargo_lock_with_mode(&sub_root, &sub_pkg_names, true)?;
    Ok(())
}

/// Walk `checkout/tools/` (when present) and reject symlinks, nested
/// Cargo/toolchain override entries, or any unregistered `Cargo.toml` /
/// `Cargo.lock`.
fn scan_tools_tree(
    checkout: &Path,
    registered_tools_manifests: &BTreeSet<String>,
    registered_tools_locks: &BTreeSet<String>,
) -> Result<(), Failure> {
    let phase = "cargo-boundary";
    let tools_dir = checkout.join("tools");
    let meta = match fs::symlink_metadata(&tools_dir) {
        Ok(meta) => meta,
        Err(e) if e.kind() == io::ErrorKind::NotFound => return Ok(()),
        Err(e) => {
            return Err(Failure::new(2, phase, format!("cannot inspect tools/: {e}")));
        }
    };
    if meta.file_type().is_symlink() || !meta.is_dir() {
        return Err(Failure::new(1, phase, "tools/ must be a regular directory"));
    }
    let mut stack = vec![tools_dir];
    while let Some(dir) = stack.pop() {
        let entries = fs::read_dir(&dir)
            .map_err(|e| Failure::new(2, phase, format!("cannot read {}: {e}", dir.display())))?;
        for entry in entries {
            let entry = entry
                .map_err(|e| Failure::new(2, phase, format!("cannot inspect tools/ entry: {e}")))?;
            let path = entry.path();
            let md = fs::symlink_metadata(&path).map_err(|e| {
                Failure::new(1, phase, format!("cannot stat {}: {e}", path.display()))
            })?;
            if md.file_type().is_symlink() {
                return Err(Failure::new(
                    1,
                    phase,
                    format!("disallowed symlink under tools/: {}", path.display()),
                ));
            }
            let file_name = entry.file_name();
            let lower = file_name.to_string_lossy().to_ascii_lowercase();
            let rel = path
                .strip_prefix(checkout)
                .map_err(|_| Failure::new(2, phase, "tools/ strip_prefix failed"))?
                .to_string_lossy()
                .replace('\\', "/");
            if lower == ".cargo"
                || lower == ".gitmodules"
                || lower == "rust-toolchain"
                || lower.starts_with("rust-toolchain.")
            {
                return Err(Failure::new(
                    1,
                    phase,
                    format!("forbidden Cargo/toolchain override under tools/: {rel}"),
                ));
            }
            if md.is_dir() {
                stack.push(path);
            } else if lower == "cargo.toml" {
                // Match case-insensitively: on case-insensitive filesystems
                // Cargo may load `cargo.toml` or `CARGO.TOML`, so only the
                // exact registered spelling is admitted.
                if !registered_tools_manifests.contains(&rel) {
                    return Err(Failure::new(
                        1,
                        phase,
                        format!("unregistered Cargo manifest under tools/: {rel}"),
                    ));
                }
            } else if lower == "cargo.lock" && !registered_tools_locks.contains(&rel) {
                return Err(Failure::new(
                    1,
                    phase,
                    format!("unregistered Cargo.lock under tools/: {rel}"),
                ));
            }
        }
    }
    Ok(())
}

/// Verify Cargo workspace DAG containment, root Cargo/toolchain hygiene,
/// `Cargo.lock` dependency provenance, and `trusted/root-manifest.sha256` (when
/// present; [`check_checkout_cargo_hygiene`] also requires it): root workspace
/// members must reside under `trusted/` (production
/// TCB, zone 0) or `tests/` (non-trusted test/harness crates with
/// `publish = false`, zone 1). Crates under `tools/` (untrusted tools with
/// `publish = false`, zone 2, where `proc-macro` targets are permitted) must
/// be listed in `workspace.exclude` so they never build in the root
/// workspace. Every `path` dependency must target a registered crate
/// satisfying `zone(dst) <= zone(src)` (enforcing the three-zone monotonic
/// lattice so `trusted/` crates may never depend on `tests/` or `tools/`, and
/// `tests/` crates may never depend on `tools/`). No member or excluded
/// manifest may declare `[patch]` or `[replace]`. Excluded standalone
/// `[workspace]` tools under `tools/` must pass the same zone-2 crate and
/// `Cargo.lock` checks, and no unregistered `Cargo.toml` or `Cargo.lock` may
/// exist under `tools/`. Each `Cargo.lock` may list without a `source` only
/// the crates it resolves and their transitive `path` dependencies.
///
/// This check reads only Cargo manifests, `Cargo.lock`,
/// `trusted/root-manifest.sha256`, and the root build files that the root
/// manifest pins. Lean bundle parity belongs to [`verify_bundled_resources`],
/// which [`check_checkout_cargo_hygiene`] runs separately.
pub fn check_cargo_boundary(checkout: &Path) -> Result<(), Failure> {
    let _manifest_present = check_cargo_boundary_with_manifest_presence(checkout)?;
    Ok(())
}

/// [`check_cargo_boundary`], also returning whether
/// `trusted/root-manifest.sha256` is present.
fn check_cargo_boundary_with_manifest_presence(checkout: &Path) -> Result<bool, Failure> {
    let phase = "cargo-boundary";
    reject_cargo_toolchain_overrides(checkout)?;
    let root_toml_path = checkout.join("Cargo.toml");
    let capture_toml_path = checkout.join("trusted/rustc-capture/Cargo.toml");
    regular(&root_toml_path, phase)?;
    regular(&capture_toml_path, phase)?;
    let manifest_present = verify_root_manifest_sha256(checkout)?;

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

    let mut member_set: BTreeSet<String> =
        root_manifest.workspace.members.iter().cloned().collect();
    if !member_set.contains("trusted/rustc-capture") {
        return Err(Failure::new(1, phase, "trusted/rustc-capture missing from workspace.members"));
    }

    let mut crate_entries: Vec<(String, WorkspaceZone)> = Vec::new();
    let mut excluded_single_crates: Vec<(String, WorkspaceZone)> = Vec::new();
    let mut registered_tools_manifests = BTreeSet::new();
    let mut registered_tools_locks = BTreeSet::new();
    for member in &root_manifest.workspace.members {
        let src_zone = classify_member_zone(member)?;
        // `validate_member_target` admits proc-macros in `tools/`, so a
        // `tools/` crate must never build as part of the root workspace.
        if src_zone == WorkspaceZone::Tools {
            return Err(Failure::new(
                1,
                phase,
                format!(
                    "tools/ crate must be in workspace.exclude, not workspace.members: {member}"
                ),
            ));
        }
        crate_entries.push((member.clone(), src_zone));
    }
    for excl in &root_manifest.workspace.exclude {
        let excl_zone = classify_member_zone(excl)?;
        require_real_directory(checkout, excl, "excluded crate")?;
        let excl_root = checkout.join(excl);
        let excl_toml_path = excl_root.join("Cargo.toml");
        regular(&excl_toml_path, phase)?;
        let excl_text = fs::read_to_string(&excl_toml_path)
            .map_err(|e| Failure::new(1, phase, format!("malformed Cargo.toml in {excl}: {e}")))?;
        let raw_excl: toml::Table = toml::from_str(&excl_text)
            .map_err(|e| Failure::new(1, phase, format!("malformed Cargo.toml in {excl}: {e}")))?;
        if raw_excl.contains_key("workspace") {
            if excl_zone != WorkspaceZone::Tools {
                return Err(Failure::new(
                    1,
                    phase,
                    format!("disallowed [workspace] in excluded crate outside tools/: {excl}"),
                ));
            }
            let sub_manifest: RootCargoManifest = toml::from_str(&excl_text).map_err(|e| {
                Failure::new(
                    1,
                    phase,
                    format!("{excl}/Cargo.toml may contain only [workspace]: {e}"),
                )
            })?;
            validate_tools_subworkspace(
                checkout,
                &checkout_canon,
                excl,
                &sub_manifest,
                &mut registered_tools_manifests,
                &mut registered_tools_locks,
            )?;
        } else {
            reject_cargo_toolchain_overrides(&excl_root)?;
            if excl_zone == WorkspaceZone::Tools {
                registered_tools_manifests.insert(format!("{excl}/Cargo.toml"));
                registered_tools_locks.insert(format!("{excl}/Cargo.lock"));
            }
            member_set.insert(excl.clone());
            crate_entries.push((excl.clone(), excl_zone));
            excluded_single_crates.push((excl.clone(), excl_zone));
        }
    }

    let mut crates = BTreeMap::new();
    for (member, src_zone) in &crate_entries {
        let krate =
            validate_member_crate(checkout, &checkout_canon, member, *src_zone, &member_set)?;
        crates.insert(member.clone(), krate);
    }

    // Each excluded single crate is its own Cargo root, so its `Cargo.lock`
    // may name without a `source` only itself and its transitive `path`
    // dependencies, never the root workspace's other members.
    for (excl, excl_zone) in &excluded_single_crates {
        let excl_pkg_names = local_package_closure([excl.as_str()], &crates)?;
        verify_cargo_lock_with_mode(
            &checkout.join(excl),
            &excl_pkg_names,
            *excl_zone == WorkspaceZone::Tools,
        )?;
    }

    scan_tools_tree(checkout, &registered_tools_manifests, &registered_tools_locks)?;
    // Likewise, the root `Cargo.lock` admits only root members and their
    // transitive `path` dependencies. No root member is in `tools/`, and the
    // lattice forbids `trusted/` or `tests/` -> `tools/`, so no excluded
    // `tools/` crate name can enter this set.
    let root_pkg_names =
        local_package_closure(root_manifest.workspace.members.iter().map(String::as_str), &crates)?;
    verify_cargo_lock(checkout, &root_pkg_names)?;
    Ok(manifest_present)
}

/// Reject `.cargo*` and `rust-toolchain*` overrides at `checkout`, and run
/// [`check_cargo_boundary`], root-manifest presence enforcement,
/// [`verify_upstream_pin`], and (when `require_mir_wp` is enabled)
/// [`verify_bundled_resources`] whenever any Cargo, root-manifest, or vendored
/// Miri TCB path is present. A checkout with such a path is audited as a
/// repository, so it must carry `trusted/root-manifest.sha256`.
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
        if !check_cargo_boundary_with_manifest_presence(checkout)? {
            return Err(missing_root_manifest_failure());
        }
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

    /// The auditor accepts exactly the entries `ci/update_root_manifest.py`
    /// accepts: lowercase digests, either GNU mode marker, and canonical
    /// relative paths, with no padding or stray carriage return.
    #[test]
    fn root_manifest_entries_follow_the_updater_grammar() {
        let hex = "0123456789abcdef".repeat(4);
        for (line, rel) in [
            (format!("{hex}  Cargo.toml"), "Cargo.toml"),
            (format!("{hex} *Cargo.toml"), "Cargo.toml"),
            (format!("{hex}  trusted/audit/Cargo.toml"), "trusted/audit/Cargo.toml"),
        ] {
            assert_eq!(parse_root_manifest_entry(&line), Some((hex.as_str(), rel)), "{line:?}");
        }
        let upper = hex.to_ascii_uppercase();
        for line in [
            format!("{upper}  Cargo.toml"),
            format!("{}  Cargo.toml", &hex[..63]),
            format!("{hex} Cargo.toml"),
            format!("{hex}\tCargo.toml"),
            format!("{hex} \tCargo.toml"),
            format!("{hex}  "),
            format!(" {hex}  Cargo.toml"),
            format!("{hex}  Cargo.toml\r"),
            format!("{hex}  ./Cargo.toml"),
            format!("{hex}  trusted//audit/Cargo.toml"),
            format!("{hex}  trusted/./audit/Cargo.toml"),
            format!("{hex}  trusted/audit/"),
            format!("{hex}  ../Cargo.toml"),
            format!("{hex}  /Cargo.toml"),
        ] {
            assert_eq!(parse_root_manifest_entry(&line), None, "{line:?}");
        }
    }

    /// `verify_root_manifest_sha256` reports `Ok(false)` for an absent
    /// manifest, which repository audits turn into a policy failure
    /// (`code == 1`), and `Ok(true)` for a present, valid one.
    #[test]
    fn root_manifest_verification_reports_presence() {
        let dir = tempfile::tempdir().unwrap();
        assert!(!verify_root_manifest_sha256(dir.path()).unwrap());
        let err = missing_root_manifest_failure();
        assert_eq!(err.code, 1, "unexpected missing-manifest error: {err}");
        assert!(
            err.message.contains("requires trusted/root-manifest.sha256"),
            "unexpected missing-manifest message: {err}"
        );
        let mut manifest = String::from("# root build files\n");
        for rel in ["Cargo.toml", "Cargo.lock", "flake.nix", "flake.lock"] {
            let path = dir.path().join(rel);
            fs::write(&path, rel.as_bytes()).unwrap();
            let digest = sha256_file(&path, "test").unwrap();
            manifest.push_str(&format!("{digest}  {rel}\n"));
        }
        fs::create_dir_all(dir.path().join("trusted")).unwrap();
        fs::write(dir.path().join("trusted/root-manifest.sha256"), manifest).unwrap();
        assert!(verify_root_manifest_sha256(dir.path()).unwrap());
    }

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

        // `tools/` is optional, but only `NotFound` may skip its scan.
        let err_tools =
            scan_tools_tree(&not_a_checkout_dir, &BTreeSet::new(), &BTreeSet::new()).unwrap_err();
        assert_eq!(err_tools.code, 2, "unexpected tools error: {err_tools}");
        assert!(
            err_tools.message.contains("cannot inspect tools/"),
            "unexpected tools message: {err_tools}"
        );
        scan_tools_tree(&blocked_dir, &BTreeSet::new(), &BTreeSet::new()).unwrap();
    }
}
