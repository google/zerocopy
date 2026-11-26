// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Defines the canonical Pass 1 `theory/` bundle manifest, validation, and
//! deterministic JSON rendering shared between `build.rs`, `bundle.rs`,
//! `regenerate_bundle`, and `anneal-audit`.

use std::{
    collections::BTreeSet,
    fmt::Write as _,
    fs, io,
    path::{Component, Path, PathBuf},
};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use super::trusted_bundle::{
    BundleError, CURRENT_MIR_AST_WIRE_VERSION, LOCKED_LEAN_TOOLCHAIN, is_anneal_workspace,
    render_bundled_resources_parts, sha256_bytes, validate_bundle_source,
    validate_destination_path, validate_parent_directories,
};

/// Names the repository-relative path of the sorted, SHA-256-pinned manifest
/// enumerating bundled Pass 1 `theory/Anneal/**/*.lean` proof libraries.
pub const THEORY_BUNDLE_MANIFEST: &str = "theory/bundle-manifest.json";

/// Names the manifest filename inside an external `--theory-dir` directory.
pub const EXTERNAL_THEORY_MANIFEST_FILENAME: &str = "bundle-manifest.json";

/// Names the legacy checked-in JSON theory bundle path, which must stay absent
/// from clean repository checkouts now that `build.rs` emits into `$OUT_DIR`.
pub const LEGACY_THEORY_BUNDLE_DESTINATION: &str =
    "trusted/cargo-anneal/src/bundled_theory.json";

/// Names the repository-relative path used strictly for transient standalone
/// `.crate` packaging snapshots (`regenerate_bundle --stage-package`).
pub const PACKAGED_THEORY_BUNDLE_DESTINATION: &str =
    "trusted/cargo-anneal/packaged/bundled_theory.json";

/// Names the crate-relative path of the standalone `.crate` theory snapshot
/// inside `cargo-anneal`.
pub const PACKAGED_THEORY_BUNDLE_CRATE_REL: &str = "packaged/bundled_theory.json";

pub(crate) const REQUIRED_THEORY_BUNDLE_PATH: &str = "theory/Anneal/MirWp.lean";

pub(crate) fn is_lean_ident(s: &str) -> bool {
    let mut chars = s.chars();
    chars.next().is_some_and(|first| first.is_ascii_alphabetic())
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

pub(crate) fn is_clean_relative_path(rel: &str) -> bool {
    let mut comps = Path::new(rel).components();
    comps.clone().next().is_some() && comps.all(|c| matches!(c, Component::Normal(_)))
}

fn is_lowercase_sha256_hex(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'))
}

fn feed_len_str(h: &mut Sha256, s: &str) {
    h.update((s.len() as u64).to_le_bytes());
    h.update(s.as_bytes());
}

/// Compute the canonical `0`-TCB `theory/` Merkle root (`theory_merkle_root`)
/// over strictly sorted [`TheoryBundleEntry`] records.
pub fn compute_theory_merkle_root(entries: &[TheoryBundleEntry]) -> String {
    let mut h = Sha256::new();
    h.update(b"anneal-theory-merkle-v1\0");
    h.update((entries.len() as u64).to_le_bytes());
    for entry in entries {
        feed_len_str(&mut h, &entry.path);
        feed_len_str(&mut h, &entry.sha256);
    }
    let mut hex = String::with_capacity(64);
    for byte in h.finalize() {
        let _ = write!(&mut hex, "{byte:02x}");
    }
    hex
}

/// Describes one SHA-256-pinned entry in [`THEORY_BUNDLE_MANIFEST`].
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct TheoryBundleEntry {
    /// Clean repository-relative path under `theory/Anneal/` ending in `.lean`.
    pub path: String,
    /// Lowercase 64-character hex SHA-256 digest of the file's UTF-8 bytes.
    pub sha256: String,
}

/// Represents the validated contents of [`THEORY_BUNDLE_MANIFEST`].
///
/// `schema_version = 2` carries fast-fail compatibility headers
/// (`lean_toolchain`, `compatible_trusted_merkle_roots`,
/// `min_mir_ast_wire_version`, `theory_merkle_root`) so an external
/// `--theory-dir` or `--theory-archive` fails closed in `<1 ms` on Ring-0
/// `Trusted/` or toolchain skew rather than mid-elaboration. Version `1`
/// omits those optional headers for backward compatibility in legacy synthetic
/// unit fixtures.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct TheoryBundleManifest {
    /// Manifest format version (`1` or `2`; external `--theory-dir` needs `2`).
    pub schema_version: u32,
    /// Pinned Lean toolchain identifier (`schema_version = 2`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub lean_toolchain: Option<String>,
    /// Allowed Ring-0 `Trusted/` Merkle roots (`schema_version = 2`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub compatible_trusted_merkle_roots: Option<Vec<String>>,
    /// Minimum `MirAst` wire schema version required (`schema_version = 2`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub min_mir_ast_wire_version: Option<u32>,
    /// Canonical Merkle digest over `modules` (`schema_version = 2`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub theory_merkle_root: Option<String>,
    /// Strictly lexicographically sorted, duplicate-free list of bundled
    /// `theory/Anneal/**/*.lean` modules.
    pub modules: Vec<TheoryBundleEntry>,
}

/// Holds one embedded or externally loaded `theory/` source module.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct BundledTheoryModule {
    /// Clean repository-relative path under `theory/Anneal/` ending in `.lean`.
    pub path: String,
    /// Lowercase 64-character hex SHA-256 digest of `content.as_bytes()`.
    pub sha256: String,
    /// Exact UTF-8 source bytes of the `theory/` module.
    pub content: String,
}

/// Holds the parsed, self-verified contents of `$OUT_DIR/bundled_theory.json`
/// (or an externally loaded `--theory-dir` / `--theory-archive` bundle).
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct BundledTheory {
    /// Bundle format version (`1` or `2`).
    pub schema_version: u32,
    /// Lowercase 64-character hex SHA-256 digest of the canonical
    /// [`THEORY_BUNDLE_MANIFEST`] file bytes used to render this bundle.
    pub manifest_sha256: String,
    /// Canonical Merkle root over `modules`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub theory_merkle_root: Option<String>,
    /// Pinned Lean toolchain identifier from a `schema_version = 2` manifest.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub lean_toolchain: Option<String>,
    /// Allowed Ring-0 `Trusted/` Merkle roots from a v2 manifest.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub compatible_trusted_merkle_roots: Option<Vec<String>>,
    /// Minimum `MirAst` wire schema version from a `schema_version = 2`
    /// manifest.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub min_mir_ast_wire_version: Option<u32>,
    /// Strictly lexicographically sorted, duplicate-free list of
    /// `theory/Anneal/**/*.lean` modules.
    pub modules: Vec<BundledTheoryModule>,
}

/// Prepare and validate [`PACKAGED_THEORY_BUNDLE_DESTINATION`] under `root`.
///
/// Validates that every existing parent component of
/// [`PACKAGED_THEORY_BUNDLE_DESTINATION`] under `root` is a regular directory
/// (not a symlink), creates `trusted/cargo-anneal/packaged` if absent, and
/// validates that [`PACKAGED_THEORY_BUNDLE_DESTINATION`] itself, if present,
/// is a regular file.
pub fn prepare_packaged_theory_destination(
    root: &Path,
) -> Result<(PathBuf, Option<fs::Permissions>), BundleError> {
    let rel = Path::new(PACKAGED_THEORY_BUNDLE_DESTINATION);
    if let Some(parent) = rel.parent() {
        let pkg_dir = root.join(parent);
        if let Err(err) = fs::symlink_metadata(&pkg_dir)
            && err.kind() == io::ErrorKind::NotFound
        {
            validate_parent_directories(root, parent, "bundle parent")?;
            fs::create_dir(&pkg_dir).map_err(BundleError::Io)?;
        }
    }
    validate_destination_path(root, PACKAGED_THEORY_BUNDLE_DESTINATION)
}

fn validate_theory_module_path(path: &str) -> Result<(), BundleError> {
    if !is_clean_relative_path(path) {
        return Err(BundleError::Policy(format!(
            "invalid relative theory bundle path: {path}"
        )));
    }
    let Some(rest) = path.strip_prefix("theory/") else {
        return Err(BundleError::Policy(format!(
            "theory bundle path must reside under theory/Anneal/: {path}"
        )));
    };
    let Some(stem) = rest.strip_suffix(".lean") else {
        return Err(BundleError::Policy(format!(
            "theory bundle path must end in .lean: {path}"
        )));
    };
    let components: Vec<&str> = stem.split('/').collect();
    if components.len() < 2
        || components[0] != "Anneal"
        || !components.iter().copied().all(is_lean_ident)
    {
        return Err(BundleError::Policy(format!(
            "theory bundle path must name a module under theory/Anneal/: {path}"
        )));
    }
    Ok(())
}

fn validate_theory_path_sequence<'a, I>(paths: I, label: &str) -> Result<(), BundleError>
where
    I: IntoIterator<Item = &'a str>,
{
    let mut seen = BTreeSet::new();
    let mut prev: Option<&str> = None;
    let mut has_required = false;
    let mut count = 0usize;
    for path in paths {
        count += 1;
        validate_theory_module_path(path)?;
        if !seen.insert(path) {
            return Err(BundleError::Policy(format!(
                "duplicate theory bundle path in {label}: {path}"
            )));
        }
        if let Some(prev_path) = prev
            && path < prev_path
        {
            return Err(BundleError::Policy(format!(
                "unsorted theory bundle entry in {label}: {path} precedes {prev_path}"
            )));
        }
        if path == REQUIRED_THEORY_BUNDLE_PATH {
            has_required = true;
        }
        prev = Some(path);
    }
    if count == 0 {
        return Err(BundleError::Policy(format!("{label} must list at least one theory module")));
    }
    if !has_required {
        return Err(BundleError::Policy(format!(
            "{label} missing required theory module: {REQUIRED_THEORY_BUNDLE_PATH}"
        )));
    }
    Ok(())
}

/// Parse and structurally validate raw `bundle-manifest.json` bytes,
/// returning `(manifest_sha256, manifest)`.
pub fn parse_theory_bundle_manifest_bytes(
    manifest_bytes: &[u8],
    label: &str,
) -> Result<(String, TheoryBundleManifest), BundleError> {
    let manifest_sha256 = sha256_bytes(manifest_bytes);
    let manifest: TheoryBundleManifest = serde_json::from_slice(manifest_bytes)
        .map_err(|err| BundleError::Policy(format!("malformed {label}: {err}")))?;
    validate_theory_path_sequence(manifest.modules.iter().map(|entry| entry.path.as_str()), label)?;
    for entry in &manifest.modules {
        if !is_lowercase_sha256_hex(&entry.sha256) {
            return Err(BundleError::Policy(format!(
                "invalid lowercase SHA-256 in {label} for {}",
                entry.path
            )));
        }
    }
    let computed_merkle = compute_theory_merkle_root(&manifest.modules);
    match manifest.schema_version {
        1 => {
            if manifest.lean_toolchain.is_some()
                || manifest.compatible_trusted_merkle_roots.is_some()
                || manifest.min_mir_ast_wire_version.is_some()
                || manifest.theory_merkle_root.is_some()
            {
                return Err(BundleError::Policy(format!(
                    "schema_version 1 in {label} must not include v2 compatibility headers"
                )));
            }
        }
        2 => {
            let tc = manifest.lean_toolchain.as_deref().unwrap_or("");
            if tc.trim().is_empty() {
                return Err(BundleError::Policy(format!(
                    "missing or empty lean_toolchain in {label} (schema_version 2)"
                )));
            }
            let Some(ref roots) = manifest.compatible_trusted_merkle_roots else {
                return Err(BundleError::Policy(format!(
                    "missing compatible_trusted_merkle_roots in {label} (schema_version 2)"
                )));
            };
            if roots.is_empty() {
                return Err(BundleError::Policy(format!(
                    "compatible_trusted_merkle_roots in {label} must list at least one root"
                )));
            }
            let mut prev_root: Option<&str> = None;
            for root_hex in roots {
                if !is_lowercase_sha256_hex(root_hex) {
                    return Err(BundleError::Policy(format!(
                        "invalid lowercase SHA-256 in compatible_trusted_merkle_roots of {label}: {root_hex}"
                    )));
                }
                if let Some(prev) = prev_root
                    && root_hex.as_str() <= prev
                {
                    return Err(BundleError::Policy(format!(
                        "compatible_trusted_merkle_roots in {label} must be strictly sorted and duplicate-free"
                    )));
                }
                prev_root = Some(root_hex.as_str());
            }
            let Some(min_wire) = manifest.min_mir_ast_wire_version else {
                return Err(BundleError::Policy(format!(
                    "missing min_mir_ast_wire_version in {label} (schema_version 2)"
                )));
            };
            if min_wire == 0 {
                return Err(BundleError::Policy(format!(
                    "min_mir_ast_wire_version in {label} must be >= 1"
                )));
            }
            let Some(ref declared_merkle) = manifest.theory_merkle_root else {
                return Err(BundleError::Policy(format!(
                    "missing theory_merkle_root in {label} (schema_version 2)"
                )));
            };
            if !is_lowercase_sha256_hex(declared_merkle) {
                return Err(BundleError::Policy(format!(
                    "invalid lowercase SHA-256 theory_merkle_root in {label}"
                )));
            }
            if *declared_merkle != computed_merkle {
                return Err(BundleError::Policy(format!(
                    "theory_merkle_root mismatch in {label}: expected {declared_merkle}, computed {computed_merkle}"
                )));
            }
        }
        other => {
            return Err(BundleError::Policy(format!(
                "unsupported schema_version {other} in {label}"
            )));
        }
    }
    Ok((manifest_sha256, manifest))
}

/// Fail closed unless `manifest` is compatible with the binary's locked
/// `expected_lean_toolchain`, `expected_trusted_merkle_root`, and
/// `current_mir_ast_wire_version`.
///
/// When `require_v2` is `true` (all external `--theory-dir` /
/// `--theory-archive` loads), `schema_version = 1` manifests without
/// compatibility headers are rejected outright.
pub fn validate_theory_compatibility(
    manifest: &TheoryBundleManifest,
    label: &str,
    expected_lean_toolchain: &str,
    expected_trusted_merkle_root: &str,
    current_mir_ast_wire_version: u32,
    require_v2: bool,
) -> Result<(), BundleError> {
    if require_v2 && manifest.schema_version != 2 {
        return Err(BundleError::Policy(format!(
            "external theory manifest {label} must declare schema_version 2 (got {})",
            manifest.schema_version
        )));
    }
    if let Some(ref tc) = manifest.lean_toolchain
        && tc != expected_lean_toolchain
    {
        return Err(BundleError::Policy(format!(
            "theory manifest {label} targets lean_toolchain {tc:?}, incompatible with locked {expected_lean_toolchain:?}"
        )));
    }
    if let Some(min_wire) = manifest.min_mir_ast_wire_version
        && min_wire > current_mir_ast_wire_version
    {
        return Err(BundleError::Policy(format!(
            "theory manifest {label} requires min_mir_ast_wire_version {min_wire}, but embedded Trusted/MirAst wire version is {current_mir_ast_wire_version}"
        )));
    }
    if let Some(ref roots) = manifest.compatible_trusted_merkle_roots
        && !roots.iter().any(|r| r == expected_trusted_merkle_root)
    {
        return Err(BundleError::Policy(format!(
            "theory manifest {label} is incompatible with embedded Ring-0 Trusted/ Merkle root {expected_trusted_merkle_root} (manifest allows {roots:?})"
        )));
    }
    Ok(())
}

/// Load and strictly validate [`THEORY_BUNDLE_MANIFEST`] under `root`,
/// returning `(manifest_sha256, manifest)`.
pub fn load_theory_bundle_manifest(
    root: &Path,
) -> Result<(String, TheoryBundleManifest), BundleError> {
    let manifest_path = validate_bundle_source(root, THEORY_BUNDLE_MANIFEST)?;
    let manifest_bytes = fs::read(manifest_path).map_err(BundleError::Io)?;
    parse_theory_bundle_manifest_bytes(&manifest_bytes, THEORY_BUNDLE_MANIFEST)
}

/// Parse and self-verify a serialized [`BundledTheory`] JSON payload.
pub fn parse_bundled_theory(raw: &str) -> Result<BundledTheory, BundleError> {
    let parsed: BundledTheory = serde_json::from_str(raw).map_err(|err| {
        BundleError::Policy(format!("malformed bundled_theory.json: {err}"))
    })?;
    if !matches!(parsed.schema_version, 1 | 2) {
        return Err(BundleError::Policy(format!(
            "unsupported schema_version {} in bundled_theory.json",
            parsed.schema_version
        )));
    }
    if !is_lowercase_sha256_hex(&parsed.manifest_sha256) {
        return Err(BundleError::Policy(
            "invalid manifest_sha256 in bundled_theory.json".to_owned(),
        ));
    }
    validate_theory_path_sequence(
        parsed.modules.iter().map(|entry| entry.path.as_str()),
        "bundled_theory.json",
    )?;
    let mut entries = Vec::with_capacity(parsed.modules.len());
    for entry in &parsed.modules {
        if !is_lowercase_sha256_hex(&entry.sha256) {
            return Err(BundleError::Policy(format!(
                "invalid lowercase SHA-256 in bundled_theory.json for {}",
                entry.path
            )));
        }
        let actual = sha256_bytes(entry.content.as_bytes());
        if actual != entry.sha256 {
            return Err(BundleError::Policy(format!(
                "embedded theory bundle SHA-256 mismatch for {}: expected {}, got {actual}",
                entry.path, entry.sha256
            )));
        }
        entries.push(TheoryBundleEntry { path: entry.path.clone(), sha256: entry.sha256.clone() });
    }
    let computed_merkle = compute_theory_merkle_root(&entries);
    if let Some(ref declared) = parsed.theory_merkle_root
        && *declared != computed_merkle
    {
        return Err(BundleError::Policy(format!(
            "theory_merkle_root mismatch in bundled_theory.json: expected {declared}, computed {computed_merkle}"
        )));
    }
    if parsed.schema_version == 2 {
        let synthetic_manifest = TheoryBundleManifest {
            schema_version: 2,
            lean_toolchain: parsed.lean_toolchain.clone(),
            compatible_trusted_merkle_roots: parsed.compatible_trusted_merkle_roots.clone(),
            min_mir_ast_wire_version: parsed.min_mir_ast_wire_version,
            theory_merkle_root: parsed.theory_merkle_root.clone(),
            modules: entries,
        };
        let manifest_bytes = serde_json::to_vec(&synthetic_manifest)
            .map_err(|e| BundleError::Policy(format!("cannot encode manifest check: {e}")))?;
        parse_theory_bundle_manifest_bytes(&manifest_bytes, "bundled_theory.json")?;
    }
    Ok(parsed)
}

fn render_bundled_theory_from_manifest(
    root: &Path,
    manifest_sha256: String,
    manifest: TheoryBundleManifest,
) -> Result<String, BundleError> {
    if manifest.schema_version == 2
        && let Ok(trusted_parts) = render_bundled_resources_parts(root)
    {
        validate_theory_compatibility(
            &manifest,
            THEORY_BUNDLE_MANIFEST,
            LOCKED_LEAN_TOOLCHAIN,
            &trusted_parts.trusted_merkle_root,
            CURRENT_MIR_AST_WIRE_VERSION,
            /*require_v2=*/ true,
        )?;
    }
    let computed_merkle = compute_theory_merkle_root(&manifest.modules);
    let mut modules = Vec::with_capacity(manifest.modules.len());
    for entry in manifest.modules {
        let source_path = validate_bundle_source(root, &entry.path)?;
        let content = fs::read_to_string(source_path).map_err(BundleError::Io)?;
        let actual_sha = sha256_bytes(content.as_bytes());
        if actual_sha != entry.sha256 {
            return Err(BundleError::Policy(format!(
                "theory bundle manifest SHA-256 mismatch for {}: expected {}, got {actual_sha}",
                entry.path, entry.sha256
            )));
        }
        modules.push(BundledTheoryModule {
            path: entry.path,
            sha256: actual_sha,
            content,
        });
    }
    let payload = BundledTheory {
        schema_version: manifest.schema_version,
        manifest_sha256,
        theory_merkle_root: if manifest.schema_version == 2 { Some(computed_merkle) } else { None },
        lean_toolchain: manifest.lean_toolchain,
        compatible_trusted_merkle_roots: manifest.compatible_trusted_merkle_roots,
        min_mir_ast_wire_version: manifest.min_mir_ast_wire_version,
        modules,
    };
    let mut rendered = serde_json::to_string_pretty(&payload).map_err(|err| {
        BundleError::Policy(format!("failed to serialize bundled_theory.json: {err}"))
    })?;
    rendered.push('\n');
    Ok(rendered)
}

/// Render the exact expected contents of `bundled_theory.json` (generated into
/// `$OUT_DIR/bundled_theory.json` by `build.rs` or staged for standalone
/// `.crate` packaging) from [`THEORY_BUNDLE_MANIFEST`] and the canonical
/// regular `theory/` source files under `root`, failing closed on any missing
/// file, symlink, invalid path, unsorted/duplicate manifest entry, or SHA-256
/// mismatch.
pub fn render_bundled_theory(root: &Path) -> Result<String, BundleError> {
    let (manifest_sha256, manifest) = load_theory_bundle_manifest(root)?;
    render_bundled_theory_from_manifest(root, manifest_sha256, manifest)
}

/// Output of [`resolve_build_script_theory_bundle`]: the Cargo
/// `rerun-if-changed` paths to emit and the deterministic JSON to write to
/// `$OUT_DIR/bundled_theory.json`.
// Consumed by `build.rs` (via `#[path]`) and unit tests in this module.
#[allow(dead_code)]
#[derive(Debug, PartialEq, Eq)]
pub struct TheoryBuildScriptPlan {
    /// Paths to emit as `cargo:rerun-if-changed=<path>` directives.
    pub rerun_if_changed: Vec<PathBuf>,
    /// Deterministic contents of `$OUT_DIR/bundled_theory.json`.
    pub rendered_json: String,
}

/// Resolve workspace-vs-standalone mode, fail-closed theory bundle checks, and
/// Cargo `rerun-if-changed` paths for `trusted/cargo-anneal/build.rs`.
#[allow(dead_code)]
pub fn resolve_build_script_theory_bundle(
    manifest_dir: &Path,
) -> Result<TheoryBuildScriptPlan, BundleError> {
    if fs::symlink_metadata(manifest_dir.join("src/bundled_theory.json")).is_ok() {
        return Err(BundleError::Policy(
            "legacy checked-in src/bundled_theory.json is forbidden; \
             build.rs generates $OUT_DIR/bundled_theory.json"
                .to_owned(),
        ));
    }

    let workspace_root = manifest_dir.join("../..");
    let in_workspace = is_anneal_workspace(manifest_dir, &workspace_root);
    let packaged_exists = fs::symlink_metadata(manifest_dir.join("packaged")).is_ok();

    let mut rerun_if_changed = vec![
        PathBuf::from("build.rs"),
        PathBuf::from("src/theory_bundle.rs"),
        PathBuf::from("src"),
    ];

    // Only watch `.` in workspace mode when `packaged/` does not yet exist;
    // standalone crate builds place `target/` inside the package root, where
    // watching `.` would force rebuilds on every invocation.
    if packaged_exists {
        rerun_if_changed.push(PathBuf::from("packaged"));
        rerun_if_changed.push(PathBuf::from(PACKAGED_THEORY_BUNDLE_CRATE_REL));
    } else if in_workspace {
        rerun_if_changed.push(PathBuf::from("."));
    }

    if in_workspace {
        rerun_if_changed.push(workspace_root.join(THEORY_BUNDLE_MANIFEST));
        let (manifest_sha256, manifest) = load_theory_bundle_manifest(&workspace_root)?;
        for entry in &manifest.modules {
            rerun_if_changed.push(workspace_root.join(&entry.path));
        }
        let rendered_json =
            render_bundled_theory_from_manifest(&workspace_root, manifest_sha256, manifest)?;

        if packaged_exists {
            let (pkg_path, perms) =
                validate_destination_path(manifest_dir, PACKAGED_THEORY_BUNDLE_CRATE_REL)?;
            if perms.is_none() {
                return Err(BundleError::Policy(format!(
                    "packaged/ directory exists without {PACKAGED_THEORY_BUNDLE_CRATE_REL}; \
                     remove trusted/cargo-anneal/packaged first (for example: \
                     rm -rf trusted/cargo-anneal/packaged)"
                )));
            }
            let staged = fs::read(&pkg_path).map_err(BundleError::Io)?;
            if staged != rendered_json.as_bytes() {
                return Err(BundleError::Policy(format!(
                    "{} is stale relative to canonical workspace sources; \
                     remove trusted/cargo-anneal/packaged first \
                     (cargo run -p cargo-anneal --example regenerate_bundle \
                     cannot run while stale packaged/ exists), then re-stage \
                     with --stage-package if publishing",
                    pkg_path.display()
                )));
            }
        }

        Ok(TheoryBuildScriptPlan { rerun_if_changed, rendered_json })
    } else {
        let (pkg_path, perms) =
            validate_destination_path(manifest_dir, PACKAGED_THEORY_BUNDLE_CRATE_REL)?;
        if perms.is_none() {
            return Err(BundleError::Policy(format!(
                "missing {} for standalone cargo-anneal crate build",
                pkg_path.display()
            )));
        }
        let rendered_json = fs::read_to_string(&pkg_path).map_err(BundleError::Io)?;
        parse_bundled_theory(&rendered_json)?;
        Ok(TheoryBuildScriptPlan { rerun_if_changed, rendered_json })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn seed_synthetic_workspace_fixture(dest: &Path) -> PathBuf {
        let manifest_dir = dest.join("trusted/cargo-anneal");
        fs::create_dir_all(manifest_dir.join("src")).unwrap();
        let trusted_root = dest.join("trusted/lean/Trusted.lean");
        fs::create_dir_all(trusted_root.parent().unwrap()).unwrap();
        fs::write(&trusted_root, b"-- synthetic trusted root\n").unwrap();

        let theory_sources = ["theory/Anneal/MirWp.lean", "theory/Anneal/NatBitwise.lean"];
        let mut entries = Vec::new();
        for rel in theory_sources {
            let dst = dest.join(rel);
            fs::create_dir_all(dst.parent().unwrap()).unwrap();
            let content = format!("-- synthetic theory fixture for {rel}\n");
            fs::write(&dst, content.as_bytes()).unwrap();
            entries.push(TheoryBundleEntry {
                path: rel.to_owned(),
                sha256: sha256_bytes(content.as_bytes()),
            });
        }
        let manifest = TheoryBundleManifest {
            schema_version: 1,
            lean_toolchain: None,
            compatible_trusted_merkle_roots: None,
            min_mir_ast_wire_version: None,
            theory_merkle_root: None,
            modules: entries,
        };
        let manifest_path = dest.join(THEORY_BUNDLE_MANIFEST);
        fs::create_dir_all(manifest_path.parent().unwrap()).unwrap();
        fs::write(
            &manifest_path,
            format!("{}\n", serde_json::to_string_pretty(&manifest).unwrap()),
        )
        .unwrap();
        manifest_dir
    }

    #[test]
    fn build_script_workspace_mode_and_fail_closed_packaged_guards() {
        let tmp = tempfile::tempdir().unwrap();
        let workspace_root = tmp.path().join("anneal");
        let manifest_dir = seed_synthetic_workspace_fixture(&workspace_root);

        // Clean workspace: enters workspace mode and watches `.` plus manifest
        // and listed theory modules.
        let plan = resolve_build_script_theory_bundle(&manifest_dir).unwrap();
        assert!(plan.rerun_if_changed.contains(&PathBuf::from("build.rs")));
        assert!(plan.rerun_if_changed.contains(&PathBuf::from("src/theory_bundle.rs")));
        assert!(plan.rerun_if_changed.contains(&PathBuf::from("src")));
        assert!(plan.rerun_if_changed.contains(&PathBuf::from(".")));
        assert!(!plan.rerun_if_changed.contains(&PathBuf::from("packaged")));
        let expected_ws_root = manifest_dir.join("../..");
        assert!(plan.rerun_if_changed.contains(&expected_ws_root.join(THEORY_BUNDLE_MANIFEST)));
        assert!(plan.rerun_if_changed.contains(&expected_ws_root.join("theory/Anneal/MirWp.lean")));
        assert!(
            plan.rerun_if_changed.contains(&expected_ws_root.join("theory/Anneal/NatBitwise.lean"))
        );
        assert_eq!(plan.rendered_json, render_bundled_theory(&workspace_root).unwrap());

        // Reintroduced legacy src/bundled_theory.json fails closed.
        let legacy = manifest_dir.join("src/bundled_theory.json");
        fs::write(&legacy, b"{}\n").unwrap();
        let err = resolve_build_script_theory_bundle(&manifest_dir).unwrap_err();
        assert!(err.to_string().contains("legacy checked-in src/bundled_theory.json"), "{err}");
        fs::remove_file(&legacy).unwrap();

        // Empty packaged/ directory fails closed with removal guidance.
        let packaged_dir = manifest_dir.join("packaged");
        fs::create_dir(&packaged_dir).unwrap();
        let err = resolve_build_script_theory_bundle(&manifest_dir).unwrap_err();
        assert!(
            err.to_string().contains("packaged/ directory exists without")
                && err.to_string().contains("rm -rf trusted/cargo-anneal/packaged"),
            "{err}"
        );

        // Stale packaged/bundled_theory.json fails closed with removal advice.
        let pkg_file = manifest_dir.join(PACKAGED_THEORY_BUNDLE_CRATE_REL);
        fs::write(&pkg_file, b"{}\n").unwrap();
        let err = resolve_build_script_theory_bundle(&manifest_dir).unwrap_err();
        assert!(
            err.to_string().contains("is stale relative to canonical workspace sources")
                && err.to_string().contains("remove trusted/cargo-anneal/packaged first"),
            "{err}"
        );

        // Symlinked `packaged/bundled_theory.json` fails closed in workspace
        // mode.
        #[cfg(unix)]
        {
            let outside = tmp.path().join("outside-theory.json");
            fs::write(&outside, plan.rendered_json.as_bytes()).unwrap();
            fs::remove_file(&pkg_file).unwrap();
            std::os::unix::fs::symlink(&outside, &pkg_file).unwrap();
            let err = resolve_build_script_theory_bundle(&manifest_dir).unwrap_err();
            assert!(err.to_string().contains("regular file"), "{err}");
            fs::remove_file(&pkg_file).unwrap();
        }

        // Matching staged snapshot succeeds and watches `packaged` (not `.`).
        fs::write(&pkg_file, plan.rendered_json.as_bytes()).unwrap();
        let staged_plan = resolve_build_script_theory_bundle(&manifest_dir).unwrap();
        assert!(!staged_plan.rerun_if_changed.contains(&PathBuf::from(".")));
        assert!(staged_plan.rerun_if_changed.contains(&PathBuf::from("packaged")));
        assert!(
            staged_plan.rerun_if_changed.contains(&PathBuf::from(PACKAGED_THEORY_BUNDLE_CRATE_REL))
        );
        assert_eq!(staged_plan.rendered_json, plan.rendered_json);
    }

    #[test]
    fn build_script_standalone_mode_omits_dot_watch_and_fails_closed() {
        let tmp = tempfile::tempdir().unwrap();
        let ws_root = tmp.path().join("seed-ws");
        seed_synthetic_workspace_fixture(&ws_root);
        let valid_json = render_bundled_theory(&ws_root).unwrap();
        let valid = parse_bundled_theory(&valid_json).unwrap();

        // Even if the unpacked directory happens to end in
        // `trusted/cargo-anneal`, the absence of canonical TCB Lean roots keeps
        // it in standalone mode.
        let manifest_dir = tmp.path().join("unpacked/trusted/cargo-anneal");
        fs::create_dir_all(manifest_dir.join("src")).unwrap();
        assert!(!is_anneal_workspace(&manifest_dir, &manifest_dir.join("../..")));

        // Legacy checked-in src/bundled_theory.json fails closed in standalone
        // mode too.
        let legacy = manifest_dir.join("src/bundled_theory.json");
        fs::write(&legacy, valid_json.as_bytes()).unwrap();
        let err = resolve_build_script_theory_bundle(&manifest_dir).unwrap_err();
        assert!(err.to_string().contains("legacy checked-in src/bundled_theory.json"), "{err}");
        fs::remove_file(&legacy).unwrap();

        // Missing packaged/ directory fails closed.
        let err = resolve_build_script_theory_bundle(&manifest_dir).unwrap_err();
        assert!(err.to_string().contains("bundle parent must be a regular directory"), "{err}");

        // Empty packaged/ directory (missing snapshot) fails closed.
        let packaged_dir = manifest_dir.join("packaged");
        fs::create_dir(&packaged_dir).unwrap();
        let err = resolve_build_script_theory_bundle(&manifest_dir).unwrap_err();
        assert!(err.to_string().contains("missing"), "{err}");

        // Malformed JSON and tampered payloads fail closed via
        // `parse_bundled_theory`.
        let pkg_file = manifest_dir.join(PACKAGED_THEORY_BUNDLE_CRATE_REL);
        fs::write(&pkg_file, b"{not json\n").unwrap();
        let err = resolve_build_script_theory_bundle(&manifest_dir).unwrap_err();
        assert!(err.to_string().contains("malformed bundled_theory.json"), "{err}");

        let mut tampered = valid.clone();
        tampered.modules[0].content.push_str("-- tampered\n");
        fs::write(&pkg_file, serde_json::to_string(&tampered).unwrap().as_bytes()).unwrap();
        let err = resolve_build_script_theory_bundle(&manifest_dir).unwrap_err();
        assert!(err.to_string().contains("SHA-256 mismatch"), "{err}");

        let mut missing_required = valid;
        missing_required.modules.retain(|m| m.path != REQUIRED_THEORY_BUNDLE_PATH);
        fs::write(&pkg_file, serde_json::to_string(&missing_required).unwrap().as_bytes()).unwrap();
        let err = resolve_build_script_theory_bundle(&manifest_dir).unwrap_err();
        assert!(err.to_string().contains("missing required theory module"), "{err}");

        // Valid standalone snapshot succeeds and MUST NOT emit `.` so in-place
        // builds with a crate-local `target/` remain fresh.
        fs::write(&pkg_file, valid_json.as_bytes()).unwrap();
        let plan = resolve_build_script_theory_bundle(&manifest_dir).unwrap();
        assert!(!plan.rerun_if_changed.contains(&PathBuf::from(".")));
        assert!(plan.rerun_if_changed.contains(&PathBuf::from("packaged")));
        assert!(plan.rerun_if_changed.contains(&PathBuf::from(PACKAGED_THEORY_BUNDLE_CRATE_REL)));
        assert_eq!(plan.rendered_json, valid_json);

        // Symlinked packaged/bundled_theory.json and symlinked packaged/ dir
        // fail closed.
        #[cfg(unix)]
        {
            let outside = tmp.path().join("outside.json");
            fs::write(&outside, valid_json.as_bytes()).unwrap();
            fs::remove_file(&pkg_file).unwrap();
            std::os::unix::fs::symlink(&outside, &pkg_file).unwrap();
            let err = resolve_build_script_theory_bundle(&manifest_dir).unwrap_err();
            assert!(err.to_string().contains("regular file"), "{err}");
            fs::remove_file(&pkg_file).unwrap();

            let outside_dir = tmp.path().join("outside-packaged");
            fs::create_dir(&outside_dir).unwrap();
            fs::write(outside_dir.join("bundled_theory.json"), valid_json.as_bytes()).unwrap();
            fs::remove_dir(&packaged_dir).unwrap();
            std::os::unix::fs::symlink(&outside_dir, &packaged_dir).unwrap();
            let err = resolve_build_script_theory_bundle(&manifest_dir).unwrap_err();
            assert!(err.to_string().contains("regular directory"), "{err}");
        }
    }
}
