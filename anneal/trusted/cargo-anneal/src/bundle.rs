// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Defines the canonical source inventory and deterministic Rust rendering of
//! the audited resources embedded into `cargo-anneal`.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{self, Write as _};
use std::fs;
use std::io;
use std::path::{Component, Path, PathBuf};

use serde::{Deserialize, Serialize};
use walkdir::WalkDir;

use crate::toolchain::{
    LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256, is_clean_relative_path, is_lean_ident,
    is_sha256_hex, sha256_bytes,
};

/// Lists the canonical repository-relative trusted source files embedded into
/// `cargo-anneal` via [`BUNDLE_DESTINATION`].
///
/// Resource ownership remains explicit so runtime target verification never
/// discovers model, lock, or inspector files from an untrusted checkout.
/// Bundled Pass 1 `theory/` libraries are registered separately in
/// [`THEORY_BUNDLE_MANIFEST`] and embedded as pure UTF-8 JSON data in
/// [`THEORY_BUNDLE_DESTINATION`], keeping `trusted/` registrations decoupled
/// from untrusted proof-library additions.
pub const TRUSTED_BUNDLE_SOURCES: &[&str] = &[
    "trusted/audit/SpecPreflight.lean",
    "trusted/audit/TrustedBoundary.lean",
    "trusted/audit/library-lock.json",
    "trusted/lean/foundation-lock.json",
    "trusted/lean/lean-toolchain",
    "trusted/lean/Trusted.lean",
    "trusted/lean/Trusted/MirAst.lean",
    "trusted/lean/Trusted/MirAst/Body.lean",
    "trusted/lean/Trusted/MirAst/Places.lean",
    "trusted/lean/Trusted/MirAst/Rvalues.lean",
    "trusted/lean/Trusted/MirAst/Statements.lean",
    "trusted/lean/Trusted/MirAst/Terminators.lean",
    "trusted/lean/Trusted/MirAst/Types.lean",
    "trusted/lean/Trusted/MirModel.lean",
    "trusted/lean/Trusted/MirSemantics.lean",
    "trusted/lean/Trusted/MirSemantics/Boundary.lean",
    "trusted/lean/Trusted/MirSemantics/Bytes.lean",
    "trusted/lean/Trusted/MirSemantics/CanaryFixtures.lean",
    "trusted/lean/Trusted/MirSemantics/Enum.lean",
    "trusted/lean/Trusted/MirSemantics/Layout.lean",
    "trusted/lean/Trusted/MirSemantics/Memory.lean",
    "trusted/lean/Trusted/MirSemantics/Ops.lean",
    "trusted/lean/Trusted/MirSemantics/State.lean",
    "trusted/lean/Trusted/MirSemantics/Step.lean",
];

/// Names the repository-relative path of the sorted, SHA-256-pinned manifest
/// enumerating bundled Pass 1 `theory/Anneal/**/*.lean` proof libraries.
pub const THEORY_BUNDLE_MANIFEST: &str = "theory/bundle-manifest.json";

/// Names the repository-relative path of the generated pure-data JSON bundle
/// embedded into `cargo-anneal` via `include_str!` for bundled `theory/`
/// libraries.
pub const THEORY_BUNDLE_DESTINATION: &str = "trusted/cargo-anneal/src/bundled_theory.json";

const REQUIRED_THEORY_BUNDLE_PATH: &str = "theory/Anneal/MirWp.lean";
const EMBEDDED_THEORY_BUNDLE_JSON: &str = include_str!("bundled_theory.json");

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
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct TheoryBundleManifest {
    /// Manifest format version (must be `1`).
    pub schema_version: u32,
    /// Strictly lexicographically sorted, duplicate-free list of bundled
    /// `theory/Anneal/**/*.lean` modules.
    pub modules: Vec<TheoryBundleEntry>,
}

/// Holds one embedded bundled `theory/` source module inside
/// [`THEORY_BUNDLE_DESTINATION`].
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct BundledTheoryModule {
    /// Clean repository-relative path under `theory/Anneal/` ending in `.lean`.
    pub path: String,
    /// Lowercase 64-character hex SHA-256 digest of `content.as_bytes()`.
    pub sha256: String,
    /// Exact UTF-8 source bytes of the bundled `theory/` module.
    pub content: String,
}

/// Holds the parsed, self-verified contents of [`THEORY_BUNDLE_DESTINATION`].
#[derive(Debug, Clone, PartialEq, Eq, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
pub struct BundledTheory {
    /// Bundle format version (must be `1`).
    pub schema_version: u32,
    /// Lowercase 64-character hex SHA-256 digest of the canonical
    /// [`THEORY_BUNDLE_MANIFEST`] file bytes used to render this bundle.
    pub manifest_sha256: String,
    /// Strictly lexicographically sorted, duplicate-free list of embedded
    /// `theory/Anneal/**/*.lean` modules.
    pub modules: Vec<BundledTheoryModule>,
}

const UPSTREAM_PIN_PATH: &str = "vendor/lean-miri/UPSTREAM_PIN.json";
const CORRESPONDENCE_ADAPTER_DIR: &str = "trusted/correspondence";
const CORRESPONDENCE_ADAPTER_PATHS: &[&str] = &[
    "trusted/correspondence/Trusted/Correspondence.lean",
    "trusted/correspondence/Trusted/Correspondence/CanaryFixtures.lean",
    "trusted/correspondence/Trusted/Correspondence/Codec.lean",
    "trusted/correspondence/Trusted/Correspondence/Config.lean",
    "trusted/correspondence/Trusted/Correspondence/Eval.lean",
    "trusted/correspondence/Trusted/Correspondence/Simulation.lean",
    "trusted/correspondence/Trusted/Correspondence/State.lean",
];
const CORRESPONDENCE_PROOF_DIR: &str = "correspondence";
const CORRESPONDENCE_PROOF_PATHS: &[&str] = &[
    "correspondence/Anneal/MirCorrespondence/ByteCodec.lean",
    "correspondence/Anneal/MirCorrespondence/Canaries.lean",
    "correspondence/Anneal/MirCorrespondence/Codec.lean",
    "correspondence/Anneal/MirCorrespondence/CopyReturnPair.lean",
    "correspondence/Anneal/MirCorrespondence/CopyReturnScalar.lean",
    "correspondence/Anneal/MirCorrespondence/EnumEquiv.lean",
    "correspondence/Anneal/MirCorrespondence/InitAndSim.lean",
    "correspondence/Anneal/MirCorrespondence/MemAlloc.lean",
    "correspondence/Anneal/MirCorrespondence/MemRoundTrip.lean",
    "correspondence/Anneal/MirCorrespondence/RetPlace.lean",
    "correspondence/Anneal/MirCorrespondence/RvalueStep.lean",
    "correspondence/Anneal/MirCorrespondence/ScalarEquiv.lean",
    "correspondence/Anneal/MirCorrespondence/SimHelpers.lean",
    "correspondence/Anneal/MirCorrespondence/StmtTermStep.lean",
    "correspondence/Anneal/MirCorrespondence/ValidateLocal.lean",
    "correspondence/Anneal/MirCorrespondenceProof.lean",
];
const TRUSTED_LEAN_PREFIX: &str = "trusted/lean/";

/// Lists the canonical repository-relative files hashed into
/// `CORRESPONDENCE_PROVENANCE_JSON` in [`BUNDLE_DESTINATION`].
///
/// These files are never embedded verbatim or shipped to target users; only
/// their pinned metadata and SHA-256 digests are recorded so verification
/// receipts identify the Pass 2 correspondence certification performed in
/// repository CI. Derived from the single set of named provenance constants
/// above and cross-checked against the `.lean` trees under
/// `trusted/correspondence/` and `correspondence/` during rendering.
pub const PROVENANCE_SOURCES: &[&str] = &[
    UPSTREAM_PIN_PATH,
    "trusted/correspondence/Trusted/Correspondence.lean",
    "trusted/correspondence/Trusted/Correspondence/CanaryFixtures.lean",
    "trusted/correspondence/Trusted/Correspondence/Codec.lean",
    "trusted/correspondence/Trusted/Correspondence/Config.lean",
    "trusted/correspondence/Trusted/Correspondence/Eval.lean",
    "trusted/correspondence/Trusted/Correspondence/Simulation.lean",
    "trusted/correspondence/Trusted/Correspondence/State.lean",
    "correspondence/Anneal/MirCorrespondence/ByteCodec.lean",
    "correspondence/Anneal/MirCorrespondence/Canaries.lean",
    "correspondence/Anneal/MirCorrespondence/Codec.lean",
    "correspondence/Anneal/MirCorrespondence/CopyReturnPair.lean",
    "correspondence/Anneal/MirCorrespondence/CopyReturnScalar.lean",
    "correspondence/Anneal/MirCorrespondence/EnumEquiv.lean",
    "correspondence/Anneal/MirCorrespondence/InitAndSim.lean",
    "correspondence/Anneal/MirCorrespondence/MemAlloc.lean",
    "correspondence/Anneal/MirCorrespondence/MemRoundTrip.lean",
    "correspondence/Anneal/MirCorrespondence/RetPlace.lean",
    "correspondence/Anneal/MirCorrespondence/RvalueStep.lean",
    "correspondence/Anneal/MirCorrespondence/ScalarEquiv.lean",
    "correspondence/Anneal/MirCorrespondence/SimHelpers.lean",
    "correspondence/Anneal/MirCorrespondence/StmtTermStep.lean",
    "correspondence/Anneal/MirCorrespondence/ValidateLocal.lean",
    "correspondence/Anneal/MirCorrespondenceProof.lean",
];
/// Describes what the Pass 2 provenance does and does not certify, matching
/// `docs/mir-correspondence-design.md`: the kernel checks only the operational
/// execution rules of `Trusted/MirSemantics*`, while its theorem-stating
/// surface, shared model types, and correspondence adapter remain
/// human-audited.
const CORRESPONDENCE_PROVENANCE_NOTE: &str = "Pass 2 (anneal-audit --require-correspondence) \
    kernel-certifies the initState/evalStep execution rules of \
    Trusted/MirSemantics* against pinned vendor/lean-miri/ via \
    Trusted/Correspondence* (CorrespondenceClaim, FaultEquivalenceClaim) \
    in blocking repository CI. The theorem-stating surface of \
    Trusted/MirSemantics* (Behavior, BodyVerified, ProgramVerified, \
    CrateTheorem, UnitTheorem, and the helpers they reference), \
    Trusted/MirModel.lean, vendor/lean-miri/, and Trusted/Correspondence* \
    remain human-audited.";

#[derive(Deserialize)]
struct UpstreamPinProvenance {
    repository: String,
    commit: String,
    upstream_lean_toolchain: String,
    build_lean_toolchain: String,
    patched_files: Vec<PatchedFileProvenance>,
}

#[derive(Deserialize, Serialize)]
struct PatchedFileProvenance {
    path: String,
    upstream_sha256: String,
    patched_sha256: String,
}

#[derive(Serialize)]
struct CorrespondenceProvenance {
    schema_version: u32,
    upstream_repository: String,
    upstream_commit: String,
    upstream_lean_toolchain: String,
    build_lean_toolchain: String,
    upstream_pin_sha256: String,
    sysroot_foundation_manifest_sha256: &'static str,
    patched_files: Vec<PatchedFileProvenance>,
    correspondence_adapters: BTreeMap<&'static str, String>,
    correspondence_proofs: BTreeMap<&'static str, String>,
    trusted_lean: BTreeMap<&'static str, String>,
    note: &'static str,
}

/// Names the repository-relative path of the generated Rust bundle table.
pub const BUNDLE_DESTINATION: &str = "trusted/cargo-anneal/src/bundled_resources.rs";

const HEADER: &str = "\
// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// @generated by examples/regenerate_bundle.rs; do not edit.
// Regenerate with:
// cargo run -p cargo-anneal --example regenerate_bundle -- --root .

#[rustfmt::skip]
const BUNDLE: &[(&str, &str)] = &[
";

/// Classifies failures encountered while validating or rendering embedded
/// bundle files.
#[derive(Debug)]
pub enum BundleError {
    /// Indicates a missing file, non-regular file, or symlink along a bundle
    /// source or destination path.
    Policy(String),
    /// Indicates an OS I/O failure while inspecting or reading a regular file.
    Io(io::Error),
}

impl fmt::Display for BundleError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Policy(msg) => f.write_str(msg),
            Self::Io(err) => fmt::Display::fmt(err, f),
        }
    }
}

impl std::error::Error for BundleError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Policy(_) => None,
            Self::Io(err) => Some(err),
        }
    }
}

/// Validate each parent directory of `rel` under `root`, one component at a
/// time with `symlink_metadata`, and return the joined parent path.
///
/// Checking every component rejects a symlinked ancestor even when the final
/// path would resolve to a regular file, so neither regeneration nor parity
/// checking can read or write outside `root`. A missing, non-directory, or
/// symlinked component is a [`BundleError::Policy`] labeled with `label`; any
/// other inspection failure is a [`BundleError::Io`].
fn validate_parent_directories(
    root: &Path,
    rel: &Path,
    label: &str,
) -> Result<PathBuf, BundleError> {
    let mut directory = root.to_path_buf();
    if let Some(parent) = rel.parent() {
        for component in parent.components() {
            let Component::Normal(segment) = component else {
                return Err(BundleError::Policy(format!(
                    "invalid relative {label} path: {}",
                    rel.display()
                )));
            };
            directory.push(segment);
            let meta = fs::symlink_metadata(&directory).map_err(|err| {
                if err.kind() == io::ErrorKind::NotFound {
                    BundleError::Policy(format!(
                        "{label} must be a regular directory: {}",
                        directory.display()
                    ))
                } else {
                    BundleError::Io(err)
                }
            })?;
            if meta.file_type().is_symlink() || !meta.file_type().is_dir() {
                return Err(BundleError::Policy(format!(
                    "{label} must be a regular directory: {}",
                    directory.display()
                )));
            }
        }
    }
    Ok(directory)
}

/// Validate that every parent component of `rel_dest` under `root` is a regular
/// directory (not a symlink) and that `rel_dest` itself, if present, is a
/// regular file.
fn validate_destination_path(
    root: &Path,
    rel_dest: &str,
) -> Result<(PathBuf, Option<fs::Permissions>), BundleError> {
    let rel = Path::new(rel_dest);
    validate_parent_directories(root, rel, "bundle parent")?;
    let destination = root.join(rel);
    let permissions = match fs::symlink_metadata(&destination) {
        Ok(meta) if !meta.file_type().is_symlink() && meta.file_type().is_file() => {
            Some(meta.permissions())
        }
        Ok(_) => {
            return Err(BundleError::Policy(format!(
                "bundle destination must be a regular file: {}",
                destination.display()
            )));
        }
        Err(err) if err.kind() == io::ErrorKind::NotFound => None,
        Err(err) => return Err(BundleError::Io(err)),
    };
    Ok((destination, permissions))
}

/// Validate that every parent component of [`BUNDLE_DESTINATION`] under `root`
/// is a regular directory (not a symlink) and that [`BUNDLE_DESTINATION`]
/// itself, if present, is a regular file.
///
/// Return the destination path and, when the file exists, its permissions so
/// regeneration can preserve them. A missing destination is not an error here:
/// regeneration creates it, and `anneal-audit` rejects its absence separately.
pub fn validate_bundle_destination(
    root: &Path,
) -> Result<(PathBuf, Option<fs::Permissions>), BundleError> {
    validate_destination_path(root, BUNDLE_DESTINATION)
}

/// Validate that every parent component of [`THEORY_BUNDLE_DESTINATION`] under
/// `root` is a regular directory (not a symlink) and that
/// [`THEORY_BUNDLE_DESTINATION`] itself, if present, is a regular file.
pub fn validate_theory_bundle_destination(
    root: &Path,
) -> Result<(PathBuf, Option<fs::Permissions>), BundleError> {
    validate_destination_path(root, THEORY_BUNDLE_DESTINATION)
}

fn is_lowercase_sha256_hex(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'))
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

/// Load and strictly validate [`THEORY_BUNDLE_MANIFEST`] under `root`,
/// returning `(manifest_sha256, manifest)`.
///
/// Rejects symlinks, malformed JSON, unknown fields, wrong `schema_version`,
/// out-of-tree or non-`Anneal` paths, duplicate or unsorted entries, missing
/// required core theory (`theory/Anneal/MirWp.lean`), and non-lowercase or
/// malformed SHA-256 digests. Callers that need on-disk source parity should
/// use [`render_bundled_theory`], which also checks every listed file's bytes
/// against its manifest digest.
pub fn load_theory_bundle_manifest(
    root: &Path,
) -> Result<(String, TheoryBundleManifest), BundleError> {
    let manifest_path = validate_bundle_source(root, THEORY_BUNDLE_MANIFEST)?;
    let manifest_bytes = fs::read(manifest_path).map_err(BundleError::Io)?;
    let manifest_sha256 = sha256_bytes(&manifest_bytes);
    let manifest: TheoryBundleManifest = serde_json::from_slice(&manifest_bytes).map_err(|err| {
        BundleError::Policy(format!("malformed {THEORY_BUNDLE_MANIFEST}: {err}"))
    })?;
    if manifest.schema_version != 1 {
        return Err(BundleError::Policy(format!(
            "unsupported schema_version {} in {THEORY_BUNDLE_MANIFEST}",
            manifest.schema_version
        )));
    }
    validate_theory_path_sequence(
        manifest.modules.iter().map(|entry| entry.path.as_str()),
        THEORY_BUNDLE_MANIFEST,
    )?;
    for entry in &manifest.modules {
        if !is_lowercase_sha256_hex(&entry.sha256) {
            return Err(BundleError::Policy(format!(
                "invalid lowercase SHA-256 in {THEORY_BUNDLE_MANIFEST} for {}",
                entry.path
            )));
        }
    }
    Ok((manifest_sha256, manifest))
}

/// Parse and self-verify a serialized [`BundledTheory`] JSON payload.
///
/// Verifies schema version, manifest digest format, strict canonical path
/// ordering under `theory/Anneal/`, required core module presence, and
/// per-module SHA-256 equality against each embedded UTF-8 source payload.
pub fn parse_bundled_theory(raw: &str) -> Result<BundledTheory, BundleError> {
    let parsed: BundledTheory = serde_json::from_str(raw).map_err(|err| {
        BundleError::Policy(format!("malformed {THEORY_BUNDLE_DESTINATION}: {err}"))
    })?;
    if parsed.schema_version != 1 {
        return Err(BundleError::Policy(format!(
            "unsupported schema_version {} in {THEORY_BUNDLE_DESTINATION}",
            parsed.schema_version
        )));
    }
    if !is_lowercase_sha256_hex(&parsed.manifest_sha256) {
        return Err(BundleError::Policy(format!(
            "invalid manifest_sha256 in {THEORY_BUNDLE_DESTINATION}"
        )));
    }
    validate_theory_path_sequence(
        parsed.modules.iter().map(|entry| entry.path.as_str()),
        THEORY_BUNDLE_DESTINATION,
    )?;
    for entry in &parsed.modules {
        if !is_lowercase_sha256_hex(&entry.sha256) {
            return Err(BundleError::Policy(format!(
                "invalid lowercase SHA-256 in {THEORY_BUNDLE_DESTINATION} for {}",
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
    }
    Ok(parsed)
}

/// Return the parsed, self-verified [`BundledTheory`] embedded into
/// `cargo-anneal` via `include_str!("bundled_theory.json")`.
pub fn embedded_theory_bundle() -> Result<BundledTheory, BundleError> {
    parse_bundled_theory(EMBEDDED_THEORY_BUNDLE_JSON)
}

/// Validate that every parent component and the leaf file of `rel` under `root`
/// exist and are regular directories and a regular file without symlinks, and
/// return the joined source path.
pub fn validate_bundle_source(root: &Path, rel: &str) -> Result<PathBuf, BundleError> {
    let rel_path = Path::new(rel);
    validate_parent_directories(root, rel_path, "bundle source parent")?;
    let source = root.join(rel_path);
    match fs::symlink_metadata(&source) {
        Ok(meta) if !meta.file_type().is_symlink() && meta.file_type().is_file() => Ok(source),
        Ok(_) => Err(BundleError::Policy(format!(
            "bundle source must be a regular file: {}",
            source.display()
        ))),
        Err(err) if err.kind() == io::ErrorKind::NotFound => Err(BundleError::Policy(format!(
            "missing canonical bundle source: {rel}"
        ))),
        Err(err) => Err(BundleError::Io(err)),
    }
}

/// Walk `root/<subdir>` without following symlinks and assert that its exact
/// set of `.lean` files matches `expected`, failing closed if a newly added
/// Pass 2 certified module would otherwise be omitted from provenance.
fn verify_correspondence_lean_inventory(
    root: &Path,
    subdir: &str,
    expected: &[&str],
) -> Result<(), BundleError> {
    let dir_rel = Path::new(subdir);
    validate_parent_directories(root, dir_rel, "correspondence directory parent")?;
    let dir = root.join(dir_rel);
    let root_meta = fs::symlink_metadata(&dir).map_err(|err| {
        if err.kind() == io::ErrorKind::NotFound {
            BundleError::Policy(format!(
                "missing correspondence directory: {}",
                dir.display()
            ))
        } else {
            BundleError::Io(err)
        }
    })?;
    if root_meta.file_type().is_symlink() || !root_meta.file_type().is_dir() {
        return Err(BundleError::Policy(format!(
            "correspondence directory must be a regular directory: {}",
            dir.display()
        )));
    }
    let mut found = BTreeSet::new();
    for entry in WalkDir::new(&dir).follow_links(false) {
        let entry = entry.map_err(|err| {
            let msg = err.to_string();
            err.into_io_error()
                .map_or_else(|| BundleError::Policy(msg), BundleError::Io)
        })?;
        let ft = entry.file_type();
        if ft.is_symlink() {
            return Err(BundleError::Policy(format!(
                "symlink forbidden under {subdir}: {}",
                entry.path().display()
            )));
        }
        if ft.is_dir() {
            continue;
        }
        if !ft.is_file() {
            return Err(BundleError::Policy(format!(
                "non-regular file under {subdir}: {}",
                entry.path().display()
            )));
        }
        let rel = entry
            .path()
            .strip_prefix(root)
            .map_err(|e| BundleError::Policy(e.to_string()))?;
        let rel_str = rel.to_string_lossy().replace('\\', "/");
        if rel_str.ends_with(".lean") {
            found.insert(rel_str);
        }
    }
    let expected_set: BTreeSet<String> = expected.iter().map(|s| (*s).to_string()).collect();
    if found != expected_set {
        return Err(BundleError::Policy(format!(
            "correspondence provenance inventory mismatch under {subdir}: expected {expected_set:?}, found {found:?}"
        )));
    }
    Ok(())
}

fn hash_bundle_sources(
    root: &Path,
    paths: &[&'static str],
) -> Result<BTreeMap<&'static str, String>, BundleError> {
    let mut hashes = BTreeMap::new();
    for rel in paths {
        let path = validate_bundle_source(root, rel)?;
        let bytes = fs::read(path).map_err(BundleError::Io)?;
        hashes.insert(*rel, sha256_bytes(&bytes));
    }
    Ok(hashes)
}

fn render_correspondence_provenance(
    root: &Path,
    trusted_lean: BTreeMap<&'static str, String>,
) -> Result<String, BundleError> {
    let pin_path = validate_bundle_source(root, UPSTREAM_PIN_PATH)?;
    let pin_bytes = fs::read(pin_path).map_err(BundleError::Io)?;
    let upstream_pin_sha256 = sha256_bytes(&pin_bytes);
    let mut pin: UpstreamPinProvenance = serde_json::from_slice(&pin_bytes).map_err(|err| {
        BundleError::Policy(format!(
            "malformed {UPSTREAM_PIN_PATH} for provenance: {err}"
        ))
    })?;
    if pin.repository.is_empty()
        || pin.commit.is_empty()
        || pin.upstream_lean_toolchain.is_empty()
        || pin.build_lean_toolchain.is_empty()
    {
        return Err(BundleError::Policy(format!(
            "empty provenance metadata field in {UPSTREAM_PIN_PATH}"
        )));
    }
    pin.patched_files.sort_by(|a, b| a.path.cmp(&b.path));
    let mut seen_paths = BTreeSet::new();
    for entry in &pin.patched_files {
        if entry.path.is_empty()
            || !seen_paths.insert(entry.path.as_str())
            || !is_sha256_hex(&entry.upstream_sha256)
            || !is_sha256_hex(&entry.patched_sha256)
        {
            return Err(BundleError::Policy(format!(
                "invalid patched_files provenance record in {UPSTREAM_PIN_PATH}: {}",
                entry.path
            )));
        }
    }

    let correspondence_adapters = hash_bundle_sources(root, CORRESPONDENCE_ADAPTER_PATHS)?;
    let correspondence_proofs = hash_bundle_sources(root, CORRESPONDENCE_PROOF_PATHS)?;

    verify_correspondence_lean_inventory(
        root,
        CORRESPONDENCE_ADAPTER_DIR,
        CORRESPONDENCE_ADAPTER_PATHS,
    )?;
    verify_correspondence_lean_inventory(
        root,
        CORRESPONDENCE_PROOF_DIR,
        CORRESPONDENCE_PROOF_PATHS,
    )?;

    let provenance = CorrespondenceProvenance {
        schema_version: 1,
        upstream_repository: pin.repository,
        upstream_commit: pin.commit,
        upstream_lean_toolchain: pin.upstream_lean_toolchain,
        build_lean_toolchain: pin.build_lean_toolchain,
        upstream_pin_sha256,
        sysroot_foundation_manifest_sha256: LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256,
        patched_files: pin.patched_files,
        correspondence_adapters,
        correspondence_proofs,
        trusted_lean,
        note: CORRESPONDENCE_PROVENANCE_NOTE,
    };
    serde_json::to_string(&provenance).map_err(|err| {
        BundleError::Policy(format!(
            "failed to serialize correspondence provenance: {err}"
        ))
    })
}

/// Render the exact expected contents of [`BUNDLE_DESTINATION`] from the
/// canonical regular `trusted/` files in [`TRUSTED_BUNDLE_SOURCES`] under
/// `root`.
pub fn render_bundled_resources(root: &Path) -> Result<String, BundleError> {
    let mut generated = HEADER.to_owned();
    let mut trusted_lean = BTreeMap::new();
    for path in TRUSTED_BUNDLE_SOURCES {
        let source_path = validate_bundle_source(root, path)?;
        let source = fs::read_to_string(source_path).map_err(BundleError::Io)?;
        if path.starts_with(TRUSTED_LEAN_PREFIX) {
            trusted_lean.insert(*path, sha256_bytes(source.as_bytes()));
        }
        // Rust's standard string formatter supplies valid Rust literal escapes.
        // The embedded bytes must equal the canonical UTF-8 source exactly.
        writeln!(
            generated,
            "    (\n        {path:?},\n        {source:?},\n    ),"
        )
        .expect("writing to String cannot fail");
    }
    generated.push_str("];\n\n");
    let provenance_json = render_correspondence_provenance(root, trusted_lean)?;
    writeln!(
        generated,
        "#[rustfmt::skip]\nconst CORRESPONDENCE_PROVENANCE_JSON: &str = {provenance_json:?};"
    )
    .expect("writing to String cannot fail");
    Ok(generated)
}

/// Render the exact expected contents of [`THEORY_BUNDLE_DESTINATION`] from
/// [`THEORY_BUNDLE_MANIFEST`] and the canonical regular `theory/` source files
/// under `root`, failing closed on any missing file, symlink, invalid path,
/// unsorted/duplicate manifest entry, or SHA-256 mismatch.
pub fn render_bundled_theory(root: &Path) -> Result<String, BundleError> {
    let (manifest_sha256, manifest) = load_theory_bundle_manifest(root)?;
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
        schema_version: 1,
        manifest_sha256,
        modules,
    };
    let mut rendered = serde_json::to_string_pretty(&payload).map_err(|err| {
        BundleError::Policy(format!("failed to serialize {THEORY_BUNDLE_DESTINATION}: {err}"))
    })?;
    rendered.push('\n');
    Ok(rendered)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn provenance_sources_match_component_lists() {
        let expected: Vec<&str> = std::iter::once(UPSTREAM_PIN_PATH)
            .chain(CORRESPONDENCE_ADAPTER_PATHS.iter().copied())
            .chain(CORRESPONDENCE_PROOF_PATHS.iter().copied())
            .collect();
        assert_eq!(PROVENANCE_SOURCES, expected.as_slice());
    }

    #[test]
    fn embedded_theory_bundle_is_self_consistent() {
        let bundled = embedded_theory_bundle().expect("embedded theory bundle must verify");
        assert_eq!(bundled.schema_version, 1);
        assert!(bundled.modules.iter().any(|m| m.path == REQUIRED_THEORY_BUNDLE_PATH));
    }

    #[test]
    fn parse_bundled_theory_rejects_tampered_and_invalid_payloads() {
        let valid = embedded_theory_bundle().unwrap();
        let mut tampered = valid.clone();
        tampered.modules[0].content.push_str("\n-- tampered\n");
        let err = parse_bundled_theory(&serde_json::to_string(&tampered).unwrap()).unwrap_err();
        assert!(err.to_string().contains("SHA-256 mismatch"), "{err}");

        let mut dup = valid.clone();
        let first = dup.modules[0].clone();
        dup.modules.push(first);
        let err = parse_bundled_theory(&serde_json::to_string(&dup).unwrap()).unwrap_err();
        assert!(err.to_string().contains("duplicate theory bundle path"), "{err}");

        let mut unsorted = valid.clone();
        unsorted.modules.swap(0, 1);
        let err = parse_bundled_theory(&serde_json::to_string(&unsorted).unwrap()).unwrap_err();
        assert!(err.to_string().contains("unsorted theory bundle entry"), "{err}");

        let mut escaped = valid.clone();
        escaped.modules[0].path = "trusted/lean/Trusted.lean".to_owned();
        let err = parse_bundled_theory(&serde_json::to_string(&escaped).unwrap()).unwrap_err();
        assert!(err.to_string().contains("must reside under theory/Anneal/"), "{err}");

        let mut traversal = valid.clone();
        traversal.modules[0].path = "theory/Anneal/../Trusted.lean".to_owned();
        let err = parse_bundled_theory(&serde_json::to_string(&traversal).unwrap()).unwrap_err();
        assert!(err.to_string().contains("invalid relative theory bundle path"), "{err}");

        let mut umbrella = valid.clone();
        umbrella.modules[0].path = "theory/Anneal.lean".to_owned();
        let err = parse_bundled_theory(&serde_json::to_string(&umbrella).unwrap()).unwrap_err();
        assert!(err.to_string().contains("must name a module under theory/Anneal/"), "{err}");

        let mut missing_required = valid;
        missing_required.modules.retain(|m| m.path != REQUIRED_THEORY_BUNDLE_PATH);
        let err = parse_bundled_theory(&serde_json::to_string(&missing_required).unwrap())
            .unwrap_err();
        assert!(err.to_string().contains("missing required theory module"), "{err}");
    }
}
