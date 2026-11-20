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

use crate::toolchain::{LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256, is_sha256_hex, sha256_bytes};

/// Lists the canonical repository-relative source files embedded into
/// `cargo-anneal`.
///
/// Resource ownership remains explicit so runtime target verification never
/// discovers model, lock, or inspector files from an untrusted checkout. Within
/// `theory/`, `BUNDLE_SOURCES` includes `theory/Anneal/NatBitwise.lean`,
/// `theory/Anneal/BitVec.lean`, `theory/Anneal/BitVecArith.lean`,
/// `theory/Anneal/LeBytes.lean`, `theory/Anneal/ListChunks.lean`,
/// `theory/Anneal/MirWp.lean`, and `theory/Anneal/LoopInv.lean`, which
/// target verification stages and compiles demand-driven via BFS from
/// non-bundled target modules so unused bundled theory modules incur no
/// compilation or provenance overhead.
pub const BUNDLE_SOURCES: &[&str] = &[
    "trusted/audit/TrustedBoundary.lean",
    "trusted/audit/library-lock.json",
    "trusted/lean/foundation-lock.json",
    "trusted/lean/lean-toolchain",
    "trusted/lean/Trusted.lean",
    "trusted/lean/Trusted/MirAst.lean",
    "trusted/lean/Trusted/MirSemantics.lean",
    "theory/Anneal/NatBitwise.lean",
    "theory/Anneal/BitVec.lean",
    "theory/Anneal/BitVecArith.lean",
    "theory/Anneal/LeBytes.lean",
    "theory/Anneal/ListChunks.lean",
    "theory/Anneal/MirWp.lean",
    "theory/Anneal/LoopInv.lean",
];

const UPSTREAM_PIN_PATH: &str = "vendor/lean-miri/UPSTREAM_PIN.json";
const CORRESPONDENCE_ADAPTER_DIR: &str = "trusted/correspondence";
const CORRESPONDENCE_ADAPTER_PATH: &str = "trusted/correspondence/Trusted/Correspondence.lean";
const CORRESPONDENCE_PROOF_DIR: &str = "correspondence";
const CORRESPONDENCE_PROOF_BASE_PATH: &str = "correspondence/Anneal/MirCorrespondenceBase.lean";
const CORRESPONDENCE_PROOF_MAIN_PATH: &str = "correspondence/Anneal/MirCorrespondenceProof.lean";
const CORRESPONDENCE_PROOF_PATHS: &[&str] = &[
    CORRESPONDENCE_PROOF_BASE_PATH,
    CORRESPONDENCE_PROOF_MAIN_PATH,
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
    CORRESPONDENCE_ADAPTER_PATH,
    CORRESPONDENCE_PROOF_BASE_PATH,
    CORRESPONDENCE_PROOF_MAIN_PATH,
];
/// Describes what the Pass 2 provenance does and does not certify, matching
/// `docs/mir-correspondence-design.md`: the kernel checks only the operational
/// execution rules of `Trusted/MirSemantics.lean`, while its theorem-stating
/// surface and the correspondence adapter remain human-audited.
const CORRESPONDENCE_PROVENANCE_NOTE: &str = "Pass 2 (anneal-audit --require-correspondence) \
    kernel-certifies the initState/evalStep execution rules of \
    Trusted/MirSemantics.lean against pinned vendor/lean-miri/ via \
    Trusted/Correspondence.lean (CorrespondenceClaim, FaultEquivalenceClaim) \
    in blocking repository CI. The theorem-stating surface of \
    Trusted/MirSemantics.lean (Behavior, BodyVerified, ProgramVerified, \
    CrateTheorem, UnitTheorem, and the helpers they reference), \
    vendor/lean-miri/, and Trusted/Correspondence.lean remain human-audited.";

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
    correspondence_adapter_sha256: String,
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
    let rel = Path::new(BUNDLE_DESTINATION);
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

    let adapter_path = validate_bundle_source(root, CORRESPONDENCE_ADAPTER_PATH)?;
    let adapter_bytes = fs::read(adapter_path).map_err(BundleError::Io)?;
    let correspondence_adapter_sha256 = sha256_bytes(&adapter_bytes);

    let mut correspondence_proofs = BTreeMap::new();
    for rel in CORRESPONDENCE_PROOF_PATHS {
        let proof_path = validate_bundle_source(root, rel)?;
        let proof_bytes = fs::read(proof_path).map_err(BundleError::Io)?;
        correspondence_proofs.insert(*rel, sha256_bytes(&proof_bytes));
    }

    verify_correspondence_lean_inventory(
        root,
        CORRESPONDENCE_ADAPTER_DIR,
        &[CORRESPONDENCE_ADAPTER_PATH],
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
        correspondence_adapter_sha256,
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
/// canonical regular files under `root`.
pub fn render_bundled_resources(root: &Path) -> Result<String, BundleError> {
    let mut generated = HEADER.to_owned();
    let mut trusted_lean = BTreeMap::new();
    for path in BUNDLE_SOURCES {
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
