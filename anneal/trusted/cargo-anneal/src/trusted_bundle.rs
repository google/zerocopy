// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Defines the canonical trusted-source and correspondence-provenance
//! inventory plus deterministic rendering shared between `build.rs`,
//! `bundle.rs`, and `anneal-audit`.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::{self, Write as _},
    fs, io,
    path::{Component, Path, PathBuf},
};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use walkdir::WalkDir;

/// Names the pinned SHA-256 manifest digest of all
/// `<prefix>/lib/lean/{Init,Std,Lean}*` `.olean`, `.olean.server`,
/// `.olean.private`, `.ir.sig`, and `.ir` artifacts in the pinned Lean
/// 4.34.1 toolchain, computed over sorted `"{rel_path}:{sha256}\n"` lines.
///
/// Pinned `Checker::tool_admission` verifies this manifest before running
/// `TrustedBoundary.lean` (so both `anneal-audit` Pass 1/2 and
/// `cargo-anneal verify` authenticate the sysroot `.olean` and `.ir`
/// dependency cone of the standalone inspector), and `anneal-audit` Pass 2
/// additionally extracts the sorted `.sysrootFoundation` module list before
/// compiling or loading `.vendorMiri` and `.sysrootFoundation` modules.
pub const LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256: &str =
    "9fdeeac45fb6b0b88a978729a67db26f2a71c108adf5366091cb533abea60e88";

/// Lists the canonical repository-relative trusted source files embedded into
/// `cargo-anneal` at build time into `$OUT_DIR/bundled_resources.rs`.
///
/// Resource ownership remains explicit so runtime target verification never
/// discovers model, lock, or inspector files from an untrusted checkout.
/// Bundled Pass 1 `theory/` libraries are registered separately in
/// `theory/bundle-manifest.json` and generated at build time into
/// `$OUT_DIR/bundled_theory.json`, keeping `trusted/` registrations decoupled
/// from untrusted proof-library additions.
pub const TRUSTED_BUNDLE_SOURCES: &[&str] = &[
    "trusted/audit/SpecPreflight.lean",
    "trusted/audit/TrustedBoundary.lean",
    "trusted/audit/library-lock.json",
    "trusted/lean/foundation-lock.json",
    "trusted/lean/lean-toolchain",
    "trusted/lean/Trusted.lean",
    "trusted/lean/Trusted/Framework.lean",
    "trusted/lean/Trusted/Framework/Bridge.lean",
    "trusted/lean/Trusted/Framework/Instances.lean",
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
    "trusted/lean/Trusted/MirSemantics/Contract.lean",
    "trusted/lean/Trusted/MirSemantics/CoreContracts.lean",
    "trusted/lean/Trusted/MirSemantics/Enum.lean",
    "trusted/lean/Trusted/MirSemantics/Layout.lean",
    "trusted/lean/Trusted/MirSemantics/Memory.lean",
    "trusted/lean/Trusted/MirSemantics/Ops.lean",
    "trusted/lean/Trusted/MirSemantics/State.lean",
    "trusted/lean/Trusted/MirSemantics/Step.lean",
];

/// Names the repository-relative path of the pinned upstream Miri manifest.
pub const UPSTREAM_PIN_PATH: &str = "vendor/lean-miri/UPSTREAM_PIN.json";
/// Names the repository-relative path of the pinned upstream MiniRust manifest.
pub const MINIRUST_UPSTREAM_PIN_PATH: &str = "vendor/minirust/UPSTREAM_PIN.json";
/// Names the repository-relative root directory of Pass 2 trusted adapters.
pub const CORRESPONDENCE_ADAPTER_DIR: &str = "trusted/correspondence";
/// Lists the repository-relative Pass 2 trusted correspondence adapter sources.
pub const CORRESPONDENCE_ADAPTER_PATHS: &[&str] = &[
    "trusted/correspondence/Trusted/Correspondence.lean",
    "trusted/correspondence/Trusted/Correspondence/CanaryFixtures.lean",
    "trusted/correspondence/Trusted/Correspondence/Codec.lean",
    "trusted/correspondence/Trusted/Correspondence/Config.lean",
    "trusted/correspondence/Trusted/Correspondence/Eval.lean",
    "trusted/correspondence/Trusted/Correspondence/Simulation.lean",
    "trusted/correspondence/Trusted/Correspondence/State.lean",
];
/// Names the repository-relative root of Pass 2 correspondence proofs.
pub const CORRESPONDENCE_PROOF_DIR: &str = "correspondence";
/// Lists the repository-relative Pass 2 correspondence proof modules.
pub const CORRESPONDENCE_PROOF_PATHS: &[&str] = &[
    "correspondence/Anneal/MiniRust/Anchors.lean",
    "correspondence/Anneal/MiniRust/Machine.lean",
    "correspondence/Anneal/MiniRust/Memory.lean",
    "correspondence/Anneal/MiniRust/OpSim.lean",
    "correspondence/Anneal/MiniRust/OracleCert.lean",
    "correspondence/Anneal/MiniRust/Relation.lean",
    "correspondence/Anneal/MiniRust/StepSim.lean",
    "correspondence/Anneal/MiniRust/Syntax.lean",
    "correspondence/Anneal/MiniRust/Translate.lean",
    "correspondence/Anneal/MiniRustProof.lean",
    "correspondence/Anneal/MirCorrespondence/ByteCodec.lean",
    "correspondence/Anneal/MirCorrespondence/Canaries.lean",
    "correspondence/Anneal/MirCorrespondence/Codec.lean",
    "correspondence/Anneal/MirCorrespondence/CopyReturnPair.lean",
    "correspondence/Anneal/MirCorrespondence/CopyReturnScalar.lean",
    "correspondence/Anneal/MirCorrespondence/EnumEquiv.lean",
    "correspondence/Anneal/MirCorrespondence/InitAndSim.lean",
    "correspondence/Anneal/MirCorrespondence/LayoutAndAlign.lean",
    "correspondence/Anneal/MirCorrespondence/MemAlloc.lean",
    "correspondence/Anneal/MirCorrespondence/MemRoundTrip.lean",
    "correspondence/Anneal/MirCorrespondence/MiriMemoryBridge.lean",
    "correspondence/Anneal/MirCorrespondence/RefinementBundles.lean",
    "correspondence/Anneal/MirCorrespondence/RetPlace.lean",
    "correspondence/Anneal/MirCorrespondence/RvalueStep.lean",
    "correspondence/Anneal/MirCorrespondence/ScalarEquiv.lean",
    "correspondence/Anneal/MirCorrespondence/SimHelpers.lean",
    "correspondence/Anneal/MirCorrespondence/StmtTermStep.lean",
    "correspondence/Anneal/MirCorrespondence/ValidateLocal.lean",
    "correspondence/Anneal/MirCorrespondenceProof.lean",
];
const TRUSTED_LEAN_PREFIX: &str = "trusted/lean/";

/// Lists the canonical repository-relative files hashed into the Pass 2
/// correspondence provenance record.
///
/// These files are never embedded verbatim or shipped to target users; only
/// their pinned metadata and SHA-256 digests are recorded so the packaged
/// archive's provenance record identifies the Pass 2 correspondence
/// certification performed in repository CI. `cargo-anneal` neither embeds
/// nor watches them, so Pass 2 edits never force a `cargo-anneal` rebuild.
/// Derived from the single set of named provenance constants above and
/// cross-checked against the `.lean` trees under `trusted/correspondence/`
/// and `correspondence/` during rendering.
pub const PROVENANCE_SOURCES: &[&str] = &[
    UPSTREAM_PIN_PATH,
    MINIRUST_UPSTREAM_PIN_PATH,
    "trusted/correspondence/Trusted/Correspondence.lean",
    "trusted/correspondence/Trusted/Correspondence/CanaryFixtures.lean",
    "trusted/correspondence/Trusted/Correspondence/Codec.lean",
    "trusted/correspondence/Trusted/Correspondence/Config.lean",
    "trusted/correspondence/Trusted/Correspondence/Eval.lean",
    "trusted/correspondence/Trusted/Correspondence/Simulation.lean",
    "trusted/correspondence/Trusted/Correspondence/State.lean",
    "correspondence/Anneal/MiniRust/Anchors.lean",
    "correspondence/Anneal/MiniRust/Machine.lean",
    "correspondence/Anneal/MiniRust/Memory.lean",
    "correspondence/Anneal/MiniRust/OpSim.lean",
    "correspondence/Anneal/MiniRust/OracleCert.lean",
    "correspondence/Anneal/MiniRust/Relation.lean",
    "correspondence/Anneal/MiniRust/StepSim.lean",
    "correspondence/Anneal/MiniRust/Syntax.lean",
    "correspondence/Anneal/MiniRust/Translate.lean",
    "correspondence/Anneal/MiniRustProof.lean",
    "correspondence/Anneal/MirCorrespondence/ByteCodec.lean",
    "correspondence/Anneal/MirCorrespondence/Canaries.lean",
    "correspondence/Anneal/MirCorrespondence/Codec.lean",
    "correspondence/Anneal/MirCorrespondence/CopyReturnPair.lean",
    "correspondence/Anneal/MirCorrespondence/CopyReturnScalar.lean",
    "correspondence/Anneal/MirCorrespondence/EnumEquiv.lean",
    "correspondence/Anneal/MirCorrespondence/InitAndSim.lean",
    "correspondence/Anneal/MirCorrespondence/LayoutAndAlign.lean",
    "correspondence/Anneal/MirCorrespondence/MemAlloc.lean",
    "correspondence/Anneal/MirCorrespondence/MemRoundTrip.lean",
    "correspondence/Anneal/MirCorrespondence/MiriMemoryBridge.lean",
    "correspondence/Anneal/MirCorrespondence/RefinementBundles.lean",
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
/// surface, shared model types, correspondence adapter, and unlocked MiniRust
/// specification claims remain human-audited.
pub const CORRESPONDENCE_PROVENANCE_NOTE: &str = "Pass 2 (anneal-audit --require-correspondence) \
    kernel-certifies the initState/evalStep execution rules of \
    Trusted/MirSemantics* against pinned vendor/lean-miri/ via \
    Trusted/Correspondence* (CorrespondenceClaim, FaultEquivalenceClaim) and \
    kernel-replays correspondence/Anneal/MiniRust* (whose claim statements and \
    transcribed machine reside in unlocked correspondence/, with \
    vendor/minirust/UPSTREAM_PIN.json verified by Tier-0 CI and recorded here) \
    in blocking repository CI. \
    The theorem-stating surface of Trusted/MirSemantics* (Behavior, \
    BodyVerified, ProgramVerified, CrateTheorem, UnitTheorem, and the helpers \
    they reference), Trusted/MirModel.lean, vendor/lean-miri/, \
    vendor/minirust/, Trusted/Correspondence*, and unlocked MiniRust claims \
    remain human-audited.";

fn deserialize_unique_btreemap<'de, D>(
    deserializer: D,
) -> Result<BTreeMap<String, String>, D::Error>
where
    D: serde::Deserializer<'de>,
{
    struct UniqueMapVisitor;

    impl<'de> serde::de::Visitor<'de> for UniqueMapVisitor {
        type Value = BTreeMap<String, String>;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("a JSON object mapping file paths to SHA-256 digests")
        }

        fn visit_map<M>(self, mut access: M) -> Result<Self::Value, M::Error>
        where
            M: serde::de::MapAccess<'de>,
        {
            let mut map = BTreeMap::new();
            while let Some((key, value)) = access.next_entry::<String, String>()? {
                if map.insert(key.clone(), value).is_some() {
                    return Err(serde::de::Error::custom(format!(
                        "duplicate files entry: {key:?}"
                    )));
                }
            }
            Ok(map)
        }
    }

    deserializer.deserialize_map(UniqueMapVisitor)
}

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

#[derive(Deserialize)]
struct MiniRustPinInput {
    upstream_repo: String,
    commit: String,
    tarball_sha256: String,
    file_count: usize,
    manifest_sha256: String,
    #[serde(deserialize_with = "deserialize_unique_btreemap")]
    files: BTreeMap<String, String>,
}

#[derive(Serialize)]
struct MiniRustProvenance {
    upstream_repository: String,
    upstream_commit: String,
    upstream_pin_sha256: String,
    tarball_sha256: String,
    manifest_sha256: String,
    file_count: usize,
    files: BTreeMap<String, String>,
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
    minirust_upstream: MiniRustProvenance,
    correspondence_adapters: BTreeMap<&'static str, String>,
    correspondence_proofs: BTreeMap<&'static str, String>,
    trusted_lean: BTreeMap<&'static str, String>,
    note: &'static str,
}

/// Names the legacy checked-in Rust bundle path, which must stay absent from
/// clean repository checkouts now that `build.rs` emits into `$OUT_DIR`.
pub const LEGACY_BUNDLE_DESTINATION: &str = "trusted/cargo-anneal/src/bundled_resources.rs";

/// Names the repository-relative path used strictly for transient standalone
/// `.crate` packaging snapshots (`regenerate_bundle --stage-package`).
pub const PACKAGED_BUNDLE_DESTINATION: &str = "trusted/cargo-anneal/packaged/bundled_resources.rs";

/// Names the crate-relative path of the standalone `.crate` packaging snapshot
/// inside `cargo-anneal`.
pub const PACKAGED_BUNDLE_CRATE_REL: &str = "packaged/bundled_resources.rs";

/// Names the generated header emitted at the top of `bundled_resources.rs`.
pub const BUNDLE_HEADER: &str = "\
// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

// @generated by build.rs / trusted_bundle::render_bundled_resources; do not edit.

#[rustfmt::skip]
const BUNDLE: &[(&str, &str)] = &[
";

/// Closes the `BUNDLE` array opened by [`BUNDLE_HEADER`]; every rendered
/// `bundled_resources.rs` ends with exactly this suffix.
const BUNDLE_FOOTER: &str = "];\n";

/// Compute the lowercase hex-encoded FIPS 180-4 SHA-256 digest of `data`.
pub fn sha256_bytes(data: &[u8]) -> String {
    let mut hex = String::with_capacity(64);
    for byte in Sha256::digest(data) {
        let _ = write!(&mut hex, "{byte:02x}");
    }
    hex
}

/// Return `true` if `s` is a 64-character ASCII hex digest.
pub fn is_sha256_hex(s: &str) -> bool {
    s.len() == 64 && s.bytes().all(|b| b.is_ascii_hexdigit())
}

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
pub fn validate_parent_directories(
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
pub fn validate_destination_path(
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

/// Prepare and validate [`PACKAGED_BUNDLE_DESTINATION`] under `root`.
///
/// Validates that every existing parent component of
/// [`PACKAGED_BUNDLE_DESTINATION`] under `root` is a regular directory (not a
/// symlink), creates `trusted/cargo-anneal/packaged` if it does not yet exist,
/// and validates that [`PACKAGED_BUNDLE_DESTINATION`] itself, if present, is a
/// regular file.
pub fn prepare_packaged_bundle_destination(
    root: &Path,
) -> Result<(PathBuf, Option<fs::Permissions>), BundleError> {
    let rel = Path::new(PACKAGED_BUNDLE_DESTINATION);
    if let Some(parent) = rel.parent() {
        let pkg_dir = root.join(parent);
        if let Err(err) = fs::symlink_metadata(&pkg_dir)
            && err.kind() == io::ErrorKind::NotFound
        {
            validate_parent_directories(root, parent, "bundle parent")?;
            fs::create_dir(&pkg_dir).map_err(BundleError::Io)?;
        }
    }
    validate_destination_path(root, PACKAGED_BUNDLE_DESTINATION)
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
        Err(err) if err.kind() == io::ErrorKind::NotFound => {
            Err(BundleError::Policy(format!("missing canonical bundle source: {rel}")))
        }
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
            BundleError::Policy(format!("missing correspondence directory: {}", dir.display()))
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
            err.into_io_error().map_or(BundleError::Policy(msg), BundleError::Io)
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
        let rel =
            entry.path().strip_prefix(root).map_err(|e| BundleError::Policy(e.to_string()))?;
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

/// Render the Pass 2 correspondence provenance record from canonical Miri and
/// MiniRust `UPSTREAM_PIN.json` manifests, `trusted/correspondence/`,
/// `correspondence/`, and `trusted_lean` digests.
pub fn render_correspondence_provenance(
    root: &Path,
    trusted_lean: BTreeMap<&'static str, String>,
) -> Result<String, BundleError> {
    let pin_path = validate_bundle_source(root, UPSTREAM_PIN_PATH)?;
    let pin_bytes = fs::read(pin_path).map_err(BundleError::Io)?;
    let upstream_pin_sha256 = sha256_bytes(&pin_bytes);
    let mut pin: UpstreamPinProvenance = serde_json::from_slice(&pin_bytes).map_err(|err| {
        BundleError::Policy(format!("malformed {UPSTREAM_PIN_PATH} for provenance: {err}"))
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

    let mr_pin_path = validate_bundle_source(root, MINIRUST_UPSTREAM_PIN_PATH)?;
    let mr_pin_bytes = fs::read(mr_pin_path).map_err(BundleError::Io)?;
    let mr_pin_sha256 = sha256_bytes(&mr_pin_bytes);
    let mr_pin: MiniRustPinInput = serde_json::from_slice(&mr_pin_bytes).map_err(|err| {
        BundleError::Policy(format!(
            "malformed {MINIRUST_UPSTREAM_PIN_PATH} for provenance: {err}"
        ))
    })?;
    if mr_pin.upstream_repo.is_empty() || mr_pin.commit.is_empty() {
        return Err(BundleError::Policy(format!(
            "empty provenance metadata field in {MINIRUST_UPSTREAM_PIN_PATH}"
        )));
    }
    if !is_sha256_hex(&mr_pin.tarball_sha256) || !is_sha256_hex(&mr_pin.manifest_sha256) {
        return Err(BundleError::Policy(format!(
            "invalid SHA-256 metadata field in {MINIRUST_UPSTREAM_PIN_PATH}"
        )));
    }
    if mr_pin.file_count == 0 || mr_pin.files.len() != mr_pin.file_count {
        return Err(BundleError::Policy(format!(
            "invalid file_count ({}) vs files length ({}) in {MINIRUST_UPSTREAM_PIN_PATH}",
            mr_pin.file_count,
            mr_pin.files.len()
        )));
    }
    for (path, sha) in &mr_pin.files {
        if path.is_empty() || !is_sha256_hex(sha) {
            return Err(BundleError::Policy(format!(
                "invalid files provenance record in {MINIRUST_UPSTREAM_PIN_PATH}: {path:?}"
            )));
        }
    }
    let minirust_upstream = MiniRustProvenance {
        upstream_repository: mr_pin.upstream_repo,
        upstream_commit: mr_pin.commit,
        upstream_pin_sha256: mr_pin_sha256,
        tarball_sha256: mr_pin.tarball_sha256,
        manifest_sha256: mr_pin.manifest_sha256,
        file_count: mr_pin.file_count,
        files: mr_pin.files,
    };

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
        minirust_upstream,
        correspondence_adapters,
        correspondence_proofs,
        trusted_lean,
        note: CORRESPONDENCE_PROVENANCE_NOTE,
    };
    serde_json::to_string(&provenance).map_err(|err| {
        BundleError::Policy(format!("failed to serialize correspondence provenance: {err}"))
    })
}

/// Render the Pass 2 correspondence provenance record directly from the
/// canonical sources under `root`.
///
/// `anneal-audit` uses this to check the repository's Pass 2 inventory, and
/// CI checks that `ci/render_correspondence_provenance.py` (which renders the
/// archive's `share/anneal/correspondence-provenance.json`) agrees with it.
pub fn render_correspondence_provenance_from_checkout(root: &Path) -> Result<String, BundleError> {
    let mut trusted_lean = BTreeMap::new();
    for path in TRUSTED_BUNDLE_SOURCES {
        if path.starts_with(TRUSTED_LEAN_PREFIX) {
            let source_path = validate_bundle_source(root, path)?;
            let bytes = fs::read(source_path).map_err(BundleError::Io)?;
            trusted_lean.insert(*path, sha256_bytes(&bytes));
        }
    }
    render_correspondence_provenance(root, trusted_lean)
}

/// Holds rendered canonical bundle entries.
pub struct RenderedBundleParts {
    /// Ordered `(repo_rel_path, source_text)` entries matching `BUNDLE`.
    pub entries: Vec<(&'static str, String)>,
}

/// Validate canonical files in [`TRUSTED_BUNDLE_SOURCES`] under `root` and
/// return [`RenderedBundleParts`].
///
/// [`PROVENANCE_SOURCES`] are deliberately not read here, so Pass 2
/// correspondence edits never change (or invalidate) the `cargo-anneal`
/// binary.
pub fn render_bundled_resources_parts(root: &Path) -> Result<RenderedBundleParts, BundleError> {
    let mut entries = Vec::with_capacity(TRUSTED_BUNDLE_SOURCES.len());
    for path in TRUSTED_BUNDLE_SOURCES {
        let source_path = validate_bundle_source(root, path)?;
        let source = fs::read_to_string(source_path).map_err(BundleError::Io)?;
        entries.push((*path, source));
    }
    Ok(RenderedBundleParts { entries })
}

/// Render the exact expected contents of `bundled_resources.rs` (generated
/// into `$OUT_DIR/bundled_resources.rs` by `build.rs` or staged for standalone
/// `.crate` packaging) from the canonical regular files in
/// [`TRUSTED_BUNDLE_SOURCES`] under `root`.
pub fn render_bundled_resources(root: &Path) -> Result<String, BundleError> {
    let RenderedBundleParts { entries } = render_bundled_resources_parts(root)?;
    let mut generated = BUNDLE_HEADER.to_owned();
    for (path, source) in entries {
        // Rust's standard string formatter supplies valid Rust literal escapes.
        // The embedded bytes must equal the canonical UTF-8 source exactly.
        writeln!(generated, "    (\n        {path:?},\n        {source:?},\n    ),")
            .expect("writing to String cannot fail");
    }
    generated.push_str(BUNDLE_FOOTER);
    Ok(generated)
}

/// Output of [`resolve_build_script_bundle`]: the Cargo `rerun-if-changed`
/// paths to emit and the deterministic Rust source to write to `$OUT_DIR`.
// Consumed by `build.rs` (via `#[path]`) and unit tests in this module.
#[allow(dead_code)]
#[derive(Debug, PartialEq, Eq)]
pub struct BuildScriptPlan {
    /// Paths to emit as `cargo:rerun-if-changed=<path>` directives.
    pub rerun_if_changed: Vec<PathBuf>,
    /// Deterministic contents of `$OUT_DIR/bundled_resources.rs`.
    pub rendered_source: String,
}

/// Returns `true` when building `cargo-anneal` in its canonical repository
/// workspace (`../../trusted/cargo-anneal`) rather than from an unpacked
/// standalone crate archive.
///
/// Checking both canonical path equality against `workspace_root` and the
/// presence of at least one canonical TCB Lean root (`TrustedBoundary.lean` or
/// `Trusted.lean`) prevents a standalone unpacked archive whose temporary
/// parent happens to end in `trusted/cargo-anneal` from entering workspace
/// mode, while ensuring workspace builds still run (and fail closed inside
/// `render_bundled_resources`) when other canonical source files are missing.
#[allow(dead_code)]
pub fn is_anneal_workspace(manifest_dir: &Path, workspace_root: &Path) -> bool {
    let canonical_member = fs::canonicalize(workspace_root.join("trusted/cargo-anneal"));
    let canonical_manifest = fs::canonicalize(manifest_dir);
    let matches_workspace_member = match (canonical_member, canonical_manifest) {
        (Ok(member), Ok(manifest)) => member == manifest,
        _ => false,
    };
    matches_workspace_member
        && (fs::symlink_metadata(workspace_root.join("trusted/audit/TrustedBoundary.lean")).is_ok()
            || fs::symlink_metadata(workspace_root.join("trusted/lean/Trusted.lean")).is_ok())
}

/// Resolve workspace-vs-standalone mode, fail-closed bundle checks, and Cargo
/// `rerun-if-changed` paths for `trusted/cargo-anneal/build.rs`.
#[allow(dead_code)]
pub fn resolve_build_script_bundle(manifest_dir: &Path) -> Result<BuildScriptPlan, BundleError> {
    if fs::symlink_metadata(manifest_dir.join("src/bundled_resources.rs")).is_ok() {
        return Err(BundleError::Policy(
            "legacy checked-in src/bundled_resources.rs is forbidden; \
             build.rs generates $OUT_DIR/bundled_resources.rs"
                .to_owned(),
        ));
    }

    let workspace_root = manifest_dir.join("../..");
    let in_workspace = is_anneal_workspace(manifest_dir, &workspace_root);
    let packaged_exists = fs::symlink_metadata(manifest_dir.join("packaged")).is_ok();

    let mut rerun_if_changed = vec![
        PathBuf::from("build.rs"),
        PathBuf::from("src/trusted_bundle.rs"),
        PathBuf::from("src"),
    ];

    // Only watch `.` in workspace mode when `packaged/` does not yet exist:
    // Cargo walks directory watches recursively, so emitting `.` in standalone
    // builds where `target/` sits inside the package root would force a dirty
    // rebuild on every invocation. In workspace mode `target/` lives at
    // `anneal/target/` (outside `trusted/cargo-anneal/`), so watching `.`
    // catches a newly created `packaged/` directory while keeping clean builds
    // fresh. Once `packaged/` exists (or in standalone mode where it is
    // mandatory), watching `packaged` and `packaged/bundled_resources.rs`
    // directly suffices.
    if packaged_exists {
        rerun_if_changed.push(PathBuf::from("packaged"));
        rerun_if_changed.push(PathBuf::from(PACKAGED_BUNDLE_CRATE_REL));
    } else if in_workspace {
        rerun_if_changed.push(PathBuf::from("."));
    }

    if in_workspace {
        for rel in TRUSTED_BUNDLE_SOURCES {
            rerun_if_changed.push(workspace_root.join(rel));
        }

        let rendered_source = render_bundled_resources(&workspace_root)?;

        if packaged_exists {
            let (pkg_path, perms) =
                validate_destination_path(manifest_dir, PACKAGED_BUNDLE_CRATE_REL)?;
            if perms.is_none() {
                return Err(BundleError::Policy(format!(
                    "packaged/ directory exists without {PACKAGED_BUNDLE_CRATE_REL}; remove \
                     trusted/cargo-anneal/packaged first (for example: \
                     rm -rf trusted/cargo-anneal/packaged)"
                )));
            }
            let staged = fs::read(&pkg_path).map_err(BundleError::Io)?;
            if staged != rendered_source.as_bytes() {
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

        Ok(BuildScriptPlan { rerun_if_changed, rendered_source })
    } else {
        let (pkg_path, perms) = validate_destination_path(manifest_dir, PACKAGED_BUNDLE_CRATE_REL)?;
        if perms.is_none() {
            return Err(BundleError::Policy(format!(
                "missing {} for standalone cargo-anneal crate build",
                pkg_path.display()
            )));
        }
        let rendered_source = fs::read_to_string(&pkg_path).map_err(BundleError::Io)?;
        if !rendered_source.starts_with(BUNDLE_HEADER) || !rendered_source.ends_with(BUNDLE_FOOTER)
        {
            return Err(BundleError::Policy(format!(
                "malformed packaged bundle snapshot at {}",
                pkg_path.display()
            )));
        }
        Ok(BuildScriptPlan { rerun_if_changed, rendered_source })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn seed_synthetic_workspace_fixture(dest: &Path) -> PathBuf {
        let manifest_dir = dest.join("trusted/cargo-anneal");
        fs::create_dir_all(manifest_dir.join("src")).unwrap();
        for rel in TRUSTED_BUNDLE_SOURCES.iter().copied().chain(PROVENANCE_SOURCES.iter().copied())
        {
            let dst = dest.join(rel);
            if let Some(parent) = dst.parent() {
                fs::create_dir_all(parent).unwrap();
            }
            if rel == UPSTREAM_PIN_PATH {
                let pin = format!(
                    concat!(
                        "{{\n",
                        "  \"repository\": \"https://example.invalid/lean-miri\",\n",
                        "  \"commit\": \"0123456789abcdef0123456789abcdef01234567\",\n",
                        "  \"upstream_lean_toolchain\": \"leanprover/lean4:v4.34.1\",\n",
                        "  \"build_lean_toolchain\": \"leanprover/lean4:v4.34.1\",\n",
                        "  \"patched_files\": [\n",
                        "    {{\n",
                        "      \"path\": \"vendor/lean-miri/Example.lean\",\n",
                        "      \"upstream_sha256\": \"{}\",\n",
                        "      \"patched_sha256\": \"{}\"\n",
                        "    }}\n",
                        "  ]\n",
                        "}}\n"
                    ),
                    "a".repeat(64),
                    "b".repeat(64)
                );
                fs::write(&dst, pin).unwrap();
            } else if rel == MINIRUST_UPSTREAM_PIN_PATH {
                let pin = format!(
                    concat!(
                        "{{\n",
                        "  \"schema_version\": 1,\n",
                        "  \"upstream_repo\": \"https://example.invalid/minirust\",\n",
                        "  \"commit\": \"fedcba9876543210fedcba9876543210fedcba98\",\n",
                        "  \"tarball_sha256\": \"{}\",\n",
                        "  \"file_count\": 1,\n",
                        "  \"manifest_sha256\": \"{}\",\n",
                        "  \"files\": {{\n",
                        "    \"spec/lang/machine.md\": \"{}\"\n",
                        "  }}\n",
                        "}}\n"
                    ),
                    "c".repeat(64),
                    "d".repeat(64),
                    "e".repeat(64)
                );
                fs::write(&dst, pin).unwrap();
            } else {
                fs::write(&dst, format!("-- synthetic fixture for {rel}\n")).unwrap();
            }
        }
        manifest_dir
    }

    #[test]
    fn build_script_workspace_mode_and_fail_closed_packaged_guards() {
        let tmp = tempfile::tempdir().unwrap();
        let workspace_root = tmp.path().join("anneal");
        let manifest_dir = seed_synthetic_workspace_fixture(&workspace_root);

        // Clean workspace: enters workspace mode and watches `.` for packaged/,
        // but never watches Pass 2 correspondence inputs.
        let plan = resolve_build_script_bundle(&manifest_dir).unwrap();
        assert!(plan.rerun_if_changed.contains(&PathBuf::from(".")));
        assert!(plan.rerun_if_changed.contains(&PathBuf::from("src")));
        assert!(!plan.rerun_if_changed.contains(&PathBuf::from("packaged")));
        // Watches are spelled `<manifest_dir>/../../<rel>`, so match them by
        // component suffix rather than by an exact (differently spelled) path;
        // the trusted sources prove the predicate sees real watches.
        let watches = |rel: &str| plan.rerun_if_changed.iter().any(|p| p.ends_with(rel));
        for rel in TRUSTED_BUNDLE_SOURCES {
            assert!(watches(rel), "{rel}");
        }
        for rel in PROVENANCE_SOURCES
            .iter()
            .chain([&CORRESPONDENCE_ADAPTER_DIR, &CORRESPONDENCE_PROOF_DIR])
        {
            assert!(!watches(rel), "{rel}");
        }
        assert_eq!(plan.rendered_source, render_bundled_resources(&workspace_root).unwrap());
        assert!(!plan.rendered_source.contains("CORRESPONDENCE_PROVENANCE_JSON"));

        // Missing or malformed Pass 2 inputs do not affect the embedded bundle;
        // only checkout provenance rendering (used by `anneal-audit`) fails.
        let pin = workspace_root.join(UPSTREAM_PIN_PATH);
        let orig_pin = fs::read(&pin).unwrap();
        fs::write(&pin, b"not json").unwrap();
        assert_eq!(render_bundled_resources(&workspace_root).unwrap(), plan.rendered_source);
        let err = render_correspondence_provenance_from_checkout(&workspace_root).unwrap_err();
        assert!(err.to_string().contains("malformed vendor/lean-miri/UPSTREAM_PIN.json"), "{err}");
        fs::write(&pin, orig_pin).unwrap();
        render_correspondence_provenance_from_checkout(&workspace_root).unwrap();

        // Reintroduced legacy src/bundled_resources.rs fails closed.
        let legacy = manifest_dir.join("src/bundled_resources.rs");
        fs::write(&legacy, b"// legacy\n").unwrap();
        let err = resolve_build_script_bundle(&manifest_dir).unwrap_err();
        assert!(err.to_string().contains("legacy checked-in src/bundled_resources.rs"), "{err}");
        fs::remove_file(&legacy).unwrap();

        // Empty packaged/ directory fails closed with removal guidance.
        let packaged_dir = manifest_dir.join("packaged");
        fs::create_dir(&packaged_dir).unwrap();
        let err = resolve_build_script_bundle(&manifest_dir).unwrap_err();
        assert!(
            err.to_string().contains("packaged/ directory exists without")
                && err.to_string().contains("rm -rf trusted/cargo-anneal/packaged"),
            "{err}"
        );

        // Stale packaged/bundled_resources.rs fails closed with removal advice.
        let pkg_file = manifest_dir.join(PACKAGED_BUNDLE_CRATE_REL);
        fs::write(&pkg_file, b"// stale\n").unwrap();
        let err = resolve_build_script_bundle(&manifest_dir).unwrap_err();
        assert!(
            err.to_string().contains("is stale relative to canonical workspace sources")
                && err.to_string().contains("remove trusted/cargo-anneal/packaged first"),
            "{err}"
        );

        // Matching staged snapshot succeeds and watches `packaged` (not `.`).
        fs::write(&pkg_file, plan.rendered_source.as_bytes()).unwrap();
        let staged_plan = resolve_build_script_bundle(&manifest_dir).unwrap();
        assert!(!staged_plan.rerun_if_changed.contains(&PathBuf::from(".")));
        assert!(staged_plan.rerun_if_changed.contains(&PathBuf::from("packaged")));
        assert!(staged_plan.rerun_if_changed.contains(&PathBuf::from(PACKAGED_BUNDLE_CRATE_REL)));
        assert_eq!(staged_plan.rendered_source, plan.rendered_source);
    }

    #[test]
    fn build_script_standalone_mode_omits_dot_watch_and_fails_closed() {
        let tmp = tempfile::tempdir().unwrap();
        // Even if the unpacked directory happens to end in
        // `trusted/cargo-anneal`, the absence of canonical TCB Lean roots keeps
        // it in standalone mode.
        let manifest_dir = tmp.path().join("unpacked/trusted/cargo-anneal");
        fs::create_dir_all(manifest_dir.join("src")).unwrap();
        assert!(!is_anneal_workspace(&manifest_dir, &manifest_dir.join("../..")));

        // Missing packaged/ directory fails closed.
        let err = resolve_build_script_bundle(&manifest_dir).unwrap_err();
        assert!(err.to_string().contains("bundle parent must be a regular directory"), "{err}");

        // Empty packaged/ directory (missing snapshot) fails closed.
        let packaged_dir = manifest_dir.join("packaged");
        fs::create_dir(&packaged_dir).unwrap();
        let err = resolve_build_script_bundle(&manifest_dir).unwrap_err();
        assert!(err.to_string().contains("missing"), "{err}");

        // Malformed snapshots (missing header, unterminated `BUNDLE`, or a
        // legacy trailing provenance const) fail closed.
        let pkg_file = manifest_dir.join(PACKAGED_BUNDLE_CRATE_REL);
        fs::write(&pkg_file, BUNDLE_FOOTER.as_bytes()).unwrap();
        let err = resolve_build_script_bundle(&manifest_dir).unwrap_err();
        assert!(err.to_string().contains("malformed packaged bundle snapshot"), "{err}");

        fs::write(&pkg_file, BUNDLE_HEADER.as_bytes()).unwrap();
        let err = resolve_build_script_bundle(&manifest_dir).unwrap_err();
        assert!(err.to_string().contains("malformed packaged bundle snapshot"), "{err}");

        let legacy_snapshot = format!(
            "{BUNDLE_HEADER}{BUNDLE_FOOTER}\n\
             const CORRESPONDENCE_PROVENANCE_JSON: &str = \"{{}}\";\n"
        );
        fs::write(&pkg_file, legacy_snapshot.as_bytes()).unwrap();
        let err = resolve_build_script_bundle(&manifest_dir).unwrap_err();
        assert!(err.to_string().contains("malformed packaged bundle snapshot"), "{err}");

        // Valid standalone snapshot succeeds and MUST NOT emit `.` so in-place
        // builds with a crate-local `target/` remain fresh.
        let valid_snapshot = format!("{BUNDLE_HEADER}{BUNDLE_FOOTER}");
        fs::write(&pkg_file, valid_snapshot.as_bytes()).unwrap();
        let plan = resolve_build_script_bundle(&manifest_dir).unwrap();
        assert!(!plan.rerun_if_changed.contains(&PathBuf::from(".")));
        assert!(plan.rerun_if_changed.contains(&PathBuf::from("packaged")));
        assert!(plan.rerun_if_changed.contains(&PathBuf::from(PACKAGED_BUNDLE_CRATE_REL)));
        assert_eq!(plan.rendered_source, valid_snapshot);

        // Symlinked packaged/bundled_resources.rs fails closed.
        #[cfg(unix)]
        {
            let outside = tmp.path().join("outside.rs");
            fs::write(&outside, valid_snapshot.as_bytes()).unwrap();
            fs::remove_file(&pkg_file).unwrap();
            std::os::unix::fs::symlink(&outside, &pkg_file).unwrap();
            let err = resolve_build_script_bundle(&manifest_dir).unwrap_err();
            assert!(err.to_string().contains("regular file"), "{err}");
        }
    }

    #[test]
    fn minirust_upstream_pin_validation_fails_closed() {
        let tmp = tempfile::tempdir().unwrap();
        let workspace_root = tmp.path().join("anneal");
        seed_synthetic_workspace_fixture(&workspace_root);
        let mr_pin_path = workspace_root.join(MINIRUST_UPSTREAM_PIN_PATH);
        let valid = fs::read_to_string(&mr_pin_path).unwrap();

        let h = "a".repeat(64);
        let bad_cases = [
            (
                valid.replace("\"https://example.invalid/minirust\"", "\"\""),
                "empty provenance metadata field",
            ),
            (
                valid.replace("\"fedcba9876543210fedcba9876543210fedcba98\"", "\"\""),
                "empty provenance metadata field",
            ),
            (valid.replace(&"c".repeat(64), "not-sha256"), "invalid SHA-256 metadata field"),
            (valid.replace("\"file_count\": 1", "\"file_count\": 2"), "invalid file_count"),
            (valid.replace("\"file_count\": 1", "\"file_count\": 0"), "invalid file_count"),
            (valid.replace(&"e".repeat(64), "bad"), "invalid files provenance record"),
            (
                valid.replace("\"spec/lang/machine.md\"", "\"\""),
                "invalid files provenance record",
            ),
            (
                format!(
                    "{{\"upstream_repo\":\"r\",\"commit\":\"c\",\"tarball_sha256\":\"{h}\",\
                     \"file_count\":1,\"manifest_sha256\":\"{h}\",\
                     \"files\":{{\"a.md\":\"{h}\",\"a.md\":\"{h}\"}}}}"
                ),
                "duplicate files entry",
            ),
        ];
        for (payload, expected) in bad_cases {
            fs::write(&mr_pin_path, payload).unwrap();
            let err = match render_correspondence_provenance_from_checkout(&workspace_root) {
                Ok(_) => panic!("expected rejection containing {expected:?}"),
                Err(err) => err,
            };
            assert!(err.to_string().contains(expected), "expected {expected:?}, got: {err}");
        }

        fs::write(&mr_pin_path, valid).unwrap();
        assert!(render_correspondence_provenance_from_checkout(&workspace_root).is_ok());
    }
}
