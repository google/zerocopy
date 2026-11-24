// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Defines the canonical source inventory and deterministic rendering of
//! audited resources and bundled `theory/` libraries embedded into
//! `cargo-anneal`.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

use crate::toolchain::{is_clean_relative_path, is_lean_ident, sha256_bytes};

pub use crate::trusted_bundle::{
    BUNDLE_HEADER, BundleError, CORRESPONDENCE_ADAPTER_DIR, CORRESPONDENCE_ADAPTER_PATHS,
    CORRESPONDENCE_PROOF_DIR, CORRESPONDENCE_PROOF_PATHS, CORRESPONDENCE_PROVENANCE_NOTE,
    LEGACY_BUNDLE_DESTINATION, PACKAGED_BUNDLE_CRATE_REL, PACKAGED_BUNDLE_DESTINATION,
    PROVENANCE_SOURCES, RenderedBundleParts, TRUSTED_BUNDLE_SOURCES, UPSTREAM_PIN_PATH,
    prepare_packaged_bundle_destination, render_bundled_resources, render_bundled_resources_parts,
    render_correspondence_provenance, validate_bundle_source, validate_destination_path,
    validate_parent_directories,
};

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
