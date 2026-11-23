// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Split-plane crate specification packaging, circularity-free subject digests,
//! path-free `canonical_program_sha256` slice matching, and out-of-crate
//! `<crate>-anneal-proofs` evidence carrier verification.
//!
//! Plane 1 (`<crate>/anneal/anneal.toml`, `anneal/specs/**`,
//! `anneal/models/**`, and optional inline `#[cfg_attr(anneal, ...)]`
//! attributes in `src/**/*.rs`) ships declarative contracts inside
//! `<crate>.crate` with zero verifier runtime dependencies and zero MSRV
//! increase. Plane 2 (`<crate>-anneal-proofs` `#![no_std]` carrier crates or
//! `.tar.zst` archives) ships source proofs and Receipt v3 slices bound inward
//! to Plane 1 via `source_closure_sha256`, `contract_manifest_sha256`, and
//! `anneal_toml_sha256`.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    io::Read as _,
    path::{Component, Path, PathBuf},
    process::Command,
};

use flate2::read::GzDecoder;
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use walkdir::WalkDir;

use crate::toolchain::{
    Failure, is_clean_relative_path, is_lean_ident, is_sha256_hex, read_regular_file_strict,
    regular, sha256_bytes,
};

/// Maximum `crates.io` compressed `.crate` tarball size (`10 MiB`), matching
/// `MAX_UPLOAD_SIZE` in `rust-lang/crates.io@18a7cf31c481`
/// (`src/controllers/krate/publish/publish_limits.rs:31-38`).
pub const CRATES_IO_MAX_COMPRESSED_BYTES: u64 = 10 * 1024 * 1024;

/// Recommended Plane 1 contract directory budget (`64 KiB`) enforced as an
/// advisory/strict check by `cargo anneal package-check`.
pub const PLANE1_CONTRACT_MAX_BYTES: u64 = 64 * 1024;

/// Forbidden compiled Lean artifact extensions that must never appear inside
/// Plane 1 (`anneal/**`) or Plane 2 (`<crate>-anneal-proofs`) packages because
/// `.olean` headers lock exact Lean commit SHAs and C++ build configurations.
const FORBIDDEN_BINARY_LEAN_SUFFIXES: &[&str] =
    &[".olean", ".olean.server", ".olean.private", ".ilean", ".ir", ".ir.sig"];

/// Reserved Lean root namespaces that neither Plane 1 models/specs nor Plane 2
/// proof libraries may shadow.
const RESERVED_MODULE_ROOTS: &[&str] =
    &["Trusted", "Anneal", "Init", "Std", "Lean", "Lake", "TrustedBoundary"];

/// Recursively normalizes JSON object maps into sorted [`BTreeMap`] key order
/// and encodes compact UTF-8 bytes (RFC 8785 key-sorted JSON).
pub fn canonical_json_bytes(value: &Value) -> Result<Vec<u8>, Failure> {
    fn sort_value(v: &Value) -> Value {
        match v {
            Value::Array(items) => Value::Array(items.iter().map(sort_value).collect()),
            Value::Object(map) => {
                let mut sorted = serde_json::Map::new();
                let ordered: BTreeMap<&String, &Value> = map.iter().collect();
                for (k, val) in ordered {
                    sorted.insert(k.clone(), sort_value(val));
                }
                Value::Object(sorted)
            }
            other => other.clone(),
        }
    }
    serde_json::to_vec(&sort_value(value))
        .map_err(|e| Failure::operational("json", format!("canonical JSON encoding failed: {e}")))
}

/// Path-free target and compilation-profile parameters governing MIR semantics
/// (`anneal-canonical-program-v1`).
///
/// Field declaration order matches [`canonical_json_bytes`] keys.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticProfile {
    /// Whether `debug_assertions` was enabled during MIR construction.
    pub debug_assertions: bool,
    /// Target byte order (`"little"` or `"big"`).
    pub endian: String,
    /// Whether `-Zmir-preserve-ub` was active during MIR construction.
    pub mir_preserve_ub: bool,
    /// Optimization level (`0`..=`3`) observed on the compiler session.
    pub opt_level: u8,
    /// Whether integer `overflow_checks` were enabled.
    pub overflow_checks: bool,
    /// Panic strategy (`"unwind"` or `"abort"`).
    pub panic: String,
    /// Target pointer width in bits (for example `64`).
    pub pointer_bits: u64,
    /// Target triple string (for example `"x86_64-unknown-linux-gnu"`).
    pub target: String,
}

impl SemanticProfile {
    /// Extracts a [`SemanticProfile`] from a `capture.json` `configuration`
    /// object, failing closed if any required semantic field is absent or
    /// malformed.
    pub fn from_capture_configuration(cfg: &Value) -> Result<Self, Failure> {
        let req_bool = |key: &str| -> Result<bool, Failure> {
            cfg.get(key).and_then(Value::as_bool).ok_or_else(|| {
                Failure::operational(
                    "capture",
                    format!("capture configuration missing boolean field `{key}`"),
                )
            })
        };
        let req_str = |key: &str| -> Result<String, Failure> {
            cfg.get(key)
                .and_then(Value::as_str)
                .filter(|s| !s.is_empty())
                .map(str::to_owned)
                .ok_or_else(|| {
                    Failure::operational(
                        "capture",
                        format!("capture configuration missing string field `{key}`"),
                    )
                })
        };
        let opt_u64 = cfg.get("opt_level").and_then(Value::as_u64).ok_or_else(|| {
            Failure::operational("capture", "capture configuration missing `opt_level`")
        })?;
        let opt_level = u8::try_from(opt_u64).map_err(|_| {
            Failure::operational("capture", format!("invalid `opt_level`: {opt_u64}"))
        })?;
        let pointer_bits = cfg.get("pointer_bits").and_then(Value::as_u64).ok_or_else(|| {
            Failure::operational("capture", "capture configuration missing `pointer_bits`")
        })?;
        Ok(Self {
            debug_assertions: req_bool("debug_assertions")?,
            endian: req_str("endian")?,
            mir_preserve_ub: req_bool("mir_preserve_ub")?,
            opt_level,
            overflow_checks: req_bool("overflow_checks")?,
            panic: req_str("panic")?,
            pointer_bits,
            target: req_str("target")?,
        })
    }

    /// Formats field-by-field differences against `other` for slice-mismatch
    /// diagnostics.
    pub fn diff_summary(&self, other: &Self) -> Vec<String> {
        let mut diffs = Vec::new();
        if self.target != other.target {
            diffs.push(format!("target: consumer={} vs slice={}", self.target, other.target));
        }
        if self.opt_level != other.opt_level {
            diffs.push(format!(
                "opt_level: consumer={} vs slice={}",
                self.opt_level, other.opt_level
            ));
        }
        if self.debug_assertions != other.debug_assertions {
            diffs.push(format!(
                "debug_assertions: consumer={} vs slice={}",
                self.debug_assertions, other.debug_assertions
            ));
        }
        if self.overflow_checks != other.overflow_checks {
            diffs.push(format!(
                "overflow_checks: consumer={} vs slice={}",
                self.overflow_checks, other.overflow_checks
            ));
        }
        if self.mir_preserve_ub != other.mir_preserve_ub {
            diffs.push(format!(
                "mir_preserve_ub: consumer={} vs slice={}",
                self.mir_preserve_ub, other.mir_preserve_ub
            ));
        }
        if self.panic != other.panic {
            diffs.push(format!("panic: consumer={} vs slice={}", self.panic, other.panic));
        }
        if self.pointer_bits != other.pointer_bits {
            diffs.push(format!(
                "pointer_bits: consumer={} vs slice={}",
                self.pointer_bits, other.pointer_bits
            ));
        }
        if self.endian != other.endian {
            diffs.push(format!("endian: consumer={} vs slice={}", self.endian, other.endian));
        }
        diffs
    }
}

/// Computes `canonical_program_sha256` (`anneal-canonical-program-v1`) over
/// `semantic_profile` and the raw `program` JSON value from `capture.json`.
pub fn compute_canonical_program_sha256(
    semantic_profile: &SemanticProfile,
    program: &Value,
) -> Result<String, Failure> {
    if !program.is_object() {
        return Err(Failure::operational("capture", "capture `program` must be a JSON object"));
    }
    let envelope = json!({
        "program": program,
        "schema": "anneal-canonical-program-v1",
        "semantic_profile": semantic_profile,
    });
    let bytes = canonical_json_bytes(&envelope)?;
    Ok(sha256_bytes(&bytes))
}

/// Concrete generic instantiation entry inside `anneal/anneal.toml` scopes.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ManifestInstantiation {
    /// Uninstantiated generic item path.
    pub path: String,
    /// Concrete type/lifetime/const arguments.
    pub args: Vec<String>,
}

/// Verification unit scope inside `anneal/anneal.toml`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum ManifestScope {
    /// Selected-unit verification over named function roots.
    SelectedUnit {
        /// Non-empty set of selected root item paths.
        roots: BTreeSet<String>,
        /// Optional concrete generic instantiations.
        #[serde(default, skip_serializing_if = "BTreeSet::is_empty")]
        instantiations: BTreeSet<ManifestInstantiation>,
    },
    /// Whole-crate verification scope.
    Crate {},
}

/// Plane 1 `anneal/anneal.toml` contract manifest (`schema_version = 1`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AnnealManifest {
    /// Must equal `1`.
    pub schema_version: u32,
    /// Package-level contract compatibility metadata.
    pub package: ManifestPackageSection,
    /// Optional out-of-crate evidence carrier discovery metadata.
    #[serde(default)]
    pub evidence: Option<ManifestEvidenceSection>,
    /// Optional shared declarative Lean domain models (`Role::SpecModel`).
    #[serde(default)]
    pub models: Vec<ManifestLeanModule>,
    /// Named verification units declared by this crate.
    #[serde(default)]
    pub units: Vec<ManifestUnit>,
    /// Named `(target, features, cfg, panic)` compilation slices.
    #[serde(default)]
    pub slices: BTreeMap<String, ManifestSlice>,
}

/// `[package]` section of `anneal/anneal.toml`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ManifestPackageSection {
    /// Contract syntax (`"anneal-surface-v1"` or `"anneal-lean-v1"`).
    pub spec_format: String,
    /// Optional Lean version compatibility range (required when `.lean` models
    /// or Lean specification modules are shipped in Plane 1).
    #[serde(default)]
    pub lean_compat: Option<String>,
    /// MIR model schema version (`1`).
    pub mir_model_schema: u32,
}

/// `[evidence]` section of `anneal/anneal.toml`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ManifestEvidenceSection {
    /// Default companion `#![no_std]` evidence carrier crate name.
    pub carrier_crate: String,
    /// Optional release `.tar.zst` URL template for Stage 0 archive consumers.
    #[serde(default)]
    pub archive_url_template: Option<String>,
}

/// Declarative Lean module mapping under `anneal/`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ManifestLeanModule {
    /// Dotted Lean module name (`Spec`, `LayoutModel`, etc.).
    pub module: String,
    /// Clean relative path under `<crate>/anneal/` ending in `.lean`.
    pub path: String,
}

fn default_spec_decl() -> String {
    "Spec.specs".to_owned()
}

/// One `[[units]]` entry in `anneal/anneal.toml`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ManifestUnit {
    /// Unique ASCII unit identifier (`01_usize_pointer_metadata`, etc.).
    pub id: String,
    /// Verification scope (`selected_unit` or `crate`).
    pub scope: ManifestScope,
    /// Qualified Lean specification declaration (defaults to `"Spec.specs"`).
    #[serde(default = "default_spec_decl")]
    pub specification: String,
    /// Optional explicit specification module override.
    #[serde(default)]
    pub specification_module: Option<String>,
    /// Out-of-`src/` Rust surface specification files (`specs/*.rs`) under
    /// `<crate>/anneal/`.
    #[serde(default)]
    pub surface_specs: Vec<String>,
    /// Per-unit declarative Lean specification modules (`specs/*.lean`) under
    /// `<crate>/anneal/`.
    #[serde(default)]
    pub spec_modules: Vec<ManifestLeanModule>,
    /// Names of package-level `[[models]]` modules imported by this unit.
    #[serde(default)]
    pub models: Vec<String>,
}

fn default_panic_unwind() -> String {
    "unwind".to_owned()
}

/// One `[slices.<id>]` entry in `anneal/anneal.toml`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ManifestSlice {
    /// Target triple (for example `"x86_64-unknown-linux-gnu"`).
    pub target: String,
    /// Cargo feature names enabled in this slice.
    #[serde(default)]
    pub features: Vec<String>,
    /// Whether Cargo `default` features are enabled (defaults to `false`).
    #[serde(default)]
    pub default_features: bool,
    /// Additional explicit `--cfg` flags for standalone `rustc` capture.
    #[serde(default)]
    pub cfg: Vec<String>,
    /// Panic strategy (`"unwind"` or `"abort"`).
    #[serde(default = "default_panic_unwind")]
    pub panic: String,
}

fn is_valid_unit_or_slice_id(id: &str) -> bool {
    !id.is_empty()
        && id.len() <= 128
        && id.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'-')
}

fn is_valid_crate_name(name: &str) -> bool {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first.is_ascii_alphabetic() || first == '_')
        && name.len() <= 64
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '-')
}

fn is_valid_non_reserved_lean_module(module: &str) -> bool {
    if module.is_empty() || matches!(module, "Expected" | "Captured") {
        return false;
    }
    if !module.split('.').all(is_lean_ident) {
        return false;
    }
    let root = module.split('.').next().unwrap_or("");
    !RESERVED_MODULE_ROOTS.contains(&root)
}

impl AnnealManifest {
    /// Parses and validates `anneal/anneal.toml` bytes.
    pub fn parse_and_validate(text: &str) -> Result<Self, Failure> {
        let manifest: Self = toml::from_str(text)
            .map_err(|e| Failure::policy("anneal-manifest", format!("invalid anneal.toml: {e}")))?;
        manifest.validate()?;
        Ok(manifest)
    }

    /// Enforces structural, role-separation, and path-hygiene invariants on
    /// `anneal/anneal.toml`.
    pub fn validate(&self) -> Result<(), Failure> {
        let phase = "anneal-manifest";
        if self.schema_version != 1 {
            return Err(Failure::policy(
                phase,
                format!(
                    "unsupported anneal.toml schema_version {} (expected 1)",
                    self.schema_version
                ),
            ));
        }
        if !matches!(self.package.spec_format.as_str(), "anneal-surface-v1" | "anneal-lean-v1") {
            return Err(Failure::policy(
                phase,
                format!(
                    "unsupported package.spec_format {:?} (expected \"anneal-surface-v1\" or \"anneal-lean-v1\")",
                    self.package.spec_format
                ),
            ));
        }
        if self.package.mir_model_schema != 1 {
            return Err(Failure::policy(
                phase,
                format!(
                    "unsupported package.mir_model_schema {} (expected 1)",
                    self.package.mir_model_schema
                ),
            ));
        }
        if let Some(ev) = &self.evidence
            && !is_valid_crate_name(&ev.carrier_crate)
        {
            return Err(Failure::policy(
                phase,
                format!("invalid evidence.carrier_crate {:?}", ev.carrier_crate),
            ));
        }

        let has_lean_files =
            !self.models.is_empty() || self.units.iter().any(|u| !u.spec_modules.is_empty());
        if has_lean_files && self.package.lean_compat.as_deref().is_none_or(|s| s.trim().is_empty())
        {
            return Err(Failure::policy(
                phase,
                "package.lean_compat is required when Plane 1 ships .lean models or spec_modules",
            ));
        }

        let mut model_modules = BTreeSet::new();
        for model in &self.models {
            validate_plane1_lean_module(model, phase)?;
            if !model_modules.insert(model.module.as_str()) {
                return Err(Failure::policy(
                    phase,
                    format!("duplicate [[models]] module `{}`", model.module),
                ));
            }
        }

        if self.units.is_empty() {
            return Err(Failure::policy(
                phase,
                "anneal.toml must declare at least one [[units]] entry",
            ));
        }
        let mut unit_ids = BTreeSet::new();
        for unit in &self.units {
            if !is_valid_unit_or_slice_id(&unit.id) {
                return Err(Failure::policy(phase, format!("invalid unit id {:?}", unit.id)));
            }
            if !unit_ids.insert(unit.id.as_str()) {
                return Err(Failure::policy(
                    phase,
                    format!("duplicate [[units]] id `{}`", unit.id),
                ));
            }
            if let ManifestScope::SelectedUnit { roots, .. } = &unit.scope
                && (roots.is_empty() || roots.iter().any(|r| r.trim().is_empty()))
            {
                return Err(Failure::policy(
                    phase,
                    format!("unit `{}` selected_unit scope must list non-empty roots", unit.id),
                ));
            }
            if !unit.specification.contains('.')
                || !unit.specification.split('.').all(is_lean_ident)
            {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "unit `{}` has invalid specification declaration {:?}",
                        unit.id, unit.specification
                    ),
                ));
            }
            if let Some(spec_mod) = &unit.specification_module
                && !is_valid_non_reserved_lean_module(spec_mod)
            {
                return Err(Failure::policy(
                    phase,
                    format!("unit `{}` has invalid specification_module {:?}", unit.id, spec_mod),
                ));
            }
            if unit.surface_specs.is_empty() && unit.spec_modules.is_empty() {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "unit `{}` must declare at least one entry in `surface_specs` or `spec_modules`",
                        unit.id
                    ),
                ));
            }
            for surf in &unit.surface_specs {
                validate_plane1_rel_path(surf, ".rs", phase)?;
            }
            let mut unit_mods = BTreeSet::new();
            for sm in &unit.spec_modules {
                validate_plane1_lean_module(sm, phase)?;
                if model_modules.contains(sm.module.as_str())
                    || !unit_mods.insert(sm.module.as_str())
                {
                    return Err(Failure::policy(
                        phase,
                        format!(
                            "unit `{}` has duplicate or shadowing Lean module `{}`",
                            unit.id, sm.module
                        ),
                    ));
                }
            }
            for model_ref in &unit.models {
                if !model_modules.contains(model_ref.as_str()) {
                    return Err(Failure::policy(
                        phase,
                        format!("unit `{}` references undeclared model `{model_ref}`", unit.id),
                    ));
                }
            }
        }

        if self.slices.is_empty() {
            return Err(Failure::policy(
                phase,
                "anneal.toml must declare at least one `[slices.<id>]` entry",
            ));
        }
        for (slice_id, slice) in &self.slices {
            if !is_valid_unit_or_slice_id(slice_id) {
                return Err(Failure::policy(phase, format!("invalid slice id {slice_id:?}")));
            }
            if slice.target.trim().is_empty() {
                return Err(Failure::policy(
                    phase,
                    format!("slice `{slice_id}` target must not be empty"),
                ));
            }
            if !matches!(slice.panic.as_str(), "unwind" | "abort") {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "slice `{slice_id}` panic strategy must be \"unwind\" or \"abort\", got {:?}",
                        slice.panic
                    ),
                ));
            }
        }
        Ok(())
    }
}

fn validate_plane1_rel_path(rel: &str, expected_ext: &str, phase: &str) -> Result<(), Failure> {
    if !is_clean_relative_path(rel) || !rel.ends_with(expected_ext) {
        return Err(Failure::policy(
            phase,
            format!("Plane 1 path must be a clean relative `{expected_ext}` path: {rel:?}"),
        ));
    }
    let lower = rel.to_ascii_lowercase();
    if lower == "proof.lean"
        || lower.ends_with("/proof.lean")
        || lower.starts_with("proofs/")
        || FORBIDDEN_BINARY_LEAN_SUFFIXES.iter().any(|ext| lower.ends_with(ext))
    {
        return Err(Failure::policy(
            phase,
            format!(
                "E_ANNEAL_PROOF_IN_CONTRACT_PLANE: forbidden proof or binary artifact in Plane 1: {rel}"
            ),
        ));
    }
    Ok(())
}

fn validate_plane1_lean_module(entry: &ManifestLeanModule, phase: &str) -> Result<(), Failure> {
    if !is_valid_non_reserved_lean_module(&entry.module)
        || entry.module == "Proof"
        || entry.module.starts_with("Proof.")
    {
        return Err(Failure::policy(
            phase,
            format!("invalid or reserved Plane 1 Lean module identifier: {:?}", entry.module),
        ));
    }
    validate_plane1_rel_path(&entry.path, ".lean", phase)
}

/// Computes a globally collision-free Lean module root for an upstream Cargo
/// compilation unit (`Deps.C_<pkg>_<ver>_<hex8>`), disambiguating SemVer-major
/// diamonds such as `zerocopy 0.7.35` alongside `zerocopy 0.8.64`.
pub fn disambiguated_dep_namespace(
    crate_name: &str,
    version: &str,
    stable_id_seed: &str,
) -> Result<String, Failure> {
    if !is_valid_crate_name(crate_name) {
        return Err(Failure::policy("dep-namespace", format!("invalid crate name {crate_name:?}")));
    }
    if version.is_empty() {
        return Err(Failure::policy("dep-namespace", "crate version must not be empty"));
    }
    let sanitize = |s: &str| -> String {
        s.chars().map(|c| if c.is_ascii_alphanumeric() { c } else { '_' }).collect()
    };
    let hash_input = format!("anneal-dep-id-v1\0{crate_name}\0{version}\0{stable_id_seed}");
    let hex8 = &sha256_bytes(hash_input.as_bytes())[..8];
    let root = format!("Deps.C_{}_{}_{}", sanitize(crate_name), sanitize(version), hex8);
    if !root.split('.').all(is_lean_ident) {
        return Err(Failure::operational(
            "dep-namespace",
            format!("generated invalid Lean namespace `{root}`"),
        ));
    }
    Ok(root)
}

/// Validates `<crate>-anneal-proofs` independent SemVer versioning
/// (`<ev_major>.<ev_minor>.<ev_patch>[+<crate>.<crate_ver>]`).
///
/// Build metadata (`+...`) is optional or informational, but when present must
/// match `<crate>.<crate_ver>` so mis-tagged carrier manifests fail early.
pub fn validate_evidence_carrier_version(
    evidence_version: &str,
    subject_crate: &str,
    subject_version: &str,
) -> Result<(), Failure> {
    let phase = "evidence-semver";
    let (core_and_pre, build_meta) = match evidence_version.split_once('+') {
        Some((lhs, rhs)) => (lhs, Some(rhs)),
        None => (evidence_version, None),
    };
    let core = core_and_pre.split('-').next().unwrap_or("");
    let parts: Vec<&str> = core.split('.').collect();
    if parts.len() != 3 || parts.iter().any(|p| p.is_empty() || p.parse::<u64>().is_err()) {
        return Err(Failure::policy(
            phase,
            format!("invalid SemVer version on evidence carrier: {evidence_version:?}"),
        ));
    }
    if let Some(meta) = build_meta {
        let expected_meta = format!(
            "{subject_crate}.{}",
            subject_version.split('+').next().unwrap_or(subject_version)
        );
        if meta != expected_meta {
            return Err(Failure::policy(
                phase,
                format!(
                    "evidence carrier version build metadata `+{meta}` does not match `+{expected_meta}`"
                ),
            ));
        }
    }
    Ok(())
}

/// Computed `anneal-source-closure-v1` digest and file inventory.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceClosureReport {
    /// Hex SHA-256 digest of the canonical `anneal-source-closure-v1` JSON.
    pub source_closure_sha256: String,
    /// Sorted `(rel_path, sha256)` pairs covered by the closure.
    pub files: Vec<(String, String)>,
}

/// Recomputes `source_closure_sha256` (`anneal-source-closure-v1`) directly
/// from `<crate_dir>` using strict non-symlink regular-file reads.
///
/// Walks `<crate_dir>/src/**` completely (detecting both modified files and
/// undeclared injected files even when `.cargo-checksum.json` is cleared to
/// `{"files":{}}`), plus `build.rs` when present and any `extra_rel_files`
/// outside `anneal/**` and `proofs/**`. Never hashes `Cargo.toml`,
/// `Cargo.toml.orig`, `Cargo.lock`, `.cargo_vcs_info.json`, or
/// `.cargo-checksum.json`, preserving byte-for-byte parity across Git,
/// `cargo package`, and `cargo vendor`. Instead, `cargo_semantics` (see
/// [`ValidatedCargoPackage::cargo_semantics`]) binds the parsed manifest
/// fields that change the compiled program.
pub fn compute_source_closure_sha256(
    crate_dir: &Path,
    crate_name: &str,
    edition: &str,
    cargo_semantics: &Value,
    extra_rel_files: &[String],
) -> Result<SourceClosureReport, Failure> {
    let phase = "source-closure";
    let crate_meta = fs::symlink_metadata(crate_dir).map_err(|e| {
        Failure::operational(phase, format!("cannot inspect {}: {e}", crate_dir.display()))
    })?;
    if crate_meta.file_type().is_symlink() || !crate_meta.is_dir() {
        return Err(Failure::policy(
            phase,
            format!("crate root must be a real directory: {}", crate_dir.display()),
        ));
    }

    let mut inventory: BTreeMap<String, String> = BTreeMap::new();

    let build_rs = crate_dir.join("build.rs");
    match fs::symlink_metadata(&build_rs) {
        Ok(_) => {
            let (_, sha) = read_regular_file_strict(&build_rs, None, phase)?;
            inventory.insert("build.rs".to_owned(), sha);
        }
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
        Err(e) => {
            return Err(Failure::operational(
                phase,
                format!("cannot inspect {}: {e}", build_rs.display()),
            ));
        }
    }

    let src_dir = crate_dir.join("src");
    let src_meta = fs::symlink_metadata(&src_dir).map_err(|e| {
        Failure::policy(
            phase,
            format!("missing or unreadable `src/` directory {}: {e}", src_dir.display()),
        )
    })?;
    if src_meta.file_type().is_symlink() || !src_meta.is_dir() {
        return Err(Failure::policy(
            phase,
            format!("`src/` must be a real directory, not a symlink: {}", src_dir.display()),
        ));
    }

    for entry in WalkDir::new(&src_dir).follow_links(false) {
        let entry = entry.map_err(|e| {
            Failure::operational(phase, format!("error walking {}: {e}", src_dir.display()))
        })?;
        let path = entry.path();
        if path == src_dir {
            continue;
        }
        let ft = entry.file_type();
        if ft.is_symlink() {
            return Err(Failure::policy(
                phase,
                format!(
                    "E_ANNEAL_SOURCE_CLOSURE_MISMATCH: symlink forbidden under src/: {}",
                    path.display()
                ),
            ));
        }
        if ft.is_dir() {
            continue;
        }
        if !ft.is_file() {
            return Err(Failure::policy(
                phase,
                format!("non-regular file forbidden under src/: {}", path.display()),
            ));
        }
        let rel = path.strip_prefix(crate_dir).map_err(|_| {
            Failure::operational(phase, format!("path escaped crate root: {}", path.display()))
        })?;
        let rel_utf8 = rel_path_to_posix_utf8(rel, phase)?;
        let (_, sha) = read_regular_file_strict(path, None, phase)?;
        inventory.insert(rel_utf8, sha);
    }

    for extra in extra_rel_files {
        if !is_clean_relative_path(extra)
            || extra.starts_with("anneal/")
            || extra.starts_with("proofs/")
            || matches!(
                extra.as_str(),
                "Cargo.toml"
                    | "Cargo.toml.orig"
                    | "Cargo.lock"
                    | ".cargo_vcs_info.json"
                    | ".cargo-checksum.json"
            )
        {
            return Err(Failure::policy(
                phase,
                format!("invalid extra source-closure path: {extra:?}"),
            ));
        }
        let full = verify_no_symlink_ancestors(crate_dir, Path::new(extra), phase)?;
        let (_, sha) = read_regular_file_strict(&full, None, phase)?;
        inventory.insert(extra.clone(), sha);
    }

    let files: Vec<(String, String)> = inventory.into_iter().collect();
    let payload = json!({
        "cargo": cargo_semantics,
        "crate_name": crate_name,
        "edition": edition,
        "files": files,
        "schema": "anneal-source-closure-v1",
    });
    let canonical = canonical_json_bytes(&payload)?;
    Ok(SourceClosureReport { source_closure_sha256: sha256_bytes(&canonical), files })
}

fn rel_path_to_posix_utf8(rel: &Path, phase: &str) -> Result<String, Failure> {
    let mut parts = Vec::new();
    for comp in rel.components() {
        match comp {
            Component::Normal(os) => {
                let s = os.to_str().ok_or_else(|| {
                    Failure::policy(
                        phase,
                        format!("non-UTF-8 path in crate closure: {}", rel.display()),
                    )
                })?;
                if s.is_empty() {
                    return Err(Failure::policy(phase, "empty path component"));
                }
                parts.push(s);
            }
            _ => {
                return Err(Failure::policy(
                    phase,
                    format!("non-normal relative path component in {}", rel.display()),
                ));
            }
        }
    }
    if parts.is_empty() {
        return Err(Failure::policy(phase, "empty relative path"));
    }
    Ok(parts.join("/"))
}

fn verify_no_symlink_ancestors(root: &Path, rel: &Path, phase: &str) -> Result<PathBuf, Failure> {
    let mut cur = root.to_path_buf();
    let comps: Vec<_> = rel.components().collect();
    for (idx, comp) in comps.iter().enumerate() {
        let Component::Normal(seg) = comp else {
            return Err(Failure::policy(
                phase,
                format!("non-normal path segment in {}", rel.display()),
            ));
        };
        cur.push(seg);
        let meta = fs::symlink_metadata(&cur).map_err(|e| {
            Failure::policy(phase, format!("cannot inspect {}: {e}", cur.display()))
        })?;
        if meta.file_type().is_symlink() {
            return Err(Failure::policy(
                phase,
                format!("symlink forbidden in packaged tree: {}", cur.display()),
            ));
        }
        if idx + 1 < comps.len() && !meta.is_dir() {
            return Err(Failure::policy(
                phase,
                format!("expected directory component: {}", cur.display()),
            ));
        }
    }
    Ok(cur)
}

fn raw_string_open_len(bytes: &[u8], i: usize) -> Option<(usize, usize)> {
    // Only recognize raw strings not attached to a preceding identifier.
    if i > 0 && (bytes[i - 1].is_ascii_alphanumeric() || bytes[i - 1] == b'_') {
        return None;
    }
    let rest = &bytes[i..];
    let prefix_len = if rest.starts_with(b"br")
        || rest.starts_with(b"rb")
        || rest.starts_with(b"cr")
        || rest.starts_with(b"rc")
    {
        2
    } else if rest.starts_with(b"r") {
        1
    } else {
        return None;
    };
    let mut hashes = 0usize;
    while i + prefix_len + hashes < bytes.len() && bytes[i + prefix_len + hashes] == b'#' {
        hashes += 1;
    }
    if bytes.get(i + prefix_len + hashes) == Some(&b'"') {
        Some((prefix_len + hashes + 1, hashes))
    } else {
        None
    }
}

fn char_or_byte_literal_end(bytes: &[u8], i: usize) -> Option<usize> {
    let start = if i + 1 < bytes.len()
        && bytes[i] == b'b'
        && bytes[i + 1] == b'\''
        && (i == 0 || !(bytes[i - 1].is_ascii_alphanumeric() || bytes[i - 1] == b'_'))
    {
        i + 1
    } else if bytes.get(i) == Some(&b'\'') {
        i
    } else {
        return None;
    };
    let next = *bytes.get(start + 1)?;
    if next == b'\\' {
        // Escaped char/byte literal: scan until matching `'` on the same line.
        let mut k = start + 2;
        while k < bytes.len() && bytes[k] != b'\n' && k - start <= 16 {
            if bytes[k] == b'\\' {
                k = (k + 2).min(bytes.len());
                continue;
            }
            if bytes[k] == b'\'' {
                return Some(k + 1);
            }
            k += 1;
        }
        return None;
    }
    if next == b'\'' || next == b'\n' || next == b'\r' {
        return None;
    }
    // Single-scalar literal `'x'` (never consumes `'a` lifetimes).
    let tail = std::str::from_utf8(&bytes[start + 1..]).ok()?;
    let ch = tail.chars().next()?;
    let close_idx = start + 1 + ch.len_utf8();
    if bytes.get(close_idx) == Some(&b'\'') { Some(close_idx + 1) } else { None }
}

/// Advances past a Rust comment or literal starting at `i`, returning
/// `(next_index, is_comment)` when consumed.
fn consume_rust_comment_or_literal(bytes: &[u8], i: usize) -> Option<(usize, bool)> {
    if i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'/' {
        let mut k = i + 2;
        while k < bytes.len() && bytes[k] != b'\n' {
            k += 1;
        }
        return Some((k, true));
    }
    if i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'*' {
        let mut k = i + 2;
        let mut depth = 1usize;
        while k < bytes.len() && depth > 0 {
            if k + 1 < bytes.len() && bytes[k] == b'/' && bytes[k + 1] == b'*' {
                depth += 1;
                k += 2;
            } else if k + 1 < bytes.len() && bytes[k] == b'*' && bytes[k + 1] == b'/' {
                depth -= 1;
                k += 2;
            } else {
                k += 1;
            }
        }
        return Some((k, true));
    }
    if let Some((open_len, hashes)) = raw_string_open_len(bytes, i) {
        let mut k = i + open_len;
        while k < bytes.len() {
            if bytes[k] == b'"'
                && k + 1 + hashes <= bytes.len()
                && bytes[k + 1..k + 1 + hashes].iter().all(|&b| b == b'#')
            {
                return Some((k + 1 + hashes, false));
            }
            k += 1;
        }
        return Some((bytes.len(), false));
    }
    if let Some(end) = char_or_byte_literal_end(bytes, i) {
        return Some((end, false));
    }
    if bytes[i] == b'"' {
        let mut k = i + 1;
        while k < bytes.len() {
            if bytes[k] == b'\\' {
                k = (k + 2).min(bytes.len());
            } else if bytes[k] == b'"' {
                return Some((k + 1, false));
            } else {
                k += 1;
            }
        }
        return Some((bytes.len(), false));
    }
    None
}

/// Scans `rust_src` for top-level inline `#[cfg_attr(anneal, ...)]` or
/// `#![cfg_attr(anneal, ...)]` attributes and canonicalizes whitespace so
/// edits outside contracts do not perturb `contract_manifest_sha256`, while
/// any contract token edit changes the digest.
pub fn extract_inline_anneal_cfg_attrs(rust_src: &str) -> Vec<String> {
    let bytes = rust_src.as_bytes();
    let mut i = 0;
    let mut extracted = Vec::new();
    while i < bytes.len() {
        if let Some((next, _)) = consume_rust_comment_or_literal(bytes, i) {
            i = next;
            continue;
        }
        if bytes[i] == b'#' {
            let start = i;
            i += 1;
            while i < bytes.len() && bytes[i].is_ascii_whitespace() {
                i += 1;
            }
            if i < bytes.len() && bytes[i] == b'!' {
                i += 1;
                while i < bytes.len() && bytes[i].is_ascii_whitespace() {
                    i += 1;
                }
            }
            if i < bytes.len() && bytes[i] == b'[' {
                let mut depth = 1usize;
                i += 1;
                while i < bytes.len() && depth > 0 {
                    if let Some((next, _)) = consume_rust_comment_or_literal(bytes, i) {
                        i = next;
                        continue;
                    }
                    if bytes[i] == b'[' {
                        depth += 1;
                    } else if bytes[i] == b']' {
                        depth -= 1;
                    }
                    i += 1;
                }
                if depth == 0 {
                    let normalized = normalize_attr_tokens(&rust_src[start..i]);
                    if normalized.starts_with("#[cfg_attr(anneal,")
                        || normalized.starts_with("#![cfg_attr(anneal,")
                    {
                        extracted.push(normalized);
                    }
                }
                continue;
            }
        }
        i += 1;
    }
    extracted
}

fn normalize_attr_tokens(raw: &str) -> String {
    let bytes = raw.as_bytes();
    let mut out = String::new();
    let mut prev_space = false;
    let mut i = 0usize;
    while i < bytes.len() {
        if let Some((next, is_comment)) = consume_rust_comment_or_literal(bytes, i) {
            if is_comment {
                prev_space = true;
            } else {
                if prev_space && !out.is_empty() && !out.ends_with(['(', '[', '{', ',', '#', '!'])
                {
                    out.push(' ');
                }
                prev_space = false;
                out.push_str(&raw[i..next]);
            }
            i = next;
            continue;
        }
        let ch = raw[i..].chars().next().unwrap();
        let next = i + ch.len_utf8();
        if ch.is_whitespace() {
            prev_space = true;
            i = next;
            continue;
        }
        let is_punct =
            matches!(ch, '(' | ')' | '[' | ']' | '{' | '}' | ',' | ':' | ';' | '#' | '!');
        if prev_space && !is_punct && !out.is_empty() {
            let last = out.chars().last().unwrap_or(' ');
            if !matches!(last, '(' | '[' | '{' | ',' | ':' | ';' | '#' | '!') {
                out.push(' ');
            }
        }
        prev_space = false;
        out.push(ch);
        i = next;
    }
    out
}

/// Plane 1 contract manifest digests and inventory.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ContractPlaneDigests {
    /// Parsed `anneal/anneal.toml` manifest.
    pub manifest: AnnealManifest,
    /// Hex SHA-256 of `anneal/anneal.toml` raw bytes.
    pub anneal_toml_sha256: String,
    /// Hex SHA-256 of canonical `anneal-spec-manifest-v1` JSON covering all
    /// files under `anneal/specs/**` and `anneal/models/**` plus normalized
    /// inline `#[cfg_attr(anneal, ...)]` attributes in `src/**/*.rs`.
    pub contract_manifest_sha256: String,
    /// Total uncompressed byte size of `<crate>/anneal/**`.
    pub total_plane1_bytes: u64,
    /// Sorted `(rel_path, sha256)` pairs for all files under `<crate>/anneal/`.
    pub plane1_files: Vec<(String, String)>,
    /// Count of inline `#[cfg_attr(anneal, ...)]` attributes found in `src/**`.
    pub inline_attr_count: usize,
}

/// Audits `<crate_dir>/anneal/` (`O_NOFOLLOW`, rejecting symlinks, proof files,
/// and binary `.olean*` artifacts) and computes `anneal_toml_sha256` and
/// `contract_manifest_sha256` (`anneal-spec-manifest-v1`).
pub fn inspect_contract_plane(
    crate_dir: &Path,
    manifest_rel_path: &str,
) -> Result<ContractPlaneDigests, Failure> {
    let phase = "contract-plane";
    if !is_clean_relative_path(manifest_rel_path) {
        return Err(Failure::policy(
            phase,
            format!("manifest path must be a clean relative path: {manifest_rel_path:?}"),
        ));
    }
    let manifest_full =
        verify_no_symlink_ancestors(crate_dir, Path::new(manifest_rel_path), phase)?;
    let (manifest_bytes, anneal_toml_sha256) =
        read_regular_file_strict(&manifest_full, None, phase)?;
    let manifest_text = std::str::from_utf8(&manifest_bytes)
        .map_err(|e| Failure::policy(phase, format!("anneal.toml is not valid UTF-8: {e}")))?;
    let manifest = AnnealManifest::parse_and_validate(manifest_text)?;

    let anneal_dir = manifest_full
        .parent()
        .ok_or_else(|| Failure::policy(phase, "anneal.toml has no parent directory"))?;
    let mut total_plane1_bytes = 0u64;
    let mut plane1_inventory: BTreeMap<String, String> = BTreeMap::new();
    let mut spec_manifest_files: BTreeMap<String, String> = BTreeMap::new();

    for entry in WalkDir::new(anneal_dir).follow_links(false) {
        let entry = entry.map_err(|e| {
            Failure::operational(phase, format!("error walking {}: {e}", anneal_dir.display()))
        })?;
        let path = entry.path();
        if path == anneal_dir {
            continue;
        }
        let ft = entry.file_type();
        if ft.is_symlink() {
            return Err(Failure::policy(
                phase,
                format!("symlink forbidden under Plane 1 directory: {}", path.display()),
            ));
        }
        if ft.is_dir() {
            continue;
        }
        if !ft.is_file() {
            return Err(Failure::policy(
                phase,
                format!("non-regular file forbidden under Plane 1 directory: {}", path.display()),
            ));
        }
        let rel = path.strip_prefix(anneal_dir).map_err(|_| {
            Failure::operational(phase, format!("escaped anneal dir: {}", path.display()))
        })?;
        let rel_str = rel_path_to_posix_utf8(rel, phase)?;
        let lower = rel_str.to_ascii_lowercase();
        if FORBIDDEN_BINARY_LEAN_SUFFIXES.iter().any(|ext| lower.ends_with(ext)) {
            return Err(Failure::policy(
                phase,
                format!(
                    "E_ANNEAL_BINARY_OLEAN_FORBIDDEN: binary Lean artifact forbidden in Plane 1: {rel_str}"
                ),
            ));
        }
        if lower == "proof.lean" || lower.ends_with("/proof.lean") || lower.starts_with("proofs/") {
            return Err(Failure::policy(
                phase,
                format!(
                    "E_ANNEAL_PROOF_IN_CONTRACT_PLANE: proof file forbidden in Plane 1: {rel_str}"
                ),
            ));
        }
        let (bytes, sha) = read_regular_file_strict(path, None, phase)?;
        total_plane1_bytes = total_plane1_bytes.saturating_add(bytes.len() as u64);
        plane1_inventory.insert(rel_str.clone(), sha.clone());
        if rel_str != "anneal.toml" {
            spec_manifest_files.insert(rel_str, sha);
        }
    }

    // Verify every file referenced by `manifest` exists in `plane1_inventory`.
    for m in &manifest.models {
        if !plane1_inventory.contains_key(&m.path) {
            return Err(Failure::policy(
                phase,
                format!("missing declared [[models]] file under anneal/: {}", m.path),
            ));
        }
    }
    for u in &manifest.units {
        for s in &u.surface_specs {
            if !plane1_inventory.contains_key(s) {
                return Err(Failure::policy(
                    phase,
                    format!("unit `{}` missing surface_specs file under anneal/: {s}", u.id),
                ));
            }
        }
        for sm in &u.spec_modules {
            if !plane1_inventory.contains_key(&sm.path) {
                return Err(Failure::policy(
                    phase,
                    format!("unit `{}` missing spec_modules file under anneal/: {}", u.id, sm.path),
                ));
            }
        }
    }

    // Scan `src/**/*.rs` for inline `#[cfg_attr(anneal, ...)]` token streams.
    let src_dir = crate_dir.join("src");
    let mut inline_attrs: Vec<(String, Vec<String>)> = Vec::new();
    let mut inline_attr_count = 0usize;
    match fs::symlink_metadata(&src_dir) {
        Ok(meta) if meta.file_type().is_symlink() => {
            return Err(Failure::policy(
                phase,
                format!("symlink forbidden at src/: {}", src_dir.display()),
            ));
        }
        Ok(meta) if meta.is_dir() => {
            for entry in WalkDir::new(&src_dir).follow_links(false) {
                let entry = entry.map_err(|e| {
                    Failure::operational(phase, format!("error walking {}: {e}", src_dir.display()))
                })?;
                let path = entry.path();
                if path == src_dir {
                    continue;
                }
                let ft = entry.file_type();
                if ft.is_symlink() {
                    return Err(Failure::policy(
                        phase,
                        format!("symlink forbidden under src/: {}", path.display()),
                    ));
                }
                if ft.is_file() && path.extension().is_some_and(|e| e == "rs") {
                    let rel = rel_path_to_posix_utf8(
                        path.strip_prefix(crate_dir)
                            .map_err(|_| Failure::operational(phase, "strip_prefix failed"))?,
                        phase,
                    )?;
                    let (bytes, _) = read_regular_file_strict(path, None, phase)?;
                    let text = std::str::from_utf8(&bytes).map_err(|e| {
                        Failure::policy(phase, format!("{rel} is not valid UTF-8: {e}"))
                    })?;
                    let attrs = extract_inline_anneal_cfg_attrs(text);
                    if !attrs.is_empty() {
                        inline_attr_count += attrs.len();
                        inline_attrs.push((rel, attrs));
                    }
                }
            }
        }
        Ok(_) => {}
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
        Err(e) => {
            return Err(Failure::operational(
                phase,
                format!("cannot inspect {}: {e}", src_dir.display()),
            ));
        }
    }
    inline_attrs.sort_by(|a, b| a.0.cmp(&b.0));

    let spec_files_vec: Vec<(String, String)> = spec_manifest_files.into_iter().collect();
    let spec_manifest_payload = json!({
        "files": spec_files_vec,
        "inline_cfg_attrs": inline_attrs,
        "schema": "anneal-spec-manifest-v1",
    });
    let contract_manifest_sha256 = sha256_bytes(&canonical_json_bytes(&spec_manifest_payload)?);
    Ok(ContractPlaneDigests {
        manifest,
        anneal_toml_sha256,
        contract_manifest_sha256,
        total_plane1_bytes,
        plane1_files: plane1_inventory.into_iter().collect(),
        inline_attr_count,
    })
}

fn parse_msrv_triple(raw: &str) -> Option<(u64, u64, u64)> {
    let mut parts = raw.trim().split('.');
    let major = parts.next()?.parse().ok()?;
    let minor = parts.next().unwrap_or("0").parse().ok()?;
    let patch = parts.next().unwrap_or("0").parse().ok()?;
    if parts.next().is_some() {
        return None;
    }
    Some((major, minor, patch))
}

/// Extracted `Cargo.toml` package metadata validated against Plane 1 packaging
/// laws (§2.2).
#[derive(Clone, Debug)]
pub struct ValidatedCargoPackage {
    /// Cargo `package.name`.
    pub name: String,
    /// Cargo `package.version`.
    pub version: String,
    /// Cargo `package.edition` (defaults to `"2015"` per Cargo when absent).
    pub edition: String,
    /// Optional `package.rust-version`.
    pub rust_version: Option<String>,
    /// Manifest path relative to crate root from `[package.metadata.anneal]`
    /// (defaults to `"anneal/anneal.toml"`).
    pub anneal_manifest_rel: String,
    /// Optional evidence carrier crate name from `[package.metadata.anneal]`.
    pub evidence_crate_hint: Option<String>,
    /// `[package.metadata.build-rs]` version-gated negative cfg map
    /// (`key -> min_version_str`).
    pub build_rs_version_cfgs: BTreeMap<String, String>,
    /// Declared `[features]` table (`feat -> [activated...]`).
    pub features: BTreeMap<String, Vec<String>>,
    /// Optional `[lib] name`, which Cargo passes to `rustc` as `--crate-name`
    /// instead of the package name.
    pub lib_name: Option<String>,
}

impl ValidatedCargoPackage {
    /// Returns the compilation-relevant Cargo manifest fields that the
    /// source closure binds alongside source bytes.
    ///
    /// `Cargo.toml` itself is not hashed, because `cargo package` rewrites it.
    /// These parsed fields survive that rewrite and determine the `--cfg
    /// feature=...` set, the version cfgs, and the crate name passed to
    /// `rustc`, so changing any of them changes the closure digest.
    pub fn cargo_semantics(&self) -> Value {
        // `version` reaches the program through `CARGO_PKG_VERSION*`. The
        // effective library name is bound rather than the raw `[lib] name`,
        // because `cargo package` writes an explicit `[lib]` table into the
        // normalized Cargo.toml.
        json!({
            "build_rs_version_cfgs": self.build_rs_version_cfgs,
            "features": self.features,
            "lib_name": self.lib_crate_name(),
            "version": self.version,
        })
    }

    /// The library target's crate name, as Cargo passes it to rustc.
    pub fn lib_crate_name(&self) -> String {
        self.lib_name.as_deref().unwrap_or(&self.name).replace('-', "_")
    }
}

/// Cargo semantics of a package with no features, no version cfgs, and no
/// `[lib] name` override (the feature-free Cargo shortcut).
pub fn empty_cargo_semantics() -> Value {
    json!({
        "build_rs_version_cfgs": {},
        "features": {},
        "lib_name": null,
        "version": null,
    })
}

/// Hex SHA-256 over the sorted `(module, sha256)` list of authored
/// proof-role Lean sources, encoded as pretty JSON.
///
/// `cargo anneal verify` records this digest as `proof_manifest_sha256` in
/// the receipt, and evidence validation recomputes it from the shipped
/// `proof_sources`, so a carrier cannot swap a proof file for one that the
/// receipt was not produced from.
pub fn proof_manifest_sha256(entries: &BTreeMap<String, String>) -> Result<String, Failure> {
    let list: Vec<(&String, &String)> = entries.iter().collect();
    let encoded = serde_json::to_vec_pretty(&list).map_err(|e| {
        Failure::operational("proof-manifest", format!("JSON encoding failed: {e}"))
    })?;
    Ok(sha256_bytes(&encoded))
}

/// Validates `<crate_dir>/Cargo.toml` against §2.2 packaging laws:
/// 1. Mutual exclusion of `package.include` and `package.exclude`
///    (`E_ANNEAL_INCLUDE_SHADOWS_EXCLUDE`, `rust-lang/cargo@930a674d`
///    `src/ops/cargo_package/mod.rs:483-487`).
/// 2. Zero `dep:` / `?/` `features2` syntax when `rust-version < 1.60.0`
///    (`E_ANNEAL_MSRV_FEATURES2`).
/// 3. Zero verifier crates in `[dependencies]` or `[build-dependencies]`
///    (`E_ANNEAL_VERIFIER_RUNTIME_DEP`).
pub fn validate_crate_cargo_toml(crate_dir: &Path) -> Result<ValidatedCargoPackage, Failure> {
    let phase = "package-check";
    let cargo_toml_path = crate_dir.join("Cargo.toml");
    let (bytes, _) = read_regular_file_strict(&cargo_toml_path, None, phase)?;
    let text = std::str::from_utf8(&bytes)
        .map_err(|e| Failure::policy(phase, format!("Cargo.toml is not UTF-8: {e}")))?;
    let doc: toml::Value = toml::from_str(text)
        .map_err(|e| Failure::policy(phase, format!("invalid Cargo.toml: {e}")))?;
    let pkg = doc
        .get("package")
        .and_then(toml::Value::as_table)
        .ok_or_else(|| Failure::policy(phase, "Cargo.toml missing `[package]` table"))?;

    if pkg.contains_key("include") && pkg.contains_key("exclude") {
        return Err(Failure::policy(
            phase,
            "E_ANNEAL_INCLUDE_SHADOWS_EXCLUDE: Cargo.toml specifies both `package.include` and \
             `package.exclude`; Cargo silently ignores `exclude` when `include` is set",
        ));
    }

    let name = pkg
        .get("name")
        .and_then(toml::Value::as_str)
        .filter(|s| !s.is_empty())
        .ok_or_else(|| Failure::policy(phase, "Cargo.toml missing `package.name`"))?
        .to_owned();
    let version = pkg
        .get("version")
        .and_then(toml::Value::as_str)
        .filter(|s| !s.is_empty())
        .ok_or_else(|| Failure::policy(phase, "Cargo.toml missing `package.version`"))?
        .to_owned();
    let edition = pkg.get("edition").and_then(toml::Value::as_str).unwrap_or("2015").to_owned();
    let rust_version = pkg.get("rust-version").and_then(toml::Value::as_str).map(str::to_owned);

    // Check `[dependencies]` and `[build-dependencies]` (including target-gated
    // tables) for accidental runtime/build verifier coupling (`C+1`).
    let is_verifier_crate = |name: &str| {
        name == "cargo-anneal" || name == "anneal-spec" || name.ends_with("-anneal-proofs")
    };
    let check_dep_keys = |sec_name: &str,
                          tbl: &toml::map::Map<String, toml::Value>|
     -> Result<(), Failure> {
        for (dep_key, dep_val) in tbl {
            // A table-form dependency may rename the crate with `package`.
            let renamed_from = dep_val.get("package").and_then(toml::Value::as_str);
            if is_verifier_crate(dep_key) || renamed_from.is_some_and(is_verifier_crate) {
                let shown = match renamed_from {
                    Some(package) if package != dep_key => {
                        format!("{dep_key}` (package `{package}`)")
                    }
                    _ => format!("{dep_key}`"),
                };
                return Err(Failure::policy(
                    phase,
                    format!(
                        "E_ANNEAL_VERIFIER_RUNTIME_DEP: `{shown} forbidden in `{sec_name}`; \
                         Plane 1 contracts must add zero runtime/build dependencies (use `[dev-dependencies]` for evidence carriers)"
                    ),
                ));
            }
        }
        Ok(())
    };
    for sec in ["dependencies", "build-dependencies", "build_dependencies"] {
        if let Some(tbl) = doc.get(sec).and_then(toml::Value::as_table) {
            check_dep_keys(sec, tbl)?;
        }
    }
    if let Some(targets) = doc.get("target").and_then(toml::Value::as_table) {
        for (cfg_key, cfg_val) in targets {
            if let Some(cfg_tbl) = cfg_val.as_table() {
                for sec in ["dependencies", "build-dependencies", "build_dependencies"] {
                    if let Some(tbl) = cfg_tbl.get(sec).and_then(toml::Value::as_table) {
                        check_dep_keys(&format!("target.{cfg_key}.{sec}"), tbl)?;
                    }
                }
            }
        }
    }

    let mut features = BTreeMap::new();
    let msrv_below_1_60 =
        rust_version.as_deref().and_then(parse_msrv_triple).is_some_and(|v| v < (1, 60, 0));
    if let Some(feat_tbl) = doc.get("features").and_then(toml::Value::as_table) {
        for (feat_name, raw_list) in feat_tbl {
            let arr = raw_list.as_array().ok_or_else(|| {
                Failure::policy(phase, format!("feature `{feat_name}` value must be an array"))
            })?;
            let mut items = Vec::with_capacity(arr.len());
            for v in arr {
                let s = v.as_str().ok_or_else(|| {
                    Failure::policy(phase, format!("feature `{feat_name}` item must be a string"))
                })?;
                if msrv_below_1_60 && (s.starts_with("dep:") || s.contains("?/")) {
                    return Err(Failure::policy(
                        phase,
                        format!(
                            "E_ANNEAL_MSRV_FEATURES2: feature `{feat_name}` uses Cargo 1.60+ \
                             syntax `{s}` while `rust-version = {:?}` is below 1.60.0",
                            rust_version
                        ),
                    ));
                }
                items.push(s.to_owned());
            }
            features.insert(feat_name.clone(), items);
        }
    }

    let metadata = pkg.get("metadata").and_then(toml::Value::as_table);
    let anneal_meta = metadata.and_then(|m| m.get("anneal")).and_then(toml::Value::as_table);
    let anneal_manifest_rel = anneal_meta
        .and_then(|a| a.get("manifest"))
        .and_then(toml::Value::as_str)
        .unwrap_or("anneal/anneal.toml")
        .to_owned();
    let evidence_crate_hint = anneal_meta
        .and_then(|a| a.get("evidence_crate"))
        .and_then(toml::Value::as_str)
        .map(str::to_owned);

    let lib_name = doc
        .get("lib")
        .and_then(|lib| lib.get("name"))
        .and_then(toml::Value::as_str)
        .map(str::to_owned);

    let mut build_rs_version_cfgs = BTreeMap::new();
    if let Some(build_rs_tbl) =
        metadata.and_then(|m| m.get("build-rs")).and_then(toml::Value::as_table)
    {
        for (k, v) in build_rs_tbl {
            if let Some(ver_str) = v.as_str() {
                build_rs_version_cfgs.insert(k.replace('-', "_"), ver_str.to_owned());
            }
        }
    }

    Ok(ValidatedCargoPackage {
        name,
        version,
        edition,
        rust_version,
        anneal_manifest_rel,
        evidence_crate_hint,
        build_rs_version_cfgs,
        features,
        lib_name,
    })
}

fn has_cfg_anneal_check_directive(directive: &str) -> bool {
    let trimmed = directive.trim();
    trimmed == "cfg(anneal)" || trimmed.starts_with("cfg(anneal,")
}

/// Checks §2.2 Law 3: if inline `#[cfg_attr(anneal, ...)]` attributes appear
/// in `src/**/*.rs`, either `build.rs` or `Cargo.toml` `[lints.rust]` must
/// configure `cfg(anneal)` for `rustc >= 1.80`'s `unexpected_cfgs` lint.
pub fn verify_unexpected_cfgs_guard(
    crate_dir: &Path,
    inline_attr_count: usize,
) -> Result<(), Failure> {
    if inline_attr_count == 0 {
        return Ok(());
    }
    let phase = "package-check";
    let build_rs = crate_dir.join("build.rs");
    if fs::symlink_metadata(&build_rs).is_ok() {
        let (bytes, _) = read_regular_file_strict(&build_rs, None, phase)?;
        let text = String::from_utf8_lossy(&bytes);
        if text.lines().any(|line| {
            let trimmed = line.trim_start();
            !trimmed.starts_with("//")
                && (trimmed.contains("rustc-check-cfg=cfg(anneal)")
                    || trimmed.contains("rustc-check-cfg=cfg(anneal,"))
        }) {
            return Ok(());
        }
    }
    let (cargo_bytes, _) = read_regular_file_strict(&crate_dir.join("Cargo.toml"), None, phase)?;
    let cargo_text = std::str::from_utf8(&cargo_bytes)
        .map_err(|e| Failure::policy(phase, format!("Cargo.toml is not UTF-8: {e}")))?;
    let doc: toml::Value = toml::from_str(cargo_text)
        .map_err(|e| Failure::policy(phase, format!("invalid Cargo.toml: {e}")))?;
    if let Some(check_cfgs) = doc
        .get("lints")
        .and_then(|l| l.get("rust"))
        .and_then(|r| r.get("unexpected_cfgs"))
        .and_then(|u| u.get("check-cfg"))
        .and_then(toml::Value::as_array)
        && check_cfgs.iter().filter_map(toml::Value::as_str).any(has_cfg_anneal_check_directive)
    {
        return Ok(());
    }
    Err(Failure::policy(
        phase,
        "E_ANNEAL_UNEXPECTED_CFGS_UNGUARDED: inline `#[cfg_attr(anneal, ...)]` used in `src/` \
         without `rustc-check-cfg=cfg(anneal)` in `build.rs` or `[lints.rust] unexpected_cfgs`",
    ))
}

/// Master `anneal-evidence.json` schema (`schema_version = 1`) shipped inside
/// `<crate>-anneal-proofs` carrier crates or Stage 0 `.tar.zst` archives.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EvidenceBundleManifest {
    /// Must equal `1`.
    pub schema_version: u32,
    /// Subject digests binding Plane 2 evidence inward to Plane 1 `<crate>`.
    pub subject: EvidenceSubject,
    /// Optional overlay metadata when this carrier verifies a third-party
    /// uncooperative crate (`§7.4`).
    #[serde(default)]
    pub overlay: Option<OverlayPolicyMetadata>,
    /// Source proof units for `source-replay` and human audit.
    #[serde(default)]
    pub proof_units: BTreeMap<String, EvidenceProofUnit>,
    /// Pre-verified slice receipts indexed by slice identifier.
    #[serde(default)]
    pub slices: BTreeMap<String, EvidenceSlice>,
}

/// Subject identity inside `anneal-evidence.json`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EvidenceSubject {
    /// Subject Cargo package name.
    pub crate_name: String,
    /// Subject Cargo package version.
    pub crate_version: String,
    /// Expected `source_closure_sha256` (`anneal-source-closure-v1`).
    pub source_closure_sha256: String,
    /// Expected Plane 1 `contract_manifest_sha256` (`anneal-spec-manifest-v1`),
    /// stored under `specification_manifest_sha256` per §3.3.
    pub specification_manifest_sha256: String,
    /// Expected SHA-256 of `anneal/anneal.toml`.
    pub anneal_toml_sha256: String,
}

/// Trust classification for external overlays (§7.4).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum OverlayTrustClass {
    /// Kernel-checked against the third-party crate's actual MIR (`0` axioms).
    ThirdPartyVerified,
    /// Unproved external contract assumption (restricted strictly to the root
    /// verifying workspace; forbidden in transitive carriers per `C-4`).
    AssumedExternal,
}

/// Overlay policy metadata inside `anneal-evidence.json` (§7.4).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct OverlayPolicyMetadata {
    /// Trust class (`third_party_verified` vs `assumed_external`).
    pub trust_class: OverlayTrustClass,
    /// Whether this overlay exports closed private-field type invariants
    /// (`LibValid`), which requires `crate_verified` scope across the
    /// visibility cone (`§7.4`).
    #[serde(default)]
    pub exports_type_invariants: bool,
    /// Whether this overlay was loaded from the root workspace policy ledger.
    #[serde(default)]
    pub is_root_workspace_ledger: bool,
}

/// Proof unit source descriptor inside `anneal-evidence.json`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EvidenceProofUnit {
    /// Qualified Lean proof theorem name (`Proof.verify`).
    pub theorem: String,
    /// Sharding mode (`"none"` or `"nominal"`).
    #[serde(default = "default_shard_none")]
    pub shard_mode: String,
    /// Authored proof files with SHA-256 digests.
    pub proof_sources: Vec<EvidenceFileRecord>,
    /// Shared `Role::ProofLibrary` module names imported by this proof.
    #[serde(default)]
    pub proof_library_deps: Vec<String>,
}

fn default_shard_none() -> String {
    "none".to_owned()
}

/// SHA-256-pinned file entry in `anneal-evidence.json`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EvidenceFileRecord {
    /// Lean module name.
    pub module: String,
    /// Clean relative path inside the evidence carrier.
    pub path: String,
    /// Expected lowercase 64-hex SHA-256 of the file.
    pub sha256: String,
}

/// Pre-verified slice entry inside `anneal-evidence.json`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EvidenceSlice {
    /// Path-free `SemanticProfile` of this slice.
    pub semantic_profile: SemanticProfile,
    /// Compiler commit SHA recorded during slice verification.
    pub rustc_commit_sha: String,
    /// Lean toolchain identifier recorded during slice verification.
    pub lean_toolchain: String,
    /// Per-unit verified receipts and cones within this slice.
    pub units: BTreeMap<String, EvidenceSliceUnit>,
}

/// Per-unit receipt and cone record within an [`EvidenceSlice`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EvidenceSliceUnit {
    /// Path-free `canonical_program_sha256` of the verified unit.
    pub canonical_program_sha256: String,
    /// Clean relative path to the Receipt v3 JSON file.
    pub receipt_path: String,
    /// Expected SHA-256 of `receipt_path`.
    pub receipt_sha256: String,
    /// Optional clean relative path to `expected_cone.ndjson`.
    #[serde(default)]
    pub expected_cone_path: Option<String>,
    /// Optional expected SHA-256 of `expected_cone_path`.
    #[serde(default)]
    pub expected_cone_sha256: Option<String>,
    /// Optional clean relative path to a Sigstore DSSE / SLSA v1.0 attestation.
    #[serde(default)]
    pub attestation_path: Option<String>,
}

/// Options governing Plane 2 evidence carrier validation.
#[derive(Clone, Debug, Default)]
pub struct EvidenceVerifyOptions {
    /// Require every verified receipt to carry empty `taint_reasons: []`.
    pub require_untainted: bool,
    /// Require a Sigstore DSSE attestation bundle on all slices (even those not
    /// claiming `external_unverified_by_binary` containment).
    pub require_attestation: bool,
}

/// Summary of a verified Plane 2 evidence carrier.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct EvidenceVerificationReport {
    /// Validated subject crate name.
    pub crate_name: String,
    /// Validated subject crate version.
    pub crate_version: String,
    /// Verified `source_closure_sha256`.
    pub source_closure_sha256: String,
    /// Verified Plane 1 `contract_manifest_sha256`.
    pub contract_manifest_sha256: String,
    /// Verified `anneal_toml_sha256`.
    pub anneal_toml_sha256: String,
    /// Number of validated source proof units.
    pub verified_proof_unit_count: usize,
    /// Number of validated pre-verified slice unit receipts.
    pub verified_slice_receipt_count: usize,
    /// Union of `taint_reasons` across all validated slice receipts.
    pub transitive_taint_reasons: Vec<String>,
    /// Union of permitted Lean axioms used across validated slice receipts.
    pub transitive_axioms: Vec<String>,
}

/// Authenticates an unpacked Plane 2 evidence carrier directory against a live
/// or vendored Plane 1 `<crate_dir>` (`§3.3`, `§4.2`, `§4.3`, `§7.4`).
pub fn verify_evidence_carrier_dir(
    crate_dir: &Path,
    pkg: &ValidatedCargoPackage,
    source_closure: &SourceClosureReport,
    plane1: &ContractPlaneDigests,
    evidence_dir: &Path,
    opts: &EvidenceVerifyOptions,
) -> Result<(EvidenceBundleManifest, EvidenceVerificationReport), Failure> {
    let phase = "evidence-verify";
    let ev_meta = fs::symlink_metadata(evidence_dir).map_err(|e| {
        Failure::operational(phase, format!("cannot inspect {}: {e}", evidence_dir.display()))
    })?;
    if ev_meta.file_type().is_symlink() || !ev_meta.is_dir() {
        return Err(Failure::policy(
            phase,
            format!("evidence directory must not be a symlink: {}", evidence_dir.display()),
        ));
    }

    // Walk the entire evidence carrier first to forbid symlinks and binary
    // `.olean*` files (`§6.2`).
    for entry in WalkDir::new(evidence_dir).follow_links(false) {
        let entry = entry.map_err(|e| {
            Failure::operational(phase, format!("error walking {}: {e}", evidence_dir.display()))
        })?;
        let path = entry.path();
        if path == evidence_dir {
            continue;
        }
        let ft = entry.file_type();
        if ft.is_symlink() {
            return Err(Failure::policy(
                phase,
                format!("symlink forbidden inside evidence carrier: {}", path.display()),
            ));
        }
        if !ft.is_dir() && !ft.is_file() {
            return Err(Failure::policy(
                phase,
                format!("non-regular file forbidden inside evidence carrier: {}", path.display()),
            ));
        }
        if ft.is_file() {
            let name_l = entry.file_name().to_string_lossy().to_ascii_lowercase();
            if FORBIDDEN_BINARY_LEAN_SUFFIXES.iter().any(|ext| name_l.ends_with(ext)) {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "E_ANNEAL_BINARY_OLEAN_FORBIDDEN: binary Lean artifact forbidden in evidence carrier: {}",
                        path.display()
                    ),
                ));
            }
        }
    }

    // Validate Cargo carrier metadata (`Cargo.toml` and zero `build.rs`).
    let ev_build_rs = evidence_dir.join("build.rs");
    if fs::symlink_metadata(&ev_build_rs).is_ok() {
        return Err(Failure::policy(phase, "evidence carrier crate must not ship a `build.rs`"));
    }
    let ev_cargo_toml = evidence_dir.join("Cargo.toml");
    if fs::symlink_metadata(&ev_cargo_toml).is_ok() {
        validate_carrier_cargo_toml(&ev_cargo_toml, &pkg.name, &pkg.version, phase)?;
    }

    let ev_json_path =
        verify_no_symlink_ancestors(evidence_dir, Path::new("anneal-evidence.json"), phase)?;
    let (ev_bytes, _) = read_regular_file_strict(&ev_json_path, None, phase)?;
    let ev: EvidenceBundleManifest = serde_json::from_slice(&ev_bytes)
        .map_err(|e| Failure::policy(phase, format!("malformed anneal-evidence.json: {e}")))?;
    if ev.schema_version != 1 {
        return Err(Failure::policy(
            phase,
            format!(
                "unsupported anneal-evidence.json schema_version {} (expected 1)",
                ev.schema_version
            ),
        ));
    }

    // Enforce subject cryptographic bindings against recomputed `<crate_dir>`
    // digests (defeating `.cargo-checksum.json` clearing and file injection).
    let _ = crate_dir;
    if ev.subject.crate_name != pkg.name || ev.subject.crate_version != pkg.version {
        return Err(Failure::policy(
            phase,
            format!(
                "E_ANNEAL_SOURCE_CLOSURE_MISMATCH: evidence subject `{} {}` does not match crate `{} {}`",
                ev.subject.crate_name, ev.subject.crate_version, pkg.name, pkg.version
            ),
        ));
    }
    if !is_sha256_hex(&ev.subject.source_closure_sha256)
        || ev.subject.source_closure_sha256 != source_closure.source_closure_sha256
    {
        return Err(Failure::policy(
            phase,
            format!(
                "E_ANNEAL_SOURCE_CLOSURE_MISMATCH: source_closure_sha256 mismatch (evidence={} vs crate={})",
                ev.subject.source_closure_sha256, source_closure.source_closure_sha256
            ),
        ));
    }
    if !is_sha256_hex(&ev.subject.specification_manifest_sha256)
        || ev.subject.specification_manifest_sha256 != plane1.contract_manifest_sha256
    {
        return Err(Failure::policy(
            phase,
            format!(
                "E_ANNEAL_SOURCE_CLOSURE_MISMATCH: specification_manifest_sha256 mismatch (evidence={} vs crate={})",
                ev.subject.specification_manifest_sha256, plane1.contract_manifest_sha256
            ),
        ));
    }
    if !is_sha256_hex(&ev.subject.anneal_toml_sha256)
        || ev.subject.anneal_toml_sha256 != plane1.anneal_toml_sha256
    {
        return Err(Failure::policy(
            phase,
            format!(
                "E_ANNEAL_SOURCE_CLOSURE_MISMATCH: anneal_toml_sha256 mismatch (evidence={} vs crate={})",
                ev.subject.anneal_toml_sha256, plane1.anneal_toml_sha256
            ),
        ));
    }

    // Enforce §7.4 overlay trust-class & visibility-cone encapsulation gates.
    if let Some(overlay) = &ev.overlay {
        if overlay.trust_class == OverlayTrustClass::AssumedExternal
            && !overlay.is_root_workspace_ledger
        {
            return Err(Failure::policy(
                phase,
                "E_ANNEAL_OVERLAY_SCOPE_VIOLATION: transitive `assumed_external` overlays are \
                 forbidden; unproved external specs may live only in the root workspace ledger",
            ));
        }
        if overlay.exports_type_invariants {
            let all_crate_scoped = !plane1.manifest.units.is_empty()
                && plane1.manifest.units.iter().all(|u| matches!(u.scope, ManifestScope::Crate {}));
            if !all_crate_scoped {
                return Err(Failure::policy(
                    phase,
                    "E_ANNEAL_OVERLAY_SCOPE_VIOLATION: `third_party_verified` overlay exporting \
                     closed type invariants (`LibValid`) requires `crate` verification scope",
                ));
            }
        }
    }

    let declared_units: BTreeMap<&str, &ManifestUnit> =
        plane1.manifest.units.iter().map(|u| (u.id.as_str(), u)).collect();

    // Validate proof_units source files and SHA-256 digests.
    for (unit_id, pu) in &ev.proof_units {
        if !declared_units.contains_key(unit_id.as_str()) {
            return Err(Failure::policy(
                phase,
                format!("proof_units `{unit_id}` is not declared in anneal/anneal.toml"),
            ));
        }
        if !pu.theorem.contains('.') || !pu.theorem.split('.').all(is_lean_ident) {
            return Err(Failure::policy(
                phase,
                format!("proof_units `{unit_id}` has invalid theorem {:?}", pu.theorem),
            ));
        }
        if pu.proof_sources.is_empty() {
            return Err(Failure::policy(
                phase,
                format!("proof_units `{unit_id}` must list at least one proof source"),
            ));
        }
        for src in &pu.proof_sources {
            if !is_clean_relative_path(&src.path) || !src.path.ends_with(".lean") {
                return Err(Failure::policy(
                    phase,
                    format!("invalid proof source path {:?} in `{unit_id}`", src.path),
                ));
            }
            if !is_sha256_hex(&src.sha256) {
                return Err(Failure::policy(
                    phase,
                    format!("invalid sha256 on proof source {:?} in `{unit_id}`", src.path),
                ));
            }
            let full = verify_no_symlink_ancestors(evidence_dir, Path::new(&src.path), phase)?;
            let (_, actual_sha) = read_regular_file_strict(&full, None, phase)?;
            if actual_sha != src.sha256 {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "proof source SHA-256 mismatch for {}: expected {}, got {actual_sha}",
                        src.path, src.sha256
                    ),
                ));
            }
        }
    }

    let mut verified_slice_receipt_count = 0usize;
    let mut transitive_taints = BTreeSet::new();
    let mut transitive_axioms = BTreeSet::new();
    const ALLOWED_AXIOMS: &[&str] = &["Classical.choice", "Quot.sound", "propext"];

    for (slice_id, slice) in &ev.slices {
        if !is_valid_unit_or_slice_id(slice_id) {
            return Err(Failure::policy(phase, format!("invalid slice id {slice_id:?}")));
        }
        // A slice verified by another compiler or Lean toolchain is not
        // evidence for this verifier, whose model is pinned to both.
        if slice.rustc_commit_sha != crate::verify::PINNED_RUSTC_COMMIT {
            return Err(Failure::policy(
                phase,
                format!(
                    "slice `{slice_id}` rustc_commit_sha {:?} differs from the pinned compiler \
                     commit {}",
                    slice.rustc_commit_sha,
                    crate::verify::PINNED_RUSTC_COMMIT
                ),
            ));
        }
        if slice.lean_toolchain != crate::toolchain::TOOLCHAIN {
            return Err(Failure::policy(
                phase,
                format!(
                    "slice `{slice_id}` lean_toolchain {:?} differs from the pinned Lean \
                     toolchain {}",
                    slice.lean_toolchain,
                    crate::toolchain::TOOLCHAIN
                ),
            ));
        }
        for (unit_id, su) in &slice.units {
            let Some(expected_unit) = declared_units.get(unit_id.as_str()) else {
                return Err(Failure::policy(
                    phase,
                    format!("slice `{slice_id}` references undeclared unit `{unit_id}`"),
                ));
            };
            let Some(expected_proof_unit) = ev.proof_units.get(unit_id) else {
                return Err(Failure::policy(
                    phase,
                    format!("slice `{slice_id}` references unit `{unit_id}` missing from `proof_units`"),
                ));
            };
            if !is_sha256_hex(&su.canonical_program_sha256) || !is_sha256_hex(&su.receipt_sha256) {
                return Err(Failure::policy(
                    phase,
                    format!("slice `{slice_id}` unit `{unit_id}` has invalid SHA-256 hex"),
                ));
            }
            if !is_clean_relative_path(&su.receipt_path) {
                return Err(Failure::policy(
                    phase,
                    format!("invalid receipt_path {:?}", su.receipt_path),
                ));
            }
            let receipt_full =
                verify_no_symlink_ancestors(evidence_dir, Path::new(&su.receipt_path), phase)?;
            let (receipt_bytes, actual_receipt_sha) =
                read_regular_file_strict(&receipt_full, None, phase)?;
            if actual_receipt_sha != su.receipt_sha256 {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "receipt SHA-256 mismatch for {}: expected {}, got {actual_receipt_sha}",
                        su.receipt_path, su.receipt_sha256
                    ),
                ));
            }
            let receipt: Value = serde_json::from_slice(&receipt_bytes).map_err(|e| {
                Failure::policy(phase, format!("malformed receipt {}: {e}", su.receipt_path))
            })?;
            validate_slice_receipt(
                &receipt,
                slice_id,
                unit_id,
                expected_unit,
                expected_proof_unit,
                plane1,
                source_closure,
                &slice.semantic_profile,
                su,
                opts,
                ALLOWED_AXIOMS,
                &mut transitive_taints,
                &mut transitive_axioms,
            )?;

            if let Some(cone_rel) = &su.expected_cone_path {
                if !is_clean_relative_path(cone_rel) {
                    return Err(Failure::policy(
                        phase,
                        format!("invalid expected_cone_path {cone_rel:?}"),
                    ));
                }
                let expected_cone_sha = su.expected_cone_sha256.as_deref().ok_or_else(|| {
                    Failure::policy(phase, format!("missing expected_cone_sha256 for {cone_rel}"))
                })?;
                if !is_sha256_hex(expected_cone_sha) {
                    return Err(Failure::policy(
                        phase,
                        format!("invalid expected_cone_sha256 for {cone_rel}"),
                    ));
                }
                let cone_full =
                    verify_no_symlink_ancestors(evidence_dir, Path::new(cone_rel), phase)?;
                let (_, actual_cone_sha) = read_regular_file_strict(&cone_full, None, phase)?;
                if actual_cone_sha != expected_cone_sha {
                    return Err(Failure::policy(
                        phase,
                        format!(
                            "expected_cone SHA-256 mismatch for {cone_rel}: expected {expected_cone_sha}, got {actual_cone_sha}"
                        ),
                    ));
                }
            }
            verified_slice_receipt_count += 1;
        }
    }

    let report = EvidenceVerificationReport {
        crate_name: pkg.name.clone(),
        crate_version: pkg.version.clone(),
        source_closure_sha256: source_closure.source_closure_sha256.clone(),
        contract_manifest_sha256: plane1.contract_manifest_sha256.clone(),
        anneal_toml_sha256: plane1.anneal_toml_sha256.clone(),
        verified_proof_unit_count: ev.proof_units.len(),
        verified_slice_receipt_count,
        transitive_taint_reasons: transitive_taints.into_iter().collect(),
        transitive_axioms: transitive_axioms.into_iter().collect(),
    };
    Ok((ev, report))
}

/// Computes the expected `specification_manifest_sha256` matching `verify.rs`
/// for a Plane 1 unit that declares `[[models]]` or `spec_modules`. Returns
/// `Ok(None)` when a unit relies solely on inline `surface_specs`.
pub fn unit_specification_manifest_sha256(
    plane1: &ContractPlaneDigests,
    unit: &ManifestUnit,
) -> Result<Option<String>, Failure> {
    if unit.models.is_empty() && unit.spec_modules.is_empty() {
        return Ok(None);
    }
    let files_by_rel: BTreeMap<&str, &str> =
        plane1.plane1_files.iter().map(|(rel, sha)| (rel.as_str(), sha.as_str())).collect();
    let mut spec_identity: Vec<(String, String)> = Vec::new();
    for model_name in &unit.models {
        let model = plane1.manifest.models.iter().find(|m| &m.module == model_name).ok_or_else(
            || {
                Failure::policy(
                    "evidence-verify",
                    format!("unit `{}` references unknown model `{model_name}`", unit.id),
                )
            },
        )?;
        let sha = files_by_rel.get(model.path.as_str()).ok_or_else(|| {
            Failure::policy(
                "evidence-verify",
                format!("missing digest for model file {}", model.path),
            )
        })?;
        spec_identity.push((model.module.clone(), (*sha).to_owned()));
    }
    for sm in &unit.spec_modules {
        let sha = files_by_rel.get(sm.path.as_str()).ok_or_else(|| {
            Failure::policy(
                "evidence-verify",
                format!("missing digest for spec module file {}", sm.path),
            )
        })?;
        spec_identity.push((sm.module.clone(), (*sha).to_owned()));
    }
    let encoded = serde_json::to_vec_pretty(&spec_identity).map_err(|e| {
        Failure::operational("evidence-verify", format!("JSON encoding failed: {e}"))
    })?;
    Ok(Some(sha256_bytes(&encoded)))
}

#[allow(clippy::too_many_arguments)]
fn validate_slice_receipt(
    receipt: &Value,
    slice_id: &str,
    unit_id: &str,
    expected_unit: &ManifestUnit,
    expected_proof_unit: &EvidenceProofUnit,
    plane1: &ContractPlaneDigests,
    source_closure: &SourceClosureReport,
    expected_profile: &SemanticProfile,
    su: &EvidenceSliceUnit,
    opts: &EvidenceVerifyOptions,
    allowed_axioms: &[&str],
    transitive_taints: &mut BTreeSet<String>,
    transitive_axioms: &mut BTreeSet<String>,
) -> Result<(), Failure> {
    let phase = "evidence-verify";
    if receipt.get("schema_version").and_then(Value::as_u64) != Some(3) {
        return Err(Failure::policy(
            phase,
            format!("slice `{slice_id}` unit `{unit_id}` receipt must have schema_version == 3"),
        ));
    }
    let status = receipt.get("status").and_then(Value::as_str).unwrap_or("");
    let expected_untainted = match expected_unit.scope {
        ManifestScope::Crate {} => "crate_verified",
        ManifestScope::SelectedUnit { .. } => "selected_unit_verified",
    };
    let expected_tainted = match expected_unit.scope {
        ManifestScope::Crate {} => "tainted_crate_verified",
        ManifestScope::SelectedUnit { .. } => "tainted_selected_unit_verified",
    };
    if status != expected_untainted && status != expected_tainted {
        return Err(Failure::policy(
            phase,
            format!(
                "slice `{slice_id}` unit `{unit_id}` receipt has non-passing or mismatched status {status:?}"
            ),
        ));
    }
    let taints = receipt.get("taint_reasons").and_then(Value::as_array).ok_or_else(|| {
        Failure::policy(phase, format!("receipt `{unit_id}` missing `taint_reasons` array"))
    })?;
    for t in taints {
        let s = t.as_str().ok_or_else(|| {
            Failure::policy(phase, format!("non-string taint reason in `{unit_id}`"))
        })?;
        transitive_taints.insert(s.to_owned());
    }
    // The slice index records the pinned Lean toolchain (checked by the
    // caller), so a receipt from an `--allow-unpinned-lean` run contradicts
    // it even when tainted receipts are otherwise accepted. The compiler
    // needs no such check: `verify` refuses captures from any rustc commit
    // other than the pinned one.
    if taints.iter().any(|t| t.as_str() == Some("unpinned_lean"))
        || receipt.get("unpinned_lean").is_some()
    {
        return Err(Failure::policy(
            phase,
            format!(
                "slice `{slice_id}` unit `{unit_id}` receipt was produced with an unpinned \
                 Lean toolchain, not the slice's pinned lean_toolchain"
            ),
        ));
    }
    if opts.require_untainted && (!taints.is_empty() || status != expected_untainted) {
        return Err(Failure::policy(
            phase,
            format!("slice `{slice_id}` unit `{unit_id}` receipt is tainted ({taints:?})"),
        ));
    }
    let sandbox = receipt
        .get("elaboration_sandbox")
        .and_then(Value::as_str)
        .filter(|s| !s.is_empty())
        .ok_or_else(|| {
            Failure::policy(phase, format!("receipt `{unit_id}` missing `elaboration_sandbox`"))
        })?;
    if opts.require_untainted && sandbox == "none" {
        return Err(Failure::policy(
            phase,
            format!("slice `{slice_id}` unit `{unit_id}` used unsandboxed elaboration"),
        ));
    }

    let rec_closure =
        receipt.get("source_closure_sha256").and_then(Value::as_str).ok_or_else(|| {
            Failure::policy(phase, format!("receipt `{unit_id}` missing `source_closure_sha256`"))
        })?;
    if rec_closure != source_closure.source_closure_sha256 {
        return Err(Failure::policy(
            phase,
            format!(
                "E_ANNEAL_SOURCE_CLOSURE_MISMATCH: receipt `{unit_id}` `source_closure_sha256` \
                 ({rec_closure}) != {}",
                source_closure.source_closure_sha256
            ),
        ));
    }

    let rec_spec_sha = receipt
        .get("specification_manifest_sha256")
        .and_then(Value::as_str)
        .filter(|s| is_sha256_hex(s))
        .ok_or_else(|| {
            Failure::policy(
                phase,
                format!("receipt `{unit_id}` missing valid `specification_manifest_sha256`"),
            )
        })?;
    if let Some(expected_spec_sha) = unit_specification_manifest_sha256(plane1, expected_unit)?
        && rec_spec_sha != expected_spec_sha
    {
        return Err(Failure::policy(
            phase,
            format!(
                "E_ANNEAL_SOURCE_CLOSURE_MISMATCH: receipt `{unit_id}` \
                 `specification_manifest_sha256` ({rec_spec_sha}) != Plane 1 ({expected_spec_sha})"
            ),
        ));
    }

    // Bind the shipped proof files to the receipt, not only to the mutable
    // evidence index that lists them.
    let rec_proof_sha = receipt
        .get("proof_manifest_sha256")
        .and_then(Value::as_str)
        .filter(|s| is_sha256_hex(s))
        .ok_or_else(|| {
            Failure::policy(
                phase,
                format!("receipt `{unit_id}` missing valid `proof_manifest_sha256`"),
            )
        })?;
    let mut shipped_proofs = BTreeMap::new();
    for src in &expected_proof_unit.proof_sources {
        if shipped_proofs.insert(src.module.clone(), src.sha256.clone()).is_some() {
            return Err(Failure::policy(
                phase,
                format!("proof_units `{unit_id}` lists module `{}` twice", src.module),
            ));
        }
    }
    let expected_proof_sha = proof_manifest_sha256(&shipped_proofs)?;
    if rec_proof_sha != expected_proof_sha {
        return Err(Failure::policy(
            phase,
            format!(
                "E_ANNEAL_SOURCE_CLOSURE_MISMATCH: receipt `{unit_id}` `proof_manifest_sha256` \
                 ({rec_proof_sha}) != shipped proof sources ({expected_proof_sha})"
            ),
        ));
    }

    let scope_val = receipt
        .get("scope")
        .ok_or_else(|| Failure::policy(phase, format!("receipt `{unit_id}` missing `scope`")))?;
    let receipt_scope: ManifestScope = serde_json::from_value(scope_val.clone()).map_err(|e| {
        Failure::policy(phase, format!("receipt `{unit_id}` has invalid `scope`: {e}"))
    })?;
    if receipt_scope != expected_unit.scope {
        return Err(Failure::policy(
            phase,
            format!("slice `{slice_id}` unit `{unit_id}` receipt `scope` does not match anneal.toml"),
        ));
    }

    if let Some(rec_canon) = receipt.get("canonical_program_sha256").and_then(Value::as_str) {
        if rec_canon != su.canonical_program_sha256 {
            return Err(Failure::policy(
                phase,
                format!(
                    "slice `{slice_id}` unit `{unit_id}` canonical_program_sha256 mismatch between index and receipt"
                ),
            ));
        }
    } else {
        return Err(Failure::policy(
            phase,
            format!(
                "slice `{slice_id}` unit `{unit_id}` receipt missing `canonical_program_sha256`"
            ),
        ));
    }

    let cfg_val = receipt.get("configuration").ok_or_else(|| {
        Failure::policy(phase, format!("receipt `{unit_id}` missing `configuration`"))
    })?;
    let receipt_profile = SemanticProfile::from_capture_configuration(cfg_val)?;
    if &receipt_profile != expected_profile {
        return Err(Failure::policy(
            phase,
            format!(
                "slice `{slice_id}` unit `{unit_id}` SemanticProfile mismatch: {}",
                receipt_profile.diff_summary(expected_profile).join("; ")
            ),
        ));
    }

    let audit = receipt.get("audit").and_then(Value::as_object).ok_or_else(|| {
        Failure::policy(phase, format!("receipt `{unit_id}` missing `audit` object"))
    })?;
    if audit.get("replay").and_then(Value::as_bool) != Some(true)
        || audit.get("exactType").and_then(Value::as_bool) != Some(true)
    {
        return Err(Failure::policy(
            phase,
            format!("receipt `{unit_id}` audit must certify replay == true and exactType == true"),
        ));
    }
    let expected_canonical_root = match expected_unit.scope {
        ManifestScope::Crate {} => "Trusted.MirSemantics.CrateTheorem",
        ManifestScope::SelectedUnit { .. } => "Trusted.MirSemantics.UnitTheorem",
    };
    if audit.get("canonicalRoot").and_then(Value::as_str) != Some(expected_canonical_root)
        || audit.get("subject").and_then(Value::as_str) != Some("Captured.program")
        || audit.get("expected").and_then(Value::as_str) != Some("Expected.claim")
        || audit.get("theorem").and_then(Value::as_str) != Some(expected_proof_unit.theorem.as_str())
        || audit.get("specification").and_then(Value::as_str)
            != Some(expected_unit.specification.as_str())
    {
        return Err(Failure::policy(
            phase,
            format!(
                "receipt `{unit_id}` audit root/theorem/specification bindings do not match Plane 1"
            ),
        ));
    }
    let expected_spec_mod = expected_unit.specification_module.as_deref().unwrap_or("Spec");
    let spec_closure = audit
        .get("specificationClosure")
        .and_then(Value::as_array)
        .ok_or_else(|| {
            Failure::policy(phase, format!("receipt `{unit_id}` missing audit.specificationClosure"))
        })?;
    let binds_spec = spec_closure.iter().any(|entry| {
        entry.get("name").and_then(Value::as_str) == Some(expected_unit.specification.as_str())
            && entry.get("module").and_then(Value::as_str) == Some(expected_spec_mod)
    });
    if !binds_spec {
        return Err(Failure::policy(
            phase,
            format!(
                "receipt `{unit_id}` audit.specificationClosure does not bind `{}` in `{expected_spec_mod}`",
                expected_unit.specification
            ),
        ));
    }
    let axioms = audit.get("axioms").and_then(Value::as_array).ok_or_else(|| {
        Failure::policy(phase, format!("receipt `{unit_id}` missing audit.axioms"))
    })?;
    for ax in axioms {
        let name = ax
            .as_str()
            .ok_or_else(|| Failure::policy(phase, format!("non-string axiom in `{unit_id}`")))?;
        if name == "sorryAx" && opts.require_untainted {
            return Err(Failure::policy(phase, format!("receipt `{unit_id}` contains `sorryAx`")));
        }
        if name != "sorryAx" && !allowed_axioms.contains(&name) {
            return Err(Failure::policy(
                phase,
                format!("receipt `{unit_id}` uses disallowed axiom `{name}`"),
            ));
        }
        transitive_axioms.insert(name.to_owned());
    }

    // Provenance / attestation enforcement (`D4-A`, §4.3): required whenever
    // `--require-attestation` is passed or the receipt claims external remote
    // containment (`external_unverified_by_binary`). This verifier does not
    // yet check DSSE signatures, signer identities, or predicate subjects, so
    // it cannot authenticate an attestation and rejects every receipt that
    // needs one rather than accepting an unverified envelope.
    let claims_remote_unverified = sandbox == "external_unverified_by_binary"
        || receipt
            .get("elaboration_containment")
            .and_then(|c| c.get("enforcer"))
            .and_then(Value::as_str)
            == Some("external_unverified_by_binary");
    if opts.require_attestation || claims_remote_unverified {
        let detail = if su.attestation_path.is_some() {
            "DSSE signature verification is not implemented, so its attestation cannot \
             be authenticated"
        } else {
            "it has no `attestation_path`, and DSSE signature verification is not \
             implemented"
        };
        return Err(Failure::policy(
            phase,
            format!(
                "E_ANNEAL_UNATTESTED_REMOTE_RECEIPT: slice `{slice_id}` unit `{unit_id}` \
                 requires an authenticated attestation, but {detail}"
            ),
        ));
    }
    if let Some(att_rel) = su.attestation_path.as_deref()
        && !is_clean_relative_path(att_rel)
    {
        return Err(Failure::policy(phase, format!("invalid attestation_path {att_rel:?}")));
    }
    Ok(())
}

fn validate_carrier_cargo_toml(
    cargo_toml_path: &Path,
    subject_crate: &str,
    subject_version: &str,
    phase: &str,
) -> Result<(), Failure> {
    let (bytes, _) = read_regular_file_strict(cargo_toml_path, None, phase)?;
    let text = std::str::from_utf8(&bytes)
        .map_err(|e| Failure::policy(phase, format!("carrier Cargo.toml is not UTF-8: {e}")))?;
    let doc: toml::Value = toml::from_str(text)
        .map_err(|e| Failure::policy(phase, format!("invalid carrier Cargo.toml: {e}")))?;
    let pkg = doc
        .get("package")
        .and_then(toml::Value::as_table)
        .ok_or_else(|| Failure::policy(phase, "carrier Cargo.toml missing `[package]`"))?;
    if pkg.contains_key("include") && pkg.contains_key("exclude") {
        return Err(Failure::policy(
            phase,
            "E_ANNEAL_INCLUDE_SHADOWS_EXCLUDE: carrier Cargo.toml sets both `include` and `exclude`",
        ));
    }
    if let Some(build) = pkg.get("build")
        && build.as_bool() != Some(false)
    {
        return Err(Failure::policy(
            phase,
            "evidence carrier crate must not declare `package.build`",
        ));
    }
    if doc
        .get("lib")
        .and_then(|l| l.get("proc-macro").or_else(|| l.get("proc_macro")))
        .and_then(toml::Value::as_bool)
        == Some(true)
    {
        return Err(Failure::policy(
            phase,
            "evidence carrier crate must not be a `proc-macro` crate",
        ));
    }
    let ver = pkg
        .get("version")
        .and_then(toml::Value::as_str)
        .ok_or_else(|| Failure::policy(phase, "carrier Cargo.toml missing `package.version`"))?;
    validate_evidence_carrier_version(ver, subject_crate, subject_version)?;
    for forbidden_sec in ["dependencies", "build-dependencies", "build_dependencies"] {
        if doc.get(forbidden_sec).and_then(toml::Value::as_table).is_some_and(|t| !t.is_empty()) {
            return Err(Failure::policy(
                phase,
                format!("evidence carrier crate must have zero `{forbidden_sec}`"),
            ));
        }
    }
    if let Some(targets) = doc.get("target").and_then(toml::Value::as_table) {
        for (cfg_key, cfg_val) in targets {
            if let Some(cfg_tbl) = cfg_val.as_table() {
                for forbidden_sec in ["dependencies", "build-dependencies", "build_dependencies"] {
                    if cfg_tbl
                        .get(forbidden_sec)
                        .and_then(toml::Value::as_table)
                        .is_some_and(|t| !t.is_empty())
                    {
                        return Err(Failure::policy(
                            phase,
                            format!(
                                "evidence carrier crate must have zero `target.{cfg_key}.{forbidden_sec}`"
                            ),
                        ));
                    }
                }
            }
        }
    }
    Ok(())
}

/// Matches a consumer's `(canonical_program_sha256, SemanticProfile)` for
/// `unit_id` against a verified [`EvidenceBundleManifest`] (`O(1)` lookup).
pub fn match_consumer_slice<'a>(
    evidence: &'a EvidenceBundleManifest,
    unit_id: &str,
    consumer_canonical_program_sha256: &str,
    consumer_profile: &SemanticProfile,
) -> Result<(&'a str, &'a EvidenceSliceUnit), Failure> {
    let mut closest_diff: Option<(String, Vec<String>, String)> = None;
    for (slice_id, slice) in &evidence.slices {
        let Some(su) = slice.units.get(unit_id) else {
            continue;
        };
        if &slice.semantic_profile == consumer_profile
            && su.canonical_program_sha256 == consumer_canonical_program_sha256
        {
            return Ok((slice_id.as_str(), su));
        }
        let diffs = consumer_profile.diff_summary(&slice.semantic_profile);
        let replace = match &closest_diff {
            None => true,
            Some((_, prev_diffs, _)) => diffs.len() < prev_diffs.len(),
        };
        if replace {
            closest_diff = Some((slice_id.clone(), diffs, su.canonical_program_sha256.clone()));
        }
    }
    let detail = match closest_diff {
        Some((closest_slice, diffs, slice_prog_sha)) if diffs.is_empty() => format!(
            "E_ANNEAL_SLICE_UNVERIFIED: no slice in anneal-evidence.json matched unit `{unit_id}` \
             `canonical_program_sha256`={consumer_canonical_program_sha256} \
             (closest slice `{closest_slice}` had identical SemanticProfile but MIR digest {slice_prog_sha})"
        ),
        Some((closest_slice, diffs, _)) => format!(
            "E_ANNEAL_SLICE_UNVERIFIED: no slice in anneal-evidence.json matched unit `{unit_id}`; \
             closest slice `{closest_slice}` differed on SemanticProfile: {}",
            diffs.join(", ")
        ),
        None => format!(
            "E_ANNEAL_SLICE_UNVERIFIED: unit `{unit_id}` has no pre-verified slices in anneal-evidence.json"
        ),
    };
    Err(Failure::policy("slice-match", detail))
}

/// Extracts a `.tar.zst` archive into `dest_dir`, optionally verifying
/// `expected_sha256` over the compressed stream before passing any bytes to
/// `zstd` or `tar`, and rejecting symlinks, hardlinks, device nodes, or parent
/// path traversals.
#[cfg(feature = "setup")]
pub fn extract_tar_zst_strict(
    archive_path: &Path,
    expected_sha256: Option<&str>,
    dest_dir: &Path,
) -> Result<String, Failure> {
    let phase = "archive";
    regular(archive_path, phase)?;
    let (compressed_bytes, actual_sha) = read_regular_file_strict(archive_path, None, phase)?;
    if let Some(expected) = expected_sha256 {
        if !is_sha256_hex(expected) {
            return Err(Failure::policy(
                phase,
                format!("invalid expected SHA-256 hex string: {expected:?}"),
            ));
        }
        if !actual_sha.eq_ignore_ascii_case(expected) {
            return Err(Failure::policy(
                phase,
                format!(
                    "archive SHA-256 mismatch for {}: expected {expected}, got {actual_sha}",
                    archive_path.display()
                ),
            ));
        }
    }
    let decoder = zstd::stream::read::Decoder::new(compressed_bytes.as_slice()).map_err(|e| {
        Failure::policy(phase, format!("invalid zstd stream in {}: {e}", archive_path.display()))
    })?;
    unpack_tar_regular_only(decoder, dest_dir, phase)?;
    Ok(actual_sha)
}

/// Whether `component` names the same file on every supported file system:
/// Windows strips trailing `.` and ` `, and reserves device names by stem.
fn is_portable_path_component(component: &str) -> bool {
    if component.ends_with(['.', ' ']) {
        return false;
    }
    let stem = component.split('.').next().unwrap_or_default().trim_end_matches(' ');
    let upper = stem.to_ascii_uppercase();
    // `COM0`-`COM9` and `LPT0`-`LPT9`, plus superscript `COM¹` etc.
    let is_numbered_device = |prefix: &str| {
        upper.strip_prefix(prefix).is_some_and(|n| {
            (n.len() == 1 && n.as_bytes()[0].is_ascii_digit())
                || matches!(n, "\u{b9}" | "\u{b2}" | "\u{b3}")
        })
    };
    !(matches!(upper.as_str(), "CON" | "PRN" | "AUX" | "NUL")
        || is_numbered_device("COM")
        || is_numbered_device("LPT"))
}

/// A key under which two archive paths collide if a case-insensitive file
/// system (Windows, default macOS) may map them to the same file. The Unicode
/// case fold is deliberately coarse: extra collisions only reject more
/// archives.
fn path_collision_key(path: &str) -> String {
    path.to_uppercase().to_lowercase()
}

fn unpack_tar_regular_only<R: std::io::Read>(
    reader: R,
    dest_dir: &Path,
    phase: &str,
) -> Result<Vec<String>, Failure> {
    let mut archive = tar::Archive::new(reader);
    let mut unpacked_paths = Vec::new();
    let mut seen_files = BTreeSet::new();
    let entries = archive
        .entries()
        .map_err(|e| Failure::policy(phase, format!("invalid tar header: {e}")))?;
    for entry_res in entries {
        let mut entry =
            entry_res.map_err(|e| Failure::policy(phase, format!("invalid tar entry: {e}")))?;
        let entry_type = entry.header().entry_type();
        let raw_path = entry
            .path()
            .map_err(|e| Failure::policy(phase, format!("non-UTF-8 or invalid tar path: {e}")))?
            .into_owned();
        let rel_str = rel_path_to_posix_utf8(&raw_path, phase)?;
        if let Some(component) = rel_str.split('/').find(|c| !is_portable_path_component(c)) {
            return Err(Failure::policy(
                phase,
                format!("tar entry `{rel_str}` has non-portable path component `{component}`"),
            ));
        }
        if entry_type.is_dir() {
            fs::create_dir_all(dest_dir.join(&rel_str)).map_err(|e| {
                Failure::operational(phase, format!("cannot create dir {rel_str}: {e}"))
            })?;
            continue;
        }
        if !entry_type.is_file() {
            return Err(Failure::policy(
                phase,
                format!("forbidden non-regular tar entry `{rel_str}` ({entry_type:?})"),
            ));
        }
        if !seen_files.insert(path_collision_key(&rel_str)) {
            return Err(Failure::policy(
                phase,
                format!("duplicate (or case-insensitively equal) tar entry `{rel_str}`"),
            ));
        }
        let out_path = dest_dir.join(&rel_str);
        if let Some(parent) = out_path.parent() {
            fs::create_dir_all(parent).map_err(|e| {
                Failure::operational(phase, format!("cannot create parent for {rel_str}: {e}"))
            })?;
        }
        let mut bytes = Vec::new();
        entry.read_to_end(&mut bytes).map_err(|e| {
            Failure::policy(phase, format!("failed reading tar entry `{rel_str}`: {e}"))
        })?;
        fs::write(&out_path, &bytes)
            .map_err(|e| Failure::operational(phase, format!("cannot write `{rel_str}`: {e}")))?;
        unpacked_paths.push(rel_str);
    }
    Ok(unpacked_paths)
}

/// Runs `cargo package --allow-dirty --no-verify --exclude-lockfile` into a
/// private staging directory, inspects the produced `.crate` `.tar.gz` archive,
/// asserts zero `proofs/` or `.olean*` leaks and `< 10 MiB` compressed size,
/// and verifies byte-identical `source_closure_sha256`,
/// `contract_manifest_sha256`, and `anneal_toml_sha256` after unpacking!
pub fn verify_packaged_crate_roundtrip(
    crate_dir: &Path,
    pkg: &ValidatedCargoPackage,
    expected_closure: &SourceClosureReport,
    expected_plane1: &ContractPlaneDigests,
) -> Result<u64, Failure> {
    let phase = "package-check";
    let canon_crate_dir = fs::canonicalize(crate_dir).map_err(|e| {
        Failure::operational(phase, format!("cannot canonicalize {}: {e}", crate_dir.display()))
    })?;
    let temp = tempfile::Builder::new()
        .prefix("anneal-pkg-check-")
        .tempdir()
        .map_err(|e| Failure::operational(phase, format!("tempdir failed: {e}")))?;
    let target_dir = temp.path().join("target");
    let mut cmd = Command::new("cargo");
    cmd.current_dir(temp.path()).env_clear();
    for key in ["PATH", "HOME", "CARGO_HOME", "RUSTUP_HOME", "TMPDIR"] {
        if let Some(val) = std::env::var_os(key) {
            cmd.env(key, val);
        }
    }
    let out = cmd
        .args([
            "package",
            "--allow-dirty",
            "--no-verify",
            "--exclude-lockfile",
            "--offline",
            "--manifest-path",
        ])
        .arg(canon_crate_dir.join("Cargo.toml"))
        .arg("--target-dir")
        .arg(&target_dir)
        .output()
        .map_err(|e| Failure::operational(phase, format!("cannot invoke `cargo package`: {e}")))?;
    if !out.status.success() {
        return Err(Failure::policy(
            phase,
            format!("`cargo package` failed: {}", String::from_utf8_lossy(&out.stderr).trim()),
        ));
    }

    let crate_archive =
        target_dir.join("package").join(format!("{}-{}.crate", pkg.name, pkg.version));
    let (archive_bytes, _) = read_regular_file_strict(&crate_archive, None, phase)?;
    let compressed_size = archive_bytes.len() as u64;
    if compressed_size > CRATES_IO_MAX_COMPRESSED_BYTES {
        return Err(Failure::policy(
            phase,
            format!(".crate archive exceeds 10 MiB crates.io limit: {compressed_size} bytes"),
        ));
    }

    let unpack_root = temp.path().join("unpacked");
    fs::create_dir_all(&unpack_root)
        .map_err(|e| Failure::operational(phase, format!("mkdir failed: {e}")))?;
    let gz = GzDecoder::new(archive_bytes.as_slice());
    let entries = unpack_tar_regular_only(gz, &unpack_root, phase)?;
    let prefix = format!("{}-{}/", pkg.name, pkg.version);
    for entry in &entries {
        let inner = entry.strip_prefix(&prefix).unwrap_or(entry.as_str());
        let lower = inner.to_ascii_lowercase();
        if lower.starts_with("proofs/") || lower == "proof.lean" || lower.ends_with("/proof.lean") {
            return Err(Failure::policy(
                phase,
                format!(
                    "E_ANNEAL_PROOF_IN_CONTRACT_PLANE: proof file leaked into .crate tarball: {inner}"
                ),
            ));
        }
        if FORBIDDEN_BINARY_LEAN_SUFFIXES.iter().any(|ext| lower.ends_with(ext)) {
            return Err(Failure::policy(
                phase,
                format!(
                    "E_ANNEAL_BINARY_OLEAN_FORBIDDEN: binary Lean file leaked into .crate tarball: {inner}"
                ),
            ));
        }
    }

    let unpacked_crate_dir = unpack_root.join(format!("{}-{}", pkg.name, pkg.version));
    // Consumers see the normalized Cargo.toml that `cargo package` writes, so
    // the closure is recomputed from it rather than from the original.
    let unpacked_pkg = validate_crate_cargo_toml(&unpacked_crate_dir)?;
    let unpacked_closure = compute_source_closure_sha256(
        &unpacked_crate_dir,
        &unpacked_pkg.name,
        &unpacked_pkg.edition,
        &unpacked_pkg.cargo_semantics(),
        &[],
    )?;
    if unpacked_closure.source_closure_sha256 != expected_closure.source_closure_sha256 {
        return Err(Failure::policy(
            phase,
            format!(
                "source_closure_sha256 drifted across `cargo package` ({} vs {})",
                unpacked_closure.source_closure_sha256, expected_closure.source_closure_sha256
            ),
        ));
    }
    let unpacked_plane1 = inspect_contract_plane(&unpacked_crate_dir, &pkg.anneal_manifest_rel)?;
    if unpacked_plane1.anneal_toml_sha256 != expected_plane1.anneal_toml_sha256
        || unpacked_plane1.contract_manifest_sha256 != expected_plane1.contract_manifest_sha256
    {
        return Err(Failure::policy(
            phase,
            "Plane 1 contract digests drifted across `cargo package`",
        ));
    }
    Ok(compressed_size)
}

/// Computes the transitive closure of active Cargo feature names enabled by
/// `slice` against `pkg.features`.
pub fn resolve_slice_feature_closure(
    pkg: &ValidatedCargoPackage,
    slice: &ManifestSlice,
) -> Result<BTreeSet<String>, Failure> {
    let phase = "slice-cfg";
    let mut active_features = BTreeSet::new();
    let mut queue = Vec::new();
    if slice.default_features && pkg.features.contains_key("default") {
        queue.push("default".to_owned());
    }
    for feat in &slice.features {
        if !pkg.features.contains_key(feat) {
            return Err(Failure::policy(
                phase,
                format!("slice enables undeclared Cargo feature `{feat}`"),
            ));
        }
        queue.push(feat.clone());
    }
    while let Some(feat) = queue.pop() {
        if !active_features.insert(feat.clone()) {
            continue;
        }
        if let Some(deps) = pkg.features.get(&feat) {
            for dep in deps {
                // Only propagate local package features (`foo`), skipping
                // optional crate/dep activations (`dep:x`, `x/y`, `x?/y`).
                if !dep.starts_with("dep:") && !dep.contains('/') && pkg.features.contains_key(dep)
                {
                    queue.push(dep.clone());
                }
            }
        }
    }
    Ok(active_features)
}

/// Resolves Cargo feature transitive closures and `[package.metadata.build-rs]`
/// version-gated negative `cfg`s for a slice in `anneal/anneal.toml`.
pub fn resolve_slice_cfgs(
    pkg: &ValidatedCargoPackage,
    slice: &ManifestSlice,
    rustc_semver: Option<(u64, u64, u64)>,
) -> Result<BTreeSet<String>, Failure> {
    let active_features = resolve_slice_feature_closure(pkg, slice)?;

    let mut cfgs = BTreeSet::new();
    for feat in &active_features {
        cfgs.insert(format!("feature=\"{feat}\""));
    }
    if let Some(compiler_ver) = rustc_semver {
        for (cfg_name, threshold_raw) in &pkg.build_rs_version_cfgs {
            if let Some(threshold) = parse_msrv_triple(threshold_raw)
                && compiler_ver < threshold
            {
                cfgs.insert(cfg_name.clone());
            }
        }
    }
    for explicit_cfg in &slice.cfg {
        cfgs.insert(explicit_cfg.clone());
    }
    Ok(cfgs)
}

/// Standard `CARGO_PKG_*` compile-time environment bindings derived from
/// `Cargo.toml` so `anneal/anneal.toml` never hardcodes stale release versions.
pub fn derive_cargo_pkg_env(pkg: &ValidatedCargoPackage) -> BTreeMap<String, String> {
    let mut env = BTreeMap::new();
    env.insert("CARGO_PKG_NAME".to_owned(), pkg.name.clone());
    env.insert("CARGO_PKG_VERSION".to_owned(), pkg.version.clone());
    let without_build = pkg.version.split('+').next().unwrap_or(&pkg.version);
    let (core, pre) = match without_build.split_once('-') {
        Some((c, p)) => (c, p),
        None => (without_build, ""),
    };
    let mut parts = core.split('.');
    env.insert("CARGO_PKG_VERSION_MAJOR".to_owned(), parts.next().unwrap_or("0").to_owned());
    env.insert("CARGO_PKG_VERSION_MINOR".to_owned(), parts.next().unwrap_or("0").to_owned());
    env.insert("CARGO_PKG_VERSION_PATCH".to_owned(), parts.next().unwrap_or("0").to_owned());
    env.insert("CARGO_PKG_VERSION_PRE".to_owned(), pre.to_owned());
    env
}

/// CLI arguments for `cargo anneal package-check`.
#[derive(clap::Args, Debug, Clone)]
pub struct PackageCheckArgs {
    /// Path to the crate's `Cargo.toml`.
    #[arg(long, value_name = "PATH")]
    pub manifest_path: PathBuf,
    /// Optional unpacked `<crate>-anneal-proofs` directory to cross-verify.
    #[cfg_attr(
        feature = "setup",
        arg(long, value_name = "DIR", conflicts_with = "evidence_archive")
    )]
    #[cfg_attr(not(feature = "setup"), arg(long, value_name = "DIR"))]
    pub evidence_dir: Option<PathBuf>,
    /// Optional Stage 0 `.tar.zst` evidence bundle archive to cross-verify.
    #[cfg(feature = "setup")]
    #[arg(long, value_name = "PATH", conflicts_with = "evidence_dir")]
    pub evidence_archive: Option<PathBuf>,
    /// Expected lowercase 64-hex SHA-256 of `--evidence-archive`.
    #[cfg(feature = "setup")]
    #[arg(long, value_name = "SHA256", requires = "evidence_archive")]
    pub evidence_sha256: Option<String>,
    /// Run `cargo package --offline` and verify `.crate` tarball hygiene and
    /// digest round-trip invariance.
    #[arg(long)]
    pub run_cargo_package: bool,
    /// Require untainted slice receipts (`taint_reasons: []`) when validating
    /// evidence.
    #[arg(long)]
    pub require_untainted: bool,
    /// Require Sigstore DSSE attestations on all verified slice receipts.
    /// DSSE signature verification is not implemented yet, so every slice
    /// receipt is rejected while this flag is set.
    #[arg(long)]
    pub require_attestation: bool,
}

/// Executes `cargo anneal package-check` and returns pretty-printed JSON.
pub fn run_package_check(args: &PackageCheckArgs) -> Result<String, Failure> {
    let phase = "package-check";
    regular(&args.manifest_path, phase)?;
    let canon_manifest = fs::canonicalize(&args.manifest_path).map_err(|e| {
        Failure::operational(
            phase,
            format!("cannot canonicalize {}: {e}", args.manifest_path.display()),
        )
    })?;
    let crate_dir = canon_manifest
        .parent()
        .ok_or_else(|| Failure::policy(phase, "manifest path has no parent directory"))?;

    let pkg = validate_crate_cargo_toml(crate_dir)?;
    let source_closure = compute_source_closure_sha256(
        crate_dir,
        &pkg.name,
        &pkg.edition,
        &pkg.cargo_semantics(),
        &[],
    )?;
    let plane1 = inspect_contract_plane(crate_dir, &pkg.anneal_manifest_rel)?;
    verify_unexpected_cfgs_guard(crate_dir, plane1.inline_attr_count)?;

    if plane1.total_plane1_bytes > PLANE1_CONTRACT_MAX_BYTES {
        return Err(Failure::policy(
            phase,
            format!(
                "Plane 1 `anneal/` directory ({} bytes) exceeds {} KiB contract plane budget",
                plane1.total_plane1_bytes,
                PLANE1_CONTRACT_MAX_BYTES / 1024
            ),
        ));
    }

    let packaged_crate_bytes = if args.run_cargo_package {
        Some(verify_packaged_crate_roundtrip(crate_dir, &pkg, &source_closure, &plane1)?)
    } else {
        None
    };

    let ev_opts = EvidenceVerifyOptions {
        require_untainted: args.require_untainted,
        require_attestation: args.require_attestation,
    };
    #[cfg_attr(not(feature = "setup"), allow(unused_mut))]
    let mut archive_sha256_verified: Option<String> = None;
    let evidence_report = if let Some(ev_dir) = &args.evidence_dir {
        let (_, rep) = verify_evidence_carrier_dir(
            crate_dir,
            &pkg,
            &source_closure,
            &plane1,
            ev_dir,
            &ev_opts,
        )?;
        Some(rep)
    } else {
        #[cfg(feature = "setup")]
        if let Some(ev_archive) = &args.evidence_archive {
            let tmp = tempfile::Builder::new()
                .prefix("anneal-ev-archive-")
                .tempdir()
                .map_err(|e| Failure::operational(phase, format!("tempdir failed: {e}")))?;
            let sha =
                extract_tar_zst_strict(ev_archive, args.evidence_sha256.as_deref(), tmp.path())?;
            archive_sha256_verified = Some(sha);
            let (_, rep) = verify_evidence_carrier_dir(
                crate_dir,
                &pkg,
                &source_closure,
                &plane1,
                tmp.path(),
                &ev_opts,
            )?;
            Some(rep)
        } else {
            None
        }
        #[cfg(not(feature = "setup"))]
        {
            None
        }
    };

    let mut out = json!({
        "status": "package_ok",
        "crate_name": pkg.name,
        "crate_version": pkg.version,
        "edition": pkg.edition,
        "rust_version": pkg.rust_version,
        "source_closure_sha256": source_closure.source_closure_sha256,
        "source_file_count": source_closure.files.len(),
        "anneal_toml_sha256": plane1.anneal_toml_sha256,
        "specification_manifest_sha256": plane1.contract_manifest_sha256,
        "plane1_bytes": plane1.total_plane1_bytes,
        "unit_ids": plane1.manifest.units.iter().map(|u| &u.id).collect::<Vec<_>>(),
        "slice_ids": plane1.manifest.slices.keys().collect::<Vec<_>>(),
    });
    if let Some(sz) = packaged_crate_bytes {
        out.as_object_mut().unwrap().insert("packaged_crate_compressed_bytes".into(), json!(sz));
    }
    if let Some(sha) = archive_sha256_verified {
        out.as_object_mut().unwrap().insert("evidence_archive_sha256".into(), json!(sha));
    }
    if let Some(rep) = evidence_report {
        out.as_object_mut().unwrap().insert("evidence".into(), serde_json::to_value(rep).unwrap());
    }
    let mut rendered = serde_json::to_string_pretty(&out)
        .map_err(|e| Failure::operational(phase, format!("JSON render failed: {e}")))?;
    rendered.push('\n');
    Ok(rendered)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn write_minimal_crate(dir: &Path) {
        fs::create_dir_all(dir.join("src")).unwrap();
        fs::create_dir_all(dir.join("anneal/specs")).unwrap();
        fs::write(
            dir.join("Cargo.toml"),
            r#"[package]
name = "demo-crate"
version = "0.8.64"
edition = "2021"
rust-version = "1.56.0"
exclude = [".*", "/proofs"]

[package.metadata.anneal]
manifest = "anneal/anneal.toml"
evidence_crate = "demo-crate-anneal-proofs"

[package.metadata.build-rs]
no-demo-alloc-1-100-0 = "1.100.0"

[features]
alloc = []
simd = []
"#,
        )
        .unwrap();
        fs::write(
            dir.join("build.rs"),
            "fn main() { println!(\"cargo:rustc-check-cfg=cfg(anneal)\"); }\n",
        )
        .unwrap();
        fs::write(
            dir.join("src/lib.rs"),
            "#[cfg_attr(anneal, anneal::spec(ensures = \"ret == x\"))]\npub fn id(x: usize) -> usize { x }\n",
        )
        .unwrap();
        fs::write(dir.join("anneal/specs/id_spec.lean"), "prelude\nnamespace Spec\nend Spec\n")
            .unwrap();
        fs::write(
            dir.join("anneal/anneal.toml"),
            r#"schema_version = 1

[package]
spec_format = "anneal-lean-v1"
lean_compat = ">=4.34.1, <4.36.0"
mir_model_schema = 1

[evidence]
carrier_crate = "demo-crate-anneal-proofs"

[[units]]
id = "01_id"
scope = { kind = "selected_unit", roots = ["id"] }
spec_modules = [{ module = "Spec", path = "specs/id_spec.lean" }]

[slices.core_linux_x86_64]
target = "x86_64-unknown-linux-gnu"
features = []
default_features = false
"#,
        )
        .unwrap();
    }

    #[test]
    fn rejects_include_and_exclude_together_and_msrv_features2() {
        let tmp = tempfile::tempdir().unwrap();
        write_minimal_crate(tmp.path());
        let orig = fs::read_to_string(tmp.path().join("Cargo.toml")).unwrap();
        fs::write(
            tmp.path().join("Cargo.toml"),
            format!("{orig}\n# bad\n").replace(
                "exclude = [\".*\", \"/proofs\"]",
                "include = [\"/src/**\"]\nexclude = [\"/proofs\"]",
            ),
        )
        .unwrap();
        let err = validate_crate_cargo_toml(tmp.path()).unwrap_err();
        assert!(err.message.contains("E_ANNEAL_INCLUDE_SHADOWS_EXCLUDE"), "{err}");

        fs::write(
            tmp.path().join("Cargo.toml"),
            orig.replace("alloc = []", "alloc = [\"dep:foo\"]"),
        )
        .unwrap();
        let err = validate_crate_cargo_toml(tmp.path()).unwrap_err();
        assert!(err.message.contains("E_ANNEAL_MSRV_FEATURES2"), "{err}");
    }

    #[test]
    fn source_closure_ignores_cargo_packaging_files_and_catches_injected_rs() {
        let tmp = tempfile::tempdir().unwrap();
        write_minimal_crate(tmp.path());
        let base = compute_source_closure_sha256(
            tmp.path(),
            "demo-crate",
            "2021",
            &empty_cargo_semantics(),
            &[],
        )
        .unwrap();

        // Simulate `cargo package` / `cargo vendor` metadata rewrites and
        // `.cargo-checksum.json` clearing (`{"files":{}}`).
        fs::write(tmp.path().join("Cargo.toml.orig"), b"orig").unwrap();
        fs::write(tmp.path().join(".cargo_vcs_info.json"), b"{}").unwrap();
        fs::write(tmp.path().join(".cargo-checksum.json"), b"{\"files\":{}}").unwrap();
        let vendor_closure = compute_source_closure_sha256(
            tmp.path(),
            "demo-crate",
            "2021",
            &empty_cargo_semantics(),
            &[],
        )
        .unwrap();
        assert_eq!(base.source_closure_sha256, vendor_closure.source_closure_sha256);

        // Comment shifts around inline `#[cfg_attr(anneal, ...)]` keep
        // `contract_manifest_sha256` invariant, while changing contract tokens
        // alters it. Also exercise char literals and raw strings containing
        // decoy quotes, comments, or attributes.
        let p1_before = inspect_contract_plane(tmp.path(), "anneal/anneal.toml").unwrap();
        fs::write(
            tmp.path().join("src/lib.rs"),
            "// extra comment line\n\
             const Q: char = '\"';\n\
             const DECOY: &str = r#\"#[cfg_attr(anneal, decoy)] \"#;\n\
             #[cfg_attr(anneal,   /* inline comment */ anneal::spec( ensures = \"ret == x\" ))]\n\
             pub fn id<'a>(x: &'a usize) -> &'a usize { x }\n",
        )
        .unwrap();
        let p1_comment_shift = inspect_contract_plane(tmp.path(), "anneal/anneal.toml").unwrap();
        assert_eq!(p1_before.contract_manifest_sha256, p1_comment_shift.contract_manifest_sha256);

        fs::write(
            tmp.path().join("src/lib.rs"),
            "#[cfg_attr(anneal, anneal::spec(ensures = \"ret >= x\"))]\npub fn id(x: usize) -> usize { x }\n",
        )
        .unwrap();
        let p1_mutated = inspect_contract_plane(tmp.path(), "anneal/anneal.toml").unwrap();
        assert_ne!(p1_before.contract_manifest_sha256, p1_mutated.contract_manifest_sha256);

        // Decoy raw string after identifier (`foo_r#"..."#`) vs real raw string
        // must still keep subsequent `#[cfg_attr(anneal, ...)]` intact.
        let extracted = extract_inline_anneal_cfg_attrs(
            "let q = '\"'; let bq = b'\"'; let r = r#\" #[cfg_attr(anneal, bad)] \" \"#;\n\
             #[cfg_attr(anneal, doc = \"good\")]\npub fn f() {}\n",
        );
        assert_eq!(extracted, vec!["#[cfg_attr(anneal,doc = \"good\")]"]);

        // Injecting an undeclared `.rs` file under `src/` must alter
        // `source_closure_sha256`.
        fs::write(
            tmp.path().join("src/lib.rs"),
            "#[cfg_attr(anneal, anneal::spec(ensures = \"ret == x\"))]\npub fn id(x: usize) -> usize { x }\n",
        )
        .unwrap();
        fs::write(tmp.path().join("src/injected_mod.rs"), "pub fn backdoor() {}\n").unwrap();
        let tampered = compute_source_closure_sha256(
            tmp.path(),
            "demo-crate",
            "2021",
            &empty_cargo_semantics(),
            &[],
        )
        .unwrap();
        assert_ne!(base.source_closure_sha256, tampered.source_closure_sha256);
    }

    #[test]
    fn source_closure_binds_cargo_semantics_lib_name_and_version() {
        let tmp = tempfile::tempdir().unwrap();
        write_minimal_crate(tmp.path());
        let closure_of = |dir: &Path| {
            let pkg = validate_crate_cargo_toml(dir).unwrap();
            compute_source_closure_sha256(dir, &pkg.name, &pkg.edition, &pkg.cargo_semantics(), &[])
                .unwrap()
                .source_closure_sha256
        };
        let base = closure_of(tmp.path());
        let cargo_toml = fs::read_to_string(tmp.path().join("Cargo.toml")).unwrap();

        // Re-pointing a feature changes the `--cfg feature=...` set that a
        // slice compiles with, so it must change the closure.
        fs::write(
            tmp.path().join("Cargo.toml"),
            cargo_toml.replace("simd = []", "simd = [\"alloc\"]"),
        )
        .unwrap();
        assert_ne!(base, closure_of(tmp.path()));

        // So must a version-cfg threshold and a `[lib] name` override.
        fs::write(tmp.path().join("Cargo.toml"), cargo_toml.replace("\"1.100.0\"", "\"1.90.0\""))
            .unwrap();
        assert_ne!(base, closure_of(tmp.path()));
        fs::write(
            tmp.path().join("Cargo.toml"),
            format!("{cargo_toml}\n[lib]\nname = \"other\"\n"),
        )
        .unwrap();
        assert_eq!(
            validate_crate_cargo_toml(tmp.path()).unwrap().lib_name.as_deref(),
            Some("other")
        );
        assert_ne!(base, closure_of(tmp.path()));

        // `CARGO_PKG_VERSION*` reach the program, so the version is bound.
        fs::write(
            tmp.path().join("Cargo.toml"),
            cargo_toml.replace("version = \"0.8.64\"", "version = \"0.8.65\""),
        )
        .unwrap();
        assert_ne!(base, closure_of(tmp.path()));

        // An explicit `[lib] name` equal to the default, as `cargo package`
        // writes into the normalized Cargo.toml, names the same crate.
        fs::write(
            tmp.path().join("Cargo.toml"),
            format!("{cargo_toml}\n[lib]\nname = \"demo_crate\"\npath = \"src/lib.rs\"\n"),
        )
        .unwrap();
        assert_eq!(base, closure_of(tmp.path()));

        // Restoring the manifest restores the digest.
        fs::write(tmp.path().join("Cargo.toml"), &cargo_toml).unwrap();
        assert_eq!(base, closure_of(tmp.path()));
    }

    #[test]
    fn unpack_rejects_case_folded_duplicates_and_windows_aliases() {
        let tar_of = |paths: &[&str]| {
            let mut builder = tar::Builder::new(Vec::new());
            for path in paths {
                let mut header = tar::Header::new_gnu();
                header.set_size(1);
                header.set_mode(0o644);
                header.set_entry_type(tar::EntryType::Regular);
                // `set_path` would reject some of these names itself.
                header.as_gnu_mut().unwrap().name[..path.len()]
                    .copy_from_slice(path.as_bytes());
                header.set_cksum();
                builder.append(&header, &b"x"[..]).unwrap();
            }
            builder.into_inner().unwrap()
        };
        let unpack = |paths: &[&str]| {
            let dest = tempfile::tempdir().unwrap();
            unpack_tar_regular_only(tar_of(paths).as_slice(), dest.path(), "test")
        };
        for paths in [
            &["src/Lib.rs", "src/lib.rs"][..],
            &["SRC/lib.rs", "src/lib.rs"],
            &["src/\u{212a}.rs", "src/k.rs"],
        ] {
            let err = unpack(paths).unwrap_err();
            assert!(err.message.contains("duplicate"), "{paths:?}: {err}");
        }
        for path in
            ["src/lib.rs.", "src/lib.rs ", "src./lib.rs", "src/nul.rs", "src/COM1", "src/con .rs"]
        {
            let err = unpack(&[path]).unwrap_err();
            assert!(err.message.contains("non-portable"), "{path:?}: {err}");
        }
        let ok = ["src/lib.rs", "src/lib.rs.bak", "src/console.rs", "src/com10.rs"];
        assert_eq!(unpack(&ok).unwrap().len(), 4);
    }

    #[test]
    fn rejects_verifier_dependencies_renamed_with_package() {
        let tmp = tempfile::tempdir().unwrap();
        write_minimal_crate(tmp.path());
        let cargo_toml = fs::read_to_string(tmp.path().join("Cargo.toml")).unwrap();
        for (section, dep) in [
            ("dependencies", "anneal = { package = \"cargo-anneal\", version = \"0.2\" }"),
            ("build-dependencies", "spec = { package = \"anneal-spec\", version = \"0.1\" }"),
            (
                "target.'cfg(unix)'.dependencies",
                "proofs = { package = \"demo-crate-anneal-proofs\", version = \"0.1\" }",
            ),
        ] {
            fs::write(tmp.path().join("Cargo.toml"), format!("{cargo_toml}\n[{section}]\n{dep}\n"))
                .unwrap();
            let err = validate_crate_cargo_toml(tmp.path()).unwrap_err();
            assert!(err.message.contains("E_ANNEAL_VERIFIER_RUNTIME_DEP"), "{section}: {err}");
        }
        // An unrelated renamed dependency is still allowed.
        fs::write(
            tmp.path().join("Cargo.toml"),
            format!("{cargo_toml}\n[dependencies]\nbits = {{ package = \"bitflags\", version = \"2\" }}\n"),
        )
        .unwrap();
        validate_crate_cargo_toml(tmp.path()).unwrap();
    }

    #[test]
    fn diamond_disambiguation_and_evidence_semver_and_slice_matching() {
        let ns_07 = disambiguated_dep_namespace("zerocopy", "0.7.35", "svh_a").unwrap();
        let ns_08 = disambiguated_dep_namespace("zerocopy", "0.8.64", "svh_b").unwrap();
        assert_ne!(ns_07, ns_08);
        assert!(ns_07.starts_with("Deps.C_zerocopy_0_7_35_"));
        assert!(ns_08.starts_with("Deps.C_zerocopy_0_8_64_"));

        validate_evidence_carrier_version("0.1.0+zerocopy.0.8.64", "zerocopy", "0.8.64").unwrap();
        validate_evidence_carrier_version("0.1.1+zerocopy.0.8.64", "zerocopy", "0.8.64").unwrap();
        assert!(
            validate_evidence_carrier_version("0.1.0+zerocopy.0.8.63", "zerocopy", "0.8.64")
                .is_err()
        );

        let tmp = tempfile::tempdir().unwrap();
        write_minimal_crate(tmp.path());
        let pkg = validate_crate_cargo_toml(tmp.path()).unwrap();
        let closure = compute_source_closure_sha256(
            tmp.path(),
            &pkg.name,
            &pkg.edition,
            &pkg.cargo_semantics(),
            &[],
        )
        .unwrap();
        let plane1 = inspect_contract_plane(tmp.path(), &pkg.anneal_manifest_rel).unwrap();

        // Check build.rs version cfg resolution on 1.98.0 (< 1.100.0) vs 1.100.
        let slice = &plane1.manifest.slices["core_linux_x86_64"];
        let cfgs_198 = resolve_slice_cfgs(&pkg, slice, Some((1, 98, 0))).unwrap();
        assert!(cfgs_198.contains("no_demo_alloc_1_100_0"));
        let cfgs_1100 = resolve_slice_cfgs(&pkg, slice, Some((1, 100, 0))).unwrap();
        assert!(!cfgs_1100.contains("no_demo_alloc_1_100_0"));

        // Construct a valid Plane 2 evidence carrier and verify slice matching
        // + tamper/attestation rejections.
        let ev_dir = tmp.path().join("evidence");
        fs::create_dir_all(ev_dir.join("proofs/01_id")).unwrap();
        fs::create_dir_all(ev_dir.join("slices/core_linux_x86_64")).unwrap();
        let proof_bytes = b"prelude\nimport Expected\ntheorem verify : Expected.claim := sorry\n";
        let proof_sha = sha256_bytes(proof_bytes);
        fs::write(ev_dir.join("proofs/01_id/Proof.lean"), proof_bytes).unwrap();

        let profile = SemanticProfile {
            debug_assertions: false,
            endian: "little".into(),
            mir_preserve_ub: true,
            opt_level: 2,
            overflow_checks: false,
            panic: "unwind".into(),
            pointer_bits: 64,
            target: "x86_64-unknown-linux-gnu".into(),
        };
        let canon_prog_sha = "9".repeat(64);
        let expected_spec_sha =
            unit_specification_manifest_sha256(&plane1, &plane1.manifest.units[0])
                .unwrap()
                .unwrap();
        let proof_manifest_sha =
            proof_manifest_sha256(&BTreeMap::from([("Proof".to_owned(), proof_sha.clone())]))
                .unwrap();
        let build_receipt =
            |spec_sha: &str, closure_sha: &str, spec_name: &str, proof_manifest: &str| -> Vec<u8> {
                serde_json::to_vec_pretty(&json!({
                    "schema_version": 3,
                    "status": "selected_unit_verified",
                    "taint_reasons": [],
                    "elaboration_sandbox": "linux_bwrap",
                    "source_closure_sha256": closure_sha,
                    "specification_manifest_sha256": spec_sha,
                    "proof_manifest_sha256": proof_manifest,
                    "canonical_program_sha256": canon_prog_sha,
                    "scope": { "kind": "selected_unit", "roots": ["id"] },
                    "configuration": {
                        "target": "x86_64-unknown-linux-gnu",
                        "opt_level": 2,
                        "debug_assertions": false,
                        "overflow_checks": false,
                        "mir_preserve_ub": true,
                        "panic": "unwind",
                        "pointer_bits": 64,
                        "endian": "little",
                    },
                    "audit": {
                        "replay": true,
                        "exactType": true,
                        "canonicalRoot": "Trusted.MirSemantics.UnitTheorem",
                        "subject": "Captured.program",
                        "expected": "Expected.claim",
                        "theorem": "Proof.verify",
                        "specification": spec_name,
                        "specificationClosure": [{ "name": spec_name, "module": "Spec" }],
                        "axioms": ["propext"],
                    }
                }))
                .unwrap()
            };
        let receipt_json = build_receipt(
            &expected_spec_sha,
            &closure.source_closure_sha256,
            "Spec.specs",
            &proof_manifest_sha,
        );
        let receipt_sha = sha256_bytes(&receipt_json);
        fs::write(ev_dir.join("slices/core_linux_x86_64/01_id.receipt.v3.json"), &receipt_json)
            .unwrap();

        let ev_manifest = EvidenceBundleManifest {
            schema_version: 1,
            subject: EvidenceSubject {
                crate_name: pkg.name.clone(),
                crate_version: pkg.version.clone(),
                source_closure_sha256: closure.source_closure_sha256.clone(),
                specification_manifest_sha256: plane1.contract_manifest_sha256.clone(),
                anneal_toml_sha256: plane1.anneal_toml_sha256.clone(),
            },
            overlay: None,
            proof_units: BTreeMap::from([(
                "01_id".into(),
                EvidenceProofUnit {
                    theorem: "Proof.verify".into(),
                    shard_mode: "none".into(),
                    proof_sources: vec![EvidenceFileRecord {
                        module: "Proof".into(),
                        path: "proofs/01_id/Proof.lean".into(),
                        sha256: proof_sha,
                    }],
                    proof_library_deps: vec![],
                },
            )]),
            slices: BTreeMap::from([(
                "core_linux_x86_64".into(),
                EvidenceSlice {
                    semantic_profile: profile.clone(),
                    rustc_commit_sha: "f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1".into(),
                    lean_toolchain: "leanprover/lean4:v4.34.1".into(),
                    units: BTreeMap::from([(
                        "01_id".into(),
                        EvidenceSliceUnit {
                            canonical_program_sha256: canon_prog_sha.clone(),
                            receipt_path: "slices/core_linux_x86_64/01_id.receipt.v3.json".into(),
                            receipt_sha256: receipt_sha,
                            expected_cone_path: None,
                            expected_cone_sha256: None,
                            attestation_path: None,
                        },
                    )]),
                },
            )]),
        };
        fs::write(
            ev_dir.join("anneal-evidence.json"),
            serde_json::to_vec_pretty(&ev_manifest).unwrap(),
        )
        .unwrap();

        let (verified_ev, rep) = verify_evidence_carrier_dir(
            tmp.path(),
            &pkg,
            &closure,
            &plane1,
            &ev_dir,
            &EvidenceVerifyOptions { require_untainted: true, require_attestation: false },
        )
        .unwrap();
        assert_eq!(rep.verified_slice_receipt_count, 1);

        let (matched_slice, _) =
            match_consumer_slice(&verified_ev, "01_id", &canon_prog_sha, &profile).unwrap();
        assert_eq!(matched_slice, "core_linux_x86_64");

        // Mismatched MIR digest (e.g. from `#[cfg(not(feature = "derive"))]`)
        // must fail closed with `E_ANNEAL_SLICE_UNVERIFIED`.
        let miss =
            match_consumer_slice(&verified_ev, "01_id", &"0".repeat(64), &profile).unwrap_err();
        assert!(miss.message.contains("E_ANNEAL_SLICE_UNVERIFIED"), "{miss}");

        // Requiring attestation without `attestation_path` must fail closed.
        let att_err = verify_evidence_carrier_dir(
            tmp.path(),
            &pkg,
            &closure,
            &plane1,
            &ev_dir,
            &EvidenceVerifyOptions { require_untainted: true, require_attestation: true },
        )
        .unwrap_err();
        assert!(att_err.message.contains("E_ANNEAL_UNATTESTED_REMOTE_RECEIPT"), "{att_err}");

        // Swapped-spec or wrong-closure Receipt v3 must fail closed.
        for (label, tampered_bytes) in [
            (
                "wrong spec_manifest_sha256",
                build_receipt(
                    &"1".repeat(64),
                    &closure.source_closure_sha256,
                    "Spec.specs",
                    &proof_manifest_sha,
                ),
            ),
            (
                "wrong source_closure_sha256",
                build_receipt(
                    &expected_spec_sha,
                    &"2".repeat(64),
                    "Spec.specs",
                    &proof_manifest_sha,
                ),
            ),
            (
                "wrong audit specification",
                build_receipt(
                    &expected_spec_sha,
                    &closure.source_closure_sha256,
                    "Spec.weak",
                    &proof_manifest_sha,
                ),
            ),
            (
                "wrong proof_manifest_sha256",
                build_receipt(
                    &expected_spec_sha,
                    &closure.source_closure_sha256,
                    "Spec.specs",
                    &"3".repeat(64),
                ),
            ),
        ] {
            let mut bad_ev = ev_manifest.clone();
            let tampered_sha = sha256_bytes(&tampered_bytes);
            bad_ev.slices.get_mut("core_linux_x86_64").unwrap().units.get_mut("01_id").unwrap().receipt_sha256 = tampered_sha;
            fs::write(ev_dir.join("slices/core_linux_x86_64/01_id.receipt.v3.json"), &tampered_bytes).unwrap();
            fs::write(ev_dir.join("anneal-evidence.json"), serde_json::to_vec_pretty(&bad_ev).unwrap()).unwrap();
            let err = verify_evidence_carrier_dir(
                tmp.path(),
                &pkg,
                &closure,
                &plane1,
                &ev_dir,
                &EvidenceVerifyOptions { require_untainted: true, require_attestation: false },
            )
            .unwrap_err();
            assert!(!err.message.is_empty(), "{label} should fail");
        }
        fs::write(ev_dir.join("slices/core_linux_x86_64/01_id.receipt.v3.json"), &receipt_json)
            .unwrap();
        fs::write(
            ev_dir.join("anneal-evidence.json"),
            serde_json::to_vec_pretty(&ev_manifest).unwrap(),
        )
        .unwrap();

        let verify_ev = |manifest: &EvidenceBundleManifest, require_attestation: bool| {
            fs::write(
                ev_dir.join("anneal-evidence.json"),
                serde_json::to_vec_pretty(manifest).unwrap(),
            )
            .unwrap();
            verify_evidence_carrier_dir(
                tmp.path(),
                &pkg,
                &closure,
                &plane1,
                &ev_dir,
                &EvidenceVerifyOptions { require_untainted: true, require_attestation },
            )
        };

        // Slices recorded with a different compiler or Lean toolchain are not
        // evidence for this verifier.
        let mut other_rustc = ev_manifest.clone();
        other_rustc.slices.get_mut("core_linux_x86_64").unwrap().rustc_commit_sha = "0".repeat(40);
        let err = verify_ev(&other_rustc, false).unwrap_err();
        assert!(err.message.contains("rustc_commit_sha"), "{err}");
        let mut other_lean = ev_manifest.clone();
        other_lean.slices.get_mut("core_linux_x86_64").unwrap().lean_toolchain =
            "leanprover/lean4:v4.35.0".into();
        let err = verify_ev(&other_lean, false).unwrap_err();
        assert!(err.message.contains("lean_toolchain"), "{err}");

        // A receipt from an unpinned-Lean run behind a pinned slice header
        // fails closed even when tainted receipts are accepted.
        for unpinned_field in [false, true] {
            let mut unpinned: Value = serde_json::from_slice(&receipt_json).unwrap();
            unpinned["status"] = json!("tainted_selected_unit_verified");
            if unpinned_field {
                unpinned["unpinned_lean"] = json!({});
            } else {
                unpinned["taint_reasons"] = json!(["unpinned_lean"]);
            }
            let unpinned_bytes = serde_json::to_vec_pretty(&unpinned).unwrap();
            let receipt_path = ev_dir.join("slices/core_linux_x86_64/01_id.receipt.v3.json");
            fs::write(receipt_path, &unpinned_bytes).unwrap();
            let mut unpinned_ev = ev_manifest.clone();
            unpinned_ev
                .slices
                .get_mut("core_linux_x86_64")
                .unwrap()
                .units
                .get_mut("01_id")
                .unwrap()
                .receipt_sha256 = sha256_bytes(&unpinned_bytes);
            fs::write(
                ev_dir.join("anneal-evidence.json"),
                serde_json::to_vec_pretty(&unpinned_ev).unwrap(),
            )
            .unwrap();
            let err = verify_evidence_carrier_dir(
                tmp.path(),
                &pkg,
                &closure,
                &plane1,
                &ev_dir,
                &EvidenceVerifyOptions { require_untainted: false, require_attestation: false },
            )
            .unwrap_err();
            assert!(err.message.contains("unpinned Lean toolchain"), "{err}");
        }
        fs::write(ev_dir.join("slices/core_linux_x86_64/01_id.receipt.v3.json"), &receipt_json)
            .unwrap();

        // A structurally valid DSSE envelope is not authenticated, so a
        // required attestation still fails closed.
        fs::write(
            ev_dir.join("slices/core_linux_x86_64/01_id.intoto.json"),
            br#"{"payload":"e30=","payloadType":"application/vnd.in-toto+json","signatures":[{"sig":"AAAA"}]}"#,
        )
        .unwrap();
        let mut with_att = ev_manifest.clone();
        with_att
            .slices
            .get_mut("core_linux_x86_64")
            .unwrap()
            .units
            .get_mut("01_id")
            .unwrap()
            .attestation_path = Some("slices/core_linux_x86_64/01_id.intoto.json".into());
        let err = verify_ev(&with_att, true).unwrap_err();
        assert!(err.message.contains("DSSE signature verification is not implemented"), "{err}");
        // Without the requirement, an unused attestation does not block.
        verify_ev(&with_att, false).unwrap();

        // Replacing a shipped proof file and its index digest, while keeping a
        // receipt produced from the original proof, must fail closed.
        let swapped_bytes =
            b"prelude\nimport Expected\ntheorem verify : Expected.claim := by sorry\n";
        fs::write(ev_dir.join("proofs/01_id/Proof.lean"), swapped_bytes).unwrap();
        let mut swapped = ev_manifest.clone();
        swapped.proof_units.get_mut("01_id").unwrap().proof_sources[0].sha256 =
            sha256_bytes(swapped_bytes);
        let err = verify_ev(&swapped, false).unwrap_err();
        assert!(err.message.contains("proof_manifest_sha256"), "{err}");
        fs::write(ev_dir.join("proofs/01_id/Proof.lean"), proof_bytes).unwrap();
        verify_ev(&ev_manifest, false).unwrap();

        // Carrier `[target.*.dependencies]`, `lib.proc-macro`, and `build.rs`
        // must fail.
        fs::write(
            ev_dir.join("Cargo.toml"),
            "[package]\nname = \"demo-crate-anneal-proofs\"\nversion = \"0.1.0+demo-crate.0.8.64\"\n\
             [target.'cfg(unix)'.dependencies]\nlibc = \"0.2\"\n",
        )
        .unwrap();
        assert!(
            verify_evidence_carrier_dir(
                tmp.path(),
                &pkg,
                &closure,
                &plane1,
                &ev_dir,
                &EvidenceVerifyOptions::default(),
            )
            .is_err()
        );
        fs::remove_file(ev_dir.join("Cargo.toml")).unwrap();
        fs::write(ev_dir.join("build.rs"), "fn main() {}\n").unwrap();
        assert!(
            verify_evidence_carrier_dir(
                tmp.path(),
                &pkg,
                &closure,
                &plane1,
                &ev_dir,
                &EvidenceVerifyOptions::default(),
            )
            .is_err()
        );
        fs::remove_file(ev_dir.join("build.rs")).unwrap();

        // Forbidden `.olean` binary inside evidence carrier must fail closed.
        fs::write(ev_dir.join("proofs/01_id/Proof.olean"), b"olean").unwrap();
        let olean_err = verify_evidence_carrier_dir(
            tmp.path(),
            &pkg,
            &closure,
            &plane1,
            &ev_dir,
            &EvidenceVerifyOptions::default(),
        )
        .unwrap_err();
        assert!(olean_err.message.contains("E_ANNEAL_BINARY_OLEAN_FORBIDDEN"), "{olean_err}");
    }
}
