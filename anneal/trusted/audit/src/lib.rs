// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Repository trusted-boundary and `.olean` environment auditor for Anneal.
//!
//! This crate implements the CI repository gate that pairs with
//! `trusted/audit/TrustedBoundary.lean`. While `TrustedBoundary.lean` inspects
//! Lean syntax trees and compiled `.olean` kernel environments from inside
//! Lean, an inner Lean script cannot verify the host filesystem, Cargo
//! workspace manifests, Lean binary version admission, or the `--setup` flags
//! and environment variables used to invoke `lean` in the first place.
//!
//! Together, `trusted/audit` and `TrustedBoundary.lean` enforce five
//! repository-level invariants across a four-stage pipeline:
//!
//! 1. **Cargo DAG containment ([`check_cargo_boundary`]):** Because Rust code
//!    (including `build.rs` scripts and proc-macros) is effectful and not
//!    checked by the Lean kernel, every Cargo workspace member must reside
//!    under `trusted/` and no member may declare a `path` dependency outside
//!    `trusted/`.
//! 2. **Toolchain, source-tree, and foundation-lock admission
//!    ([`scan_lean_tree`], [`Checker::tool_admission`]):** Source directories
//!    (`trusted/lean/` and `theory/`) must contain only regular files and zero
//!    pre-existing `.olean`/`.ilean`/`.ir` artifacts (preventing pre-compiled
//!    `.olean` files from shadowing source compilation). The `lean` binary
//!    version and SHA-256 digest must match `trusted/lean/foundation-lock.json`
//!    (Lean v4.34.1), and every `Init.*` module's `.lean` source and
//!    `.olean`/`.ir` companion parts must match the lock's presence/absence
//!    specification, producing a verified [`AdmittedToolchain`].
//! 3. **Hermetic preflight and synchronous `--setup` compilation
//!    ([`Checker::new_with_env`], [`Checker::inspect`],
//!    [`Checker::compile_lean_module`]):** Ambient `LEAN_*`, `LAKE_*`,
//!    `ELAN_*`, and `LD_*`/`DYLD_*` variables are stripped. Before any `.lean`
//!    file is compiled, `TrustedBoundary.lean` runs in
//!    [`InspectorRequest::Preflight`] mode using only the locked `foundation`
//!    parser environment to reject forbidden syntax (`axiom`, `unsafe`,
//!    `partial`, `meta`, `native_decide`, `by_elab`, `#eval`, `set_option`,
//!    compiler-override attributes, etc.) and extract each `Trusted` module's
//!    typed [`TrustTier`] (`-- anneal-trust-tier:` directive). Admitted modules
//!    are then compiled in topological order via `lean --setup
//!    <module>.setup.json -DElab.async=false -Ddebug.skipKernelTC=false`,
//!    binding every import directly to its staged `.olean` path.
//! 4. **Module-level trust-tier separation and namespace hygiene
//!    ([`InspectorRequest::Audit`]):** Each `Trusted` module declares a single
//!    module-level [`TrustTier`] (`vetted` or `candidate:<feature>`), and every
//!    constant compiled into that module's `.olean` inherits its origin
//!    module's tier. Constants in `vetted` modules never reference constants in
//!    `candidate:<feature>` modules; `Trusted` modules never import or
//!    reference `theory/` (`Anneal.*`); and non-`Trusted` modules cannot
//!    declare constants in the `Trusted` namespace or `opaque` definitions.
//! 5. **Zero custom axioms and full kernel replay ([`Checker::run`]):** All
//!    non-foundation constants in `Trusted` and `Anneal` are checked against
//!    the foundation axiom allowlist in `foundation-lock.json` and replayed
//!    from scratch through `base.toKernelEnv.replay` with `loadExts := false`.

use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::io;
use std::path::{Component, Path, PathBuf};
use std::process::Command;

use serde::{Deserialize, Serialize};
use serde_json::json;
use sha2::{Digest, Sha256};
use walkdir::WalkDir;

/// JSON value representation used at the `TrustedBoundary.lean` IPC boundary.
pub type Json = serde_json::Value;

/// Pinned Lean 4 toolchain identifier required by `foundation-lock.json`.
pub const TOOLCHAIN: &str = "leanprover/lean4:v4.34.1";

/// `.olean` artifact companion suffixes passed in the first array of
/// `Lean.ImportArtifacts`.
pub const OLEAN_PARTS: [&str; 3] = ["olean", "olean.server", "olean.private"];

/// `.ir` artifact companion suffixes passed in the second array of
/// `Lean.ImportArtifacts`.
pub const IR_PARTS: [&str; 2] = ["ir.sig", "ir"];

/// All five compiled Lean artifact companion suffixes tracked by
/// `foundation-lock.json` and module compilation.
pub const PARTS: [&str; 5] = [
    "olean",
    "olean.server",
    "olean.private",
    "ir.sig",
    "ir",
];

// ---------------------------------------------------------------------------
// Domain types
// ---------------------------------------------------------------------------

/// Structured audit failure distinguishing policy rejections (`code == 1`)
/// from operational or environment failures (`code == 2`).
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("{message}")]
pub struct Failure {
    /// Process exit code (`1` for policy rejection, `2` for operational error).
    pub code: i32,
    /// Audit phase in which the failure occurred.
    pub phase: String,
    /// Human-readable diagnostic message.
    pub message: String,
}

impl Failure {
    /// Construct a new [`Failure`].
    pub fn new(
        code: i32,
        phase: impl Into<String>,
        message: impl Into<String>,
    ) -> Self {
        Self {
            code,
            phase: phase.into(),
            message: message.into(),
        }
    }

    /// Construct a TCB policy-rejection [`Failure`] (`code == 1`).
    pub fn policy(
        phase: impl Into<String>,
        message: impl Into<String>,
    ) -> Self {
        Self::new(1, phase, message)
    }

    /// Construct an operational or environment [`Failure`] (`code == 2`).
    pub fn operational(
        phase: impl Into<String>,
        message: impl Into<String>,
    ) -> Self {
        Self::new(2, phase, message)
    }
}

/// Subsystem candidate-trusted feature identifiers recognized by Anneal.
///
/// Must stay in sync with `TrustedBoundary.validCandidateFeatures` in
/// `trusted/audit/TrustedBoundary.lean`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum CandidateFeature {
    Refinement,
    StepResult,
    Memory,
    MirAst,
    MirSemantics,
    RustcCapture,
}

impl CandidateFeature {
    /// Parse a candidate feature identifier string.
    pub fn parse(raw: &str) -> Option<Self> {
        match raw {
            "refinement" => Some(Self::Refinement),
            "step_result" => Some(Self::StepResult),
            "memory" => Some(Self::Memory),
            "mir_ast" => Some(Self::MirAst),
            "mir_semantics" => Some(Self::MirSemantics),
            "rustc_capture" => Some(Self::RustcCapture),
            _ => None,
        }
    }

    /// Return the canonical identifier string for this candidate feature.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Refinement => "refinement",
            Self::StepResult => "step_result",
            Self::Memory => "memory",
            Self::MirAst => "mir_ast",
            Self::MirSemantics => "mir_semantics",
            Self::RustcCapture => "rustc_capture",
        }
    }
}

/// Module-level trust tier declared by a `Trusted` module via
/// `-- anneal-trust-tier: <tier>`.
///
/// Making `TrustTier` a sum type over [`CandidateFeature`] ensures that an
/// invalid or misspelled tier cannot be represented.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TrustTier {
    /// Human-audited, permanently trusted TCB module (`vetted`).
    Vetted,
    /// Alpha TCB module gated behind an explicit candidate feature opt-in
    /// (`candidate:<feature>`).
    Candidate(CandidateFeature),
}

impl TrustTier {
    /// Parse `"vetted"` or `"candidate:<feature>"`.
    pub fn parse(raw: &str) -> Option<Self> {
        if raw == "vetted" {
            Some(Self::Vetted)
        } else {
            let feat = raw.strip_prefix("candidate:")?;
            Some(Self::Candidate(CandidateFeature::parse(feat)?))
        }
    }

    /// Render the canonical wire string (`"vetted"` or
    /// `"candidate:<feature>"`).
    pub fn render(self) -> String {
        match self {
            Self::Vetted => "vetted".to_string(),
            Self::Candidate(f) => format!("candidate:{}", f.as_str()),
        }
    }
}

/// Validated artifact companion paths for a single compiled Lean module.
///
/// `Lean.ImportArtifacts` expects two path arrays per module:
/// 1. `olean_parts`: `[.olean, .olean.server?, .olean.private?]` (always
///    non-empty; `.olean` is mandatory).
/// 2. `ir_parts`: `[.ir.sig?, .ir?]`.
///
/// Representing these two groups as named fields rather than `Vec<Vec<String>>`
/// makes malformed artifact-group counts unrepresentable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleArtifacts {
    /// Non-empty `.olean` companion group (`OLEAN_PARTS`).
    pub olean_parts: Vec<String>,
    /// Optional `.ir` companion group (`IR_PARTS`).
    pub ir_parts: Vec<String>,
}

impl ModuleArtifacts {
    /// Construct [`ModuleArtifacts`] from a map of available part suffixes
    /// (`"olean"` -> path, etc.), failing if the primary `"olean"` part is
    /// absent.
    pub fn from_available(
        available: &BTreeMap<&str, String>,
        phase: &str,
        err_msg: impl FnOnce() -> String,
    ) -> Result<Self, Failure> {
        if !available.contains_key("olean") {
            return Err(Failure::new(2, phase, err_msg()));
        }
        let olean_parts = OLEAN_PARTS
            .iter()
            .filter_map(|p| available.get(*p).cloned())
            .collect();
        let ir_parts = IR_PARTS
            .iter()
            .filter_map(|p| available.get(*p).cloned())
            .collect();
        Ok(Self {
            olean_parts,
            ir_parts,
        })
    }

    /// Convert to the two-element array representation expected by
    /// `Lean.ImportArtifacts` in `--setup` and `TrustedBoundary.lean`.
    pub fn to_wire(&self) -> [&[String]; 2] {
        [&self.olean_parts, &self.ir_parts]
    }
}

/// A single `import` edge in a Lean module header, matching Lean's `Import`
/// JSON encoding (`Lean.Import`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
pub struct ImportEdge {
    /// Imported module name (e.g. `"Init.Core"` or `"Trusted.MirAst"`).
    pub module: String,
    /// Whether `import all` was used (always `false` in admitted modules).
    pub import_all: bool,
    /// Whether the import is exported (`true` for standard `import`).
    pub is_exported: bool,
    /// Whether `meta import` was used (always `false` in admitted modules).
    pub is_meta: bool,
}

/// Typed request sent to `TrustedBoundary.lean`.
///
/// Encoding the two inspector phases as a sum type ensures that `"preflight"`
/// is always invoked with a source list against the foundation graph, and
/// `"audit"` is always invoked with the full module inventory and validated
/// [`TrustTier`] map.
#[derive(Debug, Clone)]
pub enum InspectorRequest {
    /// Phase 1 (`"preflight"`): parse `(module_name, staged_path)` pairs
    /// against the locked foundation parser environment before any elaboration.
    Preflight {
        sources: Vec<(String, PathBuf)>,
    },
    /// Phase 2 (`"audit"`): load compiled `.olean`s with `loadExts := false`,
    /// verify module-level trust tiers and namespace hygiene, and replay all
    /// non-foundation constants through the Lean kernel.
    Audit {
        trusted: Vec<String>,
        theory: Vec<String>,
        module_tiers: BTreeMap<String, TrustTier>,
    },
}

impl InspectorRequest {
    /// Return the wire mode tag (`"preflight"` or `"audit"`).
    pub const fn mode(&self) -> &'static str {
        match self {
            Self::Preflight { .. } => "preflight",
            Self::Audit { .. } => "audit",
        }
    }
}

// ---------------------------------------------------------------------------
// File, digest, and identifier predicates
// ---------------------------------------------------------------------------

/// Verify that `path` exists and is a regular file (not a symlink, directory,
/// FIFO, or device node) using `symlink_metadata` so symlinks are never
/// silently followed.
pub fn regular(path: &Path, phase: &str) -> Result<(), Failure> {
    let meta = fs::symlink_metadata(path).map_err(|e| {
        Failure::new(
            2,
            phase,
            format!("cannot inspect {}: {e}", path.display()),
        )
    })?;
    if meta.file_type().is_symlink() || !meta.file_type().is_file() {
        return Err(Failure::new(
            1,
            phase,
            format!("expected a regular file: {}", path.display()),
        ));
    }
    Ok(())
}

/// Compute the lowercase hex-encoded FIPS 180-4 SHA-256 digest of `data`.
pub fn sha256_bytes(data: &[u8]) -> String {
    format!("{:x}", Sha256::digest(data))
}

/// Verify that `path` is a regular file and return its lowercase hex SHA-256
/// digest.
pub fn sha256_file(path: &Path, phase: &str) -> Result<String, Failure> {
    regular(path, phase)?;
    let bytes = fs::read(path).map_err(|e| {
        Failure::new(
            2,
            phase,
            format!("cannot read {}: {e}", path.display()),
        )
    })?;
    Ok(sha256_bytes(&bytes))
}

/// Copy a regular source file `src` to `dst`, creating parent directories as
/// needed, and return the SHA-256 digest of the copied bytes.
fn stage_regular_file(
    src: &Path,
    dst: &Path,
    phase: &str,
) -> Result<String, Failure> {
    regular(src, phase)?;
    let bytes = fs::read(src).map_err(|e| {
        Failure::new(
            2,
            phase,
            format!("cannot read {}: {e}", src.display()),
        )
    })?;
    if let Some(parent) = dst.parent() {
        fs::create_dir_all(parent).map_err(|e| {
            Failure::new(
                2,
                phase,
                format!("cannot create {}: {e}", parent.display()),
            )
        })?;
    }
    fs::write(dst, &bytes).map_err(|e| {
        Failure::new(
            2,
            phase,
            format!("cannot write {}: {e}", dst.display()),
        )
    })?;
    Ok(sha256_bytes(&bytes))
}

/// Return `true` if `s` is a 64-character ASCII hex digest.
fn is_sha256_hex(s: &str) -> bool {
    s.len() == 64 && s.bytes().all(|b| b.is_ascii_hexdigit())
}

/// Return `true` if `s` is a valid ASCII Lean module identifier component.
fn is_lean_ident(s: &str) -> bool {
    let mut chars = s.chars();
    chars
        .next()
        .is_some_and(|first| first.is_ascii_alphabetic())
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// Return `true` if `rel` consists exclusively of normal path components (no
/// `/`, `.`, or `..`).
fn is_clean_relative_path(rel: &str) -> bool {
    let mut comps = Path::new(rel).components();
    comps.clone().next().is_some()
        && comps.all(|c| matches!(c, Component::Normal(_)))
}

// ---------------------------------------------------------------------------
// Stage 1: Cargo workspace and root TCB manifest boundary
// ---------------------------------------------------------------------------

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
    fn all_targets(
        &self,
    ) -> impl Iterator<Item = (&'static str, &MemberTarget)> {
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
            ("dev_dependencies", self.dev_dependencies_underscore.as_ref()),
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
fn reject_cargo_toolchain_overrides(checkout: &Path) -> Result<(), Failure> {
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
                format!(
                    "forbidden Cargo/toolchain override at repository root: {forbidden}"
                ),
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
    let manifest_text = fs::read_to_string(&manifest_path).map_err(|e| {
        Failure::new(
            1,
            phase,
            format!("cannot read root-manifest.sha256: {e}"),
        )
    })?;
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
                format!(
                    "invalid or duplicate entry in root-manifest.sha256: {line}"
                ),
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
    for required_rel in ["Cargo.toml", "Cargo.lock", "flake.nix", "flake.lock"]
    {
        if !seen_paths.contains(required_rel) {
            return Err(Failure::new(
                1,
                phase,
                format!(
                    "root-manifest.sha256 missing required entry: {required_rel}"
                ),
            ));
        }
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
    if path.is_absolute()
        || path.components().any(|c| matches!(c, Component::ParentDir))
    {
        return Err(Failure::new(
            1,
            "cargo-boundary",
            format!(
                "{member} target {section}.path escapes member directory: {p}"
            ),
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
                format!(
                    "non-string path dependency {dep_name} in {member}/Cargo.toml"
                ),
            ));
        };
        let resolved =
            fs::canonicalize(member_parent.join(dep_path)).map_err(|_| {
                Failure::new(
                    1,
                    phase,
                    format!(
                        "{member} path dependency target does not exist: {dep_path}"
                    ),
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
                format!(
                    "{member} path dependency points outside trusted/: {rel_str}"
                ),
            ));
        }
        if !member_set.contains(&rel_str) {
            return Err(Failure::new(
                1,
                phase,
                format!(
                    "{member} path dependency points to non-member crate: {rel_str}"
                ),
            ));
        }
        regular(&resolved.join("Cargo.toml"), phase)?;
    }
    Ok(())
}

/// Validate `Cargo.lock` (when present): version 4, every external dependency
/// sourced from `crates.io-index` with a 64-hex SHA-256 checksum, and every
/// source-less package belonging to `member_pkg_names`.
fn verify_cargo_lock(
    checkout: &Path,
    member_pkg_names: &BTreeSet<String>,
) -> Result<(), Failure> {
    let phase = "cargo-boundary";
    let lock_path = checkout.join("Cargo.lock");
    if fs::symlink_metadata(&lock_path).is_err() {
        return Ok(());
    }
    regular(&lock_path, phase)?;
    let lock_text = fs::read_to_string(&lock_path).map_err(|e| {
        Failure::new(1, phase, format!("cannot read Cargo.lock: {e}"))
    })?;
    let lock_file: CargoLockFile = toml::from_str(&lock_text).map_err(|e| {
        Failure::new(1, phase, format!("malformed Cargo.lock: {e}"))
    })?;
    if lock_file.version != Some(4) {
        return Err(Failure::new(
            1,
            phase,
            "Cargo.lock must have version = 4",
        ));
    }
    for pkg in &lock_file.package {
        let pkg_name = pkg.name.as_str();
        match pkg.source.as_deref() {
            Some("registry+https://github.com/rust-lang/crates.io-index") => {
                if !pkg.checksum.as_deref().is_some_and(is_sha256_hex) {
                    return Err(Failure::new(
                        1,
                        phase,
                        format!(
                            "missing or invalid checksum in Cargo.lock for {pkg_name}"
                        ),
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
                if pkg.checksum.is_some() || !member_pkg_names.contains(pkg_name)
                {
                    return Err(Failure::new(
                        1,
                        phase,
                        format!(
                            "untrusted local package without source in Cargo.lock: {pkg_name}"
                        ),
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
pub fn check_cargo_boundary(checkout: &Path) -> Result<(), Failure> {
    let phase = "cargo-boundary";
    reject_cargo_toolchain_overrides(checkout)?;
    let root_toml_path = checkout.join("Cargo.toml");
    let capture_toml_path = checkout.join("trusted/rustc-capture/Cargo.toml");
    regular(&root_toml_path, phase)?;
    regular(&capture_toml_path, phase)?;
    verify_root_manifest_sha256(checkout)?;

    let root_text = fs::read_to_string(&root_toml_path).map_err(|e| {
        Failure::new(1, phase, format!("malformed Cargo manifest: {e}"))
    })?;
    let root_manifest: RootCargoManifest =
        toml::from_str(&root_text).map_err(|e| {
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

    let checkout_canon = fs::canonicalize(checkout).map_err(|e| {
        Failure::new(2, phase, format!("cannot canonicalize checkout: {e}"))
    })?;

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
        let manifest: MemberCargoManifest =
            toml::from_str(&member_text).map_err(|e| {
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
            .ok_or_else(|| {
                Failure::new(
                    1,
                    phase,
                    format!("missing package.name in {member}"),
                )
            })?;
        member_pkg_names.insert(pkg_name.to_string());

        if manifest.package.build.is_some()
            || manifest.package.workspace.is_some()
        {
            return Err(Failure::new(
                1,
                phase,
                format!(
                    "disallowed package.build or package.workspace in {member}/Cargo.toml"
                ),
            ));
        }
        if fs::symlink_metadata(checkout.join(member).join("build.rs")).is_ok()
        {
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

    verify_cargo_lock(checkout, &member_pkg_names)
}

/// Reject `.cargo*` and `rust-toolchain*` overrides at `checkout`, and run
/// [`check_cargo_boundary`] whenever any Cargo or root-manifest TCB file is
/// present.
fn check_checkout_cargo_hygiene(checkout: &Path) -> Result<(), Failure> {
    reject_cargo_toolchain_overrides(checkout)?;
    if [
        "Cargo.toml",
        "Cargo.lock",
        "trusted/root-manifest.sha256",
        "trusted/rustc-capture",
    ]
    .iter()
    .any(|rel| fs::symlink_metadata(checkout.join(rel)).is_ok())
    {
        check_cargo_boundary(checkout)?;
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Stage 2: Source tree scanning & Lean toolchain admission
// ---------------------------------------------------------------------------

/// Scan a Lean directory tree (`trusted/lean` with `"Trusted"` or `theory`
/// with `"Anneal"`), rejecting symlinks, non-`.lean` files, and compiled
/// artifacts in the source tree and returning the map from dot-separated module
/// name to `.lean` path.
pub fn scan_lean_tree(
    root: &Path,
    umbrella_prefix: &str,
) -> Result<BTreeMap<String, PathBuf>, Failure> {
    let meta = fs::symlink_metadata(root).map_err(|_| {
        Failure::new(
            1,
            "snapshot",
            format!("expected regular source directory: {}", root.display()),
        )
    })?;
    if meta.file_type().is_symlink() || !meta.file_type().is_dir() {
        return Err(Failure::new(
            1,
            "snapshot",
            format!("expected regular source directory: {}", root.display()),
        ));
    }

    let mut modules = BTreeMap::new();
    for entry in WalkDir::new(root)
        .follow_links(false)
        .sort_by_file_name()
        .into_iter()
        .skip(1)
    {
        let entry = entry.map_err(|e| {
            Failure::new(
                2,
                "snapshot",
                format!("cannot read {}: {e}", root.display()),
            )
        })?;
        let path = entry.path().to_path_buf();
        if entry.file_type().is_symlink() {
            return Err(Failure::new(
                1,
                "snapshot",
                format!("unexpected symlink in source tree: {}", path.display()),
            ));
        }
        if entry.file_type().is_dir() {
            continue;
        }
        regular(&path, "snapshot")?;

        let rel_path = path.strip_prefix(root).unwrap();
        let relative = rel_path.to_string_lossy().replace('\\', "/");
        if PARTS
            .iter()
            .any(|part| relative.ends_with(&format!(".{part}")))
            || relative.ends_with(".ilean")
        {
            return Err(Failure::new(
                1,
                "snapshot",
                format!("compiled artifact in source root: {relative}"),
            ));
        }

        if let Some(stem) = relative.strip_suffix(".lean") {
            let components: Vec<&str> = stem.split('/').collect();
            if components.first().copied() != Some(umbrella_prefix)
                || !components.iter().copied().all(is_lean_ident)
            {
                return Err(Failure::new(
                    1,
                    "snapshot",
                    format!("unmappable Lean source: {relative}"),
                ));
            }
            let module = components.join(".");
            if modules.insert(module.clone(), path).is_some() {
                return Err(Failure::new(
                    1,
                    "snapshot",
                    format!("duplicate module: {module}"),
                ));
            }
        } else if !(umbrella_prefix == "Trusted"
            && (relative == "lean-toolchain"
                || relative == "foundation-lock.json"))
        {
            return Err(Failure::new(
                1,
                "snapshot",
                format!("unexpected non-Lean file in source tree: {relative}"),
            ));
        }
    }

    if (umbrella_prefix == "Trusted" || !modules.is_empty())
        && !modules.contains_key(umbrella_prefix)
    {
        return Err(Failure::new(
            1,
            "snapshot",
            format!("missing {umbrella_prefix}.lean umbrella"),
        ));
    }
    Ok(modules)
}

/// Pinned SHA-256 digests of the official Lean 4.34.1 `bin/lean` binaries from
/// `trusted/lean/foundation-lock.json`.
const LOCKED_LEAN_SHA256: [&str; 4] = [
    "79fb1d26fa5a39385d59fdc48a711a14b0710ca6480271acce99b4d177cea085",
    "1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554",
    "998f0cc2a5a754cc66df1f33b85e1447528737ff15012db35d8c501754b02f1e",
    "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550",
];

/// Resolve the default pinned Lean 4.34.1 binary path when none is explicitly
/// provided, selecting a candidate binary whose SHA-256 matches
/// `LOCKED_LEAN_SHA256`.
pub fn default_lean_path() -> PathBuf {
    let home = dirs::home_dir().unwrap_or_else(|| PathBuf::from("/root"));
    let mut candidate_paths = Vec::new();
    for base in dirs::cache_dir()
        .into_iter()
        .chain(std::iter::once(home.clone()))
    {
        let tc_base = base.join(".anneal/toolchain");
        if let Ok(entries) = fs::read_dir(&tc_base) {
            let mut dirs: Vec<(std::time::SystemTime, PathBuf)> = entries
                .filter_map(Result::ok)
                .map(|e| e.path().join("lean/bin/lean"))
                .filter(|p| p.is_file())
                .map(|p| {
                    let mtime = fs::metadata(&p)
                        .and_then(|m| m.modified())
                        .unwrap_or(std::time::UNIX_EPOCH);
                    (mtime, p)
                })
                .collect();
            dirs.sort_by(|a, b| b.0.cmp(&a.0));
            candidate_paths.extend(dirs.into_iter().map(|(_, p)| p));
        }
    }
    let elan_lean =
        home.join(".elan/toolchains/leanprover--lean4---v4.34.1/bin/lean");
    if elan_lean.is_file() {
        candidate_paths.push(elan_lean.clone());
    }
    for cand in &candidate_paths {
        if let Ok(digest) = sha256_file(cand, "toolchain")
            && LOCKED_LEAN_SHA256.contains(&digest.as_str())
        {
            return cand.clone();
        }
    }
    candidate_paths.into_iter().next().unwrap_or(elan_lean)
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct FoundationModuleRecord {
    #[serde(rename = "sourceSha256")]
    source_sha256: String,
    parts: BTreeMap<String, Option<String>>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
struct FoundationLock {
    schema: i64,
    toolchain: String,
    distributions: BTreeMap<String, String>,
    modules: BTreeMap<String, FoundationModuleRecord>,
    graph: BTreeMap<String, Vec<ImportEdge>>,
    axioms: Vec<(String, String)>,
}

/// Verified toolchain, `foundation-lock.json` metadata, and staged source state
/// produced by [`Checker::tool_admission`].
///
/// Grouping all post-admission state into [`AdmittedToolchain`] ensures that
/// [`Checker`] never carries uninitialized placeholder paths or empty lock
/// structures prior to admission.
#[derive(Debug, Clone)]
pub struct AdmittedToolchain {
    /// Staged path of `TrustedBoundary.lean`.
    pub inspector: PathBuf,
    /// Verified `lean --version` string matching `foundation-lock.json`.
    pub version: String,
    /// Canonical `lean --print-prefix` sysroot directory.
    pub prefix: PathBuf,
    /// Allowed foundation `(axiom_name, defining_module)` pairs from
    /// `foundation-lock.json`.
    pub axioms: Vec<(String, String)>,
    /// Locked `Init.*` foundation module import graph from
    /// `foundation-lock.json`. Its sorted keys are the admitted foundation
    /// module names.
    pub foundation_graph: BTreeMap<String, Vec<ImportEdge>>,
    /// Active module import graph (initially `foundation_graph`, extended with
    /// each `Trusted` and `Anneal` module as it is compiled).
    pub graph: BTreeMap<String, Vec<ImportEdge>>,
    /// Validated `.olean` and `.ir` artifact paths for each admitted module.
    pub artifacts: BTreeMap<String, ModuleArtifacts>,
    /// Staged `Trusted.*` source files (`module_name -> staged_path`).
    pub modules: BTreeMap<String, PathBuf>,
    /// Staged `Anneal.*` (`theory/`) source files
    /// (`module_name -> staged_path`).
    pub theory_modules: BTreeMap<String, PathBuf>,
}

impl AdmittedToolchain {
    /// Return the sorted list of locked `Init.*` foundation module names.
    pub fn foundation_modules(&self) -> Vec<&str> {
        self.foundation_graph.keys().map(String::as_str).collect()
    }
}

/// Validated repository source headers and module-level trust tiers produced by
/// [`Checker::preflight_repo_modules`].
#[derive(Debug, Clone)]
struct PreflightAdmission {
    /// Direct `import` edges for every staged `Trusted.*` and `Anneal.*`
    /// module.
    imports: BTreeMap<String, Vec<ImportEdge>>,
    /// Validated [`TrustTier`] for every staged `Trusted.*` module.
    module_tiers: BTreeMap<String, TrustTier>,
}

/// Repository-boundary auditor managing an isolated staging directory
/// (`stage`, owned by `_stage_dir`) and sanitized child environment.
pub struct Checker {
    _stage_dir: tempfile::TempDir,
    pub checkout: PathBuf,
    pub source: PathBuf,
    pub lean: PathBuf,
    pub stage: PathBuf,
    pub execution_began: bool,
    pub environment: BTreeMap<String, String>,
    counter: usize,
    pub admitted: Option<AdmittedToolchain>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct InspectorErrResponse {
    ok: bool,
    category: String,
    message: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct InspectorOkResponse {
    ok: bool,
    result: serde_json::Map<String, Json>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct PreflightHeader {
    module: String,
    imports: Vec<ImportEdge>,
    #[serde(default)]
    trust_tier: Option<String>,
}

#[derive(Deserialize)]
struct PreflightResult {
    headers: Vec<PreflightHeader>,
}

impl Checker {
    /// Create a new [`Checker`] with a fresh private staging directory.
    pub fn new(checkout: &Path, lean: Option<&Path>) -> io::Result<Self> {
        Self::new_with_env(checkout, lean, env::vars())
    }

    /// Create a new [`Checker`] using a closed environment allowlist.
    ///
    /// Retains only `HOME`, `TMPDIR`, `LANG`, and `LC_ALL` from `ambient_env`
    /// and pins `PATH` to `/usr/bin:/bin` so ambient search paths (`LEAN_PATH`,
    /// `LEAN_SRC_PATH`), toolchain overrides (`ELAN_TOOLCHAIN`), or dynamic
    /// linker preloading (`LD_PRELOAD`, `LD_LIBRARY_PATH`,
    /// `DYLD_INSERT_LIBRARIES`) cannot influence child `lean` invocations.
    pub fn new_with_env<I>(
        checkout: &Path,
        lean: Option<&Path>,
        ambient_env: I,
    ) -> io::Result<Self>
    where
        I: IntoIterator<Item = (String, String)>,
    {
        let checkout = fs::canonicalize(checkout)?;
        let source = checkout.join("trusted/lean");
        let lean_raw = match lean {
            Some(p) => p.to_path_buf(),
            None => default_lean_path(),
        };
        let lean = if lean_raw.is_absolute() {
            lean_raw
        } else {
            env::current_dir()?.join(lean_raw)
        };
        let stage_dir = tempfile::Builder::new()
            .prefix("anneal-trusted-")
            .tempdir()?;
        let stage = stage_dir.path().to_path_buf();

        let mut environment: BTreeMap<String, String> = ambient_env
            .into_iter()
            .filter(|(k, _)| {
                matches!(k.as_str(), "HOME" | "TMPDIR" | "LANG" | "LC_ALL")
            })
            .collect();
        environment.insert("PATH".to_string(), "/usr/bin:/bin".to_string());

        Ok(Self {
            _stage_dir: stage_dir,
            checkout,
            source,
            lean,
            stage,
            execution_began: false,
            environment,
            counter: 0,
            admitted: None,
        })
    }

    /// Return a shared reference to the [`AdmittedToolchain`], or an
    /// operational [`Failure`] if [`Checker::tool_admission`] has not run.
    pub fn admitted(&self) -> Result<&AdmittedToolchain, Failure> {
        self.admitted.as_ref().ok_or_else(|| {
            Failure::new(
                2,
                "admission",
                "tool_admission must succeed before inspecting or compiling modules",
            )
        })
    }

    /// Return a mutable reference to the [`AdmittedToolchain`], or an
    /// operational [`Failure`] if [`Checker::tool_admission`] has not run.
    pub fn admitted_mut(&mut self) -> Result<&mut AdmittedToolchain, Failure> {
        self.admitted.as_mut().ok_or_else(|| {
            Failure::new(
                2,
                "admission",
                "tool_admission must succeed before inspecting or compiling modules",
            )
        })
    }

    /// Execute `self.lean` with `arguments` in the sanitized `self.environment`
    /// with `self.stage` as the working directory.
    pub fn process(
        &mut self,
        label: &str,
        arguments: &[String],
    ) -> Result<String, Failure> {
        self.counter += 1;
        let output = Command::new(&self.lean)
            .args(arguments)
            .current_dir(&self.stage)
            .env_clear()
            .envs(&self.environment)
            .output()
            .map_err(|e| {
                Failure::new(2, label, format!("could not execute Lean: {e}"))
            })?;
        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            let stdout = String::from_utf8_lossy(&output.stdout);
            let detail = if stderr.trim().is_empty() {
                stdout.trim()
            } else {
                stderr.trim()
            };
            return Err(Failure::new(
                2,
                label,
                format!("Lean exited {:?}: {detail}", output.status.code()),
            ));
        }
        String::from_utf8(output.stdout).map_err(|e| {
            Failure::new(2, label, format!("invalid UTF-8 from Lean: {e}"))
        })
    }

    /// Write a `<module>.setup.json` descriptor for `lean --setup`.
    pub fn write_setup_json(
        &self,
        module: &str,
        imports: &[ImportEdge],
    ) -> Result<PathBuf, Failure> {
        let adm = self.admitted()?;
        let import_arts: BTreeMap<&str, [&[String]; 2]> = adm
            .artifacts
            .iter()
            .map(|(k, v)| (k.as_str(), v.to_wire()))
            .collect();
        let setup_obj = json!({
            "name": module,
            "isModule": false,
            "imports": imports,
            "importArts": import_arts,
            "dynlibs": [],
            "plugins": [],
            "options": {},
        });
        let setup_path = self.stage.join(format!("{module}.setup.json"));
        let bytes = serde_json::to_vec(&setup_obj)
            .map_err(|e| Failure::new(2, "setup", e.to_string()))?;
        fs::write(&setup_path, bytes)
            .map_err(|e| Failure::new(2, "setup", e.to_string()))?;
        Ok(setup_path)
    }

    /// Invoke `TrustedBoundary.lean` with a typed [`InspectorRequest`] and
    /// validate the structured response envelope.
    pub fn inspect(
        &mut self,
        request: InspectorRequest,
    ) -> Result<Json, Failure> {
        let mode = request.mode();
        let adm = self.admitted()?;
        let arts_arr: Vec<Json> = adm
            .artifacts
            .iter()
            .map(|(k, parts)| json!([k, parts.to_wire()]))
            .collect();
        let foundation = adm.foundation_modules();
        let req = match &request {
            InspectorRequest::Preflight { sources } => {
                let src_pairs: Vec<(&str, std::borrow::Cow<'_, str>)> = sources
                    .iter()
                    .map(|(m, p)| (m.as_str(), p.to_string_lossy()))
                    .collect();
                json!({
                    "mode": "preflight",
                    "sysroot": adm.prefix.to_string_lossy(),
                    "artifacts": arts_arr,
                    "foundation": foundation,
                    "graph": &adm.foundation_graph,
                    "axioms": &adm.axioms,
                    "sources": src_pairs,
                })
            }
            InspectorRequest::Audit {
                trusted,
                theory,
                module_tiers,
            } => {
                let tiers: Vec<(&str, String)> = module_tiers
                    .iter()
                    .map(|(m, t)| (m.as_str(), t.render()))
                    .collect();
                json!({
                    "mode": "audit",
                    "sysroot": adm.prefix.to_string_lossy(),
                    "artifacts": arts_arr,
                    "foundation": foundation,
                    "graph": &adm.graph,
                    "axioms": &adm.axioms,
                    "trusted": trusted,
                    "theory": theory,
                    "moduleTiers": tiers,
                })
            }
        };
        let inspector = adm.inspector.clone();

        self.counter += 1;
        let stem = self
            .stage
            .join(format!("request-{:03}-{mode}", self.counter));
        let request_path = PathBuf::from(format!("{}.json", stem.display()));
        let result_path =
            PathBuf::from(format!("{}.result.json", stem.display()));
        let req_bytes = serde_json::to_vec(&req).map_err(|e| {
            Failure::new(2, mode, format!("cannot serialize request: {e}"))
        })?;
        fs::write(&request_path, req_bytes).map_err(|e| {
            Failure::new(2, mode, format!("cannot write request: {e}"))
        })?;

        let args = vec![
            "-j1".to_string(),
            "-M2048".to_string(),
            "--run".to_string(),
            inspector.to_string_lossy().into_owned(),
            request_path.to_string_lossy().into_owned(),
            result_path.to_string_lossy().into_owned(),
        ];
        let output = Command::new(&self.lean)
            .args(&args)
            .current_dir(&self.stage)
            .env_clear()
            .envs(&self.environment)
            .output()
            .map_err(|e| {
                Failure::new(2, mode, format!("could not execute Lean: {e}"))
            })?;

        if !output.status.success() {
            if output.status.code() == Some(1)
                && result_path.is_file()
                && let Ok(text) = fs::read_to_string(&result_path)
                && let Ok(resp) =
                    serde_json::from_str::<InspectorErrResponse>(&text)
                && !resp.ok
                && resp.category == "policy"
                && resp.message.starts_with("policy:")
            {
                return Err(Failure::new(1, mode, resp.message));
            }
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(Failure::new(
                2,
                mode,
                format!(
                    "Lean exited {:?}: {}",
                    output.status.code(),
                    stderr.trim()
                ),
            ));
        }

        let resp_text = fs::read_to_string(&result_path).map_err(|e| {
            Failure::new(
                2,
                mode,
                format!("missing/malformed inspector result: {e}"),
            )
        })?;
        let resp: InspectorOkResponse =
            serde_json::from_str(&resp_text).map_err(|_| {
                Failure::new(2, mode, "unexpected inspector protocol response")
            })?;
        if !resp.ok {
            return Err(Failure::new(
                2,
                mode,
                "unexpected inspector protocol response",
            ));
        }
        Ok(Json::Object(resp.result))
    }

    /// Scan `root` via [`scan_lean_tree`] and copy every discovered `.lean`
    /// file into `self.stage.join(stage_subdir)`.
    fn scan_and_stage_tree(
        &self,
        root: &Path,
        umbrella_prefix: &str,
        stage_subdir: &str,
    ) -> Result<BTreeMap<String, PathBuf>, Failure> {
        scan_lean_tree(root, umbrella_prefix)?
            .into_iter()
            .map(|(mod_name, raw_path)| {
                let staged_path = self
                    .stage
                    .join(stage_subdir)
                    .join(format!("{}.lean", mod_name.replace('.', "/")));
                stage_regular_file(&raw_path, &staged_path, "snapshot")?;
                Ok((mod_name, staged_path))
            })
            .collect()
    }

    /// Wipe and recreate `self.stage` and clear any prior admission state.
    fn reset_stage(&mut self) -> Result<(), Failure> {
        if self.stage.exists() {
            fs::remove_dir_all(&self.stage).map_err(|e| {
                Failure::new(
                    2,
                    "snapshot",
                    format!("cannot clean {}: {e}", self.stage.display()),
                )
            })?;
        }
        fs::create_dir_all(&self.stage).map_err(|e| {
            Failure::new(
                2,
                "snapshot",
                format!("cannot recreate {}: {e}", self.stage.display()),
            )
        })?;
        self.admitted = None;
        self.execution_began = false;
        Ok(())
    }

    /// Snapshot and stage `trusted/lean/`, `theory/` (when present), and
    /// `TrustedBoundary.lean`, and verify the pinned Lean 4.34.1 binary and
    /// `Init.*` artifacts by SHA-256 digest against `foundation-lock.json`.
    pub fn tool_admission(&mut self) -> Result<&mut AdmittedToolchain, Failure> {
        let modules =
            self.scan_and_stage_tree(&self.source, "Trusted", "src/trusted")?;
        let theory_dir = self.checkout.join("theory");
        let theory_modules = if fs::symlink_metadata(&theory_dir).is_ok() {
            self.scan_and_stage_tree(&theory_dir, "Anneal", "src/theory")?
        } else {
            BTreeMap::new()
        };

        let inspector_src =
            self.checkout.join("trusted/audit/TrustedBoundary.lean");
        let inspector = self.stage.join("src/TrustedBoundary.lean");
        stage_regular_file(&inspector_src, &inspector, "tool-snapshot")?;

        let lock_path = self.source.join("foundation-lock.json");
        let toolchain_path = self.source.join("lean-toolchain");
        regular(&lock_path, "lock")?;
        regular(&toolchain_path, "lock")?;

        let lock_text = fs::read_to_string(&lock_path).map_err(|e| {
            Failure::new(2, "lock", format!("cannot read foundation lock: {e}"))
        })?;
        let parsed_lock: FoundationLock =
            serde_json::from_str(&lock_text).map_err(|e| {
                Failure::new(
                    2,
                    "lock",
                    format!("cannot read foundation lock: {e}"),
                )
            })?;
        if parsed_lock.schema != 1
            || parsed_lock.toolchain != TOOLCHAIN
            || parsed_lock.distributions.is_empty()
            || !parsed_lock
                .distributions
                .values()
                .all(|s| is_sha256_hex(s))
            || parsed_lock.modules.is_empty()
            || !parsed_lock.modules.keys().eq(parsed_lock.graph.keys())
        {
            return Err(Failure::new(
                2,
                "lock",
                "unsupported lock/toolchain schema",
            ));
        }
        for (module, record) in &parsed_lock.modules {
            if !is_sha256_hex(&record.source_sha256)
                || record.parts.len() != PARTS.len()
                || !PARTS.iter().all(|p| record.parts.contains_key(*p))
                || !record
                    .parts
                    .get("olean")
                    .and_then(Option::as_deref)
                    .is_some_and(is_sha256_hex)
            {
                return Err(Failure::new(
                    2,
                    "lock",
                    format!("incomplete artifact-part policy for {module}"),
                ));
            }
            for expected_opt in record.parts.values() {
                if let Some(sha) = expected_opt.as_deref()
                    && !is_sha256_hex(sha)
                {
                    return Err(Failure::new(
                        2,
                        "lock",
                        format!("invalid part digest in {module}"),
                    ));
                }
            }
        }

        let toolchain_text =
            fs::read_to_string(&toolchain_path).map_err(|e| {
                Failure::new(
                    2,
                    "lock",
                    format!("cannot read lean-toolchain: {e}"),
                )
            })?;
        if toolchain_text.trim() != TOOLCHAIN {
            return Err(Failure::new(
                1,
                "lock",
                "lean-toolchain differs from lock",
            ));
        }

        let lean_sha = sha256_file(&self.lean, "toolchain")?;
        if !parsed_lock
            .distributions
            .values()
            .any(|s| s.eq_ignore_ascii_case(&lean_sha))
        {
            return Err(Failure::new(
                2,
                "toolchain",
                format!("Lean binary SHA-256 differs from lock: {lean_sha}"),
            ));
        }

        let actual_version = self
            .process("version", &["--version".to_string()])?
            .trim()
            .to_string();
        let Some(expected_lean_sha) =
            parsed_lock.distributions.get(&actual_version)
        else {
            return Err(Failure::new(
                2,
                "toolchain",
                format!(
                    "Lean version/commit differs from lock: {actual_version}"
                ),
            ));
        };
        if !expected_lean_sha.eq_ignore_ascii_case(&lean_sha) {
            return Err(Failure::new(
                2,
                "toolchain",
                format!(
                    "Lean binary SHA-256 mismatch for {actual_version}: expected {expected_lean_sha}, got {lean_sha}"
                ),
            ));
        }

        let prefix_raw = self
            .process("prefix", &["--print-prefix".to_string()])?
            .trim()
            .to_string();
        let prefix = fs::canonicalize(&prefix_raw).map_err(|e| {
            Failure::new(2, "toolchain", format!("cannot resolve prefix: {e}"))
        })?;

        let mut artifacts = BTreeMap::new();

        for (module, record) in &parsed_lock.modules {
            let rel_mod = module.replace('.', "/");
            let source_path =
                prefix.join("src/lean").join(format!("{rel_mod}.lean"));
            let actual_source_sha = sha256_file(&source_path, "foundation")?;
            if !actual_source_sha.eq_ignore_ascii_case(&record.source_sha256) {
                return Err(Failure::new(
                    2,
                    "foundation",
                    format!(
                        "foundation source SHA-256 mismatch for {module}: expected {}, got {actual_source_sha}",
                        record.source_sha256
                    ),
                ));
            }

            let mut available: BTreeMap<&str, String> = BTreeMap::new();
            for part in PARTS {
                let relative = format!("{rel_mod}.{part}");
                let installed = prefix.join("lib/lean").join(&relative);
                match record.parts.get(part).and_then(Option::as_deref) {
                    None => {
                        if fs::symlink_metadata(&installed).is_ok() {
                            return Err(Failure::new(
                                2,
                                "foundation",
                                format!("unexpected companion part: {relative}"),
                            ));
                        }
                    }
                    Some(expected_part_sha) => {
                        let actual_part_sha =
                            sha256_file(&installed, "foundation")?;
                        if !actual_part_sha
                            .eq_ignore_ascii_case(expected_part_sha)
                        {
                            return Err(Failure::new(
                                2,
                                "foundation",
                                format!(
                                    "foundation artifact SHA-256 mismatch for {relative}: expected {expected_part_sha}, got {actual_part_sha}"
                                ),
                            ));
                        }
                        available
                            .insert(part, installed.to_string_lossy().into_owned());
                    }
                }
            }

            let mod_arts =
                ModuleArtifacts::from_available(&available, "foundation", || {
                    format!("missing olean for {module}")
                })?;
            artifacts.insert(module.clone(), mod_arts);
        }

        self.admitted = Some(AdmittedToolchain {
            inspector,
            version: actual_version,
            prefix,
            axioms: parsed_lock.axioms,
            foundation_graph: parsed_lock.graph.clone(),
            graph: parsed_lock.graph,
            artifacts,
            modules,
            theory_modules,
        });
        Ok(self.admitted.as_mut().unwrap())
    }

    // -----------------------------------------------------------------------
    // Stage 3 & 4: Preflight, `--setup` compilation, and kernel audit
    // -----------------------------------------------------------------------

    /// Run Phase 1 (`"preflight"`) over all staged `Trusted.*` and `Anneal.*`
    /// repository sources and return the validated [`PreflightAdmission`].
    fn preflight_repo_modules(&mut self) -> Result<PreflightAdmission, Failure> {
        let adm = self.admitted()?;
        let sources: Vec<(String, PathBuf)> = adm
            .modules
            .iter()
            .chain(adm.theory_modules.iter())
            .map(|(n, p)| (n.clone(), p.clone()))
            .collect();
        let pf_res: PreflightResult = serde_json::from_value(
            self.inspect(InspectorRequest::Preflight { sources })?,
        )
        .map_err(|_| {
            Failure::operational(
                "preflight",
                "incomplete source-header inventory",
            )
        })?;

        let adm = self.admitted()?;
        let mut imports: BTreeMap<String, Vec<ImportEdge>> = BTreeMap::new();
        let mut module_tiers: BTreeMap<String, TrustTier> = BTreeMap::new();
        for h in pf_res.headers {
            let mod_name = h.module;
            let is_trusted = adm.modules.contains_key(&mod_name);
            if is_trusted {
                let raw_tier = h.trust_tier.ok_or_else(|| {
                    Failure::policy(
                        "preflight",
                        format!(
                            "missing trust tier for Trusted module {mod_name}"
                        ),
                    )
                })?;
                let tier = TrustTier::parse(&raw_tier).ok_or_else(|| {
                    Failure::policy(
                        "preflight",
                        format!(
                            "invalid trust tier {raw_tier} for Trusted module {mod_name}"
                        ),
                    )
                })?;
                module_tiers.insert(mod_name.clone(), tier);
            }
            for edge in &h.imports {
                let imp_mod = edge.module.as_str();
                let allowed = if is_trusted {
                    adm.artifacts.contains_key(imp_mod)
                        || adm.modules.contains_key(imp_mod)
                } else {
                    adm.artifacts.contains_key(imp_mod)
                        || adm.modules.contains_key(imp_mod)
                        || adm.theory_modules.contains_key(imp_mod)
                };
                if !allowed {
                    return Err(Failure::policy(
                        "preflight",
                        format!(
                            "foreign/missing import {imp_mod} in {mod_name}"
                        ),
                    ));
                }
            }
            imports.insert(mod_name, h.imports);
        }

        let expected_count = adm.modules.len() + adm.theory_modules.len();
        if imports.len() != expected_count
            || !adm.modules.keys().all(|m| imports.contains_key(m))
            || !adm.theory_modules.keys().all(|m| imports.contains_key(m))
        {
            return Err(Failure::operational(
                "preflight",
                "incomplete source-header inventory",
            ));
        }

        Ok(PreflightAdmission {
            imports,
            module_tiers,
        })
    }

    /// Compile a single `"preflight"`-admitted `.lean` source file into
    /// `self.stage/<lib_subdir>` using `--setup` and strict kernel flags, and
    /// register its compiled [`ModuleArtifacts`].
    fn compile_lean_module(
        &mut self,
        module: &str,
        src_path: &Path,
        edge_list: Vec<ImportEdge>,
        lib_subdir: &str,
        warn_as_err: bool,
    ) -> Result<(), Failure> {
        let setup_path = self.write_setup_json(module, &edge_list)?;
        let output = self
            .stage
            .join(lib_subdir)
            .join(format!("{}.olean", module.replace('.', "/")));
        if let Some(parent) = output.parent() {
            fs::create_dir_all(parent)
                .map_err(|e| Failure::operational("compile", e.to_string()))?;
        }
        let mut compile_args = vec![
            "-j1".to_string(),
            "-M2048".to_string(),
            "-t0".to_string(),
            "-DElab.async=false".to_string(),
            "-Ddebug.skipKernelTC=false".to_string(),
        ];
        if warn_as_err {
            compile_args.push("-DwarningAsError=true".to_string());
        }
        compile_args.extend([
            "--setup".to_string(),
            setup_path.to_string_lossy().into_owned(),
            "-o".to_string(),
            output.to_string_lossy().into_owned(),
            src_path.to_string_lossy().into_owned(),
        ]);
        self.process(&format!("compile-{module}"), &compile_args)?;

        let stem = output
            .file_name()
            .unwrap()
            .to_string_lossy()
            .strip_suffix("olean")
            .unwrap()
            .to_string();
        let parent = output.parent().unwrap();
        let mut available: BTreeMap<&str, String> = BTreeMap::new();
        for part in PARTS {
            let artifact = parent.join(format!("{stem}{part}"));
            if fs::symlink_metadata(&artifact).is_ok() {
                regular(&artifact, "compile")?;
                available.insert(part, artifact.to_string_lossy().into_owned());
            }
        }
        let mod_arts =
            ModuleArtifacts::from_available(&available, "compile", || {
                format!("compiler omitted output for {module}")
            })?;
        let adm = self.admitted_mut()?;
        adm.artifacts.insert(module.to_string(), mod_arts);
        adm.graph.insert(module.to_string(), edge_list);
        Ok(())
    }

    /// Run the complete repository boundary check (`trusted/lean/` plus
    /// `theory/` when present).
    pub fn run(&mut self) -> Result<Json, Failure> {
        check_checkout_cargo_hygiene(&self.checkout)?;
        self.reset_stage()?;
        self.tool_admission()?;
        let preflight = self.preflight_repo_modules()?;

        let (trusted_set, theory_set) = {
            let adm = self.admitted()?;
            (
                adm.modules.keys().cloned().collect(),
                adm.theory_modules.keys().cloned().collect(),
            )
        };
        let trusted_order = topo_sort_modules(
            trusted_set,
            &preflight.imports,
            "Trusted import cycle",
        )?;
        let theory_order = topo_sort_modules(
            theory_set,
            &preflight.imports,
            "Theory import cycle",
        )?;

        for module in &trusted_order {
            let edge_list = preflight.imports[module].clone();
            let staged_src_path = self.admitted()?.modules[module].clone();
            self.execution_began = true;
            self.compile_lean_module(
                module,
                &staged_src_path,
                edge_list,
                "lib",
                false,
            )?;
        }

        for module in &theory_order {
            let edge_list = preflight.imports[module].clone();
            let staged_src_path =
                self.admitted()?.theory_modules[module].clone();
            self.execution_began = true;
            self.compile_lean_module(
                module,
                &staged_src_path,
                edge_list,
                "theory-lib",
                true,
            )?;
        }

        let audit_req = {
            let adm = self.admitted()?;
            InspectorRequest::Audit {
                trusted: adm.modules.keys().cloned().collect(),
                theory: adm.theory_modules.keys().cloned().collect(),
                module_tiers: preflight.module_tiers,
            }
        };
        let mut report = self.inspect(audit_req)?;
        let version = self.admitted()?.version.clone();
        let rep_obj = report.as_object_mut().unwrap();
        rep_obj.insert("toolchain".to_string(), json!(version));
        rep_obj.insert(
            "guarantee".to_string(),
            json!(
                "kernel dependency closure, module-origin separation, and Cargo DAG boundary"
            ),
        );

        Ok(report)
    }
}

/// Topologically sort the module set `pending` according to `imports_map`,
/// returning a policy rejection (`code == 1`) with `cycle_msg` if `pending`
/// contains an import cycle.
fn topo_sort_modules(
    pending: BTreeSet<String>,
    imports_map: &BTreeMap<String, Vec<ImportEdge>>,
    cycle_msg: &str,
) -> Result<Vec<String>, Failure> {
    if pending.is_empty() {
        return Ok(Vec::new());
    }
    let (ready, remaining): (BTreeSet<String>, BTreeSet<String>) = pending
        .iter()
        .cloned()
        .partition(|n| {
            imports_map[n]
                .iter()
                .all(|e| !pending.contains(&e.module))
        });
    if ready.is_empty() {
        return Err(Failure::policy("preflight", cycle_msg));
    }
    let mut order: Vec<String> = ready.into_iter().collect();
    order.extend(topo_sort_modules(remaining, imports_map, cycle_msg)?);
    Ok(order)
}
