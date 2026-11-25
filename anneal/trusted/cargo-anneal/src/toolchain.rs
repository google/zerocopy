// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Defines the shared Lean 4.34.1 toolchain lock schemas, artifact records,
//! digest and path validators, deterministic topological ordering, and bounded
//! parallel DAG scheduling.

use std::{
    collections::{BTreeMap, BTreeSet},
    ffi::OsStr,
    fs, io,
    num::NonZero,
    path::{Component, Path, PathBuf},
    sync::{
        Condvar, Mutex,
        atomic::{AtomicUsize, Ordering},
    },
};

use serde::Deserialize;
use sha2::{Digest as _, Sha256};
use walkdir::WalkDir;

pub use crate::core::{
    Failure, IR_PARTS, ImportEdge, ModuleArtifacts, OLEAN_PARTS, PARTS, digest_to_hex,
    is_clean_relative_path, is_lean_ident, is_sha256_hex, sha256_bytes, topo_sort_modules,
};
use crate::sys_util::SafeFs;
pub use crate::trusted_bundle::LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256;

/// Represents a JSON value at the `TrustedBoundary.lean` IPC boundary.
pub type Json = serde_json::Value;

/// Names the pinned Lean 4 toolchain identifier required by
/// `foundation-lock.json`.
pub const TOOLCHAIN: &str = "leanprover/lean4:v4.34.1";

/// Lists the six minimal `Init.*` foundation modules forming the transitive
/// closure of `{Init.Prelude, Init.Core}` in unpinned Lean admission.
pub const UNPINNED_FOUNDATION_MODULES: [&str; 6] =
    ["Init.Coe", "Init.Core", "Init.Notation", "Init.Prelude", "Init.SizeOf", "Init.Tactics"];

/// Lists the three foundational axioms permitted in target verification.
pub const FOUNDATION_AXIOMS: [(&str, &str); 3] = [
    ("Classical.choice", "Init.Prelude"),
    ("Quot.sound", "Init.Prelude"),
    ("propext", "Init.Core"),
];

// `OLEAN_PARTS`, `IR_PARTS`, and `PARTS` are re-exported from `crate::core`.

/// Lists the pinned SHA-256 digests of the official Lean 4.34.1 `bin/lean`
/// binaries from `trusted/lean/foundation-lock.json`.
///
/// For `x86_64-unknown-linux-gnu` (`LOCKED_LEAN_X86_64_LINUX_SHA256`), runtime
/// shared libraries under `<prefix>/lib` and `<prefix>/lib/lean` are
/// additionally pinned in [`LOCKED_LEAN_X86_64_LINUX_RUNTIME_LIBS`]; runtime
/// shared libraries on the other triples remain uncatalogued here.
pub const LOCKED_LEAN_SHA256: [&str; 4] = [
    "79fb1d26fa5a39385d59fdc48a711a14b0710ca6480271acce99b4d177cea085",
    "1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554",
    "998f0cc2a5a754cc66df1f33b85e1447528737ff15012db35d8c501754b02f1e",
    LOCKED_LEAN_X86_64_LINUX_SHA256,
];

// Core error, artifact, and import-edge types live in `crate::core`, and
// `LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256` lives in `crate::trusted_bundle`;
// all are re-exported at the top of this module.

/// Represents a header response entry returned by `TrustedBoundary.lean`
/// `"headers"` and `"preflight"` modes.
#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PreflightHeader {
    /// Names the inspected module.
    pub module: String,
    /// Lists the module's header imports in source order.
    pub imports: Vec<ImportEdge>,
    /// Indicates whether the source declares a Lean 4 `module` header.
    #[serde(default)]
    pub is_module: bool,
    /// Holds a `Trusted` module's `-- anneal-trust-tier:` value in
    /// `"preflight"` mode; `"headers"` mode never reports a tier.
    #[serde(default)]
    pub trust_tier: Option<String>,
}

/// Wraps the `"headers"` response array from `TrustedBoundary.lean` `"headers"`
/// and `"preflight"` modes.
#[derive(Debug, Clone, Deserialize)]
pub struct PreflightResult {
    /// Lists one header per inspected source.
    pub headers: Vec<PreflightHeader>,
}

/// Stores the source and 5-part compiled artifact SHA-256 digests inside
/// `foundation-lock.json`.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct FoundationModuleRecord {
    #[serde(rename = "sourceSha256")]
    pub source_sha256: String,
    pub parts: BTreeMap<String, Option<String>>,
}

impl FoundationModuleRecord {
    /// Validate that `source_sha256` and all five [`PARTS`] entries are present
    /// with valid SHA-256 hex digests and a non-null primary `"olean"` digest.
    pub(crate) fn validate_schema(&self, module: &str, phase: &str) -> Result<(), Failure> {
        if !is_sha256_hex(&self.source_sha256)
            || self.parts.len() != PARTS.len()
            || !PARTS.iter().all(|p| self.parts.contains_key(*p))
            || !self.parts.get("olean").and_then(Option::as_deref).is_some_and(is_sha256_hex)
        {
            return Err(Failure::operational(
                phase,
                format!("incomplete artifact-part policy for {module}"),
            ));
        }
        for expected_opt in self.parts.values() {
            if let Some(sha) = expected_opt.as_deref()
                && !is_sha256_hex(sha)
            {
                return Err(Failure::operational(
                    phase,
                    format!("invalid part digest in {module}"),
                ));
            }
        }
        Ok(())
    }
}

/// Deserializes `trusted/lean/foundation-lock.json`.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct FoundationLock {
    pub schema: i64,
    pub toolchain: String,
    pub distributions: BTreeMap<String, String>,
    pub modules: BTreeMap<String, FoundationModuleRecord>,
    pub graph: BTreeMap<String, Vec<ImportEdge>>,
    pub axioms: Vec<(String, String)>,
}

/// Stores the 4-tree recursive SHA-256 sysroot lock loaded from
/// `trusted/audit/library-lock.json` (authenticating `lean/lib/lean/Init/**`,
/// `lean/lib/lean/Std/**`, `lean/src/lean/Init/**`, and
/// `lean/src/lean/Std/**` so dynamically resolved `Init.*` and `Std.*`
/// library imports remain pinned without enumerating thousands of module
/// records; resolved library declarations remain logically untrusted and
/// undergo kernel replay in `targetAudit`).
pub(crate) const LIBRARY_LOCK_TREE_LABELS: [&str; 4] = [
    "lean/lib/lean/Init/**",
    "lean/lib/lean/Std/**",
    "lean/src/lean/Init/**",
    "lean/src/lean/Std/**",
];

/// Parses and enforces the compact 4-line recursive sysroot tree digest in
/// `trusted/audit/library-lock.json`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LibraryLock {
    pub(crate) lib_init_sha256: String,
    pub(crate) lib_std_sha256: String,
    pub(crate) src_init_sha256: String,
    pub(crate) src_std_sha256: String,
}

impl LibraryLock {
    /// Parse a strict 4-line `<sha256>  <tree-label>` lock file, rejecting
    /// empty lines, comments, duplicates, non-hex digests, or unknown/missing
    /// trees.
    pub(crate) fn parse(raw: &str) -> Result<Self, Failure> {
        if raw.contains('\r') {
            return Err(Failure::operational("library-lock", "invalid checked-library catalog"));
        }
        let normalized = raw.strip_suffix('\n').unwrap_or(raw);
        let mut seen: BTreeMap<&str, String> = BTreeMap::new();
        for line in normalized.split('\n') {
            let Some((digest, label)) = line.split_once("  ") else {
                return Err(Failure::operational(
                    "library-lock",
                    "invalid checked-library catalog",
                ));
            };
            if !is_sha256_hex(digest)
                || !LIBRARY_LOCK_TREE_LABELS.contains(&label)
                || seen.contains_key(label)
            {
                return Err(Failure::operational(
                    "library-lock",
                    "invalid checked-library catalog",
                ));
            }
            seen.insert(label, digest.to_ascii_lowercase());
        }
        if seen.len() != LIBRARY_LOCK_TREE_LABELS.len() {
            return Err(Failure::operational("library-lock", "invalid checked-library catalog"));
        }
        Ok(Self {
            lib_init_sha256: seen.remove("lean/lib/lean/Init/**").expect("validated key"),
            lib_std_sha256: seen.remove("lean/lib/lean/Std/**").expect("validated key"),
            src_init_sha256: seen.remove("lean/src/lean/Init/**").expect("validated key"),
            src_std_sha256: seen.remove("lean/src/lean/Std/**").expect("validated key"),
        })
    }

    /// Render the canonical 4-line `library-lock.json` representation.
    #[cfg(test)]
    pub(crate) fn render(&self) -> String {
        format!(
            "{}  lean/lib/lean/Init/**\n{}  lean/lib/lean/Std/**\n{}  lean/src/lean/Init/**\n{}  lean/src/lean/Std/**\n",
            self.lib_init_sha256, self.lib_std_sha256, self.src_init_sha256, self.src_std_sha256,
        )
    }

    /// Compute a 4-tree `LibraryLock` from an installed Lean `prefix`.
    #[cfg(test)]
    pub(crate) fn compute_for_prefix(prefix: &Path, phase: &str) -> Result<Self, Failure> {
        Ok(Self {
            lib_init_sha256: compute_sysroot_tree_digest(&prefix.join("lib/lean/Init"), phase)?,
            lib_std_sha256: compute_sysroot_tree_digest(&prefix.join("lib/lean/Std"), phase)?,
            src_init_sha256: compute_sysroot_tree_digest(&prefix.join("src/lean/Init"), phase)?,
            src_std_sha256: compute_sysroot_tree_digest(&prefix.join("src/lean/Std"), phase)?,
        })
    }

    /// Verify all four `Init`/`Std` sysroot trees beneath `prefix` match this
    /// lock without following symlinks or permitting non-regular files.
    pub(crate) fn verify_prefix(&self, prefix: &Path, phase: &str) -> Result<(), Failure> {
        for (label, rel_dir, expected) in [
            ("lean/lib/lean/Init/**", "lib/lean/Init", &self.lib_init_sha256),
            ("lean/lib/lean/Std/**", "lib/lean/Std", &self.lib_std_sha256),
            ("lean/src/lean/Init/**", "src/lean/Init", &self.src_init_sha256),
            ("lean/src/lean/Std/**", "src/lean/Std", &self.src_std_sha256),
        ] {
            let actual = compute_sysroot_tree_digest(&prefix.join(rel_dir), phase)?;
            if !actual.eq_ignore_ascii_case(expected) {
                return Err(Failure::operational(
                    phase,
                    format!(
                        "sysroot tree {label} SHA-256 mismatch: expected {expected}, got {actual}"
                    ),
                ));
            }
        }
        Ok(())
    }
}

/// Holds the admitted Lean 4.34.1 toolchain state, `foundation-lock.json`
/// metadata, and active artifact graph produced by
/// [`crate::Checker::tool_admission`].
///
/// Grouping all post-admission toolchain state into [`AdmittedToolchain`]
/// ensures that [`crate::Checker`] never carries uninitialized placeholder
/// paths or empty lock structures prior to admission, and avoids coupling
/// target verification to repository-CI source scanning.
#[derive(Debug, Clone)]
pub struct AdmittedToolchain {
    /// Holds the staged path of `TrustedBoundary.lean`.
    pub inspector: PathBuf,
    /// SHA-256 digest of staged `control/TrustedBoundary.lean` at admission.
    pub(crate) inspector_sha256: String,
    /// Verified SHA-256 digest of the admitted `lean` binary.
    pub(crate) lean_sha256: String,
    /// Holds the verified `lean --version` string matching
    /// `foundation-lock.json`.
    pub version: String,
    /// Holds the canonical `lean --print-prefix` sysroot directory.
    pub prefix: PathBuf,
    /// Lists the allowed foundation `(axiom_name, defining_module)` pairs from
    /// `foundation-lock.json`.
    pub axioms: Vec<(String, String)>,
    /// Stores the locked `Init.*` foundation module import graph from
    /// `foundation-lock.json`. Its sorted keys are the admitted foundation
    /// module names.
    pub foundation_graph: BTreeMap<String, Vec<ImportEdge>>,
    /// Tracks the active module import graph (initially `foundation_graph`,
    /// extended with each admitted library and compiled module).
    pub graph: BTreeMap<String, Vec<ImportEdge>>,
    /// Maps each admitted module to its validated `.olean` and `.ir` paths.
    pub artifacts: BTreeMap<String, ModuleArtifacts>,
    /// Holds the installed checked-library catalog, authenticated lazily per
    /// target import closure.
    pub(crate) library_lock: Option<LibraryLock>,
    /// Tracks already authenticated checked libraries. These never join the
    /// replay foundation base.
    pub library_modules: BTreeSet<String>,
    /// Indicates whether this toolchain was admitted under unpinned host
    /// policy (`allow_unpinned_lean = true`) rather than locked SHA-256s.
    pub unpinned: bool,
    /// Collects package roots discovered under `<prefix>/lib/lean` in unpinned
    /// mode (empty in pinned mode).
    pub sysroot_package_roots: BTreeSet<String>,
    /// Records the admitted sysroot source and binary part digests in unpinned
    /// mode so `target-provenance` can detect mid-run sysroot mutation.
    pub(crate) unpinned_records: BTreeMap<String, UnpinnedSysrootArtifacts>,
    /// Records the SHA-256 digest of the unpinned Lean binary at admission so
    /// `target-provenance` can detect mid-run binary replacement.
    pub lean_binary_sha256: Option<String>,
    /// Resolved executable Lean binary (`<prefix>/bin/lean` when present, else
    /// the caller-provided Lean path).
    pub(crate) exec_lean: PathBuf,
    /// Expected locked SHA-256 digest of `exec_lean` in pinned mode.
    pub(crate) expected_lean_sha: Option<String>,
    /// Verified SHA-256 manifest digest of `<prefix>/lib/lean/{Init,Std,Lean}*`
    /// `.olean*` artifacts (populated eagerly in pinned mode and lazily on cache
    /// access in unpinned mode).
    pub(crate) sysroot_manifest_sha256: Option<String>,
    /// Staged precompiled `control/TrustedBoundary.olean` built once per
    /// `Checker` from `control/TrustedBoundary.lean`, plus its SHA-256 digest.
    pub(crate) inspector_olean: Option<(PathBuf, String)>,
    /// Whether this toolchain's runtime shared libraries were verified against
    /// a pinned runtime-library allowlist
    /// (`LOCKED_LEAN_X86_64_LINUX_RUNTIME_LIBS`).
    pub runtime_libs_verified: bool,
}

impl AdmittedToolchain {
    /// Return the sorted list of locked `Init.*` foundation module names.
    pub fn foundation_modules(&self) -> Vec<&str> {
        self.foundation_graph.keys().map(String::as_str).collect()
    }
}

/// Verify an installed toolchain module's `.lean` source and 5 compiled
/// companion parts under `prefix` against `record`, enforcing both SHA-256
/// equality on present parts and physical absence on `None` parts.
pub(crate) fn verify_installed_module_record(
    prefix: &Path,
    module: &str,
    record: &FoundationModuleRecord,
    phase: &str,
) -> Result<ModuleArtifacts, Failure> {
    record.validate_schema(module, phase)?;
    let rel_mod = module.replace('.', "/");
    let source_path = prefix.join("src/lean").join(format!("{rel_mod}.lean"));
    let actual_source_sha = sha256_file(&source_path, phase)?;
    if !actual_source_sha.eq_ignore_ascii_case(&record.source_sha256) {
        return Err(Failure::operational(
            phase,
            format!(
                "{phase} source SHA-256 mismatch for {module}: expected {}, got {actual_source_sha}",
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
                    return Err(Failure::operational(
                        phase,
                        format!("unexpected companion part: {relative}"),
                    ));
                }
            }
            Some(expected_part_sha) => {
                let actual_part_sha = sha256_file(&installed, phase)?;
                if !actual_part_sha.eq_ignore_ascii_case(expected_part_sha) {
                    return Err(Failure::operational(
                        phase,
                        format!(
                            "{phase} artifact SHA-256 mismatch for {relative}: expected {expected_part_sha}, got {actual_part_sha}"
                        ),
                    ));
                }
                available.insert(part, installed.to_string_lossy().into_owned());
            }
        }
    }

    ModuleArtifacts::from_available(&available, phase, || format!("missing olean for {module}"))
}

/// Return `true` if `module` is a valid dotted ASCII Lean module name whose
/// root component is `"Init"` or `"Std"`.
pub(crate) fn is_allowed_unpinned_sysroot_module(module: &str) -> bool {
    !module.is_empty()
        && module.split('.').all(is_lean_ident)
        && matches!(module.split('.').next(), Some("Init" | "Std"))
}

/// Return `true` if `module` lies strictly beneath `Init.*` or `Std.*` so all
/// of its `.lean` and `.olean`/`.ir` files live inside the four directories
/// covered by [`LibraryLock`] (excluding bare `Init`/`Std` barrel files outside
/// `Init/**` and `Std/**`).
pub(crate) fn is_allowed_pinned_library_module(module: &str) -> bool {
    module.contains('.') && is_allowed_unpinned_sysroot_module(module)
}

/// Validate that every module and import target in an unpinned sysroot graph
/// belongs strictly to `Init` or `Std` and is present in `graph`.
pub(crate) fn validate_unpinned_sysroot_graph(
    graph: &BTreeMap<String, Vec<ImportEdge>>,
) -> Result<(), Failure> {
    validate_sysroot_graph_with(graph, false)
}

/// Validate that every module and import target in a pinned `library-lock`
/// sysroot graph belongs strictly to `Init.*` or `Std.*` and is present in
/// `graph`.
pub(crate) fn validate_pinned_library_graph(
    graph: &BTreeMap<String, Vec<ImportEdge>>,
) -> Result<(), Failure> {
    validate_sysroot_graph_with(graph, true)
}

fn validate_sysroot_graph_with(
    graph: &BTreeMap<String, Vec<ImportEdge>>,
    require_submodules_only: bool,
) -> Result<(), Failure> {
    let is_ok = |m: &str| {
        if require_submodules_only {
            is_allowed_pinned_library_module(m)
        } else {
            is_allowed_unpinned_sysroot_module(m)
        }
    };
    let allowed_desc = if require_submodules_only {
        "only Init.* and Std.* are permitted"
    } else {
        "only Init and Std are permitted"
    };
    for (module, edges) in graph {
        if !is_ok(module) {
            return Err(Failure::policy(
                "sysroot",
                format!("disallowed sysroot module {module}: {allowed_desc}"),
            ));
        }
        for edge in edges {
            if !is_ok(&edge.module) {
                return Err(Failure::policy(
                    "sysroot",
                    format!(
                        "disallowed sysroot import {} in {module}: {allowed_desc}",
                        edge.module
                    ),
                ));
            }
            if !graph.contains_key(&edge.module) {
                return Err(Failure::operational(
                    "sysroot",
                    format!("missing resolved import {} from {module}", edge.module),
                ));
            }
        }
    }
    Ok(())
}

/// Compute the minimal foundation closure of `{Init.Prelude, Init.Core}` over
/// `graph`, failing closed if any module in `graph` is outside `Init`/`Std`,
/// any of the six expected foundation modules is missing, or the foundation
/// closure leaves `Init.*`.
pub(crate) fn compute_unpinned_foundation_closure(
    graph: &BTreeMap<String, Vec<ImportEdge>>,
) -> Result<BTreeSet<String>, Failure> {
    validate_unpinned_sysroot_graph(graph)?;
    let mut closure = BTreeSet::new();
    let mut pending = vec!["Init.Prelude".to_string(), "Init.Core".to_string()];
    while let Some(module) = pending.pop() {
        let Some(edges) = graph.get(&module) else {
            return Err(Failure::policy(
                "sysroot",
                format!("missing required foundation module {module}"),
            ));
        };
        if !closure.insert(module.clone()) {
            continue;
        }
        if module.split('.').next() != Some("Init") {
            return Err(Failure::policy(
                "sysroot",
                format!("foundation closure exceeded Init.*: {module}"),
            ));
        }
        pending.extend(edges.iter().map(|edge| edge.module.clone()));
    }
    for required in UNPINNED_FOUNDATION_MODULES {
        if !closure.contains(required) {
            return Err(Failure::policy(
                "sysroot",
                format!("missing required foundation module {required}"),
            ));
        }
    }
    Ok(closure)
}

/// Scan `<prefix>/lib/lean` (dereferencing symlinks) to collect all sysroot
/// package roots from subdirectories and `.olean` files.
pub(crate) fn scan_sysroot_package_roots(
    prefix: &Path,
    phase: &str,
) -> Result<BTreeSet<String>, Failure> {
    let lib_lean = prefix.join("lib/lean");
    let lib_meta = fs::metadata(&lib_lean).map_err(|e| {
        Failure::operational(phase, format!("cannot inspect {}: {e}", lib_lean.display()))
    })?;
    if !lib_meta.is_dir() {
        return Err(Failure::operational(
            phase,
            format!("expected sysroot library directory: {}", lib_lean.display()),
        ));
    }
    let mut roots = BTreeSet::new();
    let entries = fs::read_dir(&lib_lean).map_err(|e| {
        Failure::operational(phase, format!("cannot read {}: {e}", lib_lean.display()))
    })?;
    for entry in entries {
        let entry = entry.map_err(|e| {
            Failure::operational(phase, format!("cannot read {}: {e}", lib_lean.display()))
        })?;
        let path = entry.path();
        let meta = fs::metadata(&path).map_err(|e| {
            Failure::operational(phase, format!("cannot inspect {}: {e}", path.display()))
        })?;
        let Some(name) = entry.file_name().to_str().map(str::to_owned) else {
            continue;
        };
        if meta.is_dir() && is_lean_ident(&name) {
            roots.insert(name);
        } else if meta.is_file()
            && let Some(stem) = name.strip_suffix(".olean")
            && is_lean_ident(stem)
        {
            roots.insert(stem.to_owned());
        }
    }
    Ok(roots)
}

/// Compute the transitive import closure of `imports` across `graph`, following
/// every edge (including `isExported: false` private and `isMeta: true` meta
/// imports).
pub(crate) fn transitive_import_closure(
    graph: &BTreeMap<String, Vec<ImportEdge>>,
    imports: &[ImportEdge],
) -> BTreeSet<String> {
    let mut closure = BTreeSet::new();
    let mut pending: Vec<String> = imports.iter().map(|e| e.module.clone()).collect();
    while let Some(module) = pending.pop() {
        if !closure.insert(module.clone()) {
            continue;
        }
        if let Some(edges) = graph.get(&module) {
            pending.extend(edges.iter().map(|e| e.module.clone()));
        }
    }
    closure
}

/// Holds validated paths and in-place SHA-256 digests for an unpinned sysroot
/// module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct UnpinnedSysrootArtifacts {
    pub artifacts: ModuleArtifacts,
    pub source_sha256: Option<String>,
    pub part_hashes: Vec<(String, String)>,
}

/// Read and SHA-256 hash a regular file, dereferencing symlinks while guarding
/// against non-regular targets (FIFOs, sockets, devices) and TOCTOU swaps.
pub fn read_regular_file_deref(path: &Path, phase: &str) -> Result<(Vec<u8>, String), Failure> {
    SafeFs::read_regular_file_deref(path, phase)
}

#[cfg(test)]
fn open_regular_nofollow_nonblock(path: &Path, phase: &str) -> Result<fs::File, Failure> {
    SafeFs::open_regular_nofollow_nonblock(path, phase)
}

fn read_regular_file_strict_raw(
    path: &Path,
    expected_canon: Option<&Path>,
    phase: &str,
) -> Result<(Vec<u8>, [u8; 32]), Failure> {
    SafeFs::read_regular_file_strict_raw(path, expected_canon, phase)
}

/// Read and SHA-256 hash a regular file while rejecting symlinks and
/// non-regular files, verifying the open fd and post-read canonical path.
pub fn read_regular_file_strict(
    path: &Path,
    expected_canon: Option<&Path>,
    phase: &str,
) -> Result<(Vec<u8>, String), Failure> {
    SafeFs::read_regular_file_strict(path, expected_canon, phase)
}

/// Hash a file, dereferencing symlinks (for sysroot libraries/sources and tool
/// binaries).
pub fn sha256_file_deref(path: &Path, phase: &str) -> Result<String, Failure> {
    SafeFs::sha256_file_deref(path, phase)
}

fn hash_optional_file_deref(path: &Path, phase: &str) -> Result<Option<String>, Failure> {
    match fs::symlink_metadata(path) {
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(None),
        Err(e) => {
            Err(Failure::operational(phase, format!("cannot inspect {}: {e}", path.display())))
        }
        Ok(_) => Ok(Some(sha256_file_deref(path, phase)?)),
    }
}

/// Hash every present binary artifact part of an unpinned sysroot `module`
/// under `prefix` (requiring `.olean`) and hash its `.lean` source if present
/// (`None` when absent).
pub(crate) fn hash_unpinned_sysroot_module(
    prefix: &Path,
    module: &str,
    phase: &str,
) -> Result<UnpinnedSysrootArtifacts, Failure> {
    if !is_allowed_unpinned_sysroot_module(module) {
        return Err(Failure::policy(phase, format!("disallowed unpinned sysroot module {module}")));
    }
    let rel_mod = module.replace('.', "/");
    let source_path = prefix.join("src/lean").join(format!("{rel_mod}.lean"));
    let source_sha256 = hash_optional_file_deref(&source_path, phase)?;

    let mut available: BTreeMap<&str, String> = BTreeMap::new();
    let mut hashes_by_part: BTreeMap<&str, (String, String)> = BTreeMap::new();
    for part in PARTS {
        let installed = prefix.join("lib/lean").join(format!("{rel_mod}.{part}"));
        if let Some(sha) = hash_optional_file_deref(&installed, phase)? {
            let file_name = installed
                .file_name()
                .and_then(|s| s.to_str())
                .ok_or_else(|| Failure::operational(phase, "non-UTF-8 artifact file name"))?
                .to_owned();
            available.insert(part, installed.to_string_lossy().into_owned());
            hashes_by_part.insert(part, (file_name, sha));
        }
    }
    let artifacts = ModuleArtifacts::from_available(&available, phase, || {
        format!("missing olean for {module}")
    })?;
    let part_hashes = OLEAN_PARTS
        .iter()
        .chain(IR_PARTS.iter())
        .filter_map(|p| hashes_by_part.remove(*p))
        .collect();
    Ok(UnpinnedSysrootArtifacts { artifacts, source_sha256, part_hashes })
}

fn non_empty_path(value: Option<&OsStr>) -> Option<PathBuf> {
    value.filter(|v| !v.is_empty()).map(PathBuf::from)
}

pub(crate) fn cache_dir_for_platform(
    is_macos: bool,
    xdg_cache_home: Option<&OsStr>,
    home: &Path,
) -> PathBuf {
    if is_macos {
        home.join("Library/Caches")
    } else {
        non_empty_path(xdg_cache_home)
            .filter(|p| p.is_absolute())
            .unwrap_or_else(|| home.join(".cache"))
    }
}

/// Resolve the ordered `anneal/toolchain` parent directories and the fallback
/// `.elan` Lean binary path from raw `XDG_CACHE_HOME` and `HOME` values.
fn lean_search_locations_for_platform(
    is_macos: bool,
    xdg_cache_home: Option<&OsStr>,
    home: Option<&OsStr>,
) -> ([PathBuf; 2], PathBuf) {
    let home = non_empty_path(home).unwrap_or_else(|| PathBuf::from("/root"));
    let cache = cache_dir_for_platform(is_macos, xdg_cache_home, &home);
    let tc_bases = [cache.join("anneal/toolchain"), home.join("anneal/toolchain")];
    let elan_lean = home.join(".elan/toolchains/leanprover--lean4---v4.34.1/bin/lean");
    (tc_bases, elan_lean)
}

fn lean_search_locations(
    xdg_cache_home: Option<&OsStr>,
    home: Option<&OsStr>,
) -> ([PathBuf; 2], PathBuf) {
    lean_search_locations_for_platform(cfg!(target_os = "macos"), xdg_cache_home, home)
}

#[doc(hidden)]
pub fn default_lean_search_bases_from_env(
    xdg_cache_home: Option<&OsStr>,
    home: Option<&OsStr>,
) -> [PathBuf; 2] {
    lean_search_locations(xdg_cache_home, home).0
}

fn default_lean_path_for_platform(
    is_macos: bool,
    xdg_cache_home: Option<&OsStr>,
    home: Option<&OsStr>,
) -> PathBuf {
    let (tc_bases, elan_lean) = lean_search_locations_for_platform(is_macos, xdg_cache_home, home);
    let mut candidate_paths = Vec::new();
    for tc_base in tc_bases {
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
            dirs.sort_by_key(|a| std::cmp::Reverse(a.0));
            candidate_paths.extend(dirs.into_iter().map(|(_, p)| p));
        }
    }
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

fn default_lean_path_from_env(xdg_cache_home: Option<&OsStr>, home: Option<&OsStr>) -> PathBuf {
    default_lean_path_for_platform(cfg!(target_os = "macos"), xdg_cache_home, home)
}

/// Resolve the default pinned Lean 4.34.1 binary path when none is explicitly
/// provided, selecting a candidate binary whose SHA-256 matches
/// [`LOCKED_LEAN_SHA256`].
pub fn default_lean_path() -> PathBuf {
    default_lean_path_from_env(
        std::env::var_os("XDG_CACHE_HOME").as_deref(),
        std::env::var_os("HOME").as_deref(),
    )
}

/// Verify that `path` exists and is a regular file (not a symlink, directory,
/// FIFO, or device node) using `symlink_metadata` so symlinks are never
/// silently followed.
pub fn regular(path: &Path, phase: &str) -> Result<(), Failure> {
    SafeFs::regular(path, phase)
}

/// Verify that `path` is a regular file and return its lowercase hex SHA-256
/// digest.
pub fn sha256_file(path: &Path, phase: &str) -> Result<String, Failure> {
    SafeFs::sha256_file(path, phase)
}

/// Copy a regular source file `src` to `dst`, creating parent directories as
/// needed, and return the SHA-256 digest of the copied bytes.
pub fn stage_regular_file(src: &Path, dst: &Path, phase: &str) -> Result<String, Failure> {
    SafeFs::stage_regular_file(src, dst, phase)
}

fn walk_and_hash_sysroot_dir(
    lib_dir: &Path,
    foundation_modules: &BTreeSet<String>,
    phase: &str,
) -> Result<(String, BTreeSet<String>), Failure> {
    walk_and_hash_sysroot_dir_with_mode(lib_dir, foundation_modules, false, phase)
}

fn walk_and_hash_sysroot_dir_with_mode(
    lib_dir: &Path,
    foundation_modules: &BTreeSet<String>,
    unpinned_tolerant: bool,
    phase: &str,
) -> Result<(String, BTreeSet<String>), Failure> {
    let mut files_to_hash: Vec<(String, PathBuf)> = Vec::new();
    let mut modules: BTreeSet<String> = BTreeSet::new();
    for pkg in ["Init", "Std", "Lean"] {
        for ext in OLEAN_PARTS {
            let rel = format!("{pkg}.{ext}");
            let path = lib_dir.join(&rel);
            let meta_res =
                if unpinned_tolerant { fs::metadata(&path) } else { fs::symlink_metadata(&path) };
            match meta_res {
                Ok(meta) => {
                    let ft = meta.file_type();
                    if !unpinned_tolerant && ft.is_symlink() {
                        return Err(Failure::policy(
                            phase,
                            format!("symlink forbidden in sysroot: {}", path.display()),
                        ));
                    }
                    if !ft.is_file() {
                        return Err(Failure::policy(
                            phase,
                            format!("unexpected file type in sysroot: {}", path.display()),
                        ));
                    }
                    files_to_hash.push((rel, path));
                    if ext == "olean" && !foundation_modules.contains(pkg) {
                        modules.insert(pkg.to_string());
                    }
                }
                Err(e) if e.kind() == io::ErrorKind::NotFound => {}
                Err(e) => {
                    return Err(Failure::policy(
                        phase,
                        format!("cannot inspect sysroot {}: {e}", path.display()),
                    ));
                }
            }
        }
        let pkg_dir = lib_dir.join(pkg);
        if unpinned_tolerant {
            match fs::metadata(&pkg_dir) {
                Ok(meta) if meta.is_dir() => {}
                Ok(_) => {
                    return Err(Failure::policy(
                        phase,
                        format!("unexpected file type in sysroot: {}", pkg_dir.display()),
                    ));
                }
                Err(e) if e.kind() == io::ErrorKind::NotFound => continue,
                Err(e) => {
                    return Err(Failure::policy(
                        phase,
                        format!("cannot inspect sysroot {}: {e}", pkg_dir.display()),
                    ));
                }
            }
        }
        for item in WalkDir::new(&pkg_dir).follow_links(unpinned_tolerant) {
            let item = item.map_err(|e| {
                Failure::policy(phase, format!("cannot walk sysroot {}: {e}", pkg_dir.display()))
            })?;
            let ft = item.file_type();
            if !unpinned_tolerant && ft.is_symlink() {
                return Err(Failure::policy(
                    phase,
                    format!("symlink forbidden in sysroot: {}", item.path().display()),
                ));
            }
            if ft.is_dir() {
                continue;
            }
            if !ft.is_file() {
                return Err(Failure::policy(
                    phase,
                    format!("unexpected file type in sysroot: {}", item.path().display()),
                ));
            }
            let rel_path = item.path().strip_prefix(lib_dir).map_err(|e| {
                Failure::operational(phase, format!("invalid sysroot relative path: {e}"))
            })?;
            let mut segs = Vec::new();
            for comp in rel_path.components() {
                let Component::Normal(os) = comp else {
                    return Err(Failure::policy(
                        phase,
                        format!("invalid path component in {}", item.path().display()),
                    ));
                };
                let Some(s) = os.to_str() else {
                    return Err(Failure::policy(
                        phase,
                        format!("non-UTF-8 path in sysroot: {}", item.path().display()),
                    ));
                };
                segs.push(s);
            }
            let rel_str = segs.join("/");
            let is_olean_part = OLEAN_PARTS.iter().any(|ext| rel_str.ends_with(&format!(".{ext}")));
            if is_olean_part {
                if let Some(stem) = rel_str.strip_suffix(".olean") {
                    let mod_name = stem.replace('/', ".");
                    if !mod_name.split('.').all(is_lean_ident) {
                        return Err(Failure::policy(
                            phase,
                            format!("invalid sysroot module identifier: {mod_name}"),
                        ));
                    }
                    if !foundation_modules.contains(&mod_name) {
                        modules.insert(mod_name);
                    }
                }
                files_to_hash.push((rel_str, item.path().to_path_buf()));
            }
        }
    }

    // Hash the validated regular files across up to 4 bounded worker threads,
    // then reassemble digests in deterministic index order so both the
    // canonical `BTreeMap` manifest and the first reported error match a
    // single-threaded walk.
    let workers = std::thread::available_parallelism()
        .map(NonZero::get)
        .unwrap_or(1)
        .min(4)
        .min(files_to_hash.len());
    let mut entries: BTreeMap<String, String> = BTreeMap::new();
    let hash_one = |path: &Path| {
        if unpinned_tolerant { sha256_file_deref(path, phase) } else { sha256_file(path, phase) }
    };
    if workers <= 1 {
        for (rel, path) in files_to_hash {
            let sha = hash_one(&path)?;
            entries.insert(rel, sha);
        }
    } else {
        let next_idx = AtomicUsize::new(0);
        let min_err_idx = AtomicUsize::new(usize::MAX);
        let outcomes: Mutex<Vec<(usize, Result<String, Failure>)>> =
            Mutex::new(Vec::with_capacity(files_to_hash.len()));
        std::thread::scope(|scope| {
            for _ in 0..workers {
                scope.spawn(|| {
                    let mut local = Vec::new();
                    loop {
                        let idx = next_idx.fetch_add(1, Ordering::Relaxed);
                        if idx >= files_to_hash.len() || idx > min_err_idx.load(Ordering::Relaxed) {
                            break;
                        }
                        let res = hash_one(&files_to_hash[idx].1);
                        if res.is_err() {
                            min_err_idx.fetch_min(idx, Ordering::Relaxed);
                        }
                        local.push((idx, res));
                    }
                    outcomes.lock().unwrap_or_else(|e| e.into_inner()).extend(local);
                });
            }
        });
        let mut collected = outcomes.into_inner().unwrap_or_else(|e| e.into_inner());
        collected.sort_unstable_by_key(|(idx, _)| *idx);
        for (idx, res) in collected {
            let sha = res?;
            entries.insert(files_to_hash[idx].0.clone(), sha);
        }
    }

    let mut manifest = String::new();
    for (rel, sha) in &entries {
        manifest.push_str(rel);
        manifest.push(':');
        manifest.push_str(sha);
        manifest.push('\n');
    }
    Ok((sha256_bytes(manifest.as_bytes()), modules))
}

/// Authenticate every `Init`, `Std`, and `Lean` `.olean`/`.olean.server`/
/// `.olean.private` artifact under `lib_dir` against `expected_manifest_sha`
/// and return the sorted `.sysrootFoundation` module names (excluding
/// `foundation_modules`).
pub fn verify_sysroot_foundation_dir(
    lib_dir: &Path,
    foundation_modules: &BTreeSet<String>,
    expected_manifest_sha: &str,
) -> Result<Vec<String>, Failure> {
    let phase = "sysroot-foundation";
    let (actual_manifest_sha, modules) =
        walk_and_hash_sysroot_dir(lib_dir, foundation_modules, phase)?;
    if !actual_manifest_sha.eq_ignore_ascii_case(expected_manifest_sha) {
        return Err(Failure::policy(
            phase,
            format!(
                "sysroot Init/Std/Lean .olean manifest SHA-256 mismatch: expected {expected_manifest_sha}, got {actual_manifest_sha}"
            ),
        ));
    }
    Ok(modules.into_iter().collect())
}

/// Compute the canonical SHA-256 manifest digest of `<prefix>/lib/lean/{Init,Std,Lean}*`
/// `.olean*` artifacts without filtering any module names.
pub(crate) fn compute_sysroot_manifest_sha256(
    lib_dir: &Path,
    phase: &str,
) -> Result<String, Failure> {
    walk_and_hash_sysroot_dir(lib_dir, &BTreeSet::new(), phase).map(|(sha, _)| sha)
}

/// Compute the SHA-256 manifest digest of an unpinned sysroot `lib/lean` tree,
/// tolerating optional absent packages (`Std`/`Lean`) and dereferencing
/// symlinks permitted in `--allow-unpinned-lean` configurations.
pub(crate) fn compute_unpinned_sysroot_manifest_sha256(
    lib_dir: &Path,
    phase: &str,
) -> Result<String, Failure> {
    walk_and_hash_sysroot_dir_with_mode(lib_dir, &BTreeSet::new(), true, phase).map(|(sha, _)| sha)
}

/// Compute a deterministic SHA-256 digest over every regular file recursively
/// beneath `root_dir`, framing entries as `<rel-posix>\0<sha256-digest>` sorted
/// by POSIX relative path and failing closed on symlinks or non-regular files.
pub(crate) fn compute_sysroot_tree_digest(root_dir: &Path, phase: &str) -> Result<String, Failure> {
    let root_meta = fs::symlink_metadata(root_dir).map_err(|e| {
        Failure::operational(
            phase,
            format!("cannot inspect sysroot tree {}: {e}", root_dir.display()),
        )
    })?;
    if root_meta.file_type().is_symlink() {
        return Err(Failure::policy(
            phase,
            format!("symlink forbidden in sysroot: {}", root_dir.display()),
        ));
    }
    if !root_meta.file_type().is_dir() {
        return Err(Failure::operational(
            phase,
            format!("expected sysroot directory: {}", root_dir.display()),
        ));
    }
    let mut files: Vec<(String, PathBuf)> = Vec::new();
    for item in WalkDir::new(root_dir).follow_links(false) {
        let item = item.map_err(|e| {
            Failure::policy(phase, format!("cannot walk sysroot {}: {e}", root_dir.display()))
        })?;
        let ft = item.file_type();
        if ft.is_symlink() {
            return Err(Failure::policy(
                phase,
                format!("symlink forbidden in sysroot: {}", item.path().display()),
            ));
        }
        if ft.is_dir() {
            continue;
        }
        if !ft.is_file() {
            return Err(Failure::policy(
                phase,
                format!("unexpected file type in sysroot: {}", item.path().display()),
            ));
        }
        let rel_path = item.path().strip_prefix(root_dir).map_err(|e| {
            Failure::operational(phase, format!("invalid sysroot relative path: {e}"))
        })?;
        let mut segs = Vec::new();
        for comp in rel_path.components() {
            let Component::Normal(os) = comp else {
                return Err(Failure::policy(
                    phase,
                    format!("invalid path component in {}", item.path().display()),
                ));
            };
            let Some(s) = os.to_str() else {
                return Err(Failure::policy(
                    phase,
                    format!("non-UTF-8 path in sysroot: {}", item.path().display()),
                ));
            };
            segs.push(s);
        }
        files.push((segs.join("/"), item.path().to_path_buf()));
    }
    files.sort_by(|a, b| a.0.as_bytes().cmp(b.0.as_bytes()));

    let workers =
        std::thread::available_parallelism().map(NonZero::get).unwrap_or(1).min(4).min(files.len());
    let digests: Vec<[u8; 32]> = if workers <= 1 {
        let mut out = Vec::with_capacity(files.len());
        for (_, path) in &files {
            let (_, digest) = read_regular_file_strict_raw(path, None, phase)?;
            out.push(digest);
        }
        out
    } else {
        type DigestOutcome = (usize, Result<[u8; 32], Failure>);
        let next_idx = AtomicUsize::new(0);
        let min_err_idx = AtomicUsize::new(usize::MAX);
        let outcomes: Mutex<Vec<DigestOutcome>> = Mutex::new(Vec::with_capacity(files.len()));
        std::thread::scope(|scope| {
            for _ in 0..workers {
                scope.spawn(|| {
                    let mut local = Vec::new();
                    loop {
                        let idx = next_idx.fetch_add(1, Ordering::Relaxed);
                        if idx >= files.len() || idx > min_err_idx.load(Ordering::Relaxed) {
                            break;
                        }
                        let res = read_regular_file_strict_raw(&files[idx].1, None, phase)
                            .map(|(_, digest)| digest);
                        if res.is_err() {
                            min_err_idx.fetch_min(idx, Ordering::Relaxed);
                        }
                        local.push((idx, res));
                    }
                    outcomes.lock().unwrap_or_else(|e| e.into_inner()).extend(local);
                });
            }
        });
        let mut collected = outcomes.into_inner().unwrap_or_else(|e| e.into_inner());
        collected.sort_unstable_by_key(|(idx, _)| *idx);
        let mut out = Vec::with_capacity(files.len());
        for (_, res) in collected {
            out.push(res?);
        }
        out
    };

    let mut outer = Sha256::new();
    for ((rel, _), digest) in files.iter().zip(digests.iter()) {
        outer.update(rel.as_bytes());
        outer.update([0u8]);
        outer.update(digest);
    }
    let finalized: [u8; 32] = outer.finalize().into();
    Ok(digest_to_hex(&finalized))
}

/// Collect regular binary artifact parts for a pinned `Init.*`/`Std.*`
/// `module` under `prefix`, strictly forbidding symlinks.
pub(crate) fn collect_pinned_sysroot_module_artifacts(
    prefix: &Path,
    module: &str,
    phase: &str,
) -> Result<ModuleArtifacts, Failure> {
    if !is_allowed_pinned_library_module(module) {
        return Err(Failure::policy(phase, format!("disallowed sysroot module {module}")));
    }
    let rel_mod = module.replace('.', "/");
    let source_path = prefix.join("src/lean").join(format!("{rel_mod}.lean"));
    match fs::symlink_metadata(&source_path) {
        Err(e) if e.kind() == io::ErrorKind::NotFound => {}
        Err(e) => {
            return Err(Failure::operational(
                phase,
                format!("cannot inspect {}: {e}", source_path.display()),
            ));
        }
        Ok(_) => regular(&source_path, phase)?,
    }
    let mut available: BTreeMap<&str, String> = BTreeMap::new();
    for part in PARTS {
        let installed = prefix.join("lib/lean").join(format!("{rel_mod}.{part}"));
        match fs::symlink_metadata(&installed) {
            Err(e) if e.kind() == io::ErrorKind::NotFound => {}
            Err(e) => {
                return Err(Failure::operational(
                    phase,
                    format!("cannot inspect {}: {e}", installed.display()),
                ));
            }
            Ok(_) => {
                regular(&installed, phase)?;
                available.insert(part, installed.to_string_lossy().into_owned());
            }
        }
    }
    ModuleArtifacts::from_available(&available, phase, || format!("missing olean for {module}"))
}

#[cfg(test)]
pub(crate) fn compute_sysroot_manifest_sha256_for_test(lib_dir: &Path) -> String {
    walk_and_hash_sysroot_dir(lib_dir, &BTreeSet::new(), "sysroot-foundation")
        .expect("test sysroot directory should hash cleanly")
        .0
}

// `is_clean_relative_path` & `topo_sort_modules` are re-exported from `core`.

/// Return a bounded worker count based on available host parallelism, capped
/// at `cap` and never below `1`.
#[doc(hidden)]
pub fn default_compile_workers(cap: usize) -> usize {
    std::thread::available_parallelism().map(NonZero::get).unwrap_or(1).min(cap.max(1)).max(1)
}

/// Validated acyclic DAG plan for [`run_parallel_dag`].
///
/// Construction rejects duplicate/self edges, out-of-range indices, and cycles
/// so callers cannot schedule an invalid dependency graph.
#[doc(hidden)]
pub struct ParallelDagPlan {
    active: Vec<bool>,
    in_degree: Vec<usize>,
    dependents: Vec<Vec<usize>>,
    min_active_descendant: Vec<usize>,
}

impl ParallelDagPlan {
    /// Validate an indexed DAG (`0..active.len()`) whose dependency edges are
    /// `dependents` (each `u -> v` edge means `v` waits for `u`), deriving
    /// `in_degree` directly so edge counts cannot drift, and returning a
    /// policy rejection with `(cycle_phase, cycle_msg)` on any cycle or
    /// self-loop.
    pub fn from_indexed_edges(
        active: Vec<bool>,
        dependents: Vec<Vec<usize>>,
        cycle_phase: &str,
        cycle_msg: &str,
    ) -> Result<Self, Failure> {
        let total_len = active.len();
        if dependents.len() != total_len {
            return Err(Failure::operational(cycle_phase, "mismatched parallel DAG dimension"));
        }
        let mut normalized: Vec<Vec<usize>> = Vec::with_capacity(total_len);
        let mut in_degree = vec![0usize; total_len];
        for (u, edges) in dependents.into_iter().enumerate() {
            let mut unique = BTreeSet::new();
            let mut deduped = Vec::with_capacity(edges.len());
            for v in edges {
                if v >= total_len {
                    return Err(Failure::operational(
                        cycle_phase,
                        "out-of-range parallel DAG edge",
                    ));
                }
                if v == u {
                    return Err(Failure::policy(cycle_phase, cycle_msg));
                }
                if unique.insert(v) {
                    in_degree[v] += 1;
                    deduped.push(v);
                }
            }
            normalized.push(deduped);
        }
        let topo_order = verify_dag_acyclic(&in_degree, &normalized, cycle_phase, cycle_msg)?;
        let mut min_active_descendant = vec![usize::MAX; total_len];
        for &u in topo_order.iter().rev() {
            let mut best = if active[u] { u } else { usize::MAX };
            for &v in &normalized[u] {
                best = best.min(min_active_descendant[v]);
            }
            min_active_descendant[u] = best;
        }
        Ok(Self { active, in_degree, dependents: normalized, min_active_descendant })
    }

    /// Build a validated DAG plan over `order` (all nodes active) from the
    /// verified `imports` map, ignoring imports outside `order`.
    pub fn from_module_order(
        order: &[String],
        imports: &BTreeMap<String, Vec<ImportEdge>>,
        cycle_phase: &str,
        cycle_msg: &str,
    ) -> Result<Self, Failure> {
        let total_len = order.len();
        let idx_by_module: BTreeMap<&str, usize> =
            order.iter().enumerate().map(|(idx, m)| (m.as_str(), idx)).collect();
        if idx_by_module.len() != total_len {
            return Err(Failure::policy(cycle_phase, "duplicate module in compile order"));
        }
        let mut dependents: Vec<Vec<usize>> = vec![Vec::new(); total_len];
        for (dst_idx, module) in order.iter().enumerate() {
            let Some(edges) = imports.get(module) else {
                return Err(Failure::operational(
                    cycle_phase,
                    format!("missing import inventory for {module}"),
                ));
            };
            for edge in edges {
                if let Some(&src_idx) = idx_by_module.get(edge.module.as_str()) {
                    dependents[src_idx].push(dst_idx);
                }
            }
        }
        Self::from_indexed_edges(vec![true; total_len], dependents, cycle_phase, cycle_msg)
    }

    /// Count how many nodes in this plan require execution.
    pub fn active_count(&self) -> usize {
        self.active.iter().filter(|&&a| a).count()
    }
}

struct DagState {
    ready: BTreeSet<(usize, usize)>,
    in_degree: Vec<usize>,
    active_workers: usize,
    first_error: Option<(usize, Failure)>,
}

struct DagWorkerPanicGuard<'sync, 's, S> {
    sync: &'sync (Mutex<(DagState, &'s mut S)>, Condvar),
    entry_idx: usize,
    panic_phase: &'sync str,
    panic_message: &'sync str,
    armed: bool,
}

impl<S> Drop for DagWorkerPanicGuard<'_, '_, S> {
    fn drop(&mut self) {
        if self.armed {
            let (lock, cvar) = self.sync;
            let mut guard = lock.lock().unwrap_or_else(|e| e.into_inner());
            guard.0.active_workers = guard.0.active_workers.saturating_sub(1);
            record_earliest_dag_error(
                &mut guard.0.first_error,
                self.entry_idx,
                Failure::operational(self.panic_phase, self.panic_message),
            );
            cvar.notify_all();
        }
    }
}

struct NotifyOnDrop<'a>(&'a Condvar);

impl Drop for NotifyOnDrop<'_> {
    fn drop(&mut self) {
        self.0.notify_all();
    }
}

fn record_earliest_dag_error(slot: &mut Option<(usize, Failure)>, entry_idx: usize, err: Failure) {
    // Operational failures (`code != 1`, e.g. sandbox, timeout, Door 1, or I/O
    // errors) strictly outrank ordinary `code == 1` source/proof rejections so
    // parallel compilation never downgrades `tool_failed` into `proof_failed`.
    // Ties within the same severity class break deterministically by smallest
    // node index.
    let is_op = |f: &Failure| f.code != 1;
    let outranks =
        slot.as_ref().is_none_or(|(best_idx, best_err)| match (is_op(&err), is_op(best_err)) {
            (true, false) => true,
            (false, true) => false,
            _ => entry_idx < *best_idx,
        });
    if outranks {
        *slot = Some((entry_idx, err));
    }
}

fn propagate_dag_completions(
    mut newly_done: Vec<usize>,
    active: &[bool],
    min_active_descendant: &[usize],
    dependents: &[Vec<usize>],
    state: &mut DagState,
) {
    while let Some(done_idx) = newly_done.pop() {
        for &dep_idx in &dependents[done_idx] {
            state.in_degree[dep_idx] -= 1;
            if state.in_degree[dep_idx] == 0 {
                if active[dep_idx] {
                    let min_desc = min_active_descendant[dep_idx];
                    let dep_beaten = state
                        .first_error
                        .as_ref()
                        .is_some_and(|(best_idx, _)| *best_idx < min_desc);
                    if !dep_beaten {
                        state.ready.insert((min_desc, dep_idx));
                    }
                } else {
                    newly_done.push(dep_idx);
                }
            }
        }
    }
}

fn verify_dag_acyclic(
    in_degree: &[usize],
    dependents: &[Vec<usize>],
    cycle_phase: &str,
    cycle_msg: &str,
) -> Result<Vec<usize>, Failure> {
    let mut rem = in_degree.to_vec();
    let mut stack: Vec<usize> = (0..rem.len()).filter(|&i| rem[i] == 0).collect();
    let mut topo_order = Vec::with_capacity(rem.len());
    while let Some(u) = stack.pop() {
        topo_order.push(u);
        for &v in &dependents[u] {
            rem[v] -= 1;
            if rem[v] == 0 {
                stack.push(v);
            }
        }
    }
    if topo_order.len() != rem.len() {
        return Err(Failure::policy(cycle_phase, cycle_msg));
    }
    Ok(topo_order)
}

/// Execute all active nodes in `plan` across at most `max_workers` scoped
/// threads while preserving deterministic failure reporting: operational
/// failures (`Failure.code != 1`) outrank ordinary `code == 1` rejections, and
/// ties within the same severity class break by smallest node index.
///
/// For each ready node `idx`, `prepare` runs under the scheduler mutex before
/// spawning unlocked concurrent work in `run`, and `commit` runs under the
/// same mutex upon successful completion (unless an earlier node index has
/// already failed) before unlocking dependent nodes.
#[doc(hidden)]
#[allow(clippy::too_many_arguments)]
pub fn run_parallel_dag<S, P, T, FP, FR, FC>(
    plan: &ParallelDagPlan,
    max_workers: usize,
    panic_phase: &str,
    panic_message: &str,
    shared: &mut S,
    prepare: FP,
    run: FR,
    commit: FC,
) -> Result<(), Failure>
where
    S: Send,
    FP: Fn(&mut S, usize) -> Result<P, Failure> + Sync,
    FR: Fn(usize, P) -> Result<T, Failure> + Sync,
    FC: Fn(&mut S, usize, T) -> Result<(), Failure> + Sync,
{
    let active_count = plan.active_count();
    if active_count == 0 {
        return Ok(());
    }
    let workers = max_workers.min(active_count).max(1);
    let total_len = plan.active.len();
    let mut init_state = DagState {
        ready: BTreeSet::new(),
        in_degree: plan.in_degree.clone(),
        active_workers: 0,
        first_error: None,
    };
    let mut inactive_roots = Vec::new();
    for idx in 0..total_len {
        if init_state.in_degree[idx] == 0 {
            if plan.active[idx] {
                init_state.ready.insert((plan.min_active_descendant[idx], idx));
            } else {
                inactive_roots.push(idx);
            }
        }
    }
    propagate_dag_completions(
        inactive_roots,
        &plan.active,
        &plan.min_active_descendant,
        &plan.dependents,
        &mut init_state,
    );

    let sync = (Mutex::new((init_state, shared)), Condvar::new());
    std::thread::scope(|scope| {
        for _ in 0..workers {
            scope.spawn(|| {
                let (lock, cvar) = &sync;
                loop {
                    let (entry_idx, prepared) = {
                        let mut guard = lock.lock().unwrap_or_else(|e| e.into_inner());
                        let (state, shared_ref) = &mut *guard;
                        while let Some(&(last_min_desc, _)) = state.ready.last() {
                            let beaten = state
                                .first_error
                                .as_ref()
                                .is_some_and(|(best_idx, _)| *best_idx < last_min_desc);
                            if beaten {
                                state.ready.pop_last();
                            } else {
                                break;
                            }
                        }
                        if let Some((_, next_idx)) = state.ready.pop_first() {
                            let _notify = NotifyOnDrop(cvar);
                            match prepare(*shared_ref, next_idx) {
                                Ok(prep) => {
                                    state.active_workers += 1;
                                    (next_idx, prep)
                                }
                                Err(err) => {
                                    record_earliest_dag_error(
                                        &mut state.first_error,
                                        next_idx,
                                        err,
                                    );
                                    continue;
                                }
                            }
                        } else if state.active_workers == 0 {
                            cvar.notify_all();
                            break;
                        } else {
                            drop(cvar.wait(guard).unwrap_or_else(|e| e.into_inner()));
                            continue;
                        }
                    };

                    let mut panic_guard = DagWorkerPanicGuard {
                        sync: &sync,
                        entry_idx,
                        panic_phase,
                        panic_message,
                        armed: true,
                    };
                    let run_res = run(entry_idx, prepared);

                    let mut guard = lock.lock().unwrap_or_else(|e| e.into_inner());
                    panic_guard.armed = false;
                    let _notify = NotifyOnDrop(cvar);
                    let (state, shared_ref) = &mut *guard;
                    state.active_workers -= 1;
                    let min_desc = plan.min_active_descendant[entry_idx];
                    let beaten = state
                        .first_error
                        .as_ref()
                        .is_some_and(|(best_idx, _)| *best_idx < min_desc);
                    match run_res {
                        Ok(output) if !beaten => match commit(*shared_ref, entry_idx, output) {
                            Ok(()) => propagate_dag_completions(
                                vec![entry_idx],
                                &plan.active,
                                &plan.min_active_descendant,
                                &plan.dependents,
                                state,
                            ),
                            Err(err) => {
                                record_earliest_dag_error(&mut state.first_error, entry_idx, err)
                            }
                        },
                        Ok(_) => {}
                        Err(err) => {
                            record_earliest_dag_error(&mut state.first_error, entry_idx, err);
                        }
                    }
                }
            });
        }
    });

    let (final_state, _) = sync.0.into_inner().unwrap_or_else(|e| e.into_inner());
    if let Some((_, err)) = final_state.first_error {
        return Err(err);
    }
    Ok(())
}

/// SHA-256 digest of the pinned `leanprover/lean4:v4.34.1` `bin/lean` stub for
/// `x86_64-unknown-linux-gnu` (`foundation-lock.json` `distributions`).
pub const LOCKED_LEAN_X86_64_LINUX_SHA256: &str =
    "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550";

/// Core Lean runtime shared libraries required under `<prefix>/lib/` on
/// `x86_64-unknown-linux-gnu`.
const REQUIRED_LEAN_X86_64_LINUX_RUNTIME_LIBS: &[&str] = &[
    "lean/libInit_shared.so",
    "lean/libLake_shared.so",
    "lean/libleanshared.so",
    "lean/libleanshared_1.so",
    "lean/libleanshared_2.so",
];

/// Canonical SHA-256 allowlist for all shared libraries and linker scripts
/// shipped under `<prefix>/lib/` in `leanprover/lean4:v4.34.1` for
/// `x86_64-unknown-linux-gnu` (including both `elan` and Anneal omnibus
/// distributions).
pub const LOCKED_LEAN_X86_64_LINUX_RUNTIME_LIBS: &[(&str, &str)] = &[
    ("glibc/ld-linux-x86.so", "cf102aa2866d69b6b1b6f5195da0031deb7fbae374a0c2f677a1fffc9e01f3f2"),
    ("glibc/ld.so", "cf102aa2866d69b6b1b6f5195da0031deb7fbae374a0c2f677a1fffc9e01f3f2"),
    ("glibc/libc.so", "e256592ceadd9c7c4256e92e845b0899d297d5bd4a6ad932048db5cd5e799e0d"),
    ("glibc/libdl.so", "fc529305501bfce8aa9f614c041c936827cefed5c2c533abbb1867d5ebf84a55"),
    ("glibc/libm.so", "dd9e596df3c48d1805c235fc5b89161c4942dc6641200a813fa75914152d04e9"),
    ("glibc/libpthread.so", "27ba14f60ea7a4d46579879c87e206de33eaac0ccd130d87e6ef4cb3fa28cf86"),
    ("glibc/librt.so", "542ef722b42111dbeaa9f1f6579b933e7bbf1c95466f4dc3604d7905d657e924"),
    ("lean/libInit_shared.so", "07f8c1156271ab6ec36c14c3031b5572329325d5f73dde3e89a1615d88f4e5cb"),
    ("lean/libLake_shared.so", "ef0eb8942cd68ffb61ae573850a7181f70860580959e296c6e1a0e31ec50a38a"),
    ("lean/libleanshared.so", "6b30cc963d065fc9d2f87f7e9cbe0682b23000ae5425bccd769c5d477fa74f13"),
    ("lean/libleanshared_1.so", "69e900c025f40bf05c14f5b9ec48071b3130e34c96a7c45ee2eb5b6f307e19e6"),
    ("lean/libleanshared_2.so", "38d0a03750b2e8d51161885ad597a8b4f6d3b85215c5a52aecd2b3753273cf3f"),
    ("libLLVM-22.so", "5145af96bc961289f6dff7efc0dc7f75cbc4b91634aa3b5d517749dce5f3f300"),
    ("libLLVM.so", "5145af96bc961289f6dff7efc0dc7f75cbc4b91634aa3b5d517749dce5f3f300"),
    ("libLLVM.so.22.1", "5145af96bc961289f6dff7efc0dc7f75cbc4b91634aa3b5d517749dce5f3f300"),
    ("libatomic.so", "b2d3f7d9ebf9a0d5dc9caedcb33a43f6ac1b33221ada1f029147d8a66db43c09"),
    ("libatomic.so.1", "b2d3f7d9ebf9a0d5dc9caedcb33a43f6ac1b33221ada1f029147d8a66db43c09"),
    ("libatomic.so.1.2.0", "b2d3f7d9ebf9a0d5dc9caedcb33a43f6ac1b33221ada1f029147d8a66db43c09"),
    ("libc++.so", "9a82146864488c9d491a6e60be5af3ca986a9af57f6057763c5c0a8dda85a66e"),
    ("libc++.so.1", "0ec88ab403524f6c3bc3d9029772b97d9af08837267a2973bf6b24fa79119704"),
    ("libc++.so.1.0", "0ec88ab403524f6c3bc3d9029772b97d9af08837267a2973bf6b24fa79119704"),
    ("libc++abi.so", "3cb42a1a34f48dd20da4aa7559e634ca2eaeab6b019869fd060f90128ae3cb8b"),
    ("libc++abi.so.1", "3cb42a1a34f48dd20da4aa7559e634ca2eaeab6b019869fd060f90128ae3cb8b"),
    ("libc++abi.so.1.0", "3cb42a1a34f48dd20da4aa7559e634ca2eaeab6b019869fd060f90128ae3cb8b"),
    ("libclang-cpp.so", "e11640dbbd29d2abebcdb62f8e90e8a965d7276df914e3cdcfd5263f427208eb"),
    ("libclang-cpp.so.22.1", "e11640dbbd29d2abebcdb62f8e90e8a965d7276df914e3cdcfd5263f427208eb"),
    ("libgcc_s.so", "69a56a9993b7729b29b274e65016031c81f2397f176ed5ad44d59bd50425e0bd"),
    ("libgcc_s.so.1", "3f499bb3b14f33c5c321f52015d385c145c7bd4551a66c5fcff4262c833f2d2a"),
    ("libunwind.so", "c54929622b0991b21088050bf3f23d6756d3d2e082acd293b0e788ddc901da72"),
    ("libunwind.so.1", "c54929622b0991b21088050bf3f23d6756d3d2e082acd293b0e788ddc901da72"),
    ("libunwind.so.1.0", "c54929622b0991b21088050bf3f23d6756d3d2e082acd293b0e788ddc901da72"),
    ("libz.so", "d0aeafffcfe309a107a857dfa1f9afd0db90796d32c2b735a3959eccb317f5b4"),
    ("libz.so.1", "d0aeafffcfe309a107a857dfa1f9afd0db90796d32c2b735a3959eccb317f5b4"),
    ("libz.so.1.2.11", "d0aeafffcfe309a107a857dfa1f9afd0db90796d32c2b735a3959eccb317f5b4"),
];

fn is_dynamic_runtime_lib_candidate(name: &str) -> bool {
    name.ends_with(".so")
        || name.contains(".so.")
        || name.ends_with(".dylib")
        || name.ends_with(".dll")
}

fn check_no_dynamic_libs_in_bin(bin_dir: &Path) -> Result<(), Failure> {
    let entries = fs::read_dir(bin_dir).map_err(|err| {
        Failure::new(
            2,
            "toolchain",
            format!("cannot read Lean sysroot bin directory {}: {err}", bin_dir.display()),
        )
    })?;
    for entry in entries {
        let entry = entry.map_err(|err| {
            Failure::new(
                2,
                "toolchain",
                format!("cannot inspect Lean sysroot bin directory {}: {err}", bin_dir.display()),
            )
        })?;
        let name = entry.file_name();
        let name_str = name.to_string_lossy();
        if is_dynamic_runtime_lib_candidate(&name_str) {
            return Err(Failure::new(
                2,
                "toolchain",
                format!("unexpected runtime shared library in Lean sysroot: bin/{name_str}"),
            ));
        }
    }
    Ok(())
}

fn walk_and_check_runtime_lib_dir(
    lib_root: &Path,
    dir: &Path,
    allowed: &BTreeMap<&str, &str>,
    seen: &mut BTreeSet<String>,
) -> Result<(), Failure> {
    let entries = fs::read_dir(dir).map_err(|err| {
        Failure::new(
            2,
            "toolchain",
            format!("cannot read Lean sysroot lib directory {}: {err}", dir.display()),
        )
    })?;
    for entry in entries {
        let entry = entry.map_err(|err| {
            Failure::new(
                2,
                "toolchain",
                format!("cannot inspect Lean sysroot lib directory {}: {err}", dir.display()),
            )
        })?;
        let path = entry.path();
        let rel = path.strip_prefix(lib_root).map_err(|err| {
            Failure::operational("toolchain", format!("runtime lib relative path failure: {err}"))
        })?;
        let rel_str = rel
            .components()
            .map(|c| c.as_os_str().to_string_lossy().into_owned())
            .collect::<Vec<_>>()
            .join("/");
        let lmeta = fs::symlink_metadata(&path).map_err(|err| {
            Failure::new(
                2,
                "toolchain",
                format!("cannot stat Lean sysroot lib entry lib/{rel_str}: {err}"),
            )
        })?;
        let ftype = lmeta.file_type();
        if ftype.is_dir() {
            walk_and_check_runtime_lib_dir(lib_root, &path, allowed, seen)?;
            continue;
        }
        if ftype.is_symlink() && fs::metadata(&path).is_ok_and(|meta| meta.is_dir()) {
            if matches!(rel_str.as_str(), "lean/Lake" | "lean/LeanChecker") {
                walk_and_check_runtime_lib_dir(lib_root, &path, allowed, seen)?;
                continue;
            }
            return Err(Failure::new(
                2,
                "toolchain",
                format!("unexpected symlinked directory in Lean sysroot: lib/{rel_str}"),
            ));
        }
        let name = entry.file_name();
        let name_str = name.to_string_lossy();
        if !is_dynamic_runtime_lib_candidate(&name_str) {
            continue;
        }
        let Some(&expected_sha) = allowed.get(rel_str.as_str()) else {
            return Err(Failure::new(
                2,
                "toolchain",
                format!("unexpected runtime shared library in Lean sysroot: lib/{rel_str}"),
            ));
        };
        let actual_sha = sha256_file_deref(&path, "toolchain")
            .map_err(|err| Failure::new(2, "toolchain", err.message))?;
        if !expected_sha.eq_ignore_ascii_case(&actual_sha) {
            return Err(Failure::new(
                2,
                "toolchain",
                format!(
                    "Lean runtime shared library SHA-256 mismatch for lib/{rel_str}: \
                     expected {expected_sha}, got {actual_sha}"
                ),
            ));
        }
        seen.insert(rel_str);
    }
    Ok(())
}

/// Authenticate Lean's dynamically loaded runtime shared libraries under
/// `<prefix>/lib` (and reject unexpected dynamic libraries in `<prefix>/bin`
/// or `<prefix>/lib`) against pinned distribution digests.
///
/// Returns `Ok(true)` when runtime shared libraries for `lean_sha256` were
/// checked and matched, or `Ok(false)` only for distributions whose runtime
/// shared-library manifest is not yet catalogued in this build (currently
/// non-`x86_64-unknown-linux-gnu` triples).
pub fn verify_sysroot_runtime_libs_for_sha(
    prefix: &Path,
    lean_sha256: &str,
) -> Result<bool, Failure> {
    if !lean_sha256.eq_ignore_ascii_case(LOCKED_LEAN_X86_64_LINUX_SHA256) {
        return Ok(false);
    }
    check_no_dynamic_libs_in_bin(&prefix.join("bin"))?;
    let lib_root = prefix.join("lib");
    let allowed: BTreeMap<&str, &str> =
        LOCKED_LEAN_X86_64_LINUX_RUNTIME_LIBS.iter().copied().collect();
    let mut seen = BTreeSet::new();
    walk_and_check_runtime_lib_dir(&lib_root, &lib_root, &allowed, &mut seen)?;
    for &required in REQUIRED_LEAN_X86_64_LINUX_RUNTIME_LIBS {
        if !seen.contains(required) {
            return Err(Failure::new(
                2,
                "toolchain",
                format!("missing required Lean runtime shared library: lib/{required}"),
            ));
        }
    }
    Ok(true)
}

#[cfg(test)]
mod module_order_tests {
    use super::*;

    fn import(module: &str) -> ImportEdge {
        ImportEdge {
            module: module.to_string(),
            import_all: false,
            is_exported: true,
            is_meta: false,
        }
    }

    fn sort(modules: &[(&str, &[&str])]) -> Result<Vec<String>, Failure> {
        let imports: BTreeMap<_, _> = modules
            .iter()
            .map(|(module, dependencies)| {
                (module.to_string(), dependencies.iter().map(|name| import(name)).collect())
            })
            .collect();
        topo_sort_modules(imports.keys().cloned().collect(), &imports, "fixture import cycle")
    }

    #[test]
    fn empty_module_set_has_no_ordering_work() {
        assert_eq!(sort(&[]).unwrap(), Vec::<String>::new());
    }

    #[test]
    fn independent_roots_are_sorted() {
        assert_eq!(sort(&[("Z", &[]), ("A", &[]), ("M", &[])]).unwrap(), ["A", "M", "Z"]);
    }

    #[test]
    fn branching_graph_preserves_sorted_ready_layers() {
        assert_eq!(
            sort(&[
                ("Final", &["AChild", "ZChild"]),
                ("ZRoot", &[]),
                ("AChild", &["ZRoot"]),
                ("ARoot", &[]),
                ("ZChild", &["ARoot"]),
            ])
            .unwrap(),
            ["ARoot", "ZRoot", "AChild", "ZChild", "Final"]
        );
    }

    #[test]
    fn imports_outside_the_pending_set_are_already_available() {
        let imports = BTreeMap::from([
            ("Trusted.Child".to_string(), vec![import("Trusted.Root"), import("External.Ready")]),
            ("Trusted.Root".to_string(), vec![import("Init.Prelude"), import("Init.Notation")]),
            ("External.Ready".to_string(), Vec::new()),
        ]);
        assert_eq!(
            topo_sort_modules(
                BTreeSet::from(["Trusted.Child".to_string(), "Trusted.Root".to_string()]),
                &imports,
                "fixture import cycle",
            )
            .unwrap(),
            ["Trusted.Root", "Trusted.Child"]
        );
    }

    #[test]
    fn cycles_reject_with_the_selected_policy_message() {
        let expected = Err(Failure::policy("preflight", "fixture import cycle"));
        assert_eq!(sort(&[("Self", &["Self"])]), expected);
        assert_eq!(sort(&[("Root", &[]), ("A", &["B"]), ("B", &["A"])]), expected);
    }

    #[test]
    fn deep_dependency_chain_fits_a_small_thread_stack() {
        let modules: Vec<_> = (0..512).map(|i| format!("Module{i:03}")).collect();
        let imports = modules
            .iter()
            .enumerate()
            .map(|(index, module)| {
                let dependencies =
                    if index == 0 { Vec::new() } else { vec![import(&modules[index - 1])] };
                (module.clone(), dependencies)
            })
            .collect();
        let pending = modules.iter().cloned().collect();
        let order = std::thread::Builder::new()
            .stack_size(128 * 1024)
            .spawn(move || topo_sort_modules(pending, &imports, "fixture import cycle"))
            .expect("spawn module ordering thread")
            .join()
            .expect("module ordering thread panicked")
            .unwrap();
        assert_eq!(order, modules);
    }
}

#[cfg(test)]
mod parallel_dag_tests {
    use std::sync::{
        Arc, Barrier,
        atomic::{AtomicUsize, Ordering},
    };

    use super::*;

    #[test]
    fn empty_and_all_inactive_plans_succeed_without_work() {
        let empty = ParallelDagPlan::from_indexed_edges(vec![], vec![], "dag", "cycle").unwrap();
        let mut shared = 0usize;
        run_parallel_dag(
            &empty,
            4,
            "dag",
            "panic",
            &mut shared,
            |s, _| {
                *s += 1;
                Ok(())
            },
            |_, ()| Ok(()),
            |s, _, ()| {
                *s += 1;
                Ok(())
            },
        )
        .unwrap();
        assert_eq!(shared, 0);

        let inactive = ParallelDagPlan::from_indexed_edges(
            vec![false, false],
            vec![vec![1], vec![]],
            "dag",
            "cycle",
        )
        .unwrap();
        run_parallel_dag(
            &inactive,
            4,
            "dag",
            "panic",
            &mut shared,
            |s, _| {
                *s += 1;
                Ok(())
            },
            |_, ()| Ok(()),
            |s, _, ()| {
                *s += 1;
                Ok(())
            },
        )
        .unwrap();
        assert_eq!(shared, 0);
    }

    #[test]
    fn rejects_cycles_self_loops_and_out_of_range_edges() {
        let cycle = ParallelDagPlan::from_indexed_edges(
            vec![true, true],
            vec![vec![1], vec![0]],
            "dag",
            "dag cycle",
        );
        assert_eq!(cycle.err(), Some(Failure::policy("dag", "dag cycle")));

        let self_loop =
            ParallelDagPlan::from_indexed_edges(vec![true], vec![vec![0]], "dag", "dag cycle");
        assert_eq!(self_loop.err(), Some(Failure::policy("dag", "dag cycle")));

        let bad_edge =
            ParallelDagPlan::from_indexed_edges(vec![true], vec![vec![5]], "dag", "dag cycle");
        assert_eq!(
            bad_edge.err(),
            Some(Failure::operational("dag", "out-of-range parallel DAG edge"))
        );
    }

    #[test]
    fn executes_independent_roots_concurrently_and_orders_dependents() {
        // 0, 1, 2 are independent roots; 3 is inactive and depends on 0 and 1;
        // 4 depends on 3 and 2.
        let plan = ParallelDagPlan::from_indexed_edges(
            vec![true, true, true, false, true],
            vec![vec![3], vec![3], vec![4], vec![4], vec![]],
            "dag",
            "cycle",
        )
        .unwrap();
        let barrier = Arc::new(Barrier::new(3));
        let mut committed = BTreeSet::new();
        run_parallel_dag(
            &plan,
            3,
            "dag",
            "panic",
            &mut committed,
            |done, idx| {
                if idx == 4 {
                    assert!(done.contains(&0) && done.contains(&1) && done.contains(&2));
                }
                Ok(())
            },
            |idx, ()| {
                if idx < 3 {
                    // Only completes if all three roots execute simultaneously.
                    barrier.wait();
                }
                Ok(idx)
            },
            |done, idx, val| {
                assert_eq!(idx, val);
                assert!(done.insert(idx));
                Ok(())
            },
        )
        .unwrap();
        assert_eq!(committed, BTreeSet::from([0, 1, 2, 4]));
    }

    #[test]
    fn preserves_earliest_index_failure_and_prunes_beaten_descendants() {
        // Graph on indices 0..5 with non-topological edges `3 -> 0` and
        // `3 -> 4`, plus independent roots `1` and `2`:
        // - `min_active_descendant` is `[0, 1, 2, 0, 4]`, so initial
        //   `state.ready` is `{(0, 3), (1, 1), (2, 2)}`.
        // - With `max_workers = 2`, the first worker to lock pops `(0, 3)`,
        //   releases the lock, and waits on `rx.recv()` inside `run(3)`. The
        //   second worker pops `(1, 1)` and fails inside `prepare(1)` while
        //   holding the scheduler mutex: it signals `tx` and records
        //   `first_error = (1, "failure-1")` before releasing the mutex, so
        //   `first_error` is already set before `run(3)` can lock to commit or
        //   fail and before the next `state.ready` loop prunes `(2, 2)`.
        //
        // Case A (`run(3)` succeeds, then `run(0)` fails):
        // - `propagate_dag_completions(3)` unlocks `0` (`min_desc = 0 <= 1`)
        //   while `dep_beaten` prunes `4` (`min_desc = 4 > 1`).
        // - `0` fails (`"failure-0"`), overwriting `(1, ...)` via `0 < 1`.
        let plan = ParallelDagPlan::from_indexed_edges(
            vec![true, true, true, true, true],
            vec![vec![], vec![], vec![], vec![0, 4], vec![]],
            "dag",
            "cycle",
        )
        .unwrap();

        let (tx_a, rx_a) = std::sync::mpsc::channel::<()>();
        let rx_a = Mutex::new(rx_a);
        let prepared_a: [AtomicUsize; 5] = std::array::from_fn(|_| AtomicUsize::new(0));
        let ran_a: [AtomicUsize; 5] = std::array::from_fn(|_| AtomicUsize::new(0));
        let mut shared = ();
        let err_a = run_parallel_dag(
            &plan,
            2,
            "dag",
            "panic",
            &mut shared,
            |_, idx| {
                prepared_a[idx].fetch_add(1, Ordering::Relaxed);
                if idx == 1 {
                    tx_a.send(()).unwrap();
                    return Err(Failure::policy("dag", "failure-1"));
                }
                Ok(())
            },
            |idx, ()| {
                ran_a[idx].fetch_add(1, Ordering::Relaxed);
                match idx {
                    3 => {
                        rx_a.lock().unwrap().recv().unwrap();
                        Ok(())
                    }
                    0 => Err(Failure::policy("dag", "failure-0")),
                    _ => Ok(()),
                }
            },
            |_, _, ()| Ok(()),
        )
        .unwrap_err();
        assert_eq!(err_a, Failure::policy("dag", "failure-0"));
        assert_eq!(prepared_a.map(|c| c.into_inner()), [1, 1, 0, 1, 0]);
        assert_eq!(ran_a.map(|c| c.into_inner()), [1, 0, 0, 1, 0]);

        // Case B (`run(3)` fails after `(1, "failure-1")` is recorded):
        // Failure at index `3 > 1` must NOT overwrite `(1, "failure-1")`.
        let (tx_b, rx_b) = std::sync::mpsc::channel::<()>();
        let rx_b = Mutex::new(rx_b);
        let prepared_b: [AtomicUsize; 5] = std::array::from_fn(|_| AtomicUsize::new(0));
        let ran_b: [AtomicUsize; 5] = std::array::from_fn(|_| AtomicUsize::new(0));
        let err_b = run_parallel_dag(
            &plan,
            2,
            "dag",
            "panic",
            &mut shared,
            |_, idx| {
                prepared_b[idx].fetch_add(1, Ordering::Relaxed);
                if idx == 1 {
                    tx_b.send(()).unwrap();
                    return Err(Failure::policy("dag", "failure-1"));
                }
                Ok(())
            },
            |idx, ()| {
                ran_b[idx].fetch_add(1, Ordering::Relaxed);
                if idx == 3 {
                    rx_b.lock().unwrap().recv().unwrap();
                    return Err(Failure::policy("dag", "failure-3"));
                }
                Ok(())
            },
            |_, _, ()| Ok(()),
        )
        .unwrap_err();
        assert_eq!(err_b, Failure::policy("dag", "failure-1"));
        assert_eq!(prepared_b.map(|c| c.into_inner()), [0, 1, 0, 1, 0]);
        assert_eq!(ran_b.map(|c| c.into_inner()), [0, 0, 0, 1, 0]);
    }

    #[test]
    fn worker_panic_unblocks_sibling_workers_without_deadlock() {
        let plan = ParallelDagPlan::from_indexed_edges(
            vec![true, true],
            vec![vec![1], vec![]],
            "dag",
            "cycle",
        )
        .unwrap();
        let mut shared = ();
        let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            run_parallel_dag(
                &plan,
                2,
                "dag",
                "worker panicked",
                &mut shared,
                |_, _| Ok(()),
                |idx, ()| {
                    if idx == 0 {
                        panic!("synthetic worker panic");
                    }
                    Ok(())
                },
                |_, _, ()| Ok(()),
            )
        }));
        assert!(res.is_err());
    }

    #[test]
    fn operational_failure_outranks_earlier_policy_rejection_in_both_orders() {
        let plan = ParallelDagPlan::from_indexed_edges(
            vec![true, true, true],
            vec![vec![], vec![], vec![]],
            "dag",
            "cycle",
        )
        .unwrap();
        let mut shared = ();

        // 1. Both 0 and 2 start `run` concurrently (via `start1`); `commit(0)`
        //    records `code == 1` under the scheduler lock first, then `run(2)`
        //    returns `code == 2`: operational failure at index 2 must win.
        let start1 = Arc::new(Barrier::new(2));
        let (tx1, rx1) = std::sync::mpsc::channel::<()>();
        let rx1 = Mutex::new(rx1);
        let err1 = run_parallel_dag(
            &plan,
            3,
            "dag",
            "panic",
            &mut shared,
            |_, _| Ok(()),
            |idx, ()| match idx {
                0 => {
                    start1.wait();
                    Ok(())
                }
                2 => {
                    start1.wait();
                    rx1.lock().unwrap().recv().unwrap();
                    Err(Failure::operational("sandbox", "sandbox-io-2"))
                }
                _ => Ok(()),
            },
            |_, idx, ()| {
                if idx == 0 {
                    tx1.send(()).unwrap();
                    return Err(Failure::policy("dag", "proof-rejected-0"));
                }
                Ok(())
            },
        )
        .unwrap_err();
        assert_eq!(err1, Failure::operational("sandbox", "sandbox-io-2"));

        // 2. Both 0 and 2 start `run` concurrently; `commit(2)` records
        //    `code == 2` first, then `run(0)` returns `code == 1`: operational
        //    failure at index 2 must not be overwritten by the lower-index
        //    policy rejection.
        let start2 = Arc::new(Barrier::new(2));
        let (tx2, rx2) = std::sync::mpsc::channel::<()>();
        let rx2 = Mutex::new(rx2);
        let err2 = run_parallel_dag(
            &plan,
            3,
            "dag",
            "panic",
            &mut shared,
            |_, _| Ok(()),
            |idx, ()| match idx {
                2 => {
                    start2.wait();
                    Ok(())
                }
                0 => {
                    start2.wait();
                    rx2.lock().unwrap().recv().unwrap();
                    Err(Failure::policy("dag", "proof-rejected-0"))
                }
                _ => Ok(()),
            },
            |_, idx, ()| {
                if idx == 2 {
                    tx2.send(()).unwrap();
                    return Err(Failure::operational("sandbox", "sandbox-io-2"));
                }
                Ok(())
            },
        )
        .unwrap_err();
        assert_eq!(err2, Failure::operational("sandbox", "sandbox-io-2"));

        // 3. Among two concurrent operational (`code == 2`) failures, smallest
        //    index wins even when index 2 records its failure first.
        let start3 = Arc::new(Barrier::new(2));
        let (tx3, rx3) = std::sync::mpsc::channel::<()>();
        let rx3 = Mutex::new(rx3);
        let err3 = run_parallel_dag(
            &plan,
            3,
            "dag",
            "panic",
            &mut shared,
            |_, _| Ok(()),
            |idx, ()| match idx {
                2 => {
                    start3.wait();
                    Ok(())
                }
                1 => {
                    start3.wait();
                    rx3.lock().unwrap().recv().unwrap();
                    Err(Failure::operational("sandbox", "sandbox-io-1"))
                }
                _ => Ok(()),
            },
            |_, idx, ()| {
                if idx == 2 {
                    tx3.send(()).unwrap();
                    return Err(Failure::operational("sandbox", "sandbox-io-2"));
                }
                Ok(())
            },
        )
        .unwrap_err();
        assert_eq!(err3, Failure::operational("sandbox", "sandbox-io-1"));
    }
}

#[cfg(test)]
mod default_lean_path_tests {
    use super::*;

    #[test]
    fn search_locations_honor_xdg_cache_home_home_and_fallbacks() {
        let (bases, elan) = lean_search_locations_for_platform(
            false,
            Some(OsStr::new("/tmp/xdg-cache")),
            Some(OsStr::new("/home/alice")),
        );
        assert_eq!(
            bases,
            [
                PathBuf::from("/tmp/xdg-cache/anneal/toolchain"),
                PathBuf::from("/home/alice/anneal/toolchain"),
            ]
        );
        assert_eq!(
            elan,
            PathBuf::from("/home/alice/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean")
        );

        // Per XDG spec (matching `dirs::cache_dir`), relative `XDG_CACHE_HOME`
        // values are ignored in favor of `$HOME/.cache`.
        for ignored_xdg in [None, Some(OsStr::new("")), Some(OsStr::new("relative/cache"))] {
            let (bases, elan) = lean_search_locations_for_platform(
                false,
                ignored_xdg,
                Some(OsStr::new("/home/bob")),
            );
            assert_eq!(
                bases,
                [
                    PathBuf::from("/home/bob/.cache/anneal/toolchain"),
                    PathBuf::from("/home/bob/anneal/toolchain"),
                ]
            );
            assert_eq!(
                elan,
                PathBuf::from("/home/bob/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean")
            );
        }

        // On macOS, `dirs::cache_dir` always resolves to `$HOME/Library/Caches`
        // regardless of `XDG_CACHE_HOME`.
        let (bases, elan) = lean_search_locations_for_platform(
            true,
            Some(OsStr::new("/tmp/xdg-ignored")),
            Some(OsStr::new("/Users/alice")),
        );
        assert_eq!(
            bases,
            [
                PathBuf::from("/Users/alice/Library/Caches/anneal/toolchain"),
                PathBuf::from("/Users/alice/anneal/toolchain"),
            ]
        );
        assert_eq!(
            elan,
            PathBuf::from("/Users/alice/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean")
        );

        for empty_or_none in [None, Some(OsStr::new(""))] {
            let (bases, elan) = lean_search_locations_for_platform(false, None, empty_or_none);
            assert_eq!(
                bases,
                [
                    PathBuf::from("/root/.cache/anneal/toolchain"),
                    PathBuf::from("/root/anneal/toolchain"),
                ]
            );
            assert_eq!(
                elan,
                PathBuf::from("/root/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean")
            );
        }

        let (bases, elan) = lean_search_locations_for_platform(
            false,
            Some(OsStr::new("/tmp/xdg-only")),
            Some(OsStr::new("")),
        );
        assert_eq!(
            bases,
            [
                PathBuf::from("/tmp/xdg-only/anneal/toolchain"),
                PathBuf::from("/root/anneal/toolchain"),
            ]
        );
        assert_eq!(
            elan,
            PathBuf::from("/root/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean")
        );
    }

    #[test]
    fn default_lean_path_for_platform_prefers_cache_then_home_then_elan() {
        let dir = tempfile::tempdir().unwrap();
        let xdg = dir.path().join("xdg");
        let home = dir.path().join("home");

        let xdg_lean = xdg.join("anneal/toolchain/v1/lean/bin/lean");
        let home_cache_lean = home.join(".cache/anneal/toolchain/v1/lean/bin/lean");
        let macos_cache_lean = home.join("Library/Caches/anneal/toolchain/v1/lean/bin/lean");
        let home_tc_lean = home.join("anneal/toolchain/v1/lean/bin/lean");
        let elan_lean = home.join(".elan/toolchains/leanprover--lean4---v4.34.1/bin/lean");

        for p in [&xdg_lean, &home_cache_lean, &macos_cache_lean, &home_tc_lean, &elan_lean] {
            fs::create_dir_all(p.parent().unwrap()).unwrap();
            fs::write(p, b"fake lean").unwrap();
        }

        // Linux / non-macOS precedence: XDG_CACHE_HOME -> $HOME/.cache ->
        // $HOME/anneal -> .elan.
        assert_eq!(
            default_lean_path_for_platform(false, Some(xdg.as_os_str()), Some(home.as_os_str())),
            xdg_lean
        );
        assert_eq!(
            default_lean_path_for_platform(false, None, Some(home.as_os_str())),
            home_cache_lean
        );
        assert_eq!(
            default_lean_path_for_platform(false, Some(OsStr::new("")), Some(home.as_os_str())),
            home_cache_lean
        );

        // macOS precedence: $HOME/Library/Caches (ignoring XDG_CACHE_HOME) ->
        // $HOME/anneal -> .elan.
        assert_eq!(
            default_lean_path_for_platform(true, Some(xdg.as_os_str()), Some(home.as_os_str())),
            macos_cache_lean
        );

        // Host wrapper matches the active target OS.
        let expected_host = if cfg!(target_os = "macos") { &macos_cache_lean } else { &xdg_lean };
        assert_eq!(
            &default_lean_path_from_env(Some(xdg.as_os_str()), Some(home.as_os_str())),
            expected_host
        );

        fs::remove_dir_all(home.join(".cache")).unwrap();
        fs::remove_dir_all(home.join("Library")).unwrap();
        assert_eq!(
            default_lean_path_for_platform(false, None, Some(home.as_os_str())),
            home_tc_lean
        );
        assert_eq!(
            default_lean_path_for_platform(true, Some(xdg.as_os_str()), Some(home.as_os_str())),
            home_tc_lean
        );

        fs::remove_dir_all(home.join("anneal")).unwrap();
        assert_eq!(default_lean_path_for_platform(false, None, Some(home.as_os_str())), elan_lean);
        assert_eq!(default_lean_path_for_platform(true, None, Some(home.as_os_str())), elan_lean);

        fs::remove_file(&elan_lean).unwrap();
        assert_eq!(default_lean_path_for_platform(false, None, Some(home.as_os_str())), elan_lean);
        assert_eq!(default_lean_path_for_platform(true, None, Some(home.as_os_str())), elan_lean);
    }

    #[test]
    fn sha256_bytes_produces_lowercase_hex_digest() {
        assert_eq!(
            sha256_bytes(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
        assert_eq!(
            sha256_bytes(b""),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
    }
}

#[cfg(test)]
mod unpinned_sysroot_tests {
    use super::*;

    fn edge_with(module: &str, is_exported: bool, is_meta: bool) -> ImportEdge {
        ImportEdge { module: module.to_string(), import_all: false, is_exported, is_meta }
    }

    fn edge(module: &str) -> ImportEdge {
        edge_with(module, true, false)
    }

    fn six_module_graph() -> BTreeMap<String, Vec<ImportEdge>> {
        BTreeMap::from([
            ("Init.Prelude".to_string(), Vec::new()),
            (
                "Init.Coe".to_string(),
                vec![edge("Init.Prelude"), edge_with("Init.Prelude", true, true)],
            ),
            ("Init.Notation".to_string(), vec![edge("Init.Coe")]),
            ("Init.Tactics".to_string(), vec![edge("Init.Notation")]),
            (
                "Init.SizeOf".to_string(),
                vec![edge("Init.Notation"), edge_with("Init.Tactics", false, false)],
            ),
            ("Init.Core".to_string(), vec![edge("Init.SizeOf"), edge("Init.Tactics")]),
        ])
    }

    #[test]
    fn foundation_closure_computes_exact_six_modules_and_excludes_libraries() {
        let mut graph = six_module_graph();
        graph.insert("Init.Data.BitVec.Basic".to_string(), vec![edge("Init.Core")]);
        graph.insert("Std.Data.HashMap".to_string(), vec![edge("Init.Data.BitVec.Basic")]);

        let closure = compute_unpinned_foundation_closure(&graph).unwrap();
        let expected: BTreeSet<String> =
            UNPINNED_FOUNDATION_MODULES.iter().map(|s| (*s).to_string()).collect();
        assert_eq!(closure, expected);
        assert!(!closure.contains("Init.Data.BitVec.Basic"));
        assert!(!closure.contains("Std.Data.HashMap"));
    }

    #[test]
    fn foundation_closure_rejects_missing_core_or_foundation_modules() {
        for missing in UNPINNED_FOUNDATION_MODULES {
            let mut graph = six_module_graph();
            graph.remove(missing);
            // Also drop incoming edges so failure comes from missing
            // foundation module, not dangling graph edge.
            for edges in graph.values_mut() {
                edges.retain(|e| e.module != missing);
            }
            let err = compute_unpinned_foundation_closure(&graph).unwrap_err();
            assert_eq!(err.code, 1, "{missing}: {err}");
            assert!(err.message.contains("missing required foundation module"), "{missing}: {err}");
        }
    }

    #[test]
    fn sysroot_guard_rejects_lean_lake_and_non_init_std_modules() {
        for forbidden in ["Lean", "Lean.Meta", "Lake", "Lake.Build", "InitFake", "User"] {
            let mut graph = six_module_graph();
            graph.insert(forbidden.to_string(), vec![edge("Init.Core")]);
            let err = compute_unpinned_foundation_closure(&graph).unwrap_err();
            assert_eq!(err.code, 1, "{forbidden}: {err}");
            assert!(err.message.contains("only Init and Std are permitted"), "{forbidden}: {err}");

            let mut edge_graph = six_module_graph();
            edge_graph.insert("Std.Wrapper".to_string(), vec![edge(forbidden)]);
            edge_graph.insert(forbidden.to_string(), Vec::new());
            let err = compute_unpinned_foundation_closure(&edge_graph).unwrap_err();
            assert_eq!(err.code, 1, "{forbidden} edge: {err}");
        }

        // Foundation closure itself cannot escape Init.* into Std.*.
        let mut std_in_core = six_module_graph();
        std_in_core.insert("Std.Helper".to_string(), vec![edge("Init.Prelude")]);
        std_in_core.get_mut("Init.Core").unwrap().push(edge("Std.Helper"));
        let err = compute_unpinned_foundation_closure(&std_in_core).unwrap_err();
        assert_eq!(err.code, 1);
        assert!(err.message.contains("exceeded Init.*"), "{err}");
    }

    #[cfg(unix)]
    #[test]
    fn scan_sysroot_package_roots_collects_dirs_oleans_and_symlinks() {
        use std::os::unix::fs::symlink;

        let dir = tempfile::tempdir().unwrap();
        let prefix = dir.path().join("sysroot");
        let lib_lean = prefix.join("lib/lean");
        fs::create_dir_all(lib_lean.join("Init")).unwrap();
        fs::write(lib_lean.join("Std.olean"), b"std").unwrap();
        fs::write(lib_lean.join("libInit.a"), b"archive").unwrap();
        fs::write(lib_lean.join("Ignored.ilean"), b"ilean").unwrap();
        fs::write(lib_lean.join("Ignored.olean.private"), b"priv").unwrap();

        let ext = dir.path().join("external");
        fs::create_dir_all(ext.join("LeanPkg")).unwrap();
        fs::write(ext.join("LakePkg.olean"), b"lake").unwrap();
        symlink(ext.join("LeanPkg"), lib_lean.join("Lean")).unwrap();
        symlink(ext.join("LakePkg.olean"), lib_lean.join("Lake.olean")).unwrap();

        let roots = scan_sysroot_package_roots(&prefix, "toolchain").unwrap();
        assert_eq!(
            roots,
            BTreeSet::from([
                "Init".to_string(),
                "Lake".to_string(),
                "Lean".to_string(),
                "Std".to_string(),
            ])
        );
    }

    #[test]
    fn hash_unpinned_sysroot_module_allows_absent_lean_and_hashes_present_parts() {
        let dir = tempfile::tempdir().unwrap();
        let prefix = dir.path();
        let lib_dir = prefix.join("lib/lean/Std/Data");
        fs::create_dir_all(&lib_dir).unwrap();
        for (suffix, bytes) in [
            ("olean", b"olean bytes" as &[u8]),
            ("olean.server", b"server bytes"),
            ("olean.private", b"private bytes"),
            ("ir.sig", b"ir sig bytes"),
            ("ir", b"ir bytes"),
        ] {
            fs::write(lib_dir.join(format!("HashMap.{suffix}")), bytes).unwrap();
        }

        let absent = hash_unpinned_sysroot_module(prefix, "Std.Data.HashMap", "sysroot").unwrap();
        assert_eq!(absent.source_sha256, None);
        assert_eq!(absent.artifacts.olean_parts.len(), 3);
        assert_eq!(absent.artifacts.ir_parts.len(), 2);
        assert_eq!(absent.part_hashes.len(), 5);
        assert_eq!(absent.part_hashes[0].0, "HashMap.olean");
        assert_eq!(absent.part_hashes[0].1, sha256_bytes(b"olean bytes"));

        // Missing primary .olean must fail closed.
        fs::remove_file(lib_dir.join("HashMap.olean")).unwrap();
        assert!(hash_unpinned_sysroot_module(prefix, "Std.Data.HashMap", "sysroot").is_err());

        // Present .lean source is hashed.
        fs::write(lib_dir.join("HashMap.olean"), b"olean bytes").unwrap();
        let src_dir = prefix.join("src/lean/Std/Data");
        fs::create_dir_all(&src_dir).unwrap();
        fs::write(src_dir.join("HashMap.lean"), b"source bytes").unwrap();
        let present = hash_unpinned_sysroot_module(prefix, "Std.Data.HashMap", "sysroot").unwrap();
        assert_eq!(present.source_sha256, Some(sha256_bytes(b"source bytes")));
    }

    #[test]
    fn transitive_import_closure_follows_private_and_meta_edges() {
        let graph = BTreeMap::from([
            ("A".to_string(), vec![edge_with("B", false, false), edge_with("C", true, true)]),
            ("B".to_string(), vec![edge("D")]),
            ("C".to_string(), Vec::new()),
            ("D".to_string(), Vec::new()),
            ("Unrelated".to_string(), vec![edge("D")]),
        ]);
        let closure = transitive_import_closure(&graph, &[edge("A")]);
        assert_eq!(
            closure,
            BTreeSet::from(["A".to_string(), "B".to_string(), "C".to_string(), "D".to_string(),])
        );
    }

    #[cfg(unix)]
    #[test]
    fn safe_regular_file_primitives_reject_fifos_without_blocking() {
        use std::{os::unix::fs::symlink, process::Command};

        let dir = tempfile::tempdir().unwrap();
        let fifo = dir.path().join("pipe");
        let status = Command::new("mkfifo").arg(&fifo).status().unwrap();
        assert!(status.success());

        let fifo_link = dir.path().join("pipe_link");
        symlink(&fifo, &fifo_link).unwrap();

        let err_strict = read_regular_file_strict(&fifo, None, "test").unwrap_err();
        assert_eq!(err_strict.code, 1);

        let err_deref = read_regular_file_deref(&fifo_link, "test").unwrap_err();
        assert_eq!(err_deref.code, 1);

        let regular_file = dir.path().join("regular.txt");
        fs::write(&regular_file, b"hello").unwrap();
        let regular_link = dir.path().join("regular_link.txt");
        symlink(&regular_file, &regular_link).unwrap();

        assert!(open_regular_nofollow_nonblock(&regular_link, "test").is_err());
        assert!(read_regular_file_strict(&regular_link, None, "test").is_err());
        let (bytes, sha) = read_regular_file_deref(&regular_link, "test").unwrap();
        assert_eq!(bytes, b"hello");
        assert_eq!(sha, sha256_bytes(b"hello"));

        let unreadable = dir.path().join("unreadable.txt");
        fs::write(&unreadable, b"secret").unwrap();
        SafeFs::set_mode(&unreadable, 0o000, "test").unwrap();
        // Verify unreadable regular files fail as operational (code 2), not
        // policy rejections (code 1), unless running as root with DAC_OVERRIDE.
        if fs::File::open(&unreadable).is_err() {
            let err_unreadable = read_regular_file_strict(&unreadable, None, "test").unwrap_err();
            assert_eq!(err_unreadable.code, 2);
        }
        SafeFs::set_mode(&unreadable, 0o600, "test").unwrap();
    }
}
