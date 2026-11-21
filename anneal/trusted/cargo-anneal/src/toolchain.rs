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
    fs,
    num::NonZero,
    path::{Component, Path, PathBuf},
    sync::{Condvar, Mutex},
};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

/// Represents a JSON value at the `TrustedBoundary.lean` IPC boundary.
pub type Json = serde_json::Value;

/// Names the pinned Lean 4 toolchain identifier required by
/// `foundation-lock.json` and `library-lock.json`.
pub const TOOLCHAIN: &str = "leanprover/lean4:v4.34.1";

/// Lists the `.olean` artifact companion suffixes passed in the first array of
/// `Lean.ImportArtifacts`.
pub const OLEAN_PARTS: [&str; 3] = ["olean", "olean.server", "olean.private"];

/// Lists the `.ir` artifact companion suffixes passed in the second array of
/// `Lean.ImportArtifacts`.
pub const IR_PARTS: [&str; 2] = ["ir.sig", "ir"];

/// Lists all five compiled Lean artifact companion suffixes tracked by
/// `foundation-lock.json`, `library-lock.json`, and module compilation.
pub const PARTS: [&str; 5] = ["olean", "olean.server", "olean.private", "ir.sig", "ir"];

/// Lists the pinned SHA-256 digests of the official Lean 4.34.1 `bin/lean`
/// binaries from `trusted/lean/foundation-lock.json`. They cover only that
/// executable file, not the Lean shared libraries it loads.
pub const LOCKED_LEAN_SHA256: [&str; 4] = [
    "79fb1d26fa5a39385d59fdc48a711a14b0710ca6480271acce99b4d177cea085",
    "1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554",
    "998f0cc2a5a754cc66df1f33b85e1447528737ff15012db35d8c501754b02f1e",
    "e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550",
];

/// Names the pinned SHA-256 manifest digest of all
/// `<prefix>/lib/lean/{Init,Std,Lean}*` `.olean`, `.olean.server`, and
/// `.olean.private` artifacts in the pinned Lean 4.34.1 toolchain, computed
/// over sorted `"{rel_path}:{sha256}\n"` lines.
///
/// Verifying this digest before `"correspondence-audit"` ensures that every
/// `.sysrootFoundation` module loaded by `vendor/lean-miri` is
/// cryptographically authenticated to the pinned toolchain rather than checked
/// only by path existence.
///
/// Target verification does not check this manifest. Of these sysroot modules,
/// it hashes only those in `foundation-lock.json` and the imported
/// `library-lock.json` modules.
pub const LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256: &str =
    "2fa0ec692ae74051072ed105a66054843dcb711eb702bb64dc7947b96ea4fcdf";

/// Represents a structured audit or verification failure distinguishing
/// reported frontend/source or policy rejections (`code == 1`) from
/// operational or environment failures (`code == 2`).
///
/// A rejection does not establish that the requested proposition is false.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("{message}")]
pub struct Failure {
    /// Holds the process exit code (`1` for rejection, `2` for operational
    /// failure).
    pub code: i32,
    /// Names the phase in which the failure occurred.
    pub phase: String,
    /// Contains the human-readable diagnostic message.
    pub message: String,
}

impl Failure {
    /// Construct a new [`Failure`].
    pub fn new(code: i32, phase: impl Into<String>, message: impl Into<String>) -> Self {
        Self { code, phase: phase.into(), message: message.into() }
    }

    /// Construct a policy-rejection [`Failure`] (`code == 1`).
    pub fn policy(phase: impl Into<String>, message: impl Into<String>) -> Self {
        Self::new(1, phase, message)
    }

    /// Construct an operational or environment [`Failure`] (`code == 2`).
    pub fn operational(phase: impl Into<String>, message: impl Into<String>) -> Self {
        Self::new(2, phase, message)
    }
}

/// Holds the validated artifact companion paths for a single compiled Lean
/// module.
///
/// `Lean.ImportArtifacts` expects two path arrays per module:
///
/// 1. `olean_parts`: `[.olean, .olean.server?, .olean.private?]` (always
///    non-empty; `.olean` is mandatory).
/// 2. `ir_parts`: `[.ir.sig?, .ir?]`.
///
/// Representing these two groups as named fields rather than `Vec<Vec<String>>`
/// makes malformed artifact-group counts unrepresentable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleArtifacts {
    /// Holds the non-empty `.olean` companion group (`OLEAN_PARTS`).
    pub olean_parts: Vec<String>,
    /// Holds the optional `.ir` companion group (`IR_PARTS`).
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
        let olean_parts = OLEAN_PARTS.iter().filter_map(|p| available.get(*p).cloned()).collect();
        let ir_parts = IR_PARTS.iter().filter_map(|p| available.get(*p).cloned()).collect();
        Ok(Self { olean_parts, ir_parts })
    }

    /// Convert to the two-element array representation expected by
    /// `Lean.ImportArtifacts` in `--setup` and `TrustedBoundary.lean`.
    pub fn to_wire(&self) -> [&[String]; 2] {
        [&self.olean_parts, &self.ir_parts]
    }
}

/// Represents a single `import` edge in a Lean module header, matching Lean's
/// `Import` JSON encoding (`Lean.Import`).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct ImportEdge {
    /// Names the imported module (for example `"Init.Core"` or
    /// `"Trusted.MirAst"`).
    pub module: String,
    /// Indicates whether `import all` was used (always `false` in admitted
    /// modules).
    pub import_all: bool,
    /// Indicates whether the import is exported (`true` for standard `import`).
    pub is_exported: bool,
    /// Indicates whether `meta import` was used (always `false` in admitted
    /// modules).
    pub is_meta: bool,
}

/// Represents a header response entry returned by `TrustedBoundary.lean`
/// `"headers"` and `"preflight"` modes.
#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PreflightHeader {
    /// Names the inspected module.
    pub module: String,
    /// Lists the module's header imports in source order.
    pub imports: Vec<ImportEdge>,
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
/// `foundation-lock.json` and `library-lock.json`.
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

/// Deserializes `trusted/audit/library-lock.json` (authenticated installed
/// modules that remain logically untrusted and undergo kernel replay in
/// `targetAudit`).
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct LibraryLock {
    pub schema: i64,
    pub toolchain: String,
    pub modules: BTreeMap<String, FoundationModuleRecord>,
    pub graph: BTreeMap<String, Vec<ImportEdge>>,
}

/// Stage-local compiled inspector and its thin import runner.
#[derive(Debug, Clone)]
pub(crate) struct CompiledInspectorPaths {
    pub(crate) lib_dir: PathBuf,
    pub(crate) runner: PathBuf,
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
    pub(crate) inspector_sha256: String,
    pub(crate) lean_sha256: String,
    pub(crate) compiled_inspector: Option<CompiledInspectorPaths>,
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

/// Resolve the default pinned Lean 4.34.1 binary path when none is explicitly
/// provided, selecting a candidate binary whose SHA-256 matches
/// [`LOCKED_LEAN_SHA256`].
pub fn default_lean_path() -> PathBuf {
    let home = dirs::home_dir().unwrap_or_else(|| PathBuf::from("/root"));
    let mut candidate_paths = Vec::new();
    for base in dirs::cache_dir().into_iter().chain(std::iter::once(home.clone())) {
        let tc_base = base.join("anneal/toolchain");
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
    let elan_lean = home.join(".elan/toolchains/leanprover--lean4---v4.34.1/bin/lean");
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

/// Verify that `path` exists and is a regular file (not a symlink, directory,
/// FIFO, or device node) using `symlink_metadata` so symlinks are never
/// silently followed.
pub fn regular(path: &Path, phase: &str) -> Result<(), Failure> {
    let meta = fs::symlink_metadata(path)
        .map_err(|e| Failure::new(2, phase, format!("cannot inspect {}: {e}", path.display())))?;
    if meta.file_type().is_symlink() || !meta.file_type().is_file() {
        return Err(Failure::new(1, phase, format!("expected a regular file: {}", path.display())));
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
    let bytes = fs::read(path)
        .map_err(|e| Failure::new(2, phase, format!("cannot read {}: {e}", path.display())))?;
    Ok(sha256_bytes(&bytes))
}

/// Copy a regular source file `src` to `dst`, creating parent directories as
/// needed, and return the SHA-256 digest of the copied bytes.
pub fn stage_regular_file(src: &Path, dst: &Path, phase: &str) -> Result<String, Failure> {
    regular(src, phase)?;
    let bytes = fs::read(src)
        .map_err(|e| Failure::new(2, phase, format!("cannot read {}: {e}", src.display())))?;
    if let Some(parent) = dst.parent() {
        fs::create_dir_all(parent).map_err(|e| {
            Failure::new(2, phase, format!("cannot create {}: {e}", parent.display()))
        })?;
    }
    fs::write(dst, &bytes)
        .map_err(|e| Failure::new(2, phase, format!("cannot write {}: {e}", dst.display())))?;
    Ok(sha256_bytes(&bytes))
}

/// Return `true` if `s` is a 64-character ASCII hex digest.
pub fn is_sha256_hex(s: &str) -> bool {
    s.len() == 64 && s.bytes().all(|b| b.is_ascii_hexdigit())
}

/// Return `true` if `s` is a valid ASCII Lean module identifier component.
#[doc(hidden)]
pub fn is_lean_ident(s: &str) -> bool {
    let mut chars = s.chars();
    chars.next().is_some_and(|first| first.is_ascii_alphabetic())
        && chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// Return `true` if `rel` consists exclusively of normal path components (no
/// `/`, `.`, or `..`).
pub fn is_clean_relative_path(rel: &str) -> bool {
    let mut comps = Path::new(rel).components();
    comps.clone().next().is_some() && comps.all(|c| matches!(c, Component::Normal(_)))
}

/// Topologically sort the module set `pending` according to `imports_map`,
/// returning a policy rejection (`code == 1`) with `cycle_msg` if `pending`
/// contains an import cycle.
///
/// Emit each ready layer in sorted order. Imports outside `pending` are assumed
/// to be available. Use iteration so deep import chains do not consume one Rust
/// stack frame per module.
pub fn topo_sort_modules(
    mut pending: BTreeSet<String>,
    imports_map: &BTreeMap<String, Vec<ImportEdge>>,
    cycle_msg: &str,
) -> Result<Vec<String>, Failure> {
    let mut order = Vec::with_capacity(pending.len());
    while !pending.is_empty() {
        // Snapshot the whole ready layer before removing modules so newly
        // unlocked modules cannot interleave with its sorted order.
        let ready: Vec<_> = pending
            .iter()
            .filter(|module| {
                imports_map[*module].iter().all(|edge| !pending.contains(&edge.module))
            })
            .cloned()
            .collect();
        if ready.is_empty() {
            return Err(Failure::policy("preflight", cycle_msg));
        }
        for module in ready {
            pending.remove(&module);
            order.push(module);
        }
    }
    Ok(order)
}

/// Return a bounded worker count based on available host parallelism, capped
/// at `cap` and never below `1`.
#[doc(hidden)]
pub fn default_compile_workers(cap: usize) -> usize {
    std::thread::available_parallelism()
        .map(NonZero::get)
        .unwrap_or(1)
        .min(cap.max(1))
        .max(1)
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
            return Err(Failure::operational(
                cycle_phase,
                "mismatched parallel DAG dimension",
            ));
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
        Ok(Self {
            active,
            in_degree,
            dependents: normalized,
            min_active_descendant,
        })
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

fn record_earliest_dag_error(
    slot: &mut Option<(usize, Failure)>,
    entry_idx: usize,
    err: Failure,
) {
    if slot.as_ref().is_none_or(|(best_idx, _)| entry_idx < *best_idx) {
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
/// threads while preserving deterministic earliest-index failure reporting.
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
                init_state
                    .ready
                    .insert((plan.min_active_descendant[idx], idx));
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
                            Err(err) => record_earliest_dag_error(
                                &mut state.first_error,
                                entry_idx,
                                err,
                            ),
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

        let self_loop = ParallelDagPlan::from_indexed_edges(
            vec![true],
            vec![vec![0]],
            "dag",
            "dag cycle",
        );
        assert_eq!(self_loop.err(), Some(Failure::policy("dag", "dag cycle")));

        let bad_edge = ParallelDagPlan::from_indexed_edges(
            vec![true],
            vec![vec![5]],
            "dag",
            "dag cycle",
        );
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
}
