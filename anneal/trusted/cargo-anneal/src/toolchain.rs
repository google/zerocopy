// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Defines the shared Lean 4.34.1 toolchain lock schemas, artifact records,
//! digest and path validators, and deterministic topological ordering.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::{Component, Path, PathBuf},
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
