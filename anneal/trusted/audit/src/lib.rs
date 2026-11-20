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
//! Together, `trusted/audit` and `TrustedBoundary.lean` enforce six
//! repository-level invariants across a five-stage pipeline:
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
//! 6. **Pinned `vendor/lean-miri/` closure verification
//!    ([`verify_upstream_pin`], [`Checker::verify_and_stage_miri_entries`],
//!    [`InspectorRequest::CorrespondenceAudit`]):** When `vendor/lean-miri/` is
//!    present, `UPSTREAM_PIN.json` and every vendored file are verified against
//!    TCB-locked SHA-256 digests, the sysroot `Init`/`Std`/`Lean` `.olean`
//!    manifest is authenticated before compilation, the 160-module
//!    `ExecutionMachine` slice is restored from a digest-gated cache outside
//!    the checkout or compiled cold inside a per-module OS-level sandbox
//!    (`bwrap --unshare-all` with an empty `tmpfs` root, read-only toolchain
//!    and staged inputs, zero network/credentials, and writes confined strictly
//!    to an isolated output directory) with write-after-verify `.olean` digest
//!    and unexpected-file checking before staging, and the loaded closure is
//!    checked for namespace isolation, trust-tier separation, and `.vendorMiri`
//!    axiom/`unsafe`/`sorryAx`/compiler-primitive absence, kernel-replayed from
//!    scratch onto the authenticated sysroot base on every run (cold compile
//!    and cache hit alike), and checked for execution-cone freedom from
//!    `unsafe`, `partial`, `.vendorMiri` `opaque`, and unapproved axioms
//!    (without source-preflighting vendor modules).

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::env;
use std::ffi::OsString;
use std::fs;
use std::io;
#[cfg(unix)]
use std::os::unix::fs::{DirBuilderExt, PermissionsExt};
use std::path::{Component, Path, PathBuf};
use std::process::{Command, Output};

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
pub const PARTS: [&str; 5] = ["olean", "olean.server", "olean.private", "ir.sig", "ir"];

/// Pinned upstream `proofs-rs/lean-miri` commit hash required by
/// `vendor/lean-miri/UPSTREAM_PIN.json`.
pub const LOCKED_MIRI_COMMIT: &str = "c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a";

/// Pinned SHA-256 digest of `vendor/lean-miri/UPSTREAM_PIN.json` so that any
/// change to `UPSTREAM_PIN.json` requires a corresponding TCB diff inside
/// `trusted/audit/`.
pub const LOCKED_UPSTREAM_PIN_SHA256: &str =
    "b629a9b4c3fd184b20b791d34621a9f6aa1518ed9b164e42561b4eb688157271";

/// Pinned SHA-256 manifest digest of all `<prefix>/lib/lean/{Init,Std,Lean}*`
/// `.olean`, `.olean.server`, and `.olean.private` artifacts in the pinned Lean
/// 4.34.1 toolchain, computed over sorted `"{rel_path}:{sha256}\n"` lines.
///
/// Verifying this digest before `"correspondence-audit"` ensures that every
/// `.sysrootFoundation` module loaded by `vendor/lean-miri` is
/// cryptographically authenticated to the pinned toolchain rather than checked
/// only by path existence.
pub const LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256: &str =
    "2fa0ec692ae74051072ed105a66054843dcb711eb702bb64dc7947b96ea4fcdf";

/// Exact set of `vendor/lean-miri` files that must each carry one
/// consumer-side patch record in `UPSTREAM_PIN.json`.
pub const LOCKED_PATCHED_MIRI_FILES: &[&str] = &[
    "Miri/Interpreter/Call.lean",
    "Miri/Interpreter/Cast.lean",
    "Miri/Interpreter/ExecutionCalls.lean",
    "Miri/Interpreter/ExecutionCast.lean",
    "Miri/Interpreter/ExecutionMachine.lean",
    "Miri/Interpreter/LocalAccess.lean",
    "Miri/Interpreter/MachineHooks.lean",
    "Miri/Interpreter/OperandMachine.lean",
    "Miri/Interpreter/Place.lean",
    "Miri/Interpreter/PlaceMachine.lean",
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
    pub fn new(code: i32, phase: impl Into<String>, message: impl Into<String>) -> Self {
        Self {
            code,
            phase: phase.into(),
            message: message.into(),
        }
    }

    /// Construct a TCB policy-rejection [`Failure`] (`code == 1`).
    pub fn policy(phase: impl Into<String>, message: impl Into<String>) -> Self {
        Self::new(1, phase, message)
    }

    /// Construct an operational or environment [`Failure`] (`code == 2`).
    pub fn operational(phase: impl Into<String>, message: impl Into<String>) -> Self {
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
/// Encoding the inspector phases as a sum type ensures that `"preflight"`
/// is always invoked with a source list against the foundation graph,
/// `"audit"` is always invoked with the full module inventory and validated
/// [`TrustTier`] map, and `"correspondence-audit"` is always invoked with the
/// complete correspondence-audit module sets and search path.
#[derive(Debug, Clone)]
pub enum InspectorRequest {
    /// Phase 1 (`"preflight"`): parse `(module_name, staged_path)` pairs
    /// against the locked foundation parser environment before any elaboration.
    Preflight { sources: Vec<(String, PathBuf)> },
    /// Phase 2 (`"audit"`): load compiled `.olean`s with `loadExts := false`,
    /// verify module-level trust tiers and namespace hygiene, and replay all
    /// non-foundation constants through the Lean kernel.
    Audit {
        trusted: Vec<String>,
        theory: Vec<String>,
        module_tiers: BTreeMap<String, TrustTier>,
    },
    /// Phase 3 (`"correspondence-audit"`): load the pinned `lean-miri` closure
    /// `.olean`s with `loadExts := false`, verify 5-role module provenance,
    /// `.vendorMiri` inventory integrity and axiom/`unsafe`/`sorryAx`/
    /// compiler-primitive absence, kernel-replay every non-`isPartial`
    /// `.vendorMiri` declaration onto the authenticated sysroot base on every
    /// run (cold compile and cache hit alike), and verify constant-cone purity
    /// for `Miri.Interpreter.ExecutionMachine`. `corr_trusted` and
    /// `corr_theory` are currently passed empty by `run_miri_closure` until
    /// `trusted/correspondence/` and `correspondence/` are added and wired into
    /// directory scanning.
    CorrespondenceAudit {
        search_path: Vec<PathBuf>,
        trusted: Vec<String>,
        corr_trusted: Vec<String>,
        theory: Vec<String>,
        corr_theory: Vec<String>,
        vendor_miri: Vec<String>,
        module_tiers: BTreeMap<String, TrustTier>,
    },
}

impl InspectorRequest {
    /// Return the wire mode tag (`"preflight"`, `"audit"`, or
    /// `"correspondence-audit"`).
    pub const fn mode(&self) -> &'static str {
        match self {
            Self::Preflight { .. } => "preflight",
            Self::Audit { .. } => "audit",
            Self::CorrespondenceAudit { .. } => "correspondence-audit",
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
    let meta = fs::symlink_metadata(path)
        .map_err(|e| Failure::new(2, phase, format!("cannot inspect {}: {e}", path.display())))?;
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
    let bytes = fs::read(path)
        .map_err(|e| Failure::new(2, phase, format!("cannot read {}: {e}", path.display())))?;
    Ok(sha256_bytes(&bytes))
}

/// Copy a regular source file `src` to `dst`, creating parent directories as
/// needed, and return the SHA-256 digest of the copied bytes.
fn stage_regular_file(src: &Path, dst: &Path, phase: &str) -> Result<String, Failure> {
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

/// Normalize `.` and `..` path components purely lexically without consulting
/// the filesystem.
fn lexical_normalize(path: &Path) -> PathBuf {
    let mut normalized = PathBuf::new();
    for comp in path.components() {
        match comp {
            Component::Prefix(prefix) => normalized.push(prefix.as_os_str()),
            Component::RootDir => normalized.push(comp.as_os_str()),
            Component::CurDir => {}
            Component::ParentDir => {
                if matches!(
                    normalized.components().next_back(),
                    Some(Component::Normal(_))
                ) {
                    normalized.pop();
                } else if !normalized.has_root() {
                    normalized.push(comp.as_os_str());
                }
            }
            Component::Normal(seg) => normalized.push(seg),
        }
    }
    normalized
}

/// Resolve an absolute path by following symlinks on every existing prefix
/// component (including dangling symlinks) while preserving non-existent
/// trailing components and normalizing `.`/`..`. Rejects any symlink located
/// inside `forbidden_root`.
fn resolve_path_for_containment(
    abs_path: &Path,
    forbidden_root: &Path,
    phase: &str,
) -> Result<PathBuf, Failure> {
    const MAX_SYMLINK_HOPS: usize = 40;
    let mut remaining_hops = MAX_SYMLINK_HOPS;
    let mut resolved = PathBuf::new();
    let mut queue: VecDeque<OsString> = VecDeque::new();
    let mut saw_root = false;

    for comp in abs_path.components() {
        match comp {
            Component::Prefix(prefix) => resolved.push(prefix.as_os_str()),
            Component::RootDir => {
                resolved.push(comp.as_os_str());
                saw_root = true;
            }
            Component::CurDir => {}
            Component::ParentDir => queue.push_back(OsString::from("..")),
            Component::Normal(seg) => queue.push_back(seg.to_os_string()),
        }
    }
    if !saw_root {
        return Err(Failure::operational(
            phase,
            format!("expected absolute path, got {}", abs_path.display()),
        ));
    }

    while let Some(seg) = queue.pop_front() {
        if seg == "." {
            continue;
        }
        if seg == ".." {
            if matches!(
                resolved.components().next_back(),
                Some(Component::Normal(_))
            ) {
                resolved.pop();
            }
            continue;
        }
        resolved.push(&seg);
        match fs::symlink_metadata(&resolved) {
            Ok(meta) if meta.file_type().is_symlink() => {
                if resolved.starts_with(forbidden_root) {
                    return Err(Failure::policy(
                        phase,
                        format!(
                            "Miri .olean cache directory must not traverse a symlink inside the repository checkout {}: {}",
                            forbidden_root.display(),
                            abs_path.display()
                        ),
                    ));
                }
                if remaining_hops == 0 {
                    return Err(Failure::policy(
                        phase,
                        format!(
                            "symlink loop while resolving Miri .olean cache directory: {}",
                            abs_path.display()
                        ),
                    ));
                }
                remaining_hops -= 1;
                let target = fs::read_link(&resolved).map_err(|e| {
                    Failure::operational(
                        phase,
                        format!("cannot read symlink {}: {e}", resolved.display()),
                    )
                })?;
                if target.is_absolute() {
                    resolved.clear();
                } else {
                    resolved.pop();
                }
                let mut target_segs = Vec::new();
                for comp in target.components() {
                    match comp {
                        Component::Prefix(prefix) => resolved.push(prefix.as_os_str()),
                        Component::RootDir => resolved.push(comp.as_os_str()),
                        Component::CurDir => {}
                        Component::ParentDir => target_segs.push(OsString::from("..")),
                        Component::Normal(s) => target_segs.push(s.to_os_string()),
                    }
                }
                for s in target_segs.into_iter().rev() {
                    queue.push_front(s);
                }
            }
            Ok(_) => {}
            Err(e)
                if matches!(
                    e.kind(),
                    io::ErrorKind::NotFound | io::ErrorKind::NotADirectory
                ) => {}
            Err(e) => {
                return Err(Failure::operational(
                    phase,
                    format!("cannot inspect {}: {e}", resolved.display()),
                ));
            }
        }
    }
    Ok(resolved)
}

/// Reject any `--miri-cache-dir` / `ANNEAL_MIRI_CACHE_DIR` path that resides
/// inside (or equals) the repository checkout `checkout`, checking both
/// lexical containment and symlink-resolved containment (including
/// non-existent leaf directories and dangling symlinks).
///
/// Keeping the Miri `.olean` cache outside the checkout prevents a PR from
/// committing pre-built `.olean` files inside the repository to satisfy cache
/// hits without compiling the pinned sources.
pub fn ensure_miri_cache_outside_checkout(
    checkout: &Path,
    cache_dir: &Path,
) -> Result<(), Failure> {
    let phase = "miri-pin";
    let canonical_checkout = fs::canonicalize(checkout).map_err(|e| {
        Failure::operational(
            phase,
            format!("cannot canonicalize checkout {}: {e}", checkout.display()),
        )
    })?;
    let abs_cache = if cache_dir.is_absolute() {
        cache_dir.to_path_buf()
    } else {
        env::current_dir()
            .map_err(|e| Failure::operational(phase, format!("cannot read cwd: {e}")))?
            .join(cache_dir)
    };
    let lexical_cache = lexical_normalize(&abs_cache);
    let resolved_cache = resolve_path_for_containment(&abs_cache, &canonical_checkout, phase)?;
    if lexical_cache.starts_with(&canonical_checkout)
        || resolved_cache.starts_with(&canonical_checkout)
    {
        return Err(Failure::policy(
            phase,
            format!(
                "Miri .olean cache directory must reside outside the repository checkout {}: {}",
                canonical_checkout.display(),
                cache_dir.display()
            ),
        ));
    }
    Ok(())
}

/// Validate that `cache_dir` and every path component of `rel_path` under
/// `cache_dir` is free of symlinks, returning the validated destination path
/// and creating missing intermediate directories without following links.
fn prepare_nosymlink_cache_path(
    cache_dir: &Path,
    rel_path: &str,
    create_dirs: bool,
    phase: &str,
) -> Result<PathBuf, Failure> {
    if !is_clean_relative_path(rel_path) {
        return Err(Failure::policy(
            phase,
            format!("invalid relative cache path: {rel_path}"),
        ));
    }
    // Strip any trailing slash so `symlink_metadata` inspects a symlinked
    // `cache_dir` entry itself rather than dereferencing it under POSIX.
    let cache_dir_buf: PathBuf = cache_dir.components().collect();
    let cache_dir = cache_dir_buf.as_path();
    match fs::symlink_metadata(cache_dir) {
        Ok(meta) => {
            if !meta.file_type().is_dir() {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "cache root must be a regular directory (not a symlink or file): {}",
                        cache_dir.display()
                    ),
                ));
            }
        }
        Err(e) if e.kind() == io::ErrorKind::NotFound => {
            if create_dirs {
                fs::create_dir_all(cache_dir).map_err(|err| {
                    Failure::operational(
                        phase,
                        format!("cannot create cache root {}: {err}", cache_dir.display()),
                    )
                })?;
                let meta = fs::symlink_metadata(cache_dir).map_err(|err| {
                    Failure::operational(
                        phase,
                        format!("cannot stat cache root {}: {err}", cache_dir.display()),
                    )
                })?;
                if !meta.file_type().is_dir() {
                    return Err(Failure::policy(
                        phase,
                        format!(
                            "cache root is not a regular directory: {}",
                            cache_dir.display()
                        ),
                    ));
                }
            } else {
                return Ok(cache_dir.join(rel_path));
            }
        }
        Err(e) => {
            return Err(Failure::operational(
                phase,
                format!("cannot stat cache root {}: {e}", cache_dir.display()),
            ));
        }
    }
    let rel = Path::new(rel_path);
    let mut cur = cache_dir.to_path_buf();
    if let Some(parent) = rel.parent() {
        for comp in parent.components() {
            cur.push(comp);
            match fs::symlink_metadata(&cur) {
                Ok(meta) => {
                    if !meta.file_type().is_dir() {
                        return Err(Failure::policy(
                            phase,
                            format!(
                                "symlink or non-directory forbidden in cache path: {}",
                                cur.display()
                            ),
                        ));
                    }
                }
                Err(e) if e.kind() == io::ErrorKind::NotFound => {
                    if create_dirs {
                        fs::create_dir(&cur).map_err(|err| {
                            Failure::operational(
                                phase,
                                format!("cannot create cache directory {}: {err}", cur.display()),
                            )
                        })?;
                    } else {
                        return Ok(cache_dir.join(rel_path));
                    }
                }
                Err(e) => {
                    return Err(Failure::operational(
                        phase,
                        format!("cannot stat cache directory {}: {e}", cur.display()),
                    ));
                }
            }
        }
    }
    let dst = cache_dir.join(rel_path);
    match fs::symlink_metadata(&dst) {
        Ok(meta) => {
            if !meta.file_type().is_file() {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "symlink or non-regular file forbidden at cache entry: {}",
                        dst.display()
                    ),
                ));
            }
        }
        Err(e) if e.kind() == io::ErrorKind::NotFound => {}
        Err(e) => {
            return Err(Failure::operational(
                phase,
                format!("cannot stat cache entry {}: {e}", dst.display()),
            ));
        }
    }
    Ok(dst)
}

/// Write a compiled artifact `src` into `cache_dir/rel_path` after rejecting
/// symlinks at every path component and creating a fresh regular file with
/// `create_new(true)`.
fn write_cache_file(
    src: &Path,
    cache_dir: &Path,
    rel_path: &str,
    phase: &str,
) -> Result<(), Failure> {
    regular(src, phase)?;
    let bytes = fs::read(src)
        .map_err(|e| Failure::operational(phase, format!("cannot read {}: {e}", src.display())))?;
    let dst = prepare_nosymlink_cache_path(cache_dir, rel_path, true, phase)?;
    if fs::symlink_metadata(&dst).is_ok() {
        fs::remove_file(&dst).map_err(|e| {
            Failure::operational(
                phase,
                format!("cannot replace cache entry {}: {e}", dst.display()),
            )
        })?;
    }
    let mut file = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&dst)
        .map_err(|e| {
            Failure::operational(
                phase,
                format!("cannot create cache entry {}: {e}", dst.display()),
            )
        })?;
    io::Write::write_all(&mut file, &bytes).map_err(|e| {
        Failure::operational(
            phase,
            format!("cannot write cache entry {}: {e}", dst.display()),
        )
    })?;
    Ok(())
}

/// Remove a stale companion artifact at `cache_dir/rel_path` after rejecting
/// symlinks along the path.
fn remove_cache_file(cache_dir: &Path, rel_path: &str, phase: &str) -> Result<(), Failure> {
    let dst = prepare_nosymlink_cache_path(cache_dir, rel_path, false, phase)?;
    if fs::symlink_metadata(&dst).is_ok() {
        fs::remove_file(&dst).map_err(|e| {
            Failure::operational(
                phase,
                format!("cannot remove stale cache entry {}: {e}", dst.display()),
            )
        })?;
    }
    Ok(())
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
    comps.clone().next().is_some() && comps.all(|c| matches!(c, Component::Normal(_)))
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
    fn all_targets(&self) -> impl Iterator<Item = (&'static str, &MemberTarget)> {
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
            (
                "dev_dependencies",
                self.dev_dependencies_underscore.as_ref(),
            ),
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
                format!("forbidden Cargo/toolchain override at repository root: {forbidden}"),
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
    let manifest_text = fs::read_to_string(&manifest_path)
        .map_err(|e| Failure::new(1, phase, format!("cannot read root-manifest.sha256: {e}")))?;
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
                format!("invalid or duplicate entry in root-manifest.sha256: {line}"),
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
    for required_rel in ["Cargo.toml", "Cargo.lock", "flake.nix", "flake.lock"] {
        if !seen_paths.contains(required_rel) {
            return Err(Failure::new(
                1,
                phase,
                format!("root-manifest.sha256 missing required entry: {required_rel}"),
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
    if path.is_absolute() || path.components().any(|c| matches!(c, Component::ParentDir)) {
        return Err(Failure::new(
            1,
            "cargo-boundary",
            format!("{member} target {section}.path escapes member directory: {p}"),
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
                format!("non-string path dependency {dep_name} in {member}/Cargo.toml"),
            ));
        };
        let resolved = fs::canonicalize(member_parent.join(dep_path)).map_err(|_| {
            Failure::new(
                1,
                phase,
                format!("{member} path dependency target does not exist: {dep_path}"),
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
                format!("{member} path dependency points outside trusted/: {rel_str}"),
            ));
        }
        if !member_set.contains(&rel_str) {
            return Err(Failure::new(
                1,
                phase,
                format!("{member} path dependency points to non-member crate: {rel_str}"),
            ));
        }
        regular(&resolved.join("Cargo.toml"), phase)?;
    }
    Ok(())
}

/// Validate `Cargo.lock` (when present): version 4, every external dependency
/// sourced from `crates.io-index` with a 64-hex SHA-256 checksum, and every
/// source-less package belonging to `member_pkg_names`.
fn verify_cargo_lock(checkout: &Path, member_pkg_names: &BTreeSet<String>) -> Result<(), Failure> {
    let phase = "cargo-boundary";
    let lock_path = checkout.join("Cargo.lock");
    if fs::symlink_metadata(&lock_path).is_err() {
        return Ok(());
    }
    regular(&lock_path, phase)?;
    let lock_text = fs::read_to_string(&lock_path)
        .map_err(|e| Failure::new(1, phase, format!("cannot read Cargo.lock: {e}")))?;
    let lock_file: CargoLockFile = toml::from_str(&lock_text)
        .map_err(|e| Failure::new(1, phase, format!("malformed Cargo.lock: {e}")))?;
    if lock_file.version != Some(4) {
        return Err(Failure::new(1, phase, "Cargo.lock must have version = 4"));
    }
    for pkg in &lock_file.package {
        let pkg_name = pkg.name.as_str();
        match pkg.source.as_deref() {
            Some("registry+https://github.com/rust-lang/crates.io-index") => {
                if !pkg.checksum.as_deref().is_some_and(is_sha256_hex) {
                    return Err(Failure::new(
                        1,
                        phase,
                        format!("missing or invalid checksum in Cargo.lock for {pkg_name}"),
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
                if pkg.checksum.is_some() || !member_pkg_names.contains(pkg_name) {
                    return Err(Failure::new(
                        1,
                        phase,
                        format!("untrusted local package without source in Cargo.lock: {pkg_name}"),
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

    let root_text = fs::read_to_string(&root_toml_path)
        .map_err(|e| Failure::new(1, phase, format!("malformed Cargo manifest: {e}")))?;
    let root_manifest: RootCargoManifest = toml::from_str(&root_text).map_err(|e| {
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

    let checkout_canon = fs::canonicalize(checkout)
        .map_err(|e| Failure::new(2, phase, format!("cannot canonicalize checkout: {e}")))?;

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
        let manifest: MemberCargoManifest = toml::from_str(&member_text).map_err(|e| {
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
            .ok_or_else(|| Failure::new(1, phase, format!("missing package.name in {member}")))?;
        member_pkg_names.insert(pkg_name.to_string());

        if manifest.package.build.is_some() || manifest.package.workspace.is_some() {
            return Err(Failure::new(
                1,
                phase,
                format!("disallowed package.build or package.workspace in {member}/Cargo.toml"),
            ));
        }
        if fs::symlink_metadata(checkout.join(member).join("build.rs")).is_ok() {
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
/// [`check_cargo_boundary`] and [`verify_upstream_pin`] whenever any Cargo,
/// root-manifest, or vendored Miri TCB path is present.
fn check_checkout_cargo_hygiene(checkout: &Path) -> Result<(), Failure> {
    reject_cargo_toolchain_overrides(checkout)?;
    if [
        "Cargo.toml",
        "Cargo.lock",
        "trusted/root-manifest.sha256",
        "trusted/rustc-capture",
        "vendor",
    ]
    .iter()
    .any(|rel| fs::symlink_metadata(checkout.join(rel)).is_ok())
    {
        check_cargo_boundary(checkout)?;
        verify_upstream_pin(&checkout.join("vendor/lean-miri"))?;
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
            && (relative == "lean-toolchain" || relative == "foundation-lock.json"))
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
    /// Cached SHA-256-verified `.sysrootFoundation` module names (`Init.*`,
    /// `Std.*`, and `Lean.*` modules outside `foundation_graph` in
    /// `<prefix>/lib/lean`).
    pub sysroot_foundation: Option<Vec<String>>,
}

impl AdmittedToolchain {
    /// Return the sorted list of locked `Init.*` foundation module names.
    pub fn foundation_modules(&self) -> Vec<&str> {
        self.foundation_graph.keys().map(String::as_str).collect()
    }

    /// Verify the SHA-256 digests of all `<prefix>/lib/lean/{Init,Std,Lean}*`
    /// `.olean`, `.olean.server`, and `.olean.private` files against
    /// [`LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256`] and return the sorted list
    /// of `.sysrootFoundation` module names (excluding `foundation_graph`).
    pub fn ensure_sysroot_foundation(&mut self) -> Result<&[String], Failure> {
        if self.sysroot_foundation.is_none() {
            let lib_dir = self.prefix.join("lib/lean");
            let foundation_modules: BTreeSet<String> =
                self.foundation_graph.keys().cloned().collect();
            let modules = verify_sysroot_foundation_dir(
                &lib_dir,
                &foundation_modules,
                LOCKED_SYSROOT_FOUNDATION_MANIFEST_SHA256,
            )?;
            self.sysroot_foundation = Some(modules);
        }
        Ok(self.sysroot_foundation.as_deref().unwrap())
    }
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
    let mut entries: BTreeMap<String, String> = BTreeMap::new();
    let mut modules: BTreeSet<String> = BTreeSet::new();
    for pkg in ["Init", "Std", "Lean"] {
        for ext in OLEAN_PARTS {
            let rel = format!("{pkg}.{ext}");
            let path = lib_dir.join(&rel);
            if fs::symlink_metadata(&path).is_ok() {
                let sha = sha256_file(&path, phase)?;
                entries.insert(rel, sha);
                if ext == "olean" && !foundation_modules.contains(pkg) {
                    modules.insert(pkg.to_string());
                }
            }
        }
        let pkg_dir = lib_dir.join(pkg);
        for item in WalkDir::new(&pkg_dir).follow_links(false) {
            let item = item.map_err(|e| {
                Failure::policy(
                    phase,
                    format!("cannot walk sysroot {}: {e}", pkg_dir.display()),
                )
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
            let is_olean_part = OLEAN_PARTS
                .iter()
                .any(|ext| rel_str.ends_with(&format!(".{ext}")));
            if is_olean_part {
                let sha = sha256_file(item.path(), phase)?;
                entries.insert(rel_str.clone(), sha);
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
            }
        }
    }
    let mut manifest = String::new();
    for (rel, sha) in &entries {
        manifest.push_str(rel);
        manifest.push(':');
        manifest.push_str(sha);
        manifest.push('\n');
    }
    let actual_manifest_sha = sha256_bytes(manifest.as_bytes());
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
    pub miri_cache_dir: Option<PathBuf>,
    pub require_mir_wp: bool,
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

fn is_retained_environment_key(key: &str) -> bool {
    matches!(key, "HOME" | "TMPDIR" | "LANG" | "LC_ALL")
}

impl Checker {
    /// Create a new [`Checker`] with a fresh private staging directory.
    ///
    /// Discard unlisted environment entries before decoding their values. A
    /// retained value that is not valid UTF-8 returns an `InvalidInput` error.
    ///
    /// If `ANNEAL_MIRI_CACHE_DIR` is set and non-empty in the process
    /// environment, it initializes the optional vendored `.olean` cache
    /// directory (overridable via [`Checker::set_miri_cache_dir`]). Cached
    /// entries are accepted only when their SHA-256 digests match
    /// `UPSTREAM_PIN.json` and written back only after digest verification.
    pub fn new(checkout: &Path, lean: Option<&Path>) -> io::Result<Self> {
        // Unforwarded host settings have no bearing on the Lean child, so
        // they impose no UTF-8 requirement. Validate retained values without
        // lossy conversion before admitting them to the child environment.
        let environment = env::vars_os()
            .filter_map(|(key, value)| {
                let key = key.to_str()?;
                is_retained_environment_key(key).then(|| (key.to_owned(), value))
            })
            .map(|(key, value)| {
                let value = value.into_string().map_err(|_| {
                    io::Error::new(
                        io::ErrorKind::InvalidInput,
                        format!("environment variable {key} is not valid UTF-8"),
                    )
                })?;
                Ok((key, value))
            })
            .collect::<io::Result<Vec<_>>>()?;
        let mut checker = Self::new_with_env(checkout, lean, environment)?;
        if let Some(cache_dir) = env::var_os("ANNEAL_MIRI_CACHE_DIR")
            && !cache_dir.is_empty()
        {
            checker.miri_cache_dir = Some(PathBuf::from(cache_dir));
        }
        Ok(checker)
    }

    /// Create a new [`Checker`] using a closed environment allowlist.
    ///
    /// Retains only `HOME`, `TMPDIR`, `LANG`, and `LC_ALL` from `ambient_env`
    /// and pins `PATH` to `/usr/bin:/bin` so ambient search paths (`LEAN_PATH`,
    /// `LEAN_SRC_PATH`), toolchain overrides (`ELAN_TOOLCHAIN`), or dynamic
    /// linker preloading (`LD_PRELOAD`, `LD_LIBRARY_PATH`,
    /// `DYLD_INSERT_LIBRARIES`) cannot influence child `lean` invocations.
    pub fn new_with_env<I>(checkout: &Path, lean: Option<&Path>, ambient_env: I) -> io::Result<Self>
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
        let mut stage_builder = tempfile::Builder::new();
        stage_builder.prefix("anneal-trusted-");
        // Staged sources and proofs must not be readable by other Unix users.
        // Set permissions at creation, before any inputs reach the directory.
        #[cfg(unix)]
        stage_builder.permissions(fs::Permissions::from_mode(0o700));
        let stage_dir = stage_builder.tempdir()?;
        let stage = stage_dir.path().to_path_buf();

        let mut environment: BTreeMap<String, String> = ambient_env
            .into_iter()
            .filter(|(k, _)| is_retained_environment_key(k))
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
            miri_cache_dir: None,
            require_mir_wp: true,
        })
    }

    /// Configure an optional cache directory for verified `Miri.*` `.olean`
    /// artifacts (`execution_machine_closure` in `UPSTREAM_PIN.json`).
    pub fn set_miri_cache_dir(&mut self, cache_dir: Option<PathBuf>) {
        self.miri_cache_dir = cache_dir;
    }

    /// Configure whether the Phase 2 `"audit"` inspector unconditionally
    /// requires `Trusted.MirAst`, `Trusted.MirSemantics`, and `Anneal.MirWp`
    /// to be present (defaults to `true`; only disabled in minimal synthetic
    /// unit test fixtures; even when `false`, the check still runs if any MIR
    /// or `PureLift` module is loaded).
    pub fn set_require_mir_wp(&mut self, require: bool) {
        self.require_mir_wp = require;
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

    /// Capture a Lean child in the stage with only the selected environment.
    ///
    /// I/O errors remain distinct from a completed child's exit status. Each
    /// caller applies its own diagnostic and protocol rules to the raw output.
    fn launch_lean(&self, arguments: &[String]) -> io::Result<Output> {
        self.launch_lean_with_path(arguments, None)
    }

    /// Capture a Lean child in the stage with an optional `LEAN_PATH`
    /// override pointing at staged `.olean` directories (Lean appends the
    /// authenticated toolchain sysroot library path automatically).
    fn launch_lean_with_path(
        &self,
        arguments: &[String],
        lean_path: Option<&std::ffi::OsStr>,
    ) -> io::Result<Output> {
        let mut cmd = Command::new(&self.lean);
        cmd.args(arguments)
            .current_dir(&self.stage)
            .env_clear()
            .envs(&self.environment);
        if let Some(lp) = lean_path {
            cmd.env("LEAN_PATH", lp);
        }
        cmd.output()
    }

    /// Execute `self.lean` with `arguments` in the sanitized `self.environment`
    /// with `self.stage` as the working directory.
    pub fn process(&mut self, label: &str, arguments: &[String]) -> Result<String, Failure> {
        self.process_with_path(label, arguments, None)
    }

    /// Execute `self.lean` with `arguments` and an optional hermetic
    /// `LEAN_PATH` override.
    pub fn process_with_path(
        &mut self,
        label: &str,
        arguments: &[String],
        lean_path: Option<&std::ffi::OsStr>,
    ) -> Result<String, Failure> {
        self.counter += 1;
        let output = self
            .launch_lean_with_path(arguments, lean_path)
            .map_err(|e| Failure::new(2, label, format!("could not execute Lean: {e}")))?;
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
        String::from_utf8(output.stdout)
            .map_err(|e| Failure::new(2, label, format!("invalid UTF-8 from Lean: {e}")))
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
        let bytes =
            serde_json::to_vec(&setup_obj).map_err(|e| Failure::new(2, "setup", e.to_string()))?;
        fs::write(&setup_path, bytes).map_err(|e| Failure::new(2, "setup", e.to_string()))?;
        Ok(setup_path)
    }

    /// Invoke `TrustedBoundary.lean` with a typed [`InspectorRequest`] and
    /// validate the structured response envelope.
    pub fn inspect(&mut self, request: InspectorRequest) -> Result<Json, Failure> {
        let mode = request.mode();
        if matches!(request, InspectorRequest::CorrespondenceAudit { .. }) {
            self.admitted_mut()?.ensure_sysroot_foundation()?;
        }
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
                    "requireMirWp": self.require_mir_wp,
                })
            }
            InspectorRequest::CorrespondenceAudit {
                search_path,
                trusted,
                corr_trusted,
                theory,
                corr_theory,
                vendor_miri,
                module_tiers,
            } => {
                let sysroot_foundation = adm.sysroot_foundation.as_deref().unwrap_or(&[]);
                let sp: Vec<std::borrow::Cow<'_, str>> =
                    search_path.iter().map(|p| p.to_string_lossy()).collect();
                let tiers: Vec<(&str, String)> = module_tiers
                    .iter()
                    .map(|(m, t)| (m.as_str(), t.render()))
                    .collect();
                json!({
                    "mode": "correspondence-audit",
                    "sysroot": adm.prefix.to_string_lossy(),
                    "searchPath": sp,
                    "foundation": foundation,
                    "sysrootFoundation": sysroot_foundation,
                    "axioms": &adm.axioms,
                    "trusted": trusted,
                    "corrTrusted": corr_trusted,
                    "theory": theory,
                    "corrTheory": corr_theory,
                    "vendorMiri": vendor_miri,
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
        let result_path = PathBuf::from(format!("{}.result.json", stem.display()));
        let req_bytes = serde_json::to_vec(&req)
            .map_err(|e| Failure::new(2, mode, format!("cannot serialize request: {e}")))?;
        fs::write(&request_path, req_bytes)
            .map_err(|e| Failure::new(2, mode, format!("cannot write request: {e}")))?;

        // Keep Phase 1/2 capped at `-M2048` during preflight and core audit.
        // Raise the cap to `-M8192` for Phase 3 (`CorrespondenceAudit`), which
        // loads the 160-module `lean-miri` and `Lean.*` closure alongside the
        // already-audited `Trusted.*` and `theory/` `.olean` files (resource
        // bound only; soundness does not depend on this limit).
        let mem_limit = match request {
            InspectorRequest::CorrespondenceAudit { .. } => "-M8192",
            InspectorRequest::Preflight { .. } | InspectorRequest::Audit { .. } => "-M2048",
        };
        let args = vec![
            "-j1".to_string(),
            mem_limit.to_string(),
            "--run".to_string(),
            inspector.to_string_lossy().into_owned(),
            request_path.to_string_lossy().into_owned(),
            result_path.to_string_lossy().into_owned(),
        ];
        let output = self
            .launch_lean(&args)
            .map_err(|e| Failure::new(2, mode, format!("could not execute Lean: {e}")))?;

        if !output.status.success() {
            if output.status.code() == Some(1)
                && result_path.is_file()
                && let Ok(text) = fs::read_to_string(&result_path)
                && let Ok(resp) = serde_json::from_str::<InspectorErrResponse>(&text)
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
                format!("Lean exited {:?}: {}", output.status.code(), stderr.trim()),
            ));
        }

        let resp_text = fs::read_to_string(&result_path).map_err(|e| {
            Failure::new(2, mode, format!("missing/malformed inspector result: {e}"))
        })?;
        let resp: InspectorOkResponse = serde_json::from_str(&resp_text)
            .map_err(|_| Failure::new(2, mode, "unexpected inspector protocol response"))?;
        if !resp.ok {
            return Err(Failure::new(
                2,
                mode,
                "unexpected inspector protocol response",
            ));
        }
        if let InspectorRequest::CorrespondenceAudit { vendor_miri, .. } = &request {
            validate_correspondence_report(&resp.result, !vendor_miri.is_empty())?;
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
        let mut stage_builder = fs::DirBuilder::new();
        // Recreating the stage must preserve its owner-only Unix permissions.
        // A pre-existing replacement directory must cause creation to fail.
        #[cfg(unix)]
        stage_builder.mode(0o700);
        stage_builder.create(&self.stage).map_err(|e| {
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
        let modules = self.scan_and_stage_tree(&self.source, "Trusted", "src/trusted")?;
        let theory_dir = self.checkout.join("theory");
        let theory_modules = if fs::symlink_metadata(&theory_dir).is_ok() {
            self.scan_and_stage_tree(&theory_dir, "Anneal", "src/theory")?
        } else {
            BTreeMap::new()
        };

        let inspector_src = self.checkout.join("trusted/audit/TrustedBoundary.lean");
        let inspector = self.stage.join("src/TrustedBoundary.lean");
        stage_regular_file(&inspector_src, &inspector, "tool-snapshot")?;

        let lock_path = self.source.join("foundation-lock.json");
        let toolchain_path = self.source.join("lean-toolchain");
        regular(&lock_path, "lock")?;
        regular(&toolchain_path, "lock")?;

        let lock_text = fs::read_to_string(&lock_path)
            .map_err(|e| Failure::new(2, "lock", format!("cannot read foundation lock: {e}")))?;
        let parsed_lock: FoundationLock = serde_json::from_str(&lock_text)
            .map_err(|e| Failure::new(2, "lock", format!("cannot read foundation lock: {e}")))?;
        if parsed_lock.schema != 1
            || parsed_lock.toolchain != TOOLCHAIN
            || parsed_lock.distributions.is_empty()
            || !parsed_lock.distributions.values().all(|s| is_sha256_hex(s))
            || parsed_lock.modules.is_empty()
            || !parsed_lock.modules.keys().eq(parsed_lock.graph.keys())
        {
            return Err(Failure::new(2, "lock", "unsupported lock/toolchain schema"));
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

        let toolchain_text = fs::read_to_string(&toolchain_path)
            .map_err(|e| Failure::new(2, "lock", format!("cannot read lean-toolchain: {e}")))?;
        if toolchain_text.trim() != TOOLCHAIN {
            return Err(Failure::new(1, "lock", "lean-toolchain differs from lock"));
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
        let Some(expected_lean_sha) = parsed_lock.distributions.get(&actual_version) else {
            return Err(Failure::new(
                2,
                "toolchain",
                format!("Lean version/commit differs from lock: {actual_version}"),
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
        let prefix = fs::canonicalize(&prefix_raw)
            .map_err(|e| Failure::new(2, "toolchain", format!("cannot resolve prefix: {e}")))?;

        let mut artifacts = BTreeMap::new();

        for (module, record) in &parsed_lock.modules {
            let rel_mod = module.replace('.', "/");
            let source_path = prefix.join("src/lean").join(format!("{rel_mod}.lean"));
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
                        let actual_part_sha = sha256_file(&installed, "foundation")?;
                        if !actual_part_sha.eq_ignore_ascii_case(expected_part_sha) {
                            return Err(Failure::new(
                                2,
                                "foundation",
                                format!(
                                    "foundation artifact SHA-256 mismatch for {relative}: expected {expected_part_sha}, got {actual_part_sha}"
                                ),
                            ));
                        }
                        available.insert(part, installed.to_string_lossy().into_owned());
                    }
                }
            }

            let mod_arts = ModuleArtifacts::from_available(&available, "foundation", || {
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
            sysroot_foundation: None,
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
        let pf_res: PreflightResult =
            serde_json::from_value(self.inspect(InspectorRequest::Preflight { sources })?)
                .map_err(|_| {
                    Failure::operational("preflight", "incomplete source-header inventory")
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
                        format!("missing trust tier for Trusted module {mod_name}"),
                    )
                })?;
                let tier = TrustTier::parse(&raw_tier).ok_or_else(|| {
                    Failure::policy(
                        "preflight",
                        format!("invalid trust tier {raw_tier} for Trusted module {mod_name}"),
                    )
                })?;
                module_tiers.insert(mod_name.clone(), tier);
            }
            for edge in &h.imports {
                let imp_mod = edge.module.as_str();
                let allowed = if is_trusted {
                    adm.artifacts.contains_key(imp_mod) || adm.modules.contains_key(imp_mod)
                } else {
                    adm.artifacts.contains_key(imp_mod)
                        || adm.modules.contains_key(imp_mod)
                        || adm.theory_modules.contains_key(imp_mod)
                };
                if !allowed {
                    return Err(Failure::policy(
                        "preflight",
                        format!("foreign/missing import {imp_mod} in {mod_name}"),
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
        let mod_arts = ModuleArtifacts::from_available(&available, "compile", || {
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
        if let Some(cache_dir) = &self.miri_cache_dir {
            ensure_miri_cache_outside_checkout(&self.checkout, cache_dir)?;
        }
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
        let trusted_order =
            topo_sort_modules(trusted_set, &preflight.imports, "Trusted import cycle")?;
        let theory_order =
            topo_sort_modules(theory_set, &preflight.imports, "Theory import cycle")?;

        for module in &trusted_order {
            let edge_list = preflight.imports[module].clone();
            let staged_src_path = self.admitted()?.modules[module].clone();
            self.execution_began = true;
            self.compile_lean_module(module, &staged_src_path, edge_list, "lib", false)?;
        }

        for module in &theory_order {
            let edge_list = preflight.imports[module].clone();
            let staged_src_path = self.admitted()?.theory_modules[module].clone();
            self.execution_began = true;
            self.compile_lean_module(module, &staged_src_path, edge_list, "theory-lib", true)?;
        }

        let audit_req = {
            let adm = self.admitted()?;
            InspectorRequest::Audit {
                trusted: adm.modules.keys().cloned().collect(),
                theory: adm.theory_modules.keys().cloned().collect(),
                module_tiers: preflight.module_tiers.clone(),
            }
        };
        let mut report = self.inspect(audit_req)?;
        let version = self.admitted()?.version.clone();
        {
            let rep_obj = report.as_object_mut().unwrap();
            rep_obj.insert("toolchain".to_string(), json!(version));
            rep_obj.insert(
                "guarantee".to_string(),
                json!(
                    "kernel dependency closure, module-origin separation, and Cargo DAG boundary"
                ),
            );
        }

        if let Some(corr_report) = self.run_miri_closure(&preflight.module_tiers)?
            && let (Some(rep_obj), Some(corr_obj)) =
                (report.as_object_mut(), corr_report.as_object())
        {
            for (k, v) in corr_obj {
                rep_obj.insert(k.clone(), v.clone());
            }
        }

        Ok(report)
    }

    /// Stage, compile (or restore from verified cache), and audit the
    /// 160-module `Miri.Interpreter.ExecutionMachine` closure whenever
    /// `vendor/lean-miri` is present in `self.checkout`.
    fn run_miri_closure(
        &mut self,
        base_tiers: &BTreeMap<String, TrustTier>,
    ) -> Result<Option<Json>, Failure> {
        let vendor_dir = self.checkout.join("vendor/lean-miri");
        if fs::symlink_metadata(&vendor_dir).is_err() {
            return Ok(None);
        }

        let pin = verify_upstream_pin(&vendor_dir)?;
        // Authenticate the toolchain sysroot `.olean` manifest before compiling
        // any vendored module against `Init`/`Std`/`Lean`.
        self.admitted_mut()?.ensure_sysroot_foundation()?;

        let expected_sources = pin.expected_source_digests();
        let miri_lib = self.verify_and_stage_miri_entries(
            &vendor_dir,
            &pin.execution_machine_closure,
            &expected_sources,
        )?;

        let search_dirs = vec![
            self.stage.join("lib"),
            self.stage.join("theory-lib"),
            miri_lib,
        ];
        let corr_req = {
            let adm = self.admitted()?;
            InspectorRequest::CorrespondenceAudit {
                search_path: search_dirs,
                trusted: adm.modules.keys().cloned().collect(),
                corr_trusted: Vec::new(),
                theory: adm.theory_modules.keys().cloned().collect(),
                corr_theory: Vec::new(),
                vendor_miri: pin
                    .execution_machine_closure
                    .iter()
                    .map(|e| e.module.clone())
                    .collect(),
                module_tiers: base_tiers.clone(),
            }
        };
        let mut corr_report = self.inspect(corr_req)?;
        if let Some(obj) = corr_report.as_object_mut() {
            validate_correspondence_report(obj, !pin.execution_machine_closure.is_empty())?;
            obj.insert("miriCommit".to_string(), json!(pin.commit));
            obj.insert(
                "miriClosureModules".to_string(),
                json!(pin.execution_machine_closure.len()),
            );
        } else {
            return Err(Failure::operational(
                "correspondence-audit",
                "expected JSON object from correspondence audit",
            ));
        }
        Ok(Some(corr_report))
    }

    /// Stage, restore from the digest-gated cache or compile cold inside an
    /// OS-level sandbox, verify every staged source and output `.olean`
    /// companion digest (plus absence of symlinks or unexpected sandbox
    /// outputs), and write newly compiled artifacts to `self.miri_cache_dir`
    /// only after verification succeeds.
    pub fn verify_and_stage_miri_entries(
        &mut self,
        vendor_dir: &Path,
        entries: &[MiriClosureEntry],
        expected_sources: &BTreeMap<String, String>,
    ) -> Result<PathBuf, Failure> {
        if let Some(cache_dir) = &self.miri_cache_dir {
            ensure_miri_cache_outside_checkout(&self.checkout, cache_dir)?;
        }
        let miri_src_root = self.stage.join("src/vendor-miri");
        let miri_lib = self.stage.join("miri-lib");
        fs::create_dir_all(&miri_lib)
            .map_err(|e| Failure::operational("miri-compile", e.to_string()))?;
        for entry in entries {
            let Some(expected_src_sha) = expected_sources.get(&entry.path) else {
                return Err(Failure::policy(
                    "miri-pin",
                    format!(
                        "missing pinned source digest for Miri closure module {}",
                        entry.path
                    ),
                ));
            };
            let src_file = vendor_dir.join(&entry.path);
            let staged_src = miri_src_root.join(&entry.path);
            let actual_src_sha = stage_regular_file(&src_file, &staged_src, "miri-pin")?;
            if !actual_src_sha.eq_ignore_ascii_case(expected_src_sha) {
                return Err(Failure::policy(
                    "miri-pin",
                    format!(
                        "staged Miri source SHA-256 mismatch for {}: expected {expected_src_sha}, got {actual_src_sha}",
                        entry.path
                    ),
                ));
            }
        }

        for entry in entries {
            let rel_stem = entry.module.replace('.', "/");
            let rel_olean = format!("{rel_stem}.olean");
            let staged_olean = miri_lib.join(&rel_olean);
            if let Some(parent) = staged_olean.parent() {
                fs::create_dir_all(parent)
                    .map_err(|e| Failure::operational("miri-compile", e.to_string()))?;
            }
            let mut cache_hit = false;
            if let Some(cache_dir) = &self.miri_cache_dir {
                let cached =
                    prepare_nosymlink_cache_path(cache_dir, &rel_olean, false, "miri-pin")?;
                let olean_matches = sha256_file(&cached, "miri-pin")
                    .is_ok_and(|h| h.eq_ignore_ascii_case(&entry.olean_sha256));
                let mut parts_match = true;
                for (part, expected_opt) in [
                    ("olean.server", entry.olean_server_sha256.as_deref()),
                    ("olean.private", entry.olean_private_sha256.as_deref()),
                ] {
                    let rel_part = format!("{rel_stem}.{part}");
                    let cached_part =
                        prepare_nosymlink_cache_path(cache_dir, &rel_part, false, "miri-pin")?;
                    let ok = match expected_opt {
                        Some(exp_sha) => sha256_file(&cached_part, "miri-pin")
                            .is_ok_and(|h| h.eq_ignore_ascii_case(exp_sha)),
                        None => fs::symlink_metadata(&cached_part).is_err(),
                    };
                    if !ok {
                        parts_match = false;
                    }
                }
                if olean_matches && parts_match {
                    stage_regular_file(&cached, &staged_olean, "miri-pin")?;
                    for (part, expected_opt) in [
                        ("olean.server", entry.olean_server_sha256.as_deref()),
                        ("olean.private", entry.olean_private_sha256.as_deref()),
                    ] {
                        if expected_opt.is_some() {
                            let rel_part = format!("{rel_stem}.{part}");
                            let cached_part = prepare_nosymlink_cache_path(
                                cache_dir, &rel_part, false, "miri-pin",
                            )?;
                            stage_regular_file(
                                &cached_part,
                                &miri_lib.join(&rel_part),
                                "miri-pin",
                            )?;
                        }
                    }
                    cache_hit = true;
                }
            }
            if cache_hit {
                let actual_olean_sha = sha256_file(&staged_olean, "miri-pin")?;
                if !actual_olean_sha.eq_ignore_ascii_case(&entry.olean_sha256) {
                    return Err(Failure::policy(
                        "miri-pin",
                        format!(
                            "compiled Miri .olean SHA-256 mismatch for {}: expected {}, got {actual_olean_sha}",
                            entry.module, entry.olean_sha256
                        ),
                    ));
                }
                for (part, expected_opt) in [
                    ("olean.server", entry.olean_server_sha256.as_deref()),
                    ("olean.private", entry.olean_private_sha256.as_deref()),
                ] {
                    let staged_part = miri_lib.join(format!("{rel_stem}.{part}"));
                    match expected_opt {
                        Some(exp_sha) => {
                            if fs::symlink_metadata(&staged_part).is_err() {
                                return Err(Failure::policy(
                                    "miri-pin",
                                    format!(
                                        "missing compiled Miri .{part} sidecar for {}",
                                        entry.module
                                    ),
                                ));
                            }
                            let actual_sha = sha256_file(&staged_part, "miri-pin")?;
                            if !actual_sha.eq_ignore_ascii_case(exp_sha) {
                                return Err(Failure::policy(
                                    "miri-pin",
                                    format!(
                                        "compiled Miri .{part} SHA-256 mismatch for {}: expected {exp_sha}, got {actual_sha}",
                                        entry.module
                                    ),
                                ));
                            }
                        }
                        None => {
                            if fs::symlink_metadata(&staged_part).is_ok() {
                                return Err(Failure::policy(
                                    "miri-pin",
                                    format!("unexpected Miri .{part} sidecar for {}", entry.module),
                                ));
                            }
                        }
                    }
                }
                continue;
            }

            // Cold vendor elaboration runs inside an isolated per-module OS
            // sandbox whose sole host-backed writable directory is a fresh
            // owner-only temporary directory outside `self.stage`, the
            // checkout, `$HOME`, and `self.miri_cache_dir`.
            self.execution_began = true;
            let mut out_builder = tempfile::Builder::new();
            out_builder.prefix("anneal-miri-out-");
            #[cfg(unix)]
            out_builder.permissions(fs::Permissions::from_mode(0o700));
            let module_out_dir = out_builder
                .tempdir()
                .map_err(|e| Failure::operational("miri-compile", e.to_string()))?;
            let out_olean = module_out_dir.path().join(&rel_olean);
            if let Some(parent) = out_olean.parent() {
                fs::create_dir_all(parent)
                    .map_err(|e| Failure::operational("miri-compile", e.to_string()))?;
            }
            self.sandbox_compile_miri_module(
                &format!("compile-{}", entry.module),
                &miri_src_root,
                &miri_lib,
                module_out_dir.path(),
                &rel_olean,
                &entry.path,
            )?;

            let actual_olean_sha = sha256_file(&out_olean, "miri-pin")?;
            if !actual_olean_sha.eq_ignore_ascii_case(&entry.olean_sha256) {
                return Err(Failure::policy(
                    "miri-pin",
                    format!(
                        "compiled Miri .olean SHA-256 mismatch for {}: expected {}, got {actual_olean_sha}",
                        entry.module, entry.olean_sha256
                    ),
                ));
            }
            let mut expected_out_files = BTreeSet::from([rel_olean.clone()]);
            for (part, expected_opt) in [
                ("olean.server", entry.olean_server_sha256.as_deref()),
                ("olean.private", entry.olean_private_sha256.as_deref()),
            ] {
                let rel_part = format!("{rel_stem}.{part}");
                let out_part = module_out_dir.path().join(&rel_part);
                match expected_opt {
                    Some(exp_sha) => {
                        if fs::symlink_metadata(&out_part).is_err() {
                            return Err(Failure::policy(
                                "miri-pin",
                                format!(
                                    "missing compiled Miri .{part} sidecar for {}",
                                    entry.module
                                ),
                            ));
                        }
                        let actual_sha = sha256_file(&out_part, "miri-pin")?;
                        if !actual_sha.eq_ignore_ascii_case(exp_sha) {
                            return Err(Failure::policy(
                                "miri-pin",
                                format!(
                                    "compiled Miri .{part} SHA-256 mismatch for {}: expected {exp_sha}, got {actual_sha}",
                                    entry.module
                                ),
                            ));
                        }
                        expected_out_files.insert(rel_part);
                    }
                    None => {
                        if fs::symlink_metadata(&out_part).is_ok() {
                            return Err(Failure::policy(
                                "miri-pin",
                                format!("unexpected Miri .{part} sidecar for {}", entry.module),
                            ));
                        }
                    }
                }
            }
            // Lean 4 `module`-system files (identified by pinned `.olean.server`
            // or `.olean.private` sidecars, such as `Miri.Memory.QSortProof`)
            // also emit ephemeral `.ir` and `.ir.sig` sidecars alongside `-o`.
            // Permit them as regular files in the per-module sandbox output
            // directory only for `module`-system entries; they are discarded
            // when `module_out_dir` drops and are never staged or cached.
            if entry.olean_server_sha256.is_some() || entry.olean_private_sha256.is_some() {
                expected_out_files.insert(format!("{rel_stem}.ir"));
                expected_out_files.insert(format!("{rel_stem}.ir.sig"));
            }
            verify_no_unexpected_sandbox_outputs(
                module_out_dir.path(),
                &expected_out_files,
                &rel_olean,
                &entry.module,
            )?;

            // Stage verified regular artifacts from the isolated sandbox output
            // into `self.stage/miri-lib`, re-checking the copied byte digests.
            let staged_olean_sha = stage_regular_file(&out_olean, &staged_olean, "miri-pin")?;
            if !staged_olean_sha.eq_ignore_ascii_case(&entry.olean_sha256) {
                return Err(Failure::policy(
                    "miri-pin",
                    format!(
                        "staged Miri .olean SHA-256 mismatch for {}: expected {}, got {staged_olean_sha}",
                        entry.module, entry.olean_sha256
                    ),
                ));
            }
            for (part, expected_opt) in [
                ("olean.server", entry.olean_server_sha256.as_deref()),
                ("olean.private", entry.olean_private_sha256.as_deref()),
            ] {
                if let Some(exp_sha) = expected_opt {
                    let rel_part = format!("{rel_stem}.{part}");
                    let staged_part_sha = stage_regular_file(
                        &module_out_dir.path().join(&rel_part),
                        &miri_lib.join(&rel_part),
                        "miri-pin",
                    )?;
                    if !staged_part_sha.eq_ignore_ascii_case(exp_sha) {
                        return Err(Failure::policy(
                            "miri-pin",
                            format!(
                                "staged Miri .{part} SHA-256 mismatch for {}: expected {exp_sha}, got {staged_part_sha}",
                                entry.module
                            ),
                        ));
                    }
                }
            }

            if let Some(cache_dir) = &self.miri_cache_dir {
                write_cache_file(&staged_olean, cache_dir, &rel_olean, "miri-pin")?;
                for part in &OLEAN_PARTS[1..] {
                    let rel_part = format!("{rel_stem}.{part}");
                    let staged_part = miri_lib.join(&rel_part);
                    if fs::symlink_metadata(&staged_part).is_ok() {
                        write_cache_file(&staged_part, cache_dir, &rel_part, "miri-pin")?;
                    } else {
                        remove_cache_file(cache_dir, &rel_part, "miri-pin")?;
                    }
                }
            }
        }
        Ok(miri_lib)
    }

    /// Compile one vendored `Miri.*` module inside an OS-level isolated
    /// sandbox so unpreflighted compile-time metaprograms (`run_cmd`,
    /// `initialize`, custom `elab`s) have zero credentials, zero network
    /// access, and no writable access to the repository checkout, home
    /// directory, cache, or auditor staging state.
    ///
    /// On Linux this invokes `/usr/bin/bwrap` (or `/bin/bwrap`) with
    /// `--unshare-all --die-with-parent --new-session --clearenv --tmpfs /`,
    /// mounting the Lean toolchain, staged vendor sources, and already-verified
    /// `miri-lib` strictly read-only and exposing `module_out_dir` as the sole
    /// host-backed writable directory (`/work/out`). On platforms without a
    /// supported OS sandbox, cold compilation fails closed.
    fn sandbox_compile_miri_module(
        &mut self,
        label: &str,
        miri_src_root: &Path,
        miri_lib: &Path,
        module_out_dir: &Path,
        rel_olean: &str,
        entry_rel_path: &str,
    ) -> Result<(), Failure> {
        #[cfg(not(target_os = "linux"))]
        {
            let _ = (
                miri_src_root,
                miri_lib,
                module_out_dir,
                rel_olean,
                entry_rel_path,
            );
            return Err(Failure::operational(
                label,
                "cold vendor Lean compilation requires an OS-level sandbox (currently supported via Linux bubblewrap /usr/bin/bwrap); supply a verified --miri-cache-dir or run on Linux",
            ));
        }

        #[cfg(target_os = "linux")]
        {
            let bwrap = ["/usr/bin/bwrap", "/bin/bwrap"]
                .into_iter()
                .map(Path::new)
                .find(|p| fs::metadata(p).is_ok_and(|m| m.is_file()))
                .ok_or_else(|| {
                    Failure::operational(
                        label,
                        "cold vendor Lean compilation requires Linux bubblewrap (/usr/bin/bwrap) to enforce OS-level sandboxing",
                    )
                })?;

            let lean_prefix = self.admitted()?.prefix.clone();
            let lean_canon = fs::canonicalize(&self.lean).map_err(|e| {
                Failure::operational(label, format!("cannot resolve Lean binary path: {e}"))
            })?;
            let lean_rel = lean_canon.strip_prefix(&lean_prefix).map_err(|_| {
                Failure::operational(
                    label,
                    format!(
                        "Lean binary {} does not reside under admitted toolchain prefix {}",
                        lean_canon.display(),
                        lean_prefix.display()
                    ),
                )
            })?;
            let sandbox_lean = Path::new("/toolchain").join(lean_rel);

            let args = build_bwrap_miri_compile_args(
                &lean_prefix,
                &sandbox_lean,
                miri_src_root,
                miri_lib,
                module_out_dir,
                rel_olean,
                entry_rel_path,
            );
            self.counter += 1;
            let output = Command::new(bwrap)
                .args(&args)
                .current_dir(module_out_dir)
                .env_clear()
                .output()
                .map_err(|e| {
                    Failure::new(
                        2,
                        label,
                        format!(
                            "could not execute bubblewrap sandbox {}: {e}",
                            bwrap.display()
                        ),
                    )
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
                    format!("sandboxed Lean exited {:?}: {detail}", output.status.code()),
                ));
            }
            Ok(())
        }
    }
}

/// Build the `bwrap` argument vector that confines cold `vendor/lean-miri/`
/// compilation to an empty `tmpfs` root with isolated user, mount, PID, IPC,
/// UTS, and network namespaces, read-only runtime libraries/toolchain/inputs,
/// and a single host-backed writable output directory (`/work/out`).
fn build_bwrap_miri_compile_args(
    lean_prefix: &Path,
    sandbox_lean: &Path,
    miri_src_root: &Path,
    miri_lib: &Path,
    module_out_dir: &Path,
    rel_olean: &str,
    entry_rel_path: &str,
) -> Vec<OsString> {
    let mut args: Vec<OsString> = Vec::new();
    for flag in [
        "--unshare-all",
        "--die-with-parent",
        "--new-session",
        "--clearenv",
        "--tmpfs",
        "/",
        "--dev",
        "/dev",
        "--proc",
        "/proc",
        "--ro-bind",
        "/usr/lib",
        "/usr/lib",
        "--ro-bind-try",
        "/usr/lib64",
        "/usr/lib64",
        "--ro-bind-try",
        "/lib",
        "/lib",
        "--ro-bind-try",
        "/lib64",
        "/lib64",
        "--ro-bind-try",
        "/etc/ld.so.cache",
        "/etc/ld.so.cache",
        "--ro-bind-try",
        "/etc/ld.so.conf",
        "/etc/ld.so.conf",
        "--ro-bind-try",
        "/etc/ld.so.conf.d",
        "/etc/ld.so.conf.d",
    ] {
        args.push(OsString::from(flag));
    }
    if lean_prefix.starts_with("/nix/store") {
        args.push(OsString::from("--ro-bind"));
        args.push(OsString::from("/nix/store"));
        args.push(OsString::from("/nix/store"));
    }

    args.push(OsString::from("--ro-bind"));
    args.push(lean_prefix.as_os_str().to_os_string());
    args.push(OsString::from("/toolchain"));

    args.push(OsString::from("--ro-bind"));
    args.push(miri_src_root.as_os_str().to_os_string());
    args.push(OsString::from("/work/src/vendor-miri"));

    args.push(OsString::from("--ro-bind"));
    args.push(miri_lib.as_os_str().to_os_string());
    args.push(OsString::from("/work/miri-lib"));

    args.push(OsString::from("--bind"));
    args.push(module_out_dir.as_os_str().to_os_string());
    args.push(OsString::from("/work/out"));

    for flag in [
        "--tmpfs",
        "/work/tmp",
        "--chdir",
        "/work",
        "--setenv",
        "PATH",
        "/toolchain/bin",
        "--setenv",
        "LEAN_PATH",
        "/work/miri-lib",
        "--setenv",
        "HOME",
        "/work/tmp",
        "--setenv",
        "TMPDIR",
        "/work/tmp",
        "--setenv",
        "LANG",
        "C.UTF-8",
        "--setenv",
        "LC_ALL",
        "C.UTF-8",
        "--",
    ] {
        args.push(OsString::from(flag));
    }

    args.push(sandbox_lean.as_os_str().to_os_string());
    for arg in [
        "-j1",
        "-M2048",
        "-t0",
        "-DElab.async=false",
        "-Ddebug.skipKernelTC=false",
        "-R",
        "src/vendor-miri",
        "-o",
    ] {
        args.push(OsString::from(arg));
    }
    args.push(OsString::from(format!("out/{rel_olean}")));
    args.push(OsString::from(format!("src/vendor-miri/{entry_rel_path}")));
    args
}

/// Reject any symlink, non-regular file, unexpected file, or unexpected
/// subdirectory created inside a per-module sandbox output directory.
fn verify_no_unexpected_sandbox_outputs(
    out_root: &Path,
    expected_files: &BTreeSet<String>,
    rel_olean: &str,
    module: &str,
) -> Result<(), Failure> {
    let mut allowed_dirs = BTreeSet::new();
    let mut ancestor = Path::new(rel_olean).parent();
    while let Some(dir) = ancestor {
        if dir.as_os_str().is_empty() {
            break;
        }
        let mut segs = Vec::new();
        for comp in dir.components() {
            if let Component::Normal(s) = comp
                && let Some(s) = s.to_str()
            {
                segs.push(s);
            }
        }
        if !segs.is_empty() {
            allowed_dirs.insert(segs.join("/"));
        }
        ancestor = dir.parent();
    }

    for item in WalkDir::new(out_root).follow_links(false) {
        let item = item.map_err(|e| {
            Failure::policy(
                "miri-pin",
                format!("cannot inspect sandbox output for {module}: {e}"),
            )
        })?;
        if item.path() == out_root {
            continue;
        }
        let ft = item.file_type();
        if ft.is_symlink() {
            return Err(Failure::policy(
                "miri-pin",
                format!(
                    "symlink forbidden in sandboxed Miri output for {module}: {}",
                    item.path().display()
                ),
            ));
        }
        let rel = item.path().strip_prefix(out_root).map_err(|e| {
            Failure::operational("miri-pin", format!("invalid sandbox relative path: {e}"))
        })?;
        let mut segs = Vec::new();
        for comp in rel.components() {
            let Component::Normal(os) = comp else {
                return Err(Failure::policy(
                    "miri-pin",
                    format!(
                        "invalid path component in sandboxed Miri output for {module}: {}",
                        item.path().display()
                    ),
                ));
            };
            let Some(s) = os.to_str() else {
                return Err(Failure::policy(
                    "miri-pin",
                    format!(
                        "non-UTF-8 path in sandboxed Miri output for {module}: {}",
                        item.path().display()
                    ),
                ));
            };
            segs.push(s);
        }
        let rel_str = segs.join("/");
        if ft.is_dir() {
            if !allowed_dirs.contains(&rel_str) {
                return Err(Failure::policy(
                    "miri-pin",
                    format!(
                        "unexpected directory in sandboxed Miri output for {module}: {rel_str}"
                    ),
                ));
            }
        } else if ft.is_file() {
            if !expected_files.contains(&rel_str) {
                return Err(Failure::policy(
                    "miri-pin",
                    format!("unexpected file in sandboxed Miri output for {module}: {rel_str}"),
                ));
            }
        } else {
            return Err(Failure::policy(
                "miri-pin",
                format!("unexpected file type in sandboxed Miri output for {module}: {rel_str}"),
            ));
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Stage 5: `vendor/lean-miri/UPSTREAM_PIN.json` verification
// ---------------------------------------------------------------------------

/// Fail-closed validation of the `"correspondence-audit"` JSON result returned
/// by `TrustedBoundary.lean`.
///
/// Requires `miriReplay == true` and a numeric `miriReplayedDeclarations`
/// count (which must be positive whenever `has_vendor_miri` is `true`).
fn validate_correspondence_report(
    result: &serde_json::Map<String, Json>,
    has_vendor_miri: bool,
) -> Result<(), Failure> {
    let phase = "correspondence-audit";
    if result.get("miriReplay").and_then(Json::as_bool) != Some(true) {
        return Err(Failure::policy(
            phase,
            "correspondence audit did not confirm vendor Miri kernel replay",
        ));
    }
    let Some(replayed) = result
        .get("miriReplayedDeclarations")
        .and_then(Json::as_u64)
    else {
        return Err(Failure::operational(
            phase,
            "missing miriReplayedDeclarations in correspondence audit result",
        ));
    };
    if has_vendor_miri && replayed == 0 {
        return Err(Failure::policy(
            phase,
            "correspondence audit replayed zero vendor Miri declarations",
        ));
    }
    Ok(())
}

/// Deserialized representation of `vendor/lean-miri/UPSTREAM_PIN.json`.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct UpstreamPin {
    pub schema_version: i64,
    pub repository: String,
    pub commit: String,
    pub upstream_lean_toolchain: String,
    pub build_lean_toolchain: String,
    pub notes: Vec<String>,
    pub upstream_git_objects: BTreeMap<String, String>,
    pub upstream_pins: UpstreamSubPins,
    pub patched_files: Vec<PatchedMiriFile>,
    pub execution_machine_closure: Vec<MiriClosureEntry>,
    pub vendor_aux_files: Vec<VendorFileEntry>,
    pub vendor_tree: VendorTree,
}

impl UpstreamPin {
    /// Return the expected on-disk SHA-256 digest for each vendored `.lean`
    /// source file (`patched_sha256` when patched, otherwise `sha256`).
    pub fn expected_source_digests(&self) -> BTreeMap<String, String> {
        self.vendor_tree
            .files
            .iter()
            .map(|entry| {
                let sha = entry
                    .patched_sha256
                    .as_deref()
                    .unwrap_or(&entry.sha256)
                    .to_string();
                (entry.path.clone(), sha)
            })
            .collect()
    }
}

/// Pinned upstream commit hashes inside `UPSTREAM_PIN.json`.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct UpstreamSubPins {
    pub aes_commit: String,
    pub miri_commit: String,
    pub rustc_apfloat_commit: String,
    pub rustc_commit: String,
    pub source_lock_sha256: String,
}

/// Record for one consumer-side patched file in `UPSTREAM_PIN.json`.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PatchedMiriFile {
    pub path: String,
    pub upstream_sha256: String,
    pub patched_sha256: String,
    pub rationale: String,
}

/// Record for one compiled `Miri.*` module in `execution_machine_closure`.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MiriClosureEntry {
    pub module: String,
    pub path: String,
    pub olean_sha256: String,
    #[serde(default)]
    pub olean_server_sha256: Option<String>,
    #[serde(default)]
    pub olean_private_sha256: Option<String>,
}

/// File path and SHA-256 entry in `vendor_tree` or `vendor_aux_files`.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VendorFileEntry {
    pub path: String,
    pub sha256: String,
    #[serde(default)]
    pub patched_sha256: Option<String>,
}

/// Full `.lean` file manifest in `UPSTREAM_PIN.json`.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VendorTree {
    pub file_count: usize,
    pub files: Vec<VendorFileEntry>,
    pub manifest_sha256: String,
}

/// Verify `vendor/lean-miri/UPSTREAM_PIN.json` and every file on disk under
/// `vendor_root`.
pub fn verify_upstream_pin(vendor_root: &Path) -> Result<UpstreamPin, Failure> {
    let phase = "miri-pin";
    if let Some(parent) = vendor_root.parent()
        && parent.file_name().and_then(|s| s.to_str()) == Some("vendor")
    {
        let parent_meta = fs::symlink_metadata(parent).map_err(|_| {
            Failure::policy(
                phase,
                format!("expected regular vendor directory: {}", parent.display()),
            )
        })?;
        if parent_meta.file_type().is_symlink() || !parent_meta.file_type().is_dir() {
            return Err(Failure::policy(
                phase,
                format!("expected regular vendor directory: {}", parent.display()),
            ));
        }
    }
    let root_meta = fs::symlink_metadata(vendor_root).map_err(|_| {
        Failure::policy(
            phase,
            format!(
                "expected regular vendor/lean-miri directory: {}",
                vendor_root.display()
            ),
        )
    })?;
    if root_meta.file_type().is_symlink() || !root_meta.file_type().is_dir() {
        return Err(Failure::policy(
            phase,
            format!(
                "expected regular vendor/lean-miri directory: {}",
                vendor_root.display()
            ),
        ));
    }
    let pin_path = vendor_root.join("UPSTREAM_PIN.json");
    let pin_meta = fs::symlink_metadata(&pin_path).map_err(|_| {
        Failure::policy(
            phase,
            format!("missing UPSTREAM_PIN.json: {}", pin_path.display()),
        )
    })?;
    if pin_meta.file_type().is_symlink() || !pin_meta.file_type().is_file() {
        return Err(Failure::policy(
            phase,
            format!(
                "expected regular file for UPSTREAM_PIN.json: {}",
                pin_path.display()
            ),
        ));
    }
    let pin_bytes = fs::read(&pin_path)
        .map_err(|e| Failure::operational(phase, format!("cannot read UPSTREAM_PIN.json: {e}")))?;
    let pin_sha = sha256_bytes(&pin_bytes);
    if !pin_sha.eq_ignore_ascii_case(LOCKED_UPSTREAM_PIN_SHA256) {
        return Err(Failure::policy(
            phase,
            format!(
                "UPSTREAM_PIN.json SHA-256 differs from locked digest: expected {LOCKED_UPSTREAM_PIN_SHA256}, got {pin_sha}"
            ),
        ));
    }
    verify_upstream_pin_bytes(vendor_root, &pin_bytes)
}

/// Parse and verify `UPSTREAM_PIN.json` bytes and every file on disk under
/// `vendor_root` after [`verify_upstream_pin`] has authenticated `pin_bytes`
/// against [`LOCKED_UPSTREAM_PIN_SHA256`].
fn verify_upstream_pin_bytes(vendor_root: &Path, pin_bytes: &[u8]) -> Result<UpstreamPin, Failure> {
    let phase = "miri-pin";
    let pin: UpstreamPin = serde_json::from_slice(pin_bytes)
        .map_err(|e| Failure::policy(phase, format!("malformed UPSTREAM_PIN.json: {e}")))?;

    if pin.schema_version != 2 {
        return Err(Failure::policy(
            phase,
            format!(
                "unsupported UPSTREAM_PIN.json schema_version: {}",
                pin.schema_version
            ),
        ));
    }
    if pin.commit != LOCKED_MIRI_COMMIT {
        return Err(Failure::policy(
            phase,
            format!(
                "UPSTREAM_PIN.json commit mismatch: expected {LOCKED_MIRI_COMMIT}, got {}",
                pin.commit
            ),
        ));
    }
    if pin.build_lean_toolchain != TOOLCHAIN {
        return Err(Failure::policy(
            phase,
            format!(
                "UPSTREAM_PIN.json build_lean_toolchain mismatch: expected {TOOLCHAIN}, got {}",
                pin.build_lean_toolchain
            ),
        ));
    }

    // Verify `patched_files` against the closed allowlist.
    let mut patched_map: BTreeMap<&str, &PatchedMiriFile> = BTreeMap::new();
    for pf in &pin.patched_files {
        if !LOCKED_PATCHED_MIRI_FILES.contains(&pf.path.as_str()) {
            return Err(Failure::policy(
                phase,
                format!(
                    "unauthorized patched file in UPSTREAM_PIN.json: {}",
                    pf.path
                ),
            ));
        }
        if !is_sha256_hex(&pf.upstream_sha256)
            || !is_sha256_hex(&pf.patched_sha256)
            || pf.upstream_sha256.eq_ignore_ascii_case(&pf.patched_sha256)
            || pf.rationale.trim().is_empty()
        {
            return Err(Failure::policy(
                phase,
                format!("invalid patched_files record for {}", pf.path),
            ));
        }
        if patched_map.insert(pf.path.as_str(), pf).is_some() {
            return Err(Failure::policy(
                phase,
                format!("duplicate patched_files record for {}", pf.path),
            ));
        }
    }
    if patched_map.len() != LOCKED_PATCHED_MIRI_FILES.len() {
        return Err(Failure::policy(
            phase,
            "patched_files list in UPSTREAM_PIN.json does not match locked allowlist",
        ));
    }

    // Verify `vendor_tree` and `vendor_aux_files` against on-disk files.
    if pin.vendor_tree.files.is_empty()
        || pin.vendor_tree.files.len() != pin.vendor_tree.file_count
        || !is_sha256_hex(&pin.vendor_tree.manifest_sha256)
    {
        return Err(Failure::policy(
            phase,
            "invalid vendor_tree count or manifest_sha256 in UPSTREAM_PIN.json",
        ));
    }

    let mut expected_lean_files: BTreeMap<String, String> = BTreeMap::new();
    let mut manifest_buf = String::new();
    for entry in &pin.vendor_tree.files {
        if !is_clean_relative_path(&entry.path)
            || !entry.path.ends_with(".lean")
            || !is_sha256_hex(&entry.sha256)
        {
            return Err(Failure::policy(
                phase,
                format!("invalid vendor_tree entry: {}", entry.path),
            ));
        }
        let disk_sha = match (
            patched_map.get(entry.path.as_str()),
            entry.patched_sha256.as_deref(),
        ) {
            (Some(pf), Some(entry_patched)) => {
                if !pf.upstream_sha256.eq_ignore_ascii_case(&entry.sha256)
                    || !pf.patched_sha256.eq_ignore_ascii_case(entry_patched)
                {
                    return Err(Failure::policy(
                        phase,
                        format!(
                            "patched_sha256 mismatch between patched_files and vendor_tree for {}",
                            entry.path
                        ),
                    ));
                }
                entry_patched.to_string()
            }
            (None, None) => entry.sha256.clone(),
            _ => {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "inconsistent patched_sha256 annotation in vendor_tree for {}",
                        entry.path
                    ),
                ));
            }
        };
        if expected_lean_files
            .insert(entry.path.clone(), disk_sha)
            .is_some()
        {
            return Err(Failure::policy(
                phase,
                format!("duplicate vendor_tree entry: {}", entry.path),
            ));
        }
        manifest_buf.push_str(&format!("{}  {}\n", entry.sha256, entry.path));
    }
    let computed_manifest = sha256_bytes(manifest_buf.as_bytes());
    if !computed_manifest.eq_ignore_ascii_case(&pin.vendor_tree.manifest_sha256) {
        return Err(Failure::policy(
            phase,
            format!(
                "vendor_tree manifest_sha256 mismatch: expected {}, got {computed_manifest}",
                pin.vendor_tree.manifest_sha256
            ),
        ));
    }

    let mut expected_aux_files: BTreeMap<String, String> = BTreeMap::new();
    for entry in &pin.vendor_aux_files {
        if !is_clean_relative_path(&entry.path)
            || entry.path.ends_with(".lean")
            || entry.path == "UPSTREAM_PIN.json"
            || !is_sha256_hex(&entry.sha256)
        {
            return Err(Failure::policy(
                phase,
                format!("invalid vendor_aux_files entry: {}", entry.path),
            ));
        }
        if expected_aux_files
            .insert(entry.path.clone(), entry.sha256.clone())
            .is_some()
        {
            return Err(Failure::policy(
                phase,
                format!("duplicate vendor_aux_files entry: {}", entry.path),
            ));
        }
    }

    // Walk `vendor_root` without following symlinks and verify that on-disk
    // files match `expected_lean_files`, `expected_aux_files`, and
    // `UPSTREAM_PIN.json` with zero untracked files or compiled artifacts.
    let mut seen_lean = BTreeSet::new();
    let mut seen_aux = BTreeSet::new();
    for entry_res in WalkDir::new(vendor_root).follow_links(false) {
        let entry = entry_res.map_err(|e| Failure::operational(phase, e.to_string()))?;
        let path = entry.path();
        if path == vendor_root {
            continue;
        }
        let ft = entry.file_type();
        if ft.is_symlink() {
            return Err(Failure::policy(
                phase,
                format!("symlink forbidden in vendor/lean-miri: {}", path.display()),
            ));
        }
        if ft.is_dir() {
            continue;
        }
        if !ft.is_file() {
            return Err(Failure::policy(
                phase,
                format!("non-regular file in vendor/lean-miri: {}", path.display()),
            ));
        }
        let rel = path
            .strip_prefix(vendor_root)
            .map_err(|e| Failure::operational(phase, e.to_string()))?;
        let rel_str = rel
            .components()
            .map(|c| c.as_os_str().to_string_lossy())
            .collect::<Vec<_>>()
            .join("/");
        if rel_str == "UPSTREAM_PIN.json" {
            continue;
        }
        let actual_sha = sha256_file(path, phase)?;
        if rel_str.ends_with(".lean") {
            let Some(exp_sha) = expected_lean_files.get(&rel_str) else {
                return Err(Failure::policy(
                    phase,
                    format!("unlisted Lean file in vendor/lean-miri: {rel_str}"),
                ));
            };
            if !actual_sha.eq_ignore_ascii_case(exp_sha) {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "vendor file SHA-256 mismatch for {rel_str}: expected {exp_sha}, got {actual_sha}"
                    ),
                ));
            }
            seen_lean.insert(rel_str);
        } else {
            let Some(exp_sha) = expected_aux_files.get(&rel_str) else {
                return Err(Failure::policy(
                    phase,
                    format!("unlisted file in vendor/lean-miri: {rel_str}"),
                ));
            };
            if !actual_sha.eq_ignore_ascii_case(exp_sha) {
                return Err(Failure::policy(
                    phase,
                    format!(
                        "vendor aux file SHA-256 mismatch for {rel_str}: expected {exp_sha}, got {actual_sha}"
                    ),
                ));
            }
            seen_aux.insert(rel_str);
        }
    }
    if seen_lean.len() != expected_lean_files.len() {
        return Err(Failure::policy(
            phase,
            "missing pinned .lean file in vendor/lean-miri",
        ));
    }
    if seen_aux.len() != expected_aux_files.len() {
        return Err(Failure::policy(
            phase,
            "missing pinned auxiliary file in vendor/lean-miri",
        ));
    }

    // Verify `execution_machine_closure` (when present) and ensure
    // `Miri.Input.NativeMathHost` (which contains `@[extern]` host math
    // bindings) is excluded from the correspondence slice.
    let mut seen_closure_mods = BTreeSet::new();
    for entry in &pin.execution_machine_closure {
        let expected_rel = format!("{}.lean", entry.module.replace('.', "/"));
        if !entry.module.starts_with("Miri.")
            || entry.module == "Miri.Input.NativeMathHost"
            || entry.module == "Miri"
            || entry.path != expected_rel
            || !expected_lean_files.contains_key(&entry.path)
            || !is_sha256_hex(&entry.olean_sha256)
            || entry
                .olean_server_sha256
                .as_deref()
                .is_some_and(|h| !is_sha256_hex(h))
            || entry
                .olean_private_sha256
                .as_deref()
                .is_some_and(|h| !is_sha256_hex(h))
            || !seen_closure_mods.insert(entry.module.as_str())
        {
            return Err(Failure::policy(
                phase,
                format!(
                    "invalid execution_machine_closure entry for {}",
                    entry.module
                ),
            ));
        }
    }
    if pin.execution_machine_closure.len() != 160 {
        return Err(Failure::policy(
            phase,
            format!(
                "expected 160 execution_machine_closure entries in UPSTREAM_PIN.json, got {}",
                pin.execution_machine_closure.len()
            ),
        ));
    }
    if !seen_closure_mods.contains("Miri.Interpreter.ExecutionMachine") {
        return Err(Failure::policy(
            phase,
            "execution_machine_closure is missing Miri.Interpreter.ExecutionMachine",
        ));
    }

    Ok(pin)
}

/// Topologically sort the module set `pending` according to `imports_map`,
/// returning a policy rejection (`code == 1`) with `cycle_msg` if `pending`
/// contains an import cycle.
///
/// Emit each ready layer in sorted order. Imports outside `pending` are assumed
/// to be available.
///
/// Use iteration so deep import chains do not consume one Rust stack frame
/// per module. Sorted layers keep staging and checking order deterministic.
fn topo_sort_modules(
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
                imports_map[*module]
                    .iter()
                    .all(|edge| !pending.contains(&edge.module))
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
                (
                    module.to_string(),
                    dependencies.iter().map(|name| import(name)).collect(),
                )
            })
            .collect();
        topo_sort_modules(
            imports.keys().cloned().collect(),
            &imports,
            "fixture import cycle",
        )
    }

    #[test]
    fn empty_module_set_has_no_ordering_work() {
        assert_eq!(sort(&[]).unwrap(), Vec::<String>::new());
    }

    #[test]
    fn independent_roots_are_sorted() {
        assert_eq!(
            sort(&[("Z", &[]), ("A", &[]), ("M", &[])]).unwrap(),
            ["A", "M", "Z"]
        );
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
            (
                "Trusted.Child".to_string(),
                vec![import("Trusted.Root"), import("External.Ready")],
            ),
            (
                "Trusted.Root".to_string(),
                vec![import("Init.Prelude"), import("Init.Notation")],
            ),
            ("External.Ready".to_string(), Vec::new()),
        ]);
        assert_eq!(
            topo_sort_modules(
                BTreeSet::from(["Trusted.Child".to_string(), "Trusted.Root".to_string(),]),
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
        assert_eq!(
            sort(&[("Root", &[]), ("A", &["B"]), ("B", &["A"])]),
            expected
        );
    }

    #[test]
    fn deep_dependency_chain_fits_a_small_thread_stack() {
        let modules: Vec<_> = (0..512).map(|i| format!("Module{i:03}")).collect();
        let imports = modules
            .iter()
            .enumerate()
            .map(|(index, module)| {
                let dependencies = if index == 0 {
                    Vec::new()
                } else {
                    vec![import(&modules[index - 1])]
                };
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

#[cfg(all(test, unix))]
mod process_tests {
    use super::*;

    fn shell_checker(checkout: &Path) -> Checker {
        Checker::new_with_env(checkout, Some(Path::new("/bin/sh")), []).unwrap()
    }

    #[test]
    fn keeps_staging_private_at_creation_and_after_reset() {
        const PROBE: &str = "ANNEAL_AUDIT_STAGE_PERMISSION_PROBE";
        if env::var_os(PROBE).is_some() {
            use std::os::unix::fs::PermissionsExt;

            let checkout = tempfile::tempdir().unwrap();
            let mut checker = shell_checker(checkout.path());
            assert_eq!(
                fs::metadata(&checker.stage).unwrap().permissions().mode() & 0o777,
                0o700,
                "initial staging directory exposes its contents to other users"
            );
            fs::write(checker.stage.join("input"), b"private source bytes").unwrap();
            checker.reset_stage().unwrap();
            assert_eq!(
                fs::metadata(&checker.stage).unwrap().permissions().mode() & 0o777,
                0o700,
                "reset staging directory exposes its contents to other users"
            );
            assert!(!checker.stage.join("input").exists());
            return;
        }

        // Change only the child's umask; other tests may run concurrently.
        let output = Command::new("/bin/sh")
            .args(["-c", "umask 022 && exec \"$@\"", "stage-permissions"])
            .arg(env::current_exe().unwrap())
            .args([
                "--exact",
                "process_tests::keeps_staging_private_at_creation_and_after_reset",
                "--nocapture",
            ])
            .env(PROBE, "1")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "permission probe failed:\n{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(String::from_utf8_lossy(&output.stdout).contains("1 passed"));
    }

    #[test]
    fn captures_successful_child_output() {
        let checkout = tempfile::tempdir().unwrap();
        let checker = shell_checker(checkout.path());
        let output = checker
            .launch_lean(&[
                "-c".to_string(),
                "printf 'stdout\\000\\377'; printf 'stderr\\000\\376' >&2".to_string(),
            ])
            .unwrap();

        assert!(output.status.success());
        assert_eq!(output.stdout, b"stdout\0\xff");
        assert_eq!(output.stderr, b"stderr\0\xfe");
    }

    #[test]
    fn preserves_failed_child_status_and_raw_streams() {
        let checkout = tempfile::tempdir().unwrap();
        let checker = shell_checker(checkout.path());
        let output = checker
            .launch_lean(&[
                "-c".to_string(),
                "printf 'stdout\\000\\377'; printf 'stderr\\000\\376' >&2; exit 37".to_string(),
            ])
            .unwrap();

        assert_eq!(output.status.code(), Some(37));
        assert_eq!(output.stdout, b"stdout\0\xff");
        assert_eq!(output.stderr, b"stderr\0\xfe");
    }

    #[test]
    fn returns_io_error_when_child_cannot_launch() {
        let checkout = tempfile::tempdir().unwrap();
        let missing = checkout.path().join("missing-lean");
        let checker = Checker::new_with_env(checkout.path(), Some(&missing), []).unwrap();

        let error = checker.launch_lean(&[]).unwrap_err();

        assert_eq!(error.kind(), io::ErrorKind::NotFound);
    }

    #[test]
    fn preserves_arguments_and_stage_working_directory() {
        let checkout = tempfile::tempdir().unwrap();
        let checker = shell_checker(checkout.path());
        fs::write(checker.stage.join("marker"), b"from-stage\n").unwrap();
        let output = checker
            .launch_lean(&[
                "-c".to_string(),
                "IFS= read -r marker < marker; printf '%s\\000' \"$marker\" \"$@\"".to_string(),
                "fixture".to_string(),
                "space separated".to_string(),
                String::new(),
                "$HOME;*".to_string(),
                "line\nbreak".to_string(),
            ])
            .unwrap();

        assert!(output.status.success());
        assert_eq!(
            output.stdout,
            b"from-stage\0space separated\0\0$HOME;*\0line\nbreak\0"
        );
        assert!(output.stderr.is_empty());
    }

    #[test]
    fn launches_with_only_the_filtered_environment() {
        let checkout = tempfile::tempdir().unwrap();
        let checker = Checker::new_with_env(
            checkout.path(),
            Some(Path::new("/usr/bin/env")),
            [
                ("HOME".to_string(), "/selected/home".to_string()),
                ("TMPDIR".to_string(), "/selected/tmp".to_string()),
                ("LANG".to_string(), "C".to_string()),
                ("LC_ALL".to_string(), "C".to_string()),
                ("PATH".to_string(), "/unselected/bin".to_string()),
                ("LEAN_PATH".to_string(), "/unselected/lean".to_string()),
                ("ELAN_TOOLCHAIN".to_string(), "unselected".to_string()),
                ("LD_PRELOAD".to_string(), "/unselected.so".to_string()),
            ],
        )
        .unwrap();
        let output = checker.launch_lean(&[]).unwrap();

        assert!(output.status.success());
        let environment = String::from_utf8(output.stdout).unwrap();
        assert_eq!(
            environment.lines().collect::<BTreeSet<_>>(),
            BTreeSet::from([
                "HOME=/selected/home",
                "LANG=C",
                "LC_ALL=C",
                "PATH=/usr/bin:/bin",
                "TMPDIR=/selected/tmp",
            ])
        );
        assert!(output.stderr.is_empty());
    }

    #[cfg(unix)]
    #[test]
    fn rejects_symlinks_in_miri_cache_dir() {
        use std::os::unix::fs::symlink;

        let tmp = tempfile::tempdir().unwrap();
        let src = tmp.path().join("staged.olean");
        fs::write(&src, b"compiled-olean").unwrap();
        let outside = tmp.path().join("outside");
        fs::create_dir_all(&outside).unwrap();
        let victim = outside.join("victim.olean");
        fs::write(&victim, b"keep-me").unwrap();

        // 1. Symlinked cache root (with/without trailing slash) is rejected.
        let sym_root = tmp.path().join("sym-cache");
        symlink(&outside, &sym_root).unwrap();
        assert_eq!(
            write_cache_file(&src, &sym_root, "Miri/Hex.olean", "miri-pin")
                .unwrap_err()
                .code,
            1
        );
        let sym_root_slash = PathBuf::from(format!("{}/", sym_root.display()));
        assert_eq!(
            prepare_nosymlink_cache_path(&sym_root_slash, "Miri/Hex.olean", false, "miri-pin")
                .unwrap_err()
                .code,
            1
        );

        // 2. Symlinked intermediate subdir inside `cache_dir` is rejected.
        let cache = tmp.path().join("real-cache");
        fs::create_dir_all(&cache).unwrap();
        symlink(&outside, cache.join("Miri")).unwrap();
        assert_eq!(
            write_cache_file(&src, &cache, "Miri/Hex.olean", "miri-pin")
                .unwrap_err()
                .code,
            1
        );
        assert!(!outside.join("Hex.olean").exists());
        fs::remove_file(cache.join("Miri")).unwrap();

        // 3. Symlinked (existing or dangling) leaf cache entry is rejected on
        // both write and stale-companion removal without touching the target.
        fs::create_dir_all(cache.join("Miri")).unwrap();
        symlink(&victim, cache.join("Miri/Hex.olean")).unwrap();
        assert_eq!(
            write_cache_file(&src, &cache, "Miri/Hex.olean", "miri-pin")
                .unwrap_err()
                .code,
            1
        );
        assert_eq!(
            remove_cache_file(&cache, "Miri/Hex.olean", "miri-pin")
                .unwrap_err()
                .code,
            1
        );
        assert_eq!(fs::read(&victim).unwrap(), b"keep-me");
    }

    #[test]
    fn validates_correspondence_replay_fields_fail_closed() {
        let obj = |v: Json| v.as_object().unwrap().clone();

        // Missing or false `miriReplay` fails closed with policy code 1.
        let err_missing =
            validate_correspondence_report(&obj(json!({"miriReplayedDeclarations": 10})), true)
                .unwrap_err();
        assert_eq!(err_missing.code, 1);
        let err_false = validate_correspondence_report(
            &obj(json!({"miriReplay": false, "miriReplayedDeclarations": 10})),
            true,
        )
        .unwrap_err();
        assert_eq!(err_false.code, 1);

        // Missing `miriReplayedDeclarations` fails closed (operational code 2).
        let err_no_count =
            validate_correspondence_report(&obj(json!({"miriReplay": true})), true).unwrap_err();
        assert_eq!(err_no_count.code, 2);

        // Zero replayed declarations fails closed when vendor modules are
        // present.
        let err_zero = validate_correspondence_report(
            &obj(json!({"miriReplay": true, "miriReplayedDeclarations": 0})),
            true,
        )
        .unwrap_err();
        assert_eq!(err_zero.code, 1);

        // Zero is permitted only when `vendor_miri` is empty.
        validate_correspondence_report(
            &obj(json!({"miriReplay": true, "miriReplayedDeclarations": 0})),
            false,
        )
        .unwrap();

        // Positive replayed count with `miriReplay == true` succeeds.
        validate_correspondence_report(
            &obj(json!({"miriReplay": true, "miriReplayedDeclarations": 38728})),
            true,
        )
        .unwrap();
    }

    #[test]
    fn rejects_unauthorized_patched_files_and_bad_closure_in_pin_bytes() {
        let vendor_root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../vendor/lean-miri");
        let orig_pin_bytes = fs::read(vendor_root.join("UPSTREAM_PIN.json")).unwrap();

        // Unauthorized `patched_files` entry, mismatched `patched_sha256`
        // between `patched_files` and `vendor_tree`, and missing
        // `patched_sha256` annotation in `vendor_tree` are rejected even if
        // the outer pin digest check has already passed.
        let mut pin_json: Json = serde_json::from_slice(&orig_pin_bytes).unwrap();
        pin_json["patched_files"]
            .as_array_mut()
            .unwrap()
            .push(json!({
                "path": "Miri.lean",
                "upstream_sha256": "0000000000000000000000000000000000000000000000000000000000000000",
                "patched_sha256": "1111111111111111111111111111111111111111111111111111111111111111",
                "rationale": "unauthorized patch"
            }));
        let err_unauth_patch =
            verify_upstream_pin_bytes(&vendor_root, &serde_json::to_vec(&pin_json).unwrap())
                .unwrap_err();
        assert_eq!(err_unauth_patch.code, 1);
        assert!(
            err_unauth_patch
                .message
                .contains("unauthorized patched file in UPSTREAM_PIN.json: Miri.lean"),
            "unexpected error: {err_unauth_patch}"
        );

        let mut pin_mismatch_json: Json = serde_json::from_slice(&orig_pin_bytes).unwrap();
        pin_mismatch_json["patched_files"][0]["patched_sha256"] =
            json!("2222222222222222222222222222222222222222222222222222222222222222");
        let err_patch_mismatch = verify_upstream_pin_bytes(
            &vendor_root,
            &serde_json::to_vec(&pin_mismatch_json).unwrap(),
        )
        .unwrap_err();
        assert_eq!(err_patch_mismatch.code, 1);
        assert!(
            err_patch_mismatch
                .message
                .contains("patched_sha256 mismatch between patched_files and vendor_tree"),
            "unexpected error: {err_patch_mismatch}"
        );

        let mut pin_missing_annot_json: Json = serde_json::from_slice(&orig_pin_bytes).unwrap();
        for entry in pin_missing_annot_json["vendor_tree"]["files"]
            .as_array_mut()
            .unwrap()
        {
            if entry["path"].as_str() == Some("Miri/Interpreter/Call.lean") {
                entry.as_object_mut().unwrap().remove("patched_sha256");
            }
        }
        let err_missing_annot = verify_upstream_pin_bytes(
            &vendor_root,
            &serde_json::to_vec(&pin_missing_annot_json).unwrap(),
        )
        .unwrap_err();
        assert_eq!(err_missing_annot.code, 1);
        assert!(
            err_missing_annot.message.contains(
                "inconsistent patched_sha256 annotation in vendor_tree for Miri/Interpreter/Call.lean"
            ),
            "unexpected error: {err_missing_annot}"
        );

        // Forbidden `Miri.Input.NativeMathHost` closure entry is rejected.
        let mut pin_closure_json: Json = serde_json::from_slice(&orig_pin_bytes).unwrap();
        pin_closure_json["execution_machine_closure"] = json!([{
            "module": "Miri.Input.NativeMathHost",
            "path": "Miri/Input/NativeMathHost.lean",
            "olean_sha256": "0000000000000000000000000000000000000000000000000000000000000000"
        }]);
        let err_bad_closure = verify_upstream_pin_bytes(
            &vendor_root,
            &serde_json::to_vec(&pin_closure_json).unwrap(),
        )
        .unwrap_err();
        assert_eq!(err_bad_closure.code, 1);
        assert!(
            err_bad_closure
                .message
                .contains("invalid execution_machine_closure entry for Miri.Input.NativeMathHost"),
            "unexpected error: {err_bad_closure}"
        );

        // Empty `execution_machine_closure` is rejected.
        pin_closure_json["execution_machine_closure"] = json!([]);
        let err_empty_closure = verify_upstream_pin_bytes(
            &vendor_root,
            &serde_json::to_vec(&pin_closure_json).unwrap(),
        )
        .unwrap_err();
        assert_eq!(err_empty_closure.code, 1);
        assert!(
            err_empty_closure.message.contains(
                "expected 160 execution_machine_closure entries in UPSTREAM_PIN.json, got 0"
            ),
            "unexpected error: {err_empty_closure}"
        );
    }

    #[test]
    fn bwrap_miri_compile_args_enforce_isolation_and_readonly_inputs() {
        let args: Vec<String> = build_bwrap_miri_compile_args(
            Path::new("/opt/lean-4.34.1"),
            Path::new("/toolchain/bin/lean"),
            Path::new("/tmp/stage/src/vendor-miri"),
            Path::new("/tmp/stage/miri-lib"),
            Path::new("/tmp/miri-out-123"),
            "Miri/Memory/Identity.olean",
            "Miri/Memory/Identity.lean",
        )
        .into_iter()
        .map(|a| a.to_string_lossy().into_owned())
        .collect();

        for required in [
            "--unshare-all",
            "--die-with-parent",
            "--new-session",
            "--clearenv",
            "--tmpfs",
            "--chdir",
        ] {
            assert!(
                args.iter().any(|a| a == required),
                "missing required sandbox flag {required}: {args:?}"
            );
        }

        // Only `module_out_dir` may be mounted read-write via `--bind`; all
        // toolchain, source, and verified `.olean` inputs must be `--ro-bind`.
        let rw_binds: Vec<(&str, &str)> = args
            .windows(3)
            .filter(|w| w[0] == "--bind")
            .map(|w| (w[1].as_str(), w[2].as_str()))
            .collect();
        assert_eq!(rw_binds, vec![("/tmp/miri-out-123", "/work/out")]);

        let ro_binds: Vec<(&str, &str)> = args
            .windows(3)
            .filter(|w| w[0] == "--ro-bind")
            .map(|w| (w[1].as_str(), w[2].as_str()))
            .collect();
        assert!(ro_binds.contains(&("/opt/lean-4.34.1", "/toolchain")));
        assert!(ro_binds.contains(&("/tmp/stage/src/vendor-miri", "/work/src/vendor-miri")));
        assert!(ro_binds.contains(&("/tmp/stage/miri-lib", "/work/miri-lib")));
        assert!(
            !args.iter().any(|a| a == "/usr/bin" || a == "/bin"),
            "host shell/utility directories must not be mounted: {args:?}"
        );
    }

    #[test]
    fn sandbox_output_check_allows_only_expected_regular_files() {
        let out_dir = tempfile::Builder::new()
            .prefix("anneal-sandbox-out-unit-")
            .tempdir()
            .unwrap();
        let mod_dir = out_dir.path().join("Miri/Memory");
        fs::create_dir_all(&mod_dir).unwrap();
        fs::write(mod_dir.join("QSortProof.olean"), b"olean").unwrap();
        fs::write(mod_dir.join("QSortProof.olean.server"), b"srv").unwrap();
        fs::write(mod_dir.join("QSortProof.olean.private"), b"priv").unwrap();
        fs::write(mod_dir.join("QSortProof.ir"), b"ir").unwrap();
        fs::write(mod_dir.join("QSortProof.ir.sig"), b"irsig").unwrap();

        let non_module_expected = BTreeSet::from(["Miri/Memory/QSortProof.olean".to_string()]);
        let err_non_mod = verify_no_unexpected_sandbox_outputs(
            out_dir.path(),
            &non_module_expected,
            "Miri/Memory/QSortProof.olean",
            "Miri.Memory.QSortProof",
        )
        .unwrap_err();
        assert_eq!(err_non_mod.code, 1);
        assert!(
            err_non_mod
                .message
                .contains("unexpected file in sandboxed Miri output"),
            "unexpected error: {err_non_mod}"
        );

        let module_expected = BTreeSet::from([
            "Miri/Memory/QSortProof.olean".to_string(),
            "Miri/Memory/QSortProof.olean.server".to_string(),
            "Miri/Memory/QSortProof.olean.private".to_string(),
            "Miri/Memory/QSortProof.ir".to_string(),
            "Miri/Memory/QSortProof.ir.sig".to_string(),
        ]);
        verify_no_unexpected_sandbox_outputs(
            out_dir.path(),
            &module_expected,
            "Miri/Memory/QSortProof.olean",
            "Miri.Memory.QSortProof",
        )
        .unwrap();

        #[cfg(unix)]
        {
            fs::remove_file(mod_dir.join("QSortProof.ir")).unwrap();
            std::os::unix::fs::symlink(
                mod_dir.join("QSortProof.olean"),
                mod_dir.join("QSortProof.ir"),
            )
            .unwrap();
            let err_sym = verify_no_unexpected_sandbox_outputs(
                out_dir.path(),
                &module_expected,
                "Miri/Memory/QSortProof.olean",
                "Miri.Memory.QSortProof",
            )
            .unwrap_err();
            assert_eq!(err_sym.code, 1);
            assert!(
                err_sym
                    .message
                    .contains("symlink forbidden in sandboxed Miri output"),
                "unexpected error: {err_sym}"
            );
        }
    }

    #[test]
    fn rejects_malformed_patched_files_and_vendor_tree_annotations_in_pin_bytes() {
        let vendor_root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../vendor/lean-miri");
        let orig_pin_bytes = fs::read(vendor_root.join("UPSTREAM_PIN.json")).unwrap();

        // (a) A `patched_sha256` annotation on a non-allowlisted file in
        // `vendor_tree` is rejected.
        let mut pin_extra_annot: Json = serde_json::from_slice(&orig_pin_bytes).unwrap();
        let mut found_miri = false;
        for entry in pin_extra_annot["vendor_tree"]["files"]
            .as_array_mut()
            .unwrap()
        {
            if entry["path"].as_str() == Some("Miri.lean") {
                entry.as_object_mut().unwrap().insert(
                    "patched_sha256".to_string(),
                    json!("3333333333333333333333333333333333333333333333333333333333333333"),
                );
                found_miri = true;
            }
        }
        assert!(found_miri, "Miri.lean must appear in vendor_tree.files");
        let err_extra_annot =
            verify_upstream_pin_bytes(&vendor_root, &serde_json::to_vec(&pin_extra_annot).unwrap())
                .unwrap_err();
        assert_eq!(err_extra_annot.code, 1);
        assert!(
            err_extra_annot
                .message
                .contains("inconsistent patched_sha256 annotation in vendor_tree for Miri.lean"),
            "unexpected error: {err_extra_annot}"
        );

        // (b) A dropped record / count mismatch in `patched_files` is
        // rejected.
        let mut pin_dropped: Json = serde_json::from_slice(&orig_pin_bytes).unwrap();
        pin_dropped["patched_files"].as_array_mut().unwrap().pop();
        let err_dropped =
            verify_upstream_pin_bytes(&vendor_root, &serde_json::to_vec(&pin_dropped).unwrap())
                .unwrap_err();
        assert_eq!(err_dropped.code, 1);
        assert!(
            err_dropped.message.contains(
                "patched_files list in UPSTREAM_PIN.json does not match locked allowlist"
            ),
            "unexpected error: {err_dropped}"
        );

        // (c) Duplicate records in `patched_files` are rejected.
        let mut pin_dup: Json = serde_json::from_slice(&orig_pin_bytes).unwrap();
        let first_record = pin_dup["patched_files"][0].clone();
        let first_path = first_record["path"].as_str().unwrap().to_string();
        pin_dup["patched_files"]
            .as_array_mut()
            .unwrap()
            .push(first_record);
        let err_dup =
            verify_upstream_pin_bytes(&vendor_root, &serde_json::to_vec(&pin_dup).unwrap())
                .unwrap_err();
        assert_eq!(err_dup.code, 1);
        assert!(
            err_dup
                .message
                .contains(&format!("duplicate patched_files record for {first_path}")),
            "unexpected error: {err_dup}"
        );

        // (d1) An invalid `patched_files` record with
        // `upstream_sha256 == patched_sha256` is rejected.
        let mut pin_same_sha: Json = serde_json::from_slice(&orig_pin_bytes).unwrap();
        let same_path = pin_same_sha["patched_files"][0]["path"]
            .as_str()
            .unwrap()
            .to_string();
        let upstream_sha = pin_same_sha["patched_files"][0]["upstream_sha256"].clone();
        pin_same_sha["patched_files"][0]["patched_sha256"] = upstream_sha;
        let err_same_sha =
            verify_upstream_pin_bytes(&vendor_root, &serde_json::to_vec(&pin_same_sha).unwrap())
                .unwrap_err();
        assert_eq!(err_same_sha.code, 1);
        assert!(
            err_same_sha
                .message
                .contains(&format!("invalid patched_files record for {same_path}")),
            "unexpected error: {err_same_sha}"
        );

        // (d2) An invalid `patched_files` record with empty/whitespace
        // `rationale` is rejected.
        let mut pin_blank_rationale: Json = serde_json::from_slice(&orig_pin_bytes).unwrap();
        let blank_path = pin_blank_rationale["patched_files"][0]["path"]
            .as_str()
            .unwrap()
            .to_string();
        pin_blank_rationale["patched_files"][0]["rationale"] = json!("   \t\n ");
        let err_blank_rationale = verify_upstream_pin_bytes(
            &vendor_root,
            &serde_json::to_vec(&pin_blank_rationale).unwrap(),
        )
        .unwrap_err();
        assert_eq!(err_blank_rationale.code, 1);
        assert!(
            err_blank_rationale
                .message
                .contains(&format!("invalid patched_files record for {blank_path}")),
            "unexpected error: {err_blank_rationale}"
        );

        // (e) A mismatch between `patched_files.upstream_sha256` and
        // `vendor_tree.files[].sha256` is rejected.
        let mut pin_upstream_mismatch: Json = serde_json::from_slice(&orig_pin_bytes).unwrap();
        let mismatch_path = pin_upstream_mismatch["patched_files"][0]["path"]
            .as_str()
            .unwrap()
            .to_string();
        pin_upstream_mismatch["patched_files"][0]["upstream_sha256"] =
            json!("4444444444444444444444444444444444444444444444444444444444444444");
        let err_upstream_mismatch = verify_upstream_pin_bytes(
            &vendor_root,
            &serde_json::to_vec(&pin_upstream_mismatch).unwrap(),
        )
        .unwrap_err();
        assert_eq!(err_upstream_mismatch.code, 1);
        assert!(
            err_upstream_mismatch.message.contains(&format!(
                "patched_sha256 mismatch between patched_files and vendor_tree for {mismatch_path}"
            )),
            "unexpected error: {err_upstream_mismatch}"
        );
    }
}
