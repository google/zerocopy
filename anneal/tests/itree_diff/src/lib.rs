// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Multi-step and multi-call observable-trace (`ITree`) differential testing
//! and deterministic fuzzing harness for Anneal (`anneal-itree-diff`).
//!
//! Coordinates 4 execution authorities from the non-TCB Zone-1 test ring:
//! 1. Host `rustc` at BOTH `-C opt-level=0` AND `-C opt-level=2` (`O0 == O2`
//!    parity on defined-behavior inputs; skipped when Miri detects UB).
//! 2. Miri with Tree Borrows (`-Zmiri-tree-borrows`) run first as the UB
//!    ground-truth oracle (emitting `DegradedNoMiri` when Miri is absent and
//!    failing closed under `--require-miri` / `ANNEAL_ITREE_REQUIRE_MIRI=1`).
//! 3. Lean 4 `Trusted.MirSemantics` trace driver (via `Anneal.MirTotal` at
//!    `mirTyBeqAt 64`) in both Strict Verbatim Mode (a) and Compositional
//!    Multi-Call ITree Mode (b).
//! 4. Optional pluggable `anneal-mir-eval` CLI/JSON adapter.

pub mod corpus;
pub mod fuzzer;
pub mod lean_trace_runner;
pub mod mir_eval_adapter;
pub mod miri_runner;
pub mod outcome;
pub mod rustc_runner;
pub mod shrink;
pub mod spec;
pub mod trace_observer;

use std::{
    collections::{BTreeMap, VecDeque},
    env,
    ffi::OsString,
    fmt,
    ops::Deref,
    path::{Component, Path, PathBuf},
    sync::{Arc, Mutex, OnceLock, Weak},
};

pub use corpus::filter_corpus_cases;
use serde::{Deserialize, Serialize};

use crate::{
    fuzzer::{FuzzProgram, generate_fuzz_batch},
    lean_trace_runner::{
        CapturedArtifacts, LeanTraceMode, LeanTraceSession, MetamorphicDualityReceipt,
    },
    mir_eval_adapter::{MirEvalAdapter, MirEvalAvailability},
    miri_runner::{MiriAvailability, MiriRunner},
    outcome::{
        AuthorityRunResult, CallerFrameLaw, ExpectedConservativeSpec, ExpectedUbSpec,
        MetamorphicStatus, SpineCompareMode, TerminalOutcome, TraceVerdict, UbFaultClass,
        classify_four_way_with_ub_guard, classify_ub_fault_detail, compare_ub_fault_results,
    },
    rustc_runner::{
        RustcDualResult, RustcRunner, compiler_matches_pinned_sysroot_with_suffix,
        sysroots_equivalent,
    },
    shrink::{
        ShrinkBudget, ShrinkFailureSignature, WitnessArtifact, shrink_fuzz_program_with_budget,
    },
    spec::{CaseCategory, ExpectedCaseClass, LeanProgramSpec, MetamorphicTwin, TraceTestCase},
    trace_observer::{EnvSchedule, ObservableEvent, ObservableSpine},
};

/// Resolved default cache directory path paired with an optional RAII
/// [`tempfile::TempDir`] owner so temporary fallback caches are automatically
/// removed when the configuration or engine drops rather than leaking across
/// CLI invocations.
#[derive(Clone, Debug)]
pub struct ResolvedCacheRoot {
    path: PathBuf,
    temp_guard: Option<Arc<tempfile::TempDir>>,
}

impl ResolvedCacheRoot {
    fn persistent(path: PathBuf) -> Self {
        Self { path, temp_guard: None }
    }

    fn temporary(guard: Arc<tempfile::TempDir>) -> Self {
        let path = guard.path().to_path_buf();
        Self { path, temp_guard: Some(guard) }
    }

    pub fn as_path(&self) -> &Path {
        &self.path
    }
}

impl Deref for ResolvedCacheRoot {
    type Target = Path;

    fn deref(&self) -> &Path {
        &self.path
    }
}

impl AsRef<Path> for ResolvedCacheRoot {
    fn as_ref(&self) -> &Path {
        &self.path
    }
}

impl PartialEq<PathBuf> for ResolvedCacheRoot {
    fn eq(&self, other: &PathBuf) -> bool {
        &self.path == other
    }
}

impl PartialEq<Path> for ResolvedCacheRoot {
    fn eq(&self, other: &Path) -> bool {
        self.path.as_path() == other
    }
}

impl PartialEq<&Path> for ResolvedCacheRoot {
    fn eq(&self, other: &&Path) -> bool {
        self.path.as_path() == *other
    }
}

impl fmt::Display for ResolvedCacheRoot {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.path.display().fmt(f)
    }
}

/// Top-level configuration for a differential testing or fuzzing run.
#[derive(Clone, Debug)]
pub struct DifferentialConfig {
    pub anneal_root: PathBuf,
    pub cache_root: PathBuf,
    pub enable_miri: bool,
    pub require_miri: bool,
    pub enable_lean: bool,
    pub lean_mode: LeanTraceMode,
    pub check_metamorphic_duality: bool,
    pub shrink_on_divergence: bool,
    pub witness_dir: Option<PathBuf>,
    _temp_cache_guard: Option<Arc<tempfile::TempDir>>,
}

impl DifferentialConfig {
    pub fn for_workspace(anneal_root: PathBuf) -> Self {
        Self::for_workspace_with_cache(anneal_root, None)
    }

    pub fn for_workspace_with_cache(
        anneal_root: PathBuf,
        explicit_cache_dir: Option<PathBuf>,
    ) -> Self {
        let anneal_root = normalize_configured_path(&anneal_root);
        let (cache_root, temp_cache_guard) = match explicit_cache_dir {
            Some(dir) => (normalize_configured_path(&dir), None),
            None => {
                let resolved = resolve_default_cache_root(&anneal_root);
                (resolved.path, resolved.temp_guard)
            }
        };
        let require_miri = env::var("ANNEAL_ITREE_REQUIRE_MIRI").ok().as_deref() == Some("1");
        Self {
            anneal_root,
            cache_root,
            enable_miri: true,
            require_miri,
            enable_lean: true,
            lean_mode: LeanTraceMode::CompositionalITree,
            check_metamorphic_duality: true,
            shrink_on_divergence: true,
            witness_dir: None,
            _temp_cache_guard: temp_cache_guard,
        }
    }
}

/// Resolve the default content-keyed harness cache directory outside the
/// checkout so `ci-core` read-only `/work` sandboxes never fail with `EROFS`
/// and local runs never bloat in-checkout `anneal/target/`.
pub fn resolve_default_cache_root(anneal_root: &Path) -> ResolvedCacheRoot {
    resolve_default_cache_root_with_env(anneal_root, |k| env::var_os(k), &env::temp_dir())
}

/// Environment-injected variant of [`resolve_default_cache_root`] for
/// deterministic unit testing without mutating process-wide environment state.
///
/// Precedence:
/// 1. Explicit `ANNEAL_ITREE_CACHE_DIR` override (if non-empty, normalized
///    against the caller's working directory).
/// 2. `CARGO_TARGET_TMPDIR` (`<dir>/anneal-itree-diff-cache`) when resolved
///    outside [`checkout_boundary_root`] and writable.
/// 3. `CARGO_TARGET_DIR` (`<dir>/anneal-itree-diff-cache`) when resolved
///    outside [`checkout_boundary_root`] and writable (`ci-core`
///    `SCRATCH_ROOT`).
/// 4. User-private `XDG_CACHE_HOME` (`<dir>/anneal-itree-diff`) or `HOME`
///    (`<home>/.cache/anneal-itree-diff`) when resolved outside
///    [`checkout_boundary_root`] and writable.
/// 5. Scope-owned `O_EXCL` (`0700`) random directory created via
///    [`tempfile::Builder`] inside an out-of-checkout temp directory and
///    automatically removed when the owning [`ResolvedCacheRoot`] /
///    [`DifferentialConfig`] drops.
pub fn resolve_default_cache_root_with_env(
    anneal_root: &Path,
    get_env: impl Fn(&str) -> Option<std::ffi::OsString>,
    sys_temp_dir: &Path,
) -> ResolvedCacheRoot {
    if let Some(explicit) = get_env("ANNEAL_ITREE_CACHE_DIR").filter(|v| !v.is_empty()) {
        return ResolvedCacheRoot::persistent(normalize_configured_path(Path::new(&explicit)));
    }
    for key in ["CARGO_TARGET_TMPDIR", "CARGO_TARGET_DIR"] {
        if let Some(base) = get_env(key).filter(|v| !v.is_empty()) {
            let candidate =
                normalize_configured_path(Path::new(&base)).join("anneal-itree-diff-cache");
            if !path_within_checkout(&candidate, anneal_root)
                && is_writable_cache_dir_candidate(&candidate)
            {
                return ResolvedCacheRoot::persistent(candidate);
            }
        }
    }
    if let Some(xdg) = get_env("XDG_CACHE_HOME").filter(|v| !v.is_empty()) {
        let candidate = normalize_configured_path(Path::new(&xdg)).join("anneal-itree-diff");
        if !path_within_checkout(&candidate, anneal_root)
            && is_writable_cache_dir_candidate(&candidate)
        {
            return ResolvedCacheRoot::persistent(candidate);
        }
    }
    if let Some(home) = get_env("HOME").filter(|v| !v.is_empty()) {
        let candidate =
            normalize_configured_path(Path::new(&home)).join(".cache/anneal-itree-diff");
        if !path_within_checkout(&candidate, anneal_root)
            && is_writable_cache_dir_candidate(&candidate)
        {
            return ResolvedCacheRoot::persistent(candidate);
        }
    }
    type ProcessTempCacheMap = BTreeMap<(PathBuf, PathBuf), Weak<tempfile::TempDir>>;
    static PROCESS_TEMP_CACHES: OnceLock<Mutex<ProcessTempCacheMap>> = OnceLock::new();
    let cache_key = (resolve_best_effort_path(anneal_root), sys_temp_dir.to_path_buf());
    let mut map = PROCESS_TEMP_CACHES
        .get_or_init(|| Mutex::new(BTreeMap::new()))
        .lock()
        .unwrap_or_else(|e| e.into_inner());
    if let Some(existing) = map
        .get(&cache_key)
        .and_then(Weak::upgrade)
        .filter(|td| td.path().is_dir() && !path_within_checkout(td.path(), anneal_root))
    {
        return ResolvedCacheRoot::temporary(existing);
    }

    let mut temp_bases = Vec::new();
    let mut push_out_of_tree = |cand: PathBuf| {
        if !cand.as_os_str().is_empty()
            && !path_within_checkout(&cand, anneal_root)
            && !temp_bases.iter().any(|b| b == &cand)
        {
            temp_bases.push(cand);
        }
    };
    push_out_of_tree(sys_temp_dir.to_path_buf());
    push_out_of_tree(env::temp_dir());
    #[cfg(unix)]
    {
        push_out_of_tree(PathBuf::from("/tmp"));
        push_out_of_tree(PathBuf::from("/var/tmp"));
    }

    for base in &temp_bases {
        let _ = std::fs::create_dir_all(base);
        if let Ok(td) = tempfile::Builder::new().prefix("anneal-itree-diff-cache-").tempdir_in(base)
            && !path_within_checkout(td.path(), anneal_root)
        {
            let arc = Arc::new(td);
            map.insert(cache_key, Arc::downgrade(&arc));
            return ResolvedCacheRoot::temporary(arc);
        }
    }

    // No writable out-of-checkout temp directory was available; return an
    // uncreatable character-device child path outside `anneal_root` (never a
    // predictable name in a world-writable temp dir) without panicking so
    // `DifferentialEngine` preparation reports a clean configuration `Err`.
    #[cfg(unix)]
    {
        ResolvedCacheRoot::persistent(PathBuf::from(
            "/dev/null/anneal-itree-diff-cache-unavailable",
        ))
    }
    #[cfg(not(unix))]
    {
        ResolvedCacheRoot::persistent(PathBuf::from(
            r"\\?\GLOBALROOT\Device\Null\anneal-itree-diff-cache-unavailable",
        ))
    }
}

/// Reject cache directories located inside the repository checkout boundary
/// ([`checkout_boundary_root`]) so explicit `--cache-dir` or
/// `ANNEAL_ITREE_CACHE_DIR` overrides never write build or sysroot artifacts
/// into `<repo>` or `<repo>/anneal`.
pub fn validate_cache_root_outside_checkout(
    anneal_root: &Path,
    cache_root: &Path,
) -> Result<(), String> {
    if cache_root.as_os_str().is_empty() {
        return Err("invalid cache directory configuration: cache_root is empty".to_string());
    }
    let boundary = checkout_boundary_root(anneal_root);
    if path_within_checkout(cache_root, anneal_root) {
        return Err(format!(
            "invalid cache directory configuration: cache_root ({}) must reside outside the checkout ({})",
            cache_root.display(),
            boundary.display(),
        ));
    }
    Ok(())
}

/// Resolve the enclosing repository checkout boundary for `anneal_root` so
/// cache-path guards block writes anywhere inside the checkout (including
/// `<repo>/.cache` or `<repo>/target`), not only under `<repo>/anneal`.
pub fn checkout_boundary_root(anneal_root: &Path) -> PathBuf {
    let norm_anneal = resolve_best_effort_path(anneal_root);
    for anc in norm_anneal.ancestors() {
        if std::fs::symlink_metadata(anc.join(".git")).is_ok() {
            return anc.to_path_buf();
        }
    }
    if norm_anneal.file_name() == Some(std::ffi::OsStr::new("anneal"))
        && let Some(parent) = norm_anneal.parent()
        && (parent.join("Cargo.toml").is_file()
            || parent.join("ci").is_dir()
            || parent.join(".github").is_dir())
    {
        return parent.to_path_buf();
    }
    norm_anneal
}

/// Normalize non-empty relative or dot-containing paths against the process
/// current working directory before passing them into subprocesses whose `cwd`
/// changes (such as `cargo build --target-dir` inside `anneal_root`). Leaves
/// clean absolute paths untouched so host temp-dir comparisons stay invariant.
pub fn normalize_configured_path(path: &Path) -> PathBuf {
    if path.as_os_str().is_empty() {
        return PathBuf::new();
    }
    if !path.is_absolute()
        || path
            .components()
            .any(|c| matches!(c, std::path::Component::ParentDir | std::path::Component::CurDir))
    {
        resolve_best_effort_path(path)
    } else {
        path.to_path_buf()
    }
}

fn is_writable_cache_dir_candidate(dir: &Path) -> bool {
    if std::fs::create_dir_all(dir).is_err() {
        return false;
    }
    tempfile::Builder::new().prefix(".anneal-cache-write-probe-").tempfile_in(dir).is_ok()
}

fn resolve_best_effort_path(path: &Path) -> PathBuf {
    enum PathStep {
        Prefix(OsString),
        Root(OsString),
        Parent,
        Normal(OsString),
    }

    fn push_components_front(queue: &mut VecDeque<PathStep>, src: &Path) {
        for c in src.components().rev() {
            match c {
                Component::Prefix(p) => queue.push_front(PathStep::Prefix(p.as_os_str().into())),
                Component::RootDir => queue.push_front(PathStep::Root(c.as_os_str().into())),
                Component::CurDir => {}
                Component::ParentDir => queue.push_front(PathStep::Parent),
                Component::Normal(s) => queue.push_front(PathStep::Normal(s.to_os_string())),
            }
        }
    }

    let abs = if path.is_absolute() {
        path.to_path_buf()
    } else {
        env::current_dir().map(|cwd| cwd.join(path)).unwrap_or_else(|_| path.to_path_buf())
    };
    let mut pending = VecDeque::new();
    push_components_front(&mut pending, &abs);
    let mut cur = PathBuf::new();
    let mut missing_depth = 0usize;
    let mut symlink_hops = 0usize;

    while let Some(step) = pending.pop_front() {
        match step {
            PathStep::Prefix(p) => {
                cur.push(p);
                missing_depth = 0;
            }
            PathStep::Root(r) => {
                cur.push(r);
                missing_depth = 0;
            }
            PathStep::Parent => {
                if cur.pop() {
                    missing_depth = missing_depth.saturating_sub(1);
                } else if !cur.has_root() {
                    cur.push("..");
                }
                if missing_depth == 0
                    && let Ok(canon) = std::fs::canonicalize(&cur)
                {
                    cur = canon;
                }
            }
            PathStep::Normal(part) => {
                cur.push(part);
                if missing_depth == 0 {
                    if let Ok(canon) = std::fs::canonicalize(&cur) {
                        cur = canon;
                    } else if symlink_hops < 40
                        && std::fs::symlink_metadata(&cur).is_ok_and(|m| m.file_type().is_symlink())
                        && let Ok(target) = std::fs::read_link(&cur)
                    {
                        symlink_hops += 1;
                        cur.pop();
                        if target.is_absolute() {
                            cur.clear();
                        }
                        push_components_front(&mut pending, &target);
                    } else {
                        missing_depth = 1;
                    }
                } else {
                    missing_depth += 1;
                }
            }
        }
    }
    cur
}

fn path_within_checkout(candidate: &Path, anneal_root: &Path) -> bool {
    let boundary = checkout_boundary_root(anneal_root);
    let norm_cand = resolve_best_effort_path(candidate);
    !norm_cand.is_absolute()
        || norm_cand.starts_with(&boundary)
        || candidate.starts_with(&boundary)
        || candidate.starts_with(anneal_root)
}

/// Prepared 4-way differential execution engine.
pub struct DifferentialEngine {
    pub config: DifferentialConfig,
    pub rustc: RustcRunner,
    pub miri: Option<MiriRunner>,
    pub miri_status: String,
    pub lean: Option<LeanTraceSession>,
    pub mir_eval: Option<MirEvalAdapter>,
    pub mir_eval_status: String,
}

fn strip_env_schedule_for_strict_probe(case: &TraceTestCase) -> TraceTestCase {
    let mut stripped = case.clone();
    let scheduled_callees: Vec<String> = case.env_schedule.per_callee.keys().cloned().collect();
    let has_global = !case.env_schedule.global.is_empty();
    stripped.env_schedule = Default::default();
    if !scheduled_callees.is_empty() || has_global {
        match &mut stripped.lean_program_spec {
            LeanProgramSpec::MultiCallWithCapturedCallees { external_callees, .. }
            | LeanProgramSpec::SyntheticMirAst { external_callees, .. } => {
                for callee in scheduled_callees {
                    if !external_callees.contains(&callee) {
                        external_callees.push(callee);
                    }
                }
                if has_global && !external_callees.iter().any(|c| c == "*") {
                    external_callees.push("*".to_string());
                }
            }
            LeanProgramSpec::CapturedRust { .. } => {}
        }
    }
    stripped
}

impl DifferentialEngine {
    /// Discover and initialize all enabled execution authorities, failing
    /// closed when `require_miri` (`--require-miri` /
    /// `ANNEAL_ITREE_REQUIRE_MIRI=1`) is set and Miri is unavailable, or when
    /// an explicit `ANNEAL_ITREE_RUSTC`, `ANNEAL_ITREE_MIRI_*`, or
    /// `ANNEAL_MIR_EVAL_BIN` override is invalid.
    pub fn prepare(config: DifferentialConfig) -> Result<Self, String> {
        Self::prepare_with_env(config, |k| env::var_os(k))
    }

    /// Deterministic environment-injected variant of [`Self::prepare`] for
    /// unit-testing explicit authority overrides without mutating global
    /// process environment variables across parallel test threads.
    pub fn prepare_with_env(
        mut config: DifferentialConfig,
        get_env: impl Fn(&str) -> Option<std::ffi::OsString>,
    ) -> Result<Self, String> {
        config.anneal_root = normalize_configured_path(&config.anneal_root);
        config.cache_root = normalize_configured_path(&config.cache_root);
        validate_cache_root_outside_checkout(&config.anneal_root, &config.cache_root)?;
        let lean = if config.enable_lean {
            Some(LeanTraceSession::prepare(&config.anneal_root, &config.cache_root)?)
        } else {
            None
        };

        let lean_sysroot = lean.as_ref().map(|l| l.rust_sysroot.as_path());
        let rustc = RustcRunner::discover_with_env(lean_sysroot, &get_env)?;
        if let Some(l) = &lean {
            let rustc_matches_lean = match rustc.sysroot.as_deref() {
                Some(rsr) => sysroots_equivalent(&l.rust_sysroot, rsr)?,
                None => false,
            };
            if !rustc_matches_lean {
                return Err(format!(
                    "toolchain version skew: resolved `rustc` sysroot ({:?}) differs from Lean/capture sysroot ({})",
                    rustc.sysroot,
                    l.rust_sysroot.display(),
                ));
            }
            if !compiler_matches_pinned_sysroot_with_suffix(
                &rustc.rustc_bin,
                &l.rust_sysroot,
                env::consts::EXE_SUFFIX,
            )? {
                return Err(format!(
                    "toolchain compiler mismatch: resolved `rustc` binary ({}) is not the pinned sysroot compiler for {}",
                    rustc.rustc_bin.display(),
                    l.rust_sysroot.display(),
                ));
            }
            if rustc.host_target != l.host_target {
                return Err(format!(
                    "toolchain target skew: resolved `rustc` target (`{}`) differs from Lean/capture target (`{}`)",
                    rustc.host_target, l.host_target,
                ));
            }
        }
        let selected_sysroot = lean_sysroot.or(rustc.sysroot.as_deref());

        let (miri, miri_status) = if config.enable_miri {
            match MiriRunner::probe_with_env(&config.cache_root, selected_sysroot, &get_env) {
                MiriAvailability::Available(m) => {
                    if m.target != rustc.host_target {
                        return Err(format!(
                            "toolchain target skew: resolved Miri target (`{}`) differs from `rustc` target (`{}`)",
                            m.target, rustc.host_target,
                        ));
                    }
                    let desc = format!("available ({}, target={})", m.label, m.target);
                    (Some(m), desc)
                }
                MiriAvailability::InvalidConfig { reason } => {
                    return Err(format!("invalid Miri configuration: {reason}"));
                }
                MiriAvailability::Unavailable { reason } => {
                    if config.require_miri {
                        return Err(format!(
                            "Miri required (`--require-miri` / `ANNEAL_ITREE_REQUIRE_MIRI=1`) but unavailable: {reason}"
                        ));
                    }
                    (None, format!("unavailable ({reason})"))
                }
            }
        } else {
            if config.require_miri {
                return Err(
                    "conflicting configuration: `require_miri` set while `enable_miri` is false"
                        .to_string(),
                );
            }
            (None, "disabled (--no-miri)".to_string())
        };

        let (mir_eval, mir_eval_status) = if !config.enable_lean {
            if get_env("ANNEAL_MIR_EVAL_BIN").is_some() {
                match MirEvalAdapter::probe_with_env(&get_env) {
                    MirEvalAvailability::InvalidConfig { reason } => {
                        return Err(format!("invalid ANNEAL_MIR_EVAL_BIN configuration: {reason}"));
                    }
                    MirEvalAvailability::Available(a) => {
                        return Err(format!(
                            "conflicting configuration: explicit ANNEAL_MIR_EVAL_BIN ({}) requires MIR capture, which is disabled when `enable_lean` is false (`--no-lean`)",
                            a.binary.display()
                        ));
                    }
                    MirEvalAvailability::Unavailable { .. } => {}
                }
            }
            (None, "disabled (--no-lean)".to_string())
        } else {
            match MirEvalAdapter::probe_with_env(&get_env) {
                MirEvalAvailability::Available(a) => {
                    let s = format!("available ({})", a.binary.display());
                    (Some(a), s)
                }
                MirEvalAvailability::InvalidConfig { reason } => {
                    return Err(format!("invalid ANNEAL_MIR_EVAL_BIN configuration: {reason}"));
                }
                MirEvalAvailability::Unavailable { reason } => {
                    (None, format!("unavailable ({reason})"))
                }
            }
        };

        Ok(Self { config, rustc, miri, miri_status, lean, mir_eval, mir_eval_status })
    }

    /// Execute one [`TraceTestCase`] across all active authorities (`miri`
    /// first to guard against executing host UB), plus Strict-vs-Compositional
    /// conservative checking and full-authority metamorphic twin duality.
    pub fn run_case(&self, case: &TraceTestCase) -> CaseReport {
        // 1. Run Miri FIRST when available so UB inputs are never executed
        //    natively under host `rustc -O0` / `-O2`, and fail closed by
        //    skipping native execution whenever Miri cannot certify the case.
        let miri_res = self.miri.as_ref().map(|m| m.run_case(case));
        let rustc_dual = match should_skip_host_rustc(case.is_expected_ub(), miri_res.as_ref()) {
            Some(reason) => RustcDualResult::skipped_for_ub(reason),
            None => self.rustc.run_dual(case),
        };

        let (lean_res, captured_arts, strict_conservative_check) = match &self.lean {
            Some(l) => {
                let primary_case = if self.config.lean_mode == LeanTraceMode::StrictVerbatim
                    && !matches!(case.lean_program_spec, LeanProgramSpec::CapturedRust { .. })
                {
                    std::borrow::Cow::Owned(strip_env_schedule_for_strict_probe(case))
                } else {
                    std::borrow::Cow::Borrowed(case)
                };
                let (primary, arts) = l.run_case(&primary_case, self.config.lean_mode);
                let strict_probe = if self.config.lean_mode == LeanTraceMode::CompositionalITree
                    && !matches!(case.lean_program_spec, LeanProgramSpec::CapturedRust { .. })
                {
                    let strict_case = strip_env_schedule_for_strict_probe(case);
                    Some(l.run_case(&strict_case, LeanTraceMode::StrictVerbatim).0)
                } else {
                    None
                };
                (Some(primary), arts, strict_probe)
            }
            None => (None, None, None),
        };

        let mir_eval_res =
            evaluate_mir_eval_leg(self.mir_eval.as_ref(), captured_arts.as_ref(), case);

        let mut verdict = classify_four_way_with_ub_guard(
            &rustc_dual.o0,
            &rustc_dual.o2,
            rustc_dual.skipped_for_ub,
            miri_res.as_ref(),
            lean_res.as_ref(),
            mir_eval_res.as_ref(),
            case.spine_mode,
            case.disclosed_gap.as_ref(),
        );

        // Enforce that strict mode on multi-call/unwind cases NEVER produces
        // `UnsoundAccept`, `undeclared_ub_fault`, or `ToolError`, AND that it
        // conservatively refuses (`CaptureRefused`) whenever the primary
        // `CompositionalITree` execution actually exercised a call boundary.
        if !verdict.is_critical_failure()
            && let (Some(primary_lean), Some(strict_res)) = (&lean_res, &strict_conservative_check)
        {
            let strict_verdict = classify_four_way_with_ub_guard(
                &rustc_dual.o0,
                &rustc_dual.o2,
                rustc_dual.skipped_for_ub,
                miri_res.as_ref(),
                Some(strict_res),
                None,
                SpineCompareMode::OutcomeOnly,
                case.disclosed_gap.as_ref(),
            );
            if let Some(promoted) = validate_strict_multicall_probe_for_case(
                case,
                primary_lean,
                strict_res,
                &strict_verdict,
            ) {
                verdict = promoted;
            }
        }

        // Full-authority metamorphic inlining duality check across `rustc`,
        // `miri`, and `Lean` (preserving `ToolError` without relabeling as
        // `UnsoundAccept`, and separating `SkippedConservative` from `Passed`).
        let metamorphic_receipt = if self.config.check_metamorphic_duality
            && let (Some(l), Some(twin)) = (&self.lean, &case.metamorphic_inlined_twin)
            && let Some(called_lean) = &lean_res
        {
            let receipt = self.run_full_metamorphic_duality(
                case,
                twin,
                &rustc_dual,
                miri_res.as_ref(),
                l,
                called_lean,
            );
            if let Some((auth, detail)) = &receipt.tool_error {
                if !verdict.is_critical_failure() {
                    verdict =
                        TraceVerdict::ToolError { authority: auth.clone(), detail: detail.clone() };
                }
            } else if matches!(receipt.status, MetamorphicStatus::Failed)
                && !verdict.is_critical_failure()
            {
                verdict = TraceVerdict::UnsoundAccept { detail: receipt.detail.clone() };
            }
            Some(receipt)
        } else {
            None
        };

        let expectation_violation = check_case_expectation_for_case(
            case,
            &verdict,
            &rustc_dual,
            miri_res.as_ref(),
            lean_res.as_ref(),
            mir_eval_res.as_ref(),
            self.config.lean_mode,
        );

        CaseReport {
            case_id: case.id.clone(),
            category: case.category,
            expected_class: case.expected_class,
            verdict,
            expectation_violation,
            rustc_dual,
            miri: miri_res,
            lean: lean_res,
            lean_strict_probe: strict_conservative_check,
            mir_eval: mir_eval_res,
            metamorphic: metamorphic_receipt,
        }
    }

    fn run_full_metamorphic_duality(
        &self,
        case: &TraceTestCase,
        twin: &MetamorphicTwin,
        called_rustc: &RustcDualResult,
        called_miri: Option<&AuthorityRunResult>,
        lean_session: &LeanTraceSession,
        called_lean: &AuthorityRunResult,
    ) -> MetamorphicDualityReceipt {
        let twin_case = TraceTestCase {
            id: format!("{}__inlined_twin", case.id),
            category: case.category,
            pure_rust_source: twin.pure_rust_source.clone(),
            traced_rust_source: None,
            entry_fn: twin.entry_fn.clone(),
            rust_arg_exprs: case.rust_arg_exprs.clone(),
            lean_args: case.lean_args.clone(),
            ret_shape: case.ret_shape.clone(),
            lean_program_spec: LeanProgramSpec::CapturedRust {
                crate_name: twin.crate_name.clone(),
                select_fn: twin.entry_fn.clone(),
            },
            metamorphic_inlined_twin: None,
            env_schedule: EnvSchedule::default(),
            fuel: case.fuel,
            spine_mode: SpineCompareMode::OutcomeOnly,
            expected_class: case.expected_class,
            expected_ub: case.expected_ub.clone(),
            expected_conservative: case.expected_conservative.clone(),
            disclosed_gap: None,
        };

        let twin_miri = self.miri.as_ref().map(|m| m.run_case(&twin_case));
        let twin_rustc =
            match should_skip_host_rustc(twin_case.is_expected_ub(), twin_miri.as_ref()) {
                Some(reason) => RustcDualResult::skipped_for_ub(reason),
                None => self.rustc.run_dual(&twin_case),
            };
        let (inlined_lean, _) = lean_session.run_case(&twin_case, LeanTraceMode::StrictVerbatim);
        evaluate_metamorphic_duality(
            called_rustc,
            called_miri,
            called_lean,
            &twin_rustc,
            twin_miri.as_ref(),
            inlined_lean,
        )
    }

    /// Execute a slice of [`TraceTestCase`]s and aggregate a structured
    /// [`DifferentialReport`].
    pub fn run_cases(&self, cases: &[TraceTestCase]) -> DifferentialReport {
        let mut reports = Vec::with_capacity(cases.len());
        for c in cases {
            reports.push(self.run_case(c));
        }
        DifferentialReport::from_cases(
            &self.miri_status,
            self.miri.is_some(),
            self.config.require_miri,
            &self.mir_eval_status,
            self.config.lean_mode,
            reports,
            Vec::new(),
        )
    }

    /// Run a seeded deterministic multi-call fuzz campaign of `count` programs,
    /// shrinking any semantic divergence under its pinned
    /// [`ShrinkFailureSignature`] (rejecting `ToolError` candidates and
    /// propagating witness write failures as `ToolError`).
    pub fn run_fuzz_campaign(&self, seed: u64, count: usize) -> DifferentialReport {
        let programs: Vec<FuzzProgram> = generate_fuzz_batch(seed, count);
        let mut reports = Vec::with_capacity(programs.len());
        let mut witnesses = Vec::new();

        for prog in &programs {
            let case = prog.to_trace_test_case();
            let mut report = self.run_case(&case);
            if self.config.shrink_on_divergence
                && let Some(target_sig) = ShrinkFailureSignature::from_case_report(&report)
            {
                let (witness, propagated_tool_err) = shrink_and_build_witness_with(
                    &report.case_id,
                    prog,
                    &report.verdict,
                    &target_sig,
                    |cand| self.run_case(&cand.to_trace_test_case()),
                );
                apply_fuzz_shrink_outcome(
                    &mut report,
                    self.config.witness_dir.as_deref(),
                    &mut witnesses,
                    witness,
                    propagated_tool_err,
                );
                report.expectation_violation = check_case_expectation_with_mir_eval(
                    case.expected_class,
                    case.expected_ub.as_ref(),
                    case.expected_conservative.as_ref(),
                    case.category,
                    &case.lean_program_spec,
                    &report.verdict,
                    &report.rustc_dual,
                    report.miri.as_ref(),
                    report.lean.as_ref(),
                    report.mir_eval.as_ref(),
                    self.config.lean_mode,
                );
            }
            reports.push(report);
        }

        DifferentialReport::from_cases(
            &self.miri_status,
            self.miri.is_some(),
            self.config.require_miri,
            &self.mir_eval_status,
            self.config.lean_mode,
            reports,
            witnesses,
        )
    }
}

/// Evaluate `case` under an optional `anneal-mir-eval` adapter without ever
/// silently returning `None` when `mir_eval` is configured: missing captured
/// bodies fail closed with `ToolError`, while unsupported multi-call/synthetic
/// cases or unavailable captures return an explicit `CaptureRefused` sentinel
/// so 4-way verdicts record `ConservativeOverApprox` instead of false `Agree`.
pub fn evaluate_mir_eval_leg(
    mir_eval: Option<&MirEvalAdapter>,
    captured_arts: Option<&CapturedArtifacts>,
    case: &TraceTestCase,
) -> Option<AuthorityRunResult> {
    let adapter = mir_eval?;
    Some(match (captured_arts, &case.lean_program_spec) {
        (Some(arts), LeanProgramSpec::CapturedRust { select_fn, .. }) => {
            match arts.body_ids_by_fn.get(select_fn) {
                Some(&body_id) => adapter.eval_captured_for_shape(
                    &arts.capture_json,
                    body_id,
                    case.fuel,
                    &case.lean_args,
                    Some(&case.ret_shape),
                ),
                None => AuthorityRunResult::tool_error(
                    "anneal-mir-eval",
                    format!("selected function `{select_fn}` missing from captured MIR manifest"),
                ),
            }
        }
        (None, LeanProgramSpec::CapturedRust { select_fn, .. }) => AuthorityRunResult {
            authority: "anneal-mir-eval".to_string(),
            outcome: TerminalOutcome::CaptureRefused {
                reason: format!(
                    "MIR capture artifacts unavailable for `{select_fn}`; anneal-mir-eval could not evaluate"
                ),
            },
            spine: ObservableSpine::default(),
            caller_frame_law: CallerFrameLaw::all_satisfied(),
            tool_error: None,
            raw_diagnostics: String::new(),
            elapsed_ms: 0,
            post_only_mem_digest: false,
            entry_mem_digest: None,
        },
        _ => AuthorityRunResult {
            authority: "anneal-mir-eval".to_string(),
            outcome: TerminalOutcome::CaptureRefused {
                reason: "anneal-mir-eval only evaluates single-crate CapturedRust captures; multi-call/synthetic Lean AST and EnvSchedule cases are unsupported"
                    .to_string(),
            },
            spine: ObservableSpine::default(),
            caller_frame_law: CallerFrameLaw::all_satisfied(),
            tool_error: None,
            raw_diagnostics: String::new(),
            elapsed_ms: 0,
            post_only_mem_digest: false,
            entry_mem_digest: None,
        },
    })
}

/// Record a shrink pass's secondary `ToolError` (including budget cutoff
/// before 1-minimality) and emit the [`WitnessArtifact`] strictly when
/// `witness.shrink.succeeded && witness.shrink.is_one_minimal`.
pub fn apply_fuzz_shrink_outcome(
    report: &mut CaseReport,
    witness_dir: Option<&Path>,
    witnesses: &mut Vec<WitnessArtifact>,
    witness: WitnessArtifact,
    propagated_tool_err: Option<TraceVerdict>,
) {
    if let Some(TraceVerdict::ToolError { authority, detail }) = propagated_tool_err {
        attach_secondary_tool_error(&mut report.verdict, &authority, &detail);
    }
    if witness.shrink.succeeded && witness.shrink.is_one_minimal {
        if let Some(dir) = witness_dir {
            let out_path = dir.join(format!("{}.witness.json", report.case_id));
            if let Err(err) = witness.write_json(&out_path) {
                attach_secondary_tool_error(&mut report.verdict, "witness-writer", &err);
            }
        }
        witnesses.push(witness);
    }
}

/// Record a secondary witness-building or witness-writing tool failure without
/// overwriting an existing primary `UnsoundAccept` or `undeclared_ub_fault`
/// classification (`unsound_accept` / `undeclared_ub_fault` counts remain
/// intact).
pub fn attach_secondary_tool_error(verdict: &mut TraceVerdict, authority: &str, err_detail: &str) {
    match verdict {
        TraceVerdict::UnsoundAccept { detail }
        | TraceVerdict::ConservativeOverApprox {
            reason: detail, undeclared_ub_fault: true, ..
        } => {
            detail.push_str(&format!("; secondary {authority} tool error: {err_detail}"));
        }
        _ => {
            *verdict = TraceVerdict::ToolError {
                authority: authority.to_string(),
                detail: err_detail.to_string(),
            };
        }
    }
}

/// Validate a `StrictVerbatim` probe paired with a `CompositionalITree`
/// multi-call run: promotes critical `strict_verdict` failures and requires
/// `CaptureRefused` when `requires_strict_refusal` holds (or matching execution
/// for intra-crate calls supported by `evalStep`).
pub fn validate_strict_multicall_probe_for_case(
    case: &TraceTestCase,
    primary_lean: &AuthorityRunResult,
    strict_probe: &AuthorityRunResult,
    strict_verdict: &TraceVerdict,
) -> Option<TraceVerdict> {
    validate_strict_multicall_probe_inner(
        case.requires_strict_refusal(),
        primary_lean,
        strict_probe,
        strict_verdict,
    )
}

/// Spec-only variant of `validate_strict_multicall_probe_for_case` checking
/// [`LeanProgramSpec::requires_strict_refusal`].
pub fn validate_strict_multicall_probe_for_spec(
    spec: &LeanProgramSpec,
    primary_lean: &AuthorityRunResult,
    strict_probe: &AuthorityRunResult,
    strict_verdict: &TraceVerdict,
) -> Option<TraceVerdict> {
    validate_strict_multicall_probe_inner(
        spec.requires_strict_refusal(),
        primary_lean,
        strict_probe,
        strict_verdict,
    )
}

/// Legacy conservative-refusal wrapper for
/// `validate_strict_multicall_probe_for_spec` assuming external or cleanup
/// call boundaries require `CaptureRefused`.
pub fn validate_strict_multicall_probe(
    primary_lean: &AuthorityRunResult,
    strict_probe: &AuthorityRunResult,
    strict_verdict: &TraceVerdict,
) -> Option<TraceVerdict> {
    validate_strict_multicall_probe_inner(true, primary_lean, strict_probe, strict_verdict)
}

fn validate_strict_multicall_probe_inner(
    requires_refusal: bool,
    primary_lean: &AuthorityRunResult,
    strict_probe: &AuthorityRunResult,
    strict_verdict: &TraceVerdict,
) -> Option<TraceVerdict> {
    if strict_verdict.is_critical_failure() {
        return Some(strict_verdict.clone());
    }
    if let Some(detail) = &strict_probe.tool_error {
        return Some(TraceVerdict::ToolError {
            authority: strict_probe.authority.clone(),
            detail: detail.clone(),
        });
    }
    let primary_exercised_call = primary_lean.spine.events.iter().any(|ev| {
        matches!(ev, ObservableEvent::CallEnter { .. } | ObservableEvent::CallUnwind { .. })
    });
    if primary_exercised_call {
        if requires_refusal {
            if !matches!(strict_probe.outcome, TerminalOutcome::CaptureRefused { .. }) {
                return Some(TraceVerdict::UnsoundAccept {
                    detail: format!(
                        "StrictVerbatim failed to conservatively refuse multi-call execution: expected CaptureRefused, got {:?}",
                        strict_probe.outcome
                    ),
                });
            }
        } else if !primary_lean.outcome.semantically_eq(&strict_probe.outcome) {
            return Some(TraceVerdict::UnsoundAccept {
                detail: format!(
                    "StrictVerbatim intra-crate call outcome diverged from CompositionalITree: {:?} vs {:?}",
                    strict_probe.outcome, primary_lean.outcome
                ),
            });
        }
    }
    None
}

/// Shrink `initial_prog` under [`ShrinkBudget::default`] and its pinned
/// [`ShrinkFailureSignature`], recomputing the [`WitnessArtifact`]'s `verdict`
/// from the minimized program (preserving `original_verdict` separately and
/// returning `Some(ToolError)` on re-evaluation errors, non-reproduction, or
/// shrink-budget cutoff prior to 1-minimality).
pub fn shrink_and_build_witness_with<F>(
    case_id: &str,
    initial_prog: &FuzzProgram,
    initial_verdict: &TraceVerdict,
    target_sig: &ShrinkFailureSignature,
    eval_prog: F,
) -> (WitnessArtifact, Option<TraceVerdict>)
where
    F: FnMut(&FuzzProgram) -> CaseReport,
{
    shrink_and_build_witness_with_budget(
        case_id,
        initial_prog,
        initial_verdict,
        target_sig,
        ShrinkBudget::default(),
        eval_prog,
    )
}

/// Budget-parameterized variant of [`shrink_and_build_witness_with`], surfacing
/// `Some(ToolError { authority: "shrink-witness", .. })` if `budget` expires
/// before reaching a verified 1-minimal fixpoint.
pub fn shrink_and_build_witness_with_budget<F>(
    case_id: &str,
    initial_prog: &FuzzProgram,
    initial_verdict: &TraceVerdict,
    target_sig: &ShrinkFailureSignature,
    budget: ShrinkBudget,
    mut eval_prog: F,
) -> (WitnessArtifact, Option<TraceVerdict>)
where
    F: FnMut(&FuzzProgram) -> CaseReport,
{
    let original_verdict = initial_verdict.clone();
    let first_eval_tool_err: std::cell::RefCell<Option<TraceVerdict>> =
        std::cell::RefCell::new(None);
    let mut shrunk = shrink_fuzz_program_with_budget(initial_prog, budget, |cand| {
        let cand_rep = eval_prog(cand);
        if cand == initial_prog
            && first_eval_tool_err.borrow().is_none()
            && matches!(cand_rep.verdict, TraceVerdict::ToolError { .. })
        {
            *first_eval_tool_err.borrow_mut() = Some(cand_rep.verdict.clone());
        }
        ShrinkFailureSignature::from_case_report(&cand_rep).as_ref() == Some(target_sig)
    });
    let min_report = eval_prog(&shrunk.minimized);
    let reproduced_target =
        ShrinkFailureSignature::from_case_report(&min_report).as_ref() == Some(target_sig);
    if !reproduced_target {
        shrunk.succeeded = false;
        shrunk.is_one_minimal = false;
    }
    let propagated_tool_err = if matches!(min_report.verdict, TraceVerdict::ToolError { .. }) {
        Some(min_report.verdict.clone())
    } else if let Some(te) = first_eval_tool_err.into_inner()
        && !shrunk.succeeded
    {
        Some(te)
    } else if !shrunk.succeeded {
        Some(TraceVerdict::ToolError {
            authority: "shrink-witness".to_string(),
            detail: format!(
                "shrunk candidate failed to reproduce target signature {target_sig:?}: got {}",
                min_report.verdict
            ),
        })
    } else if !shrunk.is_one_minimal {
        Some(TraceVerdict::ToolError {
            authority: "shrink-witness".to_string(),
            detail: format!(
                "shrink budget exhausted before reaching 1-minimal witness (evals={}, budget_exhausted={}); suppressing non-1-minimal witness",
                shrunk.predicate_evaluations, shrunk.budget_exhausted
            ),
        })
    } else {
        None
    };
    let witness =
        WitnessArtifact::from_shrink(case_id, min_report.verdict, original_verdict, shrunk);
    (witness, propagated_tool_err)
}

/// Validate a case's verdict and terminal outcome against its declared
/// [`ExpectedCaseClass`] across full, degraded (`--no-miri` / `--no-lean`), and
/// `StrictVerbatim` modes. Returns `None` when satisfied or `Some(reason)` when
/// violated.
#[allow(clippy::too_many_arguments)]
pub fn check_case_expectation(
    expected: ExpectedCaseClass,
    expected_ub: Option<&ExpectedUbSpec>,
    expected_conservative: Option<&ExpectedConservativeSpec>,
    category: CaseCategory,
    lean_program_spec: &LeanProgramSpec,
    verdict: &TraceVerdict,
    rustc_dual: &RustcDualResult,
    miri: Option<&AuthorityRunResult>,
    lean: Option<&AuthorityRunResult>,
    lean_mode: LeanTraceMode,
) -> Option<String> {
    check_case_expectation_with_mir_eval(
        expected,
        expected_ub,
        expected_conservative,
        category,
        lean_program_spec,
        verdict,
        rustc_dual,
        miri,
        lean,
        None,
        lean_mode,
    )
}

/// Validate a full [`TraceTestCase`]'s verdict and terminal outcome against its
/// declared [`ExpectedCaseClass`] (accounting for both `lean_program_spec` and
/// `env_schedule` `StrictVerbatim` refusal rules plus optional
/// `anneal-mir-eval` refusals).
#[allow(clippy::too_many_arguments)]
pub fn check_case_expectation_for_case(
    case: &TraceTestCase,
    verdict: &TraceVerdict,
    rustc_dual: &RustcDualResult,
    miri: Option<&AuthorityRunResult>,
    lean: Option<&AuthorityRunResult>,
    mir_eval: Option<&AuthorityRunResult>,
    lean_mode: LeanTraceMode,
) -> Option<String> {
    check_case_expectation_inner(
        case.expected_class,
        case.expected_ub.as_ref(),
        case.expected_conservative.as_ref(),
        case.category,
        &case.lean_program_spec,
        case.requires_strict_refusal(),
        verdict,
        rustc_dual,
        miri,
        lean,
        mir_eval,
        lean_mode,
    )
}

/// Validate a case's verdict and terminal outcome against its declared
/// [`ExpectedCaseClass`], accounting for optional `anneal-mir-eval`
/// conservative refusals on unsupported multi-call/synthetic shapes while still
/// rejecting `Agree` whenever `mir_eval` did not verify the case.
#[allow(clippy::too_many_arguments)]
pub fn check_case_expectation_with_mir_eval(
    expected: ExpectedCaseClass,
    expected_ub: Option<&ExpectedUbSpec>,
    expected_conservative: Option<&ExpectedConservativeSpec>,
    category: CaseCategory,
    lean_program_spec: &LeanProgramSpec,
    verdict: &TraceVerdict,
    rustc_dual: &RustcDualResult,
    miri: Option<&AuthorityRunResult>,
    lean: Option<&AuthorityRunResult>,
    mir_eval: Option<&AuthorityRunResult>,
    lean_mode: LeanTraceMode,
) -> Option<String> {
    check_case_expectation_inner(
        expected,
        expected_ub,
        expected_conservative,
        category,
        lean_program_spec,
        lean_program_spec.requires_strict_refusal(),
        verdict,
        rustc_dual,
        miri,
        lean,
        mir_eval,
        lean_mode,
    )
}

#[allow(clippy::too_many_arguments)]
fn check_case_expectation_inner(
    expected: ExpectedCaseClass,
    expected_ub: Option<&ExpectedUbSpec>,
    expected_conservative: Option<&ExpectedConservativeSpec>,
    category: CaseCategory,
    lean_program_spec: &LeanProgramSpec,
    spec_or_case_requires_strict_refusal: bool,
    verdict: &TraceVerdict,
    rustc_dual: &RustcDualResult,
    miri: Option<&AuthorityRunResult>,
    lean: Option<&AuthorityRunResult>,
    mir_eval: Option<&AuthorityRunResult>,
    lean_mode: LeanTraceMode,
) -> Option<String> {
    if verdict.is_critical_failure() {
        return Some(format!(
            "critical verdict failure for expected {expected:?} ({category:?}): {verdict}"
        ));
    }
    if expected != ExpectedCaseClass::UndefinedBehavior && expected_ub.is_some() {
        return Some(format!(
            "unexpected `expected_ub` spec declared on non-UB case {expected:?} ({category:?})"
        ));
    }
    if expected != ExpectedCaseClass::ConservativeOverApprox && expected_conservative.is_some() {
        return Some(format!(
            "unexpected `expected_conservative` spec declared on non-conservative case {expected:?} ({category:?})"
        ));
    }

    let ref_outcome = if let Some(m) = miri {
        Some(&m.outcome)
    } else if !rustc_dual.skipped_for_ub {
        Some(&rustc_dual.o0.outcome)
    } else {
        None
    };

    let strict_multicall_refusal_required =
        lean_mode == LeanTraceMode::StrictVerbatim && spec_or_case_requires_strict_refusal;
    let mir_eval_conservative = mir_eval.is_some_and(|me| {
        matches!(
            me.outcome,
            TerminalOutcome::CaptureRefused { .. } | TerminalOutcome::Diverged { .. }
        )
    });

    let check_clean_or_degraded_verdict = |v: &TraceVerdict| -> bool {
        if mir_eval_conservative || (strict_multicall_refusal_required && lean.is_some()) {
            return matches!(
                v,
                TraceVerdict::ConservativeOverApprox { undeclared_ub_fault: false, .. }
            );
        }
        match (miri.is_some(), lean.is_some()) {
            (true, true) => matches!(v, TraceVerdict::Agree),
            (false, true) | (false, false) => matches!(v, TraceVerdict::DegradedNoMiri { .. }),
            (true, false) => matches!(v, TraceVerdict::DegradedNoLean { .. }),
        }
    };

    let check_terminal_class = |outcome_label: &str,
                                matches_expected: fn(&TerminalOutcome) -> bool|
     -> Option<String> {
        if !ref_outcome.is_some_and(matches_expected) {
            return Some(format!(
                "expected {outcome_label} reference outcome for {expected:?} ({category:?}), got {ref_outcome:?}"
            ));
        }
        if let Some(l) = lean {
            if strict_multicall_refusal_required {
                if !matches!(l.outcome, TerminalOutcome::CaptureRefused { .. }) {
                    return Some(format!(
                        "expected CaptureRefused Lean outcome in StrictVerbatim for {expected:?} ({category:?}), got {:?}",
                        l.outcome
                    ));
                }
            } else if !matches_expected(&l.outcome) {
                return Some(format!(
                    "expected {outcome_label} Lean outcome for {expected:?} ({category:?}), got {:?}",
                    l.outcome
                ));
            }
        }
        if !check_clean_or_degraded_verdict(verdict) {
            return Some(format!(
                "unexpected verdict for {expected:?} ({category:?}) in {lean_mode:?} (miri={}, lean={}): {verdict}",
                miri.is_some(),
                lean.is_some(),
            ));
        }
        None
    };

    match expected {
        ExpectedCaseClass::Agree => {
            check_terminal_class("Returned", |o| matches!(o, TerminalOutcome::Returned { .. }))
        }
        ExpectedCaseClass::Unwind => {
            check_terminal_class("Unwound", |o| matches!(o, TerminalOutcome::Unwound { .. }))
        }
        ExpectedCaseClass::Abort => {
            check_terminal_class("Aborted", |o| matches!(o, TerminalOutcome::Aborted { .. }))
        }
        ExpectedCaseClass::ConservativeOverApprox => {
            let Some(cons_spec) = expected_conservative else {
                return Some(format!(
                    "expected non-empty `expected_conservative` refusal spec for {expected:?} ({category:?})"
                ));
            };
            let cons_marker = cons_spec.lean_marker.trim();
            if cons_marker.is_empty() {
                return Some(format!(
                    "invalid empty `expected_conservative.lean_marker` for {expected:?} ({category:?})"
                ));
            }
            if !cons_spec.ref_kind.matches_outcome(ref_outcome) {
                return Some(format!(
                    "expected {:?} reference outcome for {expected:?} ({category:?}), got {ref_outcome:?}",
                    cons_spec.ref_kind
                ));
            }
            if let Some(l) = lean {
                match &l.outcome {
                    TerminalOutcome::CaptureRefused { reason } => {
                        if !reason.contains(cons_marker) {
                            return Some(format!(
                                "conservative Lean refusal marker mismatch for {expected:?} ({category:?}): expected substring {cons_marker:?}, got {reason:?}"
                            ));
                        }
                    }
                    other => {
                        return Some(format!(
                            "expected conservative Lean CaptureRefused matching {cons_marker:?} for {expected:?} ({category:?}), got {other:?}"
                        ));
                    }
                }
            }
            let verdict_ok = if lean.is_some() {
                matches!(
                    verdict,
                    TraceVerdict::ConservativeOverApprox { undeclared_ub_fault: false, .. }
                )
            } else if miri.is_some() {
                matches!(verdict, TraceVerdict::DegradedNoLean { .. })
            } else {
                matches!(verdict, TraceVerdict::DegradedNoMiri { .. })
            };
            if !verdict_ok {
                return Some(format!(
                    "unexpected verdict for {expected:?} ({category:?}) (miri={}, lean={}): {verdict}",
                    miri.is_some(),
                    lean.is_some(),
                ));
            }
            None
        }
        ExpectedCaseClass::DisclosedGap => {
            if !ref_outcome.is_some_and(TerminalOutcome::is_accepting) {
                return Some(format!(
                    "expected accepting reference outcome for {expected:?} ({category:?}), got {ref_outcome:?}"
                ));
            }
            if let Some(l) = lean
                && !matches!(
                    l.outcome,
                    TerminalOutcome::CaptureRefused { .. } | TerminalOutcome::FaultUb { .. }
                )
            {
                return Some(format!(
                    "expected disclosed-gap Lean refusal/fault for {expected:?} ({category:?}), got {:?}",
                    l.outcome
                ));
            }
            let verdict_ok = if lean.is_some() {
                matches!(verdict, TraceVerdict::DisclosedGapArtifact { .. })
            } else if miri.is_some() {
                matches!(verdict, TraceVerdict::DegradedNoLean { .. })
            } else {
                matches!(verdict, TraceVerdict::DegradedNoMiri { .. })
            };
            if !verdict_ok {
                return Some(format!(
                    "unexpected verdict for {expected:?} ({category:?}) (miri={}, lean={}): {verdict}",
                    miri.is_some(),
                    lean.is_some(),
                ));
            }
            None
        }
        ExpectedCaseClass::UndefinedBehavior => {
            let Some(ub_spec) = expected_ub else {
                return Some(format!(
                    "expected non-empty `expected_ub` fault cause spec for {expected:?} ({category:?})"
                ));
            };
            let miri_marker = ub_spec.miri_marker.trim();
            if ub_spec.class == UbFaultClass::Unclassified || miri_marker.is_empty() {
                return Some(format!(
                    "invalid `expected_ub` spec for {expected:?} ({category:?}): class={:?}, miri_marker={:?}",
                    ub_spec.class, ub_spec.miri_marker
                ));
            }
            if !rustc_dual.skipped_for_ub {
                return Some(format!(
                    "expected host rustc execution to be skipped for {expected:?} ({category:?})"
                ));
            }
            if let Some(m) = miri {
                match &m.outcome {
                    TerminalOutcome::FaultUb { detail } => {
                        let actual_class = classify_ub_fault_detail(detail);
                        if actual_class != ub_spec.class {
                            return Some(format!(
                                "Miri UB fault class mismatch for {expected:?} ({category:?}): expected {:?}, got {actual_class:?} ({detail})",
                                ub_spec.class
                            ));
                        }
                        if !detail.contains(miri_marker) {
                            return Some(format!(
                                "Miri UB diagnostic marker mismatch for {expected:?} ({category:?}): expected substring {miri_marker:?}, got {detail:?}"
                            ));
                        }
                    }
                    other => {
                        return Some(format!(
                            "expected Miri FaultUb for {expected:?} ({category:?}), got {other:?}"
                        ));
                    }
                }
            }
            if let Some(l) = lean {
                let lean_marker =
                    ub_spec.lean_marker.as_deref().map(str::trim).filter(|s| !s.is_empty());
                let lean_refusal_marker =
                    ub_spec.lean_refusal_marker.as_deref().map(str::trim).filter(|s| !s.is_empty());
                if !spec_or_case_requires_strict_refusal
                    && lean_marker.is_some()
                    && lean_refusal_marker.is_some()
                {
                    return Some(format!(
                        "conflicting `expected_ub` spec for {expected:?} ({category:?}): both `lean_marker` and `lean_refusal_marker` set without strict-refusal duality"
                    ));
                }
                if strict_multicall_refusal_required {
                    match &l.outcome {
                        TerminalOutcome::CaptureRefused { reason } => {
                            if let Some(rm) = lean_refusal_marker
                                && !reason.contains(rm)
                            {
                                return Some(format!(
                                    "StrictVerbatim UB refusal marker mismatch for {expected:?} ({category:?}): expected substring {rm:?}, got {reason:?}"
                                ));
                            }
                        }
                        other => {
                            return Some(format!(
                                "expected CaptureRefused Lean outcome in StrictVerbatim for multi-call {expected:?} ({category:?}), got {other:?}"
                            ));
                        }
                    }
                } else {
                    match &l.outcome {
                        TerminalOutcome::FaultUb { detail } => {
                            let actual_class = classify_ub_fault_detail(detail);
                            if actual_class != ub_spec.class {
                                return Some(format!(
                                    "Lean UB fault class mismatch for {expected:?} ({category:?}): expected {:?}, got {actual_class:?} ({detail})",
                                    ub_spec.class
                                ));
                            }
                            if let Some(lm) = lean_marker
                                && !detail.contains(lm)
                            {
                                return Some(format!(
                                    "Lean UB diagnostic marker mismatch for {expected:?} ({category:?}): expected substring {lm:?}, got {detail:?}"
                                ));
                            }
                        }
                        TerminalOutcome::CaptureRefused { reason } => {
                            if let Some(lm) = lean_marker {
                                return Some(format!(
                                    "expected Lean FaultUb matching {lm:?} for {expected:?} ({category:?}) in {lean_mode:?}, got CaptureRefused({reason:?})"
                                ));
                            }
                            let Some(rm) = lean_refusal_marker else {
                                return Some(format!(
                                    "missing `expected_ub.lean_refusal_marker` to validate conservative Lean CaptureRefused for {expected:?} ({category:?}): {reason:?}"
                                ));
                            };
                            if !reason.contains(rm) {
                                return Some(format!(
                                    "Lean UB refusal marker mismatch for {expected:?} ({category:?}): expected substring {rm:?}, got {reason:?}"
                                ));
                            }
                        }
                        other => {
                            if let Some(lm) = lean_marker {
                                return Some(format!(
                                    "expected Lean FaultUb matching {lm:?} for {expected:?} ({category:?}) in {lean_mode:?}, got {other:?}"
                                ));
                            }
                            return Some(format!(
                                "expected Lean FaultUb or explicit CaptureRefused for {expected:?} ({category:?}) in {lean_mode:?}, got {other:?}"
                            ));
                        }
                    }
                }
            }
            if let Some(me) = mir_eval {
                let mir_eval_marker =
                    ub_spec.mir_eval_marker.as_deref().map(str::trim).filter(|s| !s.is_empty());
                match &me.outcome {
                    TerminalOutcome::FaultUb { detail } => {
                        let actual_class = classify_ub_fault_detail(detail);
                        if actual_class != ub_spec.class {
                            return Some(format!(
                                "anneal-mir-eval UB fault class mismatch for {expected:?} ({category:?}): expected {:?}, got {actual_class:?} ({detail})",
                                ub_spec.class
                            ));
                        }
                        let Some(mm) = mir_eval_marker else {
                            return Some(format!(
                                "missing `expected_ub.mir_eval_marker` to validate anneal-mir-eval FaultUb for {expected:?} ({category:?}): {detail:?}"
                            ));
                        };
                        if !detail.contains(mm) {
                            return Some(format!(
                                "anneal-mir-eval UB diagnostic marker mismatch for {expected:?} ({category:?}): expected substring {mm:?}, got {detail:?}"
                            ));
                        }
                    }
                    other => {
                        let is_expected_refusal = matches!(
                            other,
                            TerminalOutcome::CaptureRefused { reason }
                                if !matches!(lean_program_spec, LeanProgramSpec::CapturedRust { .. })
                                    || lean.is_some_and(|l| {
                                        matches!(l.outcome, TerminalOutcome::CaptureRefused { .. })
                                    })
                                    || reason.contains("MIR capture artifacts unavailable")
                        );
                        if !is_expected_refusal {
                            return Some(format!(
                                "expected anneal-mir-eval FaultUb matching {mir_eval_marker:?} for {expected:?} ({category:?}), got {other:?}"
                            ));
                        }
                    }
                }
            }
            if miri.is_none() && lean.is_none() {
                return Some(format!(
                    "cannot certify {expected:?} ({category:?}) probe when both Miri and Lean authorities are disabled or unavailable"
                ));
            }
            let verdict_ok = match (miri.is_some(), lean.is_some()) {
                (true, true) if strict_multicall_refusal_required => matches!(
                    verdict,
                    TraceVerdict::ConservativeOverApprox { undeclared_ub_fault: false, .. }
                ),
                (true, true) => {
                    matches!(verdict, TraceVerdict::Agree)
                        || matches!(
                            verdict,
                            TraceVerdict::ConservativeOverApprox { undeclared_ub_fault: false, .. }
                        )
                }
                (false, true) => matches!(verdict, TraceVerdict::DegradedNoMiri { .. }),
                (true, false) => matches!(verdict, TraceVerdict::DegradedNoLean { .. }),
                (false, false) => false,
            };
            if !verdict_ok {
                return Some(format!(
                    "unexpected verdict for {expected:?} ({category:?}) (miri={}, lean={}): {verdict}",
                    miri.is_some(),
                    lean.is_some(),
                ));
            }
            None
        }
    }
}

/// Per-case 4-way differential execution receipt.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CaseReport {
    pub case_id: String,
    pub category: CaseCategory,
    pub expected_class: ExpectedCaseClass,
    pub verdict: TraceVerdict,
    #[serde(default)]
    pub expectation_violation: Option<String>,
    pub rustc_dual: RustcDualResult,
    pub miri: Option<AuthorityRunResult>,
    pub lean: Option<AuthorityRunResult>,
    pub lean_strict_probe: Option<AuthorityRunResult>,
    pub mir_eval: Option<AuthorityRunResult>,
    pub metamorphic: Option<MetamorphicDualityReceipt>,
}

/// Decide whether native host `rustc` execution must be skipped to prevent
/// executing uncertified Undefined Behavior on the host:
/// 1. Miri detected `TerminalOutcome::FaultUb`,
/// 2. Miri was provisioned and returned a per-case `tool_error` before
///    certifying UB absence (even on cases not pre-labeled `expected_ub`), or
/// 3. The case is pre-labeled `expected_ub` while Miri is unavailable.
pub fn should_skip_host_rustc(
    case_is_expected_ub: bool,
    miri_res: Option<&AuthorityRunResult>,
) -> Option<&'static str> {
    let miri_detected_ub =
        miri_res.is_some_and(|m| matches!(m.outcome, TerminalOutcome::FaultUb { .. }));
    let miri_had_tool_error = miri_res.is_some_and(|m| m.tool_error.is_some());
    if miri_detected_ub {
        Some("skipped native rustc execution because Miri detected Undefined Behavior")
    } else if miri_had_tool_error {
        Some("skipped native rustc execution because Miri reported tool_error")
    } else if case_is_expected_ub && miri_res.is_none() {
        Some("skipped native rustc execution on expected-UB probe while Miri was unavailable")
    } else {
        None
    }
}

/// Evaluate metamorphic equivalence between a multi-call case execution and its
/// source-inlined single-body twin across `rustc`, `miri`, and `lean`.
///
/// Marks conservative Lean outcomes (`CaptureRefused` or `Diverged`) on either
/// twin leg as [`MetamorphicStatus::SkippedConservative`]
/// (`duality_holds == false`) so conservative refusals or step-fuel cutoffs
/// are never counted as `metamorphic_passed`.
pub fn evaluate_metamorphic_duality(
    called_rustc: &RustcDualResult,
    called_miri: Option<&AuthorityRunResult>,
    called_lean: &AuthorityRunResult,
    twin_rustc: &RustcDualResult,
    twin_miri: Option<&AuthorityRunResult>,
    inlined_lean: AuthorityRunResult,
) -> MetamorphicDualityReceipt {
    let found_tool_err = [
        if called_rustc.skipped_for_ub { None } else { Some(&called_rustc.o0) },
        if called_rustc.skipped_for_ub { None } else { Some(&called_rustc.o2) },
        called_miri,
        Some(called_lean),
        Some(&inlined_lean),
        if twin_rustc.skipped_for_ub { None } else { Some(&twin_rustc.o0) },
        if twin_rustc.skipped_for_ub { None } else { Some(&twin_rustc.o2) },
        twin_miri,
    ]
    .into_iter()
    .flatten()
    .find_map(|a| a.tool_error.as_ref().map(|e| (a.authority.clone(), e.clone())));
    if let Some((auth_name, err_msg)) = found_tool_err {
        let detail = format!("metamorphic_duality: authority tool error in {auth_name}: {err_msg}");
        return MetamorphicDualityReceipt {
            called_lean: called_lean.clone(),
            inlined_lean,
            inlined_rustc_parity_ok: twin_rustc.parity_ok,
            inlined_miri_matched: None,
            tool_error: Some((auth_name, err_msg)),
            status: MetamorphicStatus::Failed,
            duality_holds: false,
            detail,
            failed_relations: vec!["tool_error".to_string()],
            twin_outcome_summary: String::new(),
        };
    }

    let outcomes_match = |a: &AuthorityRunResult, b: &AuthorityRunResult| -> bool {
        if matches!(a.outcome, TerminalOutcome::FaultUb { .. })
            && matches!(b.outcome, TerminalOutcome::FaultUb { .. })
        {
            compare_ub_fault_results(a, b).is_ok()
        } else {
            a.outcome.semantically_eq(&b.outcome)
        }
    };

    let inlined_miri_matched = match (called_miri, twin_miri) {
        (Some(cm), Some(tm)) => Some(
            outcomes_match(cm, tm)
                && cm.caller_frame_law.is_satisfied()
                && tm.caller_frame_law.is_satisfied(),
        ),
        (Some(_), None) | (None, Some(_)) => Some(false),
        (None, None) => None,
    };

    let called_is_conservative = matches!(
        called_lean.outcome,
        TerminalOutcome::CaptureRefused { .. } | TerminalOutcome::Diverged { .. }
    );
    let inlined_is_conservative = matches!(
        inlined_lean.outcome,
        TerminalOutcome::CaptureRefused { .. } | TerminalOutcome::Diverged { .. }
    );
    let lean_twin_conservative = called_is_conservative || inlined_is_conservative;

    let mut problems = Vec::new();
    let mut failed_relations = Vec::new();
    if !lean_twin_conservative && !outcomes_match(called_lean, &inlined_lean) {
        failed_relations.push("lean_called_vs_inlined".to_string());
        problems.push(format!(
            "metamorphic_duality: Lean multi-call vs source-inlined outcome mismatch: {:?} vs {:?}",
            called_lean.outcome, inlined_lean.outcome
        ));
    }
    if !called_rustc.skipped_for_ub && !called_rustc.parity_ok {
        failed_relations.push("called_rustc_o0_vs_o2".to_string());
        problems.push(format!(
            "metamorphic_duality: original multi-call rustc O0 vs O2 mismatch: {:?}",
            called_rustc.mismatch_detail
        ));
    }
    if !twin_rustc.skipped_for_ub && !twin_rustc.parity_ok {
        failed_relations.push("inlined_rustc_o0_vs_o2".to_string());
        problems.push(format!(
            "metamorphic_duality: source-inlined twin rustc O0 vs O2 mismatch: {:?}",
            twin_rustc.mismatch_detail
        ));
    }
    if !called_rustc.skipped_for_ub
        && !twin_rustc.skipped_for_ub
        && (!called_rustc.o0.outcome.semantically_eq(&twin_rustc.o0.outcome)
            || !called_rustc.o2.outcome.semantically_eq(&twin_rustc.o2.outcome))
    {
        failed_relations.push("rustc_called_vs_inlined".to_string());
        problems.push(format!(
            "metamorphic_duality: rustc multi-call vs source-inlined mismatch: O0=({:?} vs {:?}), O2=({:?} vs {:?})",
            called_rustc.o0.outcome,
            twin_rustc.o0.outcome,
            called_rustc.o2.outcome,
            twin_rustc.o2.outcome,
        ));
    }
    for (tag, desc, lean_label, rustc_dual, miri_opt, lean_res, is_conservative) in [
        (
            "called",
            "original multi-call",
            "CompositionalITree",
            called_rustc,
            called_miri,
            called_lean,
            called_is_conservative,
        ),
        (
            "inlined",
            "source-inlined twin",
            "StrictVerbatim",
            twin_rustc,
            twin_miri,
            &inlined_lean,
            inlined_is_conservative,
        ),
    ] {
        if !is_conservative
            && !rustc_dual.skipped_for_ub
            && !rustc_dual.o0.outcome.semantically_eq(&lean_res.outcome)
        {
            failed_relations.push(format!("{tag}_rustc_vs_lean"));
            problems.push(format!(
                "metamorphic_duality: {desc} rustc-O0 vs Lean {lean_label} mismatch: {:?} vs {:?}",
                rustc_dual.o0.outcome, lean_res.outcome
            ));
        }
        if !is_conservative
            && let Some(m) = miri_opt
            && (matches!(m.outcome, TerminalOutcome::FaultUb { .. }) || rustc_dual.skipped_for_ub)
            && !outcomes_match(m, lean_res)
        {
            failed_relations.push(format!("{tag}_miri_vs_lean_ub"));
            let detail = if matches!(m.outcome, TerminalOutcome::FaultUb { .. })
                && matches!(lean_res.outcome, TerminalOutcome::FaultUb { .. })
            {
                match compare_ub_fault_results(m, lean_res) {
                    Err(msg) => msg,
                    Ok(()) => format!(
                        "{desc} Miri detected UB ({:?}) while Lean {lean_label} produced {:?}",
                        m.outcome, lean_res.outcome
                    ),
                }
            } else {
                format!(
                    "{desc} Miri detected UB ({:?}) while Lean {lean_label} produced {:?}",
                    m.outcome, lean_res.outcome
                )
            };
            problems.push(format!("metamorphic_duality: {detail}"));
        }
        if rustc_dual.skipped_for_ub && miri_opt.is_none() && lean_res.outcome.is_accepting() {
            failed_relations.push(format!("{tag}_skipped_ub_lean_accept"));
            problems.push(format!(
                "metamorphic_duality: {desc} skipped host rustc for UB without Miri, but Lean {lean_label} accepted with {:?}",
                lean_res.outcome
            ));
        }
    }
    if inlined_miri_matched == Some(false) {
        failed_relations.push("miri_called_vs_inlined".to_string());
        problems.push(format!(
            "metamorphic_duality: Miri multi-call vs source-inlined mismatch: {:?} vs {:?}",
            called_miri.map(|m| &m.outcome),
            twin_miri.map(|m| &m.outcome)
        ));
    }
    let called_rustc_frame_ok = called_rustc.skipped_for_ub
        || (called_rustc.o0.caller_frame_law.is_satisfied()
            && called_rustc.o2.caller_frame_law.is_satisfied());
    let twin_rustc_frame_ok = twin_rustc.skipped_for_ub
        || (twin_rustc.o0.caller_frame_law.is_satisfied()
            && twin_rustc.o2.caller_frame_law.is_satisfied());
    let rustc_preservation_ok = called_rustc_frame_ok && twin_rustc_frame_ok;
    if !rustc_preservation_ok
        || !called_lean.caller_frame_law.is_satisfied()
        || !inlined_lean.caller_frame_law.is_satisfied()
    {
        if !called_rustc_frame_ok {
            failed_relations.push("metamorphic_caller_frame_law:called_rustc".to_string());
        }
        if !twin_rustc_frame_ok {
            failed_relations.push("metamorphic_caller_frame_law:inlined_rustc".to_string());
        }
        if !called_lean.caller_frame_law.is_satisfied() {
            failed_relations.push("metamorphic_caller_frame_law:called_lean".to_string());
        }
        if !inlined_lean.caller_frame_law.is_satisfied() {
            failed_relations.push("metamorphic_caller_frame_law:inlined_lean".to_string());
        }
        problems.push("metamorphic_duality: CallerFrameLaw failed in metamorphic pair".to_string());
    }

    let called_o0_tag =
        if called_rustc.skipped_for_ub { "skipped" } else { called_rustc.o0.outcome.kind_tag() };
    let called_o2_tag =
        if called_rustc.skipped_for_ub { "skipped" } else { called_rustc.o2.outcome.kind_tag() };
    let inlined_o0_tag =
        if twin_rustc.skipped_for_ub { "skipped" } else { twin_rustc.o0.outcome.kind_tag() };
    let inlined_o2_tag =
        if twin_rustc.skipped_for_ub { "skipped" } else { twin_rustc.o2.outcome.kind_tag() };
    let called_miri_tag = called_miri.map(|m| m.outcome.kind_tag()).unwrap_or("none");
    let inlined_miri_tag = twin_miri.map(|m| m.outcome.kind_tag()).unwrap_or("none");
    let twin_outcome_summary = format!(
        "called_o0={called_o0_tag},called_o2={called_o2_tag},called_miri={called_miri_tag},inlined_o0={inlined_o0_tag},inlined_o2={inlined_o2_tag},inlined_miri={inlined_miri_tag},called_lean={},inlined_lean={}",
        called_lean.outcome.kind_tag(),
        inlined_lean.outcome.kind_tag(),
    );

    let (status, duality_holds, detail) = if !problems.is_empty() {
        (MetamorphicStatus::Failed, false, problems.join("; "))
    } else if lean_twin_conservative {
        let reason = format!(
            "Lean twin conservative outcome (called={}, inlined={}); compiler/Miri twins matched",
            called_lean.outcome.kind_tag(),
            inlined_lean.outcome.kind_tag(),
        );
        let detail = format!("metamorphic_duality: skipped conservative ({reason})");
        (MetamorphicStatus::SkippedConservative { reason }, false, detail)
    } else {
        (
            MetamorphicStatus::Passed,
            true,
            "multi-call CompositionalITree matches source-inlined StrictVerbatim across all active authorities"
                .to_string(),
        )
    };

    MetamorphicDualityReceipt {
        called_lean: called_lean.clone(),
        inlined_lean,
        inlined_rustc_parity_ok: twin_rustc.parity_ok,
        inlined_miri_matched,
        tool_error: None,
        status,
        duality_holds,
        detail,
        failed_relations,
        twin_outcome_summary,
    }
}

/// Summary counts across a differential suite or fuzz campaign.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct VerdictCounts {
    pub total: usize,
    pub agree: usize,
    pub degraded_no_miri: usize,
    pub degraded_no_lean: usize,
    pub unsound_accept: usize,
    pub conservative_over_approx: usize,
    pub undeclared_ub_fault: usize,
    pub disclosed_gap_artifact: usize,
    pub tool_error: usize,
    #[serde(default)]
    pub expectation_mismatches: usize,
    pub metamorphic_checked: usize,
    pub metamorphic_passed: usize,
    pub metamorphic_skipped: usize,
    pub rustc_o0_o2_parity_checked: usize,
}

/// Full structured report emitted by library API and CLI (`--json-report`).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DifferentialReport {
    pub miri_status: String,
    pub miri_available: bool,
    pub require_miri: bool,
    pub mir_eval_status: String,
    pub lean_mode: LeanTraceMode,
    pub counts: VerdictCounts,
    pub by_category: BTreeMap<CaseCategory, usize>,
    pub cases: Vec<CaseReport>,
    pub witnesses: Vec<WitnessArtifact>,
}

impl DifferentialReport {
    pub fn from_cases(
        miri_status: &str,
        miri_available: bool,
        require_miri: bool,
        mir_eval_status: &str,
        lean_mode: LeanTraceMode,
        cases: Vec<CaseReport>,
        witnesses: Vec<WitnessArtifact>,
    ) -> Self {
        let mut counts = VerdictCounts { total: cases.len(), ..Default::default() };
        let mut by_category = BTreeMap::new();
        for c in &cases {
            *by_category.entry(c.category).or_insert(0) += 1;
            if c.expectation_violation.is_some() {
                counts.expectation_mismatches += 1;
            }
            if c.rustc_dual.parity_ok {
                counts.rustc_o0_o2_parity_checked += 1;
            }
            if let Some(m) = &c.metamorphic {
                counts.metamorphic_checked += 1;
                match &m.status {
                    MetamorphicStatus::Passed => counts.metamorphic_passed += 1,
                    MetamorphicStatus::SkippedConservative { .. } => {
                        counts.metamorphic_skipped += 1;
                    }
                    MetamorphicStatus::Failed => {}
                }
            }
            match &c.verdict {
                TraceVerdict::Agree => counts.agree += 1,
                TraceVerdict::DegradedNoMiri { .. } => counts.degraded_no_miri += 1,
                TraceVerdict::DegradedNoLean { .. } => counts.degraded_no_lean += 1,
                TraceVerdict::UnsoundAccept { .. } => counts.unsound_accept += 1,
                TraceVerdict::ConservativeOverApprox { undeclared_ub_fault, .. } => {
                    counts.conservative_over_approx += 1;
                    if *undeclared_ub_fault {
                        counts.undeclared_ub_fault += 1;
                    }
                }
                TraceVerdict::DisclosedGapArtifact { .. } => counts.disclosed_gap_artifact += 1,
                TraceVerdict::ToolError { .. } => counts.tool_error += 1,
            }
        }
        Self {
            miri_status: miri_status.to_string(),
            miri_available,
            require_miri,
            mir_eval_status: mir_eval_status.to_string(),
            lean_mode,
            counts,
            by_category,
            cases,
            witnesses,
        }
    }

    pub fn has_critical_failures(&self) -> bool {
        self.counts.total == 0
            || self.counts.unsound_accept > 0
            || self.counts.undeclared_ub_fault > 0
            || self.counts.tool_error > 0
            || self.counts.expectation_mismatches > 0
            || (self.require_miri && (!self.miri_available || self.counts.degraded_no_miri > 0))
    }
}

/// Validate CLI / campaign selection flags before initializing any authorities,
/// rejecting orphaned `--filter` flags, vacuous `--fuzz 0` campaigns (whether
/// `--corpus` is also set or not), and empty test selections.
pub fn validate_run_plan(
    run_corpus: bool,
    filter: Option<&str>,
    fuzz: Option<usize>,
) -> Result<(), String> {
    validate_cli_run_plan(run_corpus, filter, fuzz, false, false)
}

/// Full CLI plan validator enforcing `--shrink` and `--witness-dir` coupling to
/// an active `--fuzz <N>` campaign in addition to [`validate_run_plan`] checks.
pub fn validate_cli_run_plan(
    run_corpus: bool,
    filter: Option<&str>,
    fuzz: Option<usize>,
    shrink: bool,
    has_witness_dir: bool,
) -> Result<(), String> {
    if !run_corpus && filter.is_some() {
        return Err(
            "--filter requires corpus execution (pass --corpus alongside --fuzz, or omit --filter)"
                .to_string(),
        );
    }
    if fuzz == Some(0) {
        return Err("--fuzz count must be >= 1 (got 0)".to_string());
    }
    if !run_corpus && fuzz.is_none() {
        return Err("no test cases selected (pass --corpus or --fuzz <N>)".to_string());
    }
    if shrink && fuzz.is_none() {
        return Err("--shrink requires a fuzz campaign (pass --fuzz <N>)".to_string());
    }
    if has_witness_dir && (!shrink || fuzz.is_none()) {
        return Err("--witness-dir requires both --fuzz <N> and --shrink".to_string());
    }
    Ok(())
}

/// Resolve the `anneal/` repository root from `CARGO_MANIFEST_DIR`.
pub fn workspace_anneal_root() -> Result<PathBuf, String> {
    anneal_testkit::ToolchainEnv::repo_root_from_manifest(Path::new(env!("CARGO_MANIFEST_DIR")))
}
