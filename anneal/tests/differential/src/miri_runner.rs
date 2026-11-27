// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Reference-oracle runner invoking Miri on staged differential fixtures.
//!
//! Uses a file-locked offline `cargo miri setup` cache configured with
//! `CARGO_NET_OFFLINE=true` and vendored crates from
//! `<rust_sysroot>/lib/rustlib/src/rust/library/vendor` inside an isolated
//! scratch `CARGO_HOME/config.toml` unless `ANNEAL_MIRI_SYSROOT` explicitly
//! provides a valid prepared non-symlink sysroot.

use std::{
    collections::{BTreeMap, BTreeSet, hash_map::RandomState},
    env,
    ffi::{OsStr, OsString},
    fmt::Write as _,
    fs::{self, File},
    hash::{BuildHasher as _, Hasher as _},
    io::Read as _,
    path::{Component, Path, PathBuf},
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    },
    thread,
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};

use anneal_testkit::{Invocation, Termination};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use sha2::{Digest, Sha256};

use crate::{
    corpus::LitmusCase,
    r#gen::{GenProgram, render_batch_crate},
    lean_runner::{
        effective_timeout_duration, effective_timeout_secs, sha256_bytes_hex, sha256_file_hex,
    },
    rustc_runner::{
        FuzzExecCase, ImmutableStagingDir, PinnedPrivateDir, STORE_PREFIX, TRUSTED_CHILD_PATH_DIRS,
        build_child_path_with_bins, collect_rel_file_sha256s_nofollow, copy_opened_file_to_new_dst,
        copy_validated_subtree, copy_verified_regular_file, is_global_compiler_or_sysroot_stderr,
        prepare_sysroot_binary, prepare_sysroot_binary_in, run_supervised_in_tmp,
        sha256_opened_file_hex, try_validate_store_contained_path,
        validate_store_contained_dir_tree, validate_store_contained_entry,
    },
    verdict::{Expectation, IntKind, MirValue, ObservedOutcome, OrderingKind},
};

const MIRI_RET_STEM: &str = "ANNEAL_MIRI_RET";
const MIRI_RET_PREFIX: &str = "ANNEAL_MIRI_RET=";
static MIRI_MARKER_SEQ: AtomicU64 = AtomicU64::new(0);
const MIRI_BATCH_CASE_PREFIX: &str = "ANNEAL_MIRI_CASE:";
const MIRI_RUN_PREFIX: &str = "ANNEAL_MIRI_RUN:";
const MIRI_BATCH_CHUNK_SIZE: usize = 32;
const PINNED_MIRI_TARGET: &str = "x86_64-unknown-linux-gnu";
const MIRI_SETUP_TIMEOUT_SECS: u64 = 300;
const MIRI_CASE_TIMEOUT_SECS: u64 = 120;
const RUSTC_PROBE_TIMEOUT_SECS: u64 = 30;

/// Prepared Miri binary and sysroot coordinates for executing reference checks.
#[derive(Clone, Debug)]
pub struct MiriSession {
    pub miri_bin: PathBuf,
    pub rust_sysroot: PathBuf,
    pub miri_sysroot: PathBuf,
    pub ld_library_path: String,
    pub(crate) validated_tmpdir: Option<PathBuf>,
    pub(crate) _sysroot_staging: Option<Arc<ImmutableStagingDir>>,
    pub(crate) _miri_sysroot_staging: Option<Arc<ImmutableStagingDir>>,
}

#[derive(Clone, Copy)]
struct MiriChildEnv<'a> {
    ld_path: &'a str,
    path_env: &'a OsStr,
    tmpdir: Option<&'a Path>,
}

#[derive(Clone, Copy)]
enum MiriCacheRoot<'a> {
    Path(&'a Path),
    Pinned(&'a PinnedPrivateDir),
}

impl MiriSession {
    /// Locate `miri` alongside `rust_sysroot` and resolve or offline-prepare
    /// a Miri target sysroot under `cache_root`.
    pub fn prepare(rust_sysroot: &Path, cache_root: &Path) -> Result<Self, String> {
        Self::prepare_with_env(rust_sysroot, cache_root, |k| env::var_os(k))
    }

    pub fn prepare_with_env(
        rust_sysroot: &Path,
        cache_root: &Path,
        get_env: impl Fn(&str) -> Option<OsString>,
    ) -> Result<Self, String> {
        let caller_cwd =
            env::current_dir().map_err(|e| format!("determine caller working directory: {e}"))?;
        Self::prepare_with_env_at(rust_sysroot, cache_root, &caller_cwd, get_env)
    }

    fn prepare_with_env_at(
        rust_sysroot: &Path,
        cache_root: &Path,
        caller_cwd: &Path,
        get_env: impl Fn(&str) -> Option<OsString>,
    ) -> Result<Self, String> {
        let validated_tmpdir = crate::mir_eval_runner::validate_optional_existing_dir_env(
            get_env("TMPDIR").as_deref(),
            caller_cwd,
            "TMPDIR",
        )?;
        let prepared = prepare_sysroot_binary_in(
            rust_sysroot,
            "bin/miri",
            Path::new(STORE_PREFIX),
            validated_tmpdir.as_deref(),
            "Miri binary",
        )?;
        Self::prepare_from_sysroot_at_cache(
            prepared,
            MiriCacheRoot::Path(cache_root),
            caller_cwd,
            validated_tmpdir,
            get_env,
        )
    }

    pub(crate) fn prepare_from_sysroot(
        prepared: crate::rustc_runner::PreparedSysroot,
        cache_root: &Path,
    ) -> Result<Self, String> {
        let caller_cwd =
            env::current_dir().map_err(|e| format!("determine caller working directory: {e}"))?;
        let get_env = |k: &str| env::var_os(k);
        let validated_tmpdir = crate::mir_eval_runner::validate_optional_existing_dir_env(
            get_env("TMPDIR").as_deref(),
            &caller_cwd,
            "TMPDIR",
        )?;
        Self::prepare_from_sysroot_at_cache(
            prepared,
            MiriCacheRoot::Path(cache_root),
            &caller_cwd,
            validated_tmpdir,
            get_env,
        )
    }

    pub(crate) fn prepare_from_sysroot_pinned(
        prepared: crate::rustc_runner::PreparedSysroot,
        cache_root: &PinnedPrivateDir,
    ) -> Result<Self, String> {
        let caller_cwd =
            env::current_dir().map_err(|e| format!("determine caller working directory: {e}"))?;
        let get_env = |k: &str| env::var_os(k);
        let validated_tmpdir = crate::mir_eval_runner::validate_optional_existing_dir_env(
            get_env("TMPDIR").as_deref(),
            &caller_cwd,
            "TMPDIR",
        )?;
        Self::prepare_from_sysroot_at_cache(
            prepared,
            MiriCacheRoot::Pinned(cache_root),
            &caller_cwd,
            validated_tmpdir,
            get_env,
        )
    }

    fn prepare_from_sysroot_at_cache(
        prepared: crate::rustc_runner::PreparedSysroot,
        cache: MiriCacheRoot<'_>,
        caller_cwd: &Path,
        validated_tmpdir: Option<PathBuf>,
        get_env: impl Fn(&str) -> Option<OsString>,
    ) -> Result<Self, String> {
        let raw_sysroot = prepared.sysroot;
        let raw_miri_bin = if let Some(ref staging) = prepared._staging {
            let _ = staging.open_verified_rel_file(Path::new("bin/miri"), "Miri binary")?;
            raw_sysroot.join("bin/miri")
        } else {
            crate::rustc_runner::validated_store_aware_executable(
                &raw_sysroot.join("bin/miri"),
                Path::new(STORE_PREFIX),
                caller_cwd,
                "Miri binary",
            )?
        };
        let raw_ld = prepared.ld_library_path;
        let rust_sysroot =
            ImmutableStagingDir::pin_path_with_guards(&[prepared._staging.as_ref()], &raw_sysroot);
        let miri_bin =
            ImmutableStagingDir::pin_path_with_guards(&[prepared._staging.as_ref()], &raw_miri_bin);
        let ld_library_path = if raw_ld.is_empty() {
            String::new()
        } else {
            ImmutableStagingDir::pin_env_paths_with_guards(
                &[prepared._staging.as_ref()],
                OsStr::new(&raw_ld),
            )?
            .to_string_lossy()
            .into_owned()
        };

        if let Some(explicit) =
            get_env("ANNEAL_MIRI_SYSROOT").filter(|v| !v.is_empty()).map(PathBuf::from)
        {
            let (raw_miri_sysroot, miri_staging) = stage_miri_sysroot_dir_in(
                &explicit,
                caller_cwd,
                Path::new(STORE_PREFIX),
                validated_tmpdir.as_deref(),
                "ANNEAL_MIRI_SYSROOT",
            )?;
            let ver_tag = rustc_version_tag(
                &rust_sysroot,
                &ld_library_path,
                get_env("PATH").as_deref(),
                validated_tmpdir.as_deref(),
                caller_cwd,
            )?;
            let setup_sha = compute_miri_setup_input_sha256_inner(
                &raw_sysroot,
                &ver_tag,
                prepared._staging.as_deref(),
            )?;
            verify_miri_sysroot_stamp_with_store(
                &raw_miri_sysroot,
                miri_staging.as_deref(),
                Path::new(STORE_PREFIX),
                &ver_tag,
                &setup_sha,
            )?;
            let miri_sysroot = ImmutableStagingDir::pin_path_with_guards(
                &[miri_staging.as_ref()],
                &raw_miri_sysroot,
            );
            return Ok(Self {
                miri_bin,
                rust_sysroot,
                miri_sysroot,
                ld_library_path,
                validated_tmpdir,
                _sysroot_staging: prepared._staging,
                _miri_sysroot_staging: miri_staging,
            });
        }

        let ver_tag = rustc_version_tag(
            &rust_sysroot,
            &ld_library_path,
            get_env("PATH").as_deref(),
            validated_tmpdir.as_deref(),
            caller_cwd,
        )?;
        let setup_sha = compute_miri_setup_input_sha256_inner(
            &raw_sysroot,
            &ver_tag,
            prepared._staging.as_deref(),
        )?;
        let cache_id = format!("{ver_tag}-{}", &setup_sha[..16]);
        let target_rel = PathBuf::from(format!("miri-sysroot-{cache_id}"));
        let lock_rel = PathBuf::from(format!("miri-sysroot-{cache_id}.setup.lock"));
        let (canon_cache_root, target_dir, lock_path) = match cache {
            MiriCacheRoot::Path(cache_root) => {
                fs::create_dir_all(cache_root)
                    .map_err(|e| format!("create cache dir {}: {e}", cache_root.display()))?;
                let canon = fs::canonicalize(cache_root)
                    .map_err(|e| format!("canonicalize cache dir {}: {e}", cache_root.display()))?;
                let t = canon.join(&target_rel);
                let l = canon.join(&lock_rel);
                (Some(canon), t, l)
            }
            MiriCacheRoot::Pinned(pinned) => {
                (None, pinned.pin_path(&target_rel), pinned.pin_path(&lock_rel))
            }
        };
        let lock_file = File::options()
            .create(true)
            .read(true)
            .write(true)
            .truncate(false)
            .open(&lock_path)
            .map_err(|e| format!("open Miri lock {}: {e}", lock_path.display()))?;
        lock_file
            .lock()
            .map_err(|e| format!("acquire Miri setup lock {}: {e}", lock_path.display()))?;

        let cached_ready = match cache {
            MiriCacheRoot::Path(_) => {
                let caller = canon_cache_root.as_deref().unwrap_or(caller_cwd);
                if fs::symlink_metadata(&target_dir).is_ok() {
                    stage_and_verify_miri_sysroot_in(
                        &target_dir,
                        caller,
                        Path::new(STORE_PREFIX),
                        validated_tmpdir.as_deref(),
                        &ver_tag,
                        &setup_sha,
                        "cached Miri sysroot",
                    )
                    .ok()
                } else {
                    None
                }
            }
            MiriCacheRoot::Pinned(pinned) => {
                if pinned.has_rel_dir(&target_rel, "cached Miri sysroot") {
                    stage_and_verify_miri_sysroot_from_pinned_in(
                        pinned,
                        &target_rel,
                        Path::new(STORE_PREFIX),
                        validated_tmpdir.as_deref(),
                        &ver_tag,
                        &setup_sha,
                        "cached Miri sysroot",
                    )
                    .ok()
                } else {
                    None
                }
            }
        };
        let (raw_miri_sysroot, miri_staging) = match cached_ready {
            Some(pair) => pair,
            None => {
                build_offline_miri_sysroot_in(
                    cache,
                    &rust_sysroot,
                    &miri_bin,
                    &target_dir,
                    &ver_tag,
                    &setup_sha,
                    &ld_library_path,
                    get_env("PATH").as_deref(),
                    validated_tmpdir.as_deref(),
                    caller_cwd,
                )?;
                match cache {
                    MiriCacheRoot::Path(_) => {
                        let caller = canon_cache_root.as_deref().unwrap_or(caller_cwd);
                        stage_and_verify_miri_sysroot_in(
                            &target_dir,
                            caller,
                            Path::new(STORE_PREFIX),
                            validated_tmpdir.as_deref(),
                            &ver_tag,
                            &setup_sha,
                            "cached Miri sysroot",
                        )?
                    }
                    MiriCacheRoot::Pinned(pinned) => stage_and_verify_miri_sysroot_from_pinned_in(
                        pinned,
                        &target_rel,
                        Path::new(STORE_PREFIX),
                        validated_tmpdir.as_deref(),
                        &ver_tag,
                        &setup_sha,
                        "cached Miri sysroot",
                    )?,
                }
            }
        };
        drop(lock_file);
        let miri_sysroot =
            ImmutableStagingDir::pin_path_with_guards(&[miri_staging.as_ref()], &raw_miri_sysroot);

        Ok(Self {
            miri_bin,
            rust_sysroot,
            miri_sysroot,
            ld_library_path,
            validated_tmpdir,
            _sysroot_staging: prepared._staging,
            _miri_sysroot_staging: miri_staging,
        })
    }

    fn resolve_miri_rustc_bin(
        &self,
    ) -> Result<(PathBuf, Option<Arc<ImmutableStagingDir>>), String> {
        if let Some(ref staging) = self._sysroot_staging {
            let _ = staging.open_verified_rel_file(Path::new("bin/rustc"), "Miri rustc binary")?;
            return Ok((staging.pin_path(Path::new("bin/rustc")), None));
        }
        let prepared = prepare_sysroot_binary(
            &self.rust_sysroot,
            "bin/rustc",
            Path::new(STORE_PREFIX),
            "Miri rustc binary",
        )?;
        let pinned_bin = ImmutableStagingDir::pin_path_with_guards(
            &[prepared._staging.as_ref()],
            &prepared.binary,
        );
        Ok((pinned_bin, prepared._staging))
    }

    /// Execute all litmus cases under Miri, grouping harness generation by
    /// fixture source file and running cases across bounded worker threads.
    pub fn run_cases(
        &self,
        cases: &[LitmusCase],
    ) -> Result<BTreeMap<String, ObservedOutcome>, String> {
        let mut by_source: BTreeMap<PathBuf, Vec<&LitmusCase>> = BTreeMap::new();
        for case in cases {
            by_source.entry(case.source_abs.clone()).or_default().push(case);
        }

        let workers = thread::available_parallelism().map(|n| n.get().clamp(1, 4)).unwrap_or(1);
        let ld_path = &self.ld_library_path;
        let path_env =
            build_child_path(&self.rust_sysroot.join("bin"), env::var_os("PATH").as_deref())?;
        let (rustc_bin, _rustc_staging) = self.resolve_miri_rustc_bin()?;
        let setup_timeout = effective_timeout_secs(MIRI_SETUP_TIMEOUT_SECS)?;

        let work_root = crate::mir_eval_runner::build_temp_dir(
            "anneal-miri-work-",
            self.validated_tmpdir.as_deref(),
        )?;
        let child_env =
            MiriChildEnv { ld_path, path_env: &path_env, tmpdir: self.validated_tmpdir.as_deref() };
        let mut results = BTreeMap::new();
        struct MiriWorkItem {
            case_id: String,
            harness_path: PathBuf,
            bridge_rlib: PathBuf,
            corpus_dir: PathBuf,
            selector: String,
            token: String,
        }
        let mut work_items: Vec<MiriWorkItem> = Vec::with_capacity(cases.len());

        for (group_idx, (source_abs, group_cases)) in by_source.iter().enumerate() {
            let source_text = fs::read_to_string(source_abs)
                .map_err(|e| format!("read fixture {}: {e}", source_abs.display()))?;
            let bundle_res = build_isolated_miri_group(
                work_root.path(),
                group_idx,
                &source_text,
                group_cases,
                &rustc_bin,
                &self.miri_sysroot,
                child_env,
                Duration::from_secs(setup_timeout),
            );
            match bundle_res {
                Ok(bundle) => {
                    for case in group_cases {
                        work_items.push(MiriWorkItem {
                            case_id: case.id.clone(),
                            harness_path: bundle.harness_path.clone(),
                            bridge_rlib: bundle.bridge_rlib.clone(),
                            corpus_dir: bundle.corpus_dir.clone(),
                            selector: case.id.clone(),
                            token: bundle.token.clone(),
                        });
                    }
                }
                Err(detail) => {
                    for case in group_cases {
                        results.insert(
                            case.id.clone(),
                            ObservedOutcome::ToolError { detail: detail.clone() },
                        );
                    }
                }
            }
        }

        for chunk in work_items.chunks(workers) {
            let outcomes = thread::scope(|scope| {
                let mut handles = Vec::with_capacity(chunk.len());
                for item in chunk {
                    let miri_bin = &self.miri_bin;
                    let miri_sysroot = &self.miri_sysroot;
                    handles.push(scope.spawn(move || {
                        let out = run_single_miri(
                            miri_bin,
                            miri_sysroot,
                            child_env,
                            &item.harness_path,
                            &item.bridge_rlib,
                            &item.corpus_dir,
                            &item.selector,
                            Some(item.token.as_str()),
                        );
                        (item.case_id.clone(), out)
                    }));
                }
                handles
                    .into_iter()
                    .map(|h| {
                        h.join().unwrap_or_else(|_| {
                            (
                                "<panicked>".to_owned(),
                                ObservedOutcome::ToolError {
                                    detail: "Miri worker thread panicked".to_owned(),
                                },
                            )
                        })
                    })
                    .collect::<Vec<_>>()
            });
            for (case_id, outcome) in outcomes {
                results.insert(case_id, outcome);
            }
        }

        Ok(results)
    }

    /// Execute a Stage-2 fuzz batch under Miri (`-Zmiri-tree-borrows`) using
    /// batched execution for expected-clean cases with automatic recursive
    /// bisection down to isolated single-case runs on any UB/panic/error, and
    /// isolated parallel worker runs for expected-UB/scope cases.
    pub fn run_fuzz_batch(
        &self,
        source_text: &str,
        cases: &[crate::rustc_runner::FuzzExecCase],
    ) -> Result<BTreeMap<String, ObservedOutcome>, String> {
        self.run_fuzz_batch_until(source_text, cases, None)
    }

    /// Deadline-clamped variant of [`Self::run_fuzz_batch`] used by the
    /// shrinker so stalled candidates cannot run past `max_duration_secs`.
    pub fn run_fuzz_batch_until(
        &self,
        source_text: &str,
        cases: &[crate::rustc_runner::FuzzExecCase],
        deadline: Option<Instant>,
    ) -> Result<BTreeMap<String, ObservedOutcome>, String> {
        let with_ev = self.run_fuzz_batch_with_evidence_until(source_text, cases, deadline)?;
        Ok(with_ev.into_iter().map(|(id, (outcome, _ev))| (id, outcome)).collect())
    }

    /// Deadline-clamped execution returning `(outcome, case_bound_evidence)`
    /// for every case in `cases`.
    pub fn run_fuzz_batch_with_evidence_until(
        &self,
        source_text: &str,
        cases: &[FuzzExecCase],
        deadline: Option<Instant>,
    ) -> Result<BTreeMap<String, (ObservedOutcome, Option<String>)>, String> {
        self.run_fuzz_crate_with_evidence_impl(source_text, None, cases, deadline)
    }

    /// Program-aware deadline-clamped execution preserving single-crate Miri
    /// batching on the happy path while isolating ordinary compiler diagnostics
    /// (`error[E...]`, syntax errors) via subset-specific harnesses.
    pub fn run_fuzz_crate_with_evidence_until(
        &self,
        source_text: &str,
        programs: &[&GenProgram],
        cases: &[FuzzExecCase],
        deadline: Option<Instant>,
    ) -> Result<BTreeMap<String, (ObservedOutcome, Option<String>)>, String> {
        if programs.len() != cases.len() {
            return Err(format!(
                "Miri crate program count ({}) does not match case count ({})",
                programs.len(),
                cases.len()
            ));
        }
        let pairs: Vec<(&GenProgram, &FuzzExecCase)> =
            programs.iter().copied().zip(cases.iter()).collect();
        for (prog, case) in &pairs {
            if prog.case_id != case.case_id {
                return Err(format!(
                    "Miri crate program `{}` does not match case `{}`",
                    prog.case_id, case.case_id
                ));
            }
        }
        self.run_fuzz_crate_with_evidence_impl(source_text, Some(&pairs), cases, deadline)
    }

    fn run_fuzz_crate_with_evidence_impl(
        &self,
        source_text: &str,
        programs: Option<&[(&GenProgram, &FuzzExecCase)]>,
        cases: &[FuzzExecCase],
        deadline: Option<Instant>,
    ) -> Result<BTreeMap<String, (ObservedOutcome, Option<String>)>, String> {
        if cases.is_empty() {
            return Ok(BTreeMap::new());
        }
        let ld_path = &self.ld_library_path;
        let path_env =
            build_child_path(&self.rust_sysroot.join("bin"), env::var_os("PATH").as_deref())?;
        let (rustc_bin, _rustc_staging) = self.resolve_miri_rustc_bin()?;
        let work_root = crate::mir_eval_runner::build_temp_dir(
            "anneal-miri-fuzz-",
            self.validated_tmpdir.as_deref(),
        )?;
        let child_env =
            MiriChildEnv { ld_path, path_env: &path_env, tmpdir: self.validated_tmpdir.as_deref() };
        let bundle = match build_isolated_miri_fuzz_group(
            work_root.path(),
            "fuzz",
            source_text,
            cases,
            &rustc_bin,
            &self.miri_sysroot,
            child_env,
            deadline,
        ) {
            Ok(b) => b,
            Err(MiriBatchFailure::Global(detail)) => {
                return Ok(cases
                    .iter()
                    .map(|c| {
                        (
                            c.case_id.clone(),
                            (ObservedOutcome::ToolError { detail: detail.clone() }, None),
                        )
                    })
                    .collect());
            }
            Err(MiriBatchFailure::CompileDiagnostic(detail)) => {
                if let Some(items) = programs
                    && items.len() > 1
                {
                    let mid = items.len() / 2;
                    let mut combined = run_miri_compile_bisect_slice(
                        &self.miri_bin,
                        &rustc_bin,
                        &self.miri_sysroot,
                        child_env,
                        &items[..mid],
                        deadline,
                    );
                    combined.extend(run_miri_compile_bisect_slice(
                        &self.miri_bin,
                        &rustc_bin,
                        &self.miri_sysroot,
                        child_env,
                        &items[mid..],
                        deadline,
                    ));
                    return Ok(combined);
                }
                return Ok(cases
                    .iter()
                    .map(|c| {
                        (
                            c.case_id.clone(),
                            (ObservedOutcome::ToolError { detail: detail.clone() }, None),
                        )
                    })
                    .collect());
            }
        };

        let mut results = BTreeMap::new();

        let clean_pairs: Vec<(String, String)> = cases
            .iter()
            .filter(|c| c.expected_clean_batch)
            .map(|c| (c.case_id.clone(), c.fn_name.clone()))
            .collect();
        let clean_progs: Vec<(&GenProgram, &FuzzExecCase)> = programs
            .map(|ps| ps.iter().copied().filter(|(_, c)| c.expected_clean_batch).collect())
            .unwrap_or_default();
        let isolated_pairs: Vec<(String, String)> = cases
            .iter()
            .filter(|c| !c.expected_clean_batch)
            .map(|c| (c.case_id.clone(), c.fn_name.clone()))
            .collect();
        let isolated_progs: Vec<(&GenProgram, &FuzzExecCase)> = programs
            .map(|ps| ps.iter().copied().filter(|(_, c)| !c.expected_clean_batch).collect())
            .unwrap_or_default();

        // Execute clean chunks in parallel (up to 4 chunks at once), bisecting
        // any chunk that faults so verdict accuracy matches per-case execution.
        let workers = thread::available_parallelism().map(|n| n.get().clamp(1, 4)).unwrap_or(1);
        let chunks: Vec<&[(String, String)]> = clean_pairs.chunks(MIRI_BATCH_CHUNK_SIZE).collect();
        let prog_chunks: Vec<&[(&GenProgram, &FuzzExecCase)]> = if programs.is_some() {
            clean_progs.chunks(MIRI_BATCH_CHUNK_SIZE).collect()
        } else {
            Vec::new()
        };
        for (group_idx, group) in chunks.chunks(workers).enumerate() {
            let group_base = group_idx * workers;
            let group_maps = thread::scope(|scope| {
                let mut handles = Vec::with_capacity(group.len());
                for (local_idx, chunk) in group.iter().enumerate() {
                    let miri_bin = &self.miri_bin;
                    let rustc_bin = &rustc_bin;
                    let miri_sysroot = &self.miri_sysroot;
                    let harness_path = &bundle.harness_path;
                    let bridge_rlib = &bundle.bridge_rlib;
                    let corpus_dir = &bundle.corpus_dir;
                    let expected_token = bundle.token.as_str();
                    let chunk_progs = prog_chunks.get(group_base + local_idx).copied();
                    handles.push(scope.spawn(move || {
                        run_miri_chunk_with_bisection(
                            miri_bin,
                            Some(rustc_bin.as_path()),
                            miri_sysroot,
                            child_env,
                            harness_path,
                            Some((bridge_rlib.as_path(), corpus_dir.as_path())),
                            chunk,
                            chunk_progs,
                            false,
                            Some(expected_token),
                            deadline,
                        )
                    }));
                }
                handles.into_iter().map(|h| h.join().unwrap_or_default()).collect::<Vec<_>>()
            });
            for m in group_maps {
                results.extend(m);
            }
        }

        // Execute isolated UB / scope-control cases directly in parallel,
        // falling back to a standalone harness if another batch-mate failed to
        // compile in the shared crate.
        for (group_idx, chunk) in isolated_pairs.chunks(workers).enumerate() {
            let group_base = group_idx * workers;
            let outcomes = thread::scope(|scope| {
                let mut handles = Vec::with_capacity(chunk.len());
                for (local_idx, (case_id, fn_name)) in chunk.iter().enumerate() {
                    let miri_bin = &self.miri_bin;
                    let rustc_bin = &rustc_bin;
                    let miri_sysroot = &self.miri_sysroot;
                    let harness_path = &bundle.harness_path;
                    let bridge_rlib = &bundle.bridge_rlib;
                    let corpus_dir = &bundle.corpus_dir;
                    let expected_token = bundle.token.as_str();
                    let iso_prog =
                        programs.and_then(|_| isolated_progs.get(group_base + local_idx).copied());
                    handles.push(scope.spawn(move || {
                        let out = run_single_miri_fuzz_with_fallback(
                            miri_bin,
                            Some(rustc_bin.as_path()),
                            miri_sysroot,
                            child_env,
                            harness_path,
                            Some((bridge_rlib.as_path(), corpus_dir.as_path())),
                            (case_id, fn_name),
                            iso_prog,
                            Some(expected_token),
                            deadline,
                        );
                        (case_id.clone(), out)
                    }));
                }
                handles
                    .into_iter()
                    .map(|h| {
                        h.join().unwrap_or_else(|_| {
                            (
                                "<panicked>".to_owned(),
                                (
                                    ObservedOutcome::ToolError {
                                        detail: "Miri fuzz worker thread panicked".to_owned(),
                                    },
                                    None,
                                ),
                            )
                        })
                    })
                    .collect::<Vec<_>>()
            });
            for (id, outcome) in outcomes {
                results.insert(id, outcome);
            }
        }

        Ok(results)
    }
}

#[derive(Serialize)]
struct ScratchCargoConfig {
    source: ScratchCargoSources,
}

#[derive(Serialize)]
struct ScratchCargoSources {
    #[serde(rename = "crates-io")]
    crates_io: ScratchCratesIoReplace,
    #[serde(rename = "vendored-sources")]
    vendored_sources: ScratchVendorDir,
}

#[derive(Serialize)]
struct ScratchCratesIoReplace {
    #[serde(rename = "replace-with")]
    replace_with: &'static str,
}

#[derive(Serialize)]
struct ScratchVendorDir {
    directory: String,
}

fn render_vendored_cargo_config(vendor_dir: &Path) -> Result<String, String> {
    let cfg = ScratchCargoConfig {
        source: ScratchCargoSources {
            crates_io: ScratchCratesIoReplace { replace_with: "vendored-sources" },
            vendored_sources: ScratchVendorDir {
                directory: vendor_dir.to_string_lossy().into_owned(),
            },
        },
    };
    toml::to_string(&cfg).map_err(|e| format!("serialize offline Miri Cargo config: {e}"))
}

fn build_child_path(primary_bin: &Path, ambient_path: Option<&OsStr>) -> Result<OsString, String> {
    let caller_cwd =
        env::current_dir().map_err(|e| format!("resolve current working directory: {e}"))?;
    let store_prefix = Path::new(STORE_PREFIX);
    let trusted_dirs: Vec<&Path> = TRUSTED_CHILD_PATH_DIRS.iter().map(Path::new).collect();
    build_child_path_with_bins(
        &[primary_bin],
        None,
        store_prefix,
        &trusted_dirs,
        ambient_path,
        &caller_cwd,
    )
}

fn parse_rustc_version_tag(rustc: &Path, text: &str) -> Result<String, String> {
    let commit = text
        .lines()
        .find_map(|line| line.strip_prefix("commit-hash: "))
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .ok_or_else(|| format!("`{} -vV` output missing `commit-hash:` line", rustc.display()))?;
    let short: String = commit.chars().take(12).collect();
    let host = text
        .lines()
        .find_map(|line| line.strip_prefix("host: "))
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .ok_or_else(|| format!("`{} -vV` output missing `host:` line", rustc.display()))?;
    let rustc_sha = sha256_file_hex(rustc)?;
    Ok(format!("{short}-{host}-{}", &rustc_sha[..12]))
}

const MIRI_SYSROOT_STAMP_VERSION: u32 = 3;

#[derive(Debug, Deserialize, Serialize)]
struct MiriSysrootStamp {
    version: u32,
    ver_tag: String,
    setup_sha: String,
    files: BTreeMap<String, String>,
}

fn expected_miri_ready_stamp_json(
    ver_tag: &str,
    setup_sha: &str,
    files: BTreeMap<String, String>,
) -> Result<String, String> {
    let mut payload = serde_json::to_string_pretty(&MiriSysrootStamp {
        version: MIRI_SYSROOT_STAMP_VERSION,
        ver_tag: ver_tag.to_owned(),
        setup_sha: setup_sha.to_owned(),
        files,
    })
    .map_err(|e| format!("serialize Miri ready stamp: {e}"))?;
    payload.push('\n');
    Ok(payload)
}

#[cfg(test)]
fn expected_miri_ready_stamp_for_dir(
    miri_sysroot: &Path,
    ver_tag: &str,
    setup_sha: &str,
) -> String {
    let rustlib = miri_sysroot.join("lib/rustlib");
    let files = collect_rel_file_sha256s_nofollow(&rustlib, None, "test Miri lib/rustlib")
        .unwrap_or_default();
    expected_miri_ready_stamp_json(ver_tag, setup_sha, files).unwrap()
}

fn stage_miri_sysroot_dir_in(
    raw_dir: &Path,
    caller_cwd: &Path,
    store_prefix: &Path,
    tmp_parent: Option<&Path>,
    label: &str,
) -> Result<(PathBuf, Option<Arc<ImmutableStagingDir>>), String> {
    if raw_dir.components().any(|c| matches!(c, Component::ParentDir)) {
        return Err(format!(
            "{label} must not contain `..` path traversal segments: {}",
            raw_dir.display()
        ));
    }
    let abs_dir =
        if raw_dir.is_absolute() { raw_dir.to_path_buf() } else { caller_cwd.join(raw_dir) };

    if let Some(res) =
        try_validate_store_contained_path(&abs_dir, store_prefix, caller_cwd, true, label)
    {
        let canon_sysroot = res?;
        let canon_store =
            crate::mir_eval_runner::validate_dir_path_no_symlinks(store_prefix, caller_cwd)?;
        let rustlib_dir = canon_sysroot.join("lib/rustlib");
        if fs::symlink_metadata(canon_sysroot.join("lib")).is_err()
            || fs::symlink_metadata(&rustlib_dir).is_err()
        {
            return Err(format!("{label}={} does not contain `lib/rustlib`", raw_dir.display()));
        }
        let canon_rustlib = validate_store_contained_entry(
            &rustlib_dir,
            &canon_store,
            &canon_store,
            true,
            &format!("{label} lib/rustlib"),
        )?;
        validate_store_contained_dir_tree(
            &canon_rustlib,
            &canon_store,
            &canon_store,
            &format!("{label} lib/rustlib"),
        )?;
        let stamp_path = canon_sysroot.join(".anneal-miri-ready");
        let _ = validate_store_contained_entry(
            &stamp_path,
            &canon_store,
            &canon_store,
            false,
            &format!("{label} .anneal-miri-ready"),
        )
        .map_err(|e| {
            format!(
                "{label}={} lacks verifiable `.anneal-miri-ready` setup stamp ({e})",
                raw_dir.display()
            )
        })?;
        return Ok((canon_sysroot, None));
    }

    let canon_sysroot = crate::mir_eval_runner::validate_dir_path_no_symlinks(&abs_dir, caller_cwd)
        .map_err(|e| format!("{label}={} must not be a symlink: {e}", raw_dir.display()))?;
    let lib_dir = canon_sysroot.join("lib");
    let rustlib_dir = lib_dir.join("rustlib");
    if fs::symlink_metadata(&lib_dir).is_err() || fs::symlink_metadata(&rustlib_dir).is_err() {
        return Err(format!("{label}={} does not contain `lib/rustlib`", raw_dir.display()));
    }
    let canon_rustlib =
        crate::mir_eval_runner::validate_dir_path_no_symlinks(&rustlib_dir, &canon_sysroot)
            .map_err(|e| format!("{label}={} invalid `lib/rustlib`: {e}", raw_dir.display()))?;

    let stamp_src = canon_sysroot.join(".anneal-miri-ready");
    if let Err(e) = fs::symlink_metadata(&stamp_src) {
        return Err(format!(
            "{label}={} lacks verifiable `.anneal-miri-ready` setup stamp ({e})",
            raw_dir.display()
        ));
    }

    let temp = crate::mir_eval_runner::build_temp_dir("anneal-miri-sys-", tmp_parent)?;
    let (_, staging) = ImmutableStagingDir::build_and_pin(temp, label, |_, pinned_root| {
        copy_verified_regular_file(
            &stamp_src,
            &pinned_root.join(".anneal-miri-ready"),
            false,
            &format!("{label} .anneal-miri-ready"),
        )?;
        copy_validated_subtree(
            &canon_rustlib,
            &pinned_root.join("lib/rustlib"),
            None,
            false,
            &format!("{label} lib/rustlib"),
        )
    })?;
    Ok((staging.root().to_path_buf(), Some(staging)))
}

fn collect_store_rel_file_sha256s(
    root_dir: &Path,
    store_prefix: &Path,
    canon_store: &Path,
    label: &str,
) -> Result<BTreeMap<String, String>, String> {
    validate_store_contained_dir_tree(root_dir, store_prefix, canon_store, label)?;
    let mut files = BTreeMap::new();
    let mut visited = BTreeSet::new();
    let mut stack = vec![(root_dir.to_path_buf(), PathBuf::new())];
    visited.insert(root_dir.to_path_buf());
    while let Some((cur_dir, rel_prefix)) = stack.pop() {
        let mut entries: Vec<_> = fs::read_dir(&cur_dir)
            .map_err(|e| format!("read {label} dir {}: {e}", cur_dir.display()))?
            .collect::<Result<Vec<_>, _>>()
            .map_err(|e| format!("iterate {label} dir {}: {e}", cur_dir.display()))?;
        entries.sort_by_key(|e| e.file_name());
        for entry in entries {
            let path = entry.path();
            let next_rel = rel_prefix.join(entry.file_name());
            let meta = fs::symlink_metadata(&path)
                .map_err(|e| format!("stat {label} {}: {e}", path.display()))?;
            let target = if meta.file_type().is_symlink() {
                let canon_target = fs::canonicalize(&path)
                    .map_err(|e| format!("canonicalize {label} {}: {e}", path.display()))?;
                let cmeta = fs::symlink_metadata(&canon_target)
                    .map_err(|e| format!("stat {label} {}: {e}", canon_target.display()))?;
                validate_store_contained_entry(
                    &path,
                    store_prefix,
                    canon_store,
                    cmeta.is_dir(),
                    label,
                )?
            } else {
                path
            };
            let tmeta = fs::symlink_metadata(&target)
                .map_err(|e| format!("stat {label} {}: {e}", target.display()))?;
            if tmeta.is_dir() {
                if visited.insert(target.clone()) {
                    stack.push((target, next_rel));
                }
            } else if tmeta.is_file() {
                let mut segs = Vec::new();
                for comp in next_rel.components() {
                    let Component::Normal(os) = comp else {
                        return Err(format!("invalid relative component in {label}"));
                    };
                    segs.push(os.to_str().ok_or_else(|| {
                        format!("non-UTF-8 path in {label}: {}", next_rel.display())
                    })?);
                }
                files.insert(segs.join("/"), sha256_file_hex(&target)?);
            }
        }
    }
    Ok(files)
}

fn verify_miri_sysroot_stamp_with_store(
    miri_sysroot: &Path,
    staging: Option<&ImmutableStagingDir>,
    store_prefix: &Path,
    ver_tag: &str,
    setup_sha: &str,
) -> Result<(), String> {
    let mut stamp_file = if let Some(stage) = staging {
        stage
            .open_verified_rel_file(
                Path::new(".anneal-miri-ready"),
                "ANNEAL_MIRI_SYSROOT .anneal-miri-ready",
            )
            .map_err(|e| {
                format!(
                    "ANNEAL_MIRI_SYSROOT={} lacks verifiable `.anneal-miri-ready` setup stamp ({e})",
                    miri_sysroot.display()
                )
            })?
    } else {
        let ready_stamp = miri_sysroot.join(".anneal-miri-ready");
        let canon_stamp = if let Some(res) = try_validate_store_contained_path(
            &ready_stamp,
            store_prefix,
            miri_sysroot,
            false,
            "ANNEAL_MIRI_SYSROOT .anneal-miri-ready",
        ) {
            res
        } else {
            crate::mir_eval_runner::validate_executable_no_links(
                &ready_stamp,
                miri_sysroot,
                "ANNEAL_MIRI_SYSROOT .anneal-miri-ready",
            )
        }
        .map_err(|e| {
            format!(
                "ANNEAL_MIRI_SYSROOT={} lacks verifiable `.anneal-miri-ready` setup stamp ({e})",
                miri_sysroot.display()
            )
        })?;
        let f = File::open(&canon_stamp).map_err(|e| {
            format!("open ANNEAL_MIRI_SYSROOT stamp {}: {e}", canon_stamp.display())
        })?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt as _;

            let opened = f.metadata().map_err(|e| {
                format!("fstat ANNEAL_MIRI_SYSROOT stamp {}: {e}", canon_stamp.display())
            })?;
            if !opened.is_file() || opened.nlink() > 1 {
                return Err(format!(
                    "ANNEAL_MIRI_SYSROOT={} `.anneal-miri-ready` must not be a hardlink (nlink={})",
                    miri_sysroot.display(),
                    opened.nlink()
                ));
            }
        }
        f
    };

    let mut raw = String::new();
    std::io::Read::read_to_string(&mut stamp_file, &mut raw).map_err(|e| {
        format!("read ANNEAL_MIRI_SYSROOT stamp in {}: {e}", miri_sysroot.display())
    })?;
    let stamp: MiriSysrootStamp = serde_json::from_str(&raw).map_err(|_| {
        format!(
            "ANNEAL_MIRI_SYSROOT={} setup stamp does not match current Miri/rust-src inputs",
            miri_sysroot.display()
        )
    })?;
    if stamp.version != MIRI_SYSROOT_STAMP_VERSION
        || stamp.ver_tag != ver_tag
        || stamp.setup_sha != setup_sha
    {
        return Err(format!(
            "ANNEAL_MIRI_SYSROOT={} setup stamp does not match current Miri/rust-src inputs",
            miri_sysroot.display()
        ));
    }

    let disk_files = if let Some(stage) = staging {
        stage.collect_rel_file_sha256s(
            Some(Path::new("lib/rustlib")),
            None,
            "staged Miri lib/rustlib",
        )?
    } else {
        let rustlib = miri_sysroot.join("lib/rustlib");
        if miri_sysroot.starts_with(store_prefix) && fs::symlink_metadata(store_prefix).is_ok() {
            let canon_store =
                crate::mir_eval_runner::validate_dir_path_no_symlinks(store_prefix, miri_sysroot)?;
            collect_store_rel_file_sha256s(
                &rustlib,
                store_prefix,
                &canon_store,
                "store Miri lib/rustlib",
            )?
        } else {
            collect_rel_file_sha256s_nofollow(&rustlib, None, "Miri lib/rustlib")?
        }
    };

    if disk_files.len() != stamp.files.len() {
        return Err(format!(
            "ANNEAL_MIRI_SYSROOT={} lib/rustlib file set does not match `.anneal-miri-ready` manifest",
            miri_sysroot.display()
        ));
    }
    for (rel, expected_sha) in &stamp.files {
        let Some(actual_sha) = disk_files.get(rel) else {
            return Err(format!(
                "ANNEAL_MIRI_SYSROOT={} missing lib/rustlib artifact listed in `.anneal-miri-ready`: {rel}",
                miri_sysroot.display()
            ));
        };
        if !actual_sha.eq_ignore_ascii_case(expected_sha) {
            return Err(format!(
                "ANNEAL_MIRI_SYSROOT={} lib/rustlib artifact `{rel}` failed SHA-256 verification against `.anneal-miri-ready`",
                miri_sysroot.display()
            ));
        }
    }
    Ok(())
}

#[cfg(test)]
fn verify_explicit_miri_sysroot_stamp(
    miri_sysroot: &Path,
    ver_tag: &str,
    setup_sha: &str,
) -> Result<(), String> {
    verify_miri_sysroot_stamp_with_store(
        miri_sysroot,
        None,
        Path::new(STORE_PREFIX),
        ver_tag,
        setup_sha,
    )
}

#[cfg(test)]
fn stage_and_verify_miri_sysroot(
    raw_dir: &Path,
    caller_cwd: &Path,
    store_prefix: &Path,
    ver_tag: &str,
    setup_sha: &str,
    label: &str,
) -> Result<(PathBuf, Option<Arc<ImmutableStagingDir>>), String> {
    stage_and_verify_miri_sysroot_in(
        raw_dir,
        caller_cwd,
        store_prefix,
        None,
        ver_tag,
        setup_sha,
        label,
    )
}

fn stage_and_verify_miri_sysroot_in(
    raw_dir: &Path,
    caller_cwd: &Path,
    store_prefix: &Path,
    tmp_parent: Option<&Path>,
    ver_tag: &str,
    setup_sha: &str,
    label: &str,
) -> Result<(PathBuf, Option<Arc<ImmutableStagingDir>>), String> {
    let (miri_sysroot, miri_staging) =
        stage_miri_sysroot_dir_in(raw_dir, caller_cwd, store_prefix, tmp_parent, label)?;
    verify_miri_sysroot_stamp_with_store(
        &miri_sysroot,
        miri_staging.as_deref(),
        store_prefix,
        ver_tag,
        setup_sha,
    )?;
    Ok((miri_sysroot, miri_staging))
}

#[cfg(test)]
fn stage_and_verify_miri_sysroot_from_pinned(
    pinned: &PinnedPrivateDir,
    rel_dir: &Path,
    store_prefix: &Path,
    ver_tag: &str,
    setup_sha: &str,
    label: &str,
) -> Result<(PathBuf, Option<Arc<ImmutableStagingDir>>), String> {
    stage_and_verify_miri_sysroot_from_pinned_in(
        pinned,
        rel_dir,
        store_prefix,
        None,
        ver_tag,
        setup_sha,
        label,
    )
}

fn stage_and_verify_miri_sysroot_from_pinned_in(
    pinned: &PinnedPrivateDir,
    rel_dir: &Path,
    store_prefix: &Path,
    tmp_parent: Option<&Path>,
    ver_tag: &str,
    setup_sha: &str,
    label: &str,
) -> Result<(PathBuf, Option<Arc<ImmutableStagingDir>>), String> {
    if !pinned.has_rel_dir(&rel_dir.join("lib/rustlib"), &format!("{label} lib/rustlib")) {
        return Err(format!("{label}={} does not contain `lib/rustlib`", rel_dir.display()));
    }
    let mut stamp_file = pinned
        .open_verified_rel_file(
            &rel_dir.join(".anneal-miri-ready"),
            &format!("{label} .anneal-miri-ready"),
        )
        .map_err(|e| {
            format!(
                "{label}={} lacks verifiable `.anneal-miri-ready` setup stamp ({e})",
                rel_dir.display()
            )
        })?;
    let temp = crate::mir_eval_runner::build_temp_dir("anneal-miri-sys-", tmp_parent)?;
    let (_, miri_staging) = ImmutableStagingDir::build_and_pin(temp, label, |_, pinned_root| {
        copy_opened_file_to_new_dst(
            &mut stamp_file,
            false,
            &pinned_root.join(".anneal-miri-ready"),
            false,
            &format!("{label} .anneal-miri-ready"),
        )?;
        pinned.copy_rel_subtree_to(
            &rel_dir.join("lib/rustlib"),
            &pinned_root.join("lib/rustlib"),
            false,
            &format!("{label} lib/rustlib"),
        )
    })?;
    let priv_root = miri_staging.root().to_path_buf();
    verify_miri_sysroot_stamp_with_store(
        &priv_root,
        Some(&miri_staging),
        store_prefix,
        ver_tag,
        setup_sha,
    )?;
    Ok((priv_root, Some(miri_staging)))
}

/// Compute a full SHA-256 digest over all inputs participating in
/// `cargo miri setup` (`rustc`, `cargo`, `miri`, `cargo-miri`,
/// `PINNED_MIRI_TARGET`, and the entire `lib/rustlib/src/rust/library` tree
/// including `vendor/`) so cached Miri sysroots are invalidated whenever any
/// setup input changes.
#[cfg(test)]
fn compute_miri_setup_input_sha256(rust_sysroot: &Path, ver_tag: &str) -> Result<String, String> {
    compute_miri_setup_input_sha256_inner(rust_sysroot, ver_tag, None)
}

fn compute_miri_setup_input_sha256_inner(
    rust_sysroot: &Path,
    ver_tag: &str,
    staging: Option<&ImmutableStagingDir>,
) -> Result<String, String> {
    let mut bin_shas = Vec::with_capacity(4);
    for rel_bin in ["bin/rustc", "bin/cargo", "bin/miri", "bin/cargo-miri"] {
        let sha = if let Some(stage) = staging {
            let mut f = stage.open_verified_rel_file(Path::new(rel_bin), rel_bin)?;
            sha256_opened_file_hex(&mut f, rel_bin)?
        } else {
            let prepared =
                prepare_sysroot_binary(rust_sysroot, rel_bin, Path::new(STORE_PREFIX), rel_bin)?;
            sha256_file_hex(&prepared.binary)?
        };
        bin_shas.push((rel_bin, sha));
    }

    let library_sha = if let Some(stage) = staging {
        let vendor_rel = Path::new("lib/rustlib/src/rust/library/vendor");
        if !stage.has_rel_dir(vendor_rel, "rust-src vendor") {
            return Err(format!(
                "pinned rust_sysroot lacks vendored `rust-src` crates at {}",
                rust_sysroot.join(vendor_rel).display()
            ));
        }
        let lib_rel = Path::new("lib/rustlib/src/rust/library");
        let entries = stage.collect_rel_file_sha256s(Some(lib_rel), None, "rust-src library")?;
        format_rel_file_manifest_sha256(&entries)
    } else {
        let library_dir = rust_sysroot.join("lib/rustlib/src/rust/library");
        let vendor_dir = library_dir.join("vendor");
        if !vendor_dir.is_dir() {
            return Err(format!(
                "pinned rust_sysroot lacks vendored `rust-src` crates at {}",
                vendor_dir.display()
            ));
        }
        let canon_library = fs::canonicalize(&library_dir)
            .map_err(|e| format!("canonicalize rust-src library {}: {e}", library_dir.display()))?;
        hash_directory_tree_contents(&canon_library)?
    };

    let mut h = Sha256::new();
    h.update(b"anneal-miri-setup-inputs-v2\0");
    h.update(PINNED_MIRI_TARGET.as_bytes());
    h.update(b"\0");
    h.update(ver_tag.as_bytes());
    h.update(b"\0");
    for (name, sha) in &bin_shas {
        h.update(name.as_bytes());
        h.update(b":");
        h.update(sha.as_bytes());
        h.update(b"\n");
    }
    h.update(b"rust-src-library:");
    h.update(library_sha.as_bytes());
    h.update(b"\n");
    let digest = h.finalize();
    let mut hex = String::with_capacity(64);
    for b in digest {
        use std::fmt::Write as _;
        let _ = write!(hex, "{b:02x}");
    }
    Ok(hex)
}

fn format_rel_file_manifest_sha256(entries: &BTreeMap<String, String>) -> String {
    let mut manifest = String::new();
    for (rel, sha) in entries {
        manifest.push_str(rel);
        manifest.push(':');
        manifest.push_str(sha);
        manifest.push('\n');
    }
    sha256_bytes_hex(manifest.as_bytes())
}

fn hash_directory_tree_contents(root_dir: &Path) -> Result<String, String> {
    let store_prefix = Path::new(STORE_PREFIX);
    let entries =
        if root_dir.starts_with(store_prefix) && fs::symlink_metadata(store_prefix).is_ok() {
            let canon_store =
                crate::mir_eval_runner::validate_dir_path_no_symlinks(store_prefix, root_dir)?;
            collect_store_rel_file_sha256s(
                root_dir,
                store_prefix,
                &canon_store,
                "store rust-src library",
            )?
        } else {
            collect_rel_file_sha256s_nofollow(root_dir, None, "rust-src library")?
        };
    Ok(format_rel_file_manifest_sha256(&entries))
}

fn rustc_version_tag(
    rust_sysroot: &Path,
    ld_library_path: &str,
    ambient_path: Option<&OsStr>,
    validated_tmpdir: Option<&Path>,
    work_dir: &Path,
) -> Result<String, String> {
    let rustc = rust_sysroot.join("bin/rustc");
    let path_env = build_child_path(&rust_sysroot.join("bin"), ambient_path)?;
    let mut inv = Invocation::new(&rustc, &["-vV"])
        .env("LD_LIBRARY_PATH", ld_library_path)
        .env("PATH", path_env);
    if let Some(td) = validated_tmpdir {
        inv = inv.env("TMPDIR", td);
    }
    let probe_timeout = effective_timeout_secs(RUSTC_PROBE_TIMEOUT_SECS)?;
    let out = run_supervised_in_tmp(
        &inv,
        work_dir,
        Duration::from_secs(probe_timeout),
        validated_tmpdir,
        "rustc -vV",
    )?;
    match out.termination {
        Termination::Exited(status) if status.success() => {}
        other => {
            return Err(format!(
                "`{} -vV` failed ({}): {}",
                rustc.display(),
                other.describe(),
                String::from_utf8_lossy(&out.stderr)
            ));
        }
    }
    let text = String::from_utf8_lossy(&out.stdout);
    parse_rustc_version_tag(&rustc, &text)
}

fn write_new_miri_ready_stamp(staging_dir: &Path, expected_stamp: &str) -> Result<(), String> {
    use std::io::Write as _;

    let stamp_path = staging_dir.join(".anneal-miri-ready");
    let mut opts = fs::OpenOptions::new();
    opts.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        opts.custom_flags(libc::O_NOFOLLOW);
    }
    let mut file = opts
        .open(&stamp_path)
        .map_err(|e| format!("create staged Miri ready stamp {}: {e}", stamp_path.display()))?;
    file.write_all(expected_stamp.as_bytes())
        .map_err(|e| format!("write staged Miri ready stamp {}: {e}", stamp_path.display()))?;
    file.flush()
        .map_err(|e| format!("flush staged Miri ready stamp {}: {e}", stamp_path.display()))?;
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn build_offline_miri_sysroot_in(
    cache: MiriCacheRoot<'_>,
    rust_sysroot: &Path,
    miri_bin: &Path,
    target_dir: &Path,
    ver_tag: &str,
    setup_sha: &str,
    ld_library_path: &str,
    ambient_path: Option<&OsStr>,
    validated_tmpdir: Option<&Path>,
    _work_dir: &Path,
) -> Result<(), String> {
    let rustc = rust_sysroot.join("bin/rustc");
    let cargo_bin = rust_sysroot.join("bin/cargo");
    if !cargo_bin.is_file() {
        return Err(format!("pinned sysroot lacks `bin/cargo`: {}", cargo_bin.display()));
    }

    let vendor_dir = rust_sysroot.join("lib/rustlib/src/rust/library/vendor");
    if !vendor_dir.is_dir() {
        return Err(format!(
            "pinned rust_sysroot lacks vendored `rust-src` crates at {}",
            vendor_dir.display()
        ));
    }

    let pinned_parent = match cache {
        MiriCacheRoot::Pinned(p) => Some(p.path()),
        MiriCacheRoot::Path(_) => None,
    };
    let parent = match &pinned_parent {
        Some(p) => p.as_path(),
        None => target_dir
            .parent()
            .ok_or_else(|| format!("target dir has no parent: {}", target_dir.display()))?,
    };
    let staging = tempfile::Builder::new()
        .prefix("miri-staging-")
        .tempdir_in(parent)
        .map_err(|e| format!("create Miri staging dir: {e}"))?;
    let scratch_cargo_home = if pinned_parent.is_some() {
        tempfile::Builder::new().prefix("miri-cargo-home-").tempdir_in(parent)
    } else {
        tempfile::Builder::new().prefix("miri-cargo-home-").tempdir()
    }
    .map_err(|e| format!("create offline Miri CARGO_HOME: {e}"))?;
    let scratch_home = if pinned_parent.is_some() {
        tempfile::Builder::new().prefix("miri-home-").tempdir_in(parent)
    } else {
        tempfile::Builder::new().prefix("miri-home-").tempdir()
    }
    .map_err(|e| format!("create offline Miri HOME: {e}"))?;
    let cargo_config = render_vendored_cargo_config(&vendor_dir)?;
    fs::write(scratch_cargo_home.path().join("config.toml"), cargo_config)
        .map_err(|e| format!("write offline Miri Cargo config.toml: {e}"))?;

    let joined_path = build_child_path(&rust_sysroot.join("bin"), ambient_path)?;
    let scratch_tmp = scratch_home.path().join("tmp");
    fs::create_dir_all(&scratch_tmp).map_err(|e| format!("create Miri scratch tmp: {e}"))?;

    let inv = Invocation::new(&cargo_bin, &["miri", "setup", "--target", PINNED_MIRI_TARGET])
        .env("PATH", joined_path)
        .env("HOME", scratch_home.path())
        .env("CARGO_HOME", scratch_cargo_home.path())
        .env("TMPDIR", &scratch_tmp)
        .env("RUSTC", &rustc)
        .env("MIRI", miri_bin)
        .env("MIRI_SYSROOT", staging.path())
        .env("CARGO_NET_OFFLINE", "true")
        .env("LD_LIBRARY_PATH", ld_library_path);

    let setup_timeout = effective_timeout_secs(MIRI_SETUP_TIMEOUT_SECS)?;
    let out = run_supervised_in_tmp(
        &inv,
        scratch_home.path(),
        Duration::from_secs(setup_timeout),
        validated_tmpdir,
        "miri setup",
    )?;
    match out.termination {
        Termination::Exited(status) if status.success() => {}
        other => {
            return Err(format!(
                "`cargo miri setup` failed ({}):\nstdout:\n{}\nstderr:\n{}",
                other.describe(),
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            ));
        }
    }

    let built_files = match cache {
        MiriCacheRoot::Pinned(p) => {
            let stage_name = staging.path().file_name().ok_or_else(|| {
                format!("Miri staging dir has no file name: {}", staging.path().display())
            })?;
            p.collect_rel_file_sha256s(
                Some(&Path::new(stage_name).join("lib/rustlib")),
                None,
                "built Miri lib/rustlib",
            )?
        }
        MiriCacheRoot::Path(_) => {
            let built_rustlib = staging.path().join("lib/rustlib");
            collect_rel_file_sha256s_nofollow(&built_rustlib, None, "built Miri lib/rustlib")?
        }
    };
    let expected_stamp = expected_miri_ready_stamp_json(ver_tag, setup_sha, built_files)?;
    write_new_miri_ready_stamp(staging.path(), &expected_stamp)?;

    match fs::symlink_metadata(target_dir) {
        Ok(meta) if meta.is_dir() => {
            fs::remove_dir_all(target_dir)
                .map_err(|e| format!("clean stale {}: {e}", target_dir.display()))?;
        }
        Ok(_) => {
            fs::remove_file(target_dir)
                .map_err(|e| format!("clean stale {}: {e}", target_dir.display()))?;
        }
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {}
        Err(e) => {
            return Err(format!("stat target Miri cache dir {}: {e}", target_dir.display()));
        }
    }
    let staged_path = staging.keep();
    fs::rename(&staged_path, target_dir).map_err(|e| {
        let _ = fs::remove_dir_all(&staged_path);
        format!("promote Miri sysroot {} -> {}: {e}", staged_path.display(), target_dir.display())
    })?;
    Ok(())
}

fn fresh_miri_marker_token(disallowed_haystack: &str) -> String {
    loop {
        let nanos = SystemTime::now().duration_since(UNIX_EPOCH).map(|d| d.as_nanos()).unwrap_or(0);
        let seq = MIRI_MARKER_SEQ.fetch_add(1, Ordering::Relaxed);
        let mut h = Sha256::new();
        h.update(b"anneal-miri-marker-v2\0");
        h.update(nanos.to_le_bytes());
        h.update(std::process::id().to_le_bytes());
        h.update(seq.to_le_bytes());
        h.update((disallowed_haystack.len() as u64).to_le_bytes());
        let mut rs = RandomState::new().build_hasher();
        rs.write_u64(seq);
        h.update(rs.finish().to_le_bytes());
        if let Ok(mut urand) = File::open("/dev/urandom") {
            let mut buf = [0u8; 16];
            if urand.read_exact(&mut buf).is_ok() {
                h.update(buf);
            }
        }
        let digest = h.finalize();
        let mut tok = String::with_capacity(32);
        for b in &digest[..16] {
            let _ = write!(tok, "{b:02x}");
        }
        if !disallowed_haystack.contains(&tok) {
            return tok;
        }
    }
}

fn validate_rust_ident(ident: &str, label: &str) -> Result<(), String> {
    let mut bytes = ident.bytes();
    let Some(first) = bytes.next() else {
        return Err(format!("empty {label}"));
    };
    if !(first.is_ascii_alphabetic() || first == b'_')
        || !bytes.all(|b| b.is_ascii_alphanumeric() || b == b'_')
    {
        return Err(format!("invalid {label} `{ident}`"));
    }
    Ok(())
}

fn validate_rust_fn_path(path: &str) -> Result<(), String> {
    if path.is_empty()
        || path.split("::").any(|seg| validate_rust_ident(seg, "fixture function segment").is_err())
    {
        return Err(format!("invalid fixture function path `{path}`"));
    }
    Ok(())
}

struct IsolatedMiriBundle {
    token: String,
    harness_path: PathBuf,
    bridge_rlib: PathBuf,
    corpus_dir: PathBuf,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum MiriBatchFailure {
    /// Genuine Miri/rustc/sysroot/timeout/launch failure affecting all cases.
    Global(String),
    /// Ordinary compilation diagnostic (e.g., `error[E0308]`, syntax error)
    /// that can be isolated cleanly using subset-specific crates/harnesses.
    CompileDiagnostic(String),
}

impl MiriBatchFailure {
    fn into_detail(self) -> String {
        match self {
            Self::Global(d) | Self::CompileDiagnostic(d) => d,
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn compile_miri_rlib_status(
    rustc_bin: &Path,
    miri_sysroot: &Path,
    child_env: MiriChildEnv<'_>,
    crate_name: &str,
    src_path: &Path,
    out_rlib: &Path,
    extra_extern: Option<(&str, &Path)>,
    extra_lib_dir: Option<&Path>,
    timeout: Duration,
) -> Result<(), MiriBatchFailure> {
    let mut inv = Invocation::new(rustc_bin, &["--edition=2024", "--target", PINNED_MIRI_TARGET])
        .arg("--sysroot")
        .arg(miri_sysroot)
        .arg("--cfg")
        .arg("miri")
        .arg("-Zalways-encode-mir")
        .arg("-C")
        .arg("opt-level=0")
        .arg("-C")
        .arg("debug-assertions=no")
        .arg("-C")
        .arg("overflow-checks=no")
        .arg("-A")
        .arg("dead_code")
        .arg("--crate-type=lib")
        .arg("--crate-name")
        .arg(crate_name);
    if let Some((dep_name, dep_rlib)) = extra_extern {
        inv = inv.arg("--extern").arg(format!("{dep_name}={}", dep_rlib.display()));
    }
    if let Some(lib_dir) = extra_lib_dir {
        inv = inv.arg("-L").arg(lib_dir);
    }
    inv = inv
        .arg("-o")
        .arg(out_rlib)
        .arg(src_path)
        .env("LD_LIBRARY_PATH", child_env.ld_path)
        .env("PATH", child_env.path_env);
    if let Some(td) = child_env.tmpdir {
        inv = inv.env("TMPDIR", td);
    }

    let work_dir = src_path.parent().unwrap_or_else(|| Path::new("/"));
    let out = run_supervised_in_tmp(&inv, work_dir, timeout, child_env.tmpdir, crate_name)
        .map_err(MiriBatchFailure::Global)?;
    match out.termination {
        Termination::Exited(status) if status.success() => Ok(()),
        other => {
            let stderr = String::from_utf8_lossy(&out.stderr);
            let snippet = stderr.lines().take(6).collect::<Vec<_>>().join(" | ");
            let msg = format!(
                "compile Miri `{crate_name}` crate failed ({}): {snippet}",
                other.describe()
            );
            if matches!(other, Termination::Exited(_)) && !is_miri_global_stderr(&stderr) {
                Err(MiriBatchFailure::CompileDiagnostic(msg))
            } else {
                Err(MiriBatchFailure::Global(msg))
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn compile_isolated_miri_crates(
    work_root: &Path,
    group_rel: &str,
    source_text: &str,
    bridge_code: String,
    render_harness: impl FnOnce(&str) -> Result<String, String>,
    rustc_bin: &Path,
    miri_sysroot: &Path,
    child_env: MiriChildEnv<'_>,
    deadline: Option<Instant>,
) -> Result<IsolatedMiriBundle, MiriBatchFailure> {
    let group_dir = work_root.join(group_rel);
    let corpus_dir = group_dir.join("c");
    let bridge_dir = group_dir.join("b");
    fs::create_dir_all(&corpus_dir).map_err(|e| {
        MiriBatchFailure::Global(format!("create Miri corpus dir {}: {e}", corpus_dir.display()))
    })?;
    fs::create_dir_all(&bridge_dir).map_err(|e| {
        MiriBatchFailure::Global(format!("create Miri bridge dir {}: {e}", bridge_dir.display()))
    })?;

    // Compile `corpus` and `bridge` into separate `.rlib` crates BEFORE
    // generating the secret token or writing `h/harness.rs`, keeping the
    // token strictly inside `h/harness.rs` source literals (never in paths,
    // symbols, args, or stack frame metadata).
    let corpus_src = corpus_dir.join("corpus.rs");
    fs::write(&corpus_src, source_text).map_err(|e| {
        MiriBatchFailure::Global(format!("write Miri corpus {}: {e}", corpus_src.display()))
    })?;
    let corpus_rlib = corpus_dir.join("libcorpus.rlib");
    let corpus_timeout = effective_timeout_duration(MIRI_SETUP_TIMEOUT_SECS, deadline)
        .map_err(MiriBatchFailure::Global)?;
    compile_miri_rlib_status(
        rustc_bin,
        miri_sysroot,
        child_env,
        "corpus",
        &corpus_src,
        &corpus_rlib,
        None,
        None,
        corpus_timeout,
    )?;

    let bridge_src = bridge_dir.join("bridge.rs");
    fs::write(&bridge_src, &bridge_code).map_err(|e| {
        MiriBatchFailure::Global(format!("write Miri bridge {}: {e}", bridge_src.display()))
    })?;
    let bridge_rlib = bridge_dir.join("libbridge.rlib");
    let bridge_timeout = effective_timeout_duration(MIRI_SETUP_TIMEOUT_SECS, deadline)
        .map_err(MiriBatchFailure::Global)?;
    compile_miri_rlib_status(
        rustc_bin,
        miri_sysroot,
        child_env,
        "bridge",
        &bridge_src,
        &bridge_rlib,
        Some(("corpus", &corpus_rlib)),
        Some(&corpus_dir),
        bridge_timeout,
    )?;

    let mut disallowed = String::with_capacity(source_text.len() + bridge_code.len() + 1);
    disallowed.push_str(source_text);
    disallowed.push('\n');
    disallowed.push_str(&bridge_code);
    let token = fresh_miri_marker_token(&disallowed);

    let harness_code = render_harness(&token).map_err(MiriBatchFailure::CompileDiagnostic)?;
    let harness_dir = group_dir.join("h");
    fs::create_dir_all(&harness_dir).map_err(|e| {
        MiriBatchFailure::Global(format!("create Miri harness dir {}: {e}", harness_dir.display()))
    })?;
    let harness_path = harness_dir.join("harness.rs");
    fs::write(&harness_path, harness_code).map_err(|e| {
        MiriBatchFailure::Global(format!("write Miri harness {}: {e}", harness_path.display()))
    })?;

    Ok(IsolatedMiriBundle { token, harness_path, bridge_rlib, corpus_dir })
}

#[allow(clippy::too_many_arguments)]
fn build_isolated_miri_group(
    work_root: &Path,
    group_idx: usize,
    source_text: &str,
    group_cases: &[&LitmusCase],
    rustc_bin: &Path,
    miri_sysroot: &Path,
    child_env: MiriChildEnv<'_>,
    setup_timeout: Duration,
) -> Result<IsolatedMiriBundle, String> {
    let bridge_code = generate_miri_bridge(group_cases)?;
    let deadline = Instant::now().checked_add(setup_timeout);
    compile_isolated_miri_crates(
        work_root,
        &format!("group_{group_idx}"),
        source_text,
        bridge_code,
        |tok| generate_miri_harness_with_token(group_cases, Some(tok)),
        rustc_bin,
        miri_sysroot,
        child_env,
        deadline,
    )
    .map_err(MiriBatchFailure::into_detail)
}

#[allow(clippy::too_many_arguments)]
fn build_isolated_miri_fuzz_group(
    work_root: &Path,
    group_rel: &str,
    source_text: &str,
    cases: &[FuzzExecCase],
    rustc_bin: &Path,
    miri_sysroot: &Path,
    child_env: MiriChildEnv<'_>,
    deadline: Option<Instant>,
) -> Result<IsolatedMiriBundle, MiriBatchFailure> {
    let bridge_code =
        generate_miri_fuzz_bridge(cases).map_err(MiriBatchFailure::CompileDiagnostic)?;
    compile_isolated_miri_crates(
        work_root,
        group_rel,
        source_text,
        bridge_code,
        |tok| generate_miri_fuzz_harness_with_token(cases, Some(tok)),
        rustc_bin,
        miri_sysroot,
        child_env,
        deadline,
    )
}

fn miri_marker_prefix(stem_with_sep: &str, token: Option<&str>) -> String {
    match token {
        Some(tok) => {
            if let Some(stem) = stem_with_sep.strip_suffix('=') {
                format!("{stem}:{tok}=")
            } else {
                format!("{stem_with_sep}{tok}:")
            }
        }
        None => stem_with_sep.to_owned(),
    }
}

fn miri_ret_prefix_for_token(token: Option<&str>) -> String {
    miri_marker_prefix(MIRI_RET_PREFIX, token)
}

fn generate_miri_bridge(cases: &[&LitmusCase]) -> Result<String, String> {
    let mut out = String::from("#![allow(unused_unsafe)]\nextern crate corpus;\n\n");
    for (idx, case) in cases.iter().enumerate() {
        validate_rust_fn_path(&case.function)?;
        let arg_exprs =
            case.args.iter().map(rust_arg_expr).collect::<Result<Vec<_>, _>>()?.join(", ");
        let call = format!("unsafe {{ corpus::{}({arg_exprs}) }}", case.function);
        match (&case.expected, &case.expected_return) {
            (Expectation::Pass, Some(exp)) => {
                let ret_ty = rust_ret_type(exp)?;
                let _ = writeln!(
                    out,
                    "#[inline(never)]\npub fn call_case_{idx}() -> {ret_ty} {{\n    {call}\n}}\n"
                );
            }
            _ => {
                let _ = writeln!(
                    out,
                    "#[inline(never)]\npub fn call_case_{idx}() {{\n    let _ret = {call};\n}}\n"
                );
            }
        }
    }
    Ok(out)
}

fn generate_miri_fuzz_bridge(cases: &[FuzzExecCase]) -> Result<String, String> {
    let mut out = String::from("#![allow(unused_unsafe)]\nextern crate corpus;\n\n");
    for (idx, case) in cases.iter().enumerate() {
        validate_rust_fn_path(&case.fn_name)?;
        let arg_exprs =
            case.args.iter().map(rust_arg_expr).collect::<Result<Vec<_>, _>>()?.join(", ");
        let ret_ty = rust_ret_type(&case.ret_shape)?;
        let _ = writeln!(
            out,
            "#[inline(never)]\npub fn call_fuzz_case_{idx}() -> {ret_ty} {{\n    unsafe {{ corpus::{}({arg_exprs}) }}\n}}\n",
            case.fn_name
        );
    }
    Ok(out)
}

#[cfg_attr(not(test), allow(dead_code))]
fn generate_miri_harness(cases: &[&LitmusCase]) -> Result<String, String> {
    generate_miri_harness_with_token(cases, None)
}

fn generate_miri_harness_with_token(
    cases: &[&LitmusCase],
    token: Option<&str>,
) -> Result<String, String> {
    let ret_prefix = miri_ret_prefix_for_token(token);
    let mut out = String::from("extern crate bridge;\n\nfn main() {\n");
    out.push_str("    let selector = std::env::args().nth(1).expect(\"missing case selector\");\n");
    out.push_str("    match selector.as_str() {\n");

    for (idx, case) in cases.iter().enumerate() {
        out.push_str(&format!("        {:?} => {{\n", case.id));
        match (&case.expected, &case.expected_return) {
            (Expectation::Pass, Some(exp)) => {
                let ret_ty = rust_ret_type(exp)?;
                out.push_str(&format!(
                    "            match std::panic::catch_unwind(std::panic::AssertUnwindSafe(bridge::call_case_{idx})) {{\n\
                     \x20               Ok(ret) => {{ let ret: {ret_ty} = ret; {}; }}\n\
                     \x20               Err(_) => println!(\"{ret_prefix}PANICKED\"),\n\
                     \x20           }}\n",
                    rust_print_ret_stmt(exp, "ret", &ret_prefix)?
                ));
            }
            _ => {
                out.push_str(&format!(
                    "            match std::panic::catch_unwind(std::panic::AssertUnwindSafe(bridge::call_case_{idx})) {{\n\
                     \x20               Ok(()) => println!(\"{ret_prefix}UNEXPECTED_RETURN\"),\n\
                     \x20               Err(_) => println!(\"{ret_prefix}PANICKED\"),\n\
                     \x20           }}\n"
                ));
            }
        }
        out.push_str("        }\n");
    }

    out.push_str("        other => panic!(\"unknown differential case selector: {other}\"),\n");
    out.push_str("    }\n}\n");
    Ok(out)
}

pub(crate) fn rust_arg_expr_pub(val: &MirValue) -> Result<String, String> {
    rust_arg_expr(val)
}

pub(crate) fn rust_ret_type_pub(shape: &MirValue) -> Result<String, String> {
    rust_ret_type(shape)
}

/// Format a Rust expression producing a `String` matching
/// `parse_miri_ret_line`.
pub(crate) fn rust_print_ret_payload_expr(shape: &MirValue, var: &str) -> Result<String, String> {
    match shape {
        MirValue::Int { int_kind, .. } => {
            Ok(format!("format!(\"INT:{}:{{}}\", {var})", int_kind.rust_name()))
        }
        MirValue::Bool { .. } => Ok(format!("format!(\"BOOL:{{}}\", {var})")),
        MirValue::Char { .. } => Ok(format!("format!(\"CHAR:{{}}\", {var} as u32)")),
        MirValue::Ordering { .. } => Ok(format!(
            "format!(\"ORDERING:{{}}\", match {var} {{ \
             core::cmp::Ordering::Less => \"less\", \
             core::cmp::Ordering::Equal => \"equal\", \
             core::cmp::Ordering::Greater => \"greater\" }})"
        )),
        MirValue::Unit => Ok(format!("{{ let () = {var}; \"UNIT\".to_owned() }}")),
        MirValue::OverflowPair { int_kind, .. } => {
            Ok(format!("format!(\"OVF:{}:{{}}:{{}}\", {var}.0, {var}.1)", int_kind.rust_name()))
        }
        MirValue::Enum { .. } => Err("Enum expected_return is not supported".to_owned()),
    }
}

/// Partition crate-level inner attributes (`#![...]`, including multi-line
/// attributes) from module body lines, dropping `#![no_std]` so std harnesses
/// compile cleanly.
pub(crate) fn split_crate_attrs(source_text: &str) -> (Vec<String>, Vec<String>) {
    let mut crate_attrs = Vec::new();
    let mut mod_lines = Vec::new();
    let mut in_attr = false;
    let mut bracket_depth: i32 = 0;

    for line in source_text.lines() {
        let trimmed = line.trim();
        if !in_attr && trimmed == "#![no_std]" {
            continue;
        }
        if !in_attr && trimmed.starts_with("#![") {
            in_attr = true;
            bracket_depth = 0;
        }
        if in_attr {
            crate_attrs.push(line.to_owned());
            for ch in line.chars() {
                match ch {
                    '[' => bracket_depth += 1,
                    ']' => bracket_depth -= 1,
                    _ => {}
                }
            }
            if bracket_depth <= 0 {
                in_attr = false;
                bracket_depth = 0;
            }
        } else {
            mod_lines.push(line.to_owned());
        }
    }
    (crate_attrs, mod_lines)
}

fn generate_miri_fuzz_harness_with_token(
    cases: &[FuzzExecCase],
    token: Option<&str>,
) -> Result<String, String> {
    let run_prefix = miri_marker_prefix(MIRI_RUN_PREFIX, token);
    let case_prefix = miri_marker_prefix(MIRI_BATCH_CASE_PREFIX, token);
    let ret_prefix = miri_ret_prefix_for_token(token);

    let mut out =
        String::from("extern crate bridge;\n\nfn run_one(selector: &str, batch_mode: bool) {\n");
    out.push_str("    use std::io::Write;\n");
    out.push_str("    match selector {\n");

    for (idx, case) in cases.iter().enumerate() {
        let ret_ty = rust_ret_type(&case.ret_shape)?;
        let payload_expr = rust_print_ret_payload_expr(&case.ret_shape, "ret")?;
        let _ = writeln!(out, "        {:?} => {{", case.case_id);
        let _ = writeln!(
            out,
            "            println!(\"{run_prefix}{}:{}\");",
            case.case_id, case.fn_name
        );
        out.push_str("            let _ = std::io::stdout().flush();\n");
        out.push_str("            if !batch_mode {\n");
        let _ = writeln!(
            out,
            "                match std::panic::catch_unwind(std::panic::AssertUnwindSafe(bridge::call_fuzz_case_{idx})) {{\n\
             \x20                   Ok(ret) => {{\n\
             \x20                       let ret: {ret_ty} = ret;\n\
             \x20                       let payload = {payload_expr};\n\
             \x20                       println!(\"{case_prefix}{}:{{payload}}\");\n\
             \x20                       println!(\"{ret_prefix}{{payload}}\");\n\
             \x20                   }}\n\
             \x20                   Err(_) => println!(\"{ret_prefix}PANICKED\"),\n\
             \x20               }}",
            case.case_id
        );
        out.push_str("            } else {\n");
        let _ =
            writeln!(out, "                let ret: {ret_ty} = bridge::call_fuzz_case_{idx}();");
        let _ = writeln!(out, "                let payload = {payload_expr};");
        let _ = writeln!(
            out,
            "                println!(\"{case_prefix}{}:{{payload}}\");",
            case.case_id
        );
        out.push_str("            }\n");
        out.push_str("            let _ = std::io::stdout().flush();\n");
        out.push_str("        }\n");
    }

    out.push_str("        other => panic!(\"unknown differential fuzz selector: {other}\"),\n");
    out.push_str("    }\n}\n\nfn main() {\n");
    out.push_str("    let args: Vec<String> = std::env::args().skip(1).collect();\n");
    out.push_str("    if args.first().map(String::as_str) == Some(\"__BATCH__\") {\n");
    out.push_str("        for sel in &args[1..] {\n");
    out.push_str("            run_one(sel, true);\n");
    out.push_str("        }\n");
    out.push_str("    } else if let Some(sel) = args.first() {\n");
    out.push_str("        run_one(sel, false);\n");
    out.push_str("    } else {\n");
    out.push_str("        panic!(\"missing case selector\");\n");
    out.push_str("    }\n}\n");
    Ok(out)
}

fn tool_error_map(
    case_pairs: &[(String, String)],
    detail: &str,
) -> BTreeMap<String, (ObservedOutcome, Option<String>)> {
    case_pairs
        .iter()
        .map(|(id, _)| {
            (id.clone(), (ObservedOutcome::ToolError { detail: detail.to_owned() }, None))
        })
        .collect()
}

fn add_miri_crate_args(mut inv: Invocation, miri_deps: Option<(&Path, &Path)>) -> Invocation {
    if let Some((bridge_rlib, corpus_dir)) = miri_deps {
        let bridge_dir = bridge_rlib.parent().unwrap_or_else(|| Path::new("/"));
        inv = inv
            .arg("--crate-name")
            .arg("harness")
            .arg("--extern")
            .arg(format!("bridge={}", bridge_rlib.display()))
            .arg("-L")
            .arg(bridge_dir)
            .arg("-L")
            .arg(corpus_dir);
    }
    inv
}

#[expect(clippy::too_many_arguments)]
fn run_miri_chunk_with_bisection(
    miri_bin: &Path,
    rustc_bin: Option<&Path>,
    miri_sysroot: &Path,
    child_env: MiriChildEnv<'_>,
    harness_path: &Path,
    miri_deps: Option<(&Path, &Path)>,
    case_pairs: &[(String, String)],
    prog_items: Option<&[(&GenProgram, &FuzzExecCase)]>,
    harness_is_exact_subset: bool,
    expected_token: Option<&str>,
    deadline: Option<Instant>,
) -> BTreeMap<String, (ObservedOutcome, Option<String>)> {
    if case_pairs.is_empty() {
        return BTreeMap::new();
    }
    if case_pairs.len() == 1 {
        let mut out = BTreeMap::new();
        let standalone = prog_items.and_then(|ps| (!harness_is_exact_subset).then_some(ps[0]));
        out.insert(
            case_pairs[0].0.clone(),
            run_single_miri_fuzz_with_fallback(
                miri_bin,
                rustc_bin,
                miri_sysroot,
                child_env,
                harness_path,
                miri_deps,
                (&case_pairs[0].0, &case_pairs[0].1),
                standalone,
                expected_token,
                deadline,
            ),
        );
        return out;
    }

    let inv = Invocation::new(
        miri_bin,
        &["--edition=2024", "--target", PINNED_MIRI_TARGET, "--error-format=json"],
    )
    .arg("--sysroot")
    .arg(miri_sysroot)
    .arg("-C")
    .arg("opt-level=0")
    .arg("-C")
    .arg("debug-assertions=no")
    .arg("-C")
    .arg("overflow-checks=no")
    .arg("-Zmiri-tree-borrows")
    .arg("-Zmiri-seed=0");
    let mut inv = add_miri_crate_args(inv, miri_deps)
        .arg(harness_path)
        .arg("--")
        .arg("__BATCH__")
        .env("LD_LIBRARY_PATH", child_env.ld_path)
        .env("PATH", child_env.path_env);
    for (id, _) in case_pairs {
        inv = inv.arg(id);
    }
    if let Some(td) = child_env.tmpdir {
        inv = inv.env("TMPDIR", td);
    }

    let work_dir = harness_path.parent().unwrap_or_else(|| Path::new("/"));
    let batch_timeout = match effective_timeout_duration(240, deadline) {
        Ok(t) => t,
        Err(detail) => return tool_error_map(case_pairs, &detail),
    };
    match run_supervised_in_tmp(&inv, work_dir, batch_timeout, child_env.tmpdir, "miri batch") {
        Ok(proc_out) => {
            if matches!(proc_out.termination, Termination::Exited(s) if s.success()) {
                let stdout = String::from_utf8_lossy(&proc_out.stdout);
                if let Some(parsed) =
                    parse_miri_batch_stdout_with_token(&stdout, case_pairs, expected_token)
                {
                    return parsed;
                }
            }
            let stderr = String::from_utf8_lossy(&proc_out.stderr);
            match classify_miri_batch_failure(&proc_out.termination, &stderr) {
                Some(MiriBatchFailure::Global(detail)) => {
                    return tool_error_map(case_pairs, &detail);
                }
                Some(MiriBatchFailure::CompileDiagnostic(detail)) => {
                    if let (Some(items), Some(r_bin)) = (prog_items, rustc_bin)
                        && items.len() > 1
                    {
                        let mid = items.len() / 2;
                        let mut combined = run_miri_compile_bisect_slice(
                            miri_bin,
                            r_bin,
                            miri_sysroot,
                            child_env,
                            &items[..mid],
                            deadline,
                        );
                        combined.extend(run_miri_compile_bisect_slice(
                            miri_bin,
                            r_bin,
                            miri_sysroot,
                            child_env,
                            &items[mid..],
                            deadline,
                        ));
                        return combined;
                    }
                    return tool_error_map(case_pairs, &detail);
                }
                None => {}
            }
        }
        Err(err) => {
            let detail = format!("Miri batch supervisor error: {err}");
            return tool_error_map(case_pairs, &detail);
        }
    }

    // Runtime-local faults (UB, panic, abort, unsupported, or partial output)
    // bisect down on the already-compiling shared harness.
    let mid = case_pairs.len() / 2;
    let left_progs = prog_items.map(|ps| &ps[..mid]);
    let right_progs = prog_items.map(|ps| &ps[mid..]);
    let mut combined = run_miri_chunk_with_bisection(
        miri_bin,
        rustc_bin,
        miri_sysroot,
        child_env,
        harness_path,
        miri_deps,
        &case_pairs[..mid],
        left_progs,
        false,
        expected_token,
        deadline,
    );
    combined.extend(run_miri_chunk_with_bisection(
        miri_bin,
        rustc_bin,
        miri_sysroot,
        child_env,
        harness_path,
        miri_deps,
        &case_pairs[mid..],
        right_progs,
        false,
        expected_token,
        deadline,
    ));
    combined
}

fn run_miri_compile_bisect_slice(
    miri_bin: &Path,
    rustc_bin: &Path,
    miri_sysroot: &Path,
    child_env: MiriChildEnv<'_>,
    items: &[(&GenProgram, &FuzzExecCase)],
    deadline: Option<Instant>,
) -> BTreeMap<String, (ObservedOutcome, Option<String>)> {
    if items.is_empty() {
        return BTreeMap::new();
    }
    let sub_pairs: Vec<(String, String)> =
        items.iter().map(|(_, c)| (c.case_id.clone(), c.fn_name.clone())).collect();
    let sub_progs: Vec<&GenProgram> = items.iter().map(|(p, _)| *p).collect();
    let sub_cases: Vec<FuzzExecCase> = items.iter().map(|(_, c)| (*c).clone()).collect();
    let sub_src = if sub_progs.len() == 1 {
        sub_progs[0].render_standalone()
    } else {
        render_batch_crate(&sub_progs)
    };
    let work_dir =
        match crate::mir_eval_runner::build_temp_dir("anneal-miri-bisect-", child_env.tmpdir) {
            Ok(d) => d,
            Err(e) => return tool_error_map(&sub_pairs, &e),
        };
    let bundle = match build_isolated_miri_fuzz_group(
        work_dir.path(),
        "slice",
        &sub_src,
        &sub_cases,
        rustc_bin,
        miri_sysroot,
        child_env,
        deadline,
    ) {
        Ok(b) => b,
        Err(MiriBatchFailure::Global(detail)) => return tool_error_map(&sub_pairs, &detail),
        Err(MiriBatchFailure::CompileDiagnostic(detail)) => {
            drop(work_dir);
            if items.len() > 1 {
                let mid = items.len() / 2;
                let mut combined = run_miri_compile_bisect_slice(
                    miri_bin,
                    rustc_bin,
                    miri_sysroot,
                    child_env,
                    &items[..mid],
                    deadline,
                );
                combined.extend(run_miri_compile_bisect_slice(
                    miri_bin,
                    rustc_bin,
                    miri_sysroot,
                    child_env,
                    &items[mid..],
                    deadline,
                ));
                return combined;
            }
            return tool_error_map(&sub_pairs, &detail);
        }
    };
    let slice_items: Vec<(&GenProgram, &FuzzExecCase)> =
        sub_progs.into_iter().zip(sub_cases.iter()).collect();
    run_miri_chunk_with_bisection(
        miri_bin,
        Some(rustc_bin),
        miri_sysroot,
        child_env,
        &bundle.harness_path,
        Some((&bundle.bridge_rlib, &bundle.corpus_dir)),
        &sub_pairs,
        Some(&slice_items),
        true,
        Some(&bundle.token),
        deadline,
    )
}

fn is_miri_global_stderr(stderr: &str) -> bool {
    if is_global_compiler_or_sysroot_stderr(stderr) {
        return true;
    }
    for line in stderr.lines() {
        let trimmed = line.trim();
        if let Ok(val) = serde_json::from_str::<Value>(trimmed)
            && val.get("$message_type").and_then(Value::as_str) == Some("diagnostic")
        {
            if let Some(code) = val.get("code").and_then(|c| c.get("code")).and_then(Value::as_str)
                && code == "E0463"
            {
                return true;
            }
            if let Some(msg) = val.get("message").and_then(Value::as_str)
                && (msg.starts_with("internal compiler error:")
                    || msg.contains("can't find crate for")
                    || msg.contains("could not execute process"))
            {
                return true;
            }
            if let Some(rendered) = val.get("rendered").and_then(Value::as_str)
                && is_global_compiler_or_sysroot_stderr(rendered)
            {
                return true;
            }
        }
    }
    false
}

fn is_case_local_runtime_stderr(stderr: &str) -> bool {
    for line in stderr.lines() {
        let trimmed = line.trim();
        if let Ok(val) = serde_json::from_str::<Value>(trimmed)
            && val.get("$message_type").and_then(Value::as_str) == Some("diagnostic")
        {
            if val.get("level").and_then(Value::as_str) == Some("error")
                && let Some(msg) = val.get("message").and_then(Value::as_str)
                && (msg.starts_with("Undefined Behavior:")
                    || msg.starts_with("abnormal termination:")
                    || msg.starts_with("unsupported operation:"))
            {
                return true;
            }
            continue;
        }
    }
    stderr.contains("error: Undefined Behavior:")
        || stderr.contains("error: abnormal termination:")
        || stderr.contains("error: unsupported operation:")
        || stderr.contains("panicked at ")
}

fn classify_miri_batch_failure(
    termination: &Termination,
    stderr: &str,
) -> Option<MiriBatchFailure> {
    let snippet = || stderr.lines().take(6).collect::<Vec<_>>().join(" | ");
    match termination {
        Termination::TimedOut(_) => Some(MiriBatchFailure::Global(format!(
            "Miri batch timed out ({}): {}",
            termination.describe(),
            snippet()
        ))),
        Termination::LaunchFailed(msg) => {
            Some(MiriBatchFailure::Global(format!("Miri batch launch failed: {msg}")))
        }
        Termination::Exited(status) => {
            if is_miri_global_stderr(stderr) {
                return Some(MiriBatchFailure::Global(format!(
                    "Miri batch compiler/sysroot failure ({}): {}",
                    termination.describe(),
                    snippet()
                )));
            }
            if !status.success() && !is_case_local_runtime_stderr(stderr) {
                return Some(MiriBatchFailure::CompileDiagnostic(format!(
                    "Miri batch compile failure ({}): {}",
                    termination.describe(),
                    snippet()
                )));
            }
            None
        }
    }
}

fn parse_miri_batch_stdout_with_token(
    stdout: &str,
    case_pairs: &[(String, String)],
    expected_token: Option<&str>,
) -> Option<BTreeMap<String, (ObservedOutcome, Option<String>)>> {
    let run_pfx = miri_marker_prefix(MIRI_RUN_PREFIX, expected_token);
    let case_pfx = miri_marker_prefix(MIRI_BATCH_CASE_PREFIX, expected_token);
    let ret_pfx_tok = format!("{MIRI_RET_STEM}:");
    let mut run_seen = BTreeMap::new();
    let mut raw = BTreeMap::new();
    for line in stdout.lines() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix(&run_pfx)
            && let Some((id, fn_name)) = rest.split_once(':')
        {
            if run_seen.insert(id.to_owned(), fn_name.to_owned()).is_some() {
                return None;
            }
        } else if let Some(rest) = trimmed.strip_prefix(&case_pfx)
            && let Some((id, payload)) = rest.split_once(':')
        {
            let value = parse_miri_ret_line(payload).ok()?;
            if raw
                .insert(id.to_owned(), (ObservedOutcome::Returned { value }, payload.to_owned()))
                .is_some()
            {
                return None;
            }
        } else if expected_token.is_some()
            && (trimmed.starts_with(MIRI_RUN_PREFIX)
                || trimmed.starts_with(MIRI_BATCH_CASE_PREFIX)
                || trimmed.starts_with(MIRI_RET_PREFIX)
                || trimmed.starts_with(&ret_pfx_tok))
        {
            return None;
        }
    }
    if raw.len() != case_pairs.len() || run_seen.len() != case_pairs.len() {
        return None;
    }
    let mut out = BTreeMap::new();
    for (id, fn_name) in case_pairs {
        if run_seen.get(id).map(String::as_str) != Some(fn_name.as_str()) {
            return None;
        }
        let (outcome, payload) = raw.remove(id)?;
        let evidence =
            format!("{MIRI_RUN_PREFIX}{id}:{fn_name}|{MIRI_BATCH_CASE_PREFIX}{id}:{payload}");
        out.insert(id.clone(), (outcome, Some(evidence)));
    }
    Some(out)
}

fn rust_arg_expr(val: &MirValue) -> Result<String, String> {
    match val {
        MirValue::Int { int_kind, bits } => Ok(int_kind.format_rust_literal(*bits)),
        MirValue::Bool { value } => Ok(value.to_string()),
        MirValue::Char { scalar } => {
            char::from_u32(*scalar).ok_or_else(|| format!("invalid Unicode scalar {scalar}"))?;
            Ok(format!("char::from_u32({scalar}u32).unwrap()"))
        }
        MirValue::Ordering { value } => Ok(value.to_rust_expr().to_owned()),
        MirValue::Unit => Ok("()".to_owned()),
        MirValue::Enum { enum_type, variant, .. } => {
            validate_rust_ident(enum_type, "enum name")?;
            validate_rust_ident(variant, "enum variant")?;
            Ok(format!("corpus::{enum_type}::{variant}"))
        }
        MirValue::OverflowPair { .. } => {
            Err("OverflowPair is not a supported Miri harness input type in Stage 1".to_owned())
        }
    }
}

fn rust_ret_type(shape: &MirValue) -> Result<String, String> {
    match shape {
        MirValue::Int { int_kind, .. } => Ok(int_kind.rust_name().to_owned()),
        MirValue::Bool { .. } => Ok("bool".to_owned()),
        MirValue::Char { .. } => Ok("char".to_owned()),
        MirValue::Ordering { .. } => Ok("core::cmp::Ordering".to_owned()),
        MirValue::Unit => Ok("()".to_owned()),
        MirValue::OverflowPair { int_kind, .. } => Ok(format!("({}, bool)", int_kind.rust_name())),
        MirValue::Enum { .. } => Err("Enum expected_return is not supported in Stage 1".to_owned()),
    }
}

fn rust_print_ret_stmt(shape: &MirValue, var: &str, ret_prefix: &str) -> Result<String, String> {
    match shape {
        MirValue::Int { int_kind, .. } => {
            Ok(format!("println!(\"{ret_prefix}INT:{}:{{}}\", {var})", int_kind.rust_name()))
        }
        MirValue::Bool { .. } => Ok(format!("println!(\"{ret_prefix}BOOL:{{}}\", {var})")),
        MirValue::Char { .. } => Ok(format!("println!(\"{ret_prefix}CHAR:{{}}\", {var} as u32)")),
        MirValue::Ordering { .. } => Ok(format!(
            "println!(\"{ret_prefix}ORDERING:{{}}\", match {var} {{ \
             core::cmp::Ordering::Less => \"less\", \
             core::cmp::Ordering::Equal => \"equal\", \
             core::cmp::Ordering::Greater => \"greater\" }})"
        )),
        MirValue::Unit => Ok(format!("let () = {var}; println!(\"{ret_prefix}UNIT\")")),
        MirValue::OverflowPair { int_kind, .. } => Ok(format!(
            "println!(\"{ret_prefix}OVF:{}:{{}}:{{}}\", {var}.0, {var}.1)",
            int_kind.rust_name()
        )),
        MirValue::Enum { .. } => Err("Enum expected_return is not supported in Stage 1".to_owned()),
    }
}

#[allow(clippy::too_many_arguments)]
fn run_single_miri(
    miri_bin: &Path,
    miri_sysroot: &Path,
    child_env: MiriChildEnv<'_>,
    harness_path: &Path,
    bridge_rlib: &Path,
    corpus_dir: &Path,
    selector: &str,
    expected_token: Option<&str>,
) -> ObservedOutcome {
    run_single_miri_until(
        miri_bin,
        miri_sysroot,
        child_env,
        harness_path,
        Some((bridge_rlib, corpus_dir)),
        selector,
        expected_token,
        None,
    )
}

#[expect(clippy::too_many_arguments)]
fn invoke_single_miri_until(
    miri_bin: &Path,
    miri_sysroot: &Path,
    child_env: MiriChildEnv<'_>,
    harness_path: &Path,
    miri_deps: Option<(&Path, &Path)>,
    selector: &str,
    mute_target_io: bool,
    deadline: Option<Instant>,
) -> Result<(Option<i32>, String, String), ObservedOutcome> {
    let mut inv = Invocation::new(
        miri_bin,
        &["--edition=2024", "--target", PINNED_MIRI_TARGET, "--error-format=json"],
    )
    .arg("--sysroot")
    .arg(miri_sysroot)
    .arg("-C")
    .arg("opt-level=0")
    .arg("-C")
    .arg("debug-assertions=no")
    .arg("-C")
    .arg("overflow-checks=no")
    .arg("-Zmiri-tree-borrows")
    .arg("-Zmiri-seed=0");
    if mute_target_io {
        inv = inv.arg("-Zmiri-mute-stdout-stderr");
    }
    let mut inv = add_miri_crate_args(inv, miri_deps)
        .arg(harness_path)
        .arg("--")
        .arg(selector)
        .env("LD_LIBRARY_PATH", child_env.ld_path)
        .env("PATH", child_env.path_env);
    if let Some(td) = child_env.tmpdir {
        inv = inv.env("TMPDIR", td);
    }

    let case_timeout = effective_timeout_duration(MIRI_CASE_TIMEOUT_SECS, deadline)
        .map_err(|detail| ObservedOutcome::ToolError { detail })?;
    let work_dir = harness_path.parent().unwrap_or_else(|| Path::new("/"));
    let out = run_supervised_in_tmp(&inv, work_dir, case_timeout, child_env.tmpdir, selector)
        .map_err(|detail| ObservedOutcome::ToolError { detail })?;
    let exit_code = match out.termination {
        Termination::Exited(status) => status.code(),
        Termination::TimedOut(status) => {
            return Err(ObservedOutcome::ToolError {
                detail: format!(
                    "miri timed out after {:.3}s for {selector} ({status})",
                    case_timeout.as_secs_f64()
                ),
            });
        }
        Termination::LaunchFailed(err) => {
            return Err(ObservedOutcome::ToolError {
                detail: format!("spawn miri for {selector}: {err}"),
            });
        }
    };

    Ok((
        exit_code,
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    ))
}

fn invoke_single_miri_verified_until(
    miri_bin: &Path,
    miri_sysroot: &Path,
    child_env: MiriChildEnv<'_>,
    harness_path: &Path,
    miri_deps: Option<(&Path, &Path)>,
    selector: &str,
    deadline: Option<Instant>,
) -> Result<(Option<i32>, String, String), ObservedOutcome> {
    let (exit_code, stdout, stderr) = invoke_single_miri_until(
        miri_bin,
        miri_sysroot,
        child_env,
        harness_path,
        miri_deps,
        selector,
        false,
        deadline,
    )?;
    if exit_code == Some(0) {
        return Ok((exit_code, stdout, stderr));
    }
    // Non-zero exits re-run with `-Zmiri-mute-stdout-stderr` so Miri's host
    // diagnostics arrive over a channel fixture code cannot write.
    let (muted_exit, _muted_stdout, muted_stderr) = invoke_single_miri_until(
        miri_bin,
        miri_sysroot,
        child_env,
        harness_path,
        miri_deps,
        selector,
        true,
        deadline,
    )?;
    if muted_exit == Some(0) {
        return Err(ObservedOutcome::ToolError {
            detail: format!(
                "Miri non-zero exit ({exit_code:?}) for {selector} did not reproduce under -Zmiri-mute-stdout-stderr"
            ),
        });
    }
    Ok((muted_exit, stdout, muted_stderr))
}

#[expect(clippy::too_many_arguments)]
fn run_single_miri_until(
    miri_bin: &Path,
    miri_sysroot: &Path,
    child_env: MiriChildEnv<'_>,
    harness_path: &Path,
    miri_deps: Option<(&Path, &Path)>,
    selector: &str,
    expected_token: Option<&str>,
    deadline: Option<Instant>,
) -> ObservedOutcome {
    match invoke_single_miri_verified_until(
        miri_bin,
        miri_sysroot,
        child_env,
        harness_path,
        miri_deps,
        selector,
        deadline,
    ) {
        Ok((exit_code, stdout, stderr)) => {
            parse_miri_output_with_token(exit_code, &stdout, &stderr, expected_token)
        }
        Err(err_outcome) => err_outcome,
    }
}

#[expect(clippy::too_many_arguments)]
fn run_single_miri_fuzz_with_fallback(
    miri_bin: &Path,
    rustc_bin: Option<&Path>,
    miri_sysroot: &Path,
    child_env: MiriChildEnv<'_>,
    harness_path: &Path,
    miri_deps: Option<(&Path, &Path)>,
    (case_id, fn_name): (&str, &str),
    standalone_item: Option<(&GenProgram, &FuzzExecCase)>,
    expected_token: Option<&str>,
    deadline: Option<Instant>,
) -> (ObservedOutcome, Option<String>) {
    let (exit_code, stdout, stderr) = match invoke_single_miri_verified_until(
        miri_bin,
        miri_sysroot,
        child_env,
        harness_path,
        miri_deps,
        case_id,
        deadline,
    ) {
        Ok(res) => res,
        Err(err_outcome) => return (err_outcome, None),
    };
    let parsed = parse_miri_fuzz_single_output_with_token(
        exit_code,
        case_id,
        fn_name,
        &stdout,
        &stderr,
        expected_token,
    );
    if matches!(&parsed.0, ObservedOutcome::ToolError { .. })
        && let Some(item) = standalone_item
        && let Some(rustc_bin) = rustc_bin
        && exit_code.is_some_and(|c| c != 0)
        && !is_miri_global_stderr(&stderr)
        && !is_case_local_runtime_stderr(&stderr)
    {
        let mut isolated = run_miri_compile_bisect_slice(
            miri_bin,
            rustc_bin,
            miri_sysroot,
            child_env,
            &[item],
            deadline,
        );
        if let Some(res) = isolated.remove(case_id) {
            return res;
        }
    }
    parsed
}

fn parse_miri_fuzz_single_output_with_token(
    exit_code: Option<i32>,
    case_id: &str,
    fn_name: &str,
    stdout: &str,
    stderr: &str,
    expected_token: Option<&str>,
) -> (ObservedOutcome, Option<String>) {
    let run_pfx = miri_marker_prefix(MIRI_RUN_PREFIX, expected_token);
    let case_pfx = miri_marker_prefix(MIRI_BATCH_CASE_PREFIX, expected_token);
    let run_marker = format!("{run_pfx}{case_id}:{fn_name}");
    let case_prefix = format!("{case_pfx}{case_id}:");
    let canonical_run = format!("{MIRI_RUN_PREFIX}{case_id}:{fn_name}");
    let canonical_case_prefix = format!("{MIRI_BATCH_CASE_PREFIX}{case_id}:");
    let mut run_count = 0usize;
    let mut matched_payload: Option<&str> = None;
    for line in stdout.lines() {
        let trimmed = line.trim();
        if trimmed == run_marker {
            run_count += 1;
            if run_count > 1 {
                return (
                    ObservedOutcome::ToolError {
                        detail: format!("Miri output contained duplicate `{run_marker}` marker"),
                    },
                    None,
                );
            }
        } else if let Some(payload) = trimmed.strip_prefix(&case_prefix) {
            if matched_payload.is_some() {
                return (
                    ObservedOutcome::ToolError {
                        detail: format!("Miri output contained duplicate `{case_prefix}` payload"),
                    },
                    None,
                );
            }
            matched_payload = Some(payload);
        } else if expected_token.is_some()
            && (trimmed.starts_with(MIRI_RUN_PREFIX) || trimmed.starts_with(MIRI_BATCH_CASE_PREFIX))
        {
            return (
                ObservedOutcome::ToolError {
                    detail: format!(
                        "Miri output contained unauthenticated case/run marker: {trimmed:?}"
                    ),
                },
                None,
            );
        }
    }
    let has_run = run_count == 1;
    let outcome = parse_miri_output_with_token(exit_code, stdout, stderr, expected_token);
    match outcome {
        ObservedOutcome::Returned { value } => {
            if !has_run {
                return (
                    ObservedOutcome::ToolError {
                        detail: format!("Miri output missing case marker `{run_marker}`"),
                    },
                    None,
                );
            }
            let Some(payload) = matched_payload else {
                return (
                    ObservedOutcome::ToolError {
                        detail: format!("Miri output missing `{case_prefix}` payload"),
                    },
                    None,
                );
            };
            (
                ObservedOutcome::Returned { value },
                Some(format!("{canonical_run}|{canonical_case_prefix}{payload}")),
            )
        }
        ObservedOutcome::UndefinedBehavior { ref detail } => {
            if has_run {
                let ev = format!("{canonical_run}|UB|{detail}");
                (outcome, Some(ev))
            } else {
                (
                    ObservedOutcome::ToolError {
                        detail: format!("Miri UB lacked `{run_marker}`: {detail}"),
                    },
                    None,
                )
            }
        }
        ObservedOutcome::AbnormalAbort { ref detail } => {
            if has_run {
                let ev = format!("{canonical_run}|ABORT|{detail}");
                (outcome, Some(ev))
            } else {
                (
                    ObservedOutcome::ToolError {
                        detail: format!("Miri abort lacked `{run_marker}`: {detail}"),
                    },
                    None,
                )
            }
        }
        ObservedOutcome::Panic { ref detail } => {
            if has_run {
                let ev = format!("{canonical_run}|PANIC|{detail}");
                (outcome, Some(ev))
            } else {
                (
                    ObservedOutcome::ToolError {
                        detail: format!("Miri panic lacked `{run_marker}`: {detail}"),
                    },
                    None,
                )
            }
        }
        ObservedOutcome::Unsupported { ref detail } => {
            if has_run {
                let ev = format!("{canonical_run}|UNSUPPORTED|{detail}");
                (outcome, Some(ev))
            } else {
                (
                    ObservedOutcome::ToolError {
                        detail: format!("Miri unsupported lacked `{run_marker}`: {detail}"),
                    },
                    None,
                )
            }
        }
        other => (other, None),
    }
}

/// Parse Miri stdout, stderr, and exit status into an [`ObservedOutcome`].
pub fn parse_miri_output(exit_code: Option<i32>, stdout: &str, stderr: &str) -> ObservedOutcome {
    parse_miri_output_with_token(exit_code, stdout, stderr, None)
}

fn parse_miri_output_with_token(
    exit_code: Option<i32>,
    stdout: &str,
    stderr: &str,
    expected_token: Option<&str>,
) -> ObservedOutcome {
    if exit_code == Some(0) {
        let prefix = miri_ret_prefix_for_token(expected_token);
        let mut matched: Option<&str> = None;
        for raw_line in stdout.lines() {
            if let Some(payload) = raw_line.strip_prefix(&prefix) {
                if matched.is_some() {
                    return ObservedOutcome::ToolError {
                        detail: format!(
                            "Miri stdout contained duplicate `{prefix}` markers; stdout={stdout:?}"
                        ),
                    };
                }
                matched = Some(payload);
            } else if expected_token.is_some()
                && (raw_line.starts_with(MIRI_RET_PREFIX)
                    || raw_line.starts_with(&format!("{MIRI_RET_STEM}:")))
            {
                return ObservedOutcome::ToolError {
                    detail: format!(
                        "Miri stdout contained unauthenticated `{MIRI_RET_STEM}` marker; stdout={stdout:?}"
                    ),
                };
            }
        }
        let Some(line) = matched else {
            return ObservedOutcome::ToolError {
                detail: format!("Miri exited 0 without `{prefix}` line; stdout={stdout:?}"),
            };
        };
        if line == "PANICKED" {
            return ObservedOutcome::Panic {
                detail: "panicked during Miri execution (caught by harness)".to_owned(),
            };
        }
        if line == "UNEXPECTED_RETURN" {
            // Represent a clean return cleanly so evaluate_case distinguishes
            // normal return from expected UB or panic.
            return ObservedOutcome::Returned { value: MirValue::Unit };
        }
        return match parse_miri_ret_line(line) {
            Ok(value) => ObservedOutcome::Returned { value },
            Err(e) => {
                ObservedOutcome::ToolError { detail: format!("parse Miri return {line:?}: {e}") }
            }
        };
    }

    if expected_token.is_some() {
        return parse_miri_json_stderr(exit_code, stderr);
    }

    if stderr.contains("error: internal compiler error:")
        || stderr.contains("thread 'rustc' panicked at ")
    {
        return ObservedOutcome::ToolError {
            detail: format!(
                "Miri compiler ICE ({:?}): {}",
                exit_code,
                stderr.lines().take(6).collect::<Vec<_>>().join(" | ")
            ),
        };
    }
    if stderr.contains("error: Undefined Behavior:") {
        let headline = stderr
            .lines()
            .find(|l| l.contains("error: Undefined Behavior:"))
            .unwrap_or("Undefined Behavior")
            .trim()
            .to_owned();
        return ObservedOutcome::UndefinedBehavior { detail: headline };
    }
    if stderr.contains("error: abnormal termination:") {
        let headline = stderr
            .lines()
            .find(|l| l.contains("error: abnormal termination:"))
            .unwrap_or("abnormal termination")
            .trim()
            .to_owned();
        return ObservedOutcome::AbnormalAbort { detail: headline };
    }
    if stderr.contains("error: unsupported operation:") {
        let headline = stderr
            .lines()
            .find(|l| l.contains("error: unsupported operation:"))
            .unwrap_or("unsupported operation")
            .trim()
            .to_owned();
        return ObservedOutcome::Unsupported { detail: headline };
    }
    if stderr.contains("panicked at ") {
        let headline = stderr
            .lines()
            .find(|l| l.contains("panicked at "))
            .unwrap_or("panicked")
            .trim()
            .to_owned();
        return ObservedOutcome::Panic { detail: headline };
    }

    ObservedOutcome::ToolError {
        detail: format!(
            "Miri exited {:?}: {}",
            exit_code,
            stderr.lines().take(6).collect::<Vec<_>>().join(" | ")
        ),
    }
}

fn is_forged_plain_diagnostic_line(line: &str) -> bool {
    let trimmed = line.trim();
    trimmed.contains("error: Undefined Behavior:")
        || trimmed.contains("error: abnormal termination:")
        || trimmed.contains("error: unsupported operation:")
        || trimmed.contains("error: internal compiler error:")
}

fn is_abort_summary_message(msg: &str) -> bool {
    msg.starts_with("aborting due to ") && msg.contains("previous error")
}

fn normalize_diag_path(path: &str) -> String {
    path.replace('\\', "/")
}

fn path_matches_isolated_harness(path: &str) -> bool {
    let norm = normalize_diag_path(path);
    norm == "h/harness.rs" || norm.ends_with("/h/harness.rs")
}

fn is_harness_like_diag_path(path: &str) -> bool {
    let norm = normalize_diag_path(path);
    let base = norm.rsplit('/').next().unwrap_or("");
    base == "harness.rs"
        || base.starts_with("harness_")
        || base.starts_with("fuzz_miri_harness_")
        || norm.starts_with("sec_")
        || norm.contains("/sec_")
}

fn backtrace_note_references_active_harness(msg: &str) -> bool {
    if !msg.starts_with("stack backtrace:") {
        return false;
    }
    msg.lines().any(|line| {
        let Some(rest) = line.trim().strip_prefix("at ") else {
            return false;
        };
        let mut path_part = rest.split_once(": ").map_or(rest, |(head, _)| head);
        for _ in 0..2 {
            if let Some((head, tail)) = path_part.rsplit_once(':')
                && !tail.is_empty()
                && tail.bytes().all(|b| b.is_ascii_digit())
            {
                path_part = head;
            } else {
                break;
            }
        }
        path_matches_isolated_harness(path_part.trim())
    })
}

fn validate_diagnostic_origin(obj: &Value, msg: &str) -> Result<(), String> {
    let Some(spans) = obj.get("spans").and_then(Value::as_array) else {
        return Err("missing diagnostic spans array".to_owned());
    };
    let Some(children) = obj.get("children").and_then(Value::as_array) else {
        return Err("missing diagnostic children array".to_owned());
    };
    if !obj.get("rendered").is_some_and(Value::is_string) {
        return Err("missing diagnostic rendered text".to_owned());
    }
    let mut saw_active_harness = false;
    for span in spans {
        let Some(fname) = span.get("file_name").and_then(Value::as_str) else {
            return Err("diagnostic span missing file_name".to_owned());
        };
        if path_matches_isolated_harness(fname) {
            saw_active_harness = true;
        } else if is_harness_like_diag_path(fname) {
            return Err(format!("diagnostic span `{fname}` does not match isolated harness path"));
        }
    }
    for child in children {
        if child.get("level").and_then(Value::as_str) == Some("note")
            && let Some(cmsg) = child.get("message").and_then(Value::as_str)
            && backtrace_note_references_active_harness(cmsg)
        {
            saw_active_harness = true;
        }
    }
    if !msg.starts_with("internal compiler error:") && !saw_active_harness {
        return Err("diagnostic lacked stack frame or span from active isolated harness".to_owned());
    }
    Ok(())
}

fn parse_miri_json_stderr(exit_code: Option<i32>, stderr: &str) -> ObservedOutcome {
    if stderr.contains("thread 'rustc' panicked at ") {
        return ObservedOutcome::ToolError {
            detail: format!(
                "Miri compiler ICE ({:?}): {}",
                exit_code,
                stderr.lines().take(6).collect::<Vec<_>>().join(" | ")
            ),
        };
    }

    let mut fatal_errors: Vec<String> = Vec::new();
    let mut saw_abort_summary = false;
    let mut saw_plain_panic = false;

    for raw_line in stderr.lines() {
        let trimmed = raw_line.trim();
        if trimmed.is_empty() {
            continue;
        }
        if let Ok(val) = serde_json::from_str::<Value>(trimmed)
            && val.get("$message_type").and_then(Value::as_str) == Some("diagnostic")
        {
            if val.get("level").and_then(Value::as_str) == Some("error") {
                let Some(msg) = val.get("message").and_then(Value::as_str) else {
                    return ObservedOutcome::ToolError {
                        detail: format!("Miri JSON error diagnostic missing message: {trimmed}"),
                    };
                };
                if is_abort_summary_message(msg) {
                    saw_abort_summary = true;
                } else {
                    if let Err(err) = validate_diagnostic_origin(&val, msg) {
                        return ObservedOutcome::ToolError {
                            detail: format!("Miri diagnostic failed schema/origin check: {err}"),
                        };
                    }
                    fatal_errors.push(msg.to_owned());
                }
            }
            continue;
        }
        if is_forged_plain_diagnostic_line(trimmed) {
            return ObservedOutcome::ToolError {
                detail: format!(
                    "Miri stderr contained unauthenticated plain-text diagnostic: {trimmed:?}"
                ),
            };
        }
        if trimmed.contains("panicked at ") {
            saw_plain_panic = true;
        }
    }

    if fatal_errors.len() > 1 {
        return ObservedOutcome::ToolError {
            detail: format!(
                "Miri stderr contained multiple fatal error diagnostics: {fatal_errors:?}"
            ),
        };
    }
    if let Some(msg) = fatal_errors.into_iter().next() {
        if saw_plain_panic || !saw_abort_summary {
            return ObservedOutcome::ToolError {
                detail: format!(
                    "Miri diagnostic `{msg}` lacked clean aborting summary or collided with target panic"
                ),
            };
        }
        if msg.starts_with("internal compiler error:") {
            return ObservedOutcome::ToolError {
                detail: format!("Miri compiler ICE ({exit_code:?}): error: {msg}"),
            };
        }
        if msg.starts_with("Undefined Behavior:") {
            return ObservedOutcome::UndefinedBehavior { detail: format!("error: {msg}") };
        }
        if msg.starts_with("abnormal termination:") {
            return ObservedOutcome::AbnormalAbort { detail: format!("error: {msg}") };
        }
        if msg.starts_with("unsupported operation:") {
            return ObservedOutcome::Unsupported { detail: format!("error: {msg}") };
        }
        return ObservedOutcome::ToolError {
            detail: format!("Miri exited {exit_code:?}: error: {msg}"),
        };
    }

    if exit_code == Some(101) && saw_plain_panic {
        let headline = stderr
            .lines()
            .find(|l| l.contains("panicked at "))
            .unwrap_or("panicked")
            .trim()
            .to_owned();
        return ObservedOutcome::Panic { detail: headline };
    }

    ObservedOutcome::ToolError {
        detail: format!(
            "Miri exited {:?}: {}",
            exit_code,
            stderr.lines().take(6).collect::<Vec<_>>().join(" | ")
        ),
    }
}

pub fn parse_miri_ret_line(line: &str) -> Result<MirValue, String> {
    if line == "UNIT" {
        return Ok(MirValue::Unit);
    }
    if let Some(rest) = line.strip_prefix("INT:") {
        let (kind_raw, dec_raw) =
            rest.split_once(':').ok_or_else(|| format!("malformed INT payload {rest:?}"))?;
        let int_kind = IntKind::parse_rust_name(kind_raw)?;
        let bits = int_kind.parse_decimal_bits(dec_raw)?;
        return Ok(MirValue::Int { int_kind, bits });
    }
    if let Some(rest) = line.strip_prefix("BOOL:") {
        return match rest.trim() {
            "true" => Ok(MirValue::Bool { value: true }),
            "false" => Ok(MirValue::Bool { value: false }),
            _ => Err(format!("invalid BOOL payload {rest:?}")),
        };
    }
    if let Some(rest) = line.strip_prefix("CHAR:") {
        let scalar: u32 =
            rest.trim().parse().map_err(|e| format!("invalid CHAR scalar {rest:?}: {e}"))?;
        char::from_u32(scalar).ok_or_else(|| format!("CHAR {scalar} is not a Unicode scalar"))?;
        return Ok(MirValue::Char { scalar });
    }
    if let Some(rest) = line.strip_prefix("ORDERING:") {
        return Ok(MirValue::Ordering { value: OrderingKind::parse(rest)? });
    }
    if let Some(rest) = line.strip_prefix("OVF:") {
        let mut parts = rest.splitn(3, ':');
        let kind_raw = parts.next().ok_or_else(|| format!("malformed OVF payload {rest:?}"))?;
        let dec_raw = parts.next().ok_or_else(|| format!("malformed OVF payload {rest:?}"))?;
        let ovf_raw = parts.next().ok_or_else(|| format!("malformed OVF payload {rest:?}"))?;
        let int_kind = IntKind::parse_rust_name(kind_raw)?;
        let bits = int_kind.parse_decimal_bits(dec_raw)?;
        let overflow = match ovf_raw.trim() {
            "true" => true,
            "false" => false,
            _ => return Err(format!("invalid OVF flag {ovf_raw:?}")),
        };
        return Ok(MirValue::OverflowPair { int_kind, bits, overflow });
    }
    Err(format!("unknown Miri return line {line:?}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_miri_return_lines() {
        assert_eq!(
            parse_miri_output(Some(0), "ANNEAL_MIRI_RET=INT:i32:-20\n", ""),
            ObservedOutcome::Returned {
                value: MirValue::Int { int_kind: IntKind::I32, bits: (-20i32 as u32) as u128 }
            }
        );
        assert_eq!(
            parse_miri_output(Some(0), "ANNEAL_MIRI_RET=OVF:u64:4:true\n", ""),
            ObservedOutcome::Returned {
                value: MirValue::OverflowPair { int_kind: IntKind::U64, bits: 4, overflow: true }
            }
        );
        assert_eq!(
            parse_miri_output(Some(0), "ANNEAL_MIRI_RET=ORDERING:less\n", ""),
            ObservedOutcome::Returned { value: MirValue::Ordering { value: OrderingKind::Less } }
        );
        let dup = parse_miri_output(
            Some(0),
            "ANNEAL_MIRI_RET=INT:u32:99\nANNEAL_MIRI_RET=INT:u32:7\n",
            "",
        );
        assert!(matches!(dup, ObservedOutcome::ToolError { .. }), "{dup:?}");
        let forged_bare = parse_miri_output_with_token(
            Some(0),
            "ANNEAL_MIRI_RET=INT:u32:99\nANNEAL_MIRI_RET:deadbeef=INT:u32:7\n",
            "",
            Some("deadbeef"),
        );
        assert!(matches!(forged_bare, ObservedOutcome::ToolError { .. }), "{forged_bare:?}");
        let forged_tok = parse_miri_output_with_token(
            Some(0),
            "ANNEAL_MIRI_RET:badtok=INT:u32:99\n",
            "",
            Some("deadbeef"),
        );
        assert!(matches!(forged_tok, ObservedOutcome::ToolError { .. }), "{forged_tok:?}");
        let valid_tok = parse_miri_output_with_token(
            Some(0),
            "ANNEAL_MIRI_RET:deadbeef=INT:u32:7\n",
            "",
            Some("deadbeef"),
        );
        assert_eq!(
            valid_tok,
            ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 7 } }
        );

        let pairs = vec![("c0".to_owned(), "f0".to_owned())];
        let batch_dup_case = parse_miri_batch_stdout_with_token(
            "ANNEAL_MIRI_RUN:deadbeef:c0:f0\nANNEAL_MIRI_CASE:deadbeef:c0:INT:u32:99\n\
             ANNEAL_MIRI_CASE:deadbeef:c0:INT:u32:7\n",
            &pairs,
            Some("deadbeef"),
        );
        assert!(batch_dup_case.is_none());
        let batch_unauth = parse_miri_batch_stdout_with_token(
            "ANNEAL_MIRI_RUN:c0:f0\nANNEAL_MIRI_CASE:deadbeef:c0:INT:u32:7\n\
             ANNEAL_MIRI_RUN:deadbeef:c0:f0\n",
            &pairs,
            Some("deadbeef"),
        );
        assert!(batch_unauth.is_none());
        let batch_ok = parse_miri_batch_stdout_with_token(
            "ANNEAL_MIRI_RUN:deadbeef:c0:f0\nANNEAL_MIRI_CASE:deadbeef:c0:INT:u32:7\n",
            &pairs,
            Some("deadbeef"),
        )
        .expect("tokenized batch output should parse");
        assert_eq!(
            batch_ok["c0"].1.as_deref(),
            Some("ANNEAL_MIRI_RUN:c0:f0|ANNEAL_MIRI_CASE:c0:INT:u32:7")
        );

        let (fuzz_unauth, _) = parse_miri_fuzz_single_output_with_token(
            Some(0),
            "c0",
            "f0",
            "ANNEAL_MIRI_RUN:c0:f0\nANNEAL_MIRI_RUN:deadbeef:c0:f0\n\
             ANNEAL_MIRI_CASE:deadbeef:c0:INT:u32:7\nANNEAL_MIRI_RET:deadbeef=INT:u32:7\n",
            "",
            Some("deadbeef"),
        );
        assert!(matches!(fuzz_unauth, ObservedOutcome::ToolError { .. }), "{fuzz_unauth:?}");
        let (fuzz_ok, fuzz_ev) = parse_miri_fuzz_single_output_with_token(
            Some(0),
            "c0",
            "f0",
            "ANNEAL_MIRI_RUN:deadbeef:c0:f0\nANNEAL_MIRI_CASE:deadbeef:c0:INT:u32:7\n\
             ANNEAL_MIRI_RET:deadbeef=INT:u32:7\n",
            "",
            Some("deadbeef"),
        );
        assert_eq!(
            fuzz_ok,
            ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 7 } }
        );
        assert_eq!(fuzz_ev.as_deref(), Some("ANNEAL_MIRI_RUN:c0:f0|ANNEAL_MIRI_CASE:c0:INT:u32:7"));
    }

    #[test]
    fn parses_miri_ub_abort_unsupported_and_panic() {
        let ub = parse_miri_output(
            Some(1),
            "",
            "error: Undefined Behavior: dividing by zero\n  --> src/ub.rs:5:1\n",
        );
        assert!(matches!(ub, ObservedOutcome::UndefinedBehavior { .. }));

        let abort = parse_miri_output(
            Some(1),
            "",
            "error: abnormal termination: the program aborted execution\n",
        );
        assert!(matches!(abort, ObservedOutcome::AbnormalAbort { .. }));

        let unsup = parse_miri_output(
            Some(1),
            "",
            "error: unsupported operation: calling foreign function\n",
        );
        assert!(matches!(unsup, ObservedOutcome::Unsupported { .. }));

        let panic = parse_miri_output(
            Some(101),
            "",
            "thread 'main' (1) panicked at src/main.rs:2:5:\nexplicit panic\n",
        );
        assert!(
            matches!(panic, ObservedOutcome::Panic { detail } if detail.contains("panicked at "))
        );

        // Genuine UB alongside panic text must not masquerade as benign Panic.
        let ub_with_panic = parse_miri_output(
            Some(101),
            "",
            "panicked at foo\nerror: Undefined Behavior: entering unreachable code\n",
        );
        assert!(matches!(ub_with_panic, ObservedOutcome::UndefinedBehavior { .. }));

        // Compiler/Miri ICEs must never masquerade as target-program panics.
        let ice = parse_miri_output(Some(101), "", "error: internal compiler error: broken MIR\n");
        assert!(matches!(ice, ObservedOutcome::ToolError { .. }));

        let rustc_panic = parse_miri_output(
            Some(101),
            "",
            "thread 'rustc' panicked at compiler/rustc_mir_transform/src/lib.rs:1:1:\nICE\n",
        );
        assert!(matches!(rustc_panic, ObservedOutcome::ToolError { .. }));

        // Authenticated JSON stderr checks: reject plain-text fixture
        // spoofing, mismatched harness spans, and duplicate diagnostics,
        // while classifying genuine `--error-format=json` Miri output and
        // `PANICKED` stdout tokens.
        let tok_panicked = parse_miri_output_with_token(
            Some(0),
            "ANNEAL_MIRI_RET:deadbeef=PANICKED\n",
            "error: Undefined Behavior: arithmetic overflow\n",
            Some("deadbeef"),
        );
        assert!(matches!(tok_panicked, ObservedOutcome::Panic { .. }), "{tok_panicked:?}");

        let forged_plain_ub = parse_miri_output_with_token(
            Some(101),
            "",
            "error: Undefined Behavior: arithmetic overflow\n\
             thread 'main' (1) panicked at src/main.rs:2:5:\nexplicit panic\n",
            Some("deadbeef"),
        );
        assert!(
            matches!(forged_plain_ub, ObservedOutcome::ToolError { .. }),
            "{forged_plain_ub:?}"
        );

        let forged_plain_abort = parse_miri_output_with_token(
            Some(1),
            "",
            "error: Undefined Behavior: forged\n\
             {\"$message_type\":\"diagnostic\",\"message\":\"abnormal termination: the program aborted execution\",\"level\":\"error\",\"spans\":[{\"file_name\":\"/tmp/c/corpus.rs\"}],\"children\":[{\"message\":\"stack backtrace:\\n0: main\\n    at /tmp/h/harness.rs:5:1: 5:10\",\"level\":\"note\",\"spans\":[],\"children\":[],\"rendered\":null}],\"rendered\":\"...\"}\n\
             {\"$message_type\":\"diagnostic\",\"message\":\"aborting due to 1 previous error\",\"level\":\"error\",\"spans\":[],\"children\":[],\"rendered\":\"...\"}\n",
            Some("deadbeef"),
        );
        assert!(
            matches!(forged_plain_abort, ObservedOutcome::ToolError { .. }),
            "{forged_plain_abort:?}"
        );

        let multi_json_err = parse_miri_output_with_token(
            Some(1),
            "",
            "{\"$message_type\":\"diagnostic\",\"message\":\"Undefined Behavior: forged\",\"level\":\"error\",\"spans\":[{\"file_name\":\"/tmp/h/harness.rs\"}],\"children\":[],\"rendered\":\"...\"}\n\
             {\"$message_type\":\"diagnostic\",\"message\":\"abnormal termination: the program aborted execution\",\"level\":\"error\",\"spans\":[{\"file_name\":\"/tmp/c/corpus.rs\"}],\"children\":[{\"message\":\"stack backtrace:\\n0: main\\n    at /tmp/h/harness.rs:5:1: 5:10\",\"level\":\"note\",\"spans\":[],\"children\":[],\"rendered\":null}],\"rendered\":\"...\"}\n\
             {\"$message_type\":\"diagnostic\",\"message\":\"aborting due to 1 previous error\",\"level\":\"error\",\"spans\":[],\"children\":[],\"rendered\":\"...\"}\n",
            Some("deadbeef"),
        );
        assert!(matches!(multi_json_err, ObservedOutcome::ToolError { .. }), "{multi_json_err:?}");

        let wrong_harness_span = parse_miri_output_with_token(
            Some(1),
            "",
            "{\"$message_type\":\"diagnostic\",\"message\":\"Undefined Behavior: entering unreachable code\",\"level\":\"error\",\"spans\":[{\"file_name\":\"/tmp/other/harness.rs\"}],\"children\":[],\"rendered\":\"...\"}\n\
             {\"$message_type\":\"diagnostic\",\"message\":\"aborting due to 1 previous error\",\"level\":\"error\",\"spans\":[],\"children\":[],\"rendered\":\"...\"}\n",
            Some("deadbeef"),
        );
        assert!(
            matches!(wrong_harness_span, ObservedOutcome::ToolError { .. }),
            "{wrong_harness_span:?}"
        );

        // Forged JSON diagnostics emitting empty `spans: []` or only corpus
        // spans without an authenticated harness stack frame must fail closed.
        let forged_empty_spans = parse_miri_output_with_token(
            Some(1),
            "",
            "{\"$message_type\":\"diagnostic\",\"message\":\"Undefined Behavior: forged\",\"level\":\"error\",\"spans\":[],\"children\":[],\"rendered\":\"...\"}\n\
             {\"$message_type\":\"diagnostic\",\"message\":\"aborting due to 1 previous error\",\"level\":\"error\",\"spans\":[],\"children\":[],\"rendered\":\"...\"}\n",
            Some("deadbeef"),
        );
        assert!(
            matches!(forged_empty_spans, ObservedOutcome::ToolError { .. }),
            "{forged_empty_spans:?}"
        );

        let forged_corpus_only = parse_miri_output_with_token(
            Some(1),
            "",
            "{\"$message_type\":\"diagnostic\",\"message\":\"Undefined Behavior: forged\",\"level\":\"error\",\"spans\":[{\"file_name\":\"/tmp/c/corpus.rs\"}],\"children\":[],\"rendered\":\"...\"}\n\
             {\"$message_type\":\"diagnostic\",\"message\":\"aborting due to 1 previous error\",\"level\":\"error\",\"spans\":[],\"children\":[],\"rendered\":\"...\"}\n",
            Some("deadbeef"),
        );
        assert!(
            matches!(forged_corpus_only, ObservedOutcome::ToolError { .. }),
            "{forged_corpus_only:?}"
        );

        let wrong_backtrace_tok = parse_miri_output_with_token(
            Some(1),
            "",
            "{\"$message_type\":\"diagnostic\",\"message\":\"Undefined Behavior: entering unreachable code\",\"level\":\"error\",\"spans\":[{\"file_name\":\"/tmp/c/corpus.rs\"}],\"children\":[{\"message\":\"stack backtrace:\\n0: corpus::f\\n    at /tmp/c/corpus.rs:3:5: 3:20\\n1: main\\n    at /tmp/other/harness.rs:5:1: 5:10\",\"level\":\"note\",\"spans\":[],\"children\":[],\"rendered\":null}],\"rendered\":\"...\"}\n\
             {\"$message_type\":\"diagnostic\",\"message\":\"aborting due to 1 previous error\",\"level\":\"error\",\"spans\":[],\"children\":[],\"rendered\":\"...\"}\n",
            Some("deadbeef"),
        );
        assert!(
            matches!(wrong_backtrace_tok, ObservedOutcome::ToolError { .. }),
            "{wrong_backtrace_tok:?}"
        );

        let valid_json_ub = parse_miri_output_with_token(
            Some(1),
            "",
            "{\"$message_type\":\"diagnostic\",\"message\":\"Undefined Behavior: entering unreachable code\",\"level\":\"error\",\"spans\":[{\"file_name\":\"/tmp/c/corpus.rs\"}],\"children\":[{\"message\":\"stack backtrace:\\n0: corpus::ub\\n    at /tmp/c/corpus.rs:3:5: 3:20\\n1: bridge::call_case_0\\n    at /tmp/b/bridge.rs:4:5: 4:20\\n2: main\\n    at /tmp/h/harness.rs:5:1: 5:10\",\"level\":\"note\",\"spans\":[],\"children\":[],\"rendered\":null}],\"rendered\":\"...\"}\n\
             {\"$message_type\":\"diagnostic\",\"message\":\"aborting due to 1 previous error\",\"level\":\"error\",\"spans\":[],\"children\":[],\"rendered\":\"...\"}\n",
            Some("deadbeef"),
        );
        assert!(
            matches!(
                valid_json_ub,
                ObservedOutcome::UndefinedBehavior { ref detail }
                    if detail == "error: Undefined Behavior: entering unreachable code"
            ),
            "{valid_json_ub:?}"
        );
    }

    #[test]
    fn offline_cargo_config_escapes_vendor_path() {
        let rendered = render_vendored_cargo_config(Path::new(
            "/tmp/rust/lib/rustlib/src/rust/library/vendor",
        ))
        .expect("render vendored Cargo config");
        assert!(rendered.contains("replace-with = \"vendored-sources\""), "{rendered}");
        assert!(
            rendered.contains("directory = \"/tmp/rust/lib/rustlib/src/rust/library/vendor\""),
            "{rendered}"
        );
    }

    #[test]
    fn missing_miri_or_vendor_sysroot_fails_closed() {
        let dir = tempfile::tempdir().unwrap();
        let err = MiriSession::prepare(dir.path(), dir.path()).unwrap_err();
        assert!(err.contains("lacks `bin/miri`"), "{err}");

        let fake_sysroot = dir.path().join("sys");
        fs::create_dir_all(fake_sysroot.join("bin")).unwrap();
        fs::write(fake_sysroot.join("bin/miri"), b"fake").unwrap();
        fs::write(fake_sysroot.join("bin/rustc"), b"fake").unwrap();
        fs::write(fake_sysroot.join("bin/cargo"), b"fake").unwrap();
        let cache = dir.path().join("cache");
        let err_vendor = build_offline_miri_sysroot_in(
            MiriCacheRoot::Path(&cache),
            &fake_sysroot,
            &fake_sysroot.join("bin/miri"),
            &cache.join("miri-out"),
            "expected-tag",
            "expected-sha",
            "",
            None,
            None,
            &cache,
        )
        .unwrap_err();
        assert!(err_vendor.contains("vendored `rust-src` crates"), "{err_vendor}");

        let bogus = dir.path().join("bogus-miri");
        fs::create_dir_all(&bogus).unwrap();
        let err_explicit = MiriSession::prepare_with_env(&fake_sysroot, &cache, |k| {
            (k == "ANNEAL_MIRI_SYSROOT").then(|| OsString::from(&bogus))
        })
        .unwrap_err();
        assert!(err_explicit.contains("does not contain `lib/rustlib`"), "{err_explicit}");

        // Ambient `MIRI_SYSROOT` is ignored rather than substituting a sysroot.
        let ambient_miri = dir.path().join("ambient-miri");
        fs::create_dir_all(ambient_miri.join("lib/rustlib")).unwrap();
        let err_ambient = MiriSession::prepare_with_env(&fake_sysroot, &cache, |k| {
            (k == "MIRI_SYSROOT").then(|| OsString::from(&ambient_miri))
        })
        .unwrap_err();
        assert!(!err_ambient.contains("MIRI_SYSROOT"), "{err_ambient}");

        #[cfg(unix)]
        {
            let sym = dir.path().join("sym-miri-sysroot");
            std::os::unix::fs::symlink(&ambient_miri, &sym).unwrap();
            let err_sym = MiriSession::prepare_with_env(&fake_sysroot, &cache, |k| {
                (k == "ANNEAL_MIRI_SYSROOT").then(|| OsString::from(&sym))
            })
            .unwrap_err();
            assert!(err_sym.contains("must not be a symlink"), "{err_sym}");
        }
    }

    #[test]
    fn rustc_version_tag_requires_metadata_and_harness_emits_typed_ret() {
        let dir = tempfile::tempdir().unwrap();
        let fake_rustc = dir.path().join("rustc");
        fs::write(&fake_rustc, b"fake-rustc").unwrap();

        assert!(parse_rustc_version_tag(&fake_rustc, "rustc 1.98.0-nightly\nhost: x\n").is_err());
        assert!(parse_rustc_version_tag(&fake_rustc, "commit-hash: abcdef123456\n").is_err());
        let tag = parse_rustc_version_tag(
            &fake_rustc,
            "commit-hash: abcdef1234567890\nhost: x86_64-unknown-linux-gnu\n",
        )
        .unwrap();
        assert!(tag.starts_with("abcdef123456-x86_64-unknown-linux-gnu-"), "{tag}");

        let src_file = dir.path().join("f.rs");
        fs::write(&src_file, "#![no_std]\npub fn f() -> u32 { 7 }\n").unwrap();
        let case = LitmusCase {
            id: "c1".to_owned(),
            source_rel: PathBuf::from("f.rs"),
            source_abs: src_file,
            function: "f".to_owned(),
            category: "arith".to_owned(),
            expected: Expectation::Pass,
            miri_ub_contains: None,
            expected_miri: None,
            args: vec![],
            expected_return: Some(MirValue::Int { int_kind: IntKind::U32, bits: 7 }),
            fuel: 100,
        };
        let bridge = generate_miri_bridge(&[&case]).unwrap();
        assert!(bridge.contains("pub fn call_case_0() -> u32"), "{bridge}");
        assert!(bridge.contains("unsafe { corpus::f() }"), "{bridge}");
        let harness = generate_miri_harness(&[&case]).unwrap();
        assert!(harness.contains("bridge::call_case_0"), "{harness}");

        let bad_case = LitmusCase { function: "evil_macro!".to_owned(), ..case };
        assert!(generate_miri_bridge(&[&bad_case]).is_err());
    }

    #[test]
    fn miri_setup_fingerprint_tracks_binaries_and_rust_src_contents() {
        let dir = tempfile::tempdir().unwrap();
        let sys = dir.path().join("sysroot");
        let bin_dir = sys.join("bin");
        let vendor_dir = sys.join("lib/rustlib/src/rust/library/vendor/dep_a");
        let core_dir = sys.join("lib/rustlib/src/rust/library/core/src");
        fs::create_dir_all(&bin_dir).unwrap();
        fs::create_dir_all(&vendor_dir).unwrap();
        fs::create_dir_all(&core_dir).unwrap();

        fs::write(bin_dir.join("rustc"), b"rustc-v1").unwrap();
        fs::write(bin_dir.join("cargo"), b"cargo-v1").unwrap();
        fs::write(bin_dir.join("miri"), b"miri-v1").unwrap();
        fs::write(bin_dir.join("cargo-miri"), b"cargo-miri-v1").unwrap();
        fs::write(vendor_dir.join("lib.rs"), b"pub fn dep() {}\n").unwrap();
        fs::write(core_dir.join("lib.rs"), b"#![no_std]\n").unwrap();

        let ver_tag = "abcdef123456-x86_64-unknown-linux-gnu-001122334455";
        let base_fp = compute_miri_setup_input_sha256(&sys, ver_tag).unwrap();
        assert_eq!(base_fp.len(), 64);

        // Mutating `miri` without changing `rustc` must change the fingerprint.
        fs::write(bin_dir.join("miri"), b"miri-v2").unwrap();
        let miri_fp = compute_miri_setup_input_sha256(&sys, ver_tag).unwrap();
        assert_ne!(miri_fp, base_fp);

        // Mutating `cargo-miri` must change the fingerprint.
        fs::write(bin_dir.join("cargo-miri"), b"cargo-miri-v2").unwrap();
        let cmiri_fp = compute_miri_setup_input_sha256(&sys, ver_tag).unwrap();
        assert_ne!(cmiri_fp, miri_fp);

        // Mutating vendored `rust-src` must change the fingerprint.
        fs::write(vendor_dir.join("lib.rs"), b"pub fn dep() { let _ = 1; }\n").unwrap();
        let src_fp = compute_miri_setup_input_sha256(&sys, ver_tag).unwrap();
        assert_ne!(src_fp, cmiri_fp);

        // Explicit `ANNEAL_MIRI_SYSROOT` must carry a matching ready stamp.
        let explicit_sys = dir.path().join("explicit-miri-sysroot");
        fs::create_dir_all(explicit_sys.join("lib/rustlib")).unwrap();
        let unstamped = verify_explicit_miri_sysroot_stamp(&explicit_sys, ver_tag, &src_fp);
        assert!(unstamped.is_err());

        fs::write(
            explicit_sys.join(".anneal-miri-ready"),
            expected_miri_ready_stamp_for_dir(&explicit_sys, ver_tag, &src_fp),
        )
        .unwrap();
        verify_explicit_miri_sysroot_stamp(&explicit_sys, ver_tag, &src_fp).unwrap();

        // Stale stamp after `miri` or `rust-src` mutation must fail closed.
        assert!(verify_explicit_miri_sysroot_stamp(&explicit_sys, ver_tag, &cmiri_fp).is_err());

        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;

            let fake_rustc = bin_dir.join("rustc");
            fs::write(
                &fake_rustc,
                b"#!/bin/sh\nprintf 'commit-hash: abcdef1234567890\\nhost: x86_64-unknown-linux-gnu\\n'\n",
            )
            .unwrap();
            fs::set_permissions(&fake_rustc, fs::Permissions::from_mode(0o755)).unwrap();

            let real_tag = rustc_version_tag(&sys, "", None, None, dir.path()).unwrap();
            let real_sha = compute_miri_setup_input_sha256(&sys, &real_tag).unwrap();
            let cache = dir.path().join("cache");

            // Stale stamp from pre-executable `rustc` is rejected by
            // `prepare_with_env` before accepting `ANNEAL_MIRI_SYSROOT`.
            let Err(stale_err) = MiriSession::prepare_with_env(&sys, &cache, |k| {
                (k == "ANNEAL_MIRI_SYSROOT").then(|| OsString::from(&explicit_sys))
            }) else {
                panic!("stale explicit stamp must fail");
            };
            assert!(stale_err.contains("setup stamp does not match"), "{stale_err}");

            // Refreshing the stamp to match current inputs succeeds and
            // stages `ANNEAL_MIRI_SYSROOT` into a private immutable directory.
            fs::create_dir_all(explicit_sys.join("lib/rustlib/x86_64/lib")).unwrap();
            let explicit_rlib = explicit_sys.join("lib/rustlib/x86_64/lib/libcore.rlib");
            fs::write(&explicit_rlib, b"trusted-explicit-rlib").unwrap();
            fs::write(
                explicit_sys.join(".anneal-miri-ready"),
                expected_miri_ready_stamp_for_dir(&explicit_sys, &real_tag, &real_sha),
            )
            .unwrap();
            let session = MiriSession::prepare_with_env(&sys, &cache, |k| {
                (k == "ANNEAL_MIRI_SYSROOT").then(|| OsString::from(&explicit_sys))
            })
            .expect("matching explicit stamp must succeed");
            assert!(session._miri_sysroot_staging.is_some());
            assert_ne!(session.miri_sysroot, fs::canonicalize(&explicit_sys).unwrap());
            let staged_explicit_rlib =
                session.miri_sysroot.join("lib/rustlib/x86_64/lib/libcore.rlib");
            assert!(fs::metadata(&staged_explicit_rlib).unwrap().permissions().readonly());
            assert!(
                fs::metadata(session.miri_sysroot.join("lib/rustlib"))
                    .unwrap()
                    .permissions()
                    .readonly()
            );
            // Atomic replacement in the original writable `explicit_sys`
            // after `prepare` cannot alter the staged `session.miri_sysroot`.
            let tampered_tmp = explicit_sys.join("lib/rustlib/x86_64/lib/.libcore.rlib.tmp");
            fs::write(&tampered_tmp, b"poisoned-explicit-rlib").unwrap();
            fs::rename(&tampered_tmp, &explicit_rlib).unwrap();
            assert_eq!(fs::read(&staged_explicit_rlib).unwrap(), b"trusted-explicit-rlib");

            // Symlinked `ANNEAL_MIRI_SYSROOT` inside a mock store allows
            // confined symlinks without copying and rejects outside escapes.
            let canon_dir = dir.path().canonicalize().unwrap();
            let mock_store = canon_dir.join("mock-nix-store");
            let store_real = mock_store.join("1111-real-miri");
            let store_join = mock_store.join("2222-join-miri");
            fs::create_dir_all(store_real.join("lib/rustlib/x86_64/lib")).unwrap();
            fs::create_dir_all(store_join.join("lib")).unwrap();
            fs::write(store_real.join("lib/rustlib/x86_64/lib/libcore.rlib"), b"store-rlib")
                .unwrap();
            fs::write(
                store_real.join(".anneal-miri-ready"),
                expected_miri_ready_stamp_for_dir(&store_real, &real_tag, &real_sha),
            )
            .unwrap();
            use std::os::unix::fs::symlink;
            symlink(store_real.join("lib/rustlib"), store_join.join("lib/rustlib")).unwrap();
            symlink(store_real.join(".anneal-miri-ready"), store_join.join(".anneal-miri-ready"))
                .unwrap();
            let (store_miri, store_miri_stage) = stage_and_verify_miri_sysroot(
                &store_join,
                &canon_dir,
                &mock_store,
                &real_tag,
                &real_sha,
                "ANNEAL_MIRI_SYSROOT",
            )
            .expect("store-contained Miri sysroot must succeed");
            assert!(store_miri_stage.is_none());
            assert_eq!(store_miri, store_join);
            let wrapper_miri = canon_dir.join("wrapper-miri-sysroot");
            symlink(&store_join, &wrapper_miri).unwrap();
            let (wrapper_resolved, wrapper_stage) = stage_and_verify_miri_sysroot(
                &wrapper_miri,
                &canon_dir,
                &mock_store,
                &real_tag,
                &real_sha,
                "ANNEAL_MIRI_SYSROOT",
            )
            .expect("wrapper symlink into store Miri sysroot must succeed");
            assert!(wrapper_stage.is_none());
            assert_eq!(wrapper_resolved, store_join);
            symlink(&explicit_rlib, store_join.join("lib/rustlib/x86_64/lib/escape.rlib")).unwrap();
            let err_store_esc = stage_and_verify_miri_sysroot(
                &store_join,
                &canon_dir,
                &mock_store,
                &real_tag,
                &real_sha,
                "ANNEAL_MIRI_SYSROOT",
            )
            .unwrap_err();
            assert!(err_store_esc.contains("escaped"), "{err_store_esc}");

            // 1. Real leaf under symlinked ancestor must fail closed.
            let real_parent = canon_dir.join("real-miri-parent");
            let sym_parent = canon_dir.join("sym-miri-parent");
            let nested_miri = real_parent.join("miri-leaf");
            fs::create_dir_all(nested_miri.join("lib/rustlib")).unwrap();
            fs::write(
                nested_miri.join(".anneal-miri-ready"),
                expected_miri_ready_stamp_for_dir(&nested_miri, &real_tag, &real_sha),
            )
            .unwrap();
            symlink(&real_parent, &sym_parent).unwrap();
            let err_anc_sym = MiriSession::prepare_with_env(&sys, &cache, |k| {
                (k == "ANNEAL_MIRI_SYSROOT").then(|| OsString::from(sym_parent.join("miri-leaf")))
            })
            .unwrap_err();
            assert!(err_anc_sym.contains("symlink"), "{err_anc_sym}");

            // 2. Parent traversal (`..`) in `ANNEAL_MIRI_SYSROOT` must fail.
            let err_trav = MiriSession::prepare_with_env(&sys, &cache, |k| {
                (k == "ANNEAL_MIRI_SYSROOT")
                    .then(|| OsString::from(real_parent.join("sub/../miri-leaf")))
            })
            .unwrap_err();
            assert!(err_trav.contains(".."), "{err_trav}");

            // 3. Hardlinked `.anneal-miri-ready` stamp must fail closed.
            let evil_outside = canon_dir.join("evil-outside-artifact");
            fs::write(
                &evil_outside,
                expected_miri_ready_stamp_json(&real_tag, &real_sha, BTreeMap::new()).unwrap(),
            )
            .unwrap();
            let hard_stamp_sys = canon_dir.join("hard-stamp-sys");
            fs::create_dir_all(hard_stamp_sys.join("lib/rustlib")).unwrap();
            fs::hard_link(&evil_outside, hard_stamp_sys.join(".anneal-miri-ready")).unwrap();
            let err_hard_stamp = MiriSession::prepare_with_env(&sys, &cache, |k| {
                (k == "ANNEAL_MIRI_SYSROOT").then(|| OsString::from(&hard_stamp_sys))
            })
            .unwrap_err();
            assert!(err_hard_stamp.contains("hardlink"), "{err_hard_stamp}");

            // 4. Symlinked or hardlinked artifacts inside `lib/rustlib` fail.
            let rustlib_target_lib = nested_miri.join("lib/rustlib/x86_64/lib");
            fs::create_dir_all(&rustlib_target_lib).unwrap();
            let sym_rlib = rustlib_target_lib.join("libcore.rlib");
            symlink(&evil_outside, &sym_rlib).unwrap();
            let err_rustlib_sym = MiriSession::prepare_with_env(&sys, &cache, |k| {
                (k == "ANNEAL_MIRI_SYSROOT").then(|| OsString::from(&nested_miri))
            })
            .unwrap_err();
            assert!(err_rustlib_sym.contains("symlink"), "{err_rustlib_sym}");
            fs::remove_file(&sym_rlib).unwrap();

            fs::hard_link(&evil_outside, &sym_rlib).unwrap();
            let err_rustlib_hard = MiriSession::prepare_with_env(&sys, &cache, |k| {
                (k == "ANNEAL_MIRI_SYSROOT").then(|| OsString::from(&nested_miri))
            })
            .unwrap_err();
            assert!(err_rustlib_hard.contains("hardlink"), "{err_rustlib_hard}");
            fs::remove_file(&sym_rlib).unwrap();

            // Symlinked intermediate `lib/rustlib` directory fails closed.
            fs::remove_dir_all(nested_miri.join("lib/rustlib")).unwrap();
            let outside_rustlib = canon_dir.join("outside-rustlib");
            fs::create_dir_all(&outside_rustlib).unwrap();
            symlink(&outside_rustlib, nested_miri.join("lib/rustlib")).unwrap();
            let err_sym_rustlib = MiriSession::prepare_with_env(&sys, &cache, |k| {
                (k == "ANNEAL_MIRI_SYSROOT").then(|| OsString::from(&nested_miri))
            })
            .unwrap_err();
            assert!(err_sym_rustlib.contains("symlink"), "{err_sym_rustlib}");

            // 5. Auto-cached Miri build writes `.anneal-miri-ready` in the
            //    private staging tree before promoting to `target_dir`, so a
            //    stale `.anneal-miri-ready` symlink in cache is never followed
            //    and `write_new_miri_ready_stamp` refuses existing symlinks.
            let auto_cache = canon_dir.join("auto-cache");
            fs::create_dir_all(&auto_cache).unwrap();
            let setup_count = canon_dir.join("miri-setup.count");
            let fake_cargo = bin_dir.join("cargo");
            fs::write(
                &fake_cargo,
                format!(
                    "#!/bin/sh\n\
                     printf x >> '{}'\n\
                     mkdir -p \"$MIRI_SYSROOT/lib/rustlib\"\n\
                     touch \"$MIRI_SYSROOT/lib/rustlib/stamp.rlib\"\n",
                    setup_count.display()
                ),
            )
            .unwrap();
            fs::set_permissions(&fake_cargo, fs::Permissions::from_mode(0o755)).unwrap();

            let auto_sha = compute_miri_setup_input_sha256(&sys, &real_tag).unwrap();
            let auto_id = format!("{real_tag}-{}", &auto_sha[..16]);
            let stale_target = auto_cache.join(format!("miri-sysroot-{auto_id}"));
            fs::create_dir_all(stale_target.join("lib/rustlib")).unwrap();
            let canary = canon_dir.join("canary.txt");
            fs::write(&canary, b"untouched-canary").unwrap();
            symlink(&canary, stale_target.join(".anneal-miri-ready")).unwrap();

            let auto_session = MiriSession::prepare_with_env(&sys, &auto_cache, |_| None)
                .expect("auto-cache rebuild must stage stamp safely before rename");
            assert!(auto_session._miri_sysroot_staging.is_some());
            assert_ne!(auto_session.miri_sysroot, stale_target);
            assert_eq!(fs::read(&canary).unwrap(), b"untouched-canary");
            let auto_stamp_meta =
                fs::symlink_metadata(auto_session.miri_sysroot.join(".anneal-miri-ready")).unwrap();
            assert!(!auto_stamp_meta.file_type().is_symlink());
            assert!(auto_stamp_meta.permissions().readonly());
            let stamp: MiriSysrootStamp = serde_json::from_str(
                &fs::read_to_string(auto_session.miri_sysroot.join(".anneal-miri-ready")).unwrap(),
            )
            .unwrap();
            assert_eq!(stamp.version, MIRI_SYSROOT_STAMP_VERSION);
            assert_eq!(stamp.ver_tag, real_tag);
            assert_eq!(stamp.setup_sha, auto_sha);
            assert!(stamp.files.contains_key("stamp.rlib"));
            assert_eq!(fs::read(&setup_count).unwrap().len(), 1);
            // Valid un-tampered cached Miri sysroot hits without re-running
            // setup.
            let auto_hit = MiriSession::prepare_with_env(&sys, &auto_cache, |_| None)
                .expect("verified staged stamp must hit cache on clean second call");
            assert!(auto_hit._miri_sysroot_staging.is_some());
            assert_ne!(auto_hit.miri_sysroot, stale_target);
            assert_eq!(fs::read(&setup_count).unwrap().len(), 1);
            // Poisoning or tampering `.rlib` inside the writable cache after
            // setup cannot mutate staged `auto_session.miri_sysroot` and
            // invalidates the authenticated v3 manifest so the next `prepare`
            // rejects and rebuilds.
            let cached_rlib = stale_target.join("lib/rustlib/stamp.rlib");
            let staged_auto_rlib = auto_session.miri_sysroot.join("lib/rustlib/stamp.rlib");
            assert_eq!(fs::read(&staged_auto_rlib).unwrap(), b"");
            let cache_tmp = stale_target.join("lib/rustlib/.stamp.rlib.tmp");
            fs::write(&cache_tmp, b"poisoned-cache-rlib").unwrap();
            fs::rename(&cache_tmp, &cached_rlib).unwrap();
            assert_eq!(fs::read(&staged_auto_rlib).unwrap(), b"");

            let rebuilt_after_poison = MiriSession::prepare_with_env(&sys, &auto_cache, |_| None)
                .expect("tampered cached Miri sysroot must rebuild cleanly");
            assert!(rebuilt_after_poison._miri_sysroot_staging.is_some());
            assert_ne!(rebuilt_after_poison.miri_sysroot, stale_target);
            assert_eq!(fs::read(&setup_count).unwrap().len(), 2);
            assert_eq!(
                fs::read(rebuilt_after_poison.miri_sysroot.join("lib/rustlib/stamp.rlib")).unwrap(),
                b""
            );

            let clobber_dir = canon_dir.join("clobber-staging");
            fs::create_dir_all(&clobber_dir).unwrap();
            symlink(&canary, clobber_dir.join(".anneal-miri-ready")).unwrap();
            assert!(write_new_miri_ready_stamp(&clobber_dir, "stamp").is_err());
            assert_eq!(fs::read(&canary).unwrap(), b"untouched-canary");
        }

        // Missing `cargo-miri` fails closed.
        fs::remove_file(bin_dir.join("cargo-miri")).unwrap();
        assert!(compute_miri_setup_input_sha256(&sys, ver_tag).is_err());
    }

    #[cfg(unix)]
    #[test]
    fn miri_batch_global_failures_do_not_bisect() {
        use std::os::unix::process::ExitStatusExt;

        let exit_sig9 = std::process::ExitStatus::from_raw(9);
        let exit_1 = std::process::ExitStatus::from_raw(1 << 8);

        let timed_out = classify_miri_batch_failure(&Termination::TimedOut(exit_sig9), "stalled");
        assert!(
            matches!(timed_out, Some(MiriBatchFailure::Global(ref d)) if d.contains("timed out"))
        );

        let launch_err =
            classify_miri_batch_failure(&Termination::LaunchFailed("ENOENT".to_owned()), "");
        assert!(matches!(
            launch_err,
            Some(MiriBatchFailure::Global(ref d)) if d.contains("launch failed")
        ));

        let ice_err = classify_miri_batch_failure(
            &Termination::Exited(exit_1),
            "error: internal compiler error: broken MIR\n",
        );
        assert!(matches!(
            ice_err,
            Some(MiriBatchFailure::Global(ref d)) if d.contains("compiler/sysroot failure")
        ));

        let rustc_panic_err = classify_miri_batch_failure(
            &Termination::Exited(exit_1),
            "thread 'rustc' panicked at compiler/rustc_mir_transform/src/lib.rs:1:1:\nice\n",
        );
        assert!(matches!(
            rustc_panic_err,
            Some(MiriBatchFailure::Global(ref d)) if d.contains("compiler/sysroot failure")
        ));

        let sysroot_err = classify_miri_batch_failure(
            &Termination::Exited(exit_1),
            "error[E0463]: can't find crate for `core`\n",
        );
        assert!(matches!(
            sysroot_err,
            Some(MiriBatchFailure::Global(ref d)) if d.contains("compiler/sysroot failure")
        ));

        // Ordinary per-function compile diagnostics classify as
        // `CompileDiagnostic`, NOT `Global`, so subset-crate bisection
        // isolates only the broken generated function.
        let type_err = classify_miri_batch_failure(
            &Termination::Exited(exit_1),
            "error[E0308]: mismatched types\n  --> harness.rs:10:5\n",
        );
        assert!(matches!(
            type_err,
            Some(MiriBatchFailure::CompileDiagnostic(ref d))
                if d.contains("error[E0308]: mismatched types")
        ));

        let syntax_err = classify_miri_batch_failure(
            &Termination::Exited(exit_1),
            "error: expected `;`, found `}`\n",
        );
        assert!(matches!(
            syntax_err,
            Some(MiriBatchFailure::CompileDiagnostic(ref d)) if d.contains("compile failure")
        ));

        // Case-local UB, abort, unsupported, and guest panics remain bisectable
        // (`None`) on the shared harness.
        assert!(
            classify_miri_batch_failure(
                &Termination::Exited(exit_1),
                "error: Undefined Behavior: dividing by zero\n",
            )
            .is_none()
        );
        assert!(
            classify_miri_batch_failure(
                &Termination::Exited(exit_1),
                "error: abnormal termination: the program aborted execution\n",
            )
            .is_none()
        );
        assert!(
            classify_miri_batch_failure(
                &Termination::Exited(exit_1),
                "error: unsupported operation: foreign function not supported\n",
            )
            .is_none()
        );
        assert!(
            classify_miri_batch_failure(
                &Termination::Exited(exit_1),
                "thread 'main' panicked at library/core/src/panicking.rs:1:1:\nexplicit panic\n",
            )
            .is_none()
        );

        // End-to-end: genuine global ICE fails the whole batch in 1 invocation
        // without bisecting 2*N - 1 times, and string-only legacy API without
        // `&[&GenProgram]` stops on CompileDiagnostic in 1 call too.
        let dir = tempfile::tempdir().unwrap();
        let fake_miri = dir.path().join("fake-miri");
        let count_file = dir.path().join("invocations.log");
        let harness = dir.path().join("harness.rs");
        let fake_sys = dir.path().join("sysroot");
        fs::create_dir_all(&fake_sys).unwrap();
        fs::write(&harness, "fn main() {}\n").unwrap();
        fs::write(
            &fake_miri,
            format!(
                "#!/bin/sh\necho x >> '{}'\necho 'error: internal compiler error: broken MIR' >&2\nexit 1\n",
                count_file.display()
            ),
        )
        .unwrap();
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(&fake_miri, fs::Permissions::from_mode(0o755)).unwrap();

        let case_pairs: Vec<(String, String)> =
            (0..8).map(|i| (format!("c{i}"), format!("f{i}"))).collect();
        let bin_path_env = OsString::from("/bin");
        let out = run_miri_chunk_with_bisection(
            &fake_miri,
            None,
            &fake_sys,
            MiriChildEnv { ld_path: "", path_env: &bin_path_env, tmpdir: None },
            &harness,
            None,
            &case_pairs,
            None,
            false,
            None,
            None,
        );
        let calls = fs::read_to_string(&count_file).unwrap().lines().count();
        assert_eq!(calls, 1, "expected 1 global Miri invocation, saw {calls}");
        assert_eq!(out.len(), 8);
        assert!(out.values().all(|(o, _)| matches!(
            o,
            ObservedOutcome::ToolError { detail } if detail.contains("internal compiler error")
        )));
    }

    #[cfg(unix)]
    #[test]
    fn miri_compile_diagnostic_bisects_subset_harnesses_to_isolate_bad_program() {
        use std::os::unix::fs::PermissionsExt;

        use crate::{
            r#gen::{GenCategory, GenExpr, GenType},
            verdict::IntKind,
        };

        let dir = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(dir.path()).unwrap();
        let fake_sys = base.join("sysroot");
        fs::create_dir_all(fake_sys.join("bin")).unwrap();
        fs::create_dir_all(fake_sys.join("lib")).unwrap();
        let fake_rustc = fake_sys.join("bin/rustc");
        let fake_miri = fake_sys.join("bin/miri");
        let miri_target = base.join("miri-target");
        fs::create_dir_all(miri_target.join("lib/rustlib")).unwrap();

        // Fake `rustc` fails with ordinary `error[E0308]` iff the compiled
        // `corpus.rs` crate includes `fn fuzz_fn_5(`, triggering subset
        // bisection across clean neighbors.
        fs::write(
            &fake_rustc,
            "#!/bin/sh\nset -eu\n\
             out=\"\"\n\
             src=\"\"\n\
             while [ \"$#\" -gt 0 ]; do\n\
               case \"$1\" in\n\
                 -o) out=\"$2\"; shift 2 ;;\n\
                 *.rs) src=\"$1\"; shift ;;\n\
                 *) shift ;;\n\
               esac\n\
             done\n\
             if [ -n \"$src\" ] && grep -q 'fn fuzz_fn_5(' \"$src\"; then\n\
               echo 'error[E0308]: mismatched types in fuzz_fn_5' >&2\n\
               exit 1\n\
             fi\n\
             if [ -n \"$out\" ]; then\n\
               : > \"$out\"\n\
             fi\n",
        )
        .unwrap();
        fs::set_permissions(&fake_rustc, fs::Permissions::from_mode(0o755)).unwrap();

        // Fake Miri driver evaluates clean `__BATCH__` or single-selector calls
        // on isolated `h/harness.rs`.
        fs::write(
            &fake_miri,
            "#!/bin/sh\nset -eu\n\
             harness=\"\"\n\
             while [ \"$#\" -gt 0 ]; do\n\
               case \"$1\" in\n\
                 --target|--sysroot|-C|--edition|--crate-name|--extern|-L) shift ;;\n\
                 --edition=*|-Zmiri-*) ;;\n\
                 --) shift; break ;;\n\
                 *.rs) harness=\"$1\" ;;\n\
               esac\n\
               shift\n\
             done\n\
             tok=$(sed -n 's/.*ANNEAL_MIRI_RUN:\\([0-9a-f]\\{32\\}\\):.*/\\1/p' \"$harness\" | head -n 1 || true)\n\
             run_pfx='ANNEAL_MIRI_RUN:'\n\
             case_pfx='ANNEAL_MIRI_CASE:'\n\
             ret_pfx='ANNEAL_MIRI_RET='\n\
             if [ -n \"$tok\" ]; then\n\
               run_pfx=\"ANNEAL_MIRI_RUN:${tok}:\"\n\
               case_pfx=\"ANNEAL_MIRI_CASE:${tok}:\"\n\
               ret_pfx=\"ANNEAL_MIRI_RET:${tok}=\"\n\
             fi\n\
             if [ \"${1:-}\" = \"__BATCH__\" ]; then\n\
               shift\n\
               for cid in \"$@\"; do\n\
                 idx=\"${cid#case_}\"\n\
                 printf '%s%s:fuzz_fn_%s\\n' \"$run_pfx\" \"$cid\" \"$idx\"\n\
                 printf '%s%s:INT:u32:7\\n' \"$case_pfx\" \"$cid\"\n\
               done\n\
             else\n\
               cid=\"${1:-}\"\n\
               idx=\"${cid#case_}\"\n\
               printf '%s%s:fuzz_fn_%s\\n' \"$run_pfx\" \"$cid\" \"$idx\"\n\
               printf '%s%s:INT:u32:7\\n' \"$case_pfx\" \"$cid\"\n\
               printf '%sINT:u32:7\\n' \"$ret_pfx\"\n\
             fi\n",
        )
        .unwrap();
        fs::set_permissions(&fake_miri, fs::Permissions::from_mode(0o755)).unwrap();

        let session = MiriSession {
            miri_bin: fake_miri,
            rust_sysroot: fake_sys,
            miri_sysroot: miri_target,
            ld_library_path: String::new(),
            validated_tmpdir: None,
            _sysroot_staging: None,
            _miri_sysroot_staging: None,
        };

        // Include both clean-batch (`case_0..4`, bad `case_5`, `case_6`) AND an
        // isolated case (`case_7`, `TargetedUbProbe`) to prove neither clean
        // neighbors nor isolated probes get poisoned by `case_5`.
        let programs: Vec<GenProgram> = (0..8)
            .map(|i| GenProgram {
                case_id: format!("case_{i}"),
                fn_name: format!("fuzz_fn_{i}"),
                master_seed: 2,
                case_index: i,
                category: if i == 7 {
                    GenCategory::TargetedUbProbe
                } else {
                    GenCategory::SafeAdmitted
                },
                is_unsafe: false,
                params: vec![],
                locals: vec![],
                body: vec![],
                ret_ty: GenType::Int(IntKind::U32),
                ret_expr: GenExpr::Lit(MirValue::Int { int_kind: IntKind::U32, bits: 7 }),
                fuel: 200,
            })
            .collect();
        let prog_refs: Vec<&GenProgram> = programs.iter().collect();
        let cases: Vec<FuzzExecCase> = programs
            .iter()
            .map(|p| FuzzExecCase {
                case_id: p.case_id.clone(),
                fn_name: p.fn_name.clone(),
                args: vec![],
                ret_shape: p.ret_shape(),
                fuel: p.fuel,
                expected_clean_batch: p.category.counts_toward_admission(),
            })
            .collect();
        let full_src = render_batch_crate(&prog_refs);
        let out = session
            .run_fuzz_crate_with_evidence_until(&full_src, &prog_refs, &cases, None)
            .expect("Miri compile-diagnostic subset bisection");

        assert_eq!(out.len(), 8);
        for i in 0..8 {
            let cid = format!("case_{i}");
            if i == 5 {
                assert!(
                    matches!(&out[&cid].0, ObservedOutcome::ToolError { detail } if detail.contains("error[E0308]")),
                    "expected isolated ToolError for case_5, got {:?}",
                    out[&cid]
                );
            } else {
                assert_eq!(
                    out[&cid].0,
                    ObservedOutcome::Returned {
                        value: MirValue::Int { int_kind: IntKind::U32, bits: 7 }
                    },
                    "valid neighbor case_{i} must not be poisoned"
                );
            }
        }

        // Stalled single-case `invoke_single_miri_until` error must return
        // immediately without invoking Miri a second time.
        let count_file = base.join("timeout_count.txt");
        let stall_miri = base.join("stall-miri");
        fs::write(
            &stall_miri,
            format!("#!/bin/sh\necho x >> '{}'\nsleep 2\n", count_file.display()),
        )
        .unwrap();
        fs::set_permissions(&stall_miri, fs::Permissions::from_mode(0o755)).unwrap();
        let harness = base.join("single_stall.rs");
        fs::write(&harness, "fn main() {}\n").unwrap();
        let stall_path_env = OsString::from("/bin");
        let (err_out, err_ev) = run_single_miri_fuzz_with_fallback(
            &stall_miri,
            None,
            &session.miri_sysroot,
            MiriChildEnv { ld_path: "", path_env: &stall_path_env, tmpdir: None },
            &harness,
            None,
            ("case_stall", "fuzz_stall"),
            None,
            None,
            Some(Instant::now() + Duration::from_millis(80)),
        );
        assert!(matches!(err_out, ObservedOutcome::ToolError { .. }), "{err_out:?}");
        assert!(err_ev.is_none());
        assert_eq!(fs::read_to_string(&count_file).unwrap().lines().count(), 1);
    }

    #[cfg(unix)]
    #[test]
    fn miri_drops_ambient_ld_library_path_and_rejects_symlinked_lib() {
        use std::os::unix::fs::{PermissionsExt, symlink};

        let dir = tempfile::tempdir().unwrap();
        let base = dir.path().canonicalize().unwrap();
        let sys = base.join("sysroot");
        let bin_dir = sys.join("bin");
        let lib_dir = sys.join("lib");
        let vendor = sys.join("lib/rustlib/src/rust/library/vendor");
        fs::create_dir_all(&bin_dir).unwrap();
        fs::create_dir_all(&vendor).unwrap();

        let ver_ld_log = base.join("rustc_ver_ld.log");
        let ver_path_log = base.join("rustc_ver_path.log");
        let compile_ld_log = base.join("rustc_compile_ld.log");
        let compile_path_log = base.join("rustc_compile_path.log");
        let setup_ld_log = base.join("setup_ld.log");
        let setup_path_log = base.join("setup_path.log");
        let run_ld_log = base.join("miri_run_ld.log");
        let run_path_log = base.join("miri_run_path.log");
        let miri_sys = base.join("explicit_miri_sysroot");
        fs::create_dir_all(miri_sys.join("lib/rustlib")).unwrap();

        let poisoned_bin = base.join("poisoned-ambient-bin");
        fs::create_dir_all(&poisoned_bin).unwrap();
        let direct_path = build_child_path(
            &bin_dir,
            Some(OsStr::new(&format!("{}:./relative-bin:/usr/bin", poisoned_bin.display()))),
        )
        .expect("build sanitized Miri PATH");
        let direct_entries: Vec<PathBuf> = env::split_paths(&direct_path).collect();
        assert_eq!(direct_entries.first(), Some(&bin_dir), "{direct_entries:?}");
        assert!(
            !direct_entries.iter().any(|p| p == &poisoned_bin || !p.is_absolute()),
            "sanitized PATH kept untrusted entries: {direct_entries:?}"
        );

        let fake_rustc = bin_dir.join("rustc");
        fs::write(
            &fake_rustc,
            format!(
                "#!/bin/sh\nset -eu\n\
                 is_ver=0\n\
                 out=\"\"\n\
                 while [ \"$#\" -gt 0 ]; do\n\
                   case \"$1\" in\n\
                     -vV) is_ver=1; shift ;;\n\
                     -o) out=\"$2\"; shift 2 ;;\n\
                     *) shift ;;\n\
                   esac\n\
                 done\n\
                 if [ \"$is_ver\" = 1 ]; then\n\
                   printf '%s\\n' \"${{LD_LIBRARY_PATH:-}}\" > '{}'\n\
                   printf '%s\\n' \"${{PATH:-}}\" > '{}'\n\
                   printf 'rustc 1.98.0-nightly\\ncommit-hash: abcdef123456\\nhost: x86_64-unknown-linux-gnu\\n'\n\
                 else\n\
                   printf '%s\\n' \"${{LD_LIBRARY_PATH:-}}\" >> '{}'\n\
                   printf '%s\\n' \"${{PATH:-}}\" >> '{}'\n\
                   if [ -n \"$out\" ]; then : > \"$out\"; fi\n\
                 fi\n",
                ver_ld_log.display(),
                ver_path_log.display(),
                compile_ld_log.display(),
                compile_path_log.display(),
            ),
        )
        .unwrap();
        fs::set_permissions(&fake_rustc, fs::Permissions::from_mode(0o755)).unwrap();

        let fake_cargo = bin_dir.join("cargo");
        fs::write(
            &fake_cargo,
            format!(
                "#!/bin/sh\nset -eu\n\
                 printf '%s\\n' \"${{LD_LIBRARY_PATH:-}}\" > '{}'\n\
                 printf '%s\\n' \"${{PATH:-}}\" > '{}'\n\
                 mkdir -p \"$MIRI_SYSROOT/lib/rustlib\"\n",
                setup_ld_log.display(),
                setup_path_log.display()
            ),
        )
        .unwrap();
        fs::set_permissions(&fake_cargo, fs::Permissions::from_mode(0o755)).unwrap();

        let fake_cargo_miri = bin_dir.join("cargo-miri");
        fs::write(&fake_cargo_miri, "#!/bin/sh\nexit 0\n").unwrap();
        fs::set_permissions(&fake_cargo_miri, fs::Permissions::from_mode(0o755)).unwrap();

        let fake_miri = bin_dir.join("miri");
        fs::write(
            &fake_miri,
            format!(
                "#!/bin/sh\nset -eu\n\
                 printf '%s\\n' \"${{LD_LIBRARY_PATH:-}}\" >> '{}'\n\
                 printf '%s\\n' \"${{PATH:-}}\" >> '{}'\n\
                 harness=\"\"\n\
                 last=\"\"\n\
                 while [ \"$#\" -gt 0 ]; do\n\
                   last=\"$1\"\n\
                   case \"$1\" in\n\
                     --target|--sysroot|-C|--edition|--crate-name|--extern|-L) shift ;;\n\
                     *.rs) harness=\"$1\" ;;\n\
                   esac\n\
                   shift\n\
                 done\n\
                 tok=\"\"\n\
                 if [ -n \"$harness\" ] && [ -f \"$harness\" ]; then\n\
                   tok=$(sed -n 's/.*ANNEAL_MIRI_RUN:\\([0-9a-f]\\{{32\\}}\\):.*/\\1/p' \"$harness\" | head -n 1 || true)\n\
                   if [ -z \"$tok\" ]; then\n\
                     tok=$(sed -n 's/.*ANNEAL_MIRI_RET:\\([0-9a-f]\\{{32\\}}\\)=.*/\\1/p' \"$harness\" | head -n 1 || true)\n\
                   fi\n\
                 fi\n\
                 run_pfx='ANNEAL_MIRI_RUN:'\n\
                 case_pfx='ANNEAL_MIRI_CASE:'\n\
                 ret_pfx='ANNEAL_MIRI_RET='\n\
                 if [ -n \"$tok\" ]; then\n\
                   run_pfx=\"ANNEAL_MIRI_RUN:${{tok}}:\"\n\
                   case_pfx=\"ANNEAL_MIRI_CASE:${{tok}}:\"\n\
                   ret_pfx=\"ANNEAL_MIRI_RET:${{tok}}=\"\n\
                 fi\n\
                 if [ \"$last\" = \"c_ok\" ]; then\n\
                   printf '%sc_ok:f_ok\\n' \"$run_pfx\"\n\
                   printf '%sc_ok:INT:u32:7\\n' \"$case_pfx\"\n\
                   printf '%sINT:u32:7\\n' \"$ret_pfx\"\n\
                 else\n\
                   printf '%sc_stage1:f_s1\\n%sINT:u32:7\\n' \"$run_pfx\" \"$ret_pfx\"\n\
                 fi\n",
                run_ld_log.display(),
                run_path_log.display()
            ),
        )
        .unwrap();
        fs::set_permissions(&fake_miri, fs::Permissions::from_mode(0o755)).unwrap();

        let cache = base.join("cache");
        let poisoned_path_env = format!("{}:./rel:/usr/bin", poisoned_bin.display());
        let session = MiriSession::prepare_with_env(&sys, &cache, |k| match k {
            "LD_LIBRARY_PATH" => Some(OsString::from("/tmp/poisoned-ambient-lib")),
            "PATH" => Some(OsString::from(&poisoned_path_env)),
            _ => None,
        })
        .expect("prepare offline Miri session with clean validated LD_LIBRARY_PATH and PATH");
        assert!(session._sysroot_staging.is_some());
        assert_ne!(session.rust_sysroot, sys);
        let staged_bin_dir = session.rust_sysroot.join("bin");
        let expected_lib = session.rust_sysroot.join("lib").to_string_lossy().into_owned();
        assert_eq!(session.ld_library_path, expected_lib);
        assert_eq!(fs::read_to_string(&ver_ld_log).unwrap().trim(), expected_lib);
        assert_eq!(fs::read_to_string(&setup_ld_log).unwrap().trim(), expected_lib);
        for path_log in [&ver_path_log, &setup_path_log] {
            let logged = fs::read_to_string(path_log).unwrap();
            let entries: Vec<PathBuf> = env::split_paths(logged.trim()).collect();
            assert_eq!(entries.first(), Some(&staged_bin_dir), "{entries:?}");
            assert!(!logged.contains("poisoned-ambient-bin"), "{logged}");
            assert!(!entries.iter().any(|p| !p.is_absolute()), "{entries:?}");
        }

        let fuzz_case = FuzzExecCase {
            case_id: "c_ok".to_owned(),
            fn_name: "f_ok".to_owned(),
            args: vec![],
            ret_shape: MirValue::Int { int_kind: IntKind::U32, bits: 0 },
            fuel: 200,
            expected_clean_batch: true,
        };
        let fuzz_out = session
            .run_fuzz_batch_with_evidence_until(
                "#![no_std]\npub fn f_ok() -> u32 { 7 }\n",
                &[fuzz_case],
                None,
            )
            .expect("Stage-2 Miri batch run");
        assert_eq!(
            fuzz_out["c_ok"].0,
            ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 7 } }
        );

        let litmus_src = base.join("litmus.rs");
        fs::write(&litmus_src, "pub fn f_s1() -> u32 { 7 }\n").unwrap();
        let stage1_case = LitmusCase {
            id: "c_stage1".to_owned(),
            source_rel: PathBuf::from("litmus.rs"),
            source_abs: litmus_src,
            function: "f_s1".to_owned(),
            category: "pass".to_owned(),
            expected: Expectation::Pass,
            miri_ub_contains: None,
            expected_miri: None,
            args: vec![],
            expected_return: Some(MirValue::Int { int_kind: IntKind::U32, bits: 7 }),
            fuel: 500,
        };
        let s1_out = session.run_cases(&[stage1_case]).expect("Stage-1 Miri run");
        assert_eq!(
            s1_out["c_stage1"],
            ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 7 } }
        );

        let compile_lds: Vec<String> =
            fs::read_to_string(&compile_ld_log).unwrap().lines().map(ToOwned::to_owned).collect();
        assert_eq!(compile_lds.len(), 4, "{compile_lds:?}");
        for ld in compile_lds {
            assert_eq!(ld, expected_lib);
            assert!(!ld.contains("poisoned"));
        }
        let recorded_lds: Vec<String> =
            fs::read_to_string(&run_ld_log).unwrap().lines().map(ToOwned::to_owned).collect();
        assert_eq!(recorded_lds.len(), 2, "{recorded_lds:?}");
        for ld in recorded_lds {
            assert_eq!(ld, expected_lib);
            assert!(!ld.contains("poisoned"));
        }
        let mut recorded_paths: Vec<String> =
            fs::read_to_string(&compile_path_log).unwrap().lines().map(ToOwned::to_owned).collect();
        recorded_paths
            .extend(fs::read_to_string(&run_path_log).unwrap().lines().map(ToOwned::to_owned));
        assert_eq!(recorded_paths.len(), 6, "{recorded_paths:?}");
        for recorded in recorded_paths {
            let entries: Vec<PathBuf> = env::split_paths(&recorded).collect();
            assert_eq!(entries.first(), Some(&staged_bin_dir), "{entries:?}");
            assert!(!entries.iter().any(|p| !p.is_absolute()), "{entries:?}");
            for tail in &entries[1..] {
                assert!(
                    TRUSTED_CHILD_PATH_DIRS.iter().any(|d| tail == Path::new(d))
                        || tail.starts_with(STORE_PREFIX),
                    "unexpected non-trusted child PATH entry in Miri run: {tail:?} ({entries:?})"
                );
            }
        }

        // Symlinked `rust_sysroot/lib` fails closed before `rustc` or Miri.
        let bad_sys = base.join("bad_sys");
        fs::create_dir_all(bad_sys.join("bin")).unwrap();
        fs::copy(&fake_miri, bad_sys.join("bin/miri")).unwrap();
        fs::copy(&fake_rustc, bad_sys.join("bin/rustc")).unwrap();
        symlink(&lib_dir, bad_sys.join("lib")).unwrap();
        let sym_err = MiriSession::prepare_with_env(&bad_sys, &cache, |_| None).unwrap_err();
        assert!(sym_err.contains("symlink"), "{sym_err}");

        // Relative TMPDIR anchors cleanly against `caller_cwd` before
        // running rustc -vV, cargo compiles, or miri; traversal/symlink/missing
        // TMPDIR fails closed before invoking rustc.
        let caller_cwd = base.join("caller");
        let rel_tmp = caller_cwd.join("tmp");
        fs::create_dir_all(&rel_tmp).unwrap();
        let miri_tmp_log = base.join("miri-run-tmps.txt");
        let miri_probe_tmp_log = base.join("miri-probe-tmps.txt");
        fs::write(
            &fake_rustc,
            format!(
                "#!/bin/sh\nset -eu\n\
                 if [ \"${{1:-}}\" = \"-vV\" ]; then\n\
                   printf '%s\\n' \"${{TMPDIR:-}}\" >> '{}'\n\
                   printf 'commit-hash: abcdef1234567890\\nhost: x86_64-unknown-linux-gnu\\n'\n\
                   exit 0\n\
                 fi\n\
                 printf '%s\\n' \"${{TMPDIR:-}}\" >> '{}'\n\
                 out=\"\"\n\
                 while [ \"$#\" -gt 0 ]; do\n\
                   if [ \"$1\" = \"-o\" ]; then shift; out=\"${{1:-}}\"; fi\n\
                   shift\n\
                 done\n\
                 : > \"$out\"\n",
                miri_probe_tmp_log.display(),
                miri_tmp_log.display(),
            ),
        )
        .unwrap();
        fs::set_permissions(&fake_rustc, fs::Permissions::from_mode(0o755)).unwrap();
        let run_tmp_log = base.join("miri-exec-tmps.txt");
        fs::write(
            &fake_miri,
            format!(
                "#!/bin/sh\nset -eu\n\
                 printf '%s\\n' \"${{TMPDIR:-}}\" >> '{}'\n\
                 harness=\"\"\n\
                 while [ \"$#\" -gt 0 ]; do\n\
                   case \"$1\" in --) shift; break ;; *) harness=\"$1\" ;; esac\n\
                   shift\n\
                 done\n\
                 tok=$(grep -oE 'ANNEAL_MIRI_RUN:[0-9a-f]+:' \"$harness\" | head -n1 | cut -d: -f2)\n\
                 is_batch=0\n\
                 if [ \"${{1:-}}\" = \"__BATCH__\" ]; then is_batch=1; shift; fi\n\
                 for cid in \"$@\"; do\n\
                   printf 'ANNEAL_MIRI_RUN:%s:%s:f_ok\\nANNEAL_MIRI_CASE:%s:%s:INT:u32:7\\n' \"$tok\" \"$cid\" \"$tok\" \"$cid\"\n\
                   if [ \"$is_batch\" -eq 0 ]; then\n\
                     printf 'ANNEAL_MIRI_RET:%s=INT:u32:7\\n' \"$tok\"\n\
                   fi\n\
                 done\n",
                run_tmp_log.display(),
            ),
        )
        .unwrap();
        fs::set_permissions(&fake_miri, fs::Permissions::from_mode(0o755)).unwrap();
        let miri_ready_tag = rustc_version_tag(&sys, "", None, None, &base).unwrap();
        let miri_ready_sha = compute_miri_setup_input_sha256(&sys, &miri_ready_tag).unwrap();
        let explicit_miri = base.join("explicit-miri-tmp");
        fs::create_dir_all(explicit_miri.join("lib/rustlib")).unwrap();
        fs::write(
            explicit_miri.join(".anneal-miri-ready"),
            expected_miri_ready_stamp_for_dir(&explicit_miri, &miri_ready_tag, &miri_ready_sha),
        )
        .unwrap();
        let _ = fs::remove_file(&miri_probe_tmp_log);
        let anchored_session =
            MiriSession::prepare_with_env_at(&sys, &cache, &caller_cwd, |k| match k {
                "ANNEAL_MIRI_SYSROOT" => Some(explicit_miri.as_os_str().to_os_string()),
                "TMPDIR" => Some(OsString::from("tmp")),
                _ => None,
            })
            .expect("relative existing TMPDIR must anchor cleanly for MiriSession");
        assert_eq!(anchored_session.validated_tmpdir.as_deref(), Some(rel_tmp.as_path()));
        assert_eq!(
            fs::read_to_string(&miri_probe_tmp_log).unwrap().trim(),
            rel_tmp.display().to_string()
        );
        let fuzz_case_tmp = FuzzExecCase {
            case_id: "c_tmp".to_owned(),
            fn_name: "f_ok".to_owned(),
            args: vec![],
            ret_shape: MirValue::Int { int_kind: IntKind::U32, bits: 0 },
            fuel: 100,
            expected_clean_batch: true,
        };
        let tmp_out = anchored_session
            .run_fuzz_batch_with_evidence_until(
                "#![no_std]\npub fn f_ok() -> u32 { 7 }\n",
                &[fuzz_case_tmp],
                None,
            )
            .expect("Miri run with anchored TMPDIR");
        assert_eq!(
            tmp_out["c_tmp"].0,
            ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 7 } }
        );
        assert!(
            fs::read_to_string(&miri_tmp_log)
                .unwrap()
                .lines()
                .all(|l| l == rel_tmp.display().to_string())
        );
        assert_eq!(fs::read_to_string(&run_tmp_log).unwrap().trim(), rel_tmp.display().to_string());

        let _ = fs::remove_file(&miri_probe_tmp_log);
        let sym_tmp = caller_cwd.join("sym-tmp");
        symlink(&rel_tmp, &sym_tmp).unwrap();
        for bad_tmp in [OsStr::new("../outside"), sym_tmp.as_os_str(), OsStr::new("missing-tmp")] {
            let err = MiriSession::prepare_with_env_at(&sys, &cache, &caller_cwd, |k| {
                (k == "TMPDIR").then(|| bad_tmp.to_os_string())
            })
            .unwrap_err();
            assert!(err.contains("TMPDIR"), "bad TMPDIR {:?} -> {err}", bad_tmp);
            assert!(!miri_probe_tmp_log.exists(), "rustc -vV ran with bad TMPDIR {:?}", bad_tmp);
        }
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn miri_pinned_cache_dir_resists_parent_rename_and_traps_substitutions() {
        let tmp = tempfile::tempdir().unwrap();
        let base = fs::canonicalize(tmp.path()).unwrap();
        let tmp_parent = base.join("tmpdir");
        fs::create_dir_all(&tmp_parent).unwrap();
        let pinned = PinnedPrivateDir::create("miri-pin-", Some(&tmp_parent), &base, "pinned miri")
            .expect("create pinned miri cache dir");
        assert!(pinned.path().starts_with("/proc/self/fd/"));

        let disk_path = pinned.fs_root().to_path_buf();
        let target_rel = Path::new("miri-sysroot-test");
        let real_sys = pinned.pin_path(target_rel);
        fs::create_dir_all(real_sys.join("lib/rustlib")).unwrap();
        fs::write(real_sys.join("lib/rustlib/libcore.rlib"), b"legit-rlib").unwrap();

        // Attacker renames the `0o700` dir out from under writable `TMPDIR`
        // and plants a poisoned tree with a valid-looking stamp at the old
        // path.
        let moved_path = base.join("moved-miri");
        fs::rename(&disk_path, &moved_path).unwrap();
        fs::create_dir_all(disk_path.join("miri-sysroot-test/lib/rustlib")).unwrap();
        fs::write(disk_path.join("miri-sysroot-test/lib/rustlib/libcore.rlib"), b"trojan-rlib")
            .unwrap();
        fs::write(
            disk_path.join("miri-sysroot-test/.anneal-miri-ready"),
            expected_miri_ready_stamp_for_dir(
                &disk_path.join("miri-sysroot-test"),
                "trojan-tag",
                "bad-sha",
            ),
        )
        .unwrap();

        let files = pinned
            .collect_rel_file_sha256s(Some(&target_rel.join("lib/rustlib")), None, "miri lib")
            .unwrap();
        let stamp = expected_miri_ready_stamp_json("test-tag", "test-sha", files).unwrap();
        write_new_miri_ready_stamp(&real_sys, &stamp).unwrap();

        let (staged_sysroot, guard) = stage_and_verify_miri_sysroot_from_pinned(
            &pinned,
            target_rel,
            Path::new(STORE_PREFIX),
            "test-tag",
            "test-sha",
            "pinned Miri",
        )
        .expect("staging via PinnedPrivateDir fd must ignore trojan TMPDIR replacement");
        let _guard = guard.expect("frozen staging guard");
        assert_eq!(
            fs::read(staged_sysroot.join("lib/rustlib/libcore.rlib")).unwrap(),
            b"legit-rlib"
        );
    }
}
