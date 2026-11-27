// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Leg 0 compiled host `rustc` differential runner.
//!
//! Compiles concrete Stage-2 cases on the host target with `-C opt-level=0`,
//! `-C debug-assertions=no`, and `-C overflow-checks=off` inside a temporary
//! directory under [`ProcessSupervisor`] bounded timeouts.
//!
//! Uses batched single-process execution for speed and automatically falls back
//! to per-case isolated execution whenever a batch panics, traps, aborts, or
//! misses any expected case output, while propagating batch-wide timeouts and
//! launch failures directly as `ToolError` without amplification.

use std::{
    collections::{BTreeMap, BTreeSet},
    env,
    ffi::{CStr, CString, OsStr, OsString},
    fmt::Write as _,
    fs::{self, File, OpenOptions},
    io::{self, Read as _},
    path::{Component, Path, PathBuf},
    process::ExitStatus,
    sync::Arc,
    time::{Duration, Instant},
};

use anneal_testkit::{Invocation, ProcessOutcome, ProcessSupervisor, Termination};
use sha2::{Digest as _, Sha256};

use crate::{
    r#gen::{GenProgram, render_batch_crate},
    lean_runner::effective_timeout_duration,
    miri_runner::{
        parse_miri_ret_line, rust_arg_expr_pub, rust_print_ret_payload_expr, rust_ret_type_pub,
    },
    verdict::{MirValue, ObservedOutcome},
};

const RUSTC_CASE_PREFIX: &str = "ANNEAL_RUSTC_CASE:";
const RUSTC_RUN_PREFIX: &str = "ANNEAL_RUSTC_RUN:";
const RUSTC_COMPILE_TIMEOUT_SECS: u64 = 120;
const RUSTC_EXEC_TIMEOUT_SECS: u64 = 30;
pub(crate) const RUSTC_PROBE_TIMEOUT_SECS: u64 = 30;
#[cfg(windows)]
const LINKER_BIN_NAME: &str = "cc.exe";
#[cfg(not(windows))]
const LINKER_BIN_NAME: &str = "cc";
#[cfg(not(windows))]
pub(crate) const TRUSTED_LINKER_DIRS: &[&str] = &["/usr/bin", "/usr/local/bin"];
#[cfg(windows)]
pub(crate) const TRUSTED_LINKER_DIRS: &[&str] = &[];
#[cfg(not(windows))]
pub(crate) const TRUSTED_LINKER_SYMLINK_DIRS: &[&str] = &["/etc/alternatives"];
#[cfg(windows)]
pub(crate) const TRUSTED_LINKER_SYMLINK_DIRS: &[&str] = &[];
#[cfg(not(windows))]
pub(crate) const TRUSTED_CHILD_PATH_DIRS: &[&str] = &["/usr/bin", "/bin"];
#[cfg(windows)]
pub(crate) const TRUSTED_CHILD_PATH_DIRS: &[&str] = &[];
pub(crate) const STORE_PREFIX: &str = "/nix/store";
const MAX_LINKER_SYMLINK_HOPS: usize = 16;

type RustcOutcomeMap = BTreeMap<String, (ObservedOutcome, Option<String>)>;

enum CompileHarnessFailure {
    Global(String),
    Diagnostic(String),
}

#[derive(Debug)]
struct PreparedRustcHarness {
    exec_path: PathBuf,
    _staging: Arc<ImmutableStagingDir>,
}

#[cfg(unix)]
fn stage_compiled_harness_binary(
    work_dir_fd: std::os::fd::BorrowedFd<'_>,
    _work_dir: &Path,
    bin_name: &str,
    tmp_parent: Option<&Path>,
) -> Result<PreparedRustcHarness, String> {
    let mut bin_file = open_rel_regular_file_from_fd(
        work_dir_fd,
        Path::new(bin_name),
        false,
        "compiled rustc harness",
    )?;
    let stage_temp = crate::mir_eval_runner::build_temp_dir("anneal-rustc-bin-", tmp_parent)?;
    let (_, staging) =
        ImmutableStagingDir::build_and_pin(stage_temp, "compiled rustc harness", |_, pinned| {
            let dst_bin = pinned.join(bin_name);
            copy_opened_file_to_new_dst(
                &mut bin_file,
                false,
                &dst_bin,
                true,
                "compiled rustc harness",
            )
        })?;
    let exec_path = staging.pin_path(Path::new(bin_name));
    Ok(PreparedRustcHarness { exec_path, _staging: staging })
}

#[cfg(not(unix))]
fn stage_compiled_harness_binary(
    work_dir: &Path,
    bin_name: &str,
    tmp_parent: Option<&Path>,
) -> Result<PreparedRustcHarness, String> {
    let raw_bin = work_dir.join(bin_name);
    let canon_bin = crate::mir_eval_runner::validate_executable_no_links(
        &raw_bin,
        work_dir,
        "compiled rustc harness",
    )?;
    let stage_temp = crate::mir_eval_runner::build_temp_dir("anneal-rustc-bin-", tmp_parent)?;
    let (_, staging) =
        ImmutableStagingDir::build_and_pin(stage_temp, "compiled rustc harness", |_, pinned| {
            let dst_bin = pinned.join(bin_name);
            copy_verified_regular_file(&canon_bin, &dst_bin, true, "compiled rustc harness")
        })?;
    let exec_path = staging.pin_path(Path::new(bin_name));
    Ok(PreparedRustcHarness { exec_path, _staging: staging })
}

pub(crate) fn is_global_compiler_or_sysroot_stderr(stderr: &str) -> bool {
    stderr.contains("error: internal compiler error:")
        || stderr.contains("thread 'rustc' panicked at")
        || stderr.contains("can't find crate for")
        || stderr.contains("error[E0463]:")
        || stderr.contains("error: could not execute process")
        || stderr.contains("error while loading shared libraries")
        || stderr.contains("cannot open shared object file")
}

/// Lightweight execution specification shared by Stage-2 batched runners.
#[derive(Clone, Debug)]
pub struct FuzzExecCase {
    pub case_id: String,
    pub fn_name: String,
    pub args: Vec<MirValue>,
    pub ret_shape: MirValue,
    pub fuel: usize,
    pub expected_clean_batch: bool,
}

/// Prepared host `rustc` binary coordinates for Leg 0 execution.
#[derive(Clone, Debug)]
pub struct RustcSession {
    pub rustc_bin: PathBuf,
    pub rust_sysroot: PathBuf,
    pub ld_library_path: String,
    pub child_path: OsString,
    pub linker: PathBuf,
    pub pass_sysroot_arg: bool,
    pub(crate) validated_tmpdir: Option<PathBuf>,
    pub(crate) _sysroot_staging: Option<Arc<ImmutableStagingDir>>,
}

impl RustcSession {
    /// Locate `bin/rustc` inside `rust_sysroot`, resolve and validate an
    /// explicit C linker driver plus a fixed minimal toolchain `PATH` (without
    /// inheriting arbitrary ambient `PATH` entries), verify the host and
    /// compiled target are 64-bit (`target_pointer_width == "64"` matching Miri
    /// and Lean Profile v1 `usize`/`isize`), and probe whether `--sysroot` must
    /// be passed explicitly or is already supplied by a wrapper script (such as
    /// Nix `testSysroot` -> `rustCompilerForBuild`).
    pub fn prepare(rust_sysroot: &Path) -> Result<Self, String> {
        let store_prefix = Path::new(STORE_PREFIX);
        let trusted_dirs: Vec<&Path> = TRUSTED_LINKER_DIRS.iter().map(Path::new).collect();
        let symlink_dirs: Vec<&Path> = TRUSTED_LINKER_SYMLINK_DIRS.iter().map(Path::new).collect();
        let child_dirs: Vec<&Path> = TRUSTED_CHILD_PATH_DIRS.iter().map(Path::new).collect();
        let ambient_path = env::var_os("PATH");
        Self::prepare_with_config(
            rust_sysroot,
            store_prefix,
            &trusted_dirs,
            &symlink_dirs,
            &child_dirs,
            ambient_path.as_deref(),
        )
    }

    fn prepare_with_config(
        rust_sysroot: &Path,
        store_prefix: &Path,
        trusted_dirs: &[&Path],
        symlink_dirs: &[&Path],
        trusted_child_dirs: &[&Path],
        ambient_path: Option<&OsStr>,
    ) -> Result<Self, String> {
        let caller_cwd =
            env::current_dir().map_err(|e| format!("resolve current working directory: {e}"))?;
        let ambient_tmpdir = env::var_os("TMPDIR");
        Self::prepare_with_config_at(
            rust_sysroot,
            store_prefix,
            trusted_dirs,
            symlink_dirs,
            trusted_child_dirs,
            ambient_path,
            &caller_cwd,
            ambient_tmpdir.as_deref(),
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn prepare_with_config_at(
        rust_sysroot: &Path,
        store_prefix: &Path,
        trusted_dirs: &[&Path],
        symlink_dirs: &[&Path],
        trusted_child_dirs: &[&Path],
        ambient_path: Option<&OsStr>,
        caller_cwd: &Path,
        tmpdir_env: Option<&OsStr>,
    ) -> Result<Self, String> {
        ensure_64_bit_host(usize::BITS)?;
        // Anchor and validate TMPDIR before changing work_dir to sysroot or a
        // private harness directory so relative/bad values never resolve late.
        let validated_tmpdir = crate::mir_eval_runner::validate_optional_existing_dir_env(
            tmpdir_env, caller_cwd, "TMPDIR",
        )?;
        let prepared = prepare_sysroot_binary_in(
            rust_sysroot,
            "bin/rustc",
            store_prefix,
            validated_tmpdir.as_deref(),
            "Leg 0 rustc binary",
        )?;
        Self::prepare_from_prepared_sysroot_with_config(
            prepared,
            store_prefix,
            trusted_dirs,
            symlink_dirs,
            trusted_child_dirs,
            ambient_path,
            caller_cwd,
            validated_tmpdir,
        )
    }

    pub(crate) fn prepare_from_sysroot(
        prepared: PreparedSysroot,
        validated_tmpdir: Option<PathBuf>,
    ) -> Result<Self, String> {
        ensure_64_bit_host(usize::BITS)?;
        let caller_cwd =
            env::current_dir().map_err(|e| format!("resolve current working directory: {e}"))?;
        let store_prefix = Path::new(STORE_PREFIX);
        let trusted_dirs: Vec<&Path> = TRUSTED_LINKER_DIRS.iter().map(Path::new).collect();
        let symlink_dirs: Vec<&Path> = TRUSTED_LINKER_SYMLINK_DIRS.iter().map(Path::new).collect();
        let trusted_child_dirs: Vec<&Path> =
            TRUSTED_CHILD_PATH_DIRS.iter().map(Path::new).collect();
        let ambient_path = env::var_os("PATH");
        Self::prepare_from_prepared_sysroot_with_config(
            prepared,
            store_prefix,
            &trusted_dirs,
            &symlink_dirs,
            &trusted_child_dirs,
            ambient_path.as_deref(),
            &caller_cwd,
            validated_tmpdir,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn prepare_from_prepared_sysroot_with_config(
        prepared: PreparedSysroot,
        store_prefix: &Path,
        trusted_dirs: &[&Path],
        symlink_dirs: &[&Path],
        trusted_child_dirs: &[&Path],
        ambient_path: Option<&OsStr>,
        caller_cwd: &Path,
        validated_tmpdir: Option<PathBuf>,
    ) -> Result<Self, String> {
        let raw_sysroot = prepared.sysroot;
        let raw_rustc_bin = prepared.binary;
        let raw_ld_library_path = prepared.ld_library_path;
        let linker = resolve_and_validate_linker_with(
            &raw_sysroot,
            store_prefix,
            trusted_dirs,
            symlink_dirs,
            ambient_path,
            caller_cwd,
        )?;
        let raw_child_path = build_child_path_with(
            &raw_sysroot.join("bin"),
            &linker,
            store_prefix,
            trusted_child_dirs,
            ambient_path,
            caller_cwd,
        )?;
        let staging_guards = [prepared._staging.as_ref()];
        let rust_sysroot = ImmutableStagingDir::pin_path_with_guards(&staging_guards, &raw_sysroot);
        let rustc_bin = ImmutableStagingDir::pin_path_with_guards(&staging_guards, &raw_rustc_bin);
        let ld_library_path = if raw_ld_library_path.is_empty() {
            String::new()
        } else {
            ImmutableStagingDir::pin_env_paths_with_guards(
                &staging_guards,
                OsStr::new(&raw_ld_library_path),
            )?
            .to_string_lossy()
            .into_owned()
        };
        let child_path =
            ImmutableStagingDir::pin_env_paths_with_guards(&staging_guards, &raw_child_path)?;
        let pass_sysroot_arg = detect_pass_sysroot_arg(
            &rustc_bin,
            &rust_sysroot,
            &ld_library_path,
            &child_path,
            store_prefix,
            caller_cwd,
            validated_tmpdir.as_deref(),
        )?;
        ensure_64_bit_rustc_target(
            &rustc_bin,
            &rust_sysroot,
            &ld_library_path,
            &child_path,
            pass_sysroot_arg,
            validated_tmpdir.as_deref(),
        )?;
        Ok(Self {
            rustc_bin,
            rust_sysroot,
            ld_library_path,
            child_path,
            linker,
            pass_sysroot_arg,
            validated_tmpdir,
            _sysroot_staging: prepared._staging,
        })
    }

    /// Compile `source_text` once into a temporary native harness executable,
    /// stage it into a frozen `0o555`/`0o444` directory pinned against `TMPDIR`
    /// renames, and prepare it for batched and isolated executions.
    fn compile_harness_binary(
        &self,
        work_dir: &Path,
        source_text: &str,
        cases: &[FuzzExecCase],
        deadline: Option<Instant>,
    ) -> Result<Result<PreparedRustcHarness, CompileHarnessFailure>, String> {
        ensure_64_bit_host(usize::BITS)?;
        #[cfg(unix)]
        let work_dir_fd = open_dir_handle_no_symlinks(work_dir, None, "compiled rustc workdir")?;
        let harness_src = generate_rustc_harness(source_text, cases)?;
        let rel_src = "rustc_harness.rs";
        let rel_bin = if cfg!(windows) { "rustc_harness_bin.exe" } else { "rustc_harness_bin" };
        let harness_path = work_dir.join(rel_src);
        fs::write(&harness_path, harness_src)
            .map_err(|e| format!("write rustc harness {}: {e}", harness_path.display()))?;

        let mut compile_inv = Invocation::new(&self.rustc_bin, &["--edition=2024"]);
        if self.pass_sysroot_arg {
            compile_inv = compile_inv.arg("--sysroot").arg(&self.rust_sysroot);
        }
        let linker_arg = format!("linker={}", self.linker.display());
        compile_inv = compile_inv
            .arg("-C")
            .arg(linker_arg)
            .arg("-C")
            .arg("opt-level=0")
            .arg("-C")
            .arg("debug-assertions=no")
            .arg("-C")
            .arg("overflow-checks=off")
            .arg("-o")
            .arg(rel_bin)
            .arg(rel_src)
            .env("LD_LIBRARY_PATH", &self.ld_library_path)
            .env("PATH", &self.child_path);
        if let Some(td) = &self.validated_tmpdir {
            compile_inv = compile_inv.env("TMPDIR", td);
        }

        let compile_timeout = effective_timeout_duration(RUSTC_COMPILE_TIMEOUT_SECS, deadline)?;
        let compile_out = run_supervised_in_tmp(
            &compile_inv,
            work_dir,
            compile_timeout,
            self.validated_tmpdir.as_deref(),
            "rustc compile",
        )?;
        match compile_out.termination {
            Termination::Exited(status) if status.success() => {
                #[cfg(unix)]
                let prepared = {
                    use std::os::fd::AsFd as _;
                    stage_compiled_harness_binary(
                        work_dir_fd.as_fd(),
                        work_dir,
                        rel_bin,
                        self.validated_tmpdir.as_deref(),
                    )?
                };
                #[cfg(not(unix))]
                let prepared = stage_compiled_harness_binary(
                    work_dir,
                    rel_bin,
                    self.validated_tmpdir.as_deref(),
                )?;
                Ok(Ok(prepared))
            }
            Termination::TimedOut(_) | Termination::LaunchFailed(_) => {
                let stderr = String::from_utf8_lossy(&compile_out.stderr);
                let detail = format!(
                    "compiled rustc harness failed ({}): {}",
                    compile_out.termination.describe(),
                    stderr.lines().take(6).collect::<Vec<_>>().join(" | ")
                );
                Ok(Err(CompileHarnessFailure::Global(detail)))
            }
            Termination::Exited(_) => {
                let stderr = String::from_utf8_lossy(&compile_out.stderr);
                let detail = format!(
                    "compiled rustc harness failed ({}): {}",
                    compile_out.termination.describe(),
                    stderr.lines().take(6).collect::<Vec<_>>().join(" | ")
                );
                if is_global_compiler_or_sysroot_stderr(&stderr) {
                    Ok(Err(CompileHarnessFailure::Global(detail)))
                } else {
                    Ok(Err(CompileHarnessFailure::Diagnostic(detail)))
                }
            }
        }
    }

    /// Compile `source_text` once with a generated `fn main()` dispatcher and
    /// run `expected_clean_batch == true` cases in one fast `__BATCH__`
    /// invocation, running all remaining (UB-probe / failed-batch) cases in
    /// isolated per-case subprocesses.
    pub fn run_batch(
        &self,
        source_text: &str,
        cases: &[FuzzExecCase],
    ) -> Result<BTreeMap<String, ObservedOutcome>, String> {
        self.run_batch_until(source_text, cases, None)
    }

    /// Deadline-clamped variant of [`Self::run_batch`] used by the shrinker.
    pub fn run_batch_until(
        &self,
        source_text: &str,
        cases: &[FuzzExecCase],
        deadline: Option<Instant>,
    ) -> Result<BTreeMap<String, ObservedOutcome>, String> {
        let with_ev = self.run_batch_with_evidence_until(source_text, cases, deadline)?;
        Ok(with_ev.into_iter().map(|(id, (outcome, _ev))| (id, outcome)).collect())
    }

    /// Deadline-clamped execution returning `(outcome, case_bound_evidence)`
    /// for every case in `cases`.
    pub fn run_batch_with_evidence_until(
        &self,
        source_text: &str,
        cases: &[FuzzExecCase],
        deadline: Option<Instant>,
    ) -> Result<BTreeMap<String, (ObservedOutcome, Option<String>)>, String> {
        self.run_batch_with_evidence_impl(source_text, None, cases, deadline)
    }

    /// Program-aware deadline-clamped execution that isolates ordinary compiler
    /// diagnostics via recursive subset-crate bisection so one broken
    /// generated function never poisons valid batch-mates.
    pub fn run_batch_crate_with_evidence_until(
        &self,
        source_text: &str,
        programs: &[&GenProgram],
        cases: &[FuzzExecCase],
        deadline: Option<Instant>,
    ) -> Result<RustcOutcomeMap, String> {
        if programs.len() != cases.len() {
            return Err(format!(
                "rustc crate program count ({}) does not match case count ({})",
                programs.len(),
                cases.len()
            ));
        }
        let pairs: Vec<(&GenProgram, &FuzzExecCase)> =
            programs.iter().copied().zip(cases.iter()).collect();
        for (prog, case) in &pairs {
            if prog.case_id != case.case_id {
                return Err(format!(
                    "rustc crate program `{}` does not match case `{}`",
                    prog.case_id, case.case_id
                ));
            }
        }
        self.run_batch_with_evidence_impl(source_text, Some(&pairs), cases, deadline)
    }

    fn run_batch_with_evidence_impl(
        &self,
        source_text: &str,
        programs: Option<&[(&GenProgram, &FuzzExecCase)]>,
        cases: &[FuzzExecCase],
        deadline: Option<Instant>,
    ) -> Result<RustcOutcomeMap, String> {
        self.run_batch_with_evidence_hook_impl(source_text, programs, cases, deadline, |_, _| {})
    }

    fn run_batch_with_evidence_hook_impl(
        &self,
        source_text: &str,
        programs: Option<&[(&GenProgram, &FuzzExecCase)]>,
        cases: &[FuzzExecCase],
        deadline: Option<Instant>,
        on_compiled: impl FnOnce(&Path, &PreparedRustcHarness),
    ) -> Result<RustcOutcomeMap, String> {
        if cases.is_empty() {
            return Ok(BTreeMap::new());
        }

        let work_dir = crate::mir_eval_runner::build_temp_dir(
            "anneal-rustc-work-",
            self.validated_tmpdir.as_deref(),
        )?;
        let canon_work = fs::canonicalize(work_dir.path())
            .map_err(|e| format!("canonicalize temporary rustc workdir: {e}"))?;
        let harness =
            match self.compile_harness_binary(&canon_work, source_text, cases, deadline)? {
                Ok(harness) => harness,
                Err(CompileHarnessFailure::Diagnostic(_))
                    if programs.is_some_and(|p| p.len() > 1) =>
                {
                    let pairs = programs.expect("checked is_some above");
                    let mid = pairs.len() / 2;
                    let mut combined = self.run_rustc_subset_slice(&pairs[..mid], deadline)?;
                    combined.extend(self.run_rustc_subset_slice(&pairs[mid..], deadline)?);
                    return Ok(combined);
                }
                Err(
                    CompileHarnessFailure::Global(detail)
                    | CompileHarnessFailure::Diagnostic(detail),
                ) => {
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
        // Remove the writable compilation workspace once the compiled binary
        // has been frozen and descriptor-pinned inside `PreparedRustcHarness`.
        drop(work_dir);
        on_compiled(&canon_work, &harness);

        let exec_work_dir = harness._staging.pin_path(Path::new(""));
        let mut results = BTreeMap::new();
        let clean_cases: Vec<&FuzzExecCase> =
            cases.iter().filter(|c| c.expected_clean_batch).collect();
        let isolated_cases: Vec<&FuzzExecCase> =
            cases.iter().filter(|c| !c.expected_clean_batch).collect();

        if !clean_cases.is_empty() {
            if let Some(batch_map) = self.try_run_compiled_batch(
                &harness.exec_path,
                &exec_work_dir,
                &clean_cases,
                deadline,
            )? {
                results.extend(batch_map);
            } else {
                // Automatic per-case isolation fallback whenever a batch fails,
                // panics, aborts, or misses any case output.
                for c in &clean_cases {
                    let out = self.run_compiled_single(
                        &harness.exec_path,
                        &exec_work_dir,
                        &c.case_id,
                        &c.fn_name,
                        deadline,
                    )?;
                    results.insert(c.case_id.clone(), out);
                }
            }
        }

        for c in &isolated_cases {
            let out = self.run_compiled_single(
                &harness.exec_path,
                &exec_work_dir,
                &c.case_id,
                &c.fn_name,
                deadline,
            )?;
            results.insert(c.case_id.clone(), out);
        }

        Ok(results)
    }

    fn run_rustc_subset_slice(
        &self,
        pairs: &[(&GenProgram, &FuzzExecCase)],
        deadline: Option<Instant>,
    ) -> Result<RustcOutcomeMap, String> {
        let sub_progs: Vec<&GenProgram> = pairs.iter().map(|(p, _)| *p).collect();
        let sub_cases: Vec<FuzzExecCase> = pairs.iter().map(|(_, c)| (*c).clone()).collect();
        let sub_src = render_batch_crate(&sub_progs);
        let sub_pairs: Vec<(&GenProgram, &FuzzExecCase)> =
            sub_progs.into_iter().zip(sub_cases.iter()).collect();
        self.run_batch_with_evidence_impl(&sub_src, Some(&sub_pairs), &sub_cases, deadline)
    }

    /// Re-run `programs` individually in fresh child processes (forcing
    /// single-case execution instead of `__BATCH__`) and bisect any
    /// `CompileHarnessFailure::Diagnostic` across subset crates so a broken
    /// neighbor can never poison clean cases during `clean_batch_hit_ub`
    /// isolation.
    pub fn run_isolated_programs_with_evidence_until(
        &self,
        programs: &[&GenProgram],
        cases: &[FuzzExecCase],
        deadline: Option<Instant>,
    ) -> Result<RustcOutcomeMap, String> {
        if programs.len() != cases.len() {
            return Err(format!(
                "isolated rustc program count {} mismatches case count {}",
                programs.len(),
                cases.len()
            ));
        }
        if programs.is_empty() {
            return Ok(BTreeMap::new());
        }
        let iso_cases: Vec<FuzzExecCase> = cases
            .iter()
            .zip(programs)
            .map(|(case, prog)| {
                if prog.case_id != case.case_id {
                    return Err(format!(
                        "isolated rustc program `{}` does not match case `{}`",
                        prog.case_id, case.case_id
                    ));
                }
                Ok(FuzzExecCase { expected_clean_batch: false, ..case.clone() })
            })
            .collect::<Result<Vec<_>, String>>()?;
        let source_text = render_batch_crate(programs);
        let pairs: Vec<(&GenProgram, &FuzzExecCase)> =
            programs.iter().copied().zip(iso_cases.iter()).collect();
        self.run_batch_with_evidence_impl(&source_text, Some(&pairs), &iso_cases, deadline)
    }

    /// Re-run a specific subset of `isolate_ids` individually in fresh child
    /// processes using identical host compilation flags as `run_batch` so an
    /// unexpected Miri UB in one `expected_clean_batch` case can never taint
    /// its batch-mates.
    pub fn run_isolated_subset(
        &self,
        source_text: &str,
        all_cases: &[FuzzExecCase],
        isolate_ids: &[String],
    ) -> Result<BTreeMap<String, ObservedOutcome>, String> {
        let with_ev = self.run_isolated_subset_with_evidence_until(
            source_text,
            all_cases,
            isolate_ids,
            None,
        )?;
        Ok(with_ev.into_iter().map(|(id, (outcome, _ev))| (id, outcome)).collect())
    }

    /// Deadline-clamped variant of [`Self::run_isolated_subset`].
    pub fn run_isolated_subset_until(
        &self,
        source_text: &str,
        all_cases: &[FuzzExecCase],
        isolate_ids: &[String],
        deadline: Option<Instant>,
    ) -> Result<BTreeMap<String, ObservedOutcome>, String> {
        let with_ev = self.run_isolated_subset_with_evidence_until(
            source_text,
            all_cases,
            isolate_ids,
            deadline,
        )?;
        Ok(with_ev.into_iter().map(|(id, (outcome, _ev))| (id, outcome)).collect())
    }

    /// Deadline-clamped isolated re-execution returning
    /// `(outcome, case_bound_evidence)` for each requested `case_id`.
    pub fn run_isolated_subset_with_evidence_until(
        &self,
        source_text: &str,
        all_cases: &[FuzzExecCase],
        isolate_ids: &[String],
        deadline: Option<Instant>,
    ) -> Result<BTreeMap<String, (ObservedOutcome, Option<String>)>, String> {
        if isolate_ids.is_empty() {
            return Ok(BTreeMap::new());
        }
        let work_dir = crate::mir_eval_runner::build_temp_dir(
            "anneal-rustc-iso-",
            self.validated_tmpdir.as_deref(),
        )?;
        let canon_work = fs::canonicalize(work_dir.path())
            .map_err(|e| format!("canonicalize rustc isolated workdir: {e}"))?;
        let harness =
            match self.compile_harness_binary(&canon_work, source_text, all_cases, deadline)? {
                Ok(harness) => harness,
                Err(
                    CompileHarnessFailure::Global(detail)
                    | CompileHarnessFailure::Diagnostic(detail),
                ) => {
                    return Ok(isolate_ids
                        .iter()
                        .map(|id| {
                            (
                                id.clone(),
                                (ObservedOutcome::ToolError { detail: detail.clone() }, None),
                            )
                        })
                        .collect());
                }
            };
        drop(work_dir);
        let exec_work_dir = harness._staging.pin_path(Path::new(""));
        let fn_by_id: BTreeMap<&str, &str> =
            all_cases.iter().map(|c| (c.case_id.as_str(), c.fn_name.as_str())).collect();
        let mut results = BTreeMap::new();
        for id in isolate_ids {
            let fn_name = fn_by_id.get(id.as_str()).copied().unwrap_or(id.as_str());
            let out = self.run_compiled_single(
                &harness.exec_path,
                &exec_work_dir,
                id,
                fn_name,
                deadline,
            )?;
            results.insert(id.clone(), out);
        }
        Ok(results)
    }

    fn try_run_compiled_batch(
        &self,
        bin: &Path,
        work_dir: &Path,
        cases: &[&FuzzExecCase],
        deadline: Option<Instant>,
    ) -> Result<Option<RustcOutcomeMap>, String> {
        let mut inv = Invocation::new(bin, &["__BATCH__"])
            .env("LD_LIBRARY_PATH", &self.ld_library_path)
            .env("PATH", &self.child_path)
            .env("RUST_BACKTRACE", "0");
        for c in cases {
            inv = inv.arg(&c.case_id);
        }
        let timeout = effective_timeout_duration(RUSTC_EXEC_TIMEOUT_SECS, deadline)?;
        let out = run_supervised_in_tmp(
            &inv,
            work_dir,
            timeout,
            self.validated_tmpdir.as_deref(),
            "rustc batch exec",
        )?;
        match &out.termination {
            Termination::TimedOut(_) | Termination::LaunchFailed(_) => {
                let detail = format!(
                    "compiled rustc batch infrastructure failure ({})",
                    out.termination.describe()
                );
                return Ok(Some(
                    cases
                        .iter()
                        .map(|c| {
                            (
                                c.case_id.clone(),
                                (ObservedOutcome::ToolError { detail: detail.clone() }, None),
                            )
                        })
                        .collect(),
                ));
            }
            Termination::Exited(_) => {}
        }
        let Termination::Exited(status) = out.termination else {
            return Ok(None);
        };
        if !status.success() {
            return Ok(None);
        }
        let stdout = String::from_utf8_lossy(&out.stdout);
        let parsed = parse_rustc_batch_stdout(&stdout, cases);
        Ok(parsed)
    }

    fn run_compiled_single(
        &self,
        bin: &Path,
        work_dir: &Path,
        case_id: &str,
        fn_name: &str,
        deadline: Option<Instant>,
    ) -> Result<(ObservedOutcome, Option<String>), String> {
        let inv = Invocation::new(bin, &[case_id])
            .env("LD_LIBRARY_PATH", &self.ld_library_path)
            .env("PATH", &self.child_path)
            .env("RUST_BACKTRACE", "0");
        let timeout = effective_timeout_duration(RUSTC_EXEC_TIMEOUT_SECS, deadline)?;
        let out = run_supervised_in_tmp(
            &inv,
            work_dir,
            timeout,
            self.validated_tmpdir.as_deref(),
            case_id,
        )?;
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        Ok(parse_rustc_fuzz_single_output(&out.termination, case_id, fn_name, &stdout, &stderr))
    }
}

/// Generate a standalone std harness that compiles `source_text` inside
/// `mod corpus` and dispatches either a single `<case_id>` or `__BATCH__ ...`.
pub fn generate_rustc_harness(source_text: &str, cases: &[FuzzExecCase]) -> Result<String, String> {
    let (crate_attrs, mod_lines) = crate::miri_runner::split_crate_attrs(source_text);

    let mut out = String::new();
    for attr in &crate_attrs {
        out.push_str(attr);
        out.push('\n');
    }
    out.push_str("\n#[allow(dead_code)]\nmod corpus {\n");
    for line in &mod_lines {
        out.push_str("    ");
        out.push_str(line);
        out.push('\n');
    }
    out.push_str("}\n\nfn run_one(selector: &str) {\n");
    out.push_str("    use std::io::Write;\n");
    out.push_str("    match selector {\n");

    for case in cases {
        let arg_exprs =
            case.args.iter().map(rust_arg_expr_pub).collect::<Result<Vec<_>, _>>()?.join(", ");
        let ret_ty = rust_ret_type_pub(&case.ret_shape)?;
        let payload_expr = rust_print_ret_payload_expr(&case.ret_shape, "ret")?;
        let _ = writeln!(out, "        {:?} => {{", case.case_id);
        let _ = writeln!(
            out,
            "            println!(\"{RUSTC_RUN_PREFIX}{}:{}\");",
            case.case_id, case.fn_name
        );
        out.push_str("            let _ = std::io::stdout().flush();\n");
        let _ = writeln!(
            out,
            "            let ret: {ret_ty} = std::hint::black_box(unsafe {{ corpus::{}({arg_exprs}) }});",
            case.fn_name
        );
        let _ = writeln!(
            out,
            "            println!(\"{RUSTC_CASE_PREFIX}{}:{{}}\", {payload_expr});",
            case.case_id
        );
        out.push_str("            let _ = std::io::stdout().flush();\n");
        out.push_str("        }\n");
    }

    out.push_str(
        "        other => panic!(\"unknown rustc differential case selector: {other}\"),\n",
    );
    out.push_str("    }\n}\n\nfn main() {\n");
    out.push_str("    let args: Vec<String> = std::env::args().skip(1).collect();\n");
    out.push_str("    if args.first().map(String::as_str) == Some(\"__BATCH__\") {\n");
    out.push_str("        for sel in &args[1..] {\n");
    out.push_str("            run_one(sel);\n");
    out.push_str("        }\n");
    out.push_str("    } else if let Some(sel) = args.first() {\n");
    out.push_str("        run_one(sel);\n");
    out.push_str("    } else {\n");
    out.push_str("        panic!(\"missing differential case selector\");\n");
    out.push_str("    }\n}\n");
    Ok(out)
}

fn parse_rustc_batch_stdout(
    stdout: &str,
    cases: &[&FuzzExecCase],
) -> Option<BTreeMap<String, (ObservedOutcome, Option<String>)>> {
    let mut run_seen = BTreeMap::new();
    let mut raw = BTreeMap::new();
    for line in stdout.lines() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix(RUSTC_RUN_PREFIX)
            && let Some((id, fn_name)) = rest.split_once(':')
        {
            run_seen.insert(id.to_owned(), fn_name.to_owned());
        } else if let Some(rest) = trimmed.strip_prefix(RUSTC_CASE_PREFIX)
            && let Some((id, payload)) = rest.split_once(':')
        {
            let value = parse_miri_ret_line(payload).ok()?;
            raw.insert(id.to_owned(), (ObservedOutcome::Returned { value }, payload.to_owned()));
        }
    }
    if raw.len() != cases.len() {
        return None;
    }
    let mut out = BTreeMap::new();
    for c in cases {
        if run_seen.get(&c.case_id).map(String::as_str) != Some(c.fn_name.as_str()) {
            return None;
        }
        let (outcome, payload) = raw.remove(&c.case_id)?;
        let evidence = format!(
            "{RUSTC_RUN_PREFIX}{}:{}|{RUSTC_CASE_PREFIX}{}:{payload}",
            c.case_id, c.fn_name, c.case_id
        );
        out.insert(c.case_id.clone(), (outcome, Some(evidence)));
    }
    Some(out)
}

fn parse_rustc_fuzz_single_output(
    termination: &Termination,
    case_id: &str,
    fn_name: &str,
    stdout: &str,
    stderr: &str,
) -> (ObservedOutcome, Option<String>) {
    let run_marker = format!("{RUSTC_RUN_PREFIX}{case_id}:{fn_name}");
    let has_run = stdout.lines().any(|l| l.trim() == run_marker);
    let outcome = parse_rustc_single_output(termination, case_id, stdout, stderr);
    match outcome {
        ObservedOutcome::Returned { value } => {
            if !has_run {
                return (
                    ObservedOutcome::ToolError {
                        detail: format!("compiled rustc binary did not emit `{run_marker}`"),
                    },
                    None,
                );
            }
            let prefix = format!("{RUSTC_CASE_PREFIX}{case_id}:");
            let Some(payload) = stdout.lines().find_map(|l| l.trim().strip_prefix(&prefix)) else {
                return (
                    ObservedOutcome::ToolError {
                        detail: format!("compiled rustc binary missing `{prefix}` payload"),
                    },
                    None,
                );
            };
            (ObservedOutcome::Returned { value }, Some(format!("{run_marker}|{prefix}{payload}")))
        }
        ObservedOutcome::AbnormalAbort { ref detail } => {
            if has_run {
                let ev = format!("{run_marker}|ABORT|{detail}");
                (outcome, Some(ev))
            } else {
                (
                    ObservedOutcome::ToolError {
                        detail: format!(
                            "compiled rustc binary aborted without `{run_marker}`: {detail}"
                        ),
                    },
                    None,
                )
            }
        }
        ObservedOutcome::Panic { ref detail } => {
            if has_run {
                let ev = format!("{run_marker}|PANIC|{detail}");
                (outcome, Some(ev))
            } else {
                (
                    ObservedOutcome::ToolError {
                        detail: format!(
                            "compiled rustc binary panicked without `{run_marker}`: {detail}"
                        ),
                    },
                    None,
                )
            }
        }
        other => (other, None),
    }
}

fn status_signal_detail(status: ExitStatus) -> Option<String> {
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;
        status.signal().map(|sig| format!("terminated by signal {sig}"))
    }
    #[cfg(not(unix))]
    {
        let _ = status;
        None
    }
}

/// Classify a single compiled-binary execution into an [`ObservedOutcome`].
pub fn parse_rustc_single_output(
    termination: &Termination,
    case_id: &str,
    stdout: &str,
    stderr: &str,
) -> ObservedOutcome {
    match termination {
        Termination::TimedOut(status) => ObservedOutcome::ToolError {
            detail: format!("compiled rustc binary timed out for {case_id} ({status})"),
        },
        Termination::LaunchFailed(err) => ObservedOutcome::ToolError {
            detail: format!("launch compiled rustc binary for {case_id}: {err}"),
        },
        Termination::Exited(status) => {
            if status.success() {
                let prefix = format!("{RUSTC_CASE_PREFIX}{case_id}:");
                let Some(payload) = stdout.lines().find_map(|l| l.strip_prefix(&prefix)) else {
                    return ObservedOutcome::ToolError {
                        detail: format!(
                            "compiled rustc binary exited 0 without `{prefix}` line; stdout={stdout:?}"
                        ),
                    };
                };
                return match parse_miri_ret_line(payload) {
                    Ok(value) => ObservedOutcome::Returned { value },
                    Err(e) => ObservedOutcome::ToolError {
                        detail: format!("parse rustc return payload {payload:?}: {e}"),
                    },
                };
            }
            if let Some(sig_detail) = status_signal_detail(*status) {
                return ObservedOutcome::AbnormalAbort { detail: sig_detail };
            }
            if stderr.contains("panicked at ") || status.code() == Some(101) {
                let headline = stderr
                    .lines()
                    .find(|l| l.contains("panicked at "))
                    .unwrap_or("panicked")
                    .trim()
                    .to_owned();
                return ObservedOutcome::Panic { detail: headline };
            }
            ObservedOutcome::AbnormalAbort {
                detail: format!("compiled rustc binary exited with {status}"),
            }
        }
    }
}

pub(crate) fn ensure_64_bit_host(pointer_bits: u32) -> Result<(), String> {
    if pointer_bits == 64 {
        Ok(())
    } else {
        Err(format!(
            "Leg 0 (rustc) requires a 64-bit host matching Miri and Lean `x86_64` \
             64-bit `usize`/`isize` semantics (host pointer width is {pointer_bits}-bit); \
             re-run with `--no-rustc` or on a 64-bit host"
        ))
    }
}

fn parse_target_pointer_width(cfg_stdout: &str) -> Result<u32, String> {
    let mut parsed: Vec<u32> = Vec::new();
    for line in cfg_stdout.lines() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix("target_pointer_width=") {
            let raw = rest.trim().strip_prefix('"').and_then(|s| s.strip_suffix('"')).ok_or_else(
                || format!("parse `rustc --print cfg` target_pointer_width line: {trimmed:?}"),
            )?;
            let width = raw.parse::<u32>().map_err(|e| {
                format!("parse `rustc --print cfg` target_pointer_width={raw:?}: {e}")
            })?;
            parsed.push(width);
        }
    }
    match parsed.as_slice() {
        [] => Err("`rustc --print cfg` output missing `target_pointer_width`".to_owned()),
        [first, rest @ ..] if rest.iter().all(|w| w == first) => Ok(*first),
        _ => Err(format!(
            "conflicting `target_pointer_width` entries in `rustc --print cfg`: {parsed:?}"
        )),
    }
}

#[allow(clippy::too_many_arguments)]
fn run_rustc_print_probe(
    rustc_bin: &Path,
    rust_sysroot: &Path,
    ld_library_path: &str,
    child_path: &OsString,
    with_sysroot: bool,
    print_arg: &str,
    validated_tmpdir: Option<&Path>,
) -> Result<ProcessOutcome, String> {
    let mut inv = Invocation::new(rustc_bin, &[]);
    if with_sysroot {
        inv = inv.arg("--sysroot").arg(rust_sysroot);
    }
    inv = inv
        .arg("--print")
        .arg(print_arg)
        .env("LD_LIBRARY_PATH", ld_library_path)
        .env("PATH", child_path);
    if let Some(td) = validated_tmpdir {
        inv = inv.env("TMPDIR", td);
    }
    run_supervised_in_tmp(
        &inv,
        rust_sysroot,
        Duration::from_secs(RUSTC_PROBE_TIMEOUT_SECS),
        validated_tmpdir,
        &format!("rustc --print {print_arg}"),
    )
}

fn ensure_64_bit_rustc_target(
    rustc_bin: &Path,
    rust_sysroot: &Path,
    ld_library_path: &str,
    child_path: &OsString,
    pass_sysroot_arg: bool,
    validated_tmpdir: Option<&Path>,
) -> Result<(), String> {
    let cfg_out = run_rustc_print_probe(
        rustc_bin,
        rust_sysroot,
        ld_library_path,
        child_path,
        pass_sysroot_arg,
        "cfg",
        validated_tmpdir,
    )?;
    match &cfg_out.termination {
        Termination::Exited(status) if status.success() => {}
        other => {
            let stderr = String::from_utf8_lossy(&cfg_out.stderr);
            return Err(format!(
                "`{}` `--print cfg` probe failed ({}: {})",
                rustc_bin.display(),
                other.describe(),
                stderr.trim(),
            ));
        }
    }
    let stdout = String::from_utf8_lossy(&cfg_out.stdout);
    let width = parse_target_pointer_width(&stdout)?;
    if width != 64 {
        return Err(format!(
            "Leg 0 `{}` targets {width}-bit (`target_pointer_width=\"{width}\"`), whereas Miri and Lean Profile v1 model `usize`/`isize` as 64-bit; re-run with `--no-rustc` or a 64-bit host toolchain",
            rustc_bin.display(),
        ));
    }
    Ok(())
}

fn detect_pass_sysroot_arg(
    rustc_bin: &Path,
    rust_sysroot: &Path,
    ld_library_path: &str,
    child_path: &OsString,
    store_prefix: &Path,
    caller_cwd: &Path,
    validated_tmpdir: Option<&Path>,
) -> Result<bool, String> {
    let with_flag = run_rustc_print_probe(
        rustc_bin,
        rust_sysroot,
        ld_library_path,
        child_path,
        true,
        "sysroot",
        validated_tmpdir,
    )?;
    match &with_flag.termination {
        Termination::Exited(status) if status.success() => return Ok(true),
        Termination::Exited(_) => {}
        other => {
            return Err(format!(
                "`{}` `--sysroot` probe failed ({})",
                rustc_bin.display(),
                other.describe(),
            ));
        }
    }
    let with_flag_stderr = String::from_utf8_lossy(&with_flag.stderr);
    let without_flag = run_rustc_print_probe(
        rustc_bin,
        rust_sysroot,
        ld_library_path,
        child_path,
        false,
        "sysroot",
        validated_tmpdir,
    )?;
    let reported_stdout = String::from_utf8_lossy(&without_flag.stdout);
    let trimmed = reported_stdout.trim();
    if matches!(without_flag.termination, Termination::Exited(status) if status.success())
        && !trimmed.is_empty()
    {
        let reported_sysroot = Path::new(trimmed);
        validate_reported_wrapper_sysroot(reported_sysroot, store_prefix, caller_cwd)?;
        return Ok(false);
    }
    let without_flag_stderr = String::from_utf8_lossy(&without_flag.stderr);
    Err(format!(
        "`{}` rejected `--sysroot` ({}: {}) and failed `--print sysroot` ({}: {})",
        rustc_bin.display(),
        with_flag.termination.describe(),
        with_flag_stderr.trim(),
        without_flag.termination.describe(),
        without_flag_stderr.trim(),
    ))
}

fn validate_reported_wrapper_sysroot(
    reported_sysroot: &Path,
    store_prefix: &Path,
    caller_cwd: &Path,
) -> Result<PathBuf, String> {
    let label = "Leg 0 wrapper-reported sysroot";
    if reported_sysroot.components().any(|c| matches!(c, Component::ParentDir)) {
        return Err(format!(
            "{label} must not contain `..` traversal segments: {}",
            reported_sysroot.display()
        ));
    }
    let canon_sysroot =
        validated_store_aware_dir(reported_sysroot, store_prefix, caller_cwd, label)?;
    let lib_dir = canon_sysroot.join("lib");
    match fs::symlink_metadata(&lib_dir) {
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            return Err(format!("{label} missing `lib` directory: {}", lib_dir.display()));
        }
        Err(e) => {
            return Err(format!("stat {label} lib {}: {e}", lib_dir.display()));
        }
        Ok(_) => {}
    }
    if canon_sysroot.starts_with(store_prefix) && fs::symlink_metadata(store_prefix).is_ok() {
        let canon_store =
            crate::mir_eval_runner::validate_dir_path_no_symlinks(store_prefix, caller_cwd)?;
        let canon_lib = validate_store_contained_entry(
            &lib_dir,
            store_prefix,
            &canon_store,
            true,
            "Leg 0 wrapper-reported sysroot lib",
        )?;
        validate_store_contained_dir_tree(
            &canon_lib,
            store_prefix,
            &canon_store,
            "Leg 0 wrapper-reported sysroot lib",
        )?;
    } else {
        let canon_lib =
            crate::mir_eval_runner::validate_dir_path_no_symlinks(&lib_dir, caller_cwd)?;
        // A wrapper that rejects `--sysroot` resolves its reported sysroot
        // directly, so non-store symlinks cannot be isolated and must fail.
        validate_dir_tree_no_links(&canon_lib, "Leg 0 wrapper-reported sysroot lib")?;
    }
    if fs::symlink_metadata(canon_sysroot.join("bin/rustc")).is_ok() {
        let _ = validated_store_aware_executable(
            &canon_sysroot.join("bin/rustc"),
            store_prefix,
            caller_cwd,
            "Leg 0 wrapper-reported sysroot rustc",
        )?;
    }
    Ok(canon_sysroot)
}

#[cfg(target_os = "linux")]
fn open_pinned_cloexec_clear_dir_fd(
    abs_dir: &Path,
    expected_mode: Option<libc::mode_t>,
    require_empty: bool,
    label: &str,
) -> Result<std::os::fd::OwnedFd, String> {
    use std::os::fd::{AsFd as _, AsRawFd as _};

    let fd = open_dir_handle_no_symlinks(abs_dir, None, label)?;
    let st = fstat_fd(fd.as_fd(), label)?;
    let expected_uid = unsafe { libc::geteuid() };
    if st.st_uid != expected_uid {
        return Err(format!(
            "{label} directory owner mismatch before pinning: {}",
            abs_dir.display()
        ));
    }
    if let Some(mode) = expected_mode
        && (st.st_mode as libc::mode_t & 0o777) != mode
    {
        return Err(format!(
            "{label} directory permissions altered before pinning: {}",
            abs_dir.display()
        ));
    }
    if require_empty && !read_dir_entries_from_fd(fd.as_fd(), label)?.is_empty() {
        return Err(format!(
            "{label} directory was not empty before pinning: {}",
            abs_dir.display()
        ));
    }
    // Allow child processes (`ProcessSupervisor`, `cargo miri setup`, `lean`)
    // to access `/proc/self/fd/<fd>` while staying immune to parent-dir
    // renames under `TMPDIR`.
    // SAFETY: `fd` is a live owned directory descriptor; clearing `FD_CLOEXEC`
    // only adjusts its descriptor flag bit.
    let rc = unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_SETFD, 0) };
    if rc != 0 {
        return Err(format!(
            "clear FD_CLOEXEC on {label} dir {}: {}",
            abs_dir.display(),
            io::Error::last_os_error()
        ));
    }
    Ok(fd)
}

#[cfg(target_os = "linux")]
fn proc_fd_subpath(fd: std::os::fd::BorrowedFd<'_>, rel: &Path) -> PathBuf {
    use std::os::fd::AsRawFd as _;
    let base = PathBuf::from(format!("/proc/self/fd/{}", fd.as_raw_fd()));
    if rel.as_os_str().is_empty() { base } else { base.join(rel) }
}

#[cfg(target_os = "linux")]
pub(crate) fn open_pinned_proc_dir_fd(
    pinned_root: &Path,
    label: &str,
) -> Result<std::os::fd::OwnedFd, String> {
    use std::os::fd::{AsFd as _, FromRawFd as _, OwnedFd};

    let rel = pinned_root.strip_prefix("/proc/self/fd").map_err(|_| {
        format!("{label} expected /proc/self/fd/<fd> path: {}", pinned_root.display())
    })?;
    let mut parts = Vec::new();
    for comp in rel.components() {
        match comp {
            Component::CurDir => {}
            Component::Normal(s) => parts.push(s),
            Component::ParentDir | Component::RootDir | Component::Prefix(_) => {
                return Err(format!(
                    "{label} /proc/self/fd subpath must not contain traversal: {}",
                    pinned_root.display()
                ));
            }
        }
    }
    let mut parts_iter = parts.into_iter();
    let fd_os = parts_iter.next().ok_or_else(|| {
        format!("{label} missing /proc/self/fd descriptor: {}", pinned_root.display())
    })?;
    let fd_str = fd_os
        .to_str()
        .filter(|s| !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit()))
        .ok_or_else(|| {
            format!("{label} invalid /proc/self/fd descriptor: {}", pinned_root.display())
        })?;
    let raw_fd: std::os::fd::RawFd =
        fd_str.parse().map_err(|e| format!("{label} parse /proc/self/fd descriptor: {e}"))?;
    if raw_fd <= 2 {
        return Err(format!("{label} /proc/self/fd must not target stdio fd {raw_fd}"));
    }
    // SAFETY: `F_DUPFD_CLOEXEC` probes whether `raw_fd` is an open descriptor
    // and duplicates it safely without taking ownership of `raw_fd`.
    let dup_raw = unsafe { libc::fcntl(raw_fd, libc::F_DUPFD_CLOEXEC, 3) };
    if dup_raw < 0 {
        return Err(format!("dup {label} pinned fd {raw_fd}: {}", io::Error::last_os_error()));
    }
    // SAFETY: `dup_raw` was just allocated by `F_DUPFD_CLOEXEC`.
    let mut cur_fd = unsafe { OwnedFd::from_raw_fd(dup_raw) };
    let root_st = fstat_fd(cur_fd.as_fd(), label)?;
    // SAFETY: `geteuid` takes no pointers and cannot fail.
    let expected_uid = unsafe { libc::geteuid() };
    if !is_dir_mode(&root_st) || root_st.st_uid != expected_uid {
        return Err(format!("{label} pinned dir owner/type mismatch: {}", pinned_root.display()));
    }
    for seg in parts_iter {
        let c_seg = os_str_to_cstring(seg, label)?;
        cur_fd = open_child_dir_nofollow(cur_fd.as_fd(), &c_seg, None, label)?;
    }
    Ok(cur_fd)
}

fn open_verified_rel_file_in(
    root: &Path,
    #[cfg(target_os = "linux")] fd_opt: Option<std::os::fd::BorrowedFd<'_>>,
    rel: &Path,
    label: &str,
) -> Result<File, String> {
    #[cfg(target_os = "linux")]
    if let Some(fd) = fd_opt {
        return open_rel_regular_file_from_fd(fd, rel, false, label);
    }
    crate::mir_eval_runner::validate_executable_no_links(&root.join(rel), root, label)
        .and_then(|canon| open_verified_path_regular_file(&canon, false, label))
}

fn has_rel_dir_in(
    root: &Path,
    #[cfg(target_os = "linux")] fd_opt: Option<std::os::fd::BorrowedFd<'_>>,
    rel: &Path,
    label: &str,
) -> bool {
    #[cfg(target_os = "linux")]
    if let Some(fd) = fd_opt {
        return open_rel_dir_nofollow(fd, rel, label).is_ok();
    }
    root.join(rel).is_dir()
}

fn collect_rel_file_sha256s_in(
    root: &Path,
    #[cfg(target_os = "linux")] fd_opt: Option<std::os::fd::BorrowedFd<'_>>,
    rel_subdir: Option<&Path>,
    skip_rel: Option<&Path>,
    label: &str,
) -> Result<BTreeMap<String, String>, String> {
    #[cfg(target_os = "linux")]
    if let Some(fd) = fd_opt {
        let sub_fd = match rel_subdir {
            Some(sub) => Some(open_rel_dir_nofollow(fd, sub, label)?),
            None => None,
        };
        let target_fd = sub_fd.as_ref().map(|d| d.as_fd_borrowed()).unwrap_or(fd);
        return collect_rel_file_sha256s_from_fd(target_fd, skip_rel, label);
    }
    let target_dir = match rel_subdir {
        Some(sub) => root.join(sub),
        None => root.to_path_buf(),
    };
    collect_rel_file_sha256s_from_dir(&target_dir, skip_rel, label)
}

#[derive(Debug)]
pub(crate) struct ImmutableStagingDir {
    temp: Option<tempfile::TempDir>,
    root: PathBuf,
    #[cfg(target_os = "linux")]
    pinned_root_fd: Option<std::os::fd::OwnedFd>,
}

impl ImmutableStagingDir {
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn root(&self) -> &Path {
        &self.root
    }

    pub(crate) fn build_and_pin<T>(
        temp: tempfile::TempDir,
        label: &str,
        populate: impl FnOnce(&Path, &Path) -> Result<T, String>,
    ) -> Result<(T, Arc<Self>), String> {
        let mut out: Option<T> = None;
        let staging = Self::build_and_pin_with_writable(temp, label, |priv_root, pinned_root| {
            out = Some(populate(priv_root, pinned_root)?);
            Ok(None)
        })?;
        Ok((out.expect("populate closure succeeded without output"), staging))
    }

    pub(crate) fn build_and_pin_with_writable(
        temp: tempfile::TempDir,
        label: &str,
        populate: impl FnOnce(&Path, &Path) -> Result<Option<PathBuf>, String>,
    ) -> Result<Arc<Self>, String> {
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;
            fs::set_permissions(temp.path(), fs::Permissions::from_mode(0o700)).map_err(|e| {
                format!("chmod private {label} staging dir {}: {e}", temp.path().display())
            })?;
        }
        let priv_root = fs::canonicalize(temp.path())
            .map_err(|e| format!("canonicalize private {label} staging dir: {e}"))?;
        #[cfg(target_os = "linux")]
        let pinned_root_fd = Some(open_pinned_cloexec_clear_dir_fd(
            &priv_root,
            Some(0o700),
            true,
            &format!("{label} staging root"),
        )?);
        #[cfg(target_os = "linux")]
        let pinned_root = proc_fd_subpath(
            pinned_root_fd.as_ref().expect("checked Some above").as_fd_borrowed(),
            Path::new(""),
        );
        #[cfg(not(target_os = "linux"))]
        let pinned_root = priv_root.clone();

        let writable_subdir_rel = populate(&priv_root, &pinned_root)?;

        #[cfg(target_os = "linux")]
        {
            let fd_b = pinned_root_fd.as_ref().expect("checked Some above").as_fd_borrowed();
            freeze_staging_dir_from_fd(fd_b, &pinned_root, writable_subdir_rel.as_deref(), label)?;
            let st = fstat_fd(fd_b, label)?;
            if !is_dir_mode(&st) || (st.st_mode as libc::mode_t & 0o777) != 0o555 {
                return Err(format!(
                    "{label} staging root permissions altered after freeze: {}",
                    priv_root.display()
                ));
            }
        }
        #[cfg(not(target_os = "linux"))]
        {
            let writable_abs = writable_subdir_rel.as_deref().map(|rel| priv_root.join(rel));
            freeze_staging_dir_with_writable(&priv_root, writable_abs.as_deref(), label)?;
        }
        Ok(Arc::new(Self {
            temp: Some(temp),
            root: priv_root,
            #[cfg(target_os = "linux")]
            pinned_root_fd,
        }))
    }

    pub(crate) fn pin_path(&self, abs_or_rel: &Path) -> PathBuf {
        #[cfg(target_os = "linux")]
        if let Some(ref fd) = self.pinned_root_fd {
            let rel = if abs_or_rel.is_absolute() {
                match abs_or_rel.strip_prefix(&self.root) {
                    Ok(r) => r,
                    Err(_) => return abs_or_rel.to_path_buf(),
                }
            } else {
                abs_or_rel
            };
            return proc_fd_subpath(fd.as_fd_borrowed(), rel);
        }
        if abs_or_rel.is_absolute() { abs_or_rel.to_path_buf() } else { self.root.join(abs_or_rel) }
    }

    pub(crate) fn pin_root_prefix(&self) -> Option<String> {
        #[cfg(target_os = "linux")]
        if let Some(ref fd) = self.pinned_root_fd {
            use std::os::fd::AsRawFd as _;
            return Some(format!("/proc/self/fd/{}", fd.as_raw_fd()));
        }
        None
    }

    pub(crate) fn resolve_staged_rel(&self, path: &Path) -> Option<PathBuf> {
        let pin_prefix = self.pin_root_prefix();
        let rel = if let Some(ref prefix) = pin_prefix {
            path.strip_prefix(prefix).ok()?
        } else {
            path.strip_prefix(&self.root).ok()?
        };
        let mut clean = PathBuf::new();
        for comp in rel.components() {
            match comp {
                Component::CurDir => {}
                Component::Normal(seg) => {
                    if seg.as_encoded_bytes().contains(&0) {
                        return None;
                    }
                    clean.push(seg);
                }
                Component::Prefix(_) | Component::RootDir | Component::ParentDir => return None,
            }
        }
        (!clean.as_os_str().is_empty()).then_some(clean)
    }

    pub(crate) fn pin_path_with_guards(guards: &[Option<&Arc<Self>>], path: &Path) -> PathBuf {
        for g in guards.iter().flatten() {
            if path.starts_with(&g.root) {
                return g.pin_path(path);
            }
        }
        path.to_path_buf()
    }

    pub(crate) fn pin_env_paths_with_guards(
        guards: &[Option<&Arc<Self>>],
        joined: &OsStr,
    ) -> Result<OsString, String> {
        let mapped: Vec<PathBuf> =
            env::split_paths(joined).map(|p| Self::pin_path_with_guards(guards, &p)).collect();
        env::join_paths(mapped).map_err(|e| format!("join pinned path list: {e}"))
    }

    pub(crate) fn open_verified_rel_file(&self, rel: &Path, label: &str) -> Result<File, String> {
        open_verified_rel_file_in(
            &self.root,
            #[cfg(target_os = "linux")]
            self.pinned_root_fd.as_ref().map(|d| d.as_fd_borrowed()),
            rel,
            label,
        )
    }

    pub(crate) fn has_rel_dir(&self, rel: &Path, label: &str) -> bool {
        has_rel_dir_in(
            &self.root,
            #[cfg(target_os = "linux")]
            self.pinned_root_fd.as_ref().map(|d| d.as_fd_borrowed()),
            rel,
            label,
        )
    }

    pub(crate) fn collect_rel_file_sha256s(
        &self,
        rel_subdir: Option<&Path>,
        skip_rel: Option<&Path>,
        label: &str,
    ) -> Result<BTreeMap<String, String>, String> {
        collect_rel_file_sha256s_in(
            &self.root,
            #[cfg(target_os = "linux")]
            self.pinned_root_fd.as_ref().map(|d| d.as_fd_borrowed()),
            rel_subdir,
            skip_rel,
            label,
        )
    }
}

/// Private mutable `0o700` scratch/build cache root pinned by an empty-verified
/// `O_RDONLY | O_DIRECTORY | O_NOFOLLOW` descriptor (`FD_CLOEXEC` cleared) so
/// concurrent same-user `TMPDIR` parent renames cannot swap the root during
/// Miri sysroot or Lean DAG setup.
#[derive(Debug)]
pub(crate) struct PinnedPrivateDir {
    temp: Option<tempfile::TempDir>,
    root: PathBuf,
    #[cfg(target_os = "linux")]
    pinned_root_fd: Option<std::os::fd::OwnedFd>,
}

impl PinnedPrivateDir {
    pub(crate) fn create(
        prefix: &str,
        tmp_parent: Option<&Path>,
        caller_cwd: &Path,
        label: &str,
    ) -> Result<Self, String> {
        let temp = crate::mir_eval_runner::build_temp_dir(prefix, tmp_parent)?;
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt as _;
            fs::set_permissions(temp.path(), fs::Permissions::from_mode(0o700))
                .map_err(|e| format!("chmod {label} {}: {e}", temp.path().display()))?;
        }
        let root = crate::mir_eval_runner::validate_dir_path_no_symlinks(temp.path(), caller_cwd)?;
        #[cfg(target_os = "linux")]
        let pinned_root_fd =
            Some(open_pinned_cloexec_clear_dir_fd(&root, Some(0o700), true, label)?);
        Ok(Self {
            temp: Some(temp),
            root,
            #[cfg(target_os = "linux")]
            pinned_root_fd,
        })
    }

    pub(crate) fn path(&self) -> PathBuf {
        self.pin_path(Path::new(""))
    }

    pub(crate) fn pin_path(&self, rel: &Path) -> PathBuf {
        #[cfg(target_os = "linux")]
        if let Some(ref fd) = self.pinned_root_fd {
            return proc_fd_subpath(fd.as_fd_borrowed(), rel);
        }
        if rel.as_os_str().is_empty() { self.root.clone() } else { self.root.join(rel) }
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn fs_root(&self) -> &Path {
        &self.root
    }

    pub(crate) fn open_verified_rel_file(&self, rel: &Path, label: &str) -> Result<File, String> {
        open_verified_rel_file_in(
            &self.root,
            #[cfg(target_os = "linux")]
            self.pinned_root_fd.as_ref().map(|d| d.as_fd_borrowed()),
            rel,
            label,
        )
    }

    pub(crate) fn has_rel_dir(&self, rel: &Path, label: &str) -> bool {
        has_rel_dir_in(
            &self.root,
            #[cfg(target_os = "linux")]
            self.pinned_root_fd.as_ref().map(|d| d.as_fd_borrowed()),
            rel,
            label,
        )
    }

    pub(crate) fn collect_rel_file_sha256s(
        &self,
        rel_subdir: Option<&Path>,
        skip_rel: Option<&Path>,
        label: &str,
    ) -> Result<BTreeMap<String, String>, String> {
        collect_rel_file_sha256s_in(
            &self.root,
            #[cfg(target_os = "linux")]
            self.pinned_root_fd.as_ref().map(|d| d.as_fd_borrowed()),
            rel_subdir,
            skip_rel,
            label,
        )
    }

    pub(crate) fn copy_rel_subtree_to(
        &self,
        rel_subdir: &Path,
        dst_root: &Path,
        force_exec: bool,
        label: &str,
    ) -> Result<(), String> {
        #[cfg(target_os = "linux")]
        if let Some(ref fd) = self.pinned_root_fd {
            use std::os::fd::AsFd as _;
            let sub_fd = open_rel_dir_nofollow(fd.as_fd_borrowed(), rel_subdir, label)?;
            return copy_validated_subtree_from_fd_with_filter(
                sub_fd.as_fd(),
                &self.pin_path(rel_subdir),
                dst_root,
                None,
                force_exec,
                label,
                |_, _, _| false,
            );
        }
        copy_validated_subtree(&self.root.join(rel_subdir), dst_root, None, force_exec, label)
    }
}

impl Drop for PinnedPrivateDir {
    fn drop(&mut self) {
        #[cfg(target_os = "linux")]
        drop(self.pinned_root_fd.take());
        drop(self.temp.take());
    }
}

#[cfg(target_os = "linux")]
trait BorrowedFdExt {
    fn as_fd_borrowed(&self) -> std::os::fd::BorrowedFd<'_>;
}

#[cfg(target_os = "linux")]
impl BorrowedFdExt for std::os::fd::OwnedFd {
    fn as_fd_borrowed(&self) -> std::os::fd::BorrowedFd<'_> {
        std::os::fd::AsFd::as_fd(self)
    }
}

#[cfg(unix)]
pub(crate) fn restore_dir_write_perms_top_down(root: &Path) {
    use std::os::unix::fs::PermissionsExt as _;
    let mut stack = vec![root.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let _ = fs::set_permissions(&dir, fs::Permissions::from_mode(0o700));
        if let Ok(entries) = fs::read_dir(&dir) {
            for entry in entries.flatten() {
                let path = entry.path();
                if let Ok(meta) = fs::symlink_metadata(&path)
                    && !meta.file_type().is_symlink()
                    && meta.is_dir()
                {
                    stack.push(path);
                }
            }
        }
    }
}

#[cfg(not(unix))]
fn restore_dir_write_perms_top_down(_root: &Path) {}

impl Drop for ImmutableStagingDir {
    fn drop(&mut self) {
        #[cfg(target_os = "linux")]
        drop(self.pinned_root_fd.take());
        if let Some(temp) = self.temp.take() {
            restore_dir_write_perms_top_down(temp.path());
            drop(temp);
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct PreparedSysroot {
    pub(crate) sysroot: PathBuf,
    pub(crate) binary: PathBuf,
    pub(crate) ld_library_path: String,
    pub(crate) _staging: Option<Arc<ImmutableStagingDir>>,
}

#[derive(Clone, Debug)]
pub(crate) struct PreparedToolchainLibs {
    pub(crate) ld_library_path: String,
    pub(crate) _staging: Option<Arc<ImmutableStagingDir>>,
}

#[derive(Clone, Debug)]
pub(crate) struct PreparedLeanLibs {
    pub(crate) lean_bin: PathBuf,
    pub(crate) bin_dir: PathBuf,
    pub(crate) ld_library_path: String,
    pub(crate) lib_lean_dir: Option<PathBuf>,
    pub(crate) source_lib_lean_dir: Option<PathBuf>,
    pub(crate) _staging: Option<Arc<ImmutableStagingDir>>,
}

#[cfg(unix)]
pub(crate) struct VerifiedDirEntry {
    pub(crate) c_name: CString,
    pub(crate) os_name: OsString,
    pub(crate) stat: libc::stat,
}

#[cfg(unix)]
struct DirStreamGuard(*mut libc::DIR);

#[cfg(unix)]
impl Drop for DirStreamGuard {
    fn drop(&mut self) {
        if !self.0.is_null() {
            // SAFETY: `self.0` came from `libc::fdopendir` and is unclosed.
            unsafe {
                libc::closedir(self.0);
            }
        }
    }
}

#[cfg(unix)]
fn clear_errno() {
    #[cfg(any(target_os = "linux", target_os = "android"))]
    // SAFETY: `__errno_location()` yields thread-local errno on Linux/Android.
    unsafe {
        *libc::__errno_location() = 0;
    }
    #[cfg(any(target_os = "macos", target_os = "ios", target_os = "freebsd"))]
    // SAFETY: `__error()` yields thread-local errno pointer on Apple/BSD.
    unsafe {
        *libc::__error() = 0;
    }
}

#[cfg(unix)]
pub(crate) fn os_str_to_cstring(seg: &OsStr, label: &str) -> Result<CString, String> {
    use std::os::unix::ffi::OsStrExt as _;
    CString::new(seg.as_bytes())
        .map_err(|e| format!("{label} contains interior NUL byte ({seg:?}): {e}"))
}

#[cfg(unix)]
fn fstat_fd(fd: std::os::fd::BorrowedFd<'_>, label: &str) -> Result<libc::stat, String> {
    use std::os::fd::AsRawFd as _;
    let mut st = std::mem::MaybeUninit::<libc::stat>::uninit();
    // SAFETY: `fd` is a valid open descriptor and `st.as_mut_ptr()` is aligned.
    if unsafe { libc::fstat(fd.as_raw_fd(), st.as_mut_ptr()) } != 0 {
        return Err(format!("fstat {label}: {}", io::Error::last_os_error()));
    }
    // SAFETY: `libc::fstat` returned 0 and initialized `st`.
    Ok(unsafe { st.assume_init() })
}

#[cfg(unix)]
pub(crate) fn is_dir_mode(st: &libc::stat) -> bool {
    (st.st_mode & libc::S_IFMT) == libc::S_IFDIR
}

#[cfg(unix)]
pub(crate) fn is_reg_mode(st: &libc::stat) -> bool {
    (st.st_mode & libc::S_IFMT) == libc::S_IFREG
}

#[cfg(unix)]
pub(crate) fn is_lnk_mode(st: &libc::stat) -> bool {
    (st.st_mode & libc::S_IFMT) == libc::S_IFLNK
}

#[cfg(unix)]
#[allow(clippy::unnecessary_cast)]
pub(crate) fn stat_dev_ino(st: &libc::stat) -> (u64, u64) {
    (st.st_dev as u64, st.st_ino as u64)
}

#[cfg(unix)]
#[allow(clippy::unnecessary_cast)]
pub(crate) fn stat_nlink(st: &libc::stat) -> u64 {
    st.st_nlink as u64
}

#[cfg(unix)]
pub(crate) fn open_child_dir_nofollow(
    parent: std::os::fd::BorrowedFd<'_>,
    name: &CStr,
    expected_dev_ino: Option<(u64, u64)>,
    label: &str,
) -> Result<std::os::fd::OwnedFd, String> {
    use std::os::fd::{AsFd as _, AsRawFd as _, FromRawFd as _, OwnedFd};
    let bytes = name.to_bytes();
    if bytes.is_empty() || bytes == b"." || bytes == b".." || bytes.contains(&b'/') {
        return Err(format!("{label} directory segment must not traverse: {:?}", name));
    }
    let flags = libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC;
    // SAFETY: `parent` is an open dir fd and `name` is a NUL-terminated CStr.
    let raw = unsafe { libc::openat(parent.as_raw_fd(), name.as_ptr(), flags) };
    if raw < 0 {
        let err = io::Error::last_os_error();
        let mut is_sym = err.raw_os_error() == Some(libc::ELOOP);
        if !is_sym && err.raw_os_error() == Some(libc::ENOTDIR) {
            let mut st = std::mem::MaybeUninit::<libc::stat>::uninit();
            // SAFETY: `parent` is open and `name` is NUL-terminated.
            if unsafe {
                libc::fstatat(
                    parent.as_raw_fd(),
                    name.as_ptr(),
                    st.as_mut_ptr(),
                    libc::AT_SYMLINK_NOFOLLOW,
                )
            } == 0
            {
                // SAFETY: `fstatat` succeeded and initialized `st`.
                let st_init = unsafe { st.assume_init() };
                is_sym = is_lnk_mode(&st_init);
            }
        }
        return Err(if is_sym {
            format!("{label} must not be or traverse a symlink: {:?}", name)
        } else {
            format!("open {label} {:?}: {err}", name)
        });
    }
    // SAFETY: `raw` is a freshly opened non-negative file descriptor.
    let fd = unsafe { OwnedFd::from_raw_fd(raw) };
    let st = fstat_fd(fd.as_fd(), label)?;
    if !is_dir_mode(&st) {
        return Err(format!("{label} is not a directory: {:?}", name));
    }
    if let Some((exp_dev, exp_ino)) = expected_dev_ino
        && stat_dev_ino(&st) != (exp_dev, exp_ino)
    {
        return Err(format!("{label} directory changed identity during traversal: {:?}", name));
    }
    Ok(fd)
}

#[cfg(unix)]
pub(crate) fn open_dir_handle_no_symlinks(
    abs_dir: &Path,
    expected_dev_ino: Option<(u64, u64)>,
    label: &str,
) -> Result<std::os::fd::OwnedFd, String> {
    use std::os::fd::{AsFd as _, FromRawFd as _, OwnedFd};
    if !abs_dir.is_absolute() {
        return Err(format!("{label} must be an absolute path: {}", abs_dir.display()));
    }
    let root_c = CString::new("/").expect("static string has no NUL");
    let root_flags = libc::O_RDONLY | libc::O_DIRECTORY | libc::O_NOFOLLOW | libc::O_CLOEXEC;
    // SAFETY: opening `/` with O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC.
    let raw_root = unsafe { libc::open(root_c.as_ptr(), root_flags) };
    if raw_root < 0 {
        return Err(format!("open `/` for {label}: {}", io::Error::last_os_error()));
    }
    // SAFETY: `raw_root` is a freshly opened valid descriptor.
    let mut cur_fd = unsafe { OwnedFd::from_raw_fd(raw_root) };
    for comp in abs_dir.components() {
        match comp {
            Component::RootDir | Component::CurDir => {}
            Component::ParentDir | Component::Prefix(_) => {
                return Err(format!(
                    "{label} must not contain `..` or unsupported prefix: {}",
                    abs_dir.display()
                ));
            }
            Component::Normal(seg) => {
                let c_seg = os_str_to_cstring(seg, label)?;
                cur_fd = open_child_dir_nofollow(cur_fd.as_fd(), &c_seg, None, label)
                    .map_err(|e| format!("{e} (under {})", abs_dir.display()))?;
            }
        }
    }
    let st = fstat_fd(cur_fd.as_fd(), label)?;
    if !is_dir_mode(&st) {
        return Err(format!("{label} is not a directory: {}", abs_dir.display()));
    }
    if let Some((exp_dev, exp_ino)) = expected_dev_ino
        && stat_dev_ino(&st) != (exp_dev, exp_ino)
    {
        return Err(format!(
            "{label} directory changed identity before open: {}",
            abs_dir.display()
        ));
    }
    Ok(cur_fd)
}

#[cfg(unix)]
pub(crate) fn open_rel_dir_nofollow(
    base_fd: std::os::fd::BorrowedFd<'_>,
    rel_dir: &Path,
    label: &str,
) -> Result<std::os::fd::OwnedFd, String> {
    use std::os::fd::{AsFd as _, AsRawFd as _, FromRawFd as _, OwnedFd};
    // SAFETY: `base_fd` is an open directory fd; `F_DUPFD_CLOEXEC` duplicates
    // it safely.
    let dup = unsafe { libc::fcntl(base_fd.as_raw_fd(), libc::F_DUPFD_CLOEXEC, 0) };
    if dup < 0 {
        return Err(format!("dup {label} dir fd: {}", io::Error::last_os_error()));
    }
    // SAFETY: `dup` is a freshly duplicated valid descriptor.
    let mut cur_fd = unsafe { OwnedFd::from_raw_fd(dup) };
    for comp in rel_dir.components() {
        match comp {
            Component::CurDir => {}
            Component::Normal(seg) => {
                let c_seg = os_str_to_cstring(seg, label)?;
                cur_fd = open_child_dir_nofollow(cur_fd.as_fd(), &c_seg, None, label)?;
            }
            _ => {
                return Err(format!(
                    "{label} relative subdir must be normal path: {}",
                    rel_dir.display()
                ));
            }
        }
    }
    Ok(cur_fd)
}

#[cfg(unix)]
pub(crate) fn read_dir_entries_from_fd(
    dir_fd: std::os::fd::BorrowedFd<'_>,
    label: &str,
) -> Result<Vec<VerifiedDirEntry>, String> {
    use std::os::{fd::AsRawFd as _, unix::ffi::OsStrExt as _};

    // SAFETY: `dir_fd` is a valid directory descriptor.
    let dup = unsafe { libc::fcntl(dir_fd.as_raw_fd(), libc::F_DUPFD_CLOEXEC, 0) };
    if dup < 0 {
        return Err(format!("dup dir fd for {label}: {}", io::Error::last_os_error()));
    }
    // SAFETY: `dup` was just created; `fdopendir` takes ownership on success.
    let dir_ptr = unsafe { libc::fdopendir(dup) };
    if dir_ptr.is_null() {
        let err = io::Error::last_os_error();
        // SAFETY: `fdopendir` failed so we must close `dup` ourselves.
        unsafe {
            libc::close(dup);
        }
        return Err(format!("fdopendir {label}: {err}"));
    }
    let _guard = DirStreamGuard(dir_ptr);
    // Reset shared open-file-description directory offset after any prior
    // `dup`/inspection reads on the same descriptor (e.g. emptiness checks).
    // SAFETY: `dir_ptr` is an open valid `DIR*`.
    unsafe {
        libc::rewinddir(dir_ptr);
    }
    let mut out = Vec::new();
    loop {
        clear_errno();
        // SAFETY: `dir_ptr` is an open `DIR*` owned uniquely by this loop.
        let ent = unsafe { libc::readdir(dir_ptr) };
        if ent.is_null() {
            let err = io::Error::last_os_error();
            if err.raw_os_error().unwrap_or(0) != 0 {
                return Err(format!("readdir {label}: {err}"));
            }
            break;
        }
        // SAFETY: `ent` is non-null and `d_name` is a NUL-terminated buffer.
        let c_name = unsafe { CStr::from_ptr((*ent).d_name.as_ptr()) }.to_owned();
        let bytes = c_name.as_bytes();
        if bytes == b"." || bytes == b".." {
            continue;
        }
        let mut st = std::mem::MaybeUninit::<libc::stat>::uninit();
        // SAFETY: `dir_fd` is open, `c_name` is NUL-terminated, `st` is valid.
        if unsafe {
            libc::fstatat(
                dir_fd.as_raw_fd(),
                c_name.as_ptr(),
                st.as_mut_ptr(),
                libc::AT_SYMLINK_NOFOLLOW,
            )
        } != 0
        {
            return Err(format!("fstatat {label} {:?}: {}", c_name, io::Error::last_os_error()));
        }
        // SAFETY: `fstatat` succeeded and initialized `st`.
        let stat = unsafe { st.assume_init() };
        let os_name = OsStr::from_bytes(bytes).to_os_string();
        out.push(VerifiedDirEntry { c_name, os_name, stat });
    }
    out.sort_by(|a, b| a.os_name.cmp(&b.os_name));
    Ok(out)
}

#[cfg(unix)]
pub(crate) fn open_regular_file_from_fd(
    dir_fd: std::os::fd::BorrowedFd<'_>,
    name: &CStr,
    expected_dev_ino: Option<(u64, u64)>,
    allow_hardlink: bool,
    label: &str,
) -> Result<(File, libc::stat), String> {
    use std::os::fd::{AsRawFd as _, FromRawFd as _, OwnedFd};
    let flags = libc::O_RDONLY | libc::O_NOFOLLOW | libc::O_CLOEXEC;
    // SAFETY: `dir_fd` is open and `name` is NUL-terminated.
    let raw = unsafe { libc::openat(dir_fd.as_raw_fd(), name.as_ptr(), flags) };
    if raw < 0 {
        let err = io::Error::last_os_error();
        return Err(if err.raw_os_error() == Some(libc::ELOOP) {
            format!("{label} must not be a symlink: {:?}", name)
        } else {
            format!("open {label} {:?}: {err}", name)
        });
    }
    // SAFETY: `raw` is a freshly opened valid descriptor.
    let owned = unsafe { OwnedFd::from_raw_fd(raw) };
    let file = File::from(owned);
    let mut st = std::mem::MaybeUninit::<libc::stat>::uninit();
    // SAFETY: `file` is open and `st` is writable.
    if unsafe { libc::fstat(file.as_raw_fd(), st.as_mut_ptr()) } != 0 {
        return Err(format!("fstat {label} {:?}: {}", name, io::Error::last_os_error()));
    }
    // SAFETY: `fstat` succeeded.
    let st = unsafe { st.assume_init() };
    if !is_reg_mode(&st) {
        return Err(format!("{label} is not a regular file: {:?}", name));
    }
    if !allow_hardlink && stat_nlink(&st) > 1 {
        return Err(format!(
            "{label} file must not be a hardlink (nlink={}): {:?}",
            st.st_nlink, name
        ));
    }
    if let Some((exp_dev, exp_ino)) = expected_dev_ino
        && stat_dev_ino(&st) != (exp_dev, exp_ino)
    {
        return Err(format!("{label} inode changed between validation and open: {:?}", name));
    }
    Ok((file, st))
}

#[cfg(unix)]
fn open_rel_regular_file_from_fd(
    root_fd: std::os::fd::BorrowedFd<'_>,
    rel_path: &Path,
    allow_hardlink: bool,
    label: &str,
) -> Result<File, String> {
    use std::os::fd::AsFd as _;
    let mut comps = Vec::new();
    for comp in rel_path.components() {
        match comp {
            Component::CurDir => {}
            Component::Normal(seg) => comps.push(os_str_to_cstring(seg, label)?),
            _ => {
                return Err(format!(
                    "{label} must be relative without `..`: {}",
                    rel_path.display()
                ));
            }
        }
    }
    let Some((leaf, parents)) = comps.split_last() else {
        return Err(format!("{label} empty relative file path"));
    };
    let mut cur_opt: Option<std::os::fd::OwnedFd> = None;
    for dir_seg in parents {
        let cur_b = cur_opt.as_ref().map(|d| d.as_fd()).unwrap_or(root_fd);
        cur_opt = Some(open_child_dir_nofollow(cur_b, dir_seg, None, label)?);
    }
    let parent_b = cur_opt.as_ref().map(|d| d.as_fd()).unwrap_or(root_fd);
    let (file, _) = open_regular_file_from_fd(parent_b, leaf, None, allow_hardlink, label)?;
    Ok(file)
}

#[cfg(unix)]
fn readlink_from_fd(
    dir_fd: std::os::fd::BorrowedFd<'_>,
    name: &CStr,
    label: &str,
) -> Result<PathBuf, String> {
    use std::os::{fd::AsRawFd as _, unix::ffi::OsStringExt as _};
    let mut cap = 256usize;
    loop {
        let mut buf = vec![0u8; cap];
        // SAFETY: `dir_fd` is open, `name` is NUL-terminated, `buf` holds
        // `cap` bytes.
        let n = unsafe {
            libc::readlinkat(
                dir_fd.as_raw_fd(),
                name.as_ptr(),
                buf.as_mut_ptr().cast::<libc::c_char>(),
                buf.len(),
            )
        };
        if n < 0 {
            return Err(format!("readlinkat {label} {:?}: {}", name, io::Error::last_os_error()));
        }
        let n = n as usize;
        if n < buf.len() {
            buf.truncate(n);
            return Ok(PathBuf::from(OsString::from_vec(buf)));
        }
        if cap >= 65536 {
            return Err(format!("{label} symlink target exceeds maximum length: {:?}", name));
        }
        cap *= 2;
    }
}

#[cfg(unix)]
fn resolve_and_open_confined_lib_symlink_from_fd(
    root_fd: std::os::fd::BorrowedFd<'_>,
    cur_fd: std::os::fd::BorrowedFd<'_>,
    cur_rel_segs: &[OsString],
    link_c_name: &CStr,
    link_display: &Path,
    label: &str,
) -> Result<(File, libc::stat), String> {
    use std::os::fd::{AsFd as _, AsRawFd as _};

    enum HopDir {
        Initial,
        Root,
        Owned(std::os::fd::OwnedFd),
    }

    let mut hop_dir = HopDir::Initial;
    let mut hop_rel_segs: Vec<OsString> = cur_rel_segs.to_vec();
    let mut hop_c_name: CString = link_c_name.to_owned();
    for _ in 0..MAX_LINKER_SYMLINK_HOPS {
        let active_dir_b = match &hop_dir {
            HopDir::Initial => cur_fd,
            HopDir::Root => root_fd,
            HopDir::Owned(fd) => fd.as_fd(),
        };
        let raw_target = readlink_from_fd(active_dir_b, &hop_c_name, label)?;
        if raw_target.is_absolute() {
            return Err(format!(
                "{label} must not contain an absolute symlink: {} -> {}",
                link_display.display(),
                raw_target.display()
            ));
        }
        let mut target_segs = hop_rel_segs;
        for comp in raw_target.components() {
            match comp {
                Component::CurDir => {}
                Component::ParentDir => {
                    if target_segs.pop().is_none() {
                        return Err(format!(
                            "{label} symlink escaped {label}: {} -> {}",
                            link_display.display(),
                            raw_target.display()
                        ));
                    }
                }
                Component::Normal(seg) => target_segs.push(seg.to_os_string()),
                Component::Prefix(_) | Component::RootDir => {
                    return Err(format!(
                        "{label} must not contain an absolute symlink: {} -> {}",
                        link_display.display(),
                        raw_target.display()
                    ));
                }
            }
        }
        if target_segs.is_empty() {
            return Err(format!(
                "{label} symlink targets {label} root: {} -> {}",
                link_display.display(),
                raw_target.display()
            ));
        }
        let (leaf_os, dir_segs) = target_segs.split_last().expect("non-empty checked above");
        let mut walk_fd: Option<std::os::fd::OwnedFd> = None;
        for seg in dir_segs {
            let c_seg = os_str_to_cstring(seg, label)?;
            let parent_b = walk_fd.as_ref().map(|d| d.as_fd()).unwrap_or(root_fd);
            walk_fd =
                Some(open_child_dir_nofollow(parent_b, &c_seg, None, label).map_err(|_| {
                    format!(
                        "{label} symlink must resolve to a regular file inside {label}: {}",
                        link_display.display()
                    )
                })?);
        }
        let target_dir_b = walk_fd.as_ref().map(|d| d.as_fd()).unwrap_or(root_fd);
        let leaf_c = os_str_to_cstring(leaf_os, label)?;
        let mut st = std::mem::MaybeUninit::<libc::stat>::uninit();
        // SAFETY: `target_dir_b` is open and `leaf_c` is NUL-terminated.
        if unsafe {
            libc::fstatat(
                target_dir_b.as_raw_fd(),
                leaf_c.as_ptr(),
                st.as_mut_ptr(),
                libc::AT_SYMLINK_NOFOLLOW,
            )
        } != 0
        {
            return Err(format!(
                "stat {label} target of {}: {}",
                link_display.display(),
                io::Error::last_os_error()
            ));
        }
        // SAFETY: `fstatat` succeeded.
        let st = unsafe { st.assume_init() };
        if is_lnk_mode(&st) {
            if stat_nlink(&st) > 1 {
                return Err(format!(
                    "{label} symlink target must not be a hardlink (nlink={}): {}",
                    st.st_nlink,
                    link_display.display()
                ));
            }
            hop_rel_segs = dir_segs.to_vec();
            hop_dir = match walk_fd {
                Some(fd) => HopDir::Owned(fd),
                None => HopDir::Root,
            };
            hop_c_name = leaf_c;
            continue;
        }
        if !is_reg_mode(&st) {
            return Err(format!(
                "{label} symlink must resolve to a regular file inside {label}: {}",
                link_display.display()
            ));
        }
        if stat_nlink(&st) > 1 {
            return Err(format!(
                "{label} symlink target must not be a hardlink (nlink={}): {}",
                st.st_nlink,
                link_display.display()
            ));
        }
        return open_regular_file_from_fd(
            target_dir_b,
            &leaf_c,
            Some(stat_dev_ino(&st)),
            false,
            label,
        );
    }
    Err(format!(
        "{label} exceeded {MAX_LINKER_SYMLINK_HOPS} symlink hops: {}",
        link_display.display()
    ))
}

pub(crate) fn sha256_opened_file_hex(file: &mut File, label: &str) -> Result<String, String> {
    let mut h = Sha256::new();
    let mut buf = [0u8; 65536];
    loop {
        let n = match file.read(&mut buf) {
            Ok(0) => break,
            Ok(n) => n,
            Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
            Err(e) => return Err(format!("read {label}: {e}")),
        };
        h.update(&buf[..n]);
    }
    Ok(format!("{:x}", h.finalize()))
}

#[cfg(unix)]
pub(crate) fn collect_rel_file_sha256s_from_fd(
    root_fd: std::os::fd::BorrowedFd<'_>,
    skip_rel: Option<&Path>,
    label: &str,
) -> Result<BTreeMap<String, String>, String> {
    use std::os::fd::{AsFd as _, OwnedFd};

    let mut out = BTreeMap::new();
    let mut stack: Vec<(Option<OwnedFd>, PathBuf)> = vec![(None, PathBuf::new())];
    while let Some((dir_opt, rel_prefix)) = stack.pop() {
        let cur_b = dir_opt.as_ref().map(|d| d.as_fd()).unwrap_or(root_fd);
        let entries = read_dir_entries_from_fd(cur_b, label)?;
        for entry in entries {
            let next_rel = rel_prefix.join(&entry.os_name);
            if skip_rel.is_some_and(|s| s == next_rel) {
                continue;
            }
            if is_lnk_mode(&entry.stat) {
                return Err(format!("{label} must not contain a symlink: {}", next_rel.display()));
            }
            if is_dir_mode(&entry.stat) {
                let child = open_child_dir_nofollow(
                    cur_b,
                    &entry.c_name,
                    Some(stat_dev_ino(&entry.stat)),
                    label,
                )?;
                stack.push((Some(child), next_rel));
            } else if is_reg_mode(&entry.stat) {
                let mut f = open_regular_file_from_fd(
                    cur_b,
                    &entry.c_name,
                    Some(stat_dev_ino(&entry.stat)),
                    false,
                    label,
                )?
                .0;
                let rel_key = path_slashes_utf8(&next_rel, label)?;
                let sha =
                    sha256_opened_file_hex(&mut f, &format!("{label} {}", next_rel.display()))?;
                out.insert(rel_key, sha);
            } else {
                return Err(format!("{label} contains non-regular entry: {}", next_rel.display()));
            }
        }
    }
    Ok(out)
}

pub(crate) fn path_slashes_utf8(rel: &Path, label: &str) -> Result<String, String> {
    let mut segs = Vec::new();
    for comp in rel.components() {
        let Component::Normal(os) = comp else {
            return Err(format!("unexpected relative component in {label}: {}", rel.display()));
        };
        let s =
            os.to_str().ok_or_else(|| format!("non-UTF-8 path in {label}: {}", rel.display()))?;
        segs.push(s);
    }
    Ok(segs.join("/"))
}

#[cfg_attr(target_os = "linux", allow(dead_code))]
fn collect_rel_file_sha256s_from_dir(
    root_dir: &Path,
    skip_rel: Option<&Path>,
    label: &str,
) -> Result<BTreeMap<String, String>, String> {
    validate_dir_tree_no_links(root_dir, label)?;
    let mut out = BTreeMap::new();
    let mut stack = vec![root_dir.to_path_buf()];
    while let Some(cur_dir) = stack.pop() {
        let mut entries: Vec<_> = fs::read_dir(&cur_dir)
            .map_err(|e| format!("read {label} dir {}: {e}", cur_dir.display()))?
            .collect::<Result<Vec<_>, _>>()
            .map_err(|e| format!("iterate {label} dir {}: {e}", cur_dir.display()))?;
        entries.sort_by_key(|e| e.file_name());
        for entry in entries {
            let path = entry.path();
            let meta = fs::symlink_metadata(&path)
                .map_err(|e| format!("stat {label} {}: {e}", path.display()))?;
            if meta.is_dir() {
                stack.push(path);
            } else if meta.is_file() {
                let rel = path
                    .strip_prefix(root_dir)
                    .map_err(|e| format!("relative {label} path {}: {e}", path.display()))?;
                if skip_rel.is_some_and(|s| s == rel) {
                    continue;
                }
                let mut f = open_verified_path_regular_file(&path, false, label)?;
                let sha = sha256_opened_file_hex(&mut f, &format!("{label} {}", path.display()))?;
                out.insert(path_slashes_utf8(rel, label)?, sha);
            }
        }
    }
    Ok(out)
}

#[cfg(unix)]
pub(crate) fn collect_rel_file_sha256s_nofollow(
    dir_path: &Path,
    skip_rel: Option<&Path>,
    label: &str,
) -> Result<BTreeMap<String, String>, String> {
    use std::os::fd::AsFd as _;
    let fd = open_dir_handle_no_symlinks(dir_path, None, label)?;
    collect_rel_file_sha256s_from_fd(fd.as_fd(), skip_rel, label)
}

#[cfg(not(unix))]
pub(crate) fn collect_rel_file_sha256s_nofollow(
    dir_path: &Path,
    skip_rel: Option<&Path>,
    label: &str,
) -> Result<BTreeMap<String, String>, String> {
    collect_rel_file_sha256s_from_dir(dir_path, skip_rel, label)
}

#[cfg_attr(target_os = "linux", allow(dead_code))]
fn open_verified_path_regular_file(
    src_path: &Path,
    allow_hardlink: bool,
    label: &str,
) -> Result<File, String> {
    let lstat = fs::symlink_metadata(src_path)
        .map_err(|e| format!("stat {label} {}: {e}", src_path.display()))?;
    if lstat.file_type().is_symlink() || !lstat.is_file() {
        return Err(format!("{label} is not a regular file: {}", src_path.display()));
    }
    let nlink = hardlink_count(&lstat);
    if !allow_hardlink && nlink > 1 {
        return Err(format!(
            "{label} file must not be a hardlink (nlink={nlink}): {}",
            src_path.display()
        ));
    }
    File::open(src_path).map_err(|e| format!("open {label} {}: {e}", src_path.display()))
}

#[cfg(not(unix))]
fn resolve_confined_lib_symlink(
    canon_lib: &Path,
    cur_dir: &Path,
    path: &Path,
    label: &str,
) -> Result<PathBuf, String> {
    let raw_target =
        fs::read_link(path).map_err(|e| format!("readlink {label} {}: {e}", path.display()))?;
    if raw_target.is_absolute() {
        return Err(format!(
            "{label} must not contain an absolute symlink: {} -> {}",
            path.display(),
            raw_target.display()
        ));
    }
    let mut cur_lex = cur_dir.to_path_buf();
    for comp in raw_target.components() {
        match comp {
            Component::CurDir => {}
            Component::ParentDir => {
                if !cur_lex.pop() || !cur_lex.starts_with(canon_lib) {
                    return Err(format!(
                        "{label} symlink escaped {label}: {} -> {}",
                        path.display(),
                        raw_target.display()
                    ));
                }
            }
            Component::Normal(seg) => cur_lex.push(seg),
            Component::Prefix(_) | Component::RootDir => {
                return Err(format!(
                    "{label} must not contain an absolute symlink: {} -> {}",
                    path.display(),
                    raw_target.display()
                ));
            }
        }
    }
    if cur_lex == canon_lib {
        return Err(format!(
            "{label} symlink targets {label} root: {} -> {}",
            path.display(),
            raw_target.display()
        ));
    }
    let canon_target = fs::canonicalize(path)
        .map_err(|e| format!("canonicalize {label} {}: {e}", path.display()))?;
    if !canon_target.starts_with(canon_lib) || canon_target == canon_lib {
        return Err(format!(
            "{label} symlink escaped {label}: {} -> {}",
            path.display(),
            canon_target.display()
        ));
    }
    let canon_meta = fs::symlink_metadata(&canon_target)
        .map_err(|e| format!("stat {label} {}: {e}", canon_target.display()))?;
    if canon_meta.file_type().is_symlink() || !canon_meta.is_file() {
        return Err(format!(
            "{label} symlink must resolve to a regular file inside {label}: {}",
            path.display()
        ));
    }
    let target_nlink = hardlink_count(&canon_meta);
    if target_nlink > 1 {
        return Err(format!(
            "{label} symlink target must not be a hardlink (nlink={target_nlink}): {}",
            canon_target.display()
        ));
    }
    Ok(canon_target)
}

/// Inspect a non-store `lib/` tree (`nlink == 1` regular files and confined
/// relative file symlinks only) through no-follow directory handles so no
/// intermediate directory can be swapped for a symlink mid-walk.
fn inspect_sysroot_lib_dir_tree(
    canon_lib: &Path,
    allow_subdir_symlinks: bool,
    label: &str,
) -> Result<bool, String> {
    #[cfg(unix)]
    {
        use std::os::fd::AsFd as _;

        let root_fd = open_dir_handle_no_symlinks(canon_lib, None, label)?;
        let mut stack: Vec<(Option<std::os::fd::OwnedFd>, Vec<OsString>, PathBuf)> =
            vec![(None, Vec::new(), canon_lib.to_path_buf())];
        let mut has_symlinks = false;
        while let Some((dir_opt, rel_segs, cur_display)) = stack.pop() {
            let cur_fd = dir_opt.as_ref().map(|d| d.as_fd()).unwrap_or_else(|| root_fd.as_fd());
            let entries = read_dir_entries_from_fd(cur_fd, label)?;
            for entry in entries {
                let path = cur_display.join(&entry.os_name);
                if is_lnk_mode(&entry.stat) {
                    if !allow_subdir_symlinks && !rel_segs.is_empty() {
                        return Err(format!(
                            "{label} must not contain symlink in subdirectory: {}",
                            path.display()
                        ));
                    }
                    if stat_nlink(&entry.stat) > 1 {
                        return Err(format!(
                            "{label} symlink must not be a hardlink (nlink={}): {}",
                            entry.stat.st_nlink,
                            path.display()
                        ));
                    }
                    let _ = resolve_and_open_confined_lib_symlink_from_fd(
                        root_fd.as_fd(),
                        cur_fd,
                        &rel_segs,
                        &entry.c_name,
                        &path,
                        label,
                    )?;
                    has_symlinks = true;
                } else if is_dir_mode(&entry.stat) {
                    let child_fd = open_child_dir_nofollow(
                        cur_fd,
                        &entry.c_name,
                        Some(stat_dev_ino(&entry.stat)),
                        label,
                    )?;
                    let mut next_segs = rel_segs.clone();
                    next_segs.push(entry.os_name);
                    stack.push((Some(child_fd), next_segs, path));
                } else if is_reg_mode(&entry.stat) {
                    if stat_nlink(&entry.stat) > 1 {
                        return Err(format!(
                            "{label} file must not be a hardlink (nlink={}): {}",
                            entry.stat.st_nlink,
                            path.display()
                        ));
                    }
                } else {
                    return Err(format!("{label} contains non-regular entry: {}", path.display()));
                }
            }
        }
        Ok(has_symlinks)
    }

    #[cfg(not(unix))]
    {
        let mut stack = vec![canon_lib.to_path_buf()];
        let mut has_symlinks = false;
        while let Some(cur_dir) = stack.pop() {
            let mut entries: Vec<_> = fs::read_dir(&cur_dir)
                .map_err(|e| format!("read {label} dir {}: {e}", cur_dir.display()))?
                .collect::<Result<Vec<_>, _>>()
                .map_err(|e| format!("iterate {label} dir {}: {e}", cur_dir.display()))?;
            entries.sort_by_key(|e| e.file_name());
            for entry in entries {
                let path = entry.path();
                let meta = fs::symlink_metadata(&path)
                    .map_err(|e| format!("stat {label} {}: {e}", path.display()))?;
                if meta.file_type().is_symlink() {
                    if !allow_subdir_symlinks && cur_dir != canon_lib {
                        return Err(format!(
                            "{label} must not contain symlink in subdirectory: {}",
                            path.display()
                        ));
                    }
                    let nlink = hardlink_count(&meta);
                    if nlink > 1 {
                        return Err(format!(
                            "{label} symlink must not be a hardlink (nlink={nlink}): {}",
                            path.display()
                        ));
                    }
                    let _ = resolve_confined_lib_symlink(canon_lib, &cur_dir, &path, label)?;
                    has_symlinks = true;
                } else if meta.is_dir() {
                    stack.push(path);
                } else if meta.is_file() {
                    let nlink = hardlink_count(&meta);
                    if nlink > 1 {
                        return Err(format!(
                            "{label} file must not be a hardlink (nlink={nlink}): {}",
                            path.display()
                        ));
                    }
                } else {
                    return Err(format!("{label} contains non-regular entry: {}", path.display()));
                }
            }
        }
        Ok(has_symlinks)
    }
}

pub(crate) fn copy_opened_file_to_new_dst(
    src_file: &mut File,
    src_exec: bool,
    dst_path: &Path,
    force_exec: bool,
    label: &str,
) -> Result<(), String> {
    let mut dst_file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(dst_path)
        .map_err(|e| format!("create staged {label} {}: {e}", dst_path.display()))?;
    io::copy(src_file, &mut dst_file)
        .map_err(|e| format!("copy {label} -> {}: {e}", dst_path.display()))?;
    io::Write::flush(&mut dst_file)
        .map_err(|e| format!("flush staged {label} {}: {e}", dst_path.display()))?;
    #[cfg(unix)]
    {
        use std::os::fd::AsRawFd as _;
        let mode: libc::mode_t = if force_exec || src_exec { 0o555 } else { 0o444 };
        // SAFETY: `dst_file` is an exclusive fd opened via `create_new`.
        if unsafe { libc::fchmod(dst_file.as_raw_fd(), mode) } != 0 {
            return Err(format!(
                "chmod staged {label} {}: {}",
                dst_path.display(),
                io::Error::last_os_error()
            ));
        }
    }
    #[cfg(not(unix))]
    let _ = (src_exec, force_exec);
    Ok(())
}

pub(crate) fn copy_verified_regular_file(
    src_path: &Path,
    dst_path: &Path,
    force_exec: bool,
    label: &str,
) -> Result<(), String> {
    let lstat = fs::symlink_metadata(src_path)
        .map_err(|e| format!("stat {label} {}: {e}", src_path.display()))?;
    if lstat.file_type().is_symlink() {
        return Err(format!("{label} must not be a symlink: {}", src_path.display()));
    }
    if !lstat.is_file() {
        return Err(format!("{label} copy source is not a regular file: {}", src_path.display()));
    }
    let lstat_nlink = hardlink_count(&lstat);
    if lstat_nlink > 1 {
        return Err(format!(
            "{label} file must not be a hardlink (nlink={lstat_nlink}): {}",
            src_path.display()
        ));
    }
    #[cfg(unix)]
    let (mut src_file, src_exec) = {
        use std::os::unix::fs::{MetadataExt as _, OpenOptionsExt as _, PermissionsExt as _};
        let file = OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_NOFOLLOW)
            .open(src_path)
            .map_err(|e| format!("open {label} {}: {e}", src_path.display()))?;
        let fstat =
            file.metadata().map_err(|e| format!("fstat {label} {}: {e}", src_path.display()))?;
        if !fstat.is_file() || fstat.nlink() > 1 {
            return Err(format!(
                "{label} descriptor changed or hardlinked during copy: {}",
                src_path.display()
            ));
        }
        if lstat.dev() != fstat.dev() || lstat.ino() != fstat.ino() {
            return Err(format!(
                "{label} inode changed between validation and open: {}",
                src_path.display()
            ));
        }
        (file, (fstat.permissions().mode() & 0o111) != 0)
    };
    #[cfg(not(unix))]
    let (mut src_file, src_exec) = (
        fs::File::open(src_path)
            .map_err(|e| format!("open {label} {}: {e}", src_path.display()))?,
        false,
    );

    copy_opened_file_to_new_dst(&mut src_file, src_exec, dst_path, force_exec, label)
}

#[cfg(unix)]
fn freeze_staging_dir_from_fd(
    root_fd: std::os::fd::BorrowedFd<'_>,
    root_disp: &Path,
    writable_rel: Option<&Path>,
    label: &str,
) -> Result<(), String> {
    use std::os::fd::{AsFd as _, AsRawFd as _};

    let root_dup = root_fd
        .try_clone_to_owned()
        .map_err(|e| format!("dup {label} staging fd {}: {e}", root_disp.display()))?;
    let mut fds = vec![(root_dup, PathBuf::new(), root_disp.to_path_buf())];
    let mut idx = 0;
    while idx < fds.len() {
        let entries = read_dir_entries_from_fd(fds[idx].0.as_fd(), label)?;
        let parent_rel = fds[idx].1.clone();
        let parent_disp = fds[idx].2.clone();
        idx += 1;
        for entry in entries {
            let path = parent_disp.join(&entry.os_name);
            if is_lnk_mode(&entry.stat) {
                return Err(format!("{label} must not contain a symlink: {}", path.display()));
            }
            if is_dir_mode(&entry.stat) {
                let child = open_child_dir_nofollow(
                    fds[idx - 1].0.as_fd(),
                    &entry.c_name,
                    Some(stat_dev_ino(&entry.stat)),
                    label,
                )?;
                let child_rel = if parent_rel.as_os_str().is_empty() {
                    PathBuf::from(&entry.os_name)
                } else {
                    parent_rel.join(&entry.os_name)
                };
                fds.push((child, child_rel, path));
            } else if is_reg_mode(&entry.stat) {
                let nlink = stat_nlink(&entry.stat);
                if nlink > 1 {
                    return Err(format!(
                        "{label} file must not be a hardlink (nlink={nlink}): {}",
                        path.display()
                    ));
                }
            } else {
                return Err(format!("{label} contains non-regular entry: {}", path.display()));
            }
        }
    }
    for (dir_fd, dir_rel, dir_path) in fds.into_iter().rev() {
        let mode: libc::mode_t =
            if writable_rel.is_some_and(|w| w == dir_rel) { 0o700 } else { 0o555 };
        // SAFETY: `dir_fd` is a held directory descriptor inside staging.
        if unsafe { libc::fchmod(dir_fd.as_raw_fd(), mode) } != 0 {
            return Err(format!(
                "freeze staged {label} {}: {}",
                dir_path.display(),
                io::Error::last_os_error()
            ));
        }
    }
    Ok(())
}

#[cfg(not(target_os = "linux"))]
fn freeze_staging_dir_with_writable(
    root: &Path,
    writable_dir: Option<&Path>,
    label: &str,
) -> Result<(), String> {
    #[cfg(unix)]
    {
        use std::os::fd::AsFd as _;

        let root_fd = open_dir_handle_no_symlinks(root, None, label)?;
        let writable_rel = writable_dir.and_then(|w| w.strip_prefix(root).ok());
        freeze_staging_dir_from_fd(root_fd.as_fd(), root, writable_rel, label)
    }
    #[cfg(not(unix))]
    {
        let _ = writable_dir;
        validate_dir_tree_no_links(root, label)
    }
}

/// Lean sysroot manifest packages (`Init`, `Std`, `Lean`) omitted from the
/// `Init`-only runtime staging tree so prebuilt overlay verification can still
/// hash them directly from the validated source sysroot.
pub(crate) const LEAN_RUNTIME_OMITTED_SYSROOT_PACKAGES: &[&str] = &["Std", "Lean"];

fn is_lean_compiler_or_static_entry(rel_segs: &[OsString], name: &OsStr, is_dir: bool) -> bool {
    let s = name.to_string_lossy();
    if s.ends_with(".a") {
        return true;
    }
    if rel_segs.is_empty() {
        let is_omitted_pkg = |cand: &str| LEAN_RUNTIME_OMITTED_SYSROOT_PACKAGES.contains(&cand);
        if is_dir {
            return is_omitted_pkg(s.as_ref()) || matches!(s.as_ref(), "Lake" | "LeanIR");
        }
        return s.ends_with(".ilean")
            || LEAN_RUNTIME_OMITTED_SYSROOT_PACKAGES
                .iter()
                .any(|pkg| s.strip_prefix(pkg).is_some_and(|rest| rest.starts_with('.')))
            || s.starts_with("Lake.")
            || s.starts_with("LeanIR.")
            || s.starts_with("LeanChecker")
            || s.starts_with("Leanc");
    }
    false
}

pub(crate) fn copy_validated_subtree(
    src_root: &Path,
    dst_root: &Path,
    canon_symlink_root: Option<&Path>,
    force_exec: bool,
    label: &str,
) -> Result<(), String> {
    copy_validated_subtree_with_filter(
        src_root,
        dst_root,
        canon_symlink_root,
        force_exec,
        label,
        |_, _, _| false,
    )
}

#[cfg(unix)]
pub(crate) fn copy_validated_subtree_from_fd_with_filter(
    root_fd: std::os::fd::BorrowedFd<'_>,
    src_disp_root: &Path,
    dst_root: &Path,
    canon_symlink_root: Option<&Path>,
    force_exec: bool,
    label: &str,
    should_skip: impl Fn(&[OsString], &OsStr, bool) -> bool,
) -> Result<(), String> {
    use std::os::fd::AsFd as _;

    fs::create_dir_all(dst_root)
        .map_err(|e| format!("create staged {label} dir {}: {e}", dst_root.display()))?;
    let mut stack: Vec<(Option<std::os::fd::OwnedFd>, Vec<OsString>, PathBuf, PathBuf)> =
        vec![(None, Vec::new(), src_disp_root.to_path_buf(), dst_root.to_path_buf())];
    while let Some((dir_opt, rel_segs, cur_src_disp, dst_dir)) = stack.pop() {
        fs::create_dir_all(&dst_dir)
            .map_err(|e| format!("create staged {label} dir {}: {e}", dst_dir.display()))?;
        let cur_fd = dir_opt.as_ref().map(|d| d.as_fd()).unwrap_or(root_fd);
        let entries = read_dir_entries_from_fd(cur_fd, label)?;
        for entry in entries {
            let path = cur_src_disp.join(&entry.os_name);
            let dst_path = dst_dir.join(&entry.os_name);
            if is_lnk_mode(&entry.stat) {
                if canon_symlink_root.is_none() {
                    return Err(format!("{label} must not contain a symlink: {}", path.display()));
                }
                if stat_nlink(&entry.stat) > 1 {
                    return Err(format!(
                        "{label} symlink must not be a hardlink: {}",
                        path.display()
                    ));
                }
                let (mut src_file, st) = resolve_and_open_confined_lib_symlink_from_fd(
                    root_fd,
                    cur_fd,
                    &rel_segs,
                    &entry.c_name,
                    &path,
                    label,
                )?;
                copy_opened_file_to_new_dst(
                    &mut src_file,
                    (st.st_mode as libc::mode_t & 0o111) != 0,
                    &dst_path,
                    force_exec,
                    label,
                )?;
            } else if is_dir_mode(&entry.stat) {
                let child_fd = open_child_dir_nofollow(
                    cur_fd,
                    &entry.c_name,
                    Some(stat_dev_ino(&entry.stat)),
                    label,
                )?;
                if should_skip(&rel_segs, &entry.os_name, true) {
                    drop(child_fd);
                    continue;
                }
                let mut next_segs = rel_segs.clone();
                next_segs.push(entry.os_name);
                stack.push((Some(child_fd), next_segs, path, dst_path));
            } else if is_reg_mode(&entry.stat) {
                if should_skip(&rel_segs, &entry.os_name, false) {
                    if stat_nlink(&entry.stat) > 1 {
                        return Err(format!(
                            "{label} file must not be a hardlink (nlink={}): {}",
                            entry.stat.st_nlink,
                            path.display()
                        ));
                    }
                    continue;
                }
                let (mut src_file, st) = open_regular_file_from_fd(
                    cur_fd,
                    &entry.c_name,
                    Some(stat_dev_ino(&entry.stat)),
                    false,
                    label,
                )?;
                copy_opened_file_to_new_dst(
                    &mut src_file,
                    (st.st_mode as libc::mode_t & 0o111) != 0,
                    &dst_path,
                    force_exec,
                    label,
                )?;
            } else {
                return Err(format!("{label} contains non-regular entry: {}", path.display()));
            }
        }
    }
    Ok(())
}

fn copy_validated_subtree_with_filter(
    src_root: &Path,
    dst_root: &Path,
    canon_symlink_root: Option<&Path>,
    force_exec: bool,
    label: &str,
    should_skip: impl Fn(&[OsString], &OsStr, bool) -> bool,
) -> Result<(), String> {
    fs::create_dir_all(dst_root)
        .map_err(|e| format!("create staged {label} dir {}: {e}", dst_root.display()))?;
    #[cfg(unix)]
    {
        use std::os::fd::AsFd as _;

        let root_fd = open_dir_handle_no_symlinks(src_root, None, label)?;
        copy_validated_subtree_from_fd_with_filter(
            root_fd.as_fd(),
            src_root,
            dst_root,
            canon_symlink_root,
            force_exec,
            label,
            should_skip,
        )
    }

    #[cfg(not(unix))]
    {
        let mut stack = vec![(src_root.to_path_buf(), Vec::<OsString>::new())];
        while let Some((cur_dir, rel_segs)) = stack.pop() {
            let rel_dir = cur_dir
                .strip_prefix(src_root)
                .map_err(|e| format!("strip {label} prefix {}: {e}", cur_dir.display()))?;
            let dst_dir = dst_root.join(rel_dir);
            fs::create_dir_all(&dst_dir)
                .map_err(|e| format!("create staged {label} dir {}: {e}", dst_dir.display()))?;
            let mut entries: Vec<_> = fs::read_dir(&cur_dir)
                .map_err(|e| format!("read {label} dir {}: {e}", cur_dir.display()))?
                .collect::<Result<Vec<_>, _>>()
                .map_err(|e| format!("iterate {label} dir {}: {e}", cur_dir.display()))?;
            entries.sort_by_key(|e| e.file_name());
            for entry in entries {
                let path = entry.path();
                let name = entry.file_name();
                let dst_path = dst_dir.join(&name);
                let meta = fs::symlink_metadata(&path)
                    .map_err(|e| format!("stat {label} {}: {e}", path.display()))?;
                if meta.file_type().is_symlink() {
                    let Some(canon_lib) = canon_symlink_root else {
                        return Err(format!(
                            "{label} must not contain a symlink: {}",
                            path.display()
                        ));
                    };
                    if hardlink_count(&meta) > 1 {
                        return Err(format!(
                            "{label} symlink must not be a hardlink: {}",
                            path.display()
                        ));
                    }
                    let target = resolve_confined_lib_symlink(canon_lib, &cur_dir, &path, label)?;
                    copy_verified_regular_file(&target, &dst_path, force_exec, label)?;
                } else if meta.is_dir() {
                    if should_skip(&rel_segs, &name, true) {
                        continue;
                    }
                    let mut next_segs = rel_segs.clone();
                    next_segs.push(name);
                    stack.push((path, next_segs));
                } else if meta.is_file() {
                    if should_skip(&rel_segs, &name, false) {
                        let nlink = hardlink_count(&meta);
                        if nlink > 1 {
                            return Err(format!(
                                "{label} file must not be a hardlink (nlink={nlink}): {}",
                                path.display()
                            ));
                        }
                        continue;
                    }
                    copy_verified_regular_file(&path, &dst_path, force_exec, label)?;
                } else {
                    return Err(format!("{label} contains non-regular entry: {}", path.display()));
                }
            }
        }
        Ok(())
    }
}

fn materialize_immutable_sysroot(
    canon_sysroot: &Path,
    canon_lib: Option<&Path>,
    rel_bin: &str,
    tmp_parent: Option<&Path>,
    label: &str,
) -> Result<PreparedSysroot, String> {
    if !Path::new(rel_bin).starts_with("bin") {
        return Err(format!("{label} path `{rel_bin}` must reside under `bin/`"));
    }
    let bin_dir = canon_sysroot.join("bin");
    let canon_bin_dir =
        crate::mir_eval_runner::validate_dir_path_no_symlinks(&bin_dir, canon_sysroot)?;
    validate_dir_tree_no_links(&canon_bin_dir, &format!("{label} bin"))?;

    let temp = crate::mir_eval_runner::build_temp_dir("anneal-sysroot-", tmp_parent)?;
    let (_, staging) = ImmutableStagingDir::build_and_pin(temp, label, |_, pinned_root| {
        copy_validated_subtree(
            &canon_bin_dir,
            &pinned_root.join("bin"),
            None,
            false,
            &format!("{label} bin"),
        )?;
        if let Some(canon_lib) = canon_lib {
            copy_validated_subtree(
                canon_lib,
                &pinned_root.join("lib"),
                Some(canon_lib),
                false,
                &format!("{label} lib"),
            )?;
        }
        Ok(())
    })?;
    let _ = staging.open_verified_rel_file(Path::new(rel_bin), label)?;
    let priv_root = staging.root().to_path_buf();
    let priv_bin = priv_root.join(rel_bin);
    let ld_library_path = if canon_lib.is_some() {
        priv_root.join("lib").display().to_string()
    } else {
        String::new()
    };
    Ok(PreparedSysroot {
        sysroot: priv_root,
        binary: priv_bin,
        ld_library_path,
        _staging: Some(staging),
    })
}

pub(crate) fn stage_top_level_lib_into(
    canon_lib: &Path,
    dst_lib: &Path,
    label: &str,
) -> Result<(), String> {
    stage_top_level_lib_into_filtered(canon_lib, dst_lib, false, label)
}

fn stage_top_level_lib_into_filtered(
    canon_lib: &Path,
    dst_lib: &Path,
    skip_static_archives: bool,
    label: &str,
) -> Result<(), String> {
    fs::create_dir_all(dst_lib)
        .map_err(|e| format!("create staged {label} dir {}: {e}", dst_lib.display()))?;
    #[cfg(unix)]
    {
        use std::os::fd::AsFd as _;

        let root_fd = open_dir_handle_no_symlinks(canon_lib, None, label)?;
        let entries = read_dir_entries_from_fd(root_fd.as_fd(), label)?;
        for entry in entries {
            let path = canon_lib.join(&entry.os_name);
            let dst_path = dst_lib.join(&entry.os_name);
            let is_static_a =
                skip_static_archives && entry.os_name.to_string_lossy().ends_with(".a");
            if is_lnk_mode(&entry.stat) {
                if stat_nlink(&entry.stat) > 1 {
                    return Err(format!(
                        "{label} symlink must not be a hardlink: {}",
                        path.display()
                    ));
                }
                let (mut src_file, _) = resolve_and_open_confined_lib_symlink_from_fd(
                    root_fd.as_fd(),
                    root_fd.as_fd(),
                    &[],
                    &entry.c_name,
                    &path,
                    label,
                )?;
                if !is_static_a {
                    copy_opened_file_to_new_dst(&mut src_file, false, &dst_path, false, label)?;
                }
            } else if is_reg_mode(&entry.stat) {
                let (mut src_file, _) = open_regular_file_from_fd(
                    root_fd.as_fd(),
                    &entry.c_name,
                    Some(stat_dev_ino(&entry.stat)),
                    false,
                    label,
                )?;
                if !is_static_a {
                    copy_opened_file_to_new_dst(&mut src_file, false, &dst_path, false, label)?;
                }
            } else if !is_dir_mode(&entry.stat) {
                return Err(format!("{label} contains non-regular entry: {}", path.display()));
            }
        }
        Ok(())
    }

    #[cfg(not(unix))]
    {
        let mut entries: Vec<_> = fs::read_dir(canon_lib)
            .map_err(|e| format!("read {label} dir {}: {e}", canon_lib.display()))?
            .collect::<Result<Vec<_>, _>>()
            .map_err(|e| format!("iterate {label} dir {}: {e}", canon_lib.display()))?;
        entries.sort_by_key(|e| e.file_name());
        for entry in entries {
            let path = entry.path();
            let meta = fs::symlink_metadata(&path)
                .map_err(|e| format!("stat {label} {}: {e}", path.display()))?;
            let dst_path = dst_lib.join(entry.file_name());
            let is_static_a =
                skip_static_archives && entry.file_name().to_string_lossy().ends_with(".a");
            if meta.file_type().is_symlink() {
                if hardlink_count(&meta) > 1 {
                    return Err(format!(
                        "{label} symlink must not be a hardlink: {}",
                        path.display()
                    ));
                }
                let target = resolve_confined_lib_symlink(canon_lib, canon_lib, &path, label)?;
                if !is_static_a {
                    copy_verified_regular_file(&target, &dst_path, false, label)?;
                }
            } else if meta.is_file() {
                if !is_static_a {
                    copy_verified_regular_file(&path, &dst_path, false, label)?;
                }
            } else if !meta.is_dir() {
                return Err(format!("{label} contains non-regular entry: {}", path.display()));
            }
        }
        Ok(())
    }
}

fn materialize_immutable_top_level_lib_in(
    canon_lib: &Path,
    tmp_parent: Option<&Path>,
    label: &str,
) -> Result<(PathBuf, Arc<ImmutableStagingDir>), String> {
    let temp = crate::mir_eval_runner::build_temp_dir("anneal-tc-lib-", tmp_parent)?;
    let (_, staging) = ImmutableStagingDir::build_and_pin(temp, label, |_, pinned_root| {
        stage_top_level_lib_into(canon_lib, &pinned_root.join("lib"), label)
    })?;
    Ok((staging.root().join("lib"), staging))
}

pub(crate) fn validate_dir_tree_no_links(root_dir: &Path, label: &str) -> Result<(), String> {
    #[cfg(unix)]
    {
        use std::os::fd::AsFd as _;

        let root_fd = open_dir_handle_no_symlinks(root_dir, None, label)?;
        let mut stack: Vec<(Option<std::os::fd::OwnedFd>, PathBuf)> =
            vec![(None, root_dir.to_path_buf())];
        while let Some((dir_opt, cur_dir)) = stack.pop() {
            let cur_fd = dir_opt.as_ref().map(|d| d.as_fd()).unwrap_or_else(|| root_fd.as_fd());
            let entries = read_dir_entries_from_fd(cur_fd, label)?;
            for entry in entries {
                let path = cur_dir.join(&entry.os_name);
                if is_lnk_mode(&entry.stat) {
                    return Err(format!("{label} must not contain a symlink: {}", path.display()));
                }
                if is_dir_mode(&entry.stat) {
                    let child_fd = open_child_dir_nofollow(
                        cur_fd,
                        &entry.c_name,
                        Some(stat_dev_ino(&entry.stat)),
                        label,
                    )?;
                    stack.push((Some(child_fd), path));
                } else if is_reg_mode(&entry.stat) {
                    let nlink = stat_nlink(&entry.stat);
                    if nlink > 1 {
                        return Err(format!(
                            "{label} file must not be a hardlink (nlink={nlink}): {}",
                            path.display()
                        ));
                    }
                } else {
                    return Err(format!("{label} contains non-regular entry: {}", path.display()));
                }
            }
        }
        Ok(())
    }

    #[cfg(not(unix))]
    {
        let mut stack = vec![root_dir.to_path_buf()];
        while let Some(cur_dir) = stack.pop() {
            let mut entries: Vec<_> = fs::read_dir(&cur_dir)
                .map_err(|e| format!("read {label} dir {}: {e}", cur_dir.display()))?
                .collect::<Result<Vec<_>, _>>()
                .map_err(|e| format!("iterate {label} dir {}: {e}", cur_dir.display()))?;
            entries.sort_by_key(|e| e.file_name());
            for entry in entries {
                let path = entry.path();
                let meta = fs::symlink_metadata(&path)
                    .map_err(|e| format!("stat {label} {}: {e}", path.display()))?;
                if meta.file_type().is_symlink() {
                    return Err(format!("{label} must not contain a symlink: {}", path.display()));
                }
                if meta.is_dir() {
                    stack.push(path);
                } else if meta.is_file() {
                    let nlink = hardlink_count(&meta);
                    if nlink > 1 {
                        return Err(format!(
                            "{label} file must not be a hardlink (nlink={nlink}): {}",
                            path.display()
                        ));
                    }
                } else {
                    return Err(format!("{label} contains non-regular entry: {}", path.display()));
                }
            }
        }
        Ok(())
    }
}

pub(crate) fn validate_store_contained_dir_tree(
    root_dir: &Path,
    store_prefix: &Path,
    canon_store: &Path,
    label: &str,
) -> Result<(), String> {
    let mut stack = vec![root_dir.to_path_buf()];
    let mut visited = BTreeSet::new();
    visited.insert(root_dir.to_path_buf());
    while let Some(cur_dir) = stack.pop() {
        let mut entries: Vec<_> = fs::read_dir(&cur_dir)
            .map_err(|e| format!("read {label} dir {}: {e}", cur_dir.display()))?
            .collect::<Result<Vec<_>, _>>()
            .map_err(|e| format!("iterate {label} dir {}: {e}", cur_dir.display()))?;
        entries.sort_by_key(|e| e.file_name());
        for entry in entries {
            let path = entry.path();
            let meta = fs::symlink_metadata(&path)
                .map_err(|e| format!("stat {label} {}: {e}", path.display()))?;
            if meta.file_type().is_symlink() {
                let nlink = hardlink_count(&meta);
                if nlink > 1 {
                    return Err(format!(
                        "{label} symlink must not be a hardlink (nlink={nlink}): {}",
                        path.display()
                    ));
                }
                let canon = fs::canonicalize(&path)
                    .map_err(|e| format!("canonicalize {label} {}: {e}", path.display()))?;
                if !canon.starts_with(canon_store) {
                    return Err(format!(
                        "{label} symlink escaped store {}: {} -> {}",
                        canon_store.display(),
                        path.display(),
                        canon.display()
                    ));
                }
                let canon_meta = fs::symlink_metadata(&canon)
                    .map_err(|e| format!("stat {label} {}: {e}", canon.display()))?;
                let checked = validate_store_contained_entry(
                    &path,
                    store_prefix,
                    canon_store,
                    canon_meta.is_dir(),
                    label,
                )?;
                if canon_meta.is_dir() && visited.insert(checked.clone()) {
                    stack.push(checked);
                }
            } else if meta.is_dir() {
                if visited.insert(path.clone()) {
                    stack.push(path);
                }
            } else if meta.is_file() {
                let nlink = hardlink_count(&meta);
                if nlink > 1 {
                    return Err(format!(
                        "{label} file must not be a hardlink (nlink={nlink}): {}",
                        path.display()
                    ));
                }
            } else {
                return Err(format!("{label} contains non-regular entry: {}", path.display()));
            }
        }
    }
    Ok(())
}

fn is_transient_etxtbsy(term: &Termination) -> bool {
    matches!(
        term,
        Termination::LaunchFailed(err)
            if err.contains("Text file busy") || err.contains("os error 26")
    )
}

pub(crate) fn run_supervised_in_tmp(
    inv: &Invocation,
    work_dir: &Path,
    timeout: Duration,
    tmp_parent: Option<&Path>,
    context: &str,
) -> Result<ProcessOutcome, String> {
    let canon_work = fs::canonicalize(work_dir)
        .map_err(|e| format!("canonicalize work dir ({context}): {e}"))?;
    let deadline = Instant::now() + timeout;
    let mut step_timeout = timeout;
    let mut backoff_ms = 5_u64;
    for attempt in 0..=5_u8 {
        let supervisor = ProcessSupervisor::new(step_timeout)?;
        let tmp = crate::mir_eval_runner::build_temp_dir("anneal-sup-", tmp_parent)
            .map_err(|e| format!("create supervisor temp dir ({context}): {e}"))?;
        let canon_root = fs::canonicalize(tmp.path())
            .map_err(|e| format!("canonicalize supervisor temp dir ({context}): {e}"))?;
        let out = supervisor.run(inv, &canon_work, &canon_root.join("log"), &canon_root)?;
        // Retry bounded transient `ETXTBSY` when sibling threads `fork()` while
        // staging a temporary executable across `ProcessSupervisor` spawns.
        if attempt < 5 && is_transient_etxtbsy(&out.termination) {
            let sleep_dur = Duration::from_millis(backoff_ms);
            if Instant::now() + sleep_dur < deadline {
                std::thread::sleep(sleep_dur);
                let remaining = deadline.saturating_duration_since(Instant::now());
                if !remaining.is_zero() {
                    step_timeout = remaining;
                    backoff_ms = backoff_ms.saturating_mul(2);
                    continue;
                }
            }
        }
        return Ok(out);
    }
    unreachable!("bounded loop always returns before terminating")
}

#[cfg(unix)]
pub(crate) fn hardlink_count(meta: &fs::Metadata) -> u64 {
    use std::os::unix::fs::MetadataExt as _;
    meta.nlink()
}

#[cfg(not(unix))]
pub(crate) fn hardlink_count(_meta: &fs::Metadata) -> u64 {
    1
}

/// Validate `rust_sysroot` and `rust_sysroot/<rel_bin>` against symlinks and
/// hardlinks (`st_nlink > 1`) before any binary invocation. Allows Nix-built
/// `symlinkJoin` or store-contained sysroots ONLY when `store_prefix`
/// (`/nix/store`) is itself symlink-free and `rust_sysroot`, `lib/`, and
/// `<rel_bin>` canonical targets stay strictly inside `store_prefix`. Every
/// non-store sysroot is copied into a private, read-only, link-free directory.
pub(crate) fn prepare_sysroot_binary(
    rust_sysroot: &Path,
    rel_bin: &str,
    store_prefix: &Path,
    label: &str,
) -> Result<PreparedSysroot, String> {
    prepare_sysroot_binary_in(rust_sysroot, rel_bin, store_prefix, None, label)
}

pub(crate) fn prepare_sysroot_binary_in(
    rust_sysroot: &Path,
    rel_bin: &str,
    store_prefix: &Path,
    tmp_parent: Option<&Path>,
    label: &str,
) -> Result<PreparedSysroot, String> {
    if rust_sysroot.components().any(|c| matches!(c, Component::ParentDir))
        || Path::new(rel_bin).components().any(|c| !matches!(c, Component::Normal(_)))
    {
        return Err(format!(
            "rust_sysroot must not contain `..` path traversal segments: {}",
            rust_sysroot.display()
        ));
    }
    let caller_cwd =
        env::current_dir().map_err(|e| format!("resolve current working directory: {e}"))?;
    let abs_sysroot = if rust_sysroot.is_absolute() {
        rust_sysroot.to_path_buf()
    } else {
        caller_cwd.join(rust_sysroot)
    };
    let abs_bin = abs_sysroot.join(rel_bin);

    match fs::symlink_metadata(&abs_bin) {
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            return Err(format!("pinned sysroot lacks `{rel_bin}`: {}", abs_bin.display()));
        }
        Err(e) => {
            return Err(format!("stat {label} {}: {e}", abs_bin.display()));
        }
        Ok(_) => {}
    }

    if abs_sysroot != store_prefix
        && abs_sysroot.starts_with(store_prefix)
        && crate::mir_eval_runner::validate_dir_path_no_symlinks(store_prefix, &caller_cwd).is_ok()
    {
        let (canon_sysroot, canon_bin) = validate_store_contained_sysroot_binary(
            &abs_sysroot,
            &abs_bin,
            rel_bin,
            &caller_cwd,
            store_prefix,
            label,
            format!("invalid store-contained sysroot: {}", abs_sysroot.display()),
        )?;
        let store_lib = canon_sysroot.join("lib");
        let ld_library_path =
            if store_lib.is_dir() { store_lib.display().to_string() } else { String::new() };
        return Ok(PreparedSysroot {
            sysroot: canon_sysroot,
            binary: canon_bin,
            ld_library_path,
            _staging: None,
        });
    }

    let canon_sysroot =
        crate::mir_eval_runner::validate_dir_path_no_symlinks(&abs_sysroot, &caller_cwd)?;
    let _canon_bin =
        crate::mir_eval_runner::validate_executable_no_links(&abs_bin, &caller_cwd, label)?;
    let lib_dir = abs_sysroot.join("lib");
    let canon_lib = match fs::symlink_metadata(&lib_dir) {
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => None,
        Err(e) => return Err(format!("stat rust_sysroot lib {}: {e}", lib_dir.display())),
        Ok(_) => {
            let canon_lib =
                crate::mir_eval_runner::validate_dir_path_no_symlinks(&lib_dir, &caller_cwd)?;
            let _has_symlinks = inspect_sysroot_lib_dir_tree(&canon_lib, true, "rust_sysroot lib")?;
            Some(canon_lib)
        }
    };
    materialize_immutable_sysroot(&canon_sysroot, canon_lib.as_deref(), rel_bin, tmp_parent, label)
}

pub(crate) fn validate_store_contained_entry(
    abs_path: &Path,
    store_prefix: &Path,
    canon_store: &Path,
    expect_dir: bool,
    label: &str,
) -> Result<PathBuf, String> {
    if abs_path.components().any(|c| matches!(c, Component::ParentDir))
        || !abs_path.starts_with(store_prefix)
        || abs_path == store_prefix
    {
        return Err(format!(
            "{label} must stay inside store {}: {}",
            store_prefix.display(),
            abs_path.display()
        ));
    }
    let rel_inside_store = abs_path.strip_prefix(store_prefix).map_err(|_| {
        format!("{label} escaped store {}: {}", store_prefix.display(), abs_path.display())
    })?;
    let mut comps = Vec::new();
    for c in rel_inside_store.components() {
        match c {
            Component::Normal(seg) => comps.push(seg),
            Component::CurDir => {}
            _ => {
                return Err(format!(
                    "{label} contains invalid path component inside store: {}",
                    abs_path.display()
                ));
            }
        }
    }
    if comps.is_empty() {
        return Err(format!("{label} must not equal store root {}", store_prefix.display()));
    }

    let mut cur = canon_store.to_path_buf();
    for (idx, seg) in comps.iter().enumerate() {
        cur.push(seg);
        let is_last = idx + 1 == comps.len();
        let meta = fs::symlink_metadata(&cur)
            .map_err(|e| format!("stat {label} {}: {e}", cur.display()))?;
        let nlink = hardlink_count(&meta);
        if ((is_last && !expect_dir) || !meta.is_dir()) && nlink > 1 {
            return Err(format!(
                "{label} must not be a hardlink (nlink={nlink}): {}",
                cur.display()
            ));
        }
        if meta.file_type().is_symlink() {
            let step_canon = fs::canonicalize(&cur)
                .map_err(|e| format!("canonicalize {label} {}: {e}", cur.display()))?;
            if !step_canon.starts_with(canon_store) {
                return Err(format!(
                    "{label} symlink escaped store {}: {} -> {}",
                    canon_store.display(),
                    cur.display(),
                    step_canon.display()
                ));
            }
        }
    }

    let canon = fs::canonicalize(abs_path)
        .map_err(|e| format!("canonicalize {label} {}: {e}", abs_path.display()))?;
    if !canon.starts_with(canon_store) {
        return Err(format!(
            "{label} escaped store {}: {}",
            canon_store.display(),
            canon.display()
        ));
    }
    let canon_meta = fs::symlink_metadata(&canon)
        .map_err(|e| format!("stat {label} {}: {e}", canon.display()))?;
    if canon_meta.file_type().is_symlink() {
        return Err(format!("{label} canonical target is a symlink: {}", canon.display()));
    }
    if expect_dir {
        if !canon_meta.is_dir() {
            return Err(format!("{label} is not a directory: {}", canon.display()));
        }
    } else {
        if !canon_meta.is_file() {
            return Err(format!("{label} target is not a regular file: {}", canon.display()));
        }
        let canon_nlink = hardlink_count(&canon_meta);
        if canon_nlink > 1 {
            return Err(format!(
                "{label} target must not be a hardlink (nlink={canon_nlink}): {}",
                canon.display()
            ));
        }
    }
    Ok(canon)
}

fn validate_store_contained_sysroot_binary(
    abs_sysroot: &Path,
    abs_bin: &Path,
    rel_bin: &str,
    caller_cwd: &Path,
    store_prefix: &Path,
    label: &str,
    std_err: String,
) -> Result<(PathBuf, PathBuf), String> {
    if abs_sysroot.components().any(|c| matches!(c, Component::ParentDir))
        || Path::new(rel_bin).components().any(|c| !matches!(c, Component::Normal(_)))
        || !abs_sysroot.starts_with(store_prefix)
        || abs_sysroot == store_prefix
    {
        return Err(std_err);
    }
    let Ok(canon_store) =
        crate::mir_eval_runner::validate_dir_path_no_symlinks(store_prefix, caller_cwd)
    else {
        return Err(std_err);
    };

    let canon_bin =
        validate_store_contained_entry(abs_bin, store_prefix, &canon_store, false, label)?;
    let canon_sysroot = validate_store_contained_entry(
        abs_sysroot,
        store_prefix,
        &canon_store,
        true,
        "rust_sysroot",
    )?;
    let lib_dir = abs_sysroot.join("lib");
    if fs::symlink_metadata(&lib_dir).is_ok() {
        let canon_lib = validate_store_contained_entry(
            &lib_dir,
            store_prefix,
            &canon_store,
            true,
            "rust_sysroot lib",
        )?;
        validate_store_contained_dir_tree(
            &canon_lib,
            store_prefix,
            &canon_store,
            "rust_sysroot lib",
        )?;
    }
    Ok((canon_sysroot, canon_bin))
}

#[cfg(unix)]
fn path_has_hardlinked_non_dir(abs_path: &Path) -> bool {
    let mut cur = PathBuf::new();
    for comp in abs_path.components() {
        match comp {
            Component::Prefix(p) => cur.push(p.as_os_str()),
            Component::RootDir => cur.push(comp.as_os_str()),
            Component::CurDir => continue,
            Component::ParentDir => return true,
            Component::Normal(seg) => {
                cur.push(seg);
                let Ok(meta) = fs::symlink_metadata(&cur) else {
                    return false;
                };
                if !meta.is_dir() && hardlink_count(&meta) > 1 {
                    return true;
                }
            }
        }
    }
    false
}

#[cfg(not(unix))]
fn path_has_hardlinked_non_dir(_abs_path: &Path) -> bool {
    false
}

pub(crate) fn try_validate_store_contained_path(
    path: &Path,
    store_prefix: &Path,
    caller_cwd: &Path,
    expect_dir: bool,
    label: &str,
) -> Option<Result<PathBuf, String>> {
    if path.components().any(|c| matches!(c, Component::ParentDir)) {
        return None;
    }
    let abs = if path.is_absolute() { path.to_path_buf() } else { caller_cwd.join(path) };
    let store_exists = fs::symlink_metadata(store_prefix).is_ok();
    if !store_exists {
        return None;
    }
    let canon_store =
        match crate::mir_eval_runner::validate_dir_path_no_symlinks(store_prefix, caller_cwd) {
            Ok(canon) => canon,
            Err(e) => {
                return if abs.starts_with(store_prefix) { Some(Err(e)) } else { None };
            }
        };
    if abs.starts_with(store_prefix) {
        return Some(validate_store_contained_entry(
            &abs,
            store_prefix,
            &canon_store,
            expect_dir,
            label,
        ));
    }
    // Reject hardlinked symlink chains before checking canonical store
    // containment, and allow non-store Nix wrapper symlinks (e.g.
    // `/opt/anneal-nix/rust-toolchain -> /nix/store/...`) only when their
    // canonical target remains strictly inside `canon_store`.
    if path_has_hardlinked_non_dir(&abs) {
        return None;
    }
    let Ok(canon) = fs::canonicalize(&abs) else {
        return None;
    };
    if !canon.starts_with(&canon_store) || canon == canon_store {
        return None;
    }
    Some(validate_store_contained_entry(&canon, &canon_store, &canon_store, expect_dir, label))
}

pub(crate) fn try_validate_store_contained_executable(
    bin: &Path,
    store_prefix: &Path,
    caller_cwd: &Path,
    label: &str,
) -> Option<Result<PathBuf, String>> {
    try_validate_store_contained_path(bin, store_prefix, caller_cwd, false, label)
}

pub(crate) fn validated_store_aware_dir(
    dir: &Path,
    store_prefix: &Path,
    caller_cwd: &Path,
    label: &str,
) -> Result<PathBuf, String> {
    if let Some(res) = try_validate_store_contained_path(dir, store_prefix, caller_cwd, true, label)
    {
        return res;
    }
    crate::mir_eval_runner::validate_dir_path_no_symlinks(dir, caller_cwd)
}

pub(crate) fn validated_store_aware_executable(
    bin: &Path,
    store_prefix: &Path,
    caller_cwd: &Path,
    label: &str,
) -> Result<PathBuf, String> {
    if let Some(res) = try_validate_store_contained_executable(bin, store_prefix, caller_cwd, label)
    {
        return res;
    }
    crate::mir_eval_runner::validate_executable_no_links(bin, caller_cwd, label)
}

/// Verified non-symlink file opened via retained no-follow parent directory
/// descriptors so staging streams directly from `file` without a second
/// pathname open.
#[derive(Debug)]
pub(crate) struct OpenedExecutable {
    pub(crate) canon_path: PathBuf,
    pub(crate) file: File,
    pub(crate) nlink: u64,
    pub(crate) dev_ino: (u64, u64),
    #[cfg(unix)]
    pub(crate) parent_fd: Option<std::os::fd::OwnedFd>,
}

#[cfg(target_os = "linux")]
fn verify_frozen_proc_fd_entry(
    st: &libc::stat,
    euid: libc::uid_t,
    expect_dir: bool,
    desc: &str,
    label: &str,
) -> Result<(), String> {
    if expect_dir && !is_dir_mode(st) {
        return Err(format!("{label} pinned fd target is not a directory: {desc}"));
    }
    if st.st_uid != euid {
        return Err(format!("{label} pinned entry owner {} != euid {euid}: {desc}", st.st_uid));
    }
    if (st.st_mode & 0o222) != 0 {
        return Err(format!(
            "{label} pinned entry must be frozen non-writable (mode {:04o}): {desc}",
            st.st_mode & 0o777
        ));
    }
    Ok(())
}

#[cfg(target_os = "linux")]
fn try_open_pinned_proc_fd_executable(
    file_path: &Path,
    reject_hardlinks: bool,
    label: &str,
) -> Result<Option<OpenedExecutable>, String> {
    use std::os::fd::{AsFd as _, FromRawFd as _, OwnedFd, RawFd};

    let Ok(rel_proc) = file_path.strip_prefix("/proc/self/fd") else {
        return Ok(None);
    };
    let mut comps = Vec::new();
    for comp in rel_proc.components() {
        match comp {
            Component::CurDir => {}
            Component::Normal(seg) => comps.push(seg),
            _ => {
                return Err(format!(
                    "{label} pinned fd path must not traverse directories: {}",
                    file_path.display()
                ));
            }
        }
    }
    if comps.len() < 2 {
        return Err(format!(
            "{label} pinned fd path must name an open dir fd and file: {}",
            file_path.display()
        ));
    }
    let fd_str = comps[0].to_str().ok_or_else(|| {
        format!("{label} pinned fd segment is not valid UTF-8: {}", file_path.display())
    })?;
    if fd_str.is_empty() || !fd_str.bytes().all(|b| b.is_ascii_digit()) {
        return Err(format!("{label} pinned fd segment must be numeric: {}", file_path.display()));
    }
    let raw_fd: RawFd = fd_str
        .parse::<RawFd>()
        .map_err(|e| format!("{label} pinned fd number invalid ({}): {e}", file_path.display()))?;
    if raw_fd <= 2 {
        return Err(format!(
            "{label} pinned fd must not target stdio descriptor {raw_fd}: {}",
            file_path.display()
        ));
    }
    // SAFETY: `F_DUPFD_CLOEXEC` duplicates `raw_fd` if it is currently open in
    // this process, failing safely with `EBADF` otherwise.
    let dup = unsafe { libc::fcntl(raw_fd, libc::F_DUPFD_CLOEXEC, 3) };
    if dup < 0 {
        return Err(format!(
            "{label} pinned descriptor fd {raw_fd} is unavailable ({}): {}",
            file_path.display(),
            io::Error::last_os_error()
        ));
    }
    // SAFETY: `dup` is a freshly duplicated valid descriptor >= 3.
    let mut cur_fd = unsafe { OwnedFd::from_raw_fd(dup) };
    // SAFETY: querying current effective UID has no preconditions.
    let euid = unsafe { libc::geteuid() };
    let root_st = fstat_fd(cur_fd.as_fd(), label)?;
    verify_frozen_proc_fd_entry(&root_st, euid, true, &format!("/proc/self/fd/{raw_fd}"), label)?;

    let disp = file_path.display().to_string();
    let (leaf_seg, subdirs) = comps[1..].split_last().expect("comps.len() >= 2 checked above");
    for seg in subdirs {
        let c_seg = os_str_to_cstring(seg, label)?;
        cur_fd = open_child_dir_nofollow(cur_fd.as_fd(), &c_seg, None, label)?;
        let st = fstat_fd(cur_fd.as_fd(), label)?;
        verify_frozen_proc_fd_entry(&st, euid, true, &disp, label)?;
    }
    let c_leaf = os_str_to_cstring(leaf_seg, label)?;
    let (file, st) =
        open_regular_file_from_fd(cur_fd.as_fd(), &c_leaf, None, !reject_hardlinks, label)?;
    verify_frozen_proc_fd_entry(&st, euid, false, &disp, label)?;
    Ok(Some(OpenedExecutable {
        canon_path: file_path.to_path_buf(),
        file,
        nlink: stat_nlink(&st),
        dev_ino: stat_dev_ino(&st),
        parent_fd: Some(cur_fd),
    }))
}

/// Walk `path` against `caller_cwd` through `O_DIRECTORY | O_NOFOLLOW` ancestor
/// directory descriptors, verify leaf metadata (regular file, non-symlink, and
/// `nlink == 1` when `reject_hardlinks` is set), and return the opened handle
/// alongside the retained leaf parent directory descriptor.
pub(crate) fn open_verified_executable_via_dirfd(
    file_path: &Path,
    caller_cwd: &Path,
    reject_hardlinks: bool,
    label: &str,
) -> Result<OpenedExecutable, String> {
    let joined =
        if file_path.is_absolute() { file_path.to_path_buf() } else { caller_cwd.join(file_path) };
    if joined.components().any(|c| matches!(c, Component::ParentDir)) {
        return Err(format!(
            "{label} must not contain parent-directory traversal (`..`): {}",
            file_path.display()
        ));
    }
    #[cfg(target_os = "linux")]
    if let Some(opened) = try_open_pinned_proc_fd_executable(file_path, reject_hardlinks, label)? {
        return Ok(opened);
    }
    #[cfg(unix)]
    {
        use std::os::fd::AsFd as _;
        let Some(leaf) = joined.file_name() else {
            return Err(format!("{label} is not a regular file: {}", joined.display()));
        };
        let Some(parent) = joined.parent() else {
            return Err(format!("{label} has no parent directory: {}", joined.display()));
        };
        let parent_fd = open_dir_handle_no_symlinks(parent, None, label)?;
        let c_leaf = os_str_to_cstring(leaf, label)?;
        let (file, st) =
            open_regular_file_from_fd(parent_fd.as_fd(), &c_leaf, None, !reject_hardlinks, label)?;
        let canon_path = fs::canonicalize(&joined)
            .map_err(|e| format!("canonicalize {label} {}: {e}", joined.display()))?;
        let canon_meta = fs::symlink_metadata(&canon_path)
            .map_err(|e| format!("stat {label} {}: {e}", canon_path.display()))?;
        {
            use std::os::unix::fs::MetadataExt as _;
            if (canon_meta.dev(), canon_meta.ino()) != stat_dev_ino(&st) {
                return Err(format!(
                    "{label} ancestor changed concurrently during validation: {}",
                    joined.display()
                ));
            }
        }
        Ok(OpenedExecutable {
            canon_path,
            file,
            nlink: stat_nlink(&st),
            dev_ino: stat_dev_ino(&st),
            parent_fd: Some(parent_fd),
        })
    }
    #[cfg(not(unix))]
    {
        let canon_path = if reject_hardlinks {
            crate::mir_eval_runner::validate_executable_no_links(file_path, caller_cwd, label)?
        } else {
            crate::mir_eval_runner::validate_file_path_no_symlinks(file_path, caller_cwd, label)?
        };
        let file = File::open(&canon_path)
            .map_err(|e| format!("open {label} {}: {e}", canon_path.display()))?;
        let meta =
            file.metadata().map_err(|e| format!("fstat {label} {}: {e}", canon_path.display()))?;
        let nlink = hardlink_count(&meta);
        if reject_hardlinks && nlink > 1 {
            return Err(format!(
                "{label} must not be a hardlink (nlink={nlink}): {}",
                canon_path.display()
            ));
        }
        Ok(OpenedExecutable { canon_path, file, nlink, dev_ino: (0, 0) })
    }
}

pub(crate) fn stage_immutable_opened_executable(
    opened: &mut OpenedExecutable,
    tmp_parent: Option<&Path>,
    label: &str,
) -> Result<(PathBuf, Option<Arc<ImmutableStagingDir>>), String> {
    let file_name = opened
        .canon_path
        .file_name()
        .ok_or_else(|| format!("{label} has no file name: {}", opened.canon_path.display()))?;
    let rel_bin = Path::new("bin").join(file_name);
    let temp = crate::mir_eval_runner::build_temp_dir("anneal-bin-", tmp_parent)?;
    let (_, staging) = ImmutableStagingDir::build_and_pin(temp, label, |_, pinned_root| {
        let bin_dir = pinned_root.join("bin");
        fs::create_dir_all(&bin_dir).map_err(|e| {
            format!("create private {label} staging bin dir {}: {e}", bin_dir.display())
        })?;
        let dst_bin = pinned_root.join(&rel_bin);
        copy_opened_file_to_new_dst(&mut opened.file, true, &dst_bin, true, label)
    })?;
    let _ = staging.open_verified_rel_file(&rel_bin, label)?;
    let staged_bin = staging.root().join(&rel_bin);
    Ok((staged_bin, Some(staging)))
}

pub(crate) fn stage_immutable_named_executable(
    bin_path: &Path,
    store_prefix: &Path,
    caller_cwd: &Path,
    tmp_parent: Option<&Path>,
    label: &str,
) -> Result<(PathBuf, Option<Arc<ImmutableStagingDir>>), String> {
    if let Some(res) =
        try_validate_store_contained_executable(bin_path, store_prefix, caller_cwd, label)
    {
        return Ok((res?, None));
    }
    let mut opened = open_verified_executable_via_dirfd(bin_path, caller_cwd, true, label)?;
    stage_immutable_opened_executable(&mut opened, tmp_parent, label)
}

#[cfg(test)]
pub(crate) fn prepare_toolchain_library_path(
    rust_sysroot: &Path,
    store_prefix: &Path,
    caller_cwd: &Path,
    materialize_top_level_symlinks: bool,
) -> Result<PreparedToolchainLibs, String> {
    prepare_toolchain_library_path_in(
        rust_sysroot,
        store_prefix,
        caller_cwd,
        materialize_top_level_symlinks,
        None,
    )
}

pub(crate) fn prepare_toolchain_library_path_in(
    rust_sysroot: &Path,
    store_prefix: &Path,
    caller_cwd: &Path,
    materialize_top_level_symlinks: bool,
    tmp_parent: Option<&Path>,
) -> Result<PreparedToolchainLibs, String> {
    let lib_dir = rust_sysroot.join("lib");
    match fs::symlink_metadata(&lib_dir) {
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            return Ok(PreparedToolchainLibs { ld_library_path: String::new(), _staging: None });
        }
        Err(e) => return Err(format!("stat rust_sysroot lib {}: {e}", lib_dir.display())),
        Ok(_) => {}
    }
    if let Some(res) = try_validate_store_contained_path(
        &lib_dir,
        store_prefix,
        caller_cwd,
        true,
        "rust_sysroot lib",
    ) {
        let canon = res?;
        let canon_store =
            crate::mir_eval_runner::validate_dir_path_no_symlinks(store_prefix, caller_cwd)?;
        validate_store_contained_dir_tree(&canon, &canon_store, &canon_store, "rust_sysroot lib")?;
        return Ok(PreparedToolchainLibs {
            ld_library_path: canon.display().to_string(),
            _staging: None,
        });
    }
    let canon_lib = crate::mir_eval_runner::validate_dir_path_no_symlinks(&lib_dir, caller_cwd)?;
    if materialize_top_level_symlinks {
        let _has_symlinks = inspect_sysroot_lib_dir_tree(&canon_lib, true, "rust_sysroot lib")?;
    } else {
        validate_dir_tree_no_links(&canon_lib, "rust_sysroot lib")?;
    }
    let (priv_lib, staging) =
        materialize_immutable_top_level_lib_in(&canon_lib, tmp_parent, "rust_sysroot lib")?;
    Ok(PreparedToolchainLibs {
        ld_library_path: priv_lib.display().to_string(),
        _staging: Some(staging),
    })
}

pub(crate) fn prepare_lean_library_path(
    lean_bin: &Path,
    store_prefix: &Path,
    caller_cwd: &Path,
) -> Result<PreparedLeanLibs, String> {
    prepare_lean_library_path_in(lean_bin, store_prefix, caller_cwd, None)
}

pub(crate) fn prepare_lean_library_path_in(
    lean_bin: &Path,
    store_prefix: &Path,
    caller_cwd: &Path,
    tmp_parent: Option<&Path>,
) -> Result<PreparedLeanLibs, String> {
    prepare_lean_library_path_inner(lean_bin, store_prefix, caller_cwd, tmp_parent, false)
}

pub(crate) fn prepare_lean_runtime_library_path_in(
    lean_bin: &Path,
    store_prefix: &Path,
    caller_cwd: &Path,
    tmp_parent: Option<&Path>,
) -> Result<PreparedLeanLibs, String> {
    prepare_lean_library_path_inner(lean_bin, store_prefix, caller_cwd, tmp_parent, true)
}

fn prepare_lean_library_path_inner(
    lean_bin: &Path,
    store_prefix: &Path,
    caller_cwd: &Path,
    tmp_parent: Option<&Path>,
    init_runtime_only: bool,
) -> Result<PreparedLeanLibs, String> {
    let abs_lean =
        if lean_bin.is_absolute() { lean_bin.to_path_buf() } else { caller_cwd.join(lean_bin) };
    let (canon_lean, mut opened_lean) = if let Some(res) =
        try_validate_store_contained_executable(&abs_lean, store_prefix, caller_cwd, "Lean binary")
    {
        (res?, None)
    } else {
        let opened =
            open_verified_executable_via_dirfd(&abs_lean, caller_cwd, true, "Lean binary")?;
        (opened.canon_path.clone(), Some(opened))
    };
    let is_store_lean = opened_lean.is_none();
    let mut dirs = Vec::new();
    let mut seen = BTreeSet::new();
    let mut lib_lean_dir = None;
    let mut source_lib_lean_dir = None;
    let mut pending_lib_stages: Vec<(&'static str, bool, &'static str, PathBuf)> = Vec::new();
    if let Some(prefix) = abs_lean.parent().and_then(Path::parent) {
        for (rel, allow_top_level_symlinks, label) in
            [("lib/lean", false, "lean toolchain lib/lean"), ("lib", true, "lean toolchain lib")]
        {
            let cand = prefix.join(rel);
            match fs::symlink_metadata(&cand) {
                Err(e) if e.kind() == std::io::ErrorKind::NotFound => continue,
                Err(e) => return Err(format!("stat {label} {}: {e}", cand.display())),
                Ok(_) => {}
            }
            if let Some(res) =
                try_validate_store_contained_path(&cand, store_prefix, caller_cwd, true, label)
            {
                let canon = res?;
                let canon_store = crate::mir_eval_runner::validate_dir_path_no_symlinks(
                    store_prefix,
                    caller_cwd,
                )?;
                validate_store_contained_dir_tree(&canon, &canon_store, &canon_store, label)?;
                if !allow_top_level_symlinks {
                    lib_lean_dir = Some(canon.clone());
                }
                if seen.insert(canon.clone()) {
                    dirs.push(canon);
                }
                continue;
            }
            let canon = crate::mir_eval_runner::validate_dir_path_no_symlinks(&cand, caller_cwd)?;
            if allow_top_level_symlinks {
                let _has_symlinks = inspect_sysroot_lib_dir_tree(&canon, false, label)?;
            }
            pending_lib_stages.push((rel, allow_top_level_symlinks, label, canon));
        }
    }

    let lean_file_name = if opened_lean.is_some() {
        Some(
            canon_lean
                .file_name()
                .ok_or_else(|| format!("Lean binary has no file name: {}", canon_lean.display()))?
                .to_os_string(),
        )
    } else {
        None
    };

    let staging_out = if !pending_lib_stages.is_empty() || opened_lean.is_some() {
        let temp = crate::mir_eval_runner::build_temp_dir("anneal-lean-libs-", tmp_parent)?;
        let (_, staging) =
            ImmutableStagingDir::build_and_pin(temp, "lean toolchain", |_, pinned_root| {
                for (rel, allow_top_level_symlinks, label, canon) in &pending_lib_stages {
                    let dst = pinned_root.join(rel);
                    if *allow_top_level_symlinks {
                        stage_top_level_lib_into_filtered(canon, &dst, init_runtime_only, label)?;
                    } else if init_runtime_only {
                        validate_dir_tree_no_links(canon, label)?;
                        copy_validated_subtree_with_filter(
                            canon,
                            &dst,
                            None,
                            false,
                            label,
                            is_lean_compiler_or_static_entry,
                        )?;
                    } else {
                        copy_validated_subtree(canon, &dst, None, false, label)?;
                    }
                }
                if let (Some(opened), Some(file_name)) = (opened_lean.as_mut(), &lean_file_name) {
                    let dst_bin_dir = pinned_root.join("bin");
                    fs::create_dir_all(&dst_bin_dir).map_err(|e| {
                        format!("create staged Lean bin dir {}: {e}", dst_bin_dir.display())
                    })?;
                    let dst_lean_bin = dst_bin_dir.join(file_name);
                    copy_opened_file_to_new_dst(
                        &mut opened.file,
                        true,
                        &dst_lean_bin,
                        true,
                        "Lean binary",
                    )?;
                }
                Ok(())
            })?;
        for (rel, allow_top_level_symlinks, _, canon) in pending_lib_stages {
            let dst = staging.root().join(rel);
            if !allow_top_level_symlinks {
                lib_lean_dir = Some(dst.clone());
                if init_runtime_only {
                    source_lib_lean_dir = Some(canon);
                }
            }
            if seen.insert(dst.clone()) {
                dirs.push(dst);
            }
        }
        Some(staging)
    } else {
        None
    };

    let (final_lean_bin, final_bin_dir) =
        if let (Some(staging), Some(file_name)) = (&staging_out, &lean_file_name) {
            let rel_bin = Path::new("bin").join(file_name);
            let _ = staging.open_verified_rel_file(&rel_bin, "Lean binary")?;
            let priv_root = staging.root();
            (priv_root.join(&rel_bin), priv_root.join("bin"))
        } else if is_store_lean {
            let bin_dir = canon_lean
                .parent()
                .ok_or_else(|| format!("Lean binary has no parent dir: {}", canon_lean.display()))?
                .to_path_buf();
            (canon_lean, bin_dir)
        } else {
            return Err("non-store Lean binary was not staged".to_owned());
        };
    let ld_library_path = if dirs.is_empty() {
        String::new()
    } else {
        env::join_paths(dirs)
            .map(|s| s.to_string_lossy().into_owned())
            .map_err(|e| format!("join Lean LD_LIBRARY_PATH: {e}"))?
    };
    Ok(PreparedLeanLibs {
        lean_bin: final_lean_bin,
        bin_dir: final_bin_dir,
        ld_library_path,
        lib_lean_dir,
        source_lib_lean_dir,
        _staging: staging_out,
    })
}

fn canonical_dir_matches_any(canon_dir: &Path, allowed_dirs: &[&Path], caller_cwd: &Path) -> bool {
    allowed_dirs.iter().any(|allowed| {
        crate::mir_eval_runner::validate_dir_path_no_symlinks(allowed, caller_cwd)
            .is_ok_and(|c| c == canon_dir)
    })
}

fn normalize_no_parent_dirs(path: &Path, label: &str) -> Result<PathBuf, String> {
    let mut out = PathBuf::new();
    for comp in path.components() {
        match comp {
            Component::Prefix(p) => out.push(p.as_os_str()),
            Component::RootDir => out.push(comp.as_os_str()),
            Component::CurDir => {}
            Component::ParentDir => {
                return Err(format!("{label} must not contain `..` traversal: {}", path.display()));
            }
            Component::Normal(seg) => out.push(seg),
        }
    }
    Ok(out)
}

fn validate_bounded_system_file(
    cand: &Path,
    trusted_dirs: &[&Path],
    symlink_dirs: &[&Path],
    caller_cwd: &Path,
    label: &str,
) -> Result<PathBuf, String> {
    let mut cur = cand.to_path_buf();
    for _ in 0..MAX_LINKER_SYMLINK_HOPS {
        let parent =
            cur.parent().ok_or_else(|| format!("{label} missing parent dir: {}", cur.display()))?;
        let canon_parent =
            crate::mir_eval_runner::validate_dir_path_no_symlinks(parent, caller_cwd)?;
        let meta = fs::symlink_metadata(&cur)
            .map_err(|e| format!("stat {label} {}: {e}", cur.display()))?;
        let nlink = hardlink_count(&meta);
        if nlink > 1 {
            return Err(format!(
                "{label} must not be a hardlink (nlink={nlink}): {}",
                cur.display()
            ));
        }
        if !meta.file_type().is_symlink() {
            if !canonical_dir_matches_any(&canon_parent, trusted_dirs, caller_cwd) {
                return Err(format!(
                    "{label} target escaped trusted system directories: {}",
                    cur.display()
                ));
            }
            return crate::mir_eval_runner::validate_executable_no_links(&cur, caller_cwd, label);
        }
        if !canonical_dir_matches_any(&canon_parent, trusted_dirs, caller_cwd)
            && !canonical_dir_matches_any(&canon_parent, symlink_dirs, caller_cwd)
        {
            return Err(format!("{label} symlink escaped trusted directories: {}", cur.display()));
        }
        let target =
            fs::read_link(&cur).map_err(|e| format!("readlink {label} {}: {e}", cur.display()))?;
        let raw_next = if target.is_absolute() { target } else { parent.join(target) };
        let next = normalize_no_parent_dirs(&raw_next, label)?;
        let next_parent = next
            .parent()
            .ok_or_else(|| format!("{label} symlink target missing parent: {}", next.display()))?;
        let canon_next_parent =
            crate::mir_eval_runner::validate_dir_path_no_symlinks(next_parent, caller_cwd)?;
        if !canonical_dir_matches_any(&canon_next_parent, trusted_dirs, caller_cwd)
            && !canonical_dir_matches_any(&canon_next_parent, symlink_dirs, caller_cwd)
        {
            return Err(format!(
                "{label} symlink target escaped trusted directories: {} -> {}",
                cur.display(),
                next.display()
            ));
        }
        cur = next;
    }
    Err(format!("{label} exceeded {MAX_LINKER_SYMLINK_HOPS} symlink hops: {}", cand.display()))
}

fn validate_trusted_system_linker(
    trusted_dirs: &[&Path],
    symlink_dirs: &[&Path],
    caller_cwd: &Path,
) -> Result<Option<PathBuf>, String> {
    for dir in trusted_dirs {
        let cand = dir.join(LINKER_BIN_NAME);
        match fs::symlink_metadata(&cand) {
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => continue,
            Err(e) => {
                return Err(format!("stat trusted Leg 0 linker {}: {e}", cand.display()));
            }
            Ok(_) => {
                let canon = validate_bounded_system_file(
                    &cand,
                    trusted_dirs,
                    symlink_dirs,
                    caller_cwd,
                    "Leg 0 linker binary",
                )?;
                return Ok(Some(canon));
            }
        }
    }
    Ok(None)
}

fn validate_store_linker_from_path(
    store_prefix: &Path,
    canon_store: &Path,
    path_env: Option<&OsStr>,
    caller_cwd: &Path,
) -> Result<Option<PathBuf>, String> {
    let Some(path_var) = path_env else {
        return Ok(None);
    };
    for dir in env::split_paths(path_var) {
        if !dir.is_absolute() || dir.components().any(|c| matches!(c, Component::ParentDir)) {
            continue;
        }
        let cand = dir.join(LINKER_BIN_NAME);
        match fs::symlink_metadata(&cand) {
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => continue,
            Err(e) => {
                return Err(format!("stat store Leg 0 linker {}: {e}", cand.display()));
            }
            Ok(_) => {
                if dir.starts_with(store_prefix) && dir != store_prefix {
                    let canon = validate_store_contained_entry(
                        &cand,
                        store_prefix,
                        canon_store,
                        false,
                        "Leg 0 linker binary",
                    )?;
                    return Ok(Some(canon));
                }
                if let Some(res) = try_validate_store_contained_executable(
                    &cand,
                    store_prefix,
                    caller_cwd,
                    "Leg 0 linker binary",
                ) {
                    return res.map(Some);
                }
            }
        }
    }
    Ok(None)
}

pub(crate) fn resolve_and_validate_linker_with(
    rust_sysroot: &Path,
    store_prefix: &Path,
    trusted_dirs: &[&Path],
    symlink_dirs: &[&Path],
    ambient_path: Option<&OsStr>,
    caller_cwd: &Path,
) -> Result<PathBuf, String> {
    let is_store_sysroot =
        rust_sysroot.starts_with(store_prefix) && fs::symlink_metadata(store_prefix).is_ok();

    if is_store_sysroot {
        let canon_store =
            crate::mir_eval_runner::validate_dir_path_no_symlinks(store_prefix, caller_cwd)?;
        if let Some(linker) =
            validate_store_linker_from_path(store_prefix, &canon_store, ambient_path, caller_cwd)?
        {
            return Ok(linker);
        }
        if let Some(linker) =
            validate_trusted_system_linker(trusted_dirs, symlink_dirs, caller_cwd)?
        {
            return Ok(linker);
        }
    } else {
        if let Some(linker) =
            validate_trusted_system_linker(trusted_dirs, symlink_dirs, caller_cwd)?
        {
            return Ok(linker);
        }
        if fs::symlink_metadata(store_prefix).is_ok() {
            let canon_store =
                crate::mir_eval_runner::validate_dir_path_no_symlinks(store_prefix, caller_cwd)?;
            if let Some(linker) = validate_store_linker_from_path(
                store_prefix,
                &canon_store,
                ambient_path,
                caller_cwd,
            )? {
                return Ok(linker);
            }
        }
    }

    Err(format!(
        "cannot resolve validated Leg 0 linker (`{LINKER_BIN_NAME}`) in trusted system directories or Nix store"
    ))
}

fn build_child_path_with(
    primary_bin: &Path,
    linker: &Path,
    store_prefix: &Path,
    trusted_child_dirs: &[&Path],
    ambient_path: Option<&OsStr>,
    caller_cwd: &Path,
) -> Result<OsString, String> {
    build_child_path_with_bins(
        &[primary_bin],
        Some(linker),
        store_prefix,
        trusted_child_dirs,
        ambient_path,
        caller_cwd,
    )
}

pub(crate) fn build_child_path_with_bins(
    primary_bins: &[&Path],
    linker: Option<&Path>,
    store_prefix: &Path,
    trusted_child_dirs: &[&Path],
    ambient_path: Option<&OsStr>,
    caller_cwd: &Path,
) -> Result<OsString, String> {
    let mut seen = BTreeSet::new();
    let mut path_entries = Vec::new();
    let mut push_unique = |dir: PathBuf| {
        if seen.insert(dir.clone()) {
            path_entries.push(dir);
        }
    };

    for dir in primary_bins {
        push_unique((*dir).to_path_buf());
    }
    if let Some(linker_dir) = linker.and_then(Path::parent) {
        push_unique(linker_dir.to_path_buf());
    }

    let uses_store_prefix = primary_bins.iter().any(|p| p.starts_with(store_prefix))
        || linker.is_some_and(|l| l.starts_with(store_prefix));
    if uses_store_prefix && fs::symlink_metadata(store_prefix).is_ok() {
        let canon_store =
            crate::mir_eval_runner::validate_dir_path_no_symlinks(store_prefix, caller_cwd)?;
        let uses_store = primary_bins.iter().any(|p| p.starts_with(&canon_store))
            || linker.is_some_and(|l| l.starts_with(&canon_store));
        if uses_store && let Some(path_var) = ambient_path {
            for dir in env::split_paths(path_var) {
                if !dir.is_absolute() || dir.components().any(|c| matches!(c, Component::ParentDir))
                {
                    continue;
                }
                if dir.starts_with(store_prefix) && dir != store_prefix {
                    if matches!(
                        fs::symlink_metadata(&dir),
                        Err(e) if e.kind() == std::io::ErrorKind::NotFound
                    ) {
                        continue;
                    }
                    let canon_dir = validate_store_contained_entry(
                        &dir,
                        store_prefix,
                        &canon_store,
                        true,
                        "toolchain store PATH dir",
                    )?;
                    push_unique(canon_dir);
                    continue;
                }
                if let Some(res) = try_validate_store_contained_path(
                    &dir,
                    store_prefix,
                    caller_cwd,
                    true,
                    "toolchain store PATH dir",
                ) {
                    push_unique(res?);
                }
            }
        }
    }

    for sys_dir in trusted_child_dirs {
        match fs::symlink_metadata(sys_dir) {
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => continue,
            Err(e) => {
                return Err(format!("stat trusted PATH dir {}: {e}", sys_dir.display()));
            }
            Ok(meta) => {
                if !meta.file_type().is_symlink() {
                    let canon =
                        crate::mir_eval_runner::validate_dir_path_no_symlinks(sys_dir, caller_cwd)?;
                    push_unique(canon);
                } else if *sys_dir == Path::new("/bin") {
                    // Debian/Ubuntu usrmerge symlinks `/bin -> usr/bin`; accept
                    // only when its canonical target is `/usr/bin` and
                    // symlink-free.
                    let canon = fs::canonicalize(sys_dir)
                        .map_err(|e| format!("canonicalize {}: {e}", sys_dir.display()))?;
                    if canon != Path::new("/usr/bin") {
                        return Err(format!(
                            "trusted PATH dir {} symlinked outside /usr/bin: {}",
                            sys_dir.display(),
                            canon.display()
                        ));
                    }
                    let valid_usr =
                        crate::mir_eval_runner::validate_dir_path_no_symlinks(&canon, caller_cwd)?;
                    push_unique(valid_usr);
                } else {
                    return Err(format!(
                        "trusted PATH dir must not be a symlink: {}",
                        sys_dir.display()
                    ));
                }
            }
        }
    }

    env::join_paths(path_entries).map_err(|e| format!("join PATH entries: {e}"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::verdict::IntKind;

    #[test]
    fn generates_batch_and_single_rustc_harness_and_parses_batch_stdout() {
        let cases = vec![
            FuzzExecCase {
                case_id: "c0".to_owned(),
                fn_name: "f0".to_owned(),
                args: vec![MirValue::Int { int_kind: IntKind::U32, bits: 3 }],
                ret_shape: MirValue::Int { int_kind: IntKind::U32, bits: 0 },
                fuel: 200,
                expected_clean_batch: true,
            },
            FuzzExecCase {
                case_id: "c1".to_owned(),
                fn_name: "f1".to_owned(),
                args: vec![],
                ret_shape: MirValue::Bool { value: false },
                fuel: 200,
                expected_clean_batch: true,
            },
        ];
        let src = "#![no_std]\npub fn f0(x: u32) -> u32 { x + 1 }\npub fn f1() -> bool { true }\n";
        let harness = generate_rustc_harness(src, &cases).expect("generate rustc harness");
        assert!(harness.contains("__BATCH__"));
        assert!(harness.contains("ANNEAL_RUSTC_RUN:c0:f0"));
        assert!(harness.contains("ANNEAL_RUSTC_CASE:c0:"));
        assert!(harness.contains("ANNEAL_RUSTC_RUN:c1:f1"));
        assert!(harness.contains("ANNEAL_RUSTC_CASE:c1:"));

        let refs: Vec<&FuzzExecCase> = cases.iter().collect();
        let parsed = parse_rustc_batch_stdout(
            "ANNEAL_RUSTC_RUN:c0:f0\nANNEAL_RUSTC_CASE:c0:INT:u32:4\n\
             ANNEAL_RUSTC_RUN:c1:f1\nANNEAL_RUSTC_CASE:c1:BOOL:true\n",
            &refs,
        )
        .expect("parse complete batch output");
        assert_eq!(
            parsed["c0"].0,
            ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 4 } }
        );
        assert_eq!(
            parsed["c0"].1.as_deref(),
            Some("ANNEAL_RUSTC_RUN:c0:f0|ANNEAL_RUSTC_CASE:c0:INT:u32:4")
        );
        assert_eq!(
            parsed["c1"].0,
            ObservedOutcome::Returned { value: MirValue::Bool { value: true } }
        );
        assert_eq!(
            parsed["c1"].1.as_deref(),
            Some("ANNEAL_RUSTC_RUN:c1:f1|ANNEAL_RUSTC_CASE:c1:BOOL:true")
        );

        // Missing a case line or RUN marker must return None to trigger
        // isolated fallback!
        assert!(
            parse_rustc_batch_stdout(
                "ANNEAL_RUSTC_RUN:c0:f0\nANNEAL_RUSTC_CASE:c0:INT:u32:4\n",
                &refs
            )
            .is_none()
        );
        assert!(
            parse_rustc_batch_stdout(
                "ANNEAL_RUSTC_CASE:c0:INT:u32:4\nANNEAL_RUSTC_CASE:c1:BOOL:true\n",
                &refs
            )
            .is_none()
        );
    }

    #[test]
    fn rejects_non_64_bit_host_and_parses_cfg_pointer_width() {
        assert!(ensure_64_bit_host(64).is_ok());
        let err = ensure_64_bit_host(32).expect_err("32-bit host must fail");
        assert!(err.contains("32-bit"), "{err}");
        assert!(err.contains("--no-rustc"), "{err}");

        assert_eq!(
            parse_target_pointer_width(
                "target_arch=\"x86_64\"\ntarget_pointer_width=\"64\"\ntarget_os=\"linux\"\n"
            )
            .expect("64-bit cfg"),
            64
        );
        assert_eq!(
            parse_target_pointer_width("target_pointer_width=\"32\"\n").expect("32-bit cfg"),
            32
        );
        assert!(parse_target_pointer_width("target_arch=\"i686\"\n").is_err());
        assert!(
            parse_target_pointer_width(
                "target_pointer_width=\"32\"\ntarget_pointer_width=\"64\"\n"
            )
            .is_err()
        );
    }

    #[cfg(unix)]
    #[test]
    fn prepare_rejects_32_bit_rustc_target_before_compiling() {
        use std::os::unix::fs::PermissionsExt;

        let tmp = tempfile::tempdir().expect("tempdir");
        let sysroot32 = tmp.path().join("sysroot-32");
        fs::create_dir_all(sysroot32.join("bin")).expect("create 32-bit bin");
        fs::create_dir_all(sysroot32.join("lib")).expect("create 32-bit lib");
        let rustc32 = sysroot32.join("bin/rustc");
        fs::write(
            &rustc32,
            "#!/bin/sh\nset -eu\n\
             print_kind=\"\"\n\
             while [ \"$#\" -gt 0 ]; do\n\
               case \"$1\" in\n\
                 --sysroot) shift ;;\n\
                 --print) shift; print_kind=\"${1:-}\" ;;\n\
                 -o) echo \"unexpected compile invocation\" >&2; exit 2 ;;\n\
               esac\n\
               shift\n\
             done\n\
             if [ \"$print_kind\" = \"sysroot\" ]; then printf '%s\\n' \"$0\"; exit 0; fi\n\
             if [ \"$print_kind\" = \"cfg\" ]; then\n\
               printf 'target_arch=\"x86\"\\ntarget_pointer_width=\"32\"\\n'\n\
               exit 0\n\
             fi\n\
             exit 1\n",
        )
        .expect("write 32-bit rustc stub");
        fs::set_permissions(&rustc32, fs::Permissions::from_mode(0o755)).expect("chmod 32-bit");

        let err = RustcSession::prepare(&sysroot32).expect_err("32-bit rustc must fail");
        assert!(err.contains("32-bit"), "{err}");
        assert!(err.contains("64-bit"), "{err}");
        assert!(err.contains("--no-rustc"), "{err}");
    }

    #[cfg(unix)]
    #[test]
    fn prepare_skips_duplicate_sysroot_for_wrapper_and_preserves_for_unwrapped_rustc() {
        use std::os::unix::fs::PermissionsExt;

        let tmp = tempfile::tempdir().expect("tempdir");
        let base = fs::canonicalize(tmp.path()).expect("canonicalize tempdir");

        // 1. Wrapper `bin/rustc` (regular non-linked file outside `/nix/store`)
        // that injects its own `--sysroot <underlying>` and fails when
        // `--sysroot` is passed a second time.
        let underlying = base.join("rust-toolchain");
        fs::create_dir_all(underlying.join("lib")).expect("create underlying lib");
        let wrapper_sysroot = base.join("anneal-wrapper-sysroot");
        fs::create_dir_all(wrapper_sysroot.join("bin")).expect("create wrapper sysroot bin");
        fs::create_dir_all(wrapper_sysroot.join("lib")).expect("create wrapper sysroot lib");
        let wrapper = wrapper_sysroot.join("bin/rustc");
        fs::write(
            &wrapper,
            format!(
                "#!/bin/sh\nset -eu\n\
                 print_kind=\"\"\nout_bin=\"\"\n\
                 while [ \"$#\" -gt 0 ]; do\n\
                   case \"$1\" in\n\
                     --sysroot) echo \"error: Option 'sysroot' given more than once\" >&2; exit 1 ;;\n\
                     --print) shift; print_kind=\"${{1:-}}\" ;;\n\
                     -o) shift; out_bin=\"${{1:-}}\" ;;\n\
                   esac\n\
                   shift\n\
                 done\n\
                 if [ \"$print_kind\" = \"sysroot\" ]; then printf '%s\\n' '{}'; exit 0; fi\n\
                 if [ \"$print_kind\" = \"cfg\" ]; then printf 'target_pointer_width=\"64\"\\n'; exit 0; fi\n\
                 printf '#!/bin/sh\\nprintf \"ANNEAL_RUSTC_RUN:c0:f0\\\\nANNEAL_RUSTC_CASE:c0:INT:u32:7\\\\n\"\\n' > \"$out_bin\"\n\
                 chmod +x \"$out_bin\"\n",
                underlying.display()
            ),
        )
        .expect("write wrapper");
        fs::set_permissions(&wrapper, fs::Permissions::from_mode(0o755)).expect("chmod wrapper");

        let wrapper_session =
            RustcSession::prepare(&wrapper_sysroot).expect("prepare wrapper rustc");
        assert!(!wrapper_session.pass_sysroot_arg);

        let cases = vec![FuzzExecCase {
            case_id: "c0".to_owned(),
            fn_name: "f0".to_owned(),
            args: vec![],
            ret_shape: MirValue::Int { int_kind: IntKind::U32, bits: 0 },
            fuel: 200,
            expected_clean_batch: true,
        }];
        let wrapper_out = wrapper_session
            .run_batch("#![no_std]\npub fn f0() -> u32 { 7 }\n", &cases)
            .expect("run batch through wrapper");
        assert_eq!(
            wrapper_out["c0"],
            ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 7 } }
        );

        // 2. Unwrapped `<sysroot>/bin/rustc`: accepts explicit `--sysroot` and
        // fails without it.
        let unwrapped_sysroot = base.join("unwrapped-sysroot");
        fs::create_dir_all(unwrapped_sysroot.join("bin")).expect("create unwrapped bin");
        fs::create_dir_all(unwrapped_sysroot.join("lib")).expect("create unwrapped lib");
        let unwrapped_bin = unwrapped_sysroot.join("bin/rustc");
        fs::write(
            &unwrapped_bin,
            "#!/bin/sh\nset -eu\n\
             seen_sysroot=\"\"\nprint_kind=\"\"\nout_bin=\"\"\n\
             while [ \"$#\" -gt 0 ]; do\n\
               case \"$1\" in\n\
                 --sysroot) shift; seen_sysroot=\"${1:-}\" ;;\n\
                 --print) shift; print_kind=\"${1:-}\" ;;\n\
                 -o) shift; out_bin=\"${1:-}\" ;;\n\
               esac\n\
               shift\n\
             done\n\
             if [ -z \"$seen_sysroot\" ]; then echo \"missing --sysroot\" >&2; exit 1; fi\n\
             if [ \"$print_kind\" = \"sysroot\" ]; then printf '%s\\n' \"$seen_sysroot\"; exit 0; fi\n\
             if [ \"$print_kind\" = \"cfg\" ]; then printf 'target_pointer_width=\"64\"\\n'; exit 0; fi\n\
             printf '#!/bin/sh\\nprintf \"ANNEAL_RUSTC_RUN:c0:f0\\\\nANNEAL_RUSTC_CASE:c0:INT:u32:7\\\\n\"\\n' > \"$out_bin\"\n\
             chmod +x \"$out_bin\"\n",
        )
        .expect("write unwrapped stub");
        fs::set_permissions(&unwrapped_bin, fs::Permissions::from_mode(0o755))
            .expect("chmod unwrapped");

        let direct_session =
            RustcSession::prepare(&unwrapped_sysroot).expect("prepare unwrapped rustc");
        assert!(direct_session.pass_sysroot_arg);
        let direct_out = direct_session
            .run_batch("#![no_std]\npub fn f0() -> u32 { 7 }\n", &cases)
            .expect("run batch through direct rustc");
        assert_eq!(
            direct_out["c0"],
            ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 7 } }
        );
    }

    #[cfg(unix)]
    #[test]
    fn prepare_rejects_outside_store_symlinks_and_hardlinks_before_invoking() {
        use std::os::unix::fs::{PermissionsExt, symlink};

        let tmp = tempfile::tempdir().expect("tempdir");
        let base = fs::canonicalize(tmp.path()).expect("canonicalize tempdir");
        let marker = base.join("invoked.marker");
        let target_bin = base.join("real-rustc");
        fs::write(
            &target_bin,
            format!(
                "#!/bin/sh\ntouch '{}'\nprintf 'target_pointer_width=\"64\"\\n'\n",
                marker.display()
            ),
        )
        .expect("write target stub");
        fs::set_permissions(&target_bin, fs::Permissions::from_mode(0o755)).expect("chmod stub");

        // 1. Symlinked `bin/rustc` outside `/nix/store`.
        let sym_leaf_sys = base.join("sym-leaf-sys");
        fs::create_dir_all(sym_leaf_sys.join("bin")).unwrap();
        fs::create_dir_all(sym_leaf_sys.join("lib")).unwrap();
        symlink(&target_bin, sym_leaf_sys.join("bin/rustc")).unwrap();
        let err = RustcSession::prepare(&sym_leaf_sys).expect_err("symlinked bin/rustc must fail");
        assert!(err.contains("symlink"), "{err}");
        assert!(!marker.exists(), "must reject symlinked bin/rustc before invoking it");

        // 2. Symlinked `bin/` directory outside `/nix/store`.
        let real_bin_dir = base.join("real-bin-dir");
        fs::create_dir_all(&real_bin_dir).unwrap();
        fs::copy(&target_bin, real_bin_dir.join("rustc")).unwrap();
        let sym_bin_sys = base.join("sym-bin-sys");
        fs::create_dir_all(sym_bin_sys.join("lib")).unwrap();
        symlink(&real_bin_dir, sym_bin_sys.join("bin")).unwrap();
        let err = RustcSession::prepare(&sym_bin_sys).expect_err("symlinked bin/ must fail");
        assert!(err.contains("symlink"), "{err}");
        assert!(!marker.exists(), "must reject symlinked bin/ before invoking rustc");

        // 3. Symlinked sysroot ancestor outside `/nix/store`.
        let sym_root_sys = base.join("sym-root-sys");
        let real_root_sys = base.join("real-root-sys");
        fs::create_dir_all(real_root_sys.join("bin")).unwrap();
        fs::create_dir_all(real_root_sys.join("lib")).unwrap();
        fs::copy(&target_bin, real_root_sys.join("bin/rustc")).unwrap();
        symlink(&real_root_sys, &sym_root_sys).unwrap();
        let err = RustcSession::prepare(&sym_root_sys).expect_err("symlinked sysroot must fail");
        assert!(err.contains("symlink"), "{err}");
        assert!(!marker.exists(), "must reject symlinked sysroot before invoking rustc");

        // 4. Hardlinked `bin/rustc` (`st_nlink > 1`).
        let hard_sys = base.join("hardlink-sys");
        fs::create_dir_all(hard_sys.join("bin")).unwrap();
        fs::create_dir_all(hard_sys.join("lib")).unwrap();
        fs::hard_link(&target_bin, hard_sys.join("bin/rustc")).unwrap();
        let err = RustcSession::prepare(&hard_sys).expect_err("hardlinked bin/rustc must fail");
        assert!(err.contains("hardlink"), "{err}");
        assert!(!marker.exists(), "must reject hardlinked bin/rustc before invoking rustc");
    }

    #[cfg(unix)]
    #[test]
    fn validate_sysroot_allows_store_joined_symlink_and_rejects_escape() {
        use std::os::unix::fs::{PermissionsExt, symlink};

        let tmp = tempfile::tempdir().expect("tempdir");
        let base = fs::canonicalize(tmp.path()).expect("canonicalize tempdir");
        let fake_store = base.join("nix-store");
        let pkg_build = fake_store.join("aaaa-anneal-build-rustc");
        let pkg_sysroot = fake_store.join("bbbb-anneal-test-sysroot");
        let pkg_toolchain = fake_store.join("cccc-rust-toolchain");
        fs::create_dir_all(pkg_build.join("bin")).unwrap();
        fs::create_dir_all(pkg_toolchain.join("lib")).unwrap();
        fs::create_dir_all(pkg_sysroot.join("bin")).unwrap();

        let real_rustc = pkg_build.join("bin/anneal-build-rustc");
        fs::write(&real_rustc, "#!/bin/sh\nexit 0\n").unwrap();
        fs::set_permissions(&real_rustc, fs::Permissions::from_mode(0o755)).unwrap();
        symlink(&real_rustc, pkg_sysroot.join("bin/rustc")).unwrap();
        symlink(pkg_toolchain.join("lib"), pkg_sysroot.join("lib")).unwrap();

        // Store-contained `symlinkJoin` succeeds.
        let prepared =
            prepare_sysroot_binary(&pkg_sysroot, "bin/rustc", &fake_store, "Leg 0 rustc binary")
                .expect("store-contained symlinkJoin must succeed");
        assert_eq!(prepared.sysroot, pkg_sysroot);
        assert_eq!(prepared.binary, real_rustc);

        // Store `bin/rustc` symlink escaping outside `fake_store` fails.
        let outside = base.join("outside-rustc");
        fs::write(&outside, "#!/bin/sh\nexit 0\n").unwrap();
        let escape_sysroot = fake_store.join("dddd-escaping-sysroot");
        fs::create_dir_all(escape_sysroot.join("bin")).unwrap();
        symlink(&outside, escape_sysroot.join("bin/rustc")).unwrap();
        let err =
            prepare_sysroot_binary(&escape_sysroot, "bin/rustc", &fake_store, "Leg 0 rustc binary")
                .expect_err("store symlink escaping outside store must fail");
        assert!(err.contains("escaped store"), "{err}");

        // Parent traversal through store fails.
        let parent_escape = fake_store.join("../outside-dir");
        fs::create_dir_all(parent_escape.join("bin")).unwrap();
        fs::write(parent_escape.join("bin/rustc"), "#!/bin/sh\nexit 0\n").unwrap();
        assert!(
            prepare_sysroot_binary(&parent_escape, "bin/rustc", &fake_store, "Leg 0 rustc binary")
                .is_err()
        );

        // Hardlink to `nlink > 1` inside store is still rejected.
        let hard_pkg = fake_store.join("eeee-hard-sysroot");
        fs::create_dir_all(hard_pkg.join("bin")).unwrap();
        fs::hard_link(&real_rustc, hard_pkg.join("bin/rustc")).unwrap();
        let err = prepare_sysroot_binary(&hard_pkg, "bin/rustc", &fake_store, "Leg 0 rustc binary")
            .expect_err("hardlink inside store must still fail");
        assert!(err.contains("hardlink"), "{err}");
    }

    #[cfg(unix)]
    #[test]
    fn rustc_compile_diagnostic_bisects_subset_crates_to_isolate_bad_program() {
        use std::os::unix::fs::PermissionsExt;

        use crate::r#gen::{GenCategory, GenExpr, GenType};

        let tmp = tempfile::tempdir().expect("tempdir");
        let base = fs::canonicalize(tmp.path()).expect("canonicalize tempdir");
        let fake_sysroot = base.join("fake-sysroot");
        fs::create_dir_all(fake_sysroot.join("bin")).unwrap();
        fs::create_dir_all(fake_sysroot.join("lib")).unwrap();
        let fake_rustc = fake_sysroot.join("bin/rustc");
        let log_file = base.join("compile.log");

        // Compile succeeds cleanly whenever `corpus::fuzz_fn_5` is absent, and
        // fails with ordinary diagnostic `error[E0308]` when `fuzz_fn_5` is
        // present. Compiled harness emits deterministic u32 outputs for both
        // `__BATCH__` and isolated single-case selectors.
        fs::write(
            &fake_rustc,
            format!(
                "#!/bin/sh\nset -eu\n\
                 print_kind=\"\"\nout_bin=\"\"\nsrc_file=\"\"\n\
                 while [ \"$#\" -gt 0 ]; do\n\
                   case \"$1\" in\n\
                     --sysroot|-C|--edition) shift ;;\n\
                     --edition=*) ;;\n\
                     --print) shift; print_kind=\"${{1:-}}\" ;;\n\
                     -o) shift; out_bin=\"${{1:-}}\" ;;\n\
                     *.rs) src_file=\"$1\" ;;\n\
                   esac\n\
                   shift\n\
                 done\n\
                 if [ \"$print_kind\" = \"sysroot\" ]; then printf '%s\\n' '{}'; exit 0; fi\n\
                 if [ \"$print_kind\" = \"cfg\" ]; then printf 'target_pointer_width=\"64\"\\n'; exit 0; fi\n\
                 echo \"$src_file\" >> '{}'\n\
                 if grep -q 'fn fuzz_fn_5(' \"$src_file\"; then\n\
                   echo 'error[E0308]: mismatched types in fuzz_fn_5' >&2\n\
                   exit 1\n\
                 fi\n\
                 cat > \"$out_bin\" <<'EOFBIN'\n\
#!/bin/sh\n\
if [ \"$1\" = \"__BATCH__\" ]; then\n\
  shift\n\
  for cid in \"$@\"; do\n\
    idx=\"${{cid#case_}}\"\n\
    printf 'ANNEAL_RUSTC_RUN:%s:fuzz_fn_%s\\n' \"$cid\" \"$idx\"\n\
    printf 'ANNEAL_RUSTC_CASE:%s:INT:u32:7\\n' \"$cid\"\n\
  done\n\
else\n\
  cid=\"$1\"\n\
  idx=\"${{cid#case_}}\"\n\
  printf 'ANNEAL_RUSTC_RUN:%s:fuzz_fn_%s\\n' \"$cid\" \"$idx\"\n\
  printf 'ANNEAL_RUSTC_CASE:%s:INT:u32:7\\n' \"$cid\"\n\
fi\n\
EOFBIN\n\
                 chmod +x \"$out_bin\"\n",
                fake_sysroot.display(),
                log_file.display()
            ),
        )
        .unwrap();
        fs::set_permissions(&fake_rustc, fs::Permissions::from_mode(0o755)).unwrap();

        let session = RustcSession::prepare(&fake_sysroot).expect("prepare fake rustc session");

        let programs: Vec<GenProgram> = (0..8)
            .map(|i| GenProgram {
                case_id: format!("case_{i}"),
                fn_name: format!("fuzz_fn_{i}"),
                master_seed: 1,
                case_index: i,
                category: if i == 6 {
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
            .run_batch_crate_with_evidence_until(&full_src, &prog_refs, &cases, None)
            .expect("rustc subset bisection");

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

        // Clean-batch isolation must likewise render only clean programs and
        // bisect any case-local compile diagnostic individually without
        // invoking `__BATCH__` or poisoning valid clean neighbors.
        let clean_progs: Vec<&GenProgram> =
            programs.iter().filter(|p| p.category.counts_toward_admission()).collect();
        let clean_cases: Vec<FuzzExecCase> =
            cases.iter().filter(|c| c.expected_clean_batch).cloned().collect();
        let isolated_out = session
            .run_isolated_programs_with_evidence_until(&clean_progs, &clean_cases, None)
            .expect("isolated clean-program bisection");
        assert_eq!(isolated_out.len(), clean_cases.len());
        for c in &clean_cases {
            if c.case_id == "case_5" {
                assert!(matches!(
                    &isolated_out[&c.case_id].0,
                    ObservedOutcome::ToolError { detail } if detail.contains("error[E0308]")
                ));
            } else {
                assert_eq!(
                    isolated_out[&c.case_id].0,
                    ObservedOutcome::Returned {
                        value: MirValue::Int { int_kind: IntKind::U32, bits: 7 }
                    },
                    "clean isolation poisoned {}",
                    c.case_id
                );
            }
        }
    }

    #[cfg(unix)]
    #[test]
    fn session_pins_explicit_linker_and_strips_poisoned_ambient_path() {
        use std::os::unix::fs::{PermissionsExt, symlink};

        let tmp = tempfile::tempdir().expect("tempdir");
        let base = fs::canonicalize(tmp.path()).expect("canonicalize tempdir");
        let fake_store = base.join("nix-store");
        let sysroot = base.join("sysroot");
        let trusted_bin = base.join("trusted-usr-bin");
        let alternatives = base.join("trusted-alternatives");
        let evil_dir = base.join("evil-path");
        for d in [
            fake_store.as_path(),
            sysroot.join("bin").as_path(),
            sysroot.join("lib").as_path(),
            trusted_bin.as_path(),
            alternatives.as_path(),
            evil_dir.as_path(),
        ] {
            fs::create_dir_all(d).unwrap();
        }

        // Poisoned ambient PATH entries carrying fake `cc` and `ld`.
        let evil_cc = evil_dir.join(LINKER_BIN_NAME);
        let evil_ld = evil_dir.join("ld");
        fs::write(&evil_cc, "#!/bin/sh\nexit 99\n").unwrap();
        fs::write(&evil_ld, "#!/bin/sh\nexit 99\n").unwrap();
        fs::set_permissions(&evil_cc, fs::Permissions::from_mode(0o755)).unwrap();
        fs::set_permissions(&evil_ld, fs::Permissions::from_mode(0o755)).unwrap();

        // Debian-style multi-hop alternatives symlink inside trusted dirs.
        let real_gcc = trusted_bin.join("gcc-real");
        fs::write(&real_gcc, "#!/bin/sh\nexit 0\n").unwrap();
        fs::set_permissions(&real_gcc, fs::Permissions::from_mode(0o755)).unwrap();
        symlink(&real_gcc, alternatives.join(LINKER_BIN_NAME)).unwrap();
        symlink(alternatives.join(LINKER_BIN_NAME), trusted_bin.join(LINKER_BIN_NAME)).unwrap();

        let args_log = base.join("rustc_args.log");
        let path_log = base.join("rustc_path.log");
        let rustc_ld_log = base.join("rustc_ld.log");
        let bin_ld_log = base.join("bin_ld.log");
        let rustc_stub = sysroot.join("bin/rustc");
        fs::write(
            &rustc_stub,
            format!(
                "#!/bin/sh\nset -eu\n\
                 print_kind=\"\"\nout_bin=\"\"\n\
                 seen_linker=\"\"\nprev=\"\"\n\
                 for a in \"$@\"; do\n\
                   if [ \"$prev\" = \"-C\" ] && [ -z \"$seen_linker\" ]; then\n\
                     case \"$a\" in linker=*) seen_linker=\"${{a#linker=}}\" ;; esac\n\
                   fi\n\
                   prev=\"$a\"\n\
                 done\n\
                 while [ \"$#\" -gt 0 ]; do\n\
                   case \"$1\" in\n\
                     --sysroot|-C|--edition) shift ;;\n\
                     --print) shift; print_kind=\"${{1:-}}\" ;;\n\
                     -o) shift; out_bin=\"${{1:-}}\" ;;\n\
                   esac\n\
                   shift\n\
                 done\n\
                 if [ \"$print_kind\" = \"sysroot\" ]; then printf '%s\\n' '{}'; exit 0; fi\n\
                 if [ \"$print_kind\" = \"cfg\" ]; then printf 'target_pointer_width=\"64\"\\n'; exit 0; fi\n\
                 printf '%s\\n' \"$seen_linker\" > '{}'\n\
                 printf '%s\\n' \"$PATH\" > '{}'\n\
                 printf '%s\\n' \"${{LD_LIBRARY_PATH:-}}\" > '{}'\n\
                 cat > \"$out_bin\" <<'EOFBIN'\n\
#!/bin/sh\n\
printf '%s\\n' \"${{LD_LIBRARY_PATH:-}}\" > '{}'\n\
printf \"ANNEAL_RUSTC_RUN:c0:f0\\nANNEAL_RUSTC_CASE:c0:INT:u32:7\\n\"\n\
EOFBIN\n\
                 chmod +x \"$out_bin\"\n",
                sysroot.display(),
                args_log.display(),
                path_log.display(),
                rustc_ld_log.display(),
                bin_ld_log.display()
            ),
        )
        .unwrap();
        fs::set_permissions(&rustc_stub, fs::Permissions::from_mode(0o755)).unwrap();

        // Keep real system utilities (`/usr/bin` or `/bin`) available in
        // `trusted_child_dirs` so POSIX `/bin/sh` + `chmod` execute while
        // poisoned `evil_dir` and relative `./evil` are dropped from PATH.
        let mut child_dirs: Vec<&Path> = vec![trusted_bin.as_path()];
        for sys_cand in [Path::new("/usr/bin"), Path::new("/bin")] {
            if fs::symlink_metadata(sys_cand).is_ok() {
                child_dirs.push(sys_cand);
            }
        }
        let poisoned_env = env::join_paths([
            evil_dir.as_path(),
            Path::new("./relative-evil"),
            trusted_bin.as_path(),
        ])
        .unwrap();

        let session = RustcSession::prepare_with_config(
            &sysroot,
            &fake_store,
            &[trusted_bin.as_path()],
            &[alternatives.as_path()],
            &child_dirs,
            Some(poisoned_env.as_os_str()),
        )
        .expect("prepare with poisoned ambient PATH must pin trusted linker");

        assert_eq!(session.linker, real_gcc);
        assert!(session._sysroot_staging.is_some());
        assert_ne!(session.rust_sysroot, sysroot);
        let expected_staged_lib = session.rust_sysroot.join("lib").to_string_lossy().into_owned();
        assert_eq!(session.ld_library_path, expected_staged_lib);
        let child_dirs_out: Vec<PathBuf> = env::split_paths(&session.child_path).collect();
        assert!(!child_dirs_out.contains(&evil_dir), "poisoned PATH leaked: {child_dirs_out:?}");
        assert!(
            !child_dirs_out.contains(&PathBuf::from("./relative-evil")),
            "relative PATH leaked: {child_dirs_out:?}"
        );
        assert!(child_dirs_out.contains(&session.rust_sysroot.join("bin")));
        assert!(child_dirs_out.contains(&trusted_bin));

        let cases = vec![FuzzExecCase {
            case_id: "c0".to_owned(),
            fn_name: "f0".to_owned(),
            args: vec![],
            ret_shape: MirValue::Int { int_kind: IntKind::U32, bits: 0 },
            fuel: 200,
            expected_clean_batch: true,
        }];
        let out = session
            .run_batch("#![no_std]\npub fn f0() -> u32 { 7 }\n", &cases)
            .expect("compile with pinned linker");
        assert_eq!(
            out["c0"],
            ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 7 } }
        );
        assert_eq!(fs::read_to_string(&args_log).unwrap().trim(), real_gcc.to_string_lossy());
        assert_eq!(fs::read_to_string(&rustc_ld_log).unwrap().trim(), expected_staged_lib);
        assert_eq!(fs::read_to_string(&bin_ld_log).unwrap().trim(), expected_staged_lib);
        let logged_path: Vec<PathBuf> =
            env::split_paths(fs::read_to_string(&path_log).unwrap().trim()).collect();
        assert!(!logged_path.contains(&evil_dir));

        // Store-contained sysroot skips non-store ambient PATH entries while
        // pinning a store-contained linker and store toolchain dirs.
        let store_sysroot = fake_store.join("1111-store-sysroot");
        let store_cc_pkg = fake_store.join("2222-gcc-wrapper");
        let store_binutils = fake_store.join("3333-binutils");
        for d in [
            store_sysroot.join("bin"),
            store_sysroot.join("lib"),
            store_cc_pkg.join("bin"),
            store_binutils.join("bin"),
        ] {
            fs::create_dir_all(d).unwrap();
        }
        let store_gcc = store_cc_pkg.join("bin/gcc");
        fs::write(&store_gcc, "#!/bin/sh\nexit 0\n").unwrap();
        fs::set_permissions(&store_gcc, fs::Permissions::from_mode(0o755)).unwrap();
        symlink(&store_gcc, store_cc_pkg.join("bin").join(LINKER_BIN_NAME)).unwrap();
        let store_rustc = store_sysroot.join("bin/rustc");
        fs::write(
            &store_rustc,
            format!(
                "#!/bin/sh\nset -eu\n\
                 print_kind=\"\"\n\
                 while [ \"$#\" -gt 0 ]; do\n\
                   case \"$1\" in\n\
                     --sysroot|-C) shift ;;\n\
                     --print) shift; print_kind=\"${{1:-}}\" ;;\n\
                   esac\n\
                   shift\n\
                 done\n\
                 if [ \"$print_kind\" = \"sysroot\" ]; then printf '%s\\n' '{}'; exit 0; fi\n\
                 if [ \"$print_kind\" = \"cfg\" ]; then printf 'target_pointer_width=\"64\"\\n'; exit 0; fi\n",
                store_sysroot.display(),
            ),
        )
        .unwrap();
        fs::set_permissions(&store_rustc, fs::Permissions::from_mode(0o755)).unwrap();
        let store_ambient = env::join_paths([
            evil_dir.as_path(),
            store_binutils.join("bin").as_path(),
            store_cc_pkg.join("bin").as_path(),
        ])
        .unwrap();
        let store_session = RustcSession::prepare_with_config(
            &store_sysroot,
            &fake_store,
            &[],
            &[],
            &child_dirs,
            Some(store_ambient.as_os_str()),
        )
        .expect("prepare store sysroot session");
        assert_eq!(store_session.linker, store_gcc);
        assert_eq!(store_session.ld_library_path, store_sysroot.join("lib").to_string_lossy());
        let store_path_dirs: Vec<PathBuf> = env::split_paths(&store_session.child_path).collect();
        assert!(!store_path_dirs.contains(&evil_dir));
        assert!(store_path_dirs.contains(&store_binutils.join("bin")));
        assert!(store_path_dirs.contains(&store_cc_pkg.join("bin")));
    }

    #[cfg(unix)]
    #[test]
    fn linker_validator_rejects_escape_symlinks_hardlinks_and_symlinked_dirs() {
        use std::os::unix::fs::{PermissionsExt, symlink};

        let tmp = tempfile::tempdir().expect("tempdir");
        let base = fs::canonicalize(tmp.path()).expect("canonicalize tempdir");
        let caller_cwd = base.clone();
        let fake_store = base.join("nix-store");
        let trusted_dir = base.join("trusted-usr-bin");
        let alt_dir = base.join("trusted-alternatives");
        let outside = base.join("outside");
        for d in [&fake_store, &trusted_dir, &alt_dir, &outside] {
            fs::create_dir_all(d).unwrap();
        }
        let evil = outside.join("evil-cc");
        fs::write(&evil, "#!/bin/sh\nexit 0\n").unwrap();
        fs::set_permissions(&evil, fs::Permissions::from_mode(0o755)).unwrap();

        // 1. Trusted `cc` symlink escaping directly outside trusted dirs.
        let cc_link = trusted_dir.join(LINKER_BIN_NAME);
        symlink(&evil, &cc_link).unwrap();
        let err = validate_trusted_system_linker(
            &[trusted_dir.as_path()],
            &[alt_dir.as_path()],
            &caller_cwd,
        )
        .unwrap_err();
        assert!(err.contains("escaped trusted"), "{err}");
        fs::remove_file(&cc_link).unwrap();

        // 2. Trusted `cc -> alternatives/cc -> outside/evil` multi-hop escape.
        let alt_cc = alt_dir.join(LINKER_BIN_NAME);
        symlink(&evil, &alt_cc).unwrap();
        symlink(&alt_cc, &cc_link).unwrap();
        let err = validate_trusted_system_linker(
            &[trusted_dir.as_path()],
            &[alt_dir.as_path()],
            &caller_cwd,
        )
        .unwrap_err();
        assert!(err.contains("escaped trusted"), "{err}");
        fs::remove_file(&cc_link).unwrap();
        fs::remove_file(&alt_cc).unwrap();

        // 3. Hardlinked `cc` (`nlink > 1`) is rejected fail-closed.
        fs::hard_link(&evil, &cc_link).unwrap();
        let err = validate_trusted_system_linker(
            &[trusted_dir.as_path()],
            &[alt_dir.as_path()],
            &caller_cwd,
        )
        .unwrap_err();
        assert!(err.contains("hardlink"), "{err}");
        fs::remove_file(&cc_link).unwrap();

        // 4. Symlinked trusted directory is rejected fail-closed.
        let sym_trusted = base.join("sym-trusted");
        symlink(&outside, &sym_trusted).unwrap();
        symlink(&evil, outside.join(LINKER_BIN_NAME)).unwrap();
        let err = validate_trusted_system_linker(
            &[sym_trusted.as_path()],
            &[alt_dir.as_path()],
            &caller_cwd,
        )
        .unwrap_err();
        assert!(err.contains("symlink"), "{err}");

        // 5. Store-contained linker escaping store or hardlinked is rejected.
        let store_pkg = fake_store.join("aaaa-bad-gcc");
        fs::create_dir_all(store_pkg.join("bin")).unwrap();
        let store_cc = store_pkg.join("bin").join(LINKER_BIN_NAME);
        symlink(&evil, &store_cc).unwrap();
        let path_var = env::join_paths([store_pkg.join("bin")]).unwrap();
        let err = validate_store_linker_from_path(
            &fake_store,
            &fake_store,
            Some(path_var.as_os_str()),
            &caller_cwd,
        )
        .unwrap_err();
        assert!(err.contains("escaped store"), "{err}");
        fs::remove_file(&store_cc).unwrap();

        fs::hard_link(&evil, &store_cc).unwrap();
        let err = validate_store_linker_from_path(
            &fake_store,
            &fake_store,
            Some(path_var.as_os_str()),
            &caller_cwd,
        )
        .unwrap_err();
        assert!(err.contains("hardlink"), "{err}");

        // Non-store symlink pointing into store resolves canonical entry;
        // non-store symlink pointing outside store is ignored/rejected.
        let good_pkg = fake_store.join("bbbb-good-gcc");
        fs::create_dir_all(good_pkg.join("bin")).unwrap();
        let good_cc = good_pkg.join("bin").join(LINKER_BIN_NAME);
        fs::write(&good_cc, "#!/bin/sh\nexit 0\n").unwrap();
        fs::set_permissions(&good_cc, fs::Permissions::from_mode(0o755)).unwrap();
        let nix_wrap = base.join("opt-nix-profile");
        symlink(&good_pkg, &nix_wrap).unwrap();
        let canon_wrap_dir =
            validated_store_aware_dir(&nix_wrap, &fake_store, &caller_cwd, "wrapped store dir")
                .expect("wrapper symlink into store must succeed");
        assert_eq!(canon_wrap_dir, good_pkg);
        let canon_wrap_cc = validated_store_aware_executable(
            &nix_wrap.join("bin").join(LINKER_BIN_NAME),
            &fake_store,
            &caller_cwd,
            "wrapped store bin",
        )
        .expect("wrapped store executable must succeed");
        assert_eq!(canon_wrap_cc, good_cc);

        let outside_wrap = base.join("opt-bad-profile");
        symlink(&outside, &outside_wrap).unwrap();
        assert!(
            validated_store_aware_dir(&outside_wrap, &fake_store, &caller_cwd, "outside wrap")
                .is_err(),
            "wrapper symlink outside store must still fail closed"
        );
    }

    #[cfg(unix)]
    #[test]
    fn prepare_rejects_linked_sysroot_lib_artifacts_and_invalid_wrapper_sysroots() {
        use std::os::unix::fs::{PermissionsExt, symlink};

        let tmp = tempfile::tempdir().expect("tempdir");
        let base = fs::canonicalize(tmp.path()).expect("canon tempdir");
        let fake_store = base.join("nix-store");
        let trusted_bin = base.join("trusted-usr-bin");
        let outside = base.join("outside");
        for d in [&fake_store, &trusted_bin, &outside] {
            fs::create_dir_all(d).unwrap();
        }
        let real_cc = trusted_bin.join(LINKER_BIN_NAME);
        fs::write(&real_cc, "#!/bin/sh\nexit 0\n").unwrap();
        fs::set_permissions(&real_cc, fs::Permissions::from_mode(0o755)).unwrap();
        let evil_rlib = outside.join("libstd.rlib");
        fs::write(&evil_rlib, b"tampered-rlib").unwrap();
        let marker = base.join("rustc_invoked.marker");
        let child_dirs = [trusted_bin.as_path()];

        let make_rustc = |bin_path: &Path, body: &str| {
            fs::write(bin_path, body).unwrap();
            fs::set_permissions(bin_path, fs::Permissions::from_mode(0o755)).unwrap();
        };
        let unwrapped_body = format!(
            "#!/bin/sh\ntouch '{}'\nprintf 'target_pointer_width=\"64\"\\n'\n",
            marker.display()
        );

        // 1. Symlinked artifact inside `lib/` fails closed before `rustc`.
        let sym_lib_sys = base.join("sym-lib-artifact-sys");
        fs::create_dir_all(sym_lib_sys.join("bin")).unwrap();
        fs::create_dir_all(sym_lib_sys.join("lib/rustlib/x86_64-unknown-linux-gnu/lib")).unwrap();
        make_rustc(&sym_lib_sys.join("bin/rustc"), &unwrapped_body);
        symlink(
            &evil_rlib,
            sym_lib_sys.join("lib/rustlib/x86_64-unknown-linux-gnu/lib/libstd.rlib"),
        )
        .unwrap();
        let err = RustcSession::prepare_with_config(
            &sym_lib_sys,
            &fake_store,
            &[trusted_bin.as_path()],
            &[],
            &child_dirs,
            None,
        )
        .unwrap_err();
        assert!(err.contains("symlink"), "{err}");
        assert!(!marker.exists());

        // 1b. Relative escaping symlink (`../..`) and directory symlink inside
        //     `lib/` fail closed, while intra-`lib/` relative file symlinks
        //     matching `pack_omnibus_archive.sh` (`../../../libLLVM.so`) are
        //     materialized into a private, read-only, symlink-free sysroot.
        let bundle_sys = base.join("bundled-omnibus-sys");
        fs::create_dir_all(bundle_sys.join("bin")).unwrap();
        fs::create_dir_all(bundle_sys.join("lib/rustlib/x86_64-unknown-linux-gnu/lib")).unwrap();
        make_rustc(&bundle_sys.join("bin/rustc"), &unwrapped_body);
        fs::write(bundle_sys.join("lib/libLLVM-test.so"), b"llvm-so").unwrap();
        symlink(
            "../../../libLLVM-test.so",
            bundle_sys.join("lib/rustlib/x86_64-unknown-linux-gnu/lib/libLLVM-test.so"),
        )
        .unwrap();
        let staged_bundle =
            prepare_sysroot_binary(&bundle_sys, "bin/rustc", &fake_store, "Leg 0 rustc binary")
                .expect("relative intra-lib deduplication symlink must materialize cleanly");
        assert!(staged_bundle._staging.is_some());
        let staged_llvm =
            staged_bundle.sysroot.join("lib/rustlib/x86_64-unknown-linux-gnu/lib/libLLVM-test.so");
        let staged_llvm_meta = fs::symlink_metadata(&staged_llvm).unwrap();
        assert!(!staged_llvm_meta.file_type().is_symlink());
        assert_eq!(hardlink_count(&staged_llvm_meta), 1);
        assert!(staged_llvm_meta.permissions().readonly());
        assert!(fs::metadata(staged_llvm.parent().unwrap()).unwrap().permissions().readonly());
        assert_eq!(fs::read(&staged_llvm).unwrap(), b"llvm-so");
        drop(staged_bundle);

        // 1c. Ordinary single-link non-store sysroots (both with `lib/` and
        //     without `lib/`) and `prepare_toolchain_library_path` must ALSO
        //     materialize into private, read-only directories isolated from
        //     concurrent source writes or renames.
        let plain_sys = base.join("plain-non-store-sys");
        fs::create_dir_all(plain_sys.join("bin")).unwrap();
        fs::create_dir_all(plain_sys.join("lib")).unwrap();
        make_rustc(&plain_sys.join("bin/rustc"), &unwrapped_body);
        fs::write(plain_sys.join("lib/libplain.so"), b"plain-so-v1").unwrap();
        let staged_plain =
            prepare_sysroot_binary(&plain_sys, "bin/rustc", &fake_store, "Leg 0 rustc binary")
                .expect("ordinary non-store sysroot must materialize immutably");
        assert!(staged_plain._staging.is_some());
        assert_ne!(staged_plain.sysroot, plain_sys);
        assert_ne!(staged_plain.binary, plain_sys.join("bin/rustc"));
        assert_ne!(staged_plain.ld_library_path, plain_sys.join("lib").display().to_string());
        let staged_plain_bin_meta = fs::symlink_metadata(&staged_plain.binary).unwrap();
        let staged_plain_lib = PathBuf::from(&staged_plain.ld_library_path).join("libplain.so");
        let staged_plain_lib_meta = fs::symlink_metadata(&staged_plain_lib).unwrap();
        assert!(!staged_plain_bin_meta.file_type().is_symlink());
        assert_eq!(hardlink_count(&staged_plain_bin_meta), 1);
        assert!(staged_plain_bin_meta.permissions().readonly());
        assert!(staged_plain_lib_meta.permissions().readonly());
        // Mutating original writable binaries/libs must not affect staged view.
        fs::rename(plain_sys.join("bin/rustc"), plain_sys.join("bin/rustc.old")).unwrap();
        make_rustc(&plain_sys.join("bin/rustc"), "#!/bin/sh\necho EVIL\n");
        fs::write(plain_sys.join("lib/libplain.so"), b"evil-so-v2").unwrap();
        assert_eq!(fs::read(&staged_plain.binary).unwrap(), unwrapped_body.as_bytes());
        assert_eq!(fs::read(&staged_plain_lib).unwrap(), b"plain-so-v1");
        drop(staged_plain);

        let no_lib_sys = base.join("plain-non-store-no-lib-sys");
        fs::create_dir_all(no_lib_sys.join("bin")).unwrap();
        make_rustc(&no_lib_sys.join("bin/rustc"), &unwrapped_body);
        let staged_no_lib =
            prepare_sysroot_binary(&no_lib_sys, "bin/rustc", &fake_store, "Leg 0 rustc binary")
                .expect("non-store sysroot without lib/ must materialize bin/");
        assert!(staged_no_lib._staging.is_some());
        assert_ne!(staged_no_lib.sysroot, no_lib_sys);
        assert!(staged_no_lib.ld_library_path.is_empty());
        assert!(fs::symlink_metadata(&staged_no_lib.binary).unwrap().permissions().readonly());
        drop(staged_no_lib);

        let staged_plain_lib_only =
            prepare_toolchain_library_path(&plain_sys, &fake_store, &base, false)
                .expect("ordinary non-store lib/ must materialize into immutable LD_LIBRARY_PATH");
        assert!(staged_plain_lib_only._staging.is_some());
        assert_ne!(
            staged_plain_lib_only.ld_library_path,
            plain_sys.join("lib").display().to_string()
        );
        let isolated_so = PathBuf::from(&staged_plain_lib_only.ld_library_path).join("libplain.so");
        assert!(fs::symlink_metadata(&isolated_so).unwrap().permissions().readonly());
        fs::write(plain_sys.join("lib/libplain.so"), b"evil-so-v3").unwrap();
        assert_eq!(fs::read(&isolated_so).unwrap(), b"evil-so-v2");
        drop(staged_plain_lib_only);

        // `prepare_toolchain_library_path(..., true)` must likewise allow
        // confined intra-`lib/` relative deduplication symlinks while staging
        // immutable `LD_LIBRARY_PATH` and rejecting escaping links.
        let staged_tc_lib = prepare_toolchain_library_path(&bundle_sys, &fake_store, &base, true)
            .expect("omnibus deduplication symlinks must prepare immutable LD_LIBRARY_PATH");
        let staged_top_so = PathBuf::from(&staged_tc_lib.ld_library_path).join("libLLVM-test.so");
        let staged_top_meta = fs::symlink_metadata(&staged_top_so).unwrap();
        assert!(!staged_top_meta.file_type().is_symlink());
        assert_eq!(hardlink_count(&staged_top_meta), 1);
        assert_eq!(fs::read(&staged_top_so).unwrap(), b"llvm-so");
        drop(staged_tc_lib);

        let rel_esc_link = bundle_sys.join("lib/rustlib/x86_64-unknown-linux-gnu/lib/libesc.rlib");
        symlink("../../../../outside/libstd.rlib", &rel_esc_link).unwrap();
        let err_rel_esc =
            prepare_sysroot_binary(&bundle_sys, "bin/rustc", &fake_store, "Leg 0 rustc binary")
                .unwrap_err();
        assert!(err_rel_esc.contains("escaped"), "{err_rel_esc}");
        let err_lib_esc =
            prepare_toolchain_library_path(&bundle_sys, &fake_store, &base, true).unwrap_err();
        assert!(err_lib_esc.contains("escaped"), "{err_lib_esc}");
        fs::remove_file(&rel_esc_link).unwrap();

        let dir_link = bundle_sys.join("lib/rustlib/dirsym");
        symlink("x86_64-unknown-linux-gnu", &dir_link).unwrap();
        let err_dir_link =
            prepare_sysroot_binary(&bundle_sys, "bin/rustc", &fake_store, "Leg 0 rustc binary")
                .unwrap_err();
        assert!(err_dir_link.contains("regular file"), "{err_dir_link}");
        fs::remove_file(&dir_link).unwrap();

        // 2. Hardlinked artifact inside `lib/` (`nlink > 1`) fails closed.
        let hard_lib_sys = base.join("hard-lib-artifact-sys");
        fs::create_dir_all(hard_lib_sys.join("bin")).unwrap();
        fs::create_dir_all(hard_lib_sys.join("lib/rustlib/x86_64-unknown-linux-gnu/lib")).unwrap();
        make_rustc(&hard_lib_sys.join("bin/rustc"), &unwrapped_body);
        fs::hard_link(
            &evil_rlib,
            hard_lib_sys.join("lib/rustlib/x86_64-unknown-linux-gnu/lib/libstd.rlib"),
        )
        .unwrap();
        let err = RustcSession::prepare_with_config(
            &hard_lib_sys,
            &fake_store,
            &[trusted_bin.as_path()],
            &[],
            &child_dirs,
            None,
        )
        .unwrap_err();
        assert!(err.contains("hardlink"), "{err}");
        assert!(!marker.exists());

        // 3. Store `symlinkJoin` `lib/` allows store-contained symlinks and
        //    rejects escaping symlinks or hardlinks inside `lib/`.
        let store_target = fake_store.join("1111-real-rustlib");
        fs::create_dir_all(store_target.join("lib/rustlib/lib")).unwrap();
        fs::write(store_target.join("lib/rustlib/lib/libcore.rlib"), b"core").unwrap();
        let store_sys = fake_store.join("2222-join-sys");
        fs::create_dir_all(store_sys.join("bin")).unwrap();
        fs::create_dir_all(store_sys.join("lib/rustlib/lib")).unwrap();
        make_rustc(&store_sys.join("bin/rustc"), &unwrapped_body);
        symlink(
            store_target.join("lib/rustlib/lib/libcore.rlib"),
            store_sys.join("lib/rustlib/lib/libcore.rlib"),
        )
        .unwrap();
        let prepared_store_sys =
            prepare_sysroot_binary(&store_sys, "bin/rustc", &fake_store, "Leg 0 rustc binary")
                .expect("store-contained lib artifact symlink must succeed");
        assert_eq!(prepared_store_sys.sysroot, store_sys);
        assert!(prepared_store_sys._staging.is_none());

        let direct_store_sys = fake_store.join("3333-direct-store-sys");
        fs::create_dir_all(direct_store_sys.join("bin")).unwrap();
        fs::create_dir_all(direct_store_sys.join("lib")).unwrap();
        make_rustc(&direct_store_sys.join("bin/rustc"), &unwrapped_body);
        fs::write(direct_store_sys.join("lib/libstd.so"), b"store-so").unwrap();
        let prepared_direct_store = prepare_sysroot_binary(
            &direct_store_sys,
            "bin/rustc",
            &fake_store,
            "Leg 0 rustc binary",
        )
        .expect("direct symlink-free store sysroot must validate without staging");
        assert_eq!(prepared_direct_store.sysroot, direct_store_sys);
        assert!(prepared_direct_store._staging.is_none());

        symlink(&evil_rlib, store_sys.join("lib/rustlib/lib/libstd.rlib")).unwrap();
        let err =
            prepare_sysroot_binary(&store_sys, "bin/rustc", &fake_store, "Leg 0 rustc binary")
                .unwrap_err();
        assert!(err.contains("escaped store"), "{err}");
        fs::remove_file(store_sys.join("lib/rustlib/lib/libstd.rlib")).unwrap();

        fs::hard_link(&evil_rlib, store_sys.join("lib/rustlib/lib/libstd.rlib")).unwrap();
        let err =
            prepare_sysroot_binary(&store_sys, "bin/rustc", &fake_store, "Leg 0 rustc binary")
                .unwrap_err();
        assert!(err.contains("hardlink"), "{err}");

        // 4. Wrapper `bin/rustc` reporting an unvalidated or linked sysroot via
        //    `--print sysroot` must fail before `pass_sysroot_arg=false`.
        let wrap_sys = base.join("wrapper-bad-reported-sysroot");
        fs::create_dir_all(wrap_sys.join("bin")).unwrap();
        fs::create_dir_all(wrap_sys.join("lib")).unwrap();
        let reported_real = base.join("reported-real");
        fs::create_dir_all(reported_real.join("lib")).unwrap();
        let reported_sym = base.join("reported-sym");
        symlink(&reported_real, &reported_sym).unwrap();
        let write_wrapper = |target: &Path| {
            make_rustc(
                &wrap_sys.join("bin/rustc"),
                &format!(
                    "#!/bin/sh\nset -eu\nprint_kind=\"\"\n\
                     while [ \"$#\" -gt 0 ]; do\n\
                       case \"$1\" in\n\
                         --sysroot) exit 1 ;;\n\
                         --print) shift; print_kind=\"${{1:-}}\" ;;\n\
                       esac\n\
                       shift\n\
                     done\n\
                     if [ \"$print_kind\" = \"sysroot\" ]; then printf '%s\\n' '{}'; exit 0; fi\n\
                     exit 0\n",
                    target.display()
                ),
            );
        };

        write_wrapper(&reported_sym);
        let err = RustcSession::prepare_with_config(
            &wrap_sys,
            &fake_store,
            &[trusted_bin.as_path()],
            &[],
            &child_dirs,
            None,
        )
        .unwrap_err();
        assert!(err.contains("symlink"), "{err}");

        symlink(&evil_rlib, reported_real.join("lib/libstd.rlib")).unwrap();
        write_wrapper(&reported_real);
        let err = RustcSession::prepare_with_config(
            &wrap_sys,
            &fake_store,
            &[trusted_bin.as_path()],
            &[],
            &child_dirs,
            None,
        )
        .unwrap_err();
        assert!(err.contains("symlink"), "{err}");
        fs::remove_file(reported_real.join("lib/libstd.rlib")).unwrap();

        fs::hard_link(&evil_rlib, reported_real.join("lib/libstd.rlib")).unwrap();
        let err = RustcSession::prepare_with_config(
            &wrap_sys,
            &fake_store,
            &[trusted_bin.as_path()],
            &[],
            &child_dirs,
            None,
        )
        .unwrap_err();
        assert!(err.contains("hardlink"), "{err}");
    }

    #[cfg(unix)]
    #[test]
    fn prepare_lean_library_path_materializes_top_level_links_and_rejects_escapes() {
        use std::os::unix::fs::symlink;

        let tmp = tempfile::tempdir().expect("tempdir");
        let base = fs::canonicalize(tmp.path()).expect("canon tempdir");
        let fake_store = base.join("nix-store");
        let outside = base.join("outside");
        fs::create_dir_all(&fake_store).unwrap();
        fs::create_dir_all(&outside).unwrap();
        let evil_so = outside.join("libevil.so");
        fs::write(&evil_so, b"evil-so").unwrap();

        let lean_tc = base.join("lean-tc");
        fs::create_dir_all(lean_tc.join("bin")).unwrap();
        fs::create_dir_all(lean_tc.join("lib/lean")).unwrap();
        let lean_bin = lean_tc.join("bin/lean");
        fs::write(&lean_bin, b"#!/bin/sh\n").unwrap();
        fs::write(lean_tc.join("lib/libleanshared.so.1"), b"lean-so").unwrap();
        symlink("libleanshared.so.1", lean_tc.join("lib/libleanshared.so")).unwrap();
        fs::write(lean_tc.join("lib/lean/Init.olean"), b"init").unwrap();

        let prepared = prepare_lean_library_path(&lean_bin, &fake_store, &base)
            .expect("relative intra-lib .so symlink must materialize into private immutable lib");
        assert!(prepared._staging.is_some());
        assert_ne!(prepared.lean_bin, lean_bin);
        assert_ne!(prepared.bin_dir, lean_tc.join("bin"));
        assert_eq!(prepared.lean_bin.parent(), Some(prepared.bin_dir.as_path()));
        let staged_lean_meta = fs::symlink_metadata(&prepared.lean_bin).unwrap();
        assert!(!staged_lean_meta.file_type().is_symlink());
        assert_eq!(hardlink_count(&staged_lean_meta), 1);
        assert!(staged_lean_meta.permissions().readonly());
        assert!(fs::metadata(&prepared.bin_dir).unwrap().permissions().readonly());
        assert_eq!(fs::read(&prepared.lean_bin).unwrap(), b"#!/bin/sh\n");
        let joined: Vec<PathBuf> = env::split_paths(&prepared.ld_library_path).collect();
        assert_eq!(joined.len(), 2);
        assert_ne!(joined[0], lean_tc.join("lib/lean"));
        assert_ne!(joined[1], lean_tc.join("lib"));
        assert_eq!(prepared.lib_lean_dir.as_deref(), Some(joined[0].as_path()));
        let staged_olean = joined[0].join("Init.olean");
        let staged_olean_meta = fs::symlink_metadata(&staged_olean).unwrap();
        assert!(!staged_olean_meta.file_type().is_symlink());
        assert_eq!(hardlink_count(&staged_olean_meta), 1);
        assert!(staged_olean_meta.permissions().readonly());
        assert!(fs::metadata(&joined[0]).unwrap().permissions().readonly());
        assert_eq!(fs::read(&staged_olean).unwrap(), b"init");
        let staged_so = joined[1].join("libleanshared.so");
        let staged_meta = fs::symlink_metadata(&staged_so).unwrap();
        assert!(!staged_meta.file_type().is_symlink());
        assert_eq!(hardlink_count(&staged_meta), 1);
        assert!(staged_meta.permissions().readonly());
        assert!(fs::metadata(&joined[1]).unwrap().permissions().readonly());
        assert_eq!(fs::read(&staged_so).unwrap(), b"lean-so");
        // Mutating source binary or files after prepare leaves staged copies
        // untouched.
        fs::write(&lean_bin, b"#!/bin/sh\necho tampered\n").unwrap();
        fs::write(lean_tc.join("lib/lean/Init.olean"), b"tampered-init").unwrap();
        fs::write(lean_tc.join("lib/libleanshared.so.1"), b"tampered-so").unwrap();
        assert_eq!(fs::read(&prepared.lean_bin).unwrap(), b"#!/bin/sh\n");
        assert_eq!(fs::read(&staged_olean).unwrap(), b"init");
        assert_eq!(fs::read(&staged_so).unwrap(), b"lean-so");
        fs::write(&lean_bin, b"#!/bin/sh\n").unwrap();
        drop(prepared);

        // 0b. Symlink inside a subdirectory of `lib/` fails closed.
        fs::create_dir_all(lean_tc.join("lib/sub")).unwrap();
        let sub_sym = lean_tc.join("lib/sub/libsub.so");
        symlink("../libleanshared.so.1", &sub_sym).unwrap();
        let err_sub = prepare_lean_library_path(&lean_bin, &fake_store, &base).unwrap_err();
        assert!(err_sub.contains("subdirectory"), "{err_sub}");
        fs::remove_dir_all(lean_tc.join("lib/sub")).unwrap();

        // 1. Escaping symlink inside `lib/` fails closed.
        let esc_so = lean_tc.join("lib/libescape.so");
        symlink("../../outside/libevil.so", &esc_so).unwrap();
        let err_esc = prepare_lean_library_path(&lean_bin, &fake_store, &base).unwrap_err();
        assert!(err_esc.contains("escaped"), "{err_esc}");
        fs::remove_file(&esc_so).unwrap();

        // 2. Hardlinked regular file inside `lib/` fails closed.
        let hard_so = lean_tc.join("lib/libhard.so");
        fs::hard_link(&evil_so, &hard_so).unwrap();
        let err_hard = prepare_lean_library_path(&lean_bin, &fake_store, &base).unwrap_err();
        assert!(err_hard.contains("hardlink"), "{err_hard}");
        fs::remove_file(&hard_so).unwrap();

        // 3. Symlink or hardlink inside `lib/lean/` fails closed.
        let sym_olean = lean_tc.join("lib/lean/Evil.olean");
        symlink("../../outside/libevil.so", &sym_olean).unwrap();
        let err_olean_sym = prepare_lean_library_path(&lean_bin, &fake_store, &base).unwrap_err();
        assert!(err_olean_sym.contains("symlink"), "{err_olean_sym}");
        fs::remove_file(&sym_olean).unwrap();

        fs::hard_link(&evil_so, &sym_olean).unwrap();
        let err_olean_hard = prepare_lean_library_path(&lean_bin, &fake_store, &base).unwrap_err();
        assert!(err_olean_hard.contains("hardlink"), "{err_olean_hard}");
        fs::remove_file(&sym_olean).unwrap();

        // 4. Nix store Lean `lib/` permits store-contained symlinks and rejects
        //    outside-store escapes without materializing.
        let store_real = fake_store.join("1111-lean-real");
        fs::create_dir_all(store_real.join("lib")).unwrap();
        fs::write(store_real.join("lib/libstore.so"), b"store").unwrap();
        let store_join = fake_store.join("2222-lean-join");
        fs::create_dir_all(store_join.join("bin")).unwrap();
        fs::create_dir_all(store_join.join("lib/lean")).unwrap();
        let store_lean = store_join.join("bin/lean");
        fs::write(&store_lean, b"#!/bin/sh\n").unwrap();
        symlink(store_real.join("lib/libstore.so"), store_join.join("lib/libstore.so")).unwrap();
        let store_prepared = prepare_lean_library_path(&store_lean, &fake_store, &base)
            .expect("store-contained Lean lib symlinks must succeed");
        assert!(store_prepared._staging.is_none());
        assert_eq!(store_prepared.lean_bin, store_lean);

        symlink(&evil_so, store_join.join("lib/libesc.so")).unwrap();
        let err_store_esc = prepare_lean_library_path(&store_lean, &fake_store, &base).unwrap_err();
        assert!(err_store_esc.contains("escaped store"), "{err_store_esc}");
    }

    #[cfg(unix)]
    #[test]
    fn prepare_lean_runtime_library_path_omits_compiler_packages_and_tracks_source() {
        let tmp = tempfile::tempdir().expect("tempdir");
        let base = fs::canonicalize(tmp.path()).expect("canon tempdir");
        let fake_store = base.join("nix-store");
        fs::create_dir_all(&fake_store).unwrap();

        let lean_tc = base.join("lean-tc");
        fs::create_dir_all(lean_tc.join("bin")).unwrap();
        for dir in ["Init", "Std", "Lean", "Lake", "LeanIR"] {
            fs::create_dir_all(lean_tc.join("lib/lean").join(dir)).unwrap();
        }
        let lean_bin = lean_tc.join("bin/lean");
        fs::write(&lean_bin, b"#!/bin/sh\n").unwrap();
        fs::write(lean_tc.join("lib/libleanshared.so"), b"so").unwrap();
        fs::write(lean_tc.join("lib/libstatic.a"), b"archive").unwrap();
        fs::write(lean_tc.join("lib/lean/Init.olean"), b"init").unwrap();
        fs::write(lean_tc.join("lib/lean/Init/Core.olean"), b"init-core").unwrap();
        fs::write(lean_tc.join("lib/lean/Std.olean"), b"std").unwrap();
        fs::write(lean_tc.join("lib/lean/Std/Data.olean"), b"std-data").unwrap();
        fs::write(lean_tc.join("lib/lean/Lean.olean"), b"lean").unwrap();
        fs::write(lean_tc.join("lib/lean/Lean/Meta.olean"), b"lean-meta").unwrap();
        fs::write(lean_tc.join("lib/lean/libLean.a"), b"lean-a").unwrap();

        let prepared =
            prepare_lean_runtime_library_path_in(&lean_bin, &fake_store, &base, Some(&base))
                .expect("runtime Lean staging");
        let staged_lib_lean = prepared.lib_lean_dir.as_ref().expect("staged lib/lean");
        assert_eq!(
            prepared.source_lib_lean_dir.as_deref(),
            Some(lean_tc.join("lib/lean").as_path())
        );
        assert!(staged_lib_lean.join("Init.olean").is_file());
        assert!(staged_lib_lean.join("Init/Core.olean").is_file());
        for omitted in ["Std", "Lean", "Lake", "LeanIR", "Std.olean", "Lean.olean", "libLean.a"] {
            assert!(!staged_lib_lean.join(omitted).exists(), "unexpected staged {omitted}");
        }
        assert!(staged_lib_lean.parent().unwrap().join("libleanshared.so").is_file());
        assert!(!staged_lib_lean.parent().unwrap().join("libstatic.a").exists());
        assert!(!is_lean_compiler_or_static_entry(&[], OsStr::new("Init"), true));
        assert!(!is_lean_compiler_or_static_entry(&[], OsStr::new("Init.olean"), false));
        for pkg in LEAN_RUNTIME_OMITTED_SYSROOT_PACKAGES {
            assert!(is_lean_compiler_or_static_entry(&[], OsStr::new(pkg), true));
            assert!(is_lean_compiler_or_static_entry(
                &[],
                OsStr::new(&format!("{pkg}.olean")),
                false
            ));
        }
    }

    #[cfg(unix)]
    #[test]
    fn rustc_session_anchors_relative_tmpdir_and_rejects_unsafe_tmpdir() {
        use std::os::unix::fs::{PermissionsExt as _, symlink};

        let tmp = tempfile::tempdir().expect("tempdir");
        let base = fs::canonicalize(tmp.path()).expect("canon tempdir");
        let caller_cwd = base.join("caller");
        let rel_tmp = caller_cwd.join("tmp");
        let trusted_bin = base.join("trusted-bin");
        let fake_store = base.join("nix-store");
        let sysroot = base.join("sysroot");
        for d in [&rel_tmp, &trusted_bin, &fake_store, &sysroot.join("bin"), &sysroot.join("lib")] {
            fs::create_dir_all(d).unwrap();
        }

        let cc_bin = trusted_bin.join(LINKER_BIN_NAME);
        fs::write(&cc_bin, "#!/bin/sh\nexit 0\n").unwrap();
        fs::set_permissions(&cc_bin, fs::Permissions::from_mode(0o755)).unwrap();

        let probe_tmps = base.join("probe-tmps.txt");
        let compile_log = base.join("compile-tmp.txt");
        let compile_sentinel = base.join("compile-sentinel");
        let rustc_stub = sysroot.join("bin/rustc");
        fs::write(
            &rustc_stub,
            format!(
                "#!/bin/sh\nset -eu\n\
                 print_kind=\"\"\nout_bin=\"\"\n\
                 while [ \"$#\" -gt 0 ]; do\n\
                   case \"$1\" in\n\
                     --sysroot|-C) shift ;;\n\
                     --print) shift; print_kind=\"${{1:-}}\" ;;\n\
                     -o) shift; out_bin=\"${{1:-}}\" ;;\n\
                   esac\n\
                   shift\n\
                 done\n\
                 [ -n \"${{TMPDIR:-}}\" ] && [ -d \"$TMPDIR\" ]\n\
                 if [ -n \"$print_kind\" ]; then\n\
                   printf '%s\\n' \"$TMPDIR\" >> '{}'\n\
                   if [ \"$print_kind\" = \"sysroot\" ]; then printf '%s\\n' '{}'; exit 0; fi\n\
                   if [ \"$print_kind\" = \"cfg\" ]; then printf 'target_pointer_width=\"64\"\\n'; exit 0; fi\n\
                 fi\n\
                 touch '{}'\n\
                 printf 'TMP=%s\\nPWD=%s\\n' \"$TMPDIR\" \"$(pwd -P)\" > '{}'\n\
                 printf '#!/bin/sh\\nprintf \"ANNEAL_RUSTC_RUN:c0:f0\\\\nANNEAL_RUSTC_CASE:c0:INT:u32:7\\\\n\"\\n' > \"$out_bin\"\n\
                 chmod +x \"$out_bin\"\n",
                probe_tmps.display(),
                sysroot.display(),
                compile_sentinel.display(),
                compile_log.display(),
            ),
        )
        .unwrap();
        fs::set_permissions(&rustc_stub, fs::Permissions::from_mode(0o755)).unwrap();

        let mut child_dirs: Vec<&Path> = vec![trusted_bin.as_path()];
        for sys_cand in [Path::new("/usr/bin"), Path::new("/bin")] {
            if fs::symlink_metadata(sys_cand).is_ok() {
                child_dirs.push(sys_cand);
            }
        }
        let session = RustcSession::prepare_with_config_at(
            &sysroot,
            &fake_store,
            &[trusted_bin.as_path()],
            &[],
            &child_dirs,
            Some(trusted_bin.as_os_str()),
            &caller_cwd,
            Some(OsStr::new("tmp")),
        )
        .expect("relative existing TMPDIR must anchor cleanly against caller_cwd");
        assert_eq!(session.validated_tmpdir.as_deref(), Some(rel_tmp.as_path()));
        let recorded_probes = fs::read_to_string(&probe_tmps).unwrap();
        assert_eq!(
            recorded_probes.lines().collect::<Vec<_>>(),
            vec![rel_tmp.display().to_string(), rel_tmp.display().to_string()]
        );

        let case = FuzzExecCase {
            case_id: "c0".to_owned(),
            fn_name: "f0".to_owned(),
            args: vec![],
            ret_shape: MirValue::Int { int_kind: IntKind::U32, bits: 0 },
            fuel: 100,
            expected_clean_batch: true,
        };
        let out = session
            .run_batch("#![no_std]\npub fn f0() -> u32 { 7 }\n", &[case])
            .expect("compile inside anchored private workdir must succeed");
        assert_eq!(
            out["c0"],
            ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 7 } }
        );
        let compile_text = fs::read_to_string(&compile_log).unwrap();
        assert!(compile_text.contains(&format!("TMP={}\n", rel_tmp.display())), "{compile_text}");
        let compile_pwd = compile_text
            .lines()
            .find_map(|l| l.strip_prefix("PWD="))
            .expect("compile PWD recorded");
        assert!(Path::new(compile_pwd).starts_with(&rel_tmp), "{compile_pwd}");

        // Traversal, symlink, or missing TMPDIR must fail BEFORE any probe.
        let _ = fs::remove_file(&probe_tmps);
        let _ = fs::remove_file(&compile_sentinel);
        let sym_tmp = caller_cwd.join("sym-tmp");
        symlink(&rel_tmp, &sym_tmp).unwrap();
        for bad_tmp in [OsStr::new("../outside"), sym_tmp.as_os_str(), OsStr::new("missing-tmp")] {
            let err = RustcSession::prepare_with_config_at(
                &sysroot,
                &fake_store,
                &[trusted_bin.as_path()],
                &[],
                &child_dirs,
                Some(trusted_bin.as_os_str()),
                &caller_cwd,
                Some(bad_tmp),
            )
            .unwrap_err();
            assert!(err.contains("TMPDIR"), "bad TMPDIR {:?} -> {err}", bad_tmp);
            assert!(!probe_tmps.exists(), "probe must not run for bad TMPDIR {:?}", bad_tmp);
            assert!(!compile_sentinel.exists());
        }
    }

    #[cfg(unix)]
    #[test]
    fn staging_resists_parent_dir_rename_and_multi_hop_lib_symlinks() {
        use std::os::unix::fs::{PermissionsExt, symlink};

        let tmp = tempfile::tempdir().expect("tempdir");
        let base = fs::canonicalize(tmp.path()).expect("canon tempdir");
        let rename_root = base.join("rename-parent");
        let tmp_sub = rename_root.join("active");
        let moved_sub = rename_root.join("moved");
        let trusted_bin = base.join("trusted-usr-bin");
        let fake_store = base.join("nix-store");
        let tc = base.join("tc");
        let outside = base.join("outside");
        for d in [&tmp_sub, &trusted_bin, &fake_store, &tc.join("bin"), &tc.join("lib"), &outside] {
            fs::create_dir_all(d).unwrap();
        }

        // 2-hop relative confined symlink (`libc++abi.so -> .so.1 -> .so.1.0`)
        // matching real elan Lean `lib/` layouts must stage cleanly, while
        // a 2-hop escaping symlink must fail closed.
        fs::write(tc.join("lib/libc++abi.so.1.0"), b"real-cxxabi").unwrap();
        symlink("libc++abi.so.1.0", tc.join("lib/libc++abi.so.1")).unwrap();
        symlink("libc++abi.so.1", tc.join("lib/libc++abi.so")).unwrap();
        let staged_libs = prepare_toolchain_library_path(&tc, &fake_store, &base, true)
            .expect("2-hop confined relative symlink inside lib/ must materialize cleanly");
        assert_eq!(
            fs::read(PathBuf::from(&staged_libs.ld_library_path).join("libc++abi.so")).unwrap(),
            b"real-cxxabi"
        );
        drop(staged_libs);

        fs::write(outside.join("evil.so"), b"evil").unwrap();
        symlink("../../outside/evil.so", tc.join("lib/hop2.so")).unwrap();
        symlink("hop2.so", tc.join("lib/hop1.so")).unwrap();
        let err_2hop = prepare_toolchain_library_path(&tc, &fake_store, &base, true).unwrap_err();
        assert!(err_2hop.contains("escaped"), "{err_2hop}");
        fs::remove_file(tc.join("lib/hop1.so")).unwrap();
        fs::remove_file(tc.join("lib/hop2.so")).unwrap();

        let cc_bin = trusted_bin.join(LINKER_BIN_NAME);
        fs::write(&cc_bin, "#!/bin/sh\nexit 0\n").unwrap();
        fs::set_permissions(&cc_bin, fs::Permissions::from_mode(0o755)).unwrap();
        let rustc_stub = tc.join("bin/rustc");
        fs::write(
            &rustc_stub,
            format!(
                "#!/bin/sh\nset -eu\n\
                 print_kind=\"\"\nout_bin=\"\"\n\
                 while [ \"$#\" -gt 0 ]; do\n\
                   case \"$1\" in\n\
                     --sysroot|-C) shift ;;\n\
                     --print) shift; print_kind=\"${{1:-}}\" ;;\n\
                     -o) shift; out_bin=\"${{1:-}}\" ;;\n\
                   esac\n\
                   shift\n\
                 done\n\
                 if [ \"$print_kind\" = \"sysroot\" ]; then printf '%s\\n' '{}'; exit 0; fi\n\
                 if [ \"$print_kind\" = \"cfg\" ]; then printf 'target_pointer_width=\"64\"\\n'; exit 0; fi\n\
                 printf '#!/bin/sh\\nprintf \"ANNEAL_RUSTC_RUN:c0:f0\\\\nANNEAL_RUSTC_CASE:c0:INT:u32:7\\\\n\"\\n' > \"$out_bin\"\n\
                 chmod +x \"$out_bin\"\n",
                tc.display()
            ),
        )
        .unwrap();
        fs::set_permissions(&rustc_stub, fs::Permissions::from_mode(0o755)).unwrap();

        let mut child_dirs: Vec<&Path> = vec![trusted_bin.as_path()];
        for sys_cand in [Path::new("/usr/bin"), Path::new("/bin")] {
            if fs::symlink_metadata(sys_cand).is_ok() {
                child_dirs.push(sys_cand);
            }
        }
        let session = RustcSession::prepare_with_config_at(
            &tc,
            &fake_store,
            &[trusted_bin.as_path()],
            &[],
            &child_dirs,
            Some(trusted_bin.as_os_str()),
            &base,
            Some(tmp_sub.as_os_str()),
        )
        .expect("prepare sysroot inside renameable parent");
        assert!(session.rustc_bin.starts_with("/proc/self/fd/"));
        let disk_root = session._sysroot_staging.as_ref().unwrap().root().to_path_buf();
        assert!(disk_root.starts_with(&tmp_sub));

        // Simulate renaming a writable staging parent directory and planting a
        // trojan `bin/rustc` at the vacated path. `TMPDIR` points at a clean
        // directory while `rustc_bin` executes via held descriptor.
        fs::rename(&tmp_sub, &moved_sub).unwrap();
        fs::create_dir_all(disk_root.join("bin")).unwrap();
        fs::write(disk_root.join("bin/rustc"), "#!/bin/sh\necho TROJAN >&2\nexit 99\n").unwrap();
        fs::set_permissions(disk_root.join("bin/rustc"), fs::Permissions::from_mode(0o755))
            .unwrap();
        fs::create_dir_all(&tmp_sub).unwrap();
        let case = FuzzExecCase {
            case_id: "c0".to_owned(),
            fn_name: "f0".to_owned(),
            args: vec![],
            ret_shape: MirValue::Int { int_kind: IntKind::U32, bits: 0 },
            fuel: 100,
            expected_clean_batch: true,
        };
        let out = session
            .run_batch("#![no_std]\npub fn f0() -> u32 { 7 }\n", &[case])
            .expect("pinned staging fd must resist parent rename + path hijack");
        assert_eq!(
            out["c0"],
            ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 7 } }
        );

        // Restore original parent before `session` drops for `TempDir` cleanup.
        fs::remove_dir_all(&tmp_sub).unwrap();
        fs::rename(&moved_sub, &tmp_sub).unwrap();
    }

    #[cfg(unix)]
    #[test]
    fn compiled_harness_execution_resists_workdir_rename_and_leaf_hijack() {
        use std::os::unix::fs::PermissionsExt as _;

        let tmp = tempfile::tempdir().expect("tempdir");
        let base = fs::canonicalize(tmp.path()).expect("canon tempdir");
        let rename_root = base.join("rename-parent");
        let tmp_sub = rename_root.join("active");
        let moved_sub = rename_root.join("moved");
        let trusted_bin = base.join("trusted-usr-bin");
        let fake_store = base.join("nix-store");
        let tc = base.join("tc");
        for d in [&tmp_sub, &trusted_bin, &fake_store, &tc.join("bin"), &tc.join("lib")] {
            fs::create_dir_all(d).unwrap();
        }

        let cc_bin = trusted_bin.join(LINKER_BIN_NAME);
        fs::write(&cc_bin, "#!/bin/sh\nexit 0\n").unwrap();
        fs::set_permissions(&cc_bin, fs::Permissions::from_mode(0o755)).unwrap();
        let rustc_stub = tc.join("bin/rustc");
        fs::write(
            &rustc_stub,
            format!(
                "#!/bin/sh\nset -eu\n\
                 print_kind=\"\"\nout_bin=\"\"\n\
                 while [ \"$#\" -gt 0 ]; do\n\
                   case \"$1\" in\n\
                     --sysroot|-C) shift ;;\n\
                     --print) shift; print_kind=\"${{1:-}}\" ;;\n\
                     -o) shift; out_bin=\"${{1:-}}\" ;;\n\
                   esac\n\
                   shift\n\
                 done\n\
                 if [ \"$print_kind\" = \"sysroot\" ]; then printf '%s\\n' '{}'; exit 0; fi\n\
                 if [ \"$print_kind\" = \"cfg\" ]; then printf 'target_pointer_width=\"64\"\\n'; exit 0; fi\n\
                 cat <<'HARNESS' > \"$out_bin\"\n#!/bin/sh\ncase \"${{1:-}}\" in __BATCH__) sel=\"${{2:-}}\";; *) sel=\"${{1:-}}\";; esac\nprintf 'ANNEAL_RUSTC_RUN:%s:f0\\nANNEAL_RUSTC_CASE:%s:INT:u32:7\\n' \"$sel\" \"$sel\"\nHARNESS\n\
                 chmod +x \"$out_bin\"\n",
                tc.display()
            ),
        )
        .unwrap();
        fs::set_permissions(&rustc_stub, fs::Permissions::from_mode(0o755)).unwrap();

        let mut child_dirs: Vec<&Path> = vec![trusted_bin.as_path()];
        for sys_cand in [Path::new("/usr/bin"), Path::new("/bin")] {
            if fs::symlink_metadata(sys_cand).is_ok() {
                child_dirs.push(sys_cand);
            }
        }
        let session = RustcSession::prepare_with_config_at(
            &tc,
            &fake_store,
            &[trusted_bin.as_path()],
            &[],
            &child_dirs,
            Some(trusted_bin.as_os_str()),
            &base,
            Some(tmp_sub.as_os_str()),
        )
        .expect("prepare session in renameable TMPDIR");

        let cases = vec![
            FuzzExecCase {
                case_id: "c_batch".to_owned(),
                fn_name: "f0".to_owned(),
                args: vec![],
                ret_shape: MirValue::Int { int_kind: IntKind::U32, bits: 0 },
                fuel: 100,
                expected_clean_batch: true,
            },
            FuzzExecCase {
                case_id: "c_iso".to_owned(),
                fn_name: "f0".to_owned(),
                args: vec![],
                ret_shape: MirValue::Int { int_kind: IntKind::U32, bits: 0 },
                fuel: 100,
                expected_clean_batch: false,
            },
        ];

        let mut captured_stage_root = None;
        let out = session
            .run_batch_with_evidence_hook_impl(
                "#![no_std]\npub fn f0() -> u32 { 7 }\n",
                None,
                &cases,
                None,
                |old_work, harness| {
                    assert!(harness.exec_path.starts_with("/proc/self/fd/"));
                    let disk_stage = harness._staging.root().to_path_buf();
                    assert!(disk_stage.starts_with(&tmp_sub));
                    assert!(!old_work.exists());
                    captured_stage_root = Some(disk_stage.clone());

                    // Simulate concurrent parent-dir rename and leaf trojan
                    // planting between compilation and both batch/isolated
                    // harness execution.
                    fs::rename(&tmp_sub, &moved_sub).unwrap();
                    fs::create_dir_all(&disk_stage).unwrap();
                    fs::create_dir_all(old_work).unwrap();
                    for trojan in
                        [disk_stage.join("rustc_harness_bin"), old_work.join("rustc_harness_bin")]
                    {
                        fs::write(
                            &trojan,
                            "#!/bin/sh\nprintf 'ANNEAL_RUSTC_RUN:c_batch:f0\\n\
                             ANNEAL_RUSTC_CASE:c_batch:INT:u32:999\\n'\n",
                        )
                        .unwrap();
                        fs::set_permissions(&trojan, fs::Permissions::from_mode(0o755)).unwrap();
                    }
                },
            )
            .expect("pinned compiled harness must resist parent rename + leaf hijack");
        assert_eq!(
            out["c_batch"].0,
            ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 7 } }
        );
        assert_eq!(
            out["c_iso"].0,
            ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 7 } }
        );

        let _ = captured_stage_root;
        fs::remove_dir_all(&tmp_sub).unwrap();
        fs::rename(&moved_sub, &tmp_sub).unwrap();
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn immutable_staging_build_and_pin_resists_parent_rename_during_populate_and_freeze() {
        use std::os::unix::fs::{MetadataExt as _, PermissionsExt as _, symlink};

        let tmp = tempfile::tempdir().expect("tempdir");
        let base = fs::canonicalize(tmp.path()).expect("canon root");
        let parent_dir = base.join("stage-parent");
        let moved_parent = base.join("moved-parent");
        fs::create_dir_all(&parent_dir).unwrap();

        let temp = tempfile::Builder::new().prefix("pin-race-").tempdir_in(&parent_dir).unwrap();
        let temp_disk = fs::canonicalize(temp.path()).unwrap();
        let (_, staging) =
            ImmutableStagingDir::build_and_pin(temp, "pin race test", |priv_root, pinned_root| {
                assert!(pinned_root.starts_with("/proc/self/fd/"));
                // Attacker renames the staging parent out from under
                // writable `parent_dir` and installs an adversarial symlink
                // directory at the old path while populate runs.
                fs::rename(&parent_dir, &moved_parent).unwrap();
                fs::create_dir_all(priv_root).unwrap();
                symlink(base.join("nonexistent-target"), priv_root.join("evil-sym")).unwrap();

                let dst = pinned_root.join("payload.txt");
                fs::write(&dst, b"genuine-pinned").unwrap();
                fs::set_permissions(&dst, fs::Permissions::from_mode(0o444)).unwrap();
                Ok(())
            })
            .expect("build_and_pin must stay bound to original pinned inode across rename");

        let pinned_payload = staging.pin_path(Path::new("payload.txt"));
        assert_eq!(fs::read(&pinned_payload).unwrap(), b"genuine-pinned");
        assert!(!staging.pin_path(Path::new("evil-sym")).exists());
        let root_meta = fs::metadata(staging.pin_path(Path::new(""))).unwrap();
        assert_eq!(root_meta.permissions().mode() & 0o777, 0o555);
        assert_eq!(fs::symlink_metadata(&pinned_payload).unwrap().nlink(), 1);
        assert_ne!(temp_disk, moved_parent);

        drop(staging);
        fs::remove_dir_all(&parent_dir).unwrap();
        restore_dir_write_perms_top_down(&moved_parent);
        fs::remove_dir_all(&moved_parent).unwrap();
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn open_pinned_proc_dir_fd_and_child_open_reject_parent_traversal() {
        use std::os::fd::{AsFd as _, AsRawFd as _};

        let tmp = tempfile::tempdir().expect("tempdir");
        let base = fs::canonicalize(tmp.path()).expect("canon root");
        let inner = base.join("inner");
        let sub = inner.join("sub");
        let outside = base.join("outside");
        for d in [&sub, &outside] {
            fs::create_dir_all(d).unwrap();
        }
        let inner_fd = open_dir_handle_no_symlinks(&inner, None, "inner").unwrap();
        let raw = inner_fd.as_raw_fd();

        for bad_seg in [c"", c".", c"..", c"sub/x"] {
            let err =
                open_child_dir_nofollow(inner_fd.as_fd(), bad_seg, None, "child").unwrap_err();
            assert!(err.contains("traverse"), "{bad_seg:?} -> {err}");
        }

        let valid_sub = open_pinned_proc_dir_fd(
            Path::new(&format!("/proc/self/fd/{raw}/sub")),
            "valid proc sub",
        )
        .expect("direct child dir via /proc/self/fd must open");
        drop(valid_sub);

        let esc_path = PathBuf::from(format!("/proc/self/fd/{raw}/../outside"));
        let err = open_pinned_proc_dir_fd(&esc_path, "escaped proc path").unwrap_err();
        assert!(err.contains("traversal"), "{err}");
    }

    #[cfg(unix)]
    #[test]
    fn confined_subdir_multihop_symlink_via_root_resolves_against_root_fd() {
        use std::os::{fd::AsFd as _, unix::fs::symlink};

        let tmp = tempfile::tempdir().expect("tempdir");
        let base = fs::canonicalize(tmp.path()).expect("canon root");
        let lib = base.join("lib");
        let dst = base.join("dst");
        let lib_neg = base.join("lib-neg");
        for d in [lib.join("sub"), lib.join("sub2"), lib.join("sub3"), lib_neg.join("sub")] {
            fs::create_dir_all(d).unwrap();
        }

        // Hop 1 returns to `lib/` (`sub/a.so -> ../b.so`, `b.so -> real.so`)
        // while a decoy `sub/b.so` exists inside `cur_fd`.
        fs::write(lib.join("real.so"), b"genuine-from-root").unwrap();
        fs::write(lib.join("sub/b.so"), b"wrong-subdir-decoy").unwrap();
        symlink("real.so", lib.join("b.so")).unwrap();
        symlink("../b.so", lib.join("sub/a.so")).unwrap();

        // Hop 2 from `lib/` enters another subdir (`sub2/c.so -> ../d.so`,
        // `d.so -> sub3/e.so`).
        fs::write(lib.join("sub3/e.so"), b"hop-via-root-to-sub3").unwrap();
        symlink("sub3/e.so", lib.join("d.so")).unwrap();
        symlink("../d.so", lib.join("sub2/c.so")).unwrap();

        assert!(
            inspect_sysroot_lib_dir_tree(&lib, true, "confined multihop lib")
                .expect("subdir symlink hopping back to root must pass inspection")
        );
        let root_fd = open_dir_handle_no_symlinks(&lib, None, "confined multihop lib").unwrap();
        copy_validated_subtree_from_fd_with_filter(
            root_fd.as_fd(),
            &lib,
            &dst,
            Some(&lib),
            false,
            "confined multihop lib",
            |_, _, _| false,
        )
        .expect("copy_validated_subtree must read hop 2 from root_fd");
        assert_eq!(fs::read(dst.join("sub/a.so")).unwrap(), b"genuine-from-root");
        assert_eq!(fs::read(dst.join("sub2/c.so")).unwrap(), b"hop-via-root-to-sub3");

        // Ensure hop 2 returning to `root_fd` never falls back to `cur_fd`:
        // `only_in_sub.so` exists only in `sub/`, not in `lib_neg/`.
        fs::write(lib_neg.join("sub/only_in_sub.so"), b"decoy").unwrap();
        symlink("only_in_sub.so", lib_neg.join("root_hop.so")).unwrap();
        symlink("../root_hop.so", lib_neg.join("sub/bad.so")).unwrap();
        let neg_err = inspect_sysroot_lib_dir_tree(&lib_neg, true, "neg lib").unwrap_err();
        assert!(!neg_err.is_empty());
    }
}
