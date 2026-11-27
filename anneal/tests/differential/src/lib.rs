// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Stage-1 multi-leg MIR differential oracle comparing Miri (`rustc` / Tree
//! Borrows), captured MIR evaluated by Lean `Anneal.MirTotal.StepCore`
//! (paired with kernel `Anneal.MirWp` adequacy theorems for budget-fitting
//! single-block pass/UB cases: `<= 9` MIR statements, no 128-bit scalars,
//! `<= 16` WP fuel), and optional `anneal-mir-eval`.
//!
//! Evaluation split:
//! - Runtime `#eval` on all cases uses `evalMirFuelBy (mirTyBeqAt 8)`.
//! - Lean kernel proof obligations (`wpProg_of_evalMirFuelTotal` /
//!   `wpFaultProg_of_evalMirFuelTotal`) check `evalMirFuelTotal` (`MirTy.beq`)
//!   inside Lean's kernel type checker for budget-fitting single-block `pass`
//!   and `ub` cases (`kernel_checked_pass_count`, `kernel_checked_ub_count`).
//!
//! Workspace test prerequisites:
//! - Running `cargo test -p anneal-differential-tests` executes the live suite
//!   against a Rust sysroot providing `rustc`, `cargo`, `miri`, and vendored
//!   `rust-src` sources (`<sysroot>/lib/rustlib/src/rust/library/vendor`),
//!   alongside Lean 4.34.1 and `anneal-rustc-capture`.
//!
//! Stage 0 Alpha — Not Yet Audited: empirical differential testing raises
//! confidence and surfaces divergences rather than proving universal soundness.
//!
//! Threat model: runs assume a trusted single-tenant host and UID domain (OS,
//! container, and CI-runner boundaries such as `bwrap` own defense against a
//! concurrent same-UID adversary mutating `TMPDIR`, Cargo caches, or scratch
//! build/capture directories mid-run).

pub mod corpus;
pub mod fuzz;
pub mod r#gen;
pub mod lean_runner;
pub mod mir_eval_runner;
pub mod miri_runner;
pub mod mutants;
pub mod rustc_runner;
pub mod shrink;
pub mod verdict;

use std::{
    collections::BTreeMap,
    env,
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
    sync::Arc,
    thread,
};

use anneal_testkit::{ToolchainEnv, ToolchainMode};
use serde::{Deserialize, Serialize};

#[cfg(test)]
use crate::lean_runner::sha256_file_hex;
use crate::{
    corpus::{DEFAULT_CORPUS_MANIFEST_REL, LitmusCase, load_manifest},
    lean_runner::{CapturedModule, LeanCaseResult, LeanSession},
    miri_runner::MiriSession,
    mutants::MutantSuiteReport,
    verdict::{Expectation, ObservedOutcome, SuiteMetrics, Verdict, evaluate_case},
};

/// Stage-0 Alpha honesty notice preserved in serialized reports.
pub const ALPHA_NOTICE: &str = "Stage 0 Alpha — Not Yet Audited (this is alpha software!)";

/// Configuration governing a full differential oracle invocation.
#[derive(Clone, Debug)]
pub struct RunOptions {
    pub manifest_path: PathBuf,
    pub capture_bin: Option<PathBuf>,
    pub mir_eval_bin: Option<PathBuf>,
    pub self_check_oracle: bool,
    pub cache_root: Option<PathBuf>,
}

/// Per-case comparison record across all active legs.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CaseReport {
    pub id: String,
    pub source: String,
    pub function: String,
    pub category: String,
    pub expected: Expectation,
    pub allow_conservative_unsupported: bool,
    pub kernel_checked: bool,
    pub miri: ObservedOutcome,
    pub lean: ObservedOutcome,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub mir_eval: Option<ObservedOutcome>,
    pub verdict: Verdict,
}

/// Full JSON-serializable report produced by `run_differential_suite`.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct DifferentialReport {
    pub schema: String,
    pub alpha_notice: String,
    pub mir_dialect: String,
    pub manifest_path: String,
    pub capture_bin_source: String,
    pub capture_bin_sha256: String,
    pub prebuilt_overlay: String,
    pub legs: Vec<String>,
    pub metrics: SuiteMetrics,
    pub red_flags_passed: usize,
    pub red_flag_error: Option<String>,
    pub cases: Vec<CaseReport>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub mutant_check: Option<MutantSuiteReport>,
}

impl DifferentialReport {
    /// Whether every case verdict passed, all red flags cleared, and any
    /// requested mutant self-check killed 100% of mutants and synthetic probes.
    pub fn is_passing(&self) -> bool {
        if self.red_flag_error.is_some() {
            return false;
        }
        if self.cases.iter().any(|c| !c.verdict.is_ok()) {
            return false;
        }
        if let Some(m) = &self.mutant_check
            && (m.total_mutants == 0
                || m.killed_mutants != m.total_mutants
                || m.synthetic_lean_probes.is_empty()
                || m.synthetic_lean_probes.iter().any(|p| !p.passed))
        {
            return false;
        }
        true
    }
}

/// Locate the `anneal/` workspace root from either the manifest path or crate
/// location.
pub fn find_anneal_root(manifest_path: &Path) -> Result<PathBuf, String> {
    if let Ok(canon) = std::fs::canonicalize(manifest_path) {
        let mut cur = canon.parent();
        while let Some(dir) = cur {
            if dir.join("Cargo.toml").is_file() && dir.join("trusted/lean/lean-toolchain").is_file()
            {
                return Ok(dir.to_path_buf());
            }
            cur = dir.parent();
        }
    }
    ToolchainEnv::repo_root_from_manifest(Path::new(env!("CARGO_MANIFEST_DIR")))
}

/// Resolve the default Stage-1 Profile v1 corpus manifest path.
pub fn default_manifest_path() -> Result<PathBuf, String> {
    let root = ToolchainEnv::repo_root_from_manifest(Path::new(env!("CARGO_MANIFEST_DIR")))?;
    Ok(root.join(DEFAULT_CORPUS_MANIFEST_REL))
}

/// Resolve the differential cache root, honoring explicit `--cache-root`,
/// `ANNEAL_DIFF_CACHE_DIR`, `CARGO_TARGET_DIR`, or a writable in-checkout
/// `target/anneal-diff-cache`, and falling back to a private temporary
/// directory when the checkout is read-only.
pub fn resolve_cache_root(
    anneal_root: &Path,
    explicit: Option<&Path>,
) -> Result<(PathBuf, Option<tempfile::TempDir>), String> {
    let caller_cwd =
        env::current_dir().map_err(|e| format!("resolve current working directory: {e}"))?;
    let validated_tmpdir = crate::mir_eval_runner::validate_optional_existing_dir_env(
        env::var_os("TMPDIR").as_deref(),
        &caller_cwd,
        "TMPDIR",
    )?;
    let in_repo_target = anneal_root.join("target");
    let in_repo_target_clean_dir = fs::symlink_metadata(&in_repo_target)
        .is_ok_and(|m| !m.file_type().is_symlink() && m.is_dir());
    let (raw_cache, label) = if let Some(p) = explicit {
        (p.to_path_buf(), "--cache-root")
    } else if let Some(cd) = env::var_os("ANNEAL_DIFF_CACHE_DIR").filter(|v| !v.is_empty()) {
        (PathBuf::from(cd), "ANNEAL_DIFF_CACHE_DIR")
    } else if let Some(td) = env::var_os("CARGO_TARGET_DIR").filter(|v| !v.is_empty()) {
        (PathBuf::from(td).join("anneal-diff-cache"), "CARGO_TARGET_DIR")
    } else if in_repo_target_clean_dir && tempfile::tempfile_in(&in_repo_target).is_ok() {
        (in_repo_target.join("anneal-diff-cache"), "anneal target cache")
    } else {
        let private_tmp = crate::mir_eval_runner::build_temp_dir(
            "anneal-diff-cache-",
            validated_tmpdir.as_deref(),
        )?;
        let path =
            crate::mir_eval_runner::validate_dir_path_no_symlinks(private_tmp.path(), &caller_cwd)?;
        return Ok((path, Some(private_tmp)));
    };
    let abs_cache = crate::mir_eval_runner::validate_dir_or_uncreated_path_no_symlinks(
        &raw_cache,
        &caller_cwd,
        label,
    )?;
    Ok((abs_cache, None))
}

fn format_report_manifest_path(anneal_root: &Path, manifest_path: &Path) -> String {
    if let Ok(rel) = manifest_path.strip_prefix(anneal_root) {
        return rel.to_string_lossy().into_owned();
    }
    manifest_path
        .file_name()
        .map(|n| n.to_string_lossy().into_owned())
        .unwrap_or_else(|| "manifest.toml".to_owned())
}

/// Resolved suite toolchain with an immutable staged copy of
/// `anneal-rustc-capture` whose SHA-256 matches the exact staged executable.
#[derive(Debug)]
pub struct PreparedSuiteToolchain {
    pub tools: ToolchainEnv,
    pub capture_bin_source: String,
    pub capture_bin_sha256: String,
    pub(crate) _capture_staging: Option<Arc<crate::rustc_runner::ImmutableStagingDir>>,
}

fn stage_capture_bin_with_store(
    raw_cap: &Path,
    store_prefix: &Path,
    caller_cwd: &Path,
    tmp_parent: Option<&Path>,
) -> Result<(PathBuf, PathBuf, String, Option<Arc<crate::rustc_runner::ImmutableStagingDir>>), String>
{
    if let Some(res) = crate::rustc_runner::try_validate_store_contained_executable(
        raw_cap,
        store_prefix,
        caller_cwd,
        "capture binary",
    ) {
        let canon = res?;
        let (staged, sha, staging) = crate::mir_eval_runner::stage_verified_single_link_executable(
            &canon,
            "anneal-rustc-capture",
            tmp_parent,
            false,
        )?;
        return Ok((canon, staged, sha, staging));
    }
    let opened = crate::rustc_runner::open_verified_executable_via_dirfd(
        raw_cap,
        caller_cwd,
        true,
        "capture binary",
    )?;
    let canon_orig = opened.canon_path.clone();
    let (staged, sha, staging) =
        crate::mir_eval_runner::stage_opened_single_link_executable_with_hook(
            opened,
            "anneal-rustc-capture",
            tmp_parent,
            false,
            || {},
        )?;
    Ok((canon_orig, staged, sha, staging))
}

/// Resolve toolchain coordinates and capture binary provenance without
/// allowing ambient `ANNEAL_CAPTURE` / `ANNEAL_MVP_CAPTURE` to override an
/// explicit `capture_bin`. Rejects uncontained symlinks and hardlinks
/// (`nlink > 1`) before staging `anneal-rustc-capture` into a private immutable
/// directory and recording the SHA-256 of the copied executable.
pub fn resolve_toolchain_for_suite(
    explicit_capture_bin: Option<&Path>,
    get_env: impl Fn(&str) -> Option<OsString>,
) -> Result<PreparedSuiteToolchain, String> {
    resolve_toolchain_for_suite_with_store(
        explicit_capture_bin,
        Path::new(crate::rustc_runner::STORE_PREFIX),
        get_env,
    )
}

pub(crate) fn resolve_toolchain_for_suite_with_store(
    explicit_capture_bin: Option<&Path>,
    store_prefix: &Path,
    get_env: impl Fn(&str) -> Option<OsString>,
) -> Result<PreparedSuiteToolchain, String> {
    let non_empty_path = |key: &str| -> Option<PathBuf> {
        get_env(key).filter(|v| !v.is_empty()).map(PathBuf::from)
    };
    let caller_cwd =
        env::current_dir().map_err(|e| format!("resolve current working directory: {e}"))?;
    let validated_tmpdir = crate::mir_eval_runner::validate_optional_existing_dir_env(
        get_env("TMPDIR").as_deref(),
        &caller_cwd,
        "TMPDIR",
    )?;
    if let Some(raw_lean) =
        non_empty_path("ANNEAL_LEAN").or_else(|| non_empty_path("ANNEAL_MVP_LEAN"))
    {
        let _ = crate::rustc_runner::validated_store_aware_executable(
            &raw_lean,
            store_prefix,
            &caller_cwd,
            "ANNEAL_LEAN",
        )?;
    } else if let Some(inst_root) = non_empty_path("ANNEAL_TEST_INSTALL_ROOT") {
        let inst_lean = inst_root.join("lean/bin/lean");
        if fs::symlink_metadata(&inst_lean).is_ok() {
            let _ = crate::rustc_runner::validated_store_aware_executable(
                &inst_lean,
                store_prefix,
                &caller_cwd,
                "ANNEAL_TEST_INSTALL_ROOT lean",
            )?;
        }
    }

    if let Some(explicit) = explicit_capture_bin {
        let (_canon_orig, staged_cap, sha256, capture_staging) = stage_capture_bin_with_store(
            explicit,
            store_prefix,
            &caller_cwd,
            validated_tmpdir.as_deref(),
        )?;
        let mut tools = ToolchainEnv::resolve_with_env(
            ToolchainMode::WorkspaceBuild {
                cli_bin: None,
                capture_bin: Some(staged_cap.clone()),
                auditor_bin: None,
            },
            |key| {
                if matches!(key, "ANNEAL_CAPTURE" | "ANNEAL_MVP_CAPTURE") {
                    None
                } else {
                    get_env(key)
                }
            },
        )?;
        tools.capture = Some(
            capture_staging
                .as_ref()
                .map_or_else(|| staged_cap.clone(), |s| s.pin_path(&staged_cap)),
        );
        return Ok(PreparedSuiteToolchain {
            tools,
            capture_bin_source: "explicit".to_owned(),
            capture_bin_sha256: sha256,
            _capture_staging: capture_staging,
        });
    }

    let env_capture =
        non_empty_path("ANNEAL_CAPTURE").or_else(|| non_empty_path("ANNEAL_MVP_CAPTURE"));
    let mut pre_staged: Option<(
        PathBuf,
        String,
        Option<Arc<crate::rustc_runner::ImmutableStagingDir>>,
    )> = None;
    let capture_bin_source = if let Some(raw_cap) = env_capture {
        let (_canon_orig, staged, sha, staging) = stage_capture_bin_with_store(
            &raw_cap,
            store_prefix,
            &caller_cwd,
            validated_tmpdir.as_deref(),
        )?;
        pre_staged = Some((staged, sha, staging));
        "env_anneal_capture"
    } else {
        let sib_cap = if let Some(cli_raw) =
            non_empty_path("ANNEAL_CLI").or_else(|| non_empty_path("ANNEAL_MVP_CLI"))
        {
            let canon_cli = if let Some(res) =
                crate::rustc_runner::try_validate_store_contained_executable(
                    &cli_raw,
                    store_prefix,
                    &caller_cwd,
                    "ANNEAL_CLI",
                ) {
                res?
            } else {
                crate::mir_eval_runner::validate_file_path_no_symlinks(
                    &cli_raw,
                    &caller_cwd,
                    "ANNEAL_CLI",
                )?
            };
            ["anneal-rustc-capture", "anneal-rustc-capture-test-bin"]
                .into_iter()
                .map(|name| canon_cli.with_file_name(name))
                .find(|cand| {
                    fs::symlink_metadata(cand)
                        .is_ok_and(|m| m.is_file() || m.file_type().is_symlink())
                })
        } else {
            None
        };
        if let Some(sib_cap) = sib_cap {
            let (_canon_orig, staged, sha, staging) = stage_capture_bin_with_store(
                &sib_cap,
                store_prefix,
                &caller_cwd,
                validated_tmpdir.as_deref(),
            )?;
            pre_staged = Some((staged, sha, staging));
            "sibling_capture_bin"
        } else {
            if let Some(root) = non_empty_path("ANNEAL_TEST_INSTALL_ROOT") {
                let inst_cap = root.join("bin/anneal-rustc-capture");
                if fs::symlink_metadata(&inst_cap).is_ok() {
                    let (_canon_orig, staged, sha, staging) = stage_capture_bin_with_store(
                        &inst_cap,
                        store_prefix,
                        &caller_cwd,
                        validated_tmpdir.as_deref(),
                    )?;
                    pre_staged = Some((staged, sha, staging));
                }
            }
            "env_install_root"
        }
    };

    let has_pre_staged = pre_staged.is_some();
    let pre_staged_cap = pre_staged.as_ref().map(|(staged, _, _)| staged.clone());
    let mut tools = ToolchainEnv::resolve_with_env(
        ToolchainMode::WorkspaceBuild {
            cli_bin: None,
            capture_bin: pre_staged_cap,
            auditor_bin: None,
        },
        |key| {
            if has_pre_staged && matches!(key, "ANNEAL_CAPTURE" | "ANNEAL_MVP_CAPTURE") {
                None
            } else {
                get_env(key)
            }
        },
    )?;
    let (staged_cap, sha256, capture_staging) = if let Some((staged, sha, staging)) = pre_staged {
        (staged, sha, staging)
    } else {
        let resolved_capture = tools.capture.as_deref().ok_or_else(|| {
            "missing `anneal-rustc-capture` binary: pass `--capture-bin` or set `ANNEAL_CAPTURE`, `ANNEAL_CLI`, or `ANNEAL_TEST_INSTALL_ROOT`".to_owned()
        })?;
        let (_, staged, sha, staging) = stage_capture_bin_with_store(
            resolved_capture,
            store_prefix,
            &caller_cwd,
            validated_tmpdir.as_deref(),
        )?;
        (staged, sha, staging)
    };
    tools.capture = Some(
        capture_staging.as_ref().map_or_else(|| staged_cap.clone(), |s| s.pin_path(&staged_cap)),
    );
    Ok(PreparedSuiteToolchain {
        tools,
        capture_bin_source: capture_bin_source.to_owned(),
        capture_bin_sha256: sha256,
        _capture_staging: capture_staging,
    })
}

/// Execute all active legs against the manifest corpus and return the summary
/// report (caller inspects [`DifferentialReport::is_passing`]).
pub fn run_differential_suite(opts: &RunOptions) -> Result<DifferentialReport, String> {
    let loaded = load_manifest(&opts.manifest_path)?;
    let anneal_root = find_anneal_root(&loaded.manifest_path)?;
    let (cache_root, _cache_guard) = resolve_cache_root(&anneal_root, opts.cache_root.as_deref())?;
    let resolved_mir_eval = opts
        .mir_eval_bin
        .as_deref()
        .map(mir_eval_runner::stage_mir_eval_bin_no_links)
        .transpose()?;
    let prepared_tools =
        resolve_toolchain_for_suite(opts.capture_bin.as_deref(), |k| env::var_os(k))?;
    let tools = &prepared_tools.tools;
    let capture_bin_source = prepared_tools.capture_bin_source.clone();
    let capture_bin_sha256 = prepared_tools.capture_bin_sha256.clone();

    let caller_cwd =
        env::current_dir().map_err(|e| format!("resolve current working directory: {e}"))?;
    let ambient_tmpdir = env::var_os("TMPDIR");
    let validated_tmpdir = crate::mir_eval_runner::validate_optional_existing_dir_env(
        ambient_tmpdir.as_deref(),
        &caller_cwd,
        "TMPDIR",
    )?;
    let prepared_sys = crate::rustc_runner::prepare_sysroot_binary_in(
        &tools.sysroot,
        &format!("bin/rustc{}", env::consts::EXE_SUFFIX),
        Path::new(crate::rustc_runner::STORE_PREFIX),
        validated_tmpdir.as_deref(),
        "Suite rustc sysroot",
    )?;

    let miri_sys = prepared_sys.clone();
    let (miri_res, lean_res) = thread::scope(|scope| {
        let m = scope.spawn(|| MiriSession::prepare_from_sysroot(miri_sys, &cache_root));
        let l = scope.spawn(|| {
            LeanSession::prepare_from_sysroot(&anneal_root, tools, &cache_root, prepared_sys)
        });
        (
            m.join().unwrap_or_else(|_| Err("Miri prepare panicked".to_owned())),
            l.join().unwrap_or_else(|_| Err("Lean prepare panicked".to_owned())),
        )
    });
    let miri_session = miri_res?;
    let lean_session = lean_res?;

    let run_workspace = crate::mir_eval_runner::build_temp_dir(
        "anneal-diff-run-",
        lean_session.validated_tmpdir.as_deref(),
    )?;

    let miri_outcomes = miri_session.run_cases(&loaded.cases)?;

    // Group capture & Lean StepCore evaluation by fixture source file.
    let mut by_source: BTreeMap<PathBuf, Vec<&LitmusCase>> = BTreeMap::new();
    for case in &loaded.cases {
        by_source.entry(case.source_abs.clone()).or_default().push(case);
    }

    let mut captured_by_source: BTreeMap<PathBuf, CapturedModule> = BTreeMap::new();
    let mut lean_outcomes: BTreeMap<String, LeanCaseResult> = BTreeMap::new();
    for (idx, (source_abs, group_cases)) in by_source.iter().enumerate() {
        let group_dir = run_workspace.path().join(format!("group_{idx}"));
        std::fs::create_dir_all(&group_dir)
            .map_err(|e| format!("create {}: {e}", group_dir.display()))?;
        let crate_name = format!("diff_corpus_{idx}");
        let (cap_mod, outcomes) = lean_session.capture_and_evaluate_group(
            &group_dir,
            &crate_name,
            source_abs,
            group_cases,
        )?;
        captured_by_source.insert(source_abs.clone(), cap_mod);
        lean_outcomes.extend(outcomes);
    }

    let mut case_reports = Vec::with_capacity(loaded.cases.len());
    for case in &loaded.cases {
        let miri = miri_outcomes
            .get(&case.id)
            .cloned()
            .ok_or_else(|| format!("missing Miri outcome for case {:?}", case.id))?;
        let lean_res = lean_outcomes
            .get(&case.id)
            .cloned()
            .ok_or_else(|| format!("missing Lean outcome for case {:?}", case.id))?;
        let mir_eval = if let Some(eval_bin) = &resolved_mir_eval {
            let cap = captured_by_source
                .get(&case.source_abs)
                .ok_or_else(|| format!("missing capture module for {:?}", case.source_abs))?;
            match cap.body_ids_by_fn.get(&case.function) {
                Some(&body_id) => Some(mir_eval_runner::run_prepared_mir_eval_case(
                    eval_bin,
                    &cap.capture_json,
                    body_id,
                    case,
                )),
                None => Some(ObservedOutcome::ToolError {
                    detail: format!(
                        "missing captured body id for function {:?} in {}",
                        case.function,
                        cap.capture_json.display()
                    ),
                }),
            }
        } else {
            None
        };

        let verdict = evaluate_case(
            case.expected,
            case.expected_return.as_ref(),
            case.miri_ub_contains.as_deref(),
            case.expected_miri,
            &miri,
            &lean_res.outcome,
            mir_eval.as_ref(),
        );
        let allow_conservative_unsupported = case.expected == Expectation::UnsupportedControl;
        case_reports.push(CaseReport {
            id: case.id.clone(),
            source: case.source_rel.to_string_lossy().into_owned(),
            function: case.function.clone(),
            category: case.category.clone(),
            expected: case.expected,
            allow_conservative_unsupported,
            kernel_checked: lean_res.kernel_checked,
            miri,
            lean: lean_res.outcome,
            mir_eval,
            verdict,
        });
    }

    let metrics =
        SuiteMetrics::from_outcomes(case_reports.iter().map(|r| (&r.verdict, r.kernel_checked)));
    let (mut red_flags_passed, mut red_flag_error) = match metrics.check_red_flags() {
        Ok(n) => (n, None),
        Err(e) => (0, Some(e)),
    };
    if red_flag_error.is_none() {
        for case in &loaded.cases {
            if case.id == "cf_move_then_reinit" {
                let has_move_reinit = captured_by_source
                    .get(&case.source_abs)
                    .is_some_and(|cap| cap.move_reinit_fns.contains(&case.function));
                if !has_move_reinit {
                    red_flags_passed = 0;
                    red_flag_error = Some(format!(
                        "red flag: case {:?} ({}) did not emit Rvalue::Use(Operand::Move) + reinitialization on a non-ZST local in captured MIR",
                        case.id, case.function
                    ));
                    break;
                }
            }
        }
    }

    let mutant_check = if opts.self_check_oracle {
        Some(mutants::run_self_check_mutants(
            &lean_session,
            &captured_by_source,
            &loaded.cases,
            &miri_outcomes,
        )?)
    } else {
        None
    };

    let mut legs = vec![
        "miri".to_owned(),
        "lean_step_core_captured".to_owned(),
        "lean_wp_kernel_single_block".to_owned(),
    ];
    if opts.mir_eval_bin.is_some() {
        legs.push("anneal_mir_eval_captured".to_owned());
    }

    let report_manifest = format_report_manifest_path(&anneal_root, &loaded.manifest_path);
    let prebuilt_overlay = lean_session.prebuilt_overlay.clone();

    Ok(DifferentialReport {
        schema: "anneal-differential-run/v1".to_owned(),
        alpha_notice: ALPHA_NOTICE.to_owned(),
        mir_dialect: loaded.mir_dialect,
        manifest_path: report_manifest,
        capture_bin_source,
        capture_bin_sha256,
        prebuilt_overlay,
        legs,
        metrics,
        red_flags_passed,
        red_flag_error,
        cases: case_reports,
        mutant_check,
    })
}

#[cfg(test)]
mod tests {
    use anneal_testkit::toolchain::{default_lean_path, default_rust_sysroot};

    use super::*;
    use crate::verdict::{IntKind, MirValue};

    #[test]
    fn explicit_capture_bin_overrides_ambient_env_and_rejects_symlinks() {
        let lean_bin = default_lean_path().expect("resolve pinned lean");
        let sysroot = default_rust_sysroot().expect("resolve rust sysroot");

        let tmp = tempfile::tempdir().unwrap();
        let explicit_bin = tmp.path().join("explicit-capture");
        let env_bin = tmp.path().join("env-capture");
        let inst_root = tmp.path().join("install");
        fs::create_dir_all(inst_root.join("bin")).unwrap();
        let inst_bin = inst_root.join("bin/anneal-rustc-capture");
        fs::write(&explicit_bin, b"explicit-driver-bytes").unwrap();
        fs::write(&env_bin, b"ambient-env-driver-bytes").unwrap();
        fs::write(&inst_bin, b"installed-driver-bytes").unwrap();

        let expected_explicit_sha = sha256_file_hex(&explicit_bin).unwrap();
        let expected_env_sha = sha256_file_hex(&env_bin).unwrap();
        let expected_inst_sha = sha256_file_hex(&inst_bin).unwrap();

        let prepared_explicit = resolve_toolchain_for_suite(Some(&explicit_bin), |key| match key {
            "ANNEAL_CAPTURE" => Some(OsString::from("/tmp/nonexistent-sentinel")),
            "ANNEAL_MVP_CAPTURE" => Some(env_bin.as_os_str().to_os_string()),
            "ANNEAL_LEAN" => Some(lean_bin.as_os_str().to_os_string()),
            "ANNEAL_SYSROOT" => Some(sysroot.as_os_str().to_os_string()),
            _ => None,
        })
        .expect("explicit capture_bin must override ambient ANNEAL_CAPTURE");
        let staged_explicit =
            prepared_explicit.tools.capture.as_deref().expect("staged explicit capture path");
        assert_ne!(staged_explicit, fs::canonicalize(&explicit_bin).unwrap().as_path());
        assert_eq!(prepared_explicit.capture_bin_source, "explicit");
        assert_eq!(prepared_explicit.capture_bin_sha256, expected_explicit_sha);
        assert_ne!(prepared_explicit.capture_bin_sha256, expected_env_sha);

        // Mutating the original writable source after toolchain resolution must
        // never alter the immutable staged binary executed by Legs 1/2.
        fs::write(&explicit_bin, b"tampered-after-hash").unwrap();
        assert_eq!(fs::read(staged_explicit).unwrap(), b"explicit-driver-bytes");
        assert_eq!(sha256_file_hex(staged_explicit).unwrap(), prepared_explicit.capture_bin_sha256);
        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt as _;
            let st_meta = fs::symlink_metadata(staged_explicit).unwrap();
            assert!(!st_meta.file_type().is_symlink());
            assert_eq!(st_meta.nlink(), 1);
            assert!(st_meta.permissions().readonly());
            assert!(
                fs::metadata(staged_explicit.parent().unwrap()).unwrap().permissions().readonly()
            );
        }
        fs::write(&explicit_bin, b"explicit-driver-bytes").unwrap();

        let prepared_env = resolve_toolchain_for_suite(None, |key| match key {
            "ANNEAL_CAPTURE" => Some(env_bin.as_os_str().to_os_string()),
            "ANNEAL_TEST_INSTALL_ROOT" => Some(inst_root.as_os_str().to_os_string()),
            "ANNEAL_LEAN" => Some(lean_bin.as_os_str().to_os_string()),
            "ANNEAL_SYSROOT" => Some(sysroot.as_os_str().to_os_string()),
            _ => None,
        })
        .expect("env capture resolves when capture_bin is None");
        let staged_env = prepared_env.tools.capture.as_deref().unwrap();
        assert_ne!(staged_env, fs::canonicalize(&env_bin).unwrap().as_path());
        assert_eq!(prepared_env.capture_bin_source, "env_anneal_capture");
        assert_eq!(prepared_env.capture_bin_sha256, expected_env_sha);
        fs::write(&env_bin, b"mutated-env-capture").unwrap();
        assert_eq!(sha256_file_hex(staged_env).unwrap(), expected_env_sha);

        let prepared_inst = resolve_toolchain_for_suite(None, |key| match key {
            "ANNEAL_TEST_INSTALL_ROOT" => Some(inst_root.as_os_str().to_os_string()),
            "ANNEAL_LEAN" => Some(lean_bin.as_os_str().to_os_string()),
            "ANNEAL_SYSROOT" => Some(sysroot.as_os_str().to_os_string()),
            _ => None,
        })
        .expect("install root fallback resolves when ANNEAL_CAPTURE is unset");
        let staged_inst = prepared_inst.tools.capture.as_deref().unwrap();
        assert_ne!(staged_inst, fs::canonicalize(&inst_bin).unwrap().as_path());
        assert_eq!(prepared_inst.capture_bin_source, "env_install_root");
        assert_eq!(prepared_inst.capture_bin_sha256, expected_inst_sha);

        let cli_dir = tmp.path().join("cli_bin");
        fs::create_dir_all(&cli_dir).unwrap();
        let cli_bin = cli_dir.join("cargo-anneal");
        let sib_cap = cli_dir.join("anneal-rustc-capture-test-bin");
        fs::write(&cli_bin, b"cli").unwrap();
        fs::write(&sib_cap, b"sib-capture").unwrap();
        let prepared_sib = resolve_toolchain_for_suite(None, |key| match key {
            "ANNEAL_CLI" => Some(cli_bin.as_os_str().to_os_string()),
            "ANNEAL_TEST_INSTALL_ROOT" => Some(inst_root.as_os_str().to_os_string()),
            "ANNEAL_LEAN" => Some(lean_bin.as_os_str().to_os_string()),
            "ANNEAL_SYSROOT" => Some(sysroot.as_os_str().to_os_string()),
            _ => None,
        })
        .expect("sibling capture resolves when ANNEAL_CLI has adjacent capture bin");
        let staged_sib = prepared_sib.tools.capture.as_deref().unwrap();
        assert_ne!(staged_sib, fs::canonicalize(&sib_cap).unwrap().as_path());
        assert_eq!(prepared_sib.capture_bin_source, "sibling_capture_bin");
        assert_eq!(prepared_sib.capture_bin_sha256, sha256_file_hex(&sib_cap).unwrap());

        let (abs_explicit, _) =
            resolve_cache_root(tmp.path(), Some(Path::new("rel-cache"))).unwrap();
        assert!(abs_explicit.is_absolute(), "{}", abs_explicit.display());

        #[cfg(unix)]
        {
            let sym = tmp.path().join("sym-capture");
            std::os::unix::fs::symlink(&explicit_bin, &sym).unwrap();
            let sym_err = resolve_toolchain_for_suite(Some(&sym), |key| match key {
                "ANNEAL_LEAN" => Some(lean_bin.as_os_str().to_os_string()),
                "ANNEAL_SYSROOT" => Some(sysroot.as_os_str().to_os_string()),
                _ => None,
            })
            .unwrap_err();
            assert!(sym_err.contains("symlink"), "{sym_err}");

            // Even when ANNEAL_CLI is set without a sibling and falls back to
            // ANNEAL_TEST_INSTALL_ROOT, a symlinked install-root capture fails.
            let cli_no_sib = tmp.path().join("solo-cli");
            fs::write(&cli_no_sib, b"cli").unwrap();
            let bad_inst = tmp.path().join("bad_install");
            fs::create_dir_all(bad_inst.join("bin")).unwrap();
            std::os::unix::fs::symlink(&inst_bin, bad_inst.join("bin/anneal-rustc-capture"))
                .unwrap();
            let fall_err = resolve_toolchain_for_suite(None, |key| match key {
                "ANNEAL_CLI" => Some(cli_no_sib.as_os_str().to_os_string()),
                "ANNEAL_TEST_INSTALL_ROOT" => Some(bad_inst.as_os_str().to_os_string()),
                "ANNEAL_LEAN" => Some(lean_bin.as_os_str().to_os_string()),
                "ANNEAL_SYSROOT" => Some(sysroot.as_os_str().to_os_string()),
                _ => None,
            })
            .unwrap_err();
            assert!(fall_err.contains("symlink"), "{fall_err}");

            // Symlinked `ANNEAL_LEAN` / `ANNEAL_MVP_LEAN` leaves and ancestor
            // directories must fail before canonicalization in both modes.
            let sym_lean = tmp.path().join("sym-lean");
            std::os::unix::fs::symlink(&lean_bin, &sym_lean).unwrap();
            let sym_lean_dir = tmp.path().join("sym-lean-dir");
            fs::create_dir_all(tmp.path().join("real-lean-dir")).unwrap();
            let real_lean_in_dir = tmp.path().join("real-lean-dir/lean");
            fs::copy(&lean_bin, &real_lean_in_dir).unwrap();
            std::os::unix::fs::symlink(tmp.path().join("real-lean-dir"), &sym_lean_dir).unwrap();
            for bad_lean in [sym_lean, sym_lean_dir.join("lean")] {
                for key_name in ["ANNEAL_LEAN", "ANNEAL_MVP_LEAN"] {
                    let err_explicit = resolve_toolchain_for_suite(Some(&explicit_bin), |key| {
                        if key == key_name {
                            Some(bad_lean.as_os_str().to_os_string())
                        } else if key == "ANNEAL_SYSROOT" {
                            Some(sysroot.as_os_str().to_os_string())
                        } else {
                            None
                        }
                    })
                    .unwrap_err();
                    assert!(err_explicit.contains("symlink"), "{err_explicit}");

                    let err_env = resolve_toolchain_for_suite(None, |key| {
                        if key == key_name {
                            Some(bad_lean.as_os_str().to_os_string())
                        } else if key == "ANNEAL_CAPTURE" {
                            Some(env_bin.as_os_str().to_os_string())
                        } else if key == "ANNEAL_SYSROOT" {
                            Some(sysroot.as_os_str().to_os_string())
                        } else {
                            None
                        }
                    })
                    .unwrap_err();
                    assert!(err_env.contains("symlink"), "{err_env}");
                }
            }

            // Hardlinked Lean overrides (`ANNEAL_LEAN` / `ANNEAL_MVP_LEAN`)
            // and install-root Lean paths (`nlink > 1`) fail closed before
            // canonicalization in both capture-bin resolution modes.
            let hard_lean = tmp.path().join("hard-lean");
            fs::hard_link(&real_lean_in_dir, &hard_lean).unwrap();
            for key_name in ["ANNEAL_LEAN", "ANNEAL_MVP_LEAN"] {
                let hard_lean_exp_err = resolve_toolchain_for_suite(Some(&explicit_bin), |key| {
                    if key == key_name {
                        Some(hard_lean.as_os_str().to_os_string())
                    } else if key == "ANNEAL_SYSROOT" {
                        Some(sysroot.as_os_str().to_os_string())
                    } else {
                        None
                    }
                })
                .unwrap_err();
                assert!(hard_lean_exp_err.contains("hardlink"), "{hard_lean_exp_err}");

                let hard_lean_env_err = resolve_toolchain_for_suite(None, |key| {
                    if key == key_name {
                        Some(hard_lean.as_os_str().to_os_string())
                    } else if key == "ANNEAL_CAPTURE" {
                        Some(env_bin.as_os_str().to_os_string())
                    } else if key == "ANNEAL_SYSROOT" {
                        Some(sysroot.as_os_str().to_os_string())
                    } else {
                        None
                    }
                })
                .unwrap_err();
                assert!(hard_lean_env_err.contains("hardlink"), "{hard_lean_env_err}");
            }
            let hard_lean_inst = tmp.path().join("hard_lean_install");
            fs::create_dir_all(hard_lean_inst.join("lean/bin")).unwrap();
            fs::hard_link(&real_lean_in_dir, hard_lean_inst.join("lean/bin/lean")).unwrap();
            let hard_lean_inst_err = resolve_toolchain_for_suite(Some(&explicit_bin), |key| {
                if key == "ANNEAL_TEST_INSTALL_ROOT" {
                    Some(hard_lean_inst.as_os_str().to_os_string())
                } else if key == "ANNEAL_SYSROOT" {
                    Some(sysroot.as_os_str().to_os_string())
                } else {
                    None
                }
            })
            .unwrap_err();
            assert!(hard_lean_inst_err.contains("hardlink"), "{hard_lean_inst_err}");

            // Hardlinked capture binaries (`nlink > 1`) fail closed across
            // explicit, env, sibling, and install-root selection modes.
            let hard_cap = tmp.path().join("hard-capture");
            fs::hard_link(&explicit_bin, &hard_cap).unwrap();
            let hard_exp_err = resolve_toolchain_for_suite(Some(&hard_cap), |key| match key {
                "ANNEAL_LEAN" => Some(lean_bin.as_os_str().to_os_string()),
                "ANNEAL_SYSROOT" => Some(sysroot.as_os_str().to_os_string()),
                _ => None,
            })
            .unwrap_err();
            assert!(hard_exp_err.contains("hardlink"), "{hard_exp_err}");

            let hard_env_err = resolve_toolchain_for_suite(None, |key| match key {
                "ANNEAL_CAPTURE" => Some(hard_cap.as_os_str().to_os_string()),
                "ANNEAL_LEAN" => Some(lean_bin.as_os_str().to_os_string()),
                "ANNEAL_SYSROOT" => Some(sysroot.as_os_str().to_os_string()),
                _ => None,
            })
            .unwrap_err();
            assert!(hard_env_err.contains("hardlink"), "{hard_env_err}");

            let hard_cli_dir = tmp.path().join("hard_sib_cli_dir");
            fs::create_dir_all(&hard_cli_dir).unwrap();
            let hard_cli = hard_cli_dir.join("cargo-anneal");
            fs::write(&hard_cli, b"cli").unwrap();
            fs::hard_link(&explicit_bin, hard_cli_dir.join("anneal-rustc-capture")).unwrap();
            let hard_sib_err = resolve_toolchain_for_suite(None, |key| match key {
                "ANNEAL_CLI" => Some(hard_cli.as_os_str().to_os_string()),
                "ANNEAL_TEST_INSTALL_ROOT" => Some(inst_root.as_os_str().to_os_string()),
                "ANNEAL_LEAN" => Some(lean_bin.as_os_str().to_os_string()),
                "ANNEAL_SYSROOT" => Some(sysroot.as_os_str().to_os_string()),
                _ => None,
            })
            .unwrap_err();
            assert!(hard_sib_err.contains("hardlink"), "{hard_sib_err}");

            // Symlinked `ANNEAL_CLI` / `ANNEAL_MVP_CLI` must fail directly
            // without falling through to `ANNEAL_TEST_INSTALL_ROOT`.
            let sym_cli_leaf = tmp.path().join("sym-cli-leaf");
            std::os::unix::fs::symlink(&cli_bin, &sym_cli_leaf).unwrap();
            let sym_cli_dir = tmp.path().join("sym-cli-dir");
            std::os::unix::fs::symlink(&cli_dir, &sym_cli_dir).unwrap();
            for key_name in ["ANNEAL_CLI", "ANNEAL_MVP_CLI"] {
                for bad_cli in [sym_cli_leaf.clone(), sym_cli_dir.join("cargo-anneal")] {
                    let cli_err = resolve_toolchain_for_suite(None, |key| {
                        if key == key_name {
                            Some(bad_cli.as_os_str().to_os_string())
                        } else if key == "ANNEAL_TEST_INSTALL_ROOT" {
                            Some(inst_root.as_os_str().to_os_string())
                        } else if key == "ANNEAL_LEAN" {
                            Some(lean_bin.as_os_str().to_os_string())
                        } else if key == "ANNEAL_SYSROOT" {
                            Some(sysroot.as_os_str().to_os_string())
                        } else {
                            None
                        }
                    })
                    .unwrap_err();
                    assert!(cli_err.contains("symlink"), "{cli_err}");
                }
            }

            // `resolve_cache_root` rejects symlink leaves and symlink ancestor
            // components on explicit `--cache-root` before any session prepare.
            let real_cache_target = tmp.path().join("real-cache-target");
            fs::create_dir_all(&real_cache_target).unwrap();
            let sym_cache_leaf = tmp.path().join("sym-cache-leaf");
            std::os::unix::fs::symlink(&real_cache_target, &sym_cache_leaf).unwrap();
            for bad_cache in [sym_cache_leaf.clone(), sym_cache_leaf.join("sub/nested")] {
                let cache_err = resolve_cache_root(tmp.path(), Some(&bad_cache)).unwrap_err();
                assert!(cache_err.contains("symlink"), "{cache_err}");
            }

            // Store-contained Nix symlinks (`symlinkJoin` and wrapper links
            // targeting `/nix/store`) work for `ANNEAL_LEAN`,
            // `ANNEAL_TEST_INSTALL_ROOT`, `ANNEAL_CAPTURE`, and `ANNEAL_CLI`,
            // while store-escaping symlinks still fail closed.
            let fake_store = tmp.path().join("nix/store");
            let real_lean_pkg = fake_store.join("1111-lean/bin");
            let real_cap_pkg = fake_store.join("2222-capture/bin");
            let store_env_bin = fake_store.join("3333-env/bin");
            let opt_wrappers = tmp.path().join("opt-nix/bin");
            fs::create_dir_all(&real_lean_pkg).unwrap();
            fs::create_dir_all(&real_cap_pkg).unwrap();
            fs::create_dir_all(&store_env_bin).unwrap();
            fs::create_dir_all(&opt_wrappers).unwrap();
            let store_real_lean = real_lean_pkg.join("lean");
            let store_real_cap = real_cap_pkg.join("anneal-rustc-capture");
            let store_real_cli = real_cap_pkg.join("cargo-anneal");
            fs::write(&store_real_lean, b"store-lean").unwrap();
            fs::write(&store_real_cap, b"store-capture-bytes").unwrap();
            fs::write(&store_real_cli, b"store-cli").unwrap();
            let join_lean = store_env_bin.join("lean");
            let join_cap = store_env_bin.join("anneal-rustc-capture");
            let wrap_lean = opt_wrappers.join("lean");
            let wrap_cap = opt_wrappers.join("anneal-rustc-capture");
            let wrap_cli = opt_wrappers.join("cargo-anneal");
            std::os::unix::fs::symlink(&store_real_lean, &join_lean).unwrap();
            std::os::unix::fs::symlink(&store_real_cap, &join_cap).unwrap();
            std::os::unix::fs::symlink(&join_lean, &wrap_lean).unwrap();
            std::os::unix::fs::symlink(&join_cap, &wrap_cap).unwrap();
            std::os::unix::fs::symlink(&store_real_cli, &wrap_cli).unwrap();
            let expected_store_cap_sha = sha256_file_hex(&store_real_cap).unwrap();

            let prep_join =
                resolve_toolchain_for_suite_with_store(None, &fake_store, |key| match key {
                    "ANNEAL_LEAN" => Some(join_lean.as_os_str().to_os_string()),
                    "ANNEAL_CAPTURE" => Some(join_cap.as_os_str().to_os_string()),
                    "ANNEAL_SYSROOT" => Some(sysroot.as_os_str().to_os_string()),
                    _ => None,
                })
                .expect("store symlinkJoin Lean and capture must resolve");
            assert_eq!(prep_join.capture_bin_sha256, expected_store_cap_sha);
            assert_eq!(
                fs::read(prep_join.tools.capture.as_deref().unwrap()).unwrap(),
                b"store-capture-bytes"
            );

            let prep_wrap = resolve_toolchain_for_suite_with_store(
                Some(&wrap_cap),
                &fake_store,
                |key| match key {
                    "ANNEAL_LEAN" => Some(wrap_lean.as_os_str().to_os_string()),
                    "ANNEAL_SYSROOT" => Some(sysroot.as_os_str().to_os_string()),
                    _ => None,
                },
            )
            .expect("wrapper symlinks targeting store must resolve and stage");
            assert_eq!(prep_wrap.capture_bin_sha256, expected_store_cap_sha);

            let prep_wrap_cli =
                resolve_toolchain_for_suite_with_store(None, &fake_store, |key| match key {
                    "ANNEAL_MVP_LEAN" => Some(wrap_lean.as_os_str().to_os_string()),
                    "ANNEAL_CLI" => Some(wrap_cli.as_os_str().to_os_string()),
                    "ANNEAL_SYSROOT" => Some(sysroot.as_os_str().to_os_string()),
                    _ => None,
                })
                .expect("store-contained ANNEAL_CLI sibling capture must resolve");
            assert_eq!(prep_wrap_cli.capture_bin_source, "sibling_capture_bin");
            assert_eq!(prep_wrap_cli.capture_bin_sha256, expected_store_cap_sha);

            let esc_store_cap = store_env_bin.join("esc-capture");
            std::os::unix::fs::symlink(&explicit_bin, &esc_store_cap).unwrap();
            let err_esc =
                resolve_toolchain_for_suite_with_store(Some(&esc_store_cap), &fake_store, |key| {
                    match key {
                        "ANNEAL_LEAN" => Some(join_lean.as_os_str().to_os_string()),
                        "ANNEAL_SYSROOT" => Some(sysroot.as_os_str().to_os_string()),
                        _ => None,
                    }
                })
                .unwrap_err();
            assert!(err_esc.contains("escaped store"), "{err_esc}");
        }
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn resolve_toolchain_keeps_fd_pinned_anneal_capture_without_pathname_restage() {
        use std::os::unix::fs::PermissionsExt as _;

        let lean_bin = default_lean_path().expect("resolve pinned lean");
        let sysroot = default_rust_sysroot().expect("resolve rust sysroot");
        let tmp = tempfile::tempdir().unwrap();
        let root = fs::canonicalize(tmp.path()).unwrap();
        let fake_store = root.join("nix-store");
        fs::create_dir_all(&fake_store).unwrap();

        let stage_tmp = tempfile::Builder::new().prefix("fd-cap-").tempdir_in(&root).unwrap();
        let stage_disk = fs::canonicalize(stage_tmp.path()).unwrap();
        let rel_bin = Path::new(".anneal-isolated-bins/anneal-rustc-capture-0123456789abcdef");
        let (_, pre_staging) = crate::rustc_runner::ImmutableStagingDir::build_and_pin(
            stage_tmp,
            "fd-pinned capture",
            |_, pinned_root| {
                let iso_dir = pinned_root.join(".anneal-isolated-bins");
                fs::create_dir_all(&iso_dir).unwrap();
                let bin = pinned_root.join(rel_bin);
                fs::write(&bin, b"genuine-fd-pinned-capture").unwrap();
                fs::set_permissions(&bin, fs::Permissions::from_mode(0o555)).unwrap();
                Ok(())
            },
        )
        .unwrap();
        let pinned_cap = pre_staging.pin_path(rel_bin);
        assert!(pinned_cap.starts_with("/proc/self/fd/"), "{}", pinned_cap.display());
        let expected_sha = sha256_file_hex(&pinned_cap).unwrap();

        // Move the backing directory aside so unpinned `/tmp` resolution points
        // at a stale/deleted path; pre_staging must remain authoritative.
        let moved_disk = root.join("moved-fd-cap");
        fs::rename(&stage_disk, &moved_disk).unwrap();

        let prepared = resolve_toolchain_for_suite_with_store(None, &fake_store, |key| match key {
            "ANNEAL_CAPTURE" => Some(pinned_cap.as_os_str().to_os_string()),
            "ANNEAL_LEAN" => Some(lean_bin.as_os_str().to_os_string()),
            "ANNEAL_SYSROOT" => Some(sysroot.as_os_str().to_os_string()),
            _ => None,
        })
        .expect("fd-pinned ANNEAL_CAPTURE must resolve cleanly via pre_staged");
        assert_eq!(prepared.capture_bin_source, "env_anneal_capture");
        assert_eq!(prepared.capture_bin_sha256, expected_sha);
        let resolved_cap = prepared.tools.capture.as_deref().unwrap();
        assert!(resolved_cap.starts_with("/proc/self/fd/"), "{}", resolved_cap.display());
        assert_eq!(fs::read(resolved_cap).unwrap(), b"genuine-fd-pinned-capture");

        drop(prepared);
        drop(pre_staging);
        crate::rustc_runner::restore_dir_write_perms_top_down(&moved_disk);
        fs::remove_dir_all(&moved_disk).unwrap();
    }

    #[test]
    fn differential_report_has_no_duplicate_kind_keys_and_round_trips() {
        let u32_val = MirValue::Int { int_kind: IntKind::U32, bits: 4 };
        let report = DifferentialReport {
            schema: "anneal-differential-run/v1".to_owned(),
            alpha_notice: ALPHA_NOTICE.to_owned(),
            mir_dialect: "profile_v1".to_owned(),
            manifest_path: DEFAULT_CORPUS_MANIFEST_REL.to_owned(),
            capture_bin_source: "explicit".to_owned(),
            capture_bin_sha256: "a".repeat(64),
            prebuilt_overlay: "none".to_owned(),
            legs: vec![
                "miri".to_owned(),
                "lean_step_core_captured".to_owned(),
                "lean_wp_kernel_single_block".to_owned(),
            ],
            metrics: SuiteMetrics {
                compared_count: 1,
                pass_agreed_count: 1,
                ub_agreed_count: 0,
                conservative_unsupported_count: 0,
                kernel_checked_pass_count: 1,
                kernel_checked_ub_count: 0,
                unsound_missed_fault_count: 0,
                value_mismatch_count: 0,
                unexpected_conservative_count: 0,
                leg_divergence_count: 0,
            },
            red_flags_passed: 0,
            red_flag_error: Some("partial synthetic".to_owned()),
            cases: vec![CaseReport {
                id: "arith_u32_wrapping_add".to_owned(),
                source: "src/arith_pass.rs".to_owned(),
                function: "u32_wrapping_add".to_owned(),
                category: "arith".to_owned(),
                expected: Expectation::Pass,
                allow_conservative_unsupported: false,
                kernel_checked: true,
                miri: ObservedOutcome::Returned { value: u32_val.clone() },
                lean: ObservedOutcome::Returned { value: u32_val.clone() },
                mir_eval: Some(ObservedOutcome::Returned { value: u32_val.clone() }),
                verdict: Verdict::AgreeValue { value: u32_val },
            }],
            mutant_check: None,
        };

        let serialized =
            serde_json::to_string_pretty(&report).expect("serialize DifferentialReport");
        assert!(serialized.contains("\"value\": {"), "{serialized}");
        let round_trip: DifferentialReport =
            serde_json::from_str(&serialized).expect("round-trip DifferentialReport JSON");
        assert_eq!(round_trip, report);
    }
}
