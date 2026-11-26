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

pub mod corpus;
pub mod lean_runner;
pub mod mir_eval_runner;
pub mod miri_runner;
pub mod mutants;
pub mod verdict;

use std::{
    collections::BTreeMap,
    env,
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
    thread,
};

use anneal_testkit::{ToolchainEnv, ToolchainMode};
use serde::{Deserialize, Serialize};

use crate::{
    corpus::{DEFAULT_CORPUS_MANIFEST_REL, LitmusCase, load_manifest},
    lean_runner::{
        CapturedModule, LeanCaseResult, LeanSession, sha256_file_hex,
        validate_and_canonicalize_capture_bin,
    },
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
    let in_repo_target = anneal_root.join("target");
    let raw_cache = if let Some(p) = explicit {
        p.to_path_buf()
    } else if let Some(cd) = env::var_os("ANNEAL_DIFF_CACHE_DIR").filter(|v| !v.is_empty()) {
        PathBuf::from(cd)
    } else if let Some(td) = env::var_os("CARGO_TARGET_DIR").filter(|v| !v.is_empty()) {
        PathBuf::from(td).join("anneal-diff-cache")
    } else if in_repo_target.is_dir() && tempfile::tempfile_in(&in_repo_target).is_ok() {
        in_repo_target.join("anneal-diff-cache")
    } else {
        let private_tmp = tempfile::Builder::new()
            .prefix("anneal-diff-cache-")
            .tempdir()
            .map_err(|e| format!("create private differential cache tempdir: {e}"))?;
        let path = std::path::absolute(private_tmp.path())
            .map_err(|e| format!("absolutize private cache tempdir: {e}"))?;
        return Ok((path, Some(private_tmp)));
    };
    let abs_cache = std::path::absolute(&raw_cache)
        .map_err(|e| format!("absolutize cache root {}: {e}", raw_cache.display()))?;
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

/// Resolve toolchain coordinates and capture binary provenance without
/// allowing ambient `ANNEAL_CAPTURE` / `ANNEAL_MVP_CAPTURE` to override an
/// explicit `capture_bin`. Rejects symlink capture binaries BEFORE
/// canonicalization.
pub fn resolve_toolchain_for_suite(
    explicit_capture_bin: Option<&Path>,
    get_env: impl Fn(&str) -> Option<OsString>,
) -> Result<(ToolchainEnv, String, String), String> {
    if let Some(explicit) = explicit_capture_bin {
        let canon_explicit = validate_and_canonicalize_capture_bin(explicit)?;
        let sha256 = sha256_file_hex(&canon_explicit)?;
        let tools = ToolchainEnv::resolve_with_env(
            ToolchainMode::WorkspaceBuild {
                cli_bin: None,
                capture_bin: Some(canon_explicit),
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
        return Ok((tools, "explicit".to_owned(), sha256));
    }

    let non_empty_path = |key: &str| -> Option<PathBuf> {
        get_env(key).filter(|v| !v.is_empty()).map(PathBuf::from)
    };
    let env_capture =
        non_empty_path("ANNEAL_CAPTURE").or_else(|| non_empty_path("ANNEAL_MVP_CAPTURE"));
    let capture_bin_source = if let Some(raw_cap) = env_capture {
        let _ = validate_and_canonicalize_capture_bin(&raw_cap)?;
        "env_anneal_capture"
    } else if let Some(sib_cap) = non_empty_path("ANNEAL_CLI")
        .or_else(|| non_empty_path("ANNEAL_MVP_CLI"))
        .and_then(|cli_raw| fs::canonicalize(&cli_raw).ok())
        .and_then(|canon_cli| {
            ["anneal-rustc-capture", "anneal-rustc-capture-test-bin"]
                .into_iter()
                .map(|name| canon_cli.with_file_name(name))
                .find(|cand| {
                    fs::symlink_metadata(cand)
                        .is_ok_and(|m| m.is_file() || m.file_type().is_symlink())
                })
        })
    {
        let _ = validate_and_canonicalize_capture_bin(&sib_cap)?;
        "sibling_capture_bin"
    } else if let Some(root) = non_empty_path("ANNEAL_TEST_INSTALL_ROOT") {
        let inst_cap = root.join("bin/anneal-rustc-capture");
        if fs::symlink_metadata(&inst_cap).is_ok() {
            let _ = validate_and_canonicalize_capture_bin(&inst_cap)?;
        }
        "env_install_root"
    } else {
        "env_install_root"
    };

    let tools = ToolchainEnv::resolve_with_env(
        ToolchainMode::WorkspaceBuild { cli_bin: None, capture_bin: None, auditor_bin: None },
        &get_env,
    )?;
    let canon_capture = tools.capture.as_deref().ok_or_else(|| {
        "missing `anneal-rustc-capture` binary: pass `--capture-bin` or set `ANNEAL_CAPTURE`, `ANNEAL_CLI`, or `ANNEAL_TEST_INSTALL_ROOT`".to_owned()
    })?;
    let sha256 = sha256_file_hex(canon_capture)?;
    Ok((tools, capture_bin_source.to_owned(), sha256))
}

/// Execute all active legs against the manifest corpus and return the summary
/// report (caller inspects [`DifferentialReport::is_passing`]).
pub fn run_differential_suite(opts: &RunOptions) -> Result<DifferentialReport, String> {
    let loaded = load_manifest(&opts.manifest_path)?;
    let anneal_root = find_anneal_root(&loaded.manifest_path)?;
    let (cache_root, _cache_guard) = resolve_cache_root(&anneal_root, opts.cache_root.as_deref())?;
    let (tools, capture_bin_source, capture_bin_sha256) =
        resolve_toolchain_for_suite(opts.capture_bin.as_deref(), |k| env::var_os(k))?;

    let (miri_res, lean_res) = thread::scope(|scope| {
        let m = scope.spawn(|| MiriSession::prepare(&tools.sysroot, &cache_root));
        let l = scope.spawn(|| LeanSession::prepare(&anneal_root, &tools, &cache_root));
        (
            m.join().unwrap_or_else(|_| Err("Miri prepare panicked".to_owned())),
            l.join().unwrap_or_else(|_| Err("Lean prepare panicked".to_owned())),
        )
    });
    let miri_session = miri_res?;
    let lean_session = lean_res?;

    let run_workspace =
        tempfile::tempdir().map_err(|e| format!("create temporary differential workdir: {e}"))?;

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
        let mir_eval = if let Some(eval_bin) = &opts.mir_eval_bin {
            let cap = captured_by_source
                .get(&case.source_abs)
                .ok_or_else(|| format!("missing capture module for {:?}", case.source_abs))?;
            match cap.body_ids_by_fn.get(&case.function) {
                Some(&body_id) => Some(mir_eval_runner::run_mir_eval_case(
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

        let (tools_explicit, src_explicit, sha_explicit) =
            resolve_toolchain_for_suite(Some(&explicit_bin), |key| match key {
                "ANNEAL_CAPTURE" => Some(OsString::from("/tmp/nonexistent-sentinel")),
                "ANNEAL_MVP_CAPTURE" => Some(env_bin.as_os_str().to_os_string()),
                "ANNEAL_LEAN" => Some(lean_bin.as_os_str().to_os_string()),
                "ANNEAL_SYSROOT" => Some(sysroot.as_os_str().to_os_string()),
                _ => None,
            })
            .expect("explicit capture_bin must override ambient ANNEAL_CAPTURE");
        assert_eq!(
            tools_explicit.capture.as_deref(),
            Some(fs::canonicalize(&explicit_bin).unwrap().as_path())
        );
        assert_eq!(src_explicit, "explicit");
        assert_eq!(sha_explicit, sha256_file_hex(&explicit_bin).unwrap());
        assert_ne!(sha_explicit, sha256_file_hex(&env_bin).unwrap());

        let (tools_env, src_env, sha_env) = resolve_toolchain_for_suite(None, |key| match key {
            "ANNEAL_CAPTURE" => Some(env_bin.as_os_str().to_os_string()),
            "ANNEAL_TEST_INSTALL_ROOT" => Some(inst_root.as_os_str().to_os_string()),
            "ANNEAL_LEAN" => Some(lean_bin.as_os_str().to_os_string()),
            "ANNEAL_SYSROOT" => Some(sysroot.as_os_str().to_os_string()),
            _ => None,
        })
        .expect("env capture resolves when capture_bin is None");
        assert_eq!(
            tools_env.capture.as_deref(),
            Some(fs::canonicalize(&env_bin).unwrap().as_path())
        );
        assert_eq!(src_env, "env_anneal_capture");
        assert_eq!(sha_env, sha256_file_hex(&env_bin).unwrap());

        let (tools_inst, src_inst, sha_inst) = resolve_toolchain_for_suite(None, |key| match key {
            "ANNEAL_TEST_INSTALL_ROOT" => Some(inst_root.as_os_str().to_os_string()),
            "ANNEAL_LEAN" => Some(lean_bin.as_os_str().to_os_string()),
            "ANNEAL_SYSROOT" => Some(sysroot.as_os_str().to_os_string()),
            _ => None,
        })
        .expect("install root fallback resolves when ANNEAL_CAPTURE is unset");
        assert_eq!(
            tools_inst.capture.as_deref(),
            Some(fs::canonicalize(&inst_bin).unwrap().as_path())
        );
        assert_eq!(src_inst, "env_install_root");
        assert_eq!(sha_inst, sha256_file_hex(&inst_bin).unwrap());

        let cli_dir = tmp.path().join("cli_bin");
        fs::create_dir_all(&cli_dir).unwrap();
        let cli_bin = cli_dir.join("cargo-anneal");
        let sib_cap = cli_dir.join("anneal-rustc-capture-test-bin");
        fs::write(&cli_bin, b"cli").unwrap();
        fs::write(&sib_cap, b"sib-capture").unwrap();
        let (tools_sib, src_sib, sha_sib) = resolve_toolchain_for_suite(None, |key| match key {
            "ANNEAL_CLI" => Some(cli_bin.as_os_str().to_os_string()),
            "ANNEAL_TEST_INSTALL_ROOT" => Some(inst_root.as_os_str().to_os_string()),
            "ANNEAL_LEAN" => Some(lean_bin.as_os_str().to_os_string()),
            "ANNEAL_SYSROOT" => Some(sysroot.as_os_str().to_os_string()),
            _ => None,
        })
        .expect("sibling capture resolves when ANNEAL_CLI has adjacent capture bin");
        assert_eq!(
            tools_sib.capture.as_deref(),
            Some(fs::canonicalize(&sib_cap).unwrap().as_path())
        );
        assert_eq!(src_sib, "sibling_capture_bin");
        assert_eq!(sha_sib, sha256_file_hex(&sib_cap).unwrap());

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
        }
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
