// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Stage-2 seeded property fuzzer, batched 4-way oracle runner, and
//! auto-shrinking campaign orchestrator (`anneal-diff fuzz`).

use std::{
    collections::{BTreeMap, BTreeSet},
    env,
    path::{Path, PathBuf},
    sync::Arc,
    thread,
    time::{Duration, Instant},
};

use anneal_testkit::ToolchainEnv;
use serde::{Deserialize, Serialize};

use crate::{
    ALPHA_NOTICE,
    r#gen::{GenCategory, GenConfig, GenProgram, generate_campaign, render_batch_crate},
    lean_runner::{FuzzCaptureBody, FuzzLeanCaseResult, LeanSession},
    mir_eval_runner::{
        build_mir_eval_from_manifest, run_mir_eval_raw_with_evidence,
        run_pinned_mir_eval_raw_with_evidence,
    },
    miri_runner::MiriSession,
    resolve_cache_root, resolve_toolchain_for_suite,
    rustc_runner::{FuzzExecCase, ImmutableStagingDir, RustcSession},
    shrink::{ShrinkConfig, ShrinkOutcome, ShrinkTrace, shrink_program_with_deadline},
    verdict::{
        FuzzCaseEvaluation, MirValue, ObservedOutcome, OracleAgreementClass, RustcCheckStatus,
        TerminalOutcome, evaluate_fuzz_case_with_rustc_leg, outcomes_agree_mir,
    },
};

const FUZZ_BATCH_SIZE: usize = 32;
const MIR_EVAL_BATCH_BUDGET_SECS: u64 = 180;
const SHRINK_CAMPAIGN_BUDGET_SECS: u64 = 180;

const fn default_fuzz_max_stmts() -> usize {
    6
}

const fn default_fuzz_ub_ratio() -> f64 {
    0.20
}

const fn default_fuzz_fuel() -> usize {
    1_500
}

/// Configuration for a Stage-2 generative differential fuzz campaign.
#[derive(Clone, Debug)]
pub struct FuzzOptions {
    pub seed: u64,
    pub cases: usize,
    pub max_stmts: usize,
    pub ub_ratio: f64,
    pub shrink: bool,
    pub run_rustc: bool,
    pub capture_bin: Option<PathBuf>,
    pub mir_eval_bin: Option<PathBuf>,
    pub mir_eval_manifest: Option<PathBuf>,
    pub cache_root: Option<PathBuf>,
    pub min_admission_rate: f64,
    pub fuel: usize,
    pub shrink_config: ShrinkConfig,
}

impl Default for FuzzOptions {
    fn default() -> Self {
        Self {
            seed: 20_261_124,
            cases: 32,
            max_stmts: 6,
            ub_ratio: 0.20,
            shrink: true,
            run_rustc: true,
            capture_bin: None,
            mir_eval_bin: None,
            mir_eval_manifest: None,
            cache_root: None,
            min_admission_rate: 0.90,
            fuel: 1_500,
            shrink_config: ShrinkConfig::default(),
        }
    }
}

/// Per-leg case-bound result evidence proving each leg's reported
/// [`ObservedOutcome`] originated from executing this specific `case_id` /
/// `fn_name` / captured `body_id`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FuzzLegEvidence {
    #[serde(skip_serializing_if = "Option::is_none")]
    pub lean_probe_line: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub capture_refusal_json: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub miri_evidence: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rustc_evidence: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub mir_eval_body_id: Option<usize>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub mir_eval_raw_json: Option<String>,
}

/// Verified multi-leg oracle evaluation receipt binding a minimized
/// counterexample (`ShrinkTrace::minimized_source`,
/// `ShrinkTrace::minimized_args`) to live per-leg executions that preserve the
/// original failure signature.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FuzzMinimizedVerification {
    pub fn_name: String,
    pub args: Vec<MirValue>,
    pub program_sha256: String,
    #[serde(default = "default_fuzz_fuel")]
    pub fuel: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub capture_body: Option<FuzzCaptureBody>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rustc: Option<ObservedOutcome>,
    pub miri: ObservedOutcome,
    pub lean: ObservedOutcome,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub mir_eval: Option<ObservedOutcome>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub capture_rejected: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub leg_evidence: Option<FuzzLegEvidence>,
    pub evaluation: FuzzCaseEvaluation,
}

impl FuzzMinimizedVerification {
    fn from_case_report(rep: FuzzCaseReport) -> Self {
        Self {
            fn_name: rep.fn_name,
            args: rep.args,
            program_sha256: rep.program_sha256,
            fuel: rep.fuel,
            capture_body: rep.capture_body,
            rustc: rep.rustc,
            miri: rep.miri,
            lean: rep.lean,
            mir_eval: rep.mir_eval,
            capture_rejected: rep.capture_rejected,
            leg_evidence: rep.leg_evidence,
            evaluation: rep.evaluation,
        }
    }
}

/// Per-case Stage-2 4-way differential record.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FuzzCaseReport {
    pub case_id: String,
    pub fn_name: String,
    pub master_seed: u64,
    pub case_index: usize,
    pub category: GenCategory,
    pub args: Vec<MirValue>,
    pub program_sha256: String,
    #[serde(default = "default_fuzz_fuel")]
    pub fuel: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub capture_body: Option<FuzzCaptureBody>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rustc: Option<ObservedOutcome>,
    pub miri: ObservedOutcome,
    pub lean: ObservedOutcome,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub mir_eval: Option<ObservedOutcome>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub capture_rejected: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub leg_evidence: Option<FuzzLegEvidence>,
    #[serde(default)]
    pub exercised_move_reinit: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub move_reinit_evidence: Option<crate::lean_runner::MoveReinitEvidence>,
    pub evaluation: FuzzCaseEvaluation,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub shrink_trace: Option<ShrinkTrace>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub shrink_verification: Option<Box<FuzzMinimizedVerification>>,
}

/// Aggregate counters and telemetry for a Stage-2 fuzz campaign.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct FuzzMetrics {
    pub total_cases: usize,
    pub safe_admitted_cases: usize,
    pub boundary_edge_cases: usize,
    pub targeted_ub_probes: usize,
    pub scope_control_cases: usize,
    pub admission_eligible_cases: usize,
    pub admitted_cases: usize,
    pub admission_rate: f64,
    pub bi_fault_equiv_count: usize,
    pub ub_probes_agreed_count: usize,
    pub conservative_over_approx_count: usize,
    pub spurious_lean_ub_count: usize,
    pub admitted_authority_ub_count: usize,
    pub unsound_accept_count: usize,
    pub authority_disagreement_count: usize,
    pub move_reinit_exercised_count: usize,
    pub disclosed_gaps: BTreeMap<String, usize>,
    pub rustc_agreed_count: usize,
    pub rustc_ignored_ub_count: usize,
    pub rustc_disagreement_count: usize,
    pub wall_clock_sec: f64,
}

/// Complete JSON-serializable report emitted by `run_fuzz_campaign` and
/// `anneal-diff fuzz`.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct FuzzReport {
    pub schema: String,
    pub alpha_notice: String,
    pub mir_dialect: String,
    pub seed: u64,
    #[serde(default = "default_fuzz_max_stmts")]
    pub max_stmts: usize,
    #[serde(default = "default_fuzz_ub_ratio")]
    pub ub_ratio: f64,
    #[serde(default = "default_fuzz_fuel")]
    pub fuel: usize,
    pub capture_bin_source: String,
    pub capture_bin_sha256: String,
    pub prebuilt_overlay: String,
    pub legs: Vec<String>,
    pub min_admission_rate: f64,
    pub metrics: FuzzMetrics,
    pub gate_error: Option<String>,
    pub cases: Vec<FuzzCaseReport>,
}

impl FuzzReport {
    /// Whether zero hard/spurious/generator-UB failures occurred and all
    /// anti-vacuity and admission gates passed.
    pub fn is_passing(&self) -> bool {
        let rustc_complete = !self.legs.iter().any(|l| l == "rustc_compiled")
            || self.cases.iter().all(|c| {
                c.rustc.is_some() || matches!(c.miri, ObservedOutcome::UndefinedBehavior { .. })
            });
        self.gate_error.is_none()
            && self.mir_dialect == "profile_v1"
            && rustc_complete
            && self.metrics.total_cases > 0
            && self.metrics.unsound_accept_count == 0
            && self.metrics.authority_disagreement_count == 0
            && self.metrics.spurious_lean_ub_count == 0
            && self.metrics.admitted_authority_ub_count == 0
            && self.metrics.bi_fault_equiv_count > 0
            && (self.metrics.targeted_ub_probes == 0
                || self.metrics.ub_probes_agreed_count == self.metrics.targeted_ub_probes)
            && self.metrics.admission_eligible_cases > 0
            && self.metrics.admission_rate >= self.min_admission_rate
    }
}

/// Coarse discriminant tag for a [`TerminalOutcome`] used in
/// [`FailureSignature`] matching during counterexample shrinking.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TerminalKindTag {
    Returned,
    Unwound,
    Aborted,
    UndefinedBehavior,
    Unsupported,
    OutOfFuel,
}

impl TerminalKindTag {
    fn from_terminal(t: &TerminalOutcome) -> Self {
        match t {
            TerminalOutcome::Returned { .. } => Self::Returned,
            TerminalOutcome::Unwound { .. } => Self::Unwound,
            TerminalOutcome::Aborted { .. } => Self::Aborted,
            TerminalOutcome::UndefinedBehavior { .. } => Self::UndefinedBehavior,
            TerminalOutcome::Unsupported { .. } => Self::Unsupported,
            TerminalOutcome::OutOfFuel { .. } => Self::OutOfFuel,
        }
    }
}

/// Normalized Miri UB cause bucket preserved during counterexample shrinking so
/// minimizing one UB mode (such as `MIN / -1` signed overflow) cannot drift
/// into a distinct UB mode (such as division by zero).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MiriUbBucket {
    DivisionByZero,
    SignedDivOverflow,
    ArithmeticOverflow,
    OversizedShift,
    Unreachable,
    InvalidValue,
    Uninitialized,
    Other,
}

impl MiriUbBucket {
    pub fn classify(detail: &str) -> Self {
        let lower = detail.to_ascii_lowercase();
        if lower.contains("dividing by zero") || lower.contains("divisor of zero") {
            Self::DivisionByZero
        } else if lower.contains("overflow in signed")
            || lower.contains("calculating the remainder with overflow")
            || lower.contains("dividing min by -1")
        {
            Self::SignedDivOverflow
        } else if lower.contains("arithmetic overflow")
            || lower.contains("overflowing add")
            || lower.contains("overflowing sub")
            || lower.contains("overflowing mul")
        {
            Self::ArithmeticOverflow
        } else if lower.contains("overflowing shift") {
            Self::OversizedShift
        } else if lower.contains("unreachable") {
            Self::Unreachable
        } else if lower.contains("invalid value") || lower.contains("discriminant") {
            Self::InvalidValue
        } else if lower.contains("uninitialized") || lower.contains("uninit") {
            Self::Uninitialized
        } else {
            Self::Other
        }
    }
}

/// Whether any active leg in `report` encountered an
/// [`ObservedOutcome::ToolError`] (ignoring a `rustc` `ToolError` when Miri
/// already established UB and marked Leg 0 `IgnoredDueToMiriUb`).
pub fn report_has_any_tool_error(report: &FuzzCaseReport) -> bool {
    let rustc_err = !matches!(report.evaluation.rustc_status, RustcCheckStatus::IgnoredDueToMiriUb)
        && matches!(report.rustc, Some(ObservedOutcome::ToolError { .. }));
    matches!(report.miri, ObservedOutcome::ToolError { .. })
        || rustc_err
        || matches!(report.mir_eval, Some(ObservedOutcome::ToolError { .. }))
        || (report.capture_rejected.is_none()
            && matches!(report.lean, ObservedOutcome::ToolError { .. }))
}

/// Normalized secondary-leg (`rustc` or `anneal-mir-eval`) disagreement
/// subtype preserved during counterexample shrinking.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SecondaryMismatchKind {
    /// Both the reference leg and the secondary leg returned concrete values,
    /// and the returned values differed (`Returned(v1)` vs `Returned(v2)`).
    ReturnedValue,
    /// At least one leg terminated without a matching return; pins the
    /// secondary leg's normalized outcome tag, init-rejection bit, and UB
    /// bucket so shrinking cannot drift across failure modes.
    OutcomeKind { kind: TerminalKindTag, init_unsupported: bool, ub_bucket: Option<MiriUbBucket> },
}

fn secondary_mismatch_kind(
    primary: &TerminalOutcome,
    secondary: &ObservedOutcome,
) -> Option<SecondaryMismatchKind> {
    let secondary_term = secondary.to_terminal_outcome().ok()?;
    if let (TerminalOutcome::Returned { value: lhs }, TerminalOutcome::Returned { value: rhs }) =
        (primary, &secondary_term)
        && lhs != rhs
    {
        return Some(SecondaryMismatchKind::ReturnedValue);
    }
    let ub_bucket = match &secondary_term {
        TerminalOutcome::UndefinedBehavior { detail } => Some(MiriUbBucket::classify(detail)),
        _ => None,
    };
    Some(SecondaryMismatchKind::OutcomeKind {
        kind: TerminalKindTag::from_terminal(&secondary_term),
        init_unsupported: matches!(secondary, ObservedOutcome::InitUnsupported { .. }),
        ub_bucket,
    })
}

/// Whether a case targets the admitted Profile v1 subset (`SafeAdmitted` or
/// `BoundaryEdgeCase`) yet triggered Miri Undefined Behavior (a
/// generator-safety invariant failure that must retain source and be shrunk).
pub const fn is_admitted_authority_ub(category: GenCategory, miri: &ObservedOutcome) -> bool {
    category.counts_toward_admission() && matches!(miri, ObservedOutcome::UndefinedBehavior { .. })
}

/// Whether a [`GenCategory::TargetedUbProbe`] failed to exhibit agreed
/// Undefined Behavior across Miri and Lean (e.g., Miri stopped hitting UB or
/// Lean conservatively refused the probe).
pub const fn is_missed_targeted_ub_probe(
    category: GenCategory,
    miri: &ObservedOutcome,
    evaluation: &FuzzCaseEvaluation,
) -> bool {
    matches!(category, GenCategory::TargetedUbProbe)
        && (!matches!(miri, ObservedOutcome::UndefinedBehavior { .. })
            || !matches!(evaluation.agreement, OracleAgreementClass::BiFaultEquivAgreement))
}

/// Whether `report` (or a candidate evaluation) is a shrinkable failure whose
/// source and counterexample trace should be retained.
pub const fn is_shrinkable_case(
    category: GenCategory,
    miri: &ObservedOutcome,
    evaluation: &FuzzCaseEvaluation,
) -> bool {
    evaluation.is_shrinkable_failure()
        || is_admitted_authority_ub(category, miri)
        || is_missed_targeted_ub_probe(category, miri, evaluation)
}

/// Exact failure signature preserved by counterexample shrinking.
///
/// Rejects any candidate where any active leg produced
/// [`ObservedOutcome::ToolError`] and pins `(agreement, miri_kind,
/// miri_ub_bucket, lean_kind, lean_ub_bucket, lean_init_unsupported,
/// rustc_mismatch, mir_eval_mismatch, is_spurious_lean_ub,
/// admitted_authority_ub, missed_targeted_ub_probe)` so shrinking never drifts
/// between value mismatch, distinct Miri or Lean UB causes, secondary-leg
/// mismatch subtypes, spurious Lean UB, accidental admitted-category UB,
/// targeted UB misses, or infrastructure errors.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FailureSignature {
    pub agreement: OracleAgreementClass,
    pub miri_kind: TerminalKindTag,
    pub miri_ub_bucket: Option<MiriUbBucket>,
    pub lean_kind: Option<TerminalKindTag>,
    pub lean_ub_bucket: Option<MiriUbBucket>,
    pub lean_init_unsupported: bool,
    pub rustc_mismatch: Option<SecondaryMismatchKind>,
    pub mir_eval_mismatch: Option<SecondaryMismatchKind>,
    pub is_spurious_lean_ub: bool,
    pub admitted_authority_ub: bool,
    pub missed_targeted_ub_probe: bool,
}

/// Compute the shrinkable [`FailureSignature`] for `report`, returning `None`
/// if `report` is not a shrinkable failure or if any active leg hit a
/// `ToolError`.
pub fn failure_signature_of(report: &FuzzCaseReport) -> Option<FailureSignature> {
    let admitted_authority_ub = is_admitted_authority_ub(report.category, &report.miri);
    let missed_targeted_ub_probe =
        is_missed_targeted_ub_probe(report.category, &report.miri, &report.evaluation);
    if !is_shrinkable_case(report.category, &report.miri, &report.evaluation)
        || report_has_any_tool_error(report)
    {
        return None;
    }
    let miri_term = report.miri.to_terminal_outcome().ok()?;
    let miri_ub_bucket = match &miri_term {
        TerminalOutcome::UndefinedBehavior { detail } => Some(MiriUbBucket::classify(detail)),
        _ => None,
    };
    let lean_init_unsupported = report.capture_rejected.is_none()
        && matches!(report.lean, ObservedOutcome::InitUnsupported { .. });
    let lean_term = if report.capture_rejected.is_some() {
        None
    } else {
        Some(report.lean.to_terminal_outcome().ok()?)
    };
    let lean_kind = lean_term.as_ref().map(TerminalKindTag::from_terminal);
    let lean_ub_bucket = match &lean_term {
        Some(TerminalOutcome::UndefinedBehavior { detail }) => Some(MiriUbBucket::classify(detail)),
        _ => None,
    };
    let rustc_mismatch =
        if matches!(report.evaluation.rustc_status, RustcCheckStatus::Disagreement { .. }) {
            Some(secondary_mismatch_kind(&miri_term, report.rustc.as_ref()?)?)
        } else {
            None
        };
    let mir_eval_mismatch = match (&lean_term, report.mir_eval.as_ref()) {
        (Some(lt), Some(ev))
            if report.evaluation.agreement == OracleAgreementClass::AuthorityDisagreement
                && !outcomes_agree_mir(&report.lean, ev) =>
        {
            Some(secondary_mismatch_kind(lt, ev)?)
        }
        _ => None,
    };
    Some(FailureSignature {
        agreement: report.evaluation.agreement,
        miri_kind: TerminalKindTag::from_terminal(&miri_term),
        miri_ub_bucket,
        lean_kind,
        lean_ub_bucket,
        lean_init_unsupported,
        rustc_mismatch,
        mir_eval_mismatch,
        is_spurious_lean_ub: report.evaluation.is_spurious_lean_ub,
        admitted_authority_ub,
        missed_targeted_ub_probe,
    })
}

/// Reusable prepared multi-leg session for Stage-2 fuzzing and live shrinking.
pub struct FuzzSession {
    pub rustc: Option<RustcSession>,
    pub miri: MiriSession,
    pub lean: LeanSession,
    pub mir_eval_bin: Option<PathBuf>,
    mir_eval_exec_bin: Option<PathBuf>,
    pub capture_bin_source: String,
    pub capture_bin_sha256: String,
    _capture_staging: Option<Arc<ImmutableStagingDir>>,
    _mir_eval_guard: Option<Arc<ImmutableStagingDir>>,
    _cache_guard: Option<crate::rustc_runner::PinnedPrivateDir>,
    _lean_cache_guard: Option<crate::rustc_runner::PinnedPrivateDir>,
}

fn resolve_private_fuzz_cache_dir(
    prefix: &str,
    tmpdir_env: Option<&std::ffi::OsStr>,
    caller_cwd: &Path,
) -> Result<crate::rustc_runner::PinnedPrivateDir, String> {
    let validated_tmpdir = crate::mir_eval_runner::validate_optional_existing_dir_env(
        tmpdir_env, caller_cwd, "TMPDIR",
    )?;
    crate::rustc_runner::PinnedPrivateDir::create(
        prefix,
        validated_tmpdir.as_deref(),
        caller_cwd,
        "private fuzz cache dir",
    )
}

fn resolve_private_fuzz_lean_cache(
    tmpdir_env: Option<&std::ffi::OsStr>,
    caller_cwd: &Path,
) -> Result<crate::rustc_runner::PinnedPrivateDir, String> {
    resolve_private_fuzz_cache_dir("anneal-fuzz-lean-", tmpdir_env, caller_cwd)
}

impl FuzzSession {
    /// Prepare Miri, Lean `.olean` DAG, optional Leg 0 `rustc`, and optional
    /// Leg 3 `anneal-mir-eval` sessions.
    pub fn prepare(opts: &FuzzOptions) -> Result<Self, String> {
        if opts.mir_eval_bin.is_some() && opts.mir_eval_manifest.is_some() {
            return Err("--mir-eval-bin and --mir-eval-manifest are mutually exclusive".to_owned());
        }
        let anneal_root =
            ToolchainEnv::repo_root_from_manifest(Path::new(env!("CARGO_MANIFEST_DIR")))?;
        let caller_cwd =
            env::current_dir().map_err(|e| format!("resolve current working directory: {e}"))?;
        if opts.cache_root.is_some() {
            let _ = resolve_cache_root(&anneal_root, opts.cache_root.as_deref())?;
        }
        // Isolate both Stage-2 Miri sysroot and Lean DAG compilation from any
        // writable `--cache-root`, `ANNEAL_DIFF_CACHE_DIR`, `CARGO_TARGET_DIR`,
        // or `anneal/target` directory and pin both `0o700` roots by open dir
        // descriptor so parent-dir renames under `TMPDIR` can never spoof Leg 1
        // or Leg 2 setup.
        let ambient_tmpdir = env::var_os("TMPDIR");
        let miri_cache_guard = resolve_private_fuzz_cache_dir(
            "anneal-fuzz-miri-",
            ambient_tmpdir.as_deref(),
            &caller_cwd,
        )?;
        let lean_cache_guard =
            resolve_private_fuzz_lean_cache(ambient_tmpdir.as_deref(), &caller_cwd)?;
        let prepared_tools =
            resolve_toolchain_for_suite(opts.capture_bin.as_deref(), |k| env::var_os(k))?;
        let tools = &prepared_tools.tools;

        let resolved_mir_eval = if let Some(bin) = &opts.mir_eval_bin {
            let prepared = crate::mir_eval_runner::stage_mir_eval_bin_no_links(bin)?;
            Some(prepared)
        } else if let Some(manifest) = &opts.mir_eval_manifest {
            Some(build_mir_eval_from_manifest(manifest)?)
        } else {
            None
        };
        let (resolved_mir_eval, mir_eval_exec_bin, mir_eval_guard) = match resolved_mir_eval {
            Some(prepared) => (Some(prepared.path), Some(prepared.exec_path), prepared._staging),
            None => (None, None, None),
        };

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
            "FuzzSession rustc sysroot",
        )?;

        let rustc = if opts.run_rustc {
            Some(RustcSession::prepare_from_sysroot(prepared_sys.clone(), validated_tmpdir)?)
        } else {
            None
        };

        let miri_sys = prepared_sys.clone();
        let (miri_res, lean_res) = thread::scope(|scope| {
            let m = scope
                .spawn(|| MiriSession::prepare_from_sysroot_pinned(miri_sys, &miri_cache_guard));
            let l = scope.spawn(|| {
                LeanSession::prepare_from_sysroot_pinned(
                    &anneal_root,
                    tools,
                    &lean_cache_guard,
                    prepared_sys,
                )
            });
            (
                m.join().unwrap_or_else(|_| Err("Miri prepare panicked".to_owned())),
                l.join().unwrap_or_else(|_| Err("Lean prepare panicked".to_owned())),
            )
        });
        let miri = miri_res?;
        let lean = lean_res?;
        // Both sessions now pin frozen immutable copies under `_staging` dirs;
        // drop the temporary build caches right away to reduce `/tmp` pressure.
        drop(miri_cache_guard);
        drop(lean_cache_guard);

        Ok(Self {
            rustc,
            miri,
            lean,
            mir_eval_bin: resolved_mir_eval,
            mir_eval_exec_bin,
            capture_bin_source: prepared_tools.capture_bin_source,
            capture_bin_sha256: prepared_tools.capture_bin_sha256,
            _capture_staging: prepared_tools._capture_staging,
            _mir_eval_guard: mir_eval_guard,
            _cache_guard: None,
            _lean_cache_guard: None,
        })
    }

    /// Evaluate a single [`GenProgram`] across all active legs (used by the
    /// shrinker and live oracle self-tests).
    pub fn evaluate_single_program(&self, prog: &GenProgram) -> Result<FuzzCaseReport, String> {
        self.evaluate_single_program_until(prog, None)
    }

    /// Evaluate a single [`GenProgram`] while clamping every external leg's
    /// subprocess timeout to `deadline`.
    pub fn evaluate_single_program_until(
        &self,
        prog: &GenProgram,
        deadline: Option<Instant>,
    ) -> Result<FuzzCaseReport, String> {
        let mut reports = self.evaluate_batch_until(std::slice::from_ref(prog), 0, deadline)?;
        reports.pop().ok_or_else(|| format!("missing evaluation result for {}", prog.case_id))
    }

    /// Evaluate a batch of programs across Leg 1 (`miri`) and Leg 2
    /// (`anneal-rustc-capture` + Lean `#eval`) first, then invoke Leg 0
    /// (`rustc`) exclusively on Miri-confirmed UB-free cases and optional Leg 3
    /// (`anneal-mir-eval`).
    pub fn evaluate_batch(
        &self,
        programs: &[GenProgram],
        batch_idx: usize,
    ) -> Result<Vec<FuzzCaseReport>, String> {
        self.evaluate_batch_until(programs, batch_idx, None)
    }

    /// Deadline-clamped variant of [`Self::evaluate_batch`] used during
    /// counterexample shrinking so stalled external legs respect the shrink
    /// wall-clock budget.
    pub fn evaluate_batch_until(
        &self,
        programs: &[GenProgram],
        batch_idx: usize,
        deadline: Option<Instant>,
    ) -> Result<Vec<FuzzCaseReport>, String> {
        let mut leg3_global_failure = None;
        self.evaluate_batch_with_leg3_guard(programs, batch_idx, deadline, &mut leg3_global_failure)
    }

    fn evaluate_batch_with_leg3_guard(
        &self,
        programs: &[GenProgram],
        batch_idx: usize,
        deadline: Option<Instant>,
        leg3_global_failure: &mut Option<String>,
    ) -> Result<Vec<FuzzCaseReport>, String> {
        let mut rustc_missing = Vec::new();
        self.evaluate_batch_with_guards(
            programs,
            batch_idx,
            deadline,
            leg3_global_failure,
            &mut rustc_missing,
        )
    }

    fn evaluate_batch_with_guards(
        &self,
        programs: &[GenProgram],
        batch_idx: usize,
        deadline: Option<Instant>,
        leg3_global_failure: &mut Option<String>,
        rustc_missing_cases: &mut Vec<String>,
    ) -> Result<Vec<FuzzCaseReport>, String> {
        if programs.is_empty() {
            return Ok(Vec::new());
        }
        if deadline.is_some_and(|dl| Instant::now() >= dl) {
            return Err("shrink wall-clock deadline exhausted before oracle evaluation".to_owned());
        }
        let prog_refs: Vec<&GenProgram> = programs.iter().collect();
        let batch_src = render_batch_crate(&prog_refs);
        let exec_cases: Vec<FuzzExecCase> = programs
            .iter()
            .map(|p| FuzzExecCase {
                case_id: p.case_id.clone(),
                fn_name: p.fn_name.clone(),
                args: p.args(),
                ret_shape: p.ret_shape(),
                fuel: p.fuel,
                expected_clean_batch: p.category.counts_toward_admission(),
            })
            .collect();

        let lean_work = crate::mir_eval_runner::build_temp_dir(
            "anneal-lean-fuzz-",
            self.lean.validated_tmpdir.as_deref(),
        )?;
        let crate_name = format!("fuzz_batch_{batch_idx}");

        let refs = &prog_refs;
        let (miri_res, lean_res) = thread::scope(|scope| {
            let m_handle = {
                let src = &batch_src;
                let cases = &exec_cases;
                scope.spawn(move || {
                    self.miri.run_fuzz_crate_with_evidence_until(src, refs, cases, deadline)
                })
            };
            let l_handle = {
                let dir = lean_work.path();
                let cname = &crate_name;
                scope.spawn(move || {
                    self.lean.capture_and_evaluate_fuzz_batch_until(dir, cname, refs, deadline)
                })
            };

            let m_out = m_handle.join().unwrap_or_else(|_| Err("Miri batch panicked".to_owned()));
            let l_out = l_handle.join().unwrap_or_else(|_| Err("Lean batch panicked".to_owned()));
            (m_out, l_out)
        });

        let miri_map = miri_res?;
        let lean_map = lean_res?;

        // Run native host `rustc` (Leg 0) ONLY on cases Miri confirmed UB-free
        // so known-UB probes or accidental generator UB never run natively on
        // the host.
        let mut ub_free_progs = Vec::new();
        let mut ub_free_cases = Vec::new();
        let mut ub_free_ids: BTreeSet<&str> = BTreeSet::new();
        for (&prog, ec) in prog_refs.iter().zip(&exec_cases) {
            if miri_map.get(&ec.case_id).is_some_and(|(out, _)| is_miri_ub_free_outcome(out)) {
                ub_free_progs.push(prog);
                ub_free_cases.push(ec.clone());
                ub_free_ids.insert(prog.case_id.as_str());
            }
        }
        let rustc_map = if let Some(session) = &self.rustc {
            if ub_free_progs.is_empty() {
                Some(BTreeMap::new())
            } else {
                let ub_free_src = render_batch_crate(&ub_free_progs);
                Some(session.run_batch_crate_with_evidence_until(
                    &ub_free_src,
                    &ub_free_progs,
                    &ub_free_cases,
                    deadline,
                )?)
            }
        } else {
            None
        };

        let leg3_deadline = match deadline {
            Some(dl) => Some(dl),
            None => Some(Instant::now() + Duration::from_secs(MIR_EVAL_BATCH_BUDGET_SECS)),
        };
        let mut reports = Vec::with_capacity(programs.len());
        for prog in programs {
            let (rustc, rustc_evidence, rustc_missing) =
                if ub_free_ids.contains(prog.case_id.as_str()) {
                    resolve_rustc_case_outcome(rustc_map.as_ref(), &prog.case_id)
                } else {
                    (None, None, false)
                };
            if rustc_missing {
                rustc_missing_cases.push(prog.case_id.clone());
            }
            let (miri, miri_evidence) = miri_map.get(&prog.case_id).cloned().unwrap_or_else(|| {
                (
                    ObservedOutcome::ToolError {
                        detail: format!("missing Miri outcome for {}", prog.case_id),
                    },
                    None,
                )
            });
            let lean_entry =
                lean_map.get(&prog.case_id).cloned().unwrap_or_else(|| FuzzLeanCaseResult {
                    outcome: ObservedOutcome::ToolError {
                        detail: format!("missing Lean outcome for {}", prog.case_id),
                    },
                    capture_rejected: None,
                    capture_refusal_json: None,
                    capture_json: None,
                    capture_body: None,
                    lean_probe_line: None,
                    exercised_move_reinit: false,
                    move_reinit_evidence: None,
                });

            let (mir_eval, mir_eval_evidence) =
                if self.mir_eval_exec_bin.is_some() || self.mir_eval_bin.is_some() {
                    if lean_entry.capture_rejected.is_some() {
                        (None, None)
                    } else if let (Some(cap_json), Some(cb)) =
                        (&lean_entry.capture_json, lean_entry.capture_body.as_ref())
                    {
                        let args = prog.args();
                        let (outcome, ev) =
                            eval_leg3_with_evidence_short_circuit(leg3_global_failure, || {
                                if let Some(exec_bin) = self.mir_eval_exec_bin.as_deref() {
                                    run_pinned_mir_eval_raw_with_evidence(
                                        exec_bin,
                                        cap_json,
                                        (cb.body_id, &cb.fn_identity),
                                        &args,
                                        prog.fuel,
                                        leg3_deadline,
                                    )
                                } else {
                                    let eval_bin = self
                                        .mir_eval_bin
                                        .as_deref()
                                        .expect("checked mir_eval_bin is Some above");
                                    run_mir_eval_raw_with_evidence(
                                        eval_bin,
                                        cap_json,
                                        (cb.body_id, &cb.fn_identity),
                                        &args,
                                        prog.fuel,
                                        leg3_deadline,
                                    )
                                }
                            });
                        (Some(outcome), ev)
                    } else {
                        (
                            Some(ObservedOutcome::ToolError {
                                detail: format!("missing capture metadata for {}", prog.case_id),
                            }),
                            None,
                        )
                    }
                } else {
                    (None, None)
                };
            let (mir_eval_body_id, mir_eval_raw_json) = match mir_eval_evidence {
                Some((bid, raw_json)) => (Some(bid), Some(raw_json)),
                None => (None, None),
            };
            let capture_refusal_json = if lean_entry.capture_rejected.is_some() {
                lean_entry.capture_refusal_json
            } else {
                None
            };
            let leg_evidence = if lean_entry.lean_probe_line.is_some()
                || capture_refusal_json.is_some()
                || miri_evidence.is_some()
                || rustc_evidence.is_some()
                || mir_eval_raw_json.is_some()
            {
                Some(FuzzLegEvidence {
                    lean_probe_line: lean_entry.lean_probe_line,
                    capture_refusal_json,
                    miri_evidence,
                    rustc_evidence,
                    mir_eval_body_id,
                    mir_eval_raw_json,
                })
            } else {
                None
            };

            let evaluation = evaluate_fuzz_case_with_rustc_leg(
                &miri,
                &lean_entry.outcome,
                rustc.as_ref(),
                mir_eval.as_ref(),
                lean_entry.capture_rejected.as_deref(),
                self.rustc.is_some(),
            );
            let retain_source = is_shrinkable_case(prog.category, &miri, &evaluation);
            let source = if retain_source { Some(prog.render_standalone()) } else { None };

            let (exercised_move_reinit, move_reinit_evidence) = if lean_entry.exercised_move_reinit
                && evaluation.agreement == OracleAgreementClass::BiFaultEquivAgreement
                && !matches!(miri, ObservedOutcome::UndefinedBehavior { .. })
                && let Some(ev) = lean_entry.move_reinit_evidence
            {
                (true, Some(ev))
            } else {
                (false, None)
            };

            reports.push(FuzzCaseReport {
                case_id: prog.case_id.clone(),
                fn_name: prog.fn_name.clone(),
                master_seed: prog.master_seed,
                case_index: prog.case_index,
                category: prog.category,
                args: prog.args(),
                program_sha256: prog.program_sha256(),
                fuel: prog.fuel,
                capture_body: lean_entry.capture_body,
                rustc,
                miri,
                lean: lean_entry.outcome,
                mir_eval,
                capture_rejected: lean_entry.capture_rejected,
                leg_evidence,
                exercised_move_reinit,
                move_reinit_evidence,
                evaluation,
                source,
                shrink_trace: None,
                shrink_verification: None,
            });
        }
        Ok(reports)
    }
}

fn is_miri_ub_free_outcome(outcome: &ObservedOutcome) -> bool {
    matches!(
        outcome,
        ObservedOutcome::Returned { .. }
            | ObservedOutcome::Panic { .. }
            | ObservedOutcome::Unwound { .. }
            | ObservedOutcome::AbnormalAbort { .. }
    )
}

fn resolve_rustc_case_outcome(
    rustc_map: Option<&BTreeMap<String, (ObservedOutcome, Option<String>)>>,
    case_id: &str,
) -> (Option<ObservedOutcome>, Option<String>, bool) {
    let Some(map) = rustc_map else {
        return (None, None, false);
    };
    match map.get(case_id).cloned() {
        Some((out, ev)) => (Some(out), ev, false),
        None => (
            Some(ObservedOutcome::ToolError {
                detail: format!("missing rustc outcome for {case_id}"),
            }),
            None,
            true,
        ),
    }
}

fn eval_leg3_with_evidence_short_circuit<T, F>(
    global_failure: &mut Option<String>,
    run_once: F,
) -> (ObservedOutcome, Option<T>)
where
    F: FnOnce() -> (ObservedOutcome, Option<T>, bool),
{
    if let Some(detail) = global_failure.as_ref() {
        return (ObservedOutcome::ToolError { detail: detail.clone() }, None);
    }
    let (outcome, evidence, is_global) = run_once();
    if is_global && let ObservedOutcome::ToolError { detail } = &outcome {
        *global_failure = Some(detail.clone());
    }
    (outcome, evidence)
}

#[cfg(test)]
fn eval_leg3_with_short_circuit<F>(
    global_failure: &mut Option<String>,
    run_once: F,
) -> ObservedOutcome
where
    F: FnOnce() -> (ObservedOutcome, bool),
{
    eval_leg3_with_evidence_short_circuit(global_failure, || {
        let (outcome, is_global) = run_once();
        (outcome, None::<()>, is_global)
    })
    .0
}

/// Validate [`FuzzOptions`] and generator bounds before preparing external
/// toolchains or writing `--out` files.
pub fn validate_fuzz_options(opts: &FuzzOptions) -> Result<GenConfig, String> {
    if opts.run_rustc {
        crate::rustc_runner::ensure_64_bit_host(usize::BITS)?;
    }
    if opts.cases == 0 {
        return Err("fuzz campaign requires `--cases >= 1`".to_owned());
    }
    if opts.mir_eval_bin.is_some() && opts.mir_eval_manifest.is_some() {
        return Err("--mir-eval-bin and --mir-eval-manifest are mutually exclusive".to_owned());
    }
    if !opts.min_admission_rate.is_finite() || !(0.0..=1.0).contains(&opts.min_admission_rate) {
        return Err(format!(
            "`--min-admission-rate` must be in 0.0..=1.0, got {}",
            opts.min_admission_rate
        ));
    }
    let gen_cfg = GenConfig {
        master_seed: opts.seed,
        max_stmts: opts.max_stmts,
        ub_ratio: opts.ub_ratio,
        default_fuel: opts.fuel,
    };
    gen_cfg.validate()?;
    Ok(gen_cfg)
}

/// Run a full Stage-2 seeded generative differential fuzz campaign.
pub fn run_fuzz_campaign(opts: &FuzzOptions) -> Result<FuzzReport, String> {
    let gen_cfg = validate_fuzz_options(opts)?;

    let start = Instant::now();
    let session = FuzzSession::prepare(opts)?;
    let programs = generate_campaign(&gen_cfg, opts.cases);

    let mut all_reports = Vec::with_capacity(programs.len());
    let mut leg3_global_failure: Option<String> = None;
    let mut rustc_missing_cases: Vec<String> = Vec::new();
    let mut shrink_campaign_deadline: Option<Instant> = None;
    for (batch_idx, chunk) in programs.chunks(FUZZ_BATCH_SIZE).enumerate() {
        let mut batch_reports = session.evaluate_batch_with_guards(
            chunk,
            batch_idx,
            None,
            &mut leg3_global_failure,
            &mut rustc_missing_cases,
        )?;
        if opts.shrink && leg3_global_failure.is_none() {
            for (prog, report) in chunk.iter().zip(batch_reports.iter_mut()) {
                if let Some(target_sig) = failure_signature_of(report) {
                    let camp_dl = *shrink_campaign_deadline.get_or_insert_with(|| {
                        Instant::now() + Duration::from_secs(SHRINK_CAMPAIGN_BUDGET_SECS)
                    });
                    let rem_secs = camp_dl.saturating_duration_since(Instant::now()).as_secs();
                    if rem_secs == 0 {
                        break;
                    }
                    let mut clamped_cfg = opts.shrink_config.clone();
                    clamped_cfg.max_duration_secs = clamped_cfg.max_duration_secs.min(rem_secs);
                    let mut preserved_reports: BTreeMap<(String, String), FuzzCaseReport> =
                        BTreeMap::new();
                    let (min_prog, mut trace) =
                        shrink_program_with_deadline(prog, &clamped_cfg, |cand, deadline| {
                            let Ok(r) = session.evaluate_single_program_until(cand, Some(deadline))
                            else {
                                return ShrinkOutcome::Inconclusive;
                            };
                            if report_has_any_tool_error(&r) {
                                return ShrinkOutcome::Inconclusive;
                            }
                            if failure_signature_of(&r).as_ref() == Some(&target_sig) {
                                let args_key =
                                    serde_json::to_string(&cand.args()).unwrap_or_default();
                                preserved_reports.insert((cand.program_sha256(), args_key), r);
                                ShrinkOutcome::Preserved
                            } else {
                                ShrinkOutcome::NotPreserved
                            }
                        });
                    let min_args_key = serde_json::to_string(&min_prog.args()).unwrap_or_default();
                    let shrink_verification = preserved_reports
                        .remove(&(min_prog.program_sha256(), min_args_key))
                        .filter(|min_rep| {
                            failure_signature_of(min_rep).as_ref() == Some(&target_sig)
                        })
                        .map(|min_rep| {
                            Box::new(FuzzMinimizedVerification::from_case_report(min_rep))
                        });
                    if shrink_verification.is_none() {
                        trace.converged_1_minimal = false;
                    }
                    report.shrink_trace = Some(trace);
                    report.shrink_verification = shrink_verification;
                }
            }
        }
        all_reports.extend(batch_reports);
    }

    let wall_clock_sec = start.elapsed().as_secs_f64();
    let metrics = compute_fuzz_metrics(&all_reports, wall_clock_sec);
    let gate_error =
        check_fuzz_gates(&metrics, opts.min_admission_rate, opts.ub_ratio, opts.max_stmts).or_else(
            || {
                (!rustc_missing_cases.is_empty()).then(|| {
                    format!(
                        "incomplete rustc runner output: missing outcomes for {}",
                        rustc_missing_cases.join(", ")
                    )
                })
            },
        );

    let mut legs = Vec::new();
    if opts.run_rustc {
        legs.push("rustc_compiled".to_owned());
    }
    legs.push("miri".to_owned());
    legs.push("lean_step_core_captured".to_owned());
    if session.mir_eval_bin.is_some() {
        legs.push("anneal_mir_eval_captured".to_owned());
    }

    Ok(FuzzReport {
        schema: "anneal-differential-fuzz/v1".to_owned(),
        alpha_notice: ALPHA_NOTICE.to_owned(),
        mir_dialect: "profile_v1".to_owned(),
        seed: opts.seed,
        max_stmts: opts.max_stmts,
        ub_ratio: opts.ub_ratio,
        fuel: opts.fuel,
        capture_bin_source: session.capture_bin_source,
        capture_bin_sha256: session.capture_bin_sha256,
        prebuilt_overlay: session.lean.prebuilt_overlay,
        legs,
        min_admission_rate: opts.min_admission_rate,
        metrics,
        gate_error,
        cases: all_reports,
    })
}

fn compute_fuzz_metrics(cases: &[FuzzCaseReport], wall_clock_sec: f64) -> FuzzMetrics {
    let mut m = FuzzMetrics {
        total_cases: cases.len(),
        safe_admitted_cases: 0,
        boundary_edge_cases: 0,
        targeted_ub_probes: 0,
        scope_control_cases: 0,
        admission_eligible_cases: 0,
        admitted_cases: 0,
        admission_rate: 0.0,
        bi_fault_equiv_count: 0,
        ub_probes_agreed_count: 0,
        conservative_over_approx_count: 0,
        spurious_lean_ub_count: 0,
        admitted_authority_ub_count: 0,
        unsound_accept_count: 0,
        authority_disagreement_count: 0,
        move_reinit_exercised_count: 0,
        disclosed_gaps: BTreeMap::new(),
        rustc_agreed_count: 0,
        rustc_ignored_ub_count: 0,
        rustc_disagreement_count: 0,
        wall_clock_sec,
    };

    for c in cases {
        match c.category {
            GenCategory::SafeAdmitted => m.safe_admitted_cases += 1,
            GenCategory::BoundaryEdgeCase => m.boundary_edge_cases += 1,
            GenCategory::TargetedUbProbe => m.targeted_ub_probes += 1,
            GenCategory::ScopeControl => m.scope_control_cases += 1,
        }
        if c.exercised_move_reinit && c.move_reinit_evidence.is_some() {
            m.move_reinit_exercised_count += 1;
        }
        if c.evaluation.is_spurious_lean_ub {
            m.spurious_lean_ub_count += 1;
        }
        if c.category.counts_toward_admission() {
            m.admission_eligible_cases += 1;
            if matches!(c.miri, ObservedOutcome::UndefinedBehavior { .. }) {
                m.admitted_authority_ub_count += 1;
            } else if c.capture_rejected.is_none()
                && matches!(c.miri, ObservedOutcome::Returned { .. })
                && c.evaluation.agreement == OracleAgreementClass::BiFaultEquivAgreement
            {
                m.admitted_cases += 1;
            }
        }
        match c.evaluation.agreement {
            OracleAgreementClass::BiFaultEquivAgreement => {
                m.bi_fault_equiv_count += 1;
                if c.category == GenCategory::TargetedUbProbe
                    && matches!(c.miri, ObservedOutcome::UndefinedBehavior { .. })
                {
                    m.ub_probes_agreed_count += 1;
                }
            }
            OracleAgreementClass::ConservativeOverApproxForwardSimOnly => {
                if !c.evaluation.is_spurious_lean_ub {
                    m.conservative_over_approx_count += 1;
                }
            }
            OracleAgreementClass::UnsoundAcceptCritical => {
                m.unsound_accept_count += 1;
            }
            OracleAgreementClass::AuthorityDisagreement => {
                m.authority_disagreement_count += 1;
            }
        }
        if let Some(gap) = c.evaluation.disclosed_gap {
            *m.disclosed_gaps.entry(gap.as_str().to_owned()).or_insert(0) += 1;
        }
        match c.evaluation.rustc_status {
            RustcCheckStatus::Agreed => m.rustc_agreed_count += 1,
            RustcCheckStatus::IgnoredDueToMiriUb => m.rustc_ignored_ub_count += 1,
            RustcCheckStatus::Disagreement { .. } => m.rustc_disagreement_count += 1,
            RustcCheckStatus::NotRun => {}
        }
    }

    m.admission_rate = if m.admission_eligible_cases == 0 {
        0.0
    } else {
        (m.admitted_cases as f64) / (m.admission_eligible_cases as f64)
    };
    m
}

fn check_fuzz_gates(
    m: &FuzzMetrics,
    min_admission_rate: f64,
    ub_ratio: f64,
    max_stmts: usize,
) -> Option<String> {
    if m.unsound_accept_count > 0 {
        return Some(format!(
            "P0 soundness failure: {} UnsoundAcceptCritical case(s) detected",
            m.unsound_accept_count
        ));
    }
    if m.authority_disagreement_count > 0 {
        return Some(format!(
            "authority failure: {} AuthorityDisagreement case(s) detected",
            m.authority_disagreement_count
        ));
    }
    if m.spurious_lean_ub_count > 0 {
        return Some(format!(
            "spurious Lean UB failure: {} case(s) reported Lean UB on UB-free authority execution",
            m.spurious_lean_ub_count
        ));
    }
    if m.admitted_authority_ub_count > 0 {
        return Some(format!(
            "generator safety invariant failure: {} SafeAdmitted/BoundaryEdgeCase case(s) triggered Miri UB",
            m.admitted_authority_ub_count
        ));
    }
    if m.admission_eligible_cases == 0 {
        return Some("vacuous fuzz campaign: zero SafeAdmitted/BoundaryEdgeCase cases".to_owned());
    }
    if m.admission_rate < min_admission_rate {
        return Some(format!(
            "admission rate {:.1}% ({}/{}) fell below non-vacuity floor {:.1}%",
            m.admission_rate * 100.0,
            m.admitted_cases,
            m.admission_eligible_cases,
            min_admission_rate * 100.0
        ));
    }
    if m.bi_fault_equiv_count == 0 {
        return Some("vacuous fuzz campaign: zero BiFaultEquivAgreement cases".to_owned());
    }
    if ub_ratio > 0.0 && m.total_cases >= 3 && m.targeted_ub_probes == 0 {
        return Some(
            "vacuous UB fuzzing: zero TargetedUbProbe cases generated for positive ub_ratio"
                .to_owned(),
        );
    }
    if m.targeted_ub_probes > 0 && m.ub_probes_agreed_count != m.targeted_ub_probes {
        return Some(format!(
            "targeted UB coverage failure: only {}/{} TargetedUbProbe cases agreed on UB",
            m.ub_probes_agreed_count, m.targeted_ub_probes
        ));
    }
    if max_stmts >= 4 && m.total_cases >= 16 && m.move_reinit_exercised_count == 0 {
        return Some(
            "vacuous move-reinit fuzzing: zero captured bodies exercised non-Copy Operand::Move + reinit"
                .to_owned(),
        );
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::verdict::{IntKind, evaluate_fuzz_case};

    fn make_case(
        category: GenCategory,
        miri: ObservedOutcome,
        lean: ObservedOutcome,
        rustc: Option<ObservedOutcome>,
    ) -> FuzzCaseReport {
        let evaluation = evaluate_fuzz_case(&miri, &lean, rustc.as_ref(), None, None);
        FuzzCaseReport {
            case_id: "c".to_owned(),
            fn_name: "f".to_owned(),
            master_seed: 1,
            case_index: 0,
            category,
            args: vec![],
            program_sha256: "0".repeat(64),
            fuel: 1_500,
            capture_body: None,
            rustc,
            miri,
            lean,
            mir_eval: None,
            capture_rejected: None,
            leg_evidence: None,
            exercised_move_reinit: false,
            move_reinit_evidence: None,
            evaluation,
            source: None,
            shrink_trace: None,
            shrink_verification: None,
        }
    }

    #[test]
    fn failure_signature_rejects_tool_errors_and_separates_mismatch_modes() {
        let ret_7 =
            ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 7 } };
        let ret_8 =
            ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 8 } };
        let ub_div0 = ObservedOutcome::UndefinedBehavior {
            detail: "Undefined Behavior: dividing by zero".to_owned(),
        };
        let ub_min_ovf = ObservedOutcome::UndefinedBehavior {
            detail: "Undefined Behavior: overflow in signed remainder".to_owned(),
        };
        let tool_err = ObservedOutcome::ToolError { detail: "timeout".to_owned() };

        let mut val_mis =
            make_case(GenCategory::SafeAdmitted, ret_7.clone(), ret_8.clone(), Some(ret_7.clone()));
        // Differing UB/Unwound/Unsupported detail strings between Lean and
        // `anneal-mir-eval` must NOT set `mir_eval_mismatch`.
        val_mis.lean = ObservedOutcome::Unwound { detail: "TerminalOut.unwound".to_owned() };
        val_mis.mir_eval =
            Some(ObservedOutcome::Unwound { detail: "mir_eval::unwound".to_owned() });
        val_mis.evaluation = evaluate_fuzz_case(
            &val_mis.miri,
            &val_mis.lean,
            val_mis.rustc.as_ref(),
            val_mis.mir_eval.as_ref(),
            None,
        );

        let missed_div0 = make_case(
            GenCategory::TargetedUbProbe,
            ub_div0.clone(),
            ret_7.clone(),
            Some(ret_7.clone()),
        );
        let missed_ovf =
            make_case(GenCategory::TargetedUbProbe, ub_min_ovf, ret_7.clone(), Some(ret_7.clone()));
        let spurious_ub = make_case(
            GenCategory::SafeAdmitted,
            ret_7.clone(),
            ub_div0.clone(),
            Some(ret_7.clone()),
        );
        let miri_tool_fail = make_case(GenCategory::SafeAdmitted, tool_err, ret_7.clone(), None);

        let sig_val = failure_signature_of(&val_mis).expect("spurious unwind signature");
        assert!(
            sig_val.mir_eval_mismatch.is_none(),
            "matching Unwound legs must agree despite detail text"
        );
        let sig_div0 = failure_signature_of(&missed_div0).expect("missed div0 UB signature");
        let sig_ovf = failure_signature_of(&missed_ovf).expect("missed signed overflow signature");
        let sig_spur = failure_signature_of(&spurious_ub).expect("spurious UB signature");
        assert_ne!(sig_val, sig_div0, "value/unwind mismatch must never shrink to missed UB");
        assert_ne!(
            sig_div0, sig_ovf,
            "signed overflow UB must not drift into division-by-zero UB during shrinking"
        );
        assert_ne!(sig_val, sig_spur);
        assert!(
            failure_signature_of(&miri_tool_fail).is_none(),
            "ToolError must never match a shrink signature"
        );

        // When Miri hits UB, a host `rustc` timeout/trap (`ToolError` masked as
        // `IgnoredDueToMiriUb`) must still yield a shrinkable UB signature.
        let ub_with_rustc_hang = make_case(
            GenCategory::TargetedUbProbe,
            ub_div0,
            ret_7,
            Some(ObservedOutcome::ToolError { detail: "host UB timed out".to_owned() }),
        );
        assert!(
            failure_signature_of(&ub_with_rustc_hang).is_some(),
            "ignored rustc ToolError on Miri UB must remain shrinkable"
        );
    }

    #[test]
    fn failure_signature_preserves_secondary_leg_mismatch_subtypes() {
        let ret_7 =
            ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 7 } };
        let ret_8 =
            ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 8 } };
        let panic_out = ObservedOutcome::Panic { detail: "panicked at shrink probe".to_owned() };
        let abort_out = ObservedOutcome::AbnormalAbort { detail: "SIGABRT".to_owned() };

        // Leg 0 (`rustc`) compiled-value mismatch must stay distinct from
        // compiled panic/unwind and compiled abort while Miri and Lean return.
        let rustc_val_mis =
            make_case(GenCategory::SafeAdmitted, ret_7.clone(), ret_7.clone(), Some(ret_8.clone()));
        let rustc_panic_mis = make_case(
            GenCategory::SafeAdmitted,
            ret_7.clone(),
            ret_7.clone(),
            Some(panic_out.clone()),
        );
        let rustc_abort_mis = make_case(
            GenCategory::SafeAdmitted,
            ret_7.clone(),
            ret_7.clone(),
            Some(abort_out.clone()),
        );
        let sig_rustc_val =
            failure_signature_of(&rustc_val_mis).expect("rustc value mismatch signature");
        let sig_rustc_panic =
            failure_signature_of(&rustc_panic_mis).expect("rustc panic mismatch signature");
        let sig_rustc_abort =
            failure_signature_of(&rustc_abort_mis).expect("rustc abort mismatch signature");
        assert_eq!(sig_rustc_val.rustc_mismatch, Some(SecondaryMismatchKind::ReturnedValue));
        assert_ne!(sig_rustc_val, sig_rustc_panic);
        assert_ne!(sig_rustc_val, sig_rustc_abort);
        assert_ne!(sig_rustc_panic, sig_rustc_abort);

        // Leg 3 (`anneal-mir-eval`) return-value mismatch, unwind, UB buckets,
        // step-time unsupported, init-unsupported, and out-of-fuel must all
        // yield pairwise-distinct shrink signatures.
        let make_mir_eval_case = |ev: ObservedOutcome| {
            let mut c = make_case(
                GenCategory::SafeAdmitted,
                ret_7.clone(),
                ret_7.clone(),
                Some(ret_7.clone()),
            );
            c.evaluation = evaluate_fuzz_case(&c.miri, &c.lean, c.rustc.as_ref(), Some(&ev), None);
            c.mir_eval = Some(ev);
            failure_signature_of(&c).expect("mir_eval mismatch must be shrinkable")
        };
        let mir_eval_sigs = [
            make_mir_eval_case(ret_8),
            make_mir_eval_case(panic_out),
            make_mir_eval_case(abort_out),
            make_mir_eval_case(ObservedOutcome::UndefinedBehavior {
                detail: "dividing by zero".to_owned(),
            }),
            make_mir_eval_case(ObservedOutcome::UndefinedBehavior {
                detail: "overflow in signed remainder".to_owned(),
            }),
            make_mir_eval_case(ObservedOutcome::Unsupported { detail: "unsupported".to_owned() }),
            make_mir_eval_case(ObservedOutcome::InitUnsupported { detail: "init".to_owned() }),
            make_mir_eval_case(ObservedOutcome::OutOfFuel { detail: "fuel".to_owned() }),
        ];
        assert_eq!(mir_eval_sigs[0].mir_eval_mismatch, Some(SecondaryMismatchKind::ReturnedValue));
        for i in 0..mir_eval_sigs.len() {
            for j in (i + 1)..mir_eval_sigs.len() {
                assert_ne!(
                    mir_eval_sigs[i], mir_eval_sigs[j],
                    "mir_eval mismatch subtype {i} and {j} collided"
                );
            }
        }

        // Spurious Lean UB failures preserve normalized `lean_ub_bucket` so an
        // oversized-shift false positive cannot shrink into division-by-zero,
        // and primary `UnsoundAcceptCritical` cases ignore secondary Leg-3
        // `mir_eval` UB buckets in `FailureSignature`.
        let ret_val =
            ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 7 } };
        let spurious_shift = make_case(
            GenCategory::SafeAdmitted,
            ret_val.clone(),
            ObservedOutcome::UndefinedBehavior { detail: "overflowing shift".to_owned() },
            Some(ret_val.clone()),
        );
        let spurious_div0 = make_case(
            GenCategory::SafeAdmitted,
            ret_val.clone(),
            ObservedOutcome::UndefinedBehavior { detail: "dividing by zero".to_owned() },
            Some(ret_val.clone()),
        );
        let sig_shift = failure_signature_of(&spurious_shift).unwrap();
        let sig_div0 = failure_signature_of(&spurious_div0).unwrap();
        assert_eq!(sig_shift.lean_ub_bucket, Some(MiriUbBucket::OversizedShift));
        assert_eq!(sig_div0.lean_ub_bucket, Some(MiriUbBucket::DivisionByZero));
        assert_ne!(sig_shift, sig_div0);

        let mut primary_unsound_with_leg3 = make_case(
            GenCategory::TargetedUbProbe,
            ObservedOutcome::UndefinedBehavior { detail: "dividing by zero".to_owned() },
            ret_val.clone(),
            Some(ret_val.clone()),
        );
        let leg3_ub = ObservedOutcome::UndefinedBehavior { detail: "dividing by zero".to_owned() };
        primary_unsound_with_leg3.evaluation = evaluate_fuzz_case(
            &primary_unsound_with_leg3.miri,
            &primary_unsound_with_leg3.lean,
            primary_unsound_with_leg3.rustc.as_ref(),
            Some(&leg3_ub),
            None,
        );
        primary_unsound_with_leg3.mir_eval = Some(leg3_ub);
        let sig_primary = failure_signature_of(&primary_unsound_with_leg3).unwrap();
        assert_eq!(sig_primary.agreement, OracleAgreementClass::UnsoundAcceptCritical);
        assert_eq!(sig_primary.mir_eval_mismatch, None);
    }

    #[test]
    fn spurious_lean_ub_and_admitted_authority_ub_fail_zero_tolerance_gates() {
        let ret_1 =
            ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 1 } };
        let ub = ObservedOutcome::UndefinedBehavior { detail: "dividing by zero".to_owned() };
        let ok_case =
            make_case(GenCategory::SafeAdmitted, ret_1.clone(), ret_1.clone(), Some(ret_1.clone()));
        let bad_spurious =
            make_case(GenCategory::SafeAdmitted, ret_1.clone(), ub.clone(), Some(ret_1.clone()));

        let m = compute_fuzz_metrics(&[ok_case.clone(), bad_spurious], 1.0);
        assert_eq!(m.admission_eligible_cases, 2);
        assert_eq!(m.admitted_cases, 1, "spurious Lean UB must not count as admitted");
        assert_eq!(m.spurious_lean_ub_count, 1);
        assert_eq!(
            m.conservative_over_approx_count, 0,
            "spurious Lean UB must not inflate conservative_over_approx_count"
        );
        assert!(m.disclosed_gaps.is_empty());
        let gate = check_fuzz_gates(&m, 0.50, 0.0, 6);
        assert!(
            gate.as_deref().is_some_and(|g| g.contains("spurious Lean UB")),
            "expected zero-tolerance spurious Lean UB gate failure, got {gate:?}"
        );

        // A SafeAdmitted or BoundaryEdgeCase program that triggers Miri UB must
        // NOT count as admitted even if Lean also reports UB, and must fail
        // `admitted_authority_ub_count == 0`.
        let accidental_ub =
            make_case(GenCategory::SafeAdmitted, ub.clone(), ub.clone(), Some(ret_1.clone()));
        let m_ub = compute_fuzz_metrics(&[ok_case, accidental_ub], 1.0);
        assert_eq!(m_ub.admission_eligible_cases, 2);
        assert_eq!(m_ub.admitted_cases, 1, "accidental Miri UB on SafeAdmitted is not admitted");
        assert_eq!(m_ub.admitted_authority_ub_count, 1);
        let ub_gate = check_fuzz_gates(&m_ub, 0.50, 0.0, 6);
        assert!(
            ub_gate.as_deref().is_some_and(|g| g.contains("SafeAdmitted/BoundaryEdgeCase")),
            "expected admitted_authority_ub_count gate failure, got {ub_gate:?}"
        );

        // Sub-percent positive `ub_ratio` (e.g. `0.001`) generates a real
        // `TargetedUbProbe` on `cases >= 3` and passes `check_fuzz_gates`; tiny
        // 1-2 case runs before slot 2 also stay non-vacuous without failing.
        let sub_cfg = GenConfig {
            master_seed: 20_261_124,
            max_stmts: 4,
            ub_ratio: 0.001,
            default_fuel: 1_500,
        };
        let sub_progs = generate_campaign(&sub_cfg, 8);
        let sub_reports: Vec<FuzzCaseReport> = sub_progs
            .iter()
            .map(|p| {
                if p.category == GenCategory::TargetedUbProbe {
                    let u = ObservedOutcome::UndefinedBehavior {
                        detail: "dividing by zero".to_owned(),
                    };
                    make_case(p.category, u.clone(), u, Some(ret_1.clone()))
                } else {
                    make_case(p.category, ret_1.clone(), ret_1.clone(), Some(ret_1.clone()))
                }
            })
            .collect();
        let m_sub = compute_fuzz_metrics(&sub_reports, 1.0);
        assert!(m_sub.targeted_ub_probes >= 1);
        assert_eq!(check_fuzz_gates(&m_sub, 0.90, 0.001, 4), None);

        let m_two = compute_fuzz_metrics(&sub_reports[..2], 1.0);
        assert_eq!(m_two.targeted_ub_probes, 0);
        assert_eq!(check_fuzz_gates(&m_two, 0.90, 0.001, 4), None);

        // If any TargetedUbProbe stops producing UB (even when both legs
        // agree on returning a value), both `check_fuzz_gates` and
        // `FuzzReport::is_passing` must fail closed.
        let ub_agreed =
            make_case(GenCategory::TargetedUbProbe, ub.clone(), ub, Some(ret_1.clone()));
        let broken_ub_probe = make_case(
            GenCategory::TargetedUbProbe,
            ret_1.clone(),
            ret_1.clone(),
            Some(ret_1.clone()),
        );
        let partial_cases = vec![
            make_case(GenCategory::SafeAdmitted, ret_1.clone(), ret_1.clone(), Some(ret_1.clone())),
            make_case(GenCategory::SafeAdmitted, ret_1.clone(), ret_1.clone(), Some(ret_1)),
            ub_agreed,
            broken_ub_probe,
        ];
        let partial_m = compute_fuzz_metrics(&partial_cases, 1.0);
        assert_eq!(partial_m.targeted_ub_probes, 2);
        assert_eq!(partial_m.ub_probes_agreed_count, 1);
        let partial_gate = check_fuzz_gates(&partial_m, 0.90, 0.20, 4);
        assert!(
            partial_gate.as_deref().is_some_and(|g| g.contains("1/2 TargetedUbProbe")),
            "expected partial TargetedUbProbe coverage failure, got {partial_gate:?}"
        );
        let forged_partial_rep = FuzzReport {
            schema: "anneal-differential-fuzz/v1".to_owned(),
            alpha_notice: ALPHA_NOTICE.to_owned(),
            mir_dialect: "profile_v1".to_owned(),
            seed: 1,
            max_stmts: 4,
            ub_ratio: 0.20,
            fuel: 1_500,
            capture_bin_source: "explicit".to_owned(),
            capture_bin_sha256: "a".repeat(64),
            prebuilt_overlay: "none".to_owned(),
            legs: vec![
                "rustc_compiled".to_owned(),
                "miri".to_owned(),
                "lean_step_core_captured".to_owned(),
            ],
            min_admission_rate: 0.90,
            metrics: partial_m,
            gate_error: None,
            cases: partial_cases,
        };
        assert!(!forged_partial_rep.is_passing());
    }

    #[test]
    fn leg3_short_circuit_and_low_max_stmts_move_reinit_gate_behave_cleanly() {
        let mut invocations = 0usize;
        let mut global_err: Option<String> = None;
        for _ in 0..32 {
            let out = eval_leg3_with_short_circuit(&mut global_err, || {
                invocations += 1;
                (
                    ObservedOutcome::ToolError {
                        detail: "anneal-mir-eval timed out after 120.000s".to_owned(),
                    },
                    true,
                )
            });
            assert!(matches!(out, ObservedOutcome::ToolError { .. }));
        }
        assert_eq!(
            invocations, 1,
            "global Leg-3 timeout/launch failure must short-circuit remaining cases"
        );

        // Non-global exit-code errors on one case must NOT short-circuit peers.
        let mut case_calls = 0usize;
        let mut non_global_err: Option<String> = None;
        for _ in 0..4 {
            let _ = eval_leg3_with_short_circuit(&mut non_global_err, || {
                case_calls += 1;
                (ObservedOutcome::ToolError { detail: "malformed json".to_owned() }, false)
            });
        }
        assert_eq!(case_calls, 4);
        assert_eq!(non_global_err, None);

        // For `max_stmts < 4`, UB-free `MoveReinit` + mixer (4 statements)
        // cannot fit, so `check_fuzz_gates` disables the `>= 16` move/reinit
        // floor while keeping it enforced at `max_stmts >= 4`.
        let ret_1 =
            ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 1 } };
        let sixteen_ok: Vec<FuzzCaseReport> = (0..16)
            .map(|_| {
                make_case(
                    GenCategory::SafeAdmitted,
                    ret_1.clone(),
                    ret_1.clone(),
                    Some(ret_1.clone()),
                )
            })
            .collect();
        let m_16 = compute_fuzz_metrics(&sixteen_ok, 1.0);
        assert_eq!(m_16.move_reinit_exercised_count, 0);
        for small_budget in 1..=3 {
            assert_eq!(check_fuzz_gates(&m_16, 0.90, 0.0, small_budget), None);
        }
        assert!(
            check_fuzz_gates(&m_16, 0.90, 0.0, 4)
                .as_deref()
                .is_some_and(|g| g.contains("vacuous move-reinit fuzzing"))
        );
    }

    #[test]
    fn admitted_cases_requires_clean_returned_outcome_and_bounds_run_before_prepare() {
        let panic_out = ObservedOutcome::Panic { detail: "panicked".to_owned() };
        let unwound_out = ObservedOutcome::Unwound { detail: "TerminalOut.unwound".to_owned() };
        let abort_out = ObservedOutcome::AbnormalAbort { detail: "aborted".to_owned() };
        let safe_panic =
            make_case(GenCategory::SafeAdmitted, panic_out.clone(), unwound_out, Some(panic_out));
        let bound_abort = make_case(
            GenCategory::BoundaryEdgeCase,
            abort_out.clone(),
            abort_out.clone(),
            Some(abort_out),
        );
        assert_eq!(safe_panic.evaluation.agreement, OracleAgreementClass::BiFaultEquivAgreement);
        assert_eq!(bound_abort.evaluation.agreement, OracleAgreementClass::BiFaultEquivAgreement);

        let m = compute_fuzz_metrics(&[safe_panic, bound_abort], 1.0);
        assert_eq!(m.bi_fault_equiv_count, 2);
        assert_eq!(m.admission_eligible_cases, 2);
        assert_eq!(m.admitted_cases, 0, "panics/aborts must never count as admitted_cases");
        assert_eq!(m.admission_rate, 0.0);
        assert!(
            check_fuzz_gates(&m, 0.90, 0.0, 6)
                .as_deref()
                .is_some_and(|g| g.contains("admission rate"))
        );

        let missing_manifest = Some(PathBuf::from("/nonexistent/mir-eval/Cargo.toml"));
        for (bad_opts, needle) in [
            (
                FuzzOptions {
                    fuel: 0,
                    mir_eval_manifest: missing_manifest.clone(),
                    ..FuzzOptions::default()
                },
                "--fuel",
            ),
            (
                FuzzOptions {
                    max_stmts: 0,
                    mir_eval_manifest: missing_manifest.clone(),
                    ..FuzzOptions::default()
                },
                "--max-stmts",
            ),
            (
                FuzzOptions {
                    cases: 0,
                    mir_eval_manifest: missing_manifest,
                    ..FuzzOptions::default()
                },
                "--cases",
            ),
        ] {
            let err = run_fuzz_campaign(&bad_opts).unwrap_err();
            assert!(
                err.contains(needle),
                "expected generator bound rejection containing {needle:?} before toolchain prepare, got: {err}"
            );
        }

        #[cfg(unix)]
        {
            let tmp_cache = tempfile::tempdir().unwrap();
            let real_cache = tmp_cache.path().join("real-cache");
            std::fs::create_dir_all(&real_cache).unwrap();
            let sym_cache = tmp_cache.path().join("sym-cache");
            std::os::unix::fs::symlink(&real_cache, &sym_cache).unwrap();
            for bad_cache in [sym_cache.clone(), sym_cache.join("sub")] {
                let prep_err = match FuzzSession::prepare(&FuzzOptions {
                    cache_root: Some(bad_cache.clone()),
                    ..FuzzOptions::default()
                }) {
                    Ok(_) => {
                        panic!("expected symlinked cache_root failure for {}", bad_cache.display())
                    }
                    Err(e) => e,
                };
                assert!(prep_err.contains("symlink"), "{prep_err}");
                let run_err = run_fuzz_campaign(&FuzzOptions {
                    cache_root: Some(bad_cache),
                    ..FuzzOptions::default()
                })
                .unwrap_err();
                assert!(run_err.contains("symlink"), "{run_err}");
            }
        }

        let report = FuzzReport {
            schema: "anneal-differential-fuzz/v1".to_owned(),
            alpha_notice: ALPHA_NOTICE.to_owned(),
            mir_dialect: "profile_v1".to_owned(),
            seed: 42,
            max_stmts: 6,
            ub_ratio: 0.20,
            fuel: 777,
            capture_bin_source: "explicit".to_owned(),
            capture_bin_sha256: "a".repeat(64),
            prebuilt_overlay: "none".to_owned(),
            legs: vec!["miri".to_owned(), "lean_step_core_captured".to_owned()],
            min_admission_rate: 0.90,
            metrics: m,
            gate_error: None,
            cases: Vec::new(),
        };
        let raw = serde_json::to_value(&report).expect("serialize FuzzReport");
        assert_eq!(raw.get("fuel").and_then(|v| v.as_u64()), Some(777));
        let round: FuzzReport = serde_json::from_value(raw).expect("deserialize FuzzReport");
        assert_eq!(round.fuel, 777);
    }

    #[test]
    fn incomplete_rustc_map_converts_missing_case_to_tool_error_and_fails_passing() {
        let mut incomplete_map = BTreeMap::new();
        let ret_1 =
            ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 1 } };
        incomplete_map.insert(
            "fuzz_s1_c0000".to_owned(),
            (ret_1.clone(), Some("ANNEAL_RUSTC_RUN:fuzz_s1_c0000:fuzz_case_0000|".to_owned())),
        );

        let (present_out, present_ev, present_missing) =
            resolve_rustc_case_outcome(Some(&incomplete_map), "fuzz_s1_c0000");
        assert!(!present_missing);
        assert_eq!(present_out, Some(ret_1.clone()));
        assert!(present_ev.is_some());

        let (missing_out, missing_ev, is_missing) =
            resolve_rustc_case_outcome(Some(&incomplete_map), "fuzz_s1_c0001");
        assert!(is_missing);
        assert!(missing_ev.is_none());
        assert!(matches!(missing_out, Some(ObservedOutcome::ToolError { .. })));

        // When rustc leg is disabled, `None` map yields `NotRun` cleanly.
        let (disabled_out, disabled_ev, disabled_missing) =
            resolve_rustc_case_outcome(None, "fuzz_s1_c0001");
        assert!(!disabled_missing);
        assert!(disabled_out.is_none());
        assert!(disabled_ev.is_none());

        let mut omitted_case =
            make_case(GenCategory::SafeAdmitted, ret_1.clone(), ret_1.clone(), missing_out);
        omitted_case.evaluation = evaluate_fuzz_case(
            &omitted_case.miri,
            &omitted_case.lean,
            omitted_case.rustc.as_ref(),
            None,
            None,
        );
        assert_eq!(omitted_case.evaluation.agreement, OracleAgreementClass::AuthorityDisagreement);
        assert!(matches!(
            omitted_case.evaluation.rustc_status,
            RustcCheckStatus::Disagreement { .. }
        ));
        let metrics = compute_fuzz_metrics(&[omitted_case.clone()], 0.5);
        assert_eq!(metrics.authority_disagreement_count, 1);
        let failing_rep = FuzzReport {
            schema: "anneal-differential-fuzz/v1".to_owned(),
            alpha_notice: ALPHA_NOTICE.to_owned(),
            mir_dialect: "profile_v1".to_owned(),
            seed: 1,
            max_stmts: 6,
            ub_ratio: 0.20,
            fuel: 1_500,
            capture_bin_source: "explicit".to_owned(),
            capture_bin_sha256: "a".repeat(64),
            prebuilt_overlay: "none".to_owned(),
            legs: vec![
                "rustc_compiled".to_owned(),
                "miri".to_owned(),
                "lean_step_core_captured".to_owned(),
            ],
            min_admission_rate: 0.90,
            metrics: metrics.clone(),
            gate_error: None,
            cases: vec![omitted_case],
        };
        assert!(!failing_rep.is_passing());

        // `is_passing()` also rejects `rustc: None` when `"rustc_compiled"` is
        // advertised in `legs` for non-UB cases, while accepting `rustc: None`
        // when Miri established UB (`IgnoredDueToMiriUb`).
        let mut null_rustc_rep = failing_rep.clone();
        null_rustc_rep.cases =
            vec![make_case(GenCategory::SafeAdmitted, ret_1.clone(), ret_1.clone(), None)];
        null_rustc_rep.metrics = compute_fuzz_metrics(&null_rustc_rep.cases, 0.5);
        assert!(!null_rustc_rep.is_passing());

        let ub_div0 = ObservedOutcome::UndefinedBehavior { detail: "dividing by zero".to_owned() };
        let mut ub_probe_skipped =
            make_case(GenCategory::TargetedUbProbe, ub_div0.clone(), ub_div0, None);
        ub_probe_skipped.evaluation = evaluate_fuzz_case_with_rustc_leg(
            &ub_probe_skipped.miri,
            &ub_probe_skipped.lean,
            None,
            None,
            None,
            true,
        );
        let mut ok_rep = failing_rep;
        ok_rep.cases = vec![
            make_case(GenCategory::SafeAdmitted, ret_1.clone(), ret_1, Some(ret_1_val())),
            ub_probe_skipped,
        ];
        ok_rep.metrics = compute_fuzz_metrics(&ok_rep.cases, 0.5);
        assert_eq!(ok_rep.metrics.rustc_ignored_ub_count, 1);
        assert!(ok_rep.is_passing());
    }

    #[test]
    fn admitted_category_miri_ub_yields_failure_signature_and_case_fuel() {
        let ub = ObservedOutcome::UndefinedBehavior {
            detail: "Undefined Behavior: dividing by zero".to_owned(),
        };
        let ret_0 =
            ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 0 } };
        for cat in [GenCategory::SafeAdmitted, GenCategory::BoundaryEdgeCase] {
            let mut case = make_case(cat, ub.clone(), ub.clone(), Some(ret_0.clone()));
            case.fuel = 1_500;
            assert_eq!(case.evaluation.agreement, OracleAgreementClass::BiFaultEquivAgreement);
            assert!(is_admitted_authority_ub(case.category, &case.miri));
            let sig = failure_signature_of(&case)
                .expect("admitted-category Miri UB must produce shrink FailureSignature");
            assert!(sig.admitted_authority_ub);
            assert_eq!(sig.agreement, OracleAgreementClass::BiFaultEquivAgreement);
            assert_eq!(sig.miri_ub_bucket, Some(MiriUbBucket::DivisionByZero));

            // Shrinking away the accidental UB must NOT match `sig`.
            let non_ub_cand = make_case(cat, ret_0.clone(), ret_0.clone(), Some(ret_0.clone()));
            assert_ne!(failure_signature_of(&non_ub_cand).as_ref(), Some(&sig));
        }

        // Deliberate `TargetedUbProbe` UB agreement must remain non-shrinkable.
        let ub_probe = make_case(GenCategory::TargetedUbProbe, ub.clone(), ub, Some(ret_0));
        assert!(!is_admitted_authority_ub(ub_probe.category, &ub_probe.miri));
        assert!(failure_signature_of(&ub_probe).is_none());

        let rep_case = make_case(GenCategory::ScopeControl, ret_0_u32(), ret_0_u32(), None);
        let mut scoped_case = rep_case;
        scoped_case.fuel = 40;
        let round_case: FuzzCaseReport = serde_json::from_value(
            serde_json::to_value(&scoped_case).expect("serialize FuzzCaseReport"),
        )
        .expect("deserialize FuzzCaseReport");
        assert_eq!(round_case.fuel, 40);

        let mut verif = FuzzMinimizedVerification::from_case_report(scoped_case);
        verif.fuel = 40;
        let round_verif: FuzzMinimizedVerification = serde_json::from_value(
            serde_json::to_value(&verif).expect("serialize FuzzMinimizedVerification"),
        )
        .expect("deserialize FuzzMinimizedVerification");
        assert_eq!(round_verif.fuel, 40);
    }

    #[test]
    fn missed_targeted_ub_probes_yield_shrink_signatures_and_retain_reproducers() {
        let ret_0 =
            ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 0 } };
        let ub_div0 = ObservedOutcome::UndefinedBehavior {
            detail: "Undefined Behavior: dividing by zero".to_owned(),
        };
        let lean_unsup =
            ObservedOutcome::Unsupported { detail: "Trusted.MirSemantics.unsupported".to_owned() };

        // 1. Targeted probe that stops hitting UB on Miri (both return 0) must
        //    still be shrinkable and yield a `FailureSignature`.
        let mut no_ub_probe =
            make_case(GenCategory::TargetedUbProbe, ret_0.clone(), ret_0.clone(), Some(ret_0));
        no_ub_probe.evaluation = evaluate_fuzz_case(
            &no_ub_probe.miri,
            &no_ub_probe.lean,
            no_ub_probe.rustc.as_ref(),
            None,
            None,
        );
        assert!(is_missed_targeted_ub_probe(
            no_ub_probe.category,
            &no_ub_probe.miri,
            &no_ub_probe.evaluation
        ));
        assert!(is_shrinkable_case(
            no_ub_probe.category,
            &no_ub_probe.miri,
            &no_ub_probe.evaluation
        ));
        let sig_no_ub =
            failure_signature_of(&no_ub_probe).expect("missed targeted non-UB probe must shrink");
        assert!(sig_no_ub.missed_targeted_ub_probe);

        // 2. Targeted probe where Miri hits UB but Lean conservatively refuses
        //    (`Unsupported` or `capture_rejected`) must likewise shrink cleanly
        //    with distinct signatures across those two failure modes.
        let mut cons_probe =
            make_case(GenCategory::TargetedUbProbe, ub_div0.clone(), lean_unsup, Some(ret_0_u32()));
        cons_probe.evaluation = evaluate_fuzz_case(
            &cons_probe.miri,
            &cons_probe.lean,
            cons_probe.rustc.as_ref(),
            None,
            None,
        );
        let sig_cons =
            failure_signature_of(&cons_probe).expect("conservative targeted UB miss must shrink");
        assert!(sig_cons.missed_targeted_ub_probe);
        assert_ne!(sig_no_ub, sig_cons);

        let mut cap_rej_probe = make_case(
            GenCategory::TargetedUbProbe,
            ub_div0.clone(),
            ObservedOutcome::Unsupported { detail: "capture unsupported".to_owned() },
            Some(ret_0_u32()),
        );
        cap_rej_probe.capture_rejected = Some("capture unsupported".to_owned());
        cap_rej_probe.evaluation = evaluate_fuzz_case(
            &cap_rej_probe.miri,
            &cap_rej_probe.lean,
            cap_rej_probe.rustc.as_ref(),
            None,
            cap_rej_probe.capture_rejected.as_deref(),
        );
        let sig_cap = failure_signature_of(&cap_rej_probe)
            .expect("capture-rejected targeted UB miss must shrink");
        assert!(sig_cap.missed_targeted_ub_probe);
        assert_ne!(sig_cons, sig_cap);

        // 3. Agreeing TargetedUbProbe must stay non-shrinkable, so shrinking a
        //    missed targeted probe cannot drift into an agreeing UB probe.
        let agreed_probe = make_case(GenCategory::TargetedUbProbe, ub_div0.clone(), ub_div0, None);
        assert!(!is_missed_targeted_ub_probe(
            agreed_probe.category,
            &agreed_probe.miri,
            &agreed_probe.evaluation
        ));
        assert!(!is_shrinkable_case(
            agreed_probe.category,
            &agreed_probe.miri,
            &agreed_probe.evaluation
        ));
        assert!(failure_signature_of(&agreed_probe).is_none());
    }

    fn ret_1_val() -> ObservedOutcome {
        ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 1 } }
    }

    fn ret_0_u32() -> ObservedOutcome {
        ObservedOutcome::Returned { value: MirValue::Int { int_kind: IntKind::U32, bits: 0 } }
    }

    #[cfg(unix)]
    #[test]
    fn miri_runs_before_rustc_and_skips_ub_probes_completely() {
        use std::{fs, os::unix::fs::PermissionsExt};

        use crate::r#gen::{GenExpr, GenStmt};

        let dir = tempfile::tempdir().unwrap();
        let base = dir.path().canonicalize().unwrap();
        let sys = base.join("sysroot");
        let bin_dir = sys.join("bin");
        let lib_dir = sys.join("lib");
        fs::create_dir_all(&bin_dir).unwrap();
        fs::create_dir_all(&lib_dir).unwrap();
        let miri_sys = base.join("miri_sysroot");
        fs::create_dir_all(miri_sys.join("lib/rustlib")).unwrap();

        let cc_stub = bin_dir.join("cc");
        fs::write(&cc_stub, "#!/bin/sh\nexit 0\n").unwrap();
        fs::set_permissions(&cc_stub, fs::Permissions::from_mode(0o755)).unwrap();

        let rustc_src_log = base.join("rustc_compiled_src.log");
        let rustc_exec_log = base.join("rustc_exec.log");
        let fake_rustc = bin_dir.join("rustc");
        fs::write(
            &fake_rustc,
            format!(
                "#!/bin/sh\nset -eu\n\
                 out_bin=\"\"\nsrc_file=\"\"\nprev=\"\"\nis_lib=0\n\
                 for a in \"$@\"; do\n\
                   if [ \"$prev\" = \"-o\" ]; then out_bin=\"$a\"; fi\n\
                   if [ \"$a\" = \"--crate-type=lib\" ]; then is_lib=1; fi\n\
                   case \"$a\" in *.rs) src_file=\"$a\" ;; esac\n\
                   prev=\"$a\"\n\
                 done\n\
                 if [ \"$is_lib\" = 1 ] && [ -n \"$out_bin\" ]; then\n\
                   : > \"$out_bin\"\n\
                   exit 0\n\
                 fi\n\
                 if [ -n \"$src_file\" ]; then\n\
                   cat \"$src_file\" >> '{}'\n\
                 fi\n\
                 if [ -n \"$out_bin\" ]; then\n\
                   cat > \"$out_bin\" <<'EOF'\n\
#!/bin/sh\n\
for arg in \"$@\"; do printf '%s\\n' \"$arg\" >> '{}'; done\n\
printf 'ANNEAL_RUSTC_RUN:c_ok:fuzz_fn_ok\\nANNEAL_RUSTC_CASE:c_ok:INT:u32:7\\nANNEAL_RUSTC_RET=INT:u32:7\\n'\n\
EOF\n\
                   chmod +x \"$out_bin\"\n\
                 fi\n",
                rustc_src_log.display(),
                rustc_exec_log.display()
            ),
        )
        .unwrap();
        fs::set_permissions(&fake_rustc, fs::Permissions::from_mode(0o755)).unwrap();

        let fake_miri = bin_dir.join("miri");
        fs::write(
            &fake_miri,
            "#!/bin/sh\nset -eu\n\
             mode=\"single\"\nsaw_sep=0\nlast=\"\"\nharness=\"\"\nfmt_json=0\n\
             for a in \"$@\"; do\n\
               if [ \"$saw_sep\" = 1 ] && [ \"$a\" = \"__BATCH__\" ]; then mode=\"batch\"; fi\n\
               if [ \"$a\" = \"--\" ]; then saw_sep=1; fi\n\
               if [ \"$a\" = \"--error-format=json\" ]; then fmt_json=1; fi\n\
               case \"$a\" in *.rs) harness=\"$a\" ;; esac\n\
               last=\"$a\"\n\
             done\n\
             tok=\"\"\n\
             if [ -n \"$harness\" ] && [ -f \"$harness\" ]; then\n\
               tok=$(sed -n 's/.*ANNEAL_MIRI_RUN:\\([0-9a-f]\\{32\\}\\):.*/\\1/p' \"$harness\" | head -n 1 || true)\n\
             fi\n\
             run_pfx='ANNEAL_MIRI_RUN:'\n\
             case_pfx='ANNEAL_MIRI_CASE:'\n\
             ret_pfx='ANNEAL_MIRI_RET='\n\
             if [ -n \"$tok\" ]; then\n\
               run_pfx=\"ANNEAL_MIRI_RUN:${tok}:\"\n\
               case_pfx=\"ANNEAL_MIRI_CASE:${tok}:\"\n\
               ret_pfx=\"ANNEAL_MIRI_RET:${tok}=\"\n\
             fi\n\
             emit_err() {\n\
               if [ \"$fmt_json\" = 1 ]; then\n\
                 printf '{\"$message_type\":\"diagnostic\",\"message\":\"%s\",\"level\":\"error\",\"spans\":[{\"file_name\":\"c/corpus.rs\"}],\"children\":[{\"message\":\"stack backtrace:\\\\n0: main\\\\n    at %s:1:1\",\"level\":\"note\",\"spans\":[],\"children\":[],\"rendered\":null}],\"rendered\":\"error: %s\"}\\n' \"$1\" \"$harness\" \"$1\" >&2\n\
                 printf '{\"$message_type\":\"diagnostic\",\"message\":\"aborting due to 1 previous error\",\"level\":\"error\",\"spans\":[],\"children\":[],\"rendered\":\"error: aborting due to 1 previous error\"}\\n' >&2\n\
               else\n\
                 printf 'error: %s\\n' \"$1\" >&2\n\
               fi\n\
             }\n\
             if [ \"$mode\" = \"batch\" ]; then\n\
               emit_err 'Undefined Behavior: dividing by zero'\n\
               exit 1\n\
             fi\n\
             case \"$last\" in\n\
               c_ok)\n\
                 printf '%sc_ok:fuzz_fn_ok\\n' \"$run_pfx\"\n\
                 printf '%sc_ok:INT:u32:7\\n' \"$case_pfx\"\n\
                 printf '%sINT:u32:7\\n' \"$ret_pfx\"\n\
                 ;;\n\
               c_acc_ub)\n\
                 printf '%sc_acc_ub:fuzz_fn_acc_ub\\n' \"$run_pfx\"\n\
                 emit_err 'Undefined Behavior: dividing by zero'\n\
                 exit 1\n\
                 ;;\n\
               c_ub)\n\
                 printf '%sc_ub:fuzz_fn_ub\\n' \"$run_pfx\"\n\
                 emit_err 'Undefined Behavior: entering unreachable code'\n\
                 exit 1\n\
                 ;;\n\
             esac\n",
        )
        .unwrap();
        fs::set_permissions(&fake_miri, fs::Permissions::from_mode(0o755)).unwrap();

        let fake_capture = base.join("fake_capture");
        fs::write(
            &fake_capture,
            "#!/bin/sh\nset -eu\nout_dir=\"\"\nprev=\"\"\n\
             for a in \"$@\"; do\n\
               if [ \"$prev\" = \"--out-dir\" ]; then out_dir=\"$a\"; fi\n\
               prev=\"$a\"\n\
             done\n\
             mkdir -p \"$out_dir\"\n\
             cat > \"$out_dir/capture.json\" <<'EOF'\n\
{\"program\":{\"bodies\":[{\"identity\":\"fuzz_fn_ok\",\"arg_count\":0,\"local_tys\":[],\"blocks\":[]},{\"identity\":\"fuzz_fn_acc_ub\",\"arg_count\":0,\"local_tys\":[],\"blocks\":[]},{\"identity\":\"fuzz_fn_ub\",\"arg_count\":0,\"local_tys\":[],\"blocks\":[]}]}}\n\
EOF\n\
             : > \"$out_dir/Captured.lean\"\n\
             printf '{\"status\":\"captured\",\"capture\":\"%s/capture.json\",\"lean\":\"%s/Captured.lean\"}\\n' \"$out_dir\" \"$out_dir\"\n",
        )
        .unwrap();
        fs::set_permissions(&fake_capture, fs::Permissions::from_mode(0o755)).unwrap();

        let fake_lean = base.join("fake_lean");
        fs::write(
            &fake_lean,
            "#!/bin/sh\nset -eu\nolean=\"\"\nprev=\"\"\n\
             for a in \"$@\"; do\n\
               if [ \"$prev\" = \"-o\" ]; then olean=\"$a\"; fi\n\
               prev=\"$a\"\n\
             done\n\
             if [ -n \"$olean\" ]; then : > \"$olean\"; exit 0; fi\n\
             printf 'ANNEAL_LEAN_CASE:c_ok:BODY|0|fuzz_fn_ok|MR0:RETURNED:INT:u32:7\\n'\n\
             printf 'ANNEAL_LEAN_CASE:c_acc_ub:BODY|1|fuzz_fn_acc_ub|MR0:FAULT:undefined:dividing by zero\\n'\n\
             printf 'ANNEAL_LEAN_CASE:c_ub:BODY|2|fuzz_fn_ub|MR0:FAULT:undefined:unreachable\\n'\n",
        )
        .unwrap();
        fs::set_permissions(&fake_lean, fs::Permissions::from_mode(0o755)).unwrap();

        let canon_lib = fs::canonicalize(&lib_dir).unwrap().to_string_lossy().into_owned();
        let child_path = env::join_paths([bin_dir.as_path(), Path::new("/bin")]).unwrap();
        let session = FuzzSession {
            rustc: Some(RustcSession {
                rustc_bin: fs::canonicalize(&fake_rustc).unwrap(),
                rust_sysroot: fs::canonicalize(&sys).unwrap(),
                ld_library_path: canon_lib.clone(),
                child_path: child_path.clone(),
                linker: fs::canonicalize(&cc_stub).unwrap(),
                pass_sysroot_arg: true,
                validated_tmpdir: None,
                _sysroot_staging: None,
            }),
            miri: MiriSession {
                miri_bin: fs::canonicalize(&fake_miri).unwrap(),
                rust_sysroot: fs::canonicalize(&sys).unwrap(),
                miri_sysroot: fs::canonicalize(&miri_sys).unwrap(),
                ld_library_path: canon_lib.clone(),
                validated_tmpdir: None,
                _sysroot_staging: None,
                _miri_sysroot_staging: None,
            },
            lean: LeanSession {
                anneal_root: base.clone(),
                capture_bin: fs::canonicalize(&fake_capture).unwrap(),
                rust_sysroot: fs::canonicalize(&sys).unwrap(),
                lean_bin: fs::canonicalize(&fake_lean).unwrap(),
                olean_paths: vec![],
                prebuilt_overlay: "none".to_owned(),
                ld_library_path: canon_lib,
                child_path: child_path.clone(),
                lean_ld_library_path: String::new(),
                lean_child_path: child_path,
                validated_tmpdir: None,
                _rust_sysroot_staging: None,
                _capture_staging: None,
                _lean_lib_staging: None,
                _lean_stdlib_staging: None,
                _lean_dag_staging: None,
            },
            mir_eval_bin: None,
            mir_eval_exec_bin: None,
            capture_bin_source: "explicit".to_owned(),
            capture_bin_sha256: "a".repeat(64),
            _capture_staging: None,
            _mir_eval_guard: None,
            _cache_guard: None,
            _lean_cache_guard: None,
        };

        let make_prog =
            |case_id: &str, fn_name: &str, cat: GenCategory, ub_stmt: bool| GenProgram {
                case_id: case_id.to_owned(),
                fn_name: fn_name.to_owned(),
                master_seed: 1,
                case_index: 0,
                category: cat,
                is_unsafe: ub_stmt,
                params: vec![],
                locals: vec![],
                body: if ub_stmt { vec![GenStmt::HintUnreachable] } else { vec![] },
                ret_ty: crate::r#gen::GenType::Int(IntKind::U32),
                ret_expr: GenExpr::Lit(MirValue::Int { int_kind: IntKind::U32, bits: 7 }),
                fuel: 200,
            };
        let progs = vec![
            make_prog("c_ok", "fuzz_fn_ok", GenCategory::SafeAdmitted, false),
            make_prog("c_acc_ub", "fuzz_fn_acc_ub", GenCategory::SafeAdmitted, true),
            make_prog("c_ub", "fuzz_fn_ub", GenCategory::TargetedUbProbe, true),
        ];

        let reports = session.evaluate_batch(&progs, 0).expect("evaluate mixed batch");
        assert_eq!(reports.len(), 3);
        assert_eq!(
            reports[0].rustc,
            Some(ObservedOutcome::Returned {
                value: MirValue::Int { int_kind: IntKind::U32, bits: 7 }
            })
        );
        assert_eq!(reports[0].evaluation.rustc_status, RustcCheckStatus::Agreed);

        // Both accidental SafeAdmitted UB and TargetedUbProbe UB must NEVER be
        // compiled or executed by Leg 0 `rustc`.
        for ub_rep in [&reports[1], &reports[2]] {
            assert!(ub_rep.rustc.is_none(), "expected rustc=None for {}", ub_rep.case_id);
            assert_eq!(ub_rep.evaluation.rustc_status, RustcCheckStatus::IgnoredDueToMiriUb);
            assert!(
                ub_rep.leg_evidence.as_ref().and_then(|le| le.rustc_evidence.as_ref()).is_none()
            );
        }
        let compiled_src = fs::read_to_string(&rustc_src_log).unwrap();
        assert!(compiled_src.contains("fuzz_fn_ok"), "{compiled_src}");
        assert!(!compiled_src.contains("fuzz_fn_acc_ub"), "UB compiled by rustc: {compiled_src}");
        assert!(!compiled_src.contains("fuzz_fn_ub"), "UB probe compiled by rustc: {compiled_src}");
        assert!(!compiled_src.contains("unreachable_unchecked"), "{compiled_src}");
        let exec_log = fs::read_to_string(&rustc_exec_log).unwrap();
        assert!(!exec_log.contains("c_acc_ub"), "{exec_log}");
        assert!(!exec_log.contains("c_ub"), "{exec_log}");

        // When every batch case hits Miri UB, skip invoking `rustc`.
        let src_len_before = compiled_src.len();
        let all_ub_only = session
            .evaluate_batch(std::slice::from_ref(&progs[2]), 1)
            .expect("evaluate all-UB batch");
        assert_eq!(all_ub_only.len(), 1);
        assert!(all_ub_only[0].rustc.is_none());
        assert_eq!(all_ub_only[0].evaluation.rustc_status, RustcCheckStatus::IgnoredDueToMiriUb);
        assert_eq!(fs::read_to_string(&rustc_src_log).unwrap().len(), src_len_before);
    }

    #[test]
    fn resolve_private_fuzz_caches_ignore_poisoned_external_caches() {
        let tmp = tempfile::tempdir().unwrap();
        let base = std::fs::canonicalize(tmp.path()).unwrap();
        let poisoned_cache = base.join("poisoned-cache");
        let forged_dag = poisoned_cache.join("lean-mirtotal-full-0000000000000000");
        std::fs::create_dir_all(&forged_dag).unwrap();
        std::fs::write(forged_dag.join(".anneal-oleans-ready"), "none\n").unwrap();
        let forged_miri = poisoned_cache.join("miri-sysroot-deadbeef-0000000000000000");
        std::fs::create_dir_all(forged_miri.join("lib/rustlib")).unwrap();
        std::fs::write(forged_miri.join(".anneal-miri-ready"), "{}").unwrap();

        let valid_tmp = base.join("clean-tmp");
        std::fs::create_dir_all(&valid_tmp).unwrap();
        let lean_guard = resolve_private_fuzz_lean_cache(Some(valid_tmp.as_os_str()), &base)
            .expect("private fuzz Lean cache must resolve cleanly");
        let miri_guard =
            resolve_private_fuzz_cache_dir("anneal-fuzz-miri-", Some(valid_tmp.as_os_str()), &base)
                .expect("private fuzz Miri cache must resolve cleanly");
        let lean_disk = lean_guard.fs_root().to_path_buf();
        let miri_disk = miri_guard.fs_root().to_path_buf();
        for (guard, disk) in [(&lean_guard, &lean_disk), (&miri_guard, &miri_disk)] {
            assert!(disk.starts_with(&valid_tmp));
            assert!(!disk.starts_with(&poisoned_cache));
            assert!(guard.path().is_dir());
            #[cfg(target_os = "linux")]
            assert!(guard.path().starts_with("/proc/self/fd/"));
        }
        assert_ne!(lean_disk, miri_disk);

        #[cfg(unix)]
        {
            use std::os::unix::fs::{PermissionsExt as _, symlink};
            for (guard, disk) in [(&lean_guard, &lean_disk), (&miri_guard, &miri_disk)] {
                let mode = std::fs::metadata(disk).unwrap().permissions().mode() & 0o777;
                assert_eq!(mode, 0o700);
                #[cfg(target_os = "linux")]
                {
                    let moved = base.join(format!(
                        "moved-{}",
                        guard.fs_root().file_name().unwrap().to_string_lossy()
                    ));
                    let canary = Path::new("canary.txt");
                    std::fs::write(guard.pin_path(canary), b"legit").unwrap();
                    std::fs::rename(disk, &moved).unwrap();
                    std::fs::create_dir_all(disk).unwrap();
                    std::fs::write(disk.join(canary), b"trojan").unwrap();
                    let mut f = guard.open_verified_rel_file(canary, "pinned canary").unwrap();
                    let mut got = String::new();
                    std::io::Read::read_to_string(&mut f, &mut got).unwrap();
                    assert_eq!(got, "legit");
                    std::fs::remove_dir_all(disk).unwrap();
                    std::fs::rename(&moved, disk).unwrap();
                }
            }
            let sym_tmp = base.join("sym-tmp");
            symlink(&valid_tmp, &sym_tmp).unwrap();
            let err =
                resolve_private_fuzz_lean_cache(Some(sym_tmp.as_os_str()), &base).unwrap_err();
            assert!(err.contains("TMPDIR") || err.contains("symlink"), "{err}");
            let miri_err = resolve_private_fuzz_cache_dir(
                "anneal-fuzz-miri-",
                Some(sym_tmp.as_os_str()),
                &base,
            )
            .unwrap_err();
            assert!(miri_err.contains("TMPDIR") || miri_err.contains("symlink"), "{miri_err}");
        }
        drop(lean_guard);
        drop(miri_guard);
        assert!(!lean_disk.exists());
        assert!(!miri_disk.exists());
    }
}
