// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! `anneal-itree-semantic-detail/v1` JSONL and `anneal-known-bug/v1` telemetry
//! emitters preserving [`ALPHA_BANNER_DEFAULT`] and fail-closed build-freshness
//! gates.

use std::{
    env,
    fmt::Write as _,
    path::Path,
    process::Command,
    time::{SystemTime, UNIX_EPOCH},
};

use serde::{Deserialize, Serialize};

use crate::{
    CaseReport, DifferentialReport,
    dedup::{
        BugRegistry, KnownBugRecord, ProvisionalFinding, SemanticsDetailKnownBug,
        dialect_key_for_mode,
    },
    lean_trace_runner::LeanTraceMode,
    outcome::{AuthorityRunResult, TerminalOutcome, TraceVerdict},
    shrink::{ShrinkFailureSignature, WitnessArtifact, atomic_write_text},
    spec::CaseCategory,
};

/// Mandatory Stage 0 Alpha honesty banner emitted on telemetry artifacts.
pub const ALPHA_BANNER_DEFAULT: &str =
    "Stage 0 Alpha \u{2014} Not Yet Audited (this is alpha software!)";

/// Canonical schema tag for `itree-diff --semantics-detail-out` JSONL
/// (`anneal-itree-semantic-detail/v1`, distinct from
/// `anneal/ci/check_mir_differential.py`'s full-case
/// `anneal-semantic-detail/v1` JSON schema).
pub const SEMANTIC_DETAIL_SCHEMA: &str = "anneal-itree-semantic-detail/v1";

/// Canonical default trust tier emitted on telemetry rows.
pub const TRUST_TIER_DEFAULT: &str = "stage0_alpha_unaudited";

/// Build-freshness gate enforced locally before telemetry emission.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BuildFreshness {
    VerifiedAtHead,
    FailedOrOom,
    TimedOut,
    Stale,
    NotRun,
}

impl BuildFreshness {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::VerifiedAtHead => "verified_at_head",
            Self::FailedOrOom => "failed_or_oom",
            Self::TimedOut => "timed_out",
            Self::Stale => "stale",
            Self::NotRun => "not_run",
        }
    }

    pub fn parse(s: &str) -> Option<Self> {
        match s {
            "verified_at_head" => Some(Self::VerifiedAtHead),
            "failed_or_oom" => Some(Self::FailedOrOom),
            "timed_out" => Some(Self::TimedOut),
            "stale" => Some(Self::Stale),
            "not_run" => Some(Self::NotRun),
            _ => None,
        }
    }
}

/// Metadata context for emitting `anneal-itree-semantic-detail/v1` and
/// `anneal-known-bug/v1` records.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TelemetryContext {
    pub repo: String,
    pub branch: String,
    pub branch_scope: String,
    pub exposed_on_main: bool,
    pub commit_sha: String,
    pub commit_unix_ts: i64,
    pub environment_profile: String,
    pub source_url: String,
    pub profile_v2: bool,
    pub build_freshness_override: Option<BuildFreshness>,
    pub build_exit_code_override: Option<i64>,
    #[serde(default)]
    pub head_provenance_verified: bool,
    #[serde(default)]
    pub discovered_head_sha: Option<String>,
}

impl TelemetryContext {
    /// Auto-discover Git repository/branch/HEAD metadata under `anneal_root`
    /// with fail-safe fallbacks when executed outside a git checkout, and
    /// verify whether the running executable is provably up-to-date with clean
    /// `HEAD`.
    pub fn discover(anneal_root: &Path) -> Self {
        let origin = run_git_trimmed(anneal_root, &["remote", "get-url", "origin"])
            .unwrap_or_else(|| "google/zerocopy".to_string());
        let repo = normalize_repo_slug(&origin);
        let branch = run_git_trimmed(anneal_root, &["rev-parse", "--abbrev-ref", "HEAD"])
            .unwrap_or_else(|| "unknown".to_string());
        let discovered_head_sha = run_git_trimmed(anneal_root, &["rev-parse", "--verify", "HEAD"])
            .filter(|s| is_valid_git_commit_sha(s));
        let commit_sha = discovered_head_sha.clone().unwrap_or_else(|| "0".repeat(40));
        let commit_unix_ts = run_git_trimmed(anneal_root, &["show", "-s", "--format=%ct", "HEAD"])
            .and_then(|s| s.parse::<i64>().ok())
            .unwrap_or_else(|| {
                SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .map(|d| d.as_secs() as i64)
                    .unwrap_or(0)
            });
        let cur_exe = env::current_exe().ok();
        let head_provenance_verified = verify_head_build_provenance_with(
            anneal_root,
            discovered_head_sha.as_deref(),
            Path::new(env!("CARGO_MANIFEST_DIR")),
            cur_exe.as_deref(),
            None,
            None,
        );
        let is_main = branch == "main";
        Self {
            repo,
            branch: branch.clone(),
            branch_scope: if is_main { "main".to_string() } else { "unstable_only".to_string() },
            exposed_on_main: is_main,
            commit_sha,
            commit_unix_ts,
            environment_profile: "local-itree-diff".to_string(),
            source_url: String::new(),
            profile_v2: false,
            build_freshness_override: None,
            build_exit_code_override: None,
            head_provenance_verified,
            discovered_head_sha,
        }
    }

    /// Return `true` only when executable build provenance was verified on a
    /// clean tree AND `self.commit_sha` still matches `discovered_head_sha`.
    pub fn is_verified_for_commit(&self) -> bool {
        self.head_provenance_verified
            && is_valid_git_commit_sha(&self.commit_sha)
            && self
                .discovered_head_sha
                .as_deref()
                .is_some_and(|head| head.eq_ignore_ascii_case(&self.commit_sha))
    }
}

pub(crate) fn is_40_hex_sha(s: &str) -> bool {
    s.len() == 40 && s.bytes().all(|b| b.is_ascii_hexdigit())
}

pub(crate) fn is_valid_git_commit_sha(s: &str) -> bool {
    is_40_hex_sha(s) && !s.bytes().all(|b| b == b'0')
}

fn run_git_raw(cwd: &Path, args: &[&str]) -> Option<Vec<u8>> {
    let mut cmd = Command::new("git");
    for var in [
        "GIT_DIR",
        "GIT_WORK_TREE",
        "GIT_INDEX_FILE",
        "GIT_COMMON_DIR",
        "GIT_OBJECT_DIRECTORY",
        "GIT_ALTERNATE_OBJECT_DIRECTORIES",
    ] {
        cmd.env_remove(var);
    }
    let out = cmd
        .env("GIT_TERMINAL_PROMPT", "0")
        .arg("--no-optional-locks")
        .arg("-C")
        .arg(cwd)
        .args(args)
        .output()
        .ok()?;
    if !out.status.success() {
        return None;
    }
    Some(out.stdout)
}

fn run_git_trimmed(cwd: &Path, args: &[&str]) -> Option<String> {
    let raw = run_git_raw(cwd, args)?;
    let s = String::from_utf8_lossy(&raw).trim().to_string();
    if s.is_empty() { None } else { Some(s) }
}

/// Fail-closed check for executable build provenance against clean `HEAD` at
/// `anneal_root`.
///
/// Standalone `anneal-itree-diff` binaries cannot `build.rs`-embed or
/// cryptographically authenticate their own binary contents against a clean Git
/// commit (`cargo_boundary` forbids `build.rs` and unauthenticated compile-time
/// env flags like `ANNEAL_BUILD_COMMIT_SHA` or mtimes can be forged on a
/// dirty build later restored cleanly). Therefore this self-check always
/// fails closed (`false`) so unauthenticated local builds emit
/// `build_freshness = "stale"` (`overall_status = "UNVERIFIED"`), and
/// `"verified_at_head"` requires an explicit trusted orchestrator provenance
/// context.
pub fn verify_head_build_provenance_with(
    anneal_root: &Path,
    discovered_head_sha: Option<&str>,
    _compile_manifest_dir: &Path,
    _current_exe: Option<&Path>,
    _build_commit_sha_env: Option<&str>,
    _build_tree_clean_env: Option<&str>,
) -> bool {
    let Some(_head_sha) = discovered_head_sha.filter(|s| is_valid_git_commit_sha(s)) else {
        return false;
    };
    let Some(_status_out) =
        run_git_raw(anneal_root, &["status", "--porcelain", "--untracked-files=all"])
    else {
        return false;
    };
    false
}

fn is_valid_slug_segment(seg: &str) -> bool {
    !seg.is_empty()
        && seg != "."
        && seg != ".."
        && seg.bytes().all(|b| b.is_ascii_alphanumeric() || matches!(b, b'-' | b'_' | b'.'))
}

/// Strictly validate and normalize a remote URL or explicit `<org>/<repo>`
/// slug, failing closed on empty strings, `file://` URLs, local paths,
/// multi-segment non-host paths, or invalid characters.
pub fn try_normalize_repo_slug(raw: &str) -> Result<String, String> {
    let trimmed = raw.trim();
    let without_query = trimmed.split(&['?', '#'][..]).next().unwrap_or("").trim_end_matches('/');
    if without_query.is_empty() {
        return Err("repository slug or URL must not be empty".to_string());
    }

    let path_part = if let Some((scheme, after_scheme)) = without_query.split_once("://") {
        if scheme.eq_ignore_ascii_case("file") {
            return Err(format!("local file:// repository URIs are rejected: {raw:?}"));
        }
        let without_creds =
            after_scheme.rsplit_once('@').map(|(_, rest)| rest).unwrap_or(after_scheme);
        let Some((_host_port, rest_path)) = without_creds.split_once('/') else {
            return Err(format!("repository URL is missing owner/repo path: {raw:?}"));
        };
        rest_path
    } else if without_query.get(..5).is_some_and(|p| p.eq_ignore_ascii_case("file:")) {
        return Err(format!("local file: repository URIs are rejected: {raw:?}"));
    } else if without_query.starts_with('/')
        || without_query.starts_with("./")
        || without_query.starts_with("../")
        || without_query.contains('\\')
        || is_windows_drive_path(without_query)
    {
        return Err(format!("local filesystem repository paths are rejected: {raw:?}"));
    } else {
        let without_creds =
            without_query.rsplit_once('@').map(|(_, rest)| rest).unwrap_or(without_query);
        let colon_pos = without_creds.find(':');
        let slash_pos = without_creds.find('/');
        if let Some(c_idx) = colon_pos
            && slash_pos.is_none_or(|s_idx| c_idx < s_idx)
        {
            let host = &without_creds[..c_idx];
            if host.eq_ignore_ascii_case("file")
                || !(host.contains('.') || host.eq_ignore_ascii_case("localhost"))
            {
                return Err(format!(
                    "repository URI requires a valid remote host before `:`, got {raw:?}"
                ));
            }
            &without_creds[c_idx + 1..]
        } else {
            let segs: Vec<&str> = without_creds.split('/').filter(|s| !s.is_empty()).collect();
            if segs.len() >= 3
                && (segs[0].contains('.') || segs[0].eq_ignore_ascii_case("localhost"))
            {
                let prefix_len = without_creds.find('/').map(|i| i + 1).unwrap_or(0);
                &without_creds[prefix_len..]
            } else if segs.len() == 2 && colon_pos.is_none() {
                without_creds
            } else {
                return Err(format!(
                    "expected `<org>/<repo>` slug or remote repository URL, got {raw:?}"
                ));
            }
        }
    };

    let mut clean_path = path_part.trim_matches('/');
    for suffix in [".git", ".bundle"] {
        if let Some(stem) = clean_path.strip_suffix(suffix) {
            clean_path = stem.trim_end_matches('/');
        }
    }
    let segs: Vec<&str> = clean_path.split('/').filter(|s| !s.is_empty()).collect();
    if segs.len() < 2 {
        return Err(format!("repository specifier must include `<org>/<repo>`: {raw:?}"));
    }
    let org = segs[segs.len() - 2];
    let repo = segs[segs.len() - 1];
    if !is_valid_slug_segment(org) || !is_valid_slug_segment(repo) {
        return Err(format!("invalid characters in normalized slug `{org}/{repo}` from {raw:?}"));
    }
    Ok(format!("{org}/{repo}"))
}

/// Normalize remote URLs or slugs into strictly `<org>/<repo>` with zero
/// credential, scheme, hostname, port, query, or local-path leakage, falling
/// back to `google/zerocopy` when automatic origin discovery sees an unusable
/// remote string.
pub fn normalize_repo_slug(raw: &str) -> String {
    try_normalize_repo_slug(raw).unwrap_or_else(|_| "google/zerocopy".to_string())
}

fn is_windows_drive_path(s: &str) -> bool {
    let b = s.as_bytes();
    b.len() >= 2 && b[0].is_ascii_alphabetic() && b[1] == b':'
}

/// Evidence block inside `anneal-itree-semantic-detail/v1`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EvidenceBlockTelemetry {
    pub domain: String,
    pub evidence_grade: String,
    pub build_freshness: String,
    pub build_exit_code: i64,
    pub overall_status: String,
}

/// Differential suite summary inside `anneal-itree-semantic-detail/v1`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DifferentialRunTelemetry {
    pub suite: String,
    pub legs: Vec<String>,
    pub compared_count: usize,
    pub agree_count: usize,
    pub unsound_missed_fault_count: usize,
    pub value_mismatch_count: usize,
    pub kernel_checked_count: usize,
    pub sound_conservative_abstraction_count: usize,
    pub undeclared_ub_fault_count: usize,
    pub disclosed_gap_count: usize,
    pub degraded_count: usize,
    pub tool_error_count: usize,
    pub panic_agreed_count: usize,
    #[serde(default)]
    pub expectation_mismatch_count: usize,
    pub overall_status: String,
}

/// Full `anneal-itree-semantic-detail/v1` record emitted for downstream
/// consumers.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SemanticDetailRecord {
    pub schema: String,
    pub alpha_notice: String,
    pub repo: String,
    pub branch: String,
    pub commit_sha: String,
    pub commit_unix_ts: i64,
    pub mir_dialect: String,
    pub environment_profile: String,
    pub trust_tier: String,
    pub build_freshness: String,
    pub build_exit_code: i64,
    pub overall_status: String,
    pub source_url: String,
    pub evidence_blocks: Vec<EvidenceBlockTelemetry>,
    pub differential_runs: Vec<DifferentialRunTelemetry>,
    pub known_bugs: Vec<SemanticsDetailKnownBug>,
}

fn validate_registry_repo_binding(
    registry: &BugRegistry,
    expected_repo: &str,
) -> Result<(), String> {
    if registry.repo != expected_repo {
        return Err(format!(
            "bug registry repo {:?} does not match telemetry repo {:?}",
            registry.repo, expected_repo
        ));
    }
    for bucket in registry.buckets.values() {
        if bucket.repo != expected_repo {
            return Err(format!(
                "bug {} has repo {:?} outside telemetry repo {:?}",
                bucket.bug_id, bucket.repo, expected_repo
            ));
        }
    }
    Ok(())
}

fn validate_report_accounting(report: &DifferentialReport) -> Result<(), String> {
    let (expected_counts, expected_by_category) =
        DifferentialReport::expected_counts_and_categories(&report.cases);
    if report.counts != expected_counts || report.by_category != expected_by_category {
        return Err(format!(
            "differential report accounting mismatch: reported counts {:?} vs cases-derived {:?}",
            report.counts, expected_counts
        ));
    }
    Ok(())
}

impl SemanticDetailRecord {
    /// Build a validated [`SemanticDetailRecord`] from a
    /// [`DifferentialReport`], deduplicated [`BugRegistry`], and
    /// [`TelemetryContext`].
    pub fn from_report_and_registry(
        report: &DifferentialReport,
        registry: &BugRegistry,
        ctx: &TelemetryContext,
    ) -> Result<Self, String> {
        validate_report_accounting(report)?;
        let dialect_key = dialect_key_for_mode(report.lean_mode, ctx.profile_v2).to_string();

        let (derived_freshness, derived_exit_code) =
            derive_freshness_from_report_and_ctx(report, ctx);
        let freshness = ctx.build_freshness_override.unwrap_or(derived_freshness);
        let exit_code = ctx.build_exit_code_override.unwrap_or(derived_exit_code);

        let mut corpus_cases: Vec<&CaseReport> = Vec::new();
        let mut fuzz_cases: Vec<&CaseReport> = Vec::new();
        for c in &report.cases {
            if c.category == CaseCategory::FuzzGenerated {
                fuzz_cases.push(c);
            } else {
                corpus_cases.push(c);
            }
        }

        let overall_status = compute_honest_overall_status(report, freshness, exit_code);
        let mut differential_runs = Vec::new();
        let downgrade_non_verified = freshness != BuildFreshness::VerifiedAtHead
            || exit_code != 0
            || !report.miri_available
            || overall_status == "UNVERIFIED";
        if !corpus_cases.is_empty() {
            let corpus_legs = executed_legs_for_slice(report.lean_mode, &corpus_cases);
            let mut slice = summarize_run_slice(
                "itree_diff_corpus",
                &corpus_legs,
                &corpus_cases,
                report.require_miri,
            );
            if downgrade_non_verified && slice.overall_status == "PASS" {
                slice.overall_status = "UNVERIFIED".to_string();
            }
            differential_runs.push(slice);
        }
        if !fuzz_cases.is_empty() {
            let fuzz_legs = executed_legs_for_slice(report.lean_mode, &fuzz_cases);
            let mut slice = summarize_run_slice(
                "itree_diff_fuzz",
                &fuzz_legs,
                &fuzz_cases,
                report.require_miri,
            );
            if downgrade_non_verified && slice.overall_status == "PASS" {
                slice.overall_status = "UNVERIFIED".to_string();
            }
            differential_runs.push(slice);
        }
        if overall_status == "FAIL" && !differential_runs.iter().any(|r| r.overall_status == "FAIL")
        {
            for slice in &mut differential_runs {
                if slice.overall_status == "PASS" {
                    slice.overall_status = "UNVERIFIED".to_string();
                }
            }
        }

        let block_status = overall_status.to_string();
        let evidence_blocks = vec![EvidenceBlockTelemetry {
            domain: "differential_oracle".to_string(),
            evidence_grade: "empirical_difftest".to_string(),
            build_freshness: freshness.as_str().to_string(),
            build_exit_code: exit_code,
            overall_status: block_status,
        }];

        validate_registry_repo_binding(registry, &ctx.repo)?;
        let known_bugs = registry.to_semantics_detail_entries()?;

        let rec = Self {
            schema: SEMANTIC_DETAIL_SCHEMA.to_string(),
            alpha_notice: ALPHA_BANNER_DEFAULT.to_string(),
            repo: ctx.repo.clone(),
            branch: ctx.branch.clone(),
            commit_sha: ctx.commit_sha.clone(),
            commit_unix_ts: ctx.commit_unix_ts,
            mir_dialect: dialect_key,
            environment_profile: ctx.environment_profile.clone(),
            trust_tier: TRUST_TIER_DEFAULT.to_string(),
            build_freshness: freshness.as_str().to_string(),
            build_exit_code: exit_code,
            overall_status: overall_status.to_string(),
            source_url: ctx.source_url.clone(),
            evidence_blocks,
            differential_runs,
            known_bugs,
        };
        rec.validate_honesty()?;
        Ok(rec)
    }

    /// Enforce every honesty invariant locally before writing to disk.
    pub fn validate_honesty(&self) -> Result<(), String> {
        if self.schema != SEMANTIC_DETAIL_SCHEMA {
            return Err(format!("unexpected schema `{}`", self.schema));
        }
        if self.alpha_notice != ALPHA_BANNER_DEFAULT {
            return Err(format!(
                "alpha_notice must equal `{ALPHA_BANNER_DEFAULT}`, got {:?}",
                self.alpha_notice
            ));
        }
        if self.trust_tier != TRUST_TIER_DEFAULT {
            return Err(format!(
                "trust_tier must equal `{TRUST_TIER_DEFAULT}`, got {:?}",
                self.trust_tier
            ));
        }
        if self.repo.trim().is_empty() || self.mir_dialect.trim().is_empty() {
            return Err("repo and mir_dialect must be non-empty".to_string());
        }
        if !is_40_hex_sha(&self.commit_sha) {
            return Err(format!(
                "semantic_detail commit_sha must be a 40-character hexadecimal Git SHA, got {:?}",
                self.commit_sha
            ));
        }
        let parent_freshness = validate_freshness_and_exit_code(
            &self.build_freshness,
            self.build_exit_code,
            "semantic_detail",
        )?;
        if !matches!(self.overall_status.as_str(), "PASS" | "FAIL" | "UNVERIFIED") {
            return Err(format!("invalid overall_status {:?}", self.overall_status));
        }
        if (parent_freshness == BuildFreshness::VerifiedAtHead || self.overall_status == "PASS")
            && !is_valid_git_commit_sha(&self.commit_sha)
        {
            return Err(format!(
                "semantic_detail commit_sha cannot be all-zero when build_freshness={:?}, overall_status={:?}",
                self.build_freshness, self.overall_status
            ));
        }
        let stale_parent =
            parent_freshness != BuildFreshness::VerifiedAtHead || self.build_exit_code != 0;
        if stale_parent && self.overall_status == "PASS" {
            return Err(format!(
                "overall_status PASS forbidden when build_freshness={:?}, build_exit_code={}",
                self.build_freshness, self.build_exit_code
            ));
        }
        if self.overall_status == "PASS" && self.evidence_blocks.is_empty() {
            return Err("overall_status PASS forbidden without evidence_blocks".to_string());
        }
        for b in &self.evidence_blocks {
            let block_ctx = format!("evidence block `{}`", b.domain);
            let block_freshness = validate_freshness_and_exit_code(
                &b.build_freshness,
                b.build_exit_code,
                &block_ctx,
            )?;
            if !matches!(b.overall_status.as_str(), "PASS" | "FAIL" | "UNVERIFIED") {
                return Err(format!(
                    "evidence block `{}` has invalid overall_status {:?}",
                    b.domain, b.overall_status
                ));
            }
            if self.overall_status == "PASS" && b.overall_status != "PASS" {
                return Err(format!(
                    "overall_status PASS forbidden when evidence block `{}` has overall_status={:?}",
                    b.domain, b.overall_status
                ));
            }
            let stale_block =
                block_freshness != BuildFreshness::VerifiedAtHead || b.build_exit_code != 0;
            if stale_block && (b.overall_status == "PASS" || self.overall_status == "PASS") {
                return Err(format!(
                    "PASS forbidden when evidence block `{}` has freshness={:?} exit={} (block_status={:?}, overall_status={:?})",
                    b.domain,
                    b.build_freshness,
                    b.build_exit_code,
                    b.overall_status,
                    self.overall_status
                ));
            }
            if b.overall_status == "PASS" && (stale_parent || self.overall_status == "UNVERIFIED") {
                return Err(format!(
                    "evidence block `{}` cannot report PASS when parent build_freshness={:?}, build_exit_code={}, overall_status={:?}",
                    b.domain, self.build_freshness, self.build_exit_code, self.overall_status
                ));
            }
            if b.overall_status == "FAIL" && self.overall_status != "FAIL" {
                return Err(format!(
                    "overall_status {:?} forbidden when evidence block `{}` has overall_status=\"FAIL\"",
                    self.overall_status, b.domain
                ));
            }
        }
        if self.overall_status == "PASS"
            && !self.differential_runs.iter().any(|r| r.compared_count > 0)
        {
            return Err(
                "overall_status PASS forbidden without at least one differential slice with compared_count > 0"
                    .to_string(),
            );
        }
        let any_fail_slice = self.differential_runs.iter().any(|r| r.overall_status == "FAIL");
        if any_fail_slice && self.overall_status != "FAIL" {
            return Err(format!(
                "overall_status {:?} forbidden when a differential slice has overall_status=\"FAIL\"",
                self.overall_status
            ));
        }
        if any_fail_slice {
            let mut saw_diff_block = false;
            for b in &self.evidence_blocks {
                if b.domain == "differential_oracle" {
                    saw_diff_block = true;
                    if b.overall_status != "FAIL" {
                        return Err(format!(
                            "evidence block `{}` has overall_status={:?} despite failed differential slice(s)",
                            b.domain, b.overall_status
                        ));
                    }
                }
            }
            if !saw_diff_block {
                return Err(
                    "differential_oracle evidence block required when a differential slice has overall_status=\"FAIL\""
                        .to_string(),
                );
            }
        }
        for run in &self.differential_runs {
            if !matches!(run.overall_status.as_str(), "PASS" | "FAIL" | "UNVERIFIED") {
                return Err(format!(
                    "differential slice `{}` has invalid overall_status {:?}",
                    run.suite, run.overall_status
                ));
            }
            let accounted_total = run
                .agree_count
                .checked_add(run.unsound_missed_fault_count)
                .and_then(|n| n.checked_add(run.value_mismatch_count))
                .and_then(|n| n.checked_add(run.sound_conservative_abstraction_count))
                .and_then(|n| n.checked_add(run.undeclared_ub_fault_count))
                .and_then(|n| n.checked_add(run.disclosed_gap_count))
                .and_then(|n| n.checked_add(run.degraded_count))
                .and_then(|n| n.checked_add(run.tool_error_count));
            if accounted_total != Some(run.compared_count)
                || run.panic_agreed_count > run.agree_count
                || run.expectation_mismatch_count > run.compared_count
                || run.kernel_checked_count > run.compared_count
            {
                return Err(format!(
                    "differential slice `{}` has inconsistent result accounting (compared={}, accounted={:?}, panic_agreed={}, agree={}, exp_mismatch={}, kernel={})",
                    run.suite,
                    run.compared_count,
                    accounted_total,
                    run.panic_agreed_count,
                    run.agree_count,
                    run.expectation_mismatch_count,
                    run.kernel_checked_count
                ));
            }
            let has_hard_slice_failure = run.expectation_mismatch_count > 0
                || run.tool_error_count > 0
                || run.unsound_missed_fault_count > 0
                || run.value_mismatch_count > 0
                || run.undeclared_ub_fault_count > 0;
            if has_hard_slice_failure && run.overall_status != "FAIL" {
                return Err(format!(
                    "differential slice `{}` cannot report {:?} with non-zero failure counters",
                    run.suite, run.overall_status
                ));
            }
            let has_slice_issues = has_hard_slice_failure || run.degraded_count > 0;
            if self.overall_status == "PASS" && (run.overall_status != "PASS" || has_slice_issues) {
                return Err(format!(
                    "overall_status PASS forbidden when differential slice `{}` has status={:?} expectation_mismatches={} degraded={}",
                    run.suite,
                    run.overall_status,
                    run.expectation_mismatch_count,
                    run.degraded_count
                ));
            }
            let has_miri_leg = run.legs.iter().any(|l| l == "miri_tree_borrows");
            let has_lean_leg = run
                .legs
                .iter()
                .any(|l| l == "lean_strict_verbatim" || l == "lean_compositional_itree");
            let parent_blocks_slice_pass = stale_parent
                || self.overall_status == "UNVERIFIED"
                || (self.overall_status == "FAIL" && !any_fail_slice);
            if run.overall_status == "PASS"
                && (parent_blocks_slice_pass
                    || !has_miri_leg
                    || !has_lean_leg
                    || run.compared_count == 0
                    || has_slice_issues)
            {
                return Err(format!(
                    "differential slice `{}` cannot report PASS (parent_status={:?}, legs={:?}, compared={}, degraded={}, mismatches={})",
                    run.suite,
                    self.overall_status,
                    run.legs,
                    run.compared_count,
                    run.degraded_count,
                    run.expectation_mismatch_count
                ));
            }
        }
        let mut seen_bug_ids = std::collections::BTreeSet::new();
        for bug in &self.known_bugs {
            bug.validate()?;
            if (parent_freshness == BuildFreshness::VerifiedAtHead || self.overall_status == "PASS")
                && !is_valid_git_commit_sha(&bug.introduced_sha)
            {
                return Err(format!(
                    "Known bug {} introduced_sha cannot be all-zero when build_freshness={:?}, overall_status={:?}",
                    bug.bug_id, self.build_freshness, self.overall_status
                ));
            }
            if !seen_bug_ids.insert(bug.bug_id.as_str()) {
                return Err(format!("semantic_detail contains duplicate bug_id {:?}", bug.bug_id));
            }
            if bug.mir_dialect != self.mir_dialect {
                return Err(format!(
                    "Known bug {} has mir_dialect {:?} outside detail record mir_dialect {:?}",
                    bug.bug_id, bug.mir_dialect, self.mir_dialect
                ));
            }
        }
        Ok(())
    }

    /// Write one-line `anneal-itree-semantic-detail/v1` JSONL atomically to
    /// `path`.
    pub fn write_jsonl(&self, path: &Path) -> Result<(), String> {
        self.validate_honesty()?;
        let line = serde_json::to_string(self)
            .map_err(|e| format!("serialize semantic detail JSONL: {e}"))?;
        atomic_write_text(path, &format!("{line}\n"))
    }
}

/// Export envelope for `--known-bugs-out`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct KnownBugsExport {
    pub schema: String,
    pub alpha_notice: String,
    pub repo: String,
    pub branch: String,
    pub commit_sha: String,
    pub dialect_key: String,
    pub build_freshness: String,
    pub build_exit_code: i64,
    pub provisional_count: usize,
    pub known_bugs: Vec<KnownBugRecord>,
}

impl KnownBugsExport {
    pub fn from_report_and_registry(
        report: &DifferentialReport,
        registry: &BugRegistry,
        ctx: &TelemetryContext,
    ) -> Result<Self, String> {
        validate_report_accounting(report)?;
        let (derived_freshness, derived_exit_code) =
            derive_freshness_from_report_and_ctx(report, ctx);
        let freshness = ctx.build_freshness_override.unwrap_or(derived_freshness);
        let exit_code = ctx.build_exit_code_override.unwrap_or(derived_exit_code);
        validate_registry_repo_binding(registry, &ctx.repo)?;
        let known_bugs = registry.to_known_bug_records()?;
        let export = Self {
            schema: "anneal-known-bugs/v1".to_string(),
            alpha_notice: ALPHA_BANNER_DEFAULT.to_string(),
            repo: ctx.repo.clone(),
            branch: ctx.branch.clone(),
            commit_sha: ctx.commit_sha.clone(),
            dialect_key: dialect_key_for_mode(report.lean_mode, ctx.profile_v2).to_string(),
            build_freshness: freshness.as_str().to_string(),
            build_exit_code: exit_code,
            provisional_count: registry.provisional_cases.len(),
            known_bugs,
        };
        export.validate()?;
        Ok(export)
    }

    /// Enforce every structural and lifecycle invariant on this export envelope
    /// and every embedded [`KnownBugRecord`].
    pub fn validate(&self) -> Result<(), String> {
        if self.schema != "anneal-known-bugs/v1" {
            return Err(format!("unexpected known-bugs schema {:?}", self.schema));
        }
        if self.alpha_notice != ALPHA_BANNER_DEFAULT {
            return Err(format!(
                "known_bugs_export alpha_notice must equal `{ALPHA_BANNER_DEFAULT}`, got {:?}",
                self.alpha_notice
            ));
        }
        if self.repo.trim().is_empty() || self.dialect_key.trim().is_empty() {
            return Err("known_bugs_export repo and dialect_key must be non-empty".to_string());
        }
        if !is_40_hex_sha(&self.commit_sha) {
            return Err(format!(
                "known_bugs_export commit_sha must be a 40-character hexadecimal Git SHA, got {:?}",
                self.commit_sha
            ));
        }
        let freshness = validate_freshness_and_exit_code(
            &self.build_freshness,
            self.build_exit_code,
            "known_bugs_export",
        )?;
        if freshness == BuildFreshness::VerifiedAtHead && !is_valid_git_commit_sha(&self.commit_sha)
        {
            return Err(
                "known_bugs_export commit_sha cannot be all-zero when build_freshness=verified_at_head"
                    .to_string(),
            );
        }
        let mut seen_bug_ids = std::collections::BTreeSet::new();
        for row in &self.known_bugs {
            row.validate()?;
            if freshness == BuildFreshness::VerifiedAtHead
                && !is_valid_git_commit_sha(&row.introduced_sha)
            {
                return Err(format!(
                    "known bug {} introduced_sha cannot be all-zero when build_freshness=verified_at_head",
                    row.bug_id
                ));
            }
            if !seen_bug_ids.insert(row.bug_id.as_str()) {
                return Err(format!(
                    "known_bugs_export contains duplicate bug_id {:?}",
                    row.bug_id
                ));
            }
            if row.repo != self.repo {
                return Err(format!(
                    "known bug {} has repo {:?} outside envelope repo {:?}",
                    row.bug_id, row.repo, self.repo
                ));
            }
            if row.dialect_key != self.dialect_key {
                return Err(format!(
                    "known bug {} has dialect_key {:?} outside envelope dialect_key {:?}",
                    row.bug_id, row.dialect_key, self.dialect_key
                ));
            }
        }
        Ok(())
    }

    /// Write either NDJSON (`anneal-known-bug/v1` rows with envelope
    /// provenance fields, or an `anneal-known-bugs/v1` summary line when
    /// `known_bugs` is empty) when `path` ends with `.jsonl` / `.ndjson`, or
    /// pretty JSON otherwise.
    pub fn write_to_path(&self, path: &Path) -> Result<(), String> {
        self.validate()?;
        let ext = path.extension().and_then(|e| e.to_str()).unwrap_or("");
        if ext.eq_ignore_ascii_case("jsonl") || ext.eq_ignore_ascii_case("ndjson") {
            let mut body = String::new();
            if self.known_bugs.is_empty() {
                let line = serde_json::to_string(self)
                    .map_err(|e| format!("serialize known-bugs empty NDJSON summary: {e}"))?;
                let _ = writeln!(body, "{line}");
            } else {
                #[derive(Serialize)]
                struct KnownBugNdjsonRow<'a> {
                    #[serde(flatten)]
                    record: &'a KnownBugRecord,
                    alpha_notice: &'a str,
                    commit_sha: &'a str,
                    build_freshness: &'a str,
                    build_exit_code: i64,
                    provisional_count: usize,
                }
                for row in &self.known_bugs {
                    let wrapped = KnownBugNdjsonRow {
                        record: row,
                        alpha_notice: &self.alpha_notice,
                        commit_sha: &self.commit_sha,
                        build_freshness: &self.build_freshness,
                        build_exit_code: self.build_exit_code,
                        provisional_count: self.provisional_count,
                    };
                    let line = serde_json::to_string(&wrapped)
                        .map_err(|e| format!("serialize known-bug NDJSON row: {e}"))?;
                    let _ = writeln!(body, "{line}");
                }
            }
            atomic_write_text(path, &body)
        } else {
            let body = serde_json::to_string_pretty(self)
                .map_err(|e| format!("serialize known-bugs JSON: {e}"))?;
            atomic_write_text(path, &format!("{body}\n"))
        }
    }
}

fn validate_freshness_and_exit_code(
    freshness_str: &str,
    exit_code: i64,
    context: &str,
) -> Result<BuildFreshness, String> {
    let freshness = BuildFreshness::parse(freshness_str)
        .ok_or_else(|| format!("{context} has invalid build_freshness {freshness_str:?}"))?;
    match freshness {
        BuildFreshness::VerifiedAtHead if exit_code != 0 => Err(format!(
            "{context} build_freshness \"verified_at_head\" forbids non-zero build_exit_code {exit_code}"
        )),
        BuildFreshness::FailedOrOom | BuildFreshness::TimedOut | BuildFreshness::NotRun
            if exit_code == 0 =>
        {
            Err(format!(
                "{context} build_freshness {:?} forbids zero build_exit_code",
                freshness.as_str()
            ))
        }
        _ => Ok(freshness),
    }
}

fn derive_freshness_from_report_and_ctx(
    report: &DifferentialReport,
    ctx: &TelemetryContext,
) -> (BuildFreshness, i64) {
    let has_case_tool_error =
        report.cases.iter().any(|c| matches!(c.verdict, TraceVerdict::ToolError { .. }));
    if has_case_tool_error || report.counts.tool_error > 0 {
        let has_timeout = report.cases.iter().any(|c| match &c.verdict {
            TraceVerdict::ToolError { detail, .. } => {
                let lower = detail.to_ascii_lowercase();
                lower.contains("timed out") || lower.contains("timeout")
            }
            _ => false,
        });
        if has_timeout {
            return (BuildFreshness::TimedOut, 124);
        }
        return (BuildFreshness::FailedOrOom, 1);
    }
    if report.cases.is_empty() || report.counts.total == 0 {
        return (BuildFreshness::NotRun, 2);
    }
    if !ctx.is_verified_for_commit() {
        return (BuildFreshness::Stale, 0);
    }
    (BuildFreshness::VerifiedAtHead, 0)
}

fn has_failed_metamorphic_receipt(c: &CaseReport) -> bool {
    c.metamorphic
        .as_ref()
        .is_some_and(|m| matches!(m.status, crate::outcome::MetamorphicStatus::Failed))
}

fn compute_honest_overall_status(
    report: &DifferentialReport,
    freshness: BuildFreshness,
    exit_code: i64,
) -> &'static str {
    let (case_counts, _) = DifferentialReport::expected_counts_and_categories(&report.cases);
    let has_failed_metamorphic = report.cases.iter().any(has_failed_metamorphic_receipt)
        || case_counts.metamorphic_checked
            > case_counts.metamorphic_passed.saturating_add(case_counts.metamorphic_skipped)
        || report.counts.metamorphic_checked
            > report.counts.metamorphic_passed.saturating_add(report.counts.metamorphic_skipped);
    if case_counts.unsound_accept > 0
        || report.counts.unsound_accept > 0
        || case_counts.undeclared_ub_fault > 0
        || report.counts.undeclared_ub_fault > 0
        || case_counts.expectation_mismatches > 0
        || report.counts.expectation_mismatches > 0
        || case_counts.tool_error > 0
        || report.counts.tool_error > 0
        || has_failed_metamorphic
        || (report.require_miri
            && (!report.miri_available
                || case_counts.degraded_no_miri > 0
                || report.counts.degraded_no_miri > 0))
    {
        return "FAIL";
    }
    if matches!(
        freshness,
        BuildFreshness::NotRun | BuildFreshness::FailedOrOom | BuildFreshness::TimedOut
    ) || exit_code != 0
        || freshness != BuildFreshness::VerifiedAtHead
        || report.cases.is_empty()
        || report.counts.total == 0
        || !report.miri_available
        || case_counts.degraded_no_miri > 0
        || report.counts.degraded_no_miri > 0
        || case_counts.degraded_no_lean > 0
        || report.counts.degraded_no_lean > 0
        || case_counts.metamorphic_skipped > 0
        || report.counts.metamorphic_skipped > 0
        || report.cases.iter().any(|c| c.miri.is_none() || c.lean.is_none())
    {
        return "UNVERIFIED";
    }
    "PASS"
}

fn mir_eval_leg_executed(mir_eval: Option<&AuthorityRunResult>) -> bool {
    let Some(me) = mir_eval else {
        return false;
    };
    !matches!(
        &me.outcome,
        TerminalOutcome::CaptureRefused { reason }
            if reason.starts_with("anneal-mir-eval only evaluates single-crate CapturedRust captures")
                || reason.starts_with("MIR capture artifacts unavailable")
    )
}

fn executed_legs_for_slice(lean_mode: LeanTraceMode, cases: &[&CaseReport]) -> Vec<String> {
    let mut legs = Vec::new();
    if cases.iter().any(|c| !c.rustc_dual.skipped_for_ub) {
        legs.push("rustc_o0".to_string());
        legs.push("rustc_o2".to_string());
    }
    if cases.iter().any(|c| c.miri.is_some()) {
        legs.push("miri_tree_borrows".to_string());
    }
    if cases.iter().any(|c| c.lean.is_some()) {
        legs.push(match lean_mode {
            LeanTraceMode::StrictVerbatim => "lean_strict_verbatim".to_string(),
            LeanTraceMode::CompositionalITree => "lean_compositional_itree".to_string(),
        });
    }
    if cases.iter().any(|c| mir_eval_leg_executed(c.mir_eval.as_ref())) {
        legs.push("anneal_mir_eval".to_string());
    }
    legs
}

fn is_value_only_metamorphic_divergence(c: &CaseReport, sig: &ShrinkFailureSignature) -> bool {
    if sig.mismatch_category != "metamorphic_duality"
        || sig.ref_ub_class.is_some()
        || sig.lean_ub_class.is_some()
    {
        return false;
    }
    let has_fault_or_frame_issue = |auth: Option<&AuthorityRunResult>| -> bool {
        auth.is_some_and(|a| {
            matches!(a.outcome, TerminalOutcome::FaultUb { .. })
                || !a.caller_frame_law.is_satisfied()
        })
    };
    if has_fault_or_frame_issue(c.miri.as_ref()) || has_fault_or_frame_issue(c.lean.as_ref()) {
        return false;
    }
    if !c.rustc_dual.skipped_for_ub
        && (!c.rustc_dual.o0.caller_frame_law.is_satisfied()
            || !c.rustc_dual.o2.caller_frame_law.is_satisfied())
    {
        return false;
    }
    let Some(m) = &c.metamorphic else {
        return false;
    };
    if matches!(m.called_lean.outcome, TerminalOutcome::FaultUb { .. })
        || matches!(m.inlined_lean.outcome, TerminalOutcome::FaultUb { .. })
        || !m.called_lean.caller_frame_law.is_satisfied()
        || !m.inlined_lean.caller_frame_law.is_satisfied()
    {
        return false;
    }
    // Exclude `miri_called_vs_inlined` (as well as UB and CallerFrameLaw
    // relations): `MetamorphicDualityReceipt` does not carry `twin_miri`
    // separately, so a Miri twin mismatch without explicit frame-law evidence
    // must classify conservatively under `unsound_missed_fault_count`.
    let relation_is_value_only = |rel: &str| {
        matches!(
            rel,
            "lean_called_vs_inlined"
                | "called_rustc_o0_vs_o2"
                | "inlined_rustc_o0_vs_o2"
                | "rustc_called_vs_inlined"
                | "called_rustc_vs_lean"
                | "inlined_rustc_vs_lean"
        )
    };
    if m.failed_relations.is_empty()
        || !m.failed_relations.iter().all(|rel| relation_is_value_only(rel))
    {
        return false;
    }
    let lower_detail = m.detail.to_ascii_lowercase();
    !lower_detail.contains("faultub")
        && !lower_detail.contains("detected ub")
        && !lower_detail.contains("spine mismatch")
        && !lower_detail.contains("callerframelaw")
}

fn summarize_run_slice(
    suite: &str,
    legs: &[String],
    cases: &[&CaseReport],
    require_miri: bool,
) -> DifferentialRunTelemetry {
    let mut agree_count = 0usize;
    let mut unsound_missed_fault_count = 0usize;
    let mut value_mismatch_count = 0usize;
    let mut sound_conservative_abstraction_count = 0usize;
    let mut undeclared_ub_fault_count = 0usize;
    let mut disclosed_gap_count = 0usize;
    let mut degraded_count = 0usize;
    let mut degraded_no_miri_count = 0usize;
    let mut tool_error_count = 0usize;
    let mut panic_agreed_count = 0usize;
    let mut expectation_mismatch_count = 0usize;

    for c in cases {
        if c.expectation_violation.is_some() {
            expectation_mismatch_count += 1;
        }
        match &c.verdict {
            TraceVerdict::Agree => {
                if has_failed_metamorphic_receipt(c) {
                    unsound_missed_fault_count += 1;
                } else {
                    agree_count += 1;
                    let ref_outcome =
                        c.miri.as_ref().map(|m| &m.outcome).or(if !c.rustc_dual.skipped_for_ub {
                            Some(&c.rustc_dual.o0.outcome)
                        } else {
                            None
                        });
                    if matches!(
                        ref_outcome,
                        Some(TerminalOutcome::Unwound { .. } | TerminalOutcome::Aborted { .. })
                    ) {
                        panic_agreed_count += 1;
                    }
                }
            }
            TraceVerdict::UnsoundAccept { detail } => {
                let lower_detail = detail.to_ascii_lowercase();
                let detail_blocks_value = lower_detail.contains("spine mismatch")
                    || lower_detail.contains("event interleaving")
                    || lower_detail.contains("callerframelaw");
                let is_value_mismatch = !detail_blocks_value
                    && ShrinkFailureSignature::from_case_report(c).is_some_and(|sig| {
                        let outcome_authority_mismatch = match sig.mismatch_category {
                            "terminal_outcome_mismatch" => true,
                            "rustc_o0_o2" => {
                                c.rustc_dual.skipped_for_ub
                                    || !c
                                        .rustc_dual
                                        .o0
                                        .outcome
                                        .semantically_eq(&c.rustc_dual.o2.outcome)
                            }
                            "miri_vs_rustc" => {
                                c.rustc_dual.skipped_for_ub
                                    || c.miri.as_ref().is_none_or(|m| {
                                        !m.outcome.semantically_eq(&c.rustc_dual.o0.outcome)
                                    })
                            }
                            _ => false,
                        };
                        outcome_authority_mismatch || is_value_only_metamorphic_divergence(c, &sig)
                    });
                if is_value_mismatch {
                    value_mismatch_count += 1;
                } else {
                    unsound_missed_fault_count += 1;
                }
            }
            TraceVerdict::ConservativeOverApprox { undeclared_ub_fault, .. } => {
                if *undeclared_ub_fault {
                    undeclared_ub_fault_count += 1;
                } else {
                    sound_conservative_abstraction_count += 1;
                }
            }
            TraceVerdict::DisclosedGapArtifact { .. } => {
                disclosed_gap_count += 1;
            }
            TraceVerdict::DegradedNoMiri { .. } => {
                degraded_count += 1;
                degraded_no_miri_count += 1;
            }
            TraceVerdict::DegradedNoLean { .. } => {
                degraded_count += 1;
            }
            TraceVerdict::ToolError { .. } => {
                tool_error_count += 1;
            }
        }
    }

    let has_miri_leg = legs.iter().any(|l| l == "miri_tree_borrows");
    let has_lean_leg =
        legs.iter().any(|l| l == "lean_strict_verbatim" || l == "lean_compositional_itree");
    let missing_authority = !has_miri_leg
        || !has_lean_leg
        || cases.iter().any(|c| c.miri.is_none() || c.lean.is_none());

    let has_failed_metamorphic = cases.iter().copied().any(has_failed_metamorphic_receipt);
    let has_skipped_metamorphic = cases.iter().any(|c| {
        c.metamorphic.as_ref().is_some_and(|m| {
            matches!(m.status, crate::outcome::MetamorphicStatus::SkippedConservative { .. })
        })
    });
    let overall_status = if unsound_missed_fault_count
        + value_mismatch_count
        + undeclared_ub_fault_count
        + tool_error_count
        + expectation_mismatch_count
        > 0
        || has_failed_metamorphic
        || (require_miri && degraded_no_miri_count > 0)
    {
        "FAIL"
    } else if degraded_count > 0 || cases.is_empty() || missing_authority || has_skipped_metamorphic
    {
        "UNVERIFIED"
    } else {
        "PASS"
    };

    DifferentialRunTelemetry {
        suite: suite.to_string(),
        legs: legs.to_vec(),
        compared_count: cases.len(),
        agree_count,
        unsound_missed_fault_count,
        value_mismatch_count,
        kernel_checked_count: 0,
        sound_conservative_abstraction_count,
        undeclared_ub_fault_count,
        disclosed_gap_count,
        degraded_count,
        tool_error_count,
        panic_agreed_count,
        expectation_mismatch_count,
        overall_status: overall_status.to_string(),
    }
}

/// Record witnesses 1-to-1 against `cases` using `report_index` (or verdict +
/// unmatched `case_id` fallback), ensuring a converged witness never masks a
/// distinct unshrunk failure sharing `(seed, index)` / `case_id`.
pub fn record_report_telemetry_witnesses(
    registry: &mut BugRegistry,
    cases: &[CaseReport],
    witnesses: &[WitnessArtifact],
    branch_scope: &str,
    exposed_on_main: bool,
    dialect_key: &str,
    commit_sha: &str,
) {
    let mut matched_cases = vec![false; cases.len()];
    let is_unshrunk_verdict = |v: &TraceVerdict| -> bool {
        match v {
            TraceVerdict::ToolError { authority, .. } => authority == "shrink-witness",
            TraceVerdict::UnsoundAccept { detail }
            | TraceVerdict::ConservativeOverApprox { reason: detail, .. } => {
                detail.contains("secondary shrink-witness tool error")
            }
            _ => false,
        }
    };

    for w in witnesses {
        if w.minimized_report.as_ref().is_some_and(|mr| mr.case_id != w.case_id) {
            continue;
        }
        let matched_idx = match w.report_index {
            Some(idx) => (!matched_cases.get(idx).copied().unwrap_or(true)
                && cases
                    .get(idx)
                    .is_some_and(|c| c.case_id == w.case_id && c.verdict == w.original_verdict))
            .then_some(idx),
            None => cases.iter().enumerate().position(|(idx, c)| {
                !matched_cases[idx]
                    && c.case_id == w.case_id
                    && c.verdict == w.original_verdict
                    && !is_unshrunk_verdict(&c.verdict)
            }),
        };

        let Some(idx) = matched_idx else {
            continue;
        };
        if w.minimized_report.as_ref().is_some_and(|mr| mr.case_id != cases[idx].case_id) {
            continue;
        }
        matched_cases[idx] = true;
        let rep = w.minimized_report.as_deref().unwrap_or(&cases[idx]);
        let _ = registry.record_witness(
            w,
            rep,
            branch_scope,
            exposed_on_main,
            dialect_key,
            commit_sha,
            None,
        );
    }

    for (idx, c) in cases.iter().enumerate() {
        if c.verdict.is_critical_failure() && !matched_cases[idx] {
            registry.provisional_cases.push(ProvisionalFinding {
                case_id: c.case_id.clone(),
                verdict: format!("{}", c.verdict),
                reason: "critical failure without converged 1-minimal shrink witness".to_string(),
                commit_sha: commit_sha.to_string(),
            });
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use super::*;
    use crate::{
        CaseCategory, ExpectedCaseClass, RustcDualResult,
        lean_trace_runner::LeanTraceMode,
        outcome::{AuthorityRunResult, CallerFrameLaw, TerminalOutcome, TraceVal},
        trace_observer::ObservableSpine,
    };

    fn mk_auth_ret(auth: &str, v: u32) -> AuthorityRunResult {
        AuthorityRunResult {
            authority: auth.to_string(),
            outcome: TerminalOutcome::Returned {
                ret: TraceVal::u32(v),
                mem_digest: crate::outcome::compute_boundary_mem_digest(&[]),
            },
            spine: ObservableSpine::default(),
            caller_frame_law: CallerFrameLaw::default(),
            entry_mem_digest: None,
            post_only_mem_digest: false,
            elapsed_ms: 1,
            raw_diagnostics: String::new(),
            tool_error: None,
        }
    }

    #[test]
    fn freshness_and_overall_status_derive_directly_from_cases_despite_forged_counters() {
        let sha = "a".repeat(40);
        let ctx = TelemetryContext {
            repo: "google/zerocopy".to_string(),
            branch: "main".to_string(),
            branch_scope: "main".to_string(),
            exposed_on_main: true,
            commit_sha: sha.clone(),
            commit_unix_ts: 1_700_000_000,
            environment_profile: "unit".to_string(),
            source_url: String::new(),
            profile_v2: false,
            build_freshness_override: None,
            build_exit_code_override: None,
            head_provenance_verified: true,
            discovered_head_sha: Some(sha),
        };

        // Empty cases with forged positive `counts.total` must be NotRun.
        let mut empty_forged = DifferentialReport::from_cases(
            "available",
            true,
            true,
            "unavailable",
            LeanTraceMode::CompositionalITree,
            Vec::new(),
            Vec::new(),
        );
        empty_forged.counts.total = 3;
        empty_forged.counts.agree = 3;
        let (f_empty, code_empty) = derive_freshness_from_report_and_ctx(&empty_forged, &ctx);
        assert_eq!((f_empty, code_empty), (BuildFreshness::NotRun, 2));
        assert_eq!(compute_honest_overall_status(&empty_forged, f_empty, code_empty), "UNVERIFIED");

        // ToolError case with forged `counts.tool_error = 0` must be TimedOut
        // or FailedOrOom.
        let err_case = CaseReport {
            case_id: "tool_err".to_string(),
            category: CaseCategory::FuzzGenerated,
            expected_class: ExpectedCaseClass::Agree,
            verdict: TraceVerdict::ToolError {
                authority: "lean".to_string(),
                detail: "timed out after 30s".to_string(),
            },
            expectation_violation: None,
            rustc_dual: RustcDualResult {
                o0: mk_auth_ret("rustc-O0", 1),
                o2: mk_auth_ret("rustc-O2", 1),
                parity_ok: true,
                skipped_for_ub: false,
                mismatch_detail: None,
            },
            miri: Some(mk_auth_ret("miri", 1)),
            lean: Some(mk_auth_ret("lean", 1)),
            lean_strict_probe: None,
            mir_eval: None,
            metamorphic: None,
        };
        let mut err_forged = DifferentialReport {
            miri_status: "available".to_string(),
            miri_available: true,
            require_miri: true,
            mir_eval_status: "unavailable".to_string(),
            lean_mode: LeanTraceMode::CompositionalITree,
            counts: crate::VerdictCounts { total: 1, agree: 1, ..Default::default() },
            by_category: BTreeMap::from([(CaseCategory::FuzzGenerated, 1)]),
            cases: vec![err_case],
            witnesses: Vec::new(),
        };
        let (f_err, code_err) = derive_freshness_from_report_and_ctx(&err_forged, &ctx);
        assert_eq!((f_err, code_err), (BuildFreshness::TimedOut, 124));
        assert_eq!(compute_honest_overall_status(&err_forged, f_err, code_err), "FAIL");

        // UnsoundAccept case with forged `counts.unsound_accept = 0` forces
        // FAIL.
        err_forged.cases[0].verdict =
            TraceVerdict::UnsoundAccept { detail: "missed UB".to_string() };
        let (f_ua, code_ua) = derive_freshness_from_report_and_ctx(&err_forged, &ctx);
        assert_eq!((f_ua, code_ua), (BuildFreshness::VerifiedAtHead, 0));
        assert_eq!(compute_honest_overall_status(&err_forged, f_ua, code_ua), "FAIL");
    }
}
