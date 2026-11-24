// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Typed receipt/verdict parsing and assertion helpers for Anneal tools.

use std::collections::BTreeMap;
use std::path::PathBuf;

use serde::Deserialize;
use serde_json::Value;

use crate::TestResult;
use crate::process::{ProcessOutcome, Termination};

/// Phase latency breakdown in `cargo-anneal verify` receipts.
#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
#[serde(deny_unknown_fields)]
pub struct TimingMs {
    pub capture: u64,
    pub proof_and_audit: u64,
    pub total: u64,
}

/// Typed representation of a passing `cargo-anneal verify` Schema v3 receipt.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerifySuccessReceipt {
    pub schema_version: u32,
    pub status: String,
    pub taint_reasons: Vec<String>,
    pub elaboration_sandbox: Option<String>,
    pub experimental: bool,
    pub candidate_features: Vec<String>,
    pub request_sha256: String,
    pub capture_sha256: String,
    pub capture_binary_sha256: String,
    pub toolchain_identity: Value,
    pub model_manifest_sha256: String,
    pub specification_manifest_sha256: String,
    pub correspondence_provenance: Value,
    pub scope: Value,
    pub selected: Value,
    pub census: Value,
    pub sources: Value,
    pub configuration: Value,
    pub audit: Value,
    pub timing_ms: TimingMs,
    pub assumptions: Vec<String>,
    pub deferred: Vec<String>,
    #[serde(default)]
    pub unpinned_lean: Option<Value>,
    #[serde(default)]
    pub spec_warnings: Vec<Value>,
    #[serde(default)]
    pub sorry_declarations: Option<Vec<Value>>,
    #[serde(default)]
    pub capture_shards_sha256: Option<String>,
    #[serde(default)]
    pub shards: Option<Value>,
    #[serde(default)]
    pub artifacts: Option<String>,
}

/// Typed representation of a failing `cargo-anneal verify` Schema v3 receipt.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerifyFailureReceipt {
    pub schema_version: u32,
    pub taint_reasons: Vec<String>,
    #[serde(default)]
    pub elaboration_sandbox: Option<String>,
    pub status: String,
    pub phase: String,
    pub detail: String,
    #[serde(default)]
    pub hint: Option<String>,
    #[serde(default)]
    pub artifacts: Option<Option<String>>,
}

/// Parsed `cargo-anneal verify` JSON receipt (Schema v3).
#[derive(Clone, Debug)]
pub enum VerifyReceipt {
    Verified(Box<VerifySuccessReceipt>),
    Failed(VerifyFailureReceipt),
}

impl VerifyReceipt {
    /// Parse raw JSON stdout emitted by `cargo-anneal verify`.
    pub fn from_json_slice(bytes: &[u8]) -> TestResult<Self> {
        let raw: Value = serde_json::from_slice(bytes)
            .map_err(|error| format!("parse verify receipt JSON: {error}"))?;
        let status = raw
            .get("status")
            .and_then(Value::as_str)
            .ok_or_else(|| format!("verify receipt missing string `status`: {raw}"))?;
        match status {
            "crate_verified"
            | "selected_unit_verified"
            | "tainted_crate_verified"
            | "tainted_selected_unit_verified" => {
                let parsed: VerifySuccessReceipt = serde_json::from_value(raw)
                    .map_err(|error| format!("strict parse verified receipt: {error}"))?;
                Ok(Self::Verified(Box::new(parsed)))
            }
            "unsupported" | "proof_failed" | "tool_failed" | "compiler_failed" => {
                let parsed: VerifyFailureReceipt = serde_json::from_value(raw)
                    .map_err(|error| format!("strict parse failure receipt: {error}"))?;
                Ok(Self::Failed(parsed))
            }
            other => Err(format!("unrecognized verify receipt status {other:?}")),
        }
    }

    pub fn schema_version(&self) -> u32 {
        match self {
            Self::Verified(v) => v.schema_version,
            Self::Failed(f) => f.schema_version,
        }
    }

    pub fn status(&self) -> &str {
        match self {
            Self::Verified(v) => &v.status,
            Self::Failed(f) => &f.status,
        }
    }

    pub fn taint_reasons(&self) -> &[String] {
        match self {
            Self::Verified(v) => &v.taint_reasons,
            Self::Failed(f) => &f.taint_reasons,
        }
    }
}

/// Passing `anneal-rustc-capture capture` status payload.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CaptureSuccessStatus {
    pub status: String,
    pub capture: PathBuf,
    pub lean: PathBuf,
    pub selected_count: usize,
    pub census_count: usize,
    pub source_count: usize,
    #[serde(default)]
    pub capture_shards: Option<PathBuf>,
    #[serde(default)]
    pub shard_count: Option<usize>,
}

/// Failing `anneal-rustc-capture capture` status payload.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CaptureFailureStatus {
    pub status: String,
    pub diagnostics: Vec<String>,
    pub unsupported: Vec<Value>,
}

/// Parsed `anneal-rustc-capture capture` JSON status output.
#[derive(Clone, Debug)]
pub enum CaptureStatus {
    Captured(CaptureSuccessStatus),
    Failed(CaptureFailureStatus),
}

impl CaptureStatus {
    /// Parse raw JSON stdout emitted by `anneal-rustc-capture capture`.
    pub fn from_json_slice(bytes: &[u8]) -> TestResult<Self> {
        let raw: Value = serde_json::from_slice(bytes)
            .map_err(|error| format!("parse capture status JSON: {error}"))?;
        let status = raw
            .get("status")
            .and_then(Value::as_str)
            .ok_or_else(|| format!("capture status missing string `status`: {raw}"))?;
        match status {
            "captured" => {
                let parsed: CaptureSuccessStatus = serde_json::from_value(raw)
                    .map_err(|error| format!("strict parse capture success: {error}"))?;
                Ok(Self::Captured(parsed))
            }
            "unsupported" | "compiler_failed" | "tool_failed" => {
                let parsed: CaptureFailureStatus = serde_json::from_value(raw)
                    .map_err(|error| format!("strict parse capture failure: {error}"))?;
                Ok(Self::Failed(parsed))
            }
            other => Err(format!("unrecognized capture status {other:?}")),
        }
    }

    pub fn status(&self) -> &str {
        match self {
            Self::Captured(c) => &c.status,
            Self::Failed(f) => &f.status,
        }
    }
}

/// Typed representation of `anneal-audit --json` output across Pass 1 and
/// optional Pass 2 correspondence verification.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AuditReport {
    pub graph: BTreeMap<String, Vec<Value>>,
    pub declarations: Vec<Value>,
    #[serde(rename = "kernelDeclarations")]
    pub kernel_declarations: u64,
    #[serde(rename = "replayedDeclarations")]
    pub replayed_declarations: u64,
    #[serde(rename = "checkedAlternateProofs")]
    pub checked_alternate_proofs: u64,
    #[serde(rename = "compilerOnlyNames")]
    pub compiler_only_names: u64,
    #[serde(rename = "reachableDeclarations")]
    pub reachable_declarations: u64,
    pub axioms: Vec<String>,
    pub replay: bool,
    pub toolchain: String,
    pub guarantee: String,
    #[serde(rename = "vettedModules")]
    pub vetted_modules: Vec<String>,
    #[serde(rename = "candidateFeatures")]
    pub candidate_features: BTreeMap<String, Vec<String>>,
    #[serde(default, rename = "miriReplay")]
    pub miri_replay: Option<bool>,
    #[serde(default, rename = "miriReplayedDeclarations")]
    pub miri_replayed_declarations: Option<u64>,
    #[serde(default, rename = "miriClosureReachableDeclarations")]
    pub miri_closure_reachable_declarations: Option<u64>,
    #[serde(default, rename = "miriClosureAxioms")]
    pub miri_closure_axioms: Option<Vec<String>>,
    #[serde(default, rename = "miriCommit")]
    pub miri_commit: Option<String>,
    #[serde(default, rename = "miriClosureModules")]
    pub miri_closure_modules: Option<u64>,
    #[serde(default, rename = "correspondenceReplay")]
    pub correspondence_replay: Option<bool>,
    #[serde(default, rename = "correspondenceDeclarations")]
    pub correspondence_declarations: Option<u64>,
    #[serde(default, rename = "correspondenceReplayedDeclarations")]
    pub correspondence_replayed_declarations: Option<u64>,
    #[serde(default, rename = "correspondenceReachableDeclarations")]
    pub correspondence_reachable_declarations: Option<u64>,
    #[serde(default, rename = "correspondenceAxioms")]
    pub correspondence_axioms: Option<Vec<String>>,
}

impl AuditReport {
    /// Parse JSON stdout emitted by `anneal-audit --json`.
    pub fn from_json_slice(bytes: &[u8]) -> TestResult<Self> {
        serde_json::from_slice(bytes)
            .map_err(|error| format!("strict parse anneal-audit JSON report: {error}"))
    }
}

/// Assert normal process termination with `expected_code`.
pub fn assert_outcome_exit(outcome: &ProcessOutcome, expected_code: i32) -> TestResult {
    match outcome.termination {
        Termination::Exited(status) if status.code() == Some(expected_code) => Ok(()),
        _ => Err(format!(
            "expected exit code {expected_code}: {}",
            outcome.describe()
        )),
    }
}

/// Assert a Schema v3 verification receipt succeeded cleanly with zero taint
/// and kernel replay enabled.
pub fn assert_verified_untainted(receipt: &VerifyReceipt) -> TestResult<&VerifySuccessReceipt> {
    let VerifyReceipt::Verified(v) = receipt else {
        return Err(format!("expected verified receipt, got {receipt:?}"));
    };
    if v.schema_version != 3 {
        return Err(format!(
            "expected receipt schema_version 3, got {}",
            v.schema_version
        ));
    }
    if !v.taint_reasons.is_empty() {
        return Err(format!(
            "expected untainted receipt, got taint_reasons={:?}",
            v.taint_reasons
        ));
    }
    if !matches!(
        v.status.as_str(),
        "crate_verified" | "selected_unit_verified"
    ) {
        return Err(format!(
            "expected untainted verified status, got {:?}",
            v.status
        ));
    }
    if v.audit.get("replay").and_then(Value::as_bool) != Some(true) {
        return Err(format!("expected audit.replay == true, got {}", v.audit));
    }
    Ok(v)
}

/// Assert a Schema v3 verification receipt rejected with `expected_status`,
/// optional `expected_phase`, and `detail_substr`.
pub fn assert_rejected<'a>(
    receipt: &'a VerifyReceipt,
    expected_status: &str,
    expected_phase: Option<&str>,
    detail_substr: &str,
) -> TestResult<&'a VerifyFailureReceipt> {
    let VerifyReceipt::Failed(f) = receipt else {
        return Err(format!(
            "expected rejection status {expected_status:?}, got verified receipt: {receipt:?}"
        ));
    };
    if f.schema_version != 3 {
        return Err(format!(
            "expected receipt schema_version 3, got {}",
            f.schema_version
        ));
    }
    if f.status != expected_status {
        return Err(format!(
            "expected rejection status {expected_status:?}, got {:?} ({})",
            f.status, f.detail
        ));
    }
    if let Some(phase) = expected_phase
        && f.phase != phase
    {
        return Err(format!(
            "expected rejection phase {phase:?}, got {:?} ({})",
            f.phase, f.detail
        ));
    }
    if !f.detail.contains(detail_substr) {
        return Err(format!(
            "expected rejection detail containing {detail_substr:?}, got {:?}",
            f.detail
        ));
    }
    Ok(f)
}

/// Assert `CaptureStatus` succeeded and captured at least `min_selected` roots.
pub fn assert_captured(
    status: &CaptureStatus,
    min_selected: usize,
) -> TestResult<&CaptureSuccessStatus> {
    let CaptureStatus::Captured(c) = status else {
        return Err(format!("expected captured status, got {status:?}"));
    };
    if c.selected_count < min_selected {
        return Err(format!(
            "expected at least {min_selected} selected items, got {}",
            c.selected_count
        ));
    }
    Ok(c)
}

/// Assert `CaptureStatus` failed with `expected_status` and diagnostic text
/// containing `diag_substr`.
pub fn assert_capture_rejected<'a>(
    status: &'a CaptureStatus,
    expected_status: &str,
    diag_substr: &str,
) -> TestResult<&'a CaptureFailureStatus> {
    let CaptureStatus::Failed(f) = status else {
        return Err(format!(
            "expected capture failure {expected_status:?}, got captured: {status:?}"
        ));
    };
    if f.status != expected_status {
        return Err(format!(
            "expected capture failure status {expected_status:?}, got {:?} ({:?})",
            f.status, f.diagnostics
        ));
    }
    let joined = f.diagnostics.join("\n");
    if !joined.contains(diag_substr) && !serde_json::to_string(&f.unsupported).unwrap_or_default().contains(diag_substr) {
        return Err(format!(
            "expected capture diagnostic containing {diag_substr:?}, got diagnostics={:?} unsupported={:?}",
            f.diagnostics, f.unsupported
        ));
    }
    Ok(f)
}

/// Assert `AuditReport` kernel-replayed at least `min_kernel_decls` and uses
/// only axioms from `allowed_axioms`.
pub fn assert_audit_passed(
    report: &AuditReport,
    min_kernel_decls: u64,
    allowed_axioms: &[&str],
) -> TestResult {
    if !report.replay {
        return Err("expected audit report replay == true".into());
    }
    if report.kernel_declarations < min_kernel_decls {
        return Err(format!(
            "expected at least {min_kernel_decls} kernel declarations, got {}",
            report.kernel_declarations
        ));
    }
    for ax in &report.axioms {
        if !allowed_axioms.contains(&ax.as_str()) {
            return Err(format!(
                "audit report used disallowed axiom {ax:?} (allowed: {allowed_axioms:?})"
            ));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn verify_receipt_rejects_unknown_fields_and_checks_untainted() {
        let raw_ok = br#"{
            "schema_version": 3,
            "status": "selected_unit_verified",
            "taint_reasons": [],
            "elaboration_sandbox": "linux_bwrap",
            "experimental": true,
            "candidate_features": [],
            "request_sha256": "aaa",
            "capture_sha256": "bbb",
            "capture_binary_sha256": "ccc",
            "toolchain_identity": {},
            "model_manifest_sha256": "ddd",
            "specification_manifest_sha256": "eee",
            "correspondence_provenance": {},
            "scope": {"kind": "selected_unit", "roots": ["id"]},
            "selected": [],
            "census": [],
            "sources": {},
            "configuration": {},
            "audit": {"replay": true},
            "timing_ms": {"capture": 1, "proof_and_audit": 2, "total": 3},
            "assumptions": [],
            "deferred": []
        }"#;
        let parsed = VerifyReceipt::from_json_slice(raw_ok).unwrap();
        assert_verified_untainted(&parsed).unwrap();

        let with_extra = br#"{
            "schema_version": 3,
            "status": "proof_failed",
            "taint_reasons": [],
            "phase": "audit",
            "detail": "bad",
            "rogue_field": 123
        }"#;
        assert!(VerifyReceipt::from_json_slice(with_extra).is_err());

        let compiler_failed = br#"{
            "schema_version": 3,
            "taint_reasons": [],
            "status": "compiler_failed",
            "phase": "capture",
            "detail": "rustc rejected compilation",
            "artifacts": null
        }"#;
        let parsed_cf = VerifyReceipt::from_json_slice(compiler_failed).unwrap();
        assert_rejected(&parsed_cf, "compiler_failed", Some("capture"), "rustc").unwrap();
    }

    #[test]
    fn capture_status_and_audit_report_strict_deserialization() {
        let cap = br#"{"status":"captured","capture":"/tmp/c.json","lean":"/tmp/C.lean","selected_count":2,"census_count":3,"source_count":1}"#;
        let parsed_cap = CaptureStatus::from_json_slice(cap).unwrap();
        assert_captured(&parsed_cap, 2).unwrap();

        let aud = br#"{
            "graph": {},
            "declarations": [],
            "kernelDeclarations": 10,
            "replayedDeclarations": 10,
            "checkedAlternateProofs": 0,
            "compilerOnlyNames": 0,
            "reachableDeclarations": 10,
            "axioms": ["propext"],
            "replay": true,
            "toolchain": "4.34.1",
            "guarantee": "ok",
            "vettedModules": [],
            "candidateFeatures": {}
        }"#;
        let parsed_aud = AuditReport::from_json_slice(aud).unwrap();
        assert_audit_passed(&parsed_aud, 10, &["propext"]).unwrap();
        assert!(parsed_aud.vetted_modules.is_empty());
        assert!(parsed_aud.candidate_features.is_empty());
        assert!(assert_audit_passed(&parsed_aud, 10, &[]).is_err());

        let aud_missing_tiers = br#"{
            "graph": {},
            "declarations": [],
            "kernelDeclarations": 10,
            "replayedDeclarations": 10,
            "checkedAlternateProofs": 0,
            "compilerOnlyNames": 0,
            "reachableDeclarations": 10,
            "axioms": ["propext"],
            "replay": true,
            "toolchain": "4.34.1",
            "guarantee": "ok"
        }"#;
        assert!(AuditReport::from_json_slice(aud_missing_tiers).is_err());
    }
}
