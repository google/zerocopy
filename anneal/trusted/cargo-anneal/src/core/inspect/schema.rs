// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Pure Receipt Schema v3 parsing and 14-point envelope cross-checking.

use std::collections::BTreeSet;

use serde::Serialize;
use serde_json::{Map, Value};

use crate::core::{
    digest::{is_sha256_hex, sha256_bytes},
    identifiers::is_feature_name,
    inspect::{
        profile::{
            ArtifactAxis, AssuranceProfile, AxiomAxis, ContainmentAxis, ReplayAxis, ScopeAxis,
            TaintAxis,
        },
        strict_json::{ObjectCursor, StrictJsonDom, escape_json_pointer_token},
    },
};

const EXPECTED_RECEIPT_SCHEMA_VERSION: u64 = 3;
const EXPECTED_CAPTURE_SHARDS_SCHEMA_VERSION: u64 = 1;
const ALLOWED_TAINT_ATOMS: &[&str] =
    &["sorry_in_proof", "unmodeled_unstable_features", "unpinned_lean", "unsandboxed_elaboration"];
/// Taint atom inserted by `cargo anneal verify --allow-unstable-feature`.
pub const UNSTABLE_FEATURES_TAINT: &str = "unmodeled_unstable_features";
/// Static assumption `cargo anneal verify` records under
/// [`UNSTABLE_FEATURES_TAINT`]. The feature sets live in `unstable_features`,
/// so changes to them diff there rather than in this sentence.
pub const UNSTABLE_FEATURES_ASSUMPTION: &str = "unmodeled unstable rustc features allowed by \
    operator (see unstable_features); non-interference with captured MIR semantics is \
    unverified";
const ALLOWED_SANDBOXES: &[&str] = &["linux_bwrap", "linux_landlock_seccomp", "none"];
const ALLOWED_FOUNDATION_AXIOMS: &[&str] = &["Classical.choice", "Quot.sound", "propext"];
const ALLOWED_ASSURANCE_STAGES: &[&str] = &["stage0_alpha", "stage1_audited", "stage2_hardened"];
const ALLOWED_CANDIDATE_FEATURES: &[&str] =
    &["memory", "mir_ast", "mir_semantics", "refinement", "rustc_capture", "step_result"];
const ALLOWED_SHIM_KINDS: &[&str] = &[
    "capture_driver",
    "unpinned_lean",
    "upstream_bugfix_patch",
    "append_only_spec_lemma",
    "approved_opaque",
    "assumed_seam",
    "extern_ffi_axiom",
    "rustc_pass_shim",
];
const ALLOWED_SHIM_STATUSES: &[&str] = &["proved", "tested", "assumed"];
const ALLOWED_RELATION_KINDS: &[&str] =
    &["none", "embedding", "homomorphism", "abstraction", "simulation"];
const ALLOWED_RELATION_QUALIFIERS: &[&str] = &["lock_step", "wf_stutter", "stutter"];
const ALLOWED_RELATION_DIRECTIONS: &[&str] = &["forward", "backward", "bidirectional"];
const ALLOWED_CLAIM_SHAPES: &[&str] =
    &["exists_witness", "forall_safety", "general_hyper", "subset_hyper", "termination"];
const ALLOWED_CLAIM_KINDS: &[&str] = &["exact_refines", "sound_refines", "pure_spec_agreement"];
const ALLOWED_PROVENANCE_TAINTS: &[&str] =
    &["assumed_seams_present", "choice_total_false", "vendor_upstream_patches_present"];
const ALLOWED_PROVENANCE_SCOPES: &[&str] = &["full_gate", "partial_gate"];

/// Controls how unrecognized RFC 6901 JSON pointers in a receipt are handled.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum UnknownFieldsPolicy {
    /// Warn on stderr and surface an `UNVERIFIED EXTENSIONS` banner; fails
    /// default single-receipt validator checks (`exit 1`) unless `--passive` is
    /// set (`exit 0`).
    #[default]
    Warn,
    /// Hard operational rejection in CLI (`exit 2`, or policy violation when
    /// evaluated strictly via [`ReceiptEnvelope::evaluate_policy`]) when any
    /// unrecognized JSON key is present.
    Deny,
}

/// Policy gates evaluated by `cargo anneal inspect` against a valid Receipt v3
/// envelope (`D1-A`/`D2-A` defaults enforce passing, untainted, recognized
/// single receipts unless opted out via [`PolicyRequirements::passive`]).
#[derive(Clone, Debug)]
pub struct PolicyRequirements {
    /// Fail unless the receipt reports a passing, untainted verification status
    /// without unrecognized v3 extension fields (enabled by [`Default`];
    /// disabled by [`PolicyRequirements::passive`]).
    pub check: bool,
    /// Fail unless `taint_reasons` is empty (enabled by [`Default`]; disabled
    /// by [`PolicyRequirements::passive`]).
    pub require_untainted: bool,
    /// Fail unless `scope.kind == "crate"`.
    pub require_crate_scope: bool,
    /// Fail unless `elaboration_sandbox != "none"`.
    pub require_containment: bool,
    /// Minimum required distinct passing replay kernels.
    pub require_kernel_replay: Option<u64>,
    /// Optional allowlist restricting permitted entries in `audit.axioms`.
    pub allowed_axioms: Option<BTreeSet<String>>,
    /// Admit the `unmodeled_unstable_features` taint (and no other) when
    /// every allowed and observed unstable feature belongs to this set.
    pub allowed_unstable_features: Option<BTreeSet<String>>,
    /// Fail when the receipt reports any incomplete unstable feature.
    pub forbid_incomplete_unstable_features: bool,
    /// Handling policy for unrecognized RFC 6901 JSON fields.
    pub unknown_fields: UnknownFieldsPolicy,
}

impl Default for PolicyRequirements {
    fn default() -> Self {
        Self {
            check: true,
            require_untainted: true,
            require_crate_scope: false,
            require_containment: false,
            require_kernel_replay: None,
            allowed_axioms: None,
            allowed_unstable_features: None,
            forbid_incomplete_unstable_features: false,
            unknown_fields: UnknownFieldsPolicy::Warn,
        }
    }
}

impl PolicyRequirements {
    /// Passive viewer configuration that checks envelope invariants only and
    /// does not enforce status, taint, or warn-mode unknown-field gates.
    pub fn passive() -> Self {
        Self {
            check: false,
            require_untainted: false,
            require_crate_scope: false,
            require_containment: false,
            require_kernel_replay: None,
            allowed_axioms: None,
            allowed_unstable_features: None,
            forbid_incomplete_unstable_features: false,
            unknown_fields: UnknownFieldsPolicy::Warn,
        }
    }
}

/// Typed parse/validation error distinguishing operational/malformed envelope
/// errors (`exit 2`) from valid-envelope policy rejections (`exit 1`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InspectParseError {
    /// Operational, size-limit, I/O, or malformed JSON/schema error (`exit 2`).
    Operational(String),
    /// Policy or ledger comparison failure on a valid receipt (`exit 1`).
    Policy(String),
}

impl InspectParseError {
    /// Return the stable CLI exit code (`1` for policy, `2` for operational).
    pub const fn exit_code(&self) -> i32 {
        match self {
            Self::Policy(_) => 1,
            Self::Operational(_) => 2,
        }
    }

    /// Borrow the underlying error message.
    pub fn message(&self) -> &str {
        match self {
            Self::Policy(msg) | Self::Operational(msg) => msg,
        }
    }
}

/// Typed anti-vacuity warning record from `spec_warnings`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct SpecWarningEntry {
    pub code: String,
    pub declaration: String,
    pub message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub body: Option<String>,
}

/// Typed `horizon` record (`{"kind": "unbounded"}` or
/// `{"kind": "bounded", "k": N}`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum HorizonRecord {
    Unbounded,
    Bounded { k: u64 },
    Unknown { raw_kind: String },
}

/// Typed GUTNS TCB shim record (`tcb_shims[]`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct TcbShimEntry {
    pub id: String,
    pub kind: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub commit: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub sha256: Option<String>,
    pub status: String,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub guards: Vec<String>,
}

/// Typed GUTNS model-to-system relation metadata (`model_system_relation`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ModelSystemRelation {
    pub kind: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub qualifier: Option<String>,
    pub direction: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub anchored_at: Option<String>,
    pub licensed_claim_shapes: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub unmodeled_downstream: Vec<String>,
}

/// Typed `correspondence_provenance.qualifiers` record for v3 provenance.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ProvenanceQualifiers {
    pub choice_total: bool,
    pub assumed_seams: Vec<String>,
    pub scope_kind: String,
}

/// Typed `scope.instantiations[]` monomorphized target record.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct ScopeInstantiation {
    pub path: String,
    pub args: Vec<String>,
}

/// Typed Closure element `{ "name": ..., "module": ... }` in audit metadata.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ClosureNode {
    pub name: String,
    pub module: String,
}

/// Typed source file identity `{ "relative_path": ..., "sha256": ... }`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ReceiptSourceIdentity {
    pub relative_path: String,
    pub sha256: String,
}

/// Typed selected body record (`def_id`, `path`, `body_index`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ReceiptSelectedBody {
    pub def_id: u64,
    pub path: String,
    pub body_index: u64,
}

/// Typed compiler census entry.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ReceiptCensusItem {
    pub def_id: u64,
    pub path: String,
    pub kind: String,
    pub has_body: bool,
    pub selected: bool,
    pub required: bool,
}

/// Typed phase timings (`timing_ms`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ReceiptTimingMs {
    pub capture: u64,
    pub proof_and_audit: u64,
    pub total: u64,
}

/// Typed Lean source provenance entry (`audit.sources[i]`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct AuditSourceEntry {
    pub module: String,
    pub role: String,
    pub source_sha256: String,
}

/// Typed per-shard metadata entry inside `shards.shards[]`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ReceiptShardEntry {
    pub shard_idx: u64,
    pub capture_module: String,
    pub proof_module: String,
    pub capture_sha256: String,
    pub num_bodies: u64,
    pub ast_nodes: u64,
    pub has_cycle: bool,
    pub oversized_scc: bool,
    pub scc_ids: Vec<u64>,
    pub callee_shards: Vec<u64>,
    pub global_def_id_range: [u64; 2],
    pub identities: Vec<String>,
}

/// Typed capture-sharding manifest embedded in `shards`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ReceiptShardsManifest {
    pub schema_version: u64,
    pub scope: String,
    pub total_bodies: u64,
    pub total_sccs: u64,
    pub cyclic_sccs: u64,
    pub total_shards: u64,
    pub is_lean_module: bool,
    pub id_tree_sha256: String,
    pub shards: Vec<ReceiptShardEntry>,
}

/// Parsed verified Receipt Schema v3 envelope.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SuccessReceipt {
    pub schema_version: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub assurance_stage: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub horizon: Option<HorizonRecord>,
    pub status: String,
    pub taint_reasons: Vec<String>,
    pub elaboration_sandbox: String,
    pub experimental: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub candidate_features: Option<Vec<String>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub permitted_axioms: Option<Vec<String>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub tcb_shims: Option<Vec<TcbShimEntry>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub model_system_relation: Option<ModelSystemRelation>,
    pub request_sha256: String,
    pub capture_sha256: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub capture_shards_sha256: Option<String>,
    pub capture_binary_sha256: String,
    pub model_manifest_sha256: String,
    pub specification_manifest_sha256: String,
    pub sha256_locked: Vec<String>,
    pub sha256_recorded: Vec<String>,
    pub unhashed: Vec<String>,
    pub correspondence_applicable: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub correspondence_schema_version: Option<u64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub correspondence_claim_kind: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub correspondence_permitted_axioms: Option<Vec<String>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub correspondence_model_system_relation: Option<ModelSystemRelation>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub correspondence_tcb_shims: Option<Vec<TcbShimEntry>>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub correspondence_taint_reasons: Vec<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub correspondence_qualifiers: Option<ProvenanceQualifiers>,
    pub upstream_pin_sha256: Option<String>,
    pub sysroot_foundation_manifest_sha256: Option<String>,
    pub upstream_repository: Option<String>,
    pub upstream_commit: Option<String>,
    pub upstream_lean_toolchain: Option<String>,
    pub build_lean_toolchain: Option<String>,
    pub correspondence_provenance_sha256: String,
    #[serde(skip)]
    pub correspondence_provenance_residual_sha256: String,
    pub scope_kind: String,
    pub scope_roots: Vec<String>,
    pub scope_instantiations: Vec<ScopeInstantiation>,
    pub crate_name: String,
    pub crate_type: String,
    pub panic: String,
    pub edition: String,
    pub target: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub stdlib_crate: Option<String>,
    pub selected: Vec<ReceiptSelectedBody>,
    pub census: Vec<ReceiptCensusItem>,
    pub sources: Vec<ReceiptSourceIdentity>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub audit_sources: Vec<AuditSourceEntry>,
    pub theorem: String,
    pub canonical_root: String,
    pub subject: String,
    pub specification: String,
    pub expected: String,
    pub axioms: Vec<String>,
    pub sorry_declarations: Vec<String>,
    pub top_sorry_declarations: Option<Vec<String>>,
    pub replay: bool,
    pub exact_type: bool,
    pub replayed_declarations: u64,
    pub checked_alternate_proofs: u64,
    pub audit_mode: Option<String>,
    pub kernels_passed: Vec<String>,
    pub kernels_skipped: Vec<String>,
    #[serde(skip)]
    pub has_kernels_passed: bool,
    #[serde(skip)]
    pub has_kernels_skipped: bool,
    pub paranoid_quorum: Option<bool>,
    pub subject_closure: Vec<ClosureNode>,
    pub model_closure: Vec<ClosureNode>,
    pub specification_closure: Vec<ClosureNode>,
    pub timing_ms: ReceiptTimingMs,
    pub assumptions: Vec<String>,
    pub deferred: Vec<String>,
    pub spec_warnings: Vec<SpecWarningEntry>,
    pub artifacts: Option<String>,
    pub unpinned_lean: Option<UnpinnedLeanRecord>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub shards: Option<ReceiptShardsManifest>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub unstable_features: Option<UnstableFeaturesRecord>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub stabilized_features_present: Vec<String>,
}

/// Parsed operator-allowed unstable feature record (`unstable_features`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct UnstableFeaturesRecord {
    pub allowed: Vec<String>,
    pub observed: Vec<String>,
    pub incomplete_observed: Vec<String>,
}

impl SuccessReceipt {
    /// Returns `true` when the receipt carries multi-kernel audit metadata.
    pub fn is_multi_kernel(&self) -> bool {
        self.has_kernels_passed
            || self.has_kernels_skipped
            || self.audit_mode.is_some()
            || self.paranoid_quorum.is_some()
    }
}

/// Parsed unpinned-Lean identity record (`unpinned_lean`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct UnpinnedLeanRecord {
    pub expected_toolchain: String,
    pub observed_version: String,
    pub lean_binary_sha256: String,
    pub foundation_modules: Vec<String>,
    pub sysroot_modules_sha256: String,
    pub admitted_sysroot_module_count: u64,
}

/// Parsed failure Receipt Schema v3 envelope.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct FailureReceipt {
    pub schema_version: u64,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub assurance_stage: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub horizon: Option<HorizonRecord>,
    pub taint_reasons: Vec<String>,
    pub elaboration_sandbox: Option<String>,
    pub status: String,
    pub phase: String,
    pub detail: String,
    pub hint: Option<String>,
    pub artifacts: Option<String>,
}

/// Validated Receipt v3 union.
#[allow(clippy::large_enum_variant)]
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum ParsedReceipt {
    Success(Box<SuccessReceipt>),
    Failure(FailureReceipt),
}

impl ParsedReceipt {
    pub fn status(&self) -> &str {
        match self {
            Self::Success(s) => &s.status,
            Self::Failure(f) => &f.status,
        }
    }

    pub fn taint_reasons(&self) -> &[String] {
        match self {
            Self::Success(s) => &s.taint_reasons,
            Self::Failure(f) => &f.taint_reasons,
        }
    }

    pub fn artifacts(&self) -> Option<&str> {
        match self {
            Self::Success(s) => s.artifacts.as_deref(),
            Self::Failure(f) => f.artifacts.as_deref(),
        }
    }

    pub fn is_success(&self) -> bool {
        matches!(self, Self::Success(_))
    }
}

/// Complete pure inspection result for one Receipt Schema v3 document.
#[derive(Clone, Debug, Serialize)]
pub struct ReceiptEnvelope {
    pub receipt_sha256: String,
    pub receipt: ParsedReceipt,
    pub profile: AssuranceProfile,
    pub unrecognized_fields: Vec<String>,
    pub invariant_violations: Vec<String>,
    #[serde(skip)]
    pub raw_value: Value,
}

impl ReceiptEnvelope {
    /// Evaluate policy gates (default validator mode unless `--passive`,
    /// `--require-*`, and `--unknown-fields`) against this envelope.
    pub fn evaluate_policy(&self, policy: &PolicyRequirements) -> Vec<String> {
        let mut failures = Vec::new();
        for v in &self.invariant_violations {
            failures.push(format!("envelope invariant violation: {v}"));
        }
        if !self.unrecognized_fields.is_empty()
            && (policy.unknown_fields == UnknownFieldsPolicy::Deny
                || (policy.unknown_fields == UnknownFieldsPolicy::Warn && policy.check))
        {
            failures.push(format!(
                "unrecognized receipt field(s) ({}): {}",
                if policy.unknown_fields == UnknownFieldsPolicy::Deny {
                    "rejected by --unknown-fields=deny"
                } else {
                    "unverified extensions; pass --passive to view without failing"
                },
                self.unrecognized_fields.join(", ")
            ));
        }
        match &self.receipt {
            ParsedReceipt::Failure(f) => {
                if policy.check
                    || policy.require_untainted
                    || policy.require_crate_scope
                    || policy.require_containment
                    || policy.require_kernel_replay.is_some()
                    || policy.allowed_axioms.is_some()
                    || policy.allowed_unstable_features.is_some()
                    || policy.forbid_incomplete_unstable_features
                {
                    failures.push(format!(
                        "receipt status `{}` in phase `{}` did not succeed",
                        f.status, f.phase
                    ));
                }
            }
            ParsedReceipt::Success(s) => {
                // `--allowed-unstable-features` admits exactly the unstable
                // feature taint; every other taint still fails.
                let residual_taints: Vec<&str> = s
                    .taint_reasons
                    .iter()
                    .map(String::as_str)
                    .filter(|&t| {
                        !(policy.allowed_unstable_features.is_some()
                            && t == UNSTABLE_FEATURES_TAINT)
                    })
                    .collect();
                if (policy.check || policy.require_untainted) && !residual_taints.is_empty() {
                    failures.push(format!("receipt is tainted ({})", residual_taints.join(", ")));
                }
                if let Some(permitted) = &policy.allowed_unstable_features
                    && let Some(record) = &s.unstable_features
                {
                    for (field, names) in
                        [("allowed", &record.allowed), ("observed", &record.observed)]
                    {
                        for name in names.iter().filter(|name| !permitted.contains(*name)) {
                            failures.push(format!(
                                "unstable feature `{name}` in unstable_features.{field} is \
                                 outside --allowed-unstable-features"
                            ));
                        }
                    }
                }
                if policy.forbid_incomplete_unstable_features
                    && let Some(record) = &s.unstable_features
                    && !record.incomplete_observed.is_empty()
                {
                    failures.push(format!(
                        "receipt enables incomplete unstable feature(s) ({})",
                        record.incomplete_observed.join(", ")
                    ));
                }
                if policy.require_crate_scope && s.scope_kind != "crate" {
                    failures.push(format!(
                        "receipt scope is `{}`, expected whole-crate scope `crate`",
                        s.scope_kind
                    ));
                }
                if policy.require_containment && s.elaboration_sandbox == "none" {
                    failures.push(
                        "receipt used unsandboxed elaboration (`elaboration_sandbox = none`)"
                            .to_string(),
                    );
                }
                // Under `--check` (default), require at least one passing
                // replay kernel even without `--require-kernel-replay`.
                let min_k = policy.require_kernel_replay.unwrap_or(0).max(u64::from(policy.check));
                if min_k > 0 {
                    let count = if s.is_multi_kernel() {
                        let unique: BTreeSet<&str> = s
                            .kernels_passed
                            .iter()
                            .map(|k| k.trim())
                            .filter(|k| !k.is_empty())
                            .collect();
                        unique.len() as u64
                    } else if s.replay {
                        1
                    } else {
                        0
                    };
                    if count < min_k {
                        failures.push(format!(
                            "receipt verified {count} replay kernel(s), below required {min_k}"
                        ));
                    }
                }
                if let Some(allowed) = &policy.allowed_axioms {
                    for ax in &s.axioms {
                        if !allowed.contains(ax) {
                            failures.push(format!(
                                "axiom `{ax}` is outside --allowed-axioms allowlist"
                            ));
                        }
                    }
                }
            }
        }
        failures
    }
}

/// Parse raw receipt bytes using [`StrictJsonDom`], validate the schema, run
/// all 14 cross-checks, and compute its [`AssuranceProfile`].
pub fn parse_and_validate_receipt(bytes: &[u8]) -> Result<ReceiptEnvelope, InspectParseError> {
    let receipt_sha256 = sha256_bytes(bytes);
    let raw_value = StrictJsonDom::parse(bytes).map_err(InspectParseError::Operational)?;
    let root_obj = raw_value.as_object().ok_or_else(|| {
        InspectParseError::Operational("receipt root must be a JSON object".into())
    })?;
    let mut root = ObjectCursor::root(root_obj);
    let mut unknown = Vec::new();
    let mut violations = Vec::new();

    let schema_version = root.req_u64("schema_version").map_err(InspectParseError::Operational)?;
    if schema_version != EXPECTED_RECEIPT_SCHEMA_VERSION {
        return Err(InspectParseError::Operational(format!(
            "unsupported schema_version {schema_version} (expected {EXPECTED_RECEIPT_SCHEMA_VERSION})"
        )));
    }
    let status = root.req_str("status").map_err(InspectParseError::Operational)?.to_owned();
    let taint_reasons =
        root.req_str_array("taint_reasons").map_err(InspectParseError::Operational)?;
    validate_taint_reasons(&taint_reasons, &mut violations);

    let receipt = match status.as_str() {
        "crate_verified"
        | "selected_unit_verified"
        | "tainted_crate_verified"
        | "tainted_selected_unit_verified" => ParsedReceipt::Success(Box::new(
            parse_success_receipt(
                schema_version,
                status,
                taint_reasons,
                &mut root,
                &mut unknown,
                &mut violations,
            )
            .map_err(InspectParseError::Operational)?,
        )),
        "unsupported" | "proof_failed" | "compiler_failed" | "tool_failed" => {
            ParsedReceipt::Failure(
                parse_failure_receipt(
                    schema_version,
                    status,
                    taint_reasons,
                    &mut root,
                    &mut unknown,
                    &mut violations,
                )
                .map_err(InspectParseError::Operational)?,
            )
        }
        other => {
            return Err(InspectParseError::Operational(format!(
                "unrecognized Receipt v3 status `{other}`"
            )));
        }
    };

    root.collect_unrecognized(&mut unknown);
    unknown.sort();
    unknown.dedup();
    let profile = build_profile(&receipt);

    Ok(ReceiptEnvelope {
        receipt_sha256,
        receipt,
        profile,
        unrecognized_fields: unknown,
        invariant_violations: violations,
        raw_value,
    })
}

fn validate_taint_reasons(taint_reasons: &[String], violations: &mut Vec<String>) {
    let mut prev: Option<&str> = None;
    for reason in taint_reasons {
        if !ALLOWED_TAINT_ATOMS.contains(&reason.as_str()) {
            violations.push(format!("unknown taint_reasons atom `{reason}`"));
        }
        if let Some(p) = prev
            && p >= reason.as_str()
        {
            violations.push(format!(
                "taint_reasons must be strictly sorted and duplicate-free (`{p}` before `{reason}`)"
            ));
        }
        prev = Some(reason.as_str());
    }
}

fn req_sha256(
    cursor: &mut ObjectCursor<'_>,
    key: &'static str,
    v: &mut Vec<String>,
) -> Result<String, String> {
    let ptr = cursor.child_pointer(key);
    let hex = cursor.req_str(key)?.to_owned();
    if !is_sha256_hex(&hex) {
        v.push(format!("field `{ptr}` must be a 64-character SHA-256 hex digest, got `{hex}`"));
    }
    Ok(hex)
}

fn parse_failure_receipt(
    schema_version: u64,
    status: String,
    taint_reasons: Vec<String>,
    root: &mut ObjectCursor<'_>,
    unknown: &mut Vec<String>,
    violations: &mut Vec<String>,
) -> Result<FailureReceipt, String> {
    let assurance_stage = parse_opt_assurance_stage(root, violations)?;
    let horizon = parse_opt_horizon(root, unknown, violations)?;
    let elaboration_sandbox = root.opt_str("elaboration_sandbox")?.map(str::to_owned);
    if let Some(ref sb) = elaboration_sandbox {
        if !ALLOWED_SANDBOXES.contains(&sb.as_str()) {
            violations.push(format!("unknown elaboration_sandbox `{sb}`"));
        }
        if sb == "none" && !taint_reasons.iter().any(|t| t == "unsandboxed_elaboration") {
            violations.push(
                "elaboration_sandbox == `none` requires `unsandboxed_elaboration` in taint_reasons"
                    .into(),
            );
        }
    }
    let phase = root.req_str("phase")?.to_owned();
    let detail = root.req_str("detail")?.to_owned();
    if phase.is_empty() {
        violations.push("failure receipt `phase` must be non-empty".into());
    }
    if detail.is_empty() {
        violations.push("failure receipt `detail` must be non-empty".into());
    }
    let hint = root.opt_str("hint")?.map(str::to_owned);
    let artifacts = root.opt_str("artifacts")?.map(str::to_owned);
    Ok(FailureReceipt {
        schema_version,
        assurance_stage,
        horizon,
        taint_reasons,
        elaboration_sandbox,
        status,
        phase,
        detail,
        hint,
        artifacts,
    })
}

fn parse_success_receipt(
    schema_version: u64,
    status: String,
    taint_reasons: Vec<String>,
    root: &mut ObjectCursor<'_>,
    unknown: &mut Vec<String>,
    violations: &mut Vec<String>,
) -> Result<SuccessReceipt, String> {
    let assurance_stage = parse_opt_assurance_stage(root, violations)?;
    let horizon = parse_opt_horizon(root, unknown, violations)?;
    let is_tainted_status = status.starts_with("tainted_");
    if is_tainted_status != !taint_reasons.is_empty() {
        violations.push(format!("status `{status}` contradicts taint_reasons={taint_reasons:?}"));
    }

    let elaboration_sandbox = root.req_str("elaboration_sandbox")?.to_owned();
    if !ALLOWED_SANDBOXES.contains(&elaboration_sandbox.as_str()) {
        violations.push(format!("unknown elaboration_sandbox `{elaboration_sandbox}`"));
    }
    let has_unsandboxed_taint = taint_reasons.iter().any(|t| t == "unsandboxed_elaboration");
    if (elaboration_sandbox == "none") != has_unsandboxed_taint {
        violations.push(format!(
            "elaboration_sandbox `{elaboration_sandbox}` contradicts taint_reasons `{taint_reasons:?}`"
        ));
    }

    let experimental = root.req_bool("experimental")?;
    let candidate_features = match root.opt_array("candidate_features")? {
        Some(arr) => {
            let list = parse_str_list(arr, "/candidate_features")?;
            validate_sorted_subset(
                "/candidate_features",
                &list,
                ALLOWED_CANDIDATE_FEATURES,
                violations,
            );
            if experimental != !list.is_empty() {
                violations.push(format!(
                    "`experimental` ({experimental}) disagrees with `candidate_features` ({list:?})"
                ));
            }
            Some(list)
        }
        None => None,
    };
    let permitted_axioms = match root.opt_array("permitted_axioms")? {
        Some(arr) => {
            let list = parse_str_list(arr, "/permitted_axioms")?;
            validate_permitted_axioms("/permitted_axioms", &list, violations);
            Some(list)
        }
        None => None,
    };
    let tcb_shims = match root.opt_array("tcb_shims")? {
        Some(arr) => Some(parse_tcb_shims("/tcb_shims", arr, unknown, violations)?),
        None => None,
    };
    let model_system_relation = match root.opt_obj("model_system_relation")? {
        Some(obj) => {
            Some(parse_model_system_relation("/model_system_relation", obj, unknown, violations)?)
        }
        None => None,
    };
    let request_sha256 = req_sha256(root, "request_sha256", violations)?;
    let capture_sha256 = req_sha256(root, "capture_sha256", violations)?;
    let capture_shards_sha256 = match root.opt_str("capture_shards_sha256")? {
        Some(hex) => {
            if !is_sha256_hex(hex) {
                violations.push(format!(
                    "field `/capture_shards_sha256` must be a 64-character SHA-256 hex digest, \
                     got `{hex}`"
                ));
            }
            Some(hex.to_owned())
        }
        None => None,
    };
    let capture_binary_sha256 = req_sha256(root, "capture_binary_sha256", violations)?;
    let model_manifest_sha256 = req_sha256(root, "model_manifest_sha256", violations)?;
    let specification_manifest_sha256 =
        req_sha256(root, "specification_manifest_sha256", violations)?;

    let tc_obj = root.req_obj("toolchain_identity")?;
    let mut tc = ObjectCursor::nested("/toolchain_identity", tc_obj);
    let sha256_locked = tc.req_str_array("sha256_locked")?;
    let sha256_recorded = tc.req_str_array("sha256_recorded")?;
    let unhashed = tc.req_str_array("unhashed")?;
    tc.collect_unrecognized(unknown);

    let has_unpinned_taint = taint_reasons.iter().any(|t| t == "unpinned_lean");
    if has_unpinned_taint && !sha256_locked.is_empty() {
        violations
            .push("taint `unpinned_lean` requires empty toolchain_identity.sha256_locked".into());
    } else if !has_unpinned_taint && sha256_locked.is_empty() {
        violations
            .push("pinned verification requires non-empty toolchain_identity.sha256_locked".into());
    }

    let prov_obj = root.req_obj("correspondence_provenance")?;
    let prov_summary = parse_provenance(prov_obj, has_unpinned_taint, unknown, violations)?;

    let scope_obj = root.req_obj("scope")?;
    let mut scope = ObjectCursor::nested("/scope", scope_obj);
    let scope_kind = scope.req_str("kind")?.to_owned();
    let (scope_roots, scope_instantiations) = match scope_kind.as_str() {
        "crate" => {
            if !status.ends_with("crate_verified") {
                violations.push(format!("scope.kind `crate` contradicts status `{status}`"));
            }
            (Vec::new(), Vec::new())
        }
        "selected_unit" => {
            if !status.ends_with("selected_unit_verified") {
                violations
                    .push(format!("scope.kind `selected_unit` contradicts status `{status}`"));
            }
            let roots = scope.req_str_array("roots")?;
            let instantiations = match scope.opt_array("instantiations")? {
                Some(arr) => parse_instantiations(arr, unknown)?,
                None => Vec::new(),
            };
            if roots.is_empty() && instantiations.is_empty() {
                violations.push(
                    "selected_unit scope must list at least one root or instantiation".into(),
                );
            }
            (roots, instantiations)
        }
        other => {
            return Err(format!("unrecognized scope.kind `{other}`"));
        }
    };
    scope.collect_unrecognized(unknown);

    let selected = parse_selected(root.req_array("selected")?, unknown)?;
    let census = parse_census(root.req_array("census")?, unknown)?;
    let sources = parse_sources(root.req_array("sources")?, unknown, violations)?;

    let cfg_obj = root.req_obj("configuration")?;
    let mut cfg = ObjectCursor::nested("/configuration", cfg_obj);
    let crate_name = cfg.req_str("crate_name")?.to_owned();
    let crate_type = cfg.req_str("crate_type")?.to_owned();
    let panic = cfg.req_str("panic")?.to_owned();
    let edition = cfg.req_str("edition")?.to_owned();
    let target = cfg.req_str("target")?.to_owned();
    let stdlib_crate = cfg.opt_str("stdlib_crate")?.map(str::to_owned);
    if let Some(ref sc) = stdlib_crate {
        check_trimmed_nonempty("/configuration", "stdlib_crate", sc, violations);
    }
    let mut cfg_feature_list = |key: &'static str| -> Result<Vec<String>, String> {
        let ptr = format!("/configuration/{key}");
        let Some(arr) = cfg.opt_array(key)? else {
            return Ok(Vec::new());
        };
        let list = parse_str_list(arr, &ptr)?;
        if list.is_empty() {
            violations.push(format!("`{ptr}` must be omitted rather than empty"));
        }
        validate_feature_names(&ptr, &list, violations);
        Ok(list)
    };
    let cfg_allowed_unstable = cfg_feature_list("allowed_unstable_features")?;
    let cfg_observed_unstable = cfg_feature_list("observed_unstable_features")?;
    let cfg_incomplete_unstable = cfg_feature_list("incomplete_observed_unstable_features")?;
    let stabilized_features_present = cfg_feature_list("stabilized_features_present")?;
    for known_cfg_key in [
        "crate_root",
        "cfg",
        "env",
        "opt_level",
        "debug_assertions",
        "overflow_checks",
        "mir_preserve_ub",
        "pointer_bits",
        "endian",
        "declared_source_files",
    ] {
        cfg.mark_visited(known_cfg_key);
    }
    cfg.collect_unrecognized(unknown);

    let timing_obj = root.req_obj("timing_ms")?;
    let mut timing = ObjectCursor::nested("/timing_ms", timing_obj);
    let timing_ms = ReceiptTimingMs {
        capture: timing.req_u64("capture")?,
        proof_and_audit: timing.req_u64("proof_and_audit")?,
        total: timing.req_u64("total")?,
    };
    timing.collect_unrecognized(unknown);

    let assumptions = root.req_str_array("assumptions")?;
    let deferred = root.req_str_array("deferred")?;
    if elaboration_sandbox == "none"
        && !deferred.iter().any(|d| d == "hostile Lean elaborator effects")
    {
        violations
            .push("unsandboxed run must list `hostile Lean elaborator effects` in deferred".into());
    }

    let spec_warnings = if let Some(arr) = root.opt_array("spec_warnings")? {
        parse_spec_warnings(arr, "/spec_warnings", "spec_warnings", unknown, violations)?
    } else {
        Vec::new()
    };

    let artifacts = root.opt_str("artifacts")?.map(str::to_owned);

    let top_sorry_declarations = match root.opt_array("sorry_declarations")? {
        Some(arr) => Some(parse_str_list(arr, "/sorry_declarations")?),
        None => None,
    };
    let has_sorry_taint = taint_reasons.iter().any(|t| t == "sorry_in_proof");
    if has_sorry_taint != top_sorry_declarations.is_some() {
        violations.push(
            "`sorry_in_proof` taint must match presence of top-level `sorry_declarations`".into(),
        );
    }

    let unpinned_lean = match root.opt_obj("unpinned_lean")? {
        Some(obj) => Some(parse_unpinned_obj("/unpinned_lean", obj, false, unknown, violations)?),
        None => None,
    };

    let unstable_features = match root.opt_obj("unstable_features")? {
        Some(obj) => Some(parse_unstable_features(obj, unknown, violations)?),
        None => None,
    };
    check_unstable_features_envelope(
        &taint_reasons,
        unstable_features.as_ref(),
        [&cfg_allowed_unstable, &cfg_observed_unstable, &cfg_incomplete_unstable],
        &assumptions,
        violations,
    );
    // `--stdlib-crate` conflicts with `--allow-unstable-feature` and keeps its
    // pinned feature list, so it records neither feature disclosure.
    if stdlib_crate.is_some()
        && (unstable_features.is_some() || !stabilized_features_present.is_empty())
    {
        violations.push(
            "configuration.stdlib_crate excludes unstable_features and \
             stabilized_features_present"
                .into(),
        );
    }
    if has_unpinned_taint != unpinned_lean.is_some() {
        violations
            .push("`unpinned_lean` taint must match presence of top-level `unpinned_lean`".into());
    }
    if let Some(ref shims) = tcb_shims {
        for s in shims {
            if s.kind == "capture_driver"
                && let Some(ref shim_sha) = s.sha256
                && shim_sha != &capture_binary_sha256
            {
                violations.push(format!(
                    "tcb_shims capture_driver `{}` sha256 `{shim_sha}` disagrees with capture_binary_sha256 `{capture_binary_sha256}`",
                    s.id
                ));
            }
            if s.kind == "unpinned_lean" {
                match (&unpinned_lean, &s.sha256) {
                    (None, _) => {
                        violations.push(format!(
                            "tcb_shims unpinned_lean `{}` present without top-level `unpinned_lean`",
                            s.id
                        ));
                    }
                    (Some(ul), Some(shim_sha)) if shim_sha != &ul.lean_binary_sha256 => {
                        violations.push(format!(
                            "tcb_shims unpinned_lean `{}` sha256 `{shim_sha}` disagrees with unpinned_lean.lean_binary_sha256 `{}`",
                            s.id, ul.lean_binary_sha256
                        ));
                    }
                    _ => {}
                }
            }
        }
    }

    let audit_obj = root.req_obj("audit")?;
    let mut audit = ObjectCursor::nested("/audit", audit_obj);
    // The NDJSON comparator route (`auditMode == "ndjson_comparator"`) has no
    // alternate-proof pass and records its export and kernel digests.
    let ndjson_comparator =
        audit_obj.get("auditMode").and_then(Value::as_str) == Some("ndjson_comparator");
    let theorem = audit.req_str("theorem")?.to_owned();
    let canonical_root = audit.req_str("canonicalRoot")?.to_owned();
    let subject = audit.req_str("subject")?.to_owned();
    let specification = audit.req_str("specification")?.to_owned();
    let expected = audit.req_str("expected")?.to_owned();
    let _graph = audit.req_obj("graph")?;
    let axioms = audit.req_str_array("axioms")?;
    let sorry_declarations = audit.req_str_array("sorryDeclarations")?;
    let replay = audit.req_bool("replay")?;
    let exact_type = audit.req_bool("exactType")?;
    let replayed_declarations = audit.req_u64("replayedDeclarations")?;
    let checked_alternate_proofs = if ndjson_comparator {
        audit.opt_u64("checkedAlternateProofs")?.unwrap_or(0)
    } else {
        audit.req_u64("checkedAlternateProofs")?
    };
    let subject_closure =
        parse_closure(audit.req_array("subjectClosure")?, "subjectClosure", unknown)?;
    let model_closure = parse_closure(audit.req_array("modelClosure")?, "modelClosure", unknown)?;
    let specification_closure =
        parse_closure(audit.req_array("specificationClosure")?, "specificationClosure", unknown)?;

    let bindings_obj = audit.req_obj("bindings")?;
    let mut bindings = ObjectCursor::nested("/audit/bindings", bindings_obj);
    let b_req = req_sha256(&mut bindings, "requestSha256", violations)?;
    let b_cap = req_sha256(&mut bindings, "captureSha256", violations)?;
    let b_mod = req_sha256(&mut bindings, "modelManifestSha256", violations)?;
    let b_spec = req_sha256(&mut bindings, "specificationManifestSha256", violations)?;
    bindings.collect_unrecognized(unknown);
    if b_req != request_sha256
        || b_cap != capture_sha256
        || b_mod != model_manifest_sha256
        || b_spec != specification_manifest_sha256
    {
        violations.push("audit.bindings digests differ from top-level manifest digests".into());
    }

    if !replay || !exact_type {
        violations.push(format!(
            "audit must certify replay=true and exactType=true (got replay={replay}, exactType={exact_type})"
        ));
    }
    if replayed_declarations == 0 {
        violations.push("audit.replayedDeclarations must be >= 1".into());
    }
    if subject_closure.is_empty() || model_closure.is_empty() || specification_closure.is_empty() {
        violations.push(
            "audit.{subjectClosure, modelClosure, specificationClosure} must all be non-empty"
                .into(),
        );
    }

    let (expected_v1_root, expected_v2_root) = match scope_kind.as_str() {
        "crate" => ("Trusted.MirSemantics.CrateTheorem", "Trusted.MirSemantics.CrateTheoremV2"),
        _ => ("Trusted.MirSemantics.UnitTheorem", "Trusted.MirSemantics.UnitTheoremV2"),
    };
    let is_v2_root = canonical_root == expected_v2_root;
    if canonical_root != expected_v1_root && !is_v2_root {
        violations.push(format!(
            "audit.canonicalRoot `{canonical_root}` mismatches scope `{scope_kind}` \
             (expected `{expected_v1_root}` or `{expected_v2_root}`)"
        ));
    }
    let has_v2_assumption =
        assumptions.iter().any(|a| a.starts_with("experimental Profile v2 MIR semantics"));
    if is_v2_root != has_v2_assumption {
        violations.push(format!(
            "audit.canonicalRoot `{canonical_root}` disagrees with Profile v2 `assumptions` \
             declaration"
        ));
    }
    let has_v1_assumption =
        assumptions.iter().any(|a| a.starts_with("experimental pointer-free MIR semantics"));
    if is_v2_root && has_v1_assumption {
        violations.push(format!(
            "Profile v2 `audit.canonicalRoot` `{canonical_root}` cannot retain Profile v1 \
             pointer-free `assumptions`"
        ));
    }
    if !has_unpinned_taint && canonical_root == expected_v1_root && !prov_summary.applicable {
        violations.push(
            "pinned Profile v1 verification correspondence_provenance must omit `applicable: false`"
                .into(),
        );
    } else if !has_unpinned_taint && is_v2_root && prov_summary.applicable {
        violations.push(
            "Profile v2 verification expects correspondence_provenance.applicable == false".into(),
        );
    }

    let mut uses_sorry_ax = false;
    for ax in &axioms {
        if ax == "sorryAx" {
            uses_sorry_ax = true;
        } else if !ALLOWED_FOUNDATION_AXIOMS.contains(&ax.as_str()) {
            violations.push(format!("unexpected axiom `{ax}` in audit.axioms"));
        } else if let Some(ref permitted) = permitted_axioms
            && !permitted.contains(ax)
        {
            violations.push(format!("audit.axioms entry `{ax}` is absent from permitted_axioms"));
        }
    }
    if has_sorry_taint {
        if uses_sorry_ax != !sorry_declarations.is_empty() {
            violations.push("audit.axioms (`sorryAx`) contradicts audit.sorryDeclarations".into());
        }
    } else if uses_sorry_ax || !sorry_declarations.is_empty() {
        violations.push(
            "receipt lacks `sorry_in_proof` taint despite sorryAx / sorryDeclarations".into(),
        );
    }
    if let Some(ref top) = top_sorry_declarations
        && top != &sorry_declarations
    {
        violations
            .push("top-level `sorry_declarations` differs from `audit.sorryDeclarations`".into());
    }

    let audit_unpinned = match audit.opt_obj("unpinnedLean")? {
        Some(obj) => {
            Some(parse_unpinned_obj("/audit/unpinnedLean", obj, true, unknown, violations)?)
        }
        None => None,
    };
    if has_unpinned_taint != audit_unpinned.is_some() {
        violations.push("`unpinned_lean` taint must match presence of audit.unpinnedLean".into());
    }
    if let (Some(top), Some(aud)) = (&unpinned_lean, &audit_unpinned)
        && top != aud
    {
        violations.push("top-level unpinned_lean differs from audit.unpinnedLean".into());
    }

    let audit_mode = audit.opt_str("auditMode")?.map(str::to_owned);
    if let Some(mode) = &audit_mode {
        check_trimmed_nonempty("/audit", "auditMode", mode, violations);
    }
    let (has_kernels_passed, kernels_passed) = match audit.opt_array("kernelsPassed")? {
        Some(arr) => (true, parse_str_list(arr, "/audit/kernelsPassed")?),
        None => (false, Vec::new()),
    };
    for (i, k) in kernels_passed.iter().enumerate() {
        if k.trim().is_empty() {
            violations.push(format!("field `/audit/kernelsPassed/{i}` must be a non-empty string"));
        }
    }
    let (has_kernels_skipped, kernels_skipped) = match audit.opt_array("kernelsSkipped")? {
        Some(arr) => (true, parse_skipped_kernels(arr, unknown, violations)?),
        None => (false, Vec::new()),
    };
    for (i, k) in kernels_skipped.iter().enumerate() {
        if k.trim().is_empty() {
            violations
                .push(format!("field `/audit/kernelsSkipped/{i}` must be a non-empty string"));
        }
    }
    let paranoid_quorum = match audit.get("paranoidQuorum") {
        None | Some(Value::Null) => None,
        Some(Value::Bool(b)) => Some(*b),
        Some(_) => return Err("field `/audit/paranoidQuorum` must be a boolean".into()),
    };
    let audit_spec_warnings = match audit.opt_array("specWarnings")? {
        Some(arr) => parse_spec_warnings(
            arr,
            "/audit/specWarnings",
            "audit.specWarnings",
            unknown,
            violations,
        )?,
        None => Vec::new(),
    };
    if audit_spec_warnings != spec_warnings {
        violations.push("top-level `spec_warnings` differs from `audit.specWarnings`".into());
    }
    let audit_sources = match audit.opt_array("sources")? {
        Some(arr) => parse_audit_sources(arr, unknown, violations)?,
        None => Vec::new(),
    };
    if !audit_sources.is_empty() {
        let spec_entries: Vec<(&str, &str)> = audit_sources
            .iter()
            .filter(|e| e.role == "specification")
            .map(|e| (e.module.as_str(), e.source_sha256.as_str()))
            .collect();
        if spec_entries.is_empty() {
            violations
                .push("`audit.sources` is present but contains no `specification` module".into());
        } else if let Ok(encoded_specs) = serde_json::to_vec_pretty(&spec_entries) {
            let expected_manifest = sha256_bytes(&encoded_specs);
            if !expected_manifest.eq_ignore_ascii_case(&specification_manifest_sha256) {
                violations.push(format!(
                    "`specification_manifest_sha256` ({specification_manifest_sha256}) does \
                     not match `audit.sources` specification hashes ({expected_manifest})"
                ));
            }
        }
    }
    if ndjson_comparator {
        let kernels = NdjsonKernelFacts {
            passed: &kernels_passed,
            skipped: &kernels_skipped,
            paranoid_quorum,
            sorry_used: uses_sorry_ax,
        };
        parse_ndjson_comparator_audit(&mut audit, &kernels, unknown, violations)?;
    }
    for extra in ["moduleIdentities", "toolchain"] {
        audit.mark_visited(extra);
    }
    audit.collect_unrecognized(unknown);

    let shards = match root.opt_obj("shards")? {
        Some(obj) => Some(parse_shards(obj, unknown, violations)?),
        None => None,
    };
    if capture_shards_sha256.is_some() != shards.is_some() {
        violations.push(
            "`capture_shards_sha256` and `shards` must either both be present or both be omitted"
                .into(),
        );
    }
    if let Some(ref sh) = shards {
        let expected_shard_scope = match scope_kind.as_str() {
            "crate" => "crate",
            "selected_unit" => "unit",
            _ => "",
        };
        if !expected_shard_scope.is_empty() && sh.scope != expected_shard_scope {
            violations.push(format!(
                "shards.scope `{}` disagrees with scope.kind `{scope_kind}` \
                 (expected `{expected_shard_scope}`)",
                sh.scope
            ));
        }
        if sh.total_bodies < selected.len() as u64 {
            violations.push(format!(
                "shards.total_bodies ({}) is smaller than selected body count ({})",
                sh.total_bodies,
                selected.len()
            ));
        }
        for sel in &selected {
            if sel.body_index >= sh.total_bodies {
                violations.push(format!(
                    "selected body `{}` body_index {} is out of range for shards.total_bodies {}",
                    sel.path, sel.body_index, sh.total_bodies
                ));
            }
        }
        if !audit_sources.is_empty() {
            match audit_sources.iter().find(|e| e.module == "Proof.IdTree") {
                None => {
                    violations
                        .push("sharded receipt `audit.sources` is missing `Proof.IdTree`".into());
                }
                Some(entry) => {
                    if entry.role != "proof" {
                        violations.push(format!(
                            "`audit.sources` entry `Proof.IdTree` has role `{}` \
                             (expected `proof`)",
                            entry.role
                        ));
                    }
                    if !entry.source_sha256.eq_ignore_ascii_case(&sh.id_tree_sha256) {
                        violations.push(format!(
                            "`audit.sources` `Proof.IdTree` sha256 ({}) differs from \
                             `shards.id_tree_sha256` ({})",
                            entry.source_sha256, sh.id_tree_sha256
                        ));
                    }
                }
            }
            for shard_entry in &sh.shards {
                match audit_sources.iter().find(|e| e.module == shard_entry.capture_module) {
                    None => violations.push(format!(
                        "sharded receipt `audit.sources` is missing `{}`",
                        shard_entry.capture_module
                    )),
                    Some(entry) => {
                        if entry.role != "capture" {
                            violations.push(format!(
                                "`audit.sources` entry `{}` has role `{}` (expected `capture`)",
                                entry.module, entry.role
                            ));
                        }
                        if !entry.source_sha256.eq_ignore_ascii_case(&shard_entry.capture_sha256) {
                            violations.push(format!(
                                "`audit.sources` `{}` sha256 ({}) differs from \
                                 `shards` capture_sha256 ({})",
                                entry.module, entry.source_sha256, shard_entry.capture_sha256
                            ));
                        }
                    }
                }
            }
        }
    }

    Ok(SuccessReceipt {
        schema_version,
        assurance_stage,
        horizon,
        status,
        taint_reasons,
        elaboration_sandbox,
        experimental,
        candidate_features,
        permitted_axioms,
        tcb_shims,
        model_system_relation,
        request_sha256,
        capture_sha256,
        capture_shards_sha256,
        capture_binary_sha256,
        model_manifest_sha256,
        specification_manifest_sha256,
        sha256_locked,
        sha256_recorded,
        unhashed,
        correspondence_applicable: prov_summary.applicable,
        correspondence_schema_version: prov_summary.schema_version,
        correspondence_claim_kind: prov_summary.claim_kind,
        correspondence_permitted_axioms: prov_summary.permitted_axioms,
        correspondence_model_system_relation: prov_summary.model_system_relation,
        correspondence_tcb_shims: prov_summary.tcb_shims,
        correspondence_taint_reasons: prov_summary.taint_reasons,
        correspondence_qualifiers: prov_summary.qualifiers,
        upstream_pin_sha256: prov_summary.upstream_pin_sha256,
        sysroot_foundation_manifest_sha256: prov_summary.sysroot_foundation_manifest_sha256,
        upstream_repository: prov_summary.upstream_repository,
        upstream_commit: prov_summary.upstream_commit,
        upstream_lean_toolchain: prov_summary.upstream_lean_toolchain,
        build_lean_toolchain: prov_summary.build_lean_toolchain,
        correspondence_provenance_sha256: prov_summary.digest,
        correspondence_provenance_residual_sha256: prov_summary.residual_digest,
        scope_kind,
        scope_roots,
        scope_instantiations,
        crate_name,
        crate_type,
        panic,
        edition,
        target,
        stdlib_crate,
        selected,
        census,
        sources,
        audit_sources,
        theorem,
        canonical_root,
        subject,
        specification,
        expected,
        axioms,
        sorry_declarations,
        top_sorry_declarations,
        replay,
        exact_type,
        replayed_declarations,
        checked_alternate_proofs,
        audit_mode,
        kernels_passed,
        kernels_skipped,
        has_kernels_passed,
        has_kernels_skipped,
        paranoid_quorum,
        subject_closure,
        model_closure,
        specification_closure,
        timing_ms,
        assumptions,
        deferred,
        spec_warnings,
        artifacts,
        unpinned_lean,
        shards,
        unstable_features,
        stabilized_features_present,
    })
}

struct ProvenanceSummary {
    applicable: bool,
    schema_version: Option<u64>,
    claim_kind: Option<String>,
    permitted_axioms: Option<Vec<String>>,
    model_system_relation: Option<ModelSystemRelation>,
    tcb_shims: Option<Vec<TcbShimEntry>>,
    taint_reasons: Vec<String>,
    qualifiers: Option<ProvenanceQualifiers>,
    upstream_pin_sha256: Option<String>,
    sysroot_foundation_manifest_sha256: Option<String>,
    upstream_repository: Option<String>,
    upstream_commit: Option<String>,
    upstream_lean_toolchain: Option<String>,
    build_lean_toolchain: Option<String>,
    digest: String,
    residual_digest: String,
}

const INDIVIDUALLY_DIFFED_PROVENANCE_KEYS: &[&str] = &[
    "applicable",
    "schema_version",
    "claim_kind",
    "permitted_axioms",
    "tcb_shims",
    "taint_reasons",
    "model_system_relation",
    "qualifiers",
    "upstream_pin_sha256",
    "sysroot_foundation_manifest_sha256",
    "upstream_repository",
    "upstream_commit",
    "upstream_lean_toolchain",
    "build_lean_toolchain",
];

fn canonical_object_sha256(obj: &Map<String, Value>) -> String {
    let encoded = serde_json::to_vec(obj).unwrap_or_default();
    sha256_bytes(&encoded)
}

fn canonical_residual_provenance_sha256(obj: &Map<String, Value>) -> String {
    let mut residual = Map::new();
    for (k, v) in obj {
        if !INDIVIDUALLY_DIFFED_PROVENANCE_KEYS.contains(&k.as_str()) {
            residual.insert(k.clone(), v.clone());
        }
    }
    canonical_object_sha256(&residual)
}

fn parse_provenance(
    obj: &Map<String, Value>,
    has_unpinned_taint: bool,
    unknown: &mut Vec<String>,
    violations: &mut Vec<String>,
) -> Result<ProvenanceSummary, String> {
    let digest = canonical_object_sha256(obj);
    let residual_digest = canonical_residual_provenance_sha256(obj);
    let mut prov = ObjectCursor::nested("/correspondence_provenance", obj);
    if has_unpinned_taint || obj.contains_key("applicable") {
        let applicable = prov.req_bool("applicable")?;
        if applicable {
            let msg = if has_unpinned_taint {
                "`unpinned_lean` taint expects correspondence_provenance.applicable == false"
            } else {
                "correspondence_provenance may only set `applicable` to `false` \
                 (omit it when applicable)"
            };
            violations.push(msg.into());
        }
        let reason = prov.req_str("reason")?;
        check_trimmed_nonempty("/correspondence_provenance", "reason", reason, violations);
        prov.collect_unrecognized(unknown);
        Ok(ProvenanceSummary {
            applicable,
            schema_version: None,
            claim_kind: None,
            permitted_axioms: None,
            model_system_relation: None,
            tcb_shims: None,
            taint_reasons: Vec::new(),
            qualifiers: None,
            upstream_pin_sha256: None,
            sysroot_foundation_manifest_sha256: None,
            upstream_repository: None,
            upstream_commit: None,
            upstream_lean_toolchain: None,
            build_lean_toolchain: None,
            digest,
            residual_digest,
        })
    } else {
        let sv = prov.req_u64("schema_version")?;
        if sv != 1 && sv != 3 {
            violations.push(format!(
                "unsupported correspondence_provenance.schema_version {sv} (expected 1 or 3)"
            ));
        }
        let upstream_repository = prov.req_str("upstream_repository")?.to_owned();
        let upstream_commit = prov.req_str("upstream_commit")?.to_owned();
        let upstream_lean_toolchain = prov.req_str("upstream_lean_toolchain")?.to_owned();
        let build_lean_toolchain = prov.req_str("build_lean_toolchain")?.to_owned();
        let upstream_pin_sha256 = req_sha256(&mut prov, "upstream_pin_sha256", violations)?;
        let sysroot_foundation_manifest_sha256 =
            req_sha256(&mut prov, "sysroot_foundation_manifest_sha256", violations)?;
        let (
            claim_kind,
            permitted_axioms,
            model_system_relation,
            tcb_shims,
            taint_reasons,
            qualifiers,
        ) = if sv == 3 {
            let ck = prov.req_str("claim_kind")?.to_owned();
            if !ALLOWED_CLAIM_KINDS.contains(&ck.as_str()) {
                violations.push(format!("unknown correspondence_provenance.claim_kind `{ck}`"));
            }
            let pa = prov.req_str_array("permitted_axioms")?;
            validate_permitted_axioms(
                "/correspondence_provenance/permitted_axioms",
                &pa,
                violations,
            );
            let rel_obj = prov.req_obj("model_system_relation")?;
            let rel = parse_model_system_relation(
                "/correspondence_provenance/model_system_relation",
                rel_obj,
                unknown,
                violations,
            )?;
            let shims_arr = prov.req_array("tcb_shims")?;
            let shims = parse_tcb_shims(
                "/correspondence_provenance/tcb_shims",
                shims_arr,
                unknown,
                violations,
            )?;
            let tr = prov.req_str_array("taint_reasons")?;
            validate_sorted_subset(
                "/correspondence_provenance/taint_reasons",
                &tr,
                ALLOWED_PROVENANCE_TAINTS,
                violations,
            );
            let qual_obj = prov.req_obj("qualifiers")?;
            let qual = parse_provenance_qualifiers(qual_obj, unknown, violations)?;

            validate_claim_kind_relation(&ck, &rel, violations);

            let mut patched_by_id = std::collections::BTreeMap::new();
            let pf_arr = prov.req_array("patched_files")?;
            for (i, entry) in pf_arr.iter().enumerate() {
                let obj = entry.as_object().ok_or_else(|| {
                    format!("correspondence_provenance.patched_files[{i}] must be a JSON object")
                })?;
                let ptr = format!("/correspondence_provenance/patched_files/{i}");
                let mut pc = ObjectCursor::nested(&ptr, obj);
                let path = pc.req_str("path")?.to_owned();
                check_trimmed_nonempty(&ptr, "path", &path, violations);
                let _upstream_sha = req_sha256(&mut pc, "upstream_sha256", violations)?;
                let patched_sha = req_sha256(&mut pc, "patched_sha256", violations)?;
                pc.collect_unrecognized(unknown);
                let shim_id = format!("lean-miri:{path}");
                if patched_by_id.insert(shim_id, patched_sha).is_some() {
                    violations.push(format!(
                        "duplicate correspondence_provenance.patched_files path `{path}`"
                    ));
                }
            }

            let shims_by_id: std::collections::BTreeMap<&str, &TcbShimEntry> =
                shims.iter().map(|s| (s.id.as_str(), s)).collect();
            for (shim_id, patched_sha) in &patched_by_id {
                match shims_by_id.get(shim_id.as_str()) {
                    None => violations.push(format!(
                        "correspondence_provenance.patched_files entry `{shim_id}` is missing from tcb_shims"
                    )),
                    Some(shim) => {
                        if shim.kind != "upstream_bugfix_patch" || shim.status != "assumed" {
                            violations.push(format!(
                                "correspondence_provenance.tcb_shims entry `{shim_id}` must have kind `upstream_bugfix_patch` and status `assumed`"
                            ));
                        }
                        if shim.sha256.as_deref() != Some(patched_sha.as_str()) {
                            violations.push(format!(
                                "correspondence_provenance.tcb_shims `{shim_id}` sha256 disagrees with patched_files.patched_sha256"
                            ));
                        }
                    }
                }
            }
            for shim in &shims {
                if shim.kind == "upstream_bugfix_patch" && !patched_by_id.contains_key(&shim.id) {
                    violations.push(format!(
                        "correspondence_provenance.tcb_shims upstream_bugfix_patch `{}` has no matching patched_files entry",
                        shim.id
                    ));
                }
                if shim.kind == "assumed_seam" && !qual.assumed_seams.iter().any(|s| s == &shim.id)
                {
                    violations.push(format!(
                        "correspondence_provenance.tcb_shims assumed_seam `{}` is absent from qualifiers.assumed_seams",
                        shim.id
                    ));
                }
            }
            for seam in &qual.assumed_seams {
                match shims_by_id.get(seam.as_str()) {
                    None => violations.push(format!(
                        "correspondence_provenance.qualifiers.assumed_seams entry `{seam}` is missing from tcb_shims"
                    )),
                    Some(shim) if shim.kind != "assumed_seam" || shim.status != "assumed" => {
                        violations.push(format!(
                            "correspondence_provenance.tcb_shims `{seam}` must have kind `assumed_seam` and status `assumed`"
                        ));
                    }
                    Some(_) => {}
                }
            }

            let mut expected_taints = Vec::new();
            if !qual.assumed_seams.is_empty() {
                expected_taints.push("assumed_seams_present".to_owned());
            }
            if !qual.choice_total {
                expected_taints.push("choice_total_false".to_owned());
            }
            if shims.iter().any(|s| s.kind == "upstream_bugfix_patch") {
                expected_taints.push("vendor_upstream_patches_present".to_owned());
            }
            if tr != expected_taints {
                violations.push(format!(
                    "correspondence_provenance.taint_reasons {tr:?} disagrees with expected {expected_taints:?}"
                ));
            }

            (Some(ck), Some(pa), Some(rel), Some(shims), tr, Some(qual))
        } else {
            (None, None, None, None, Vec::new(), None)
        };
        let mr_obj = prov.req_obj("minirust_upstream")?;
        parse_minirust_upstream(mr_obj, unknown, violations)?;
        for known in [
            "patched_files",
            "correspondence_adapters",
            "correspondence_proofs",
            "trusted_lean",
            "note",
        ] {
            prov.mark_visited(known);
        }
        prov.collect_unrecognized(unknown);
        Ok(ProvenanceSummary {
            applicable: true,
            schema_version: Some(sv),
            claim_kind,
            permitted_axioms,
            model_system_relation,
            tcb_shims,
            taint_reasons,
            qualifiers,
            upstream_pin_sha256: Some(upstream_pin_sha256),
            sysroot_foundation_manifest_sha256: Some(sysroot_foundation_manifest_sha256),
            upstream_repository: Some(upstream_repository),
            upstream_commit: Some(upstream_commit),
            upstream_lean_toolchain: Some(upstream_lean_toolchain),
            build_lean_toolchain: Some(build_lean_toolchain),
            digest,
            residual_digest,
        })
    }
}

fn parse_minirust_upstream(
    mr_obj: &Map<String, Value>,
    unknown: &mut Vec<String>,
    violations: &mut Vec<String>,
) -> Result<(), String> {
    const PREFIX: &str = "/correspondence_provenance/minirust_upstream";
    let mut c = ObjectCursor::nested(PREFIX, mr_obj);
    let upstream_repository = c.req_str("upstream_repository")?;
    check_trimmed_nonempty(PREFIX, "upstream_repository", upstream_repository, violations);
    let upstream_commit = c.req_str("upstream_commit")?;
    check_trimmed_nonempty(PREFIX, "upstream_commit", upstream_commit, violations);
    let _upstream_pin_sha256 = req_sha256(&mut c, "upstream_pin_sha256", violations)?;
    let _tarball_sha256 = req_sha256(&mut c, "tarball_sha256", violations)?;
    let _manifest_sha256 = req_sha256(&mut c, "manifest_sha256", violations)?;
    let file_count = c.req_u64("file_count")?;
    let files_obj = c.req_obj("files")?;
    if file_count == 0 || files_obj.len() as u64 != file_count {
        violations.push(format!(
            "correspondence_provenance.minirust_upstream.file_count ({file_count}) disagrees with files length ({})",
            files_obj.len()
        ));
    }
    for (rel, val) in files_obj {
        let escaped = escape_json_pointer_token(rel);
        if rel.trim().is_empty() || rel.trim() != rel {
            violations.push(format!(
                "correspondence_provenance.minirust_upstream.files key `{rel}` must be trimmed and non-empty"
            ));
        }
        let hex = val
            .as_str()
            .ok_or_else(|| format!("field `{PREFIX}/files/{escaped}` must be a string"))?;
        if !is_sha256_hex(hex) {
            violations.push(format!(
                "field `{PREFIX}/files/{escaped}` must be a 64-character SHA-256 hex digest, got `{hex}`"
            ));
        }
    }
    c.collect_unrecognized(unknown);
    Ok(())
}

fn parse_instantiations(
    arr: &[Value],
    unknown: &mut Vec<String>,
) -> Result<Vec<ScopeInstantiation>, String> {
    let mut out = Vec::with_capacity(arr.len());
    for (i, val) in arr.iter().enumerate() {
        let obj = val
            .as_object()
            .ok_or_else(|| format!("scope.instantiations[{i}] must be a JSON object"))?;
        let mut c = ObjectCursor::nested(format!("/scope/instantiations/{i}"), obj);
        let path = c.req_str("path")?.to_owned();
        let args = c.req_str_array("args")?;
        c.collect_unrecognized(unknown);
        out.push(ScopeInstantiation { path, args });
    }
    Ok(out)
}

fn parse_unpinned_obj(
    prefix: &str,
    obj: &Map<String, Value>,
    camel: bool,
    unknown: &mut Vec<String>,
    violations: &mut Vec<String>,
) -> Result<UnpinnedLeanRecord, String> {
    let mut c = ObjectCursor::nested(prefix, obj);
    let expected_toolchain =
        c.req_str(if camel { "expectedToolchain" } else { "expected_toolchain" })?.to_owned();
    let observed_version =
        c.req_str(if camel { "observedVersion" } else { "observed_version" })?.to_owned();
    let lean_binary_sha256 = req_sha256(
        &mut c,
        if camel { "leanBinarySha256" } else { "lean_binary_sha256" },
        violations,
    )?;
    let foundation_modules =
        c.req_str_array(if camel { "foundationModules" } else { "foundation_modules" })?;
    let sysroot_modules_sha256 = req_sha256(
        &mut c,
        if camel { "sysrootModulesSha256" } else { "sysroot_modules_sha256" },
        violations,
    )?;
    let admitted_sysroot_module_count = c.req_u64(if camel {
        "admittedSysrootModuleCount"
    } else {
        "admitted_sysroot_module_count"
    })?;
    c.collect_unrecognized(unknown);
    Ok(UnpinnedLeanRecord {
        expected_toolchain,
        observed_version,
        lean_binary_sha256,
        foundation_modules,
        sysroot_modules_sha256,
        admitted_sysroot_module_count,
    })
}

fn parse_selected(
    arr: &[Value],
    unknown: &mut Vec<String>,
) -> Result<Vec<ReceiptSelectedBody>, String> {
    arr.iter()
        .enumerate()
        .map(|(i, val)| {
            let obj =
                val.as_object().ok_or_else(|| format!("selected[{i}] must be a JSON object"))?;
            let mut c = ObjectCursor::nested(format!("/selected/{i}"), obj);
            let item = ReceiptSelectedBody {
                def_id: c.req_u64("def_id")?,
                path: c.req_str("path")?.to_owned(),
                body_index: c.req_u64("body_index")?,
            };
            c.collect_unrecognized(unknown);
            Ok(item)
        })
        .collect()
}

fn parse_census(
    arr: &[Value],
    unknown: &mut Vec<String>,
) -> Result<Vec<ReceiptCensusItem>, String> {
    arr.iter()
        .enumerate()
        .map(|(i, val)| {
            let obj =
                val.as_object().ok_or_else(|| format!("census[{i}] must be a JSON object"))?;
            let mut c = ObjectCursor::nested(format!("/census/{i}"), obj);
            let item = ReceiptCensusItem {
                def_id: c.req_u64("def_id")?,
                path: c.req_str("path")?.to_owned(),
                kind: c.req_str("kind")?.to_owned(),
                has_body: c.req_bool("has_body")?,
                selected: c.req_bool("selected")?,
                required: c.req_bool("required")?,
            };
            c.collect_unrecognized(unknown);
            Ok(item)
        })
        .collect()
}

fn parse_sources(
    arr: &[Value],
    unknown: &mut Vec<String>,
    violations: &mut Vec<String>,
) -> Result<Vec<ReceiptSourceIdentity>, String> {
    arr.iter()
        .enumerate()
        .map(|(i, val)| {
            let obj =
                val.as_object().ok_or_else(|| format!("sources[{i}] must be a JSON object"))?;
            let mut c = ObjectCursor::nested(format!("/sources/{i}"), obj);
            let relative_path = c.req_str("relative_path")?.to_owned();
            let sha256 = req_sha256(&mut c, "sha256", violations)?;
            c.collect_unrecognized(unknown);
            Ok(ReceiptSourceIdentity { relative_path, sha256 })
        })
        .collect()
}

const ALLOWED_AUDIT_SOURCE_ROLES: &[&str] =
    &["model", "specification", "capture", "expected", "proof"];

fn parse_audit_sources(
    arr: &[Value],
    unknown: &mut Vec<String>,
    violations: &mut Vec<String>,
) -> Result<Vec<AuditSourceEntry>, String> {
    let mut seen_modules = BTreeSet::new();
    arr.iter()
        .enumerate()
        .map(|(i, val)| {
            let obj = val
                .as_object()
                .ok_or_else(|| format!("audit.sources[{i}] must be a JSON object"))?;
            let mut c = ObjectCursor::nested(format!("/audit/sources/{i}"), obj);
            let module = c.req_str("module")?.to_owned();
            let valid_ident = !module.is_empty()
                && module.split('.').all(|seg| {
                    !seg.is_empty() && seg.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_')
                });
            if !valid_ident {
                violations
                    .push(format!("audit.sources[{i}].module `{module}` is not a valid module"));
            } else if !seen_modules.insert(module.clone()) {
                violations.push(format!("duplicate module `{module}` in `audit.sources`"));
            }
            let role = c.req_str("role")?.to_owned();
            if !ALLOWED_AUDIT_SOURCE_ROLES.contains(&role.as_str()) {
                violations.push(format!("unknown audit.sources[{i}].role `{role}`"));
            }
            let source_sha256 = req_sha256(&mut c, "sourceSha256", violations)?;
            if let Some(artifacts) = c.opt_array("artifacts")? {
                for (j, art) in artifacts.iter().enumerate() {
                    let art_obj = art.as_object().ok_or_else(|| {
                        format!("audit.sources[{i}].artifacts[{j}] must be a JSON object")
                    })?;
                    let mut ac =
                        ObjectCursor::nested(format!("/audit/sources/{i}/artifacts/{j}"), art_obj);
                    let _ = req_sha256(&mut ac, "sha256", violations)?;
                    ac.collect_unrecognized(unknown);
                }
            }
            c.collect_unrecognized(unknown);
            Ok(AuditSourceEntry { module, role, source_sha256 })
        })
        .collect()
}

fn parse_closure(
    arr: &[Value],
    label: &str,
    unknown: &mut Vec<String>,
) -> Result<Vec<ClosureNode>, String> {
    arr.iter()
        .enumerate()
        .map(|(i, val)| {
            let obj = val
                .as_object()
                .ok_or_else(|| format!("audit.{label}[{i}] must be a JSON object"))?;
            let mut c = ObjectCursor::nested(format!("/audit/{label}/{i}"), obj);
            let item = ClosureNode {
                name: c.req_str("name")?.to_owned(),
                module: c.req_str("module")?.to_owned(),
            };
            c.collect_unrecognized(unknown);
            Ok(item)
        })
        .collect()
}

fn parse_spec_warnings(
    arr: &[Value],
    ptr_prefix: &str,
    label: &str,
    unknown: &mut Vec<String>,
    violations: &mut Vec<String>,
) -> Result<Vec<SpecWarningEntry>, String> {
    arr.iter()
        .enumerate()
        .map(|(i, val)| {
            let obj =
                val.as_object().ok_or_else(|| format!("{label}[{i}] must be a JSON object"))?;
            let mut c = ObjectCursor::nested(format!("{ptr_prefix}/{i}"), obj);
            let code = c.req_str("code")?.to_owned();
            let declaration = c.req_str("declaration")?.to_owned();
            let message = c.req_str("message")?.to_owned();
            let body = c.opt_str("body")?.map(str::to_owned);
            c.collect_unrecognized(unknown);
            if code.is_empty() || declaration.is_empty() || message.is_empty() {
                violations.push(format!("{label}[{i}] contains empty required field"));
            }
            if body.as_deref().is_some_and(str::is_empty) {
                violations.push(format!("{label}[{i}].body must not be empty"));
            }
            Ok(SpecWarningEntry { code, declaration, message, body })
        })
        .collect()
}

/// Record a violation unless `names` are strictly sorted `#![feature(...)]`
/// identifiers of the form `[a-z][a-z0-9_]*`.
fn validate_feature_names(ptr: &str, names: &[String], violations: &mut Vec<String>) {
    for name in names {
        if !is_feature_name(name) {
            violations.push(format!("invalid feature name `{name}` in `{ptr}`"));
        }
    }
    if names.windows(2).any(|pair| pair[0] >= pair[1]) {
        violations.push(format!("`{ptr}` must be strictly sorted and duplicate-free"));
    }
}

fn parse_unstable_features(
    obj: &Map<String, Value>,
    unknown: &mut Vec<String>,
    violations: &mut Vec<String>,
) -> Result<UnstableFeaturesRecord, String> {
    let mut c = ObjectCursor::nested("/unstable_features", obj);
    let allowed = c.req_str_array("allowed")?;
    let observed = c.req_str_array("observed")?;
    let incomplete_observed = c.req_str_array("incomplete_observed")?;
    c.collect_unrecognized(unknown);
    validate_feature_names("/unstable_features/allowed", &allowed, violations);
    validate_feature_names("/unstable_features/observed", &observed, violations);
    validate_feature_names(
        "/unstable_features/incomplete_observed",
        &incomplete_observed,
        violations,
    );
    if allowed.is_empty() {
        violations.push("`/unstable_features/allowed` must be non-empty".into());
    }
    for name in observed.iter().filter(|name| !allowed.contains(name)) {
        violations.push(format!("unstable_features.observed `{name}` is not allowed"));
    }
    for name in incomplete_observed.iter().filter(|name| !observed.contains(name)) {
        violations.push(format!("unstable_features.incomplete_observed `{name}` is not observed"));
    }
    Ok(UnstableFeaturesRecord { allowed, observed, incomplete_observed })
}

/// Cross-check the `unmodeled_unstable_features` taint against the top-level
/// `unstable_features` record, the capture `configuration` feature lists
/// (`allowed`, `observed`, `incomplete_observed`, each omitted when empty),
/// and the static assumption.
fn check_unstable_features_envelope(
    taint_reasons: &[String],
    record: Option<&UnstableFeaturesRecord>,
    configuration: [&Vec<String>; 3],
    assumptions: &[String],
    violations: &mut Vec<String>,
) {
    let tainted = taint_reasons.iter().any(|t| t == UNSTABLE_FEATURES_TAINT);
    if tainted != record.is_some() {
        violations.push(
            "`unmodeled_unstable_features` taint must match presence of top-level \
             `unstable_features`"
                .into(),
        );
    }
    let empty = Vec::new();
    let top = record
        .map_or([&empty, &empty, &empty], |r| [&r.allowed, &r.observed, &r.incomplete_observed]);
    for ((field, top), cfg) in
        ["allowed", "observed", "incomplete_observed"].into_iter().zip(top).zip(configuration)
    {
        if top != cfg {
            violations.push(format!(
                "unstable_features.{field} disagrees with the capture configuration"
            ));
        }
    }
    if tainted != assumptions.iter().any(|a| a == UNSTABLE_FEATURES_ASSUMPTION) {
        violations.push(
            "`unmodeled_unstable_features` taint must match the unstable-features assumption"
                .into(),
        );
    }
}

/// Parse `audit.kernelsSkipped`: each entry names a skipped kernel, either as
/// a string or, as the NDJSON comparator records it, as `{kernel, reason}`
/// with a non-empty reason.
fn parse_skipped_kernels(
    arr: &[Value],
    unknown: &mut Vec<String>,
    violations: &mut Vec<String>,
) -> Result<Vec<String>, String> {
    let mut kernels = Vec::with_capacity(arr.len());
    for (i, val) in arr.iter().enumerate() {
        let ptr = format!("/audit/kernelsSkipped/{i}");
        match val {
            Value::String(kernel) => kernels.push(kernel.clone()),
            Value::Object(obj) => {
                let mut entry = ObjectCursor::nested(&ptr, obj);
                let kernel = entry.req_str("kernel")?.to_owned();
                let reason = entry.req_str("reason")?;
                if reason.trim().is_empty() {
                    violations.push(format!("field `{ptr}/reason` must be a non-empty string"));
                }
                entry.collect_unrecognized(unknown);
                kernels.push(kernel);
            }
            _ => return Err(format!("element `{ptr}` must be a string or an object")),
        }
    }
    Ok(kernels)
}

/// Number of pinned `Init` primitives the NDJSON comparator exports and
/// checks (`ndjson_comparator::PINNED_INIT_PRIMITIVES`).
pub(crate) const NDJSON_PINNED_PRIMITIVE_COUNT: u64 = 39;

/// Phase timings, in milliseconds, of an NDJSON comparator run.
const NDJSON_TIMING_FIELDS: &[&str] = &[
    "initPrimitives",
    "targetConsts",
    "sysrootPins",
    "exportExpected",
    "exportProof",
    "rustCompare",
    "nanoda",
    "conRon",
    "paranoidQuorum",
    "total",
];

/// The kernels an NDJSON comparator receipt records, as already parsed.
struct NdjsonKernelFacts<'a> {
    passed: &'a [String],
    skipped: &'a [String],
    paranoid_quorum: Option<bool>,
    sorry_used: bool,
}

/// Validate the fields only the NDJSON comparator route records (its export
/// and declaration counts, the SHA-256 digests of its exports and of the
/// comparator and kernel binaries, and its phase timings) and the invariants
/// `validate_ndjson_verdict` enforces when emitting them: all pinned
/// primitives checked; `nanoda_bin` passed, and `con-ron` too unless the
/// proof uses `sorryAx`; under `paranoidQuorum`, `lean4lean` (and, without
/// `sorryAx`, `con-leche`) passed with their digests, and neither otherwise;
/// and no kernel both passed and skipped.
fn parse_ndjson_comparator_audit(
    audit: &mut ObjectCursor<'_>,
    kernels: &NdjsonKernelFacts<'_>,
    unknown: &mut Vec<String>,
    violations: &mut Vec<String>,
) -> Result<(), String> {
    let expected_cone_declarations = audit.req_u64("expectedConeDeclarations")?;
    let pinned_primitives_count = audit.req_u64("pinnedPrimitivesCount")?;
    audit.req_u64("sysrootPinnedDeclarations")?;
    if expected_cone_declarations == 0 {
        violations.push("audit.expectedConeDeclarations must be >= 1".into());
    }
    if pinned_primitives_count != NDJSON_PINNED_PRIMITIVE_COUNT {
        violations.push(format!(
            "audit.pinnedPrimitivesCount must be {NDJSON_PINNED_PRIMITIVE_COUNT}, got \
             {pinned_primitives_count}"
        ));
    }
    for key in [
        "expectedConeSha256",
        "proofNdjsonSha256",
        "initPrimitivesSha256",
        "sysrootPinsSha256",
        "leanexportSha256",
        "nanodaBinSha256",
        "conRonSha256",
    ] {
        req_sha256(audit, key, violations)?;
    }
    let mut quorum_digests = [false; 2];
    for (present, key) in quorum_digests.iter_mut().zip(["conLecheSha256", "lean4leanSha256"]) {
        let ptr = audit.child_pointer(key);
        if let Some(hex) = audit.opt_str(key)? {
            *present = true;
            if !is_sha256_hex(hex) {
                violations.push(format!(
                    "field `{ptr}` must be a 64-character SHA-256 hex digest, got `{hex}`"
                ));
            }
        }
    }
    let [con_leche_digest, lean4lean_digest] = quorum_digests;

    let timing_obj = audit.req_obj("timingMs")?;
    let mut timing = ObjectCursor::nested("/audit/timingMs", timing_obj);
    for &key in NDJSON_TIMING_FIELDS {
        timing.req_u64(key)?;
    }
    timing.collect_unrecognized(unknown);

    let passed = |k: &str| kernels.passed.iter().any(|p| p == k);
    for (i, k) in kernels.passed.iter().chain(kernels.skipped).enumerate() {
        if !["nanoda_bin", "con-ron", "con-leche", "lean4lean"].contains(&k.as_str()) {
            violations.push(format!("unknown NDJSON comparator kernel `{k}`"));
        }
        if kernels.passed.iter().chain(kernels.skipped).take(i).any(|p| p == k) {
            violations.push(format!("kernel `{k}` is recorded more than once"));
        }
    }
    if !passed("nanoda_bin") {
        violations.push("NDJSON comparator receipt lacks a passing `nanoda_bin`".into());
    }
    if !kernels.sorry_used && !passed("con-ron") {
        violations.push("NDJSON comparator receipt lacks a passing `con-ron`".into());
    }
    match kernels.paranoid_quorum {
        None => violations.push("NDJSON comparator receipt lacks `audit.paranoidQuorum`".into()),
        Some(true) => {
            if !passed("lean4lean") || !lean4lean_digest {
                violations
                    .push("`paranoidQuorum` requires a passing `lean4lean` and its digest".into());
            }
            if !kernels.sorry_used && (!passed("con-leche") || !con_leche_digest) {
                violations
                    .push("`paranoidQuorum` requires a passing `con-leche` and its digest".into());
            }
        }
        Some(false) => {
            let recorded = |k: &str| passed(k) || kernels.skipped.iter().any(|s| s == k);
            if recorded("con-leche")
                || recorded("lean4lean")
                || con_leche_digest
                || lean4lean_digest
            {
                violations
                    .push("quorum kernels or digests are recorded without `paranoidQuorum`".into());
            }
        }
    }
    Ok(())
}

fn parse_str_list(arr: &[Value], ptr: &str) -> Result<Vec<String>, String> {
    arr.iter()
        .enumerate()
        .map(|(i, val)| {
            val.as_str()
                .map(str::to_owned)
                .ok_or_else(|| format!("element `{ptr}/{i}` must be a string"))
        })
        .collect()
}

fn parse_u64_list(arr: &[Value], ptr: &str) -> Result<Vec<u64>, String> {
    arr.iter()
        .enumerate()
        .map(|(i, val)| {
            val.as_u64().ok_or_else(|| format!("element `{ptr}/{i}` must be a non-negative integer"))
        })
        .collect()
}

fn parse_shards(
    obj: &Map<String, Value>,
    unknown: &mut Vec<String>,
    violations: &mut Vec<String>,
) -> Result<ReceiptShardsManifest, String> {
    let mut c = ObjectCursor::nested("/shards", obj);
    let schema_version = c.req_u64("schema_version")?;
    if schema_version != EXPECTED_CAPTURE_SHARDS_SCHEMA_VERSION {
        violations.push(format!(
            "unsupported shards.schema_version {schema_version} \
             (expected {EXPECTED_CAPTURE_SHARDS_SCHEMA_VERSION})"
        ));
    }
    let scope = c.req_str("scope")?.to_owned();
    if scope != "crate" && scope != "unit" {
        violations.push(format!("unknown shards.scope `{scope}` (expected `crate` or `unit`)"));
    }
    let total_bodies = c.req_u64("total_bodies")?;
    if total_bodies == 0 {
        violations.push("shards.total_bodies must be >= 1".into());
    }
    let total_sccs = c.req_u64("total_sccs")?;
    if total_sccs == 0 || total_sccs > total_bodies {
        violations.push(format!(
            "shards.total_sccs ({total_sccs}) is invalid for total_bodies ({total_bodies})"
        ));
    }
    let cyclic_sccs = c.req_u64("cyclic_sccs")?;
    if cyclic_sccs > total_sccs {
        violations.push(format!(
            "shards.cyclic_sccs ({cyclic_sccs}) exceeds shards.total_sccs ({total_sccs})"
        ));
    }
    let total_shards = c.req_u64("total_shards")?;
    let is_lean_module = c.req_bool("is_lean_module")?;
    if !is_lean_module {
        violations.push("shards.is_lean_module must be true".into());
    }
    let id_tree_sha256 = req_sha256(&mut c, "id_tree_sha256", violations)?;
    let shards_arr = c.req_array("shards")?;
    if total_shards == 0 || total_shards != shards_arr.len() as u64 {
        violations.push(format!(
            "shards.total_shards ({total_shards}) disagrees with shards array length ({})",
            shards_arr.len()
        ));
    }

    let mut parsed_shards = Vec::with_capacity(shards_arr.len());
    let mut seen_sccs = BTreeSet::new();
    let mut seen_identities = BTreeSet::new();
    let mut cyclic_shards = 0u64;
    let mut cyclic_shard_sccs = 0u64;
    let mut cursor = 0u64;
    for (i, val) in shards_arr.iter().enumerate() {
        let entry_obj = val
            .as_object()
            .ok_or_else(|| format!("shards.shards[{i}] must be a JSON object"))?;
        let ptr = format!("/shards/shards/{i}");
        let mut sc = ObjectCursor::nested(&ptr, entry_obj);
        let shard_idx = sc.req_u64("shard_idx")?;
        if shard_idx != i as u64 {
            violations.push(format!(
                "shards.shards[{i}].shard_idx ({shard_idx}) is out of order (expected {i})"
            ));
        }
        let capture_module = sc.req_str("capture_module")?.to_owned();
        let expected_cap = format!("Captured.Shard_{i:03}");
        if capture_module != expected_cap {
            violations.push(format!(
                "shards.shards[{i}].capture_module `{capture_module}` != `{expected_cap}`"
            ));
        }
        let proof_module = sc.req_str("proof_module")?.to_owned();
        let expected_proof = format!("Proof.Shard_{i:03}");
        if proof_module != expected_proof {
            violations.push(format!(
                "shards.shards[{i}].proof_module `{proof_module}` != `{expected_proof}`"
            ));
        }
        let capture_sha256 = req_sha256(&mut sc, "capture_sha256", violations)?;
        let num_bodies = sc.req_u64("num_bodies")?;
        let ast_nodes = sc.req_u64("ast_nodes")?;
        let has_cycle = sc.req_bool("has_cycle")?;
        let oversized_scc = sc.req_bool("oversized_scc")?;
        let scc_ids = parse_u64_list(sc.req_array("scc_ids")?, &format!("{ptr}/scc_ids"))?;
        let callee_shards =
            parse_u64_list(sc.req_array("callee_shards")?, &format!("{ptr}/callee_shards"))?;
        let range_vals = parse_u64_list(
            sc.req_array("global_def_id_range")?,
            &format!("{ptr}/global_def_id_range"),
        )?;
        if range_vals.len() != 2 {
            return Err(format!("field `{ptr}/global_def_id_range` must have length 2"));
        }
        let global_def_id_range = [range_vals[0], range_vals[1]];
        let identities = sc.req_str_array("identities")?;
        sc.collect_unrecognized(unknown);

        if num_bodies == 0 || num_bodies != identities.len() as u64 {
            violations.push(format!(
                "shards.shards[{i}].num_bodies ({num_bodies}) disagrees with identities length ({})",
                identities.len()
            ));
        }
        for ident in &identities {
            if ident.is_empty() {
                violations.push(format!("shards.shards[{i}].identities contains an empty entry"));
            } else if !seen_identities.insert(ident.clone()) {
                violations.push(format!("duplicate identity `{ident}` across shards"));
            }
        }
        if scc_ids.is_empty() || scc_ids.len() as u64 > num_bodies {
            violations.push(format!(
                "shards.shards[{i}].scc_ids count ({}) is invalid for num_bodies ({num_bodies})",
                scc_ids.len()
            ));
        }
        if oversized_scc && scc_ids.len() != 1 {
            violations.push(format!(
                "shards.shards[{i}] marks oversized_scc with {} SCCs (expected 1)",
                scc_ids.len()
            ));
        }
        for &scc_id in &scc_ids {
            if scc_id >= total_sccs {
                violations.push(format!(
                    "shards.shards[{i}] references out-of-range scc_id {scc_id} \
                     (total_sccs={total_sccs})"
                ));
            } else if !seen_sccs.insert(scc_id) {
                violations.push(format!("shards.shards[{i}] duplicates scc_id {scc_id}"));
            }
        }
        if has_cycle {
            cyclic_shards = cyclic_shards.saturating_add(1);
            cyclic_shard_sccs = cyclic_shard_sccs.saturating_add(scc_ids.len() as u64);
        }
        if num_bodies > 0 {
            let expected_end = cursor.checked_add(num_bodies - 1);
            if global_def_id_range[0] != cursor || expected_end != Some(global_def_id_range[1]) {
                violations.push(format!(
                    "shards.shards[{i}].global_def_id_range {:?} disagrees with expected range \
                     starting at {cursor} for {num_bodies} bodies",
                    global_def_id_range
                ));
            }
            cursor = cursor.saturating_add(num_bodies);
        }
        for (pos, &callee) in callee_shards.iter().enumerate() {
            if callee >= i as u64 {
                violations.push(format!(
                    "shards.shards[{i}].callee_shards references non-earlier shard {callee}"
                ));
            }
            if pos > 0 && callee_shards[pos - 1] >= callee {
                violations.push(format!(
                    "shards.shards[{i}].callee_shards must be strictly sorted and duplicate-free"
                ));
            }
        }

        parsed_shards.push(ReceiptShardEntry {
            shard_idx,
            capture_module,
            proof_module,
            capture_sha256,
            num_bodies,
            ast_nodes,
            has_cycle,
            oversized_scc,
            scc_ids,
            callee_shards,
            global_def_id_range,
            identities,
        });
    }
    if seen_sccs.len() as u64 != total_sccs {
        violations.push(format!(
            "shards cover {} distinct scc_id(s) != shards.total_sccs ({total_sccs})",
            seen_sccs.len()
        ));
    }
    if cyclic_sccs < cyclic_shards || cyclic_sccs > cyclic_shard_sccs {
        violations.push(format!(
            "shards.cyclic_sccs ({cyclic_sccs}) is inconsistent with cyclic shard capacities \
             [{cyclic_shards}..={cyclic_shard_sccs}]"
        ));
    }
    if cursor != total_bodies {
        violations.push(format!(
            "shards cover {cursor} bodies != shards.total_bodies ({total_bodies})"
        ));
    }
    c.collect_unrecognized(unknown);
    Ok(ReceiptShardsManifest {
        schema_version,
        scope,
        total_bodies,
        total_sccs,
        cyclic_sccs,
        total_shards,
        is_lean_module,
        id_tree_sha256,
        shards: parsed_shards,
    })
}

fn validate_sorted_subset(
    ptr: &str,
    items: &[String],
    allowed: &[&str],
    violations: &mut Vec<String>,
) {
    let mut prev: Option<&str> = None;
    for item in items {
        if !allowed.contains(&item.as_str()) {
            violations.push(format!("unexpected entry `{item}` in `{ptr}`"));
        }
        if let Some(p) = prev
            && p >= item.as_str()
        {
            violations.push(format!(
                "`{ptr}` must be strictly sorted and duplicate-free (`{p}` before `{item}`)"
            ));
        }
        prev = Some(item.as_str());
    }
}

fn validate_permitted_axioms(ptr: &str, axioms: &[String], violations: &mut Vec<String>) {
    if axioms.is_empty() {
        violations.push(format!("`{ptr}` must not be empty"));
    }
    validate_sorted_subset(ptr, axioms, ALLOWED_FOUNDATION_AXIOMS, violations);
}

fn parse_opt_assurance_stage(
    root: &mut ObjectCursor<'_>,
    violations: &mut Vec<String>,
) -> Result<Option<String>, String> {
    let Some(stage) = root.opt_str("assurance_stage")? else {
        return Ok(None);
    };
    if !ALLOWED_ASSURANCE_STAGES.contains(&stage) {
        violations.push(format!("unknown assurance_stage `{stage}`"));
    }
    Ok(Some(stage.to_owned()))
}

fn parse_opt_horizon(
    root: &mut ObjectCursor<'_>,
    unknown: &mut Vec<String>,
    violations: &mut Vec<String>,
) -> Result<Option<HorizonRecord>, String> {
    let Some(obj) = root.opt_obj("horizon")? else {
        return Ok(None);
    };
    let mut c = ObjectCursor::nested("/horizon", obj);
    let kind = c.req_str("kind")?.to_owned();
    let rec = match kind.as_str() {
        "unbounded" => {
            if obj.contains_key("k") {
                violations.push("unbounded `horizon` must omit `k`".into());
                c.mark_visited("k");
            }
            HorizonRecord::Unbounded
        }
        "bounded" => HorizonRecord::Bounded { k: c.req_u64("k")? },
        other => {
            violations.push(format!("unknown horizon.kind `{other}`"));
            c.mark_visited("k");
            HorizonRecord::Unknown { raw_kind: other.to_owned() }
        }
    };
    c.collect_unrecognized(unknown);
    Ok(Some(rec))
}

fn check_trimmed_nonempty(prefix: &str, field: &str, value: &str, violations: &mut Vec<String>) {
    if value.trim().is_empty() || value.trim() != value {
        violations.push(format!("{prefix}.{field} must be trimmed and non-empty"));
    }
}

fn check_unique_trimmed_nonempty(
    prefix: &str,
    field: &str,
    values: &[String],
    violations: &mut Vec<String>,
) {
    let mut seen = BTreeSet::new();
    for v in values {
        if v.trim().is_empty() || v.trim() != v {
            violations.push(format!("{prefix}.{field} entries must be trimmed and non-empty"));
        } else if !seen.insert(v.as_str()) {
            violations.push(format!("duplicate entry `{v}` in {prefix}.{field}"));
        }
    }
}

fn validate_claim_kind_relation(
    claim_kind: &str,
    rel: &ModelSystemRelation,
    violations: &mut Vec<String>,
) {
    let expected_ok = match claim_kind {
        "exact_refines" => {
            rel.kind == "simulation"
                && rel.direction == "bidirectional"
                && matches!(rel.qualifier.as_deref(), Some("wf_stutter" | "lock_step"))
                && rel.licensed_claim_shapes == ["forall_safety"]
        }
        "sound_refines" => {
            rel.kind == "simulation"
                && rel.direction == "forward"
                && matches!(rel.qualifier.as_deref(), Some("wf_stutter" | "lock_step"))
                && rel.licensed_claim_shapes == ["forall_safety"]
        }
        "pure_spec_agreement" => {
            rel.kind == "embedding"
                && rel.direction == "bidirectional"
                && !matches!(rel.qualifier.as_deref(), Some("wf_stutter" | "stutter"))
                && rel.licensed_claim_shapes == ["forall_safety"]
        }
        _ => true,
    };
    if !expected_ok {
        violations.push(format!(
            "correspondence_provenance.claim_kind `{claim_kind}` is incompatible with model_system_relation ({}/{:?}/{})",
            rel.kind, rel.qualifier, rel.direction
        ));
    }
}

fn parse_tcb_shims(
    prefix: &str,
    arr: &[Value],
    unknown: &mut Vec<String>,
    violations: &mut Vec<String>,
) -> Result<Vec<TcbShimEntry>, String> {
    let mut seen_ids = BTreeSet::new();
    let mut out = Vec::with_capacity(arr.len());
    for (i, val) in arr.iter().enumerate() {
        let obj = val.as_object().ok_or_else(|| format!("{prefix}[{i}] must be a JSON object"))?;
        let ptr = format!("{prefix}/{i}");
        let mut c = ObjectCursor::nested(&ptr, obj);
        let id = c.req_str("id")?.to_owned();
        if id.trim().is_empty() || id.trim() != id {
            violations.push(format!("{ptr}.id must be trimmed and non-empty"));
        } else if !seen_ids.insert(id.clone()) {
            violations.push(format!("duplicate tcb_shims id `{id}` in `{prefix}`"));
        }
        let kind = c.req_str("kind")?.to_owned();
        if !ALLOWED_SHIM_KINDS.contains(&kind.as_str()) {
            violations.push(format!("unknown {ptr}.kind `{kind}`"));
        }
        let commit = c.opt_str("commit")?.map(str::to_owned);
        if let Some(ref cm) = commit {
            check_trimmed_nonempty(&ptr, "commit", cm, violations);
        }
        let sha256 = match c.opt_str("sha256")? {
            Some(hex) => {
                if !is_sha256_hex(hex) {
                    violations.push(format!(
                        "field `{ptr}/sha256` must be a 64-character SHA-256 hex digest, got `{hex}`"
                    ));
                }
                Some(hex.to_owned())
            }
            None => None,
        };
        if commit.is_none() && sha256.is_none() {
            violations.push(format!("{ptr} must specify at least one of `commit` or `sha256`"));
        }
        let status = c.req_str("status")?.to_owned();
        if !ALLOWED_SHIM_STATUSES.contains(&status.as_str()) {
            violations.push(format!("unknown {ptr}.status `{status}`"));
        }
        let guards = match c.opt_array("guards")? {
            Some(guard_arr) => {
                let list = parse_str_list(guard_arr, &format!("{ptr}/guards"))?;
                let mut seen_guards = BTreeSet::new();
                for g in &list {
                    if g.is_empty() {
                        violations.push(format!("{ptr}.guards must not contain empty strings"));
                    } else if !seen_guards.insert(g.as_str()) {
                        violations.push(format!("duplicate guard `{g}` in {ptr}.guards"));
                    }
                }
                list
            }
            None => Vec::new(),
        };
        c.collect_unrecognized(unknown);
        out.push(TcbShimEntry { id, kind, commit, sha256, status, guards });
    }
    Ok(out)
}

fn parse_model_system_relation(
    prefix: &str,
    obj: &Map<String, Value>,
    unknown: &mut Vec<String>,
    violations: &mut Vec<String>,
) -> Result<ModelSystemRelation, String> {
    let mut c = ObjectCursor::nested(prefix, obj);
    let kind = c.req_str("kind")?.to_owned();
    if !ALLOWED_RELATION_KINDS.contains(&kind.as_str()) {
        violations.push(format!("unknown {prefix}.kind `{kind}`"));
    }
    let qualifier = c.opt_str("qualifier")?.map(str::to_owned);
    if let Some(ref q) = qualifier
        && !ALLOWED_RELATION_QUALIFIERS.contains(&q.as_str())
    {
        violations.push(format!("unknown {prefix}.qualifier `{q}`"));
    }
    if matches!(kind.as_str(), "homomorphism" | "abstraction" | "simulation") && qualifier.is_none()
    {
        violations.push(format!("{prefix}.kind `{kind}` requires `qualifier`"));
    }
    if kind == "none" && qualifier.is_some() {
        violations.push(format!("{prefix}.kind `none` must omit `qualifier`"));
    }
    if kind == "embedding" && matches!(qualifier.as_deref(), Some("wf_stutter" | "stutter")) {
        violations.push(format!(
            "{prefix}.kind `embedding` does not admit `{}`",
            qualifier.as_deref().unwrap_or("")
        ));
    }
    let direction = c.req_str("direction")?.to_owned();
    if !ALLOWED_RELATION_DIRECTIONS.contains(&direction.as_str()) {
        violations.push(format!("unknown {prefix}.direction `{direction}`"));
    }
    let anchored_at = c.opt_str("anchored_at")?.map(str::to_owned);
    if let Some(ref anchor) = anchored_at {
        check_trimmed_nonempty(prefix, "anchored_at", anchor, violations);
    }
    let licensed_claim_shapes = c.req_str_array("licensed_claim_shapes")?;
    validate_sorted_subset(
        &format!("{prefix}/licensed_claim_shapes"),
        &licensed_claim_shapes,
        ALLOWED_CLAIM_SHAPES,
        violations,
    );
    if (kind == "none") != licensed_claim_shapes.is_empty() {
        violations.push(format!(
            "{prefix}.licensed_claim_shapes must be empty iff {prefix}.kind == `none`"
        ));
    }
    if licensed_claim_shapes.iter().any(|c| c == "general_hyper")
        && !(matches!(kind.as_str(), "simulation" | "homomorphism")
            && qualifier.as_deref() == Some("lock_step")
            && direction == "bidirectional")
    {
        violations.push(format!(
            "{prefix}: `general_hyper` requires bidirectional lock_step simulation or homomorphism"
        ));
    }
    if licensed_claim_shapes.iter().any(|c| c == "termination")
        && qualifier.as_deref() == Some("stutter")
    {
        violations.push(format!(
            "{prefix}: `termination` cannot be licensed under non-well-founded `stutter`"
        ));
    }
    let unmodeled_downstream = match c.opt_array("unmodeled_downstream")? {
        Some(arr) => {
            let list = parse_str_list(arr, &format!("{prefix}/unmodeled_downstream"))?;
            check_unique_trimmed_nonempty(prefix, "unmodeled_downstream", &list, violations);
            list
        }
        None => Vec::new(),
    };
    c.collect_unrecognized(unknown);
    Ok(ModelSystemRelation {
        kind,
        qualifier,
        direction,
        anchored_at,
        licensed_claim_shapes,
        unmodeled_downstream,
    })
}

fn parse_provenance_qualifiers(
    obj: &Map<String, Value>,
    unknown: &mut Vec<String>,
    violations: &mut Vec<String>,
) -> Result<ProvenanceQualifiers, String> {
    let mut c = ObjectCursor::nested("/correspondence_provenance/qualifiers", obj);
    let choice_total = c.req_bool("choice_total")?;
    let assumed_seams = c.req_str_array("assumed_seams")?;
    check_unique_trimmed_nonempty(
        "/correspondence_provenance/qualifiers",
        "assumed_seams",
        &assumed_seams,
        violations,
    );
    let scope_kind = c.req_str("scope_kind")?.to_owned();
    if !ALLOWED_PROVENANCE_SCOPES.contains(&scope_kind.as_str()) {
        violations.push(format!(
            "unknown correspondence_provenance.qualifiers.scope_kind `{scope_kind}`"
        ));
    }
    c.collect_unrecognized(unknown);
    Ok(ProvenanceQualifiers { choice_total, assumed_seams, scope_kind })
}

fn build_profile(receipt: &ParsedReceipt) -> AssuranceProfile {
    let taint = if receipt.taint_reasons().is_empty() {
        TaintAxis::Untainted
    } else {
        TaintAxis::Tainted { reasons: receipt.taint_reasons().to_vec() }
    };
    let artifacts = match receipt.artifacts() {
        Some(path) => ArtifactAxis::RetainedPathRecorded { path: path.to_owned() },
        None => ArtifactAxis::Omitted,
    };
    match receipt {
        ParsedReceipt::Failure(f) => AssuranceProfile {
            taint,
            scope: ScopeAxis::Failed { status: f.status.clone() },
            containment: match f.elaboration_sandbox.as_deref() {
                Some("none") => ContainmentAxis::Unsandboxed,
                Some(mode) => ContainmentAxis::Sandboxed { mode: mode.to_owned() },
                None => ContainmentAxis::Unknown,
            },
            replay: ReplayAxis::NotReached,
            axioms: AxiomAxis::NotReached,
            artifacts,
        },
        ParsedReceipt::Success(s) => AssuranceProfile {
            taint,
            scope: if s.scope_kind == "crate" {
                ScopeAxis::WholeCrate {
                    selected_bodies: s.selected.len(),
                    census_items: s.census.len(),
                }
            } else {
                ScopeAxis::SelectedUnits {
                    roots: s.scope_roots.len(),
                    instantiations: s.scope_instantiations.len(),
                    selected_bodies: s.selected.len(),
                    census_items: s.census.len(),
                }
            },
            containment: if s.elaboration_sandbox == "none" {
                ContainmentAxis::Unsandboxed
            } else {
                ContainmentAxis::Sandboxed { mode: s.elaboration_sandbox.clone() }
            },
            replay: if s.is_multi_kernel() {
                ReplayAxis::MultiKernel {
                    replayed_declarations: s.replayed_declarations,
                    kernels_passed: s.kernels_passed.clone(),
                    kernels_skipped: s.kernels_skipped.clone(),
                }
            } else {
                ReplayAxis::SingleKernel { replayed_declarations: s.replayed_declarations }
            },
            axioms: if s.axioms.iter().any(|a| a == "sorryAx") || !s.sorry_declarations.is_empty() {
                AxiomAxis::ContainsSorry {
                    axioms: s.axioms.clone(),
                    sorry_count: s.sorry_declarations.len(),
                }
            } else if s.axioms.iter().any(|a| !ALLOWED_FOUNDATION_AXIOMS.contains(&a.as_str())) {
                AxiomAxis::Unexpected { axioms: s.axioms.clone() }
            } else {
                AxiomAxis::StrictFoundation { axioms: s.axioms.clone() }
            },
            artifacts,
        },
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use serde_json::json;

    use super::*;

    pub fn sample_success_json() -> Value {
        let h = "a".repeat(64);
        json!({
            "schema_version": 3,
            "status": "crate_verified",
            "taint_reasons": [],
            "elaboration_sandbox": "linux_bwrap",
            "experimental": true,
            "request_sha256": h,
            "capture_sha256": h,
            "capture_binary_sha256": h,
            "toolchain_identity": {
                "sha256_locked": ["Lean executable in foundation-lock.json"],
                "sha256_recorded": ["capture executable as capture_binary_sha256"],
                "unhashed": ["Rust compiler and sysroot"]
            },
            "model_manifest_sha256": h,
            "specification_manifest_sha256": h,
            "correspondence_provenance": {
                "schema_version": 1,
                "upstream_repository": "https://github.com/proofs-rs/lean-miri",
                "upstream_commit": "c92d1d97",
                "upstream_lean_toolchain": "leanprover/lean4:v4.34.1",
                "build_lean_toolchain": "leanprover/lean4:v4.34.1",
                "upstream_pin_sha256": h,
                "sysroot_foundation_manifest_sha256": h,
                "patched_files": [],
                "minirust_upstream": {
                    "upstream_repository": "https://github.com/minirust/minirust",
                    "upstream_commit": "d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed",
                    "upstream_pin_sha256": h,
                    "tarball_sha256": h,
                    "manifest_sha256": h,
                    "file_count": 2,
                    "files": {
                        "README.md": h,
                        "spec/mem/basic.md": h
                    }
                },
                "correspondence_adapters": [],
                "correspondence_proofs": [],
                "trusted_lean": {},
                "note": "pass2"
            },
            "scope": { "kind": "crate" },
            "selected": [{ "def_id": 0, "path": "scalar::zero", "body_index": 0 }],
            "census": [{
                "def_id": 0,
                "path": "scalar::zero",
                "kind": "fn",
                "has_body": true,
                "selected": true,
                "required": true
            }],
            "sources": [{ "relative_path": "lib.rs", "sha256": h }],
            "configuration": {
                "crate_root": "lib.rs",
                "crate_name": "scalar",
                "crate_type": "lib",
                "panic": "unwind",
                "edition": "2024",
                "target": "x86_64-unknown-linux-gnu",
                "cfg": [],
                "env": {},
                "opt_level": 0,
                "debug_assertions": true,
                "overflow_checks": true,
                "mir_preserve_ub": false,
                "pointer_bits": 64,
                "endian": "little",
                "declared_source_files": ["lib.rs"]
            },
            "audit": {
                "theorem": "Proof.verify",
                "canonicalRoot": "Trusted.MirSemantics.CrateTheorem",
                "subject": "Captured.program",
                "specification": "Spec.specs",
                "graph": { "Init.Prelude": [] },
                "expected": "Expected.claim",
                "axioms": ["propext"],
                "sorryDeclarations": [],
                "replay": true,
                "exactType": true,
                "replayedDeclarations": 42,
                "checkedAlternateProofs": 0,
                "subjectClosure": [{ "name": "Captured.program", "module": "Captured" }],
                "modelClosure": [{ "name": "Trusted.MirSemantics.CrateTheorem", "module": "Trusted.MirSemantics" }],
                "specificationClosure": [{ "name": "Spec.specs", "module": "Spec" }],
                "bindings": {
                    "requestSha256": h,
                    "captureSha256": h,
                    "modelManifestSha256": h,
                    "specificationManifestSha256": h
                },
                "moduleIdentities": {},
                "sources": [],
                "toolchain": "leanprover/lean4:v4.34.1"
            },
            "timing_ms": { "capture": 12, "proof_and_audit": 34, "total": 46 },
            "assumptions": ["faithful pinned compiler capture"],
            "deferred": ["complete review-surface reporting"],
            "spec_warnings": []
        })
    }

    /// `sample_success_json` tainted by `--allow-unstable-feature`, with the
    /// matching top-level record, capture configuration, and assumption.
    pub fn unstable_feature_receipt_json(
        allowed: &[&str],
        observed: &[&str],
        incomplete: &[&str],
    ) -> Value {
        let mut receipt = sample_success_json();
        receipt["status"] = json!("tainted_crate_verified");
        receipt["taint_reasons"] = json!([UNSTABLE_FEATURES_TAINT]);
        receipt["unstable_features"] =
            json!({"allowed": allowed, "observed": observed, "incomplete_observed": incomplete});
        for (key, list) in [
            ("allowed_unstable_features", allowed),
            ("observed_unstable_features", observed),
            ("incomplete_observed_unstable_features", incomplete),
        ] {
            if !list.is_empty() {
                receipt["configuration"][key] = json!(list);
            }
        }
        receipt["assumptions"] =
            json!(["faithful pinned compiler capture", UNSTABLE_FEATURES_ASSUMPTION]);
        receipt
    }

    fn parse_json(receipt: &Value) -> ReceiptEnvelope {
        parse_and_validate_receipt(&serde_json::to_vec(receipt).unwrap()).unwrap()
    }

    fn unstable_policy(features: &[&str]) -> PolicyRequirements {
        PolicyRequirements {
            allowed_unstable_features: Some(features.iter().map(|f| (*f).to_owned()).collect()),
            ..PolicyRequirements::default()
        }
    }

    #[test]
    fn validates_unstable_feature_receipts_and_gates_exact_feature_sets() {
        let receipt = unstable_feature_receipt_json(
            &["doc_cfg", "specialization"],
            &["specialization"],
            &["specialization"],
        );
        let env = parse_json(&receipt);
        assert!(env.invariant_violations.is_empty(), "{:?}", env.invariant_violations);
        assert!(env.unrecognized_fields.is_empty(), "{:?}", env.unrecognized_fields);
        let ParsedReceipt::Success(s) = &env.receipt else { panic!("expected success") };
        assert_eq!(
            s.unstable_features,
            Some(UnstableFeaturesRecord {
                allowed: vec!["doc_cfg".into(), "specialization".into()],
                observed: vec!["specialization".into()],
                incomplete_observed: vec!["specialization".into()],
            })
        );

        // Bare validation still rejects every tainted receipt.
        let fails = env.evaluate_policy(&PolicyRequirements::default());
        assert!(fails.iter().any(|f| f.contains("tainted")), "{fails:?}");
        // The exact (or a wider) feature set admits the unstable taint.
        assert!(env.evaluate_policy(&unstable_policy(&["doc_cfg", "specialization"])).is_empty());
        assert!(
            env.evaluate_policy(&unstable_policy(&["allocator_api", "doc_cfg", "specialization"]))
                .is_empty()
        );
        // Allowed or observed features outside the gate fail.
        let fails = env.evaluate_policy(&unstable_policy(&["specialization"]));
        assert_eq!(fails.len(), 1, "{fails:?}");
        assert!(fails[0].contains("`doc_cfg` in unstable_features.allowed"), "{fails:?}");
        let fails = env.evaluate_policy(&unstable_policy(&["doc_cfg"]));
        assert_eq!(fails.len(), 2, "{fails:?}");
        // Incomplete features can be forbidden outright.
        let forbid = PolicyRequirements {
            forbid_incomplete_unstable_features: true,
            ..unstable_policy(&["doc_cfg", "specialization"])
        };
        let fails = env.evaluate_policy(&forbid);
        assert_eq!(fails.len(), 1, "{fails:?}");
        assert!(fails[0].contains("incomplete unstable feature(s) (specialization)"), "{fails:?}");

        // The gate admits only the unstable-feature taint, never another.
        let mut co_tainted = receipt.clone();
        co_tainted["taint_reasons"] = json!([UNSTABLE_FEATURES_TAINT, "unsandboxed_elaboration"]);
        co_tainted["elaboration_sandbox"] = json!("none");
        co_tainted["deferred"] = json!(["hostile Lean elaborator effects"]);
        let env = parse_json(&co_tainted);
        assert!(env.invariant_violations.is_empty(), "{:?}", env.invariant_violations);
        let fails = env.evaluate_policy(&unstable_policy(&["doc_cfg", "specialization"]));
        assert_eq!(fails, ["receipt is tainted (unsandboxed_elaboration)"]);

        // Failure receipts never satisfy a feature gate.
        let failure = parse_json(&json!({
            "schema_version": 3,
            "status": "unsupported",
            "taint_reasons": [UNSTABLE_FEATURES_TAINT],
            "phase": "capture",
            "detail": "#![feature(f16)] is unsupported during capture",
        }));
        assert!(failure.invariant_violations.is_empty(), "{:?}", failure.invariant_violations);
        for policy in [
            PolicyRequirements {
                check: false,
                require_untainted: false,
                ..unstable_policy(&["f16"])
            },
            PolicyRequirements {
                check: false,
                require_untainted: false,
                forbid_incomplete_unstable_features: true,
                ..PolicyRequirements::passive()
            },
        ] {
            assert!(!failure.evaluate_policy(&policy).is_empty(), "{policy:?}");
        }

        // Flag present, no feature enabled: still tainted, still gateable.
        let unused = parse_json(&unstable_feature_receipt_json(&["doc_cfg"], &[], &[]));
        assert!(unused.invariant_violations.is_empty(), "{:?}", unused.invariant_violations);
        assert!(!unused.evaluate_policy(&PolicyRequirements::default()).is_empty());
        assert!(unused.evaluate_policy(&unstable_policy(&["doc_cfg"])).is_empty());

        // Untainted receipts pass the gate unchanged, and stabilized features
        // are recognized without tainting.
        let mut stabilized = sample_success_json();
        stabilized["configuration"]["stabilized_features_present"] = json!(["doc_alias"]);
        let env = parse_json(&stabilized);
        assert!(env.invariant_violations.is_empty(), "{:?}", env.invariant_violations);
        assert!(env.unrecognized_fields.is_empty(), "{:?}", env.unrecognized_fields);
        assert!(env.evaluate_policy(&PolicyRequirements::default()).is_empty());
        assert!(env.evaluate_policy(&unstable_policy(&["doc_cfg"])).is_empty());
    }

    #[test]
    fn rejects_inconsistent_unstable_feature_envelopes() {
        let valid = unstable_feature_receipt_json(&["doc_cfg", "f16"], &["f16"], &[]);
        let mutations: Vec<(&str, Box<dyn Fn(&mut Value)>)> = vec![
            (
                "taint without record",
                Box::new(|r| {
                    r.as_object_mut().unwrap().remove("unstable_features");
                }),
            ),
            (
                "record without taint",
                Box::new(|r| {
                    r["status"] = json!("crate_verified");
                    r["taint_reasons"] = json!([]);
                }),
            ),
            (
                "observed not allowed",
                Box::new(|r| {
                    r["unstable_features"]["observed"] = json!(["allocator_api"]);
                    r["configuration"]["observed_unstable_features"] = json!(["allocator_api"]);
                }),
            ),
            (
                "incomplete not observed",
                Box::new(|r| {
                    r["unstable_features"]["incomplete_observed"] = json!(["doc_cfg"]);
                    r["configuration"]["incomplete_observed_unstable_features"] =
                        json!(["doc_cfg"]);
                }),
            ),
            (
                "unsorted allowed",
                Box::new(|r| {
                    r["unstable_features"]["allowed"] = json!(["f16", "doc_cfg"]);
                    r["configuration"]["allowed_unstable_features"] = json!(["f16", "doc_cfg"]);
                }),
            ),
            (
                "invalid name",
                Box::new(|r| {
                    r["unstable_features"]["allowed"] = json!(["*", "f16"]);
                    r["configuration"]["allowed_unstable_features"] = json!(["*", "f16"]);
                }),
            ),
            (
                "empty allowed",
                Box::new(|r| {
                    r["unstable_features"] =
                        json!({"allowed": [], "observed": [], "incomplete_observed": []});
                    r["configuration"].as_object_mut().unwrap().remove("allowed_unstable_features");
                    r["configuration"]
                        .as_object_mut()
                        .unwrap()
                        .remove("observed_unstable_features");
                }),
            ),
            (
                "stdlib crate with unstable features",
                Box::new(|r| {
                    r["configuration"]["stdlib_crate"] = json!("core");
                }),
            ),
            (
                "configuration allowed differs",
                Box::new(|r| {
                    r["configuration"]["allowed_unstable_features"] = json!(["f16"]);
                }),
            ),
            (
                "configuration observed missing",
                Box::new(|r| {
                    r["configuration"]
                        .as_object_mut()
                        .unwrap()
                        .remove("observed_unstable_features");
                }),
            ),
            (
                "configuration list empty",
                Box::new(|r| {
                    r["configuration"]["incomplete_observed_unstable_features"] = json!([]);
                }),
            ),
            (
                "missing assumption",
                Box::new(|r| {
                    r["assumptions"] = json!(["faithful pinned compiler capture"]);
                }),
            ),
            (
                "invalid stabilized name",
                Box::new(|r| {
                    r["configuration"]["stabilized_features_present"] = json!(["Doc_alias"]);
                }),
            ),
        ];
        for (label, mutate) in mutations {
            let mut receipt = valid.clone();
            mutate(&mut receipt);
            let env = parse_json(&receipt);
            assert!(!env.invariant_violations.is_empty(), "{label}: accepted {receipt}");
        }

        // An untainted receipt may not carry the assumption or capture lists.
        for key in ["allowed_unstable_features", "observed_unstable_features"] {
            let mut receipt = sample_success_json();
            receipt["configuration"][key] = json!(["doc_cfg"]);
            assert!(!parse_json(&receipt).invariant_violations.is_empty(), "{key}");
        }
        let mut receipt = sample_success_json();
        receipt["assumptions"] =
            json!(["faithful pinned compiler capture", UNSTABLE_FEATURES_ASSUMPTION]);
        assert!(!parse_json(&receipt).invariant_violations.is_empty());
        let mut receipt = sample_success_json();
        receipt["configuration"]["stdlib_crate"] = json!("core");
        receipt["configuration"]["stabilized_features_present"] = json!(["doc_alias"]);
        assert!(!parse_json(&receipt).invariant_violations.is_empty());
    }

    #[test]
    fn validates_clean_receipt_and_rejects_broken_cross_checks() {
        let valid = sample_success_json();
        let bytes = serde_json::to_vec(&valid).unwrap();
        let env = parse_and_validate_receipt(&bytes).unwrap();
        assert!(env.invariant_violations.is_empty(), "{:?}", env.invariant_violations);
        assert!(env.unrecognized_fields.is_empty(), "{:?}", env.unrecognized_fields);
        assert!(env.evaluate_policy(&PolicyRequirements::default()).is_empty());
        assert!(env.evaluate_policy(&PolicyRequirements::passive()).is_empty());

        // Cross-check: status/taint mismatch fails invariant check (`exit 1`).
        let mut tampered = valid.clone();
        tampered["status"] = json!("tainted_crate_verified");
        let env = parse_and_validate_receipt(&serde_json::to_vec(&tampered).unwrap()).unwrap();
        assert!(!env.invariant_violations.is_empty());
        assert!(!env.evaluate_policy(&PolicyRequirements::default()).is_empty());

        // Cross-check: replay=false fails invariant check.
        let mut no_replay = valid.clone();
        no_replay["audit"]["replay"] = json!(false);
        let env = parse_and_validate_receipt(&serde_json::to_vec(&no_replay).unwrap()).unwrap();
        assert!(env.invariant_violations.iter().any(|v| v.contains("replay=true")));

        // Cross-check: mismatched bindings digest fails invariant check.
        let mut bad_bind = valid.clone();
        bad_bind["audit"]["bindings"]["requestSha256"] = json!("b".repeat(64));
        let env = parse_and_validate_receipt(&serde_json::to_vec(&bad_bind).unwrap()).unwrap();
        assert!(env.invariant_violations.iter().any(|v| v.contains("audit.bindings")));

        // Unknown fields fail default validator policy while passing passive
        // mode, and fail hard on `--unknown-fields=deny`.
        let mut extra = valid.clone();
        extra["custom_extra"] = json!(1);
        extra["unknown_test_field"] = json!(["fake_ext"]);
        extra["selected"][0]["extra_item"] = json!(true);
        extra["census"][0]["extra_census"] = json!(1);
        extra["sources"][0]["extra_src"] = json!(1);
        extra["audit"]["subjectClosure"][0]["extra_node"] = json!(1);
        extra["spec_warnings"] = json!([{
            "code": "W1",
            "declaration": "Spec.id",
            "message": "warn",
            "extra_warn": 1
        }]);
        extra["audit"]["specWarnings"] = json!([{
            "code": "W1",
            "declaration": "Spec.id",
            "message": "warn"
        }]);
        extra["status"] = json!("selected_unit_verified");
        extra["scope"] = json!({
            "kind": "selected_unit",
            "roots": ["scalar::zero"],
            "instantiations": [{"path": "scalar::zero", "args": ["u64"], "extra_inst": 1}]
        });
        extra["audit"]["canonicalRoot"] = json!("Trusted.MirSemantics.UnitTheorem");
        let env = parse_and_validate_receipt(&serde_json::to_vec(&extra).unwrap()).unwrap();
        assert_eq!(
            env.unrecognized_fields,
            vec![
                "/audit/subjectClosure/0/extra_node",
                "/census/0/extra_census",
                "/custom_extra",
                "/scope/instantiations/0/extra_inst",
                "/selected/0/extra_item",
                "/sources/0/extra_src",
                "/spec_warnings/0/extra_warn",
                "/unknown_test_field",
            ]
        );
        assert!(!env.evaluate_policy(&PolicyRequirements::default()).is_empty());
        assert!(env.evaluate_policy(&PolicyRequirements::passive()).is_empty());
        let deny = PolicyRequirements {
            unknown_fields: UnknownFieldsPolicy::Deny,
            ..PolicyRequirements::default()
        };
        assert!(!env.evaluate_policy(&deny).is_empty());
    }

    #[test]
    fn enforces_require_flags_and_failure_receipts() {
        let mut tainted = sample_success_json();
        tainted["status"] = json!("tainted_crate_verified");
        tainted["taint_reasons"] = json!(["unsandboxed_elaboration"]);
        tainted["elaboration_sandbox"] = json!("none");
        tainted["deferred"] = json!(["hostile Lean elaborator effects"]);
        let env = parse_and_validate_receipt(&serde_json::to_vec(&tainted).unwrap()).unwrap();
        assert!(env.invariant_violations.is_empty(), "{:?}", env.invariant_violations);
        let req = PolicyRequirements {
            require_untainted: true,
            require_containment: true,
            ..PolicyRequirements::default()
        };
        let fails = env.evaluate_policy(&req);
        assert_eq!(fails.len(), 2, "{fails:?}");
    }

    #[test]
    fn validates_s3_gutns_v3_receipt_and_provenance() {
        let mut s3 = sample_success_json();
        let h = "b".repeat(64);
        let ha = "a".repeat(64);
        s3["assurance_stage"] = json!("stage1_audited");
        s3["horizon"] = json!({"kind": "bounded", "k": 8});
        s3["permitted_axioms"] = json!(["Classical.choice", "Quot.sound", "propext"]);
        s3["tcb_shims"] = json!([{
            "id": "rustc_post_cleanup_capture",
            "kind": "capture_driver",
            "commit": "pinned",
            "sha256": ha,
            "status": "assumed",
            "guards": ["mir_preserve_ub"]
        }]);
        s3["model_system_relation"] = json!({
            "kind": "simulation",
            "qualifier": "wf_stutter",
            "direction": "forward",
            "anchored_at": "post_cleanup_mir",
            "licensed_claim_shapes": ["forall_safety"],
            "unmodeled_downstream": ["rustc_mir_opt"]
        });
        s3["correspondence_provenance"]["schema_version"] = json!(3);
        s3["correspondence_provenance"]["claim_kind"] = json!("exact_refines");
        s3["correspondence_provenance"]["permitted_axioms"] =
            json!(["Classical.choice", "Quot.sound", "propext"]);
        s3["correspondence_provenance"]["model_system_relation"] = json!({
            "kind": "simulation",
            "qualifier": "wf_stutter",
            "direction": "bidirectional",
            "licensed_claim_shapes": ["forall_safety"]
        });
        s3["correspondence_provenance"]["patched_files"] = json!([{
            "path": "Patch.lean",
            "upstream_sha256": ha,
            "patched_sha256": h
        }]);
        s3["correspondence_provenance"]["tcb_shims"] = json!([{
            "id": "lean-miri:Patch.lean",
            "kind": "upstream_bugfix_patch",
            "sha256": h,
            "status": "assumed"
        }]);
        s3["correspondence_provenance"]["taint_reasons"] =
            json!(["vendor_upstream_patches_present"]);
        s3["correspondence_provenance"]["qualifiers"] = json!({
            "choice_total": true,
            "assumed_seams": [],
            "scope_kind": "full_gate"
        });
        let env = parse_and_validate_receipt(&serde_json::to_vec(&s3).unwrap()).unwrap();
        assert!(env.unrecognized_fields.is_empty(), "{:?}", env.unrecognized_fields);
        assert!(env.invariant_violations.is_empty(), "{:?}", env.invariant_violations);

        let mut bad_s3 = s3.clone();
        bad_s3["audit"]["axioms"] = json!(["Classical.choice"]);
        bad_s3["permitted_axioms"] = json!(["propext"]);
        bad_s3["correspondence_provenance"]["taint_reasons"] = json!([]);
        bad_s3["correspondence_provenance"]["claim_kind"] = json!("pure_spec_agreement");
        let bad_env = parse_and_validate_receipt(&serde_json::to_vec(&bad_s3).unwrap()).unwrap();
        assert!(
            bad_env.invariant_violations.iter().any(|v| v.contains("absent from permitted_axioms")),
            "{:?}",
            bad_env.invariant_violations
        );
        assert!(
            bad_env.invariant_violations.iter().any(|v| v.contains("taint_reasons")),
            "{:?}",
            bad_env.invariant_violations
        );
        assert!(
            bad_env.invariant_violations.iter().any(|v| v.contains("claim_kind")),
            "{:?}",
            bad_env.invariant_violations
        );
    }

    #[test]
    fn recognizes_stdlib_crate_and_enforces_sorry_and_assumed_seam_cross_checks() {
        let mut core = sample_success_json();
        core["configuration"]["stdlib_crate"] = json!("core");
        let core_env = parse_and_validate_receipt(&serde_json::to_vec(&core).unwrap()).unwrap();
        assert!(core_env.unrecognized_fields.is_empty(), "{:?}", core_env.unrecognized_fields);
        assert!(core_env.invariant_violations.is_empty(), "{:?}", core_env.invariant_violations);
        let ParsedReceipt::Success(s) = &core_env.receipt else {
            panic!("expected success");
        };
        assert_eq!(s.stdlib_crate.as_deref(), Some("core"));

        let mut blank_stdlib = sample_success_json();
        blank_stdlib["configuration"]["stdlib_crate"] = json!(" ");
        let blank_env =
            parse_and_validate_receipt(&serde_json::to_vec(&blank_stdlib).unwrap()).unwrap();
        assert!(
            blank_env.invariant_violations.iter().any(|v| v.contains("stdlib_crate")),
            "{:?}",
            blank_env.invariant_violations
        );

        let mut sorry_mismatch = sample_success_json();
        sorry_mismatch["status"] = json!("tainted_crate_verified");
        sorry_mismatch["taint_reasons"] = json!(["sorry_in_proof"]);
        sorry_mismatch["sorry_declarations"] = json!(["Proof.a"]);
        sorry_mismatch["audit"]["axioms"] = json!(["propext", "sorryAx"]);
        sorry_mismatch["audit"]["sorryDeclarations"] = json!(["Proof.b"]);
        let sorry_env =
            parse_and_validate_receipt(&serde_json::to_vec(&sorry_mismatch).unwrap()).unwrap();
        assert!(
            sorry_env
                .invariant_violations
                .iter()
                .any(|v| v.contains("differs from `audit.sorryDeclarations`")),
            "{:?}",
            sorry_env.invariant_violations
        );

        let mut seam = sample_success_json();
        let h = "1".repeat(64);
        seam["assurance_stage"] = json!("stage1_audited");
        seam["correspondence_provenance"]["schema_version"] = json!(3);
        seam["correspondence_provenance"]["claim_kind"] = json!("exact_refines");
        seam["correspondence_provenance"]["permitted_axioms"] =
            json!(["Classical.choice", "Quot.sound", "propext"]);
        seam["correspondence_provenance"]["model_system_relation"] = json!({
            "kind": "simulation",
            "qualifier": "wf_stutter",
            "direction": "bidirectional",
            "licensed_claim_shapes": ["forall_safety"]
        });
        seam["correspondence_provenance"]["tcb_shims"] = json!([{
            "id": "unregistered_seam",
            "kind": "assumed_seam",
            "sha256": h,
            "status": "assumed"
        }]);
        seam["correspondence_provenance"]["taint_reasons"] = json!([]);
        seam["correspondence_provenance"]["qualifiers"] = json!({
            "choice_total": true,
            "assumed_seams": [],
            "scope_kind": "full_gate"
        });
        let seam_env = parse_and_validate_receipt(&serde_json::to_vec(&seam).unwrap()).unwrap();
        assert!(
            seam_env
                .invariant_violations
                .iter()
                .any(|v| v.contains("absent from qualifiers.assumed_seams")),
            "{:?}",
            seam_env.invariant_violations
        );

        let warn_item = json!({
            "code": "unsatisfiable_safety",
            "declaration": "Spec.bad",
            "message": "ensures is unsatisfiable"
        });
        let mut stripped_top = sample_success_json();
        stripped_top["audit"]["specWarnings"] = json!([warn_item.clone()]);
        let stripped_env =
            parse_and_validate_receipt(&serde_json::to_vec(&stripped_top).unwrap()).unwrap();
        assert!(
            stripped_env
                .invariant_violations
                .iter()
                .any(|v| v.contains("differs from `audit.specWarnings`")),
            "{:?}",
            stripped_env.invariant_violations
        );

        let mut fabricated_top = sample_success_json();
        fabricated_top["spec_warnings"] = json!([warn_item.clone()]);
        let fabricated_env =
            parse_and_validate_receipt(&serde_json::to_vec(&fabricated_top).unwrap()).unwrap();
        assert!(
            fabricated_env
                .invariant_violations
                .iter()
                .any(|v| v.contains("differs from `audit.specWarnings`")),
            "{:?}",
            fabricated_env.invariant_violations
        );

        let mut audit_warn_extra = sample_success_json();
        audit_warn_extra["spec_warnings"] = json!([warn_item]);
        audit_warn_extra["audit"]["specWarnings"] = json!([{
            "code": "unsatisfiable_safety",
            "declaration": "Spec.bad",
            "message": "ensures is unsatisfiable",
            "extra_audit_warn": 1
        }]);
        let extra_env =
            parse_and_validate_receipt(&serde_json::to_vec(&audit_warn_extra).unwrap()).unwrap();
        assert!(extra_env.invariant_violations.is_empty(), "{:?}", extra_env.invariant_violations);
        assert_eq!(extra_env.unrecognized_fields, vec!["/audit/specWarnings/0/extra_audit_warn"]);

        let mut bad_audit_warn = sample_success_json();
        bad_audit_warn["audit"]["specWarnings"] = json!([123]);
        assert!(matches!(
            parse_and_validate_receipt(&serde_json::to_vec(&bad_audit_warn).unwrap()),
            Err(InspectParseError::Operational(_))
        ));
    }

    #[test]
    fn validates_profile_v2_pinned_and_rejects_mismatches() {
        for (scope, expected_root, status) in [
            (json!({ "kind": "crate" }), "Trusted.MirSemantics.CrateTheoremV2", "crate_verified"),
            (
                json!({
                    "kind": "selected_unit",
                    "roots": ["scalar::zero"],
                    "instantiations": [{ "path": "scalar::zero", "args": [] }]
                }),
                "Trusted.MirSemantics.UnitTheoremV2",
                "selected_unit_verified",
            ),
        ] {
            let mut v2 = sample_success_json();
            v2["status"] = json!(status);
            v2["scope"] = scope;
            v2["audit"]["canonicalRoot"] = json!(expected_root);
            v2["audit"]["modelClosure"] =
                json!([{ "name": expected_root, "module": "Trusted.MirSemantics" }]);
            v2["assumptions"] = json!([
                "faithful pinned compiler capture",
                "experimental Profile v2 MIR semantics: bounded caller memory"
            ]);
            v2["correspondence_provenance"] = json!({
                "applicable": false,
                "reason": "bundled Pass 2 correspondence covers Profile v1 semantics only"
            });
            let env = parse_and_validate_receipt(&serde_json::to_vec(&v2).unwrap()).unwrap();
            assert!(env.unrecognized_fields.is_empty(), "{:?}", env.unrecognized_fields);
            assert!(env.invariant_violations.is_empty(), "{:?}", env.invariant_violations);
            let ParsedReceipt::Success(s) = &env.receipt else {
                panic!("expected success");
            };
            assert!(!s.correspondence_applicable);
            assert!(env.evaluate_policy(&PolicyRequirements::default()).is_empty());
            let deny = PolicyRequirements {
                unknown_fields: UnknownFieldsPolicy::Deny,
                ..PolicyRequirements::default()
            };
            assert!(env.evaluate_policy(&deny).is_empty());

            // Missing Profile v2 assumption fails closed.
            let mut missing_assump = v2.clone();
            missing_assump["assumptions"] = json!(["faithful pinned compiler capture"]);
            let env =
                parse_and_validate_receipt(&serde_json::to_vec(&missing_assump).unwrap()).unwrap();
            assert!(
                env.invariant_violations
                    .iter()
                    .any(|v| v.contains("disagrees with Profile v2 `assumptions`")),
                "{:?}",
                env.invariant_violations
            );

            // Profile v2 root with v1 pointer-free assumption fails closed.
            let mut mixed_assump = v2.clone();
            mixed_assump["assumptions"] = json!([
                "experimental pointer-free MIR semantics",
                "experimental Profile v2 MIR semantics: bounded caller memory"
            ]);
            let env =
                parse_and_validate_receipt(&serde_json::to_vec(&mixed_assump).unwrap()).unwrap();
            assert!(
                env.invariant_violations
                    .iter()
                    .any(|v| v.contains("cannot retain Profile v1 pointer-free")),
                "{:?}",
                env.invariant_violations
            );

            // Profile v2 root with applicable v1 provenance fails closed.
            let mut v1_prov = v2.clone();
            v1_prov["correspondence_provenance"] =
                sample_success_json()["correspondence_provenance"].clone();
            let env = parse_and_validate_receipt(&serde_json::to_vec(&v1_prov).unwrap()).unwrap();
            assert!(
                env.invariant_violations
                    .iter()
                    .any(|v| v.contains("correspondence_provenance.applicable == false")),
                "{:?}",
                env.invariant_violations
            );

            // Extra unknown field inside Profile v2 provenance is tracked.
            let mut extra_prov = v2.clone();
            extra_prov["correspondence_provenance"]["extra_v2_prov"] = json!(1);
            let env =
                parse_and_validate_receipt(&serde_json::to_vec(&extra_prov).unwrap()).unwrap();
            assert_eq!(env.unrecognized_fields, vec!["/correspondence_provenance/extra_v2_prov"]);

            // Blank provenance reason fails closed.
            let mut blank_reason = v2.clone();
            blank_reason["correspondence_provenance"]["reason"] = json!("   ");
            let env =
                parse_and_validate_receipt(&serde_json::to_vec(&blank_reason).unwrap()).unwrap();
            assert!(
                env.invariant_violations.iter().any(|v| v.contains("reason")),
                "{:?}",
                env.invariant_violations
            );
        }

        // Profile v1 with Profile v2 assumption or `applicable: false` fails.
        let mut v1_with_v2_assump = sample_success_json();
        v1_with_v2_assump["assumptions"] = json!(["experimental Profile v2 MIR semantics: forged"]);
        let env =
            parse_and_validate_receipt(&serde_json::to_vec(&v1_with_v2_assump).unwrap()).unwrap();
        assert!(
            env.invariant_violations
                .iter()
                .any(|v| v.contains("disagrees with Profile v2 `assumptions`")),
            "{:?}",
            env.invariant_violations
        );

        let mut v1_inapplicable = sample_success_json();
        v1_inapplicable["correspondence_provenance"] = json!({
            "applicable": false,
            "reason": "forged omission on Profile v1"
        });
        let env =
            parse_and_validate_receipt(&serde_json::to_vec(&v1_inapplicable).unwrap()).unwrap();
        assert!(
            env.invariant_violations
                .iter()
                .any(|v| v.contains("pinned Profile v1 verification correspondence_provenance")),
            "{:?}",
            env.invariant_violations
        );

        let mut v2_applicable_true = sample_success_json();
        v2_applicable_true["audit"]["canonicalRoot"] = json!("Trusted.MirSemantics.CrateTheoremV2");
        v2_applicable_true["assumptions"] =
            json!(["experimental Profile v2 MIR semantics: bounded"]);
        v2_applicable_true["correspondence_provenance"] = json!({
            "applicable": true,
            "reason": "contradictory"
        });
        let env =
            parse_and_validate_receipt(&serde_json::to_vec(&v2_applicable_true).unwrap()).unwrap();
        assert!(
            env.invariant_violations
                .iter()
                .any(|v| v.contains("may only set `applicable` to `false`")),
            "{:?}",
            env.invariant_violations
        );
    }

    /// A passing receipt as the NDJSON comparator route emits it.
    pub fn sample_ndjson_success_json() -> Value {
        let mut r = sample_success_json();
        let audit = r["audit"].as_object_mut().unwrap();
        audit.remove("checkedAlternateProofs");
        let h = "b".repeat(64);
        for (key, val) in [
            ("auditMode", json!("ndjson_comparator")),
            ("kernelsPassed", json!(["nanoda_bin", "con-ron"])),
            ("paranoidQuorum", json!(false)),
            ("expectedConeDeclarations", json!(5)),
            ("pinnedPrimitivesCount", json!(39)),
            ("sysrootPinnedDeclarations", json!(7)),
            ("expectedConeSha256", json!(h)),
            ("proofNdjsonSha256", json!(h)),
            ("initPrimitivesSha256", json!(h)),
            ("sysrootPinsSha256", json!(h)),
            ("leanexportSha256", json!(h)),
            ("nanodaBinSha256", json!(h)),
            ("conRonSha256", json!(h)),
            (
                "timingMs",
                json!({
                    "initPrimitives": 1, "targetConsts": 1, "sysrootPins": 1,
                    "exportExpected": 1, "exportProof": 1, "rustCompare": 1,
                    "nanoda": 1, "conRon": 1, "paranoidQuorum": 0, "total": 9
                }),
            ),
        ] {
            audit.insert(key.to_owned(), val);
        }
        r
    }

    #[test]
    fn accepts_ndjson_comparator_receipts_and_validates_their_fields() {
        let deny =
            PolicyRequirements { unknown_fields: UnknownFieldsPolicy::Deny, ..Default::default() };
        let parse =
            |v: &Value| parse_and_validate_receipt(&serde_json::to_vec(v).unwrap()).unwrap();

        let good = sample_ndjson_success_json();
        let env = parse(&good);
        assert!(env.invariant_violations.is_empty(), "{:?}", env.invariant_violations);
        assert!(env.unrecognized_fields.is_empty(), "{:?}", env.unrecognized_fields);
        assert!(env.evaluate_policy(&deny).is_empty(), "{:?}", env.evaluate_policy(&deny));
        let ParsedReceipt::Success(s) = &env.receipt else { panic!("expected success") };
        assert_eq!(s.checked_alternate_proofs, 0);

        // A `--paranoid-quorum` receipt records all four kernels and both
        // quorum digests.
        let mut quorum = good.clone();
        quorum["audit"]["paranoidQuorum"] = json!(true);
        quorum["audit"]["kernelsPassed"] =
            json!(["nanoda_bin", "con-ron", "con-leche", "lean4lean"]);
        quorum["audit"]["conLecheSha256"] = json!("c".repeat(64));
        quorum["audit"]["lean4leanSha256"] = json!("d".repeat(64));
        let env = parse(&quorum);
        assert!(env.invariant_violations.is_empty(), "{:?}", env.invariant_violations);
        assert!(env.evaluate_policy(&deny).is_empty(), "{:?}", env.evaluate_policy(&deny));

        // A `sorryAx` receipt skips `con-ron`, recorded as `{kernel, reason}`.
        let mut sorry = good.clone();
        sorry["status"] = json!("tainted_crate_verified");
        sorry["taint_reasons"] = json!(["sorry_in_proof"]);
        sorry["sorry_declarations"] = json!(["Proof.hole"]);
        sorry["audit"]["axioms"] = json!(["propext", "sorryAx"]);
        sorry["audit"]["sorryDeclarations"] = json!(["Proof.hole"]);
        sorry["audit"]["kernelsPassed"] = json!(["nanoda_bin"]);
        sorry["audit"]["kernelsSkipped"] =
            json!([{"kernel": "con-ron", "reason": "sorryAx is not admitted"}]);
        let env = parse(&sorry);
        assert!(env.invariant_violations.is_empty(), "{:?}", env.invariant_violations);
        assert!(env.unrecognized_fields.is_empty(), "{:?}", env.unrecognized_fields);
        let ParsedReceipt::Success(s) = &env.receipt else { panic!("expected success") };
        assert_eq!(s.kernels_skipped, ["con-ron"]);

        // A `--paranoid-quorum` `sorryAx` receipt skips `con-ron` and
        // `con-leche` and records only `lean4lean`'s quorum digest.
        let mut quorum_sorry = sorry.clone();
        quorum_sorry["audit"]["paranoidQuorum"] = json!(true);
        quorum_sorry["audit"]["kernelsPassed"] = json!(["nanoda_bin", "lean4lean"]);
        quorum_sorry["audit"]["kernelsSkipped"] = json!([
            {"kernel": "con-ron", "reason": "sorryAx is not admitted"},
            {"kernel": "con-leche", "reason": "sorryAx is not admitted"}
        ]);
        quorum_sorry["audit"]["lean4leanSha256"] = json!("d".repeat(64));
        let env = parse(&quorum_sorry);
        assert!(env.invariant_violations.is_empty(), "{:?}", env.invariant_violations);

        // Receipts `validate_ndjson_verdict` never emits are violations.
        let edit = |f: &dyn Fn(&mut Value)| {
            let mut r = good.clone();
            f(&mut r["audit"]);
            parse(&r).invariant_violations
        };
        for (needle, violations) in [
            ("pinnedPrimitivesCount must be 39", edit(&|a| a["pinnedPrimitivesCount"] = json!(0))),
            (
                "expectedConeDeclarations must be >= 1",
                edit(&|a| a["expectedConeDeclarations"] = json!(0)),
            ),
            ("lacks a passing `con-ron`", edit(&|a| a["kernelsPassed"] = json!(["nanoda_bin"]))),
            ("lacks a passing `nanoda_bin`", edit(&|a| a["kernelsPassed"] = json!(["con-ron"]))),
            (
                "recorded more than once",
                edit(&|a| a["kernelsSkipped"] = json!([{"kernel": "con-ron", "reason": "r"}])),
            ),
            (
                "unknown NDJSON comparator kernel",
                edit(&|a| a["kernelsPassed"] = json!(["nanoda_bin", "con-ron", "x"])),
            ),
            ("requires a passing `lean4lean`", edit(&|a| a["paranoidQuorum"] = json!(true))),
            ("without `paranoidQuorum`", edit(&|a| a["conLecheSha256"] = json!("c".repeat(64)))),
            (
                "without `paranoidQuorum`",
                edit(&|a| a["kernelsSkipped"] = json!([{"kernel": "lean4lean", "reason": "r"}])),
            ),
            (
                "lacks `audit.paranoidQuorum`",
                edit(&|a| {
                    a.as_object_mut().unwrap().remove("paranoidQuorum");
                }),
            ),
        ] {
            assert!(violations.iter().any(|v| v.contains(needle)), "{needle}: {violations:?}");
        }

        // `timingMs` is a fixed schema: an extra key is unrecognized and a
        // missing or non-integer timing is an error.
        let mut extra_timing = good.clone();
        extra_timing["audit"]["timingMs"]["extra"] = json!(1);
        let env = parse(&extra_timing);
        assert_eq!(env.unrecognized_fields, ["/audit/timingMs/extra"]);
        assert!(!env.evaluate_policy(&deny).is_empty());
        for bad_timing in [json!({"total": 1}), json!(null)] {
            let mut r = good.clone();
            r["audit"]["timingMs"] = bad_timing;
            assert!(parse_and_validate_receipt(&serde_json::to_vec(&r).unwrap()).is_err());
        }

        // Malformed digests and skipped-kernel entries are violations, and
        // unknown skipped-kernel keys are unrecognized.
        let mut bad = sorry.clone();
        bad["audit"]["proofNdjsonSha256"] = json!("xyz");
        bad["audit"]["kernelsSkipped"] = json!([{"kernel": "con-ron", "reason": " ", "x": 1}]);
        let env = parse(&bad);
        for needle in ["/audit/proofNdjsonSha256", "/reason"] {
            assert!(
                env.invariant_violations.iter().any(|v| v.contains(needle)),
                "{needle}: {:?}",
                env.invariant_violations
            );
        }
        assert_eq!(env.unrecognized_fields, ["/audit/kernelsSkipped/0/x"]);
        let mut bad_quorum = quorum.clone();
        bad_quorum["audit"]["lean4leanSha256"] = json!("");
        let env = parse(&bad_quorum);
        assert!(
            env.invariant_violations.iter().any(|v| v.contains("/audit/lean4leanSha256")),
            "{:?}",
            env.invariant_violations
        );
        let mut missing = good.clone();
        missing["audit"].as_object_mut().unwrap().remove("conRonSha256");
        assert!(parse_and_validate_receipt(&serde_json::to_vec(&missing).unwrap()).is_err());
        let mut non_string = good.clone();
        non_string["audit"]["kernelsSkipped"] = json!([1]);
        assert!(parse_and_validate_receipt(&serde_json::to_vec(&non_string).unwrap()).is_err());

        // Without `auditMode == "ndjson_comparator"`, `checkedAlternateProofs`
        // stays required and the comparator fields are unrecognized.
        let mut other_mode = good.clone();
        other_mode["audit"]["auditMode"] = json!("strict");
        assert!(parse_and_validate_receipt(&serde_json::to_vec(&other_mode).unwrap()).is_err());
        other_mode["audit"]["checkedAlternateProofs"] = json!(0);
        let env = parse(&other_mode);
        assert!(env.unrecognized_fields.contains(&"/audit/proofNdjsonSha256".to_owned()));
        assert!(!env.evaluate_policy(&deny).is_empty());
    }

    #[test]
    fn enforces_multi_kernel_replay_policy_and_accepts_checked_alternate_proofs() {
        // Nonzero `checkedAlternateProofs` is emitted on passing multi-module
        // realized-theorem audits and must pass with zero invariant violations.
        let mut alt = sample_success_json();
        alt["audit"]["checkedAlternateProofs"] = json!(2);
        let alt_env = parse_and_validate_receipt(&serde_json::to_vec(&alt).unwrap()).unwrap();
        assert!(alt_env.invariant_violations.is_empty(), "{:?}", alt_env.invariant_violations);
        assert!(alt_env.evaluate_policy(&PolicyRequirements::default()).is_empty());
        let ParsedReceipt::Success(s) = &alt_env.receipt else {
            panic!("expected success");
        };
        assert_eq!(s.checked_alternate_proofs, 2);

        // Explicit empty `kernelsPassed` fails both default `--check` and
        // `--require-kernel-replay 1`, while `--no-check` (`passive()`)
        // allows it.
        let req_1 =
            PolicyRequirements { require_kernel_replay: Some(1), ..PolicyRequirements::default() };
        let mut empty_k = sample_success_json();
        empty_k["audit"]["kernelsPassed"] = json!([]);
        let empty_env = parse_and_validate_receipt(&serde_json::to_vec(&empty_k).unwrap()).unwrap();
        assert!(empty_env.invariant_violations.is_empty(), "{:?}", empty_env.invariant_violations);
        assert!(matches!(empty_env.profile.replay, ReplayAxis::MultiKernel { .. }));
        assert!(!empty_env.evaluate_policy(&PolicyRequirements::default()).is_empty());
        assert!(empty_env.evaluate_policy(&PolicyRequirements::passive()).is_empty());
        assert!(!empty_env.evaluate_policy(&req_1).is_empty());

        // `auditMode` + `kernelsSkipped` with omitted `kernelsPassed` counts 0.
        let mut skipped_only = sample_success_json();
        skipped_only["audit"]["auditMode"] = json!("strict");
        skipped_only["audit"]["kernelsSkipped"] = json!(["lean4"]);
        let skipped_env =
            parse_and_validate_receipt(&serde_json::to_vec(&skipped_only).unwrap()).unwrap();
        assert!(matches!(skipped_env.profile.replay, ReplayAxis::MultiKernel { .. }));
        assert!(!skipped_env.evaluate_policy(&PolicyRequirements::default()).is_empty());
        assert!(skipped_env.evaluate_policy(&PolicyRequirements::passive()).is_empty());
        assert!(!skipped_env.evaluate_policy(&req_1).is_empty());

        // `embedding` must not license `general_hyper`.
        let mut emb = sample_success_json();
        emb["model_system_relation"] = json!({
            "kind": "embedding",
            "direction": "bidirectional",
            "licensed_claim_shapes": ["general_hyper"]
        });
        let emb_env = parse_and_validate_receipt(&serde_json::to_vec(&emb).unwrap()).unwrap();
        assert!(
            emb_env.invariant_violations.iter().any(|v| v.contains("general_hyper")),
            "expected general_hyper violation for embedding, got {:?}",
            emb_env.invariant_violations
        );

        // `audit.sources` specification hashes must match
        // `specification_manifest_sha256`.
        let mut bad_src = sample_success_json();
        bad_src["audit"]["sources"] = json!([
            {
                "module": "Spec",
                "role": "specification",
                "sourceSha256": "b".repeat(64),
                "artifacts": [{ "sha256": "c".repeat(64) }]
            }
        ]);
        let bad_src_env =
            parse_and_validate_receipt(&serde_json::to_vec(&bad_src).unwrap()).unwrap();
        assert!(
            bad_src_env
                .invariant_violations
                .iter()
                .any(|v| v.contains("specification_manifest_sha256")),
            "expected spec manifest mismatch, got {:?}",
            bad_src_env.invariant_violations
        );

        // Blank kernel names are invariant violations and never count.
        let req_2 =
            PolicyRequirements { require_kernel_replay: Some(2), ..PolicyRequirements::default() };
        let mut blank_k = sample_success_json();
        blank_k["audit"]["kernelsPassed"] = json!(["", " "]);
        let blank_env = parse_and_validate_receipt(&serde_json::to_vec(&blank_k).unwrap()).unwrap();
        assert_eq!(blank_env.invariant_violations.len(), 2, "{:?}", blank_env.invariant_violations);
        assert!(!blank_env.evaluate_policy(&req_2).is_empty());

        // Trimmed duplicates count once, while single-kernel replay counts 1.
        let mut dup_k = sample_success_json();
        dup_k["audit"]["kernelsPassed"] = json!(["lean4", " lean4 "]);
        let dup_env = parse_and_validate_receipt(&serde_json::to_vec(&dup_k).unwrap()).unwrap();
        assert!(dup_env.invariant_violations.is_empty(), "{:?}", dup_env.invariant_violations);
        assert!(dup_env.evaluate_policy(&req_1).is_empty());
        assert!(!dup_env.evaluate_policy(&req_2).is_empty());

        let single_env =
            parse_and_validate_receipt(&serde_json::to_vec(&sample_success_json()).unwrap())
                .unwrap();
        assert!(matches!(single_env.profile.replay, ReplayAxis::SingleKernel { .. }));
        assert!(single_env.evaluate_policy(&req_1).is_empty());
        assert!(!single_env.evaluate_policy(&req_2).is_empty());

        // `candidate_features` must be a sorted, duplicate-free subset of
        // recognized subsystem identifiers and agree with `experimental`.
        let mut cf_ok = sample_success_json();
        cf_ok["experimental"] = json!(true);
        cf_ok["candidate_features"] = json!(["memory", "mir_semantics"]);
        let cf_ok_env = parse_and_validate_receipt(&serde_json::to_vec(&cf_ok).unwrap()).unwrap();
        assert!(cf_ok_env.unrecognized_fields.is_empty(), "{:?}", cf_ok_env.unrecognized_fields);
        assert!(cf_ok_env.invariant_violations.is_empty(), "{:?}", cf_ok_env.invariant_violations);

        let mut cf_empty = sample_success_json();
        cf_empty["experimental"] = json!(false);
        cf_empty["candidate_features"] = json!([]);
        let cf_empty_env =
            parse_and_validate_receipt(&serde_json::to_vec(&cf_empty).unwrap()).unwrap();
        assert!(
            cf_empty_env.invariant_violations.is_empty(),
            "{:?}",
            cf_empty_env.invariant_violations
        );

        let mut cf_mismatch = sample_success_json();
        cf_mismatch["experimental"] = json!(false);
        cf_mismatch["candidate_features"] = json!(["mir_semantics"]);
        let cf_mismatch_env =
            parse_and_validate_receipt(&serde_json::to_vec(&cf_mismatch).unwrap()).unwrap();
        assert!(
            cf_mismatch_env.invariant_violations.iter().any(|v| v.contains("candidate_features")),
            "{:?}",
            cf_mismatch_env.invariant_violations
        );

        let mut cf_bad = sample_success_json();
        cf_bad["experimental"] = json!(true);
        cf_bad["candidate_features"] = json!(["mir_semantics", "memory", "unknown_feat"]);
        let cf_bad_env = parse_and_validate_receipt(&serde_json::to_vec(&cf_bad).unwrap()).unwrap();
        assert!(
            cf_bad_env.invariant_violations.len() >= 2,
            "expected unsorted + unknown violations, got {:?}",
            cf_bad_env.invariant_violations
        );
    }

    pub fn sample_sharded_success_json() -> Value {
        let mut r = sample_success_json();
        let h_shards = "1".repeat(64);
        let h_id_tree = "2".repeat(64);
        let h_shard0 = "3".repeat(64);
        let h_shard1 = "4".repeat(64);
        let h_spec = "5".repeat(64);
        let spec_manifest_sha =
            sha256_bytes(&serde_json::to_vec_pretty(&[("Spec", h_spec.as_str())]).unwrap());
        r["specification_manifest_sha256"] = json!(spec_manifest_sha);
        r["audit"]["bindings"]["specificationManifestSha256"] = json!(spec_manifest_sha);
        r["selected"] = json!([
            { "def_id": 0, "path": "scalar::callee", "body_index": 0 },
            { "def_id": 1, "path": "scalar::caller", "body_index": 1 }
        ]);
        r["capture_shards_sha256"] = json!(h_shards);
        r["shards"] = json!({
            "schema_version": 1,
            "scope": "crate",
            "total_bodies": 2,
            "total_sccs": 2,
            "cyclic_sccs": 0,
            "total_shards": 2,
            "is_lean_module": true,
            "id_tree_sha256": h_id_tree,
            "shards": [
                {
                    "shard_idx": 0,
                    "capture_module": "Captured.Shard_000",
                    "proof_module": "Proof.Shard_000",
                    "capture_sha256": h_shard0,
                    "num_bodies": 1,
                    "ast_nodes": 12,
                    "has_cycle": false,
                    "oversized_scc": false,
                    "scc_ids": [0],
                    "callee_shards": [],
                    "global_def_id_range": [0, 0],
                    "identities": ["rust-path-v1::callee"]
                },
                {
                    "shard_idx": 1,
                    "capture_module": "Captured.Shard_001",
                    "proof_module": "Proof.Shard_001",
                    "capture_sha256": h_shard1,
                    "num_bodies": 1,
                    "ast_nodes": 18,
                    "has_cycle": false,
                    "oversized_scc": false,
                    "scc_ids": [1],
                    "callee_shards": [0],
                    "global_def_id_range": [1, 1],
                    "identities": ["rust-path-v1::caller"]
                }
            ]
        });
        r["audit"]["sources"] = json!([
            { "module": "Spec", "role": "specification", "sourceSha256": h_spec },
            { "module": "Captured.Shard_000", "role": "capture", "sourceSha256": h_shard0 },
            { "module": "Captured.Shard_001", "role": "capture", "sourceSha256": h_shard1 },
            { "module": "Proof.IdTree", "role": "proof", "sourceSha256": h_id_tree }
        ]);
        r
    }

    #[test]
    fn validates_sharded_receipt_and_rejects_shard_invariants_and_unknown_keys() {
        let valid = sample_sharded_success_json();
        let env = parse_and_validate_receipt(&serde_json::to_vec(&valid).unwrap()).unwrap();
        assert!(env.unrecognized_fields.is_empty(), "{:?}", env.unrecognized_fields);
        assert!(env.invariant_violations.is_empty(), "{:?}", env.invariant_violations);
        assert!(env.evaluate_policy(&PolicyRequirements::default()).is_empty());
        let deny = PolicyRequirements {
            unknown_fields: UnknownFieldsPolicy::Deny,
            ..PolicyRequirements::default()
        };
        assert!(env.evaluate_policy(&deny).is_empty());

        // `selected_unit` scope maps to `shards.scope == "unit"` and may have
        // transitive callees so `selected.len() <= shards.total_bodies`.
        let mut unit = valid.clone();
        unit["status"] = json!("selected_unit_verified");
        unit["scope"] = json!({ "kind": "selected_unit", "roots": ["scalar::caller"] });
        unit["audit"]["canonicalRoot"] = json!("Trusted.MirSemantics.UnitTheorem");
        unit["selected"] = json!([{ "def_id": 1, "path": "scalar::caller", "body_index": 1 }]);
        unit["shards"]["scope"] = json!("unit");
        let unit_env = parse_and_validate_receipt(&serde_json::to_vec(&unit).unwrap()).unwrap();
        assert!(unit_env.unrecognized_fields.is_empty(), "{:?}", unit_env.unrecognized_fields);
        assert!(unit_env.invariant_violations.is_empty(), "{:?}", unit_env.invariant_violations);

        // Unpaired `capture_shards_sha256` / `shards` fail closed.
        let mut missing_shards = valid.clone();
        missing_shards.as_object_mut().unwrap().remove("shards");
        let env = parse_and_validate_receipt(&serde_json::to_vec(&missing_shards).unwrap()).unwrap();
        assert!(env.invariant_violations.iter().any(|v| v.contains("capture_shards_sha256")));

        let mut missing_hash = valid.clone();
        missing_hash.as_object_mut().unwrap().remove("capture_shards_sha256");
        let env = parse_and_validate_receipt(&serde_json::to_vec(&missing_hash).unwrap()).unwrap();
        assert!(env.invariant_violations.iter().any(|v| v.contains("capture_shards_sha256")));

        // Nested unrecognized keys inside `/shards` and `/shards/shards/0`.
        let mut extra = valid.clone();
        extra["shards"]["extra_top"] = json!(true);
        extra["shards"]["shards"][0]["extra_entry"] = json!(1);
        let env = parse_and_validate_receipt(&serde_json::to_vec(&extra).unwrap()).unwrap();
        assert_eq!(
            env.unrecognized_fields,
            vec!["/shards/extra_top", "/shards/shards/0/extra_entry"]
        );

        // Scope mismatch, non-module shards, non-earlier callee, and
        // `audit.sources` digest/presence mismatches all trigger violations.
        let mut bad = valid.clone();
        bad["shards"]["scope"] = json!("unit");
        bad["shards"]["is_lean_module"] = json!(false);
        bad["shards"]["shards"][1]["callee_shards"] = json!([1]);
        bad["audit"]["sources"][3]["sourceSha256"] = json!("9".repeat(64));
        bad["audit"]["sources"][1]["sourceSha256"] = json!("8".repeat(64));
        let env = parse_and_validate_receipt(&serde_json::to_vec(&bad).unwrap()).unwrap();
        for needle in [
            "shards.scope",
            "is_lean_module",
            "non-earlier shard",
            "Proof.IdTree",
            "Captured.Shard_000",
        ] {
            assert!(
                env.invariant_violations.iter().any(|v| v.contains(needle)),
                "expected `{needle}` in {:?}",
                env.invariant_violations
            );
        }

        // Missing `Proof.IdTree` in non-empty `audit.sources` fails closed.
        let mut missing_id_tree = valid.clone();
        missing_id_tree["audit"]["sources"]
            .as_array_mut()
            .unwrap()
            .retain(|e| e["module"] != "Proof.IdTree");
        let env =
            parse_and_validate_receipt(&serde_json::to_vec(&missing_id_tree).unwrap()).unwrap();
        assert!(
            env.invariant_violations.iter().any(|v| v.contains("missing `Proof.IdTree`")),
            "{:?}",
            env.invariant_violations
        );
    }

    #[test]
    fn minirust_upstream_provenance_validation_and_unknown_field_tracking() {
        let h2 = "b".repeat(64);
        let base = sample_success_json();
        let base_env = parse_and_validate_receipt(&serde_json::to_vec(&base).unwrap()).unwrap();
        assert!(base_env.unrecognized_fields.is_empty(), "{:?}", base_env.unrecognized_fields);
        assert!(base_env.invariant_violations.is_empty(), "{:?}", base_env.invariant_violations);
        assert!(base_env.evaluate_policy(&PolicyRequirements::default()).is_empty());

        // Omitting `minirust_upstream` on applicable provenance fails closed.
        let mut missing_mr = base.clone();
        missing_mr["correspondence_provenance"]
            .as_object_mut()
            .unwrap()
            .remove("minirust_upstream");
        let missing_err =
            parse_and_validate_receipt(&serde_json::to_vec(&missing_mr).unwrap()).unwrap_err();
        assert!(
            missing_err.message().contains("/correspondence_provenance/minirust_upstream"),
            "{}",
            missing_err.message()
        );

        // Null, non-object, or any missing subfield inside `minirust_upstream`
        // fails closed operationally.
        for bad_mr in [json!(null), json!(["bad"])] {
            let mut non_obj = base.clone();
            non_obj["correspondence_provenance"]["minirust_upstream"] = bad_mr;
            let err =
                parse_and_validate_receipt(&serde_json::to_vec(&non_obj).unwrap()).unwrap_err();
            assert!(
                err.message().contains("/correspondence_provenance/minirust_upstream"),
                "{}",
                err.message()
            );
        }
        for omitted_field in [
            "upstream_repository",
            "upstream_commit",
            "upstream_pin_sha256",
            "tarball_sha256",
            "manifest_sha256",
            "file_count",
            "files",
        ] {
            let mut omitted = base.clone();
            omitted["correspondence_provenance"]["minirust_upstream"]
                .as_object_mut()
                .unwrap()
                .remove(omitted_field);
            let err =
                parse_and_validate_receipt(&serde_json::to_vec(&omitted).unwrap()).unwrap_err();
            assert!(
                err.message().contains(&format!(
                    "/correspondence_provenance/minirust_upstream/{omitted_field}"
                )),
                "expected missing {omitted_field} error, got {}",
                err.message()
            );
        }

        // Changing `minirust_upstream` updates
        // `correspondence_provenance_residual_sha256`.
        let mut mr = base.clone();
        mr["correspondence_provenance"]["minirust_upstream"]["files"]["spec/mem/basic.md"] =
            json!(h2);
        let ok_env = parse_and_validate_receipt(&serde_json::to_vec(&mr).unwrap()).unwrap();
        assert!(ok_env.unrecognized_fields.is_empty(), "{:?}", ok_env.unrecognized_fields);
        assert!(ok_env.invariant_violations.is_empty(), "{:?}", ok_env.invariant_violations);
        assert!(ok_env.evaluate_policy(&PolicyRequirements::default()).is_empty());
        match (&base_env.receipt, &ok_env.receipt) {
            (ParsedReceipt::Success(b), ParsedReceipt::Success(n)) => {
                assert_ne!(
                    b.correspondence_provenance_residual_sha256,
                    n.correspondence_provenance_residual_sha256
                );
            }
            _ => panic!("expected success receipts"),
        }

        // Extra unrecognized field inside `minirust_upstream` is surfaced.
        let mut extra = mr.clone();
        extra["correspondence_provenance"]["minirust_upstream"]["extra_mr"] = json!(1);
        let extra_env = parse_and_validate_receipt(&serde_json::to_vec(&extra).unwrap()).unwrap();
        assert_eq!(
            extra_env.unrecognized_fields,
            vec!["/correspondence_provenance/minirust_upstream/extra_mr"]
        );

        // `file_count` mismatch and invalid file digest produce invariant
        // violations.
        let mut bad_count = mr.clone();
        bad_count["correspondence_provenance"]["minirust_upstream"]["file_count"] = json!(1);
        bad_count["correspondence_provenance"]["minirust_upstream"]["files"]["spec/mem/basic.md"] =
            json!("not-sha");
        let bad_env = parse_and_validate_receipt(&serde_json::to_vec(&bad_count).unwrap()).unwrap();
        assert!(
            bad_env.invariant_violations.iter().any(|v| v.contains("file_count")),
            "{:?}",
            bad_env.invariant_violations
        );
        assert!(
            bad_env.invariant_violations.iter().any(|v| v.contains(
                "/correspondence_provenance/minirust_upstream/files/spec~1mem~1basic.md"
            )),
            "{:?}",
            bad_env.invariant_violations
        );

        // Non-string digest inside `files` is rejected operationally.
        let mut non_str = mr.clone();
        non_str["correspondence_provenance"]["minirust_upstream"]["files"]["spec/mem/basic.md"] =
            json!(123);
        let err = parse_and_validate_receipt(&serde_json::to_vec(&non_str).unwrap()).unwrap_err();
        assert!(
            err.message()
                .contains("/correspondence_provenance/minirust_upstream/files/spec~1mem~1basic.md"),
            "{}",
            err.message()
        );

        // Empty and non-empty untrimmed `files` keys must both fail
        // independently (`is_empty()` vs `trim() != rel`), as must empty
        // `files` (`file_count == 0`), untrimmed metadata, and bad SHAs.
        for bad_key in ["", "   ", " README.md "] {
            let mut bad_keys = mr.clone();
            bad_keys["correspondence_provenance"]["minirust_upstream"]["file_count"] = json!(1);
            bad_keys["correspondence_provenance"]["minirust_upstream"]["files"] =
                json!({ bad_key: h2 });
            let bad_key_env =
                parse_and_validate_receipt(&serde_json::to_vec(&bad_keys).unwrap()).unwrap();
            assert!(
                bad_key_env
                    .invariant_violations
                    .iter()
                    .any(|v| v.contains("files key") && v.contains("trimmed and non-empty")),
                "expected trimmed/non-empty files key violation for {bad_key:?}, got {:?}",
                bad_key_env.invariant_violations
            );
        }

        let mut zero_files = mr.clone();
        zero_files["correspondence_provenance"]["minirust_upstream"]["file_count"] = json!(0);
        zero_files["correspondence_provenance"]["minirust_upstream"]["files"] = json!({});
        let zero_env =
            parse_and_validate_receipt(&serde_json::to_vec(&zero_files).unwrap()).unwrap();
        assert!(
            zero_env.invariant_violations.iter().any(|v| v.contains("file_count (0)")),
            "{:?}",
            zero_env.invariant_violations
        );

        for (field, bad_val) in [
            ("upstream_repository", ""),
            ("upstream_repository", " https://example.invalid "),
            ("upstream_commit", ""),
            ("upstream_commit", " deadbeef "),
        ] {
            let mut bad_meta = mr.clone();
            bad_meta["correspondence_provenance"]["minirust_upstream"][field] = json!(bad_val);
            let meta_env =
                parse_and_validate_receipt(&serde_json::to_vec(&bad_meta).unwrap()).unwrap();
            assert!(
                meta_env
                    .invariant_violations
                    .iter()
                    .any(|v| v.contains(field) && v.contains("trimmed and non-empty")),
                "expected metadata violation for {field}={bad_val:?}, got {:?}",
                meta_env.invariant_violations
            );
        }

        for sha_field in ["upstream_pin_sha256", "tarball_sha256", "manifest_sha256"] {
            let mut bad_sha = mr.clone();
            bad_sha["correspondence_provenance"]["minirust_upstream"][sha_field] = json!("bad-sha");
            let sha_env =
                parse_and_validate_receipt(&serde_json::to_vec(&bad_sha).unwrap()).unwrap();
            assert!(
                sha_env
                    .invariant_violations
                    .iter()
                    .any(|v| v.contains(sha_field) && v.contains("64-character SHA-256")),
                "expected SHA-256 violation for {sha_field}, got {:?}",
                sha_env.invariant_violations
            );
        }
    }
}
