// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Pure sanitized renderers (`human`, `ledger`, `markdown`, `json`) for
//! Receipt Schema v3 inspection and 3-tier receipt diffs.

use std::{collections::BTreeSet, fmt::Write as _};

use serde::Serialize;

use crate::core::{
    digest::is_sha256_hex,
    inspect::{
        diff::{DiffTier, ReceiptDiff},
        profile::{ArtifactAxis, ContainmentAxis, ReplayAxis, ScopeAxis, TaintAxis},
        schema::{ParsedReceipt, ReceiptEnvelope},
    },
    sanitize::{
        SanitizedBlock, SanitizedInline, escape_gfm_cell, format_fenced_code_block,
        format_gfm_code_cell, sanitize_inline_string,
    },
};

/// Supported output formats for `cargo anneal inspect`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum InspectFormat {
    /// Human-readable summary card.
    #[default]
    Human,
    /// Deterministic line-oriented `key=value` golden ledger.
    Ledger,
    /// GitHub-Flavored Markdown report.
    Markdown,
    /// Structured JSON report envelope.
    Json,
}

/// Color control mode for terminal output.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum ColorChoice {
    /// Enable ANSI color when stdout is a TTY and `NO_COLOR` / `--passive`
    /// do not suppress it.
    #[default]
    Auto,
    /// Force ANSI color escapes.
    Always,
    /// Disable ANSI color escapes.
    Never,
}

/// Filterable report sections for `--section`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum InspectSection {
    /// Top-level verification summary banner.
    Summary,
    /// Orthogonal 6-axis assurance profile.
    Assurance,
    /// Cryptographic input and bundle digests.
    Digests,
    /// Closure symbol counts.
    Closures,
    /// Compiler census and selected-body counts.
    Census,
    /// Anti-vacuity specification warnings.
    Warnings,
    /// Recorded verification assumptions and deferred obligations.
    Assumptions,
    /// Phase timing breakdown.
    Timing,
    /// Unrecognized JSON field pointers.
    UnknownFields,
}

/// Artifact verification status computed optionally by the OS shell.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ArtifactVerificationSummary {
    /// Local directory path inspected for retained artifacts.
    pub directory: String,
    /// `true` when every checked artifact exists cleanly and matches digests.
    pub exact_match: bool,
    /// Number of regular files read and verified.
    pub checked_files: usize,
    /// List of failing artifact checks, if any.
    pub failures: Vec<String>,
}

/// Pure formatting options passed from CLI arguments.
#[derive(Clone, Debug, Default)]
pub struct RenderOptions {
    /// Selected output format (`human`, `ledger`, `markdown`, or `json`).
    pub format: InspectFormat,
    /// Whether ANSI SGR color styling is enabled.
    pub use_color: bool,
    /// Emit full 64-character SHA-256 digests instead of 12-char prefixes.
    pub full_digests: bool,
    /// Restrict human output to the primary summary status line.
    pub quiet: bool,
    /// Include full selected body/assumption/failure blocks.
    pub verbose: bool,
    /// Optional explicit `--section` display filter.
    pub sections: Option<BTreeSet<InspectSection>>,
}

impl RenderOptions {
    fn shows(&self, section: InspectSection) -> bool {
        match &self.sections {
            Some(set) => set.contains(&section),
            None => !self.quiet || section == InspectSection::Summary,
        }
    }

    fn fmt_digest(&self, hex: &str) -> String {
        if is_sha256_hex(hex) {
            if self.full_digests { hex.to_owned() } else { hex[..12].to_owned() }
        } else {
            let clean = sanitize_inline_string(hex);
            if self.full_digests || clean.chars().count() <= 12 {
                clean
            } else {
                let mut prefix: String = clean.chars().take(12).collect();
                prefix.push_str("...");
                prefix
            }
        }
    }
}

/// Render a validated [`ReceiptEnvelope`] in the requested format.
pub fn render_inspection(
    env: &ReceiptEnvelope,
    artifact_check: Option<&ArtifactVerificationSummary>,
    policy_violations: &[String],
    opts: &RenderOptions,
) -> String {
    match opts.format {
        InspectFormat::Human => render_human(env, artifact_check, policy_violations, opts),
        InspectFormat::Ledger => render_ledger(env, artifact_check, policy_violations),
        InspectFormat::Markdown => render_markdown(env, artifact_check, policy_violations, opts),
        InspectFormat::Json => {
            #[derive(Serialize)]
            struct JsonView<'a> {
                receipt_sha256: &'a str,
                status: &'a str,
                tainted: bool,
                taint_reasons: &'a [String],
                profile: &'a crate::core::inspect::profile::AssuranceProfile,
                unrecognized_fields: &'a [String],
                invariant_violations: &'a [String],
                policy_violations: &'a [String],
                artifact_verification: Option<&'a ArtifactVerificationSummary>,
                receipt: &'a ParsedReceipt,
            }
            let view = JsonView {
                receipt_sha256: &env.receipt_sha256,
                status: env.receipt.status(),
                tainted: !env.receipt.taint_reasons().is_empty(),
                taint_reasons: env.receipt.taint_reasons(),
                profile: &env.profile,
                unrecognized_fields: &env.unrecognized_fields,
                invariant_violations: &env.invariant_violations,
                policy_violations,
                artifact_verification: artifact_check,
                receipt: &env.receipt,
            };
            let mut out = serde_json::to_string_pretty(&view).unwrap_or_else(|_| "{}".to_owned());
            out.push('\n');
            out
        }
    }
}

/// Render a 3-tier [`ReceiptDiff`] in the requested format.
pub fn render_diff(diff: &ReceiptDiff, opts: &RenderOptions) -> String {
    match opts.format {
        InspectFormat::Json => {
            let mut out = serde_json::to_string_pretty(diff).unwrap_or_else(|_| "{}".to_owned());
            out.push('\n');
            out
        }
        InspectFormat::Ledger => {
            let mut out = String::new();
            let _ = writeln!(out, "diff.base_receipt_sha256={}", diff.base_receipt_sha256);
            let _ = writeln!(out, "diff.head_receipt_sha256={}", diff.head_receipt_sha256);
            let _ = writeln!(out, "diff.has_regressions={}", diff.has_regressions);
            let _ = writeln!(out, "diff.change_count={}", diff.changes.len());
            if !diff.base_invariant_violations.is_empty() {
                let _ = writeln!(
                    out,
                    "diff.base_invariant_violations={}",
                    diff.base_invariant_violations.len()
                );
                for (i, v) in diff.base_invariant_violations.iter().enumerate() {
                    let _ =
                        writeln!(out, "diff.base_invariant_violation.{i}={}", SanitizedInline(v));
                }
            }
            if !diff.head_invariant_violations.is_empty() {
                let _ = writeln!(
                    out,
                    "diff.head_invariant_violations={}",
                    diff.head_invariant_violations.len()
                );
                for (i, v) in diff.head_invariant_violations.iter().enumerate() {
                    let _ =
                        writeln!(out, "diff.head_invariant_violation.{i}={}", SanitizedInline(v));
                }
            }
            if !diff.base_unrecognized_fields.is_empty() {
                let _ = writeln!(
                    out,
                    "diff.base_unrecognized_fields={}",
                    diff.base_unrecognized_fields.len()
                );
                for (i, f) in diff.base_unrecognized_fields.iter().enumerate() {
                    let _ =
                        writeln!(out, "diff.base_unrecognized_field.{i}={}", SanitizedInline(f));
                }
            }
            if !diff.head_unrecognized_fields.is_empty() {
                let _ = writeln!(
                    out,
                    "diff.head_unrecognized_fields={}",
                    diff.head_unrecognized_fields.len()
                );
                for (i, f) in diff.head_unrecognized_fields.iter().enumerate() {
                    let _ =
                        writeln!(out, "diff.head_unrecognized_field.{i}={}", SanitizedInline(f));
                }
            }
            for (i, ch) in diff.changes.iter().enumerate() {
                let tier = match ch.tier {
                    DiffTier::TierA => "tier_a_regression",
                    DiffTier::TierB => "tier_b_trusted",
                    DiffTier::TierC => "tier_c_metadata",
                };
                let _ = writeln!(
                    out,
                    "diff.change.{i}={tier}: {} ({} -> {}) [{}]",
                    SanitizedInline(&ch.field),
                    SanitizedInline(&ch.base),
                    SanitizedInline(&ch.head),
                    SanitizedInline(&ch.note),
                );
            }
            out
        }
        InspectFormat::Markdown => {
            let mut out = String::new();
            out.push_str("## Anneal Receipt Diff\n\n");
            let has_invalid = !diff.base_invariant_violations.is_empty()
                || !diff.head_invariant_violations.is_empty();
            let has_unrecognized = !diff.base_unrecognized_fields.is_empty()
                || !diff.head_unrecognized_fields.is_empty();
            let _ = writeln!(
                out,
                "- **Base Receipt:** `{}`\n- **Head Receipt:** `{}`\n- **Regressions:** `{}`",
                opts.fmt_digest(&diff.base_receipt_sha256),
                opts.fmt_digest(&diff.head_receipt_sha256),
                diff.has_regressions
            );
            if has_invalid {
                out.push_str("- **Envelope Validity:** `INVALID ENVELOPE(S)`\n");
            }
            if has_unrecognized {
                out.push_str("- **Extensions:** `UNVERIFIED EXTENSIONS`\n");
            }
            out.push('\n');
            if has_unrecognized {
                let mut parts = Vec::new();
                if !diff.base_unrecognized_fields.is_empty() {
                    let fields: Vec<String> = diff
                        .base_unrecognized_fields
                        .iter()
                        .map(|f| format_gfm_code_cell(f))
                        .collect();
                    parts.push(format!("base: {}", fields.join(", ")));
                }
                if !diff.head_unrecognized_fields.is_empty() {
                    let fields: Vec<String> = diff
                        .head_unrecognized_fields
                        .iter()
                        .map(|f| format_gfm_code_cell(f))
                        .collect();
                    parts.push(format!("head: {}", fields.join(", ")));
                }
                let _ = writeln!(
                    out,
                    "> [!WARNING]\n> **UNVERIFIED EXTENSIONS:** {}\n",
                    parts.join("; ")
                );
            }
            if has_invalid {
                out.push_str("### Invariant Violations\n\n");
                for v in &diff.base_invariant_violations {
                    let _ = writeln!(out, "- **base:** {}", escape_gfm_cell(v));
                }
                for v in &diff.head_invariant_violations {
                    let _ = writeln!(out, "- **head:** {}", escape_gfm_cell(v));
                }
                out.push('\n');
            }
            if diff.changes.is_empty() {
                if !has_invalid && !has_unrecognized {
                    out.push_str("No differences recorded across verified fields.\n");
                }
                return out;
            }
            out.push_str("| Tier | Field | Base | Head | Note |\n|---|---|---|---|---|\n");
            for ch in &diff.changes {
                let tier = match ch.tier {
                    DiffTier::TierA => "Tier A (Regression)",
                    DiffTier::TierB => "Tier B (Trusted/Spec)",
                    DiffTier::TierC => "Tier C (Metadata)",
                };
                let _ = writeln!(
                    out,
                    "| {} | {} | {} | {} | {} |",
                    tier,
                    format_gfm_code_cell(&ch.field),
                    format_gfm_code_cell(&ch.base),
                    format_gfm_code_cell(&ch.head),
                    escape_gfm_cell(&ch.note),
                );
            }
            out
        }
        InspectFormat::Human => {
            let mut out = String::new();
            let has_invalid = !diff.base_invariant_violations.is_empty()
                || !diff.head_invariant_violations.is_empty();
            let has_unrecognized = !diff.base_unrecognized_fields.is_empty()
                || !diff.head_unrecognized_fields.is_empty();
            let status = match (has_invalid, diff.has_regressions) {
                (true, true) => "INVALID ENVELOPE(S) / REGRESSIONS DETECTED",
                (true, false) => "INVALID ENVELOPE(S)",
                (false, true) => "REGRESSIONS DETECTED",
                (false, false) => "NO REGRESSIONS",
            };
            let ext_suffix = if has_unrecognized { " [UNVERIFIED EXTENSIONS]" } else { "" };
            let _ = writeln!(
                out,
                "Receipt Diff ({} -> {}): {status}{ext_suffix}",
                opts.fmt_digest(&diff.base_receipt_sha256),
                opts.fmt_digest(&diff.head_receipt_sha256),
            );
            if !diff.base_unrecognized_fields.is_empty() {
                let _ = writeln!(
                    out,
                    "  Base Unrecognized Fields ({}): {}",
                    diff.base_unrecognized_fields.len(),
                    sanitize_inline_string(&diff.base_unrecognized_fields.join(", ")),
                );
            }
            if !diff.head_unrecognized_fields.is_empty() {
                let _ = writeln!(
                    out,
                    "  Head Unrecognized Fields ({}): {}",
                    diff.head_unrecognized_fields.len(),
                    sanitize_inline_string(&diff.head_unrecognized_fields.join(", ")),
                );
            }
            if !diff.base_invariant_violations.is_empty() {
                out.push_str("  Base Invariant Violations:\n");
                for v in &diff.base_invariant_violations {
                    let _ = writeln!(out, "    ! {}", SanitizedInline(v));
                }
            }
            if !diff.head_invariant_violations.is_empty() {
                out.push_str("  Head Invariant Violations:\n");
                for v in &diff.head_invariant_violations {
                    let _ = writeln!(out, "    ! {}", SanitizedInline(v));
                }
            }
            if diff.changes.is_empty() {
                if !has_invalid && !has_unrecognized {
                    out.push_str("  no changes\n");
                }
                return out;
            }
            for ch in &diff.changes {
                let label = match ch.tier {
                    DiffTier::TierA => "[Tier A REGRESSION]",
                    DiffTier::TierB => "[Tier B Trusted/Spec]",
                    DiffTier::TierC => "[Tier C Info]",
                };
                let _ = writeln!(
                    out,
                    "  {label} {}: {} -> {} ({})",
                    SanitizedInline(&ch.field),
                    SanitizedInline(&ch.base),
                    SanitizedInline(&ch.head),
                    SanitizedInline(&ch.note),
                );
            }
            out
        }
    }
}

fn style_badge(use_color: bool, ok: bool, warn: bool, text: &str) -> String {
    if !use_color {
        return text.to_owned();
    }
    let code = if !ok {
        "31;1"
    } else if warn {
        "33;1"
    } else {
        "32;1"
    };
    format!("\x1b[{code}m{text}\x1b[0m")
}

fn fmt_horizon(h: &crate::core::inspect::schema::HorizonRecord) -> String {
    match h {
        crate::core::inspect::schema::HorizonRecord::Unbounded => "unbounded".to_owned(),
        crate::core::inspect::schema::HorizonRecord::Bounded { k } => format!("bounded(k={k})"),
        crate::core::inspect::schema::HorizonRecord::Unknown { raw_kind } => {
            format!("unknown({})", sanitize_inline_string(raw_kind))
        }
    }
}

fn has_qualifying_shim(shims: Option<&[crate::core::inspect::schema::TcbShimEntry]>) -> bool {
    shims.is_some_and(|list| list.iter().any(|s| s.kind != "capture_driver"))
}

fn assurance_qualification_tags(receipt: &ParsedReceipt) -> Vec<String> {
    let mut tags = Vec::new();
    let horizon_opt = match receipt {
        ParsedReceipt::Failure(f) => f.horizon.as_ref(),
        ParsedReceipt::Success(s) => s.horizon.as_ref(),
    };
    if let Some(h) = horizon_opt
        && !matches!(h, crate::core::inspect::schema::HorizonRecord::Unbounded)
    {
        tags.push(format!("horizon={}", fmt_horizon(h)));
    }
    if let ParsedReceipt::Success(s) = receipt {
        if has_qualifying_shim(s.tcb_shims.as_deref())
            || has_qualifying_shim(s.correspondence_tcb_shims.as_deref())
        {
            tags.push("tcb_shims=non_empty".to_owned());
        }
        let has_prov_qual = s.correspondence_qualifiers.as_ref().is_some_and(|q| {
            !q.choice_total || !q.assumed_seams.is_empty() || q.scope_kind == "partial_gate"
        }) || !s.correspondence_taint_reasons.is_empty();
        if has_prov_qual {
            tags.push("provenance=qualified".to_owned());
        }
        // No Pass 2 record binds the model this receipt relied on (Profile v2,
        // unpinned Lean, or the decoupled sentinel), so the success is only as
        // strong as a separate `anneal-audit --require-correspondence` run.
        if !s.correspondence_applicable {
            tags.push("correspondence=inapplicable".to_owned());
        }
    }
    tags
}

fn fmt_shims_summary(shims: &[crate::core::inspect::schema::TcbShimEntry]) -> String {
    if shims.is_empty() {
        return "none".to_owned();
    }
    shims
        .iter()
        .map(|s| format!("{} ({}:{})", s.id, s.kind, s.status))
        .collect::<Vec<_>>()
        .join(", ")
}

fn fmt_relation_summary(rel: &crate::core::inspect::schema::ModelSystemRelation) -> String {
    let mut parts = vec![rel.qualifier.as_deref().unwrap_or("-").to_owned(), rel.direction.clone()];
    if let Some(anchor) = &rel.anchored_at {
        parts.push(format!("anchor={anchor}"));
    }
    parts.push(format!("claims=[{}]", rel.licensed_claim_shapes.join(",")));
    if !rel.unmodeled_downstream.is_empty() {
        parts.push(format!("unmodeled=[{}]", rel.unmodeled_downstream.join(",")));
    }
    format!("{} ({})", rel.kind, parts.join(", "))
}

fn render_human(
    env: &ReceiptEnvelope,
    artifact_check: Option<&ArtifactVerificationSummary>,
    policy_violations: &[String],
    opts: &RenderOptions,
) -> String {
    let mut out = String::new();
    let tainted = !env.receipt.taint_reasons().is_empty();
    let qual_tags = assurance_qualification_tags(&env.receipt);
    let qualified = !qual_tags.is_empty();
    let badge = style_badge(
        opts.use_color,
        env.receipt.is_success() && env.invariant_violations.is_empty(),
        tainted || qualified || !env.unrecognized_fields.is_empty(),
        &sanitize_inline_string(env.receipt.status()),
    );
    let qual_suffix = if qualified { " [QUALIFIED]" } else { "" };

    if opts.shows(InspectSection::Summary) {
        let _ = writeln!(out, "Anneal Receipt v3: {badge}{qual_suffix}");
        if qualified {
            let _ = writeln!(
                out,
                "  qualified_assurance: {}",
                sanitize_inline_string(&qual_tags.join(", "))
            );
        }
        let _ = writeln!(out, "  receipt_sha256: {}", opts.fmt_digest(&env.receipt_sha256));
        if !env.unrecognized_fields.is_empty() {
            let _ = writeln!(
                out,
                "  ! UNVERIFIED EXTENSIONS ({} unrecognized v3 field(s)): {}",
                env.unrecognized_fields.len(),
                sanitize_inline_string(&env.unrecognized_fields.join(", "))
            );
        }
        match &env.receipt {
            ParsedReceipt::Failure(f) => {
                if let Some(stage) = &f.assurance_stage {
                    let _ = writeln!(out, "  stage: {}", SanitizedInline(stage));
                }
                if let Some(h) = &f.horizon {
                    let _ = writeln!(out, "  horizon: {}", fmt_horizon(h));
                }
                let _ = writeln!(out, "  phase: {}", SanitizedInline(&f.phase));
                let _ = writeln!(out, "  detail:\n{}", SanitizedBlock(&f.detail));
                if let Some(hint) = &f.hint {
                    let _ = writeln!(out, "  hint:\n{}", SanitizedBlock(hint));
                }
            }
            ParsedReceipt::Success(s) => {
                if let Some(stage) = &s.assurance_stage {
                    let _ = writeln!(out, "  stage: {}", SanitizedInline(stage));
                }
                if let Some(h) = &s.horizon {
                    let _ = writeln!(out, "  horizon: {}", fmt_horizon(h));
                }
                if let Some(cf) = &s.candidate_features
                    && !cf.is_empty()
                {
                    let _ = writeln!(
                        out,
                        "  candidate_features: {}",
                        sanitize_inline_string(&cf.join(", "))
                    );
                }
                let stdlib_suffix = s
                    .stdlib_crate
                    .as_deref()
                    .map_or_else(String::new, |sc| format!(", stdlib={}", SanitizedInline(sc)));
                let _ = writeln!(
                    out,
                    "  crate: {} ({}, edition {}, target {}, panic={}{})",
                    SanitizedInline(&s.crate_name),
                    SanitizedInline(&s.crate_type),
                    SanitizedInline(&s.edition),
                    SanitizedInline(&s.target),
                    SanitizedInline(&s.panic),
                    stdlib_suffix,
                );
                let _ = writeln!(
                    out,
                    "  theorem: {} == {}",
                    SanitizedInline(&s.theorem),
                    SanitizedInline(&s.canonical_root)
                );
                let _ = writeln!(out, "  specification: {}", SanitizedInline(&s.specification));
                if let Some(pa) = &s.permitted_axioms {
                    let _ = writeln!(
                        out,
                        "  permitted_axioms: {}",
                        sanitize_inline_string(&pa.join(", "))
                    );
                }
                if let Some(shims) = &s.tcb_shims {
                    let _ = writeln!(
                        out,
                        "  tcb_shims ({}): {}",
                        shims.len(),
                        sanitize_inline_string(&fmt_shims_summary(shims))
                    );
                }
                if let Some(rel) = &s.model_system_relation {
                    let _ = writeln!(
                        out,
                        "  relation: {}",
                        sanitize_inline_string(&fmt_relation_summary(rel))
                    );
                }
                if let Some(reason) = &s.correspondence_inapplicable_reason {
                    let _ = writeln!(
                        out,
                        "  correspondence: inapplicable ({})",
                        SanitizedInline(reason)
                    );
                }
                if s.correspondence_schema_version == Some(3) {
                    let qual_str = s.correspondence_qualifiers.as_ref().map_or_else(
                        || "-".to_owned(),
                        |q| {
                            format!(
                                "choice_total:{},scope:{},seams:[{}]",
                                q.choice_total,
                                q.scope_kind,
                                q.assumed_seams.join(",")
                            )
                        },
                    );
                    let rel_str = s
                        .correspondence_model_system_relation
                        .as_ref()
                        .map_or_else(|| "-".to_owned(), fmt_relation_summary);
                    let _ = writeln!(
                        out,
                        "  provenance_v3: claim={}, axioms=[{}], relation={}, shims=[{}], taints=[{}], qualifiers=({})",
                        SanitizedInline(s.correspondence_claim_kind.as_deref().unwrap_or("-")),
                        sanitize_inline_string(
                            &s.correspondence_permitted_axioms.as_deref().unwrap_or(&[]).join(",")
                        ),
                        sanitize_inline_string(&rel_str),
                        sanitize_inline_string(&fmt_shims_summary(
                            s.correspondence_tcb_shims.as_deref().unwrap_or(&[])
                        )),
                        sanitize_inline_string(&s.correspondence_taint_reasons.join(",")),
                        sanitize_inline_string(&qual_str)
                    );
                }
            }
        }
    }

    if opts.shows(InspectSection::Assurance) {
        out.push_str("Assurance Profile:\n");
        let taint_str = match &env.profile.taint {
            TaintAxis::Untainted => "untainted".to_owned(),
            TaintAxis::Tainted { reasons } => {
                format!("tainted ({})", sanitize_inline_string(&reasons.join(", ")))
            }
        };
        let scope_str = match &env.profile.scope {
            ScopeAxis::WholeCrate { selected_bodies, census_items } => {
                format!("crate ({selected_bodies}/{census_items} bodies)")
            }
            ScopeAxis::SelectedUnits { roots, instantiations, selected_bodies, census_items } => {
                format!(
                    "selected_unit ({roots} roots, {instantiations} inst, {selected_bodies}/{census_items} bodies)"
                )
            }
            ScopeAxis::Failed { status } => format!("failed ({})", SanitizedInline(status)),
        };
        let sandbox_str = match &env.profile.containment {
            ContainmentAxis::Sandboxed { mode } => format!("sandboxed ({})", SanitizedInline(mode)),
            ContainmentAxis::Unsandboxed => "unsandboxed (none)".to_owned(),
            ContainmentAxis::Unknown => "unknown".to_owned(),
        };
        let replay_str = match &env.profile.replay {
            ReplayAxis::SingleKernel { replayed_declarations } => {
                format!("1 kernel ({replayed_declarations} decls)")
            }
            ReplayAxis::MultiKernel { replayed_declarations, kernels_passed, kernels_skipped } => {
                format!(
                    "multi-kernel ({replayed_declarations} decls, passed={}, skipped={})",
                    sanitize_inline_string(&kernels_passed.join(",")),
                    sanitize_inline_string(&kernels_skipped.join(","))
                )
            }
            ReplayAxis::NotReached => "not reached".to_owned(),
        };
        let axiom_str = match &env.profile.axioms {
            crate::core::inspect::profile::AxiomAxis::StrictFoundation { axioms } => {
                format!("[{}]", sanitize_inline_string(&axioms.join(", ")))
            }
            crate::core::inspect::profile::AxiomAxis::ContainsSorry { axioms, sorry_count } => {
                format!(
                    "SORRY ({sorry_count} decls; [{}])",
                    sanitize_inline_string(&axioms.join(", "))
                )
            }
            crate::core::inspect::profile::AxiomAxis::Unexpected { axioms } => {
                format!("UNEXPECTED ([{}])", sanitize_inline_string(&axioms.join(", ")))
            }
            crate::core::inspect::profile::AxiomAxis::NotReached => "not reached".to_owned(),
        };
        let art_str = match &env.profile.artifacts {
            ArtifactAxis::Omitted => "omitted".to_owned(),
            ArtifactAxis::RetainedPathRecorded { path } => {
                format!("recorded ({})", SanitizedInline(path))
            }
            ArtifactAxis::VerifiedLocal { path, checked_files } => {
                format!("verified ({checked_files} files at {})", SanitizedInline(path))
            }
        };
        let _ = writeln!(out, "  1. taint:       {taint_str}");
        if let ParsedReceipt::Success(s) = &env.receipt
            && let Some(features) = &s.unstable_features
        {
            let _ = writeln!(
                out,
                "     unstable features: allowed=[{}], observed=[{}], incomplete=[{}]",
                sanitize_inline_string(&features.allowed.join(", ")),
                sanitize_inline_string(&features.observed.join(", ")),
                sanitize_inline_string(&features.incomplete_observed.join(", "))
            );
        }
        let _ = writeln!(out, "  2. scope:       {scope_str}");
        let _ = writeln!(out, "  3. containment: {sandbox_str}");
        let _ = writeln!(out, "  4. replay:      {replay_str}");
        let _ = writeln!(out, "  5. axioms:      {axiom_str}");
        let _ = writeln!(out, "  6. artifacts:   {art_str}");
    }

    if let ParsedReceipt::Success(s) = &env.receipt {
        if opts.shows(InspectSection::Digests) {
            out.push_str("Digests:\n");
            let _ = writeln!(out, "  request:       {}", opts.fmt_digest(&s.request_sha256));
            let _ = writeln!(out, "  capture:       {}", opts.fmt_digest(&s.capture_sha256));
            if let Some(shards_sha) = &s.capture_shards_sha256 {
                let _ = writeln!(out, "  capture_shards: {}", opts.fmt_digest(shards_sha));
            }
            if let Some(sh) = &s.shards {
                let _ = writeln!(
                    out,
                    "  shards:        {} shard(s), {} body(s), {} SCC(s) ({} cyclic), id_tree={}",
                    sh.total_shards,
                    sh.total_bodies,
                    sh.total_sccs,
                    sh.cyclic_sccs,
                    opts.fmt_digest(&sh.id_tree_sha256)
                );
            }
            let _ = writeln!(out, "  capture_bin:   {}", opts.fmt_digest(&s.capture_binary_sha256));
            let _ = writeln!(out, "  model:         {}", opts.fmt_digest(&s.model_manifest_sha256));
            let _ = writeln!(
                out,
                "  specification: {}",
                opts.fmt_digest(&s.specification_manifest_sha256)
            );
            if let Some(pin) = &s.upstream_pin_sha256 {
                let _ = writeln!(out, "  miri_pin:      {}", opts.fmt_digest(pin));
            }
        }
        if opts.shows(InspectSection::Closures) && (opts.verbose || opts.sections.is_some()) {
            let _ = writeln!(
                out,
                "Closures: subject={}, model={}, specification={}",
                s.subject_closure.len(),
                s.model_closure.len(),
                s.specification_closure.len()
            );
        }
        if opts.shows(InspectSection::Census) && (opts.verbose || opts.sections.is_some()) {
            let _ = writeln!(
                out,
                "Census: {} item(s), {} selected body(s), {} source file(s)",
                s.census.len(),
                s.selected.len(),
                s.sources.len()
            );
            for item in &s.selected {
                let _ = writeln!(
                    out,
                    "  selected[{}]: {} (def_id={})",
                    item.body_index,
                    SanitizedInline(&item.path),
                    item.def_id
                );
            }
        }
        if opts.shows(InspectSection::Warnings) && !s.spec_warnings.is_empty() {
            out.push_str("Anti-Vacuity Warnings:\n");
            for w in &s.spec_warnings {
                let _ = writeln!(
                    out,
                    "  [{}] {}: {}",
                    SanitizedInline(&w.code),
                    SanitizedInline(&w.declaration),
                    SanitizedInline(&w.message)
                );
            }
        }
        if opts.shows(InspectSection::Assumptions) && (opts.verbose || opts.sections.is_some()) {
            out.push_str("Assumptions:\n");
            for a in &s.assumptions {
                let _ = writeln!(out, "  - {}", SanitizedInline(a));
            }
            out.push_str("Deferred:\n");
            for d in &s.deferred {
                let _ = writeln!(out, "  - {}", SanitizedInline(d));
            }
        }
        if opts.shows(InspectSection::Timing) {
            let _ = writeln!(
                out,
                "Timing: capture={}ms, proof_and_audit={}ms, total={}ms",
                s.timing_ms.capture, s.timing_ms.proof_and_audit, s.timing_ms.total
            );
        }
    }

    if let Some(check) = artifact_check {
        let _ = writeln!(
            out,
            "Artifacts Check: {} ({} files verified at {})",
            if check.exact_match { "PASS" } else { "FAIL" },
            check.checked_files,
            SanitizedInline(&check.directory),
        );
        for err in &check.failures {
            let _ = writeln!(out, "  ! {}", SanitizedInline(err));
        }
    }

    if opts.shows(InspectSection::UnknownFields) && !env.unrecognized_fields.is_empty() {
        let _ = writeln!(
            out,
            "Unrecognized Fields ({}): {}",
            env.unrecognized_fields.len(),
            sanitize_inline_string(&env.unrecognized_fields.join(", "))
        );
    }
    if !env.invariant_violations.is_empty() {
        out.push_str("Invariant Violations:\n");
        for v in &env.invariant_violations {
            let _ = writeln!(out, "  ! {}", SanitizedInline(v));
        }
    }
    if !policy_violations.is_empty() {
        out.push_str("Policy Violations:\n");
        for p in policy_violations {
            let _ = writeln!(out, "  ! {}", SanitizedInline(p));
        }
    }
    out
}

fn render_ledger(
    env: &ReceiptEnvelope,
    artifact_check: Option<&ArtifactVerificationSummary>,
    policy_violations: &[String],
) -> String {
    let mut out = String::new();
    let _ = writeln!(out, "receipt_sha256={}", SanitizedInline(&env.receipt_sha256));
    let _ = writeln!(out, "schema_version=3");
    let _ = writeln!(out, "status={}", SanitizedInline(env.receipt.status()));
    let _ = writeln!(
        out,
        "taint_reasons={}",
        sanitize_inline_string(&env.receipt.taint_reasons().join(","))
    );
    let _ = writeln!(out, "invariant_violations={}", env.invariant_violations.len());
    let _ = writeln!(out, "policy_violations={}", policy_violations.len());
    let sanitized_unknown: Vec<String> =
        env.unrecognized_fields.iter().map(|p| sanitize_inline_string(p)).collect();
    let _ = writeln!(out, "unrecognized_fields={}", sanitized_unknown.join(","));
    match &env.receipt {
        ParsedReceipt::Failure(f) => {
            if let Some(stage) = &f.assurance_stage {
                let _ = writeln!(out, "assurance_stage={}", SanitizedInline(stage));
            }
            if let Some(h) = &f.horizon {
                let _ = writeln!(out, "horizon={}", fmt_horizon(h));
            }
            let _ = writeln!(out, "failure.phase={}", SanitizedInline(&f.phase));
            let _ = writeln!(out, "failure.detail={}", SanitizedInline(&f.detail));
        }
        ParsedReceipt::Success(s) => {
            if let Some(stage) = &s.assurance_stage {
                let _ = writeln!(out, "assurance_stage={}", SanitizedInline(stage));
            }
            if let Some(h) = &s.horizon {
                let _ = writeln!(out, "horizon={}", fmt_horizon(h));
            }
            if let Some(cf) = &s.candidate_features {
                let _ =
                    writeln!(out, "candidate_features={}", sanitize_inline_string(&cf.join(",")));
            }
            if let Some(pa) = &s.permitted_axioms {
                let _ = writeln!(out, "permitted_axioms={}", sanitize_inline_string(&pa.join(",")));
            }
            if let Some(shims) = &s.tcb_shims {
                let ids: Vec<String> = shims
                    .iter()
                    .map(|t| sanitize_inline_string(&format!("{}:{}:{}", t.id, t.kind, t.status)))
                    .collect();
                let _ = writeln!(out, "tcb_shims={}", ids.join(","));
            }
            if let Some(rel) = &s.model_system_relation {
                let _ = writeln!(
                    out,
                    "model_system_relation={}",
                    sanitize_inline_string(&fmt_relation_summary(rel))
                );
            }
            if let Some(sv) = s.correspondence_schema_version {
                let _ = writeln!(out, "correspondence_provenance.schema_version={sv}");
            }
            if let Some(ck) = &s.correspondence_claim_kind {
                let _ =
                    writeln!(out, "correspondence_provenance.claim_kind={}", SanitizedInline(ck));
            }
            if let Some(reason) = &s.correspondence_inapplicable_reason {
                let _ = writeln!(out, "correspondence_provenance.applicable=false");
                let _ =
                    writeln!(out, "correspondence_provenance.reason={}", SanitizedInline(reason));
            }
            if let Some(pa) = &s.correspondence_permitted_axioms {
                let _ = writeln!(
                    out,
                    "correspondence_provenance.permitted_axioms={}",
                    sanitize_inline_string(&pa.join(","))
                );
            }
            if let Some(shims) = &s.correspondence_tcb_shims {
                let ids: Vec<String> = shims
                    .iter()
                    .map(|t| sanitize_inline_string(&format!("{}:{}:{}", t.id, t.kind, t.status)))
                    .collect();
                let _ = writeln!(out, "correspondence_provenance.tcb_shims={}", ids.join(","));
            }
            if let Some(rel) = &s.correspondence_model_system_relation {
                let _ = writeln!(
                    out,
                    "correspondence_provenance.model_system_relation={}",
                    sanitize_inline_string(&fmt_relation_summary(rel))
                );
            }
            if !s.correspondence_taint_reasons.is_empty() {
                let _ = writeln!(
                    out,
                    "correspondence_provenance.taint_reasons={}",
                    sanitize_inline_string(&s.correspondence_taint_reasons.join(","))
                );
            }
            if let Some(q) = &s.correspondence_qualifiers {
                let _ = writeln!(
                    out,
                    "correspondence_provenance.qualifiers=choice_total:{},scope:{},seams:[{}]",
                    q.choice_total,
                    SanitizedInline(&q.scope_kind),
                    sanitize_inline_string(&q.assumed_seams.join(","))
                );
            }
            let _ = writeln!(out, "crate.name={}", SanitizedInline(&s.crate_name));
            let _ = writeln!(out, "crate.target={}", SanitizedInline(&s.target));
            if let Some(sc) = &s.stdlib_crate {
                let _ = writeln!(out, "crate.stdlib_crate={}", SanitizedInline(sc));
            }
            let _ = writeln!(out, "scope.kind={}", SanitizedInline(&s.scope_kind));
            let _ =
                writeln!(out, "elaboration_sandbox={}", SanitizedInline(&s.elaboration_sandbox));
            let _ = writeln!(out, "audit.theorem={}", SanitizedInline(&s.theorem));
            let _ = writeln!(out, "audit.canonical_root={}", SanitizedInline(&s.canonical_root));
            let _ = writeln!(out, "audit.specification={}", SanitizedInline(&s.specification));
            let _ = writeln!(out, "audit.axioms={}", sanitize_inline_string(&s.axioms.join(",")));
            let _ = writeln!(out, "audit.replay={}", s.replay);
            let _ = writeln!(out, "audit.exact_type={}", s.exact_type);
            let _ = writeln!(out, "audit.replayed_declarations={}", s.replayed_declarations);
            let _ = writeln!(out, "digest.request_sha256={}", SanitizedInline(&s.request_sha256));
            let _ = writeln!(out, "digest.capture_sha256={}", SanitizedInline(&s.capture_sha256));
            if let Some(shards_sha) = &s.capture_shards_sha256 {
                let _ = writeln!(
                    out,
                    "digest.capture_shards_sha256={}",
                    SanitizedInline(shards_sha)
                );
            }
            let _ = writeln!(
                out,
                "digest.capture_binary_sha256={}",
                SanitizedInline(&s.capture_binary_sha256)
            );
            let _ = writeln!(
                out,
                "digest.model_manifest_sha256={}",
                SanitizedInline(&s.model_manifest_sha256)
            );
            let _ = writeln!(
                out,
                "digest.specification_manifest_sha256={}",
                SanitizedInline(&s.specification_manifest_sha256)
            );
            let _ = writeln!(out, "counts.selected={}", s.selected.len());
            let _ = writeln!(out, "counts.census={}", s.census.len());
            let _ = writeln!(out, "counts.sources={}", s.sources.len());
            if let Some(sh) = &s.shards {
                let _ = writeln!(out, "counts.shards={}", sh.total_shards);
                let _ = writeln!(
                    out,
                    "shards.id_tree_sha256={}",
                    SanitizedInline(&sh.id_tree_sha256)
                );
            }
            let _ = writeln!(out, "counts.spec_warnings={}", s.spec_warnings.len());
        }
    }
    if let Some(check) = artifact_check {
        let _ = writeln!(out, "artifacts.verified={}", check.exact_match);
        let _ = writeln!(out, "artifacts.checked_files={}", check.checked_files);
    }
    out
}

fn render_markdown(
    env: &ReceiptEnvelope,
    artifact_check: Option<&ArtifactVerificationSummary>,
    policy_violations: &[String],
    opts: &RenderOptions,
) -> String {
    let mut out = String::new();
    let _ =
        writeln!(out, "## Anneal Receipt v3 ({})\n", format_gfm_code_cell(env.receipt.status()));
    if !env.unrecognized_fields.is_empty() {
        let fields: Vec<String> =
            env.unrecognized_fields.iter().map(|f| format_gfm_code_cell(f)).collect();
        let _ = writeln!(
            out,
            "> [!WARNING]\n> **UNVERIFIED EXTENSIONS:** receipt contains {} unrecognized v3 field(s): {}\n",
            env.unrecognized_fields.len(),
            fields.join(", ")
        );
    }
    let (stage_opt, horizon_opt) = match &env.receipt {
        ParsedReceipt::Failure(f) => (f.assurance_stage.as_deref(), f.horizon.as_ref()),
        ParsedReceipt::Success(s) => (s.assurance_stage.as_deref(), s.horizon.as_ref()),
    };
    let tags = assurance_qualification_tags(&env.receipt);
    if !tags.is_empty() {
        let _ = writeln!(
            out,
            "> [!WARNING]\n> **QUALIFIED ASSURANCE:** verification carries explicit bounds or TCB qualifications ({})\n",
            tags.iter().map(|t| format_gfm_code_cell(t)).collect::<Vec<_>>().join(", ")
        );
    }
    out.push_str("| Property | Value |\n|---|---|\n");
    let _ = writeln!(
        out,
        "| Receipt SHA-256 | {} |",
        format_gfm_code_cell(&opts.fmt_digest(&env.receipt_sha256))
    );
    if let Some(stage) = stage_opt {
        let _ = writeln!(out, "| Assurance Stage | {} |", format_gfm_code_cell(stage));
    }
    if let Some(h) = horizon_opt {
        let _ = writeln!(out, "| Horizon | {} |", format_gfm_code_cell(&fmt_horizon(h)));
    }
    let _ = writeln!(
        out,
        "| Taint | {} |",
        if env.receipt.taint_reasons().is_empty() {
            "`untainted`".to_owned()
        } else {
            format_gfm_code_cell(&env.receipt.taint_reasons().join(", "))
        }
    );
    if let ParsedReceipt::Success(s) = &env.receipt {
        let _ = writeln!(
            out,
            "| Target | {} ({}) |",
            format_gfm_code_cell(&s.crate_name),
            format_gfm_code_cell(&s.target)
        );
        let _ = writeln!(
            out,
            "| Scope | {} ({} selected / {} census) |",
            format_gfm_code_cell(&s.scope_kind),
            s.selected.len(),
            s.census.len()
        );
        let _ = writeln!(out, "| Containment | {} |", format_gfm_code_cell(&s.elaboration_sandbox));
        let _ = writeln!(
            out,
            "| Replay | `{}` (`{}` decls, `exactType={}`) |",
            s.replay, s.replayed_declarations, s.exact_type
        );
        if let Some(cf) = &s.candidate_features
            && !cf.is_empty()
        {
            let _ =
                writeln!(out, "| Candidate Features | {} |", format_gfm_code_cell(&cf.join(", ")));
        }
        let _ = writeln!(out, "| Axioms | {} |", format_gfm_code_cell(&s.axioms.join(", ")));
        if let Some(pa) = &s.permitted_axioms {
            let _ =
                writeln!(out, "| Permitted Axioms | {} |", format_gfm_code_cell(&pa.join(", ")));
        }
        if let Some(shims) = &s.tcb_shims {
            let _ = writeln!(
                out,
                "| TCB Shims | {} |",
                format_gfm_code_cell(&fmt_shims_summary(shims))
            );
        }
        if let Some(rel) = &s.model_system_relation {
            let _ = writeln!(
                out,
                "| Model-System Relation | {} |",
                format_gfm_code_cell(&fmt_relation_summary(rel))
            );
        }
        if let Some(reason) = &s.correspondence_inapplicable_reason {
            let _ = writeln!(
                out,
                "| Correspondence Provenance | not applicable: {} |",
                format_gfm_code_cell(reason)
            );
        }
        if let Some(sv) = s.correspondence_schema_version {
            let _ = writeln!(
                out,
                "| Correspondence Provenance | `v{sv}`{} |",
                s.correspondence_claim_kind
                    .as_deref()
                    .map_or_else(String::new, |ck| format!(" ({})", format_gfm_code_cell(ck)))
            );
        }
        if let Some(pa) = &s.correspondence_permitted_axioms {
            let _ = writeln!(
                out,
                "| Provenance Permitted Axioms | {} |",
                format_gfm_code_cell(&pa.join(", "))
            );
        }
        if let Some(rel) = &s.correspondence_model_system_relation {
            let _ = writeln!(
                out,
                "| Provenance Relation | {} |",
                format_gfm_code_cell(&fmt_relation_summary(rel))
            );
        }
        if let Some(shims) = &s.correspondence_tcb_shims {
            let _ = writeln!(
                out,
                "| Provenance TCB Shims | {} |",
                format_gfm_code_cell(&fmt_shims_summary(shims))
            );
        }
        if !s.correspondence_taint_reasons.is_empty() {
            let _ = writeln!(
                out,
                "| Provenance Taint | {} |",
                format_gfm_code_cell(&s.correspondence_taint_reasons.join(", "))
            );
        }
        if let Some(q) = &s.correspondence_qualifiers {
            let q_desc = format!(
                "choice_total={}, scope={}, assumed_seams=[{}]",
                q.choice_total,
                q.scope_kind,
                q.assumed_seams.join(", ")
            );
            let _ = writeln!(out, "| Provenance Qualifiers | {} |", format_gfm_code_cell(&q_desc));
        }
        if let Some(sh) = &s.shards {
            let _ = writeln!(
                out,
                "| Capture Shards | `{}` shard(s), `{}` SCC(s) (`{}` cyclic) |",
                sh.total_shards, sh.total_sccs, sh.cyclic_sccs
            );
        }
        let _ = writeln!(
            out,
            "| Model Digest | {} |",
            format_gfm_code_cell(&opts.fmt_digest(&s.model_manifest_sha256))
        );
        let _ = writeln!(
            out,
            "| Specification Digest | {} |",
            format_gfm_code_cell(&opts.fmt_digest(&s.specification_manifest_sha256))
        );
    } else if let ParsedReceipt::Failure(f) = &env.receipt {
        let _ = writeln!(out, "| Phase | {} |", format_gfm_code_cell(&f.phase));
        let _ = writeln!(out, "| Detail | {} |", escape_gfm_cell(&f.detail));
        if opts.verbose {
            out.push_str("\n### Failure Detail\n\n");
            out.push_str(&format_fenced_code_block("text", &f.detail));
            out.push('\n');
        }
    }
    if let Some(check) = artifact_check {
        let _ = writeln!(
            out,
            "| Artifacts Check | `{}` ({} files) |",
            if check.exact_match { "pass" } else { "fail" },
            check.checked_files
        );
    }
    if !env.invariant_violations.is_empty() {
        out.push_str("\n### Invariant Violations\n\n");
        for v in &env.invariant_violations {
            let _ = writeln!(out, "- {}", escape_gfm_cell(v));
        }
    }
    if !policy_violations.is_empty() {
        out.push_str("\n### Policy Violations\n\n");
        for p in policy_violations {
            let _ = writeln!(out, "- {}", escape_gfm_cell(p));
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;
    use crate::core::inspect::schema::{parse_and_validate_receipt, tests::sample_success_json};

    #[test]
    fn renders_sanitize_terminal_and_markdown_injection() {
        let mut evil = sample_success_json();
        let payload = "Evil\x1b[31m|`<tag>\r\n## Spoofed";
        evil["audit"]["theorem"] = json!(payload);
        evil["configuration"]["crate_name"] = json!(payload);
        evil["request_sha256"] = json!("0123456789\u{00E9}\x1b[31m\r\n");
        evil["horizon"] = json!({"kind": "\x1b[8m\ninvariant_violations=0"});
        evil["\x1b[31m\nbad_key"] = json!(1);
        let env = parse_and_validate_receipt(&serde_json::to_vec(&evil).unwrap()).unwrap();

        let human = render_inspection(&env, None, &[], &RenderOptions::default());
        assert!(!human.contains('\x1b'));
        assert!(!human.contains('\r'));
        assert!(human.lines().all(|line| !line.trim_start().starts_with("## Spoofed")));
        assert!(human.lines().all(|line| !line.starts_with("invariant_violations=0")));
        assert!(human.contains("\\r\\n## Spoofed"));
        assert!(human.contains("\\u{001B}[31m"));
        assert!(human.contains("horizon=unknown(\\u{001B}[8m\\ninvariant_violations=0)"));

        let md = render_inspection(
            &env,
            None,
            &[],
            &RenderOptions { format: InspectFormat::Markdown, ..RenderOptions::default() },
        );
        assert!(!md.contains('\x1b'));
        assert!(md.contains(&format_gfm_code_cell(payload)));
        assert!(md.lines().all(|line| !line.starts_with("invariant_violations=0")));

        let ledger = render_inspection(
            &env,
            None,
            &[],
            &RenderOptions { format: InspectFormat::Ledger, ..RenderOptions::default() },
        );
        assert!(!ledger.contains('\x1b'));
        assert!(ledger.contains("schema_version=3\n"));
        assert!(ledger.contains("audit.canonical_root=Trusted.MirSemantics.CrateTheorem\n"));
        assert!(ledger.contains("horizon=unknown(\\u{001B}[8m\\ninvariant_violations=0)\n"));
        assert!(ledger.lines().all(|line| !line.starts_with("invariant_violations=0")));
        assert!(ledger.contains("unrecognized_fields=/\\u{001B}[31m\\nbad_key"));
    }

    #[test]
    fn renders_sanitize_inapplicable_correspondence_reason() {
        let mut r = sample_success_json();
        let reason = "Evil\x1b[31m|`<tag>\r\n## Spoofed\ncorrespondence_provenance.applicable=true";
        r["correspondence_provenance"] = json!({ "applicable": false, "reason": reason });
        let env = parse_and_validate_receipt(&serde_json::to_vec(&r).unwrap()).unwrap();
        let render = |format| {
            render_inspection(
                &env,
                None,
                &[],
                &RenderOptions { format, ..RenderOptions::default() },
            )
        };
        let injected = |out: &str| {
            out.lines().any(|line| {
                let line = line.trim_start();
                line.starts_with("## Spoofed")
                    || line.starts_with("correspondence_provenance.applicable=true")
            })
        };

        let human = render(InspectFormat::Human);
        assert!(!human.contains('\x1b') && !human.contains('\r'), "{human}");
        assert!(!injected(&human), "{human}");
        assert!(human.contains(" [QUALIFIED]\n"), "{human}");
        assert!(human.contains("  correspondence: inapplicable (Evil\\u{001B}[31m"), "{human}");

        let md = render(InspectFormat::Markdown);
        assert!(!md.contains('\x1b') && !injected(&md), "{md}");
        assert!(
            md.contains(&format!(
                "| Correspondence Provenance | not applicable: {} |\n",
                format_gfm_code_cell(reason)
            )),
            "{md}"
        );

        let ledger = render(InspectFormat::Ledger);
        assert!(!ledger.contains('\x1b') && !injected(&ledger), "{ledger}");
        assert!(ledger.contains("correspondence_provenance.applicable=false\n"), "{ledger}");
        assert_eq!(
            ledger.lines().filter(|l| l.starts_with("correspondence_provenance.reason=")).count(),
            1,
            "{ledger}"
        );
    }

    fn s3_relation_test_receipt(scope_kind: &str) -> serde_json::Value {
        let mut r = sample_success_json();
        let cap_bin_sha = r["capture_binary_sha256"].as_str().unwrap().to_owned();
        r["assurance_stage"] = json!("stage1_audited");
        r["horizon"] = json!({"kind": "unbounded"});
        r["permitted_axioms"] = json!(["Classical.choice", "Quot.sound", "propext"]);
        r["tcb_shims"] = json!([{
            "id": "rustc_post_cleanup_capture",
            "kind": "capture_driver",
            "commit": "pinned",
            "sha256": cap_bin_sha,
            "status": "assumed",
            "guards": ["mir_preserve_ub"]
        }]);
        r["model_system_relation"] = json!({
            "kind": "simulation",
            "qualifier": "wf_stutter",
            "direction": "forward",
            "anchored_at": "post_cleanup_mir",
            "licensed_claim_shapes": ["forall_safety"],
            "unmodeled_downstream": ["llvm_codegen"]
        });
        r["correspondence_provenance"]["schema_version"] = json!(3);
        r["correspondence_provenance"]["claim_kind"] = json!("exact_refines");
        r["correspondence_provenance"]["permitted_axioms"] =
            json!(["Classical.choice", "Quot.sound", "propext"]);
        r["correspondence_provenance"]["model_system_relation"] = json!({
            "kind": "simulation",
            "qualifier": "wf_stutter",
            "direction": "bidirectional",
            "anchored_at": "lean_spec",
            "licensed_claim_shapes": ["forall_safety"],
            "unmodeled_downstream": ["rustc_mir_opt"]
        });
        r["correspondence_provenance"]["tcb_shims"] = json!([]);
        r["correspondence_provenance"]["taint_reasons"] = json!([]);
        r["correspondence_provenance"]["qualifiers"] = json!({
            "choice_total": true,
            "assumed_seams": [],
            "scope_kind": scope_kind
        });
        r
    }

    #[test]
    fn human_and_markdown_highlight_partial_gate_and_relation_details() {
        let r = s3_relation_test_receipt("partial_gate");
        let env = parse_and_validate_receipt(&serde_json::to_vec(&r).unwrap()).unwrap();
        let color_opts = RenderOptions { use_color: true, ..RenderOptions::default() };
        let human = render_inspection(&env, None, &[], &color_opts);
        assert!(human.contains("\x1b[33;1mcrate_verified\x1b[0m [QUALIFIED]"), "{human}");
        assert!(!human.contains("\x1b[32;1m"), "{human}");
        assert!(human.contains("qualified_assurance: provenance=qualified"), "{human}");
        assert!(human.contains("anchor=post_cleanup_mir"), "{human}");
        assert!(human.contains("unmodeled=[llvm_codegen]"), "{human}");
        assert!(human.contains("anchor=lean_spec"), "{human}");
        assert!(human.contains("unmodeled=[rustc_mir_opt]"), "{human}");
        assert!(human.contains("scope:partial_gate"), "{human}");

        let ledger = render_inspection(
            &env,
            None,
            &[],
            &RenderOptions { format: InspectFormat::Ledger, ..RenderOptions::default() },
        );
        assert!(
            ledger.contains("correspondence_provenance.model_system_relation=simulation (wf_stutter, bidirectional, anchor=lean_spec, claims=[forall_safety], unmodeled=[rustc_mir_opt])\n"),
            "{ledger}"
        );

        let md = render_inspection(
            &env,
            None,
            &[],
            &RenderOptions { format: InspectFormat::Markdown, ..RenderOptions::default() },
        );
        assert!(md.contains("QUALIFIED ASSURANCE"), "{md}");
        assert!(md.contains("`provenance=qualified`"), "{md}");
        assert!(!md.contains("`tcb_shims=non_empty`"), "{md}");
        assert!(md.contains("| Provenance Relation |"), "{md}");
        assert!(md.contains("anchor=lean_spec"), "{md}");
    }

    #[test]
    fn unbounded_full_gate_with_only_capture_driver_is_not_qualified() {
        let r = s3_relation_test_receipt("full_gate");
        let env = parse_and_validate_receipt(&serde_json::to_vec(&r).unwrap()).unwrap();
        let color_opts = RenderOptions { use_color: true, ..RenderOptions::default() };
        let human = render_inspection(&env, None, &[], &color_opts);
        assert!(human.contains("\x1b[32;1mcrate_verified\x1b[0m\n"), "{human}");
        assert!(!human.contains("[QUALIFIED]"), "{human}");
        assert!(!human.contains("qualified_assurance:"), "{human}");

        let md = render_inspection(
            &env,
            None,
            &[],
            &RenderOptions { format: InspectFormat::Markdown, ..RenderOptions::default() },
        );
        assert!(!md.contains("QUALIFIED ASSURANCE"), "{md}");
    }

    #[test]
    fn render_diff_surfaces_invariant_violations_across_all_formats() {
        let base_json = sample_success_json();
        let mut head_json = sample_success_json();
        head_json["audit"]["bindings"]["requestSha256"] = json!("b".repeat(64));
        let base = parse_and_validate_receipt(&serde_json::to_vec(&base_json).unwrap()).unwrap();
        let head = parse_and_validate_receipt(&serde_json::to_vec(&head_json).unwrap()).unwrap();
        let diff = crate::core::inspect::diff::diff_receipts(&base, &head, false);

        let human = render_diff(&diff, &RenderOptions::default());
        assert!(human.contains("INVALID ENVELOPE(S)"), "{human}");
        assert!(!human.contains("NO REGRESSIONS"), "{human}");
        assert!(human.contains("Head Invariant Violations:"), "{human}");
        assert!(human.contains("audit.bindings"), "{human}");

        let md = render_diff(
            &diff,
            &RenderOptions { format: InspectFormat::Markdown, ..RenderOptions::default() },
        );
        assert!(md.contains("INVALID ENVELOPE(S)"), "{md}");
        assert!(md.contains("### Invariant Violations"), "{md}");
        assert!(md.contains("audit.bindings"), "{md}");

        let ledger = render_diff(
            &diff,
            &RenderOptions { format: InspectFormat::Ledger, ..RenderOptions::default() },
        );
        assert!(ledger.contains("diff.head_invariant_violations=1\n"), "{ledger}");
        assert!(ledger.contains("diff.head_invariant_violation.0="), "{ledger}");

        let json_out = render_diff(
            &diff,
            &RenderOptions { format: InspectFormat::Json, ..RenderOptions::default() },
        );
        let parsed: serde_json::Value = serde_json::from_str(&json_out).unwrap();
        assert_eq!(parsed["head_invariant_violations"].as_array().unwrap().len(), 1);
        assert!(parsed.get("base_invariant_violations").is_none());
    }

    #[test]
    fn render_diff_surfaces_unrecognized_fields_across_all_formats() {
        let base_json = sample_success_json();
        let mut head_json = sample_success_json();
        head_json["future_extension"] = json!("alpha");
        let base = parse_and_validate_receipt(&serde_json::to_vec(&base_json).unwrap()).unwrap();
        let head = parse_and_validate_receipt(&serde_json::to_vec(&head_json).unwrap()).unwrap();
        let diff = crate::core::inspect::diff::diff_receipts(&base, &head, false);

        let human = render_diff(&diff, &RenderOptions::default());
        assert!(human.contains("[UNVERIFIED EXTENSIONS]"), "{human}");
        assert!(human.contains("Head Unrecognized Fields (1): /future_extension"), "{human}");
        assert!(!human.contains("  no changes"), "{human}");

        let md = render_diff(
            &diff,
            &RenderOptions { format: InspectFormat::Markdown, ..RenderOptions::default() },
        );
        assert!(md.contains("UNVERIFIED EXTENSIONS"), "{md}");
        assert!(md.contains("`/future_extension`"), "{md}");
        assert!(!md.contains("No differences recorded across verified fields."), "{md}");

        let ledger = render_diff(
            &diff,
            &RenderOptions { format: InspectFormat::Ledger, ..RenderOptions::default() },
        );
        assert!(ledger.contains("diff.head_unrecognized_fields=1\n"), "{ledger}");
        assert!(ledger.contains("diff.head_unrecognized_field.0=/future_extension\n"), "{ledger}");

        let json_out = render_diff(
            &diff,
            &RenderOptions { format: InspectFormat::Json, ..RenderOptions::default() },
        );
        let parsed: serde_json::Value = serde_json::from_str(&json_out).unwrap();
        assert_eq!(parsed["head_unrecognized_fields"], json!(["/future_extension"]));
        assert!(parsed.get("base_unrecognized_fields").is_none());
    }

    #[test]
    fn markdown_reports_model_digest_alongside_human_and_ledger() {
        let mut r = sample_success_json();
        let model = "c".repeat(64);
        r["model_manifest_sha256"] = json!(model);
        r["audit"]["bindings"]["modelManifestSha256"] = json!(model);
        let env = parse_and_validate_receipt(&serde_json::to_vec(&r).unwrap()).unwrap();
        assert!(env.invariant_violations.is_empty(), "{:?}", env.invariant_violations);

        let human = render_inspection(&env, None, &[], &RenderOptions::default());
        assert!(human.contains("model:         cccccccccccc"), "{human}");
        let ledger = render_inspection(
            &env,
            None,
            &[],
            &RenderOptions { format: InspectFormat::Ledger, ..RenderOptions::default() },
        );
        assert!(ledger.contains(&format!("digest.model_manifest_sha256={model}\n")), "{ledger}");
        let md = render_inspection(
            &env,
            None,
            &[],
            &RenderOptions { format: InspectFormat::Markdown, ..RenderOptions::default() },
        );
        assert!(md.contains("| Model Digest | `cccccccccccc` |\n"), "{md}");
        let full_md = render_inspection(
            &env,
            None,
            &[],
            &RenderOptions {
                format: InspectFormat::Markdown,
                full_digests: true,
                ..RenderOptions::default()
            },
        );
        assert!(full_md.contains(&format!("| Model Digest | `{model}` |\n")), "{full_md}");
    }

    #[test]
    fn renders_sharded_receipt_digests_and_summary_across_all_formats() {
        use crate::core::inspect::schema::tests::sample_sharded_success_json;

        let sharded = sample_sharded_success_json();
        let env = parse_and_validate_receipt(&serde_json::to_vec(&sharded).unwrap()).unwrap();
        assert!(env.unrecognized_fields.is_empty(), "{:?}", env.unrecognized_fields);
        assert!(env.invariant_violations.is_empty(), "{:?}", env.invariant_violations);

        let human = render_inspection(&env, None, &[], &RenderOptions::default());
        assert!(human.contains("capture_shards: 111111111111"), "{human}");
        assert!(human.contains("2 shard(s), 2 body(s), 2 SCC(s) (0 cyclic)"), "{human}");

        let ledger = render_inspection(
            &env,
            None,
            &[],
            &RenderOptions { format: InspectFormat::Ledger, ..RenderOptions::default() },
        );
        assert!(ledger.contains(&format!("digest.capture_shards_sha256={}\n", "1".repeat(64))));
        assert!(ledger.contains("counts.shards=2\n"), "{ledger}");
        assert!(ledger.contains(&format!("shards.id_tree_sha256={}\n", "2".repeat(64))));

        let md = render_inspection(
            &env,
            None,
            &[],
            &RenderOptions { format: InspectFormat::Markdown, ..RenderOptions::default() },
        );
        assert!(md.contains("| Capture Shards | `2` shard(s), `2` SCC(s) (`0` cyclic) |"), "{md}");

        let json_out = render_inspection(
            &env,
            None,
            &[],
            &RenderOptions { format: InspectFormat::Json, ..RenderOptions::default() },
        );
        let parsed: serde_json::Value = serde_json::from_str(&json_out).unwrap();
        assert_eq!(parsed["receipt"]["capture_shards_sha256"], json!("1".repeat(64)));
        assert_eq!(parsed["receipt"]["shards"]["total_shards"], json!(2));
    }
}
