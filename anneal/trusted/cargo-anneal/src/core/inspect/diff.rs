// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Pure 3-tier receipt comparison (`--diff <BASE> <HEAD>`).

use std::collections::{BTreeMap, BTreeSet};

use serde::Serialize;

use crate::core::inspect::schema::{
    ParsedReceipt, ReceiptEnvelope, ScopeInstantiation, SpecWarningEntry,
};

/// Classifies the severity of a difference between `base` and `head` receipts.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum DiffTier {
    /// Assurance regression (taint added, scope narrowed, containment dropped,
    /// new axioms, verification failure, or spec change under
    /// `--require-unchanged-specs`).
    TierA,
    /// Trusted model, specification, compiler, or verified item identity
    /// change without necessarily reducing assurance tier.
    TierB,
    /// Informational metadata delta (timings, declaration counts, artifacts).
    TierC,
}

/// One typed difference item between `base` and `head`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct DiffChange {
    /// Assurance severity tier of this difference.
    pub tier: DiffTier,
    /// Dot-separated receipt field path (`scope.kind`, `audit.axioms`, etc.).
    pub field: String,
    /// Recorded value in the baseline receipt.
    pub base: String,
    /// Recorded value in the head receipt.
    pub head: String,
    /// Human-readable classification explanation.
    pub note: String,
}

/// Complete 3-tier receipt diff summary.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ReceiptDiff {
    /// SHA-256 hex digest of the base receipt input.
    pub base_receipt_sha256: String,
    /// SHA-256 hex digest of the head receipt input.
    pub head_receipt_sha256: String,
    /// `true` when at least one `TierA` assurance regression was detected.
    pub has_regressions: bool,
    /// Invariant violations recorded on the baseline receipt, if any.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub base_invariant_violations: Vec<String>,
    /// Invariant violations recorded on the head receipt, if any.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub head_invariant_violations: Vec<String>,
    /// Unrecognized Receipt v3 field pointers recorded on the baseline receipt.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub base_unrecognized_fields: Vec<String>,
    /// Unrecognized Receipt v3 field pointers recorded on the head receipt.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub head_unrecognized_fields: Vec<String>,
    /// Ordered list of field-level differences across Tiers A, B, and C.
    pub changes: Vec<DiffChange>,
}

/// Compute a structured 3-tier diff between `base` and `head` receipts.
pub fn diff_receipts(
    base: &ReceiptEnvelope,
    head: &ReceiptEnvelope,
    require_unchanged_specs: bool,
) -> ReceiptDiff {
    let mut changes = Vec::new();
    let push = |changes: &mut Vec<DiffChange>,
                tier: DiffTier,
                field: &str,
                b: String,
                h: String,
                note: &str| {
        changes.push(DiffChange {
            tier,
            field: field.to_owned(),
            base: b,
            head: h,
            note: note.to_owned(),
        });
    };

    if base.receipt.status() != head.receipt.status() {
        let tier = if base.receipt.is_success() && !head.receipt.is_success() {
            DiffTier::TierA
        } else {
            DiffTier::TierB
        };
        push(
            &mut changes,
            tier,
            "status",
            base.receipt.status().to_owned(),
            head.receipt.status().to_owned(),
            "verification outcome status changed",
        );
    }

    let base_taints: BTreeSet<&str> =
        base.receipt.taint_reasons().iter().map(String::as_str).collect();
    let head_taints: BTreeSet<&str> =
        head.receipt.taint_reasons().iter().map(String::as_str).collect();
    if base_taints != head_taints {
        let added_taint = head_taints.difference(&base_taints).next().is_some();
        push(
            &mut changes,
            if added_taint { DiffTier::TierA } else { DiffTier::TierB },
            "taint_reasons",
            base.receipt.taint_reasons().join(","),
            head.receipt.taint_reasons().join(","),
            if added_taint { "new taint introduced in head" } else { "taint removed in head" },
        );
    }

    if let (ParsedReceipt::Success(b), ParsedReceipt::Success(h)) = (&base.receipt, &head.receipt) {
        if b.scope_kind != h.scope_kind {
            let narrowed = b.scope_kind == "crate" && h.scope_kind == "selected_unit";
            push(
                &mut changes,
                if narrowed { DiffTier::TierA } else { DiffTier::TierB },
                "scope.kind",
                b.scope_kind.clone(),
                h.scope_kind.clone(),
                if narrowed {
                    "verification scope narrowed from crate to selected_unit"
                } else {
                    "verification scope changed"
                },
            );
        } else if b.scope_kind == "selected_unit" {
            let b_roots: BTreeSet<&str> = b.scope_roots.iter().map(String::as_str).collect();
            let h_roots: BTreeSet<&str> = h.scope_roots.iter().map(String::as_str).collect();
            if b_roots != h_roots {
                let dropped_root = b_roots.difference(&h_roots).next().is_some();
                push(
                    &mut changes,
                    if dropped_root { DiffTier::TierA } else { DiffTier::TierB },
                    "scope.roots",
                    b.scope_roots.join(","),
                    h.scope_roots.join(","),
                    if dropped_root {
                        "selected_unit roots removed or narrowed in head"
                    } else {
                        "selected_unit roots expanded in head"
                    },
                );
            }
            let b_insts: BTreeSet<&ScopeInstantiation> = b.scope_instantiations.iter().collect();
            let h_insts: BTreeSet<&ScopeInstantiation> = h.scope_instantiations.iter().collect();
            if b_insts != h_insts {
                let dropped_inst = b_insts.difference(&h_insts).next().is_some();
                let fmt_insts = |insts: &[ScopeInstantiation]| -> String {
                    insts
                        .iter()
                        .map(|inst| {
                            if inst.args.is_empty() {
                                inst.path.clone()
                            } else {
                                format!("{}<{}>", inst.path, inst.args.join(","))
                            }
                        })
                        .collect::<Vec<_>>()
                        .join(",")
                };
                push(
                    &mut changes,
                    if dropped_inst { DiffTier::TierA } else { DiffTier::TierB },
                    "scope.instantiations",
                    fmt_insts(&b.scope_instantiations),
                    fmt_insts(&h.scope_instantiations),
                    if dropped_inst {
                        "selected_unit instantiations removed or changed in head"
                    } else {
                        "selected_unit instantiations expanded in head"
                    },
                );
            }
        }

        if b.experimental != h.experimental {
            let newly_experimental = !b.experimental && h.experimental;
            push(
                &mut changes,
                if newly_experimental { DiffTier::TierA } else { DiffTier::TierB },
                "experimental",
                b.experimental.to_string(),
                h.experimental.to_string(),
                if newly_experimental {
                    "head uses experimental verification mode"
                } else {
                    "head stabilized out of experimental mode"
                },
            );
        }

        if b.candidate_features != h.candidate_features {
            let regressed = match (&b.candidate_features, &h.candidate_features) {
                (Some(_), None) => true,
                (None, Some(hc)) => !hc.is_empty(),
                (Some(bc), Some(hc)) => {
                    let b_set: BTreeSet<&str> = bc.iter().map(String::as_str).collect();
                    hc.iter().any(|f| !b_set.contains(f.as_str()))
                }
                (None, None) => false,
            };
            let fmt_cf = |cf: Option<&[String]>| match cf {
                None => "<none>".to_owned(),
                Some([]) => "[]".to_owned(),
                Some(list) => list.join(","),
            };
            push(
                &mut changes,
                if regressed { DiffTier::TierA } else { DiffTier::TierB },
                "candidate_features",
                fmt_cf(b.candidate_features.as_deref()),
                fmt_cf(h.candidate_features.as_deref()),
                if regressed {
                    "new candidate feature(s) entered trusted closure or metadata dropped in head"
                } else {
                    "candidate feature(s) retired or metadata added"
                },
            );
        }

        if b.elaboration_sandbox != h.elaboration_sandbox {
            let weakened = h.elaboration_sandbox == "none" && b.elaboration_sandbox != "none";
            push(
                &mut changes,
                if weakened { DiffTier::TierA } else { DiffTier::TierB },
                "elaboration_sandbox",
                b.elaboration_sandbox.clone(),
                h.elaboration_sandbox.clone(),
                if weakened {
                    "OS elaboration containment disabled"
                } else {
                    "elaboration sandbox backend changed"
                },
            );
        }

        diff_stage_and_horizon(
            &mut changes,
            b.assurance_stage.as_deref(),
            h.assurance_stage.as_deref(),
            b.horizon.as_ref(),
            h.horizon.as_ref(),
        );

        if b.permitted_axioms != h.permitted_axioms {
            let expanded = match (&b.permitted_axioms, &h.permitted_axioms) {
                (Some(ba), Some(ha)) => ha.iter().any(|a| !ba.contains(a)),
                (None, Some(ha)) => ha.iter().any(|a| !is_standard_axiom(a)),
                (Some(_), None) => true,
                (None, None) => false,
            };
            push(
                &mut changes,
                if expanded { DiffTier::TierA } else { DiffTier::TierB },
                "permitted_axioms",
                b.permitted_axioms.as_ref().map_or("<none>".to_owned(), |v| v.join(",")),
                h.permitted_axioms.as_ref().map_or("<none>".to_owned(), |v| v.join(",")),
                if expanded {
                    "permitted axiom allowlist expanded or dropped in head"
                } else {
                    "permitted axiom allowlist changed"
                },
            );
        }

        diff_tcb_shims_opt(
            &mut changes,
            "tcb_shims",
            b.tcb_shims.as_deref(),
            h.tcb_shims.as_deref(),
        );

        if b.model_system_relation != h.model_system_relation {
            let weakened = is_relation_regression(
                b.model_system_relation.as_ref(),
                h.model_system_relation.as_ref(),
            );
            push(
                &mut changes,
                if weakened { DiffTier::TierA } else { DiffTier::TierB },
                "model_system_relation",
                format_relation(b.model_system_relation.as_ref()),
                format_relation(h.model_system_relation.as_ref()),
                if weakened {
                    "model-system relation weakened or claims narrowed in head"
                } else {
                    "model-system relation metadata changed"
                },
            );
        }

        let b_assump: BTreeSet<&str> = b.assumptions.iter().map(String::as_str).collect();
        let h_assump: BTreeSet<&str> = h.assumptions.iter().map(String::as_str).collect();
        if b_assump != h_assump {
            let added = h_assump.difference(&b_assump).next().is_some();
            push(
                &mut changes,
                if added { DiffTier::TierA } else { DiffTier::TierB },
                "assumptions",
                b.assumptions.join("; "),
                h.assumptions.join("; "),
                if added { "new trust assumption added in head" } else { "assumption retired" },
            );
        }

        let b_def: BTreeSet<&str> = b.deferred.iter().map(String::as_str).collect();
        let h_def: BTreeSet<&str> = h.deferred.iter().map(String::as_str).collect();
        if b_def != h_def {
            let added = h_def.difference(&b_def).next().is_some();
            push(
                &mut changes,
                if added { DiffTier::TierA } else { DiffTier::TierB },
                "deferred",
                b.deferred.join("; "),
                h.deferred.join("; "),
                if added {
                    "new deferred trust obligation added in head"
                } else {
                    "deferred trust obligation retired"
                },
            );
        }

        let b_ax: BTreeSet<&str> = b.axioms.iter().map(String::as_str).collect();
        let h_ax: BTreeSet<&str> = h.axioms.iter().map(String::as_str).collect();
        if b_ax != h_ax {
            let added_ax = h_ax.difference(&b_ax).next().is_some();
            push(
                &mut changes,
                if added_ax { DiffTier::TierA } else { DiffTier::TierB },
                "audit.axioms",
                b.axioms.join(","),
                h.axioms.join(","),
                if added_ax {
                    "head relies on additional logical axiom(s)"
                } else {
                    "head dropped axiom usage"
                },
            );
        }

        let b_sorry: BTreeSet<&str> = b.sorry_declarations.iter().map(String::as_str).collect();
        let h_sorry: BTreeSet<&str> = h.sorry_declarations.iter().map(String::as_str).collect();
        if b_sorry != h_sorry || b.sorry_declarations.len() != h.sorry_declarations.len() {
            let added_sorry = h_sorry.difference(&b_sorry).next().is_some()
                || h.sorry_declarations.len() > b.sorry_declarations.len();
            push(
                &mut changes,
                if added_sorry { DiffTier::TierA } else { DiffTier::TierB },
                "audit.sorryDeclarations",
                b.sorry_declarations.join(","),
                h.sorry_declarations.join(","),
                if added_sorry {
                    "head introduced or increased sorry-using proof declaration(s)"
                } else {
                    "head retired sorry-using proof declaration(s)"
                },
            );
        }

        let b_kernels: BTreeSet<&str> =
            b.kernels_passed.iter().map(|k| k.trim()).filter(|k| !k.is_empty()).collect();
        let h_kernels: BTreeSet<&str> =
            h.kernels_passed.iter().map(|k| k.trim()).filter(|k| !k.is_empty()).collect();
        let b_eff = if b.is_multi_kernel() {
            b_kernels.len()
        } else if b.replay {
            1
        } else {
            0
        };
        let h_eff = if h.is_multi_kernel() {
            h_kernels.len()
        } else if h.replay {
            1
        } else {
            0
        };
        if b_kernels != h_kernels || b_eff != h_eff {
            let fmt_k = |s: &crate::core::inspect::schema::SuccessReceipt, ks: &BTreeSet<&str>| {
                if !s.is_multi_kernel() && s.replay {
                    "<single-kernel>".to_owned()
                } else {
                    ks.iter().copied().collect::<Vec<_>>().join(",")
                }
            };
            let dropped = h_eff < b_eff || b_kernels.difference(&h_kernels).next().is_some();
            push(
                &mut changes,
                if dropped { DiffTier::TierA } else { DiffTier::TierB },
                "audit.kernelsPassed",
                fmt_k(b, &b_kernels),
                fmt_k(h, &h_kernels),
                if dropped {
                    "replay kernel quorum reduced or dropped passing kernel(s)"
                } else {
                    "multi-kernel replay quorum expanded"
                },
            );
        }

        let b_skipped: BTreeSet<&str> =
            b.kernels_skipped.iter().map(|k| k.trim()).filter(|k| !k.is_empty()).collect();
        let h_skipped: BTreeSet<&str> =
            h.kernels_skipped.iter().map(|k| k.trim()).filter(|k| !k.is_empty()).collect();
        if b_skipped != h_skipped {
            let added = h_skipped.difference(&b_skipped).next().is_some();
            push(
                &mut changes,
                if added { DiffTier::TierA } else { DiffTier::TierB },
                "audit.kernelsSkipped",
                b_skipped.iter().copied().collect::<Vec<_>>().join(","),
                h_skipped.iter().copied().collect::<Vec<_>>().join(","),
                if added {
                    "multi-kernel replay skipped additional kernel(s)"
                } else {
                    "fewer replay kernels skipped"
                },
            );
        }

        if b.paranoid_quorum != h.paranoid_quorum {
            let regressed = b.paranoid_quorum == Some(true) && h.paranoid_quorum != Some(true);
            push(
                &mut changes,
                if regressed { DiffTier::TierA } else { DiffTier::TierB },
                "audit.paranoidQuorum",
                b.paranoid_quorum.map_or("<none>".to_owned(), |v| v.to_string()),
                h.paranoid_quorum.map_or("<none>".to_owned(), |v| v.to_string()),
                if regressed {
                    "paranoid multi-kernel quorum disabled or removed"
                } else {
                    "paranoid multi-kernel quorum metadata changed"
                },
            );
        }

        if b.audit_mode != h.audit_mode {
            let mode_rank = |m: Option<&str>| match m {
                Some("paranoid") => 2u8,
                Some("strict") => 1,
                _ => 0,
            };
            let regressed = mode_rank(h.audit_mode.as_deref()) < mode_rank(b.audit_mode.as_deref());
            push(
                &mut changes,
                if regressed { DiffTier::TierA } else { DiffTier::TierB },
                "audit.auditMode",
                b.audit_mode.as_deref().unwrap_or("<none>").to_owned(),
                h.audit_mode.as_deref().unwrap_or("<none>").to_owned(),
                if regressed {
                    "multi-kernel auditMode downgraded or removed"
                } else {
                    "multi-kernel auditMode changed"
                },
            );
        }

        if b.checked_alternate_proofs != h.checked_alternate_proofs {
            push(
                &mut changes,
                DiffTier::TierC,
                "audit.checkedAlternateProofs",
                b.checked_alternate_proofs.to_string(),
                h.checked_alternate_proofs.to_string(),
                "checked alternate proof count changed",
            );
        }

        if b.specification_manifest_sha256 != h.specification_manifest_sha256 {
            push(
                &mut changes,
                if require_unchanged_specs { DiffTier::TierA } else { DiffTier::TierB },
                "specification_manifest_sha256",
                b.specification_manifest_sha256.clone(),
                h.specification_manifest_sha256.clone(),
                if require_unchanged_specs {
                    "specification digest changed under --require-unchanged-specs"
                } else {
                    "specification digest changed"
                },
            );
        }

        let b_locked: BTreeSet<&str> = b.sha256_locked.iter().map(String::as_str).collect();
        let h_locked: BTreeSet<&str> = h.sha256_locked.iter().map(String::as_str).collect();
        if b_locked != h_locked {
            let dropped = b_locked.difference(&h_locked).next().is_some();
            push(
                &mut changes,
                if dropped { DiffTier::TierA } else { DiffTier::TierB },
                "toolchain_identity.sha256_locked",
                b.sha256_locked.join("; "),
                h.sha256_locked.join("; "),
                if dropped {
                    "SHA-256 locked toolchain component removed in head"
                } else {
                    "SHA-256 locked toolchain component list changed"
                },
            );
        }

        let b_recorded: BTreeSet<&str> = b.sha256_recorded.iter().map(String::as_str).collect();
        let h_recorded: BTreeSet<&str> = h.sha256_recorded.iter().map(String::as_str).collect();
        if b_recorded != h_recorded {
            push(
                &mut changes,
                DiffTier::TierB,
                "toolchain_identity.sha256_recorded",
                b.sha256_recorded.join("; "),
                h.sha256_recorded.join("; "),
                "SHA-256 recorded toolchain component list changed",
            );
        }

        let b_unhashed: BTreeSet<&str> = b.unhashed.iter().map(String::as_str).collect();
        let h_unhashed: BTreeSet<&str> = h.unhashed.iter().map(String::as_str).collect();
        if b_unhashed != h_unhashed {
            let added = h_unhashed.difference(&b_unhashed).next().is_some();
            push(
                &mut changes,
                if added { DiffTier::TierA } else { DiffTier::TierB },
                "toolchain_identity.unhashed",
                b.unhashed.join("; "),
                h.unhashed.join("; "),
                if added {
                    "new unhashed toolchain component introduced in head"
                } else {
                    "unhashed toolchain component retired"
                },
            );
        }

        match (&b.unpinned_lean, &h.unpinned_lean) {
            (Some(bu), Some(hu)) => {
                if bu.expected_toolchain != hu.expected_toolchain {
                    push(
                        &mut changes,
                        DiffTier::TierB,
                        "unpinned_lean.expected_toolchain",
                        bu.expected_toolchain.clone(),
                        hu.expected_toolchain.clone(),
                        "unpinned Lean expected toolchain changed",
                    );
                }
                if bu.observed_version != hu.observed_version {
                    push(
                        &mut changes,
                        DiffTier::TierB,
                        "unpinned_lean.observed_version",
                        bu.observed_version.clone(),
                        hu.observed_version.clone(),
                        "unpinned Lean observed compiler version changed",
                    );
                }
                if bu.lean_binary_sha256 != hu.lean_binary_sha256 {
                    push(
                        &mut changes,
                        DiffTier::TierB,
                        "unpinned_lean.lean_binary_sha256",
                        bu.lean_binary_sha256.clone(),
                        hu.lean_binary_sha256.clone(),
                        "unpinned Lean binary digest changed",
                    );
                }
                if bu.sysroot_modules_sha256 != hu.sysroot_modules_sha256 {
                    push(
                        &mut changes,
                        DiffTier::TierB,
                        "unpinned_lean.sysroot_modules_sha256",
                        bu.sysroot_modules_sha256.clone(),
                        hu.sysroot_modules_sha256.clone(),
                        "unpinned Lean sysroot modules digest changed",
                    );
                }
                if bu.foundation_modules != hu.foundation_modules {
                    push(
                        &mut changes,
                        DiffTier::TierB,
                        "unpinned_lean.foundation_modules",
                        bu.foundation_modules.join(","),
                        hu.foundation_modules.join(","),
                        "unpinned Lean foundation module closure changed",
                    );
                }
                if bu.admitted_sysroot_module_count != hu.admitted_sysroot_module_count {
                    push(
                        &mut changes,
                        DiffTier::TierC,
                        "unpinned_lean.admitted_sysroot_module_count",
                        bu.admitted_sysroot_module_count.to_string(),
                        hu.admitted_sysroot_module_count.to_string(),
                        "unpinned Lean admitted sysroot module count changed",
                    );
                }
            }
            (None, Some(hu)) => {
                push(
                    &mut changes,
                    DiffTier::TierB,
                    "unpinned_lean",
                    "<none>".to_owned(),
                    hu.lean_binary_sha256.clone(),
                    "head uses unpinned Lean toolchain",
                );
            }
            (Some(bu), None) => {
                push(
                    &mut changes,
                    DiffTier::TierB,
                    "unpinned_lean",
                    bu.lean_binary_sha256.clone(),
                    "<none>".to_owned(),
                    "head switched away from unpinned Lean toolchain",
                );
            }
            (None, None) => {}
        }

        for (field, bv, hv, note) in [
            (
                "request_sha256",
                &b.request_sha256,
                &h.request_sha256,
                "request configuration digest changed",
            ),
            ("capture_sha256", &b.capture_sha256, &h.capture_sha256, "captured MIR digest changed"),
            (
                "capture_binary_sha256",
                &b.capture_binary_sha256,
                &h.capture_binary_sha256,
                "capture driver binary digest changed",
            ),
            (
                "model_manifest_sha256",
                &b.model_manifest_sha256,
                &h.model_manifest_sha256,
                "Anneal trusted/theory bundle digest changed",
            ),
            ("audit.canonicalRoot", &b.canonical_root, &h.canonical_root, "root theorem changed"),
            ("audit.theorem", &b.theorem, &h.theorem, "proof theorem symbol changed"),
        ] {
            if bv != hv {
                push(&mut changes, DiffTier::TierB, field, bv.clone(), hv.clone(), note);
            }
        }
        if b.specification != h.specification {
            push(
                &mut changes,
                if require_unchanged_specs { DiffTier::TierA } else { DiffTier::TierB },
                "audit.specification",
                b.specification.clone(),
                h.specification.clone(),
                if require_unchanged_specs {
                    "specification symbol changed under --require-unchanged-specs"
                } else {
                    "specification symbol changed"
                },
            );
        }
        let b_spec_closure: BTreeSet<(&str, &str)> =
            b.specification_closure.iter().map(|n| (n.module.as_str(), n.name.as_str())).collect();
        let h_spec_closure: BTreeSet<(&str, &str)> =
            h.specification_closure.iter().map(|n| (n.module.as_str(), n.name.as_str())).collect();
        if b_spec_closure != h_spec_closure {
            let fmt_sc = |set: &BTreeSet<(&str, &str)>| {
                set.iter().map(|(m, n)| format!("{m}:{n}")).collect::<Vec<_>>().join(",")
            };
            push(
                &mut changes,
                if require_unchanged_specs { DiffTier::TierA } else { DiffTier::TierB },
                "audit.specificationClosure",
                fmt_sc(&b_spec_closure),
                fmt_sc(&h_spec_closure),
                if require_unchanged_specs {
                    "specification closure changed under --require-unchanged-specs"
                } else {
                    "specification closure changed"
                },
            );
        }

        if b.upstream_pin_sha256 != h.upstream_pin_sha256 {
            push(
                &mut changes,
                DiffTier::TierB,
                "correspondence_provenance.upstream_pin_sha256",
                b.upstream_pin_sha256.as_deref().unwrap_or("<none>").to_owned(),
                h.upstream_pin_sha256.as_deref().unwrap_or("<none>").to_owned(),
                "correspondence upstream pin changed",
            );
        }
        if b.sysroot_foundation_manifest_sha256 != h.sysroot_foundation_manifest_sha256 {
            push(
                &mut changes,
                DiffTier::TierB,
                "correspondence_provenance.sysroot_foundation_manifest_sha256",
                b.sysroot_foundation_manifest_sha256.as_deref().unwrap_or("<none>").to_owned(),
                h.sysroot_foundation_manifest_sha256.as_deref().unwrap_or("<none>").to_owned(),
                "correspondence sysroot foundation manifest digest changed",
            );
        }
        if b.upstream_repository != h.upstream_repository {
            push(
                &mut changes,
                DiffTier::TierB,
                "correspondence_provenance.upstream_repository",
                b.upstream_repository.as_deref().unwrap_or("<none>").to_owned(),
                h.upstream_repository.as_deref().unwrap_or("<none>").to_owned(),
                "correspondence upstream repository changed",
            );
        }
        if b.upstream_commit != h.upstream_commit {
            push(
                &mut changes,
                DiffTier::TierB,
                "correspondence_provenance.upstream_commit",
                b.upstream_commit.as_deref().unwrap_or("<none>").to_owned(),
                h.upstream_commit.as_deref().unwrap_or("<none>").to_owned(),
                "correspondence upstream commit changed",
            );
        }
        if b.upstream_lean_toolchain != h.upstream_lean_toolchain {
            push(
                &mut changes,
                DiffTier::TierB,
                "correspondence_provenance.upstream_lean_toolchain",
                b.upstream_lean_toolchain.as_deref().unwrap_or("<none>").to_owned(),
                h.upstream_lean_toolchain.as_deref().unwrap_or("<none>").to_owned(),
                "correspondence upstream Lean toolchain changed",
            );
        }
        if b.build_lean_toolchain != h.build_lean_toolchain {
            push(
                &mut changes,
                DiffTier::TierB,
                "correspondence_provenance.build_lean_toolchain",
                b.build_lean_toolchain.as_deref().unwrap_or("<none>").to_owned(),
                h.build_lean_toolchain.as_deref().unwrap_or("<none>").to_owned(),
                "correspondence build Lean toolchain changed",
            );
        }
        if b.correspondence_schema_version != h.correspondence_schema_version {
            push(
                &mut changes,
                DiffTier::TierB,
                "correspondence_provenance.schema_version",
                b.correspondence_schema_version.map_or("<none>".to_owned(), |v| v.to_string()),
                h.correspondence_schema_version.map_or("<none>".to_owned(), |v| v.to_string()),
                "correspondence provenance schema_version changed (v1->v3 upgrade may surface new v3 metadata)",
            );
        }
        if b.correspondence_permitted_axioms != h.correspondence_permitted_axioms {
            let expanded =
                match (&b.correspondence_permitted_axioms, &h.correspondence_permitted_axioms) {
                    (Some(ba), Some(ha)) => ha.iter().any(|a| !ba.contains(a)),
                    (None, Some(ha)) => ha.iter().any(|a| !is_standard_axiom(a)),
                    (Some(_), None) => true,
                    (None, None) => false,
                };
            push(
                &mut changes,
                if expanded { DiffTier::TierA } else { DiffTier::TierB },
                "correspondence_provenance.permitted_axioms",
                b.correspondence_permitted_axioms
                    .as_ref()
                    .map_or("<none>".to_owned(), |v| v.join(",")),
                h.correspondence_permitted_axioms
                    .as_ref()
                    .map_or("<none>".to_owned(), |v| v.join(",")),
                if expanded {
                    "correspondence permitted axiom allowlist expanded or dropped in head"
                } else {
                    "correspondence permitted axiom allowlist changed"
                },
            );
        }
        if b.correspondence_claim_kind != h.correspondence_claim_kind {
            let weakened = match (
                b.correspondence_claim_kind.as_deref(),
                h.correspondence_claim_kind.as_deref(),
            ) {
                (Some(bc), Some(hc)) => claim_kind_rank(hc) < claim_kind_rank(bc),
                (None, Some(hc)) => claim_kind_rank(hc) < claim_kind_rank("exact_refines"),
                (Some(_), None) => true,
                (None, None) => false,
            };
            push(
                &mut changes,
                if weakened { DiffTier::TierA } else { DiffTier::TierB },
                "correspondence_provenance.claim_kind",
                b.correspondence_claim_kind.as_deref().unwrap_or("<none>").to_owned(),
                h.correspondence_claim_kind.as_deref().unwrap_or("<none>").to_owned(),
                if weakened {
                    "correspondence claim_kind weakened or removed in head"
                } else {
                    "correspondence claim_kind changed"
                },
            );
        }
        diff_tcb_shims_opt(
            &mut changes,
            "correspondence_provenance.tcb_shims",
            b.correspondence_tcb_shims.as_deref(),
            h.correspondence_tcb_shims.as_deref(),
        );
        let b_prov_taints: BTreeSet<&str> =
            b.correspondence_taint_reasons.iter().map(String::as_str).collect();
        let h_prov_taints: BTreeSet<&str> =
            h.correspondence_taint_reasons.iter().map(String::as_str).collect();
        if b_prov_taints != h_prov_taints {
            let added = h_prov_taints.difference(&b_prov_taints).next().is_some();
            push(
                &mut changes,
                if added { DiffTier::TierA } else { DiffTier::TierB },
                "correspondence_provenance.taint_reasons",
                b.correspondence_taint_reasons.join(","),
                h.correspondence_taint_reasons.join(","),
                if added {
                    "new correspondence provenance taint added in head"
                } else {
                    "correspondence provenance taint retired"
                },
            );
        }
        if b.correspondence_model_system_relation != h.correspondence_model_system_relation {
            let weakened = is_relation_regression(
                b.correspondence_model_system_relation.as_ref(),
                h.correspondence_model_system_relation.as_ref(),
            );
            push(
                &mut changes,
                if weakened { DiffTier::TierA } else { DiffTier::TierB },
                "correspondence_provenance.model_system_relation",
                format_relation(b.correspondence_model_system_relation.as_ref()),
                format_relation(h.correspondence_model_system_relation.as_ref()),
                if weakened {
                    "correspondence model-system relation weakened in head"
                } else {
                    "correspondence model-system relation changed"
                },
            );
        }
        if b.correspondence_qualifiers != h.correspondence_qualifiers {
            let weakened = match (&b.correspondence_qualifiers, &h.correspondence_qualifiers) {
                (Some(_), None) => true,
                (None, Some(hq)) => {
                    hq.scope_kind != "full_gate" || !hq.choice_total || !hq.assumed_seams.is_empty()
                }
                (Some(bq), Some(hq)) => {
                    (bq.choice_total && !hq.choice_total)
                        || (bq.scope_kind == "full_gate" && hq.scope_kind != "full_gate")
                        || hq.assumed_seams.iter().any(|s| !bq.assumed_seams.contains(s))
                }
                (None, None) => false,
            };
            push(
                &mut changes,
                if weakened { DiffTier::TierA } else { DiffTier::TierB },
                "correspondence_provenance.qualifiers",
                format!("{:?}", b.correspondence_qualifiers),
                format!("{:?}", h.correspondence_qualifiers),
                if weakened {
                    "correspondence qualifiers weakened or removed in head"
                } else {
                    "correspondence qualifiers changed"
                },
            );
        }
        if b.correspondence_provenance_residual_sha256
            != h.correspondence_provenance_residual_sha256
        {
            push(
                &mut changes,
                DiffTier::TierB,
                "correspondence_provenance",
                b.correspondence_provenance_residual_sha256.clone(),
                h.correspondence_provenance_residual_sha256.clone(),
                "correspondence provenance metadata changed",
            );
        }

        if b.selected.len() != h.selected.len() {
            push(
                &mut changes,
                DiffTier::TierC,
                "selected.count",
                b.selected.len().to_string(),
                h.selected.len().to_string(),
                "selected body count changed",
            );
        }
        if b.census.len() != h.census.len() {
            push(
                &mut changes,
                DiffTier::TierC,
                "census.count",
                b.census.len().to_string(),
                h.census.len().to_string(),
                "compiler census count changed",
            );
        }
        if b.sources != h.sources {
            push(
                &mut changes,
                DiffTier::TierB,
                "sources",
                format!("{} file(s)", b.sources.len()),
                format!("{} file(s)", h.sources.len()),
                "verified Rust source digests changed",
            );
        }
        if b.stdlib_crate != h.stdlib_crate {
            push(
                &mut changes,
                DiffTier::TierB,
                "configuration.stdlib_crate",
                b.stdlib_crate.as_deref().unwrap_or("<none>").to_owned(),
                h.stdlib_crate.as_deref().unwrap_or("<none>").to_owned(),
                "target stdlib crate configuration changed",
            );
        }
        if b.replayed_declarations != h.replayed_declarations {
            push(
                &mut changes,
                DiffTier::TierC,
                "audit.replayedDeclarations",
                b.replayed_declarations.to_string(),
                h.replayed_declarations.to_string(),
                "replayed declaration count changed",
            );
        }
        if b.timing_ms != h.timing_ms {
            push(
                &mut changes,
                DiffTier::TierC,
                "timing_ms.total",
                b.timing_ms.total.to_string(),
                h.timing_ms.total.to_string(),
                "total verification elapsed time changed",
            );
        }
        let b_warn_counts = count_warnings(&b.spec_warnings);
        let h_warn_counts = count_warnings(&h.spec_warnings);
        if b_warn_counts != h_warn_counts {
            let added_or_increased = h_warn_counts
                .iter()
                .any(|(w, &hc)| hc > b_warn_counts.get(w).copied().unwrap_or(0));
            let fmt_warnings = |ws: &[SpecWarningEntry]| -> String {
                if ws.is_empty() {
                    return "<none>".to_owned();
                }
                ws.iter()
                    .map(|w| format!("{}:{}", w.code, w.declaration))
                    .collect::<Vec<_>>()
                    .join(",")
            };
            push(
                &mut changes,
                if added_or_increased { DiffTier::TierA } else { DiffTier::TierB },
                "spec_warnings",
                fmt_warnings(&b.spec_warnings),
                fmt_warnings(&h.spec_warnings),
                if added_or_increased {
                    "head introduced or increased anti-vacuity warning(s)"
                } else {
                    "head retired anti-vacuity warning(s)"
                },
            );
        }
    } else if let (ParsedReceipt::Failure(b), ParsedReceipt::Failure(h)) =
        (&base.receipt, &head.receipt)
    {
        diff_stage_and_horizon(
            &mut changes,
            b.assurance_stage.as_deref(),
            h.assurance_stage.as_deref(),
            b.horizon.as_ref(),
            h.horizon.as_ref(),
        );
    }

    if base.receipt.artifacts() != head.receipt.artifacts() {
        push(
            &mut changes,
            DiffTier::TierC,
            "artifacts",
            base.receipt.artifacts().unwrap_or("<none>").to_owned(),
            head.receipt.artifacts().unwrap_or("<none>").to_owned(),
            "retained artifacts path changed",
        );
    }

    let has_regressions = changes.iter().any(|c| c.tier == DiffTier::TierA);
    ReceiptDiff {
        base_receipt_sha256: base.receipt_sha256.clone(),
        head_receipt_sha256: head.receipt_sha256.clone(),
        has_regressions,
        base_invariant_violations: base.invariant_violations.clone(),
        head_invariant_violations: head.invariant_violations.clone(),
        base_unrecognized_fields: base.unrecognized_fields.clone(),
        head_unrecognized_fields: head.unrecognized_fields.clone(),
        changes,
    }
}

fn stage_rank(stage: &str) -> u8 {
    match stage {
        "stage0_alpha" => 0,
        "stage1_audited" => 1,
        "stage2_hardened" => 2,
        _ => 0,
    }
}

fn format_horizon(h: Option<&crate::core::inspect::schema::HorizonRecord>) -> String {
    match h {
        None => "<none>".to_owned(),
        Some(crate::core::inspect::schema::HorizonRecord::Unbounded) => "unbounded".to_owned(),
        Some(crate::core::inspect::schema::HorizonRecord::Bounded { k }) => format!("bounded({k})"),
        Some(crate::core::inspect::schema::HorizonRecord::Unknown { raw_kind }) => {
            format!("unknown({raw_kind})")
        }
    }
}

fn is_standard_axiom(axiom: &str) -> bool {
    matches!(axiom, "Classical.choice" | "Quot.sound" | "propext")
}

fn claim_kind_rank(ck: &str) -> u8 {
    match ck {
        "pure_spec_agreement" => 0,
        "sound_refines" => 1,
        "exact_refines" => 2,
        _ => 0,
    }
}

fn relation_kind_rank(kind: &str) -> u8 {
    match kind {
        "none" => 0,
        "embedding" => 1,
        "abstraction" => 2,
        "homomorphism" => 3,
        "simulation" => 4,
        _ => 0,
    }
}

fn qualifier_rank(qual: Option<&str>) -> u8 {
    match qual {
        None => 0,
        Some("stutter") => 1,
        Some("wf_stutter") => 2,
        Some("lock_step") => 3,
        _ => 0,
    }
}

fn count_warnings(ws: &[SpecWarningEntry]) -> BTreeMap<&SpecWarningEntry, usize> {
    let mut counts = BTreeMap::new();
    for w in ws {
        *counts.entry(w).or_insert(0) += 1;
    }
    counts
}

fn is_direction_regression(base: &str, head: &str) -> bool {
    base != head && head != "bidirectional"
}

fn format_relation(r: Option<&crate::core::inspect::schema::ModelSystemRelation>) -> String {
    match r {
        None => "<none>".to_owned(),
        Some(rel) => format!(
            "{}({}, {}, anchor={}, claims=[{}], unmodeled=[{}])",
            rel.kind,
            rel.qualifier.as_deref().unwrap_or("-"),
            rel.direction,
            rel.anchored_at.as_deref().unwrap_or("-"),
            rel.licensed_claim_shapes.join(","),
            rel.unmodeled_downstream.join(","),
        ),
    }
}

fn diff_stage_and_horizon(
    changes: &mut Vec<DiffChange>,
    base_stage: Option<&str>,
    head_stage: Option<&str>,
    base_horizon: Option<&crate::core::inspect::schema::HorizonRecord>,
    head_horizon: Option<&crate::core::inspect::schema::HorizonRecord>,
) {
    if base_stage != head_stage {
        let regressed = (base_stage.is_some() && head_stage.is_none())
            || matches!((base_stage, head_stage), (Some(b), Some(h)) if stage_rank(h) < stage_rank(b));
        changes.push(DiffChange {
            tier: if regressed { DiffTier::TierA } else { DiffTier::TierB },
            field: "assurance_stage".to_owned(),
            base: base_stage.unwrap_or("<none>").to_owned(),
            head: head_stage.unwrap_or("<none>").to_owned(),
            note: if regressed {
                "assurance stage downgraded or removed in head".to_owned()
            } else {
                "assurance stage changed".to_owned()
            },
        });
    }
    if base_horizon != head_horizon {
        use crate::core::inspect::schema::HorizonRecord;
        // Pre-S-3 receipts omit `horizon` and represent unbounded verification;
        // moving from absent or explicit unbounded to bounded narrows
        // guarantees.
        let narrowed = (base_horizon.is_some() && head_horizon.is_none())
            || matches!(
                (base_horizon, head_horizon),
                (None | Some(HorizonRecord::Unbounded), Some(HorizonRecord::Bounded { .. }))
                    | (_, Some(HorizonRecord::Unknown { .. }))
            )
            || matches!(
                (base_horizon, head_horizon),
                (Some(HorizonRecord::Bounded { k: bk }), Some(HorizonRecord::Bounded { k: hk }))
                    if hk < bk
            );
        changes.push(DiffChange {
            tier: if narrowed { DiffTier::TierA } else { DiffTier::TierB },
            field: "horizon".to_owned(),
            base: format_horizon(base_horizon),
            head: format_horizon(head_horizon),
            note: if narrowed {
                "verification horizon narrowed or removed in head".to_owned()
            } else {
                "verification horizon changed".to_owned()
            },
        });
    }
}

fn shim_status_rank(status: &str) -> Option<u8> {
    match status {
        "assumed" => Some(0),
        "tested" => Some(1),
        "proved" => Some(2),
        _ => None,
    }
}

type CanonicalTcbShim<'a> = (&'a str, Option<&'a str>, Option<&'a str>, &'a str, BTreeSet<&'a str>);

fn canonical_tcb_shims<'a>(
    shims: Option<&'a [crate::core::inspect::schema::TcbShimEntry]>,
) -> Option<BTreeMap<&'a str, CanonicalTcbShim<'a>>> {
    shims.map(|list| {
        let mut map = BTreeMap::new();
        for s in list {
            let guards: BTreeSet<&str> = s.guards.iter().map(String::as_str).collect();
            map.insert(
                s.id.as_str(),
                (
                    s.kind.as_str(),
                    s.commit.as_deref(),
                    s.sha256.as_deref(),
                    s.status.as_str(),
                    guards,
                ),
            );
        }
        map
    })
}

fn diff_tcb_shims_opt(
    changes: &mut Vec<DiffChange>,
    field: &str,
    base: Option<&[crate::core::inspect::schema::TcbShimEntry]>,
    head: Option<&[crate::core::inspect::schema::TcbShimEntry]>,
) {
    let fmt = |shims: Option<&[crate::core::inspect::schema::TcbShimEntry]>| -> String {
        match shims {
            None => "<none>".to_owned(),
            Some([]) => "[]".to_owned(),
            Some(list) => {
                let mut items: Vec<String> =
                    list.iter().map(|s| format!("{}({}:{})", s.id, s.kind, s.status)).collect();
                items.sort();
                items.join(",")
            }
        }
    };
    let b_map = canonical_tcb_shims(base);
    let h_map = canonical_tcb_shims(head);
    if b_map == h_map {
        return;
    }
    let regressed = match (&b_map, &h_map) {
        (Some(_), None) => true,
        (None, Some(h)) => !h.is_empty(),
        (Some(b), Some(h)) => h.iter().any(|(id, h_entry)| match b.get(id) {
            None => true,
            Some(b_entry) => {
                let status_regressed =
                    match (shim_status_rank(b_entry.3), shim_status_rank(h_entry.3)) {
                        (Some(b_rank), Some(h_rank)) => h_rank < b_rank,
                        _ => h_entry.3 != b_entry.3,
                    };
                let metadata_changed = b_entry.0 != h_entry.0
                    || b_entry.1 != h_entry.1
                    || b_entry.2 != h_entry.2
                    || b_entry.4 != h_entry.4;
                status_regressed || metadata_changed
            }
        }),
        (None, None) => false,
    };
    changes.push(DiffChange {
        tier: if regressed { DiffTier::TierA } else { DiffTier::TierB },
        field: field.to_owned(),
        base: fmt(base),
        head: fmt(head),
        note: if regressed {
            "new, altered, or unrecorded TCB shim metadata in head".to_owned()
        } else {
            "TCB shim retired or strengthened in head".to_owned()
        },
    });
}

fn is_relation_regression(
    base: Option<&crate::core::inspect::schema::ModelSystemRelation>,
    head: Option<&crate::core::inspect::schema::ModelSystemRelation>,
) -> bool {
    let (Some(b), Some(h)) = (base, head) else {
        return match (base, head) {
            (Some(_), None) => true,
            (None, Some(h)) => h.kind == "none",
            _ => false,
        };
    };
    if relation_kind_rank(&h.kind) < relation_kind_rank(&b.kind) {
        return true;
    }
    if qualifier_rank(h.qualifier.as_deref()) < qualifier_rank(b.qualifier.as_deref()) {
        return true;
    }
    if is_direction_regression(&b.direction, &h.direction) {
        return true;
    }
    if b.anchored_at.is_some() && b.anchored_at != h.anchored_at {
        return true;
    }
    if b.licensed_claim_shapes.iter().any(|c| !h.licensed_claim_shapes.contains(c)) {
        return true;
    }
    h.unmodeled_downstream.iter().any(|u| !b.unmodeled_downstream.contains(u))
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;
    use crate::core::inspect::schema::{parse_and_validate_receipt, tests::sample_success_json};

    #[test]
    fn classifies_tier_a_regressions_and_tier_b_spec_edits() {
        let base_json = sample_success_json();
        let base = parse_and_validate_receipt(&serde_json::to_vec(&base_json).unwrap()).unwrap();

        let mut head_json = base_json.clone();
        head_json["status"] = json!("tainted_selected_unit_verified");
        head_json["taint_reasons"] = json!(["unsandboxed_elaboration"]);
        head_json["elaboration_sandbox"] = json!("none");
        head_json["deferred"] = json!(["hostile Lean elaborator effects"]);
        head_json["assumptions"] = json!(["faithful pinned compiler capture", "extra"]);
        head_json["scope"] = json!({"kind": "selected_unit", "roots": ["zero"]});
        head_json["audit"]["canonicalRoot"] = json!("Trusted.MirSemantics.UnitTheorem");
        head_json["specification_manifest_sha256"] = json!("b".repeat(64));
        head_json["audit"]["bindings"]["specificationManifestSha256"] = json!("b".repeat(64));
        let head = parse_and_validate_receipt(&serde_json::to_vec(&head_json).unwrap()).unwrap();

        let diff = diff_receipts(&base, &head, true);
        assert!(diff.has_regressions);
        assert!(
            diff.changes.iter().any(|c| c.field == "taint_reasons" && c.tier == DiffTier::TierA)
        );
        assert!(diff.changes.iter().any(|c| c.field == "scope.kind" && c.tier == DiffTier::TierA));
        assert!(diff.changes.iter().any(|c| c.field == "assumptions" && c.tier == DiffTier::TierA));
        assert!(diff.changes.iter().any(|c| c.field == "deferred" && c.tier == DiffTier::TierA));
        assert!(
            diff.changes
                .iter()
                .any(|c| c.field == "specification_manifest_sha256" && c.tier == DiffTier::TierA)
        );

        let diff_allow_spec = diff_receipts(&base, &head, false);
        assert!(
            diff_allow_spec
                .changes
                .iter()
                .any(|c| c.field == "specification_manifest_sha256" && c.tier == DiffTier::TierB)
        );

        // Removing taint (`tainted_crate_verified` -> `crate_verified`) must
        // not be flagged as a Tier A regression.
        let mut tainted_base_json = base_json.clone();
        tainted_base_json["status"] = json!("tainted_crate_verified");
        tainted_base_json["taint_reasons"] = json!(["unsandboxed_elaboration"]);
        tainted_base_json["elaboration_sandbox"] = json!("none");
        tainted_base_json["deferred"] =
            json!(["complete review-surface reporting", "hostile Lean elaborator effects"]);
        let tainted_base =
            parse_and_validate_receipt(&serde_json::to_vec(&tainted_base_json).unwrap()).unwrap();
        let improvement = diff_receipts(&tainted_base, &base, true);
        assert!(
            !improvement.has_regressions,
            "improvement unexpectedly flagged regression: {:?}",
            improvement.changes
        );

        // Trust-root identity changes (`toolchain_identity`, `unpinned_lean`,
        // `correspondence_provenance`) must be surfaced cleanly.
        let mut unverified_libs = base_json.clone();
        unverified_libs["toolchain_identity"]["sha256_locked"] = json!([]);
        unverified_libs["toolchain_identity"]["unhashed"] =
            json!(["Rust compiler and sysroot", "Lean shared libraries"]);
        // Keep pinned validation satisfied while testing dropped lock entries:
        unverified_libs["toolchain_identity"]["sha256_locked"] =
            json!(["foundation-lock.json modules"]);
        let mut verified_libs = base_json.clone();
        verified_libs["toolchain_identity"]["sha256_locked"] =
            json!(["foundation-lock.json modules", "Lean runtime shared libraries"]);
        verified_libs["toolchain_identity"]["unhashed"] = json!(["Rust compiler and sysroot"]);
        let b_libs =
            parse_and_validate_receipt(&serde_json::to_vec(&verified_libs).unwrap()).unwrap();
        let h_libs =
            parse_and_validate_receipt(&serde_json::to_vec(&unverified_libs).unwrap()).unwrap();
        let libs_diff = diff_receipts(&b_libs, &h_libs, true);
        assert!(libs_diff.has_regressions, "{:?}", libs_diff.changes);
        assert!(libs_diff.changes.iter().any(|c| {
            c.field == "toolchain_identity.sha256_locked" && c.tier == DiffTier::TierA
        }));
        assert!(
            libs_diff
                .changes
                .iter()
                .any(|c| { c.field == "toolchain_identity.unhashed" && c.tier == DiffTier::TierA })
        );

        let mut prov_changed = base_json.clone();
        prov_changed["correspondence_provenance"]["upstream_commit"] = json!("deadbeef");
        prov_changed["correspondence_provenance"]["sysroot_foundation_manifest_sha256"] =
            json!("d".repeat(64));
        let h_prov =
            parse_and_validate_receipt(&serde_json::to_vec(&prov_changed).unwrap()).unwrap();
        let prov_diff = diff_receipts(&base, &h_prov, true);
        assert!(!prov_diff.has_regressions);
        assert!(prov_diff.changes.iter().any(|c| {
            c.field == "correspondence_provenance.upstream_commit" && c.tier == DiffTier::TierB
        }));
        assert!(prov_diff.changes.iter().any(|c| {
            c.field == "correspondence_provenance.sysroot_foundation_manifest_sha256"
                && c.tier == DiffTier::TierB
        }));

        let mut unpinned_a = base_json.clone();
        let h_a = "1".repeat(64);
        let h_b = "2".repeat(64);
        let unpinned_obj = |bin_sha: &str, sys_sha: &str, ver: &str| {
            json!({
                "expected_toolchain": "leanprover/lean4:v4.34.1",
                "observed_version": ver,
                "lean_binary_sha256": bin_sha,
                "foundation_modules": ["Init.Prelude"],
                "sysroot_modules_sha256": sys_sha,
                "admitted_sysroot_module_count": 1
            })
        };
        let unpinned_audit = |bin_sha: &str, sys_sha: &str, ver: &str| {
            json!({
                "expectedToolchain": "leanprover/lean4:v4.34.1",
                "observedVersion": ver,
                "leanBinarySha256": bin_sha,
                "foundationModules": ["Init.Prelude"],
                "sysrootModulesSha256": sys_sha,
                "admittedSysrootModuleCount": 1
            })
        };
        unpinned_a["status"] = json!("tainted_crate_verified");
        unpinned_a["taint_reasons"] = json!(["unpinned_lean"]);
        unpinned_a["toolchain_identity"]["sha256_locked"] = json!([]);
        unpinned_a["correspondence_provenance"] =
            json!({"applicable": false, "reason": "unpinned"});
        unpinned_a["unpinned_lean"] = unpinned_obj(&h_a, &h_a, "4.34.1");
        unpinned_a["audit"]["unpinnedLean"] = unpinned_audit(&h_a, &h_a, "4.34.1");
        let mut unpinned_b = unpinned_a.clone();
        unpinned_b["unpinned_lean"] = unpinned_obj(&h_b, &h_b, "4.35.0");
        unpinned_b["audit"]["unpinnedLean"] = unpinned_audit(&h_b, &h_b, "4.35.0");
        let ua = parse_and_validate_receipt(&serde_json::to_vec(&unpinned_a).unwrap()).unwrap();
        let ub = parse_and_validate_receipt(&serde_json::to_vec(&unpinned_b).unwrap()).unwrap();
        let u_diff = diff_receipts(&ua, &ub, true);
        assert!(u_diff.changes.iter().any(|c| {
            c.field == "unpinned_lean.lean_binary_sha256" && c.tier == DiffTier::TierB
        }));
        assert!(u_diff.changes.iter().any(|c| {
            c.field == "unpinned_lean.sysroot_modules_sha256" && c.tier == DiffTier::TierB
        }));
        assert!(
            u_diff.changes.iter().any(|c| {
                c.field == "unpinned_lean.observed_version" && c.tier == DiffTier::TierB
            })
        );

        let mut s3_base = base_json.clone();
        s3_base["assurance_stage"] = json!("stage1_audited");
        s3_base["horizon"] = json!({"kind": "unbounded"});
        s3_base["permitted_axioms"] = json!(["Classical.choice", "Quot.sound", "propext"]);
        s3_base["tcb_shims"] = json!([{
            "id": "rustc_post_cleanup_capture",
            "kind": "capture_driver",
            "commit": "abc123",
            "status": "assumed"
        }]);
        s3_base["model_system_relation"] = json!({
            "kind": "simulation",
            "qualifier": "wf_stutter",
            "direction": "forward",
            "licensed_claim_shapes": ["forall_safety"]
        });
        s3_base["correspondence_provenance"]["schema_version"] = json!(3);
        s3_base["correspondence_provenance"]["claim_kind"] = json!("exact_refines");
        s3_base["correspondence_provenance"]["permitted_axioms"] =
            json!(["Classical.choice", "Quot.sound", "propext"]);
        s3_base["correspondence_provenance"]["model_system_relation"] = json!({
            "kind": "simulation",
            "qualifier": "wf_stutter",
            "direction": "bidirectional",
            "licensed_claim_shapes": ["forall_safety"]
        });
        s3_base["correspondence_provenance"]["patched_files"] = json!([]);
        s3_base["correspondence_provenance"]["tcb_shims"] = json!([]);
        s3_base["correspondence_provenance"]["taint_reasons"] = json!([]);
        s3_base["correspondence_provenance"]["qualifiers"] = json!({
            "choice_total": true,
            "assumed_seams": [],
            "scope_kind": "full_gate"
        });
        let mut s3_head = s3_base.clone();
        s3_head["tcb_shims"] = json!([
            {
                "id": "rustc_post_cleanup_capture",
                "kind": "capture_driver",
                "commit": "abc123",
                "status": "assumed"
            },
            {
                "id": "extra_seam",
                "kind": "assumed_seam",
                "sha256": "b".repeat(64),
                "status": "assumed"
            }
        ]);
        s3_head["horizon"] = json!({"kind": "bounded", "k": 16});
        // Widening `correspondence_provenance.permitted_axioms` alongside
        // another provenance subfield change must still surface as TierA.
        s3_base["correspondence_provenance"]["permitted_axioms"] = json!(["propext"]);
        s3_head["correspondence_provenance"]["claim_kind"] = json!("sound_refines");
        s3_head["correspondence_provenance"]["model_system_relation"]["direction"] =
            json!("forward");
        s3_head["correspondence_provenance"]["permitted_axioms"] =
            json!(["Classical.choice", "Quot.sound", "propext"]);
        let sb = parse_and_validate_receipt(&serde_json::to_vec(&s3_base).unwrap()).unwrap();
        let sh = parse_and_validate_receipt(&serde_json::to_vec(&s3_head).unwrap()).unwrap();
        let s3_diff = diff_receipts(&sb, &sh, true);
        assert!(s3_diff.has_regressions, "{:?}", s3_diff.changes);
        assert!(
            s3_diff.changes.iter().any(|c| c.field == "tcb_shims" && c.tier == DiffTier::TierA)
        );
        assert!(s3_diff.changes.iter().any(|c| c.field == "horizon" && c.tier == DiffTier::TierA));
        assert!(s3_diff.changes.iter().any(|c| {
            c.field == "correspondence_provenance.permitted_axioms" && c.tier == DiffTier::TierA
        }));
        assert!(s3_diff.changes.iter().any(|c| {
            c.field == "correspondence_provenance.claim_kind" && c.tier == DiffTier::TierA
        }));

        // A pre-S-3 receipt (missing horizon) followed by a bounded head must
        // surface as a TierA regression under `--no-regressions`.
        let pre_s3 =
            parse_and_validate_receipt(&serde_json::to_vec(&sample_success_json()).unwrap())
                .unwrap();
        let mut bounded_only = sample_success_json();
        bounded_only["horizon"] = json!({"kind": "bounded", "k": 8});
        let bounded_head =
            parse_and_validate_receipt(&serde_json::to_vec(&bounded_only).unwrap()).unwrap();
        let bounded_diff = diff_receipts(&pre_s3, &bounded_head, true);
        assert!(bounded_diff.has_regressions, "{:?}", bounded_diff.changes);
        assert!(
            bounded_diff.changes.iter().any(|c| c.field == "horizon" && c.tier == DiffTier::TierA),
            "{:?}",
            bounded_diff.changes
        );
    }

    #[test]
    fn detects_instantiation_swap_sorry_growth_direction_flip_and_spec_warnings() {
        let mut base_inst = sample_success_json();
        base_inst["status"] = json!("selected_unit_verified");
        base_inst["scope"] = json!({
            "kind": "selected_unit",
            "roots": ["foo"],
            "instantiations": [{"path": "foo", "args": ["u8"]}]
        });
        base_inst["audit"]["canonicalRoot"] = json!("Trusted.MirSemantics.UnitTheorem");
        let mut head_inst = base_inst.clone();
        head_inst["scope"]["instantiations"] = json!([{"path": "foo", "args": ["u16"]}]);
        let bi = parse_and_validate_receipt(&serde_json::to_vec(&base_inst).unwrap()).unwrap();
        let hi = parse_and_validate_receipt(&serde_json::to_vec(&head_inst).unwrap()).unwrap();
        assert!(bi.invariant_violations.is_empty(), "{:?}", bi.invariant_violations);
        assert!(hi.invariant_violations.is_empty(), "{:?}", hi.invariant_violations);
        let inst_diff = diff_receipts(&bi, &hi, false);
        assert!(inst_diff.has_regressions, "{:?}", inst_diff.changes);
        assert!(
            inst_diff
                .changes
                .iter()
                .any(|c| { c.field == "scope.instantiations" && c.tier == DiffTier::TierA })
        );

        let mut base_sorry = sample_success_json();
        base_sorry["status"] = json!("tainted_crate_verified");
        base_sorry["taint_reasons"] = json!(["sorry_in_proof"]);
        base_sorry["sorry_declarations"] = json!(["Proof.a"]);
        base_sorry["audit"]["axioms"] = json!(["propext", "sorryAx"]);
        base_sorry["audit"]["sorryDeclarations"] = json!(["Proof.a"]);
        let mut head_sorry = base_sorry.clone();
        head_sorry["sorry_declarations"] = json!(["Proof.a", "Proof.b"]);
        head_sorry["audit"]["sorryDeclarations"] = json!(["Proof.a", "Proof.b"]);
        let bs = parse_and_validate_receipt(&serde_json::to_vec(&base_sorry).unwrap()).unwrap();
        let hs = parse_and_validate_receipt(&serde_json::to_vec(&head_sorry).unwrap()).unwrap();
        let sorry_diff = diff_receipts(&bs, &hs, false);
        assert!(sorry_diff.has_regressions, "{:?}", sorry_diff.changes);
        assert!(
            sorry_diff
                .changes
                .iter()
                .any(|c| { c.field == "audit.sorryDeclarations" && c.tier == DiffTier::TierA })
        );
        let sorry_improved = diff_receipts(&hs, &bs, false);
        assert!(!sorry_improved.has_regressions, "{:?}", sorry_improved.changes);
        assert!(
            sorry_improved
                .changes
                .iter()
                .any(|c| { c.field == "audit.sorryDeclarations" && c.tier == DiffTier::TierB })
        );

        let mut rel_fwd = sample_success_json();
        rel_fwd["model_system_relation"] = json!({
            "kind": "simulation",
            "qualifier": "wf_stutter",
            "direction": "forward",
            "licensed_claim_shapes": ["forall_safety"]
        });
        let mut rel_bwd = rel_fwd.clone();
        rel_bwd["model_system_relation"]["direction"] = json!("backward");
        let rf = parse_and_validate_receipt(&serde_json::to_vec(&rel_fwd).unwrap()).unwrap();
        let rb = parse_and_validate_receipt(&serde_json::to_vec(&rel_bwd).unwrap()).unwrap();
        let dir_diff = diff_receipts(&rf, &rb, false);
        assert!(dir_diff.has_regressions, "{:?}", dir_diff.changes);
        assert!(
            dir_diff
                .changes
                .iter()
                .any(|c| { c.field == "model_system_relation" && c.tier == DiffTier::TierA })
        );

        let h_sha = "a".repeat(64);
        let mut shim_assumed = sample_success_json();
        shim_assumed["tcb_shims"] = json!([{
            "id": "seam_x",
            "kind": "capture_driver",
            "sha256": h_sha,
            "status": "assumed"
        }]);
        let mut shim_proved = shim_assumed.clone();
        shim_proved["tcb_shims"][0]["status"] = json!("proved");
        let sa = parse_and_validate_receipt(&serde_json::to_vec(&shim_assumed).unwrap()).unwrap();
        let sp = parse_and_validate_receipt(&serde_json::to_vec(&shim_proved).unwrap()).unwrap();
        let shim_upgrade = diff_receipts(&sa, &sp, false);
        assert!(!shim_upgrade.has_regressions, "{:?}", shim_upgrade.changes);
        assert!(
            shim_upgrade
                .changes
                .iter()
                .any(|c| { c.field == "tcb_shims" && c.tier == DiffTier::TierB })
        );
        let shim_downgrade = diff_receipts(&sp, &sa, false);
        assert!(shim_downgrade.has_regressions, "{:?}", shim_downgrade.changes);

        let base_w =
            parse_and_validate_receipt(&serde_json::to_vec(&sample_success_json()).unwrap())
                .unwrap();
        let mut head_w_json = sample_success_json();
        let warn_item = json!([{
            "code": "unsatisfiable_safety",
            "declaration": "Spec.foo",
            "message": "ensures is vacuously false"
        }]);
        head_w_json["spec_warnings"] = warn_item.clone();
        head_w_json["audit"]["specWarnings"] = warn_item;
        let head_w =
            parse_and_validate_receipt(&serde_json::to_vec(&head_w_json).unwrap()).unwrap();
        assert!(head_w.invariant_violations.is_empty(), "{:?}", head_w.invariant_violations);
        let warn_diff = diff_receipts(&base_w, &head_w, false);
        assert!(warn_diff.has_regressions, "{:?}", warn_diff.changes);
        assert!(
            warn_diff
                .changes
                .iter()
                .any(|c| { c.field == "spec_warnings" && c.tier == DiffTier::TierA })
        );

        let mut ext_head_json = sample_success_json();
        ext_head_json["future_extension"] = json!("alpha");
        let ext_head =
            parse_and_validate_receipt(&serde_json::to_vec(&ext_head_json).unwrap()).unwrap();
        let ext_diff = diff_receipts(&base_w, &ext_head, false);
        assert!(ext_diff.base_unrecognized_fields.is_empty());
        assert_eq!(ext_diff.head_unrecognized_fields, vec!["/future_extension"]);

        // Increasing `audit.checkedAlternateProofs` is informational (Tier C).
        let mut alt_head_json = sample_success_json();
        alt_head_json["audit"]["checkedAlternateProofs"] = json!(2);
        let alt_head =
            parse_and_validate_receipt(&serde_json::to_vec(&alt_head_json).unwrap()).unwrap();
        assert!(alt_head.invariant_violations.is_empty(), "{:?}", alt_head.invariant_violations);
        let alt_diff = diff_receipts(&base_w, &alt_head, false);
        assert!(!alt_diff.has_regressions, "{:?}", alt_diff.changes);
        assert!(
            alt_diff
                .changes
                .iter()
                .any(|c| c.field == "audit.checkedAlternateProofs" && c.tier == DiffTier::TierC)
        );

        // Multi-kernel replay downgrades (1-kernel -> 0-kernel, paranoidQuorum
        // true -> false, added kernelsSkipped, auditMode downgrade) are Tier A.
        let mut zero_k_json = sample_success_json();
        zero_k_json["audit"]["auditMode"] = json!("strict");
        zero_k_json["audit"]["kernelsPassed"] = json!([]);
        zero_k_json["audit"]["kernelsSkipped"] = json!(["lean4"]);
        zero_k_json["audit"]["paranoidQuorum"] = json!(false);
        let zero_k =
            parse_and_validate_receipt(&serde_json::to_vec(&zero_k_json).unwrap()).unwrap();
        let zero_k_diff = diff_receipts(&base_w, &zero_k, false);
        assert!(zero_k_diff.has_regressions, "{:?}", zero_k_diff.changes);
        assert!(
            zero_k_diff
                .changes
                .iter()
                .any(|c| c.field == "audit.kernelsPassed" && c.tier == DiffTier::TierA)
        );
        assert!(
            zero_k_diff
                .changes
                .iter()
                .any(|c| c.field == "audit.kernelsSkipped" && c.tier == DiffTier::TierA)
        );

        let mut pq_base_json = sample_success_json();
        pq_base_json["audit"]["auditMode"] = json!("paranoid");
        pq_base_json["audit"]["kernelsPassed"] = json!(["nanoda", "con-ron"]);
        pq_base_json["audit"]["kernelsSkipped"] = json!([]);
        pq_base_json["audit"]["paranoidQuorum"] = json!(true);
        let mut pq_head_json = pq_base_json.clone();
        pq_head_json["audit"]["auditMode"] = json!("strict");
        pq_head_json["audit"]["kernelsSkipped"] = json!(["lean4lean"]);
        pq_head_json["audit"]["paranoidQuorum"] = json!(false);
        let pq_base =
            parse_and_validate_receipt(&serde_json::to_vec(&pq_base_json).unwrap()).unwrap();
        let pq_head =
            parse_and_validate_receipt(&serde_json::to_vec(&pq_head_json).unwrap()).unwrap();
        let pq_diff = diff_receipts(&pq_base, &pq_head, false);
        assert!(pq_diff.has_regressions, "{:?}", pq_diff.changes);
        for f in ["audit.kernelsSkipped", "audit.paranoidQuorum", "audit.auditMode"] {
            assert!(
                pq_diff.changes.iter().any(|c| c.field == f && c.tier == DiffTier::TierA),
                "missing Tier A for {f}: {:?}",
                pq_diff.changes
            );
        }

        // `--require-unchanged-specs` gates `audit.specification` symbol swaps
        // even when `specification_manifest_sha256` is unchanged.
        let mut swap_spec_json = sample_success_json();
        swap_spec_json["audit"]["specification"] = json!("Spec.weak");
        let swap_spec =
            parse_and_validate_receipt(&serde_json::to_vec(&swap_spec_json).unwrap()).unwrap();
        let swap_tier_b = diff_receipts(&base_w, &swap_spec, false);
        assert!(!swap_tier_b.has_regressions);
        let swap_tier_a = diff_receipts(&base_w, &swap_spec, true);
        assert!(swap_tier_a.has_regressions, "{:?}", swap_tier_a.changes);
        assert!(
            swap_tier_a
                .changes
                .iter()
                .any(|c| c.field == "audit.specification" && c.tier == DiffTier::TierA)
        );

        // Permuting unordered `tcb_shims` and `guards` produces zero changes.
        let mut shims_a_json = sample_success_json();
        let sha_a = "1".repeat(64);
        let sha_b = "2".repeat(64);
        shims_a_json["tcb_shims"] = json!([
            {
                "id": "shim_a",
                "kind": "assumed_seam",
                "sha256": sha_a,
                "status": "assumed",
                "guards": ["g1", "g2"]
            },
            {
                "id": "shim_b",
                "kind": "assumed_seam",
                "sha256": sha_b,
                "status": "assumed",
                "guards": ["g3"]
            }
        ]);
        let mut shims_b_json = shims_a_json.clone();
        shims_b_json["tcb_shims"] = json!([
            {
                "id": "shim_b",
                "kind": "assumed_seam",
                "sha256": sha_b,
                "status": "assumed",
                "guards": ["g3"]
            },
            {
                "id": "shim_a",
                "kind": "assumed_seam",
                "sha256": sha_a,
                "status": "assumed",
                "guards": ["g2", "g1"]
            }
        ]);
        let shims_a =
            parse_and_validate_receipt(&serde_json::to_vec(&shims_a_json).unwrap()).unwrap();
        let shims_b =
            parse_and_validate_receipt(&serde_json::to_vec(&shims_b_json).unwrap()).unwrap();
        let shims_diff = diff_receipts(&shims_a, &shims_b, false);
        assert!(shims_diff.changes.is_empty(), "{:?}", shims_diff.changes);

        // Removing or shifting `anchored_at` is a Tier A regression and
        // `format_relation` renders `anchor=` and `unmodeled=`.
        let mut rel_a_json = sample_success_json();
        rel_a_json["model_system_relation"] = json!({
            "kind": "simulation",
            "qualifier": "wf_stutter",
            "direction": "bidirectional",
            "anchored_at": "source_hir",
            "licensed_claim_shapes": ["forall_safety"],
            "unmodeled_downstream": ["llvm"]
        });
        let mut rel_b_json = rel_a_json.clone();
        rel_b_json["model_system_relation"].as_object_mut().unwrap().remove("anchored_at");
        let rel_a = parse_and_validate_receipt(&serde_json::to_vec(&rel_a_json).unwrap()).unwrap();
        let rel_b = parse_and_validate_receipt(&serde_json::to_vec(&rel_b_json).unwrap()).unwrap();
        let rel_diff = diff_receipts(&rel_a, &rel_b, false);
        assert!(rel_diff.has_regressions, "{:?}", rel_diff.changes);
        let rel_change = rel_diff
            .changes
            .iter()
            .find(|c| c.field == "model_system_relation")
            .expect("model_system_relation diff");
        assert_eq!(rel_change.tier, DiffTier::TierA);
        assert!(rel_change.base.contains("anchor=source_hir"), "{}", rel_change.base);
        assert!(rel_change.base.contains("unmodeled=[llvm]"), "{}", rel_change.base);
        assert!(rel_change.head.contains("anchor=-"), "{}", rel_change.head);

        // Residual provenance mutations (`trusted_lean`, `note`, etc.) must be
        // surfaced even when `tcb_shims` order or `upstream_commit` also
        // changes; reordering `tcb_shims` alone produces zero diff changes.
        let mut prov_a_json = sample_success_json();
        prov_a_json["correspondence_provenance"]["schema_version"] = json!(3);
        prov_a_json["correspondence_provenance"]["claim_kind"] = json!("exact_refines");
        prov_a_json["correspondence_provenance"]["permitted_axioms"] =
            json!(["Classical.choice", "Quot.sound", "propext"]);
        prov_a_json["correspondence_provenance"]["model_system_relation"] = json!({
            "kind": "simulation",
            "qualifier": "wf_stutter",
            "direction": "bidirectional",
            "licensed_claim_shapes": ["forall_safety"]
        });
        prov_a_json["correspondence_provenance"]["patched_files"] = json!([]);
        prov_a_json["correspondence_provenance"]["taint_reasons"] = json!([]);
        prov_a_json["correspondence_provenance"]["qualifiers"] = json!({
            "choice_total": true,
            "assumed_seams": [],
            "scope_kind": "full_gate"
        });
        prov_a_json["correspondence_provenance"]["tcb_shims"] = json!([
            {
                "id": "p1",
                "kind": "append_only_spec_lemma",
                "sha256": sha_a,
                "status": "proved",
                "guards": ["g1", "g2"]
            },
            {
                "id": "p2",
                "kind": "append_only_spec_lemma",
                "sha256": sha_b,
                "status": "tested",
                "guards": ["g3"]
            }
        ]);
        let mut prov_reorder_only = prov_a_json.clone();
        prov_reorder_only["correspondence_provenance"]["tcb_shims"] = json!([
            {
                "id": "p2",
                "kind": "append_only_spec_lemma",
                "sha256": sha_b,
                "status": "tested",
                "guards": ["g3"]
            },
            {
                "id": "p1",
                "kind": "append_only_spec_lemma",
                "sha256": sha_a,
                "status": "proved",
                "guards": ["g2", "g1"]
            }
        ]);
        let prov_a =
            parse_and_validate_receipt(&serde_json::to_vec(&prov_a_json).unwrap()).unwrap();
        let prov_r =
            parse_and_validate_receipt(&serde_json::to_vec(&prov_reorder_only).unwrap()).unwrap();
        assert!(diff_receipts(&prov_a, &prov_r, false).changes.is_empty());

        let mut prov_reorder_and_mut = prov_reorder_only.clone();
        prov_reorder_and_mut["correspondence_provenance"]["trusted_lean"] =
            json!({"Trusted.MirAst": sha_b});
        prov_reorder_and_mut["correspondence_provenance"]["upstream_commit"] = json!("feedface");
        let prov_m =
            parse_and_validate_receipt(&serde_json::to_vec(&prov_reorder_and_mut).unwrap())
                .unwrap();
        let prov_m_diff = diff_receipts(&prov_a, &prov_m, false);
        assert!(
            prov_m_diff
                .changes
                .iter()
                .any(|c| c.field == "correspondence_provenance.upstream_commit"),
            "{:?}",
            prov_m_diff.changes
        );
        assert!(
            prov_m_diff
                .changes
                .iter()
                .any(|c| c.field == "correspondence_provenance" && c.tier == DiffTier::TierB),
            "{:?}",
            prov_m_diff.changes
        );

        // Adding a candidate feature is a Tier A regression; retiring one is
        // Tier B.
        let mut cf_base = sample_success_json();
        cf_base["experimental"] = json!(true);
        cf_base["candidate_features"] = json!(["mir_semantics"]);
        let mut cf_added = cf_base.clone();
        cf_added["candidate_features"] = json!(["memory", "mir_semantics"]);
        let mut cf_retired = cf_base.clone();
        cf_retired["experimental"] = json!(false);
        cf_retired["candidate_features"] = json!([]);
        let cf_b_env = parse_and_validate_receipt(&serde_json::to_vec(&cf_base).unwrap()).unwrap();
        let cf_a_env = parse_and_validate_receipt(&serde_json::to_vec(&cf_added).unwrap()).unwrap();
        let cf_r_env =
            parse_and_validate_receipt(&serde_json::to_vec(&cf_retired).unwrap()).unwrap();
        let cf_add_diff = diff_receipts(&cf_b_env, &cf_a_env, false);
        assert!(cf_add_diff.has_regressions, "{:?}", cf_add_diff.changes);
        assert!(
            cf_add_diff
                .changes
                .iter()
                .any(|c| c.field == "candidate_features" && c.tier == DiffTier::TierA),
            "{:?}",
            cf_add_diff.changes
        );
        let cf_ret_diff = diff_receipts(&cf_b_env, &cf_r_env, false);
        assert!(!cf_ret_diff.has_regressions, "{:?}", cf_ret_diff.changes);
        assert!(
            cf_ret_diff
                .changes
                .iter()
                .any(|c| c.field == "candidate_features" && c.tier == DiffTier::TierB),
            "{:?}",
            cf_ret_diff.changes
        );

        // Dropping `candidate_features` (`Some(_) -> None`) is a Tier A
        // regression, whereas adding an empty `candidate_features: []` to a
        // legacy receipt (`None -> Some([])`) is Tier B.
        let mut cf_omitted = cf_base.clone();
        cf_omitted.as_object_mut().unwrap().remove("candidate_features");
        let cf_o_env =
            parse_and_validate_receipt(&serde_json::to_vec(&cf_omitted).unwrap()).unwrap();
        let cf_drop_diff = diff_receipts(&cf_b_env, &cf_o_env, false);
        assert!(cf_drop_diff.has_regressions, "{:?}", cf_drop_diff.changes);
        assert!(
            cf_drop_diff
                .changes
                .iter()
                .any(|c| c.field == "candidate_features" && c.tier == DiffTier::TierA),
            "{:?}",
            cf_drop_diff.changes
        );
        let mut cf_legacy_clean = sample_success_json();
        cf_legacy_clean.as_object_mut().unwrap().remove("candidate_features");
        let cf_legacy_env =
            parse_and_validate_receipt(&serde_json::to_vec(&cf_legacy_clean).unwrap()).unwrap();
        let cf_upgrade_diff = diff_receipts(&cf_legacy_env, &cf_r_env, false);
        assert!(!cf_upgrade_diff.has_regressions, "{:?}", cf_upgrade_diff.changes);
        assert!(
            cf_upgrade_diff
                .changes
                .iter()
                .any(|c| c.field == "candidate_features" && c.tier == DiffTier::TierB),
            "{:?}",
            cf_upgrade_diff.changes
        );
        let cf_drop_empty_diff = diff_receipts(&cf_r_env, &cf_legacy_env, false);
        assert!(cf_drop_empty_diff.has_regressions, "{:?}", cf_drop_empty_diff.changes);
        assert!(
            cf_drop_empty_diff
                .changes
                .iter()
                .any(|c| c.field == "candidate_features" && c.tier == DiffTier::TierA),
            "{:?}",
            cf_drop_empty_diff.changes
        );

        // Correspondence provenance v1 -> v3 qualifier/claim regressions and
        // `Some(_) -> None` qualifier removal must be Tier A, whereas clean
        // v1 -> v3 (`exact_refines`, `full_gate`, `choice_total: true`,
        // `assumed_seams: []`) stays Tier B.
        let v1_base =
            parse_and_validate_receipt(&serde_json::to_vec(&sample_success_json()).unwrap())
                .unwrap();
        let mut v3_clean_json = sample_success_json();
        v3_clean_json["correspondence_provenance"]["schema_version"] = json!(3);
        v3_clean_json["correspondence_provenance"]["claim_kind"] = json!("exact_refines");
        v3_clean_json["correspondence_provenance"]["permitted_axioms"] =
            json!(["Classical.choice", "Quot.sound", "propext"]);
        v3_clean_json["correspondence_provenance"]["model_system_relation"] = json!({
            "kind": "simulation",
            "qualifier": "wf_stutter",
            "direction": "bidirectional",
            "licensed_claim_shapes": ["forall_safety"]
        });
        v3_clean_json["correspondence_provenance"]["patched_files"] = json!([]);
        v3_clean_json["correspondence_provenance"]["tcb_shims"] = json!([]);
        v3_clean_json["correspondence_provenance"]["taint_reasons"] = json!([]);
        v3_clean_json["correspondence_provenance"]["qualifiers"] = json!({
            "choice_total": true,
            "assumed_seams": [],
            "scope_kind": "full_gate"
        });
        let v3_clean =
            parse_and_validate_receipt(&serde_json::to_vec(&v3_clean_json).unwrap()).unwrap();
        assert!(v3_clean.invariant_violations.is_empty(), "{:?}", v3_clean.invariant_violations);
        let v1_to_v3_clean = diff_receipts(&v1_base, &v3_clean, false);
        assert!(!v1_to_v3_clean.has_regressions, "{:?}", v1_to_v3_clean.changes);
        assert!(
            v1_to_v3_clean.changes.iter().any(|c| {
                c.field == "correspondence_provenance.qualifiers" && c.tier == DiffTier::TierB
            }),
            "{:?}",
            v1_to_v3_clean.changes
        );

        let mut v3_partial_json = v3_clean_json.clone();
        v3_partial_json["correspondence_provenance"]["qualifiers"]["scope_kind"] =
            json!("partial_gate");
        let v3_partial =
            parse_and_validate_receipt(&serde_json::to_vec(&v3_partial_json).unwrap()).unwrap();
        assert!(
            v3_partial.invariant_violations.is_empty(),
            "{:?}",
            v3_partial.invariant_violations
        );
        let v1_to_v3_partial = diff_receipts(&v1_base, &v3_partial, false);
        assert!(v1_to_v3_partial.has_regressions, "{:?}", v1_to_v3_partial.changes);
        assert!(
            v1_to_v3_partial.changes.iter().any(|c| {
                c.field == "correspondence_provenance.qualifiers" && c.tier == DiffTier::TierA
            }),
            "{:?}",
            v1_to_v3_partial.changes
        );

        // Dropping recorded qualifiers (`Some(_) -> None`) is Tier A.
        let v3_to_v1 = diff_receipts(&v3_clean, &v1_base, false);
        assert!(v3_to_v1.has_regressions, "{:?}", v3_to_v1.changes);
        assert!(
            v3_to_v1.changes.iter().any(|c| {
                c.field == "correspondence_provenance.qualifiers" && c.tier == DiffTier::TierA
            }),
            "{:?}",
            v3_to_v1.changes
        );

        // v1 -> v3 introducing non-standard permitted_axioms or weaker
        // claim_kind is Tier A.
        let mut v3_weak_json = v3_clean_json.clone();
        v3_weak_json["correspondence_provenance"]["claim_kind"] = json!("sound_refines");
        v3_weak_json["correspondence_provenance"]["permitted_axioms"] =
            json!(["Classical.choice", "CustomUnvettedAxiom", "Quot.sound", "propext"]);
        let v3_weak =
            parse_and_validate_receipt(&serde_json::to_vec(&v3_weak_json).unwrap()).unwrap();
        let v1_to_v3_weak = diff_receipts(&v1_base, &v3_weak, false);
        assert!(v1_to_v3_weak.has_regressions, "{:?}", v1_to_v3_weak.changes);
        assert!(
            v1_to_v3_weak.changes.iter().any(|c| {
                c.field == "correspondence_provenance.claim_kind" && c.tier == DiffTier::TierA
            }),
            "{:?}",
            v1_to_v3_weak.changes
        );
        assert!(
            v1_to_v3_weak.changes.iter().any(|c| {
                c.field == "correspondence_provenance.permitted_axioms" && c.tier == DiffTier::TierA
            }),
            "{:?}",
            v1_to_v3_weak.changes
        );
    }

    #[test]
    fn model_system_relation_transitions_classify_regressions_and_upgrades() {
        use crate::core::inspect::schema::ModelSystemRelation;

        let parse_with_rel = |rel: Option<serde_json::Value>| {
            let mut raw = sample_success_json();
            if let Some(val) = rel {
                raw["model_system_relation"] = val;
            }
            let env = parse_and_validate_receipt(&serde_json::to_vec(&raw).unwrap()).unwrap();
            assert!(
                env.invariant_violations.is_empty(),
                "fixture must be valid Receipt v3: {:?}",
                env.invariant_violations
            );
            env
        };

        let assert_rel_tier = |label: &str,
                               base_rel: Option<serde_json::Value>,
                               head_rel: Option<serde_json::Value>,
                               expect_tier: DiffTier| {
            let b = parse_with_rel(base_rel);
            let h = parse_with_rel(head_rel);
            let diff = diff_receipts(&b, &h, false);
            assert_eq!(
                diff.has_regressions,
                expect_tier == DiffTier::TierA,
                "{label}: unexpected has_regressions for changes {:?}",
                diff.changes
            );
            let change = diff
                .changes
                .iter()
                .find(|c| c.field == "model_system_relation")
                .unwrap_or_else(|| panic!("{label}: missing model_system_relation diff"));
            assert_eq!(
                change.tier, expect_tier,
                "{label}: expected {expect_tier:?}, got {:?}",
                change
            );
        };

        let make_rel = |kind: &str,
                        qualifier: Option<&str>,
                        direction: &str,
                        anchored_at: Option<&str>,
                        claims: &[&str],
                        unmodeled: &[&str]| {
            let mut obj = serde_json::Map::new();
            obj.insert("kind".into(), json!(kind));
            if let Some(q) = qualifier {
                obj.insert("qualifier".into(), json!(q));
            }
            obj.insert("direction".into(), json!(direction));
            if let Some(a) = anchored_at {
                obj.insert("anchored_at".into(), json!(a));
            }
            obj.insert("licensed_claim_shapes".into(), json!(claims));
            if !unmodeled.is_empty() {
                obj.insert("unmodeled_downstream".into(), json!(unmodeled));
            }
            serde_json::Value::Object(obj)
        };

        let sim_lock = make_rel(
            "simulation",
            Some("lock_step"),
            "bidirectional",
            None,
            &["forall_safety"],
            &[],
        );
        let hom_lock = make_rel(
            "homomorphism",
            Some("lock_step"),
            "bidirectional",
            None,
            &["forall_safety"],
            &[],
        );
        let abs_lock = make_rel(
            "abstraction",
            Some("lock_step"),
            "bidirectional",
            None,
            &["forall_safety"],
            &[],
        );
        let emb_lock = make_rel(
            "embedding",
            Some("lock_step"),
            "bidirectional",
            None,
            &["forall_safety"],
            &[],
        );
        let emb_none_q =
            make_rel("embedding", None, "bidirectional", None, &["forall_safety"], &[]);
        let none_rel = make_rel("none", None, "bidirectional", None, &[], &[]);

        // Presence transitions: `Some -> None` and `None -> Some(none)` are
        // Tier A regressions; `None -> Some(non-none)` is a Tier B improvement.
        assert_rel_tier("drop_relation", Some(sim_lock.clone()), None, DiffTier::TierA);
        assert_rel_tier("add_vacuous_none_relation", None, Some(none_rel.clone()), DiffTier::TierA);
        assert_rel_tier("add_substantive_relation", None, Some(sim_lock.clone()), DiffTier::TierB);

        // Relation kind downgrades (Tier A) vs upgrades (Tier B) across
        // `none < embedding < abstraction < homomorphism < simulation`.
        assert_rel_tier(
            "kind_sim_to_hom",
            Some(sim_lock.clone()),
            Some(hom_lock.clone()),
            DiffTier::TierA,
        );
        assert_rel_tier(
            "kind_hom_to_abs",
            Some(hom_lock.clone()),
            Some(abs_lock.clone()),
            DiffTier::TierA,
        );
        assert_rel_tier(
            "kind_abs_to_emb",
            Some(abs_lock.clone()),
            Some(emb_lock.clone()),
            DiffTier::TierA,
        );
        assert_rel_tier(
            "kind_emb_to_none",
            Some(emb_none_q.clone()),
            Some(none_rel.clone()),
            DiffTier::TierA,
        );
        assert_rel_tier(
            "kind_none_to_emb",
            Some(none_rel.clone()),
            Some(emb_none_q.clone()),
            DiffTier::TierB,
        );
        assert_rel_tier(
            "kind_emb_to_abs",
            Some(emb_lock.clone()),
            Some(abs_lock.clone()),
            DiffTier::TierB,
        );
        assert_rel_tier(
            "kind_abs_to_hom",
            Some(abs_lock.clone()),
            Some(hom_lock.clone()),
            DiffTier::TierB,
        );
        assert_rel_tier(
            "kind_hom_to_sim",
            Some(hom_lock.clone()),
            Some(sim_lock.clone()),
            DiffTier::TierB,
        );

        // Qualifier downgrades (Tier A) vs upgrades (Tier B) across
        // `None < stutter < wf_stutter < lock_step`.
        let sim_wf = make_rel(
            "simulation",
            Some("wf_stutter"),
            "bidirectional",
            None,
            &["forall_safety"],
            &[],
        );
        let sim_stutter =
            make_rel("simulation", Some("stutter"), "bidirectional", None, &["forall_safety"], &[]);
        assert_rel_tier(
            "qual_lock_to_wf",
            Some(sim_lock.clone()),
            Some(sim_wf.clone()),
            DiffTier::TierA,
        );
        assert_rel_tier(
            "qual_wf_to_stutter",
            Some(sim_wf.clone()),
            Some(sim_stutter.clone()),
            DiffTier::TierA,
        );
        assert_rel_tier(
            "qual_emb_lock_to_none",
            Some(emb_lock.clone()),
            Some(emb_none_q.clone()),
            DiffTier::TierA,
        );
        assert_rel_tier(
            "qual_stutter_to_wf",
            Some(sim_stutter.clone()),
            Some(sim_wf.clone()),
            DiffTier::TierB,
        );
        assert_rel_tier(
            "qual_wf_to_lock",
            Some(sim_wf.clone()),
            Some(sim_lock.clone()),
            DiffTier::TierB,
        );
        assert_rel_tier(
            "qual_emb_none_to_lock",
            Some(emb_none_q.clone()),
            Some(emb_lock.clone()),
            DiffTier::TierB,
        );

        // Direction downgrades/flips (Tier A) vs upgrades to `bidirectional`
        // (Tier B).
        let sim_fwd =
            make_rel("simulation", Some("wf_stutter"), "forward", None, &["forall_safety"], &[]);
        let sim_bwd =
            make_rel("simulation", Some("wf_stutter"), "backward", None, &["forall_safety"], &[]);
        assert_rel_tier(
            "dir_bi_to_fwd",
            Some(sim_wf.clone()),
            Some(sim_fwd.clone()),
            DiffTier::TierA,
        );
        assert_rel_tier(
            "dir_bi_to_bwd",
            Some(sim_wf.clone()),
            Some(sim_bwd.clone()),
            DiffTier::TierA,
        );
        assert_rel_tier(
            "dir_fwd_to_bwd",
            Some(sim_fwd.clone()),
            Some(sim_bwd.clone()),
            DiffTier::TierA,
        );
        assert_rel_tier(
            "dir_bwd_to_fwd",
            Some(sim_bwd.clone()),
            Some(sim_fwd.clone()),
            DiffTier::TierA,
        );
        assert_rel_tier(
            "dir_fwd_to_bi",
            Some(sim_fwd.clone()),
            Some(sim_wf.clone()),
            DiffTier::TierB,
        );
        assert_rel_tier(
            "dir_bwd_to_bi",
            Some(sim_bwd.clone()),
            Some(sim_wf.clone()),
            DiffTier::TierB,
        );

        // Anchor transitions: adding an anchor (`None -> Some`) is Tier B,
        // while dropping or shifting an existing anchor is Tier A; retaining
        // the same anchor across an unrelated Tier B improvement stays Tier B.
        let sim_anchored_hir = make_rel(
            "simulation",
            Some("wf_stutter"),
            "bidirectional",
            Some("source_hir"),
            &["forall_safety"],
            &[],
        );
        let sim_anchored_mir = make_rel(
            "simulation",
            Some("wf_stutter"),
            "bidirectional",
            Some("mir_post_cleanup"),
            &["forall_safety"],
            &[],
        );
        let sim_anchored_hir_more_claims = make_rel(
            "simulation",
            Some("wf_stutter"),
            "bidirectional",
            Some("source_hir"),
            &["forall_safety", "termination"],
            &[],
        );
        assert_rel_tier(
            "anchor_added",
            Some(sim_wf.clone()),
            Some(sim_anchored_hir.clone()),
            DiffTier::TierB,
        );
        assert_rel_tier(
            "anchor_removed",
            Some(sim_anchored_hir.clone()),
            Some(sim_wf.clone()),
            DiffTier::TierA,
        );
        assert_rel_tier(
            "anchor_shifted",
            Some(sim_anchored_hir.clone()),
            Some(sim_anchored_mir),
            DiffTier::TierA,
        );
        assert_rel_tier(
            "anchor_preserved_on_claim_expansion",
            Some(sim_anchored_hir.clone()),
            Some(sim_anchored_hir_more_claims),
            DiffTier::TierB,
        );

        // Licensed claim shape transitions: dropping any shape (even while
        // keeping another) or swapping disjoint shapes is Tier A; adding a
        // shape while retaining all existing shapes is Tier B.
        let sim_both_claims = make_rel(
            "simulation",
            Some("wf_stutter"),
            "bidirectional",
            None,
            &["forall_safety", "termination"],
            &[],
        );
        let sim_term_only = make_rel(
            "simulation",
            Some("wf_stutter"),
            "bidirectional",
            None,
            &["termination"],
            &[],
        );
        assert_rel_tier(
            "claims_drop_one_keep_one",
            Some(sim_both_claims.clone()),
            Some(sim_wf.clone()),
            DiffTier::TierA,
        );
        assert_rel_tier(
            "claims_disjoint_swap",
            Some(sim_wf.clone()),
            Some(sim_term_only),
            DiffTier::TierA,
        );
        assert_rel_tier(
            "claims_expand",
            Some(sim_wf.clone()),
            Some(sim_both_claims),
            DiffTier::TierB,
        );

        // Unmodeled downstream assumptions: adding any new entry (including
        // from empty `[]`) is Tier A; retiring entries (partial or full) is
        // Tier B.
        let sim_unmodeled_one = make_rel(
            "simulation",
            Some("wf_stutter"),
            "bidirectional",
            None,
            &["forall_safety"],
            &["llvm"],
        );
        let sim_unmodeled_two = make_rel(
            "simulation",
            Some("wf_stutter"),
            "bidirectional",
            None,
            &["forall_safety"],
            &["llvm", "linker"],
        );
        let sim_unmodeled_linker = make_rel(
            "simulation",
            Some("wf_stutter"),
            "bidirectional",
            None,
            &["forall_safety"],
            &["linker"],
        );
        assert_rel_tier(
            "unmodeled_add_from_empty",
            Some(sim_wf.clone()),
            Some(sim_unmodeled_one.clone()),
            DiffTier::TierA,
        );
        assert_rel_tier(
            "unmodeled_add_second",
            Some(sim_unmodeled_one.clone()),
            Some(sim_unmodeled_two.clone()),
            DiffTier::TierA,
        );
        assert_rel_tier(
            "unmodeled_disjoint_swap",
            Some(sim_unmodeled_one.clone()),
            Some(sim_unmodeled_linker),
            DiffTier::TierA,
        );
        assert_rel_tier(
            "unmodeled_retire_one_keep_one",
            Some(sim_unmodeled_two),
            Some(sim_unmodeled_one.clone()),
            DiffTier::TierB,
        );
        assert_rel_tier(
            "unmodeled_retire_all",
            Some(sim_unmodeled_one),
            Some(sim_wf.clone()),
            DiffTier::TierB,
        );

        // Mixed-axis transition: upgrading `kind` (`homomorphism` to
        // `simulation`) while regressing `qualifier` (`lock_step` to
        // `wf_stutter`) must still classify as Tier A.
        assert_rel_tier(
            "mixed_kind_upgrade_qual_downgrade",
            Some(hom_lock),
            Some(sim_wf),
            DiffTier::TierA,
        );

        // Direct boundary assertions on `is_relation_regression` for isolated
        // single-field transitions and `(None, None)` / `stutter -> None`
        // cases not independently reachable through receipt schema invariants.
        let rel = |kind: &str, qual: Option<&str>| ModelSystemRelation {
            kind: kind.to_owned(),
            qualifier: qual.map(str::to_owned),
            direction: "bidirectional".to_owned(),
            anchored_at: None,
            licensed_claim_shapes: vec!["forall_safety".to_owned()],
            unmodeled_downstream: Vec::new(),
        };
        assert!(!is_relation_regression(None, None));
        assert!(is_relation_regression(Some(&rel("embedding", None)), Some(&rel("none", None))));
        assert!(!is_relation_regression(Some(&rel("none", None)), Some(&rel("embedding", None))));
        assert!(is_relation_regression(
            Some(&rel("simulation", Some("stutter"))),
            Some(&rel("simulation", None))
        ));
        assert!(!is_relation_regression(
            Some(&rel("simulation", None)),
            Some(&rel("simulation", Some("stutter")))
        ));
        assert!(!is_relation_regression(
            Some(&rel("simulation", Some("wf_stutter"))),
            Some(&rel("simulation", Some("wf_stutter")))
        ));
    }
}
