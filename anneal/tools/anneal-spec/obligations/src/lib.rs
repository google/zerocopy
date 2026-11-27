// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Builds a per-function evidence ledger for Anneal verification obligations.
//!
//! [`build`] combines three kinds of input into one [`Ledger`]:
//!
//! - Receipt Schema v3 documents written by `cargo anneal verify`. Their
//!   compiler census enumerates the crate's functions, and the `selected` list
//!   of a verified receipt names the functions, and the instances of generic
//!   functions, that the run's theorem covers.
//! - `request.json` files. Their selected-unit `scope.roots`, the functions
//!   their zero-argument `scope.instantiations` name, and the instances that
//!   their other `scope.instantiations` entries produce have a stated
//!   specification.
//! - Rust sources carrying `anneal::spec` attributes or
//!   `anneal::external_spec!` blocks. Their targets also have a stated
//!   specification.
//!
//! Each function gets exactly one [`Tier`]. Nothing here re-checks a proof or
//! a receipt's integrity: the ledger only projects what its inputs say, so
//! receipts should first pass `cargo anneal inspect`.

#![forbid(unsafe_code)]

mod binding;

use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use anneal_spec_lower::{list_targets, Source};
pub use binding::SpecSource;
use binding::{
    canonical_request_sha256, matches_instantiation, opt_sha256_field, parse_receipt_instantiations,
};
use serde_json::{json, Map, Value};

/// The JSON ledger format that [`Ledger::to_json`] writes and
/// [`Baseline::from_json`] reads.
pub const SCHEMA: &str = "anneal-obligations/1";

/// The prefix of every item ID. The rest of the ID is the function's compiler
/// census path, which is also the path that `request.json` roots and
/// `anneal-spec` targets use.
pub const ID_PREFIX: &str = "rust-path-v1::";

const SUCCESS_STATUSES: [&str; 4] = [
    "crate_verified",
    "selected_unit_verified",
    "tainted_crate_verified",
    "tainted_selected_unit_verified",
];
const FAILURE_STATUSES: [&str; 4] =
    ["compiler_failed", "proof_failed", "tool_failed", "unsupported"];
const FOUNDATION_AXIOMS: [&str; 3] = ["Classical.choice", "Quot.sound", "propext"];
/// The Profile v1 and Profile v2 theorems, in that order, that
/// `audit.canonicalRoot` names on a whole-crate receipt.
const CRATE_ROOTS: [&str; 2] =
    ["Trusted.MirSemantics.CrateTheorem", "Trusted.MirSemantics.CrateTheoremV2"];
/// The same, on a selected-unit receipt.
const UNIT_ROOTS: [&str; 2] =
    ["Trusted.MirSemantics.UnitTheorem", "Trusted.MirSemantics.UnitTheoremV2"];
/// Census kinds that the ledger tracks: the definitions that selected-unit
/// verification accepts as roots.
const FUNCTION_KINDS: [&str; 2] = ["AssocFn", "Fn"];
const SORRY_TAINT: &str = "sorry_in_proof";
const SORRY_AXIOM: &str = "sorryAx";

/// How much evidence an item has, ordered from weakest to strongest.
///
/// The derived order is the ratchet order: an item regresses when its tier
/// becomes smaller.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub enum Tier {
    /// A function in a receipt census with no stated specification.
    #[default]
    Uncontracted,
    /// A function with a stated specification but no complete verified proof
    /// among the inputs.
    Deferred,
    /// [`Tier::ProvenConditional`] as reported under `--audit-assumptions`,
    /// which refuses to count a proof whose receipt discloses conditions.
    Assumed,
    /// Reserved for runtime-checked obligations. No input format produces it
    /// yet.
    RuntimeChecked,
    /// Reserved for runtime-checked obligations that are also exercised by a
    /// fuzzing or Miri harness. No input format produces it yet.
    CheckedFuzz,
    /// Reserved for values minted by a verified validator. No input format
    /// produces it yet.
    EnvelopeMinted,
    /// Covered by a verified receipt that discloses at least one condition.
    ProvenConditional,
    /// Covered by a verified receipt that discloses no condition.
    ProvenClosed,
}

impl Tier {
    /// Every tier, weakest first.
    pub const ALL: [Tier; 8] = [
        Tier::Uncontracted,
        Tier::Deferred,
        Tier::Assumed,
        Tier::RuntimeChecked,
        Tier::CheckedFuzz,
        Tier::EnvelopeMinted,
        Tier::ProvenConditional,
        Tier::ProvenClosed,
    ];

    /// The tier's name in text and JSON output.
    pub const fn name(self) -> &'static str {
        match self {
            Tier::Uncontracted => "uncontracted",
            Tier::Deferred => "deferred",
            Tier::Assumed => "assumed",
            Tier::RuntimeChecked => "runtime_checked",
            Tier::CheckedFuzz => "checked_fuzz",
            Tier::EnvelopeMinted => "envelope_minted",
            Tier::ProvenConditional => "proven_conditional",
            Tier::ProvenClosed => "proven_closed",
        }
    }

    /// Parses a tier name.
    pub fn from_name(name: &str) -> Option<Tier> {
        Tier::ALL.into_iter().find(|t| t.name() == name)
    }

    /// Whether a verified receipt covers the item. [`Tier::Assumed`] is not
    /// proven: it is how `--audit-assumptions` reports a conditional proof.
    pub fn is_proven(self) -> bool {
        self >= Tier::ProvenConditional
    }
}

/// What a verified receipt establishes for the functions it selects.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Discharge {
    /// The kernel accepted a proof that uses neither `sorry` nor an axiom
    /// outside the Lean foundation, subject to the listed conditions.
    Proven(BTreeSet<String>),
    /// The proof uses `sorry` or a non-foundation axiom, for the listed
    /// reasons, so it establishes nothing about the selected functions.
    Incomplete(BTreeSet<String>),
}

/// The parts of a Receipt Schema v3 document that the ledger uses.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Receipt {
    /// The receipt's `status`.
    pub status: String,
    /// `configuration.crate_name`, which failure receipts do not record.
    pub crate_name: Option<String>,
    /// `request_sha256`, when recorded on a verified receipt.
    pub request_sha256: Option<String>,
    /// `specification_manifest_sha256`, when recorded on a verified receipt.
    pub specification_manifest_sha256: Option<String>,
    /// Census paths of the crate's functions with bodies.
    pub functions: BTreeSet<String>,
    /// The paths the receipt selects: members of [`Receipt::functions`], and
    /// the instance paths of bodies instantiated from `scope.instantiations`.
    pub selected: BTreeSet<String>,
    /// For each member of [`Receipt::selected`] that is an instance of a
    /// generic function, the `scope.instantiations` entries (path and
    /// generic arguments) that could have produced it. A request that lists
    /// one of these entries states a specification for the instance.
    pub instances: BTreeMap<String, BTreeSet<(String, Vec<String>)>>,
    /// What the receipt establishes for [`Receipt::selected`], or `None` for a
    /// failure receipt.
    pub discharge: Option<Discharge>,
}

impl Receipt {
    /// Reads a receipt, rejecting documents whose fields disagree in ways that
    /// would make the ledger overstate the evidence.
    pub fn from_json(value: &Value) -> Result<Receipt, String> {
        Receipt::parse(value).map_err(|e| escape_controls(&e))
    }

    fn parse(value: &Value) -> Result<Receipt, String> {
        let root = value.as_object().ok_or("receipt root must be a JSON object")?;
        match root.get("schema_version").and_then(Value::as_u64) {
            Some(3) => {}
            _ => return Err("receipt schema_version must be 3".into()),
        }
        let status = str_field(root, "status", "")?.to_owned();
        let taints = str_array(root, "taint_reasons", "")?;
        // Failure statuses have no `tainted_` form: a failed run records its
        // relaxations in `taint_reasons` alone.
        if FAILURE_STATUSES.contains(&status.as_str()) {
            return Ok(Receipt {
                status,
                crate_name: None,
                request_sha256: None,
                specification_manifest_sha256: None,
                functions: BTreeSet::new(),
                selected: BTreeSet::new(),
                instances: BTreeMap::new(),
                discharge: None,
            });
        }
        if !SUCCESS_STATUSES.contains(&status.as_str()) {
            return Err(format!("unrecognized receipt status `{status}`"));
        }
        if status.starts_with("tainted_") == taints.is_empty() {
            return Err(format!(
                "receipt status `{status}` disagrees with taint_reasons {taints:?}"
            ));
        }

        let request_sha256 = opt_sha256_field(root, "request_sha256", "")?;
        let specification_manifest_sha256 =
            opt_sha256_field(root, "specification_manifest_sha256", "")?;
        let crate_name =
            str_field(obj_field(root, "configuration", "")?, "crate_name", "/configuration")?;
        let scope = obj_field(root, "scope", "")?;
        let scope_kind = str_field(scope, "kind", "/scope")?;
        let crate_scope = match scope_kind {
            "crate" => true,
            "selected_unit" => false,
            other => return Err(format!("unrecognized receipt scope kind `{other}`")),
        };
        if status.ends_with("crate_verified") != crate_scope {
            return Err(format!(
                "receipt status `{status}` disagrees with scope kind `{scope_kind}`"
            ));
        }
        let (declared_roots, instantiations) = if crate_scope {
            if scope.contains_key("roots") {
                return Err("/scope/roots is not allowed on a crate receipt".into());
            }
            if scope.contains_key("instantiations") {
                return Err("/scope/instantiations is not allowed on a crate receipt".into());
            }
            (BTreeSet::new(), Vec::new())
        } else {
            let roots: BTreeSet<String> =
                str_array(scope, "roots", "/scope")?.into_iter().collect();
            if roots.iter().any(String::is_empty) {
                return Err("/scope/roots entries must be non-empty".into());
            }
            let insts = parse_receipt_instantiations(scope)?;
            if roots.is_empty() && insts.is_empty() {
                return Err("/scope needs at least one root or instantiation".into());
            }
            (roots, insts)
        };

        // Census functions with bodies, by `def_id`, with their `selected`
        // flags. Other census kinds are neither tracked nor listed in
        // `selected`, although whole-crate capture flags them as selected.
        let mut functions = BTreeSet::new();
        let mut duplicates = BTreeSet::new();
        let mut by_def: BTreeMap<u64, (&str, bool)> = BTreeMap::new();
        for (i, entry) in array_field(root, "census", "")?.iter().enumerate() {
            let ptr = format!("/census/{i}");
            let entry = entry.as_object().ok_or_else(|| format!("{ptr} must be an object"))?;
            let path = str_field(entry, "path", &ptr)?;
            let kind = str_field(entry, "kind", &ptr)?;
            let has_body = bool_field(entry, "has_body", &ptr)?;
            let census_selected = bool_field(entry, "selected", &ptr)?;
            if !(has_body && FUNCTION_KINDS.contains(&kind)) {
                continue;
            }
            if crate_scope && !census_selected {
                return Err(format!("crate receipt census leaves function `{path}` unselected"));
            }
            let def_id = u64_field(entry, "def_id", &ptr)?;
            if by_def.insert(def_id, (path, census_selected)).is_some() {
                return Err(format!("receipt census lists def_id {def_id} twice"));
            }
            if !functions.insert(path.to_owned()) {
                duplicates.insert(path.to_owned());
            }
        }
        let census_roots: BTreeSet<&str> =
            by_def.values().filter(|(_, selected)| *selected).map(|(path, _)| *path).collect();
        if !crate_scope {
            let expected_roots: BTreeSet<&str> =
                declared_roots.iter().map(String::as_str).collect();
            if census_roots != expected_roots {
                return Err(
                    "receipt `/scope/roots` disagrees with the census `selected` flags".into()
                );
            }
        }

        // Capture lists each selected root under its census path, and each
        // body instantiated from `scope.instantiations` under its instance
        // path (which includes the generic arguments) and the `def_id` of
        // the function it instantiates. An instance is its own item: proving
        // `f::<u8>` says nothing about `f::<T>` for other `T`.
        let mut roots = BTreeSet::new();
        let mut selected = BTreeSet::new();
        let mut instances: BTreeMap<String, BTreeSet<(String, Vec<String>)>> = BTreeMap::new();
        let mut instantiated_selected = 0usize;
        for (i, entry) in array_field(root, "selected", "")?.iter().enumerate() {
            let ptr = format!("/selected/{i}");
            let entry = entry.as_object().ok_or_else(|| format!("{ptr} must be an object"))?;
            let path = str_field(entry, "path", &ptr)?;
            let def_id = u64_field(entry, "def_id", &ptr)?;
            let &(census_path, census_selected) = by_def.get(&def_id).ok_or_else(|| {
                format!("{ptr} names def_id {def_id}, which is not a census function with a body")
            })?;
            if census_selected && path == census_path {
                roots.insert(path);
            } else if matches_instantiation(census_path, path, &instantiations) {
                instantiated_selected += 1;
                // Zero-argument entries name non-generic functions, which a
                // request covers as it covers a root.
                let producers: BTreeSet<(String, Vec<String>)> = instantiations
                    .iter()
                    .filter(|(_, args)| !args.is_empty())
                    .filter(|inst| {
                        matches_instantiation(census_path, path, std::slice::from_ref(*inst))
                    })
                    .cloned()
                    .collect();
                if !producers.is_empty() {
                    instances.entry(path.to_owned()).or_default().extend(producers);
                }
            } else {
                return Err(format!(
                    "{ptr} `{path}` is neither a selected census function nor an instantiation \
                     of `{census_path}`"
                ));
            }
            selected.insert(path.to_owned());
        }
        if roots != census_roots {
            return Err("receipt `selected` disagrees with the census `selected` flags".into());
        }
        if instantiated_selected > instantiations.len() {
            return Err(
                "receipt `selected` lists more instantiations than `/scope/instantiations`".into(),
            );
        }
        if instantiated_selected == 0
            && instantiations
                .iter()
                .any(|(ip, args)| !args.is_empty() || !declared_roots.contains(ip.as_str()))
        {
            return Err("receipt `selected` omits `/scope/instantiations`".into());
        }
        // Capture refuses two captured functions with one identity, so this
        // only fires on a malformed receipt; unselected duplicates are merged.
        if let Some(path) = selected.intersection(&duplicates).next() {
            return Err(format!("receipt census lists selected function `{path}` twice"));
        }

        let audit = obj_field(root, "audit", "")?;
        let canonical_root = str_field(audit, "canonicalRoot", "/audit")?;
        let axioms = str_array(audit, "axioms", "/audit")?;
        let mut sorry = str_array(audit, "sorryDeclarations", "/audit")?;
        if let Some(top) = root.get("sorry_declarations") {
            if !top.is_null() {
                sorry.extend(value_str_array(top, "/sorry_declarations")?);
            }
        }

        let mut reasons = BTreeSet::new();
        if !sorry.is_empty()
            || taints.iter().any(|t| t == SORRY_TAINT)
            || axioms.iter().any(|a| a == SORRY_AXIOM)
        {
            reasons.insert(SORRY_TAINT.to_owned());
        }
        for axiom in &axioms {
            if axiom != SORRY_AXIOM && !FOUNDATION_AXIOMS.contains(&axiom.as_str()) {
                reasons.insert(format!("nonfoundation_axiom:{axiom}"));
            }
        }
        if !bool_field(audit, "replay", "/audit")? {
            reasons.insert("no_kernel_replay".to_owned());
        }
        if !bool_field(audit, "exactType", "/audit")? {
            reasons.insert("inexact_theorem_type".to_owned());
        }
        let spec_warning_codes = spec_warning_codes(root, audit)?;
        // A theorem for the other scope would misstate what was proved, and a
        // theorem the ledger does not know says nothing it can interpret.
        let (scope_roots, other_roots) =
            if crate_scope { (CRATE_ROOTS, UNIT_ROOTS) } else { (UNIT_ROOTS, CRATE_ROOTS) };
        if other_roots.contains(&canonical_root) {
            return Err(format!(
                "audit.canonicalRoot `{canonical_root}` disagrees with scope kind `{scope_kind}`"
            ));
        }
        if !scope_roots.contains(&canonical_root) {
            reasons.insert("unrecognized_canonical_root".to_owned());
        }

        let profile_v2 = canonical_root == scope_roots[1];
        let mut conditions = BTreeSet::new();
        for taint in &taints {
            if taint != SORRY_TAINT {
                conditions.insert(format!("taint:{taint}"));
            }
        }
        if !crate_scope {
            conditions.insert("selected_unit_scope".to_owned());
        }
        if profile_v2 {
            conditions.insert("unbridged_semantics".to_owned());
            conditions.insert("caller_memory_thread_isolation".to_owned());
        }
        match root.get("experimental") {
            Some(Value::Bool(false)) => {}
            Some(Value::Bool(true)) => {
                conditions.insert("candidate_tier_model".to_owned());
            }
            _ => return Err("receipt `experimental` must be a boolean".into()),
        }
        shim_conditions(root, "", "tcb_shim", &mut conditions)?;
        if let Some(horizon) = root.get("horizon") {
            let horizon = horizon.as_object().ok_or("/horizon must be an object")?;
            match str_field(horizon, "kind", "/horizon")? {
                "unbounded" => {}
                "bounded" => {
                    let k = u64_field(horizon, "k", "/horizon")?;
                    conditions.insert(format!("bounded_horizon:{k}"));
                }
                other => {
                    conditions.insert(format!("horizon:{other}"));
                }
            }
        }
        relation_condition(root, "", "model_system_relation", &mut conditions)?;
        // The anti-vacuity lint does not block verification, so a property
        // weakened to `True` still verifies; surface its warnings, and its
        // absence, so that they show up in the tier and the ratchet.
        match spec_warning_codes {
            None => {
                conditions.insert("spec_lint_not_run".to_owned());
            }
            Some(codes) => {
                conditions.extend(codes.into_iter().map(|code| format!("spec_warning:{code}")));
            }
        }
        let provenance = obj_field(root, "correspondence_provenance", "")?;
        // Profile v2 never has correspondence, which `unbridged_semantics`
        // already discloses; a Profile v1 receipt may instead leave it to a
        // repository check that the receipt does not record.
        match provenance.get("applicable") {
            None | Some(Value::Bool(true)) => {}
            Some(Value::Bool(false)) => {
                if !profile_v2 {
                    conditions.insert("correspondence_not_bound".to_owned());
                }
            }
            Some(_) => return Err("/correspondence_provenance/applicable must be a boolean".into()),
        }
        let provenance_ptr = "/correspondence_provenance";
        shim_conditions(provenance, provenance_ptr, "correspondence_tcb_shim", &mut conditions)?;
        if let Some(taints) = provenance.get("taint_reasons") {
            for taint in value_str_array(taints, "/correspondence_provenance/taint_reasons")? {
                conditions.insert(format!("correspondence_taint:{taint}"));
            }
        }
        // `taint_reasons` summarizes some qualifiers but not a partial gate,
        // so read the qualifiers themselves, deriving the same taint atoms
        // that `cargo anneal inspect` expects them to imply.
        if let Some(qualifiers) = provenance.get("qualifiers") {
            let ptr = "/correspondence_provenance/qualifiers";
            let qualifiers =
                qualifiers.as_object().ok_or_else(|| format!("{ptr} must be an object"))?;
            match str_field(qualifiers, "scope_kind", ptr)? {
                "full_gate" => {}
                other => {
                    conditions.insert(format!("correspondence_scope:{other}"));
                }
            }
            if !bool_field(qualifiers, "choice_total", ptr)? {
                conditions.insert("correspondence_taint:choice_total_false".to_owned());
            }
            if !str_array(qualifiers, "assumed_seams", ptr)?.is_empty() {
                conditions.insert("correspondence_taint:assumed_seams_present".to_owned());
            }
        }
        // `exact_refines` is the strongest claim; `cargo anneal inspect diff`
        // treats any move away from it as a regression.
        match provenance.get("claim_kind") {
            None => {}
            Some(Value::String(kind)) if kind == "exact_refines" => {}
            Some(Value::String(kind)) => {
                conditions.insert(format!("correspondence_claim:{kind}"));
            }
            Some(_) => return Err("/correspondence_provenance/claim_kind must be a string".into()),
        }
        relation_condition(
            provenance,
            provenance_ptr,
            "correspondence_model_system_relation",
            &mut conditions,
        )?;
        let discharge = if reasons.is_empty() {
            Discharge::Proven(conditions)
        } else {
            Discharge::Incomplete(reasons)
        };

        Ok(Receipt {
            status,
            crate_name: Some(crate_name.to_owned()),
            request_sha256,
            specification_manifest_sha256,
            functions,
            selected,
            instances,
            discharge: Some(discharge),
        })
    }
}

/// The `code` of every anti-vacuity warning in the receipt's `spec_warnings`
/// and its `audit.specWarnings`, or `None` if the receipt has no
/// `spec_warnings` field, meaning that the lint did not run (as on the NDJSON
/// comparator route).
fn spec_warning_codes(
    root: &Map<String, Value>,
    audit: &Map<String, Value>,
) -> Result<Option<BTreeSet<String>>, String> {
    let collect = |value: &Value, ptr: &str, codes: &mut BTreeSet<String>| {
        let entries = value.as_array().ok_or_else(|| format!("{ptr} must be an array"))?;
        for (i, entry) in entries.iter().enumerate() {
            let entry_ptr = format!("{ptr}/{i}");
            let entry =
                entry.as_object().ok_or_else(|| format!("{entry_ptr} must be an object"))?;
            let code = str_field(entry, "code", &entry_ptr)?;
            if code.is_empty() {
                return Err(format!("{entry_ptr}/code must be non-empty"));
            }
            codes.insert(code.to_owned());
        }
        Ok::<(), String>(())
    };
    let mut codes = BTreeSet::new();
    if let Some(raw) = audit.get("specWarnings") {
        collect(raw, "/audit/specWarnings", &mut codes)?;
    }
    match root.get("spec_warnings") {
        None => Ok(None),
        Some(raw) => {
            collect(raw, "/spec_warnings", &mut codes)?;
            Ok(Some(codes))
        }
    }
}

/// The parts of a `cargo anneal verify` `request.json` that the ledger uses.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Request {
    /// `compilation.crate_name`, when present.
    pub crate_name: Option<String>,
    /// Canonical `request_sha256` matching `cargo anneal verify`, when the
    /// request includes complete compilation and proof sections.
    pub request_sha256: Option<String>,
    /// The concrete functions a selected-unit request states a specification
    /// for: its `scope.roots`, then the paths of its zero-argument
    /// `scope.instantiations` entries, which name non-generic functions that
    /// capture selects under their census paths. Empty for a crate request,
    /// whose receipt supplies the covered functions instead.
    pub roots: Vec<String>,
    /// The `scope.instantiations` entries with generic arguments, as path and
    /// arguments. The request states a specification for each listed
    /// instance only, so a receipt proves the instances as separate items
    /// named by their instance paths, and the generic function itself stays
    /// `deferred`.
    pub instantiated: Vec<(String, Vec<String>)>,
}

impl Request {
    /// Reads a request.
    pub fn from_json(value: &Value) -> Result<Request, String> {
        Request::parse(value).map_err(|e| escape_controls(&e))
    }

    fn parse(value: &Value) -> Result<Request, String> {
        let root = value.as_object().ok_or("request root must be a JSON object")?;
        match root.get("schema_version").and_then(Value::as_u64) {
            Some(1) => {}
            _ => return Err("request schema_version must be 1".into()),
        }
        let crate_name = match obj_field(root, "compilation", "")?.get("crate_name") {
            None => None,
            Some(Value::String(name)) => Some(name.clone()),
            Some(_) => return Err("/compilation/crate_name must be a string".into()),
        };
        let scope = obj_field(root, "scope", "")?;
        let (roots, instantiated) = match str_field(scope, "kind", "/scope")? {
            "crate" if scope.contains_key("instantiations") => {
                return Err("/scope/instantiations is not allowed on a crate request".into());
            }
            "crate" => (Vec::new(), Vec::new()),
            "selected_unit" => {
                let mut roots = str_array(scope, "roots", "/scope")?;
                let mut instantiated = Vec::new();
                let mut any_instantiation = false;
                if let Some(insts) = scope.get("instantiations") {
                    let insts = insts.as_array().ok_or("/scope/instantiations must be an array")?;
                    for (i, inst) in insts.iter().enumerate() {
                        let ptr = format!("/scope/instantiations/{i}");
                        let inst =
                            inst.as_object().ok_or_else(|| format!("{ptr} must be an object"))?;
                        let args = str_array(inst, "args", &ptr)?;
                        let path = str_field(inst, "path", &ptr)?.to_owned();
                        any_instantiation = true;
                        if args.is_empty() {
                            if !roots.contains(&path) {
                                roots.push(path);
                            }
                        } else {
                            instantiated.push((path, args));
                        }
                    }
                }
                if roots.is_empty() && !any_instantiation {
                    return Err("/scope needs at least one root or instantiation".into());
                }
                (roots, instantiated)
            }
            other => return Err(format!("unrecognized request scope kind `{other}`")),
        };
        let request_sha256 = canonical_request_sha256(root)?;
        Ok(Request { crate_name, request_sha256, roots, instantiated })
    }
}

/// Lists the `anneal::spec` targets in `sources` as one [`Input::Spec`] per
/// file, labeled with the file's [`Source::label`]. The files are checked
/// together, with the same file-level, duplicate-target, and claim-collision
/// checks as `anneal-spec-lower --list-targets`.
pub fn spec_inputs(sources: &[Source]) -> Result<Vec<LabeledInput>, String> {
    let targets = list_targets(sources).map_err(|errors| {
        let display_sources: Vec<Source> = sources
            .iter()
            .map(|s| Source {
                label: escape_controls(&s.label),
                text: s.text.clone(),
                module: s.module.clone(),
            })
            .collect();
        let rendered: String = errors.iter().map(|e| e.render(&display_sources)).collect();
        escape_diagnostic_lines(&rendered)
    })?;
    let shared: Arc<[Source]> = sources
        .iter()
        .map(|s| Source { label: s.label.clone(), text: s.text.clone(), module: s.module.clone() })
        .collect::<Vec<_>>()
        .into();
    let whole_v1 = anneal_spec_lower::lower_with(&shared, &anneal_spec_lower::Options::default())
        .ok()
        .map(|l| binding::single_module_spec_manifest_sha256("Spec", &l.spec_lean));
    let mut by_file: BTreeMap<usize, Vec<(String, String)>> = BTreeMap::new();
    for target in targets {
        by_file.entry(target.file).or_default().push((target.target, target.claim));
    }
    Ok(sources
        .iter()
        .enumerate()
        .map(|(i, source)| LabeledInput {
            label: source.label.clone(),
            input: Input::Spec(SpecSource::from_lowered(
                i,
                &shared,
                by_file.remove(&i).unwrap_or_default(),
                whole_v1.as_deref(),
            )),
        })
        .collect())
}

/// One parsed input to [`build`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Input {
    Receipt(Receipt),
    Request(Request),
    /// The targets and lowered specification digests of one file's
    /// `anneal::spec` items (see [`spec_inputs`]).
    Spec(SpecSource),
}

impl Input {
    fn kind(&self) -> &'static str {
        match self {
            Input::Receipt(_) => "receipt",
            Input::Request(_) => "request",
            Input::Spec(_) => "spec",
        }
    }
}

/// An [`Input`] and the path it was read from, which the ledger reports.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LabeledInput {
    pub label: String,
    pub input: Input,
}

/// One item of a [`Ledger`].
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Entry {
    pub tier: Tier,
    /// For a proven tier, the conditions its receipt discloses; for a deferred
    /// item with an incomplete proof, the reasons the proof is incomplete.
    pub conditions: BTreeSet<String>,
    /// The receipt that supplied the tier, if any.
    pub evidence: Option<String>,
    /// `<kind>:<path>` of every request or source that states a specification
    /// for the item.
    pub contracts: BTreeSet<String>,
}

/// An input the ledger was built from.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SourceInfo {
    pub kind: &'static str,
    pub path: String,
    /// A receipt's `status`.
    pub status: Option<String>,
}

/// A per-function evidence ledger.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ledger {
    pub crate_name: Option<String>,
    pub audit_assumptions: bool,
    pub sources: Vec<SourceInfo>,
    /// Items keyed by ID ([`ID_PREFIX`] followed by the census path).
    pub items: BTreeMap<String, Entry>,
}

/// A receipt's claim about one function, used to pick the strongest one.
#[derive(Clone)]
struct Candidate {
    tier: Tier,
    conditions: BTreeSet<String>,
    evidence: String,
    request_sha256: Option<String>,
    specification_manifest_sha256: Option<String>,
}

impl Candidate {
    /// Whether `self` is stronger evidence than `other`: a higher tier, then
    /// fewer conditions, then the first by conditions and path, so the choice
    /// never depends on input order. Conditions from different receipts are
    /// never combined for one obligation, because no single proof would support
    /// the result.
    fn beats(&self, other: &Candidate) -> bool {
        if self.tier != other.tier {
            return self.tier > other.tier;
        }
        (self.conditions.len(), &self.conditions, &self.evidence)
            < (other.conditions.len(), &other.conditions, &other.evidence)
    }

    fn satisfies_contract(&self, req: &ContractBinding) -> bool {
        match req {
            ContractBinding::Request(Some(expected)) => {
                self.request_sha256.as_deref() == Some(expected.as_str())
            }
            ContractBinding::Spec(allowed) if !allowed.is_empty() => self
                .specification_manifest_sha256
                .as_deref()
                .is_some_and(|actual| allowed.contains(actual)),
            ContractBinding::Request(None)
            | ContractBinding::Spec(_)
            | ContractBinding::UnprovenGeneric => false,
        }
    }
}

#[derive(Clone)]
enum ContractBinding {
    Request(Option<String>),
    Spec(BTreeSet<String>),
    /// Generic function named by `scope.instantiations` in a request: receipts
    /// prove concrete instances, while the unquantified generic stays deferred.
    UnprovenGeneric,
}

/// Builds the ledger for `inputs`.
///
/// Every input must agree on the crate, as must `crate_name` when given.
/// Under `audit_assumptions`, every [`Tier::ProvenConditional`] item is
/// reported as [`Tier::Assumed`].
pub fn build(
    inputs: &[LabeledInput],
    crate_name: Option<&str>,
    audit_assumptions: bool,
) -> Result<Ledger, String> {
    let mut crate_name = crate_name.map(str::to_owned);
    for LabeledInput { label, input } in inputs {
        match input {
            Input::Receipt(receipt) => {
                if let Some(name) = &receipt.crate_name {
                    unify_crate(&mut crate_name, name, label)?;
                }
            }
            Input::Request(request) => {
                if let Some(name) = &request.crate_name {
                    unify_crate(&mut crate_name, name, label)?;
                }
            }
            Input::Spec(_) => {}
        }
    }

    let mut items: BTreeMap<String, Entry> = BTreeMap::new();
    let mut item_contracts: BTreeMap<String, BTreeMap<String, ContractBinding>> = BTreeMap::new();
    let mut candidates_by_id: BTreeMap<String, Vec<Candidate>> = BTreeMap::new();
    let mut v2_cache: BTreeMap<(usize, String, String), Option<String>> = BTreeMap::new();
    let mut sources = Vec::new();
    for LabeledInput { label, input } in inputs {
        let kind = input.kind();
        let mut add_contract = |path: &str, binding: ContractBinding| {
            let id = item_id(path);
            let contract_key = format!("{kind}:{label}");
            items.entry(id.clone()).or_default().contracts.insert(contract_key.clone());
            item_contracts.entry(id).or_default().entry(contract_key).or_insert(binding);
        };
        match input {
            Input::Receipt(receipt) => {
                for path in &receipt.functions {
                    items.entry(item_id(path)).or_default();
                }
                let (tier, conditions) = match &receipt.discharge {
                    None => (None, BTreeSet::new()),
                    Some(Discharge::Proven(c)) if c.is_empty() => {
                        (Some(Tier::ProvenClosed), c.clone())
                    }
                    Some(Discharge::Proven(c)) => (Some(Tier::ProvenConditional), c.clone()),
                    Some(Discharge::Incomplete(r)) => (Some(Tier::Deferred), r.clone()),
                };
                if let Some(tier) = tier {
                    for path in &receipt.selected {
                        let id = item_id(path);
                        items.entry(id.clone()).or_default();
                        candidates_by_id.entry(id).or_default().push(Candidate {
                            tier,
                            conditions: conditions.clone(),
                            evidence: label.clone(),
                            request_sha256: receipt.request_sha256.clone(),
                            specification_manifest_sha256: receipt
                                .specification_manifest_sha256
                                .clone(),
                        });
                    }
                }
            }
            Input::Request(request) => {
                for path in &request.roots {
                    add_contract(path, ContractBinding::Request(request.request_sha256.clone()));
                }
                for (path, _) in &request.instantiated {
                    add_contract(path, ContractBinding::UnprovenGeneric);
                }
            }
            Input::Spec(spec_src) => {
                for path in spec_src.target_paths() {
                    let digests =
                        spec_src.digests_for_target(path, crate_name.as_deref(), &mut v2_cache);
                    add_contract(path, ContractBinding::Spec(digests));
                }
            }
        }
        let status = match input {
            Input::Receipt(r) => Some(r.status.clone()),
            _ => None,
        };
        sources.push(SourceInfo { kind, path: label.clone(), status });
    }
    // A request that lists an instantiation entry states a specification for
    // each instance that entry produces, bound to its `request_sha256` as for
    // a root. Receipts name the instances, so bind them here, after every
    // request has been read.
    for LabeledInput { input, .. } in inputs {
        let Input::Receipt(receipt) = input else { continue };
        for (instance, producers) in &receipt.instances {
            for LabeledInput { label, input } in inputs {
                let Input::Request(request) = input else { continue };
                if request.instantiated.iter().any(|inst| producers.contains(inst)) {
                    let id = item_id(instance);
                    let contract_key = format!("request:{label}");
                    items.entry(id.clone()).or_default().contracts.insert(contract_key.clone());
                    item_contracts.entry(id).or_default().entry(contract_key).or_insert_with(
                        || ContractBinding::Request(request.request_sha256.clone()),
                    );
                }
            }
        }
    }
    sources.sort();
    sources.dedup();

    for (id, entry) in &mut items {
        let candidates = candidates_by_id.remove(id).unwrap_or_default();
        let Some(contracts) = item_contracts.get(id) else {
            // Uncontracted census item (or instantiated body without an
            // item-level contract): pick the strongest single receipt.
            let mut best: Option<Candidate> = None;
            for cand in candidates {
                if best.as_ref().is_none_or(|cur| cand.beats(cur)) {
                    best = Some(cand);
                }
            }
            if let Some(best) = best {
                entry.tier = best.tier;
                entry.conditions = best.conditions;
                entry.evidence = Some(best.evidence);
            }
            continue;
        };

        // When one or more contracts are stated for this item, every contract
        // must be discharged by a verified receipt bound to that contract; if
        // any stated contract lacks a verified proof, the item stays
        // `Deferred`.
        entry.tier = Tier::Deferred;
        let mut all_proven = true;
        let mut weakest_proven: Option<Candidate> = None;
        let mut combined_conditions = BTreeSet::new();
        let mut incomplete_reasons = BTreeSet::new();
        let mut incomplete_evidence: Option<String> = None;
        for binding in contracts.values() {
            let mut contract_best: Option<Candidate> = None;
            for cand in candidates.iter().filter(|c| c.satisfies_contract(binding)) {
                if contract_best.as_ref().is_none_or(|cur| cand.beats(cur)) {
                    contract_best = Some(cand.clone());
                }
            }
            match contract_best {
                Some(best) if best.tier.is_proven() => {
                    combined_conditions.extend(best.conditions.iter().cloned());
                    if weakest_proven.as_ref().is_none_or(|cur| cur.beats(&best)) {
                        weakest_proven = Some(best);
                    }
                }
                Some(inc) => {
                    all_proven = false;
                    incomplete_reasons.extend(inc.conditions);
                    if incomplete_evidence.as_ref().is_none_or(|e| &inc.evidence < e) {
                        incomplete_evidence = Some(inc.evidence);
                    }
                }
                None => {
                    all_proven = false;
                }
            }
        }
        if all_proven {
            if let Some(weakest) = weakest_proven {
                entry.tier = if combined_conditions.is_empty() {
                    Tier::ProvenClosed
                } else {
                    Tier::ProvenConditional
                };
                entry.conditions = combined_conditions;
                entry.evidence = Some(weakest.evidence);
            }
        } else {
            entry.conditions = incomplete_reasons;
            entry.evidence = incomplete_evidence;
        }
    }
    if audit_assumptions {
        for entry in items.values_mut() {
            if entry.tier == Tier::ProvenConditional {
                entry.tier = Tier::Assumed;
            }
        }
    }
    Ok(Ledger { crate_name, audit_assumptions, sources, items })
}

impl Ledger {
    /// The number of items in `tier`.
    pub fn count(&self, tier: Tier) -> usize {
        self.items.values().filter(|e| e.tier == tier).count()
    }

    /// The number of items that are not proven.
    pub fn unproven(&self) -> usize {
        self.items.values().filter(|e| !e.tier.is_proven()).count()
    }

    /// Renders the ledger as [`SCHEMA`] JSON.
    pub fn to_json(&self) -> Value {
        let mut tiers = Map::new();
        for tier in Tier::ALL {
            tiers.insert(tier.name().into(), json!(self.count(tier)));
        }
        let sources: Vec<Value> = self
            .sources
            .iter()
            .map(|s| {
                let mut obj = Map::new();
                obj.insert("kind".into(), json!(s.kind));
                obj.insert("path".into(), json!(s.path));
                if let Some(status) = &s.status {
                    obj.insert("status".into(), json!(status));
                }
                Value::Object(obj)
            })
            .collect();
        let items: Vec<Value> = self
            .items
            .iter()
            .map(|(id, e)| {
                json!({
                    "id": id,
                    "tier": e.tier.name(),
                    "conditions": e.conditions,
                    "evidence": e.evidence,
                    "contracts": e.contracts,
                })
            })
            .collect();
        json!({
            "schema": SCHEMA,
            "crate": self.crate_name,
            "audit_assumptions": self.audit_assumptions,
            "sources": sources,
            "summary": {
                "items": self.items.len(),
                "unproven": self.unproven(),
                "tiers": tiers,
            },
            "items": items,
        })
    }

    /// Renders the ledger as text: one line per item, then a summary.
    pub fn to_text(&self) -> String {
        let mut out = String::new();
        for (id, e) in &self.items {
            out.push_str(&format!("{:<18}  {}", e.tier.name(), escape_controls(id)));
            if !e.conditions.is_empty() {
                let conditions: Vec<String> =
                    e.conditions.iter().map(|c| escape_controls(c)).collect();
                out.push_str(&format!("  [{}]", conditions.join(", ")));
            }
            out.push('\n');
        }
        if !self.items.is_empty() {
            out.push('\n');
        }
        if let Some(name) = &self.crate_name {
            out.push_str(&format!("crate: {}\n", escape_controls(name)));
        }
        if self.audit_assumptions {
            out.push_str("view: --audit-assumptions (conditional proofs count as assumed)\n");
        }
        out.push_str(&format!("{} items, {} unproven\n", self.items.len(), self.unproven()));
        for tier in Tier::ALL {
            out.push_str(&format!("  {:<18}  {}\n", tier.name(), self.count(tier)));
        }
        out
    }
}

/// A ledger read back from [`SCHEMA`] JSON for `--ratchet`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Baseline {
    pub crate_name: Option<String>,
    pub audit_assumptions: bool,
    /// Each item's tier and conditions. A hand-written baseline may omit
    /// `conditions`, which then default to none.
    pub items: BTreeMap<String, (Tier, BTreeSet<String>)>,
}

impl Baseline {
    /// Reads a baseline, recomputing its counts from its items rather than
    /// trusting its summary.
    pub fn from_json(value: &Value) -> Result<Baseline, String> {
        Baseline::parse(value).map_err(|e| escape_controls(&e))
    }

    fn parse(value: &Value) -> Result<Baseline, String> {
        let root = value.as_object().ok_or("baseline root must be a JSON object")?;
        if root.get("schema").and_then(Value::as_str) != Some(SCHEMA) {
            return Err(format!("baseline schema must be `{SCHEMA}`"));
        }
        let crate_name = match root.get("crate") {
            Some(Value::Null) => None,
            Some(Value::String(name)) => Some(name.clone()),
            _ => return Err("baseline `crate` must be a string or null".into()),
        };
        let audit_assumptions = bool_field(root, "audit_assumptions", "")?;
        let mut items = BTreeMap::new();
        for (i, item) in array_field(root, "items", "")?.iter().enumerate() {
            let ptr = format!("/items/{i}");
            let item = item.as_object().ok_or_else(|| format!("{ptr} must be an object"))?;
            let id = str_field(item, "id", &ptr)?;
            let name = str_field(item, "tier", &ptr)?;
            let tier = Tier::from_name(name)
                .ok_or_else(|| format!("{ptr}/tier: unrecognized tier `{name}`"))?;
            let conditions = match item.get("conditions") {
                None => BTreeSet::new(),
                Some(c) => value_str_array(c, &format!("{ptr}/conditions"))?.into_iter().collect(),
            };
            if items.insert(id.to_owned(), (tier, conditions)).is_some() {
                return Err(format!("baseline lists `{id}` twice"));
            }
        }
        Ok(Baseline { crate_name, audit_assumptions, items })
    }

    /// The number of items that are not proven.
    pub fn unproven(&self) -> usize {
        self.items.values().filter(|(t, _)| !t.is_proven()).count()
    }
}

/// Compares `current` with `baseline`, returning one finding per regression.
///
/// An item regresses when its tier falls, when a `proven_conditional` or
/// `assumed` item gains a condition, or when it disappears from the ledger,
/// since a missing receipt would otherwise make a proven item vanish
/// silently; regenerate the baseline after deleting a function. The total
/// number of unproven items may not grow. Ledgers for different crates or
/// different `--audit-assumptions` views are not comparable, which is an
/// error rather than a finding.
pub fn ratchet(baseline: &Baseline, current: &Ledger) -> Result<Vec<String>, String> {
    if baseline.audit_assumptions != current.audit_assumptions {
        return Err(format!(
            "baseline was built {} --audit-assumptions; build the ledger the same way",
            if baseline.audit_assumptions { "with" } else { "without" }
        ));
    }
    if baseline.crate_name != current.crate_name {
        return Err(format!(
            "baseline is for crate {}, but the ledger is for crate {}",
            describe_crate(&baseline.crate_name),
            describe_crate(&current.crate_name)
        ));
    }
    let mut findings = Vec::new();
    for (raw_id, (old, old_conditions)) in &baseline.items {
        let id = escape_controls(raw_id);
        let id = id.as_str();
        let Some(entry) = current.items.get(raw_id) else {
            findings.push(format!("missing: {id} (was {})", old.name()));
            continue;
        };
        if entry.tier < *old {
            findings.push(format!("regressed: {id}: {} -> {}", old.name(), entry.tier.name()));
        } else if entry.tier == *old && matches!(old, Tier::ProvenConditional | Tier::Assumed) {
            let added: Vec<String> =
                entry.conditions.difference(old_conditions).map(|c| escape_controls(c)).collect();
            if !added.is_empty() {
                findings.push(format!("weakened: {id}: new conditions [{}]", added.join(", ")));
            }
        }
    }
    let (old, new) = (baseline.unproven(), current.unproven());
    if new > old {
        findings.push(format!("unproven items increased: {old} -> {new}"));
    }
    Ok(findings)
}

fn describe_crate(name: &Option<String>) -> String {
    name.as_ref().map_or_else(|| "(none)".to_owned(), |n| format!("`{}`", escape_controls(n)))
}

fn item_id(path: &str) -> String {
    format!("{ID_PREFIX}{path}")
}

fn unify_crate(current: &mut Option<String>, found: &str, label: &str) -> Result<(), String> {
    match current {
        Some(name) if name != found => Err(escape_controls(&format!(
            "{label} is for crate `{found}`, but the ledger is for crate `{name}`"
        ))),
        Some(_) => Ok(()),
        None => {
            *current = Some(found.to_owned());
            Ok(())
        }
    }
}

fn field<'a>(obj: &'a Map<String, Value>, key: &str, ptr: &str) -> Result<&'a Value, String> {
    obj.get(key).ok_or_else(|| format!("missing {ptr}/{key}"))
}

fn str_field<'a>(obj: &'a Map<String, Value>, key: &str, ptr: &str) -> Result<&'a str, String> {
    field(obj, key, ptr)?.as_str().ok_or_else(|| format!("{ptr}/{key} must be a string"))
}

fn bool_field(obj: &Map<String, Value>, key: &str, ptr: &str) -> Result<bool, String> {
    field(obj, key, ptr)?.as_bool().ok_or_else(|| format!("{ptr}/{key} must be a boolean"))
}

fn obj_field<'a>(
    obj: &'a Map<String, Value>,
    key: &str,
    ptr: &str,
) -> Result<&'a Map<String, Value>, String> {
    field(obj, key, ptr)?.as_object().ok_or_else(|| format!("{ptr}/{key} must be an object"))
}

fn array_field<'a>(
    obj: &'a Map<String, Value>,
    key: &str,
    ptr: &str,
) -> Result<&'a Vec<Value>, String> {
    field(obj, key, ptr)?.as_array().ok_or_else(|| format!("{ptr}/{key} must be an array"))
}

fn u64_field(obj: &Map<String, Value>, key: &str, ptr: &str) -> Result<u64, String> {
    field(obj, key, ptr)?.as_u64().ok_or_else(|| format!("{ptr}/{key} must be an unsigned integer"))
}

fn value_str_array(value: &Value, ptr: &str) -> Result<Vec<String>, String> {
    value
        .as_array()
        .and_then(|a| a.iter().map(|v| v.as_str().map(str::to_owned)).collect::<Option<Vec<_>>>())
        .ok_or_else(|| format!("{ptr} must be an array of strings"))
}

/// Adds `<prefix>:<status>:<id>` for each entry of `obj`'s optional
/// `tcb_shims` array whose status is not `proved`.
fn shim_conditions(
    obj: &Map<String, Value>,
    ptr: &str,
    prefix: &str,
    conditions: &mut BTreeSet<String>,
) -> Result<(), String> {
    let Some(shims) = obj.get("tcb_shims") else {
        return Ok(());
    };
    let shims = shims.as_array().ok_or_else(|| format!("{ptr}/tcb_shims must be an array"))?;
    for (i, shim) in shims.iter().enumerate() {
        let ptr = format!("{ptr}/tcb_shims/{i}");
        let shim = shim.as_object().ok_or_else(|| format!("{ptr} must be an object"))?;
        let status = str_field(shim, "status", &ptr)?;
        if status != "proved" {
            let id = str_field(shim, "id", &ptr)?;
            conditions.insert(format!("{prefix}:{status}:{id}"));
        }
    }
    Ok(())
}

/// Adds `<label>:none` when `obj`'s optional `model_system_relation` has kind
/// `none`, which declares no relation between the model and the system.
fn relation_condition(
    obj: &Map<String, Value>,
    ptr: &str,
    label: &str,
    conditions: &mut BTreeSet<String>,
) -> Result<(), String> {
    let Some(relation) = obj.get("model_system_relation") else {
        return Ok(());
    };
    let ptr = format!("{ptr}/model_system_relation");
    let relation = relation.as_object().ok_or_else(|| format!("{ptr} must be an object"))?;
    if str_field(relation, "kind", &ptr)? == "none" {
        conditions.insert(format!("{label}:none"));
    }
    Ok(())
}

/// Escapes the control, line/paragraph-separator, and bidirectional-formatting
/// characters in `s`, an input string bound for human-readable output, so that
/// an input cannot forge output lines or send sequences to a terminal. JSON
/// output needs no such step.
pub fn escape_controls(s: &str) -> String {
    escape_chars(s, false)
}

/// Like [`escape_controls`], preserving `\n` line breaks between diagnostic
/// lines rendered by `anneal-spec-lower`.
fn escape_diagnostic_lines(s: &str) -> String {
    escape_chars(s, true)
}

fn escape_chars(s: &str, keep_lf: bool) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        if keep_lf && c == '\n' {
            out.push('\n');
            continue;
        }
        let unsafe_sep_or_bidi = matches!(
            c,
            '\u{061c}'
                | '\u{200e}'
                | '\u{200f}'
                | '\u{2028}'
                | '\u{2029}'
                | '\u{202a}'..='\u{202e}'
                | '\u{2066}'..='\u{2069}'
        );
        if c.is_control() || unsafe_sep_or_bidi {
            out.extend(c.escape_default());
        } else {
            out.push(c);
        }
    }
    out
}

fn str_array(obj: &Map<String, Value>, key: &str, ptr: &str) -> Result<Vec<String>, String> {
    array_field(obj, key, ptr)?
        .iter()
        .map(|v| v.as_str().map(str::to_owned))
        .collect::<Option<Vec<_>>>()
        .ok_or_else(|| format!("{ptr}/{key} must be an array of strings"))
}

#[cfg(test)]
mod tests;
