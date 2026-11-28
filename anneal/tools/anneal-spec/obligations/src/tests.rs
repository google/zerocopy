// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use serde_json::json;

use super::*;

/// A verified selected-unit Profile v1 receipt for crate `demo` whose census
/// has functions `a`, `b`, and `c`, a closure, a constant, and a bodiless
/// trait method, and which selects the functions in `selected`.
fn receipt_json(selected: &[&str]) -> Value {
    let census: Vec<Value> = [
        ("a", "Fn", true),
        ("b", "AssocFn", true),
        ("c", "Fn", true),
        ("a::{closure#0}", "Closure", true),
        ("K", "Const { is_type_const: false }", true),
        ("Tr::decl", "AssocFn", false),
    ]
    .iter()
    .enumerate()
    .map(|(i, (path, kind, has_body))| {
        json!({
            "def_id": i + 1,
            "path": path,
            "kind": kind,
            "has_body": has_body,
            "selected": selected.contains(path),
            "required": true,
        })
    })
    .collect();
    let roots_val: Vec<&str> = selected.to_vec();
    let selected: Vec<Value> =
        selected.iter().map(|p| json!({"def_id": def_id(p), "path": p, "body_index": 0})).collect();
    json!({
        "schema_version": 3,
        "status": "selected_unit_verified",
        "taint_reasons": [],
        "experimental": false,
        "elaboration_sandbox": "linux_bwrap",
        "spec_warnings": [],
        "scope": {"kind": "selected_unit", "roots": roots_val},
        "configuration": {"crate_name": "demo"},
        "correspondence_provenance": {"schema_version": 1},
        "census": census,
        "selected": selected,
        "audit": {
            "canonicalRoot": "Trusted.MirSemantics.UnitTheorem",
            "axioms": ["propext"],
            "sorryDeclarations": [],
            "replay": true,
            "exactType": true,
        },
    })
}

/// The census `def_id` of function `a`, `b`, or `c` in `receipt_json`.
fn def_id(path: &str) -> u64 {
    match path {
        "a" => 1,
        "b" => 2,
        "c" => 3,
        _ => panic!("no function `{path}`"),
    }
}

/// Turns `receipt_json(&["a", "b", "c"])` into a verified whole-crate
/// receipt. As in real whole-crate captures, every census entry is flagged
/// selected, but `selected` lists only the functions with bodies.
fn crate_receipt_json() -> Value {
    let mut r = receipt_json(&["a", "b", "c"]);
    r["status"] = json!("crate_verified");
    r["scope"] = json!({"kind": "crate"});
    r["audit"]["canonicalRoot"] = json!("Trusted.MirSemantics.CrateTheorem");
    for entry in r["census"].as_array_mut().unwrap() {
        entry["selected"] = json!(true);
    }
    r
}

/// Adds a generic function `g` (census `def_id` 7) to `receipt_json(&["a"])`
/// and selects the instances `g::<u8>` and `g::<u16>` through
/// `scope.instantiations`.
fn instantiated_receipt_json() -> Value {
    let mut r = receipt_json(&["a"]);
    r["census"].as_array_mut().unwrap().push(json!({
        "def_id": 7, "path": "g", "kind": "Fn", "has_body": true,
        "selected": false, "required": true,
    }));
    r["scope"]["instantiations"] =
        json!([{"path": "g", "args": ["u8"]}, {"path": "g", "args": ["u16"]}]);
    for inst in ["g::<u8>", "g::<u16>"] {
        r["selected"].as_array_mut().unwrap().push(json!({"def_id": 7, "path": inst}));
    }
    r
}

fn parse(value: &Value) -> Receipt {
    Receipt::from_json(value).unwrap()
}

fn conditions(receipt: &Receipt) -> Vec<String> {
    match &receipt.discharge {
        Some(Discharge::Proven(c)) => c.iter().cloned().collect(),
        other => panic!("expected a proven discharge, got {other:?}"),
    }
}

fn request(roots: &[&str]) -> Request {
    Request {
        crate_name: None,
        request_sha256: None,
        roots: roots.iter().map(|r| (*r).to_owned()).collect(),
        instantiated: vec![],
    }
}

fn spec(targets: &[&str]) -> Input {
    Input::Spec(SpecSource::targets(targets.iter().copied()))
}

fn input(label: &str, input: Input) -> LabeledInput {
    LabeledInput { label: label.into(), input }
}

fn tiers(ledger: &Ledger) -> Vec<(String, Tier)> {
    ledger.items.iter().map(|(id, e)| (id.clone(), e.tier)).collect()
}

#[test]
fn tiers_are_ordered_and_named_round_trip() {
    for pair in Tier::ALL.windows(2) {
        assert!(pair[0] < pair[1]);
    }
    for tier in Tier::ALL {
        assert_eq!(Tier::from_name(tier.name()), Some(tier));
    }
    assert_eq!(Tier::from_name("proven"), None);
    let proven: Vec<Tier> = Tier::ALL.into_iter().filter(|t| t.is_proven()).collect();
    assert_eq!(proven, [Tier::ProvenConditional, Tier::ProvenClosed]);
}

#[test]
fn receipt_tracks_only_functions_with_bodies() {
    let r = parse(&receipt_json(&["a"]));
    assert_eq!(r.crate_name.as_deref(), Some("demo"));
    assert_eq!(r.functions.iter().map(String::as_str).collect::<Vec<_>>(), ["a", "b", "c"]);
    assert_eq!(r.selected.iter().map(String::as_str).collect::<Vec<_>>(), ["a"]);
    assert_eq!(conditions(&r), ["selected_unit_scope"]);
}

#[test]
fn whole_crate_profile_v1_receipt_discloses_no_condition() {
    assert!(conditions(&parse(&crate_receipt_json())).is_empty());
}

#[test]
fn receipt_conditions_follow_disclosed_signals() {
    let mut r = crate_receipt_json();
    r["experimental"] = json!(true);
    assert_eq!(conditions(&parse(&r)), ["candidate_tier_model"]);

    let mut r = crate_receipt_json();
    r["audit"]["canonicalRoot"] = json!("Trusted.MirSemantics.CrateTheoremV2");
    assert_eq!(conditions(&parse(&r)), ["caller_memory_thread_isolation", "unbridged_semantics"]);

    // Profile v1 that leaves correspondence to a repository check discloses
    // it; Profile v2 already discloses unbridged semantics instead.
    let decoupled = json!({"applicable": false, "reason": "checked elsewhere"});
    let mut r = crate_receipt_json();
    r["correspondence_provenance"] = decoupled.clone();
    assert_eq!(conditions(&parse(&r)), ["correspondence_not_bound"]);
    r["audit"]["canonicalRoot"] = json!("Trusted.MirSemantics.CrateTheoremV2");
    assert_eq!(conditions(&parse(&r)), ["caller_memory_thread_isolation", "unbridged_semantics"]);

    let mut r = crate_receipt_json();
    r["status"] = json!("tainted_crate_verified");
    r["taint_reasons"] = json!(["unpinned_lean", "unsandboxed_elaboration"]);
    assert_eq!(conditions(&parse(&r)), ["taint:unpinned_lean", "taint:unsandboxed_elaboration"]);

    let mut r = crate_receipt_json();
    r["horizon"] = json!({"kind": "bounded", "k": 8});
    r["model_system_relation"] = json!({"kind": "none", "direction": "forward"});
    r["correspondence_provenance"] = json!({
        "tcb_shims": [
            {"id": "pin", "status": "proved"},
            {"id": "seam", "status": "assumed"},
        ],
        "taint_reasons": ["assumed_seams_present"],
    });
    assert_eq!(
        conditions(&parse(&r)),
        [
            "bounded_horizon:8",
            "correspondence_taint:assumed_seams_present",
            "correspondence_tcb_shim:assumed:seam",
            "model_system_relation:none",
        ]
    );
    r["horizon"] = json!({"kind": "unbounded"});
    r["model_system_relation"] = json!({"kind": "simulation", "direction": "forward"});
    r["correspondence_provenance"] = json!({});
    assert!(conditions(&parse(&r)).is_empty());

    let mut r = crate_receipt_json();
    r["tcb_shims"] = json!([
        {"id": "capture", "kind": "capture_driver", "status": "proved"},
        {"id": "seam", "kind": "assumed_seam", "status": "assumed"},
        {"id": "patch", "kind": "upstream_bugfix_patch", "status": "tested"},
    ]);
    assert_eq!(conditions(&parse(&r)), ["tcb_shim:assumed:seam", "tcb_shim:tested:patch"]);
}

#[test]
fn sorry_and_nonfoundation_axioms_make_a_proof_incomplete() {
    let mut r = crate_receipt_json();
    r["status"] = json!("tainted_crate_verified");
    r["taint_reasons"] = json!(["sorry_in_proof"]);
    let incomplete = |r: &Value| match parse(r).discharge {
        Some(Discharge::Incomplete(reasons)) => reasons.into_iter().collect::<Vec<_>>(),
        other => panic!("expected an incomplete discharge, got {other:?}"),
    };
    assert_eq!(incomplete(&r), ["sorry_in_proof"]);

    // A `sorryDeclarations` entry counts even without the taint.
    let mut r = crate_receipt_json();
    r["audit"]["sorryDeclarations"] = json!(["Proof.verify"]);
    assert_eq!(incomplete(&r), ["sorry_in_proof"]);

    let mut r = crate_receipt_json();
    r["sorry_declarations"] = json!(["Proof.helper"]);
    assert_eq!(incomplete(&r), ["sorry_in_proof"]);

    let mut r = crate_receipt_json();
    r["audit"]["axioms"] = json!(["propext", "sorryAx"]);
    assert_eq!(incomplete(&r), ["sorry_in_proof"]);

    let mut r = crate_receipt_json();
    r["audit"]["axioms"] = json!(["propext", "Proof.cheat"]);
    assert_eq!(incomplete(&r), ["nonfoundation_axiom:Proof.cheat"]);

    let mut r = crate_receipt_json();
    r["audit"]["replay"] = json!(false);
    r["audit"]["exactType"] = json!(false);
    assert_eq!(incomplete(&r), ["inexact_theorem_type", "no_kernel_replay"]);

    // A theorem the ledger does not know proves nothing it can interpret.
    let mut r = crate_receipt_json();
    r["audit"]["canonicalRoot"] = json!("Trusted.MirSemantics.SomethingElse");
    assert_eq!(incomplete(&r), ["unrecognized_canonical_root"]);
    let ledger = build(&[input("r.json", Input::Receipt(parse(&r)))], None, false).unwrap();
    assert_eq!(ledger.items["rust-path-v1::a"].tier, Tier::Deferred);
    assert_eq!(ledger.count(Tier::ProvenClosed), 0);
}

#[test]
fn canonical_root_must_match_scope() {
    for (mut r, root) in [
        (crate_receipt_json(), "Trusted.MirSemantics.UnitTheorem"),
        (crate_receipt_json(), "Trusted.MirSemantics.UnitTheoremV2"),
        (receipt_json(&["a"]), "Trusted.MirSemantics.CrateTheorem"),
        (receipt_json(&["a"]), "Trusted.MirSemantics.CrateTheoremV2"),
    ] {
        r["audit"]["canonicalRoot"] = json!(root);
        let err = Receipt::from_json(&r).unwrap_err();
        assert!(err.contains("disagrees with scope kind"), "{err}");
    }
    let mut r = receipt_json(&["a"]);
    r["audit"]["canonicalRoot"] = json!("Trusted.MirSemantics.UnitTheoremV2");
    assert_eq!(
        conditions(&parse(&r)),
        ["caller_memory_thread_isolation", "selected_unit_scope", "unbridged_semantics"]
    );
}

#[test]
fn correspondence_qualifiers_claim_and_relation_are_conditions() {
    // The shape of Pass 2 provenance (correspondence provenance schema v3).
    // A partial gate leaves `taint_reasons` empty.
    let provenance = |scope_kind: &str| {
        json!({
            "schema_version": 3,
            "claim_kind": "exact_refines",
            "model_system_relation": {
                "kind": "simulation",
                "qualifier": "lock_step",
                "direction": "bidirectional",
                "licensed_claim_shapes": ["forall_safety"],
            },
            "tcb_shims": [],
            "taint_reasons": [],
            "qualifiers": {"choice_total": true, "assumed_seams": [], "scope_kind": scope_kind},
        })
    };
    let with = |p: Value| {
        let mut r = crate_receipt_json();
        r["correspondence_provenance"] = p;
        r
    };
    let full = with(provenance("full_gate"));
    assert!(conditions(&parse(&full)).is_empty());
    let full = [input("full.json", Input::Receipt(parse(&full)))];
    let baseline = Baseline::from_json(&build(&full, None, false).unwrap().to_json()).unwrap();
    let closed_to_conditional =
        "regressed: rust-path-v1::a: proven_closed -> proven_conditional".to_owned();

    let partial = with(provenance("partial_gate"));
    assert_eq!(conditions(&parse(&partial)), ["correspondence_scope:partial_gate"]);
    let inputs = [input("partial.json", Input::Receipt(parse(&partial)))];
    let ledger = build(&inputs, None, false).unwrap();
    assert_eq!(ledger.items["rust-path-v1::a"].tier, Tier::ProvenConditional);
    assert_eq!(build(&inputs, None, true).unwrap().items["rust-path-v1::a"].tier, Tier::Assumed);
    assert!(ratchet(&baseline, &ledger).unwrap().contains(&closed_to_conditional));

    // Only `exact_refines` is unconditional.
    let mut p = provenance("full_gate");
    p["claim_kind"] = json!("sound_refines");
    p["model_system_relation"]["direction"] = json!("forward");
    let sound = with(p);
    assert_eq!(conditions(&parse(&sound)), ["correspondence_claim:sound_refines"]);
    let inputs = [input("sound.json", Input::Receipt(parse(&sound)))];
    let ledger = build(&inputs, None, false).unwrap();
    assert!(ratchet(&baseline, &ledger).unwrap().contains(&closed_to_conditional));

    // Qualifiers imply their taint atoms even if `taint_reasons` omits them.
    let mut p = provenance("full_gate");
    p["qualifiers"]["choice_total"] = json!(false);
    p["qualifiers"]["assumed_seams"] = json!(["seam"]);
    assert_eq!(
        conditions(&parse(&with(p))),
        ["correspondence_taint:assumed_seams_present", "correspondence_taint:choice_total_false"]
    );

    let mut p = provenance("full_gate");
    p["model_system_relation"] =
        json!({"kind": "none", "direction": "forward", "licensed_claim_shapes": []});
    assert_eq!(conditions(&parse(&with(p))), ["correspondence_model_system_relation:none"]);

    let mut p = provenance("full_gate");
    p["qualifiers"] = json!({"choice_total": true});
    let err = Receipt::from_json(&with(p)).unwrap_err();
    assert!(err.contains("/correspondence_provenance/qualifiers/scope_kind"), "{err}");
    let mut p = provenance("full_gate");
    p["claim_kind"] = json!(3);
    let err = Receipt::from_json(&with(p)).unwrap_err();
    assert!(err.contains("claim_kind must be a string"), "{err}");
}

#[test]
fn text_output_escapes_control_characters() {
    let hostile = "evil\nproven_closed       rust-path-v1::forged\u{1b}[2J\u{202e}\u{2028}\u{2029}";
    let ledger = build(&[input("s.rs", spec(&[hostile]))], None, false).unwrap();
    let text = ledger.to_text();
    assert!(
        !text.contains('\u{1b}')
            && !text.contains('\u{202e}')
            && !text.contains('\u{2028}')
            && !text.contains('\u{2029}'),
        "{text:?}"
    );
    assert!(text.starts_with(
        "deferred            rust-path-v1::evil\\nproven_closed       \
         rust-path-v1::forged\\u{1b}[2J\\u{202e}\\u{2028}\\u{2029}\n"
    ));
    // The JSON ledger keeps the string as is.
    let value = ledger.to_json();
    assert_eq!(value["items"][0]["id"], json!(format!("{ID_PREFIX}{hostile}")));

    let baseline = Baseline::from_json(&value).unwrap();
    let empty = build(&[input("s.rs", spec(&[]))], None, false).unwrap();
    let findings = ratchet(&baseline, &empty).unwrap();
    assert!(findings[0].starts_with("missing: rust-path-v1::evil\\nproven_closed"), "{findings:?}");

    let mut r = receipt_json(&["a"]);
    r["status"] = json!("bad\nstatus");
    let err = Receipt::from_json(&r).unwrap_err();
    assert!(err.contains("bad\\nstatus") && !err.contains('\n'), "{err}");

    let bad_spec = Source {
        label: "bad\u{1b}[31m\nname.rs".into(),
        text: "#[anneal::spec(unknown_clause(\"\u{1b}[2J\u{202e}\u{2028}\r\"))]\npub fn f() {}\n"
            .into(),
        module: vec![],
    };
    let diag = spec_inputs(&[bad_spec]).unwrap_err();
    assert!(
        !diag.contains('\u{1b}')
            && !diag.contains('\r')
            && !diag.contains('\u{202e}')
            && !diag.contains('\u{2028}')
            && !diag.contains('\u{2029}'),
        "{diag:?}"
    );
    assert!(diag.contains("\\u{1b}[2J") && diag.contains("bad\\u{1b}[31m\\nname.rs"), "{diag}");
}

#[test]
fn instances_are_separate_items() {
    let r = parse(&instantiated_receipt_json());
    assert_eq!(
        r.selected.iter().map(String::as_str).collect::<Vec<_>>(),
        ["a", "g::<u16>", "g::<u8>"]
    );
    let ledger = build(&[input("r.json", Input::Receipt(r))], None, false).unwrap();
    let tier = |id: &str| ledger.items[id].tier;
    assert_eq!(tier("rust-path-v1::g::<u8>"), Tier::ProvenConditional);
    assert_eq!(tier("rust-path-v1::g::<u16>"), Tier::ProvenConditional);
    assert_eq!(tier("rust-path-v1::g"), Tier::Uncontracted);

    // An instance is admitted only through `scope.instantiations`, and only
    // for a census function with a body.
    let mut r = instantiated_receipt_json();
    r["scope"].as_object_mut().unwrap().remove("instantiations");
    let err = Receipt::from_json(&r).unwrap_err();
    assert!(err.contains("neither a selected census function nor an instantiation"), "{err}");
    let mut r = crate_receipt_json();
    r["scope"]["instantiations"] = json!([]);
    let err = Receipt::from_json(&r).unwrap_err();
    assert!(err.contains("not allowed on a crate receipt"), "{err}");
    let mut r = instantiated_receipt_json();
    r["selected"][1]["def_id"] = json!(5);
    let err = Receipt::from_json(&r).unwrap_err();
    assert!(err.contains("def_id 5, which is not a census function"), "{err}");
}

const SHA_1: &str = "1111111111111111111111111111111111111111111111111111111111111111";
const SHA_2: &str = "2222222222222222222222222222222222222222222222222222222222222222";

/// A zero-argument `scope.instantiations` entry names a non-generic function,
/// which capture selects under its census path, `<impl ...>` and all. The
/// request covers it as it covers a root, bound to its `request_sha256`.
#[test]
fn zero_argument_instantiations_are_concrete_contracts() {
    let path = "m::_::<impl K for X<u8>>::f";
    let q = Request::from_json(&json!({
        "schema_version": 1,
        "compilation": {},
        "scope": {
            "kind": "selected_unit",
            "roots": ["a"],
            "instantiations": [
                {"path": path, "args": []},
                {"path": "a", "args": []},
                {"path": "g", "args": ["u8"]},
            ],
        },
    }))
    .unwrap();
    assert_eq!(q.roots, ["a", path]);
    assert_eq!(q.instantiated, [("g".to_owned(), vec!["u8".to_owned()])]);

    let receipt = |sha: &str| {
        let mut r = receipt_json(&["a"]);
        r["request_sha256"] = json!(sha);
        r["census"].as_array_mut().unwrap().push(json!({
            "def_id": 8, "path": path, "kind": "AssocFn", "has_body": true,
            "selected": false, "required": true,
        }));
        r["scope"]["instantiations"] = json!([{"path": path, "args": []}]);
        r["selected"].as_array_mut().unwrap().push(json!({"def_id": 8, "path": path}));
        parse(&r)
    };
    let r = receipt(SHA_1);
    assert!(r.selected.contains(path));
    assert!(r.instances.is_empty());

    let id = format!("rust-path-v1::{path}");
    let q = Request { request_sha256: Some(SHA_1.into()), ..q };
    let ledger = |r: Receipt| {
        build(
            &[input("r.json", Input::Receipt(r)), input("q.json", Input::Request(q.clone()))],
            None,
            false,
        )
        .unwrap()
    };
    let ok = ledger(receipt(SHA_1));
    assert_eq!(ok.items[&id].tier, Tier::ProvenConditional);
    assert_eq!(ok.items["rust-path-v1::a"].tier, Tier::ProvenConditional);
    assert!(ok.items[&id].contracts.contains("request:q.json"));
    // The generic function `g` stays deferred: the request covers only its
    // `u8` instance, which this receipt does not select.
    assert_eq!(ok.items["rust-path-v1::g"].tier, Tier::Deferred);
    // A receipt for another request does not discharge this one.
    let other = ledger(receipt(SHA_2));
    assert_eq!(other.items[&id].tier, Tier::Deferred);

    // The census path must match exactly, and some entry must name it.
    let mut r = receipt_json(&["a"]);
    r["census"].as_array_mut().unwrap().push(json!({
        "def_id": 8, "path": path, "kind": "AssocFn", "has_body": true,
        "selected": false, "required": true,
    }));
    r["scope"]["instantiations"] = json!([{"path": "m::_::<impl K for X<u16>>::f", "args": []}]);
    r["selected"].as_array_mut().unwrap().push(json!({"def_id": 8, "path": path}));
    let err = Receipt::from_json(&r).unwrap_err();
    assert!(err.contains("neither a selected census function nor an instantiation"), "{err}");
}

/// Generic arguments that contain `::` do not hide the callable's name.
#[test]
fn instance_paths_with_qualified_generic_arguments_match() {
    let census = "m::<impl Foo for T>::bar";
    for (selected, arg) in [
        ("m::<impl Foo for T>::bar::<core::cmp::Ordering>", "core::cmp::Ordering"),
        ("m::<impl Foo for T>::bar::<core::option::Option<u32>>", "core::option::Option<u32>"),
        ("m::<impl Foo for core::cmp::Ordering>::bar", "core::cmp::Ordering"),
    ] {
        let insts = [(census.to_owned(), vec![arg.to_owned()])];
        assert!(matches_instantiation(census, selected, &insts), "{selected}");
        // An entry for another callable does not produce it.
        let other = [("m::<impl Foo for T>::baz".to_owned(), vec![arg.to_owned()])];
        assert!(!matches_instantiation(census, selected, &other), "{selected}");
    }
    let insts = [(census.to_owned(), vec!["u8".to_owned()])];
    assert!(!matches_instantiation(census, "m::<impl Foo for T>", &insts));
    assert!(!matches_instantiation(census, "m::<impl Foo for T>::bar::<u8", &insts));
    // Non-empty generic arguments never match an uninstantiated selected path
    // (`selected_path == census_path`) on the same `def_id`.
    assert!(!matches_instantiation("g", "g", &[("g".into(), vec!["u8".into()])]));
    assert!(!matches_instantiation(census, census, &insts));
    // Cross-trait and cross-module `impl` paths sharing a method leaf never
    // match one another or an unrelated free function.
    assert!(!matches_instantiation(
        "mod_b::<impl TraitB for u8>::bar",
        "mod_b::<impl TraitB for u8>::bar",
        &[("other_mod::bar".into(), vec!["u8".into()])],
    ));
    assert!(!matches_instantiation(
        "mod_b::<impl TraitB for u8>::bar",
        "mod_b::<impl TraitB for u8>::bar::<u8>",
        &[("mod_a::<impl TraitA for T>::bar".into(), vec!["u8".into()])],
    ));
    assert!(!matches_instantiation(
        "m::<impl TraitA for T>::bar",
        "m::<impl TraitB for u8>::bar",
        &[("m::<impl TraitA for T>::bar".into(), vec!["u8".into()])],
    ));
    assert!(!matches_instantiation(
        "TraitB::<impl Foo>::bar",
        "TraitB::<impl Foo>::bar",
        &[("TraitB::bar".into(), vec!["Foo".into()])],
    ));
    assert!(!matches_instantiation(
        "mod_b::<impl mod_c::TraitA for u8>::bar",
        "mod_b::<impl mod_c::TraitA for u8>::bar",
        &[("mod_a::TraitA::bar".into(), vec!["u8".into()])],
    ));
    // Const `char` angle brackets and function-pointer arrows inside `<...>`
    // keep angle-group parsing balanced.
    assert!(matches_instantiation("ch", "ch::<'<'>", &[("ch".into(), vec!["'<'".into()])]));
    assert!(matches_instantiation("ch", "ch::<'>'>", &[("ch".into(), vec!["'>'".into()])]));
    assert!(matches_instantiation(
        "m::<impl KnownLayout for fn() -> T>::f",
        "m::<impl KnownLayout for fn() -> u8>::f",
        &[("m::<impl KnownLayout for fn() -> T>::f".into(), vec!["u8".into()])],
    ));
}

#[test]
fn non_empty_instantiation_rejects_uninstantiated_selected_entry_and_accepts_trait_dispatch() {
    // Malformed receipt: `g` (`selected: false`) cannot be accepted as proven
    // under its bare census path when `scope.instantiations` has non-empty
    // generic arguments.
    let mut bad = receipt_json(&["a"]);
    bad["census"].as_array_mut().unwrap().push(json!({
        "def_id": 7, "path": "g", "kind": "Fn", "has_body": true,
        "selected": false, "required": true,
    }));
    bad["scope"]["instantiations"] = json!([{"path": "g", "args": ["u8"]}]);
    bad["selected"].as_array_mut().unwrap().push(json!({"def_id": 7, "path": "g"}));
    let err = Receipt::from_json(&bad).unwrap_err();
    assert!(err.contains("neither a selected census function nor an instantiation"), "{err}");

    // Valid receipt: `StaticOnly::v` with `["&'static u8"]` dispatches through
    // `Instance::try_resolve` to concrete non-generic
    // `<&'static u8 as StaticOnly>::v`, whose `selected_path == census_path`.
    for impl_path in ["<&'static u8 as StaticOnly>::v", "_::<impl StaticOnly for &'static u8>::v"] {
        let make_rec = |sha: &str| {
            let mut r = receipt_json(&["a"]);
            r["request_sha256"] = json!(sha);
            r["census"].as_array_mut().unwrap().push(json!({
                "def_id": 8, "path": impl_path, "kind": "AssocFn", "has_body": true,
                "selected": false, "required": true,
            }));
            r["scope"]["instantiations"] =
                json!([{"path": "StaticOnly::v", "args": ["&'static u8"]}]);
            r["selected"].as_array_mut().unwrap().push(json!({"def_id": 8, "path": impl_path}));
            parse(&r)
        };
        let q = Request {
            crate_name: None,
            request_sha256: Some(SHA_1.into()),
            roots: vec!["a".into()],
            instantiated: vec![("StaticOnly::v".into(), vec!["&'static u8".into()])],
        };
        let id = format!("rust-path-v1::{impl_path}");
        let ok = build(
            &[
                input("r.json", Input::Receipt(make_rec(SHA_1))),
                input("q.json", Input::Request(q.clone())),
            ],
            None,
            false,
        )
        .unwrap();
        assert_eq!(ok.items[&id].tier, Tier::ProvenConditional, "{impl_path}");
        assert!(ok.items[&id].contracts.contains("request:q.json"), "{impl_path}");
        let wrong_sha = build(
            &[input("r.json", Input::Receipt(make_rec(SHA_2))), input("q.json", Input::Request(q))],
            None,
            false,
        )
        .unwrap();
        assert_eq!(wrong_sha.items[&id].tier, Tier::Deferred, "{impl_path}");
    }
}

/// A request that lists an instantiation entry states a specification for the
/// instances it produces, so they are bound to its `request_sha256` just as
/// roots are, and losing the receipt for one of two requests that list the
/// same instance is a regression.
#[test]
fn instances_are_bound_to_the_requests_that_list_them() {
    let receipt = |sha: &str| {
        let mut r = instantiated_receipt_json();
        r["request_sha256"] = json!(sha);
        parse(&r)
    };
    let request = |sha: &str, args: &[&str]| Request {
        crate_name: None,
        request_sha256: Some(sha.into()),
        roots: vec!["a".into()],
        instantiated: args.iter().map(|a| ("g".to_owned(), vec![(*a).to_owned()])).collect(),
    };
    let r1 = receipt(SHA_1);
    assert_eq!(
        r1.instances["g::<u8>"].iter().cloned().collect::<Vec<_>>(),
        [("g".to_owned(), vec!["u16".to_owned()]), ("g".to_owned(), vec!["u8".to_owned()])]
    );
    let tier = |inputs: &[LabeledInput], id: &str| {
        build(inputs, None, false).unwrap().items[&format!("rust-path-v1::{id}")].tier
    };
    let q1 = input("q1.json", Input::Request(request(SHA_1, &["u8", "u16"])));
    let q2 = input("q2.json", Input::Request(request(SHA_2, &["u8", "u16"])));
    let rec1 = input("r1.json", Input::Receipt(r1.clone()));
    let rec2 = input("r2.json", Input::Receipt(receipt(SHA_2)));

    let both = [rec1.clone(), q1.clone()];
    assert_eq!(tier(&both, "g::<u8>"), Tier::ProvenConditional);
    assert_eq!(tier(&both, "g"), Tier::Deferred);
    let ledger = build(&both, None, false).unwrap();
    assert!(ledger.items["rust-path-v1::g::<u8>"].contracts.contains("request:q1.json"));

    // A receipt produced from another request does not discharge `q1`.
    assert_eq!(tier(&[rec2.clone(), q1.clone()], "g::<u8>"), Tier::Deferred);

    // Two requests listing the same instance each need their own receipt.
    let full = build(&[rec1.clone(), rec2.clone(), q1.clone(), q2.clone()], None, false).unwrap();
    assert_eq!(full.items["rust-path-v1::g::<u8>"].tier, Tier::ProvenConditional);
    let lost = build(&[rec2.clone(), q1.clone(), q2.clone()], None, false).unwrap();
    assert_eq!(lost.items["rust-path-v1::g::<u8>"].tier, Tier::Deferred);
    let baseline = Baseline::from_json(&full.to_json()).unwrap();
    assert!(ratchet(&baseline, &lost)
        .unwrap()
        .contains(&"regressed: rust-path-v1::g::<u8>: proven_conditional -> deferred".to_owned()));

    // A request listing other instances states nothing about these.
    let q3 = input("q3.json", Input::Request(request(SHA_2, &["u32"])));
    assert_eq!(tier(&[rec1, q3], "g::<u8>"), Tier::ProvenConditional);
}

/// Anti-vacuity warnings do not block verification, so they, and a receipt
/// on which the lint did not run, are conditions that the ratchet notices.
#[test]
fn spec_warnings_are_conditions() {
    let warning = |code: &str| json!({"code": code, "declaration": "Spec.f", "message": "m"});
    let mut r = crate_receipt_json();
    r["spec_warnings"] = json!([warning("trivial_property")]);
    r["audit"]["specWarnings"] = json!([warning("unsatisfiable_safety")]);
    assert_eq!(
        conditions(&parse(&r)),
        ["spec_warning:trivial_property", "spec_warning:unsatisfiable_safety"]
    );

    let mut r = crate_receipt_json();
    r.as_object_mut().unwrap().remove("spec_warnings");
    assert_eq!(conditions(&parse(&r)), ["spec_lint_not_run"]);

    // A whole-crate proof that gains a warning falls from `proven_closed`.
    let closed =
        build(&[input("r.json", Input::Receipt(parse(&crate_receipt_json())))], None, false)
            .unwrap();
    assert_eq!(closed.items["rust-path-v1::a"].tier, Tier::ProvenClosed);
    let mut r = crate_receipt_json();
    r["spec_warnings"] = json!([warning("trivial_property")]);
    let warned = build(&[input("r.json", Input::Receipt(parse(&r)))], None, false).unwrap();
    assert_eq!(warned.items["rust-path-v1::a"].tier, Tier::ProvenConditional);
    let baseline = Baseline::from_json(&closed.to_json()).unwrap();
    assert!(!ratchet(&baseline, &warned).unwrap().is_empty());

    // A selected-unit proof that gains a warning gains a condition.
    let unit = build(&[input("r.json", Input::Receipt(parse(&receipt_json(&["a"]))))], None, false)
        .unwrap();
    let mut r = receipt_json(&["a"]);
    r["spec_warnings"] = json!([warning("trivial_property")]);
    let warned = build(&[input("r.json", Input::Receipt(parse(&r)))], None, false).unwrap();
    let baseline = Baseline::from_json(&unit.to_json()).unwrap();
    assert!(!ratchet(&baseline, &warned).unwrap().is_empty());

    for (field, bad, needle) in [
        ("spec_warnings", json!({}), "/spec_warnings must be an array"),
        ("spec_warnings", json!([1]), "/spec_warnings/0 must be an object"),
        ("spec_warnings", json!([{"code": ""}]), "/spec_warnings/0/code"),
        ("spec_warnings", json!([{}]), "/spec_warnings/0"),
    ] {
        let mut r = receipt_json(&["a"]);
        r[field] = bad;
        let err = Receipt::from_json(&r).unwrap_err();
        assert!(err.contains(needle), "{err}");
    }
    let mut r = receipt_json(&["a"]);
    r["audit"]["specWarnings"] = json!("x");
    let err = Receipt::from_json(&r).unwrap_err();
    assert!(err.contains("/audit/specWarnings must be an array"), "{err}");
}

#[test]
fn failure_receipt_contributes_no_functions() {
    let r = parse(&json!({
        "schema_version": 3,
        "status": "proof_failed",
        "taint_reasons": [],
        "phase": "proof",
    }));
    assert_eq!(r.discharge, None);
    assert!(r.functions.is_empty() && r.selected.is_empty());

    // A failed run records its relaxations in `taint_reasons`, but failure
    // statuses have no `tainted_` form.
    for (status, taint) in
        [("proof_failed", "unsandboxed_elaboration"), ("unsupported", "unpinned_lean")]
    {
        let r = parse(&json!({
            "schema_version": 3,
            "status": status,
            "taint_reasons": [taint],
        }));
        assert_eq!(r.status, status);
        assert_eq!(r.discharge, None);
        let ledger = build(&[input("f.json", Input::Receipt(r))], None, false).unwrap();
        assert!(ledger.items.is_empty());
    }
}

#[test]
fn inconsistent_receipts_are_rejected() {
    let reject = |r: Value, needle: &str| {
        let err = Receipt::from_json(&r).unwrap_err();
        assert!(err.contains(needle), "{err}");
    };
    let mut r = receipt_json(&["a"]);
    r["schema_version"] = json!(2);
    reject(r, "schema_version");

    let mut r = receipt_json(&["a"]);
    r["taint_reasons"] = json!(["unpinned_lean"]);
    reject(r, "disagrees with taint_reasons");

    let mut r = receipt_json(&["a"]);
    r["status"] = json!("tainted_selected_unit_verified");
    reject(r, "disagrees with taint_reasons");

    let mut r = receipt_json(&["a"]);
    r["status"] = json!("crate_verified");
    reject(r, "disagrees with scope kind");

    let mut r = receipt_json(&["a"]);
    r["selected"] = json!([{"def_id": 2, "path": "b"}]);
    reject(r, "neither a selected census function");

    let mut r = receipt_json(&["a"]);
    r["selected"] = json!([]);
    reject(r, "census `selected` flags");

    let mut r = receipt_json(&["a"]);
    r["audit"].as_object_mut().unwrap().remove("replay");
    reject(r, "replay");

    let mut r = receipt_json(&["a"]);
    r["status"] = json!("verified");
    reject(r, "unrecognized receipt status");

    let mut r = receipt_json(&["a"]);
    r["experimental"] = json!("no");
    reject(r, "experimental");

    let mut r = receipt_json(&["a"]);
    r["correspondence_provenance"] = json!({"applicable": "no"});
    reject(r, "applicable");

    let mut r = receipt_json(&["a"]);
    r.as_object_mut().unwrap().remove("correspondence_provenance");
    reject(r, "correspondence_provenance");

    let mut r = receipt_json(&["a"]);
    r["census"].as_array_mut().unwrap().push(json!({
        "def_id": 9, "path": "a", "kind": "Fn", "has_body": true,
        "selected": true, "required": true,
    }));
    reject(r, "twice");

    let mut r = receipt_json(&["a"]);
    r["census"].as_array_mut().unwrap().push(json!({
        "def_id": 1, "path": "d", "kind": "Fn", "has_body": true,
        "selected": false, "required": true,
    }));
    reject(r, "def_id 1 twice");

    // Selected-unit `scope.roots` and `scope.instantiations` must agree with
    // `census` and `selected`.
    let mut r = receipt_json(&["a", "b", "c"]);
    r["scope"] = json!({"kind": "selected_unit", "roots": ["a"]});
    reject(r, "/scope/roots");

    let mut r = receipt_json(&["a"]);
    r["scope"] = json!({"kind": "selected_unit"});
    reject(r, "/scope/roots");

    let r = receipt_json(&[]);
    reject(r, "at least one root or instantiation");

    let mut r = receipt_json(&["a"]);
    r["scope"]["instantiations"] = json!([1]);
    reject(r, "/scope/instantiations/0 must be an object");

    let mut r = instantiated_receipt_json();
    r["selected"].as_array_mut().unwrap().push(json!({"def_id": 2, "path": "b"}));
    reject(r, "neither a selected census function nor an instantiation");

    let mut r = instantiated_receipt_json();
    r["selected"][1] = json!({"def_id": 7, "path": "b"});
    reject(r, "neither a selected census function nor an instantiation");

    let mut r = instantiated_receipt_json();
    r["selected"][1] = json!({"def_id": 7, "path": "b::<u8>"});
    reject(r, "neither a selected census function nor an instantiation");

    let mut r = crate_receipt_json();
    r["scope"] = json!({"kind": "crate", "roots": ["a"]});
    reject(r, "not allowed on a crate receipt");

    let mut r = crate_receipt_json();
    r["census"][1]["selected"] = json!(false);
    reject(r, "leaves function `b` unselected");

    let mut r = receipt_json(&["a"]);
    r["request_sha256"] = json!("not-hex");
    reject(r, "request_sha256");
}

#[test]
fn unselected_duplicate_function_paths_are_merged() {
    let mut r = receipt_json(&["a"]);
    r["census"].as_array_mut().unwrap().push(json!({
        "def_id": 9, "path": "b", "kind": "Fn", "has_body": true,
        "selected": false, "required": true,
    }));
    assert_eq!(parse(&r).functions.len(), 3);
}

#[test]
fn request_roots_are_contracts() {
    let q = Request::from_json(&json!({
        "schema_version": 1,
        "compilation": {"crate_name": "demo"},
        "scope": {"kind": "selected_unit", "roots": ["b"]},
    }))
    .unwrap();
    assert_eq!(
        q,
        Request {
            crate_name: Some("demo".into()),
            request_sha256: None,
            roots: vec!["b".into()],
            instantiated: vec![],
        }
    );

    let q = Request::from_json(&json!({
        "schema_version": 1,
        "compilation": {},
        "scope": {
            "kind": "selected_unit",
            "roots": [],
            "instantiations": [{"path": "g", "args": ["u8"]}],
        },
    }))
    .unwrap();
    assert_eq!(q.instantiated, [("g".to_owned(), vec!["u8".to_owned()])]);
    assert!(q.roots.is_empty());

    let err = Request::from_json(&json!({
        "schema_version": 1,
        "compilation": {},
        "scope": {"kind": "crate", "instantiations": []},
    }))
    .unwrap_err();
    assert!(err.contains("not allowed on a crate request"), "{err}");

    let q = Request::from_json(&json!({
        "schema_version": 1,
        "compilation": {},
        "scope": {"kind": "crate"},
    }))
    .unwrap();
    assert_eq!(
        q,
        Request { crate_name: None, request_sha256: None, roots: vec![], instantiated: vec![] }
    );

    let err = Request::from_json(&json!({
        "schema_version": 1,
        "compilation": {},
        "scope": {"kind": "selected_unit", "roots": []},
    }))
    .unwrap_err();
    assert!(err.contains("at least one root or instantiation"), "{err}");
}

#[test]
fn spec_inputs_group_targets_by_file() {
    let sources = [
        Source {
            label: "lib.rs".into(),
            text: "#[cfg_attr(anneal, anneal::spec(ensures(|r| r == 0)))]\n\
                   pub fn zero() -> u8 { 0 }\n"
                .into(),
            module: vec![],
        },
        Source { label: "empty.rs".into(), text: "pub fn f() {}\n".into(), module: vec![] },
    ];
    let inputs = spec_inputs(&sources).unwrap();
    assert_eq!(inputs.len(), 2);
    assert_eq!(inputs[0].label, "lib.rs");
    assert_eq!(inputs[1].label, "empty.rs");
    let Input::Spec(s0) = &inputs[0].input else { panic!("expected spec") };
    let Input::Spec(s1) = &inputs[1].input else { panic!("expected spec") };
    assert_eq!(s0.target_paths(), ["zero"]);
    assert!(s1.target_paths().is_empty());
}

#[test]
fn build_assigns_one_tier_per_function() {
    let inputs = [
        input("r.json", Input::Receipt(parse(&receipt_json(&["a"])))),
        input("q.json", Input::Request(request(&["b"]))),
        input("s.rs", spec(&["spec_only"])),
    ];
    let ledger = build(&inputs, None, false).unwrap();
    assert_eq!(ledger.crate_name.as_deref(), Some("demo"));
    assert_eq!(
        tiers(&ledger),
        [
            ("rust-path-v1::a".to_owned(), Tier::ProvenConditional),
            ("rust-path-v1::b".to_owned(), Tier::Deferred),
            ("rust-path-v1::c".to_owned(), Tier::Uncontracted),
            ("rust-path-v1::spec_only".to_owned(), Tier::Deferred),
        ]
    );
    let a = &ledger.items["rust-path-v1::a"];
    assert_eq!(a.evidence.as_deref(), Some("r.json"));
    assert!(a.contracts.is_empty());
    let b = &ledger.items["rust-path-v1::b"];
    assert_eq!(b.contracts.iter().map(String::as_str).collect::<Vec<_>>(), ["request:q.json"]);
    assert_eq!(ledger.unproven(), 3);
    assert_eq!(
        ledger.sources.iter().map(|s| (s.kind, s.path.as_str())).collect::<Vec<_>>(),
        [("receipt", "r.json"), ("request", "q.json"), ("spec", "s.rs")]
    );
}

#[test]
fn build_prefers_the_strongest_single_receipt() {
    let unit = parse(&receipt_json(&["a"]));
    let whole = parse(&crate_receipt_json());
    let mut sorry = crate_receipt_json();
    sorry["audit"]["sorryDeclarations"] = json!(["Proof.verify"]);
    let sorry = parse(&sorry);
    for order in [[0, 1, 2], [2, 1, 0], [1, 2, 0]] {
        let all = [
            input("unit.json", Input::Receipt(unit.clone())),
            input("whole.json", Input::Receipt(whole.clone())),
            input("sorry.json", Input::Receipt(sorry.clone())),
        ];
        let inputs: Vec<LabeledInput> = order.iter().map(|&i| all[i].clone()).collect();
        let ledger = build(&inputs, None, false).unwrap();
        let a = &ledger.items["rust-path-v1::a"];
        assert_eq!(a.tier, Tier::ProvenClosed);
        assert_eq!(a.evidence.as_deref(), Some("whole.json"));
    }

    // With only an incomplete proof, the function keeps its specification
    // and records why the proof does not count.
    let ledger = build(&[input("sorry.json", Input::Receipt(sorry))], None, false).unwrap();
    let a = &ledger.items["rust-path-v1::a"];
    assert_eq!(a.tier, Tier::Deferred);
    assert_eq!(a.conditions.iter().map(String::as_str).collect::<Vec<_>>(), ["sorry_in_proof"]);
}

#[test]
fn conditions_from_different_receipts_are_never_combined() {
    let mut v2 = crate_receipt_json();
    v2["audit"]["canonicalRoot"] = json!("Trusted.MirSemantics.CrateTheoremV2");
    let inputs = [
        input("unit.json", Input::Receipt(parse(&receipt_json(&["a"])))),
        input("v2.json", Input::Receipt(parse(&v2))),
    ];
    let a = &build(&inputs, None, false).unwrap().items["rust-path-v1::a"];
    assert_eq!(a.tier, Tier::ProvenConditional);
    assert_eq!(a.evidence.as_deref(), Some("unit.json"));
    assert_eq!(
        a.conditions.iter().map(String::as_str).collect::<Vec<_>>(),
        ["selected_unit_scope"]
    );
}

#[test]
fn audit_assumptions_reports_conditional_proofs_as_assumed() {
    let inputs = [
        input("unit.json", Input::Receipt(parse(&receipt_json(&["a"])))),
        input("q.json", Input::Request(request(&["b"]))),
    ];
    let ledger = build(&inputs, None, true).unwrap();
    assert_eq!(ledger.items["rust-path-v1::a"].tier, Tier::Assumed);
    assert_eq!(ledger.items["rust-path-v1::b"].tier, Tier::Deferred);
    assert_eq!(ledger.unproven(), 3);

    let closed = [input("whole.json", Input::Receipt(parse(&crate_receipt_json())))];
    let ledger = build(&closed, None, true).unwrap();
    assert_eq!(ledger.count(Tier::ProvenClosed), 3);
}

#[test]
fn build_reports_each_source_once() {
    let r = parse(&receipt_json(&["a"]));
    let inputs = [input("r.json", Input::Receipt(r.clone())), input("r.json", Input::Receipt(r))];
    assert_eq!(build(&inputs, None, false).unwrap().sources.len(), 1);
}

#[test]
fn build_rejects_mixed_crates() {
    let other = Request { crate_name: Some("other".into()), ..request(&["x"]) };
    let err = build(
        &[
            input("r.json", Input::Receipt(parse(&receipt_json(&["a"])))),
            input("q.json", Input::Request(other)),
        ],
        None,
        false,
    )
    .unwrap_err();
    assert!(err.contains("q.json is for crate `other`"), "{err}");

    let err =
        build(&[input("r.json", Input::Receipt(parse(&receipt_json(&["a"]))))], Some("x"), false)
            .unwrap_err();
    assert!(err.contains("r.json is for crate `demo`"), "{err}");
}

#[test]
fn json_round_trips_through_baseline() {
    let inputs = [
        input("r.json", Input::Receipt(parse(&receipt_json(&["a"])))),
        input("q.json", Input::Request(request(&["b"]))),
    ];
    let ledger = build(&inputs, None, false).unwrap();
    let value = ledger.to_json();
    assert_eq!(value["summary"]["items"], json!(3));
    assert_eq!(value["summary"]["unproven"], json!(2));
    assert_eq!(value["summary"]["tiers"]["proven_conditional"], json!(1));
    assert_eq!(value["summary"]["tiers"]["checked_fuzz"], json!(0));
    let baseline = Baseline::from_json(&value).unwrap();
    assert_eq!(baseline.crate_name.as_deref(), Some("demo"));
    assert_eq!(baseline.items.len(), 3);
    assert_eq!(
        baseline.items["rust-path-v1::a"],
        (Tier::ProvenConditional, BTreeSet::from(["selected_unit_scope".to_owned()]))
    );
    assert_eq!(baseline.unproven(), 2);
    assert_eq!(ratchet(&baseline, &ledger).unwrap(), Vec::<String>::new());
}

#[test]
fn baseline_rejects_malformed_documents() {
    let ledger =
        build(&[input("r.json", Input::Receipt(parse(&receipt_json(&["a"]))))], None, false)
            .unwrap();
    let reject = |value: Value, needle: &str| {
        let err = Baseline::from_json(&value).unwrap_err();
        assert!(err.contains(needle), "{err}");
    };
    let mut v = ledger.to_json();
    v["schema"] = json!("anneal-obligations/0");
    reject(v, "schema");
    let mut v = ledger.to_json();
    v["items"][0]["tier"] = json!("proven");
    reject(v, "unrecognized tier");
    let mut v = ledger.to_json();
    let first = v["items"][0].clone();
    v["items"].as_array_mut().unwrap().push(first);
    reject(v, "twice");
}

#[test]
fn ratchet_reports_regressions_missing_items_and_growth() {
    let proven = build(
        &[
            input("whole.json", Input::Receipt(parse(&crate_receipt_json()))),
            input("s.rs", spec(&["extra"])),
        ],
        None,
        false,
    )
    .unwrap();
    let baseline = Baseline::from_json(&proven.to_json()).unwrap();
    let weaker = build(
        &[
            input("unit.json", Input::Receipt(parse(&receipt_json(&["a"])))),
            input("q.json", Input::Request(request(&["b"]))),
        ],
        None,
        false,
    )
    .unwrap();
    assert_eq!(
        ratchet(&baseline, &weaker).unwrap(),
        [
            "regressed: rust-path-v1::a: proven_closed -> proven_conditional",
            "regressed: rust-path-v1::b: proven_closed -> deferred",
            "regressed: rust-path-v1::c: proven_closed -> uncontracted",
            "missing: rust-path-v1::extra (was deferred)",
            "unproven items increased: 1 -> 2",
        ]
    );

    // Growth alone fails too: a new uncontracted function is no regression
    // of an existing item but still adds an unproven obligation.
    let small = build(&[input("s.rs", spec(&["a"]))], None, false).unwrap();
    let baseline = Baseline::from_json(&small.to_json()).unwrap();
    let grown = build(&[input("s.rs", spec(&["a", "b"]))], None, false).unwrap();
    assert_eq!(ratchet(&baseline, &grown).unwrap(), ["unproven items increased: 1 -> 2"]);

    // A conditional proof that gains a condition is weaker evidence at the
    // same tier.
    let unit = [input("unit.json", Input::Receipt(parse(&receipt_json(&["a"]))))];
    let baseline = Baseline::from_json(&build(&unit, None, false).unwrap().to_json()).unwrap();
    let mut tainted = receipt_json(&["a"]);
    tainted["status"] = json!("tainted_selected_unit_verified");
    tainted["taint_reasons"] = json!(["unpinned_lean"]);
    let tainted = [input("tainted.json", Input::Receipt(parse(&tainted)))];
    assert_eq!(
        ratchet(&baseline, &build(&tainted, None, false).unwrap()).unwrap(),
        ["weakened: rust-path-v1::a: new conditions [taint:unpinned_lean]"]
    );
}

#[test]
fn ratchet_refuses_incomparable_ledgers() {
    let inputs = [input("r.json", Input::Receipt(parse(&receipt_json(&["a"]))))];
    let plain = build(&inputs, None, false).unwrap();
    let audit = build(&inputs, None, true).unwrap();
    let baseline = Baseline::from_json(&plain.to_json()).unwrap();
    let err = ratchet(&baseline, &audit).unwrap_err();
    assert!(err.contains("without --audit-assumptions"), "{err}");

    let spec_only = build(&[input("s.rs", spec(&["a"]))], None, false).unwrap();
    let err = ratchet(&baseline, &spec_only).unwrap_err();
    assert!(err.contains("crate `demo`"), "{err}");
}

#[test]
fn overlapping_contracts_require_matching_receipts_and_ratchet_catches_loss() {
    let req_json = |spec_decl: &str, spec_mod: &str, spec_path: &str| {
        json!({
            "schema_version": 1,
            "compilation": {
                "source_root": ".",
                "crate_root": "lib.rs",
                "crate_name": "demo",
                "source_files": ["lib.rs"],
            },
            "scope": {"kind": "selected_unit", "roots": ["a"]},
            "proof": {
                "source_root": ".",
                "specification": spec_decl,
                "theorem": "Proof.verify",
                "sources": [
                    {"module": spec_mod, "path": spec_path, "role": "specification"},
                    {"module": "Proof", "path": "Proof.lean", "role": "proof"},
                ],
            },
        })
    };
    let src_v1 = [Source {
        label: "lib.rs".into(),
        text: "#[cfg_attr(anneal, anneal::spec(claim = \"c_a\", ensures(|r| r == 0)))]\n\
               pub fn a() -> u8 { 0 }\n"
            .into(),
        module: vec![],
    }];
    let spec_in = spec_inputs(&src_v1).unwrap().into_iter().next().unwrap();
    let lowered_v2 = anneal_spec_lower::lower_with(
        &src_v1,
        &anneal_spec_lower::Options {
            targets: vec![],
            claim: Some("c_a".into()),
            format: anneal_spec_lower::Format::V2Module,
            crate_slug: Some("demo".into()),
        },
    )
    .ok()
    .unwrap();
    let spec_sha_03 =
        binding::single_module_spec_manifest_sha256("Specs.demo.c_a", &lowered_v2.spec_lean);
    let spec_sha_04 = binding::single_module_spec_manifest_sha256("Spec", "-- other spec\n");

    let q03 = Request::from_json(&req_json(
        "Specs.demo.c_a.specs",
        "Specs.demo.c_a",
        "Specs/demo/c_a.lean",
    ))
    .unwrap();
    let q04 = Request::from_json(&req_json("Spec.specs", "Spec", "Spec.lean")).unwrap();
    assert_ne!(q03.request_sha256, q04.request_sha256);

    let mut r03_json = receipt_json(&["a"]);
    r03_json["request_sha256"] = json!(q03.request_sha256.clone().unwrap());
    r03_json["specification_manifest_sha256"] = json!(spec_sha_03);
    let mut r04_json = receipt_json(&["a"]);
    r04_json["request_sha256"] = json!(q04.request_sha256.clone().unwrap());
    r04_json["specification_manifest_sha256"] = json!(spec_sha_04);

    // Both units verified: `a`'s two requests and inline spec are all proven.
    let full = build(
        &[
            input("r03.json", Input::Receipt(parse(&r03_json))),
            input("r04.json", Input::Receipt(parse(&r04_json))),
            input("q03.json", Input::Request(q03.clone())),
            input("q04.json", Input::Request(q04.clone())),
            spec_in.clone(),
        ],
        None,
        false,
    )
    .unwrap();
    assert_eq!(full.items["rust-path-v1::a"].tier, Tier::ProvenConditional);
    let baseline = Baseline::from_json(&full.to_json()).unwrap();

    // Omitting `r03.json` while `r04.json` still verifies leaves `q03` and
    // `spec:lib.rs` unproven, so `a` drops to `deferred` and `--ratchet` fails.
    let missing_r03 = build(
        &[
            input("r04.json", Input::Receipt(parse(&r04_json))),
            input("q03.json", Input::Request(q03.clone())),
            input("q04.json", Input::Request(q04.clone())),
            spec_in.clone(),
        ],
        None,
        false,
    )
    .unwrap();
    assert_eq!(missing_r03.items["rust-path-v1::a"].tier, Tier::Deferred);
    assert!(ratchet(&baseline, &missing_r03)
        .unwrap()
        .contains(&"regressed: rust-path-v1::a: proven_conditional -> deferred".to_owned()));

    // Making `r03` sorry-tainted likewise leaves `a` deferred with
    // `sorry_in_proof`.
    let mut r03_sorry = r03_json.clone();
    r03_sorry["audit"]["sorryDeclarations"] = json!(["Proof.verify"]);
    let tainted_r03 = build(
        &[
            input("r03.json", Input::Receipt(parse(&r03_sorry))),
            input("r04.json", Input::Receipt(parse(&r04_json))),
            input("q03.json", Input::Request(q03.clone())),
            input("q04.json", Input::Request(q04.clone())),
            spec_in,
        ],
        None,
        false,
    )
    .unwrap();
    assert_eq!(tainted_r03.items["rust-path-v1::a"].tier, Tier::Deferred);
    assert!(tainted_r03.items["rust-path-v1::a"].conditions.contains("sorry_in_proof"));
    assert!(!ratchet(&baseline, &tainted_r03).unwrap().is_empty());

    // Strengthening the inline spec invalidates `r03`'s
    // `specification_manifest_sha256`.
    let strengthened = [Source {
        label: "lib.rs".into(),
        text: "#[cfg_attr(anneal, anneal::spec(claim = \"c_a\", ensures(|r| r == 1)))]\n\
               pub fn a() -> u8 { 0 }\n"
            .into(),
        module: vec![],
    }];
    let strengthened_in = spec_inputs(&strengthened).unwrap().into_iter().next().unwrap();
    let stale_spec = build(
        &[
            input("r03.json", Input::Receipt(parse(&r03_json))),
            input("r04.json", Input::Receipt(parse(&r04_json))),
            input("q03.json", Input::Request(q03)),
            input("q04.json", Input::Request(q04)),
            strengthened_in,
        ],
        None,
        false,
    )
    .unwrap();
    assert_eq!(stale_spec.items["rust-path-v1::a"].tier, Tier::Deferred);
    assert!(!ratchet(&baseline, &stale_spec).unwrap().is_empty());
}

#[test]
fn text_lists_items_then_summary() {
    let inputs = [input("r.json", Input::Receipt(parse(&receipt_json(&["a"]))))];
    let text = build(&inputs, None, true).unwrap().to_text();
    let expected = "\
assumed             rust-path-v1::a  [selected_unit_scope]
uncontracted        rust-path-v1::b
uncontracted        rust-path-v1::c

crate: demo
view: --audit-assumptions (conditional proofs count as assumed)
3 items, 3 unproven
  uncontracted        2
  deferred            0
  assumed             1
  runtime_checked     0
  checked_fuzz        0
  envelope_minted     0
  proven_conditional  0
  proven_closed       0
";
    assert_eq!(text, expected);
}
