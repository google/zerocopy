// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use std::{fs, path::Path, process::Command};

use anneal_spec_lower::{
    closure::parse_capture_json, lower, lower_with, module_path, Format, Lowered, Options, Scope,
    Source,
};

fn src(label: &str, text: &str) -> Source {
    Source { label: label.into(), text: text.into(), module: Vec::new() }
}

fn lower_one(text: &str) -> Result<Lowered, Vec<(String, String)>> {
    let sources = [src("spec.rs", text)];
    lower(&sources).map_err(|errs| {
        errs.iter().map(|e| (e.diag.code.to_string(), e.render(&sources))).collect()
    })
}

fn expect_error(text: &str, code: &str) -> String {
    match lower_one(text) {
        Ok(l) => panic!("expected {code}, but lowering succeeded:\n{}", l.spec_lean),
        Err(errs) => {
            let found = errs.iter().find(|(c, _)| c == code);
            found.unwrap_or_else(|| panic!("expected {code}, got {errs:?}")).1.clone()
        }
    }
}

fn wrap(attr: &str, sig: &str) -> String {
    format!("anneal::external_spec! {{ #[anneal::spec({attr})] {sig}; }}")
}

/// The external form of the step-bounded `<usize as PointerMetadata>`
/// specification that `zerocopy/src/lib.rs` writes inline.
const USIZE_MAX_STEPS_SPEC: &str = "anneal::external_spec! {
    impl PointerMetadata for usize {
        #[anneal::spec(terminates, no_panic, max_steps = 2, ensures(|ret| ret == elems))]
        fn from_elem_count(elems: usize) -> Self;

        #[anneal::spec(terminates, no_panic, max_steps = 2, ensures(|count| count == self))]
        fn to_elem_count(self) -> usize;
    }
}
";

#[test]
fn max_steps_zerocopy_unit_matches_checked_in_golden_and_cli_check() {
    let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../../zerocopy/src");
    let unit = src.join("../proofs/01_usize_pointer_metadata");
    let claim = "zc01_usize_pointer_metadata";
    let sources = [Source {
        label: "lib.rs".into(),
        text: fs::read_to_string(src.join("lib.rs")).unwrap(),
        module: module_path("lib.rs"),
    }];
    let opts = Options {
        claim: Some(claim.into()),
        format: Format::V2Module,
        crate_slug: Some("zerocopy".into()),
        ..Options::default()
    };
    let l = lower_with(&sources, &opts).unwrap_or_else(|e| panic!("{}", e[0].render(&sources)));
    let golden = fs::read_to_string(unit.join(format!("Specs/zerocopy/{claim}.lean"))).unwrap();
    assert_eq!(l.spec_lean, golden);
    assert_eq!(l.spec_closure, fs::read_to_string(unit.join("spec-closure.golden")).unwrap());
    assert!(
        golden.contains(
            "entrySatisfiesStepBoundV1 _p__anneal fn0_id fn0_sig fn0_contract fn0_max_steps"
        ),
        "{golden}"
    );
    assert!(
        golden.contains(
            "entrySatisfiesStepBoundV1 _p__anneal fn1_id fn1_sig fn1_contract fn1_max_steps"
        ),
        "{golden}"
    );

    let bin = env!("CARGO_BIN_EXE_anneal-spec-lower");
    let status = Command::new(bin)
        .arg("--src-root")
        .arg(&src)
        .args(["--format", "v2-module", "--crate-slug", "zerocopy", "--claim", claim])
        .arg("--check")
        .arg(&unit)
        .arg("lib.rs")
        .status()
        .unwrap();
    assert!(status.success(), "{claim}: --check failed");
}

#[test]
fn inline_and_external_max_steps_lower_to_identical_spec_lean() {
    let external = USIZE_MAX_STEPS_SPEC;
    let inline = r#"
pub trait PointerMetadata { fn from_elem_count(elems: usize) -> Self; fn to_elem_count(self) -> usize; }

impl PointerMetadata for usize {
    #[cfg_attr(anneal, anneal::spec(terminates, no_panic, max_steps = 2, ensures(|ret| ret == elems)))]
    fn from_elem_count(elems: usize) -> usize {
        elems
    }

    #[cfg_attr(anneal, anneal::spec(terminates, no_panic, max_steps = 2, ensures(|count| count == self)))]
    fn to_elem_count(self) -> usize {
        self
    }
}
"#;
    let a = lower_one(external).unwrap();
    let b = lower(&[Source {
        label: "lib.rs".into(),
        text: inline.into(),
        module: module_path("lib.rs"),
    }])
    .unwrap_or_else(|_| panic!("inline max_steps form failed"));
    assert_eq!(a.spec_lean, b.spec_lean);
}

#[test]
fn max_steps_emits_tactic_free_nat_rec_and_honest_caveat() {
    let l = lower_one(&wrap(
        "terminates, no_panic, max_steps = 34 * len + 540, ensures(|r| r == len)",
        "fn scan(len: usize) -> usize",
    ))
    .unwrap();
    assert!(l.spec_lean.contains("noncomputable def reachesDoneWithin"), "{}", l.spec_lean);
    assert!(l.spec_lean.contains("@Nat.rec (fun _ => State → Prop)"), "{}", l.spec_lean);
    assert!(l.spec_lean.contains("not physical wall-clock time"), "{}", l.spec_lean);
    assert!(!l.spec_lean.contains(":= by"), "unexpected tactic block in:\n{}", l.spec_lean);
    assert!(
        l.spec_lean.contains(
            "noncomputable def fn0_max_steps (_q__anneal : Query) : Nat :=\n  (((34 : Nat) * (specNat (specArg _q__anneal 0))) + (540 : Nat))"
        ),
        "{}",
        l.spec_lean
    );
    assert!(
        l.spec_lean.contains(
            "entrySatisfiesStepBoundV1 _p__anneal fn0_id fn0_sig fn0_contract fn0_max_steps"
        ),
        "{}",
        l.spec_lean
    );

    // `math(...)` wrapper inside `max_steps` lowers identically to the bare
    // mathematical expression.
    let l_math = lower_one(&wrap(
        "terminates, no_panic, max_steps = math(34 * len + 540), ensures(|r| r == len)",
        "fn scan(len: usize) -> usize",
    ))
    .unwrap();
    assert_eq!(l.spec_lean, l_math.spec_lean);
}

#[test]
fn constant_max_steps_uses_wildcard_query_binder() {
    // Anti-vacuity `unused_spec_binding` rejects unused named `q` binders in
    // `Spec.lean`.
    let l = lower_one(&wrap("max_steps = 10", "fn constant_work()")).unwrap();
    assert!(
        l.spec_lean.contains(
            "noncomputable def fn0_max_steps (_q__anneal : Query) : Nat :=\n  (10 : Nat)"
        ),
        "{}",
        l.spec_lean
    );
    assert!(!l.spec_lean.contains("def specNat"), "{}", l.spec_lean);
    assert!(!l.spec_lean.contains("def specArg"), "{}", l.spec_lean);
    assert!(
        l.spec_lean
            .contains("effects := { terminates := true, noUnwind := true, noAbort := true }"),
        "{}",
        l.spec_lean
    );
}

#[test]
fn max_steps_supports_guarded_div_mod_helpers_and_may_panic() {
    let l = lower_one(
        "anneal::external_spec! {
            #[anneal::pure] fn extra(x: u16) -> u16 { wrapping_add(x, 4u16) }
            #[anneal::spec(
                requires(d > 0usize),
                max_steps = n / d + n % (2usize) + extra(k) + wrapping_mul(k, 2u16),
            )]
            fn chunked(n: usize, d: usize, k: u16);
        }",
    )
    .unwrap();
    assert!(
        l.spec_lean.contains(
            "(Nat.div (specNat (specArg _q__anneal 0)) (specNat (specArg _q__anneal 1)))"
        ),
        "{}",
        l.spec_lean
    );
    assert!(
        l.spec_lean.contains("(Nat.mod (specNat (specArg _q__anneal 0)) (2 : Nat))"),
        "{}",
        l.spec_lean
    );
    assert!(
        l.spec_lean.contains("(Int.toNat (Spec.pure_extra (specInt (specArg _q__anneal 2))))"),
        "{}",
        l.spec_lean
    );

    // `may_panic` + `max_steps` on `-> !` bounds MIR steps to unwind (while
    // `.aborted` remains False).
    let panic_sink = lower_one(&wrap("may_panic, max_steps = 16", "fn fail_fast() -> !")).unwrap();
    assert!(
        panic_sink
            .spec_lean
            .contains("effects := { terminates := true, noUnwind := false, noAbort := true }"),
        "{}",
        panic_sink.spec_lean
    );
}

#[test]
fn max_steps_span_map_records_exact_clause_span() {
    let text = "anneal::external_spec! { #[anneal::spec(total, max_steps = 34 * n + 540)] fn f(n: usize); }";
    let l = lower_one(text).unwrap();
    let map: serde_json::Value = serde_json::from_str(&l.span_map).unwrap();
    let entry = map["entries"]
        .as_array()
        .unwrap()
        .iter()
        .find(|e| e["lean_decl"] == "Spec.fn0_max_steps")
        .expect("Spec.fn0_max_steps entry");
    let b0 = entry["rust"]["start_byte"].as_u64().unwrap() as usize;
    let b1 = entry["rust"]["end_byte"].as_u64().unwrap() as usize;
    assert_eq!(&text[b0..b1], "max_steps = 34 * n + 540");
}

#[test]
fn max_steps_doc_comments_stay_within_80_columns() {
    let name = "long_function_name_that_forces_doc_wrapping_";
    let l = lower_one(&wrap("max_steps = 42", &format!("fn {name}()"))).unwrap();
    let mut in_doc = false;
    for line in l.spec_lean.lines() {
        in_doc |= line.starts_with("/--");
        if in_doc {
            assert!(line.chars().count() <= 80, "line > 80 cols: {line}");
        }
        in_doc &= !line.ends_with("-/");
    }
}

#[test]
fn max_steps_rejects_invalid_and_negative_forms_fail_closed() {
    // Conflict with `may_diverge` in either order, plus `terminates` +
    // `may_diverge` + `max_steps`.
    expect_error(&wrap("may_diverge, max_steps = 10", "fn f()"), "E_ANNEAL_CONFLICTING_EFFECTS");
    expect_error(&wrap("max_steps = 10, may_diverge", "fn f()"), "E_ANNEAL_CONFLICTING_EFFECTS");
    expect_error(
        &wrap("terminates, may_diverge, max_steps = 10", "fn f()"),
        "E_ANNEAL_CONFLICTING_EFFECTS",
    );

    // Duplicate and malformed `max_steps` clauses.
    expect_error(&wrap("max_steps = 5, max_steps = 10", "fn f()"), "E_ANNEAL_DUPLICATE_CLAUSE");
    expect_error(&wrap("max_steps", "fn f()"), "E_ANNEAL_SPEC_SYNTAX");
    expect_error(&wrap("max_steps(10)", "fn f()"), "E_ANNEAL_SPEC_SYNTAX");
    expect_error(&wrap("max_steps =", "fn f()"), "E_ANNEAL_SPEC_SYNTAX");

    // Negative literals, signed suffixes, signed parameters, signed helpers,
    // and subtraction.
    expect_error(&wrap("max_steps = -1", "fn f()"), "E_ANNEAL_SPEC_TYPE_MISMATCH");
    expect_error(&wrap("max_steps = math(-1)", "fn f()"), "E_ANNEAL_SPEC_TYPE_MISMATCH");
    expect_error(&wrap("max_steps = 5i32", "fn f()"), "E_ANNEAL_SPEC_TYPE_MISMATCH");
    expect_error(&wrap("max_steps = -5i32", "fn f()"), "E_ANNEAL_SPEC_TYPE_MISMATCH");
    expect_error(&wrap("max_steps = x", "fn f(x: i32)"), "E_ANNEAL_SPEC_TYPE_MISMATCH");
    expect_error(
        &wrap("max_steps = math(x) + 10", "fn f(x: isize)"),
        "E_ANNEAL_SPEC_TYPE_MISMATCH",
    );
    expect_error(
        &wrap("max_steps = a - b", "fn f(a: usize, b: usize)"),
        "E_ANNEAL_SPEC_TYPE_MISMATCH",
    );
    expect_error(&wrap("max_steps = 10 - 1", "fn f()"), "E_ANNEAL_SPEC_TYPE_MISMATCH");
    expect_error(
        "anneal::external_spec! {
            #[anneal::pure] fn signed_h(x: u8) -> i16 { 1i16 }
            #[anneal::spec(max_steps = signed_h(x))] fn f(x: u8);
        }",
        "E_ANNEAL_SPEC_TYPE_MISMATCH",
    );
    expect_error(
        &wrap("max_steps = wrapping_add(a, 1i8)", "fn f(a: i8)"),
        "E_ANNEAL_SPEC_TYPE_MISMATCH",
    );

    // Non-integer expressions.
    expect_error(&wrap("max_steps = true", "fn f()"), "E_ANNEAL_SPEC_TYPE_MISMATCH");
    expect_error(&wrap("max_steps = ()", "fn f()"), "E_ANNEAL_SPEC_TYPE_MISMATCH");
    expect_error(&wrap("max_steps = !flag", "fn f(flag: bool)"), "E_ANNEAL_SPEC_TYPE_MISMATCH");
    expect_error(&wrap("max_steps = a == b", "fn f(a: u8, b: u8)"), "E_ANNEAL_SPEC_TYPE_MISMATCH");
    expect_error(
        &wrap("max_steps = a < b < c", "fn f(a: u8, b: u8, c: u8)"),
        "E_ANNEAL_CHAINED_COMPARISON",
    );
    expect_error(&wrap("max_steps = a & 1u8", "fn f(a: u8)"), "E_ANNEAL_UNSUPPORTED_BITWISE");

    // Division guards, `safety_requires` non-leakage, `old(...)`,
    // unknown/return binders, and literal range.
    expect_error(
        &wrap("max_steps = n / d", "fn f(n: usize, d: usize)"),
        "E_ANNEAL_UNGUARDED_SPEC_DIV",
    );
    expect_error(
        &wrap("safety_requires(d != 0usize), max_steps = n / d", "unsafe fn f(n: usize, d: usize)"),
        "E_ANNEAL_UNGUARDED_SPEC_DIV",
    );
    expect_error(&wrap("max_steps = old(n)", "fn f(n: usize)"), "E_ANNEAL_OLD_IN_PRECONDITION");
    let ret_msg =
        expect_error(&wrap("max_steps = ret", "fn f() -> usize"), "E_ANNEAL_SPEC_UNKNOWN_IDENT");
    assert!(ret_msg.contains("ensures"), "{ret_msg}");
    expect_error(&wrap("max_steps = 256u8", "fn f()"), "E_ANNEAL_SPEC_LITERAL_RANGE");
}

#[test]
fn profile_v2_capture_emits_entry_satisfies_step_bound_v2() {
    let text =
        "anneal::external_spec! { #[anneal::spec(max_steps = n + 4)] fn step_v2(n: usize); }";
    let cap_json = serde_json::json!({
        "program": {
            "scope": "unit",
            "mir_profile_version": 2,
            "bodies": [{
                "identity": "rust-path-v1::step_v2",
                "is_unsafe": false,
                "arg_count": 1,
                "local_tys": [
                    {"kind": "int", "width": "isize", "signed": false},
                    {"kind": "int", "width": "isize", "signed": false}
                ]
            }]
        }
    })
    .to_string();
    let cap = parse_capture_json(&cap_json).unwrap();
    let sources = [src("spec.rs", text)];
    let l = match lower_with(
        &sources,
        &Options { scope: Scope::Unit, capture: Some(cap.clone()), ..Options::default() },
    ) {
        Ok(l) => l,
        Err(errs) => panic!("expected Ok, got {}", errs[0].diag.code),
    };
    assert!(l.spec_lean.contains("def reachesDoneWithinV2"), "{}", l.spec_lean);
    assert!(l.spec_lean.contains("StepV2 _p__anneal"), "{}", l.spec_lean);
    assert!(l.spec_lean.contains("def entrySatisfiesStepBoundV2"), "{}", l.spec_lean);
    assert!(l.spec_lean.contains("ValidEntryArgsV2 _body__anneal _q__anneal"), "{}", l.spec_lean);
    assert!(l.spec_lean.contains("initStateV2"), "{}", l.spec_lean);
    assert!(
        l.spec_lean.contains(
            "entrySatisfiesStepBoundV2 _p__anneal fn0_id fn0_sig fn0_contract fn0_max_steps"
        ),
        "{}",
        l.spec_lean
    );
    assert!(!l.spec_lean.contains("entrySatisfiesStepBoundV1"), "{}", l.spec_lean);

    // Conflicting `Options::scope` and `capture.scope` fails closed in library
    // calls too.
    let Err(conflict) = lower_with(
        &sources,
        &Options { scope: Scope::Crate, capture: Some(cap), ..Options::default() },
    ) else {
        panic!("scope mismatch must fail");
    };
    assert_eq!(conflict[0].diag.code, "E_ANNEAL_INVALID_OPTIONS");
}
