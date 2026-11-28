// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use std::{fs, path::Path, process::Command};

use anneal_spec_lower::{
    ast::mangle_slug, list_targets, lower, lower_with, module_path, Format, Lowered, Options,
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

/// The external form of unit 01's specification, kept here so that tests of
/// lowering behavior do not depend on which form the unit itself uses.
const USIZE_POINTER_METADATA_SPEC: &str = "anneal::external_spec! {
    impl PointerMetadata for usize {
        #[anneal::spec(total, ensures(|ret| ret == elems))]
        fn from_elem_count(elems: usize) -> Self;

        #[anneal::spec(total, ensures(|count| count == self))]
        fn to_elem_count(self) -> usize;
    }
}
";

/// The `zerocopy` source root, from which inline specifications lower.
fn zerocopy_src() -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../../zerocopy/src")
}

/// A claim-bound `zerocopy/proofs` unit: its directory, the `zerocopy/src`
/// files its `spec_sources.json` names, and its claim.
struct ClaimUnit {
    dir: std::path::PathBuf,
    files: Vec<String>,
    claim: String,
}

impl ClaimUnit {
    fn module(&self) -> std::path::PathBuf {
        self.dir.join(format!("Specs/zerocopy/{}.lean", self.claim))
    }
}

fn claim_units() -> Vec<ClaimUnit> {
    let proofs = zerocopy_src().join("../proofs");
    let mut units: Vec<_> = fs::read_dir(&proofs)
        .unwrap()
        .filter_map(|e| {
            let dir = e.unwrap().path();
            let json = fs::read_to_string(dir.join("spec_sources.json")).ok()?;
            let v: serde_json::Value = serde_json::from_str(&json).unwrap();
            let files =
                v["files"].as_array().unwrap().iter().map(|f| f.as_str().unwrap().into()).collect();
            Some(ClaimUnit { dir, files, claim: v["claim"].as_str().unwrap().into() })
        })
        .collect();
    units.sort_by(|a, b| a.dir.cmp(&b.dir));
    units
}

#[test]
fn zerocopy_units_match_checked_in_goldens() {
    let units = claim_units();
    // `__unsafe`, `add_scaled_metadata`, and the two `PointerMetadata` impls.
    assert!(units.len() >= 4, "found {} claim-bound units", units.len());
    for unit in &units {
        let sources: Vec<Source> = unit
            .files
            .iter()
            .map(|f| Source {
                label: f.clone(),
                text: fs::read_to_string(zerocopy_src().join(f)).unwrap(),
                module: module_path(f),
            })
            .collect();
        let opts = Options {
            claim: Some(unit.claim.clone()),
            format: Format::V2Module,
            crate_slug: Some("zerocopy".into()),
            ..Options::default()
        };
        let l = lower_with(&sources, &opts)
            .unwrap_or_else(|e| panic!("{}: {}", unit.claim, e[0].render(&sources)));
        assert_eq!(l.spec_lean, fs::read_to_string(unit.module()).unwrap(), "{}", unit.claim);
    }
}

#[test]
fn cli_check_accepts_goldens_and_rejects_stale_output() {
    let bin = env!("CARGO_BIN_EXE_anneal-spec-lower");
    let check = |unit: &ClaimUnit, dir: &Path| {
        Command::new(bin)
            .arg("--src-root")
            .arg(zerocopy_src())
            .args(["--format", "v2-module", "--crate-slug", "zerocopy", "--claim", &unit.claim])
            .arg("--check")
            .arg(dir)
            .args(&unit.files)
            .output()
            .unwrap()
    };
    let units = claim_units();
    for unit in &units {
        let out = check(unit, &unit.dir);
        assert!(out.status.success(), "{}: --check failed; regenerate with --out-dir", unit.claim);
    }
    let tmp = std::env::temp_dir().join(format!("anneal-spec-stale-{}", std::process::id()));
    fs::create_dir_all(tmp.join("Specs/zerocopy")).unwrap();
    fs::write(tmp.join(format!("Specs/zerocopy/{}.lean", units[0].claim)), "stale").unwrap();
    let out = check(&units[0], &tmp);
    fs::remove_dir_all(&tmp).unwrap();
    assert_eq!(out.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&out.stderr).contains("is stale"));
}

#[test]
fn cli_v1_out_dir_and_check_round_trip() {
    let bin = env!("CARGO_BIN_EXE_anneal-spec-lower");
    let tmp = std::env::temp_dir().join(format!("anneal-spec-v1-{}", std::process::id()));
    let out = tmp.join("out");
    fs::create_dir_all(&tmp).unwrap();
    fs::write(tmp.join("spec.rs"), USIZE_POINTER_METADATA_SPEC).unwrap();
    let run = |mode: &str| {
        Command::new(bin)
            .arg("--src-root")
            .arg(&tmp)
            .arg(mode)
            .arg(&out)
            .arg("spec.rs")
            .output()
            .unwrap()
    };
    assert!(run("--out-dir").status.success());
    assert!(out.join("Spec.lean").is_file() && out.join("spec_span_map.json").is_file());
    assert!(run("--check").status.success());
    fs::write(out.join("spec_span_map.json"), "{}").unwrap();
    let stale = run("--check");
    fs::remove_dir_all(&tmp).unwrap();
    assert_eq!(stale.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&stale.stderr).contains("spec_span_map.json is stale"));
}

#[test]
fn inline_and_external_forms_lower_to_identical_spec_lean() {
    let external = USIZE_POINTER_METADATA_SPEC;
    let inline = r#"
pub trait PointerMetadata { fn from_elem_count(elems: usize) -> Self; fn to_elem_count(self) -> usize; }

impl PointerMetadata for usize {
    #[inline]
    #[cfg_attr(anneal, anneal::spec(total, ensures(|ret| ret == elems)))]
    fn from_elem_count(elems: usize) -> usize {
        elems
    }

    #[cfg_attr(anneal, anneal::spec(total, ensures(|count| count == self)))]
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
    .unwrap_or_else(|_| panic!("inline form failed"));
    assert_eq!(a.spec_lean, b.spec_lean);
}

#[test]
fn lowering_is_independent_of_item_order() {
    let a = "anneal::external_spec! { \
        #[anneal::spec(ensures(|r| r == x))] fn b(x: u8) -> u8; \
        #[anneal::spec(ensures(|r| r == x))] fn a(x: u8) -> u8; }";
    let b = "anneal::external_spec! { \
        #[anneal::spec(ensures(|r| r == x))] fn a(x: u8) -> u8; \
        #[anneal::spec(ensures(|r| r == x))] fn b(x: u8) -> u8; }";
    assert_eq!(lower_one(a).unwrap().spec_lean, lower_one(b).unwrap().spec_lean);
}

#[test]
fn module_paths_follow_rust_file_layout() {
    assert_eq!(module_path("lib.rs"), Vec::<String>::new());
    assert_eq!(module_path("util/macros.rs"), vec!["util", "macros"]);
    assert_eq!(module_path("pointer/mod.rs"), vec!["pointer"]);
}

#[test]
fn inline_items_take_their_file_module_path() {
    let sources = [Source {
        label: "util/macros.rs".into(),
        text:
            "#[cfg_attr(anneal, anneal::spec(total))]\npub(crate) const unsafe fn __unsafe() {}\n"
                .into(),
        module: module_path("util/macros.rs"),
    }];
    let l = lower(&sources).unwrap_or_else(|_| panic!("lowering failed"));
    assert!(l.spec_lean.contains("\"rust-path-v1::util::macros::__unsafe\""), "{}", l.spec_lean);
}

#[test]
fn requires_on_safe_fn_restricts_behavior_but_never_excuses_ub() {
    let safe =
        lower_one(&wrap("requires(x > 0u8), ensures(|r| r == x)", "fn f(x: u8) -> u8")).unwrap();
    assert!(safe.spec_lean.contains("behaviorPre := fn0_pre"), "{}", safe.spec_lean);
    assert!(!safe.spec_lean.contains("safetyPre"), "{}", safe.spec_lean);

    let unsafe_ = lower_one(&wrap("requires(x > 0u8)", "unsafe fn f(x: u8) -> u8")).unwrap();
    assert!(unsafe_.spec_lean.contains("safetyPre := fn0_safety"), "{}", unsafe_.spec_lean);
    assert!(unsafe_.spec_lean.contains("behaviorPre := fn0_pre"), "{}", unsafe_.spec_lean);

    let split = lower_one(&wrap(
        "safety_requires(x != 0u8), requires(x < 9u8)",
        "unsafe fn f(x: u8) -> u8",
    ))
    .unwrap();
    assert!(
        split.spec_lean.contains(
            "def fn0_safety (q : Query) : Prop :=\n  (((specInt (specArg q 0)) ≠ (0 : Int)) ∧ ((specInt (specArg q 0)) < (9 : Int)))"
        ),
        "{}",
        split.spec_lean
    );
    expect_error(
        &wrap("safety_requires(x != 0u8)", "fn f(x: u8)"),
        "E_ANNEAL_SAFETY_REQUIRES_ON_SAFE_FN",
    );
}

#[test]
fn effect_qualifiers_set_the_effect_mask() {
    let mask = |attr: &str| {
        let l = lower_one(&wrap(attr, "fn f()")).unwrap();
        l.spec_lean.lines().find(|l| l.contains("effects :=")).unwrap().trim().to_string()
    };
    assert_eq!(mask("ensures(|_| true)"), "effects := { terminates := true, noUnwind := true }");
    assert_eq!(mask("total"), "effects := { terminates := true, noUnwind := true }");
    assert_eq!(mask("no_panic"), "effects := { terminates := true, noUnwind := true }");
    assert_eq!(mask("no_unwind"), "effects := { terminates := true, noUnwind := true }");
    assert_eq!(mask("terminates"), "effects := { terminates := true, noUnwind := true }");
    assert_eq!(mask("may_diverge"), "effects := { terminates := false, noUnwind := true }");
    assert_eq!(mask("may_unwind"), "effects := { terminates := true, noUnwind := false }");
    assert_eq!(mask("may_panic"), "effects := { terminates := true, noUnwind := false }");
    assert_eq!(
        mask("may_diverge, may_unwind"),
        "effects := { terminates := false, noUnwind := false }"
    );
    expect_error(&wrap("may_diverge, terminates", "fn f()"), "E_ANNEAL_CONFLICTING_EFFECTS");
    expect_error(&wrap("may_diverge, total", "fn f()"), "E_ANNEAL_CONFLICTING_EFFECTS");
    expect_error(&wrap("may_unwind, no_unwind", "fn f()"), "E_ANNEAL_CONFLICTING_EFFECTS");
    expect_error(&wrap("total, may_unwind", "fn f()"), "E_ANNEAL_CONFLICTING_EFFECTS");
    expect_error(&wrap("no_panic, may_panic", "fn f()"), "E_ANNEAL_CONFLICTING_EFFECTS");
    expect_error(&wrap("no_abort", "fn f()"), "E_ANNEAL_UNSUPPORTED_CLAUSE");

    // Never-return (`-> !`) functions: reject bare specs with no precondition
    // or effect opt-out, while admitting `may_panic`, `may_diverge`, and
    // guarded contracts such as `safety_requires(false)`.
    expect_error(
        &wrap("ensures(false)", "fn bad_never() -> !"),
        "E_ANNEAL_UNSATISFIABLE_NEVER_EFFECTS",
    );
    expect_error(
        &wrap("may_panic, ensures(|r| true)", "fn bad_ret_binder() -> !"),
        "E_ANNEAL_UNSUPPORTED_TYPE",
    );
    assert_eq!(
        lower_one(&wrap("may_panic", "fn panic_sink() -> !"))
            .unwrap()
            .spec_lean
            .lines()
            .find(|l| l.contains("effects :="))
            .unwrap()
            .trim(),
        "effects := { terminates := true, noUnwind := false }"
    );
    assert_eq!(
        lower_one(&wrap("may_diverge", "fn spin() -> !"))
            .unwrap()
            .spec_lean
            .lines()
            .find(|l| l.contains("effects :="))
            .unwrap()
            .trim(),
        "effects := { terminates := false, noUnwind := true }"
    );
    lower_one(&wrap("safety_requires(false)", "unsafe fn unreachable() -> !")).unwrap();
}

#[test]
fn vacuous_ok_waives_inhabitation_and_requires_a_reason() {
    let l = lower_one(
        "anneal::external_spec! { #[anneal::vacuous_ok(reason = \"intentionally empty domain\")] \
         #[anneal::spec(requires(false))] fn f(); }",
    )
    .unwrap();
    assert!(l.spec_lean.contains("-- vacuous_ok: intentionally empty domain"), "{}", l.spec_lean);
    assert!(l.spec_lean.contains("requireInhabited := false"), "{}", l.spec_lean);
    expect_error(
        "anneal::external_spec! { #[anneal::vacuous_ok(reason = \"\")] #[anneal::spec(total)] fn f(); }",
        "E_ANNEAL_VACUOUS_OK_REASON",
    );
}

#[test]
fn pure_helpers_lower_in_call_order_and_reject_recursion() {
    let l = lower_one(
        "anneal::external_spec! {
            #[anneal::pure] fn outer(x: u32, y: u32) -> bool { inner(x) && inner(y) }
            #[anneal::pure] fn inner(x: u32) -> bool { x != 0u32 }
            #[anneal::spec(requires(outer(a, b)))] fn f(a: u32, b: u32);
        }",
    )
    .unwrap();
    let inner = l.spec_lean.find("def pure_inner").unwrap();
    let outer = l.spec_lean.find("def pure_outer").unwrap();
    assert!(inner < outer, "{}", l.spec_lean);
    assert!(l
        .spec_lean
        .contains("(Spec.pure_outer (specInt (specArg q 0)) (specInt (specArg q 1)))"));
    expect_error(
        "anneal::external_spec! {
            #[anneal::pure] fn a(x: u8) -> bool { b(x) }
            #[anneal::pure] fn b(x: u8) -> bool { a(x) }
            #[anneal::spec(requires(a(v)))] fn f(v: u8);
        }",
        "E_ANNEAL_PURE_RECURSION",
    );
}

#[test]
fn arithmetic_requires_an_explicit_meaning() {
    let r = expect_error(
        &wrap("ensures(|r| r == a + b)", "fn f(a: usize, b: usize) -> usize"),
        "E_ANNEAL_AMBIGUOUS_SPEC_ARITH",
    );
    assert!(r.contains("math(a) + math(b)"), "{r}");
    let l = lower_one(&wrap(
        "ensures(|r| math(r) == math(a) + math(b))",
        "fn f(a: usize, b: usize) -> usize",
    ))
    .unwrap();
    assert!(l
        .spec_lean
        .contains("((specInt out.ret) = ((specInt (specArg q 0)) + (specInt (specArg q 1))))"));
    let w = lower_one(&wrap("ensures(|r| r == wrapping_add(a, b))", "fn f(a: u8, b: u8) -> u8"))
        .unwrap();
    assert!(
        w.spec_lean.contains("(Trusted.MirSemantics.intEmod ((specInt (specArg q 0)) + (specInt (specArg q 1))) 256)"),
        "{}",
        w.spec_lean
    );
    let s = lower_one(&wrap("ensures(|r| r == wrapping_sub(a, b))", "fn f(a: i8, b: i8) -> i8"))
        .unwrap();
    assert!(
        s.spec_lean.contains(
            "(Trusted.MirSemantics.intEmod ((specInt (specArg q 0)) - (specInt (specArg q 1)) + 128) 256 - 128)"
        ),
        "{}",
        s.spec_lean
    );
    let o = lower_one(&wrap("requires(no_overflow_mul(a, b))", "fn f(a: u16, b: u16)")).unwrap();
    assert!(o.spec_lean.contains("((0 : Int) ≤ (specInt (specArg q 0)) * (specInt (specArg q 1)) ∧ (specInt (specArg q 0)) * (specInt (specArg q 1)) < 65536)"), "{}", o.spec_lean);
}

#[test]
fn division_needs_a_nonzero_guard() {
    expect_error(
        &wrap("ensures(|r| math(r) == math(a / b))", "fn f(a: u8, b: u8) -> u8"),
        "E_ANNEAL_UNGUARDED_SPEC_DIV",
    );
    let l = lower_one(&wrap(
        "ensures(|r| b != 0u8 ==> math(r) == math(a / b))",
        "fn f(a: u8, b: u8) -> u8",
    ))
    .unwrap();
    assert!(
        l.spec_lean.contains(
            "(Trusted.MirSemantics.intTdiv (specInt (specArg q 0)) (specInt (specArg q 1)))"
        ),
        "{}",
        l.spec_lean
    );
    lower_one(&wrap(
        "requires(b > 0u8), ensures(|r| math(r) == math(a % b))",
        "fn f(a: u8, b: u8) -> u8",
    ))
    .unwrap();
    lower_one(&wrap("ensures(|r| math(r) == math(a / 2))", "fn f(a: u8) -> u8")).unwrap();
}

#[test]
fn trap_spellings_are_rejected() {
    let cases: &[(&str, &str, &str)] = &[
        ("requires(a & b)", "fn f(a: bool, b: bool)", "E_ANNEAL_EAGER_CLAUSE_JOIN"),
        ("requires(a | b)", "fn f(a: bool, b: bool)", "E_ANNEAL_EAGER_CLAUSE_JOIN"),
        ("requires(!a == b)", "fn f(a: bool, b: bool)", "E_ANNEAL_AMBIGUOUS_NEGATION"),
        ("requires(a < b < c)", "fn f(a: u8, b: u8, c: u8)", "E_ANNEAL_CHAINED_COMPARISON"),
        ("requires(a = b)", "fn f(a: u8, b: u8)", "E_ANNEAL_IMPURE_SPEC_EXPR"),
        ("requires({ a })", "fn f(a: bool)", "E_ANNEAL_IMPURE_SPEC_EXPR"),
        ("requires(while a { })", "fn f(a: bool)", "E_ANNEAL_IMPURE_SPEC_EXPR"),
        ("requires(old(a) == a)", "fn f(a: u8)", "E_ANNEAL_OLD_IN_PRECONDITION"),
        ("ensures(|r| r == old(a))", "fn f(a: u8) -> u8", "E_ANNEAL_UNSUPPORTED_OLD"),
        ("requires(lenght > 0usize)", "fn f(length: usize)", "E_ANNEAL_SPEC_UNKNOWN_IDENT"),
        ("requires(ret == 0u8)", "fn f() -> u8", "E_ANNEAL_SPEC_UNKNOWN_IDENT"),
        ("requires(a == b)", "fn f(a: u8, b: u16)", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
        ("requires(a == 256)", "fn f(a: u8)", "E_ANNEAL_SPEC_LITERAL_RANGE"),
        ("requires(a.len() > 0)", "fn f(a: u8)", "E_ANNEAL_SPEC_UNSUPPORTED_EXPR"),
        ("modifies(none)", "fn f()", "E_ANNEAL_UNSUPPORTED_CLAUSE"),
        ("requirs(true)", "fn f()", "E_ANNEAL_UNKNOWN_CLAUSE"),
        ("ensures(|a| a == a)", "fn f(a: u8) -> u8", "E_ANNEAL_SPEC_SHADOWING"),
        ("requires(lookup(a))", "fn f(a: u8)", "E_ANNEAL_SPEC_UNKNOWN_FN"),
        ("total", "fn f(a: &[u8])", "E_ANNEAL_UNSUPPORTED_TYPE"),
        ("requires(a)", "fn f(a: u8)", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
    ];
    for (attr, sig, code) in cases {
        expect_error(&wrap(attr, sig), code);
    }
    let suggestion = expect_error(
        &wrap("requires(lenght > 0usize)", "fn f(length: usize)"),
        "E_ANNEAL_SPEC_UNKNOWN_IDENT",
    );
    assert!(suggestion.contains("`length`"), "{suggestion}");
}

#[test]
fn if_expressions_lower_by_result_type() {
    // A `bool`-valued `if` lowers to two implications.
    let l = lower_one(&wrap(
        "ensures(|r| if a > 0u8 { r == a } else { r == 1u8 })",
        "fn f(a: u8) -> u8",
    ))
    .unwrap();
    let cond = "((specInt (specArg q 0)) > (0 : Int))";
    let want = format!(
        "(({cond} → ((specInt out.ret) = (specInt (specArg q 0)))) ∧ \
         (¬ {cond} → ((specInt out.ret) = (1 : Int))))"
    );
    assert!(l.spec_lean.contains(&want), "{}", l.spec_lean);
    // An `if` that chooses a value lowers to Lean's `if`, and an `else if`
    // chain nests.
    let l = lower_one(&wrap(
        "ensures(|r| r == if a < 10u8 { a } else if a < 20u8 { 10u8 } else { 20 })",
        "fn f(a: u8) -> u8",
    ))
    .unwrap();
    assert!(
        l.spec_lean.contains(
            "(if ((specInt (specArg q 0)) < (10 : Int)) then (specInt (specArg q 0)) else \
             (if ((specInt (specArg q 0)) < (20 : Int)) then (10 : Int) else (20 : Int)))"
        ),
        "{}",
        l.spec_lean
    );
    // Untyped literal branches take their type from context, which
    // range-checks them.
    let l =
        lower_one(&wrap("ensures(|r| r == if b { 1 } else { 0 })", "fn f(b: bool) -> u8")).unwrap();
    assert!(
        l.spec_lean.contains("(if (specBool (specArg q 0) = true) then (1 : Int) else (0 : Int))"),
        "{}",
        l.spec_lean
    );
    for body in ["r == if b { 256 } else { 0 }", "r == if b { 0 } else { -1 }"] {
        expect_error(
            &wrap(&format!("ensures(|r| {body})"), "fn f(b: bool) -> u8"),
            "E_ANNEAL_SPEC_LITERAL_RANGE",
        );
    }
    expect_error(
        &wrap("requires((if b { 1 } else { 0 }) == 1)", "fn f(b: bool)"),
        "E_ANNEAL_SPEC_TYPE_ANNOTATION_NEEDED",
    );
    lower_one(&wrap("requires(math(if b { 1 } else { 0 }) == 1)", "fn f(b: bool)")).unwrap();
    lower_one(&wrap("requires(math(x) < -(if b { 1 } else { 2 }))", "fn f(b: bool, x: i8)"))
        .unwrap();
    // A helper may return an `if` of untyped literals at its return type.
    lower_one(
        "anneal::external_spec! {
            #[anneal::pure]
            fn bit(b: u8) -> u8 { if b == 0u8 { 0 } else { 1 } }
            #[anneal::spec(ensures(|r| r == bit(a)))]
            fn f(a: u8) -> u8;
        }",
    )
    .unwrap();
    // `max_steps` may choose between bounds.
    let l = lower_one(&wrap("max_steps = if n > 100 { n } else { 100 }", "fn f(n: u32)")).unwrap();
    assert!(
        l.spec_lean.contains(
            "(if ((specInt (specArg q 0)) > (100 : Int)) then (specNat (specArg q 0)) else \
             (100 : Nat))"
        ),
        "{}",
        l.spec_lean
    );
}

#[test]
fn if_expressions_are_parsed_and_type_checked_strictly() {
    let cases: &[(&str, &str, &str)] = &[
        ("requires(if a { true })", "fn f(a: bool)", "E_ANNEAL_SPEC_SYNTAX"),
        ("requires(if a { true } else false)", "fn f(a: bool)", "E_ANNEAL_SPEC_SYNTAX"),
        ("requires(if a { true } else if { false })", "fn f(a: bool)", "E_ANNEAL_SPEC_SYNTAX"),
        ("requires(if { true } else { false })", "fn f(a: bool)", "E_ANNEAL_SPEC_SYNTAX"),
        ("requires(if a { } else { false })", "fn f(a: bool)", "E_ANNEAL_SPEC_SYNTAX"),
        ("requires(if a { a; a } else { false })", "fn f(a: bool)", "E_ANNEAL_SPEC_SYNTAX"),
        ("requires(if x { true } else { false })", "fn f(x: u8)", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
        (
            "ensures(|r| r == if a { 1u8 } else { true })",
            "fn f(a: bool) -> u8",
            "E_ANNEAL_SPEC_TYPE_MISMATCH",
        ),
        (
            "ensures(|r| r == if a { x } else { y })",
            "fn f(a: bool, x: u8, y: u16) -> u8",
            "E_ANNEAL_SPEC_TYPE_MISMATCH",
        ),
        (
            "ensures(|r| math(r) == if a { math(x) } else { x })",
            "fn f(a: bool, x: u8) -> u8",
            "E_ANNEAL_SPEC_TYPE_MISMATCH",
        ),
        (
            "requires((if a { x } else { y }) + 1u8 > 0u8)",
            "fn f(a: bool, x: u8, y: u8)",
            "E_ANNEAL_AMBIGUOUS_SPEC_ARITH",
        ),
        (
            "requires(if let true = a { true } else { false })",
            "fn f(a: bool)",
            "E_ANNEAL_IMPURE_SPEC_EXPR",
        ),
        (
            "requires(if math { x } > 0 { true } else { false })",
            "fn f(x: u8)",
            "E_ANNEAL_SPEC_SYNTAX",
        ),
    ];
    for (attr, sig, code) in cases {
        expect_error(&wrap(attr, sig), code);
    }
    let r = expect_error(&wrap("requires(if a { true })", "fn f(a: bool)"), "E_ANNEAL_SPEC_SYNTAX");
    assert!(r.contains("`if` without `else`"), "{r}");
    // A binary operator after an `if` would bind to the whole `if`, which is
    // easy to misread as binding inside the `else` branch.
    for clause in [
        "requires(if a { x } else { y } > 0u8)",
        "requires(x == if a { x } else { y } && a)",
        "requires(!if a { a } else { b } == a)",
    ] {
        let r = expect_error(
            &wrap(clause, "fn f(a: bool, b: bool, x: u8, y: u8)"),
            "E_ANNEAL_SPEC_SYNTAX",
        );
        assert!(r.contains("must be parenthesized"), "{clause}: {r}");
    }
    lower_one(&wrap("requires((x == if a { x } else { y }) && a)", "fn f(a: bool, x: u8, y: u8)"))
        .unwrap();
    // As in Rust, a condition ends at the first `{`, but a nested `if` in the
    // condition keeps its own branches.
    lower_one(&wrap(
        "requires(if if a { b } else { !b } { x > 0u8 } else { x == 0u8 })",
        "fn f(a: bool, b: bool, x: u8)",
    ))
    .unwrap();
}

#[test]
fn if_branches_may_divide_by_what_the_condition_proves_nonzero() {
    let sig = "fn f(n: u8, d: u8) -> u8";
    for body in [
        "if d != 0u8 { math(r) == math(n / d) } else { r == 0u8 }",
        "if d == 0u8 { r == 0u8 } else { math(r) == math(n % d) }",
        "if !(d > 0u8) { r == 0u8 } else { math(r) == math(n / d) }",
        "if d == 0u8 || n == 0u8 { r == 0u8 } else { math(r) == math(n / d) }",
        "if n == 0u8 { r == 0u8 } else if d <= 0u8 { r == 1u8 } else { math(r) == math(n / d) }",
        "if d == u8::MIN { r == 0u8 } else { math(r) == math(n / d) }",
    ] {
        lower_one(&wrap(&format!("ensures(|r| {body})"), sig))
            .unwrap_or_else(|e| panic!("{body}: {e:?}"));
    }
    for body in [
        "if d == 0u8 { math(r) == math(n / d) } else { r == 0u8 }",
        "if d != 0u8 { r == 0u8 } else { math(r) == math(n / d) }",
        "if d != 0u8 || n == 0u8 { math(r) == math(n / d) } else { r == 0u8 }",
        "(if d != 0u8 { r == 0u8 } else { r == 1u8 }) && math(r) == math(n / d)",
    ] {
        expect_error(&wrap(&format!("ensures(|r| {body})"), sig), "E_ANNEAL_UNGUARDED_SPEC_DIV");
    }
    lower_one(&wrap("max_steps = if d == 0 { 1 } else { n / d }", "fn f(n: u32, d: u32)")).unwrap();
    expect_error(
        &wrap("max_steps = if d == 0 { n / d } else { 1 }", "fn f(n: u32, d: u32)"),
        "E_ANNEAL_UNGUARDED_SPEC_DIV",
    );
}

#[test]
fn value_ifs_need_decidable_conditions() {
    let r = expect_error(
        "anneal::external_spec! {
            #[anneal::pure]
            fn pick(b: bool, x: u8) -> u8 { if b { x } else { 0u8 } }
        }",
        "E_ANNEAL_UNDECIDABLE_SPEC_IF",
    );
    assert!(r.contains("`b` is a `bool` helper parameter"), "{r}");
    let small = "#[anneal::pure] fn small(x: u8) -> bool { x < 10u8 }";
    let r = expect_error(
        &format!(
            "anneal::external_spec! {{ {small}
                #[anneal::spec(ensures(|r| r == if small(a) {{ 1u8 }} else {{ 0u8 }}))]
                fn f(a: u8) -> u8;
            }}"
        ),
        "E_ANNEAL_UNDECIDABLE_SPEC_IF",
    );
    assert!(r.contains("`small` is a `bool` helper"), "{r}");
    expect_error(
        &wrap("ensures(|r| r == if () == () { 1u8 } else { 0u8 })", "fn f() -> u8"),
        "E_ANNEAL_UNDECIDABLE_SPEC_IF",
    );
    // `()`-valued `if` branches inside a value-choosing `if` condition must
    // still report undecidable equality even when guarded by nonzero facts.
    expect_error(
        &wrap(
            "ensures(|r| d != 0u8 && r == if (if math(n / d) > 0 { () } else { () }) == () { 1u8 } else { 0u8 })",
            "fn f(n: u8, d: u8) -> u8",
        ),
        "E_ANNEAL_UNDECIDABLE_SPEC_IF",
    );
    // Deeply nested `if`s in a comparison condition must lower in linear time.
    let mut nested = "x == 0u8".to_string();
    for _ in 0..30 {
        nested = format!("(if {nested} {{ 1u8 }} else {{ 0u8 }}) == 1u8");
    }
    lower_one(&wrap(
        &format!("ensures(|r| r == if {nested} {{ 1u8 }} else {{ 0u8 }})"),
        "fn f(x: u8) -> u8",
    ))
    .unwrap();
    // A `bool`-valued `if` needs no decidable condition.
    lower_one(&format!(
        "anneal::external_spec! {{ {small}
            #[anneal::pure]
            fn pick(b: bool, x: u8) -> bool {{ if b {{ x == 1u8 }} else {{ x == 0u8 }} }}
            #[anneal::spec(ensures(|r| if small(a) {{ r == 1u8 }} else {{ pick(false, r) }}))]
            fn f(a: u8) -> u8;
        }}"
    ))
    .unwrap();
}

#[test]
fn let_bindings_lower_to_lean_lets() {
    let l = lower_one(&wrap(
        "requires(align != 0u64), requires({ let rem = math(len) % math(align); rem == 0 })",
        "fn f(len: u64, align: u64)",
    ))
    .unwrap();
    assert!(
        l.spec_lean.contains(
            "(let «rem» : Int := (Trusted.MirSemantics.intTmod (specInt (specArg q 0)) \
             (specInt (specArg q 1))); («rem» = (0 : Int)))"
        ),
        "{}",
        l.spec_lean
    );
    // Bindings nest, and each takes the Lean type of its value.
    let l = lower_one(&wrap(
        "ensures(|ret| { let m = if a > b { a } else { b }; let big = m > 9u8; \
         let u = (); let twice = math(m) * 2; big ==> ret == m && twice >= 0 && u == () })",
        "fn f(a: u8, b: u8) -> u8",
    ))
    .unwrap();
    for want in [
        "(let «m» : Int := (if ((specInt (specArg q 0)) > (specInt (specArg q 1))) then \
         (specInt (specArg q 0)) else (specInt (specArg q 1))); ",
        "(let «big» : Prop := («m» > (9 : Int)); ",
        "(let «u» : Trusted.MirSemantics.Val := Trusted.MirSemantics.Val.unit; ",
        "(let «twice» : Int := («m» * (2 : Int)); ",
    ] {
        assert!(l.spec_lean.contains(want), "missing {want}:\n{}", l.spec_lean);
    }
    // `if` branches, `math { .. }`, and helper bodies are blocks too.
    let l = lower_one(
        "anneal::external_spec! {
            #[anneal::pure]
            fn clamp9(x: u8) -> u8 { let cap: u8 = 9; if x > cap { cap } else { x } }
            #[anneal::spec(ensures(|ret| if a > 0u8 { let x: u8 = a; ret == x } \
                                         else { math { let z = 0; z } == math(ret) }))]
            fn f(a: u8) -> u8;
        }",
    )
    .unwrap();
    for want in [
        "(let «cap» : Int := (9 : Int); (if («x» > «cap») then «cap» else «x»))",
        "(let «x» : Int := (specInt (specArg q 0)); ((specInt out.ret) = «x»))",
        "(let «z» : Int := (0 : Int); «z»)",
    ] {
        assert!(l.spec_lean.contains(want), "missing {want}:\n{}", l.spec_lean);
    }
    // In `max_steps`, an integer binding is a `Nat` step count, compared in
    // conditions through `Int.ofNat`.
    let l = lower_one(&wrap(
        "max_steps = { let base: u32 = 10; let twice = n * 2; \
         if twice > base { twice } else { base } }",
        "fn f(n: u32)",
    ))
    .unwrap();
    assert!(
        l.spec_lean.contains(
            "(let «base» : Nat := (10 : Nat); (let «twice» : Nat := ((specNat (specArg q 0)) * \
             (2 : Nat)); (if ((Int.ofNat «twice») > (Int.ofNat «base»)) then «twice» else \
             «base»)))"
        ),
        "{}",
        l.spec_lean
    );
}

#[test]
fn let_bindings_are_typed_like_their_values() {
    let sig = "fn f(a: u8, b: u8) -> u8";
    for (clause, code) in [
        ("ensures(|ret| { let k = 4; ret == k })", "E_ANNEAL_SPEC_TYPE_ANNOTATION_NEEDED"),
        (
            "ensures(|ret| { let k = if a > b { 1 } else { 2 }; ret == k })",
            "E_ANNEAL_SPEC_TYPE_ANNOTATION_NEEDED",
        ),
        ("ensures(|ret| { let k: u8 = 256; ret == k })", "E_ANNEAL_SPEC_LITERAL_RANGE"),
        ("ensures(|ret| { let x: u16 = a; ret == 0u8 })", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
        ("ensures(|ret| { let x: u8 = math(a); ret == x })", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
        ("ensures(|ret| { let p: bool = a; p })", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
        ("ensures(|ret| { let s = a + b; ret == s })", "E_ANNEAL_AMBIGUOUS_SPEC_ARITH"),
        // A binding of a machine integer keeps its machine type.
        ("ensures(|ret| { let x = a; x + 1u8 == ret })", "E_ANNEAL_AMBIGUOUS_SPEC_ARITH"),
    ] {
        expect_error(&wrap(clause, sig), code);
    }
    for clause in [
        "ensures(|ret| { let k: u8 = 4; ret == k })",
        "ensures(|ret| { let s = math(a) + math(b); math(ret) <= s })",
        "ensures(|ret| { let x = a; math(x) + 1 == math(ret) })",
        // Inside `math`, a binding is mathematical unless annotated, and an
        // annotated one is a machine-typed value that `math` then lifts.
        "ensures(|ret| math({ let s = a + b; s * 2 }) >= math(ret))",
        "ensures(|ret| math({ let k = 4; let x: u8 = a; x * k }) >= 0)",
    ] {
        lower_one(&wrap(clause, sig)).unwrap_or_else(|e| panic!("{clause}: {e:?}"));
    }
    for (clause, code) in [
        ("max_steps = { let s: i32 = 1; n }", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
        ("max_steps = { let x = n - 1; x }", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
        ("max_steps = { let x = n; -x }", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
        ("max_steps = { let big = n > 3; big }", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
        ("max_steps = { let k: u8 = n; k }", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
    ] {
        expect_error(&wrap(clause, "fn f(n: u32)"), code);
    }
    for clause in [
        "max_steps = { let big = n > 3; if big { n } else { 3 } }",
        "max_steps = { let k: u32 = n; k }",
        "max_steps = { let k: u64 = n * 2; k }",
    ] {
        lower_one(&wrap(clause, "fn f(n: u32)")).unwrap_or_else(|e| panic!("{clause}: {e:?}"));
    }
}

#[test]
fn let_bindings_cannot_shadow_or_capture_names() {
    let sig = "fn f(a: u8, b: u8) -> u8";
    for clause in [
        "ensures(|ret| { let a: u8 = b; ret == a })",
        "ensures(|ret| { let ret: u8 = b; ret == a })",
        "ensures(|ret| { let x: u8 = a; ({ let x: u8 = b; x }) == x })",
    ] {
        expect_error(&wrap(clause, sig), "E_ANNEAL_SPEC_SHADOWING");
    }
    let r = expect_error(
        "anneal::external_spec! {
            #[anneal::pure] fn small(x: u8) -> bool { x < 10u8 }
            #[anneal::spec(ensures(|ret| { let small: u8 = a; ret == small }))]
            fn f(a: u8) -> u8;
        }",
        "E_ANNEAL_SPEC_SHADOWING",
    );
    assert!(r.contains("`#[anneal::pure]` helper"), "{r}");
    // A binder named after a name that the generated Lean references would
    // capture that reference.
    for name in ["Int", "True", "Trusted", "Spec", "Nat", "q", "out", "specInt", "math", "old"] {
        expect_error(
            &wrap(&format!("ensures(|ret| {{ let {name}: u8 = a; ret == {name} }})"), sig),
            "E_ANNEAL_RESERVED_PARAM_NAME",
        );
    }
    // Sibling blocks may reuse a name.
    lower_one(&wrap(
        "ensures(|ret| ({ let x: u8 = a; x == a }) && ({ let x: u8 = b; x == b }))",
        sig,
    ))
    .unwrap();
}

#[test]
fn let_statements_are_parsed_strictly() {
    let sig = "fn f(a: u8) -> u8";
    for (clause, code) in [
        ("ensures(|ret| { let x: u8 = a; })", "E_ANNEAL_SPEC_SYNTAX"),
        ("ensures(|ret| { let x: u8 = a; ; ret == x })", "E_ANNEAL_SPEC_SYNTAX"),
        ("ensures(|ret| { a == a; ret == a })", "E_ANNEAL_SPEC_SYNTAX"),
        ("ensures(|ret| { let x: u8; ret == a })", "E_ANNEAL_SPEC_SYNTAX"),
        ("ensures(|ret| { let mut x: u8 = a; ret == x })", "E_ANNEAL_IMPURE_SPEC_EXPR"),
        ("ensures(|ret| { let (x, y) = (a, a); ret == x })", "E_ANNEAL_IMPURE_SPEC_EXPR"),
        ("ensures(|ret| { let Some(x) = a; ret == x })", "E_ANNEAL_IMPURE_SPEC_EXPR"),
        ("ensures(|ret| { let _ = a; ret == a })", "E_ANNEAL_IMPURE_SPEC_EXPR"),
        ("ensures(|ret| { let x: u8 = a else { 0u8 }; ret == x })", "E_ANNEAL_IMPURE_SPEC_EXPR"),
        ("ensures(|ret| { let x: f32 = a; ret == a })", "E_ANNEAL_UNSUPPORTED_TYPE"),
        ("ensures(|ret| { let x: &u8 = a; ret == a })", "E_ANNEAL_UNSUPPORTED_TYPE"),
        ("ensures(|ret| { ret == a })", "E_ANNEAL_IMPURE_SPEC_EXPR"),
        ("ensures(|ret| { })", "E_ANNEAL_IMPURE_SPEC_EXPR"),
    ] {
        expect_error(&wrap(clause, sig), code);
    }
    // Lean warns about an unused binder.
    let r = expect_error(
        &wrap("ensures(|ret| { let x: u8 = a; let y: u8 = x; ret == x })", sig),
        "E_ANNEAL_UNUSED_LET",
    );
    assert!(r.contains("`y` is never used"), "{r}");
    // A binary operator after a block would apply to the whole block.
    let r = expect_error(
        &wrap("ensures(|ret| { let x: u8 = a; x } == ret)", sig),
        "E_ANNEAL_SPEC_SYNTAX",
    );
    assert!(r.contains("a block must be parenthesized"), "{r}");
    lower_one(&wrap("ensures(|ret| ({ let x: u8 = a; x }) == ret)", sig)).unwrap();
    // An initializer may itself be an `if` with an `else`.
    lower_one(&wrap(
        "ensures(|ret| { let x = if a > 1u8 { a } else if a > 0u8 { 1u8 } else { 0u8 }; ret == x })",
        sig,
    ))
    .unwrap();
    // A helper body is a block: `let` statements, then one expression.
    expect_error(
        "anneal::external_spec! {
            #[anneal::pure] fn g(x: u8) -> u8 { let y: u8 = x; y; }
        }",
        "E_ANNEAL_IMPURE_SPEC_EXPR",
    );
}

#[test]
fn let_bound_bools_keep_undecidable_conditions_rejected() {
    let small = "#[anneal::pure] fn small(x: u8) -> bool { x < 10u8 }";
    let spec = |ensures: &str| {
        format!(
            "anneal::external_spec! {{ {small}
                #[anneal::spec(ensures(|r| {ensures}))]
                fn f(a: u8) -> u8;
            }}"
        )
    };
    let r = expect_error(
        &spec("{ let p = small(a); r == if p { 1u8 } else { 0u8 } }"),
        "E_ANNEAL_UNDECIDABLE_SPEC_IF",
    );
    assert!(r.contains("`p` is bound to a `bool` that Lean cannot decide"), "{r}");
    for ensures in [
        "r == if ({ let p = small(a); p }) { 1u8 } else { 0u8 }",
        "r == if ({ let u = (); u == u }) { 1u8 } else { 0u8 }",
        "{ let p = small(a); let p2 = p && a > 1u8; r == if p2 { 1u8 } else { 0u8 } }",
    ] {
        expect_error(&spec(ensures), "E_ANNEAL_UNDECIDABLE_SPEC_IF");
    }
    // The check sees each block in the context it was lowered in: under a
    // guard, and inside `math`.
    let guarded = |cond: &str| {
        format!(
            "anneal::external_spec! {{ {small}
                #[anneal::spec(ensures(|r| d != 0u8 ==> (r == if ({cond}) {{ 1u8 }} else {{ 0u8 }})))]
                fn f(a: u8, n: u8, d: u8) -> u8;
            }}"
        )
    };
    expect_error(
        &guarded("{ let p = small(a) && math(n / d) > 0; p }"),
        "E_ANNEAL_UNDECIDABLE_SPEC_IF",
    );
    lower_one(&guarded("{ let p = a > 1u8 && math(n / d) > 0; p }")).unwrap();
    for ensures in [
        "math(r) == math(if ({ let k = 1; small(a) && k > 0 }) { 1 } else { 0 })",
        "math(r) == math(if ({ let k = 1; () == () && k > 0 }) { 1 } else { 0 })",
    ] {
        expect_error(&spec(ensures), "E_ANNEAL_UNDECIDABLE_SPEC_IF");
    }
    lower_one(&spec("math(r) == math(if ({ let k = 1; a > 1u8 && k > 0 }) { 1 } else { 0 })"))
        .unwrap();
    lower_one(&spec("r == if (math({ let k = 1; k }) > 0) { 1u8 } else { 0u8 }")).unwrap();
    for ensures in [
        "{ let p = a > 5u8; r == if p { 1u8 } else { 0u8 } }",
        "{ let p = small(a); if p { r == 1u8 } else { r == 0u8 } }",
    ] {
        lower_one(&spec(ensures)).unwrap_or_else(|e| panic!("{ensures}: {e:?}"));
    }
}

#[test]
fn let_bindings_carry_divisor_guards_soundly() {
    let sig = "fn f(n: u8, d: u8) -> u8";
    for clause in [
        "ensures(|r| { let k: u8 = 4; math(r) == math(n / k) })",
        "ensures(|r| { let z: u8 = 0; d != z ==> math(r) == math(n / d) })",
        "ensures(|r| { let ok = d != 0u8; ok ==> math(r) == math(n / d) })",
        "ensures(|r| { let zero = d == 0u8; if zero { r == 0u8 } else { math(r) == math(n % d) } })",
        "ensures(|r| { let e = d; e != 0u8 ==> math(r) == math(n / e) })",
        "requires({ let ok = d != 0u8; ok }), ensures(|r| math(r) == math(n / d))",
        "requires(d != 0u8), ensures(|r| { let e = d; math(r) == math(n / e) })",
    ] {
        lower_one(&wrap(clause, sig)).unwrap_or_else(|e| panic!("{clause}: {e:?}"));
    }
    for clause in [
        "ensures(|r| { let z: u8 = 0; math(r) == math(n / z) })",
        "ensures(|r| { let e = d; e != 0u8 ==> math(r) == math(n / d) })",
        "ensures(|r| { let ok = d == 0u8; ok ==> math(r) == math(n / d) })",
        // A fact about a block's own binding does not leave the block, even
        // to guard a later binding of the same name.
        "requires({ let e = d; e != 0u8 }), ensures(|r| math(r) == math(n / d))",
        "requires({ let e = d; e != 0u8 }), ensures(|r| { let e = n; math(r) == math(n / e) })",
    ] {
        expect_error(&wrap(clause, sig), "E_ANNEAL_UNGUARDED_SPEC_DIV");
    }
    lower_one(&wrap("max_steps = { let k: u32 = 2; n / k }", "fn f(n: u32)")).unwrap();
    expect_error(
        &wrap("max_steps = { let z: u32 = 0; n / z }", "fn f(n: u32)"),
        "E_ANNEAL_UNGUARDED_SPEC_DIV",
    );
}

#[test]
fn match_expressions_lower_by_result_type() {
    // Integer arms choose a value with Lean's `if`; the scrutinee is bound
    // once, and or-patterns and constants are disjunctions of equalities.
    let l = lower_one(
        "anneal::external_spec! {
            #[anneal::pure]
            fn bucket(x: u8) -> u8 { match x { 0 => 0, 1 | 2 => 1, u8::MAX => 3, _ => 2 } }
            #[anneal::spec(ensures(|r| r == bucket(a)))]
            fn f(a: u8) -> u8;
        }",
    )
    .unwrap();
    assert!(
        l.spec_lean.contains(
            "(let «match» : Int := «x»; (if («match» = (0 : Int)) then (0 : Int) else \
             (if ((«match» = (1 : Int)) ∨ («match» = (2 : Int))) then (1 : Int) else \
             (if («match» = (255 : Int)) then (3 : Int) else (2 : Int)))))"
        ),
        "{}",
        l.spec_lean
    );
    // `bool` arms join as implications, and a name binds the scrutinee.
    let l = lower_one(&wrap(
        "ensures(|ret| match a { 0 => ret == 0u8, k => { let z: u8 = k; ret == z } })",
        "fn f(a: u8) -> u8",
    ))
    .unwrap();
    assert!(
        l.spec_lean.contains(
            "(let «match» : Int := (specInt (specArg q 0)); (((«match» = (0 : Int)) → \
             ((specInt out.ret) = (0 : Int))) ∧ (¬ («match» = (0 : Int)) → \
             (let «k» : Int := «match»; (let «z» : Int := «k»; ((specInt out.ret) = «z»))))))"
        ),
        "{}",
        l.spec_lean
    );
    let l = lower_one(&wrap(
        "ensures(|ret| ret == match a > b { true => a, false => b })",
        "fn f(a: u8, b: u8) -> u8",
    ))
    .unwrap();
    assert!(l.spec_lean.contains("(let «match» : Prop := "), "{}", l.spec_lean);
    // Untyped literal arms take their type from context, which range-checks
    // them.
    lower_one(&wrap("ensures(|ret| ret == match a { 0 => 1, _ => 2 })", "fn f(a: u8) -> u8"))
        .unwrap();
    expect_error(
        &wrap("ensures(|ret| ret == match a { 0 => 256, _ => 2 })", "fn f(a: u8) -> u8"),
        "E_ANNEAL_SPEC_LITERAL_RANGE",
    );
    // A lone catch-all arm needs no scrutinee binding, which Lean would warn
    // is unused.
    let l = lower_one(&wrap("requires(match a { _ => true })", "fn f(a: u8)")).unwrap();
    assert!(!l.spec_lean.contains("«match»"), "{}", l.spec_lean);
    // In `max_steps`, an integer scrutinee and its bindings are step counts.
    let l = lower_one(&wrap("max_steps = match n { 0 => 1, m => m * 2 }", "fn f(n: u32)")).unwrap();
    assert!(
        l.spec_lean.contains(
            "(let «match» : Nat := (specNat (specArg q 0)); (if («match» = (0 : Nat)) then \
             (1 : Nat) else (let «m» : Nat := «match»; («m» * (2 : Nat)))))"
        ),
        "{}",
        l.spec_lean
    );
}

#[test]
fn match_patterns_are_checked_strictly() {
    let sig = "fn f(a: u8, b: bool) -> u8";
    for (clause, code) in [
        (
            "ensures(|r| match a { x if x > 1u8 => true, _ => false })",
            "E_ANNEAL_SPEC_UNSUPPORTED_EXPR",
        ),
        ("ensures(|r| match a { (x, y) => true, _ => false })", "E_ANNEAL_SPEC_UNSUPPORTED_EXPR"),
        ("ensures(|r| match a { 0..=5 => true, _ => false })", "E_ANNEAL_SPEC_UNSUPPORTED_EXPR"),
        ("ensures(|r| match a { ref x => r == x })", "E_ANNEAL_SPEC_UNSUPPORTED_EXPR"),
        ("ensures(|r| match a { mut x => r == x })", "E_ANNEAL_SPEC_UNSUPPORTED_EXPR"),
        ("ensures(|r| match a { Some(x) => true, _ => false })", "E_ANNEAL_SPEC_UNSUPPORTED_EXPR"),
        ("ensures(|r| match a { Foo::Bar => true, _ => false })", "E_ANNEAL_SPEC_UNSUPPORTED_EXPR"),
        ("ensures(|r| match a { 0 | _ => true })", "E_ANNEAL_SPEC_UNSUPPORTED_EXPR"),
        ("ensures(|r| match a { \"x\" => true, _ => false })", "E_ANNEAL_SPEC_UNSUPPORTED_EXPR"),
        ("ensures(|r| match a { })", "E_ANNEAL_NON_EXHAUSTIVE_MATCH"),
        ("ensures(|r| match b { true => true })", "E_ANNEAL_NON_EXHAUSTIVE_MATCH"),
        ("ensures(|r| match a { 0 => true, 1 => false })", "E_ANNEAL_NON_EXHAUSTIVE_MATCH"),
        ("ensures(|r| match a { _ => true, 0 => false })", "E_ANNEAL_UNREACHABLE_MATCH_ARM"),
        ("ensures(|r| match a { 0 | 0 => true, _ => false })", "E_ANNEAL_UNREACHABLE_MATCH_ARM"),
        (
            "ensures(|r| match a { 0 => true, 0 => false, _ => true })",
            "E_ANNEAL_UNREACHABLE_MATCH_ARM",
        ),
        (
            "ensures(|r| match b { true => true, true => false, _ => true })",
            "E_ANNEAL_UNREACHABLE_MATCH_ARM",
        ),
        (
            "ensures(|r| match b { true => true, false => false, _ => true })",
            "E_ANNEAL_UNREACHABLE_MATCH_ARM",
        ),
        ("ensures(|r| match a { true => true, _ => false })", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
        ("ensures(|r| match b { 0 => true, _ => false })", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
        ("ensures(|r| match a { 0u16 => true, _ => false })", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
        ("ensures(|r| match a { 256 => true, _ => false })", "E_ANNEAL_SPEC_LITERAL_RANGE"),
        ("ensures(|r| match a { -1 => true, _ => false })", "E_ANNEAL_SPEC_LITERAL_RANGE"),
        ("ensures(|r| match () { _ => true })", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
        ("ensures(|r| match a { 0 => 1u8, _ => true } == r)", "E_ANNEAL_SPEC_SYNTAX"),
        ("ensures(|r| match a { 0 true, _ => false })", "E_ANNEAL_SPEC_SYNTAX"),
        ("ensures(|r| match { _ => true })", "E_ANNEAL_SPEC_SYNTAX"),
        ("ensures(|r| r == match a { 0 => 1u8, _ => true })", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
        // Pattern bindings follow the `let` rules.
        ("ensures(|r| match a { b => r == a })", "E_ANNEAL_SPEC_SHADOWING"),
        ("ensures(|r| match a { q => r == q })", "E_ANNEAL_RESERVED_PARAM_NAME"),
        ("ensures(|r| match a { k => true })", "E_ANNEAL_UNUSED_LET"),
    ] {
        expect_error(&wrap(clause, sig), code);
    }
    let r = expect_error(
        &wrap("ensures(|r| match a { x if x > 1u8 => true, _ => false })", sig),
        "E_ANNEAL_SPEC_UNSUPPORTED_EXPR",
    );
    assert!(r.contains("`match` guards are not supported"), "{r}");
    let r = expect_error(
        &wrap("ensures(|r| match a { 0 => r == 0u8, _ => true } && b)", sig),
        "E_ANNEAL_SPEC_SYNTAX",
    );
    assert!(r.contains("a `match` expression must be parenthesized"), "{r}");
    lower_one(&wrap("ensures(|r| (match a { 0 => r == 0u8, _ => true }) && b)", sig)).unwrap();
    for clause in [
        "max_steps = match n { 0 => 1, _ => 2 }",
        "max_steps = match m { -1 => 1, _ => 2 }",
        "max_steps = match m { 0i32 => 1, _ => 2 }",
    ] {
        expect_error(&wrap(clause, "fn f(n: i32, m: u32)"), "E_ANNEAL_SPEC_TYPE_MISMATCH");
    }
    // A `max_steps` pattern is checked against the scrutinee's machine type,
    // as in a `max_steps` `if` condition, and against its own suffix.
    let sig = "fn f(m: u32)";
    for (clause, code) in [
        ("max_steps = match m { 3u8 => 1, _ => 2 }", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
        ("max_steps = match m { 300u8 => 1, _ => 2 }", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
        ("max_steps = match m { u8::MAX => 1, _ => 2 }", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
        ("max_steps = match m { 4294967296 => 1, _ => 2 }", "E_ANNEAL_SPEC_LITERAL_RANGE"),
        (
            "max_steps = { let k = m * 2; match k { 300u8 => 1, _ => 2 } }",
            "E_ANNEAL_SPEC_LITERAL_RANGE",
        ),
        ("max_steps = match 5 { 300u8 => 1, _ => 2 }", "E_ANNEAL_SPEC_LITERAL_RANGE"),
    ] {
        expect_error(&wrap(clause, sig), code);
    }
    for clause in [
        "max_steps = match m { 3u32 => 1, u32::MAX => 2, 4294967294 => 3, _ => 4 }",
        // A step count with no machine type, such as a sum, product, or
        // `let` binding of step counts, compares like `k == 3u8` does in a
        // `max_steps` condition.
        "max_steps = match m * 2 { 3u8 => 1, _ => 2 }",
        "max_steps = { let k = m * 2; match k { 3u8 => 1, _ => 2 } }",
        "max_steps = { let k = m * 2; if k == 3u8 { 1 } else { 2 } }",
    ] {
        lower_one(&wrap(clause, sig)).unwrap_or_else(|e| panic!("{clause}: {e:?}"));
    }
    // A suffixed pattern on a `math` scrutinee is in range for its suffix.
    let sig = "fn f(a: u8) -> u8";
    expect_error(
        &wrap("ensures(|r| match math(a) { 300u8 => true, _ => false })", sig),
        "E_ANNEAL_SPEC_LITERAL_RANGE",
    );
    lower_one(&wrap("ensures(|r| match math(a) { 3u16 => true, _ => r == a })", sig)).unwrap();
}

#[test]
fn block_match_arms_need_no_comma() {
    let sig = "fn f(a: u8, b: bool) -> u8";
    let with = lower_one(&wrap(
        "ensures(|r| match a { 0 => { r == 0u8 }, 1 => { let s = 1u8; r == s }, _ => b })",
        sig,
    ))
    .unwrap();
    let without = lower_one(&wrap(
        "ensures(|r| match a { 0 => { r == 0u8 } 1 => { let s = 1u8; r == s } _ => b })",
        sig,
    ))
    .unwrap();
    assert_eq!(with.spec_lean, without.spec_lean);
    let r = expect_error(
        &wrap("ensures(|r| match a { 0 => { r == 0u8 } && b, _ => true })", sig),
        "E_ANNEAL_SPEC_SYNTAX",
    );
    assert!(r.contains("arm body ends at its `}`"), "{r}");
    lower_one(&wrap("ensures(|r| match a { 0 => { r == 0u8 && b } _ => true })", sig)).unwrap();
    // Other bodies, including `if` and `match`, still need a comma.
    for clause in [
        "ensures(|r| match a { 0 => r == 0u8 _ => b })",
        "ensures(|r| match a { 0 => if b { true } else { false } _ => b })",
        "ensures(|r| match a { 0 => match b { _ => true } _ => b })",
        "ensures(|r| match a { 0 => { r == 0u8 }, 1 true, _ => b })",
    ] {
        let r = expect_error(&wrap(clause, sig), "E_ANNEAL_SPEC_SYNTAX");
        assert!(!r.contains("arm body ends at its `}`"), "{r}");
    }
}

#[test]
fn match_arms_may_divide_by_what_their_patterns_prove_nonzero() {
    let sig = "fn f(n: u32, d: u32) -> u32";
    for body in [
        "match d { 0 => r == 0u32, _ => math(r) == math(n / d) }",
        "match d { 1 => math(r) == math(n / d), 0 => r == 0u32, _ => r == 0u32 }",
        "match d { 0 => r == 0u32, k => math(r) == math(n / k) }",
        "match d { 0 | 1 => r == 0u32, _ => math(r) == math(n % d) }",
        "match d { 1 | 2 => math(r) == math(n / d), _ => r == 0u32 }",
        "match d != 0u32 { true => math(r) == math(n / d), false => r == 0u32 }",
        "match d == 0u32 { true => r == 0u32, false => math(r) == math(n / d) }",
    ] {
        lower_one(&wrap(&format!("ensures(|r| {body})"), sig))
            .unwrap_or_else(|e| panic!("{body}: {e:?}"));
    }
    for body in [
        "match d { 0 => math(r) == math(n / d), _ => r == 0u32 }",
        "match d { 1 => r == 0u32, k => math(r) == math(n / k) }",
        "match d { 0 | 1 => math(r) == math(n / d), _ => r == 0u32 }",
        "match d != 0u32 { true => r == 0u32, false => math(r) == math(n / d) }",
    ] {
        expect_error(&wrap(&format!("ensures(|r| {body})"), sig), "E_ANNEAL_UNGUARDED_SPEC_DIV");
    }
    lower_one(&wrap("max_steps = match d { 0 => 1, _ => n / d }", "fn f(n: u32, d: u32)")).unwrap();
    expect_error(
        &wrap("max_steps = match d { 0 => n / d, _ => 1 }", "fn f(n: u32, d: u32)"),
        "E_ANNEAL_UNGUARDED_SPEC_DIV",
    );
    // A guard about a pattern binding does not leave its arm, so it cannot
    // guard a later binding of the same name.
    let sig = "fn f(n: u32, d: u32)";
    lower_one(&wrap("requires((match d { _ => d != 0u32 }) && math(n / d) > 0)", sig)).unwrap();
    expect_error(
        &wrap(
            "requires((match d { k => k != 0u32 }) && { let k: u32 = 0; math(n / k) == 0 })",
            sig,
        ),
        "E_ANNEAL_UNGUARDED_SPEC_DIV",
    );
}

#[test]
fn value_matches_need_decidable_scrutinees() {
    let small = "#[anneal::pure] fn small(x: u8) -> bool { x < 10u8 }";
    let spec = |ensures: &str| {
        format!(
            "anneal::external_spec! {{ {small}
                #[anneal::spec(ensures(|r| {ensures}))]
                fn f(a: u8) -> u8;
            }}"
        )
    };
    for ensures in [
        "r == match small(a) { true => 1u8, false => 0u8 }",
        "match small(a) { p => r == if p { 1u8 } else { 0u8 } }",
        "r == if (match small(a) { true => a > 1u8, false => true }) { 1u8 } else { 0u8 }",
    ] {
        expect_error(&spec(ensures), "E_ANNEAL_UNDECIDABLE_SPEC_IF");
    }
    for ensures in [
        "match small(a) { true => r == 1u8, false => r == 0u8 }",
        "r == match a { 0 => 1u8, _ => 0u8 }",
        "r == match a > 3u8 { true => 1u8, false => 0u8 }",
    ] {
        lower_one(&spec(ensures)).unwrap_or_else(|e| panic!("{ensures}: {e:?}"));
    }
    // A `max_steps` match chooses a step count, so it needs a decidable
    // `bool` scrutinee too.
    let steps = |max_steps: &str| {
        format!(
            "anneal::external_spec! {{ {small}
                #[anneal::spec(max_steps = {max_steps})]
                fn f(a: u8);
            }}"
        )
    };
    expect_error(
        &steps("match small(a) { true => 1, false => 2 }"),
        "E_ANNEAL_UNDECIDABLE_SPEC_IF",
    );
    lower_one(&steps("match a > 3u8 { true => 1, false => 2 }")).unwrap();
}

#[test]
fn duplicate_targets_are_rejected() {
    expect_error(
        "anneal::external_spec! { #[anneal::spec(total)] fn f(); #[anneal::spec(total)] fn f(); }",
        "E_ANNEAL_DUPLICATE_TARGET",
    );
}

#[test]
fn diagnostics_use_utf8_byte_offsets_and_scalar_columns() {
    // `é` is two UTF-8 bytes but one Unicode scalar value.
    let text = "anneal::external_spec! { #[anneal::spec(requires(/* é */ zz))] fn f(); }";
    let sources = [src("spec.rs", text)];
    let errs = lower(&sources).err().expect("unknown identifier");
    let rendered = errs[0].render(&sources);
    let col_scalars = text[..text.find("zz").unwrap()].chars().count() + 1;
    assert!(rendered.contains(&format!("spec.rs:1:{col_scalars}")), "{rendered}");
    let map = anneal_spec_lower::SourceMap::new(text);
    let s = map.span(errs[0].diag.span);
    assert_eq!(&text[s.start_byte..s.end_byte], "zz");
}

#[test]
fn span_map_points_lean_declarations_at_rust_clauses() {
    let text = USIZE_POINTER_METADATA_SPEC;
    let l = lower_one(text).unwrap();
    let map: serde_json::Value = serde_json::from_str(&l.span_map).unwrap();
    let lean_lines: Vec<&str> = l.spec_lean.lines().collect();
    let post = map["entries"]
        .as_array()
        .unwrap()
        .iter()
        .find(|e| e["lean_decl"] == "Spec.fn0_post")
        .expect("fn0_post entry");
    let start = post["lean_line_start"].as_u64().unwrap() as usize;
    assert!(
        lean_lines[start - 1].starts_with("/-- Normal-return postcondition"),
        "{}",
        lean_lines[start - 1]
    );
    let (b0, b1) = (
        post["rust"]["start_byte"].as_u64().unwrap() as usize,
        post["rust"]["end_byte"].as_u64().unwrap() as usize,
    );
    assert_eq!(&text[b0..b1], "ensures(|ret| ret == elems)");
}

#[test]
fn inactive_cfg_attr_specs_compile_without_any_dependency() {
    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".into());
    let dir = std::env::temp_dir().join(format!("anneal-spec-inert-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let lib = dir.join("lib.rs");
    fs::write(
        &lib,
        "#![deny(warnings)]\n\
         #[cfg_attr(anneal, anneal::spec(requires(a ==> b), ensures(|r| r <==> (a && b)), total))]\n\
         pub fn both(a: bool, b: bool) -> bool { a && b }\n",
    )
    .unwrap();
    let out = Command::new(rustc)
        .args(["--edition=2021", "--crate-type=lib", "--check-cfg=cfg(anneal)", "--out-dir"])
        .arg(&dir)
        .arg(&lib)
        .output()
        .unwrap();
    fs::remove_dir_all(&dir).unwrap();
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
}

#[test]
fn generated_spec_lean_sets_no_options() {
    // `spec-preflight` rejects `set_option autoImplicit`; `cargo-anneal`
    // already compiles specification modules with it disabled.
    let l = lower_one(&wrap("total", "fn f()")).unwrap();
    assert!(!l.spec_lean.contains("set_option"), "{}", l.spec_lean);
}

#[test]
fn generated_doc_comments_wrap_without_splitting_code_spans() {
    let name = "long_function_name_that_forces_doc_wrapping_";
    let l = lower_one(&wrap(
        "requires(x > 0u8), ensures(|r| r == x)",
        &format!("unsafe fn {name}(x: u8) -> u8"),
    ))
    .unwrap();
    let mut in_doc = false;
    for line in l.spec_lean.lines() {
        in_doc |= line.starts_with("/--");
        if in_doc {
            assert!(line.chars().count() <= 80, "{line}");
            // Every doc line closes the code spans it opens.
            assert!(line.matches('`').count() % 2 == 0, "{line}");
        }
        in_doc &= !line.ends_with("-/");
    }
    let post = format!("/-- Normal-return postcondition of\n`{name}`. -/");
    assert!(l.spec_lean.contains(&post), "{}", l.spec_lean);
    // Short doc comments keep their one-line form.
    let short = lower_one(&wrap("total", "fn f()")).unwrap();
    assert!(short.spec_lean.contains("/-- `fn f() -> ()` -/"), "{}", short.spec_lean);
}

#[test]
fn integer_constants_lower_to_target_values() {
    let l = lower_one(&wrap(
        "requires(math(a) + math(b) <= math(usize::MAX) && c != isize::MIN && d > i8::MIN), \
         ensures(|r| r == u32::BITS && usize::BITS == 64u32 && u128::MAX != u128::MIN)",
        "fn f(a: usize, b: usize, c: isize, d: i8) -> u32",
    ))
    .unwrap();
    for want in [
        "(18446744073709551615 : Int)",
        "(Int.neg 9223372036854775808)",
        "(Int.neg 128)",
        "(32 : Int)",
        "(64 : Int)",
        "(340282366920938463463374607431768211455 : Int)",
        "(0 : Int)",
    ] {
        assert!(l.spec_lean.contains(want), "missing {want}:\n{}", l.spec_lean);
    }
    // `T::MIN` and `T::MAX` have type `T`, and `T::BITS` has type `u32`.
    let r = expect_error(
        &wrap("ensures(|r| r == usize::BITS)", "fn f() -> usize"),
        "E_ANNEAL_SPEC_TYPE_MISMATCH",
    );
    assert!(r.contains("u32"), "{r}");
    expect_error(&wrap("requires(a <= u8::MAX)", "fn f(a: u16)"), "E_ANNEAL_SPEC_TYPE_MISMATCH");
    // Machine-integer arithmetic on a constant must still say what it means.
    expect_error(
        &wrap("requires(a <= usize::MAX - 1)", "fn f(a: usize)"),
        "E_ANNEAL_AMBIGUOUS_SPEC_ARITH",
    );
    expect_error(&wrap("requires(-i8::MIN > 0i8)", "fn f()"), "E_ANNEAL_AMBIGUOUS_SPEC_ARITH");
    lower_one(&wrap("requires(math(-i8::MIN) == 128)", "fn f()")).unwrap();
}

#[test]
fn integer_constants_in_step_bounds_and_divisors() {
    let l = lower_one(&wrap(
        "max_steps = u8::MAX + u32::BITS * n + n / u16::MAX + u64::MIN",
        "fn f(n: usize)",
    ))
    .unwrap();
    for want in ["(255 : Nat)", "(32 : Nat)", "(65535 : Nat)", "(0 : Nat)"] {
        assert!(l.spec_lean.contains(want), "missing {want}:\n{}", l.spec_lean);
    }
    let r = expect_error(&wrap("max_steps = i32::MAX", "fn f()"), "E_ANNEAL_SPEC_TYPE_MISMATCH");
    assert!(r.contains("signed `i32::MAX`"), "{r}");
    // A nonzero constant guards a divisor like a nonzero literal; `u8::MIN`,
    // which is zero, does not, but comparing a divisor against a zero constant
    // (`d != u8::MIN`, `d > usize::MIN`, `u8::MIN < d`) proves `d != 0` just
    // like comparing against `0` (while `i8::MIN` is -128, not zero).
    lower_one(&wrap("ensures(|r| math(r) == math(a / u8::MAX))", "fn f(a: u8) -> u8")).unwrap();
    lower_one(&wrap(
        "requires(d != u8::MIN), ensures(|r| math(r) == math(a / d))",
        "fn f(a: u8, d: u8) -> u8",
    ))
    .unwrap();
    lower_one(&wrap(
        "requires(d > usize::MIN), ensures(|r| math(r) == math(a / d))",
        "fn f(a: usize, d: usize) -> usize",
    ))
    .unwrap();
    lower_one(&wrap(
        "requires(u8::MIN < d), ensures(|r| math(r) == math(a / d))",
        "fn f(a: u8, d: u8) -> u8",
    ))
    .unwrap();
    expect_error(
        &wrap(
            "requires(d != i8::MIN), ensures(|r| math(r) == math(a / d))",
            "fn f(a: i8, d: i8) -> i8",
        ),
        "E_ANNEAL_UNGUARDED_SPEC_DIV",
    );
    expect_error(
        &wrap(
            "requires(d > i8::MIN), ensures(|r| math(r) == math(a / d))",
            "fn f(a: i8, d: i8) -> i8",
        ),
        "E_ANNEAL_UNGUARDED_SPEC_DIV",
    );
    expect_error(
        &wrap("ensures(|r| math(r) == math(a / u8::MIN))", "fn f(a: u8) -> u8"),
        "E_ANNEAL_UNGUARDED_SPEC_DIV",
    );
    expect_error(&wrap("max_steps = n / u32::MIN", "fn f(n: u32)"), "E_ANNEAL_UNGUARDED_SPEC_DIV");
}

#[test]
fn only_integer_constants_may_be_named() {
    for (clause, code) in [
        ("requires(a <= usize::max_value)", "E_ANNEAL_SPEC_UNSUPPORTED_EXPR"),
        ("requires(a <= usize::MAX::X)", "E_ANNEAL_SPEC_UNSUPPORTED_EXPR"),
        ("requires(a <= usize::MAX())", "E_ANNEAL_SPEC_UNSUPPORTED_EXPR"),
        ("requires(a <= core::usize::MAX)", "E_ANNEAL_SPEC_UNSUPPORTED_EXPR"),
        ("requires(a <= Self::MAX)", "E_ANNEAL_SPEC_UNSUPPORTED_EXPR"),
        ("requires(a <= f32::MAX)", "E_ANNEAL_SPEC_UNSUPPORTED_EXPR"),
        ("requires(a <= u08::MAX)", "E_ANNEAL_SPEC_UNSUPPORTED_EXPR"),
        ("requires(a <= i032::MIN)", "E_ANNEAL_SPEC_UNSUPPORTED_EXPR"),
        ("requires(a <= u008::BITS)", "E_ANNEAL_SPEC_UNSUPPORTED_EXPR"),
        ("requires(a <= usize::)", "E_ANNEAL_SPEC_SYNTAX"),
    ] {
        let r = expect_error(&wrap(clause, "fn f(a: usize)"), code);
        if code == "E_ANNEAL_SPEC_UNSUPPORTED_EXPR" {
            assert!(r.contains("`T::MIN`, `T::MAX`"), "{clause}: {r}");
        }
    }
    expect_error(&wrap("requires(a == 0)", "fn f(a: u08)"), "E_ANNEAL_UNSUPPORTED_TYPE");
}

#[test]
fn wide_integer_intrinsics_use_exact_moduli() {
    let w = lower_one(&wrap("ensures(|r| r == wrapping_add(a, 1u128))", "fn f(a: u128) -> u128"))
        .unwrap();
    assert!(w.spec_lean.contains("340282366920938463463374607431768211456)"), "{}", w.spec_lean);
    let o = lower_one(&wrap("requires(no_overflow_add(a, b))", "fn f(a: i128, b: i128)")).unwrap();
    let h = "170141183460469231731687303715884105728";
    assert!(o.spec_lean.contains(&format!("((Int.neg {h}) ≤")), "{}", o.spec_lean);
    assert!(o.spec_lean.contains(&format!("< {h})")), "{}", o.spec_lean);
    let s =
        lower_one(&wrap("ensures(|r| r == wrapping_mul(a, b))", "fn f(a: i128, b: i128) -> i128"))
            .unwrap();
    let want = format!("+ {h}) 340282366920938463463374607431768211456 - {h})");
    assert!(s.spec_lean.contains(&want), "{}", s.spec_lean);
    let t = lower_one(&wrap(
        "ensures(|r| r == saturating_mul(a, b))",
        "fn f(a: i128, b: i128) -> i128",
    ))
    .unwrap();
    let want = format!(
        "if «saturating» < (Int.neg {h}) then (Int.neg {h}) else if \
         (170141183460469231731687303715884105727 : Int) < «saturating»"
    );
    assert!(t.spec_lean.contains(&want), "{}", t.spec_lean);
    let u = lower_one(&wrap(
        "ensures(|r| r == saturating_add(a, b))",
        "fn f(a: u128, b: u128) -> u128",
    ))
    .unwrap();
    assert!(
        u.spec_lean.contains("if (340282366920938463463374607431768211455 : Int) < «saturating»"),
        "{}",
        u.spec_lean
    );
}

#[test]
fn bitwise_operators_and_shifts_lower_exactly() {
    let x = "(specInt (specArg q 0))";
    let y = "(specInt (specArg q 1))";
    let lean = |clause: &str, sig: &str| {
        lower_one(&wrap(clause, sig)).unwrap_or_else(|e| panic!("{clause}: {e:?}")).spec_lean
    };
    let has = |text: &str, want: &str| assert!(text.contains(want), "missing {want} in\n{text}");
    // Unsigned operands are their own bits.
    has(
        &lean("ensures(|r| r == a & b)", "fn f(a: u8, b: u8) -> u8"),
        &format!("(Int.ofNat ((Int.toNat {x}) &&& (Int.toNat {y})))"),
    );
    has(
        &lean("ensures(|r| r == a | b)", "fn f(a: u16, b: u16) -> u16"),
        &format!("(Int.ofNat ((Int.toNat {x}) ||| (Int.toNat {y})))"),
    );
    // Signed operands act through their two's-complement bits.
    has(
        &lean("ensures(|r| r == a ^ b)", "fn f(a: i8, b: i8) -> i8"),
        &format!(
            "(Trusted.MirSemantics.intEmod (Int.ofNat ((Int.toNat (Trusted.MirSemantics.intEmod \
             {x} 256)) ^^^ (Int.toNat (Trusted.MirSemantics.intEmod {y} 256))) + 128) 256 - 128)"
        ),
    );
    has(&lean("ensures(|r| r == !a)", "fn f(a: u8) -> u8"), &format!("((255 : Int) - {x})"));
    has(&lean("ensures(|r| r == !a)", "fn f(a: i32) -> i32"), &format!("(Int.neg {x} - 1)"));
    // Shifts by a constant amount below the width.
    has(
        &lean("ensures(|r| r == a << 3)", "fn f(a: u8) -> u8"),
        &format!("(Trusted.MirSemantics.intEmod (Trusted.MirSemantics.intShiftLeft {x} 3) 256)"),
    );
    has(
        &lean("ensures(|r| r == a << 7u32)", "fn f(a: i8) -> i8"),
        &format!(
            "(Trusted.MirSemantics.intEmod (Trusted.MirSemantics.intShiftLeft {x} 7 + 128) 256 \
             - 128)"
        ),
    );
    // A `let`-bound amount is written as its binding.
    has(
        &lean("ensures(|r| { let k: u8 = 2; r == a >> k })", "fn f(a: i64) -> i64"),
        &format!("(Trusted.MirSemantics.intShiftRight {x} (Int.toNat «k»))"),
    );
    // The masked shifts take any `u32` amount.
    has(
        &lean("ensures(|r| r == wrapping_shl(a, n))", "fn f(a: u16, n: u32) -> u16"),
        &format!(
            "(Trusted.MirSemantics.intEmod (Trusted.MirSemantics.intShiftLeft {x} (Int.toNat \
             (Trusted.MirSemantics.intEmod {y} 16))) 65536)"
        ),
    );
    has(
        &lean("ensures(|r| r == wrapping_shr(a, 9))", "fn f(a: i8) -> i8"),
        &format!(
            "(Trusted.MirSemantics.intShiftRight {x} (Int.toNat (Trusted.MirSemantics.intEmod \
             (9 : Int) 8)))"
        ),
    );
    // Rust's precedence: shifts bind tighter than `&`, which binds tighter
    // than `^`, `|`, and comparisons.
    lean("requires(a & 1u8 << 2 == 4u8)", "fn f(a: u8)");
    lean("requires(a | b ^ a & b == a | b)", "fn f(a: u8, b: u8)");
    // Inside `math`, operands keep their machine types and results are
    // mathematical.
    lean("ensures(|r| math(r) == math(a & b) + math(a << 1))", "fn f(a: u8, b: u8) -> u8");
    lean("ensures(|r| { let n: u8 = !a; math(r) == math(n) + 1 })", "fn f(a: u8) -> u8");
    lean("ensures(|r| r == if a & 1u8 == 0u8 { 1u8 } else { 0u8 })", "fn f(a: u8) -> u8");
    lean("max_steps = (n & 255u32) + (n >> 4) + !m", "fn f(n: u32, m: u8)");
    for (clause, code) in [
        ("max_steps = a & b", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
        ("max_steps = !a", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
    ] {
        expect_error(&wrap(clause, "fn f(a: i8, b: i8)"), code);
    }
}

#[test]
fn bitwise_operators_and_shifts_are_checked_strictly() {
    let sig = "fn f(a: u8, b: u16, c: bool, i: i8, n: u32) -> u8";
    for (clause, code) in [
        ("requires(a & b == 0u8)", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
        ("requires(a & math(a) == 0u8)", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
        ("requires(1 & 3 == 1u8)", "E_ANNEAL_SPEC_TYPE_ANNOTATION_NEEDED"),
        ("requires(a | 256 == 0u8)", "E_ANNEAL_SPEC_LITERAL_RANGE"),
        ("requires(c & c)", "E_ANNEAL_EAGER_CLAUSE_JOIN"),
        ("requires(c ^ c)", "E_ANNEAL_SPEC_UNSUPPORTED_EXPR"),
        ("requires(math(!a) == 0)", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
        ("requires((!5) == 0u8)", "E_ANNEAL_SPEC_TYPE_ANNOTATION_NEEDED"),
        ("requires((!()) == ())", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
        ("requires(a << n == 0u8)", "E_ANNEAL_AMBIGUOUS_SPEC_ARITH"),
        ("requires(a >> 8 == 0u8)", "E_ANNEAL_SPEC_LITERAL_RANGE"),
        ("requires(i << -1 == 0i8)", "E_ANNEAL_SPEC_LITERAL_RANGE"),
        ("requires(1 << 3 == 8u8)", "E_ANNEAL_SPEC_TYPE_ANNOTATION_NEEDED"),
        ("requires(c << 1 == c)", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
        ("requires(a << c == 0u8)", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
        ("requires(math(a) << 1 == 0)", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
        ("requires(wrapping_shl(a, a) == 0u8)", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
        ("requires(wrapping_shl(a) == 0u8)", "E_ANNEAL_SPEC_ARITY"),
        ("requires(wrapping_shr(5, n) == 0u8)", "E_ANNEAL_SPEC_TYPE_ANNOTATION_NEEDED"),
        ("requires(saturating_shl(a, n) == 0u8)", "E_ANNEAL_SPEC_UNKNOWN_FN"),
    ] {
        expect_error(&wrap(clause, sig), code);
    }
    let r = expect_error(&wrap("requires(a << n == 0u8)", sig), "E_ANNEAL_AMBIGUOUS_SPEC_ARITH");
    assert!(r.contains("`wrapping_shl(a, n)`"), "{r}");
    let r = expect_error(&wrap("requires(math(!a) == 0)", sig), "E_ANNEAL_SPEC_TYPE_MISMATCH");
    assert!(r.contains("depends on the operand's width"), "{r}");
    let r = expect_error(&wrap("requires(a >> 8 == 0u8)", sig), "E_ANNEAL_SPEC_LITERAL_RANGE");
    assert!(r.contains("shifts by less than 8"), "{r}");
    // The largest in-range amount is accepted, of any integer type.
    lower_one(&wrap("requires(a >> 7u64 == 0u8 && i << 7i8 == 0i8)", sig)).unwrap();
}

#[test]
fn saturating_negation_and_abs_diff_intrinsics_lower_exactly() {
    let x = "(specInt (specArg q 0))";
    let y = "(specInt (specArg q 1))";
    let lean = |clause: &str, sig: &str| {
        lower_one(&wrap(clause, sig)).unwrap_or_else(|e| panic!("{clause}: {e:?}")).spec_lean
    };
    let has = |text: &str, want: &str| assert!(text.contains(want), "missing {want} in\n{text}");
    // Saturating arithmetic binds the exact result once and clamps it to the
    // type's range.
    has(
        &lean("ensures(|r| r == saturating_add(a, b))", "fn f(a: u8, b: u8) -> u8"),
        &format!(
            "(let «saturating» : Int := {x} + {y}; if «saturating» < (0 : Int) then (0 : Int) \
             else if (255 : Int) < «saturating» then (255 : Int) else «saturating»)"
        ),
    );
    has(
        &lean("ensures(|r| r == saturating_sub(a, b))", "fn f(a: i8, b: i8) -> i8"),
        &format!(
            "(let «saturating» : Int := {x} - {y}; if «saturating» < (Int.neg 128) then \
             (Int.neg 128) else if (127 : Int) < «saturating» then (127 : Int) else «saturating»)"
        ),
    );
    has(
        &lean("ensures(|r| r == saturating_neg(a))", "fn f(a: i16) -> i16"),
        &format!(
            "(let «saturating» : Int := Int.neg {x}; if «saturating» < (Int.neg 32768) then \
             (Int.neg 32768) else if (32767 : Int) < «saturating» then (32767 : Int) else \
             «saturating»)"
        ),
    );
    // Nesting binds each operand once rather than duplicating it.
    let nested = lean(
        "ensures(|r| r == saturating_add(saturating_mul(a, b), a))",
        "fn f(a: u8, b: u8) -> u8",
    );
    assert_eq!(nested.matches("(specArg q 1)").count(), 1, "{nested}");
    assert_eq!(nested.matches("(specArg q 0)").count(), 2, "{nested}");
    // Negation wraps and overflows like `wrapping_sub(0, a)`.
    has(
        &lean("ensures(|r| r == wrapping_neg(a))", "fn f(a: u8) -> u8"),
        &format!("(Trusted.MirSemantics.intEmod (Int.neg {x}) 256)"),
    );
    has(
        &lean("ensures(|r| r == wrapping_neg(a))", "fn f(a: i8) -> i8"),
        &format!("(Trusted.MirSemantics.intEmod (Int.neg {x} + 128) 256 - 128)"),
    );
    has(
        &lean("requires(no_overflow_neg(a))", "fn f(a: u32)"),
        &format!("((0 : Int) ≤ Int.neg {x} ∧ Int.neg {x} < 4294967296)"),
    );
    has(
        &lean("requires(no_overflow_neg(a))", "fn f(a: i8)"),
        &format!("((Int.neg 128) ≤ Int.neg {x} ∧ Int.neg {x} < 128)"),
    );
    // `abs_diff` is the exact distance, of the unsigned type of the
    // operands' width.
    has(
        &lean("ensures(|r| r == abs_diff(a, b))", "fn f(a: i8, b: i8) -> u8"),
        &format!("((specInt out.ret) = (Int.ofNat (Int.natAbs ({x} - {y}))))"),
    );
    lean("ensures(|r| r == abs_diff(a, b))", "fn f(a: isize, b: isize) -> usize");
    lean("ensures(|r| r == abs_diff(a, 7))", "fn f(a: u64) -> u64");
    let r = expect_error(
        &wrap("ensures(|r| r == abs_diff(a, b))", "fn f(a: i8, b: i8) -> i8"),
        "E_ANNEAL_SPEC_TYPE_MISMATCH",
    );
    assert!(r.contains("`i8` and `u8`"), "{r}");
    // Inside `math`, the results are mathematical integers, but the
    // operands keep their machine types.
    lean("ensures(|r| math(r) == math(saturating_add(a, b)) + 1)", "fn f(a: u8, b: u8) -> u8");
    lean(
        "ensures(|r| math(r) == math(abs_diff(a, b) + wrapping_neg(a)))",
        "fn f(a: i8, b: i8) -> u8",
    );
    lean("ensures(|r| r == if no_overflow_neg(a) { 1u8 } else { 0u8 })", "fn f(a: i8) -> u8");
    lean("max_steps = abs_diff(a, b) + saturating_add(n, 1u32)", "fn f(a: i32, b: i32, n: u32)");
    expect_error(
        &wrap("max_steps = saturating_neg(a)", "fn f(a: i32)"),
        "E_ANNEAL_SPEC_TYPE_MISMATCH",
    );
}

#[test]
fn new_arithmetic_intrinsics_are_checked_strictly() {
    let sig = "fn f(a: u8, b: bool, c: u16, i: i8) -> u8";
    for (clause, code) in [
        ("requires(saturating_neg(a) == 0u8)", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
        ("requires(wrapping_neg(5) == 0u8)", "E_ANNEAL_SPEC_TYPE_ANNOTATION_NEEDED"),
        (
            "requires(wrapping_neg(if b { 1 } else { 2 }) == 0u8)",
            "E_ANNEAL_SPEC_TYPE_ANNOTATION_NEEDED",
        ),
        ("requires(saturating_neg(math(i)) == 0)", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
        ("requires(no_overflow_neg(b))", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
        ("requires(wrapping_neg(a, a) == 0u8)", "E_ANNEAL_SPEC_ARITY"),
        ("requires(saturating_add(a) == 0u8)", "E_ANNEAL_SPEC_ARITY"),
        ("requires(abs_diff(a, a, a) == 0u8)", "E_ANNEAL_SPEC_ARITY"),
        ("requires(saturating_add(a, c) == 0u8)", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
        ("requires(saturating_sub(math(a), a) == 0u8)", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
        ("requires(abs_diff(b, b) == 0u8)", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
        ("requires(abs_diff(a, math(a)) == 0u8)", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
        ("requires(abs_diff(1, 2) == 0u8)", "E_ANNEAL_SPEC_TYPE_ANNOTATION_NEEDED"),
        ("requires(saturating_add(a, 256) == 0u8)", "E_ANNEAL_SPEC_LITERAL_RANGE"),
        ("requires(saturating_div(a, a) == 0u8)", "E_ANNEAL_SPEC_UNKNOWN_FN"),
        ("requires(wrapping_abs(i) == 0i8)", "E_ANNEAL_SPEC_UNKNOWN_FN"),
        ("requires({ let abs_diff = a; abs_diff == 0u8 })", "E_ANNEAL_RESERVED_PARAM_NAME"),
        ("requires({ let saturating_x = a; saturating_x == 0u8 })", "E_ANNEAL_RESERVED_PARAM_NAME"),
        (
            "requires(match a { saturating_x => saturating_x == 0u8 })",
            "E_ANNEAL_RESERVED_PARAM_NAME",
        ),
    ] {
        expect_error(&wrap(clause, sig), code);
    }
    let r = expect_error(
        &wrap("requires(saturating_neg(a) == 0u8)", sig),
        "E_ANNEAL_SPEC_TYPE_MISMATCH",
    );
    assert!(r.contains("`saturating_neg` needs a signed integer, found `u8`"), "{r}");
    let r = expect_error(&wrap("requires(abs_dif(a, a) == 0u8)", sig), "E_ANNEAL_SPEC_UNKNOWN_FN");
    assert!(r.contains("did you mean `abs_diff`?"), "{r}");
    // A name that only starts like an intrinsic is an ordinary binding.
    lower_one(&wrap("requires({ let saturating = a; saturating == 0u8 })", sig)).unwrap();
    for helper in ["abs_diff", "saturating_add", "saturating_pow"] {
        expect_error(
            &format!(
                "anneal::external_spec! {{
                    #[anneal::pure] fn {helper}(a: u8, b: u8) -> u8 {{ a }}
                    #[anneal::spec(ensures(|r| r == {helper}(x, x)))] fn f(x: u8) -> u8;
                }}"
            ),
            "E_ANNEAL_RESERVED_HELPER_NAME",
        );
    }
}

#[test]
fn targets_are_validated_and_honored_in_both_forms() {
    let injected = "#[cfg_attr(anneal, anneal::spec(target = \"x /- -/ -/ theorem t : True := \
                    trivial --\", total))]\nfn f() {}\n";
    expect_error(injected, "E_ANNEAL_INVALID_TARGET");
    expect_error(&wrap("target = \"a\\\"b\"", "fn f()"), "E_ANNEAL_INVALID_TARGET");
    let ext = lower_one(
        "anneal::external_spec! { mod m { #[anneal::spec(target = \"other::g\", total)] fn f(); } }",
    )
    .unwrap();
    let inline = lower(&[Source {
        label: "lib.rs".into(),
        text: "mod m { #[cfg_attr(anneal, anneal::spec(target = \"other::g\", total))] fn f() {} }"
            .into(),
        module: Vec::new(),
    }])
    .unwrap_or_else(|_| panic!("inline form failed"));
    assert!(ext.spec_lean.contains("\"rust-path-v1::other::g\""), "{}", ext.spec_lean);
    assert_eq!(ext.spec_lean, inline.spec_lean);
}

#[test]
fn anneal_items_in_unread_positions_are_errors() {
    for text in [
        "#[cfg_attr(all(anneal), anneal::spec(total))]\nfn f() {}\n",
        "#[cfg_attr(anneal, inline, anneal::spec(total))]\nfn f() {}\n",
        "fn outer() { anneal::external_spec! { #[anneal::spec(total)] fn f(); } }\n\
         #[cfg_attr(anneal, anneal::spec(total))]\nfn g() {}\n",
        "#[cfg_attr(anneal, anneal::spec(total))]\nstruct S;\n\
         #[cfg_attr(anneal, anneal::spec(total))]\nfn g() {}\n",
    ] {
        expect_error(text, "E_ANNEAL_IGNORED_ATTRIBUTE");
    }
    expect_error(
        "anneal::external_spec! { #[anneal::vacuous_ok(reason = \"a\")] \
         #[anneal::vacuous_ok(reason = \"b\")] #[anneal::spec(total)] fn f(); }",
        "E_ANNEAL_DUPLICATE_CLAUSE",
    );
    expect_error(
        "#[cfg_attr(anneal, anneal::vacuous_ok(reason = \"r\"))]\nfn f() {}\n\
         #[cfg_attr(anneal, anneal::spec(total))]\nfn g() {}\n",
        "E_ANNEAL_VACUOUS_OK_REASON",
    );
    expect_error(
        "anneal::external_spec! { #[anneal::vacuous_ok(reason = \"a\u{202e}b\")] \
         #[anneal::spec(total)] fn f(); }",
        "E_ANNEAL_VACUOUS_OK_REASON",
    );
}

#[test]
fn helpers_cannot_shadow_intrinsics() {
    expect_error(
        "anneal::external_spec! {
            #[anneal::pure] fn wrapping_add(a: u8, b: u8) -> u8 { a }
            #[anneal::spec(ensures(|r| r == wrapping_add(x, x)))] fn f(x: u8) -> u8;
        }",
        "E_ANNEAL_RESERVED_HELPER_NAME",
    );
}

#[test]
fn safety_guards_do_not_guard_behavioral_preconditions() {
    expect_error(
        &wrap("safety_requires(b != 0u8), requires(math(a / b) == 1)", "unsafe fn f(a: u8, b: u8)"),
        "E_ANNEAL_UNGUARDED_SPEC_DIV",
    );
    lower_one(&wrap(
        "requires(b != 0u8), ensures(|r| math(r) == math(a / b))",
        "fn f(a: u8, b: u8) -> u8",
    ))
    .unwrap();
}

#[test]
fn importing_or_renaming_anneal_is_rejected() {
    for text in [
        "use anneal::*;\n#[spec(requires(false))]\nfn f() {}\n",
        "use anneal::{spec};\n#[spec(requires(false))]\nfn f() {}\n",
        "use anneal as an;\n#[an::spec(requires(false))]\nfn f() {}\n",
        "extern crate anneal as an;\n#[an::spec(requires(false))]\nfn f() {}\n",
    ] {
        expect_error(text, "E_ANNEAL_UNSUPPORTED_IMPORT");
    }
    // A plain `use anneal::spec;` imports a name the lowering would not
    // follow, so it is reported as an unread path.
    expect_error("use anneal::spec;\n#[spec(total)]\nfn f() {}\n", "E_ANNEAL_IGNORED_ATTRIBUTE");
}

#[test]
fn cargo_renamed_anneal_paths_are_rejected() {
    for text in [
        "#[alias::spec(total)]\nfn f() {}\n",
        "#[cfg_attr(anneal, alias::spec(total))]\nfn f() {}\n",
        "#[alias::pure]\nfn helper() -> bool { true }\n",
        "#[alias::vacuous_ok(reason = \"empty\")]\nfn f() {}\n",
        "alias::external_spec! { #[spec(total)] fn f(); }\n",
    ] {
        expect_error(text, "E_ANNEAL_UNSUPPORTED_IMPORT");
    }
    lower_one("#[allow(clippy::all)]\n#[cfg_attr(anneal, anneal::spec(total))]\nfn f() {}\n")
        .unwrap();
}

#[test]
fn negative_and_extreme_integer_literals_lower_without_overflow() {
    let mins = [
        ("i8", "-128i8", "(Int.neg 128)"),
        ("i16", "-32768i16", "(Int.neg 32768)"),
        ("i32", "-2147483648i32", "(Int.neg 2147483648)"),
        ("i64", "-9223372036854775808i64", "(Int.neg 9223372036854775808)"),
        (
            "i128",
            "-170141183460469231731687303715884105728i128",
            "(Int.neg 170141183460469231731687303715884105728)",
        ),
    ];
    for (ty, lit, lean) in mins {
        let l = lower_one(&wrap(&format!("ensures(|r| r == {lit})"), &format!("fn f() -> {ty}")))
            .unwrap();
        assert!(l.spec_lean.contains(lean), "{ty}: {}", l.spec_lean);
    }
    let untyped_i128_min = lower_one(&wrap(
        "requires(a == -170141183460469231731687303715884105728)",
        "fn f(a: i128)",
    ))
    .unwrap();
    assert!(
        untyped_i128_min.spec_lean.contains("(Int.neg 170141183460469231731687303715884105728)"),
        "{}",
        untyped_i128_min.spec_lean
    );
    let u128_max = lower_one(&wrap(
        "requires(a == 340282366920938463463374607431768211455u128)",
        "fn f(a: u128)",
    ))
    .unwrap();
    assert!(
        u128_max.spec_lean.contains("(340282366920938463463374607431768211455 : Int)"),
        "{}",
        u128_max.spec_lean
    );
    let double_neg = lower_one(&wrap(
        "requires(math(- -170141183460469231731687303715884105728) == math(a))",
        "fn f(a: u128)",
    ))
    .unwrap();
    assert!(
        double_neg.spec_lean.contains("(170141183460469231731687303715884105728 : Int)"),
        "{}",
        double_neg.spec_lean
    );
    for (attr, sig) in [
        ("requires(a == -(128i8))", "fn f(a: i8)"),
        ("requires(a == -129i8)", "fn f(a: i8)"),
        ("requires(a == -170141183460469231731687303715884105729i128)", "fn f(a: i128)"),
        ("requires(a == -170141183460469231731687303715884105729)", "fn f(a: i128)"),
    ] {
        expect_error(&wrap(attr, sig), "E_ANNEAL_SPEC_LITERAL_RANGE");
    }
    expect_error(&wrap("requires(a == -5u8)", "fn f(a: u8)"), "E_ANNEAL_AMBIGUOUS_SPEC_ARITH");
}

#[test]
fn duplicate_parameter_names_are_rejected() {
    for text in [
        "anneal::external_spec! { #[anneal::spec(total)] fn f(x: u8, x: u16); }",
        "#[cfg_attr(anneal, anneal::spec(total))] fn f(x: u8, x: u16) {}",
        "anneal::external_spec! { #[anneal::pure] fn h(x: u8, x: u8) -> bool { true } #[anneal::spec(requires(h(a, a)))] fn f(a: u8); }",
    ] {
        expect_error(text, "E_ANNEAL_SPEC_SYNTAX");
    }
}

#[test]
fn helper_parameters_cannot_capture_generated_names() {
    // Helper parameters become Lean binders. References to generated and
    // library names are qualified, so parameters named like the unqualified
    // names (`pure_g`, `intTdiv`, `Val`) are harmless.
    let l = lower_one(
        "anneal::external_spec! {
            #[anneal::pure] fn g() -> u8 { 1u8 }
            #[anneal::pure] fn h(pure_g: u8) -> bool { pure_g == g() }
            #[anneal::pure] fn n(intTdiv: i8, Val: i8) -> bool { math(intTdiv / 2) == math(Val % 2) && () == () }
            #[anneal::spec(requires(h(x) && n(0i8, 0i8)))] fn f(x: u8);
        }",
    )
    .unwrap();
    for want in [
        "noncomputable def pure_h («pure_g» : Int) : Prop :=\n  («pure_g» = Spec.pure_g)",
        "noncomputable def pure_n («intTdiv» : Int) («Val» : Int) : Prop :=\n  \
         (((Trusted.MirSemantics.intTdiv «intTdiv» (2 : Int)) = \
         (Trusted.MirSemantics.intTmod «Val» (2 : Int))) ∧ \
         (Trusted.MirSemantics.Val.unit = Trusted.MirSemantics.Val.unit))",
        "(Spec.pure_h (specInt (specArg q 0)))",
    ] {
        assert!(l.spec_lean.contains(want), "missing {want:?} in\n{}", l.spec_lean);
    }
    // A parameter named after the root of a qualified reference would capture
    // it (`True`, or `Trusted` in `Trusted.MirSemantics.intTdiv`), and the
    // `Spec.lean` policy rejects `_root_`.
    for name in ["True", "False", "Int", "Trusted", "Spec", "Specs", "_root_"] {
        let msg = expect_error(
            &format!(
                "anneal::external_spec! {{
                    #[anneal::pure] fn r({name}: bool) -> bool {{ {name} }}
                    #[anneal::spec(requires(r(x)))] fn f(x: bool);
                }}"
            ),
            "E_ANNEAL_RESERVED_PARAM_NAME",
        );
        assert!(msg.contains(&format!("`{name}` cannot name")), "{msg}");
    }
}

#[test]
fn spec_lean_names_only_library_functions_in_scope() {
    // `Spec.lean` imports only `Trusted.MirSemantics` on top of `prelude`, so
    // division and wrapping must not use `Init.Data.Int.DivMod`'s `Int.tdiv`,
    // `Int.tmod`, or `Int.emod`.
    let l = lower_one(&wrap(
        "requires(d != 0u8), ensures(|r| math(r) == math(n / d) && math(n % d) < math(d) \
         && wrapping_add(r, d) != wrapping_sub(r, d) && wrapping_mul(r, d) == r)",
        "fn f(n: u8, d: u8) -> u8",
    ))
    .unwrap();
    for banned in ["Int.tdiv", "Int.tmod", "Int.emod"] {
        assert!(!l.spec_lean.contains(banned), "{banned} in\n{}", l.spec_lean);
    }
    for want in ["intTdiv", "intTmod", "intEmod"] {
        assert!(
            l.spec_lean.contains(&format!("Trusted.MirSemantics.{want} ")),
            "{want} missing in\n{}",
            l.spec_lean
        );
    }
}

#[test]
fn non_root_module_trait_impl_requires_target() {
    expect_error(
        "mod inner { trait Tr { fn g(self); } impl Tr for usize { #[cfg_attr(anneal, anneal::spec(total))] fn g(self) {} } }",
        "E_ANNEAL_TARGET_REQUIRED",
    );
    let ok = lower_one(
        "mod inner { trait Tr { fn g(self); } impl Tr for usize { #[cfg_attr(anneal, anneal::spec(target = \"<usize as inner::Tr>::g\", total))] fn g(self) {} } }",
    )
    .unwrap();
    assert!(ok.spec_lean.contains("\"rust-path-v1::<usize as inner::Tr>::g\""), "{}", ok.spec_lean);
}

#[test]
fn contract_signature_is_emitted_in_spec_lean() {
    let safe = lower_one(&wrap("total", "fn f(a: u8, b: bool) -> i128")).unwrap();
    assert!(
        safe.spec_lean.contains(
            "signature := some { isUnsafe := false, params := [.int .i8 false, .bool], ret := .int .i128 true }"
        ),
        "{}",
        safe.spec_lean
    );
    let unsafe_never = lower_one(&wrap("may_diverge", "unsafe fn spin() -> !")).unwrap();
    assert!(
        unsafe_never
            .spec_lean
            .contains("signature := some { isUnsafe := true, params := [], ret := .never }"),
        "{}",
        unsafe_never.spec_lean
    );
}

fn lower_selected(text: &str, opts: &Options) -> Result<Lowered, Vec<String>> {
    let sources = [src("spec.rs", text)];
    lower_with(&sources, opts)
        .map_err(|errs| errs.iter().map(|e| e.diag.code.to_string()).collect())
}

/// Three items in two claims, with a helper chain used by only one claim.
const CLAIMS_SPEC: &str = "anneal::external_spec! {
    #[anneal::pure] fn nonzero(x: u8) -> bool { x != 0u8 }
    #[anneal::pure] fn positive(x: u8) -> bool { nonzero(x) }
    #[anneal::pure] fn unused(x: u8) -> bool { x == 1u8 }
    #[anneal::spec(claim = \"pair\", requires(positive(x)), ensures(|r| r == x))]
    fn a(x: u8) -> u8;
    #[anneal::spec(claim = \"pair\", ensures(|r| r == x))]
    fn b(x: u8) -> u8;
    mod m {
        #[anneal::spec(ensures(|r| r == x))]
        fn c(x: u8) -> u8;
    }
}";

#[test]
fn claim_clause_names_a_claim_and_instantiate_is_reserved() {
    lower_one(&wrap("claim = \"zc01_usize\", total", "fn f()")).unwrap();
    for bad in ["Spec", "specs", "1x", "a-b", "", "namespace"] {
        expect_error(&wrap(&format!("claim = \"{bad}\""), "fn f()"), "E_ANNEAL_INVALID_CLAIM");
    }
    expect_error(
        &wrap(&format!("claim = \"{}\"", "a".repeat(65)), "fn f()"),
        "E_ANNEAL_INVALID_CLAIM",
    );
    expect_error(&wrap("claim = x", "fn f()"), "E_ANNEAL_SPEC_SYNTAX");
    expect_error(&wrap("claim = \"a\", claim = \"b\"", "fn f()"), "E_ANNEAL_DUPLICATE_CLAUSE");
    expect_error(
        &wrap("instantiate = [[\"u8\"], [\"u32\"]]", "fn f()"),
        "E_ANNEAL_UNSUPPORTED_CLAUSE",
    );
    for bad in ["[]", "[[]]", "[\"u8\"]", "[[u8]]", "[[\"\"]]"] {
        expect_error(&wrap(&format!("instantiate = {bad}"), "fn f()"), "E_ANNEAL_SPEC_SYNTAX");
    }
}

#[test]
fn singleton_claims_mangle_item_paths() {
    assert_eq!(
        mangle_slug("<usize as PointerMetadata>::from_elem_count"),
        "impl_PointerMetadata_for_usize__from_elem_count"
    );
    assert_eq!(mangle_slug("util::macros::__unsafe"), "util__macros____unsafe");
    assert_eq!(mangle_slug("layout::DstLayout::add"), "layout__DstLayout__add");
    assert_eq!(
        mangle_slug("<() as PointerMetadata>::to_elem_count"),
        "impl_PointerMetadata_for_unit__to_elem_count"
    );
    assert_eq!(mangle_slug("<[u8] as Tr>::f"), "impl_Tr_for__u8___f");
    assert_eq!(mangle_slug("_f"), "c__f");
}

#[test]
fn selection_checks_everything_but_lowers_only_the_selection() {
    let all = lower_one(CLAIMS_SPEC).unwrap();
    // No selection is exactly `lower`.
    let same = lower_selected(CLAIMS_SPEC, &Options::default()).unwrap();
    assert_eq!(all.spec_lean, same.spec_lean);
    assert_eq!(all.span_map, same.span_map);

    let pair =
        lower_selected(CLAIMS_SPEC, &Options { claim: Some("pair".into()), ..Options::default() })
            .unwrap();
    assert!(pair.spec_lean.contains("rust-path-v1::a\""), "{}", pair.spec_lean);
    assert!(pair.spec_lean.contains("rust-path-v1::b\""), "{}", pair.spec_lean);
    assert!(!pair.spec_lean.contains("rust-path-v1::m::c\""), "{}", pair.spec_lean);
    // The helper cone: `positive` and the `nonzero` it calls, not `unused`.
    assert!(pair.spec_lean.contains("def pure_positive"), "{}", pair.spec_lean);
    assert!(pair.spec_lean.contains("def pure_nonzero"), "{}", pair.spec_lean);
    assert!(!pair.spec_lean.contains("pure_unused"), "{}", pair.spec_lean);

    // `m::c` is alone in its singleton claim and reaches no helper.
    let c =
        lower_selected(CLAIMS_SPEC, &Options { claim: Some("m__c".into()), ..Options::default() })
            .unwrap();
    assert!(c.spec_lean.contains("rust-path-v1::m::c\""), "{}", c.spec_lean);
    assert!(!c.spec_lean.contains("def pure_"), "{}", c.spec_lean);
    let by_target = lower_selected(
        CLAIMS_SPEC,
        &Options { targets: vec!["m::c".into()], ..Options::default() },
    )
    .unwrap();
    assert_eq!(c.spec_lean, by_target.spec_lean);

    // The runtime definitions follow the selection too: only `flag` reads a
    // `bool` argument.
    let mixed = "anneal::external_spec! {
        #[anneal::spec(requires(b))] fn flag(b: bool);
        #[anneal::spec(ensures(|r| r == x))] fn id(x: u8) -> u8;
    }";
    let select = |c: &str| {
        lower_selected(mixed, &Options { claim: Some(c.into()), ..Options::default() })
            .unwrap()
            .spec_lean
    };
    assert!(lower_one(mixed).unwrap().spec_lean.contains("def specBool"));
    assert!(select("flag").contains("def specBool"));
    assert!(!select("id").contains("def specBool"), "{}", select("id"));
    assert!(select("id").contains("def specInt"), "{}", select("id"));

    // A helper called only from `max_steps` is still in the cone.
    let steps = "anneal::external_spec! {
        #[anneal::pure] fn extra(x: u16) -> u16 { x }
        #[anneal::spec(total, max_steps = extra(k))] fn g(k: u16);
        #[anneal::spec(total)] fn h();
    }";
    let g = lower_selected(steps, &Options { claim: Some("g".into()), ..Options::default() })
        .unwrap()
        .spec_lean;
    assert!(g.contains("def pure_extra"), "{g}");
    let h = lower_selected(steps, &Options { claim: Some("h".into()), ..Options::default() })
        .unwrap()
        .spec_lean;
    assert!(!h.contains("pure_extra"), "{h}");

    let codes = |opts: Options| lower_selected(CLAIMS_SPEC, &opts).err().unwrap();
    assert_eq!(
        codes(Options { targets: vec!["nope".into()], ..Options::default() }),
        ["E_ANNEAL_UNKNOWN_TARGET"]
    );
    assert_eq!(
        codes(Options {
            targets: vec!["m::c".into()],
            claim: Some("pair".into()),
            ..Options::default()
        }),
        ["E_ANNEAL_UNKNOWN_TARGET"]
    );
    assert_eq!(
        codes(Options { claim: Some("nope".into()), ..Options::default() }),
        ["E_ANNEAL_EMPTY_CLAIM"]
    );

    // An error in an unselected item still fails the selection.
    let broken = CLAIMS_SPEC.replace("fn c(x: u8) -> u8;", "fn c(x: u8) -> u8 { x }");
    assert!(lower_selected(&broken, &Options { claim: Some("pair".into()), ..Options::default() })
        .is_err());
}

#[test]
fn v2_modules_are_span_free_lean_modules() {
    let opts = Options {
        claim: Some("pair".into()),
        format: Format::V2Module,
        crate_slug: Some("zerocopy".into()),
        ..Options::default()
    };
    let m = lower_selected(CLAIMS_SPEC, &opts).unwrap();
    assert_eq!(m.module_path.as_deref(), Some("Specs/zerocopy/pair.lean"));
    assert_eq!(m.outputs(), [("Specs/zerocopy/pair.lean", m.spec_lean.as_str())]);
    assert!(m.span_map.is_empty());
    for needle in [
        "\nmodule\nprelude\npublic import Trusted.MirSemantics\n\n@[expose] public section\n\n\
         namespace Specs.«zerocopy».«pair»\n",
        "(Specs.«zerocopy».«pair».pure_positive (specInt (specArg q 0)))",
        "(Specs.«zerocopy».«pair».pure_nonzero «x»)",
        "\nend Specs.«zerocopy».«pair»\n\nend\n",
    ] {
        assert!(m.spec_lean.contains(needle), "missing {needle:?} in\n{}", m.spec_lean);
    }
    assert!(!m.spec_lean.contains("Spec.pure_"), "{}", m.spec_lean);
    // `max_steps` declarations that `Spec.lean` keeps private are public in a
    // module, whose public `specs` refers to them.
    let steps = wrap("total, max_steps = 2", "fn f()");
    assert!(lower_one(&steps).unwrap().spec_lean.contains("private noncomputable def"));
    let module =
        lower_selected(&steps, &Options { claim: Some("f".into()), ..opts.clone() }).unwrap();
    assert!(module.spec_lean.contains("noncomputable def contractSpecs"), "{}", module.spec_lean);
    assert!(!module.spec_lean.contains("private"), "{}", module.spec_lean);

    // A derived claim that is not a valid module name (`open` is a Lean
    // keyword) lowers in v1 but cannot name a v2 module.
    let open = wrap("ensures(|r| r == x)", "fn open(x: u8) -> u8");
    lower_one(&open).unwrap();
    assert_eq!(
        lower_selected(&open, &Options { claim: Some("open".into()), ..opts.clone() })
            .err()
            .unwrap(),
        ["E_ANNEAL_INVALID_OPTIONS"]
    );
    // Moving the items within the file leaves the module unchanged.
    let moved = format!("// a comment\n\n\n{}", CLAIMS_SPEC.replace("\n    ", "\n        "));
    assert_eq!(lower_selected(&moved, &opts).unwrap().spec_lean, m.spec_lean);

    for bad in [
        Options { format: Format::V2Module, ..Options::default() },
        Options { claim: None, ..opts.clone() },
        Options { crate_slug: Some("zero-copy".into()), ..opts.clone() },
        Options { claim: Some("panic".into()), ..opts.clone() },
        Options { format: Format::V1, ..opts.clone() },
    ] {
        assert_eq!(lower_selected(CLAIMS_SPEC, &bad).err().unwrap(), ["E_ANNEAL_INVALID_OPTIONS"]);
    }
}

#[test]
fn specification_paths_in_macro_arguments_are_rejected() {
    expect_error(
        "macro_rules! m { ($p:ident :: $q:ident) => { #[cfg($p)] fn f() {} } }\n\
         m!(anneal::spec);\n#[cfg_attr(anneal, anneal::spec(total))]\nfn g() {}",
        "E_ANNEAL_IGNORED_ATTRIBUTE",
    );
}

#[test]
fn derived_claims_may_not_collide() {
    let derived = "anneal::external_spec! {
        mod foo { #[anneal::spec(total)] fn bar(); }
        #[anneal::spec(total)] fn foo__bar();
    }";
    expect_error(derived, "E_ANNEAL_CLAIM_COLLISION");
    let explicit = "anneal::external_spec! {
        #[anneal::spec(total)] fn g();
        #[anneal::spec(claim = \"g\", total)] fn h();
    }";
    expect_error(explicit, "E_ANNEAL_CLAIM_COLLISION");
    // Explicit claims are shared on purpose.
    lower_one(CLAIMS_SPEC).unwrap();
}

#[test]
fn keyword_claims_are_escaped_in_modules() {
    let text = wrap("claim = \"syntax\", total", "fn f()");
    let opts = Options {
        claim: Some("syntax".into()),
        format: Format::V2Module,
        crate_slug: Some("zerocopy".into()),
        ..Options::default()
    };
    let m = lower_selected(&text, &opts).unwrap();
    assert_eq!(m.module_path.as_deref(), Some("Specs/zerocopy/syntax.lean"));
    assert!(m.spec_lean.contains("\nnamespace Specs.«zerocopy».«syntax»\n"), "{}", m.spec_lean);
}

#[test]
fn list_targets_reports_every_item_and_accepts_none() {
    let sources = [
        src("spec.rs", CLAIMS_SPEC),
        Source {
            label: "lib.rs".into(),
            text: "#[cfg_attr(anneal, anneal::spec(total))]\nfn d() {}\n".into(),
            module: Vec::new(),
        },
    ];
    let t = list_targets(&sources).unwrap_or_else(|_| panic!("listing failed"));
    let got: Vec<_> =
        t.iter().map(|t| (t.target.as_str(), t.claim.as_str(), t.file, t.external)).collect();
    assert_eq!(
        got,
        [
            ("a", "pair", 0, true),
            ("b", "pair", 0, true),
            ("d", "d", 1, false),
            ("m::c", "m__c", 0, true)
        ]
    );
    assert!(list_targets(&[src("lib.rs", "fn f() {}")]).unwrap_or_else(|_| panic!()).is_empty());
    assert!(list_targets(&[src("lib.rs", "#[anneal::spec(total)] fn f();")]).is_err());
    for dup in ["target = \"a\", target = \"b\"", "claim = \"c1\", claim = \"c2\""] {
        let text = format!("#[cfg_attr(anneal, anneal::spec({dup}, total))]\nfn f() {{}}\n");
        let errs = list_targets(&[src("lib.rs", &text)]).err().unwrap_or_else(|| panic!("{dup}"));
        assert_eq!(errs[0].diag.code, "E_ANNEAL_DUPLICATE_CLAUSE");
    }
    // Listing checks no clauses, so files that different units lower may
    // each define a helper of the same name, or use one defined elsewhere.
    let a = "#[cfg_attr(anneal, anneal::pure)]\nfn h() -> bool { true }\n\
             #[cfg_attr(anneal, anneal::spec(requires(h())))]\nfn a() {}\n";
    let b = "#[cfg_attr(anneal, anneal::pure)]\nfn h() -> bool { false }\n\
             #[cfg_attr(anneal, anneal::spec(requires(elsewhere())))]\nfn b() {}\n";
    let both = [src("a.rs", a), src("b.rs", b)];
    let listed = list_targets(&both).unwrap_or_else(|_| panic!("listing failed"));
    assert_eq!(listed.len(), 2);
    assert!(lower(&both).is_err());
}

#[test]
fn anneal_cfg_may_only_enable_specification_attributes() {
    for ok in [
        "#[cfg_attr(anneal, anneal::spec(total))]\nfn f() {}",
        "fn f() -> &'static str { \"anneal\" }",
        "#[cfg_attr(anneal, anneal::pure)]\nfn p() -> bool { true }",
        "#[cfg_attr(anneal, anneal::vacuous_ok(reason = \"r\"))]\n\
         #[cfg_attr(anneal, anneal::spec(requires(false)))]\nfn f() {}",
        "#[cfg(not(test))]\nfn f() {}\n#[cfg_attr(test, inline)]\nfn g() {}",
        "fn f() -> bool { cfg!(test) }",
    ] {
        lower_one(&format!(
            "{ok}\n#[cfg_attr(anneal, anneal::spec(total))]\nfn spec_anchor() {{}}"
        ))
        .unwrap_or_else(|e| panic!("{ok}: {e:?}"));
    }
    for bad in [
        "#[cfg(anneal)]\nfn f() {}",
        "#![cfg(anneal)]",
        "#[cfg(any(anneal, test))]\nfn f() {}",
        "#[cfg_attr(anneal, inline)]\nfn f() {}",
        "#[cfg_attr(any(anneal, test), anneal::spec(total))]\nfn f() {}",
        "#[cfg_attr(not(anneal), inline)]\nfn f() {}",
        "#[cfg_attr(anneal, anneal::spec(total), inline)]\nfn f() {}",
        "#[cfg_attr(anneal)]\nfn f() {}",
        "#[cfg_attr(anneal, anneal::pure, anneal::pure)]\nfn p() -> bool { true }",
        "#[cfg_attr(test, cfg(anneal))]\nfn f() {}",
        "fn f() -> bool { cfg!(anneal) }",
        "macro_rules! m { () => { #[cfg(anneal)] fn f() {} } }",
        "#[cfg(r#anneal)]\nfn f() {}",
        "#[r#cfg(anneal)]\nfn f() {}",
        "#[r#cfg_attr(r#anneal, inline)]\nfn f() {}",
        "#[cfg_attr(r#anneal, anneal::spec(total))]\nfn f() {}",
        "fn f() -> bool { r#cfg!(r#anneal) }",
        // A macro can assemble a cfg predicate from separate tokens, so the
        // identifier `anneal` is reserved everywhere else.
        "macro_rules! m { ($p:meta) => { #[cfg($p)] fn f() {} } }\nm!(not(anneal));",
        "macro_rules! m { ($a:meta) => { #[$a] fn f() {} } }\nm!(cfg(anneal));",
        "fn f() { let anneal = 1; }",
        "cfg_select! { anneal => { fn f() {} } _ => { fn f() {} } }",
        "core::cfg_select! { r#anneal => {} _ => {} }",
        "#[derive(D)]\n#[d(cfg(anneal))]\nstruct S;",
        "macro_rules! m { ($p:ident :: $q:ident) => { #[cfg($p)] fn f() {} } }\nm!(anneal::x);",
        "macro_rules! m { ($p:ident ::) => { #[cfg($p)] fn f() {} } }\nm!(anneal::);",
        "macro_rules! m { ($p:ident : :) => { #[cfg($p)] fn f() {} } }\nm!(anneal : :);",
        "macro_rules! m { ($p:ident :: $q:ident) => { #[cfg($p)] fn f() {} } }\nm!(r#anneal::spec);",
    ] {
        let text =
            format!("{bad}\n#[cfg_attr(anneal, anneal::spec(total))]\nfn spec_anchor() {{}}");
        expect_error(&text, "E_ANNEAL_BARE_OR_COMPOUND_CFG");
    }
}

#[test]
fn cli_selects_lists_and_writes_v2_modules() {
    let bin = env!("CARGO_BIN_EXE_anneal-spec-lower");
    let tmp = std::env::temp_dir().join(format!("anneal-spec-v2-{}", std::process::id()));
    fs::create_dir_all(&tmp).unwrap();
    fs::write(tmp.join("spec.rs"), CLAIMS_SPEC).unwrap();
    let run = |args: &[&str]| {
        Command::new(bin).arg("--src-root").arg(&tmp).args(args).arg("spec.rs").output().unwrap()
    };

    let out = run(&["--list-targets"]);
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
    let listed: serde_json::Value = serde_json::from_slice(&out.stdout).unwrap();
    assert_eq!(
        listed[0],
        serde_json::json!({"target": "a", "claim": "pair", "file": "spec.rs", "kind": "external"})
    );
    assert_eq!(listed.as_array().unwrap().len(), 3);

    let out_dir = tmp.join("out");
    let v2 = ["--format", "v2-module", "--crate-slug", "zerocopy", "--claim", "pair"];
    let out = run(&[&v2[..], &["--out-dir", out_dir.to_str().unwrap()]].concat());
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));
    assert!(out_dir.join("Specs/zerocopy/pair.lean").is_file());
    assert!(!out_dir.join("spec_span_map.json").exists());
    let out = run(&[&v2[..], &["--check", out_dir.to_str().unwrap()]].concat());
    assert!(out.status.success(), "{}", String::from_utf8_lossy(&out.stderr));

    assert_eq!(
        run(&["--claim", "nope", "--check", out_dir.to_str().unwrap()]).status.code(),
        Some(1)
    );
    assert_eq!(run(&["--format", "v2-module", "--out-dir", "x"]).status.code(), Some(2));
    assert_eq!(run(&["--list-targets", "--claim", "pair"]).status.code(), Some(2));
    assert_eq!(run(&["--list-targets", "--format", "v1"]).status.code(), Some(2));
    assert_eq!(run(&["--list-targets", "--out-dir", "x"]).status.code(), Some(2));
    assert_eq!(run(&["--crate-slug", "zerocopy", "--out-dir", "x"]).status.code(), Some(2));
    fs::remove_dir_all(&tmp).unwrap();
}
