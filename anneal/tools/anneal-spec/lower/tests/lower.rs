// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use std::{fs, path::Path, process::Command};

use anneal_spec_lower::{lower, module_path, Lowered, Source};

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

const UNITS: &[&str] = &[
    "01_usize_pointer_metadata",
    "02_unit_pointer_metadata",
    "03_macros_unsafe",
    "04_layout_add_scaled_metadata",
];

fn unit_dir(unit: &str) -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../tests/zerocopy").join(unit)
}

#[test]
fn zerocopy_units_match_checked_in_goldens() {
    for unit in UNITS {
        let dir = unit_dir(unit);
        let text = fs::read_to_string(dir.join("spec.rs")).unwrap();
        let sources =
            [Source { label: format!("tests/zerocopy/{unit}/spec.rs"), text, module: Vec::new() }];
        let l = lower(&sources).unwrap_or_else(|e| panic!("{unit}: {}", e[0].render(&sources)));
        assert_eq!(
            l.spec_lean,
            fs::read_to_string(dir.join("Spec.lean")).unwrap(),
            "{unit} Spec.lean"
        );
    }
}

#[test]
fn cli_check_accepts_goldens_and_rejects_stale_output() {
    let bin = env!("CARGO_BIN_EXE_anneal-spec-lower");
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("..");
    for unit in UNITS {
        let rel = format!("tests/zerocopy/{unit}/spec.rs");
        let dir = format!("tests/zerocopy/{unit}");
        let status = Command::new(bin)
            .args(["--src-root", ".", "--check", &dir, &rel])
            .current_dir(&root)
            .status()
            .unwrap();
        assert!(status.success(), "{unit}: --check failed; regenerate with --out-dir");
    }
    let tmp = std::env::temp_dir().join(format!("anneal-spec-stale-{}", std::process::id()));
    fs::create_dir_all(&tmp).unwrap();
    fs::write(tmp.join("Spec.lean"), "stale").unwrap();
    fs::write(tmp.join("spec_span_map.json"), "{}").unwrap();
    let out = Command::new(bin)
        .args(["--check", tmp.to_str().unwrap()])
        .arg(unit_dir(UNITS[0]).join("spec.rs"))
        .output()
        .unwrap();
    fs::remove_dir_all(&tmp).unwrap();
    assert_eq!(out.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&out.stderr).contains("is stale"));
}

#[test]
fn inline_and_external_forms_lower_to_identical_spec_lean() {
    let external = fs::read_to_string(unit_dir(UNITS[0]).join("spec.rs")).unwrap();
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
    let a = lower_one(&external).unwrap();
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
        ("requires(if a { true } else { false })", "fn f(a: bool)", "E_ANNEAL_IMPURE_SPEC_EXPR"),
        ("requires(old(a) == a)", "fn f(a: u8)", "E_ANNEAL_OLD_IN_PRECONDITION"),
        ("ensures(|r| r == old(a))", "fn f(a: u8) -> u8", "E_ANNEAL_UNSUPPORTED_OLD"),
        ("requires(lenght > 0usize)", "fn f(length: usize)", "E_ANNEAL_SPEC_UNKNOWN_IDENT"),
        ("requires(ret == 0u8)", "fn f() -> u8", "E_ANNEAL_SPEC_UNKNOWN_IDENT"),
        ("requires(a == b)", "fn f(a: u8, b: u16)", "E_ANNEAL_SPEC_TYPE_MISMATCH"),
        ("requires(a == 256)", "fn f(a: u8)", "E_ANNEAL_SPEC_LITERAL_RANGE"),
        ("requires(a.len() > 0)", "fn f(a: u8)", "E_ANNEAL_SPEC_UNSUPPORTED_EXPR"),
        ("requires(a & 1u8 == 0u8)", "fn f(a: u8)", "E_ANNEAL_UNSUPPORTED_BITWISE"),
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
    let text = fs::read_to_string(unit_dir(UNITS[0]).join("spec.rs")).unwrap();
    let l = lower_one(&text).unwrap();
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
    for name in ["True", "False", "Int", "Trusted", "Spec", "_root_"] {
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
