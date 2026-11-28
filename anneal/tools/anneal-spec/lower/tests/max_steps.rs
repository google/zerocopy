// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

use std::{fs, path::Path, process::Command};

use anneal_spec_lower::{lower, lower_with, module_path, Format, Lowered, Options, Source};

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
    assert!(golden.contains("entrySatisfiesStepBound p fn0_id"), "{golden}");
    assert!(golden.contains("entrySatisfiesStepBound p fn1_id"), "{golden}");

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
    assert!(l.spec_lean.contains("private noncomputable def reachesDoneWithin"), "{}", l.spec_lean);
    assert!(l.spec_lean.contains("@Nat.rec (fun _ => State → Prop)"), "{}", l.spec_lean);
    assert!(l.spec_lean.contains("not physical wall-clock time"), "{}", l.spec_lean);
    assert!(!l.spec_lean.contains(":= by"), "unexpected tactic block in:\n{}", l.spec_lean);
    assert!(
        l.spec_lean.contains(
            "noncomputable def fn0_max_steps (q : Query) : Nat :=\n  (((34 : Nat) * (specNat (specArg q 0))) + (540 : Nat))"
        ),
        "{}",
        l.spec_lean
    );
    assert!(l.spec_lean.contains("entrySatisfiesStepBound p fn0_id"), "{}", l.spec_lean);

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
        l.spec_lean.contains("noncomputable def fn0_max_steps (_q : Query) : Nat :=\n  (10 : Nat)"),
        "{}",
        l.spec_lean
    );
    assert!(!l.spec_lean.contains("def specNat"), "{}", l.spec_lean);
    assert!(!l.spec_lean.contains("def specArg"), "{}", l.spec_lean);
    assert!(
        l.spec_lean.contains("effects := { terminates := true, noUnwind := true }"),
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
        l.spec_lean.contains("(Nat.div (specNat (specArg q 0)) (specNat (specArg q 1)))"),
        "{}",
        l.spec_lean
    );
    assert!(l.spec_lean.contains("(Nat.mod (specNat (specArg q 0)) (2 : Nat))"), "{}", l.spec_lean);
    assert!(
        l.spec_lean.contains("(Int.toNat (Spec.pure_extra (specInt (specArg q 2))))"),
        "{}",
        l.spec_lean
    );

    // `may_panic` + `max_steps` on `-> !` bounds MIR steps to unwind (while
    // `.aborted` remains False).
    let panic_sink = lower_one(&wrap("may_panic, max_steps = 16", "fn fail_fast() -> !")).unwrap();
    assert!(
        panic_sink.spec_lean.contains("effects := { terminates := true, noUnwind := false }"),
        "{}",
        panic_sink.spec_lean
    );
}

#[test]
fn max_steps_counts_casts_to_unsigned_types() {
    let l = lower_one(&wrap(
        "max_steps = n as u64 + (k as u8 as usize) + c as u32",
        "fn f(n: u32, k: i16, c: bool)",
    ))
    .unwrap();
    for want in [
        "(Int.toNat (specInt (specArg q 0)))",
        "(Int.toNat (Trusted.MirSemantics.intEmod (specInt (specArg q 1)) 256))",
        "(Int.toNat (if (specBool (specArg q 2) = true) then (1 : Int) else (0 : Int)))",
    ] {
        assert!(l.spec_lean.contains(want), "missing {want} in\n{}", l.spec_lean);
    }
    expect_error(&wrap("max_steps = k as i64", "fn f(k: u8)"), "E_ANNEAL_SPEC_TYPE_MISMATCH");
}

#[test]
fn max_steps_counts_unsigned_integer_method_results() {
    let l = lower_one(&wrap(
        "max_steps = n.max(4u32) + n.clamp(1, 9) + k.abs_diff(0i8) as u32",
        "fn f(n: u32, k: i8)",
    ))
    .unwrap();
    for want in [
        "(Int.toNat (Max.max (specInt (specArg q 0)) (4 : Int)))",
        "(Int.toNat (Min.min (Max.max (specInt (specArg q 0)) (1 : Int)) (9 : Int)))",
        "(Int.toNat (Int.ofNat (Int.natAbs ((specInt (specArg q 1)) - (0 : Int)))))",
    ] {
        assert!(l.spec_lean.contains(want), "missing {want} in\n{}", l.spec_lean);
    }
    expect_error(&wrap("max_steps = k.min(0i8)", "fn f(k: i8)"), "E_ANNEAL_SPEC_TYPE_MISMATCH");
}

#[test]
fn max_steps_counts_guarded_div_ceil_and_rotations() {
    let l = lower_one(&wrap(
        "requires(d > 0usize), max_steps = n.div_ceil(d) + n.rotate_right(1)",
        "fn f(n: usize, d: usize)",
    ))
    .unwrap();
    assert!(
        l.spec_lean.contains(
            "(Int.toNat ((fun («n» «d» : Int) => Trusted.MirSemantics.intTdiv («n» + «d» - 1) \
             «d») (specInt (specArg q 0)) (specInt (specArg q 1))))"
        ),
        "{}",
        l.spec_lean
    );
    assert!(l.spec_lean.contains("(Int.toNat (Int.ofNat ((fun («x» «k» : Nat)"), "{}", l.spec_lean);
    expect_error(
        &wrap("max_steps = n.div_ceil(d)", "fn f(n: usize, d: usize)"),
        "E_ANNEAL_UNGUARDED_SPEC_DIV",
    );
}

#[test]
fn max_steps_counts_unsigned_abs_and_bit_casts() {
    let l = lower_one(&wrap(
        "max_steps = k.unsigned_abs() as usize + k.cast_unsigned() as usize",
        "fn f(k: i64)",
    ))
    .unwrap();
    for want in [
        "(Int.toNat (Int.ofNat (Int.natAbs (specInt (specArg q 0)))))",
        "(Int.toNat (Trusted.MirSemantics.intEmod (specInt (specArg q 0)) 18446744073709551616))",
    ] {
        assert!(l.spec_lean.contains(want), "missing {want} in\n{}", l.spec_lean);
    }
    expect_error(
        &wrap("max_steps = k.wrapping_abs()", "fn f(k: i64)"),
        "E_ANNEAL_SPEC_TYPE_MISMATCH",
    );
}

#[test]
fn max_steps_counts_mixed_signedness_sums_on_unsigned_receivers() {
    let l =
        lower_one(&wrap("max_steps = n.wrapping_add_signed(d)", "fn f(n: u64, d: i64)")).unwrap();
    assert!(
        l.spec_lean.contains(
            "(Int.toNat (Trusted.MirSemantics.intEmod ((specInt (specArg q 0)) + (specInt \
             (specArg q 1))) 18446744073709551616))"
        ),
        "{}",
        l.spec_lean
    );
    expect_error(
        &wrap("max_steps = d.saturating_sub_unsigned(n)", "fn f(n: u64, d: i64)"),
        "E_ANNEAL_SPEC_TYPE_MISMATCH",
    );
}

#[test]
fn max_steps_counts_unbounded_shifts_and_midpoints_of_unsigned_values() {
    let l =
        lower_one(&wrap("max_steps = n.unbounded_shr(4) + n.midpoint(m)", "fn f(n: u32, m: u32)"))
            .unwrap();
    for want in [
        "(Int.toNat ((fun («x» «n» : Int) => if «n» < (32 : Int) then",
        "(Int.toNat (Trusted.MirSemantics.intTdiv ((specInt (specArg q 0)) + (specInt (specArg q \
         1))) (2 : Int)))",
    ] {
        assert!(l.spec_lean.contains(want), "missing {want} in\n{}", l.spec_lean);
    }
    expect_error(
        &wrap("max_steps = k.unbounded_shl(1)", "fn f(k: i32)"),
        "E_ANNEAL_SPEC_TYPE_MISMATCH",
    );
}

#[test]
fn max_steps_counts_guarded_unsigned_divisions() {
    let l = lower_one(&wrap(
        "requires(d != 0u32), max_steps = n.div_euclid(d) + n.wrapping_rem_euclid(d)",
        "fn f(n: u32, d: u32)",
    ))
    .unwrap();
    for want in [
        "(Int.toNat (Trusted.MirSemantics.intTdiv (specInt (specArg q 0)) (specInt (specArg q 1))))",
        "(Int.toNat (Trusted.MirSemantics.intEmod (specInt (specArg q 0)) (specInt (specArg q 1))))",
    ] {
        assert!(l.spec_lean.contains(want), "missing {want} in\n{}", l.spec_lean);
    }
    expect_error(
        &wrap("max_steps = n.div_euclid(d)", "fn f(n: u32, d: u32)"),
        "E_ANNEAL_UNGUARDED_SPEC_DIV",
    );
}

#[test]
fn max_steps_counts_guarded_unsigned_saturating_division() {
    let l = lower_one(&wrap(
        "requires(d != 0u64), max_steps = n.saturating_div(d)",
        "fn f(n: u64, d: u64)",
    ))
    .unwrap();
    let want = "(Int.toNat (Trusted.MirSemantics.intTdiv (specInt (specArg q 0)) (specInt (specArg q 1))))";
    assert!(l.spec_lean.contains(want), "missing {want} in\n{}", l.spec_lean);
    expect_error(
        &wrap("max_steps = saturating_div(n, d)", "fn f(n: u64, d: u64)"),
        "E_ANNEAL_UNGUARDED_SPEC_DIV",
    );
}

#[test]
fn max_steps_counts_swapped_unsigned_bytes() {
    let l = lower_one(&wrap("max_steps = n.swap_bytes()", "fn f(n: u16)")).unwrap();
    let want = "(Int.toNat (Int.ofNat ((fun («x» : Nat) => (((«x» >>> 0) % 256) <<< 8) ||| (((«x» >>> 8) % \
                256) <<< 0)) (Int.toNat (Trusted.MirSemantics.intEmod (specInt (specArg q 0)) 65536)))))";
    assert!(l.spec_lean.contains(want), "missing {want} in\n{}", l.spec_lean);
}

#[test]
fn max_steps_counts_population_counts() {
    let l = lower_one(&wrap("max_steps = k.count_ones()", "fn f(k: i32)")).unwrap();
    let want = "(Int.toNat (Int.ofNat (((fun («x» : Nat) => «x» + («x» >>> 16))";
    assert!(l.spec_lean.contains(want), "missing {want} in\n{}", l.spec_lean);
}

#[test]
fn max_steps_counts_leading_and_trailing_zeros() {
    let l = lower_one(&wrap("max_steps = k.leading_zeros() + k.trailing_zeros()", "fn f(k: u16)"))
        .unwrap();
    for want in [
        "(Int.toNat ((16 : Int) - (Int.ofNat",
        "(fun («x» : Nat) => («x» ||| («x» <<< 8)) % 65536)",
    ] {
        assert!(l.spec_lean.contains(want), "missing {want} in\n{}", l.spec_lean);
    }
}

#[test]
fn max_steps_matches_step_counts_against_ranges() {
    let l = lower_one(&wrap(
        "max_steps = match n { 0..=9 => 1, 10..=99 => n, _ => 100 }",
        "fn f(n: usize)",
    ))
    .unwrap();
    for want in [
        "((0 : Nat) ≤ «match» ∧ «match» ≤ (9 : Nat))",
        "((10 : Nat) ≤ «match» ∧ «match» ≤ (99 : Nat))",
    ] {
        assert!(l.spec_lean.contains(want), "missing {want} in\n{}", l.spec_lean);
    }
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
    expect_error(&wrap("max_steps = a & 1i8", "fn f(a: i8)"), "E_ANNEAL_SPEC_TYPE_MISMATCH");

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
fn max_steps_counts_a_guarded_ilog2() {
    let sig = "fn f(n: u64, i: i32)";
    for clause in [
        "max_steps = if n > 0 { n.ilog2() } else { 0 }",
        "max_steps = match n { 0 => 0, _ => n.ilog2() }",
        "max_steps = if i > 0 { i.ilog2() } else { 0 }",
    ] {
        lower_one(&wrap(clause, sig)).unwrap_or_else(|e| panic!("{clause}: {e:?}"));
    }
    for clause in ["max_steps = n.ilog2()", "max_steps = if i != 0 { i.ilog2() } else { 0 }"] {
        expect_error(&wrap(clause, sig), "E_ANNEAL_UNGUARDED_SPEC_LOG");
    }
}

#[test]
fn max_steps_counts_a_bounded_next_power_of_two() {
    let sig = "fn f(n: u64)";
    for clause in [
        "max_steps = if n <= 1024 { n.next_power_of_two() } else { 0 }",
        "max_steps = match n { 0..=64 => n.next_power_of_two(), _ => 1 }",
    ] {
        lower_one(&wrap(clause, sig)).unwrap_or_else(|e| panic!("{clause}: {e:?}"));
    }
    expect_error(
        &wrap("max_steps = n.next_power_of_two()", sig),
        "E_ANNEAL_UNGUARDED_SPEC_OVERFLOW",
    );
}
