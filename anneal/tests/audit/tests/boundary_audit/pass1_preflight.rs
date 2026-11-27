// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Pass 1 preflight: forbidden syntax and attributes, `sorry`, import
//! cycles, scoped namespaces, the module system, and admitted theorem
//! shapes.

use super::*;

/// Verifies that Phase 1 (`"preflight"`) rejects forbidden headers, imports,
/// commands (`#eval`), terms (`unsafe`, `by_elab`), tactics (`native_decide`,
/// `decide +native`), attributes (`@[extern]`, `@[implemented_by]`), and
/// invalid or missing `-- anneal-trust-tier:` directives before Lean ever
/// compiles or executes the file (`execution_began == false`).
#[test]
fn rejects_forbidden_syntax_and_attributes_without_executing_eval() {
    let base_fix = TempFixture::new(None);
    let sentinel = base_fix.root.join("must-not-exist");
    let eval_sentinel_src =
        format!("{HEADER}#eval IO.FS.writeFile \"{}\" \"executed\"\n", sentinel.display());

    let full_run_negatives: Vec<(&str, String)> = vec![
        (
            "implicit default Init",
            "-- anneal-trust-tier: vetted\nimport Init.Core\ndef x : Nat := 0\n".to_string(),
        ),
        (
            "foreign namespace spoof",
            format!("{HEADER}import Foreign\nnamespace Trusted\ndef x : Nat := 0\nend Trusted\n"),
        ),
        ("Std import", "-- anneal-trust-tier: vetted\nprelude\nimport Std\n".to_string()),
        ("evaluation sentinel", eval_sentinel_src),
    ];

    for (_label, src) in &full_run_negatives {
        let mut f = TempFixture::new(Some(src));
        let _ = f.check_expected(Some(1), Some("preflight"), Some(false));
        assert!(!sentinel.exists(), "evaluation sentinel executed!");
    }

    let inspector_negatives: Vec<(&str, String)> = vec![
        (
            "trusted import all",
            "-- anneal-trust-tier: vetted\nmodule\nprelude\nimport all Init.Data.Nat.Bitwise.Basic\n"
                .to_string(),
        ),
        (
            "module meta import",
            "-- anneal-trust-tier: vetted\nmodule\nprelude\nmeta import Init.Core\n"
                .to_string(),
        ),
        (
            "module meta section",
            "-- anneal-trust-tier: vetted\nmodule\nprelude\npublic import Init.Core\nmeta section\nend\n"
                .to_string(),
        ),
        (
            "module noncomputable section",
            "-- anneal-trust-tier: vetted\nmodule\nprelude\npublic import Init.Core\nnoncomputable section\nend\n"
                .to_string(),
        ),
        (
            "direct meta import",
            "-- anneal-trust-tier: vetted\nprelude\nmeta import Init.Core\n"
                .to_string(),
        ),
        (
            "direct all import",
            "-- anneal-trust-tier: vetted\nprelude\nimport all Init.Core\n"
                .to_string(),
        ),
        (
            "public import",
            "-- anneal-trust-tier: vetted\nprelude\npublic import Init.Core\n"
                .to_string(),
        ),
        (
            "nested unsafe",
            format!("{HEADER}open Nat in\nunsafe def x : Nat := 0\n"),
        ),
        (
            "term unsafe generated hook",
            format!("{HEADER}def generatedUnsafe : Nat := unsafe 0\n"),
        ),
        (
            "mutual unsafe",
            format!("{HEADER}mutual\n unsafe def x : Nat := 0\nend\n"),
        ),
        (
            "nested forbidden command",
            format!("{HEADER}open Nat in\n#eval 0\n"),
        ),
        (
            "nested attribute",
            format!(
                "{HEADER}structure X where\n @[extern \"foreign\"] x : Nat\n"
            ),
        ),
        (
            "implemented_by",
            format!("{HEADER}@[implemented_by other] def x : Nat := 0\n"),
        ),
        (
            "attribute removal",
            format!("{HEADER}attribute [-extern] Nat.add\n"),
        ),
        (
            "deriving",
            format!("{HEADER}structure X where\n x : Nat\nderiving Repr\n"),
        ),
        ("open scoped", format!("{HEADER}open scoped Nat\n")),
        (
            "set_option wrapper",
            format!(
                "{HEADER}set_option debug.skipKernelTC true in\ndef x : Nat := 0\n"
            ),
        ),
        ("custom macro", format!("{HEADER}macro \"x\" : term => `(0)\n")),
        (
            "native shortcut",
            format!("{HEADER}theorem x : True := by native_decide\n"),
        ),
        (
            "native decide config",
            format!("{HEADER}theorem x : True := by decide +native\n"),
        ),
        (
            "by_elab",
            format!(
                "{HEADER}def x : Nat := by_elab return Lean.mkNatLit 0\n"
            ),
        ),
        (
            "missing module trust tier",
            "prelude\nimport Init.NotationExtra\ndef x : Nat := 0\n"
                .to_string(),
        ),
        (
            "unknown candidate feature",
            "-- anneal-trust-tier: candidate:nonexistent\nprelude\nimport Init.NotationExtra\n"
                .to_string(),
        ),
        (
            "multiple module trust tiers",
            "-- anneal-trust-tier: vetted\n-- anneal-trust-tier: candidate:mir_ast\nprelude\nimport Init.NotationExtra\n"
                .to_string(),
        ),
        (
            "invalid module trust tier",
            "-- anneal-trust-tier: bogus\nprelude\nimport Init.NotationExtra\n"
                .to_string(),
        ),
        (
            "legacy declaration trust attribute",
            format!("{HEADER}@[vetted] def x : Nat := 0\n"),
        ),
        ("malformed recovery", format!("{HEADER}def broken : :=\n")),
        (
            "decide +kernel",
            format!("{HEADER}theorem x : True := by decide +kernel\n"),
        ),
        ("decideBang", format!("{HEADER}theorem x : True := by decide!\n")),
        (
            "bv_decide",
            format!("{HEADER}theorem x : True := by bv_decide\n"),
        ),
        ("rfl'", format!("{HEADER}theorem x : True := by rfl'\n")),
        (
            "grind set_option",
            format!(
                "{HEADER}theorem x : True := by grind => set_option debug.skipKernelTC true\n"
            ),
        ),
        (
            "include_str",
            format!(
                "{HEADER}def x : String := include_str \"Trusted.lean\"\n"
            ),
        ),
        (
            "noncomputable section",
            format!("{HEADER}noncomputable section\n"),
        ),
        (
            "_root_ escape",
            format!(
                "{HEADER}namespace Trusted\ndef _root_.Spoof : Nat := 0\nend Trusted\n"
            ),
        ),
        (
            "section inside in-command",
            format!("{HEADER}section S in\ndef x : Nat := 0\n"),
        ),
        (
            "namespace inside in-command",
            format!("{HEADER}namespace A in\ndef x : Nat := 0\n"),
        ),
        (
            "with_decl_name% term",
            format!("{HEADER}def f : Nat := with_decl_name% Foo 0\n"),
        ),
        (
            "private_decl% term",
            format!("{HEADER}def f : Name := private_decl% f\n"),
        ),
        (
            "decl_name% term",
            format!("{HEADER}def f : Name := decl_name%\n"),
        ),
        (
            "namespace on RHS of in-command",
            format!("{HEADER}open Nat in\nnamespace A\n"),
        ),
        (
            "empty French-quote identifier",
            format!("{HEADER}def «» : Nat := 0\n"),
        ),
        (
            "tactic block in Trusted module",
            format!("{HEADER}theorem x : Eq 0 0 := by rfl\n"),
        ),
    ];

    let mut checker = base_fix.checker();
    checker.tool_admission().unwrap();
    for (idx, (label, src)) in inspector_negatives.iter().enumerate() {
        let neg_path = checker.stage().join(format!("neg-{idx}.lean"));
        fs::write(&neg_path, src.as_bytes()).unwrap();
        let err = checker
            .inspect(InspectorRequest::Preflight {
                sources: vec![("Trusted".to_string(), neg_path)],
                base_trusted_sources: Vec::new(),
                allow_local_semireducible: false,
            })
            .expect_err(&format!("expected preflight rejection for {label}"));
        assert_eq!(err.code, 1, "unexpected code for {label}: {err}");
    }

    // Verify that `SourceRole.theory` (`Anneal`) admits allowed tactics (`by
    // rfl`) while still rejecting disallowed tactics and tactic configurations
    // (`native_decide`, `decide +native`, `decide +kernel`, `decide!`,
    // `bv_decide`, `rfl'`, `grind`, `sorry`).
    let theory_header = "prelude\nimport Init.NotationExtra\n";
    let theory_pos_path = checker.stage().join("theory-pos.lean");
    fs::write(
        &theory_pos_path,
        format!("{theory_header}theorem ok : Eq 0 0 := by rfl\n").as_bytes(),
    )
    .unwrap();
    checker
        .inspect(InspectorRequest::Preflight {
            sources: vec![("Anneal".to_string(), theory_pos_path)],
            base_trusted_sources: Vec::new(),
            allow_local_semireducible: false,
        })
        .expect("expected theory module with `by rfl` to pass preflight");

    let theory_negatives: Vec<(&str, String)> = vec![
        ("theory native_decide", format!("{theory_header}theorem x : True := by native_decide\n")),
        (
            "theory decide +native",
            format!("{theory_header}theorem x : True := by decide +native\n"),
        ),
        (
            "theory decide +kernel",
            format!("{theory_header}theorem x : True := by decide +kernel\n"),
        ),
        ("theory decideBang", format!("{theory_header}theorem x : True := by decide!\n")),
        ("theory bv_decide", format!("{theory_header}theorem x : True := by bv_decide\n")),
        ("theory rfl'", format!("{theory_header}theorem x : True := by rfl'\n")),
        (
            "theory grind set_option",
            format!(
                "{theory_header}theorem x : True := by grind => set_option debug.skipKernelTC true\n"
            ),
        ),
        ("theory by sorry", format!("{theory_header}theorem x : False := by sorry\n")),
        ("theory term sorry", format!("{theory_header}theorem x : False := sorry\n")),
    ];
    for (idx, (label, src)) in theory_negatives.iter().enumerate() {
        let neg_path = checker.stage().join(format!("theory-neg-{idx}.lean"));
        fs::write(&neg_path, src.as_bytes()).unwrap();
        let err = checker
            .inspect(InspectorRequest::Preflight {
                sources: vec![("Anneal".to_string(), neg_path)],
                base_trusted_sources: Vec::new(),
                allow_local_semireducible: false,
            })
            .expect_err(&format!("expected preflight rejection for {label}"));
        assert_eq!(err.code, 1, "unexpected code for {label}: {err}");
    }
}

/// Verifies the one admitted `local` attribute in `theory/` modules,
/// `attribute [local semireducible] _root_.<c> in <theorem or def>` with `<c>`
/// in `TrustedBoundary.localSemireducibleAllowlist` (`Nat.bitwise`), and that
/// every nearby shape stays rejected by `"preflight"`: other attributes and
/// kinds, unlisted or unqualified constants, chained `in`, other declaration
/// kinds, attributes on the declaration, `mutual` blocks, shadowing
/// declarations, constructors, fields, and parent projections, `Trusted`
/// modules, and requests without `allow_local_semireducible` (as Pass 2
/// `correspondence/` sends).
#[test]
fn admits_only_scoped_local_semireducible_in_theory_modules() {
    let base_fix = TempFixture::new(None);
    let mut checker = base_fix.checker();
    checker.tool_admission().unwrap();
    let theory_header = "prelude\nimport Init.NotationExtra\n";
    let pattern = "attribute [local semireducible] _root_.Nat.bitwise in\n";
    let preflight = |checker: &mut Checker, module: &str, path: PathBuf, allow: bool| {
        checker.inspect(InspectorRequest::Preflight {
            sources: vec![(module.to_string(), path)],
            base_trusted_sources: Vec::new(),
            allow_local_semireducible: allow,
        })
    };

    let positives: Vec<(&str, String)> = vec![
        (
            "private theorem in a namespace",
            format!(
                "{theory_header}namespace Anneal.X\n{pattern}private theorem t : True := True.intro\nend Anneal.X\n"
            ),
        ),
        ("def", format!("{theory_header}{pattern}def d : Nat := 0\n")),
    ];
    for (idx, (label, src)) in positives.iter().enumerate() {
        let path = checker.stage().join(format!("ls-pos-{idx}.lean"));
        fs::write(&path, src.as_bytes()).unwrap();
        preflight(&mut checker, "Anneal", path, true)
            .unwrap_or_else(|err| panic!("expected preflight to admit {label}: {err}"));
    }

    // Each negative must reach a specific rejection: shadowing sources fail
    // the shadow check, and every other source falls through the exception
    // matcher to the ordinary `in` rule, which shows the exception declined it.
    let in_lhs = "only `open` and `variable` commands are permitted on the LHS of `in`";
    let shadow = "declares a constant whose name could shadow one in `localSemireducibleAllowlist`";
    let theorem = "theorem t : True := True.intro\n";
    let theory_negatives: Vec<(&str, String)> = vec![
        (
            "local simp",
            format!("{theory_header}attribute [local simp] _root_.Nat.bitwise in\n{theorem}"),
        ),
        (
            "local instance",
            format!("{theory_header}attribute [local instance] _root_.Nat.bitwise in\n{theorem}"),
        ),
        (
            "local reducible",
            format!("{theory_header}attribute [local reducible] _root_.Nat.bitwise in\n{theorem}"),
        ),
        (
            "local irreducible",
            format!(
                "{theory_header}attribute [local irreducible] _root_.Nat.bitwise in\n{theorem}"
            ),
        ),
        (
            "local semireducible with an argument",
            format!(
                "{theory_header}attribute [local semireducible 1] _root_.Nat.bitwise in\n{theorem}"
            ),
        ),
        (
            "scoped semireducible",
            format!(
                "{theory_header}attribute [scoped semireducible] _root_.Nat.bitwise in\n{theorem}"
            ),
        ),
        (
            "global semireducible",
            format!("{theory_header}attribute [semireducible] _root_.Nat.bitwise in\n{theorem}"),
        ),
        (
            "constant not allowlisted",
            format!(
                "{theory_header}attribute [local semireducible] _root_.Nat.land in\n{theorem}"
            ),
        ),
        (
            "two attributes",
            format!(
                "{theory_header}attribute [local semireducible, local reducible] _root_.Nat.bitwise in\n{theorem}"
            ),
        ),
        (
            "two constants",
            format!(
                "{theory_header}attribute [local semireducible] _root_.Nat.bitwise _root_.Nat.land in\n{theorem}"
            ),
        ),
        (
            "unqualified constant inside a namespace",
            format!(
                "{theory_header}namespace Foo\nattribute [local semireducible] Nat.bitwise in\n{theorem}end Foo\n"
            ),
        ),
        (
            "chained set_option",
            format!("{theory_header}{pattern}set_option pp.all true in\n{theorem}"),
        ),
        ("chained open on the outside", format!("{theory_header}open Nat in\n{pattern}{theorem}")),
        ("chained open on the inside", format!("{theory_header}{pattern}open Nat in\n{theorem}")),
        (
            "instance declaration",
            format!("{theory_header}{pattern}instance : Inhabited Nat := ⟨0⟩\n"),
        ),
        ("inside mutual", format!("{theory_header}mutual\n{pattern}{theorem}end\n")),
        (
            "shadowing declaration",
            format!(
                "{theory_header}namespace Foo\ndef Nat.bitwise : Nat := 0\nend Foo\n{pattern}{theorem}"
            ),
        ),
        (
            "shadowing declaration through a namespace",
            format!(
                "{theory_header}namespace Foo.Nat\ndef bitwise : Nat := 0\nend Foo.Nat\n{pattern}{theorem}"
            ),
        ),
        (
            "shadowing inductive constructor",
            format!(
                "{theory_header}namespace Foo\ninductive Nat where\n  | bitwise : Nat\nend Foo\n{pattern}{theorem}"
            ),
        ),
        (
            "shadowing structure field",
            format!(
                "{theory_header}namespace Foo\nstructure Nat where\n  bitwise : Bool\nend Foo\n{pattern}{theorem}"
            ),
        ),
        (
            "shadowing structure constructor",
            format!(
                "{theory_header}namespace Foo\nstructure Nat where\n  bitwise ::\n  val : Bool\nend Foo\n{pattern}{theorem}"
            ),
        ),
        (
            "shadowing structure parent projection",
            format!(
                "{theory_header}namespace Foo\nstructure Q where\n  x : Bool\nstructure Nat extends bitwise : Q where\n  y : Bool\nend Foo\n{pattern}{theorem}"
            ),
        ),
        (
            "instance attribute on the declaration",
            format!("{theory_header}{pattern}@[instance] def i : Inhabited Nat := ⟨0⟩\n"),
        ),
        ("simp attribute on the declaration", format!("{theory_header}{pattern}@[simp] {theorem}")),
    ];
    for (idx, (label, src)) in theory_negatives.iter().enumerate() {
        let path = checker.stage().join(format!("ls-neg-{idx}.lean"));
        fs::write(&path, src.as_bytes()).unwrap();
        let err = preflight(&mut checker, "Anneal", path, true)
            .expect_err(&format!("expected preflight rejection for {label}"));
        assert_eq!(err.code, 1, "unexpected code for {label}: {err}");
        let expected = if label.starts_with("shadowing") { shadow } else { in_lhs };
        assert!(err.message.contains(expected), "expected `{expected}` for {label}, got: {err}");
    }

    // `Trusted` modules never get the exception.
    let trusted_path = checker.stage().join("ls-trusted.lean");
    fs::write(&trusted_path, format!("{HEADER}{pattern}def d : Nat := 0\n").as_bytes()).unwrap();
    let err = preflight(&mut checker, "Trusted", trusted_path, true)
        .expect_err("expected preflight rejection for a Trusted module");
    assert_eq!(err.code, 1, "unexpected code for a Trusted module: {err}");
    assert!(err.message.contains(in_lhs), "unexpected error for a Trusted module: {err}");

    // Requests without the flag, as Pass 2 sends for `correspondence/`
    // sources, never get the exception, even for a theory-role source that the
    // flagged request admits.
    let unflagged_path = checker.stage().join("ls-unflagged.lean");
    fs::write(&unflagged_path, format!("{theory_header}{pattern}def d : Nat := 0\n").as_bytes())
        .unwrap();
    preflight(&mut checker, "Anneal", unflagged_path.clone(), true)
        .expect("expected the flagged request to admit the pattern");
    let err = preflight(&mut checker, "Anneal", unflagged_path, false)
        .expect_err("expected preflight rejection without allow_local_semireducible");
    assert_eq!(err.code, 1, "unexpected code without allow_local_semireducible: {err}");
    assert!(
        err.message.contains(in_lhs),
        "unexpected error without allow_local_semireducible: {err}"
    );
}

/// Verifies that `"preflight"` rejects surface `sorry` syntax before
/// compilation (`execution_began == false`), and that Phase 2 (`"audit"`)
/// rejects direct `sorryAx` applications (which use only allowed function
/// application syntax, so they reach Phase 2 where `sorryAx` is excluded from
/// `foundation-lock.json`'s axiom allowlist), both in `Trusted.lean` and in an
/// unimported `Trusted/Unused.lean` module discovered by `scan_lean_tree`.
#[test]
fn rejects_sorry_and_unreferenced_module_with_sorry() {
    let mut f_sorry = TempFixture::new(Some(&format!("{HEADER}theorem bad : False := by sorry\n")));
    let _ = f_sorry.check_expected(Some(1), Some("preflight"), Some(false));

    let mut f_sorry_ax =
        TempFixture::new(Some(&format!("{HEADER}theorem bad : False := sorryAx False true\n")));
    let _ = f_sorry_ax.check_expected(Some(1), Some("audit"), Some(true));

    let mut f_unused = TempFixture::new(None);
    fs::create_dir_all(f_unused.root.join("trusted/lean/Trusted")).unwrap();
    fs::write(
        f_unused.root.join("trusted/lean/Trusted/Unused.lean"),
        format!("{HEADER}theorem unreferenced : False := sorryAx False true\n").as_bytes(),
    )
    .unwrap();
    let _ = f_unused.check_expected(Some(1), Some("audit"), Some(true));
}

/// Verifies that cyclic imports between modules are rejected during
/// `"preflight"` before compilation begins.
#[test]
fn rejects_source_import_cycles() {
    let mut fix = TempFixture::new(Some(&format!("{HEADER}import Trusted.Other\n")));
    fs::create_dir_all(fix.root.join("trusted/lean/Trusted")).unwrap();
    fs::write(
        fix.root.join("trusted/lean/Trusted/Other.lean"),
        format!("{HEADER}import Trusted\n").as_bytes(),
    )
    .unwrap();
    let _ = fix.check_expected(Some(1), Some("preflight"), Some(false));
}

/// Verifies Pass 1 foundation `"preflight"` rejects `open List` (an `Init.*`
/// namespace with scoped notations) in both `theory/` and `trusted/lean/`
/// before compilation—including when shadowed by a local decoy namespace.
#[test]
fn rejects_scoped_namespace_in_pass1_preflight() {
    let cases: &[(&str, &str)] = &[
        (
            "theory/Anneal/OpenList.lean",
            "prelude\nimport Init.Data.List.Basic\n\
             open List\n\
             def f : Nat := 0\n",
        ),
        (
            "trusted/lean/Trusted/OpenList.lean",
            "-- anneal-trust-tier: candidate:mir_semantics\n\
             prelude\nimport Init.Data.List.Basic\n\
             open List\n\
             def f : Nat := 0\n",
        ),
        (
            "theory/Anneal/OpenListDecoy.lean",
            "prelude\nimport Init.Data.List.Basic\n\
             namespace Anneal.List\n\
             def decoy : Nat := 0\n\
             end Anneal.List\n\
             namespace Anneal\n\
             open List\n\
             def f : Nat := 0\n\
             end Anneal\n",
        ),
    ];

    for (rel, body) in cases {
        let mut fix = TempFixture::new(None);
        let path = fix.root.join(rel);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        if rel.starts_with("theory/") {
            fs::write(fix.root.join("theory/Anneal.lean"), "prelude\nimport Init.Core\n").unwrap();
        }
        fs::write(&path, body).unwrap();
        let err = fix.check_expected(Some(1), Some("preflight"), Some(false)).unwrap_err();
        assert!(
            err.message.contains("cannot open namespace List with scoped syntax or extensions"),
            "expected scoped List rejection for {rel}, got: {err}"
        );
    }
}

/// Repository auditing (`Checker::run`) restricts imports in `trusted/lean/`
/// and `theory/` to `foundation-lock.json` even when
/// `trusted/audit/library-lock.json` is present (`library-lock.json` applies
/// exclusively to `targetAudit`), while `vetted` modules are rejected even
/// earlier at tier-import preflight for non-foundation `Init.*` imports.
#[test]
fn rejects_library_lock_imports_in_repository_audit() {
    let checkout = repo_root();

    let mut vetted_fix = TempFixture::new(Some(
        "-- anneal-trust-tier: vetted\nprelude\nimport Init.Data.BitVec.Lemmas\n",
    ));
    fs::copy(
        checkout.join("trusted/audit/library-lock.json"),
        vetted_fix.root.join("trusted/audit/library-lock.json"),
    )
    .unwrap();
    let err = vetted_fix.check_expected(Some(1), Some("preflight"), Some(false)).unwrap_err();
    assert!(
        err.message.contains(
            "vetted module Trusted cannot import non-foundation module Init.Data.BitVec.Lemmas"
        ),
        "unexpected error: {err}"
    );

    let mut cand_fix = TempFixture::new(Some(
        "-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.Data.BitVec.Lemmas\n",
    ));
    fs::copy(
        checkout.join("trusted/audit/library-lock.json"),
        cand_fix.root.join("trusted/audit/library-lock.json"),
    )
    .unwrap();
    let err = cand_fix.check_expected(Some(1), Some("preflight"), Some(false)).unwrap_err();
    assert!(
        err.message.contains("foreign/missing import Init.Data.BitVec.Lemmas in Trusted"),
        "unexpected error: {err}"
    );

    let mut theory_fix = TempFixture::new(Some(
        "-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.Core\n",
    ));
    fs::copy(
        checkout.join("trusted/audit/library-lock.json"),
        theory_fix.root.join("trusted/audit/library-lock.json"),
    )
    .unwrap();
    fs::create_dir_all(theory_fix.root.join("theory/Anneal")).unwrap();
    fs::write(
        theory_fix.root.join("theory/Anneal/Helper.lean"),
        "prelude\nimport Init.Data.BitVec.Lemmas\n",
    )
    .unwrap();
    fs::write(
        theory_fix.root.join("theory/Anneal.lean"),
        "prelude\nimport Init.Core\nimport Anneal.Helper\n",
    )
    .unwrap();
    let err = theory_fix.check_expected(Some(1), Some("preflight"), Some(false)).unwrap_err();
    assert!(
        err.message.contains("foreign/missing import Init.Data.BitVec.Lemmas in Anneal.Helper"),
        "unexpected error: {err}"
    );
}

/// Pass 1 `"preflight"` and `"audit"` admit Lean 4 `module`-system `Trusted`
/// and `theory/` files (`public import`, `@[expose] public section`,
/// `public section` + `@[expose] def`, private `import`, and narrowly scoped
/// `import all Init.Data.Nat.Bitwise.Basic` in `theory/`), thread `isModule`
/// into `lean --setup`, and fail closed when a `theory/` module attempts
/// `import all` on any non-allowlisted foundation module.
#[test]
fn admits_module_system_pass1_and_restricts_import_all() {
    // Positive case: `Trusted` and `Anneal` both use Lean 4 `module` syntax,
    // including `import all Init.Data.Nat.Bitwise.Basic` in `Anneal`.
    {
        let fix = TempFixture::new(Some(
            "-- anneal-trust-tier: vetted\n\
             module\n\
             prelude\n\
             public import Init.Core\n\
             @[expose] public section\n\
             namespace Trusted\n\
             def seed : Nat := 7\n\
             end Trusted\n\
             end\n",
        ));
        fs::create_dir_all(fix.root.join("theory")).unwrap();
        fs::write(
            fix.root.join("theory/Anneal.lean"),
            "module\n\
             prelude\n\
             public import Init.Core\n\
             public import Init.Data.Nat.Bitwise.Basic\n\
             public import Trusted\n\
             import all Init.Data.Nat.Bitwise.Basic\n\
             public section\n\
             namespace Anneal\n\
             @[expose] def bump : Nat := Trusted.seed\n\
             theorem land_bridge (n m : Nat) : Nat.land n m = Nat.bitwise and n m := by rfl\n\
             end Anneal\n\
             end\n",
        )
        .unwrap();

        let mut checker = fix.checker();
        checker.set_require_mir_wp(false);
        let report = checker.run().unwrap();
        assert_eq!(report["replay"], json!(true), "unexpected report: {report}");
        assert!(
            checker.stage().join("lib/Trusted.olean.private").exists(),
            "module-compiled Trusted must emit .olean.private"
        );
        assert!(
            checker.stage().join("theory-lib/Anneal.olean.private").exists(),
            "module-compiled Anneal must emit .olean.private"
        );
    }

    // Negative case: `theory/` cannot `import all` outside the narrow
    // `allowedTheoryImportAllModules` allowlist.
    {
        let fix = TempFixture::new(Some(
            "-- anneal-trust-tier: vetted\n\
             module\n\
             prelude\n\
             public import Init.Core\n\
             @[expose] public section\n\
             namespace Trusted\n\
             def seed : Nat := 7\n\
             end Trusted\n\
             end\n",
        ));
        fs::create_dir_all(fix.root.join("theory")).unwrap();
        fs::write(
            fix.root.join("theory/Anneal.lean"),
            "module\n\
             prelude\n\
             public import Init.Core\n\
             import all Init.Core\n\
             public section\n\
             theorem ok : True := True.intro\n\
             end\n",
        )
        .unwrap();

        let mut checker = fix.checker();
        checker.set_require_mir_wp(false);
        let err = checker.run().unwrap_err();
        assert_eq!(err.code, 1, "expected policy exit 1: {err}");
        assert_eq!(err.phase, "preflight", "expected preflight rejection: {err}");
        assert!(
            err.message.contains("import modifiers are unsupported"),
            "unexpected error: {err}"
        );
    }
}

/// Pass-1 `"preflight"` explicitly rejects `include_str`, `Init/Util.lean`'s
/// `lean_dbg_*` externs (`dbgSleep`, `dbgTrace`, `dbgTraceIfShared`,
/// `dbgStackTrace`), `Lean.LoadDynlib` / `loadDynlib`, `Init.System.*`, and
/// `Std.Internal.UV.*` in both `Trusted` and `theory/` modules.
#[test]
fn preflight_rejects_pure_signature_io_debug_dynlib_and_system_uv() {
    let cases = [
        (
            "include_str",
            "disallowed syntax",
            "def embedded : String := include_str \"Cargo.toml\"\n",
        ),
        ("dbgSleep", "disallowed reference", "def f : Nat := dbgSleep 0 (fun _ => 1)\n"),
        ("dbgTrace", "disallowed reference", "def f : Nat := dbgTrace \"leak\" (fun _ => 1)\n"),
        (
            "dbgTraceIfShared",
            "disallowed reference",
            "def f (x : Nat) : Nat := dbgTraceIfShared \"leak\" x\n",
        ),
        ("dbgStackTrace", "disallowed reference", "def f : Nat := dbgStackTrace (fun _ => 1)\n"),
        (
            "lean_dbg_trace",
            "disallowed reference",
            "def f : Nat := lean_dbg_trace \"leak\" (fun _ => 1)\n",
        ),
        (
            "lean_dbg_sleep",
            "disallowed reference",
            "def f : Nat := lean_dbg_sleep 0 (fun _ => 1)\n",
        ),
        ("loadDynlib", "disallowed reference", "def f : Nat → Nat := loadDynlib\n"),
        ("loadPlugin", "disallowed reference", "def f : Nat → Nat := loadPlugin\n"),
        ("lean_load_dynlib", "disallowed reference", "def f : Nat := Lean.LoadDynlib.foo\n"),
        ("init_system_ident", "disallowed reference", "def f := Init.System.FilePath.mk \".\"\n"),
        ("std_internal_uv_ident", "disallowed reference", "def f := Std.Internal.UV.Loop.mk\n"),
        (
            "open_init_system",
            "disallowed reference System.FilePath.mk",
            "open Init in\ndef f := System.FilePath.mk \".\"\n",
        ),
        (
            "open_std_internal_uv",
            "disallowed reference UV.Loop.mk",
            "open Std.Internal in\ndef f := UV.Loop.mk\n",
        ),
    ];
    for (label, expected_msg, body) in cases {
        let mut trusted_fix = TempFixture::new(Some(&format!("{HEADER}{body}")));
        let err = trusted_fix
            .check_expected(Some(1), Some("preflight"), Some(false))
            .expect_err(&format!("Trusted {label} must fail preflight"));
        assert!(err.message.contains(expected_msg), "Trusted {label}: {err}");

        let mut theory_fix = TempFixture::new(None);
        fs::create_dir_all(theory_fix.root.join("theory")).unwrap();
        fs::write(
            theory_fix.root.join("theory/Anneal.lean"),
            format!("prelude\nimport Init.NotationExtra\n{body}"),
        )
        .unwrap();
        let err = theory_fix
            .check_expected(Some(1), Some("preflight"), Some(false))
            .expect_err(&format!("Theory {label} must fail preflight"));
        assert!(err.message.contains(expected_msg), "Theory {label}: {err}");
    }

    for (label, imp) in [
        ("import_init_system_io", "import Init.System.IO\n"),
        ("import_std_internal_uv", "import Std.Internal.UV\n"),
        ("import_std_internal_uv_tcp", "import Std.Internal.UV.TCP\n"),
    ] {
        let mut theory_fix = TempFixture::new(None);
        fs::create_dir_all(theory_fix.root.join("theory")).unwrap();
        fs::write(
            theory_fix.root.join("theory/Anneal.lean"),
            format!("prelude\nimport Init.NotationExtra\n{imp}def ok : Nat := 0\n"),
        )
        .unwrap();
        let err = theory_fix.check_expected(Some(1), Some("preflight"), Some(false)).unwrap_err();
        assert!(err.message.contains("disallowed sysroot import"), "{label}: {err}");
    }
}

/// Pass-1 `"audit"` admits sibling modules independently realizing the same
/// equation theorem (`sameRealizedThmHeader`) and computable well-founded
/// recursive definitions (`wfStep._unsafe_rec` paired with safe `wfStep`),
/// while failing closed on logical references to `_unsafe_rec` helpers,
/// unpaired `partial` declarations, and mismatched duplicate theorems.
#[test]
fn audit_admits_diamond_realized_theorems_and_paired_unsafe_rec() {
    let trusted_wf = "-- anneal-trust-tier: vetted\n\
         prelude\n\
         import Init.NotationExtra\n\
         import Init.Data.Nat.Basic\n\
         import Init.SimpLemmas\n\
         namespace Trusted\n\
         def wfStep (n : Nat) : Nat :=\n  \
           if h : n = 0 then 0 else\n    \
             have : n - 1 < n := Nat.sub_one_lt h\n    \
             wfStep (n - 1)\n\
         end Trusted\n";
    let mut fix = TempFixture::new(Some(trusted_wf));
    fs::create_dir_all(fix.root.join("theory/Anneal")).unwrap();
    fs::write(
        fix.root.join("theory/Anneal.lean"),
        "prelude\nimport Init.NotationExtra\nimport Anneal.Left\nimport Anneal.Right\n",
    )
    .unwrap();
    for side in ["Left", "Right"] {
        fs::write(
            fix.root.join(format!("theory/Anneal/{side}.lean")),
            format!(
                "prelude\n\
                 import Init.NotationExtra\n\
                 import Init.Data.Nat.Basic\n\
                 import Init.SimpLemmas\n\
                 import Trusted\n\
                 namespace Anneal.{side}\n\
                 theorem step_zero : Trusted.wfStep 0 = 0 := by\n  \
                   rw [Trusted.wfStep]\n  \
                   decide\n\
                 def localWf (n : Nat) : Nat :=\n  \
                   if h : n = 0 then 0 else\n    \
                     have : n - 1 < n := Nat.sub_one_lt h\n    \
                     localWf (n - 1)\n\
                 end Anneal.{side}\n"
            ),
        )
        .unwrap();
    }
    let report = fix.check_expected(None, None, None).unwrap();
    assert_eq!(report["replay"], serde_json::json!(true), "{report}");

    // Negative 1: logical reference to a paired `_unsafe_rec` helper fails
    // closed in Pass-1 `"audit"`. Compile a stub `Trusted` where
    // `wfStep._unsafe_rec` is a safe `def` so Lean accepts
    // `Anneal.ForgedRecRef`, then swap that `.olean` into `fix`'s real
    // `Trusted` environment (`wfStep._unsafe_rec` is `partial`) and run
    // `"audit"` directly.
    let fix_ok = TempFixture::new(Some(trusted_wf));
    fs::create_dir_all(fix_ok.root.join("theory")).unwrap();
    fs::write(
        fix_ok.root.join("theory/Anneal.lean"),
        "prelude\nimport Init.NotationExtra\nimport Trusted\n",
    )
    .unwrap();
    let mut checker_ok = fix_ok.checker();
    checker_ok.set_require_mir_wp(false);
    checker_ok.run().unwrap();

    let fix_stub = TempFixture::new(Some(
        "-- anneal-trust-tier: vetted\n\
         prelude\n\
         import Init.NotationExtra\n\
         namespace Trusted\n\
         def wfStep (n : Nat) : Nat := n\n\
         def wfStep._unsafe_rec (n : Nat) : Nat := n\n\
         end Trusted\n",
    ));
    fs::create_dir_all(fix_stub.root.join("theory")).unwrap();
    fs::write(
        fix_stub.root.join("theory/Anneal.lean"),
        "prelude\nimport Init.NotationExtra\nimport Trusted\n",
    )
    .unwrap();
    let mut stub_checker = fix_stub.checker();
    stub_checker.set_require_mir_wp(false);
    stub_checker.run().unwrap();
    let stub_lib = stub_checker.stage().join("lib");
    let forged_src = stub_checker.stage().join("src/forged-rec");
    compile_forged_module(
        &mut stub_checker,
        &forged_src,
        &stub_lib,
        &["Trusted"],
        "Anneal.ForgedRecRef",
        "prelude\n\
         import Init.Core\n\
         import Trusted\n\
         theorem Anneal.ForgedRecRef.bad (n : Nat) :\n  \
           Trusted.wfStep._unsafe_rec n = Trusted.wfStep._unsafe_rec n := rfl\n",
    );

    let forged_dst = checker_ok.stage().join("lib/Anneal/ForgedRecRef.olean");
    fs::create_dir_all(forged_dst.parent().unwrap()).unwrap();
    fs::copy(stub_lib.join("Anneal/ForgedRecRef.olean"), &forged_dst).unwrap();
    let edges = vec![
        ImportEdge {
            module: "Init.Core".to_string(),
            import_all: false,
            is_exported: true,
            is_meta: false,
        },
        ImportEdge {
            module: "Trusted".to_string(),
            import_all: false,
            is_exported: true,
            is_meta: false,
        },
    ];
    let avail = BTreeMap::from([("olean", forged_dst.to_string_lossy().into_owned())]);
    let forged_arts = ModuleArtifacts::from_available(&avail, "test", String::new).unwrap();
    let adm = checker_ok.admitted_mut().unwrap();
    adm.artifacts.insert("Anneal.ForgedRecRef".to_string(), forged_arts);
    adm.graph.insert("Anneal.ForgedRecRef".to_string(), edges);

    let rec_err = checker_ok
        .inspect(InspectorRequest::Audit {
            trusted: vec!["Trusted".to_string()],
            theory: vec!["Anneal".to_string(), "Anneal.ForgedRecRef".to_string()],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert_eq!(rec_err.code, 1, "{rec_err}");
    assert_eq!(rec_err.phase, "audit", "{rec_err}");
    assert!(
        rec_err.message.contains("paired _unsafe_rec helper Trusted.wfStep._unsafe_rec"),
        "{rec_err}"
    );

    // Negative 2: unpaired `partial def` (parent is `.opaqueInfo` rather than
    // a safe `.defnInfo`) bypassing `"preflight"` fails closed in `"audit"`.
    // Drop `Anneal.ForgedRecRef` from `checker_ok` so the admitted graph
    // matches `[Trusted, Trusted.ForgedPartial, Anneal]`.
    let adm_mut = checker_ok.admitted_mut().unwrap();
    adm_mut.artifacts.remove("Anneal.ForgedRecRef");
    adm_mut.graph.remove("Anneal.ForgedRecRef");
    let forged_partial_src = checker_ok.stage().join("src/forged-partial");
    let ok_lib = checker_ok.stage().join("lib");
    compile_forged_module(
        &mut checker_ok,
        &forged_partial_src,
        &ok_lib,
        &[],
        "Trusted.ForgedPartial",
        "prelude\nimport Init.Core\n\
         partial def Trusted.ForgedPartial.barePartial : Nat → Nat\n  \
           | n => barePartial n\n",
    );
    let partial_err = checker_ok
        .inspect(InspectorRequest::Audit {
            trusted: vec!["Trusted".to_string(), "Trusted.ForgedPartial".to_string()],
            theory: vec!["Anneal".to_string()],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                ("Trusted.ForgedPartial".to_string(), TrustTier::Vetted),
            ]),
        })
        .unwrap_err();
    assert_eq!(partial_err.code, 1, "{partial_err}");
    assert_eq!(partial_err.phase, "audit", "{partial_err}");
    assert!(partial_err.message.contains("unsafe/partial declaration"), "{partial_err}");

    // Negative 3: diamond siblings defining the same theorem header with an
    // ill-typed forged alternate proof pass Lean's `importModules`
    // (`subsumesInfo` ignores `.thmInfo.value`) and fail closed in Pass-1
    // `"audit"` via `inventoryAlternates` + `checkAlternateProofs`.
    let adm_mut = checker_ok.admitted_mut().unwrap();
    adm_mut.artifacts.remove("Trusted.ForgedPartial");
    adm_mut.graph.remove("Trusted.ForgedPartial");
    let left_src = checker_ok.stage().join("src/forged-dup-left");
    compile_forged_module(
        &mut checker_ok,
        &left_src,
        &ok_lib,
        &[],
        "Anneal.DupLeft",
        "prelude\nimport Init.Core\n\
         theorem Anneal.Shared.dup : True := True.intro\n",
    );
    let right_olean = ok_lib.join("Anneal/DupRight.olean");
    let right_script = checker_ok.stage().join("forge-dup-right.lean");
    run_lean_script(
        &mut checker_ok,
        "forge-dup-right",
        &right_script,
        &format!(
            "import Lean\n\
             open Lean\n\
             def main : IO Unit := do\n  \
               let ci : ConstantInfo := .thmInfo {{\n    \
                 name := `Anneal.Shared.dup\n    \
                 levelParams := []\n    \
                 type := .const `True []\n    \
                 value := .const `False []\n    \
                 all := [`Anneal.Shared.dup]\n  \
               }}\n  \
               let md : ModuleData := {{\n    \
                 isModule := false\n    \
                 imports := #[{{ module := `Init.Core }}]\n    \
                 constNames := #[`Anneal.Shared.dup]\n    \
                 constants := #[ci]\n    \
                 extraConstNames := #[]\n    \
                 entries := #[]\n  \
               }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Anneal.DupRight md\n",
            right_olean.to_string_lossy()
        ),
    );
    let core_edge = vec![ImportEdge {
        module: "Init.Core".to_string(),
        import_all: false,
        is_exported: true,
        is_meta: false,
    }];
    let right_arts = ModuleArtifacts::from_available(
        &BTreeMap::from([("olean", right_olean.to_string_lossy().into_owned())]),
        "test",
        String::new,
    )
    .unwrap();
    let adm_dup = checker_ok.admitted_mut().unwrap();
    adm_dup.artifacts.insert("Anneal.DupRight".to_string(), right_arts);
    adm_dup.graph.insert("Anneal.DupRight".to_string(), core_edge);
    let thm_err = checker_ok
        .inspect(InspectorRequest::Audit {
            trusted: vec!["Trusted".to_string()],
            theory: vec![
                "Anneal".to_string(),
                "Anneal.DupLeft".to_string(),
                "Anneal.DupRight".to_string(),
            ],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert_eq!(thm_err.phase, "audit", "{thm_err}");
    assert!(
        thm_err.message.contains("alternate pinned theorem proof check Anneal.Shared.dup"),
        "{thm_err}"
    );
}

/// Verifies `autoParam` and `Lean.Syntax` isolation across preflight and audit:
/// - Rejects `Init.Meta*`, `autoParam`, `optParam`, `Lean.Syntax*`,
///   `Lean.Name*`, `Lean.SourceInfo*`, `Lean.TSyntax*`, `Lean.Elab*`, and
///   `Lean.Macro*` during Pass-1 `"preflight"` and Pass-2
///   `"correspondence-preflight"` before any Lean module compilation occurs
///   (`execution_began() == false`).
/// - Defense in depth on compiled `.olean`s audited directly in Pass-1
///   `"audit"` and Pass-2 `"correspondence-audit"`: rejects non-`_auto_`
///   `Lean.Syntax` constants, non-literal `_auto_<N>` bodies (e.g. `let`/
///   `Array.mk`), literal `_auto_<N>` scripts encoding disallowed tactics
///   (`set_option ... in ...`), `_auto_<N>` helpers outside `theory/` or
///   `correspondence/`, direct references to `_auto_<N>` / `Lean.Name` /
///   malformed `autoParam`, while still admitting legitimate `theory/`
///   `binderTactic` (`:= by rfl`) helpers and non-`Syntax` declarations whose
///   names happen to end in `_auto_<N>` or `_autoParam`.
#[test]
fn rejects_autoparam_and_syntax_construction_across_preflight_and_olean_audit() {
    // 1. Positive control: legitimate `binderTactic` (`:= by rfl`) and pure
    //    non-`Syntax` declarations named `_auto_1` / `_autoParam` /
    //    `cache_auto_1` in `theory/Anneal.lean` pass full Pass-1 preflight,
    //    compilation, and `validateRepoAutoParamAndMeta` replay.
    let mut good_fix = TempFixture::new(Some(HEADER));
    fs::create_dir_all(good_fix.root.join("theory")).unwrap();
    fs::write(
        good_fix.root.join("theory/Anneal.lean"),
        "prelude\nimport Init.NotationExtra\nimport Trusted\n\
         namespace Anneal\n\
         namespace Sub\ndef subVal : Nat := 7\nend Sub\n\
         export Sub (subVal)\n\
         private theorem privRfl : 0 = 0 := rfl\n\
         def goodBinderAuto (n : Nat) (_h : 0 = 0 := by rfl) : Nat := n\n\
         def goodPrivAuto (n : Nat) (_h : 0 = 0 := by exact privRfl) : Nat := n\n\
         def _auto_1 : Nat := 1\n\
         def _autoParam : Nat := 2\n\
         def cache_auto_1 : Nat := 3\n\
         def useAutoNamed : Nat := _auto_1 + _autoParam + cache_auto_1 + subVal\n\
         end Anneal\n",
    )
    .unwrap();
    let rep_ok = good_fix.check_expected(None, None, None).unwrap();
    assert_eq!(rep_ok.get("replay"), Some(&json!(true)));

    // 2. Pass-1 `"preflight"` rejections in both `theory/Anneal.lean` and
    //    `Trusted.lean` with `execution_began() == false`.
    let import_cases = [
        ("import_init_meta_defs", "import Init.Meta.Defs\n"),
        ("import_init_meta", "import Init.Meta\n"),
    ];
    for (label, imp) in import_cases {
        let mut theory_fix = TempFixture::new(Some(HEADER));
        fs::create_dir_all(theory_fix.root.join("theory")).unwrap();
        fs::write(
            theory_fix.root.join("theory/Anneal.lean"),
            format!("prelude\nimport Init.NotationExtra\n{imp}def Anneal.bad : Nat := 0\n"),
        )
        .unwrap();
        let err = theory_fix
            .check_expected(Some(1), Some("preflight"), Some(false))
            .expect_err(&format!("theory {label} must fail preflight"));
        assert!(err.message.contains("disallowed sysroot import"), "theory {label}: {err}");

        let mut trusted_fix = TempFixture::new(Some(&format!("{HEADER}{imp}")));
        let err_t = trusted_fix
            .check_expected(Some(1), Some("preflight"), Some(false))
            .expect_err(&format!("trusted {label} must fail preflight"));
        assert!(err_t.message.contains("disallowed sysroot import"), "trusted {label}: {err_t}");
    }

    let pure_cases = [
        (
            "auto_param",
            "disallowed reference autoParam",
            "def badAuto (h : autoParam (0 = 0) x) : Nat := 0\n",
        ),
        (
            "opt_param",
            "disallowed reference optParam",
            "def badOpt (n : optParam Nat 0) : Nat := n\n",
        ),
        (
            "lean_syntax_node",
            "disallowed reference Lean.Syntax.node",
            "def badNode := Lean.Syntax.node\n",
        ),
        (
            "lean_source_info",
            "disallowed reference Lean.SourceInfo.none",
            "def badInfo := Lean.SourceInfo.none\n",
        ),
        ("lean_mk_atom", "disallowed reference Lean.mkAtom", "def badAtom := Lean.mkAtom \"x\"\n"),
        (
            "lean_name_mkstr",
            "disallowed reference Lean.Name.mkStr1",
            "def badName := Lean.Name.mkStr1 \"x\"\n",
        ),
        ("lean_tsyntax", "disallowed reference Lean.TSyntax", "def badTStx := Lean.TSyntax\n"),
        (
            "lean_elab",
            "disallowed reference Lean.Elab.Command.CommandElab",
            "def badElab := Lean.Elab.Command.CommandElab\n",
        ),
        (
            "lean_macro",
            "disallowed reference Lean.Macro.throwUnsupported",
            "def badMacro := Lean.Macro.throwUnsupported\n",
        ),
        (
            "lean_term_alias",
            "disallowed reference Lean.Term",
            "def badTerm := Lean.Term\n",
        ),
        (
            "lean_mk_lit",
            "disallowed reference Lean.mkLit",
            "def badLit := Lean.mkLit\n",
        ),
        (
            "repo_export_std_uv",
            "disallowed export item Std.Internal.UV.Loop.alive",
            "export Std.Internal (UV.Loop.alive)\n",
        ),
        (
            "repo_export_std_async",
            "disallowed export item Std.Async.DNS.getAddrInfo",
            "export Std (Async.DNS.getAddrInfo)\n",
        ),
        (
            "repo_export_std_http",
            "disallowed export item Std.Http.Client",
            "export Std (Http.Client)\n",
        ),
        // Chained `export` -> `open` alias tracking (`top`, `in`, and `mutual`)
        // in `TrustedBoundary.lean` is exercised against scoped namespaces in
        // `pass2_syntax_preflight::rejects_scoped_syntax_and_extensions_in_preflight`
        // (`Anneal.ChainedExport{,In,Mutual}ScopedOpen`).
        (
            "repo_nested_ns_raw_io",
            "disallowed reference IO",
            "namespace SubWrap\nnamespace IO\ndef x : Nat := 0\nend IO\nend SubWrap\n",
        ),
        (
            "repo_export_raw_io_item",
            "disallowed reference IO.println",
            "namespace SubWrap\nexport Sub (IO.println)\nend SubWrap\n",
        ),
        (
            "repo_open_raw_dbg_trace",
            "disallowed reference dbgTrace",
            "open dbgTrace\n",
        ),
        (
            "repo_export_lean_root",
            "cannot export from forbidden namespace Lean.Parser",
            "export Lean.Parser (ident)\n",
        ),
        (
            "repo_unlisted_lean_loop_member",
            "disallowed reference Lean.Loop.fake",
            "def x := Lean.Loop.fake\n",
        ),
        (
            "repo_open_lean_loop",
            "cannot open forbidden namespace Lean.Loop",
            "open Lean.Loop\n",
        ),
        (
            "repo_export_lean_loop",
            "cannot export from forbidden namespace Lean.Loop",
            "export Lean.Loop (mk)\n",
        ),
    ];
    // 3. Defense in depth in Pass-1 `"audit"`: forged `.olean` modules
    //    audited directly against `TrustedBoundary.lean`. Reuse one
    //    admitted checker for the pure-identifier preflight matrix so the test
    //    stays well under CI's nextest timeout.
    let fix_audit = TempFixture::new(Some(HEADER));
    fs::create_dir_all(fix_audit.root.join("theory")).unwrap();
    fs::write(
        fix_audit.root.join("theory/Anneal.lean"),
        "prelude\nimport Init.NotationExtra\nimport Trusted\n",
    )
    .unwrap();
    let mut checker = fix_audit.checker();
    checker.set_require_mir_wp(false);
    checker.run().unwrap();
    let stage = checker.stage().to_path_buf();
    let theory_lib = stage.join("lib");
    let forged_src = stage.join("src/forged-auto");
    let pf_src = stage.join("src/auto-pf");
    fs::create_dir_all(&pf_src).unwrap();

    for (label, expected_msg, body) in pure_cases {
        let theory_p = pf_src.join(format!("theory_{label}.lean"));
        fs::write(
            &theory_p,
            format!("prelude\nimport Init.NotationExtra\nnamespace Anneal\n{body}end Anneal\n"),
        )
        .unwrap();
        let err = checker
            .inspect(InspectorRequest::Preflight {
                sources: vec![("Anneal".to_string(), theory_p)],
                base_trusted_sources: Vec::new(),
                allow_local_semireducible: true,
            })
            .expect_err(&format!("theory {label} must fail preflight"));
        assert_eq!((err.code, err.phase.as_str()), (1, "preflight"), "theory {label}: {err}");
        assert!(err.message.contains(expected_msg), "theory {label}: {err}");

        let trusted_p = pf_src.join(format!("trusted_{label}.lean"));
        fs::write(&trusted_p, format!("{HEADER}{body}")).unwrap();
        let err_t = checker
            .inspect(InspectorRequest::Preflight {
                sources: vec![("Trusted".to_string(), trusted_p)],
                base_trusted_sources: Vec::new(),
                allow_local_semireducible: false,
            })
            .expect_err(&format!("trusted {label} must fail preflight"));
        assert_eq!(
            (err_t.code, err_t.phase.as_str()),
            (1, "preflight"),
            "trusted {label}: {err_t}"
        );
        assert!(err_t.message.contains(expected_msg), "trusted {label}: {err_t}");
    }

    // Closed allowlist `allowedRepoSurfaceLeanDecls` admits the exact 7 pure
    // `Init.*` `Lean.Loop` / `Lean.Order` constants used by loop-unfolding
    // proofs in `theory/` and `correspondence/` term position while keeping
    // `Trusted` modules, top-level `Lean.*` declarations, and `open`/`export`/
    // other `Lean.*` identifiers blocked.
    let loop_pos_p = pf_src.join("theory_allowed_lean_loop_order.lean");
    fs::write(
        &loop_pos_p,
        "prelude\nimport Init.Control.Do\nnamespace Anneal\n\
         def loopRefs := (Lean.Loop, Lean.Loop.mk, Lean.Loop.forIn_eq_of_monadTail,\n  \
           Lean.Order.MonadTail, Lean.Order.instCCPOPi,\n  \
           Lean.Order.FlatOrder.instCCPO, Lean.Order.FlatOrder.rel.refl)\n\
         end Anneal\n",
    )
    .unwrap();
    checker
        .inspect(InspectorRequest::Preflight {
            sources: vec![("Anneal".to_string(), loop_pos_p)],
            base_trusted_sources: Vec::new(),
            allow_local_semireducible: true,
        })
        .expect("allowedRepoSurfaceLeanDecls must pass theory preflight");

    let trusted_loop_p = pf_src.join("trusted_disallowed_lean_loop.lean");
    fs::write(
        &trusted_loop_p,
        format!("{HEADER}import Init.Control.Do\nnamespace Trusted\ndef loopRef := Lean.Loop.mk\nend Trusted\n"),
    )
    .unwrap();
    let err_trusted_loop = checker
        .inspect(InspectorRequest::Preflight {
            sources: vec![("Trusted".to_string(), trusted_loop_p)],
            base_trusted_sources: Vec::new(),
            allow_local_semireducible: false,
        })
        .expect_err("Trusted modules must still reject Lean.Loop.mk in preflight");
    assert_eq!((err_trusted_loop.code, err_trusted_loop.phase.as_str()), (1, "preflight"));
    assert!(
        err_trusted_loop.message.contains("disallowed reference Lean.Loop.mk"),
        "trusted Lean.Loop.mk: {err_trusted_loop}"
    );

    let top_decl_loop_p = pf_src.join("theory_declare_lean_loop_mk.lean");
    fs::write(
        &top_decl_loop_p,
        "prelude\nimport Init.NotationExtra\n\
         def Lean.Loop.mk : Nat := 0\n",
    )
    .unwrap();
    let err_top_decl = checker
        .inspect(InspectorRequest::Preflight {
            sources: vec![("Anneal".to_string(), top_decl_loop_p)],
            base_trusted_sources: Vec::new(),
            allow_local_semireducible: true,
        })
        .expect_err("declaring top-level Lean.Loop.mk must fail preflight");
    assert_eq!((err_top_decl.code, err_top_decl.phase.as_str()), (1, "preflight"));
    assert!(
        err_top_decl.message.contains("cannot declare in namespace Lean with scoped syntax or extensions"),
        "top decl Lean.Loop.mk: {err_top_decl}"
    );

    // Top-level `export` in `theory/` and `Trusted` must validate the created
    // alias name `currNs ++ itemId` (`currNs = .anonymous`), rejecting
    // `Trusted.*` aliases outside `Trusted` and reserved/forbidden alias roots
    // (`Expected.*`, `IO.*`, `Lean.*`) everywhere.
    for (label, theory_only, expected_msg, src) in [
        (
            "top_export_trusted",
            true,
            "non-Trusted module cannot export alias Trusted.fake in Trusted namespace",
            "prelude\nimport Init.Core\n\
             namespace Anneal.Foo.Trusted\ndef fake : Nat := 0\nend Anneal.Foo.Trusted\n\
             export Anneal.Foo (Trusted.fake)\n",
        ),
        (
            "top_export_expected",
            false,
            "cannot export alias Expected.claim in reserved kernel namespace Expected",
            "prelude\nimport Init.Core\n\
             namespace Anneal.Foo.Expected\ndef claim : Prop := True\nend Anneal.Foo.Expected\n\
             export Anneal.Foo (Expected.claim)\n",
        ),
        (
            "top_export_io",
            false,
            "cannot export alias IO.println in reserved kernel namespace IO",
            "prelude\nimport Init.Core\n\
             namespace Anneal.Foo.IO\ndef println : Nat := 0\nend Anneal.Foo.IO\n\
             export Anneal.Foo (IO.println)\n",
        ),
        (
            "top_export_lean",
            false,
            "cannot export alias Lean.fake in reserved kernel namespace Lean",
            "prelude\nimport Init.Core\n\
             namespace Anneal.Foo.Lean\ndef fake : Nat := 0\nend Anneal.Foo.Lean\n\
             export Anneal.Foo (Lean.fake)\n",
        ),
    ] {
        let p_th = pf_src.join(format!("theory_{label}.lean"));
        fs::write(&p_th, src).unwrap();
        let err = checker
            .inspect(InspectorRequest::Preflight {
                sources: vec![("Anneal".to_string(), p_th)],
                base_trusted_sources: Vec::new(),
                allow_local_semireducible: true,
            })
            .expect_err(&format!("theory {label} must fail preflight"));
        assert_eq!((err.code, err.phase.as_str()), (1, "preflight"), "theory {label}: {err}");
        assert!(err.message.contains(expected_msg), "theory {label}: {err}");

        if !theory_only {
            let p_tr = pf_src.join(format!("trusted_{label}.lean"));
            fs::write(
                &p_tr,
                format!("-- anneal-trust-tier: vetted\n{src}"),
            )
            .unwrap();
            let err_t = checker
                .inspect(InspectorRequest::Preflight {
                    sources: vec![("Trusted".to_string(), p_tr)],
                    base_trusted_sources: Vec::new(),
                    allow_local_semireducible: false,
                })
                .expect_err(&format!("trusted {label} must fail preflight"));
            assert_eq!(
                (err_t.code, err_t.phase.as_str()),
                (1, "preflight"),
                "trusted {label}: {err_t}"
            );
            assert!(err_t.message.contains(expected_msg), "trusted {label}: {err_t}");
        }
    }

    for (module, body, expected_msg) in [
        (
            "Anneal.ForgeNonAutoSyntax",
            "prelude\nimport Init.Core\n\
             def Anneal.ForgeNonAutoSyntax.s : Lean.Syntax := Lean.mkAtom \"x\"\n",
            "disallowed Lean.Syntax declaration Anneal.ForgeNonAutoSyntax.s",
        ),
        (
            "Anneal.ForgeObfAuto",
            "prelude\nimport Init.Core\n\
             def Anneal.ForgeObfAuto.f._auto_1 : Lean.Syntax :=\n  \
               Lean.Syntax.node .none .anonymous (Array.mk (List.cons (Lean.mkAtom \"x\") List.nil))\n\
             def Anneal.ForgeObfAuto.f (_h : autoParam (0 = 0) Anneal.ForgeObfAuto.f._auto_1) : Nat := 0\n",
            "disallowed non-literal autoParam tactic Anneal.ForgeObfAuto.f._auto_1",
        ),
        (
            "Anneal.ForgeLetAuto",
            "prelude\nimport Init.Core\n\
             def Anneal.ForgeLetAuto.f._auto_1 : Lean.Syntax :=\n  \
               let a := Lean.mkAtom \"x\"\n  a\n\
             def Anneal.ForgeLetAuto.f (_h : autoParam (0 = 0) Anneal.ForgeLetAuto.f._auto_1) : Nat := 0\n",
            "disallowed non-literal autoParam tactic Anneal.ForgeLetAuto.f._auto_1",
        ),
        (
            "Anneal.ForgeBadAutoTactic",
            "prelude\nimport Init.Core\n\
             def Anneal.ForgeBadAutoTactic.f (_h : 0 = 0 := by set_option maxHeartbeats 1 in exact rfl) : Nat := 0\n",
            "disallowed syntax",
        ),
        // Literal `Syntax.ident` with harmless `x` name and forbidden
        // `IO.println` preresolved entry passes `decodePureAutoSyntax?` and
        // `inspectSyntax`, specifically exercising
        // `inspectDecodedAutoPreresolved`.
        (
            "Anneal.ForgePreresolvedAuto",
            "prelude\nimport Init.Core\n\
             def Anneal.ForgePreresolvedAuto.f._auto_1 : Lean.Syntax :=\n  \
               Lean.Syntax.ident Lean.SourceInfo.none (String.toRawSubstring \"x\")\n    \
                 (Lean.Name.mkStr1 \"x\")\n    \
                 (List.cons (Lean.Syntax.Preresolved.decl (Lean.Name.mkStr2 \"IO\" \"println\") List.nil) List.nil)\n\
             def Anneal.ForgePreresolvedAuto.f (_h : autoParam (0 = 0) Anneal.ForgePreresolvedAuto.f._auto_1) : Nat := 0\n",
            "disallowed reference x",
        ),
        // Private-mangled preresolved target
        // (`_private.Init.Core.0.IO.println`) using Lean's actual
        // `OfNat.ofNat` literal encoding (`0`, matching `ToExpr Name` /
        // `Lean.mkNatLit`) must be decoded and normalized via
        // `privateToUserName` before checking forbidden namespaces.
        (
            "Anneal.ForgePrivatePreresolvedAuto",
            "prelude\nimport Init.Core\n\
             def Anneal.ForgePrivatePreresolvedAuto.f._auto_1 : Lean.Syntax :=\n  \
               Lean.Syntax.ident Lean.SourceInfo.none (String.toRawSubstring \"x\")\n    \
                 (Lean.Name.mkStr1 \"x\")\n    \
                 (List.cons (Lean.Syntax.Preresolved.decl (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.mkStr3 \"_private\" \"Init\" \"Core\") 0) \"IO\") \"println\") List.nil) List.nil)\n\
             def Anneal.ForgePrivatePreresolvedAuto.f (_h : autoParam (0 = 0) Anneal.ForgePrivatePreresolvedAuto.f._auto_1) : Nat := 0\n",
            "disallowed reference x",
        ),
        // Raw `.lit (.natVal 0)` encoding is also decoded and normalized.
        (
            "Anneal.ForgeRawNatLitPreresolvedAuto",
            "prelude\nimport Init.Core\n\
             def Anneal.ForgeRawNatLitPreresolvedAuto.f._auto_1 : Lean.Syntax :=\n  \
               Lean.Syntax.ident Lean.SourceInfo.none (String.toRawSubstring \"x\")\n    \
                 (Lean.Name.mkStr1 \"x\")\n    \
                 (List.cons (Lean.Syntax.Preresolved.decl (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.mkStr3 \"_private\" \"Init\" \"Core\") (nat_lit 0)) \"IO\") \"println\") List.nil) List.nil)\n\
             def Anneal.ForgeRawNatLitPreresolvedAuto.f (_h : autoParam (0 = 0) Anneal.ForgeRawNatLitPreresolvedAuto.f._auto_1) : Nat := 0\n",
            "disallowed reference x",
        ),
        // Custom `OfNat` instance (`{ ofNat := 99 }` instead of `instOfNatNat`)
        // is rejected as non-literal.
        (
            "Anneal.ForgeMismatchedOfNatAuto",
            "prelude\nimport Init.Core\n\
             def Anneal.ForgeMismatchedOfNatAuto.f._auto_1 : Lean.Syntax :=\n  \
               Lean.Syntax.ident Lean.SourceInfo.none (String.toRawSubstring \"x\")\n    \
                 (Lean.Name.num .anonymous (@OfNat.ofNat Nat (nat_lit 0) { ofNat := 99 }))\n    \
                 List.nil\n\
             def Anneal.ForgeMismatchedOfNatAuto.f (_h : autoParam (0 = 0) Anneal.ForgeMismatchedOfNatAuto.f._auto_1) : Nat := 0\n",
            "disallowed non-literal autoParam tactic Anneal.ForgeMismatchedOfNatAuto.f._auto_1",
        ),
        // Private-mangled preresolved target in a forbidden module
        // (`_private.Init.System.IO.0.secret`) using `OfNat.ofNat` (`0`) must
        // also be rejected via its embedded module prefix.
        (
            "Anneal.ForgePrivateModPreresolvedAuto",
            "prelude\nimport Init.Core\n\
             def Anneal.ForgePrivateModPreresolvedAuto.f._auto_1 : Lean.Syntax :=\n  \
               Lean.Syntax.ident Lean.SourceInfo.none (String.toRawSubstring \"x\")\n    \
                 (Lean.Name.mkStr1 \"x\")\n    \
                 (List.cons (Lean.Syntax.Preresolved.decl (Lean.Name.str (Lean.Name.num (Lean.Name.mkStr4 \"_private\" \"Init\" \"System\" \"IO\") 0) \"secret\") List.nil) List.nil)\n\
             def Anneal.ForgePrivateModPreresolvedAuto.f (_h : autoParam (0 = 0) Anneal.ForgePrivateModPreresolvedAuto.f._auto_1) : Nat := 0\n",
            "disallowed reference x",
        ),
        // `_root_`-prefixed and multi-`_root_` / embedded-`_root_` preresolved
        // targets (`OfNat.ofNat` `0`) must strip arbitrary leading `_root_`
        // segments via `stripLeadingRootPrefix` and reject embedded `_root_`.
        (
            "Anneal.ForgeRootPrivatePreresolvedAuto",
            "prelude\nimport Init.Core\n\
             def Anneal.ForgeRootPrivatePreresolvedAuto.f._auto_1 : Lean.Syntax :=\n  \
               Lean.Syntax.ident Lean.SourceInfo.none (String.toRawSubstring \"x\")\n    \
                 (Lean.Name.mkStr1 \"x\")\n    \
                 (List.cons (Lean.Syntax.Preresolved.decl (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.mkStr4 \"_root_\" \"_private\" \"Init\" \"Core\") 0) \"IO\") \"println\") List.nil) List.nil)\n\
             def Anneal.ForgeRootPrivatePreresolvedAuto.f (_h : autoParam (0 = 0) Anneal.ForgeRootPrivatePreresolvedAuto.f._auto_1) : Nat := 0\n",
            "disallowed reference x",
        ),
        (
            "Anneal.ForgeMultiRootPrivModPreresolvedAuto",
            "prelude\nimport Init.Core\n\
             def Anneal.ForgeMultiRootPrivModPreresolvedAuto.f._auto_1 : Lean.Syntax :=\n  \
               Lean.Syntax.ident Lean.SourceInfo.none (String.toRawSubstring \"x\")\n    \
                 (Lean.Name.mkStr1 \"x\")\n    \
                 (List.cons (Lean.Syntax.Preresolved.decl (Lean.Name.str (Lean.Name.num (Lean.Name.mkStr6 \"_root_\" \"_root_\" \"_private\" \"Init\" \"System\" \"IO\") 0) \"secret\") List.nil) List.nil)\n\
             def Anneal.ForgeMultiRootPrivModPreresolvedAuto.f (_h : autoParam (0 = 0) Anneal.ForgeMultiRootPrivModPreresolvedAuto.f._auto_1) : Nat := 0\n",
            "disallowed reference x",
        ),
        (
            "Anneal.ForgeMultiRootIoPreresolvedAuto",
            "prelude\nimport Init.Core\n\
             def Anneal.ForgeMultiRootIoPreresolvedAuto.f._auto_1 : Lean.Syntax :=\n  \
               Lean.Syntax.ident Lean.SourceInfo.none (String.toRawSubstring \"x\")\n    \
                 (Lean.Name.mkStr1 \"x\")\n    \
                 (List.cons (Lean.Syntax.Preresolved.decl (Lean.Name.mkStr6 \"_root_\" \"_root_\" \"_root_\" \"_root_\" \"IO\" \"println\") List.nil) List.nil)\n\
             def Anneal.ForgeMultiRootIoPreresolvedAuto.f (_h : autoParam (0 = 0) Anneal.ForgeMultiRootIoPreresolvedAuto.f._auto_1) : Nat := 0\n",
            "disallowed reference x",
        ),
        (
            "Anneal.ForgeMultiRootAutoParamPreresolvedAuto",
            "prelude\nimport Init.Core\n\
             def Anneal.ForgeMultiRootAutoParamPreresolvedAuto.f._auto_1 : Lean.Syntax :=\n  \
               Lean.Syntax.ident Lean.SourceInfo.none (String.toRawSubstring \"x\")\n    \
                 (Lean.Name.mkStr1 \"x\")\n    \
                 (List.cons (Lean.Syntax.Preresolved.decl (Lean.Name.mkStr4 \"_root_\" \"_root_\" \"_root_\" \"autoParam\") List.nil) List.nil)\n\
             def Anneal.ForgeMultiRootAutoParamPreresolvedAuto.f (_h : autoParam (0 = 0) Anneal.ForgeMultiRootAutoParamPreresolvedAuto.f._auto_1) : Nat := 0\n",
            "disallowed reference x",
        ),
        (
            "Anneal.ForgeMultiRootIncludeStrPreresolvedAuto",
            "prelude\nimport Init.Core\n\
             def Anneal.ForgeMultiRootIncludeStrPreresolvedAuto.f._auto_1 : Lean.Syntax :=\n  \
               Lean.Syntax.ident Lean.SourceInfo.none (String.toRawSubstring \"x\")\n    \
                 (Lean.Name.mkStr1 \"x\")\n    \
                 (List.cons (Lean.Syntax.Preresolved.decl (Lean.Name.mkStr4 \"_root_\" \"_root_\" \"_root_\" \"includeStr\") List.nil) List.nil)\n\
             def Anneal.ForgeMultiRootIncludeStrPreresolvedAuto.f (_h : autoParam (0 = 0) Anneal.ForgeMultiRootIncludeStrPreresolvedAuto.f._auto_1) : Nat := 0\n",
            "disallowed reference x",
        ),
        (
            "Anneal.ForgeEmbeddedRootPrivatePreresolvedAuto",
            "prelude\nimport Init.Core\n\
             def Anneal.ForgeEmbeddedRootPrivatePreresolvedAuto.f._auto_1 : Lean.Syntax :=\n  \
               Lean.Syntax.ident Lean.SourceInfo.none (String.toRawSubstring \"x\")\n    \
                 (Lean.Name.mkStr1 \"x\")\n    \
                 (List.cons (Lean.Syntax.Preresolved.decl (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.mkStr3 \"_private\" \"Init\" \"Core\") 0) \"_root_\") \"_root_\") \"_private\") \"Init\") \"System\") \"IO\") 0) \"secret\") List.nil) List.nil)\n\
             def Anneal.ForgeEmbeddedRootPrivatePreresolvedAuto.f (_h : autoParam (0 = 0) Anneal.ForgeEmbeddedRootPrivatePreresolvedAuto.f._auto_1) : Nat := 0\n",
            "disallowed reference x",
        ),
        // Nested `_private` preresolved target (`OfNat.ofNat` `0`) must be
        // rejected fail-closed.
        (
            "Anneal.ForgeNestedPrivatePreresolvedAuto",
            "prelude\nimport Init.Core\n\
             def Anneal.ForgeNestedPrivatePreresolvedAuto.f._auto_1 : Lean.Syntax :=\n  \
               Lean.Syntax.ident Lean.SourceInfo.none (String.toRawSubstring \"x\")\n    \
                 (Lean.Name.mkStr1 \"x\")\n    \
                 (List.cons (Lean.Syntax.Preresolved.decl (Lean.Name.str (Lean.Name.num (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.num (Lean.Name.mkStr2 \"_private\" \"Anneal\") 0) \"_private\") \"Init\") \"System\") \"IO\") 0) \"secret\") List.nil) List.nil)\n\
             def Anneal.ForgeNestedPrivatePreresolvedAuto.f (_h : autoParam (0 = 0) Anneal.ForgeNestedPrivatePreresolvedAuto.f._auto_1) : Nat := 0\n",
            "disallowed reference x",
        ),
        // Forged `.olean` `export` aliases in `theory/` creating `Trusted.*`,
        // reserved-root (`Expected.*`), or forbidden-namespace (`IO.*`) aliases
        // are rejected in Pass-1 `"audit"` (`validateRepoAliases`).
        (
            "Anneal.ForgeExportTrustedAlias",
            "prelude\nimport Init.Core\n\
             namespace Anneal.Foo.Trusted\ndef fake : Nat := 0\nend Anneal.Foo.Trusted\n\
             export Anneal.Foo (Trusted.fake)\n",
            "cannot export alias Trusted.fake in Trusted namespace",
        ),
        (
            "Anneal.ForgeExportReservedAlias",
            "prelude\nimport Init.Core\n\
             namespace Anneal.Foo.Expected\ndef claim : Prop := True\nend Anneal.Foo.Expected\n\
             export Anneal.Foo (Expected.claim)\n",
            "cannot export alias Expected.claim in reserved kernel namespace Expected",
        ),
        (
            "Anneal.ForgeExportIoAlias",
            "prelude\nimport Init.Core\n\
             namespace Anneal.Foo.IO\ndef fake : Nat := 0\nend Anneal.Foo.IO\n\
             export Anneal.Foo (IO.fake)\n",
            "cannot export alias IO.fake in reserved kernel namespace IO",
        ),
        (
            "Anneal.ForgeExportOptParamAlias",
            "prelude\nimport Init.Core\n\
             namespace Anneal.Foo\ndef optParam : Nat := 0\nend Anneal.Foo\n\
             export Anneal.Foo (optParam)\n",
            "disallowed export alias optParam in Anneal.ForgeExportOptParamAlias",
        ),
        (
            "Anneal.ForgeExportMetaTarget",
            "prelude\nimport Init.Core\n\
             namespace Anneal.ForgeExportMetaTarget\nexport Lean (ParserDescr)\n\
             end Anneal.ForgeExportMetaTarget\n",
            "disallowed export target Lean.ParserDescr in Anneal.ForgeExportMetaTarget",
        ),
        // Lean's type system requires `Lean.Syntax` in the binder/type of any
        // direct `_auto_<N>` or partial `autoParam` expression, so these hit
        // the `Lean.Syntax` reference/declaration guards upfront while the
        // `checkRepoExprAutoAndMeta` direct/malformed checks stay as
        // defense in depth for untyped forged `.olean` expressions.
        (
            "Anneal.ForgeDirectAutoRef",
            "prelude\nimport Init.Core\n\
             def Anneal.ForgeDirectAutoRef.h (_x : 0 = 0 := by rfl) : Nat := 0\n\
             def Anneal.ForgeDirectAutoRef.leak : Nat :=\n  \
               (fun (_ : Lean.Syntax) => 0) Anneal.ForgeDirectAutoRef.h._auto_1\n",
            "disallowed reference Lean.Syntax",
        ),
        (
            "Anneal.ForgePartialAuto",
            "prelude\nimport Init.Core\n\
             def Anneal.ForgePartialAuto.bad : Lean.Syntax → Prop := @autoParam (0 = 0)\n",
            "disallowed Lean.Syntax declaration",
        ),
        (
            "Anneal.ForgeNameRef",
            "prelude\nimport Init.Core\n\
             def Anneal.ForgeNameRef.n : Lean.Name := Lean.Name.mkStr1 \"x\"\n",
            "disallowed reference Lean.Name",
        ),
        (
            "Anneal.ForgeMetaParserDescr",
            "prelude\nimport Init.Core\n\
             def Anneal.ForgeMetaParserDescr.pd : Type := Lean.ParserDescr\n",
            "disallowed reference Lean.ParserDescr",
        ),
        (
            "Anneal.ForgeDisallowedAutoTactic",
            "prelude\nimport Init.Core\n\
             def Anneal.ForgeDisallowedAutoTactic.f (_h : autoParam (0 = 0) Lean.Syntax.missing) : Nat := 0\n",
            "disallowed autoParam tactic Lean.Syntax.missing",
        ),
    ] {
        compile_forged_module(&mut checker, &forged_src, &theory_lib, &[], module, body);
        let err = checker
            .inspect(InspectorRequest::Audit {
                trusted: vec!["Trusted".to_string()],
                theory: vec!["Anneal".to_string(), module.to_string()],
                module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
            })
            .unwrap_err();
        assert_eq!((err.code, err.phase.as_str()), (1, "audit"), "{module}: {err}");
        assert!(
            err.message.contains(expected_msg)
                || (expected_msg == "disallowed syntax"
                    && err.message.contains("unsupported syntax kind")),
            "{module}: {err}"
        );
        let adm = checker.admitted_mut().unwrap();
        adm.artifacts.remove(module);
        adm.graph.remove(module);
    }

    compile_forged_module(
        &mut checker,
        &forged_src,
        &theory_lib,
        &[],
        "Trusted.ForgeAutoHelper",
        "prelude\nimport Init.Core\n\
         def Trusted.ForgeAutoHelper.f (_h : 0 = 0 := by rfl) : Nat := 0\n",
    );
    let err_trusted_auto = checker
        .inspect(InspectorRequest::Audit {
            trusted: vec!["Trusted".to_string(), "Trusted.ForgeAutoHelper".to_string()],
            theory: vec!["Anneal".to_string()],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                ("Trusted.ForgeAutoHelper".to_string(), TrustTier::Vetted),
            ]),
        })
        .unwrap_err();
    assert_eq!((err_trusted_auto.code, err_trusted_auto.phase.as_str()), (1, "audit"));
    assert!(err_trusted_auto.message.contains("disallowed autoParam helper"), "{err_trusted_auto}");
    {
        let adm = checker.admitted_mut().unwrap();
        adm.artifacts.remove("Trusted.ForgeAutoHelper");
        adm.graph.remove("Trusted.ForgeAutoHelper");
    }

    // Exercise remaining Pass-1 `validateRepoAliases` branches (`opaque`
    // target outside `Trusted`, role-edge violation, and `unsafe` target)
    // before Pass-2 `CorrespondenceAudit` remounts `checker`'s sandbox roots.
    compile_forged_module(
        &mut checker,
        &forged_src,
        &theory_lib,
        &[],
        "Trusted.WithOpaque",
        "prelude\nimport Init.Core\nopaque Trusted.WithOpaque.opq : Nat := 0\n",
    );
    compile_forged_module(
        &mut checker,
        &forged_src,
        &theory_lib,
        &["Trusted.WithOpaque"],
        "Anneal.ForgeExportOpaqueTarget",
        "prelude\nimport Init.Core\nimport Trusted.WithOpaque\n\
         namespace Anneal.ForgeExportOpaqueTarget\n\
         export Trusted.WithOpaque (opq)\n\
         end Anneal.ForgeExportOpaqueTarget\n",
    );
    let err_opq = checker
        .inspect(InspectorRequest::Audit {
            trusted: vec!["Trusted".to_string(), "Trusted.WithOpaque".to_string()],
            theory: vec!["Anneal".to_string(), "Anneal.ForgeExportOpaqueTarget".to_string()],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                ("Trusted.WithOpaque".to_string(), TrustTier::Vetted),
            ]),
        })
        .unwrap_err();
    assert_eq!((err_opq.code, err_opq.phase.as_str()), (1, "audit"), "{err_opq}");
    assert!(
        err_opq.message.contains("opaque export target Trusted.WithOpaque.opq"),
        "{err_opq}"
    );
    {
        let adm = checker.admitted_mut().unwrap();
        adm.artifacts.remove("Anneal.ForgeExportOpaqueTarget");
        adm.graph.remove("Anneal.ForgeExportOpaqueTarget");
        adm.artifacts.remove("Trusted.WithOpaque");
        adm.graph.remove("Trusted.WithOpaque");
    }

    compile_forged_module(
        &mut checker,
        &forged_src,
        &theory_lib,
        &[],
        "Anneal.HelperTheory",
        "prelude\nimport Init.Core\ndef Anneal.HelperTheory.val : Nat := 0\n",
    );
    for (label, trusted_mod, entry_expr, expected_sub) in [
        (
            "role_edge",
            "Trusted.ForgeAliasEdge",
            "(`Trusted.ForgeAliasEdge.bad, `Anneal.HelperTheory.val)",
            "references Anneal.HelperTheory.val from non-Trusted module Anneal.HelperTheory",
        ),
        (
            "unsafe_target",
            "Trusted.ForgeAliasUnsafe",
            "(`Trusted.ForgeAliasUnsafe.bad, `unsafeCast)",
            "disallowed unsafe/partial/axiom export target unsafeCast",
        ),
    ] {
        compile_forged_module(
            &mut checker,
            &forged_src,
            &theory_lib,
            &[],
            trusted_mod,
            "prelude\nimport Init.Core\ndef Trusted.dummyVal : Nat := 0\n",
        );
        let olean_path = theory_lib.join(format!("{}.olean", trusted_mod.replace('.', "/")));
        let patch_src = forged_src.join(format!("patch_{label}.lean"));
        fs::write(
            &patch_src,
            format!(
                "import Lean\nopen Lean in\ndef main : IO Unit := do\n  \
                   let p := System.FilePath.mk {:?}\n  \
                   let (data, _) ← readModuleData p\n  \
                   let e : Array EnvExtensionEntry := unsafe unsafeCast \
                     (#[{entry_expr}] : Array (Name × Name))\n  \
                   saveModuleData p `{trusted_mod} \
                     {{ data with entries := data.entries.push (Lean.aliasExtension.name, e) }}\n",
                olean_path.to_string_lossy()
            ),
        )
        .unwrap();
        checker
            .process(
                label,
                &["-j1".into(), "-M2048".into(), "--run".into(), patch_src.to_string_lossy().into()],
            )
            .unwrap();
        let err = checker
            .inspect(InspectorRequest::Audit {
                trusted: vec!["Trusted".to_string(), trusted_mod.to_string()],
                theory: vec!["Anneal".to_string(), "Anneal.HelperTheory".to_string()],
                module_tiers: BTreeMap::from([
                    ("Trusted".to_string(), TrustTier::Vetted),
                    (trusted_mod.to_string(), TrustTier::Vetted),
                ]),
            })
            .unwrap_err();
        assert_eq!((err.code, err.phase.as_str()), (1, "audit"), "{label}: {err}");
        assert!(err.message.contains(expected_sub), "{label}: {err}");
        let adm = checker.admitted_mut().unwrap();
        adm.artifacts.remove(trusted_mod);
        adm.graph.remove(trusted_mod);
    }
    {
        let adm = checker.admitted_mut().unwrap();
        adm.artifacts.remove("Anneal.HelperTheory");
        adm.graph.remove("Anneal.HelperTheory");
    }

    // 4. Pass-2 `"correspondence-preflight"` and `"correspondence-audit"`
    //    coverage for the same `Init.Meta*` / `autoParam` / `Lean.Syntax` /
    //    alias isolation checks.
    let corr_pf_dir = stage.join("src/corr-auto-pf");
    fs::create_dir_all(&corr_pf_dir).unwrap();
    let trusted_base_src = checker.modules()["Trusted"].clone();
    for (label, body, expected_msg) in [
        (
            "corr_pf_init_meta",
            "prelude\nimport Init.Core\nimport Init.Meta.Defs\ndef Anneal.CorrMeta.x : Nat := 0\n",
            "disallowed sysroot import Init.Meta.Defs",
        ),
        (
            "corr_pf_syntax_node",
            "prelude\nimport Init.Core\ndef Anneal.CorrStx.x := Lean.Syntax.node\n",
            "disallowed reference Lean.Syntax.node",
        ),
        (
            "corr_pf_auto_param",
            "prelude\nimport Init.Core\ndef Anneal.CorrAp.x (h : autoParam (0 = 0) y) : Nat := 0\n",
            "disallowed reference autoParam",
        ),
    ] {
        let p = corr_pf_dir.join(format!("{label}.lean"));
        fs::write(&p, body).unwrap();
        let err = checker
            .inspect(InspectorRequest::CorrespondencePreflight {
                search_path: vec![theory_lib.clone()],
                trusted: vec!["Trusted".to_string()],
                theory: Vec::new(),
                vendor_miri: Vec::new(),
                base_trusted_sources: vec![("Trusted".to_string(), trusted_base_src.clone())],
                sources: vec![(format!("Anneal.{label}"), p)],
            })
            .unwrap_err();
        assert_eq!(
            (err.code, err.phase.as_str()),
            (1, "correspondence-preflight"),
            "{label}: {err}"
        );
        assert!(err.message.contains(expected_msg), "{label}: {err}");
    }

    let corr_mod = "Anneal.CorrForgedObfAuto";
    compile_forged_module(
        &mut checker,
        &forged_src,
        &theory_lib,
        &[],
        corr_mod,
        "prelude\nimport Init.Core\n\
         def Anneal.CorrForgedObfAuto.f._auto_1 : Lean.Syntax :=\n  \
           let a := Lean.mkAtom \"x\"\n  a\n\
         def Anneal.CorrForgedObfAuto.f (_h : autoParam (0 = 0) Anneal.CorrForgedObfAuto.f._auto_1) : Nat := 0\n",
    );
    let err_ca = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: vec![theory_lib.clone()],
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: vec![corr_mod.to_string()],
            vendor_miri: Vec::new(),
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert_eq!((err_ca.code, err_ca.phase.as_str()), (1, "correspondence-audit"), "{err_ca}");
    assert!(err_ca.message.contains("disallowed non-literal autoParam tactic"), "{err_ca}");
    {
        let adm = checker.admitted_mut().unwrap();
        adm.artifacts.remove(corr_mod);
        adm.graph.remove(corr_mod);
    }

    let corr_alias_mod = "Anneal.CorrForgedTrustedAlias";
    compile_forged_module(
        &mut checker,
        &forged_src,
        &theory_lib,
        &[],
        corr_alias_mod,
        "prelude\nimport Init.Core\n\
         namespace Anneal.Foo.Trusted\ndef fake : Nat := 0\nend Anneal.Foo.Trusted\n\
         export Anneal.Foo (Trusted.fake)\n",
    );
    let err_ca_alias = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: vec![theory_lib.clone()],
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: vec![corr_alias_mod.to_string()],
            vendor_miri: Vec::new(),
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert_eq!(
        (err_ca_alias.code, err_ca_alias.phase.as_str()),
        (1, "correspondence-audit"),
        "{err_ca_alias}"
    );
    assert!(
        err_ca_alias.message.contains("cannot export alias Trusted.fake in Trusted namespace"),
        "{err_ca_alias}"
    );
}
