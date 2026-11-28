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

#[path = "pass1_preflight/forbidden_syntax.rs"]
mod forbidden_syntax;
#[path = "pass1_preflight/realized_theorems.rs"]
mod realized_theorems;
