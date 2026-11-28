// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Pass 1 preflight rejection of forbidden syntax, attributes, and
//! side-effecting declarations before Lean runs.

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
