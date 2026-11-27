// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Trust tiers, namespace hygiene, reserved theory roots, universe
//! polymorphism, and the theory umbrella and manifest.

use super::*;

/// Verifies module-level trust-tier non-contamination (both syntactic
/// `"preflight"` and compiled `.olean` `"audit"`) and `Trusted` namespace
/// hygiene:
/// - A `vetted` module importing a `candidate:<feature>` module—whether or not
///   it references any candidate constant—is rejected during `"preflight"`
///   before Lean compiles the file.
/// - Bypassing `"preflight"` to present a compiled `.olean` with a
///   declaration-free `vetted -> candidate` import is still rejected by
///   `RepoOrigin.importViolation?` in `"audit"`, and a forged `.olean` whose
///   header omits the import while referencing a candidate constant is still
///   rejected by `RepoOrigin.edgeViolation?`.
/// - A `vetted` umbrella importing only `vetted` submodules, with a
///   `candidate:<feature>` module importing a `vetted` submodule and
///   `theory/Anneal.lean` importing both directly, passes `"audit"`.
/// - A `theory/Anneal.lean` module attempting to declare a constant inside the
///   reserved `Trusted` namespace (or an `opaque` constant) is rejected during
///   `"audit"`.
#[test]
fn enforces_module_level_trust_tiers_and_namespace_hygiene() {
    // 1a. A vetted module (`Trusted.lean`) importing and referencing a
    // candidate constant in `Trusted/Cand.lean` is rejected during
    // `"preflight"` before compilation starts.
    let mut f_contam = TempFixture::new(Some(&format!(
        "{HEADER}import Trusted.Cand\nnamespace Trusted\ndef badVetted : Prop := candHelper\nend Trusted\n"
    )));
    fs::create_dir_all(f_contam.root.join("trusted/lean/Trusted")).unwrap();
    fs::write(
        f_contam.root.join("trusted/lean/Trusted/Cand.lean"),
        b"-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.NotationExtra\nnamespace Trusted\ndef candHelper : Prop := True\nend Trusted\n",
    )
    .unwrap();
    let err_contam = f_contam.check_expected(Some(1), Some("preflight"), Some(false)).unwrap_err();
    assert!(
        err_contam.message.contains(
            "vetted module Trusted cannot import candidate:mir_semantics module Trusted.Cand"
        ),
        "unexpected error: {err_contam}"
    );

    // 1b. Even a declaration-free `vetted` umbrella `Trusted.lean` importing a
    // `candidate:<feature>` module is rejected during `"preflight"` before
    // compilation starts.
    let mut f_decl_free = TempFixture::new(Some(&format!("{HEADER}import Trusted.Cand\n")));
    fs::create_dir_all(f_decl_free.root.join("trusted/lean/Trusted")).unwrap();
    fs::write(
        f_decl_free.root.join("trusted/lean/Trusted/Cand.lean"),
        b"-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.NotationExtra\nnamespace Trusted\ndef candHelper : Prop := True\nend Trusted\n",
    )
    .unwrap();
    let err_decl_free =
        f_decl_free.check_expected(Some(1), Some("preflight"), Some(false)).unwrap_err();
    assert!(
        err_decl_free.message.contains(
            "vetted module Trusted cannot import candidate:mir_semantics module Trusted.Cand"
        ),
        "unexpected error: {err_decl_free}"
    );

    // 1c. Direct Lean `"preflight"` sensitivity check (independent of Rust's
    // `check_preflight_tier_imports` in `preflight_and_order_modules`): calling
    // `InspectorRequest::Preflight` directly rejects declaration-free
    // `vetted -> candidate` and `vetted -> theory` imports inside
    // `TrustedBoundary.lean`'s `checkPreflightTierImports`.
    let mut checker_lean_pf = f_decl_free.checker();
    checker_lean_pf.tool_admission().unwrap();
    let lean_pf_trusted = checker_lean_pf.stage().join("pf-trusted.lean");
    let lean_pf_cand = checker_lean_pf.stage().join("pf-cand.lean");
    fs::write(&lean_pf_trusted, format!("{HEADER}import Trusted.Cand\n")).unwrap();
    fs::write(
        &lean_pf_cand,
        b"-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.NotationExtra\n",
    )
    .unwrap();
    let err_lean_pf = checker_lean_pf
        .inspect(InspectorRequest::Preflight {
            sources: vec![
                ("Trusted".to_string(), lean_pf_trusted),
                ("Trusted.Cand".to_string(), lean_pf_cand),
            ],
            base_trusted_sources: Vec::new(),
        })
        .unwrap_err();
    assert_eq!(err_lean_pf.code, 1, "unexpected code: {err_lean_pf}");
    assert_eq!(err_lean_pf.phase, "preflight", "unexpected phase: {err_lean_pf}");
    assert!(
        err_lean_pf.message.contains(
            "vetted module Trusted cannot import candidate:mir_semantics module Trusted.Cand"
        ),
        "unexpected Lean preflight error: {err_lean_pf}"
    );

    let lean_pf_trusted_theory = checker_lean_pf.stage().join("pf-trusted-theory.lean");
    let lean_pf_theory = checker_lean_pf.stage().join("pf-theory.lean");
    fs::write(&lean_pf_trusted_theory, format!("{HEADER}import Anneal.Helper\n")).unwrap();
    fs::write(&lean_pf_theory, b"prelude\nimport Init.NotationExtra\n").unwrap();
    let err_lean_pf_theory = checker_lean_pf
        .inspect(InspectorRequest::Preflight {
            sources: vec![
                ("Trusted".to_string(), lean_pf_trusted_theory),
                ("Anneal.Helper".to_string(), lean_pf_theory),
            ],
            base_trusted_sources: Vec::new(),
        })
        .unwrap_err();
    assert_eq!(err_lean_pf_theory.code, 1, "unexpected theory code: {err_lean_pf_theory}");
    assert_eq!(err_lean_pf_theory.phase, "preflight", "unexpected phase: {err_lean_pf_theory}");
    assert!(
        err_lean_pf_theory
            .message
            .contains("vetted module Trusted cannot import non-foundation module Anneal.Helper"),
        "unexpected Lean preflight theory error: {err_lean_pf_theory}"
    );

    // 1d. Authenticating staged `base_trusted_sources` (`"baseSources"`) in
    // `InspectorRequest::Preflight` accepts a `vetted` correspondence source
    // importing a `vetted` on-disk base module, rejects importing an on-disk
    // `candidate` base module, rejects non-`Trusted`, foundation-named,
    // malformed-syntax, or duplicate `base_trusted_sources` entries, and
    // rejects duplicate or base-colliding `sources`.
    let lean_pf_base_vetted = checker_lean_pf.stage().join("pf-base-vetted.lean");
    let lean_pf_base_cand = checker_lean_pf.stage().join("pf-base-cand.lean");
    let lean_pf_base_theory = checker_lean_pf.stage().join("pf-base-theory.lean");
    let lean_pf_base_tactic = checker_lean_pf.stage().join("pf-base-tactic.lean");
    fs::write(&lean_pf_base_vetted, HEADER.as_bytes()).unwrap();
    fs::write(
        &lean_pf_base_cand,
        b"-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.NotationExtra\n",
    )
    .unwrap();
    fs::write(&lean_pf_base_theory, b"prelude\nimport Init.NotationExtra\n").unwrap();
    fs::write(&lean_pf_base_tactic, format!("{HEADER}theorem bad : Eq 0 0 := by rfl\n")).unwrap();
    let pf_base_sources = vec![
        ("Trusted.Base".to_string(), lean_pf_base_vetted.clone()),
        ("Trusted.Cand".to_string(), lean_pf_base_cand.clone()),
    ];
    let lean_pf_corr_ok = checker_lean_pf.stage().join("pf-corr-ok.lean");
    fs::write(&lean_pf_corr_ok, format!("{HEADER}import Trusted.Base\n")).unwrap();
    checker_lean_pf
        .inspect(InspectorRequest::Preflight {
            sources: vec![("Trusted.Correspondence".to_string(), lean_pf_corr_ok.clone())],
            base_trusted_sources: pf_base_sources.clone(),
        })
        .expect("vetted source importing vetted base module in baseSources must pass");

    let lean_pf_corr_bad = checker_lean_pf.stage().join("pf-corr-bad.lean");
    fs::write(&lean_pf_corr_bad, format!("{HEADER}import Trusted.Cand\n")).unwrap();
    let err_pf_base_cand = checker_lean_pf
        .inspect(InspectorRequest::Preflight {
            sources: vec![("Trusted.Correspondence".to_string(), lean_pf_corr_bad)],
            base_trusted_sources: pf_base_sources.clone(),
        })
        .unwrap_err();
    assert_eq!(err_pf_base_cand.code, 1, "unexpected code: {err_pf_base_cand}");
    assert_eq!(err_pf_base_cand.phase, "preflight");
    assert!(
        err_pf_base_cand.message.contains(
            "vetted module Trusted.Correspondence cannot import candidate:mir_semantics module Trusted.Cand"
        ),
        "unexpected base-candidate error: {err_pf_base_cand}"
    );

    let err_pf_non_trusted_base = checker_lean_pf
        .inspect(InspectorRequest::Preflight {
            sources: vec![("Trusted.Correspondence".to_string(), lean_pf_corr_ok.clone())],
            base_trusted_sources: vec![("Anneal.Helper".to_string(), lean_pf_base_theory)],
        })
        .unwrap_err();
    assert_eq!(err_pf_non_trusted_base.code, 1);
    assert_eq!(err_pf_non_trusted_base.phase, "preflight");
    assert!(
        err_pf_non_trusted_base.message.contains("non-Trusted base preflight source Anneal.Helper"),
        "unexpected non-Trusted base source error: {err_pf_non_trusted_base}"
    );

    let err_pf_foundation_base = checker_lean_pf
        .inspect(InspectorRequest::Preflight {
            sources: vec![("Trusted.Correspondence".to_string(), lean_pf_corr_ok.clone())],
            base_trusted_sources: vec![("Init.Core".to_string(), lean_pf_base_vetted.clone())],
        })
        .unwrap_err();
    assert_eq!(err_pf_foundation_base.code, 1);
    assert_eq!(err_pf_foundation_base.phase, "preflight");
    assert!(
        err_pf_foundation_base.message.contains("non-Trusted base preflight source Init.Core"),
        "unexpected foundation base source error: {err_pf_foundation_base}"
    );

    let err_pf_dup_base = checker_lean_pf
        .inspect(InspectorRequest::Preflight {
            sources: vec![("Trusted.Correspondence".to_string(), lean_pf_corr_ok.clone())],
            base_trusted_sources: vec![
                ("Trusted.Base".to_string(), lean_pf_base_cand),
                ("Trusted.Base".to_string(), lean_pf_base_vetted),
            ],
        })
        .unwrap_err();
    assert_eq!(err_pf_dup_base.code, 1);
    assert_eq!(err_pf_dup_base.phase, "preflight");
    assert!(
        err_pf_dup_base.message.contains("duplicate base preflight source module Trusted.Base"),
        "unexpected duplicate base source error: {err_pf_dup_base}"
    );

    let err_pf_bad_base_syntax = checker_lean_pf
        .inspect(InspectorRequest::Preflight {
            sources: vec![("Trusted.Correspondence".to_string(), lean_pf_corr_ok)],
            base_trusted_sources: vec![("Trusted.Base".to_string(), lean_pf_base_tactic)],
        })
        .unwrap_err();
    assert_eq!(err_pf_bad_base_syntax.code, 1);
    assert_eq!(err_pf_bad_base_syntax.phase, "preflight");

    let lean_pf_override = checker_lean_pf.stage().join("pf-override.lean");
    fs::write(&lean_pf_override, HEADER.as_bytes()).unwrap();
    let lean_pf_user = checker_lean_pf.stage().join("pf-user.lean");
    fs::write(&lean_pf_user, format!("{HEADER}import Trusted.Cand\n")).unwrap();
    let err_pf_collision = checker_lean_pf
        .inspect(InspectorRequest::Preflight {
            sources: vec![
                ("Trusted.Cand".to_string(), lean_pf_override),
                ("Trusted.Correspondence".to_string(), lean_pf_user.clone()),
            ],
            base_trusted_sources: pf_base_sources,
        })
        .unwrap_err();
    assert_eq!(err_pf_collision.code, 1, "unexpected collision code: {err_pf_collision}");
    assert_eq!(err_pf_collision.phase, "preflight");
    assert!(
        err_pf_collision
            .message
            .contains("preflight source module Trusted.Cand collides with base module"),
        "unexpected base collision error: {err_pf_collision}"
    );

    let lean_pf_dup_cand = checker_lean_pf.stage().join("pf-dup-cand.lean");
    let lean_pf_dup_vetted = checker_lean_pf.stage().join("pf-dup-vetted.lean");
    let lean_pf_dup_caller = checker_lean_pf.stage().join("pf-dup-caller.lean");
    fs::write(
        &lean_pf_dup_cand,
        b"-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.NotationExtra\n",
    )
    .unwrap();
    fs::write(&lean_pf_dup_vetted, HEADER.as_bytes()).unwrap();
    fs::write(&lean_pf_dup_caller, format!("{HEADER}import Trusted.Dup\n")).unwrap();
    let err_pf_dup = checker_lean_pf
        .inspect(InspectorRequest::Preflight {
            sources: vec![
                ("Trusted.Dup".to_string(), lean_pf_dup_cand),
                ("Trusted.Dup".to_string(), lean_pf_dup_vetted),
                ("Trusted.DupCaller".to_string(), lean_pf_dup_caller),
            ],
            base_trusted_sources: Vec::new(),
        })
        .unwrap_err();
    assert_eq!(err_pf_dup.code, 1, "unexpected duplicate code: {err_pf_dup}");
    assert_eq!(err_pf_dup.phase, "preflight");
    assert!(
        err_pf_dup.message.contains("duplicate preflight source module Trusted.Dup"),
        "unexpected duplicate error: {err_pf_dup}"
    );

    // 2. `Trusted.lean` (`vetted`) importing only `Trusted.VettedSub`
    // (`vetted`), `Trusted.Cand` (`candidate:mir_semantics`) importing
    // `Trusted.VettedSub`, and `theory/Anneal.lean` importing `Trusted` and
    // `Trusted.Cand` directly passes cleanly.
    let mut f_ok = TempFixture::new(Some(&format!("{HEADER}import Trusted.VettedSub\n")));
    fs::create_dir_all(f_ok.root.join("trusted/lean/Trusted")).unwrap();
    fs::write(
        f_ok.root.join("trusted/lean/Trusted/VettedSub.lean"),
        b"-- anneal-trust-tier: vetted\nprelude\nimport Init.NotationExtra\nnamespace Trusted\ndef vettedProp : Prop := True\nend Trusted\n",
    )
    .unwrap();
    fs::write(
        f_ok.root.join("trusted/lean/Trusted/Cand.lean"),
        b"-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.NotationExtra\nimport Trusted.VettedSub\nnamespace Trusted\ndef candProp : Prop := vettedProp\nend Trusted\n",
    )
    .unwrap();
    fs::create_dir_all(f_ok.root.join("theory")).unwrap();
    fs::write(
        f_ok.root.join("theory/Anneal.lean"),
        b"prelude\nimport Trusted\nimport Trusted.Cand\nnamespace Anneal\ntheorem uses_both : Trusted.candProp := True.intro\nend Anneal\n",
    )
    .unwrap();
    let mut checker_ok = f_ok.checker();
    checker_ok.set_require_mir_wp(false);
    let rep_ok = checker_ok.run().unwrap();
    assert_eq!(rep_ok.get("replay"), Some(&json!(true)));

    // 2b. Defense in depth in `"audit"`: bypassing `"preflight"` with a
    // compiled declaration-free `vetted` module whose `.olean` header imports
    // `Trusted.Cand` is rejected by `RepoOrigin.importViolation?`.
    let stage = checker_ok.stage().to_path_buf();
    let trusted_lib = stage.join("lib");
    compile_forged_module(
        &mut checker_ok,
        &stage.join("src/forged-tier"),
        &trusted_lib,
        &["Trusted.Cand"],
        "Trusted.VettedImportsCand",
        "prelude\nimport Init.Core\nimport Trusted.Cand\n",
    );
    let err_audit_imp = checker_ok
        .inspect(InspectorRequest::Audit {
            trusted: vec![
                "Trusted".to_string(),
                "Trusted.VettedSub".to_string(),
                "Trusted.Cand".to_string(),
                "Trusted.VettedImportsCand".to_string(),
            ],
            theory: vec!["Anneal".to_string()],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                ("Trusted.VettedSub".to_string(), TrustTier::Vetted),
                ("Trusted.Cand".to_string(), TrustTier::Candidate(CandidateFeature::MirSemantics)),
                ("Trusted.VettedImportsCand".to_string(), TrustTier::Vetted),
            ]),
        })
        .unwrap_err();
    assert_eq!(err_audit_imp.code, 1, "unexpected code: {err_audit_imp}");
    assert_eq!(err_audit_imp.phase, "audit", "unexpected phase: {err_audit_imp}");
    assert!(
        err_audit_imp.message.contains(
            "vetted module Trusted.VettedImportsCand cannot import candidate:mir_semantics module Trusted.Cand"
        ),
        "unexpected audit import error: {err_audit_imp}"
    );

    // 2c. Defense in depth in `"audit"`: a forged `vetted` `.olean` whose
    // header imports only `Init.Core` (bypassing `RepoOrigin.importViolation?`)
    // while referencing `Trusted.candProp` is still rejected by
    // `RepoOrigin.edgeViolation?`.
    let forged_edge_mod = "Trusted.ForgedVettedEdge";
    let forged_edge_out = trusted_lib.join("Trusted/ForgedVettedEdge.olean");
    run_lean_script(
        &mut checker_ok,
        "gen-forged-vetted-edge",
        &stage.join("gen_forged_vetted_edge.lean"),
        &format!(
            "import Lean.Environment\n\
             open Lean\n\
             def main : IO Unit := do\n\
               let ci : ConstantInfo := .defnInfo {{\n\
                 name := `Trusted.ForgedVettedEdge.x\n\
                 levelParams := []\n\
                 type := .sort .zero\n\
                 value := .const `Trusted.candProp []\n\
                 hints := .abbrev\n\
                 safety := .safe\n\
                 all := [`Trusted.ForgedVettedEdge.x]\n\
               }}\n\
               let md : ModuleData := {{\n\
                 isModule := false\n\
                 imports := #[{{ module := `Init.Core }}]\n\
                 constNames := #[`Trusted.ForgedVettedEdge.x]\n\
                 constants := #[ci]\n\
                 extraConstNames := #[]\n\
                 entries := #[]\n\
               }}\n\
               saveModuleData (System.FilePath.mk {:?}) `Trusted.ForgedVettedEdge md\n",
            forged_edge_out.to_string_lossy()
        ),
    );
    let core_edge = vec![ImportEdge {
        module: "Init.Core".to_string(),
        import_all: false,
        is_exported: true,
        is_meta: false,
    }];
    let forged_arts = ModuleArtifacts::from_available(
        &BTreeMap::from([("olean", forged_edge_out.to_string_lossy().into_owned())]),
        "test",
        String::new,
    )
    .unwrap();
    {
        let adm = checker_ok.admitted_mut().unwrap();
        adm.graph.remove("Trusted.VettedImportsCand");
        adm.artifacts.remove("Trusted.VettedImportsCand");
        adm.graph.insert(forged_edge_mod.to_string(), core_edge);
        adm.artifacts.insert(forged_edge_mod.to_string(), forged_arts);
    }
    let err_audit_edge = checker_ok
        .inspect(InspectorRequest::Audit {
            trusted: vec![
                "Trusted".to_string(),
                "Trusted.VettedSub".to_string(),
                "Trusted.Cand".to_string(),
                forged_edge_mod.to_string(),
            ],
            theory: vec!["Anneal".to_string()],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                ("Trusted.VettedSub".to_string(), TrustTier::Vetted),
                ("Trusted.Cand".to_string(), TrustTier::Candidate(CandidateFeature::MirSemantics)),
                (forged_edge_mod.to_string(), TrustTier::Vetted),
            ]),
        })
        .unwrap_err();
    assert_eq!(err_audit_edge.code, 1, "unexpected code: {err_audit_edge}");
    assert_eq!(err_audit_edge.phase, "audit", "unexpected phase: {err_audit_edge}");
    assert!(
        err_audit_edge.message.contains(
            "vetted constant Trusted.ForgedVettedEdge.x references candidate:mir_semantics constant Trusted.candProp"
        ),
        "unexpected audit edge error: {err_audit_edge}"
    );

    // 3. `theory/Anneal.lean` attempting to declare a constant inside the
    // reserved `Trusted` namespace is rejected during `"audit"`.
    fs::write(
        f_ok.root.join("theory/Anneal.lean"),
        b"prelude\nimport Trusted\nnamespace Trusted\ndef Spoof : Nat := 0\nend Trusted\n",
    )
    .unwrap();
    let err_spoof = f_ok.check_expected(Some(1), Some("audit"), Some(true)).unwrap_err();
    assert!(
        err_spoof.message.contains(
            "non-Trusted module Anneal cannot declare constant Trusted.Spoof in Trusted namespace"
        ),
        "unexpected error: {err_spoof}"
    );

    // 4. `theory/Anneal.lean` attempting to declare an `opaque` constant is
    // rejected during `"audit"`.
    fs::write(
        f_ok.root.join("theory/Anneal.lean"),
        b"prelude\nimport Trusted\nnamespace Anneal\nopaque badOpaque : Nat := 0\nend Anneal\n",
    )
    .unwrap();
    let err_opaque = f_ok.check_expected(Some(1), Some("audit"), Some(true)).unwrap_err();
    assert!(
        err_opaque.message.contains(
            "opaque declaration Anneal.badOpaque in Anneal is not allowed outside Trusted"
        ),
        "unexpected error: {err_opaque}"
    );
}

#[test]
fn rejects_reserved_kernel_roots_and_user_splitter_children_in_theory() {
    let mut fix =
        TempFixture::new(Some("-- anneal-trust-tier: vetted\nprelude\nimport Init.Prelude\n"));
    fs::create_dir_all(fix.root.join("trusted/lean/Trusted")).unwrap();
    fs::write(
        fix.root.join("trusted/lean/Trusted/MirAst.lean"),
        b"-- anneal-trust-tier: candidate:mir_ast\n\
          prelude\nimport Init.Prelude\n\
          namespace Trusted.MirAst\n\
          structure Place where\n  localId : Nat\n\
          end Trusted.MirAst\n",
    )
    .unwrap();
    fs::create_dir_all(fix.root.join("theory")).unwrap();

    // (a) `def Nat.gcd`, `theorem Nat.gcd` (kernel-accelerated),
    // `theorem Nat.fakeThm` (non-accelerated `.thmInfo` in `Nat`),
    // `private def Nat.privFake`, and `def Int8.fake` in `theory/` must all be
    // rejected by `validateRepoConstant` with exit code 1.
    for (theory_src, expected_msg) in [
        (
            "prelude\nimport Trusted\nnamespace Nat\ndef gcd : Nat := 0\nend Nat\n",
            "repository module Anneal cannot declare constant Nat.gcd in reserved kernel namespace Nat",
        ),
        (
            "prelude\nimport Trusted\nnamespace Nat\ntheorem gcd : True := True.intro\nend Nat\n",
            "repository module Anneal cannot declare constant Nat.gcd in reserved kernel namespace Nat",
        ),
        (
            "prelude\nimport Trusted\nnamespace Nat\ntheorem fakeThm : True := True.intro\nend Nat\n",
            "repository module Anneal cannot declare constant Nat.fakeThm in reserved kernel namespace Nat",
        ),
        (
            "prelude\nimport Trusted\nnamespace Nat\nprivate def privFake : Nat := 0\nend Nat\n",
            "in reserved kernel namespace Nat",
        ),
        (
            "prelude\nimport Trusted\nnamespace Int8\ndef fake : Nat := 0\nend Int8\n",
            "repository module Anneal cannot declare constant Int8.fake in reserved kernel namespace Int8",
        ),
        // (b) User-authored declaration beneath `<CompoundConst>.splitter`
        // (`Trusted.MirAst.Place` is an already-imported compound `Trusted`
        // constant) must be rejected by `isGeneratedSplitterSubtree`.
        (
            "prelude\nimport Trusted\nimport Trusted.MirAst\n\
             namespace Trusted.MirAst.Place.splitter\n\
             private def evil : Nat := 0\n\
             end Trusted.MirAst.Place.splitter\n",
            "non-Trusted module Anneal cannot declare constant",
        ),
    ] {
        fs::write(fix.root.join("theory/Anneal.lean"), theory_src).unwrap();
        let err = fix.check_expected(Some(1), Some("audit"), Some(true)).unwrap_err();
        assert!(
            err.message.starts_with("policy:") && err.message.contains(expected_msg),
            "expected `{expected_msg}`, got: {err}"
        );
    }

    // `theorem Nat.land` collides with `foundation-lock.json`'s
    // `Init.Data.Nat.Bitwise.Basic` and is rejected even earlier by
    // `importModules`.
    fs::write(
        fix.root.join("theory/Anneal.lean"),
        "prelude\nimport Trusted\nnamespace Nat\ntheorem land : True := True.intro\nend Nat\n",
    )
    .unwrap();
    let err_land = fix.check_expected(Some(2), Some("audit"), Some(true)).unwrap_err();
    assert!(
        err_land.message.contains("already contains 'Nat.land'"),
        "expected Nat.land collision rejection, got: {err_land}"
    );
}

/// Verifies `requireClaimProof` universe-parameter rejection in both Pass 1
/// (`"audit"`) and Pass 2 (`"correspondence-audit"`): neither a required
/// `*Claim` definition nor its proof theorem may declare universe parameters.
#[test]
fn rejects_universe_polymorphic_claims_and_proofs() {
    // 1. Pass 1 (`Audit`): universe-polymorphic claim and theorem rejection.
    let fix = TempFixture::new(None);
    let mut checker = fix.checker();
    checker.set_require_mir_wp(false);
    checker.run().unwrap();
    checker.set_require_mir_wp(true);

    let stage = checker.stage().to_path_buf();
    let src = stage.join("src/univ-poly");
    let lib = stage.join("lib");
    let theory_lib = stage.join("theory-lib");

    compile_forged_module(
        &mut checker,
        &src,
        &lib,
        &[],
        "Trusted.MirAst",
        "prelude\nimport Init.Core\nnamespace Trusted.MirAst\ndef x : Nat := 0\nend Trusted.MirAst\n",
    );
    compile_forged_module(
        &mut checker,
        &src,
        &theory_lib,
        &[],
        "Anneal.MirWp.Canaries",
        "prelude\nimport Init.Core\n",
    );
    let run_pass1_audit = |chk: &mut Checker| {
        chk.inspect(InspectorRequest::Audit {
            trusted: vec![
                "Trusted".to_string(),
                "Trusted.MirAst".to_string(),
                "Trusted.MirSemantics".to_string(),
            ],
            theory: vec![
                "Anneal.MirWp".to_string(),
                "Anneal.MirWp.Canaries".to_string(),
            ],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                ("Trusted.MirAst".to_string(), TrustTier::Candidate(CandidateFeature::MirAst)),
                (
                    "Trusted.MirSemantics".to_string(),
                    TrustTier::Candidate(CandidateFeature::MirSemantics),
                ),
            ]),
        })
    };

    // 1a. Universe-polymorphic Pass 1 claim.
    compile_forged_module(
        &mut checker,
        &src,
        &lib,
        &["Trusted.MirAst"],
        "Trusted.MirSemantics",
        "prelude\nimport Init.Core\nimport Trusted.MirAst\n\
         namespace Trusted.MirSemantics\n\
         def SatisfiesPost : Prop := True\n\
         def Diverges : Prop := True\n\
         def Behavior : Prop := True\n\
         def WpSoundnessClaim.{u} (_f : Nat) : Prop :=\n\
           (fun (_ : PUnit.{u + 1}) => And SatisfiesPost (And Diverges Behavior)) PUnit.unit\n\
         end Trusted.MirSemantics\n",
    );
    compile_forged_module(
        &mut checker,
        &src,
        &theory_lib,
        &["Trusted.MirSemantics"],
        "Anneal.MirWp",
        "prelude\nimport Init.Core\nimport Trusted.MirSemantics\n\
         namespace Anneal.MirWp\n\
         def wpProg : Nat := 0\n\
         theorem wellFormed_and_spec_of_wp : \
           Trusted.MirSemantics.WpSoundnessClaim.{0} wpProg := \
           And.intro True.intro (And.intro True.intro True.intro)\n\
         end Anneal.MirWp\n",
    );
    let err_claim_u = run_pass1_audit(&mut checker).unwrap_err();
    assert_eq!(err_claim_u.code, 1, "unexpected code: {err_claim_u}");
    assert_eq!(err_claim_u.phase, "audit");
    assert!(
        err_claim_u.message.contains(
            "claim Trusted.MirSemantics.WpSoundnessClaim must have no universe parameters"
        ),
        "unexpected Pass 1 poly-claim error: {err_claim_u}"
    );

    // 1b. Universe-polymorphic Pass 1 proof theorem.
    compile_forged_module(
        &mut checker,
        &src,
        &lib,
        &["Trusted.MirAst"],
        "Trusted.MirSemantics",
        "prelude\nimport Init.Core\nimport Trusted.MirAst\n\
         namespace Trusted.MirSemantics\n\
         def SatisfiesPost : Prop := True\n\
         def Diverges : Prop := True\n\
         def Behavior : Prop := True\n\
         def WpSoundnessClaim (_f : Nat) : Prop := And SatisfiesPost (And Diverges Behavior)\n\
         end Trusted.MirSemantics\n",
    );
    compile_forged_module(
        &mut checker,
        &src,
        &theory_lib,
        &["Trusted.MirSemantics"],
        "Anneal.MirWp",
        "prelude\nimport Init.Core\nimport Trusted.MirSemantics\n\
         namespace Anneal.MirWp\n\
         def wpProg : Nat := 0\n\
         theorem wellFormed_and_spec_of_wp.{u} :\n\
           (fun (_ : PUnit.{u + 1}) => Trusted.MirSemantics.WpSoundnessClaim wpProg) PUnit.unit :=\n\
           And.intro True.intro (And.intro True.intro True.intro)\n\
         end Anneal.MirWp\n",
    );
    let err_thm_u = run_pass1_audit(&mut checker).unwrap_err();
    assert_eq!(err_thm_u.code, 1, "unexpected code: {err_thm_u}");
    assert_eq!(err_thm_u.phase, "audit");
    assert!(
        err_thm_u.message.contains(
            "theorem Anneal.MirWp.wellFormed_and_spec_of_wp must have no universe parameters"
        ),
        "unexpected Pass 1 poly-theorem error: {err_thm_u}"
    );

    // 2. Pass 2 (`CorrespondenceAudit`): universe-polymorphic claim and
    // theorem rejection.
    let vendor_lib = stage.join("univ-vendor-lib");
    let corr_lib = stage.join("univ-corr-lib");
    compile_forged_module(
        &mut checker,
        &src,
        &vendor_lib,
        &[],
        "Miri.UnivStub",
        "prelude\nimport Init.Core\n\
         namespace Miri.Interpreter.ExecutionMachine\n\
         def step : Nat := 0\n\
         def AllowedStep : Nat := 0\n\
         def withValidation : Nat := 0\n\
         def stepHooks : Nat := 0\n\
         def rvalueHooks : Nat := 0\n\
         def operandHooks : Nat := 0\n\
         def projectionHooks : Nat := 0\n\
         def discriminantHooks : Nat := 0\n\
         def scalarHooks : Nat := 0\n\
         end Miri.Interpreter.ExecutionMachine\n\
         namespace Miri.Interpreter.Step\n\
         def step : Nat := 0\n\
         def evalStatement : Nat := 0\n\
         end Miri.Interpreter.Step\n\
         namespace Miri.Interpreter.ControlFlow\n\
         def goToBlock : Nat := 0\n\
         def evalTerminator : Nat := 0\n\
         def returnFromCurrentFrame : Nat := 0\n\
         end Miri.Interpreter.ControlFlow\n\
         namespace Miri.Interpreter.ExecutionControl\n\
         def hooks : Nat := 0\n\
         end Miri.Interpreter.ExecutionControl\n\
         namespace Miri.Interpreter.MachineHooks\n\
         def storageLiveDyn : Nat := 0\n\
         def storageDead : Nat := 0\n\
         end Miri.Interpreter.MachineHooks\n\
         namespace Miri.Interpreter.OperandMachine\n\
         def evalOperand : Nat := 0\n\
         def evalPlaceToOp : Nat := 0\n\
         end Miri.Interpreter.OperandMachine\n\
         namespace Miri.Interpreter.PlaceMachine\n\
         def readImmediate : Nat := 0\n\
         def writeMemory : Nat := 0\n\
         end Miri.Interpreter.PlaceMachine\n\
         namespace Miri.Interpreter.ValidityVisitor\n\
         def validatePlace : Nat := 0\n\
         end Miri.Interpreter.ValidityVisitor\n\
         namespace Miri.Interpreter.ValidityMemory\n\
         def bind : Nat := 0\n\
         end Miri.Interpreter.ValidityMemory\n\
         namespace Miri.Interpreter\n\
         def evalRvalueIntoPlace : Nat := 0\n\
         def evalOperand : Nat := 0\n\
         end Miri.Interpreter\n\
         namespace Miri.Interpreter.TerminatorMachine\n\
         def beforeTerminatorWithChoice : Nat := 0\n\
         end Miri.Interpreter.TerminatorMachine\n\
         namespace Miri.Interpreter.ScalarOps\n\
         def binary : Nat := 0\n\
         def unary : Nat := 0\n\
         end Miri.Interpreter.ScalarOps\n\
         namespace Miri.Interpreter.IntegerOps\n\
         def binary : Nat := 0\n\
         def binaryBool : Nat := 0\n\
         def unary : Nat := 0\n\
         end Miri.Interpreter.IntegerOps\n\
         namespace Miri.Interpreter.Discriminant\n\
         def readDiscriminant : Nat := 0\n\
         def discriminantForVariant : Nat := 0\n\
         end Miri.Interpreter.Discriminant\n\
         namespace Miri.Memory.ScalarInt\n\
         def truncateFromUInt : Nat := 0\n\
         def tryFromUInt : Nat := 0\n\
         def tryToBool : Nat := 0\n\
         end Miri.Memory.ScalarInt\n",
    );
    compile_forged_module(
        &mut checker,
        &src,
        &lib,
        &[],
        "Trusted.MirSemantics",
        "prelude\nimport Init.Core\n\
         namespace Trusted.MirSemantics\n\
         def WellFormed : Prop := True\n\
         def Behavior : Prop := True\n\
         def Diverges : Prop := True\n\
         end Trusted.MirSemantics\n",
    );
    let run_pass2_audit = |chk: &mut Checker| {
        chk.inspect(InspectorRequest::CorrespondenceAudit {
            search_path: vec![lib.clone(), vendor_lib.clone(), corr_lib.clone()],
            trusted: vec!["Trusted".to_string(), "Trusted.MirSemantics".to_string()],
            corr_trusted: vec!["Trusted.Correspondence".to_string()],
            theory: Vec::new(),
            corr_theory: vec!["Anneal.MirCorrespondenceProof".to_string()],
            vendor_miri: vec!["Miri.UnivStub".to_string()],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                (
                    "Trusted.MirSemantics".to_string(),
                    TrustTier::Candidate(CandidateFeature::MirSemantics),
                ),
                (
                    "Trusted.Correspondence".to_string(),
                    TrustTier::Candidate(CandidateFeature::MirSemantics),
                ),
            ]),
        })
    };

    // 2a. Universe-polymorphic `CorrespondenceClaim`.
    compile_forged_module(
        &mut checker,
        &src,
        &lib,
        &["Trusted.MirSemantics"],
        "Trusted.Correspondence",
        "prelude\nimport Init.Core\nimport Trusted.MirSemantics\n\
         namespace Trusted.Correspondence\n\
         def RefWellFormed : Prop := True\n\
         def RefBehavior : Prop := True\n\
         def RefDiverges : Prop := True\n\
         def encodeProg : Nat := 0\n\
         def CorrespondenceClaim.{u} : Prop :=\n\
           (fun (_ : PUnit.{u + 1}) =>\n\
             Trusted.MirSemantics.WellFormed ∧ RefWellFormed ∧\n\
             Trusted.MirSemantics.Behavior ∧ RefBehavior ∧\n\
             Trusted.MirSemantics.Diverges ∧ RefDiverges ∧ encodeProg = encodeProg) PUnit.unit\n\
         end Trusted.Correspondence\n",
    );
    compile_forged_module(
        &mut checker,
        &src,
        &corr_lib,
        &["Trusted.Correspondence"],
        "Anneal.MirCorrespondenceProof",
        "prelude\nimport Init.Core\nimport Trusted.Correspondence\n\
         namespace Anneal.MirCorrespondenceProof\n\
         theorem correspondence_claim_holds : \
           Trusted.Correspondence.CorrespondenceClaim.{0} :=\n\
           ⟨True.intro, True.intro, True.intro, True.intro, True.intro, True.intro, Eq.refl _⟩\n\
         end Anneal.MirCorrespondenceProof\n",
    );
    let err_p2_claim = run_pass2_audit(&mut checker).unwrap_err();
    assert_eq!(err_p2_claim.code, 1, "unexpected code: {err_p2_claim}");
    assert_eq!(err_p2_claim.phase, "correspondence-audit");
    assert!(
        err_p2_claim.message.contains(
            "claim Trusted.Correspondence.CorrespondenceClaim must have no universe parameters"
        ),
        "unexpected Pass 2 poly-claim error: {err_p2_claim}"
    );

    // 2b. Universe-polymorphic `correspondence_claim_holds`.
    compile_forged_module(
        &mut checker,
        &src,
        &lib,
        &["Trusted.MirSemantics"],
        "Trusted.Correspondence",
        "prelude\nimport Init.Core\nimport Trusted.MirSemantics\n\
         namespace Trusted.Correspondence\n\
         def RefWellFormed : Prop := True\n\
         def RefBehavior : Prop := True\n\
         def RefDiverges : Prop := True\n\
         def encodeProg : Nat := 0\n\
         def CorrespondenceClaim : Prop :=\n\
           Trusted.MirSemantics.WellFormed ∧ RefWellFormed ∧\n\
           Trusted.MirSemantics.Behavior ∧ RefBehavior ∧\n\
           Trusted.MirSemantics.Diverges ∧ RefDiverges ∧ encodeProg = encodeProg\n\
         end Trusted.Correspondence\n",
    );
    compile_forged_module(
        &mut checker,
        &src,
        &corr_lib,
        &["Trusted.Correspondence"],
        "Anneal.MirCorrespondenceProof",
        "prelude\nimport Init.Core\nimport Trusted.Correspondence\n\
         namespace Anneal.MirCorrespondenceProof\n\
         theorem correspondence_claim_holds.{u} :\n\
           (fun (_ : PUnit.{u + 1}) => Trusted.Correspondence.CorrespondenceClaim) PUnit.unit :=\n\
           ⟨True.intro, True.intro, True.intro, True.intro, True.intro, True.intro, Eq.refl _⟩\n\
         end Anneal.MirCorrespondenceProof\n",
    );
    let err_p2_thm = run_pass2_audit(&mut checker).unwrap_err();
    assert_eq!(err_p2_thm.code, 1, "unexpected code: {err_p2_thm}");
    assert_eq!(err_p2_thm.phase, "correspondence-audit");
    assert!(
        err_p2_thm.message.contains(
            "theorem Anneal.MirCorrespondenceProof.correspondence_claim_holds must have no universe parameters"
        ),
        "unexpected Pass 2 poly-theorem error: {err_p2_thm}"
    );
}

fn parse_lean_header_imports_for_test(source: &str) -> Vec<String> {
    let bytes = source.as_bytes();
    let mut pos = 0usize;
    let mut imports = Vec::new();
    let mut expecting_import_target = false;
    while pos < bytes.len() {
        while pos < bytes.len() && bytes[pos].is_ascii_whitespace() {
            pos += 1;
        }
        if pos >= bytes.len() {
            break;
        }
        if bytes[pos..].starts_with(b"--") {
            while pos < bytes.len() && bytes[pos] != b'\n' {
                pos += 1;
            }
            continue;
        }
        if bytes[pos..].starts_with(b"/-") {
            pos += 2;
            let mut depth = 1usize;
            while pos < bytes.len() && depth > 0 {
                if bytes[pos..].starts_with(b"/-") {
                    depth += 1;
                    pos += 2;
                } else if bytes[pos..].starts_with(b"-/") {
                    depth -= 1;
                    pos += 2;
                } else {
                    pos += 1;
                }
            }
            continue;
        }
        let start = pos;
        while pos < bytes.len()
            && !bytes[pos].is_ascii_whitespace()
            && !bytes[pos..].starts_with(b"--")
            && !bytes[pos..].starts_with(b"/-")
        {
            pos += 1;
        }
        let token = &source[start..pos];
        if expecting_import_target {
            if token == "all" {
                continue;
            }
            imports.push(token.to_string());
            expecting_import_target = false;
        } else if token == "import" {
            expecting_import_target = true;
        } else if !matches!(token, "module" | "prelude" | "public" | "meta") {
            break;
        }
    }
    imports
}

/// Ensures `theory/Anneal.lean` is absent, all four domain umbrellas
/// (`Anneal.{Scalar,Wp,PureLift,Simd}`) exist in `theory/`,
/// `theory/bundle-manifest.json` includes `Scalar` and `Wp`, excludes
/// `*Canaries*`, and is transitively closed under `Anneal.*` header imports,
/// `Anneal.Scalar`'s closure stays free of `Trusted.*`, `MirWp*`, `LoopInv`,
/// `ClassicalEm`, and `BitTrieLrat`, zero non-canary `theory/` modules import
/// `*Canaries*`, and `scan_lean_tree` still discovers all decoupled
/// `*Canaries*.lean` files for Pass-1 repository `anneal-audit`.
#[test]
fn theory_umbrella_and_manifest_exclude_canaries_and_match() {
    let checkout = repo_root();
    assert!(
        !checkout.join("theory/Anneal.lean").exists(),
        "monolithic theory/Anneal.lean must stay retired in favor of domain umbrellas"
    );
    let (_, manifest) = bundle::load_theory_bundle_manifest(&checkout)
        .expect("load theory/bundle-manifest.json");
    let manifest_paths: BTreeSet<String> =
        manifest.modules.iter().map(|m| m.path.clone()).collect();
    assert!(
        !manifest_paths.iter().any(|p| p.contains("Canaries")),
        "bundle-manifest.json must exclude *Canaries* modules: {manifest_paths:?}"
    );
    assert!(
        manifest_paths.contains("theory/Anneal/Scalar.lean"),
        "bundle-manifest.json must bundle theory/Anneal/Scalar.lean"
    );
    assert!(
        manifest_paths.contains("theory/Anneal/Wp.lean"),
        "bundle-manifest.json must bundle theory/Anneal/Wp.lean"
    );
    assert!(
        manifest_paths.contains("theory/Anneal/Framework.lean"),
        "bundle-manifest.json must bundle theory/Anneal/Framework.lean"
    );

    let theory_modules =
        scan_lean_tree(&checkout.join("theory"), "Anneal").expect("scan_lean_tree on theory/");
    assert!(!theory_modules.contains_key("Anneal"));
    for domain_umbrella in ["Anneal.Scalar", "Anneal.Wp", "Anneal.PureLift", "Anneal.Simd"] {
        assert!(
            theory_modules.contains_key(domain_umbrella),
            "expected domain umbrella {domain_umbrella} in theory/"
        );
    }

    let canary_modules: BTreeSet<String> =
        theory_modules.keys().filter(|m| m.contains("Canaries")).cloned().collect();
    assert!(
        canary_modules.contains("Anneal.MirWp.Canaries"),
        "scan_lean_tree must still discover decoupled Anneal.MirWp.Canaries for Pass-1 audit"
    );
    assert!(
        canary_modules.contains("Anneal.F2Simd.Canaries"),
        "scan_lean_tree must still discover decoupled Anneal.F2Simd.Canaries for Pass-1 audit"
    );
    assert!(
        canary_modules.contains("Anneal.ByteRun.Canaries"),
        "scan_lean_tree must still discover decoupled Anneal.ByteRun.Canaries for Pass-1 audit"
    );
    assert!(
        canary_modules.contains("Anneal.OverflowCastJoin.Canaries"),
        "scan_lean_tree must still discover decoupled Anneal.OverflowCastJoin.Canaries for Pass-1 audit"
    );
    assert!(
        canary_modules.contains("Anneal.RefFrame.Canaries"),
        "scan_lean_tree must still discover decoupled Anneal.RefFrame.Canaries for Pass-1 audit"
    );
    assert!(
        canary_modules.contains("Anneal.CallStackUnwind.Canaries"),
        "scan_lean_tree must still discover decoupled Anneal.CallStackUnwind.Canaries for Pass-1 audit"
    );
    assert!(
        canary_modules.contains("Anneal.Framework.Canaries"),
        "scan_lean_tree must still discover decoupled Anneal.Framework.Canaries for Pass-1 audit"
    );
    assert!(
        canary_modules.len() >= 17,
        "expected scan_lean_tree to discover all decoupled *Canaries*.lean modules dynamically, got {canary_modules:?}"
    );

    // Every non-canary module under `theory/` (including bundled and unbundled
    // domain umbrellas) must not import any `*Canaries*` module or monolithic
    // `Anneal`.
    for (module, path) in &theory_modules {
        if canary_modules.contains(module) {
            continue;
        }
        let src = fs::read_to_string(path).unwrap();
        let imps = parse_lean_header_imports_for_test(&src);
        assert!(
            !imps.iter().any(|dep| dep.contains("Canaries")),
            "non-canary theory module {module} must not import any *Canaries* module: {imps:?}"
        );
        assert!(
            !imps.iter().any(|dep| dep == "Anneal"),
            "theory module {module} must not import retired Anneal umbrella: {imps:?}"
        );
    }

    // `theory/bundle-manifest.json` must be transitively closed under
    // `Anneal.*` header imports so every bundled module's theory dependencies
    // are also bundled.
    for rel_path in &manifest_paths {
        let src = fs::read_to_string(checkout.join(rel_path)).unwrap();
        for dep in parse_lean_header_imports_for_test(&src) {
            if dep == "Anneal" || dep.starts_with("Anneal.") {
                let dep_rel = format!("theory/{}.lean", dep.replace('.', "/"));
                assert!(
                    manifest_paths.contains(&dep_rel),
                    "bundled module {rel_path} imports unbundled theory module {dep} ({dep_rel})"
                );
            }
        }
    }

    // Verify `Anneal.Scalar`'s transitive header import closure stays purely
    // constructive and model-independent (excluding `Trusted.*`, `MirWp*`,
    // `LoopInv`, `ClassicalEm`, and `BitTrieLrat`).
    let mut scalar_theory_visited = BTreeSet::new();
    let mut scalar_all_imports = BTreeSet::new();
    let mut queue = VecDeque::from([String::from("Anneal.Scalar")]);
    while let Some(module) = queue.pop_front() {
        if !scalar_theory_visited.insert(module.clone()) {
            continue;
        }
        let path = theory_modules
            .get(&module)
            .unwrap_or_else(|| panic!("missing theory source for {module}"));
        let src = fs::read_to_string(path).unwrap();
        for dep in parse_lean_header_imports_for_test(&src) {
            scalar_all_imports.insert(dep.clone());
            if dep.starts_with("Anneal.") && !scalar_theory_visited.contains(&dep) {
                queue.push_back(dep);
            }
        }
    }
    for imp in &scalar_all_imports {
        assert!(
            imp != "Trusted"
                && !imp.starts_with("Trusted.")
                && imp != "Anneal.MirWp"
                && !imp.starts_with("Anneal.MirWp.")
                && imp != "Anneal.LoopInv"
                && imp != "Anneal.ClassicalEm"
                && imp != "Anneal.BitTrieLrat"
                && !imp.contains("Canaries"),
            "Anneal.Scalar transitive closure must exclude {imp} (closure={scalar_all_imports:?})"
        );
    }
}

/// Verifies that `Trusted.Framework` (`candidate:refinement`) compiles,
/// passes `"preflight"` and Pass-1 kernel replay onto `foundation-lock.json`,
/// discharges a structured `EnvelopeTheorem` proof in `Anneal.*`, and remains
/// isolated from `vetted` modules.
#[test]
fn trusted_framework_pass1_replay_and_vetted_tier_isolation() {
    let checkout = repo_root();
    let framework_src =
        fs::read_to_string(checkout.join("trusted/lean/Trusted/Framework.lean")).unwrap();
    let mut fix = TempFixture::new(Some(HEADER));
    fs::create_dir_all(fix.root.join("trusted/lean/Trusted")).unwrap();
    fs::write(fix.root.join("trusted/lean/Trusted/Framework.lean"), &framework_src).unwrap();
    fs::create_dir_all(fix.root.join("theory/Anneal")).unwrap();
    fs::write(
        fix.root.join("theory/Anneal/TrustedFrameworkTest.lean"),
        concat!(
            "module\n",
            "prelude\n",
            "public import Init.NotationExtra\n",
            "public import Init.Data.List.Basic\n",
            "public import Trusted.Framework\n",
            "public section\n",
            "namespace Anneal\n",
            "open Trusted.Framework\n",
            "def unitModel : ExecutionModel Unit Unit Unit Unit Unit Unit :=\n",
            "  { profileId := \"unit_v1\"\n",
            "    oracleGrade := .biFaultEquiv \"unit_ref\"\n",
            "    programAdmitted := fun _ => true\n",
            "    bodyAdmitted := fun _ _ => true\n",
            "    isPartialScope := fun _ => false\n",
            "    bodyAt := fun _ n => match n with | 0 => some () | _ => none\n",
            "    uniqueIdentities := fun _ => true\n",
            "    bodyIdentity := fun _ => \"fn_u\"\n",
            "    bodyIsUnsafe := fun _ => false\n",
            "    bodyIsExternal := fun _ => false\n",
            "    bodyMatchesSig := fun _ _ => true\n",
            "    modelGaps := []\n",
            "    requiredGaps := fun _ => []\n",
            "    claimShapeGaps := fun _ => []\n",
            "    entryDom := fun _ _ => True\n",
            "    returnValid := fun _ _ _ => True\n",
            "    memValid := fun _ => True\n",
            "    execForBody := fun p _ => p\n",
            "    wellFormed := fun _ _ => True\n",
            "    produces := fun _ _ out => out = .returned () ()\n",
            "    diverges := fun _ _ => False\n",
            "    faultsUB := fun _ _ => False }\n",
            "theorem nonEmptyUnitId : (\"unit_v1\" : String) ≠ \"\" := by\n",
            "  intro h\n",
            "  exact Nat.noConfusion\n",
            "    (congrArg (fun s => s.toByteArray.data.toList.length) h)\n",
            "theorem nonEmptyRefId : (\"unit_ref\" : String) ≠ \"\" := by\n",
            "  intro h\n",
            "  exact Nat.noConfusion\n",
            "    (congrArg (fun s => s.toByteArray.data.toList.length) h)\n",
            "theorem nonEmptyFnId : (\"fn_u\" : String) ≠ \"\" := by\n",
            "  intro h\n",
            "  exact Nat.noConfusion\n",
            "    (congrArg (fun s => s.toByteArray.data.toList.length) h)\n",
            "theorem unitEnvelopeOk :\n",
            "    EnvelopeTheorem (mkEnvelope unitModel ()\n",
            "      [{ identity := \"fn_u\"\n",
            "         sig := ()\n",
            "         contract := {\n",
            "           effects := {\n",
            "             terminates := true,\n",
            "             noUnwind := true,\n",
            "             noAbort := true } } }]\n",
            "      [] [] [.forallSafety, .termination] []) := by\n",
            "  refine ⟨⟨nonEmptyUnitId, rfl, (fun _ _ _ => rfl), rfl,\n",
            "           (fun h => Bool.noConfusion h), nonEmptyRefId, ?_,\n",
            "           (fun _ h => by cases h)⟩,\n",
            "          ?_, ⟨nonEmptyFnId, (fun _ h => by cases h), True.intro⟩,\n",
            "          ?_, (fun _ h => by cases h), (fun _ h => by cases h), ?_⟩\n",
            "  · intro cs hMem\n",
            "    cases hMem with\n",
            "    | head => exact ⟨rfl, fun _ h => by cases h⟩\n",
            "    | tail _ h2 =>\n",
            "      cases h2 with\n",
            "      | head => exact ⟨rfl, fun _ h => by cases h⟩\n",
            "      | tail _ hNil => cases hNil\n",
            "  · intro _ _\n",
            "    exact ⟨List.Mem.head _,\n",
            "           fun _ => List.Mem.tail _ (List.Mem.head _)⟩\n",
            "  · intro e hMem\n",
            "    cases hMem with\n",
            "    | head =>\n",
            "      refine ⟨0, (), rfl, rfl, rfl, rfl, (fun _ h => by cases h),\n",
            "              (fun _ _ _ => True.intro), ?_, ?_⟩\n",
            "      · intro _ _ _\n",
            "        refine ⟨(fun _ hDiv => hDiv),\n",
            "                (fun _ _ _ => ⟨True.intro, True.intro⟩),\n",
            "                (fun _ h => by cases h),\n",
            "                (fun _ h => by cases h)⟩\n",
            "      · exact Or.inl ⟨rfl, Or.inl ⟨(), True.intro,\n",
            "          ⟨(fun h => Bool.noConfusion h), True.intro⟩⟩⟩\n",
            "    | tail _ hNil => cases hNil\n",
            "  · intro defId _ hGet\n",
            "    cases defId with\n",
            "    | zero => exact List.Mem.head _\n",
            "    | succ _ => cases hGet\n",
            "end Anneal\n",
            "end\n",
        ),
    )
    .unwrap();
    let mut checker = Checker::new(&fix.root, None).unwrap();
    checker.set_require_mir_wp(false);
    let report = checker.run().unwrap();
    assert_eq!(report["replay"], json!(true), "{report}");
    let decls = report["declarations"].as_array().unwrap();
    let fw_decls: Vec<&Json> =
        decls.iter().filter(|d| d["module"] == json!("Trusted.Framework")).collect();
    assert!(!fw_decls.is_empty(), "expected Trusted.Framework declarations in report");
    for d in &fw_decls {
        assert_eq!(d["trustStatus"], json!("candidate:refinement"), "{d}");
    }
    // Non-vacuously inspect the compiled `Trusted/Framework.olean` via
    // `Lean.readModuleData` (since `report["declarations"]` excludes partial
    // paired `._unsafe_rec` helpers) to confirm zero `partial` / `._unsafe_rec`
    // constants are emitted for `NoDupStrings` or any other declaration.
    let fw_olean = checker.stage().join("lib/Trusted/Framework.olean");
    let check_script = checker.stage().join("CheckNoUnsafeRec.lean");
    run_lean_script(
        &mut checker,
        "check-no-unsafe-rec",
        &check_script,
        &format!(
            r#"import Lean
open Lean in
def main : IO Unit := do
  let (data, _) ← readModuleData (System.FilePath.mk {:?})
  unless data.constants.any (fun ci => ci.name == `Trusted.Framework.NoDupStrings) do
    throw (IO.userError "missing Trusted.Framework.NoDupStrings in compiled olean")
  for ci in data.constants do
    if ci.isPartial || ci.name.toString.endsWith "._unsafe_rec" then
      throw (IO.userError s!"unexpected partial/_unsafe_rec constant: {{ci.name}}")
  for n in data.extraConstNames do
    if n.toString.endsWith "._unsafe_rec" then
      throw (IO.userError s!"unexpected extra _unsafe_rec constant: {{n}}")
"#,
            fw_olean.to_string_lossy()
        ),
    );

    // Negative: a `vetted` module attempting to import `Trusted.Framework`
    // (`candidate:refinement`) fails closed in `"preflight"`.
    fs::write(
        fix.root.join("trusted/lean/Trusted/VettedImportsFramework.lean"),
        "-- anneal-trust-tier: vetted\n\
         module\n\
         prelude\n\
         public import Init.NotationExtra\n\
         public import Trusted.Framework\n",
    )
    .unwrap();
    let err = fix.check_expected(Some(1), Some("preflight"), Some(false)).unwrap_err();
    assert!(
        err.message.contains(
            "vetted module Trusted.VettedImportsFramework cannot import candidate:refinement module Trusted.Framework"
        ),
        "{err}"
    );
}
