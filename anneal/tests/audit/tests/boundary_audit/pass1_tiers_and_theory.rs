// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Trust tiers, namespace hygiene, and reserved theory roots.

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
            allow_local_semireducible: false,
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
            allow_local_semireducible: false,
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
            allow_local_semireducible: false,
        })
        .expect("vetted source importing vetted base module in baseSources must pass");

    let lean_pf_corr_bad = checker_lean_pf.stage().join("pf-corr-bad.lean");
    fs::write(&lean_pf_corr_bad, format!("{HEADER}import Trusted.Cand\n")).unwrap();
    let err_pf_base_cand = checker_lean_pf
        .inspect(InspectorRequest::Preflight {
            sources: vec![("Trusted.Correspondence".to_string(), lean_pf_corr_bad)],
            base_trusted_sources: pf_base_sources.clone(),
            allow_local_semireducible: false,
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
            allow_local_semireducible: false,
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
            allow_local_semireducible: false,
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
            allow_local_semireducible: false,
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
            allow_local_semireducible: false,
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
            allow_local_semireducible: false,
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
            allow_local_semireducible: false,
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

/// Pass 1 `"audit"` independently rejects a compiled `theory/` constant whose
/// name ends with a name in `localSemireducibleAllowlist`, even when the
/// module was compiled without repository `"preflight"`, so
/// `declaresLocalSemireducibleShadow` never saw it. Only
/// `validateRepoConstant` can reject it.
#[test]
fn rejects_compiled_local_semireducible_shadow_in_theory() {
    let fix = TempFixture::new(None);
    fs::create_dir_all(fix.root.join("theory")).unwrap();
    fs::write(
        fix.root.join("theory/Anneal.lean"),
        b"prelude\nimport Trusted\nnamespace Anneal\ndef helper : Nat := 0\nend Anneal\n",
    )
    .unwrap();
    let mut checker = fix.checker();
    checker.set_require_mir_wp(false);
    checker.run().unwrap();

    let stage = checker.stage().to_path_buf();
    compile_forged_module(
        &mut checker,
        &stage.join("src/forged"),
        &stage.join("lib"),
        &[],
        "Anneal.Forged",
        "prelude\nimport Init.Core\nnamespace Foo.Nat\ndef bitwise : Nat := 0\nend Foo.Nat\n",
    );
    let err = checker
        .inspect(InspectorRequest::Audit {
            trusted: vec!["Trusted".to_string()],
            theory: vec!["Anneal".to_string(), "Anneal.Forged".to_string()],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert_eq!(err.code, 1, "unexpected code: {err}");
    assert_eq!(err.phase, "audit", "unexpected phase: {err}");
    assert!(
        err.message.contains(
            "theory module Anneal.Forged cannot declare constant Foo.Nat.bitwise, whose name \
             could shadow one in `localSemireducibleAllowlist`"
        ),
        "unexpected error: {err}"
    );
}
