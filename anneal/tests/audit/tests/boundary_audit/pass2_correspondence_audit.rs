// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Correspondence audit violations and sysroot mismatches.

use super::*;

/// Verifies negative cases for correspondence-audit rules in
/// `TrustedBoundary.lean` (`classifyCorrModules`,
/// `CorrOrigin.importViolation?`, `CorrOrigin.edgeViolation?`, and
/// `closureCorr` unapproved-axiom rejection) and for toolchain sysroot
/// manifest authentication (`verify_sysroot_foundation_dir`).
#[test]
fn rejects_correspondence_audit_violations_and_sysroot_mismatch() {
    let fix = TempFixture::new(None);

    // 1. Sysroot manifest mismatch & symlink rejection.
    let fake_lib = fix.root.join("fake-sysroot-lib");
    for pkg in ["Init", "Std", "Lean"] {
        fs::create_dir_all(fake_lib.join(pkg)).unwrap();
    }
    fs::write(fake_lib.join("Init/Dummy.olean"), b"dummy-olean").unwrap();
    let err_sysroot =
        verify_sysroot_foundation_dir(&fake_lib, &BTreeSet::new(), &"0".repeat(64)).unwrap_err();
    assert_eq!(err_sysroot.phase, "sysroot-foundation");
    assert!(
        err_sysroot.message.contains("sysroot Init/Std/Lean .olean/.ir manifest SHA-256 mismatch"),
        "unexpected sysroot mismatch error: {err_sysroot}"
    );
    symlink(fake_lib.join("Init/Dummy.olean"), fake_lib.join("Std/Link.olean")).unwrap();
    let err_sym =
        verify_sysroot_foundation_dir(&fake_lib, &BTreeSet::new(), &"0".repeat(64)).unwrap_err();
    assert!(
        err_sym.message.contains("symlink forbidden in sysroot"),
        "unexpected sysroot symlink error: {err_sym}"
    );

    // Prepare compiled synthetic modules for `TrustedBoundary.lean`
    // `"correspondence-audit"` negative cases.
    let mut checker = fix.checker();
    checker.set_require_mir_wp(false);
    checker.run().unwrap();
    let trusted_lib = checker.stage().join("lib");
    let aux_src = checker.stage().join("src/corr-neg");
    let aux_path = env::join_paths([&trusted_lib]).unwrap();

    let compile_aux = |chk: &mut Checker, module: &str, body: &str| {
        let rel = module.replace('.', "/");
        let src = aux_src.join(format!("{rel}.lean"));
        fs::create_dir_all(src.parent().unwrap()).unwrap();
        fs::write(&src, body).unwrap();
        let out = trusted_lib.join(format!("{rel}.olean"));
        fs::create_dir_all(out.parent().unwrap()).unwrap();
        chk.process_with_path(
            &format!("compile-{module}"),
            &[
                "-j1".to_string(),
                "-M2048".to_string(),
                "-t0".to_string(),
                "-R".to_string(),
                aux_src.to_string_lossy().into_owned(),
                "-o".to_string(),
                out.to_string_lossy().into_owned(),
                src.to_string_lossy().into_owned(),
            ],
            Some(&aux_path),
        )
        .unwrap();
    };

    compile_aux(
        &mut checker,
        "Miri.Child",
        "prelude\nimport Init.Core\nnamespace Miri.Child\ndef c : Nat := 1\nend Miri.Child\n",
    );
    compile_aux(
        &mut checker,
        "Miri.Parent",
        "prelude\nimport Init.Core\nimport Miri.Child\n\
         namespace Miri.Parent\ndef p : Nat := Miri.Child.c\nend Miri.Parent\n",
    );
    compile_aux(
        &mut checker,
        "Trusted.CandHelper",
        "-- anneal-trust-tier: candidate:mir_semantics\n\
         prelude\nimport Init.Core\nnamespace Trusted.CandHelper\ndef h : Nat := 1\nend Trusted.CandHelper\n",
    );
    compile_aux(
        &mut checker,
        "Trusted.VettedRefsCand",
        "prelude\nimport Init.Core\nimport Trusted.CandHelper\n\
         namespace Trusted.VettedRefsCand\ndef x : Nat := Trusted.CandHelper.h\nend Trusted.VettedRefsCand\n",
    );
    compile_aux(
        &mut checker,
        "Trusted.VettedRefsMiri",
        "prelude\nimport Init.Core\nimport Miri.Child\n\
         namespace Trusted.VettedRefsMiri\ndef x : Nat := Miri.Child.c\nend Trusted.VettedRefsMiri\n",
    );
    compile_aux(
        &mut checker,
        "Anneal.Helper",
        "prelude\nimport Init.Core\nnamespace Anneal.Helper\ndef t : Nat := 2\nend Anneal.Helper\n",
    );
    compile_aux(
        &mut checker,
        "Trusted.CandRefsTheory",
        "prelude\nimport Init.Core\nimport Anneal.Helper\n\
         namespace Trusted.CandRefsTheory\ndef x : Nat := Anneal.Helper.t\nend Trusted.CandRefsTheory\n",
    );
    compile_aux(
        &mut checker,
        "Miri.Interpreter.ExecutionMachine",
        "prelude\nimport Init.Core\n\
         namespace Miri.Interpreter.ExecutionMachine\n\
         theorem step : (True ↔ True) → True = True := propext\n\
         end Miri.Interpreter.ExecutionMachine\n",
    );

    let search = vec![trusted_lib];

    // 2a. `classifyCorrModules`: overlapping module role.
    let err_overlap = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Trusted".to_string()],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert!(
        err_overlap.message.contains("overlapping module role for Trusted"),
        "unexpected overlap error: {err_overlap}"
    );

    // 2b. `classifyCorrModules`: missing trust tier for Trusted module.
    let err_missing_tier = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            module_tiers: BTreeMap::new(),
        })
        .unwrap_err();
    assert!(
        err_missing_tier.message.contains("missing trust tier for Trusted module Trusted"),
        "unexpected missing-tier error: {err_missing_tier}"
    );

    // 2c. `classifyCorrModules`: trust tier declared for non-Trusted module.
    let err_non_trusted_tier = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                ("Miri.Child".to_string(), TrustTier::Vetted),
            ]),
        })
        .unwrap_err();
    assert!(
        err_non_trusted_tier
            .message
            .contains("trust tier declared for non-Trusted module Miri.Child"),
        "unexpected non-trusted-tier error: {err_non_trusted_tier}"
    );

    // 2d. `classifyCorrModules`: foreign module in correspondence environment
    // (`Miri.Parent` imports unlisted `Miri.Child`).
    let err_foreign = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.Parent".to_string()],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert!(
        err_foreign.message.contains("foreign module Miri.Child in correspondence environment"),
        "unexpected foreign-module error: {err_foreign}"
    );

    // 3a. `CorrOrigin.importViolation?`: vetted -> candidate (rejected before
    // `checkDeclarationEdges` inspects the constant reference).
    let err_vetted_cand = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search.clone(),
            trusted: vec![
                "Trusted".to_string(),
                "Trusted.CandHelper".to_string(),
                "Trusted.VettedRefsCand".to_string(),
            ],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                (
                    "Trusted.CandHelper".to_string(),
                    TrustTier::Candidate(CandidateFeature::MirSemantics),
                ),
                ("Trusted.VettedRefsCand".to_string(), TrustTier::Vetted),
            ]),
        })
        .unwrap_err();
    assert_eq!(err_vetted_cand.code, 1, "unexpected vetted->cand code: {err_vetted_cand}");
    assert!(
        err_vetted_cand.message.contains(
            "vetted module Trusted.VettedRefsCand cannot import candidate:mir_semantics module Trusted.CandHelper"
        ),
        "unexpected vetted->cand error: {err_vetted_cand}"
    );

    // 3b. `CorrOrigin.importViolation?`: vetted -> vendorMiri (rejected before
    // `checkDeclarationEdges` inspects the constant reference).
    let err_vetted_miri = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string(), "Trusted.VettedRefsMiri".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                ("Trusted.VettedRefsMiri".to_string(), TrustTier::Vetted),
            ]),
        })
        .unwrap_err();
    assert_eq!(err_vetted_miri.code, 1, "unexpected vetted->miri code: {err_vetted_miri}");
    assert!(
        err_vetted_miri.message.contains(
            "vetted module Trusted.VettedRefsMiri cannot import non-foundation module Miri.Child"
        ),
        "unexpected vetted->miri error: {err_vetted_miri}"
    );

    // 3a-edge & 3b-edge. `CorrOrigin.edgeViolation?` defense in depth: forged
    // `vetted` `.olean` headers importing only `Init.Core` while referencing
    // `Trusted.CandHelper.h` or `Miri.Child.c` remain rejected by
    // `checkDeclarationEdges`.
    let stage = checker.stage().to_path_buf();
    for (forged_mod, ref_const, extra_trusted, expected_msg) in [
        (
            "Trusted.ForgedCorrVettedCand",
            "Trusted.CandHelper.h",
            true,
            "vetted constant Trusted.ForgedCorrVettedCand.x references candidate:mir_semantics constant Trusted.CandHelper.h",
        ),
        (
            "Trusted.ForgedCorrVettedMiri",
            "Miri.Child.c",
            false,
            "vetted constant Trusted.ForgedCorrVettedMiri.x references non-foundation constant Miri.Child.c",
        ),
    ] {
        let out = search[0].join(format!("{}.olean", forged_mod.replace('.', "/")));
        fs::create_dir_all(out.parent().unwrap()).unwrap();
        run_lean_script(
            &mut checker,
            &format!("gen-{forged_mod}"),
            &stage.join(format!("gen_{}.lean", forged_mod.replace('.', "_"))),
            &format!(
                "import Lean.Environment\n\
                 open Lean\n\
                 def main : IO Unit := do\n\
                   let ci : ConstantInfo := .defnInfo {{\n\
                     name := `{forged_mod}.x\n\
                     levelParams := []\n\
                     type := .const `Nat []\n\
                     value := .const `{ref_const} []\n\
                     hints := .abbrev\n\
                     safety := .safe\n\
                     all := [`{forged_mod}.x]\n\
                   }}\n\
                   let md : ModuleData := {{\n\
                     isModule := false\n\
                     imports := #[{{ module := `Init.Core }}]\n\
                     constNames := #[`{forged_mod}.x]\n\
                     constants := #[ci]\n\
                     extraConstNames := #[]\n\
                     entries := #[]\n\
                   }}\n\
                   saveModuleData (System.FilePath.mk {:?}) `{forged_mod} md\n",
                out.to_string_lossy()
            ),
        );
        let mut trusted_mods = vec!["Trusted".to_string(), forged_mod.to_string()];
        let mut tiers = BTreeMap::from([
            ("Trusted".to_string(), TrustTier::Vetted),
            (forged_mod.to_string(), TrustTier::Vetted),
        ]);
        if extra_trusted {
            trusted_mods.push("Trusted.CandHelper".to_string());
            tiers.insert(
                "Trusted.CandHelper".to_string(),
                TrustTier::Candidate(CandidateFeature::MirSemantics),
            );
        }
        let err_edge = checker
            .inspect(InspectorRequest::CorrespondenceAudit {
                search_path: search.clone(),
                trusted: trusted_mods,
                corr_trusted: Vec::new(),
                theory: Vec::new(),
                corr_theory: Vec::new(),
                vendor_miri: vec!["Miri.Child".to_string()],
                module_tiers: tiers,
            })
            .unwrap_err();
        assert_eq!(err_edge.code, 1, "unexpected forged edge code for {forged_mod}: {err_edge}");
        assert!(
            err_edge.message.contains(expected_msg),
            "unexpected forged edge error for {forged_mod}: {err_edge}"
        );
    }

    // 3d. `"correspondence-preflight"` rejects a declaration-free `vetted`
    // Pass 2 source importing a Pass 1 `candidate:mir_semantics` module, a
    // `vendor/lean-miri` module, or a Pass 1 `.repo .theory` module
    // (`Anneal.Helper`) before compilation, deriving Pass 1 base tiers
    // directly from staged `"baseSources"` rather than a caller map.
    let trusted_base_src = checker.modules()["Trusted"].clone();
    let cand_helper_src = aux_src.join("Trusted/CandHelper.lean");
    let corr_pf_dir = stage.join("src/corr-pf-tier");
    fs::create_dir_all(&corr_pf_dir).unwrap();
    let corr_vetted_cand_src = corr_pf_dir.join("CorrVettedCand.lean");
    fs::write(
        &corr_vetted_cand_src,
        "-- anneal-trust-tier: vetted\nprelude\nimport Init.Core\nimport Trusted.CandHelper\n",
    )
    .unwrap();
    let err_pf_cand = checker
        .inspect(InspectorRequest::CorrespondencePreflight {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string(), "Trusted.CandHelper".to_string()],
            theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            base_trusted_sources: vec![
                ("Trusted".to_string(), trusted_base_src.clone()),
                ("Trusted.CandHelper".to_string(), cand_helper_src.clone()),
            ],
            sources: vec![("Trusted.CorrVettedCand".to_string(), corr_vetted_cand_src.clone())],
        })
        .unwrap_err();
    assert_eq!(err_pf_cand.code, 1, "unexpected corr-pf cand code: {err_pf_cand}");
    assert_eq!(err_pf_cand.phase, "correspondence-preflight");
    assert!(
        err_pf_cand.message.contains(
            "vetted module Trusted.CorrVettedCand cannot import candidate:mir_semantics module Trusted.CandHelper"
        ),
        "unexpected corr-pf cand error: {err_pf_cand}"
    );

    let corr_vetted_miri_src = corr_pf_dir.join("CorrVettedMiri.lean");
    fs::write(
        &corr_vetted_miri_src,
        "-- anneal-trust-tier: vetted\nprelude\nimport Init.Core\nimport Miri.Child\n",
    )
    .unwrap();
    let err_pf_miri = checker
        .inspect(InspectorRequest::CorrespondencePreflight {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            base_trusted_sources: vec![("Trusted".to_string(), trusted_base_src.clone())],
            sources: vec![("Trusted.CorrVettedMiri".to_string(), corr_vetted_miri_src)],
        })
        .unwrap_err();
    assert_eq!(err_pf_miri.code, 1, "unexpected corr-pf miri code: {err_pf_miri}");
    assert_eq!(err_pf_miri.phase, "correspondence-preflight");
    assert!(
        err_pf_miri.message.contains(
            "vetted module Trusted.CorrVettedMiri cannot import non-foundation module Miri.Child"
        ),
        "unexpected corr-pf miri error: {err_pf_miri}"
    );

    let corr_vetted_theory_src = corr_pf_dir.join("CorrVettedTheory.lean");
    fs::write(
        &corr_vetted_theory_src,
        "-- anneal-trust-tier: vetted\nprelude\nimport Init.Core\nimport Anneal.Helper\n",
    )
    .unwrap();
    let err_pf_theory = checker
        .inspect(InspectorRequest::CorrespondencePreflight {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            theory: vec!["Anneal.Helper".to_string()],
            vendor_miri: vec!["Miri.Child".to_string()],
            base_trusted_sources: vec![("Trusted".to_string(), trusted_base_src.clone())],
            sources: vec![("Trusted.CorrVettedTheory".to_string(), corr_vetted_theory_src)],
        })
        .unwrap_err();
    assert_eq!(err_pf_theory.code, 1, "unexpected corr-pf theory code: {err_pf_theory}");
    assert_eq!(err_pf_theory.phase, "correspondence-preflight");
    assert!(
        err_pf_theory.message.contains(
            "vetted module Trusted.CorrVettedTheory cannot import non-foundation module Anneal.Helper"
        ),
        "unexpected corr-pf theory error: {err_pf_theory}"
    );

    // Reject a direct `"correspondence-preflight"` caller that submits a
    // vetted source colliding with an already-loaded Pass 1 `candidate`
    // module (`Trusted.CandHelper`), or submits missing, extra, duplicate,
    // non-`Trusted`, or tactic-contaminated `base_trusted_sources`.
    let corr_fake_cand_src = corr_pf_dir.join("FakeCandHelper.lean");
    fs::write(&corr_fake_cand_src, b"-- anneal-trust-tier: vetted\nprelude\nimport Init.Core\n")
        .unwrap();
    let corr_vetted_cand_src2 = corr_pf_dir.join("CorrVettedCand2.lean");
    fs::write(
        &corr_vetted_cand_src2,
        b"-- anneal-trust-tier: vetted\nprelude\nimport Init.Core\nimport Trusted.CandHelper\n",
    )
    .unwrap();
    let err_pf_cand_collision = checker
        .inspect(InspectorRequest::CorrespondencePreflight {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string(), "Trusted.CandHelper".to_string()],
            theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            base_trusted_sources: vec![
                ("Trusted".to_string(), trusted_base_src.clone()),
                ("Trusted.CandHelper".to_string(), cand_helper_src.clone()),
            ],
            sources: vec![
                ("Trusted.CandHelper".to_string(), corr_fake_cand_src),
                ("Trusted.CorrVettedCand".to_string(), corr_vetted_cand_src2),
            ],
        })
        .unwrap_err();
    assert_eq!(err_pf_cand_collision.code, 1, "unexpected collision code: {err_pf_cand_collision}");
    assert_eq!(err_pf_cand_collision.phase, "correspondence-preflight");
    assert!(
        err_pf_cand_collision
            .message
            .contains("preflight source module Trusted.CandHelper collides with base module"),
        "unexpected corr-pf collision error: {err_pf_cand_collision}"
    );

    let err_pf_missing_base = checker
        .inspect(InspectorRequest::CorrespondencePreflight {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string(), "Trusted.CandHelper".to_string()],
            theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            base_trusted_sources: vec![("Trusted".to_string(), trusted_base_src.clone())],
            sources: vec![("Trusted.CorrVettedCand".to_string(), corr_vetted_cand_src.clone())],
        })
        .unwrap_err();
    assert_eq!(err_pf_missing_base.code, 1);
    assert_eq!(err_pf_missing_base.phase, "correspondence-preflight");
    assert!(
        err_pf_missing_base
            .message
            .contains("missing base preflight source for Trusted module Trusted.CandHelper"),
        "unexpected corr-pf missing base error: {err_pf_missing_base}"
    );

    let err_pf_extra_base = checker
        .inspect(InspectorRequest::CorrespondencePreflight {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            base_trusted_sources: vec![
                ("Trusted".to_string(), trusted_base_src.clone()),
                ("Trusted.CandHelper".to_string(), cand_helper_src),
            ],
            sources: vec![("Trusted.CorrVettedCand".to_string(), corr_vetted_cand_src.clone())],
        })
        .unwrap_err();
    assert_eq!(err_pf_extra_base.code, 1);
    assert_eq!(err_pf_extra_base.phase, "correspondence-preflight");
    assert!(
        err_pf_extra_base.message.contains(
            "extra base preflight source Trusted.CandHelper missing from trusted inventory"
        ),
        "unexpected corr-pf extra base error: {err_pf_extra_base}"
    );

    let err_pf_dup_base = checker
        .inspect(InspectorRequest::CorrespondencePreflight {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            base_trusted_sources: vec![
                ("Trusted".to_string(), trusted_base_src.clone()),
                ("Trusted".to_string(), trusted_base_src.clone()),
            ],
            sources: vec![("Trusted.CorrVettedCand".to_string(), corr_vetted_cand_src.clone())],
        })
        .unwrap_err();
    assert_eq!(err_pf_dup_base.code, 1);
    assert_eq!(err_pf_dup_base.phase, "correspondence-preflight");
    assert!(
        err_pf_dup_base.message.contains("duplicate base preflight source module Trusted"),
        "unexpected corr-pf duplicate base error: {err_pf_dup_base}"
    );

    let err_pf_non_trusted_base = checker
        .inspect(InspectorRequest::CorrespondencePreflight {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            base_trusted_sources: vec![
                ("Trusted".to_string(), trusted_base_src),
                ("Anneal.Helper".to_string(), aux_src.join("Anneal/Helper.lean")),
            ],
            sources: vec![("Trusted.CorrVettedCand".to_string(), corr_vetted_cand_src.clone())],
        })
        .unwrap_err();
    assert_eq!(err_pf_non_trusted_base.code, 1);
    assert_eq!(err_pf_non_trusted_base.phase, "correspondence-preflight");
    assert!(
        err_pf_non_trusted_base.message.contains("non-Trusted base preflight source Anneal.Helper"),
        "unexpected corr-pf non-Trusted base error: {err_pf_non_trusted_base}"
    );

    let bad_base_tactic_src = corr_pf_dir.join("BadBaseTactic.lean");
    fs::write(
        &bad_base_tactic_src,
        b"-- anneal-trust-tier: vetted\nprelude\nimport Init.Core\ntheorem bad : Eq 0 0 := by rfl\n",
    )
    .unwrap();
    let err_pf_tactic_base = checker
        .inspect(InspectorRequest::CorrespondencePreflight {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            base_trusted_sources: vec![("Trusted".to_string(), bad_base_tactic_src)],
            sources: vec![("Trusted.CorrVettedCand".to_string(), corr_vetted_cand_src)],
        })
        .unwrap_err();
    assert_eq!(err_pf_tactic_base.code, 1);
    assert_eq!(err_pf_tactic_base.phase, "correspondence-preflight");

    // 3c. `CorrOrigin.importViolation?`: candidate Trusted -> theory. The
    // compiled `.olean` header import of `Anneal.Helper` is rejected before
    // `checkDeclarationEdges` inspects the constant reference;
    // `rejects_forged_trusted_constant_referencing_theory` covers that
    // constant-edge rule with a forged header that omits the import.
    let err_cand_theory = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string(), "Trusted.CandRefsTheory".to_string()],
            corr_trusted: Vec::new(),
            theory: vec!["Anneal.Helper".to_string()],
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                (
                    "Trusted.CandRefsTheory".to_string(),
                    TrustTier::Candidate(CandidateFeature::MirSemantics),
                ),
            ]),
        })
        .unwrap_err();
    assert_eq!(err_cand_theory.code, 1, "unexpected cand->theory code: {err_cand_theory}");
    assert!(
        err_cand_theory.message.contains(
            "Trusted module Trusted.CandRefsTheory cannot import non-Trusted module Anneal.Helper"
        ),
        "unexpected cand->theory error: {err_cand_theory}"
    );

    // 4. `closureCorr`: reachable unapproved axiom (`propext` from `Init.Core`
    // when omitted from the axiom allowlist) rejected after passing
    // `verifyAndCollectCorrLocals` and standalone kernel replay.
    checker.admitted_mut().unwrap().axioms.retain(|(ax, _)| ax != "propext");
    let err_axiom = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search,
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.Interpreter.ExecutionMachine".to_string()],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert!(
        err_axiom.message.contains("unapproved axiom propext from Init.Core"),
        "unexpected unapproved-axiom error: {err_axiom}"
    );
}
