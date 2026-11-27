// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Pass 2 import and origin isolation from `theory/`, and forged trusted
//! and correspondence declarations.

use super::*;

/// Pins end-to-end Pass 2 `baseSources` forwarding across
/// [`Checker::run_correspondence_with_closure`] and
/// `preflight_and_order_modules`:
/// - a `vetted` Pass 2 module importing a `vetted` Pass 1 base module passes
///   Pass 2 `"preflight"`, `"correspondence-preflight"`, and sandboxed
///   compilation into `lib/` before failing later in `"correspondence-audit"`
///   on the synthetic empty Miri closure; and
/// - a `vetted` Pass 2 module importing a `candidate:*` Pass 1 base module is
///   rejected in phase `"preflight"` before Pass 2 compilation.
#[test]
fn preflights_pass2_vetted_imports_against_authenticated_pass1_base_sources() {
    let setup_pass1 = |corr_import: &str| {
        let fix = TempFixture::new(None);
        fs::create_dir_all(fix.root.join("trusted/lean/Trusted")).unwrap();
        fs::write(
            fix.root.join("trusted/lean/Trusted/VettedBase.lean"),
            b"-- anneal-trust-tier: vetted\n\
              prelude\nimport Init.Core\n\
              namespace Trusted.VettedBase\n\
              def ok : Nat := 1\n\
              end Trusted.VettedBase\n",
        )
        .unwrap();
        fs::write(
            fix.root.join("trusted/lean/Trusted/CandBase.lean"),
            b"-- anneal-trust-tier: candidate:mir_semantics\n\
              prelude\nimport Init.Core\n\
              namespace Trusted.CandBase\n\
              def cand : Nat := 2\n\
              end Trusted.CandBase\n",
        )
        .unwrap();
        let mut checker = fix.checker();
        checker.set_require_mir_wp(false);
        checker.run().unwrap();

        let vendor_dir = fix.root.join("synthetic-miri");
        fs::create_dir_all(&vendor_dir).unwrap();
        let corr_trusted = fix.root.join("trusted/correspondence/Trusted/Correspondence.lean");
        let corr_proof = fix.root.join("correspondence/Anneal/MirCorrespondenceProof.lean");
        fs::create_dir_all(corr_trusted.parent().unwrap()).unwrap();
        fs::create_dir_all(corr_proof.parent().unwrap()).unwrap();
        fs::write(
            &corr_trusted,
            format!(
                "-- anneal-trust-tier: vetted\n\
                 prelude\nimport Init.Core\nimport {corr_import}\n\
                 namespace Trusted.Correspondence\n\
                 def corrOk : Nat := 0\n\
                 end Trusted.Correspondence\n"
            ),
        )
        .unwrap();
        fs::write(
            &corr_proof,
            "prelude\nimport Init.Core\nimport Trusted.Correspondence\n\
             namespace Anneal.MirCorrespondenceProof\n\
             def proofOk : Nat := Trusted.Correspondence.corrOk\n\
             end Anneal.MirCorrespondenceProof\n",
        )
        .unwrap();
        let base_tiers = BTreeMap::from([
            ("Trusted".to_string(), TrustTier::Vetted),
            ("Trusted.VettedBase".to_string(), TrustTier::Vetted),
            ("Trusted.CandBase".to_string(), TrustTier::Candidate(CandidateFeature::MirSemantics)),
        ]);
        (fix, checker, vendor_dir, base_tiers)
    };

    // Case 1: `vetted` Pass 2 importing `vetted` Pass 1 base module passes
    // `"preflight"` and `"correspondence-preflight"` and compiles Pass 2.
    let (_fix_ok, mut checker_ok, vendor_ok, base_tiers_ok) = setup_pass1("Trusted.VettedBase");
    let err_ok = checker_ok
        .run_correspondence_with_closure(
            &base_tiers_ok,
            &vendor_ok,
            "synthetic-commit",
            &[],
            &BTreeMap::new(),
        )
        .unwrap_err();
    assert_eq!(err_ok.code, 1, "unexpected error: {err_ok}");
    assert_eq!(
        err_ok.phase, "correspondence-audit",
        "vetted -> vetted Pass 2 import must clear preflight and compile: {err_ok}"
    );
    assert!(
        checker_ok.stage().join("lib/Trusted/Correspondence.olean").exists(),
        "Pass 2 Trusted.Correspondence must compile when importing vetted Pass 1 module"
    );
    assert!(
        checker_ok.stage().join("theory-lib/Anneal/MirCorrespondenceProof.olean").exists(),
        "Pass 2 Anneal.MirCorrespondenceProof must compile after preflight passes"
    );

    // Case 2: `vetted` Pass 2 importing `candidate` Pass 1 base module fails in
    // phase `"preflight"` before Pass 2 compilation.
    let (_fix_bad, mut checker_bad, vendor_bad, base_tiers_bad) = setup_pass1("Trusted.CandBase");
    let err_bad = checker_bad
        .run_correspondence_with_closure(
            &base_tiers_bad,
            &vendor_bad,
            "synthetic-commit",
            &[],
            &BTreeMap::new(),
        )
        .unwrap_err();
    assert_eq!(err_bad.code, 1, "unexpected error: {err_bad}");
    assert_eq!(err_bad.phase, "preflight", "expected preflight failure: {err_bad}");
    assert!(
        err_bad.message.contains(
            "vetted module Trusted.Correspondence cannot import candidate:mir_semantics module Trusted.CandBase"
        ),
        "unexpected error: {err_bad}"
    );
    assert!(
        !checker_bad.stage().join("lib/Trusted/Correspondence.olean").exists(),
        "Pass 2 Trusted.Correspondence must not compile on vetted -> candidate import"
    );
}

/// Pass 1 `"audit"` independently rejects a compiled `Trusted` module whose
/// `.olean` header imports a `theory/` module, even when the module was
/// compiled without repository `"preflight"` and references none of the
/// imported constants (so only `RepoOrigin.importViolation?` applies).
#[test]
fn rejects_compiled_trusted_header_import_of_theory() {
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
        &["Anneal"],
        "Trusted.Forged",
        "prelude\nimport Init.Core\nimport Anneal\nnamespace Trusted\ndef forged : Nat := 0\nend Trusted\n",
    );
    let err = checker
        .inspect(InspectorRequest::Audit {
            trusted: vec!["Trusted".to_string(), "Trusted.Forged".to_string()],
            theory: vec!["Anneal".to_string()],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                ("Trusted.Forged".to_string(), TrustTier::Vetted),
            ]),
        })
        .unwrap_err();
    assert_eq!(err.code, 1, "unexpected code: {err}");
    assert_eq!(err.phase, "audit", "unexpected phase: {err}");
    assert!(
        err.message
            .contains("Trusted module Trusted.Forged cannot import non-Trusted module Anneal"),
        "unexpected error: {err}"
    );
}

/// Pass 1 `"audit"` and Pass 2 `"correspondence-audit"` both reject a
/// `Trusted` constant that references a `theory/` constant (the
/// `.repo (.trusted _), .repo .theory` arm of `RepoOrigin.edgeViolation?` and
/// `CorrOrigin.edgeViolation?`) with policy exit code `1`.
///
/// `Lean.saveModuleData` forges `Trusted.ForgedRef.olean`, whose header
/// imports only `Init.Core` (so `checkHeaderImports` admits it) while its
/// well-typed definition `Trusted.ForgedRef.x : Nat := Anneal.helper`
/// references the compiled `theory/` constant `Anneal.helper`. Only
/// `checkDeclarationEdges` can therefore reject it. Pass 1 audits the forged
/// module as `vetted` and Pass 2 as `candidate:mir_semantics`, covering both
/// tiers that the `.trusted _` pattern matches.
#[test]
fn rejects_forged_trusted_constant_referencing_theory() {
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

    // `Trusted.*` modules must share the search-path entry holding
    // `Trusted.olean`, so the forged module goes into the staged `lib/`.
    let stage = checker.stage().to_path_buf();
    let trusted_lib = stage.join("lib");
    let forged_module = "Trusted.ForgedRef";
    let forged_out = trusted_lib.join("Trusted/ForgedRef.olean");
    fs::create_dir_all(forged_out.parent().unwrap()).unwrap();
    run_lean_script(
        &mut checker,
        "gen-forged-ref",
        &stage.join("gen_forged_ref.lean"),
        &format!(
            "import Lean.Environment\n\
             open Lean\n\
             def main : IO Unit := do\n\
               let ci : ConstantInfo := .defnInfo {{\n\
                 name := `Trusted.ForgedRef.x\n\
                 levelParams := []\n\
                 type := .const `Nat []\n\
                 value := .const `Anneal.helper []\n\
                 hints := .abbrev\n\
                 safety := .safe\n\
                 all := [`Trusted.ForgedRef.x]\n\
               }}\n\
               let md : ModuleData := {{\n\
                 isModule := false\n\
                 imports := #[{{ module := `Init.Core }}]\n\
                 constNames := #[`Trusted.ForgedRef.x]\n\
                 constants := #[ci]\n\
                 extraConstNames := #[]\n\
                 entries := #[]\n\
               }}\n\
               saveModuleData (System.FilePath.mk {:?}) `Trusted.ForgedRef md\n",
            forged_out.to_string_lossy()
        ),
    );
    // Pass 1 loads modules from the admitted artifact map and compares their
    // headers with the admitted import graph.
    let core_edge = vec![ImportEdge {
        module: "Init.Core".to_string(),
        import_all: false,
        is_exported: true,
        is_meta: false,
    }];
    let arts = ModuleArtifacts::from_available(
        &BTreeMap::from([("olean", forged_out.to_string_lossy().into_owned())]),
        "test",
        String::new,
    )
    .unwrap();
    {
        let adm = checker.admitted_mut().unwrap();
        adm.graph.insert(forged_module.to_string(), core_edge);
        adm.artifacts.insert(forged_module.to_string(), arts);
    }

    let expected = "Trusted constant Trusted.ForgedRef.x references Anneal.helper \
                    from non-Trusted module Anneal";
    let err_audit = checker
        .inspect(InspectorRequest::Audit {
            trusted: vec!["Trusted".to_string(), forged_module.to_string()],
            theory: vec!["Anneal".to_string()],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                (forged_module.to_string(), TrustTier::Vetted),
            ]),
        })
        .unwrap_err();
    assert_eq!(err_audit.code, 1, "unexpected Pass 1 code: {err_audit}");
    assert_eq!(err_audit.phase, "audit", "unexpected Pass 1 phase: {err_audit}");
    assert!(err_audit.message.contains(expected), "unexpected Pass 1 error: {err_audit}");

    let err_corr = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: vec![trusted_lib, stage.join("theory-lib")],
            trusted: vec!["Trusted".to_string(), forged_module.to_string()],
            corr_trusted: Vec::new(),
            theory: vec!["Anneal".to_string()],
            corr_theory: Vec::new(),
            vendor_miri: Vec::new(),
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                (forged_module.to_string(), TrustTier::Candidate(CandidateFeature::MirSemantics)),
            ]),
        })
        .unwrap_err();
    assert_eq!(err_corr.code, 1, "unexpected Pass 2 code: {err_corr}");
    assert_eq!(err_corr.phase, "correspondence-audit", "unexpected Pass 2 phase: {err_corr}");
    assert!(err_corr.message.contains(expected), "unexpected Pass 2 error: {err_corr}");
}

/// Pass 2 `"preflight"` keeps `trusted/correspondence/` isolated from Pass 1
/// `theory/` modules. Pass 1 compiles the real `Trusted.MirAst`,
/// `Trusted.MirSemantics`, and `Anneal.MirWp` first, so `Anneal.MirWp` is an
/// admitted compiled artifact when Pass 2 starts; a `Trusted.Correspondence`
/// source importing it is still rejected before any Pass 2 module compiles.
#[test]
fn rejects_trusted_correspondence_import_of_theory_in_pass2_preflight() {
    let checkout = repo_root();
    let fix = TempFixture::new(None);
    copy_cargo_workspace(&fix.root);
    copy_dir_all(&checkout.join("vendor/lean-miri"), &fix.root.join("vendor/lean-miri")).unwrap();
    let (_, theory_manifest) = anneal_audit::bundle::load_theory_bundle_manifest(&checkout)
        .expect("checkout theory bundle manifest");
    for rel in anneal_audit::bundle::TRUSTED_BUNDLE_SOURCES
        .iter()
        .copied()
        .chain(std::iter::once(anneal_audit::bundle::THEORY_BUNDLE_MANIFEST))
        .chain(theory_manifest.modules.iter().map(|entry| entry.path.as_str()))
        .chain(std::iter::once("theory/Anneal/MirWp/Canaries.lean"))
    {
        let dst = fix.root.join(rel);
        fs::create_dir_all(dst.parent().unwrap()).unwrap();
        fs::copy(checkout.join(rel), dst).unwrap();
    }
    fs::write(
        fix.root.join("theory/Anneal.lean"),
        b"prelude\nimport Init.NotationExtra\nimport Trusted\nimport Anneal.MirWp\n",
    )
    .unwrap();
    for rel in anneal_audit::bundle::PROVENANCE_SOURCES {
        if rel.ends_with(".lean") {
            let dst = fix.root.join(rel);
            fs::create_dir_all(dst.parent().unwrap()).unwrap();
            let contents = if *rel == "trusted/correspondence/Trusted/Correspondence.lean" {
                "-- anneal-trust-tier: candidate:mir_semantics\n\
                 prelude\nimport Init.NotationExtra\nimport Anneal.MirWp\n"
            } else if rel.starts_with("trusted/correspondence/") {
                "-- anneal-trust-tier: candidate:mir_semantics\n\
                 prelude\nimport Init.NotationExtra\n"
            } else {
                "prelude\nimport Trusted.Correspondence\n"
            };
            fs::write(dst, contents.as_bytes()).unwrap();
        }
    }

    let mut checker = fix.checker();
    // Synthetic fixture overrides `trusted/correspondence/` and
    // `correspondence/` with 3-line stubs, so embedded-bundle parity is
    // disabled while `"audit"` still checks `Trusted.*` / `Anneal.MirWp`.
    checker.set_require_mir_wp(false);
    let err = checker.run().unwrap_err();
    assert_eq!(err.code, 1, "unexpected code: {err}");
    assert_eq!(err.phase, "preflight", "unexpected phase: {err}");
    assert!(
        err.message.contains("foreign/missing import Anneal.MirWp in Trusted.Correspondence"),
        "unexpected error: {err}"
    );
}

/// Pass 2 `"correspondence-audit"` independently rejects a compiled
/// `Trusted.Correspondence` whose `.olean` header imports the `theory/` module
/// `Anneal.MirWp`, even when the module was compiled without repository
/// `"preflight"` and references none of the imported constants (so only
/// `CorrOrigin.importViolation?` applies).
#[test]
fn rejects_trusted_correspondence_import_of_theory_in_correspondence_audit() {
    let fix = TempFixture::new(None);
    let mut checker = fix.checker();
    checker.set_require_mir_wp(false);
    checker.run().unwrap();

    let stage = checker.stage().to_path_buf();
    let src = stage.join("src/forged-corr");
    let trusted_lib = stage.join("lib");
    let corr_lib = stage.join("forged-corr-lib");
    let vendor_lib = stage.join("forged-vendor-lib");
    compile_forged_module(
        &mut checker,
        &stage.join("src/forged-vendor"),
        &vendor_lib,
        &[],
        "Miri.Forged",
        "prelude\nimport Init.Core\nnamespace Miri.Forged\ndef ok : Nat := 0\nend Miri.Forged\n",
    );
    compile_forged_module(
        &mut checker,
        &src,
        &corr_lib,
        &[],
        "Anneal.MirWp",
        "prelude\nimport Init.Core\nnamespace Anneal.MirWp\ndef wpProg : Nat := 0\nend Anneal.MirWp\n",
    );
    compile_forged_module(
        &mut checker,
        &src,
        &trusted_lib,
        &["Anneal.MirWp"],
        "Trusted.Correspondence",
        "prelude\nimport Init.Core\nimport Anneal.MirWp\nnamespace Trusted.Correspondence\ndef CorrespondenceClaim : Prop := True\nend Trusted.Correspondence\n",
    );
    compile_forged_module(
        &mut checker,
        &src,
        &corr_lib,
        &["Trusted.Correspondence"],
        "Anneal.MirCorrespondenceProof",
        "prelude\nimport Init.Core\nimport Trusted.Correspondence\n",
    );
    let err = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: vec![trusted_lib, vendor_lib, corr_lib],
            trusted: vec!["Trusted".to_string()],
            corr_trusted: vec!["Trusted.Correspondence".to_string()],
            theory: vec!["Anneal.MirWp".to_string()],
            corr_theory: vec!["Anneal.MirCorrespondenceProof".to_string()],
            vendor_miri: vec!["Miri.Forged".to_string()],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                (
                    "Trusted.Correspondence".to_string(),
                    TrustTier::parse("candidate:mir_semantics").unwrap(),
                ),
            ]),
        })
        .unwrap_err();
    assert_eq!(err.code, 1, "unexpected code: {err}");
    assert_eq!(err.phase, "correspondence-audit", "unexpected phase: {err}");
    assert!(
        err.message.contains(
            "Trusted module Trusted.Correspondence cannot import non-Trusted module Anneal.MirWp"
        ),
        "unexpected error: {err}"
    );
}

/// Pass 2 `"correspondence-audit"` kernel-replays correspondence declarations:
/// a forged `Anneal.MirCorrespondenceProof.olean` holding the ill-typed theorem
/// `Anneal.MirCorrespondenceProof.bogus : False := True.intro` is rejected
/// with operational exit code `2` and `"correspondence kernel replay failed"`.
///
/// `Lean.saveModuleData` writes the theorem without elaborating or
/// kernel-checking it, and the theorem passes every inventory, origin, and
/// edge check, so only the correspondence replay in `replayCorrAndVendor`
/// rejects it. If that replay were skipped, a later Pass 2 policy check would
/// reject this fixture with exit code `1` instead.
#[test]
fn rejects_forged_ill_typed_correspondence_declaration_during_replay() {
    let fix = TempFixture::new(None);
    let mut checker = fix.checker();
    checker.set_require_mir_wp(false);
    checker.run().unwrap();

    let stage = checker.stage().to_path_buf();
    let corr_lib = stage.join("forged-corr-lib");
    let forged_out = corr_lib.join("Anneal/MirCorrespondenceProof.olean");
    fs::create_dir_all(forged_out.parent().unwrap()).unwrap();
    run_lean_script(
        &mut checker,
        "gen-bogus-corr-proof",
        &stage.join("gen_bogus_corr_proof.lean"),
        &format!(
            "import Lean.Environment\n\
             open Lean\n\
             def main : IO Unit := do\n\
               let ci : ConstantInfo := .thmInfo {{\n\
                 name := `Anneal.MirCorrespondenceProof.bogus\n\
                 levelParams := []\n\
                 type := .const `False []\n\
                 value := .const `True.intro []\n\
                 all := [`Anneal.MirCorrespondenceProof.bogus]\n\
               }}\n\
               let md : ModuleData := {{\n\
                 isModule := false\n\
                 imports := #[{{ module := `Init.Core }}]\n\
                 constNames := #[`Anneal.MirCorrespondenceProof.bogus]\n\
                 constants := #[ci]\n\
                 extraConstNames := #[]\n\
                 entries := #[]\n\
               }}\n\
               saveModuleData (System.FilePath.mk {:?}) `Anneal.MirCorrespondenceProof md\n",
            forged_out.to_string_lossy()
        ),
    );

    let err = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: vec![stage.join("lib"), corr_lib],
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: vec!["Anneal.MirCorrespondenceProof".to_string()],
            vendor_miri: Vec::new(),
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    // Kernel replay exceptions are operational errors (exit code `2`) so no
    // stringified `Kernel.Exception` can spoof `"policy:"`.
    assert_eq!(
        err.code, 2,
        "expected operational exit code 2 on correspondence replay failure: {err}"
    );
    assert_eq!(err.phase, "correspondence-audit", "unexpected phase: {err}");
    assert!(
        err.message.contains("correspondence kernel replay failed")
            && err.message.contains("Anneal.MirCorrespondenceProof.bogus")
            && err.message.contains("declaration type mismatch"),
        "expected correspondence kernel replay rejection, got: {err}"
    );
}
