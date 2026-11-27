// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Pass 2 correspondence entry modules, external and foreign imports,
//! import cycles, and Pass 1 and Pass 2 module-name overlap.

use super::*;

/// Verifies `Checker::run` rejects correspondence setups that are missing the
/// required `Trusted/Correspondence.lean` umbrella or
/// `Anneal/MirCorrespondenceProof.lean` entry module with policy exit code `1`.
#[test]
fn rejects_missing_correspondence_entry_modules() {
    let checkout = repo_root();
    let fix = TempFixture::new(None);
    copy_cargo_workspace(&fix.root);
    copy_dir_all(&checkout.join("vendor/lean-miri"), &fix.root.join("vendor/lean-miri")).unwrap();
    fs::create_dir_all(fix.root.join("trusted/correspondence/Trusted")).unwrap();
    fs::create_dir_all(fix.root.join("correspondence/Anneal")).unwrap();

    // 1. Missing `Trusted/Correspondence.lean` umbrella.
    fs::write(
        fix.root.join("trusted/correspondence/Trusted/Other.lean"),
        b"-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.NotationExtra\n",
    )
    .unwrap();
    fs::write(
        fix.root.join("correspondence/Anneal/MirCorrespondenceProof.lean"),
        b"prelude\nimport Init.NotationExtra\n",
    )
    .unwrap();
    let mut checker1 = fix.checker();
    checker1.set_require_mir_wp(false);
    let err_missing_corr = checker1.run().unwrap_err();
    assert_eq!(err_missing_corr.code, 1);
    assert_eq!(err_missing_corr.phase, "snapshot");
    assert!(
        err_missing_corr
            .message
            .contains("missing Trusted/Correspondence.lean umbrella in trusted/correspondence"),
        "unexpected missing Trusted.Correspondence error: {err_missing_corr}"
    );

    // 2. Missing `Anneal/MirCorrespondenceProof.lean`.
    fs::write(
        fix.root.join("trusted/correspondence/Trusted/Correspondence.lean"),
        b"-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.NotationExtra\n",
    )
    .unwrap();
    fs::remove_file(fix.root.join("correspondence/Anneal/MirCorrespondenceProof.lean")).unwrap();
    fs::write(
        fix.root.join("correspondence/Anneal/Other.lean"),
        b"prelude\nimport Init.NotationExtra\n",
    )
    .unwrap();
    let mut checker2 = fix.checker();
    checker2.set_require_mir_wp(false);
    let err_missing_proof = checker2.run().unwrap_err();
    assert_eq!(err_missing_proof.code, 1);
    assert_eq!(err_missing_proof.phase, "snapshot");
    assert!(
        err_missing_proof
            .message
            .contains("missing Anneal/MirCorrespondenceProof.lean in correspondence"),
        "unexpected missing Anneal.MirCorrespondenceProof error: {err_missing_proof}"
    );
}

/// Verifies every external-origin branch of `CorrOrigin.importViolation?`
/// (`.vendorMiri -> .repo`, `.sysrootFoundation -> .vendorMiri/.repo`,
/// `.foundation -> .vendorMiri/.repo`) and `checkHeaderImports`'s defensive
/// `"foreign import"` rejection with policy exit code `1`.
#[test]
fn rejects_external_origin_header_imports_and_foreign_imports() {
    let fix = TempFixture::new(None);
    let mut checker = fix.checker();
    checker.set_require_mir_wp(false);
    checker.run().unwrap();

    let stage = checker.stage().to_path_buf();
    let trusted_lib = stage.join("lib");
    let ext_src = stage.join("src/ext-imp");
    let ext_path = env::join_paths([&trusted_lib]).unwrap();

    let compile_ext = |chk: &mut Checker, module: &str, body: &str| {
        let rel = module.replace('.', "/");
        let src = ext_src.join(format!("{rel}.lean"));
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
                ext_src.to_string_lossy().into_owned(),
                "-o".to_string(),
                out.to_string_lossy().into_owned(),
                src.to_string_lossy().into_owned(),
            ],
            Some(&ext_path),
        )
        .unwrap();
    };

    compile_ext(
        &mut checker,
        "Miri.Child",
        "prelude\nimport Init.Core\nnamespace Miri.Child\ndef c : Nat := 1\nend Miri.Child\n",
    );
    compile_ext(
        &mut checker,
        "Miri.ImpTrusted",
        "prelude\nimport Init.Core\nimport Trusted\nnamespace Miri.ImpTrusted\ndef x : Nat := 0\nend Miri.ImpTrusted\n",
    );
    compile_ext(
        &mut checker,
        "FakeSysrootMiri",
        "prelude\nimport Init.Core\nimport Miri.Child\nnamespace FakeSysrootMiri\ndef x : Nat := 0\nend FakeSysrootMiri\n",
    );
    compile_ext(
        &mut checker,
        "Miri.UsesFakeSysrootMiri",
        "prelude\nimport Init.Core\nimport FakeSysrootMiri\nnamespace Miri.UsesFakeSysrootMiri\ndef x : Nat := 0\nend Miri.UsesFakeSysrootMiri\n",
    );
    compile_ext(
        &mut checker,
        "FakeSysrootRepo",
        "prelude\nimport Init.Core\nimport Trusted\nnamespace FakeSysrootRepo\ndef x : Nat := 0\nend FakeSysrootRepo\n",
    );
    compile_ext(
        &mut checker,
        "Miri.UsesFakeSysrootRepo",
        "prelude\nimport Init.Core\nimport FakeSysrootRepo\nnamespace Miri.UsesFakeSysrootRepo\ndef x : Nat := 0\nend Miri.UsesFakeSysrootRepo\n",
    );
    compile_ext(
        &mut checker,
        "FakeFoundMiri",
        "prelude\nimport Init.Core\nimport Miri.Child\nnamespace FakeFoundMiri\ndef x : Nat := 0\nend FakeFoundMiri\n",
    );
    compile_ext(
        &mut checker,
        "FakeFoundRepo",
        "prelude\nimport Init.Core\nimport Trusted\nnamespace FakeFoundRepo\ndef x : Nat := 0\nend FakeFoundRepo\n",
    );

    let search = vec![trusted_lib.clone()];

    // 1. `.vendorMiri` importing `.repo` (`Trusted`).
    let err_miri_repo = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.ImpTrusted".to_string()],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert_eq!(err_miri_repo.code, 1);
    assert!(
        err_miri_repo.message.contains("vendor Miri module Miri.ImpTrusted cannot import Trusted"),
        "unexpected vendor->repo error: {err_miri_repo}"
    );

    // 2. `.sysrootFoundation` importing `.vendorMiri`.
    checker
        .set_sysroot_foundation_for_test(vec![
            "FakeSysrootMiri".to_string(),
            "FakeSysrootRepo".to_string(),
        ])
        .unwrap();
    let err_sys_miri = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string(), "Miri.UsesFakeSysrootMiri".to_string()],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert_eq!(err_sys_miri.code, 1);
    assert!(
        err_sys_miri.message.contains("sysroot module FakeSysrootMiri cannot import Miri.Child"),
        "unexpected sysroot->vendor error: {err_sys_miri}"
    );

    // 3. `.sysrootFoundation` importing `.repo` (`Trusted`).
    let err_sys_repo = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.UsesFakeSysrootRepo".to_string()],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert_eq!(err_sys_repo.code, 1);
    assert!(
        err_sys_repo.message.contains("sysroot module FakeSysrootRepo cannot import Trusted"),
        "unexpected sysroot->repo error: {err_sys_repo}"
    );

    // 4. `.foundation` importing `.vendorMiri`.
    checker
        .admitted_mut()
        .unwrap()
        .foundation_graph
        .insert("FakeFoundMiri".to_string(), Vec::new());
    let err_found_miri = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search.clone(),
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert_eq!(err_found_miri.code, 1);
    assert!(
        err_found_miri.message.contains("foundation module FakeFoundMiri cannot import Miri.Child"),
        "unexpected foundation->vendor error: {err_found_miri}"
    );
    checker.admitted_mut().unwrap().foundation_graph.remove("FakeFoundMiri");

    // 5. `.foundation` importing `.repo` (`Trusted`).
    checker
        .admitted_mut()
        .unwrap()
        .foundation_graph
        .insert("FakeFoundRepo".to_string(), Vec::new());
    let err_found_repo = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: search,
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.Child".to_string()],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert_eq!(err_found_repo.code, 1);
    assert!(
        err_found_repo.message.contains("foundation module FakeFoundRepo cannot import Trusted"),
        "unexpected foundation->repo error: {err_found_repo}"
    );

    // 6. `checkHeaderImports` defensive `"foreign import"` rejection on a
    // `ModuleData` whose header imports a module absent from `roles`.
    let inspector_path = checker.admitted().unwrap().inspector.clone();
    let tb_lib = stage.join("tb-lib");
    fs::create_dir_all(&tb_lib).unwrap();
    let tb_olean = tb_lib.join("TrustedBoundary.olean");
    checker
        .process(
            "compile-TrustedBoundary",
            &[
                "-j1".to_string(),
                "-M4096".to_string(),
                "-t0".to_string(),
                "-R".to_string(),
                inspector_path.parent().unwrap().to_string_lossy().into_owned(),
                "-o".to_string(),
                tb_olean.to_string_lossy().into_owned(),
                inspector_path.to_string_lossy().into_owned(),
            ],
        )
        .unwrap();
    let driver = stage.join("check_foreign_import.lean");
    fs::write(
        &driver,
        "import TrustedBoundary\n\
         open TrustedBoundary\n\
         #eval show IO Unit from do\n\
           let roles : Std.HashMap Lean.Name RepoOrigin := {}\n\
           let md : Lean.ModuleData := {\n\
             isModule := false\n\
             imports := #[{ module := `Unlisted.Ghost }]\n\
             constNames := #[]\n\
             constants := #[]\n\
             extraConstNames := #[]\n\
             entries := #[]\n\
           }\n\
           checkHeaderImports roles `Trusted.Forged (.repo (.trusted .vetted)) \
             md RepoOrigin.importViolation?\n",
    )
    .unwrap();
    let tb_path = env::join_paths([&tb_lib]).unwrap();
    let err_foreign_imp = checker
        .process_with_path(
            "check-foreign-import",
            &["-j1".to_string(), "-M4096".to_string(), driver.to_string_lossy().into_owned()],
            Some(&tb_path),
        )
        .unwrap_err();
    assert!(
        err_foreign_imp.message.contains("policy:foreign import Unlisted.Ghost in Trusted.Forged"),
        "expected checkHeaderImports foreign-import rejection, got: {err_foreign_imp}"
    );

    // 7. `requireClaimProof` rejects an empty `reqConsts` list at runtime
    // with policy exit code `1`.
    let driver_req = stage.join("check_empty_req_consts.lean");
    fs::write(
        &driver_req,
        "import TrustedBoundary\n\
         open TrustedBoundary\n\
         #eval show IO Unit from do\n\
           let env ← Lean.mkEmptyEnvironment\n\
           let locals : Std.HashMap Lean.Name Lean.ConstantInfo := {}\n\
           requireClaimProof env locals `Trusted.Correspondence \
             `Anneal.MirCorrespondenceProof `Trusted.Correspondence.EmptyReq \
             none `Anneal.MirCorrespondenceProof.empty_req []\n",
    )
    .unwrap();
    let err_empty_req = checker
        .process_with_path(
            "check-empty-req-consts",
            &["-j1".to_string(), "-M4096".to_string(), driver_req.to_string_lossy().into_owned()],
            Some(&tb_path),
        )
        .unwrap_err();
    assert!(
        err_empty_req.message.contains(
            "policy:claim Trusted.Correspondence.EmptyReq requires a non-empty required-constants list"
        ),
        "expected requireClaimProof empty reqConsts rejection, got: {err_empty_req}"
    );
}

/// Verifies Pass 2 preflight rejects import cycles in both
/// `trusted/correspondence/` (`"Trusted correspondence import cycle"`) and
/// `correspondence/` (`"Correspondence proof import cycle"`) with policy exit
/// code `1` before compiling Miri or any Pass 2 module.
#[test]
fn rejects_pass2_correspondence_import_cycles() {
    let checkout = repo_root();
    let fix = TempFixture::new(None);
    copy_cargo_workspace(&fix.root);
    copy_dir_all(&checkout.join("vendor/lean-miri"), &fix.root.join("vendor/lean-miri")).unwrap();
    fs::create_dir_all(fix.root.join("trusted/correspondence/Trusted")).unwrap();
    fs::create_dir_all(fix.root.join("correspondence/Anneal")).unwrap();

    // 1. Import cycle inside `trusted/correspondence/`.
    fs::write(
        fix.root.join("trusted/correspondence/Trusted/Correspondence.lean"),
        b"-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.NotationExtra\n",
    )
    .unwrap();
    fs::write(
        fix.root.join("trusted/correspondence/Trusted/CycleA.lean"),
        b"-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.NotationExtra\nimport Trusted.CycleB\n",
    )
    .unwrap();
    fs::write(
        fix.root.join("trusted/correspondence/Trusted/CycleB.lean"),
        b"-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.NotationExtra\nimport Trusted.CycleA\n",
    )
    .unwrap();
    fs::write(
        fix.root.join("correspondence/Anneal/MirCorrespondenceProof.lean"),
        b"prelude\nimport Trusted.Correspondence\n",
    )
    .unwrap();

    let mut checker1 = fix.checker();
    checker1.set_require_mir_wp(false);
    let err_trusted_cycle = checker1.run().unwrap_err();
    assert_eq!(err_trusted_cycle.code, 1);
    assert_eq!(err_trusted_cycle.phase, "preflight");
    assert!(
        err_trusted_cycle.message.contains("Trusted correspondence import cycle"),
        "unexpected trusted-correspondence cycle error: {err_trusted_cycle}"
    );

    // 2. Import cycle inside `correspondence/`.
    fs::remove_file(fix.root.join("trusted/correspondence/Trusted/CycleA.lean")).unwrap();
    fs::remove_file(fix.root.join("trusted/correspondence/Trusted/CycleB.lean")).unwrap();
    fs::write(
        fix.root.join("correspondence/Anneal/CycleA.lean"),
        b"prelude\nimport Init.NotationExtra\nimport Anneal.CycleB\n",
    )
    .unwrap();
    fs::write(
        fix.root.join("correspondence/Anneal/CycleB.lean"),
        b"prelude\nimport Init.NotationExtra\nimport Anneal.CycleA\n",
    )
    .unwrap();

    let mut checker2 = fix.checker();
    checker2.set_require_mir_wp(false);
    let err_theory_cycle = checker2.run().unwrap_err();
    assert_eq!(err_theory_cycle.code, 1);
    assert_eq!(err_theory_cycle.phase, "preflight");
    assert!(
        err_theory_cycle.message.contains("Correspondence proof import cycle"),
        "unexpected correspondence-proof cycle error: {err_theory_cycle}"
    );
}

/// Verifies that Pass 2 `"correspondence-audit"` fails closed when a compiled
/// correspondence module imports a Pass 1 `theory/` module omitted from
/// `CorrespondenceAudit.theory` (the transitive import closure of
/// `correspondence/`).
#[test]
fn rejects_unadmitted_pass1_theory_import_in_correspondence_audit() {
    let fix = TempFixture::new(None);
    fs::create_dir_all(fix.root.join("theory/Anneal")).unwrap();
    fs::write(
        fix.root.join("theory/Anneal/Unimported.lean"),
        "prelude\nimport Init.Core\nnamespace Anneal.Unimported\ndef hidden : Nat := 7\nend Anneal.Unimported\n",
    )
    .unwrap();
    fs::write(
        fix.root.join("theory/Anneal.lean"),
        "prelude\nimport Init.Core\nimport Anneal.Unimported\n",
    )
    .unwrap();

    let mut checker = fix.checker();
    checker.set_require_mir_wp(false);
    checker.run().unwrap();

    let stage = checker.stage().to_path_buf();
    let src = stage.join("src/forged-unimported");
    let theory_lib = stage.join("theory-lib");
    compile_forged_module(
        &mut checker,
        &src,
        &theory_lib,
        &["Anneal.Unimported"],
        "Anneal.MirCorrespondenceProof",
        "prelude\nimport Init.Core\nimport Anneal.Unimported\nnamespace Anneal.MirCorrespondenceProof\ndef leak : Nat := Anneal.Unimported.hidden\nend Anneal.MirCorrespondenceProof\n",
    );

    let err = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: vec![stage.join("lib"), theory_lib],
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: vec!["Anneal.MirCorrespondenceProof".to_string()],
            vendor_miri: Vec::new(),
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert_eq!(err.code, 1, "expected policy rejection: {err}");
    assert_eq!(err.phase, "correspondence-audit", "unexpected phase: {err}");
    assert!(
        err.message.contains("foreign module Anneal.Unimported in correspondence environment"),
        "unexpected error: {err}"
    );
}

/// Verifies that [`Checker::run_correspondence_with_closure`] rejects Pass 2
/// modules whose names collide with Pass 1 `theory/` or `trusted/lean/`
/// modules (`code == 1`, `phase == "snapshot"`) before Pass 2 preflight or
/// compilation can touch `<stage>/lib` or `<stage>/theory-lib`.
#[test]
fn rejects_overlapping_pass1_and_pass2_module_names() {
    // Case 1: Pass 1 `theory/Anneal/MirCorrespondenceProof.lean` collides with
    // Pass 2 `correspondence/Anneal/MirCorrespondenceProof.lean`.
    {
        let fix = TempFixture::new(None);
        fs::create_dir_all(fix.root.join("theory/Anneal")).unwrap();
        fs::write(
            fix.root.join("theory/Anneal/MirCorrespondenceProof.lean"),
            "prelude\nimport Init.Core\nnamespace Anneal.MirCorrespondenceProof\ndef decoy : Nat := 1\nend Anneal.MirCorrespondenceProof\n",
        )
        .unwrap();
        fs::write(
            fix.root.join("theory/Anneal.lean"),
            "prelude\nimport Init.Core\nimport Anneal.MirCorrespondenceProof\n",
        )
        .unwrap();

        let mut checker = fix.checker();
        checker.set_require_mir_wp(false);
        checker.run().unwrap();
        let pass1_olean = checker.stage().join("theory-lib/Anneal/MirCorrespondenceProof.olean");
        let pass1_sha = sha256_file(&pass1_olean, "test").unwrap();

        let vendor_dir = fix.root.join("synthetic-miri");
        fs::create_dir_all(&vendor_dir).unwrap();
        let corr_trusted = fix.root.join("trusted/correspondence/Trusted/Correspondence.lean");
        let corr_proof = fix.root.join("correspondence/Anneal/MirCorrespondenceProof.lean");
        fs::create_dir_all(corr_trusted.parent().unwrap()).unwrap();
        fs::create_dir_all(corr_proof.parent().unwrap()).unwrap();
        fs::write(
            &corr_trusted,
            "-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.Core\nnamespace Trusted.Correspondence\ndef ok : Nat := 0\nend Trusted.Correspondence\n",
        )
        .unwrap();
        fs::write(
            &corr_proof,
            "prelude\nimport Init.Core\nimport Trusted.Correspondence\nnamespace Anneal.MirCorrespondenceProof\ndef real : Nat := Trusted.Correspondence.ok\nend Anneal.MirCorrespondenceProof\n",
        )
        .unwrap();

        let base_tiers = BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]);
        let err = checker
            .run_correspondence_with_closure(
                &base_tiers,
                &vendor_dir,
                "synthetic-commit",
                &[],
                &BTreeMap::new(),
            )
            .unwrap_err();
        assert_eq!(err.code, 1, "expected policy exit 1: {err}");
        assert_eq!(err.phase, "snapshot", "expected snapshot rejection: {err}");
        assert!(
            err.message.contains("overlapping module role for Anneal.MirCorrespondenceProof"),
            "unexpected error: {err}"
        );
        assert_eq!(
            sha256_file(&pass1_olean, "test").unwrap(),
            pass1_sha,
            "Pass 1 theory .olean must not be overwritten on collision"
        );
        assert!(
            !checker.stage().join("lib/Trusted/Correspondence.olean").exists(),
            "Pass 2 Trusted.Correspondence must not compile on collision"
        );
    }

    // Case 2: Pass 1 `trusted/lean/Trusted/Correspondence.lean` collides with
    // Pass 2 `trusted/correspondence/Trusted/Correspondence.lean`.
    {
        let fix = TempFixture::new(None);
        fs::create_dir_all(fix.root.join("trusted/lean/Trusted")).unwrap();
        fs::write(
            fix.root.join("trusted/lean/Trusted/Correspondence.lean"),
            "-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.Core\nnamespace Trusted.Correspondence\ndef decoy : Nat := 2\nend Trusted.Correspondence\n",
        )
        .unwrap();
        fs::create_dir_all(fix.root.join("theory/Anneal")).unwrap();
        fs::write(
            fix.root.join("theory/Anneal.lean"),
            "prelude\nimport Init.Core\nimport Trusted.Correspondence\ndef reach : Nat := Trusted.Correspondence.decoy\n",
        )
        .unwrap();

        let mut checker = fix.checker();
        checker.set_require_mir_wp(false);
        checker.run().unwrap();
        let pass1_olean = checker.stage().join("lib/Trusted/Correspondence.olean");
        let pass1_sha = sha256_file(&pass1_olean, "test").unwrap();

        let vendor_dir = fix.root.join("synthetic-miri");
        fs::create_dir_all(&vendor_dir).unwrap();
        let corr_trusted = fix.root.join("trusted/correspondence/Trusted/Correspondence.lean");
        let corr_proof = fix.root.join("correspondence/Anneal/MirCorrespondenceProof.lean");
        fs::create_dir_all(corr_trusted.parent().unwrap()).unwrap();
        fs::create_dir_all(corr_proof.parent().unwrap()).unwrap();
        fs::write(
            &corr_trusted,
            "-- anneal-trust-tier: candidate:mir_semantics\nprelude\nimport Init.Core\nnamespace Trusted.Correspondence\ndef real : Nat := 0\nend Trusted.Correspondence\n",
        )
        .unwrap();
        fs::write(
            &corr_proof,
            "prelude\nimport Init.Core\nimport Trusted.Correspondence\nnamespace Anneal.MirCorrespondenceProof\ndef ok : Nat := Trusted.Correspondence.real\nend Anneal.MirCorrespondenceProof\n",
        )
        .unwrap();

        let base_tiers = BTreeMap::from([
            ("Trusted".to_string(), TrustTier::Vetted),
            (
                "Trusted.Correspondence".to_string(),
                TrustTier::parse("candidate:mir_semantics").unwrap(),
            ),
        ]);
        let err = checker
            .run_correspondence_with_closure(
                &base_tiers,
                &vendor_dir,
                "synthetic-commit",
                &[],
                &BTreeMap::new(),
            )
            .unwrap_err();
        assert_eq!(err.code, 1, "expected policy exit 1: {err}");
        assert_eq!(err.phase, "snapshot", "expected snapshot rejection: {err}");
        assert!(
            err.message.contains("overlapping module role for Trusted.Correspondence"),
            "unexpected error: {err}"
        );
        assert_eq!(
            sha256_file(&pass1_olean, "test").unwrap(),
            pass1_sha,
            "Pass 1 trusted .olean must not be overwritten on collision"
        );
    }
}
