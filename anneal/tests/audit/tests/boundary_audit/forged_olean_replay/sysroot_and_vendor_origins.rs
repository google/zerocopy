// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Sections 9 through 11: forged `.vendorMiri` constructors and
//! `.sysrootFoundation` provenance and `extraConstNames`.

use super::*;

/// Runs sections 9 through 11 and returns the checker.
pub(super) fn rejects_forged_vendor_and_sysroot_origins(
    mut checker: Checker,
    stage: PathBuf,
    lib_dir: PathBuf,
) -> Checker {
    // 9. `.vendorMiri` forged `.ctorInfo` with `induct := .anonymous` reaches
    //    `validateReplayMap` via `replayCorrAndVendor` and fails closed.
    // 10. `.sysrootFoundation` module whose constant resolves provenance to
    //     `.vendorMiri` fails `.sysrootFoundation`
    //     `inventory origin mismatch`.
    let p2_ctor_sysroot_lib = stage.join("p2-ctor-sysroot-lib");
    let miri_anon_ctor_olean = p2_ctor_sysroot_lib.join("Miri/AnonCtorInd.olean");
    let miri_dup_olean = p2_ctor_sysroot_lib.join("Miri/DupOrig.olean");
    let sysroot_dup_olean = p2_ctor_sysroot_lib.join("Sysroot/DupOrig.olean");
    let dup_driver_olean = p2_ctor_sysroot_lib.join("Anneal/DupDriver.olean");
    fs::create_dir_all(miri_anon_ctor_olean.parent().unwrap()).unwrap();
    fs::create_dir_all(sysroot_dup_olean.parent().unwrap()).unwrap();
    fs::create_dir_all(dup_driver_olean.parent().unwrap()).unwrap();
    run_lean_script(
        &mut checker,
        "forge-pass2-ctor-and-sysroot-origin",
        &stage.join("forge_pass2_ctor_and_sysroot_origin.lean"),
        &format!(
            "import Lean\nopen Lean in\n\
             def main : IO Unit := do\n  \
               let imp := #[{{ module := `Init.Core : Import }}]\n  \
               let anonCtor : ConstantInfo := .ctorInfo {{\n    \
                 name := `Miri.AnonCtorInd.mk, levelParams := [],\n    \
                 type := .const `True [], induct := .anonymous, cidx := 0,\n    \
                 numParams := 0, numFields := 0, isUnsafe := false }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Miri.AnonCtorInd {{\n    \
                 isModule := false, imports := imp,\n    \
                 constNames := #[`Miri.AnonCtorInd.mk], constants := #[anonCtor],\n    \
                 extraConstNames := #[], entries := #[] }}\n  \
               let dupThm : ConstantInfo := .thmInfo {{\n    \
                 name := `External.Dup.t, levelParams := [],\n    \
                 type := .const `True [], value := .const `True.intro [],\n    \
                 all := [`External.Dup.t] }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Miri.DupOrig {{\n    \
                 isModule := false, imports := imp,\n    \
                 constNames := #[`External.Dup.t], constants := #[dupThm],\n    \
                 extraConstNames := #[], entries := #[] }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Sysroot.DupOrig {{\n    \
                 isModule := false, imports := imp,\n    \
                 constNames := #[`External.Dup.t], constants := #[dupThm],\n    \
                 extraConstNames := #[], entries := #[] }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Anneal.DupDriver {{\n    \
                 isModule := false,\n    \
                 imports := #[{{ module := `Miri.DupOrig }}, {{ module := `Sysroot.DupOrig }}],\n    \
                 constNames := #[], constants := #[],\n    \
                 extraConstNames := #[], entries := #[] }}\n",
            miri_anon_ctor_olean.to_string_lossy(),
            miri_dup_olean.to_string_lossy(),
            sysroot_dup_olean.to_string_lossy(),
            dup_driver_olean.to_string_lossy()
        ),
    );
    let anon_ctor_err = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: vec![lib_dir.clone(), p2_ctor_sysroot_lib.clone()],
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.AnonCtorInd".to_string()],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert_eq!(
        (anon_ctor_err.code, anon_ctor_err.phase.as_str()),
        (1, "correspondence-audit"),
        "{anon_ctor_err}"
    );
    assert!(
        anon_ctor_err.message.contains("anonymous inductive on constructor Miri.AnonCtorInd.mk"),
        "expected anonymous inductive rejection, got: {anon_ctor_err}"
    );

    let orig_sysroot = checker.ensure_sysroot_foundation().unwrap().to_vec();
    let mut sysroot_with_dup = orig_sysroot.clone();
    sysroot_with_dup.push("Sysroot.DupOrig".to_string());
    checker.set_sysroot_foundation_for_test(sysroot_with_dup).unwrap();
    let sysroot_origin_err = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: vec![lib_dir.clone(), p2_ctor_sysroot_lib],
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: vec!["Anneal.DupDriver".to_string()],
            corr_theory: Vec::new(),
            vendor_miri: vec!["Miri.DupOrig".to_string()],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    checker.set_sysroot_foundation_for_test(orig_sysroot.clone()).unwrap();
    assert_eq!(
        (sysroot_origin_err.code, sysroot_origin_err.phase.as_str()),
        (1, "correspondence-audit"),
        "{sysroot_origin_err}"
    );
    assert!(
        sysroot_origin_err.message.contains("inventory origin mismatch External.Dup.t"),
        "expected .sysrootFoundation origin mismatch, got: {sysroot_origin_err}"
    );

    // 11. `.sysrootFoundation` `extraConstNames` naming a helper owned by an
    //     earlier `.repo` module fails closed with
    //     `IR helper provenance mismatch`.
    let p2_sysroot_ir_lib = stage.join("p2-sysroot-ir-lib");
    let repo_ir_owner_olean = p2_sysroot_ir_lib.join("Anneal/IrOwner.olean");
    let sysroot_ir_leak_olean = p2_sysroot_ir_lib.join("Sysroot/IrLeak.olean");
    let ir_driver_olean = p2_sysroot_ir_lib.join("Anneal/IrDriver.olean");
    fs::create_dir_all(repo_ir_owner_olean.parent().unwrap()).unwrap();
    fs::create_dir_all(sysroot_ir_leak_olean.parent().unwrap()).unwrap();
    run_lean_script(
        &mut checker,
        "forge-pass2-sysroot-ir-provenance",
        &stage.join("forge_pass2_sysroot_ir_provenance.lean"),
        &format!(
            "import Lean\nopen Lean in\n\
             def main : IO Unit := do\n  \
               let imp := #[{{ module := `Init.Core : Import }}]\n  \
               let helperThm : ConstantInfo := .thmInfo {{\n    \
                 name := `External.IrHelper.h, levelParams := [],\n    \
                 type := .const `True [], value := .const `True.intro [],\n    \
                 all := [`External.IrHelper.h] }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Anneal.IrOwner {{\n    \
                 isModule := false, imports := imp,\n    \
                 constNames := #[`External.IrHelper.h], constants := #[helperThm],\n    \
                 extraConstNames := #[], entries := #[] }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Sysroot.IrLeak {{\n    \
                 isModule := false, imports := imp,\n    \
                 constNames := #[], constants := #[],\n    \
                 extraConstNames := #[`External.IrHelper.h], entries := #[] }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Anneal.IrDriver {{\n    \
                 isModule := false,\n    \
                 imports := #[{{ module := `Anneal.IrOwner }}, {{ module := `Sysroot.IrLeak }}],\n    \
                 constNames := #[], constants := #[],\n    \
                 extraConstNames := #[], entries := #[] }}\n",
            repo_ir_owner_olean.to_string_lossy(),
            sysroot_ir_leak_olean.to_string_lossy(),
            ir_driver_olean.to_string_lossy()
        ),
    );
    let mut sysroot_with_ir = orig_sysroot.clone();
    sysroot_with_ir.push("Sysroot.IrLeak".to_string());
    checker.set_sysroot_foundation_for_test(sysroot_with_ir).unwrap();
    let ir_prov_err = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: vec![lib_dir, p2_sysroot_ir_lib],
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: vec!["Anneal.IrDriver".to_string(), "Anneal.IrOwner".to_string()],
            corr_theory: Vec::new(),
            vendor_miri: Vec::new(),
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    checker.set_sysroot_foundation_for_test(orig_sysroot).unwrap();
    assert_eq!(
        (ir_prov_err.code, ir_prov_err.phase.as_str()),
        (1, "correspondence-audit"),
        "{ir_prov_err}"
    );
    assert!(
        ir_prov_err.message.contains("IR helper provenance mismatch External.IrHelper.h"),
        "expected .sysrootFoundation IR helper provenance mismatch, got: {ir_prov_err}"
    );
    checker
}
