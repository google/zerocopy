// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Uninventoried libraries, extra source helpers, and `sorry`-allowing
//! alternate proofs during replay.

use super::*;

/// Verifies `targetAudit` admission guards on uninventoried library and
/// source `extraConstNames` declarations using never-reached theorems so
/// downstream reach-time checks cannot mask regressions.
#[test]
fn target_audit_rejects_uninventoried_library_and_source_extra_helpers() {
    use std::collections::BTreeMap;

    use anneal_audit::{ImportEdge, ModuleArtifacts};

    let f_src = Fixture::new(PROOF);
    let mut c_src = f_src.accepted_checker();
    let adm_src = c_src.admitted().unwrap();
    let dep_src = adm_src.foundation_modules().into_iter().next().unwrap().to_owned();
    let lib_src_olean = c_src.stage().join("lib/LibSrc.olean");
    let cap_src_olean = c_src.stage().join("lib/Captured.olean");
    let forge_src = c_src.stage().join("ForgeSourceUninventoriedLib.lean");
    run_lean_script(
        &mut c_src,
        "forge-source-uninventoried-lib",
        &forge_src,
        &format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               let libMd : ModuleData := {{\n    \
                 isModule := false, imports := #[{{ module := `{dep_src} }}],\n    \
                 constNames := #[], constants := #[],\n    \
                 extraConstNames := #[`LibSrc.uninv], entries := #[] }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `LibSrc libMd\n  \
               let capPath := System.FilePath.mk {:?}\n  \
               let (capData, _) ← readModuleData capPath\n  \
               let uninvThm : ConstantInfo := .thmInfo {{\n    \
                 name := `LibSrc.uninv, levelParams := [],\n    \
                 type := .const `True [], value := .const `True.intro [],\n    \
                 all := [`LibSrc.uninv] }}\n  \
               saveModuleData capPath `Captured {{ capData with\n    \
                 imports := capData.imports.push {{ module := `LibSrc }},\n    \
                 constNames := capData.constNames.push `LibSrc.uninv,\n    \
                 constants := capData.constants.push uninvThm }}\n",
            lib_src_olean.to_string_lossy(),
            cap_src_olean.to_string_lossy(),
        ),
    );
    let lib_src_avail = BTreeMap::from([("olean", lib_src_olean.to_string_lossy().into_owned())]);
    let lib_src_arts = ModuleArtifacts::from_available(&lib_src_avail, "fixture", String::new).unwrap();
    let adm_src_mut = c_src.admitted_mut().unwrap();
    adm_src_mut.artifacts.insert("LibSrc".into(), lib_src_arts);
    adm_src_mut.library_modules.insert("LibSrc".into());
    let dep_edge = ImportEdge {
        module: dep_src,
        import_all: false,
        is_exported: true,
        is_meta: false,
    };
    adm_src_mut.graph.insert("LibSrc".into(), vec![dep_edge]);
    adm_src_mut.graph.get_mut("Captured").unwrap().push(ImportEdge {
        module: "LibSrc".into(),
        import_all: false,
        is_exported: true,
        is_meta: false,
    });
    reject_inspected(
        &mut c_src,
        f_src.request.clone(),
        "uninventoried target library dependency LibSrc.uninv",
    );

    let f_prf = Fixture::new(PROOF);
    let mut c_prf = f_prf.accepted_checker();
    let adm_prf = c_prf.admitted().unwrap();
    let dep_prf = adm_prf.foundation_modules().into_iter().next().unwrap().to_owned();
    let lib1_olean = c_prf.stage().join("lib/LibPrf1.olean");
    let lib2_olean = c_prf.stage().join("lib/LibPrf2.olean");
    let prf_olean = c_prf.stage().join("lib/Proof.olean");
    let forge_prf = c_prf.stage().join("ForgeProofUninventoriedLib.lean");
    run_lean_script(
        &mut c_prf,
        "forge-proof-uninventoried-lib",
        &forge_prf,
        &format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               let uninvThm : ConstantInfo := .thmInfo {{\n    \
                 name := `LibPrf1.uninv, levelParams := [],\n    \
                 type := .const `True [], value := .const `True.intro [],\n    \
                 all := [`LibPrf1.uninv] }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `LibPrf1 {{\n    \
                 isModule := false, imports := #[{{ module := `{dep_prf} }}],\n    \
                 constNames := #[], constants := #[],\n    \
                 extraConstNames := #[`LibPrf1.uninv], entries := #[] }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `LibPrf2 {{\n    \
                 isModule := false,\n    \
                 imports := #[{{ module := `{dep_prf} }}, {{ module := `LibPrf1 }}],\n    \
                 constNames := #[`LibPrf1.uninv], constants := #[uninvThm],\n    \
                 extraConstNames := #[], entries := #[] }}\n  \
               let prfPath := System.FilePath.mk {:?}\n  \
               let (prfData, _) ← readModuleData prfPath\n  \
               saveModuleData prfPath `Proof {{ prfData with\n    \
                 constNames := prfData.constNames.push `LibPrf1.uninv,\n    \
                 constants := prfData.constants.push uninvThm }}\n",
            lib1_olean.to_string_lossy(),
            lib2_olean.to_string_lossy(),
            prf_olean.to_string_lossy(),
        ),
    );
    let lib1_arts = ModuleArtifacts::from_available(
        &BTreeMap::from([("olean", lib1_olean.to_string_lossy().into_owned())]),
        "fixture",
        String::new,
    )
    .unwrap();
    let lib2_arts = ModuleArtifacts::from_available(
        &BTreeMap::from([("olean", lib2_olean.to_string_lossy().into_owned())]),
        "fixture",
        String::new,
    )
    .unwrap();
    let adm_prf_mut = c_prf.admitted_mut().unwrap();
    adm_prf_mut.artifacts.insert("LibPrf1".into(), lib1_arts);
    adm_prf_mut.artifacts.insert("LibPrf2".into(), lib2_arts);
    adm_prf_mut.library_modules.insert("LibPrf1".into());
    adm_prf_mut.library_modules.insert("LibPrf2".into());
    let dep_prf_edge = ImportEdge {
        module: dep_prf,
        import_all: false,
        is_exported: true,
        is_meta: false,
    };
    adm_prf_mut.graph.insert("LibPrf1".into(), vec![dep_prf_edge.clone()]);
    adm_prf_mut.graph.insert(
        "LibPrf2".into(),
        vec![
            dep_prf_edge,
            ImportEdge {
                module: "LibPrf1".into(),
                import_all: false,
                is_exported: true,
                is_meta: false,
            },
        ],
    );
    reject_inspected(
        &mut c_prf,
        f_prf.request.clone(),
        "uninventoried target library dependency LibPrf1.uninv",
    );

    let f_extra = Fixture::new(PROOF);
    let mut c_extra = f_extra.accepted_checker();
    let cap_extra_olean = c_extra.stage().join("lib/Captured.olean");
    let exp_extra_olean = c_extra.stage().join("lib/Expected.olean");
    let forge_extra = c_extra.stage().join("ForgeSourceExtraConst.lean");
    run_lean_script(
        &mut c_extra,
        "forge-source-extra-const",
        &forge_extra,
        &format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               let capPath := System.FilePath.mk {:?}\n  \
               let (capData, _) ← readModuleData capPath\n  \
               saveModuleData capPath `Captured {{ capData with\n    \
                 extraConstNames := capData.extraConstNames.push `Captured.irHelper }}\n  \
               let expPath := System.FilePath.mk {:?}\n  \
               let (expData, _) ← readModuleData expPath\n  \
               let helperThm : ConstantInfo := .thmInfo {{\n    \
                 name := `Captured.irHelper, levelParams := [],\n    \
                 type := .const `True [], value := .const `True.intro [],\n    \
                 all := [`Captured.irHelper] }}\n  \
               saveModuleData expPath `Expected {{ expData with\n    \
                 constNames := expData.constNames.push `Captured.irHelper,\n    \
                 constants := expData.constants.push helperThm }}\n",
            cap_extra_olean.to_string_lossy(),
            exp_extra_olean.to_string_lossy(),
        ),
    );
    reject_inspected(
        &mut c_extra,
        f_extra.request.clone(),
        "uninventoried kernel compiler helper Captured.irHelper",
    );

    // Reversed extra-name collisions: when an already-declared foundation,
    // source, or library name appears in a later `.source` module's
    // `extraConstNames` (absent from `modConsts`), `const2ModIdx` preserves the
    // earlier owner, so `auditTarget` must still reject the checked-env
    // collision regardless of `actualOrig`.
    for (owner_kind, helper_sym, err_sub) in [
        ("foundation", "True.intro", "uninventoried kernel compiler helper True.intro"),
        ("source", "Captured.srcHelper", "uninventoried kernel compiler helper Captured.srcHelper"),
        ("library", "LibSrc2.libHelper", "uninventoried kernel compiler helper LibSrc2.libHelper"),
    ] {
        let f_rev = Fixture::new(PROOF);
        let mut c_rev = f_rev.accepted_checker();
        let dep_rev = c_rev.admitted().unwrap().foundation_modules().into_iter().next().unwrap().to_owned();
        let lib2_rev_olean = c_rev.stage().join("lib/LibSrc2.olean");
        let cap_rev_olean = c_rev.stage().join("lib/Captured.olean");
        let exp_rev_olean = c_rev.stage().join("lib/Expected.olean");
        let forge_rev = c_rev.stage().join(format!("ForgeRevExtra_{owner_kind}.lean"));
        run_lean_script(
            &mut c_rev,
            &format!("forge-rev-extra-{owner_kind}"),
            &forge_rev,
            &format!(
                "import Lean\n\
                 open Lean in\n\
                 def main : IO Unit := do\n  \
                   let helperName := `{helper_sym}\n  \
                   let helperThm : ConstantInfo := .thmInfo {{\n    \
                     name := helperName, levelParams := [],\n    \
                     type := .const `True [], value := .const `True.intro [],\n    \
                     all := [helperName] }}\n  \
                   let capPath := System.FilePath.mk {:?}\n  \
                   let (capData, _) ← readModuleData capPath\n  \
                   let expPath := System.FilePath.mk {:?}\n  \
                   let (expData, _) ← readModuleData expPath\n  \
                   if {:?} == \"foundation\" then\n    \
                     saveModuleData expPath `Expected {{ expData with\n      \
                       extraConstNames := expData.extraConstNames.push helperName }}\n  \
                   else if {:?} == \"source\" then\n    \
                     saveModuleData capPath `Captured {{ capData with\n      \
                       constNames := capData.constNames.push helperName,\n      \
                       constants := capData.constants.push helperThm }}\n    \
                     saveModuleData expPath `Expected {{ expData with\n      \
                       extraConstNames := expData.extraConstNames.push helperName }}\n  \
                   else\n    \
                     saveModuleData (System.FilePath.mk {:?}) `LibSrc2 {{\n      \
                       isModule := false, imports := #[{{ module := `{dep_rev} }}],\n      \
                       constNames := #[helperName], constants := #[helperThm],\n      \
                       extraConstNames := #[], entries := #[] }}\n    \
                     saveModuleData capPath `Captured {{ capData with\n      \
                       imports := capData.imports.push {{ module := `LibSrc2 }},\n      \
                       extraConstNames := capData.extraConstNames.push helperName }}\n",
                cap_rev_olean.to_string_lossy(),
                exp_rev_olean.to_string_lossy(),
                owner_kind,
                owner_kind,
                lib2_rev_olean.to_string_lossy(),
            ),
        );
        if owner_kind == "library" {
            let lib2_arts = ModuleArtifacts::from_available(
                &BTreeMap::from([("olean", lib2_rev_olean.to_string_lossy().into_owned())]),
                "fixture",
                String::new,
            )
            .unwrap();
            let adm_rev = c_rev.admitted_mut().unwrap();
            adm_rev.artifacts.insert("LibSrc2".into(), lib2_arts);
            adm_rev.library_modules.insert("LibSrc2".into());
            adm_rev.graph.insert(
                "LibSrc2".into(),
                vec![ImportEdge {
                    module: dep_rev,
                    import_all: false,
                    is_exported: true,
                    is_meta: false,
                }],
            );
            adm_rev.graph.get_mut("Captured").unwrap().push(ImportEdge {
                module: "LibSrc2".into(),
                import_all: false,
                is_exported: true,
                is_meta: false,
            });
        }
        reject_inspected(&mut c_rev, f_rev.request.clone(), err_sub);
    }
}

/// Under `--allow-sorry-in-proof`, a `.source .proof` alternate body
/// referencing `sorryAx`:
/// 1. still enqueues non-`sorryAx` dependencies into `phase2Roots` (rejecting
///    unapproved axioms and tampered helpers fail-closed);
/// 2. still undergoes fresh kernel typechecking via `checkAlternateProofs`
///    (and `phase2Roots` replay when `idx == 0` across two `Proof` modules),
///    rejecting ill-typed `sorryAx`-bearing alternate proof bodies fail-closed;
/// 3. passes when the `sorryAx`-bearing alternate proof body is well-typed,
///    recording the theorem in `sorryDeclarations`.
#[test]
fn target_audit_allow_sorry_alternate_keeps_non_sorry_deps_in_phase2() {
    let mut f_sorry_alt_ax = Fixture::new(PROOF);
    f_sorry_alt_ax.request.allow_sorry_in_proof = true;
    let mut c_sorry_alt_ax = f_sorry_alt_ax.accepted_checker();
    let sorry_alt_prefix = c_sorry_alt_ax.admitted().unwrap().prefix.clone();
    let proof_sorry_ax_olean = c_sorry_alt_ax.stage().join("lib/Proof.olean");
    let sorry_ax_script = c_sorry_alt_ax.stage().join("ForgeProofSorryAltAxiom.lean");
    run_lean_script(
        &mut c_sorry_alt_ax,
        "forge-proof-sorry-alt-axiom",
        &sorry_ax_script,
        &format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               initSearchPath (System.FilePath.mk {:?})\n  \
               let env ← importModules #[{{ module := `Init.Core }}] {{}} \
                 (trustLevel := 0) (plugins := #[]) (loadExts := false) \
                 (level := .private)\n  \
               let some (.thmInfo flipTv) := env.checked.get.find? `flip.eq_1 \
                 | throw (IO.userError \"missing flip.eq_1\")\n  \
               let (data, _) ← readModuleData (System.FilePath.mk {:?})\n  \
               let badAx : ConstantInfo := .axiomInfo {{\n    \
                 name := `Proof.badAxiom, levelParams := [],\n    \
                 type := .const `True [], isUnsafe := false }}\n  \
               let sorryTerm := mkApp2 (.const `sorryAx [.zero]) \
                 (.const `True []) (.const `Bool.false [])\n  \
               let wrapped := Expr.letE `_s (.const `True []) sorryTerm\n    \
                 (Expr.letE `_a (.const `True []) (.const `Proof.badAxiom []) \
                   flipTv.value false) false\n  \
               let forgedFlip : ConstantInfo := .thmInfo {{ flipTv with value := wrapped }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Proof {{ data with\n    \
                 constNames := (data.constNames.push `Proof.badAxiom).push `flip.eq_1,\n    \
                 constants := (data.constants.push badAx).push forgedFlip }}\n",
            sorry_alt_prefix.to_string_lossy(),
            proof_sorry_ax_olean.to_string_lossy(),
            proof_sorry_ax_olean.to_string_lossy()
        ),
    );
    reject_inspected(
        &mut c_sorry_alt_ax,
        f_sorry_alt_ax.request.clone(),
        "unapproved axiom Proof.badAxiom from Proof",
    );

    let mut f_sorry_alt_bad = Fixture::new(PROOF);
    f_sorry_alt_bad.request.allow_sorry_in_proof = true;
    let mut c_sorry_alt_bad = f_sorry_alt_bad.accepted_checker();
    let sorry_bad_prefix = c_sorry_alt_bad.admitted().unwrap().prefix.clone();
    let proof_sorry_bad_olean = c_sorry_alt_bad.stage().join("lib/Proof.olean");
    let sorry_bad_script = c_sorry_alt_bad.stage().join("ForgeProofSorryAltBadHelper.lean");
    run_lean_script(
        &mut c_sorry_alt_bad,
        "forge-proof-sorry-alt-bad-helper",
        &sorry_bad_script,
        &format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               initSearchPath (System.FilePath.mk {:?})\n  \
               let env ← importModules #[{{ module := `Init.Core }}] {{}} \
                 (trustLevel := 0) (plugins := #[]) (loadExts := false) \
                 (level := .private)\n  \
               let some (.thmInfo flipTv) := env.checked.get.find? `flip.eq_1 \
                 | throw (IO.userError \"missing flip.eq_1\")\n  \
               let (data, _) ← readModuleData (System.FilePath.mk {:?})\n  \
               let badHelper : ConstantInfo := .thmInfo {{\n    \
                 name := `Proof.badHelper, levelParams := [],\n    \
                 type := .const `True [], value := .const `Bool.true [],\n    \
                 all := [`Proof.badHelper] }}\n  \
               let sorryTerm := mkApp2 (.const `sorryAx [.zero]) \
                 (.const `True []) (.const `Bool.false [])\n  \
               let wrapped := Expr.letE `_s (.const `True []) sorryTerm\n    \
                 (Expr.letE `_h (.const `True []) (.const `Proof.badHelper []) \
                   flipTv.value false) false\n  \
               let forgedFlip : ConstantInfo := .thmInfo {{ flipTv with value := wrapped }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Proof {{ data with\n    \
                 constNames := (data.constNames.push `Proof.badHelper).push `flip.eq_1,\n    \
                 constants := (data.constants.push badHelper).push forgedFlip }}\n",
            sorry_bad_prefix.to_string_lossy(),
            proof_sorry_bad_olean.to_string_lossy(),
            proof_sorry_bad_olean.to_string_lossy()
        ),
    );
    let replay_err = c_sorry_alt_bad
        .inspect(anneal_audit::InspectorRequest::TargetAudit {
            request: f_sorry_alt_bad.request.clone(),
        })
        .unwrap_err();
    assert_eq!(replay_err.code, 2, "{replay_err}");
    assert!(
        replay_err
            .message
            .contains("kernel replay rejected target dependency")
            && replay_err.message.contains("Proof.badHelper"),
        "expected kernel replay rejection on Proof.badHelper, got: {replay_err}"
    );

    // 3. Under `--allow-sorry-in-proof`, an ill-typed `sorryAx`-bearing
    //    `.source .proof` alternate (`idx == 1` overriding `.foundation`
    //    `flip.eq_1`) MUST still undergo fresh kernel typechecking via
    //    `checkAlternateProofs` and fail closed.
    let mut f_sorry_ill = Fixture::new(PROOF);
    f_sorry_ill.request.allow_sorry_in_proof = true;
    let mut c_sorry_ill = f_sorry_ill.accepted_checker();
    let sorry_ill_prefix = c_sorry_ill.admitted().unwrap().prefix.clone();
    let proof_sorry_ill_olean = c_sorry_ill.stage().join("lib/Proof.olean");
    let sorry_ill_script = c_sorry_ill.stage().join("ForgeProofSorryAltIllTyped.lean");
    run_lean_script(
        &mut c_sorry_ill,
        "forge-proof-sorry-alt-ill-typed",
        &sorry_ill_script,
        &format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               initSearchPath (System.FilePath.mk {:?})\n  \
               let env ← importModules #[{{ module := `Init.Core }}] {{}} \
                 (trustLevel := 0) (plugins := #[]) (loadExts := false) \
                 (level := .private)\n  \
               let some (.thmInfo flipTv) := env.checked.get.find? `flip.eq_1 \
                 | throw (IO.userError \"missing flip.eq_1\")\n  \
               let (data, _) ← readModuleData (System.FilePath.mk {:?})\n  \
               let sorryTerm := mkApp2 (.const `sorryAx [.zero]) \
                 (.const `True []) (.const `Bool.false [])\n  \
               let illBody := Expr.letE `_s (.const `True []) sorryTerm \
                 (.const `Bool.true []) false\n  \
               let forgedFlip : ConstantInfo := .thmInfo {{ flipTv with value := illBody }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Proof {{ data with\n    \
                 constNames := data.constNames.push `flip.eq_1,\n    \
                 constants := data.constants.push forgedFlip }}\n",
            sorry_ill_prefix.to_string_lossy(),
            proof_sorry_ill_olean.to_string_lossy(),
            proof_sorry_ill_olean.to_string_lossy()
        ),
    );
    let ill_err = c_sorry_ill
        .inspect(anneal_audit::InspectorRequest::TargetAudit {
            request: f_sorry_ill.request.clone(),
        })
        .unwrap_err();
    assert_eq!(ill_err.code, 2, "{ill_err}");
    assert!(
        ill_err
            .message
            .contains("kernel operation failed (alternate pinned theorem proof check flip.eq_1)")
            && ill_err.message.contains("declaration type mismatch"),
        "expected checkAlternateProofs rejection on ill-typed sorryAx alternate flip.eq_1, got: {ill_err}"
    );

    // 4. Across two `.source .proof` modules (`ProofHelper` `idx == 0` and
    //    `Proof` `idx == 1`), when `Proof.verify` never references
    //    `ProofHelper.unused` and both exports carry `sorryAx`-bearing
    //    alternate bodies (`ProofHelper` ill-typed), `target-audit` enqueues
    //    `idx == 0` into `phase2Roots` and both into `sourceAlternateProofs`,
    //    rejecting fail-closed.
    let mut f_two_proof = Fixture::new(
        "prelude\nimport Expected\nimport Init.Data.BitVec.Lemmas\nimport ProofHelper\n\
         theorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n",
    );
    f_two_proof.set(
        "ProofHelper",
        TargetRole::Proof,
        "prelude\nimport Expected\ntheorem ProofHelper.unused : True := sorry\n",
    );
    f_two_proof.request.allow_sorry_in_proof = true;
    let mut c_two_proof = f_two_proof.accepted_checker();
    let helper_olean = c_two_proof.stage().join("lib/ProofHelper.olean");
    let main_proof_olean = c_two_proof.stage().join("lib/Proof.olean");
    let two_proof_script = c_two_proof.stage().join("ForgeTwoProofSorryAltIllTyped.lean");
    run_lean_script(
        &mut c_two_proof,
        "forge-two-proof-sorry-alt-ill-typed",
        &two_proof_script,
        &format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               let helperPath := System.FilePath.mk {:?}\n  \
               let (helperData, _) ← readModuleData helperPath\n  \
               let sorryTrue := mkApp2 (.const `sorryAx [.zero]) \
                 (.const `True []) (.const `Bool.false [])\n  \
               let illBody := Expr.letE `_s (.const `True []) sorryTrue \
                 (.const `Bool.true []) false\n  \
               let helperAlt : ConstantInfo := .thmInfo {{\n    \
                 name := `ProofHelper.unused, levelParams := [],\n    \
                 type := .const `True [], value := illBody,\n    \
                 all := [`ProofHelper.unused] }}\n  \
               saveModuleData helperPath `ProofHelper {{ helperData with\n    \
                 constants := helperData.constants.map fun ci =>\n      \
                   if ci.name == `ProofHelper.unused then helperAlt else ci }}\n  \
               let mainPath := System.FilePath.mk {:?}\n  \
               let (mainData, _) ← readModuleData mainPath\n  \
               let otherSorry := Expr.letE `_t (.const `True []) sorryTrue \
                 (.const `True.intro []) false\n  \
               let mainAlt : ConstantInfo := .thmInfo {{\n    \
                 name := `ProofHelper.unused, levelParams := [],\n    \
                 type := .const `True [], value := otherSorry,\n    \
                 all := [`ProofHelper.unused] }}\n  \
               saveModuleData mainPath `Proof {{ mainData with\n    \
                 constNames := mainData.constNames.push `ProofHelper.unused,\n    \
                 constants := mainData.constants.push mainAlt }}\n",
            helper_olean.to_string_lossy(),
            main_proof_olean.to_string_lossy()
        ),
    );
    let two_err = c_two_proof
        .inspect(anneal_audit::InspectorRequest::TargetAudit {
            request: f_two_proof.request.clone(),
        })
        .unwrap_err();
    assert_eq!(two_err.code, 2, "{two_err}");
    assert!(
        two_err
            .message
            .contains("kernel replay rejected target dependency")
            && two_err.message.contains("ProofHelper.unused"),
        "expected kernel replay rejection on idx == 0 ill-typed sorryAx alternate ProofHelper.unused, got: {two_err}"
    );

    // 5. Positive control: a well-typed `sorryAx`-bearing `.source .proof`
    //    alternate overriding `.foundation` `flip.eq_1` passes fresh kernel
    //    typechecking in `checkAlternateProofs` and records `flip.eq_1` in
    //    `sorryDeclarations`.
    let mut f_sorry_ok = Fixture::new(PROOF);
    f_sorry_ok.request.allow_sorry_in_proof = true;
    let mut c_sorry_ok = f_sorry_ok.accepted_checker();
    let sorry_ok_prefix = c_sorry_ok.admitted().unwrap().prefix.clone();
    let proof_sorry_ok_olean = c_sorry_ok.stage().join("lib/Proof.olean");
    let sorry_ok_script = c_sorry_ok.stage().join("ForgeProofSorryAltWellTyped.lean");
    run_lean_script(
        &mut c_sorry_ok,
        "forge-proof-sorry-alt-well-typed",
        &sorry_ok_script,
        &format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               initSearchPath (System.FilePath.mk {:?})\n  \
               let env ← importModules #[{{ module := `Init.Core }}] {{}} \
                 (trustLevel := 0) (plugins := #[]) (loadExts := false) \
                 (level := .private)\n  \
               let some (.thmInfo flipTv) := env.checked.get.find? `flip.eq_1 \
                 | throw (IO.userError \"missing flip.eq_1\")\n  \
               let (data, _) ← readModuleData (System.FilePath.mk {:?})\n  \
               let sorryFlip := mkApp2 (.const `sorryAx [.zero]) \
                 flipTv.type (.const `Bool.false [])\n  \
               let forgedFlip : ConstantInfo := .thmInfo {{ flipTv with value := sorryFlip }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Proof {{ data with\n    \
                 constNames := data.constNames.push `flip.eq_1,\n    \
                 constants := data.constants.push forgedFlip }}\n",
            sorry_ok_prefix.to_string_lossy(),
            proof_sorry_ok_olean.to_string_lossy(),
            proof_sorry_ok_olean.to_string_lossy()
        ),
    );
    let ok_rep = c_sorry_ok
        .inspect(anneal_audit::InspectorRequest::TargetAudit {
            request: f_sorry_ok.request.clone(),
        })
        .unwrap();
    assert_eq!(ok_rep["replay"], true);
    assert_eq!(ok_rep["exactType"], true);
    assert!(
        ok_rep["sorryDeclarations"]
            .as_array()
            .unwrap()
            .iter()
            .any(|n| n == "flip.eq_1"),
        "expected flip.eq_1 in sorryDeclarations: {ok_rep}"
    );

    // 6. When a Phase-1 stored constant (`flip.eq_1` used by `Spec.specs`)
    //    is sorry-free, a well-typed `sorryAx`-bearing `.source .proof`
    //    alternate in `Proof.olean` enters `altSorryDecls` and must be rejected
    //    by `TrustedBoundary.lean`'s post-Phase-1 check.
    let mut f_sorry_phase1_alt = Fixture::new(
        "prelude\nimport Expected\nimport Init.Data.BitVec.Lemmas\n\
         theorem Proof.verify : Expected.claim := And.intro rfl BitVec.and_self\n",
    );
    f_sorry_phase1_alt.set(
        "Spec",
        TargetRole::Specification,
        "prelude\nimport Model\n\
         def Spec.specs (p : BitVec 8) : Prop :=\n  \
           (fun (_ : flip Nat.add 0 1 = Nat.add 1 0) => BitVec.and p p = p)\n    \
             (@flip.eq_1 Nat Nat Nat Nat.add 1 0)\n",
    );
    f_sorry_phase1_alt.request.allow_sorry_in_proof = true;
    let mut c_sorry_phase1_alt = f_sorry_phase1_alt.accepted_checker();
    let p1_alt_prefix = c_sorry_phase1_alt.admitted().unwrap().prefix.clone();
    let proof_p1_alt_olean = c_sorry_phase1_alt.stage().join("lib/Proof.olean");
    let p1_alt_script = c_sorry_phase1_alt.stage().join("ForgeProofSorryPhase1Alt.lean");
    run_lean_script(
        &mut c_sorry_phase1_alt,
        "forge-proof-sorry-phase1-alt",
        &p1_alt_script,
        &format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               initSearchPath (System.FilePath.mk {:?})\n  \
               let env ← importModules #[{{ module := `Init.Core }}] {{}} \
                 (trustLevel := 0) (plugins := #[]) (loadExts := false) \
                 (level := .private)\n  \
               let some (.thmInfo flipTv) := env.checked.get.find? `flip.eq_1 \
                 | throw (IO.userError \"missing flip.eq_1\")\n  \
               let (data, _) ← readModuleData (System.FilePath.mk {:?})\n  \
               let sorryFlip := mkApp2 (.const `sorryAx [.zero]) \
                 flipTv.type (.const `Bool.false [])\n  \
               let forgedFlip : ConstantInfo := .thmInfo {{ flipTv with value := sorryFlip }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Proof {{ data with\n    \
                 constNames := data.constNames.push `flip.eq_1,\n    \
                 constants := data.constants.push forgedFlip }}\n",
            p1_alt_prefix.to_string_lossy(),
            proof_p1_alt_olean.to_string_lossy(),
            proof_p1_alt_olean.to_string_lossy()
        ),
    );
    reject_inspected(
        &mut c_sorry_phase1_alt,
        f_sorry_phase1_alt.request.clone(),
        "unapproved axiom sorryAx from Init.Prelude",
    );
}
