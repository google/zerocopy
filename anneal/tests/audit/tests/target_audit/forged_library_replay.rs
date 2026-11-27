// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Forged library keys, duplicate libraries, `unsafe_rec` type mismatches,
//! and identical foundation copies during replay.

use super::*;

/// Verifies `lean4#16677` defense-in-depth hardening in `TrustedBoundary.lean`:
/// - mismatched `constNames` vs `ConstantInfo.name` in `.olean` inventories;
/// - intra-module duplicate names in `.library` `.olean` inventories; and
/// - `TargetRole::Specification` `p._unsafe_rec` with mismatched type.
#[test]
fn target_audit_rejects_key_mismatch_dup_library_and_unsafe_rec_type_mismatch() {
    use std::collections::BTreeMap;

    use anneal_audit::{ImportEdge, ModuleArtifacts};

    // 1. Mismatched `constNames` key (`Captured.wrongKey` vs `Captured.aux`).
    let mut f_key = Fixture::new(PROOF);
    f_key.set(
        "Captured",
        TargetRole::Capture,
        "prelude\nimport Model\n\
         def Captured.aux : Nat := 1\n\
         def Captured.program : BitVec 8 := BitVec.ofNat 8 7\n",
    );
    let mut c_key = f_key.accepted_checker();
    let cap_olean = c_key.stage().join("lib/Captured.olean");
    let key_script = c_key.stage().join("ForgeKeyMismatch.lean");
    run_lean_script(
        &mut c_key,
        "forge-key-mismatch",
        &key_script,
        &format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               let p := System.FilePath.mk {:?}\n  \
               let (data, _) ← readModuleData p\n  \
               let patched := data.constNames.map (fun n =>\n    \
                 if n == `Captured.aux then `Captured.wrongKey else n)\n  \
               saveModuleData p `Captured {{ data with constNames := patched }}\n",
            cap_olean.to_string_lossy()
        ),
    );
    reject_inspected(&mut c_key, f_key.request.clone(), "mismatched checked environment key");

    // 2. Intra-module duplicate declaration in a `.library` module must fail
    //    closed rather than collapsing silently via `NameSet.ofList`.
    let f_dup = Fixture::new(PROOF);
    let mut c_dup = f_dup.accepted_checker();
    let adm = c_dup.admitted().unwrap();
    let dep = adm.foundation_modules().into_iter().next().unwrap().to_owned();
    let dup_lib_olean = c_dup.stage().join("lib/DupLib.olean");
    let dup_script = c_dup.stage().join("ForgeDupLib.lean");
    run_lean_script(
        &mut c_dup,
        "forge-dup-lib",
        &dup_script,
        &format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               let ci : ConstantInfo := .thmInfo {{\n    \
                 name := `DupLib.t\n    \
                 levelParams := []\n    \
                 type := .const `True []\n    \
                 value := .const `True.intro []\n    \
                 all := [`DupLib.t]\n  \
               }}\n  \
               let md : ModuleData := {{\n    \
                 isModule := false\n    \
                 imports := #[{{ module := `{dep} }}]\n    \
                 constNames := #[`DupLib.t, `DupLib.t]\n    \
                 constants := #[ci, ci]\n    \
                 extraConstNames := #[]\n    \
                 entries := #[]\n  \
               }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `DupLib md\n",
            dup_lib_olean.to_string_lossy()
        ),
    );
    let dup_avail = BTreeMap::from([("olean", dup_lib_olean.to_string_lossy().into_owned())]);
    let dup_arts = ModuleArtifacts::from_available(&dup_avail, "fixture", String::new).unwrap();
    let adm_mut = c_dup.admitted_mut().unwrap();
    adm_mut.artifacts.insert("DupLib".into(), dup_arts);
    adm_mut.library_modules.insert("DupLib".into());
    adm_mut.graph.insert(
        "DupLib".into(),
        vec![ImportEdge {
            module: dep,
            import_all: false,
            is_exported: true,
            is_meta: false,
        }],
    );
    reject_inspected(
        &mut c_dup,
        f_dup.request.clone(),
        "duplicate target library declaration DupLib.t",
    );

    // 3. `TargetRole::Specification` `p._unsafe_rec` with mismatched type fails
    //    `pairedSpecUnsafeRecParent?` and is rejected as unreplayable partial.
    let f_rec = Fixture::new(PROOF);
    let mut c_rec = f_rec.accepted_checker();
    let spec_olean = c_rec.stage().join("lib/Spec.olean");
    let rec_script = c_rec.stage().join("ForgeBadUnsafeRec.lean");
    run_lean_script(
        &mut c_rec,
        "forge-bad-unsafe-rec",
        &rec_script,
        &format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               let p := System.FilePath.mk {:?}\n  \
               let (data, _) ← readModuleData p\n  \
               let parentCi : ConstantInfo := .defnInfo {{\n    \
                 name := `Spec.foo\n    \
                 levelParams := []\n    \
                 type := .const `Nat []\n    \
                 value := .lit (.natVal 0)\n    \
                 hints := .abbrev\n    \
                 safety := .safe\n    \
                 all := [`Spec.foo]\n  \
               }}\n  \
               let badRecCi : ConstantInfo := .defnInfo {{\n    \
                 name := `Spec.foo._unsafe_rec\n    \
                 levelParams := []\n    \
                 type := .const `Bool []\n    \
                 value := .const `Bool.true []\n    \
                 hints := .abbrev\n    \
                 safety := .partial\n    \
                 all := [`Spec.foo._unsafe_rec]\n  \
               }}\n  \
               let newNames := data.constNames ++ #[`Spec.foo, `Spec.foo._unsafe_rec]\n  \
               let newConsts := data.constants ++ #[parentCi, badRecCi]\n  \
               saveModuleData p `Spec \
                 {{ data with constNames := newNames, constants := newConsts }}\n",
            spec_olean.to_string_lossy()
        ),
    );
    reject_inspected(
        &mut c_rec,
        f_rec.request.clone(),
        "unsafe/partial logical dependency Spec.foo._unsafe_rec",
    );

    // 4. Duplicate constant inside a `.foundation` `.olean` is rejected by
    //    `verifyModuleHeaderInventory` in `targetAudit`'s `.foundation` arm.
    let f_found = Fixture::new(PROOF);
    let mut c_found = f_found.accepted_checker();
    let orig_core = c_found.admitted().unwrap().artifacts["Init.Core"].clone();
    let orig_core_path = orig_core
        .olean_parts
        .first()
        .expect("Init.Core olean");
    let forged_core = c_found.stage().join("lib/ForgedInitCore.olean");
    let found_script = c_found.stage().join("ForgeInitCore.lean");
    let found_src = format!(
        "import Lean\n\
         open Lean in\n\
         def main : IO Unit := do\n  \
           let (data, _) ← readModuleData (System.FilePath.mk {:?})\n  \
           let extra := data.constants[0]!\n  \
           let md : ModuleData := {{ data with\n    \
             isModule := false,\n    \
             constNames := data.constNames.push extra.name,\n    \
             constants := data.constants.push extra }}\n  \
           saveModuleData (System.FilePath.mk {:?}) `Init.Core md\n",
        orig_core_path.as_str(),
        forged_core.to_string_lossy()
    );
    run_lean_script(&mut c_found, "forge-foundation-dup", &found_script, &found_src);
    let forged_avail = BTreeMap::from([("olean", forged_core.to_string_lossy().into_owned())]);
    let forged_arts = ModuleArtifacts::from_available(&forged_avail, "fixture", String::new).unwrap();
    c_found.admitted_mut().unwrap().artifacts.insert("Init.Core".into(), forged_arts);
    reject_inspected(
        &mut c_found,
        f_found.request.clone(),
        "duplicate target declaration",
    );

    // 5. `Model` `.olean` re-declaring `propext` as a theorem overwrites
    //    `stored` via Lean `subsumesInfo`, exercising `targetAudit`'s
    //    `.foundation` reconciliation (`sameConstantShape stored ci`).
    let f_hijack = Fixture::new(PROOF);
    let mut c_model_hijack = f_hijack.accepted_checker();
    let hijack_model = c_model_hijack.stage().join("lib/Model.olean");
    let hijack_prefix = c_model_hijack.admitted().unwrap().prefix.clone();
    let hijack_script = c_model_hijack.stage().join("ForgeModelPropextHijack.lean");
    let hijack_src = format!(
        "import Lean\n\
         open Lean in\n\
         def main : IO Unit := do\n  \
           initSearchPath (System.FilePath.mk {:?})\n  \
           let env ← importModules #[{{ module := `Init.Core }}] {{}} \
             (trustLevel := 0) (plugins := #[]) (loadExts := false) \
             (level := .private)\n  \
           let some px := env.checked.get.find? `propext \
             | throw (IO.userError \"missing propext\")\n  \
           let p := System.FilePath.mk {:?}\n  \
           let (data, _) ← readModuleData p\n  \
           let body := Expr.const `True []\n  \
           let fakeThm : ConstantInfo := .thmInfo {{\n    \
             name := `propext, levelParams := px.levelParams,\n    \
             type := px.type, value := body, all := [`propext] }}\n  \
           let newNames := data.constNames.push `propext\n  \
           let newConsts := data.constants.push fakeThm\n  \
           saveModuleData p `Model \
             {{ data with constNames := newNames, constants := newConsts }}\n",
        hijack_prefix.to_string_lossy(),
        hijack_model.to_string_lossy()
    );
    run_lean_script(&mut c_model_hijack, "forge-model-propext-hijack", &hijack_script, &hijack_src);
    reject_inspected(
        &mut c_model_hijack,
        f_hijack.request.clone(),
        "stored target declaration differs propext",
    );

    // 6. A `.library` `.olean` overriding a `.foundation` theorem (`Iff.refl`)
    //    via `subsumesInfo` with a proof body referencing a `.source` constant
    //    (`Proof.verify`) is rejected by `pendingSourceAlternates` checking
    //    both `stored` and `ci` even when `Proof.verify` never references
    //    `Iff.refl`.
    let f_lib_sub = Fixture::new(PROOF);
    let mut c_lib_sub = f_lib_sub.accepted_checker();
    let lib_sub_prefix = c_lib_sub.admitted().unwrap().prefix.clone();
    let proof_olean_path = c_lib_sub.admitted().unwrap().artifacts["Proof"]
        .olean_parts
        .first()
        .expect("Proof olean")
        .clone();
    let lib_sub_olean = c_lib_sub.stage().join("lib/ZZZZSubsumesLib.olean");
    let lib_sub_script = c_lib_sub.stage().join("ForgeLibSubsumesFoundation.lean");
    run_lean_script(
        &mut c_lib_sub,
        "forge-lib-subsumes-foundation",
        &lib_sub_script,
        &format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               initSearchPath (System.FilePath.mk {:?})\n  \
               let env ← importModules #[{{ module := `Init.Core }}] {{}} \
                 (trustLevel := 0) (plugins := #[]) (loadExts := false) \
                 (level := .private)\n  \
               let some (.thmInfo iffTv) := env.checked.get.find? `Iff.refl \
                 | throw (IO.userError \"missing Iff.refl\")\n  \
               let (proofData, _) ← readModuleData (System.FilePath.mk {:?})\n  \
               let some rootCi := proofData.constants.find? (·.name == `Proof.verify) \
                 | throw (IO.userError \"missing Proof.verify\")\n  \
               let wrapped := Expr.letE `_src rootCi.type \
                 (.const `Proof.verify []) iffTv.value false\n  \
               let forged : ConstantInfo := .thmInfo {{ iffTv with value := wrapped }}\n  \
               let md : ModuleData := {{\n    \
                 isModule := false,\n    \
                 imports := #[{{ module := `Init.Core }}],\n    \
                 constNames := #[`Iff.refl],\n    \
                 constants := #[forged],\n    \
                 extraConstNames := #[],\n    \
                 entries := #[] }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `ZZZZSubsumesLib md\n",
            lib_sub_prefix.to_string_lossy(),
            proof_olean_path.as_str(),
            lib_sub_olean.to_string_lossy()
        ),
    );
    let lib_sub_avail =
        BTreeMap::from([("olean", lib_sub_olean.to_string_lossy().into_owned())]);
    let lib_sub_arts =
        ModuleArtifacts::from_available(&lib_sub_avail, "fixture", String::new).unwrap();
    {
        let adm_mut = c_lib_sub.admitted_mut().unwrap();
        adm_mut.artifacts.insert("ZZZZSubsumesLib".into(), lib_sub_arts);
        adm_mut.library_modules.insert("ZZZZSubsumesLib".into());
        adm_mut.graph.insert(
            "ZZZZSubsumesLib".into(),
            vec![ImportEdge {
                module: "Init.Core".into(),
                import_all: false,
                is_exported: true,
                is_meta: false,
            }],
        );
    }
    reject_inspected(
        &mut c_lib_sub,
        f_lib_sub.request.clone(),
        "installed library Iff.refl references target source Proof.verify",
    );

    // 7. Realizing a `.foundation` theorem (`flip.eq_1`) inside a `.source`
    //    `.olean` via `subsumesInfo` derives `storedOrigin` from the actual
    //    defining module (`storedRoleMap`): `Expected` referencing
    //    `Spec.specs` (`TargetRole::Specification`, allowed for `Expected`)
    //    succeeds and kernel-checks both alternates, whereas `Model`
    //    referencing `Spec.specs` (`TargetRole::Model` cannot depend on
    //    `Specification`) fails closed with `"target authority violation"`.
    let forge_flip_sub = |checker: &mut anneal_audit::Checker,
                          label: &str,
                          target_mod: &str,
                          target_olean: &std::path::Path| {
        let prefix = checker.admitted().unwrap().prefix.clone();
        let spec_olean = checker.stage().join("lib/Spec.olean");
        let script = checker.stage().join(format!("{label}.lean"));
        run_lean_script(
            checker,
            label,
            &script,
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
                   let (specData, _) ← readModuleData (System.FilePath.mk {:?})\n  \
                   let some specCi := specData.constants.find? (·.name == `Spec.specs) \
                     | throw (IO.userError \"missing Spec.specs\")\n  \
                   let p := System.FilePath.mk {:?}\n  \
                   let (modData, _) ← readModuleData p\n  \
                   let wrapped := Expr.letE `_spec specCi.type \
                     (.const `Spec.specs []) flipTv.value false\n  \
                   let forged : ConstantInfo := .thmInfo {{ flipTv with value := wrapped }}\n  \
                   saveModuleData p `{target_mod} {{ modData with\n    \
                     constNames := modData.constNames.push `flip.eq_1,\n    \
                     constants := modData.constants.push forged }}\n",
                prefix.to_string_lossy(),
                spec_olean.to_string_lossy(),
                target_olean.to_string_lossy()
            ),
        );
    };
    let f_src_sub = Fixture::new(PROOF);
    let mut c_src_sub = f_src_sub.accepted_checker();
    let expected_olean = c_src_sub.stage().join("lib/Expected.olean");
    forge_flip_sub(
        &mut c_src_sub,
        "forge-expected-subsumes-foundation",
        "Expected",
        &expected_olean,
    );
    let src_sub_ok = c_src_sub
        .inspect(anneal_audit::InspectorRequest::TargetAudit {
            request: f_src_sub.request.clone(),
        })
        .unwrap();
    assert_eq!(src_sub_ok["replay"], true, "{src_sub_ok}");
    assert_eq!(src_sub_ok["exactType"], true, "{src_sub_ok}");
    assert!(
        src_sub_ok["checkedAlternateProofs"].as_u64().unwrap_or(0) >= 2,
        "expected alternate proof checks for realized flip.eq_1: {src_sub_ok}"
    );

    let f_model_sub = Fixture::new(PROOF);
    let mut c_model_sub = f_model_sub.accepted_checker();
    let model_olean_for_sub = c_model_sub.stage().join("lib/Model.olean");
    forge_flip_sub(
        &mut c_model_sub,
        "forge-model-subsumes-foundation",
        "Model",
        &model_olean_for_sub,
    );
    reject_inspected(
        &mut c_model_sub,
        f_model_sub.request.clone(),
        "target authority violation flip.eq_1 references Spec.specs",
    );

    // 7c. A `.library` `.olean` exporting the exact same `ConstantInfo` body
    //     for `flip.eq_1` as a later `.source` `.olean` (`Expected`) must still
    //     be rejected via `isLibraryStored` even though `storedOrigin` resolves
    //     to `.source .expected`.
    let f_lib_dup_sub = Fixture::new(PROOF);
    let mut c_lib_dup_sub = f_lib_dup_sub.accepted_checker();
    let lib_dup_prefix = c_lib_dup_sub.admitted().unwrap().prefix.clone();
    let lib_dup_spec = c_lib_dup_sub.stage().join("lib/Spec.olean");
    let lib_dup_exp = c_lib_dup_sub.stage().join("lib/Expected.olean");
    let lib_dup_mod = c_lib_dup_sub.stage().join("lib/ZZZZDupLib.olean");
    let lib_dup_script = c_lib_dup_sub.stage().join("ForgeLibAndExpectedDup.lean");
    run_lean_script(
        &mut c_lib_dup_sub,
        "forge-lib-and-expected-dup",
        &lib_dup_script,
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
               let (specData, _) ← readModuleData (System.FilePath.mk {:?})\n  \
               let some specCi := specData.constants.find? (·.name == `Spec.specs) \
                 | throw (IO.userError \"missing Spec.specs\")\n  \
               let wrapped := Expr.letE `_spec specCi.type \
                 (.const `Spec.specs []) flipTv.value false\n  \
               let forged : ConstantInfo := .thmInfo {{ flipTv with value := wrapped }}\n  \
               let pExp := System.FilePath.mk {:?}\n  \
               let (expData, _) ← readModuleData pExp\n  \
               saveModuleData pExp `Expected {{ expData with\n    \
                 constNames := expData.constNames.push `flip.eq_1,\n    \
                 constants := expData.constants.push forged }}\n  \
               let libMd : ModuleData := {{\n    \
                 isModule := false,\n    \
                 imports := #[{{ module := `Init.Core }}],\n    \
                 constNames := #[`flip.eq_1],\n    \
                 constants := #[forged],\n    \
                 extraConstNames := #[],\n    \
                 entries := #[] }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `ZZZZDupLib libMd\n",
            lib_dup_prefix.to_string_lossy(),
            lib_dup_spec.to_string_lossy(),
            lib_dup_exp.to_string_lossy(),
            lib_dup_mod.to_string_lossy()
        ),
    );
    let lib_dup_avail =
        BTreeMap::from([("olean", lib_dup_mod.to_string_lossy().into_owned())]);
    let lib_dup_arts =
        ModuleArtifacts::from_available(&lib_dup_avail, "fixture", String::new).unwrap();
    {
        let adm_mut = c_lib_dup_sub.admitted_mut().unwrap();
        adm_mut.artifacts.insert("ZZZZDupLib".into(), lib_dup_arts);
        adm_mut.library_modules.insert("ZZZZDupLib".into());
        adm_mut.graph.insert(
            "ZZZZDupLib".into(),
            vec![ImportEdge {
                module: "Init.Core".into(),
                import_all: false,
                is_exported: true,
                is_meta: false,
            }],
        );
    }
    reject_inspected(
        &mut c_lib_dup_sub,
        f_lib_dup_sub.request.clone(),
        "installed library flip.eq_1 references target source Spec.specs",
    );

    // 7d. A first-exporter `.source` module (`Model`) declaring a theorem
    //     (`Model.badRealized`) referencing `Spec.specs` cannot hide behind a
    //     later `Expected` module exporting a byte-identical copy.
    let f_model_dup = Fixture::new(PROOF);
    let mut c_model_dup = f_model_dup.accepted_checker();
    let model_dup_spec = c_model_dup.stage().join("lib/Spec.olean");
    let model_dup_model = c_model_dup.stage().join("lib/Model.olean");
    let model_dup_exp = c_model_dup.stage().join("lib/Expected.olean");
    let model_dup_script = c_model_dup.stage().join("ForgeModelAndExpectedDup.lean");
    run_lean_script(
        &mut c_model_dup,
        "forge-model-and-expected-dup",
        &model_dup_script,
        &format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               let (specData, _) ← readModuleData (System.FilePath.mk {:?})\n  \
               let some specCi := specData.constants.find? (·.name == `Spec.specs) \
                 | throw (IO.userError \"missing Spec.specs\")\n  \
               let badThm : ConstantInfo := .thmInfo {{\n    \
                 name := `Model.badRealized, levelParams := [],\n    \
                 type := .const `True [],\n    \
                 value := Expr.letE `_spec specCi.type (.const `Spec.specs []) \
                   (.const `True.intro []) false,\n    \
                 all := [`Model.badRealized] }}\n  \
               for (modName, pathStr) in [(`Model, {:?}), (`Expected, {:?})] do\n    \
                 let p := System.FilePath.mk pathStr\n    \
                 let (d, _) ← readModuleData p\n    \
                 saveModuleData p modName {{ d with\n      \
                   constNames := d.constNames.push `Model.badRealized,\n      \
                   constants := d.constants.push badThm }}\n",
            model_dup_spec.to_string_lossy(),
            model_dup_model.to_string_lossy(),
            model_dup_exp.to_string_lossy()
        ),
    );
    reject_inspected(
        &mut c_model_dup,
        f_model_dup.request.clone(),
        "target authority violation Model.badRealized references Spec.specs",
    );

    // 8. A non-proof `.source` `.olean` (`Model`) injecting a `.thmInfo` under
    //    an `Init.Prelude` `extraConstNames` IR-helper name (`mixHash._boxed`)
    //    is rejected by `targetAudit`'s `.foundation` `extraConstNames` check.
    let f_extra_src = Fixture::new(PROOF);
    let mut c_extra_src = f_extra_src.accepted_checker();
    let model_extra_olean = c_extra_src.stage().join("lib/Model.olean");
    let extra_src_script = c_extra_src.stage().join("ForgeModelExtraCollide.lean");
    run_lean_script(
        &mut c_extra_src,
        "forge-model-extra-collide",
        &extra_src_script,
        &format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               let p := System.FilePath.mk {:?}\n  \
               let (data, _) ← readModuleData p\n  \
               let badThm : ConstantInfo := .thmInfo {{\n    \
                 name := `mixHash._boxed, levelParams := [],\n    \
                 type := .const `False [], value := .const `True.intro [],\n    \
                 all := [`mixHash._boxed] }}\n  \
               saveModuleData p `Model {{ data with\n    \
                 constNames := data.constNames.push `mixHash._boxed,\n    \
                 constants := data.constants.push badThm }}\n",
            model_extra_olean.to_string_lossy()
        ),
    );
    reject_inspected(
        &mut c_extra_src,
        f_extra_src.request.clone(),
        "uninventoried kernel compiler helper mixHash._boxed",
    );

    // 9. An exported `Proof` module declaring a constant under an
    //    `Init.Prelude` `extraConstNames` IR-helper name (`mixHash._boxed`) is
    //    rejected before `originOf` can misclassify it as `.foundation`.
    let f_extra_prf = Fixture::new(PROOF);
    let mut c_extra_prf = f_extra_prf.accepted_checker();
    let proof_extra_olean = c_extra_prf.stage().join("lib/Proof.olean");
    let extra_prf_script = c_extra_prf.stage().join("ForgeProofExtraCollide.lean");
    run_lean_script(
        &mut c_extra_prf,
        "forge-proof-extra-collide",
        &extra_prf_script,
        &format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               let p := System.FilePath.mk {:?}\n  \
               let (data, _) ← readModuleData p\n  \
               let badThm : ConstantInfo := .thmInfo {{\n    \
                 name := `mixHash._boxed, levelParams := [],\n    \
                 type := .const `True [], value := .const `True.intro [],\n    \
                 all := [`mixHash._boxed] }}\n  \
               saveModuleData p `Proof {{ data with\n    \
                 constNames := data.constNames.push `mixHash._boxed,\n    \
                 constants := data.constants.push badThm }}\n",
            proof_extra_olean.to_string_lossy()
        ),
    );
    reject_inspected(
        &mut c_extra_prf,
        f_extra_prf.request.clone(),
        "target declaration mixHash._boxed collides with imported IR helper",
    );
}

/// Verifies `targetAudit` identical-copy role tracking:
/// 1. A `.foundation` module exporting a theorem (`Target.Alt`) referencing
///    `.library` (`ZZZZLibMod.secret`) cannot mask the violation behind a
///    byte-identical copy in a later `.source` module (`Expected`), either
///    directly or after an earlier `.foundation` declaration (`ZZZZF0`).
/// 2. Conversely, a valid `.library` theorem referencing another `.library`
///    declaration also exported identically in `Expected` continues to pass.
#[test]
fn target_audit_rejects_foundation_identical_copy_with_later_source() {
    use anneal_audit::{ImportEdge, InspectorRequest, ModuleArtifacts};

    // Case A & B: `.foundation` `ZZZZFBad` exports `Target.Alt` referencing
    // `.library` `ZZZZLibMod.secret` alongside an identical copy in `Expected`
    // (both direct first-export `use_f0 = false` and post-`ZZZZF0` realization
    // `use_f0 = true`).
    for use_f0 in [false, true] {
        let f = Fixture::new(PROOF);
        let mut c = f.accepted_checker();
        let dep_core = "Init.Core".to_string();
        let f0_olean = c.stage().join("lib/ZZZZF0.olean");
        let lib_olean = c.stage().join("lib/ZZZZLibMod.olean");
        let fbad_olean = c.stage().join("lib/ZZZZFBad.olean");
        let exp_olean = c.stage().join("lib/Expected.olean");
        let script = c.stage().join(if use_f0 {
            "ForgeFoundationLibCopyAfterF0.lean"
        } else {
            "ForgeFoundationLibCopy.lean"
        });
        run_lean_script(
            &mut c,
            if use_f0 {
                "forge-foundation-lib-copy-f0"
            } else {
                "forge-foundation-lib-copy"
            },
            &script,
            &format!(
                "import Lean\n\
                 open Lean in\n\
                 def main : IO Unit := do\n  \
                   let secretThm : ConstantInfo := .thmInfo {{\n    \
                     name := `ZZZZLibMod.secret, levelParams := [],\n    \
                     type := .const `True [], value := .const `True.intro [],\n    \
                     all := [`ZZZZLibMod.secret] }}\n  \
                   saveModuleData (System.FilePath.mk {:?}) `ZZZZLibMod {{\n    \
                     isModule := false, imports := #[{{ module := `Init.Core }}],\n    \
                     constNames := #[`ZZZZLibMod.secret], constants := #[secretThm],\n    \
                     extraConstNames := #[], entries := #[] }}\n  \
                   if {use_f0} then\n    \
                     let baseThm : ConstantInfo := .thmInfo {{\n      \
                       name := `Target.Alt, levelParams := [],\n      \
                       type := .const `True [], value := .const `True.intro [],\n      \
                       all := [`Target.Alt] }}\n    \
                     saveModuleData (System.FilePath.mk {:?}) `ZZZZF0 {{\n      \
                       isModule := false, imports := #[{{ module := `Init.Core }}],\n      \
                       constNames := #[`Target.Alt], constants := #[baseThm],\n      \
                       extraConstNames := #[], entries := #[] }}\n  \
                   let badVal := Expr.letE `_sec (.const `True [])\n    \
                     (.const `ZZZZLibMod.secret []) (.const `True.intro []) false\n  \
                   let badThm : ConstantInfo := .thmInfo {{\n    \
                     name := `Target.Alt, levelParams := [],\n    \
                     type := .const `True [], value := badVal,\n    \
                     all := [`Target.Alt] }}\n  \
                   let fbadImports := if {use_f0} then\n    \
                     #[{{ module := `Init.Core }}, {{ module := `ZZZZLibMod }}, {{ module := `ZZZZF0 }}]\n  \
                     else #[{{ module := `Init.Core }}, {{ module := `ZZZZLibMod }}]\n  \
                   saveModuleData (System.FilePath.mk {:?}) `ZZZZFBad {{\n    \
                     isModule := false, imports := fbadImports,\n    \
                     constNames := #[`Target.Alt], constants := #[badThm],\n    \
                     extraConstNames := #[], entries := #[] }}\n  \
                   let expPath := System.FilePath.mk {:?}\n  \
                   let (expData, _) ← readModuleData expPath\n  \
                   saveModuleData expPath `Expected {{ expData with\n    \
                     constNames := expData.constNames.push `Target.Alt,\n    \
                     constants := expData.constants.push badThm }}\n",
                lib_olean.to_string_lossy(),
                f0_olean.to_string_lossy(),
                fbad_olean.to_string_lossy(),
                exp_olean.to_string_lossy(),
            ),
        );
        let mk_edge = |m: &str| ImportEdge {
            module: m.to_string(),
            import_all: false,
            is_exported: true,
            is_meta: false,
        };
        let lib_arts = ModuleArtifacts::from_available(
            &BTreeMap::from([("olean", lib_olean.to_string_lossy().into_owned())]),
            "fixture",
            String::new,
        )
        .unwrap();
        let fbad_arts = ModuleArtifacts::from_available(
            &BTreeMap::from([("olean", fbad_olean.to_string_lossy().into_owned())]),
            "fixture",
            String::new,
        )
        .unwrap();
        let adm = c.admitted_mut().unwrap();
        adm.artifacts.insert("ZZZZLibMod".into(), lib_arts);
        adm.library_modules.insert("ZZZZLibMod".into());
        adm.graph.insert("ZZZZLibMod".into(), vec![mk_edge(&dep_core)]);
        let mut fbad_edges = vec![mk_edge(&dep_core), mk_edge("ZZZZLibMod")];
        if use_f0 {
            let f0_arts = ModuleArtifacts::from_available(
                &BTreeMap::from([("olean", f0_olean.to_string_lossy().into_owned())]),
                "fixture",
                String::new,
            )
            .unwrap();
            adm.artifacts.insert("ZZZZF0".into(), f0_arts);
            adm.foundation_graph
                .insert("ZZZZF0".into(), vec![mk_edge(&dep_core)]);
            adm.graph.insert("ZZZZF0".into(), vec![mk_edge(&dep_core)]);
            fbad_edges.push(mk_edge("ZZZZF0"));
        }
        adm.artifacts.insert("ZZZZFBad".into(), fbad_arts);
        adm.foundation_graph
            .insert("ZZZZFBad".into(), fbad_edges.clone());
        adm.graph.insert("ZZZZFBad".into(), fbad_edges);
        reject_inspected(
            &mut c,
            f.request.clone(),
            "target authority violation Target.Alt references ZZZZLibMod.secret",
        );
    }

    // Case C: Legitimate `.library` theorem referencing another `.library`
    // declaration (`ZZZZLibGood.helper`) with a byte-identical copy in
    // `Expected` must continue to be accepted (no `.foundation` confusion).
    let f_ok = Fixture::new(PROOF);
    let mut c_ok = f_ok.accepted_checker();
    let lib_ok_olean = c_ok.stage().join("lib/ZZZZLibGood.olean");
    let exp_ok_olean = c_ok.stage().join("lib/Expected.olean");
    let ok_script = c_ok.stage().join("ForgeLibOkCopy.lean");
    run_lean_script(
        &mut c_ok,
        "forge-lib-ok-copy",
        &ok_script,
        &format!(
            "import Lean\n\
             open Lean in\n\
             def main : IO Unit := do\n  \
               let helperThm : ConstantInfo := .thmInfo {{\n    \
                 name := `ZZZZLibGood.helper, levelParams := [],\n    \
                 type := .const `True [], value := .const `True.intro [],\n    \
                 all := [`ZZZZLibGood.helper] }}\n  \
               let sharedVal := Expr.letE `_hlp (.const `True [])\n    \
                 (.const `ZZZZLibGood.helper []) (.const `True.intro []) false\n  \
               let sharedThm : ConstantInfo := .thmInfo {{\n    \
                 name := `Target.LibShared, levelParams := [],\n    \
                 type := .const `True [], value := sharedVal,\n    \
                 all := [`Target.LibShared] }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `ZZZZLibGood {{\n    \
                 isModule := false, imports := #[{{ module := `Init.Core }}],\n    \
                 constNames := #[`ZZZZLibGood.helper, `Target.LibShared],\n    \
                 constants := #[helperThm, sharedThm],\n    \
                 extraConstNames := #[], entries := #[] }}\n  \
               let expPath := System.FilePath.mk {:?}\n  \
               let (expData, _) ← readModuleData expPath\n  \
               saveModuleData expPath `Expected {{ expData with\n    \
                 constNames := expData.constNames.push `Target.LibShared,\n    \
                 constants := expData.constants.push sharedThm }}\n",
            lib_ok_olean.to_string_lossy(),
            exp_ok_olean.to_string_lossy(),
        ),
    );
    let lib_ok_arts = ModuleArtifacts::from_available(
        &BTreeMap::from([("olean", lib_ok_olean.to_string_lossy().into_owned())]),
        "fixture",
        String::new,
    )
    .unwrap();
    let adm_ok = c_ok.admitted_mut().unwrap();
    adm_ok.artifacts.insert("ZZZZLibGood".into(), lib_ok_arts);
    adm_ok.library_modules.insert("ZZZZLibGood".into());
    adm_ok.graph.insert(
        "ZZZZLibGood".into(),
        vec![ImportEdge {
            module: "Init.Core".to_string(),
            import_all: false,
            is_exported: true,
            is_meta: false,
        }],
    );
    let ok_rep = c_ok
        .inspect(InspectorRequest::TargetAudit {
            request: f_ok.request.clone(),
        })
        .unwrap();
    assert_eq!(ok_rep["replay"], true, "{ok_rep}");
}
