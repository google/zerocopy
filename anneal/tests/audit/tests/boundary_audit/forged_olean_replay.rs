// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Forged `.olean` keys, duplicate declarations, replay invariants, and
//! foundation axiom hijacking.

use super::*;

/// Verifies Pass-1 and Pass-2 `.olean` replay-key, intra-module duplicate,
/// anonymous declaration, `_unsafe_rec` header parity, `validateReplayMap`
/// (`hasNoDuplicateNames`, missing peers, ctor mismatch),
/// `checkSysrootAlternates`, and `.foundation` `sorryAx` subsumption defenses.
#[test]
fn rejects_forged_olean_keys_dups_replay_invariants_and_foundation_axiom_hijack() {
    use anneal_audit::ImportEdge;

    let fix = TempFixture::new(None);
    fs::create_dir_all(fix.root.join("theory")).unwrap();
    fs::write(
        fix.root.join("theory/Anneal.lean"),
        "prelude\nimport Init.NotationExtra\nimport Trusted\n",
    )
    .unwrap();
    let mut checker = Checker::new(&fix.root, None).unwrap();
    checker.set_require_mir_wp(false);
    checker.run().unwrap();

    let stage = checker.stage().to_path_buf();
    let lib_dir = stage.join("lib");
    let forged_lib = stage.join("forged-pass1-lib");
    fs::create_dir_all(forged_lib.join("Anneal")).unwrap();
    fs::create_dir_all(forged_lib.join("Trusted")).unwrap();
    let orig_arts = checker.admitted().unwrap().artifacts.clone();
    let orig_graph = checker.admitted().unwrap().graph.clone();
    let core_edge = vec![ImportEdge {
        module: "Init.Core".to_string(),
        import_all: false,
        is_exported: true,
        is_meta: false,
    }];

    let inspect_pass1_mod = |checker: &mut Checker,
                             mod_name: &str,
                             olean_path: &Path,
                             is_trusted: bool,
                             edge: Vec<ImportEdge>| {
        let adm = checker.admitted_mut().unwrap();
        adm.artifacts = orig_arts.clone();
        adm.graph = orig_graph.clone();
        let avail = BTreeMap::from([("olean", olean_path.to_string_lossy().into_owned())]);
        let arts = ModuleArtifacts::from_available(&avail, "test", String::new).unwrap();
        adm.artifacts.insert(mod_name.to_string(), arts);
        adm.graph.insert(mod_name.to_string(), edge);
        let (trusted, theory, tiers) = if is_trusted {
            (
                vec!["Trusted".to_string(), mod_name.to_string()],
                vec!["Anneal".to_string()],
                BTreeMap::from([
                    ("Trusted".to_string(), TrustTier::Vetted),
                    (mod_name.to_string(), TrustTier::Vetted),
                ]),
            )
        } else {
            (
                vec!["Trusted".to_string()],
                vec!["Anneal".to_string(), mod_name.to_string()],
                BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
            )
        };
        checker
            .inspect(InspectorRequest::Audit { trusted, theory, module_tiers: tiers })
            .unwrap_err()
    };

    // 1. Checked-env `constNames` key mismatch (`verifyCheckedEnvKeys`).
    let key_olean = forged_lib.join("Anneal/KeyMismatch.olean");
    run_lean_script(
        &mut checker,
        "forge-pass1-key-mismatch",
        &stage.join("forge_pass1_key.lean"),
        &format!(
            "import Lean\nopen Lean in\n\
             def main : IO Unit := do\n  \
               let ci : ConstantInfo := .thmInfo {{\n    \
                 name := `Anneal.KeyMismatch.ok, levelParams := [],\n    \
                 type := .const `True [], value := .const `True.intro [],\n    \
                 all := [`Anneal.KeyMismatch.ok] }}\n  \
               let md : ModuleData := {{\n    \
                 isModule := false, imports := #[{{ module := `Init.Core }}],\n    \
                 constNames := #[`Anneal.KeyMismatch.wrong], constants := #[ci],\n    \
                 extraConstNames := #[], entries := #[] }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Anneal.KeyMismatch md\n",
            key_olean.to_string_lossy()
        ),
    );
    let key_err =
        inspect_pass1_mod(&mut checker, "Anneal.KeyMismatch", &key_olean, false, core_edge.clone());
    assert_eq!((key_err.code, key_err.phase.as_str()), (1, "audit"), "{key_err}");
    assert!(
        key_err.message.contains("mismatched checked environment key"),
        "expected key-mismatch error: {key_err}"
    );

    // 2. Intra-module duplicate declaration (`verifyModuleHeaderInventory`).
    let dup_olean = forged_lib.join("Anneal/DupDecl.olean");
    run_lean_script(
        &mut checker,
        "forge-pass1-dup",
        &stage.join("forge_pass1_dup.lean"),
        &format!(
            "import Lean\nopen Lean in\n\
             def main : IO Unit := do\n  \
               let ci : ConstantInfo := .thmInfo {{\n    \
                 name := `Anneal.DupDecl.t, levelParams := [],\n    \
                 type := .const `True [], value := .const `True.intro [],\n    \
                 all := [`Anneal.DupDecl.t] }}\n  \
               let md : ModuleData := {{\n    \
                 isModule := false, imports := #[{{ module := `Init.Core }}],\n    \
                 constNames := #[`Anneal.DupDecl.t, `Anneal.DupDecl.t],\n    \
                 constants := #[ci, ci], extraConstNames := #[], entries := #[] }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Anneal.DupDecl md\n",
            dup_olean.to_string_lossy()
        ),
    );
    let dup_err =
        inspect_pass1_mod(&mut checker, "Anneal.DupDecl", &dup_olean, false, core_edge.clone());
    assert_eq!((dup_err.code, dup_err.phase.as_str()), (1, "audit"), "{dup_err}");
    assert!(dup_err.message.contains("duplicate declaration Anneal.DupDecl.t"), "{dup_err}");

    // 3. Anonymous declaration rejection (`verifyCheckedEnvKeys` at import).
    let anon_olean = forged_lib.join("Anneal/AnonDecl.olean");
    run_lean_script(
        &mut checker,
        "forge-pass1-anon",
        &stage.join("forge_pass1_anon.lean"),
        &format!(
            "import Lean\nopen Lean in\n\
             def main : IO Unit := do\n  \
               let ci : ConstantInfo := .thmInfo {{\n    \
                 name := .anonymous, levelParams := [],\n    \
                 type := .const `True [], value := .const `True.intro [],\n    \
                 all := [.anonymous] }}\n  \
               let md : ModuleData := {{\n    \
                 isModule := false, imports := #[{{ module := `Init.Core }}],\n    \
                 constNames := #[.anonymous], constants := #[ci],\n    \
                 extraConstNames := #[], entries := #[] }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Anneal.AnonDecl md\n",
            anon_olean.to_string_lossy()
        ),
    );
    let anon_err =
        inspect_pass1_mod(&mut checker, "Anneal.AnonDecl", &anon_olean, false, core_edge.clone());
    assert_eq!((anon_err.code, anon_err.phase.as_str()), (1, "audit"), "{anon_err}");
    assert!(anon_err.message.contains("mismatched checked environment key"), "{anon_err}");

    // 4. Pass-1 `_unsafe_rec` type mismatch (`sameUnsafeRecHeader`).
    let bad_rec_olean = forged_lib.join("Trusted/BadRec.olean");
    run_lean_script(
        &mut checker,
        "forge-pass1-bad-rec",
        &stage.join("forge_pass1_bad_rec.lean"),
        &format!(
            "import Lean\nopen Lean in\n\
             def main : IO Unit := do\n  \
               let parentCi : ConstantInfo := .defnInfo {{\n    \
                 name := `Trusted.BadRec.f, levelParams := [],\n    \
                 type := .const `Nat [], value := .lit (.natVal 0),\n    \
                 hints := .abbrev, safety := .safe, all := [`Trusted.BadRec.f] }}\n  \
               let badRecCi : ConstantInfo := .defnInfo {{\n    \
                 name := `Trusted.BadRec.f._unsafe_rec, levelParams := [],\n    \
                 type := .const `Bool [], value := .const `Bool.true [],\n    \
                 hints := .abbrev, safety := .partial,\n    \
                 all := [`Trusted.BadRec.f._unsafe_rec] }}\n  \
               let md : ModuleData := {{\n    \
                 isModule := false, imports := #[{{ module := `Init.Core }}],\n    \
                 constNames := #[`Trusted.BadRec.f, `Trusted.BadRec.f._unsafe_rec],\n    \
                 constants := #[parentCi, badRecCi],\n    \
                 extraConstNames := #[], entries := #[] }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Trusted.BadRec md\n",
            bad_rec_olean.to_string_lossy()
        ),
    );
    let rec_err =
        inspect_pass1_mod(&mut checker, "Trusted.BadRec", &bad_rec_olean, true, core_edge.clone());
    assert_eq!((rec_err.code, rec_err.phase.as_str()), (1, "audit"), "{rec_err}");
    assert!(
        rec_err.message.contains("unsafe/partial declaration Trusted.BadRec.f._unsafe_rec"),
        "{rec_err}"
    );

    // 5. `validateReplayMap`: forged empty mutual block `all := []`.
    let bad_all_olean = forged_lib.join("Anneal/BadAll.olean");
    run_lean_script(
        &mut checker,
        "forge-pass1-bad-all",
        &stage.join("forge_pass1_bad_all.lean"),
        &format!(
            "import Lean\nopen Lean in\n\
             def main : IO Unit := do\n  \
               let ci : ConstantInfo := .thmInfo {{\n    \
                 name := `Anneal.BadAll.t, levelParams := [],\n    \
                 type := .const `True [], value := .const `True.intro [], all := [] }}\n  \
               let md : ModuleData := {{\n    \
                 isModule := false, imports := #[{{ module := `Init.Core }}],\n    \
                 constNames := #[`Anneal.BadAll.t], constants := #[ci],\n    \
                 extraConstNames := #[], entries := #[] }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Anneal.BadAll md\n",
            bad_all_olean.to_string_lossy()
        ),
    );
    let all_err = inspect_pass1_mod(
        &mut checker,
        "Anneal.BadAll",
        &bad_all_olean,
        false,
        core_edge.clone(),
    );
    assert_eq!((all_err.code, all_err.phase.as_str()), (1, "audit"), "{all_err}");
    assert!(all_err.message.contains("invalid mutual block `all` on Anneal.BadAll.t"), "{all_err}");

    // 5b. `validateReplayMap`: duplicate `all` entry (`hasNoDuplicateNames`),
    //     missing mutual inductive peer, and mismatched constructor `induct`.
    let dup_all_olean = forged_lib.join("Anneal/DupAll.olean");
    run_lean_script(
        &mut checker,
        "forge-pass1-dup-all",
        &stage.join("forge_pass1_dup_all.lean"),
        &format!(
            "import Lean\nopen Lean in\n\
             def main : IO Unit := do\n  \
               let ci : ConstantInfo := .thmInfo {{\n    \
                 name := `Anneal.DupAll.t, levelParams := [],\n    \
                 type := .const `True [], value := .const `True.intro [],\n    \
                 all := [`Anneal.DupAll.t, `Anneal.DupAll.t] }}\n  \
               let md : ModuleData := {{\n    \
                 isModule := false, imports := #[{{ module := `Init.Core }}],\n    \
                 constNames := #[`Anneal.DupAll.t], constants := #[ci],\n    \
                 extraConstNames := #[], entries := #[] }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Anneal.DupAll md\n",
            dup_all_olean.to_string_lossy()
        ),
    );
    let dup_all_err = inspect_pass1_mod(
        &mut checker,
        "Anneal.DupAll",
        &dup_all_olean,
        false,
        core_edge.clone(),
    );
    assert_eq!((dup_all_err.code, dup_all_err.phase.as_str()), (1, "audit"), "{dup_all_err}");
    assert!(
        dup_all_err.message.contains("invalid mutual block `all` on Anneal.DupAll.t"),
        "{dup_all_err}"
    );

    let miss_peer_olean = forged_lib.join("Anneal/MissPeer.olean");
    run_lean_script(
        &mut checker,
        "forge-pass1-miss-peer",
        &stage.join("forge_pass1_miss_peer.lean"),
        &format!(
            "import Lean\nopen Lean in\n\
             def main : IO Unit := do\n  \
               let indCi : ConstantInfo := .inductInfo {{\n    \
                 name := `Anneal.MissPeer.Ind, levelParams := [],\n    \
                 type := .sort (.succ .zero), numParams := 0, numIndices := 0,\n    \
                 all := [`Anneal.MissPeer.Ind, `Anneal.MissPeer.Other],\n    \
                 ctors := [], numNested := 0, isRec := false,\n    \
                 isUnsafe := false, isReflexive := false }}\n  \
               let otherCi : ConstantInfo := .defnInfo {{\n    \
                 name := `Anneal.MissPeer.Other, levelParams := [],\n    \
                 type := .sort .zero, value := .const `True [],\n    \
                 hints := .abbrev, safety := .safe, all := [`Anneal.MissPeer.Other] }}\n  \
               let md : ModuleData := {{\n    \
                 isModule := false, imports := #[{{ module := `Init.Core }}],\n    \
                 constNames := #[`Anneal.MissPeer.Ind, `Anneal.MissPeer.Other],\n    \
                 constants := #[indCi, otherCi],\n    \
                 extraConstNames := #[], entries := #[] }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Anneal.MissPeer md\n",
            miss_peer_olean.to_string_lossy()
        ),
    );
    let peer_err = inspect_pass1_mod(
        &mut checker,
        "Anneal.MissPeer",
        &miss_peer_olean,
        false,
        core_edge.clone(),
    );
    assert_eq!((peer_err.code, peer_err.phase.as_str()), (1, "audit"), "{peer_err}");
    assert!(
        peer_err.message.contains("missing mutual inductive peer Anneal.MissPeer.Other"),
        "{peer_err}"
    );

    let bad_ctor_olean = forged_lib.join("Anneal/BadCtor.olean");
    run_lean_script(
        &mut checker,
        "forge-pass1-bad-ctor",
        &stage.join("forge_pass1_bad_ctor.lean"),
        &format!(
            "import Lean\nopen Lean in\n\
             def main : IO Unit := do\n  \
               let indCi : ConstantInfo := .inductInfo {{\n    \
                 name := `Anneal.BadCtor.Ind, levelParams := [],\n    \
                 type := .sort (.succ .zero), numParams := 0, numIndices := 0,\n    \
                 all := [`Anneal.BadCtor.Ind], ctors := [`Anneal.BadCtor.Ind.mk],\n    \
                 numNested := 0, isRec := false, isUnsafe := false,\n    \
                 isReflexive := false }}\n  \
               let ctorCi : ConstantInfo := .ctorInfo {{\n    \
                 name := `Anneal.BadCtor.Ind.mk, levelParams := [],\n    \
                 type := .const `Anneal.BadCtor.Ind [],\n    \
                 induct := `Anneal.BadCtor.WrongInd, cidx := 0,\n    \
                 numParams := 0, numFields := 0, isUnsafe := false }}\n  \
               let wrongIndCi : ConstantInfo := .inductInfo {{\n    \
                 name := `Anneal.BadCtor.WrongInd, levelParams := [],\n    \
                 type := .sort (.succ .zero), numParams := 0, numIndices := 0,\n    \
                 all := [`Anneal.BadCtor.WrongInd], ctors := [`Anneal.BadCtor.Ind.mk],\n    \
                 numNested := 0, isRec := false, isUnsafe := false,\n    \
                 isReflexive := false }}\n  \
               let md : ModuleData := {{\n    \
                 isModule := false, imports := #[{{ module := `Init.Core }}],\n    \
                 constNames := #[`Anneal.BadCtor.Ind, `Anneal.BadCtor.Ind.mk,\n      \
                   `Anneal.BadCtor.WrongInd],\n    \
                 constants := #[indCi, ctorCi, wrongIndCi], extraConstNames := #[],\n    \
                 entries := #[] }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Anneal.BadCtor md\n",
            bad_ctor_olean.to_string_lossy()
        ),
    );
    let ctor_err =
        inspect_pass1_mod(&mut checker, "Anneal.BadCtor", &bad_ctor_olean, false, core_edge.clone());
    assert_eq!((ctor_err.code, ctor_err.phase.as_str()), (1, "audit"), "{ctor_err}");
    assert!(
        ctor_err
            .message
            .contains("constructor Anneal.BadCtor.Ind.mk points to Anneal.BadCtor.WrongInd"),
        "{ctor_err}"
    );

    let asym_all_olean = forged_lib.join("Anneal/AsymAll.olean");
    run_lean_script(
        &mut checker,
        "forge-pass1-asym-all",
        &stage.join("forge_pass1_asym_all.lean"),
        &format!(
            "import Lean\nopen Lean in\n\
             def main : IO Unit := do\n  \
               let indA : ConstantInfo := .inductInfo {{\n    \
                 name := `Anneal.AsymAll.A, levelParams := [],\n    \
                 type := .sort (.succ .zero), numParams := 0, numIndices := 0,\n    \
                 all := [`Anneal.AsymAll.A, `Anneal.AsymAll.B], ctors := [],\n    \
                 numNested := 0, isRec := false, isUnsafe := false,\n    \
                 isReflexive := false }}\n  \
               let indB : ConstantInfo := .inductInfo {{\n    \
                 name := `Anneal.AsymAll.B, levelParams := [],\n    \
                 type := .sort (.succ .zero), numParams := 0, numIndices := 0,\n    \
                 all := [`Anneal.AsymAll.B], ctors := [],\n    \
                 numNested := 0, isRec := false, isUnsafe := false,\n    \
                 isReflexive := false }}\n  \
               let md : ModuleData := {{\n    \
                 isModule := false, imports := #[{{ module := `Init.Core }}],\n    \
                 constNames := #[`Anneal.AsymAll.A, `Anneal.AsymAll.B],\n    \
                 constants := #[indA, indB], extraConstNames := #[], entries := #[] }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Anneal.AsymAll md\n",
            asym_all_olean.to_string_lossy()
        ),
    );
    let asym_err = inspect_pass1_mod(
        &mut checker,
        "Anneal.AsymAll",
        &asym_all_olean,
        false,
        core_edge.clone(),
    );
    assert_eq!((asym_err.code, asym_err.phase.as_str()), (1, "audit"), "{asym_err}");
    assert!(
        asym_err.message.contains("asymmetric mutual `all` on Anneal.AsymAll.B"),
        "{asym_err}"
    );

    let miss_ctor_olean = forged_lib.join("Anneal/MissCtor.olean");
    run_lean_script(
        &mut checker,
        "forge-pass1-miss-ctor",
        &stage.join("forge_pass1_miss_ctor.lean"),
        &format!(
            "import Lean\nopen Lean in\n\
             def main : IO Unit := do\n  \
               let indCi : ConstantInfo := .inductInfo {{\n    \
                 name := `Anneal.MissCtor.Ind, levelParams := [],\n    \
                 type := .sort (.succ .zero), numParams := 0, numIndices := 0,\n    \
                 all := [`Anneal.MissCtor.Ind], ctors := [`True.intro],\n    \
                 numNested := 0, isRec := false, isUnsafe := false,\n    \
                 isReflexive := false }}\n  \
               let md : ModuleData := {{\n    \
                 isModule := false, imports := #[{{ module := `Init.Core }}],\n    \
                 constNames := #[`Anneal.MissCtor.Ind],\n    \
                 constants := #[indCi], extraConstNames := #[], entries := #[] }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Anneal.MissCtor md\n",
            miss_ctor_olean.to_string_lossy()
        ),
    );
    let miss_ctor_err = inspect_pass1_mod(
        &mut checker,
        "Anneal.MissCtor",
        &miss_ctor_olean,
        false,
        core_edge.clone(),
    );
    assert_eq!((miss_ctor_err.code, miss_ctor_err.phase.as_str()), (1, "audit"), "{miss_ctor_err}");
    assert!(
        miss_ctor_err
            .message
            .contains("missing constructor True.intro for Anneal.MissCtor.Ind"),
        "{miss_ctor_err}"
    );

    // 5c. Remaining `validateReplayMap` ctor/recursor branches
    //     (`expected constructor`, `missing from`, `missing inductive`,
    //     `recursor ... all`, and `missing inductive ... for recursor`).
    let non_ctor_olean = forged_lib.join("Anneal/NonCtor.olean");
    let ctor_miss_from_olean = forged_lib.join("Anneal/CtorMissingFromInd.olean");
    let miss_ctor_ind_olean = forged_lib.join("Anneal/MissCtorInd.olean");
    let rec_all_diff_olean = forged_lib.join("Anneal/RecAllDiff.olean");
    let rec_miss_ind_olean = forged_lib.join("Anneal/RecMissInd.olean");
    run_lean_script(
        &mut checker,
        "forge-pass1-replay-variants",
        &stage.join("forge_pass1_replay_variants.lean"),
        &format!(
            "import Lean\nopen Lean in\n\
             def main : IO Unit := do\n  \
               let imp := #[{{ module := `Init.Core : Import }}]\n  \
               let indNonCtor : ConstantInfo := .inductInfo {{\n    \
                 name := `Anneal.NonCtor.Ind, levelParams := [],\n    \
                 type := .sort (.succ .zero), numParams := 0, numIndices := 0,\n    \
                 all := [`Anneal.NonCtor.Ind], ctors := [`Anneal.NonCtor.NotACtor],\n    \
                 numNested := 0, isRec := false, isUnsafe := false,\n    \
                 isReflexive := false }}\n  \
               let notACtor : ConstantInfo := .thmInfo {{\n    \
                 name := `Anneal.NonCtor.NotACtor, levelParams := [],\n    \
                 type := .const `True [], value := .const `True.intro [],\n    \
                 all := [`Anneal.NonCtor.NotACtor] }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Anneal.NonCtor {{\n    \
                 isModule := false, imports := imp,\n    \
                 constNames := #[`Anneal.NonCtor.Ind, `Anneal.NonCtor.NotACtor],\n    \
                 constants := #[indNonCtor, notACtor],\n    \
                 extraConstNames := #[], entries := #[] }}\n  \
               let indEmpty : ConstantInfo := .inductInfo {{\n    \
                 name := `Anneal.CtorMissingFromInd.Ind, levelParams := [],\n    \
                 type := .sort (.succ .zero), numParams := 0, numIndices := 0,\n    \
                 all := [`Anneal.CtorMissingFromInd.Ind], ctors := [],\n    \
                 numNested := 0, isRec := false, isUnsafe := false,\n    \
                 isReflexive := false }}\n  \
               let strayedCtor : ConstantInfo := .ctorInfo {{\n    \
                 name := `Anneal.CtorMissingFromInd.mk, levelParams := [],\n    \
                 type := .const `True [],\n    \
                 induct := `Anneal.CtorMissingFromInd.Ind, cidx := 0,\n    \
                 numParams := 0, numFields := 0, isUnsafe := false }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Anneal.CtorMissingFromInd {{\n    \
                 isModule := false, imports := imp,\n    \
                 constNames := #[`Anneal.CtorMissingFromInd.Ind,\n      \
                   `Anneal.CtorMissingFromInd.mk],\n    \
                 constants := #[indEmpty, strayedCtor],\n    \
                 extraConstNames := #[], entries := #[] }}\n  \
               let orphanCtor : ConstantInfo := .ctorInfo {{\n    \
                 name := `Anneal.MissCtorInd.mk, levelParams := [],\n    \
                 type := .const `True [], induct := `True, cidx := 0,\n    \
                 numParams := 0, numFields := 0, isUnsafe := false }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Anneal.MissCtorInd {{\n    \
                 isModule := false, imports := imp,\n    \
                 constNames := #[`Anneal.MissCtorInd.mk], constants := #[orphanCtor],\n    \
                 extraConstNames := #[], entries := #[] }}\n  \
               let indA : ConstantInfo := .inductInfo {{\n    \
                 name := `Anneal.RecAllDiff.IndA, levelParams := [],\n    \
                 type := .sort (.succ .zero), numParams := 0, numIndices := 0,\n    \
                 all := [`Anneal.RecAllDiff.IndA, `Anneal.RecAllDiff.IndB],\n    \
                 ctors := [], numNested := 0, isRec := false,\n    \
                 isUnsafe := false, isReflexive := false }}\n  \
               let indB : ConstantInfo := .inductInfo {{\n    \
                 name := `Anneal.RecAllDiff.IndB, levelParams := [],\n    \
                 type := .sort (.succ .zero), numParams := 0, numIndices := 0,\n    \
                 all := [`Anneal.RecAllDiff.IndA, `Anneal.RecAllDiff.IndB],\n    \
                 ctors := [], numNested := 0, isRec := false,\n    \
                 isUnsafe := false, isReflexive := false }}\n  \
               let badRec : ConstantInfo := .recInfo {{\n    \
                 name := `Anneal.RecAllDiff.rec, levelParams := [],\n    \
                 type := .const `True [], all := [`Anneal.RecAllDiff.IndA],\n    \
                 numParams := 0, numIndices := 0, numMotives := 0, numMinors := 0,\n    \
                 rules := [], k := false, isUnsafe := false }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Anneal.RecAllDiff {{\n    \
                 isModule := false, imports := imp,\n    \
                 constNames := #[`Anneal.RecAllDiff.IndA, `Anneal.RecAllDiff.IndB,\n      \
                   `Anneal.RecAllDiff.rec],\n    \
                 constants := #[indA, indB, badRec],\n    \
                 extraConstNames := #[], entries := #[] }}\n  \
               let orphanRec : ConstantInfo := .recInfo {{\n    \
                 name := `Anneal.RecMissInd.rec, levelParams := [],\n    \
                 type := .const `True [], all := [`True],\n    \
                 numParams := 0, numIndices := 0, numMotives := 0, numMinors := 0,\n    \
                 rules := [], k := false, isUnsafe := false }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Anneal.RecMissInd {{\n    \
                 isModule := false, imports := imp,\n    \
                 constNames := #[`Anneal.RecMissInd.rec], constants := #[orphanRec],\n    \
                 extraConstNames := #[], entries := #[] }}\n",
            non_ctor_olean.to_string_lossy(),
            ctor_miss_from_olean.to_string_lossy(),
            miss_ctor_ind_olean.to_string_lossy(),
            rec_all_diff_olean.to_string_lossy(),
            rec_miss_ind_olean.to_string_lossy()
        ),
    );
    for (mod_name, olean_path, expected_msg) in [
        (
            "Anneal.NonCtor",
            &non_ctor_olean,
            "expected constructor Anneal.NonCtor.NotACtor for Anneal.NonCtor.Ind",
        ),
        (
            "Anneal.CtorMissingFromInd",
            &ctor_miss_from_olean,
            "constructor Anneal.CtorMissingFromInd.mk missing from \
             Anneal.CtorMissingFromInd.Ind",
        ),
        (
            "Anneal.MissCtorInd",
            &miss_ctor_ind_olean,
            "missing inductive True for Anneal.MissCtorInd.mk",
        ),
        (
            "Anneal.RecAllDiff",
            &rec_all_diff_olean,
            "recursor Anneal.RecAllDiff.rec `all` differs from Anneal.RecAllDiff.IndA",
        ),
        (
            "Anneal.RecMissInd",
            &rec_miss_ind_olean,
            "missing inductive True for recursor Anneal.RecMissInd.rec",
        ),
    ] {
        let err = inspect_pass1_mod(&mut checker, mod_name, olean_path, false, core_edge.clone());
        assert_eq!((err.code, err.phase.as_str()), (1, "audit"), "{err}");
        assert!(err.message.contains(expected_msg), "expected `{expected_msg}`, got: {err}");
    }

    // 6. Pass-2 `sorryAx` axiom-to-theorem `subsumesInfo` hijack rejected by
    //    `verifyAndCollectCorrLocals` `.foundation` reconciliation.
    let prefix = checker.admitted().unwrap().prefix.clone();
    let corr_lib = stage.join("hijack-corr-lib");
    let corr_proof_olean = corr_lib.join("Anneal/MirCorrespondenceProof.olean");
    fs::create_dir_all(corr_proof_olean.parent().unwrap()).unwrap();
    run_lean_script(
        &mut checker,
        "forge-pass2-sorry-hijack",
        &stage.join("forge_pass2_sorry_hijack.lean"),
        &format!(
            "import Lean.Environment\nopen Lean in\n\
             def main : IO Unit := do\n  \
               initSearchPath (System.FilePath.mk {:?})\n  \
               let env ← importModules #[{{ module := `Init.Prelude }}] {{}} \
                 (trustLevel := 0) (plugins := #[]) (loadExts := false) \
                 (level := .private)\n  \
               let some sax := env.checked.get.find? `sorryAx \
                 | throw (IO.userError \"missing sorryAx\")\n  \
               let body := Expr.lam `α (.sort (.succ .zero)) \
                 (.lam `synthetic (.const `Bool []) (.const `True []) .default) .implicit\n  \
               let fakeThm : ConstantInfo := .thmInfo {{\n    \
                 name := `sorryAx, levelParams := sax.levelParams,\n    \
                 type := sax.type, value := body, all := [`sorryAx] }}\n  \
               let md : ModuleData := {{\n    \
                 isModule := false, imports := #[{{ module := `Init.Prelude }}],\n    \
                 constNames := #[`sorryAx], constants := #[fakeThm],\n    \
                 extraConstNames := #[], entries := #[] }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Anneal.MirCorrespondenceProof md\n",
            prefix.to_string_lossy(),
            corr_proof_olean.to_string_lossy()
        ),
    );
    let hijack_err = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: vec![lib_dir.clone(), corr_lib],
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: vec!["Anneal.MirCorrespondenceProof".to_string()],
            vendor_miri: Vec::new(),
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert_eq!(
        (hijack_err.code, hijack_err.phase.as_str()),
        (1, "correspondence-audit"),
        "{hijack_err}"
    );
    assert!(
        hijack_err.message.contains("stored declaration differs from inventory sorryAx"),
        "expected foundation sorryAx hijack rejection, got: {hijack_err}"
    );

    // 7. `checkExternalAlternates`: a `.repo (.trusted .vetted)` proof
    //    replacing foundation `Iff.refl` via `subsumesInfo` with a body
    //    referencing `.repo .theory` constant `Anneal.Helper.h` fails closed in
    //    both Pass 2 and Pass 1 (`"Trusted constant Iff.refl references ..."`),
    //    while a legitimate `.repo .theory` realized theorem referencing
    //    `Anneal.Helper.h` passes Pass-1 end-to-end replay and checks both
    //    alternates via `checkAlternateProofs`.
    let alt_lib = stage.join("alt-edge-corr-lib");
    let helper_olean = alt_lib.join("Anneal/Helper.olean");
    let alt_trusted_olean = alt_lib.join("BadTrusted/ForgedAlt.olean");
    let alt_theory_olean = alt_lib.join("Anneal/RealizedAlt.olean");
    fs::create_dir_all(helper_olean.parent().unwrap()).unwrap();
    fs::create_dir_all(alt_trusted_olean.parent().unwrap()).unwrap();
    run_lean_script(
        &mut checker,
        "forge-pass2-alt-edge",
        &stage.join("forge_pass2_alt_edge.lean"),
        &format!(
            "import Lean.Environment\nopen Lean in\n\
             def main : IO Unit := do\n  \
               initSearchPath (System.FilePath.mk {:?})\n  \
               let env ← importModules #[{{ module := `Init.NotationExtra }}] {{}} \
                 (trustLevel := 0) (plugins := #[]) (loadExts := false) \
                 (level := .private)\n  \
               let some iffRefl := env.checked.get.find? `Iff.refl \
                 | throw (IO.userError \"missing Iff.refl\")\n  \
               let some (.thmInfo dropEq) := env.checked.get.find? `List.drop.eq_def \
                 | throw (IO.userError \"missing List.drop.eq_def\")\n  \
               let helperCi : ConstantInfo := .defnInfo {{\n    \
                 name := `Anneal.Helper.h, levelParams := [],\n    \
                 type := .const `True [], value := .const `True.intro [],\n    \
                 hints := .abbrev, safety := .safe, all := [`Anneal.Helper.h] }}\n  \
               let helperMd : ModuleData := {{\n    \
                 isModule := false, imports := #[{{ module := `Init.Core }}],\n    \
                 constNames := #[`Anneal.Helper.h], constants := #[helperCi],\n    \
                 extraConstNames := #[], entries := #[] }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Anneal.Helper helperMd\n  \
               let altBody := Expr.lam `a (.sort .zero)\n    \
                 (mkApp2 (.const `Iff.intro []) (.bvar 0) (.bvar 0)\n      \
                   |> fun _ => mkApp2 (.const `Iff.intro [])\n        \
                     (.lam `x (.bvar 0) (.bvar 0) .default)\n        \
                     (.lam `y (.bvar 0) (.bvar 0) .default))\n    \
                 .default\n  \
               let wrappedBody := Expr.lam `a (.sort .zero)\n    \
                 (.app (.lam `_ (.const `True [])\n      \
                   (.app altBody (.bvar 1)) .default) (.const `Anneal.Helper.h []))\n    \
                 .default\n  \
               let forgedRefl : ConstantInfo := .thmInfo {{\n    \
                 name := `Iff.refl, levelParams := iffRefl.levelParams,\n    \
                 type := iffRefl.type, value := wrappedBody, all := [`Iff.refl] }}\n  \
               let trustedMd : ModuleData := {{\n    \
                 isModule := false,\n    \
                 imports := #[{{ module := `Init.Core }}],\n    \
                 constNames := #[`Iff.refl], constants := #[forgedRefl],\n    \
                 extraConstNames := #[], entries := #[] }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `BadTrusted.ForgedAlt trustedMd\n  \
               let wrappedDrop := .app (.lam `_ (.const `True [])\n    \
                 dropEq.value .default) (.const `Anneal.Helper.h [])\n  \
               let realizedDrop : ConstantInfo := .thmInfo {{\n    \
                 dropEq with value := wrappedDrop }}\n  \
               let theoryMd : ModuleData := {{\n    \
                 isModule := false,\n    \
                 imports := #[{{ module := `Init.NotationExtra }}, {{ module := `Anneal.Helper }}],\n    \
                 constNames := #[`List.drop.eq_def], constants := #[realizedDrop],\n    \
                 extraConstNames := #[], entries := #[] }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Anneal.RealizedAlt theoryMd\n",
            prefix.to_string_lossy(),
            helper_olean.to_string_lossy(),
            alt_trusted_olean.to_string_lossy(),
            alt_theory_olean.to_string_lossy()
        ),
    );
    let alt_err = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: vec![lib_dir.clone(), alt_lib.clone()],
            trusted: vec!["Trusted".to_string(), "BadTrusted.ForgedAlt".to_string()],
            corr_trusted: Vec::new(),
            theory: vec!["Anneal.Helper".to_string()],
            corr_theory: Vec::new(),
            vendor_miri: Vec::new(),
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                ("BadTrusted.ForgedAlt".to_string(), TrustTier::Vetted),
            ]),
        })
        .unwrap_err();
    assert_eq!((alt_err.code, alt_err.phase.as_str()), (1, "correspondence-audit"), "{alt_err}");
    assert!(
        alt_err.message.contains(
            "Trusted constant Iff.refl references Anneal.Helper.h from non-Trusted module Anneal.Helper"
        ),
        "expected checkExternalAlternates Trusted authority rejection, got: {alt_err}"
    );

    // 8. Pass-1 `verifyAndCollectLocals` rejects `.repo (.trusted .vetted)`
    //    `subsumesInfo` alternates referencing `.repo .theory`, accepts
    //    legitimate `.repo .theory` realized theorem copies referencing
    //    `.repo .theory` helpers while kernel-checking both alternates, and
    //    both Pass 1 and Pass 2 reject `.repo` declarations injected under
    //    `.foundation` or `.sysrootFoundation` `extraConstNames` IR helpers.
    {
        let adm = checker.admitted_mut().unwrap();
        adm.artifacts = orig_arts.clone();
        adm.graph = orig_graph.clone();
        let helper_avail =
            BTreeMap::from([("olean", helper_olean.to_string_lossy().into_owned())]);
        let trusted_alt_avail =
            BTreeMap::from([("olean", alt_trusted_olean.to_string_lossy().into_owned())]);
        adm.artifacts.insert(
            "Anneal.Helper".to_string(),
            ModuleArtifacts::from_available(&helper_avail, "test", String::new).unwrap(),
        );
        adm.artifacts.insert(
            "BadTrusted.ForgedAlt".to_string(),
            ModuleArtifacts::from_available(&trusted_alt_avail, "test", String::new).unwrap(),
        );
        adm.graph.insert("Anneal.Helper".to_string(), core_edge.clone());
        adm.graph.insert("BadTrusted.ForgedAlt".to_string(), core_edge.clone());
    }
    let pass1_alt_err = checker
        .inspect(InspectorRequest::Audit {
            trusted: vec!["Trusted".to_string(), "BadTrusted.ForgedAlt".to_string()],
            theory: vec!["Anneal".to_string(), "Anneal.Helper".to_string()],
            module_tiers: BTreeMap::from([
                ("Trusted".to_string(), TrustTier::Vetted),
                ("BadTrusted.ForgedAlt".to_string(), TrustTier::Vetted),
            ]),
        })
        .unwrap_err();
    assert_eq!(
        (pass1_alt_err.code, pass1_alt_err.phase.as_str()),
        (1, "audit"),
        "{pass1_alt_err}"
    );
    assert!(
        pass1_alt_err.message.contains(
            "Trusted constant Iff.refl references Anneal.Helper.h from non-Trusted module Anneal.Helper"
        ),
        "expected Pass-1 Trusted realized-theorem authority rejection, got: {pass1_alt_err}"
    );
    {
        let adm = checker.admitted_mut().unwrap();
        adm.artifacts.remove("BadTrusted.ForgedAlt");
        adm.graph.remove("BadTrusted.ForgedAlt");
        let theory_alt_avail =
            BTreeMap::from([("olean", alt_theory_olean.to_string_lossy().into_owned())]);
        adm.artifacts.insert(
            "Anneal.RealizedAlt".to_string(),
            ModuleArtifacts::from_available(&theory_alt_avail, "test", String::new).unwrap(),
        );
        adm.graph.insert(
            "Anneal.RealizedAlt".to_string(),
            vec![
                ImportEdge {
                    module: "Init.NotationExtra".to_string(),
                    import_all: false,
                    is_exported: true,
                    is_meta: false,
                },
                ImportEdge {
                    module: "Anneal.Helper".to_string(),
                    import_all: false,
                    is_exported: true,
                    is_meta: false,
                },
            ],
        );
    }
    let pass1_theory_ok = checker
        .inspect(InspectorRequest::Audit {
            trusted: vec!["Trusted".to_string()],
            theory: vec![
                "Anneal".to_string(),
                "Anneal.Helper".to_string(),
                "Anneal.RealizedAlt".to_string(),
            ],
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap();
    assert_eq!(pass1_theory_ok["replay"].as_bool(), Some(true));
    assert!(
        pass1_theory_ok["checkedAlternateProofs"].as_u64().unwrap_or(0) >= 2,
        "expected Pass-1 checkAlternateProofs to check both realized List.drop.eq_def copies: {pass1_theory_ok}"
    );

    let extra_lib = stage.join("extra-collide-lib");
    let fnd_extra_olean = extra_lib.join("Anneal/ExtraCollide.olean");
    let sys_extra_olean = extra_lib.join("Anneal/SysrootExtraCollide.olean");
    fs::create_dir_all(fnd_extra_olean.parent().unwrap()).unwrap();
    run_lean_script(
        &mut checker,
        "forge-extra-collide",
        &stage.join("forge_extra_collide.lean"),
        &format!(
            "import Lean.Environment\nopen Lean in\n\
             def main : IO Unit := do\n  \
               initSearchPath (System.FilePath.mk {:?})\n  \
               let badFnd : ConstantInfo := .thmInfo {{\n    \
                 name := `mixHash._boxed, levelParams := [],\n    \
                 type := .const `False [], value := .const `True.intro [],\n    \
                 all := [`mixHash._boxed] }}\n  \
               let mdFnd : ModuleData := {{\n    \
                 isModule := false, imports := #[{{ module := `Init.Prelude }}],\n    \
                 constNames := #[`mixHash._boxed], constants := #[badFnd],\n    \
                 extraConstNames := #[], entries := #[] }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Anneal.ExtraCollide mdFnd\n  \
               let env ← importModules #[{{ module := `Std.Data.HashMap.Basic }}] {{}} \
                 (trustLevel := 0) (plugins := #[]) (loadExts := false) \
                 (level := .private)\n  \
               let mut picked : Option Name := none\n  \
               for m in env.header.modules, d in env.header.moduleData do\n    \
                 if m.module == `Std.Data.HashMap.Basic then\n      \
                   let modSet : NameSet := .ofList d.constNames.toList\n      \
                   for n in d.extraConstNames do\n        \
                     if !modSet.contains n && (env.checked.get.find? n).isNone &&\n          \
                         env.getModuleIdxFor? n != none then\n          \
                       picked := some n\n          \
                       break\n  \
               let some sysHelper := picked\n    \
                 | throw (IO.userError \"missing Std.Data.HashMap.Basic IR-only helper\")\n  \
               let badSys : ConstantInfo := .thmInfo {{\n    \
                 name := sysHelper, levelParams := [],\n    \
                 type := .const `False [], value := .const `True.intro [],\n    \
                 all := [sysHelper] }}\n  \
               let mdSys : ModuleData := {{\n    \
                 isModule := false,\n    \
                 imports := #[{{ module := `Std.Data.HashMap.Basic }}],\n    \
                 constNames := #[sysHelper], constants := #[badSys],\n    \
                 extraConstNames := #[], entries := #[] }}\n  \
               saveModuleData (System.FilePath.mk {:?}) `Anneal.SysrootExtraCollide mdSys\n",
            prefix.to_string_lossy(),
            fnd_extra_olean.to_string_lossy(),
            sys_extra_olean.to_string_lossy()
        ),
    );
    let prelude_edge = vec![ImportEdge {
        module: "Init.Prelude".to_string(),
        import_all: false,
        is_exported: true,
        is_meta: false,
    }];
    let p1_extra_err = inspect_pass1_mod(
        &mut checker,
        "Anneal.ExtraCollide",
        &fnd_extra_olean,
        false,
        prelude_edge,
    );
    assert_eq!(
        (p1_extra_err.code, p1_extra_err.phase.as_str()),
        (1, "audit"),
        "{p1_extra_err}"
    );
    assert!(
        p1_extra_err
            .message
            .contains("uninventoried kernel compiler helper mixHash._boxed"),
        "expected Pass-1 foundation extraConstNames rejection, got: {p1_extra_err}"
    );

    let p2_fnd_extra_err = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: vec![lib_dir.clone(), extra_lib.clone()],
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: vec!["Anneal.ExtraCollide".to_string()],
            vendor_miri: Vec::new(),
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert_eq!(
        (p2_fnd_extra_err.code, p2_fnd_extra_err.phase.as_str()),
        (1, "correspondence-audit"),
        "{p2_fnd_extra_err}"
    );
    assert!(
        p2_fnd_extra_err
            .message
            .contains("uninventoried kernel compiler helper mixHash._boxed"),
        "expected Pass-2 foundation extraConstNames rejection, got: {p2_fnd_extra_err}"
    );

    let p2_sys_extra_err = checker
        .inspect(InspectorRequest::CorrespondenceAudit {
            search_path: vec![lib_dir.clone(), extra_lib],
            trusted: vec!["Trusted".to_string()],
            corr_trusted: Vec::new(),
            theory: Vec::new(),
            corr_theory: vec!["Anneal.SysrootExtraCollide".to_string()],
            vendor_miri: Vec::new(),
            module_tiers: BTreeMap::from([("Trusted".to_string(), TrustTier::Vetted)]),
        })
        .unwrap_err();
    assert_eq!(
        (p2_sys_extra_err.code, p2_sys_extra_err.phase.as_str()),
        (1, "correspondence-audit"),
        "{p2_sys_extra_err}"
    );
    assert!(
        p2_sys_extra_err
            .message
            .contains("uninventoried kernel compiler helper"),
        "expected Pass-2 sysroot extraConstNames rejection, got: {p2_sys_extra_err}"
    );

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

    // 12. Direct `verifyAndCollectCorrLocals` probe confirming that
    //     `buildStoredRoleMap` checks a late `.foundation` alternate's edges
    //     under `.foundation` even when an earlier `.sysrootFoundation` module
    //     also alternates.
    let probe_dir = stage.join("p2-sysroot-alt-order");
    fs::create_dir_all(&probe_dir).unwrap();
    let inspector = checker.tool_admission().unwrap().inspector.clone();
    let mut probe_src = fs::read_to_string(inspector).unwrap();
    probe_src.push_str(&format!(
        r#"

#eval
  show IO Unit from do
    let dir := System.FilePath.mk {:?}
    let propImp : Lean.Expr := .forallE `x (.sort .zero) (.sort .zero) .default
    let idLam : Lean.Expr := .lam `x (.sort .zero) (.bvar 0) .default
    let m0 : Lean.ConstantInfo := .thmInfo {{
      name := `External.Alt.t, levelParams := [],
      type := propImp, value := idLam,
      all := [`External.Alt.t] }}
    let sysHelper : Lean.ConstantInfo := .thmInfo {{
      name := `External.SysHelper.t, levelParams := [],
      type := propImp, value := idLam,
      all := [`External.SysHelper.t] }}
    let altVal := Lean.Expr.letE `h propImp
      (.const `External.SysHelper.t []) idLam false
    let altThm : Lean.ConstantInfo := .thmInfo {{
      name := `External.Alt.t, levelParams := [],
      type := propImp, value := altVal,
      all := [`External.Alt.t] }}
    let altVal2 := Lean.Expr.letE `h2 propImp altVal idLam false
    let altThm2 : Lean.ConstantInfo := .thmInfo {{
      name := `External.Alt.t, levelParams := [],
      type := propImp, value := altVal2,
      all := [`External.Alt.t] }}
    Lean.saveModuleData (dir / "F0.olean") `External.F0 {{
      isModule := false, imports := #[],
      constNames := #[`External.Alt.t], constants := #[m0],
      extraConstNames := #[], entries := #[] }}
    Lean.saveModuleData (dir / "SysH.olean") `External.SysHelper {{
      isModule := false, imports := #[],
      constNames := #[`External.SysHelper.t], constants := #[sysHelper],
      extraConstNames := #[], entries := #[] }}
    Lean.saveModuleData (dir / "SysA.olean") `External.SysAlt {{
      isModule := false,
      imports := #[{{ module := `External.F0 }}, {{ module := `External.SysHelper }}],
      constNames := #[`External.Alt.t], constants := #[altThm],
      extraConstNames := #[], entries := #[] }}
    Lean.saveModuleData (dir / "F1.olean") `External.F1 {{
      isModule := false, imports := #[],
      constNames := #[`External.Alt.t], constants := #[altThm2],
      extraConstNames := #[], entries := #[] }}
    Lean.saveModuleData (dir / "DrvOk.olean") `Anneal.DrvOk {{
      isModule := false, imports := #[{{ module := `External.SysAlt }}],
      constNames := #[], constants := #[],
      extraConstNames := #[], entries := #[] }}
    Lean.saveModuleData (dir / "DrvBad.olean") `Anneal.DrvBad {{
      isModule := false,
      imports := #[{{ module := `External.SysAlt }}, {{ module := `External.F1 }}],
      constNames := #[], constants := #[],
      extraConstNames := #[], entries := #[] }}
    let mut arts : Lean.NameMap Lean.ImportArtifacts := {{}}
    for (n, f) in [(`External.F0, "F0.olean"), (`External.SysHelper, "SysH.olean"),
        (`External.SysAlt, "SysA.olean"), (`External.F1, "F1.olean"),
        (`Anneal.DrvOk, "DrvOk.olean"), (`Anneal.DrvBad, "DrvBad.olean")] do
      arts := arts.insert n (Lean.ImportArtifacts.ofArrays #[#[dir / f], #[]])
    let baseRoles : Std.HashMap Lean.Name TrustedBoundary.CorrOrigin :=
      Std.HashMap.ofList [
        (`External.F0, .foundation),
        (`External.SysHelper, .sysrootFoundation),
        (`External.SysAlt, .sysrootFoundation),
        (`External.F1, .foundation),
        (`Anneal.DrvOk, .repo .theory),
        (`Anneal.DrvBad, .repo .theory)]
    let envOk ← Lean.importModules #[{{ module := `Anneal.DrvOk }}] {{}}
      (trustLevel := 0) (plugins := #[]) (loadExts := false)
      (level := .private) (arts := arts)
    let envOk ← TrustedBoundary.finalizeImportedEnv envOk
    let _ ← TrustedBoundary.verifyAndCollectCorrLocals envOk baseRoles {{}}
    let envBad ← Lean.importModules #[{{ module := `Anneal.DrvBad }}] {{}}
      (trustLevel := 0) (plugins := #[]) (loadExts := false)
      (level := .private) (arts := arts)
    let envBad ← TrustedBoundary.finalizeImportedEnv envBad
    let rejected ← try
      let _ ← TrustedBoundary.verifyAndCollectCorrLocals envBad baseRoles {{}}
      pure false
    catch err =>
      unless err.toString.startsWith
          "policy:authority violation: External.Alt.t references External.SysHelper.t" do
        throw err
      pure true
    unless rejected do
      throw <| IO.userError "late foundation alternate referencing sysroot was accepted"
    let repoHelper : Lean.ConstantInfo := .thmInfo {{
      name := `Anneal.Helper.t, levelParams := [],
      type := propImp, value := idLam,
      all := [`Anneal.Helper.t] }}
    let repoAltVal := Lean.Expr.letE `h propImp
      (.const `Anneal.Helper.t []) idLam false
    let repoAltThm : Lean.ConstantInfo := .thmInfo {{
      name := `External.Alt.t, levelParams := [],
      type := propImp, value := repoAltVal,
      all := [`External.Alt.t] }}
    Lean.saveModuleData (dir / "RepoH.olean") `Anneal.Helper {{
      isModule := false, imports := #[],
      constNames := #[`Anneal.Helper.t], constants := #[repoHelper],
      extraConstNames := #[], entries := #[] }}
    Lean.saveModuleData (dir / "FRepoBad.olean") `External.FRepoBad {{
      isModule := false, imports := #[{{ module := `External.F0 }}],
      constNames := #[`External.Alt.t], constants := #[repoAltThm],
      extraConstNames := #[], entries := #[] }}
    Lean.saveModuleData (dir / "DrvFRepoBad.olean") `Anneal.DrvFRepoBad {{
      isModule := false, imports := #[{{ module := `External.FRepoBad }}, {{ module := `Anneal.Helper }}],
      constNames := #[], constants := #[],
      extraConstNames := #[], entries := #[] }}
    Lean.saveModuleData (dir / "TheoryBadCopy.olean") `Anneal.TheoryBadCopy {{
      isModule := false,
      imports := #[{{ module := `External.F0 }}, {{ module := `Anneal.Helper }}],
      constNames := #[`External.Alt.t], constants := #[repoAltThm],
      extraConstNames := #[], entries := #[] }}
    Lean.saveModuleData (dir / "DrvFRepoBadDup.olean") `Anneal.DrvFRepoBadDup {{
      isModule := false,
      imports := #[{{ module := `External.FRepoBad }}, {{ module := `Anneal.Helper }},
        {{ module := `Anneal.TheoryBadCopy }}],
      constNames := #[], constants := #[],
      extraConstNames := #[], entries := #[] }}
    Lean.saveModuleData (dir / "SysRepoBad.olean") `External.SysRepoBad {{
      isModule := false, imports := #[{{ module := `External.F0 }}],
      constNames := #[`External.Alt.t], constants := #[repoAltThm],
      extraConstNames := #[], entries := #[] }}
    Lean.saveModuleData (dir / "DrvSysRepoBadDup.olean") `Anneal.DrvSysRepoBadDup {{
      isModule := false,
      imports := #[{{ module := `External.SysRepoBad }}, {{ module := `Anneal.Helper }},
        {{ module := `Anneal.TheoryBadCopy }}],
      constNames := #[], constants := #[],
      extraConstNames := #[], entries := #[] }}
    Lean.saveModuleData (dir / "SysAlt2.olean") `External.SysAlt2 {{
      isModule := false,
      imports := #[{{ module := `External.F0 }}, {{ module := `External.SysHelper }}],
      constNames := #[`External.Alt.t], constants := #[altThm2],
      extraConstNames := #[], entries := #[] }}
    Lean.saveModuleData (dir / "DrvF1SysDup.olean") `Anneal.DrvF1SysDup {{
      isModule := false,
      imports := #[{{ module := `External.F1 }}, {{ module := `External.SysHelper }},
        {{ module := `External.SysAlt2 }}],
      constNames := #[], constants := #[],
      extraConstNames := #[], entries := #[] }}
    Lean.saveModuleData (dir / "TheoryRealized.olean") `Anneal.TheoryRealized {{
      isModule := false, imports := #[{{ module := `External.F0 }}, {{ module := `Anneal.Helper }}],
      constNames := #[`External.Alt.t], constants := #[repoAltThm],
      extraConstNames := #[], entries := #[] }}
    Lean.saveModuleData (dir / "FExtraCollide.olean") `External.FExtraCollide {{
      isModule := false, imports := #[{{ module := `External.F0 }}],
      constNames := #[], constants := #[],
      extraConstNames := #[`External.Alt.t], entries := #[] }}
    Lean.saveModuleData (dir / "SysExtraCollide.olean") `External.SysExtraCollide {{
      isModule := false, imports := #[{{ module := `External.F0 }}],
      constNames := #[], constants := #[],
      extraConstNames := #[`External.Alt.t], entries := #[] }}
    for (n, f) in [(`Anneal.Helper, "RepoH.olean"), (`External.FRepoBad, "FRepoBad.olean"),
        (`Anneal.DrvFRepoBad, "DrvFRepoBad.olean"),
        (`Anneal.TheoryBadCopy, "TheoryBadCopy.olean"),
        (`Anneal.DrvFRepoBadDup, "DrvFRepoBadDup.olean"),
        (`External.SysRepoBad, "SysRepoBad.olean"),
        (`Anneal.DrvSysRepoBadDup, "DrvSysRepoBadDup.olean"),
        (`External.SysAlt2, "SysAlt2.olean"),
        (`Anneal.DrvF1SysDup, "DrvF1SysDup.olean"),
        (`Anneal.TheoryRealized, "TheoryRealized.olean"),
        (`External.FExtraCollide, "FExtraCollide.olean"), (`External.SysExtraCollide, "SysExtraCollide.olean")] do
      arts := arts.insert n (Lean.ImportArtifacts.ofArrays #[#[dir / f], #[]])
    let p2SharedRoles : Std.HashMap Lean.Name TrustedBoundary.CorrOrigin :=
      Std.HashMap.ofList [
        (`External.F0, .foundation),
        (`Anneal.Helper, .repo .theory)]
    let p2BadRoles := p2SharedRoles
      |>.insert `External.FRepoBad .foundation
      |>.insert `Anneal.DrvFRepoBad (.repo .theory)
    let p1SharedRoles : Std.HashMap Lean.Name TrustedBoundary.RepoOrigin :=
      Std.HashMap.ofList [
        (`External.F0, .foundation),
        (`Anneal.Helper, .repo .theory)]
    let p1BadRoles := p1SharedRoles
      |>.insert `External.FRepoBad .foundation
      |>.insert `Anneal.DrvFRepoBad (.repo .theory)
    let envFRepoBad ← Lean.importModules #[{{ module := `Anneal.DrvFRepoBad }}] {{}}
      (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private) (arts := arts)
    let envFRepoBad ← TrustedBoundary.finalizeImportedEnv envFRepoBad
    for label in ["pass1", "pass2"] do
      let fBadRejected ← try
        if label == "pass1" then
          discard <| TrustedBoundary.verifyAndCollectLocals envFRepoBad p1BadRoles
        else
          discard <| TrustedBoundary.verifyAndCollectCorrLocals envFRepoBad p2BadRoles {{}}
        pure false
      catch err =>
        unless err.toString.startsWith
            "policy:authority violation: External.Alt.t references Anneal.Helper.t" do
          throw err
        pure true
      unless fBadRejected do
        throw <| IO.userError s!"{{label}} foundation alternate referencing repo was accepted"
    let p1BadDupRoles := p1SharedRoles
      |>.insert `External.FRepoBad .foundation
      |>.insert `Anneal.TheoryBadCopy (.repo .theory)
      |>.insert `Anneal.DrvFRepoBadDup (.repo .theory)
    let p2BadDupRoles := p2SharedRoles
      |>.insert `External.FRepoBad .foundation
      |>.insert `Anneal.TheoryBadCopy (.repo .theory)
      |>.insert `Anneal.DrvFRepoBadDup (.repo .theory)
    let envFRepoBadDup ← Lean.importModules #[{{ module := `Anneal.DrvFRepoBadDup }}] {{}}
      (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private) (arts := arts)
    let envFRepoBadDup ← TrustedBoundary.finalizeImportedEnv envFRepoBadDup
    for label in ["pass1-dup", "pass2-dup"] do
      let fBadDupRejected ← try
        if label == "pass1-dup" then
          discard <| TrustedBoundary.verifyAndCollectLocals envFRepoBadDup p1BadDupRoles
        else
          discard <| TrustedBoundary.verifyAndCollectCorrLocals envFRepoBadDup p2BadDupRoles {{}}
        pure false
      catch err =>
        unless err.toString.startsWith
            "policy:authority violation: External.Alt.t references Anneal.Helper.t" do
          throw err
        pure true
      unless fBadDupRejected do
        throw <| IO.userError s!"{{label}} trailing repo copy masked foundation violation"
    let p2SysRepoDupRoles := p2SharedRoles
      |>.insert `External.SysRepoBad .sysrootFoundation
      |>.insert `Anneal.TheoryBadCopy (.repo .theory)
      |>.insert `Anneal.DrvSysRepoBadDup (.repo .theory)
    let envSysRepoBadDup ← Lean.importModules #[{{ module := `Anneal.DrvSysRepoBadDup }}] {{}}
      (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private) (arts := arts)
    let envSysRepoBadDup ← TrustedBoundary.finalizeImportedEnv envSysRepoBadDup
    let sysDupRejected ← try
      discard <| TrustedBoundary.verifyAndCollectCorrLocals envSysRepoBadDup p2SysRepoDupRoles {{}}
      pure false
    catch err =>
      unless err.toString.startsWith
          "policy:authority violation: External.Alt.t references Anneal.Helper.t" do
        throw err
      pure true
    unless sysDupRejected do
      throw <| IO.userError "pass2 trailing repo copy masked sysrootFoundation violation"
    let p2F1SysDupRoles : Std.HashMap Lean.Name TrustedBoundary.CorrOrigin :=
      Std.HashMap.ofList [
        (`External.F0, .foundation),
        (`External.SysHelper, .sysrootFoundation),
        (`External.F1, .foundation),
        (`External.SysAlt2, .sysrootFoundation),
        (`Anneal.DrvF1SysDup, .repo .theory)]
    let envF1SysDup ← Lean.importModules #[{{ module := `Anneal.DrvF1SysDup }}] {{}}
      (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private) (arts := arts)
    let envF1SysDup ← TrustedBoundary.finalizeImportedEnv envF1SysDup
    let f1SysDupRejected ← try
      discard <| TrustedBoundary.verifyAndCollectCorrLocals envF1SysDup p2F1SysDupRoles {{}}
      pure false
    catch err =>
      unless err.toString.startsWith
          "policy:authority violation: External.Alt.t references External.SysHelper.t" do
        throw err
      pure true
    unless f1SysDupRejected do
      throw <| IO.userError "pass2 trailing sysroot copy masked foundation violation"
    let envRepoOk ← Lean.importModules #[{{ module := `Anneal.TheoryRealized }}] {{}}
      (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private) (arts := arts)
    let envRepoOk ← TrustedBoundary.finalizeImportedEnv envRepoOk
    let (_, _, _, p1Alts, _) ← TrustedBoundary.verifyAndCollectLocals envRepoOk
      (p1SharedRoles.insert `Anneal.TheoryRealized (.repo .theory))
    unless p1Alts.size == 2 do
      throw <| IO.userError s!"expected 2 Pass-1 alternates for .repo .theory realization, got {{p1Alts.size}}"
    let (_, _, _, p2RepoAlts, p2VendorAlts, _, _) ← TrustedBoundary.verifyAndCollectCorrLocals envRepoOk
      (p2SharedRoles.insert `Anneal.TheoryRealized (.repo .theory))
      {{}}
    unless p2VendorAlts.size == 1 && p2RepoAlts.size == 1 do
      throw <| IO.userError s!"expected 1 vendor + 1 repo alternate, got {{p2VendorAlts.size}}/{{p2RepoAlts.size}}"
    let envFExtra ← Lean.importModules #[{{ module := `External.FExtraCollide }}] {{}}
      (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private) (arts := arts)
    let envFExtra ← TrustedBoundary.finalizeImportedEnv envFExtra
    let p1FExtraBad ← try
      discard <| TrustedBoundary.verifyAndCollectLocals envFExtra
        (Std.HashMap.ofList [(`External.F0, .foundation), (`External.FExtraCollide, .foundation)])
      pure false
    catch err =>
      unless err.toString == "policy:uninventoried kernel compiler helper External.Alt.t" do
        throw err
      pure true
    unless p1FExtraBad do
      throw <| IO.userError "Pass-1 foundation extraConstNames collision with earlier module was accepted"
    let p2FExtraBad ← try
      discard <| TrustedBoundary.verifyAndCollectCorrLocals envFExtra
        (Std.HashMap.ofList [(`External.F0, .foundation), (`External.FExtraCollide, .foundation)]) {{}}
      pure false
    catch err =>
      unless err.toString == "policy:uninventoried kernel compiler helper External.Alt.t" do
        throw err
      pure true
    unless p2FExtraBad do
      throw <| IO.userError "Pass-2 foundation extraConstNames collision with earlier module was accepted"
    let envSysExtra ← Lean.importModules #[{{ module := `External.SysExtraCollide }}] {{}}
      (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private) (arts := arts)
    let envSysExtra ← TrustedBoundary.finalizeImportedEnv envSysExtra
    let p2SysExtraBad ← try
      discard <| TrustedBoundary.verifyAndCollectCorrLocals envSysExtra
        (Std.HashMap.ofList [(`External.F0, .foundation), (`External.SysExtraCollide, .sysrootFoundation)]) {{}}
      pure false
    catch err =>
      unless err.toString == "policy:uninventoried kernel compiler helper External.Alt.t" do
        throw err
      pure true
    unless p2SysExtraBad do
      throw <| IO.userError "Pass-2 sysrootFoundation extraConstNames collision with earlier module was accepted"
"#,
        probe_dir.to_string_lossy()
    ));
    let probe_path = stage.join("CheckSysrootAlternatesOrder.lean");
    fs::write(&probe_path, probe_src).unwrap();
    checker
        .process(
            "check-sysroot-alternates-order",
            &[probe_path.to_string_lossy().into_owned()],
        )
        .unwrap();
}
