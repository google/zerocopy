// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Sections 1 through 5c: forged Pass 1 checked-environment keys, module
//! headers, `_unsafe_rec` headers, and `validateReplayMap` invariants.

use anneal_audit::Failure;

use super::*;

/// Runs sections 1 through 5c and returns the checker.
pub(super) fn rejects_forged_keys_headers_and_replay_maps(
    mut checker: Checker,
    stage: PathBuf,
    forged_lib: PathBuf,
    core_edge: Vec<ImportEdge>,
    inspect_pass1_mod: &impl Fn(&mut Checker, &str, &Path, bool, Vec<ImportEdge>) -> Failure,
) -> Checker {
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
    checker
}
