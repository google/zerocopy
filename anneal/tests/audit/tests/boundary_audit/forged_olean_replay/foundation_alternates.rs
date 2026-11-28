// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Sections 6 through 8: the `sorryAx` subsumption hijack, external
//! alternate edges, and Pass 1 `.repo (.trusted .vetted)` locals.

use anneal_audit::Failure;

use super::*;

/// Runs sections 6 through 8 and returns the checker.
pub(super) fn rejects_axiom_hijack_and_forged_alternates(
    mut checker: Checker,
    stage: PathBuf,
    lib_dir: PathBuf,
    orig_arts: BTreeMap<String, ModuleArtifacts>,
    orig_graph: BTreeMap<String, Vec<ImportEdge>>,
    core_edge: Vec<ImportEdge>,
    inspect_pass1_mod: &impl Fn(&mut Checker, &str, &Path, bool, Vec<ImportEdge>) -> Failure,
) -> Checker {
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
    checker
}
