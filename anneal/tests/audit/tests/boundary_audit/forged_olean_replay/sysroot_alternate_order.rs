// Copyright 2026 The Fuchsia Authors
//
// Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
// <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
// license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
// This file may not be copied, modified, or distributed except according to
// those terms.

//! Section 12: the direct `verifyAndCollectCorrLocals` probe of alternate
//! ordering between `.sysrootFoundation` and `.foundation` modules.

use super::*;

/// Runs section 12.
pub(super) fn checks_sysroot_alternate_order(mut checker: Checker, stage: PathBuf) {
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
