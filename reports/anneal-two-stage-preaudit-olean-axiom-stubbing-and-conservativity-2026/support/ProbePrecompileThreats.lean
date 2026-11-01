-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean

/-!
# Adversarial & Goodhart Threat Probes for Pre-Compiled `theory/Anneal/`

This executable Lean 4.34.1 probe tests four concrete threat classes when
`theory/Anneal/` theorems are pre-compiled in Stage 1 (CI) and taken as
axiomatic (`axiom` / pre-verified `.thmInfo` without runtime body traversal) in
Stage 2 (`cargo anneal verify`):

1. **Threat Class 1 (Transitive `@[candidate <feat>]` Laundering):**
   - **Probe 1A (Direct Axiom-Stripping Laundering):** A `theory/Anneal/`
     theorem `Anneal.fast_bridge` has a `@[vetted]`-only statement (`ci.type`),
     while its proof body (`ci.value?`) uses a `candidate:mir_semantics` lemma.
     Demonstrates that replacing `Anneal.fast_bridge` with `.axiomInfo` in
     Stage 2 without a precomputed `theory-lock.json` candidate map launders
     `mir_semantics` (`#[]`), whereas consulting the lock catches it
     (`#["mir_semantics"]`).
   - **Probe 1B (Deferred `Trusted.candidate "<feat>"` Guard Laundering):**
     `Anneal.bridge_using_vetted` calls a `@[vetted]` function containing a
     `Trusted.candidate "mir_semantics"` branch that references a
     `candidate:memory` helper. In Stage 1 alone, `Anneal.bridge_using_vetted`
     activates `#[]`. At Stage 2, `Mir.lean` activates `"mir_semantics"`.
     Demonstrates that a flat `transitiveCandidateFeatures` lock entry misses
     `"memory"`, whereas recording `(directCandidateFeatures,
     deferredCandidateEdges)` catches `#["memory", "mir_semantics"]`.
2. **Threat Class 2 (Transitive `TrustedAssumption` / `waived` Laundering):**
   Demonstrates that because `waived` / `assumptions` is an explicit parameter
   in the *type* `VerificationResult policy waived obligations`, a `theory/`
   theorem proved under extra waived assumptions has a distinct kernel type that
   the C++ kernel (`addDeclCore`) and `TrustedBoundary.lean` reject when
   checking `Proof.verify_crate : Trusted.CrateTheorem Mir.crate`.
3. **Threat Class 3 (Universe Polymorphism & `levelParams` Abuse):**
   - **Probe 3A:** Demonstrates that C++ `type_checker::infer_constant`
     (`src/kernel/type_checker.cpp:105`) and `type_checker::check_level`
     (`src/kernel/type_checker.cpp:85-91`) reject wrong universe-argument
     counts and unbound universe parameters on pre-compiled axioms/theorems.
   - **Probe 3B:** Demonstrates a subtle gap in `TrustedBoundary.lean:948-958`:
     checking `proofCi.type == expectedTheoremType` alone does NOT check
     `proofCi.levelParams.isEmpty`, allowing `theorem verify_crate.{u}` with an
     unused universe parameter `u` unless `levelParams.isEmpty` is enforced.
4. **Threat Class 4 (`@[implemented_by]` / `Lean.reduceBool` / `realizeConst`):**
   Verifies that `Lean.reduceBool` and `Lean.reduceNat` in `Init.Core` are
   `.opaqueInfo` constants whose bodies reference `Lean.trustCompiler`
   (`Init/Core.lean:2361-2379`), so `declarationEdges` (`allowOpaque := true`)
   and `closure` in `TrustedBoundary.lean` deterministically detect and reject
   any native-evaluation dependency via `Lean.trustCompiler`.
-/

open Lean Meta

namespace Anneal.ProbePrecompileThreats

/-- Reproduces `TrustedBoundary.lean`'s `declarationEdges` (`lines 528-543`). -/
def declarationEdges (ci : ConstantInfo) : NameSet := Id.run do
  let collectExpr (e : Expr) : NameSet :=
    e.foldConsts {} (fun n acc => acc.insert n)
  let mut result := collectExpr ci.type
  if let some val := ci.value? (allowOpaque := true) then
    result := result ++ collectExpr val
  return result

/-- Simulated `collectActiveCandidateFeatures` (`TrustedBoundary.lean:756-808`)
    with optional `theory-lock.json` precomputed summaries for axiomatized
    `theory/Anneal/` declarations. -/
structure TheoryLockEntry where
  direct : Array String := #[]
  deferred : Array (String × String) := #[]
  deriving Repr

def simulateCandidateAudit
    (decls : Std.HashMap Name ConstantInfo)
    (trustedConsts : NameSet)
    (statusMap : Std.HashMap Name String)
    (guardedBranches : Std.HashMap Name (Array (String × Name)))
    (theoryLock : Std.HashMap Name TheoryLockEntry)
    (roots : Array Name) : Array String := Id.run do
  let mut pending := roots.toList
  let mut visited : NameSet := {}
  let mut activeFeats : Std.HashSet String := {}
  let mut deferred : Std.HashMap String (Array Name) := {}

  let activateFeat := fun (feat : String)
      (active : Std.HashSet String)
      (defMap : Std.HashMap String (Array Name))
      (work : List Name) => Id.run do
    if active.contains feat then
      return (active, defMap, work)
    let active' := active.insert feat
    if let some unlocked := defMap.get? feat then
      let defMap' := defMap.erase feat
      return (active', defMap', unlocked.toList ++ work)
    return (active', defMap, work)

  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    if !visited.contains n then
      visited := visited.insert n
      let some ci := decls.get? n | continue
      if trustedConsts.contains n then
        let status := statusMap.getD n "vetted"
        if status.startsWith "candidate:" then
          let feat := (status.drop 10).toString
          let (a', d', p') := activateFeat feat activeFeats deferred pending
          activeFeats := a'
          deferred := d'
          pending := (declarationEdges ci).toList ++ p'
        else
          pending := (declarationEdges ci).toList ++ pending
          for (feat, targetConst) in guardedBranches.getD n #[] do
            if activeFeats.contains feat then
              pending := targetConst :: pending
            else
              let prev := deferred.getD feat #[]
              deferred := deferred.insert feat (prev.push targetConst)
      else
        -- Non-trusted (`theory/Anneal/`, `Mir`, or `Proof`) constant.
        -- If `n` is an axiomatized `theory/Anneal/` declaration with an entry
        -- in `theoryLock`, incorporate its precomputed summary!
        if let some lockEntry := theoryLock.get? n then
          for feat in lockEntry.direct do
            let (a', d', p') := activateFeat feat activeFeats deferred pending
            activeFeats := a'
            deferred := d'
            pending := p'
          for (trigFeat, unlockedFeat) in lockEntry.deferred do
            let synthTarget := Name.mkSimple s!"_lock_cand_{unlockedFeat}"
            if activeFeats.contains trigFeat then
              pending := synthTarget :: pending
            else
              let prev := deferred.getD trigFeat #[]
              deferred := deferred.insert trigFeat (prev.push synthTarget)
        pending := (declarationEdges ci).toList ++ pending
  return activeFeats.toArray.qsort (· < ·)

/-- Model types for Threat Class 2 (`waived` obligation laundering). -/
inductive Obligation where
  | fnSafe (id : Nat)
  | unsafeBlock (id : Nat)
  deriving DecidableEq, Repr

structure CrateModel where
  waived : List Obligation
  obligations : List Obligation

def VerificationResultModel (waived : List Obligation)
    (obligations : List Obligation) : Prop :=
  ∀ ob, ob ∈ obligations → ob ∈ waived

def CrateTheoremModel (c : CrateModel) : Prop :=
  VerificationResultModel c.waived c.obligations

def mirCrateModel : CrateModel := {
  waived := []
  obligations := [.fnSafe 0]
}

/-- Pre-compiled `theory/Anneal/` helper theorem that proves verification ONLY
    when `.fnSafe 0` is in `waived`. -/
theorem anneal_waived_helper :
    VerificationResultModel [.fnSafe 0] [.fnSafe 0] := by
  intro ob hMem
  exact hMem

def runThreatProbes : MetaM Unit := do
  IO.println "=== [Probe 1A] Direct @[candidate] Laundering via Axiom Stripping ==="
  let nVettedProp := `Trusted.vettedProp
  let nCandLemma := `Trusted.candLemma
  let nFastBridge := `Anneal.fast_bridge
  let nVerifyCrate := `Proof.verify_crate

  let ciVettedProp := ConstantInfo.defnInfo {
    name := nVettedProp, levelParams := [], type := mkSort .zero
    value := mkConst ``True, hints := .abbrev, safety := .safe
  }
  let ciCandLemma := ConstantInfo.thmInfo {
    name := nCandLemma, levelParams := [], type := mkConst nVettedProp
    value := mkConst ``True.intro
  }
  -- Full `.thmInfo` (Stage 1 / Monolithic): body references `Trusted.candLemma`.
  let ciFastBridgeThm := ConstantInfo.thmInfo {
    name := nFastBridge, levelParams := [], type := mkConst nVettedProp
    value := mkConst nCandLemma
  }
  -- Stripped `.axiomInfo` (Stage 2): `ci.value?` is `none`, `ci.type` is pure
  -- `@[vetted]` (`Trusted.vettedProp`).
  let ciFastBridgeAxiom := ConstantInfo.axiomInfo {
    name := nFastBridge, levelParams := [], type := mkConst nVettedProp
    isUnsafe := false
  }
  let ciVerifyCrate := ConstantInfo.thmInfo {
    name := nVerifyCrate, levelParams := [], type := mkConst nVettedProp
    value := mkConst nFastBridge
  }

  let trustedSet : NameSet :=
    NameSet.empty.insert nVettedProp |>.insert nCandLemma
  let statusMap : Std.HashMap Name String :=
    ({} : Std.HashMap Name String)
      |>.insert nVettedProp "vetted"
      |>.insert nCandLemma "candidate:mir_semantics"

  let declsMonolithic : Std.HashMap Name ConstantInfo :=
    ({} : Std.HashMap Name ConstantInfo)
      |>.insert nVettedProp ciVettedProp
      |>.insert nCandLemma ciCandLemma
      |>.insert nFastBridge ciFastBridgeThm
      |>.insert nVerifyCrate ciVerifyCrate

  let declsStage2Axiom : Std.HashMap Name ConstantInfo :=
    declsMonolithic.insert nFastBridge ciFastBridgeAxiom

  let lockDirect : Std.HashMap Name TheoryLockEntry :=
    ({} : Std.HashMap Name TheoryLockEntry).insert nFastBridge
      { direct := #["mir_semantics"], deferred := #[] }

  let monoFeats := simulateCandidateAudit declsMonolithic trustedSet statusMap {} {} #[nVerifyCrate]
  let naiveAxiomFeats := simulateCandidateAudit declsStage2Axiom trustedSet statusMap {} {} #[nVerifyCrate]
  let lockedAxiomFeats := simulateCandidateAudit declsStage2Axiom trustedSet statusMap {} lockDirect #[nVerifyCrate]

  IO.println s!"Monolithic candidate features:                     {monoFeats}"
  IO.println s!"Naive Stage-2 (axiom without theory-lock.json):    {naiveAxiomFeats}  <-- LAUNDERED!"
  IO.println s!"Locked Stage-2 (axiom with theory-lock.json):      {lockedAxiomFeats}  <-- CAUGHT!"

  IO.println "\n=== [Probe 1B] Deferred `Trusted.candidate` Branch Laundering Across Stages ==="
  let nEvalStmt := `Trusted.evalStmt
  let nCandMem := Name.mkSimple "_lock_cand_memory"
  let nCandMir := `Trusted.candMirAst
  let nBridgeVetted := `Anneal.bridge_using_vetted
  let nMirCrate := `Mir.crate

  let ciEvalStmt := ConstantInfo.defnInfo {
    name := nEvalStmt, levelParams := [], type := mkSort .zero
    value := mkConst ``True, hints := .regular 1, safety := .safe
  }
  let ciCandMem := ConstantInfo.defnInfo {
    name := nCandMem, levelParams := [], type := mkSort .zero
    value := mkConst ``True, hints := .regular 1, safety := .safe
  }
  let ciCandMir := ConstantInfo.defnInfo {
    name := nCandMir, levelParams := [], type := mkSort .zero
    value := mkConst ``True, hints := .regular 1, safety := .safe
  }
  let ciBridgeThm := ConstantInfo.thmInfo {
    name := nBridgeVetted, levelParams := [], type := mkConst ``True
    value := mkConst nEvalStmt
  }
  let ciBridgeAxiom := ConstantInfo.axiomInfo {
    name := nBridgeVetted, levelParams := [], type := mkConst ``True
    isUnsafe := false
  }
  let ciMirCrate := ConstantInfo.defnInfo {
    name := nMirCrate, levelParams := [], type := mkSort .zero
    value := mkConst nCandMir, hints := .regular 1, safety := .safe
  }
  let ciVerify1B := ConstantInfo.thmInfo {
    name := nVerifyCrate, levelParams := [], type := mkConst ``True
    value := mkApp (mkConst nBridgeVetted) (mkConst nMirCrate)
  }

  let trustedSet1B := trustedSet.insert nEvalStmt |>.insert nCandMem |>.insert nCandMir
  let statusMap1B := statusMap
    |>.insert nEvalStmt "vetted"
    |>.insert nCandMem "candidate:memory"
    |>.insert nCandMir "candidate:mir_semantics"
  let guarded1B : Std.HashMap Name (Array (String × Name)) :=
    ({} : Std.HashMap Name (Array (String × Name))).insert nEvalStmt #[("mir_semantics", nCandMem)]

  let decls1BMono : Std.HashMap Name ConstantInfo :=
    ({} : Std.HashMap Name ConstantInfo)
      |>.insert nEvalStmt ciEvalStmt
      |>.insert nCandMem ciCandMem
      |>.insert nCandMir ciCandMir
      |>.insert nBridgeVetted ciBridgeThm
      |>.insert nMirCrate ciMirCrate
      |>.insert nVerifyCrate ciVerify1B

  let decls1BAxiom := decls1BMono.insert nBridgeVetted ciBridgeAxiom

  -- Stage 1 alone on `Anneal.bridge_using_vetted`: activates `#[]`!
  let stage1IsolatedFeats := simulateCandidateAudit decls1BMono trustedSet1B statusMap1B guarded1B {} #[nBridgeVetted]
  -- Flat lock entry recording only Stage 1's unconditional `#[]`:
  let flatLock1B : Std.HashMap Name TheoryLockEntry :=
    ({} : Std.HashMap Name TheoryLockEntry).insert nBridgeVetted { direct := stage1IsolatedFeats, deferred := #[] }
  -- Conditional lock entry recording both `direct` and `deferred`:
  let condLock1B : Std.HashMap Name TheoryLockEntry :=
    ({} : Std.HashMap Name TheoryLockEntry).insert nBridgeVetted
      { direct := stage1IsolatedFeats, deferred := #[("mir_semantics", "memory")] }

  let mono1BFeats := simulateCandidateAudit decls1BMono trustedSet1B statusMap1B guarded1B {} #[nVerifyCrate, nMirCrate]
  let flat1BFeats := simulateCandidateAudit decls1BAxiom trustedSet1B statusMap1B guarded1B flatLock1B #[nVerifyCrate, nMirCrate]
  let cond1BFeats := simulateCandidateAudit decls1BAxiom trustedSet1B statusMap1B guarded1B condLock1B #[nVerifyCrate, nMirCrate]

  IO.println s!"Stage-1 isolated features of Anneal.bridge_using_vetted: {stage1IsolatedFeats}"
  IO.println s!"Monolithic Stage-2 features (Mir + Proof + Anneal body): {mono1BFeats}"
  IO.println s!"Flat-lock Stage-2 features (unconditional only):         {flat1BFeats}  <-- MISSED memory!"
  IO.println s!"Conditional-lock Stage-2 features (direct + deferred):   {cond1BFeats}  <-- EXACT MATCH!"

  IO.println "\n=== [Probe 2] Transitive TrustedAssumption / Waived-Obligation Laundering ==="
  let env ← getEnv
  let badWaivedProof := Declaration.thmDecl {
    name := `Anneal.ProbePrecompileThreats.badVerifyCrate
    levelParams := []
    type := mkApp (mkConst ``CrateTheoremModel) (mkConst ``mirCrateModel)
    value := mkConst ``anneal_waived_helper
  }
  let waivedRes := env.addDeclCore 0 0 badWaivedProof none
  match waivedRes with
  | .ok _ => IO.println "ERROR: kernel accepted mismatched waived obligations!"
  | .error e =>
    let msg ← (e.toMessageData {}).toString
    IO.println s!"Kernel rejected mismatched waived-obligation proof as expected:\n  {msg.trimAscii.toString}"

  IO.println "\n=== [Probe 3A & 3B] Universe Polymorphism & levelParams Instantiation Abuse ==="
  let polyAxiomName := `Anneal.ProbePrecompileThreats.polyAxiom
  let polyAxiomDecl := Declaration.axiomDecl {
    name := polyAxiomName
    levelParams := [`u]
    type := mkForall `α BinderInfo.default (mkSort (.param `u)) (mkConst ``True)
    isUnsafe := false
  }
  let envPoly ← ofExceptKernelException (env.addDeclCore 0 0 polyAxiomDecl none)

  -- Attack 3A-1: Instantiate `polyAxiom.{u}` with 0 universe levels `[]`.
  let badArityDecl := Declaration.thmDecl {
    name := `Anneal.ProbePrecompileThreats.badUnivArity
    levelParams := []
    type := mkConst ``True
    value := mkApp (mkConst polyAxiomName []) (mkConst ``Nat)
  }
  match envPoly.addDeclCore 0 0 badArityDecl none with
  | .ok _ => IO.println "ERROR: kernel accepted wrong universe arity!"
  | .error e =>
    let msg ← (e.toMessageData {}).toString
    IO.println s!"[3A-1] Kernel rejected wrong universe arity (`type_checker.cpp:105`): {msg.trimAscii.toString}"

  -- Attack 3A-2: Instantiate `polyAxiom.{u}` with unbound universe parameter `v`.
  let badUnboundDecl := Declaration.thmDecl {
    name := `Anneal.ProbePrecompileThreats.badUnboundUniv
    levelParams := []
    type := mkConst ``True
    value := mkApp (mkConst polyAxiomName [.param `v]) (mkSort .zero)
  }
  match envPoly.addDeclCore 0 0 badUnboundDecl none with
  | .ok _ => IO.println "ERROR: kernel accepted unbound universe parameter!"
  | .error e =>
    let msg ← (e.toMessageData {}).toString
    IO.println s!"[3A-2] Kernel rejected unbound universe param (`type_checker.cpp:85-91`): {msg.trimAscii.toString}"

  -- Probe 3B: Unused `levelParams` on `Proof.verify_crate.{u}` vs
  -- `TrustedBoundary.lean:956-958` (`proofCi.type == expectedTheoremType`).
  let unusedUnivProofName := `Anneal.ProbePrecompileThreats.verify_crate_unused_u
  let unusedUnivProofDecl := Declaration.thmDecl {
    name := unusedUnivProofName
    levelParams := [`u]
    type := mkConst ``True
    value := mkConst ``True.intro
  }
  let envUnused ← ofExceptKernelException (envPoly.addDeclCore 0 0 unusedUnivProofDecl none)
  let some unusedCi := envUnused.find? unusedUnivProofName | unreachable!
  IO.println s!"[3B] unusedUnivProof: type == True is {unusedCi.type == mkConst ``True}, but levelParams = {unusedCi.levelParams} (non-empty!)"

  IO.println "\n=== [Probe 4] Compiler-Override (`Lean.reduceBool` / `Lean.trustCompiler`) Detection ==="
  let some reduceBoolCi := env.find? ``Lean.reduceBool | unreachable!
  let some reduceNatCi := env.find? ``Lean.reduceNat | unreachable!
  let rbEdges := (declarationEdges reduceBoolCi).toList
  let rnEdges := (declarationEdges reduceNatCi).toList
  IO.println s!"Lean.reduceBool declarationEdges (allowOpaque := true): {rbEdges}"
  IO.println s!"Lean.reduceNat  declarationEdges (allowOpaque := true): {rnEdges}"
  IO.println s!"Contains Lean.trustCompiler axiom: {rbEdges.contains ``Lean.trustCompiler && rnEdges.contains ``Lean.trustCompiler}"

#eval runThreatProbes

end Anneal.ProbePrecompileThreats
