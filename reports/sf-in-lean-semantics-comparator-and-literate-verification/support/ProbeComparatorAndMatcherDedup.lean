-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean
import Lean.Replay

/-!
# Probe: `comparator`, `comparator-autograder`, and Match Deduplication

Self-contained Lean `v4.34.1` executable probe (`lean --run`) that reproduces
and verifies:

1. The `sf-in-lean` `Template` (`List.IsNil := sorry`) vs. `Submission`
   (`List.IsNil` with `match`) matcher deduplication hazard caused by
   `Lean.Meta.Match.mkMatcherAuxDefinition` caching compiled match splitters in
   `matcherExt` by `{ value := result.value, compile, isPrivate }`:
   - `LF.Poly.List.In._f` references `LF.Poly.List.In.match_1` in `Template`
     and `LF.Poly.List.IsNil.match_1` in `Submission`.
   - `Kernel.isDefEqGuarded` equates the two `LF.Poly.List.In._f` bodies
     (`true`) because both splitters carry `ReducibilityHints.abbrev` and
     identical values, whereas syntactic `ConstantInfo` `BEq` (`Comparator`)
     evaluates to `false`.
   - Separate namespaces (`NsA` vs. `NsB`) and motive sort changes (`: Bool` vs.
     `: Prop`) do not prevent `matcherExt` collisions because
     `Closure.mkValueTypeClosure` generalizes the motive sort to `Sort.{u_2}`,
     whereas `if-then-else` avoids `matcherExt`.
   - Under `-DElab.async=true` (Lean default), theorem bodies elaborate on
     isolated async environment branches where `matcherExt` (`asyncMode :=
     .local`) updates are discarded; under `-DElab.async=false` (Anneal's flag),
     theorem bodies share `.match_1` splitters across theorems.
2. Two soundness and completeness defects in `plclub/comparator-autograder`:
   - `@[autogradedHole]` on `inductive` declarations checks only
     `toConstantVal` and `isUnsafe` (`inductiveHoleMatches`) and pushes only
     `solutionConst.type.getUsedConstants` onto `compareWorklist`, accepting a
     spoofed `Even.cheat : ∀ n, Even n` constructor in
     `Kernel.Environment.replay` and `Compare.loop`.
   - `Compare.loop` uses syntactic `ConstantInfo` `BEq` (`TheoremVal.value ==
     TheoremVal.value`), rejecting student-proved helper theorems referenced
     inside non-hole definitions despite kernel proof irrelevance.
-/

open Lean

namespace ProbeComparatorAndMatcherDedup

-- Exact `BEq` instances derived by `xhalo32/comparator/Comparator/Util.lean`:
deriving instance BEq for Lean.ConstantVal
deriving instance BEq for Lean.AxiomVal
deriving instance BEq for Lean.DefinitionVal
deriving instance BEq for Lean.TheoremVal
deriving instance BEq for Lean.OpaqueVal
deriving instance BEq for Lean.QuotKind
deriving instance BEq for Lean.QuotVal
deriving instance BEq for Lean.InductiveVal
deriving instance BEq for Lean.ConstructorVal
deriving instance BEq for Lean.RecursorRule
deriving instance BEq for Lean.RecursorVal
deriving instance BEq for Lean.ConstantInfo
deriving instance Repr for Lean.ReducibilityHints

/-- Fails the probe immediately if `cond` is false. -/
def assertTrue (label : String) (cond : Bool) : IO Unit := do
  unless cond do
    throw <| IO.userError s!"assertion failed: {label}"

/-- Returns `true` when `n` contains a `"match_"` substring. -/
def hasMatchSubstr (n : Name) : Bool :=
  (n.toString.splitOn "match_").length > 1

/-- Collects all constants referenced in `info`'s type and value. -/
def getAllUsedConsts (info : ConstantInfo) : Array Name := Id.run do
  let mut s : NameSet := info.type.getUsedConstantsAsSet
  if let some v := info.value? (allowOpaque := true) then
    s := s.union v.getUsedConstantsAsSet
  return s.toArray.qsort Name.lt

/-- Finds a constant by name in `ModuleData`. -/
def findInMod? (md : ModuleData) (n : Name) : Option ConstantInfo := Id.run do
  for c in md.constants do
    if c.name == n then
      return some c
  return none

/-- Compiles a Lean source string to `oleanPath` using the current `lean`
    executable. -/
def compileLeanModule (leanExe : System.FilePath) (tmpDir : System.FilePath)
    (modName : String) (src : String) (extraArgs : Array String := #[]) :
    IO System.FilePath := do
  let leanFile := tmpDir / s!"{modName}.lean"
  let oleanFile := tmpDir / s!"{modName}.olean"
  IO.FS.writeFile leanFile src
  let out ← IO.Process.output {
    cmd := leanExe.toString
    args := extraArgs ++ #["-o", oleanFile.toString, leanFile.toString]
    cwd := some tmpDir
    env := #[("LEAN_PATH", some tmpDir.toString)]
  }
  unless out.exitCode == 0 do
    throw <| IO.userError
      s!"failed to compile {modName}:\n{out.stdout}\n{out.stderr}"
  return oleanFile

def templateSrc : String :=
  "namespace LF.Poly\n" ++
  "def List.IsNil (l : List α) : Prop := sorry\n" ++
  "def List.In (x : α) (xs : List α) : Prop :=\n" ++
  "  match xs with\n" ++
  "  | [] => False\n" ++
  "  | x' :: xs' => x = x' ∨ List.In x xs'\n" ++
  "theorem In_singleton (x : α) : List.In x [x] := sorry\n" ++
  "end LF.Poly\n"

def submissionSrc : String :=
  "namespace LF.Poly\n" ++
  "def List.IsNil (l : List α) : Prop :=\n" ++
  "  match l with\n" ++
  "  | [] => True\n" ++
  "  | _ :: _ => False\n" ++
  "def List.In (x : α) (xs : List α) : Prop :=\n" ++
  "  match xs with\n" ++
  "  | [] => False\n" ++
  "  | x' :: xs' => x = x' ∨ List.In x xs'\n" ++
  "theorem In_singleton (x : α) : List.In x [x] := Or.inl rfl\n" ++
  "end LF.Poly\n"

def scopeAndAsyncSrc : String :=
  "namespace NsA\n" ++
  "def firstMatch (l : List α) : Prop :=\n" ++
  "  match l with\n" ++
  "  | [] => True\n" ++
  "  | _ :: _ => False\n" ++
  "end NsA\n" ++
  "namespace NsB\n" ++
  "def secondMatch (l : List α) : Prop :=\n" ++
  "  match l with\n" ++
  "  | [] => False\n" ++
  "  | _ :: _ => True\n" ++
  "end NsB\n" ++
  "namespace MitigationSort\n" ++
  "def firstBoolMatch (l : List α) : Bool :=\n" ++
  "  match l with\n" ++
  "  | [] => true\n" ++
  "  | _ :: _ => false\n" ++
  "def secondPropMatch (l : List α) : Prop :=\n" ++
  "  match l with\n" ++
  "  | [] => False\n" ++
  "  | _ :: _ => True\n" ++
  "end MitigationSort\n" ++
  "namespace MitigationIte\n" ++
  "def firstIte (l : List α) : Prop :=\n" ++
  "  if l.isEmpty then True else False\n" ++
  "def secondMatchAfterIte (l : List α) : Prop :=\n" ++
  "  match l with\n" ++
  "  | [] => False\n" ++
  "  | _ :: _ => True\n" ++
  "end MitigationIte\n" ++
  "namespace ThmVsDef\n" ++
  "theorem thmWithMatch (o : Option Nat) : True :=\n" ++
  "  match o with\n" ++
  "  | none => trivial\n" ++
  "  | some _ => trivial\n" ++
  "theorem thm2WithMatch (o : Option Nat) : True :=\n" ++
  "  match o with\n" ++
  "  | none => trivial\n" ++
  "  | some _ => trivial\n" ++
  "def defAfterThmWithMatch (o : Option Nat) : Prop :=\n" ++
  "  match o with\n" ++
  "  | none => False\n" ++
  "  | some _ => False\n" ++
  "theorem thmAfterDefWithMatch (o : Option Nat) : True :=\n" ++
  "  match o with\n" ++
  "  | none => trivial\n" ++
  "  | some _ => trivial\n" ++
  "end ThmVsDef\n"

/-- Reproduces the `@[autogradedHole]` inductive spoofing flaw in
    `ComparatorAutograder/Comparator.lean:70-110`. -/
def runInductiveHoleUnsoundnessProbe : IO Unit := do
  IO.println "\n=== 2A. `comparator-autograder` `@[autogradedHole]` Inductive Unsoundness ==="
  let env ← importModules #[{ module := `Init }] {}
  let natConst := mkConst ``Nat
  let evenName := `ProbeInd.Even
  let evenType := mkForall `n .default natConst (mkSort 0)

  let challengeInd : InductiveVal := {
    name := evenName
    levelParams := []
    type := evenType
    numParams := 0
    numIndices := 1
    all := [evenName]
    ctors := []
    numNested := 0
    isRec := false
    isUnsafe := false
    isReflexive := false
  }
  let solutionInd : InductiveVal := {
    name := evenName
    levelParams := []
    type := evenType
    numParams := 0
    numIndices := 1
    all := [evenName]
    ctors := [`ProbeInd.Even.cheat]
    numNested := 0
    isRec := false
    isUnsafe := false
    isReflexive := false
  }
  let indHoleMatches :=
    challengeInd.toConstantVal == solutionInd.toConstantVal &&
    challengeInd.isUnsafe == solutionInd.isUnsafe
  let worklistAdditions := solutionInd.type.getUsedConstants

  IO.println s!"  inductiveHoleMatches(challengeInd, solutionInd) = {indHoleMatches}"
  IO.println s!"  challengeInd.ctors = {challengeInd.ctors}"
  IO.println s!"  solutionInd.ctors  = {solutionInd.ctors}"
  IO.println s!"  Compare.loop worklist additions for `{evenName}`: {worklistAdditions}"
  assertTrue "inductiveHoleMatches ignores ctors" indHoleMatches
  assertTrue "Compare.loop worklist omits Even.cheat"
    (!worklistAdditions.contains `ProbeInd.Even.cheat)

  let cheatCtor : ConstructorVal := {
    name := `ProbeInd.Even.cheat
    levelParams := []
    type := mkForall `n .default natConst (mkApp (mkConst evenName) (mkBVar 0))
    induct := evenName
    cidx := 0
    numParams := 0
    numFields := 1
    isUnsafe := false
  }
  let fourExpr :=
    mkApp (mkConst ``Nat.succ)
      (mkApp (mkConst ``Nat.succ)
        (mkApp (mkConst ``Nat.succ)
          (mkApp (mkConst ``Nat.succ) (mkConst ``Nat.zero))))
  let thmVal : TheoremVal := {
    name := `ProbeInd.even_four
    levelParams := []
    type := mkApp (mkConst evenName) fourExpr
    value := mkApp (mkConst `ProbeInd.Even.cheat) fourExpr
  }
  let mut replayMap : Std.HashMap Name ConstantInfo := {}
  replayMap := replayMap.insert evenName (.inductInfo solutionInd)
  replayMap := replayMap.insert `ProbeInd.Even.cheat (.ctorInfo cheatCtor)
  replayMap := replayMap.insert `ProbeInd.even_four (.thmInfo thmVal)
  let kenv' ← env.toKernelEnv.replay replayMap
  let replayedOk := (kenv'.find? `ProbeInd.even_four).isSome
  IO.println s!"  Kernel.Environment.replay accepted spoofed inductive + `even_four`: {replayedOk}"
  assertTrue "Kernel.Environment.replay accepts spoofed Even.cheat" replayedOk

/-- Reproduces `Compare.loop`'s syntactic `ConstantInfo` `BEq` rejection of
    student-proved helper theorems referenced by non-hole definitions. -/
def runTheoremDepInNonHoleDefProbe : IO Unit := do
  IO.println "\n=== 2B. `Comparator` `.thmInfo` `BEq` Proof-Irrelevance Rejection ==="
  let trueConst := mkConst ``True
  let trivialConst := mkConst ``True.intro
  let sorryProof :=
    mkApp2 (mkConst ``sorryAx [0]) trueConst (mkConst ``Bool.true)
  let challengeLemma : ConstantInfo := .thmInfo {
    name := `ProbeThm.helper_lemma
    levelParams := []
    type := trueConst
    value := sorryProof
    all := [`ProbeThm.helper_lemma]
  }
  let solutionLemma : ConstantInfo := .thmInfo {
    name := `ProbeThm.helper_lemma
    levelParams := []
    type := trueConst
    value := trivialConst
    all := [`ProbeThm.helper_lemma]
  }
  let hdrEq := challengeLemma.toConstantVal == solutionLemma.toConstantVal
  let fullEq := challengeLemma == solutionLemma
  IO.println s!"  challengeLemma.toConstantVal == solutionLemma.toConstantVal: {hdrEq}"
  IO.println s!"  challengeLemma == solutionLemma (`Compare.loop` line 112):   {fullEq}"
  assertTrue "theorem headers match" hdrEq
  assertTrue "ConstantInfo BEq rejects different proof terms" (!fullEq)

def main : IO UInt32 := do
  let leanExe ← IO.appPath
  let sysroot ← Lean.findSysroot leanExe.toString
  IO.FS.withTempDir fun tmpDir => do
    let templateOlean ← compileLeanModule leanExe tmpDir "Template" templateSrc
    let submissionOlean ← compileLeanModule leanExe tmpDir "Submission" submissionSrc
    let asyncTrueOlean ← compileLeanModule leanExe tmpDir "AsyncTrue" scopeAndAsyncSrc
      #["-DElab.async=true"]
    let asyncFalseOlean ← compileLeanModule leanExe tmpDir "AsyncFalse" scopeAndAsyncSrc
      #["-DElab.async=false"]

    initSearchPath sysroot [tmpDir]

    let (templateMd, _) ← readModuleData templateOlean
    let (submissionMd, _) ← readModuleData submissionOlean

    IO.println "=== 1A. `Template` vs. `Submission` Match Deduplication (`List.IsNil` / `List.In`) ==="
    let some tInF := findInMod? templateMd `LF.Poly.List.In._f
      | throw <| IO.userError "missing Template LF.Poly.List.In._f"
    let some sInF := findInMod? submissionMd `LF.Poly.List.In._f
      | throw <| IO.userError "missing Submission LF.Poly.List.In._f"
    let some tMatch := findInMod? templateMd `LF.Poly.List.In.match_1
      | throw <| IO.userError "missing Template LF.Poly.List.In.match_1"
    let some sMatch := findInMod? submissionMd `LF.Poly.List.IsNil.match_1
      | throw <| IO.userError "missing Submission LF.Poly.List.IsNil.match_1"

    let tInFMatchers := (getAllUsedConsts tInF).filter hasMatchSubstr
    let sInFMatchers := (getAllUsedConsts sInF).filter hasMatchSubstr
    let hdrEq := tInF.toConstantVal == sInF.toConstantVal
    let fullEq := tInF == sInF
    let matchTypeEq := tMatch.type == sMatch.type
    let matchValEq := tMatch.value! == sMatch.value!

    IO.println s!"  Template `LF.Poly.List.In._f` matchers:   {tInFMatchers}"
    IO.println s!"  Submission `LF.Poly.List.In._f` matchers: {sInFMatchers}"
    IO.println s!"  `LF.Poly.List.In._f` toConstantVal BEq:   {hdrEq}"
    IO.println s!"  `LF.Poly.List.In._f` ConstantInfo BEq:    {fullEq}"
    IO.println s!"  Matcher types identical:                  {matchTypeEq}"
    IO.println s!"  Matcher values identical:                 {matchValEq}"

    assertTrue "Template List.In._f uses List.In.match_1"
      (tInFMatchers == #[`LF.Poly.List.In.match_1])
    assertTrue "Submission List.In._f uses List.IsNil.match_1"
      (sInFMatchers == #[`LF.Poly.List.IsNil.match_1])
    assertTrue "Submission has no List.In.match_1"
      (findInMod? submissionMd `LF.Poly.List.In.match_1).isNone
    assertTrue "List.In._f headers equal" hdrEq
    assertTrue "List.In._f ConstantInfo BEq false" (!fullEq)
    assertTrue "Matcher types equal" matchTypeEq
    assertTrue "Matcher values equal" matchValEq

    let subEnv ← importModules #[{ module := `Submission }] {}
    let declTMatch : Declaration := match tMatch with
      | .defnInfo d => .defnDecl d
      | _ => unreachable!
    let subEnvBoth ← match subEnv.addDeclCore 0 0 declTMatch none with
      | Except.ok e => pure e
      | Except.error _ => throw <| IO.userError "failed to add tMatch"
    let kDefEq := Kernel.isDefEqGuarded subEnvBoth {} tInF.value! sInF.value!
    IO.println s!"  Kernel.isDefEqGuarded(Template.List.In._f, Submission.List.In._f): {kDefEq}"
    assertTrue "Kernel.isDefEqGuarded equates List.In._f bodies" kDefEq

    IO.println "\n=== 1B. Namespace Isolation, Sort Generalization, `if-then-else`, and `Elab.async` ==="
    let (asyncTrueMd, _) ← readModuleData asyncTrueOlean
    let (asyncFalseMd, _) ← readModuleData asyncFalseOlean

    let getMatchers (md : ModuleData) (n : Name) : IO (Array Name) := do
      let some c := findInMod? md n
        | throw <| IO.userError s!"missing constant {n}"
      return (getAllUsedConsts c).filter hasMatchSubstr

    let nsBMatchers ← getMatchers asyncTrueMd `NsB.secondMatch
    let boolMatchers ← getMatchers asyncTrueMd `MitigationSort.firstBoolMatch
    let propMatchers ← getMatchers asyncTrueMd `MitigationSort.secondPropMatch
    let iteMatchers ← getMatchers asyncTrueMd `MitigationIte.firstIte
    let thm1AsyncTrue ← getMatchers asyncTrueMd `ThmVsDef.thmWithMatch
    let thm2AsyncTrue ← getMatchers asyncTrueMd `ThmVsDef.thm2WithMatch
    let thm1AsyncFalse ← getMatchers asyncFalseMd `ThmVsDef.thmWithMatch
    let thm2AsyncFalse ← getMatchers asyncFalseMd `ThmVsDef.thm2WithMatch

    IO.println s!"  NsB.secondMatch matchers:                     {nsBMatchers}"
    IO.println s!"  MitigationSort.firstBoolMatch (: Bool):       {boolMatchers}"
    IO.println s!"  MitigationSort.secondPropMatch (: Prop):      {propMatchers}"
    IO.println s!"  MitigationIte.firstIte (if-then-else):        {iteMatchers}"
    IO.println s!"  ThmVsDef.thm2WithMatch (Elab.async=true):     {thm2AsyncTrue}"
    IO.println s!"  ThmVsDef.thm2WithMatch (Elab.async=false):    {thm2AsyncFalse}"

    assertTrue "NsB.secondMatch reuses NsA.firstMatch.match_1"
      (nsBMatchers == #[`NsA.firstMatch.match_1])
    assertTrue "firstBoolMatch reuses NsA.firstMatch.match_1"
      (boolMatchers == #[`NsA.firstMatch.match_1])
    assertTrue "secondPropMatch reuses NsA.firstMatch.match_1"
      (propMatchers == #[`NsA.firstMatch.match_1])
    assertTrue "if-then-else avoids matcherExt"
      iteMatchers.isEmpty
    assertTrue "Elab.async=true isolates theorem matchers"
      (thm1AsyncTrue != thm2AsyncTrue)
    assertTrue "Elab.async=false shares theorem matchers"
      (thm1AsyncFalse == thm2AsyncFalse &&
       thm2AsyncFalse == #[`ThmVsDef.thmWithMatch.match_1])

    runInductiveHoleUnsoundnessProbe
    runTheoremDepInNonHoleDefProbe

    IO.println "\nAll ProbeComparatorAndMatcherDedup assertions passed."
    return 0

end ProbeComparatorAndMatcherDedup

def main : IO UInt32 := ProbeComparatorAndMatcherDedup.main
