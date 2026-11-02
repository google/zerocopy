-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean

/-!
# Self-Contained Probe: `sf_recall`, Matcher Edge Cases, and `matcherExt`

This standalone Lean `v4.34.1` probe embeds the core `SFLCompat.Recall`
elaboration-based drift checker from `plclub/sf-in-lean`
(`13e9425b4647402a09316c1d39fa555e9bc3c257`) and verifies:

1. Positive semantic matches (`sf_recall`, `sf_recall +strictUniverse`, and
   `sf_recall statement`) across representative Anneal declarations, including
   alpha-renaming, definitional reformulations (`Language.WellFormedOn` named
   fields vs. anonymous constructor), and universe specialization.
2. Negative semantic drift detection (constructor order, constructor names,
   parameter types, structure field names, `class` vs. `structure` metadata,
   theorem hypotheses, and strict universe mismatches).
3. Unchecked declaration metadata (`abbrev` vs. `def` reducibility hints,
   structure field defaults and `private` visibility, and `theorem` recalled as
   `def`).
4. Five edge cases in `sf_recall` involving auxiliary matcher constants
   (`<decl>.match_1` and `<decl>._sparseCasesOn_1`), including the cross-module
   failure caused by `Lean.Meta.Match.matcherExt` not persisting across `.olean`
   imports, together with the mechanized `sf_recall_fixed` repair (`renameExact`
   plus `unfoldMatchersIn`).
-/

namespace ProbeRecallAndMatcherExt

open Lean Meta Elab Command

-- ============================================================================
-- 1. Core `SFLCompat.Recall` Implementation (`Common.lean` & `Check.lean`)
-- ============================================================================

/-- All `declId` syntax nodes in a command, in source order. -/
partial def declIds (stx : Syntax) : Array Syntax :=
  let inner := stx.getArgs.flatMap declIds
  if stx.isOfKind ``Lean.Parser.Command.declId then #[stx] ++ inner else inner

/-- The syntax node and user-written name of a single recalled declaration. -/
structure DeclSyntax where
  ident : Syntax
  written : Name

/-- Extracts the single `declId` node of a declaration command, rejecting
    commands that declare zero names or multiple names (`mutual` blocks). -/
def declaredName (cmd : Syntax) : CommandElabM DeclSyntax := do
  let defined := declIds cmd
  match h : defined.size with
  | 0 => throwErrorAt cmd "the restated command does not declare a name"
  | 1 =>
    let declId := defined[0]
    return { ident := declId[0], written := declId[0].getId }
  | n + 2 =>
    for h : i in 0...(n + 1) do
      logErrorAt defined[i]
        "the restated command declares several names; recall one at a time"
    throwErrorAt defined[n + 1]
      "the restated command declares several names; recall one at a time"

/-- Pairs an internal environment constant name (possibly private) with its
    user-facing display name. -/
structure DeclId where
  actual : Name
  display : Name

def DeclId.ofActual (actual : Name) : DeclId :=
  { actual, display := privateToUserName actual }

/-- Looks up the elaborated declaration name inside the temporary namespace. -/
def tempDeclId (userName : Name) : CommandElabM DeclId := do
  let env ← getEnv
  let privateName := mkPrivateName env userName
  let actual ←
    if env.contains privateName then pure privateName
    else if env.contains userName then pure userName
    else throwError "the re-elaborated declaration '{userName}' was not found"
  return .ofActual actual

/-- Rewrites any constant name `n` that has `chk` as a prefix to replace `chk`
    with `orig` (`SFLCompat/Recall/Check.lean:65-69`). -/
def renameBackName (chk orig n : Name) : Name :=
  if chk.isPrefixOf n then n.replacePrefix chk orig
  else
    let chk := privateToUserName chk
    if chk.isPrefixOf n then n.replacePrefix chk orig else n

/-- Applies `renameBackName` to all `.const` nodes in `e`
    (`SFLCompat/Recall/Check.lean:79-84`). -/
def renameBack (chk orig : DeclId) (e : Expr) : Expr :=
  e.replace fun
    | .const n us =>
      let n' := renameBackName chk.actual orig.actual n
      if n == n' then none else some (.const n' us)
    | _ => none

/-- Rewrites hidden-namespace constant references in `InfoTree` nodes back to
    the original constant (`SFLCompat/Recall/Check.lean:93-110`). -/
partial def renameBackInfoTree (chk orig : DeclId) (t : InfoTree) : InfoTree :=
  match t with
  | .context (.parentDeclCtx n) t' =>
    .context (.parentDeclCtx (renameBackName chk.actual orig.actual n))
      (renameBackInfoTree chk orig t')
  | .context ctx t' => .context ctx (renameBackInfoTree chk orig t')
  | .node i children =>
    let i := match i with
      | .ofTermInfo ti => .ofTermInfo (reTerm ti)
      | .ofDelabTermInfo dti =>
        .ofDelabTermInfo { dti with toTermInfo := reTerm dti.toTermInfo }
      | other => other
    .node i (children.map (renameBackInfoTree chk orig))
  | .hole m => .hole m
where
  reTerm (ti : TermInfo) : TermInfo :=
    { ti with
      expr := renameBack chk orig ti.expr
      expectedType? := ti.expectedType?.map (renameBack chk orig) }

abbrev Specialization := List Name × List Level

def renameBackS (specialization? : Option Specialization)
    (chk orig : DeclId) (e : Expr) : Expr :=
  match specialization? with
  | none => renameBack chk orig e
  | some (_params, levels) =>
    e.replace fun
      | .const n _ =>
        let n' := renameBackName chk.actual orig.actual n
        if n == n' then none else some <| .const n' levels
      | _ => none

def levelsFor (specialization : Specialization) (info : ConstantInfo) :
    TermElabM (List Level) :=
  let (params, levels) := specialization
  info.levelParams.mapM fun param =>
    match params.findIdx? (· == param) with
    | some index => pure levels[index]!
    | none => throwError
      "universe parameter '{param}' of '{info.name}' is not a parameter"

/-- Compares the types of `x` and `chk` up to `Meta.isDefEq`
    (`SFLCompat/Recall/Check.lean:146-166`). -/
def checkTypesMatch (x chk : DeclId) (ref : Syntax)
    (specialization? : Option Specialization)
    (renChk : DeclId := chk) (renOrig : DeclId := x) : TermElabM Unit := do
  let origInfo ← getConstInfo x.actual
  let chkInfo ← getConstInfo chk.actual
  if specialization?.isNone then
    unless origInfo.levelParams.length == chkInfo.levelParams.length do
      throwErrorAt ref "universe parameters of '{x.display}' do not match"
  let origType ← match specialization? with
    | none => pure origInfo.type
    | some s => origInfo.instantiateTypeLevelParams <$> levelsFor s origInfo
  let chkType := match specialization? with
    | none =>
      (renameBackS specialization? renChk renOrig chkInfo.type).instantiateLevelParams
        chkInfo.levelParams (origInfo.levelParams.map .param)
    | some _ => renameBackS specialization? renChk renOrig chkInfo.type
  unless ← isDefEq chkType origType do
    throwErrorAt ref
      m!"the statement of '{x.display}' does not match.\n\
          Original:{indentD origInfo.type}\nRestated:{indentD chkType}"

partial def ctorStxs (stx : Syntax) : Array Syntax :=
  let inner := stx.getArgs.flatMap ctorStxs
  if stx.isOfKind ``Lean.Parser.Command.ctor
      || stx.isOfKind ``Lean.Parser.Command.structCtor then
    #[stx] ++ inner
  else inner

/-- Compares the constant kinds, values, constructors, and structure metadata of
    `x` and `chk` (`SFLCompat/Recall/Check.lean:215-289`). -/
def checkMatchCore (x chk : DeclId) (ref : Syntax)
    (specialization? : Option Specialization) : TermElabM Unit := do
  checkTypesMatch x chk ref specialization?
  let origInfo ← getConstInfo x.actual
  let chkInfo ← getConstInfo chk.actual
  match origInfo, chkInfo with
  | .defnInfo orig, .defnInfo restated =>
    let origVal ← match specialization? with
      | none => pure orig.value
      | some s => origInfo.instantiateValueLevelParams! <$> levelsFor s origInfo
    let chkVal := match specialization? with
      | none =>
        (renameBackS specialization? chk x restated.value).instantiateLevelParams
          restated.levelParams (orig.levelParams.map .param)
      | some _ => renameBackS specialization? chk x restated.value
    unless ← isDefEq chkVal origVal do
      throwErrorAt ref
        m!"the value of '{x.display}' does not match.\n\
            Original:{indentD orig.value}\nRestated:{indentD chkVal}"
  | .inductInfo orig, .inductInfo restated =>
    unless orig.numParams == restated.numParams
        && orig.numIndices == restated.numIndices do
      throwErrorAt ref "parameters or indices of '{x.display}' do not match"
    unless orig.ctors.length == restated.ctors.length do
      throwErrorAt ref
        m!"'{x.display}' has {orig.ctors.length} constructors, \
            the restatement has {restated.ctors.length}"
    let ctorRefs := ctorStxs ref
    let mut i := 0
    for origCtorActual in orig.ctors, chkCtorActual in restated.ctors do
      let origCtor := DeclId.ofActual origCtorActual
      let chkCtor := DeclId.ofActual chkCtorActual
      let ctorRef := ctorRefs[i]?.getD ref
      let renamedChkCtor := DeclId.ofActual <|
        chkCtor.actual.replacePrefix chk.actual x.actual
      unless origCtor.actual == renamedChkCtor.actual do
        throwErrorAt ctorRef
          m!"constructor '{renamedChkCtor.display}' does not match \
              '{origCtor.display}'"
      checkTypesMatch origCtor chkCtor ctorRef specialization?
        (renChk := chk) (renOrig := x)
      i := i + 1
    let env ← getEnv
    match getStructureInfo? env x.actual, getStructureInfo? env chk.actual with
    | some origSi, some chkSi =>
      let origFields := origSi.fieldNames.map DeclId.ofActual
      let chkFields := chkSi.fieldNames.map DeclId.ofActual
      unless origFields.map (·.actual) == chkFields.map (·.actual) do
        throwErrorAt ref m!"the fields of '{x.display}' do not match"
      unless getOutParamPositions? env x.actual == getOutParamPositions? env chk.actual
          && getOutLevelParamPositions? env x.actual
             == getOutLevelParamPositions? env chk.actual do
        throwErrorAt ref m!"the type-class metadata of '{x.display}' does not match"
    | some _, none =>
      throwErrorAt ref m!"'{x.display}' is a structure, but the restatement is not"
    | none, some _ =>
      throwErrorAt ref m!"'{x.display}' is not a structure, but the restatement is"
    | none, none => pure ()
  | .thmInfo _, .thmInfo _ => pure ()
  | .thmInfo _, .defnInfo _ => pure ()
  | .axiomInfo _, .axiomInfo _ => pure ()
  | .opaqueInfo _, .opaqueInfo _ => pure ()
  | _, _ =>
    throwErrorAt ref
      m!"'{x.display}' and its restatement are different kinds of declaration"

def checkpointDefEq' (action : TermElabM Bool) : TermElabM Bool :=
  controlAt MetaM fun runInBase =>
    checkpointDefEq (mayPostpone := false) (runInBase action)

def checkMatch (x chk : DeclId) (ref : Syntax)
    (strictUniverse : Bool) : TermElabM Unit := do
  let origInfo ← getConstInfo x.actual
  let chkInfo ← getConstInfo chk.actual
  if origInfo.levelParams.length == chkInfo.levelParams.length then
    checkMatchCore x chk ref none
  else if !strictUniverse && !origInfo.levelParams.isEmpty
      && chkInfo.levelParams.isEmpty then
    let succeeded ← checkpointDefEq' do
      let levels ← mkFreshLevelMVarsFor origInfo
      checkMatchCore x chk ref (some (origInfo.levelParams, levels))
      pure true
    unless succeeded do
      throwErrorAt ref m!"the statement of '{x.display}' does not match"
  else
    throwErrorAt ref m!"universe parameters of '{x.display}' do not match"

syntax (name := recallChk) "sf_recall " command : command
syntax (name := recallChkStrict)
  "sf_recall" " +" noWs &"strictUniverse" ppSpace command : command
syntax (name := recallChkStmt)
  "sf_recall " &"statement " ident " : " term : command

def elabRecallCommand (cmd : Syntax) (strictUniverse : Bool) :
    CommandElabM Unit := do
  let decl ← declaredName cmd
  let xActual ← liftCoreM <| withoutExporting <|
    realizeGlobalConstNoOverloadWithInfo decl.ident
  let x := DeclId.ofActual xActual
  let ns := Name.mkStr1 (← liftCoreM (mkFreshId : CoreM Name)).toString
  let envBefore ← getEnv
  try
    let chk ← withScope
        (fun sc => { sc with currNamespace := sc.currNamespace ++ ns }) do
      let saved ← getResetInfoTrees
      try
        elabCommand cmd
        let userName := (← getScope).currNamespace ++ decl.written
        let chk ← tempDeclId userName
        let inner ← getResetInfoTrees
        modifyInfoState fun s =>
          { s with trees := saved ++ inner.map (renameBackInfoTree chk x) }
        return chk
      catch e =>
        let inner ← getResetInfoTrees
        modifyInfoState fun s => { s with trees := saved ++ inner }
        throw e
    runTermElabM fun _ => checkMatch x chk cmd strictUniverse
  finally
    setEnv envBefore

def elabRecallStatement (ident stmt : Syntax) : CommandElabM Unit := do
  let xActual ← liftCoreM <| withoutExporting <|
    realizeGlobalConstNoOverloadWithInfo ident
  let x := DeclId.ofActual xActual
  addConstInfo ident x.actual
  runTermElabM fun _ => do
    let t ← Term.elabType stmt
    Term.synthesizeSyntheticMVarsNoPostponing
    let t ← instantiateMVars (← Term.levelMVarToParam t)
    let origInfo ← getConstInfo x.actual
    let stParams := (collectLevelParams {} t).params
    unless stParams.size == origInfo.levelParams.length do
      throwErrorAt stmt m!"universe parameters of '{x.display}' do not match"
    let t := t.instantiateLevelParams stParams.toList
      (origInfo.levelParams.map .param)
    unless ← isDefEq t origInfo.type do
      throwErrorAt stmt
        m!"the restated statement of '{x.display}' does not match.\n\
            Original:{indentD origInfo.type}\nRestated:{indentD t}"

elab_rules : command
  | `(sf_recall $cmd:command) => elabRecallCommand cmd false
  | `(sf_recall +strictUniverse $cmd:command) => elabRecallCommand cmd true
  | `(sf_recall statement $ident:ident : $stmt:term) =>
    elabRecallStatement ident stmt

/-- Helper command elaborator that verifies an inner command fails and stores
    the concatenated error messages into a `String` constant `id` for assertion
    in `main`. -/
elab "capture_expected_error " id:ident cmd:command : command => do
  let savedState ← get
  modify fun s => { s with messages := {} }
  try
    elabCommand cmd
  catch e =>
    logError e.toMessageData
  let newMsgs := (← get).messages
  let hasErr := newMsgs.hasErrors
  let mut msgStrs : Array String := #[]
  for m in newMsgs.toList do
    msgStrs := msgStrs.push (← m.data.toString)
  let rendered := String.intercalate "\n" msgStrs.toList
  set savedState
  unless hasErr do
    throwErrorAt cmd "expected command to fail, but it succeeded"
  let decl := Declaration.defnDecl {
    name := (← getCurrNamespace) ++ id.getId
    levelParams := []
    type := mkConst ``String
    value := mkStrLit rendered
    hints := .abbrev
    safety := .safe
  }
  liftCoreM <| addAndCompile decl

-- ============================================================================
-- 2. Representative Anneal Declarations (`trusted/lean/` & `theory/Anneal/`)
-- ============================================================================

namespace AnnealSample

instance instLEProp : LE Prop where
  le P Q := P → Q

instance instLEFun {A : Type u} {B : Type v} [LE B] : LE (A → B) where
  le f g := ∀ a, f a ≤ g a

abbrev BehaviorSet (α : Type u) : Type u := α → Prop

structure Partial (B : Type u) : Type u where
  defined : Prop
  val : defined → B

def Partial.pure {B : Type u} (b : B) : Partial B :=
  ⟨True, fun _ => b⟩

instance instLEPartial {B : Type u} [LE B] : LE (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂

def Partial.contract {Out : Type u}
    (safetyPre funcPre : Prop) (post : Out → Prop) :
    Partial (BehaviorSet Out) where
  defined := safetyPre
  val := fun _ out => funcPre → post out

structure Language : Type 1 where
  Prog : Type
  Query : Type
  Out : Type
  sem : Prog → Query → Partial (BehaviorSet Out)

abbrev Language.Behavior (L : Language) : Type :=
  L.Query → Partial (BehaviorSet L.Out)

def Language.WellFormedOn (L : Language) (safetyPre : L.Query → Prop) :
    L.Behavior :=
  fun q => ⟨safetyPre q, fun _ _ => True⟩

abbrev Language.WellFormed (L : Language) : L.Behavior :=
  L.WellFormedOn (fun _ => True)

def Language.ContractSpec (L : Language)
    (safetyPre funcPre : L.Query → Prop)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  fun q => Partial.contract (safetyPre q) (funcPre q) (post q)

abbrev Compiles (L_src L_tgt : Language)
    (π_c : L_src.Behavior → L_tgt.Behavior)
    (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  L_tgt.sem t ≤ π_c (L_src.sem s)

structure Compiler (L_src L_tgt : Language) : Type 1 where
  compile : L_src.Prog → L_tgt.Prog
  π : L_src.Behavior → L_tgt.Behavior

def Compiler.Verified {L_src L_tgt : Language}
    (C : Compiler L_src L_tgt) (s : L_src.Prog) (spec : L_src.Behavior) : Prop :=
  L_src.sem s ≤ spec ∧
  Compiles L_src L_tgt C.π s (C.compile s) ∧
  L_tgt.sem (C.compile s) ≤ C.π spec

theorem safe_contractSpec_preserves_wellFormed
    {L : Language} (funcPre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    L.ContractSpec (fun _ => True) funcPre post ≤ L.WellFormed :=
  fun _ h_pre => ⟨h_pre, fun _ _ => trivial⟩

theorem misplaced_contractSpec_violates_wellFormed
    {L : Language} (funcPre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (q : L.Query) (h_not_pre : ¬ funcPre q) :
    ¬ (L.ContractSpec funcPre (fun _ => True) post ≤ L.WellFormed) := by
  intro h_ref
  exact h_not_pre (h_ref q trivial).1

inductive ChoiceKind where
  | demonic
  | angelic

inductive TerminationKind (Val : Type) where
  | normal (ret : Val)
  | unwind

inductive FailureKind where
  | ub
  | contractViolation

inductive StepResult (State Obs Val : Type) where
  | step (obs : Obs) (next : State)
  | choice (kind : ChoiceKind) (branches : State → Prop)
  | terminated (term : TerminationKind Val)
  | failed (err : FailureKind)

inductive PrefixOutcome (Val : Type) where
  | running
  | terminated (term : TerminationKind Val)
  | failed (err : FailureKind)
  | stuck

def PrefixOutcome.isSafe : PrefixOutcome Val → Prop
  | .running => True
  | .terminated _ => True
  | .failed _ => False
  | .stuck => False

/-- Non-matcher definition using projections (`p.1 + p.2`), which creates no
    `pairSumProj.match_1` constant in the environment. -/
def pairSumProj (p : Nat × Nat) : Nat :=
  p.1 + p.2

/-- Recursive list-conjunction definition from `Trusted.VerificationResult`. -/
def AllHold : List Prop → Prop
  | [] => True
  | p :: rest => p ∧ AllHold rest

inductive Value : Type where
  | scalar (bits : Nat)
  | unit

structure CapturedMir : Type where
  defPath : String
  numLocals : Nat := 0

structure Claim : Type 1 where
  body : CapturedMir
  pre : List Value → Prop
  post : List Value → Value → Prop

class ItemSpec (defId : String) : Type 1 where
  pre : List Value → Prop := fun _ => True
  post : List Value → Value → Prop := fun _ _ => True

end AnnealSample

open AnnealSample

-- ============================================================================
-- 3. Positive Matches, Unchecked Metadata, and Negative Drift Detection
-- ============================================================================

-- 3a. Positive match: exact inductive (`StepResult`) and structure (`Partial`)
sf_recall
  inductive StepResult (State Obs Val : Type) where
    | step (obs : Obs) (next : State)
    | choice (kind : ChoiceKind) (branches : State → Prop)
    | terminated (term : TerminationKind Val)
    | failed (err : FailureKind)

sf_recall
  structure Partial (B : Type u) : Type u where
    defined : Prop
    val : defined → B

-- 3b. Positive match: alpha-renamed binders and unfolded `Compiles`
sf_recall
  def Compiler.Verified {L1 L2 : Language}
      (comp : Compiler L1 L2) (prog : L1.Prog) (contract : L1.Behavior) : Prop :=
    L1.sem prog ≤ contract ∧
    (L2.sem (comp.compile prog) ≤ comp.π (L1.sem prog)) ∧
    L2.sem (comp.compile prog) ≤ comp.π contract

-- 3c. Positive match: `Language.WellFormedOn` restated with named structure
-- fields `{ defined := ..., val := ... }` against `⟨..., ...⟩`
sf_recall
  def Language.WellFormedOn (L : Language) (safetyPre : L.Query → Prop) :
      L.Behavior :=
    fun q => {
      defined := safetyPre q
      val := fun _ _ => True
    }

-- 3d. Positive match: monomorphic universe specialization without
-- `+strictUniverse`, and `sf_recall statement` on theorems
sf_recall
  structure Partial (B : Type) : Type where
    defined : Prop
    val : defined → B

sf_recall statement safe_contractSpec_preserves_wellFormed :
    ∀ {L : Language} (funcPre : L.Query → Prop) (post : L.Query → L.Out → Prop),
      L.ContractSpec (fun _ => True) funcPre post ≤ L.WellFormed

-- 3e. Unchecked metadata accepted by `sf_recall`:
-- (1) `abbrev` recalled as `def`, (2) structure field default and `private`
-- visibility changed, (3) `theorem` recalled as `def`.
sf_recall
  def Compiles (L_src L_tgt : Language)
      (π_c : L_src.Behavior → L_tgt.Behavior)
      (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
    L_tgt.sem t ≤ π_c (L_src.sem s)

sf_recall
  structure CapturedMir : Type where
    defPath : String
    private numLocals : Nat := 999

sf_recall
  def safe_contractSpec_preserves_wellFormed
      {L : Language} (funcPre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
      L.ContractSpec (fun _ => True) funcPre post ≤ L.WellFormed :=
    fun _ h_pre => ⟨h_pre, fun _ _ => trivial⟩

-- 3f. Negative drift detection
section NegativeDrift
set_option linter.unusedVariables false

capture_expected_error errCtorOrder
  sf_recall
    inductive StepResult (State Obs Val : Type) where
      | choice (kind : ChoiceKind) (branches : State → Prop)
      | step (obs : Obs) (next : State)
      | terminated (term : TerminationKind Val)
      | failed (err : FailureKind)

capture_expected_error errStructField
  sf_recall
    structure Partial (B : Type u) : Type u where
      wellDefined : Prop
      val : wellDefined → B

capture_expected_error errClassVsStruct
  sf_recall
    structure ItemSpec (defId : String) : Type 1 where
      pre : List Value → Prop
      post : List Value → Value → Prop

capture_expected_error errThmHyp
  sf_recall statement misplaced_contractSpec_violates_wellFormed :
    ∀ {L : Language} (funcPre : L.Query → Prop) (post : L.Query → L.Out → Prop)
      (q : L.Query),
      funcPre q →
      ¬ (L.ContractSpec funcPre (fun _ => True) post ≤ L.WellFormed)

capture_expected_error errStrictUniv
  sf_recall +strictUniverse
    structure Partial (B : Type) : Type where
      defined : Prop
      val : defined → B

end NegativeDrift

-- ============================================================================
-- 4. Five Matcher & Cross-Module `matcherExt` Edge Cases and `sf_recall_fixed`
-- ============================================================================

-- Edge Case 1: Dangling `.match_1` crash when `orig` has no matcher.
-- `pairSumProj` is defined via `p.1 + p.2` (no `pairSumProj.match_1` exists).
-- Restating it with pattern matching creates `_uniq.N.pairSumProj.match_1`,
-- which `renameBackName` rewrites to the non-existent
-- `AnnealSample.pairSumProj.match_1`.
capture_expected_error errEdgeCase1DanglingMatcher
  sf_recall
    def pairSumProj : Nat × Nat → Nat
      | (a, b) => a + b

-- Edge Case 2: Ill-typed `Expr` corruption when `match` arms are reordered.
-- Placing `| .stuck => False` first gives
-- `_uniq.N.PrefixOutcome.isSafe.match_1` a different minor-premise order than
-- `PrefixOutcome.isSafe.match_1`. `renameBackName` rewrites the head constant
-- to `PrefixOutcome.isSafe.match_1`, feeding `(fun _ : Unit => True)` into the
-- `(TerminationKind Val → Prop)` slot.
capture_expected_error errEdgeCase2ReorderedArms
  sf_recall
    def PrefixOutcome.isSafe : PrefixOutcome Val → Prop
      | .stuck => False
      | .running => True
      | .terminated _ => True
      | .failed _ => False

-- Edge Case 3: `Meta.isDefEq` vs. `Kernel.isDefEq` on neutral matcher apps.
-- Restating `PrefixOutcome.isSafe` with `PrefixOutcome.casesOn` fails in
-- `Meta.isDefEq` because `Meta.whnfCore` refuses to unfold `isMatcherApp` when
-- the discriminant `o` is a free variable, even though `Kernel.isDefEq` reduces
-- both to `PrefixOutcome.casesOn` and returns `true`.
capture_expected_error errEdgeCase3CasesOnNeutral
  sf_recall
    def PrefixOutcome.isSafe (o : PrefixOutcome Val) : Prop :=
      PrefixOutcome.casesOn o True (fun _ => True) (fun _ => False) False

-- Edge Case 4: Lean 4.34 `_sparseCasesOn_1` wildcard compilation on >= 4 ctors.
-- Using a catch-all `| _ => False` for `.failed _` and `.stuck` generates
-- `_sparseCasesOn_1` with motive `fun t => (Nat.hasNotBit 3 t.ctorIdx → ...)`,
-- which requires a commuting conversion on a neutral variable `t` and fails
-- both `Meta.isDefEq` and `Kernel.isDefEq`.
capture_expected_error errEdgeCase4SparseCasesOn
  sf_recall
    def PrefixOutcome.isSafe : PrefixOutcome Val → Prop
      | .running => True
      | .terminated _ => True
      | _ => False

-- Edge Case 5: Cross-module `matcherExt` non-persistence crash on byte-for-byte
-- identical definitions.
--
-- When `ModA` defines `earlierIsNil` and `laterIsNil` with the same `match`
-- splitter on `List α`, `earlierIsNil` populates the non-persistent
-- `Lean.Meta.Match.matcherExt` (`registerEnvExtension (pure {}) (asyncMode :=
-- .local)`), so `laterIsNil` reuses `earlierIsNil.match_1` and never creates
-- `laterIsNil.match_1`. When `ModB` imports `ModA.olean`, `ModA`'s constants
-- and persistent `Match.Extension` (`MatcherInfo`) are loaded, but the
-- non-persistent `matcherExt` is empty.
--
-- We verify both regimes in-process by elaborating `earlierIsNil` and
-- `laterIsNil` (testing same-module `sf_recall` while `matcherExt` is live),
-- and then transferring only the `.olean`-persisted constants and `MatcherInfo`
-- into a clean pre-module `Environment` whose non-persistent `matcherExt` is
-- empty (reproducing the exact cross-module `.olean` import state).

namespace CrossModuleSim

/-- Runs `earlierIsNil` and `laterIsNil` in `ModA`'s live elaboration state
    (where `matcherExt` holds `earlierIsNil.match_1`), verifies that same-module
    `sf_recall` succeeds, and then resets to `envBeforeModA` (where the
    non-persistent `matcherExt` is empty) while replaying only the `.olean`
    declarations and persistent `MatcherInfo`. -/
elab "setup_and_test_cross_module_matcher_ext" : command => do
  let envBeforeModA ← getEnv
  let idEarlier := mkIdent `earlierIsNil
  let idLater := mkIdent `laterIsNil
  let idAlpha := mkIdent `α
  elabCommand (← `(
    def $idEarlier:ident {$idAlpha:ident : Type} (xs : List $idAlpha) : Bool :=
      match xs with
      | [] => true
      | _ :: _ => false
  ))
  elabCommand (← `(
    def $idLater:ident {$idAlpha:ident : Type} (xs : List $idAlpha) : Bool :=
      match xs with
      | [] => true
      | _ :: _ => false
  ))
  let envModA ← getEnv
  let currNs ← getCurrNamespace
  let earlierMatcher := currNs ++ `earlierIsNil.match_1
  let laterMatcher := currNs ++ `laterIsNil.match_1
  unless envModA.contains earlierMatcher && !envModA.contains laterMatcher do
    throwError "unexpected matcher constants in ModA state"

  -- In the defining module itself, `matcherExt` still holds
  -- `earlierIsNil.match_1`, so stock `sf_recall` reuses `earlierIsNil.match_1`
  -- and succeeds.
  elabCommand (← `(
    sf_recall
      def $idLater:ident {$idAlpha:ident : Type} (xs : List $idAlpha) : Bool :=
        match xs with
        | [] => true
        | _ :: _ => false
  ))

  -- Reconstruct the exact post-`.olean`-import environment for a downstream
  -- module: reset to `envBeforeModA` (where `matcherExt` is empty) and replay
  -- `earlierIsNil.match_1`, `earlierIsNil`, `laterIsNil`, and `MatcherInfo`.
  setEnv envBeforeModA
  for cname in [earlierMatcher, currNs ++ `earlierIsNil, currNs ++ `laterIsNil] do
    if let some (.defnInfo dv) := envModA.find? cname then
      liftCoreM <| addAndCompile (.defnDecl dv)
  if let some minfo := Meta.getMatcherInfoCore? envModA earlierMatcher then
    liftCoreM <| Meta.Match.addMatcherInfo earlierMatcher minfo

setup_and_test_cross_module_matcher_ext

-- In the post-import environment (`matcherExt` empty), calling stock
-- `sf_recall` on the byte-for-byte identical definition of `laterIsNil`
-- elaborates a fresh `_uniq.N.laterIsNil.match_1`, which `renameBackName`
-- rewrites to the non-existent `CrossModuleSim.laterIsNil.match_1`!
capture_expected_error errEdgeCase5CrossModuleMatcherExt
  sf_recall
    def laterIsNil {α : Type} (xs : List α) : Bool :=
      match xs with
      | [] => true
      | _ :: _ => false

end CrossModuleSim

open CrossModuleSim

-- ============================================================================
-- 5. Mechanized Fix: `sf_recall_fixed` (`renameExact` + `unfoldMatchersIn`)
-- ============================================================================

/-- Renames only exact occurrences of the top-level constant `chk` (`n == chk`)
    on `defnInfo`, leaving auxiliary matcher constants `_uniq.N.<decl>.match_1`
    in the temporary environment with their true parameter signatures. -/
def renameExact (chk orig : Name) (e : Expr) : Expr :=
  e.replace fun
    | .const n us => if n == chk then some (.const orig us) else none
    | _ => none

/-- Unfolds matcher applications (`isMatcher`) via `unfoldDefinition?` when
    `Meta.isDefEq` initially returns `false` on neutral discriminants. -/
def unfoldMatchersIn (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun e => do
    if let .const c _ := e.getAppFn then
      if ← isMatcher c then
        if let some e' ← unfoldDefinition? e then
          return .visit e'
    return .continue)

elab "sf_recall_fixed " cmd:command : command => do
  let decl ← declaredName cmd
  let origActual ← liftCoreM <| withoutExporting <|
    realizeGlobalConstNoOverloadWithInfo decl.ident
  let ns := Name.mkStr1 (← liftCoreM (mkFreshId : CoreM Name)).toString
  let envBefore ← getEnv
  try
    withScope (fun sc => { sc with currNamespace := sc.currNamespace ++ ns }) do
      elabCommand cmd
      let env ← getEnv
      let chkName := (← getCurrNamespace) ++ decl.ident.getId
      let some chkInfo := env.find? chkName
        | throwError "could not find elaborated declaration '{chkName}'"
      let some origInfo := env.find? origActual
        | throwError "could not find original declaration '{origActual}'"
      let u1 := origInfo.levelParams.map Level.param
      let chkType :=
        (renameExact chkName origActual chkInfo.type).instantiateLevelParams
          chkInfo.levelParams u1
      let chkVal :=
        (renameExact chkName origActual chkInfo.value!).instantiateLevelParams
          chkInfo.levelParams u1
      let typeEq ← liftTermElabM <| withNewMCtxDepth <|
        isDefEq chkType origInfo.type
      unless typeEq do
        throwError "type mismatch for '{origActual}'"
      let valEq ← liftTermElabM <| withNewMCtxDepth do
        if ← isDefEq chkVal origInfo.value! then
          pure true
        else
          isDefEq (← unfoldMatchersIn chkVal) (← unfoldMatchersIn origInfo.value!)
      unless valEq do
        throwError "value mismatch for '{origActual}'"
  finally
    setEnv envBefore

-- Verify that `sf_recall_fixed` resolves Edge Cases 1, 2, 3, and 5:
sf_recall_fixed
  def pairSumProj : Nat × Nat → Nat
    | (a, b) => a + b

sf_recall_fixed
  def PrefixOutcome.isSafe : PrefixOutcome Val → Prop
    | .stuck => False
    | .running => True
    | .terminated _ => True
    | .failed _ => False

sf_recall_fixed
  def PrefixOutcome.isSafe (o : PrefixOutcome Val) : Prop :=
    PrefixOutcome.casesOn o True (fun _ => True) (fun _ => False) False

sf_recall_fixed
  def laterIsNil {α : Type} (xs : List α) : Bool :=
    match xs with
    | [] => true
    | _ :: _ => false

/-- Captures the boolean presence of `earlierIsNil.match_1` and
    `laterIsNil.match_1` in the environment at compile time. -/
elab "record_matcher_presence" : command => do
  let env ← getEnv
  let currNs ← getCurrNamespace
  let hasEarlier := env.contains (currNs ++ `CrossModuleSim.earlierIsNil.match_1)
  let hasLater := env.contains (currNs ++ `CrossModuleSim.laterIsNil.match_1)
  for (id, b) in [(`hasEarlierMatcher, hasEarlier), (`hasLaterMatcher, hasLater)] do
    let decl := Declaration.defnDecl {
      name := currNs ++ id
      levelParams := []
      type := mkConst ``Bool
      value := toExpr b
      hints := .abbrev
      safety := .safe
    }
    liftCoreM <| addAndCompile decl

record_matcher_presence

end ProbeRecallAndMatcherExt

open ProbeRecallAndMatcherExt
open ProbeRecallAndMatcherExt.CrossModuleSim

def hasSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

def assertSubstr (label text expected : String) : IO Unit := do
  unless hasSubstr text expected do
    throw <| IO.userError
      s!"Assertion failed for {label}: expected '{expected}' in '{text}'"

def main : IO UInt32 := do
  IO.println "=== ProbeRecallAndMatcherExt (Lean v4.34.1) ==="
  IO.println "1. Positive matches (`sf_recall`, `sf_recall statement`, universe specialization): PASS"
  IO.println "2. Unchecked metadata (`abbrev` vs `def`, field defaults/visibility, `theorem` as `def`): PASS"

  assertSubstr "errCtorOrder" errCtorOrder "constructor"
  assertSubstr "errStructField" errStructField "fields of"
  assertSubstr "errClassVsStruct" errClassVsStruct "type-class metadata"
  assertSubstr "errThmHyp" errThmHyp "restated statement"
  assertSubstr "errStrictUniv" errStrictUniv "universe parameters"
  IO.println "3. Negative drift checks (ctor order, field names, class vs structure, thm hyp, +strictUniverse): PASS"

  assertSubstr "EdgeCase1" errEdgeCase1DanglingMatcher "pairSumProj.match_1"
  assertSubstr "EdgeCase2" errEdgeCase2ReorderedArms "PrefixOutcome.isSafe"
  assertSubstr "EdgeCase3" errEdgeCase3CasesOnNeutral "PrefixOutcome.isSafe"
  assertSubstr "EdgeCase4" errEdgeCase4SparseCasesOn "PrefixOutcome.isSafe"
  assertSubstr "EdgeCase5" errEdgeCase5CrossModuleMatcherExt "laterIsNil.match_1"

  unless hasEarlierMatcher == true && hasLaterMatcher == false do
    throw <| IO.userError
      s!"Unexpected matcher presence: earlier={hasEarlierMatcher}, later={hasLaterMatcher}"

  IO.println s!"4. MatcherReuse in CrossModuleSim: earlierIsNil.match_1={hasEarlierMatcher}, laterIsNil.match_1={hasLaterMatcher}"
  IO.println s!"   Edge Case 1 (dangling .match_1): {errEdgeCase1DanglingMatcher}"
  IO.println s!"   Edge Case 5 (cross-module empty matcherExt): {errEdgeCase5CrossModuleMatcherExt}"
  IO.println "5. `sf_recall_fixed` (`renameExact` + `unfoldMatchersIn`) on Edge Cases 1, 2, 3, and 5: PASS"
  return 0
