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
# Self-Contained Probe: `sf_experiment`, `ngen`, Tutor Drift, and Kernel Replay

This standalone Lean `v4.34.1` probe embeds `SFLCompat.Experiment`
(`sf_experiment`, `sf_expect_failure_in`, `sf_expect_failure_in?`, and
`rawCommandBlock`) alongside `SFLCompat.Recall` (`sf_recall`) from
`plclub/sf-in-lean` (`13e9425b4647402a09316c1d39fa555e9bc3c257`) and verifies:

1. In-file state rollback (`withRestoringState`) and indentation-sensitive raw
   command parsing (`rawCommandBlock`), including parse-error capture.
2. Why `commandWithoutAsync` (`Elab.async.set false`) is mandatory for
   synchronous theorem proof error detection (`Command.State.snapshotTasks`).
3. The `NameGenerator` (`ngen`) reset bug in `withRestoringState`
   (`SFLCompat/Experiment.lean:29-38`), which assigns identical `FVarId`s
   (`_uniq.N`) to local binders inside `sf_experiment` and the subsequent
   declaration in `InfoTree`s (colliding in `SubVerso`'s `VarTypeKey.fvar` hover
   table), and the `ngen`/`nextMacroScope`-preserving fix.
4. Live semantic drift detection across the unmanaged Lean fenced blocks in
   Anneal Tutor (`6b7c210c6c70f2f1710424dd07b4829742ff9154`).
5. Zero constant leakage in `Environment.constants.map₂`, clean replay of all
   user declarations through `Kernel.Environment.replay` (`Init + Std` only),
   and `TrustedBoundary.inspectSource` closed-parser behavior.
-/

namespace ProbeExperimentAndTutorAudit

open Lean Meta Elab Command Parser

-- ============================================================================
-- 1. Core `SFLCompat.Experiment` Implementation (`Experiment.lean:15-185`)
-- ============================================================================

/-- Disables `Elab.async` on the current command scope so that theorem proof
    bodies elaborate synchronously rather than in background `snapshotTasks`
    (`SFLCompat/Experiment.lean:15-27`). -/
def commandWithoutAsync (act : CommandElabM Unit) : CommandElabM Unit := do
  match (← get).scopes with
  | [] => act
  | h :: t =>
    let mut orig : Option Bool := none
    try
      orig := h.opts.get? `Elab.async
      modify fun s =>
        { s with scopes := { h with opts := h.opts.setBool `Elab.async false } :: t }
      act
    finally
      if let h :: t := (← get).scopes then
        let opts :=
          orig.map (h.opts.setBool `Elab.async) |>.getD (h.opts.erase `Elab.async)
        modify fun s => { s with scopes := { h with opts := opts } :: t }

/-- Executes `m` and restores `savedState`, preserving `infoState` and
    (optionally) `messages` (`SFLCompat/Experiment.lean:29-38`). Note that stock
    `withRestoringState` resets `ngen` and `nextMacroScope` to `savedState`. -/
def withRestoringState (keepMsgs : Bool) (m : CommandElabM Unit) :
    CommandElabM Unit := do
  let savedState ← get
  try
    m
  finally
    let state ← get
    set { savedState with
      infoState := state.infoState
      messages := if keepMsgs then state.messages else savedState.messages }

namespace IndentedCommands

def rawLineEndFn : ParserFn :=
  eoiFn <|> satisfyFn (· == '\n') "line break"

def rawLineFn : ParserFn :=
  takeUntilFn (· == '\n') >> rawLineEndFn

def rawIndentedLineFn : ParserFn := atomicFn <|
  takeWhileFn (· == ' ') >>
  (satisfyFn (· == '\n') "line break" <|>
    (checkColGeFn "indented command sequence" >> rawLineFn))

def rawCommandBlockFn : ParserFn :=
  rawFn (rawLineFn >> manyFn rawIndentedLineFn) (trailingWs := true)

def rawCommandBlock : Parser := { fn := rawCommandBlockFn }

@[combinator_parenthesizer rawCommandBlock]
def rawCommandBlock.parenthesizer := PrettyPrinter.Parenthesizer.visitToken

@[combinator_formatter rawCommandBlock]
def rawCommandBlock.formatter :=
  PrettyPrinter.Formatter.visitAtom Name.anonymous

partial def runRawCmdsAux
    (ictx : InputContext) (pstate : ModuleParserState) : CommandElabM Unit := do
  let state ← get
  let scope := state.scopes.head!
  let pctx : ParserModuleContext := {
    env := state.env
    options := scope.opts
    currNamespace := scope.currNamespace
    openDecls := scope.openDecls
  }
  let (cmd, pstate, messages) := parseCommand ictx pctx pstate state.messages
  modify fun state => { state with messages }
  unless cmd.isOfKind ``Command.eoi do
    elabCommand cmd
    runLinters cmd
    unless isTerminalCommand cmd do
      runRawCmdsAux ictx pstate

def runRawCmds (body : Syntax) : CommandElabM Unit := do
  let some source :=
      body.getSubstring? (withLeading := false) (withTrailing := false)
    | throwErrorAt body "command sequence has no source range"
  let fileName ← getFileName
  let fileMap ← getFileMap
  let stopPos := source.trimRight.stopPos
  if h : stopPos ≤ fileMap.source.rawEndPos then
    let ictx := InputContext.mk fileMap.source fileName
      (fileMap := fileMap) (endPos := stopPos) (endPos_valid := h)
    runRawCmdsAux ictx
      { pos := source.startPos, recovering := false, hasLeading := false }
  else
    throwErrorAt body "invalid command-sequence source range"

end IndentedCommands

open IndentedCommands

def experimentTk := leading_parser "sf_experiment"
def expectFailureTk := leading_parser "sf_expect_failure_in"
def expectFailureInfoTk := leading_parser "sf_expect_failure_in?"

@[command_parser] def experimentCmd := leading_parser
  experimentTk >> checkLinebreakBefore "indented command sequence" >>
    checkColGt "indented command sequence" >> withPosition rawCommandBlock

@[command_parser] def expectFailureCmd := leading_parser
  expectFailureTk >> checkLinebreakBefore "indented command sequence" >>
    checkColGt "indented command sequence" >> withPosition rawCommandBlock

@[command_parser] def expectFailureInfoCmd := leading_parser
  expectFailureInfoTk >> checkLinebreakBefore "indented command sequence" >>
    checkColGt "indented command sequence" >> withPosition rawCommandBlock

@[command_elab experimentCmd]
def elabExperimentCmd : CommandElab := fun stx => do
  let body := stx.getArgs.back!
  commandWithoutAsync <| withRestoringState true do
    runRawCmds body

@[command_elab expectFailureCmd, command_elab expectFailureInfoCmd]
def elabExpectFailureCmd : CommandElab := fun stx => do
  let keepMsgs := stx.isOfKind ``expectFailureInfoCmd
  unless keepMsgs || stx.isOfKind ``expectFailureCmd do
    throwUnsupportedSyntax
  let tk := stx[0]
  let body := stx.getArgs.back!
  commandWithoutAsync <| withRestoringState keepMsgs do
    withRef tk <| failIfSucceeds <| runRawCmds body

-- ============================================================================
-- 2. Core `sf_recall` Elaborator for Auditing Tutor Blocks
-- ============================================================================

partial def declIds (stx : Syntax) : Array Syntax :=
  let inner := stx.getArgs.flatMap declIds
  if stx.isOfKind ``Lean.Parser.Command.declId then #[stx] ++ inner else inner

def declaredName (cmd : Syntax) : CommandElabM (Syntax × Name) := do
  let defined := declIds cmd
  match h : defined.size with
  | 0 => throwErrorAt cmd "the restated command does not declare a name"
  | 1 =>
    let declId := defined[0]
    return (declId[0], declId[0].getId)
  | _ => throwErrorAt cmd "the restated command declares several names"

def renameExact (chk orig : Name) (e : Expr) : Expr :=
  e.replace fun
    | .const n us => if n == chk then some (.const orig us) else none
    | _ => none

def renamePrefix (chk orig : Name) (e : Expr) : Expr :=
  e.replace fun
    | .const n us =>
      if chk.isPrefixOf n then some (.const (n.replacePrefix chk orig) us)
      else none
    | _ => none

elab "sf_recall " cmd:command : command => do
  let (ident, written) ← declaredName cmd
  let origActual ← liftCoreM <| withoutExporting <|
    realizeGlobalConstNoOverloadWithInfo ident
  let ns := Name.mkStr1 (← liftCoreM (mkFreshId : CoreM Name)).toString
  let envBefore ← getEnv
  try
    withScope (fun sc => { sc with currNamespace := sc.currNamespace ++ ns }) do
      elabCommand cmd
      let env ← getEnv
      let chkName := (← getCurrNamespace) ++ written
      let some chkInfo := env.find? chkName
        | throwError "could not find elaborated declaration '{chkName}'"
      let some origInfo := env.find? origActual
        | throwError "could not find original declaration '{origActual}'"
      unless origInfo.levelParams.length == chkInfo.levelParams.length do
        throwError "universe parameters of '{origActual}' do not match"
      let u1 := origInfo.levelParams.map Level.param
      let chkType :=
        (renamePrefix chkName origActual chkInfo.type).instantiateLevelParams
          chkInfo.levelParams u1
      unless ← liftTermElabM <| withNewMCtxDepth <|
          isDefEq chkType origInfo.type do
        throwError "the statement of '{origActual}' does not match"
      match origInfo, chkInfo with
      | .defnInfo orig, .defnInfo restated =>
        let chkVal :=
          (renameExact chkName origActual restated.value).instantiateLevelParams
            restated.levelParams u1
        unless ← liftTermElabM <| withNewMCtxDepth <|
            isDefEq chkVal orig.value do
          throwError "the value of '{origActual}' does not match"
      | .inductInfo orig, .inductInfo restated =>
        unless orig.numParams == restated.numParams
            && orig.numIndices == restated.numIndices
            && orig.ctors.length == restated.ctors.length do
          throwError "inductive structure of '{origActual}' does not match"
        if let some origSi := getStructureInfo? env origActual then
          if let some chkSi := getStructureInfo? env chkName then
            unless origSi.fieldNames == chkSi.fieldNames do
              throwError "the fields of '{origActual}' do not match"
      | .thmInfo _, .thmInfo _ => pure ()
      | .thmInfo _, .defnInfo _ => pure ()
      | _, _ => throwError "declaration kind mismatch for '{origActual}'"
  finally
    setEnv envBefore

-- ============================================================================
-- 3. Checking `sf_experiment`, `rawCommandBlock`, `Elab.async`, and `ngen`
-- ============================================================================

-- 3a. Verify that declarations inside `sf_experiment` and
-- `sf_expect_failure_in` are rolled back from `Command.State.env`.
sf_experiment
  def leakedDef : Nat := 999
  inductive LeakedInd where
    | alpha
    | beta
  structure LeakedStruct where
    field : Nat
  theorem leakedThm : leakedDef = 999 := rfl
  axiom leakedAxiom : False

-- 3b. Verify that `rawCommandBlock` captures raw parse errors inside
-- `sf_expect_failure_in` without aborting the outer file parse.
sf_expect_failure_in
  def := := syntax error here !@#

-- 3c. Verify that `leakedDef` is not in scope after `sf_experiment`.
sf_expect_failure_in
  #check leakedDef

/-- Verifies that under `Elab.async = true`, a broken `theorem` proof spawns a
    background task in `Command.State.snapshotTasks` and leaves synchronous
    `messages.hasErrors == false` immediately after `elabCommand`, whereas
    `Elab.async = false` (`commandWithoutAsync`) elaborates the proof
    synchronously (`snapshotTasks.size == 0`, `messages.hasErrors == true`). -/
elab "verify_async_theorem_behavior" : command => do
  let saved1 ← get
  let mut asyncHasErr := false
  let mut asyncTasks := 0
  try
    modifyScope fun sc => { sc with opts := sc.opts.setBool `Elab.async true }
    modify fun s => { s with messages := {}, snapshotTasks := #[] }
    elabCommand (← `(theorem asyncBroken : 1 = 2 := by rfl))
    asyncHasErr := (← get).messages.hasErrors
    asyncTasks := (← get).snapshotTasks.size
  finally
    set saved1

  let saved2 ← get
  let mut syncHasErr := false
  let mut syncTasks := 0
  try
    modifyScope fun sc => { sc with opts := sc.opts.setBool `Elab.async false }
    modify fun s => { s with messages := {}, snapshotTasks := #[] }
    elabCommand (← `(theorem syncBroken : 1 = 2 := by rfl))
    syncHasErr := (← get).messages.hasErrors
    syncTasks := (← get).snapshotTasks.size
  finally
    set saved2

  if asyncHasErr || asyncTasks == 0 then
    throwError "expected Elab.async=true to defer theorem proof to snapshotTasks"
  unless syncHasErr && syncTasks == 0 do
    throwError "expected Elab.async=false to report theorem error synchronously"

  let currNs ← getCurrNamespace
  for (id, n) in [(`recordedAsyncTasks, asyncTasks), (`recordedSyncTasks, syncTasks)] do
    liftCoreM <| addAndCompile <| .defnDecl {
      name := currNs ++ id
      levelParams := []
      type := mkConst ``Nat
      value := toExpr n
      hints := .abbrev
      safety := .safe
    }

verify_async_theorem_behavior

/-- Collects all local variable `FVarId` names referenced in `TermInfo` nodes
    inside an `InfoTree`. -/
partial def collectTermFVarIds (t : InfoTree) : Array Name :=
  match t with
  | .context _ t' => collectTermFVarIds t'
  | .node info children =>
    let here := match info with
      | .ofTermInfo ti =>
        match ti.expr with
        | .fvar id => #[id.name]
        | _ => #[]
      | _ => #[]
    children.foldl (fun acc c => acc ++ collectTermFVarIds c) here
  | .hole _ => #[]

/-- Reproduces the `NameGenerator` (`ngen`) reset collision in stock
    `withRestoringState` (`SFLCompat/Experiment.lean:29-38`) and verifies that
    preserving `ngen` and `nextMacroScope` eliminates the `FVarId` overlap. -/
elab "verify_ngen_collision_and_fix" : command => do
  let savedOuter ← get
  let mut stockOverlap : Array Name := #[]
  let mut fixedOverlap : Array Name := #[]
  try
    -- 1. Stock `withRestoringState` (resets `ngen` while keeping `infoState`):
    modify fun st => { st with infoState.trees := {}, infoState.enabled := true }
    let savedExp ← get
    try
      elabCommand (← `(def expFn (a : String) : String := a))
    finally
      let st ← get
      set { savedExp with infoState := st.infoState, messages := st.messages }
    elabCommand (← `(def nextFn (b : Bool) : Bool := b))
    let trees := (← get).infoState.trees
    let fvars0 := collectTermFVarIds trees[0]!
    let fvars1 := collectTermFVarIds trees[1]!
    for id in fvars0 do
      if fvars1.contains id && !stockOverlap.contains id then
        stockOverlap := stockOverlap.push id
    if stockOverlap.isEmpty then
      throwError "expected FVarId collision when ngen is reset"

    -- 2. Fixed `withRestoringState` (preserves `ngen` and `nextMacroScope`):
    modify fun st => { st with infoState.trees := {}, infoState.enabled := true }
    let savedFixed ← get
    try
      elabCommand (← `(def expFnFixed (a : String) : String := a))
    finally
      let st ← get
      set { savedFixed with
        infoState := st.infoState
        messages := st.messages
        ngen := st.ngen
        nextMacroScope := st.nextMacroScope }
    elabCommand (← `(def nextFnFixed (b : Bool) : Bool := b))
    let treesFixed := (← get).infoState.trees
    let fixed0 := collectTermFVarIds treesFixed[0]!
    let fixed1 := collectTermFVarIds treesFixed[1]!
    for id in fixed0 do
      if fixed1.contains id && !fixedOverlap.contains id then
        fixedOverlap := fixedOverlap.push id
    unless fixedOverlap.isEmpty do
      throwError "unexpected FVarId collision when ngen is preserved"
  finally
    set savedOuter

  let currNs ← getCurrNamespace
  for (id, n) in [(`stockFVarCollisions, stockOverlap.size),
                  (`fixedFVarCollisions, fixedOverlap.size)] do
    liftCoreM <| addAndCompile <| .defnDecl {
      name := currNs ++ id
      levelParams := []
      type := mkConst ``Nat
      value := toExpr n
      hints := .abbrev
      safety := .safe
    }

verify_ngen_collision_and_fix

-- ============================================================================
-- 4. Audit of Unmanaged Lean Fenced Blocks in Anneal Tutor (`6b7c210c`)
-- ============================================================================

namespace TutorAudit

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

inductive Value : Type where
  | scalar (bits : Nat)
  | unit

structure CapturedMir : Type where
  defPath : String
  numLocals : Nat := 0

inductive MirEvent : Type where
  | obs (tag : Nat)
  | call (target : String)

abbrev Memory : Type := Nat

inductive MirOutcome : Type where
  | normal (ret : Value × Memory)
  | panic
  | abort

def mirCallTree (_body : CapturedMir) (_args : List Value) :
    Partial (BehaviorSet (List MirEvent × MirOutcome)) :=
  Partial.pure (fun _ => True)

def mirStatefulTree (_body : CapturedMir) (_args : List Value) (_mem : Memory) :
    Partial (BehaviorSet (List MirEvent × MirOutcome)) :=
  Partial.pure (fun _ => True)

def MirExecPartial (body : CapturedMir) (args : List Value) :
    Partial (BehaviorSet (List MirEvent × MirOutcome)) :=
  mirCallTree body args

def MirContractSpec
    (safetyPre pre : List Value → Prop)
    (post : List Value → Value → Prop)
    (args : List Value) :
    Partial (BehaviorSet (List MirEvent × MirOutcome)) where
  defined := safetyPre args
  val _ outPair :=
    pre args →
      ∀ retVal mem', outPair.2 = .normal (retVal, mem') → post args retVal

def MirContractHoldsWithSafety
    (body : CapturedMir)
    (safetyPre pre : List Value → Prop)
    (post : List Value → Value → Prop) : Prop :=
  MirExecPartial body ≤ MirContractSpec safetyPre pre post

def MirContractHolds
    (body : CapturedMir)
    (pre : List Value → Prop)
    (post : List Value → Value → Prop) : Prop :=
  MirContractHoldsWithSafety body pre pre post

def MirStatefulExecPartial
    (body : CapturedMir) (args : List Value) (mem : Memory) :
    Partial (BehaviorSet (List MirEvent × MirOutcome)) :=
  mirStatefulTree body args mem

def MirStatefulContractSpec
    (safetyPre pre : List Value → Memory → Prop)
    (post : List Value → Memory → Value → Memory → Prop)
    (args : List Value) (mem : Memory) :
    Partial (BehaviorSet (List MirEvent × MirOutcome)) where
  defined := safetyPre args mem
  val _ outPair :=
    pre args mem →
      ∀ retVal mem',
        outPair.2 = .normal (retVal, mem') → post args mem retVal mem'

-- 4a. Unmanaged blocks in `docs/tutor/` on `6b7c210c` that PASS `sf_recall`:
-- Block #1 (`docs/tutor/README.md:40-46`) and Block #3
-- (`docs/tutor/02-rust-specifications.md:589-612`, where
-- `Language.WellFormedOn` uses named structure fields
-- `{ defined := safetyPre q, val := ... }` instead of `⟨safetyPre q, ...⟩`):
sf_recall
  structure Partial (B : Type u) : Type u where
    defined : Prop
    val : defined → B

sf_recall
  def Language.WellFormedOn (L : Language) (safetyPre : L.Query → Prop) :
      L.Behavior :=
    fun q => {
      defined := safetyPre q
      val := fun _ _ => True
    }

sf_recall
  def MirContractHoldsWithSafety
      (body : CapturedMir)
      (safetyPre pre : List Value → Prop)
      (post : List Value → Value → Prop) : Prop :=
    MirExecPartial body ≤ MirContractSpec safetyPre pre post

-- 4b. Drifted unmanaged blocks in `docs/tutor/` on `6b7c210c` caught by
-- `sf_recall` (verified via `sf_expect_failure_in`):
section DriftedTutorBlocks
set_option linter.unusedVariables false

-- Block #2 (`docs/tutor/01-basic-usage-and-outputs.md:372-407`): quotes removed
-- `ExecPrefix MirObs Value`, `MirNoUB.holds`, `MirSem`, and `Preorder.refines`.
sf_expect_failure_in
  sf_recall
    def MirExecPartial
        (body : CapturedMir)
        (args : List Value) :
        Partial (BehaviorSet (ExecPrefix MirObs Value)) where
      defined := MirNoUB.holds (MirSem ⟨body, args⟩)
      val := fun _ => MirSem ⟨body, args⟩

-- Block #4 (`docs/tutor/02-rust-specifications.md:629-637`): quotes removed
-- `Preorder.refines` instead of `≤`.
sf_expect_failure_in
  sf_recall
    def Compiles (L_src L_tgt : Language)
        (π_c : L_src.Behavior → L_tgt.Behavior)
        (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
      Preorder.refines (L_tgt.sem t) (π_c (L_src.sem s))

-- Block #5 (`docs/tutor/02-rust-specifications.md:645-662`): quotes removed
-- `Preorder.refines` on `safe_contractSpec_preserves_wellFormed`.
sf_expect_failure_in
  sf_recall
    theorem safe_contractSpec_preserves_wellFormed
        {L : Language} (funcPre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
        Preorder.refines (L.ContractSpec (fun _ => True) funcPre post) L.WellFormed :=
      Language.contractSpec_safe_refines_wellFormed funcPre post

-- Block #9 (`docs/tutor/05-verifying-unsafe-rust.md:56-99`): quotes pre-ITree
-- `Partial (BehaviorSet (Value × Memory))` instead of
-- `Partial (BehaviorSet (List MirEvent × MirOutcome))`.
sf_expect_failure_in
  sf_recall
    def MirStatefulContractSpec
        (safetyPre : List Value → Memory → Prop)
        (pre : List Value → Memory → Prop)
        (post : List Value → Memory → Value → Memory → Prop)
        (args : List Value)
        (mem : Memory) :
        Partial (BehaviorSet (Value × Memory)) where
      defined := safetyPre args mem
      val := fun _ out => pre args mem → post args mem out.1 out.2

end DriftedTutorBlocks

end TutorAudit

-- ============================================================================
-- 5. Environment Non-Leakage, `Kernel.Environment.replay`, & Closed Parser
-- ============================================================================

/-- Closed command-kind allowlist from `TrustedBoundary.lean:36-42`. -/
def trustedBoundaryCommandKinds : List Name := [
  ``Parser.Command.declaration, ``Parser.Command.namespace,
  ``Parser.Command.section, ``Parser.Command.end, ``Parser.Command.universe,
  ``Parser.Command.variable, ``Parser.Command.open, ``Parser.Command.openScoped,
  ``Parser.Command.export, ``Parser.Command.mutual, ``Parser.Command.in,
  ``Parser.Command.attribute, ``Parser.Command.moduleDoc,
  ``Parser.Command.set_option, `Lean.Parser.Command.notation,
  `Lean.Parser.Command.mixfix
]

/-- Runs `TrustedBoundary.inspectSource`'s closed-parser check on an in-memory
    source snippet under a given `parserEnv`. -/
def checkClosedParserSnippet (parserEnv : Environment) (src : String) :
    IO (Except String Nat) := do
  let ctx := Parser.mkInputContext src "<snippet>"
  let (_, initial, log) ← Parser.parseHeader ctx
  if log.hasErrors || initial.recovering then
    return .error "header parser error"
  let mut state := initial
  let mut messages := log
  let mut cmdCount := 0
  for _ in [0:32] do
    let previous := state.pos
    let (stx, next, nextMessages) :=
      Parser.parseCommand ctx { env := parserEnv, options := {} } state messages
    state := next
    messages := nextMessages
    if messages.hasErrors || state.recovering then
      return .error "command parser error (custom syntax not in closed parserEnv)"
    if stx.isOfKind ``Parser.Command.eoi then
      return .ok cmdCount
    if state.pos <= previous then
      return .error "parser made no progress"
    unless trustedBoundaryCommandKinds.contains stx.getKind do
      return .error s!"unsupported command kind {stx.getKind}"
    cmdCount := cmdCount + 1
  return .ok cmdCount

/-- Safely bridges `enableInitializersExecution` so `importModules` with
    `loadExts := true` can construct the exact `Init + Std` closed parser
    environment used by `TrustedBoundary.inspectSource`. -/
unsafe def enableInitsUnsafe : IO Unit := do
  enableInitializersExecution

@[implemented_by enableInitsUnsafe]
opaque enableInits : IO Unit

/-- Records the count of leaked `_uniq` or `sf_experiment` constants in
    `env.constants.map₂`, replays all pure `TutorAudit.*` declarations through
    `minBaseEnv.toKernelEnv.replay` (`Init + Std` only), and verifies
    `TrustedBoundary.inspectSource` under a closed `Init + Std` parser
    environment. -/
elab "verify_env_cleanliness" : command => do
  let env ← getEnv
  let mut leakedCount : Nat := 0
  let mut tutorLocals : Std.HashMap Name ConstantInfo := {}
  for (cname, cinfo) in env.constants.map₂.toList do
    let s := cname.toString
    if (s.splitOn "_uniq").length > 1 then
      leakedCount := leakedCount + 1
    for banned in ["leakedDef", "LeakedInd", "LeakedStruct", "leakedThm", "leakedAxiom"] do
      if (s.splitOn banned).length > 1 then
        leakedCount := leakedCount + 1
    if (`ProbeExperimentAndTutorAudit.TutorAudit).isPrefixOf cname then
      if !cinfo.isUnsafe && !cinfo.isPartial && !cinfo.isAxiom then
        tutorLocals := tutorLocals.insert cname cinfo

  if leakedCount != 0 then
    throwError "detected {leakedCount} leaked constants in Environment!"

  let tutorAuditDeclCount : Nat := tutorLocals.size
  let minBaseEnv ← liftCoreM <| (do
    importModules #[{ module := `Init }, { module := `Std }] {}
      (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
    : IO Environment)
  let _ ← liftCoreM <| (minBaseEnv.toKernelEnv.replay tutorLocals : IO Kernel.Environment)

  let closedParserEnv ← liftCoreM <| (do
    enableInits
    importModules #[{ module := `Init }, { module := `Std }] {}
      (trustLevel := 0) (plugins := #[]) (loadExts := true) (level := .private)
    : IO Environment)
  let pureSnippet := "namespace Demo\ndef x : Nat := 1\nend Demo\n"
  let customSnippet := "sf_recall\n  def x : Nat := 1\n"
  let pureRes ← liftCoreM <| (checkClosedParserSnippet closedParserEnv pureSnippet : IO _)
  let customRes ← liftCoreM <| (checkClosedParserSnippet closedParserEnv customSnippet : IO _)
  unless pureRes.toOption == some 3 && customRes.isOk == false do
    throwError "unexpected closed parser check results: pure={repr pureRes}, custom={repr customRes}"

  let currNs ← getCurrNamespace
  for (id, n) in [(`recordedLeakedConsts, leakedCount),
                  (`recordedTutorAuditDecls, tutorAuditDeclCount),
                  (`recordedPureCmds, pureRes.toOption.getD 0)] do
    liftCoreM <| addAndCompile <| .defnDecl {
      name := currNs ++ id
      levelParams := []
      type := mkConst ``Nat
      value := toExpr n
      hints := .abbrev
      safety := .safe
    }

verify_env_cleanliness

end ProbeExperimentAndTutorAudit

open Lean
open ProbeExperimentAndTutorAudit

def main : IO UInt32 := do
  IO.println "=== ProbeExperimentAndTutorAudit (Lean v4.34.1) ==="

  unless recordedLeakedConsts == 0 && recordedTutorAuditDecls > 0 do
    throw <| IO.userError s!"Expected 0 leaked constants, got {recordedLeakedConsts}"
  IO.println s!"1. Environment rollback & Kernel.Environment.replay (Init+Std only): PASS (0 leaked constants, {recordedTutorAuditDecls} TutorAudit decls replayed)"

  unless recordedAsyncTasks > 0 && recordedSyncTasks == 0 do
    throw <| IO.userError
      s!"Unexpected snapshotTasks: async={recordedAsyncTasks}, sync={recordedSyncTasks}"
  IO.println s!"2. `commandWithoutAsync` verification: Elab.async=true spawned {recordedAsyncTasks} background tasks (sync hasErrors=false); Elab.async=false spawned {recordedSyncTasks} tasks (sync hasErrors=true)"

  unless stockFVarCollisions > 0 && fixedFVarCollisions == 0 do
    throw <| IO.userError
      s!"Unexpected FVarId collision counts: stock={stockFVarCollisions}, fixed={fixedFVarCollisions}"
  IO.println s!"3. `withRestoringState` `ngen` collision: stock had {stockFVarCollisions} shared FVarIds across commands; `ngen`-preserving fix had {fixedFVarCollisions} shared FVarIds"

  IO.println "4. Anneal Tutor (`6b7c210c`) unmanaged block audit: passed 3 up-to-date blocks, caught 4 representative drifted blocks"

  unless recordedPureCmds == 3 do
    throw <| IO.userError s!"Expected 3 parsed pure commands, got {recordedPureCmds}"
  IO.println s!"5. `TrustedBoundary.inspectSource` closed parserEnv (Init+Std): pure Lean=Except.ok {recordedPureCmds}, custom `sf_recall`=Except.error (rejected as expected)"

  return 0
