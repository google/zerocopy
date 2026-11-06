import AnnealResearch.StatefulGenericLibraryH3H7Core

set_option maxRecDepth 131072
set_option maxHeartbeats 1600000

namespace AnnealResearch.StatefulGenericLibraryH3H7

open AnnealResearch.SubstantiveMirByteParser
open AnnealResearch.SemanticVerticalSlice
open AnnealResearch.CargoWorkspaceIntegration

/-! ## 7. `N3` (`#68` §4.2 & §6 N3): Actual `MirPhase::Built` Graph Ingestion & Independent Conditional-Drop Operational Validator -/

/-- Consume moved whole-local operands (`OperandSpec.move { localIdx := l, proj := .here }`) under
    `MirPhase::Built` semantics, deinitializing `l` (`eraseLocal locals l`) so a subsequent
    conditional `Drop(l)` at scope exit or unwind cleanup is a no-op. -/
def consumeMovedLocalBuilt (locals : List (Nat × RtVal)) : OperandSpec → List (Nat × RtVal)
  | .move { localIdx := l, proj := .here } => eraseLocal locals l
  | _ => locals

def consumeMovedOperandListBuilt (locals : List (Nat × RtVal)) : List OperandSpec → List (Nat × RtVal)
  | [] => locals
  | op :: ops => consumeMovedOperandListBuilt (consumeMovedLocalBuilt locals op) ops

/-- Statement step under `MirPhase::Built` move-deinitialization semantics:
    evaluating `assignUseNoRetag dst src` or `assignUseRetagYes dst src` reads `src`, deinitializes
    `src` if `src` is a whole-local `OperandSpec.move`, and writes `dst`. -/
def stepStmtBuilt
    (localTypes : List MirTypeTag)
    (st : WireStmt)
    (locals : List (Nat × RtVal))
    (heap : List HeapLogSlot) : Option (ExecStatus × List (Nat × RtVal) × List HeapLogSlot) :=
  match st with
  | .assignUseNoRetag dst src =>
      match evalOperand locals heap src with
      | .val v =>
          let localsAfterMove := consumeMovedLocalBuilt locals src
          match writePlace localsAfterMove heap dst v with
          | some (nl, nh) => some (.running, nl, nh)
          | none => some (.stuck, locals, heap)
      | .ub => some (.ub, locals, heap)
      | .stuck => some (.stuck, locals, heap)
  | .assignUseRetagYes dst src =>
      match evalOperand locals heap src with
      | .val v =>
          let localsAfterMove := consumeMovedLocalBuilt locals src
          match writePlace localsAfterMove heap dst v with
          | some (nl, nh) => some (.running, nl, nh)
          | none => some (.stuck, locals, heap)
      | .ub => some (.ub, locals, heap)
      | .stuck => some (.stuck, locals, heap)
  | other => stepStmt localTypes other locals heap

def execBlockStmtsBuilt
    (localTypes : List MirTypeTag)
    (stmts : List WireStmt)
    (locals : List (Nat × RtVal))
    (heap : List HeapLogSlot) : ExecStatus × List (Nat × RtVal) × List HeapLogSlot :=
  match stmts with
  | [] => (.running, locals, heap)
  | s :: ss =>
      match stepStmtBuilt localTypes s locals heap with
      | some (.running, nl, nh) => execBlockStmtsBuilt localTypes ss nl nh
      | some (otherStatus, nl, nh) => (otherStatus, nl, nh)
      | none => (.stuck, locals, heap)

/-- Terminator step under `MirPhase::Built` conditional-drop semantics:
    - At `WireTerm.drop pl glueSym tbb uw`:
      - If `pl.proj == .here` and `getLocal fr.locals pl.localIdx == none` (the local is uninitialized
        or was already moved/dropped), the conditional `Drop` is a no-op and jumps directly to `tbb`!
      - If `getLocal fr.locals pl.localIdx == some _`, it deinitializes `pl.localIdx` in `callerFr`
        and invokes `glueSym` on `&mut pl`.
    - At `Call`, any whole-local `OperandSpec.move` arguments are deinitialized in `callerFr`. -/
def stepTermBuilt
    (bodies : List WireBody)
    (fr : ExecFrame)
    (rest : List ExecFrame)
    (heap : List HeapLogSlot)
    (obsEvents : List Nat) : ExecState :=
  match fr.curTerm with
  | .drop pl glueSym tbb uw =>
      if Nat.beq glueSym 0 then
        match jumpToBlock fr tbb with
        | some nfr => { status := .running, stack := nfr :: rest, heap := heap, obsEvents := obsEvents }
        | none => { status := .stuck, stack := fr :: rest, heap := heap, obsEvents := obsEvents }
      else
        match getLocal fr.locals pl.localIdx with
        | none =>
            -- Conditional Drop of an uninitialized / already-moved local at `MirPhase::Built` is a no-op!
            match jumpToBlock fr tbb with
            | some nfr => { status := .running, stack := nfr :: rest, heap := heap, obsEvents := obsEvents }
            | none => { status := .stuck, stack := fr :: rest, heap := heap, obsEvents := obsEvents }
        | some _ =>
            match findBodyBySym bodies glueSym with
            | none => { status := .missingBody glueSym, stack := fr :: rest, heap := heap, obsEvents := obsEvents }
            | some gbody =>
                match getBlockAt gbody.blocks 0, makeRef fr.locals heap pl with
                | some blk0, .val refArg =>
                    let callerLocals := eraseLocal fr.locals pl.localIdx
                    let callerFr : ExecFrame :=
                      { fr with
                        locals := callerLocals
                        pending := some { retDst := { localIdx := 0, proj := .here }, targetBbOpt := some tbb, unwind := uw, isDropGlue := true } }
                    let glueFr : ExecFrame :=
                      { symId := glueSym
                      , localTypes := gbody.localTypes
                      , bodyBlocks := gbody.blocks
                      , bbIdx := 0
                      , remStmts := blk0.stmts
                      , curTerm := blk0.term
                      , locals := [(0, .agg0 1), (1, refArg)]
                      , pending := none }
                    { status := .running, stack := glueFr :: callerFr :: rest, heap := heap, obsEvents := obsEvents }
                | _, .ub => { status := .ub, stack := fr :: rest, heap := heap, obsEvents := obsEvents }
                | _, _ => { status := .stuck, stack := fr :: rest, heap := heap, obsEvents := obsEvents }
  | .call0 c dst t uw => dispatchCall bodies fr rest heap obsEvents c dst t uw []
  | .call1 c dst t uw a0 =>
      let st := dispatchCall bodies fr rest heap obsEvents c dst t uw [a0]
      if (findBodyBySym bodies c).isSome then
        match st.stack with
        | calleeFr :: callerFr :: r =>
            { st with stack := calleeFr :: { callerFr with locals := consumeMovedOperandListBuilt callerFr.locals [a0] } :: r }
        | _ => st
      else st
  | .call2 c dst t uw a0 a1 =>
      let st := dispatchCall bodies fr rest heap obsEvents c dst t uw [a0, a1]
      if (findBodyBySym bodies c).isSome then
        match st.stack with
        | calleeFr :: callerFr :: r =>
            { st with stack := calleeFr :: { callerFr with locals := consumeMovedOperandListBuilt callerFr.locals [a0, a1] } :: r }
        | _ => st
      else st
  | .call3 c dst t uw a0 a1 a2 =>
      let st := dispatchCall bodies fr rest heap obsEvents c dst t uw [a0, a1, a2]
      if (findBodyBySym bodies c).isSome then
        match st.stack with
        | calleeFr :: callerFr :: r =>
            { st with stack := calleeFr :: { callerFr with locals := consumeMovedOperandListBuilt callerFr.locals [a0, a1, a2] } :: r }
        | _ => st
      else st
  | .call4 c dst t uw a0 a1 a2 a3 =>
      let st := dispatchCall bodies fr rest heap obsEvents c dst t uw [a0, a1, a2, a3]
      if (findBodyBySym bodies c).isSome then
        match st.stack with
        | calleeFr :: callerFr :: r =>
            { st with stack := calleeFr :: { callerFr with locals := consumeMovedOperandListBuilt callerFr.locals [a0, a1, a2, a3] } :: r }
        | _ => st
      else st
  | otherTerm => stepTerm bodies { fr with curTerm := otherTerm } rest heap obsEvents

def stepStateBuilt (bodies : List WireBody) (st : ExecState) : ExecState :=
  match st.status with
  | .running =>
      match st.stack with
      | [] => { st with status := .stuck }
      | fr :: rest =>
          match execBlockStmtsBuilt fr.localTypes fr.remStmts fr.locals st.heap with
          | (.running, nl, nh) =>
              stepTermBuilt bodies { fr with remStmts := [], locals := nl } rest nh st.obsEvents
          | (otherStatus, nl, nh) =>
              { st with status := otherStatus, stack := { fr with remStmts := [], locals := nl } :: rest, heap := nh }
  | _ => st

def runStepsBuiltConditionalDrop (bodies : List WireBody) : Nat → ExecState → ExecState
  | 0, st => st
  | n + 1, st =>
      match st.status with
      | .running => runStepsBuiltConditionalDrop bodies n (stepStateBuilt bodies st)
      | _ => st

/-- Execute `transactional_step` (`symId = 65`) on a `MirPhase::Built` body list via the
    independent `MirPhase::Built` conditional-drop interpreter (`runStepsBuiltConditionalDrop`). -/
def evalBuiltTransactionalStepFromGraph (builtBodies : List WireBody) (triggerPanic : Bool) :
    CleanupExecOutcome :=
  let args : List RtVal :=
    [ .heapPtr 0
    , .heapPtr 1
    , .scalar (bif triggerPanic then 1 else 0) ]
  let finalSt := runStepsBuiltConditionalDrop builtBodies 45 (initEntryState builtBodies 65 args)
  let (l1, l2) := summarizeTwoHeapLogs finalSt.heap
  match finalSt.status with
  | .returned (.scalar rv) => .normalReturn rv l1 l2 finalSt.obsEvents
  | .unwoundTop => .unwoundWithCleanup l1 l2 finalSt.obsEvents
  | other => .failed other

/-- Execute `step_generic_slot` (`symId = 63`) on a `MirPhase::Built` body list via
    `runStepsBuiltConditionalDrop`. -/
def evalBuiltStepGenericSlotFromGraph (builtBodies : List WireBody) (s0 t0 : Nat) (ptrValid : Bool) (base : Nat) :
    ExecStatus × HeapLogSlot × List Nat :=
  let initSt := initEntryStateWithHeap builtBodies 63
    [.heapPtr 0, .extPtr ptrValid, .scalar base]
    [{ stepCount := s0, traceAcc := t0 }]
  let finalSt := runStepsBuiltConditionalDrop builtBodies 12 initSt
  let slot0 := match finalSt.heap with
    | h :: _ => h
    | [] => { stepCount := 0, traceAcc := 0 }
  (finalSt.status, slot0, finalSt.obsEvents)

/-- Execute `transactional_step` (`symId = 65`) on a `Runtime(PostCleanup)` body list via `runSteps`. -/
def evalPostCleanupTransactionalStep (bodies : List WireBody) (triggerPanic : Bool) :
    CleanupExecOutcome :=
  let args : List RtVal :=
    [ .heapPtr 0
    , .heapPtr 1
    , .scalar (bif triggerPanic then 1 else 0) ]
  let finalSt := runSteps bodies 45 (initEntryState bodies 65 args)
  let (l1, l2) := summarizeTwoHeapLogs finalSt.heap
  match finalSt.status with
  | .returned (.scalar rv) => .normalReturn rv l1 l2 finalSt.obsEvents
  | .unwoundTop => .unwoundWithCleanup l1 l2 finalSt.obsEvents
  | other => .failed other

/-- **Why `MirPhase::Built` and `Runtime(PostCleanup)` Have Distinct Operational Drop Semantics (`N3`)**:
    1. On the actual captured `MirPhase::Built` graph (`statefulGenericLibBuiltBodies`, 18 locals `_0.._17`,
       no drop flags `_19`/`_20`), running the late unconditional-drop interpreter (`evalPostCleanupTransactionalStep`)
       **double-drops `g2` on normal return (`obsEvents = [2, 2, 1]`) and double-drops `g1` on unwind
       (`obsEvents = [10, 1, 2, 1]`)** because `bb7` and `bb13` have unguarded `Drop(_6)` and `Drop(_4)` terminators!
    2. Running the `MirPhase::Built` conditional-drop interpreter (`evalBuiltTransactionalStepFromGraph`)
       on that same `Built` graph produces `.normalReturn 105 (1, 1) (1, 2) [2, 1]` and
       `.unwoundWithCleanup (2, 161) (1, 2) [10, 1, 2]`, matching `evalPostCleanupTransactionalStep`
       on the `ElaborateDrops`-lowered `Runtime(PostCleanup)` graph (`statefulGenericLibBodies`)! -/
theorem n3_built_graph_conditional_vs_unconditional_drop_semantics_and_elaboration_agreement :
    -- 1. Late unconditional-drop interpreter on Built graph double-drops moved guards:
    evalPostCleanupTransactionalStep statefulGenericLibBuiltBodies false =
      .normalReturn 105 (1, 1) (2, 34) [2, 2, 1] ∧
    evalPostCleanupTransactionalStep statefulGenericLibBuiltBodies true =
      .unwoundWithCleanup (3, 2577) (1, 2) [10, 1, 2, 1] ∧
    -- 2. Built conditional-drop interpreter on Built graph matches PostCleanup interpreter on PostCleanup graph:
    evalBuiltTransactionalStepFromGraph statefulGenericLibBuiltBodies false =
      .normalReturn 105 (1, 1) (1, 2) [2, 1] ∧
    evalBuiltTransactionalStepFromGraph statefulGenericLibBuiltBodies true =
      .unwoundWithCleanup (2, 161) (1, 2) [10, 1, 2] ∧
    evalBuiltTransactionalStepFromGraph statefulGenericLibBuiltBodies false =
      evalPostCleanupTransactionalStep statefulGenericLibBodies false ∧
    evalBuiltTransactionalStepFromGraph statefulGenericLibBuiltBodies true =
      evalPostCleanupTransactionalStep statefulGenericLibBodies true := by
  decide

/-- Verify Cargo invocation binding for a `MirPhase::Built` (`defaultPhase = 1`) `.amir` v3 package. -/
def verifyCargoBuiltInvocationBinding
    (expected : ExpectedCargoInvocationContext)
    (rec : CargoInvocationBindingRecord)
    (crateNameBytes amirBytes : List Nat) : Bool :=
  rec.crateName == expected.expectedCrateName &&
  rec.role == .targetCrate &&
  rec.features == expected.expectedFeatures &&
  rec.cfgFlags == expected.expectedCfgFlags &&
  (!expected.reqAlwaysEncodeMir || rec.alwaysEncodeMir) &&
  (!expected.reqPreserveUb || rec.preserveUb) &&
  Nat.beq rec.svhFingerprintLo expected.expectedSvhLo &&
  rec.externalDepSvhs == expected.expectedExternalDepSvhs &&
  Nat.beq rec.sourceContentSha256Hi64 expected.expectedSourceContentSha256Hi64 &&
  rec.generatedOutDirFileDigestTag == expected.expectedGeneratedOutDirFileDigestTag &&
  rec.completeness == .acceptedComplete &&
  isAdmittedPackageBytes amirBytes &&
  match amirBytes with
  | 65 :: 77 :: 73 :: 82 :: 3 :: 1 :: 11 :: fpHi :: fpLo :: _bodyCount :: payload =>
      let (calcHi, calcLo) := computeCargoPayloadFp16 crateNameBytes payload
      let (expHi, expLo) := rec.expectedFp16
      Nat.beq fpHi calcHi && Nat.beq fpLo calcLo &&
      Nat.beq fpHi expHi && Nat.beq fpLo expLo
  | _ => false

/-- Stage 1 of the two-sided `N3` lowering check: compilation-context & layout-table identity binding
    for both the early (`MirPhase::Built`) and late (`Runtime(PostCleanup)`) packages. -/
def checkTwoPhaseCompilationIdentity
    (expectedCtx : ExpectedCargoInvocationContext)
    (builtBindingRec postCleanupBindingRec : CargoInvocationBindingRecord)
    (crateNameBytes builtPkgBytes postCleanupPkgBytes : List Nat)
    (layoutTbl : BoundCompilerLayoutTable) : Bool :=
  verifyCargoBuiltInvocationBinding expectedCtx builtBindingRec crateNameBytes builtPkgBytes &&
  verifyCargoInvocationBinding expectedCtx postCleanupBindingRec crateNameBytes postCleanupPkgBytes &&
  checkLayoutTableBinding expectedCtx crateNameBytes layoutTbl

def checkBuiltPackageStructure (builtPkg : WirePackage) : Bool :=
  builtPkg.defaultPhase == .built &&
  builtPkg.preserveUb &&
  match findBodyBySym builtPkg.bodies 63, findBodyBySym builtPkg.bodies 65 with
  | some bStepBuilt, some bTransBuilt =>
      bStepBuilt.mirPhase == .built &&
      bTransBuilt.mirPhase == .built &&
      bTransBuilt.localCount == 18 &&
      bodyHasPlaceMention bStepBuilt.blocks
  | _, _ => false

def checkPostCleanupPackageStructure (postPkg : WirePackage) : Bool :=
  postPkg.defaultPhase == .runtimePostCleanup &&
  postPkg.preserveUb &&
  match findBodyBySym postPkg.bodies 63, findBodyBySym postPkg.bodies 65 with
  | some bStepPost, some bTransPost =>
      bStepPost.mirPhase == .runtimePostCleanup &&
      bTransPost.mirPhase == .runtimePostCleanup &&
      bTransPost.localCount == 21 &&
      bodyHasPlaceMention bStepPost.blocks &&
      (getLocalTypeAt bTransPost.localTypes 19 == .bool) &&
      (getLocalTypeAt bTransPost.localTypes 20 == .bool)
  | _, _ => false

def checkBuiltToPostCleanupStructureOnPkgs (builtPkg postPkg : WirePackage) : Bool :=
  checkPostCleanupPackageStructure postPkg && checkBuiltPackageStructure builtPkg

/-- Stage 2 of the two-sided `N3` lowering check: structural phase & drop-flag synthesis checks
    between the decoded `MirPhase::Built` package (`18` locals, `.built`) and `Runtime(PostCleanup)`
    package (`21` locals with synthesized boolean drop flags `_19` and `_20`, `.runtimePostCleanup`). -/
def checkBuiltToPostCleanupStructure (builtPkgBytes postCleanupPkgBytes : List Nat) : Bool :=
  match parseRawPackageBytes postCleanupPkgBytes with
  | .ok (postPkg, []) =>
      bif checkPostCleanupPackageStructure postPkg then
        match parseRawPackageBytes builtPkgBytes with
        | .ok (builtPkg, []) => checkBuiltPackageStructure builtPkg
        | _ => false
      else false
  | _ => false

def checkBuiltToPostCleanupBehavioralEquivOnBodies
    (expectedCtx : ExpectedCargoInvocationContext)
    (crateNameBytes : List Nat)
    (layoutTbl : BoundCompilerLayoutTable)
    (builtRawBodies postRawBodies : List WireBody) : Bool :=
  let layoutBodies := deriveLayoutCalleeBodies expectedCtx crateNameBytes layoutTbl .u32
  let builtBodies := builtRawBodies ++ layoutBodies
  let postBodies := postRawBodies ++ layoutBodies
  ((evalStepGenericSlot postBodies 0 0 false 16).1 == .ub) &&
  ((evalBuiltStepGenericSlotFromGraph builtBodies 0 0 false 16).1 == .ub) &&
  (evalBuiltStepGenericSlotFromGraph builtBodies 0 0 true 16 ==
    evalStepGenericSlot postBodies 0 0 true 16) &&
  (evalBuiltTransactionalStepFromGraph builtBodies true ==
    evalPostCleanupTransactionalStep postBodies true) &&
  (evalBuiltTransactionalStepFromGraph builtBodies false ==
    evalPostCleanupTransactionalStep postBodies false)

/-- Stage 3 of the two-sided `N3` lowering check: behavioral equivalence between the decoded
    `MirPhase::Built` graph under `runStepsBuiltConditionalDrop` and the decoded
    `Runtime(PostCleanup)` graph under `runSteps` across normal return, unwind cleanup, and
    `ptrValid = false` UB preservation. -/
def checkBuiltToPostCleanupBehavioralEquiv
    (expectedCtx : ExpectedCargoInvocationContext)
    (crateNameBytes : List Nat)
    (layoutTbl : BoundCompilerLayoutTable)
    (builtPkgBytes postCleanupPkgBytes : List Nat) : Bool :=
  checkBuiltToPostCleanupBehavioralEquivOnBodies expectedCtx crateNameBytes layoutTbl
    (decodePackageBodies builtPkgBytes) (decodePackageBodies postCleanupPkgBytes)

/-- **Two-Sided `MirPhase::Built` to `Runtime(PostCleanup)` Lowering Validator (`N3`, `#68` §4.2 & §6 N3)**:
    Ingests BOTH the captured `MirPhase::Built` `.amir` v3 package and the captured
    `Runtime(PostCleanup)` `.amir` v3 package alongside the expected compilation context and bound
    layout table, checking compilation identity, phase/drop-flag structure, and two-sided operational
    equivalence between `runStepsBuiltConditionalDrop` (on `Built`) and `runSteps` (on `PostCleanup`). -/
def validateBuiltToPostCleanupTwoSided
    (expectedCtx : ExpectedCargoInvocationContext)
    (builtBindingRec postCleanupBindingRec : CargoInvocationBindingRecord)
    (crateNameBytes builtPkgBytes postCleanupPkgBytes : List Nat)
    (layoutTbl : BoundCompilerLayoutTable) : Bool :=
  checkTwoPhaseCompilationIdentity expectedCtx builtBindingRec postCleanupBindingRec
    crateNameBytes builtPkgBytes postCleanupPkgBytes layoutTbl &&
  match parseRawPackageBytes postCleanupPkgBytes with
  | .ok (postPkg, []) =>
      bif checkPostCleanupPackageStructure postPkg then
        match parseRawPackageBytes builtPkgBytes with
        | .ok (builtPkg, []) =>
            checkBuiltPackageStructure builtPkg &&
            checkBuiltToPostCleanupBehavioralEquivOnBodies expectedCtx crateNameBytes layoutTbl
              builtPkg.bodies postPkg.bodies
        | _ => false
      else false
  | _ => false

/-- Single-argument wrapper over `realStatefulGenericLibBuiltAmirBytes` checking structural +
    two-sided behavioral equivalence against a candidate `postCleanupPkgBytes`. -/
def validateBuiltToPostCleanupDropElaboration (postCleanupPkgBytes : List Nat) : Bool :=
  match parseRawPackageBytes postCleanupPkgBytes with
  | .ok (postPkg, []) =>
      bif checkPostCleanupPackageStructure postPkg then
        match parseRawPackageBytes realStatefulGenericLibBuiltAmirBytes with
        | .ok (builtPkg, []) =>
            checkBuiltPackageStructure builtPkg &&
            checkBuiltToPostCleanupBehavioralEquivOnBodies statefulGenericLibExpectedCtx
              statefulGenericLibCrateBytes statefulGenericLibLayoutTable
              builtPkg.bodies postPkg.bodies
        | _ => false
      else false
  | _ => false

theorem h4_h6_built_to_post_cleanup_lowering_validator_accepts_real_package :
    validateBuiltToPostCleanupTwoSided
      statefulGenericLibExpectedCtx
      statefulGenericLibBuiltBindingRec
      statefulGenericLibBindingRec
      statefulGenericLibCrateBytes
      realStatefulGenericLibBuiltAmirBytes
      realStatefulGenericLibAmirBytes
      statefulGenericLibLayoutTable = true ∧
    validateBuiltToPostCleanupDropElaboration realStatefulGenericLibAmirBytes = true := by
  decide

/-! ## 8. `H5` & `N6` (`#68` §4.3 & §6 N6): Three-Layer Views and Statement-Inspecting `reconstructVerifiedStructuredView` -/

/-- Bounded postcondition predicate (`wpStateSteps`) over `runSteps`. As noted in `#68` §4.3, this is
    a bounded execution postcondition check over the CFG, not a standalone symbolic WP calculus. -/
def wpStateStepsBool
    (bodies : List WireBody)
    (fuel : Nat)
    (st : ExecState)
    (NormalPost : RtVal → List HeapLogSlot → List Nat → Bool)
    (UnwindPost : List HeapLogSlot → List Nat → Bool) : Bool :=
  let finalSt := runSteps bodies fuel st
  match finalSt.status with
  | .returned v => NormalPost v finalSt.heap finalSt.obsEvents
  | .unwoundTop => UnwindPost finalSt.heap finalSt.obsEvents
  | _ => false

def wpStateSteps
    (bodies : List WireBody)
    (fuel : Nat)
    (st : ExecState)
    (NormalPost : RtVal → List HeapLogSlot → List Nat → Bool)
    (UnwindPost : List HeapLogSlot → List Nat → Bool) : Prop :=
  wpStateStepsBool bodies fuel st NormalPost UnwindPost = true

theorem wpStateSteps_sound_on_transactional_step
    (triggerPanic : Bool) :
    wpStateSteps statefulGenericLibBodies 45
      (initEntryState statefulGenericLibBodies 65
        [.heapPtr 0, .heapPtr 1, .scalar (bif triggerPanic then 1 else 0)])
      (fun v heap evs =>
        !triggerPanic &&
        (v == .scalar 105) &&
        (summarizeTwoHeapLogs heap == ((1, 1), (1, 2))) &&
        (evs == [2, 1]))
      (fun heap evs =>
        triggerPanic &&
        (summarizeTwoHeapLogs heap == ((2, 161), (1, 2))) &&
        (evs == [10, 1, 2])) := by
  unfold wpStateSteps
  cases triggerPanic <;> decide

inductive StructuredStmtView where
  | checkPtrAndStepSlot (ptrLocal baseLocal : Nat) (eventTag : Nat)
  | callStepSlotAndAddConst (baseLocal : Nat) (addConst : Nat)
  deriving DecidableEq, Repr

/-- **Historical Naive Recognizer (`reconstructStructuredView`, `#68` §4.3)**:
    Retained ONLY so `StatefulGenericLibraryH3H7Controls.lean` can state and prove the counterexample
    `control_n6_naive_structured_recognizer_unsound_on_event_mutation` showing that checking only
    `symId`, `blocks.length`, and `bodyHasPlaceMention` is unsound when statements/operands are mutated
    (e.g. `altStatefulLibBodies` mutating event `4 -> 9`). Do NOT use `reconstructStructuredView`
    for soundness claims; use `reconstructVerifiedStructuredView` below. -/
def reconstructStructuredView (b : WireBody) : Option StructuredStmtView :=
  if b.blocks.any (fun blk => blk.isCleanup) then
    none
  else if b.symId == 63 && b.blocks.length == 4 && bodyHasPlaceMention b.blocks then
    some (.checkPtrAndStepSlot 2 3 4)
  else if b.symId == 66 && b.blocks.length == 3 then
    some (.callStepSlotAndAddConst 3 8)
  else
    none

/-- **Statement- & Terminator-Inspecting Structured Recognizer (`reconstructVerifiedStructuredView`, `N6`, `#68` §4.3 & §6 N6)**:
    Inspects the exact statements, operands, destinations, and call targets of `b.blocks` and
    extracts the actual constant operand `evTag` (in `symId = 63`) or `addK` (in `symId = 66`)
    from the decoded AST instead of hardcoding `4` or `8`. -/
def reconstructVerifiedStructuredView (b : WireBody) : Option StructuredStmtView :=
  if b.blocks.any (fun blk => blk.isCleanup) then
    none
  else if b.symId == 63 && b.blocks.length == 4 then
    match getBlockAt b.blocks 0, getBlockAt b.blocks 1, getBlockAt b.blocks 2, getBlockAt b.blocks 3 with
    | some bb0, some bb1, some bb2, some bb3 =>
        if bb0.stmts == [ .storageLive 4
                        , .assignUseRetagYes { localIdx := 4, proj := .here } .constUnit
                        , .storageDead 4
                        , .placeMention { localIdx := 2, proj := .deref }
                        , .storageLive 5 ] &&
           bb1.stmts == [ .storageLive 6
                        , .storageLive 7
                        , .assignRefOrPtr { localIdx := 7, proj := .here } .mutRef { localIdx := 1, proj := .deref } ] &&
           bb2.stmts == [ .storageDead 7
                        , .storageDead 6
                        , .storageLive 8
                        , .assignUseRetagYes { localIdx := 8, proj := .here } (.copy { localIdx := 3, proj := .here })
                        , .storageLive 9
                        , .assignUseRetagYes { localIdx := 9, proj := .here } (.copy { localIdx := 5, proj := .here }) ] &&
           bb3.stmts == [ .storageDead 9, .storageDead 8, .storageDead 5 ] then
          match bb0.term, bb1.term, bb2.term, bb3.term with
          | .call0 38 { localIdx := 5, proj := .here } (some 1) .continueUnwind,
            .call2 1 { localIdx := 6, proj := .here } (some 2) .continueUnwind
              (.move { localIdx := 7, proj := .here }) (.constU32 evTag),
            .call2 40 { localIdx := 0, proj := .here } (some 3) .continueUnwind
              (.move { localIdx := 8, proj := .here }) (.move { localIdx := 9, proj := .here }),
            .ret =>
              some (.checkPtrAndStepSlot 2 3 evTag)
          | _, _, _, _ => none
        else none
    | _, _, _, _ => none
  else if b.symId == 66 && b.blocks.length == 3 then
    match getBlockAt b.blocks 0, getBlockAt b.blocks 1, getBlockAt b.blocks 2 with
    | some bb0, some bb1, some bb2 =>
        if bb0.stmts == [ .storageLive 4
                        , .storageLive 5
                        , .assignRefOrPtr { localIdx := 5, proj := .here } .mutRef { localIdx := 1, proj := .deref }
                        , .storageLive 6
                        , .assignUseRetagYes { localIdx := 6, proj := .here } (.copy { localIdx := 2, proj := .here })
                        , .storageLive 7
                        , .assignUseRetagYes { localIdx := 7, proj := .here } (.copy { localIdx := 3, proj := .here }) ] &&
           bb1.stmts == [ .storageDead 7
                        , .storageDead 6
                        , .storageDead 5
                        , .storageLive 8
                        , .assignUseRetagYes { localIdx := 8, proj := .here } (.copy { localIdx := 4, proj := .here }) ] &&
           bb2.stmts == [ .storageDead 8, .storageDead 4 ] then
          match bb0.term, bb1.term, bb2.term with
          | .call3 63 { localIdx := 4, proj := .here } (some 1) .continueUnwind
              (.move { localIdx := 5, proj := .here })
              (.move { localIdx := 6, proj := .here })
              (.move { localIdx := 7, proj := .here }),
            .call2 40 { localIdx := 0, proj := .here } (some 2) .continueUnwind
              (.move { localIdx := 8, proj := .here }) (.constUsize addK),
            .ret =>
              some (.callStepSlotAndAddConst 3 addK)
          | _, _, _ => none
        else none
    | _, _, _ => none
  else
    none

/-- Structured evaluator for `StructuredStmtView`. -/
def evalStructuredView
    (view : StructuredStmtView)
    (s0 t0 : Nat)
    (ptrValid : Bool)
    (base : Nat) : ExecStatus × HeapLogSlot × List Nat :=
  match view with
  | .checkPtrAndStepSlot _ _ evTag =>
      if !ptrValid then
        (.ub, { stepCount := s0, traceAcc := t0 }, [])
      else
        let s1 := (s0 + 1) % u32Mod
        let t1 := ((t0 * 16) % u32Mod + evTag) % u32Mod
        (.returned (.scalar ((base + 4) % usizeMod)), { stepCount := s1, traceAcc := t1 }, [evTag])
  | .callStepSlotAndAddConst _ addK =>
      if !ptrValid then
        (.ub, { stepCount := s0, traceAcc := t0 }, [])
      else
        let s1 := (s0 + 1) % u32Mod
        let t1 := ((t0 * 16) % u32Mod + 4) % u32Mod
        (.returned (.scalar ((((base + 4) % usizeMod) + addK) % usizeMod)), { stepCount := s1, traceAcc := t1 }, [4])

/-- **`H5` & `N6` Operational Correspondence Theorem**:
    1. `reconstructVerifiedStructuredView` succeeds on `step_generic_slot` (`symId = 63`, extracting
       `evTag = 4`) and `client_contract_entry` (`symId = 66`, extracting `addK = 8`), and returns
       `none` on `transactional_step` (`symId = 65`).
    2. For **every** `ptrValid : Bool` and **every** `base : Nat`, `evalStructuredView` on the
       verified view `.checkPtrAndStepSlot 2 3 4` equals the actual stack-machine execution
       `evalStepGenericSlot statefulGenericLibBodies 0 0 ptrValid base` (`runSteps`)! -/
theorem h5_three_layer_proof_comparison_and_structured_view_correspondence :
    (match findBodyBySym statefulGenericLibBodies 63 with
     | some bStep => reconstructVerifiedStructuredView bStep == some (.checkPtrAndStepSlot 2 3 4)
     | none => false) = true ∧
    (match findBodyBySym statefulGenericLibBodies 65 with
     | some bTrans => reconstructVerifiedStructuredView bTrans == none
     | none => false) = true ∧
    (match findBodyBySym clientContractUserBodies 66 with
     | some bClient => reconstructVerifiedStructuredView bClient == some (.callStepSlotAndAddConst 3 8)
     | none => false) = true ∧
    (∀ ptrValid : Bool, ∀ base : Nat,
      evalStepGenericSlot statefulGenericLibBodies 0 0 ptrValid base =
        evalStructuredView (.checkPtrAndStepSlot 2 3 4) 0 0 ptrValid base) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro ptrValid base
  unfold evalStepGenericSlot
  cases ptrValid
  · rw [evalStepGenericSlot_false_universal]
    rfl
  · rw [evalStepGenericSlot_true_universal]
    rfl

#print axioms h3_three_crate_workspace_bindings_and_admission_verified
#print axioms step_generic_slot_symbolic_summary_matches_runSteps_universal
#print axioms step_generic_slot_stack_machine_agrees_with_symbolic_decoded_eval
#print axioms stateful_generic_lib_satisfies_operational_contract
#print axioms stateful_generic_lib_satisfies_published_contract
#print axioms client_contract_user_verified_modularly_from_operational_contract
#print axioms client_contract_oracle_matches_linked_runSteps_universal
#print axioms client_contract_linked_runSteps_universal
#print axioms client_contract_user_verified_modularly_from_published_contract
#print axioms client_direct_mir_inspector_proves_omitted_impl_facts_without_forking
#print axioms charon_h3_packages_admitted_and_closed
#print axioms charon_h3_stateful_generic_lib_satisfies_operational_contract
#print axioms charon_h3_client_contract_user_verified_modularly_and_linked
#print axioms charon_h3_inspector_matches_direct_mir_operational_outcomes
#print axioms n3_built_graph_conditional_vs_unconditional_drop_semantics_and_elaboration_agreement
#print axioms h4_h6_built_to_post_cleanup_lowering_validator_accepts_real_package
#print axioms wpStateSteps_sound_on_transactional_step
#print axioms h5_three_layer_proof_comparison_and_structured_view_correspondence

end AnnealResearch.StatefulGenericLibraryH3H7