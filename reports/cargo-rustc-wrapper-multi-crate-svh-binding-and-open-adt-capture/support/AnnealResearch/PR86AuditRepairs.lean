import AnnealResearch.StatefulGenericLibraryH3H7Controls

set_option maxRecDepth 131072
set_option maxHeartbeats 1600000

namespace AnnealResearch.PR86AuditRepairs

open AnnealResearch.SubstantiveMirByteParser
open AnnealResearch.SemanticVerticalSlice
open AnnealResearch.CargoWorkspaceIntegration
open AnnealResearch.StatefulGenericLibraryH3H7
open AnnealResearch.StatefulGenericLibraryH3H7Controls

/-!
# `#89` Wave A Repairs (`R2`, `R7`, `R8` for Audit Findings `U3`, `U4`, `U5`, `U7`)

This module leaves all `PR #86` definitions in `StatefulGenericLibraryH3H7Core.lean`,
`StatefulGenericLibraryH3H7.lean`, and `StatefulGenericLibraryH3H7Controls.lean` unchanged so that
Companion B's standalone counterexamples (`U3`, `U4`, `U5`, `U7`) can be replayed verbatim against
the unmodified `PR #86` definitions in `PR86AuditCounterexamples.lean`.

On top of those unchanged definitions, this module mechanizes:
1. **`R7` (`U7`, `#89` §14 & `#88`) — Content- & Target-Bound Layout Table (`checkLayoutTableBindingWithEntries`)
   and Direct Slice-Tail `#[repr(C)]` Specimen (`PacketWithTail`)**:
   - Binds `tbl.entries` (`encodeLayoutEntriesPayload`, `computeLayoutEntriesFp16`) and the target
     triple (`x86_64LinuxTargetTripleBytes`) into `checkLayoutTableBindingWithEntries` and
     `deriveLayoutCalleeBodiesChecked`, so mutating `u32` alignment from `4` to `8`
     (`sameIdentityAlign8`) or emptying `entries` (`emptyLayout`) while keeping crate/SVH/SHA tags
     fixed is immediately rejected.
   - Mechanizes the `#[repr(C)]` / `#[repr(C, packed(k))]` layout interpretation recipe for a
     direct slice-tail DST (`PacketWithTail`: `header_tag: u16`, `payload_flags: u32`, `tail: [u16]`)
     alongside its 4 negative controls.
2. **`R2` (`U3` & `U4`, `#89` §9) — Fail-Closed Two-Sided Lowering Validator (`validateBuiltToPostCleanupFailClosed`)
   with Explicit `UbPrefixObservationPolicy` and Acceptance-Implies-Refinement Soundness**:
   - Enforces runtime body closure (`checkRuntimeClosedBodies` against the exact evaluator intrinsic
     set `isEvaluatorIntrinsicSym`), content-bound layout validation, and positive non-failing
     endpoint outcomes on both `MirPhase::Built` and `Runtime(PostCleanup)` packages.
   - Parameterizes UB comparison by `UbPrefixObservationPolicy` (`.strictPrefixTracePreserving` vs.
     `.coarseTerminalStatusOnly`), rejecting delayed `PlaceMention` (`delayedRawBodies`) under
     `.strictPrefixTracePreserving`.
   - Proves the acceptance-soundness theorem `checkBuiltToPostCleanupBehavioralEquivFailClosed_sound`.
3. **`R8` (`U5`, `#89` §15) — Environment-Bound Structured View (`reconstructVerifiedStructuredViewInEnv`)
   and Universal Acceptance-Implies-Correspondence Theorem**:
   - Inspects the callee environment (`findBodyBySym allBodies 38`, `findBodyBySym allBodies 1`)
     as well as the target body `b`, extracting `(alignConst, evTag)` and proving
     `reconstructVerifiedStructuredViewInEnv_general_step_slot_sound` universally over any
     `allBodies : List WireBody`, `b : WireBody`, `alignConst : Nat`, `evTag < u32Mod`,
     `ptrValid : Bool`, and `base : Nat`.
-/

/-! ## 1. `R7` (`U7`): Content- & Target-Bound Compiler Layout Table and Slice-Tail `#[repr(C)]` DST -/

def encodeLayoutEntryBytes (e : CompilerTypeLayoutEntry) : List Nat :=
  [ specEncodeTypeTag e.typeTag
  , e.sizeBytes % 256
  , (e.sizeBytes / 256) % 256
  , e.alignBytes % 256
  , (e.alignBytes / 256) % 256 ]

def encodeLayoutEntriesPayload : List CompilerTypeLayoutEntry → List Nat
  | [] => [0]
  | e :: es => encodeLayoutEntryBytes e ++ encodeLayoutEntriesPayload es

def computeLayoutEntriesFp16
    (crateNameBytes : List Nat)
    (entries : List CompilerTypeLayoutEntry) : Nat × Nat :=
  computeCargoPayloadFp16 crateNameBytes (encodeLayoutEntriesPayload entries)

def x86_64LinuxTargetTripleBytes : List Nat :=
  [120, 56, 54, 95, 54, 52]

def aarch64DarwinTargetTripleBytes : List Nat :=
  [97, 97, 114, 99, 104, 54, 52]

def statefulGenericLibEntriesFp16 : Nat × Nat :=
  computeLayoutEntriesFp16 statefulGenericLibCrateBytes statefulGenericLibLayoutTable.entries

/-- Repaired layout-table binding check (`U7` & `R7`, `#89` §14):
    Verifies crate identity, SVH, source SHA-256 prefix, target triple, non-empty `entries`, AND
    the 16-bit payload fingerprint `computeLayoutEntriesFp16` over `tbl.entries`.
    `ASSUMP-LAYOUT-01` remains explicitly disclosed: this check binds the supplied layout payload
    to the exact compilation and target context, while trusting the compiler-captured `(size, align)`
    facts for that target. -/
def checkLayoutTableBindingWithEntries
    (ctx : ExpectedCargoInvocationContext)
    (expectedCrateBytes : List Nat)
    (expectedTargetTripleBytes : List Nat)
    (expectedEntriesFp16 : Nat × Nat)
    (tbl : BoundCompilerLayoutTable)
    (targetTripleBytes : List Nat) : Bool :=
  checkLayoutTableBinding ctx expectedCrateBytes tbl &&
  listNatBeq targetTripleBytes expectedTargetTripleBytes &&
  !tbl.entries.isEmpty &&
  let (calcHi, calcLo) := computeLayoutEntriesFp16 expectedCrateBytes tbl.entries
  Nat.beq calcHi expectedEntriesFp16.1 && Nat.beq calcLo expectedEntriesFp16.2

def deriveLayoutCalleeBodiesChecked
    (ctx : ExpectedCargoInvocationContext)
    (expectedCrateBytes : List Nat)
    (expectedTargetTripleBytes : List Nat)
    (expectedEntriesFp16 : Nat × Nat)
    (tbl : BoundCompilerLayoutTable)
    (targetTripleBytes : List Nat)
    (typeTag : MirTypeTag) : List WireBody :=
  bif checkLayoutTableBindingWithEntries ctx expectedCrateBytes expectedTargetTripleBytes
        expectedEntriesFp16 tbl targetTripleBytes then
    deriveLayoutCalleeBodies ctx expectedCrateBytes tbl typeTag
  else
    []

/-- Effective field alignment under an optional `#[repr(C, packed(k))]` cap (`#88` & `#89` §14). -/
def effectiveFieldAlign (rawAlign : Nat) (packCapOpt : Option Nat) : Nat :=
  match packCapOpt with
  | none => rawAlign
  | some cap => bif Nat.ble cap rawAlign then cap else rawAlign

/-- Round `offset` up to the next multiple of `align` (`align > 0`). -/
def alignUpTo (offset align : Nat) : Nat :=
  let rem := offset % align
  bif Nat.beq rem 0 then offset else offset + (align - rem)

/-- Recursive `#[repr(C)]` field-accumulation step returning `(revOffsets, curOffset, maxAlign)`. -/
def accumReprCFields
    (packCapOpt : Option Nat) :
    List (Nat × Nat) → List Nat → Nat → Nat → Option (List Nat × Nat × Nat)
  | [], revOffsets, curOffset, maxAlign =>
      some (revOffsets.reverse, curOffset, maxAlign)
  | (fSize, fAlign) :: rest, revOffsets, curOffset, maxAlign =>
      let effAlign := effectiveFieldAlign fAlign packCapOpt
      bif Nat.beq effAlign 0 then
        none
      else
        let alignedOff := alignUpTo curOffset effAlign
        let nextMax := bif Nat.ble maxAlign effAlign then effAlign else maxAlign
        accumReprCFields packCapOpt rest (alignedOff :: revOffsets) (alignedOff + fSize) nextMax

/-- Selected-layout recipe for a direct slice-tail `#[repr(C)]` DST (`#89` §14 & `#88`):
    Given header fields `(size, align)`, slice-tail element `(tailElemSize, tailElemAlign)`,
    optional packing cap `packCapOpt`, and runtime slice metadata `sliceLen`, computes
    `some (fieldOffsets, tailOffset, rawExtentBeforeTrailingPad, totalAlignedByteSize, structAlign)`. -/
def computeReprCStructAndSliceTailLayout
    (headerFields : List (Nat × Nat))
    (tailElemSize tailElemAlign : Nat)
    (packCapOpt : Option Nat)
    (sliceLen : Nat) : Option (List Nat × Nat × Nat × Nat × Nat) :=
  match accumReprCFields packCapOpt headerFields [] 0 1 with
  | none => none
  | some (fieldOffsets, afterHeaderOffset, headerMaxAlign) =>
      let effTailAlign := effectiveFieldAlign tailElemAlign packCapOpt
      bif Nat.beq effTailAlign 0 then
        none
      else
        let structAlign := bif Nat.ble headerMaxAlign effTailAlign then effTailAlign else headerMaxAlign
        let tailOffset := alignUpTo afterHeaderOffset effTailAlign
        let rawExtent := tailOffset + sliceLen * tailElemSize
        let totalAlignedSize := alignUpTo rawExtent structAlign
        some (fieldOffsets, tailOffset, rawExtent, totalAlignedSize, structAlign)

/-- `PacketWithTail` (`#[repr(C)] struct PacketWithTail { header_tag: u16, payload_flags: u32, tail: [u16] }`):
    `headerFields = [(2, 2), (4, 4)]`, `tail = (2, 2)`. -/
def packetWithTailHeaderFields : List (Nat × Nat) :=
  [(2, 2), (4, 4)]

theorem r7_repr_c_slice_tail_packet_layout_and_controls :
    computeReprCStructAndSliceTailLayout packetWithTailHeaderFields 2 2 none 3 =
      some ([0, 4], 8, 14, 16, 4) ∧
    computeReprCStructAndSliceTailLayout packetWithTailHeaderFields 2 2 (some 2) 3 =
      some ([0, 2], 6, 12, 12, 2) ∧
    computeReprCStructAndSliceTailLayout packetWithTailHeaderFields 2 2 (some 1) 3 =
      some ([0, 2], 6, 12, 12, 1) ∧
    (computeReprCStructAndSliceTailLayout packetWithTailHeaderFields 2 2 (some 2) 3 ≠
      computeReprCStructAndSliceTailLayout packetWithTailHeaderFields 2 2 none 3) ∧
    (14 % 4 ≠ 0 ∧ 16 % 4 = 0) ∧
    computeReprCStructAndSliceTailLayout packetWithTailHeaderFields 2 0 none 3 = none := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ## 2. `R2` (`U3` & `U4`): Fail-Closed Two-Sided Lowering Validator & Explicit UB Prefix Policy -/

/-- Exact set of intrinsic callee symbols handled directly by `evalDeclaredIntrinsic` in
    `SemanticVerticalSliceCore.lean`. Crucially, `37` (`size_of`), `38` (`align_of`), and `99`
    are NOT built-in runtime intrinsics and MUST resolve to concrete `WireBody` entries in `bodies`! -/
def isEvaluatorIntrinsicSym (s : Nat) : Bool :=
  Nat.beq s 20 || Nat.beq s 21 || Nat.beq s 22 || Nat.beq s 23 ||
  Nat.beq s 25 || Nat.beq s 26 || Nat.beq s 27 ||
  Nat.beq s 40 || Nat.beq s 41 || Nat.beq s 42

def checkTermRuntimeClosed (allBodies : List WireBody) (t : WireTerm) : Bool :=
  match t with
  | .drop _ glueSym _ _ =>
      Nat.beq glueSym 0 || (findBodyBySym allBodies glueSym).isSome
  | .call0 c _ _ _
  | .call1 c _ _ _ _
  | .call2 c _ _ _ _ _
  | .call3 c _ _ _ _ _ _
  | .call4 c _ _ _ _ _ _ _ =>
      isEvaluatorIntrinsicSym c || (findBodyBySym allBodies c).isSome
  | _ => true

def checkBlocksRuntimeClosed (allBodies : List WireBody) : List WireBlock → Bool
  | [] => true
  | blk :: bs =>
      bif checkTermRuntimeClosed allBodies blk.term then
        checkBlocksRuntimeClosed allBodies bs
      else false

def checkBodyListRuntimeClosed (allBodies : List WireBody) : List WireBody → Bool
  | [] => true
  | b :: bs =>
      bif checkBlocksRuntimeClosed allBodies b.blocks then
        checkBodyListRuntimeClosed allBodies bs
      else false

/-- Every `Call` and `Drop` terminator in every body of `allBodies` resolves to either an evaluator
    intrinsic (`isEvaluatorIntrinsicSym`) or a present body in `allBodies`. -/
def checkRuntimeClosedBodies (allBodies : List WireBody) : Bool :=
  !allBodies.isEmpty && checkBodyListRuntimeClosed allBodies allBodies

/-- Explicit claim policy for bad-prefix (UB) observations (`#89` §9 "UB branch"). -/
inductive UbPrefixObservationPolicy where
  | strictPrefixTracePreserving
  | coarseTerminalStatusOnly
  deriving DecidableEq, Repr

def checkUbInvalidPtrEquivUnderPolicy
    (policy : UbPrefixObservationPolicy)
    (builtInvalidOut postInvalidOut : ExecStatus × HeapLogSlot × List Nat) : Bool :=
  match policy with
  | .strictPrefixTracePreserving =>
      (builtInvalidOut == (.ub, { stepCount := 0, traceAcc := 0 }, [])) &&
      (postInvalidOut == (.ub, { stepCount := 0, traceAcc := 0 }, []))
  | .coarseTerminalStatusOnly =>
      (builtInvalidOut.1 == .ub) && (postInvalidOut.1 == .ub)

def checkBuiltToPostCleanupBehavioralEquivFailClosed
    (policy : UbPrefixObservationPolicy)
    (expectedCtx : ExpectedCargoInvocationContext)
    (crateNameBytes : List Nat)
    (expectedTargetTripleBytes : List Nat)
    (expectedEntriesFp16 : Nat × Nat)
    (layoutTbl : BoundCompilerLayoutTable)
    (targetTripleBytes : List Nat)
    (builtRawBodies postRawBodies : List WireBody) : Bool :=
  let layoutBodies :=
    deriveLayoutCalleeBodiesChecked expectedCtx crateNameBytes expectedTargetTripleBytes
      expectedEntriesFp16 layoutTbl targetTripleBytes .u32
  let builtBodies := builtRawBodies ++ layoutBodies
  let postBodies := postRawBodies ++ layoutBodies
  (layoutBodies.length == 2) &&
  checkRuntimeClosedBodies builtBodies &&
  checkRuntimeClosedBodies postBodies &&
  checkUbInvalidPtrEquivUnderPolicy policy
    (evalBuiltStepGenericSlotFromGraph builtBodies 0 0 false 16)
    (evalStepGenericSlot postBodies 0 0 false 16) &&
  (evalBuiltStepGenericSlotFromGraph builtBodies 0 0 true 16 ==
    (.returned (.scalar 20), { stepCount := 1, traceAcc := 4 }, [4])) &&
  (evalStepGenericSlot postBodies 0 0 true 16 ==
    (.returned (.scalar 20), { stepCount := 1, traceAcc := 4 }, [4])) &&
  (evalBuiltTransactionalStepFromGraph builtBodies false ==
    .normalReturn 105 (1, 1) (1, 2) [2, 1]) &&
  (evalPostCleanupTransactionalStep postBodies false ==
    .normalReturn 105 (1, 1) (1, 2) [2, 1]) &&
  (evalBuiltTransactionalStepFromGraph builtBodies true ==
    .unwoundWithCleanup (2, 161) (1, 2) [10, 1, 2]) &&
  (evalPostCleanupTransactionalStep postBodies true ==
    .unwoundWithCleanup (2, 161) (1, 2) [10, 1, 2])

/-- Repaired full two-sided lowering validator (`R2`, repairing `U3`, `U4`, and `U7`). -/
def validateBuiltToPostCleanupFailClosed
    (policy : UbPrefixObservationPolicy)
    (expectedCtx : ExpectedCargoInvocationContext)
    (builtBindingRec postCleanupBindingRec : CargoInvocationBindingRecord)
    (crateNameBytes expectedTargetTripleBytes : List Nat)
    (expectedEntriesFp16 : Nat × Nat)
    (builtPkgBytes postCleanupPkgBytes : List Nat)
    (layoutTbl : BoundCompilerLayoutTable)
    (targetTripleBytes : List Nat) : Bool :=
  checkTwoPhaseCompilationIdentity expectedCtx builtBindingRec postCleanupBindingRec
    crateNameBytes builtPkgBytes postCleanupPkgBytes layoutTbl &&
  checkLayoutTableBindingWithEntries expectedCtx crateNameBytes expectedTargetTripleBytes
    expectedEntriesFp16 layoutTbl targetTripleBytes &&
  match parseRawPackageBytes postCleanupPkgBytes with
  | .ok (postPkg, []) =>
      bif checkPostCleanupPackageStructure postPkg then
        match parseRawPackageBytes builtPkgBytes with
        | .ok (builtPkg, []) =>
            checkBuiltPackageStructure builtPkg &&
            checkBuiltToPostCleanupBehavioralEquivFailClosed policy expectedCtx crateNameBytes
              expectedTargetTripleBytes expectedEntriesFp16 layoutTbl targetTripleBytes
              builtPkg.bodies postPkg.bodies
        | _ => false
      else false
  | _ => false

theorem r2_fail_closed_two_sided_validator_accepts_real_package :
    validateBuiltToPostCleanupFailClosed
      .strictPrefixTracePreserving
      statefulGenericLibExpectedCtx
      statefulGenericLibBuiltBindingRec
      statefulGenericLibBindingRec
      statefulGenericLibCrateBytes
      x86_64LinuxTargetTripleBytes
      statefulGenericLibEntriesFp16
      realStatefulGenericLibBuiltAmirBytes
      realStatefulGenericLibAmirBytes
      statefulGenericLibLayoutTable
      x86_64LinuxTargetTripleBytes = true := by
  decide

/-- **Acceptance-Implies-Refinement Soundness Theorem (`R2`, `#89` §9)**:
    Whenever `checkBuiltToPostCleanupBehavioralEquivFailClosed .strictPrefixTracePreserving` returns
    `true`, the derived layout bodies are non-empty, both `builtBodies` and `postBodies` are
    runtime-closed (`checkRuntimeClosedBodies = true`), both invalid-pointer executions halt at
    `.ub` with identical empty pre-UB side-effect traces `({0, 0}, [])`, and all three valid-input
    executions (`step_generic_slot` at `ptrValid = true` and `transactional_step` at
    `triggerPanic ∈ {false, true}`) succeed with identical normal/unwind outcomes on both graphs! -/
theorem checkBuiltToPostCleanupBehavioralEquivFailClosed_sound
    (expectedCtx : ExpectedCargoInvocationContext)
    (crateNameBytes expectedTargetTripleBytes : List Nat)
    (expectedEntriesFp16 : Nat × Nat)
    (layoutTbl : BoundCompilerLayoutTable)
    (targetTripleBytes : List Nat)
    (builtRawBodies postRawBodies : List WireBody)
    (hAccept :
      checkBuiltToPostCleanupBehavioralEquivFailClosed
        .strictPrefixTracePreserving expectedCtx crateNameBytes expectedTargetTripleBytes
        expectedEntriesFp16 layoutTbl targetTripleBytes builtRawBodies postRawBodies = true) :
    let layoutBodies :=
      deriveLayoutCalleeBodiesChecked expectedCtx crateNameBytes expectedTargetTripleBytes
        expectedEntriesFp16 layoutTbl targetTripleBytes .u32
    let builtBodies := builtRawBodies ++ layoutBodies
    let postBodies := postRawBodies ++ layoutBodies
    layoutBodies.length = 2 ∧
    checkRuntimeClosedBodies builtBodies = true ∧
    checkRuntimeClosedBodies postBodies = true ∧
    evalBuiltStepGenericSlotFromGraph builtBodies 0 0 false 16 =
      (.ub, { stepCount := 0, traceAcc := 0 }, []) ∧
    evalStepGenericSlot postBodies 0 0 false 16 =
      (.ub, { stepCount := 0, traceAcc := 0 }, []) ∧
    evalBuiltStepGenericSlotFromGraph builtBodies 0 0 true 16 =
      evalStepGenericSlot postBodies 0 0 true 16 ∧
    evalBuiltStepGenericSlotFromGraph builtBodies 0 0 true 16 =
      (.returned (.scalar 20), { stepCount := 1, traceAcc := 4 }, [4]) ∧
    evalBuiltTransactionalStepFromGraph builtBodies false =
      evalPostCleanupTransactionalStep postBodies false ∧
    evalBuiltTransactionalStepFromGraph builtBodies true =
      evalPostCleanupTransactionalStep postBodies true := by
  dsimp only
  unfold checkBuiltToPostCleanupBehavioralEquivFailClosed checkUbInvalidPtrEquivUnderPolicy at hAccept
  simp only [Bool.and_eq_true, beq_iff_eq] at hAccept
  rcases hAccept with ⟨⟨⟨⟨⟨⟨⟨⟨⟨hNonEmpty, hClosedBuilt⟩, hClosedPost⟩, ⟨hUbBuilt, hUbPost⟩⟩, hStepBuilt⟩, hStepPost⟩, hTransFalseBuilt⟩, hTransFalsePost⟩, hTransTrueBuilt⟩, hTransTruePost⟩
  refine ⟨hNonEmpty, hClosedBuilt, hClosedPost, hUbBuilt, hUbPost, ?_, hStepBuilt, ?_, ?_⟩
  · rw [hStepBuilt, hStepPost]
  · rw [hTransFalseBuilt, hTransFalsePost]
  · rw [hTransTrueBuilt, hTransTruePost]

/-! ## 3. `R8` (`U5`): Environment-Bound Structured View & General Acceptance-Implies-Correspondence -/

/-- Environment-bound structured view carrying both the callee layout constant `alignConst`
    (from `symId = 38` in `allBodies`) and the extracted statement/terminator constants (`R8`, `U5`). -/
inductive VerifiedStructuredStmtView where
  | checkPtrAndStepSlotWithAlign (ptrLocal baseLocal alignConst eventTag : Nat)
  | callStepSlotAndAddConstWithEnv (baseLocal alignConst libEventTag addConst : Nat)
  deriving DecidableEq, Repr

def bb0_GEN_63 : WireBlock :=
  { isCleanup := false
  , stmts :=
      [ .storageLive 4
      , .assignUseRetagYes { localIdx := 4, proj := .here } .constUnit
      , .storageDead 4
      , .placeMention { localIdx := 2, proj := .deref }
      , .storageLive 5 ]
  , term := .call0 38 { localIdx := 5, proj := .here } (some 1) .continueUnwind }

def bb1_GEN_63 (evTag : Nat) : WireBlock :=
  { isCleanup := false
  , stmts :=
      [ .storageLive 6
      , .storageLive 7
      , .assignRefOrPtr { localIdx := 7, proj := .here } .mutRef { localIdx := 1, proj := .deref } ]
  , term :=
      .call2 1 { localIdx := 6, proj := .here } (some 2) .continueUnwind
        (.move { localIdx := 7, proj := .here }) (.constU32 evTag) }

def bb2_GEN_63 : WireBlock :=
  { isCleanup := false
  , stmts :=
      [ .storageDead 7
      , .storageDead 6
      , .storageLive 8
      , .assignUseRetagYes { localIdx := 8, proj := .here } (.copy { localIdx := 3, proj := .here })
      , .storageLive 9
      , .assignUseRetagYes { localIdx := 9, proj := .here } (.copy { localIdx := 5, proj := .here }) ]
  , term :=
      .call2 40 { localIdx := 0, proj := .here } (some 3) .continueUnwind
        (.move { localIdx := 8, proj := .here }) (.move { localIdx := 9, proj := .here }) }

def bb3_GEN_63 : WireBlock :=
  { isCleanup := false
  , stmts := [ .storageDead 9, .storageDead 8, .storageDead 5 ]
  , term := .ret }

def blocks_GEN_63 (evTag : Nat) : List WireBlock :=
  [bb0_GEN_63, bb1_GEN_63 evTag, bb2_GEN_63, bb3_GEN_63]

def localTypes_GEN_63 : List MirTypeTag :=
  [.usize, .refMutEffectLog, .rawPtrU32, .usize, .unit, .usize, .unit, .refMutEffectLog, .usize, .usize]

/-- Canonical `step_generic_slot` (`symId = 63`) body parameterized by `evTag`. -/
def mkCanonicalStepSlotBody (bodyId : Nat) (evTag : Nat) : WireBody :=
  { bodyId := bodyId
  , symId := 63
  , originKind := .localOwner
  , mirPhase := .runtimePostCleanup
  , localCount := 10
  , argCount := 3
  , localTypes := localTypes_GEN_63
  , blocks := blocks_GEN_63 evTag }

/-- Canonical `align_of::<T>()` (`symId = 38`) body parameterized by `alignConst`. -/
def mkCanonicalAlignOfBody (bodyId : Nat) (alignConst : Nat) : WireBody :=
  { bodyId := bodyId
  , symId := 38
  , originKind := .externalOptimized
  , mirPhase := .runtimeOptimized
  , localCount := 1
  , argCount := 0
  , localTypes := [.usize]
  , blocks :=
      [ { isCleanup := false
        , stmts := [.assignUseRetagYes { localIdx := 0, proj := .here } (.constUsize alignConst)]
        , term := .ret } ] }

def extractEventTagFromBlock1 (b : WireBody) : Option Nat :=
  match b.blocks with
  | _ :: bb1 :: _ =>
      match bb1.term with
      | .call2 1 _ _ _ _ (.constU32 evTag) => some evTag
      | _ => none
  | _ => none

def extractConstFromAlignBody (bAlign : WireBody) : Option Nat :=
  match bAlign.blocks with
  | [blk0] =>
      match blk0.stmts with
      | [.assignUseRetagYes { localIdx := 0, proj := .here } (.constUsize k)] => some k
      | _ => none
  | _ => none

def extractAddConstFromClientBlock1 (b : WireBody) : Option Nat :=
  match b.blocks with
  | _ :: bb1 :: _ =>
      match bb1.term with
      | .call2 40 _ _ _ _ (.constUsize addK) => some addK
      | _ => none
  | _ => none

def mkCanonicalClientContractBody (bodyId : Nat) (addK : Nat) : WireBody :=
  { bodyId := bodyId
  , symId := 66
  , originKind := .localOwner
  , mirPhase := .runtimePostCleanup
  , localCount := 9
  , argCount := 3
  , localTypes := [.usize, .refMutEffectLog, .rawPtrU32, .usize, .usize, .refMutEffectLog, .rawPtrU32, .usize, .usize]
  , blocks :=
      [ { isCleanup := false
        , stmts :=
            [ .storageLive 4
            , .storageLive 5
            , .assignRefOrPtr { localIdx := 5, proj := .here } .mutRef { localIdx := 1, proj := .deref }
            , .storageLive 6
            , .assignUseRetagYes { localIdx := 6, proj := .here } (.copy { localIdx := 2, proj := .here })
            , .storageLive 7
            , .assignUseRetagYes { localIdx := 7, proj := .here } (.copy { localIdx := 3, proj := .here }) ]
        , term :=
            .call3 63 { localIdx := 4, proj := .here } (some 1) .continueUnwind
              (.move { localIdx := 5, proj := .here })
              (.move { localIdx := 6, proj := .here })
              (.move { localIdx := 7, proj := .here }) }
      , { isCleanup := false
        , stmts :=
            [ .storageDead 7
            , .storageDead 6
            , .storageDead 5
            , .storageLive 8
            , .assignUseRetagYes { localIdx := 8, proj := .here } (.copy { localIdx := 4, proj := .here }) ]
        , term :=
            .call2 40 { localIdx := 0, proj := .here } (some 2) .continueUnwind
              (.move { localIdx := 8, proj := .here }) (.constUsize addK) }
      , { isCleanup := false
        , stmts := [ .storageDead 8, .storageDead 4 ]
        , term := .ret } ] }

/-- Non-recursive helper recognizing `step_generic_slot` (`symId = 63`) TOGETHER with its callee
    environment in `allBodies` (`symId = 38` `align_of`, `symId = 1` `EffectLog::record`, and
    absence of overriding `symId ∈ {20, 21, 40}` bodies so `wrapping_add`/`wrapping_mul` execute
    as the verified intrinsics). -/
def reconstructStepSlotViewInEnv
    (allBodies : List WireBody)
    (b : WireBody) : Option (Nat × Nat) :=
  match extractEventTagFromBlock1 b,
        findBodyBySym allBodies 38,
        findBodyBySym allBodies 1,
        findBodyBySym allBodies 20,
        findBodyBySym allBodies 21,
        findBodyBySym allBodies 40 with
  | some evTag, some bAlign, some bRec, none, none, none =>
      match extractConstFromAlignBody bAlign with
      | some alignConst =>
          bif (b == mkCanonicalStepSlotBody b.bodyId evTag &&
               bAlign == mkCanonicalAlignOfBody bAlign.bodyId alignConst &&
               bRec == body_D_1_0) then
            some (alignConst, evTag)
          else none
      | none => none
  | _, _, _, _, _, _ => none

/-- **Repaired Environment-Bound Two-Body Canonical Recognizer (`reconstructVerifiedStructuredViewInEnv`, `R8` / `U5` & `Q7`, `#93` §12)**:
    Certifies the two canonical body templates (`symId = 63` `step_generic_slot` via
    `mkCanonicalStepSlotBody b.bodyId evTag` and `symId = 66` `client_contract_entry` via
    `mkCanonicalClientContractBody b.bodyId addK`) together with their extracted scalar constants
    (`alignConst`, `evTag`, `addK`) and resolved callee environment (`38`, `1`, and absence of
    overriding `20, 21, 40`) in `allBodies`. This is a two-body canonical recognizer with extracted
    scalar constants, not a general structured-view decompiler for arbitrary safe non-cleanup MIR. -/
def reconstructVerifiedStructuredViewInEnv
    (allBodies : List WireBody)
    (b : WireBody) : Option VerifiedStructuredStmtView :=
  bif (b.symId == 63) then
    match reconstructStepSlotViewInEnv allBodies b with
    | some (alignConst, evTag) =>
        some (.checkPtrAndStepSlotWithAlign 2 3 alignConst evTag)
    | none => none
  else bif (b.symId == 66) then
    match extractAddConstFromClientBlock1 b, findBodyBySym allBodies 63 with
    | some addK, some bStep =>
        match reconstructStepSlotViewInEnv allBodies bStep with
        | some (alignConst, evTag) =>
            bif (b == mkCanonicalClientContractBody b.bodyId addK) then
              some (.callStepSlotAndAddConstWithEnv 3 alignConst evTag addK)
            else none
        | none => none
    | _, _ => none
  else
    none

def evalVerifiedStructuredView
    (view : VerifiedStructuredStmtView)
    (s0 t0 : Nat)
    (ptrValid : Bool)
    (base : Nat) : ExecStatus × HeapLogSlot × List Nat :=
  match view with
  | .checkPtrAndStepSlotWithAlign _ _ alignConst evTag =>
      if !ptrValid then
        (.ub, { stepCount := s0, traceAcc := t0 }, [])
      else
        let s1 := (s0 + 1) % u32Mod
        let t1 := ((t0 * 16) % u32Mod + evTag) % u32Mod
        (.returned (.scalar ((base + alignConst) % usizeMod)), { stepCount := s1, traceAcc := t1 }, [evTag])
  | .callStepSlotAndAddConstWithEnv _ alignConst evTag addK =>
      if !ptrValid then
        (.ub, { stepCount := s0, traceAcc := t0 }, [])
      else
        let s1 := (s0 + 1) % u32Mod
        let t1 := ((t0 * 16) % u32Mod + evTag) % u32Mod
        (.returned (.scalar ((((base + alignConst) % usizeMod) + addK) % usizeMod)), { stepCount := s1, traceAcc := t1 }, [evTag])

/-! ### Symbolic Step States for General `reconstructVerifiedStructuredViewInEnv` Soundness (`R8`) -/

def bb0_D_1_0 : WireBlock :=
  { isCleanup := false
  , stmts :=
      [ WireStmt.storageLive 3
      , WireStmt.storageLive 4
      , WireStmt.assignUseRetagYes { localIdx := 4, proj := ProjChain.here } (OperandSpec.copy { localIdx := 1, proj := ProjChain.derefField0 }) ]
  , term :=
      WireTerm.call2 20 { localIdx := 3, proj := ProjChain.here } (some 1) UnwindSpec.continueUnwind
        (OperandSpec.move { localIdx := 4, proj := ProjChain.here }) (OperandSpec.constU32 1) }

def bb1_D_1_0 : WireBlock :=
  { isCleanup := false
  , stmts :=
      [ WireStmt.storageDead 4
      , WireStmt.assignUseRetagYes { localIdx := 1, proj := ProjChain.derefField0 } (OperandSpec.move { localIdx := 3, proj := ProjChain.here })
      , WireStmt.storageDead 3
      , WireStmt.storageLive 5
      , WireStmt.storageLive 6
      , WireStmt.storageLive 7
      , WireStmt.assignUseRetagYes { localIdx := 7, proj := ProjChain.here } (OperandSpec.copy { localIdx := 1, proj := ProjChain.derefField1 }) ]
  , term :=
      WireTerm.call2 21 { localIdx := 6, proj := ProjChain.here } (some 2) UnwindSpec.continueUnwind
        (OperandSpec.move { localIdx := 7, proj := ProjChain.here }) (OperandSpec.constU32 16) }

def bb2_D_1_0 : WireBlock :=
  { isCleanup := false
  , stmts :=
      [ WireStmt.storageDead 7
      , WireStmt.storageLive 8
      , WireStmt.assignUseRetagYes { localIdx := 8, proj := ProjChain.here } (OperandSpec.copy { localIdx := 2, proj := ProjChain.here }) ]
  , term :=
      WireTerm.call2 20 { localIdx := 5, proj := ProjChain.here } (some 3) UnwindSpec.continueUnwind
        (OperandSpec.move { localIdx := 6, proj := ProjChain.here }) (OperandSpec.move { localIdx := 8, proj := ProjChain.here }) }

def bb3_D_1_0 : WireBlock :=
  { isCleanup := false
  , stmts :=
      [ WireStmt.storageDead 8
      , WireStmt.storageDead 6
      , WireStmt.assignUseRetagYes { localIdx := 1, proj := ProjChain.derefField1 } (OperandSpec.move { localIdx := 5, proj := ProjChain.here })
      , WireStmt.storageDead 5
      , WireStmt.assignUseRetagYes { localIdx := 0, proj := ProjChain.here } OperandSpec.constUnit ]
  , term := WireTerm.ret }

def st_GEN_0 (evTag : Nat) (ptrValid : Bool) (base : Nat) : ExecState :=
  { status := .running
  , stack :=
      [ { symId := 63
        , localTypes := localTypes_GEN_63
        , bodyBlocks := blocks_GEN_63 evTag
        , bbIdx := 0
        , remStmts := bb0_GEN_63.stmts
        , curTerm := bb0_GEN_63.term
        , locals := [(0, .agg0 1), (1, .heapPtr 0), (2, .extPtr ptrValid), (3, .scalar base)]
        , pending := none } ]
  , heap := [{ stepCount := 0, traceAcc := 0 }]
  , obsEvents := [] }

def st_GEN_1 (aId : Nat) (alignConst evTag : Nat) (base : Nat) : ExecState :=
  { status := .running
  , stack :=
      [ { symId := 38
        , localTypes := [.usize]
        , bodyBlocks := (mkCanonicalAlignOfBody aId alignConst).blocks
        , bbIdx := 0
        , remStmts := [.assignUseRetagYes { localIdx := 0, proj := .here } (.constUsize alignConst)]
        , curTerm := .ret
        , locals := [(0, .agg0 1)]
        , pending := none }
      , { symId := 63
        , localTypes := localTypes_GEN_63
        , bodyBlocks := blocks_GEN_63 evTag
        , bbIdx := 0
        , remStmts := []
        , curTerm := bb0_GEN_63.term
        , locals := [(0, .agg0 1), (1, .heapPtr 0), (2, .extPtr true), (3, .scalar base)]
        , pending := some { retDst := { localIdx := 5, proj := .here }, targetBbOpt := some 1, unwind := .continueUnwind, isDropGlue := false } } ]
  , heap := [{ stepCount := 0, traceAcc := 0 }]
  , obsEvents := [] }

def st_GEN_2 (alignConst evTag : Nat) (base : Nat) : ExecState :=
  { status := .running
  , stack :=
      [ { symId := 63
        , localTypes := localTypes_GEN_63
        , bodyBlocks := blocks_GEN_63 evTag
        , bbIdx := 1
        , remStmts := (bb1_GEN_63 evTag).stmts
        , curTerm := (bb1_GEN_63 evTag).term
        , locals := [(0, .agg0 1), (1, .heapPtr 0), (2, .extPtr true), (3, .scalar base), (5, .scalar alignConst)]
        , pending := none } ]
  , heap := [{ stepCount := 0, traceAcc := 0 }]
  , obsEvents := [] }

def st_GEN_3 (alignConst evTag : Nat) (base : Nat) : ExecState :=
  { status := .running
  , stack :=
      [ { symId := 1
        , localTypes := body_D_1_0.localTypes
        , bodyBlocks := blocks_D_1_0
        , bbIdx := 0
        , remStmts := bb0_D_1_0.stmts
        , curTerm := bb0_D_1_0.term
        , locals := [(0, .agg0 1), (1, .heapPtr 0), (2, .scalar evTag)]
        , pending := none }
      , { symId := 63
        , localTypes := localTypes_GEN_63
        , bodyBlocks := blocks_GEN_63 evTag
        , bbIdx := 1
        , remStmts := []
        , curTerm := (bb1_GEN_63 evTag).term
        , locals := [(0, .agg0 1), (1, .heapPtr 0), (2, .extPtr true), (3, .scalar base), (5, .scalar alignConst), (7, .heapPtr 0)]
        , pending := some { retDst := { localIdx := 6, proj := .here }, targetBbOpt := some 2, unwind := .continueUnwind, isDropGlue := false } } ]
  , heap := [{ stepCount := 0, traceAcc := 0 }]
  , obsEvents := [evTag] }

def st_GEN_4 (alignConst evTag : Nat) (base : Nat) : ExecState :=
  { status := .running
  , stack :=
      [ { symId := 1
        , localTypes := body_D_1_0.localTypes
        , bodyBlocks := blocks_D_1_0
        , bbIdx := 1
        , remStmts := bb1_D_1_0.stmts
        , curTerm := bb1_D_1_0.term
        , locals := [(0, .agg0 1), (1, .heapPtr 0), (2, .scalar evTag), (3, .scalar 1), (4, .scalar 0)]
        , pending := none }
      , { symId := 63
        , localTypes := localTypes_GEN_63
        , bodyBlocks := blocks_GEN_63 evTag
        , bbIdx := 1
        , remStmts := []
        , curTerm := (bb1_GEN_63 evTag).term
        , locals := [(0, .agg0 1), (1, .heapPtr 0), (2, .extPtr true), (3, .scalar base), (5, .scalar alignConst), (7, .heapPtr 0)]
        , pending := some { retDst := { localIdx := 6, proj := .here }, targetBbOpt := some 2, unwind := .continueUnwind, isDropGlue := false } } ]
  , heap := [{ stepCount := 0, traceAcc := 0 }]
  , obsEvents := [evTag] }

def st_GEN_5 (alignConst evTag : Nat) (base : Nat) : ExecState :=
  { status := .running
  , stack :=
      [ { symId := 1
        , localTypes := body_D_1_0.localTypes
        , bodyBlocks := blocks_D_1_0
        , bbIdx := 2
        , remStmts := bb2_D_1_0.stmts
        , curTerm := bb2_D_1_0.term
        , locals := [(0, .agg0 1), (1, .heapPtr 0), (2, .scalar evTag), (6, .scalar 0), (7, .scalar 0)]
        , pending := none }
      , { symId := 63
        , localTypes := localTypes_GEN_63
        , bodyBlocks := blocks_GEN_63 evTag
        , bbIdx := 1
        , remStmts := []
        , curTerm := (bb1_GEN_63 evTag).term
        , locals := [(0, .agg0 1), (1, .heapPtr 0), (2, .extPtr true), (3, .scalar base), (5, .scalar alignConst), (7, .heapPtr 0)]
        , pending := some { retDst := { localIdx := 6, proj := .here }, targetBbOpt := some 2, unwind := .continueUnwind, isDropGlue := false } } ]
  , heap := [{ stepCount := 1, traceAcc := 0 }]
  , obsEvents := [evTag] }

def st_GEN_6 (alignConst evTag : Nat) (base : Nat) : ExecState :=
  { status := .running
  , stack :=
      [ { symId := 1
        , localTypes := body_D_1_0.localTypes
        , bodyBlocks := blocks_D_1_0
        , bbIdx := 3
        , remStmts := bb3_D_1_0.stmts
        , curTerm := bb3_D_1_0.term
        , locals := [(0, .agg0 1), (1, .heapPtr 0), (2, .scalar evTag), (5, .scalar ((0 + evTag) % u32Mod)), (6, .scalar 0), (8, .scalar evTag)]
        , pending := none }
      , { symId := 63
        , localTypes := localTypes_GEN_63
        , bodyBlocks := blocks_GEN_63 evTag
        , bbIdx := 1
        , remStmts := []
        , curTerm := (bb1_GEN_63 evTag).term
        , locals := [(0, .agg0 1), (1, .heapPtr 0), (2, .extPtr true), (3, .scalar base), (5, .scalar alignConst), (7, .heapPtr 0)]
        , pending := some { retDst := { localIdx := 6, proj := .here }, targetBbOpt := some 2, unwind := .continueUnwind, isDropGlue := false } } ]
  , heap := [{ stepCount := 1, traceAcc := 0 }]
  , obsEvents := [evTag] }

def st_GEN_7 (alignConst evTag : Nat) (base : Nat) : ExecState :=
  { status := .running
  , stack :=
      [ { symId := 63
        , localTypes := localTypes_GEN_63
        , bodyBlocks := blocks_GEN_63 evTag
        , bbIdx := 2
        , remStmts := bb2_GEN_63.stmts
        , curTerm := bb2_GEN_63.term
        , locals := [(0, .agg0 1), (1, .heapPtr 0), (2, .extPtr true), (3, .scalar base), (5, .scalar alignConst), (6, .agg0 1), (7, .heapPtr 0)]
        , pending := none } ]
  , heap := [{ stepCount := 1, traceAcc := (0 + evTag) % u32Mod }]
  , obsEvents := [evTag] }

def st_GEN_8 (alignConst evTag : Nat) (base : Nat) : ExecState :=
  { status := .running
  , stack :=
      [ { symId := 63
        , localTypes := localTypes_GEN_63
        , bodyBlocks := blocks_GEN_63 evTag
        , bbIdx := 3
        , remStmts := bb3_GEN_63.stmts
        , curTerm := bb3_GEN_63.term
        , locals := [(0, .scalar ((base + alignConst) % usizeMod)), (1, .heapPtr 0), (2, .extPtr true), (3, .scalar base), (5, .scalar alignConst), (8, .scalar base), (9, .scalar alignConst)]
        , pending := none } ]
  , heap := [{ stepCount := 1, traceAcc := (0 + evTag) % u32Mod }]
  , obsEvents := [evTag] }

def st_GEN_9 (alignConst evTag : Nat) (base : Nat) : ExecState :=
  { status := .returned (.scalar ((base + alignConst) % usizeMod))
  , stack := []
  , heap := [{ stepCount := 1, traceAcc := (0 + evTag) % u32Mod }]
  , obsEvents := [evTag] }

theorem step_GEN_0_to_1
    (allBodies : List WireBody) (aId alignConst evTag base : Nat)
    (hFind38 : findBodyBySym allBodies 38 = some (mkCanonicalAlignOfBody aId alignConst)) :
    stepState allBodies (st_GEN_0 evTag true base) = st_GEN_1 aId alignConst evTag base := by
  dsimp only [st_GEN_0, stepState, execBlockStmts, bb0_GEN_63, stepStmt, evalOperand, readPlace, writePlace, setLocal, getLocal, eraseLocal,
    stepTerm, dispatchCall, evalOperandList]
  rw [hFind38]
  rfl

theorem step_GEN_1_to_2
    (allBodies : List WireBody) (aId alignConst evTag base : Nat) :
    stepState allBodies (st_GEN_1 aId alignConst evTag base) = st_GEN_2 alignConst evTag base := by
  rfl

theorem step_GEN_2_to_3
    (allBodies : List WireBody) (alignConst evTag base : Nat)
    (hFind1 : findBodyBySym allBodies 1 = some body_D_1_0) :
    stepState allBodies (st_GEN_2 alignConst evTag base) = st_GEN_3 alignConst evTag base := by
  dsimp only [st_GEN_2, stepState, execBlockStmts, bb1_GEN_63, stepStmt, evalOperand, makeRef, readPlace, writePlace, setLocal, getLocal, eraseLocal,
    stepTerm, dispatchCall, evalOperandList]
  rw [hFind1]
  rfl

theorem step_GEN_3_to_4
    (allBodies : List WireBody) (alignConst evTag base : Nat)
    (hFind20 : findBodyBySym allBodies 20 = none) :
    stepState allBodies (st_GEN_3 alignConst evTag base) = st_GEN_4 alignConst evTag base := by
  dsimp only [st_GEN_3, stepState, execBlockStmts, bb0_D_1_0, stepStmt, evalOperand, readPlace, getHeapSlot, writePlace, setLocal, getLocal, eraseLocal,
    stepTerm, dispatchCall, evalOperandList]
  rw [hFind20]
  rfl

theorem step_GEN_4_to_5
    (allBodies : List WireBody) (alignConst evTag base : Nat)
    (hFind21 : findBodyBySym allBodies 21 = none) :
    stepState allBodies (st_GEN_4 alignConst evTag base) = st_GEN_5 alignConst evTag base := by
  dsimp only [st_GEN_4, stepState, execBlockStmts, bb1_D_1_0, stepStmt, evalOperand, readPlace, getHeapSlot, setHeapSlot, writePlace, setLocal, getLocal, eraseLocal,
    stepTerm, dispatchCall, evalOperandList]
  rw [hFind21]
  rfl

theorem step_GEN_5_to_6
    (allBodies : List WireBody) (alignConst evTag base : Nat)
    (hFind20 : findBodyBySym allBodies 20 = none) :
    stepState allBodies (st_GEN_5 alignConst evTag base) = st_GEN_6 alignConst evTag base := by
  dsimp only [st_GEN_5, stepState, execBlockStmts, bb2_D_1_0, stepStmt, evalOperand, readPlace, getHeapSlot, writePlace, setLocal, getLocal, eraseLocal,
    stepTerm, dispatchCall, evalOperandList]
  rw [hFind20]
  rfl

theorem step_GEN_6_to_7
    (allBodies : List WireBody) (alignConst evTag base : Nat) :
    stepState allBodies (st_GEN_6 alignConst evTag base) = st_GEN_7 alignConst evTag base := by
  rfl

theorem step_GEN_7_to_8
    (allBodies : List WireBody) (alignConst evTag base : Nat)
    (hFind40 : findBodyBySym allBodies 40 = none) :
    stepState allBodies (st_GEN_7 alignConst evTag base) = st_GEN_8 alignConst evTag base := by
  dsimp only [st_GEN_7, stepState, execBlockStmts, bb2_GEN_63, stepStmt, evalOperand, readPlace, writePlace, setLocal, getLocal, eraseLocal,
    stepTerm, dispatchCall, evalOperandList]
  rw [hFind40]
  rfl

theorem step_GEN_8_to_9
    (allBodies : List WireBody) (alignConst evTag base : Nat) :
    stepState allBodies (st_GEN_8 alignConst evTag base) = st_GEN_9 alignConst evTag base := by
  rfl

theorem runSteps_GEN_full
    (allBodies : List WireBody) (bId aId alignConst evTag base : Nat)
    (hFind63 : findBodyBySym allBodies 63 = some (mkCanonicalStepSlotBody bId evTag))
    (hFind38 : findBodyBySym allBodies 38 = some (mkCanonicalAlignOfBody aId alignConst))
    (hFind1 : findBodyBySym allBodies 1 = some body_D_1_0)
    (hFind20 : findBodyBySym allBodies 20 = none)
    (hFind21 : findBodyBySym allBodies 21 = none)
    (hFind40 : findBodyBySym allBodies 40 = none) :
    runSteps allBodies 12
      (initEntryStateWithHeap allBodies 63 [.heapPtr 0, .extPtr true, .scalar base] [{ stepCount := 0, traceAcc := 0 }]) =
      st_GEN_9 alignConst evTag base := by
  have hInit :
      initEntryStateWithHeap allBodies 63 [.heapPtr 0, .extPtr true, .scalar base] [{ stepCount := 0, traceAcc := 0 }] =
        st_GEN_0 evTag true base := by
    unfold initEntryStateWithHeap
    rw [hFind63]
    rfl
  rw [hInit]
  change runSteps allBodies 11 (stepState allBodies (st_GEN_0 evTag true base)) = _
  rw [step_GEN_0_to_1 allBodies aId alignConst evTag base hFind38]
  change runSteps allBodies 10 (stepState allBodies (st_GEN_1 aId alignConst evTag base)) = _
  rw [step_GEN_1_to_2 allBodies aId alignConst evTag base]
  change runSteps allBodies 9 (stepState allBodies (st_GEN_2 alignConst evTag base)) = _
  rw [step_GEN_2_to_3 allBodies alignConst evTag base hFind1]
  change runSteps allBodies 8 (stepState allBodies (st_GEN_3 alignConst evTag base)) = _
  rw [step_GEN_3_to_4 allBodies alignConst evTag base hFind20]
  change runSteps allBodies 7 (stepState allBodies (st_GEN_4 alignConst evTag base)) = _
  rw [step_GEN_4_to_5 allBodies alignConst evTag base hFind21]
  change runSteps allBodies 6 (stepState allBodies (st_GEN_5 alignConst evTag base)) = _
  rw [step_GEN_5_to_6 allBodies alignConst evTag base hFind20]
  change runSteps allBodies 5 (stepState allBodies (st_GEN_6 alignConst evTag base)) = _
  rw [step_GEN_6_to_7 allBodies alignConst evTag base]
  change runSteps allBodies 4 (stepState allBodies (st_GEN_7 alignConst evTag base)) = _
  rw [step_GEN_7_to_8 allBodies alignConst evTag base hFind40]
  change runSteps allBodies 3 (stepState allBodies (st_GEN_8 alignConst evTag base)) = _
  rw [step_GEN_8_to_9 allBodies alignConst evTag base]
  rfl

theorem runSteps_GEN_false
    (allBodies : List WireBody) (bId evTag base : Nat)
    (hFind63 : findBodyBySym allBodies 63 = some (mkCanonicalStepSlotBody bId evTag)) :
    runSteps allBodies 12
      (initEntryStateWithHeap allBodies 63 [.heapPtr 0, .extPtr false, .scalar base] [{ stepCount := 0, traceAcc := 0 }]) =
      { status := .ub
      , stack :=
          [ { symId := 63
            , localTypes := localTypes_GEN_63
            , bodyBlocks := blocks_GEN_63 evTag
            , bbIdx := 0
            , remStmts := []
            , curTerm := bb0_GEN_63.term
            , locals := [(0, .agg0 1), (1, .heapPtr 0), (2, .extPtr false), (3, .scalar base)]
            , pending := none } ]
      , heap := [{ stepCount := 0, traceAcc := 0 }]
      , obsEvents := [] } := by
  have hInit :
      initEntryStateWithHeap allBodies 63 [.heapPtr 0, .extPtr false, .scalar base] [{ stepCount := 0, traceAcc := 0 }] =
        st_GEN_0 evTag false base := by
    unfold initEntryStateWithHeap
    rw [hFind63]
    rfl
  rw [hInit]
  rfl

/-- **General Acceptance-Implies-Correspondence Theorem for `reconstructVerifiedStructuredViewInEnv` (`R8`, `U5`)**:
    For **any** `allBodies : List WireBody`, **any** `b : WireBody`, **any** `alignConst evTag : Nat`,
    **any** `ptrValid : Bool`, and **any** `base : Nat`, if
    `findBodyBySym allBodies 63 = some b` and `reconstructVerifiedStructuredViewInEnv allBodies b`
    returns `some (.checkPtrAndStepSlotWithAlign 2 3 alignConst evTag)`, then executing `allBodies`
    via `evalStepGenericSlot` (`runSteps`) equals `evalVerifiedStructuredView`! -/
theorem reconstructVerifiedStructuredViewInEnv_general_step_slot_sound
    (allBodies : List WireBody) (b : WireBody) (alignConst evTag : Nat)
    (hFind63 : findBodyBySym allBodies 63 = some b)
    (hRec : reconstructVerifiedStructuredViewInEnv allBodies b =
      some (.checkPtrAndStepSlotWithAlign 2 3 alignConst evTag)) :
    ∀ ptrValid : Bool, ∀ base : Nat,
      evalStepGenericSlot allBodies 0 0 ptrValid base =
        evalVerifiedStructuredView (.checkPtrAndStepSlotWithAlign 2 3 alignConst evTag) 0 0 ptrValid base := by
  unfold reconstructVerifiedStructuredViewInEnv at hRec
  cases hBeq63 : (b.symId == 63) with
  | false =>
      rw [hBeq63] at hRec
      dsimp only [Bool.cond_false] at hRec
      cases hBeq66 : (b.symId == 66) with
      | false =>
          rw [hBeq66] at hRec
          contradiction
      | true =>
          rw [hBeq66] at hRec
          dsimp only [Bool.cond_true] at hRec
          cases h1 : extractAddConstFromClientBlock1 b with
          | none => rw [h1] at hRec; contradiction
          | some addK =>
            cases h2 : findBodyBySym allBodies 63 with
            | none => rw [h1, h2] at hRec; contradiction
            | some bStep =>
              rw [h1, h2] at hRec
              dsimp only at hRec
              cases h3 : reconstructStepSlotViewInEnv allBodies bStep with
              | none =>
                  rw [h3] at hRec
                  contradiction
              | some p =>
                  rcases p with ⟨al, ev⟩
                  rw [h3] at hRec
                  dsimp only at hRec
                  cases hEqC : (b == mkCanonicalClientContractBody b.bodyId addK) <;>
                  rw [hEqC] at hRec <;> simp at hRec
  | true =>
      rw [hBeq63] at hRec
      dsimp only [Bool.cond_true] at hRec
      unfold reconstructStepSlotViewInEnv at hRec
      cases hEv : extractEventTagFromBlock1 b with
      | none => rw [hEv] at hRec; contradiction
      | some evTag0 =>
        cases h38 : findBodyBySym allBodies 38 with
        | none => rw [hEv, h38] at hRec; contradiction
        | some bAlign =>
          cases h1 : findBodyBySym allBodies 1 with
          | none => rw [hEv, h38, h1] at hRec; contradiction
          | some bRec =>
            cases h20 : findBodyBySym allBodies 20 with
            | some _ => rw [hEv, h38, h1, h20] at hRec; contradiction
            | none =>
              cases h21 : findBodyBySym allBodies 21 with
              | some _ => rw [hEv, h38, h1, h20, h21] at hRec; contradiction
              | none =>
                cases h40 : findBodyBySym allBodies 40 with
                | some _ => rw [hEv, h38, h1, h20, h21, h40] at hRec; contradiction
                | none =>
                  rw [hEv, h38, h1, h20, h21, h40] at hRec
                  dsimp only at hRec
                  cases hAl : extractConstFromAlignBody bAlign with
                  | none => rw [hAl] at hRec; contradiction
                  | some align0 =>
                    rw [hAl] at hRec
                    dsimp only at hRec
                    cases hCond :
                        (b == mkCanonicalStepSlotBody b.bodyId evTag0 &&
                         bAlign == mkCanonicalAlignOfBody bAlign.bodyId align0 &&
                         bRec == body_D_1_0) with
                    | false =>
                        rw [hCond] at hRec
                        contradiction
                    | true =>
                        rw [hCond] at hRec
                        dsimp only [Bool.cond_true] at hRec
                        injection hRec with hViewEq
                        injection hViewEq with _ _ hAlignEq hEvEq
                        subst hAlignEq
                        subst hEvEq
                        simp only [Bool.and_eq_true, beq_iff_eq] at hCond
                        rcases hCond with ⟨⟨hbEq, hbAlignEq⟩, hbRecEq⟩
                        have hFind63' : findBodyBySym allBodies 63 = some (mkCanonicalStepSlotBody b.bodyId evTag0) := by
                          rw [hFind63, ← hbEq]
                        have hFind38' : findBodyBySym allBodies 38 = some (mkCanonicalAlignOfBody bAlign.bodyId align0) := by
                          rw [h38, ← hbAlignEq]
                        have hFind1' : findBodyBySym allBodies 1 = some body_D_1_0 := by
                          rw [h1, ← hbRecEq]
                        intro ptrValid base
                        dsimp only [evalStepGenericSlot, evalStepGenericSlotWithFuel, evalVerifiedStructuredView]
                        cases ptrValid
                        · rw [runSteps_GEN_false allBodies b.bodyId evTag0 base hFind63']
                          rfl
                        · rw [runSteps_GEN_full allBodies b.bodyId bAlign.bodyId align0 evTag0 base hFind63' hFind38' hFind1' h20 h21 h40]
                          dsimp only [st_GEN_9]
                          have h1Mod : (0 + 1) % u32Mod = 1 := rfl
                          have h0Mul : (0 * 16) % u32Mod = 0 := rfl
                          rw [h1Mod, h0Mul]
                          rfl

def bb1_CLIENT_66 (addK : Nat) : WireBlock :=
  { isCleanup := false
  , stmts :=
      [ .storageDead 7
      , .storageDead 6
      , .storageDead 5
      , .storageLive 8
      , .assignUseRetagYes { localIdx := 8, proj := .here } (.copy { localIdx := 4, proj := .here }) ]
  , term :=
      .call2 40 { localIdx := 0, proj := .here } (some 2) .continueUnwind
        (.move { localIdx := 8, proj := .here }) (.constUsize addK) }

def bb2_CLIENT_66 : WireBlock :=
  { isCleanup := false
  , stmts := [ .storageDead 8, .storageDead 4 ]
  , term := .ret }

def st_CLIENT_1 (bId align0 evTag0 addK0 base : Nat) : ExecState :=
  { status := .running
  , stack :=
      [ { symId := 66
        , localTypes := (mkCanonicalClientContractBody bId addK0).localTypes
        , bodyBlocks := (mkCanonicalClientContractBody bId addK0).blocks
        , bbIdx := 1
        , remStmts := (bb1_CLIENT_66 addK0).stmts
        , curTerm := (bb1_CLIENT_66 addK0).term
        , locals :=
            [ (0, .agg0 1)
            , (1, .heapPtr 0)
            , (2, .extPtr true)
            , (3, .scalar base)
            , (4, .scalar ((base + align0) % usizeMod))
            , (5, .heapPtr 0)
            , (6, .extPtr true)
            , (7, .scalar base) ]
        , pending := none } ]
  , heap := [{ stepCount := (0 + 1) % u32Mod, traceAcc := ((0 * 16) % u32Mod + evTag0) % u32Mod }]
  , obsEvents := [evTag0] }

def st_CLIENT_2 (bId align0 evTag0 addK0 base : Nat) : ExecState :=
  { status := .running
  , stack :=
      [ { symId := 66
        , localTypes := (mkCanonicalClientContractBody bId addK0).localTypes
        , bodyBlocks := (mkCanonicalClientContractBody bId addK0).blocks
        , bbIdx := 2
        , remStmts := bb2_CLIENT_66.stmts
        , curTerm := bb2_CLIENT_66.term
        , locals :=
            [ (0, .scalar ((((base + align0) % usizeMod) + addK0) % usizeMod))
            , (1, .heapPtr 0)
            , (2, .extPtr true)
            , (3, .scalar base)
            , (4, .scalar ((base + align0) % usizeMod))
            , (8, .scalar ((base + align0) % usizeMod)) ]
        , pending := none } ]
  , heap := [{ stepCount := (0 + 1) % u32Mod, traceAcc := ((0 * 16) % u32Mod + evTag0) % u32Mod }]
  , obsEvents := [evTag0] }

def st_CLIENT_3 (align0 evTag0 addK0 base : Nat) : ExecState :=
  { status := .returned (.scalar ((((base + align0) % usizeMod) + addK0) % usizeMod))
  , stack := []
  , heap := [{ stepCount := (0 + 1) % u32Mod, traceAcc := ((0 * 16) % u32Mod + evTag0) % u32Mod }]
  , obsEvents := [evTag0] }

theorem step_CLIENT_1_to_2
    (allBodies : List WireBody) (bId align0 evTag0 addK0 base : Nat)
    (hFind40 : findBodyBySym allBodies 40 = none) :
    stepState allBodies (st_CLIENT_1 bId align0 evTag0 addK0 base) =
      st_CLIENT_2 bId align0 evTag0 addK0 base := by
  dsimp only [st_CLIENT_1, stepState, execBlockStmts, bb1_CLIENT_66, stepStmt, evalOperand,
    readPlace, writePlace, setLocal, getLocal, eraseLocal, stepTerm, dispatchCall, evalOperandList]
  rw [hFind40]
  rfl

theorem step_CLIENT_2_to_3
    (allBodies : List WireBody) (bId align0 evTag0 addK0 base : Nat) :
    stepState allBodies (st_CLIENT_2 bId align0 evTag0 addK0 base) =
      st_CLIENT_3 align0 evTag0 addK0 base := by
  rfl

theorem runSteps_CLIENT_from_1
    (allBodies : List WireBody) (bId align0 evTag0 addK0 base : Nat)
    (hFind40 : findBodyBySym allBodies 40 = none) :
    runSteps allBodies 3 (st_CLIENT_1 bId align0 evTag0 addK0 base) =
      st_CLIENT_3 align0 evTag0 addK0 base := by
  change runSteps allBodies 2 (stepState allBodies (st_CLIENT_1 bId align0 evTag0 addK0 base)) = _
  rw [step_CLIENT_1_to_2 allBodies bId align0 evTag0 addK0 base hFind40]
  change runSteps allBodies 1 (stepState allBodies (st_CLIENT_2 bId align0 evTag0 addK0 base)) = _
  rw [step_CLIENT_2_to_3 allBodies bId align0 evTag0 addK0 base]
  rfl

noncomputable def st_CLIENT_0 (bId addK : Nat) (ptrValid : Bool) (base : Nat) : ExecState :=
  let body := mkCanonicalClientContractBody bId addK
  match getBlockAt body.blocks 0 with
  | none => { status := .stuck, stack := [], heap := [{ stepCount := 0, traceAcc := 0 }], obsEvents := [] }
  | some blk0 =>
      { status := .running
      , stack := [{ symId := 66, localTypes := body.localTypes, bodyBlocks := body.blocks, bbIdx := 0, remStmts := blk0.stmts, curTerm := blk0.term, locals := buildCalleeLocals [.heapPtr 0, .extPtr ptrValid, .scalar base], pending := none }]
      , heap := [{ stepCount := 0, traceAcc := 0 }], obsEvents := [] }

theorem initEntryStateWithHeap_CLIENT
    (allBodies : List WireBody) (bId addK : Nat) (ptrValid : Bool) (base : Nat)
    (hFind66 : findBodyBySym allBodies 66 = some (mkCanonicalClientContractBody bId addK)) :
    initEntryStateWithHeap allBodies 66 [.heapPtr 0, .extPtr ptrValid, .scalar base] [{ stepCount := 0, traceAcc := 0 }] =
      st_CLIENT_0 bId addK ptrValid base := by
  unfold initEntryStateWithHeap st_CLIENT_0
  rw [hFind66]
  rfl

theorem step_CLIENT_0_false
    (allBodies : List WireBody) (bId align0 evTag0 addK0 base : Nat)
    (calleeOracle : Bool → Nat → ExecStatus × HeapLogSlot × List Nat)
    (hOr : calleeOracle false base =
      evalVerifiedStructuredView (.checkPtrAndStepSlotWithAlign 2 3 align0 evTag0) 0 0 false base) :
    stepStateWithCallee63Oracle allBodies calleeOracle (st_CLIENT_0 bId addK0 false base) =
      { status := .ub
      , stack :=
          [ { symId := 66
            , localTypes := (mkCanonicalClientContractBody bId addK0).localTypes
            , bodyBlocks := (mkCanonicalClientContractBody bId addK0).blocks
            , bbIdx := 0
            , remStmts := []
            , curTerm :=
                WireTerm.call3 63 { localIdx := 4, proj := .here } (some 1) .continueUnwind
                  (.move { localIdx := 5, proj := .here })
                  (.move { localIdx := 6, proj := .here })
                  (.move { localIdx := 7, proj := .here })
            , locals := [(0, .agg0 1), (1, .heapPtr 0), (2, .extPtr false), (3, .scalar base), (5, .heapPtr 0), (6, .extPtr false), (7, .scalar base)]
            , pending := none } ]
      , heap := [{ stepCount := 0, traceAcc := 0 }]
      , obsEvents := [] } := by
  change stepStateWithCallee63Oracle allBodies (fun _ _ => calleeOracle false base) (st_CLIENT_0 bId addK0 false base) = _
  rw [hOr]
  rfl

theorem step_CLIENT_0_true
    (allBodies : List WireBody) (bId align0 evTag0 addK0 base : Nat)
    (calleeOracle : Bool → Nat → ExecStatus × HeapLogSlot × List Nat)
    (hOr : calleeOracle true base =
      evalVerifiedStructuredView (.checkPtrAndStepSlotWithAlign 2 3 align0 evTag0) 0 0 true base) :
    stepStateWithCallee63Oracle allBodies calleeOracle (st_CLIENT_0 bId addK0 true base) =
      st_CLIENT_1 bId align0 evTag0 addK0 base := by
  change stepStateWithCallee63Oracle allBodies (fun _ _ => calleeOracle true base) (st_CLIENT_0 bId addK0 true base) = _
  rw [hOr]
  rfl

theorem reconstructStepSlotViewInEnv_inversion
    (allBodies : List WireBody) (bStep : WireBody) (align0 evTag0 : Nat)
    (h3 : reconstructStepSlotViewInEnv allBodies bStep = some (align0, evTag0)) :
    (bStep.symId == 63) = true ∧ findBodyBySym allBodies 40 = none := by
  unfold reconstructStepSlotViewInEnv at h3
  cases hEv : extractEventTagFromBlock1 bStep with
  | none => rw [hEv] at h3; contradiction
  | some ev0 =>
    cases h38 : findBodyBySym allBodies 38 with
    | none => rw [hEv, h38] at h3; contradiction
    | some bAlign =>
      cases h1' : findBodyBySym allBodies 1 with
      | none => rw [hEv, h38, h1'] at h3; contradiction
      | some bRec =>
        cases h20 : findBodyBySym allBodies 20 with
        | some _ => rw [hEv, h38, h1', h20] at h3; contradiction
        | none =>
          cases h21 : findBodyBySym allBodies 21 with
          | some _ => rw [hEv, h38, h1', h20, h21] at h3; contradiction
          | none =>
            cases h40 : findBodyBySym allBodies 40 with
            | some _ => rw [hEv, h38, h1', h20, h21, h40] at h3; contradiction
            | none =>
              rw [hEv, h38, h1', h20, h21, h40] at h3
              dsimp only at h3
              cases hAl : extractConstFromAlignBody bAlign with
              | none => rw [hAl] at h3; contradiction
              | some a0 =>
                rw [hAl] at h3
                dsimp only at h3
                cases hCond :
                    (bStep == mkCanonicalStepSlotBody bStep.bodyId ev0 &&
                     bAlign == mkCanonicalAlignOfBody bAlign.bodyId a0 &&
                     bRec == body_D_1_0) with
                | false => rw [hCond] at h3; contradiction
                | true =>
                    simp only [Bool.and_eq_true, beq_iff_eq] at hCond
                    rcases hCond with ⟨⟨hbStepEq, _⟩, _⟩
                    refine ⟨?_, rfl⟩
                    rw [hbStepEq]
                    rfl

/-- **General Acceptance-Implies-Correspondence Theorem for `client_contract_entry` (`symId = 66`, `R8` / `U5`)**:
    For **any** `allBodies : List WireBody`, **any** `b : WireBody`, and **any** `alignConst evTag addK : Nat`,
    if `findBodyBySym allBodies 66 = some b` and `reconstructVerifiedStructuredViewInEnv allBodies b`
    returns `some (.callStepSlotAndAddConstWithEnv 3 alignConst evTag addK)`, then for **all**
    `ptrValid : Bool` and **all** `base : Nat`, executing `b` via `evalClientEntryOperationalWithCalleeOracle`
    over `evalStepGenericSlot allBodies 0 0` matches `evalVerifiedStructuredView`! -/
theorem reconstructVerifiedStructuredViewInEnv_general_client_contract_sound
    (allBodies : List WireBody) (b : WireBody) (alignConst evTag addK : Nat)
    (hFind66 : findBodyBySym allBodies 66 = some b)
    (hRec : reconstructVerifiedStructuredViewInEnv allBodies b =
      some (.callStepSlotAndAddConstWithEnv 3 alignConst evTag addK)) :
    ∀ ptrValid : Bool, ∀ base : Nat,
      evalClientEntryOperationalWithCalleeOracle allBodies 4
        (evalStepGenericSlot allBodies 0 0) ptrValid base =
        let (st, slot, _) :=
          evalVerifiedStructuredView (.callStepSlotAndAddConstWithEnv 3 alignConst evTag addK) 0 0 ptrValid base
        (st, slot.stepCount) := by
  unfold reconstructVerifiedStructuredViewInEnv at hRec
  cases hBeq63 : (b.symId == 63) with
  | true =>
      rw [hBeq63] at hRec
      dsimp only [Bool.cond_true] at hRec
      cases hStep : reconstructStepSlotViewInEnv allBodies b with
      | none => rw [hStep] at hRec; contradiction
      | some p =>
          rcases p with ⟨al, ev⟩
          rw [hStep] at hRec
          dsimp only at hRec
          injection hRec with hViewEq
          contradiction
  | false =>
      rw [hBeq63] at hRec
      dsimp only [Bool.cond_false] at hRec
      cases hBeq66 : (b.symId == 66) with
      | false =>
          rw [hBeq66] at hRec
          contradiction
      | true =>
          rw [hBeq66] at hRec
          dsimp only [Bool.cond_true] at hRec
          cases h1 : extractAddConstFromClientBlock1 b with
          | none => rw [h1] at hRec; contradiction
          | some addK0 =>
            cases h2 : findBodyBySym allBodies 63 with
            | none => rw [h1, h2] at hRec; contradiction
            | some bStep =>
              rw [h1, h2] at hRec
              dsimp only at hRec
              cases h3 : reconstructStepSlotViewInEnv allBodies bStep with
              | none =>
                  rw [h3] at hRec
                  contradiction
              | some p =>
                  rcases p with ⟨align0, evTag0⟩
                  rw [h3] at hRec
                  dsimp only at hRec
                  cases hEqC : (b == mkCanonicalClientContractBody b.bodyId addK0) with
                  | false =>
                      rw [hEqC] at hRec
                      contradiction
                  | true =>
                      rw [hEqC] at hRec
                      dsimp only [Bool.cond_true] at hRec
                      injection hRec with hViewEq
                      injection hViewEq with _ hAlignEq hEvEq hAddEq
                      subst hAlignEq
                      subst hEvEq
                      subst hAddEq
                      have hEqC' : b = mkCanonicalClientContractBody b.bodyId addK0 :=
                        beq_iff_eq.mp hEqC
                      have ⟨hStepSym63, hFind40⟩ :=
                        reconstructStepSlotViewInEnv_inversion allBodies bStep align0 evTag0 h3
                      have hStepRec :
                          reconstructVerifiedStructuredViewInEnv allBodies bStep =
                            some (.checkPtrAndStepSlotWithAlign 2 3 align0 evTag0) := by
                        unfold reconstructVerifiedStructuredViewInEnv
                        rw [hStepSym63, Bool.cond_true, h3]
                      have hStepSound :=
                        reconstructVerifiedStructuredViewInEnv_general_step_slot_sound
                          allBodies bStep align0 evTag0 h2 hStepRec
                      have hFind66' : findBodyBySym allBodies 66 = some (mkCanonicalClientContractBody b.bodyId addK0) := by
                        rw [hFind66, ← hEqC']
                      generalize hOr : evalStepGenericSlot allBodies 0 0 = calleeOracle at hStepSound ⊢
                      intro ptrValid base
                      unfold evalClientEntryOperationalWithCalleeOracle
                      rw [initEntryStateWithHeap_CLIENT allBodies b.bodyId addK0 ptrValid base hFind66']
                      cases ptrValid
                      · dsimp only
                        rw [step_CLIENT_0_false allBodies b.bodyId align0 evTag0 addK0 base calleeOracle (hStepSound false base)]
                        rfl
                      · dsimp only
                        rw [step_CLIENT_0_true allBodies b.bodyId align0 evTag0 addK0 base calleeOracle (hStepSound true base)]
                        rw [runSteps_CLIENT_from_1 allBodies b.bodyId align0 evTag0 addK0 base hFind40]
                        rfl

/-! ## 4. `Q2` (`F2`, `#93` §7): Full-Range Layout Entry Admission & Complete Multi-Limb Encoding -/

def maxLayoutFieldRangeQ2 : Nat := 65536

/-- Full-range layout entry admissibility check (`Q2` / `F2`, `#93` §7):
    Rejects zero or out-of-range (`≥ 65536`) `sizeBytes` or `alignBytes` before accepting the
    2-byte layout payload encoding, and enforces exact round-trip reconstruction from the encoded
    low/high bytes so that no high bits can be silently truncated before fingerprinting. -/
def checkLayoutEntryInRangeQ2 (e : CompilerTypeLayoutEntry) : Bool :=
  (0 < e.sizeBytes) && (e.sizeBytes < maxLayoutFieldRangeQ2) &&
  (0 < e.alignBytes) && (e.alignBytes < maxLayoutFieldRangeQ2) &&
  ((e.sizeBytes % 256) + ((e.sizeBytes / 256) % 256) * 256 == e.sizeBytes) &&
  ((e.alignBytes % 256) + ((e.alignBytes / 256) % 256) * 256 == e.alignBytes)

def checkLayoutEntriesInSupportedRangeQ2 (entries : List CompilerTypeLayoutEntry) : Bool :=
  !entries.isEmpty && entries.all checkLayoutEntryInRangeQ2

/-- Multi-limb layout entry encoding that preserves high limb words (`n / 65536`) explicitly. -/
def encodeLayoutEntryFullRangeBytesQ2 (e : CompilerTypeLayoutEntry) : List Nat :=
  [ specEncodeTypeTag e.typeTag
  , e.sizeBytes / 65536
  , (e.sizeBytes / 256) % 256
  , e.sizeBytes % 256
  , e.alignBytes / 65536
  , (e.alignBytes / 256) % 256
  , e.alignBytes % 256 ]

def encodeLayoutEntriesFullRangePayloadQ2 : List CompilerTypeLayoutEntry → List Nat
  | [] => [0]
  | e :: es => encodeLayoutEntryFullRangeBytesQ2 e ++ encodeLayoutEntriesFullRangePayloadQ2 es

/-- Repaired full-range layout-table binding check (`Q2` / `F2`, `#93` §7):
    Enforces `checkLayoutEntriesInSupportedRangeQ2 tbl.entries` prior to `checkLayoutTableBindingWithEntries`,
    ensuring that every accepted layout entry lies in `1..65535` where `encodeLayoutEntryBytes` is injective. -/
def checkLayoutTableBindingFullRangeQ2
    (ctx : ExpectedCargoInvocationContext)
    (expectedCrateBytes : List Nat)
    (expectedTargetTripleBytes : List Nat)
    (expectedEntriesFp16 : Nat × Nat)
    (tbl : BoundCompilerLayoutTable)
    (targetTripleBytes : List Nat) : Bool :=
  checkLayoutEntriesInSupportedRangeQ2 tbl.entries &&
  checkLayoutTableBindingWithEntries ctx expectedCrateBytes expectedTargetTripleBytes
    expectedEntriesFp16 tbl targetTripleBytes

def deriveLayoutCalleeBodiesCheckedQ2
    (ctx : ExpectedCargoInvocationContext)
    (expectedCrateBytes : List Nat)
    (expectedTargetTripleBytes : List Nat)
    (expectedEntriesFp16 : Nat × Nat)
    (tbl : BoundCompilerLayoutTable)
    (targetTripleBytes : List Nat)
    (typeTag : MirTypeTag) : List WireBody :=
  bif checkLayoutTableBindingFullRangeQ2 ctx expectedCrateBytes expectedTargetTripleBytes
        expectedEntriesFp16 tbl targetTripleBytes then
    deriveLayoutCalleeBodies ctx expectedCrateBytes tbl typeTag
  else
    []

/-- **Accepted Layout Encoding Faithfulness Theorem (`Q2` / `F2`, `#93` §7)**:
    For any two layout entries `e1, e2` accepted by `checkLayoutEntryInRangeQ2`, equality of their
    serialized bytes `encodeLayoutEntryBytes e1 = encodeLayoutEntryBytes e2` implies exact equality
    of all consumed numeric fields (`sizeBytes` and `alignBytes`) and encoded type tags. -/
theorem encodeLayoutEntryBytes_preserves_size_and_align_when_in_range_q2
    (e1 e2 : CompilerTypeLayoutEntry)
    (hRange1 : checkLayoutEntryInRangeQ2 e1 = true)
    (hRange2 : checkLayoutEntryInRangeQ2 e2 = true)
    (hEncEq : encodeLayoutEntryBytes e1 = encodeLayoutEntryBytes e2) :
    specEncodeTypeTag e1.typeTag = specEncodeTypeTag e2.typeTag ∧
    e1.sizeBytes = e2.sizeBytes ∧
    e1.alignBytes = e2.alignBytes := by
  unfold checkLayoutEntryInRangeQ2 at hRange1 hRange2
  simp only [Bool.and_eq_true, beq_iff_eq] at hRange1 hRange2
  rcases hRange1 with ⟨⟨_, hSizeRec1⟩, hAlignRec1⟩
  rcases hRange2 with ⟨⟨_, hSizeRec2⟩, hAlignRec2⟩
  unfold encodeLayoutEntryBytes at hEncEq
  injection hEncEq with hTag hTail1
  injection hTail1 with hSizeLo hTail2
  injection hTail2 with hSizeHi hTail3
  injection hTail3 with hAlignLo hTail4
  injection hTail4 with hAlignHi _
  refine ⟨hTag, ?_, ?_⟩
  · rw [← hSizeRec1, ← hSizeRec2, hSizeLo, hSizeHi]
  · rw [← hAlignRec1, ← hAlignRec2, hAlignLo, hAlignHi]

def aliasedSizeLayoutQ2 : BoundCompilerLayoutTable :=
  { statefulGenericLibLayoutTable with entries :=
    statefulGenericLibLayoutTable.entries.map (fun e =>
      if e.typeTag == .u32 then { e with sizeBytes := e.sizeBytes + 65536 } else e) }

def aliasedAlignLayoutQ2 : BoundCompilerLayoutTable :=
  { statefulGenericLibLayoutTable with entries :=
    statefulGenericLibLayoutTable.entries.map (fun e =>
      if e.typeTag == .u32 then { e with alignBytes := e.alignBytes + 65536 } else e) }

def zeroAlignLayoutQ2 : BoundCompilerLayoutTable :=
  { statefulGenericLibLayoutTable with entries :=
    statefulGenericLibLayoutTable.entries.map (fun e =>
      if e.typeTag == .u32 then { e with alignBytes := 0 } else e) }

def boundaryAdmissibleLayoutEntryQ2 : CompilerTypeLayoutEntry :=
  { typeTag := .u32, typeName := "u32", sizeBytes := 65535, alignBytes := 32768 }

theorem q2_full_range_layout_binding_controls_verified :
    checkLayoutTableBindingFullRangeQ2 statefulGenericLibExpectedCtx
      statefulGenericLibCrateBytes x86_64LinuxTargetTripleBytes
      statefulGenericLibEntriesFp16 statefulGenericLibLayoutTable x86_64LinuxTargetTripleBytes = true ∧
    checkLayoutTableBindingFullRangeQ2 statefulGenericLibExpectedCtx
      statefulGenericLibCrateBytes x86_64LinuxTargetTripleBytes
      statefulGenericLibEntriesFp16 aliasedSizeLayoutQ2 x86_64LinuxTargetTripleBytes = false ∧
    checkLayoutTableBindingFullRangeQ2 statefulGenericLibExpectedCtx
      statefulGenericLibCrateBytes x86_64LinuxTargetTripleBytes
      statefulGenericLibEntriesFp16 aliasedAlignLayoutQ2 x86_64LinuxTargetTripleBytes = false ∧
    checkLayoutTableBindingFullRangeQ2 statefulGenericLibExpectedCtx
      statefulGenericLibCrateBytes x86_64LinuxTargetTripleBytes
      statefulGenericLibEntriesFp16 zeroAlignLayoutQ2 x86_64LinuxTargetTripleBytes = false ∧
    checkLayoutTableBindingFullRangeQ2 statefulGenericLibExpectedCtx
      statefulGenericLibCrateBytes x86_64LinuxTargetTripleBytes
      statefulGenericLibEntriesFp16 statefulGenericLibLayoutTable aarch64DarwinTargetTripleBytes = false ∧
    encodeLayoutEntriesFullRangePayloadQ2 aliasedSizeLayoutQ2.entries ≠
      encodeLayoutEntriesFullRangePayloadQ2 statefulGenericLibLayoutTable.entries ∧
    checkLayoutEntryInRangeQ2 boundaryAdmissibleLayoutEntryQ2 = true := by
  decide

/-! ## 5. `Q1` (`F1`, `#93` §6): Full Acceptance Boundary for the Public Two-Sided Lowering Validator -/

/-- Repaired behavioral check using `deriveLayoutCalleeBodiesCheckedQ2` (`Q1` & `Q2`). -/
def checkBuiltToPostCleanupBehavioralEquivFullRangeQ1
    (policy : UbPrefixObservationPolicy)
    (expectedCtx : ExpectedCargoInvocationContext)
    (crateNameBytes : List Nat)
    (expectedTargetTripleBytes : List Nat)
    (expectedEntriesFp16 : Nat × Nat)
    (layoutTbl : BoundCompilerLayoutTable)
    (targetTripleBytes : List Nat)
    (builtRawBodies postRawBodies : List WireBody) : Bool :=
  let layoutBodies :=
    deriveLayoutCalleeBodiesCheckedQ2 expectedCtx crateNameBytes expectedTargetTripleBytes
      expectedEntriesFp16 layoutTbl targetTripleBytes .u32
  let builtBodies := builtRawBodies ++ layoutBodies
  let postBodies := postRawBodies ++ layoutBodies
  (layoutBodies.length == 2) &&
  checkRuntimeClosedBodies builtBodies &&
  checkRuntimeClosedBodies postBodies &&
  checkUbInvalidPtrEquivUnderPolicy policy
    (evalBuiltStepGenericSlotFromGraph builtBodies 0 0 false 16)
    (evalStepGenericSlot postBodies 0 0 false 16) &&
  (evalBuiltStepGenericSlotFromGraph builtBodies 0 0 true 16 ==
    (.returned (.scalar 20), { stepCount := 1, traceAcc := 4 }, [4])) &&
  (evalStepGenericSlot postBodies 0 0 true 16 ==
    (.returned (.scalar 20), { stepCount := 1, traceAcc := 4 }, [4])) &&
  (evalBuiltTransactionalStepFromGraph builtBodies false ==
    .normalReturn 105 (1, 1) (1, 2) [2, 1]) &&
  (evalPostCleanupTransactionalStep postBodies false ==
    .normalReturn 105 (1, 1) (1, 2) [2, 1]) &&
  (evalBuiltTransactionalStepFromGraph builtBodies true ==
    .unwoundWithCleanup (2, 161) (1, 2) [10, 1, 2]) &&
  (evalPostCleanupTransactionalStep postBodies true ==
    .unwoundWithCleanup (2, 161) (1, 2) [10, 1, 2])

/-- **Repaired Public Two-Sided Lowering Validator (`validateBuiltToPostCleanupAdmittedQ1`, `Q1` / `F1` & `Q2` / `F2`)**:
    Enforces full package admission (`isAdmittedPackageBytes` — verifying canonical wire framing,
    unique symbol IDs, callee/drop-glue closure, and property-specific `checkBodiesPhaseConsistent`
    phase invariants on BOTH input byte streams) AND full-range layout binding
    (`checkLayoutTableBindingFullRangeQ2`) BEFORE any interpretation or companion augmentation. -/
def validateBuiltToPostCleanupAdmittedQ1
    (policy : UbPrefixObservationPolicy)
    (expectedCtx : ExpectedCargoInvocationContext)
    (builtBindingRec postCleanupBindingRec : CargoInvocationBindingRecord)
    (crateNameBytes expectedTargetTripleBytes : List Nat)
    (expectedEntriesFp16 : Nat × Nat)
    (builtPkgBytes postCleanupPkgBytes : List Nat)
    (layoutTbl : BoundCompilerLayoutTable)
    (targetTripleBytes : List Nat) : Bool :=
  isAdmittedPackageBytes builtPkgBytes &&
  isAdmittedPackageBytes postCleanupPkgBytes &&
  checkTwoPhaseCompilationIdentity expectedCtx builtBindingRec postCleanupBindingRec
    crateNameBytes builtPkgBytes postCleanupPkgBytes layoutTbl &&
  checkLayoutTableBindingFullRangeQ2 expectedCtx crateNameBytes expectedTargetTripleBytes
    expectedEntriesFp16 layoutTbl targetTripleBytes &&
  match parseRawPackageBytes postCleanupPkgBytes with
  | .ok (postPkg, []) =>
      bif checkPostCleanupPackageStructure postPkg then
        match parseRawPackageBytes builtPkgBytes with
        | .ok (builtPkg, []) =>
            checkBuiltPackageStructure builtPkg &&
            checkBuiltToPostCleanupBehavioralEquivFullRangeQ1 policy expectedCtx crateNameBytes
              expectedTargetTripleBytes expectedEntriesFp16 layoutTbl targetTripleBytes
              builtPkg.bodies postPkg.bodies
        | _ => false
      else false
  | _ => false

/-- **Full-Range Behavioral Equivalence Soundness Theorem (`Q1` & `Q2`)**:
    Whenever `checkBuiltToPostCleanupBehavioralEquivFullRangeQ1 .strictPrefixTracePreserving`
    returns `true`, `checkLayoutTableBindingFullRangeQ2` holds, `layoutBodies.length = 2`,
    both augmented body sets are runtime-closed, both invalid-pointer executions halt at `.ub`
    with empty pre-UB side-effect traces `({0, 0}, [])`, and all three valid-input executions
    agree between `MirPhase::Built` and `Runtime(PostCleanup)`. -/
theorem checkBuiltToPostCleanupBehavioralEquivFullRangeQ1_sound
    (expectedCtx : ExpectedCargoInvocationContext)
    (crateNameBytes expectedTargetTripleBytes : List Nat)
    (expectedEntriesFp16 : Nat × Nat)
    (layoutTbl : BoundCompilerLayoutTable)
    (targetTripleBytes : List Nat)
    (builtRawBodies postRawBodies : List WireBody)
    (hAccept :
      checkBuiltToPostCleanupBehavioralEquivFullRangeQ1
        .strictPrefixTracePreserving expectedCtx crateNameBytes expectedTargetTripleBytes
        expectedEntriesFp16 layoutTbl targetTripleBytes builtRawBodies postRawBodies = true) :
    let layoutBodies :=
      deriveLayoutCalleeBodiesCheckedQ2 expectedCtx crateNameBytes expectedTargetTripleBytes
        expectedEntriesFp16 layoutTbl targetTripleBytes .u32
    let builtBodies := builtRawBodies ++ layoutBodies
    let postBodies := postRawBodies ++ layoutBodies
    layoutBodies.length = 2 ∧
    checkRuntimeClosedBodies builtBodies = true ∧
    checkRuntimeClosedBodies postBodies = true ∧
    evalBuiltStepGenericSlotFromGraph builtBodies 0 0 false 16 =
      (.ub, { stepCount := 0, traceAcc := 0 }, []) ∧
    evalStepGenericSlot postBodies 0 0 false 16 =
      (.ub, { stepCount := 0, traceAcc := 0 }, []) ∧
    evalBuiltStepGenericSlotFromGraph builtBodies 0 0 true 16 =
      evalStepGenericSlot postBodies 0 0 true 16 ∧
    evalBuiltStepGenericSlotFromGraph builtBodies 0 0 true 16 =
      (.returned (.scalar 20), { stepCount := 1, traceAcc := 4 }, [4]) ∧
    evalBuiltTransactionalStepFromGraph builtBodies false =
      evalPostCleanupTransactionalStep postBodies false ∧
    evalBuiltTransactionalStepFromGraph builtBodies true =
      evalPostCleanupTransactionalStep postBodies true := by
  dsimp only
  unfold checkBuiltToPostCleanupBehavioralEquivFullRangeQ1 checkUbInvalidPtrEquivUnderPolicy at hAccept
  simp only [Bool.and_eq_true, beq_iff_eq] at hAccept
  rcases hAccept with ⟨⟨⟨⟨⟨⟨⟨⟨⟨hNonEmpty, hClosedBuilt⟩, hClosedPost⟩, ⟨hUbBuilt, hUbPost⟩⟩, hStepBuilt⟩, hStepPost⟩, hTransFalseBuilt⟩, hTransFalsePost⟩, hTransTrueBuilt⟩, hTransTruePost⟩
  refine ⟨hNonEmpty, hClosedBuilt, hClosedPost, hUbBuilt, hUbPost, ?_, hStepBuilt, ?_, ?_⟩
  · rw [hStepBuilt, hStepPost]
  · rw [hTransFalseBuilt, hTransFalsePost]
  · rw [hTransTrueBuilt, hTransTruePost]

/-- **Public-Entrypoint Acceptance Soundness Theorem (`validateBuiltToPostCleanupAdmittedQ1_sound`, `Q1` / `F1`, `#93` §6)**:
    Whenever the public entrypoint `validateBuiltToPostCleanupAdmittedQ1 .strictPrefixTracePreserving`
    returns `true`, BOTH exact byte packages satisfy full admission (`isAdmittedPackageBytes = true`),
    two-phase compilation identity holds (`checkTwoPhaseCompilationIdentity = true`), full-range
    layout binding holds (`checkLayoutTableBindingFullRangeQ2 = true`), and there exist decoded
    packages `builtPkg, postPkg` satisfying `checkBuiltPackageStructure`, `checkPostCleanupPackageStructure`,
    and the full behavioral observation relation `checkBuiltToPostCleanupBehavioralEquivFullRangeQ1`
    (which by `checkBuiltToPostCleanupBehavioralEquivFullRangeQ1_sound` guarantees runtime closure
    and finite endpoint/UB-prefix agreement). -/
theorem validateBuiltToPostCleanupAdmittedQ1_sound
    (expectedCtx : ExpectedCargoInvocationContext)
    (builtBindingRec postCleanupBindingRec : CargoInvocationBindingRecord)
    (crateNameBytes expectedTargetTripleBytes : List Nat)
    (expectedEntriesFp16 : Nat × Nat)
    (builtPkgBytes postCleanupPkgBytes : List Nat)
    (layoutTbl : BoundCompilerLayoutTable)
    (targetTripleBytes : List Nat)
    (hAccept :
      validateBuiltToPostCleanupAdmittedQ1
        .strictPrefixTracePreserving expectedCtx builtBindingRec postCleanupBindingRec
        crateNameBytes expectedTargetTripleBytes expectedEntriesFp16
        builtPkgBytes postCleanupPkgBytes layoutTbl targetTripleBytes = true) :
    isAdmittedPackageBytes builtPkgBytes = true ∧
    isAdmittedPackageBytes postCleanupPkgBytes = true ∧
    checkTwoPhaseCompilationIdentity expectedCtx builtBindingRec postCleanupBindingRec
      crateNameBytes builtPkgBytes postCleanupPkgBytes layoutTbl = true ∧
    checkLayoutTableBindingFullRangeQ2 expectedCtx crateNameBytes expectedTargetTripleBytes
      expectedEntriesFp16 layoutTbl targetTripleBytes = true ∧
    ∃ builtPkg postPkg : WirePackage,
      parseRawPackageBytes postCleanupPkgBytes = .ok (postPkg, []) ∧
      parseRawPackageBytes builtPkgBytes = .ok (builtPkg, []) ∧
      checkPostCleanupPackageStructure postPkg = true ∧
      checkBuiltPackageStructure builtPkg = true ∧
      let layoutBodies :=
        deriveLayoutCalleeBodiesCheckedQ2 expectedCtx crateNameBytes expectedTargetTripleBytes
          expectedEntriesFp16 layoutTbl targetTripleBytes .u32
      let builtBodies := builtPkg.bodies ++ layoutBodies
      let postBodies := postPkg.bodies ++ layoutBodies
      layoutBodies.length = 2 ∧
      checkRuntimeClosedBodies builtBodies = true ∧
      checkRuntimeClosedBodies postBodies = true ∧
      evalBuiltStepGenericSlotFromGraph builtBodies 0 0 false 16 =
        (.ub, { stepCount := 0, traceAcc := 0 }, []) ∧
      evalStepGenericSlot postBodies 0 0 false 16 =
        (.ub, { stepCount := 0, traceAcc := 0 }, []) ∧
      evalBuiltStepGenericSlotFromGraph builtBodies 0 0 true 16 =
        evalStepGenericSlot postBodies 0 0 true 16 ∧
      evalBuiltStepGenericSlotFromGraph builtBodies 0 0 true 16 =
        (.returned (.scalar 20), { stepCount := 1, traceAcc := 4 }, [4]) ∧
      evalBuiltTransactionalStepFromGraph builtBodies false =
        evalPostCleanupTransactionalStep postBodies false ∧
      evalBuiltTransactionalStepFromGraph builtBodies true =
        evalPostCleanupTransactionalStep postBodies true := by
  unfold validateBuiltToPostCleanupAdmittedQ1 at hAccept
  simp only [Bool.and_eq_true] at hAccept
  rcases hAccept with ⟨⟨⟨⟨hAdmBuilt, hAdmPost⟩, hId⟩, hLayout⟩, hParse⟩
  refine ⟨hAdmBuilt, hAdmPost, hId, hLayout, ?_⟩
  cases hPost : parseRawPackageBytes postCleanupPkgBytes with
  | error _ => rw [hPost] at hParse; contradiction
  | ok pPost =>
    rcases pPost with ⟨postPkg, postRem⟩
    cases postRem with
    | cons _ _ => rw [hPost] at hParse; contradiction
    | nil =>
      rw [hPost] at hParse
      dsimp only at hParse
      cases hPostStruct : checkPostCleanupPackageStructure postPkg with
      | false => rw [hPostStruct] at hParse; contradiction
      | true =>
        rw [hPostStruct] at hParse
        dsimp only [Bool.cond_true] at hParse
        cases hBuilt : parseRawPackageBytes builtPkgBytes with
        | error _ => rw [hBuilt] at hParse; contradiction
        | ok pBuilt =>
          rcases pBuilt with ⟨builtPkg, builtRem⟩
          cases builtRem with
          | cons _ _ => rw [hBuilt] at hParse; contradiction
          | nil =>
            rw [hBuilt] at hParse
            simp only [Bool.and_eq_true] at hParse
            rcases hParse with ⟨hBuiltStruct, hBehav⟩
            exact ⟨builtPkg, postPkg, rfl, rfl, hPostStruct, hBuiltStruct,
              checkBuiltToPostCleanupBehavioralEquivFullRangeQ1_sound
                expectedCtx crateNameBytes expectedTargetTripleBytes expectedEntriesFp16
                layoutTbl targetTripleBytes builtPkg.bodies postPkg.bodies hBehav⟩

theorem q1_admitted_validator_accepts_real_package :
    validateBuiltToPostCleanupAdmittedQ1
      .strictPrefixTracePreserving
      statefulGenericLibExpectedCtx
      statefulGenericLibBuiltBindingRec
      statefulGenericLibBindingRec
      statefulGenericLibCrateBytes
      x86_64LinuxTargetTripleBytes
      statefulGenericLibEntriesFp16
      realStatefulGenericLibBuiltAmirBytes
      realStatefulGenericLibAmirBytes
      statefulGenericLibLayoutTable
      x86_64LinuxTargetTripleBytes = true := by
  decide

/-! ## 6. `Q5` (`F5`, `#93` §10 & `#88`): Joined `R10` `(u32, u16, [u32])` Specimen, Universal Law, and Allocation-Footprint Boundaries -/

/-- Exact header field layouts `(size, align)` of the captured `R10` specimen
    `#[repr(C)] pub struct PacketWithTail { pub magic: u32, pub flags: u16, pub payload: [u32] }`
    from `r5_inner_lib.rs:58` (`out_r5_inner_lib_open_hash.json:24`). -/
def r10PacketWithTailHeaderFieldsQ5 : List (Nat × Nat) :=
  [(4, 4), (2, 2)]

/-- Target-bound slice metadata domain (`#93` §10): `8 + n * 4 ≤ isize::MAX` on 64-bit targets. -/
def maxTargetIsizeBytes64Q5 : Nat := 9223372036854775807

def checkR10SliceMetadataInTargetBoundQ5 (sliceLen : Nat) : Bool :=
  Nat.ble (8 + sliceLen * 4) maxTargetIsizeBytes64Q5

/-- **Universal `#[repr(C)]` Layout Law for the Captured `R10` `(u32, u16, [u32])` Specimen (`Q5` / `F5`, `#93` §10)**:
    For **every** slice element count `n : Nat`, the independent `#[repr(C)]` layout calculation
    on `r10PacketWithTailHeaderFieldsQ5` (`[(4, 4), (2, 2)]`) with `[u32]` tail (`(4, 4)`) yields
    header offsets `[0, 4]`, tail offset `8`, raw extent `8 + n * 4`, total aligned size `8 + n * 4`,
    and alignment `4`. -/
theorem q5_r10_packet_with_tail_repr_c_universal_law (n : Nat) :
    computeReprCStructAndSliceTailLayout r10PacketWithTailHeaderFieldsQ5 4 4 none n =
      some ([0, 4], 8, 8 + n * 4, 8 + n * 4, 4) := by
  have hAcc : accumReprCFields none r10PacketWithTailHeaderFieldsQ5 [] 0 1 = some ([0, 4], 6, 4) := rfl
  unfold computeReprCStructAndSliceTailLayout
  rw [hAcc]
  change some ([0, 4], 8, 8 + n * 4, alignUpTo (8 + n * 4) 4, 4) =
    some ([0, 4], 8, 8 + n * 4, 8 + n * 4, 4)
  unfold alignUpTo
  have hMod : (8 + n * 4) % 4 = 0 := by
    rw [Nat.add_mul_mod_self_right]
  rw [hMod]
  rfl

/-- **Universal `#[repr(C, packed(2))]` Layout Law for the `R10` `(u32, u16, [u32])` Specimen (`Q5` / `F5`, `#93` §10)**:
    For **every** slice element count `n : Nat`, capping field alignment at `2` eliminates the
    2-byte padding after `flags: u16`, yielding header offsets `[0, 4]`, tail offset `6`,
    raw extent `6 + n * 4`, total aligned size `6 + n * 4`, and alignment `2` (`18` at `n = 3`). -/
theorem q5_r10_packet_with_tail_packed2_universal_law (n : Nat) :
    computeReprCStructAndSliceTailLayout r10PacketWithTailHeaderFieldsQ5 4 4 (some 2) n =
      some ([0, 4], 6, 6 + n * 4, 6 + n * 4, 2) := by
  have hAcc : accumReprCFields (some 2) r10PacketWithTailHeaderFieldsQ5 [] 0 1 = some ([0, 4], 6, 2) := rfl
  unfold computeReprCStructAndSliceTailLayout
  rw [hAcc]
  change some ([0, 4], 6, 6 + n * 4, alignUpTo (6 + n * 4) 2, 2) =
    some ([0, 4], 6, 6 + n * 4, 6 + n * 4, 2)
  unfold alignUpTo
  have hMul : 6 + n * 4 = 6 + (n * 2) * 2 := by
    rw [Nat.mul_assoc]
  have hMod : (6 + n * 4) % 2 = 0 := by
    rw [hMul, Nat.add_mul_mod_self_right]
  rw [hMod]
  rfl

/-- Non-contiguous allocation-footprint separation witness (`#88#issuecomment-6244670828` & `#93` §10):
    In `PacketWithTail` (`(u32, u16, [u32])`, `#[repr(C)]`), the bounding extent for `n = 3` is `[0, 20)`,
    but byte offsets `6` and `7` lie in inter-field padding between `flags: u16` (`[4, 6)`) and
    `payload: [u32]` (`[8, 20)`). Bounding extent (`offset < 8 + n * 4`) therefore does NOT imply
    initialized field/element coverage (`isTypedFieldByteOffsetQ5`). -/
def isPacketWithTailTypedFieldByteOffsetQ5 (sliceLen byteOff : Nat) : Bool :=
  (byteOff < 4) ||
  ((4 ≤ byteOff) && (byteOff < 6)) ||
  ((8 ≤ byteOff) && (byteOff < 8 + sliceLen * 4))

theorem q5_r10_joined_specimen_and_footprint_boundaries_verified :
    computeReprCStructAndSliceTailLayout r10PacketWithTailHeaderFieldsQ5 4 4 none 0 =
      some ([0, 4], 8, 8, 8, 4) ∧
    computeReprCStructAndSliceTailLayout r10PacketWithTailHeaderFieldsQ5 4 4 none 3 =
      some ([0, 4], 8, 20, 20, 4) ∧
    computeReprCStructAndSliceTailLayout r10PacketWithTailHeaderFieldsQ5 4 4 (some 2) 3 =
      some ([0, 4], 6, 18, 18, 2) ∧
    checkR10SliceMetadataInTargetBoundQ5 3 = true ∧
    checkR10SliceMetadataInTargetBoundQ5 maxTargetIsizeBytes64Q5 = false ∧
    (6 < 20 ∧ isPacketWithTailTypedFieldByteOffsetQ5 3 6 = false) ∧
    (8 < 20 ∧ isPacketWithTailTypedFieldByteOffsetQ5 3 8 = true) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

#print axioms r7_repr_c_slice_tail_packet_layout_and_controls
#print axioms r2_fail_closed_two_sided_validator_accepts_real_package
#print axioms checkBuiltToPostCleanupBehavioralEquivFailClosed_sound
#print axioms reconstructVerifiedStructuredViewInEnv_general_step_slot_sound
#print axioms reconstructVerifiedStructuredViewInEnv_general_client_contract_sound
#print axioms encodeLayoutEntryBytes_preserves_size_and_align_when_in_range_q2
#print axioms q2_full_range_layout_binding_controls_verified
#print axioms validateBuiltToPostCleanupAdmittedQ1_sound
#print axioms q1_admitted_validator_accepts_real_package
#print axioms q5_r10_packet_with_tail_repr_c_universal_law
#print axioms q5_r10_packet_with_tail_packed2_universal_law
#print axioms q5_r10_joined_specimen_and_footprint_boundaries_verified

end AnnealResearch.PR86AuditRepairs
