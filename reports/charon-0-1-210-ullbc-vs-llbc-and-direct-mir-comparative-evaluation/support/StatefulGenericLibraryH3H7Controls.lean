import AnnealResearch.StatefulGenericLibraryH3H7

set_option maxRecDepth 131072
set_option maxHeartbeats 1600000

namespace AnnealResearch.StatefulGenericLibraryH3H7Controls

open AnnealResearch.SubstantiveMirByteParser
open AnnealResearch.SemanticVerticalSlice
open AnnealResearch.CargoWorkspaceIntegration
open AnnealResearch.StatefulGenericLibraryH3H7

/-!
# Negative & Positive Controls for `H3`, `N1`, `N2`, `N3`/`H4`/`H6`, and `N6`/`H5` (`joshlf/anneal#64` & `#68`)

1. **`H3` & `N1` Controls (`LIB-01`–`13`, `#68` §4.1 & §6 N1)**:
   - **Control H3.1 / N1.4 (Insufficiency of Published Contract Alone & Event `4 -> 9`)**:
     Constructs `altStatefulLibBodies` (recording private event tag `9` instead of `4` in `step_generic_slot`)
     and proves that it satisfies BOTH `PublishedStatefulLibContract` and the universal operational
     contract `PublishedStatefulLibContractOperational altStatefulLibBodies 12` (`∀ base : Nat`), while
     falsifying `client_direct_mir_inspector`'s omitted implementation theorem (`log1 = (2, 145) ≠ (2, 65)`
     and `obsEvents = [9, 2, 1] ≠ [4, 2, 1]`).
   - **Control H3.2 (Missing Non-Inline Dependency Body Fails Closed)**: Stripping non-inline
     `transactional_step` (`symId = 65`) from the dependency representation causes `checkBodiesClosure`
     to return `false` and `evalClientDirectMirInspector` to fail closed with `.failed (.missingBody 65)`.
   - **Control N1.1–N1.3 & N1.5 (Arithmetic Constant, Alignment Fact, Call Destination, & Missing-Callee Controls)**:
     Tests mutating the arithmetic constant (`addK = 8 -> 12`), mutating `alignOfU32` (`4 -> 8`) in
     `BoundCompilerLayoutTable`, mutating the call destination (`_4 -> _3`), and replacing `Call 1` with
     an unlinked callee `Call 99` while keeping the exact 4-block graph shape.
2. **`N2` Strongest-Flags Charon `0.1.210` Multi-Artifact Controls (`#68` §4.4 & §6 N2)**:
   - **Control N2.1 (Missing dependency body — single-crate `Opaque` ULLBC without multi-artifact linking)**:
     Rejected by `checkBodiesClosure = false` and fails closed with `.missingBody 63`.
   - **Control N2.2 (Wrong library revision / instance)**: Linking against an instance with `align = 8`
     (`u64`) instead of `4` (`u32`) changes normal return from `105` to `109`.
   - **Control N2.3 (Omitted cleanup on Charon ULLBC)**: Leaving drop flag `_19 = true` in `bb4` of
     Charon's `transactional_step` double-drops `g1` on unwind (`[4, 10, 1, 2, 1] ≠ [4, 10, 1, 2]`).
   - **Control N2.4 (Changed private event `4 -> 9` on Charon ULLBC)**: Preserves `stepCount = 1` and
     return value while changing `obsEvents` on `charonLinkedInspectorAndLibBodies` from `[4, 2, 1]` to `[9, 2, 1]`.
   - **Control N2.5 (Valid administrative change on Charon ULLBC)**: Inserting `StorageLive(18); StorageDead(18)`
     in `bb6` of `transactional_step` produces distinct bodies while preserving exact normal, unwind, and UB outcomes.
3. **`N3` & `H4`/`H6` Two-Sided `MirPhase::Built` to `Runtime(PostCleanup)` Lowering Controls (`#68` §4.2 & §6 N3)**:
   - **Control H6.1 (Structurally valid semantic omission)**: Passes `isAdmittedPackageBytes = true` and
     `checkBuiltToPostCleanupStructure = true`, rejected by `checkBuiltToPostCleanupBehavioralEquiv = false`.
   - **Control H6.2 & N3.4 (Wrong subject AND same-shaped wrong-configuration `Built`/`PostCleanup` pair)**:
     Using the actual captured `realStatefulGenericLibBuiltWrongCfgAmirBytes` (`791` B, same function IDs
     `[1, 2, 7, 24, 63, 65]` and block counts as `realStatefulGenericLibBuiltAmirBytes`, captured under
     `--cfg wrong_cfg_probe` without `-Z mir-preserve-ub`) and matching `controlN3PostCleanupWrongCfgBytes`,
     proves separately how Stage 1 (`checkTwoPhaseCompilationIdentity`), Stage 2 (`checkBuiltToPostCleanupStructure`),
     and Stage 3 (`checkBuiltToPostCleanupBehavioralEquiv`) reject identity/configuration mismatches vs
     semantic omissions.
   - **Control H6.3 (Deleted bad prefix)**: Replacing `PlaceMention((*_2))` with `StorageLive(4)` is
     rejected because `ptrValid = false` returns `.returned (.scalar 20)` instead of `.ub`.
   - **Control H6.4 (Valid alternative administrative lowering)**: Accepted by all 3 stages (`true`).
4. **`N6` Structured-Recognizer Counterexample & Verified Repair (`#68` §4.3 & §6 N6)**:
   - Preserves the exact counterexample showing that the old `reconstructStructuredView` returns the same
     `some (.checkPtrAndStepSlot 2 3 4)` on both `statefulGenericLibBodies` (`evTag = 4`) and
     `altStatefulLibBodies` (`evTag = 9`), and proves that `reconstructVerifiedStructuredView` extracts
     `some (.checkPtrAndStepSlot 2 3 9)` on `altStatefulLibBodies` and returns `none` when a statement or
     destination local is mutated.
-/

/-! ## 1. `H3` & `N1` Controls (`LIB-01`–`13`, `#68` §4.1 & §6 N1) -/

/-- Alternative library body list where `step_generic_slot` (`symId = 63`) records private tag `9`
    instead of `4` at `bb1`, preserving the published contract (`(base + 4) % usizeMod` and `stepCount = 1`)
    while altering the omitted implementation trace (`traceAcc` and `obsEvents`). -/
def mutateBlocksEventTagTo9 (blks : List WireBlock) : List WireBlock :=
  blks.map (fun blk =>
    match blk.term with
    | .call2 1 dst t uw op0 (.constU32 4) =>
        { blk with term := .call2 1 dst t uw op0 (.constU32 9) }
    | _ => blk)

def mutateStepGenericEventTagTo9 (b : WireBody) : WireBody :=
  if b.symId == 63 then
    { b with blocks := mutateBlocksEventTagTo9 b.blocks }
  else b

def altStatefulLibBodies : List WireBody :=
  statefulGenericLibBodiesVal.map mutateStepGenericEventTagTo9

def linkedInspectorAndAltLibBodies : List WireBody :=
  clientDirectMirInspectorBodies ++ altStatefulLibBodies

def blocks_ALT_63 : List WireBlock := mutateBlocksEventTagTo9 blocks_D_63_3
def body_ALT_63 : WireBody := { body_D_63_3 with blocks := blocks_ALT_63 }
def altStatefulLibBodiesVal : List WireBody :=
  [body_D_1_0, body_D_2_1, body_D_3_2, body_ALT_63, body_D_64_4, body_D_65_5, body_D_7_6, body_D_24_7, body_D_37_8, body_D_38_9]

theorem altStatefulLibBodies_eq : altStatefulLibBodies = altStatefulLibBodiesVal := rfl

noncomputable def st_ALT_3 (base : Nat) : ExecState :=
  { status := .running
  , stack :=
      [ { symId := 1
        , localTypes := [MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32]
        , bodyBlocks := blocks_D_1_0
        , bbIdx := 0
        , remStmts := [WireStmt.storageLive 3, WireStmt.storageLive 4, WireStmt.assignUseRetagYes { localIdx := 4, proj := ProjChain.here } (OperandSpec.copy { localIdx := 1, proj := ProjChain.derefField0 })]
        , curTerm := WireTerm.call2 20 { localIdx := 3, proj := ProjChain.here } (some 1) UnwindSpec.continueUnwind (OperandSpec.move { localIdx := 4, proj := ProjChain.here }) (OperandSpec.constU32 1)
        , locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.scalar 9)]
        , pending := none }
      , { symId := 63
        , localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.unit, MirTypeTag.usize, MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.usize, MirTypeTag.usize]
        , bodyBlocks := blocks_ALT_63
        , bbIdx := 1
        , remStmts := []
        , curTerm := WireTerm.call2 1 { localIdx := 6, proj := ProjChain.here } (some 2) UnwindSpec.continueUnwind (OperandSpec.move { localIdx := 7, proj := ProjChain.here }) (OperandSpec.constU32 9)
        , locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.extPtr true), (3, RtVal.scalar base), (5, RtVal.scalar 4), (7, RtVal.heapPtr 0)]
        , pending := some { retDst := { localIdx := 6, proj := ProjChain.here }, targetBbOpt := some 2, unwind := UnwindSpec.continueUnwind, isDropGlue := false } } ]
  , heap := [{ stepCount := 0, traceAcc := 0 }]
  , obsEvents := [9] }

noncomputable def st_ALT_6 (base : Nat) : ExecState :=
  { status := .running
  , stack :=
      [ { symId := 1
        , localTypes := [MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32, MirTypeTag.u32]
        , bodyBlocks := blocks_D_1_0
        , bbIdx := 3
        , remStmts := [WireStmt.storageDead 8, WireStmt.storageDead 6, WireStmt.assignUseRetagYes { localIdx := 1, proj := ProjChain.derefField1 } (OperandSpec.move { localIdx := 5, proj := ProjChain.here }), WireStmt.storageDead 5, WireStmt.assignUseRetagYes { localIdx := 0, proj := ProjChain.here } OperandSpec.constUnit]
        , curTerm := WireTerm.ret
        , locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.scalar 9), (5, RtVal.scalar 9), (6, RtVal.scalar 0), (8, RtVal.scalar 9)]
        , pending := none }
      , { symId := 63
        , localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.unit, MirTypeTag.usize, MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.usize, MirTypeTag.usize]
        , bodyBlocks := blocks_ALT_63
        , bbIdx := 1
        , remStmts := []
        , curTerm := WireTerm.call2 1 { localIdx := 6, proj := ProjChain.here } (some 2) UnwindSpec.continueUnwind (OperandSpec.move { localIdx := 7, proj := ProjChain.here }) (OperandSpec.constU32 9)
        , locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.extPtr true), (3, RtVal.scalar base), (5, RtVal.scalar 4), (7, RtVal.heapPtr 0)]
        , pending := some { retDst := { localIdx := 6, proj := ProjChain.here }, targetBbOpt := some 2, unwind := UnwindSpec.continueUnwind, isDropGlue := false } } ]
  , heap := [{ stepCount := 1, traceAcc := 0 }]
  , obsEvents := [9] }

noncomputable def st_ALT_7 (base : Nat) : ExecState :=
  { status := .running
  , stack :=
      [ { symId := 63
        , localTypes := [MirTypeTag.usize, MirTypeTag.refMutEffectLog, MirTypeTag.rawPtrU32, MirTypeTag.usize, MirTypeTag.unit, MirTypeTag.usize, MirTypeTag.unit, MirTypeTag.refMutEffectLog, MirTypeTag.usize, MirTypeTag.usize]
        , bodyBlocks := blocks_ALT_63
        , bbIdx := 2
        , remStmts := [WireStmt.storageDead 7, WireStmt.storageDead 6, WireStmt.storageLive 8, WireStmt.assignUseRetagYes { localIdx := 8, proj := ProjChain.here } (OperandSpec.copy { localIdx := 3, proj := ProjChain.here }), WireStmt.storageLive 9, WireStmt.assignUseRetagYes { localIdx := 9, proj := ProjChain.here } (OperandSpec.copy { localIdx := 5, proj := ProjChain.here })]
        , curTerm := WireTerm.call2 40 { localIdx := 0, proj := ProjChain.here } (some 3) UnwindSpec.continueUnwind (OperandSpec.move { localIdx := 8, proj := ProjChain.here }) (OperandSpec.move { localIdx := 9, proj := ProjChain.here })
        , locals := [(0, RtVal.agg0 1), (1, RtVal.heapPtr 0), (2, RtVal.extPtr true), (3, RtVal.scalar base), (5, RtVal.scalar 4), (6, RtVal.agg0 1), (7, RtVal.heapPtr 0)]
        , pending := none } ]
  , heap := [{ stepCount := 1, traceAcc := 9 }]
  , obsEvents := [9] }

noncomputable def st_ALT_9 (base : Nat) : ExecState :=
  { status := .returned (.scalar ((base + 4) % usizeMod))
  , stack := []
  , heap := [{ stepCount := 1, traceAcc := 9 }]
  , obsEvents := [9] }

theorem step_ALT_0_3 (base : Nat) :
    runSteps altStatefulLibBodiesVal 3 (initEntryStateWithHeap altStatefulLibBodiesVal 63 [.heapPtr 0, .extPtr true, .scalar base] [{ stepCount := 0, traceAcc := 0 }]) = st_ALT_3 base := rfl
theorem step_ALT_3_6 (base : Nat) : runSteps altStatefulLibBodiesVal 3 (st_ALT_3 base) = st_ALT_6 base := rfl
theorem step_ALT_6_7 (base : Nat) : runSteps altStatefulLibBodiesVal 1 (st_ALT_6 base) = st_ALT_7 base := rfl
theorem step_ALT_7_9 (base : Nat) : runSteps altStatefulLibBodiesVal 2 (st_ALT_7 base) = st_ALT_9 base := rfl
theorem step_ALT_9_12 (base : Nat) : runSteps altStatefulLibBodiesVal 3 (st_ALT_9 base) = st_ALT_9 base := rfl

theorem runSteps_ALT_full (base : Nat) :
    runSteps altStatefulLibBodiesVal 12 (initEntryStateWithHeap altStatefulLibBodiesVal 63 [.heapPtr 0, .extPtr true, .scalar base] [{ stepCount := 0, traceAcc := 0 }]) = st_ALT_9 base := by
  have hTot : (12 : Nat) = ((((3 + 3) + 1) + 2) + 3) := rfl
  rw [hTot, runSteps_split, runSteps_split, runSteps_split, runSteps_split, step_ALT_0_3, step_ALT_3_6, step_ALT_6_7, step_ALT_7_9, step_ALT_9_12]

/-- `altStatefulLibBodies` (mutating event `4 -> 9`) still satisfies the universal operational
    contract `PublishedStatefulLibContractOperational altStatefulLibBodies 12` for **all** `base : Nat`! -/
theorem alt_stateful_lib_satisfies_operational_contract :
    PublishedStatefulLibContractOperational altStatefulLibBodies 12 := by
  constructor
  · intro base
    dsimp only [evalStepGenericSlotWithFuel]
    rw [altStatefulLibBodies_eq]
    rfl
  · intro base
    refine ⟨9, [9], ?_⟩
    dsimp only [evalStepGenericSlotWithFuel]
    rw [altStatefulLibBodies_eq, runSteps_ALT_full]
    rfl

theorem alt_stateful_lib_satisfies_published_contract :
    PublishedStatefulLibContract altStatefulLibBodies := by
  intro base
  refine ⟨9, [9], ?_⟩
  rw [altStatefulLibBodies_eq]
  rfl

/-- **Control H3.1**: Although `altStatefulLibBodies` satisfies `PublishedStatefulLibContractOperational`
    (so `client_contract_user`'s contract-only theorem still holds universally), `altStatefulLibBodies`
    falsifies `client_direct_mir_inspector`'s omitted implementation theorem (`log1 = (2, 145) ≠ (2, 65)`
    and `obsEvents = [9, 2, 1] ≠ [4, 2, 1]`). -/
theorem control_h3_1_published_contract_alone_cannot_establish_omitted_impl_fact :
    evalClientDirectMirInspector linkedInspectorAndAltLibBodies true false =
      .normalReturn 105 (2, 145) (1, 2) [9, 2, 1] ∧
    evalClientDirectMirInspector linkedInspectorAndAltLibBodies true false ≠
      .normalReturn 105 (2, 65) (1, 2) [4, 2, 1] := by
  decide

/-- **Control H3.2**: Stripping non-inline `transactional_step` (`symId = 65`) from the dependency
    representation (as happens in default `.rlib` metadata without `-Z always-encode-mir=yes`)
    is rejected by `checkBodiesClosure` and fails closed with `.failed (.missingBody 65)`. -/
def defaultEncodedLibBodiesMissingNonInline : List WireBody :=
  statefulGenericLibBodiesVal.filter (fun b => b.symId != 65)

def linkedInspectorMissingNonInlineBodies : List WireBody :=
  clientDirectMirInspectorBodies ++ defaultEncodedLibBodiesMissingNonInline

theorem control_h3_2_missing_non_inline_dependency_body_fails_closed :
    checkBodiesClosure linkedInspectorMissingNonInlineBodies linkedInspectorMissingNonInlineBodies = false ∧
    evalClientDirectMirInspector linkedInspectorMissingNonInlineBodies true false =
      .failed (.missingBody 65) := by
  decide

def mutateClientAddConstTo12 (b : WireBody) : WireBody :=
  if b.symId == 66 then
    { b with blocks := b.blocks.map (fun blk =>
        match blk.term with
        | .call2 40 dst t uw op0 (.constUsize 8) =>
            { blk with term := .call2 40 dst t uw op0 (.constUsize 12) }
        | _ => blk) }
  else b

def mutatedClientAddConst12Bodies : List WireBody :=
  clientContractUserBodiesVal.map mutateClientAddConstTo12

def mutatedLayoutTableAlign8 : BoundCompilerLayoutTable :=
  { statefulGenericLibLayoutTable with
    svhFingerprintLo := 999999
    entries :=
      [ { typeName := "u32", typeTag := .u32, sizeBytes := 8, alignBytes := 8 }
      , { typeName := "EffectLog", typeTag := .effectLog, sizeBytes := 8, alignBytes := 4 }
      , { typeName := "Guard", typeTag := .guard, sizeBytes := 16, alignBytes := 8 } ] }

def mutatedLibBodiesAlign8 : List WireBody :=
  statefulGenericLibBodiesVal.map (fun b =>
    if b.symId == 38 then
      { b with blocks := [ { isCleanup := false, stmts := [ .assignUseRetagYes { localIdx := 0, proj := .here } (.constUsize 8) ], term := .ret } ] }
    else b)

def mutateClientCallDestTo3 (b : WireBody) : WireBody :=
  if b.symId == 66 then
    { b with blocks := b.blocks.map (fun blk =>
        match blk.term with
        | .call3 63 _ t uw a0 a1 a2 =>
            { blk with term := .call3 63 { localIdx := 3, proj := .here } t uw a0 a1 a2 }
        | _ => blk) }
  else b

def mutatedClientCallDest3Bodies : List WireBody :=
  clientContractUserBodiesVal.map mutateClientCallDestTo3

def mutateStepSlotCalleeTo99 (b : WireBody) : WireBody :=
  if b.symId == 63 then
    { b with blocks := b.blocks.map (fun blk =>
        match blk.term with
        | .call2 1 dst t uw a0 a1 =>
            { blk with term := .call2 99 dst t uw a0 a1 }
        | _ => blk) }
  else b

def mutatedStepSlotMissingCallee99Bodies : List WireBody :=
  statefulGenericLibBodiesVal.map mutateStepSlotCalleeTo99

theorem control_n1_contract_breaking_and_missing_callee_mutations :
    -- 1. Arithmetic constant mutation (8 -> 12):
    evalClientEntryOperationalWithCalleeOracle mutatedClientAddConst12Bodies 4
      (evalStepGenericSlotWithFuel statefulGenericLibBodiesVal 12 0 0) true 10 = (.returned (.scalar 26), 1) ∧
    evalClientEntryOperationalWithCalleeOracle clientContractUserBodiesVal 4
      (evalStepGenericSlotWithFuel statefulGenericLibBodiesVal 12 0 0) true 10 = (.returned (.scalar 22), 1) ∧
    (match findBodyBySym mutatedClientAddConst12Bodies 66 with
     | some b => reconstructVerifiedStructuredView b == some (.callStepSlotAndAddConst 3 12)
     | none => false) = true ∧
    -- 2. Alignment fact mutation (4 -> 8):
    checkLayoutTableBinding statefulGenericLibExpectedCtx statefulGenericLibCrateBytes mutatedLayoutTableAlign8 = false ∧
    evalStepGenericSlot mutatedLibBodiesAlign8 0 0 true 10 =
      (.returned (.scalar 18), { stepCount := 1, traceAcc := 4 }, [4]) ∧
    -- 3. Call destination mutation (_4 -> _3):
    evalClientEntryOperationalWithCalleeOracle mutatedClientCallDest3Bodies 4
      (evalStepGenericSlotWithFuel statefulGenericLibBodiesVal 12 0 0) true 10 ≠ (.returned (.scalar 22), 1) ∧
    (match findBodyBySym mutatedClientCallDest3Bodies 66 with
     | some b => reconstructVerifiedStructuredView b == none
     | none => false) = true ∧
    -- 4. Missing/unsupported callee 99 with identical 4-block surrounding graph shape:
    checkBodiesClosure mutatedStepSlotMissingCallee99Bodies mutatedStepSlotMissingCallee99Bodies = false ∧
    evalStepGenericSlot mutatedStepSlotMissingCallee99Bodies 0 0 true 16 =
      (.missingBody 99, { stepCount := 0, traceAcc := 0 }, []) := by
  decide

/-! ## 2. `N2` Strongest-Flags Charon `0.1.210` Multi-Artifact Controls (`#68` §4.4 & §6 N2) -/

def charonLinkedInspectorAndLibBodiesVal : List WireBody :=
  charonClientDirectMirInspectorBodies ++ charonStatefulGenericLibBodiesVal

/-- Control N2.2: Linking `charonClientDirectMirInspectorBodies` against a library instance with
    `align_of::<u64>() = 8` instead of `align_of::<u32>() = 4`. -/
def charonLinkedWrongAlignInstanceBodies : List WireBody :=
  charonLinkedInspectorAndLibBodiesVal.map (fun b =>
    if b.symId == 38 then
      { b with blocks :=
          [ { isCleanup := false
            , stmts := [ .assignUseRetagYes { localIdx := 0, proj := .here } (.constUsize 8) ]
            , term := .ret } ] }
    else b)

/-- Control N2.3: Mutating `_18 = false` to `_18 = true` in `bb3` of Charon's `transactional_step`
    (`symId = 65`), omitting drop-flag reset after `core::mem::drop(g1)`. -/
def mutateCharonBlocksOmitDropFlagClearInBb3 : Nat → List WireBlock → List WireBlock
  | _, [] => []
  | idx, blk :: rest =>
      let blk' :=
        if idx == 3 then
          let stmts' := blk.stmts.map (fun st =>
            match st with
            | .assignUseRetagYes { localIdx := 18, proj := .here } (.constBool false) =>
                .assignUseRetagYes { localIdx := 18, proj := .here } (.constBool true)
            | other => other)
          { blk with stmts := stmts' }
        else blk
      blk' :: mutateCharonBlocksOmitDropFlagClearInBb3 (idx + 1) rest

def charonLinkedOmittedCleanupBodies : List WireBody :=
  charonLinkedInspectorAndLibBodiesVal.map (fun b =>
    if b.symId == 65 then
      { b with blocks := mutateCharonBlocksOmitDropFlagClearInBb3 0 b.blocks }
    else b)

/-- Control N2.4: Changing private event tag `4 -> 9` in `bb1` of Charon's `step_generic_slot` (`symId = 63`). -/
def charonAltEvent9LibBodies : List WireBody :=
  charonStatefulGenericLibBodiesVal.map mutateStepGenericEventTagTo9

def charonLinkedEvent9Bodies : List WireBody :=
  charonLinkedInspectorAndLibBodiesVal.map mutateStepGenericEventTagTo9

/-- Control N2.5: Valid administrative change inserting `StorageLive(17); StorageDead(17)` in `bb4`
    of Charon's `transactional_step` (`symId = 65`), matching `charon_h3_ctrl5_valid_admin_change.amir`. -/
def mutateCharonBlocksAdminInBb4 : Nat → List WireBlock → List WireBlock
  | _, [] => []
  | idx, blk :: rest =>
      let blk' :=
        if idx == 4 then
          { blk with stmts := .storageLive 17 :: .storageDead 17 :: blk.stmts }
        else blk
      blk' :: mutateCharonBlocksAdminInBb4 (idx + 1) rest

def charonLinkedAdminChangeBodies : List WireBody :=
  charonLinkedInspectorAndLibBodiesVal.map (fun b =>
    if b.symId == 65 then
      { b with blocks := mutateCharonBlocksAdminInBb4 0 b.blocks }
    else b)

theorem control_n2_charon_h3_five_required_controls :
    -- 1. Missing dependency body (single-crate Opaque ULLBC without multi-artifact linking):
    checkBodiesClosure charonClientContractUserBodiesVal charonClientContractUserBodiesVal = false ∧
    checkBodiesClosure charonClientDirectMirInspectorBodies charonClientDirectMirInspectorBodies = false ∧
    evalClientEntryLinkedOperational charonClientContractUserBodiesVal 22 true 16 = (.missingBody 63, 0) ∧
    evalClientDirectMirInspectorWithFuel charonClientDirectMirInspectorBodies 55 true false =
      .failed (.missingBody 63) ∧
    -- 2. Wrong library revision/instance (align = 8 instead of 4, so step_generic_slot(16) = 24 ≠ 20 and client_audit_entry returns 0 ≠ 105):
    evalClientDirectMirInspectorWithFuel charonLinkedWrongAlignInstanceBodies 55 true false =
      .normalReturn 0 (2, 65) (1, 2) [4, 2, 1] ∧
    (CleanupExecOutcome.normalReturn 0 (2, 65) (1, 2) [4, 2, 1] ≠
      CleanupExecOutcome.normalReturn 105 (2, 65) (1, 2) [4, 2, 1]) ∧
    -- 3. Omitted cleanup on Charon ULLBC (double-drops g1 on unwind):
    evalClientDirectMirInspectorWithFuel charonLinkedOmittedCleanupBodies 65 true true =
      .unwoundWithCleanup (4, 18961) (1, 2) [4, 10, 1, 2, 1] ∧
    (CleanupExecOutcome.unwoundWithCleanup (4, 18961) (1, 2) [4, 10, 1, 2, 1] ≠
      CleanupExecOutcome.unwoundWithCleanup (3, 1185) (1, 2) [4, 10, 1, 2]) ∧
    -- 4. Changed private event (4 -> 9) on Charon ULLBC:
    evalClientDirectMirInspectorWithFuel charonLinkedEvent9Bodies 55 true false =
      .normalReturn 105 (2, 145) (1, 2) [9, 2, 1] ∧
    evalStepGenericSlotWithFuel charonAltEvent9LibBodies 16 0 0 true 16 =
      (.returned (.scalar 20), { stepCount := 1, traceAcc := 9 }, [9]) ∧
    -- 5. Valid administrative change on Charon ULLBC:
    charonLinkedAdminChangeBodies ≠ charonLinkedInspectorAndLibBodiesVal ∧
    evalClientDirectMirInspectorWithFuel charonLinkedAdminChangeBodies 55 true false =
      .normalReturn 105 (2, 65) (1, 2) [4, 2, 1] ∧
    evalClientDirectMirInspectorWithFuel charonLinkedAdminChangeBodies 55 true true =
      .unwoundWithCleanup (3, 1185) (1, 2) [4, 10, 1, 2] ∧
    evalClientDirectMirInspectorWithFuel charonLinkedAdminChangeBodies 55 false false =
      .failed .ub := by
  decide

/-! ## 3. `N3` & `H4`/`H6` Multi-Phase Lowering Validator Controls (All 4 Required Cases + Stage Separation) -/

/-- **Control H6.1 (Structurally valid semantic omission)**:
    In `transactional_step` (`symId = 65`), `bb2` moves `_4` (`g1`) into `core::mem::drop(g1)` after
    setting synthesized drop flag `_19 = const false`. If a buggy drop-elaboration pass leaves `_19 = const true`
    in `bb2`, the resulting `.amir` v3 package is still syntactically and structurally admitted
    (`isAdmittedPackageBytes = true`) and passes `checkBuiltToPostCleanupStructure = true`, but
    `checkBuiltToPostCleanupBehavioralEquiv` (and `validateBuiltToPostCleanupDropElaboration`) rejects it (`false`)
    because `g1` is double-dropped on unwind (`obsEvents = [10, 1, 2, 1] ≠ [10, 1, 2]`). -/
def controlH6OmittedDropFlagResetBytes : List Nat :=
  realStatefulGenericLibAmirBytes.take 576 ++ (1 :: realStatefulGenericLibAmirBytes.drop 577)

/-- **Control H6.3 (Deleted bad prefix)**:
    In `step_generic_slot` (`symId = 63`), replacing `PlaceMention((*_2))` (`[48, 2, 4]`) in `bb0`
    with `StorageLive(4)` (`[32, 4]`) deletes the `ptrValid = false` UB prefix while keeping the
    package syntactically and structurally admitted (`isAdmittedPackageBytes = true`).
    `validateBuiltToPostCleanupDropElaboration` rejects it (`false`). -/
def controlH6DeletedBadPrefixBytes : List Nat :=
  realStatefulGenericLibAmirBytes.take 299 ++ [32, 4] ++ realStatefulGenericLibAmirBytes.drop 302

/-- **Control H6.4 (Valid alternative administrative lowering)**:
    Inserting an administrative `StorageLive(18); StorageDead(18)` pair (`[32, 18, 33, 18]`) into
    `bb4` of `transactional_step` (`symId = 65`) produces a distinct `.amir` v3 byte stream
    (`≠ realStatefulGenericLibAmirBytes`) whose drop-flag elaboration and normal/unwind behaviors
    still refine the `MirPhase::Built` conditional-drop specification, so
    `validateBuiltToPostCleanupDropElaboration` accepts it (`true`). -/
def controlH6ValidAlternativeAdminLoweringBytes : List Nat :=
  realStatefulGenericLibAmirBytes.take 604 ++ [3, 32, 18, 33, 18] ++ realStatefulGenericLibAmirBytes.drop 605

/-- **Control N3.4 (Same-shaped early/late artifacts from a wrong configuration, `#68` §4.2 & §6 N3)**:
    Pairs the actual captured `realStatefulGenericLibBuiltWrongCfgAmirBytes` (`756` B, captured under
    `--cfg wrong_cfg_probe` without `-Z mir-preserve-ub`, `flags = 9`, with the exact same 8 function IDs `[1, 2, 3, 63, 64, 65, 7, 24]`
    and block counts as `realStatefulGenericLibBuiltAmirBytes`) with a matching wrong-config `Runtime(PostCleanup)`
    package `controlN3PostCleanupWrongCfgBytes` (`preserveUb = false`, `PlaceMention` stripped in `bb0` of `63`). -/
def realStatefulGenericLibBuiltWrongCfgAmirBytes : List Nat :=
  [65, 77, 73, 82, 3, 1, 9, 198, 148] ++ realStatefulGenericLibBuiltAmirBytes.drop 9

def controlN3PostCleanupWrongCfgBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 9] ++ controlH6DeletedBadPrefixBytes.drop 7

def wrongCfgBuiltBindingRec : CargoInvocationBindingRecord :=
  { statefulGenericLibBuiltBindingRec with
    cfgFlags := ["wrong_cfg_probe"]
    preserveUb := false
    expectedFp16 := (198, 148) }

def wrongCfgPostCleanupBindingRec : CargoInvocationBindingRecord :=
  { statefulGenericLibBindingRec with
    cfgFlags := ["wrong_cfg_probe"]
    preserveUb := false }

def bodySymIds (bs : List WireBody) : List Nat :=
  bs.map WireBody.symId

def mutateBlocksOmitDropFlagClearInBb2 : Nat → List WireBlock → List WireBlock
  | _, [] => []
  | idx, blk :: rest =>
      let blk' :=
        if idx == 2 then
          let stmts' := blk.stmts.map (fun st =>
            match st with
            | .assignUseRetagYes { localIdx := 19, proj := .here } (.constBool false) =>
                .assignUseRetagYes { localIdx := 19, proj := .here } (.constBool true)
            | other => other)
          { blk with stmts := stmts' }
        else blk
      blk' :: mutateBlocksOmitDropFlagClearInBb2 (idx + 1) rest

def controlH6OmittedDropFlagResetBodies : List WireBody :=
  statefulGenericLibBodiesVal.map (fun b =>
    if b.symId == 65 then
      { b with blocks := mutateBlocksOmitDropFlagClearInBb2 0 b.blocks }
    else b)

def controlH6DeletedBadPrefixBodies : List WireBody :=
  statefulGenericLibBodiesVal.map (fun b =>
    if b.symId == 63 then
      { b with blocks := b.blocks.map (fun blk =>
          { blk with stmts := blk.stmts.map (fun st =>
              match st with
              | .placeMention _ => .storageLive 4
              | other => other) }) }
    else b)

theorem h6_all_four_lowering_validator_controls_verified :
    -- 1. Structurally valid semantic omission (passes B1-B2 admission & Stage 2 structure, rejected by Stage 3 behavioral equiv; double-drops g1)
    (parseAdmittedRawPackageBytes controlH6OmittedDropFlagResetBytes).isSome = true ∧
    checkBuiltToPostCleanupStructure realStatefulGenericLibBuiltAmirBytes controlH6OmittedDropFlagResetBytes = true ∧
    validateBuiltToPostCleanupDropElaboration controlH6OmittedDropFlagResetBytes = false ∧
    evalPostCleanupTransactionalStep controlH6OmittedDropFlagResetBodies true =
      .unwoundWithCleanup (3, 2577) (1, 2) [10, 1, 2, 1] ∧
    -- 2. Wrong subject or configuration (including same-shaped wrong-cfg Built/PostCleanup artifacts)
    validateBuiltToPostCleanupDropElaboration realPlaceMentionDefaultBytes = false ∧
    validateBuiltToPostCleanupDropElaboration realPlaceMentionPreserveUbBytes = false ∧
    (parseAdmittedRawPackageBytes realStatefulGenericLibBuiltWrongCfgAmirBytes).isSome = true ∧
    (parseAdmittedRawPackageBytes controlN3PostCleanupWrongCfgBytes).isSome = true ∧
    checkTwoPhaseCompilationIdentity statefulGenericLibExpectedCtx wrongCfgBuiltBindingRec
      wrongCfgPostCleanupBindingRec statefulGenericLibCrateBytes
      realStatefulGenericLibBuiltWrongCfgAmirBytes controlN3PostCleanupWrongCfgBytes
      statefulGenericLibLayoutTable = false ∧
    checkBuiltToPostCleanupStructure realStatefulGenericLibBuiltWrongCfgAmirBytes controlN3PostCleanupWrongCfgBytes = false ∧
    -- 3. Deleted bad prefix (passes B1-B2 admission, rejected by validator; misses ptrValid = false UB)
    (parseAdmittedRawPackageBytes controlH6DeletedBadPrefixBytes).isSome = true ∧
    validateBuiltToPostCleanupDropElaboration controlH6DeletedBadPrefixBytes = false ∧
    (evalStepGenericSlot controlH6DeletedBadPrefixBodies 0 0 false 16).1 =
      .returned (.scalar 20) ∧
    -- 4. Valid alternative administrative lowering (distinct bytes, accepted by Stage 2 & Stage 3)
    (controlH6ValidAlternativeAdminLoweringBytes.take 610 ≠ realStatefulGenericLibAmirBytes.take 610) ∧
    (parseAdmittedRawPackageBytes controlH6ValidAlternativeAdminLoweringBytes).isSome = true ∧
    validateBuiltToPostCleanupDropElaboration controlH6ValidAlternativeAdminLoweringBytes = true := by
  decide

/-! ## 4. `N6` Counterexample Against Naive `reconstructStructuredView` & Repair by `reconstructVerifiedStructuredView` (`#68` §4.3 & §6 N6) -/

/-- **Control N6.1 (`#68` §4.3 & §6 N6)**:
    1. On `altStatefulLibBodies` (where `step_generic_slot` `symId = 63` mutates the event tag from `4`
       to `9` in `bb1`), the historical naive recognizer `reconstructStructuredView` (which checked only
       `b.symId == 63`, `b.blocks.length == 4`, and `bodyHasPlaceMention b.blocks`) unsoundly returns
       `some (.checkPtrAndStepSlot 2 3 4)`, whose `evalStructuredView` predicts `[4]` (`≠ [9]`).
    2. The repaired statement- and terminator-inspecting recognizer `reconstructVerifiedStructuredView`
       distinguishes `b63` (`some (.checkPtrAndStepSlot 2 3 4)`) from `b63_alt` (`some (.checkPtrAndStepSlot 2 3 9)`),
       so `evalStructuredView` on the verified view matches `evalStepGenericSlot altStatefulLibBodies 0 0 true 16`! -/
theorem control_n6_naive_structured_recognizer_unsound_on_event_mutation_repaired_by_verified_recognizer :
    -- 1. Old naive recognizer conflates b63 (event 4) and body_ALT_63 (event 9):
    reconstructStructuredView body_D_63_3 = some (.checkPtrAndStepSlot 2 3 4) ∧
    reconstructStructuredView body_ALT_63 = some (.checkPtrAndStepSlot 2 3 4) ∧
    evalStructuredView (.checkPtrAndStepSlot 2 3 4) 0 0 true 16 ≠
      evalStepGenericSlot altStatefulLibBodies 0 0 true 16 ∧
    -- 2. Repaired statement-inspecting recognizer extracts the exact event tag 9 and matches runSteps:
    reconstructVerifiedStructuredView body_D_63_3 = some (.checkPtrAndStepSlot 2 3 4) ∧
    reconstructVerifiedStructuredView body_ALT_63 = some (.checkPtrAndStepSlot 2 3 9) ∧
    evalStructuredView (.checkPtrAndStepSlot 2 3 9) 0 0 true 16 =
      evalStepGenericSlot altStatefulLibBodies 0 0 true 16 := by
  decide

#print axioms alt_stateful_lib_satisfies_operational_contract
#print axioms alt_stateful_lib_satisfies_published_contract
#print axioms control_h3_1_published_contract_alone_cannot_establish_omitted_impl_fact
#print axioms control_h3_2_missing_non_inline_dependency_body_fails_closed
#print axioms control_n1_contract_breaking_and_missing_callee_mutations
#print axioms control_n2_charon_h3_five_required_controls
#print axioms h6_all_four_lowering_validator_controls_verified
#print axioms control_n6_naive_structured_recognizer_unsound_on_event_mutation_repaired_by_verified_recognizer

end AnnealResearch.StatefulGenericLibraryH3H7Controls
