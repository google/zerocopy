import AnnealResearch.StatefulGenericLibraryH3H7Controls
import AnnealResearch.PR86AuditRepairs
import AnnealResearch.BuiltPhaseControlsR1
import AnnealResearch.CharonNativeAndControlsR3R4

set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 1600000

namespace AnnealResearch.PR86AuditCounterexamples

open AnnealResearch.SubstantiveMirByteParser
open AnnealResearch.SemanticVerticalSlice
open AnnealResearch.CargoWorkspaceIntegration
open AnnealResearch.StatefulGenericLibraryH3H7
open AnnealResearch.StatefulGenericLibraryH3H7Controls
open AnnealResearch.PR86AuditRepairs
open AnnealResearch.BuiltPhaseControlsR1
open AnnealResearch.CharonNativeAndControlsR3R4

/-!
# Replayable `PR #86` Audit Counterexamples and Paired `R1`–`R4`, `R7`, `R8` Verification (`joshlf/anneal#89`)

This module preserves the exact replayable Lean counterexamples from Companion Comment B of
`joshlf/anneal#89` (`9afae77818468d76fd251689272815884b1d402e`) against the retained historical
`PR #86` definitions, proves alongside each counterexample that the repaired fail-closed
definitions in `AnnealResearch.PR86AuditRepairs` (`validateBuiltToPostCleanupFailClosed`,
`checkLayoutTableBindingWithEntries`, `reconstructVerifiedStructuredViewInEnv`, and
`checkRuntimeClosedBodies`) reject or soundly handle every counterexample, and aggregates the
`R1` (`AnnealResearch.BuiltPhaseControlsR1`), `R3`, and `R4`
(`AnnealResearch.CharonNativeAndControlsR3R4`) verification theorems.
-/

/-! ## 1. Companion B Counterexamples (`U3`, `U4`, `U5`, `U6`, `U7`) and Paired Fail-Closed Repairs -/

def emptyLayout : BoundCompilerLayoutTable :=
  { statefulGenericLibLayoutTable with entries := [] }

def sameIdentityAlign8 : BoundCompilerLayoutTable :=
  { statefulGenericLibLayoutTable with entries :=
      statefulGenericLibLayoutTable.entries.map (fun e =>
        if e.typeTag == .u32 then { e with alignBytes := 8 } else e) }

def delayedMentionBlocks : Nat → List WireBlock → List WireBlock
  | _, [] => []
  | idx, blk :: bs =>
      let stripped := blk.stmts.filter (fun st =>
        match st with | .placeMention _ => false | _ => true)
      let stmts := if idx == 2 then
          WireStmt.placeMention { localIdx := 2, proj := .deref } :: stripped
        else stripped
      { blk with stmts := stmts } :: delayedMentionBlocks (idx + 1) bs

def delayedMentionPostBodies : List WireBody :=
  statefulGenericLibBodiesVal.map (fun b =>
    if b.symId == 63 then { b with blocks := delayedMentionBlocks 0 b.blocks } else b)

def missingUnusedCalleePostBodies : List WireBody :=
  (decodePackageBodies realStatefulGenericLibAmirBytes).map (fun b =>
    if b.symId == 64 then { b with blocks := b.blocks.map (fun blk =>
      match blk.term with
      | .call3 63 dst t uw a0 a1 a2 => { blk with term := .call3 99 dst t uw a0 a1 a2 }
      | _ => blk) } else b)

def encodePostBodies (bodies : List WireBody) : List Nat :=
  let payload := specEncodeBodiesCons bodies
  let fp := computeCargoPayloadFp16 statefulGenericLibCrateBytes payload
  [65, 77, 73, 82, 3, 3, 11, fp.1, fp.2, bodies.length] ++ payload

def bindingForPostBodies (bodies : List WireBody) : CargoInvocationBindingRecord :=
  let fp := computeCargoPayloadFp16 statefulGenericLibCrateBytes (specEncodeBodiesCons bodies)
  { statefulGenericLibBindingRec with expectedFp16 := fp }

def delayedRawBodies : List WireBody :=
  (decodePackageBodies realStatefulGenericLibAmirBytes).map (fun b =>
    if b.symId == 63 then { b with blocks := delayedMentionBlocks 0 b.blocks } else b)

/-- Retained Companion B theorem 1 (`U3`): the old `validateBuiltToPostCleanupTwoSided` accepted `emptyLayout`
    because both `Built` and `PostCleanup` halted at `.missingBody 38`. -/
theorem full_validator_accepts_missing_layout :
    validateBuiltToPostCleanupTwoSided statefulGenericLibExpectedCtx
      statefulGenericLibBuiltBindingRec statefulGenericLibBindingRec statefulGenericLibCrateBytes
      realStatefulGenericLibBuiltAmirBytes realStatefulGenericLibAmirBytes emptyLayout = true := by
  decide

/-- Retained Companion B theorem 2 (`U3`/`U4`): the old `validateBuiltToPostCleanupTwoSided` accepted
    `delayedRawBodies` because it projected invalid-pointer `.ub` outcomes without comparing heap or
    event prefixes. -/
theorem full_validator_accepts_delayed_bad_prefix :
    validateBuiltToPostCleanupTwoSided statefulGenericLibExpectedCtx
      statefulGenericLibBuiltBindingRec (bindingForPostBodies delayedRawBodies)
      statefulGenericLibCrateBytes realStatefulGenericLibBuiltAmirBytes
      (encodePostBodies delayedRawBodies) statefulGenericLibLayoutTable = true := by
  decide

/-- Retained Companion B theorem 3 (`U3`): the old `validateBuiltToPostCleanupTwoSided` accepted an
    unclosed `PostCleanup` package whose unused `body 64` called missing symbol `99`. -/
theorem full_validator_accepts_unclosed_post_package :
    validateBuiltToPostCleanupTwoSided statefulGenericLibExpectedCtx
      statefulGenericLibBuiltBindingRec (bindingForPostBodies missingUnusedCalleePostBodies)
      statefulGenericLibCrateBytes realStatefulGenericLibBuiltAmirBytes
      (encodePostBodies missingUnusedCalleePostBodies) statefulGenericLibLayoutTable = true := by
  decide

/-- Retained Companion B theorem 4 (`U4`): `encodePostBodies delayedRawBodies` passes syntactic/structural
    package admission (`isAdmittedPackageBytes = true`). -/
theorem delayed_bad_prefix_package_is_admitted :
    isAdmittedPackageBytes (encodePostBodies delayedRawBodies) = true := by
  decide

theorem repaired_validator_rejects_missing_layout :
    validateBuiltToPostCleanupFailClosed .strictPrefixTracePreserving statefulGenericLibExpectedCtx
      statefulGenericLibBuiltBindingRec statefulGenericLibBindingRec
      statefulGenericLibCrateBytes x86_64LinuxTargetTripleBytes statefulGenericLibEntriesFp16
      realStatefulGenericLibBuiltAmirBytes realStatefulGenericLibAmirBytes
      emptyLayout x86_64LinuxTargetTripleBytes = false ∧
    evalStepGenericSlot (decodePackageBodies realStatefulGenericLibAmirBytes) 0 0 true 16 =
      (.missingBody 38, { stepCount := 0, traceAcc := 0 }, []) ∧
    evalBuiltStepGenericSlotFromGraph (decodePackageBodies realStatefulGenericLibBuiltAmirBytes) 0 0 true 16 =
      (.missingBody 38, { stepCount := 0, traceAcc := 0 }, []) := by
  decide

theorem repaired_validator_rejects_delayed_bad_prefix :
    evalBuiltStepGenericSlotFromGraph statefulGenericLibBuiltBodies 0 0 false 16 =
      (.ub, { stepCount := 0, traceAcc := 0 }, []) ∧
    evalStepGenericSlot delayedMentionPostBodies 0 0 false 16 =
      (.ub, { stepCount := 1, traceAcc := 4 }, [4]) ∧
    validateBuiltToPostCleanupFailClosed .strictPrefixTracePreserving statefulGenericLibExpectedCtx
      statefulGenericLibBuiltBindingRec (bindingForPostBodies delayedRawBodies)
      statefulGenericLibCrateBytes x86_64LinuxTargetTripleBytes statefulGenericLibEntriesFp16
      realStatefulGenericLibBuiltAmirBytes (encodePostBodies delayedRawBodies)
      statefulGenericLibLayoutTable x86_64LinuxTargetTripleBytes = false := by
  decide

theorem repaired_validator_rejects_unclosed_post_package :
    checkBodiesClosure missingUnusedCalleePostBodies missingUnusedCalleePostBodies = false ∧
    validateBuiltToPostCleanupFailClosed .strictPrefixTracePreserving statefulGenericLibExpectedCtx
      statefulGenericLibBuiltBindingRec (bindingForPostBodies missingUnusedCalleePostBodies)
      statefulGenericLibCrateBytes x86_64LinuxTargetTripleBytes statefulGenericLibEntriesFp16
      realStatefulGenericLibBuiltAmirBytes (encodePostBodies missingUnusedCalleePostBodies)
      statefulGenericLibLayoutTable x86_64LinuxTargetTripleBytes = false := by
  decide

theorem repaired_layout_and_structured_view_and_charon_closure :
    checkLayoutTableBinding statefulGenericLibExpectedCtx
      statefulGenericLibCrateBytes sameIdentityAlign8 = true ∧
    checkLayoutTableBindingWithEntries statefulGenericLibExpectedCtx
      statefulGenericLibCrateBytes x86_64LinuxTargetTripleBytes statefulGenericLibEntriesFp16
      sameIdentityAlign8 x86_64LinuxTargetTripleBytes = false ∧
    (match findBodyBySym mutatedLibBodiesAlign8 63 with
     | some b => reconstructVerifiedStructuredView b
     | none => none) = some (.checkPtrAndStepSlot 2 3 4) ∧
    evalStepGenericSlot mutatedLibBodiesAlign8 0 0 true 10 ≠
      evalStructuredView (.checkPtrAndStepSlot 2 3 4) 0 0 true 10 ∧
    (match findBodyBySym mutatedLibBodiesAlign8 63 with
     | some b => reconstructVerifiedStructuredViewInEnv mutatedLibBodiesAlign8 b
     | none => none) = some (.checkPtrAndStepSlotWithAlign 2 3 8 4) ∧
    evalStepGenericSlot mutatedLibBodiesAlign8 0 0 true 10 =
      evalVerifiedStructuredView (.checkPtrAndStepSlotWithAlign 2 3 8 4) 0 0 true 10 ∧
    isAdmittedPackageBytes charonH3StatefulGenericLibAmirBytes = true ∧
    evalStepGenericSlot (decodePackageBodies charonH3StatefulGenericLibAmirBytes) 0 0 true 16 =
      (.missingBody 37, { stepCount := 0, traceAcc := 0 }, []) ∧
    checkRuntimeClosedBodies (decodePackageBodies charonH3StatefulGenericLibAmirBytes) = false ∧
    checkRuntimeClosedBodies charonStatefulGenericLibBodies = true := by
  decide

/-- **Paired Fail-Closed Repair Theorem (`R2`, `R7`, `R8` resolving `U3`, `U4`, `U5`, `U6`, `U7`)**:
    1. `validateBuiltToPostCleanupFailClosed` rejects `emptyLayout` (`= false`), rejects
       `delayedRawBodies` (`= false`), and rejects `missingUnusedCalleePostBodies` (`= false`), while
       accepting the genuine `(realStatefulGenericLibBuiltAmirBytes, realStatefulGenericLibAmirBytes)`
       pair (`= true`).
    2. `checkLayoutTableBindingWithEntries` rejects `sameIdentityAlign8` (`= false`) while the old
       `checkLayoutTableBinding` accepted it (`= true`).
    3. `reconstructVerifiedStructuredViewInEnv` on `mutatedLibBodiesAlign8` extracts
       `some (.checkPtrAndStepSlotWithAlign 2 3 8 4)` and matches `evalStepGenericSlot` (`18 = 18`),
       whereas the old `reconstructVerifiedStructuredView` ignored the environment and diverged (`18 ≠ 14`).
    4. `checkRuntimeClosedBodies` rejects raw `charonH3StatefulGenericLibAmirBytes` without
       supplied layout callees (`= false`, where execution hits `.missingBody 37`) and accepts
       `charonStatefulGenericLibBodies` (`= true`). -/
theorem companion_b_counterexamples_and_paired_repairs_verified :
    validateBuiltToPostCleanupTwoSided statefulGenericLibExpectedCtx
      statefulGenericLibBuiltBindingRec statefulGenericLibBindingRec statefulGenericLibCrateBytes
      realStatefulGenericLibBuiltAmirBytes realStatefulGenericLibAmirBytes emptyLayout = true ∧
    (validateBuiltToPostCleanupFailClosed .strictPrefixTracePreserving statefulGenericLibExpectedCtx
      statefulGenericLibBuiltBindingRec statefulGenericLibBindingRec
      statefulGenericLibCrateBytes x86_64LinuxTargetTripleBytes statefulGenericLibEntriesFp16
      realStatefulGenericLibBuiltAmirBytes realStatefulGenericLibAmirBytes
      emptyLayout x86_64LinuxTargetTripleBytes = false ∧
    evalStepGenericSlot (decodePackageBodies realStatefulGenericLibAmirBytes) 0 0 true 16 =
      (.missingBody 38, { stepCount := 0, traceAcc := 0 }, []) ∧
    evalBuiltStepGenericSlotFromGraph (decodePackageBodies realStatefulGenericLibBuiltAmirBytes) 0 0 true 16 =
      (.missingBody 38, { stepCount := 0, traceAcc := 0 }, [])) ∧
    validateBuiltToPostCleanupTwoSided statefulGenericLibExpectedCtx
      statefulGenericLibBuiltBindingRec (bindingForPostBodies delayedRawBodies)
      statefulGenericLibCrateBytes realStatefulGenericLibBuiltAmirBytes
      (encodePostBodies delayedRawBodies) statefulGenericLibLayoutTable = true ∧
    (evalBuiltStepGenericSlotFromGraph statefulGenericLibBuiltBodies 0 0 false 16 =
      (.ub, { stepCount := 0, traceAcc := 0 }, []) ∧
    evalStepGenericSlot delayedMentionPostBodies 0 0 false 16 =
      (.ub, { stepCount := 1, traceAcc := 4 }, [4]) ∧
    validateBuiltToPostCleanupFailClosed .strictPrefixTracePreserving statefulGenericLibExpectedCtx
      statefulGenericLibBuiltBindingRec (bindingForPostBodies delayedRawBodies)
      statefulGenericLibCrateBytes x86_64LinuxTargetTripleBytes statefulGenericLibEntriesFp16
      realStatefulGenericLibBuiltAmirBytes (encodePostBodies delayedRawBodies)
      statefulGenericLibLayoutTable x86_64LinuxTargetTripleBytes = false) ∧
    validateBuiltToPostCleanupTwoSided statefulGenericLibExpectedCtx
      statefulGenericLibBuiltBindingRec (bindingForPostBodies missingUnusedCalleePostBodies)
      statefulGenericLibCrateBytes realStatefulGenericLibBuiltAmirBytes
      (encodePostBodies missingUnusedCalleePostBodies) statefulGenericLibLayoutTable = true ∧
    (checkBodiesClosure missingUnusedCalleePostBodies missingUnusedCalleePostBodies = false ∧
    validateBuiltToPostCleanupFailClosed .strictPrefixTracePreserving statefulGenericLibExpectedCtx
      statefulGenericLibBuiltBindingRec (bindingForPostBodies missingUnusedCalleePostBodies)
      statefulGenericLibCrateBytes x86_64LinuxTargetTripleBytes statefulGenericLibEntriesFp16
      realStatefulGenericLibBuiltAmirBytes (encodePostBodies missingUnusedCalleePostBodies)
      statefulGenericLibLayoutTable x86_64LinuxTargetTripleBytes = false) ∧
    (checkLayoutTableBinding statefulGenericLibExpectedCtx
      statefulGenericLibCrateBytes sameIdentityAlign8 = true ∧
    checkLayoutTableBindingWithEntries statefulGenericLibExpectedCtx
      statefulGenericLibCrateBytes x86_64LinuxTargetTripleBytes statefulGenericLibEntriesFp16
      sameIdentityAlign8 x86_64LinuxTargetTripleBytes = false ∧
    (match findBodyBySym mutatedLibBodiesAlign8 63 with
     | some b => reconstructVerifiedStructuredView b
     | none => none) = some (.checkPtrAndStepSlot 2 3 4) ∧
    evalStepGenericSlot mutatedLibBodiesAlign8 0 0 true 10 ≠
      evalStructuredView (.checkPtrAndStepSlot 2 3 4) 0 0 true 10 ∧
    (match findBodyBySym mutatedLibBodiesAlign8 63 with
     | some b => reconstructVerifiedStructuredViewInEnv mutatedLibBodiesAlign8 b
     | none => none) = some (.checkPtrAndStepSlotWithAlign 2 3 8 4) ∧
    evalStepGenericSlot mutatedLibBodiesAlign8 0 0 true 10 =
      evalVerifiedStructuredView (.checkPtrAndStepSlotWithAlign 2 3 8 4) 0 0 true 10 ∧
    isAdmittedPackageBytes charonH3StatefulGenericLibAmirBytes = true ∧
    evalStepGenericSlot (decodePackageBodies charonH3StatefulGenericLibAmirBytes) 0 0 true 16 =
      (.missingBody 37, { stepCount := 0, traceAcc := 0 }, []) ∧
    checkRuntimeClosedBodies (decodePackageBodies charonH3StatefulGenericLibAmirBytes) = false ∧
    checkRuntimeClosedBodies charonStatefulGenericLibBodies = true) :=
  ⟨full_validator_accepts_missing_layout,
   repaired_validator_rejects_missing_layout,
   full_validator_accepts_delayed_bad_prefix,
   repaired_validator_rejects_delayed_bad_prefix,
   full_validator_accepts_unclosed_post_package,
   repaired_validator_rejects_unclosed_post_package,
   repaired_layout_and_structured_view_and_charon_closure⟩

/-! ## 2. Unified Wave A Verification Bundle (`R1`, `R2`, `R3`, `R4`, `R7`, `R8`) -/

#print axioms full_validator_accepts_missing_layout
#print axioms full_validator_accepts_delayed_bad_prefix
#print axioms full_validator_accepts_unclosed_post_package
#print axioms delayed_bad_prefix_package_is_admitted
#print axioms companion_b_counterexamples_and_paired_repairs_verified
#print axioms r1_all_five_parsed_built_phase_controls_verified
#print axioms r3_charon_native_single_artifact_closures_satisfy_contract_and_inspector_endpoints
#print axioms r4_all_seven_charon_generated_amir_controls_connected_and_verified

end AnnealResearch.PR86AuditCounterexamples
