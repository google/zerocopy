-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Trusted
import Trusted.Correspondence
import Anneal.MirWp
import Anneal.MirCorrespondence.Codec
import Anneal.MirCorrespondence.SimHelpers
import Anneal.MirCorrespondence.ScalarEquiv
import Anneal.MirCorrespondence.EnumEquiv
import Anneal.MirCorrespondence.MemRoundTrip
import Anneal.MirCorrespondence.RvalueStep
import Anneal.MirCorrespondence.StmtTermStep
import Anneal.MirCorrespondence.InitAndSim
import Anneal.MirCorrespondence.Canaries
import Anneal.MirCorrespondence.LayoutAndAlign
import Anneal.MirCorrespondence.MiriMemoryBridge
import Anneal.MirCorrespondence.RefinementBundles
import Anneal.MirCorrespondence.ProfileV2RefMachine
import Anneal.MirCorrespondence.ProfileV2Correspondence
import Anneal.MirCorrespondence.ProfileV2Witnesses
import Anneal.MirCorrespondence.ProfileV2EdgeWitnesses
import Anneal.MirCorrespondence.ProfileV2Canaries
import Anneal.MirCorrespondence.ProfileV2PosCanaries
import Anneal.MirCorrespondence.ProfileV2PosCanariesC1
import Anneal.MirCorrespondence.ProfileV2C3AndBundles

namespace Anneal.MirCorrespondenceProof

open Trusted Trusted.MirAst Trusted.MirSemantics Trusted.Correspondence
open Anneal.MirCorrespondence

/-!
# MIR Correspondence Proof Hub (`Anneal.MirCorrespondenceProof`)

Thin Pass 2 entry module forwarding all 38 locked Profile v1 correspondence,
wiring, codec, simulation, byte-codec, and non-vacuity canary (`D6`–`D17`)
theorems, together with unlocked, untrusted-origin Profile v2
(`evalStepV2` / `CallerMemory`) correspondence evidence under
`Anneal.MirCorrespondence.*`: domain-relativized safety refinement
(`SafetyRefinementV2On`, supporting `SatisfiesPostV2`–`UnitTheoremV2`
transfers), bidirectional fault-equivalence (`BiFaultEquivV2On`),
conservative-edge separations (`Edge 1`–`Edge 3`), seven canary
(`V2_C1`–`V2_C6`, counting `V2_C4a`/`V2_C4b`) witnesses, and six regression
witnesses (their claim statements, domain predicates, fixtures, and
`ProfileV2RefMachine` live in unlocked `correspondence/`, not locked by
`TrustedBoundary.lean`, and Profile v2 verification receipts mark correspondence
inapplicable).
-/

/-- Top-level correspondence witness theorem (`CorrespondenceClaim`). -/
theorem correspondence_claim_holds : CorrespondenceClaim :=
  anneal_corresponds_to_miri

/-- Top-level bidirectional fault-equivalence witness theorem
(`FaultEquivalenceClaim`). -/
theorem fault_equivalence_claim_holds : FaultEquivalenceClaim :=
  reachesResult_fault_iff_refReachesOutcome

/-- Top-level choice-coupled correspondence witness theorem
(`CorrespondenceAtChoicesClaim`). -/
theorem correspondence_at_choices_claim_holds : CorrespondenceAtChoicesClaim :=
  correspondence_at_choices_claim_holds_base

/-- Top-level choice-coupled bidirectional fault-equivalence witness theorem
(`FaultEquivalenceAtChoicesClaim`). -/
theorem fault_equivalence_at_choices_claim_holds :
    FaultEquivalenceAtChoicesClaim :=
  fault_equivalence_at_choices_claim_holds_base

/-- Vendored `ExecutionMachine` move-deinitialization wiring witness
(`MiriMoveDeinitWiringClaim`). -/
theorem miri_move_deinit_wiring_claim_holds : MiriMoveDeinitWiringClaim :=
  miri_move_deinit_wiring_claim_holds_base

/-- Unconditional codec round-trip theorem (`decodeProg ∘ encodeProg`). -/
theorem decodeProg_encodeProg : DecodeProgEncodeProgClaim :=
  decodeProg_encodeProg_base

/-- Canonical type-table deduplication theorem for `encodeProg`. -/
theorem encodeProg_types_canonical : EncodeProgTypesCanonicalClaim :=
  encodeProg_types_canonical_base

/-- `encodeStmt` maps `.nop` and only `.nop` to `.nop`. -/
theorem encodeStmt_no_dormant_noops : EncodeStmtNoDormantNoopsClaim :=
  encodeStmt_no_dormant_noops_base

/-- `encodeRvalue` maps `.binaryOp` and only `.binaryOp` to `.binaryOp`. -/
theorem encodeRvalue_binaryOp_iff : EncodeRvalueBinaryOpIffClaim :=
  encodeRvalue_binaryOp_iff_base

/-- `encodeRvalue` maps `.unaryOp` and only `.unaryOp` to `.unaryOp`. -/
theorem encodeRvalue_unaryOp_iff : EncodeRvalueUnaryOpIffClaim :=
  encodeRvalue_unaryOp_iff_base

/-- `encodeStmt` maps `.assign` and only `.assign` to `.assign`. -/
theorem encodeStmt_assign_iff : EncodeStmtAssignIffClaim :=
  encodeStmt_assign_iff_base

/-- Left uniqueness of `SimulationInv` (`State` unique given `RefState`). -/
theorem state_unique_of_simulationInv : StateUniqueOfSimulationInvClaim :=
  state_unique_of_simulationInv_base

/-- Right uniqueness of `SimulationInv` (`RefState` unique given `State`). -/
theorem refState_unique_of_simulationInv : RefStateUniqueOfSimulationInvClaim :=
  refState_unique_of_simulationInv_base

/-- Entry initialization simulation theorem (`initRefState_sim`). -/
theorem initRefState_sim : InitRefStateSimClaim :=
  initRefState_sim_base

/-- Per-step evaluator equivalence theorem (`evalRefStep_eq`). -/
theorem evalRefStep_eq : EvalRefStepEqClaim :=
  evalRefStep_eq_base

/-- Single-step reference simulation theorem (`sim_of_refStep`). -/
theorem sim_of_refStep : SimOfRefStepClaim :=
  sim_of_refStep_base

/-- Multi-step reference simulation theorem (`sim_of_refReaches`). -/
theorem sim_of_refReaches : SimOfRefReachesClaim :=
  sim_of_refReaches_base

/-- Well-formedness transfer theorem (`refWellFormed_of_wellFormed`). -/
theorem refWellFormed_of_wellFormed : RefWellFormedOfWellFormedClaim :=
  refWellFormed_of_wellFormed_base

/-- Forward behavior simulation theorem (`refBehavior_of_behavior`). -/
theorem refBehavior_of_behavior : RefBehaviorOfBehaviorClaim :=
  refBehavior_of_behavior_base

/-- Backward behavior simulation theorem (`behavior_of_refBehavior`). -/
theorem behavior_of_refBehavior : BehaviorOfRefBehaviorClaim :=
  behavior_of_refBehavior_base

/-- Bidirectional behavior equivalence theorem (`behavior_iff_refBehavior`). -/
theorem behavior_iff_refBehavior : BehaviorIffRefBehaviorClaim :=
  behavior_iff_refBehavior_base

/-- Bidirectional divergence equivalence (`diverges_iff_refDiverges`). -/
theorem diverges_iff_refDiverges : DivergesIffRefDivergesClaim :=
  diverges_iff_refDiverges_base

theorem canary_D6_use_after_move_ub : CanaryD6UseAfterMoveUbClaim :=
  canary_D6_use_after_move_ub_base

theorem canary_D7a_binop_copy_then_move_ok : CanaryD7aBinopCopyThenMoveOkClaim :=
  canary_D7a_binop_copy_then_move_ok_base

theorem canary_D7b_binop_move_then_copy_ub : CanaryD7bBinopMoveThenCopyUbClaim :=
  canary_D7b_binop_move_then_copy_ub_base

theorem canary_D7c_binop_move_then_move_ub : CanaryD7cBinopMoveThenMoveUbClaim :=
  canary_D7c_binop_move_then_move_ub_base

theorem canary_D8_self_move_ok : CanaryD8SelfMoveOkClaim :=
  canary_D8_self_move_ok_base

theorem canary_D9_move_unit_zst_ok : CanaryD9MoveUnitZstOkClaim :=
  canary_D9_move_unit_zst_ok_base

theorem canary_D10_add_unchecked_overflow_ub : CanaryD10AddUncheckedOverflowUbClaim :=
  canary_D10_add_unchecked_overflow_ub_base

theorem canary_D11_enum_discriminant_and_const_ok : CanaryD11EnumDiscriminantAndConstOkClaim :=
  canary_D11_enum_discriminant_and_const_ok_base

theorem canary_D12_zst_enum_move_and_discr_ok : CanaryD12ZstEnumMoveAndDiscrOkClaim :=
  canary_D12_zst_enum_move_and_discr_ok_base

theorem canary_D13_enum_invalid_tag_and_uninit_ub : CanaryD13EnumInvalidTagAndUninitUbClaim :=
  canary_D13_enum_invalid_tag_and_uninit_ub_base

theorem canary_D14_char_cmp_and_switch_ok : CanaryD14CharCmpAndSwitchOkClaim :=
  canary_D14_char_cmp_and_switch_ok_base

theorem canary_D15_int_to_int_cast : CanaryD15IntToIntCastClaim :=
  canary_D15_int_to_int_cast_base

theorem canary_D16_with_overflow_ok : CanaryD16WithOverflowOkClaim :=
  canary_D16_with_overflow_ok_base

theorem canary_D17_call_and_sysroot_call : CanaryD17CallAndSysrootCallClaim :=
  canary_D17_call_and_sysroot_call_base

theorem canary_D17_assert_panic_abort : CanaryD17AssertPanicAbortClaim :=
  canary_D17_assert_panic_abort_base
theorem refStep_sound_for_allowedStep_holds : RefStepSoundForAllowedStepClaim :=
  refStep_sound_for_allowedStep_base

/-- `Trusted.MirSemantics` byte-codec agreement with `lean-miri`'s `Allocation`
scalar accesses (`BytesCodecMatchesMiriClaim`). -/
theorem bytes_codec_matches_miri : BytesCodecMatchesMiriClaim :=
  bytes_codec_matches_miri_base

/-- Every concrete `ExecutionMachine.step` call performed by `evalRefStepV2`
under `ValidRefChoice` witnesses `RefAllowedStepV2`. -/
theorem profileV2_refStep_sound_for_allowedStep (rp : RefProg) (c : Choice)
    (rs : RefState) (h_c : ValidRefChoice rp rs c) :
    let res := Miri.Interpreter.ExecutionMachine.step
      (refExecutionConfigV2 rp) refLimitsV2 c rs.miri
    RefAllowedStepV2 rp rs.miri res.1 res.2 :=
  refStepV2_sound_for_allowedStepV2 rp c rs h_c

/-- Domain-relativized Profile v2 safety refinement across `V2_C1`–`V2_C6`
(counting `V2_C4a`/`V2_C4b`). -/
theorem profileV2_canaryDomain_safetyRefinement :
    SafetyRefinementV2On ProfileV2CanaryDomain encodeProg :=
  profileV2CanaryDomain_safetyRefinement

/-- Domain-relativized Profile v2 bidirectional fault equivalence across
`V2_C1`–`V2_C6` (counting `V2_C4a`/`V2_C4b`). -/
theorem profileV2_canaryDomain_biFaultEquiv :
    BiFaultEquivV2On ProfileV2CanaryDomain encodeProg :=
  profileV2CanaryDomain_biFaultEquiv

/-- Domain-relativized Profile v2 safety refinement across
`ProfileV2ExtendedDomain` (`V2_C1`–`V2_C6` plus the three conservative
edges). -/
theorem profileV2_extendedDomain_safetyRefinement :
    SafetyRefinementV2On ProfileV2ExtendedDomain encodeProg :=
  profileV2ExtendedDomain_safetyRefinement

/-- Profile v2 bidirectional fault equivalence fails on
`ProfileV2ExtendedDomain`. -/
theorem profileV2_extendedDomain_not_biFaultEquiv :
    ¬ BiFaultEquivV2On ProfileV2ExtendedDomain encodeProg :=
  profileV2ExtendedDomain_not_biFaultEquiv

/-- Universal Profile v2 bidirectional fault equivalence is false for
`encodeProg`. -/
theorem profileV2_not_biFaultEquiv_universal :
    ¬ BiFaultEquivV2Bundle encodeProg :=
  not_biFaultEquivV2_encodeProg

/-- Profile v2 conservative-edge witness 1: zero-offset OOB `BinOp.offset`. -/
theorem profileV2_edge1_zeroOffsetOob_separation :
    ReachesResultV2 progV2Edge1ZeroOffsetOob queryV2Edge1ZeroOffsetOob
      (.fault .undefined) ∧
    ¬ WellFormedV2 progV2Edge1ZeroOffsetOob queryV2Edge1ZeroOffsetOob ∧
    RefWellFormedV2 (encodeProg progV2Edge1ZeroOffsetOob)
      queryV2Edge1ZeroOffsetOob ∧
    RefBehaviorV2 (encodeProg progV2Edge1ZeroOffsetOob)
      queryV2Edge1ZeroOffsetOob
      (.returned ⟨.ptr ⟨some 2, 8, .isize⟩, callerMemEdge1⟩) ∧
    (∀ ms, ¬ RefReachesOutcomeV2 (encodeProg progV2Edge1ZeroOffsetOob)
      queryV2Edge1ZeroOffsetOob ms .ub) :=
  conservative_edge1_zero_offset_oob_separation

/-- Profile v2 conservative-edge witness 2: null ZST dereference. -/
theorem profileV2_edge2_nullZstDeref_separation :
    ReachesResultV2 progV2Edge2NullZstDeref queryV2Edge2NullZstDeref
      (.fault .undefined) ∧
    ¬ WellFormedV2 progV2Edge2NullZstDeref queryV2Edge2NullZstDeref ∧
    RefWellFormedV2 (encodeProg progV2Edge2NullZstDeref)
      queryV2Edge2NullZstDeref ∧
    RefBehaviorV2 (encodeProg progV2Edge2NullZstDeref)
      queryV2Edge2NullZstDeref (.returned ⟨.unit, ⟨[]⟩⟩) ∧
    (∀ ms, ¬ RefReachesOutcomeV2 (encodeProg progV2Edge2NullZstDeref)
      queryV2Edge2NullZstDeref ms .ub) :=
  conservative_edge2_null_zst_deref_separation

/-- Profile v2 conservative-edge witness 3: `*const u32 as *mut u32` cast. -/
theorem profileV2_edge3_constToMutCast_separation :
    ReachesResultV2 progV2Edge3ConstToMutCast queryV2Edge3ConstToMutCast
      (.fault .unsupported) ∧
    ¬ WellFormedV2 progV2Edge3ConstToMutCast queryV2Edge3ConstToMutCast ∧
    RefWellFormedV2 (encodeProg progV2Edge3ConstToMutCast)
      queryV2Edge3ConstToMutCast ∧
    RefBehaviorV2 (encodeProg progV2Edge3ConstToMutCast)
      queryV2Edge3ConstToMutCast
      (.returned ⟨.ptr ⟨some 2, 0, .isize⟩, callerMemEdge3⟩) ∧
    (∀ ms, ¬ RefReachesOutcomeV2 (encodeProg progV2Edge3ConstToMutCast)
      queryV2Edge3ConstToMutCast ms .blocked) :=
  conservative_edge3_const_to_mut_cast_separation

/-- End-to-end Profile v2 lockstep witness for `V2_C1` (slice split). -/
theorem profileV2_canary_V2_C1_splitAt_lockstep :
    WellFormedV2 progV2_C1_splitAt queryV2_C1 ∧
    BehaviorV2 progV2_C1_splitAt queryV2_C1 outV2_C1 ∧
    ¬ DivergesV2 progV2_C1_splitAt queryV2_C1 ∧
    RefWellFormedV2 (encodeProg progV2_C1_splitAt) queryV2_C1 ∧
    RefBehaviorV2 (encodeProg progV2_C1_splitAt) queryV2_C1 outV2_C1 ∧
    (∀ out', RefBehaviorV2 (encodeProg progV2_C1_splitAt) queryV2_C1
      out' → out' = outV2_C1) ∧
    ¬ RefDivergesV2 (encodeProg progV2_C1_splitAt) queryV2_C1 :=
  V2_C1_splitAt_lockstep

/-- End-to-end Profile v2 lockstep witness for `V2_C2` (offset + write). -/
theorem profileV2_canary_V2_C2_offsetWrite_lockstep :
    WellFormedV2 progV2_C2_offsetWrite queryV2_C2 ∧
    BehaviorV2 progV2_C2_offsetWrite queryV2_C2 outV2_C2 ∧
    ¬ DivergesV2 progV2_C2_offsetWrite queryV2_C2 ∧
    RefWellFormedV2 (encodeProg progV2_C2_offsetWrite) queryV2_C2 ∧
    RefBehaviorV2 (encodeProg progV2_C2_offsetWrite) queryV2_C2 outV2_C2 ∧
    (∀ out', RefBehaviorV2 (encodeProg progV2_C2_offsetWrite) queryV2_C2
      out' → out' = outV2_C2) ∧
    ¬ RefDivergesV2 (encodeProg progV2_C2_offsetWrite) queryV2_C2 :=
  V2_C2_offsetWrite_lockstep

/-- End-to-end Profile v2 lockstep witness for `V2_C3` (`PtrMetadata`). -/
theorem profileV2_canary_V2_C3_selfPtrMetadata_lockstep :
    WellFormedV2 progV2_C3_selfPtrMetadata queryV2_C3 ∧
    BehaviorV2 progV2_C3_selfPtrMetadata queryV2_C3 outV2_C3 ∧
    ¬ DivergesV2 progV2_C3_selfPtrMetadata queryV2_C3 ∧
    RefWellFormedV2 (encodeProg progV2_C3_selfPtrMetadata) queryV2_C3 ∧
    RefBehaviorV2 (encodeProg progV2_C3_selfPtrMetadata) queryV2_C3 outV2_C3 ∧
    (∀ out', RefBehaviorV2 (encodeProg progV2_C3_selfPtrMetadata) queryV2_C3
      out' → out' = outV2_C3) ∧
    ¬ RefDivergesV2 (encodeProg progV2_C3_selfPtrMetadata) queryV2_C3 :=
  V2_C3_selfPtrMetadata_lockstep

/-- End-to-end Profile v2 lockstep witness for `V2_C4a` (entry misalign). -/
theorem profileV2_canary_V2_C4a_entryMisalign_lockstep :
    ReachesResultV2 progV2_C4a_entryMisalign queryV2_C4a (.fault .undefined) ∧
    ¬ ReachesResultV2 progV2_C4a_entryMisalign queryV2_C4a
        (.fault .unsupported) ∧
    ¬ WellFormedV2 progV2_C4a_entryMisalign queryV2_C4a ∧
    (∃ ms, RefReachesOutcomeV2 (encodeProg progV2_C4a_entryMisalign)
        queryV2_C4a ms .ub) ∧
    (∀ ms, ¬ RefReachesOutcomeV2 (encodeProg progV2_C4a_entryMisalign)
        queryV2_C4a ms .blocked) ∧
    ¬ RefWellFormedV2 (encodeProg progV2_C4a_entryMisalign) queryV2_C4a :=
  V2_C4a_entryMisalign_lockstep

/-- End-to-end Profile v2 lockstep witness for `V2_C4b` (deref misalign). -/
theorem profileV2_canary_V2_C4b_derefMisalign_lockstep :
    ReachesResultV2 progV2_C4b_derefMisalign queryV2_C4b (.fault .undefined) ∧
    ¬ ReachesResultV2 progV2_C4b_derefMisalign queryV2_C4b
        (.fault .unsupported) ∧
    ¬ WellFormedV2 progV2_C4b_derefMisalign queryV2_C4b ∧
    (∃ ms, RefReachesOutcomeV2 (encodeProg progV2_C4b_derefMisalign)
        queryV2_C4b ms .ub) ∧
    (∀ ms, ¬ RefReachesOutcomeV2 (encodeProg progV2_C4b_derefMisalign)
        queryV2_C4b ms .blocked) ∧
    ¬ RefWellFormedV2 (encodeProg progV2_C4b_derefMisalign) queryV2_C4b :=
  V2_C4b_derefMisalign_lockstep

/-- End-to-end Profile v2 lockstep witness for `V2_C5` (RO caller write). -/
theorem profileV2_canary_V2_C5_roWrite_lockstep :
    ReachesResultV2 progV2_C5_roWrite queryV2_C5 (.fault .undefined) ∧
    ¬ ReachesResultV2 progV2_C5_roWrite queryV2_C5 (.fault .unsupported) ∧
    ¬ WellFormedV2 progV2_C5_roWrite queryV2_C5 ∧
    (∃ ms, RefReachesOutcomeV2 (encodeProg progV2_C5_roWrite)
        queryV2_C5 ms .ub) ∧
    (∀ ms, ¬ RefReachesOutcomeV2 (encodeProg progV2_C5_roWrite)
        queryV2_C5 ms .blocked) ∧
    ¬ RefWellFormedV2 (encodeProg progV2_C5_roWrite) queryV2_C5 :=
  V2_C5_roWrite_lockstep

/-- End-to-end Profile v2 lockstep witness for `V2_C6` (stack-reference escape /
dangling local return). -/
theorem profileV2_canary_V2_C6_danglingLocalRef_lockstep :
    ReachesResultV2 progV2_C6_danglingLocalRef queryV2_C6 (.fault .undefined) ∧
    ¬ ReachesResultV2 progV2_C6_danglingLocalRef queryV2_C6
        (.fault .unsupported) ∧
    ¬ WellFormedV2 progV2_C6_danglingLocalRef queryV2_C6 ∧
    (∃ ms, RefReachesOutcomeV2 (encodeProg progV2_C6_danglingLocalRef)
        queryV2_C6 ms .ub) ∧
    (∀ ms, ¬ RefReachesOutcomeV2 (encodeProg progV2_C6_danglingLocalRef)
        queryV2_C6 ms .blocked) ∧
    ¬ RefWellFormedV2 (encodeProg progV2_C6_danglingLocalRef) queryV2_C6 :=
  V2_C6_danglingLocalRef_lockstep

/-- Unlocked Profile v2 regression witness: `initRefStateV2` rejects caller
and pointer `allocId`s outside non-zero `UInt64` and `nextAllocId`
wrap-around. -/
theorem profileV2_allocIdOverflow_rejected :
    let cmBadAlloc : CallerMemory := ⟨[
      { allocId := 1, alignLog2 := 0, mutability := .mut,
        bytes := [.init 1 none], live := true },
      { allocId := Nat.pow 2 64 + 1, alignLog2 := 0, mutability := .mut,
        bytes := [.init 2 none], live := true }
    ]⟩
    let cmWrapNext : CallerMemory := ⟨[
      { allocId := 1, alignLog2 := 0, mutability := .mut,
        bytes := [.init 1 none], live := true },
      { allocId := Nat.pow 2 64 - 2, alignLog2 := 0, mutability := .mut,
        bytes := [.init 2 none], live := true }
    ]⟩
    let qBadAlloc : Query := { args := [], callerMem := cmBadAlloc }
    let qWrapNext : Query := { args := [], callerMem := cmWrapNext }
    let qBadArg : Query := {
      args := [.ptr ⟨some (Nat.pow 2 64 + 2), 0, .isize⟩]
      callerMem := ⟨[]⟩
    }
    let qBadArgZeroMod : Query := {
      args := [.ptr ⟨some (Nat.pow 2 64), 0, .isize⟩]
      callerMem := ⟨[]⟩
    }
    initRefStateV2 (encodeProg progV2UnitNoop) qBadAlloc 1 =
      .error .unsupported ∧
    initRefStateV2 (encodeProg progV2UnitNoop) qWrapNext 1 =
      .error .unsupported ∧
    initRefStateV2 (encodeProg progV2Edge2NullZstDeref) qBadArg 1 =
      .error .unsupported ∧
    initRefStateV2 (encodeProg progV2Edge2NullZstDeref) qBadArgZeroMod 1 =
      .error .unsupported :=
  profileV2_rejects_allocId_overflow

/-- Unlocked Profile v2 regression witness: partial/mismatched pointer
provenance runs fail closed on entry while whole 8-byte pointers and surviving
`byteFragments` round-trip/recover on extraction. -/
theorem profileV2_partialProvenance_and_fragments_spec :
    let cmPartial : CallerMemory := ⟨[{
      allocId := 2, alignLog2 := 0, mutability := .shared,
      bytes := [.init 42 (some 2)], live := true
    }]⟩
    let cmNine : CallerMemory := ⟨[{
      allocId := 2, alignLog2 := 0, mutability := .shared,
      bytes := List.replicate 9 (.init 1 (some 2)), live := true
    }]⟩
    let cmMixed : CallerMemory := ⟨[{
      allocId := 2, alignLog2 := 0, mutability := .shared,
      bytes := List.replicate 7 (.init 1 (some 2)) ++ [.init 1 (some 3)],
      live := true
    }]⟩
    let ptrBytes := (leBytesOfNat 8 16).map (fun b => AllocByte.init b (some 2))
    let alPtr : Trusted.MirSemantics.Allocation := {
      allocId := 2, alignLog2 := 3, mutability := .mut,
      bytes := ptrBytes, live := true
    }
    (initRefStateV2 (encodeProg progV2UnitNoop)
        { args := [], callerMem := cmPartial } 1 = .error .unsupported) ∧
    (initRefStateV2 (encodeProg progV2UnitNoop)
        { args := [], callerMem := cmNine } 1 = .error .unsupported) ∧
    (initRefStateV2 (encodeProg progV2UnitNoop)
        { args := [], callerMem := cmMixed } 1 = .error .unsupported) ∧
    ((refAllocToMiriV2 alPtr).map (fun ma =>
      refExtractOneCallerAllocV2
        { (Miri.Memory.MemoryState.empty : RefMiriMem) with
          live := Array.mk [(alloc2IdV2, ⟨.machine (), ma⟩)] } alPtr) =
      .ok alPtr) ∧
    (∀ pmap : Miri.Memory.ProvenanceMap Miri.Memory.Provenance,
      pmap.ptrs = Array.empty →
      pmap.byteFragments = some (Array.mk [(Miri.ABI.Size.ofBytes 1,
        ⟨1, .concrete alloc2IdV2 Miri.Memory.BorTag.one,
          Vector.replicate 8 0⟩)]) →
      (refByteProvAtV2 pmap 0, refByteProvAtV2 pmap 1) = (none, some 2)) :=
  profileV2_partial_provenance_and_fragments_spec

/-- Unlocked Profile v2 regression witness: `--panic abort` safe assertions and
`--overflow-checks` overflow panics preserve `.aborted callerMem` mutations,
while disabled optional overflow checks and unsupported panics reject. -/
theorem profileV2_panicAbort_preserves_callerMem :
    let pBc := progV2AbortMut .boundsCheck false
    let pOvOn := progV2AbortMut (.overflow .add) true
    let pOvOff := progV2AbortMut (.overflow .add) false
    let pUns := progV2AbortMut .unsupported false
    (WellFormedV2 pBc queryV2AbortMut ∧
      BehaviorV2 pBc queryV2AbortMut (.aborted callerMemV2AbortPost) ∧
      ¬ DivergesV2 pBc queryV2AbortMut ∧
      RefWellFormedV2 (encodeProg pBc) queryV2AbortMut ∧
      RefBehaviorV2 (encodeProg pBc) queryV2AbortMut
        (.aborted callerMemV2AbortPost) ∧
      ¬ RefDivergesV2 (encodeProg pBc) queryV2AbortMut) ∧
    (WellFormedV2 pOvOn queryV2AbortMut ∧
      BehaviorV2 pOvOn queryV2AbortMut (.aborted callerMemV2AbortPost) ∧
      ¬ DivergesV2 pOvOn queryV2AbortMut ∧
      RefWellFormedV2 (encodeProg pOvOn) queryV2AbortMut ∧
      RefBehaviorV2 (encodeProg pOvOn) queryV2AbortMut
        (.aborted callerMemV2AbortPost) ∧
      ¬ RefDivergesV2 (encodeProg pOvOn) queryV2AbortMut) ∧
    (ReachesResultV2 pOvOff queryV2AbortMut (.fault .unsupported) ∧
      ¬ WellFormedV2 pOvOff queryV2AbortMut ∧
      (∃ ms, RefReachesOutcomeV2 (encodeProg pOvOff) queryV2AbortMut ms
        .blocked) ∧
      ¬ RefWellFormedV2 (encodeProg pOvOff) queryV2AbortMut) ∧
    (ReachesResultV2 pUns queryV2AbortMut (.fault .unsupported) ∧
      ¬ WellFormedV2 pUns queryV2AbortMut ∧
      (∃ ms, RefReachesOutcomeV2 (encodeProg pUns) queryV2AbortMut ms
        .blocked) ∧
      ¬ RefWellFormedV2 (encodeProg pUns) queryV2AbortMut) :=
  profileV2_panic_abort_preserves_callerMem

/-- Unlocked Profile v2 regression witness: oversized layouts (`&[u64; 2^61]`,
`[(); 2^64]`, and `([u8; 2^63], [u8; 2^63])`) fail closed before
`Miri.ABI.LayoutData` construction rather than wrapping `UInt64.ofNat`. -/
theorem profileV2_oversizedLayout_rejected :
    let u64ArrTy := MirTy.array (.int .i64 false) (Nat.pow 2 61)
    let refArrTy := MirTy.ref .shared u64ArrTy
    let zstArrTy := MirTy.array .unit (Nat.pow 2 64)
    let bigHalf := MirTy.array (.int .i8 false) (Nat.pow 2 63)
    let bigTupTy := MirTy.tuple [bigHalf, bigHalf]
    let progArrRef := mkV2Prog {
      identity := "v2_oversized_u64_arr_ref"
      argumentCount := 1
      locals := [.unit, refArrTy]
      basicBlocks := [{
        statements := [.assign ⟨0, []⟩ (.use (.constant ⟨.unit, .zeroSized⟩))]
        terminator := .return_
      }]
    }
    let progZstArr := mkV2Prog {
      identity := "v2_oversized_zst_arr"
      argumentCount := 0
      locals := [zstArrTy]
      basicBlocks := [{
        statements := []
        terminator := .return_
      }]
    }
    let progBigTup := mkV2Prog {
      identity := "v2_oversized_tuple"
      argumentCount := 0
      locals := [bigTupTy]
      basicBlocks := [{
        statements := []
        terminator := .return_
      }]
    }
    let cmEmpty : CallerMemory := ⟨[{
      allocId := 2, alignLog2 := 3, mutability := .shared,
      bytes := [], live := true
    }]⟩
    let qArr : Query := {
      args := [.ptr ⟨some 2, 0, .isize⟩]
      callerMem := cmEmpty
    }
    (refTyLayoutFitsU64V2 u64ArrTy = false) ∧
    (refTyLayoutFitsU64V2 refArrTy = false) ∧
    (refCheckedLayoutDataForTyV2 u64ArrTy = none) ∧
    (refCheckedLayoutDataForTyV2 refArrTy = none) ∧
    (refValidateRefInMiriV2 (Miri.Memory.MemoryState.empty : RefMiriMem)
      .shared u64ArrTy (.ptr ⟨some 2, 0, .isize⟩) = .error .unsupported) ∧
    (initStateV2 progArrRef qArr = .error .undefined) ∧
    (initRefStateV2 (encodeProg progArrRef) qArr 1 = .error .unsupported) ∧
    (refTyLayoutFitsU64V2 zstArrTy = false) ∧
    (refCheckedLayoutDataForTyV2 zstArrTy = none) ∧
    (initRefStateV2 (encodeProg progZstArr) { args := [], callerMem := ⟨[]⟩ } 1 =
      .error .unsupported) ∧
    (refTyLayoutFitsU64V2 bigTupTy = false) ∧
    (refCheckedLayoutDataForTyV2 bigTupTy = none) ∧
    (initRefStateV2 (encodeProg progBigTup) { args := [], callerMem := ⟨[]⟩ } 1 =
      .error .unsupported) :=
  profileV2_oversized_layout_rejected

/-- Unlocked Profile v2 regression witness: uninhabited aggregates
(`[!; N]` for `N >= 1` and tuples containing `!`) reject dangling `&[!; 1]`
references as `.undefined` (`[!; 0]` remains inhabited), and `refExecPtrAddV2`
accepts `[u8; 2^63]` with `count = 0` via unsigned `Scalar.fromUInt` while
rejecting `count = 1` as `PointerArithOverflow`. -/
theorem profileV2_uninhabitedAndLargePtrAdd_spec :
    let neverArr1 := MirTy.array .never 1
    let neverArr0 := MirTy.array .never 0
    let neverTup := MirTy.tuple [.never, .int .i8 false]
    let progNeverRef := mkV2Prog {
      identity := "v2_uninhabited_never_arr_ref"
      argumentCount := 1
      locals := [.unit, .ref .shared neverArr1]
      basicBlocks := [{
        statements := [.assign ⟨0, []⟩ (.use (.constant ⟨.unit, .zeroSized⟩))]
        terminator := .return_
      }]
    }
    let qDangling : Query := { args := [.ptr ⟨none, 1, .isize⟩], callerMem := ⟨[]⟩ }
    let emptyMem : RefMiriMem := Miri.Memory.MemoryState.empty
    let dummyBody : RefBody := {
      argumentCount := 0, locals := [0],
      basicBlocks := [{ statements := [], terminator := .return_ }]
    }
    let stDummy : RefMiriState :=
      mkRefMiriState (mkRefMiriFrameV2 [] 0 dummyBody 0 0 []
        ⟨retMemPlaceV2, refLocalLayoutForTyV2 [] .unit⟩)
        emptyMem refInitControl ⟨[]⟩
    let halfArrTy := MirTy.array (.int .i8 false) (Nat.pow 2 63)
    let rawHalfTy := MirTy.rawPtr .shared halfArrTy
    let usizeTy := MirTy.int .isize false
    let ptrTypes : List MirTy := [rawHalfTy, usizeTy, halfArrTy]
    let rawHalfLay := refLocalLayoutForTyV2 ptrTypes rawHalfTy
    let usizeLay := refLocalLayoutForTyV2 ptrTypes usizeTy
    let ptrAbi : Miri.ABI.FnAbi TyId := ⟨
      Array.mk [⟨rawHalfLay, .Direct Miri.ABI.ArgAttributes.new⟩,
        ⟨usizeLay, .Direct Miri.ABI.ArgAttributes.new⟩],
      ⟨rawHalfLay, .Direct Miri.ABI.ArgAttributes.new⟩,
      false, 2, .Rust, false⟩
    let ptr0 : Miri.Memory.Pointer Miri.Memory.Provenance :=
      ⟨Miri.ABI.Size.ZERO, .concrete alloc2IdV2 Miri.Memory.BorTag.one⟩
    let ptrImm0 : Miri.Interpreter.Immediate Miri.Memory.Provenance :=
      .scalar (.fromPointer refRuntimeLayoutV2.base ptr0)
    let opPtr0 : Miri.Interpreter.OpTy Miri.Memory.Provenance :=
      ⟨.immediate ptrImm0, rawHalfLay⟩
    let opZero : Miri.Interpreter.OpTy Miri.Memory.Provenance :=
      ⟨.immediate (.scalar (.fromScalarInt
        (Miri.Memory.ScalarInt.ofUInt64 0))), usizeLay⟩
    let opOne : Miri.Interpreter.OpTy Miri.Memory.Provenance :=
      ⟨.immediate (.scalar (.fromScalarInt
        (Miri.Memory.ScalarInt.ofUInt64 1))), usizeLay⟩
    let pFrame0 := mkRefMiriFrameV2 ptrTypes 0 dummyBody 0 0
      [⟨.live (.immediate .uninit), some rawHalfLay⟩]
      ⟨retMemPlaceV2, rawHalfLay⟩
    let pFrame0' := { pFrame0 with
      locals := Array.mk [⟨.live (.immediate ptrImm0), some rawHalfLay⟩] }
    let pSt0 : RefMiriState :=
      mkRefMiriState pFrame0 emptyMem refInitControl ⟨[]⟩
    let pSt0' : RefMiriState := { pSt0 with stack := ⟨Array.mk [pFrame0']⟩ }
    let pDest : Miri.Interpreter.RuntimePlace Miri.Memory.Provenance :=
      ⟨.local 0 0 none pFrame0.localsIdentity, rawHalfLay⟩
    let mkHalfProg (cnt : Nat) : Program := mkV2Prog {
      identity := "v2_half_arr_ptr_add"
      argumentCount := 1
      locals := [rawHalfTy, rawHalfTy]
      basicBlocks := [{
        statements := []
        terminator := .coreCall (.ptrAdd .shared halfArrTy)
          [.copy ⟨1, []⟩,
           .constant ⟨usizeTy, .scalar (BitVec.ofNat 128 cnt)⟩]
          ⟨0, []⟩ (some 1) .unreachable
      }, {
        statements := []
        terminator := .return_
      }]
    }
    let qHalf : Query := {
      args := [.ptr ⟨some 2, 0, .isize⟩]
      callerMem := ⟨[{
        allocId := 2, alignLog2 := 0, mutability := .shared,
        bytes := [], live := true
      }]⟩
    }
    ((refLayoutDataForTyV2 neverArr1).uninhabited = true) ∧
    ((refLayoutDataForTyV2 neverArr1).variants = .Empty) ∧
    ((refLayoutDataForTyV2 neverArr0).uninhabited = false) ∧
    ((refLayoutDataForTyV2 neverArr0).variants = .Single 0) ∧
    ((refLayoutDataForTyV2 neverTup).uninhabited = true) ∧
    ((refLayoutDataForTyV2 neverTup).variants = .Empty) ∧
    ((refValHooksV2 [neverArr1]).opsemInhabited 0 0 stDummy = .ok false stDummy) ∧
    ((refValHooksV2 [neverTup]).opsemInhabited 0 0 stDummy = .ok false stDummy) ∧
    (refValidateRefInMiriV2 emptyMem .shared neverArr1
      (.ptr ⟨none, 1, .isize⟩) = .error .undefined) ∧
    (refValidateRefInMiriV2 emptyMem .shared neverArr0
      (.ptr ⟨none, 1, .isize⟩) = .ok ()) ∧
    (initStateV2 progNeverRef qDangling = .error .undefined) ∧
    (initRefStateV2 (encodeProg progNeverRef) qDangling 1 = .error .undefined) ∧
    (refFnAbiOfCoreCallV2 ptrTypes
      ⟨.Item (refCoreCallDefId ptrTypes (.ptrAdd .shared halfArrTy)),
        Array.empty⟩ = .ok ptrAbi) ∧
    (WellFormedV2 (mkHalfProg 0) qHalf) ∧
    (BehaviorV2 (mkHalfProg 0) qHalf
      (.returned ⟨.ptr ⟨some 2, 0, .isize⟩, qHalf.callerMem⟩)) ∧
    (ReachesResultV2 (mkHalfProg 1) qHalf (.fault .undefined)) ∧
    (refExecPtrAddV2 ptrTypes ptrAbi (Array.mk [opPtr0, opZero]) pDest pSt0 =
      .ok .NeedsReturn pSt0') ∧
    (refExecPtrAddV2 ptrTypes ptrAbi (Array.mk [opPtr0, opOne]) pDest pSt0 =
      .error (.undefinedBehavior "PointerArithOverflow") pSt0) :=
  profileV2_uninhabited_and_large_ptrAdd_spec

/-- Unlocked Profile v2 regression witness for caller-only entry reference
validation (`&()` and 0-length `&[u8]`) and full provenance-freshness isolation
across caller allocations, live/dead caller byte provenances, argument
provenances, `retPlace`, and callee stack allocations. -/
theorem profileV2_entryRefAndProvIsolation_spec :
    let u8Ty := MirTy.int .i8 false
    let sliceU8Ty := MirTy.slice u8Ty
    let progRefUnit := mkV2Prog {
      identity := "v2_entry_dangling_ref_unit"
      argumentCount := 1
      locals := [.unit, .ref .shared .unit]
      basicBlocks := [{ statements := [], terminator := .return_ }]
    }
    let progRefSlice0 := mkV2Prog {
      identity := "v2_entry_dangling_ref_slice0"
      argumentCount := 1
      locals := [.unit, .ref .shared sliceU8Ty]
      basicBlocks := [{ statements := [], terminator := .return_ }]
    }
    let qRefUnit : Query := {
      args := [.ptr ⟨some 1, 0, .isize⟩]
      callerMem := ⟨[]⟩
    }
    let qRefSlice0 : Query := {
      args := [.slicePtr ⟨some 1, 0, .isize⟩ 0]
      callerMem := ⟨[]⟩
    }
    let progRawWrite1 := mkV2Prog {
      identity := "v2_dangling_raw_write_ret_alias"
      argumentCount := 1
      locals := [u8Ty, .rawPtr .mut u8Ty]
      basicBlocks := [{
        statements := [
          .assign ⟨1, [.deref]⟩
            (.use (.constant ⟨u8Ty, .scalar (BitVec.ofNat 128 7)⟩)),
          .assign ⟨0, []⟩
            (.use (.constant ⟨u8Ty, .scalar (BitVec.ofNat 128 0)⟩))
        ]
        terminator := .return_
      }]
    }
    let progRawOff1 := mkV2Prog {
      identity := "v2_dangling_raw_offset_ret_alias"
      argumentCount := 1
      locals := [.rawPtr .shared u8Ty, .rawPtr .shared u8Ty]
      basicBlocks := [{
        statements := [
          .assign ⟨0, []⟩
            (.binaryOp .offset (.copy ⟨1, []⟩)
              (.constant ⟨.int .isize true, .scalar (BitVec.ofNat 128 1)⟩))
        ]
        terminator := .return_
      }]
    }
    let qRaw1 : Query := {
      args := [.ptr ⟨some 1, 0, .isize⟩]
      callerMem := ⟨[]⟩
    }
    let progStackRaw := mkV2Prog {
      identity := "v2_dangling_raw_stack_alias"
      argumentCount := 1
      locals := [u8Ty, .rawPtr .mut u8Ty, .unit, .rawPtr .shared .unit]
      basicBlocks := [{
        statements := [
          .assign ⟨3, []⟩ (.addressOf .shared ⟨2, []⟩),
          .assign ⟨1, [.deref]⟩
            (.use (.constant ⟨u8Ty, .scalar (BitVec.ofNat 128 99)⟩)),
          .assign ⟨0, []⟩
            (.use (.constant ⟨u8Ty, .scalar (BitVec.ofNat 128 0)⟩))
        ]
        terminator := .return_
      }]
    }
    let qRaw2 : Query := {
      args := [.ptr ⟨some 2, 0, .isize⟩]
      callerMem := ⟨[]⟩
    }
    let alByteLive : Trusted.MirSemantics.Allocation := {
      allocId := 2, alignLog2 := 3, mutability := .mut,
      bytes := List.replicate 8 (.init 0 (some 4)), live := true
    }
    let alByteDead : Trusted.MirSemantics.Allocation := {
      allocId := 3, alignLog2 := 0, mutability := .shared,
      bytes := [.init 0 (some 1)], live := false
    }
    let cmByteProv : CallerMemory := ⟨[alByteLive, alByteDead]⟩
    (ReachesResultV2 progRefUnit qRefUnit (.fault .undefined) ∧
      ¬ WellFormedV2 progRefUnit qRefUnit ∧
      (∀ ms : Nat,
        initRefStateV2 (encodeProg progRefUnit) qRefUnit ms = .error .undefined) ∧
      (∃ ms : Nat, RefReachesOutcomeV2 (encodeProg progRefUnit) qRefUnit ms .ub) ∧
      ¬ RefWellFormedV2 (encodeProg progRefUnit) qRefUnit) ∧
    (ReachesResultV2 progRefSlice0 qRefSlice0 (.fault .undefined) ∧
      ¬ WellFormedV2 progRefSlice0 qRefSlice0 ∧
      (∀ ms : Nat,
        initRefStateV2 (encodeProg progRefSlice0) qRefSlice0 ms =
          .error .undefined) ∧
      (∃ ms : Nat,
        RefReachesOutcomeV2 (encodeProg progRefSlice0) qRefSlice0 ms .ub) ∧
      ¬ RefWellFormedV2 (encodeProg progRefSlice0) qRefSlice0) ∧
    (ReachesResultV2 progRawWrite1 qRaw1 (.fault .undefined) ∧
      ¬ WellFormedV2 progRawWrite1 qRaw1 ∧
      (∃ ms : Nat,
        RefReachesOutcomeV2 (encodeProg progRawWrite1) qRaw1 ms .ub) ∧
      ¬ RefWellFormedV2 (encodeProg progRawWrite1) qRaw1) ∧
    (ReachesResultV2 progRawOff1 qRaw1 (.fault .undefined) ∧
      ¬ WellFormedV2 progRawOff1 qRaw1 ∧
      (∃ ms : Nat,
        RefReachesOutcomeV2 (encodeProg progRawOff1) qRaw1 ms .blocked) ∧
      ¬ RefWellFormedV2 (encodeProg progRawOff1) qRaw1 ∧
      (∀ out : TerminalOut,
        ¬ RefBehaviorV2 (encodeProg progRawOff1) qRaw1 out)) ∧
    (ReachesResultV2 progStackRaw qRaw2 (.fault .undefined) ∧
      ¬ WellFormedV2 progStackRaw qRaw2 ∧
      (∃ ms : Nat,
        RefReachesOutcomeV2 (encodeProg progStackRaw) qRaw2 ms .ub) ∧
      ¬ RefWellFormedV2 (encodeProg progStackRaw) qRaw2) ∧
    (∃ st : RefState,
      initRefStateV2 (encodeProg progV2UnitNoop)
        { args := [], callerMem := cmByteProv } 1 = .ok st ∧
      st.retPlace.mplace.ptr.provenance =
        some (.concrete ⟨5, by decide⟩ Miri.Memory.BorTag.one) ∧
      st.miri.machine.memory.nextAllocId = 6) :=
  profileV2_entry_ref_and_provenance_isolation

end Anneal.MirCorrespondenceProof
