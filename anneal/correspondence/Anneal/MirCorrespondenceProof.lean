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

namespace Anneal.MirCorrespondenceProof

open Trusted Trusted.MirAst Trusted.MirSemantics Trusted.Correspondence
open Anneal.MirCorrespondence

/-!
# MIR Correspondence Proof Hub (`Anneal.MirCorrespondenceProof`)

Thin Pass 2 entry module forwarding all 38 locked correspondence, wiring,
codec, simulation, byte-codec, and non-vacuity canary (`D6`–`D17`) theorems to
their modular proof implementations under `Anneal.MirCorrespondence.*`.
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

end Anneal.MirCorrespondenceProof
