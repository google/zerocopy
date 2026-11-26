-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Data.BitVec.BasicAux
import Init.Data.Int.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Control.Except
import Trusted
import Trusted.Correspondence
import Anneal.MirWp
import Anneal.MirWp.Canaries
import Anneal.MirCorrespondence.Codec
import Anneal.MirCorrespondence.SimHelpers
import Anneal.MirCorrespondence.ScalarEquiv
import Anneal.MirCorrespondence.EnumEquiv
import Anneal.MirCorrespondence.RvalueStep
import Anneal.MirCorrespondence.StmtTermStep
import Anneal.MirCorrespondence.InitAndSim

namespace Anneal.MirCorrespondence

open Trusted Trusted.MirAst Trusted.MirSemantics Trusted.Correspondence
open Anneal.MirWp

/-! ## Move, Overflow, Enum, `char`, and Cast Canaries (`D6`–`D16`) -/

/-- `D6` (Use-After-Move UB):
`_2 = move _1; _0 = copy _1; return` deinitializes `_1` on `move _1` and
faults with `.fault .undefined` (`.ub` in $M_{\text{ref}}$) on the subsequent
`copy _1`. -/
theorem canary_D6_use_after_move_ub_base : CanaryD6UseAfterMoveUbClaim := by
  have h_wp : wpFaultProg progUseAfterMoveD6 2 queryU32_42 .undefined := by
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    rfl
  let ⟨h_ub, h_excl, _, _, h_nwf⟩ := reaches_fault_and_exclusive_of_wpFault
    progUseAfterMoveD6 queryU32_42 2 .undefined h_wp
  have h_ref_ub := (reachesResult_fault_iff_refReachesOutcome
    progUseAfterMoveD6 queryU32_42 .undefined).1 h_ub
  exact ⟨h_ub, h_excl .unsupported (fun h => FaultKind.noConfusion h), h_nwf,
    h_ref_ub⟩

/-- `D7a` (`BinaryOp` left-to-right `copy _1` then `move _1` succeeds):
`_0 = BinOp(Add, copy _1, move _1); return` reads `_1` in `lhs`, then reads
and deinitializes `_1` in `rhs`, and returns `84`. -/
theorem canary_D7a_binop_copy_then_move_ok_base :
    CanaryD7aBinopCopyThenMoveOkClaim := by
  have h_wp : wpProg progBinOpCopyThenMoveD7a 2 queryU32_42
      (fun out => out = .returned ⟨u32Val 84, ⟨[]⟩⟩) := by
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    rfl
  let ⟨h_sat, _, out, h_beh, h_eq⟩ := wellFormed_and_spec_of_wp
    progBinOpCopyThenMoveD7a queryU32_42 2 _ h_wp
  subst h_eq
  let ⟨h_rwf, h_rbeh, _⟩ := anneal_corresponds_to_miri
    progBinOpCopyThenMoveD7a queryU32_42 h_sat.1
  exact ⟨h_sat.1, h_beh, h_rwf, (h_rbeh _).1 h_beh⟩

/-- `D7b` (`BinaryOp` left-to-right `move _1` then `copy _1` faults with UB):
`_0 = BinOp(Add, move _1, copy _1); return` deinitializes `_1` in
`lhs = move _1` and faults with `.fault .undefined` (`.ub` in
$M_{\text{ref}}$) in `rhs = copy _1`. -/
theorem canary_D7b_binop_move_then_copy_ub_base :
    CanaryD7bBinopMoveThenCopyUbClaim := by
  have h_wp :
      wpFaultProg progBinOpMoveThenCopyD7b 1 queryU32_42 .undefined := by
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    rfl
  let ⟨h_ub, h_excl, _, _, h_nwf⟩ := reaches_fault_and_exclusive_of_wpFault
    progBinOpMoveThenCopyD7b queryU32_42 1 .undefined h_wp
  have h_ref_ub := (reachesResult_fault_iff_refReachesOutcome
    progBinOpMoveThenCopyD7b queryU32_42 .undefined).1 h_ub
  exact ⟨h_ub, h_excl .unsupported (fun h => FaultKind.noConfusion h), h_nwf,
    h_ref_ub⟩

/-- `D7c` (`BinaryOp` left-to-right `move _1` then `move _1` faults with UB):
`_0 = BinOp(Add, move _1, move _1); return` deinitializes `_1` in
`lhs = move _1` and faults with `.fault .undefined` (`.ub` in
$M_{\text{ref}}$) in `rhs = move _1`. -/
theorem canary_D7c_binop_move_then_move_ub_base :
    CanaryD7cBinopMoveThenMoveUbClaim := by
  have h_wp :
      wpFaultProg progBinOpMoveThenMoveD7c 1 queryU32_42 .undefined := by
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    rfl
  let ⟨h_ub, h_excl, _, _, h_nwf⟩ := reaches_fault_and_exclusive_of_wpFault
    progBinOpMoveThenMoveD7c queryU32_42 1 .undefined h_wp
  have h_ref_ub := (reachesResult_fault_iff_refReachesOutcome
    progBinOpMoveThenMoveD7c queryU32_42 .undefined).1 h_ub
  exact ⟨h_ub, h_excl .unsupported (fun h => FaultKind.noConfusion h), h_nwf,
    h_ref_ub⟩

/-- `D8` (Self-move `_1 = move _1` preserves initialized value):
`_1 = move _1; _0 = copy _1; return` reads `42` from `_1`, deinitializes `_1`
to `.immediate none`, and then writes `42` back into `_1`, so the subsequent
`_0 = copy _1` succeeds and returns `42`. -/
theorem canary_D8_self_move_ok_base : CanaryD8SelfMoveOkClaim := by
  have h_wp : wpProg progSelfMoveD8 3 queryU32_42
      (fun out => out = .returned ⟨u32Val 42, ⟨[]⟩⟩) := by
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    rfl
  let ⟨h_sat, _, out, h_beh, h_eq⟩ :=
    wellFormed_and_spec_of_wp progSelfMoveD8 queryU32_42 3 _ h_wp
  subst h_eq
  let ⟨h_rwf, h_rbeh, _⟩ :=
    anneal_corresponds_to_miri progSelfMoveD8 queryU32_42 h_sat.1
  exact ⟨h_sat.1, h_beh, h_rwf, (h_rbeh _).1 h_beh⟩

/-- `D9` (Move of 0-Byte ZST `MirTy.unit` Remains Initialized):
`_2 = move _1; _0 = copy _1; return` where `_1 : ()` sets `_1` to
`liveUninitSlot .unit = .immediate (some .unit)`, so subsequent `_0 = copy _1`
succeeds and returns `.unit`. -/
theorem canary_D9_move_unit_zst_ok_base : CanaryD9MoveUnitZstOkClaim := by
  have h_wp : wpProg progMoveUnitZstD9 3 queryEmpty
      (fun out => out = .returned ⟨.unit, ⟨[]⟩⟩) := by
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    rfl
  let ⟨h_sat, _, out, h_beh, h_eq⟩ :=
    wellFormed_and_spec_of_wp progMoveUnitZstD9 queryEmpty 3 _ h_wp
  subst h_eq
  let ⟨h_rwf, h_rbeh, _⟩ :=
    anneal_corresponds_to_miri progMoveUnitZstD9 queryEmpty h_sat.1
  exact ⟨h_sat.1, h_beh, h_rwf, (h_rbeh _).1 h_beh⟩

/-- `D10` (unchecked versus wrapping overflow): on `(u32::MAX, 1)`,
`_0 = AddUnchecked(_1, _2)` (`progAddUncheckedU32`) reaches UB in both
machines, while wrapping `_0 = Add(_1, _2)` (`progAddU32`) returns `0` in both
machines. `encodeRvalue_binaryOp_iff` keeps the codec from exchanging the two
operators, so a semantics or codec that confused them would falsify one half
of this canary. -/
theorem canary_D10_add_unchecked_overflow_ub_base :
    CanaryD10AddUncheckedOverflowUbClaim := by
  let ⟨⟨h_ub, _, h_nwf⟩, _, h_beh⟩ :=
    canary_negative_ub_add_unchecked_overflow_u32
  have h_ref_ub := (reachesResult_fault_iff_refReachesOutcome
    progAddUncheckedU32 queryU32MaxPlusOne .undefined).1 h_ub
  exact ⟨h_ub, h_nwf, h_ref_ub, h_beh,
    (behavior_iff_refBehavior_base progAddU32 queryU32MaxPlusOne _).1 h_beh⟩

/-- `D11` (explicit-repr non-index fieldless enum constant tag decoding,
non-`isize` `u8` `Rvalue.discriminant`, and signed `i8` -> `isize` tag
sign-extension in both $M_{\text{anneal}}$ and $M_{\text{ref}}$). -/
theorem canary_D11_enum_discriminant_and_const_ok_base :
    CanaryD11EnumDiscriminantAndConstOkClaim := by
  let ⟨⟨h_wf₁, h_beh₁⟩, ⟨h_wf₂, h_beh₂⟩⟩ :=
    Anneal.MirWp.canary_positive_enum_explicit_repr_anneal
  let ⟨h_rwf₁, h_rbeh₁, _⟩ :=
    anneal_corresponds_to_miri progEnumExplicitReprU8 queryEmpty h_wf₁
  let ⟨h_rwf₂, h_rbeh₂, _⟩ :=
    anneal_corresponds_to_miri progEnumSignedTagIsize queryEmpty h_wf₂
  exact ⟨h_wf₁, h_beh₁, h_rwf₁, (h_rbeh₁ _).1 h_beh₁,
    h_wf₂, h_beh₂, h_rwf₂, (h_rbeh₂ _).1 h_beh₂⟩

/-- `D12` (1-variant inhabited ZST enum implicit return, non-deinitializing
`Operand.move`, `ConstLit.zeroSized`, and `Variants.Single 0`
`Rvalue.discriminant` in both $M_{\text{anneal}}$ and $M_{\text{ref}}$). -/
theorem canary_D12_zst_enum_move_and_discr_ok_base :
    CanaryD12ZstEnumMoveAndDiscrOkClaim := by
  let ⟨⟨h_wf₁, h_beh₁⟩, ⟨h_wf₂, h_beh₂⟩⟩ :=
    Anneal.MirWp.canary_positive_zst_single_enum_anneal
  let ⟨h_rwf₁, h_rbeh₁, _⟩ :=
    anneal_corresponds_to_miri progZstSingleEnumImplicitRet queryEmpty h_wf₁
  let ⟨h_rwf₂, h_rbeh₂, _⟩ :=
    anneal_corresponds_to_miri progZstSingleEnumMoveAndDiscr queryEmpty h_wf₂
  exact ⟨h_wf₁, h_beh₁, h_rwf₁, (h_rbeh₁ _).1 h_beh₁,
    h_wf₂, h_beh₂, h_rwf₂, (h_rbeh₂ _).1 h_beh₂⟩

/-- `D13` (invalid scalar enum tag `1` on `ReprU8 { A = 10, B = 20 }` and
reading `Rvalue.discriminant` from an uninitialized scalar-tagged enum local
reach UB in both $M_{\text{anneal}}$ and $M_{\text{ref}}$). -/
theorem canary_D13_enum_invalid_tag_and_uninit_ub_base :
    CanaryD13EnumInvalidTagAndUninitUbClaim := by
  let ⟨⟨h_ub₁, h_nunsup₁, h_nwf₁⟩, ⟨h_ub₂, h_nunsup₂, h_nwf₂⟩⟩ :=
    Anneal.MirWp.canary_negative_ub_enum_invalid_tag_and_uninit_anneal
  have h_ref_ub₁ := (reachesResult_fault_iff_refReachesOutcome
    progEnumInvalidTagConstUb queryEmpty .undefined).1 h_ub₁
  have h_ref_ub₂ := (reachesResult_fault_iff_refReachesOutcome
    progEnumUninitDiscrUb queryEmpty .undefined).1 h_ub₂
  exact ⟨h_ub₁, h_nunsup₁, h_nwf₁, h_ref_ub₁,
    h_ub₂, h_nunsup₂, h_nwf₂, h_ref_ub₂⟩

/-- `D14` (`char` three-way comparison returned through the return place,
the discriminant of an `Ordering`, and `switchInt` on a `char` agree in
$M_{\text{anneal}}$ and $M_{\text{ref}}$). -/
theorem canary_D14_char_cmp_and_switch_ok_base :
    CanaryD14CharCmpAndSwitchOkClaim := by
  let ⟨_, _, _, ⟨h_wf₁, h_beh₁⟩, _, _, _, ⟨h_wf₂, h_beh₂⟩,
      ⟨h_wf₃, h_beh₃⟩, _⟩ :=
    Anneal.MirWp.canary_positive_char_and_cmp_anneal
  let ⟨h_rwf₁, h_rbeh₁, _⟩ := anneal_corresponds_to_miri _ _ h_wf₁
  let ⟨h_rwf₂, h_rbeh₂, _⟩ := anneal_corresponds_to_miri _ _ h_wf₂
  let ⟨h_rwf₃, h_rbeh₃, _⟩ := anneal_corresponds_to_miri _ _ h_wf₃
  exact ⟨h_wf₁, h_beh₁, h_rwf₁, (h_rbeh₁ _).1 h_beh₁,
    h_wf₂, h_beh₂, h_rwf₂, (h_rbeh₂ _).1 h_beh₂,
    h_wf₃, h_beh₃, h_rwf₃, (h_rbeh₃ _).1 h_beh₃⟩

/-- `D15` (`CastKind.intToInt`: `-1i8 as u32` and `200u8 as char` agree in
both machines, and `300u32 as char` is unsupported in $M_{\text{anneal}}$ and
blocked in $M_{\text{ref}}$). -/
theorem canary_D15_int_to_int_cast_base : CanaryD15IntToIntCastClaim := by
  let ⟨⟨h_wf₁, h_beh₁⟩, _, _, _, _, _, ⟨h_wf₂, h_beh₂⟩⟩ :=
    Anneal.MirWp.canary_positive_int_to_int_cast_anneal
  let ⟨⟨h_unsup, h_nub, h_nwf⟩, _, _, _⟩ :=
    Anneal.MirWp.canary_negative_int_to_int_cast_anneal
  let ⟨h_rwf₁, h_rbeh₁, _⟩ := anneal_corresponds_to_miri _ _ h_wf₁
  let ⟨h_rwf₂, h_rbeh₂, _⟩ := anneal_corresponds_to_miri _ _ h_wf₂
  have h_ref_blocked := (reachesResult_fault_iff_refReachesOutcome
    (mkIntToIntCastProg u32Ty .char) { args := [u32Val 300] }
    .unsupported).1 h_unsup
  exact ⟨h_wf₁, h_beh₁, h_rwf₁, (h_rbeh₁ _).1 h_beh₁,
    h_wf₂, h_beh₂, h_rwf₂, (h_rbeh₂ _).1 h_beh₂,
    h_unsup, h_nub, h_nwf, h_ref_blocked⟩

/-- `D16` (`BinOp.addWithOverflow` and `BinOp.subWithOverflow` return the same
`(T, bool)` overflow pair through the return place in both machines). -/
theorem canary_D16_with_overflow_ok_base : CanaryD16WithOverflowOkClaim := by
  let ⟨⟨h_wf₁, h_beh₁⟩, _, ⟨h_wf₂, h_beh₂⟩, _, _, _⟩ :=
    Anneal.MirWp.canary_positive_overflow_ops_anneal
  let ⟨h_rwf₁, h_rbeh₁, _⟩ := anneal_corresponds_to_miri _ _ h_wf₁
  let ⟨h_rwf₂, h_rbeh₂, _⟩ := anneal_corresponds_to_miri _ _ h_wf₂
  exact ⟨h_wf₁, h_beh₁, h_rwf₁, (h_rbeh₁ _).1 h_beh₁,
    h_wf₂, h_beh₂, h_rwf₂, (h_rbeh₂ _).1 h_beh₂⟩

/-- `D17` (intra-crate `.call` and `.sysrootCall` `u16::unchecked_add` ok and
overflow UB agree in both $M_{\text{anneal}}$ and $M_{\text{ref}}$). -/
theorem canary_D17_call_and_sysroot_call_base :
    CanaryD17CallAndSysrootCallClaim := by
  have h_wp_call : wpProg progDirectCallD17 4 queryU16_19
      (fun out => out = .returned ⟨scalarNatVal .i16 false 42, ⟨[]⟩⟩) := by
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    rfl
  let ⟨h_sat₁, _, out₁, h_beh₁, h_eq₁⟩ :=
    wellFormed_and_spec_of_wp progDirectCallD17 queryU16_19 4 _ h_wp_call
  subst h_eq₁
  let ⟨h_rwf₁, h_rbeh₁, _⟩ :=
    anneal_corresponds_to_miri progDirectCallD17 queryU16_19 h_sat₁.1
  have h_wp_sys_ok : wpProg progSysrootUncheckedAddOkD17 4 queryEmpty
      (fun out => out = .returned ⟨scalarNatVal .i16 false 42, ⟨[]⟩⟩) := by
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    rfl
  let ⟨h_sat₂, _, out₂, h_beh₂, h_eq₂⟩ :=
    wellFormed_and_spec_of_wp progSysrootUncheckedAddOkD17 queryEmpty 4 _ h_wp_sys_ok
  subst h_eq₂
  let ⟨h_rwf₂, h_rbeh₂, _⟩ :=
    anneal_corresponds_to_miri progSysrootUncheckedAddOkD17 queryEmpty h_sat₂.1
  have h_wp_sys_ub :
      wpFaultProg progSysrootUncheckedAddUbD17 2 queryEmpty .undefined := by
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩; subst hc
    rfl
  let ⟨h_ub₃, _, _, _, h_nwf₃⟩ := reaches_fault_and_exclusive_of_wpFault
    progSysrootUncheckedAddUbD17 queryEmpty 2 .undefined h_wp_sys_ub
  have h_ref_ub₃ := (reachesResult_fault_iff_refReachesOutcome
    progSysrootUncheckedAddUbD17 queryEmpty .undefined).1 h_ub₃
  exact ⟨h_sat₁.1, h_beh₁, h_rwf₁, (h_rbeh₁ _).1 h_beh₁,
    h_sat₂.1, h_beh₂, h_rwf₂, (h_rbeh₂ _).1 h_beh₂,
    h_ub₃, h_nwf₃, h_ref_ub₃⟩

/-- `D17` (`TerminatorKind.assert` with `--panic abort`, `--panic unwind`,
cleanup-block refusal, and pointer-UB classification in both $M_{\text{anneal}}$
and $M_{\text{ref}}$). -/
theorem canary_D17_assert_panic_abort_base : CanaryD17AssertPanicAbortClaim := by
  have h_wp₁ : wpProg (mkAssertProg .abort .continue_ .divByZero) 3
      { args := [.bool true] }
      (fun out => out = .returned ⟨u32Val 42, ⟨[]⟩⟩) := by
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    rfl
  let ⟨h_sat₁, _, out₁, h_beh₁, h_eq₁⟩ := wellFormed_and_spec_of_wp
    (mkAssertProg .abort .continue_ .divByZero) { args := [.bool true] }
    3 _ h_wp₁
  subst h_eq₁
  let ⟨h_rwf₁, h_rbeh₁, _⟩ := anneal_corresponds_to_miri
    (mkAssertProg .abort .continue_ .divByZero) { args := [.bool true] } h_sat₁.1
  have h_wp₂ : wpProg (mkAssertProg .abort .continue_ .divByZero) 1
      { args := [.bool false] }
      (fun out => out = .aborted ⟨[]⟩) := by
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    rfl
  let ⟨h_sat₂, _, out₂, h_beh₂, h_eq₂⟩ := wellFormed_and_spec_of_wp
    (mkAssertProg .abort .continue_ .divByZero) { args := [.bool false] }
    1 _ h_wp₂
  subst h_eq₂
  let ⟨h_rwf₂, h_rbeh₂, _⟩ := anneal_corresponds_to_miri
    (mkAssertProg .abort .continue_ .divByZero) { args := [.bool false] } h_sat₂.1
  have h_wp₃ : wpFaultProg (mkAssertProg .unwind .continue_ .divByZero) 1
      { args := [.bool false] } .unsupported := by
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    rfl
  let ⟨h_unsup₃, _, _, _, h_nwf₃⟩ := reaches_fault_and_exclusive_of_wpFault
    (mkAssertProg .unwind .continue_ .divByZero) { args := [.bool false] }
    1 .unsupported h_wp₃
  have h_ref₃ := (reachesResult_fault_iff_refReachesOutcome
    (mkAssertProg .unwind .continue_ .divByZero) { args := [.bool false] }
    .unsupported).1 h_unsup₃
  have h_wp₄ : wpFaultProg (mkAssertProg .abort (.cleanup 0) .boundsCheck) 1
      { args := [.bool false] } .unsupported := by
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    rfl
  let ⟨h_unsup₄, _, _, _, h_nwf₄⟩ := reaches_fault_and_exclusive_of_wpFault
    (mkAssertProg .abort (.cleanup 0) .boundsCheck) { args := [.bool false] }
    1 .unsupported h_wp₄
  have h_ref₄ := (reachesResult_fault_iff_refReachesOutcome
    (mkAssertProg .abort (.cleanup 0) .boundsCheck) { args := [.bool false] }
    .unsupported).1 h_unsup₄
  have h_wp₅ : wpFaultProg (mkAssertProg .abort .continue_ .misalignedPtrDeref) 1
      { args := [.bool false] } .undefined := by
    refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
    subst hc
    rfl
  let ⟨h_ub₅, _, _, _, h_nwf₅⟩ := reaches_fault_and_exclusive_of_wpFault
    (mkAssertProg .abort .continue_ .misalignedPtrDeref) { args := [.bool false] }
    1 .undefined h_wp₅
  have h_ref₅ := (reachesResult_fault_iff_refReachesOutcome
    (mkAssertProg .abort .continue_ .misalignedPtrDeref)
    { args := [.bool false] } .undefined).1 h_ub₅
  exact ⟨h_sat₁.1, h_beh₁, h_rwf₁, (h_rbeh₁ _).1 h_beh₁,
    h_sat₂.1, h_beh₂, h_rwf₂, (h_rbeh₂ _).1 h_beh₂,
    h_nwf₃, h_unsup₃, h_ref₃,
    h_nwf₄, h_unsup₄, h_ref₄,
    h_nwf₅, h_ub₅, h_ref₅⟩

end Anneal.MirCorrespondence
