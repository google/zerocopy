-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

module
prelude
public import Init.Core
public import Init.NotationExtra
public import Init.Data.BitVec.BasicAux
public import Init.Data.Int.Basic
public import Init.Data.Nat.Div.Basic
public import Init.Data.List.Basic
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.MirWp
public import Anneal.MirTotal.Ops
public import Anneal.MirTotal.StepCore
public import Anneal.Core.BlockTree
public import Anneal.Core.StageCut
public import Anneal.OverflowCastJoin.Join

public section

namespace Anneal.OverflowCastJoin

open Trusted.MirAst Trusted.MirSemantics
open Anneal.MirWp Anneal.MirTotal Anneal.Core

/-!
# Canaries and Negative Guards (`OverflowCastJoin.Canaries`)

Kernel-checked positive and negative witnesses (`0` `noncomputable`, `0`
`._unsafe_rec`, `0` `omega`) exercising:
1. An 8-stage (`2^8 = 256` unjoined control-flow paths) multi-diamond MIR
   pipeline (`bodyOverflowCast8Stage`, `progOverflowCast8Stage`) combining
   `CastKind.intToInt` (`u32 <-> u16`), `BinOp.mulWithOverflow`,
   `BinOp.mulUnchecked`, `BinOp.addWithOverflow`, and `BinOp.addUnchecked`,
   discharged in $O(m)$ stage cuts (`cut_stage_0_to_7`, `64` steps) into both
   `wpProg` (`58 ≤ v.toNat ≤ 1041`) and `Trusted.MirSemantics.BodyVerified`;
2. Concrete endpoint cross-checks (`1041` on all-`true`, `58` on all-`false`)
   via `evalMirFuelBlockTreeBy (mirTyBeqAt 4)`;
3. Non-adjacent `StageLocalIds` (`⟨5, 2, 7, 3⟩`) framing an untouched bystander
   local (`_4 = 0xdead`) across `seal_ovfCast_stage`; and
4. Positive `*WithOverflow` true-flag execution alongside single-cause negative
   fault and well-formedness guards (`mulUnchecked` overflow -> `.undefined`,
   `intToInt` `256u16 -> char` -> `.unsupported`, and `stageLocalIdsWf`
   rejection of out-of-bounds or aliased stage indices).
-/

/-! ## 8-Stage (`256`-Path) Multi-Diamond MIR Fixture -/

/-- Arm parameters `(blockIdx, joinBlk, mulK, addC)` for one branch of a
diamond stage. -/
structure OverflowCastArmSpec where
  /-- Basic-block index of this arm. -/
  blockIdx : Nat
  /-- Join cutpoint basic-block index targeted by `.goto`. -/
  joinBlk : Nat
  /-- Unsigned `u16` multiplier constant. -/
  mulK : Nat
  /-- Unsigned `u16` additive offset constant. -/
  addC : Nat

/-- Complete specification of one 3-block diamond stage (`entryBlk`,
`trueArm`, `falseArm`). -/
structure OverflowCastStageSpec where
  /-- Entry `switchInt` basic-block index. -/
  entryBlk : Nat
  /-- Boolean flag local branched on by `entryBlk`. -/
  flagLocal : LocalId
  /-- True-branch arm specification. -/
  trueArm : OverflowCastArmSpec
  /-- False-branch arm specification. -/
  falseArm : OverflowCastArmSpec

/-- Stage local indices `(9, 10, 11, 12)` for `bodyOverflowCast8Stage`. -/
@[expose] def stageIds8 : StageLocalIds :=
  { accId := 9, tmpId := 10, ovfMulId := 11, ovfAddId := 12 }

/-- Emits the `[entry, trueArm, falseArm]` basic-block triple for `st`. -/
@[expose] def mkStageBlocks (ids : StageLocalIds) (st : OverflowCastStageSpec) :
    List BasicBlock :=
  [ mkOverflowCastEntryBlock st.flagLocal
      st.trueArm.blockIdx st.falseArm.blockIdx,
    mkOverflowCastArmBlock ids st.trueArm.mulK st.trueArm.addC
      st.trueArm.joinBlk,
    mkOverflowCastArmBlock ids st.falseArm.mulK st.falseArm.addC
      st.falseArm.joinBlk ]

/-- Concatenates stage basic-block triples via `List.foldr` (`0`
`noncomputable`). -/
@[expose] def mkStagesBlocks (ids : StageLocalIds)
    (stages : List OverflowCastStageSpec) : List BasicBlock :=
  stages.foldr (fun st acc => mkStageBlocks ids st ++ acc) []

/-- 8 affine stages (`T: 2*x + c_T`, `F: 1*x + c_F`) mapping `[1, 1]` to
`[58, 1041]` across `256` paths without overflowing `u16` (`< 65536`). -/
@[expose] def stages8Specs : List OverflowCastStageSpec :=
  [ { entryBlk := 1, flagLocal := 1,
      trueArm := ⟨2, 4, 2, 1⟩, falseArm := ⟨3, 4, 1, 1⟩ },
    { entryBlk := 4, flagLocal := 2,
      trueArm := ⟨5, 7, 2, 3⟩, falseArm := ⟨6, 7, 1, 2⟩ },
    { entryBlk := 7, flagLocal := 3,
      trueArm := ⟨8, 10, 2, 5⟩, falseArm := ⟨9, 10, 1, 4⟩ },
    { entryBlk := 10, flagLocal := 4,
      trueArm := ⟨11, 13, 2, 7⟩, falseArm := ⟨12, 13, 1, 6⟩ },
    { entryBlk := 13, flagLocal := 5,
      trueArm := ⟨14, 16, 2, 11⟩, falseArm := ⟨15, 16, 1, 8⟩ },
    { entryBlk := 16, flagLocal := 6,
      trueArm := ⟨17, 19, 2, 13⟩, falseArm := ⟨18, 19, 1, 10⟩ },
    { entryBlk := 19, flagLocal := 7,
      trueArm := ⟨20, 22, 2, 17⟩, falseArm := ⟨21, 22, 1, 12⟩ },
    { entryBlk := 22, flagLocal := 8,
      trueArm := ⟨23, 25, 2, 19⟩, falseArm := ⟨24, 25, 1, 14⟩ } ]

/-- Block `0`: initializes `_9 := 1u32` and jumps to stage `0` (`blockIdx = 1`).
-/
@[expose] def overflowCastInitBlock : BasicBlock :=
  {
    statements := [
      .assign ⟨9, []⟩
        (.use (.constant ⟨ocjU32Ty, .scalar (BitVec.ofNat 128 1)⟩))
    ]
    terminator := .goto 1
    cleanup := false
  }

/-- Block `25`: copies `_9` into return slot `_0` and executes `.return_`. -/
@[expose] def overflowCastExitBlock : BasicBlock :=
  {
    statements := [
      .assign ⟨0, []⟩ (.use (.copy ⟨9, []⟩))
    ]
    terminator := .return_
    cleanup := false
  }

/-- 26-block, 8-argument MIR `Body` with `256` unjoined diamond paths. -/
@[expose] def bodyOverflowCast8Stage : Body :=
  {
    argumentCount := 8
    locals := [
      ocjU32Ty,
      .bool, .bool, .bool, .bool, .bool, .bool, .bool, .bool,
      ocjU32Ty,
      ocjU16Ty,
      ocjOvf16Ty,
      ocjOvf16Ty
    ]
    basicBlocks :=
      [overflowCastInitBlock] ++
      mkStagesBlocks stageIds8 stages8Specs ++
      [overflowCastExitBlock]
    isUnsafe := false
    identity := "overflow_cast_join::pipeline_8stage_256paths"
  }

/-- Normalized `BlockTree` for `bodyOverflowCast8Stage` (`depth = 5`, `26`
blocks). -/
@[expose] def btOverflowCast8Stage : BlockTree BasicBlock :=
  BlockTree.ofListAt bodyOverflowCast8Stage.basicBlocks 5

/-- Single-body `Program` wrapper around `bodyOverflowCast8Stage`. -/
@[expose] def progOverflowCast8Stage : Program :=
  {
    bodies := [bodyOverflowCast8Stage]
    entryDefId := 0
    pointerWidthBits := 64
    mirProfileVersion := 1
    scope := .unit
  }

/-- Baseline 13-slot local table parameterized by the 8 boolean input flags. -/
@[expose] def baseLocals8 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : List LocalSlot :=
  [ .immediate none,
    .immediate (some (.bool b0)),
    .immediate (some (.bool b1)),
    .immediate (some (.bool b2)),
    .immediate (some (.bool b3)),
    .immediate (some (.bool b4)),
    .immediate (some (.bool b5)),
    .immediate (some (.bool b6)),
    .immediate (some (.bool b7)),
    .immediate none,
    .immediate none,
    .immediate none,
    .immediate none ]

/-! ## $O(m)$ Stage-Cut Proofs & Composition (`256` Paths -> `8` Cuts) -/

/-- Stage 0 cut: `[1, 1] -> [2, 3]` over `8` MIR steps (`T: 2*x+1`,
`F: 1*x+1`). -/
theorem cut_stage_0 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    OvfCastStageCut bodyOverflowCast8Stage btOverflowCast8Stage
      (baseLocals8 b0 b1 b2 b3 b4 b5 b6 b7) stageIds8
      { blockIdx := 1, lo := 1, hi := 1 }
      { blockIdx := 4, lo := 2, hi := 3 } 8 :=
  seal_ovfCast_stage (flagVal := b0)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (Nat.blt_eq.mp rfl) (Nat.blt_eq.mp rfl)
    (Nat.blt_eq.mp rfl) (Nat.blt_eq.mp rfl)
    (Nat.blt_eq.mp rfl) (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
    (Nat.blt_eq.mp rfl) (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
    (Nat.blt_eq.mp rfl)

/-- Stage 1 cut: `[2, 3] -> [4, 9]`. -/
theorem cut_stage_1 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    OvfCastStageCut bodyOverflowCast8Stage btOverflowCast8Stage
      (baseLocals8 b0 b1 b2 b3 b4 b5 b6 b7) stageIds8
      { blockIdx := 4, lo := 2, hi := 3 }
      { blockIdx := 7, lo := 4, hi := 9 } 8 :=
  seal_ovfCast_stage (flagVal := b1)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (Nat.blt_eq.mp rfl) (Nat.blt_eq.mp rfl)
    (Nat.blt_eq.mp rfl) (Nat.blt_eq.mp rfl)
    (Nat.blt_eq.mp rfl) (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
    (Nat.blt_eq.mp rfl) (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
    (Nat.blt_eq.mp rfl)

/-- Stage 2 cut: `[4, 9] -> [8, 23]`. -/
theorem cut_stage_2 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    OvfCastStageCut bodyOverflowCast8Stage btOverflowCast8Stage
      (baseLocals8 b0 b1 b2 b3 b4 b5 b6 b7) stageIds8
      { blockIdx := 7, lo := 4, hi := 9 }
      { blockIdx := 10, lo := 8, hi := 23 } 8 :=
  seal_ovfCast_stage (flagVal := b2)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (Nat.blt_eq.mp rfl) (Nat.blt_eq.mp rfl)
    (Nat.blt_eq.mp rfl) (Nat.blt_eq.mp rfl)
    (Nat.blt_eq.mp rfl) (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
    (Nat.blt_eq.mp rfl) (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
    (Nat.blt_eq.mp rfl)

/-- Stage 3 cut: `[8, 23] -> [14, 53]`. -/
theorem cut_stage_3 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    OvfCastStageCut bodyOverflowCast8Stage btOverflowCast8Stage
      (baseLocals8 b0 b1 b2 b3 b4 b5 b6 b7) stageIds8
      { blockIdx := 10, lo := 8, hi := 23 }
      { blockIdx := 13, lo := 14, hi := 53 } 8 :=
  seal_ovfCast_stage (flagVal := b3)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (Nat.blt_eq.mp rfl) (Nat.blt_eq.mp rfl)
    (Nat.blt_eq.mp rfl) (Nat.blt_eq.mp rfl)
    (Nat.blt_eq.mp rfl) (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
    (Nat.blt_eq.mp rfl) (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
    (Nat.blt_eq.mp rfl)

/-- Stage 4 cut: `[14, 53] -> [22, 117]`. -/
theorem cut_stage_4 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    OvfCastStageCut bodyOverflowCast8Stage btOverflowCast8Stage
      (baseLocals8 b0 b1 b2 b3 b4 b5 b6 b7) stageIds8
      { blockIdx := 13, lo := 14, hi := 53 }
      { blockIdx := 16, lo := 22, hi := 117 } 8 :=
  seal_ovfCast_stage (flagVal := b4)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (Nat.blt_eq.mp rfl) (Nat.blt_eq.mp rfl)
    (Nat.blt_eq.mp rfl) (Nat.blt_eq.mp rfl)
    (Nat.blt_eq.mp rfl) (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
    (Nat.blt_eq.mp rfl) (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
    (Nat.blt_eq.mp rfl)

/-- Stage 5 cut: `[22, 117] -> [32, 247]`. -/
theorem cut_stage_5 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    OvfCastStageCut bodyOverflowCast8Stage btOverflowCast8Stage
      (baseLocals8 b0 b1 b2 b3 b4 b5 b6 b7) stageIds8
      { blockIdx := 16, lo := 22, hi := 117 }
      { blockIdx := 19, lo := 32, hi := 247 } 8 :=
  seal_ovfCast_stage (flagVal := b5)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (Nat.blt_eq.mp rfl) (Nat.blt_eq.mp rfl)
    (Nat.blt_eq.mp rfl) (Nat.blt_eq.mp rfl)
    (Nat.blt_eq.mp rfl) (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
    (Nat.blt_eq.mp rfl) (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
    (Nat.blt_eq.mp rfl)

/-- Stage 6 cut: `[32, 247] -> [44, 511]`. -/
theorem cut_stage_6 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    OvfCastStageCut bodyOverflowCast8Stage btOverflowCast8Stage
      (baseLocals8 b0 b1 b2 b3 b4 b5 b6 b7) stageIds8
      { blockIdx := 19, lo := 32, hi := 247 }
      { blockIdx := 22, lo := 44, hi := 511 } 8 :=
  seal_ovfCast_stage (flagVal := b6)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (Nat.blt_eq.mp rfl) (Nat.blt_eq.mp rfl)
    (Nat.blt_eq.mp rfl) (Nat.blt_eq.mp rfl)
    (Nat.blt_eq.mp rfl) (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
    (Nat.blt_eq.mp rfl) (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
    (Nat.blt_eq.mp rfl)

/-- Stage 7 cut: `[44, 511] -> [58, 1041]`. -/
theorem cut_stage_7 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    OvfCastStageCut bodyOverflowCast8Stage btOverflowCast8Stage
      (baseLocals8 b0 b1 b2 b3 b4 b5 b6 b7) stageIds8
      { blockIdx := 22, lo := 44, hi := 511 }
      { blockIdx := 25, lo := 58, hi := 1041 } 8 :=
  seal_ovfCast_stage (flagVal := b7)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (Nat.blt_eq.mp rfl) (Nat.blt_eq.mp rfl)
    (Nat.blt_eq.mp rfl) (Nat.blt_eq.mp rfl)
    (Nat.blt_eq.mp rfl) (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
    (Nat.blt_eq.mp rfl) (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
    (Nat.blt_eq.mp rfl)

/-- Balanced binary-tree composition of all 8 stages (`64` steps total). -/
theorem cut_stage_0_to_7 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    OvfCastStageCut bodyOverflowCast8Stage btOverflowCast8Stage
      (baseLocals8 b0 b1 b2 b3 b4 b5 b6 b7) stageIds8
      { blockIdx := 1, lo := 1, hi := 1 }
      { blockIdx := 25, lo := 58, hi := 1041 } 64 :=
  ovfCastStageCut_compose
    (ovfCastStageCut_compose
      (ovfCastStageCut_compose
        (cut_stage_0 b0 b1 b2 b3 b4 b5 b6 b7)
        (cut_stage_1 b0 b1 b2 b3 b4 b5 b6 b7))
      (ovfCastStageCut_compose
        (cut_stage_2 b0 b1 b2 b3 b4 b5 b6 b7)
        (cut_stage_3 b0 b1 b2 b3 b4 b5 b6 b7)))
    (ovfCastStageCut_compose
      (ovfCastStageCut_compose
        (cut_stage_4 b0 b1 b2 b3 b4 b5 b6 b7)
        (cut_stage_5 b0 b1 b2 b3 b4 b5 b6 b7))
      (ovfCastStageCut_compose
        (cut_stage_6 b0 b1 b2 b3 b4 b5 b6 b7)
        (cut_stage_7 b0 b1 b2 b3 b4 b5 b6 b7)))

/-! ## Entry, Exit, `wpProg`, and `BodyVerified` Adequacy Proofs -/

private theorem valid_btOverflowCast8Stage :
    ValidBlockTree bodyOverflowCast8Stage.basicBlocks btOverflowCast8Stage :=
  valid_blockTree_ofListAt bodyOverflowCast8Stage.basicBlocks 5
    (Nat.le_of_ble_eq_true rfl)

private theorem bvToNat_ofNat128_lt_65536 {n : Nat} (hn : n < 65536) :
    (BitVec.ofNat 128 n).toNat = n := by
  change Nat.mod n (Nat.pow 2 128) = n
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hn (Nat.le_of_ble_eq_true rfl))

private theorem initLocalsLoop_bodyOverflowCast8Stage
    (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    initLocalsLoop bodyOverflowCast8Stage
      [.bool b0, .bool b1, .bool b2, .bool b3,
       .bool b4, .bool b5, .bool b6, .bool b7]
      0 bodyOverflowCast8Stage.locals =
    baseLocals8 b0 b1 b2 b3 b4 b5 b6 b7 := by
  rw [← initLocalsLoopComp_eq]
  rfl

/-- Entry `2`-step transition from `initLocalsLoop` to stage `0` (`[1, 1]`). -/
theorem overflowCast8Stage_entry_cut (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    wpUntilCutStep (evalStep (bodyProg bodyOverflowCast8Stage) 0)
      (StageIntervalStateInv (baseLocals8 b0 b1 b2 b3 b4 b5 b6 b7) stageIds8
        { blockIdx := 1, lo := 1, hi := 1 })
      2
      (mkState 0 0
        (initLocalsLoop bodyOverflowCast8Stage
          [.bool b0, .bool b1, .bool b2, .bool b3,
           .bool b4, .bool b5, .bool b6, .bool b7]
          0 bodyOverflowCast8Stage.locals)) := by
  rw [initLocalsLoop_bodyOverflowCast8Stage]
  let base := baseLocals8 b0 b1 b2 b3 b4 b5 b6 b7
  have hTree0 : btOverflowCast8Stage.lookup 0 = some overflowCastInitBlock :=
    rfl
  have hGet9 : compGetElem? base 9 = some (.immediate none) := rfl
  have hLt9 : 9 < base.length := Nat.blt_eq.mp rfl
  have hSlotsEq :
      listSetAt base 9 (.immediate (some (ocjU32Val 1))) =
        applyStageSlots base stageIds8 1 none none none := rfl
  have hConst1 :
      evalConstLitComp ocjU32Ty (.scalar (BitVec.ofNat 128 1)) =
        .ok (ocjU32Val 1) := by
    unfold evalConstLitComp ocjU32Ty ocjU32Val
    dsimp only
    rw [truncateBitsComp_i32_of_lt (Nat.blt_eq.mp rfl),
      (bv128BeqComp_iff (BitVec.ofNat 128 1) (BitVec.ofNat 128 1)).mpr rfl]
    rfl
  have hRval1 :
      evalRvalueBy MirTy.beq bodyOverflowCast8Stage.locals base entryMemory
        ocjU32Ty
        (.use (.constant ⟨ocjU32Ty, .scalar (BitVec.ofNat 128 1)⟩)) =
        .ok (ocjU32Val 1, base, entryMemory) := by
    unfold evalRvalueBy evalOperandToSlotComp
    dsimp only
    rw [hConst1]
    rfl
  have hS0 :
      evalStep (bodyProg bodyOverflowCast8Stage) 0 (mkState 0 0 base) =
      .step (mkStageState 0 1 base stageIds8 1 none none none ⟨[]⟩
        entryMemory) := by
    have hStep := evalStep_bodyProg_block_assign (stmtIdx := 0)
      (cm := ⟨[]⟩) (mem := entryMemory)
      valid_btOverflowCast8Stage hTree0 rfl
      (rfl : compGetElem? bodyOverflowCast8Stage.locals 9 = some ocjU32Ty)
      hRval1
      (writePlace_imm_listSetAt entryMemory
        (checkVal_u32_lt (Nat.blt_eq.mp rfl)) hGet9 hLt9)
    rw [hSlotsEq] at hStep
    exact hStep
  have hS1 :
      evalStep (bodyProg bodyOverflowCast8Stage) 0
        (mkStageState 0 1 base stageIds8 1 none none none ⟨[]⟩ entryMemory) =
      .step (mkStageState 1 0 base stageIds8 1 none none none ⟨[]⟩
        entryMemory) := by
    unfold mkStageState
    rw [evalStep_bodyProg_block_term (stmtIdx := 1) valid_btOverflowCast8Stage
      hTree0 rfl rfl]
    rfl
  exact wpUntilCutStep_step hS0
    (wpUntilCutStep_step hS1
      (wpUntilCutStep_here 0
        ⟨1, none, none, none, entryMemory, rfl,
          Nat.le_refl 1, Nat.le_refl 1, Nat.blt_eq.mp rfl⟩))

/-- Exit `2`-step transition from block `25` (`[58, 1041]`) into
`wpOutcomeState` establishing `.returned ⟨.scalar ⟨.i32, false, v⟩, ⟨[]⟩⟩` with
`58 ≤ v.toNat ≤ 1041`. -/
theorem overflowCast8Stage_exit_wp (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    ∀ st : State,
      StageIntervalStateInv (baseLocals8 b0 b1 b2 b3 b4 b5 b6 b7) stageIds8
        { blockIdx := 25, lo := 58, hi := 1041 } st →
      wpOutcomeState (bodyProg bodyOverflowCast8Stage)
        (fun out => ∃ v : BitVec 128,
          out = .returned ⟨.scalar ⟨.i32, false, v⟩, ⟨[]⟩⟩ ∧
          58 ≤ v.toNat ∧ v.toNat ≤ 1041 ∧ v.toNat < 65536)
        (fun _ => False) 2 st := by
  intro st hInv
  let ⟨acc, oTmp, oMul, oAdd, mem, hEqS, hLo, hHi, hLt⟩ := hInv
  subst hEqS
  have hAccLt : acc < 65536 := Nat.lt_of_le_of_lt hHi hLt
  let base := baseLocals8 b0 b1 b2 b3 b4 b5 b6 b7
  let slots0 := applyStageSlots base stageIds8 acc oTmp oMul oAdd
  let slots1 := listSetAt slots0 0 (.immediate (some (ocjU32Val acc)))
  have hTree25 : btOverflowCast8Stage.lookup 25 = some overflowCastExitBlock :=
    rfl
  have hGet9 : compGetElem? slots0 9 =
      some (.immediate (some (ocjU32Val acc))) :=
    rfl
  have hGet0 : compGetElem? slots0 0 = some (.immediate none) := rfl
  have hLt0 : 0 < slots0.length := Nat.blt_eq.mp rfl
  have hS0 :
      evalStep (bodyProg bodyOverflowCast8Stage) 0
        (mkStageState 25 0 base stageIds8 acc oTmp oMul oAdd ⟨[]⟩ mem) =
      .step { frames := [{ defId := 0, blockIdx := 25, stmtIdx := 1,
                           locals := slots1 }],
              callerMem := ⟨[]⟩, mem := mem } := by
    unfold mkStageState
    exact evalStep_bodyProg_block_assign valid_btOverflowCast8Stage hTree25 rfl
      (rfl : compGetElem? bodyOverflowCast8Stage.locals 0 = some ocjU32Ty)
      (evalRvalue_use_copy_imm
        (rfl : compGetElem? bodyOverflowCast8Stage.locals 9 = some ocjU32Ty)
        hGet9 rfl)
      (writePlace_imm_listSetAt mem (checkVal_u32_lt hAccLt) hGet0 hLt0)
  have hS1 :
      evalStep (bodyProg bodyOverflowCast8Stage) 0
        { frames := [{ defId := 0, blockIdx := 25, stmtIdx := 1,
                       locals := slots1 }],
          callerMem := ⟨[]⟩, mem := mem } =
      .done (.returned ⟨ocjU32Val acc, ⟨[]⟩⟩) := by
    rw [evalStep_bodyProg_block_term (stmtIdx := 1) valid_btOverflowCast8Stage
      hTree25 rfl rfl]
    rfl
  have hVToNat : (BitVec.ofNat 128 acc).toNat = acc :=
    bvToNat_ofNat128_lt_65536 hAccLt
  change (∃ c₀ : Choice, ValidChoice (bodyProg bodyOverflowCast8Stage) _ c₀) ∧ _
  refine ⟨⟨0, rfl⟩, fun c hc => ?_⟩
  have hc0 : c = 0 := hc
  rw [hc0, hS0]
  change (∃ c₀ : Choice, ValidChoice (bodyProg bodyOverflowCast8Stage) _ c₀) ∧ _
  refine ⟨⟨0, rfl⟩, fun c' hc' => ?_⟩
  have hc'0 : c' = 0 := hc'
  rw [hc'0, hS1]
  refine ⟨BitVec.ofNat 128 acc, rfl, ?_, ?_, ?_⟩
  · rw [hVToNat]; exact hLo
  · rw [hVToNat]; exact hHi
  · rw [hVToNat]; exact hAccLt

/-- Whole-program `wpProg` specification for `progOverflowCast8Stage` across all
`256` boolean input combinations `(b0..b7)` in `68` fuel steps (`[propext]`
only). -/
theorem overflowCast8Stage_256paths_wpProg
    (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    wpProg progOverflowCast8Stage 68
      { args := [.bool b0, .bool b1, .bool b2, .bool b3,
                 .bool b4, .bool b5, .bool b6, .bool b7] }
      (fun out => ∃ v : BitVec 128,
        out = .returned ⟨.scalar ⟨.i32, false, v⟩, ⟨[]⟩⟩ ∧
        58 ≤ v.toNat ∧ v.toNat ≤ 1041 ∧ v.toNat < 65536) := by
  have hBody :
      Trusted.MirSemantics.getElem? progOverflowCast8Stage.bodies
        progOverflowCast8Stage.entryDefId =
      some bodyOverflowCast8Stage := rfl
  have hAdm :
      BodyStaticAdmitted progOverflowCast8Stage bodyOverflowCast8Stage = true :=
    rfl
  have hArgs :
      ValidEntryArgs bodyOverflowCast8Stage
        [.bool b0, .bool b1, .bool b2, .bool b3,
         .bool b4, .bool b5, .bool b6, .bool b7] := rfl
  unfold wpProg
  rw [initState_eq_ok hBody hAdm hArgs]
  change wpOutcomeState (bodyProg bodyOverflowCast8Stage) _ (fun _ => False)
    (2 + 64 + 2) _
  exact wpOutcomeState_of_ovfCastStageCut_and_exit
    valid_btOverflowCast8Stage
    (overflowCast8Stage_entry_cut b0 b1 b2 b3 b4 b5 b6 b7)
    (cut_stage_0_to_7 b0 b1 b2 b3 b4 b5 b6 b7)
    (overflowCast8Stage_exit_wp b0 b1 b2 b3 b4 b5 b6 b7)

private theorem validEntryArgs_8_bool_inv {args : List Val}
    (h : ValidEntryArgs bodyOverflowCast8Stage args) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 : Bool,
      args = [.bool b0, .bool b1, .bool b2, .bool b3,
              .bool b4, .bool b5, .bool b6, .bool b7] := by
  change checkArgsMatch args
    [.bool, .bool, .bool, .bool, .bool, .bool, .bool, .bool] = true at h
  let ⟨v0, r1, e0, hv0, h1⟩ := checkArgsMatch_cons_iff.mp h
  let ⟨b0, hb0⟩ := checkVal_bool_iff.mp hv0
  let ⟨v1, r2, e1, hv1, h2⟩ := checkArgsMatch_cons_iff.mp h1
  let ⟨b1, hb1⟩ := checkVal_bool_iff.mp hv1
  let ⟨v2, r3, e2, hv2, h3⟩ := checkArgsMatch_cons_iff.mp h2
  let ⟨b2, hb2⟩ := checkVal_bool_iff.mp hv2
  let ⟨v3, r4, e3, hv3, h4⟩ := checkArgsMatch_cons_iff.mp h3
  let ⟨b3, hb3⟩ := checkVal_bool_iff.mp hv3
  let ⟨v4, r5, e4, hv4, h5⟩ := checkArgsMatch_cons_iff.mp h4
  let ⟨b4, hb4⟩ := checkVal_bool_iff.mp hv4
  let ⟨v5, r6, e5, hv5, h6⟩ := checkArgsMatch_cons_iff.mp h5
  let ⟨b5, hb5⟩ := checkVal_bool_iff.mp hv5
  let ⟨v6, r7, e6, hv6, h7⟩ := checkArgsMatch_cons_iff.mp h6
  let ⟨b6, hb6⟩ := checkVal_bool_iff.mp hv6
  let ⟨v7, r8, e7, hv7, h8⟩ := checkArgsMatch_cons_iff.mp h7
  let ⟨b7, hb7⟩ := checkVal_bool_iff.mp hv7
  have e8 : r8 = [] := checkArgsMatch_nil_iff.mp h8
  subst e8; subst e7; subst e6; subst e5; subst e4
  subst e3; subst e2; subst e1; subst e0
  subst hb0; subst hb1; subst hb2; subst hb3
  subst hb4; subst hb5; subst hb6; subst hb7
  exact ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩

/-- Discharges `Trusted.MirSemantics.BodyVerified` for `bodyOverflowCast8Stage`
via the 8-stage linear interval-hull join (`[propext]` only). -/
theorem overflowCast8Stage_bodyVerified :
    BodyVerified progOverflowCast8Stage 0 bodyOverflowCast8Stage
      (fun _ => True) := by
  refine ⟨rfl, rfl, ?_⟩
  intro args hValid _
  let ⟨b0, b1, b2, b3, b4, b5, b6, b7, hEq⟩ := validEntryArgs_8_bool_inv hValid
  subst hEq
  have hWp := overflowCast8Stage_256paths_wpProg b0 b1 b2 b3 b4 b5 b6 b7
  exact (wellFormed_and_spec_of_wp_base
    (entryProgForBody progOverflowCast8Stage 0)
    { args := [.bool b0, .bool b1, .bool b2, .bool b3,
               .bool b4, .bool b5, .bool b6, .bool b7] }
    68 _ hWp).1.1

private theorem evalMirFuelBlockTreeBy_add (tyEq : MirTy → MirTy → Bool)
    (bt : BlockTree BasicBlock) (body : Body) :
    ∀ (f1 f2 : Nat) (s : State),
      (match evalMirFuelBlockTreeBy tyEq bt body f1 s with
       | .step st' => evalMirFuelBlockTreeBy tyEq bt body f2 st'
       | .done out => .done out
       | .fault k => .fault k) =
      evalMirFuelBlockTreeBy tyEq bt body (f1 + f2) s
  | 0, f2, s => by
    rw [Nat.zero_add]
    rfl
  | k + 1, f2, s => by
    rw [Nat.succ_add]
    unfold evalMirFuelBlockTreeBy
    dsimp only
    cases evalMirStepBlockTreeBy tyEq bt body s with
    | done _ | fault _ => rfl
    | step st' => exact evalMirFuelBlockTreeBy_add tyEq bt body k f2 st'

private def stageDoneState (base : List LocalSlot)
    (blk mulRes addRes : Nat) : State :=
  mkStageState blk 0 base stageIds8 addRes
    (some (ocjU16Val addRes))
    (some (.tuple [ocjU16Val mulRes, .bool false]))
    (some (.tuple [ocjU16Val addRes, .bool false]))
    ⟨[]⟩ entryMemoryComp

@[irreducible] private def FuelRun (fuel : Nat) (s : State)
    (res : StepResult State TerminalOut) : Prop :=
  evalMirFuelBlockTreeBy (mirTyBeqAt 4) btOverflowCast8Stage
    bodyOverflowCast8Stage fuel s = res

private theorem fuelRun_of_eq {fuel : Nat} {s : State}
    {res : StepResult State TerminalOut}
    (h : evalMirFuelBlockTreeBy (mirTyBeqAt 4) btOverflowCast8Stage
      bodyOverflowCast8Stage fuel s = res) :
    FuelRun fuel s res := by
  unfold FuelRun
  exact h

private theorem fuelRun_to_eq {f1 f2 : Nat} {s1 s2 : State}
    {res : StepResult State TerminalOut}
    (hf : f1 = f2) (hs : s1 = s2) (h : FuelRun f2 s2 res) :
    evalMirFuelBlockTreeBy (mirTyBeqAt 4) btOverflowCast8Stage
      bodyOverflowCast8Stage f1 s1 = res := by
  subst hf
  subst hs
  unfold FuelRun at h
  exact h

private theorem fuelRun_chain {f1 f2 : Nat} {s s' : State}
    {res : StepResult State TerminalOut}
    (h1 : FuelRun f1 s (.step s')) (h2 : FuelRun f2 s' res) :
    FuelRun (f1 + f2) s res := by
  unfold FuelRun at h1
  unfold FuelRun at h2
  unfold FuelRun
  rw [← evalMirFuelBlockTreeBy_add, h1]
  exact h2

private def baseT : List LocalSlot :=
  baseLocals8 true true true true true true true true
private def stT0 : State :=
  mkState 0 0
    (initLocalsLoopComp bodyOverflowCast8Stage
      [.bool true, .bool true, .bool true, .bool true,
       .bool true, .bool true, .bool true, .bool true]
      0 bodyOverflowCast8Stage.locals)
    0 entryMemoryComp
private def stT1 : State :=
  mkStageState 1 0 baseT stageIds8 1 none none none ⟨[]⟩ entryMemoryComp
private def stT2 : State := stageDoneState baseT 4 2 3
private def stT3 : State := stageDoneState baseT 7 6 9
private def stT4 : State := stageDoneState baseT 10 18 23
private def stT5 : State := stageDoneState baseT 13 46 53
private def stT6 : State := stageDoneState baseT 16 106 117
private def stT7 : State := stageDoneState baseT 19 234 247
private def stT8 : State := stageDoneState baseT 22 494 511
private def stT9 : State := stageDoneState baseT 25 1022 1041

private theorem stT_step0 :
    evalMirFuelBlockTreeBy (mirTyBeqAt 4) btOverflowCast8Stage
      bodyOverflowCast8Stage 2 stT0 = .step stT1 := rfl
private theorem stT_step1 :
    evalMirFuelBlockTreeBy (mirTyBeqAt 4) btOverflowCast8Stage
      bodyOverflowCast8Stage 8 stT1 = .step stT2 := rfl
private theorem stT_step2 :
    evalMirFuelBlockTreeBy (mirTyBeqAt 4) btOverflowCast8Stage
      bodyOverflowCast8Stage 8 stT2 = .step stT3 := rfl
private theorem stT_step3 :
    evalMirFuelBlockTreeBy (mirTyBeqAt 4) btOverflowCast8Stage
      bodyOverflowCast8Stage 8 stT3 = .step stT4 := rfl
private theorem stT_step4 :
    evalMirFuelBlockTreeBy (mirTyBeqAt 4) btOverflowCast8Stage
      bodyOverflowCast8Stage 8 stT4 = .step stT5 := rfl
private theorem stT_step5 :
    evalMirFuelBlockTreeBy (mirTyBeqAt 4) btOverflowCast8Stage
      bodyOverflowCast8Stage 8 stT5 = .step stT6 := rfl
private theorem stT_step6 :
    evalMirFuelBlockTreeBy (mirTyBeqAt 4) btOverflowCast8Stage
      bodyOverflowCast8Stage 8 stT6 = .step stT7 := rfl
private theorem stT_step7 :
    evalMirFuelBlockTreeBy (mirTyBeqAt 4) btOverflowCast8Stage
      bodyOverflowCast8Stage 8 stT7 = .step stT8 := rfl
private theorem stT_step8 :
    evalMirFuelBlockTreeBy (mirTyBeqAt 4) btOverflowCast8Stage
      bodyOverflowCast8Stage 8 stT8 = .step stT9 := rfl
private theorem stT_step9 :
    evalMirFuelBlockTreeBy (mirTyBeqAt 4) btOverflowCast8Stage
      bodyOverflowCast8Stage 2 stT9 =
      .done (.returned ⟨ocjU32Val 1041, ⟨[]⟩⟩) := rfl

/-- Concrete all-`true` endpoint check (`1041`) via
`evalMirFuelBlockTreeBy`. -/
theorem overflowCast8Stage_allTrue_1041_rfl :
    evalMirFuelBlockTreeBy (mirTyBeqAt 4) btOverflowCast8Stage
      bodyOverflowCast8Stage 68
      (mkState 0 0
        (initLocalsLoopComp bodyOverflowCast8Stage
          [.bool true, .bool true, .bool true, .bool true,
           .bool true, .bool true, .bool true, .bool true]
          0 bodyOverflowCast8Stage.locals)) =
      .done (.returned ⟨ocjU32Val 1041, ⟨[]⟩⟩) :=
  fuelRun_to_eq rfl rfl
    (fuelRun_chain (fuelRun_of_eq stT_step0)
      (fuelRun_chain (fuelRun_of_eq stT_step1)
        (fuelRun_chain (fuelRun_of_eq stT_step2)
          (fuelRun_chain (fuelRun_of_eq stT_step3)
            (fuelRun_chain (fuelRun_of_eq stT_step4)
              (fuelRun_chain (fuelRun_of_eq stT_step5)
                (fuelRun_chain (fuelRun_of_eq stT_step6)
                  (fuelRun_chain (fuelRun_of_eq stT_step7)
                    (fuelRun_chain (fuelRun_of_eq stT_step8)
                      (fuelRun_of_eq stT_step9))))))))))

private def baseF : List LocalSlot :=
  baseLocals8 false false false false false false false false
private def stF0 : State :=
  mkState 0 0
    (initLocalsLoopComp bodyOverflowCast8Stage
      [.bool false, .bool false, .bool false, .bool false,
       .bool false, .bool false, .bool false, .bool false]
      0 bodyOverflowCast8Stage.locals)
    0 entryMemoryComp
private def stF1 : State :=
  mkStageState 1 0 baseF stageIds8 1 none none none ⟨[]⟩ entryMemoryComp
private def stF2 : State := stageDoneState baseF 4 1 2
private def stF3 : State := stageDoneState baseF 7 2 4
private def stF4 : State := stageDoneState baseF 10 4 8
private def stF5 : State := stageDoneState baseF 13 8 14
private def stF6 : State := stageDoneState baseF 16 14 22
private def stF7 : State := stageDoneState baseF 19 22 32
private def stF8 : State := stageDoneState baseF 22 32 44
private def stF9 : State := stageDoneState baseF 25 44 58

private theorem stF_step0 :
    evalMirFuelBlockTreeBy (mirTyBeqAt 4) btOverflowCast8Stage
      bodyOverflowCast8Stage 2 stF0 = .step stF1 := rfl
private theorem stF_step1 :
    evalMirFuelBlockTreeBy (mirTyBeqAt 4) btOverflowCast8Stage
      bodyOverflowCast8Stage 8 stF1 = .step stF2 := rfl
private theorem stF_step2 :
    evalMirFuelBlockTreeBy (mirTyBeqAt 4) btOverflowCast8Stage
      bodyOverflowCast8Stage 8 stF2 = .step stF3 := rfl
private theorem stF_step3 :
    evalMirFuelBlockTreeBy (mirTyBeqAt 4) btOverflowCast8Stage
      bodyOverflowCast8Stage 8 stF3 = .step stF4 := rfl
private theorem stF_step4 :
    evalMirFuelBlockTreeBy (mirTyBeqAt 4) btOverflowCast8Stage
      bodyOverflowCast8Stage 8 stF4 = .step stF5 := rfl
private theorem stF_step5 :
    evalMirFuelBlockTreeBy (mirTyBeqAt 4) btOverflowCast8Stage
      bodyOverflowCast8Stage 8 stF5 = .step stF6 := rfl
private theorem stF_step6 :
    evalMirFuelBlockTreeBy (mirTyBeqAt 4) btOverflowCast8Stage
      bodyOverflowCast8Stage 8 stF6 = .step stF7 := rfl
private theorem stF_step7 :
    evalMirFuelBlockTreeBy (mirTyBeqAt 4) btOverflowCast8Stage
      bodyOverflowCast8Stage 8 stF7 = .step stF8 := rfl
private theorem stF_step8 :
    evalMirFuelBlockTreeBy (mirTyBeqAt 4) btOverflowCast8Stage
      bodyOverflowCast8Stage 8 stF8 = .step stF9 := rfl
private theorem stF_step9 :
    evalMirFuelBlockTreeBy (mirTyBeqAt 4) btOverflowCast8Stage
      bodyOverflowCast8Stage 2 stF9 =
      .done (.returned ⟨ocjU32Val 58, ⟨[]⟩⟩) := rfl

/-- Concrete all-`false` endpoint check (`58`) via
`evalMirFuelBlockTreeBy`. -/
theorem overflowCast8Stage_allFalse_58_rfl :
    evalMirFuelBlockTreeBy (mirTyBeqAt 4) btOverflowCast8Stage
      bodyOverflowCast8Stage 68
      (mkState 0 0
        (initLocalsLoopComp bodyOverflowCast8Stage
          [.bool false, .bool false, .bool false, .bool false,
           .bool false, .bool false, .bool false, .bool false]
          0 bodyOverflowCast8Stage.locals)) =
      .done (.returned ⟨ocjU32Val 58, ⟨[]⟩⟩) :=
  fuelRun_to_eq rfl rfl
    (fuelRun_chain (fuelRun_of_eq stF_step0)
      (fuelRun_chain (fuelRun_of_eq stF_step1)
        (fuelRun_chain (fuelRun_of_eq stF_step2)
          (fuelRun_chain (fuelRun_of_eq stF_step3)
            (fuelRun_chain (fuelRun_of_eq stF_step4)
              (fuelRun_chain (fuelRun_of_eq stF_step5)
                (fuelRun_chain (fuelRun_of_eq stF_step6)
                  (fuelRun_chain (fuelRun_of_eq stF_step7)
                    (fuelRun_chain (fuelRun_of_eq stF_step8)
                      (fuelRun_of_eq stF_step9))))))))))

/-! ## Non-Adjacent `StageLocalIds` Frame-Preservation Canary -/

/-- Shuffled, non-adjacent `StageLocalIds` (`⟨5, 2, 7, 3⟩`) leaving local `4`
untouched between stage slots. -/
@[expose] def shuffledStageIds : StageLocalIds :=
  { accId := 5, tmpId := 2, ovfMulId := 7, ovfAddId := 3 }

/-- 1-stage MIR `Body` using `shuffledStageIds` and a bystander `u32` local at
index `4`. -/
@[expose] def bodyShuffled1Stage : Body :=
  {
    argumentCount := 1
    locals := [ocjU32Ty, .bool, ocjU16Ty, ocjOvf16Ty, ocjU32Ty, ocjU32Ty,
               .unit, ocjOvf16Ty]
    basicBlocks :=
      [ mkOverflowCastEntryBlock 1 1 2,
        mkOverflowCastArmBlock shuffledStageIds 3 5 3,
        mkOverflowCastArmBlock shuffledStageIds 2 1 3,
        { statements := [], terminator := .return_, cleanup := false } ]
    isUnsafe := false
    identity := "overflow_cast_join::shuffled_stage_ids_frame"
  }

/-- Baseline locals for `bodyShuffled1Stage` holding `ocjU32Val 0xdead` in
bystander slot `4`. -/
@[expose] def shuffledBaseLocals (flag : Bool) : List LocalSlot :=
  [ .immediate (some (ocjU32Val 0)),
    .immediate (some (.bool flag)),
    .immediate none,
    .immediate none,
    .immediate (some (ocjU32Val 0xdead)),
    .immediate none,
    .immediate (some .unit),
    .immediate none ]

/-- Verifies that `seal_ovfCast_stage` works on non-adjacent
`shuffledStageIds` (`⟨5, 2, 7, 3⟩`) and preserves bystander slot `4`
(`0xdead`) and slot `6` (`.unit`) in every reachable post-cut state. -/
theorem canary_nonadjacent_stage_ids_preserves_frame (flag : Bool) :
    OvfCastStageCut bodyShuffled1Stage
      (BlockTree.ofList bodyShuffled1Stage.basicBlocks)
      (shuffledBaseLocals flag) shuffledStageIds
      { blockIdx := 0, lo := 10, hi := 20 }
      { blockIdx := 3, lo := 21, hi := 65 } 8 ∧
    (∀ st : State,
      StageIntervalStateInv (shuffledBaseLocals flag) shuffledStageIds
        { blockIdx := 3, lo := 21, hi := 65 } st →
      ∃ f : FrameState,
        st.frames = [f] ∧
        compGetElem? f.locals 4 = some (.immediate (some (ocjU32Val 0xdead))) ∧
        compGetElem? f.locals 6 = some (.immediate (some .unit))) := by
  refine ⟨?_, ?_⟩
  · exact seal_ovfCast_stage (flagVal := flag)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (Nat.blt_eq.mp rfl) (Nat.blt_eq.mp rfl)
      (Nat.blt_eq.mp rfl) (Nat.blt_eq.mp rfl)
      (Nat.blt_eq.mp rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_of_ble_eq_true rfl)
      (Nat.blt_eq.mp rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_of_ble_eq_true rfl)
      (Nat.blt_eq.mp rfl)
  · intro st hInv
    let ⟨acc, oTmp, oMul, oAdd, mem, hEq, _, _, _⟩ := hInv
    subst hEq
    exact ⟨_, rfl, rfl, rfl⟩

/-! ## Overflow-Flag Positive Canary & Single-Cause Negative Regressions -/

/-- `Body` computing `mulWithOverflow(40000u16, 2u16) = (14464u16, true)`. -/
@[expose] def bodyWithOverflowOnly : Body :=
  {
    argumentCount := 0
    locals := [ocjOvf16Ty]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.binaryOp .mulWithOverflow
          (.constant ⟨ocjU16Ty, .scalar (BitVec.ofNat 128 40000)⟩)
          (.constant ⟨ocjU16Ty, .scalar (BitVec.ofNat 128 2)⟩))
      ]
      terminator := .return_
      cleanup := false
    }]
    isUnsafe := false
    identity := "overflow_cast_join::pos_with_overflow_sets_true"
  }

/-- `Body` computing `mulWithOverflow(40000u16, 2u16)` followed by faulting
`mulUnchecked(40000u16, 2u16)`. -/
@[expose] def bodyWithOverflowThenUncheckedFault : Body :=
  {
    argumentCount := 0
    locals := [ocjOvf16Ty, ocjU16Ty]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.binaryOp .mulWithOverflow
          (.constant ⟨ocjU16Ty, .scalar (BitVec.ofNat 128 40000)⟩)
          (.constant ⟨ocjU16Ty, .scalar (BitVec.ofNat 128 2)⟩)),
        .assign ⟨1, []⟩ (.binaryOp .mulUnchecked
          (.constant ⟨ocjU16Ty, .scalar (BitVec.ofNat 128 40000)⟩)
          (.constant ⟨ocjU16Ty, .scalar (BitVec.ofNat 128 2)⟩))
      ]
      terminator := .return_
      cleanup := false
    }]
    isUnsafe := false
    identity := "overflow_cast_join::neg_unchecked_overflow_fault"
  }

/-- `Body` executing narrowing `Cast(.intToInt, 256u16, char)` (rejected by
`Trusted.MirSemantics.evalIntToIntCast` because `256 > 255` fails the
`u8::try_from` range gate). -/
@[expose] def bodyIntToIntCharFault : Body :=
  {
    argumentCount := 0
    locals := [.char]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.cast .intToInt
          (.constant ⟨ocjU16Ty, .scalar (BitVec.ofNat 128 256)⟩) .char)
      ]
      terminator := .return_
      cleanup := false
    }]
    isUnsafe := false
    identity := "overflow_cast_join::neg_int_to_int_char_fault"
  }

/-- `Program` wrapper for `bodyWithOverflowOnly`. -/
@[expose] def progWithOverflowOnly : Program :=
  { bodies := [bodyWithOverflowOnly], entryDefId := 0,
    pointerWidthBits := 64, mirProfileVersion := 1, scope := .unit }

/-- `Program` wrapper for `bodyWithOverflowThenUncheckedFault`. -/
@[expose] def progUncheckedOverflowFault : Program :=
  { bodies := [bodyWithOverflowThenUncheckedFault], entryDefId := 0,
    pointerWidthBits := 64, mirProfileVersion := 1, scope := .unit }

/-- `Program` wrapper for `bodyIntToIntCharFault`. -/
@[expose] def progIntToIntCharFault : Program :=
  { bodies := [bodyIntToIntCharFault], entryDefId := 0,
    pointerWidthBits := 64, mirProfileVersion := 1, scope := .unit }

/-- Verifies `40000u16 * 2u16` under `BinOp.mulWithOverflow` wraps to `14464u16`
and sets the overflow boolean to `true` without faulting. -/
theorem canary_withOverflow_sets_true_without_fault :
    PositiveCanaryClaim progWithOverflowOnly { args := [] }
      (.tuple [ocjU16Val 14464, .bool true]) :=
  positiveCanary_of_exec (fuel := 2) rfl

/-- Verifies `40000u16 * 2u16` under `BinOp.mulUnchecked` faults with
`.undefined` (and never `.unsupported`), refuting `WellFormed`. -/
theorem canary_neg_unchecked_overflow_faults :
    NegativeCanaryClaim progUncheckedOverflowFault { args := [] }
      .undefined .unsupported :=
  negativeCanary_of_execFault (fuel := 2)
    (fun h => FaultKind.noConfusion h) rfl

/-- Verifies `Cast(.intToInt, 256u16, .char)` faults with `.unsupported` (and
never `.undefined`). -/
theorem canary_neg_intToInt_char_overflow_faults :
    NegativeCanaryClaim progIntToIntCharFault { args := [] }
      .unsupported .undefined :=
  negativeCanary_of_execFault (fuel := 1)
    (fun h => FaultKind.noConfusion h) rfl

/-- Single-cause fail-closed negative guard regressions covering all 10
conjuncts of `stageLocalIdsWf` and `evalIntToIntCastComp`. -/
theorem canary_overflowCastJoin_negative_guards :
    -- 1. Out-of-bounds `accId` (`13 >= 13`) rejected
    stageLocalIdsWf ⟨13, 10, 11, 12⟩ 13 = false ∧
    -- 2. Out-of-bounds `tmpId` (`13 >= 13`) rejected
    stageLocalIdsWf ⟨9, 13, 11, 12⟩ 13 = false ∧
    -- 3. Out-of-bounds `ovfMulId` (`13 >= 13`) rejected
    stageLocalIdsWf ⟨9, 10, 13, 12⟩ 13 = false ∧
    -- 4. Out-of-bounds `ovfAddId` (`13 >= 13`) rejected
    stageLocalIdsWf ⟨9, 10, 11, 13⟩ 13 = false ∧
    -- 5. Aliased `accId == tmpId` rejected
    stageLocalIdsWf ⟨9, 9, 11, 12⟩ 13 = false ∧
    -- 6. Aliased `accId == ovfMulId` rejected
    stageLocalIdsWf ⟨9, 10, 9, 12⟩ 13 = false ∧
    -- 7. Aliased `accId == ovfAddId` rejected
    stageLocalIdsWf ⟨9, 10, 11, 9⟩ 13 = false ∧
    -- 8. Aliased `tmpId == ovfMulId` rejected
    stageLocalIdsWf ⟨9, 10, 10, 12⟩ 13 = false ∧
    -- 9. Aliased `tmpId == ovfAddId` rejected
    stageLocalIdsWf ⟨9, 10, 11, 10⟩ 13 = false ∧
    -- 10. Aliased `ovfMulId == ovfAddId` rejected
    stageLocalIdsWf ⟨9, 10, 11, 11⟩ 13 = false ∧
    -- 11. `evalIntToIntCastComp` accepts `255 -> .char` (`u8::MAX`)
    evalIntToIntCastComp (ocjU16Val 255) .char = .ok (.char (Char.ofNat 255)) ∧
    -- 12. `evalIntToIntCastComp` rejects `256 -> .char` with `.unsupported`
    evalIntToIntCastComp (ocjU16Val 256) .char = .error .unsupported ∧
    -- 13. `evalIntToIntCastComp` rejects non-int-like `.unit` source
    evalIntToIntCastComp .unit ocjU16Ty = .error .unsupported :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.OverflowCastJoin

end
