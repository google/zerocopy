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
public import Init.Data.Nat.Bitwise.Basic
public import Init.Data.List.Basic
public import Init.SimpLemmas
public import Init.Control.Except
public import Trusted
public import Trusted.MirAst
public import Trusted.MirModel
public import Trusted.MirSemantics
public import Anneal.MirWp
public import Anneal.MirTotal.ExecTotal

public section

namespace Anneal.MirTotal

open Trusted.MirAst Trusted.MirSemantics

/-!
# Canaries and Negative Guards for `Anneal.MirTotal` (`MirTotal.Canaries`)

Kernel-checked positive and negative verification witnesses exercising:
1. Unbounded nested-reference type agreement (`∀ d : Nat`, including depth-17
   `ty17` where bounded `evalMirStepAt 16` diverges to `.fault .unsupported`
   while both `evalMirStepTotal` and `Trusted.MirSemantics.evalStep` step to
   `.fault .undefined`);
2. Premise-free `wpFaultState_of_evalMirFuelTotal` on non-Profile-v1 local types
   (`isSupportedScalarOrUnitTy ty17 = false`);
3. `BodyVerified` and `wpFaultProg` adequacy bridges on overflowing and
   unchecked integer arithmetic (`addWithOverflow` vs. `addUnchecked`); and
4. Negative fail-closed rejection across mismatched nested types, ill-typed
   casts, unaligned or shared-allocation writes, dead-local reads, and cleanup
   `.return_` terminators.
-/

/-- Constructs a `d`-fold nested shared reference `.ref .shared (... .unit)`. -/
@[expose] def tyNestedRef (d : Nat) : MirTy :=
  @Nat.rec (fun _ => MirTy) .unit (fun _ inner => .ref .shared inner) d

/-- Depth-17 nested shared reference around `.unit` (AST depth 18). -/
@[expose] def ty17 : MirTy := tyNestedRef 17

/-- Depth-16 nested shared reference around `.unit` (AST depth 17). -/
@[expose] def ty16 : MirTy := tyNestedRef 16

/-- Single-statement MIR program copying local `1` (`srcTy`) into local `0`
(`dstTy`). -/
@[expose] def mkProgNestedRefPair (dstTy srcTy : MirTy) : Program :=
  { bodies :=
      [{ identity := "mir_total::nested_ref_uninit"
         argumentCount := 0
         locals := [dstTy, srcTy]
         basicBlocks :=
           [{ statements := [.assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))]
              terminator := .return_
              cleanup := false }] }]
    entryDefId := 0
    scope := .unit
    pointerWidthBits := 64
    mirProfileVersion := 1 }

/-- Single-statement MIR program copying uninitialized depth-`d` nested
references (`tyNestedRef d`). -/
@[expose] def mkProgNestedRefUninit (d : Nat) : Program :=
  mkProgNestedRefPair (tyNestedRef d) (tyNestedRef d)

/-- Depth-17 instantiation of `mkProgNestedRefUninit`. -/
@[expose] def progDepth17Uninit : Program :=
  mkProgNestedRefUninit 17

/-- Single-frame state with two live uninitialized immediate locals. -/
@[expose] def stateDepth17Uninit : State :=
  { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 0,
                 locals := [.immediate none, .immediate none] }]
    callerMem := ⟨[]⟩
    mem := entryMemoryComp }

/-- Verifies that `evalMirStepTotal` and `Trusted.MirSemantics.evalStep` both
return `.fault .undefined` across `ty16`, `ty17`, and universally `∀ d : Nat`
(whereas bounded `evalMirStepAt 16` diverges to `.fault .unsupported`), while
mismatched `[ty17, ty16]` fails closed with `.fault .unsupported` on both. -/
theorem depth17_nested_ref_uninit_matches_evalStep :
    MirTy.beq ty17 ty17 = true ∧
    mirTyBeqAt 16 ty17 ty17 = false ∧
    mirTyBeqAt 16 ty16 ty16 = false ∧
    mirTyBeqAt 18 ty17 ty17 = true ∧
    evalMirStepTotal progDepth17Uninit 0 stateDepth17Uninit = .fault .undefined ∧
    evalStep progDepth17Uninit 0 stateDepth17Uninit = .fault .undefined ∧
    evalMirStepTotal (mkProgNestedRefUninit 16) 0 stateDepth17Uninit = .fault .undefined ∧
    evalStep (mkProgNestedRefUninit 16) 0 stateDepth17Uninit = .fault .undefined ∧
    evalMirStepAt 16 progDepth17Uninit 0 stateDepth17Uninit = .fault .unsupported ∧
    evalMirStepAt 32 progDepth17Uninit 0 stateDepth17Uninit = .fault .undefined ∧
    evalMirStepTotal (mkProgNestedRefPair ty17 ty16) 0 stateDepth17Uninit = .fault .unsupported ∧
    evalStep (mkProgNestedRefPair ty17 ty16) 0 stateDepth17Uninit = .fault .unsupported ∧
    (∀ d : Nat,
      evalMirStepTotal (mkProgNestedRefUninit d) 0 stateDepth17Uninit = .fault .undefined ∧
      evalStep (mkProgNestedRefUninit d) 0 stateDepth17Uninit = .fault .undefined) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro d
  have hStep : evalStep (mkProgNestedRefUninit d) 0 stateDepth17Uninit = .fault .undefined := by
    have hRefl : MirTy.beq (tyNestedRef d) (tyNestedRef d) = true :=
      Anneal.MirWp.mirTy_beq_refl (tyNestedRef d)
    change (match (if !(MirTy.beq (tyNestedRef d) (tyNestedRef d)) then
        Except.error FaultKind.unsupported
      else
        (Except.error FaultKind.undefined :
          Except FaultKind (Val × List LocalSlot × MemoryState))) with
      | .error k => StepResult.fault k
      | .ok (val, localsAfterRval, memAfterRval) =>
        match writePlace localsAfterRval memAfterRval 0 (tyNestedRef d) val with
        | .error k => StepResult.fault k
        | .ok (localsAfterWrite, memAfterWrite) =>
          StepResult.step
            (State.mk [FrameState.mk 0 0 1 localsAfterWrite] (CallerMemory.mk []) memAfterWrite)) =
      StepResult.fault FaultKind.undefined
    rw [hRefl]
    rfl
  refine ⟨?_, hStep⟩
  rw [evalMirStepTotal_eq_evalStep]
  exact hStep

/-- Lifts `progDepth17Uninit` directly into `Anneal.MirWp.wpFaultState` with
zero local-type-support side condition (`isSupportedScalarOrUnitTy ty17 =
false`). -/
theorem depth17_nested_ref_wpFaultState :
    isSupportedScalarOrUnitTyComp ty17 = false ∧
    Anneal.MirWp.wpFaultState progDepth17Uninit 1 stateDepth17Uninit .undefined :=
  ⟨rfl, wpFaultState_of_evalMirFuelTotal rfl⟩

/-- Safe `u16` overflowing-addition canary (`40000 + 30000 = (4464, true)`). -/
@[expose] def canaryAddWithOverflowProg : Program :=
  { bodies :=
      [{ identity := "mir_total::canary_u16_add_with_overflow"
         argumentCount := 0
         locals := [.tuple [.int .i16 false, .bool]]
         basicBlocks :=
           [{ statements :=
                [.assign ⟨0, []⟩
                  (.binaryOp .addWithOverflow
                    (.constant ⟨.int .i16 false, .scalar (BitVec.ofNat 128 40000)⟩)
                    (.constant ⟨.int .i16 false, .scalar (BitVec.ofNat 128 30000)⟩))]
              terminator := .return_
              cleanup := false }] }]
    entryDefId := 0
    scope := .unit
    pointerWidthBits := 64
    mirProfileVersion := 1 }

/-- Faulting `u16` unchecked-addition overflow canary (`40000 + 30000`). -/
@[expose] def canaryUncheckedOverflowProg : Program :=
  { bodies :=
      [{ identity := "mir_total::canary_u16_unchecked_overflow"
         argumentCount := 0
         locals := [.int .i16 false]
         basicBlocks :=
           [{ statements :=
                [.assign ⟨0, []⟩
                  (.binaryOp .addUnchecked
                    (.constant ⟨.int .i16 false, .scalar (BitVec.ofNat 128 40000)⟩)
                    (.constant ⟨.int .i16 false, .scalar (BitVec.ofNat 128 30000)⟩))]
              terminator := .return_
              cleanup := false }] }]
    entryDefId := 0
    scope := .unit
    pointerWidthBits := 64
    mirProfileVersion := 1 }

/-- Discharges `BodyVerified` on `canaryAddWithOverflowProg` and `wpFaultProg`
(`.undefined`) on `canaryUncheckedOverflowProg` via `MirTotal.ExecTotal`. -/
theorem canary_entry_bridges_verified :
    (∀ b : Body, compGetElem? canaryAddWithOverflowProg.bodies 0 = some b →
      BodyVerified canaryAddWithOverflowProg 0 b (fun _ => True)) ∧
    Anneal.MirWp.wpFaultProg canaryUncheckedOverflowProg 1 { args := [] } .undefined := by
  refine ⟨?_, wpFaultProg_of_evalMirFuelTotal (s0 := {
      frames := [{ defId := 0, blockIdx := 0, stmtIdx := 0, locals := [.immediate none] }]
      callerMem := ⟨[]⟩
      mem := entryMemoryComp }) rfl rfl⟩
  intro b hb
  injection hb with hbEq
  subst hbEq
  refine bodyVerified_of_evalMirFuelTotal rfl rfl ?_
  intro args hArgs _
  cases args with
  | cons _ _ => cases hArgs
  | nil =>
    exact ⟨2,
      { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 0, locals := [.immediate none] }]
        callerMem := ⟨[]⟩
        mem := entryMemoryComp },
      .returned ⟨.tuple [.scalar ⟨.i16, false, BitVec.ofNat 128 4464⟩, .bool true], ⟨[]⟩⟩,
      rfl, rfl⟩

@[expose] def badCastBody : Body :=
  { identity := "g"
    argumentCount := 0
    locals := [.int .i8 false, .int .i16 false]
    basicBlocks :=
      [{ statements :=
           [.assign ⟨0, []⟩ (.cast .intToInt (.copy ⟨1, []⟩) (.int .i32 false))]
         terminator := .return_
         cleanup := false }] }

/-- Negative guard suite checking fail-closed `.undefined` and `.unsupported`
rejections across shared-allocation writes, unaligned accesses, `.uninit` loads,
dead-local reads, `StorageDead 0`, cleanup `.return_`, and ill-typed casts. -/
theorem mirTotal_negative_guards_tests :
    writeBytesComp
      { nextAllocId := 2, allocations := [⟨1, 2, .shared, [.init 0 none], true⟩] }
      ⟨1, 0⟩ 0 [.init 1 none] = .error .undefined ∧
    writeBytesComp
      { nextAllocId := 2
        allocations := [⟨1, 2, .mut, [.init 0 none, .init 0 none], true⟩] }
      ⟨1, 1⟩ 1 [.init 1 none] = .error .undefined ∧
    loadIndirectComp
      { nextAllocId := 2, allocations := [⟨1, 0, .mut, [.uninit], true⟩] }
      (.int .i8 false) ⟨1, 0⟩ = .ok none ∧
    evalStatementBy (mirTyBeqAt 8)
      { identity := "g", argumentCount := 0, locals := [.unit, .unit], basicBlocks := [] }
      { defId := 0, blockIdx := 0, stmtIdx := 0, locals := [.immediate (some .unit), .dead] }
      entryMemoryComp ⟨[]⟩ (.storageDead 0) = .fault .unsupported ∧
    evalOperandToSlotComp [.int .i32 false] [.dead] entryMemoryComp (fun _ => true)
      (.copy ⟨0, []⟩) = .error .undefined ∧
    evalTerminatorComp
      { identity := "g", argumentCount := 0, locals := [.unit], basicBlocks := [] }
      { statements := [], terminator := .return_, cleanup := true }
      { defId := 0, blockIdx := 0, stmtIdx := 0, locals := [.immediate (some .unit)] }
      entryMemoryComp ⟨[]⟩ = .fault .unsupported ∧
    castTypesValidBy (mirTyBeqAt 8) badCastBody = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.MirTotal

end
