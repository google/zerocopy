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
    change attachCallers [] (match (if !(MirTy.beq (tyNestedRef d) (tyNestedRef d)) then
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
            (State.mk [FrameState.mk 0 0 1 localsAfterWrite none none none]
              (CallerMemory.mk []) memAfterWrite)) =
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

/-- Direct intra-crate `.call` multi-frame canary (`caller(0)` calls
`callee(1)`). -/
def canaryDirectCallProg : Program :=
  { bodies :=
      [{ identity := "mir_total::canary_caller"
         argumentCount := 0
         locals := [.int .i16 false]
         basicBlocks :=
           [{ statements := []
              terminator := .call 1
                [.constant ⟨.int .i16 false, .scalar (BitVec.ofNat 128 19)⟩]
                ⟨0, []⟩ (some 1) .continue_
              cleanup := false },
            { statements := []
              terminator := .return_
              cleanup := false }] },
       { identity := "mir_total::canary_callee"
         argumentCount := 1
         locals := [.int .i16 false, .int .i16 false]
         basicBlocks :=
           [{ statements :=
                [.assign ⟨0, []⟩
                  (.binaryOp .add (.copy ⟨1, []⟩)
                    (.constant ⟨.int .i16 false, .scalar (BitVec.ofNat 128 23)⟩))]
              terminator := .return_
              cleanup := false }] }]
    entryDefId := 0
    scope := .unit
    pointerWidthBits := 64
    mirProfileVersion := 1 }

/-- `SysrootCall` `u16::unchecked_mul` positive canary (`6 * 7 = 42`). -/
def canarySysrootUncheckedMulOkProg : Program :=
  { bodies :=
      [{ identity := "mir_total::canary_sysroot_unchecked_mul_ok"
         argumentCount := 0
         locals := [.int .i16 false]
         basicBlocks :=
           [{ statements := []
              terminator := .sysrootCall
                { kind := .uncheckedMul, width := .i16, signed := false }
                [.constant ⟨.int .i16 false, .scalar (BitVec.ofNat 128 6)⟩,
                 .constant ⟨.int .i16 false, .scalar (BitVec.ofNat 128 7)⟩]
                ⟨0, []⟩ (some 1) .continue_
              cleanup := false },
            { statements := []
              terminator := .return_
              cleanup := false }] }]
    entryDefId := 0
    scope := .unit
    pointerWidthBits := 64
    mirProfileVersion := 1 }

/-- `SysrootCall` `u16::unchecked_mul` overflow UB canary (`400 * 300`). -/
def canarySysrootUncheckedMulUbProg : Program :=
  { bodies :=
      [{ identity := "mir_total::canary_sysroot_unchecked_mul_ub"
         argumentCount := 0
         locals := [.int .i16 false]
         basicBlocks :=
           [{ statements := []
              terminator := .sysrootCall
                { kind := .uncheckedMul, width := .i16, signed := false }
                [.constant ⟨.int .i16 false, .scalar (BitVec.ofNat 128 400)⟩,
                 .constant ⟨.int .i16 false, .scalar (BitVec.ofNat 128 300)⟩]
                ⟨0, []⟩ (some 1) .continue_
              cleanup := false },
            { statements := []
              terminator := .return_
              cleanup := false }] }]
    entryDefId := 0
    scope := .unit
    pointerWidthBits := 64
    mirProfileVersion := 1 }

/-- Discharges direct `.call` and `.sysrootCall` positive and negative entry
canaries via `MirTotal.ExecTotal`. -/
theorem canary_calls_verified :
    (∀ b : Body, compGetElem? canaryDirectCallProg.bodies 0 = some b →
      BodyVerified canaryDirectCallProg 0 b (fun _ => True)) ∧
    Anneal.MirWp.wpProg canaryDirectCallProg 4 { args := [] } (fun out =>
      out = .returned ⟨.scalar ⟨.i16, false, BitVec.ofNat 128 42⟩, ⟨[]⟩⟩) ∧
    (∀ b : Body, compGetElem? canarySysrootUncheckedMulOkProg.bodies 0 = some b →
      BodyVerified canarySysrootUncheckedMulOkProg 0 b (fun _ => True)) ∧
    Anneal.MirWp.wpProg canarySysrootUncheckedMulOkProg 4 { args := [] } (fun out =>
      out = .returned ⟨.scalar ⟨.i16, false, BitVec.ofNat 128 42⟩, ⟨[]⟩⟩) ∧
    Anneal.MirWp.wpFaultProg canarySysrootUncheckedMulUbProg 2 { args := [] }
      .undefined := by
  refine ⟨?_, wpProg_of_evalMirFuelTotal (s0 := {
      frames := [{ defId := 0, blockIdx := 0, stmtIdx := 0, locals := [.immediate none] }]
      callerMem := ⟨[]⟩
      mem := entryMemoryComp }) rfl rfl rfl,
    ?_, wpProg_of_evalMirFuelTotal (s0 := {
      frames := [{ defId := 0, blockIdx := 0, stmtIdx := 0, locals := [.immediate none] }]
      callerMem := ⟨[]⟩
      mem := entryMemoryComp }) rfl rfl rfl,
    wpFaultProg_of_evalMirFuelTotal (s0 := {
      frames := [{ defId := 0, blockIdx := 0, stmtIdx := 0, locals := [.immediate none] }]
      callerMem := ⟨[]⟩
      mem := entryMemoryComp }) rfl rfl⟩
  · intro b hb
    injection hb with hbEq; subst hbEq
    refine bodyVerified_of_evalMirFuelTotal rfl rfl ?_
    intro args hArgs _
    cases args with
    | cons _ _ => cases hArgs
    | nil =>
      exact ⟨4,
        { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 0, locals := [.immediate none] }]
          callerMem := ⟨[]⟩
          mem := entryMemoryComp },
        .returned ⟨.scalar ⟨.i16, false, BitVec.ofNat 128 42⟩, ⟨[]⟩⟩,
        rfl, rfl⟩
  · intro b hb
    injection hb with hbEq; subst hbEq
    refine bodyVerified_of_evalMirFuelTotal rfl rfl ?_
    intro args hArgs _
    cases args with
    | cons _ _ => cases hArgs
    | nil =>
      exact ⟨4,
        { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 0, locals := [.immediate none] }]
          callerMem := ⟨[]⟩
          mem := entryMemoryComp },
        .returned ⟨.scalar ⟨.i16, false, BitVec.ofNat 128 42⟩, ⟨[]⟩⟩,
        rfl, rfl⟩

/-- Safe unsigned division program exercising `TerminatorKind.assert`:
`if b == 0 { 0 } else { assert(!(b == 0)); a / b }`. -/
@[expose] def progSafeDivAssert : Program :=
  { bodies :=
      [{ identity := "mir_total::safe_div_assert"
         argumentCount := 2
         locals := [.int .i32 false, .int .i32 false, .int .i32 false, .bool]
         basicBlocks :=
           [{ statements :=
                [.assign ⟨3, []⟩
                  (.binaryOp .eq (.copy ⟨2, []⟩)
                    (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 0)⟩))]
              terminator := .switchInt (.copy ⟨3, []⟩) ⟨[(BitVec.ofNat 128 0, 2)], 1⟩
              cleanup := false },
            { statements :=
                [.assign ⟨0, []⟩
                  (.use (.constant ⟨.int .i32 false, .scalar (BitVec.ofNat 128 0)⟩))]
              terminator := .return_
              cleanup := false },
            { statements := []
              terminator := .assert (.copy ⟨3, []⟩) false .divByZero 3 .continue_
              cleanup := false },
            { statements :=
                [.assign ⟨0, []⟩ (.binaryOp .div (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))]
              terminator := .return_
              cleanup := false }] }]
    entryDefId := 0
    scope := .unit
    pointerWidthBits := 64
    mirProfileVersion := 1 }

/-- Verifies Profile v1 passing `Assert` (`20 / 4 = 5`), zero-guard bypass
(`20 / 0 = 0`), failing `.divByZero` under `.unwind` (`.fault .unsupported`),
non-`.bool` condition rejection (`i8` and `i32` scalars ->
`.fault .unsupported`), failing `.nullPtrDeref` and `.misalignedPtrDeref` under
`.abort` (`.fault .undefined`), and failing optional `.overflow .add` under
`.abort` (`.fault .unsupported`) through `evalMirFuelTotal`,
`evalTerminatorComp`, and `evalStep`, together with a Profile v2
(`mirProfileVersion := 2`, `panicStrategy := .abort`,
`hasLocalPanicHandler := false`) failing `.divByZero` transition reaching
`.done (.aborted ⟨[]⟩)` via `evalStepV2` and `Anneal.MirWp.execProgV2`. -/
theorem assert_terminator_positive_and_negative_canaries :
    evalMirFuelTotal progSafeDivAssert 8
      { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 0,
                     locals := [.immediate none,
                       .immediate (some (.scalar ⟨.i32, false, BitVec.ofNat 128 20⟩)),
                       .immediate (some (.scalar ⟨.i32, false, BitVec.ofNat 128 4⟩)),
                       .immediate none] }]
        callerMem := ⟨[]⟩
        mem := entryMemoryComp } =
      .done (.returned ⟨.scalar ⟨.i32, false, BitVec.ofNat 128 5⟩, ⟨[]⟩⟩) ∧
    evalMirFuelTotal progSafeDivAssert 8
      { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 0,
                     locals := [.immediate none,
                       .immediate (some (.scalar ⟨.i32, false, BitVec.ofNat 128 20⟩)),
                       .immediate (some (.scalar ⟨.i32, false, BitVec.ofNat 128 0⟩)),
                       .immediate none] }]
        callerMem := ⟨[]⟩
        mem := entryMemoryComp } =
      .done (.returned ⟨.scalar ⟨.i32, false, BitVec.ofNat 128 0⟩, ⟨[]⟩⟩) ∧
    evalTerminatorComp
      { identity := "a", argumentCount := 0, locals := [.unit, .bool], basicBlocks := [] }
      { statements := [], terminator := .assert (.copy ⟨1, []⟩) false .divByZero 0 .continue_,
        cleanup := false }
      { defId := 0, blockIdx := 0, stmtIdx := 0,
        locals := [.immediate (some .unit), .immediate (some (.bool true))] }
      entryMemoryComp ⟨[]⟩ = .fault .unsupported ∧
    evalTerminatorComp
      { identity := "a", argumentCount := 0, locals := [.unit, .int .i8 false],
        basicBlocks := [] }
      { statements := [], terminator := .assert (.copy ⟨1, []⟩) false .divByZero 0 .continue_,
        cleanup := false }
      { defId := 0, blockIdx := 0, stmtIdx := 0,
        locals := [.immediate (some .unit),
          .immediate (some (.scalar ⟨.i8, false, BitVec.ofNat 128 2⟩))] }
      entryMemoryComp ⟨[]⟩ = .fault .unsupported ∧
    evalTerminatorComp
      { identity := "a", argumentCount := 0, locals := [.unit, .int .i32 false],
        basicBlocks := [] }
      { statements := [], terminator := .assert (.copy ⟨1, []⟩) false .divByZero 0 .continue_,
        cleanup := false }
      { defId := 0, blockIdx := 0, stmtIdx := 0,
        locals := [.immediate (some .unit),
          .immediate (some (.scalar ⟨.i32, false, BitVec.ofNat 128 0⟩))] }
      entryMemoryComp ⟨[]⟩ = .fault .unsupported ∧
    evalTerminatorComp
      { identity := "a", argumentCount := 0, locals := [.unit, .bool], basicBlocks := [] }
      { statements := [], terminator := .assert (.copy ⟨1, []⟩) true .nullPtrDeref 0 .unreachable,
        cleanup := false }
      { defId := 0, blockIdx := 0, stmtIdx := 0,
        locals := [.immediate (some .unit), .immediate (some (.bool false))] }
      entryMemoryComp ⟨[]⟩ .abort false = .fault .undefined ∧
    evalTerminatorComp
      { identity := "a", argumentCount := 0, locals := [.unit, .bool], basicBlocks := [] }
      { statements := [],
        terminator := .assert (.copy ⟨1, []⟩) true .misalignedPtrDeref 0 .unreachable,
        cleanup := false }
      { defId := 0, blockIdx := 0, stmtIdx := 0,
        locals := [.immediate (some .unit), .immediate (some (.bool false))] }
      entryMemoryComp ⟨[]⟩ .abort false = .fault .undefined ∧
    evalTerminatorComp
      { identity := "a", argumentCount := 0, locals := [.unit, .bool], basicBlocks := [] }
      { statements := [],
        terminator := .assert (.copy ⟨1, []⟩) true (.overflow .add) 0 .unreachable,
        cleanup := false }
      { defId := 0, blockIdx := 0, stmtIdx := 0,
        locals := [.immediate (some .unit), .immediate (some (.bool false))] }
      entryMemoryComp ⟨[]⟩ .abort false = .fault .unsupported ∧
    evalStep
      { bodies :=
          [{ identity := "a", argumentCount := 0, locals := [.unit, .bool],
             basicBlocks :=
               [{ statements := [],
                  terminator := .assert (.copy ⟨1, []⟩) false .divByZero 0 .continue_,
                  cleanup := false }] }]
        entryDefId := 0, scope := .unit, pointerWidthBits := 64, mirProfileVersion := 1 }
      0
      { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 0,
                     locals := [.immediate (some .unit), .immediate (some (.bool true))] }]
        callerMem := ⟨[]⟩, mem := entryMemoryComp } = .fault .unsupported ∧
    evalStepV2
      { bodies :=
          [{ identity := "a", argumentCount := 1, locals := [.unit, .bool],
             basicBlocks :=
               [{ statements := [],
                  terminator := .assert (.copy ⟨1, []⟩) false .divByZero 0 .unreachable,
                  cleanup := false }] }]
        entryDefId := 0, scope := .unit, pointerWidthBits := 64, mirProfileVersion := 2,
        panicStrategy := .abort, hasLocalPanicHandler := false }
      { frames := [{ defId := 0, blockIdx := 0, stmtIdx := 0,
                     locals := [.immediate none, .immediate (some (.bool true))] }]
        callerMem := ⟨[]⟩, mem := entryMemoryComp } = .done (.aborted ⟨[]⟩) ∧
    Anneal.MirWp.execProgV2
      { bodies :=
          [{ identity := "a", argumentCount := 1, locals := [.unit, .bool],
             basicBlocks :=
               [{ statements := [],
                  terminator := .assert (.copy ⟨1, []⟩) false .divByZero 0 .unreachable,
                  cleanup := false }] }]
        entryDefId := 0, scope := .unit, pointerWidthBits := 64, mirProfileVersion := 2,
        panicStrategy := .abort, hasLocalPanicHandler := false }
      1 { args := [.bool true] } (fun out => out = .aborted ⟨[]⟩) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.MirTotal

end
