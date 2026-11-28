-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import GuardRefuteWf
import PositiveSanity

/-!
# Negative Refutations for `Trusted.MirSemantics.Step` UB Guards

Covers every `.undefined` branch and move-deinitialization guard in
`Trusted/MirSemantics/Step.lean`: dead-local copy/move/discriminant/write/
forceAllocation, use-after-move on immediate and indirect locals, uninitialized
primitive/use/cast/discriminant/return reads, `TerminatorKind.unreachable`,
and `TerminatorKind.assert` guards.
-/

namespace GuardMutation

open Trusted.MirAst Trusted.MirSemantics

/-- Program reading a dead `.unit` local via `Operand.copy`. Using `.unit`
ensures the weakened mutant returns a type-compatible `Val.unit` rather than
failing a downstream type check. -/
noncomputable def progCopyDeadLocal : Program :=
  mkSingleBlockProg 0 [.unit, .unit]
    [.storageLive 1, .storageDead 1, .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))]

/-- Guard `step_copy_dead_local`: `Operand.copy` on a `.dead` local faults
with `.undefined`. -/
theorem refute_step_copy_dead_local :
    ReachesResult progCopyDeadLocal queryEmpty (.fault .undefined) ∧
    ¬ WellFormed progCopyDeadLocal queryEmpty :=
  refutes_wf_of_execFault (fuel := 3) rfl

/-- Program reading a dead `.unit` local via `Operand.move`. -/
noncomputable def progMoveDeadLocal : Program :=
  mkSingleBlockProg 0 [.unit, .unit]
    [.storageLive 1, .storageDead 1, .assign ⟨0, []⟩ (.use (.move ⟨1, []⟩))]

/-- Guard `step_move_dead_local`: `Operand.move` on a `.dead` local faults
with `.undefined`. -/
theorem refute_step_move_dead_local :
    ReachesResult progMoveDeadLocal queryEmpty (.fault .undefined) ∧
    ¬ WellFormed progMoveDeadLocal queryEmpty :=
  refutes_wf_of_execFault (fuel := 3) rfl

/-- Guard `step_move_deinit_immediate`: moving out of an immediate non-ZST
local deinitializes it so a second read faults with `.undefined`. -/
theorem refute_step_move_deinit_immediate :
    ReachesResult progUseAfterMove { args := [u32Val 7] } (.fault .undefined) ∧
    ¬ WellFormed progUseAfterMove { args := [u32Val 7] } :=
  refutes_wf_of_execFault (fuel := 2) rfl

/-- Guard `step_move_deinit_indirect`: moving out of an `.indirect` non-ZST
local marks its memory bytes uninitialized so a subsequent read faults with
`.undefined`. -/
theorem refute_step_move_deinit_indirect :
    (match initState progUseAfterMove { args := [u32Val 7] } with
     | .ok s₀ =>
       match forceAllocation progUseAfterMove s₀ 1 with
       | .ok (s₁, _) =>
         match evalStep progUseAfterMove 0 s₁ with
         | .step s₂ =>
           evalStep progUseAfterMove 0 s₂ = .fault .undefined
         | _ => False
       | .error _ => False
     | .error _ => False) :=
  rfl

/-- Program applying `UnOp.not` to an uninitialized `bool` local. -/
noncomputable def progPrimUninitRead : Program :=
  mkSingleBlockProg 0 [.bool, .bool]
    [.storageLive 1, .assign ⟨0, []⟩ (.unaryOp .not (.copy ⟨1, []⟩))]

/-- Guard `step_prim_uninit_read`: `evalPrimitiveOperand` on an uninitialized
local faults with `.undefined`. -/
theorem refute_step_prim_uninit_read :
    ReachesResult progPrimUninitRead queryEmpty (.fault .undefined) ∧
    ¬ WellFormed progPrimUninitRead queryEmpty :=
  refutes_wf_of_execFault (fuel := 2) rfl

/-- Program reading `Rvalue.discriminant` of an uninitialized scalar-tagged
enum local. -/
noncomputable def progDiscrUninitEnum : Program :=
  mkSingleBlockProg 0 [u8Ty, .enum reprU8EnumTy]
    [.storageLive 1, .assign ⟨0, []⟩ (.discriminant ⟨1, []⟩)]

/-- Guard `step_discriminant_uninit_enum`: `evalDiscriminantOfVal` on an
uninitialized scalar-tagged enum faults with `.undefined`. -/
theorem refute_step_discriminant_uninit_enum :
    ReachesResult progDiscrUninitEnum queryEmpty (.fault .undefined) ∧
    ¬ WellFormed progDiscrUninitEnum queryEmpty :=
  refutes_wf_of_execFault (fuel := 2) rfl

/-- Program reading `Rvalue.discriminant` of an uninitialized `Ordering`
local. -/
noncomputable def progDiscrUninitOrdering : Program :=
  mkSingleBlockProg 0 [i8Ty, .ordering]
    [.storageLive 1, .assign ⟨0, []⟩ (.discriminant ⟨1, []⟩)]

/-- Guard `step_discriminant_uninit_ordering`: `evalOrderingDiscriminantOfVal`
on an uninitialized `Ordering` faults with `.undefined`. -/
theorem refute_step_discriminant_uninit_ordering :
    ReachesResult progDiscrUninitOrdering queryEmpty (.fault .undefined) ∧
    ¬ WellFormed progDiscrUninitOrdering queryEmpty :=
  refutes_wf_of_execFault (fuel := 2) rfl

/-- Program copying an uninitialized `bool` local into `_0 : bool`. -/
noncomputable def progUseUninitRead : Program :=
  mkSingleBlockProg 0 [.bool, .bool]
    [.storageLive 1, .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))]

/-- Guard `step_use_uninit_read`: `evalRvalue .use` on an uninitialized local
faults with `.undefined`. -/
theorem refute_step_use_uninit_read :
    ReachesResult progUseUninitRead queryEmpty (.fault .undefined) ∧
    ¬ WellFormed progUseUninitRead queryEmpty :=
  refutes_wf_of_execFault (fuel := 2) rfl

/-- Program casting an uninitialized `u8` local to `u32`. -/
noncomputable def progCastUninitRead : Program :=
  mkSingleBlockProg 0 [u32Ty, u8Ty]
    [.storageLive 1, .assign ⟨0, []⟩ (.cast .intToInt (.copy ⟨1, []⟩) u32Ty)]

/-- Guard `step_cast_uninit_read`: `evalRvalue (.cast .intToInt)` on an
uninitialized source local faults with `.undefined`. -/
theorem refute_step_cast_uninit_read :
    ReachesResult progCastUninitRead queryEmpty (.fault .undefined) ∧
    ¬ WellFormed progCastUninitRead queryEmpty :=
  refutes_wf_of_execFault (fuel := 2) rfl

/-- Program reading `Rvalue.discriminant` from a `.dead` `Ordering` local. -/
noncomputable def progDiscrDeadLocal : Program :=
  mkSingleBlockProg 0 [i8Ty, .ordering]
    [.storageLive 1, .storageDead 1, .assign ⟨0, []⟩ (.discriminant ⟨1, []⟩)]

/-- Guard `step_discriminant_dead_local`: `evalRvalue .discriminant` on a
`.dead` local faults with `.undefined`. -/
theorem refute_step_discriminant_dead_local :
    ReachesResult progDiscrDeadLocal queryEmpty (.fault .undefined) ∧
    ¬ WellFormed progDiscrDeadLocal queryEmpty :=
  refutes_wf_of_execFault (fuel := 3) rfl

/-- Program writing a constant into a `.dead` local. -/
noncomputable def progWriteDeadLocal : Program :=
  mkSingleBlockProg 0 [.unit, u32Ty]
    [.storageLive 1, .storageDead 1,
     .assign ⟨1, []⟩ (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 1)⟩))]

/-- Guard `step_write_dead_local`: `writePlace` on a `.dead` destination local
faults with `.undefined`. -/
theorem refute_step_write_dead_local :
    ReachesResult progWriteDeadLocal queryEmpty (.fault .undefined) ∧
    ¬ WellFormed progWriteDeadLocal queryEmpty :=
  refutes_wf_of_execFault (fuel := 3) rfl

/-- Guard `step_return_uninit_or_dead`: `TerminatorKind.return_` with an
uninitialized immediate `_0` faults with `.undefined`. -/
theorem refute_step_return_uninit_or_dead :
    ReachesResult progReturnUninit queryEmpty (.fault .undefined) ∧
    ¬ WellFormed progReturnUninit queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `step_return_indirect_uninit`: `TerminatorKind.return_` with an
uninitialized `.indirect` `_0` faults with `.undefined`. -/
theorem refute_step_return_indirect_uninit :
    (match initState progReturnUninit queryEmpty with
     | .ok s₀ =>
       match forceAllocation progReturnUninit s₀ 0 with
       | .ok (s₁, _) =>
         evalStep progReturnUninit 0 s₁ = .fault .undefined
       | .error _ => False
     | .error _ => False) :=
  rfl

/-- Program executing `TerminatorKind.unreachable`. -/
noncomputable def progUnreachable : Program :=
  mkSingleBlockProg 0 [.unit] [] .unreachable

/-- Guard `step_unreachable_terminator`: `TerminatorKind.unreachable` faults
with `.undefined`. -/
theorem refute_step_unreachable_terminator :
    ReachesResult progUnreachable queryEmpty (.fault .undefined) ∧
    ¬ WellFormed progUnreachable queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `step_force_alloc_dead_local`: `forceAllocation` on a `.dead` local
faults with `.undefined`. -/
theorem refute_step_force_alloc_dead_local :
    (match initState progDeadLocalForForceAlloc queryEmpty with
     | .ok s₀ =>
       match forceAllocation progDeadLocalForForceAlloc s₀ 1 with
       | .error .undefined => True
       | _ => False
     | .error _ => False) :=
  trivial

/-- Guard `step_v2_write_readonly`: storing through `*const u8`
(`ptrMut = .shared`) into a live `.mut` allocation faults with `.undefined`. -/
theorem refute_step_v2_write_readonly :
    (match writePlaceV2
        [.unit, .rawPtr .shared (.int .i8 false)]
        [.immediate (some .unit), .immediate (some (.ptr ⟨some 1, 0, .isize⟩))]
        { allocations := [{
            allocId := 1
            alignLog2 := 0
            mutability := .mut
            bytes := [.init 0 none]
            live := true
          }], nextAllocId := 2 }
        { localId := 1, projection := [.deref] }
        (.int .i8 false)
        (.scalar ⟨.i8, false, BitVec.ofNat 128 7⟩) with
     | .error .undefined => True
     | _ => False) :=
  trivial

/-- Guard `step_v2_return_dangling_stack_ref`: returning a reference to a
callee-allocated stack local faults with `.undefined`. -/
theorem refute_step_v2_return_dangling_stack_ref :
    (match initStateV2 progDanglingStackRefV2
        { args := [.scalar ⟨.i8, false, BitVec.ofNat 128 42⟩] } with
     | .ok s₀ =>
       match evalStepV2 progDanglingStackRefV2 s₀ with
       | .step s₁ =>
         match evalStepV2 progDanglingStackRefV2 s₁ with
         | .fault .undefined => True
         | _ => False
       | _ => False
     | .error _ => False) :=
  trivial

/-- Guard `step_v2_offset_dst_type`: `Offset` on a `*const u8` operand fails
closed when the destination local has a different raw-pointer type
(`*mut u64`). -/
theorem refute_step_v2_offset_dst_type :
    (match evalRvalueV2
        [.unit, .rawPtr .shared (.int .i8 false), .rawPtr .mut (.int .i64 false)]
        [.immediate (some .unit), .immediate (some (.ptr ⟨some 1, 0, .isize⟩)),
          .immediate none]
        { allocations := [{
            allocId := 1
            alignLog2 := 0
            mutability := .mut
            bytes := [.init 0 none, .init 0 none]
            live := true
          }], nextAllocId := 2 }
        (.rawPtr .mut (.int .i64 false))
        (.binaryOp .offset (.copy { localId := 1, projection := [] })
          (.constant ⟨.int .isize true, .scalar (BitVec.ofNat 128 1)⟩)) with
     | .error .unsupported => True
     | _ => False) :=
  trivial

/-- Guard `step_v2_ptr_cast_const_to_mut`: `PtrToPtr` casts from `*const u32`
to `*mut u32` and from `*const [u8]` to `*mut [u8]` fail closed, so
`&raw const x as *mut u32` cannot write to an immutable binding `x`. -/
theorem refute_step_v2_ptr_cast_const_to_mut :
    (match evalRvalueV2
        [.unit, .rawPtr .shared (.int .i32 false), .rawPtr .mut (.int .i32 false)]
        [.immediate (some .unit), .immediate (some (.ptr ⟨some 1, 0, .isize⟩)),
          .immediate none]
        { allocations := [{
            allocId := 1
            alignLog2 := 2
            mutability := .mut
            bytes := List.replicate 4 (.init 0 none)
            live := true
          }], nextAllocId := 2 }
        (.rawPtr .mut (.int .i32 false))
        (.cast .ptrToPtr (.copy { localId := 1, projection := [] })
          (.rawPtr .mut (.int .i32 false))) with
     | .error .unsupported => True
     | _ => False) ∧
    (match evalPtrToPtrCastV2 (.rawPtr .shared (.slice (.int .i8 false)))
        (.slicePtr ⟨some 1, 0, .isize⟩ 4) (.rawPtr .mut (.slice (.int .i8 false))) with
     | .error .unsupported => True
     | _ => False) :=
  ⟨trivial, trivial⟩

/-- Guard `step_v2_get_unchecked_range_to_in_mut`: `get_unchecked(..1)` on a
`&mut [u8]` input over a `.shared` allocation faults with `.undefined` even
though the result is `&[u8]`, because the input is validated at its own
mutability. -/
theorem refute_step_v2_get_unchecked_range_to_in_mut :
    (match execCoreCallOp sharedInit2Mem .sliceGetUncheckedRangeTo
        [(.ref .mut (.slice (.int .i8 false)), .slicePtr ⟨some 1, 0, .isize⟩ 2),
          (.rangeTo (.int .isize false), .rangeTo 1)]
        (.ref .shared (.slice (.int .i8 false))) with
     | .error .undefined => True
     | _ => False) :=
  trivial

/-- Guard `step_v2_get_unchecked_range_from_in_mut`: `get_unchecked(1..)` on a
`&mut [u8]` input over a `.shared` allocation faults with `.undefined` even
though the result is `&[u8]`. -/
theorem refute_step_v2_get_unchecked_range_from_in_mut :
    (match execCoreCallOp sharedInit2Mem .sliceGetUncheckedRangeFrom
        [(.ref .mut (.slice (.int .i8 false)), .slicePtr ⟨some 1, 0, .isize⟩ 2),
          (.rangeFrom (.int .isize false), .rangeFrom 1)]
        (.ref .shared (.slice (.int .i8 false))) with
     | .error .undefined => True
     | _ => False) :=
  trivial

/-- Body with locals `_0 : ()` and `_1 : *mut ()`, whose only statement
`*_1 = PtrMetadata(move _1)` moves out of the pointer it stores through. -/
noncomputable def bodyStoreThroughMovedPtr : Body := {
  argumentCount := 1
  locals := [.unit, .rawPtr .mut .unit]
  basicBlocks := [{
    statements := [.assign ⟨1, [.deref]⟩
      (.unaryOp .ptrMetadata (.move ⟨1, []⟩))]
    terminator := .return_
  }]
}

/-- Guard `step_v2_assign_resolves_destination_first`: an assignment resolves
its destination before its rvalue runs, so `*_1 = PtrMetadata(move _1)` stores
through the pointer `_1` held before the move instead of faulting on the
moved-out slot. -/
theorem refute_step_v2_assign_resolves_destination_first :
    (match evalStatementV2 bodyStoreThroughMovedPtr
        { defId := 0, blockIdx := 0, stmtIdx := 0,
          locals := [.immediate (some .unit),
            .immediate (some (.ptr ⟨some 1, 0, .isize⟩))] }
        { allocations := [{
            allocId := 1
            alignLog2 := 0
            mutability := .mut
            bytes := []
            live := true
          }], nextAllocId := 2 }
        {}
        (.assign ⟨1, [.deref]⟩ (.unaryOp .ptrMetadata (.move ⟨1, []⟩))) with
     | .step _ => True
     | _ => False) :=
  trivial

/-- Guard `step_v2_raw_borrow_mut_through_const`: `&raw mut *p` through a
`*const u8` faults with `.undefined` instead of yielding a `*mut u8`. -/
theorem refute_step_v2_raw_borrow_mut_through_const :
    (match evalAddressOfRvalueV2
        [.unit, .rawPtr .shared (.int .i8 false), .rawPtr .mut (.int .i8 false)]
        [.immediate (some .unit), .immediate (some (.ptr ⟨some 1, 0, .isize⟩)),
          .immediate none]
        { allocations := [{
            allocId := 1
            alignLog2 := 0
            mutability := .mut
            bytes := [.init 0 none]
            live := true
          }], nextAllocId := 2 }
        (.rawPtr .mut (.int .i8 false)) .mut
        { localId := 1, projection := [.deref] } with
     | .error .undefined => True
     | _ => False) :=
  trivial

/-! ## Partially moved overflow pairs (`LocalSlot.partialTuple`)

Under `-Coverflow-checks=yes`, rustc lowers `x + 1` to
`_t = AddWithOverflow(x, 1)`, `assert(!move (_t.1))`, and
`_r = move (_t.0)`. Moving one field leaves the other readable; the
moved field, and the tuple as a whole, must not be read again. The
`overflowPairU8` and `partialPairLocals` helpers, shared with the positive
canary, live in `PositiveSanity.lean`. -/

/-- Guard `step_v2_partial_tuple_move_moved_field`: moving an already moved
tuple field faults with `.undefined`. -/
theorem refute_step_v2_partial_tuple_move_moved_field :
    (match readPlaceV2 [.unit, overflowPairU8] partialPairLocals
        MemoryState.empty true
        { localId := 1, projection := [.field 1 .bool] } with
     | .error .undefined => True
     | _ => False) :=
  trivial

/-- Guard `step_v2_partial_tuple_copy_moved_field`: copying an already moved
tuple field faults with `.undefined`. -/
theorem refute_step_v2_partial_tuple_copy_moved_field :
    (match readPlaceV2 [.unit, overflowPairU8] partialPairLocals
        MemoryState.empty false
        { localId := 1, projection := [.field 1 .bool] } with
     | .error .undefined => True
     | _ => False) :=
  trivial

/-- Guard `step_v2_partial_tuple_whole_read`: reading a partially moved tuple
as a whole faults with `.undefined`, for both copies and moves. -/
theorem refute_step_v2_partial_tuple_whole_read :
    (match readPlaceV2 [.unit, overflowPairU8] partialPairLocals
        MemoryState.empty false { localId := 1, projection := [] } with
     | .error .undefined => True
     | _ => False) ∧
    (match readPlaceV2 [.unit, overflowPairU8] partialPairLocals
        MemoryState.empty true { localId := 1, projection := [] } with
     | .error .undefined => True
     | _ => False) :=
  ⟨trivial, trivial⟩

/-- `progOverflowAddV2` called with `x = 255`. -/
noncomputable def queryOverflowAdd255 : Query :=
  { args := [.scalar ⟨.i8, false, BitVec.ofNat 128 255⟩] }

/-- Guard `step_v2_assert_failure_faults`: the failed overflow assert of
`255 + 1` faults instead of continuing with the wrapped sum, so
`WellFormedV2` (and hence any Profile v2 verification theorem) is refuted. -/
theorem refute_step_v2_assert_failure_faults :
    ReachesResultV2 progOverflowAddV2 queryOverflowAdd255
      (.fault .unsupported) ∧
    ¬ WellFormedV2 progOverflowAddV2 queryOverflowAdd255 := by
  have hReach : ReachesResultV2 progOverflowAddV2 queryOverflowAdd255
      (.fault .unsupported) := by
    unfold ReachesResultV2
    change ∃ s : State, ReachesV2 progOverflowAddV2 _ s ∧
      StepV2 progOverflowAddV2 s (.fault .unsupported)
    exact ⟨_,
      ReachesV2.tail (ReachesV2.tail (ReachesV2.tail (ReachesV2.refl _)
        ⟨0, rfl, rfl⟩) ⟨0, rfl, rfl⟩) ⟨0, rfl, rfl⟩,
      ⟨0, rfl, rfl⟩⟩
  exact ⟨hReach, fun hWf => hWf.2 .unsupported hReach⟩

/-- Two-frame program calling a `u32`-returning helper whose `_0` remains
uninitialized on `.return_`. -/
noncomputable def progNonRootRetUninit : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [
    {
      identity := "entry"
      argumentCount := 0
      locals := [u32Ty]
      basicBlocks := [
        {
          statements := []
          terminator := .call 1 [] ⟨0, []⟩ (some 1) .continue_
        },
        {
          statements := []
          terminator := .return_
        }
      ]
    },
    {
      identity := "callee"
      argumentCount := 0
      locals := [u32Ty]
      basicBlocks := [{ statements := [], terminator := .return_ }]
    }
  ]

/-- Guard `step_nonroot_return_uninit_or_dead`: `evalNonRootReturn` faults
with `.undefined` when a callee executes `.return_` with an uninitialized or
dead `_0`. -/
theorem refute_step_nonroot_return_uninit_or_dead :
    ReachesResult progNonRootRetUninit queryEmpty (.fault .undefined) ∧
    ¬ WellFormed progNonRootRetUninit queryEmpty :=
  refutes_wf_of_execFault (fuel := 3) rfl

/-- Two-frame program executing a diverging `.call` (`target := none`) whose
callee returns normally. -/
noncomputable def progNonRootRetNoneTarget : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [
    {
      identity := "entry"
      argumentCount := 0
      locals := [u32Ty]
      basicBlocks := [
        {
          statements := []
          terminator := .call 1 [] ⟨0, []⟩ none .continue_
        }
      ]
    },
    {
      identity := "callee"
      argumentCount := 0
      locals := [u32Ty]
      basicBlocks := [
        {
          statements := [
            .assign ⟨0, []⟩
              (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 42)⟩))
          ]
          terminator := .return_
        }
      ]
    }
  ]

/-- Guard `step_nonroot_return_none_target`: `evalNonRootReturn` faults with
`.undefined` when a callee returns from a call whose caller supplied
`target := none`. -/
theorem refute_step_nonroot_return_none_target :
    ReachesResult progNonRootRetNoneTarget queryEmpty (.fault .undefined) ∧
    ¬ WellFormed progNonRootRetNoneTarget queryEmpty :=
  refutes_wf_of_execFault (fuel := 3) rfl

/-- Single-frame program invoking `u16::unchecked_add(65535, 1)` via
`TerminatorKind.sysrootCall`. -/
noncomputable def progSysrootAddUbRefute : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [
    {
      identity := "entry"
      argumentCount := 0
      locals := [.int .i16 false]
      basicBlocks := [
        {
          statements := []
          terminator := .sysrootCall
            { kind := .uncheckedAdd, width := .i16, signed := false }
            [.constant ⟨.int .i16 false, .scalar (BitVec.ofNat 128 65535)⟩,
             .constant ⟨.int .i16 false, .scalar (BitVec.ofNat 128 1)⟩]
            ⟨0, []⟩ (some 1) .continue_
        },
        {
          statements := []
          terminator := .return_
        }
      ]
    }
  ]

/-- Guard `state_sysroot_unchecked_add_ub`: `sysrootNumBinOp .uncheckedAdd` maps
to `.addUnchecked`, so overflowing `u16::unchecked_add` faults `.undefined`. -/
theorem refute_state_sysroot_unchecked_add_ub :
    ReachesResult progSysrootAddUbRefute queryEmpty (.fault .undefined) ∧
    ¬ WellFormed progSysrootAddUbRefute queryEmpty :=
  refutes_wf_of_execFault (fuel := 4) rfl

/-- Single-frame program invoking `u16::unchecked_sub(0, 1)` via
`TerminatorKind.sysrootCall`. -/
noncomputable def progSysrootSubUbRefute : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [
    {
      identity := "entry"
      argumentCount := 0
      locals := [.int .i16 false]
      basicBlocks := [
        {
          statements := []
          terminator := .sysrootCall
            { kind := .uncheckedSub, width := .i16, signed := false }
            [.constant ⟨.int .i16 false, .scalar (BitVec.ofNat 128 0)⟩,
             .constant ⟨.int .i16 false, .scalar (BitVec.ofNat 128 1)⟩]
            ⟨0, []⟩ (some 1) .continue_
        },
        {
          statements := []
          terminator := .return_
        }
      ]
    }
  ]

/-- Guard `state_sysroot_unchecked_sub_ub`: `sysrootNumBinOp .uncheckedSub` maps
to `.subUnchecked`, so underflowing `u16::unchecked_sub` faults `.undefined`. -/
theorem refute_state_sysroot_unchecked_sub_ub :
    ReachesResult progSysrootSubUbRefute queryEmpty (.fault .undefined) ∧
    ¬ WellFormed progSysrootSubUbRefute queryEmpty :=
  refutes_wf_of_execFault (fuel := 4) rfl

/-- Single-frame program invoking `u16::unchecked_mul(256, 256)` via
`TerminatorKind.sysrootCall`. -/
noncomputable def progSysrootMulUbRefute : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [
    {
      identity := "entry"
      argumentCount := 0
      locals := [.int .i16 false]
      basicBlocks := [
        {
          statements := []
          terminator := .sysrootCall
            { kind := .uncheckedMul, width := .i16, signed := false }
            [.constant ⟨.int .i16 false, .scalar (BitVec.ofNat 128 256)⟩,
             .constant ⟨.int .i16 false, .scalar (BitVec.ofNat 128 256)⟩]
            ⟨0, []⟩ (some 1) .continue_
        },
        {
          statements := []
          terminator := .return_
        }
      ]
    }
  ]

/-- Guard `state_sysroot_unchecked_mul_ub`: `sysrootNumBinOp .uncheckedMul` maps
to `.mulUnchecked`, so overflowing `u16::unchecked_mul` faults `.undefined`. -/
theorem refute_state_sysroot_unchecked_mul_ub :
    ReachesResult progSysrootMulUbRefute queryEmpty (.fault .undefined) ∧
    ¬ WellFormed progSysrootMulUbRefute queryEmpty :=
  refutes_wf_of_execFault (fuel := 4) rfl

/-- Two-frame program in which a safe entry body calls an intra-crate
`unsafe fn` that returns normally. -/
noncomputable def progUnsafeCalleeRefute : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [
    {
      identity := "entry"
      argumentCount := 0
      locals := [u32Ty]
      basicBlocks := [
        {
          statements := []
          terminator := .call 1 [] ⟨0, []⟩ (some 1) .continue_
        },
        {
          statements := []
          terminator := .return_
        }
      ]
    },
    {
      identity := "callee"
      isUnsafe := true
      argumentCount := 0
      locals := [u32Ty]
      basicBlocks := [
        {
          statements := [
            .assign ⟨0, []⟩
              (.use (.constant ⟨u32Ty, .scalar (BitVec.ofNat 128 7)⟩))]
          terminator := .return_
        }
      ]
    }
  ]

/-- Guard `state_calls_admitted_unsafe_callee`: `callsAdmitted` rejects an
intra-crate `.call` to an `unsafe fn`, so `initState` fails closed with
`.unsupported` instead of running the callee without its safety contract. -/
theorem refute_state_calls_admitted_unsafe_callee :
    ReachesResult progUnsafeCalleeRefute queryEmpty (.fault .unsupported) ∧
    ¬ WellFormed progUnsafeCalleeRefute queryEmpty :=
  refutes_wf_of_execFault (fuel := 4) rfl

/-- Guard `step_nonroot_return_indirect_local`: `evalNonRootReturn` fails
closed with `.unsupported` when the popped callee frame still holds an
`.indirect` stack allocation, rather than leaking it. -/
theorem refute_step_nonroot_return_indirect_local :
    evalNonRootReturn progNonRootRetUninit
      { identity := "callee", argumentCount := 0, locals := [u32Ty],
        basicBlocks := [{ statements := [], terminator := .return_ }] }
      { statements := [], terminator := .return_ }
      { defId := 1, blockIdx := 0, stmtIdx := 0,
        locals := [.immediate (some (.scalar ⟨.i32, false, BitVec.ofNat 128 7⟩)),
          .indirect ⟨1, 0⟩],
        retDst? := some ⟨0, []⟩, retTarget? := some 1 }
      { defId := 0, blockIdx := 0, stmtIdx := 0, locals := [.immediate none] }
      [] entryMemory ⟨[]⟩ = .fault .unsupported :=
  rfl

/-- Guard `step_v2_constant_index_min_len`: `ConstantIndex` rejects arrays
shorter than `minLength` as `.undefined`. -/
theorem refute_step_v2_constant_index_min_len :
    constantIndexOffset 2 0 4 false = .error .undefined :=
  rfl

/-- Guard `step_v2_constant_index_oob`: `ConstantIndex` rejects out-of-bounds
indices `off ≥ len` as `.undefined`. -/
theorem refute_step_v2_constant_index_oob :
    constantIndexOffset 2 3 2 false = .error .undefined :=
  rfl

/-- Guard `step_v2_read_deref_proj_raw_misaligned`: reading a sub-field
`(*p).1` (`bool`) through a misaligned `*const (u32, bool)` faults with
`.undefined` even though the `bool` leaf itself has alignment 1. -/
theorem refute_step_v2_read_deref_proj_raw_misaligned :
    (match readPlaceV2
        [.bool, .rawPtr .shared (.tuple [.int .i32 false, .bool])]
        [.immediate none, .immediate (some (.ptr ⟨some 1, 1, .isize⟩))]
        { allocations := [{
            allocId := 1
            alignLog2 := 2
            mutability := .shared
            bytes := [
              .init 0 none, .init 0 none, .init 0 none, .init 0 none,
              .init 0 none, .init 1 none, .init 0 none, .init 0 none
            ]
            live := true
          }], nextAllocId := 2 }
        false
        { localId := 1, projection := [.deref, .field 1 .bool] } with
     | .error .undefined => True
     | _ => False) :=
  trivial

/-- Guard `step_v2_read_deref_proj_no_prov_misaligned`: reading a zero-sized
element `(*p)[0]` (`[u32; 0]`, align 4) through a provenance-free misaligned
`*const [[u32; 0]; 2]` at address `2` faults with `.undefined`. -/
theorem refute_step_v2_read_deref_proj_no_prov_misaligned :
    (match readPlaceV2
        [.array (.int .i32 false) 0,
         .rawPtr .shared (.array (.array (.int .i32 false) 0) 2)]
        [.immediate none, .immediate (some (.ptr ⟨none, 2, .isize⟩))]
        MemoryState.empty
        false
        { localId := 1, projection := [.deref, .constantIndex 0 1 false] } with
     | .error .undefined => True
     | _ => False) :=
  trivial

/-- Guard `step_v2_unsize_shared_to_mut`: `CastKind.unsize` rejects widening a
shared `&[T; N]` into `&mut [T]` as `.undefined` even on a `.mut`
allocation. -/
theorem refute_step_v2_unsize_shared_to_mut :
    (match evalRvalueV2
        [.ref .mut (.slice (.int .i8 false)),
         .ref .shared (.array (.int .i8 false) 2)]
        [.immediate none, .immediate (some (.ptr ⟨some 1, 0, .isize⟩))]
        { allocations := [{
            allocId := 1
            alignLog2 := 0
            mutability := .mut
            bytes := [.init 1 none, .init 2 none]
            live := true
          }], nextAllocId := 2 }
        (.ref .mut (.slice (.int .i8 false)))
        (.cast .unsize (.copy ⟨1, []⟩) (.ref .mut (.slice (.int .i8 false)))) with
     | .error .undefined => True
     | _ => False) :=
  trivial

/-- Guard `step_v2_unsize_raw_shared_to_mut`: `CastKind.unsize` rejects
widening `*const [T; N]` into `*mut [T]` as `.undefined`. -/
theorem refute_step_v2_unsize_raw_shared_to_mut :
    (match evalRvalueV2
        [.rawPtr .mut (.slice (.int .i8 false)),
         .rawPtr .shared (.array (.int .i8 false) 2)]
        [.immediate none, .immediate (some (.ptr ⟨some 1, 0, .isize⟩))]
        { allocations := [{
            allocId := 1
            alignLog2 := 0
            mutability := .mut
            bytes := [.init 1 none, .init 2 none]
            live := true
          }], nextAllocId := 2 }
        (.rawPtr .mut (.slice (.int .i8 false)))
        (.cast .unsize (.copy ⟨1, []⟩) (.rawPtr .mut (.slice (.int .i8 false)))) with
     | .error .undefined => True
     | _ => False) :=
  trivial

/-- Guard `step_v2_unsize_src_mut_valid`: `CastKind.unsize` validates the
source `&mut [T; N]` at `srcMut` (`.mut`), faulting `.undefined` over a
`.shared` allocation even when the destination slice is `&[T]` (`.shared`). -/
theorem refute_step_v2_unsize_src_mut_valid :
    (match evalRvalueV2
        [.ref .shared (.slice (.int .i8 false)),
         .ref .mut (.array (.int .i8 false) 2)]
        [.immediate none, .immediate (some (.ptr ⟨some 1, 0, .isize⟩))]
        { allocations := [{
            allocId := 1
            alignLog2 := 0
            mutability := .shared
            bytes := [.init 1 none, .init 2 none]
            live := true
          }], nextAllocId := 2 }
        (.ref .shared (.slice (.int .i8 false)))
        (.cast .unsize (.copy ⟨1, []⟩)
          (.ref .shared (.slice (.int .i8 false)))) with
     | .error .undefined => True
     | _ => False) :=
  trivial

/-- Guard `step_v2_resolve_deref_proj_propagates_ub`: resolving an out-of-bounds
`ConstantIndex` through `&mut [u8; 4]` propagates `.error .undefined` rather
than collapsing it to `.error .unsupported`. -/
theorem refute_step_v2_resolve_deref_proj_propagates_ub :
    (match resolvePlaceDestV2
        [.unit, .ref .mut (.array (.int .i8 false) 4)]
        [.immediate none, .immediate (some (.ptr ⟨some 1, 0, .isize⟩))]
        { allocations := [{
            allocId := 1
            alignLog2 := 0
            mutability := .mut
            bytes := [.init 0 none, .init 0 none, .init 0 none, .init 0 none]
            live := true
          }], nextAllocId := 2 }
        { localId := 1, projection := [.deref, .constantIndex 5 4 false] }
        (.int .i8 false) with
     | .error .undefined => True
     | _ => False) :=
  trivial

/-- Guard `step_v2_rodata_bytes_data_ty_only`: evaluating `ConstLit.rodataBytes`
at a reference type fails closed with `.error .unsupported` instead of decoding
a null or dangling reference. -/
theorem refute_step_v2_rodata_bytes_data_ty_only :
    (match evalOperandToSlotV2
        [.unit]
        [.immediate none]
        emptyMemory
        (.constant ⟨.ref .mut (.int .i8 false),
          .rodataBytes (List.replicate 8 (.init 0))⟩) with
     | .error .unsupported => True
     | _ => False) :=
  trivial

/-- Guard `step_v2_rodata_ref_mut`: evaluating `.rodataRef` at a mutable
`&mut T` reference type fails closed with `.unsupported`. -/
theorem refute_step_v2_rodata_ref_mut :
    (match evalRodataRefConstV2
        (.ref .mut (.int .i8 false)) [.init 5] 0 0 none
        [.immediate none] emptyMemory with
     | .error .unsupported => True
     | _ => False) :=
  trivial

/-- Guard `step_v2_rodata_slice_ref_mut`: evaluating `.rodataRef` at a mutable
`&mut [T]` slice reference type fails closed with `.unsupported`. -/
theorem refute_step_v2_rodata_slice_ref_mut :
    (match evalRodataRefConstV2
        (.ref .mut (.slice (.int .i8 false))) [.init 5] 0 0 (some 1)
        [.immediate none] emptyMemory with
     | .error .unsupported => True
     | _ => False) :=
  trivial

/-- Guard `step_v2_rodata_raw_ptr_mut`: evaluating `.rodataRef` at a mutable
`*mut T` raw-pointer type fails closed with `.unsupported`. -/
theorem refute_step_v2_rodata_raw_ptr_mut :
    (match evalRodataRefConstV2
        (.rawPtr .mut (.int .i8 false)) [.init 5] 0 0 none
        [.immediate none] emptyMemory with
     | .error .unsupported => True
     | _ => False) :=
  trivial

/-- Guard `step_v2_rodata_raw_slice_mut`: evaluating `.rodataRef` at a mutable
`*mut [T]` raw-slice type fails closed with `.unsupported`. -/
theorem refute_step_v2_rodata_raw_slice_mut :
    (match evalRodataRefConstV2
        (.rawPtr .mut (.slice (.int .i8 false))) [.init 5] 0 0 (some 1)
        [.immediate none] emptyMemory with
     | .error .unsupported => True
     | _ => False) :=
  trivial

/-- Guard `step_v2_array_eq_dangling_ref`: `CoreCallOp.arrayEq` validates
reference operands via `refValidInMem`, faulting `.undefined` on `&mut [u8; 2]`
over a `.shared` allocation (so skipping validation flips to `.ok true`). -/
theorem refute_step_v2_array_eq_dangling_ref :
    (match execCoreCallOp
        { allocations := [{
            allocId := 1
            alignLog2 := 0
            mutability := .shared
            bytes := [.init 1 none, .init 2 none]
            live := true
          }], nextAllocId := 2 }
        (.arrayEq (.int .i8 false) 2)
        [(.ref .mut (.array (.int .i8 false) 2), .ptr ⟨some 1, 0, .isize⟩),
         (.ref .shared (.array (.int .i8 false) 2), .ptr ⟨some 1, 0, .isize⟩)]
        .bool with
     | .error .undefined => True
     | _ => False) :=
  trivial

/-- Guard `step_v2_return_rodata_unsupported`: returning either a `&'static`
reference or a `*const` raw pointer into a callee-allocated `.rodata`
allocation faults with `.fault .unsupported` (neither `.undefined` nor
returning a dangling allocation id). -/
theorem refute_step_v2_return_rodata_unsupported :
    let roMem : MemoryState := {
      allocations := [{
        allocId := 1
        alignLog2 := 0
        mutability := .shared
        bytes := [.init 1 none, .init 2 none]
        live := true
      }]
      nextAllocId := 2
    }
    let bb : BasicBlock :=
      { statements := [], terminator := .return_, cleanup := false }
    let refBody : Body := {
      argumentCount := 0
      locals := [.ref .shared (.slice (.int .i8 false))]
      basicBlocks := [bb]
    }
    let ptrBody : Body := {
      argumentCount := 0
      locals := [.rawPtr .shared (.array (.int .i8 false) 2)]
      basicBlocks := [bb]
    }
    let refFrame : FrameState := {
      defId := 0
      blockIdx := 0
      stmtIdx := 0
      locals := [.immediate (some (.slicePtr ⟨some 1, 0, .isize⟩ 2))]
    }
    let ptrFrame : FrameState := {
      defId := 0
      blockIdx := 0
      stmtIdx := 0
      locals := [.immediate (some (.ptr ⟨some 1, 0, .isize⟩))]
    }
    (match evalTerminatorV2 refBody bb refFrame roMem { allocations := [] } with
     | .fault .unsupported => True
     | _ => False) ∧
    (match evalTerminatorV2 ptrBody bb ptrFrame roMem { allocations := [] } with
     | .fault .unsupported => True
     | _ => False) :=
  ⟨trivial, trivial⟩

/-- Guard `bytes_v2_ptr_or_ref_alloc_ids_option`: returning `Some` of a
`*const u8` or a `&u8` into a callee-allocated `.rodata` allocation faults
with `.fault .unsupported`, because `ptrOrRefAllocIds` looks through the
`Option` payload. -/
theorem refute_step_v2_return_rodata_option_ptr :
    let roMem : MemoryState := {
      allocations := [{
        allocId := 1
        alignLog2 := 0
        mutability := .shared
        bytes := [.init 1 none]
        live := true
      }]
      nextAllocId := 2
    }
    let bb : BasicBlock :=
      { statements := [], terminator := .return_, cleanup := false }
    let ptrBody : Body := {
      argumentCount := 0
      locals := [.option (.rawPtr .shared (.int .i8 false))]
      basicBlocks := [bb]
    }
    let refBody : Body := {
      argumentCount := 0
      locals := [.option (.ref .shared (.int .i8 false))]
      basicBlocks := [bb]
    }
    let frame : FrameState := {
      defId := 0
      blockIdx := 0
      stmtIdx := 0
      locals :=
        [.immediate (some (.optionVal (some (.ptr ⟨some 1, 0, .isize⟩))))]
    }
    (match evalTerminatorV2 ptrBody bb frame roMem { allocations := [] } with
     | .fault .unsupported => True
     | _ => False) ∧
    (match evalTerminatorV2 refBody bb frame roMem { allocations := [] } with
     | .fault .unsupported => True
     | _ => False) :=
  ⟨trivial, trivial⟩

/-- Guard `step_v2_read_indirect_proj_propagates_error`: reading an unsupported
field projection from an uninitialized `.indirect` local propagates
`.error .unsupported` from `projectMemoryLayoutV2` rather than falling back to
a whole-local load and turning it into `.error .undefined`. -/
theorem refute_step_v2_read_indirect_proj_propagates_error :
    (match readPlaceV2
        [.unit, .tuple [.int .i8 false, .bool]]
        [.immediate none, .indirect ⟨1, 0⟩]
        { allocations := [{
            allocId := 1
            alignLog2 := 0
            mutability := .mut
            bytes := [.uninit, .uninit]
            live := true
          }], nextAllocId := 2 }
        false
        { localId := 1, projection := [.field 5 .bool] } with
     | .error .unsupported => True
     | _ => False) :=
  trivial

/-- Guard `step_v2_resolve_local_proj_validates_first`: assigning to an
out-of-bounds projected immediate local faults `.fault .undefined` during
destination resolution before evaluating an `.unsupported` rvalue. The positive
`updateValAtProjV2` `RangeTo`/`RangeFrom` canaries live in
`PositiveSanity.lean`. -/
theorem refute_step_v2_resolve_local_proj_validates_first :
    let body : Body := {
      argumentCount := 0
      locals := [.unit, .array (.int .i8 false) 4]
      basicBlocks := []
    }
    let frame : FrameState := {
      defId := 0
      blockIdx := 0
      stmtIdx := 0
      locals := [.immediate none,
        .immediate (some (.array [
          .scalar ⟨.i8, false, 0⟩, .scalar ⟨.i8, false, 0⟩,
          .scalar ⟨.i8, false, 0⟩, .scalar ⟨.i8, false, 0⟩
        ]))]
    }
    let stmt : StatementKind :=
      .assign
        { localId := 1, projection := [.constantIndex 5 4 false] }
        .unsupported
    (match evalStatementV2 body frame emptyMemory
        { allocations := [] } stmt with
     | .fault .undefined => True
     | _ => False) :=
  trivial

/-- Guard `step_v2_assert_abort_extract_caller_mem`: pre-abort `&mut` mutations
must survive in `.aborted (extractCallerMemory callerMem mem1)`. -/
theorem refute_step_v2_assert_abort_extract_caller_mem :
    (match initStateV2 progMutBeforeAbortV2
        { args := [.ptr ⟨some 2, 0, .isize⟩], callerMem := cmBeforeAbort } with
     | .ok s₀ =>
       match evalStepV2 progMutBeforeAbortV2 s₀ with
       | .step s₁ =>
         match evalStepV2 progMutBeforeAbortV2 s₁ with
         | .done (.aborted cm') => cm' = cmAfterAbort
         | _ => False
       | _ => False
     | .error _ => False) :=
  rfl

/-- Guard `step_assert_optional_overflow_unsupported`: under `--panic abort`
and without `overflowChecks`, optional overflow checks (`.overflow .add` and
`.overflowNeg`) stay `.fault .unsupported` rather than aborting cleanly,
because codegen elides them when overflow checks are off. -/
theorem refute_step_assert_optional_overflow_unsupported :
    evalAssertFailure (.overflow .add) .abort .unreachable
        queryEmpty.callerMem false = .fault .unsupported ∧
      evalAssertFailure .overflowNeg .abort .unreachable
        queryEmpty.callerMem false = .fault .unsupported :=
  ⟨rfl, rfl⟩

/-- Guard `step_assert_checked_overflow_local_handler_unsupported`: with
`overflowChecks` but a crate-local `#[panic_handler]`, a failed checked overflow
assertion stays `.fault .unsupported` even under `--panic abort`. -/
theorem refute_step_assert_checked_overflow_local_handler_unsupported :
    evalAssertFailure (.overflow .add) .abort .unreachable
        queryEmpty.callerMem true true = .fault .unsupported ∧
      evalAssertFailure .overflowNeg .abort .unreachable
        queryEmpty.callerMem true true = .fault .unsupported :=
  ⟨rfl, rfl⟩

/-- Guard `step_assert_local_panic_handler_unsupported`: when a crate defines a
crate-local `#[panic_handler]` (`hasLocalPanicHandler = true`), failing safe
assertions stay `.fault .unsupported` even under `--panic abort`. -/
theorem refute_step_assert_local_panic_handler_unsupported :
    evalAssertFailure .divByZero .abort .unreachable
        queryEmpty.callerMem true = .fault .unsupported ∧
      evalAssertFailure .boundsCheck .abort .continue_
        queryEmpty.callerMem true = .fault .unsupported :=
  ⟨rfl, rfl⟩

/-- Profile v2 program under `--panic abort` whose `.nullPtrDeref` assertion
fails despite no local panic handler. -/
noncomputable def progAssertNullDerefV2 : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 2
  panicStrategy := .abort
  hasLocalPanicHandler := false
  bodies := [{
    argumentCount := 0
    locals := [.unit]
    basicBlocks := [{
      statements := []
      terminator :=
        .assert (.constant ⟨.bool, .scalar (BitVec.ofNat 128 0)⟩) true
          .nullPtrDeref 0 .unreachable
    }]
    isUnsafe := false
    identity := "guard_mutation::assert_null_deref_v2"
  }]
}

/-- Guard `step_assert_ptr_deref_undefined`: `.nullPtrDeref` and
`.misalignedPtrDeref` assertions always fault with `.undefined`, even under
`--panic abort` with no crate-local panic handler. -/
theorem refute_step_assert_ptr_deref_undefined :
    evalAssertFailure .nullPtrDeref .abort .unreachable
        queryEmpty.callerMem false = .fault .undefined ∧
      evalAssertFailure .misalignedPtrDeref .abort .unreachable
          queryEmpty.callerMem false = .fault .undefined ∧
      ReachesResultV2 progAssertNullDerefV2 queryEmpty (.fault .undefined) ∧
      ¬ WellFormedV2 progAssertNullDerefV2 queryEmpty := by
  have hReach :
      ReachesResultV2 progAssertNullDerefV2 queryEmpty (.fault .undefined) :=
    ⟨_, ReachesV2.refl _, ⟨0, rfl, rfl⟩⟩
  exact ⟨rfl, rfl, hReach, fun hWf => hWf.2 .undefined hReach⟩

/-- Two-block Profile v1 program executing `TerminatorKind.assert`
on `_1 : bool` with `expected = true`, `msg = .divByZero`, and target
block `1` (which returns `_0 : ()`). -/
noncomputable def progAssertFailedV1 : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [.unit, .bool]
    basicBlocks := [
      { statements := []
        terminator :=
          .assert (.copy ⟨1, []⟩) true .divByZero 1 .continue_ },
      { statements := []
        terminator := .return_ }
    ]
  }]
}

/-- Guard `step_assert_v1_failure_faults`: a failing Profile v1
`TerminatorKind.assert` (`b != expected`) faults rather than jumping to
`target`. -/
theorem refute_step_assert_v1_failure_faults :
    ReachesResult progAssertFailedV1 { args := [.bool false] }
        (.fault .unsupported) ∧
    ¬ WellFormed progAssertFailedV1 { args := [.bool false] } :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `step_assert_v1_non_bool_unsupported`: Profile v1 `evalTerminator`
refuses non-`.bool` `.assert` condition operands as `.fault .unsupported`. -/
theorem refute_step_assert_v1_non_bool_unsupported :
    let body : Body := {
      argumentCount := 1
      locals := [.unit, u8Ty]
      basicBlocks := []
    }
    let bb : BasicBlock := {
      statements := []
      terminator := .assert (.copy ⟨1, []⟩) true .divByZero 1 .continue_
    }
    let frame : FrameState := {
      defId := 0
      blockIdx := 0
      stmtIdx := 0
      locals := [.immediate (some .unit),
        .immediate (some (scalarNatVal .i8 false 2))]
    }
    (match evalTerminator body bb frame emptyMemory { allocations := [] } with
     | .fault .unsupported => True
     | _ => False) :=
  trivial

/-- Guard `step_v2_assert_non_bool_unsupported`: Profile v2 `evalTerminatorV2`
refuses non-`.bool` `.assert` condition operands as `.fault .unsupported`. -/
theorem refute_step_v2_assert_non_bool_unsupported :
    let body : Body := {
      argumentCount := 1
      locals := [.unit, u8Ty]
      basicBlocks := []
    }
    let bb : BasicBlock := {
      statements := []
      terminator := .assert (.copy ⟨1, []⟩) true .divByZero 1 .continue_
    }
    let frame : FrameState := {
      defId := 0
      blockIdx := 0
      stmtIdx := 0
      locals := [.immediate (some .unit),
        .immediate (some (scalarNatVal .i8 false 2))]
    }
    (match evalTerminatorV2 body bb frame emptyMemory { allocations := [] } with
     | .fault .unsupported => True
     | _ => False) :=
  trivial

/-- Guard `step_v2_assign_use_overlap_ub`: `StatementKind.assign` with
`Rvalue.use` / `Rvalue.useRetag` faults `.fault .undefined` on overlapping
non-zero-sized `BackendRepr::Memory` or padded places (`*p = *p` on `[u8; 4]`,
local `a = a` on `[u8; 4]`, `*p = *p` on padded `(u32, bool)`, and `a[0] = a[0]`
on `[[u8; 4]; 2]`). The positive anti-overreach canaries for ZST, unpadded
`ScalarPair`, and disjoint element copies live in `PositiveSanity.lean`. -/
theorem refute_step_v2_assign_use_overlap_ub :
    let arr4Ty : MirTy := .array u8Ty 4
    let mem4 : MemoryState := {
      allocations := [{
        allocId := 2
        alignLog2 := 2
        mutability := .mut
        bytes := [.init 1 none, .init 2 none, .init 3 none, .init 4 none]
        live := true
      }]
      nextAllocId := 3
    }
    let bodyPtrArr : Body := {
      argumentCount := 0
      locals := [.unit, .rawPtr .mut arr4Ty]
      basicBlocks := []
    }
    let framePtrArr : FrameState := {
      defId := 0, blockIdx := 0, stmtIdx := 0
      locals := [.immediate none, .immediate (some (.ptr ⟨some 2, 0, .isize⟩))]
    }
    let bodyLocArr : Body := {
      argumentCount := 0
      locals := [.unit, arr4Ty]
      basicBlocks := []
    }
    let frameLocArr : FrameState := {
      defId := 0, blockIdx := 0, stmtIdx := 0
      locals := [.immediate none, .immediate (some (.array [
        .scalar ⟨.i8, false, 1⟩, .scalar ⟨.i8, false, 2⟩,
        .scalar ⟨.i8, false, 3⟩, .scalar ⟨.i8, false, 4⟩
      ]))]
    }
    let bodyPaddedPair : Body := {
      argumentCount := 0
      locals := [.unit, .tuple [.int .i32 false, .bool]]
      basicBlocks := []
    }
    let framePaddedPair : FrameState := {
      defId := 0, blockIdx := 0, stmtIdx := 0
      locals := [.immediate none,
        .immediate (some (.tuple [.scalar ⟨.i32, false, 9⟩, .bool true]))]
    }
    let bodyArrOfArr : Body := {
      argumentCount := 0
      locals := [.unit, .array arr4Ty 2]
      basicBlocks := []
    }
    let vArr4 : Val := .array [
      .scalar ⟨.i8, false, 1⟩, .scalar ⟨.i8, false, 2⟩,
      .scalar ⟨.i8, false, 3⟩, .scalar ⟨.i8, false, 4⟩
    ]
    let frameArrOfArr : FrameState := {
      defId := 0, blockIdx := 0, stmtIdx := 0
      locals := [.immediate none, .immediate (some (.array [vArr4, vArr4]))]
    }
    (match evalStatementV2 bodyPtrArr framePtrArr mem4 { allocations := [] }
        (.assign { localId := 1, projection := [.deref] }
          (.use (.copy { localId := 1, projection := [.deref] }))) with
     | .fault .undefined => True
     | _ => False) ∧
    (match evalStatementV2 bodyLocArr frameLocArr emptyMemory { allocations := [] }
        (.assign { localId := 1, projection := [] }
          (.use (.copy { localId := 1, projection := [] }))) with
     | .fault .undefined => True
     | _ => False) ∧
    (match evalStatementV2 bodyPaddedPair framePaddedPair emptyMemory { allocations := [] }
        (.assign { localId := 1, projection := [] }
          (.use (.copy { localId := 1, projection := [] }))) with
     | .fault .undefined => True
     | _ => False) ∧
    (match evalStatementV2 bodyArrOfArr frameArrOfArr emptyMemory { allocations := [] }
        (.assign { localId := 1, projection := [.constantIndex 0 2 false] }
          (.use (.copy { localId := 1, projection := [.constantIndex 0 2 false] }))) with
     | .fault .undefined => True
     | _ => False) :=
  ⟨trivial, trivial, trivial, trivial⟩

/-- Guard `step_v2_assign_aggregate_clobber_unsupported`: in-place `Aggregate`
where an earlier field write (`_1.0`) aliases a later operand (`_1.0` in
`_1 = (_1.1, _1.0)`) fails closed with `.fault .unsupported`. The non-clobbering
scalar aggregate canary lives in `PositiveSanity.lean`. -/
theorem refute_step_v2_assign_aggregate_clobber_unsupported :
    let u32Ty : MirTy := .int .i32 false
    let body : Body := {
      argumentCount := 0
      locals := [.unit, .tuple [u32Ty, u32Ty]]
      basicBlocks := []
    }
    let frame : FrameState := {
      defId := 0, blockIdx := 0, stmtIdx := 0
      locals := [.immediate none,
        .immediate (some (.tuple [.scalar ⟨.i32, false, 1⟩, .scalar ⟨.i32, false, 2⟩]))]
    }
    (match evalStatementV2 body frame emptyMemory { allocations := [] }
        (.assign { localId := 1, projection := [] }
          (.aggregateTuple [
            .copy { localId := 1, projection := [.field 1 u32Ty] },
            .copy { localId := 1, projection := [.field 0 u32Ty] }
          ])) with
     | .fault .unsupported => True
     | _ => False) :=
  trivial

/-- Shared locals for the `Range` aggregate hazard refutations: `_1` is the
immediate `Range<usize>` `10..20` and `_2` an immediate `usize`. -/
noncomputable def rangeHazLocals : List MirTy × List LocalSlot :=
  ([.unit, .range (.int .isize false), .int .isize false],
   [.immediate none, .immediate (some (.range 10 20)),
    .immediate (some (.scalar ⟨.isize, false, 5⟩))])

/-- Guard `step_v2_assign_aggregate_range_clobber_unsupported`: in-place
`_1 = Range { start: _1.1, end: _1.0 }` reads `_1.0` after the field-0 write
clobbered it (`write_aggregate` copies fields in order), so it fails closed
instead of evaluating both operands against the old `_1`. -/
theorem refute_step_v2_assign_aggregate_range_clobber_unsupported :
    checkAssignCopyHazardV2 rangeHazLocals.1 rangeHazLocals.2 emptyMemory
      (.local 1) (.range (.int .isize false))
      (.aggregateRange (.int .isize false)
        (.copy { localId := 1, projection :=
          [.field 1 (.int .isize false)] })
        (.copy { localId := 1, projection :=
          [.field 0 (.int .isize false)] })) =
      .error .unsupported :=
  rfl

/-- Guard `step_v2_assign_range_field_span`: `Range` field projections on an
immediate local resolve to precise spans, so
`_1 = Range { start: _2, end: _1.1 }` (which reads only the field not yet
written) passes the hazard check. -/
theorem refute_step_v2_assign_range_field_span :
    checkAssignCopyHazardV2 rangeHazLocals.1 rangeHazLocals.2 emptyMemory
      (.local 1) (.range (.int .isize false))
      (.aggregateRange (.int .isize false)
        (.copy { localId := 2, projection := [] })
        (.copy { localId := 1, projection :=
          [.field 1 (.int .isize false)] })) =
      .ok () :=
  rfl

/-- Shared locals for the `Option` payload hazard refutations:
`_1 : (Option<u32>, u32)`, `_2 : Option<u32>`, and
`_3 : (u32, u32, Option<u32>)`, all immediate. -/
noncomputable def optHazLocals : List MirTy × List LocalSlot :=
  let u32Ty : MirTy := .int .i32 false
  ([.unit, .tuple [.option u32Ty, u32Ty], .option u32Ty,
    .tuple [u32Ty, u32Ty, .option u32Ty]],
   [.immediate none,
    .immediate (some (.tuple [.optionVal (some (.scalar ⟨.i32, false, 7⟩)),
      .scalar ⟨.i32, false, 1⟩])),
    .immediate (some (.optionVal none)),
    .immediate (some (.tuple [.scalar ⟨.i32, false, 1⟩,
      .scalar ⟨.i32, false, 2⟩,
      .optionVal (some (.scalar ⟨.i32, false, 3⟩))]))])

/-- Guard `step_v2_assign_option_payload_span`: an `Option` payload read
`(_3.2 as Some).0` resolves to a sub-span of `_3.2`, so
`_3 = (_1.1, (_3.2 as Some).0, _2)` passes, while
`_1 = (_2, (_1.0 as Some).0)` reads the payload of the already-overwritten
`_1.0` and fails closed. -/
theorem refute_step_v2_assign_option_payload_span :
    let u32Ty : MirTy := .int .i32 false
    checkAssignCopyHazardV2 optHazLocals.1 optHazLocals.2 emptyMemory
      (.local 3) (.tuple [u32Ty, u32Ty, .option u32Ty])
      (.aggregateTuple [
        .copy { localId := 1, projection := [.field 1 u32Ty] },
        .copy { localId := 3, projection :=
          [.field 2 (.option u32Ty), .downcast 1,
            .field 0 u32Ty] },
        .copy { localId := 2, projection := [] }]) = .ok () ∧
    checkAssignCopyHazardV2 optHazLocals.1 optHazLocals.2 emptyMemory
      (.local 1) (.tuple [.option u32Ty, u32Ty])
      (.aggregateTuple [
        .copy { localId := 2, projection := [] },
        .copy { localId := 1, projection :=
          [.field 0 (.option u32Ty), .downcast 1,
            .field 0 u32Ty] }]) = .error .unsupported :=
  ⟨rfl, rfl⟩

/-- Guard `step_v2_assign_aggregate_unresolved_operand_unsupported`: a later
`Aggregate` operand whose source span cannot be resolved (here the bare
variant place `_1.0 as Some`) fails closed rather than being treated like a
constant. -/
theorem refute_step_v2_assign_aggregate_unresolved_operand_unsupported :
    let u32Ty : MirTy := .int .i32 false
    checkAssignCopyHazardV2 optHazLocals.1 optHazLocals.2 emptyMemory
      (.local 1) (.tuple [.option u32Ty, u32Ty])
      (.aggregateTuple [
        .copy { localId := 2, projection := [] },
        .copy { localId := 1, projection :=
          [.field 0 (.option u32Ty), .downcast 1] }]) =
      .error .unsupported :=
  rfl

/-- Guard `step_v2_assign_aggregate_deref_ptr_clobber_unsupported`: when an
earlier `Aggregate` field write overwrites the memory holding a pointer local
`_2 : *const u32`, a later `copy (*_2)` operand fails closed with
`.fault .unsupported` (for both array destinations and tuple destinations taking
the conservative `baseSpan` path). The positive read-before-overwrite canaries
live in `PositiveSanity.lean`. -/
theorem refute_step_v2_assign_aggregate_deref_ptr_clobber_unsupported :
    let u32Ty : MirTy := .int .i32 false
    let ptrU32Ty : MirTy := .rawPtr .shared u32Ty
    let arr2Ty : MirTy := .array u32Ty 2
    let tup3Ty : MirTy := .tuple [u32Ty, u32Ty, u32Ty]
    let mem : MemoryState := {
      allocations := [
        { allocId := 1, bytes := [
            .init 1 none, .init 0 none, .init 0 none, .init 0 none
          ], alignLog2 := 2, mutability := .mut, live := true },
        { allocId := 2, bytes := [
            .init 0 (some 1), .init 0 (some 1), .init 0 (some 1), .init 0 (some 1),
            .init 0 (some 1), .init 0 (some 1), .init 0 (some 1), .init 0 (some 1),
            .init 0 none, .init 0 none, .init 0 none, .init 0 none
          ], alignLog2 := 3, mutability := .mut, live := true }
      ]
      nextAllocId := 3
    }
    let body : Body := {
      argumentCount := 0
      locals := [
        .unit, u32Ty, ptrU32Ty, .rawPtr .mut arr2Ty, .rawPtr .mut tup3Ty
      ]
      basicBlocks := []
    }
    let frame : FrameState := {
      defId := 0, blockIdx := 0, stmtIdx := 0
      locals := [
        .immediate none,
        .immediate (some (.scalar ⟨.i32, false, 7⟩)),
        .indirect { allocId := 2, offset := 0 },
        .immediate (some (.ptr { allocId := some 2, offsetBytes := 0, width := .isize })),
        .immediate (some (.ptr { allocId := some 2, offsetBytes := 0, width := .isize }))
      ]
    }
    (match evalStatementV2 body frame mem { allocations := [] }
        (.assign { localId := 3, projection := [.deref] }
          (.aggregateArray u32Ty [
            .copy { localId := 1, projection := [] },
            .copy { localId := 2, projection := [.deref] }
          ])) with
     | .fault .unsupported => True
     | _ => False) ∧
    (match checkAggregateCopyHazardLoopV2 body.locals frame.locals mem
        (.memRange 2 0 12) tup3Ty false 0 [] [u32Ty, u32Ty, u32Ty] [
          .copy { localId := 1, projection := [] },
          .copy { localId := 2, projection := [.deref] },
          .copy { localId := 1, projection := [] }
        ] with
     | .error .unsupported => True
     | _ => False) :=
  ⟨trivial, trivial⟩

/-- Guard `step_v2_assign_aggregate_field_overlap_ub`: in-place `Aggregate`
copying a `BackendRepr::Memory` field onto itself (`_1 = (_1.0, _1.1)` on
`([u8; 4], [u8; 4])`) faults `.fault .undefined`. -/
theorem refute_step_v2_assign_aggregate_field_overlap_ub :
    let arr4Ty : MirTy := .array u8Ty 4
    let vArr4 : Val := .array [
      .scalar ⟨.i8, false, 1⟩, .scalar ⟨.i8, false, 2⟩,
      .scalar ⟨.i8, false, 3⟩, .scalar ⟨.i8, false, 4⟩
    ]
    let body : Body := {
      argumentCount := 0
      locals := [.unit, .tuple [arr4Ty, arr4Ty]]
      basicBlocks := []
    }
    let frame : FrameState := {
      defId := 0, blockIdx := 0, stmtIdx := 0
      locals := [.immediate none, .immediate (some (.tuple [vArr4, vArr4]))]
    }
    (match evalStatementV2 body frame emptyMemory { allocations := [] }
        (.assign { localId := 1, projection := [] }
          (.aggregateTuple [
            .copy { localId := 1, projection := [.field 0 arr4Ty] },
            .copy { localId := 1, projection := [.field 1 arr4Ty] }
          ])) with
     | .fault .undefined => True
     | _ => False) :=
  trivial

/-- Guard `step_v2_assign_repeat_overlap_ub`: in-place `Rvalue.repeat_`
copying a `BackendRepr::Memory` element `a[0]` into `a = [a[0]; 2]` faults
`.fault .undefined`. The disjoint `a = [a[1]; 2]` canary lives in
`PositiveSanity.lean`. -/
theorem refute_step_v2_assign_repeat_overlap_ub :
    let arr4Ty : MirTy := .array u8Ty 4
    let vArr4 : Val := .array [
      .scalar ⟨.i8, false, 1⟩, .scalar ⟨.i8, false, 2⟩,
      .scalar ⟨.i8, false, 3⟩, .scalar ⟨.i8, false, 4⟩
    ]
    let body : Body := {
      argumentCount := 0
      locals := [.unit, .array arr4Ty 2]
      basicBlocks := []
    }
    let frame : FrameState := {
      defId := 0, blockIdx := 0, stmtIdx := 0
      locals := [.immediate none, .immediate (some (.array [vArr4, vArr4]))]
    }
    (match evalStatementV2 body frame emptyMemory { allocations := [] }
        (.assign { localId := 1, projection := [] }
          (.repeat_ (.copy { localId := 1, projection := [.constantIndex 0 2 false] })
            arr4Ty 2)) with
     | .fault .undefined => True
     | _ => False) :=
  trivial

/-- Guard `state_v2_init_uses_entry_memory_for_args`: end-to-end Profile v2
`Program` execution where the caller passes a dangling raw pointer
`p : *const u8 = ⟨some 2, 0, .isize⟩` with empty `callerMem`, and the callee
promotes a stack local `_2 : u8 = 42` via `&raw const _2` before reading `*p`.
`initStateV2` must advance `nextAllocId` past `2` via `entryMemoryForArgsV2` so
`_2` receives `allocId = 3` and reading dangling `*p` faults `.fault .undefined`
(whereas falling back to `entryMemoryWithCaller` assigns `allocId = 2` to `_2`
and unsoundly returns `42`). -/
theorem refute_state_v2_init_uses_entry_memory_for_args :
    let rawU8Const : MirTy := .rawPtr .shared u8Ty
    let prog : Program := {
      scope := .unit
      pointerWidthBits := 64
      mirProfileVersion := 2
      bodies := [{
        argumentCount := 1
        locals := [u8Ty, rawU8Const, u8Ty, rawU8Const]
        basicBlocks := [{
          statements := [
            .storageLive 2,
            .assign { localId := 2, projection := [] }
              (.use (.constant ⟨u8Ty, .scalar (BitVec.ofNat 128 42)⟩)),
            .storageLive 3,
            .assign { localId := 3, projection := [] }
              (.addressOf .shared { localId := 2, projection := [] }),
            .assign { localId := 0, projection := [] }
              (.use (.copy { localId := 1, projection := [.deref] }))
          ]
          terminator := .return_
        }]
        isUnsafe := true
        identity := "guard_mutation::dangling_raw_ptr_vs_stack_alloc"
      }]
    }
    (match initStateV2 prog
        { args := [.ptr ⟨some 2, 0, .isize⟩], callerMem := { allocations := [] } } with
     | .ok s0 =>
       match evalStepV2 prog s0 with
       | .step s1 =>
         match evalStepV2 prog s1 with
         | .step s2 =>
           match evalStepV2 prog s2 with
           | .step s3 =>
             match evalStepV2 prog s3 with
             | .step s4 => evalStepV2 prog s4 = .fault .undefined
             | _ => False
           | _ => False
         | _ => False
       | _ => False
     | .error _ => False) :=
  rfl

/-- Guard `step_v2_fake_address_of_ref_validity`: `evalFakeAddressOfRvalueV2`
must validate `refValidInMem` when dereferencing a reference base local,
faulting `.undefined` on a null `&mut [u8]`. -/
theorem refute_step_v2_fake_address_of_ref_validity :
    (match evalFakeAddressOfRvalueV2
        [
          .unit,
          .ref .mut (.slice (.int .i8 false)),
          .rawPtr .shared (.slice (.int .i8 false))
        ]
        [
          .immediate (some .unit),
          .immediate (some (.slicePtr ⟨none, 0, .isize⟩ 0)),
          .immediate none
        ]
        { allocations := [], nextAllocId := 1 }
        (.rawPtr .shared (.slice (.int .i8 false)))
        { localId := 1, projection := [.deref] } with
     | .error .undefined => True
     | _ => False) :=
  trivial

/-- Guard `core_contracts_slice_subslice_in_mut`: `Index::index(0..1)` on a
`&mut [u8]` input over a `.shared` allocation faults with `.undefined` even
though `reqMut = .shared`, because `execSliceSubslice` validates the input at
`inMut`. -/
theorem refute_core_contracts_slice_subslice_in_mut :
    (match execCoreContractOp sharedInit2Mem
        (.sliceIndexRange .shared (.int .i8 false))
        [(.ref .mut (.slice (.int .i8 false)), .slicePtr ⟨some 1, 0, .isize⟩ 2),
          (.range (.int .isize false), .range 0 1)]
        (.ref .shared (.slice (.int .i8 false))) with
     | .error .undefined => True
     | _ => False) :=
  trivial

/-- Guard `core_contracts_slice_split_at_in_mut`: `slice::split_at(1)` on a
`&mut [u8]` input over a `.shared` allocation faults with `.undefined` even
though `reqMut = .shared`, because `execSliceSplitAt` validates the input at
`inMut`. The shared `&[u8]` canary lives in `PositiveSanity.lean`. -/
theorem refute_core_contracts_slice_split_at_in_mut :
    (match execCoreContractOp sharedInit2Mem
        (.sliceSplitAt .shared (.int .i8 false))
        [(.ref .mut (.slice (.int .i8 false)), .slicePtr ⟨some 1, 0, .isize⟩ 2),
          (.int .isize false, .scalar ⟨.isize, false, 1⟩)]
        (.tuple [.ref .shared (.slice (.int .i8 false)),
          .ref .shared (.slice (.int .i8 false))]) with
     | .error .undefined => True
     | _ => False) :=
  trivial

/-- Guard `core_contracts_i128_host_overflow`: 128-bit checked, saturating,
and overflowing arithmetic detect mathematical overflow (`intHostOverflow`)
before `BitVec 128` carrier truncation across unsigned and signed edges. The
in-bounds 128-bit canary lives in `PositiveSanity.lean`. -/
theorem refute_core_contracts_i128_host_overflow :
    let u128Ty : MirTy := .int .i128 false
    let i128Ty : MirTy := .int .i128 true
    let u128Max : ScalarVal :=
      ⟨.i128, false, BitVec.ofNat 128 340282366920938463463374607431768211455⟩
    let u128Zero : ScalarVal := ⟨.i128, false, 0⟩
    let u128One : ScalarVal := ⟨.i128, false, 1⟩
    let u128Two : ScalarVal := ⟨.i128, false, 2⟩
    let i128Max : ScalarVal :=
      ⟨.i128, true, BitVec.ofNat 128 170141183460469231731687303715884105727⟩
    let i128Min : ScalarVal :=
      ⟨.i128, true, BitVec.ofNat 128 170141183460469231731687303715884105728⟩
    let i128One : ScalarVal := ⟨.i128, true, 1⟩
    let i128NegOne : ScalarVal :=
      ⟨.i128, true, BitVec.ofNat 128 340282366920938463463374607431768211455⟩
    execCoreContractOp MemoryState.empty (.numCheckedAdd .i128 false)
      [(u128Ty, .scalar u128Max), (u128Ty, .scalar u128One)]
      (.option u128Ty) =
      .ok (.optionVal none, MemoryState.empty) ∧
    execCoreContractOp MemoryState.empty (.numCheckedSub .i128 false)
      [(u128Ty, .scalar u128Zero), (u128Ty, .scalar u128One)]
      (.option u128Ty) =
      .ok (.optionVal none, MemoryState.empty) ∧
    execCoreContractOp MemoryState.empty (.numCheckedAdd .i128 true)
      [(i128Ty, .scalar i128Max), (i128Ty, .scalar i128One)]
      (.option i128Ty) =
      .ok (.optionVal none, MemoryState.empty) ∧
    execCoreContractOp MemoryState.empty (.numCheckedMul .i128 false)
      [(u128Ty, .scalar u128Max), (u128Ty, .scalar u128Two)]
      (.option u128Ty) =
      .ok (.optionVal none, MemoryState.empty) ∧
    execCoreContractOp MemoryState.empty (.numSaturatingAdd .i128 false)
      [(u128Ty, .scalar u128Max), (u128Ty, .scalar u128One)] u128Ty =
      .ok (.scalar u128Max, MemoryState.empty) ∧
    execCoreContractOp MemoryState.empty (.numSaturatingAdd .i128 true)
      [(i128Ty, .scalar i128Max), (i128Ty, .scalar i128One)] i128Ty =
      .ok (.scalar i128Max, MemoryState.empty) ∧
    execCoreContractOp MemoryState.empty (.numSaturatingAdd .i128 true)
      [(i128Ty, .scalar i128Min), (i128Ty, .scalar i128NegOne)] i128Ty =
      .ok (.scalar i128Min, MemoryState.empty) ∧
    execCoreContractOp MemoryState.empty (.numOverflowingAdd .i128 false)
      [(u128Ty, .scalar u128Max), (u128Ty, .scalar u128One)]
      (.tuple [u128Ty, .bool]) =
      .ok (.tuple [.scalar u128Zero, .bool true], MemoryState.empty) ∧
    execCoreContractOp MemoryState.empty (.numOverflowingSub .i128 false)
      [(u128Ty, .scalar u128Zero), (u128Ty, .scalar u128One)]
      (.tuple [u128Ty, .bool]) =
      .ok (.tuple [.scalar u128Max, .bool true], MemoryState.empty) ∧
    execCoreContractOp MemoryState.empty (.numOverflowingAdd .i128 true)
      [(i128Ty, .scalar i128Max), (i128Ty, .scalar i128One)]
      (.tuple [i128Ty, .bool]) =
      .ok (.tuple [.scalar i128Min, .bool true], MemoryState.empty) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Guard `bytes_v2_slice_uninhabited_elem`: `refValidInMem` rejects
positive-length `&[!]` and `&mut [!]` slices (both provenance-free dangling
pointers and provenance-backed allocations) with `.error .undefined`.
The empty `&[!]` and inhabited ZST `&[()]` canaries live in
`PositiveSanity.lean`. -/
theorem refute_bytes_v2_slice_uninhabited_elem :
    let mutMem : MemoryState := {
      allocations := [{
        allocId := 2
        alignLog2 := 0
        mutability := .mut
        bytes := []
        live := true
      }]
      nextAllocId := 3
    }
    refValidInMem MemoryState.empty .shared (.slice .never)
      (.slicePtr ⟨none, 1, .isize⟩ 1) = .error .undefined ∧
    refValidInMem MemoryState.empty .mut (.slice .never)
      (.slicePtr ⟨none, 1, .isize⟩ 2) = .error .undefined ∧
    refValidInMem mutMem .shared (.slice .never)
      (.slicePtr ⟨some 2, 0, .isize⟩ 1) = .error .undefined ∧
    refValidInMem mutMem .mut (.slice .never)
      (.slicePtr ⟨some 2, 0, .isize⟩ 1) = .error .undefined :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Guard `core_contracts_option_unwrap_refs_valid`: `Option::unwrap` on
`Some(&u8)` pointing into a dead allocation faults `.undefined` via
`refsValidInMem`. The live `Some(&u8)` canary lives in `PositiveSanity.lean`. -/
theorem refute_core_contracts_option_unwrap_refs_valid :
    let refU8Ty : MirTy := .ref .shared (.int .i8 false)
    let deadMem : MemoryState := {
      allocations := [{
        allocId := 2
        alignLog2 := 0
        mutability := .shared
        bytes := [.init 7 none]
        live := false
      }]
      nextAllocId := 3
    }
    execCoreContractOp deadMem (.optionUnwrap refU8Ty)
      [(.option refU8Ty, .optionVal (some (.ptr ⟨some 2, 0, .isize⟩)))]
      refU8Ty = .error .undefined :=
  rfl

/-- Guard `step_v2_option_discriminant_dst_ty`: projected `Option` discriminant
rejects mismatched `dstTy` with `.unsupported`. The `isize` destination canary
lives in `PositiveSanity.lean`. -/
theorem refute_step_v2_option_discriminant_dst_ty :
    let optU8Ty : MirTy := .option (.int .i8 false)
    let tupTy : MirTy := .tuple [optU8Ty, .int .i8 false]
    let locals : List LocalSlot := [
      .immediate (some (.tuple [.optionVal (some (.scalar ⟨.i8, false, 9⟩)),
        .scalar ⟨.i8, false, 1⟩]))
    ]
    let place : Place := { localId := 0, projection := [.field 0 optU8Ty] }
    evalRvalueV2 [tupTy] locals MemoryState.empty (.int .i8 false)
      (.discriminant place) = .error .unsupported :=
  rfl

/-- Guard `step_v2_core_panic_local_handler_unsupported`: diverging
`core::panicking::*` calls stay `.fault .unsupported` when
`hasLocalPanicHandler = true`, even under `--panic abort`. -/
theorem refute_step_v2_core_panic_local_handler_unsupported :
    evalCorePanicAbort .abort .unreachable queryEmpty.callerMem true =
      .fault .unsupported ∧
    evalCorePanicAbort .abort .continue_ queryEmpty.callerMem true =
      .fault .unsupported :=
  ⟨rfl, rfl⟩

/-- Guard `step_v2_core_panic_unwind_unsupported`: diverging
`core::panicking::*` calls stay `.fault .unsupported` under `--panic unwind`. -/
theorem refute_step_v2_core_panic_unwind_unsupported :
    evalCorePanicAbort .unwind .continue_ queryEmpty.callerMem false =
      .fault .unsupported ∧
    evalCorePanicAbort .unwind .unreachable queryEmpty.callerMem false =
      .fault .unsupported :=
  ⟨rfl, rfl⟩

/-- Guard `step_v2_core_panic_abort_extract_caller_mem`: pre-abort `&mut`
mutations must survive in `.aborted (extractCallerMemory callerMem mem1)` when
stepping `.coreCall .panicAbort`. -/
theorem refute_step_v2_core_panic_abort_extract_caller_mem :
    (match initStateV2 progMutBeforeCorePanicV2
        { args := [.ptr ⟨some 2, 0, .isize⟩], callerMem := cmBeforeAbort } with
     | .ok s₀ =>
       match evalStepV2 progMutBeforeCorePanicV2 s₀ with
       | .step s₁ =>
         match evalStepV2 progMutBeforeCorePanicV2 s₁ with
         | .done (.aborted cm') => cm' = cmAfterAbort
         | _ => False
       | _ => False
     | .error _ => False) :=
  rfl

/-- Guard `step_v2_core_panic_abort_eval_args`:
`.coreCall .panicAbort` evaluates its `&str` argument (including `.rodataRef`
byte-initialization checks) before aborting, so both an uninitialized `&str`
local and an uninitialized `.rodataRef` operand fault `.fault .undefined`
rather than `.aborted`. -/
theorem refute_step_v2_core_panic_abort_eval_args :
    let uninitTerm : TerminatorKind :=
      .coreCall .panicAbort
        [.copy { localId := 1, projection := [] }]
        { localId := 2, projection := [] } none .unreachable
    let uninitRodataTerm : TerminatorKind :=
      .coreCall .panicAbort
        [.constant ⟨.ref .shared .str, .rodataRef [.uninit] 0 0 (some 1)⟩]
        { localId := 2, projection := [] } none .unreachable
    let body : Body := {
      argumentCount := 0
      locals := [.unit, .ref .shared .str, .never]
      basicBlocks := [{ statements := [], terminator := uninitTerm }]
    }
    let frame : FrameState := {
      defId := 0
      blockIdx := 0
      stmtIdx := 0
      locals := [.immediate none, .immediate none, .immediate none]
    }
    evalTerminatorV2 body { statements := [], terminator := uninitTerm }
      frame MemoryState.empty { allocations := [] } .abort false =
      .fault .undefined ∧
    evalTerminatorV2 body { statements := [], terminator := uninitRodataTerm }
      frame MemoryState.empty { allocations := [] } .abort false =
      .fault .undefined :=
  ⟨rfl, rfl⟩

/-- Guard `step_v2_core_panic_abort_ref_valid`:
`validatePanicAbortArgs` re-validates `refValidInMem` on a local `&str` operand
passed to `.coreCall .panicAbort`, so a dangling `&str` local (including zero
length into a nonexistent allocation) faults `.fault .undefined` rather than
`.aborted` or `.unsupported`. -/
theorem refute_step_v2_core_panic_abort_ref_valid :
    let term : TerminatorKind :=
      .coreCall .panicAbort
        [.copy { localId := 1, projection := [] }]
        { localId := 2, projection := [] } none .unreachable
    let body : Body := {
      argumentCount := 0
      locals := [.unit, .ref .shared .str, .never]
      basicBlocks := [{ statements := [], terminator := term }]
    }
    let danglingStr : Val := .slicePtr ⟨some 99, 0, .isize⟩ 0
    let frame : FrameState := {
      defId := 0
      blockIdx := 0
      stmtIdx := 0
      locals :=
        [.immediate none, .immediate (some danglingStr), .immediate none]
    }
    evalTerminatorV2 body { statements := [], terminator := term }
      frame MemoryState.empty { allocations := [] } .abort false =
      .fault .undefined :=
  rfl

/-- Guard `step_v2_core_panic_abort_non_utf8_unsupported`:
`validatePanicAbortArgs` rejects initialized non-UTF-8 `&str` bytes passed to
`.coreCall .panicAbort` as `.fault .unsupported` rather than `.aborted`. -/
theorem refute_step_v2_core_panic_abort_non_utf8_unsupported :
    let term : TerminatorKind :=
      .coreCall .panicAbort
        [.copy { localId := 1, projection := [] }]
        { localId := 2, projection := [] } none .unreachable
    let body : Body := {
      argumentCount := 0
      locals := [.unit, .ref .shared .str, .never]
      basicBlocks := [{ statements := [], terminator := term }]
    }
    let badUtf8Mem : MemoryState := {
      nextAllocId := 3
      allocations := [{
        allocId := 2
        bytes := [.init 0xff none]
        alignLog2 := 0
        mutability := .shared
        live := true
      }]
    }
    let badStr : Val := .slicePtr ⟨some 2, 0, .isize⟩ 1
    let frame : FrameState := {
      defId := 0
      blockIdx := 0
      stmtIdx := 0
      locals := [.immediate none, .immediate (some badStr), .immediate none]
    }
    evalTerminatorV2 body { statements := [], terminator := term }
      frame badUtf8Mem { allocations := [] } .abort false =
      .fault .unsupported :=
  rfl

/-- Guard `step_v2_ptr_metadata_str_dst_ty`:
`evalRvalueV2` `.unaryOp .ptrMetadata` on `&str` requires `usize` destination
type, failing closed as `.error .unsupported` on non-`usize` destinations. The
`usize` destination canary lives in `PositiveSanity.lean`. -/
theorem refute_step_v2_ptr_metadata_str_dst_ty :
    let localsTys : List MirTy := [.int .isize false, .ref .shared .str]
    let validStr : Val := .slicePtr ⟨some 2, 0, .isize⟩ 2
    let locals : List LocalSlot := [.immediate none, .immediate (some validStr)]
    let mem : MemoryState := {
      nextAllocId := 3
      allocations := [{
        allocId := 2
        bytes := [.init 111 none, .init 107 none]
        alignLog2 := 0
        mutability := .shared
        live := true
      }]
    }
    evalRvalueV2 localsTys locals mem .bool
      (.unaryOp .ptrMetadata (.copy { localId := 1, projection := [] })) =
      .error .unsupported :=
  rfl

/-- Guard `step_v2_ptr_metadata_str_ref_valid`:
`evalRvalueV2` `.unaryOp .ptrMetadata` on `&str` validates `refValidInMem` on
the source slice, faulting `.error .undefined` on a dangling `&str` pointer. -/
theorem refute_step_v2_ptr_metadata_str_ref_valid :
    let localsTys : List MirTy := [.int .isize false, .ref .shared .str]
    let danglingStr : Val := .slicePtr ⟨some 99, 0, .isize⟩ 3
    let locals : List LocalSlot :=
      [.immediate none, .immediate (some danglingStr)]
    evalRvalueV2 localsTys locals MemoryState.empty (.int .isize false)
      (.unaryOp .ptrMetadata (.copy { localId := 1, projection := [] })) =
      .error .undefined :=
  rfl

/-- Guard `step_v2_core_panic_abort_dead_dst_unsupported`:
`.coreCall .panicAbort` requires its `!` destination local slot to be live
(`some (.immediate _)` or `some (.indirect _)`), failing closed as
`.fault .unsupported` when `dst` is `.dead`. -/
theorem refute_step_v2_core_panic_abort_dead_dst_unsupported :
    let term : TerminatorKind :=
      .coreCall .panicAbort [panicOkStrOperand]
        { localId := 1, projection := [] } none .unreachable
    let body : Body := {
      argumentCount := 0
      locals := [.unit, .never]
      basicBlocks := [{ statements := [], terminator := term }]
    }
    let frame : FrameState := {
      defId := 0
      blockIdx := 0
      stmtIdx := 0
      locals := [.immediate none, .dead]
    }
    evalTerminatorV2 body { statements := [], terminator := term }
      frame MemoryState.empty { allocations := [] } .abort false =
      .fault .unsupported :=
  rfl

end GuardMutation
