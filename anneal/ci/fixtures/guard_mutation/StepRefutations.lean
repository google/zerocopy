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

/-!
# Negative Refutations for `Trusted.MirSemantics.Step` UB Guards

Covers every `.undefined` branch and move-deinitialization guard in
`Trusted/MirSemantics/Step.lean`: dead-local copy/move/discriminant/write/
forceAllocation, use-after-move on immediate and indirect locals, uninitialized
primitive/use/cast/discriminant/return reads, and `TerminatorKind.unreachable`.
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

/-- Program moving out of `_1 : u32` and then reading `_1` again without
re-initialization. -/
noncomputable def progUseAfterMove : Program :=
  mkSingleBlockProg 1 [u32Ty, u32Ty]
    [.assign ⟨0, []⟩ (.use (.move ⟨1, []⟩)),
     .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))]

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

/-- Program returning immediately with an uninitialized `_0 : u32`. -/
noncomputable def progReturnUninit : Program :=
  mkSingleBlockProg 0 [u32Ty] [] .return_

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

/-- Program whose local `_1` starts `.dead` because it has a `StorageLive`
annotation in the body. -/
noncomputable def progDeadLocalForForceAlloc : Program :=
  mkSingleBlockProg 0 [.unit, u32Ty] [.storageLive 1] .return_

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

/-- Profile v2 program taking a shared reference to stack parameter `_1 : u8`
and attempting to return it. -/
noncomputable def progDanglingStackRefV2 : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 2
  bodies := [{
    argumentCount := 1
    locals := [.ref .shared (.int .i8 false), .int .i8 false]
    basicBlocks := [{
      statements := [
        .assign { localId := 0, projection := [] }
          (.ref .shared { localId := 1, projection := [] })
      ]
      terminator := .return_
    }]
    isUnsafe := false
    identity := "guard_mutation::dangling_stack_ref_v2"
  }]
}

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

/-- Anti-overreach canary for zero-size raw-pointer dereference stores and
reads (`writePlaceV2` / `readPlaceV2`): `*mut ()` into a dead `.shared`
allocation succeeds consistently with `Memory.lean`. -/
theorem positive_step_v2_zst_raw_ptr_write_and_read :
    (match writePlaceV2
        [.unit, .rawPtr .mut .unit]
        [.immediate (some .unit), .immediate (some (.ptr ⟨some 1, 0, .isize⟩))]
        { allocations := [{
            allocId := 1
            alignLog2 := 0
            mutability := .shared
            bytes := [.init 0 none]
            live := false
          }], nextAllocId := 2 }
        { localId := 1, projection := [.deref] }
        .unit
        .unit with
     | .ok _ => True
     | .error _ => False) ∧
    (match readPlaceV2
        [.unit, .rawPtr .mut .unit]
        [.immediate (some .unit), .immediate (some (.ptr ⟨some 1, 0, .isize⟩))]
        { allocations := [{
            allocId := 1
            alignLog2 := 0
            mutability := .shared
            bytes := [.init 0 none]
            live := false
          }], nextAllocId := 2 }
        false
        { localId := 1, projection := [.deref] } with
     | .ok (.unit, some .unit, _, _) => True
     | _ => False) :=
  ⟨trivial, trivial⟩

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

/-- Anti-overreach canary for `step_v2_ptr_cast_const_to_mut`: `PtrToPtr`
casts that do not add mutability (`*mut u32` to `*const u32`, `*mut u32` to
`*mut u8`, `*const u32` to `*const u8`, and `*mut [u8]` to `*const [u8]`)
still succeed. -/
theorem positive_step_v2_ptr_cast_keeps_or_drops_mut :
    (match evalPtrToPtrCastV2 (.rawPtr .mut (.int .i32 false))
        (.ptr ⟨some 1, 0, .isize⟩) (.rawPtr .shared (.int .i32 false)) with
     | .ok (.ptr ⟨some 1, 0, .isize⟩) => True
     | _ => False) ∧
    (match evalPtrToPtrCastV2 (.rawPtr .mut (.int .i32 false))
        (.ptr ⟨some 1, 0, .isize⟩) (.rawPtr .mut (.int .i8 false)) with
     | .ok (.ptr ⟨some 1, 0, .isize⟩) => True
     | _ => False) ∧
    (match evalPtrToPtrCastV2 (.rawPtr .shared (.int .i32 false))
        (.ptr ⟨some 1, 0, .isize⟩) (.rawPtr .shared (.int .i8 false)) with
     | .ok (.ptr ⟨some 1, 0, .isize⟩) => True
     | _ => False) ∧
    (match evalPtrToPtrCastV2 (.rawPtr .mut (.slice (.int .i8 false)))
        (.slicePtr ⟨some 1, 0, .isize⟩ 4) (.rawPtr .shared (.slice (.int .i8 false))) with
     | .ok (.slicePtr ⟨some 1, 0, .isize⟩ 4) => True
     | _ => False) :=
  ⟨trivial, trivial, trivial, trivial⟩

/-- Admitted zero-sized single-variant fieldless enum (`enum One { A }`). -/
noncomputable def zstOneEnumTy : EnumTy := {
  id := 7
  discrWidth := .isize
  discrSigned := true
  tagRepr := .zeroSized
  discriminants := [0]
}

/-- Anti-overreach canary for provenance-free zero-size reference
dereferences: reading and writing `*r` for `r : &mut One` holding an aligned,
non-null address without provenance succeeds, consistently with
`refValidInMem` admitting such references at entry. -/
theorem positive_step_v2_zst_enum_no_provenance_deref :
    (match readPlaceV2
        [.unit, .ref .mut (.enum zstOneEnumTy)]
        [.immediate (some .unit), .immediate (some (.ptr ⟨none, 1, .isize⟩))]
        MemoryState.empty
        false
        { localId := 1, projection := [.deref] } with
     | .ok (_, some (.enumVal _ 0), _, _) => True
     | _ => False) ∧
    (match writePlaceV2
        [.unit, .ref .mut (.enum zstOneEnumTy)]
        [.immediate (some .unit), .immediate (some (.ptr ⟨none, 1, .isize⟩))]
        MemoryState.empty
        { localId := 1, projection := [.deref] }
        (.enum zstOneEnumTy)
        (.enumVal zstOneEnumTy 0) with
     | .ok _ => True
     | .error _ => False) :=
  ⟨trivial, trivial⟩

/-- Read-only 2-byte allocation with id `1` holding initialized bytes, for
the `get_unchecked` input-mutability refutations. -/
noncomputable def sharedInit2Mem : MemoryState :=
  { allocations := [{
      allocId := 1
      alignLog2 := 0
      mutability := .shared
      bytes := [.init 0 none, .init 0 none]
      live := true
    }], nextAllocId := 2 }

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

/-- Anti-overreach canary: the same `get_unchecked` calls on a `&[u8]` input
over the `.shared` allocation succeed. -/
theorem positive_step_v2_get_unchecked_shared_input :
    (match execCoreCallOp sharedInit2Mem .sliceGetUncheckedRangeTo
        [(.ref .shared (.slice (.int .i8 false)),
            .slicePtr ⟨some 1, 0, .isize⟩ 2),
          (.rangeTo (.int .isize false), .rangeTo 1)]
        (.ref .shared (.slice (.int .i8 false))) with
     | .ok _ => True
     | .error _ => False) ∧
    (match execCoreCallOp sharedInit2Mem .sliceGetUncheckedRangeFrom
        [(.ref .shared (.slice (.int .i8 false)),
            .slicePtr ⟨some 1, 0, .isize⟩ 2),
          (.rangeFrom (.int .isize false), .rangeFrom 1)]
        (.ref .shared (.slice (.int .i8 false))) with
     | .ok _ => True
     | .error _ => False) :=
  ⟨trivial, trivial⟩

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

/-- Anti-overreach canary: `&raw const *p` through the same `*const u8`
still succeeds. -/
theorem positive_step_v2_raw_borrow_const_through_const :
    (match evalAddressOfRvalueV2
        [.unit, .rawPtr .shared (.int .i8 false), .rawPtr .shared (.int .i8 false)]
        [.immediate (some .unit), .immediate (some (.ptr ⟨some 1, 0, .isize⟩)),
          .immediate none]
        { allocations := [{
            allocId := 1
            alignLog2 := 0
            mutability := .mut
            bytes := [.init 0 none]
            live := true
          }], nextAllocId := 2 }
        (.rawPtr .shared (.int .i8 false)) .shared
        { localId := 1, projection := [.deref] } with
     | .ok _ => True
     | .error _ => False) :=
  trivial

/-! ## Partially moved overflow pairs (`LocalSlot.partialTuple`)

Under `-Coverflow-checks=yes`, rustc lowers `x + 1` to
`_t = AddWithOverflow(x, 1)`, `assert(!move (_t.1))`, and
`_r = move (_t.0)`. Moving one field leaves the other readable; the
moved field, and the tuple as a whole, must not be read again. -/

/-- Overflow pair type `(u8, bool)`. -/
noncomputable def overflowPairU8 : MirTy := .tuple [.int .i8 false, .bool]

/-- Local slots after `move (_1.1)`: field 0 still holds `7_u8`. -/
noncomputable def partialPairLocals : List LocalSlot :=
  [.immediate (some .unit),
    .partialTuple [some (.scalar ⟨.i8, false, BitVec.ofNat 128 7⟩), none]]

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

/-- Anti-overreach canary: moving field 1 and then field 0 out of an
initialized overflow pair returns both values, leaves field 0 readable in
between, and restores the uninitialized `.immediate none` slot once both
fields are moved. -/
theorem positive_step_v2_partial_tuple_moves :
    readPlaceV2 [.unit, overflowPairU8]
        [.immediate (some .unit),
          .immediate (some (.tuple
            [.scalar ⟨.i8, false, BitVec.ofNat 128 7⟩, .bool false]))]
        MemoryState.empty true
        { localId := 1, projection := [.field 1 .bool] } =
      .ok (.bool, some (.bool false), partialPairLocals, MemoryState.empty) ∧
    readPlaceV2 [.unit, overflowPairU8] partialPairLocals
        MemoryState.empty false
        { localId := 1, projection := [.field 0 (.int .i8 false)] } =
      .ok (.int .i8 false, some (.scalar ⟨.i8, false, BitVec.ofNat 128 7⟩),
        partialPairLocals, MemoryState.empty) ∧
    readPlaceV2 [.unit, overflowPairU8] partialPairLocals
        MemoryState.empty true
        { localId := 1, projection := [.field 0 (.int .i8 false)] } =
      .ok (.int .i8 false, some (.scalar ⟨.i8, false, BitVec.ofNat 128 7⟩),
        [.immediate (some .unit), .immediate none], MemoryState.empty) :=
  ⟨rfl, rfl, rfl⟩

/-- `buggy_add_u8(x: u8) -> u8 { x + 1 }` as captured under
`-Coverflow-checks=yes --panic abort`. -/
noncomputable def bodyOverflowAddV2 : Body := {
  argumentCount := 1
  locals := [.int .i8 false, .int .i8 false, .int .i8 false, overflowPairU8]
  basicBlocks := [
    { statements := [
        .storageLive 2,
        .assign ⟨2, []⟩ (.use (.copy ⟨1, []⟩)),
        .assign ⟨3, []⟩ (.binaryOp .addWithOverflow (.copy ⟨2, []⟩)
          (.constant ⟨.int .i8 false, .scalar (BitVec.ofNat 128 1)⟩))
      ]
      terminator := .assert (.move ⟨3, [.field 1 .bool]⟩) false
        (.overflow .add) 1 .unreachable },
    { statements := [
        .assign ⟨0, []⟩ (.use (.move ⟨3, [.field 0 (.int .i8 false)]⟩)),
        .storageDead 2
      ]
      terminator := .return_ }
  ]
  isUnsafe := false
  identity := "guard_mutation::overflow_add_v2"
}

/-- Profile v2 program wrapping `bodyOverflowAddV2`. -/
noncomputable def progOverflowAddV2 : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 2
  bodies := [bodyOverflowAddV2]
  overflowChecks := true
}

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

/-- Anti-overreach canary: `progOverflowAddV2` with `x = 254` passes its
overflow assert and returns `255`. -/
theorem positive_step_v2_overflow_assert_passes :
    ∃ out : Out,
      ReachesResultV2 progOverflowAddV2
        { args := [.scalar ⟨.i8, false, BitVec.ofNat 128 254⟩] }
        (.done (.returned out)) ∧
      out.ret = .scalar ⟨.i8, false, BitVec.ofNat 128 255⟩ := by
  apply Exists.intro
  constructor
  · unfold ReachesResultV2
    change ∃ s : State, ReachesV2 progOverflowAddV2 _ s ∧
      StepV2 progOverflowAddV2 s _
    exact ⟨_,
      ReachesV2.tail (ReachesV2.tail (ReachesV2.tail (ReachesV2.tail
        (ReachesV2.tail (ReachesV2.tail (ReachesV2.refl _)
          ⟨0, rfl, rfl⟩) ⟨0, rfl, rfl⟩) ⟨0, rfl, rfl⟩) ⟨0, rfl, rfl⟩)
        ⟨0, rfl, rfl⟩) ⟨0, rfl, rfl⟩,
      ⟨0, rfl, rfl⟩⟩
  · rfl

end GuardMutation
