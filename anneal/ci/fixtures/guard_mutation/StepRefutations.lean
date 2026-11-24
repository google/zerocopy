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

/-! The run below is split into one declaration per state so that no single
proof has to evaluate all seven steps of `progOverflowAddV2`. -/

/-- `progOverflowAddV2` called with `x = 254`. -/
noncomputable def queryOverflowAdd254 : Query :=
  { args := [.scalar ⟨.i8, false, BitVec.ofNat 128 254⟩] }

/-- Entry state of `progOverflowAddV2` on `queryOverflowAdd254`. -/
noncomputable def overflowAdd254S0 : State :=
  match initStateV2 progOverflowAddV2 queryOverflowAdd254 with
  | .ok s => s
  | .error _ => { frames := [], mem := MemoryState.empty }

/-- Successor of `s` under `progOverflowAddV2` (or `s` itself when the step
does not continue). -/
noncomputable def overflowAdd254Next (s : State) : State :=
  match evalStepV2 progOverflowAddV2 s with
  | .step s' => s'
  | _ => s

noncomputable def overflowAdd254S1 : State :=
  overflowAdd254Next overflowAdd254S0
noncomputable def overflowAdd254S2 : State :=
  overflowAdd254Next overflowAdd254S1
noncomputable def overflowAdd254S3 : State :=
  overflowAdd254Next overflowAdd254S2
noncomputable def overflowAdd254S4 : State :=
  overflowAdd254Next overflowAdd254S3
noncomputable def overflowAdd254S5 : State :=
  overflowAdd254Next overflowAdd254S4
noncomputable def overflowAdd254S6 : State :=
  overflowAdd254Next overflowAdd254S5

/-- Terminal output of the final step from `overflowAdd254S6`. -/
noncomputable def overflowAdd254Out : Out :=
  match evalStepV2 progOverflowAddV2 overflowAdd254S6 with
  | .done (.returned out) => out
  | _ => ⟨.unit, ⟨[]⟩⟩

theorem overflowAdd254_init :
    initStateV2 progOverflowAddV2 queryOverflowAdd254 = .ok overflowAdd254S0 :=
  rfl

theorem overflowAdd254_step1 :
    StepV2 progOverflowAddV2 overflowAdd254S0 (.step overflowAdd254S1) :=
  ⟨0, rfl, rfl⟩

theorem overflowAdd254_step2 :
    StepV2 progOverflowAddV2 overflowAdd254S1 (.step overflowAdd254S2) :=
  ⟨0, rfl, rfl⟩

theorem overflowAdd254_step3 :
    StepV2 progOverflowAddV2 overflowAdd254S2 (.step overflowAdd254S3) :=
  ⟨0, rfl, rfl⟩

theorem overflowAdd254_step4 :
    StepV2 progOverflowAddV2 overflowAdd254S3 (.step overflowAdd254S4) :=
  ⟨0, rfl, rfl⟩

theorem overflowAdd254_step5 :
    StepV2 progOverflowAddV2 overflowAdd254S4 (.step overflowAdd254S5) :=
  ⟨0, rfl, rfl⟩

theorem overflowAdd254_step6 :
    StepV2 progOverflowAddV2 overflowAdd254S5 (.step overflowAdd254S6) :=
  ⟨0, rfl, rfl⟩

theorem overflowAdd254_done :
    StepV2 progOverflowAddV2 overflowAdd254S6
      (.done (.returned overflowAdd254Out)) :=
  ⟨0, rfl, rfl⟩

theorem overflowAdd254_ret :
    overflowAdd254Out.ret = .scalar ⟨.i8, false, BitVec.ofNat 128 255⟩ :=
  rfl

/-- Anti-overreach canary: `progOverflowAddV2` with `x = 254` passes its
overflow assert and returns `255`. -/
theorem positive_step_v2_overflow_assert_passes :
    ∃ out : Out,
      ReachesResultV2 progOverflowAddV2
        { args := [.scalar ⟨.i8, false, BitVec.ofNat 128 254⟩] }
        (.done (.returned out)) ∧
      out.ret = .scalar ⟨.i8, false, BitVec.ofNat 128 255⟩ := by
  refine ⟨overflowAdd254Out, ?_, overflowAdd254_ret⟩
  change ReachesResultV2 progOverflowAddV2 queryOverflowAdd254 _
  unfold ReachesResultV2
  rw [overflowAdd254_init]
  exact ⟨_,
    ReachesV2.tail (ReachesV2.tail (ReachesV2.tail (ReachesV2.tail
      (ReachesV2.tail (ReachesV2.tail (ReachesV2.refl _)
        overflowAdd254_step1) overflowAdd254_step2) overflowAdd254_step3)
      overflowAdd254_step4) overflowAdd254_step5) overflowAdd254_step6,
    overflowAdd254_done⟩

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
    let bb : BasicBlock := { statements := [], terminator := .return_, cleanup := false }
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
destination resolution before evaluating an `.unsupported` rvalue, and
`updateValAtProjV2` updates `RangeTo`/`RangeFrom` `.field 0`. -/
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
     | _ => False) ∧
    (match updateValAtProjV2
        (.rangeTo (.int .isize false)) (.rangeTo 1)
        [.field 0 (.int .isize false)] (.scalar ⟨.isize, false, 7⟩) with
     | .ok (.rangeTo 7) => True
     | _ => False) ∧
    (match updateValAtProjV2
        (.rangeFrom (.int .isize false)) (.rangeFrom 2)
        [.field 0 (.int .isize false)] (.scalar ⟨.isize, false, 9⟩) with
     | .ok (.rangeFrom 9) => True
     | _ => False) :=
  ⟨trivial, trivial, trivial⟩

/-- Profile v2 program under `--panic abort` writing `7 : u8` through `&mut u8`
before failing a non-optional `.divByZero` assert. -/
noncomputable def progMutBeforeAbortV2 : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 2
  panicStrategy := .abort
  hasLocalPanicHandler := false
  bodies := [{
    argumentCount := 1
    locals := [.unit, .ref .mut u8Ty]
    basicBlocks := [{
      statements := [
        .assign { localId := 1, projection := [.deref] }
          (.use (.constant ⟨u8Ty, .scalar (BitVec.ofNat 128 7)⟩))
      ]
      terminator :=
        .assert (.constant ⟨.bool, .scalar (BitVec.ofNat 128 0)⟩) true
          .divByZero 0 .unreachable
    }]
    isUnsafe := false
    identity := "guard_mutation::mut_before_abort_v2"
  }]
}

private def cmBeforeAbort : CallerMemory := {
  allocations := [{
    allocId := 2
    alignLog2 := 0
    mutability := .mut
    bytes := [.init 0 none]
    live := true
  }]
}

private def cmAfterAbort : CallerMemory := {
  allocations := [{
    allocId := 2
    alignLog2 := 0
    mutability := .mut
    bytes := [.init 7 none]
    live := true
  }]
}

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

/-- Guard `step_assert_optional_overflow_unsupported`: under `--panic abort`,
optional overflow checks (`.overflow .add` and `.overflowNeg`) stay
`.fault .unsupported` rather than aborting cleanly. -/
theorem refute_step_assert_optional_overflow_unsupported :
    evalAssertFailure (.overflow .add) .abort .unreachable
        queryEmpty.callerMem false = .fault .unsupported ∧
      evalAssertFailure .overflowNeg .abort .unreachable
        queryEmpty.callerMem false = .fault .unsupported :=
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

end GuardMutation
