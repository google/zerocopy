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
# Negative Refutations for `Trusted.MirSemantics.Step` Guards

Covers every `.undefined` branch, move-deinitialization guard, projection
guard, static type-check guard, storage-lifecycle guard, switch-case guard,
`TerminatorKind.assert` guard, cleanup-return guard, and fail-closed unmodeled
statement/terminator guard in `Trusted/MirSemantics/Step.lean`.
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
`-Coverflow-checks=yes --panic abort` (hence the `.unreachable` unwind
action). -/
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

/-- Profile v2 program wrapping `bodyOverflowAddV2`, with overflow checks and
the default `.unwind` panic strategy, under which a failed overflow assert
faults rather than aborting. -/
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

/-- Guard `step_v2_core_call_partial_eq_ne_routed`: `execCoreCallOpWithMem`
routes `CoreCallOp.partialEqNe` to `execCoreCallOp`, so `ne` on two equal
`[u8; 2]` values returns `false` (dropping the route falls through to the
`core` contracts, which fault `.unsupported`). -/
theorem refute_step_v2_core_call_partial_eq_ne_routed :
    (match execCoreCallOpWithMem
        { allocations := [{
            allocId := 1
            alignLog2 := 0
            mutability := .shared
            bytes := [.init 1 none, .init 2 none]
            live := true
          }], nextAllocId := 2 }
        (.partialEqNe (.array (.int .i8 false) 2))
        [(.ref .shared (.array (.int .i8 false) 2), .ptr ⟨some 1, 0, .isize⟩),
         (.ref .shared (.array (.int .i8 false) 2), .ptr ⟨some 1, 0, .isize⟩)]
        .bool with
     | .ok (.bool false, _) => True
     | _ => False) :=
  trivial

/-- Guard `step_v2_dest_deref_projection_ub`: an out-of-bounds constant index
below a dereferenced `&mut [u8; 4]` destination faults with `.undefined`
(the `projectMemoryLayoutV2` fault), not `.unsupported`. -/
theorem refute_step_v2_dest_deref_projection_ub :
    (match resolvePlaceDestV2 [.unit, .ref .mut (.array (.int .i8 false) 4)]
        [.immediate none, .immediate (some (.ptr ⟨some 1, 0, .isize⟩))]
        emptyMemory ⟨1, [.deref, .constantIndex 4 5 false]⟩ (.int .i8 false) with
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

/-- Anti-overreach canary for the two guards above: with `overflowChecks`, no
crate-local `#[panic_handler]`, and `--panic abort`, a failed checked overflow
assertion aborts with the caller memory, while under `--panic unwind` it still
faults. -/
theorem positive_step_assert_checked_overflow_aborts :
    evalAssertFailure (.overflow .add) .abort .unreachable
        queryEmpty.callerMem false true =
      .done (.aborted queryEmpty.callerMem) ∧
      evalAssertFailure .overflowNeg .abort .continue_
        queryEmpty.callerMem false true =
        .done (.aborted queryEmpty.callerMem) ∧
      evalAssertFailure (.overflow .shl) .unwind .unreachable
        queryEmpty.callerMem false true = .fault .unsupported :=
  ⟨rfl, rfl, rfl⟩

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
local `a = a` on `[u8; 4]`, and `*p = *p` on padded `(u32, bool)`), while
permitting zero-sized (`[u8; 0]`, `[u32; 0]`), `Scalar` (`u32`,
`([u32; 0], u32)`), padding-free `ScalarPair` (`(u32, u32)`, `(u8, bool)`), and
disjoint element (`a[0] = a[1]`) copies. -/
theorem refute_step_v2_assign_use_overlap_ub :
    let arr4Ty : MirTy := .array u8Ty 4
    let zstArrTy : MirTy := .array (.int .i32 false) 0
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
    let bodyNoPadPair : Body := {
      argumentCount := 0
      locals := [.unit, .tuple [u8Ty, .bool], .tuple [.int .i32 false, .int .i32 false],
                 zstArrTy, .tuple [zstArrTy, .int .i32 false]]
      basicBlocks := []
    }
    let frameNoPadPair : FrameState := {
      defId := 0, blockIdx := 0, stmtIdx := 0
      locals := [
        .immediate none,
        .immediate (some (.tuple [.scalar ⟨.i8, false, 9⟩, .bool true])),
        .immediate (some (.tuple [.scalar ⟨.i32, false, 1⟩, .scalar ⟨.i32, false, 2⟩])),
        .immediate (some (.array [])),
        .immediate (some (.tuple [.array [], .scalar ⟨.i32, false, 7⟩]))
      ]
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
    -- Negative (must fault `.undefined`):
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
     | _ => False) ∧
    -- Positive anti-overreach (must step cleanly):
    (match evalStatementV2 bodyNoPadPair frameNoPadPair emptyMemory { allocations := [] }
        (.assign { localId := 1, projection := [] }
          (.use (.copy { localId := 1, projection := [] }))) with
     | .step _ => True
     | _ => False) ∧
    (match evalStatementV2 bodyNoPadPair frameNoPadPair emptyMemory { allocations := [] }
        (.assign { localId := 2, projection := [] }
          (.use (.copy { localId := 2, projection := [] }))) with
     | .step _ => True
     | _ => False) ∧
    (match evalStatementV2 bodyNoPadPair frameNoPadPair emptyMemory { allocations := [] }
        (.assign { localId := 3, projection := [] }
          (.use (.copy { localId := 3, projection := [] }))) with
     | .step _ => True
     | _ => False) ∧
    (match evalStatementV2 bodyNoPadPair frameNoPadPair emptyMemory { allocations := [] }
        (.assign { localId := 4, projection := [] }
          (.use (.copy { localId := 4, projection := [] }))) with
     | .step _ => True
     | _ => False) ∧
    (match evalStatementV2 bodyArrOfArr frameArrOfArr emptyMemory { allocations := [] }
        (.assign { localId := 1, projection := [.constantIndex 0 2 false] }
          (.use (.copy { localId := 1, projection := [.constantIndex 1 2 false] }))) with
     | .step _ => True
     | _ => False) :=
  ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩

/-- Guard `step_v2_assign_aggregate_clobber_unsupported`: in-place `Aggregate`
where an earlier field write (`_1.0`) aliases a later operand (`_1.0` in
`_1 = (_1.1, _1.0)`) fails closed with `.fault .unsupported`, whereas
non-clobbering scalar `_1 = (_1.0, _1.1)` steps cleanly. -/
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
     | _ => False) ∧
    (match evalStatementV2 body frame emptyMemory { allocations := [] }
        (.assign { localId := 1, projection := [] }
          (.aggregateTuple [
            .copy { localId := 1, projection := [.field 0 u32Ty] },
            .copy { localId := 1, projection := [.field 1 u32Ty] }
          ])) with
     | .step _ => True
     | _ => False) :=
  ⟨trivial, trivial⟩

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
the conservative `baseSpan` path), whereas reading `*_2` at field 0 before `_2`
is overwritten steps cleanly. -/
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
     | _ => False) ∧
    (match checkAggregateCopyHazardLoopV2 body.locals frame.locals mem
        (.memRange 2 0 12) tup3Ty false 0 [] [u32Ty, u32Ty, u32Ty] [
          .copy { localId := 2, projection := [.deref] },
          .copy { localId := 1, projection := [] },
          .copy { localId := 1, projection := [] }
        ] with
     | .ok () => True
     | _ => False) ∧
    (match evalStatementV2 body frame mem { allocations := [] }
        (.assign { localId := 3, projection := [.deref] }
          (.aggregateArray u32Ty [
            .copy { localId := 2, projection := [.deref] },
            .copy { localId := 1, projection := [] }
          ])) with
     | .step _ => True
     | _ => False) :=
  ⟨trivial, trivial, trivial, trivial⟩

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
`.fault .undefined`, while `a = [a[1]; 2]` (disjoint from `a[0]`) steps
cleanly. -/
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
     | _ => False) ∧
    (match evalStatementV2 body frame emptyMemory { allocations := [] }
        (.assign { localId := 1, projection := [] }
          (.repeat_ (.copy { localId := 1, projection := [.constantIndex 1 2 false] })
            arr4Ty 2)) with
     | .step _ => True
     | _ => False) :=
  ⟨trivial, trivial⟩

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

/-- Guard `step_v2_index_dead_local`: `ProjectionElem.index` through a dead
`usize` index local faults with `.undefined`. -/
theorem refute_step_v2_index_dead_local :
    (match evalRvalueV2
        [.int .i8 false, .array (.int .i8 false) 2, .int .isize false]
        [.immediate none,
         .immediate (some (.array [.scalar ⟨.i8, false, BitVec.ofNat 128 1⟩,
           .scalar ⟨.i8, false, BitVec.ofNat 128 2⟩])),
         .dead]
        emptyMemory (.int .i8 false) (.use (.copy ⟨1, [.index 2]⟩)) with
     | .error .undefined => True
     | _ => False) :=
  trivial

/-- Guard `core_contracts_slice_split_at_in_mut`: `slice::split_at(1)` on a
`&mut [u8]` input over a `.shared` allocation faults with `.undefined` even
though `reqMut = .shared`, because `execSliceSplitAt` validates the input at
`inMut`. -/
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

/-- Guard `step_v2_index_uninit_local`: `ProjectionElem.index` through an
uninitialized `usize` index local faults with `.undefined`. -/
theorem refute_step_v2_index_uninit_local :
    (match evalRvalueV2
        [.int .i8 false, .array (.int .i8 false) 2, .int .isize false]
        [.immediate none,
         .immediate (some (.array [.scalar ⟨.i8, false, BitVec.ofNat 128 1⟩,
           .scalar ⟨.i8, false, BitVec.ofNat 128 2⟩])),
         .immediate none]
        emptyMemory (.int .i8 false) (.use (.copy ⟨1, [.index 2]⟩)) with
     | .error .undefined => True
     | _ => False) :=
  trivial

/-- Anti-overreach canary: the same `Index::index` and `split_at` calls on a
`&[u8]` input over the `.shared` allocation succeed. -/
theorem positive_core_contracts_slice_shared_input :
    (match execCoreContractOp sharedInit2Mem
        (.sliceIndexRange .shared (.int .i8 false))
        [(.ref .shared (.slice (.int .i8 false)),
            .slicePtr ⟨some 1, 0, .isize⟩ 2),
          (.range (.int .isize false), .range 0 1)]
        (.ref .shared (.slice (.int .i8 false))) with
     | .ok _ => True
     | .error _ => False) ∧
    (match execCoreContractOp sharedInit2Mem
        (.sliceSplitAt .shared (.int .i8 false))
        [(.ref .shared (.slice (.int .i8 false)),
            .slicePtr ⟨some 1, 0, .isize⟩ 2),
          (.int .isize false, .scalar ⟨.isize, false, 1⟩)]
        (.tuple [.ref .shared (.slice (.int .i8 false)),
          .ref .shared (.slice (.int .i8 false))]) with
     | .ok _ => True
     | .error _ => False) :=
  ⟨trivial, trivial⟩

/-- Guard `core_contracts_i128_host_overflow`: 128-bit checked, saturating,
and overflowing arithmetic detect mathematical overflow (`intHostOverflow`)
before `BitVec 128` carrier truncation across unsigned and signed edges. -/
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

/-- Anti-overreach canary: in-bounds 128-bit checked, saturating, and
overflowing arithmetic succeed without false overflow. -/
theorem positive_core_contracts_i128_in_bounds :
    let u128Ty : MirTy := .int .i128 false
    let u128MaxMinus1 : ScalarVal :=
      ⟨.i128, false, BitVec.ofNat 128 340282366920938463463374607431768211454⟩
    let u128Max : ScalarVal :=
      ⟨.i128, false, BitVec.ofNat 128 340282366920938463463374607431768211455⟩
    let u128One : ScalarVal := ⟨.i128, false, 1⟩
    let u128Two : ScalarVal := ⟨.i128, false, 2⟩
    let u128Three : ScalarVal := ⟨.i128, false, 3⟩
    execCoreContractOp MemoryState.empty (.numCheckedAdd .i128 false)
      [(u128Ty, .scalar u128One), (u128Ty, .scalar u128Two)]
      (.option u128Ty) =
      .ok (.optionVal (some (.scalar u128Three)), MemoryState.empty) ∧
    execCoreContractOp MemoryState.empty (.numSaturatingAdd .i128 false)
      [(u128Ty, .scalar u128MaxMinus1), (u128Ty, .scalar u128One)] u128Ty =
      .ok (.scalar u128Max, MemoryState.empty) ∧
    execCoreContractOp MemoryState.empty (.numOverflowingAdd .i128 false)
      [(u128Ty, .scalar u128One), (u128Ty, .scalar u128Two)]
      (.tuple [u128Ty, .bool]) =
      .ok (.tuple [.scalar u128Three, .bool false], MemoryState.empty) :=
  ⟨rfl, rfl, rfl⟩

/-- Guard `bytes_v2_slice_uninhabited_elem`: `refValidInMem` rejects
positive-length `&[!]` and `&mut [!]` slices (both provenance-free dangling
pointers and provenance-backed allocations) with `.error .undefined`. -/
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

/-- Anti-overreach canary: empty `&[] : &[!]` (`len = 0`) and positive-length
inhabited ZST `&[()]` slices remain valid under `refValidInMem`. -/
theorem positive_bytes_v2_slice_empty_never_and_zst_unit :
    refValidInMem MemoryState.empty .shared (.slice .never)
      (.slicePtr ⟨none, 1, .isize⟩ 0) = .ok () ∧
    refValidInMem MemoryState.empty .shared (.slice .unit)
      (.slicePtr ⟨none, 1, .isize⟩ 3) = .ok () :=
  ⟨rfl, rfl⟩

/-- Guard `core_contracts_option_unwrap_refs_valid`: `Option::unwrap` on
`Some(&u8)` pointing into a dead allocation faults `.undefined` via
`refsValidInMem`, while a live `Some(&u8)` succeeds. -/
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
    let liveMem : MemoryState := {
      allocations := [{
        allocId := 2
        alignLog2 := 0
        mutability := .shared
        bytes := [.init 7 none]
        live := true
      }]
      nextAllocId := 3
    }
    execCoreContractOp deadMem (.optionUnwrap refU8Ty)
      [(.option refU8Ty, .optionVal (some (.ptr ⟨some 2, 0, .isize⟩)))]
      refU8Ty = .error .undefined ∧
    execCoreContractOp liveMem (.optionUnwrap refU8Ty)
      [(.option refU8Ty, .optionVal (some (.ptr ⟨some 2, 0, .isize⟩)))]
      refU8Ty = .ok (.ptr ⟨some 2, 0, .isize⟩, liveMem) :=
  ⟨rfl, rfl⟩

/-- Guard `step_v2_option_discriminant_dst_ty`: projected `Option` discriminant
returns `0isize`/`1isize` for `isize` destination and rejects mismatched
`dstTy` with `.unsupported`. -/
theorem refute_step_v2_option_discriminant_dst_ty :
    let optU8Ty : MirTy := .option (.int .i8 false)
    let tupTy : MirTy := .tuple [optU8Ty, .int .i8 false]
    let locals : List LocalSlot := [
      .immediate (some (.tuple [.optionVal (some (.scalar ⟨.i8, false, 9⟩)),
        .scalar ⟨.i8, false, 1⟩]))
    ]
    let place : Place := { localId := 0, projection := [.field 0 optU8Ty] }
    evalRvalueV2 [tupTy] locals MemoryState.empty (.int .i8 false)
      (.discriminant place) = .error .unsupported ∧
    evalRvalueV2 [tupTy] locals MemoryState.empty (.int .isize true)
      (.discriminant place) =
      .ok (.scalar ⟨.isize, true, BitVec.ofNat 128 1⟩, locals,
        MemoryState.empty) :=
  ⟨rfl, rfl⟩

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

/-- Shared valid `&'static str` `"ok"` rodata operand for `.panicAbort`
guard-mutation fixtures. -/
def panicOkStrOperand : Operand :=
  .constant ⟨.ref .shared .str, .rodataRef [.init 111, .init 107] 0 0 (some 2)⟩

/-- Profile v2 program under `--panic abort` writing `7 : u8` through `&mut u8`
before executing `.coreCall .panicAbort`. -/
noncomputable def progMutBeforeCorePanicV2 : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 2
  panicStrategy := .abort
  hasLocalPanicHandler := false
  bodies := [{
    argumentCount := 1
    locals := [.unit, .ref .mut u8Ty, .never]
    basicBlocks := [{
      statements := [
        .assign { localId := 1, projection := [.deref] }
          (.use (.constant ⟨u8Ty, .scalar (BitVec.ofNat 128 7)⟩))
      ]
      terminator :=
        .coreCall .panicAbort [panicOkStrOperand]
          { localId := 2, projection := [] } none .unreachable
    }]
    isUnsafe := false
    identity := "guard_mutation::mut_before_core_panic_v2"
  }]
}

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
type, returning `.ok` on `usize` and failing closed as `.error .unsupported` on
non-`usize` destinations. -/
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
    evalRvalueV2 localsTys locals mem (.int .isize false)
      (.unaryOp .ptrMetadata (.copy { localId := 1, projection := [] })) =
      .ok (.scalar ⟨.isize, false, BitVec.ofNat 128 2⟩, locals, mem) ∧
    evalRvalueV2 localsTys locals mem .bool
      (.unaryOp .ptrMetadata (.copy { localId := 1, projection := [] })) =
      .error .unsupported :=
  ⟨rfl, rfl⟩

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

/-- Program copying from a projected place `_1.0`. -/
noncomputable def progCopyProjected : Program :=
  mkSingleBlockProg 1 [u32Ty, u32Ty]
    [.assign ⟨0, []⟩ (.use (.copy ⟨1, [.field 0 u32Ty]⟩))]

/-- Guard `step_copy_imm_reject_projection`: `Operand.copy` on an immediate
local with a non-empty projection faults with `.unsupported`. -/
theorem refute_step_copy_imm_reject_projection :
    ReachesResult progCopyProjected { args := [u32Val 7] }
      (.fault .unsupported) ∧
    ¬ WellFormed progCopyProjected { args := [u32Val 7] } :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `step_copy_indirect_reject_projection`: `Operand.copy` on an
`.indirect` local with a non-empty projection faults with `.unsupported`. -/
theorem refute_step_copy_indirect_reject_projection :
    (match initState progCopyProjected { args := [u32Val 7] } with
     | .ok s₀ =>
       match forceAllocation progCopyProjected s₀ 1 with
       | .ok (s₁, _) =>
         evalStep progCopyProjected 0 s₁ = .fault .unsupported
       | .error _ => False
     | .error _ => False) :=
  rfl

/-- Program copying `_1 : bool` into `_0 : u32` (type mismatch), used to test
that `evalOperandToSlot`'s static `tyOk` check precedes indirect byte decoding.
-/
noncomputable def progCopyBoolToU32 : Program :=
  mkSingleBlockProg 1 [u32Ty, .bool]
    [.assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))]

/-- Guard `step_copy_indirect_tyok_before_load`: copying an `.indirect` `bool`
local whose memory holds invalid byte `2` into a `u32` destination faults
`.unsupported` (static type check) rather than `.undefined` (byte decode). -/
theorem refute_step_copy_indirect_tyok_before_load :
    (match initState progCopyBoolToU32 { args := [.bool false] } with
     | .ok s₀ =>
       match forceAllocation progCopyBoolToU32 s₀ 1 with
       | .ok (s₁, mplace) =>
         match writeBytes s₁.mem mplace 0 [.init 2 none] with
         | .ok memBad =>
           evalStep progCopyBoolToU32 0 { s₁ with mem := memBad } =
             .fault .unsupported
         | .error _ => False
       | .error _ => False
     | .error _ => False) :=
  rfl

/-- Program moving from a projected place `_1.0`. -/
noncomputable def progMoveProjected : Program :=
  mkSingleBlockProg 1 [u32Ty, u32Ty]
    [.assign ⟨0, []⟩ (.use (.move ⟨1, [.field 0 u32Ty]⟩))]

/-- Guard `step_move_imm_reject_projection`: `Operand.move` on an immediate
local with a non-empty projection faults with `.unsupported`. -/
theorem refute_step_move_imm_reject_projection :
    ReachesResult progMoveProjected { args := [u32Val 7] }
      (.fault .unsupported) ∧
    ¬ WellFormed progMoveProjected { args := [u32Val 7] } :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `step_move_indirect_reject_projection`: `Operand.move` on an
`.indirect` local with a non-empty projection faults with `.unsupported`. -/
theorem refute_step_move_indirect_reject_projection :
    (match initState progMoveProjected { args := [u32Val 7] } with
     | .ok s₀ =>
       match forceAllocation progMoveProjected s₀ 1 with
       | .ok (s₁, _) =>
         evalStep progMoveProjected 0 s₁ = .fault .unsupported
       | .error _ => False
     | .error _ => False) :=
  rfl

/-- Program moving `_1 : bool` into `_0 : u32` (type mismatch). -/
noncomputable def progMoveBoolToU32 : Program :=
  mkSingleBlockProg 1 [u32Ty, .bool]
    [.assign ⟨0, []⟩ (.use (.move ⟨1, []⟩))]

/-- Guard `step_move_indirect_tyok_before_load`: moving an `.indirect` `bool`
local whose memory holds invalid byte `2` into a `u32` destination faults
`.unsupported` (static type check) rather than `.undefined` (byte decode). -/
theorem refute_step_move_indirect_tyok_before_load :
    (match initState progMoveBoolToU32 { args := [.bool false] } with
     | .ok s₀ =>
       match forceAllocation progMoveBoolToU32 s₀ 1 with
       | .ok (s₁, mplace) =>
         match writeBytes s₁.mem mplace 0 [.init 2 none] with
         | .ok memBad =>
           evalStep progMoveBoolToU32 0 { s₁ with mem := memBad } =
             .fault .unsupported
         | .error _ => False
       | .error _ => False
     | .error _ => False) :=
  rfl

/-- Program executing `switchInt` on a non-primitive-readable `.ordering`
local with an empty branch table (jumping to `bb1` return if not rejected). -/
noncomputable def progSwitchOrderingEmpty : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [.unit, .ordering]
    basicBlocks := [
      { statements := []
        terminator := .switchInt (.copy ⟨1, []⟩) ⟨[], 1⟩ },
      { statements := []
        terminator := .return_ }
    ]
  }]

/-- Guard `step_prim_operand_requires_primitive_ty`: `evalPrimitiveOperand`
rejects non-primitive-readable `.ordering` in `switchInt` with `.unsupported`.
-/
theorem refute_step_prim_operand_requires_primitive_ty :
    ReachesResult progSwitchOrderingEmpty { args := [.ordering .equal] }
      (.fault .unsupported) ∧
    ¬ WellFormed progSwitchOrderingEmpty { args := [.ordering .equal] } :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Program copying an uninitialized `u8` local `_1` into `_0 : u32`. -/
noncomputable def progUseUninitTypeMismatch : Program :=
  mkSingleBlockProg 0 [u32Ty, u8Ty]
    [.storageLive 1, .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))]

/-- Guard `step_use_type_mismatch`: `evalRvalue .use` rejects mismatched
source/destination types (`u8` into `u32`) with `.unsupported` before
uninitialized `.undefined`. -/
theorem refute_step_use_type_mismatch :
    ReachesResult progUseUninitTypeMismatch queryEmpty (.fault .unsupported) ∧
    ¬ WellFormed progUseUninitTypeMismatch queryEmpty :=
  refutes_wf_of_execFault (fuel := 2) rfl

/-- Program casting an uninitialized `.ordering` local `_1` to `u8` via
`CastKind.intToInt`. -/
noncomputable def progCastNonIntLikeSrc : Program :=
  mkSingleBlockProg 0 [u8Ty, .ordering]
    [.storageLive 1, .assign ⟨0, []⟩ (.cast .intToInt (.copy ⟨1, []⟩) u8Ty)]

/-- Guard `step_cast_requires_intlike_src`: `evalRvalue (.cast .intToInt)`
rejects non-integer-like `.ordering` source with `.unsupported` before
uninitialized `.undefined`. -/
theorem refute_step_cast_requires_intlike_src :
    ReachesResult progCastNonIntLikeSrc queryEmpty (.fault .unsupported) ∧
    ¬ WellFormed progCastNonIntLikeSrc queryEmpty :=
  refutes_wf_of_execFault (fuel := 2) rfl

/-- Program reading `Rvalue.discriminant` on a projected enum place `_1.0`. -/
noncomputable def progDiscrProjected : Program :=
  mkSingleBlockProg 1 [u8Ty, .enum reprU8EnumTy]
    [.assign ⟨0, []⟩ (.discriminant ⟨1, [.field 0 u8Ty]⟩)]

/-- Guard `step_discriminant_imm_reject_projection`: `evalRvalue .discriminant`
rejects a projected immediate place with `.unsupported`. -/
theorem refute_step_discriminant_imm_reject_projection :
    ReachesResult progDiscrProjected { args := [.enumVal reprU8EnumTy 0] }
      (.fault .unsupported) ∧
    ¬ WellFormed progDiscrProjected { args := [.enumVal reprU8EnumTy 0] } :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `step_discriminant_indirect_reject_projection`:
`evalRvalue .discriminant` rejects a projected `.indirect` place with
`.unsupported`. -/
theorem refute_step_discriminant_indirect_reject_projection :
    (match initState progDiscrProjected { args := [.enumVal reprU8EnumTy 0] } with
     | .ok s₀ =>
       match forceAllocation progDiscrProjected s₀ 1 with
       | .ok (s₁, _) =>
         evalStep progDiscrProjected 0 s₁ = .fault .unsupported
       | .error _ => False
     | .error _ => False) :=
  rfl

/-- Program assigning the `.bool` result of `BinOp.eq` into a `u8` destination
`_0`. -/
noncomputable def progWritePlaceTypeMismatch : Program :=
  mkSingleBlockProg 2 [u8Ty, u32Ty, u32Ty]
    [.assign ⟨0, []⟩ (.binaryOp .eq (.copy ⟨1, []⟩) (.copy ⟨2, []⟩))]

/-- Guard `step_write_place_check_val`: `writePlace` rejects writing a `.bool`
value into a `u8` destination with `.unsupported`. -/
theorem refute_step_write_place_check_val :
    ReachesResult progWritePlaceTypeMismatch { args := [u32Val 1, u32Val 1] }
      (.fault .unsupported) ∧
    ¬ WellFormed progWritePlaceTypeMismatch { args := [u32Val 1, u32Val 1] } :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Program executing `StorageDead 1` on a `u32` parameter `_1`. -/
noncomputable def progStorageDeadArg : Program :=
  mkSingleBlockProg 1 [.unit, u32Ty] [.storageDead 1] .return_

/-- Guard `step_deallocate_local_indirect`: `deallocateLocal` deallocates the
stack allocation of an `.indirect` local on `StorageDead`, so reading its old
`MemPlace` faults with `.undefined`. -/
theorem refute_step_deallocate_local_indirect :
    (match initState progStorageDeadArg { args := [u32Val 7] } with
     | .ok s₀ =>
       match forceAllocation progStorageDeadArg s₀ 1 with
       | .ok (s₁, mplace) =>
         match evalStep progStorageDeadArg 0 s₁ with
         | .step s₂ =>
           readBytes s₂.mem mplace 4 2 = .error .undefined
         | _ => False
       | .error _ => False
     | .error _ => False) :=
  rfl

/-- Program re-executing `StorageLive 1` on an already-initialized `u32`
parameter `_1` and then reading `_1`. -/
noncomputable def progStorageLiveReinit : Program :=
  mkSingleBlockProg 1 [u32Ty, u32Ty]
    [.storageLive 1, .assign ⟨0, []⟩ (.use (.copy ⟨1, []⟩))]

/-- Guard `step_storage_live_reinits_local`: `StorageLive` resets an
already-live non-ZST local to uninitialized so reading it faults `.undefined`.
-/
theorem refute_step_storage_live_reinits_local :
    ReachesResult progStorageLiveReinit { args := [u32Val 7] }
      (.fault .undefined) ∧
    ¬ WellFormed progStorageLiveReinit { args := [u32Val 7] } :=
  refutes_wf_of_execFault (fuel := 2) rfl

/-- Program executing `StorageDead 0; StorageLive 0; _0 = 7u8; return` on the
return place `_0` (accepted if `StorageDead 0` is not refused). -/
noncomputable def progStorageDeadRet : Program :=
  mkSingleBlockProg 0 [u8Ty]
    [.storageDead 0, .storageLive 0,
     .assign ⟨0, []⟩ (.use (.constant ⟨u8Ty, .scalar (BitVec.ofNat 128 7)⟩))]
    .return_

/-- Guard `step_storage_dead_return_place`: `StorageDead 0` faults with
`.unsupported` even when followed by `StorageLive 0` and initialization. -/
theorem refute_step_storage_dead_return_place :
    ReachesResult progStorageDeadRet queryEmpty (.fault .unsupported) ∧
    ¬ WellFormed progStorageDeadRet queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Program writing to a projected destination place `_0.0`. -/
noncomputable def progAssignDstProjected : Program :=
  mkSingleBlockProg 1 [u32Ty, u32Ty]
    [.assign ⟨0, [.field 0 u32Ty]⟩ (.use (.copy ⟨1, []⟩))]

/-- Guard `step_assign_reject_dst_projection`: `evalStatement .assign` rejects
a non-empty destination projection with `.unsupported`. -/
theorem refute_step_assign_reject_dst_projection :
    ReachesResult progAssignDstProjected { args := [u32Val 7] }
      (.fault .unsupported) ∧
    ¬ WellFormed progAssignDstProjected { args := [u32Val 7] } :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Program executing `StatementKind.unsupported`. -/
noncomputable def progUnsupportedStmt : Program :=
  mkSingleBlockProg 0 [.unit] [.unsupported] .return_

/-- Guard `step_statement_unsupported_faults`: `StatementKind.unsupported`
faults with `.unsupported`. -/
theorem refute_step_statement_unsupported_faults :
    ReachesResult progUnsupportedStmt queryEmpty (.fault .unsupported) ∧
    ¬ WellFormed progUnsupportedStmt queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Program executing `switchInt` on `u8` with an overflowing case `256`. -/
noncomputable def progSwitchIntOverflow : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [.unit, u8Ty]
    basicBlocks := [
      { statements := []
        terminator := .switchInt (.copy ⟨1, []⟩)
          ⟨[(BitVec.ofNat 128 256, 1)], 1⟩ },
      { statements := []
        terminator := .return_ }
    ]
  }]

/-- Guard `step_switch_int_case_overflow`: `evalSwitchBranches` rejects a `u8`
case value `256` overflowing 8 bits with `.unsupported`. -/
theorem refute_step_switch_int_case_overflow :
    ReachesResult progSwitchIntOverflow { args := [u8Val 0] }
      (.fault .unsupported) ∧
    ¬ WellFormed progSwitchIntOverflow { args := [u8Val 0] } :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Program executing `switchInt` on `bool` with invalid case `2`. -/
noncomputable def progSwitchBoolInvalidCase : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [.unit, .bool]
    basicBlocks := [
      { statements := []
        terminator := .switchInt (.copy ⟨1, []⟩)
          ⟨[(BitVec.ofNat 128 2, 1)], 1⟩ },
      { statements := []
        terminator := .return_ }
    ]
  }]

/-- Guard `step_switch_bool_invalid_case`: `evalBoolSwitchBranches` propagates
invalid bool case `2` as `.fault .undefined` rather than falling through. -/
theorem refute_step_switch_bool_invalid_case :
    ReachesResult progSwitchBoolInvalidCase { args := [.bool false] }
      (.fault .undefined) ∧
    ¬ WellFormed progSwitchBoolInvalidCase { args := [.bool false] } :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Program executing `switchInt` on `char` with surrogate case `0xD800`. -/
noncomputable def progSwitchCharInvalidCase : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [.unit, .char]
    basicBlocks := [
      { statements := []
        terminator := .switchInt (.copy ⟨1, []⟩)
          ⟨[(BitVec.ofNat 128 0xd800, 1)], 1⟩ },
      { statements := []
        terminator := .return_ }
    ]
  }]

/-- Guard `step_switch_char_invalid_case`: `evalCharSwitchBranches` propagates
surrogate char case `0xD800` as `.fault .undefined` rather than falling
through. -/
theorem refute_step_switch_char_invalid_case :
    ReachesResult progSwitchCharInvalidCase { args := [.char 'a'] }
      (.fault .undefined) ∧
    ¬ WellFormed progSwitchCharInvalidCase { args := [.char 'a'] } :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Program whose `bb0` is a cleanup unwind block (`cleanup := true`) with a
`TerminatorKind.return_` terminator. -/
noncomputable def progReturnInCleanupBlock : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 0
    locals := [.unit]
    basicBlocks := [{ statements := [], terminator := .return_, cleanup := true }]
  }]

/-- Guard `step_return_in_cleanup_block`: returning from a `cleanup := true`
basic block faults with `.unsupported`. -/
theorem refute_step_return_in_cleanup_block :
    ReachesResult progReturnInCleanupBlock queryEmpty (.fault .unsupported) ∧
    ¬ WellFormed progReturnInCleanupBlock queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Program executing `switchInt` on an overflow pair `(u32, bool)` with a
non-empty branch list. -/
noncomputable def progSwitchOverflowPairBranches : Program where
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 1
  bodies := [{
    argumentCount := 1
    locals := [.unit, .tuple [u32Ty, .bool]]
    basicBlocks := [
      { statements := []
        terminator := .switchInt (.copy ⟨1, []⟩)
          ⟨[(BitVec.ofNat 128 0, 1)], 1⟩ },
      { statements := []
        terminator := .return_ }
    ]
  }]

/-- Guard `step_switch_overflow_pair_nonempty_branches`: `switchInt` on an
overflow pair with non-empty branches faults with `.unsupported`. -/
theorem refute_step_switch_overflow_pair_nonempty_branches :
    ReachesResult progSwitchOverflowPairBranches
      { args := [.tuple [u32Val 0, .bool false]] } (.fault .unsupported) ∧
    ¬ WellFormed progSwitchOverflowPairBranches
      { args := [.tuple [u32Val 0, .bool false]] } :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `step_unsupported_terminators_fault`: `.unwindResume`, `.coreCall`,
`.call`, and `.unsupported` terminators all fault with `.unsupported`. -/
theorem refute_step_unsupported_terminators_fault :
    (ReachesResult (mkSingleBlockProg 0 [.unit] [] .unwindResume) queryEmpty
      (.fault .unsupported) ∧
     ¬ WellFormed (mkSingleBlockProg 0 [.unit] [] .unwindResume) queryEmpty) ∧
    (ReachesResult
      (mkSingleBlockProg 0 [.unit] []
        (.coreCall .sliceLen [] ⟨0, []⟩ none .continue_))
      queryEmpty (.fault .unsupported) ∧
     ¬ WellFormed
      (mkSingleBlockProg 0 [.unit] []
        (.coreCall .sliceLen [] ⟨0, []⟩ none .continue_))
      queryEmpty) ∧
    (ReachesResult
      (mkSingleBlockProg 0 [.unit] [] (.call 0 [] ⟨0, []⟩ none .continue_))
      queryEmpty (.fault .unsupported) ∧
     ¬ WellFormed
      (mkSingleBlockProg 0 [.unit] [] (.call 0 [] ⟨0, []⟩ none .continue_))
      queryEmpty) ∧
    (ReachesResult (mkSingleBlockProg 0 [.unit] [] .unsupported) queryEmpty
      (.fault .unsupported) ∧
     ¬ WellFormed (mkSingleBlockProg 0 [.unit] [] .unsupported) queryEmpty) :=
  ⟨refutes_wf_of_execFault (fuel := 1) rfl,
   refutes_wf_of_execFault (fuel := 1) rfl,
   refutes_wf_of_execFault (fuel := 1) rfl,
   refutes_wf_of_execFault (fuel := 1) rfl⟩

/-- Program whose `bb0` jumps to an out-of-bounds basic block index `99`. -/
noncomputable def progGotoOobBlock : Program :=
  mkSingleBlockProg 0 [.unit] [] (.goto 99)

/-- Guard `step_oob_block_idx_faults`: `evalStep` faults with `.unsupported`
when `frame.blockIdx` is out of bounds. -/
theorem refute_step_oob_block_idx_faults :
    ReachesResult progGotoOobBlock queryEmpty (.fault .unsupported) ∧
    ¬ WellFormed progGotoOobBlock queryEmpty :=
  refutes_wf_of_execFault (fuel := 2) rfl

/-- Program reading an out-of-bounds local `_7` via `Operand.copy`. -/
noncomputable def progOperandCopyOob : Program :=
  mkSingleBlockProg 0 [.unit] [.assign ⟨0, []⟩ (.use (.copy ⟨7, []⟩))]

/-- Guard `step_operand_copy_oob_local`: `evalOperandToSlot` `.copy` catch-all
rejects an out-of-bounds local index with `.unsupported`. -/
theorem refute_step_operand_copy_oob_local :
    ReachesResult progOperandCopyOob queryEmpty (.fault .unsupported) ∧
    ¬ WellFormed progOperandCopyOob queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Program reading an out-of-bounds local `_7` via `Operand.move`. -/
noncomputable def progOperandMoveOob : Program :=
  mkSingleBlockProg 0 [.unit] [.assign ⟨0, []⟩ (.use (.move ⟨7, []⟩))]

/-- Guard `step_operand_move_oob_local`: `evalOperandToSlot` `.move` catch-all
rejects an out-of-bounds local index with `.unsupported`. -/
theorem refute_step_operand_move_oob_local :
    ReachesResult progOperandMoveOob queryEmpty (.fault .unsupported) ∧
    ¬ WellFormed progOperandMoveOob queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Program computing `Rvalue.discriminant` on a non-enum `u32` local `_1`. -/
noncomputable def progDiscrNonEnumSrc : Program :=
  mkSingleBlockProg 1 [u8Ty, u32Ty] [.assign ⟨0, []⟩ (.discriminant ⟨1, []⟩)]

/-- Guard `step_discriminant_non_enum_src`: `evalRvalue .discriminant` rejects
non-enum, non-`Ordering` source locals (`u32`) with `.unsupported`. -/
theorem refute_step_discriminant_non_enum_src :
    ReachesResult progDiscrNonEnumSrc { args := [u32Val 5] }
      (.fault .unsupported) ∧
    ¬ WellFormed progDiscrNonEnumSrc { args := [u32Val 5] } :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Guard `step_rvalue_catchall_unsupported`: `evalRvalue` catch-all rejects
unmodeled `.ref`, `.addressOf`, `.cast .unsupported`, and `.unsupported`
rvalues with `.unsupported`. -/
theorem refute_step_rvalue_catchall_unsupported :
    (ReachesResult
      (mkSingleBlockProg 0 [.unit] [.assign ⟨0, []⟩ (.ref .shared ⟨0, []⟩)])
      queryEmpty (.fault .unsupported) ∧
     ¬ WellFormed
      (mkSingleBlockProg 0 [.unit] [.assign ⟨0, []⟩ (.ref .shared ⟨0, []⟩)])
      queryEmpty) ∧
    (ReachesResult
      (mkSingleBlockProg 0 [.unit] [.assign ⟨0, []⟩ (.addressOf .mut ⟨0, []⟩)])
      queryEmpty (.fault .unsupported) ∧
     ¬ WellFormed
      (mkSingleBlockProg 0 [.unit] [.assign ⟨0, []⟩ (.addressOf .mut ⟨0, []⟩)])
      queryEmpty) ∧
    (ReachesResult
      (mkSingleBlockProg 0 [.unit]
        [.assign ⟨0, []⟩
          (.cast .unsupported
            (.constant ⟨u8Ty, .scalar (BitVec.ofNat 128 1)⟩) .unit)])
      queryEmpty (.fault .unsupported) ∧
     ¬ WellFormed
      (mkSingleBlockProg 0 [.unit]
        [.assign ⟨0, []⟩
          (.cast .unsupported
            (.constant ⟨u8Ty, .scalar (BitVec.ofNat 128 1)⟩) .unit)])
      queryEmpty) ∧
    (ReachesResult
      (mkSingleBlockProg 0 [.unit] [.assign ⟨0, []⟩ .unsupported])
      queryEmpty (.fault .unsupported) ∧
     ¬ WellFormed
      (mkSingleBlockProg 0 [.unit] [.assign ⟨0, []⟩ .unsupported])
      queryEmpty) :=
  ⟨refutes_wf_of_execFault (fuel := 1) rfl,
   refutes_wf_of_execFault (fuel := 1) rfl,
   refutes_wf_of_execFault (fuel := 1) rfl,
   refutes_wf_of_execFault (fuel := 1) rfl⟩

/-- Program assigning to an out-of-bounds destination local `_9`. -/
noncomputable def progAssignOobDst : Program :=
  mkSingleBlockProg 0 [.unit]
    [.assign ⟨9, []⟩ (.use (.constant ⟨u8Ty, .scalar (BitVec.ofNat 128 1)⟩))]

/-- Guard `step_assign_oob_dst`: `evalStatement .assign` rejects an
out-of-bounds `dst.localId` (`none`) with `.unsupported`. -/
theorem refute_step_assign_oob_dst :
    ReachesResult progAssignOobDst queryEmpty (.fault .unsupported) ∧
    ¬ WellFormed progAssignOobDst queryEmpty :=
  refutes_wf_of_execFault (fuel := 1) rfl

/-- Profile v2 program whose callee returns a reference to its own stack
local `_1`, which the caller then holds. -/
noncomputable def progReturnToCallerDanglingV2 : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 2
  bodies := [{
    argumentCount := 0
    locals := [.int .i8 false, .ref .shared (.int .i8 false)]
    basicBlocks := [
      { statements := []
        terminator := .call 1 [] { localId := 1, projection := [] } (some 1)
          .continue_ },
      { statements := []
        terminator := .return_ }]
    identity := "guard_mutation::return_to_caller_dangling_main"
  }, {
    argumentCount := 0
    locals := [.ref .shared (.int .i8 false), .int .i8 false]
    basicBlocks := [{
      statements := [
        .assign { localId := 1, projection := [] }
          (.use (.constant ⟨.int .i8 false, .scalar (BitVec.ofNat 128 9)⟩)),
        .assign { localId := 0, projection := [] }
          (.ref .shared { localId := 1, projection := [] })
      ]
      terminator := .return_
    }]
    identity := "guard_mutation::return_to_caller_dangling_callee"
  }]
}

/-- Guard `step_v2_return_to_caller_dangling`: returning from a callee frame
a reference to one of its own (deallocated) stack locals faults with
`.undefined` at the return step. -/
theorem refute_step_v2_return_to_caller_dangling :
    (match initStateV2 progReturnToCallerDanglingV2 { args := [] } with
     | .ok s₀ =>
       match evalStepV2 progReturnToCallerDanglingV2 s₀ with
       | .step s₁ =>
         match evalStepV2 progReturnToCallerDanglingV2 s₁ with
         | .step s₂ =>
           match evalStepV2 progReturnToCallerDanglingV2 s₂ with
           | .step s₃ =>
             match evalStepV2 progReturnToCallerDanglingV2 s₃ with
             | .fault .undefined => True
             | _ => False
           | _ => False
         | _ => False
       | _ => False
     | .error _ => False) :=
  trivial

/-- Profile v2 program calling `callee(&u8)`; the caller frame state is built
directly with a reference argument into a deallocated allocation. -/
noncomputable def progCallArgInvalidRefV2 : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 2
  bodies := [{
    argumentCount := 1
    locals := [.int .i8 false, .ref .shared (.int .i8 false)]
    basicBlocks := [
      { statements := []
        terminator := .call 1 [.copy { localId := 1, projection := [] }]
          { localId := 0, projection := [] } (some 1) .continue_ },
      { statements := []
        terminator := .return_ }]
    identity := "guard_mutation::call_arg_invalid_ref_main"
  }, {
    argumentCount := 1
    locals := [.int .i8 false, .ref .shared (.int .i8 false)]
    basicBlocks := [{
      statements := [
        .assign { localId := 0, projection := [] }
          (.use (.copy { localId := 1, projection := [.deref] }))
      ]
      terminator := .return_
    }]
    identity := "guard_mutation::call_arg_invalid_ref_callee"
  }]
}

/-- Memory holding only the deallocated allocation `1`. -/
noncomputable def memDeadAlloc1 : MemoryState :=
  { allocations := [{
      allocId := 1
      alignLog2 := 0
      mutability := .shared
      bytes := [.init 7 none]
      live := false
    }], nextAllocId := 2 }

/-- Guard `step_v2_call_arg_invalid_ref`: an intra-crate call whose reference
argument points into a deallocated allocation faults with `.undefined`
before the callee frame is pushed. -/
theorem refute_step_v2_call_arg_invalid_ref :
    (match evalStepV2 progCallArgInvalidRefV2 {
        frames := [{
          defId := 0
          blockIdx := 0
          stmtIdx := 0
          locals := [.immediate none,
            .immediate (some (.ptr ⟨some 1, 0, .isize⟩))]
        }]
        mem := memDeadAlloc1
      } with
     | .fault .undefined => True
     | _ => False) :=
  trivial

/-- Profile v2 program whose caller calls `callee() -> _1` with the
destination `_1` dead (`initStateV2` is bypassed by building the frame
directly), or `callee(move _1) -> _1` in block 1. -/
noncomputable def progCallDestinationV2 : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 2
  bodies := [{
    argumentCount := 0
    locals := [.int .i8 false, .int .i8 false]
    basicBlocks := [
      { statements := []
        terminator := .call 1 [] { localId := 1, projection := [] } (some 2)
          .continue_ },
      { statements := []
        terminator := .call 2 [.move { localId := 1, projection := [] }]
          { localId := 1, projection := [] } (some 2) .continue_ },
      { statements := []
        terminator := .return_ }]
    identity := "guard_mutation::call_destination_main"
  }, {
    argumentCount := 0
    locals := [.int .i8 false]
    basicBlocks := [{ statements := [], terminator := .return_ }]
    identity := "guard_mutation::call_destination_callee"
  }, {
    argumentCount := 1
    locals := [.int .i8 false, .int .i8 false]
    basicBlocks := [{ statements := [], terminator := .return_ }]
    identity := "guard_mutation::call_destination_callee_arg"
  }]
}

/-- Guard `step_v2_call_dead_destination`: a call whose unprojected
destination local is dead faults with `.undefined` before the callee frame is
pushed, even though the callee could diverge. -/
theorem refute_step_v2_call_dead_destination :
    (match evalStepV2 progCallDestinationV2 {
        frames := [{
          defId := 0
          blockIdx := 0
          stmtIdx := 0
          locals := [.immediate none, .dead]
        }]
        mem := emptyMemory
      } with
     | .fault .undefined => True
     | _ => False) :=
  trivial

/-- Guard `step_v2_call_moves_disjoint`: a call whose destination is also a
`move` argument (`callee(move _1) -> _1`) is not definitely disjoint and
faults with `.unsupported`. -/
theorem refute_step_v2_call_moves_disjoint :
    (match evalStepV2 progCallDestinationV2 {
        frames := [{
          defId := 0
          blockIdx := 1
          stmtIdx := 0
          locals := [.immediate none,
            .immediate (some (.scalar ⟨.i8, false, BitVec.ofNat 128 3⟩))]
        }]
        mem := emptyMemory
      } with
     | .fault .unsupported => True
     | _ => False) :=
  trivial

/-- Profile v2 program whose safe caller calls an `unsafe` callee. -/
noncomputable def progCallUnsafeCalleeV2 : Program := {
  scope := .unit
  pointerWidthBits := 64
  mirProfileVersion := 2
  bodies := [{
    argumentCount := 0
    locals := [.int .i8 false]
    basicBlocks := [
      { statements := []
        terminator := .call 1 [] { localId := 0, projection := [] } (some 1)
          .continue_ },
      { statements := []
        terminator := .return_ }]
    identity := "guard_mutation::call_unsafe_callee_main"
  }, {
    argumentCount := 0
    locals := [.int .i8 false]
    basicBlocks := [{ statements := [], terminator := .return_ }]
    isUnsafe := true
    identity := "guard_mutation::call_unsafe_callee"
  }]
}

/-- Guard `step_v2_call_unsafe_callee`: an intra-crate call to an `unsafe`
callee, whose safety precondition Profile v2 does not check at the call site,
faults with `.unsupported` instead of pushing the callee frame. -/
theorem refute_step_v2_call_unsafe_callee :
    (match evalStepV2 progCallUnsafeCalleeV2 {
        frames := [{
          defId := 0
          blockIdx := 0
          stmtIdx := 0
          locals := [.immediate none]
        }]
        mem := emptyMemory
      } with
     | .fault .unsupported => True
     | _ => False) :=
  trivial

end GuardMutation
