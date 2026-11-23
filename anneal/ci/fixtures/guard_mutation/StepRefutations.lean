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

end GuardMutation
