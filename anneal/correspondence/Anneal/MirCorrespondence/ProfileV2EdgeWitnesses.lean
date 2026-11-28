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
import Anneal.MirCorrespondence.ByteCodec
import Anneal.MirCorrespondence.LayoutAndAlign
import Anneal.MirCorrespondence.MiriMemoryBridge
import Anneal.MirCorrespondence.ProfileV2RefMachine
import Anneal.MirCorrespondence.ProfileV2Correspondence
import Anneal.MirCorrespondence.ProfileV2Witnesses
import Anneal.MirCorrespondence.ScalarEquiv
import Anneal.MirCorrespondence.SimHelpers

namespace Anneal.MirCorrespondence

open Trusted Trusted.MirAst Trusted.MirSemantics Trusted.Correspondence

/-!
# Profile v2 Conservative-Edge Separation Witnesses
(`Anneal.MirCorrespondence.ProfileV2EdgeWitnesses`)

Companion module to `Anneal.MirCorrespondence.ProfileV2Witnesses` proving the
three concrete conservative-edge separation witnesses between Profile v2
`evalStepV2` and `ProfileV2RefMachine`:
1. `conservative_edge1_zero_offset_oob_separation`: zero-offset `BinOp.offset`
   on an out-of-bounds provenance pointer.
2. `conservative_edge2_null_zst_deref_separation`: provenance-less null ZST
   dereference `*(0 as *const ())`.
3. `conservative_edge3_const_to_mut_cast_separation`: const-to-mut raw-pointer
   cast `*const u32 as *mut u32`.
4. `not_biFaultEquivV2_encodeProg`: global impossibility of
   `BiFaultEquivV2Bundle encodeProg` (witnessed by Edge 1).
-/

/-! ## Section 1: Conservative-Edge Witness Programs and Queries -/

/-- Conservative Edge 1 program: `_0 = BinOp.offset(copy _1, 0isize); return`
on `_1 : *const u8`. -/
noncomputable def progV2Edge1ZeroOffsetOob : Program :=
  mkV2Prog {
    identity := "v2_edge1_zero_offset_oob"
    argumentCount := 1
    locals := [.rawPtr .shared u8Ty, .rawPtr .shared u8Ty]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩
          (.binaryOp .offset (.copy ⟨1, []⟩)
            (.constant ⟨.int .isize true, .scalar (BitVec.ofNat 128 0)⟩))
      ]
      terminator := .return_
    }]
  }

/-- 4-byte shared caller allocation at `allocId = 2`. -/
noncomputable def callerMemEdge1 : CallerMemory := ⟨[{
  allocId := 2, alignLog2 := 0, mutability := .shared
  bytes := [.init 7 none, .init 8 none, .init 9 none, .init 10 none]
  live := true
}]⟩

/-- Query passing an out-of-bounds provenance pointer (`offset = 8 > 4`) into
`callerMemEdge1`. -/
noncomputable def queryV2Edge1ZeroOffsetOob : Query := {
  args := [.ptr ⟨some 2, 8, .isize⟩]
  callerMem := callerMemEdge1
}

/-- Conservative Edge 2 program: `_0 = copy (*_1); return` on `_1 : *const ()`.
-/
noncomputable def progV2Edge2NullZstDeref : Program :=
  mkV2Prog {
    identity := "v2_edge2_null_zst_deref"
    argumentCount := 1
    locals := [.unit, .rawPtr .shared .unit]
    basicBlocks := [{
      statements := [.assign ⟨0, []⟩ (.use (.copy ⟨1, [.deref]⟩))]
      terminator := .return_
    }]
  }

/-- Query passing a provenance-less null pointer `(0 as *const ())`. -/
noncomputable def queryV2Edge2NullZstDeref : Query := {
  args := [.ptr ⟨none, 0, .isize⟩]
  callerMem := ⟨[]⟩
}

/-- Conservative Edge 3 program: `_0 = copy _1 as *mut u32; return` on
`_1 : *const u32`. -/
noncomputable def progV2Edge3ConstToMutCast : Program :=
  mkV2Prog {
    identity := "v2_edge3_const_to_mut_cast"
    argumentCount := 1
    locals := [.rawPtr .mut u32Ty, .rawPtr .shared u32Ty]
    basicBlocks := [{
      statements := [
        .assign ⟨0, []⟩ (.cast .ptrToPtr (.copy ⟨1, []⟩) (.rawPtr .mut u32Ty))
      ]
      terminator := .return_
    }]
  }

/-- 4-byte aligned shared caller allocation at `allocId = 2`. -/
noncomputable def callerMemEdge3 : CallerMemory := ⟨[{
  allocId := 2, alignLog2 := 2, mutability := .shared
  bytes := [.init 1 none, .init 2 none, .init 3 none, .init 4 none]
  live := true
}]⟩

/-- Query passing `*const u32` into `callerMemEdge3`. -/
noncomputable def queryV2Edge3ConstToMutCast : Query := {
  args := [.ptr ⟨some 2, 0, .isize⟩]
  callerMem := callerMemEdge3
}

/-! ## Section 2: Edge 2 Stack Deallocation & All 3 Separation Witnesses -/

theorem deallocateStack_ret_alloc2_v2
    (a1 : Miri.Memory.LocalAllocation Miri.Memory.Provenance
      Miri.TreeBorrows.BorrowTree Unit)
    (alc : RefMiriAlloc) (st : RefMiriState)
    (h_live : st.machine.memory.live =
      Array.mk [(retAllocIdV2, a1), (alloc2IdV2, ⟨.stack, alc⟩)])
    (h_dead : st.machine.memory.dead = Array.empty)
    (h_mut : alc.mutability = .Mut) :
    refDeallocateStackV2
        ⟨Miri.ABI.Size.ZERO,
          some (.concrete alloc2IdV2 Miri.Memory.BorTag.one)⟩ st =
      .ok () { st with
        machine := { st.machine with
          memory := { st.machine.memory with
            live := Array.mk [(retAllocIdV2, a1)]
            dead := Array.mk [⟨alloc2IdV2, alc.byteSize, alc.align⟩] } } } := by
  cases st with
  | mk sk mc =>
    cases mc with
    | mk mem bt dr th ra sp u pmd =>
      cases mem with
      | mk nai idex it lv dd gt igt igr fn va bk bkr sw sn se sbr rbs os sb =>
        dsimp only at h_live h_dead
        subst h_live h_dead
        let m0 : RefMiriMem :=
          { nextAllocId := nai, idSupplyExhausted := idex, issuedIdTable := it,
            live := Array.mk [(retAllocIdV2, a1), (alloc2IdV2, ⟨.stack, alc⟩)],
            dead := Array.empty, globalTable := gt, importedGlobalTable := igt,
            importedGlobalRuntimeTable := igr, extraFnPtrTable := fn,
            vaListTable := va, byteGlobalKeys := bk, byteGlobalKeysReady := bkr,
            sourceAllocIdWorldActive := sw, sourceAllocIdNext := sn,
            sourceAllocIdExhausted := se, sourceAllocIdByRuntimeTable := sbr,
            runtimeBySourceAllocIdTable := rbs, opaqueSourceGlobalIds := os,
            sourceByteImageFamilyComplete := sb }
        let m1 : RefMiriMem :=
          { m0 with live := (m0.live.filter fun old => old.1 != alloc2IdV2) }
        have h_mut_f :
            (alc.mutability == Miri.Memory.Mutability.Not) = false := by
          rw [h_mut]; rfl
        have h_m1 : m1 = { m0 with live := Array.mk [(retAllocIdV2, a1)] } := by
          dsimp only [m1, m0]
          rw [show (Array.mk [(retAllocIdV2, a1), (alloc2IdV2, ⟨.stack, alc⟩)] :
            Array (Miri.Memory.AllocId × Miri.Memory.LocalAllocation
              Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree Unit)).filter
              (fun old => old.1 != alloc2IdV2) =
              Array.mk [(retAllocIdV2, a1)] from rfl]
        have h_fnd :
            (m0.live.find? fun e => e.1 == alloc2IdV2).map Prod.snd =
              some ⟨.stack, alc⟩ := by
          dsimp only [m0]
          rw [show (Array.mk [(retAllocIdV2, a1), (alloc2IdV2, ⟨.stack, alc⟩)] :
            Array (Miri.Memory.AllocId × Miri.Memory.LocalAllocation
              Miri.Memory.Provenance Miri.TreeBorrows.BorrowTree Unit)).find?
              (fun e => e.1 == alloc2IdV2) =
              some (alloc2IdV2, ⟨.stack, alc⟩) from rfl]
          rfl
        have h_da :
            ((Array.empty : Array Miri.Memory.DeadAllocation).any fun old =>
              old.allocId == alloc2IdV2) = false := by
          rw [← Array.any_toList]; rfl
        have h_dealloc :
            Miri.Memory.MemoryLifecycle.deallocatePtrWith m0 ()
                ⟨Miri.ABI.Size.ZERO,
                  some (.concrete alloc2IdV2 Miri.Memory.BorTag.one)⟩
                none .stack ({
                  synchronizeMemory := fun _ _ => ()
                  resolvePointer := fun mem _ p sz =>
                    match refResolvePointerPure p sz with
                    | .ok r => ⟨mem, (), .ok (r.allocId, r.offset, r.extra)⟩
                    | .error addr => ⟨mem, (), .error addr⟩
                  beforeDeallocation := fun mem _ _ _ _ _ _ _ _ =>
                    ⟨mem, (), .ok ()⟩ } :
                  Miri.Memory.MemoryDeallocationHooks Miri.Memory.Provenance
                    Miri.TreeBorrows.BorrowTree Unit Unit
                    Miri.Memory.ProvenanceExtra) =
              ⟨{ m0 with
                  live := Array.mk [(retAllocIdV2, a1)],
                  dead := Array.mk [⟨alloc2IdV2, alc.byteSize, alc.align⟩] },
                (), some (alloc2IdV2, ⟨.stack, alc⟩), .ok ()⟩ := by
          dsimp only [Miri.Memory.MemoryLifecycle.deallocatePtrWith,
            refResolvePointerPure, Miri.ABI.Size.ZERO, Id.run,
            bind, Bind.bind, pure, Pure.pure]
          change ((match ((m0.live.find? fun e => e.1 == alloc2IdV2).map
                Prod.snd) with
            | none =>
              match m0.findGlobal? alloc2IdV2 with
              | some g =>
                ⟨m0, (), none,
                  .error (.globalAllocationDeallocation alloc2IdV2 g.kind)⟩
              | none => ⟨m0, (), none, .error (.useAfterFree alloc2IdV2)⟩
            | some entry =>
              if (entry.allocation.mutability == Miri.Memory.Mutability.Not) =
                  true then
                ⟨m1, (), some (alloc2IdV2, entry),
                  .error (.immutableAllocation alloc2IdV2)⟩
              else
                if entry.kind ≠ Miri.Memory.MemoryKind.stack then
                  ⟨m1, (), some (alloc2IdV2, entry),
                    .error (.memoryKindMismatch alloc2IdV2)⟩
                else
                  let de : Miri.Memory.DeadAllocation :=
                    ⟨alloc2IdV2, entry.allocation.byteSize,
                      entry.allocation.align⟩
                  let ad := m1.dead.any fun old => old.allocId == alloc2IdV2
                  let aft :=
                    { m1 with
                      dead :=
                        (m1.dead.filter fun old => old.allocId != de.allocId).push
                          de }
                  if ad = true then
                    ⟨aft, (), some (alloc2IdV2, entry),
                      .error (.duplicateDeadAllocation alloc2IdV2)⟩
                  else
                    ⟨aft, (), some (alloc2IdV2, entry), .ok ()⟩) :
              Miri.Memory.MemoryDeallocationResult Miri.Memory.Provenance
                Miri.TreeBorrows.BorrowTree Unit Unit) = _
          rw [h_fnd]
          dsimp only
          rw [h_mut_f]
          simp only [Bool.false_eq_true, ite_false]
          rw [ite_not_eq_false _ _ (fun h => h rfl), h_m1]
          dsimp only
          rw [show ({ m0 with live := Array.mk [(retAllocIdV2, a1)] } :
              RefMiriMem).dead =
                (Array.empty : Array Miri.Memory.DeadAllocation)
            from rfl, h_da]
          simp only [Bool.false_eq_true, ite_false]
          rfl
        have h_wrap :
            ∀ r : Miri.Memory.MemoryDeallocationResult Miri.Memory.Provenance
              Miri.TreeBorrows.BorrowTree Unit Unit,
            r = ⟨{ m0 with
                live := Array.mk [(retAllocIdV2, a1)],
                dead := Array.mk [⟨alloc2IdV2, alc.byteSize, alc.align⟩] },
              (), some (alloc2IdV2, ⟨.stack, alc⟩), .ok ()⟩ →
            (let st1 : RefMiriState := ⟨sk, ⟨r.memory, bt, dr, th, ra, sp, u, pmd⟩⟩
             match r.outcome with
             | .ok () => EStateM.Result.ok () st1
             | .error e => EStateM.Result.error (refLifecycleErrToStepErr e) st1) =
            EStateM.Result.ok () ⟨sk, ⟨{ m0 with
                live := Array.mk [(retAllocIdV2, a1)],
                dead := Array.mk [⟨alloc2IdV2, alc.byteSize, alc.align⟩] },
              bt, dr, th, ra, sp, u, pmd⟩⟩ := by
          intro r hr; rw [hr]
        exact h_wrap _ h_dealloc

/-- Conservative Edge 1 separation witness: zero-offset `BinOp.offset(p, 0)` on
an out-of-bounds provenance pointer faults with `.undefined` in `evalStepV2`,
while `ProfileV2RefMachine` is `RefWellFormedV2` and returns the pointer
without `.ub` (matching Miri's zero-offset rule). -/
theorem conservative_edge1_zero_offset_oob_separation :
    ReachesResultV2 progV2Edge1ZeroOffsetOob queryV2Edge1ZeroOffsetOob
      (.fault .undefined) ∧
    ¬ WellFormedV2 progV2Edge1ZeroOffsetOob queryV2Edge1ZeroOffsetOob ∧
    RefWellFormedV2 (encodeProg progV2Edge1ZeroOffsetOob)
      queryV2Edge1ZeroOffsetOob ∧
    RefBehaviorV2 (encodeProg progV2Edge1ZeroOffsetOob)
      queryV2Edge1ZeroOffsetOob
      (.returned ⟨.ptr ⟨some 2, 8, .isize⟩, callerMemEdge1⟩) ∧
    (∀ ms, ¬ RefReachesOutcomeV2 (encodeProg progV2Edge1ZeroOffsetOob)
      queryV2Edge1ZeroOffsetOob ms .ub) := by
  let ⟨h_f1, _, _, _, h_nwf1⟩ :=
    fault_and_exclusive_of_execFaultV2 (p := progV2Edge1ZeroOffsetOob)
      (q := queryV2Edge1ZeroOffsetOob) (fuel := 2) (expected := .undefined) rfl
  refine ⟨h_f1, h_nwf1, ?_⟩
  let rp := encodeProg progV2Edge1ZeroOffsetOob
  let alloc2 := @GetElem.getElem _ Nat _ _ _ callerMemEdge1.allocations 0
    (by decide)
  let raw : List UInt8 := [7, 8, 9, 10]
  let ⟨ma2, rawRet, h_rel, h_raw, h_icm, _⟩ :=
    refInit_1alloc_thinPtr_2local_v2 rp.types .shared .shared u8Ty u8Ty
      alloc2 raw 8 rfl rfl (by decide) rfl (by decide) rfl
  let mem0 : RefMiriMem :=
    ({ (Miri.Memory.MemoryState.empty : RefMiriMem) with
        nextAllocId := 3
        live := Array.mk [(alloc2IdV2, ⟨.machine (), ma2⟩),
          (retAllocIdV2, ⟨.stack, rawRet.withExtra
            (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
              (Miri.ABI.Size.ofBytes 8))⟩)] }
      ).setIssuedIds (Array.mk [alloc2IdV2, retAllocIdV2])
  let retLay := refLocalLayoutForTyV2 rp.types (.rawPtr .shared u8Ty)
  let retPlace : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance :=
    ⟨retMemPlaceV2, retLay⟩
  let ptr : Miri.Memory.Pointer Miri.Memory.Provenance :=
    ⟨Miri.ABI.Size.ofBytes 8, .concrete alloc2IdV2 Miri.Memory.BorTag.one⟩
  let ptrImm : Miri.Interpreter.Immediate Miri.Memory.Provenance :=
    .scalar (.fromPointer refRuntimeLayoutV2.base ptr)
  let rbody := @GetElem.getElem _ Nat _ _ _ rp.bodies 0 (by decide)
  let frame0 := mkRefMiriFrameV2 rp.types 0 rbody 0 0
    [⟨.live (.immediate .uninit), some retLay⟩,
     ⟨.live (.immediate ptrImm), some retLay⟩]
    retPlace
  let m0 := mkRefMiriState frame0 mem0 refInitControl callerMemEdge1
  have h_init : ∀ ms : Nat, initRefStateV2 rp queryV2Edge1ZeroOffsetOob ms =
      .ok { miri := m0, retTy := .rawPtr .shared u8Ty, retPlace := retPlace,
            stepsExecuted := 0, maxSteps := ms } := by
    intro ms
    exact initRefStateV2_ok_v2 rp queryV2Edge1ZeroOffsetOob ms rbody
      [.rawPtr .shared u8Ty, .rawPtr .shared u8Ty] (.rawPtr .shared u8Ty)
      mem0 mem0 retPlace
      [⟨.live (.immediate .uninit), some retLay⟩,
       ⟨.live (.immediate ptrImm), some retLay⟩]
      rfl rfl rfl rfl rfl rfl rfl rfl h_icm rfl rfl rfl
  let frame1 : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra :=
    { frame0 with
      locals := (Array.mk
        [⟨.live (.immediate ptrImm), some retLay⟩,
         ⟨.live (.immediate ptrImm), some retLay⟩])
      location := .mir ⟨0, 1⟩ }
  let m1 : RefMiriState := { m0 with stack := ⟨Array.mk [frame1]⟩ }
  have h_step0 : Miri.Interpreter.ExecutionMachine.step
      (refExecutionConfigV2 rp) refLimitsV2 0 m0 = (m1, .ok true) := by
    have h_cf := currentFrame_single_v2 m0 frame0 rfl
    have h_ev := projPlace_evalPlace_local_v2 rp m0 frame0 0 retLay
      (.live (.immediate .uninit)) true rfl rfl rfl
    have h_op1 := evalOperand_local_imm_v2 rp m0 frame0 1 retLay ptrImm
      (some retLay) (Miri.Interpreter.OperandPath.rvalue "left") rfl rfl rfl rfl
    have h_ri1 : Miri.Interpreter.PlaceMachine.readImmediate
        (refAccessConfigV2 rp.types) ⟨.immediate ptrImm, retLay⟩ m0 =
        .ok ⟨ptrImm, retLay⟩ m0 := rfl
    have h_opc : Miri.Interpreter.OperandMachine.evalOperandAt
        (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfgV2 rp)) 0
        (Miri.Interpreter.OperandPath.rvalue "right")
        (.Constant ⟨⟨0⟩, none, .Val (.Scalar (.Int 0 16))
          (canonicalTyId rp.types 2)⟩) none m0 =
        .ok ⟨.immediate (.scalar (.fromScalarInt (miriScalar .isize 0))),
          refLocalLayoutForTyV2 rp.types (.int .isize true)⟩ m0 := by
      dsimp only [Miri.Interpreter.OperandMachine.evalOperandAt,
        Miri.Interpreter.OperandMachine.evalOperand]
      rw [opHooks_constantAt_v2]
      exact refEvalConst_int_v2 rp.types m0 .isize true 0 2
        (miriScalar .isize 0) rfl rfl
    have h_ric : Miri.Interpreter.PlaceMachine.readImmediate
        (refAccessConfigV2 rp.types)
        ⟨.immediate (.scalar (.fromScalarInt (miriScalar .isize 0))),
          refLocalLayoutForTyV2 rp.types (.int .isize true)⟩ m0 =
        .ok ⟨.scalar (.fromScalarInt (miriScalar .isize 0)),
          refLocalLayoutForTyV2 rp.types (.int .isize true)⟩ m0 := rfl
    have h_bin := binOp_offset_zero_u8_v2 rp .shared ptr m0 rfl rfl
    have h_set0 : frame0.setLocalOperand 0 (.immediate ptrImm) =
        .ok { frame0 with locals := (Array.mk
          [⟨.live (.immediate ptrImm), some retLay⟩,
           ⟨.live (.immediate ptrImm), some retLay⟩]) } := rfl
    let frame0W := { frame0 with locals := (Array.mk
      [⟨.live (.immediate ptrImm), some retLay⟩,
       ⟨.live (.immediate ptrImm), some retLay⟩]) }
    have h_val0 := rawPtr_validate_v2 rp.types
      { m0 with stack := ⟨Array.mk [frame0W]⟩ } 0 u8Ty .shared ptr frame0W
      rfl rfl rfl rfl rfl
    have h_wr0 := writeLocalImmediate_direct_v2 rp m0 frame0 0 .uninit ptrImm
      retLay frame0W rfl rfl rfl rfl h_set0 h_val0
    have h_ass : (Miri.Interpreter.ExecutionMachine.stepHooks
        (refExecutionConfigV2 rp) refLimitsV2).assign 0 ⟨0, Array.empty⟩
        (toMiriRvalueV2 rp.types (.binaryOp .offset (.copy ⟨1, []⟩)
          (.constant ⟨tyIdFor rp.types (.int .isize true),
            .scalar (BitVec.ofNat 128 0)⟩))) m0 =
        ({ m0 with stack := ⟨Array.mk [frame0W]⟩ }, .ok ()) := by
      have h_ev_body :
          Miri.Interpreter.evalRvalueIntoPlace
              (Miri.Interpreter.ExecutionMachine.rvalueHooks (refExecCfgV2 rp)
                refLimitsV2) 0
              (toMiriRvalueV2 rp.types (.binaryOp .offset (.copy ⟨1, []⟩)
                (.constant ⟨tyIdFor rp.types (.int .isize true),
                  .scalar (BitVec.ofNat 128 0)⟩))) ⟨0, Array.empty⟩ m0 =
            EStateM.Result.ok () { m0 with stack := ⟨Array.mk [frame0W]⟩ } := by
        dsimp only [Miri.Interpreter.evalRvalueIntoPlace,
          toMiriRvalueV2, toMiriOperandV2, toMiriPlaceV2, toMiriProjElemV2,
          toMiriBinOp, List.map]
        rw [show ({ toList := [] } : Array Miri.MIR.ProjectionElem) =
              Array.empty from rfl,
          show (BitVec.ofNat 128 0).toNat = 0 from rfl,
          show canonicalTyId rp.types (tyIdFor rp.types (.int .isize true)) =
            canonicalTyId rp.types 2 from rfl,
          show Miri.MIR.BinOp.Offset.leftHomogeneous = true from rfl,
          show Miri.MIR.BinOp.Offset.rightHomogeneous = false from rfl]
        refine mh_apply_bind _ _ _ _ _ h_ev ?_
        dsimp only [Miri.Interpreter.ExecutionMachine.rvalueHooks,
          Miri.Interpreter.RuntimePlace.layout,
          ite_true_eq, ite_false_eq]
        rw [refStepCfgV2_eq]
        refine mh_apply_bind _ _ _ _ _ h_op1 ?_
        refine mh_apply_bind _ _ ⟨ptrImm, retLay⟩ _ _ h_ri1 ?_
        refine mh_apply_bind _ _ _ _ _ h_opc ?_
        refine mh_apply_bind _ _ _ _ _ h_ric ?_
        refine mh_apply_bind _ _ _ _ _ h_bin ?_
        refine mh_apply_bind _ _ () m0 m0 rfl ?_
        exact h_wr0
      dsimp only [Miri.Interpreter.ExecutionMachine.stepHooks,
        Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run]
      rw [show Miri.Interpreter.ExecutionMachine.withValidation
          (refExecutionConfigV2 rp) refLimitsV2 = refExecCfgV2 rp from rfl,
        h_ev_body]
    exact execStep_assign_ok rp m0 { m0 with stack := ⟨Array.mk [frame0W]⟩ }
      frame0 frame0W 0 0
      (toMiriBasicBlockV2 rp.types
        (@GetElem.getElem _ Nat _ _ _ rbody.basicBlocks 0 (by decide)))
      (toMiriStatementV2 rp.types
        (@GetElem.getElem _ Nat _ _ _
          (@GetElem.getElem _ Nat _ _ _ rbody.basicBlocks 0
            (by decide)).statements 0 (by decide)))
      ⟨0, Array.empty⟩
      (toMiriRvalueV2 rp.types (.binaryOp .offset (.copy ⟨1, []⟩)
        (.constant ⟨tyIdFor rp.types (.int .isize true),
          .scalar (BitVec.ofNat 128 0)⟩)))
      rfl rfl rfl rfl rfl rfl h_ass rfl rfl
  have h_find1 : m1.machine.memory.live.find? (fun e => e.1 == retAllocIdV2) =
      some (retAllocIdV2, ⟨.stack, rawRet.withExtra
        (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
          (Miri.ABI.Size.ofBytes 8))⟩) := by
    dsimp only [m1, m0, mem0, mkRefMiriState]
    rw [← Array.find?_toList]
    rfl
  have h_last1 : (m1.machine.memory.live.filter
      (fun row => row.1 != retAllocIdV2)).push
      (retAllocIdV2, ⟨.stack, rawRet.withExtra
        (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
          (Miri.ABI.Size.ofBytes 8))⟩) = m1.machine.memory.live := by
    apply Array.toList_inj.mp
    rw [Array.toList_push, Array.toList_filter]
    rfl
  let ⟨afterRet, mem', h_mem', h_step1, _, h_rd⟩ :=
    return_thinPtr_2local_v2 rp m1 frame1
      (Array.mk ((@GetElem.getElem _ Nat _ _ _ rbody.basicBlocks 0
        (by decide)).statements.map (toMiriStatementV2 rp.types)))
      .shared u8Ty ptr rawRet
      ⟨.live (.immediate ptrImm), some retLay⟩
      ⟨.live (.immediate ptrImm), some retLay⟩
      rfl rfl rfl rfl rfl rfl rfl rfl trivial rfl rfl rfl rfl rfl rfl rfl rfl rfl
      h_raw h_find1 h_last1
  have h_find2 : mem'.live.find? (fun e => e.1 == alloc2IdV2) =
      some (alloc2IdV2, ⟨.machine (), ma2⟩) := by
    rw [h_mem']
    dsimp only [m1, m0, mem0, mkRefMiriState]
    rw [← Array.find?_toList, Array.toList_push, Array.toList_filter]
    rfl
  have h_cm : refExtractCallerMemoryV2 callerMemEdge1 mem' = callerMemEdge1 := by
    dsimp only [refExtractCallerMemoryV2, callerMemEdge1]
    exact congrArg CallerMemory.mk
      (congrArg (· :: [])
        (refExtractOneCallerAllocV2_of_allocByteSliceRel mem' alloc2 alloc2
          raw alloc2IdV2 ⟨.machine (), ma2⟩ rfl rfl h_find2 h_rel))
  have h_exec : refCoreExecV2 rp (.rawPtr .shared u8Ty) retPlace
      (fun o => o = .returned ⟨.ptr ⟨some 2, 8, .isize⟩, callerMemEdge1⟩)
      False False 2 m0 := by
    change (match evalRefCoreV2 rp (.rawPtr .shared u8Ty) retPlace m0 with
      | .running m' => match evalRefCoreV2 rp (.rawPtr .shared u8Ty) retPlace m' with
        | .running _ => False
        | .returned out => out = .returned ⟨.ptr ⟨some 2, 8, .isize⟩, callerMemEdge1⟩
        | .ub | .blocked => False
      | .returned out => out = .returned ⟨.ptr ⟨some 2, 8, .isize⟩, callerMemEdge1⟩
      | .ub | .blocked => False)
    dsimp only [evalRefCoreV2]
    rw [h_step0]
    dsimp only [m1, mkRefMiriState]
    simp only [show ({ toList := [frame1] } : Array (Miri.Interpreter.Frame
        Miri.Memory.Provenance Miri.Interpreter.LocalLayout
        Miri.Interpreter.MachineHooks.FrameExtra)).isEmpty = false from rfl,
      Bool.false_eq_true, ite_false]
    rw [show Miri.Interpreter.ExecutionMachine.step (refExecutionConfigV2 rp)
        refLimitsV2 0 { m0 with stack := ⟨Array.mk [frame1]⟩ } = _ from h_step1]
    dsimp only
    rw [show ({ m1 with stack := ⟨Array.empty⟩, machine := _ } :
        RefMiriState).stack.frames.isEmpty = true from rfl, ite_true_eq]
    have h_rval : refReadReturnValV2 mem' callerMemEdge1 (.rawPtr .shared u8Ty)
        retPlace = .ok (.ptr ⟨some 2, 8, .isize⟩) := by
      have h_f' : mem'.live.find? (fun entry => entry.1 == retAllocIdV2) =
          some (retAllocIdV2, ⟨.stack, afterRet⟩) := by
        rw [h_mem']
        exact allocId_find_filter_push_v2 m1.machine.memory.live
          retAllocIdV2 ⟨.stack, afterRet⟩
      dsimp only [refReadReturnValV2, retPlace, retMemPlaceV2, retPtrV2,
        refTyLayoutFitsU64V2, Bool.not_true, ite_false]
      rw [h_f']
      dsimp only [refReadValFromAllocV2]
      rw [show Miri.ABI.Size.ofBytes (UInt64.ofNat 0) = Miri.ABI.Size.ZERO
        from rfl, h_rd]
      rfl
    rw [show ({ m1 with
        stack := ⟨Array.empty⟩
        machine := { m1.machine with
          memory := mem'
          user := { m1.machine.user with
            control := advanceRefControl refInitControl } } } :
        RefMiriState).machine.user.callerMem = callerMemEdge1 from rfl]
    rw [h_rval]
    dsimp only
    rw [h_cm]
  let ⟨h_rwf, h_rbeh, _, _⟩ := ref_ok_of_coreExec h_init h_exec
  exact ⟨h_rwf, h_rbeh, fun ms => (h_rwf ms).2.1⟩

/-- Conservative Edge 2 separation witness: dereferencing a provenance-less
null ZST pointer `*(0 as *const ())` faults with `.undefined` in `evalStepV2`,
while `ProfileV2RefMachine` is `RefWellFormedV2` and returns `()`. -/
theorem conservative_edge2_null_zst_deref_separation :
    ReachesResultV2 progV2Edge2NullZstDeref queryV2Edge2NullZstDeref
      (.fault .undefined) ∧
    ¬ WellFormedV2 progV2Edge2NullZstDeref queryV2Edge2NullZstDeref ∧
    RefWellFormedV2 (encodeProg progV2Edge2NullZstDeref)
      queryV2Edge2NullZstDeref ∧
    RefBehaviorV2 (encodeProg progV2Edge2NullZstDeref)
      queryV2Edge2NullZstDeref (.returned ⟨.unit, ⟨[]⟩⟩) ∧
    (∀ ms, ¬ RefReachesOutcomeV2 (encodeProg progV2Edge2NullZstDeref)
      queryV2Edge2NullZstDeref ms .ub) := by
  let ⟨h_f2, _, _, _, h_nwf2⟩ :=
    fault_and_exclusive_of_execFaultV2 (p := progV2Edge2NullZstDeref)
      (q := queryV2Edge2NullZstDeref) (fuel := 2) (expected := .undefined) rfl
  refine ⟨h_f2, h_nwf2, ?_⟩
  let rp := encodeProg progV2Edge2NullZstDeref
  let ⟨rawRet, h_rawRet, _, _, _, _, _, _, _, _, _, _⟩ :=
    refTryNew_spec_v2 Miri.ABI.Size.ZERO Miri.ABI.Align.ONE 1 rfl rfl
  let ⟨rawZst, h_rawZst, _, _, h_mutZ, _, _, _, _, _, _, _⟩ :=
    refTryNew_spec_v2 Miri.ABI.Size.ZERO Miri.ABI.Align.ONE 1 rfl rfl
  let unitLay := refLocalLayoutForTyV2 rp.types .unit
  let ptrLay := refLocalLayoutForTyV2 rp.types (.rawPtr .shared .unit)
  let mem0 : RefMiriMem :=
    ({ (Miri.Memory.MemoryState.empty : RefMiriMem) with
        nextAllocId := 2
        live := Array.mk [(retAllocIdV2, ⟨.stack, rawRet.withExtra
          (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
            Miri.ABI.Size.ZERO)⟩)] }).setIssuedIds (Array.mk [retAllocIdV2])
  let retPlace : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance :=
    ⟨retMemPlaceV2, unitLay⟩
  let nullPtrImm : Miri.Interpreter.Immediate Miri.Memory.Provenance :=
    .scalar (.fromScalarInt (miriScalar .isize 0))
  let rbody := @GetElem.getElem _ Nat _ _ _ rp.bodies 0 (by decide)
  let frame0 := mkRefMiriFrameV2 rp.types 0 rbody 0 0
    [⟨.live (.immediate .uninit), some unitLay⟩,
     ⟨.live (.immediate nullPtrImm), some ptrLay⟩]
    retPlace
  let m0 := mkRefMiriState frame0 mem0 refInitControl ⟨[]⟩
  have h_icm : refInitCallerMemoryV2 rp.types ⟨[]⟩ .unit =
      .ok (mem0, retPlace) := by
    dsimp only [refInitCallerMemoryV2, refOwnLayoutFitsU64V2, Bool.not_true,
      ite_false]
    rw [show (refLocalLayoutForTyV2 rp.types .unit).layout.size =
        Miri.ABI.Size.ZERO from rfl,
      show (refLocalLayoutForTyV2 rp.types .unit).layout.align.abi =
        Miri.ABI.Align.ONE from rfl, h_rawRet]
    rfl
  have h_init : ∀ ms : Nat, initRefStateV2 rp queryV2Edge2NullZstDeref ms =
      .ok { miri := m0, retTy := .unit, retPlace := retPlace,
            stepsExecuted := 0, maxSteps := ms } := by
    intro ms
    exact initRefStateV2_ok_v2 rp queryV2Edge2NullZstDeref ms rbody
      [.unit, .rawPtr .shared .unit] .unit mem0 mem0 retPlace
      [⟨.live (.immediate .uninit), some unitLay⟩,
       ⟨.live (.immediate nullPtrImm), some ptrLay⟩]
      rfl rfl rfl rfl rfl rfl rfl rfl h_icm rfl rfl rfl
  have h_nx : mem0.nextAllocId = 2 := by dsimp only [mem0]; rfl
  have h_nxn : mem0.nextAllocId.toNat = 2 := by dsimp only [mem0]; rfl
  have h_nx_nz : mem0.nextAllocId ≠ 0 := by rw [h_nx]; decide
  have h_iss : ∀ id, id ∈ mem0.issuedIds →
      id.value.toNat < mem0.nextAllocId.toNat := by
    intro id h_in
    rw [h_nxn]; dsimp only [mem0] at h_in
    cases h_in with | mk h_l =>
      cases h_l with | head => decide | tail _ h_t => cases h_t
  have h_lv : ∀ row, row ∈ mem0.live →
      row.1.value.toNat < mem0.nextAllocId.toNat := by
    intro row h_in
    rw [h_nxn]; dsimp only [mem0] at h_in
    have h_lt1 : retAllocIdV2.value.toNat < 2 := by decide
    cases h_in with | mk h_l =>
      cases h_l with | head => exact h_lt1 | tail _ h_t => cases h_t
  have h_gl : ∀ row, row ∈ mem0.globals →
      row.allocId.value.toNat < mem0.nextAllocId.toNat := by
    intro row h_in; dsimp only [mem0] at h_in
    cases h_in with | mk h_l => cases h_l
  have h_dd : ∀ row, row ∈ mem0.dead →
      row.allocId.value.toNat < mem0.nextAllocId.toNat := by
    intro row h_in; dsimp only [mem0] at h_in
    cases h_in with | mk h_l => cases h_l
  let ⟨mem1, h_res, h_as⟩ := allocateStack_unit_v2 rp m0 alloc2IdV2 rawZst
    h_rawZst rfl rfl rfl h_nx_nz (fun h => by cases h) (fun h => by cases h)
    h_iss h_lv h_gl h_dd (by
      have h_id_eq : (⟨mem0.nextAllocId, h_nx_nz⟩ : Miri.Memory.AllocId) =
          alloc2IdV2 := by
        simp only [alloc2IdV2, h_nx]
      exact h_id_eq)
  let a2Mp : Miri.Interpreter.MemPlace Miri.Memory.Provenance :=
    ⟨⟨Miri.ABI.Size.ZERO, some (.concrete alloc2IdV2 Miri.Memory.BorTag.one)⟩,
      .none, none⟩
  let frame0A : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra :=
    { frame0 with locals := (Array.mk
      [⟨.live (.indirect a2Mp), some unitLay⟩,
       ⟨.live (.immediate nullPtrImm), some ptrLay⟩]) }
  let mem2 : RefMiriMem :=
    { mem1 with
      live := mem1.live.push
        (alloc2IdV2, ⟨.stack, rawZst.withExtra
          (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
            Miri.ABI.Size.ZERO)⟩) }
  let m0A : RefMiriState :=
    { m0 with
      stack := ⟨Array.mk [frame0A]⟩
      machine := { m0.machine with
        memory := mem2
        allocationSpans :=
          (m0.machine.allocationSpans.filter fun e => e.1 != alloc2IdV2).push
            (alloc2IdV2, ⟨0⟩, none) } }
  let frame1 := { frame0A with location := .mir ⟨0, 1⟩ }
  let m1 : RefMiriState := { m0A with stack := ⟨Array.mk [frame1]⟩ }
  have h_step0 : Miri.Interpreter.ExecutionMachine.step
      (refExecutionConfigV2 rp) refLimitsV2 0 m0 = (m1, .ok true) := by
    let srcMp : Miri.Interpreter.MemPlace Miri.Memory.Provenance :=
      ⟨⟨Miri.ABI.Size.ZERO, none⟩, .none, none⟩
    have h_ev := projPlace_evalPlace_local_v2 rp m0 frame0 0 unitLay
      (.live (.immediate .uninit)) true rfl rfl rfl
    have h_deref :
        (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfgV2 rp)).dereference
          0 ⟨.immediate nullPtrImm, ptrLay⟩ m0 =
          .ok ⟨srcMp, unitLay⟩ m0 := by
      dsimp only [Miri.Interpreter.ExecutionMachine.operandHooks,
        Miri.Interpreter.ExecutionMachine.withValidation,
        refExecutionConfigV2, refOperandLeavesV2, refDereferenceOpV2, ptrLay,
        refFromImmediatePtrV2, Miri.Interpreter.PointerPlaceMachine.misalignmentWith]
      rfl
    have h_op1 :
        Miri.Interpreter.OperandMachine.evalOperandAt
            (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfgV2 rp))
            0 (Miri.Interpreter.OperandPath.rvalue "operand")
            (.Copy ⟨1, Array.mk [.Deref]⟩) (some unitLay) m0 =
          .ok ⟨.indirect srcMp, unitLay⟩ m0 := by
      have h_cf0 := currentFrame_single_v2 m0 frame0 rfl
      have h_after0 : Miri.Interpreter.MachineHooks.afterLocalRead 1 m0 =
          .ok () m0 := by
        dsimp only [Miri.Interpreter.MachineHooks.afterLocalRead,
          bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
        rw [h_cf0]; rfl
      have h_g1 : frame0.getLocal 1 =
          .ok ⟨.live (.immediate nullPtrImm), some ptrLay⟩ := rfl
      have h_gop1 : frame0.getLocalOperand 1 = .ok (.immediate nullPtrImm) := rfl
      have h_lto1 :
          Miri.Interpreter.OperandMachine.localToOp
              (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfgV2 rp))
              0 1 (if (Array.mk [Miri.MIR.ProjectionElem.Deref] :
                  Array Miri.MIR.ProjectionElem).isEmpty then some unitLay else none)
              m0 =
            .ok ⟨.immediate nullPtrImm, ptrLay⟩ m0 := by
        dsimp only [Miri.Interpreter.OperandMachine.localToOp,
          bind, Bind.bind, pure, Pure.pure]
        rw [eStateM_bind_ok h_cf0]
        rw [eStateM_bind_ok (by rw [h_g1]; rfl)]
        dsimp only
        rw [eStateM_bind_pure, eStateM_bind_ok h_cf0]
        rw [eStateM_bind_ok (by rw [h_gop1]; rfl)]
        dsimp only
        rw [show ptrLay.layout.backendRepr.isUnsized = false from rfl,
          ite_false_eq,
          eStateM_bind_ok (opHooks_validationInProgress_v2 rp m0),
          ite_false_eq, eStateM_bind_ok h_after0]
        rfl
      dsimp only [Miri.Interpreter.OperandMachine.evalOperandAt,
        Miri.Interpreter.OperandMachine.evalOperand,
        Miri.Interpreter.OperandMachine.evalPlaceToOp]
      rw [opHooks_deinitMovedPlace_v2, ite_true_eq]
      dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
        modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
      rw [show ({ m0 with machine := { m0.machine with pendingMoveDeinit := false } } :
        RefMiriState) = m0 from rfl]
      rw [h_lto1]
      dsimp only
      rw [← Array.forIn_toList, List.forIn_cons]
      dsimp only [bind, Bind.bind, pure, Pure.pure,
        Miri.Interpreter.OperandMachine.project]
      rw [show (Miri.MIR.ProjectionElem.Deref == Miri.MIR.ProjectionElem.Deref) =
          true from rfl, ite_true_eq]
      dsimp only [EStateM.bind, EStateM.pure]
      rw [h_deref]
      rfl
    have h_force0 := forceAllocation_unit_local_v2 rp m0 frame0 frame0A 0
      alloc2IdV2 mem1 rawZst rfl rfl rfl rfl h_as
    have h_toOp0 :
        Miri.Interpreter.placeToOp (refBasePlaceProjectionHooksV2 rp.types).place 0
          ⟨.local 0 0 none frame0.localsIdentity, unitLay⟩ m0A =
          .ok ⟨.indirect a2Mp, unitLay⟩ m0A := by
      dsimp only [Miri.Interpreter.placeToOp, Miri.Interpreter.placeToOpCore,
        bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
        refBasePlaceProjectionHooksV2, refBasePlaceProjectionHooks,
        Miri.Interpreter.PlaceMachine.placeHooks,
        Miri.Interpreter.PlaceMachine.localToOp,
        Miri.Interpreter.PlaceMachine.localToOpCore,
        Miri.Interpreter.PlaceMachine.layoutLocal,
        Miri.Interpreter.MachineHooks.currentFrame,
        Miri.Interpreter.Stack.currentFrame?, Miri.Interpreter.Stack.frameIndex,
        Miri.Interpreter.MachineHooks.afterLocalRead,
        get, getThe, MonadStateOf.get, EStateM.get,
        throw, throwThe, MonadExceptOf.throw, EStateM.throw]
      rw [show m0A.stack.frames = Array.mk [frame0A] from rfl]
      rfl
    have h_fself0 :
        Miri.Interpreter.forceAllocation (refBasePlaceProjectionHooksV2 rp.types).place 0
          ⟨.local 0 0 none frame0.localsIdentity, unitLay⟩ m0A =
          .ok ⟨a2Mp, unitLay⟩ m0A := by
      dsimp only [Miri.Interpreter.forceAllocation]
      rw [Miri.Interpreter.requireCurrent_eq,
        Miri.Interpreter.checkLocalIdentity_debugOff _ _ (refBaseProj_debugOff_v2 rp.types)]
      dsimp only [refBasePlaceProjectionHooksV2, refBasePlaceProjectionHooks,
        Miri.Interpreter.PlaceMachine.placeHooks,
        Miri.Interpreter.Stack.frameIndex,
        Miri.Interpreter.MachineHooks.currentFrame, Miri.Interpreter.Stack.currentFrame?,
        get, getThe, MonadStateOf.get, EStateM.get,
        bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
        throw, throwThe, MonadExceptOf.throw, EStateM.throw]
      rw [show m0A.stack.frames = Array.mk [frame0A] from rfl]
      rfl
    have h_cp0 :
        (Miri.Interpreter.ExecutionMachine.rvalueHooks (refExecCfgV2 rp)
            refLimitsV2).copyOp 0 ⟨.indirect srcMp, unitLay⟩
            ⟨.local 0 0 none frame0.localsIdentity, unitLay⟩ m0 = .ok () m0A := by
      rw [show (Miri.Interpreter.ExecutionMachine.rvalueHooks (refExecCfgV2 rp)
          refLimitsV2).copyOp = fun c s d => Miri.Interpreter.copyRuntimePlace
            (Miri.Interpreter.ExecutionMachine.projectionHooks
              (refExecCfgV2 rp)).place (refExecCfgV2 rp).copy c s d false
        from rfl]
      exact copyRuntimePlace_unit_v2 rp m0 m0A ⟨.indirect srcMp, unitLay⟩
        ⟨srcMp, unitLay⟩ ⟨a2Mp, unitLay⟩
        ⟨.local 0 0 none frame0.localsIdentity, unitLay⟩ false
        rfl rfl rfl rfl rfl rfl rfl (Or.inl rfl) h_force0 h_toOp0 h_fself0 rfl rfl
    have h_ass :
        (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfigV2 rp)
            refLimitsV2).assign 0 ⟨0, Array.empty⟩
            (toMiriRvalueV2 rp.types (.use (.copy ⟨1, [.deref]⟩))) m0 =
          (m0A, .ok ()) := by
      have h_ev_body :
          Miri.Interpreter.evalRvalueIntoPlace
              (Miri.Interpreter.ExecutionMachine.rvalueHooks (refExecCfgV2 rp)
                refLimitsV2) 0
              (toMiriRvalueV2 rp.types (.use (.copy ⟨1, [.deref]⟩)))
              ⟨0, Array.empty⟩ m0 =
            EStateM.Result.ok () m0A := by
        dsimp only [Miri.Interpreter.evalRvalueIntoPlace,
          toMiriRvalueV2, toMiriOperandV2, toMiriPlaceV2, toMiriProjElemV2,
          List.map]
        rw [show ({ toList := [Miri.MIR.ProjectionElem.Deref] } :
            Array Miri.MIR.ProjectionElem) = Array.mk [.Deref] from rfl]
        refine mh_apply_bind _ _ _ _ _ h_ev ?_
        dsimp only [Miri.Interpreter.ExecutionMachine.rvalueHooks,
          Miri.Interpreter.RuntimePlace.layout]
        rw [refStepCfgV2_eq]
        refine mh_apply_bind _ _ _ _ _ h_op1 ?_
        rw [show (Miri.MIR.WithRetag.No == Miri.MIR.WithRetag.Yes) =
          false from rfl]
        exact h_cp0
      dsimp only [Miri.Interpreter.ExecutionMachine.stepHooks,
        Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run]
      rw [show Miri.Interpreter.ExecutionMachine.withValidation
          (refExecutionConfigV2 rp) refLimitsV2 = refExecCfgV2 rp from rfl,
        h_ev_body]
    exact execStep_assign_ok rp m0 m0A frame0 frame0A 0 0
      (toMiriBasicBlockV2 rp.types
        (@GetElem.getElem _ Nat _ _ _ rbody.basicBlocks 0 (by decide)))
      (toMiriStatementV2 rp.types
        (@GetElem.getElem _ Nat _ _ _
          (@GetElem.getElem _ Nat _ _ _ rbody.basicBlocks 0
            (by decide)).statements 0 (by decide)))
      ⟨0, Array.empty⟩
      (toMiriRvalueV2 rp.types (.use (.copy ⟨1, [.deref]⟩)))
      rfl rfl rfl rfl rfl rfl h_ass rfl rfl
  let stMid : RefMiriState := { m1 with
    machine := { m1.machine with
      user := { m1.machine.user with
        control := advanceRefControl refInitControl } } }
  let stMidE : RefMiriState := { stMid with stack := ⟨Array.empty⟩ }
  have h_bt_ok := beforeTerminator_initCtrl_v2 rp m1 rfl rfl
  have h_copy1 :
      Miri.Interpreter.copyRuntimePlace
        (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfgV2 rp)).place
        (refExecCfgV2 rp).copy 0 ⟨.indirect a2Mp, unitLay⟩
        ⟨.memory retMemPlaceV2, unitLay⟩ true stMidE = .ok () stMidE :=
    copyRuntimePlace_unit_v2 rp stMidE stMidE ⟨.indirect a2Mp, unitLay⟩
      ⟨a2Mp, unitLay⟩ retPlace ⟨.memory retMemPlaceV2, unitLay⟩ true
      rfl rfl rfl rfl rfl rfl rfl (Or.inr ⟨alloc2IdV2, Miri.Memory.BorTag.one, rfl⟩)
      rfl rfl rfl rfl rfl
  have h_m1_res : mem1.live = mem0.live ∧ mem1.dead = mem0.dead :=
    reserveAllocId_live_dead_v2 mem0 mem1 alloc2IdV2 h_res
  have h_mem2_live : mem2.live =
      Array.mk [(retAllocIdV2, ⟨.stack, rawRet.withExtra
          (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
            Miri.ABI.Size.ZERO)⟩),
        (alloc2IdV2, ⟨.stack, rawZst.withExtra
          (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
            Miri.ABI.Size.ZERO)⟩)] := by
    dsimp only [mem2]
    rw [h_m1_res.1]
    rfl
  have h_mem2_dead : stMidE.machine.memory.dead = Array.empty := by
    dsimp only [stMidE, stMid, m1, m0A, mem2]
    exact h_m1_res.2
  let alc2 : RefMiriAlloc := rawZst.withExtra
    (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one Miri.ABI.Size.ZERO)
  have h_dealloc2 := deallocateStack_ret_alloc2_v2
    ⟨.stack, rawRet.withExtra
      (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one Miri.ABI.Size.ZERO)⟩
    alc2 stMidE h_mem2_live h_mem2_dead h_mutZ
  let mem3 : RefMiriMem := { mem2 with
    live := Array.mk [(retAllocIdV2, ⟨.stack, rawRet.withExtra
      (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
        Miri.ABI.Size.ZERO)⟩)]
    dead := Array.mk [⟨alloc2IdV2, alc2.byteSize, alc2.align⟩] }
  let stEnd : RefMiriState :=
    { stMid with stack := ⟨Array.empty⟩,
                 machine := { stMid.machine with memory := mem3 } }
  have h_clean :
      Miri.Interpreter.CallMachine.cleanup
        { refLifecycle rp.types with storage := refStorageHooksV2 rp.types }
        0 false frame1 stMidE = .ok .normal stEnd := by
    have h_va_for :
        forIn (m := Miri.Interpreter.MachineHooks.M Unit RefUser) frame1.vaList
            PUnit.unit (fun arg (_ : PUnit) =>
              Bind.bind
                ((refStorageHooksV2 rp.types).deallocateStack arg.mplace.ptr)
                (fun _ => pure (ForInStep.yield PUnit.unit))) stEnd =
          .ok PUnit.unit stEnd := rfl
    have h_loc_for :
        forIn (m := Miri.Interpreter.MachineHooks.M Unit RefUser)
            frame1.locals.toList PUnit.unit
            (fun slot (_ : PUnit) =>
              match slot.value with
              | .live (.indirect place) =>
                Bind.bind
                  ((refStorageHooksV2 rp.types).deallocateStack place.ptr)
                  (fun _ => pure (ForInStep.yield PUnit.unit))
              | _ => pure (ForInStep.yield PUnit.unit)) stMidE =
          .ok PUnit.unit stEnd := by
      rw [show frame1.locals.toList =
          [⟨.live (.indirect a2Mp), some unitLay⟩,
           ⟨.live (.immediate nullPtrImm), some ptrLay⟩] from rfl,
        List.forIn_cons]
      refine mh_apply_bind _ _ (ForInStep.yield PUnit.unit) stMidE stEnd
        (mh_apply_bind _ _ () stMidE stEnd h_dealloc2 rfl) ?_
      dsimp only
      rw [List.forIn_cons]
      dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
      rfl
    dsimp only [Miri.Interpreter.CallMachine.cleanup]
    rw [show frame1.returnContinuation = .stop true from rfl]
    dsimp only
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    rw [← Array.forIn_toList]
    refine mh_apply_bind _ _ _ _ _ h_loc_for ?_
    refine mh_apply_bind _ _ _ _ _ h_va_for ?_
    rfl
  have h_retOp :
      (Miri.Interpreter.ExecutionMachine.projectionHooks
          (refExecCfgV2 rp)).place.localToOp 0 0 stMid =
        .ok ⟨.indirect a2Mp, unitLay⟩ stMid := by
    rw [refProjPlace_localToOp_v2]
    dsimp only [Miri.Interpreter.PlaceMachine.localToOp,
      Miri.Interpreter.PlaceMachine.localToOpCore,
      Miri.Interpreter.PlaceMachine.layoutLocal]
    simp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
      currentFrame_single_v2 stMid frame1 rfl,
      show frame1.getLocal 0 = .ok ⟨.live (.indirect a2Mp), some unitLay⟩ from rfl,
      show frame1.getLocalOperand 0 = .ok (.indirect a2Mp) from rfl]
  have h_rf :
      (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfigV2 rp)
        refLimitsV2).terminator 0
        { sourceInfo := ⟨⟨0⟩, 0⟩, kind := .Return } stMid =
        (stEnd, .ok ()) :=
    returnFromCurrentFrame_op_single_v2 rp stMid (.indirect a2Mp) .unit
      retPlace frame1
      (Array.mk ((@GetElem.getElem _ Nat _ _ _ rbody.basicBlocks 0
        (by decide)).statements.map (toMiriStatementV2 rp.types)))
      mem2 mem3 rfl rfl rfl rfl rfl rfl rfl h_retOp h_clean h_copy1
  have h_step1 := execStep_term_ok rp m1 stMid stEnd frame1 0 1
    (toMiriBasicBlockV2 rp.types
      (@GetElem.getElem _ Nat _ _ _ rbody.basicBlocks 0 (by decide)))
    rfl rfl rfl rfl rfl h_bt_ok h_rf
  have h_exec : refCoreExecV2 rp .unit retPlace
      (fun o => o = .returned ⟨.unit, ⟨[]⟩⟩) False False 2 m0 := by
    change (match evalRefCoreV2 rp .unit retPlace m0 with
      | .running m' => match evalRefCoreV2 rp .unit retPlace m' with
        | .running _ => False
        | .returned out => out = .returned ⟨.unit, ⟨[]⟩⟩
        | .ub | .blocked => False
      | .returned out => out = .returned ⟨.unit, ⟨[]⟩⟩
      | .ub | .blocked => False)
    dsimp only [evalRefCoreV2]
    rw [h_step0]
    dsimp only [m1, m0A, mkRefMiriState]
    rw [show (Array.mk [frame1]).isEmpty = false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    rw [h_step1]
    dsimp only [stEnd, stMid, m1, m0A, mkRefMiriState]
    rw [show (⟨Array.empty⟩ : Miri.Interpreter.Stack Miri.Memory.Provenance
        Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra
        ).frames.isEmpty = true from rfl]
    simp only [ite_true]
    rfl
  let ⟨h_rwf, h_rbeh, _, _⟩ := ref_ok_of_coreExec h_init h_exec
  exact ⟨h_rwf, h_rbeh, fun ms => (h_rwf ms).2.1⟩

/-- Conservative Edge 3 separation witness: casting `*const u32` to `*mut u32`
faults with `.unsupported` in `evalStepV2`, while `ProfileV2RefMachine` is
`RefWellFormedV2` and returns the pointer via `PtrToPtr`. -/
theorem conservative_edge3_const_to_mut_cast_separation :
    ReachesResultV2 progV2Edge3ConstToMutCast queryV2Edge3ConstToMutCast
      (.fault .unsupported) ∧
    ¬ WellFormedV2 progV2Edge3ConstToMutCast queryV2Edge3ConstToMutCast ∧
    RefWellFormedV2 (encodeProg progV2Edge3ConstToMutCast)
      queryV2Edge3ConstToMutCast ∧
    RefBehaviorV2 (encodeProg progV2Edge3ConstToMutCast)
      queryV2Edge3ConstToMutCast
      (.returned ⟨.ptr ⟨some 2, 0, .isize⟩, callerMemEdge3⟩) ∧
    (∀ ms, ¬ RefReachesOutcomeV2 (encodeProg progV2Edge3ConstToMutCast)
      queryV2Edge3ConstToMutCast ms .blocked) := by
  let ⟨h_f3, _, _, _, h_nwf3⟩ :=
    fault_and_exclusive_of_execFaultV2 (p := progV2Edge3ConstToMutCast)
      (q := queryV2Edge3ConstToMutCast) (fuel := 2) (expected := .unsupported)
      rfl
  refine ⟨h_f3, h_nwf3, ?_⟩
  let rp := encodeProg progV2Edge3ConstToMutCast
  let alloc2 := @GetElem.getElem _ Nat _ _ _ callerMemEdge3.allocations 0
    (by decide)
  let raw : List UInt8 := [1, 2, 3, 4]
  let ⟨ma2, rawRet, h_rel, h_raw, h_icm, _⟩ :=
    refInit_1alloc_thinPtr_2local_v2 rp.types .mut .shared u32Ty u32Ty
      alloc2 raw 0 rfl rfl (by decide) rfl (by decide) rfl
  let mem0 : RefMiriMem :=
    ({ (Miri.Memory.MemoryState.empty : RefMiriMem) with
        nextAllocId := 3
        live := Array.mk [(alloc2IdV2, ⟨.machine (), ma2⟩),
          (retAllocIdV2, ⟨.stack, rawRet.withExtra
            (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
              (Miri.ABI.Size.ofBytes 8))⟩)] }
      ).setIssuedIds (Array.mk [alloc2IdV2, retAllocIdV2])
  let retLay := refLocalLayoutForTyV2 rp.types (.rawPtr .mut u32Ty)
  let argLay := refLocalLayoutForTyV2 rp.types (.rawPtr .shared u32Ty)
  let retPlace : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance :=
    ⟨retMemPlaceV2, retLay⟩
  let ptr : Miri.Memory.Pointer Miri.Memory.Provenance :=
    ⟨Miri.ABI.Size.ofBytes 0, .concrete alloc2IdV2 Miri.Memory.BorTag.one⟩
  let ptrImm : Miri.Interpreter.Immediate Miri.Memory.Provenance :=
    .scalar (.fromPointer refRuntimeLayoutV2.base ptr)
  let rbody := @GetElem.getElem _ Nat _ _ _ rp.bodies 0 (by decide)
  let frame0 := mkRefMiriFrameV2 rp.types 0 rbody 0 0
    [⟨.live (.immediate .uninit), some retLay⟩,
     ⟨.live (.immediate ptrImm), some argLay⟩]
    retPlace
  let m0 := mkRefMiriState frame0 mem0 refInitControl callerMemEdge3
  have h_init : ∀ ms : Nat, initRefStateV2 rp queryV2Edge3ConstToMutCast ms =
      .ok { miri := m0, retTy := .rawPtr .mut u32Ty, retPlace := retPlace,
            stepsExecuted := 0, maxSteps := ms } := by
    intro ms
    exact initRefStateV2_ok_v2 rp queryV2Edge3ConstToMutCast ms rbody
      [.rawPtr .mut u32Ty, .rawPtr .shared u32Ty] (.rawPtr .mut u32Ty)
      mem0 mem0 retPlace
      [⟨.live (.immediate .uninit), some retLay⟩,
       ⟨.live (.immediate ptrImm), some argLay⟩]
      rfl rfl rfl rfl rfl rfl rfl rfl h_icm rfl rfl rfl
  let frame0W := { frame0 with locals := (Array.mk
    [⟨.live (.immediate ptrImm), some retLay⟩,
     ⟨.live (.immediate ptrImm), some argLay⟩]) }
  let frame1 := { frame0W with location := .mir ⟨0, 1⟩ }
  let m1 : RefMiriState := { m0 with stack := ⟨Array.mk [frame1]⟩ }
  have h_step0 : Miri.Interpreter.ExecutionMachine.step
      (refExecutionConfigV2 rp) refLimitsV2 0 m0 = (m1, .ok true) := by
    have h_ev := projPlace_evalPlace_local_v2 rp m0 frame0 0 retLay
      (.live (.immediate .uninit)) true rfl rfl rfl
    have h_op1 := evalOperand_local_imm_v2 rp m0 frame0 1 argLay ptrImm
      none (Miri.Interpreter.OperandPath.rvalue "operand") rfl rfl rfl rfl
    have h_val0 := rawPtr_validate_v2 rp.types
      { m0 with stack := ⟨Array.mk [frame0W]⟩ } 0 u32Ty .mut ptr frame0W
      rfl rfl rfl rfl rfl
    have h_cast := refCastHooks_ptrToPtr_v2 rp .shared .mut u32Ty u32Ty ptr
      frame0 frame0W m0 0 rfl rfl rfl rfl rfl rfl rfl rfl rfl h_val0
    have h_ass :
        (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfigV2 rp)
            refLimitsV2).assign 0 ⟨0, Array.empty⟩
            (toMiriRvalueV2 rp.types (.cast .ptrToPtr (.copy ⟨1, []⟩)
              (tyIdFor rp.types (.rawPtr .mut u32Ty)))) m0 =
          ({ m0 with stack := ⟨Array.mk [frame0W]⟩ }, .ok ()) := by
      have h_ev_body :
          Miri.Interpreter.evalRvalueIntoPlace
              (Miri.Interpreter.ExecutionMachine.rvalueHooks (refExecCfgV2 rp)
                refLimitsV2) 0
              (toMiriRvalueV2 rp.types (.cast .ptrToPtr (.copy ⟨1, []⟩)
                (tyIdFor rp.types (.rawPtr .mut u32Ty))))
              ⟨0, Array.empty⟩ m0 =
            EStateM.Result.ok () { m0 with stack := ⟨Array.mk [frame0W]⟩ } := by
        dsimp only [Miri.Interpreter.evalRvalueIntoPlace,
          toMiriRvalueV2, toMiriOperandV2, toMiriPlaceV2, toMiriProjElemV2,
          List.map]
        rw [show ({ toList := [] } : Array Miri.MIR.ProjectionElem) =
              Array.empty from rfl,
          show canonicalTyId rp.types (tyIdFor rp.types (.rawPtr .mut u32Ty)) =
            tyIdFor rp.types (.rawPtr .mut u32Ty) from rfl]
        refine mh_apply_bind _ _ _ _ _ h_ev ?_
        dsimp only [Miri.Interpreter.ExecutionMachine.rvalueHooks,
          Miri.Interpreter.RuntimePlace.layout]
        rw [refStepCfgV2_eq]
        refine mh_apply_bind _ _ _ _ _ h_op1 ?_
        refine mh_apply_bind _ _ (tyIdFor rp.types (.rawPtr .mut u32Ty))
          _ _ rfl ?_
        exact h_cast
      dsimp only [Miri.Interpreter.ExecutionMachine.stepHooks,
        Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run]
      rw [show Miri.Interpreter.ExecutionMachine.withValidation
          (refExecutionConfigV2 rp) refLimitsV2 = refExecCfgV2 rp from rfl,
        h_ev_body]
    exact execStep_assign_ok rp m0 { m0 with stack := ⟨Array.mk [frame0W]⟩ }
      frame0 frame0W 0 0
      (toMiriBasicBlockV2 rp.types
        (@GetElem.getElem _ Nat _ _ _ rbody.basicBlocks 0 (by decide)))
      (toMiriStatementV2 rp.types
        (@GetElem.getElem _ Nat _ _ _
          (@GetElem.getElem _ Nat _ _ _ rbody.basicBlocks 0
            (by decide)).statements 0 (by decide)))
      ⟨0, Array.empty⟩
      (toMiriRvalueV2 rp.types (.cast .ptrToPtr (.copy ⟨1, []⟩)
        (tyIdFor rp.types (.rawPtr .mut u32Ty))))
      rfl rfl rfl rfl rfl rfl h_ass rfl rfl
  have h_find1 : m1.machine.memory.live.find? (fun e => e.1 == retAllocIdV2) =
      some (retAllocIdV2, ⟨.stack, rawRet.withExtra
        (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
          (Miri.ABI.Size.ofBytes 8))⟩) := by
    dsimp only [m1, m0, mem0, mkRefMiriState]
    rw [← Array.find?_toList]; rfl
  have h_last1 : (m1.machine.memory.live.filter
      (fun row => row.1 != retAllocIdV2)).push
      (retAllocIdV2, ⟨.stack, rawRet.withExtra
        (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
          (Miri.ABI.Size.ofBytes 8))⟩) = m1.machine.memory.live := by
    apply Array.toList_inj.mp
    rw [Array.toList_push, Array.toList_filter]; rfl
  let ⟨afterRet, mem', h_mem', h_step1, _, h_rd⟩ :=
    return_thinPtr_2local_v2 rp m1 frame1
      (Array.mk ((@GetElem.getElem _ Nat _ _ _ rbody.basicBlocks 0
        (by decide)).statements.map (toMiriStatementV2 rp.types)))
      .mut u32Ty ptr rawRet
      ⟨.live (.immediate ptrImm), some retLay⟩
      ⟨.live (.immediate ptrImm), some argLay⟩
      rfl rfl rfl rfl rfl rfl rfl rfl trivial rfl rfl rfl rfl rfl rfl rfl rfl rfl
      h_raw h_find1 h_last1
  have h_find2 : mem'.live.find? (fun e => e.1 == alloc2IdV2) =
      some (alloc2IdV2, ⟨.machine (), ma2⟩) := by
    rw [h_mem']
    dsimp only [m1, m0, mem0, mkRefMiriState]
    rw [← Array.find?_toList, Array.toList_push, Array.toList_filter]; rfl
  have h_cm : refExtractCallerMemoryV2 callerMemEdge3 mem' = callerMemEdge3 := by
    dsimp only [refExtractCallerMemoryV2, callerMemEdge3]
    exact congrArg CallerMemory.mk
      (congrArg (· :: [])
        (refExtractOneCallerAllocV2_of_allocByteSliceRel mem' alloc2 alloc2
          raw alloc2IdV2 ⟨.machine (), ma2⟩ rfl rfl h_find2 h_rel))
  have h_exec : refCoreExecV2 rp (.rawPtr .mut u32Ty) retPlace
      (fun o => o = .returned ⟨.ptr ⟨some 2, 0, .isize⟩, callerMemEdge3⟩)
      False False 2 m0 := by
    change (match evalRefCoreV2 rp (.rawPtr .mut u32Ty) retPlace m0 with
      | .running m' => match evalRefCoreV2 rp (.rawPtr .mut u32Ty) retPlace m' with
        | .running _ => False
        | .returned out => out =
          .returned ⟨.ptr ⟨some 2, 0, .isize⟩, callerMemEdge3⟩
        | .ub | .blocked => False
      | .returned out => out =
        .returned ⟨.ptr ⟨some 2, 0, .isize⟩, callerMemEdge3⟩
      | .ub | .blocked => False)
    dsimp only [evalRefCoreV2]
    rw [h_step0]
    dsimp only [m1, mkRefMiriState]
    simp only [show ({ toList := [frame1] } : Array (Miri.Interpreter.Frame
        Miri.Memory.Provenance Miri.Interpreter.LocalLayout
        Miri.Interpreter.MachineHooks.FrameExtra)).isEmpty = false from rfl,
      Bool.false_eq_true, ite_false]
    rw [show Miri.Interpreter.ExecutionMachine.step (refExecutionConfigV2 rp)
        refLimitsV2 0 { m0 with stack := ⟨Array.mk [frame1]⟩ } = _ from h_step1]
    dsimp only
    rw [show ({ m1 with stack := ⟨Array.empty⟩, machine := _ } :
        RefMiriState).stack.frames.isEmpty = true from rfl, ite_true_eq]
    have h_rval : refReadReturnValV2 mem' callerMemEdge3 (.rawPtr .mut u32Ty)
        retPlace = .ok (.ptr ⟨some 2, 0, .isize⟩) := by
      have h_f' : mem'.live.find? (fun entry => entry.1 == retAllocIdV2) =
          some (retAllocIdV2, ⟨.stack, afterRet⟩) := by
        rw [h_mem']
        exact allocId_find_filter_push_v2 m1.machine.memory.live
          retAllocIdV2 ⟨.stack, afterRet⟩
      dsimp only [refReadReturnValV2, retPlace, retMemPlaceV2, retPtrV2,
        refTyLayoutFitsU64V2, Bool.not_true, ite_false]
      rw [h_f']
      dsimp only [refReadValFromAllocV2]
      rw [show Miri.ABI.Size.ofBytes (UInt64.ofNat 0) = Miri.ABI.Size.ZERO
        from rfl, h_rd]
      rfl
    rw [show ({ m1 with
        stack := ⟨Array.empty⟩
        machine := { m1.machine with
          memory := mem'
          user := { m1.machine.user with
            control := advanceRefControl refInitControl } } } :
        RefMiriState).machine.user.callerMem = callerMemEdge3 from rfl]
    rw [h_rval]
    dsimp only
    rw [h_cm]
  let ⟨h_rwf, h_rbeh, _, _⟩ := ref_ok_of_coreExec h_init h_exec
  exact ⟨h_rwf, h_rbeh, fun ms => (h_rwf ms).2.2⟩

/-! ## Section 3: Boundary & Panic-Abort Regression Witnesses -/

/-- Minimal well-formed empty Profile v2 program returning `()` for
`CallerMemory` entry validation witnesses. -/
noncomputable def progV2UnitNoop : Program :=
  mkV2Prog {
    identity := "v2_unit_noop"
    argumentCount := 0
    locals := [.unit]
    basicBlocks := [{
      statements := [.assign ⟨0, []⟩ (.use (.constant ⟨.unit, .zeroSized⟩))]
      terminator := .return_
    }]
  }

/-- Regression witness: `initRefStateV2` rejects caller allocations whose
`allocId` exceeds `UInt64.max` (preventing modulo-`2^64` aliasing with id `1`),
rejects `{1, 2^64 - 2}` whose `nextAllocId` would wrap to `0`, and rejects
pointer arguments whose `allocId` exceeds `UInt64.max` (including multiples
`k * 2^64` that would otherwise truncate to `0` / `none` provenance). -/
theorem profileV2_rejects_allocId_overflow :
    let cmBadAlloc : CallerMemory := ⟨[
      { allocId := 1, alignLog2 := 0, mutability := .mut,
        bytes := [.init 1 none], live := true },
      { allocId := Nat.pow 2 64 + 1, alignLog2 := 0, mutability := .mut,
        bytes := [.init 2 none], live := true }
    ]⟩
    let cmWrapNext : CallerMemory := ⟨[
      { allocId := 1, alignLog2 := 0, mutability := .mut,
        bytes := [.init 1 none], live := true },
      { allocId := Nat.pow 2 64 - 2, alignLog2 := 0, mutability := .mut,
        bytes := [.init 2 none], live := true }
    ]⟩
    let qBadAlloc : Query := { args := [], callerMem := cmBadAlloc }
    let qWrapNext : Query := { args := [], callerMem := cmWrapNext }
    let qBadArg : Query := {
      args := [.ptr ⟨some (Nat.pow 2 64 + 2), 0, .isize⟩]
      callerMem := ⟨[]⟩
    }
    let qBadArgZeroMod : Query := {
      args := [.ptr ⟨some (Nat.pow 2 64), 0, .isize⟩]
      callerMem := ⟨[]⟩
    }
    initRefStateV2 (encodeProg progV2UnitNoop) qBadAlloc 1 =
      .error .unsupported ∧
    initRefStateV2 (encodeProg progV2UnitNoop) qWrapNext 1 =
      .error .unsupported ∧
    initRefStateV2 (encodeProg progV2Edge2NullZstDeref) qBadArg 1 =
      .error .unsupported ∧
    initRefStateV2 (encodeProg progV2Edge2NullZstDeref) qBadArgZeroMod 1 =
      .error .unsupported := by
  refine ⟨rfl, ?_, rfl, rfl⟩
  let prog := encodeProg progV2UnitNoop
  let al1 : Trusted.MirSemantics.Allocation :=
    { allocId := 1, alignLog2 := 0, mutability := .mut,
      bytes := [.init 1 none], live := true }
  let alMax2 : Trusted.MirSemantics.Allocation :=
    { allocId := Nat.pow 2 64 - 2, alignLog2 := 0, mutability := .mut,
      bytes := [.init 2 none], live := true }
  let cmWrapNext : CallerMemory := ⟨[al1, alMax2]⟩
  let tree1 := Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
    (Miri.ABI.Size.ofBytes (UInt64.ofNat 1))
  let ⟨rawRet, h_raw, _⟩ :=
    refTryNew_spec_v2 Miri.ABI.Size.ZERO Miri.ABI.Align.ONE 1 rfl rfl
  let ⟨ma1, h_fb1, _⟩ := miriAlloc_fromBytes_spec
    (Prov := Miri.Memory.Provenance) (Array.mk [1]) ⟨0⟩ .Mut tree1
    (by decide) (by decide)
  let ⟨ma2, h_fb2, _⟩ := miriAlloc_fromBytes_spec
    (Prov := Miri.Memory.Provenance) (Array.mk [2]) ⟨0⟩ .Mut tree1
    (by decide) (by decide)
  have h_id1 : (refExactAllocIdV2 1).isSome = true := rfl
  have h_id2 : (refExactAllocIdV2 (Nat.pow 2 64 - 2)).isSome = true := rfl
  have h_idRet : (refExactAllocIdV2 (Nat.pow 2 64 - 1)).isSome = true := rfl
  cases h_e1 : refExactAllocIdV2 1 with
  | none => rw [h_e1] at h_id1; cases h_id1
  | some mid1 =>
    cases h_e2 : refExactAllocIdV2 (Nat.pow 2 64 - 2) with
    | none => rw [h_e2] at h_id2; cases h_id2
    | some mid2 =>
      cases h_eRet : refExactAllocIdV2 (Nat.pow 2 64 - 1) with
      | none => rw [h_eRet] at h_idRet; cases h_idRet
      | some midRet =>
        have h_to1 : refAllocToMiriV2 al1 = .ok (ma1.withExtra tree1) := by
          dsimp only [refAllocToMiriV2]
          rw [show refPlainInitBytesV2? al1.bytes = some [1] from rfl]
          dsimp only
          rw [show al1.alignLog2 = 0 from rfl,
            show toMiriMutV2 al1.mutability = .Mut from rfl,
            show al1.bytes.length = 1 from rfl, h_fb1]
        have h_to2 : refAllocToMiriV2 alMax2 = .ok (ma2.withExtra tree1) := by
          dsimp only [refAllocToMiriV2]
          rw [show refPlainInitBytesV2? alMax2.bytes = some [2] from rfl]
          dsimp only
          rw [show alMax2.alignLog2 = 0 from rfl,
            show toMiriMutV2 alMax2.mutability = .Mut from rfl,
            show alMax2.bytes.length = 1 from rfl, h_fb2]
        have h_icm : ∀ (v : RefMiriMem → Bool), (∀ m, v m = true) →
            refInitCallerMemoryV2 prog.types cmWrapNext .unit v 0 false =
              .error .unsupported := by
          intro v h_v
          dsimp only [refInitCallerMemoryV2, refOwnLayoutFitsU64V2]
          simp only [Bool.not_true, Bool.false_eq_true, ite_false]
          rw [show (refLocalLayoutForTyV2 prog.types .unit).layout.size =
              Miri.ABI.Size.ZERO from rfl,
            show (refLocalLayoutForTyV2 prog.types .unit).layout.align.abi =
              Miri.ABI.Align.ONE from rfl, h_raw]
          rw [show cmWrapNext.allocations = [al1, alMax2] from rfl]
          dsimp only [refInsertCallerAllocsV2]
          rw [show al1.allocId = 1 from rfl, h_e1, h_to1,
            show al1.live = true from rfl]
          simp only [ite_true]
          rw [show alMax2.allocId = Nat.pow 2 64 - 2 from rfl, h_e2, h_to2]
          dsimp only
          simp only [h_v _, Bool.not_true, Bool.false_eq_true, ite_false]
          rw [show refHasAllocIdV2 1 [al1, alMax2] = true from rfl,
            show refAllocBytesHaveProvIdV2 1 [al1, alMax2] = false from rfl,
            show refMaxAllocIdV2 [al1, alMax2] = Nat.pow 2 64 - 2 from rfl,
            show refMaxAllocBytesProvIdV2 [al1, alMax2] = 0 from rfl]
          simp only [Bool.or_false, Nat.max_zero, ite_true]
          rw [show (Nat.pow 2 64 - 2) + 1 = Nat.pow 2 64 - 1 from rfl, h_eRet]
          dsimp only
          rw [show (! (UInt64.ofNat ((Nat.pow 2 64 - 2) + 2)).toNat.beq
              ((Nat.pow 2 64 - 2) + 2)) = true from rfl]
          simp only [ite_true]
        let rbody := @GetElem.getElem _ Nat _ _ _ prog.bodies 0 (by decide)
        change initRefStateV2 prog { args := [], callerMem := cmWrapNext } 1 =
          .error .unsupported
        dsimp only [initRefStateV2]
        rw [show (!Nat.beq prog.pointerWidthBits 64 ||
            !Nat.beq prog.mirProfileVersion 2) = false from rfl]
        simp only [Bool.false_eq_true, ite_false]
        rw [show (!refValidCallerMemoryV2 cmWrapNext) = false from rfl]
        simp only [Bool.false_eq_true, ite_false]
        rw [show Trusted.MirSemantics.getElem? prog.bodies prog.entryDefId =
            some rbody from rfl]
        dsimp only
        rw [show decodeLocalTys prog.types rbody.locals = some [.unit] from rfl]
        dsimp only
        rw [show (rbody.basicBlocks.isEmpty ||
            !Nat.blt rbody.argumentCount ([MirTy.unit] : List MirTy).length ||
            !refStorageAnnotationsInBounds rbody ||
            !refDiscriminantTypesValid [.unit] rbody ||
            !refCastTypesValid prog.types [.unit] rbody ||
            ![MirTy.unit].all refIsSupportedLocalTyV2 ||
            ![MirTy.unit].all refTyLayoutFitsU64V2) = false from rfl]
        simp only [Bool.false_eq_true, ite_false]
        rw [show (!checkRefArgsMatchV2 []
              (List.take rbody.argumentCount (([MirTy.unit] : List MirTy).drop 1)) ||
            !refValListAllocIdsFitU64V2 []) = false from rfl]
        simp only [Bool.false_eq_true, ite_false]
        rw [show Trusted.MirSemantics.getElem? [MirTy.unit] 0 =
            some MirTy.unit from rfl]
        dsimp only
        rw [show List.take rbody.argumentCount
            (List.drop 1 ([MirTy.unit] : List MirTy)) = [] from rfl,
          show refMaxValListAllocIdV2 [] = 0 from rfl,
          show refValListHasAllocIdV2 1 [] = false from rfl]
        rw [h_icm
          (fun memCaller => refRefsValidInMiriListV2 memCaller [] [] &&
            refSpansPairwiseDisjointV2 (refAccessSpansListV2 [] []))
          (fun _ => rfl)]

/-- Regression witness: `initRefStateV2` rejects live caller allocations with
partial (1-byte), over-long (9-byte), or mismatched provenance byte runs before
execution, while valid 8-byte provenance runs round-trip cleanly and
`refByteProvAtV2` recovers surviving `byteFragments` when `ptrs` misses. -/
theorem profileV2_partial_provenance_and_fragments_spec :
    let cmPartial : CallerMemory := ⟨[{
      allocId := 2, alignLog2 := 0, mutability := .shared,
      bytes := [.init 42 (some 2)], live := true
    }]⟩
    let cmNine : CallerMemory := ⟨[{
      allocId := 2, alignLog2 := 0, mutability := .shared,
      bytes := List.replicate 9 (.init 1 (some 2)), live := true
    }]⟩
    let cmMixed : CallerMemory := ⟨[{
      allocId := 2, alignLog2 := 0, mutability := .shared,
      bytes := List.replicate 7 (.init 1 (some 2)) ++ [.init 1 (some 3)],
      live := true
    }]⟩
    let ptrBytes := (leBytesOfNat 8 16).map (fun b => AllocByte.init b (some 2))
    let alPtr : Trusted.MirSemantics.Allocation := {
      allocId := 2, alignLog2 := 3, mutability := .mut,
      bytes := ptrBytes, live := true
    }
    (initRefStateV2 (encodeProg progV2UnitNoop)
        { args := [], callerMem := cmPartial } 1 = .error .unsupported) ∧
    (initRefStateV2 (encodeProg progV2UnitNoop)
        { args := [], callerMem := cmNine } 1 = .error .unsupported) ∧
    (initRefStateV2 (encodeProg progV2UnitNoop)
        { args := [], callerMem := cmMixed } 1 = .error .unsupported) ∧
    ((refAllocToMiriV2 alPtr).map (fun ma =>
      refExtractOneCallerAllocV2
        { (Miri.Memory.MemoryState.empty : RefMiriMem) with
          live := Array.mk [(alloc2IdV2, ⟨.machine (), ma⟩)] } alPtr) =
      .ok alPtr) ∧
    (∀ pmap : Miri.Memory.ProvenanceMap Miri.Memory.Provenance,
      pmap.ptrs = Array.empty →
      pmap.byteFragments = some (Array.mk [(Miri.ABI.Size.ofBytes 1,
        ⟨1, .concrete alloc2IdV2 Miri.Memory.BorTag.one,
          Vector.replicate 8 0⟩)]) →
      (refByteProvAtV2 pmap 0, refByteProvAtV2 pmap 1) = (none, some 2)) := by
  let prog := encodeProg progV2UnitNoop
  have initErrOfBadPop :
      ∀ (al : Trusted.MirSemantics.Allocation) (n : Nat),
        al.allocId = 2 →
        al.alignLog2 = 0 →
        al.mutability = .shared →
        al.live = true →
        al.bytes.length = n →
        (Miri.ABI.Size.ofBytes (UInt64.ofNat n)).bytes.toNat = n →
        Nat.blt n (Nat.pow 2 63) = true →
        refPlainInitBytesV2? al.bytes = none →
        (∀ blank : Miri.Memory.Allocation Miri.Memory.Provenance Unit,
          Miri.Memory.Allocation.tryNew
            (Prov := Miri.Memory.Provenance)
            (Miri.ABI.Size.ofBytes (UInt64.ofNat n)) ⟨0⟩ .Uninit
            (fun m _ => some (Array.replicate m.bytes.toNat 0)) = .ok blank →
          blank.byteSize = Miri.ABI.Size.ofBytes (UInt64.ofNat n) →
          blank.len = n →
          blank.mutability = .Mut →
          blank.provenanceMap = Miri.Memory.ProvenanceMap.new →
          blank.initializationMask =
            Miri.Memory.InitMask.new
              (Miri.ABI.Size.ofBytes (UInt64.ofNat n)) false →
          Miri.Memory.InitMask.WriteProof.WellFormed
            blank.initializationMask →
          refPopulateAllocBytesV2 blank 0 al.bytes = .error .unsupported) →
        initRefStateV2 prog { args := [], callerMem := ⟨[al]⟩ } 1 =
          .error .unsupported := by
    intro al n h_id h_al h_mut h_live h_len h_toNat h_n_lt h_plain h_pop
    let szN := Miri.ABI.Size.ofBytes (UInt64.ofNat n)
    let ⟨blank, h_try, h_bsz, h_blen, h_bmut, _, _, _, h_bpm, h_bim, h_bwf, _⟩ :=
      refTryNew_spec_v2 szN ⟨0⟩ 1 rfl rfl
    have h_blen' : blank.len = n := h_blen.trans h_toNat
    have h_to : refAllocToMiriV2 al = .error .unsupported := by
      dsimp only [refAllocToMiriV2]
      rw [h_plain]
      dsimp only
      rw [h_len, h_al, show Miri.ABI.Size.ofBytes (UInt64.ofNat n) = szN from rfl,
        h_try]
      dsimp only
      rw [h_pop blank h_try h_bsz h_blen' h_bmut h_bpm h_bim h_bwf]
    have h_ins :
        refInsertCallerAllocsV2 (Miri.Memory.MemoryState.empty : RefMiriMem)
          Array.empty [al] = .error .unsupported := by
      dsimp only [refInsertCallerAllocsV2]
      rw [h_id, show refExactAllocIdV2 2 = some alloc2IdV2 from rfl, h_live]
      dsimp only
      rw [ite_true_eq, h_to]
    have h_icm : ∀ (v : RefMiriMem → Bool) (em : Trusted.MirAst.AllocId)
        (eh : Bool),
        refInitCallerMemoryV2 prog.types ⟨[al]⟩ .unit v em eh =
          .error .unsupported := by
      intro _ _ _
      let ⟨rawRet, h_raw, _⟩ :=
        refTryNew_spec_v2 Miri.ABI.Size.ZERO Miri.ABI.Align.ONE 1 rfl rfl
      dsimp only [refInitCallerMemoryV2, refOwnLayoutFitsU64V2]
      simp only [Bool.not_true, Bool.false_eq_true, ite_false]
      rw [show (refLocalLayoutForTyV2 prog.types .unit).layout.size =
          Miri.ABI.Size.ZERO from rfl,
        show (refLocalLayoutForTyV2 prog.types .unit).layout.align.abi =
          Miri.ABI.Align.ONE from rfl, h_raw]
      dsimp only
      rw [h_ins]
    have h_cm : refValidCallerMemoryV2 ⟨[al]⟩ = true := by
      dsimp only [refValidCallerMemoryV2, refAllocIdsValidV2]
      rw [h_id, h_al, h_len, h_n_lt]
      rfl
    let rbody := @GetElem.getElem _ Nat _ _ _ prog.bodies 0 (by decide)
    have h_b : Trusted.MirSemantics.getElem? prog.bodies prog.entryDefId =
        some rbody := rfl
    dsimp only [initRefStateV2]
    rw [show (!Nat.beq prog.pointerWidthBits 64 || !Nat.beq prog.mirProfileVersion 2) =
        false from rfl]
    simp only [Bool.false_eq_true, ite_false, h_cm, Bool.not_true]
    rw [h_b]
    dsimp only
    rw [show decodeLocalTys prog.types rbody.locals = some [.unit] from rfl]
    dsimp only
    rw [show (rbody.basicBlocks.isEmpty ||
        !Nat.blt rbody.argumentCount ([MirTy.unit] : List MirTy).length ||
        !refStorageAnnotationsInBounds rbody ||
        !refDiscriminantTypesValid [.unit] rbody ||
        !refCastTypesValid prog.types [.unit] rbody ||
        ![MirTy.unit].all refIsSupportedLocalTyV2 ||
        ![MirTy.unit].all refTyLayoutFitsU64V2) = false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    rw [show (!checkRefArgsMatchV2 []
          (List.take rbody.argumentCount (([MirTy.unit] : List MirTy).drop 1)) ||
        !refValListAllocIdsFitU64V2 []) = false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    rw [show Trusted.MirSemantics.getElem? [MirTy.unit] 0 =
        some MirTy.unit from rfl]
    dsimp only
    rw [h_icm]
  refine ⟨?_, ?_, ?_, ?_, fun pmap h_p h_f => ?_⟩
  · exact initErrOfBadPop _ 1 rfl rfl rfl rfl rfl rfl rfl rfl
      fun blank _ _ _ _ _ _ _ => rfl
  · have h_nine :
        (List.replicate 9 (AllocByte.init 1 (some 2))) = [
          AllocByte.init 1 (some 2), AllocByte.init 1 (some 2),
          AllocByte.init 1 (some 2), AllocByte.init 1 (some 2),
          AllocByte.init 1 (some 2), AllocByte.init 1 (some 2),
          AllocByte.init 1 (some 2), AllocByte.init 1 (some 2),
          AllocByte.init 1 (some 2)] := rfl
    refine initErrOfBadPop _ 9 rfl rfl rfl rfl rfl rfl (by decide) rfl
      fun blank _ h_bsz h_blen h_bmut h_bpm h_bim h_bwf => ?_
    let sz8 := Miri.ABI.Size.ofBytes 8
    let rng8 := Miri.Memory.allocRange Miri.ABI.Size.ZERO sz8
    let ptrOff := Miri.ABI.Size.ofBytes (UInt64.ofNat
      (refNatOfLeBytesV2 [1, 1, 1, 1, 1, 1, 1, 1]))
    let ptr : Miri.Memory.Pointer Miri.Memory.Provenance :=
      ⟨ptrOff, .concrete alloc2IdV2 Miri.Memory.BorTag.one⟩
    have h_ins := Miri.Memory.ProvenanceMap.insertPtr_new Miri.ABI.Size.ZERO sz8
      sz8 (Miri.Memory.Provenance.concrete alloc2IdV2 Miri.Memory.BorTag.one)
      (by decide) rfl
    let ⟨updated, h_ws, _⟩ :=
      Miri.Memory.Allocation.writeScalar_spec refRuntimeLayoutV2.base blank rng8
        (.fromPointer refRuntimeLayoutV2.base ptr) (.pointer ptr)
        Miri.Memory.ProvenanceMap.new _ (by rw [h_blen, h_bsz]; rfl) h_bmut
        (by rw [h_bim, h_bsz]; rfl) h_bwf (by decide) (by decide)
        (by rw [h_bsz]; decide) rfl
        (fun fullBytes _ => by
          rw [h_bpm]
          exact Miri.Memory.ProvenanceMap.clear_new rng8 fullBytes
            (Miri.ABI.Size.fromBits refRuntimeLayoutV2.base.pointerWidth.bits)
            sz8 (by decide) rfl)
        ⟨rfl, h_ins⟩
    rw [h_nine]
    dsimp only [refPopulateAllocBytesV2, Miri.Memory.Allocation.writePointer]
    rw [show (Nat.beq 2 2 && Nat.beq 2 2 && Nat.beq 2 2 && Nat.beq 2 2 &&
          Nat.beq 2 2 && Nat.beq 2 2 && Nat.beq 2 2) = true from rfl,
      ite_true_eq, show refExactAllocIdV2 2 = some alloc2IdV2 from rfl]
    dsimp only [Miri.Memory.Allocation.writePointer]
    rw [show Miri.ABI.Size.ofBytes (UInt64.ofNat 0) = Miri.ABI.Size.ZERO
      from rfl]
    rw [show Miri.ABI.Size.ofBytes (UInt64.ofNat
      (refNatOfLeBytesV2 [1, 1, 1, 1, 1, 1, 1, 1])) = ptrOff from rfl]
    dsimp only [rng8, ptr, sz8] at h_ws
    rw [h_ws]
  · have h_mix :
        (List.replicate 7 (AllocByte.init 1 (some 2)) ++
          [AllocByte.init 1 (some 3)]) = [
          AllocByte.init 1 (some 2), AllocByte.init 1 (some 2),
          AllocByte.init 1 (some 2), AllocByte.init 1 (some 2),
          AllocByte.init 1 (some 2), AllocByte.init 1 (some 2),
          AllocByte.init 1 (some 2), AllocByte.init 1 (some 3)] := rfl
    refine initErrOfBadPop _ 8 rfl rfl rfl rfl rfl rfl (by decide) rfl
      fun blank _ _ _ _ _ _ _ => ?_
    change refPopulateAllocBytesV2 blank 0
        (List.replicate 7 (AllocByte.init 1 (some 2)) ++
          [AllocByte.init 1 (some 3)]) = .error .unsupported
    rw [h_mix]
    rfl
  · let ptrBytes := (leBytesOfNat 8 16).map (fun b => AllocByte.init b (some 2))
    let alPtr : Trusted.MirSemantics.Allocation := {
      allocId := 2, alignLog2 := 3, mutability := .mut,
      bytes := ptrBytes, live := true
    }
    have h_pb : ptrBytes = [
        AllocByte.init 16 (some 2), AllocByte.init 0 (some 2),
        AllocByte.init 0 (some 2), AllocByte.init 0 (some 2),
        AllocByte.init 0 (some 2), AllocByte.init 0 (some 2),
        AllocByte.init 0 (some 2), AllocByte.init 0 (some 2)] := rfl
    have h_plain : refPlainInitBytesV2? ptrBytes = none := rfl
    let sz8 := Miri.ABI.Size.ofBytes 8
    let rng8 := Miri.Memory.allocRange Miri.ABI.Size.ZERO sz8
    let ptr : Miri.Memory.Pointer Miri.Memory.Provenance :=
      ⟨Miri.ABI.Size.ofBytes 16, .concrete alloc2IdV2 Miri.Memory.BorTag.one⟩
    let tree := Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one sz8
    let ⟨blank, h_try, h_bsz, h_len, h_mut, h_al, _, _, h_pm, h_im, h_wf, _⟩ :=
      refTryNew_spec_v2 sz8 ⟨3⟩ 8 rfl rfl
    have h_ins := Miri.Memory.ProvenanceMap.insertPtr_new Miri.ABI.Size.ZERO sz8
      sz8 (Miri.Memory.Provenance.concrete alloc2IdV2 Miri.Memory.BorTag.one)
      (by decide) rfl
    let ⟨updated, h_ws, h_ubsz, _, _, h_ual, _, _, _, _, h_setim, _, h_upm, _,
        h_ugb_ptr, _⟩ :=
      Miri.Memory.Allocation.writeScalar_spec refRuntimeLayoutV2.base blank rng8
        (.fromPointer refRuntimeLayoutV2.base ptr) (.pointer ptr)
        Miri.Memory.ProvenanceMap.new _ (by rw [h_len, h_bsz]) h_mut
        (by rw [h_im, h_bsz]; rfl) h_wf (by decide)
        (by decide) (by rw [h_bsz]; decide) rfl
        (fun fullBytes _ => by
          rw [h_pm]
          exact Miri.Memory.ProvenanceMap.clear_new rng8 fullBytes
            (Miri.ABI.Size.fromBits refRuntimeLayoutV2.base.pointerWidth.bits)
            sz8 (by decide) rfl)
        ⟨rfl, h_ins⟩
    rw [h_im] at h_setim
    rw [Miri.Memory.InitMask.full_overwrite_stays_lazy sz8 sz8 false true rng8
      rfl rfl (by decide)] at h_setim
    injection h_setim with h_uim
    have h_raw_ok :
        updated.getBytesUnchecked rng8 = .ok (Array.mk (leBytesOfNat 8 16)) :=
      (h_ugb_ptr ptr rfl).trans
        (congrArg Except.ok (by dsimp only [ptr, rng8, sz8]; decide))
    have h_toMiri :
        refAllocToMiriV2 alPtr =
          .ok ((updated.withMutability .Mut).withExtra tree) := by
      dsimp only [refAllocToMiriV2, alPtr]
      rw [h_pb]
      rw [show refPlainInitBytesV2? [
          AllocByte.init 16 (some 2), AllocByte.init 0 (some 2),
          AllocByte.init 0 (some 2), AllocByte.init 0 (some 2),
          AllocByte.init 0 (some 2), AllocByte.init 0 (some 2),
          AllocByte.init 0 (some 2), AllocByte.init 0 (some 2)] = none from rfl]
      dsimp only
      rw [show ([
          AllocByte.init 16 (some 2), AllocByte.init 0 (some 2),
          AllocByte.init 0 (some 2), AllocByte.init 0 (some 2),
          AllocByte.init 0 (some 2), AllocByte.init 0 (some 2),
          AllocByte.init 0 (some 2), AllocByte.init 0 (some 2)] :
          List AllocByte).length = 8 from rfl]
      rw [show Miri.ABI.Size.ofBytes (UInt64.ofNat 8) = sz8 from rfl, h_try]
      dsimp only [refPopulateAllocBytesV2, Miri.Memory.Allocation.writePointer,
        toMiriMutV2]
      rw [show (Nat.beq 2 2 && Nat.beq 2 2 && Nat.beq 2 2 && Nat.beq 2 2 &&
            Nat.beq 2 2 && Nat.beq 2 2 && Nat.beq 2 2) = true from rfl,
        ite_true_eq, show refExactAllocIdV2 2 = some alloc2IdV2 from rfl]
      dsimp only [Miri.Memory.Allocation.writePointer]
      rw [show Miri.ABI.Size.ofBytes (UInt64.ofNat 0) = Miri.ABI.Size.ZERO
          from rfl,
        show Miri.ABI.Size.ofBytes (UInt64.ofNat
          (refNatOfLeBytesV2 [16, 0, 0, 0, 0, 0, 0, 0])) =
          Miri.ABI.Size.ofBytes 16 from rfl]
      dsimp only [rng8, ptr, sz8] at h_ws
      rw [h_ws]
    let ma := (updated.withMutability .Mut).withExtra tree
    have h_bp (i : Nat) :
        refByteProvAtV2 updated.provenanceMap i =
          if Nat.ble 0 i && Nat.blt i 8 then some 2 else none := by
      dsimp only [refByteProvAtV2]
      rw [h_upm, ← Array.find?_toList]
      dsimp only [List.find?]
      rw [show Miri.ABI.Size.ZERO.bytes.toNat = 0 from rfl]
      cases (Nat.ble 0 i && Nat.blt i 8) <;> rfl
    have h_ma_bsz : ma.byteSize = sz8 := h_ubsz.trans h_bsz
    have h_ma_al : ma.align = ⟨3⟩ := h_ual.trans h_al
    have h_ma_mut : ma.mutability = .Mut := rfl
    have h_ma_gb : ma.getBytesUnchecked rng8 =
        .ok (Array.mk (leBytesOfNat 8 16)) := h_raw_ok
    have h_ma_im : ma.initializationMask = Miri.Memory.InitMask.new sz8 true :=
      h_uim.symm
    have h_ma_pm : ma.provenanceMap = updated.provenanceMap := rfl
    have h_loop :
        refReadAllocBytesLoopV2 ma (Array.mk (leBytesOfNat 8 16)) 0 8 =
          ptrBytes := by
      simp only [refReadAllocBytesLoopV2, h_ma_im, h_ma_pm,
        Miri.Memory.InitMask.lazy_get, h_bp]
      rfl
    have h_ext :
        refExtractOneCallerAllocV2
          { (Miri.Memory.MemoryState.empty : RefMiriMem) with
            live := Array.mk [(alloc2IdV2,
              ({ kind := .machine (), allocation := ma } :
                Miri.Memory.LocalAllocation Miri.Memory.Provenance
                  Miri.TreeBorrows.BorrowTree Unit))] } alPtr =
          alPtr := by
      dsimp only [refExtractOneCallerAllocV2]
      rw [show refExactAllocIdV2 alPtr.allocId = some alloc2IdV2 from rfl]
      dsimp only
      have h_find_arr : (Array.mk [(alloc2IdV2,
          ({ kind := .machine (), allocation := ma } :
            Miri.Memory.LocalAllocation Miri.Memory.Provenance
              Miri.TreeBorrows.BorrowTree Unit))]).find?
          (fun entry => entry.1 == alloc2IdV2) =
          some (alloc2IdV2,
            ({ kind := .machine (), allocation := ma } :
              Miri.Memory.LocalAllocation Miri.Memory.Provenance
                Miri.TreeBorrows.BorrowTree Unit)) := by
        rw [← Array.find?_toList]; rfl
      rw [h_find_arr]
      dsimp only
      rw [h_ma_bsz]
      change (match ma.getBytesUnchecked rng8 with
        | Except.error _ => alPtr | Except.ok raw => _) = alPtr
      rw [h_ma_gb]
      dsimp only [ofMiriMutV2]
      rw [show sz8.bytes.toNat = 8 from rfl, h_ma_mut, h_ma_al, h_loop]
    dsimp only [alPtr, ptrBytes] at h_toMiri h_ext
    dsimp only [Except.map]
    rw [h_toMiri]
    exact congrArg Except.ok h_ext
  · dsimp only [refByteProvAtV2]
    rw [h_p, h_f, ← Array.find?_toList, ← Array.find?_toList]
    rfl

/-- Global impossibility of Profile v2 bidirectional fault equivalence for
`encodeProg` (directly witnessed by Edge 1,
`conservative_edge1_zero_offset_oob_separation`; Edges 2 and 3 independently
provide two further conservative-edge separations). -/
theorem not_biFaultEquivV2_encodeProg :
    ¬ BiFaultEquivV2Bundle encodeProg := by
  intro h_bi
  let ⟨h_ub, _, _, _, h_no_rub⟩ := conservative_edge1_zero_offset_oob_separation
  let ⟨ms, h_rub⟩ := (h_bi.ub_iff _ _).1 h_ub
  exact h_no_rub ms h_rub

private theorem refTyLayoutFitsU64V2_tuple_array_head (elem : MirTy) (len : Nat)
    (rest : List MirTy) :
    refTyLayoutFitsU64V2 (.tuple (.array elem len :: rest)) =
      refTupleLayoutFitsU64V2 0 0 (.array elem len :: rest) := rfl

private theorem refTupleLayoutFitsU64V2_cons (curOff maxPow2 : Nat)
    (ty : MirTy) (rest : List MirTy) :
    refTupleLayoutFitsU64V2 curOff maxPow2 (ty :: rest) =
      (refTyLayoutFitsU64V2 ty &&
        let ld := refLayoutDataForTyV2 ty
        let fPow2 := ld.align.abi.pow2
        let aligned := refAlignUpNat curOff fPow2
        let nextOff := aligned + ld.size.bytes.toNat
        refNatFitsU64V2 aligned && refNatFitsU64V2 nextOff &&
          refTupleLayoutFitsU64V2 nextOff (Nat.max maxPow2 fPow2) rest) := rfl

/-- Regression witness: oversized Profile v2 layouts whose byte size, element
count, or tuple field offsets exceed `UInt64` (`&[u64; 2^61]`, `[(); 2^64]`,
and `([u8; 2^63], [u8; 2^63])`) fail closed via `refTyLayoutFitsU64V2`,
`refCheckedLayoutDataForTyV2`, `refValidateRefInMiriV2`, and `initRefStateV2`
with `.unsupported` before `Miri.ABI.LayoutData` construction, never silently
wrapping `UInt64.ofNat` to `0` (`initStateV2` still rejects `&[u64; 2^61]`
against an empty allocation as `.undefined`). -/
theorem profileV2_oversized_layout_rejected :
    let u64ArrTy := MirTy.array (.int .i64 false) (Nat.pow 2 61)
    let refArrTy := MirTy.ref .shared u64ArrTy
    let zstArrTy := MirTy.array .unit (Nat.pow 2 64)
    let bigHalf := MirTy.array (.int .i8 false) (Nat.pow 2 63)
    let bigTupTy := MirTy.tuple [bigHalf, bigHalf]
    let progArrRef := mkV2Prog {
      identity := "v2_oversized_u64_arr_ref"
      argumentCount := 1
      locals := [.unit, refArrTy]
      basicBlocks := [{
        statements := [.assign ⟨0, []⟩ (.use (.constant ⟨.unit, .zeroSized⟩))]
        terminator := .return_
      }]
    }
    let progZstArr := mkV2Prog {
      identity := "v2_oversized_zst_arr"
      argumentCount := 0
      locals := [zstArrTy]
      basicBlocks := [{
        statements := []
        terminator := .return_
      }]
    }
    let progBigTup := mkV2Prog {
      identity := "v2_oversized_tuple"
      argumentCount := 0
      locals := [bigTupTy]
      basicBlocks := [{
        statements := []
        terminator := .return_
      }]
    }
    let cmEmpty : CallerMemory := ⟨[{
      allocId := 2, alignLog2 := 3, mutability := .shared,
      bytes := [], live := true
    }]⟩
    let qArr : Query := {
      args := [.ptr ⟨some 2, 0, .isize⟩]
      callerMem := cmEmpty
    }
    (refTyLayoutFitsU64V2 u64ArrTy = false) ∧
    (refTyLayoutFitsU64V2 refArrTy = false) ∧
    (refCheckedLayoutDataForTyV2 u64ArrTy = none) ∧
    (refCheckedLayoutDataForTyV2 refArrTy = none) ∧
    (refValidateRefInMiriV2 (Miri.Memory.MemoryState.empty : RefMiriMem)
      .shared u64ArrTy (.ptr ⟨some 2, 0, .isize⟩) = .error .unsupported) ∧
    (initStateV2 progArrRef qArr = .error .undefined) ∧
    (initRefStateV2 (encodeProg progArrRef) qArr 1 = .error .unsupported) ∧
    (refTyLayoutFitsU64V2 zstArrTy = false) ∧
    (refCheckedLayoutDataForTyV2 zstArrTy = none) ∧
    (initRefStateV2 (encodeProg progZstArr) { args := [], callerMem := ⟨[]⟩ } 1 =
      .error .unsupported) ∧
    (refTyLayoutFitsU64V2 bigTupTy = false) ∧
    (refCheckedLayoutDataForTyV2 bigTupTy = none) ∧
    (initRefStateV2 (encodeProg progBigTup) { args := [], callerMem := ⟨[]⟩ } 1 =
      .error .unsupported) := by
  intro u64ArrTy refArrTy zstArrTy bigHalf bigTupTy
    progArrRef progZstArr progBigTup cmEmpty qArr
  have h_half_fit : refTyLayoutFitsU64V2 bigHalf = true := rfl
  have h_half_ld :
      (refLayoutDataForTyV2 bigHalf).size.bytes.toNat = Nat.pow 2 63 := rfl
  have h_half_al : (refLayoutDataForTyV2 bigHalf).align.abi.pow2 = 0 := rfl
  have h_tup_fit : refTyLayoutFitsU64V2 bigTupTy = false := by
    dsimp only [bigTupTy]
    rw [refTyLayoutFitsU64V2_tuple_array_head, refTupleLayoutFitsU64V2_cons]
    dsimp only
    rw [h_half_fit, h_half_al, h_half_ld]
    rw [show refAlignUpNat 0 0 = 0 from rfl, show Nat.max 0 0 = 0 from rfl,
      show 0 + Nat.pow 2 63 = Nat.pow 2 63 from rfl,
      show refNatFitsU64V2 0 = true from rfl,
      show refNatFitsU64V2 (Nat.pow 2 63) = true from rfl]
    simp only [Bool.true_and]
    rw [refTupleLayoutFitsU64V2_cons]
    dsimp only
    rw [h_half_fit, h_half_al, h_half_ld]
    rw [show refAlignUpNat (Nat.pow 2 63) 0 = Nat.pow 2 63 from rfl,
      show Nat.pow 2 63 + Nat.pow 2 63 = Nat.pow 2 64 from rfl,
      show refNatFitsU64V2 (Nat.pow 2 63) = true from rfl,
      show refNatFitsU64V2 (Nat.pow 2 64) = false from rfl]
    simp only [Bool.and_false, Bool.false_and]
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, ?_, h_tup_fit, ?_, ?_⟩
  · let rp := encodeProg progArrRef
    let rbody := @GetElem.getElem _ Nat _ _ _ rp.bodies 0 (by decide)
    have h_fit : refTyLayoutFitsU64V2 refArrTy = false := rfl
    change initRefStateV2 rp qArr 1 = .error .unsupported
    dsimp only [initRefStateV2]
    rw [show (!Nat.beq rp.pointerWidthBits 64 ||
        !Nat.beq rp.mirProfileVersion 2) = false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    rw [show (!refValidCallerMemoryV2 qArr.callerMem) = false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    rw [show Trusted.MirSemantics.getElem? rp.bodies rp.entryDefId =
        some rbody from rfl]
    dsimp only
    rw [show decodeLocalTys rp.types rbody.locals =
        some [.unit, refArrTy] from rfl]
    dsimp only
    rw [show (![.unit, refArrTy].all refTyLayoutFitsU64V2) = true from by
        simp only [List.all_cons, List.all_nil, h_fit, Bool.and_true,
          Bool.and_false, Bool.not_false],
      Bool.or_true, ite_true_eq]
  · let rp := encodeProg progZstArr
    let rbody := @GetElem.getElem _ Nat _ _ _ rp.bodies 0 (by decide)
    have h_fit : refTyLayoutFitsU64V2 zstArrTy = false := rfl
    change initRefStateV2 rp { args := [], callerMem := ⟨[]⟩ } 1 =
      .error .unsupported
    dsimp only [initRefStateV2]
    rw [show (!Nat.beq rp.pointerWidthBits 64 ||
        !Nat.beq rp.mirProfileVersion 2) = false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    rw [show (!refValidCallerMemoryV2 ⟨[]⟩) = false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    rw [show Trusted.MirSemantics.getElem? rp.bodies rp.entryDefId =
        some rbody from rfl]
    dsimp only
    rw [show decodeLocalTys rp.types rbody.locals = some [zstArrTy] from rfl]
    dsimp only
    rw [show (![zstArrTy].all refTyLayoutFitsU64V2) = true from by
        simp only [List.all_cons, List.all_nil, h_fit, Bool.and_true,
          Bool.not_false],
      Bool.or_true, ite_true_eq]
  · dsimp only [refCheckedLayoutDataForTyV2]
    rw [h_tup_fit]
    rfl
  · let rp := encodeProg progBigTup
    let rbody := @GetElem.getElem _ Nat _ _ _ rp.bodies 0 (by decide)
    change initRefStateV2 rp { args := [], callerMem := ⟨[]⟩ } 1 =
      .error .unsupported
    dsimp only [initRefStateV2]
    rw [show (!Nat.beq rp.pointerWidthBits 64 ||
        !Nat.beq rp.mirProfileVersion 2) = false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    rw [show (!refValidCallerMemoryV2 ⟨[]⟩) = false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    rw [show Trusted.MirSemantics.getElem? rp.bodies rp.entryDefId =
        some rbody from rfl]
    dsimp only
    rw [show decodeLocalTys rp.types rbody.locals = some [bigTupTy] from rfl]
    dsimp only
    rw [show (![bigTupTy].all refTyLayoutFitsU64V2) = true from by
        simp only [List.all_cons, List.all_nil, h_tup_fit, Bool.and_true,
          Bool.not_false],
      Bool.or_true, ite_true_eq]

private theorem mulWithOverflow_usize_stride_step
    (scL scStride scOut : Miri.Memory.ScalarInt) (l : Int) (outNat : Nat)
    (h_dl : Miri.Interpreter.IntegerOps.decode
      ⟨scL, ⟨Miri.ABI.Size.ofBytes 8, .usize⟩⟩ = .ok l)
    (h_ds : Miri.Interpreter.IntegerOps.decode
      ⟨scStride, ⟨Miri.ABI.Size.ofBytes 8, .usize⟩⟩ =
      .ok (9223372036854775808 : Int))
    (h_mul : l * (9223372036854775808 : Int) = Int.ofNat outNat)
    (h_noovf : (decide (Int.ofNat outNat < 0) ||
      decide (Int.ofNat outNat ≥ Int.ofNat (Nat.pow 2 128))) = false)
    (h_bv : bvOfInt 128 (Int.ofNat outNat) = BitVec.ofNat 128 outNat)
    (h_tr : Miri.Memory.ScalarInt.truncateFromUInt
      (BitVec.ofNat 128 outNat) (Miri.ABI.Size.ofBytes 8) =
      .ok (scOut, false)) :
    Miri.Interpreter.IntegerOps.binary .MulWithOverflow
      ⟨scL, ⟨Miri.ABI.Size.ofBytes 8, .usize⟩⟩
      ⟨scStride, ⟨Miri.ABI.Size.ofBytes 8, .usize⟩⟩ =
    .ok (.withOverflow scOut false) := by
  have h_p128 : HPow.hPow (2 : Int) 128 = Int.ofNat (Nat.pow 2 128) :=
    (congrArg (fun b : Int => HPow.hPow b 128)
      (show (2 : Int) = ((2 : Nat) : Int) from rfl)).trans
      (Int.natCast_pow 2 128).symm
  dsimp only [Miri.Interpreter.IntegerOps.binary, bind, Bind.bind,
    Except.bind, pure, Pure.pure, Except.pure]
  rw [h_dl, h_ds]
  dsimp only
  rw [show (Miri.MIR.BinOp.MulWithOverflow == Miri.MIR.BinOp.Shl ||
        Miri.MIR.BinOp.MulWithOverflow == Miri.MIR.BinOp.ShlUnchecked ||
        Miri.MIR.BinOp.MulWithOverflow == Miri.MIR.BinOp.Shr ||
        Miri.MIR.BinOp.MulWithOverflow == Miri.MIR.BinOp.ShrUnchecked) =
      false from rfl]
  simp only [Bool.false_eq_true, ite_false]
  rw [show ((⟨Miri.ABI.Size.ofBytes 8, Miri.MIR.IntegerKind.usize⟩ :
        Miri.Interpreter.IntegerType) !=
      ⟨Miri.ABI.Size.ofBytes 8, Miri.MIR.IntegerKind.usize⟩) = false from rfl]
  simp only [Bool.false_eq_true, ite_false]
  change bind
    ((Miri.Memory.ScalarInt.truncateFromUInt
        (BitVec.ofInt 128 (l * (9223372036854775808 : Int)))
        (Miri.ABI.Size.ofBytes 8)).mapError
      Miri.Interpreter.IntegerOpError.scalar)
    (fun (value, lossy) =>
      if ((decide (l * (9223372036854775808 : Int) < 0) ||
            decide (l * (9223372036854775808 : Int) ≥
              HPow.hPow (2 : Int) 128)) ||
          lossy) && Miri.MIR.BinOp.MulWithOverflow.isUnchecked then
        throw (Miri.Interpreter.IntegerOpError.undefinedBehavior
          (.arithmeticOverflow .MulWithOverflow))
      else
        pure (if Miri.MIR.BinOp.MulWithOverflow.isOverflowing then
          Miri.Interpreter.IntegerResult.withOverflow value
            ((decide (l * (9223372036854775808 : Int) < 0) ||
              decide (l * (9223372036854775808 : Int) ≥
                HPow.hPow (2 : Int) 128)) ||
              lossy)
        else Miri.Interpreter.IntegerResult.scalar value)) =
    .ok (.withOverflow scOut false)
  simp only [h_mul, h_p128, h_noovf, bitVec_ofInt_eq, h_bv, h_tr]
  rfl

private theorem refValidateRefInMiriV2_neverArr_dangling (mem : RefMiriMem)
    (n : Nat) (uninh : Bool) (expected : Except FaultKind Unit)
    (h_fit : refTyLayoutFitsU64V2 (MirTy.array .never n) = true)
    (h_sz : (refLayoutDataForTyV2 (MirTy.array .never n)).size.bytes.toNat =
      0)
    (h_pow : (refLayoutDataForTyV2 (MirTy.array .never n)).align.abi.pow2 =
      0)
    (h_un : (refLayoutDataForTyV2 (MirTy.array .never n)).uninhabited =
      uninh)
    (h_exp : (if uninh then .error .undefined else .ok ()) = expected) :
    refValidateRefInMiriV2 mem .shared (MirTy.array .never n)
        (.ptr ⟨none, 1, .isize⟩) = expected := by
  dsimp only [refValidateRefInMiriV2]
  rw [show refIsSupportedPointeeTyV2 (MirTy.array .never n) = true from rfl,
    h_fit]
  simp only [Bool.not_true, Bool.false_or, Bool.false_eq_true, ite_false]
  rw [h_sz, h_pow, h_un]
  rw [show (Nat.beq (1 : UInt64).toNat 0 || Nat.blt 0 0 ||
      !Nat.beq (Nat.mod (1 : UInt64).toNat (Nat.pow 2 0)) 0) = false from rfl]
  simp only [Bool.false_or]
  exact h_exp

private theorem refExecPtrAddV2_eval_step
    (types : List MirTy) (abi : Miri.ABI.FnAbi TyId)
    (arg0 arg1 : Miri.Interpreter.OpTy Miri.Memory.Provenance)
    (dest : Miri.Interpreter.RuntimePlace Miri.Memory.Provenance)
    (st : RefMiriState) (mut_ : Trusted.MirAst.Mutability) (pt : MirTy)
    (imm0 imm1 : Miri.Interpreter.RvalueImmTy Miri.Memory.Provenance)
    (h_sz : ((Array.mk [arg0, arg1]).size != 2 ||
        arg0.layout.ty != abi.ret.layout.ty ||
        dest.layout.ty != abi.ret.layout.ty) = false)
    (h_rt0 : resolveTy types abi.ret.layout.ty = some (.rawPtr mut_ pt))
    (h_rt1 : resolveTy types arg1.layout.ty = some (.int .isize false))
    (h_uns : (refIsUnsizedTyV2 pt || !refIsSupportedPointeeTyV2 pt ||
        !refTyLayoutFitsU64V2 pt) = false)
    (h_ri0 : Miri.Interpreter.PlaceMachine.readImmediate
        (refAccessConfigV2 types) arg0 st = .ok imm0 st)
    (h_ri1 : Miri.Interpreter.PlaceMachine.readImmediate
        (refAccessConfigV2 types) arg1 st = .ok imm1 st) :
    refExecPtrAddV2 types abi (Array.mk [arg0, arg1]) dest st =
      let ptLd := refLayoutDataForTyV2 pt
      let strideRes := Miri.Memory.Scalar.fromUInt
        (BitVec.ofNat 128 ptLd.size.bytes.toNat) imm1.layout.layout.size
      match imm0.imm.toScalar, strideRes with
      | .ok ptrSc, .ok strideSc =>
        match ptrSc.toPointer refRuntimeLayoutV2.base with
        | .error e =>
          .error (Miri.Interpreter.ScalarOps.scalarError e) st
        | .ok ptr =>
          match Miri.Interpreter.ExecutionScalar.integerBinary
              (refScalarLeavesV2 types) 0 .MulWithOverflow
              imm1 ⟨.scalar strideSc, imm1.layout⟩ st with
          | .error e st3 => .error e st3
          | .ok mult st3 =>
            match mult.imm.toScalarPair with
            | .error e =>
              .error (Miri.Interpreter.ScalarOps.immediateError e) st3
            | .ok (deltaSc, ovSc) =>
              match ovSc.toBool,
                  deltaSc.toTargetIsize
                    refPointerArithmetic.pointerSize with
              | .ok true, _ =>
                .error (.undefinedBehavior "PointerArithOverflow") st3
              | .ok false, .ok offset =>
                if offset.toInt < 0 then
                  .error (.undefinedBehavior "PointerArithOverflow") st3
                else
                  match refOffsetPtrSignedV2 st3.machine.memory
                      ptr offset with
                  | .error e => .error e st3
                  | .ok resSc =>
                    match Miri.Interpreter.writePlaceImmediate
                        (refPlaceProjectionHooksV2 types).place 0
                        (.scalar resSc) dest st3 with
                    | .error e st4 => .error e st4
                    | .ok () st4 => .ok .NeedsReturn st4
              | _, _ => .error (.unsupported "ptrAdd mul decode") st3
      | _, _ => .error (.unsupported "ptrAdd scalar decode") st := by
  dsimp only [refExecPtrAddV2, EStateM]
  rw [show (Array.mk [arg0, arg1])[0]? = some arg0 from rfl,
    show (Array.mk [arg0, arg1])[1]? = some arg1 from rfl]
  dsimp only [EStateM]
  rw [h_sz]
  simp only [Bool.false_eq_true, ite_false]
  rw [h_rt0, h_rt1]
  dsimp only [EStateM]
  rw [h_uns]
  simp only [Bool.false_eq_true, ite_false]
  rw [h_ri0]
  dsimp only [EStateM]
  rw [h_ri1]
  rfl

private theorem executionScalar_integerBinary_mul_usize
    (types : List MirTy) (layData : Miri.ABI.LayoutData)
    (ovfLay : Miri.Interpreter.LocalLayout)
    (scL scR scOut : Miri.Memory.ScalarInt) (st : RefMiriState)
    (bitsL bitsR : BitVec 128)
    (h_cls : (refScalarLeavesV2 types).classify 0 1 st =
      .ok (.integer .usize) st)
    (h_ovf : (refScalarLeavesV2 types).overflowLayout 0 ⟨1, layData⟩ st =
      .ok ovfLay st)
    (h_bl : scL.toBits layData.size = .ok bitsL)
    (h_br : scR.toBits layData.size = .ok bitsR)
    (h_mul : Miri.Interpreter.IntegerOps.binary .MulWithOverflow
      ⟨scL, ⟨layData.size, .usize⟩⟩
      ⟨scR, ⟨layData.size, .usize⟩⟩ = .ok (.withOverflow scOut false)) :
    Miri.Interpreter.ExecutionScalar.integerBinary (P := Miri.Memory.Provenance)
        (refScalarLeavesV2 types) 0 .MulWithOverflow
        ⟨.scalar (.fromScalarInt (Prov := Miri.Memory.Provenance) scL),
          ⟨1, layData⟩⟩
        ⟨.scalar (.fromScalarInt (Prov := Miri.Memory.Provenance) scR),
          ⟨1, layData⟩⟩ st =
      .ok ⟨.scalarPair (.fromScalarInt scOut) (.fromBool false), ovfLay⟩
        st := by
  dsimp only [Miri.Interpreter.ExecutionScalar.integerBinary, bind,
    Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_cls]
  dsimp only [EStateM.bind]
  rw [h_cls]
  dsimp only
  let liftStep {α : Type} (ex : Except Miri.Interpreter.StepError α) :
      Miri.Interpreter.RvalueM RefMiriState α :=
    match ex with | .ok v => pure v | .error e => throw e
  let intStep (sc : Miri.Memory.ScalarInt) :
      Miri.Interpreter.RvalueM RefMiriState Miri.Interpreter.IntegerValue :=
    EStateM.bind
      (liftStep ((sc.toBits layData.size).mapError
        Miri.Interpreter.ScalarOps.scalarIntError))
      (fun _ => pure ⟨sc, ⟨layData.size, .usize⟩⟩)
  change (EStateM.bind (intStep scL) (fun leftValue =>
    EStateM.bind (intStep scR) (fun rightValue =>
      EStateM.bind (liftStep ((Miri.Interpreter.IntegerOps.binary
          .MulWithOverflow leftValue rightValue).mapError
        Miri.Interpreter.ScalarOps.integerError))
      (fun result => Miri.Interpreter.ExecutionScalar.finish
        (refScalarLeavesV2 types) 0 ⟨1, layData⟩ result)))) st =
    .ok ⟨.scalarPair (.fromScalarInt scOut) (.fromBool false), ovfLay⟩ st
  dsimp only [intStep]
  rw [h_bl, h_br]
  dsimp only [liftStep, Except.mapError, bind, Bind.bind, EStateM.bind,
    pure, Pure.pure, EStateM.pure]
  rw [h_mul]
  dsimp only [liftStep, Except.mapError, Miri.Interpreter.ExecutionScalar.finish,
    bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_ovf]

/-- Regression witness:
1. Uninhabited aggregates (`[!; N]` for `N >= 1` and tuples containing `!`)
   propagate `uninhabited = true` and `variants = .Empty` in
   `refLayoutDataForTyV2` and `opsemInhabited = .ok false` in `refValHooksV2`,
   rejecting `&[!; 1]` (even from a non-null dangling pointer) with `.undefined`
   in `refValidateRefInMiriV2` and `initRefStateV2` (matching `initStateV2`),
   while `[!; 0]` remains inhabited.
2. `refExecPtrAddV2` encodes element stride via `Scalar.fromUInt`, accepting
   zero-count `ptrAdd` on `[u8; 2^63]` cleanly (`NeedsReturn`, matching
   `evalStepV2`) and rejecting count `1` as `PointerArithOverflow` (`.ub`,
   matching `evalStepV2` `.undefined`). -/
theorem profileV2_uninhabited_and_large_ptrAdd_spec :
    let neverArr1 := MirTy.array .never 1
    let neverArr0 := MirTy.array .never 0
    let neverTup := MirTy.tuple [.never, .int .i8 false]
    let progNeverRef := mkV2Prog {
      identity := "v2_uninhabited_never_arr_ref"
      argumentCount := 1
      locals := [.unit, .ref .shared neverArr1]
      basicBlocks := [{
        statements := [.assign ⟨0, []⟩ (.use (.constant ⟨.unit, .zeroSized⟩))]
        terminator := .return_
      }]
    }
    let qDangling : Query := { args := [.ptr ⟨none, 1, .isize⟩], callerMem := ⟨[]⟩ }
    let emptyMem : RefMiriMem := Miri.Memory.MemoryState.empty
    let dummyBody : RefBody := {
      argumentCount := 0, locals := [0],
      basicBlocks := [{ statements := [], terminator := .return_ }]
    }
    let stDummy : RefMiriState :=
      mkRefMiriState (mkRefMiriFrameV2 [] 0 dummyBody 0 0 []
        ⟨retMemPlaceV2, refLocalLayoutForTyV2 [] .unit⟩)
        emptyMem refInitControl ⟨[]⟩
    let halfArrTy := MirTy.array (.int .i8 false) (Nat.pow 2 63)
    let rawHalfTy := MirTy.rawPtr .shared halfArrTy
    let usizeTy := MirTy.int .isize false
    let ptrTypes : List MirTy := [rawHalfTy, usizeTy, halfArrTy]
    let rawHalfLay := refLocalLayoutForTyV2 ptrTypes rawHalfTy
    let usizeLay := refLocalLayoutForTyV2 ptrTypes usizeTy
    let ptrAbi : Miri.ABI.FnAbi TyId := ⟨
      Array.mk [⟨rawHalfLay, .Direct Miri.ABI.ArgAttributes.new⟩,
        ⟨usizeLay, .Direct Miri.ABI.ArgAttributes.new⟩],
      ⟨rawHalfLay, .Direct Miri.ABI.ArgAttributes.new⟩,
      false, 2, .Rust, false⟩
    let ptr0 : Miri.Memory.Pointer Miri.Memory.Provenance :=
      ⟨Miri.ABI.Size.ZERO, .concrete alloc2IdV2 Miri.Memory.BorTag.one⟩
    let ptrImm0 : Miri.Interpreter.Immediate Miri.Memory.Provenance :=
      .scalar (.fromPointer refRuntimeLayoutV2.base ptr0)
    let opPtr0 : Miri.Interpreter.OpTy Miri.Memory.Provenance :=
      ⟨.immediate ptrImm0, rawHalfLay⟩
    let opZero : Miri.Interpreter.OpTy Miri.Memory.Provenance :=
      ⟨.immediate (.scalar (.fromScalarInt
        (Miri.Memory.ScalarInt.ofUInt64 0))), usizeLay⟩
    let opOne : Miri.Interpreter.OpTy Miri.Memory.Provenance :=
      ⟨.immediate (.scalar (.fromScalarInt
        (Miri.Memory.ScalarInt.ofUInt64 1))), usizeLay⟩
    let pFrame0 := mkRefMiriFrameV2 ptrTypes 0 dummyBody 0 0
      [⟨.live (.immediate .uninit), some rawHalfLay⟩]
      ⟨retMemPlaceV2, rawHalfLay⟩
    let pFrame0' := { pFrame0 with
      locals := Array.mk [⟨.live (.immediate ptrImm0), some rawHalfLay⟩] }
    let pSt0 : RefMiriState :=
      mkRefMiriState pFrame0 emptyMem refInitControl ⟨[]⟩
    let pSt0' : RefMiriState := { pSt0 with stack := ⟨Array.mk [pFrame0']⟩ }
    let pDest : Miri.Interpreter.RuntimePlace Miri.Memory.Provenance :=
      ⟨.local 0 0 none pFrame0.localsIdentity, rawHalfLay⟩
    let mkHalfProg (cnt : Nat) : Program := mkV2Prog {
      identity := "v2_half_arr_ptr_add"
      argumentCount := 1
      locals := [rawHalfTy, rawHalfTy]
      basicBlocks := [{
        statements := []
        terminator := .coreCall (.ptrAdd .shared halfArrTy)
          [.copy ⟨1, []⟩,
           .constant ⟨usizeTy, .scalar (BitVec.ofNat 128 cnt)⟩]
          ⟨0, []⟩ (some 1) .unreachable
      }, {
        statements := []
        terminator := .return_
      }]
    }
    let qHalf : Query := {
      args := [.ptr ⟨some 2, 0, .isize⟩]
      callerMem := ⟨[{
        allocId := 2, alignLog2 := 0, mutability := .shared,
        bytes := [], live := true
      }]⟩
    }
    ((refLayoutDataForTyV2 neverArr1).uninhabited = true) ∧
    ((refLayoutDataForTyV2 neverArr1).variants = .Empty) ∧
    ((refLayoutDataForTyV2 neverArr0).uninhabited = false) ∧
    ((refLayoutDataForTyV2 neverArr0).variants = .Single 0) ∧
    ((refLayoutDataForTyV2 neverTup).uninhabited = true) ∧
    ((refLayoutDataForTyV2 neverTup).variants = .Empty) ∧
    ((refValHooksV2 [neverArr1]).opsemInhabited 0 0 stDummy = .ok false stDummy) ∧
    ((refValHooksV2 [neverTup]).opsemInhabited 0 0 stDummy = .ok false stDummy) ∧
    (refValidateRefInMiriV2 emptyMem .shared neverArr1
      (.ptr ⟨none, 1, .isize⟩) = .error .undefined) ∧
    (refValidateRefInMiriV2 emptyMem .shared neverArr0
      (.ptr ⟨none, 1, .isize⟩) = .ok ()) ∧
    (initStateV2 progNeverRef qDangling = .error .undefined) ∧
    (initRefStateV2 (encodeProg progNeverRef) qDangling 1 = .error .undefined) ∧
    (refFnAbiOfCoreCallV2 ptrTypes
      ⟨.Item (refCoreCallDefId ptrTypes (.ptrAdd .shared halfArrTy)),
        Array.empty⟩ = .ok ptrAbi) ∧
    (WellFormedV2 (mkHalfProg 0) qHalf) ∧
    (BehaviorV2 (mkHalfProg 0) qHalf
      (.returned ⟨.ptr ⟨some 2, 0, .isize⟩, qHalf.callerMem⟩)) ∧
    (ReachesResultV2 (mkHalfProg 1) qHalf (.fault .undefined)) ∧
    (refExecPtrAddV2 ptrTypes ptrAbi (Array.mk [opPtr0, opZero]) pDest pSt0 =
      .ok .NeedsReturn pSt0') ∧
    (refExecPtrAddV2 ptrTypes ptrAbi (Array.mk [opPtr0, opOne]) pDest pSt0 =
      .error (.undefinedBehavior "PointerArithOverflow") pSt0) := by
  intro neverArr1 neverArr0 neverTup progNeverRef qDangling emptyMem dummyBody
    stDummy halfArrTy rawHalfTy usizeTy ptrTypes rawHalfLay usizeLay ptrAbi
    ptr0 ptrImm0 opPtr0 opZero opOne pFrame0 pFrame0' pSt0 pSt0' pDest
    mkHalfProg qHalf
  have h_half_fit : refTyLayoutFitsU64V2 halfArrTy = true := rfl
  have h_half_sz :
      (refLayoutDataForTyV2 halfArrTy).size.bytes.toNat = Nat.pow 2 63 := rfl
  have h_usize_sz : usizeLay.layout.size = Miri.ABI.Size.ofBytes 8 := rfl
  let scZero := Miri.Memory.ScalarInt.ofUInt64 0
  let scOne := Miri.Memory.ScalarInt.ofUInt64 1
  let scStride := Miri.Memory.ScalarInt.ofUInt64 (UInt64.ofNat (Nat.pow 2 63))
  have h_p63 : HPow.hPow (2 : Int) 63 = Int.ofNat (Nat.pow 2 63) :=
    (congrArg (fun b : Int => HPow.hPow b 63)
      (show (2 : Int) = ((2 : Nat) : Int) from rfl)).trans
      (Int.natCast_pow 2 63).symm
  have h_stride :
      Miri.Memory.Scalar.fromUInt (Prov := Miri.Memory.Provenance)
          (BitVec.ofNat 128 (Nat.pow 2 63)) (Miri.ABI.Size.ofBytes 8) =
        .ok (.fromScalarInt scStride) := rfl
  have h_mul0 :
      Miri.Interpreter.IntegerOps.binary .MulWithOverflow
        ⟨scZero, ⟨Miri.ABI.Size.ofBytes 8, .usize⟩⟩
        ⟨scStride, ⟨Miri.ABI.Size.ofBytes 8, .usize⟩⟩ =
      .ok (.withOverflow scZero false) :=
    mulWithOverflow_usize_stride_step scZero scStride scZero 0 0 rfl rfl rfl
      (by decide) rfl rfl
  have h_mul1 :
      Miri.Interpreter.IntegerOps.binary .MulWithOverflow
        ⟨scOne, ⟨Miri.ABI.Size.ofBytes 8, .usize⟩⟩
        ⟨scStride, ⟨Miri.ABI.Size.ofBytes 8, .usize⟩⟩ =
      .ok (.withOverflow scStride false) :=
    mulWithOverflow_usize_stride_step scOne scStride scStride 1
      9223372036854775808 rfl rfl rfl (by decide) rfl rfl
  have h_toIsize0 :
      (Miri.Memory.Scalar.fromScalarInt
          (Prov := Miri.Memory.Provenance) scZero).toTargetIsize
        refPointerArithmetic.pointerSize = .ok 0 := rfl
  let off1 : Int64 := Int64.ofInt (Neg.neg (9223372036854775808 : Int))
  have h_tb1 :
      (Miri.Memory.Scalar.fromScalarInt
          (Prov := Miri.Memory.Provenance) scStride).toBits
        refPointerArithmetic.pointerSize =
        .ok (BitVec.ofNat 128 9223372036854775808) := rfl
  have h_toIsize1 :
      (Miri.Memory.Scalar.fromScalarInt
          (Prov := Miri.Memory.Provenance) scStride).toTargetIsize
        refPointerArithmetic.pointerSize = .ok off1 := by
    dsimp only [Miri.Memory.Scalar.toTargetIsize, Miri.Memory.Scalar.toInt,
      bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
    rw [h_tb1]
    dsimp only
    rw [show refPointerArithmetic.pointerSize = toMiriSize .isize from rfl,
      size_signExtend_eq .isize,
      show signExtendBits .isize (BitVec.ofNat 128 9223372036854775808) =
        Neg.neg (9223372036854775808 : Int) from rfl]
    dsimp only [Except.mapError]
    rw [h_p63,
      show (decide (Neg.neg (9223372036854775808 : Int) <
            Neg.neg (Int.ofNat (Nat.pow 2 63))) ||
          decide (Neg.neg (9223372036854775808 : Int) ≥
            Int.ofNat (Nat.pow 2 63))) = false from by decide]
    rfl
  have h_neg1 : off1.toInt < 0 := by decide
  have h_half0 :=
    Anneal.MirWp.spec_and_behaviorV2_of_exec_eq (p := mkHalfProg 0)
      (q := qHalf) (fuel := 3)
      (out := .returned ⟨.ptr ⟨some 2, 0, .isize⟩, qHalf.callerMem⟩) rfl
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    refValidateRefInMiriV2_neverArr_dangling emptyMem 1 true
      (.error .undefined) rfl rfl rfl rfl rfl,
    refValidateRefInMiriV2_neverArr_dangling emptyMem 0 false
      (.ok ()) rfl rfl rfl rfl rfl,
    rfl, ?_, rfl, h_half0.1, h_half0.2.1, ?_, ?_, ?_⟩
  · let rp := encodeProg progNeverRef
    let rbody := @GetElem.getElem _ Nat _ _ _ rp.bodies 0 (by decide)
    let unitLay := refLocalLayoutForTyV2 rp.types .unit
    let ⟨rawRet, h_raw, _⟩ :=
      refTryNew_spec_v2 Miri.ABI.Size.ZERO Miri.ABI.Align.ONE 1 rfl rfl
    have h_refs : refRefsValidInMiriListV2 emptyMem [.ref .shared neverArr1]
        qDangling.args = false := by
      dsimp only [refRefsValidInMiriListV2, refRefsValidInMiriV2, qDangling,
        neverArr1]
      rw [refValidateRefInMiriV2_neverArr_dangling emptyMem 1 true
        (.error .undefined) rfl rfl rfl rfl rfl]
      rfl
    change initRefStateV2 rp qDangling 1 = .error .undefined
    dsimp only [initRefStateV2]
    rw [show (!Nat.beq rp.pointerWidthBits 64 ||
        !Nat.beq rp.mirProfileVersion 2) = false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    rw [show (!refValidCallerMemoryV2 qDangling.callerMem) = false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    rw [show Trusted.MirSemantics.getElem? rp.bodies rp.entryDefId =
        some rbody from rfl]
    dsimp only
    rw [show decodeLocalTys rp.types rbody.locals =
        some [.unit, .ref .shared neverArr1] from rfl]
    dsimp only
    rw [show (rbody.basicBlocks.isEmpty ||
        !Nat.blt rbody.argumentCount ([.unit, .ref .shared neverArr1] :
          List MirTy).length ||
        !refStorageAnnotationsInBounds rbody ||
        !refDiscriminantTypesValid [.unit, .ref .shared neverArr1] rbody ||
        !refCastTypesValid rp.types [.unit, .ref .shared neverArr1] rbody ||
        ![.unit, .ref .shared neverArr1].all refIsSupportedLocalTyV2 ||
        ![.unit, .ref .shared neverArr1].all refTyLayoutFitsU64V2) =
        false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    rw [show (!checkRefArgsMatchV2 qDangling.args
          (([.unit, .ref .shared neverArr1].drop 1).take
            rbody.argumentCount) ||
        !refValListAllocIdsFitU64V2 qDangling.args) = false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    rw [show Trusted.MirSemantics.getElem?
        ([MirTy.unit, MirTy.ref .shared neverArr1] : List MirTy) 0 =
        (some MirTy.unit : Option MirTy) from rfl]
    dsimp only
    dsimp only [refInitCallerMemoryV2, refOwnLayoutFitsU64V2]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    rw [show unitLay.layout.size = Miri.ABI.Size.ZERO from rfl,
      show unitLay.layout.align.abi = Miri.ABI.Align.ONE from rfl, h_raw]
    dsimp only [qDangling, refInsertCallerAllocsV2]
    rw [show List.take rbody.argumentCount
        (List.drop 1 ([MirTy.unit, MirTy.ref .shared neverArr1] : List MirTy)) =
        ([MirTy.ref .shared neverArr1] : List MirTy) from rfl]
    dsimp only [emptyMem, qDangling] at h_refs
    simp only [h_refs, Bool.false_and, Bool.not_false, ite_true]
  · exact (fault_and_exclusive_of_execFaultV2 (p := mkHalfProg 1) (q := qHalf)
      (fuel := 1) (expected := .undefined) rfl).1
  · let rpDummy : RefProg := {
      bodies := [], entryDefId := 0, types := ptrTypes,
      pointerWidthBits := 64, mirProfileVersion := 2, scope := .unit,
      overflowChecks := false, panicStrategy := .abort,
      hasLocalPanicHandler := false
    }
    have h_val : Miri.Interpreter.ValidityVisitor.validatePlace
        (refValHooksV2 ptrTypes) 0 16 pDest true true pSt0' = .ok () pSt0' :=
      rawPtr_validate_v2 ptrTypes pSt0' 0 halfArrTy .shared ptr0 pFrame0'
        rfl rfl rfl rfl rfl
    have h_wr : Miri.Interpreter.writePlaceImmediate
        (refPlaceProjectionHooksV2 ptrTypes).place 0 ptrImm0 pDest pSt0 =
        .ok () pSt0' := by
      have h_w := writeLocalImmediate_direct_v2 rpDummy pSt0 pFrame0 0 .uninit
        ptrImm0 rawHalfLay pFrame0' rfl rfl rfl rfl rfl h_val
      change (Miri.Interpreter.ExecutionMachine.rvalueHooks
        (refExecutionConfigV2 rpDummy) refLimitsV2).writeImmediate
        0 ptrImm0 pDest pSt0 = .ok () pSt0'
      exact h_w
    have h_uns : (refIsUnsizedTyV2 halfArrTy ||
        !refIsSupportedPointeeTyV2 halfArrTy ||
        !refTyLayoutFitsU64V2 halfArrTy) = false := by
      simp only [h_half_fit, Bool.not_true]
      rfl
    rw [refExecPtrAddV2_eval_step ptrTypes ptrAbi opPtr0 opZero pDest pSt0
      .shared halfArrTy ⟨ptrImm0, rawHalfLay⟩
      ⟨.scalar (.fromScalarInt scZero), usizeLay⟩ rfl rfl rfl h_uns rfl rfl]
    dsimp only
    rw [h_half_sz, h_usize_sz, h_stride,
      show ptrImm0.toScalar = .ok (.fromPointer refRuntimeLayoutV2.base ptr0)
        from rfl]
    dsimp only
    rw [show (Miri.Memory.Scalar.fromPointer refRuntimeLayoutV2.base ptr0).toPointer
        refRuntimeLayoutV2.base = .ok ptr0.withOptionalProvenance from rfl]
    dsimp only
    have h_ib0 : Miri.Interpreter.ExecutionScalar.integerBinary
        (refScalarLeavesV2 ptrTypes) 0 .MulWithOverflow
        ⟨.scalar (.fromScalarInt scZero), usizeLay⟩
        ⟨.scalar (.fromScalarInt scStride), usizeLay⟩ pSt0 =
        .ok ⟨.scalarPair (.fromScalarInt scZero) (.fromBool false),
          refLocalLayoutForTyV2 ptrTypes (.tuple [usizeTy, .bool])⟩ pSt0 :=
      executionScalar_integerBinary_mul_usize ptrTypes usizeLay.layout
        (refLocalLayoutForTyV2 ptrTypes (.tuple [usizeTy, .bool]))
        scZero scStride scZero pSt0 0 (BitVec.ofNat 128 9223372036854775808)
        rfl rfl rfl rfl h_mul0
    rw [h_ib0]
    dsimp only
    rw [show (Miri.Interpreter.Immediate.scalarPair (.fromScalarInt scZero)
        (.fromBool false)).toScalarPair =
        .ok (.fromScalarInt scZero, .fromBool false) from rfl]
    dsimp only
    rw [show (Miri.Memory.Scalar.fromBool false).toBool = .ok false from rfl,
      h_toIsize0]
    dsimp only
    rw [ite_eq_right (show ¬((0 : Int64).toInt < 0) from by decide)]
    have h_off0 :
        refOffsetPtrSignedV2 pSt0.machine.memory
          ptr0.withOptionalProvenance 0 =
        .ok (.fromPointer refRuntimeLayoutV2.base ptr0) := by
      dsimp only [refOffsetPtrSignedV2]
      rw [ite_eq_left (show ((0 : Int64) == 0) = true from rfl)]
      dsimp only
      rw [pointer_wrappingSignedOffset_zero_v2]
      rfl
    rw [h_off0]
    dsimp only
    exact congrArg (fun r : RefMiriRes Unit =>
      (match r with
      | .error e st4 => EStateM.Result.error e st4
      | .ok () st4 =>
        EStateM.Result.ok Miri.Interpreter.ForeignItems.EmulateItemResult.NeedsReturn st4 :
          RefMiriRes Miri.Interpreter.ForeignItems.EmulateItemResult))
      h_wr
  · have h_uns : (refIsUnsizedTyV2 halfArrTy ||
        !refIsSupportedPointeeTyV2 halfArrTy ||
        !refTyLayoutFitsU64V2 halfArrTy) = false := by
      simp only [h_half_fit, Bool.not_true]
      rfl
    rw [refExecPtrAddV2_eval_step ptrTypes ptrAbi opPtr0 opOne pDest pSt0
      .shared halfArrTy ⟨ptrImm0, rawHalfLay⟩
      ⟨.scalar (.fromScalarInt scOne), usizeLay⟩ rfl rfl rfl h_uns rfl rfl]
    dsimp only
    rw [h_half_sz, h_usize_sz, h_stride,
      show ptrImm0.toScalar = .ok (.fromPointer refRuntimeLayoutV2.base ptr0)
        from rfl]
    dsimp only
    rw [show (Miri.Memory.Scalar.fromPointer refRuntimeLayoutV2.base ptr0).toPointer
        refRuntimeLayoutV2.base = .ok ptr0.withOptionalProvenance from rfl]
    dsimp only
    have h_ib1 : Miri.Interpreter.ExecutionScalar.integerBinary
        (refScalarLeavesV2 ptrTypes) 0 .MulWithOverflow
        ⟨.scalar (.fromScalarInt scOne), usizeLay⟩
        ⟨.scalar (.fromScalarInt scStride), usizeLay⟩ pSt0 =
        .ok ⟨.scalarPair (.fromScalarInt scStride) (.fromBool false),
          refLocalLayoutForTyV2 ptrTypes (.tuple [usizeTy, .bool])⟩ pSt0 :=
      executionScalar_integerBinary_mul_usize ptrTypes usizeLay.layout
        (refLocalLayoutForTyV2 ptrTypes (.tuple [usizeTy, .bool]))
        scOne scStride scStride pSt0 1 (BitVec.ofNat 128 9223372036854775808)
        rfl rfl rfl rfl h_mul1
    rw [h_ib1]
    dsimp only
    rw [show (Miri.Interpreter.Immediate.scalarPair (.fromScalarInt scStride)
        (.fromBool false)).toScalarPair =
        .ok (.fromScalarInt scStride, .fromBool false) from rfl]
    dsimp only
    rw [show (Miri.Memory.Scalar.fromBool false).toBool = .ok false from rfl,
      h_toIsize1]
    dsimp only
    exact ite_eq_left h_neg1

/-- Bridge lifting an entry-reference check failure on `mem0` back to
caller-only memory inside `refInitCallerMemoryV2`. -/
theorem refInitCallerMemoryV2_withArgs_err_of_invalidRefs
    (types : List MirTy) (cm : CallerMemory) (retTy : MirTy)
    (paramTys : List MirTy) (args : List Val) (mem0 : RefMiriMem)
    (retPlace : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance)
    (h_icm : refInitCallerMemoryV2 types cm retTy = .ok (mem0, retPlace))
    (h_refs : refRefsValidInMiriListV2 mem0 paramTys args = false)
    (extraMax : Trusted.MirAst.AllocId) (extraHasOne : Bool) :
    refInitCallerMemoryV2 types cm retTy
      (fun memCaller =>
        refRefsValidInMiriListV2 memCaller paramTys args &&
          refSpansPairwiseDisjointV2 (refAccessSpansListV2 paramTys args))
      extraMax extraHasOne = .error .undefined := by
  dsimp only [refInitCallerMemoryV2] at h_icm
  dsimp only [refInitCallerMemoryV2]
  cases h_fit : refOwnLayoutFitsU64V2 retTy with
  | false =>
    rw [h_fit] at h_icm
    simp only [Bool.not_false, ite_true] at h_icm
    cases h_icm
  | true =>
    simp only [h_fit, Bool.not_true, Bool.false_eq_true, ite_false] at h_icm
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    cases h_try : Miri.Memory.Allocation.tryNew (Prov := Miri.Memory.Provenance)
        (refLocalLayoutForTyV2 types retTy).layout.size
        (refLocalLayoutForTyV2 types retTy).layout.align.abi .Uninit
        (fun n _ => some (Array.replicate n.bytes.toNat 0)) with
    | error _ => rw [h_try] at h_icm; cases h_icm
    | ok rawRet =>
      rw [h_try] at h_icm
      dsimp only at h_icm; dsimp only
      cases h_ins : refInsertCallerAllocsV2 Miri.Memory.MemoryState.empty
          Array.empty cm.allocations with
      | error _ => rw [h_ins] at h_icm; cases h_icm
      | ok p1 =>
        rw [h_ins] at h_icm
        dsimp only at h_icm; dsimp only
        have h_max0 : Nat.max (Nat.max (refMaxAllocIdV2 cm.allocations)
              (refMaxAllocBytesProvIdV2 cm.allocations)) 0 =
            Nat.max (refMaxAllocIdV2 cm.allocations)
              (refMaxAllocBytesProvIdV2 cm.allocations) := Nat.max_zero _
        have h_one0 : (refHasAllocIdV2 1 cm.allocations ||
              refAllocBytesHaveProvIdV2 1 cm.allocations || false) =
            (refHasAllocIdV2 1 cm.allocations ||
              refAllocBytesHaveProvIdV2 1 cm.allocations) := Bool.or_false _
        rw [h_max0, h_one0] at h_icm
        cases h_ex : refExactAllocIdV2 (if (refHasAllocIdV2 1 cm.allocations ||
              refAllocBytesHaveProvIdV2 1 cm.allocations) then
              Nat.max (refMaxAllocIdV2 cm.allocations)
                (refMaxAllocBytesProvIdV2 cm.allocations) + 1
            else 1) with
        | none => rw [h_ex] at h_icm; cases h_icm
        | some retId =>
          rw [h_ex] at h_icm
          dsimp only at h_icm
          cases h_nx : !Nat.beq (UInt64.ofNat (if (refHasAllocIdV2 1 cm.allocations ||
                refAllocBytesHaveProvIdV2 1 cm.allocations) then
                Nat.max (refMaxAllocIdV2 cm.allocations)
                  (refMaxAllocBytesProvIdV2 cm.allocations) + 2
              else Nat.max 2 (Nat.max (refMaxAllocIdV2 cm.allocations)
                (refMaxAllocBytesProvIdV2 cm.allocations) + 1))).toNat
              (if (refHasAllocIdV2 1 cm.allocations ||
                refAllocBytesHaveProvIdV2 1 cm.allocations) then
                Nat.max (refMaxAllocIdV2 cm.allocations)
                  (refMaxAllocBytesProvIdV2 cm.allocations) + 2
              else Nat.max 2 (Nat.max (refMaxAllocIdV2 cm.allocations)
                (refMaxAllocBytesProvIdV2 cm.allocations) + 1)) with
          | true =>
            rw [h_nx] at h_icm; simp only [ite_true] at h_icm; cases h_icm
          | false =>
            rw [h_nx] at h_icm
            simp only [Bool.false_eq_true, ite_false] at h_icm
            injection h_icm with h_pair
            have h_m0 : ({ p1.1 with
                nextAllocId := UInt64.ofNat _
                live := p1.1.live.push (retId, ⟨.stack, rawRet.withExtra
                  (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
                    (refLocalLayoutForTyV2 types retTy).layout.size)⟩)
              }).setIssuedIds (p1.2.push retId) = mem0 :=
              congrArg Prod.fst h_pair
            have h_live : mem0.live = p1.1.live.push (retId, ⟨.stack,
                rawRet.withExtra (Miri.TreeBorrows.BorrowTree.new
                  Miri.Memory.BorTag.one
                  (refLocalLayoutForTyV2 types retTy).layout.size)⟩) := by
              rw [← h_m0]; rfl
            have h_caller_false :
                refRefsValidInMiriListV2 p1.1 paramTys args = false := by
              cases h_c : refRefsValidInMiriListV2 p1.1 paramTys args with
              | false => rfl
              | true =>
                have h_t := (refRefsValidInMiriListV2_push_spec p1.1 mem0
                  (retId, ⟨.stack, rawRet.withExtra
                    (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
                      (refLocalLayoutForTyV2 types retTy).layout.size)⟩)
                  h_live paramTys args).2 h_c
                rw [h_t] at h_refs; cases h_refs
            simp only [h_caller_false, Bool.false_and, Bool.not_false, ite_true]

/-- Regression witness: a zero-length `&[u8]` slice pointing into
a live, aligned, in-bounds caller allocation whose bytes are all `.uninit`
(`InitMask.Lazy false`) is accepted by both `refValidateRefInMiriV2` and
`initRefStateV2`, matching `Trusted.MirSemantics.initStateV2` / `execProgV2`. -/
theorem profileV2_zeroLenSlice_uninitAlloc_accepted_spec :
    let sliceU8 := MirTy.ref .shared (.slice (.int .i8 false))
    let progZeroLen : Program := mkV2Prog {
      identity := "v2_zero_len_uninit_slice"
      argumentCount := 1
      locals := [.unit, sliceU8]
      basicBlocks := [{
        statements := [.assign ⟨0, []⟩ (.use (.constant ⟨.unit, .zeroSized⟩))]
        terminator := .return_
      }]
    }
    let cmUninit : CallerMemory := ⟨[{
      allocId := 1, alignLog2 := 0, mutability := .shared,
      bytes := [.uninit], live := true
    }]⟩
    let qZero : Query := {
      args := [.slicePtr ⟨some 1, 0, .isize⟩ 0]
      callerMem := cmUninit
    }
    WellFormedV2 progZeroLen qZero ∧
    BehaviorV2 progZeroLen qZero (.returned ⟨.unit, cmUninit⟩) ∧
    (∃ rs0, initRefStateV2 (encodeProg progZeroLen) qZero 4 = .ok rs0) := by
  intro sliceU8 progZeroLen cmUninit qZero
  have h_wp := Anneal.MirWp.spec_and_behaviorV2_of_exec_eq (p := progZeroLen)
    (q := qZero) (fuel := 3) (out := .returned ⟨.unit, cmUninit⟩) rfl
  refine ⟨h_wp.1, h_wp.2.1, ?_⟩
  let rp := encodeProg progZeroLen
  let rbody := @GetElem.getElem _ Nat _ _ _ rp.bodies 0 (by decide)
  let unitLay := refLocalLayoutForTyV2 rp.types .unit
  let ⟨rawRet, h_raw, _⟩ :=
    refTryNew_spec_v2 Miri.ABI.Size.ZERO Miri.ABI.Align.ONE 1 rfl rfl
  let ⟨blank, h_blank, h_bsz, _, _, h_bal, _, _, _, _, _⟩ :=
    refTryNew_spec_v2 (Miri.ABI.Size.ofBytes 1) ⟨0⟩ 1 rfl rfl
  let tree1 := Miri.TreeBorrows.BorrowTree.new
    Miri.Memory.BorTag.one (Miri.ABI.Size.ofBytes 1)
  let alloc1 : RefMiriAlloc :=
    (blank.withMutability .Not).withExtra tree1
  let allocId1 : Miri.Memory.AllocId := ⟨UInt64.ofNat 1, by decide⟩
  let allocId2 : Miri.Memory.AllocId := ⟨UInt64.ofNat 2, by decide⟩
  let emptyMem : RefMiriMem := Miri.Memory.MemoryState.empty
  let mem1 : RefMiriMem := {
    emptyMem with
    live := emptyMem.live.push (allocId1, ⟨.machine (), alloc1⟩)
  }
  have h_asz : alloc1.byteSize.bytes.toNat = 1 := by
    dsimp only [alloc1, Miri.Memory.Allocation.withExtra,
      Miri.Memory.Allocation.withMutability]
    exact congrArg (fun s : Miri.ABI.Size => s.bytes.toNat) h_bsz
  have h_aal : alloc1.align.pow2 = 0 := by
    dsimp only [alloc1, Miri.Memory.Allocation.withExtra,
      Miri.Memory.Allocation.withMutability]
    exact congrArg Miri.ABI.Align.pow2 h_bal
  have h_val : refValidateRefInMiriV2 mem1 .shared (.slice (.int .i8 false))
      (.slicePtr ⟨some 1, 0, .isize⟩ 0) = .ok () := by
    dsimp only [refValidateRefInMiriV2]
    rw [show refExactAllocIdV2 1 = some allocId1 from rfl]
    dsimp only [mem1]
    rw [show ((Miri.Memory.MemoryState.empty : RefMiriMem).live.push
        (allocId1, (⟨.machine (), alloc1⟩ :
          Miri.Memory.LocalAllocation Miri.Memory.Provenance
            Miri.TreeBorrows.BorrowTree Unit))).find?
        (fun entry => entry.1 == allocId1) =
        some (allocId1, ⟨.machine (), alloc1⟩) from rfl]
    dsimp only
    rw [h_asz, h_aal,
      show Trusted.MirAst.Mutability.beq .shared .mut = false from rfl]
    simp only [Bool.false_and, Bool.or_false]
    rfl
  have h_refs : refRefsValidInMiriListV2 mem1 [sliceU8] qZero.args = true := by
    dsimp only [refRefsValidInMiriListV2, refRefsValidInMiriV2, sliceU8, qZero]
    rw [h_val]
    rfl
  change ∃ rs0, initRefStateV2 rp qZero 4 = .ok rs0
  dsimp only [initRefStateV2]
  rw [show (!Nat.beq rp.pointerWidthBits 64 ||
      !Nat.beq rp.mirProfileVersion 2) = false from rfl]
  simp only [Bool.false_eq_true, ite_false]
  rw [show (!refValidCallerMemoryV2 qZero.callerMem) = false from rfl]
  simp only [Bool.false_eq_true, ite_false]
  rw [show Trusted.MirSemantics.getElem? rp.bodies rp.entryDefId =
      some rbody from rfl]
  dsimp only
  rw [show decodeLocalTys rp.types rbody.locals = some [.unit, sliceU8] from rfl]
  dsimp only
  rw [show (rbody.basicBlocks.isEmpty ||
      !Nat.blt rbody.argumentCount ([.unit, sliceU8] : List MirTy).length ||
      !refStorageAnnotationsInBounds rbody ||
      !refDiscriminantTypesValid [.unit, sliceU8] rbody ||
      !refCastTypesValid rp.types [.unit, sliceU8] rbody ||
      ![.unit, sliceU8].all refIsSupportedLocalTyV2 ||
      ![.unit, sliceU8].all refTyLayoutFitsU64V2) = false from rfl]
  simp only [Bool.false_eq_true, ite_false]
  rw [show (!checkRefArgsMatchV2 qZero.args
        (([.unit, sliceU8].drop 1).take rbody.argumentCount) ||
      !refValListAllocIdsFitU64V2 qZero.args) = false from rfl]
  simp only [Bool.false_eq_true, ite_false]
  rw [show Trusted.MirSemantics.getElem? ([.unit, sliceU8] : List MirTy) 0 =
      some .unit from rfl]
  dsimp only
  dsimp only [refInitCallerMemoryV2, refOwnLayoutFitsU64V2]
  simp only [Bool.not_true, Bool.false_eq_true, ite_false]
  rw [show unitLay.layout.size = Miri.ABI.Size.ZERO from rfl,
    show unitLay.layout.align.abi = Miri.ABI.Align.ONE from rfl, h_raw]
  dsimp only [qZero, cmUninit, refInsertCallerAllocsV2, refAllocToMiriV2,
    refPlainInitBytesV2?]
  rw [show Miri.ABI.Size.ofBytes (UInt64.ofNat
      ([AllocByte.uninit] : List AllocByte).length) =
      Miri.ABI.Size.ofBytes 1 from rfl,
    h_blank]
  rw [show refExactAllocIdV2 1 = some allocId1 from rfl]
  dsimp only [refPopulateAllocBytesV2, toMiriMutV2]
  simp only [ite_true]
  rw [show List.take rbody.argumentCount
      (List.drop 1 ([MirTy.unit, sliceU8] : List MirTy)) = [sliceU8] from rfl]
  have h_refs' :
      refRefsValidInMiriListV2
        ({ Miri.Memory.MemoryState.empty with
            live := Miri.Memory.MemoryState.empty.live.push
              (allocId1, ⟨.machine (), alloc1⟩) } : RefMiriMem)
        [sliceU8] qZero.args = true := h_refs
  have h_spans :
      refSpansPairwiseDisjointV2
        (refAccessSpansListV2 [sliceU8]
          [Val.slicePtr ⟨some 1, 0, .isize⟩ 0]) = true := rfl
  rw [h_refs', h_spans, show (true && true) = true from rfl,
    show (!(true : Bool)) = false from rfl]
  simp only [Bool.false_eq_true, ite_false]
  have h_has1 :
      (refHasAllocIdV2 1
            [{ allocId := 1, alignLog2 := 0, mutability := .shared,
               bytes := [AllocByte.uninit], live := true }] ||
          refAllocBytesHaveProvIdV2 1
            [{ allocId := 1, alignLog2 := 0, mutability := .shared,
               bytes := [AllocByte.uninit], live := true }] ||
          refValListHasAllocIdV2 1
            [Val.slicePtr ⟨some 1, 0, .isize⟩ 0]) = true := rfl
  have h_max1 :
      Nat.max
          (Nat.max
            (refMaxAllocIdV2
              [{ allocId := 1, alignLog2 := 0, mutability := .shared,
                 bytes := [AllocByte.uninit], live := true }])
            (refMaxAllocBytesProvIdV2
              [{ allocId := 1, alignLog2 := 0, mutability := .shared,
                 bytes := [AllocByte.uninit], live := true }]))
          (refMaxValListAllocIdV2
            [Val.slicePtr ⟨some 1, 0, .isize⟩ 0]) = 1 := rfl
  rw [h_has1, h_max1]
  simp only [ite_true]
  rw [show refExactAllocIdV2 (1 + 1) = some allocId2 from rfl]
  dsimp only
  rw [show (!Nat.beq (UInt64.ofNat (1 + 2)).toNat (1 + 2)) = false from rfl]
  simp only [Bool.false_eq_true, ite_false]
  dsimp only [initRefLocalsLoopV2]
  simp only [show refTyLayoutFitsU64V2 .unit = true from rfl,
    show refTyLayoutFitsU64V2 sliceU8 = true from rfl,
    show refTyIsImmediateV2 sliceU8 = true from rfl,
    Bool.not_true, Bool.false_eq_true, ite_false,
    show Nat.beq 0 0 = true from rfl,
    show Nat.beq 1 0 = false from rfl, ite_true]
  exact ⟨_, rfl⟩

end Anneal.MirCorrespondence
