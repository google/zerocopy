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
import Anneal.MirCorrespondence.ProfileV2EdgeWitnesses
import Anneal.MirCorrespondence.ProfileV2Canaries
import Anneal.MirCorrespondence.ProfileV2PosCanaries
import Anneal.MirCorrespondence.ProfileV2PosCanariesC1
import Anneal.MirCorrespondence.ScalarEquiv
import Anneal.MirCorrespondence.SimHelpers

namespace Anneal.MirCorrespondence

open Trusted Trusted.MirAst Trusted.MirSemantics Trusted.Correspondence
open Anneal.MirWp

/-!
# Profile v2 `V2_C3` Lockstep and Domain Refinement Bundles

Completes the final Profile v2 positive canary (`V2_C3`: self-moved thin ZST
pointer metadata overwrite) and assembles the domain-relativized safety
refinement and bidirectional fault-equivalence bundles over
`ProfileV2CanaryDomain` (`V2_C1`–`V2_C6`) and `ProfileV2ExtendedDomain`
(`V2_C1`–`V2_C6` plus the three conservative separation edges).
-/

/-! ## Section 1: Positive Canary Lockstep (`V2_C3`) -/

/-- Writing the zero-sized `.uninit` immediate through a provenance-carrying
unit memory place is a no-op that validates trivially. -/
private theorem c3_write_unit_mem (rp : RefProg) (st : RefMiriState)
    (off : Miri.ABI.Size) (id : Miri.Memory.AllocId) (tag : Miri.Memory.BorTag)
    (h_ty : resolveTy rp.types (tyIdFor rp.types .unit) = some .unit) :
    Miri.Interpreter.writePlaceImmediate
      (Miri.Interpreter.ExecutionMachine.projectionHooks
        (refExecCfgV2 rp)).place 0 .uninit
      ⟨.memory ⟨⟨off, some (.concrete id tag)⟩, .none, none⟩,
        refLocalLayoutForTyV2 rp.types .unit⟩ st = .ok () st := by
  have h_nv : Miri.Interpreter.writePlaceImmediateNoValidate
      (Miri.Interpreter.ExecutionMachine.projectionHooks
        (refExecCfgV2 rp)).place 0 .uninit
      ⟨.memory ⟨⟨off, some (.concrete id tag)⟩, .none, none⟩,
        refLocalLayoutForTyV2 rp.types .unit⟩ st = .ok () st := by
    cases st with | mk sk mc => cases mc with | mk m b d t r a u pmd => rfl
  have h_val := validatePlace_unit_forced_v2 rp.types st
    ⟨.memory ⟨⟨off, some (.concrete id tag)⟩, .none, none⟩,
      refLocalLayoutForTyV2 rp.types .unit⟩
    ⟨⟨⟨off, some (.concrete id tag)⟩, .none, none⟩,
      refLocalLayoutForTyV2 rp.types .unit⟩ rfl rfl h_ty rfl rfl rfl rfl
  dsimp only [Miri.Interpreter.writePlaceImmediate, bind, Bind.bind]
  rw [eStateM_bind_ok h_nv,
    eStateM_bind_ok (refProjPlace_enforceValidity_v2 rp 0 _ st), ite_true_eq,
    refProjPlace_validate_v2]
  exact h_val

/-- `V2_C3` (`Assign` LHS/RHS order on a self-moved thin ZST pointer):
`*_1 = PtrMetadata(move _1); _0 = (); return` is well-formed and returns
`((), callerMemV2_C3)` in `evalStepV2`, and `ProfileV2RefMachine` is
well-formed with the same unique behavior (`alloc2` unchanged) and no
divergence. -/
theorem V2_C3_selfPtrMetadata_lockstep :
    WellFormedV2 progV2_C3_selfPtrMetadata queryV2_C3 ∧
    BehaviorV2 progV2_C3_selfPtrMetadata queryV2_C3 outV2_C3 ∧
    ¬ DivergesV2 progV2_C3_selfPtrMetadata queryV2_C3 ∧
    RefWellFormedV2 (encodeProg progV2_C3_selfPtrMetadata) queryV2_C3 ∧
    RefBehaviorV2 (encodeProg progV2_C3_selfPtrMetadata) queryV2_C3 outV2_C3 ∧
    (∀ out', RefBehaviorV2 (encodeProg progV2_C3_selfPtrMetadata) queryV2_C3
      out' → out' = outV2_C3) ∧
    ¬ RefDivergesV2 (encodeProg progV2_C3_selfPtrMetadata) queryV2_C3 := by
  let ⟨h_wf, h_beh, h_nd, _⟩ := c3_m_anneal
  refine ⟨h_wf, h_beh, h_nd, ?_⟩
  let rp := encodeProg progV2_C3_selfPtrMetadata
  let rbody := @GetElem.getElem _ Nat _ _ _ rp.bodies 0 (by decide)
  let alloc2 := @GetElem.getElem _ Nat _ _ _ callerMemV2_C3.allocations 0
    (by decide)
  let raw : List UInt8 := [9]
  let ⟨ma2, h_ma2, h_rel⟩ :=
    refAllocToMiriV2_plainInit_spec alloc2 raw rfl rfl (by decide) (by decide)
  let ⟨rawRet, h_raw, _, _, _, _, _, _, _, _, _, _⟩ :=
    refTryNew_spec_v2 Miri.ABI.Size.ZERO Miri.ABI.Align.ONE 1 rfl rfl
  let mem0 : RefMiriMem :=
    ({ (Miri.Memory.MemoryState.empty : RefMiriMem) with
        nextAllocId := 3
        live := Array.mk [(alloc2IdV2, ⟨.machine (), ma2⟩),
                  (retAllocIdV2, ⟨.stack, rawRet.withExtra
                    (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
                      Miri.ABI.Size.ZERO)⟩)] }).setIssuedIds
      (Array.mk [alloc2IdV2, retAllocIdV2])
  let unitLay := refLocalLayoutForTyV2 rp.types .unit
  let ptrLay := refLocalLayoutForTyV2 rp.types (.rawPtr .mut .unit)
  let ptrImm : Miri.Interpreter.Immediate Miri.Memory.Provenance :=
    .scalar (.fromPointer refRuntimeLayoutV2.base
      ⟨Miri.ABI.Size.ZERO, .concrete alloc2IdV2 Miri.Memory.BorTag.one⟩)
  let retPlace : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance :=
    ⟨retMemPlaceV2, unitLay⟩
  let frame0 := mkRefMiriFrameV2 rp.types 0 rbody 0 0
    [⟨.live (.immediate .uninit), some unitLay⟩,
     ⟨.live (.immediate ptrImm), some ptrLay⟩] retPlace
  let m0 := mkRefMiriState frame0 mem0 refInitControl callerMemV2_C3
  have h_ins :
      refInsertCallerAllocsV2 (Miri.Memory.MemoryState.empty : RefMiriMem)
          Array.empty callerMemV2_C3.allocations =
        .ok ({ (Miri.Memory.MemoryState.empty : RefMiriMem) with
          live := Array.mk [(alloc2IdV2, ⟨.machine (), ma2⟩)] },
          Array.mk [alloc2IdV2]) := by
    rw [show callerMemV2_C3.allocations = [alloc2] from rfl]
    dsimp only [refInsertCallerAllocsV2]
    rw [show refExactAllocIdV2 alloc2.allocId = some alloc2IdV2 from rfl, h_ma2]
    rfl
  have h_icm : refInitCallerMemoryV2 rp.types callerMemV2_C3 .unit =
      .ok (mem0, retPlace) := by
    dsimp only [refInitCallerMemoryV2, refOwnLayoutFitsU64V2, Bool.not_true,
      ite_false]
    rw [show unitLay.layout.size = Miri.ABI.Size.ZERO from rfl,
      show unitLay.layout.align.abi = Miri.ABI.Align.ONE from rfl, h_raw]
    dsimp only
    rw [h_ins]
    rfl
  have h_init : ∀ ms : Nat, initRefStateV2 rp queryV2_C3 ms =
      .ok { miri := m0, retTy := .unit, retPlace := retPlace,
            stepsExecuted := 0, maxSteps := ms } := fun ms =>
    initRefStateV2_ok_v2 rp queryV2_C3 ms rbody
      [.unit, .rawPtr .mut .unit] .unit mem0 mem0 retPlace
      [⟨.live (.immediate .uninit), some unitLay⟩,
       ⟨.live (.immediate ptrImm), some ptrLay⟩]
      rfl rfl rfl rfl rfl rfl rfl rfl h_icm rfl rfl rfl
  -- `frameAt i` / `mkAt i`: `frame0` / `m0` once `move _1` has deinitialized
  -- `_1`, positioned at statement index `i` of block `0`.
  let frameAt (i : Nat) : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra :=
    { frame0 with
      locals := (Array.mk [⟨.live (.immediate .uninit), some unitLay⟩,
        ⟨.live (.immediate .uninit), some ptrLay⟩])
      location := .mir ⟨0, i⟩ }
  let mkAt (i : Nat) : RefMiriState :=
    { m0 with stack := ⟨Array.mk [frameAt i]⟩ }
  let rvh := Miri.Interpreter.ExecutionMachine.rvalueHooks (refExecCfgV2 rp)
    refLimitsV2
  let plh := (Miri.Interpreter.ExecutionMachine.projectionHooks
    (refExecCfgV2 rp)).place
  let block := toMiriBasicBlockV2 rp.types
    (@GetElem.getElem _ Nat _ _ _ rbody.basicBlocks 0 (by decide))
  let a2Place : Miri.Interpreter.RuntimePlace Miri.Memory.Provenance :=
    ⟨.memory ⟨⟨Miri.ABI.Size.ZERO, some (.concrete alloc2IdV2
      Miri.Memory.BorTag.one)⟩, .none, none⟩, unitLay⟩
  -- Step 0: `*_1 = PtrMetadata(move _1)` resolves `*_1` before moving `_1`.
  have h_step0 : Miri.Interpreter.ExecutionMachine.step
      (refExecutionConfigV2 rp) refLimitsV2 0 m0 = (mkAt 1, .ok true) := by
    have h_ev : rvh.evalPlace 0 ⟨1, Array.mk [.Deref]⟩ true m0 =
        .ok a2Place m0 := rfl
    have h_op : rvh.evalOperandAt 0
        (Miri.Interpreter.OperandPath.rvalue "operand") (.Move ⟨1, Array.empty⟩)
        none m0 = .ok ⟨.immediate ptrImm, ptrLay⟩ (mkAt 0) := rfl
    have h_ri : rvh.readImmediate 0 ⟨.immediate ptrImm, ptrLay⟩ (mkAt 0) =
        .ok ⟨ptrImm, ptrLay⟩ (mkAt 0) := rfl
    have h_un : rvh.unaryOp 0 .PtrMetadata ⟨ptrImm, ptrLay⟩ (mkAt 0) =
        .ok ⟨.uninit, unitLay⟩ (mkAt 0) := rfl
    have h_wr : rvh.writeImmediate 0 .uninit a2Place (mkAt 0) =
        .ok () (mkAt 0) :=
      c3_write_unit_mem rp (mkAt 0) _ _ _ rfl
    have h_ass : (Miri.Interpreter.ExecutionMachine.stepHooks
        (refExecutionConfigV2 rp) refLimitsV2).assign 0 ⟨1, Array.mk [.Deref]⟩
        (toMiriRvalueV2 rp.types (.unaryOp .ptrMetadata (.move ⟨1, []⟩))) m0 =
        (mkAt 0, .ok ()) := by
      have h_body : Miri.Interpreter.evalRvalueIntoPlace rvh 0
          (toMiriRvalueV2 rp.types (.unaryOp .ptrMetadata (.move ⟨1, []⟩)))
          ⟨1, Array.mk [.Deref]⟩ m0 = EStateM.Result.ok () (mkAt 0) := by
        dsimp only [Miri.Interpreter.evalRvalueIntoPlace, toMiriRvalueV2,
          toMiriOperandV2, toMiriPlaceV2, toMiriUnOp, List.map]
        refine mh_apply_bind _ _ _ _ _ h_ev ?_
        refine mh_apply_bind _ _ _ _ _ h_op ?_
        refine mh_apply_bind _ _ _ _ _ h_ri ?_
        refine mh_apply_bind _ _ _ _ _ h_un ?_
        refine mh_apply_bind _ _ () (mkAt 0) (mkAt 0) rfl ?_
        exact h_wr
      dsimp only [Miri.Interpreter.ExecutionMachine.stepHooks,
        Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run]
      rw [show Miri.Interpreter.ExecutionMachine.withValidation
          (refExecutionConfigV2 rp) refLimitsV2 = refExecCfgV2 rp from rfl,
        h_body]
    exact execStep_assign_ok rp m0 (mkAt 0) frame0 (frameAt 0) 0 0 block
      (toMiriStatementV2 rp.types
        (@GetElem.getElem _ Nat _ _ _
          (@GetElem.getElem _ Nat _ _ _ rbody.basicBlocks 0 (by decide)).statements
          0 (by decide)))
      ⟨1, Array.mk [.Deref]⟩
      (toMiriRvalueV2 rp.types (.unaryOp .ptrMetadata (.move ⟨1, []⟩)))
      rfl rfl rfl rfl rfl rfl h_ass rfl rfl
  -- Step 1: `_0 = ()` writes the zero-sized constant into immediate `_0`.
  have h_step1 : Miri.Interpreter.ExecutionMachine.step
      (refExecutionConfigV2 rp) refLimitsV2 0 (mkAt 1) =
      (mkAt 2, .ok true) := by
    let dest : Miri.Interpreter.RuntimePlace Miri.Memory.Provenance :=
      ⟨.local 0 0 none (frameAt 1).localsIdentity, unitLay⟩
    have h_ev : rvh.evalPlace 0 ⟨0, Array.empty⟩ true (mkAt 1) =
        .ok dest (mkAt 1) := rfl
    have h_op : rvh.evalOperandAt 0
        (Miri.Interpreter.OperandPath.rvalue "operand")
        (toMiriOperandV2 rp.types
          (.constant ⟨tyIdFor rp.types .unit, .zeroSized⟩))
        (some unitLay) (mkAt 1) =
        .ok ⟨.immediate .uninit, unitLay⟩ (mkAt 1) := rfl
    have h_nv : Miri.Interpreter.copyRuntimePlaceNoValidate plh
        (refExecCfgV2 rp).copy 0 ⟨.immediate .uninit, unitLay⟩ dest false
        (mkAt 1) = .ok () (mkAt 1) := rfl
    have h_vis : Miri.Interpreter.ValidityVisitor.visit (refValHooksV2 rp.types)
        0 16 (refInitSessV2 false) dest (mkAt 1) =
        .ok (refInitSessV2 false) (mkAt 1) :=
      Miri.Interpreter.ValidityVisitor.visit_fieldless (refValHooksV2 rp.types)
        0 15 (refInitSessV2 false) dest (mkAt 1) 0 rfl rfl rfl rfl rfl rfl
    have h_val := validatePlace_empty_noRanges_v2 rp.types (mkAt 1) (mkAt 1)
      dest ⟨.immediate .uninit, unitLay⟩ (refInitSessV2 false)
      (refInitSessV2 false) rfl rfl h_vis rfl rfl
    have h_cp := copyRuntimePlace_of_noValidate_v2 rp
      ⟨.immediate .uninit, unitLay⟩ dest false (mkAt 1) (mkAt 1) rfl h_nv h_val
    have h_ass : (Miri.Interpreter.ExecutionMachine.stepHooks
        (refExecutionConfigV2 rp) refLimitsV2).assign 0 ⟨0, Array.empty⟩
        (toMiriRvalueV2 rp.types
          (.use (.constant ⟨tyIdFor rp.types .unit, .zeroSized⟩))) (mkAt 1) =
        (mkAt 1, .ok ()) := by
      have h_body : Miri.Interpreter.evalRvalueIntoPlace rvh 0
          (toMiriRvalueV2 rp.types
            (.use (.constant ⟨tyIdFor rp.types .unit, .zeroSized⟩)))
          ⟨0, Array.empty⟩ (mkAt 1) = EStateM.Result.ok () (mkAt 1) := by
        dsimp only [Miri.Interpreter.evalRvalueIntoPlace, toMiriRvalueV2]
        refine mh_apply_bind _ _ _ _ _ h_ev ?_
        refine mh_apply_bind _ _ _ _ _ h_op ?_
        exact h_cp
      dsimp only [Miri.Interpreter.ExecutionMachine.stepHooks,
        Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run]
      rw [show Miri.Interpreter.ExecutionMachine.withValidation
          (refExecutionConfigV2 rp) refLimitsV2 = refExecCfgV2 rp from rfl,
        h_body]
    exact execStep_assign_ok rp (mkAt 1) (mkAt 1) (frameAt 1) (frameAt 1) 0 1
      block
      (toMiriStatementV2 rp.types
        (@GetElem.getElem _ Nat _ _ _
          (@GetElem.getElem _ Nat _ _ _ rbody.basicBlocks 0 (by decide)).statements
          1 (by decide)))
      ⟨0, Array.empty⟩
      (toMiriRvalueV2 rp.types
        (.use (.constant ⟨tyIdFor rp.types .unit, .zeroSized⟩)))
      rfl rfl rfl rfl rfl rfl h_ass rfl rfl
  -- Step 2: `return` copies zero-sized `_0` into the return place and pops.
  let stEnd : RefMiriState :=
    { m0 with
      stack := ⟨Array.empty⟩
      machine := { m0.machine with
        user := { m0.machine.user with
          control := advanceRefControl refInitControl } } }
  have h_step2 : Miri.Interpreter.ExecutionMachine.step
      (refExecutionConfigV2 rp) refLimitsV2 0 (mkAt 2) = (stEnd, .ok true) := by
    let stMid : RefMiriState := { stEnd with stack := (mkAt 2).stack }
    have h_bt := beforeTerminator_initCtrl_v2 rp (mkAt 2) rfl rfl
    have h_retOp : plh.localToOp 0 0 stMid =
        .ok ⟨.immediate .uninit, unitLay⟩ stMid := rfl
    have h_nv : Miri.Interpreter.copyRuntimePlaceNoValidate plh
        (refExecCfgV2 rp).copy 0 ⟨.immediate .uninit, unitLay⟩
        ⟨.memory retMemPlaceV2, unitLay⟩ true stEnd = .ok () stEnd := rfl
    have h_val := validatePlace_unit_forced_v2 rp.types stEnd
      ⟨.memory retMemPlaceV2, unitLay⟩ retPlace rfl rfl rfl rfl rfl rfl rfl
    have h_copy := copyRuntimePlace_of_noValidate_v2 rp
      ⟨.immediate .uninit, unitLay⟩ ⟨.memory retMemPlaceV2, unitLay⟩ true stEnd
      stEnd rfl h_nv h_val
    have h_clean : Miri.Interpreter.CallMachine.cleanup
        { refLifecycle rp.types with storage := refStorageHooksV2 rp.types }
        0 false (frameAt 2) stEnd = .ok .normal stEnd := rfl
    have h_rf := returnFromCurrentFrame_op_at_v2 rp stMid (.immediate .uninit)
      .unit retPlace (frameAt 2) 0 2
      (Array.mk ((@GetElem.getElem _ Nat _ _ _ rbody.basicBlocks 0
        (by decide)).statements.map (toMiriStatementV2 rp.types)))
      mem0 mem0 rfl rfl rfl rfl rfl rfl rfl h_retOp h_clean h_copy
    exact execStep_term_ok rp (mkAt 2) stMid stEnd (frameAt 2) 0 2 block
      rfl rfl rfl rfl rfl h_bt h_rf
  have h_find2 : mem0.live.find? (fun e => e.1 == alloc2IdV2) =
      some (alloc2IdV2, ⟨.machine (), ma2⟩) := by
    dsimp only [mem0]
    rw [← Array.find?_toList]
    rfl
  have h_cm : refExtractCallerMemoryV2 callerMemV2_C3 mem0 =
      callerMemV2_C3 := by
    dsimp only [refExtractCallerMemoryV2, callerMemV2_C3]
    exact congrArg CallerMemory.mk
      (congrArg (· :: [])
        (refExtractOneCallerAllocV2_of_allocByteSliceRel mem0 alloc2 alloc2
          raw alloc2IdV2 ⟨.machine (), ma2⟩ rfl rfl h_find2 h_rel))
  -- No `have` binds the `refCoreExecV2` witness: `whnf` of that concrete type
  -- (elaborator, linters) would run the interpreter symbolically.
  exact ref_ok_of_coreExec (fuel := 3) h_init (by
    rw [refCoreExecV2_running h_step0 rfl, refCoreExecV2_running h_step1 rfl,
      refCoreExecV2_return_ok_v2 (v := .unit) h_step2 rfl rfl]
    exact congrArg (fun cm => TerminalOut.returned ⟨.unit, cm⟩) h_cm)

/-! ## Section 2: Domain Refinement and Fault-Equivalence Bundles -/

private theorem safetyPoint_of_posLockstep {p : Program} {q : Query}
    {out : TerminalOut}
    (h_lock : WellFormedV2 p q ∧ BehaviorV2 p q out ∧ ¬ DivergesV2 p q ∧
      RefWellFormedV2 (encodeProg p) q ∧ RefBehaviorV2 (encodeProg p) q out ∧
      (∀ out', RefBehaviorV2 (encodeProg p) q out' → out' = out) ∧
      ¬ RefDivergesV2 (encodeProg p) q) :
    (WellFormedV2 p q → RefWellFormedV2 (encodeProg p) q) ∧
    (∀ out', WellFormedV2 p q →
      RefBehaviorV2 (encodeProg p) q out' → BehaviorV2 p q out') ∧
    (WellFormedV2 p q → RefDivergesV2 (encodeProg p) q → DivergesV2 p q) :=
  ⟨fun _ => h_lock.2.2.2.1,
    fun out' _ h_rbeh => by
      rw [h_lock.2.2.2.2.2.1 out' h_rbeh]
      exact h_lock.2.1,
    fun _ h_rdiv => False.elim (h_lock.2.2.2.2.2.2 h_rdiv)⟩

private theorem biFaultPoint_of_posLockstep {p : Program} {q : Query}
    {out : TerminalOut}
    (h_lock : WellFormedV2 p q ∧ BehaviorV2 p q out ∧ ¬ DivergesV2 p q ∧
      RefWellFormedV2 (encodeProg p) q ∧ RefBehaviorV2 (encodeProg p) q out ∧
      (∀ out', RefBehaviorV2 (encodeProg p) q out' → out' = out) ∧
      ¬ RefDivergesV2 (encodeProg p) q) :
    (ReachesResultV2 p q (.fault .undefined) ↔
      ∃ maxSteps : Nat, RefReachesOutcomeV2 (encodeProg p) q maxSteps .ub) ∧
    (ReachesResultV2 p q (.fault .unsupported) ↔
      ∃ maxSteps : Nat,
        RefReachesOutcomeV2 (encodeProg p) q maxSteps .blocked) :=
  ⟨⟨fun h_ub => False.elim (h_lock.1.2 .undefined h_ub),
      fun ⟨ms, h_rub⟩ => False.elim ((h_lock.2.2.2.1 ms).2.1 h_rub)⟩,
    ⟨fun h_uns => False.elim (h_lock.1.2 .unsupported h_uns),
      fun ⟨ms, h_rblk⟩ => False.elim ((h_lock.2.2.2.1 ms).2.2 h_rblk)⟩⟩

private theorem safetyPoint_of_negUbLockstep {p : Program} {q : Query}
    (h_lock : ReachesResultV2 p q (.fault .undefined) ∧
      ¬ ReachesResultV2 p q (.fault .unsupported) ∧
      ¬ WellFormedV2 p q ∧
      (∃ ms, RefReachesOutcomeV2 (encodeProg p) q ms .ub) ∧
      (∀ ms, ¬ RefReachesOutcomeV2 (encodeProg p) q ms .blocked) ∧
      ¬ RefWellFormedV2 (encodeProg p) q) :
    (WellFormedV2 p q → RefWellFormedV2 (encodeProg p) q) ∧
    (∀ out', WellFormedV2 p q →
      RefBehaviorV2 (encodeProg p) q out' → BehaviorV2 p q out') ∧
    (WellFormedV2 p q → RefDivergesV2 (encodeProg p) q → DivergesV2 p q) :=
  ⟨fun h_wf => False.elim (h_lock.2.2.1 h_wf),
    fun _ h_wf _ => False.elim (h_lock.2.2.1 h_wf),
    fun h_wf _ => False.elim (h_lock.2.2.1 h_wf)⟩

private theorem biFaultPoint_of_negUbLockstep {p : Program} {q : Query}
    (h_lock : ReachesResultV2 p q (.fault .undefined) ∧
      ¬ ReachesResultV2 p q (.fault .unsupported) ∧
      ¬ WellFormedV2 p q ∧
      (∃ ms, RefReachesOutcomeV2 (encodeProg p) q ms .ub) ∧
      (∀ ms, ¬ RefReachesOutcomeV2 (encodeProg p) q ms .blocked) ∧
      ¬ RefWellFormedV2 (encodeProg p) q) :
    (ReachesResultV2 p q (.fault .undefined) ↔
      ∃ maxSteps : Nat, RefReachesOutcomeV2 (encodeProg p) q maxSteps .ub) ∧
    (ReachesResultV2 p q (.fault .unsupported) ↔
      ∃ maxSteps : Nat,
        RefReachesOutcomeV2 (encodeProg p) q maxSteps .blocked) :=
  ⟨⟨fun _ => h_lock.2.2.2.1, fun _ => h_lock.1⟩,
    ⟨fun h_uns => False.elim (h_lock.2.1 h_uns),
      fun ⟨ms, h_rblk⟩ => False.elim (h_lock.2.2.2.2.1 ms h_rblk)⟩⟩

private theorem safetyPoint_of_nwf {p : Program} {q : Query}
    (h_nwf : ¬ WellFormedV2 p q) :
    (WellFormedV2 p q → RefWellFormedV2 (encodeProg p) q) ∧
    (∀ out', WellFormedV2 p q →
      RefBehaviorV2 (encodeProg p) q out' → BehaviorV2 p q out') ∧
    (WellFormedV2 p q → RefDivergesV2 (encodeProg p) q → DivergesV2 p q) :=
  ⟨fun h_wf => False.elim (h_nwf h_wf),
    fun _ h_wf _ => False.elim (h_nwf h_wf),
    fun h_wf _ => False.elim (h_nwf h_wf)⟩

private theorem safetyPoint_canaryDomain (p : Program) (q : Query)
    (h_dom : ProfileV2CanaryDomain p q) :
    (WellFormedV2 p q → RefWellFormedV2 (encodeProg p) q) ∧
    (∀ out', WellFormedV2 p q →
      RefBehaviorV2 (encodeProg p) q out' → BehaviorV2 p q out') ∧
    (WellFormedV2 p q → RefDivergesV2 (encodeProg p) q → DivergesV2 p q) := by
  cases h_dom with
  | inl h =>
    let ⟨hp, hq⟩ := h; subst hp; subst hq
    exact safetyPoint_of_posLockstep V2_C1_splitAt_lockstep
  | inr h => cases h with
    | inl h =>
      let ⟨hp, hq⟩ := h; subst hp; subst hq
      exact safetyPoint_of_posLockstep V2_C2_offsetWrite_lockstep
    | inr h => cases h with
      | inl h =>
        let ⟨hp, hq⟩ := h; subst hp; subst hq
        exact safetyPoint_of_posLockstep V2_C3_selfPtrMetadata_lockstep
      | inr h => cases h with
        | inl h =>
          let ⟨hp, hq⟩ := h; subst hp; subst hq
          exact safetyPoint_of_negUbLockstep V2_C4a_entryMisalign_lockstep
        | inr h => cases h with
          | inl h =>
            let ⟨hp, hq⟩ := h; subst hp; subst hq
            exact safetyPoint_of_negUbLockstep V2_C4b_derefMisalign_lockstep
          | inr h => cases h with
            | inl h =>
              let ⟨hp, hq⟩ := h; subst hp; subst hq
              exact safetyPoint_of_negUbLockstep V2_C5_roWrite_lockstep
            | inr h =>
              let ⟨hp, hq⟩ := h; subst hp; subst hq
              exact safetyPoint_of_negUbLockstep V2_C6_danglingLocalRef_lockstep

/-- Domain-relativized Profile v2 safety refinement across all seven
end-to-end Profile v2 canaries (`V2_C1`–`V2_C6`). -/
theorem profileV2CanaryDomain_safetyRefinement :
    SafetyRefinementV2On ProfileV2CanaryDomain encodeProg where
  wellFormed_transfer p q h_dom := (safetyPoint_canaryDomain p q h_dom).1
  behavior_reflect p q out' h_dom := (safetyPoint_canaryDomain p q h_dom).2.1 out'
  diverges_reflect p q h_dom := (safetyPoint_canaryDomain p q h_dom).2.2

/-- Domain-relativized Profile v2 bidirectional fault equivalence across all
seven end-to-end Profile v2 canaries (`V2_C1`–`V2_C6`). -/
theorem profileV2CanaryDomain_biFaultEquiv :
    BiFaultEquivV2On ProfileV2CanaryDomain encodeProg := by
  have h_pt : ∀ p q, ProfileV2CanaryDomain p q →
      (ReachesResultV2 p q (.fault .undefined) ↔
        ∃ maxSteps : Nat, RefReachesOutcomeV2 (encodeProg p) q maxSteps .ub) ∧
      (ReachesResultV2 p q (.fault .unsupported) ↔
        ∃ maxSteps : Nat,
          RefReachesOutcomeV2 (encodeProg p) q maxSteps .blocked) := by
    intro p q h_dom
    cases h_dom with
    | inl h =>
      let ⟨hp, hq⟩ := h; subst hp; subst hq
      exact biFaultPoint_of_posLockstep V2_C1_splitAt_lockstep
    | inr h => cases h with
      | inl h =>
        let ⟨hp, hq⟩ := h; subst hp; subst hq
        exact biFaultPoint_of_posLockstep V2_C2_offsetWrite_lockstep
      | inr h => cases h with
        | inl h =>
          let ⟨hp, hq⟩ := h; subst hp; subst hq
          exact biFaultPoint_of_posLockstep V2_C3_selfPtrMetadata_lockstep
        | inr h => cases h with
          | inl h =>
            let ⟨hp, hq⟩ := h; subst hp; subst hq
            exact biFaultPoint_of_negUbLockstep V2_C4a_entryMisalign_lockstep
          | inr h => cases h with
            | inl h =>
              let ⟨hp, hq⟩ := h; subst hp; subst hq
              exact biFaultPoint_of_negUbLockstep V2_C4b_derefMisalign_lockstep
            | inr h => cases h with
              | inl h =>
                let ⟨hp, hq⟩ := h; subst hp; subst hq
                exact biFaultPoint_of_negUbLockstep V2_C5_roWrite_lockstep
              | inr h =>
                let ⟨hp, hq⟩ := h; subst hp; subst hq
                exact biFaultPoint_of_negUbLockstep
                  V2_C6_danglingLocalRef_lockstep
  exact ⟨fun p q h_dom => (h_pt p q h_dom).1,
    fun p q h_dom => (h_pt p q h_dom).2⟩

private theorem safetyPoint_extendedDomain (p : Program) (q : Query)
    (h_dom : ProfileV2ExtendedDomain p q) :
    (WellFormedV2 p q → RefWellFormedV2 (encodeProg p) q) ∧
    (∀ out', WellFormedV2 p q →
      RefBehaviorV2 (encodeProg p) q out' → BehaviorV2 p q out') ∧
    (WellFormedV2 p q → RefDivergesV2 (encodeProg p) q → DivergesV2 p q) := by
  cases h_dom with
  | inl h_can => exact safetyPoint_canaryDomain p q h_can
  | inr h => cases h with
    | inl h =>
      let ⟨hp, hq⟩ := h; subst hp; subst hq
      exact safetyPoint_of_nwf
        conservative_edge1_zero_offset_oob_separation.2.1
    | inr h => cases h with
      | inl h =>
        let ⟨hp, hq⟩ := h; subst hp; subst hq
        exact safetyPoint_of_nwf
          conservative_edge2_null_zst_deref_separation.2.1
      | inr h =>
        let ⟨hp, hq⟩ := h; subst hp; subst hq
        exact safetyPoint_of_nwf
          conservative_edge3_const_to_mut_cast_separation.2.1

/-- Domain-relativized Profile v2 safety refinement extends over
`ProfileV2ExtendedDomain`, including all three conservative separation edges.
-/
theorem profileV2ExtendedDomain_safetyRefinement :
    SafetyRefinementV2On ProfileV2ExtendedDomain encodeProg where
  wellFormed_transfer p q h_dom := (safetyPoint_extendedDomain p q h_dom).1
  behavior_reflect p q out' h_dom :=
    (safetyPoint_extendedDomain p q h_dom).2.1 out'
  diverges_reflect p q h_dom := (safetyPoint_extendedDomain p q h_dom).2.2

/-- Adding the conservative-edge witnesses to the Profile v2 domain strictly
rules out `BiFaultEquivV2On ProfileV2ExtendedDomain encodeProg`, leaving
`SafetyRefinementV2On` as the exact domain-wide relationship. -/
theorem profileV2ExtendedDomain_not_biFaultEquiv :
    ¬ BiFaultEquivV2On ProfileV2ExtendedDomain encodeProg := by
  intro h_bi
  let ⟨h_ub, _, _, _, h_no_rub⟩ := conservative_edge1_zero_offset_oob_separation
  let ⟨ms, h_rub⟩ :=
    (h_bi.ub_iff progV2Edge1ZeroOffsetOob queryV2Edge1ZeroOffsetOob
      (Or.inr (Or.inl ⟨rfl, rfl⟩))).1 h_ub
  exact h_no_rub ms h_rub

/-! ## Section 3: Panic-Abort Caller-Memory Regression Witness -/

/-- Parameterized Profile v2 panic-abort caller-mutation regression program:
`*_1 = 7_u8; assert(false, true, msg)` with `--panic abort`, no crate-local
`#[panic_handler]`, and configurable `overflowChecks`. -/
noncomputable def progV2AbortMut (msg : AssertKind)
    (overflowChecks : Bool := false) : Program :=
  { mkV2Prog {
      identity := "v2_abort_mut"
      argumentCount := 1
      locals := [.unit, .rawPtr .mut u8Ty]
      basicBlocks := [{
        statements := [
          .assign ⟨1, [.deref]⟩
            (.use (.constant ⟨u8Ty, .scalar (BitVec.ofNat 128 7)⟩))
        ]
        terminator := .assert
          (.constant ⟨.bool, .scalar (BitVec.ofNat 128 0)⟩)
          true msg 0 .continue_
      }]
    } with
    panicStrategy := .abort
    hasLocalPanicHandler := false
    overflowChecks := overflowChecks }

/-- Pre-state 1-byte mutable caller allocation `[1]` at `allocId = 2`. -/
noncomputable def callerMemV2AbortPre : CallerMemory := ⟨[{
  allocId := 2, alignLog2 := 0, mutability := .mut
  bytes := [.init 1 none], live := true
}]⟩

/-- Post-state 1-byte mutable caller allocation `[7]` at `allocId = 2`. -/
noncomputable def callerMemV2AbortPost : CallerMemory := ⟨[{
  allocId := 2, alignLog2 := 0, mutability := .mut
  bytes := [.init 7 none], live := true
}]⟩

/-- Query passing `*mut u8` pointing to byte `0` of `callerMemV2AbortPre`. -/
noncomputable def queryV2AbortMut : Query := {
  args := [.ptr ⟨some 2, 0, .isize⟩]
  callerMem := callerMemV2AbortPre
}

private noncomputable def abortA2Pre :
    Miri.Memory.Allocation Miri.Memory.Provenance Unit :=
  exceptOkGet (Miri.Memory.Allocation.fromBytes (Array.mk [1]) ⟨0⟩ .Mut) rfl

private noncomputable def abortA2Post :
    Miri.Memory.Allocation Miri.Memory.Provenance Unit :=
  exceptOkGet (Miri.Memory.Allocation.fromBytes (Array.mk [7]) ⟨0⟩ .Mut) rfl

private theorem abort_write_a2 :
    Miri.Memory.Allocation.writeScalar refRuntimeLayoutV2.base
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 1))
      (.fromScalarInt (miriScalar .i8 (BitVec.ofNat 128 7)))
      (abortA2Pre.withExtra (c2Tree 1)) =
      .ok () (abortA2Post.withExtra (c2Tree 1)) := by
  let ⟨a', h_ws, h_bsz, h_len, h_mut, h_al, h_ex, h_nb, _, _, h_imset, _,
      h_pm, h_gb, _⟩ :=
    Miri.Memory.Allocation.writeScalar_spec refRuntimeLayoutV2.base
      (abortA2Pre.withExtra (c2Tree 1))
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 1))
      (.fromScalarInt (miriScalar .i8 (BitVec.ofNat 128 7)))
      (.bits (BitVec.ofNat 128 7)) Miri.Memory.ProvenanceMap.new
      Miri.Memory.ProvenanceMap.new
      rfl rfl rfl trivial (by decide) (by decide) (by decide) rfl
      (fun _ _ => rfl) rfl
  rw [h_ws]
  have h0 := h_gb _ rfl
  have h_im_eq :
      Miri.Memory.InitMask.setRange
        (abortA2Pre.withExtra (c2Tree 1)).initializationMask
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 1))
        true = .ok (abortA2Post.withExtra (c2Tree 1)).initializationMask :=
    Miri.Memory.InitMask.full_overwrite_stays_lazy (Miri.ABI.Size.ofBytes 1)
      (Miri.ABI.Size.ofBytes 1) true true
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 1))
      rfl rfl (by decide)
  cases a' with
  | _ rb sz pv im al mt ex nb =>
  have e_sz : sz = Miri.ABI.Size.ofBytes 1 := h_bsz
  have e_len : rb.size = 1 := h_len
  have e_mt : mt = .Mut := h_mut
  have e_al : al = ⟨0⟩ := h_al
  have e_ex : ex = c2Tree 1 := h_ex
  have e_nb : nb = none := h_nb
  have e_pv : pv = Miri.Memory.ProvenanceMap.new := h_pm
  have e_im : (Except.ok im : Except Miri.Memory.InitMaskError _) =
      .ok (abortA2Post.withExtra (c2Tree 1)).initializationMask :=
    h_imset.symm.trans h_im_eq
  injection e_im with e_im
  subst e_sz e_mt e_al e_ex e_nb e_pv e_im
  cases rb with
  | mk l =>
    cases l with
    | nil =>
      have h01 : ¬ ((0 : Nat) = 1) := by decide
      exact absurd (show (0 : Nat) = 1 from e_len) h01
    | cons b0 l =>
      cases l with
      | cons b1 l =>
        have h2 : l.length + 2 = 1 := e_len
        exact absurd (Nat.le_add_left 2 l.length) (by rw [h2]; decide)
      | nil =>
        have g0 : (Except.ok (Array.mk [b0]) :
            Except Miri.Memory.AllocError _) = .ok (Array.mk [7]) := h0
        injection g0 with g0
        injection g0 with g0
        injection g0 with g0
        subst g0
        rfl

private noncomputable def abortRp (msg : AssertKind) (oc : Bool) : RefProg :=
  encodeProg (progV2AbortMut msg oc)

private noncomputable def abortTypes : List MirTy :=
  [.unit, u8Ty, .rawPtr .mut u8Ty, .bool]

private noncomputable def abortRbody (msg : AssertKind) : RefBody := {
  argumentCount := 1
  locals := [0, 2]
  basicBlocks := [{
    statements := [
      .assign ⟨1, [.deref]⟩
        (.use (.constant ⟨1, .scalar (BitVec.ofNat 128 7)⟩))
    ]
    terminator :=
      .assert (.constant ⟨3, .scalar (BitVec.ofNat 128 0)⟩)
        true msg 0 .continue_
  }]
  isUnsafe := false
  identity := "v2_abort_mut"
}

private noncomputable def abortRpCanon (msg : AssertKind)
    (oc : Bool) : RefProg := {
  bodies := [abortRbody msg]
  entryDefId := 0
  types := abortTypes
  pointerWidthBits := 64
  mirProfileVersion := 2
  scope := .unit
  overflowChecks := oc
  panicStrategy := .abort
  hasLocalPanicHandler := false
}

private theorem abortRp_eq (msg : AssertKind) (oc : Bool) :
    abortRp msg oc = abortRpCanon msg oc := rfl

private noncomputable def abortMem (live : Array RefLiveRow) : RefMiriMem :=
  ({ (Miri.Memory.MemoryState.empty : RefMiriMem) with
      nextAllocId := 3, live := live
    }).setIssuedIds (Array.mk [alloc2IdV2, retAllocIdV2])

private noncomputable def abortA2Mp :
    Miri.Interpreter.MemPlace Miri.Memory.Provenance :=
  ⟨⟨Miri.ABI.Size.ZERO, some (.concrete alloc2IdV2 Miri.Memory.BorTag.one)⟩,
    .none, none⟩

private noncomputable def abortUnitLay :=
  refLocalLayoutForTyV2 abortTypes .unit

private noncomputable def abortPtrLay :=
  refLocalLayoutForTyV2 abortTypes (.rawPtr .mut u8Ty)

private noncomputable def abortU8Lay :=
  refLocalLayoutForTyV2 abortTypes u8Ty

private noncomputable def abortRetPlace :
    Miri.Interpreter.MPlaceTy Miri.Memory.Provenance :=
  ⟨retMemPlaceV2, abortUnitLay⟩

private noncomputable def abortA2PreExtra :=
  abortA2Pre.withExtra (c2Tree 1)

private noncomputable def abortA2PostExtra :=
  abortA2Post.withExtra (c2Tree 1)

private noncomputable def abortLive0
    (rawRet : Miri.Memory.Allocation Miri.Memory.Provenance Unit) :
    Array RefLiveRow :=
  Array.mk [
    (alloc2IdV2, ⟨.machine (), abortA2PreExtra⟩),
    (retAllocIdV2, ⟨.stack, rawRet.withExtra (c2Tree 0)⟩)]

private noncomputable def abortLive1
    (rawRet : Miri.Memory.Allocation Miri.Memory.Provenance Unit) :
    Array RefLiveRow :=
  Array.mk [
    (retAllocIdV2, ⟨.stack, rawRet.withExtra (c2Tree 0)⟩),
    (alloc2IdV2, ⟨.machine (), abortA2PreExtra⟩)]

private noncomputable def abortLive2
    (rawRet : Miri.Memory.Allocation Miri.Memory.Provenance Unit) :
    Array RefLiveRow :=
  Array.mk [
    (retAllocIdV2, ⟨.stack, rawRet.withExtra (c2Tree 0)⟩),
    (alloc2IdV2, ⟨.machine (), abortA2PostExtra⟩)]

private noncomputable def abortLocals0 : List RefLocalState := [
  ⟨.live (.immediate .uninit), some abortUnitLay⟩,
  ⟨.live (.immediate (c2Ptr alloc2IdV2 0)), some abortPtrLay⟩]

private noncomputable def abortFrame (msg : AssertKind) (idx : Nat) :=
  mkRefMiriFrameV2 abortTypes 0 (abortRbody msg) 0 idx abortLocals0
    abortRetPlace

private noncomputable def abortState (msg : AssertKind) (idx : Nat)
    (live : Array RefLiveRow) : RefMiriState :=
  mkRefMiriState (abortFrame msg idx) (abortMem live) refInitControl
    callerMemV2AbortPre

private noncomputable def abortA2Place :
    Miri.Interpreter.RuntimePlace Miri.Memory.Provenance :=
  ⟨.memory abortA2Mp, abortU8Lay⟩

private noncomputable def abortMidState (msg : AssertKind)
    (rawRet : Miri.Memory.Allocation Miri.Memory.Provenance Unit) :
    RefMiriState :=
  mkRefMiriState (abortFrame msg 1) (abortMem (abortLive2 rawRet))
    (advanceRefControl refInitControl) callerMemV2AbortPre

private theorem step_term_err_hooks_v2 {P L E M C V : Type}
    (hooks : Miri.Interpreter.StepHooks P L E M C V) (c : C)
    (st stMid st' : Miri.Interpreter.StepState P L E M)
    (frame : Miri.Interpreter.Frame P L E)
    (bbId : BasicBlockId) (sIdx : Nat) (block : Miri.MIR.BasicBlock)
    (err : Miri.Interpreter.StepError)
    (h_cf : st.stack.currentFrame? = some frame)
    (h_loc : frame.location = .mir ⟨bbId, sIdx⟩)
    (h_bb : frame.body.basicBlocks[bbId]? = some block)
    (h_st : block.statements[sIdx]? = none)
    (h_bt : hooks.beforeTerminator c st = (stMid, .ok ()))
    (h_term : hooks.terminator c block.terminator stMid = (st', .error err)) :
    Miri.Interpreter.Step.step hooks c st = (st', .error err) := by
  cases hooks with
  | mk f1 f2 f3 f4 f5 f6 f7 f8 beforeTerminator terminator =>
    dsimp only at h_bt h_term
    dsimp only [Miri.Interpreter.Step.step, Id.run, bind, Bind.bind, pure,
      Pure.pure]
    rw [h_cf]; dsimp only; rw [h_loc]; dsimp only; rw [h_bb]; dsimp only
    rw [h_st]; dsimp only; rw [h_bt]; dsimp only; rw [h_term]
    rfl

private theorem abort_cpnv_eq_writeMem (rp : RefProg) (st : RefMiriState)
    (h_tp : rp.types = abortTypes)
    (h_pmd : st.machine.pendingMoveDeinit = false) :
    Miri.Interpreter.copyRuntimePlaceNoValidate
      (Miri.Interpreter.ExecutionMachine.projectionHooks
        (refExecCfgV2 rp)).place
      (refExecCfgV2 rp).copy 0 ⟨.immediate (c2Int .i8 7), abortU8Lay⟩
      abortA2Place false st =
    Miri.Interpreter.PlaceMachine.writeMemory
      (refAccessConfigV2 abortTypes) (fun _ => true)
      (c2Int .i8 7) ⟨abortA2Mp, abortU8Lay⟩ st := by
  cases st with
  | mk sk mc =>
    cases mc with
    | mk m b d t r a u pmd =>
      dsimp only at h_pmd
      subst h_pmd
      cases rp
      dsimp only at h_tp
      subst h_tp
      rfl

private theorem abortStep1_of_term (rp : RefProg) (st stMid st' : RefMiriState)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (block : Miri.MIR.BasicBlock) (err : Miri.Interpreter.StepError)
    (h_pmd : st.machine.pendingMoveDeinit = false)
    (h_fr : st.stack.frames = Array.mk [frame])
    (h_loc : frame.location = .mir ⟨0, 1⟩)
    (h_bb : frame.body.basicBlocks[0]? = some block)
    (h_st : block.statements[1]? = none)
    (h_bt : (Miri.Interpreter.ExecutionMachine.stepHooks
      (refExecutionConfigV2 rp) refLimitsV2).beforeTerminator 0 st =
      (stMid, .ok ()))
    (h_term : (Miri.Interpreter.ExecutionMachine.stepHooks
      (refExecutionConfigV2 rp) refLimitsV2).terminator 0 block.terminator
      stMid = (st', .error err))
    (h_pmd' : st'.machine.pendingMoveDeinit = false) :
    Miri.Interpreter.ExecutionMachine.step (refExecutionConfigV2 rp)
        refLimitsV2 0 st = (st', .error err) := by
  have h_cf := stack_currentFrame_single_v2 st frame h_fr
  dsimp only [Miri.Interpreter.ExecutionMachine.step]
  rw [refState_with_pmd_false st h_pmd]
  rw [step_term_err_hooks_v2 _ 0 st stMid st' frame 0 1 block err
    h_cf h_loc h_bb h_st h_bt h_term]
  exact congrArg (·, Except.error err) (refState_with_pmd_false st' h_pmd')

private theorem abort_init_and_step0 (msg : AssertKind) (oc : Bool) :
    ∃ rawRet : Miri.Memory.Allocation Miri.Memory.Provenance Unit,
      let rp := abortRpCanon msg oc
      let m0 := abortState msg 0 (abortLive0 rawRet)
      let m1 := abortState msg 1 (abortLive2 rawRet)
      (∀ ms : Nat, initRefStateV2 rp queryV2AbortMut ms =
        .ok { miri := m0, retTy := .unit, retPlace := abortRetPlace,
              stepsExecuted := 0, maxSteps := ms }) ∧
      Miri.Interpreter.ExecutionMachine.step (refExecutionConfigV2 rp)
          refLimitsV2 0 m0 = (m1, .ok true) ∧
      refExtractCallerMemoryV2 callerMemV2AbortPre
          (abortMem (abortLive2 rawRet)) =
        callerMemV2AbortPost := by
  let ⟨rawRet, h_raw, _⟩ :=
    refTryNew_spec_v2 Miri.ABI.Size.ZERO Miri.ABI.Align.ONE 1 rfl rfl
  refine ⟨rawRet, ?_⟩
  let rp := abortRpCanon msg oc
  let m0 := abortState msg 0 (abortLive0 rawRet)
  let stW := abortState msg 0 (abortLive2 rawRet)
  let m1 := abortState msg 1 (abortLive2 rawRet)
  have h_fb1 : (match Miri.Memory.Allocation.fromBytes
      (Prov := Miri.Memory.Provenance) (Array.mk [1]) ⟨0⟩ .Mut with
    | .ok _ => true | .error _ => false) = true := rfl
  have h_ma2 :
      refAllocToMiriV2 ⟨2, 0, .mut, [.init 1 none], true⟩ =
        .ok abortA2PreExtra := by
    dsimp only [refAllocToMiriV2, toMiriMutV2]
    rw [show refPlainInitBytesV2? [.init 1 none] = some [1] from rfl]
    dsimp only
    rw [exceptOkGet_eq
      (Miri.Memory.Allocation.fromBytes (Prov := Miri.Memory.Provenance)
        (Array.mk [1]) ⟨0⟩ .Mut) h_fb1]
    rfl
  have h_ins :
      refInsertCallerAllocsV2 (Miri.Memory.MemoryState.empty : RefMiriMem)
          Array.empty callerMemV2AbortPre.allocations =
        .ok ({ (Miri.Memory.MemoryState.empty : RefMiriMem) with
          live := Array.mk [(alloc2IdV2, ⟨.machine (), abortA2PreExtra⟩)] },
          Array.mk [alloc2IdV2]) := by
    rw [show callerMemV2AbortPre.allocations =
        [⟨2, 0, .mut, [.init 1 none], true⟩] from rfl]
    dsimp only [refInsertCallerAllocsV2]
    rw [show refExactAllocIdV2 2 = some alloc2IdV2 from rfl, h_ma2]
    rfl
  have h_icm :
      refInitCallerMemoryV2 abortTypes callerMemV2AbortPre .unit =
        .ok (abortMem (abortLive0 rawRet), abortRetPlace) := by
    dsimp only [refInitCallerMemoryV2, refOwnLayoutFitsU64V2, Bool.not_true,
      ite_false]
    rw [show (refLocalLayoutForTyV2 abortTypes .unit).layout.size =
        Miri.ABI.Size.ZERO from rfl,
      show (refLocalLayoutForTyV2 abortTypes .unit).layout.align.abi =
        Miri.ABI.Align.ONE from rfl, h_raw]
    dsimp only
    rw [h_ins]
    rfl
  have h_init : ∀ ms : Nat, initRefStateV2 rp queryV2AbortMut ms =
      .ok { miri := m0, retTy := .unit, retPlace := abortRetPlace,
            stepsExecuted := 0, maxSteps := ms } := fun ms =>
    initRefStateV2_ok_v2 rp queryV2AbortMut ms (abortRbody msg)
      [.unit, .rawPtr .mut u8Ty] .unit
      (abortMem (abortLive0 rawRet)) (abortMem (abortLive0 rawRet))
      abortRetPlace abortLocals0 rfl rfl rfl rfl rfl rfl rfl rfl h_icm
      rfl rfl rfl
  let rng := Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 1)
  have h_find0 :
      (abortMem (abortLive0 rawRet)).live.find? (fun e => e.1 == alloc2IdV2) =
        some (alloc2IdV2, ⟨.machine (), abortA2PreExtra⟩) := rfl
  have h_any0 :
      ((abortMem (abortLive0 rawRet)).live.any
        (fun e => e.1 == alloc2IdV2)) = true := by
    rw [← Array.any_toList]; rfl
  have h_set1 :
      (abortMem (abortLive0 rawRet)).setLiveAllocation alloc2IdV2
          abortA2PreExtra =
        .ok (abortMem (abortLive1 rawRet)) := by
    rw [Miri.Memory.MemoryState.setLiveAllocation_of_find _ _ _ _ h_find0]
    rfl
  have h_gaMut := getPtrAllocMut_live_nonghost_v2 abortTypes
    (Miri.ABI.Size.ofBytes 1) 1
    (abortMem (abortLive0 rawRet)) (abortMem (abortLive1 rawRet))
    (.machine ()) abortA2PreExtra m0.machine alloc2IdV2 Miri.ABI.Size.ZERO
    abortA2Mp.ptr (.concrete Miri.Memory.BorTag.one)
    h_find0 rfl h_any0 h_set1 rfl (by decide) rfl rfl rfl rfl
  have h_pl :
      Miri.Interpreter.getPlaceAllocMut (abortMem (abortLive0 rawRet))
        ⟨m0.machine, none⟩
        ⟨abortA2Mp, ⟨Miri.ABI.Size.ofBytes 1, Miri.ABI.Align.ONE,
          .Scalar (.Initialized (value := .Int .I8 false)
            (validRange := refFullWrappingRangeSize (Miri.ABI.Size.ofBytes 1))),
          some abortU8Lay.ty⟩⟩
        refRuntimeLayoutV2 false none (refAccessConfigV2 abortTypes).globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks (refAccessConfigV2 abortTypes))
        (refAccessConfigV2 abortTypes).dynamicLayout =
        ⟨abortMem (abortLive1 rawRet), ⟨m0.machine, none⟩,
          some ⟨alloc2IdV2, rng, abortA2PreExtra⟩,
          .ok (some ⟨alloc2IdV2, rng, abortA2PreExtra⟩)⟩ :=
    getPlaceAllocMut_sized_of_access_v2' _ _ _ _ _ _ _ _ _ _ rfl rfl h_gaMut
  have h_set2 :
      (abortMem (abortLive1 rawRet)).setLiveAllocation alloc2IdV2
          abortA2PostExtra =
        .ok (abortMem (abortLive2 rawRet)) := by
    rw [Miri.Memory.MemoryState.setLiveAllocation_of_find
      (abortMem (abortLive1 rawRet)) alloc2IdV2
      ⟨.machine (), abortA2PreExtra⟩ _ rfl]
    rfl
  have h_wm :
      Miri.Interpreter.PlaceMachine.writeMemory (refAccessConfigV2 abortTypes)
          (fun _ => true) (c2Int .i8 7) ⟨abortA2Mp, abortU8Lay⟩ m0 =
        .ok () stW := by
    have h_w : Miri.Interpreter.writeImmediateToMplaceNoValidate
        (abortMem (abortLive0 rawRet)) ⟨m0.machine, none⟩ (c2Int .i8 7)
        ⟨abortA2Mp, Miri.Interpreter.localMemoryLayout abortU8Lay⟩
        (refAccessConfigV2 abortTypes).runtime
        (refAccessConfigV2 abortTypes).ghostMode
        (refAccessConfigV2 abortTypes).globalKind
        (refAccessConfigV2 abortTypes).globalHooks
        (Miri.Interpreter.PlaceMachine.accessHooks
          (refAccessConfigV2 abortTypes))
        (refAccessConfigV2 abortTypes).dynamicLayout (fun _ => true) =
        ⟨abortMem (abortLive2 rawRet), ⟨m0.machine, none⟩,
          some ⟨alloc2IdV2, rng, abortA2PostExtra⟩, .ok ()⟩ := by
      refine writeImmediate_scalar_u8_at_v2' _ (abortMem (abortLive1 rawRet))
        _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨alloc2IdV2, rng, abortA2PreExtra⟩ rng _
        h_pl ?_ ?_ ?_
      · rfl
      · exact abort_write_a2
      · exact h_set2
    exact Miri.Interpreter.PlaceMachine.writeMemory_of_result
      (refAccessConfigV2 abortTypes) (fun _ => true) (c2Int .i8 7)
      ⟨abortA2Mp, abortU8Lay⟩ m0 _ _ rfl h_w
  have h_read7 :
      abortA2PostExtra.readScalar refRuntimeLayoutV2.base rng false =
        .ok (.fromScalarInt (miriScalar .i8 (BitVec.ofNat 128 7))) :=
    (Miri.Memory.Allocation.readScalar_int_of_bytes _ refRuntimeLayoutV2.base
      _ (Array.mk [7]) rfl rfl (by decide) (Or.inr rfl)).trans rfl
  have h_find2 :
      (abortMem (abortLive2 rawRet)).live.find? (fun e => e.1 == alloc2IdV2) =
        some (alloc2IdV2, ⟨.machine (), abortA2PostExtra⟩) := rfl
  have h_gaGhost :
      Miri.Memory.AllocationAccess.getPtrAlloc stW.machine.memory
          (⟨stW.machine, none⟩ : Miri.Interpreter.PlaceMachine.AccessState Unit
            RefUser)
          ⟨Miri.ABI.Size.ofBytes 8⟩ abortA2Mp.ptr (Miri.ABI.Size.ofBytes 1)
          true none (refAccessConfigV2 abortTypes).globalHooks
          (Miri.Interpreter.PlaceMachine.accessHooks
            (refAccessConfigV2 abortTypes)) =
        ⟨stW.machine.memory, ⟨stW.machine, none⟩,
          some ⟨alloc2IdV2, rng, abortA2PostExtra⟩,
          .ok (some ⟨alloc2IdV2, rng, abortA2PostExtra⟩)⟩ :=
    getPtrAlloc_live_ghost_v2 (Miri.ABI.Size.ofBytes 1) 1 stW.machine.memory
      (.machine ()) abortA2PostExtra stW.machine alloc2IdV2 Miri.ABI.Size.ZERO
      abortA2Mp.ptr (.concrete Miri.Memory.BorTag.one) _ _ rfl h_find2 rfl
      (by decide) rfl rfl
  have h_raw := readImmediate_mem_u8_v2 abortTypes abortA2Mp alloc2IdV2
    abortA2PostExtra _ stW stW.machine.memory Miri.ABI.Size.ZERO true
    (refAccessConfigV2 abortTypes) rfl h_gaGhost rfl h_read7
  have h_valRead :
      (refValHooksV2 abortTypes).readImmediate 0 abortA2Place .integer stW =
        .ok ⟨c2Int .i8 7, abortU8Lay⟩ stW := by
    rw [refValHooksV2_readImmediate]
    dsimp only [bind, Bind.bind, EStateM.bind]
    rw [show Miri.Interpreter.placeToOp
        (refBasePlaceProjectionHooksV2 abortTypes).place 0 abortA2Place stW =
        .ok ⟨.indirect abortA2Mp, abortU8Lay⟩ stW from rfl]
    dsimp only [Miri.Interpreter.ValidityMemory.readImmediate,
      refValidityMemoryEnvV2, abortU8Lay, get, getThe, MonadStateOf.get,
      EStateM.get, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    rw [show refValidityMemoryEnv.memory stW = stW.machine.memory from rfl,
      show refValidityMemoryEnv.hooks stW = ⟨stW.machine, none⟩ from rfl,
      show (refAccessConfigV2 abortTypes).runtime = refRuntimeLayoutV2 from rfl,
      h_raw]
    rfl
  let sess : Miri.Interpreter.ValidityVisitor.Session Miri.Memory.Provenance :=
    { path := ⟨"", Array.empty⟩, flags := ⟨true, false⟩, ctfeMode := none,
      refTracking := some .empty,
      dataBytes := some (exceptOkGet
        (Miri.Memory.Validity.DataRangeSet.empty.addRange Miri.ABI.Size.ZERO
          (Miri.ABI.Size.ofBytes 1)) rfl) }
  have h_pre : refValidatePreMirror (refValHooksV2 abortTypes) 0 16
      abortA2Place true true stW = .ok sess stW := by
    change EStateM.bind (EStateM.bind (EStateM.bind
      ((refValHooksV2 abortTypes).readImmediate 0 abortA2Place .integer) _) _)
      _ stW = _
    rw [eStateM_bind3_ok h_valRead]
    rfl
  let rbb0 : RefBasicBlock := {
    statements := [
      .assign ⟨1, [.deref]⟩
        (.use (.constant ⟨1, .scalar (BitVec.ofNat 128 7)⟩))
    ]
    terminator :=
      .assert (.constant ⟨3, .scalar (BitVec.ofNat 128 0)⟩)
        true msg 0 .continue_
  }
  let block := toMiriBasicBlockV2 abortTypes rbb0
  let rstmt0 : RefStatementKind :=
    .assign ⟨1, [.deref]⟩
      (.use (.constant ⟨1, .scalar (BitVec.ofNat 128 7)⟩))
  let stmt0 := toMiriStatementV2 abortTypes rstmt0
  let rv0 := toMiriRvalueV2 abortTypes
    (.use (.constant ⟨1, .scalar (BitVec.ofNat 128 7)⟩))
  let rvh := Miri.Interpreter.ExecutionMachine.rvalueHooks
    (refExecCfgV2 rp) refLimitsV2
  have h_ev : rvh.evalPlace 0 ⟨1, Array.mk [.Deref]⟩ true m0 =
      .ok abortA2Place m0 := rfl
  have h_op : rvh.evalOperandAt 0
      (Miri.Interpreter.OperandPath.rvalue "operand")
      (toMiriOperandV2 abortTypes
        (.constant ⟨1, .scalar (BitVec.ofNat 128 7)⟩))
      (some abortU8Lay) m0 =
      .ok ⟨.immediate (c2Int .i8 7), abortU8Lay⟩ m0 := rfl
  have h_nv : Miri.Interpreter.copyRuntimePlaceNoValidate
      (Miri.Interpreter.ExecutionMachine.projectionHooks
        (refExecCfgV2 rp)).place
      (refExecCfgV2 rp).copy 0 ⟨.immediate (c2Int .i8 7), abortU8Lay⟩
      abortA2Place false m0 = .ok () stW := by
    rw [abort_cpnv_eq_writeMem rp m0 rfl rfl]
    exact h_wm
  have h_val := refValidatePlace_of_pre_v2 abortTypes abortA2Place stW stW sess
    h_pre rfl
  have h_cp := copyRuntimePlace_of_noValidate_v2 rp
    ⟨.immediate (c2Int .i8 7), abortU8Lay⟩ abortA2Place false m0 stW
    rfl h_nv h_val
  have h_ass : (Miri.Interpreter.ExecutionMachine.stepHooks
      (refExecutionConfigV2 rp) refLimitsV2).assign 0 ⟨1, Array.mk [.Deref]⟩
      rv0 m0 = (stW, .ok ()) := by
    have h_body : Miri.Interpreter.evalRvalueIntoPlace rvh 0 rv0
        ⟨1, Array.mk [.Deref]⟩ m0 = EStateM.Result.ok () stW := by
      dsimp only [Miri.Interpreter.evalRvalueIntoPlace, rv0, toMiriRvalueV2,
        toMiriOperandV2]
      refine mh_apply_bind _ _ _ _ _ h_ev ?_
      dsimp only [Miri.Interpreter.ExecutionMachine.rvalueHooks,
        Miri.Interpreter.RuntimePlace.layout, rvh]
      rw [refStepCfgV2_eq]
      refine mh_apply_bind _ _ _ _ _ h_op ?_
      rw [show (Miri.MIR.WithRetag.No == Miri.MIR.WithRetag.Yes) = false from rfl]
      exact h_cp
    dsimp only [Miri.Interpreter.ExecutionMachine.stepHooks,
      Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run]
    rw [show Miri.Interpreter.ExecutionMachine.withValidation
        (refExecutionConfigV2 rp) refLimitsV2 = refExecCfgV2 rp from rfl,
      h_body]
  have h_step0 : Miri.Interpreter.ExecutionMachine.step
      (refExecutionConfigV2 rp) refLimitsV2 0 m0 = (m1, .ok true) :=
    execStep_assign_ok rp m0 stW (abortFrame msg 0) (abortFrame msg 0) 0 0
      block stmt0 ⟨1, Array.mk [.Deref]⟩ rv0 rfl rfl rfl rfl rfl rfl h_ass
      rfl rfl
  have h_cm :
      refExtractCallerMemoryV2 callerMemV2AbortPre
          (abortMem (abortLive2 rawRet)) =
        callerMemV2AbortPost := by
    have h_rel : AllocByteSliceRel [7]
        ⟨2, 0, .mut, [.init 7 none], true⟩ abortA2PostExtra :=
      ⟨rfl, by decide, by decide, rfl, abortA2Post, c2Tree 1,
        exceptOkGet_eq _ rfl, rfl⟩
    have h_one := refExtractOneCallerAllocV2_of_allocByteSliceRel
      (abortMem (abortLive2 rawRet)) ⟨2, 0, .mut, [.init 1 none], true⟩
      ⟨2, 0, .mut, [.init 7 none], true⟩ [7] alloc2IdV2
      ⟨.machine (), abortA2PostExtra⟩ rfl rfl h_find2 h_rel
    dsimp only [refExtractCallerMemoryV2, callerMemV2AbortPre,
      callerMemV2AbortPost]
    rw [List.map_cons, List.map_nil, h_one]
  exact ⟨h_init, h_step0, h_cm⟩

private theorem abort_ref_aborted (msg : AssertKind) (oc : Bool)
    (h_term : ∀ rawRet,
      let rp := abortRpCanon msg oc
      let mMid := abortMidState msg rawRet
      let block := toMiriBasicBlockV2 abortTypes
        (@GetElem.getElem _ Nat _ _ _ (abortRbody msg).basicBlocks 0
          (Nat.zero_lt_succ 0))
      (Miri.Interpreter.ExecutionMachine.stepHooks
        (refExecutionConfigV2 rp) refLimitsV2).terminator 0
        block.terminator mMid =
        (mMid, .error (.termination (.abort "panic abort")))) :
    RefWellFormedV2 (abortRp msg oc) queryV2AbortMut ∧
    RefBehaviorV2 (abortRp msg oc) queryV2AbortMut
      (.aborted callerMemV2AbortPost) ∧
    (∀ out', RefBehaviorV2 (abortRp msg oc) queryV2AbortMut out' →
      out' = .aborted callerMemV2AbortPost) ∧
    ¬ RefDivergesV2 (abortRp msg oc) queryV2AbortMut := by
  rw [abortRp_eq msg oc]
  let ⟨rawRet, h_init, h_step0, h_cm⟩ := abort_init_and_step0 msg oc
  let rp := abortRpCanon msg oc
  let m1 := abortState msg 1 (abortLive2 rawRet)
  let mMid := abortMidState msg rawRet
  let block := toMiriBasicBlockV2 abortTypes
    (@GetElem.getElem _ Nat _ _ _ (abortRbody msg).basicBlocks 0
      (Nat.zero_lt_succ 0))
  have h_bt := beforeTerminator_initCtrl_v2 rp m1 rfl rfl
  have h_step1 := abortStep1_of_term rp m1 mMid mMid (abortFrame msg 1) block
    (.termination (.abort "panic abort")) rfl rfl rfl rfl rfl h_bt
    (h_term rawRet) rfl
  exact ref_ok_of_coreExec (fuel := 2) h_init (by
    rw [refCoreExecV2_step_ok_v2 h_step0 rfl]
    change (match evalRefCoreV2 rp .unit abortRetPlace m1 with
      | .running _ => False
      | .returned out => out = .aborted callerMemV2AbortPost
      | .ub | .blocked => False)
    dsimp only [evalRefCoreV2]
    rw [h_step1]
    dsimp only
    rw [show mMid.machine.user.callerMem = callerMemV2AbortPre from rfl,
      show mMid.machine.memory = abortMem (abortLive2 rawRet) from rfl, h_cm])

private theorem abort_ref_blocked (msg : AssertKind) (oc : Bool)
    (errMsg : String)
    (h_term : ∀ rawRet,
      let rp := abortRpCanon msg oc
      let mMid := abortMidState msg rawRet
      let block := toMiriBasicBlockV2 abortTypes
        (@GetElem.getElem _ Nat _ _ _ (abortRbody msg).basicBlocks 0
          (Nat.zero_lt_succ 0))
      (Miri.Interpreter.ExecutionMachine.stepHooks
        (refExecutionConfigV2 rp) refLimitsV2).terminator 0
        block.terminator mMid =
        (mMid, .error (.unsupported errMsg))) :
    (∃ ms, RefReachesOutcomeV2 (abortRp msg oc) queryV2AbortMut ms .blocked) ∧
    ¬ RefWellFormedV2 (abortRp msg oc) queryV2AbortMut := by
  rw [abortRp_eq msg oc]
  let ⟨rawRet, h_init, h_step0, _⟩ := abort_init_and_step0 msg oc
  let rp := abortRpCanon msg oc
  let m0 := abortState msg 0 (abortLive0 rawRet)
  let m1 := abortState msg 1 (abortLive2 rawRet)
  let mMid := abortMidState msg rawRet
  let block := toMiriBasicBlockV2 abortTypes
    (@GetElem.getElem _ Nat _ _ _ (abortRbody msg).basicBlocks 0
      (Nat.zero_lt_succ 0))
  have h_bt := beforeTerminator_initCtrl_v2 rp m1 rfl rfl
  have h_step1 := abortStep1_of_term rp m1 mMid mMid (abortFrame msg 1) block
    (.unsupported errMsg) rfl rfl rfl rfl rfl h_bt (h_term rawRet) rfl
  have h_blk : RefReachesOutcomeV2 rp queryV2AbortMut 2 .blocked := by
    dsimp only [RefReachesOutcomeV2]
    rw [h_init 2]
    let rs0 : RefState := ⟨m0, .unit, abortRetPlace, 0, 2⟩
    let rs1 : RefState := ⟨m1, .unit, abortRetPlace, 1, 2⟩
    have h_s0 : RefStepV2 rp rs0 (.running rs1) := by
      refine ⟨0, rfl, ?_⟩
      rw [evalRefStepV2_eq_liftCore_of_lt rp rs0 rfl]
      dsimp only [rs0, evalRefCoreV2]
      rw [h_step0]
      rfl
    have h_s1 : RefStepV2 rp rs1 .blocked := by
      refine ⟨0, rfl, ?_⟩
      rw [evalRefStepV2_eq_liftCore_of_lt rp rs1 rfl]
      dsimp only [rs1, evalRefCoreV2]
      rw [h_step1]
      rfl
    exact ⟨rs1, RefReachesV2.tail (RefReachesV2.refl rs0) h_s0, h_s1⟩
  exact ⟨⟨2, h_blk⟩, fun h_rwf => (h_rwf 2).2.2 h_blk⟩

/-- Regression witness: Profile v2 preserves panic-abort `.aborted callerMem`
outcomes (including prior caller-memory writes) for non-optional safe panics
and `--overflow-checks` overflow panics, while failing closed to
`.unsupported` / `.blocked` when `--overflow-checks` is disabled or on
unsupported `AssertKind`s. -/
theorem profileV2_panic_abort_preserves_callerMem :
    let pBc := progV2AbortMut .boundsCheck false
    let pOvOn := progV2AbortMut (.overflow .add) true
    let pOvOff := progV2AbortMut (.overflow .add) false
    let pUns := progV2AbortMut .unsupported false
    (WellFormedV2 pBc queryV2AbortMut ∧
      BehaviorV2 pBc queryV2AbortMut (.aborted callerMemV2AbortPost) ∧
      ¬ DivergesV2 pBc queryV2AbortMut ∧
      RefWellFormedV2 (encodeProg pBc) queryV2AbortMut ∧
      RefBehaviorV2 (encodeProg pBc) queryV2AbortMut
        (.aborted callerMemV2AbortPost) ∧
      ¬ RefDivergesV2 (encodeProg pBc) queryV2AbortMut) ∧
    (WellFormedV2 pOvOn queryV2AbortMut ∧
      BehaviorV2 pOvOn queryV2AbortMut (.aborted callerMemV2AbortPost) ∧
      ¬ DivergesV2 pOvOn queryV2AbortMut ∧
      RefWellFormedV2 (encodeProg pOvOn) queryV2AbortMut ∧
      RefBehaviorV2 (encodeProg pOvOn) queryV2AbortMut
        (.aborted callerMemV2AbortPost) ∧
      ¬ RefDivergesV2 (encodeProg pOvOn) queryV2AbortMut) ∧
    (ReachesResultV2 pOvOff queryV2AbortMut (.fault .unsupported) ∧
      ¬ WellFormedV2 pOvOff queryV2AbortMut ∧
      (∃ ms, RefReachesOutcomeV2 (encodeProg pOvOff) queryV2AbortMut ms
        .blocked) ∧
      ¬ RefWellFormedV2 (encodeProg pOvOff) queryV2AbortMut) ∧
    (ReachesResultV2 pUns queryV2AbortMut (.fault .unsupported) ∧
      ¬ WellFormedV2 pUns queryV2AbortMut ∧
      (∃ ms, RefReachesOutcomeV2 (encodeProg pUns) queryV2AbortMut ms
        .blocked) ∧
      ¬ RefWellFormedV2 (encodeProg pUns) queryV2AbortMut) := by
  have h_ab :
      ∀ (msg : AssertKind) (oc : Bool),
        execProgV2 (progV2AbortMut msg oc) 2 queryV2AbortMut
          (fun o => o = .aborted callerMemV2AbortPost) →
        WellFormedV2 (progV2AbortMut msg oc) queryV2AbortMut ∧
        BehaviorV2 (progV2AbortMut msg oc) queryV2AbortMut
          (.aborted callerMemV2AbortPost) ∧
        ¬ DivergesV2 (progV2AbortMut msg oc) queryV2AbortMut := by
    intro msg oc h_ex
    let ⟨h_wf, h_beh, h_nd, _⟩ := spec_and_behaviorV2_of_exec_eq h_ex
    exact ⟨h_wf, h_beh, h_nd⟩
  have h_blk_m :
      ∀ (msg : AssertKind) (oc : Bool),
        (match initStateV2 (progV2AbortMut msg oc) queryV2AbortMut with
        | .ok s0 =>
          match evalStepV2 (progV2AbortMut msg oc) s0 with
          | .step s1 =>
            evalStepV2 (progV2AbortMut msg oc) s1 = .fault .unsupported
          | _ => False
        | .error _ => False) →
        ReachesResultV2 (progV2AbortMut msg oc) queryV2AbortMut
          (.fault .unsupported) ∧
        ¬ WellFormedV2 (progV2AbortMut msg oc) queryV2AbortMut := by
    intro msg oc h_run
    cases h_i : initStateV2 (progV2AbortMut msg oc) queryV2AbortMut with
    | error _ => rw [h_i] at h_run; exact False.elim h_run
    | ok s0 =>
      rw [h_i] at h_run
      dsimp only at h_run
      cases h_s0 : evalStepV2 (progV2AbortMut msg oc) s0 with
      | done _ => rw [h_s0] at h_run; exact False.elim h_run
      | fault _ => rw [h_s0] at h_run; exact False.elim h_run
      | step s1 =>
        rw [h_s0] at h_run
        dsimp only at h_run
        have h_reach :
            ReachesResultV2 (progV2AbortMut msg oc) queryV2AbortMut
              (.fault .unsupported) := by
          dsimp only [ReachesResultV2]
          rw [h_i]
          exact ⟨s1, ReachesV2.tail (ReachesV2.refl s0) ⟨0, rfl, h_s0⟩,
            0, rfl, h_run⟩
        exact ⟨h_reach, fun h_wf => h_wf.2 .unsupported h_reach⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h_m := h_ab .boundsCheck false rfl
    let ⟨h_rwf, h_rbeh, _, h_rnd⟩ :=
      abort_ref_aborted .boundsCheck false (fun _ => rfl)
    exact ⟨h_m.1, h_m.2.1, h_m.2.2, h_rwf, h_rbeh, h_rnd⟩
  · have h_m := h_ab (.overflow .add) true rfl
    let ⟨h_rwf, h_rbeh, _, h_rnd⟩ :=
      abort_ref_aborted (.overflow .add) true (fun _ => rfl)
    exact ⟨h_m.1, h_m.2.1, h_m.2.2, h_rwf, h_rbeh, h_rnd⟩
  · have h_m := h_blk_m (.overflow .add) false rfl
    let ⟨h_rblk, h_nrwf⟩ := abort_ref_blocked (.overflow .add) false
      "optional overflow check unsupported" (fun _ => rfl)
    exact ⟨h_m.1, h_m.2, h_rblk, h_nrwf⟩
  · have h_m := h_blk_m .unsupported false rfl
    let ⟨h_rblk, h_nrwf⟩ := abort_ref_blocked .unsupported false
      "unsupported panic language item" (fun _ => rfl)
    exact ⟨h_m.1, h_m.2, h_rblk, h_nrwf⟩

private theorem reserveAllocId_findGlobal?_v2 (mem0 mem1 : RefMiriMem)
    (aid dstId : Miri.Memory.AllocId)
    (h_res : mem0.reserveAllocId = (mem1, .ok aid)) :
    mem1.findGlobal? dstId = mem0.findGlobal? dstId := by
  dsimp only [Miri.Memory.MemoryState.reserveAllocId, Id.run,
    bind, Bind.bind, pure, Pure.pure] at h_res
  have h1 := ite_pair_error_eq_ok _ _ _ _ _ _ h_res
  have h2 := ite_pair_error_eq_ok _ _ _ _ _ _ h1
  cases h_al : Miri.Memory.AllocId.ofUInt64 mem0.nextAllocId with
  | none => rw [h_al] at h2; cases h2
  | some id =>
    rw [h_al] at h2
    have h3 := ite_pair_error_eq_ok _ _ _ _ _ _ h2
    cases h_sw : mem0.sourceAllocIdWorldActive <;>
      rw [h_sw] at h3 <;>
      simp only [Bool.false_eq_true, ite_false, ite_true] at h3 <;>
      injection h3 with h_m1 _ <;>
      rw [← h_m1] <;> rfl

private theorem empty_hashmap_contains_false_v2 (k : UInt64) :
    (EmptyCollection.emptyCollection :
      Std.HashMap UInt64 (Array Nat)).contains k = false := by
  have hc :
      (Miri.Memory.KeyedArray.empty (fun (x : UInt64) => x)).contains k =
        false := by
    rw [Miri.Memory.KeyedArray.contains_rows, ← Array.contains_toList,
      Array.toList_map]
    rfl
  exact hc

private theorem empty_hashmap_get?_none_v2 (k : UInt64) :
    (EmptyCollection.emptyCollection :
      Std.HashMap UInt64 (Array Nat)).get? k = none := by
  have hc := empty_hashmap_contains_false_v2 k
  rw [Std.HashMap.contains_eq_isSome_getElem?] at hc
  rw [Std.HashMap.get?_eq_getElem?]
  cases h :
      (EmptyCollection.emptyCollection :
        Std.HashMap UInt64 (Array Nat))[k]? with
  | none => rfl
  | some _ => rw [h] at hc; cases hc

private theorem memoryState_empty_findGlobal?_none_v2
    (id : Miri.Memory.AllocId) :
    (Miri.Memory.MemoryState.empty : RefMiriMem).findGlobal? id = none := by
  dsimp only [Miri.Memory.MemoryState.findGlobal?,
    Miri.Memory.MemoryState.empty, Miri.Memory.KeyedArray.empty,
    Miri.Memory.KeyedArray.find?]
  rw [empty_hashmap_get?_none_v2 id.value]
  rfl

private theorem evalPlace_simpleDeref_rawMut_u8_v2 (rp : RefProg)
    (st : RefMiriState)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (dstPtr : Miri.Memory.Pointer Miri.Memory.Provenance)
    (h_pmd : st.machine.pendingMoveDeinit = false)
    (h_fr : st.stack.frames = Array.mk [frame])
    (h_dr : frame.extra.dataRace = none)
    (h_ptr : resolveTy rp.types
      (tyIdFor rp.types (.rawPtr .mut (.int .i8 false))) =
      some (.rawPtr .mut (.int .i8 false)))
    (h_get1 : frame.getLocal 1 =
      .ok ⟨.live (.immediate (.scalar
        (.fromPointer refRuntimeLayoutV2.base dstPtr))),
        some (refLocalLayoutForTyV2 rp.types
          (.rawPtr .mut (.int .i8 false)))⟩) :
    let u8Lay := refLocalLayoutForTyV2 rp.types (.int .i8 false)
    Miri.Interpreter.PlaceDynamic.evalPlace
        (Miri.Interpreter.ExecutionMachine.projectionHooks (refExecCfgV2 rp))
        0 ⟨1, Array.mk [Miri.MIR.ProjectionElem.Deref]⟩ true st =
      .ok ⟨.memory ⟨dstPtr.withOptionalProvenance, .none, none⟩, u8Lay⟩ st := by
  intro u8Lay
  let ptrTy := MirTy.rawPtr .mut (.int .i8 false)
  let ptrLay := refLocalLayoutForTyV2 rp.types ptrTy
  let ptrImm : Miri.Interpreter.Immediate Miri.Memory.Provenance :=
    .scalar (.fromPointer refRuntimeLayoutV2.base dstPtr)
  have h_cf := currentFrame_single_v2 st frame h_fr
  have h_fi := frameIndex_single_v2 (rp := rp) st frame h_fr
  have h_ptr_sized :
      (refLocalLayoutForTyV2 rp.types
        (.rawPtr .mut (.int .i8 false))).layout.isSized = true := rfl
  have h_lay :
      Miri.Interpreter.placeLayoutOfLocal
          (Miri.Interpreter.ExecutionMachine.projectionHooks
            (refExecCfgV2 rp)).place 0 1 st = .ok ptrLay st := by
    dsimp only [Miri.Interpreter.placeLayoutOfLocal, bind, Bind.bind,
      EStateM.bind, pure, Pure.pure, EStateM.pure]
    rw [projPlace_getFrame_eq_v2, h_cf]
    dsimp only
    rw [h_get1]
    rfl
  have h_ltp :
      Miri.Interpreter.localToPlace
          (Miri.Interpreter.ExecutionMachine.projectionHooks
            (refExecCfgV2 rp)).place 0 1 st =
        .ok ⟨.local 0 1 none frame.localsIdentity, ptrLay⟩ st := by
    dsimp only [Miri.Interpreter.localToPlace, bind, Bind.bind, EStateM.bind,
      pure, Pure.pure, EStateM.pure]
    rw [h_lay]
    dsimp only
    rw [h_ptr_sized, ite_true_eq, eStateM_bind_ok h_fi, projPlace_getFrame_eq_v2,
      eStateM_bind_ok h_cf]
    rfl
  let noDeref :
      Miri.Interpreter.PlaceMachine.CompilerHooks Unit RefUser Choice :=
    { refBaseCompilerHooks rp.types with
      layout := fun _ localId st =>
        match st.stack.currentFrame? with
        | none => .error (.stack .emptyStack) st
        | some frame =>
          match frame.body.locals[localId]? with
          | none => .error (.stack (.missingLocalType localId)) st
          | some tyId =>
            match refLayoutOfTyIdV2 rp.types tyId with
            | .ok l => .ok l st | .error e => .error e st
      projection := fun _ st =>
        .ok { refProjectionCxV2 rp.types with
          memoryOffset := Miri.Interpreter.projectionMemoryOffset
            refPointerArithmetic refResolvePointerPure
            st.machine.memory.getAllocInfo } st }
  let basePl := Miri.Interpreter.PlaceMachine.placeHooks
    (refAccessConfigV2 rp.types) refAllocationConfig noDeref
  have h_toOp :
      Miri.Interpreter.placeToOp basePl 0
          ⟨.local 0 1 none frame.localsIdentity, ptrLay⟩ st =
        .ok ⟨.immediate ptrImm, ptrLay⟩ st := by
    have h_fi' : basePl.frameIndex st = .ok 0 st := by
      dsimp only [basePl, Miri.Interpreter.PlaceMachine.placeHooks,
        bind, Bind.bind, EStateM.bind, get, getThe, MonadStateOf.get,
        EStateM.get, pure, Pure.pure, EStateM.pure, throw, throwThe,
        MonadExceptOf.throw, EStateM.throw, Miri.Interpreter.Stack.frameIndex]
      rw [h_fr]; rfl
    have h_op : frame.getLocalOperand 1 = .ok (.immediate ptrImm) := by
      dsimp only [Miri.Interpreter.Frame.getLocalOperand]; rw [h_get1]; rfl
    have h_ar := afterLocalRead_no_race_v2 st frame 1 h_fr h_dr
    have h_vip : noDeref.validationInProgress = (fun st => .ok false st) := rfl
    have h_lto : basePl.localToOp 0 1 st =
        .ok ⟨.immediate ptrImm, ptrLay⟩ st := by
      dsimp only [basePl, Miri.Interpreter.PlaceMachine.placeHooks,
        Miri.Interpreter.PlaceMachine.localToOp,
        Miri.Interpreter.PlaceMachine.localToOpCore,
        Miri.Interpreter.PlaceMachine.layoutLocal,
        bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
      rw [h_cf]; dsimp only
      rw [h_get1]; dsimp only [EStateM.pure, EStateM.bind]
      rw [h_cf]; dsimp only
      rw [h_op]; dsimp only [EStateM.pure, EStateM.bind]
      rw [h_ptr_sized]
      simp only [Bool.not_true, Bool.false_eq_true, ite_false]
      rw [h_vip]; dsimp only [EStateM.pure, EStateM.bind]
      simp only [Bool.false_eq_true, ite_false]
      rw [eStateM_bind_ok h_ar]
      rfl
    dsimp only [Miri.Interpreter.placeToOp, Miri.Interpreter.placeToOpCore,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    have h_dbg : basePl.debugAssertions = false := rfl
    rw [h_fi']
    dsimp only
    rw [show ((0 : Nat) != 0) = false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    rw [h_dbg]
    simp only [Bool.false_eq_true, ite_false]
    dsimp only [EStateM.bind, EStateM.pure]
    rw [h_lto]
  have h_ri :
      Miri.Interpreter.PlaceMachine.readImmediate (refAccessConfigV2 rp.types)
          ⟨.immediate ptrImm, ptrLay⟩ st =
        .ok ⟨ptrImm, ptrLay⟩ st := by
    cases st with | mk sk mc => cases mc with | mk m b d t r a u pmd =>
      dsimp only at h_pmd; subst h_pmd; rfl
  have h_from :
      refFromImmediatePtrV2 rp.types ⟨ptrImm, ptrLay⟩ st =
        .ok ⟨⟨dstPtr.withOptionalProvenance, .none, none⟩, u8Lay⟩ st := by
    dsimp only [refFromImmediatePtrV2, ptrLay, ptrTy, refLocalLayoutForTyV2]
    rw [h_ptr]
    simp only [show refTyLayoutFitsU64V2 (.int .i8 false) = true from rfl,
      Bool.not_true, Bool.false_eq_true, ite_false]
    have h_tp : (Miri.Memory.Scalar.fromPointer refRuntimeLayoutV2.base
        dstPtr).toPointer refRuntimeLayoutV2.base =
        .ok dstPtr.withOptionalProvenance := by cases dstPtr; rfl
    dsimp only [ptrImm, Miri.Interpreter.Immediate.toScalarAndMeta]
    rw [h_tp]
    dsimp only
    have h_mis : Miri.Interpreter.PointerPlaceMachine.misalignmentWith
        (refAccessConfigV2 rp.types) refAlignCtxV2 dstPtr.withOptionalProvenance
        u8Lay.layout.align.abi st = .ok none st := by
      dsimp only [Miri.Interpreter.PointerPlaceMachine.misalignmentWith,
        get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
        pure, Pure.pure, EStateM.pure, refAlignCtxV2]
      rw [show u8Lay.layout.align.abi.pow2 = 0 from rfl]
      rfl
    dsimp only [u8Lay, u8Ty, refLocalLayoutForTyV2] at h_mis
    rw [h_mis]
    rfl
  dsimp only [Miri.Interpreter.PlaceDynamic.evalPlace, bind, Bind.bind,
    EStateM.bind, pure, Pure.pure, EStateM.pure]
  rw [h_ltp]
  dsimp only
  rw [show (true && (Array.mk [Miri.MIR.ProjectionElem.Deref] ==
      Array.mk [Miri.MIR.ProjectionElem.Deref])) = true from rfl, ite_true_eq]
  change (match Miri.Interpreter.placeToOp basePl 0
      ⟨.local 0 1 none frame.localsIdentity, ptrLay⟩ st with
    | EStateM.Result.error e st1 => EStateM.Result.error e st1
    | EStateM.Result.ok op st1 =>
      if true = true then
        match Miri.Interpreter.PlaceMachine.readImmediate
            (refAccessConfigV2 rp.types) op st1 with
        | EStateM.Result.error e st2 => EStateM.Result.error e st2
        | EStateM.Result.ok val st2 =>
          match refFromImmediatePtrV2 rp.types val st2 with
          | EStateM.Result.error e st3 => EStateM.Result.error e st3
          | EStateM.Result.ok mp st3 =>
            EStateM.Result.ok
              (⟨.memory mp.mplace, mp.layout⟩ :
                Miri.Interpreter.RuntimePlace Miri.Memory.Provenance) st3
      else _) = _
  rw [h_toOp]
  dsimp only
  rw [ite_true_eq, h_ri]
  dsimp only
  rw [h_from]

private theorem mh_apply_bind_err {K U α β : Type}
    (x : Miri.Interpreter.MachineHooks.M K U α)
    (f : α → Miri.Interpreter.MachineHooks.M K U β)
    (e : Miri.Interpreter.StepError)
    (s s₁ : Miri.Interpreter.MachineHooks.State K U)
    (h : x s = .error e s₁) :
    (Bind.bind x f) s = .error e s₁ := by
  dsimp only [Bind.bind, EStateM.bind]; rw [h]

private theorem getPtrAllocMut_raw_err_v2 {P E K H X : Type}
    [DecidableEq K] (sz : Miri.ABI.Size) (signedSize : Int)
    (memory : Miri.Memory.MemoryState P E K) (hooks : H)
    (ptr : Miri.Memory.Pointer (Option P)) (kind : Option K)
    (global : Miri.Memory.GlobalAllocationHooks P E K H)
    (access : Miri.Memory.AllocationAccessHooks P E K H X)
    (aid : Miri.Memory.AllocId) (off : Miri.ABI.Size) (prov : X)
    (err : Miri.Memory.MemoryAccessError)
    (h_sz : Miri.Memory.sizeAsI64 sz = .ok signedSize)
    (h_nz : (signedSize != 0) = true)
    (h_res : access.resolvePointer memory hooks ptr signedSize =
      ⟨hooks, .ok (.ok ⟨aid, off, prov⟩)⟩)
    (h_raw : Miri.Memory.MemoryLifecycle.getAllocRawMut memory hooks aid kind
      global = ⟨memory, hooks, .error err⟩) :
    Miri.Memory.AllocationAccess.getPtrAllocMut memory hooks
        ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz false kind global access =
      ⟨memory, hooks, none, .error (.rawAccess err)⟩ := by
  dsimp only [Miri.Memory.AllocationAccess.getPtrAllocMut]
  change (match Miri.Memory.sizeAsI64 sz with
    | Except.ok _ => _ | Except.error _ => _) = _
  rw [h_sz]
  change (if ((signedSize != 0) = true) then _ else _) = _
  rw [h_nz, ite_true_eq]
  dsimp only [pure, Pure.pure, bind, Bind.bind]
  rw [h_res]
  dsimp only [pure, Pure.pure, bind, Bind.bind]
  simp only [ite_true]
  rw [h_raw]

private theorem getPlaceAllocMut_err_of_access_v2 {P E K H X : Type}
    [DecidableEq K]
    (memory memory' : Miri.Memory.MemoryState P E K) (hooks hooks' : H)
    (place : Miri.Interpreter.MemoryOperandPlace P)
    (ghost : Bool) (kind : Option K)
    (global : Miri.Memory.GlobalAllocationHooks P E K H)
    (access : Miri.Memory.AllocationAccessHooks P E K H X)
    (dynamic : Miri.Interpreter.DynamicLayoutResolver P E K H)
    (touched : Option (Miri.Memory.AllocationAccessRef P E))
    (err : Miri.Memory.PtrAllocationError)
    (sized : place.layout.backendRepr.isUnsized = false)
    (actual : Miri.Memory.AllocationAccess.getPtrAllocMut memory hooks
      ⟨Miri.ABI.Size.ofBytes 8⟩ place.mplace.ptr place.layout.size
      ghost kind global access =
      ⟨memory', hooks', touched, .error err⟩) :
    Miri.Interpreter.getPlaceAllocMut memory hooks place
        refRuntimeLayoutV2 ghost kind global access dynamic =
      ⟨memory', hooks', touched, .error (.pointerAccess err)⟩ := by
  cases place with
  | mk mplace layout =>
    cases mplace with
    | mk ptr metaVal misaligned =>
      cases layout with
      | mk sz al repr cty =>
        dsimp only at sized actual
        cases repr with
        | Scalar _ | ScalarPair | SimdVector | SimdScalableVector =>
          let r := Miri.Memory.AllocationAccess.getPtrAllocMut memory hooks
            ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access
          change ((match r.outcome with
            | Except.error error =>
              ⟨r.memory, r.hooks, r.touched, .error (.pointerAccess error)⟩
            | Except.ok reference? =>
              match misaligned with
              | some bad =>
                ⟨r.memory, r.hooks, r.touched,
                  .error (.pointerAccess (.access (.alignmentCheckFailed bad)))⟩
              | none => ⟨r.memory, r.hooks, r.touched, .ok reference?⟩) :
            Miri.Interpreter.MemoryOperandResult P E K H
              (Option (Miri.Memory.AllocationAccessRef P E))) = _
          dsimp only [r]
          rw [actual]
        | @Memory isSized =>
          cases isSized with
          | false => cases sized
          | true =>
            let r := Miri.Memory.AllocationAccess.getPtrAllocMut memory hooks
              ⟨Miri.ABI.Size.ofBytes 8⟩ ptr sz ghost kind global access
            change ((match r.outcome with
              | Except.error error =>
                ⟨r.memory, r.hooks, r.touched, .error (.pointerAccess error)⟩
              | Except.ok reference? =>
                match misaligned with
                | some bad =>
                  ⟨r.memory, r.hooks, r.touched,
                    .error (.pointerAccess (.access (.alignmentCheckFailed bad)))⟩
                | none => ⟨r.memory, r.hooks, r.touched, .ok reference?⟩) :
              Miri.Interpreter.MemoryOperandResult P E K H
                (Option (Miri.Memory.AllocationAccessRef P E))) = _
            dsimp only [r]
            rw [actual]

private theorem assign_deref_u8_const_absent_ub_v2 (rp : RefProg)
    (st : RefMiriState)
    (frame : Miri.Interpreter.Frame Miri.Memory.Provenance
      Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra)
    (bbId : BasicBlockId) (sIdx : Nat)
    (block : Miri.MIR.BasicBlock) (stmt : Miri.MIR.Statement)
    (dstId : Miri.Memory.AllocId) (v : Nat)
    (h_v : Miri.Memory.ScalarInt.tryFromUInt (BitVec.ofNat 128 v)
      (toMiriSize .i8) = .ok (some (miriScalar .i8 (BitVec.ofNat 128 v))))
    (h_pmd : st.machine.pendingMoveDeinit = false)
    (h_fr : st.stack.frames = Array.mk [frame])
    (h_dr : frame.extra.dataRace = none)
    (h_bt : st.machine.borrowTracker = none)
    (h_loc : frame.location = .mir ⟨bbId, sIdx⟩)
    (h_bb : frame.body.basicBlocks[bbId]? = some block)
    (h_st : block.statements[sIdx]? = some stmt)
    (h_kind : stmt.kind = .Assign ⟨1, Array.mk [Miri.MIR.ProjectionElem.Deref]⟩
      (toMiriRvalueV2 rp.types (.use (.constant
        ⟨tyIdFor rp.types (.int .i8 false), .scalar (BitVec.ofNat 128 v)⟩))))
    (h_get1 : frame.getLocal 1 =
      .ok ⟨.live (.immediate (.scalar (.fromPointer refRuntimeLayoutV2.base
        ⟨Miri.ABI.Size.ZERO, .concrete dstId Miri.Memory.BorTag.one⟩))),
        some (refLocalLayoutForTyV2 rp.types
          (.rawPtr .mut (.int .i8 false)))⟩)
    (h_u8 : MirSemantics.getElem? rp.types
      (tyIdFor rp.types (.int .i8 false)) = some (.int .i8 false))
    (h_ptr : resolveTy rp.types
      (tyIdFor rp.types (.rawPtr .mut (.int .i8 false))) =
      some (.rawPtr .mut (.int .i8 false)))
    (h_live_none : st.machine.memory.live.find? (fun e => e.1 == dstId) = none)
    (h_glob_none : st.machine.memory.findGlobal? dstId = none) :
    ∃ st' msg, Miri.Interpreter.ExecutionMachine.step
        (refExecutionConfigV2 rp) refLimitsV2 0 st =
      (st', .error (.undefinedBehavior msg)) := by
  let u8Ty := MirTy.int .i8 false
  let u8Lay := refLocalLayoutForTyV2 rp.types u8Ty
  let dstPtr : Miri.Memory.Pointer Miri.Memory.Provenance :=
    ⟨Miri.ABI.Size.ZERO, .concrete dstId Miri.Memory.BorTag.one⟩
  let dstMp : Miri.Interpreter.MemPlace Miri.Memory.Provenance :=
    ⟨dstPtr.withOptionalProvenance, .none, none⟩
  let valImm : Miri.Interpreter.Immediate Miri.Memory.Provenance :=
    .scalar (.fromScalarInt (miriScalar .i8 (BitVec.ofNat 128 v)))
  let err := Miri.Interpreter.MemoryErrors.operand
    (.pointerAccess (.rawAccess (.globalAccess (.notFound dstId))))
  have h_err_ub : ∃ msg, err = .undefinedBehavior msg := ⟨_, rfl⟩
  have h_ev := evalPlace_simpleDeref_rawMut_u8_v2 rp st frame dstPtr
    h_pmd h_fr h_dr h_ptr h_get1
  have h_op :
      (Miri.Interpreter.ExecutionMachine.rvalueHooks
          (refExecCfgV2 rp) refLimitsV2).evalOperandAt 0
          (Miri.Interpreter.OperandPath.rvalue "operand")
          (toMiriOperandV2 rp.types (.constant ⟨tyIdFor rp.types u8Ty,
            .scalar (BitVec.ofNat 128 v)⟩))
          (some u8Lay) st =
        .ok ⟨.immediate valImm, u8Lay⟩ st := by
    dsimp only [Miri.Interpreter.ExecutionMachine.rvalueHooks,
      Miri.Interpreter.OperandMachine.evalOperandAt,
      Miri.Interpreter.OperandMachine.evalOperand, toMiriOperandV2]
    rw [refStepCfgV2_eq, opHooks_deinitMovedPlace_v2]
    simp only [ite_true]
    dsimp only [bind, Bind.bind, EStateM.bind, modify, modifyGet,
      MonadStateOf.modifyGet, EStateM.modifyGet]
    rw [refState_with_pmd_false st h_pmd, opHooks_constantAt_v2]
    have h_ms :
        miriScalar .i8 (miriScalar .i8 (BitVec.ofNat 128 v)).data =
          miriScalar .i8 (BitVec.ofNat 128 v) := by
      have h1 :
          (miriScalar .i8 (miriScalar .i8 (BitVec.ofNat 128 v)).data).data =
            (miriScalar .i8 (BitVec.ofNat 128 v)).data := by
        rw [miriScalar_data, miriScalar_data, truncateBits_idem]
      have h2 :
          (miriScalar .i8 (miriScalar .i8 (BitVec.ofNat 128 v)).data).size =
            (miriScalar .i8 (BitVec.ofNat 128 v)).size := rfl
      cases hm1 : miriScalar .i8 (miriScalar .i8 (BitVec.ofNat 128 v)).data
      cases hm2 : miriScalar .i8 (BitVec.ofNat 128 v)
      rw [hm1, hm2] at h1 h2
      dsimp only [Miri.Memory.ScalarInt.data, Miri.Memory.ScalarInt.size]
        at h1 h2
      rw [h1, h2]
    have h_rc := refEvalConst_int_v2 rp.types st .i8 false
      (BitVec.ofNat 128 v).toNat (tyIdFor rp.types u8Ty)
      (miriScalar .i8 (BitVec.ofNat 128 v)) h_u8 (by
        rw [show BitVec.ofNat 128 (BitVec.ofNat 128 v).toNat =
            BitVec.ofNat 128 v from by
          apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]
          exact Nat.mod_mod _ _]
        exact h_v)
    rw [h_ms] at h_rc
    exact h_rc
  have h_res_ok :
      (Miri.Interpreter.PlaceMachine.accessHooks
          (refAccessConfigV2 rp.types)).resolvePointer
          st.machine.memory ⟨st.machine, none⟩ dstMp.ptr 1 =
        ⟨⟨st.machine, none⟩, .ok (.ok ⟨dstId, Miri.ABI.Size.ZERO,
          .concrete Miri.Memory.BorTag.one⟩)⟩ := by
    dsimp only [Miri.Interpreter.PlaceMachine.accessHooks]
    exact Miri.Interpreter.PlaceMachine.resolvePointer_ok
      (refAccessConfigV2 rp.types) st.machine.memory st.machine dstMp.ptr
      1 _ rfl
  have h_rawMut :
      Miri.Memory.MemoryLifecycle.getAllocRawMut st.machine.memory
          ⟨st.machine, none⟩ dstId none
          (refAccessConfigV2 rp.types).globalHooks =
        ⟨st.machine.memory, ⟨st.machine, none⟩,
          .error (.globalAccess (.notFound dstId))⟩ := by
    dsimp only [Miri.Memory.MemoryLifecycle.getAllocRawMut,
      Miri.Memory.MemoryLifecycle.getGlobalAlloc,
      refAccessConfigV2, refAccessConfig, refGlobalAllocationHooks,
      Id.run, bind, Bind.bind, pure, Pure.pure]
    rw [h_live_none, h_glob_none]
  have h_getPtrMut :
      Miri.Memory.AllocationAccess.getPtrAllocMut st.machine.memory
          ⟨st.machine, none⟩ ⟨Miri.ABI.Size.ofBytes 8⟩ dstMp.ptr
          (Miri.ABI.Size.ofBytes 1) false none
          (refAccessConfigV2 rp.types).globalHooks
          (Miri.Interpreter.PlaceMachine.accessHooks
            (refAccessConfigV2 rp.types)) =
        ⟨st.machine.memory, ⟨st.machine, none⟩, none,
          .error (.rawAccess (.globalAccess (.notFound dstId)))⟩ :=
    getPtrAllocMut_raw_err_v2 (Miri.ABI.Size.ofBytes 1) 1
      st.machine.memory ⟨st.machine, none⟩ dstMp.ptr none
      (refAccessConfigV2 rp.types).globalHooks
      (Miri.Interpreter.PlaceMachine.accessHooks
        (refAccessConfigV2 rp.types))
      dstId Miri.ABI.Size.ZERO (.concrete Miri.Memory.BorTag.one)
      (.globalAccess (.notFound dstId)) rfl rfl h_res_ok h_rawMut
  let u8MemLay : Miri.Interpreter.MemoryOperandLayout :=
    ⟨Miri.ABI.Size.ofBytes 1, Miri.ABI.Align.ONE,
      .Scalar (.Initialized (value := .Int .I8 false)
        (validRange := refFullWrappingRangeSize (Miri.ABI.Size.ofBytes 1))),
      some u8Lay.ty⟩
  have h_lml : Miri.Interpreter.localMemoryLayout u8Lay = u8MemLay := rfl
  have h_placeMut :
      Miri.Interpreter.getPlaceAllocMut st.machine.memory
          ⟨st.machine, none⟩ ⟨dstMp, u8MemLay⟩
          refRuntimeLayoutV2 false none
          (refAccessConfigV2 rp.types).globalHooks
          (Miri.Interpreter.PlaceMachine.accessHooks
            (refAccessConfigV2 rp.types))
          (refAccessConfigV2 rp.types).dynamicLayout =
        ⟨st.machine.memory, ⟨st.machine, none⟩, none,
          .error (.pointerAccess (.rawAccess (.globalAccess
            (.notFound dstId))))⟩ :=
    getPlaceAllocMut_err_of_access_v2 _ _ _ _ _ _ _ _ _ _ _ _ rfl h_getPtrMut
  have h_wrImm :
      Miri.Interpreter.writeImmediateToMplaceNoValidate st.machine.memory
          ⟨st.machine, none⟩ valImm
          ⟨dstMp, Miri.Interpreter.localMemoryLayout u8Lay⟩
          (refAccessConfigV2 rp.types).runtime false none
          (refAccessConfigV2 rp.types).globalHooks
          (Miri.Interpreter.PlaceMachine.accessHooks
            (refAccessConfigV2 rp.types))
          (refAccessConfigV2 rp.types).dynamicLayout
          (refBaseCompilerHooksV2 rp.types).willValidateMemory =
        ⟨st.machine.memory, ⟨st.machine, none⟩, none,
          .error (.pointerAccess (.rawAccess (.globalAccess
            (.notFound dstId))))⟩ := by
    rw [show (refAccessConfigV2 rp.types).runtime = refRuntimeLayoutV2 from rfl,
      h_lml]
    dsimp only [Miri.Interpreter.writeImmediateToMplaceNoValidate, Id.run,
      bind, Bind.bind, pure, Pure.pure]
    rw [h_placeMut]
    rfl
  have h_wrMem :
      (Miri.Interpreter.ExecutionMachine.projectionHooks
          (refExecCfgV2 rp)).place.writeMemoryNoValidate 0 valImm
          ⟨dstMp, u8Lay⟩ st =
        .error err st := by
    change Miri.Interpreter.PlaceMachine.writeMemory (refAccessConfigV2 rp.types)
      (refBaseCompilerHooksV2 rp.types).willValidateMemory valImm
      ⟨dstMp, u8Lay⟩ st = .error err st
    dsimp only [Miri.Interpreter.PlaceMachine.writeMemory,
      get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind,
      EStateM.bind, pure, Pure.pure, EStateM.pure]
    rw [show (refAccessConfigV2 rp.types).ghostMode = false from rfl,
      show (refAccessConfigV2 rp.types).globalKind = none from rfl,
      h_wrImm]
    dsimp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
      throw, MonadExceptOf.throw, EStateM.throw]
    rfl
  have h_rr :
      (refExecCfgV2 rp).copy.readRaw 0 ⟨.immediate valImm, u8Lay⟩ st =
        .ok (.immediate ⟨valImm, Miri.Interpreter.localMemoryLayout u8Lay⟩)
          st := rfl
  have h_cp_err :
      Miri.Interpreter.copyRuntimePlace
          (Miri.Interpreter.ExecutionMachine.projectionHooks
            (refExecCfgV2 rp)).place
          (refExecCfgV2 rp).copy 0 ⟨.immediate valImm, u8Lay⟩
          ⟨.memory dstMp, u8Lay⟩ false st =
        .error err st := by
    dsimp only [Miri.Interpreter.copyRuntimePlace,
      Miri.Interpreter.copyRuntimePlaceNoValidate,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    have h_compat : (refExecCfgV2 rp).copy.compatible u8Lay u8Lay = .ok true := by
      dsimp only [refExecCfgV2, Miri.Interpreter.ExecutionMachine.withValidation,
        Miri.Interpreter.TypedMachineBindings.bindValidation,
        refExecutionConfigV2, refPlaceCopyHooksV2]
      rw [beq_self_eq_true]
    have h_pad : (refExecCfgV2 rp).copy.hasPadding u8Lay = .ok false := by
      dsimp only [refExecCfgV2, Miri.Interpreter.ExecutionMachine.withValidation,
        Miri.Interpreter.TypedMachineBindings.bindValidation,
        refExecutionConfigV2, refPlaceCopyHooksV2, refHasPaddingV2, u8Lay, u8Ty]
      rfl
    have h_tpd :
        (Miri.Interpreter.ExecutionMachine.projectionHooks
            (refExecCfgV2 rp)).place.takePendingMoveDeinit st =
          .ok false st := by
      dsimp only [Miri.Interpreter.ExecutionMachine.projectionHooks,
        Miri.Interpreter.PlaceMachine.takePendingMoveDeinit,
        Miri.Interpreter.MachineHooks.takeLastPendingMoveDeinit]
      cases st with | mk sk mc => cases mc with | mk m b d t r a u pmd =>
        dsimp only at h_pmd; subst h_pmd; rfl
    rw [h_compat, Miri.Interpreter.placeLift_ok]
    dsimp only [pure, Pure.pure, EStateM.pure]
    simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false]
    rw [h_pad, Miri.Interpreter.placeLift_ok]
    dsimp only [pure, Pure.pure, EStateM.pure, EStateM.bind]
    rw [h_tpd]
    dsimp only
    rw [ite_false_eq]
    dsimp only [EStateM.bind]
    rw [show Miri.Interpreter.PlaceCopyHooks.readRaw (refExecCfgV2 rp).copy 0
        ⟨.immediate valImm, u8Lay⟩ st =
        .ok (.immediate ⟨valImm, Miri.Interpreter.localMemoryLayout u8Lay⟩) st
      from h_rr]
    dsimp only [Miri.Interpreter.writePlaceImmediate,
      Miri.Interpreter.writePlaceImmediateNoValidate,
      Miri.Interpreter.asMplaceOrMutableLocal,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    rw [show u8Lay.layout.size = Miri.ABI.Size.ofBytes 1 from rfl,
      show u8Lay.layout.isSized = true from rfl]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false,
      bne_self_eq_false, Bool.or_self, ite_true]
    dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
    rw [h_wrMem]
  have h_ass_err :
      (Miri.Interpreter.ExecutionMachine.stepHooks
          (refExecutionConfigV2 rp) refLimitsV2).assign 0
          ⟨1, Array.mk [Miri.MIR.ProjectionElem.Deref]⟩
          (toMiriRvalueV2 rp.types (.use (.constant ⟨tyIdFor rp.types u8Ty,
            .scalar (BitVec.ofNat 128 v)⟩))) st =
        (st, .error err) := by
    dsimp only [Miri.Interpreter.ExecutionMachine.stepHooks,
      Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run,
      Miri.Interpreter.evalRvalueIntoPlace,
      toMiriRvalueV2, bind, Bind.bind, EStateM.bind,
      pure, Pure.pure, EStateM.pure]
    rw [show Miri.Interpreter.ExecutionMachine.withValidation
        (refExecutionConfigV2 rp) refLimitsV2 = refExecCfgV2 rp from rfl]
    dsimp only [Miri.Interpreter.ExecutionMachine.rvalueHooks]
    rw [refStepCfgV2_eq, h_ev]
    dsimp only [Miri.Interpreter.RuntimePlace.layout]
    have h_op' := h_op
    dsimp only [Miri.Interpreter.ExecutionMachine.rvalueHooks, u8Lay, u8Ty]
      at h_op'
    rw [refStepCfgV2_eq] at h_op'
    have h_cp' := h_cp_err
    dsimp only [u8Lay, u8Ty] at h_cp'
    rw [h_op']
    dsimp only [Miri.Interpreter.MachineHooks.withRetagMode]
    rw [show (Miri.MIR.WithRetag.No == Miri.MIR.WithRetag.Yes) = false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    rw [h_bt, h_cp']
  have h_step := execStep_assign_err rp st st frame bbId sIdx block stmt
    ⟨1, Array.mk [Miri.MIR.ProjectionElem.Deref]⟩
    (toMiriRvalueV2 rp.types (.use (.constant ⟨tyIdFor rp.types u8Ty,
      .scalar (BitVec.ofNat 128 v)⟩)))
    err h_pmd h_fr h_loc h_bb h_st h_kind h_ass_err
  let ⟨msg, h_msg⟩ := h_err_ub
  rw [h_msg] at h_step
  exact ⟨_, msg, h_step⟩

private theorem ref_firstStep_blocked_no_behavior_v2 (rp : RefProg) (q : Query)
    (rs0 : RefState)
    (h_s0_eq : rs0.stepsExecuted = 0)
    (h_init : ∀ ms : Nat, initRefStateV2 rp q ms =
      .ok { rs0 with maxSteps := ms })
    (h_blk :
      evalRefCoreV2 rp rs0.retTy rs0.retPlace rs0.miri = .blocked) :
    (∃ ms : Nat, RefReachesOutcomeV2 rp q ms .blocked) ∧
    ¬ RefWellFormedV2 rp q ∧
    (∀ out : TerminalOut, ¬ RefBehaviorV2 rp q out) := by
  have h_step0 : ∀ ms : Nat, (Nat.blt rs0.stepsExecuted ms = true) →
      ∀ c, ValidRefChoice rp { rs0 with maxSteps := ms } c →
      evalRefStepV2 rp c { rs0 with maxSteps := ms } = .blocked := by
    intro ms h_lt c hc
    have hc0 : c = 0 := hc
    subst hc0
    rw [evalRefStepV2_eq_liftCore_of_lt rp { rs0 with maxSteps := ms } h_lt]
    dsimp only
    rw [h_blk]
    rfl
  have h_not_run : ∀ ms c rs',
      ValidRefChoice rp { rs0 with maxSteps := ms } c →
      evalRefStepV2 rp c { rs0 with maxSteps := ms } = .running rs' → False := by
    intro ms c rs' hc h_ev
    have hc0 : c = 0 := hc
    subst hc0
    cases h_lt : Nat.blt rs0.stepsExecuted ms with
    | false =>
      rw [evalRefStepV2_eq_exhausted_of_ge rp { rs0 with maxSteps := ms } h_lt]
        at h_ev
      cases h_ev
    | true =>
      rw [h_step0 ms h_lt 0 hc] at h_ev
      cases h_ev
  have h_reach_id : ∀ ms rs,
      RefReachesV2 rp { rs0 with maxSteps := ms } rs →
      rs = { rs0 with maxSteps := ms } := by
    intro ms rs h_r
    induction h_r with
    | refl => rfl
    | @tail rs2 rs3 _ h_step ih =>
      rw [ih] at h_step
      let ⟨c, hc, h_ev⟩ := h_step
      exact False.elim (h_not_run ms c rs3 hc h_ev)
  let ms1 := rs0.stepsExecuted + 1
  have h_blt1 : Nat.blt rs0.stepsExecuted ms1 = true := by
    rw [h_s0_eq]; rfl
  have h_out_blk : RefReachesOutcomeV2 rp q ms1 .blocked := by
    dsimp only [RefReachesOutcomeV2]
    rw [h_init ms1]
    exact ⟨{ rs0 with maxSteps := ms1 },
      RefReachesV2.refl { rs0 with maxSteps := ms1 },
      0, rfl, h_step0 ms1 h_blt1 0 rfl⟩
  refine ⟨⟨ms1, h_out_blk⟩, fun h_rwf => (h_rwf ms1).2.2 h_out_blk, ?_⟩
  intro out ⟨ms, h_r⟩
  dsimp only [RefReachesOutcomeV2] at h_r
  rw [h_init ms] at h_r
  let ⟨rs, h_reach, c, hc, h_ev⟩ := h_r
  have h_rid := h_reach_id ms rs h_reach
  rw [h_rid] at hc h_ev
  have hc0 : c = 0 := hc
  subst hc0
  cases h_lt : Nat.blt rs0.stepsExecuted ms with
  | false =>
    rw [evalRefStepV2_eq_exhausted_of_ge rp { rs0 with maxSteps := ms } h_lt]
      at h_ev
    cases h_ev
  | true =>
    rw [h_step0 ms h_lt 0 hc] at h_ev
    cases h_ev

private theorem mulWithOverflow_isize_1_1_v2 :
    Miri.Interpreter.IntegerOps.binary .MulWithOverflow
        ⟨miriScalar .isize 1,
          ⟨Miri.ABI.Size.ofBytes 8, toMiriIntKind .isize true⟩⟩
        ⟨miriScalar .isize 1,
          ⟨Miri.ABI.Size.ofBytes 8, toMiriIntKind .isize true⟩⟩ =
      .ok (.withOverflow (miriScalar .isize 1) false) := by
  have h_tf1 : Miri.Memory.ScalarInt.truncateFromInt (BitVec.ofInt 128 1).toInt
      (toMiriSize .isize) =
      match Miri.Memory.ScalarInt.truncateFromUInt
          (BitVec.ofInt 128 (BitVec.ofInt 128 1).toInt)
          (toMiriSize .isize) with
      | .ok (sc, _) =>
        match (toMiriSize .isize).signExtend sc.data with
        | .ok decoded => .ok (sc, decoded != (BitVec.ofInt 128 1).toInt)
        | .error e => .error (.sizeError e)
      | .error e => .error e := by
    let x := (BitVec.ofInt 128 1).toInt
    have h_rng : (decide (x < Neg.neg (HPow.hPow (2 : Int) 127)) ||
        decide (x ≥ HPow.hPow (2 : Int) 127)) = false := by
      dsimp only [x]; simp only [bitVec_ofInt_eq]; decide
    dsimp only [Miri.Memory.ScalarInt.truncateFromInt, bind, Bind.bind,
      Except.bind, pure, Pure.pure, Except.pure]
    change (if (decide (x < Neg.neg (HPow.hPow (2 : Int) 127)) ||
        decide (x ≥ HPow.hPow (2 : Int) 127)) = true then _ else _) = _
    rw [h_rng]; simp only [Bool.false_eq_true, ite_false]; rfl
  have h_d1 : Miri.Interpreter.IntegerOps.decode ⟨miriScalar .isize 1,
      ⟨Miri.ABI.Size.ofBytes 8, toMiriIntKind .isize true⟩⟩ = .ok 1 := by
    change Miri.Interpreter.IntegerOps.decode
      (miriIntValue ⟨.isize, true, 1⟩) = _
    rw [integerOps_decode_eq]; rfl
  have h_ib : Miri.Interpreter.IntegerOps.binary .MulWithOverflow
      ⟨miriScalar .isize 1,
        ⟨Miri.ABI.Size.ofBytes 8, toMiriIntKind .isize true⟩⟩
      ⟨miriScalar .isize 1,
        ⟨Miri.ABI.Size.ofBytes 8, toMiriIntKind .isize true⟩⟩ =
      match Miri.Memory.ScalarInt.truncateFromInt (BitVec.ofInt 128 1).toInt
          (toMiriSize .isize) with
      | .ok (value, lossy) =>
        .ok (.withOverflow value
          ((decide ((1 : Int) < Neg.neg (HPow.hPow (2 : Int) 127)) ||
            decide ((1 : Int) ≥ HPow.hPow (2 : Int) 127)) || lossy))
      | .error e => .error (.scalar e) := by
    dsimp only [Miri.Interpreter.IntegerOps.binary, bind, Bind.bind,
      Except.bind, pure, Pure.pure, Except.pure]
    rfl
  rw [h_ib, h_tf1, bitVec_ofInt_eq, bitVec_ofInt_eq,
    truncateFromUInt_eq_miriScalar .isize (bvOfInt 128 (bvOfInt 128 1).toInt)]
  dsimp only
  rw [miriScalar_data, size_signExtend_eq]
  dsimp only
  rw [show miriScalar .isize (bvOfInt 128 (bvOfInt 128 1).toInt) =
      miriScalar .isize 1 from by decide]
  rw [show ((decide ((1 : Int) < Neg.neg (HPow.hPow (2 : Int) 127)) ||
      decide ((1 : Int) ≥ HPow.hPow (2 : Int) 127)) ||
      (signExtendBits .isize (truncateBits .isize
        (bvOfInt 128 (bvOfInt 128 1).toInt)) != (bvOfInt 128 1).toInt)) =
      false from by decide]

/-- Regression witness covering entry caller-only reference validation and full
provenance-freshness isolation (`CallerMemory` allocation ids, `CallerMemory`
byte provenances across live and dead allocations, and argument pointer
provenances):
1. Dangling caller references (`&()` and 0-length `&[u8]`) targeting `allocId`
   `1` fault `.undefined` / `.ub` against caller-only memory rather than
   resolving to `retPlace`.
2. Dangling raw-pointer stores (`*_1 = 7`) targeting `allocId` `1` fault
   `.undefined` / `.ub` (`PointerUseAfterFree`), and non-zero offsets
   (`_1.offset(1)`) fault `.undefined` in Anneal and block cleanly (`.blocked`,
   `¬ RefWellFormedV2`, `∀ out, ¬ RefBehaviorV2 ... out`) in `M_ref` via
   `ExecutionScalar`'s `.unavailable` handling rather than aliasing `retPlace`.
3. Dangling raw-pointer stores targeting `allocId` `2` fault `.undefined` /
   `.ub` even after a callee stack local is promoted via `&raw const _2`.
4. Live and dead caller allocations carrying byte provenances `1` and `4` keep
   `retPlace` (`allocId = 5`) and `nextAllocId` (`6`) disjoint from all caller
   byte-provenance ids. -/
theorem profileV2_entry_ref_and_provenance_isolation :
    let u8Ty := MirTy.int .i8 false
    let sliceU8Ty := MirTy.slice u8Ty
    let progRefUnit := mkV2Prog {
      identity := "v2_entry_dangling_ref_unit"
      argumentCount := 1
      locals := [.unit, .ref .shared .unit]
      basicBlocks := [{ statements := [], terminator := .return_ }]
    }
    let progRefSlice0 := mkV2Prog {
      identity := "v2_entry_dangling_ref_slice0"
      argumentCount := 1
      locals := [.unit, .ref .shared sliceU8Ty]
      basicBlocks := [{ statements := [], terminator := .return_ }]
    }
    let qRefUnit : Query := {
      args := [.ptr ⟨some 1, 0, .isize⟩]
      callerMem := ⟨[]⟩
    }
    let qRefSlice0 : Query := {
      args := [.slicePtr ⟨some 1, 0, .isize⟩ 0]
      callerMem := ⟨[]⟩
    }
    let progRawWrite1 := mkV2Prog {
      identity := "v2_dangling_raw_write_ret_alias"
      argumentCount := 1
      locals := [u8Ty, .rawPtr .mut u8Ty]
      basicBlocks := [{
        statements := [
          .assign ⟨1, [.deref]⟩
            (.use (.constant ⟨u8Ty, .scalar (BitVec.ofNat 128 7)⟩)),
          .assign ⟨0, []⟩
            (.use (.constant ⟨u8Ty, .scalar (BitVec.ofNat 128 0)⟩))
        ]
        terminator := .return_
      }]
    }
    let progRawOff1 := mkV2Prog {
      identity := "v2_dangling_raw_offset_ret_alias"
      argumentCount := 1
      locals := [.rawPtr .shared u8Ty, .rawPtr .shared u8Ty]
      basicBlocks := [{
        statements := [
          .assign ⟨0, []⟩
            (.binaryOp .offset (.copy ⟨1, []⟩)
              (.constant ⟨.int .isize true, .scalar (BitVec.ofNat 128 1)⟩))
        ]
        terminator := .return_
      }]
    }
    let qRaw1 : Query := {
      args := [.ptr ⟨some 1, 0, .isize⟩]
      callerMem := ⟨[]⟩
    }
    let progStackRaw := mkV2Prog {
      identity := "v2_dangling_raw_stack_alias"
      argumentCount := 1
      locals := [u8Ty, .rawPtr .mut u8Ty, .unit, .rawPtr .shared .unit]
      basicBlocks := [{
        statements := [
          .assign ⟨3, []⟩ (.addressOf .shared ⟨2, []⟩),
          .assign ⟨1, [.deref]⟩
            (.use (.constant ⟨u8Ty, .scalar (BitVec.ofNat 128 99)⟩)),
          .assign ⟨0, []⟩
            (.use (.constant ⟨u8Ty, .scalar (BitVec.ofNat 128 0)⟩))
        ]
        terminator := .return_
      }]
    }
    let qRaw2 : Query := {
      args := [.ptr ⟨some 2, 0, .isize⟩]
      callerMem := ⟨[]⟩
    }
    let alByteLive : Trusted.MirSemantics.Allocation := {
      allocId := 2, alignLog2 := 3, mutability := .mut,
      bytes := List.replicate 8 (.init 0 (some 4)), live := true
    }
    let alByteDead : Trusted.MirSemantics.Allocation := {
      allocId := 3, alignLog2 := 0, mutability := .shared,
      bytes := [.init 0 (some 1)], live := false
    }
    let cmByteProv : CallerMemory := ⟨[alByteLive, alByteDead]⟩
    (ReachesResultV2 progRefUnit qRefUnit (.fault .undefined) ∧
      ¬ WellFormedV2 progRefUnit qRefUnit ∧
      (∀ ms : Nat,
        initRefStateV2 (encodeProg progRefUnit) qRefUnit ms = .error .undefined) ∧
      (∃ ms : Nat, RefReachesOutcomeV2 (encodeProg progRefUnit) qRefUnit ms .ub) ∧
      ¬ RefWellFormedV2 (encodeProg progRefUnit) qRefUnit) ∧
    (ReachesResultV2 progRefSlice0 qRefSlice0 (.fault .undefined) ∧
      ¬ WellFormedV2 progRefSlice0 qRefSlice0 ∧
      (∀ ms : Nat,
        initRefStateV2 (encodeProg progRefSlice0) qRefSlice0 ms =
          .error .undefined) ∧
      (∃ ms : Nat,
        RefReachesOutcomeV2 (encodeProg progRefSlice0) qRefSlice0 ms .ub) ∧
      ¬ RefWellFormedV2 (encodeProg progRefSlice0) qRefSlice0) ∧
    (ReachesResultV2 progRawWrite1 qRaw1 (.fault .undefined) ∧
      ¬ WellFormedV2 progRawWrite1 qRaw1 ∧
      (∃ ms : Nat,
        RefReachesOutcomeV2 (encodeProg progRawWrite1) qRaw1 ms .ub) ∧
      ¬ RefWellFormedV2 (encodeProg progRawWrite1) qRaw1) ∧
    (ReachesResultV2 progRawOff1 qRaw1 (.fault .undefined) ∧
      ¬ WellFormedV2 progRawOff1 qRaw1 ∧
      (∃ ms : Nat,
        RefReachesOutcomeV2 (encodeProg progRawOff1) qRaw1 ms .blocked) ∧
      ¬ RefWellFormedV2 (encodeProg progRawOff1) qRaw1 ∧
      (∀ out : TerminalOut,
        ¬ RefBehaviorV2 (encodeProg progRawOff1) qRaw1 out)) ∧
    (ReachesResultV2 progStackRaw qRaw2 (.fault .undefined) ∧
      ¬ WellFormedV2 progStackRaw qRaw2 ∧
      (∃ ms : Nat,
        RefReachesOutcomeV2 (encodeProg progStackRaw) qRaw2 ms .ub) ∧
      ¬ RefWellFormedV2 (encodeProg progStackRaw) qRaw2) ∧
    (∃ st : RefState,
      initRefStateV2 (encodeProg progV2UnitNoop)
        { args := [], callerMem := cmByteProv } 1 = .ok st ∧
      st.retPlace.mplace.ptr.provenance =
        some (Miri.Memory.Provenance.concrete ⟨5, by decide⟩
          Miri.Memory.BorTag.one) ∧
      st.miri.machine.memory.nextAllocId = 6) := by
  intro u8Ty sliceU8Ty progRefUnit progRefSlice0 qRefUnit qRefSlice0
    progRawWrite1 progRawOff1 qRaw1 progStackRaw qRaw2
    alByteLive alByteDead cmByteProv
  have h_a1_f :=
    fault_and_exclusive_of_execFaultV2 (p := progRefUnit) (q := qRefUnit)
      (fuel := 1) (expected := .undefined) rfl
  have h_b1_f :=
    fault_and_exclusive_of_execFaultV2 (p := progRefSlice0) (q := qRefSlice0)
      (fuel := 1) (expected := .undefined) rfl
  have h_2a_f :=
    fault_and_exclusive_of_execFaultV2 (p := progRawWrite1) (q := qRaw1)
      (fuel := 2) (expected := .undefined) rfl
  have h_2b_f :=
    fault_and_exclusive_of_execFaultV2 (p := progRawOff1) (q := qRaw1)
      (fuel := 2) (expected := .undefined) rfl
  have h_3_f :=
    fault_and_exclusive_of_execFaultV2 (p := progStackRaw) (q := qRaw2)
      (fuel := 4) (expected := .undefined) rfl
  have h_ref_unit_init : ∀ ms : Nat,
      initRefStateV2 (encodeProg progRefUnit) qRefUnit ms =
        .error .undefined := by
    intro ms
    let rp := encodeProg progRefUnit
    let ⟨rawRet, h_raw, _⟩ :=
      refTryNew_spec_v2 Miri.ABI.Size.ZERO Miri.ABI.Align.ONE 1 rfl rfl
    dsimp only [initRefStateV2]
    rw [show (!Nat.beq rp.pointerWidthBits 64 ||
        !Nat.beq rp.mirProfileVersion 2) = false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    rw [show (!refValidCallerMemoryV2 qRefUnit.callerMem) = false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    rw [show Trusted.MirSemantics.getElem? rp.bodies rp.entryDefId =
        some (@GetElem.getElem _ Nat _ _ _ rp.bodies 0 (by decide)) from rfl]
    dsimp only
    rw [show decodeLocalTys rp.types
        (@GetElem.getElem _ Nat _ _ _ rp.bodies 0 (by decide)).locals =
        some [.unit, .ref .shared .unit] from rfl]
    dsimp only
    rw [show (let rbody := @GetElem.getElem _ Nat _ _ _ rp.bodies 0 (by decide)
        rbody.basicBlocks.isEmpty ||
        !Nat.blt rbody.argumentCount
          ([MirTy.unit, MirTy.ref .shared .unit] : List MirTy).length ||
        !refStorageAnnotationsInBounds rbody ||
        !refDiscriminantTypesValid [.unit, .ref .shared .unit] rbody ||
        !refCastTypesValid rp.types [.unit, .ref .shared .unit] rbody ||
        ![MirTy.unit, MirTy.ref .shared .unit].all refIsSupportedLocalTyV2 ||
        ![MirTy.unit, MirTy.ref .shared .unit].all refTyLayoutFitsU64V2) =
        false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    rw [show (let rbody := @GetElem.getElem _ Nat _ _ _ rp.bodies 0 (by decide)
        !checkRefArgsMatchV2 qRefUnit.args
          (([MirTy.unit, MirTy.ref .shared .unit].drop 1).take
            rbody.argumentCount) ||
        !refValListAllocIdsFitU64V2 qRefUnit.args) = false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    rw [show Trusted.MirSemantics.getElem?
        ([MirTy.unit, MirTy.ref .shared .unit] : List MirTy) 0 =
        (some MirTy.unit : Option MirTy) from rfl]
    dsimp only [refInitCallerMemoryV2, refOwnLayoutFitsU64V2]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    rw [show (refLocalLayoutForTyV2 rp.types .unit).layout.size =
        Miri.ABI.Size.ZERO from rfl,
      show (refLocalLayoutForTyV2 rp.types .unit).layout.align.abi =
        Miri.ABI.Align.ONE from rfl, h_raw]
    rfl
  have h_ref_slice_init : ∀ ms : Nat,
      initRefStateV2 (encodeProg progRefSlice0) qRefSlice0 ms =
        .error .undefined := by
    intro ms
    let rp := encodeProg progRefSlice0
    let ⟨rawRet, h_raw, _⟩ :=
      refTryNew_spec_v2 Miri.ABI.Size.ZERO Miri.ABI.Align.ONE 1 rfl rfl
    dsimp only [initRefStateV2]
    rw [show (!Nat.beq rp.pointerWidthBits 64 ||
        !Nat.beq rp.mirProfileVersion 2) = false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    rw [show (!refValidCallerMemoryV2 qRefSlice0.callerMem) = false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    rw [show Trusted.MirSemantics.getElem? rp.bodies rp.entryDefId =
        some (@GetElem.getElem _ Nat _ _ _ rp.bodies 0 (by decide)) from rfl]
    dsimp only
    rw [show decodeLocalTys rp.types
        (@GetElem.getElem _ Nat _ _ _ rp.bodies 0 (by decide)).locals =
        some [.unit, .ref .shared sliceU8Ty] from rfl]
    dsimp only
    rw [show (let rbody := @GetElem.getElem _ Nat _ _ _ rp.bodies 0 (by decide)
        rbody.basicBlocks.isEmpty ||
        !Nat.blt rbody.argumentCount
          ([MirTy.unit, MirTy.ref .shared sliceU8Ty] : List MirTy).length ||
        !refStorageAnnotationsInBounds rbody ||
        !refDiscriminantTypesValid [.unit, .ref .shared sliceU8Ty] rbody ||
        !refCastTypesValid rp.types [.unit, .ref .shared sliceU8Ty] rbody ||
        ![MirTy.unit, MirTy.ref .shared sliceU8Ty].all
          refIsSupportedLocalTyV2 ||
        ![MirTy.unit, MirTy.ref .shared sliceU8Ty].all refTyLayoutFitsU64V2) =
        false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    rw [show (let rbody := @GetElem.getElem _ Nat _ _ _ rp.bodies 0 (by decide)
        !checkRefArgsMatchV2 qRefSlice0.args
          (([MirTy.unit, MirTy.ref .shared sliceU8Ty].drop 1).take
            rbody.argumentCount) ||
        !refValListAllocIdsFitU64V2 qRefSlice0.args) = false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    rw [show Trusted.MirSemantics.getElem?
        ([MirTy.unit, MirTy.ref .shared sliceU8Ty] : List MirTy) 0 =
        (some MirTy.unit : Option MirTy) from rfl]
    dsimp only [refInitCallerMemoryV2, refOwnLayoutFitsU64V2]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    rw [show (refLocalLayoutForTyV2 rp.types .unit).layout.size =
        Miri.ABI.Size.ZERO from rfl,
      show (refLocalLayoutForTyV2 rp.types .unit).layout.align.abi =
        Miri.ABI.Align.ONE from rfl, h_raw]
    rfl
  let ⟨h_u_ub, h_u_nwf, _, _, _⟩ := ref_ub_of_init_error h_ref_unit_init
  let ⟨h_s_ub, h_s_nwf, _, _, _⟩ := ref_ub_of_init_error h_ref_slice_init
  have h_2a_ref :
      (∃ ms : Nat,
        RefReachesOutcomeV2 (encodeProg progRawWrite1) qRaw1 ms .ub) ∧
      ¬ RefWellFormedV2 (encodeProg progRawWrite1) qRaw1 := by
    let rp := encodeProg progRawWrite1
    let rbody := @GetElem.getElem _ Nat _ _ _ rp.bodies 0 (by decide)
    let u8Lay := refLocalLayoutForTyV2 rp.types u8Ty
    let ptrLay := refLocalLayoutForTyV2 rp.types (.rawPtr .mut u8Ty)
    let ⟨rawRet, h_raw, _⟩ :=
      refTryNew_spec_v2 (Miri.ABI.Size.ofBytes 1) Miri.ABI.Align.ONE 1 rfl rfl
    let retPtr : Miri.Memory.Pointer (Option Miri.Memory.Provenance) :=
      ⟨Miri.ABI.Size.ZERO, some (.concrete alloc2IdV2 Miri.Memory.BorTag.one)⟩
    let retPlace : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance :=
      ⟨⟨retPtr, .none, none⟩, u8Lay⟩
    let mem0 : RefMiriMem :=
      ({ (Miri.Memory.MemoryState.empty : RefMiriMem) with
          nextAllocId := 3
          live := Array.mk [(alloc2IdV2, ⟨.stack, rawRet.withExtra
            (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
              (Miri.ABI.Size.ofBytes 1))⟩)] }).setIssuedIds
        (Array.mk [alloc2IdV2])
    let ptr1Imm : Miri.Interpreter.Immediate Miri.Memory.Provenance :=
      .scalar (.fromPointer refRuntimeLayoutV2.base
        ⟨Miri.ABI.Size.ZERO, .concrete retAllocIdV2 Miri.Memory.BorTag.one⟩)
    let frame0 := mkRefMiriFrameV2 rp.types 0 rbody 0 0
      [⟨.live (.immediate .uninit), some u8Lay⟩,
       ⟨.live (.immediate ptr1Imm), some ptrLay⟩]
      retPlace
    let m0 := mkRefMiriState frame0 mem0 refInitControl ⟨[]⟩
    have h_step_m :
        ∃ st' msg, Miri.Interpreter.ExecutionMachine.step
          (refExecutionConfigV2 rp) refLimitsV2 0 m0 =
          (st', .error (.undefinedBehavior msg)) :=
      assign_deref_u8_const_absent_ub_v2 rp m0 frame0 0 0
        (toMiriBasicBlockV2 rp.types
          (@GetElem.getElem _ Nat _ _ _ rbody.basicBlocks 0 (by decide)))
        (toMiriStatementV2 rp.types
          (@GetElem.getElem _ Nat _ _ _
            (@GetElem.getElem _ Nat _ _ _ rbody.basicBlocks 0
              (by decide)).statements 0 (by decide)))
        retAllocIdV2 7 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by
          rw [show m0.machine.memory.findGlobal? retAllocIdV2 =
              (Miri.Memory.MemoryState.empty : RefMiriMem).findGlobal?
                retAllocIdV2 from rfl]
          exact memoryState_empty_findGlobal?_none_v2 retAllocIdV2)
    let ⟨_, msg, h_s⟩ := h_step_m
    have h_init : ∀ ms : Nat, initRefStateV2 rp qRaw1 ms =
        .ok { miri := m0, retTy := u8Ty, retPlace := retPlace,
              stepsExecuted := 0, maxSteps := ms } := by
      intro ms
      dsimp only [initRefStateV2]
      rw [show (!Nat.beq rp.pointerWidthBits 64 ||
          !Nat.beq rp.mirProfileVersion 2) = false from rfl]
      simp only [Bool.false_eq_true, ite_false]
      rw [show (!refValidCallerMemoryV2 qRaw1.callerMem) = false from rfl]
      simp only [Bool.false_eq_true, ite_false]
      rw [show Trusted.MirSemantics.getElem? rp.bodies rp.entryDefId =
          some rbody from rfl]
      dsimp only
      rw [show decodeLocalTys rp.types rbody.locals =
          some [u8Ty, .rawPtr .mut u8Ty] from rfl]
      dsimp only
      rw [show (rbody.basicBlocks.isEmpty ||
          !Nat.blt rbody.argumentCount
            ([u8Ty, .rawPtr .mut u8Ty] : List MirTy).length ||
          !refStorageAnnotationsInBounds rbody ||
          !refDiscriminantTypesValid [u8Ty, .rawPtr .mut u8Ty] rbody ||
          !refCastTypesValid rp.types [u8Ty, .rawPtr .mut u8Ty] rbody ||
          ![u8Ty, .rawPtr .mut u8Ty].all refIsSupportedLocalTyV2 ||
          ![u8Ty, .rawPtr .mut u8Ty].all refTyLayoutFitsU64V2) = false from rfl]
      simp only [Bool.false_eq_true, ite_false]
      rw [show (!checkRefArgsMatchV2 qRaw1.args
            (([u8Ty, .rawPtr .mut u8Ty].drop 1).take rbody.argumentCount) ||
          !refValListAllocIdsFitU64V2 qRaw1.args) = false from rfl]
      simp only [Bool.false_eq_true, ite_false]
      rw [show Trusted.MirSemantics.getElem?
          ([u8Ty, .rawPtr .mut u8Ty] : List MirTy) 0 = some u8Ty from rfl]
      dsimp only [refInitCallerMemoryV2]
      simp only [show refOwnLayoutFitsU64V2 u8Ty = true from rfl,
        Bool.not_true, Bool.false_eq_true, ite_false]
      rw [show u8Lay.layout.size = Miri.ABI.Size.ofBytes 1 from rfl,
        show u8Lay.layout.align.abi = Miri.ABI.Align.ONE from rfl, h_raw]
      dsimp only [qRaw1, refInsertCallerAllocsV2]
      simp only [show List.take rbody.argumentCount
            (List.drop 1 ([u8Ty, .rawPtr .mut u8Ty] : List MirTy)) =
            [.rawPtr .mut u8Ty] from rfl,
        show ∀ m : RefMiriMem, refRefsValidInMiriListV2 m [.rawPtr .mut u8Ty]
            [.ptr ⟨some 1, 0, .isize⟩] = true from fun _ => rfl,
        show refSpansPairwiseDisjointV2 (refAccessSpansListV2 [.rawPtr .mut u8Ty]
            [.ptr ⟨some 1, 0, .isize⟩]) = true from rfl,
        show refHasAllocIdV2 1 [] = false from rfl,
        show refAllocBytesHaveProvIdV2 1 [] = false from rfl,
        show refMaxAllocIdV2 [] = 0 from rfl,
        show refMaxAllocBytesProvIdV2 [] = 0 from rfl,
        show refValListHasAllocIdV2 1 [.ptr ⟨some 1, 0, .isize⟩] = true
          from rfl,
        show refMaxValListAllocIdV2 [.ptr ⟨some 1, 0, .isize⟩] = 1 from rfl,
        Bool.and_true, Bool.not_true, Bool.false_eq_true, Bool.false_or,
        Nat.max_zero, Nat.zero_max, ite_false, ite_true]
      rw [show refExactAllocIdV2 (1 + 1) = some alloc2IdV2 from rfl]
      dsimp only
      rw [show (!Nat.beq (UInt64.ofNat (1 + 2)).toNat (1 + 2)) = false from rfl]
      simp only [Bool.false_eq_true, ite_false]
      rfl
    have h_exec : refCoreExecV2 rp u8Ty retPlace (fun _ => False) True False 1
        m0 := by
      dsimp only [refCoreExecV2]
      change (match evalRefCoreV2 rp u8Ty retPlace m0 with
        | .running miri' => refCoreExecV2 rp u8Ty retPlace (fun _ => False)
            True False 0 miri'
        | .returned _ => False | .ub => True | .blocked => False)
      dsimp only [evalRefCoreV2]
      rw [h_s]
      exact True.intro
    let ⟨h1, h2, _, _, _⟩ := ref_ub_of_coreExec h_init h_exec
    exact ⟨h1, h2⟩
  have h_2b_ref :
      (∃ ms : Nat,
        RefReachesOutcomeV2 (encodeProg progRawOff1) qRaw1 ms .blocked) ∧
      ¬ RefWellFormedV2 (encodeProg progRawOff1) qRaw1 ∧
      (∀ out : TerminalOut,
        ¬ RefBehaviorV2 (encodeProg progRawOff1) qRaw1 out) := by
    let rp := encodeProg progRawOff1
    let rbody := @GetElem.getElem _ Nat _ _ _ rp.bodies 0 (by decide)
    let rawTy := MirTy.rawPtr .shared u8Ty
    let ptrLay := refLocalLayoutForTyV2 rp.types rawTy
    let isizeLay := refLocalLayoutForTyV2 rp.types (.int .isize true)
    let ⟨rawRet, h_raw, _⟩ :=
      refTryNew_spec_v2 (Miri.ABI.Size.ofBytes 8) Miri.ABI.Align.EIGHT 8 rfl rfl
    let retPtr : Miri.Memory.Pointer (Option Miri.Memory.Provenance) :=
      ⟨Miri.ABI.Size.ZERO, some (.concrete alloc2IdV2 Miri.Memory.BorTag.one)⟩
    let retPlace : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance :=
      ⟨⟨retPtr, .none, none⟩, ptrLay⟩
    let mem0 : RefMiriMem :=
      ({ (Miri.Memory.MemoryState.empty : RefMiriMem) with
          nextAllocId := 3
          live := Array.mk [(alloc2IdV2, ⟨.stack, rawRet.withExtra
            (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
              (Miri.ABI.Size.ofBytes 8))⟩)] }).setIssuedIds
        (Array.mk [alloc2IdV2])
    let ptr1 : Miri.Memory.Pointer Miri.Memory.Provenance :=
      ⟨Miri.ABI.Size.ZERO, .concrete retAllocIdV2 Miri.Memory.BorTag.one⟩
    let ptr1Imm : Miri.Interpreter.Immediate Miri.Memory.Provenance :=
      .scalar (.fromPointer refRuntimeLayoutV2.base ptr1)
    let frame0 := mkRefMiriFrameV2 rp.types 0 rbody 0 0
      [⟨.live (.immediate .uninit), some ptrLay⟩,
       ⟨.live (.immediate ptr1Imm), some ptrLay⟩]
      retPlace
    let m0 := mkRefMiriState frame0 mem0 refInitControl ⟨[]⟩
    have h_ev := projPlace_evalPlace_local_v2 rp m0 frame0 0 ptrLay
      (.live (.immediate .uninit)) true rfl rfl rfl
    have h_op1 := evalOperand_local_imm_v2 rp m0 frame0 1 ptrLay ptr1Imm
      (some ptrLay) (Miri.Interpreter.OperandPath.rvalue "left") rfl rfl rfl rfl
    have h_ri1 : Miri.Interpreter.PlaceMachine.readImmediate
        (refAccessConfigV2 rp.types) ⟨.immediate ptr1Imm, ptrLay⟩ m0 =
        .ok ⟨ptr1Imm, ptrLay⟩ m0 := rfl
    have h_opc : Miri.Interpreter.OperandMachine.evalOperandAt
        (Miri.Interpreter.ExecutionMachine.operandHooks (refExecCfgV2 rp)) 0
        (Miri.Interpreter.OperandPath.rvalue "right")
        (.Constant ⟨⟨0⟩, none, .Val (.Scalar (.Int 1 16))
          (canonicalTyId rp.types 2)⟩) none m0 =
        .ok ⟨.immediate (.scalar (.fromScalarInt (miriScalar .isize 1))),
          isizeLay⟩ m0 := by
      dsimp only [Miri.Interpreter.OperandMachine.evalOperandAt,
        Miri.Interpreter.OperandMachine.evalOperand]
      rw [opHooks_constantAt_v2]
      exact refEvalConst_int_v2 rp.types m0 .isize true 1 2
        (miriScalar .isize 1) rfl rfl
    have h_ric : Miri.Interpreter.PlaceMachine.readImmediate
        (refAccessConfigV2 rp.types)
        ⟨.immediate (.scalar (.fromScalarInt (miriScalar .isize 1))),
          isizeLay⟩ m0 =
        .ok ⟨.scalar (.fromScalarInt (miriScalar .isize 1)),
          isizeLay⟩ m0 := rfl
    have h_cls_ptr : (refScalarLeavesV2 rp.types).classify 0 ptrLay.ty m0 =
        .ok .pointer m0 := by
      dsimp only [refScalarLeavesV2, ptrLay, refLocalLayoutForTyV2]; rfl
    have h_cls_is : (refScalarLeavesV2 rp.types).classify 0 isizeLay.ty m0 =
        .ok (.integer (toMiriIntKind .isize true)) m0 := by
      dsimp only [refScalarLeavesV2, isizeLay, refLocalLayoutForTyV2]; rfl
    have h_ovl : (refScalarLeavesV2 rp.types).overflowLayout 0 isizeLay m0 =
        .ok (refLocalLayoutForTyV2 rp.types
          (.tuple [.int .isize true, .bool])) m0 := by
      dsimp only [refScalarLeavesV2, isizeLay, refLocalLayoutForTyV2]; rfl
    have h_mul : Miri.Interpreter.ExecutionScalar.integerBinary
        (refScalarLeavesV2 rp.types) 0 .MulWithOverflow
        (⟨.scalar (.fromScalarInt (miriScalar .isize 1)), isizeLay⟩ :
          Miri.Interpreter.RvalueImmTy Miri.Memory.Provenance)
        (⟨.scalar (.fromScalarInt (miriScalar .isize 1)), isizeLay⟩ :
          Miri.Interpreter.RvalueImmTy Miri.Memory.Provenance) m0 =
        .ok ⟨.scalarPair (.fromScalarInt (miriScalar .isize 1))
          (.fromBool false),
          refLocalLayoutForTyV2 rp.types (.tuple [.int .isize true, .bool])⟩
          m0 := by
      dsimp only [Miri.Interpreter.ExecutionScalar.integerBinary,
        Miri.Interpreter.RvalueM, bind, Bind.bind, pure, Pure.pure]
      refine eStateM_apply_bind _ _ _ _ _ h_cls_is ?_; dsimp only
      refine eStateM_apply_bind _ _ _ _ _ h_cls_is ?_; dsimp only
      refine eStateM_apply_bind _ _
        ({ scalar := miriScalar .isize 1,
           type := ⟨Miri.ABI.Size.ofBytes 8, toMiriIntKind .isize true⟩ } :
          Miri.Interpreter.IntegerValue) _ _ rfl ?_
      refine eStateM_apply_bind _ _
        ({ scalar := miriScalar .isize 1,
           type := ⟨Miri.ABI.Size.ofBytes 8, toMiriIntKind .isize true⟩ } :
          Miri.Interpreter.IntegerValue) _ _ rfl ?_
      rw [show (Miri.MIR.BinOp.MulWithOverflow == Miri.MIR.BinOp.Shl ||
          Miri.MIR.BinOp.MulWithOverflow == Miri.MIR.BinOp.ShlUnchecked ||
          Miri.MIR.BinOp.MulWithOverflow == Miri.MIR.BinOp.Shr ||
          Miri.MIR.BinOp.MulWithOverflow == Miri.MIR.BinOp.ShrUnchecked) =
          false from rfl,
        show (isizeLay.ty == isizeLay.ty) = true from beq_self_eq_true _]
      simp only [Bool.false_eq_true, ite_false, ite_true]
      refine eStateM_apply_bind _ _ (.withOverflow (miriScalar .isize 1) false)
        _ _ (by dsimp only [Except.mapError]; rw [mulWithOverflow_isize_1_1_v2]; rfl) ?_
      dsimp only [Miri.Interpreter.ExecutionScalar.finish,
        Miri.Interpreter.RvalueM, bind, Bind.bind, EStateM.bind,
        pure, Pure.pure, EStateM.pure]
      rw [h_ovl]
    have h_bin :
        Miri.Interpreter.ScalarOps.binary
          (Miri.Interpreter.ExecutionMachine.scalarHooks (refExecCfgV2 rp)) 0
          .Offset ⟨ptr1Imm, ptrLay⟩
          ⟨.scalar (.fromScalarInt (miriScalar .isize 1)), isizeLay⟩ m0 =
          .error (.unsupported "missing pointer allocation 1") m0 := by
      dsimp only [Miri.Interpreter.ExecutionMachine.scalarHooks,
        Miri.Interpreter.ExecutionScalar.hooks,
        Miri.Interpreter.ScalarOps.binary, Miri.Interpreter.MachineHooks.M,
        bind, Bind.bind, pure, Pure.pure]
      rw [show (refExecCfgV2 rp).scalar = refScalarLeavesV2 rp.types from rfl]
      refine eStateM_apply_bind _ _ _ _ _ h_cls_ptr ?_; dsimp only
      refine eStateM_apply_bind _ _ _ _ _ h_cls_is ?_; dsimp only
      simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]
      refine eStateM_apply_bind _ _
        (Miri.Memory.Scalar.fromPointer refRuntimeLayoutV2.base ptr1)
        _ _ rfl ?_
      rw [show (refExecCfgV2 rp).access.runtime.base =
        refRuntimeLayoutV2.base from rfl]
      refine eStateM_apply_bind _ _ ptr1.withOptionalProvenance _ _ rfl ?_
      refine eStateM_apply_bind _ _ (refLocalLayoutForTyV2 rp.types u8Ty)
        _ _ rfl ?_
      rw [show ((refLocalLayoutForTyV2 rp.types u8Ty).layout.isSized &&
          decide ((refLocalLayoutForTyV2 rp.types u8Ty).layout.size.bytes.toNat <
            Nat.pow 2 63)) = true from rfl]
      simp only [ite_true]
      rw [show (refLocalLayoutForTyV2 rp.types u8Ty).layout.size.bytes.toNat =
          1 from rfl,
        show Int.ofNat 1 = (1 : Int) from rfl,
        show isizeLay.layout.size = Miri.ABI.Size.ofBytes 8 from rfl]
      rw [show Miri.Memory.Scalar.fromInt (Prov := Miri.Memory.Provenance)
          1 (Miri.ABI.Size.ofBytes 8) =
        .ok (.fromScalarInt (miriScalar .isize 1)) from by decide]
      dsimp only [Except.mapError]
      refine eStateM_apply_bind _ _
        (Miri.Memory.Scalar.fromScalarInt (miriScalar .isize 1)) _ _ rfl ?_
      rw [show ({ ty := isizeLay.ty, layout := isizeLay.layout } :
          Miri.Interpreter.LocalLayout) = isizeLay from rfl]
      refine eStateM_apply_bind _ _ _ _ _ h_mul ?_
      dsimp only [Miri.Interpreter.Immediate.toScalarPair]
      refine eStateM_apply_bind _ _
        (Miri.Memory.Scalar.fromScalarInt (miriScalar .isize 1),
         Miri.Memory.Scalar.fromBool false) _ _ rfl ?_
      rw [show (Miri.Memory.Scalar.fromBool false :
          Miri.Memory.Scalar Miri.Memory.Provenance).toBool = .ok false from rfl]
      dsimp only [Except.mapError]
      refine eStateM_apply_bind _ _ false _ _ rfl ?_
      simp only [Bool.false_eq_true, ite_false]
      rw [show (refExecCfgV2 rp).arithmetic.pointerSize =
        Miri.ABI.Size.ofBytes 8 from rfl]
      rw [show (Miri.Memory.Scalar.fromScalarInt (miriScalar .isize 1) :
          Miri.Memory.Scalar Miri.Memory.Provenance).toTargetIsize
          (Miri.ABI.Size.ofBytes 8) = .ok 1 from by decide,
        show isizeLay.layout.backendRepr.isSigned = .ok true from rfl]
      dsimp only [Except.mapError]
      refine eStateM_apply_bind _ _ (1 : Int64) _ _ rfl ?_
      refine eStateM_apply_bind _ _ true _ _ rfl ?_
      simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false]
      rw [show ((1 : Int64) != 0) = true from rfl, ite_true_eq]
      dsimp only [get, getThe, MonadStateOf.get, EStateM.get]
      refine eStateM_apply_bind EStateM.get _ m0 m0 m0 rfl ?_
      refine eStateM_apply_bind _ _
        (Except.ok ⟨retAllocIdV2, Miri.ABI.Size.ZERO, .concrete .one⟩ :
          Except UInt64 (Miri.Memory.ResolvedPointer Miri.Memory.ProvenanceExtra))
        m0 m0 rfl ?_
      have h_hfp : m0.machine.memory.hasFunctionPointer retAllocIdV2 = false := by
        dsimp only [Miri.Memory.MemoryState.hasFunctionPointer, m0,
          mkRefMiriState, mkRefMiriStackState, mem0,
          Miri.Memory.MemoryState.setIssuedIds, Miri.Memory.MemoryState.empty,
          Miri.Memory.KeyedArray.empty, Miri.Memory.KeyedArray.contains,
          Miri.Memory.KeyedArray.any?, Id.run, bind, Bind.bind, pure, Pure.pure]
        rw [empty_hashmap_contains_false_v2, empty_hashmap_get?_none_v2]
        rfl
      have h_gi : m0.machine.memory.getAllocInfo retAllocIdV2 =
          .error (.unavailable retAllocIdV2) := by
        dsimp only [Miri.Memory.MemoryState.getAllocInfo, Except.bind,
          bind, Bind.bind, pure, Pure.pure, throw, MonadExceptOf.throw]
        rw [show m0.machine.memory.live.find? (fun e => e.1 == retAllocIdV2) =
            none from rfl]
        dsimp only
        rw [h_hfp]
        simp only [Bool.false_eq_true, ite_false]
        rw [show m0.machine.memory.findGlobal? retAllocIdV2 = none from
            (rfl : m0.machine.memory.findGlobal? retAllocIdV2 =
              (Miri.Memory.MemoryState.empty : RefMiriMem).findGlobal?
                retAllocIdV2).trans
              (memoryState_empty_findGlobal?_none_v2 retAllocIdV2)]
        dsimp only
        rw [show m0.machine.memory.dead.find?
            (fun e => e.allocId == retAllocIdV2) = none from rfl]
        dsimp only [m0, mkRefMiriState, mkRefMiriStackState, mem0,
          Miri.Memory.MemoryState.setIssuedIds, Miri.Memory.MemoryState.empty,
          Miri.Memory.KeyedArray.empty, Miri.Memory.KeyedArray.contains]
        simp only [empty_hashmap_contains_false_v2, Bool.false_eq_true,
          ite_false]
        rfl
      have h_chk :
          Miri.Memory.checkPtrAccessSigned (refExecCfgV2 rp).arithmetic
            ptr1.withOptionalProvenance 1
            Miri.Memory.CheckInAllocMsg.inboundsPointerArithmetic
            (fun _ _ => (Except.ok ⟨retAllocIdV2, Miri.ABI.Size.ZERO,
              Miri.Memory.ProvenanceExtra.concrete Miri.Memory.BorTag.one⟩ :
              Except UInt64
                (Miri.Memory.ResolvedPointer Miri.Memory.ProvenanceExtra)))
            m0.machine.memory.getAllocInfo =
            .error (.allocationLookup (.unavailable retAllocIdV2)) := by
        dsimp only [Miri.Memory.checkPtrAccessSigned,
          Miri.Memory.checkAndDerefPtr,
          bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
        rw [h_gi]
        rfl
      rw [h_chk]
      dsimp only [bind, Bind.bind, EStateM.bind, throw, MonadExceptOf.throw,
        EStateM.throw]
      rfl
    have h_ass_blk :
        (Miri.Interpreter.ExecutionMachine.stepHooks
            (refExecutionConfigV2 rp) refLimitsV2).assign 0 ⟨0, Array.empty⟩
            (toMiriRvalueV2 rp.types (.binaryOp .offset (.copy ⟨1, []⟩)
              (.constant ⟨tyIdFor rp.types (.int .isize true),
                .scalar (BitVec.ofNat 128 1)⟩))) m0 =
          (m0, .error (.unsupported "missing pointer allocation 1")) := by
      have h_ev_body :
          Miri.Interpreter.evalRvalueIntoPlace
              (Miri.Interpreter.ExecutionMachine.rvalueHooks (refExecCfgV2 rp)
                refLimitsV2) 0
              (toMiriRvalueV2 rp.types (.binaryOp .offset (.copy ⟨1, []⟩)
                (.constant ⟨tyIdFor rp.types (.int .isize true),
                  .scalar (BitVec.ofNat 128 1)⟩))) ⟨0, Array.empty⟩ m0 =
            EStateM.Result.error (.unsupported "missing pointer allocation 1") m0 := by
        dsimp only [Miri.Interpreter.evalRvalueIntoPlace,
          toMiriRvalueV2, toMiriOperandV2, toMiriPlaceV2, toMiriProjElemV2,
          toMiriBinOp, List.map]
        rw [show ({ toList := [] } : Array Miri.MIR.ProjectionElem) =
              Array.empty from rfl,
          show (BitVec.ofNat 128 1).toNat = 1 from rfl,
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
        refine mh_apply_bind _ _ ⟨ptr1Imm, ptrLay⟩ _ _ h_ri1 ?_
        refine mh_apply_bind _ _ _ _ _ h_opc ?_
        refine mh_apply_bind _ _ _ _ _ h_ric ?_
        exact mh_apply_bind_err _ _ _ _ _ h_bin
      dsimp only [Miri.Interpreter.ExecutionMachine.stepHooks,
        Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run]
      rw [show Miri.Interpreter.ExecutionMachine.withValidation
          (refExecutionConfigV2 rp) refLimitsV2 = refExecCfgV2 rp from rfl,
        h_ev_body]
    have h_step0 := execStep_assign_err rp m0 m0 frame0 0 0
      (toMiriBasicBlockV2 rp.types
        (@GetElem.getElem _ Nat _ _ _ rbody.basicBlocks 0 (by decide)))
      (toMiriStatementV2 rp.types
        (@GetElem.getElem _ Nat _ _ _
          (@GetElem.getElem _ Nat _ _ _ rbody.basicBlocks 0
            (by decide)).statements 0 (by decide)))
      ⟨0, Array.empty⟩
      (toMiriRvalueV2 rp.types (.binaryOp .offset (.copy ⟨1, []⟩)
        (.constant ⟨tyIdFor rp.types (.int .isize true),
          .scalar (BitVec.ofNat 128 1)⟩)))
      (.unsupported "missing pointer allocation 1")
      rfl rfl rfl rfl rfl rfl h_ass_blk
    have h_init : ∀ ms : Nat, initRefStateV2 rp qRaw1 ms =
        .ok { miri := m0, retTy := rawTy, retPlace := retPlace,
              stepsExecuted := 0, maxSteps := ms } := by
      intro ms
      dsimp only [initRefStateV2]
      rw [show (!Nat.beq rp.pointerWidthBits 64 ||
          !Nat.beq rp.mirProfileVersion 2) = false from rfl]
      simp only [Bool.false_eq_true, ite_false]
      rw [show (!refValidCallerMemoryV2 qRaw1.callerMem) = false from rfl]
      simp only [Bool.false_eq_true, ite_false]
      rw [show Trusted.MirSemantics.getElem? rp.bodies rp.entryDefId =
          some rbody from rfl]
      dsimp only
      rw [show decodeLocalTys rp.types rbody.locals =
          some [rawTy, rawTy] from rfl]
      dsimp only
      rw [show (rbody.basicBlocks.isEmpty ||
          !Nat.blt rbody.argumentCount ([rawTy, rawTy] : List MirTy).length ||
          !refStorageAnnotationsInBounds rbody ||
          !refDiscriminantTypesValid [rawTy, rawTy] rbody ||
          !refCastTypesValid rp.types [rawTy, rawTy] rbody ||
          ![rawTy, rawTy].all refIsSupportedLocalTyV2 ||
          ![rawTy, rawTy].all refTyLayoutFitsU64V2) = false from rfl]
      simp only [Bool.false_eq_true, ite_false]
      rw [show (!checkRefArgsMatchV2 qRaw1.args
            (([rawTy, rawTy].drop 1).take rbody.argumentCount) ||
          !refValListAllocIdsFitU64V2 qRaw1.args) = false from rfl]
      simp only [Bool.false_eq_true, ite_false]
      rw [show Trusted.MirSemantics.getElem?
          ([rawTy, rawTy] : List MirTy) 0 = some rawTy from rfl]
      dsimp only [refInitCallerMemoryV2]
      simp only [show refOwnLayoutFitsU64V2 rawTy = true from rfl,
        Bool.not_true, Bool.false_eq_true, ite_false]
      rw [show ptrLay.layout.size = Miri.ABI.Size.ofBytes 8 from rfl,
        show ptrLay.layout.align.abi = Miri.ABI.Align.EIGHT from rfl, h_raw]
      dsimp only [qRaw1, refInsertCallerAllocsV2]
      simp only [show List.take rbody.argumentCount
            (List.drop 1 ([rawTy, rawTy] : List MirTy)) = [rawTy] from rfl,
        show ∀ m : RefMiriMem, refRefsValidInMiriListV2 m [rawTy]
            [.ptr ⟨some 1, 0, .isize⟩] = true from fun _ => rfl,
        show refSpansPairwiseDisjointV2 (refAccessSpansListV2 [rawTy]
            [.ptr ⟨some 1, 0, .isize⟩]) = true from rfl,
        show refHasAllocIdV2 1 [] = false from rfl,
        show refAllocBytesHaveProvIdV2 1 [] = false from rfl,
        show refMaxAllocIdV2 [] = 0 from rfl,
        show refMaxAllocBytesProvIdV2 [] = 0 from rfl,
        show refValListHasAllocIdV2 1 [.ptr ⟨some 1, 0, .isize⟩] = true
          from rfl,
        show refMaxValListAllocIdV2 [.ptr ⟨some 1, 0, .isize⟩] = 1 from rfl,
        Bool.and_true, Bool.not_true, Bool.false_eq_true, Bool.false_or,
        Nat.max_zero, Nat.zero_max, ite_false, ite_true]
      rw [show refExactAllocIdV2 (1 + 1) = some alloc2IdV2 from rfl]
      dsimp only
      rw [show (!Nat.beq (UInt64.ofNat (1 + 2)).toNat (1 + 2)) = false from rfl]
      simp only [Bool.false_eq_true, ite_false]
      rfl
    exact ref_firstStep_blocked_no_behavior_v2 rp qRaw1
      ⟨m0, rawTy, retPlace, 0, 0⟩ rfl h_init (by
        dsimp only [evalRefCoreV2]
        rw [h_step0])
  have h_3_ref :
      (∃ ms : Nat,
        RefReachesOutcomeV2 (encodeProg progStackRaw) qRaw2 ms .ub) ∧
      ¬ RefWellFormedV2 (encodeProg progStackRaw) qRaw2 := by
    let rp := encodeProg progStackRaw
    let rbody := @GetElem.getElem _ Nat _ _ _ rp.bodies 0 (by decide)
    let u8Lay := refLocalLayoutForTyV2 rp.types u8Ty
    let ptrU8Lay := refLocalLayoutForTyV2 rp.types (.rawPtr .mut u8Ty)
    let unitLay := refLocalLayoutForTyV2 rp.types .unit
    let ptrUnitLay := refLocalLayoutForTyV2 rp.types (.rawPtr .shared .unit)
    let ⟨rawRet, h_raw, _⟩ :=
      refTryNew_spec_v2 (Miri.ABI.Size.ofBytes 1) Miri.ABI.Align.ONE 1 rfl rfl
    let ⟨rawZst, h_rawZst, _⟩ :=
      refTryNew_spec_v2 Miri.ABI.Size.ZERO Miri.ABI.Align.ONE 1 rfl rfl
    let retPlace : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance :=
      ⟨retMemPlaceV2, u8Lay⟩
    let mem0 : RefMiriMem :=
      ({ (Miri.Memory.MemoryState.empty : RefMiriMem) with
          nextAllocId := 3
          live := Array.mk [(retAllocIdV2, ⟨.stack, rawRet.withExtra
            (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
              (Miri.ABI.Size.ofBytes 1))⟩)] }).setIssuedIds
        (Array.mk [retAllocIdV2])
    let ptr2Imm : Miri.Interpreter.Immediate Miri.Memory.Provenance :=
      .scalar (.fromPointer refRuntimeLayoutV2.base
        ⟨Miri.ABI.Size.ZERO, .concrete alloc2IdV2 Miri.Memory.BorTag.one⟩)
    let frame0 := mkRefMiriFrameV2 rp.types 0 rbody 0 0
      [⟨.live (.immediate .uninit), some u8Lay⟩,
       ⟨.live (.immediate ptr2Imm), some ptrU8Lay⟩,
       ⟨.live (.immediate .uninit), some unitLay⟩,
       ⟨.live (.immediate .uninit), some ptrUnitLay⟩]
      retPlace
    let m0 := mkRefMiriState frame0 mem0 refInitControl ⟨[]⟩
    have h_init : ∀ ms : Nat, initRefStateV2 rp qRaw2 ms =
        .ok { miri := m0, retTy := u8Ty, retPlace := retPlace,
              stepsExecuted := 0, maxSteps := ms } := by
      intro ms
      dsimp only [initRefStateV2]
      rw [show (!Nat.beq rp.pointerWidthBits 64 ||
          !Nat.beq rp.mirProfileVersion 2) = false from rfl]
      simp only [Bool.false_eq_true, ite_false]
      rw [show (!refValidCallerMemoryV2 qRaw2.callerMem) = false from rfl]
      simp only [Bool.false_eq_true, ite_false]
      rw [show Trusted.MirSemantics.getElem? rp.bodies rp.entryDefId =
          some rbody from rfl]
      dsimp only
      rw [show decodeLocalTys rp.types rbody.locals =
          some [u8Ty, .rawPtr .mut u8Ty, .unit, .rawPtr .shared .unit]
        from rfl]
      dsimp only
      rw [show (rbody.basicBlocks.isEmpty ||
          !Nat.blt rbody.argumentCount
            ([u8Ty, .rawPtr .mut u8Ty, .unit,
              .rawPtr .shared .unit] : List MirTy).length ||
          !refStorageAnnotationsInBounds rbody ||
          !refDiscriminantTypesValid
            [u8Ty, .rawPtr .mut u8Ty, .unit, .rawPtr .shared .unit] rbody ||
          !refCastTypesValid rp.types
            [u8Ty, .rawPtr .mut u8Ty, .unit, .rawPtr .shared .unit] rbody ||
          ![u8Ty, .rawPtr .mut u8Ty, .unit, .rawPtr .shared .unit].all
            refIsSupportedLocalTyV2 ||
          ![u8Ty, .rawPtr .mut u8Ty, .unit, .rawPtr .shared .unit].all
            refTyLayoutFitsU64V2) = false from rfl]
      simp only [Bool.false_eq_true, ite_false]
      rw [show (!checkRefArgsMatchV2 qRaw2.args
            (([u8Ty, .rawPtr .mut u8Ty, .unit,
                .rawPtr .shared .unit].drop 1).take rbody.argumentCount) ||
          !refValListAllocIdsFitU64V2 qRaw2.args) = false from rfl]
      simp only [Bool.false_eq_true, ite_false]
      rw [show Trusted.MirSemantics.getElem?
          ([u8Ty, .rawPtr .mut u8Ty, .unit, .rawPtr .shared .unit] : List MirTy)
          0 = some u8Ty from rfl]
      dsimp only [refInitCallerMemoryV2]
      simp only [show refOwnLayoutFitsU64V2 u8Ty = true from rfl,
        Bool.not_true, Bool.false_eq_true, ite_false]
      rw [show u8Lay.layout.size = Miri.ABI.Size.ofBytes 1 from rfl,
        show u8Lay.layout.align.abi = Miri.ABI.Align.ONE from rfl, h_raw]
      dsimp only [qRaw2, refInsertCallerAllocsV2]
      simp only [show List.take rbody.argumentCount
            (List.drop 1 ([u8Ty, .rawPtr .mut u8Ty, .unit,
              .rawPtr .shared .unit] : List MirTy)) =
            [.rawPtr .mut u8Ty] from rfl,
        show ∀ m : RefMiriMem, refRefsValidInMiriListV2 m [.rawPtr .mut u8Ty]
            [.ptr ⟨some 2, 0, .isize⟩] = true from fun _ => rfl,
        show refSpansPairwiseDisjointV2 (refAccessSpansListV2 [.rawPtr .mut u8Ty]
            [.ptr ⟨some 2, 0, .isize⟩]) = true from rfl,
        show refHasAllocIdV2 1 [] = false from rfl,
        show refAllocBytesHaveProvIdV2 1 [] = false from rfl,
        show refMaxAllocIdV2 [] = 0 from rfl,
        show refMaxAllocBytesProvIdV2 [] = 0 from rfl,
        show refValListHasAllocIdV2 1 [.ptr ⟨some 2, 0, .isize⟩] = false
          from rfl,
        show refMaxValListAllocIdV2 [.ptr ⟨some 2, 0, .isize⟩] = 2 from rfl,
        Bool.and_true, Bool.not_true, Bool.false_eq_true, Bool.false_or,
        Nat.max_zero, Nat.zero_max, ite_false]
      rw [show refExactAllocIdV2 1 = some retAllocIdV2 from rfl]
      dsimp only
      rw [show (!Nat.beq (UInt64.ofNat (Nat.max 2 (2 + 1))).toNat
          (Nat.max 2 (2 + 1))) = false from rfl]
      simp only [Bool.false_eq_true, ite_false]
      rfl
    have h_nx : mem0.nextAllocId = 3 := by dsimp only [mem0]; rfl
    have h_nxn : mem0.nextAllocId.toNat = 3 := by dsimp only [mem0]; rfl
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
      have h_lt1 : retAllocIdV2.value.toNat < 3 := by decide
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
    let ⟨mem1, h_res, h_as⟩ := allocateStack_unit_v2 rp m0 alloc3IdV2 rawZst
      h_rawZst rfl rfl rfl h_nx_nz (fun h => by cases h) (fun h => by cases h)
      h_iss h_lv h_gl h_dd (by
        have h_id_eq : (⟨mem0.nextAllocId, h_nx_nz⟩ : Miri.Memory.AllocId) =
            alloc3IdV2 := by
          simp only [alloc3IdV2, h_nx]
        exact h_id_eq)
    let a3Mp : Miri.Interpreter.MemPlace Miri.Memory.Provenance :=
      ⟨⟨Miri.ABI.Size.ZERO, some (.concrete alloc3IdV2 Miri.Memory.BorTag.one)⟩,
        .none, none⟩
    let frame0A : Miri.Interpreter.Frame Miri.Memory.Provenance
        Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra :=
      { frame0 with locals := (Array.mk
        [⟨.live (.immediate .uninit), some u8Lay⟩,
         ⟨.live (.immediate ptr2Imm), some ptrU8Lay⟩,
         ⟨.live (.indirect a3Mp), some unitLay⟩,
         ⟨.live (.immediate .uninit), some ptrUnitLay⟩]) }
    let mem2 : RefMiriMem :=
      { mem1 with
        live := mem1.live.push
          (alloc3IdV2, ⟨.stack, rawZst.withExtra
            (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
              Miri.ABI.Size.ZERO)⟩) }
    let m0A : RefMiriState :=
      { m0 with
        stack := ⟨Array.mk [frame0A]⟩
        machine := { m0.machine with
          memory := mem2
          allocationSpans :=
            (m0.machine.allocationSpans.filter fun e => e.1 != alloc3IdV2).push
              (alloc3IdV2, ⟨0⟩, none) } }
    have h_force2 := forceAllocation_unit_local_v2 rp m0 frame0 frame0A 2
      alloc3IdV2 mem1 rawZst rfl rfl rfl rfl h_as
    let ptr3Imm : Miri.Interpreter.Immediate Miri.Memory.Provenance :=
      .scalar (.fromPointer refRuntimeLayoutV2.base
        ⟨Miri.ABI.Size.ZERO, .concrete alloc3IdV2 Miri.Memory.BorTag.one⟩)
    let frame0B : Miri.Interpreter.Frame Miri.Memory.Provenance
        Miri.Interpreter.LocalLayout Miri.Interpreter.MachineHooks.FrameExtra :=
      { frame0A with locals := (Array.mk
        [⟨.live (.immediate .uninit), some u8Lay⟩,
         ⟨.live (.immediate ptr2Imm), some ptrU8Lay⟩,
         ⟨.live (.indirect a3Mp), some unitLay⟩,
         ⟨.live (.immediate ptr3Imm), some ptrUnitLay⟩]) }
    let m0B : RefMiriState := { m0A with stack := ⟨Array.mk [frame0B]⟩ }
    have h_val3 :
        Miri.Interpreter.ValidityVisitor.validatePlace (refValHooksV2 rp.types) 0
          16 ⟨.local 0 3 none frame0A.localsIdentity, ptrUnitLay⟩ true true
          m0B = .ok () m0B :=
      rawPtr_validate_v2 rp.types m0B 3 .unit .shared
        ⟨Miri.ABI.Size.ZERO, .concrete alloc3IdV2 Miri.Memory.BorTag.one⟩
        frame0B rfl rfl rfl rfl rfl
    have h_wr3 := writeLocalImmediate_direct_v2 rp m0A frame0A 3 .uninit ptr3Imm
      ptrUnitLay frame0B rfl rfl rfl rfl rfl h_val3
    have h_ass0 :
        (Miri.Interpreter.ExecutionMachine.stepHooks (refExecutionConfigV2 rp)
            refLimitsV2).assign 0 ⟨3, Array.empty⟩
            (toMiriRvalueV2 rp.types (.addressOf .shared ⟨2, []⟩)) m0 =
          (m0B, .ok ()) := by
      have h_evd := projPlace_evalPlace_local_v2 rp m0 frame0 3 ptrUnitLay
        (.live (.immediate .uninit)) true rfl rfl rfl
      have h_evs := projPlace_evalPlace_local_v2 rp m0 frame0 2 unitLay
        (.live (.immediate .uninit)) false rfl rfl rfl
      have h_body : Miri.Interpreter.evalRvalueIntoPlace
          (Miri.Interpreter.ExecutionMachine.rvalueHooks (refExecCfgV2 rp)
            refLimitsV2) 0
          (toMiriRvalueV2 rp.types (.addressOf .shared ⟨2, []⟩))
          ⟨3, Array.empty⟩ m0 = EStateM.Result.ok () m0B := by
        dsimp only [Miri.Interpreter.evalRvalueIntoPlace, toMiriRvalueV2,
          toMiriPlaceV2, List.map]
        refine mh_apply_bind _ _ _ _ _ h_evd ?_
        dsimp only [Miri.Interpreter.ExecutionMachine.rvalueHooks,
          Miri.Interpreter.RuntimePlace.layout]
        rw [refStepCfgV2_eq]
        refine mh_apply_bind _ _ false m0 m0 rfl ?_
        refine mh_apply_bind _ _ _ _ _ h_evs ?_
        refine mh_apply_bind _ _ a3Mp m0 m0A
          (mh_apply_bind _ _ _ _ _ h_force2 rfl) ?_
        refine mh_apply_bind _ _ ptr3Imm m0A m0A rfl ?_
        rw [show ((!false && (Miri.MIR.RawPtrKind.Const !=
            Miri.MIR.RawPtrKind.FakeForPtrMetadata)) : Bool) = true from rfl,
          ite_true_eq]
        refine mh_apply_bind _ _ ⟨ptr3Imm, ptrUnitLay⟩ m0A m0A
          (by
            change Miri.Interpreter.MachineHooks.withRetagMode .Raw _ m0A = _
            dsimp only [Miri.Interpreter.MachineHooks.withRetagMode]
            rw [show m0A.machine.borrowTracker = none from rfl]
            dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
              Miri.Interpreter.TypedRetag.machineRetagPtrValue,
              get, getThe, MonadStateOf.get, EStateM.get]
            rw [show m0A.machine.borrowTracker = none from rfl]
            rfl) ?_
        exact h_wr3
      dsimp only [Miri.Interpreter.ExecutionMachine.stepHooks,
        Miri.Interpreter.MachineHooks.run, Miri.Interpreter.Call.run]
      rw [show Miri.Interpreter.ExecutionMachine.withValidation
          (refExecutionConfigV2 rp) refLimitsV2 = refExecCfgV2 rp from rfl,
        h_body]
    let frame1 := { frame0B with location := .mir ⟨0, 1⟩ }
    let m1 : RefMiriState := { m0B with stack := ⟨Array.mk [frame1]⟩ }
    have h_step0 : Miri.Interpreter.ExecutionMachine.step
        (refExecutionConfigV2 rp) refLimitsV2 0 m0 = (m1, .ok true) :=
      execStep_assign_ok rp m0 m0B frame0 frame0B 0 0
        (toMiriBasicBlockV2 rp.types
          (@GetElem.getElem _ Nat _ _ _ rbody.basicBlocks 0 (by decide)))
        (toMiriStatementV2 rp.types
          (@GetElem.getElem _ Nat _ _ _
            (@GetElem.getElem _ Nat _ _ _ rbody.basicBlocks 0
              (by decide)).statements 0 (by decide)))
        ⟨3, Array.empty⟩
        (toMiriRvalueV2 rp.types (.addressOf .shared ⟨2, []⟩))
        rfl rfl rfl rfl rfl rfl h_ass0 rfl rfl
    have h_live2_none :
        m1.machine.memory.live.find? (fun e => e.1 == alloc2IdV2) = none := by
      have h_m1_live := (reserveAllocId_live_dead_v2 mem0 mem1 alloc3IdV2 h_res).1
      change mem2.live.find? (fun e => e.1 == alloc2IdV2) = none
      dsimp only [mem2]
      rw [← Array.find?_toList, Array.toList_push, h_m1_live]
      rfl
    have h_glob2_none : m1.machine.memory.findGlobal? alloc2IdV2 = none := by
      rw [show m1.machine.memory.findGlobal? alloc2IdV2 =
          mem1.findGlobal? alloc2IdV2 from rfl,
        reserveAllocId_findGlobal?_v2 mem0 mem1 alloc3IdV2 alloc2IdV2 h_res,
        show mem0.findGlobal? alloc2IdV2 =
          (Miri.Memory.MemoryState.empty : RefMiriMem).findGlobal?
            alloc2IdV2 from rfl]
      exact memoryState_empty_findGlobal?_none_v2 alloc2IdV2
    have h_step1_m :
        ∃ st' msg, Miri.Interpreter.ExecutionMachine.step
          (refExecutionConfigV2 rp) refLimitsV2 0 m1 =
          (st', .error (.undefinedBehavior msg)) :=
      assign_deref_u8_const_absent_ub_v2 rp m1 frame1 0 1
        (toMiriBasicBlockV2 rp.types
          (@GetElem.getElem _ Nat _ _ _ rbody.basicBlocks 0 (by decide)))
        (toMiriStatementV2 rp.types
          (@GetElem.getElem _ Nat _ _ _
            (@GetElem.getElem _ Nat _ _ _ rbody.basicBlocks 0
              (by decide)).statements 1 (by decide)))
        alloc2IdV2 99 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        h_live2_none h_glob2_none
    let ⟨_, _, h_s1⟩ := h_step1_m
    have h_exec : refCoreExecV2 rp u8Ty retPlace (fun _ => False) True False 2
        m0 := by
      dsimp only [refCoreExecV2]
      change (match evalRefCoreV2 rp u8Ty retPlace m0 with
        | .running miri' =>
          match evalRefCoreV2 rp u8Ty retPlace miri' with
          | .running miri'' =>
            refCoreExecV2 rp u8Ty retPlace (fun _ => False) True False 0 miri''
          | .returned _ => False | .ub => True | .blocked => False
        | .returned _ => False | .ub => True | .blocked => False)
      dsimp only [evalRefCoreV2]
      rw [h_step0]
      dsimp only
      rw [show m1.stack.frames.isEmpty = false from rfl, ite_false_eq]
      dsimp only [evalRefCoreV2]
      rw [h_s1]
      exact True.intro
    let ⟨h1, h2, _, _, _⟩ := ref_ub_of_coreExec h_init h_exec
    exact ⟨h1, h2⟩
  have h_4_bytes :
      ∃ st : RefState,
        initRefStateV2 (encodeProg progV2UnitNoop)
          { args := [], callerMem := cmByteProv } 1 = .ok st ∧
        st.retPlace.mplace.ptr.provenance =
          some (Miri.Memory.Provenance.concrete ⟨5, by decide⟩
            Miri.Memory.BorTag.one) ∧
        st.miri.machine.memory.nextAllocId = 6 := by
    let rp := encodeProg progV2UnitNoop
    let rbody := @GetElem.getElem _ Nat _ _ _ rp.bodies 0 (by decide)
    let sz8 := Miri.ABI.Size.ofBytes 8
    let rng8 := Miri.Memory.allocRange Miri.ABI.Size.ZERO sz8
    let alloc4Id : Miri.Memory.AllocId := ⟨4, by decide⟩
    let ptr4 : Miri.Memory.Pointer Miri.Memory.Provenance :=
      ⟨Miri.ABI.Size.ZERO, .concrete alloc4Id Miri.Memory.BorTag.one⟩
    let tree8 := Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one sz8
    let ⟨blank, h_try, h_bsz, h_len, h_mut, h_al, _, _, h_pm, h_im, h_wf, _⟩ :=
      refTryNew_spec_v2 sz8 ⟨3⟩ 8 rfl rfl
    have h_ins4 := Miri.Memory.ProvenanceMap.insertPtr_new Miri.ABI.Size.ZERO
      sz8 sz8 (Miri.Memory.Provenance.concrete alloc4Id Miri.Memory.BorTag.one)
      (by decide) rfl
    let ⟨updated, h_ws, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
      Miri.Memory.Allocation.writeScalar_spec refRuntimeLayoutV2.base blank rng8
        (.fromPointer refRuntimeLayoutV2.base ptr4) (.pointer ptr4)
        Miri.Memory.ProvenanceMap.new _ (by rw [h_len, h_bsz]) h_mut
        (by rw [h_im, h_bsz]; rfl) h_wf (by decide)
        (by decide) (by rw [h_bsz]; decide) rfl
        (fun fullBytes _ => by
          rw [h_pm]
          exact Miri.Memory.ProvenanceMap.clear_new rng8 fullBytes
            (Miri.ABI.Size.fromBits refRuntimeLayoutV2.base.pointerWidth.bits)
            sz8 (by decide) rfl)
        ⟨rfl, h_ins4⟩
    have h_toMiri :
        refAllocToMiriV2 alByteLive =
          .ok ((updated.withMutability .Mut).withExtra tree8) := by
      dsimp only [refAllocToMiriV2, alByteLive]
      rw [show refPlainInitBytesV2? (List.replicate 8 (AllocByte.init 0 (some 4))) =
          none from rfl]
      dsimp only
      rw [show (List.replicate 8 (AllocByte.init 0 (some 4))).length = 8
          from rfl,
        show Miri.ABI.Size.ofBytes (UInt64.ofNat 8) = sz8 from rfl, h_try]
      dsimp only [List.replicate, refPopulateAllocBytesV2,
        Miri.Memory.Allocation.writePointer, toMiriMutV2]
      rw [show (Nat.beq 4 4 && Nat.beq 4 4 && Nat.beq 4 4 && Nat.beq 4 4 &&
            Nat.beq 4 4 && Nat.beq 4 4 && Nat.beq 4 4) = true from rfl,
        ite_true_eq, show refExactAllocIdV2 4 = some alloc4Id from rfl]
      dsimp only [Miri.Memory.Allocation.writePointer]
      rw [show Miri.ABI.Size.ofBytes (UInt64.ofNat 0) = Miri.ABI.Size.ZERO
          from rfl,
        show Miri.ABI.Size.ofBytes (UInt64.ofNat
            (refNatOfLeBytesV2 [0, 0, 0, 0, 0, 0, 0, 0])) =
          Miri.ABI.Size.ZERO from rfl]
      dsimp only [rng8, ptr4, sz8] at h_ws
      rw [h_ws]
    let ⟨rawRet, h_rawRet, _⟩ :=
      refTryNew_spec_v2 Miri.ABI.Size.ZERO Miri.ABI.Align.ONE 1 rfl rfl
    let ma2 := (updated.withMutability .Mut).withExtra tree8
    let alloc5Id : Miri.Memory.AllocId := ⟨5, by decide⟩
    let mem0 : RefMiriMem :=
      ({ ({ (Miri.Memory.MemoryState.empty : RefMiriMem) with
            live := Array.mk [(alloc2IdV2, ⟨.machine (), ma2⟩)] } :
            RefMiriMem) with
          nextAllocId := 6
          dead := Array.mk [⟨alloc3IdV2, Miri.ABI.Size.ofBytes 1, ⟨0⟩⟩]
          live := Array.mk [
            (alloc2IdV2, ⟨.machine (), ma2⟩),
            (alloc5Id, ⟨.stack, rawRet.withExtra
              (Miri.TreeBorrows.BorrowTree.new Miri.Memory.BorTag.one
                Miri.ABI.Size.ZERO)⟩)] }).setIssuedIds
        (Array.mk [alloc2IdV2, alloc3IdV2, alloc5Id])
    let unitLay := refLocalLayoutForTyV2 rp.types .unit
    let retPtr : Miri.Memory.Pointer (Option Miri.Memory.Provenance) :=
      ⟨Miri.ABI.Size.ZERO, some (.concrete alloc5Id Miri.Memory.BorTag.one)⟩
    let retPlace : Miri.Interpreter.MPlaceTy Miri.Memory.Provenance :=
      ⟨⟨retPtr, .none, none⟩, unitLay⟩
    let stExpected : RefState := {
      miri := mkRefMiriState
        (mkRefMiriFrameV2 rp.types rp.entryDefId rbody 0 0
          [⟨.live (.immediate .uninit), some unitLay⟩] retPlace)
        mem0 refInitControl cmByteProv
      retTy := .unit, retPlace := retPlace, stepsExecuted := 0, maxSteps := 1
    }
    refine ⟨stExpected, ?_, rfl, rfl⟩
    dsimp only [initRefStateV2]
    rw [show (!Nat.beq rp.pointerWidthBits 64 ||
        !Nat.beq rp.mirProfileVersion 2) = false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    rw [show (!refValidCallerMemoryV2 cmByteProv) = false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    rw [show Trusted.MirSemantics.getElem? rp.bodies rp.entryDefId =
        some rbody from rfl]
    dsimp only
    rw [show decodeLocalTys rp.types rbody.locals = some [.unit] from rfl]
    dsimp only
    rw [show (rbody.basicBlocks.isEmpty ||
        !Nat.blt rbody.argumentCount ([MirTy.unit] : List MirTy).length ||
        !refStorageAnnotationsInBounds rbody ||
        !refDiscriminantTypesValid [.unit] rbody ||
        !refCastTypesValid rp.types [.unit] rbody ||
        ![MirTy.unit].all refIsSupportedLocalTyV2 ||
        ![MirTy.unit].all refTyLayoutFitsU64V2) = false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    rw [show (!checkRefArgsMatchV2 []
          (List.take rbody.argumentCount (([MirTy.unit] : List MirTy).drop 1)) ||
        !refValListAllocIdsFitU64V2 []) = false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    rw [show Trusted.MirSemantics.getElem? [MirTy.unit] 0 =
        some MirTy.unit from rfl]
    dsimp only [refInitCallerMemoryV2, refOwnLayoutFitsU64V2]
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    rw [show unitLay.layout.size = Miri.ABI.Size.ZERO from rfl,
      show unitLay.layout.align.abi = Miri.ABI.Align.ONE from rfl, h_rawRet]
    dsimp only
    rw [show cmByteProv.allocations = [alByteLive, alByteDead] from rfl]
    dsimp only [refInsertCallerAllocsV2]
    rw [show refExactAllocIdV2 alByteLive.allocId = some alloc2IdV2 from rfl,
      show alByteLive.live = true from rfl, h_toMiri]
    dsimp only
    rw [show refExactAllocIdV2 alByteDead.allocId = some alloc3IdV2 from rfl,
      show alByteDead.live = false from rfl]
    simp only [ite_true, Bool.false_eq_true, ite_false]
    have h_empty_refs : ∀ m : RefMiriMem,
        refRefsValidInMiriListV2 m [] [] = true := fun _ => rfl
    simp only [show List.take rbody.argumentCount
          (List.drop 1 ([MirTy.unit] : List MirTy)) = [] from rfl,
      h_empty_refs,
      show refSpansPairwiseDisjointV2 (refAccessSpansListV2 [] []) = true from rfl,
      show refHasAllocIdV2 1 [alByteLive, alByteDead] = false from rfl,
      show refAllocBytesHaveProvIdV2 1 [alByteLive, alByteDead] = true from rfl,
      show refMaxAllocIdV2 [alByteLive, alByteDead] = 3 from rfl,
      show refMaxAllocBytesProvIdV2 [alByteLive, alByteDead] = 4 from rfl,
      show refValListHasAllocIdV2 1 [] = false from rfl,
      show refMaxValListAllocIdV2 [] = 0 from rfl,
      Nat.max_zero, Bool.false_or, Bool.or_false, ite_true]
    rw [show (!(true && true)) = false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    rw [show Nat.max 3 4 = 4 from rfl,
      show refExactAllocIdV2 (4 + 1) = some alloc5Id from rfl]
    dsimp only
    rw [show (!Nat.beq (UInt64.ofNat (4 + 2)).toNat (4 + 2)) = false from rfl]
    simp only [Bool.false_eq_true, ite_false]
    dsimp only [initRefLocalsLoopV2]
    simp only [show refTyLayoutFitsU64V2 .unit = true from rfl,
      Bool.not_true, Bool.false_eq_true, ite_false,
      show Nat.beq 0 0 = true from rfl, ite_true]
    rfl
  exact ⟨⟨h_a1_f.1, h_a1_f.2.2.2.2, h_ref_unit_init, h_u_ub, h_u_nwf⟩,
    ⟨h_b1_f.1, h_b1_f.2.2.2.2, h_ref_slice_init, h_s_ub, h_s_nwf⟩,
    ⟨h_2a_f.1, h_2a_f.2.2.2.2, h_2a_ref⟩,
    ⟨h_2b_f.1, h_2b_f.2.2.2.2, h_2b_ref⟩,
    ⟨h_3_f.1, h_3_f.2.2.2.2, h_3_ref⟩,
    h_4_bytes⟩

end Anneal.MirCorrespondence
