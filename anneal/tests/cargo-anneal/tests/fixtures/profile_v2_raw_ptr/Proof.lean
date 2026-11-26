-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Data.BitVec.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.List.Lemmas
import Spec
import Expected
import Anneal.MirWp.V2Memory

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

/-- Profile v2 decodes memory little-endian, matching the 64-bit
little-endian targets that capture admits. -/
theorem profileV2_little_endian_canary :
    decodeUInt profileV2TargetEndian [1, 0, 0, 0] = 1 := rfl

private theorem loadU32_ok (cm : CallerMemory) (pv : PtrVal) (aid : AllocId)
    (a : Allocation)
    (hFind : findAllocation aid cm.allocations = some a)
    (hLive : a.live = true)
    (hBounds : isInBounds a pv.offsetBytes.toNat 4 = true)
    (hAlign : isAligned a pv.offsetBytes.toNat 2 = true)
    (hInit : isSliceAllInit ((a.bytes.drop pv.offsetBytes.toNat).take 4) = true) :
    ∃ sv : ScalarVal,
      loadIndirectV2 (entryMemoryWithCaller cm) (.int .i32 false)
        ⟨aid, pv.offsetBytes.toNat⟩ = .ok (some (.scalar sv)) ∧
      checkValV2 (.scalar sv) (.int .i32 false) = true := by
  unfold loadIndirectV2
  dsimp only [layoutOfTyV2, layoutOfTy, intLayout]
  have hRead : readBytes (entryMemoryWithCaller cm) ⟨aid, pv.offsetBytes.toNat⟩ 4 2 =
      .ok ((a.bytes.drop pv.offsetBytes.toNat).take 4) :=
    readBytes_ok_of_alloc (m := entryMemoryWithCaller cm) hFind hLive hBounds hAlign
  rw [hRead]
  have hLe : pv.offsetBytes.toNat + 4 ≤ a.bytes.length := by
    unfold isInBounds at hBounds
    exact Nat.le_of_ble_eq_true hBounds
  have hTakeLen := list_drop_take_four_len pv.offsetBytes.toNat a.bytes hLe
  match isSliceAllInit_take_four _ hTakeLen hInit with
  | ⟨b0, b1, b2, b3, p0, p1, p2, p3, hEq⟩ =>
    rw [hEq]
    have hTrunc := truncateBits_i32_of_lt (decodeUInt_little_four_lt b0 b1 b2 b3)
    have hBne :
        (truncateBits IntWidth.i32
            (BitVec.ofNat 128 (decodeUInt TargetEndian.little [b0, b1, b2, b3])) !=
          BitVec.ofNat 128 (decodeUInt TargetEndian.little [b0, b1, b2, b3])) = false := by
      rw [hTrunc]
      exact bne_self_eq_false _
    have hDec : decodeValV2 profileV2TargetEndian (.int .i32 false)
        [.init b0 p0, .init b1 p1, .init b2 p2, .init b3 p3] =
        .ok (some (.scalar ⟨.i32, false,
          truncateBits .i32
            (BitVec.ofNat 128 (decodeUInt TargetEndian.little [b0, b1, b2, b3]))⟩)) := by
      change (match (if (truncateBits .i32
            (BitVec.ofNat 128 (decodeUInt TargetEndian.little [b0, b1, b2, b3])) !=
            BitVec.ofNat 128 (decodeUInt TargetEndian.little [b0, b1, b2, b3])) then
            Except.error FaultKind.unsupported
          else
            Except.ok (Val.scalar ⟨.i32, false,
              truncateBits .i32
                (BitVec.ofNat 128 (decodeUInt TargetEndian.little [b0, b1, b2, b3]))⟩)) with
        | Except.ok v => Except.ok (some v)
        | Except.error k => Except.error k) = _
      rw [ite_bool_false hBne]
    refine ⟨_, hDec, ?_⟩
    unfold checkValV2 checkVal Val.ty?
    dsimp only
    rw [hTrunc]
    have hEq :
        (truncateBits .i32
            (BitVec.ofNat 128 (decodeUInt TargetEndian.little [b0, b1, b2, b3])) ==
          BitVec.ofNat 128 (decodeUInt TargetEndian.little [b0, b1, b2, b3])) = true := by
      rw [hTrunc]; exact beq_self_eq_true _
    change (match (if (truncateBits .i32
          (BitVec.ofNat 128 (decodeUInt TargetEndian.little [b0, b1, b2, b3])) ==
          BitVec.ofNat 128 (decodeUInt TargetEndian.little [b0, b1, b2, b3])) then
          some (MirTy.int .i32 false) else none) with
      | some vTy => MirTy.beq vTy (.int .i32 false)
      | none => false) = true
    rw [hEq]; rfl

private theorem storeU8_ok (cm : CallerMemory) (pv : PtrVal) (aid : AllocId)
    (a : Allocation) (sv : ScalarVal)
    (hSvWf : checkValV2 (.scalar sv) (.int .i8 false) = true)
    (hFind : findAllocation aid cm.allocations = some a)
    (hLive : a.live = true)
    (hMut : a.mutability = .mut)
    (hBounds : isInBounds a pv.offsetBytes.toNat 1 = true) :
    ∃ mem' : MemoryState,
      storeIndirectV2 (entryMemoryWithCaller cm) (.int .i8 false)
        ⟨aid, pv.offsetBytes.toNat⟩ (.scalar sv) = .ok mem' := by
  unfold storeIndirectV2
  dsimp only [layoutOfTyV2, layoutOfTy, intLayout]
  have hEnc : encodeValV2 profileV2TargetEndian (.int .i8 false) (.scalar sv) =
      .ok ((encodeUInt profileV2TargetEndian 1 sv.bits.toNat).map
        (fun b => AllocByte.init b none)) := by
    unfold encodeValV2
    rw [ite_bool_false (by rw [hSvWf]; rfl)]
    unfold encodeVal
    rw [ite_bool_false (by
      have hV1 : checkVal (.scalar sv) (.int .i8 false) = true := hSvWf
      rw [hV1]; rfl)]
    rfl
  rw [hEnc]
  dsimp only
  have hLen1 :
      ((encodeUInt profileV2TargetEndian 1 sv.bits.toNat).map
        (fun b => AllocByte.init b none)).length = 1 := rfl
  have hWrite := writeBytes_nonempty_ok_of_alloc
    (m := entryMemoryWithCaller cm) (place := ⟨aid, pv.offsetBytes.toNat⟩)
    (by rw [hLen1]; rfl) hFind hLive hMut
    (by rw [hLen1]; exact hBounds) (isAligned_zero a pv.offsetBytes.toNat)
  rw [hWrite]
  exact ⟨_, rfl⟩

private theorem loadU32_correct (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_0 q)
    (hSafe : Spec.loadU32Safety q) :
    WellFormedV2 (entryProgForBody Captured.program 0) q ∧
    match q.args with
    | [.ptr pv] =>
      match pv.allocId with
      | none => False
      | some aid =>
        ∃ v : Val,
          loadIndirectV2 (entryMemoryWithCaller q.callerMem) (.int .i32 false)
            ⟨aid, pv.offsetBytes.toNat⟩ = .ok (some v) ∧
          BehaviorV2 (entryProgForBody Captured.program 0) q
            (TerminalOut.returned ⟨v, q.callerMem⟩)
    | _ => False := by
  have hCallerValid := hValid.1
  have hArgsMatch := hValid.2.1
  have hRefs := hValid.2.2.1
  have hDisj := hValid.2.2.2
  cases q with
  | mk args cm =>
    dsimp only at hCallerValid hArgsMatch hRefs hDisj
    unfold Spec.loadU32Safety at hSafe
    dsimp only at hSafe
    cases args with
    | nil => exact False.elim hSafe
    | cons a0 rest =>
      cases rest with
      | cons _ _ => cases a0 <;> (change False at hSafe; exact False.elim hSafe)
      | nil =>
        cases a0 with
        | scalar _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | bool _ | char _
        | ordering _ | unit | enumVal _ _ | tuple _ | array _ | bytes _ => exact False.elim hSafe
        | ptr pv =>
          dsimp only at hSafe
          cases hAid : pv.allocId with
          | none => rw [hAid] at hSafe; exact False.elim hSafe
          | some aid =>
            rw [hAid] at hSafe
            dsimp only at hSafe
            match hSafe with
            | ⟨a, hFind, hLive, hBounds, hAlign, hInit⟩ =>
              match loadU32_ok cm pv aid a hFind hLive hBounds hAlign hInit with
              | ⟨sv, hLoad, hVWf⟩ =>
                have hEntryEq0 :
                    entryMemoryForArgsV2 cm
                      ((Captured.body_0.locals.drop 1).take Captured.body_0.argumentCount)
                      [.ptr pv] = entryMemoryWithCaller cm := by
                  have hAidLe : aid ≤ maxAllocId cm.allocations := by
                    revert hFind
                    induction cm.allocations with
                    | nil => intro hF; cases hF
                    | cons x xs ih =>
                      intro hF
                      unfold findAllocation at hF
                      cases hBeq : Nat.beq x.allocId aid with
                      | true =>
                        have hEqId : x.allocId = aid := Nat.eq_of_beq_eq_true hBeq
                        subst hEqId
                        exact Nat.le_max_left _ _
                      | false =>
                        rw [hBeq] at hF
                        exact Nat.le_trans (ih hF) (Nat.le_max_right _ _)
                  have hLeBase :
                      maxValPtrAllocIdList [.ptr pv] + 1 ≤
                        (entryMemoryWithCaller cm).nextAllocId := by
                    dsimp only [maxValPtrAllocIdList, maxValPtrAllocId]
                    rw [hAid]
                    dsimp only [Option.getD]
                    have hMax0 : Nat.max aid 0 = aid := Nat.max_eq_left (Nat.zero_le aid)
                    rw [hMax0]
                    exact Nat.le_trans
                      (Nat.succ_le_succ (Nat.le_trans hAidLe (Nat.le_max_left _ _)))
                      (Nat.le_max_right _ _)
                  change {
                      nextAllocId := Nat.max (entryMemoryWithCaller cm).nextAllocId
                        (maxValPtrAllocIdList [.ptr pv] + 1)
                      allocations := (entryMemoryWithCaller cm).allocations
                    } = entryMemoryWithCaller cm
                  cases hBase : entryMemoryWithCaller cm with
                  | mk nextId allocs =>
                    rw [hBase] at hLeBase
                    dsimp only at hLeBase ⊢
                    have hMax : Nat.max nextId (maxValPtrAllocIdList [.ptr pv] + 1) = nextId :=
                      Nat.max_eq_left hLeBase
                    rw [hMax]
                have hStep0 :
                    initStateV2 (entryProgForBody Captured.program 0) ⟨[.ptr pv], cm⟩ =
                      .ok ⟨[⟨0, 0, 0, [.immediate none, .immediate (some (.ptr pv))],
                        none, none, none⟩],
                        cm, entryMemoryWithCaller cm⟩ := by
                  rw [← hEntryEq0]
                  exact initStateV2_ok_of (p := entryProgForBody Captured.program 0)
                    (q := ⟨[.ptr pv], cm⟩) (body := Captured.body_0)
                    rfl rfl hCallerValid rfl rfl rfl rfl rfl rfl rfl rfl
                    hArgsMatch hRefs hDisj
                have hReadP : readPlaceV2 Captured.body_0.locals
                    [.immediate none, .immediate (some (.ptr pv))]
                    (entryMemoryWithCaller cm) false ⟨1, [.deref]⟩ =
                    .ok (.int .i32 false, some (.scalar sv),
                      [.immediate none, .immediate (some (.ptr pv))],
                      entryMemoryWithCaller cm) := by
                  unfold readPlaceV2
                  change (match pv.allocId with
                    | none => _
                    | some aid =>
                      match loadIndirectV2 (entryMemoryWithCaller cm)
                          (MirTy.int IntWidth.i32 false) ⟨aid, pv.offsetBytes.toNat⟩ with
                      | Except.error k => Except.error k
                      | Except.ok optVal =>
                        Except.ok (MirTy.int IntWidth.i32 false, optVal,
                          [LocalSlot.immediate none, LocalSlot.immediate (some (Val.ptr pv))],
                          entryMemoryWithCaller cm)) = _
                  rw [hAid]
                  dsimp only
                  rw [hLoad]
                have hStep1 : evalStepV2 (entryProgForBody Captured.program 0)
                    ⟨[⟨0, 0, 0, [.immediate none, .immediate (some (.ptr pv))],
                      none, none, none⟩],
                      cm, entryMemoryWithCaller cm⟩ =
                    .step ⟨[⟨0, 0, 1,
                      [.immediate (some (Val.scalar sv)), .immediate (some (.ptr pv))],
                      none, none, none⟩],
                      cm, entryMemoryWithCaller cm⟩ := by
                  unfold evalStepV2
                  change (match evalRvalueV2 Captured.body_0.locals
                      [.immediate none, .immediate (some (.ptr pv))]
                      (entryMemoryWithCaller cm) (.int .i32 false)
                      (.use (.copy ⟨1, [.deref]⟩)) with
                    | Except.error k => StepResult.fault k
                    | Except.ok (val, l1, m1) =>
                      match writePlaceDestV2 l1 m1
                          (.local 0) (.int .i32 false) val with
                      | Except.error k => StepResult.fault k
                      | Except.ok (l2, m2) =>
                        StepResult.step
                          (State.mk [FrameState.mk 0 0 1 l2 none none none] cm m2)) = _
                  have hRv : evalRvalueV2 Captured.body_0.locals
                      [.immediate none, .immediate (some (.ptr pv))]
                      (entryMemoryWithCaller cm) (.int .i32 false)
                      (.use (.copy ⟨1, [.deref]⟩)) =
                      .ok (.scalar sv, [.immediate none, .immediate (some (.ptr pv))],
                        entryMemoryWithCaller cm) := by
                    unfold evalRvalueV2 evalOperandToSlotV2
                    dsimp only
                    rw [hReadP]; rfl
                  rw [hRv]
                  dsimp only
                  rw [writePlaceDestV2_immediate_ok hVWf rfl rfl]
                have hStep2 : evalStepV2 (entryProgForBody Captured.program 0)
                    ⟨[⟨0, 0, 1,
                      [.immediate (some (Val.scalar sv)), .immediate (some (.ptr pv))],
                      none, none, none⟩],
                      cm, entryMemoryWithCaller cm⟩ =
                    .done (.returned ⟨.scalar sv, cm⟩) := by
                  change StepResult.done
                    (TerminalOut.returned
                      ⟨.scalar sv, extractCallerMemory cm (entryMemoryWithCaller cm)⟩) = _
                  rw [extractCallerMemory_entry cm hCallerValid]
                have hExec : execProgV2 (entryProgForBody Captured.program 0) 4
                    ⟨[.ptr pv], cm⟩
                    (fun out => out = TerminalOut.returned ⟨.scalar sv, cm⟩) := by
                  unfold execProgV2
                  rw [hStep0]
                  exact execOutcomeStateV2_step hStep1 (execOutcomeStateV2_done hStep2 rfl)
                have hRes := spec_and_behaviorV2_of_exec_eq hExec
                refine ⟨hRes.1, ?_⟩
                dsimp only
                rw [hAid]
                exact ⟨.scalar sv, hLoad, hRes.2.1⟩

private theorem storeU8_correct (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_1 q)
    (hSafe : Spec.storeU8Safety q) :
    WellFormedV2 (entryProgForBody Captured.program 1) q ∧
    match q.args with
    | [.ptr pv, .scalar sv] =>
      match pv.allocId with
      | none => False
      | some aid =>
        ∃ mem' : MemoryState,
          storeIndirectV2 (entryMemoryWithCaller q.callerMem) (.int .i8 false)
            ⟨aid, pv.offsetBytes.toNat⟩ (.scalar sv) = .ok mem' ∧
          BehaviorV2 (entryProgForBody Captured.program 1) q
            (TerminalOut.returned ⟨.unit, extractCallerMemory q.callerMem mem'⟩)
    | _ => False := by
  have hCallerValid := hValid.1
  have hArgsMatch := hValid.2.1
  have hRefs := hValid.2.2.1
  have hDisj := hValid.2.2.2
  cases q with
  | mk args cm =>
    dsimp only at hCallerValid hArgsMatch hRefs hDisj
    unfold Spec.storeU8Safety at hSafe
    dsimp only at hSafe
    cases args with
    | nil => exact False.elim hSafe
    | cons a0 r0 =>
      cases r0 with
      | nil => cases a0 <;> exact False.elim hSafe
      | cons a1 r1 =>
        cases r1 with
        | cons _ _ =>
          cases a0 <;> (try exact False.elim hSafe)
          cases a1 <;> exact False.elim hSafe
        | nil =>
          cases a0 with
          | scalar _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | bool _ | char _
          | ordering _ | unit | enumVal _ _ | tuple _ | array _ | bytes _ => exact False.elim hSafe
          | ptr pv =>
            cases a1 with
            | ptr _ | slicePtr _ _ | rangeTo _ | rangeFrom _ | bool _ | char _
            | ordering _ | unit | enumVal _ _ | tuple _ | array _ | bytes _ => exact False.elim hSafe
            | scalar sv =>
              dsimp only at hSafe
              cases hAid : pv.allocId with
              | none => rw [hAid] at hSafe; exact False.elim hSafe
              | some aid =>
                rw [hAid] at hSafe
                dsimp only at hSafe
                match hSafe with
                | ⟨a, hFind, hLive, hMut, hBounds⟩ =>
                  have hArgsMatch' := hArgsMatch
                  dsimp only [checkArgsMatchV2, Captured.body_1, List.drop, List.take,
                    List.foldr, Bool.and_true] at hArgsMatch'
                  have hPvWf : checkValV2 (.ptr pv) (.rawPtr .mut (.int .i8 false)) = true := by
                    cases h1 : checkValV2 (.ptr pv) (.rawPtr .mut (.int .i8 false)) with
                    | true => rfl
                    | false => rw [h1] at hArgsMatch'; exact Bool.noConfusion hArgsMatch'
                  have hSvWf : checkValV2 (.scalar sv) (.int .i8 false) = true := by
                    rw [hPvWf] at hArgsMatch'
                    cases h2 : checkValV2 (.scalar sv) (.int .i8 false) with
                    | true => rfl
                    | false => rw [h2] at hArgsMatch'; exact Bool.noConfusion hArgsMatch'
                  match storeU8_ok cm pv aid a sv hSvWf hFind hLive hMut hBounds with
                  | ⟨mem', hStore⟩ =>
                    have hEntryEq1 :
                        entryMemoryForArgsV2 cm
                          ((Captured.body_1.locals.drop 1).take Captured.body_1.argumentCount)
                          [.ptr pv, .scalar sv] = entryMemoryWithCaller cm := by
                      have hAidLe : aid ≤ maxAllocId cm.allocations := by
                        revert hFind
                        induction cm.allocations with
                        | nil => intro hF; cases hF
                        | cons x xs ih =>
                          intro hF
                          unfold findAllocation at hF
                          cases hBeq : Nat.beq x.allocId aid with
                          | true =>
                            have hEqId : x.allocId = aid := Nat.eq_of_beq_eq_true hBeq
                            subst hEqId
                            exact Nat.le_max_left _ _
                          | false =>
                            rw [hBeq] at hF
                            exact Nat.le_trans (ih hF) (Nat.le_max_right _ _)
                      have hLeBase :
                          maxValPtrAllocIdList [.ptr pv, .scalar sv] + 1 ≤
                            (entryMemoryWithCaller cm).nextAllocId := by
                        dsimp only [maxValPtrAllocIdList, maxValPtrAllocId]
                        rw [hAid]
                        dsimp only [Option.getD]
                        have hMax0 : Nat.max aid (Nat.max 0 0) = aid :=
                          Nat.max_eq_left (Nat.zero_le aid)
                        rw [hMax0]
                        exact Nat.le_trans
                          (Nat.succ_le_succ (Nat.le_trans hAidLe (Nat.le_max_left _ _)))
                          (Nat.le_max_right _ _)
                      change {
                          nextAllocId := Nat.max (entryMemoryWithCaller cm).nextAllocId
                            (maxValPtrAllocIdList [.ptr pv, .scalar sv] + 1)
                          allocations := (entryMemoryWithCaller cm).allocations
                        } = entryMemoryWithCaller cm
                      cases hBase : entryMemoryWithCaller cm with
                      | mk nextId allocs =>
                        rw [hBase] at hLeBase
                        dsimp only at hLeBase ⊢
                        have hMax :
                            Nat.max nextId (maxValPtrAllocIdList [.ptr pv, .scalar sv] + 1) =
                              nextId :=
                          Nat.max_eq_left hLeBase
                        rw [hMax]
                    have hStep0 :
                        initStateV2 (entryProgForBody Captured.program 1)
                          ⟨[.ptr pv, .scalar sv], cm⟩ =
                        .ok ⟨[⟨1, 0, 0, [
                            .immediate (some .unit),
                            .immediate (some (.ptr pv)),
                            .immediate (some (.scalar sv)),
                            .dead
                          ], none, none, none⟩], cm, entryMemoryWithCaller cm⟩ := by
                      rw [← hEntryEq1]
                      exact initStateV2_ok_of (p := entryProgForBody Captured.program 1)
                        (q := ⟨[.ptr pv, .scalar sv], cm⟩) (body := Captured.body_1)
                        rfl rfl hCallerValid rfl rfl rfl rfl rfl rfl rfl rfl
                        hArgsMatch hRefs hDisj
                    have hStep1 : evalStepV2 (entryProgForBody Captured.program 1)
                        ⟨[⟨1, 0, 0,
                          [.immediate (some .unit), .immediate (some (.ptr pv)),
                           .immediate (some (.scalar sv)), .dead], none, none, none⟩],
                          cm, entryMemoryWithCaller cm⟩ =
                        .step ⟨[⟨1, 0, 1,
                          [.immediate (some .unit), .immediate (some (.ptr pv)),
                           .immediate (some (.scalar sv)), .immediate none], none, none, none⟩],
                          cm, entryMemoryWithCaller cm⟩ := rfl
                    have hStep2 : evalStepV2 (entryProgForBody Captured.program 1)
                        ⟨[⟨1, 0, 1,
                          [.immediate (some .unit), .immediate (some (.ptr pv)),
                           .immediate (some (.scalar sv)), .immediate none], none, none, none⟩],
                          cm, entryMemoryWithCaller cm⟩ =
                        .step ⟨[⟨1, 0, 2,
                          [.immediate (some .unit), .immediate (some (.ptr pv)),
                           .immediate (some (.scalar sv)),
                           .immediate (some (.scalar sv))], none, none, none⟩],
                          cm, entryMemoryWithCaller cm⟩ := by
                      unfold evalStepV2
                      change (match writePlaceDestV2
                          [.immediate (some .unit), .immediate (some (.ptr pv)),
                           .immediate (some (.scalar sv)), .immediate none]
                          (entryMemoryWithCaller cm) (.local 3) (.int .i8 false) (.scalar sv) with
                        | Except.error k => StepResult.fault k
                        | Except.ok (l2, m2) =>
                          StepResult.step
                            (State.mk [FrameState.mk 1 0 2 l2 none none none] cm m2)) = _
                      rw [writePlaceDestV2_immediate_ok hSvWf rfl rfl]
                    have hWp3 : writePlaceDestV2
                        [.immediate (some .unit), .immediate (some (.ptr pv)),
                         .immediate (some (.scalar sv)), .immediate none]
                        (entryMemoryWithCaller cm) (.deref (.int .i8 false) ⟨1, 0⟩ pv)
                        (.int .i8 false) (.scalar sv) =
                        .ok ([.immediate (some .unit), .immediate (some (.ptr pv)),
                          .immediate (some (.scalar sv)), .immediate none], mem') :=
                      writePlaceDestV2_deref_ok hSvWf hAid hFind hLive hMut hStore
                    have hStep3 : evalStepV2 (entryProgForBody Captured.program 1)
                        ⟨[⟨1, 0, 2,
                          [.immediate (some .unit), .immediate (some (.ptr pv)),
                           .immediate (some (.scalar sv)),
                           .immediate (some (.scalar sv))], none, none, none⟩],
                          cm, entryMemoryWithCaller cm⟩ =
                        .step ⟨[⟨1, 0, 3,
                          [.immediate (some .unit), .immediate (some (.ptr pv)),
                           .immediate (some (.scalar sv)), .immediate none], none, none, none⟩],
                          cm, mem'⟩ := by
                      unfold evalStepV2
                      change (match writePlaceDestV2
                          [.immediate (some .unit), .immediate (some (.ptr pv)),
                           .immediate (some (.scalar sv)), .immediate none]
                          (entryMemoryWithCaller cm) (.deref (.int .i8 false) ⟨1, 0⟩ pv)
                          (.int .i8 false) (.scalar sv) with
                        | Except.error k => StepResult.fault k
                        | Except.ok (l2, m2) =>
                          StepResult.step
                            (State.mk [FrameState.mk 1 0 3 l2 none none none] cm m2)) = _
                      rw [hWp3]
                    have hStep4 : evalStepV2 (entryProgForBody Captured.program 1)
                        ⟨[⟨1, 0, 3,
                          [.immediate (some .unit), .immediate (some (.ptr pv)),
                           .immediate (some (.scalar sv)), .immediate none], none, none, none⟩],
                          cm, mem'⟩ =
                        .step ⟨[⟨1, 0, 4,
                          [.immediate (some .unit), .immediate (some (.ptr pv)),
                           .immediate (some (.scalar sv)), .dead], none, none, none⟩],
                          cm, mem'⟩ := rfl
                    have hStep5 : evalStepV2 (entryProgForBody Captured.program 1)
                        ⟨[⟨1, 0, 4,
                          [.immediate (some .unit), .immediate (some (.ptr pv)),
                           .immediate (some (.scalar sv)), .dead], none, none, none⟩],
                          cm, mem'⟩ =
                        .step ⟨[⟨1, 0, 5,
                          [.immediate (some .unit), .immediate (some (.ptr pv)),
                           .immediate (some (.scalar sv)), .dead], none, none, none⟩],
                          cm, mem'⟩ := rfl
                    have hStep6 : evalStepV2 (entryProgForBody Captured.program 1)
                        ⟨[⟨1, 0, 5,
                          [.immediate (some .unit), .immediate (some (.ptr pv)),
                           .immediate (some (.scalar sv)), .dead], none, none, none⟩],
                          cm, mem'⟩ =
                        .done (.returned ⟨.unit, extractCallerMemory cm mem'⟩) := rfl
                    have hExec : execProgV2 (entryProgForBody Captured.program 1) 8
                        ⟨[.ptr pv, .scalar sv], cm⟩
                        (fun out =>
                          out = TerminalOut.returned ⟨.unit, extractCallerMemory cm mem'⟩) := by
                      unfold execProgV2
                      rw [hStep0]
                      exact execOutcomeStateV2_step hStep1
                        (execOutcomeStateV2_step hStep2
                          (execOutcomeStateV2_step hStep3
                            (execOutcomeStateV2_step hStep4
                              (execOutcomeStateV2_step hStep5
                                (execOutcomeStateV2_done hStep6 rfl)))))
                    have hRes := spec_and_behaviorV2_of_exec_eq hExec
                    refine ⟨hRes.1, ?_⟩
                    dsimp only
                    rw [hAid]
                    exact ⟨mem', hStore, hRes.2.1⟩

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro defId body hFound
    cases defId with
    | zero =>
      have hEq : Captured.body_0 = body := Option.some.inj hFound
      subst hEq
      refine ⟨hFound, rfl, fun q hValid hSafe => ?_⟩
      exact (loadU32_correct q hValid (hSafe rfl)).1
    | succ n =>
      cases n with
      | zero =>
        have hEq : Captured.body_1 = body := Option.some.inj hFound
        subst hEq
        refine ⟨hFound, rfl, fun q hValid hSafe => ?_⟩
        exact (storeU8_correct q hValid (hSafe rfl)).1
      | succ _ => cases hFound
  · refine ⟨?_, ?_⟩
    · intro q hValid hSafe
      exact (loadU32_correct q hValid hSafe).2
    · intro q hValid hSafe
      exact (storeU8_correct q hValid hSafe).2

end Proof
