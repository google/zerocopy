-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.SimpLemmas
import Init.Data.List.Basic
import Expected
import Anneal.MirWp.V2Memory

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

/-! ## Problem-Specific Helpers & Shared `split_at_unchecked` Correctness -/

theorem initLocalsLoop_body0 (ptrAid : Option AllocId) (ptrOff : UInt64) (len : UInt64)
    (midBits : BitVec 128) :
    initLocalsLoop Captured.body_0
      [.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len, .scalar ⟨.isize, false, midBits⟩]
      0 Captured.body_0.locals =
    [.immediate none,
     .immediate (some (.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len)),
     .immediate (some (.scalar ⟨.isize, false, midBits⟩)),
     .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead] :=
  rfl

theorem split_at_shared_correct (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_0 q)
    (hSafe : Spec.splitAtSafety q) :
    match q.args with
    | [.slicePtr ptr len, .scalar mid] =>
      let pR :=
        match ptr.allocId with
        | none => ptr
        | some _ =>
          { ptr with offsetBytes := UInt64.ofNat (ptr.offsetBytes.toNat + mid.bits.toNat) }
      let lenL := UInt64.ofNat mid.bits.toNat
      let lenR := UInt64.ofNat (len.toNat - mid.bits.toNat)
      WellFormedV2 (entryProgForBody Captured.program 0) q ∧
      (∃ out : TerminalOut,
        BehaviorV2 (entryProgForBody Captured.program 0) q out ∧
        out = TerminalOut.returned
          ⟨.tuple [.slicePtr ptr lenL, .slicePtr pR lenR], q.callerMem⟩ ∧
        lenL.toNat + lenR.toNat = len.toNat)
    | _ => False := by
  let ⟨hCM, hMatch, hRefs, _⟩ := hValid
  have hMatch' :
      checkArgsMatchV2 q.args [.ref .shared (.slice (.int .i8 false)), .int .isize false] = true :=
    hMatch
  let ⟨ptr, len, midBits, hArgs, hPtrW, hMidWf⟩ := checkArgsMatchV2_slice_u8_isize_inv hMatch'
  unfold Spec.splitAtSafety at hSafe
  rw [hArgs] at hSafe
  cases ptr with
  | mk ptrAid ptrOff ptrW =>
    dsimp only at hPtrW
    subst hPtrW
    have hMidLe : midBits.toNat ≤ len.toNat := hSafe
    have hLenLt64 : len.toNat < Nat.pow 2 64 := len.toBitVec.isLt
    have hMidLt64 : midBits.toNat < Nat.pow 2 64 :=
      Nat.lt_of_le_of_lt hMidLe hLenLt64
    have hSubLt64 : len.toNat - midBits.toNat < Nat.pow 2 64 :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) hLenLt64
    have hLenLNat : (UInt64.ofNat midBits.toNat).toNat = midBits.toNat :=
      toNat_uint64_ofNat_lt hMidLt64
    have hLenRNat : (UInt64.ofNat (len.toNat - midBits.toNat)).toNat =
        len.toNat - midBits.toNat :=
      toNat_uint64_ofNat_lt hSubLt64
    have hSumLen : (UInt64.ofNat midBits.toNat).toNat +
        (UInt64.ofNat (len.toNat - midBits.toNat)).toNat = len.toNat := by
      rw [hLenLNat, hLenRNat]
      exact Nat.add_sub_of_le hMidLe
    let ptr : PtrVal := ⟨ptrAid, ptrOff, .isize⟩
    let m : MemoryState := entryMemoryWithCaller q.callerMem
    let lenL := UInt64.ofNat midBits.toNat
    let lenR := UInt64.ofNat (len.toNat - midBits.toNat)
    let pR : PtrVal := ⟨ptrAid, UInt64.ofNat (ptrOff.toNat + midBits.toNat), .isize⟩
    have hQ : q = ⟨[.slicePtr ptr len, .scalar ⟨.isize, false, midBits⟩], q.callerMem⟩ := by
      cases q; dsimp only at hArgs; rw [hArgs]
    have hRefValid0 :
        refValidInMem m .shared (.slice (.int .i8 false)) (.slicePtr ptr len) = .ok () := by
      have hRefs' :
          refsValidInMemList m
            [.ref .shared (.slice (.int .i8 false)), .int .isize false]
            [.slicePtr ptr len, .scalar ⟨.isize, false, midBits⟩] = true := by
        rw [← hArgs]; exact hRefs
      dsimp only [refsValidInMemList, refsValidInMem] at hRefs'
      cases hR : refValidInMem m .shared (.slice (.int .i8 false)) (.slicePtr ptr len) with
      | error k => rw [hR] at hRefs'; cases hRefs'
      | ok u => cases u; rfl
    have hOrig : sliceFromRawPartsCheck m false 1 0 ptr len = .ok (.slicePtr ptr len) :=
      sliceCheck_of_refValidInMem hRefValid0
    have hPtrAdd0 : ptrAddInMem m 1 ptr 0 = .ok ptr := by
      have h := ptrAddInMem_u8_of_sliceCheck 0 hOrig (Nat.zero_le _)
      rw [Nat.add_zero, uint64_ofNat_toNat] at h
      exact h
    have hSliceL : sliceFromRawPartsCheck m false 1 0 ptr lenL = .ok (.slicePtr ptr lenL) := by
      have hOff0Lt : ptr.offsetBytes.toNat + 0 < Nat.pow 2 64 := by
        rw [Nat.add_zero]; exact ptr.offsetBytes.toBitVec.isLt
      have h := sliceFromRawPartsCheck_u8_to_subslice (outMut := false) 0 midBits.toNat
        (fun hm => nomatch hm) hOrig (by rw [Nat.zero_add]; exact hMidLe) hOff0Lt
      dsimp only [ptr] at h ⊢
      rw [Nat.add_zero, uint64_ofNat_toNat] at h
      exact h
    have hPOffLt : ptrOff.toNat + midBits.toNat < Nat.pow 2 64 := by
      cases hAid : ptrAid with
      | none =>
        have ⟨_, hLen0⟩ :=
          (sliceFromRawPartsCheck_u8_inv hOrig).2.2.1 (by dsimp only [ptr]; rw [hAid])
        rw [hLen0] at hMidLe
        rw [Nat.eq_zero_of_le_zero hMidLe, Nat.add_zero]
        exact ptrOff.toBitVec.isLt
      | some aid =>
        have ⟨a, hFind, _, hBnd, _, _⟩ :=
          (sliceFromRawPartsCheck_u8_inv hOrig).2.2.2 aid (by dsimp only [ptr]; rw [hAid])
        have hLt64 : a.bytes.length < Nat.pow 2 64 :=
          entryMemoryWithCaller_bytes_lt q.callerMem hCM hFind
        have hBndMid : ptrOff.toNat + midBits.toNat ≤ a.bytes.length :=
          Nat.le_trans (Nat.add_le_add_left hMidLe _) hBnd
        exact Nat.lt_of_le_of_lt hBndMid hLt64
    have hPtrAddR : ptrAddInMem m 1 ptr midBits.toNat = .ok pR :=
      ptrAddInMem_u8_of_sliceCheck midBits.toNat hOrig hMidLe
    have hSliceR : sliceFromRawPartsCheck m false 1 0 pR lenR = .ok (.slicePtr pR lenR) :=
      sliceFromRawPartsCheck_u8_to_subslice midBits.toNat (len.toNat - midBits.toNat)
        (fun hm => by cases hm) hOrig
        (by rw [Nat.add_sub_of_le hMidLe]; exact Nat.le_refl _) hPOffLt
    have hPRW : pR.width = .isize := rfl
    have hPRSpecEq : pR =
        match ptr.allocId with
        | none => ptr
        | some _ =>
          { ptr with offsetBytes := UInt64.ofNat (ptr.offsetBytes.toNat + midBits.toNat) } := by
      dsimp only [ptr, pR]
      cases hAid : ptrAid with
      | none =>
        have ⟨_, hLen0⟩ :=
          (sliceFromRawPartsCheck_u8_inv hOrig).2.2.1 (by dsimp only [ptr]; rw [hAid])
        rw [hLen0] at hMidLe
        rw [Nat.eq_zero_of_le_zero hMidLe, Nat.add_zero, uint64_ofNat_toNat]
      | some _ => rfl
    let expectedOut : TerminalOut :=
      .returned ⟨.tuple [.slicePtr ptr lenL, .slicePtr pR lenR], q.callerMem⟩
    have hRefValidL :
        refValidInMem m .shared (.slice (.int .i8 false)) (.slicePtr ptr lenL) = .ok () :=
      refValidInMem_of_sliceCheck hSliceL
    have hRefValidR :
        refValidInMem m .shared (.slice (.int .i8 false)) (.slicePtr pR lenR) = .ok () :=
      refValidInMem_of_sliceCheck hSliceR
    have hGetTo :
        sliceGetUncheckedCheck m ptr len.toNat 0 lenL.toNat =
          .ok (.slicePtr ptr lenL) := by
      unfold sliceGetUncheckedCheck
      rw [hLenLNat]
      rw [Nat.ble_eq_true_of_le (Nat.zero_le _), Nat.ble_eq_true_of_le hMidLe]
      change (if false = true then _ else _) = _
      rw [ite_bool_false rfl]
      rw [hPtrAdd0]
      dsimp only
      rw [Nat.sub_zero]
    have hGetFrom :
        sliceGetUncheckedCheck m ptr len.toNat lenL.toNat len.toNat =
          .ok (.slicePtr pR lenR) := by
      unfold sliceGetUncheckedCheck
      rw [hLenLNat]
      rw [Nat.ble_eq_true_of_le hMidLe, Nat.ble_eq_true_of_le (Nat.le_refl _)]
      change (if false = true then _ else _) = _
      rw [ite_bool_false rfl]
      rw [hPtrAddR]
    have hStay :
        refsStayInCallerMem q.callerMem
          (.tuple [.ref .shared (.slice (.int .i8 false)),
                   .ref .shared (.slice (.int .i8 false))])
          (.tuple [.slicePtr ptr lenL, .slicePtr pR lenR]) = true := by
      have h1 := refsStayInCallerMem_of_refValid hRefValidL
      unfold refsStayInCallerMem refAllocIds at h1 ⊢
      dsimp only [refAllocIdsList, refAllocIds, ptr, pR] at h1 ⊢
      cases hAid : ptrAid with
      | none => rfl
      | some aid =>
        rw [hAid] at h1
        change ((findAllocation aid q.callerMem.allocations).isSome && true) = true at h1
        change ((findAllocation aid q.callerMem.allocations).isSome &&
          ((findAllocation aid q.callerMem.allocations).isSome && true)) = true
        cases hF : (findAllocation aid q.callerMem.allocations).isSome with
        | false => rw [hF] at h1; cases h1
        | true => rfl
    have hDisjOut :
        spansPairwiseDisjoint
          (refAccessSpansList
            [.ref .shared (.slice (.int .i8 false)),
             .ref .shared (.slice (.int .i8 false))]
            [.slicePtr ptr lenL, .slicePtr pR lenR]) = true :=
      spansPairwiseDisjoint_slice_u8_pair (.inl ⟨rfl, rfl⟩)
    have hExt : extractCallerMemory q.callerMem m = q.callerMem :=
      extractCallerMemory_entry q.callerMem hCM
    let ctx : BodyCtx := ⟨Captured.program, 0, Captured.body_0⟩
    have h_body : ctx.HasBody := rfl
    have hValid' : ValidEntryArgsV2 Captured.body_0
        ⟨[.slicePtr ptr len, .scalar ⟨.isize, false, midBits⟩], q.callerMem⟩ := by
      rw [← hQ]; exact hValid
    have hInit :
        initStateV2 (entryProgForBody Captured.program 0)
          ⟨[.slicePtr ptr len, .scalar ⟨.isize, false, midBits⟩], q.callerMem⟩ =
        .ok (State.mk [FrameState.mk 0 0 0
          [.immediate none,
           .immediate (some (.slicePtr ptr len)),
           .immediate (some (.scalar ⟨.isize, false, midBits⟩)),
           .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead]
          none none none]
          q.callerMem m) := by
      have h0 := ctx.initStateV2_ok_of h_body (by decide) hValid'
      change initStateV2 ctx.entryProg _ = _
      rw [h0]
      change Except.ok (State.mk [FrameState.mk 0 0 0
        (initLocalsLoop Captured.body_0
          [.slicePtr ⟨ptrAid, ptrOff, .isize⟩ len, .scalar ⟨.isize, false, midBits⟩]
          0 Captured.body_0.locals) none none none] q.callerMem m) = _
      rw [initLocalsLoop_body0]
    have hExec :
        execProgV2 (entryProgForBody Captured.program 0) 32
          ⟨[.slicePtr ptr len, .scalar ⟨.isize, false, midBits⟩], q.callerMem⟩
          (fun o => o = expectedOut) := by
      unfold execProgV2
      rw [hInit]
      -- bb0 stmts 0,1,2: storageLive 3,4,5
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_step (by rfl)
      -- bb0 stmt 3: assign 5 (.ref .shared [1, .deref])
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          evalStatementV2, resolvePlaceDestV2, placeStaticTyV2, evalRvalueV2,
          evalRefRvalueV2, writePlaceDestV2, checkValV2,
          Trusted.MirSemantics.getElem?, Trusted.MirSemantics.setElem?]
        rw [hRefValid0]
        rfl)
      -- bb0 stmts 4,5: storageLive 6,7
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_step (by rfl)
      -- bb0 stmt 6: assign 7 (.use (.copy 2))
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
          Trusted.MirSemantics.getElem?]
        rw [evalRvalueV2_use_copy_ok (by rfl) (by rfl) (by rfl)]
        dsimp only
        rw [writePlaceDestV2_immediate_ok
          (by dsimp only [checkValV2, checkVal, Val.ty?]; rw [hMidWf]; rfl)
          (by rfl) (by rfl)]
        rfl)
      -- bb0 stmts 7,8: aggregateRangeTo -> 6, storageDead 7
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          evalStatementV2, resolvePlaceDestV2, placeStaticTyV2, evalRvalueV2,
          evalOperandToSlotV2, Trusted.MirSemantics.getElem?]
        rw [readPlaceV2_move_local (by rfl) (by rfl) (by rfl) (by rfl)]
        rfl)
      apply execOutcomeStateV2_step (by rfl)
      -- bb0 term: coreCall sliceGetUncheckedRangeTo -> 4, bb1
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          evalTerminatorV2, evalArgOperandsV2, evalOperandToSlotV2,
          Trusted.MirSemantics.getElem?]
        rw [readPlaceV2_move_local (by rfl) (by rfl) (by rfl) (by rfl)]
        dsimp only
        rw [readPlaceV2_move_local (by rfl) (by rfl) (by rfl) (by rfl)]
        dsimp only [execCoreCallWithMem]
        rw [execCoreCallOp_sliceGetUncheckedRangeTo_shared_ok hRefValid0 hGetTo]
        dsimp only
        rw [writePlaceV2_immediate_ok (by rfl) (by rfl) (by rfl)]
        rfl)
      -- bb1 stmt 0: assign 3 (.ref .shared [4, .deref])
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          evalStatementV2, resolvePlaceDestV2, placeStaticTyV2, evalRvalueV2,
          evalRefRvalueV2, writePlaceDestV2, checkValV2,
          Trusted.MirSemantics.getElem?, Trusted.MirSemantics.setElem?]
        rw [hRefValidL]
        rfl)
      -- bb1 stmts 1..5: storageDead 6,5; storageLive 8,9,10
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_step (by rfl)
      -- bb1 stmt 6: assign 10 (.ref .shared [1, .deref])
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          evalStatementV2, resolvePlaceDestV2, placeStaticTyV2, evalRvalueV2,
          evalRefRvalueV2, writePlaceDestV2, checkValV2,
          Trusted.MirSemantics.getElem?, Trusted.MirSemantics.setElem?]
        rw [hRefValid0]
        rfl)
      -- bb1 stmts 7,8: storageLive 11,12
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_step (by rfl)
      -- bb1 stmt 9: assign 12 (.use (.copy 2))
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          evalStatementV2, resolvePlaceDestV2, placeStaticTyV2,
          Trusted.MirSemantics.getElem?]
        rw [evalRvalueV2_use_copy_ok (by rfl) (by rfl) (by rfl)]
        dsimp only
        rw [writePlaceDestV2_immediate_ok
          (by dsimp only [checkValV2, checkVal, Val.ty?]; rw [hMidWf]; rfl)
          (by rfl) (by rfl)]
        rfl)
      -- bb1 stmts 10,11: aggregateRangeFrom -> 11, storageDead 12
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          evalStatementV2, resolvePlaceDestV2, placeStaticTyV2, evalRvalueV2,
          evalOperandToSlotV2, Trusted.MirSemantics.getElem?]
        rw [readPlaceV2_move_local (by rfl) (by rfl) (by rfl) (by rfl)]
        rfl)
      apply execOutcomeStateV2_step (by rfl)
      -- bb1 term: coreCall sliceGetUncheckedRangeFrom -> 9, bb2
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          evalTerminatorV2, evalArgOperandsV2, evalOperandToSlotV2,
          Trusted.MirSemantics.getElem?]
        rw [readPlaceV2_move_local (by rfl) (by rfl) (by rfl) (by rfl)]
        dsimp only
        rw [readPlaceV2_move_local (by rfl) (by rfl) (by rfl) (by rfl)]
        dsimp only
        dsimp only [execCoreCallWithMem]
        rw [execCoreCallOp_sliceGetUncheckedRangeFrom_shared_ok hRefValid0 hGetFrom]
        dsimp only
        rw [writePlaceV2_immediate_ok
          (by dsimp only [checkValV2]; rw [hPRW]; rfl)
          (by rfl) (by rfl)]
        rfl)
      -- bb2 stmt 0: assign 8 (.ref .shared [9, .deref])
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          evalStatementV2, resolvePlaceDestV2, placeStaticTyV2, evalRvalueV2,
          Trusted.MirSemantics.getElem?]
        rw [evalRefRvalueV2_deref_ok (by rfl) (by rfl) (by rfl) hRefValidR]
        dsimp only
        rw [writePlaceDestV2_immediate_ok
          (by dsimp only [checkValV2]; rw [hPRW]; rfl)
          (by rfl) (by rfl)]
        rfl)
      -- bb2 stmts 1..7: storageDead 11,10; aggregateTuple -> 0;
      -- storageDead 8,3,9,4.
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_step (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          evalStatementV2, resolvePlaceDestV2, placeStaticTyV2, evalRvalueV2,
          evalArgOperandsV2, evalOperandToSlotV2, Trusted.MirSemantics.getElem?]
        rw [readPlaceV2_move_local (by rfl) (by rfl) (by rfl) (by rfl)]
        dsimp only
        rw [readPlaceV2_move_local (by rfl) (by rfl) (by rfl) (by rfl)]
        dsimp only
        rw [ite_bool_false (by
          change (!checkValV2List [.slicePtr ptr lenL, .slicePtr pR lenR]
            [.ref .shared (.slice (.int .i8 false)),
             .ref .shared (.slice (.int .i8 false))]) = false
          dsimp only [checkValV2List, checkValV2]; rw [hPRW]; rfl)]
        dsimp only
        rw [writePlaceDestV2_immediate_ok
          (by change checkValV2 (.tuple [.slicePtr ptr lenL, .slicePtr pR lenR]) _ = true
              dsimp only [checkValV2, checkValV2List]; rw [hPRW]; rfl)
          (by rfl) (by rfl)]
        rfl)
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_step (by rfl)
      apply execOutcomeStateV2_step (by rfl)
      -- bb2 term: return_
      apply execOutcomeStateV2_done (by
        dsimp only [evalStepV2, entryProgForBody, Captured.program, Captured.body_0,
          Trusted.MirSemantics.getElem?]
        rw [evalTerminatorV2_return_ok (by rfl) (by rfl) (by rfl) (by rfl) hStay
          (by dsimp only [refsValidInMem, refsValidInMemList]; rw [hRefValidL, hRefValidR]; rfl)
          hDisjOut, hExt]
        rfl)
      rfl
    have hRes := spec_and_behaviorV2_of_exec_eq hExec
    rw [← hQ] at hRes
    rw [hArgs]
    refine ⟨hRes.1, expectedOut, hRes.2.1, ?_, hSumLen⟩
    dsimp only [expectedOut]
    rw [hPRSpecEq]

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · intro defId body hBody
    cases defId with
    | zero =>
      change some Captured.body_0 = some body at hBody
      cases hBody
      refine ⟨rfl, by decide, ?_⟩
      intro q hValid hSafe
      have hId0 : Captured.body_0.identity = Spec.splitAtSharedIdentity := by decide
      have hPre : Spec.splitAtSafety q := by
        have hS := hSafe rfl
        change Spec.safetyPre Captured.body_0.identity q at hS
        unfold Spec.safetyPre at hS
        rw [hId0] at hS
        split at hS
        · exact hS
        · exact absurd rfl (by assumption)
      have hCor := split_at_shared_correct q hValid hPre
      let ⟨_, _, _, hArgs, _, _⟩ := checkArgsMatchV2_slice_u8_isize_inv hValid.2.1
      rw [hArgs] at hCor
      exact hCor.1
    | succ _ =>
      change none = some body at hBody
      cases hBody
  · intro q hValid hSafe
    have hCor := split_at_shared_correct q hValid hSafe
    let ⟨_, _, _, hArgs, _, _⟩ := checkArgsMatchV2_slice_u8_isize_inv hValid.2.1
    rw [hArgs] at hCor ⊢
    exact hCor.2

end Proof
