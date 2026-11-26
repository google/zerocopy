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
import Anneal.MirWp.V2StepShield

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

/-! ## Per-Body Correctness -/

/-- `<&[u8] as IntoByteSlice>::into_byte_slice`: `_0 = useRetag(copy _1)`. -/
theorem body0_correct (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_0 q) :
    ∃ ptr len, q.args = [.slicePtr ptr len] ∧
      execProgV2 (entryProgForBody Captured.program 0) 8 q
        (fun o => o = .returned ⟨.slicePtr ptr len, q.callerMem⟩) := by
  let ⟨ptrAid, ptrOff, len, hArgs, hCM, hRef⟩ :=
    validEntryArgsV2_slice_u8_inv (reqMut := .shared) rfl hValid
  let ptr : PtrVal := ⟨ptrAid, ptrOff, .isize⟩
  let m : MemoryState := entryMemoryWithCaller q.callerMem
  refine ⟨ptr, len, hArgs, ?_⟩
  have hQ : q = ⟨[.slicePtr ptr len], q.callerMem⟩ := by
    cases q; dsimp only at hArgs; rw [hArgs]
  have hRV := refsValidInMem_of_refValid hRef
  have hStay : refsStayInCallerMem q.callerMem
      (.ref .shared (.slice (.int .i8 false))) (.slicePtr ptr len) = true :=
    refsStayInCallerMem_of_refValid hRef
  have hExt : extractCallerMemory q.callerMem m = q.callerMem :=
    extractCallerMemory_entry q.callerMem hCM
  let ctx : BodyCtx := ⟨Captured.program, 0, Captured.body_0⟩
  have hInit :
      initStateV2 (entryProgForBody Captured.program 0)
        ⟨[.slicePtr ptr len], q.callerMem⟩ =
      .ok (stateV2 (frameV2 0 0 0
        [.immediate none, .immediate (some (.slicePtr ptr len))])
        q.callerMem m) :=
    ctx.initStateV2_ok_frameV2 rfl (by decide) (by rw [← hQ]; exact hValid)
  rw [hQ]
  unfold execProgV2
  rw [hInit]
  -- bb0 stmt 0: _0 = useRetag(copy _1)
  apply execOutcomeStateV2_step (evalStepV2_assign_local (by rfl) (by rfl)
    (by rfl) (by rfl)
    (evalRvalueV2_useRetag_copy_ok (by rfl) (by rfl) (by rfl) hRV)
    (writePlaceDestV2_immediate_ok (by rfl) (by rfl) (by rfl)))
  -- bb0 term: return_
  exact execOutcomeStateV2_done (evalStepV2_return_ok (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) hStay hRV
    spansDisjoint_single) (by rw [hExt])

/-- `<&mut [u8] as IntoByteSlice>::into_byte_slice`: `_0 = &(*_1)`. -/
theorem body1_correct (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_1 q) :
    ∃ ptr len, q.args = [.slicePtr ptr len] ∧
      execProgV2 (entryProgForBody Captured.program 1) 8 q
        (fun o => o = .returned ⟨.slicePtr ptr len, q.callerMem⟩) := by
  let ⟨ptrAid, ptrOff, len, hArgs, hCM, hRefMut⟩ :=
    validEntryArgsV2_slice_u8_inv (reqMut := .mut) rfl hValid
  let ptr : PtrVal := ⟨ptrAid, ptrOff, .isize⟩
  let m : MemoryState := entryMemoryWithCaller q.callerMem
  refine ⟨ptr, len, hArgs, ?_⟩
  have hQ : q = ⟨[.slicePtr ptr len], q.callerMem⟩ := by
    cases q; dsimp only at hArgs; rw [hArgs]
  have hRef := refValid_shared_of_mut hRefMut
  have hRV := refsValidInMem_of_refValid hRef
  have hStay : refsStayInCallerMem q.callerMem
      (.ref .shared (.slice (.int .i8 false))) (.slicePtr ptr len) = true :=
    refsStayInCallerMem_of_refValid hRef
  have hExt : extractCallerMemory q.callerMem m = q.callerMem :=
    extractCallerMemory_entry q.callerMem hCM
  let ctx : BodyCtx := ⟨Captured.program, 1, Captured.body_1⟩
  have hInit :
      initStateV2 (entryProgForBody Captured.program 1)
        ⟨[.slicePtr ptr len], q.callerMem⟩ =
      .ok (stateV2 (frameV2 1 0 0
        [.immediate none, .immediate (some (.slicePtr ptr len))])
        q.callerMem m) :=
    ctx.initStateV2_ok_frameV2 rfl (by decide) (by rw [← hQ]; exact hValid)
  rw [hQ]
  unfold execProgV2
  rw [hInit]
  -- bb0 stmt 0: _0 = &(*_1)
  apply execOutcomeStateV2_step (evalStepV2_assign_local (by rfl) (by rfl)
    (by rfl) (by rfl)
    (evalRvalueV2_ref_deref_ok (by rfl) (by rfl) (by rfl) hRef)
    (writePlaceDestV2_immediate_ok (by rfl) (by rfl) (by rfl)))
  -- bb0 term: return_
  exact execOutcomeStateV2_done (evalStepV2_return_ok (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) hStay hRV
    spansDisjoint_single) (by rw [hExt])

/-- `<&mut [u8] as IntoByteSliceMut>::into_byte_slice_mut`:
`StorageLive 2; _2 = &mut (*_1); _0 = &mut (*_2); StorageDead 2`. -/
theorem body2_correct (q : Query)
    (hValid : ValidEntryArgsV2 Captured.body_2 q) :
    ∃ ptr len, q.args = [.slicePtr ptr len] ∧
      execProgV2 (entryProgForBody Captured.program 2) 8 q
        (fun o => o = .returned ⟨.slicePtr ptr len, q.callerMem⟩) := by
  let ⟨ptrAid, ptrOff, len, hArgs, hCM, hRef⟩ :=
    validEntryArgsV2_slice_u8_inv (reqMut := .mut) rfl hValid
  let ptr : PtrVal := ⟨ptrAid, ptrOff, .isize⟩
  let m : MemoryState := entryMemoryWithCaller q.callerMem
  refine ⟨ptr, len, hArgs, ?_⟩
  have hQ : q = ⟨[.slicePtr ptr len], q.callerMem⟩ := by
    cases q; dsimp only at hArgs; rw [hArgs]
  have hRV := refsValidInMem_of_refValid hRef
  have hStay : refsStayInCallerMem q.callerMem
      (.ref .mut (.slice (.int .i8 false))) (.slicePtr ptr len) = true :=
    refsStayInCallerMem_of_refValid hRef
  have hExt : extractCallerMemory q.callerMem m = q.callerMem :=
    extractCallerMemory_entry q.callerMem hCM
  let ctx : BodyCtx := ⟨Captured.program, 2, Captured.body_2⟩
  have hInit :
      initStateV2 (entryProgForBody Captured.program 2)
        ⟨[.slicePtr ptr len], q.callerMem⟩ =
      .ok (stateV2 (frameV2 2 0 0
        [.immediate none, .immediate (some (.slicePtr ptr len)), .dead])
        q.callerMem m) :=
    ctx.initStateV2_ok_frameV2 rfl (by decide) (by rw [← hQ]; exact hValid)
  rw [hQ]
  unfold execProgV2
  rw [hInit]
  -- bb0 stmt 0: StorageLive 2
  apply execOutcomeStateV2_step (by rfl)
  -- bb0 stmt 1: _2 = &mut (*_1)
  apply execOutcomeStateV2_step (evalStepV2_assign_local (by rfl) (by rfl)
    (by rfl) (by rfl)
    (evalRvalueV2_ref_deref_ok (by rfl) (by rfl) (by rfl) hRef)
    (writePlaceDestV2_immediate_ok (by rfl) (by rfl) (by rfl)))
  -- bb0 stmt 2: _0 = &mut (*_2)
  apply execOutcomeStateV2_step (evalStepV2_assign_local (by rfl) (by rfl)
    (by rfl) (by rfl)
    (evalRvalueV2_ref_deref_ok (by rfl) (by rfl) (by rfl) hRef)
    (writePlaceDestV2_immediate_ok (by rfl) (by rfl) (by rfl)))
  -- bb0 stmt 3: StorageDead 2
  apply execOutcomeStateV2_step (by rfl)
  -- bb0 term: return_
  exact execOutcomeStateV2_done (evalStepV2_return_ok (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) hStay hRV
    spansDisjoint_single) (by rw [hExt])

/-! ## Top-Level Claim -/

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · intro defId body hBody
    cases defId with
    | zero =>
      change some Captured.body_0 = some body at hBody
      cases hBody
      refine ⟨rfl, by decide, ?_⟩
      intro q hValid _
      let ⟨_, _, hArgs, hExec⟩ := body0_correct q hValid
      exact (stable_slice_of_exec hArgs hExec).1
    | succ d =>
      cases d with
      | zero =>
        change some Captured.body_1 = some body at hBody
        cases hBody
        refine ⟨rfl, by decide, ?_⟩
        intro q hValid _
        let ⟨_, _, hArgs, hExec⟩ := body1_correct q hValid
        exact (stable_slice_of_exec hArgs hExec).1
      | succ d =>
        cases d with
        | zero =>
          change some Captured.body_2 = some body at hBody
          cases hBody
          refine ⟨rfl, by decide, ?_⟩
          intro q hValid _
          let ⟨_, _, hArgs, hExec⟩ := body2_correct q hValid
          exact (stable_slice_of_exec hArgs hExec).1
        | succ _ =>
          change none = some body at hBody
          cases hBody
  · refine ⟨?_, ?_, ?_⟩
    · intro q hValid
      let ⟨_, _, hArgs, hExec⟩ := body0_correct q hValid
      exact (stable_slice_of_exec hArgs hExec).2
    · intro q hValid
      let ⟨_, _, hArgs, hExec⟩ := body1_correct q hValid
      exact (stable_slice_of_exec hArgs hExec).2
    · intro q hValid
      let ⟨_, _, hArgs, hExec⟩ := body2_correct q hValid
      exact (stable_slice_of_exec hArgs hExec).2

end Proof
