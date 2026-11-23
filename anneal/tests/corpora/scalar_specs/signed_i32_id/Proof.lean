-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Expected
import Anneal.MirWp.Execution

namespace Proof

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

private theorem executes_id_i32 (bits : BitVec 128)
    (hTrunc : truncateBits .i32 bits = bits) :
    Executes Captured.body_0
      (mkState 0 0 (initLocalsLoop Captured.body_0
        [.scalar ⟨.i32, true, bits⟩] 0 Captured.body_0.locals))
      (.scalar ⟨.i32, true, bits⟩) := by
  have hInit :
      initLocalsLoop Captured.body_0 [.scalar ⟨.i32, true, bits⟩] 0
        Captured.body_0.locals =
      [.immediate none,
       .immediate (some (.scalar ⟨.i32, true, bits⟩))] := rfl
  rw [hInit]
  have hCheck : checkVal (.scalar ⟨.i32, true, bits⟩)
      (.int .i32 true) = true :=
    checkVal_int_iff.mpr ⟨bits, rfl, hTrunc⟩
  have hWrite :
      writePlace
        [.immediate none,
         .immediate (some (.scalar ⟨.i32, true, bits⟩))]
        entryMemory 0 (.int .i32 true) (.scalar ⟨.i32, true, bits⟩) =
      .ok ([.immediate (some (.scalar ⟨.i32, true, bits⟩)),
            .immediate (some (.scalar ⟨.i32, true, bits⟩))],
           entryMemory) := by
    unfold writePlace
    rw [ite_bool_false (by rw [hCheck]; rfl)]
    rfl
  have hStep :
      evalStep (bodyProg Captured.body_0) 0
        (mkState 0 0
          [.immediate none,
           .immediate (some (.scalar ⟨.i32, true, bits⟩))]) =
      .step (mkState 0 1
        [.immediate (some (.scalar ⟨.i32, true, bits⟩)),
         .immediate (some (.scalar ⟨.i32, true, bits⟩))]) := by
    change
      (match writePlace
        [.immediate none,
         .immediate (some (.scalar ⟨.i32, true, bits⟩))]
        entryMemory 0 (.int .i32 true) (.scalar ⟨.i32, true, bits⟩)
       with
       | .error k => StepResult.fault k
       | .ok (ls, mem) =>
         StepResult.step
           ({ frames := [{ defId := 0, blockIdx := 0, stmtIdx := 1, locals := ls }]
              callerMem := ⟨[]⟩
              mem := mem } : State)) = _
    rw [hWrite]
    rfl
  exact .next hStep (.ret rfl)

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro id body found
    cases id with
    | zero =>
      injection found with hEq
      subst hEq
      refine bodyVerified_of_safe rfl rfl (fun args valid _ => ?_)
      unfold ValidEntryArgs at valid
      change checkArgsMatch args [.int .i32 true] = true at valid
      rw [checkArgsMatch_cons_iff] at valid
      let ⟨v, rest, hCons, hv, hNil⟩ := valid
      rw [checkArgsMatch_nil_iff] at hNil
      subst hCons; subst hNil
      rw [checkVal_int_iff] at hv
      let ⟨bits, hvEq, hTrunc⟩ := hv
      subst hvEq
      exact executes_safe (executes_id_i32 bits hTrunc)
    | succ id => cases found
  · refine ⟨Captured.body_0, rfl, fun bits hTrunc => ?_⟩
    exact behavior_of_returns rfl rfl
      (by
        unfold ValidEntryArgs
        change checkArgsMatch [.scalar ⟨.i32, true, bits⟩]
          [.int .i32 true] = true
        rw [checkArgsMatch_cons_iff]
        exact ⟨_, _, rfl, checkVal_int_iff.mpr ⟨bits, rfl, hTrunc⟩, rfl⟩)
      (executes_returns (executes_id_i32 bits hTrunc))

end Proof
