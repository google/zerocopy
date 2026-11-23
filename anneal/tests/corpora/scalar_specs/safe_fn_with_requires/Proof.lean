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

private theorem bits_eq_zero_of_decode_beq {bits : BitVec 128}
    (hT : truncateBits .isize bits = bits)
    (hB : (decodeScalar ⟨.isize, false, bits⟩ ==
      decodeScalar ⟨.isize, false, BitVec.ofNat 128 0⟩) = true) :
    bits = BitVec.ofNat 128 0 := by
  have hInt : decodeScalar ⟨.isize, false, bits⟩ = 0 := eq_of_beq hB
  unfold decodeScalar at hInt
  rw [hT] at hInt
  exact bitVec_eq_of_toNat_eq (Int.ofNat.inj hInt)

private theorem step_to_switch (bits : BitVec 128)
    (hT : truncateBits .isize bits = bits) :
    Reach Captured.body_0
      (mkState 0 0 (initLocalsLoop Captured.body_0
        [.scalar ⟨.isize, false, bits⟩] 0 Captured.body_0.locals))
      (mkState 0 4 [.immediate none, .immediate (some (.scalar ⟨.isize, false, bits⟩)),
        .immediate (some (.bool (decodeScalar ⟨.isize, false, bits⟩ ==
          decodeScalar ⟨.isize, false, BitVec.ofNat 128 0⟩))),
        .immediate none]) := by
  let v := Val.scalar ⟨.isize, false, bits⟩
  let eqb := (decodeScalar ⟨.isize, false, bits⟩ ==
    decodeScalar ⟨.isize, false, BitVec.ofNat 128 0⟩)
  have hInit :
      initLocalsLoop Captured.body_0 [v] 0 Captured.body_0.locals =
      [.immediate none, .immediate (some v), .dead, .dead] := rfl
  rw [hInit]
  have hCheck : checkVal v (.int .isize false) = true :=
    checkVal_int_iff.mpr ⟨bits, rfl, hT⟩
  have hS0 : evalStep (bodyProg Captured.body_0) 0
      (mkState 0 0 [.immediate none, .immediate (some v), .dead, .dead]) =
      .step (mkState 0 1 [.immediate none, .immediate (some v), .immediate none, .dead]) := rfl
  have hS1 : evalStep (bodyProg Captured.body_0) 0
      (mkState 0 1 [.immediate none, .immediate (some v), .immediate none, .dead]) =
      .step (mkState 0 2 [.immediate none, .immediate (some v), .immediate none, .immediate none]) := rfl
  have hW3 : writePlace
      [.immediate none, .immediate (some v), .immediate none, .immediate none]
      entryMemory 3 (.int .isize false) v =
      .ok ([.immediate none, .immediate (some v), .immediate none, .immediate (some v)],
        entryMemory) := by
    unfold writePlace
    rw [ite_bool_false (by rw [hCheck]; rfl)]
    rfl
  have hS2 : evalStep (bodyProg Captured.body_0) 0
      (mkState 0 2 [.immediate none, .immediate (some v), .immediate none, .immediate none]) =
      .step (mkState 0 3 [.immediate none, .immediate (some v), .immediate none, .immediate (some v)]) := by
    change (match writePlace _ entryMemory 3 (.int .isize false) v with
      | .error k => StepResult.fault k
      | .ok (ls, m) => StepResult.step ({ frames := [{ defId := 0, blockIdx := 0, stmtIdx := 3, locals := ls }], callerMem := ⟨[]⟩, mem := m } : State)) = _
    rw [hW3]; rfl
  have hBinEq : evalBinOp .eq v (.scalar ⟨.isize, false, BitVec.ofNat 128 0⟩) =
      .ok (.bool eqb) := by
    change evalBinOp .eq (.scalar ⟨.isize, false, bits⟩)
      (.scalar ⟨.isize, false, BitVec.ofNat 128 0⟩) = .ok (.bool eqb)
    rfl
  have hRval :
      evalRvalue
        [.int .isize false, .int .isize false, .bool, .int .isize false]
        [.immediate none, .immediate (some v), .immediate none, .immediate (some v)]
        entryMemory .bool
        (.binaryOp .eq (.move ⟨3, []⟩)
          (.constant ⟨.int .isize false, .scalar (BitVec.ofNat 128 0)⟩)) =
      .ok (.bool eqb,
        [.immediate none, .immediate (some v), .immediate none, .immediate none],
        entryMemory) := by
    unfold evalRvalue
    change
      (match evalBinOp .eq v (.scalar ⟨.isize, false, BitVec.ofNat 128 0⟩) with
       | .error k => Except.error k
       | .ok res =>
         Except.ok (res,
           ([.immediate none, .immediate (some v), .immediate none, .immediate none] : List LocalSlot),
           entryMemory)) = _
    rw [hBinEq]
  have hW2 : writePlace
      [.immediate none, .immediate (some v), .immediate none, .immediate none]
      entryMemory 2 .bool (.bool eqb) =
      .ok ([.immediate none, .immediate (some v), .immediate (some (.bool eqb)), .immediate none],
        entryMemory) := by
    unfold writePlace
    rw [ite_bool_false (rfl : (!checkVal (.bool eqb) .bool) = false)]
    rfl
  have hS3 : evalStep (bodyProg Captured.body_0) 0
      (mkState 0 3 [.immediate none, .immediate (some v), .immediate none, .immediate (some v)]) =
      .step (mkState 0 4 [.immediate none, .immediate (some v), .immediate (some (.bool eqb)), .immediate none]) := by
    unfold evalStep bodyProg evalStatement
    dsimp only [Captured.body_0, Trusted.MirSemantics.getElem?, mkState]
    rw [ite_bool_false (rfl : (!([].isEmpty)) = false)]
    rw [hRval]
    dsimp only
    rw [hW2]
  exact .next (.next (.next (.next .refl hS0) hS1) hS2) hS3

private theorem executes_clamp (bits : BitVec 128)
    (hT : truncateBits .isize bits = bits) :
    Executes Captured.body_0
      (mkState 0 0 (initLocalsLoop Captured.body_0
        [.scalar ⟨.isize, false, bits⟩] 0 Captured.body_0.locals))
      (if (decodeScalar ⟨.isize, false, bits⟩ ==
          decodeScalar ⟨.isize, false, BitVec.ofNat 128 0⟩) then
        .scalar ⟨.isize, false, BitVec.ofNat 128 1⟩
      else
        .scalar ⟨.isize, false, bits⟩) := by
  let v := Val.scalar ⟨.isize, false, bits⟩
  have hPre := step_to_switch bits hT
  have hCheck : checkVal v (.int .isize false) = true :=
    checkVal_int_iff.mpr ⟨bits, rfl, hT⟩
  apply executes_prepend hPre
  cases hB : (decodeScalar ⟨.isize, false, bits⟩ ==
      decodeScalar ⟨.isize, false, BitVec.ofNat 128 0⟩) with
  | true =>
    exact .next rfl (.next rfl (.next rfl (.next rfl (.next rfl (.ret rfl)))))
  | false =>
    have hSw : evalStep (bodyProg Captured.body_0) 0
        (mkState 0 4 [.immediate none, .immediate (some v),
          .immediate (some (.bool false)), .immediate none]) =
        .step (mkState 2 0 [.immediate none, .immediate (some v),
          .immediate none, .immediate none]) := rfl
    have hDead3 : evalStep (bodyProg Captured.body_0) 0
        (mkState 2 0 [.immediate none, .immediate (some v),
          .immediate none, .immediate none]) =
        .step (mkState 2 1 [.immediate none, .immediate (some v),
          .immediate none, .dead]) := rfl
    have hW0 : writePlace
        [.immediate none, .immediate (some v), .immediate none, .dead]
        entryMemory 0 (.int .isize false) v =
        .ok ([.immediate (some v), .immediate (some v), .immediate none, .dead],
          entryMemory) := by
      unfold writePlace
      rw [ite_bool_false (by rw [hCheck]; rfl)]
      rfl
    have hAssign : evalStep (bodyProg Captured.body_0) 0
        (mkState 2 1 [.immediate none, .immediate (some v),
          .immediate none, .dead]) =
        .step (mkState 2 2 [.immediate (some v), .immediate (some v),
          .immediate none, .dead]) := by
      change (match writePlace _ entryMemory 0 (.int .isize false) v with
        | .error k => StepResult.fault k
        | .ok (ls, m) => StepResult.step ({ frames := [{ defId := 0, blockIdx := 2, stmtIdx := 2, locals := ls }], callerMem := ⟨[]⟩, mem := m } : State)) = _
      rw [hW0]; rfl
    have hGoto : evalStep (bodyProg Captured.body_0) 0
        (mkState 2 2 [.immediate (some v), .immediate (some v),
          .immediate none, .dead]) =
        .step (mkState 3 0 [.immediate (some v), .immediate (some v),
          .immediate none, .dead]) := rfl
    have hDead2 : evalStep (bodyProg Captured.body_0) 0
        (mkState 3 0 [.immediate (some v), .immediate (some v),
          .immediate none, .dead]) =
        .step (mkState 3 1 [.immediate (some v), .immediate (some v),
          .dead, .dead]) := rfl
    exact .next hSw (.next hDead3 (.next hAssign (.next hGoto (.next hDead2 (.ret rfl)))))

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro id body found
    cases id with
    | zero =>
      injection found with hEq
      subst hEq
      refine bodyVerified_of_safe rfl rfl (fun args valid _ => ?_)
      unfold ValidEntryArgs at valid
      change checkArgsMatch args [.int .isize false] = true at valid
      rw [checkArgsMatch_cons_iff] at valid
      let ⟨v, rest, hCons, hv, hNil⟩ := valid
      rw [checkArgsMatch_nil_iff] at hNil
      subst hCons; subst hNil
      rw [checkVal_int_iff] at hv
      let ⟨bits, hvEq, hTrunc⟩ := hv
      subst hvEq
      exact executes_safe (executes_clamp bits hTrunc)
    | succ id => cases found
  · refine ⟨Captured.body_0, rfl, fun bits hTrunc hNe => ?_⟩
    have hF : (decodeScalar ⟨.isize, false, bits⟩ ==
        decodeScalar ⟨.isize, false, BitVec.ofNat 128 0⟩) = false := by
      cases hB : (decodeScalar ⟨.isize, false, bits⟩ ==
          decodeScalar ⟨.isize, false, BitVec.ofNat 128 0⟩) with
      | false => rfl
      | true => exact absurd (bits_eq_zero_of_decode_beq hTrunc hB) hNe
    have hEx := executes_clamp bits hTrunc
    rw [hF] at hEx
    exact behavior_of_returns rfl rfl
      (by
        unfold ValidEntryArgs
        change checkArgsMatch [.scalar ⟨.isize, false, bits⟩]
          [.int .isize false] = true
        rw [checkArgsMatch_cons_iff]
        exact ⟨_, _, rfl, checkVal_int_iff.mpr ⟨bits, rfl, hTrunc⟩, rfl⟩)
      (executes_returns hEx)

end Proof
