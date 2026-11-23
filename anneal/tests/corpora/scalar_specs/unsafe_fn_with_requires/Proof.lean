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

private theorem executes_nonzero (bits : BitVec 128)
    (hT : truncateBits .isize bits = bits)
    (hNe : bits ≠ BitVec.ofNat 128 0) :
    Executes .little Captured.body_0
      (mkState 0 0 (initLocalsLoop Captured.body_0
        [.scalar ⟨.isize, false, bits⟩] 0 Captured.body_0.locals))
      (.scalar ⟨.isize, false, bits⟩) := by
  let v := Val.scalar ⟨.isize, false, bits⟩
  let eqb := (decodeScalar ⟨.isize, false, bits⟩ ==
    decodeScalar ⟨.isize, false, BitVec.ofNat 128 0⟩)
  have hF : eqb = false := by
    cases hB : eqb with
    | false => rfl
    | true => exact absurd (bits_eq_zero_of_decode_beq hT hB) hNe
  have hInit :
      initLocalsLoop Captured.body_0 [v] 0 Captured.body_0.locals =
      [.immediate none, .immediate (some v), .dead, .dead, .dead] := rfl
  rw [hInit]
  have hCheck : checkVal v (.int .isize false) = true :=
    checkVal_int_iff.mpr ⟨bits, rfl, hT⟩
  have hS0 : evalStep (bodyProg Captured.body_0) 0
      (mkState 0 0 [.immediate none, .immediate (some v), .dead, .dead, .dead]) =
      .step (mkState 0 1 [.immediate none, .immediate (some v), .immediate none, .dead, .dead]) := rfl
  have hS1 : evalStep (bodyProg Captured.body_0) 0
      (mkState 0 1 [.immediate none, .immediate (some v), .immediate none, .dead, .dead]) =
      .step (mkState 0 2 [.immediate none, .immediate (some v), .immediate none, .immediate none, .dead]) := rfl
  have hW3 : writePlace .little
      [.immediate none, .immediate (some v), .immediate none, .immediate none, .dead]
      entryMemory 3 (.int .isize false) v =
      .ok ([.immediate none, .immediate (some v), .immediate none, .immediate (some v), .dead],
        entryMemory) := by
    unfold writePlace
    rw [ite_bool_false (by rw [hCheck]; rfl)]
    rfl
  have hS2 : evalStep (bodyProg Captured.body_0) 0
      (mkState 0 2 [.immediate none, .immediate (some v), .immediate none, .immediate none, .dead]) =
      .step (mkState 0 3 [.immediate none, .immediate (some v), .immediate none, .immediate (some v), .dead]) := by
    change (match writePlace .little _ entryMemory 3 (.int .isize false) v with
      | .error k => StepResult.fault k
      | .ok (ls, m) => StepResult.step ({ frames := [{ defId := 0, blockIdx := 0, stmtIdx := 3, locals := ls }], callerMem := ⟨[]⟩, mem := m } : State)) = _
    rw [hW3]; rfl
  have hBinEq : evalBinOp .eq v (.scalar ⟨.isize, false, BitVec.ofNat 128 0⟩) =
      .ok (.bool eqb) := by
    change evalBinOp .eq (.scalar ⟨.isize, false, bits⟩)
      (.scalar ⟨.isize, false, BitVec.ofNat 128 0⟩) = .ok (.bool eqb)
    rfl
  have hRval :
      evalRvalue .little
        [.int .isize false, .int .isize false, .bool, .int .isize false, .never]
        [.immediate none, .immediate (some v), .immediate none, .immediate (some v), .dead]
        entryMemory .bool
        (.binaryOp .eq (.move ⟨3, []⟩)
          (.constant ⟨.int .isize false, .scalar (BitVec.ofNat 128 0)⟩)) =
      .ok (.bool false,
        [.immediate none, .immediate (some v), .immediate none, .immediate none, .dead],
        entryMemory) := by
    unfold evalRvalue
    change
      (match evalBinOp .eq v (.scalar ⟨.isize, false, BitVec.ofNat 128 0⟩) with
       | .error k => Except.error k
       | .ok res =>
         Except.ok (res,
           ([.immediate none, .immediate (some v), .immediate none, .immediate none, .dead] : List LocalSlot),
           entryMemory)) = _
    rw [hBinEq, hF]
  have hW2 : writePlace .little
      [.immediate none, .immediate (some v), .immediate none, .immediate none, .dead]
      entryMemory 2 .bool (.bool false) =
      .ok ([.immediate none, .immediate (some v), .immediate (some (.bool false)), .immediate none, .dead],
        entryMemory) := by
    unfold writePlace
    rw [ite_bool_false (rfl : (!checkVal (.bool false) .bool) = false)]
    rfl
  have hS3 : evalStep (bodyProg Captured.body_0) 0
      (mkState 0 3 [.immediate none, .immediate (some v), .immediate none, .immediate (some v), .dead]) =
      .step (mkState 0 4 [.immediate none, .immediate (some v), .immediate (some (.bool false)), .immediate none, .dead]) := by
    unfold evalStep bodyProg evalStatement
    dsimp only [Captured.body_0, Trusted.MirSemantics.getElem?, mkState]
    rw [ite_bool_false (rfl : (!([].isEmpty)) = false)]
    rw [hRval]
    dsimp only
    rw [hW2]
  have hSw : evalStep (bodyProg Captured.body_0) 0
      (mkState 0 4 [.immediate none, .immediate (some v), .immediate (some (.bool false)), .immediate none, .dead]) =
      .step (mkState 2 0 [.immediate none, .immediate (some v), .immediate none, .immediate none, .dead]) := rfl
  have hDead3 : evalStep (bodyProg Captured.body_0) 0
      (mkState 2 0 [.immediate none, .immediate (some v), .immediate none, .immediate none, .dead]) =
      .step (mkState 2 1 [.immediate none, .immediate (some v), .immediate none, .dead, .dead]) := rfl
  have hW0 : writePlace .little
      [.immediate none, .immediate (some v), .immediate none, .dead, .dead]
      entryMemory 0 (.int .isize false) v =
      .ok ([.immediate (some v), .immediate (some v), .immediate none, .dead, .dead],
        entryMemory) := by
    unfold writePlace
    rw [ite_bool_false (by rw [hCheck]; rfl)]
    rfl
  have hAssign : evalStep (bodyProg Captured.body_0) 0
      (mkState 2 1 [.immediate none, .immediate (some v), .immediate none, .dead, .dead]) =
      .step (mkState 2 2 [.immediate (some v), .immediate (some v), .immediate none, .dead, .dead]) := by
    change (match writePlace .little _ entryMemory 0 (.int .isize false) v with
      | .error k => StepResult.fault k
      | .ok (ls, m) => StepResult.step ({ frames := [{ defId := 0, blockIdx := 2, stmtIdx := 2, locals := ls }], callerMem := ⟨[]⟩, mem := m } : State)) = _
    rw [hW0]; rfl
  have hDead2 : evalStep (bodyProg Captured.body_0) 0
      (mkState 2 2 [.immediate (some v), .immediate (some v), .immediate none, .dead, .dead]) =
      .step (mkState 2 3 [.immediate (some v), .immediate (some v), .dead, .dead, .dead]) := rfl
  exact .next hS0 (.next hS1 (.next hS2 (.next hS3 (.next hSw (.next hDead3 (.next hAssign (.next hDead2 (.ret rfl))))))))

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro id body found
    cases id with
    | zero =>
      injection found with hEq
      subst hEq
      refine bodyVerified_of_safe rfl rfl (fun args valid hUnsafe => ?_)
      unfold ValidEntryArgs at valid
      change checkArgsMatch args [.int .isize false] = true at valid
      rw [checkArgsMatch_cons_iff] at valid
      let ⟨v, rest, hCons, hv, hNil⟩ := valid
      rw [checkArgsMatch_nil_iff] at hNil
      subst hCons; subst hNil
      rw [checkVal_int_iff] at hv
      let ⟨bits, hvEq, hTrunc⟩ := hv
      subst hvEq
      have hNe : bits ≠ BitVec.ofNat 128 0 := hUnsafe rfl
      exact executes_safe (executes_nonzero bits hTrunc hNe)
    | succ id => cases found
  · refine ⟨Captured.body_0, rfl, fun bits hTrunc hNe => ?_⟩
    exact behavior_of_returns rfl rfl
      (by
        unfold ValidEntryArgs
        change checkArgsMatch [.scalar ⟨.isize, false, bits⟩]
          [.int .isize false] = true
        rw [checkArgsMatch_cons_iff]
        exact ⟨_, _, rfl, checkVal_int_iff.mpr ⟨bits, rfl, hTrunc⟩, rfl⟩)
      (executes_returns (executes_nonzero bits hTrunc hNe))

end Proof
