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

private theorem write_i32 (ls : List LocalSlot) (idx : LocalId) (b : BitVec 128)
    (hT : truncateBits .i32 b = b) (old : Option Val)
    (ls' : List LocalSlot)
    (hOld : Trusted.MirSemantics.getElem? ls idx = some (.immediate old))
    (hSet : setElem? ls idx (.immediate (some (.scalar ⟨.i32, false, b⟩))) = some ls') :
    writePlace .little ls entryMemory idx (.int .i32 false) (.scalar ⟨.i32, false, b⟩) =
      .ok (ls', entryMemory) := by
  have hCheck : checkVal (.scalar ⟨.i32, false, b⟩) (.int .i32 false) = true :=
    checkVal_int_iff.mpr ⟨b, rfl, hT⟩
  unfold writePlace
  rw [ite_bool_false (by rw [hCheck]; rfl), hOld, hSet]

private theorem executes_add (b₁ b₂ : BitVec 128)
    (hT₁ : truncateBits .i32 b₁ = b₁) (hT₂ : truncateBits .i32 b₂ = b₂) :
    Executes .little Captured.body_0
      (mkState 0 0 (initLocalsLoop Captured.body_0
        [.scalar ⟨.i32, false, b₁⟩, .scalar ⟨.i32, false, b₂⟩] 0
        Captured.body_0.locals))
      (.scalar ⟨.i32, false,
        truncateBits .i32
          (bvOfInt 128
            (decodeScalar ⟨.i32, false, b₁⟩ +
             decodeScalar ⟨.i32, false, b₂⟩))⟩) := by
  let v₁ : Val := .scalar ⟨.i32, false, b₁⟩
  let v₂ : Val := .scalar ⟨.i32, false, b₂⟩
  let bSum : BitVec 128 :=
    truncateBits .i32 (bvOfInt 128 (decodeScalar ⟨.i32, false, b₁⟩ + decodeScalar ⟨.i32, false, b₂⟩))
  let vSum : Val := .scalar ⟨.i32, false, bSum⟩
  have hTSum : truncateBits .i32 bSum = bSum := truncateBits_idem .i32 _
  have hInit :
      initLocalsLoop Captured.body_0 [v₁, v₂] 0 Captured.body_0.locals =
      [.immediate none, .immediate (some v₁), .immediate (some v₂), .dead, .dead] := rfl
  rw [hInit]
  have hStep0 :
      evalStep (bodyProg Captured.body_0) 0
        (mkState 0 0 [.immediate none, .immediate (some v₁), .immediate (some v₂), .dead, .dead]) =
      .step (mkState 0 1 [.immediate none, .immediate (some v₁), .immediate (some v₂), .immediate none, .dead]) := rfl
  have hStep1 :
      evalStep (bodyProg Captured.body_0) 0
        (mkState 0 1 [.immediate none, .immediate (some v₁), .immediate (some v₂), .immediate none, .dead]) =
      .step (mkState 0 2 [.immediate none, .immediate (some v₁), .immediate (some v₂), .immediate (some v₁), .dead]) := by
    have hW := write_i32 [.immediate none, .immediate (some v₁), .immediate (some v₂), .immediate none, .dead]
      3 b₁ hT₁ none [.immediate none, .immediate (some v₁), .immediate (some v₂), .immediate (some v₁), .dead] rfl rfl
    change (match writePlace .little _ entryMemory 3 (.int .i32 false) v₁ with
      | .error k => StepResult.fault k
      | .ok (ls, m) => StepResult.step ({ frames := [{ defId := 0, blockIdx := 0, stmtIdx := 2, locals := ls }], callerMem := ⟨[]⟩, mem := m } : State)) = _
    rw [hW]; rfl
  have hStep2 :
      evalStep (bodyProg Captured.body_0) 0
        (mkState 0 2 [.immediate none, .immediate (some v₁), .immediate (some v₂), .immediate (some v₁), .dead]) =
      .step (mkState 0 3 [.immediate none, .immediate (some v₁), .immediate (some v₂), .immediate (some v₁), .immediate none]) := rfl
  have hStep3 :
      evalStep (bodyProg Captured.body_0) 0
        (mkState 0 3 [.immediate none, .immediate (some v₁), .immediate (some v₂), .immediate (some v₁), .immediate none]) =
      .step (mkState 0 4 [.immediate none, .immediate (some v₁), .immediate (some v₂), .immediate (some v₁), .immediate (some v₂)]) := by
    have hW := write_i32 [.immediate none, .immediate (some v₁), .immediate (some v₂), .immediate (some v₁), .immediate none]
      4 b₂ hT₂ none [.immediate none, .immediate (some v₁), .immediate (some v₂), .immediate (some v₁), .immediate (some v₂)] rfl rfl
    change (match writePlace .little _ entryMemory 4 (.int .i32 false) v₂ with
      | .error k => StepResult.fault k
      | .ok (ls, m) => StepResult.step ({ frames := [{ defId := 0, blockIdx := 0, stmtIdx := 4, locals := ls }], callerMem := ⟨[]⟩, mem := m } : State)) = _
    rw [hW]; rfl
  have hBin := evalBinOp_unsigned_add .i32 b₁ b₂
  have hRval :
      evalRvalue .little
        [.int .i32 false, .int .i32 false, .int .i32 false,
         .int .i32 false, .int .i32 false]
        [.immediate none, .immediate (some v₁), .immediate (some v₂),
         .immediate (some v₁), .immediate (some v₂)]
        entryMemory (.int .i32 false)
        (.binaryOp .add (.move ⟨3, []⟩) (.move ⟨4, []⟩)) =
      .ok (vSum,
        [.immediate none, .immediate (some v₁), .immediate (some v₂),
         .immediate none, .immediate none],
        entryMemory) := by
    unfold evalRvalue
    change
      (match evalBinOp .add v₁ v₂ with
       | .error k => Except.error k
       | .ok res =>
         Except.ok (res,
           ([.immediate none, .immediate (some v₁), .immediate (some v₂),
             .immediate none, .immediate none] : List LocalSlot),
           entryMemory)) = _
    rw [hBin]
  have hStep4 :
      evalStep (bodyProg Captured.body_0) 0
        (mkState 0 4 [.immediate none, .immediate (some v₁), .immediate (some v₂), .immediate (some v₁), .immediate (some v₂)]) =
      .step (mkState 0 5 [.immediate (some vSum), .immediate (some v₁), .immediate (some v₂), .immediate none, .immediate none]) := by
    have hW := write_i32 [.immediate none, .immediate (some v₁), .immediate (some v₂), .immediate none, .immediate none]
      0 bSum hTSum none [.immediate (some vSum), .immediate (some v₁), .immediate (some v₂), .immediate none, .immediate none] rfl rfl
    unfold evalStep bodyProg evalStatement
    dsimp only [Captured.body_0, Trusted.MirSemantics.getElem?, mkState]
    rw [ite_bool_false (rfl : (!([].isEmpty)) = false)]
    rw [hRval]
    dsimp only
    rw [hW]
  have hStep5 :
      evalStep (bodyProg Captured.body_0) 0
        (mkState 0 5 [.immediate (some vSum), .immediate (some v₁), .immediate (some v₂), .immediate none, .immediate none]) =
      .step (mkState 0 6 [.immediate (some vSum), .immediate (some v₁), .immediate (some v₂), .immediate none, .dead]) := rfl
  have hStep6 :
      evalStep (bodyProg Captured.body_0) 0
        (mkState 0 6 [.immediate (some vSum), .immediate (some v₁), .immediate (some v₂), .immediate none, .dead]) =
      .step (mkState 0 7 [.immediate (some vSum), .immediate (some v₁), .immediate (some v₂), .dead, .dead]) := rfl
  exact .next hStep0 (.next hStep1 (.next hStep2 (.next hStep3 (.next hStep4 (.next hStep5 (.next hStep6 (.ret rfl)))))))

theorem verify : Expected.claim := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro id body found
    cases id with
    | zero =>
      injection found with hEq
      subst hEq
      refine bodyVerified_of_safe rfl rfl (fun args valid _ => ?_)
      unfold ValidEntryArgs at valid
      change checkArgsMatch args [.int .i32 false, .int .i32 false] = true at valid
      rw [checkArgsMatch_cons_iff] at valid
      let ⟨v₁, rest₁, hCons₁, hv₁, hRest₁⟩ := valid
      rw [checkArgsMatch_cons_iff] at hRest₁
      let ⟨v₂, rest₂, hCons₂, hv₂, hNil⟩ := hRest₁
      rw [checkArgsMatch_nil_iff] at hNil
      subst hCons₁; subst hCons₂; subst hNil
      rw [checkVal_int_iff] at hv₁ hv₂
      let ⟨b₁, hEq₁, hT₁⟩ := hv₁
      let ⟨b₂, hEq₂, hT₂⟩ := hv₂
      subst hEq₁; subst hEq₂
      exact executes_safe (executes_add b₁ b₂ hT₁ hT₂)
    | succ id => cases found
  · refine ⟨Captured.body_0, rfl, fun b₁ b₂ hT₁ hT₂ => ?_⟩
    exact behavior_of_returns rfl rfl
      (by
        unfold ValidEntryArgs
        change checkArgsMatch [.scalar ⟨.i32, false, b₁⟩, .scalar ⟨.i32, false, b₂⟩]
          [.int .i32 false, .int .i32 false] = true
        rw [checkArgsMatch_cons_iff]
        refine ⟨_, _, rfl, checkVal_int_iff.mpr ⟨b₁, rfl, hT₁⟩, ?_⟩
        rw [checkArgsMatch_cons_iff]
        exact ⟨_, _, rfl, checkVal_int_iff.mpr ⟨b₂, rfl, hT₂⟩, rfl⟩)
      (executes_returns (executes_add b₁ b₂ hT₁ hT₂))

end Proof
