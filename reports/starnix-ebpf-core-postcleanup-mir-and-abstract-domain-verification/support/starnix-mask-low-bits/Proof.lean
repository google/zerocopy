-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Expected
import Anneal.Mvp.Execution

namespace Proof

open Trusted.Mvp Anneal.Mvp Spec

abbrev maskBody : Body := Captured.program.bodies[0]'(by decide)

theorem wellFormed : bodyWF maskBody = true := by decide

theorem validValue_bool (b : Bool) : validValue .bool (boolWord b) = true := by
  cases b <;> rfl

theorem evalBinary_eq_u32 (a b : Word) :
    evalBinary .eq (.int 32 false) a (.int 32 false) b = .ok (.bool, boolWord (a == b)) := by
  change (if validValue Ty.bool (boolWord (a == b)) = true then
      Except.ok (Ty.bool, boolWord (a == b)) else Except.error Fault.invalidValue) = _
  rw [validValue_bool]
  rfl

theorem evalBinary_ge_u32 (a b : Word) :
    evalBinary .ge (.int 32 false) a (.int 32 false) b =
      .ok (.bool, boolWord (decide (b.toNat ≤ a.toNat))) := by
  change (if validValue Ty.bool (boolWord (decide (b.toNat ≤ a.toNat))) = true then
      Except.ok (Ty.bool, boolWord (decide (b.toNat ≤ a.toNat))) else Except.error Fault.invalidValue) = _
  rw [validValue_bool]
  rfl

theorem evalBinary_shl_u64_u32 (a b : Word) :
    evalBinary .shl (.int 64 false) a (.int 32 false) b =
      .ok (.int 64 false, a <<< (b.toNat % 64)) := rfl

theorem localTy_2 : maskBody.localTys[2]? = some (.int 32 false) := rfl
theorem localTy_3 : maskBody.localTys[3]? = some .bool := rfl
theorem localTy_4 : maskBody.localTys[4]? = some (.int 32 false) := rfl
theorem localTy_5 : maskBody.localTys[5]? = some .bool := rfl
theorem localTy_6 : maskBody.localTys[6]? = some (.int 32 false) := rfl
theorem localTy_9 : maskBody.localTys[9]? = some (.int 64 false) := rfl
theorem localTy_10 : maskBody.localTys[10]? = some (.int 64 false) := rfl
theorem localTy_11 : maskBody.localTys[11]? = some (.int 32 false) := rfl
theorem rawValid_u32_0 : rawValid (.int 32 false) 0 = true := rfl
theorem rawValid_u32_64 : rawValid (.int 32 false) 64 = true := rfl
theorem validValue_u64 (a : Word) : validValue (.int 64 false) a = true := rfl

def s_bb0_0 (v b : Word) : State :=
  ⟨0, 0, [.uninit, .value v, .value b, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead]⟩
def s_bb0_1 (v b : Word) : State :=
  ⟨0, 1, [.uninit, .value v, .value b, .uninit, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead]⟩
def s_bb0_2 (v b : Word) : State :=
  ⟨0, 2, [.uninit, .value v, .value b, .uninit, .uninit, .dead, .dead, .dead, .dead, .dead, .dead, .dead]⟩
def s_bb0_3 (v b : Word) : State :=
  ⟨0, 3, [.uninit, .value v, .value b, .uninit, .value b, .dead, .dead, .dead, .dead, .dead, .dead, .dead]⟩
def s_bb0_4 (v b : Word) (eq0 : Word) : State :=
  ⟨0, 4, [.uninit, .value v, .value b, .value eq0, .uninit, .dead, .dead, .dead, .dead, .dead, .dead, .dead]⟩

def s_bb1_0 (v b : Word) : State :=
  ⟨1, 0, [.uninit, .value v, .value b, .uninit, .uninit, .dead, .dead, .dead, .dead, .dead, .dead, .dead]⟩

def s_bb2_0 (v b : Word) : State :=
  ⟨2, 0, [.uninit, .value v, .value b, .uninit, .uninit, .dead, .dead, .dead, .dead, .dead, .dead, .dead]⟩
def s_bb2_1 (v b : Word) : State :=
  ⟨2, 1, [.uninit, .value v, .value b, .uninit, .dead, .dead, .dead, .dead, .dead, .dead, .dead, .dead]⟩
def s_bb2_2 (v b : Word) : State :=
  ⟨2, 2, [.uninit, .value v, .value b, .uninit, .dead, .uninit, .dead, .dead, .dead, .dead, .dead, .dead]⟩
def s_bb2_3 (v b : Word) : State :=
  ⟨2, 3, [.uninit, .value v, .value b, .uninit, .dead, .uninit, .uninit, .dead, .dead, .dead, .dead, .dead]⟩
def s_bb2_4 (v b : Word) : State :=
  ⟨2, 4, [.uninit, .value v, .value b, .uninit, .dead, .uninit, .value b, .dead, .dead, .dead, .dead, .dead]⟩
def s_bb2_5 (v b : Word) (ge64 : Word) : State :=
  ⟨2, 5, [.uninit, .value v, .value b, .uninit, .dead, .value ge64, .uninit, .dead, .dead, .dead, .dead, .dead]⟩

def s_bb3_0 (v b : Word) : State :=
  ⟨3, 0, [.uninit, .value v, .value b, .uninit, .dead, .uninit, .uninit, .dead, .dead, .dead, .dead, .dead]⟩

def s_bb4_0 (v b : Word) : State :=
  ⟨4, 0, [.uninit, .value v, .value b, .uninit, .dead, .uninit, .uninit, .dead, .dead, .dead, .dead, .dead]⟩
def s_bb4_1 (v b : Word) : State :=
  ⟨4, 1, [.uninit, .value v, .value b, .uninit, .dead, .uninit, .dead, .dead, .dead, .dead, .dead, .dead]⟩
def s_bb4_2 (v b : Word) : State :=
  ⟨4, 2, [.uninit, .value v, .value b, .uninit, .dead, .uninit, .dead, .uninit, .dead, .dead, .dead, .dead]⟩
def s_bb4_3 (v b : Word) : State :=
  ⟨4, 3, [.uninit, .value v, .value b, .uninit, .dead, .uninit, .dead, .value v, .dead, .dead, .dead, .dead]⟩
def s_bb4_4 (v b : Word) : State :=
  ⟨4, 4, [.uninit, .value v, .value b, .uninit, .dead, .uninit, .dead, .value v, .uninit, .dead, .dead, .dead]⟩
def s_bb4_5 (v b : Word) : State :=
  ⟨4, 5, [.uninit, .value v, .value b, .uninit, .dead, .uninit, .dead, .value v, .uninit, .uninit, .dead, .dead]⟩
def s_bb4_6 (v b : Word) : State :=
  ⟨4, 6, [.uninit, .value v, .value b, .uninit, .dead, .uninit, .dead, .value v, .uninit, .uninit, .uninit, .dead]⟩
def s_bb4_7 (v b : Word) : State :=
  ⟨4, 7, [.uninit, .value v, .value b, .uninit, .dead, .uninit, .dead, .value v, .uninit, .uninit, .value 1, .dead]⟩
def s_bb4_8 (v b : Word) : State :=
  ⟨4, 8, [.uninit, .value v, .value b, .uninit, .dead, .uninit, .dead, .value v, .uninit, .uninit, .value 1, .uninit]⟩
def s_bb4_9 (v b : Word) : State :=
  ⟨4, 9, [.uninit, .value v, .value b, .uninit, .dead, .uninit, .dead, .value v, .uninit, .uninit, .value 1, .value b]⟩
def s_bb4_10 (v b : Word) (sh : Word) : State :=
  ⟨4, 10, [.uninit, .value v, .value b, .uninit, .dead, .uninit, .dead, .value v, .uninit, .value sh, .uninit, .uninit]⟩

theorem step_bb0_2 (v b : Word) (hb : validValue (.int 32 false) b = true) :
    step maskBody (s_bb0_2 v b) = .next (s_bb0_3 v b) := by
  change (match execStatement maskBody (s_bb0_2 v b).locals
      (.assign 4 (.use (.copy 2) true)) with
    | .ok locals => StepResult.next ⟨0, 3, locals⟩
    | .error reason => StepResult.fault reason) = .next (s_bb0_3 v b)
  simp only [execStatement, evalRvalue, evalOperand, readLocal, writeLocal, s_bb0_2,
    List.getElem?_cons_zero, List.getElem?_cons_succ, localTy_2, localTy_4, hb, ite_true]
  rfl

theorem step_bb0_3 (v b : Word) (hb : validValue (.int 32 false) b = true) :
    step maskBody (s_bb0_3 v b) = .next (s_bb0_4 v b (boolWord (b == 0))) := by
  change (match execStatement maskBody (s_bb0_3 v b).locals
      (.assign 3 (.binary .eq (.move 4) (.constant (.int 32 false) 0))) with
    | .ok locals => StepResult.next ⟨0, 4, locals⟩
    | .error reason => StepResult.fault reason) = .next (s_bb0_4 v b (boolWord (b == 0)))
  simp only [execStatement, evalRvalue, evalOperand, readLocal, writeLocal, s_bb0_3,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.set_cons_zero, List.set_cons_succ,
    localTy_3, localTy_4, rawValid_u32_0, hb, ite_true, evalBinary_eq_u32, validValue_bool]
  rfl

theorem step_bb2_3 (v b : Word) (hb : validValue (.int 32 false) b = true) :
    step maskBody (s_bb2_3 v b) = .next (s_bb2_4 v b) := by
  change (match execStatement maskBody (s_bb2_3 v b).locals
      (.assign 6 (.use (.copy 2) true)) with
    | .ok locals => StepResult.next ⟨2, 4, locals⟩
    | .error reason => StepResult.fault reason) = .next (s_bb2_4 v b)
  simp only [execStatement, evalRvalue, evalOperand, readLocal, writeLocal, s_bb2_3,
    List.getElem?_cons_zero, List.getElem?_cons_succ, localTy_2, localTy_6, hb, ite_true]
  rfl

theorem step_bb2_4 (v b : Word) (hb : validValue (.int 32 false) b = true) :
    step maskBody (s_bb2_4 v b) = .next (s_bb2_5 v b (boolWord (decide (64 ≤ b.toNat)))) := by
  change (match execStatement maskBody (s_bb2_4 v b).locals
      (.assign 5 (.binary .ge (.move 6) (.constant (.int 32 false) 64))) with
    | .ok locals => StepResult.next ⟨2, 5, locals⟩
    | .error reason => StepResult.fault reason) =
      .next (s_bb2_5 v b (boolWord (decide (64 ≤ b.toNat))))
  simp only [execStatement, evalRvalue, evalOperand, readLocal, writeLocal, s_bb2_4,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.set_cons_zero, List.set_cons_succ,
    localTy_5, localTy_6, rawValid_u32_64, hb, ite_true, evalBinary_ge_u32, validValue_bool]
  rfl

theorem step_bb4_8 (v b : Word) (hb : validValue (.int 32 false) b = true) :
    step maskBody (s_bb4_8 v b) = .next (s_bb4_9 v b) := by
  change (match execStatement maskBody (s_bb4_8 v b).locals
      (.assign 11 (.use (.copy 2) true)) with
    | .ok locals => StepResult.next ⟨4, 9, locals⟩
    | .error reason => StepResult.fault reason) = .next (s_bb4_9 v b)
  simp only [execStatement, evalRvalue, evalOperand, readLocal, writeLocal, s_bb4_8,
    List.getElem?_cons_zero, List.getElem?_cons_succ, localTy_2, localTy_11, hb, ite_true]
  rfl

theorem step_bb4_9 (v b : Word) (hb : validValue (.int 32 false) b = true) :
    step maskBody (s_bb4_9 v b) = .next (s_bb4_10 v b ((1 : Word) <<< (b.toNat % 64))) := by
  change (match execStatement maskBody (s_bb4_9 v b).locals
      (.assign 9 (.binary .shl (.move 10) (.move 11))) with
    | .ok locals => StepResult.next ⟨4, 10, locals⟩
    | .error reason => StepResult.fault reason) =
      .next (s_bb4_10 v b ((1 : Word) <<< (b.toNat % 64)))
  simp only [execStatement, evalRvalue, evalOperand, readLocal, writeLocal, s_bb4_9,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.set_cons_zero, List.set_cons_succ,
    localTy_9, localTy_10, localTy_11, hb, ite_true, evalBinary_shl_u64_u32, validValue_u64]
  rfl

theorem exec_bb1 (v b : Word) : Executes maskBody (s_bb1_0 v b) 0 :=
  run_executes (fuel := 5) rfl

theorem exec_bb3 (v b : Word) : Executes maskBody (s_bb3_0 v b) v :=
  run_executes (fuel := 7) rfl

theorem exec_bb4_tail (v b sh : Word) :
    Executes maskBody (s_bb4_10 v b sh) (v &&& (sh - 1)) :=
  run_executes (fuel := 12) rfl

theorem exec_bb4 (v b : Word) (hb : validValue (.int 32 false) b = true)
    (hlt : b.toNat < 64) :
    Executes maskBody (s_bb4_0 v b) (v &&& (((1 : Word) <<< b.toNat) - 1)) := by
  have hmod : b.toNat % 64 = b.toNat := Nat.mod_eq_of_lt hlt
  refine .next (by rfl : step maskBody (s_bb4_0 v b) = .next (s_bb4_1 v b)) ?_
  refine .next (by rfl : step maskBody (s_bb4_1 v b) = .next (s_bb4_2 v b)) ?_
  refine .next (by rfl : step maskBody (s_bb4_2 v b) = .next (s_bb4_3 v b)) ?_
  refine .next (by rfl : step maskBody (s_bb4_3 v b) = .next (s_bb4_4 v b)) ?_
  refine .next (by rfl : step maskBody (s_bb4_4 v b) = .next (s_bb4_5 v b)) ?_
  refine .next (by rfl : step maskBody (s_bb4_5 v b) = .next (s_bb4_6 v b)) ?_
  refine .next (by rfl : step maskBody (s_bb4_6 v b) = .next (s_bb4_7 v b)) ?_
  refine .next (by rfl : step maskBody (s_bb4_7 v b) = .next (s_bb4_8 v b)) ?_
  refine .next (step_bb4_8 v b hb) ?_
  have hstep9 := step_bb4_9 v b hb
  rw [hmod] at hstep9
  exact .next hstep9 (exec_bb4_tail v b ((1 : Word) <<< b.toNat))

theorem exec_bb2 (v b : Word) (hb : validValue (.int 32 false) b = true) :
    Executes maskBody (s_bb2_0 v b)
      (if decide (64 ≤ b.toNat) then v
       else v &&& (((1 : Word) <<< b.toNat) - 1)) := by
  refine .next (by rfl : step maskBody (s_bb2_0 v b) = .next (s_bb2_1 v b)) ?_
  refine .next (by rfl : step maskBody (s_bb2_1 v b) = .next (s_bb2_2 v b)) ?_
  refine .next (by rfl : step maskBody (s_bb2_2 v b) = .next (s_bb2_3 v b)) ?_
  refine .next (step_bb2_3 v b hb) ?_
  refine .next (step_bb2_4 v b hb) ?_
  cases hge : decide (64 ≤ b.toNat)
  · dsimp only [ite_false, boolWord]
    refine .next (by rfl : step maskBody (s_bb2_5 v b 0) = .next (s_bb4_0 v b)) ?_
    have hlt : b.toNat < 64 := Nat.lt_of_not_le (of_decide_eq_false hge)
    exact exec_bb4 v b hb hlt
  · dsimp only [ite_true, boolWord]
    refine .next (by rfl : step maskBody (s_bb2_5 v b 1) = .next (s_bb3_0 v b)) ?_
    exact exec_bb3 v b

theorem exec_mask (v b : Word) (hb : validValue (.int 32 false) b = true) :
    Executes maskBody (initial maskBody [v, b]) (maskLowBitsSpec v b) := by
  have hinit : initial maskBody [v, b] = s_bb0_0 v b := rfl
  rw [hinit]
  unfold maskLowBitsSpec
  refine .next (by rfl : step maskBody (s_bb0_0 v b) = .next (s_bb0_1 v b)) ?_
  refine .next (by rfl : step maskBody (s_bb0_1 v b) = .next (s_bb0_2 v b)) ?_
  refine .next (step_bb0_2 v b hb) ?_
  refine .next (step_bb0_3 v b hb) ?_
  cases heq : (b == 0)
  · dsimp only [ite_false, boolWord]
    refine .next (by rfl : step maskBody (s_bb0_4 v b 0) = .next (s_bb2_0 v b)) ?_
    exact exec_bb2 v b hb
  · dsimp only [ite_true, boolWord]
    refine .next (by rfl : step maskBody (s_bb0_4 v b 1) = .next (s_bb1_0 v b)) ?_
    exact exec_bb1 v b

theorem mask_exact : exactMaskLowBits maskBody := by
  intro value bitCount hb
  have hexec := exec_mask value bitCount hb
  exact ⟨executes_safe hexec, executes_returns hexec⟩

theorem validArgs2_elim (args : List Word) (valid : argsValid maskBody args) :
    Safe maskBody args := by
  rcases args with _ | ⟨v, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · have hlen : ([] : List Word).length = 2 := valid.1
    cases hlen
  · have hlen : ([v] : List Word).length = 2 := valid.1
    cases hlen
  · have hb_ex := valid.2 1 b rfl
    rcases hb_ex with ⟨ty, hty, hb⟩
    have heq : ty = .int 32 false := Option.some.inj (hty.symm.trans localTy_2)
    subst ty
    exact (mask_exact v b hb).1
  · have hlen : (v :: b :: c :: rest).length = 2 := valid.1
    cases hlen

theorem baseline (safetyPre : List Word → Prop) :
    BodyVerified maskBody safetyPre :=
  ⟨wellFormed, fun args valid _ => validArgs2_elim args valid⟩

theorem verify : Expected.claim := by
  constructor
  · rfl
  · constructor
    · intro id body found
      change ([maskBody] : List Body)[id]? = some body at found
      cases id with
      | zero =>
          have same : maskBody = body := Option.some.inj found
          subst body
          exact baseline _
      | succ id => simp at found
    · exact ⟨maskBody, rfl, mask_exact⟩

end Proof
