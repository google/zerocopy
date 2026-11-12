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
import Init.Data.Nat.Bitwise.Lemmas

namespace Proof

open Trusted.Mvp Anneal.Mvp Spec

abbrev popBody : Body := Captured.program.bodies[0]'(by decide)

theorem wellFormed : bodyWF popBody = true := by decide

theorem kernighan_lt (x : Word) (hx : (x != 0) = true) :
    (x &&& (x - 1)).toNat < x.toNat := by
  have hne : x ≠ 0 := by
    intro h; subst h; revert hx; decide
  have hpos : 0 < x.toNat := by
    cases Nat.eq_zero_or_pos x.toNat with
    | inl h0 => exact False.elim (hne (BitVec.eq_of_toNat_eq h0))
    | inr hp => exact hp
  have h1le : (1 : Word) ≤ x := hpos
  have hsub : (x - 1).toNat = x.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le h1le]
    rfl
  have hand : (x &&& (x - 1)).toNat ≤ (x - 1).toNat := by
    rw [BitVec.toNat_and]
    exact Nat.and_le_right
  omega

theorem kernighanSteps_irrel (fuel1 fuel2 : Nat) (x count : Word)
    (h1 : x.toNat < fuel1) (h2 : x.toNat < fuel2) :
    kernighanSteps fuel1 x count = kernighanSteps fuel2 x count := by
  induction fuel1 generalizing fuel2 x count with
  | zero => exact False.elim (Nat.not_lt_zero _ h1)
  | succ f1 ih =>
      cases fuel2 with
      | zero => exact False.elim (Nat.not_lt_zero _ h2)
      | succ f2 =>
          unfold kernighanSteps
          cases hne : (x != 0)
          · rfl
          · simp only [ite_true]
            have hlt := kernighan_lt x hne
            exact ih f2 (x &&& (x - 1)) (count + 1)
              (Nat.lt_of_lt_of_le hlt (Nat.le_of_lt_succ h1))
              (Nat.lt_of_lt_of_le hlt (Nat.le_of_lt_succ h2))

theorem kernighanSteps_add (fuel : Nat) (x count : Word) (h : x.toNat < fuel) :
    kernighanSteps fuel x count = count + kernighanSteps fuel x 0 := by
  induction fuel generalizing x count with
  | zero => exact False.elim (Nat.not_lt_zero _ h)
  | succ f ih =>
      unfold kernighanSteps
      cases hne : (x != 0)
      · simp
      · simp only [ite_true]
        have hlt : (x &&& (x - 1)).toNat < f :=
          Nat.lt_of_lt_of_le (kernighan_lt x hne) (Nat.le_of_lt_succ h)
        have h01 : (0 : Word) + 1 = 1 := rfl
        rw [ih (x &&& (x - 1)) (count + 1) hlt, h01, ih (x &&& (x - 1)) 1 hlt]
        rw [← BitVec.add_assoc]

theorem popcountSpec_zero : popcountSpec 0 = 0 := rfl

theorem popcountSpec_step (x : Word) (hx : (x != 0) = true) :
    popcountSpec x = popcountSpec (x &&& (x - 1)) + 1 := by
  unfold popcountSpec
  conv => lhs; unfold kernighanSteps
  rw [hx]
  simp only [ite_true]
  have h01 : (0 : Word) + 1 = 1 := rfl
  rw [h01]
  have hlt : (x &&& (x - 1)).toNat < x.toNat := kernighan_lt x hx
  rw [kernighanSteps_add x.toNat (x &&& (x - 1)) 1 hlt]
  rw [kernighanSteps_irrel x.toNat ((x &&& (x - 1)).toNat + 1) (x &&& (x - 1)) 0
    hlt (Nat.lt_succ_self _)]
  exact BitVec.add_comm 1 _

theorem validValue_bool (b : Bool) : validValue .bool (boolWord b) = true := by
  cases b <;> rfl

theorem evalBinary_ne_u64 (a b : Word) :
    evalBinary .ne (.int 64 false) a (.int 64 false) b = .ok (.bool, boolWord (a != b)) := by
  change (if validValue Ty.bool (boolWord (a != b)) = true then
      Except.ok (Ty.bool, boolWord (a != b)) else Except.error Fault.invalidValue) = _
  rw [validValue_bool]
  rfl

theorem localTy_5 : popBody.localTys[5]? = some .bool := rfl
theorem localTy_6 : popBody.localTys[6]? = some (.int 64 false) := rfl
theorem rawValid_u64_0 : rawValid (.int 64 false) 0 = true := rfl
theorem validValue_u64 (a : Word) : validValue (.int 64 false) a = true := rfl

def s_bb0_0 (x : Word) : State :=
  ⟨0, 0, [.uninit, .value x, .dead, .dead, .uninit, .dead, .dead, .dead, .dead, .uninit, .dead, .uninit]⟩
def s_bb0_1 (x : Word) : State :=
  ⟨0, 1, [.uninit, .value x, .uninit, .dead, .uninit, .dead, .dead, .dead, .dead, .uninit, .dead, .uninit]⟩
def s_bb0_2 (x : Word) : State :=
  ⟨0, 2, [.uninit, .value x, .value 0, .dead, .uninit, .dead, .dead, .dead, .dead, .uninit, .dead, .uninit]⟩
def s_bb0_3 (x : Word) : State :=
  ⟨0, 3, [.uninit, .value x, .value 0, .uninit, .uninit, .dead, .dead, .dead, .dead, .uninit, .dead, .uninit]⟩

def s_bb1_0 (x count : Word) (s4 : Slot) : State :=
  ⟨1, 0, [.uninit, .value x, .value count, .uninit, s4, .dead, .dead, .dead, .dead, .uninit, .dead, .uninit]⟩
def s_bb1_1 (x count : Word) (s4 : Slot) : State :=
  ⟨1, 1, [.uninit, .value x, .value count, .uninit, s4, .uninit, .dead, .dead, .dead, .uninit, .dead, .uninit]⟩
def s_bb1_2 (x count : Word) (s4 : Slot) : State :=
  ⟨1, 2, [.uninit, .value x, .value count, .uninit, s4, .uninit, .uninit, .dead, .dead, .uninit, .dead, .uninit]⟩
def s_bb1_3 (x count : Word) (s4 : Slot) : State :=
  ⟨1, 3, [.uninit, .value x, .value count, .uninit, s4, .uninit, .value x, .dead, .dead, .uninit, .dead, .uninit]⟩
def s_bb1_4 (x count : Word) (s4 : Slot) (ne0 : Word) : State :=
  ⟨1, 4, [.uninit, .value x, .value count, .uninit, s4, .value ne0, .uninit, .dead, .dead, .uninit, .dead, .uninit]⟩

def s_bb2_0 (x count : Word) (s4 : Slot) : State :=
  ⟨2, 0, [.uninit, .value x, .value count, .uninit, s4, .uninit, .uninit, .dead, .dead, .uninit, .dead, .uninit]⟩
def s_bb2_1 (x count : Word) (s4 : Slot) : State :=
  ⟨2, 1, [.uninit, .value x, .value count, .uninit, s4, .uninit, .dead, .dead, .dead, .uninit, .dead, .uninit]⟩
def s_bb2_2 (x count : Word) (s4 : Slot) : State :=
  ⟨2, 2, [.uninit, .value x, .value count, .uninit, s4, .uninit, .dead, .uninit, .dead, .uninit, .dead, .uninit]⟩
def s_bb2_3 (x count : Word) (s4 : Slot) : State :=
  ⟨2, 3, [.uninit, .value x, .value count, .uninit, s4, .uninit, .dead, .uninit, .uninit, .uninit, .dead, .uninit]⟩
def s_bb2_4 (x count : Word) (s4 : Slot) : State :=
  ⟨2, 4, [.uninit, .value x, .value count, .uninit, s4, .uninit, .dead, .uninit, .value x, .uninit, .dead, .uninit]⟩
def s_bb2_5 (x count : Word) (s4 : Slot) : State :=
  ⟨2, 5, [.uninit, .value x, .value count, .uninit, s4, .uninit, .dead, .value (x - 1), .uninit, .uninit, .dead, .uninit]⟩
def s_bb2_6 (x count : Word) (s4 : Slot) : State :=
  ⟨2, 6, [.uninit, .value x, .value count, .uninit, s4, .uninit, .dead, .value (x - 1), .dead, .uninit, .dead, .uninit]⟩
def s_bb2_7 (x count : Word) (s4 : Slot) : State :=
  ⟨2, 7, [.uninit, .value (x &&& (x - 1)), .value count, .uninit, s4, .uninit, .dead, .uninit, .dead, .uninit, .dead, .uninit]⟩
def s_bb2_8 (x count : Word) (s4 : Slot) : State :=
  ⟨2, 8, [.uninit, .value (x &&& (x - 1)), .value count, .uninit, s4, .uninit, .dead, .dead, .dead, .uninit, .dead, .uninit]⟩
def s_bb2_9 (x count : Word) (s4 : Slot) : State :=
  ⟨2, 9, [.uninit, .value (x &&& (x - 1)), .value (count + 1), .uninit, s4, .uninit, .dead, .dead, .dead, .uninit, .dead, .uninit]⟩
def s_bb2_10 (x count : Word) : State :=
  ⟨2, 10, [.uninit, .value (x &&& (x - 1)), .value (count + 1), .uninit, .value 0, .uninit, .dead, .dead, .dead, .uninit, .dead, .uninit]⟩
def s_bb2_11 (x count : Word) : State :=
  ⟨2, 11, [.uninit, .value (x &&& (x - 1)), .value (count + 1), .uninit, .value 0, .dead, .dead, .dead, .dead, .uninit, .dead, .uninit]⟩

def s_bb3_0 (x count : Word) (s4 : Slot) : State :=
  ⟨3, 0, [.uninit, .value x, .value count, .uninit, s4, .uninit, .uninit, .dead, .dead, .uninit, .dead, .uninit]⟩
def s_bb3_1 (x count : Word) (s4 : Slot) : State :=
  ⟨3, 1, [.uninit, .value x, .value count, .uninit, s4, .uninit, .dead, .dead, .dead, .uninit, .dead, .uninit]⟩
def s_bb3_2 (x count : Word) (s4 : Slot) : State :=
  ⟨3, 2, [.uninit, .value x, .value count, .uninit, s4, .uninit, .dead, .dead, .dead, .uninit, .uninit, .uninit]⟩
def s_bb3_3 (x count : Word) (s4 : Slot) : State :=
  ⟨3, 3, [.uninit, .value x, .value count, .value 0, s4, .uninit, .dead, .dead, .dead, .uninit, .uninit, .uninit]⟩
def s_bb3_4 (x count : Word) (s4 : Slot) : State :=
  ⟨3, 4, [.uninit, .value x, .value count, .value 0, s4, .uninit, .dead, .dead, .dead, .uninit, .dead, .uninit]⟩
def s_bb3_5 (x count : Word) (s4 : Slot) : State :=
  ⟨3, 5, [.uninit, .value x, .value count, .value 0, s4, .dead, .dead, .dead, .dead, .uninit, .dead, .uninit]⟩
def s_bb3_6 (x count : Word) (s4 : Slot) : State :=
  ⟨3, 6, [.uninit, .value x, .value count, .dead, s4, .dead, .dead, .dead, .dead, .uninit, .dead, .uninit]⟩
def s_bb3_7 (x count : Word) (s4 : Slot) : State :=
  ⟨3, 7, [.value count, .value x, .value count, .dead, s4, .dead, .dead, .dead, .dead, .uninit, .dead, .uninit]⟩
def s_bb3_8 (x count : Word) (s4 : Slot) : State :=
  ⟨3, 8, [.value count, .value x, .dead, .dead, s4, .dead, .dead, .dead, .dead, .uninit, .dead, .uninit]⟩

theorem step_bb1_3 (x count : Word) (s4 : Slot) :
    step popBody (s_bb1_3 x count s4) = .next (s_bb1_4 x count s4 (boolWord (x != 0))) := by
  change (match execStatement popBody (s_bb1_3 x count s4).locals
      (.assign 5 (.binary .ne (.move 6) (.constant (.int 64 false) 0))) with
    | .ok locals => StepResult.next ⟨1, 4, locals⟩
    | .error reason => StepResult.fault reason) = .next (s_bb1_4 x count s4 (boolWord (x != 0)))
  simp only [execStatement, evalRvalue, evalOperand, readLocal, writeLocal, s_bb1_3,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.set_cons_zero, List.set_cons_succ,
    localTy_5, localTy_6, rawValid_u64_0, validValue_u64, ite_true, evalBinary_ne_u64, validValue_bool]
  rfl

theorem exec_bb3 (x count : Word) (s4 : Slot) (hs4 : s4 = .uninit ∨ s4 = .value 0) :
    Executes popBody (s_bb3_0 x count s4) count := by
  cases hs4 with
  | inl h => subst h; exact run_executes (fuel := 9) rfl
  | inr h => subst h; exact run_executes (fuel := 9) rfl

theorem exec_bb2_to_bb1 (x count : Word) (s4 : Slot) (hs4 : s4 = .uninit ∨ s4 = .value 0)
    (out : Word) (hnext : Executes popBody (s_bb1_0 (x &&& (x - 1)) (count + 1) (.value 0)) out) :
    Executes popBody (s_bb2_0 x count s4) out := by
  refine .next (by rfl : step popBody (s_bb2_0 x count s4) = .next (s_bb2_1 x count s4)) ?_
  refine .next (by rfl : step popBody (s_bb2_1 x count s4) = .next (s_bb2_2 x count s4)) ?_
  refine .next (by rfl : step popBody (s_bb2_2 x count s4) = .next (s_bb2_3 x count s4)) ?_
  refine .next (by rfl : step popBody (s_bb2_3 x count s4) = .next (s_bb2_4 x count s4)) ?_
  refine .next (by rfl : step popBody (s_bb2_4 x count s4) = .next (s_bb2_5 x count s4)) ?_
  refine .next (by rfl : step popBody (s_bb2_5 x count s4) = .next (s_bb2_6 x count s4)) ?_
  refine .next (by rfl : step popBody (s_bb2_6 x count s4) = .next (s_bb2_7 x count s4)) ?_
  refine .next (by rfl : step popBody (s_bb2_7 x count s4) = .next (s_bb2_8 x count s4)) ?_
  refine .next (by rfl : step popBody (s_bb2_8 x count s4) = .next (s_bb2_9 x count s4)) ?_
  have hstep9 : step popBody (s_bb2_9 x count s4) = .next (s_bb2_10 x count) := by
    cases hs4 with
    | inl h => subst h; rfl
    | inr h => subst h; rfl
  refine .next hstep9 ?_
  refine .next (by rfl : step popBody (s_bb2_10 x count) = .next (s_bb2_11 x count)) ?_
  refine .next (by rfl : step popBody (s_bb2_11 x count) = .next (s_bb1_0 (x &&& (x - 1)) (count + 1) (.value 0))) hnext

theorem exec_loop (fuel : Nat) (x count : Word) (s4 : Slot)
    (hs4 : s4 = .uninit ∨ s4 = .value 0) (hbound : x.toNat < fuel) :
    Executes popBody (s_bb1_0 x count s4) (kernighanSteps fuel x count) := by
  induction fuel generalizing x count s4 with
  | zero => exact False.elim (Nat.not_lt_zero _ hbound)
  | succ f ih =>
      unfold kernighanSteps
      refine .next (by rfl : step popBody (s_bb1_0 x count s4) = .next (s_bb1_1 x count s4)) ?_
      refine .next (by rfl : step popBody (s_bb1_1 x count s4) = .next (s_bb1_2 x count s4)) ?_
      refine .next (by rfl : step popBody (s_bb1_2 x count s4) = .next (s_bb1_3 x count s4)) ?_
      refine .next (step_bb1_3 x count s4) ?_
      cases hne : (x != 0)
      · dsimp only [ite_false, boolWord]
        refine .next (by rfl : step popBody (s_bb1_4 x count s4 0) = .next (s_bb3_0 x count s4)) ?_
        exact exec_bb3 x count s4 hs4
      · dsimp only [ite_true, boolWord]
        refine .next (by rfl : step popBody (s_bb1_4 x count s4 1) = .next (s_bb2_0 x count s4)) ?_
        have hlt : (x &&& (x - 1)).toNat < f :=
          Nat.lt_of_lt_of_le (kernighan_lt x hne) (Nat.le_of_lt_succ hbound)
        exact exec_bb2_to_bb1 x count s4 hs4 _
          (ih (x &&& (x - 1)) (count + 1) (.value 0) (.inr rfl) hlt)

theorem exec_popcount (x : Word) :
    Executes popBody (initial popBody [x]) (popcountSpec x) := by
  have hinit : initial popBody [x] = s_bb0_0 x := rfl
  rw [hinit]
  refine .next (by rfl : step popBody (s_bb0_0 x) = .next (s_bb0_1 x)) ?_
  refine .next (by rfl : step popBody (s_bb0_1 x) = .next (s_bb0_2 x)) ?_
  refine .next (by rfl : step popBody (s_bb0_2 x) = .next (s_bb0_3 x)) ?_
  refine .next (by rfl : step popBody (s_bb0_3 x) = .next (s_bb1_0 x 0 .uninit)) ?_
  exact exec_loop (x.toNat + 1) x 0 .uninit (.inl rfl) (Nat.lt_succ_self _)

theorem popcount_exact : exactPopcount popBody :=
  ⟨fun x => ⟨executes_safe (exec_popcount x), executes_returns (exec_popcount x)⟩,
   popcountSpec_zero, popcountSpec_step⟩

inductive PopcountInv : State → Prop where
  | bb0_0 (x : Word) : PopcountInv (s_bb0_0 x)
  | bb0_1 (x : Word) : PopcountInv (s_bb0_1 x)
  | bb0_2 (x : Word) : PopcountInv (s_bb0_2 x)
  | bb0_3 (x : Word) : PopcountInv (s_bb0_3 x)
  | bb1_0 (x c : Word) (s4 : Slot) (h : s4 = .uninit ∨ s4 = .value 0) : PopcountInv (s_bb1_0 x c s4)
  | bb1_1 (x c : Word) (s4 : Slot) (h : s4 = .uninit ∨ s4 = .value 0) : PopcountInv (s_bb1_1 x c s4)
  | bb1_2 (x c : Word) (s4 : Slot) (h : s4 = .uninit ∨ s4 = .value 0) : PopcountInv (s_bb1_2 x c s4)
  | bb1_3 (x c : Word) (s4 : Slot) (h : s4 = .uninit ∨ s4 = .value 0) : PopcountInv (s_bb1_3 x c s4)
  | bb1_4 (x c : Word) (s4 : Slot) (b : Bool) (h : s4 = .uninit ∨ s4 = .value 0) : PopcountInv (s_bb1_4 x c s4 (boolWord b))
  | bb2_0 (x c : Word) (s4 : Slot) (h : s4 = .uninit ∨ s4 = .value 0) : PopcountInv (s_bb2_0 x c s4)
  | bb2_1 (x c : Word) (s4 : Slot) (h : s4 = .uninit ∨ s4 = .value 0) : PopcountInv (s_bb2_1 x c s4)
  | bb2_2 (x c : Word) (s4 : Slot) (h : s4 = .uninit ∨ s4 = .value 0) : PopcountInv (s_bb2_2 x c s4)
  | bb2_3 (x c : Word) (s4 : Slot) (h : s4 = .uninit ∨ s4 = .value 0) : PopcountInv (s_bb2_3 x c s4)
  | bb2_4 (x c : Word) (s4 : Slot) (h : s4 = .uninit ∨ s4 = .value 0) : PopcountInv (s_bb2_4 x c s4)
  | bb2_5 (x c : Word) (s4 : Slot) (h : s4 = .uninit ∨ s4 = .value 0) : PopcountInv (s_bb2_5 x c s4)
  | bb2_6 (x c : Word) (s4 : Slot) (h : s4 = .uninit ∨ s4 = .value 0) : PopcountInv (s_bb2_6 x c s4)
  | bb2_7 (x c : Word) (s4 : Slot) (h : s4 = .uninit ∨ s4 = .value 0) : PopcountInv (s_bb2_7 x c s4)
  | bb2_8 (x c : Word) (s4 : Slot) (h : s4 = .uninit ∨ s4 = .value 0) : PopcountInv (s_bb2_8 x c s4)
  | bb2_9 (x c : Word) (s4 : Slot) (h : s4 = .uninit ∨ s4 = .value 0) : PopcountInv (s_bb2_9 x c s4)
  | bb2_10 (x c : Word) : PopcountInv (s_bb2_10 x c)
  | bb2_11 (x c : Word) : PopcountInv (s_bb2_11 x c)
  | bb3_0 (x c : Word) (s4 : Slot) (h : s4 = .uninit ∨ s4 = .value 0) : PopcountInv (s_bb3_0 x c s4)
  | bb3_1 (x c : Word) (s4 : Slot) (h : s4 = .uninit ∨ s4 = .value 0) : PopcountInv (s_bb3_1 x c s4)
  | bb3_2 (x c : Word) (s4 : Slot) (h : s4 = .uninit ∨ s4 = .value 0) : PopcountInv (s_bb3_2 x c s4)
  | bb3_3 (x c : Word) (s4 : Slot) (h : s4 = .uninit ∨ s4 = .value 0) : PopcountInv (s_bb3_3 x c s4)
  | bb3_4 (x c : Word) (s4 : Slot) (h : s4 = .uninit ∨ s4 = .value 0) : PopcountInv (s_bb3_4 x c s4)
  | bb3_5 (x c : Word) (s4 : Slot) (h : s4 = .uninit ∨ s4 = .value 0) : PopcountInv (s_bb3_5 x c s4)
  | bb3_6 (x c : Word) (s4 : Slot) (h : s4 = .uninit ∨ s4 = .value 0) : PopcountInv (s_bb3_6 x c s4)
  | bb3_7 (x c : Word) (s4 : Slot) (h : s4 = .uninit ∨ s4 = .value 0) : PopcountInv (s_bb3_7 x c s4)
  | bb3_8 (x c : Word) (s4 : Slot) (h : s4 = .uninit ∨ s4 = .value 0) : PopcountInv (s_bb3_8 x c s4)

theorem popcountInv_step (state : State) (hinv : PopcountInv state) :
    (∃ next, step popBody state = .next next ∧ PopcountInv next) ∨
    (∃ val, step popBody state = .ret val) := by
  cases hinv with
  | bb0_0 x => exact .inl ⟨_, rfl, .bb0_1 x⟩
  | bb0_1 x => exact .inl ⟨_, rfl, .bb0_2 x⟩
  | bb0_2 x => exact .inl ⟨_, rfl, .bb0_3 x⟩
  | bb0_3 x => exact .inl ⟨_, rfl, .bb1_0 x 0 .uninit (.inl rfl)⟩
  | bb1_0 x c s4 h => exact .inl ⟨_, rfl, .bb1_1 x c s4 h⟩
  | bb1_1 x c s4 h => exact .inl ⟨_, rfl, .bb1_2 x c s4 h⟩
  | bb1_2 x c s4 h => exact .inl ⟨_, rfl, .bb1_3 x c s4 h⟩
  | bb1_3 x c s4 h => exact .inl ⟨_, step_bb1_3 x c s4, .bb1_4 x c s4 (x != 0) h⟩
  | bb1_4 x c s4 b h =>
      cases b
      · exact .inl ⟨_, rfl, .bb3_0 x c s4 h⟩
      · exact .inl ⟨_, rfl, .bb2_0 x c s4 h⟩
  | bb2_0 x c s4 h => exact .inl ⟨_, rfl, .bb2_1 x c s4 h⟩
  | bb2_1 x c s4 h => exact .inl ⟨_, rfl, .bb2_2 x c s4 h⟩
  | bb2_2 x c s4 h => exact .inl ⟨_, rfl, .bb2_3 x c s4 h⟩
  | bb2_3 x c s4 h => exact .inl ⟨_, rfl, .bb2_4 x c s4 h⟩
  | bb2_4 x c s4 h => exact .inl ⟨_, rfl, .bb2_5 x c s4 h⟩
  | bb2_5 x c s4 h => exact .inl ⟨_, rfl, .bb2_6 x c s4 h⟩
  | bb2_6 x c s4 h => exact .inl ⟨_, rfl, .bb2_7 x c s4 h⟩
  | bb2_7 x c s4 h => exact .inl ⟨_, rfl, .bb2_8 x c s4 h⟩
  | bb2_8 x c s4 h => exact .inl ⟨_, rfl, .bb2_9 x c s4 h⟩
  | bb2_9 x c s4 h =>
      cases h with
      | inl h0 => subst h0; exact .inl ⟨_, rfl, .bb2_10 x c⟩
      | inr h0 => subst h0; exact .inl ⟨_, rfl, .bb2_10 x c⟩
  | bb2_10 x c => exact .inl ⟨_, rfl, .bb2_11 x c⟩
  | bb2_11 x c => exact .inl ⟨_, rfl, .bb1_0 (x &&& (x - 1)) (c + 1) (.value 0) (.inr rfl)⟩
  | bb3_0 x c s4 h => exact .inl ⟨_, rfl, .bb3_1 x c s4 h⟩
  | bb3_1 x c s4 h => exact .inl ⟨_, rfl, .bb3_2 x c s4 h⟩
  | bb3_2 x c s4 h => exact .inl ⟨_, rfl, .bb3_3 x c s4 h⟩
  | bb3_3 x c s4 h => exact .inl ⟨_, rfl, .bb3_4 x c s4 h⟩
  | bb3_4 x c s4 h => exact .inl ⟨_, rfl, .bb3_5 x c s4 h⟩
  | bb3_5 x c s4 h => exact .inl ⟨_, rfl, .bb3_6 x c s4 h⟩
  | bb3_6 x c s4 h => exact .inl ⟨_, rfl, .bb3_7 x c s4 h⟩
  | bb3_7 x c s4 h => exact .inl ⟨_, rfl, .bb3_8 x c s4 h⟩
  | bb3_8 x c s4 _ => exact .inr ⟨c, rfl⟩

theorem popcount_safe_via_invariant (x : Word) : Safe popBody [x] := by
  apply safeFrom_invariant PopcountInv (.bb0_0 x)
  · intro before after hinv hstep
    rcases popcountInv_step before hinv with ⟨next, hnext, hinv_next⟩ | ⟨val, hret⟩
    · rw [hnext] at hstep
      cases hstep
      exact hinv_next
    · rw [hret] at hstep
      cases hstep
  · intro state hinv reason hfault
    rcases popcountInv_step state hinv with ⟨next, hnext, _⟩ | ⟨val, hret⟩
    · rw [hnext] at hfault
      cases hfault
    · rw [hret] at hfault
      cases hfault

theorem validArgs1_elim (args : List Word) (valid : argsValid popBody args) :
    Safe popBody args := by
  rcases args with _ | ⟨x, _ | ⟨y, rest⟩⟩
  · have hlen : ([] : List Word).length = 1 := valid.1
    cases hlen
  · exact executes_safe (exec_popcount x)
  · have hlen : (x :: y :: rest).length = 1 := valid.1
    cases hlen

theorem baseline (safetyPre : List Word → Prop) :
    BodyVerified popBody safetyPre :=
  ⟨wellFormed, fun args valid _ => validArgs1_elim args valid⟩

theorem verify : Expected.claim := by
  constructor
  · rfl
  · constructor
    · intro id body found
      change ([popBody] : List Body)[id]? = some body at found
      cases id with
      | zero =>
          have same : popBody = body := Option.some.inj found
          subst body
          exact baseline _
      | succ id => simp at found
    · exact ⟨popBody, rfl, popcount_exact⟩

end Proof
