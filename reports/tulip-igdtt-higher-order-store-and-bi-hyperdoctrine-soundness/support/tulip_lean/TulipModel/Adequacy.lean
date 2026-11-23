-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import TulipModel.Equations

/-!
# Closed-Program Adequacy Extraction (`wp_adequacy`)

Proves external Lean `Prop` adequacy of `wpRepaired` (`paper.tex:2135–2152`):
if `⊤ ⊢ wpRepaired e (BIPred.pureConst P)` holds at stage `n = k + 1` over
`World.empty (k + 1)`, and running `e` on `(World.empty (k + 1), Heaplet.empty _)`
terminates within `≤ k` guarded steps (or via computable `M.runClosed`) returning
`v : α`, then `P v` holds externally in Lean `Prop`!
-/

namespace Tulip

/-- `StepLift.TerminatesWith c fuel j hj ans` witnesses that `c : StepLift n X`
reaches a terminal answer `Sum.inl ans` at stage `(j, hj)` in at most `fuel`
guarded `Sum.inr` steps (never hitting the stage-`0` `stepZero` horizon). -/
inductive StepLift.TerminatesWith :
    {n : Nat} → {X : (m : Nat) → m ≤ n → Type 1} →
    StepLift n X → Nat → (j : Nat) → (hj : j ≤ n) → X j hj → Prop where
  | retZero {X : (m : Nat) → m ≤ 0 → Type 1}
      (ans : X 0 (Nat.le_refl 0)) (fuel : Nat) :
      StepLift.TerminatesWith (n := 0) (Sum.inl ans) fuel 0 (Nat.le_refl 0) ans
  | retSucc {m : Nat} {X : (j : Nat) → j ≤ m + 1 → Type 1}
      (ans : X (m + 1) (Nat.le_refl (m + 1))) (fuel : Nat) :
      StepLift.TerminatesWith (n := m + 1) (Sum.inl ans) fuel (m + 1) (Nat.le_refl (m + 1)) ans
  | step {m : Nat} {X : (j : Nat) → j ≤ m + 1 → Type 1}
      (c' : StepLift m (fun j hj => X j (Nat.le_succ_of_le hj)))
      (fuel : Nat) (j : Nat) (hj : j ≤ m) (ans : X j (Nat.le_succ_of_le hj)) :
      StepLift.TerminatesWith c' fuel j hj ans →
      StepLift.TerminatesWith (n := m + 1) (Sum.inr c') (fuel + 1) j (Nat.le_succ_of_le hj) ans

/-- Extracting `Φ j hj ans` from `StepLift.lLift c Φ` along a bounded-step termination witness. -/
theorem StepLift.lLift_extract {n : Nat} {X : (m : Nat) → m ≤ n → Type 1}
    {c : StepLift n X} {fuel : Nat} {j : Nat} {hj : j ≤ n} {ans : X j hj}
    {Φ : ∀ (m : Nat) (hm : m ≤ n), X m hm → Prop}
    (hterm : StepLift.TerminatesWith c fuel j hj ans)
    (hlift : StepLift.lLift c Φ) :
    Φ j hj ans := by
  induction hterm with
  | retZero _ _ => exact hlift
  | retSucc _ _ => exact hlift
  | step _ _ _ _ _ _ ih => exact ih hlift

/-- Computable step-counting extractor for `StepLift` via a projection `proj : X m hm → α`. -/
noncomputable def StepLift.extractBy {α : Type 0} :
    {n : Nat} → {X : (m : Nat) → m ≤ n → Type 1} →
    (∀ (m : Nat) (hm : m ≤ n), X m hm → α) →
    StepLift n X → Option (Nat × α)
  | 0,     _, proj, Sum.inl ans => some (0, proj 0 (Nat.le_refl 0) ans)
  | 0,     _, _,    Sum.inr _   => none
  | m + 1, _, proj, Sum.inl ans => some (0, proj (m + 1) (Nat.le_refl (m + 1)) ans)
  | _ + 1, _, proj, Sum.inr c'  =>
      match StepLift.extractBy (fun j hj x => proj j (Nat.le_succ_of_le hj) x) c' with
      | none        => none
      | some (s, v) => some (s + 1, v)

/-- Run a closed stage-`n` computation `e : M (.const α)` on `(∅, ∅)`, returning
`some (stepsTaken, v)` iff `e` terminates within `≤ n` guarded steps. -/
noncomputable def M.runClosed {n : Nat} {α : Type 0}
    (e : SemTy.eval n (M (.const α)) (World.empty n)) : Option (Nat × α) :=
  StepLift.extractBy (fun _ _ ans => ans.2.2.2.down)
    (e n (Nat.le_refl n) (World.empty n) (by simpa using World.le_refl (World.empty n))
      (Heaplet.empty (World.empty n)))

theorem StepLift.terminatesWith_of_extractBy {α : Type 0} :
    ∀ {n : Nat} {X : (m : Nat) → m ≤ n → Type 1}
      {proj : ∀ (m : Nat) (hm : m ≤ n), X m hm → α}
      {c : StepLift n X} {steps : Nat} {v : α},
      StepLift.extractBy proj c = some (steps, v) →
      steps ≤ n ∧
      ∃ (j : Nat) (hj : j ≤ n) (ans : X j hj),
        proj j hj ans = v ∧ StepLift.TerminatesWith c steps j hj ans
  | 0, _, proj, Sum.inl ans, _, _, heq => by
      dsimp only [StepLift.extractBy] at heq
      injection heq with heq
      injection heq with hs hv
      subst hs; subst hv
      exact ⟨Nat.le_refl 0, 0, Nat.le_refl 0, ans, rfl, .retZero ans 0⟩
  | 0, _, _, Sum.inr _, _, _, heq => nomatch heq
  | m + 1, _, proj, Sum.inl ans, _, _, heq => by
      dsimp only [StepLift.extractBy] at heq
      injection heq with heq
      injection heq with hs hv
      subst hs; subst hv
      exact ⟨Nat.zero_le _, m + 1, Nat.le_refl (m + 1), ans, rfl, .retSucc ans 0⟩
  | m + 1, _, proj, Sum.inr c', _, _, heq => by
      dsimp only [StepLift.extractBy] at heq
      cases hex : StepLift.extractBy (fun j hj x => proj j (Nat.le_succ_of_le hj) x) c' with
      | none => rw [hex] at heq; nomatch heq
      | some sv =>
        rcases sv with ⟨s', v'⟩
        rw [hex] at heq
        injection heq with heq
        injection heq with hs hv
        subst hs; subst hv
        rcases StepLift.terminatesWith_of_extractBy hex with ⟨hs', j, hj, ans, rfl, hterm⟩
        exact ⟨Nat.succ_le_succ hs', j, Nat.le_succ_of_le hj, ans, rfl,
          .step c' s' j hj ans hterm⟩

/-- On the empty world `World.empty n`, the empty total heap `Heaplet.empty` converts
to `ParHeap.empty`. -/
theorem TotHeap.empty_toParHeap (n : Nat) :
    TotHeap.toParHeap (Heaplet.empty (World.empty n)) =
      ParHeap.empty n (World.empty n) := by
  refine ParHeap.ext (fun l => by simp [TotHeap.toParHeap]) ?_
  intro l _ hd _
  simp [TotHeap.toParHeap] at hd

/-- **`wp_adequacy` (Closed-Program Adequacy Extraction Theorem)**:
If `⊤ ⊢ wpRepaired e (BIPred.pureConst P)` holds at stage `n = k + 1` over `World.empty (k + 1)`,
and running `e` on `(World.empty (k + 1), Heaplet.empty _)` terminates in `≤ k`
guarded steps (`StepLift.TerminatesWith ... k j hj ans`) with pure value `ans.2.2.2 = ULift.up v`,
then `P v` holds externally in Lean `Prop`! -/
theorem wp_adequacy {k : Nat} {α : Type 0} {P : α → Prop}
    (e : SemTy.eval (k + 1) (M (.const α)) (World.empty (k + 1)))
    {j : Nat} {hj : j ≤ k + 1}
    {ans : CompAns (.const α) (k + 1) (World.empty (k + 1)) j hj}
    {v : α}
    (hwp : BIProp.Entails (BIProp.top (k + 1) (World.empty (k + 1)))
      (wpRepaired e (BIPred.pureConst P)))
    (hterm : StepLift.TerminatesWith
      (e (k + 1) (Nat.le_refl (k + 1)) (World.empty (k + 1))
        (by simpa using World.le_refl (World.empty (k + 1)))
        (Heaplet.empty (World.empty (k + 1))))
      k j hj ans)
    (hval : ans.2.2.2 = ULift.up v) :
    P v := by
  let w₀ := World.empty (k + 1)
  let emp := ParHeap.empty (k + 1) w₀
  have hwp_emp := hwp (k + 1) (Nat.le_refl (k + 1)) w₀ (World.restrict_refl_le w₀) emp trivial
  have hemp_refl : (emp.restrict (Nat.le_refl (k + 1))).map
      (by simpa using World.le_refl w₀) = emp := by
    simpa using ParHeap.restrict_refl_map emp
  have htot_emp : TotHeap.toParHeap (Heaplet.empty w₀) =
      emp.union ((emp.restrict (Nat.le_refl (k + 1))).map (by simpa using World.le_refl w₀)) := by
    rw [hemp_refl, ParHeap.union_empty, TotHeap.empty_toParHeap]
  have hlift := hwp_emp (k + 1) (Nat.le_refl (k + 1)) w₀ (by simpa using World.le_refl w₀)
    emp (ParHeap.disjoint_empty_left _) (Heaplet.empty w₀) htot_emp
  rcases StepLift.lLift_extract hterm hlift with ⟨_, _, _, _, _, _, _, _, hP⟩
  change P ans.2.2.2.down at hP
  rw [hval] at hP
  exact hP

/-- **Executable Closed-Program Adequacy Corollary (`wp_adequacy_runClosed`)**:
If `⊤ ⊢ wpRepaired e (BIPred.pureConst P)` at stage `n` and `M.runClosed e = some (steps, v)`,
then `steps ≤ n` and `P v` holds in Lean `Prop`! -/
theorem wp_adequacy_runClosed {n : Nat} {α : Type 0} {P : α → Prop}
    (e : SemTy.eval n (M (.const α)) (World.empty n))
    {steps : Nat} {v : α}
    (hwp : BIProp.Entails (BIProp.top n (World.empty n))
      (wpRepaired e (BIPred.pureConst P)))
    (hrun : M.runClosed e = some (steps, v)) :
    steps ≤ n ∧ P v := by
  rcases StepLift.terminatesWith_of_extractBy hrun with ⟨hsteps, j, hj, ans, rfl, hterm⟩
  refine ⟨hsteps, ?_⟩
  let w₀ := World.empty n
  let emp := ParHeap.empty n w₀
  have hwp_emp := hwp n (Nat.le_refl n) w₀ (World.restrict_refl_le w₀) emp trivial
  have hemp_refl : (emp.restrict (Nat.le_refl n)).map
      (by simpa using World.le_refl w₀) = emp := by
    simpa using ParHeap.restrict_refl_map emp
  have htot_emp : TotHeap.toParHeap (Heaplet.empty w₀) =
      emp.union ((emp.restrict (Nat.le_refl n)).map (by simpa using World.le_refl w₀)) := by
    rw [hemp_refl, ParHeap.union_empty, TotHeap.empty_toParHeap]
  have hlift := hwp_emp n (Nat.le_refl n) w₀ (by simpa using World.le_refl w₀)
    emp (ParHeap.disjoint_empty_left _) (Heaplet.empty w₀) htot_emp
  rcases StepLift.lLift_extract hterm hlift with ⟨_, _, _, _, _, _, _, _, hP⟩
  exact hP

end Tulip
