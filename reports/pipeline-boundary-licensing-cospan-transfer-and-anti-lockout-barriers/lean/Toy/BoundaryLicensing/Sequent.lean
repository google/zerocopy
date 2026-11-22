import Toy.BoundaryLicensing.Basic

set_option autoImplicit false

namespace Toy.BoundaryLicensing

/-! ## Sequents Separating Domain `ctxHyps` from Refuted `badHyps` and Branch Non-Vacuity -/

/-- Structured theorem sequent separating domain context `ctxHyps` from refuted bad-event premises `badHyps`. -/
structure Sequent (α : Type) (m k : Nat) where
  ctxHyps : Fin m → α → Prop
  badHyps : Fin k → α → Prop
  goal : α → Prop

/-- Conjunction of all domain context hypotheses at `x`. -/
def AllCtx {α : Type} {m : Nat} (ctxHyps : Fin m → α → Prop) (x : α) : Prop :=
  ∀ i : Fin m, ctxHyps i x

/-- Conjunction of all bad-event premises at `x`. -/
def AllBad {α : Type} {k : Nat} (badHyps : Fin k → α → Prop) (x : α) : Prop :=
  ∀ j : Fin k, badHyps j x

/-- Semantic validity of `sq`: whenever both `ctxHyps` and `badHyps` hold at `x`, `goal x` holds. -/
def Sequent.Holds {α : Type} {m k : Nat} (sq : Sequent α m k) : Prop :=
  ∀ x : α, AllCtx sq.ctxHyps x → AllBad sq.badHyps x → sq.goal x

/-- Domain non-vacuity: some instance `x` satisfies all `ctxHyps` (checked even when `goal = False`). -/
def Sequent.CtxNonVacuous {α : Type} {m k : Nat} (sq : Sequent α m k) : Prop :=
  ∃ x : α, AllCtx sq.ctxHyps x

/-- Naive full-premise non-vacuity requiring both `ctxHyps` and `badHyps` to hold simultaneously. -/
def Sequent.FullPremiseNonVacuous {α : Type} {m k : Nat} (sq : Sequent α m k) : Prop :=
  ∃ x : α, AllCtx sq.ctxHyps x ∧ AllBad sq.badHyps x

/-- Per-branch domain non-vacuity across a non-empty finite list of branch predicates. -/
def Sequent.NonVacuousOnBranches {α : Type} {m k : Nat} (sq : Sequent α m k)
    (branches : List (α → Prop)) : Prop :=
  branches ≠ [] ∧ ∀ b ∈ branches, ∃ x : α, b x ∧ AllCtx sq.ctxHyps x

/-- Tightness of domain context hypothesis `i` in `sq`. -/
def Sequent.TightCtxAt {α : Type} {m k : Nat} (sq : Sequent α m k) (i : Fin m) : Prop :=
  ∃ x : α, (∀ i' : Fin m, i' ≠ i → sq.ctxHyps i' x) ∧ AllBad sq.badHyps x ∧ ¬ sq.goal x

/-- Tightness of bad-event premise `j` in `sq`. -/
def Sequent.TightBadAt {α : Type} {m k : Nat} (sq : Sequent α m k) (j : Fin k) : Prop :=
  ∃ x : α, AllCtx sq.ctxHyps x ∧ (∀ j' : Fin k, j' ≠ j → sq.badHyps j' x) ∧ ¬ sq.goal x

/-- Every valid refutation sequent (`∀ x, sq.goal x ↔ False`) necessarily fails naive
`FullPremiseNonVacuous`, explaining why `ctxHyps` must be separated from `badHyps`. -/
theorem refutation_not_fullPremiseNonVacuous {α : Type} {m k : Nat} (sq : Sequent α m k)
    (href : ∀ x, sq.goal x ↔ False) (hholds : sq.Holds) :
    ¬ sq.FullPremiseNonVacuous := by
  rintro ⟨x, hctx, hbad⟩
  exact (href x).1 (hholds x hctx hbad)

/-- Tightness counterexample for `href : ∀ x, sq.goal x ↔ False` in `refutation_not_fullPremiseNonVacuous`:
a non-refutation sequent (`goal = True`) satisfies `Holds` and `FullPremiseNonVacuous` simultaneously. -/
theorem cex_refutation_not_fullPremise_without_href :
    let sq : Sequent Nat 1 1 := {
      ctxHyps := fun _ x => x < 5
      badHyps := fun _ x => x = 3
      goal := fun _ => True
    }
    sq.Holds ∧ sq.FullPremiseNonVacuous :=
  ⟨fun _ _ _ => trivial, ⟨3, fun _ => by omega, fun _ => rfl⟩⟩

/-- Tightness counterexample for `hholds : sq.Holds` in `refutation_not_fullPremiseNonVacuous`:
an invalid refutation sequent (`goal = False`, `¬ sq.Holds`) satisfies `FullPremiseNonVacuous`. -/
theorem cex_refutation_not_fullPremise_without_hholds :
    let sq : Sequent Nat 1 1 := {
      ctxHyps := fun _ x => x < 5
      badHyps := fun _ x => x = 3
      goal := fun _ => False
    }
    (∀ x, sq.goal x ↔ False) ∧ ¬ sq.Holds ∧ sq.FullPremiseNonVacuous :=
  ⟨fun _ => Iff.rfl, fun h => h 3 (fun _ => by omega) (fun _ => rfl),
   ⟨3, fun _ => by omega, fun _ => rfl⟩⟩

/-- Because `NonVacuousOnBranches` requires `branches ≠ []`, branch-level non-vacuity strictly
entails global `CtxNonVacuous`. -/
theorem nonVacuousOnBranches_implies_ctxNonVacuous {α : Type} {m k : Nat}
    (sq : Sequent α m k) (branches : List (α → Prop))
    (hnv : sq.NonVacuousOnBranches branches) :
    sq.CtxNonVacuous := by
  rcases branches with _ | ⟨b₀, bs⟩
  · exact False.elim (hnv.1 rfl)
  · obtain ⟨x, _, hctx⟩ := hnv.2 b₀ List.mem_cons_self
    exact ⟨x, hctx⟩

/-- Enforcing `NonVacuousOnBranches` rules out vacuous refutations on every listed branch (`k = 0`). -/
theorem branch_nonVacuous_blocks_vacuous_branch_false {α : Type} {m : Nat}
    (sq : Sequent α m 0) (branches : List (α → Prop)) (b : α → Prop)
    (hmem : b ∈ branches) (hnv : sq.NonVacuousOnBranches branches) :
    ¬ (∀ x : α, b x → AllCtx sq.ctxHyps x → False) := by
  intro hvac
  obtain ⟨x, hbx, hctx⟩ := hnv.2 b hmem
  exact hvac x hbx hctx

/-- Dead-branch sequent over `Sum Unit Unit` whose `ctxHyps` restricts to `.inl` only. -/
def deadRightBranchSequent : Sequent (Sum Unit Unit) 1 0 where
  ctxHyps := fun _ x => x.isLeft = true
  badHyps := fun j => Fin.elim0 j
  goal := fun x => x.isRight = true → False

/-- Canonical branch-local vacuity counterexample: `deadRightBranchSequent` is valid (`Holds`)
and globally `CtxNonVacuous` (witnessed on `Sum.inl ()`), yet its right branch `Sum.inr` is dead,
silently licensing `False` on `Sum.inr ()`, and `NonVacuousOnBranches` rejects it. -/
theorem cex_global_ctxNonVacuous_dead_right_branch :
    deadRightBranchSequent.Holds ∧
    deadRightBranchSequent.CtxNonVacuous ∧
    (∀ u : Unit, AllCtx deadRightBranchSequent.ctxHyps (.inr u) → False) ∧
    ¬ deadRightBranchSequent.NonVacuousOnBranches
        [fun x => x.isLeft = true, fun x => x.isRight = true] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hctx _ hright
    have hleft := hctx ⟨0, by omega⟩
    cases x <;> simp [deadRightBranchSequent] at hleft hright
  · exact ⟨.inl (), fun _ => rfl⟩
  · intro u hctx
    have hleft := hctx ⟨0, by omega⟩
    simp [deadRightBranchSequent] at hleft
  · intro hbr
    have hmem : (fun x : Sum Unit Unit => x.isRight = true) ∈
        [fun x => x.isLeft = true, fun x => x.isRight = true] :=
      List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)
    obtain ⟨x, hright, hctx⟩ := hbr.2 _ hmem
    have hleft := hctx ⟨0, by omega⟩
    cases x <;> simp [deadRightBranchSequent] at hleft hright

/-! ### Proved Positive and Negative Examples & Non-Vacuity Witness for `Sequent.lean` -/

/-- Valid refutation sequent over `Nat` (`ctx: x < 2`, `bad: x = 3`, `goal: False`). -/
def natBoundRefutation : Sequent Nat 1 1 where
  ctxHyps := fun _ x => x < 2
  badHyps := fun _ x => x = 3
  goal := fun _ => False

theorem allCtx_pos : AllCtx natBoundRefutation.ctxHyps 1 := fun _ => by simp [natBoundRefutation]
theorem allCtx_neg : ¬ AllCtx natBoundRefutation.ctxHyps 5 := by
  intro h; have := h ⟨0, by omega⟩; simp [natBoundRefutation] at this

theorem allBad_pos : AllBad natBoundRefutation.badHyps 3 := fun _ => rfl
theorem allBad_neg : ¬ AllBad natBoundRefutation.badHyps 1 := by
  intro h; have := h ⟨0, by omega⟩; simp [natBoundRefutation] at this

theorem sequent_holds_pos : natBoundRefutation.Holds := by
  intro x hctx hbad
  have hc := hctx ⟨0, by omega⟩
  have hb := hbad ⟨0, by omega⟩
  simp [natBoundRefutation] at hc hb
  omega

theorem sequent_holds_neg :
    ¬ ({ ctxHyps := fun _ x => x < 5, badHyps := fun _ x => x = 3, goal := fun _ => False } :
        Sequent Nat 1 1).Holds := by
  intro h
  exact h 3 (fun _ => by omega) (fun _ => rfl)

theorem ctxNonVacuous_pos : natBoundRefutation.CtxNonVacuous := ⟨0, fun _ => by simp [natBoundRefutation]⟩
theorem ctxNonVacuous_neg :
    ¬ ({ ctxHyps := fun _ _ => False, badHyps := fun _ _ => True, goal := fun _ => False } :
        Sequent Nat 1 1).CtxNonVacuous := by
  rintro ⟨_, h⟩; exact h ⟨0, by omega⟩

theorem fullPremiseNonVacuous_pos :
    ({ ctxHyps := fun _ x => x < 5, badHyps := fun _ x => x = 3, goal := fun x => x = 3 } :
      Sequent Nat 1 1).FullPremiseNonVacuous :=
  ⟨3, fun _ => by omega, fun _ => rfl⟩

theorem fullPremiseNonVacuous_neg : ¬ natBoundRefutation.FullPremiseNonVacuous :=
  refutation_not_fullPremiseNonVacuous natBoundRefutation (fun _ => Iff.rfl) sequent_holds_pos

theorem nonVacuousOnBranches_pos :
    ({ ctxHyps := fun _ _ => True, badHyps := Fin.elim0, goal := fun _ => True } :
      Sequent (Sum Unit Unit) 1 0).NonVacuousOnBranches
      [fun x => x.isLeft = true, fun x => x.isRight = true] := by
  refine ⟨by simp, ?_⟩
  intro b hb
  rcases List.mem_cons.1 hb with rfl | hb2
  · exact ⟨.inl (), rfl, fun _ => trivial⟩
  · rcases List.mem_singleton.1 hb2 with rfl
    exact ⟨.inr (), rfl, fun _ => trivial⟩

theorem nonVacuousOnBranches_neg :
    ¬ deadRightBranchSequent.NonVacuousOnBranches
        [fun x => x.isLeft = true, fun x => x.isRight = true] :=
  cex_global_ctxNonVacuous_dead_right_branch.2.2.2

theorem tightCtxAt_pos : natBoundRefutation.TightCtxAt ⟨0, by omega⟩ := by
  refine ⟨3, ?_, fun _ => rfl, id⟩
  intro ⟨i, hi⟩ hne
  exact False.elim (hne (Fin.ext (by omega)))

theorem tightCtxAt_neg :
    ¬ ({ ctxHyps := fun _ _ => True, badHyps := fun _ _ => False, goal := fun _ => False } :
        Sequent Nat 1 1).TightCtxAt ⟨0, by omega⟩ := by
  rintro ⟨_, _, hbad, _⟩
  exact hbad ⟨0, by omega⟩

theorem tightBadAt_pos : natBoundRefutation.TightBadAt ⟨0, by omega⟩ := by
  refine ⟨0, fun _ => by simp [natBoundRefutation], ?_, id⟩
  intro ⟨j, hj⟩ hne
  exact False.elim (hne (Fin.ext (by omega)))

theorem tightBadAt_neg :
    ¬ ({ ctxHyps := fun _ _ => False, badHyps := fun _ _ => True, goal := fun _ => False } :
        Sequent Nat 1 1).TightBadAt ⟨0, by omega⟩ := by
  rintro ⟨_, hctx, _, _⟩
  exact hctx ⟨0, by omega⟩

/-- Joint non-vacuity witness for `refutation_not_fullPremiseNonVacuous` and `NonVacuousOnBranches`. -/
theorem nonvacuity_sequent_refutation_and_branches :
    (∀ x, natBoundRefutation.goal x ↔ False) ∧
    natBoundRefutation.Holds ∧
    natBoundRefutation.CtxNonVacuous ∧
    ({ ctxHyps := fun _ _ => True, badHyps := Fin.elim0, goal := fun _ => True } :
      Sequent (Sum Unit Unit) 1 0).NonVacuousOnBranches
      [fun x => x.isLeft = true, fun x => x.isRight = true] :=
  ⟨fun _ => Iff.rfl, sequent_holds_pos, ctxNonVacuous_pos, nonVacuousOnBranches_pos⟩

end Toy.BoundaryLicensing
