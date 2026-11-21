import ToyDrat.RupRat

/-!
# Clausal certificates (DRAT-style): additions, deletions, and checker soundness

A certificate is a list of steps, each adding or deleting a clause. A refutation
checker replays the steps against a current formula; each addition must pass an
addition check (RUP or RAT for DRAT, RUP only for DRUP), deletions are applied
according to a *deletion policy*, and the certificate is accepted as soon as the
empty clause is added and passes its check.

The deletion policy models the difference between *specified* DRAT (every deletion is
applied) and the *operational* variant implemented by common checkers, which ignore
deletions of unit clauses. In this toy model the operational policy ignores deletions of
syntactically unit clauses (list length one); production checkers deduplicate literals
first and also ignore deletions of clauses that are reasons for top-level assignments, a
history-dependent rule. A `DeletionPolicy` is a stateless function of the current formula
and the deleted clause.

Deletion (`deleteClause`) removes every copy of the clause that is syntactically equal as a
list. The DRAT format treats formulas as multisets and removes one copy per deletion step,
matched up to literal order; `one_copy_deletion_breaks_drup_monotonicity` and
`permuted_deletion_is_ignored` show where this difference changes conclusions.
-/

namespace Toy.Drat

/-- A certificate step. -/
inductive Step where
  | add (C : Clause)
  | del (C : Clause)
  deriving DecidableEq, Repr

/-- Delete every occurrence of clause `C` (syntactic equality). -/
def deleteClause (F : Formula) (C : Clause) : Formula := F.filter (fun D => decide (D ≠ C))

/-- A deletion policy: `ignore F C = true` means the checker skips the deletion of `C`
from the current formula `F`. -/
abbrev DeletionPolicy := Formula → Clause → Bool

/-- Apply a deletion step under a policy. -/
def applyDel (ignore : DeletionPolicy) (F : Formula) (C : Clause) : Formula :=
  if ignore F C then F else deleteClause F C

/-- Generic refutation checker, parameterized by the addition check and the deletion
policy. Accepts iff some addition of the empty clause passes the addition check, every
earlier addition passed it, and deletions were processed according to the policy. Steps
after the first accepted empty clause are not examined, and the empty certificate is
rejected even when `F` already contains the empty clause. -/
def checkGen (addCheck : Formula → Clause → Bool) (ignore : DeletionPolicy) :
    Formula → List Step → Bool
  | _, [] => false
  | F, .del C :: π => checkGen addCheck ignore (applyDel ignore F C) π
  | F, .add C :: π => addCheck F C && (C.isEmpty || checkGen addCheck ignore (C :: F) π)

/-- DRAT addition check with propagation budget `fuel`: RUP, or else RAT on the first
literal. -/
def addOK (fuel : Nat) (F : Formula) (C : Clause) : Bool := rupCheck fuel F C || ratCheck fuel F C

/-- DRAT refutation checker. -/
def checkDRAT (fuel : Nat) (ignore : DeletionPolicy) : Formula → List Step → Bool :=
  checkGen (addOK fuel) ignore

/-- DRUP refutation checker (additions must be RUP). -/
def checkDRUP (fuel : Nat) (ignore : DeletionPolicy) : Formula → List Step → Bool :=
  checkGen (rupCheck fuel) ignore

/-- Policy that applies every deletion ("specified" DRAT). -/
def honorAll : DeletionPolicy := fun _ _ => false

/-- Policy that ignores deletions of unit clauses ("operational" DRAT, toy version:
syntactic unit clauses). -/
def ignoreUnitDeletions : DeletionPolicy := fun _ C => decide (C.length = 1)

/-- Specified DRAT checker: every deletion is applied. -/
def checkSpecified (fuel : Nat) : Formula → List Step → Bool := checkDRAT fuel honorAll

/-- Operational DRAT checker: deletions of unit clauses are ignored. -/
def checkOperational (fuel : Nat) : Formula → List Step → Bool :=
  checkDRAT fuel ignoreUnitDeletions

/-- Replay a certificate without looking for the empty clause; `none` if some addition
fails its check. Returns the formula reached at the end. -/
def replay (addCheck : Formula → Clause → Bool) (ignore : DeletionPolicy) :
    Formula → List Step → Option Formula
  | F, [] => some F
  | F, .del C :: π => replay addCheck ignore (applyDel ignore F C) π
  | F, .add C :: π => if addCheck F C then replay addCheck ignore (C :: F) π else none

/-- A *naive* satisfiability checker: replay the certificate with the DRAT addition check
and all deletions applied *without any check on the deleted clauses*, then test the claimed
model against the formula reached at the end (not against the original formula). -/
def naiveSatCheck (fuel : Nat) (F : Formula) (π : List Step) (a : Assignment) : Bool :=
  match replay (addOK fuel) honorAll F π with
  | some G => G.eval a
  | none => false

/-- The certificate contains no deletion step. -/
def NoDeletions (π : List Step) : Prop := ∀ s ∈ π, ∃ C, s = .add C

/-! ## Step lemmas -/

theorem deleteClause_sub (F : Formula) (C : Clause) : FormulaSub (deleteClause F C) F := by
  intro D hD
  exact (List.mem_filter.1 hD).1

theorem applyDel_sub (ignore : DeletionPolicy) (F : Formula) (C : Clause) :
    FormulaSub (applyDel ignore F C) F := by
  unfold applyDel
  split
  · exact fun _ h => h
  · exact deleteClause_sub F C

/-- Deletion (under any policy) preserves satisfiability *forwards*. -/
theorem applyDel_preserves_satisfiability {ignore : DeletionPolicy} {F : Formula} {C : Clause}
    (h : Satisfiable F) : Satisfiable (applyDel ignore F C) :=
  let ⟨a, ha⟩ := h
  ⟨a, Satisfies_of_subset (applyDel_sub ignore F C) ha⟩

/-- A DRAT addition (RUP, or RAT on the first literal) preserves satisfiability forwards. -/
theorem addOK_preserves_satisfiability {fuel : Nat} {F : Formula} {C : Clause}
    (h : addOK fuel F C = true) (hF : Satisfiable F) : Satisfiable (C :: F) := by
  rcases Bool.or_eq_true_iff.1 h with h | h
  · obtain ⟨a, ha⟩ := hF
    exact ⟨a, (rup_addition_preserves_equivalence (rupCheck_sound h) a).2 ha⟩
  · exact rat_addition_preserves_satisfiability (ratCheck_sound h) hF

/-! ## Refutation soundness -/

/-- **Refutation soundness, generic form.** If the addition check preserves satisfiability
(`addCheck F C = true → Satisfiable F → Satisfiable (C :: F)`), then for *every* deletion
policy, a certificate accepted by `checkGen` refutes the original formula. Each step
maps satisfiable formulas to satisfiable formulas, and the final formula contains the
empty clause. -/
theorem checkGen_sound_unsat_of_addCheck_preserves_sat
    (addCheck : Formula → Clause → Bool) (ignore : DeletionPolicy)
    (hpres : ∀ F C, addCheck F C = true → Satisfiable F → Satisfiable (C :: F)) :
    ∀ (π : List Step) (F : Formula), checkGen addCheck ignore F π = true → ¬ Satisfiable F := by
  intro π
  induction π with
  | nil => intro F h; simp [checkGen] at h
  | cons s π ih =>
    intro F h hF
    cases s with
    | del C =>
      exact ih _ (by simpa [checkGen] using h) (applyDel_preserves_satisfiability hF)
    | add C =>
      simp only [checkGen, Bool.and_eq_true, Bool.or_eq_true] at h
      obtain ⟨hadd, hrest⟩ := h
      have hCF := hpres F C hadd hF
      rcases hrest with hnil | hrest
      · have : C = [] := List.isEmpty_iff.1 hnil
        subst this
        exact not_satisfiable_of_nil_mem List.mem_cons_self hCF
      · exact ih _ hrest hCF

/-- **DRAT refutation soundness.** For every propagation budget and every deletion policy,
if the DRAT checker accepts a certificate for `F` then `F` is unsatisfiable. -/
theorem checkDRAT_sound_unsat (fuel : Nat) (ignore : DeletionPolicy) (F : Formula)
    (π : List Step) (h : checkDRAT fuel ignore F π = true) : ¬ Satisfiable F :=
  checkGen_sound_unsat_of_addCheck_preserves_sat (addOK fuel) ignore
    (fun _ _ h hF => addOK_preserves_satisfiability h hF) π F h

/-- Without a satisfiability-preserving addition check the generic checker is unsound: the
check that accepts everything does not preserve satisfiability, and with it the one-step
certificate "add the empty clause" is accepted for the satisfiable empty formula. -/
theorem checkGen_unchecked_additions_unsound :
    (¬ ∀ F C, (fun _ _ => true : Formula → Clause → Bool) F C = true →
        Satisfiable F → Satisfiable (C :: F)) ∧
      checkGen (fun _ _ => true) honorAll [] [.add []] = true ∧ Satisfiable [] := by
  refine ⟨fun hpres => ?_, rfl, ⟨fun _ => true, rfl⟩⟩
  exact not_satisfiable_of_nil_mem List.mem_cons_self (hpres [] [] rfl ⟨fun _ => true, rfl⟩)

/-- Every clause is RUP w.r.t. a formula that contains the empty clause, at every budget. In
particular, additions placed after an accepted empty clause (which `checkGen` does not
examine) would all pass the RUP check. -/
theorem rupCheck_of_nil_mem {fuel : Nat} {F : Formula} {C : Clause} (h : [] ∈ F) :
    rupCheck fuel F C = true := by
  have hc : hasConflict F (negClause C) = true := by
    simp only [hasConflict, Bool.or_eq_true, List.any_eq_true, List.all_eq_true]
    exact Or.inr ⟨[], h, fun _ hl => absurd hl List.not_mem_nil⟩
  cases fuel <;> simp [rupCheck, unitProp, hc]

/-- The empty certificate is rejected, even for a formula that contains the empty clause. -/
theorem checkGen_empty_certificate (addCheck : Formula → Clause → Bool) (ignore : DeletionPolicy)
    (F : Formula) : checkGen addCheck ignore F [] = false := rfl

/-- Non-vacuity: the specified DRAT checker (budget 3) accepts the refutation
"add `x₁`, add the empty clause" of `fullSquare`. -/
theorem checkSpecified_fullSquare : checkSpecified 3 fullSquare [.add [Lit.p 1], .add []] = true := by
  decide

/-! ## Deletions and SAT claims -/

/-- **Deletion can turn an unsatisfiable formula into a satisfiable one.** -/
theorem deletion_can_turn_unsat_into_sat :
    ¬ Satisfiable [[Lit.p 0], [Lit.n 0]] ∧ Satisfiable (deleteClause [[Lit.p 0], [Lit.n 0]] [Lit.p 0]) :=
  ⟨Satisfiable_example_neg, ⟨fun _ => false, by decide⟩⟩

/-- **A SAT verdict read off the formula reached after unchecked deletions is unsound.** The
certificate "delete `x₀`" contains a deletion, and for every budget `naiveSatCheck` (which
applies deletions without checking them) accepts the all-false assignment for the
unsatisfiable formula `x₀ ∧ ¬x₀`. -/
theorem naiveSatCheck_unsound_with_deletions :
    ¬ NoDeletions [.del [Lit.p 0]] ∧
      (∀ fuel, naiveSatCheck fuel [[Lit.p 0], [Lit.n 0]] [.del [Lit.p 0]] (fun _ => false) = true) ∧
      ¬ Satisfiable [[Lit.p 0], [Lit.n 0]] := by
  refine ⟨fun h => ?_, fun _ => rfl, Satisfiable_example_neg⟩
  obtain ⟨C, hC⟩ := h (.del [Lit.p 0]) List.mem_cons_self
  cases hC

theorem replay_sub_of_noDeletions (addCheck : Formula → Clause → Bool) (ignore : DeletionPolicy) :
    ∀ (π : List Step) (F G : Formula), NoDeletions π → replay addCheck ignore F π = some G →
      FormulaSub F G := by
  intro π
  induction π with
  | nil => intro F G _ h; simp [replay] at h; subst h; exact fun _ h => h
  | cons s π ih =>
    intro F G hnd h
    obtain ⟨C, rfl⟩ := hnd s List.mem_cons_self
    simp only [replay] at h
    split at h
    · have := ih (C :: F) G (fun s hs => hnd s (List.mem_cons_of_mem _ hs)) h
      exact fun D hD => this D (List.mem_cons_of_mem _ hD)
    · simp at h

/-- Positive control for `naiveSatCheck_unsound_with_deletions`: on deletion-free
certificates the naive SAT check is sound, because the final formula contains every
original clause. -/
theorem naiveSatCheck_sound_of_noDeletions {fuel : Nat} {F : Formula} {π : List Step}
    {a : Assignment} (hnd : NoDeletions π) (h : naiveSatCheck fuel F π a = true) :
    Satisfies a F := by
  unfold naiveSatCheck at h
  split at h
  · rename_i G hG
    exact Satisfies_of_subset (replay_sub_of_noDeletions _ _ π F G hnd hG) h
  · simp at h

/-- Deletion-free replay carries models backwards for *any* addition check and *any* deletion
policy: a model of the final formula is a model of the original one. -/
theorem replay_model_sound_of_noDeletions {addCheck : Formula → Clause → Bool}
    {ignore : DeletionPolicy} {π : List Step} {F G : Formula} {a : Assignment}
    (hnd : NoDeletions π) (hrep : replay addCheck ignore F π = some G) (ha : Satisfies a G) :
    Satisfies a F :=
  Satisfies_of_subset (replay_sub_of_noDeletions addCheck ignore π F G hnd hrep) ha

/-! ## Checked deletions -/

/-- Replay in which every deletion of `C` from the current formula `F` must pass
`rupCheck fuel (deleteClause F C) C` (the deleted clause is RUP w.r.t. the formula without
it) and every addition must pass `addOK fuel`; `none` if some check fails. -/
def replayRupDel (fuel : Nat) : Formula → List Step → Option Formula
  | F, [] => some F
  | F, .del C :: π =>
    if rupCheck fuel (deleteClause F C) C then replayRupDel fuel (deleteClause F C) π else none
  | F, .add C :: π => if addOK fuel F C then replayRupDel fuel (C :: F) π else none

/-- SAT check against the final formula of `replayRupDel` (RUP-checked deletions). -/
def satCheckRupDel (fuel : Nat) (F : Formula) (π : List Step) (a : Assignment) : Bool :=
  match replayRupDel fuel F π with
  | some G => G.eval a
  | none => false

/-- Replay in which every deletion of `C` from the current formula `F` must pass the DRAT
addition check `addOK fuel (deleteClause F C) C` (RUP, or RAT on the first literal, w.r.t.
the formula without it) and every addition must pass `addOK fuel`. -/
def replayRatDel (fuel : Nat) : Formula → List Step → Option Formula
  | F, [] => some F
  | F, .del C :: π =>
    if addOK fuel (deleteClause F C) C then replayRatDel fuel (deleteClause F C) π else none
  | F, .add C :: π => if addOK fuel F C then replayRatDel fuel (C :: F) π else none

theorem sub_cons_deleteClause (F : Formula) (C : Clause) :
    FormulaSub F (C :: deleteClause F C) := by
  intro D hD
  by_cases h : D = C
  · subst h; exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_filter.2 ⟨hD, by simpa using h⟩)

theorem replayRupDel_model_backward (fuel : Nat) :
    ∀ (π : List Step) (F G : Formula) (a : Assignment),
      replayRupDel fuel F π = some G → Satisfies a G → Satisfies a F := by
  intro π
  induction π with
  | nil => intro F G a h ha; simp [replayRupDel] at h; subst h; exact ha
  | cons s π ih =>
    intro F G a h ha
    cases s with
    | del C =>
      simp only [replayRupDel] at h
      split at h
      · rename_i hrup
        have haF' := ih _ G a h ha
        have hC := rup_implies_entails (rupCheck_sound hrup) a haF'
        exact Satisfies_of_subset (sub_cons_deleteClause F C)
          ((Satisfies_cons _ _ _).2 ⟨hC, haF'⟩)
      · simp at h
    | add C =>
      simp only [replayRupDel] at h
      split at h
      · exact ((Satisfies_cons _ _ _).1 (ih _ G a h ha)).2
      · simp at h

/-- **RUP-checked deletions make the final-formula SAT check sound.** If every deletion is
checked to be RUP w.r.t. the formula without the deleted clause, a model of the final formula
is a model of the original formula. -/
theorem satCheckRupDel_sound {fuel : Nat} {F : Formula} {π : List Step} {a : Assignment}
    (h : satCheckRupDel fuel F π a = true) : Satisfies a F := by
  unfold satCheckRupDel at h
  split at h
  · rename_i G hG
    exact replayRupDel_model_backward fuel π F G a hG h
  · simp at h

/-- **RAT-checked deletions carry satisfiability backwards.** If every deletion is checked
with the DRAT addition check w.r.t. the formula without the deleted clause, satisfiability
of the final formula implies satisfiability of the original formula. (A model of the final
formula need not be a model of the original one: `replayRatDel_final_model_not_original`.) -/
theorem replayRatDel_sat_backward (fuel : Nat) :
    ∀ (π : List Step) (F G : Formula),
      replayRatDel fuel F π = some G → Satisfiable G → Satisfiable F := by
  intro π
  induction π with
  | nil => intro F G h hG; simp [replayRatDel] at h; subst h; exact hG
  | cons s π ih =>
    intro F G h hG
    cases s with
    | del C =>
      simp only [replayRatDel] at h
      split at h
      · rename_i hok
        obtain ⟨a, ha⟩ := addOK_preserves_satisfiability hok (ih _ G h hG)
        exact ⟨a, Satisfies_of_subset (sub_cons_deleteClause F C) ha⟩
      · simp at h
    | add C =>
      simp only [replayRatDel] at h
      split at h
      · obtain ⟨a, ha⟩ := ih _ G h hG
        exact ⟨a, ((Satisfies_cons _ _ _).1 ha).2⟩
      · simp at h

/-- With RAT-checked deletions, a model of the final formula need not be a model of the
original formula. Deleting the blocked clause `x₀ ∨ ¬x₁` from `(x₀ ∨ ¬x₁) ∧ (¬x₀ ∨ x₁)`
passes the RAT check (not the RUP check, so `replayRupDel` rejects at every budget); the
assignment `x₀ = false, x₁ = true` satisfies the final formula but not the original one,
and `ratWitness` turns it into a model of the original formula. -/
theorem replayRatDel_final_model_not_original :
    replayRatDel 0 [[Lit.p 0, Lit.n 1], [Lit.n 0, Lit.p 1]] [.del [Lit.p 0, Lit.n 1]] =
        some [[Lit.n 0, Lit.p 1]] ∧
      (∀ fuel, replayRupDel fuel [[Lit.p 0, Lit.n 1], [Lit.n 0, Lit.p 1]]
        [.del [Lit.p 0, Lit.n 1]] = none) ∧
      Satisfies (fun v => v == 1) [[Lit.n 0, Lit.p 1]] ∧
      ¬ Satisfies (fun v => v == 1) [[Lit.p 0, Lit.n 1], [Lit.n 0, Lit.p 1]] ∧
      Satisfies (ratWitness (fun v => v == 1) [Lit.p 0, Lit.n 1] (Lit.p 0))
        [[Lit.p 0, Lit.n 1], [Lit.n 0, Lit.p 1]] := by
  have hdel : deleteClause [[Lit.p 0, Lit.n 1], [Lit.n 0, Lit.p 1]] [Lit.p 0, Lit.n 1] =
      [[Lit.n 0, Lit.p 1]] := by decide
  have hr : ∀ fuel, rupCheck fuel [[Lit.n 0, Lit.p 1]] [Lit.p 0, Lit.n 1] = false := by
    intro fuel
    cases h : rupCheck fuel [[Lit.n 0, Lit.p 1]] [Lit.p 0, Lit.n 1] with
    | false => rfl
    | true =>
      exact absurd (rup_implies_entails (rupCheck_sound h)) RAT_example_pos_not_entailed
  refine ⟨by decide, fun fuel => ?_, by decide, by decide, by decide⟩
  simp only [replayRupDel, hdel, hr, Bool.false_eq_true, ↓reduceIte]

/-- **RAT after deletion is not RAT w.r.t. the original formula.** Starting from the
satisfiable formula `¬x₀`, the certificate "delete `¬x₀`, add `x₀`" replays successfully
(`x₀` is RAT w.r.t. the empty formula), but `x₀` is neither RUP nor RAT w.r.t. the
original formula, and the original formula together with the added clause is
unsatisfiable. -/
theorem rat_after_deletion_not_rat_wrt_original :
    replay (addOK 0) honorAll [[Lit.n 0]] [.del [Lit.n 0], .add [Lit.p 0]] = some [[Lit.p 0]] ∧
      ¬ RUP [[Lit.n 0]] [Lit.p 0] ∧ ¬ RAT [[Lit.n 0]] [Lit.p 0] ∧
      Satisfiable [[Lit.n 0]] ∧ ¬ Satisfiable [[Lit.p 0], [Lit.n 0]] := by
  refine ⟨by decide, ?_, RAT_example_neg, ⟨fun _ => false, by decide⟩, Satisfiable_example_neg⟩
  exact not_rup_of_neverConflict (neverConflict_of_closed (by decide) (by decide))

/-! ## Ignoring unit deletions -/


/-- Operational DRAT soundness: ignoring unit deletions keeps refutations sound. -/
theorem checkOperational_sound_unsat (fuel : Nat) (F : Formula) (π : List Step)
    (h : checkOperational fuel F π = true) : ¬ Satisfiable F :=
  checkDRAT_sound_unsat fuel ignoreUnitDeletions F π h

/-- **Operational acceptance does not imply specified acceptance.** For `x₀ ∧ ¬x₀` and the
certificate "delete `x₀`, add the empty clause", the operational checkers (DRAT and DRUP)
accept, while the specified checkers reject at every budget. -/
theorem operational_accepts_specified_rejects :
    checkOperational 1 [[Lit.p 0], [Lit.n 0]] [.del [Lit.p 0], .add []] = true ∧
      (∀ fuel, checkSpecified fuel [[Lit.p 0], [Lit.n 0]] [.del [Lit.p 0], .add []] = false) ∧
      checkDRUP 1 ignoreUnitDeletions [[Lit.p 0], [Lit.n 0]] [.del [Lit.p 0], .add []] = true ∧
      (∀ fuel, checkDRUP fuel honorAll [[Lit.p 0], [Lit.n 0]] [.del [Lit.p 0], .add []] = false) := by
  have hdel : applyDel honorAll [[Lit.p 0], [Lit.n 0]] [Lit.p 0] = [[Lit.n 0]] := by decide
  have hrup : ∀ fuel, rupCheck fuel [[Lit.n 0]] [] = false := fun _ =>
    rupCheck_eq_false_of_neverConflict
      (neverConflict_of_step (by decide) (neverConflict_of_closed (by decide) (by decide)))
  refine ⟨by decide, fun fuel => ?_, by decide, fun fuel => ?_⟩
  · simp only [checkSpecified, checkDRAT, checkGen, hdel, addOK, hrup, ratCheck,
      Bool.or_false, Bool.false_and]
  · simp only [checkDRUP, checkGen, hdel, hrup, Bool.false_and]

/-- `¬x₀` together with `fullSquare` (unsatisfiable, no unit propagation conflict). -/
def unitPlusSquare : Formula := [Lit.n 0] :: fullSquare

/-- The certificate "delete `¬x₀`, add `x₀`, add `x₁`, add the empty clause". -/
def unitDeletionThenRAT : List Step := [.del [Lit.n 0], .add [Lit.p 0], .add [Lit.p 1], .add []]

/-- **Specified acceptance does not imply operational acceptance (DRAT).** The specified
checker accepts `unitDeletionThenRAT` for `unitPlusSquare` (after the deletion, `x₀` is RAT
because no clause contains `¬x₀`), while the operational checker, which keeps `¬x₀`,
rejects at every budget: `x₀` is then neither RUP nor RAT. -/
theorem specified_accepts_operational_rejects :
    checkSpecified 3 unitPlusSquare unitDeletionThenRAT = true ∧
      ∀ fuel, checkOperational fuel unitPlusSquare unitDeletionThenRAT = false := by
  refine ⟨by decide, fun fuel => ?_⟩
  have hnc : NeverConflict unitPlusSquare (negClause [Lit.p 0]) :=
    neverConflict_of_closed (by decide) (by decide)
  have hrup : rupCheck fuel unitPlusSquare [Lit.p 0] = false :=
    rupCheck_eq_false_of_neverConflict hnc
  have hres : resolventOn [Lit.p 0] [Lit.n 0] (Lit.p 0) = [Lit.p 0] := by decide
  have hrat : ratCheck fuel unitPlusSquare [Lit.p 0] = false :=
    ratCheck_eq_false_of (D := [Lit.n 0]) (by simp [unitPlusSquare]) (by decide)
      (by rw [hres]; exact hrup)
  have hkeep : applyDel ignoreUnitDeletions unitPlusSquare [Lit.n 0] = unitPlusSquare := by
    decide
  simp only [checkOperational, checkDRAT, unitDeletionThenRAT, checkGen, hkeep, addOK, hrup,
    hrat, Bool.or_false, Bool.false_and]

/-- **DRAT acceptance is not monotone in the formula.** The specified checker accepts
"add `x₀`, add `x₁`, add the empty clause" for `fullSquare` (`x₀` is RAT because no clause
contains `¬x₀`), but rejects it at every budget for `unitPlusSquare`, which contains every
clause of `fullSquare` and also `¬x₀`. (Contrast `checkDRUP_honorAll_implies_any_policy`.) -/
theorem drat_certificate_not_monotone_in_formula :
    checkSpecified 3 fullSquare [.add [Lit.p 0], .add [Lit.p 1], .add []] = true ∧
      FormulaSub fullSquare unitPlusSquare ∧
      ∀ fuel, checkSpecified fuel unitPlusSquare [.add [Lit.p 0], .add [Lit.p 1], .add []] = false := by
  refine ⟨by decide, fun D hD => List.mem_cons_of_mem _ hD, fun fuel => ?_⟩
  have hnc : NeverConflict unitPlusSquare (negClause [Lit.p 0]) :=
    neverConflict_of_closed (by decide) (by decide)
  have hrup : rupCheck fuel unitPlusSquare [Lit.p 0] = false :=
    rupCheck_eq_false_of_neverConflict hnc
  have hres : resolventOn [Lit.p 0] [Lit.n 0] (Lit.p 0) = [Lit.p 0] := by decide
  have hrat : ratCheck fuel unitPlusSquare [Lit.p 0] = false :=
    ratCheck_eq_false_of (D := [Lit.n 0]) (by simp [unitPlusSquare]) (by decide)
      (by rw [hres]; exact hrup)
  simp only [checkSpecified, checkDRAT, checkGen, addOK, hrup, hrat, Bool.or_false,
    Bool.false_and]

/-- **For RUP-only certificates, honoring every deletion is the strictest policy.** If the
DRUP checker that applies every deletion accepts a certificate for `F`, then the DRUP
checker with *any* deletion policy accepts it for any `G ⊇ F` (in particular for `F`
itself with the unit-ignoring policy). -/
theorem checkDRUP_honorAll_implies_any_policy (fuel : Nat) (ignore : DeletionPolicy) :
    ∀ (π : List Step) (F G : Formula), FormulaSub F G →
      checkDRUP fuel honorAll F π = true → checkDRUP fuel ignore G π = true := by
  intro π
  induction π with
  | nil => intro F G _ h; simp [checkDRUP, checkGen] at h
  | cons s π ih =>
    intro F G hFG h
    cases s with
    | del C =>
      simp only [checkDRUP, checkGen] at h ⊢
      refine ih _ _ ?_ h
      intro D hD
      simp only [applyDel, honorAll, Bool.false_eq_true, ↓reduceIte, deleteClause,
        List.mem_filter, decide_eq_true_eq] at hD
      unfold applyDel
      split
      · exact hFG D hD.1
      · exact List.mem_filter.2 ⟨hFG D hD.1, by simpa using hD.2⟩
    | add C =>
      simp only [checkDRUP, checkGen, Bool.and_eq_true, Bool.or_eq_true] at h ⊢
      obtain ⟨hadd, hrest⟩ := h
      refine ⟨rupCheck_mono_formula hFG hadd, ?_⟩
      rcases hrest with hnil | hrest
      · exact Or.inl hnil
      · refine Or.inr (ih (C :: F) (C :: G) ?_ hrest)
        intro D hD
        rcases List.mem_cons.1 hD with rfl | hD
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hFG D hD)

/-- Corollary: specified DRUP acceptance implies operational DRUP acceptance. -/
theorem checkDRUP_specified_implies_operational (fuel : Nat) (F : Formula) (π : List Step)
    (h : checkDRUP fuel honorAll F π = true) : checkDRUP fuel ignoreUnitDeletions F π = true :=
  checkDRUP_honorAll_implies_any_policy fuel ignoreUnitDeletions π F F (fun _ h => h) h

/-! ## Deletion semantics: one copy, literal order -/

/-- Delete the first copy of `C` (syntactic equality), as in the multiset reading of DRAT. -/
def deleteOneCopy : Formula → Clause → Formula
  | [], _ => []
  | D :: F, C => if D = C then F else D :: deleteOneCopy F C

/-- DRUP checker that applies every deletion, removing one copy per deletion step. -/
def checkDRUPOneCopy (fuel : Nat) : Formula → List Step → Bool
  | _, [] => false
  | F, .del C :: π => checkDRUPOneCopy fuel (deleteOneCopy F C) π
  | F, .add C :: π => rupCheck fuel F C && (C.isEmpty || checkDRUPOneCopy fuel (C :: F) π)

/-- **The `FormulaSub` form of `checkDRUP_honorAll_implies_any_policy` fails for one-copy
deletion.** `F` has two copies of `x₀`; `G` contains every clause of `F` but only one copy of
`x₀`. With one-copy deletion the certificate "delete `x₀`, add the empty clause" is accepted
for `F` and rejected for `G` at every budget. -/
theorem one_copy_deletion_breaks_drup_monotonicity :
    FormulaSub [[Lit.p 0], [Lit.p 0], [Lit.n 0]] [[Lit.p 0], [Lit.n 0]] ∧
      checkDRUPOneCopy 1 [[Lit.p 0], [Lit.p 0], [Lit.n 0]] [.del [Lit.p 0], .add []] = true ∧
      ∀ fuel, checkDRUPOneCopy fuel [[Lit.p 0], [Lit.n 0]] [.del [Lit.p 0], .add []] = false := by
  have hdel : deleteOneCopy [[Lit.p 0], [Lit.n 0]] [Lit.p 0] = [[Lit.n 0]] := by decide
  have hrup : ∀ fuel, rupCheck fuel [[Lit.n 0]] [] = false := fun _ =>
    rupCheck_eq_false_of_neverConflict
      (neverConflict_of_step (by decide) (neverConflict_of_closed (by decide) (by decide)))
  refine ⟨?_, by decide, fun fuel => ?_⟩
  · intro D hD
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hD
    rcases hD with rfl | rfl | rfl <;> simp
  · simp only [checkDRUPOneCopy, hdel, hrup, Bool.false_and]

/-- **A deletion whose literals are permuted is ignored.** `deleteClause` matches clauses as
lists, so "delete `x₁ ∨ x₀`" leaves the stored clause `x₀ ∨ x₁` in place, and the specified
checker accepts "delete `x₁ ∨ x₀`, add the empty clause" for `(x₀ ∨ x₁) ∧ ¬x₀ ∧ ¬x₁`. Had the
deletion removed `x₀ ∨ x₁` (matching up to literal order), the remaining formula
`¬x₀ ∧ ¬x₁` with the certificate "add the empty clause" would be rejected at every budget. -/
theorem permuted_deletion_is_ignored :
    deleteClause [[Lit.p 0, Lit.p 1], [Lit.n 0], [Lit.n 1]] [Lit.p 1, Lit.p 0] =
        [[Lit.p 0, Lit.p 1], [Lit.n 0], [Lit.n 1]] ∧
      checkSpecified 2 [[Lit.p 0, Lit.p 1], [Lit.n 0], [Lit.n 1]]
        [.del [Lit.p 1, Lit.p 0], .add []] = true ∧
      ∀ fuel, checkSpecified fuel [[Lit.n 0], [Lit.n 1]] [.add []] = false := by
  have hrup : ∀ fuel, rupCheck fuel [[Lit.n 0], [Lit.n 1]] [] = false := fun _ =>
    rupCheck_eq_false_of_neverConflict
      (neverConflict_of_step (by decide) (neverConflict_of_closed (by decide) (by decide)))
  refine ⟨by decide, by decide, fun fuel => ?_⟩
  simp only [checkSpecified, checkDRAT, checkGen, addOK, hrup, ratCheck, Bool.or_false,
    Bool.false_and]

/-! ## Examples -/

section Examples

/-- Positive example of `deleteClause`: removes exactly the matching clause. -/
theorem deleteClause_example_pos :
    deleteClause [[Lit.p 0], [Lit.n 0], [Lit.p 0]] [Lit.p 0] = [[Lit.n 0]] := by decide

/-- Negative example of `deleteClause`: a permuted clause is not matched (syntactic match). -/
theorem deleteClause_example_neg :
    deleteClause [[Lit.p 0, Lit.p 1]] [Lit.p 1, Lit.p 0] = [[Lit.p 0, Lit.p 1]] := by decide

/-- Positive example of `ignoreUnitDeletions`: a unit clause deletion is ignored. -/
theorem ignoreUnitDeletions_example_pos : ignoreUnitDeletions [] [Lit.p 0] = true := rfl

/-- Negative example of `ignoreUnitDeletions`: a binary clause deletion is applied. -/
theorem ignoreUnitDeletions_example_neg : ignoreUnitDeletions [] [Lit.p 0, Lit.p 1] = false := rfl

/-- Example: `ignoreUnitDeletions` tests list length, so the deletion of `x₀ ∨ x₀` (a unit
clause after removing the duplicate literal) is applied, not ignored. -/
theorem ignoreUnitDeletions_example_dup : ignoreUnitDeletions [] [Lit.p 0, Lit.p 0] = false := rfl

/-- Positive example of `NoDeletions`. -/
theorem NoDeletions_example_pos : NoDeletions [.add [Lit.p 0], .add []] := by
  intro s hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact ⟨[Lit.p 0], rfl⟩
  · exact ⟨[], rfl⟩

/-- Negative example of `NoDeletions`. -/
theorem NoDeletions_example_neg : ¬ NoDeletions [.del [Lit.p 0]] :=
  naiveSatCheck_unsound_with_deletions.1

/-- Positive example of `addOK`: a RAT-but-not-RUP clause passes. -/
theorem addOK_example_pos : addOK 2 [[Lit.n 0, Lit.p 1]] [Lit.p 0, Lit.n 1] = true := by decide

/-- Negative example of `addOK`: `x₀` does not pass w.r.t. `¬x₀`. -/
theorem addOK_example_neg : addOK 2 [[Lit.n 0]] [Lit.p 0] = false := by decide

/-- Negative example of `checkSpecified`: a certificate that never adds the empty clause
is rejected, even for an unsatisfiable formula. -/
theorem checkSpecified_example_neg : checkSpecified 3 fullSquare [.add [Lit.p 1]] = false := by
  decide

/-- Positive example of `replay`: adding a RUP clause. -/
theorem replay_example_pos :
    replay (addOK 1) honorAll [[Lit.p 0], [Lit.n 0, Lit.p 1]] [.add [Lit.p 1]] =
      some [[Lit.p 1], [Lit.p 0], [Lit.n 0, Lit.p 1]] := by decide

/-- Negative example of `replay`: an unjustified addition stops the replay. -/
theorem replay_example_neg : replay (addOK 2) honorAll [[Lit.n 0]] [.add [Lit.p 0]] = none := by
  decide

/-- Positive example of `naiveSatCheck` on a deletion-free certificate. -/
theorem naiveSatCheck_example_pos :
    naiveSatCheck 1 [[Lit.p 0, Lit.p 1]] [] (fun v => v == 1) = true := by decide

/-- Negative example of `naiveSatCheck`: a non-model is rejected. -/
theorem naiveSatCheck_example_neg :
    naiveSatCheck 1 [[Lit.p 0, Lit.p 1]] [] (fun _ => false) = false := by decide

end Examples

end Toy.Drat
