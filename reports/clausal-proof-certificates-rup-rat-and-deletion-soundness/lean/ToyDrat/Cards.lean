import ToyDrat.Lrat

/-!
# Hypothesis tightness and non-vacuity witnesses

Each `*_tight_*` theorem exhibits a concrete instance in which all hypotheses of a main
result except the named one hold and the conclusion fails. Each `*_nonvacuous` theorem
exhibits a concrete instance in which all hypotheses of a main result hold.
-/

namespace Toy.Drat

/-! ## `rup_implies_entails`, `rup_addition_preserves_equivalence` -/

/-- Without RUP, entailment fails: `x₀ ∨ x₁` does not entail `x₀`. -/
theorem rup_implies_entails_tight_rup :
    ¬ RUP [[Lit.p 0, Lit.p 1]] [Lit.p 0] ∧ ¬ Entails [[Lit.p 0, Lit.p 1]] [Lit.p 0] :=
  ⟨RUP_example_neg, Entails_example_neg⟩

/-- Non-vacuity: `x₁` is RUP w.r.t. `x₀ ∧ (¬x₀ ∨ x₁)`. -/
theorem rup_implies_entails_nonvacuous : RUP [[Lit.p 0], [Lit.n 0, Lit.p 1]] [Lit.p 1] :=
  RUP_example_pos

/-- Without RUP (here: RAT instead), equivalence fails. -/
theorem rup_equivalence_tight_rup :
    ¬ RUP [[Lit.p 1]] [Lit.p 0] ∧ ¬ Equivalent [[Lit.p 0], [Lit.p 1]] [[Lit.p 1]] := by
  refine ⟨fun h => rat_addition_not_equivalence.2.2.2.2 (rup_implies_entails h),
    rat_addition_not_equivalence.2.2.2.1⟩

/-! ## `ratOn_witness_satisfies` -/

/-- Without `p ∈ C`: the pivot `x₀` is not in `C = x₁`; `C` is (vacuously) RAT on `x₀`
w.r.t. the empty formula, the all-false assignment is a model, but the witness falsifies
`C`. -/
theorem ratOn_witness_tight_mem :
    Lit.p 0 ∉ [Lit.p 1] ∧ RATOn [] [Lit.p 1] (Lit.p 0) ∧ Satisfies (fun _ => false) [] ∧
      ¬ Satisfies (ratWitness (fun _ => false) [Lit.p 1] (Lit.p 0)) [[Lit.p 1]] := by
  refine ⟨by decide, fun D hD => by simp at hD, rfl, by decide⟩

/-- Without RAT: `x₀` w.r.t. `¬x₀`; the all-false assignment is a model of `¬x₀`, but the
witness (which sets `x₀`) falsifies `¬x₀`. -/
theorem ratOn_witness_tight_rat :
    Lit.p 0 ∈ [Lit.p 0] ∧ Satisfies (fun _ => false) [[Lit.n 0]] ∧
      ¬ RATOn [[Lit.n 0]] [Lit.p 0] (Lit.p 0) ∧
      ¬ Satisfies (ratWitness (fun _ => false) [Lit.p 0] (Lit.p 0)) [[Lit.p 0], [Lit.n 0]] :=
  ⟨by decide, by decide, RAT_example_neg, by decide⟩

/-- Without `a ⊨ F`: the all-false assignment is not a model of `x₁`, and the witness built
from it is not a model of `x₀ ∧ x₁`. -/
theorem ratOn_witness_tight_model :
    Lit.p 0 ∈ [Lit.p 0] ∧ RATOn [[Lit.p 1]] [Lit.p 0] (Lit.p 0) ∧
      ¬ Satisfies (fun _ => false) [[Lit.p 1]] ∧
      ¬ Satisfies (ratWitness (fun _ => false) [Lit.p 0] (Lit.p 0)) [[Lit.p 0], [Lit.p 1]] :=
  ⟨by decide, rat_addition_not_equivalence.1, by decide, by decide⟩

/-- Non-vacuity, in the branch where the witness differs from `a`: `x₀ ∨ ¬x₁` is RAT on `x₀`
w.r.t. `¬x₀ ∨ x₁`, the assignment `x₀ = false, x₁ = true` is a model of `¬x₀ ∨ x₁` and
falsifies `x₀ ∨ ¬x₁`. -/
theorem ratOn_witness_nonvacuous :
    Lit.p 0 ∈ [Lit.p 0, Lit.n 1] ∧ RATOn [[Lit.n 0, Lit.p 1]] [Lit.p 0, Lit.n 1] (Lit.p 0) ∧
      Satisfies (fun v => v == 1) [[Lit.n 0, Lit.p 1]] ∧
      Clause.eval (fun v => v == 1) [Lit.p 0, Lit.n 1] = false :=
  ⟨by decide, RAT_example_pos, by decide, by decide⟩

/-! ## `rat_addition_preserves_satisfiability` -/

/-- Without RAT: `¬x₀` is satisfiable but `x₀ ∧ ¬x₀` is not. -/
theorem rat_sat_tight_rat :
    ¬ RAT [[Lit.n 0]] [Lit.p 0] ∧ Satisfiable [[Lit.n 0]] ∧ ¬ Satisfiable [[Lit.p 0], [Lit.n 0]] :=
  ⟨RAT_example_neg, ⟨fun _ => false, by decide⟩, Satisfiable_example_neg⟩

/-- Without `Satisfiable F`: `x₁` is (vacuously) RAT w.r.t. the unsatisfiable `x₀ ∧ ¬x₀`,
and adding it does not produce a satisfiable formula. -/
theorem rat_sat_tight_sat :
    RAT [[Lit.p 0], [Lit.n 0]] [Lit.p 1] ∧ ¬ Satisfiable [[Lit.p 0], [Lit.n 0]] ∧
      ¬ Satisfiable [[Lit.p 1], [Lit.p 0], [Lit.n 0]] := by
  refine ⟨?_, Satisfiable_example_neg,
    fun ⟨a, ha⟩ => Satisfiable_example_neg ⟨a, Satisfies_of_subset ?_ ha⟩⟩
  · intro D hD hneg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hD
    rcases hD with rfl | rfl <;> exact absurd hneg (by decide)
  · intro D hD
    exact List.mem_cons_of_mem _ hD

/-- Non-vacuity: a satisfiable formula and a clause that is RAT but not RUP. -/
theorem rat_sat_nonvacuous :
    RAT [[Lit.n 0, Lit.p 1]] [Lit.p 0, Lit.n 1] ∧ Satisfiable [[Lit.n 0, Lit.p 1]] :=
  ⟨RAT_example_pos, ⟨fun _ => false, by decide⟩⟩

/-- Tightness of `RAT F C` in `rat_addition_equisatisfiable`: without it the two formulas need
not be equisatisfiable. -/
theorem rat_equisat_tight_rat :
    ¬ RAT [[Lit.n 0]] [Lit.p 0] ∧ ¬ Equisatisfiable ([Lit.p 0] :: [[Lit.n 0]]) [[Lit.n 0]] :=
  ⟨rat_sat_tight_rat.1, fun heq => rat_sat_tight_rat.2.2 (heq.2 rat_sat_tight_rat.2.1)⟩

/-! ## `ratOn_preserves_satisfiability` -/

/-- Without `p ∈ C`: `x₀ ∉ [x₁]`, `[x₁]` is (vacuously) `RATOn` `x₀` w.r.t. the satisfiable
`¬x₁`, and `x₁ ∧ ¬x₁` is unsatisfiable. -/
theorem ratOn_sat_tight_mem :
    Lit.p 0 ∉ [Lit.p 1] ∧ RATOn [[Lit.n 1]] [Lit.p 1] (Lit.p 0) ∧ Satisfiable [[Lit.n 1]] ∧
      ¬ Satisfiable [[Lit.p 1], [Lit.n 1]] := by
  refine ⟨by decide, ?_, ⟨fun _ => false, by decide⟩, ?_⟩
  · intro D hD hneg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hD
    subst hD
    exact absurd hneg (by decide)
  · rintro ⟨a, ha⟩
    simp only [Satisfies, Formula.eval, Clause.eval, Lit.eval, Lit.p, Lit.n, List.all_cons,
      List.any_cons, List.any_nil, List.all_nil, Bool.or_false, Bool.and_true] at ha
    cases h1 : a 1 <;> simp [h1] at ha

/-- Without `RATOn F C p`. -/
theorem ratOn_sat_tight_rat :
    Lit.p 0 ∈ [Lit.p 0] ∧ ¬ RATOn [[Lit.n 0]] [Lit.p 0] (Lit.p 0) ∧ Satisfiable [[Lit.n 0]] ∧
      ¬ Satisfiable [[Lit.p 0], [Lit.n 0]] :=
  ⟨by decide, RAT_example_neg, ⟨fun _ => false, by decide⟩, Satisfiable_example_neg⟩

/-- Without `Satisfiable F`. -/
theorem ratOn_sat_tight_sat :
    Lit.p 1 ∈ [Lit.p 1] ∧ RATOn [[Lit.p 0], [Lit.n 0]] [Lit.p 1] (Lit.p 1) ∧
      ¬ Satisfiable [[Lit.p 0], [Lit.n 0]] ∧ ¬ Satisfiable [[Lit.p 1], [Lit.p 0], [Lit.n 0]] :=
  ⟨by decide, rat_sat_tight_sat.1, rat_sat_tight_sat.2.1, rat_sat_tight_sat.2.2⟩

/-- Non-vacuity of `ratOn_preserves_satisfiability` with a non-first pivot on which the
first-literal `RAT` fails: `x₁ ∈ x₀ ∨ x₁`, `RATOn` `x₁` w.r.t. the satisfiable `¬x₀`. -/
theorem ratOn_sat_nonvacuous :
    Lit.p 1 ∈ [Lit.p 0, Lit.p 1] ∧ RATOn [[Lit.n 0]] [Lit.p 0, Lit.p 1] (Lit.p 1) ∧
      Satisfiable [[Lit.n 0]] ∧ ¬ RAT [[Lit.n 0]] [Lit.p 0, Lit.p 1] :=
  ⟨by decide, rat_check_depends_on_pivot_order.1, ⟨fun _ => false, by decide⟩,
    rat_check_depends_on_pivot_order.2.1⟩

/-! ## `rup_implies_rat_of_ne_nil` -/

/-- Without RUP: `x₀` is nonempty, not RUP, and not RAT w.r.t. `¬x₀`. -/
theorem rup_rat_tight_rup :
    [Lit.p 0] ≠ [] ∧ ¬ RUP [[Lit.n 0]] [Lit.p 0] ∧ ¬ RAT [[Lit.n 0]] [Lit.p 0] :=
  ⟨by simp, rat_after_deletion_not_rat_wrt_original.2.1, RAT_example_neg⟩

/-- Non-vacuity: `x₁` is nonempty and RUP w.r.t. `x₀ ∧ (¬x₀ ∨ x₁)`. -/
theorem rup_rat_nonvacuous : [Lit.p 1] ≠ [] ∧ RUP [[Lit.p 0], [Lit.n 0, Lit.p 1]] [Lit.p 1] :=
  ⟨by simp, RUP_example_pos⟩

/-! ## Refutation checkers -/

/-- Acceptance is needed: the DRAT addition check preserves satisfiability, yet for a
satisfiable formula the checkers reject (here on `(x₀ ∨ x₁) ∧ ¬x₀` with the certificate
"add the empty clause"), and the conclusion `¬ Satisfiable F` fails. -/
theorem checker_acceptance_tight :
    (∀ F C, addOK 3 F C = true → Satisfiable F → Satisfiable (C :: F)) ∧
      checkSpecified 3 [[Lit.p 0, Lit.p 1], [Lit.n 0]] [.add []] = false ∧
      checkOperational 3 [[Lit.p 0, Lit.p 1], [Lit.n 0]] [.add []] = false ∧
      checkGen (addOK 3) honorAll [[Lit.p 0, Lit.p 1], [Lit.n 0]] [.add []] = false ∧
      Satisfiable [[Lit.p 0, Lit.p 1], [Lit.n 0]] :=
  ⟨fun _ _ h hF => addOK_preserves_satisfiability h hF, by decide, by decide, by decide,
    Satisfiable_example_pos⟩

/-- Non-vacuity of the generic soundness theorem: the DRAT addition check preserves
satisfiability and the generic checker with it accepts a refutation. -/
theorem checkGen_sound_nonvacuous :
    (∀ F C, addOK 3 F C = true → Satisfiable F → Satisfiable (C :: F)) ∧
      checkGen (addOK 3) honorAll fullSquare [.add [Lit.p 1], .add []] = true :=
  ⟨fun _ _ h hF => addOK_preserves_satisfiability h hF, by decide⟩

/-- Non-vacuity of DRAT soundness for both deletion policies, exercising a RAT addition that
is not RUP (`x₃`) and a unit deletion (`x₀`) on which the two policies differ. -/
theorem checkDRAT_sound_nonvacuous :
    ¬ RUP ([Lit.p 0] :: fullSquare) [Lit.p 3] ∧ ratCheck 3 ([Lit.p 0] :: fullSquare) [Lit.p 3] = true ∧
      checkSpecified 3 ([Lit.p 0] :: fullSquare)
        [.add [Lit.p 3], .del [Lit.p 0], .add [Lit.p 1], .add []] = true ∧
      checkOperational 3 ([Lit.p 0] :: fullSquare)
        [.add [Lit.p 3], .del [Lit.p 0], .add [Lit.p 1], .add []] = true ∧
      applyDel honorAll ([Lit.p 3] :: [Lit.p 0] :: fullSquare) [Lit.p 0] ≠
        applyDel ignoreUnitDeletions ([Lit.p 3] :: [Lit.p 0] :: fullSquare) [Lit.p 0] :=
  ⟨not_rup_of_neverConflict
      (neverConflict_of_step (by decide) (neverConflict_of_closed (by decide) (by decide))),
    by decide, by decide, by decide, by decide⟩

/-- Tightness of the addition-check hypothesis of `addOK_preserves_satisfiability`. -/
theorem addOK_tight_check :
    addOK 2 [[Lit.n 0]] [Lit.p 0] = false ∧ Satisfiable [[Lit.n 0]] ∧
      ¬ Satisfiable [[Lit.p 0], [Lit.n 0]] :=
  ⟨by decide, ⟨fun _ => false, by decide⟩, Satisfiable_example_neg⟩

/-- Tightness of the satisfiability hypothesis of `addOK_preserves_satisfiability`. -/
theorem addOK_tight_sat :
    addOK 1 [[Lit.p 0], [Lit.n 0]] [Lit.p 1] = true ∧ ¬ Satisfiable [[Lit.p 0], [Lit.n 0]] ∧
      ¬ Satisfiable [[Lit.p 1], [Lit.p 0], [Lit.n 0]] :=
  ⟨by decide, Satisfiable_example_neg, rat_sat_tight_sat.2.2⟩

/-- Non-vacuity of `addOK_preserves_satisfiability`. -/
theorem addOK_nonvacuous :
    addOK 2 [[Lit.n 0, Lit.p 1]] [Lit.p 0, Lit.n 1] = true ∧ Satisfiable [[Lit.n 0, Lit.p 1]] :=
  ⟨addOK_example_pos, ⟨fun _ => false, by decide⟩⟩

/-- Non-vacuity of `applyDel_preserves_satisfiability`, with a deletion that changes the
formula under the specified policy. -/
theorem applyDel_nonvacuous :
    Satisfiable [[Lit.p 0, Lit.p 1], [Lit.n 0]] ∧
      applyDel honorAll [[Lit.p 0, Lit.p 1], [Lit.n 0]] [Lit.n 0] ≠ [[Lit.p 0, Lit.p 1], [Lit.n 0]] :=
  ⟨Satisfiable_example_pos, by decide⟩

/-- Tightness of the satisfiability hypothesis of `applyDel_preserves_satisfiability`, for both
policies. -/
theorem applyDel_tight_sat :
    ¬ Satisfiable [[Lit.p 0], [Lit.n 0], [Lit.p 1]] ∧
      ¬ Satisfiable (applyDel honorAll [[Lit.p 0], [Lit.n 0], [Lit.p 1]] [Lit.p 1]) ∧
      ¬ Satisfiable (applyDel ignoreUnitDeletions [[Lit.p 0], [Lit.n 0], [Lit.p 1]] [Lit.p 1]) := by
  have hsub : FormulaSub [[Lit.p 0], [Lit.n 0]] [[Lit.p 0], [Lit.n 0], [Lit.p 1]] := by
    intro D hD
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hD
    rcases hD with rfl | rfl <;> simp
  have hunsat : ¬ Satisfiable [[Lit.p 0], [Lit.n 0], [Lit.p 1]] :=
    fun ⟨a, ha⟩ => Satisfiable_example_neg ⟨a, Satisfies_of_subset hsub ha⟩
  have hdel : applyDel honorAll [[Lit.p 0], [Lit.n 0], [Lit.p 1]] [Lit.p 1] =
      [[Lit.p 0], [Lit.n 0]] := by decide
  have hkeep : applyDel ignoreUnitDeletions [[Lit.p 0], [Lit.n 0], [Lit.p 1]] [Lit.p 1] =
      [[Lit.p 0], [Lit.n 0], [Lit.p 1]] := by decide
  exact ⟨hunsat, hdel ▸ Satisfiable_example_neg, hkeep ▸ hunsat⟩

/-- Non-vacuity of `naiveSatCheck_sound_of_noDeletions`. -/
theorem naiveSatCheck_noDel_nonvacuous :
    NoDeletions [.add [Lit.p 1]] ∧
      naiveSatCheck 1 [[Lit.p 0], [Lit.n 0, Lit.p 1]] [.add [Lit.p 1]] (fun _ => true) = true :=
  ⟨fun s hs => ⟨[Lit.p 1], by simpa using hs⟩, by decide⟩

/-- Tightness of `NoDeletions π` in `naiveSatCheck_sound_of_noDeletions` (canonical form of
`naiveSatCheck_unsound_with_deletions` at budget 0). -/
theorem naiveSatCheck_noDel_tight_noDel :
    ¬ NoDeletions [.del [Lit.p 0]] ∧
      naiveSatCheck 0 [[Lit.p 0], [Lit.n 0]] [.del [Lit.p 0]] (fun _ => false) = true ∧
      ¬ Satisfies (fun _ => false) [[Lit.p 0], [Lit.n 0]] :=
  ⟨naiveSatCheck_unsound_with_deletions.1, rfl, by decide⟩

/-- Tightness of acceptance in `naiveSatCheck_sound_of_noDeletions`. -/
theorem naiveSatCheck_noDel_tight_accept :
    NoDeletions [] ∧ naiveSatCheck 1 [[Lit.p 0]] [] (fun _ => false) = false ∧
      ¬ Satisfies (fun _ => false) [[Lit.p 0]] :=
  ⟨fun _ h => absurd h List.not_mem_nil, by decide, by decide⟩

/-! ## Checked deletions -/

/-- Non-vacuity of `satCheckRupDel_sound` with a certificate that deletes a clause: add `x₁`
(RUP), then delete `¬x₀ ∨ x₁` (RUP w.r.t. the remaining `x₁ ∧ x₀`); the all-true assignment
satisfies the final formula. -/
theorem satCheckRupDel_nonvacuous :
    ¬ NoDeletions [.add [Lit.p 1], .del [Lit.n 0, Lit.p 1]] ∧
      satCheckRupDel 1 [[Lit.p 0], [Lit.n 0, Lit.p 1]] [.add [Lit.p 1], .del [Lit.n 0, Lit.p 1]]
        (fun _ => true) = true := by
  refine ⟨fun h => ?_, by decide⟩
  obtain ⟨C, hC⟩ := h (.del [Lit.n 0, Lit.p 1]) (by simp)
  cases hC

/-- Tightness of acceptance in `satCheckRupDel_sound`. -/
theorem satCheckRupDel_tight_accept :
    satCheckRupDel 1 [[Lit.p 0]] [] (fun _ => false) = false ∧
      ¬ Satisfies (fun _ => false) [[Lit.p 0]] :=
  ⟨by decide, by decide⟩

/-- Non-vacuity of `replayRatDel_sat_backward` with a deletion that passes the RAT check but
not the RUP check. -/
theorem replayRatDel_nonvacuous :
    replayRatDel 0 [[Lit.p 0, Lit.n 1], [Lit.n 0, Lit.p 1]] [.del [Lit.p 0, Lit.n 1]] =
        some [[Lit.n 0, Lit.p 1]] ∧ Satisfiable [[Lit.n 0, Lit.p 1]] :=
  ⟨replayRatDel_final_model_not_original.1, ⟨fun _ => false, by decide⟩⟩

/-- Tightness of the replay hypothesis of `replayRatDel_sat_backward`: deleting `x₀` from
`x₀ ∧ ¬x₀` fails the check (so the replay does not return the satisfiable empty formula),
and the original formula is unsatisfiable. -/
theorem replayRatDel_tight_replay :
    replayRatDel 2 [[Lit.p 0], [Lit.n 0]] [.del [Lit.p 0]] ≠ some [] ∧ Satisfiable [] ∧
      ¬ Satisfiable [[Lit.p 0], [Lit.n 0]] :=
  ⟨by decide, ⟨fun _ => false, rfl⟩, Satisfiable_example_neg⟩

/-- Tightness of the satisfiability hypothesis of `replayRatDel_sat_backward`. -/
theorem replayRatDel_tight_sat :
    replayRatDel 0 [[Lit.p 0], [Lit.n 0]] [] = some [[Lit.p 0], [Lit.n 0]] ∧
      ¬ Satisfiable [[Lit.p 0], [Lit.n 0]] ∧ ¬ Satisfiable [[Lit.p 0], [Lit.n 0]] :=
  ⟨rfl, Satisfiable_example_neg, Satisfiable_example_neg⟩

/-- Tightness of `F ⊆ G` in `checkDRUP_honorAll_implies_any_policy`. -/
theorem checkDRUP_policy_tight_sub :
    ¬ FormulaSub [[Lit.p 0], [Lit.n 0]] [] ∧
      checkDRUP 1 honorAll [[Lit.p 0], [Lit.n 0]] [.add []] = true ∧
      checkDRUP 1 ignoreUnitDeletions [] [.add []] = false :=
  ⟨fun h => by simpa using h [Lit.p 0] (by simp), by decide, by decide⟩

/-- Acceptance is needed in `checkDRUP_honorAll_implies_any_policy`. -/
theorem checkDRUP_policy_tight_accept :
    FormulaSub [[Lit.p 0, Lit.p 1]] [[Lit.p 0, Lit.p 1]] ∧
      checkDRUP 1 honorAll [[Lit.p 0, Lit.p 1]] [.add []] = false ∧
      checkDRUP 1 ignoreUnitDeletions [[Lit.p 0, Lit.p 1]] [.add []] = false :=
  ⟨fun _ h => h, by decide, by decide⟩

/-- Non-vacuity of `checkDRUP_honorAll_implies_any_policy` with a strict superset `G ⊋ F` and a
unit deletion (`x₀`) on which `honorAll` and `ignoreUnitDeletions` differ. -/
theorem checkDRUP_policy_nonvacuous :
    FormulaSub ([Lit.p 0] :: fullSquare) ([Lit.p 3] :: [Lit.p 0] :: fullSquare) ∧
      ¬ FormulaSub ([Lit.p 3] :: [Lit.p 0] :: fullSquare) ([Lit.p 0] :: fullSquare) ∧
      checkDRUP 3 honorAll ([Lit.p 0] :: fullSquare) [.add [Lit.p 1], .del [Lit.p 0], .add []] = true ∧
      applyDel honorAll ([Lit.p 1] :: [Lit.p 0] :: fullSquare) [Lit.p 0] ≠
        applyDel ignoreUnitDeletions ([Lit.p 1] :: [Lit.p 0] :: fullSquare) [Lit.p 0] := by
  refine ⟨fun D hD => List.mem_cons_of_mem _ hD, fun h => ?_, by decide, by decide⟩
  exact absurd (h [Lit.p 3] List.mem_cons_self) (by decide)

/-! ## LRAT -/

/-- Tightness of hint acceptance in `lrat_hint_replay_implies_rup` (and its entailment
corollary). -/
theorem lrat_tight_accept :
    lratRupCheck [[Lit.p 0, Lit.p 1]] [Lit.p 0] [0] = false ∧ ¬ RUP [[Lit.p 0, Lit.p 1]] [Lit.p 0] ∧
      ¬ Entails [[Lit.p 0, Lit.p 1]] [Lit.p 0] :=
  ⟨by decide, RUP_example_neg, Entails_example_neg⟩

/-- Tightness of `RUP F C` in `lratRupCheck_complete_of_wellformed`: well-formed inputs, `C` not
RUP, and no hint list accepted. -/
theorem lrat_complete_tight_rup :
    NonTautological [Lit.p 0] ∧ DupFreeClauses [[Lit.p 0, Lit.p 1]] ∧
      ¬ RUP [[Lit.p 0, Lit.p 1]] [Lit.p 0] ∧
      ∀ hints, lratRupCheck [[Lit.p 0, Lit.p 1]] [Lit.p 0] hints = false := by
  refine ⟨?_, ?_, RUP_example_neg, fun hints => ?_⟩
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    subst hl; decide
  · intro D hD
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hD
    subst hD; decide
  · cases h : lratRupCheck [[Lit.p 0, Lit.p 1]] [Lit.p 0] hints with
    | false => rfl
    | true => exact absurd (lrat_hint_replay_implies_rup h).2 RUP_example_neg

/-- Non-vacuity of `lratRupCheck_complete_of_wellformed`. -/
theorem lrat_complete_nonvacuous :
    NonTautological [] ∧ DupFreeClauses chain3 ∧ RUP chain3 [] :=
  ⟨fun _ hl => absurd hl List.not_mem_nil, DupFreeClauses_example_pos, lrat_hint_order_matters.1⟩

end Toy.Drat
