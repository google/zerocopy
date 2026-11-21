import ToyDrat.Cards

/-!
# Supplementary witnesses

* Canonical-form tightness and non-vacuity witnesses for `replay_model_sound_of_noDeletions`
  (each `*_tight_*` theorem: all hypotheses except the named one hold and the conclusion fails;
  the `*_nonvacuous` theorem: all hypotheses hold).
* `rupCheck_of_mem`: a clause that still occurs in the formula passes `rupCheck` at every budget,
  so a deletion check that tested the deleted clause against the formula still containing it
  would accept every deletion.
* `lratRupCheck_side_conditions_not_necessary`: the side conditions `NonTautological C` and
  `DupFreeClauses F` of `lratRupCheck_complete_of_wellformed` are tight but not logically
  necessary: each can fail while some hint list is still accepted.
-/

namespace Toy.Drat

/-- Non-vacuity of `replay_model_sound_of_noDeletions`: a deletion-free certificate, a successful
replay (with the unchecked addition check `fun _ _ => true` and the policy
`ignoreUnitDeletions`), and an assignment satisfying the final formula. -/
theorem replay_model_sound_nonvacuous :
    NoDeletions [.add [Lit.p 1]] ∧
      replay (fun _ _ => true) ignoreUnitDeletions [[Lit.p 0]] [.add [Lit.p 1]] =
        some [[Lit.p 1], [Lit.p 0]] ∧
      Satisfies (fun _ => true) [[Lit.p 1], [Lit.p 0]] :=
  ⟨fun s hs => ⟨[Lit.p 1], by simpa using hs⟩, rfl, by decide⟩

/-- Tightness of `hnd : NoDeletions π` in `replay_model_sound_of_noDeletions`: with the deletion
of `x₀`, the replay of `x₀ ∧ ¬x₀` ends in `¬x₀`, which the all-false assignment satisfies, while
it does not satisfy the original formula. -/
theorem replay_model_sound_tight_noDel :
    ¬ NoDeletions [.del [Lit.p 0]] ∧
      replay (addOK 0) honorAll [[Lit.p 0], [Lit.n 0]] [.del [Lit.p 0]] = some [[Lit.n 0]] ∧
      Satisfies (fun _ => false) [[Lit.n 0]] ∧
      ¬ Satisfies (fun _ => false) [[Lit.p 0], [Lit.n 0]] :=
  ⟨naiveSatCheck_unsound_with_deletions.1, rfl, by decide, by decide⟩

/-- Tightness of `hrep : replay addCheck ignore F π = some G` in
`replay_model_sound_of_noDeletions`: the empty certificate does not replay `x₀` to the empty
formula, which the all-false assignment satisfies, while it does not satisfy `x₀`. -/
theorem replay_model_sound_tight_replay :
    NoDeletions [] ∧
      replay (addOK 0) honorAll [[Lit.p 0]] [] ≠ some [] ∧
      Satisfies (fun _ => false) [] ∧
      ¬ Satisfies (fun _ => false) [[Lit.p 0]] :=
  ⟨fun _ h => absurd h List.not_mem_nil, by decide, rfl, by decide⟩

/-- Tightness of `ha : Satisfies a G` in `replay_model_sound_of_noDeletions`: the empty
certificate replays `x₀` to itself, and the all-false assignment satisfies neither the final
formula nor the original one. -/
theorem replay_model_sound_tight_sat :
    NoDeletions [] ∧
      replay (addOK 0) honorAll [[Lit.p 0]] [] = some [[Lit.p 0]] ∧
      ¬ Satisfies (fun _ => false) [[Lit.p 0]] ∧
      ¬ Satisfies (fun _ => false) [[Lit.p 0]] :=
  ⟨fun _ h => absurd h List.not_mem_nil, rfl, by decide, by decide⟩

/-- A clause that occurs in the formula passes `rupCheck` at every budget: assuming all of its
literals false falsifies it, which `hasConflict` reports before any propagation round. -/
theorem rupCheck_of_mem {fuel : Nat} {F : Formula} {C : Clause} (hC : C ∈ F) :
    rupCheck fuel F C = true := by
  have hc : hasConflict F (negClause C) = true := by
    simp only [hasConflict, Bool.or_eq_true, List.any_eq_true, List.all_eq_true]
    refine Or.inr ⟨C, hC, fun l hl => ?_⟩
    simp only [falsified, negClause, List.mem_map, decide_eq_true_eq]
    exact ⟨l, hl, rfl⟩
  cases fuel <;> simp [rupCheck, unitProp, hc]

/-- The side conditions of `lratRupCheck_complete_of_wellformed` are not logically necessary:
(1) the tautological clause `x₀ ∨ ¬x₀` is RUP with respect to `x₁ ∧ ¬x₁` and has an accepted hint
list; (2) the formula `x₀ ∧ (¬x₀ ∨ ¬x₀ ∨ x₁) ∧ ¬x₁` repeats a literal in a clause, and the empty
clause is RUP with respect to it and has an accepted hint list. -/
theorem lratRupCheck_side_conditions_not_necessary :
    (¬ NonTautological [Lit.p 0, Lit.n 0] ∧
      DupFreeClauses [[Lit.p 1], [Lit.n 1]] ∧
      RUP [[Lit.p 1], [Lit.n 1]] [Lit.p 0, Lit.n 0] ∧
      lratRupCheck [[Lit.p 1], [Lit.n 1]] [Lit.p 0, Lit.n 0] [0, 1] = true) ∧
    (NonTautological [] ∧
      ¬ DupFreeClauses [[Lit.p 0], [Lit.n 0, Lit.n 0, Lit.p 1], [Lit.n 1]] ∧
      RUP [[Lit.p 0], [Lit.n 0, Lit.n 0, Lit.p 1], [Lit.n 1]] [] ∧
      lratRupCheck [[Lit.p 0], [Lit.n 0, Lit.n 0, Lit.p 1], [Lit.n 1]] [] [0, 1, 2] = true) := by
  refine ⟨⟨lratRupCheck_incomplete_tautology.1, ?_, ⟨1, by decide⟩, by decide⟩,
    ⟨lratRupCheck_incomplete_dup_lits.1, ?_, ⟨2, by decide⟩, by decide⟩⟩
  · intro D hD
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hD
    rcases hD with rfl | rfl <;> decide
  · intro h
    exact absurd (h [Lit.n 0, Lit.n 0, Lit.p 1] (by simp)) (by decide)

end Toy.Drat
