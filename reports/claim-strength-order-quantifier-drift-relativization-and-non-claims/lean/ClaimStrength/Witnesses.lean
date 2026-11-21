import ClaimStrength.Drift
import ClaimStrength.PrefixResults

/-!
# Countermodels of the drift non-entailments, stated as theorems

Each non-entailment `¬ Entails A B` (or `¬ SEntailsAt α φ ψ`) elsewhere in the library is proved
by exhibiting one interpretation that satisfies `A` and falsifies `B`. The theorems below state
that property for the exhibited interpretation, so that the countermodel is part of a statement
rather than of a proof. No definition is introduced here.
-/

namespace Toy.ClaimStrength

/-- The countermodel of `unsupported_not_imply_contradicted`: over the interpretations `Bool`,
the empty report neither supports nor contradicts the claim `b = true`. -/
theorem unsupported_not_imply_contradicted_witness :
    ¬ Supported ([] : List (Claim Bool)) (fun b => b = true) ∧
    ¬ Contradicted ([] : List (Claim Bool)) (fun b => b = true) :=
  worldIndependent_tight.2

/-- The countermodel of `forall_exists_not_sentails_exists_forall`: at the base type `Bool`, with
the matrix `y = x` (variables `x = 0`, `y = 1`) and the environment mapping every variable to
`false`, the prefix `∀x ∃y` holds and the prefix `∃y ∀x` fails. -/
theorem forall_exists_not_sentails_exists_forall_witness :
    eval ([A 0, X 1] : Prefix 2) (fun σ : Fin 2 → Bool => σ 1 = σ 0) (fun _ => false) ∧
    ¬ eval ([X 1, A 0] : Prefix 2) (fun σ : Fin 2 → Bool => σ 1 = σ 0) (fun _ => false) := by
  refine ⟨?_, ?_⟩
  · rw [eval_cons_all]; intro a; rw [eval_cons_ex]
    exact ⟨a, by simp [eval_nil, upd]⟩
  · intro h
    rw [eval_cons_ex] at h
    obtain ⟨b, hb⟩ := h
    rw [eval_cons_all] at hb
    have := hb (!b)
    simp [eval_nil, upd] at this

/-- The countermodel of `single_parameter_not_range`: the predicate `P k := k = 2` holds at `2`
and fails at `1`, which satisfies `1 ≤ k`. -/
theorem single_parameter_not_range_witness :
    (fun P : Nat → Prop => P 2) (fun k => k = 2) ∧
    ¬ (fun P : Nat → Prop => ∀ k, 1 ≤ k → P k) (fun k => k = 2) := by
  refine ⟨rfl, fun h => ?_⟩
  have h1 := h 1 (by decide)
  simp at h1

/-- The countermodel of `relative_not_absolute`: with `H = C = (· = 0)`, the relative claim
`∀x, H x → C x` holds and the absolute claim `∀x, C x` fails (at `x = 1`). -/
theorem relative_not_absolute_witness :
    (fun w : (Nat → Prop) × (Nat → Prop) => ∀ x, w.1 x → w.2 x) ((· = 0), (· = 0)) ∧
    ¬ (fun w : (Nat → Prop) × (Nat → Prop) => ∀ x, w.2 x) ((· = 0), (· = 0)) := by
  refine ⟨fun _ hx => hx, fun h => ?_⟩
  have h1 := h 1
  simp at h1

/-- The countermodel of `relative_to_assumption_not_absolute`: with `A = C = False`, the claim
`A → C` holds and the claim `C` fails. -/
theorem relative_to_assumption_not_absolute_witness :
    (fun w : Prop × Prop => w.1 → w.2) (False, False) ∧
    ¬ (fun w : Prop × Prop => w.2) (False, False) :=
  ⟨fun f => f, fun f => f⟩

/-- The countermodel of `conj_premise_not_disj`: with `H₁ = True`, `H₂ = False`, `C = False`,
the claim `H₁ ∧ H₂ → C` holds and the claim `H₁ ∨ H₂ → C` fails. -/
theorem conj_premise_not_disj_witness :
    (fun w : Prop × Prop × Prop => w.1 ∧ w.2.1 → w.2.2) (True, False, False) ∧
    ¬ (fun w : Prop × Prop × Prop => w.1 ∨ w.2.1 → w.2.2) (True, False, False) :=
  ⟨fun hc => hc.2, fun h => h (Or.inl trivial)⟩

/-- The countermodel of `single_counterexample_not_universal`: the predicate `P m := m ≠ 0` has
the counterexample `0`, and it is not refuted everywhere (`P 1` holds). -/
theorem single_counterexample_not_universal_witness :
    (fun P : Nat → Prop => ∃ m, ¬ P m) (fun m => m ≠ 0) ∧
    ¬ (fun P : Nat → Prop => ∀ m, ¬ P m) (fun m => m ≠ 0) := by
  refine ⟨⟨0, fun h0 => h0 rfl⟩, fun h => ?_⟩
  have h1 := h 1
  simp at h1

/-- The countermodel of `counterexample_in_class_not_in_subclass`: the predicate
`P m := m % 2 = 0` has the counterexample `1` among all naturals and no counterexample among the
even naturals. -/
theorem counterexample_in_class_not_in_subclass_witness :
    (fun P : Nat → Prop => ∃ m, ¬ P m) (fun m => m % 2 = 0) ∧
    ¬ (fun P : Nat → Prop => ∃ m, m % 2 = 0 ∧ ¬ P m) (fun m => m % 2 = 0) := by
  refine ⟨⟨1, by decide⟩, ?_⟩
  rintro ⟨m, hm, hP⟩
  exact hP hm

/-- The countermodel of `sufficient_not_characterization`: with `A = False`, `B = True`, the
claim `A → B` holds and the claim `A ↔ B` fails. -/
theorem sufficient_not_characterization_witness :
    (fun w : Prop × Prop => w.1 → w.2) (False, True) ∧
    ¬ (fun w : Prop × Prop => w.1 ↔ w.2) (False, True) :=
  ⟨fun f => False.elim f, fun h => h.2 trivial⟩

/-- The countermodel of `sufficient_not_converse`: with `A = False`, `B = True`, the claim
`A → B` holds and the claim `B → A` fails. -/
theorem sufficient_not_converse_witness :
    (fun w : Prop × Prop => w.1 → w.2) (False, True) ∧
    ¬ (fun w : Prop × Prop => w.2 → w.1) (False, True) :=
  ⟨fun f => False.elim f, fun h => h trivial⟩

/-- The countermodel of `checker_sound_not_complete`: `zeroChecker` (accepts exactly `0`; the
good inputs are the even numbers) is sound and not complete. -/
theorem checker_sound_not_complete_witness :
    CheckerSound zeroChecker ∧ ¬ CheckerComplete zeroChecker :=
  ⟨checkerSound_example_pos.1, fun h => absurd (h 2 (show 2 % 2 = 0 from rfl)) (by decide)⟩

/-- The countermodel of `checker_complete_not_sound`: `acceptAll` (accepts every input; no input
is good) is complete and not sound. -/
theorem checker_complete_not_sound_witness :
    CheckerComplete acceptAll ∧ ¬ CheckerSound acceptAll :=
  ⟨fun _ h => False.elim h, checkerSound_example_neg⟩

end Toy.ClaimStrength
