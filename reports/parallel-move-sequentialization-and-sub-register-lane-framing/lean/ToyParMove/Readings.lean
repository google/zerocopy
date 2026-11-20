import ToyParMove.Basic

/-!
Order independence of the parallel-move semantics. On every store, `pmove` is
order-independent exactly for functional moves (over a value type with two distinct values);
on one fixed store, exactly when moves with the same destination read equal values. With a
repeated destination carrying two different sources, the "first wins" and "last wins" readings
disagree. The package adopts first-match `pmove` on well-formed moves.
-/
set_option linter.unusedSectionVars false

namespace Toy.ParMove

/-! ### Definition examples -/

/-- Positive example (`pmove`): the parallel swap `[(0,1),(1,0)]` exchanges locations 0 and 1
and leaves 2 alone. -/
theorem pmove_swap_example :
    pmove [(0, 1), (1, 0)] (id : Nat → Nat) 0 = 1 ∧
    pmove [(0, 1), (1, 0)] (id : Nat → Nat) 1 = 0 ∧
    pmove [(0, 1), (1, 0)] (id : Nat → Nat) 2 = 2 := by decide

/-- Negative example (`pmove`): the chain `[(1,0),(2,1)]` read in parallel gives location 2 the
*old* value of 1, not the value that a left-to-right reading would have copied from 0. -/
theorem pmove_rejects_sequential_reading :
    pmove [(1, 0), (2, 1)] (id : Nat → Nat) 2 = 1 ∧
    runSeq [(1, 0), (2, 1)] (id : Nat → Nat) 2 = 0 := by decide

/-- Positive example (`WellFormed`). -/
theorem wellFormed_swap_example : WellFormed [((0 : Nat), (1 : Nat)), (1, 0)] := by decide

/-- Negative example (`WellFormed`): a repeated destination. -/
theorem not_wellFormed_repeated_destination :
    ¬ WellFormed [((0 : Nat), (1 : Nat)), (0, 2)] := by decide

/-- Positive example (`Functional`): the exact duplicate `[(0,1),(0,1)]` is functional but not
well-formed; with `functional_of_wellFormed`, `Functional` is strictly weaker than `WellFormed`. -/
theorem functional_duplicate_not_wellFormed :
    Functional [((0 : Nat), (1 : Nat)), (0, 1)] ∧ ¬ WellFormed [((0 : Nat), (1 : Nat)), (0, 1)] := by
  refine ⟨?_, by decide⟩
  intro d s₁ s₂ h₁ h₂
  simp at h₁ h₂
  rw [h₁.2, h₂.2]

/-- Negative example (`Functional`): one destination with two different sources. -/
theorem not_functional_two_sources : ¬ Functional [((0 : Nat), (1 : Nat)), (0, 2)] := by
  intro h
  have := h 0 1 2 (by simp) (by simp)
  omega

/-- Positive example (`runSeq`): the three-move sequence through scratch location 2 swaps 0 and 1. -/
theorem runSeq_swap_via_scratch_example :
    runSeq [(2, 0), (0, 1), (1, 2)] (id : Nat → Nat) 0 = 1 ∧
    runSeq [(2, 0), (0, 1), (1, 2)] (id : Nat → Nat) 1 = 0 := by decide

/-- Negative example (`runSeq`): emitting the two moves of a swap one after the other does not
swap. -/
theorem runSeq_naive_swap_fails :
    runSeq [(0, 1), (1, 0)] (id : Nat → Nat) 1 = 1 := by decide

/-! ### Functionality at a fixed store -/

section
variable {Loc V : Type} [DecidableEq Loc]

/-- **Functionality at a store** `σ`: moves with the same destination read *equal values* in
`σ` (their source locations may differ). Weaker than `Functional` and dependent on `σ`; it is
the store-level analogue of requiring that two copies into one variable copy the same value. -/
def FunctionalAt (σ : Loc → V) (M : List (Loc × Loc)) : Prop :=
  ∀ d s₁ s₂, (d, s₁) ∈ M → (d, s₂) ∈ M → σ s₁ = σ s₂

theorem functionalAt_of_functional {M : List (Loc × Loc)} (hF : Functional M) (σ : Loc → V) :
    FunctionalAt σ M := fun d s₁ s₂ h₁ h₂ =>
  congrArg σ (hF d s₁ s₂ h₁ h₂)

end

/-- Positive example (`FunctionalAt`): two different sources of destination `0` that hold the
same value in the store. -/
theorem functionalAt_equal_values_example :
    FunctionalAt (fun l : Nat => if l = 2 then 1 else l) [((0 : Nat), (1 : Nat)), (0, 2)] ∧
    ¬ Functional [((0 : Nat), (1 : Nat)), (0, 2)] := by
  refine ⟨?_, not_functional_two_sources⟩
  intro d s₁ s₂ h₁ h₂
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h₁ h₂
  rcases h₁ with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rcases h₂ with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide

/-- Negative example (`FunctionalAt`): the same move list at a store that distinguishes the two
sources. -/
theorem not_functionalAt_id_example :
    ¬ FunctionalAt (id : Nat → Nat) [((0 : Nat), (1 : Nat)), (0, 2)] := by
  intro h
  have := h 0 1 2 (by simp) (by simp)
  simp at this

/-! ### Order independence and the two readings -/

/-- **Counterexample (two readings).** With the repeated destination `0` (sources `1` and `2`),
the first-entry reading and the last-entry reading of the "parallel" move give different
values at location `0`. -/
theorem pmove_readings_disagree_on_repeated_destination :
    pmove [(0, 1), (0, 2)] (id : Nat → Nat) 0 = 1 ∧
    pmoveLast [(0, 1), (0, 2)] (id : Nat → Nat) 0 = 2 := by decide

section
variable {Loc V : Type} [DecidableEq Loc]

/-- **Order independence for functional moves.** If moves with equal destinations have equal
sources, then reordering the list does not change the parallel-move semantics. -/
theorem pmove_perm_invariant_of_functional {M M' : List (Loc × Loc)} (hF : Functional M)
    (hp : M.Perm M') (σ : Loc → V) : pmove M σ = pmove M' σ := by
  funext l
  by_cases hl : l ∈ dsts M
  · obtain ⟨s, hs⟩ := mem_dsts.1 hl
    rw [pmove_of_mem hF hs, pmove_of_mem (functional_of_perm hF hp) (hp.mem_iff.1 hs)]
  · have hl' : l ∉ dsts M' := by
      intro h
      obtain ⟨s, hs⟩ := mem_dsts.1 h
      exact hl (mem_dsts.2 ⟨s, hp.mem_iff.2 hs⟩)
    rw [pmove_of_not_mem_dsts hl, pmove_of_not_mem_dsts hl']

/-- **Order independence forces functionality.** If the value type has two distinct values and
every reordering of `M` has the same parallel-move semantics on every store, then `M` is
functional. -/
theorem functional_of_pmove_perm_invariant_of_two_values {M : List (Loc × Loc)} (a b : V)
    (hab : a ≠ b)
    (h : ∀ M' : List (Loc × Loc), M'.Perm M → ∀ σ : Loc → V, pmove M' σ = pmove M σ) :
    Functional M := by
  intro d s₁ s₂ h₁ h₂
  apply Classical.byContradiction
  intro hne
  let σ : Loc → V := fun l => if l = s₁ then a else b
  have e₁ := congrFun (h _ (List.perm_cons_erase h₁).symm σ) d
  have e₂ := congrFun (h _ (List.perm_cons_erase h₂).symm σ) d
  simp only [pmove, lookupSrc, ite_true] at e₁ e₂
  have : σ s₁ = σ s₂ := e₁.trans e₂.symm
  simp only [σ, ite_true, show s₂ ≠ s₁ from fun e => hne e.symm, ite_false] at this
  exact hab this

/-- **Characterization.** Over a value type with two distinct values, the parallel-move
semantics of `M` is invariant under every reordering of `M` iff `M` is functional. -/
theorem pmove_perm_invariant_iff_functional_of_two_values {M : List (Loc × Loc)} (a b : V)
    (hab : a ≠ b) :
    (∀ M' : List (Loc × Loc), M'.Perm M → ∀ σ : Loc → V, pmove M' σ = pmove M σ) ↔
      Functional M :=
  ⟨functional_of_pmove_perm_invariant_of_two_values a b hab,
   fun hF _ hp σ => (pmove_perm_invariant_of_functional hF hp.symm σ).symm⟩

/-- **Characterization at a fixed store.** For one store `σ`, the parallel-move semantics of
`M` at `σ` is invariant under every reordering of `M` iff moves with the same destination read
equal values in `σ`. No hypothesis on the value type is needed. -/
theorem pmove_perm_invariant_at_iff_functionalAt {M : List (Loc × Loc)} (σ : Loc → V) :
    (∀ M' : List (Loc × Loc), M'.Perm M → pmove M' σ = pmove M σ) ↔ FunctionalAt σ M := by
  constructor
  · intro h d s₁ s₂ h₁ h₂
    have e₁ := congrFun (h _ (List.perm_cons_erase h₁).symm) d
    have e₂ := congrFun (h _ (List.perm_cons_erase h₂).symm) d
    simp only [pmove, lookupSrc, ite_true] at e₁ e₂
    exact e₁.trans e₂.symm
  · intro hF M' hp
    funext l
    unfold pmove
    cases h1 : lookupSrc M' l with
    | none =>
      have hl' : l ∉ dsts M' := lookupSrc_eq_none_iff.1 h1
      have h2 : lookupSrc M l = none := lookupSrc_eq_none_iff.2 (fun hl => by
        obtain ⟨s, hs⟩ := mem_dsts.1 hl
        exact hl' (mem_dsts.2 ⟨s, hp.mem_iff.2 hs⟩))
      simp [h2]
    | some s =>
      have hs : (l, s) ∈ M := hp.mem_iff.1 (mem_of_lookupSrc_eq_some h1)
      cases h2 : lookupSrc M l with
      | none => exact absurd (mem_dsts.2 ⟨s, hs⟩) (lookupSrc_eq_none_iff.1 h2)
      | some s' => exact hF l s s' hs (mem_of_lookupSrc_eq_some h2)

/-- The two readings coincide at a store where moves with the same destination read equal
values. -/
theorem pmove_eq_pmoveLast_of_functionalAt {M : List (Loc × Loc)} {σ : Loc → V}
    (h : FunctionalAt σ M) : pmove M σ = pmoveLast M σ :=
  ((pmove_perm_invariant_at_iff_functionalAt σ).2 h M.reverse (List.reverse_perm M)).symm

/-- **The two readings coincide on functional moves.** -/
theorem pmove_eq_pmoveLast_of_functional {M : List (Loc × Loc)} (hF : Functional M)
    (σ : Loc → V) : pmove M σ = pmoveLast M σ :=
  pmove_perm_invariant_of_functional hF (List.reverse_perm M).symm σ

/-- Corollary for the adopted well-formedness condition (distinct destinations). -/
theorem pmove_eq_pmoveLast_of_wellFormed {M : List (Loc × Loc)} (hM : WellFormed M)
    (σ : Loc → V) : pmove M σ = pmoveLast M σ :=
  pmove_eq_pmoveLast_of_functional (functional_of_wellFormed hM) σ

end

/-- Non-claim witness: the two readings of `[(0,1),(0,2)]` agree at a store in which the two
sources hold equal values. -/
theorem pmove_readings_agree_on_equal_source_values :
    pmove [((0 : Nat), (1 : Nat)), (0, 2)] (fun l : Nat => if l = 2 then 1 else l) =
      pmoveLast [((0 : Nat), (1 : Nat)), (0, 2)] (fun l : Nat => if l = 2 then 1 else l) :=
  pmove_eq_pmoveLast_of_functionalAt functionalAt_equal_values_example.1

/-! ### Tightness and non-vacuity for order independence -/

/-- Counterexample (hypothesis `Functional` of `pmove_perm_invariant_of_functional`): the
reordering `[(0,2),(0,1)]` of `[(0,1),(0,2)]` changes the value at `0`. -/
theorem pmove_perm_invariant_needs_functional :
    ¬ Functional [((0 : Nat), (1 : Nat)), (0, 2)] ∧
    List.Perm [((0 : Nat), (1 : Nat)), (0, 2)] [(0, 2), (0, 1)] ∧
    pmove [((0 : Nat), (1 : Nat)), (0, 2)] (id : Nat → Nat) ≠ pmove [(0, 2), (0, 1)] id := by
  refine ⟨not_functional_two_sources, List.Perm.swap _ _ _, fun h => ?_⟩
  have := congrFun h 0
  simp [pmove, lookupSrc] at this

/-- Counterexample (hypothesis `Functional` of `pmove_eq_pmoveLast_of_functional`). -/
theorem pmove_eq_pmoveLast_needs_functional :
    ¬ Functional [((0 : Nat), (1 : Nat)), (0, 2)] ∧
    pmove [((0 : Nat), (1 : Nat)), (0, 2)] (id : Nat → Nat) ≠
      pmoveLast [((0 : Nat), (1 : Nat)), (0, 2)] id := by
  refine ⟨not_functional_two_sources, fun h => ?_⟩
  have := congrFun h 0
  simp [pmoveLast, pmove, lookupSrc] at this

/-- Counterexample (hypothesis `a ≠ b` of `functional_of_pmove_perm_invariant_of_two_values`
and of `pmove_perm_invariant_iff_functional_of_two_values`): over the one-element value type no
two values differ, every move list is order-independent, yet `[(0,1),(0,2)]` is not functional,
so both the implication and the equivalence fail. -/
theorem functional_of_pmove_perm_invariant_needs_two_values :
    (∀ a b : Unit, a = b) ∧
    (∀ M' : List (Nat × Nat), M'.Perm [(0, 1), (0, 2)] → ∀ σ : Nat → Unit,
      pmove M' σ = pmove [(0, 1), (0, 2)] σ) ∧
    ¬ Functional [((0 : Nat), (1 : Nat)), (0, 2)] ∧
    ¬ ((∀ M' : List (Nat × Nat), M'.Perm [(0, 1), (0, 2)] → ∀ σ : Nat → Unit,
        pmove M' σ = pmove [(0, 1), (0, 2)] σ) ↔ Functional [((0 : Nat), (1 : Nat)), (0, 2)]) := by
  have hinv : ∀ M' : List (Nat × Nat), M'.Perm [(0, 1), (0, 2)] → ∀ σ : Nat → Unit,
      pmove M' σ = pmove [(0, 1), (0, 2)] σ := fun _ _ _ => funext fun _ => rfl
  exact ⟨fun _ _ => rfl, hinv, not_functional_two_sources,
    fun h => not_functional_two_sources (h.1 hinv)⟩

/-- Counterexample (hypothesis `M.Perm M'` of `pmove_perm_invariant_of_functional`): the empty
move list is functional, but a list that is not a reordering of it has a different meaning. -/
theorem pmove_perm_invariant_needs_perm :
    Functional ([] : List (Nat × Nat)) ∧
    ¬ List.Perm ([] : List (Nat × Nat)) [(0, 1)] ∧
    pmove ([] : List (Nat × Nat)) (id : Nat → Nat) ≠ pmove [(0, 1)] id := by
  refine ⟨by intro d s₁ s₂ h; simp at h, fun h => absurd h.length_eq (by decide), fun h => ?_⟩
  have := congrFun h 0
  simp [pmove, lookupSrc] at this

/-- Counterexample (hypothesis "every reordering has the same meaning on every store" of
`functional_of_pmove_perm_invariant_of_two_values`): `Bool` has two distinct values, the
reordering `[(0,2),(0,1)]` of `[(0,1),(0,2)]` changes the result, and the list is not
functional. -/
theorem functional_of_pmove_perm_invariant_needs_perm_invariance :
    (true ≠ false) ∧
    ¬ (∀ M' : List (Nat × Nat), M'.Perm [(0, 1), (0, 2)] → ∀ σ : Nat → Bool,
        pmove M' σ = pmove [(0, 1), (0, 2)] σ) ∧
    ¬ Functional [((0 : Nat), (1 : Nat)), (0, 2)] := by
  refine ⟨by decide, fun h => ?_, not_functional_two_sources⟩
  have e := congrFun (h [(0, 2), (0, 1)] (List.Perm.swap _ _ _) (fun l => decide (l = 1))) 0
  simp [pmove, lookupSrc] at e

/-- Non-vacuity: a well-formed (hence functional) swap and its reversal. -/
theorem nonvacuity_pmove_perm_invariant :
    Functional [((0 : Nat), (1 : Nat)), (1, 0)] ∧
    List.Perm [((0 : Nat), (1 : Nat)), (1, 0)] [(1, 0), (0, 1)] :=
  ⟨functional_of_wellFormed (by decide), List.Perm.swap _ _ _⟩

/-- Non-vacuity for the characterization: `Bool` has two distinct values and the swap is
functional. -/
theorem nonvacuity_pmove_perm_invariant_iff :
    (true ≠ false) ∧ Functional [((0 : Nat), (1 : Nat)), (1, 0)] :=
  ⟨Bool.noConfusion, functional_of_wellFormed (by decide)⟩

/-- Non-vacuity for every order-independence theorem at once: two distinct `Bool` values, the
functional swap, a reordering of it, and its order independence on every `Bool` store (the
hypothesis of `functional_of_pmove_perm_invariant_of_two_values`). -/
theorem nonvacuity_pmove_perm_invariant_all :
    (true ≠ false) ∧
    Functional [((0 : Nat), (1 : Nat)), (1, 0)] ∧
    List.Perm [((0 : Nat), (1 : Nat)), (1, 0)] [(1, 0), (0, 1)] ∧
    (∀ M' : List (Nat × Nat), M'.Perm [(0, 1), (1, 0)] → ∀ σ : Nat → Bool,
      pmove M' σ = pmove [(0, 1), (1, 0)] σ) :=
  ⟨Bool.noConfusion, functional_of_wellFormed (by decide), List.Perm.swap _ _ _,
   fun _ hp σ => (pmove_perm_invariant_of_functional
     (functional_of_wellFormed (by decide)) hp.symm σ).symm⟩

end Toy.ParMove
