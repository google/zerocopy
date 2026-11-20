import ToyParMove.Swaps

/-!
Tightness counterexamples, non-vacuity witnesses, and positive controls for the cycle results
(scratch upper and lower bounds, impossibility without scratch, swap upper and lower bounds).
-/
set_option linter.unusedSectionVars false

namespace Toy.ParMove

/-- Pointwise description of the three-element non-duplicate-free "cycle" `[0,1,0]`:
location `1` receives the old value of `0`; everything else is unchanged. -/
theorem runSeq_eq_pmove_cycle_010 :
    runSeq [((1 : Nat), (0 : Nat))] (id : Nat → Nat) = pmove (cycleMoves [0, 1, 0]) id := by
  funext l
  by_cases h0 : l = 0
  · subst h0; decide
  · by_cases h1 : l = 1
    · subst h1; decide
    · simp [runSeq, seqStep, upd, pmove, lookupSrc, cycleMoves, chain, h0, h1]

theorem pmove_const (M : List (Nat × Nat)) :
    pmove M (fun _ : Nat => (0 : Nat)) = fun _ => 0 := by
  funext l
  simp only [pmove]
  cases lookupSrc M l <;> rfl

theorem not_injective_const : ¬ Function.Injective (fun _ : Nat => (0 : Nat)) :=
  fun h => absurd (h (a₁ := 0) (a₂ := 1) rfl) (by decide)

theorem injective_id_nat : Function.Injective (id : Nat → Nat) := fun _ _ h => h

/-! #### `runSeq_cycleSeqScratch` -/

/-- Counterexample (hypothesis `Nodup`): for the list `[0,1,0]` the scratch sequence leaves the
old value of `1` at `1`, while the cycle's target puts the old value of `0` there. -/
theorem runSeq_cycleSeqScratch_needs_nodup :
    ¬ ([0, 1, 0] : List Nat).Nodup ∧ (5 : Nat) ∉ ([0, 1, 0] : List Nat) ∧
    ¬ (∀ l, l ≠ 5 → runSeq (cycleSeqScratch 5 [0, 1, 0]) (id : Nat → Nat) l =
        pmove (cycleMoves [0, 1, 0]) id l) :=
  ⟨by decide, by decide, fun h => absurd (h 1 (by decide)) (by decide)⟩

/-- Counterexample (hypothesis `tmp ∉ l₀ :: rest`): using a cycle location as the scratch. -/
theorem runSeq_cycleSeqScratch_needs_tmp_fresh :
    ([0, 1] : List Nat).Nodup ∧ (0 : Nat) ∈ ([0, 1] : List Nat) ∧
    ¬ (∀ l, l ≠ 0 → runSeq (cycleSeqScratch 0 [0, 1]) (id : Nat → Nat) l =
        pmove (cycleMoves [0, 1]) id l) :=
  ⟨by decide, by decide, fun h => absurd (h 1 (by decide)) (by decide)⟩

/-- Non-vacuity of `runSeq_cycleSeqScratch` (a 3-cycle with scratch `3`), together with the
move count `k + 1 = 4`. -/
theorem nonvacuity_runSeq_cycleSeqScratch :
    ((0 : Nat) :: [1, 2]).Nodup ∧ (3 : Nat) ∉ ((0 : Nat) :: [1, 2]) ∧
    (cycleSeqScratch (3 : Nat) [0, 1, 2]).length = 4 :=
  ⟨by decide, by decide, by decide⟩

/-! #### `cycle_length_add_one_le_of_injective_of_realizes_off_tmp` -/

theorem cycle_lower_bound_needs_nodup :
    ¬ ([0, 1, 0] : List Nat).Nodup ∧ 2 ≤ ([0, 1, 0] : List Nat).length ∧
    (5 : Nat) ∉ ([0, 1, 0] : List Nat) ∧ Function.Injective (id : Nat → Nat) ∧
    (∀ l, l ≠ 5 → runSeq [((1 : Nat), (0 : Nat))] (id : Nat → Nat) l =
      pmove (cycleMoves [0, 1, 0]) id l) ∧
    ¬ (([0, 1, 0] : List Nat).length + 1 ≤ [((1 : Nat), (0 : Nat))].length) :=
  ⟨by decide, by decide, by decide, injective_id_nat,
    fun l _ => congrFun runSeq_eq_pmove_cycle_010 l, by decide⟩

theorem cycle_lower_bound_needs_two :
    ([0] : List Nat).Nodup ∧ ¬ 2 ≤ ([0] : List Nat).length ∧ (5 : Nat) ∉ ([0] : List Nat) ∧
    Function.Injective (id : Nat → Nat) ∧
    (∀ l, l ≠ 5 → runSeq ([] : List (Nat × Nat)) (id : Nat → Nat) l =
      pmove (cycleMoves [0]) id l) ∧
    ¬ (([0] : List Nat).length + 1 ≤ ([] : List (Nat × Nat)).length) := by
  refine ⟨by decide, by decide, by decide, injective_id_nat, fun l _ => ?_, by decide⟩
  by_cases h : l = 0
  · subst h; decide
  · simp [pmove, lookupSrc, cycleMoves, chain, h]

theorem cycle_lower_bound_needs_tmp_fresh :
    ([0, 1] : List Nat).Nodup ∧ 2 ≤ ([0, 1] : List Nat).length ∧ (0 : Nat) ∈ ([0, 1] : List Nat) ∧
    Function.Injective (id : Nat → Nat) ∧
    (∀ l, l ≠ 0 → runSeq [((1 : Nat), (0 : Nat))] (id : Nat → Nat) l =
      pmove (cycleMoves [0, 1]) id l) ∧
    ¬ (([0, 1] : List Nat).length + 1 ≤ [((1 : Nat), (0 : Nat))].length) := by
  refine ⟨by decide, by decide, by decide, injective_id_nat, fun l hl => ?_, by decide⟩
  by_cases h : l = 1
  · subst h; decide
  · simp [runSeq, seqStep, upd, pmove, lookupSrc, cycleMoves, chain, h, hl]

theorem cycle_lower_bound_needs_injective :
    ([0, 1] : List Nat).Nodup ∧ 2 ≤ ([0, 1] : List Nat).length ∧ (5 : Nat) ∉ ([0, 1] : List Nat) ∧
    ¬ Function.Injective (fun _ : Nat => (0 : Nat)) ∧
    (∀ l, l ≠ 5 → runSeq ([] : List (Nat × Nat)) (fun _ : Nat => (0 : Nat)) l =
      pmove (cycleMoves [0, 1]) (fun _ : Nat => (0 : Nat)) l) ∧
    ¬ (([0, 1] : List Nat).length + 1 ≤ ([] : List (Nat × Nat)).length) := by
  refine ⟨by decide, by decide, by decide, not_injective_const, fun l _ => ?_, by decide⟩
  rw [pmove_const]; rfl

theorem cycle_lower_bound_needs_realization :
    ([0, 1] : List Nat).Nodup ∧ 2 ≤ ([0, 1] : List Nat).length ∧ (5 : Nat) ∉ ([0, 1] : List Nat) ∧
    Function.Injective (id : Nat → Nat) ∧
    ¬ (∀ l, l ≠ 5 → runSeq ([] : List (Nat × Nat)) (id : Nat → Nat) l =
      pmove (cycleMoves [0, 1]) id l) ∧
    ¬ (([0, 1] : List Nat).length + 1 ≤ ([] : List (Nat × Nat)).length) :=
  ⟨by decide, by decide, by decide, injective_id_nat,
    fun h => absurd (h 0 (by decide)) (by decide), by decide⟩

/-- Non-vacuity of `cycle_length_add_one_le_of_injective_of_realizes_off_tmp`: the 2-cycle `[0,1]` with
scratch `2`, realized by `cycleSeqScratch 2 [0,1]`, which has exactly `k + 1 = 3` moves (so the
bound is attained). -/
theorem nonvacuity_cycle_lower_bound :
    ([0, 1] : List Nat).Nodup ∧ 2 ≤ ([0, 1] : List Nat).length ∧ (2 : Nat) ∉ ([0, 1] : List Nat) ∧
    Function.Injective (id : Nat → Nat) ∧
    (∀ l, l ≠ 2 → runSeq (cycleSeqScratch 2 [0, 1]) (id : Nat → Nat) l =
      pmove (cycleMoves [0, 1]) id l) ∧
    (cycleSeqScratch (2 : Nat) [0, 1]).length = ([0, 1] : List Nat).length + 1 :=
  ⟨by decide, by decide, by decide, injective_id_nat,
    runSeq_cycleSeqScratch (by decide) (by decide) id, by decide⟩

/-! #### `runSeq_ne_pmove_cycle_of_injective` and the 2-cycle corollary -/

theorem cycle_impossibility_needs_nodup :
    ¬ ([0, 1, 0] : List Nat).Nodup ∧ 2 ≤ ([0, 1, 0] : List Nat).length ∧
    Function.Injective (id : Nat → Nat) ∧
    runSeq [((1 : Nat), (0 : Nat))] (id : Nat → Nat) = pmove (cycleMoves [0, 1, 0]) id :=
  ⟨by decide, by decide, injective_id_nat, runSeq_eq_pmove_cycle_010⟩

theorem cycle_impossibility_needs_two :
    ([0] : List Nat).Nodup ∧ ¬ 2 ≤ ([0] : List Nat).length ∧ Function.Injective (id : Nat → Nat) ∧
    runSeq ([] : List (Nat × Nat)) (id : Nat → Nat) = pmove (cycleMoves [0]) id := by
  refine ⟨by decide, by decide, injective_id_nat, funext fun l => ?_⟩
  by_cases h : l = 0
  · subst h; decide
  · simp [pmove, lookupSrc, cycleMoves, chain, h]

theorem cycle_impossibility_needs_injective :
    ([0, 1] : List Nat).Nodup ∧ 2 ≤ ([0, 1] : List Nat).length ∧
    ¬ Function.Injective (fun _ : Nat => (0 : Nat)) ∧
    runSeq ([] : List (Nat × Nat)) (fun _ : Nat => (0 : Nat)) =
      pmove (cycleMoves [0, 1]) (fun _ : Nat => (0 : Nat)) := by
  refine ⟨by decide, by decide, not_injective_const, ?_⟩
  rw [pmove_const]; rfl

/-- Positive control for the impossibility: with one scratch location the 2-cycle is realized
off the scratch location; with a swap primitive it is realized exactly; and a cycle that also
has an outgoing copy (`[(3,1),(2,1),(1,2)]`) is realized exactly by plain moves with no scratch
location. -/
theorem cycle_impossibility_positive_control :
    (∀ l, l ≠ 2 → runSeq (cycleSeqScratch 2 [0, 1]) (id : Nat → Nat) l =
      pmove (cycleMoves [0, 1]) id l) ∧
    runSwaps [((0 : Nat), (1 : Nat))] (id : Nat → Nat) = pmove (cycleMoves [0, 1]) id ∧
    runSeq [((3 : Nat), (1 : Nat)), (1, 2), (2, 3)] (id : Nat → Nat) =
      pmove [((3 : Nat), (1 : Nat)), (2, 1), (1, 2)] id :=
  ⟨runSeq_cycleSeqScratch (by decide) (by decide) id,
   runSwaps_cycleSwaps (ls := [0, 1]) (by decide) id,
   cycle_with_outgoing_copy_realized_without_scratch.2 Nat id⟩

/-- Non-vacuity of `runSeq_ne_pmove_cycle_of_injective`. -/
theorem nonvacuity_cycle_impossibility :
    ([0, 1] : List Nat).Nodup ∧ 2 ≤ ([0, 1] : List Nat).length ∧
    Function.Injective (id : Nat → Nat) :=
  ⟨by decide, by decide, injective_id_nat⟩

theorem swap_impossibility_needs_distinct :
    ¬ ((0 : Nat) ≠ 0) ∧ Function.Injective (id : Nat → Nat) ∧
    runSeq ([] : List (Nat × Nat)) (id : Nat → Nat) = pmove [((0 : Nat), (0 : Nat)), (0, 0)] id := by
  refine ⟨by decide, injective_id_nat, funext fun l => ?_⟩
  by_cases h : l = 0
  · subst h; decide
  · simp [pmove, lookupSrc, h]

theorem swap_impossibility_needs_injective :
    (0 : Nat) ≠ 1 ∧ ¬ Function.Injective (fun _ : Nat => (0 : Nat)) ∧
    runSeq ([] : List (Nat × Nat)) (fun _ : Nat => (0 : Nat)) =
      pmove [((0 : Nat), (1 : Nat)), (1, 0)] (fun _ : Nat => (0 : Nat)) := by
  refine ⟨by decide, not_injective_const, ?_⟩
  rw [pmove_const]; rfl

theorem nonvacuity_swap_impossibility :
    (0 : Nat) ≠ 1 ∧ Function.Injective (id : Nat → Nat) := ⟨by decide, injective_id_nat⟩

/-! #### Swaps -/

theorem runSwaps_cycleSwaps_needs_nodup :
    ¬ ([0, 1, 0] : List Nat).Nodup ∧
    runSwaps (cycleSwaps [0, 1, 0]) (id : Nat → Nat) ≠ pmove (cycleMoves [0, 1, 0]) id :=
  ⟨by decide, fun h => absurd (congrFun h 0) (by decide)⟩

theorem nonvacuity_runSwaps_cycleSwaps :
    ([0, 1, 2] : List Nat).Nodup ∧ (cycleSwaps ([0, 1, 2] : List Nat)).length = 2 :=
  ⟨by decide, by decide⟩

theorem swap_lower_bound_needs_nodup :
    ¬ ([0, 1, 0, 1] : List Nat).Nodup ∧ Function.Injective (id : Nat → Nat) ∧
    runSwaps [((0 : Nat), (1 : Nat))] (id : Nat → Nat) = pmove (cycleMoves [0, 1, 0, 1]) id ∧
    ¬ (([0, 1, 0, 1] : List Nat).length - 1 ≤ [((0 : Nat), (1 : Nat))].length) := by
  refine ⟨by decide, injective_id_nat, funext fun l => ?_, by decide⟩
  by_cases h0 : l = 0
  · subst h0; decide
  · by_cases h1 : l = 1
    · subst h1; decide
    · simp [runSwaps, swapStore, pmove, lookupSrc, cycleMoves, chain, h0, h1]

theorem swap_lower_bound_needs_injective :
    ([0, 1] : List Nat).Nodup ∧ ¬ Function.Injective (fun _ : Nat => (0 : Nat)) ∧
    runSwaps ([] : List (Nat × Nat)) (fun _ : Nat => (0 : Nat)) =
      pmove (cycleMoves [0, 1]) (fun _ : Nat => (0 : Nat)) ∧
    ¬ (([0, 1] : List Nat).length - 1 ≤ ([] : List (Nat × Nat)).length) := by
  refine ⟨by decide, not_injective_const, ?_, by decide⟩
  rw [pmove_const]; rfl

theorem swap_lower_bound_needs_realization :
    ([0, 1] : List Nat).Nodup ∧ Function.Injective (id : Nat → Nat) ∧
    runSwaps ([] : List (Nat × Nat)) (id : Nat → Nat) ≠ pmove (cycleMoves [0, 1]) id ∧
    ¬ (([0, 1] : List Nat).length - 1 ≤ ([] : List (Nat × Nat)).length) :=
  ⟨by decide, injective_id_nat, fun h => absurd (congrFun h 0) (by decide), by decide⟩

/-- Non-vacuity of `cycle_length_sub_one_le_of_injective_of_runSwaps`: the 3-cycle realized by its two
swaps (the bound is attained). -/
theorem nonvacuity_swap_lower_bound :
    ([0, 1, 2] : List Nat).Nodup ∧ Function.Injective (id : Nat → Nat) ∧
    runSwaps (cycleSwaps [0, 1, 2]) (id : Nat → Nat) = pmove (cycleMoves [0, 1, 2]) id ∧
    (cycleSwaps ([0, 1, 2] : List Nat)).length = ([0, 1, 2] : List Nat).length - 1 :=
  ⟨by decide, injective_id_nat, runSwaps_cycleSwaps (by decide) id, by decide⟩

/-! #### Injectivity cannot be weakened to injectivity on the cycle -/

/-- Non-claim witness for the scratch lower bound: the store is injective on the cycle `[0,1]`
and the scratch `2`, but location `3` holds a copy of the old value of `0`; two moves (fewer
than `k + 1 = 3`) then realize the 2-cycle off `2`. -/
theorem cycle_lower_bound_needs_global_injectivity :
    ([0, 1] : List Nat).Nodup ∧ 2 ≤ ([0, 1] : List Nat).length ∧ (2 : Nat) ∉ ([0, 1] : List Nat) ∧
    ¬ Function.Injective (fun l : Nat => if l = 3 then 0 else l) ∧
    (∀ x y, x ∈ ([0, 1, 2] : List Nat) → y ∈ ([0, 1, 2] : List Nat) →
      (fun l : Nat => if l = 3 then 0 else l) x = (fun l : Nat => if l = 3 then 0 else l) y →
      x = y) ∧
    (∀ l, l ≠ 2 → runSeq [((0 : Nat), (1 : Nat)), (1, 3)] (fun l : Nat => if l = 3 then 0 else l) l =
      pmove (cycleMoves [0, 1]) (fun l : Nat => if l = 3 then 0 else l) l) ∧
    ¬ (([0, 1] : List Nat).length + 1 ≤ [((0 : Nat), (1 : Nat)), (1, 3)].length) := by
  refine ⟨by decide, by decide, by decide,
    fun h => absurd (h (a₁ := 0) (a₂ := 3) (by decide)) (by decide), ?_, fun l _ => ?_, by decide⟩
  · intro x y hx hy hxy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> simp_all
  · by_cases h0 : l = 0
    · subst h0; decide
    · by_cases h1 : l = 1
      · subst h1; decide
      · simp [runSeq, seqStep, upd, pmove, lookupSrc, cycleMoves, chain, h0, h1]

/-- Non-claim witness for the impossibility: the values of the cycle locations `0` and `1`
occur nowhere else, but locations `2` and `3` hold equal values; then location `2` can be
borrowed as a scratch and restored from `3`, realizing the 2-cycle exactly. -/
theorem cycle_impossibility_needs_global_injectivity :
    ([0, 1] : List Nat).Nodup ∧ 2 ≤ ([0, 1] : List Nat).length ∧
    ¬ Function.Injective (fun l : Nat => if l = 3 then 2 else l) ∧
    (∀ x ∈ ([0, 1] : List Nat), ∀ y,
      (fun l : Nat => if l = 3 then 2 else l) x = (fun l : Nat => if l = 3 then 2 else l) y →
      x = y) ∧
    runSeq [((2 : Nat), (0 : Nat)), (0, 1), (1, 2), (2, 3)] (fun l : Nat => if l = 3 then 2 else l) =
      pmove (cycleMoves [0, 1]) (fun l : Nat => if l = 3 then 2 else l) := by
  refine ⟨by decide, by decide,
    fun h => absurd (h (a₁ := 2) (a₂ := 3) (by decide)) (by decide), ?_, funext fun l => ?_⟩
  · intro x hx y hxy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> (by_cases hy : y = 3 <;> simp_all)
  · by_cases h0 : l = 0
    · subst h0; decide
    · by_cases h1 : l = 1
      · subst h1; decide
      · by_cases h2 : l = 2
        · subst h2; decide
        · simp [runSeq, seqStep, upd, pmove, lookupSrc, cycleMoves, chain, h0, h1, h2]

/-! #### Uniform (all-stores) versions -/

/-- Counterexample (hypothesis `a ≠ b` of `runSeq_ne_pmove_cycle_of_two_values`): over `Unit`
the empty sequence realizes the 2-cycle on every store. -/
theorem cycle_impossibility_uniform_needs_two_values :
    (∀ a b : Unit, a = b) ∧ ([0, 1] : List Nat).Nodup ∧ 2 ≤ ([0, 1] : List Nat).length ∧
    ∃ ms : List (Nat × Nat), ∀ σ : Nat → Unit, runSeq ms σ = pmove (cycleMoves [0, 1]) σ :=
  ⟨fun _ _ => rfl, by decide, by decide, ⟨[], fun _ => funext fun _ => rfl⟩⟩

/-- Counterexample (hypothesis `Nodup` of `runSeq_ne_pmove_cycle_of_two_values`). -/
theorem cycle_impossibility_uniform_needs_nodup :
    (true ≠ false) ∧ ¬ ([0, 1, 0] : List Nat).Nodup ∧ 2 ≤ ([0, 1, 0] : List Nat).length ∧
    ∃ ms : List (Nat × Nat), ∀ σ : Nat → Bool, runSeq ms σ = pmove (cycleMoves [0, 1, 0]) σ :=
  ⟨by decide, by decide, by decide, ⟨[(1, 0)], runSeq_eq_pmove_of_id runSeq_eq_pmove_cycle_010⟩⟩

/-- Counterexample (hypothesis `2 ≤ ls.length` of `runSeq_ne_pmove_cycle_of_two_values`). -/
theorem cycle_impossibility_uniform_needs_two :
    (true ≠ false) ∧ ([0] : List Nat).Nodup ∧ ¬ 2 ≤ ([0] : List Nat).length ∧
    ∃ ms : List (Nat × Nat), ∀ σ : Nat → Bool, runSeq ms σ = pmove (cycleMoves [0]) σ :=
  ⟨by decide, by decide, by decide, ⟨[], runSeq_eq_pmove_of_id cycle_impossibility_needs_two.2.2.2⟩⟩

/-- Non-vacuity of `runSeq_ne_pmove_cycle_of_two_values` (with `V = Bool`). -/
theorem nonvacuity_cycle_impossibility_uniform :
    (true ≠ false) ∧ ([0, 1] : List Nat).Nodup ∧ 2 ≤ ([0, 1] : List Nat).length :=
  ⟨by decide, by decide, by decide⟩

/-- Counterexample (hypothesis `a ≠ b` of
`cycle_length_add_one_le_of_two_values_of_realizes_off_tmp`). -/
theorem cycle_lower_bound_uniform_needs_two_values :
    (∀ a b : Unit, a = b) ∧ ([0, 1] : List Nat).Nodup ∧ 2 ≤ ([0, 1] : List Nat).length ∧
    (5 : Nat) ∉ ([0, 1] : List Nat) ∧
    (∀ σ : Nat → Unit, ∀ l, l ≠ 5 → runSeq ([] : List (Nat × Nat)) σ l =
      pmove (cycleMoves [0, 1]) σ l) ∧
    ¬ (([0, 1] : List Nat).length + 1 ≤ ([] : List (Nat × Nat)).length) :=
  ⟨fun _ _ => rfl, by decide, by decide, by decide, fun _ _ _ => rfl, by decide⟩

/-- Counterexample (hypothesis `Nodup` of
`cycle_length_add_one_le_of_two_values_of_realizes_off_tmp`). -/
theorem cycle_lower_bound_uniform_needs_nodup :
    (true ≠ false) ∧ ¬ ([0, 1, 0] : List Nat).Nodup ∧ 2 ≤ ([0, 1, 0] : List Nat).length ∧
    (5 : Nat) ∉ ([0, 1, 0] : List Nat) ∧
    (∀ σ : Nat → Bool, ∀ l, l ≠ 5 → runSeq [((1 : Nat), (0 : Nat))] σ l =
      pmove (cycleMoves [0, 1, 0]) σ l) ∧
    ¬ (([0, 1, 0] : List Nat).length + 1 ≤ [((1 : Nat), (0 : Nat))].length) :=
  ⟨by decide, by decide, by decide, by decide,
    fun σ l _ => congrFun (runSeq_eq_pmove_of_id runSeq_eq_pmove_cycle_010 σ) l, by decide⟩

/-- Counterexample (hypothesis `2 ≤ ls.length` of
`cycle_length_add_one_le_of_two_values_of_realizes_off_tmp`). -/
theorem cycle_lower_bound_uniform_needs_two :
    (true ≠ false) ∧ ([0] : List Nat).Nodup ∧ ¬ 2 ≤ ([0] : List Nat).length ∧
    (5 : Nat) ∉ ([0] : List Nat) ∧
    (∀ σ : Nat → Bool, ∀ l, l ≠ 5 → runSeq ([] : List (Nat × Nat)) σ l =
      pmove (cycleMoves [0]) σ l) ∧
    ¬ (([0] : List Nat).length + 1 ≤ ([] : List (Nat × Nat)).length) :=
  ⟨by decide, by decide, by decide, by decide,
    fun σ l _ => congrFun (runSeq_eq_pmove_of_id cycle_impossibility_needs_two.2.2.2 σ) l,
    by decide⟩

/-- Counterexample (hypothesis `tmp ∉ ls` of
`cycle_length_add_one_le_of_two_values_of_realizes_off_tmp`). -/
theorem cycle_lower_bound_uniform_needs_tmp_fresh :
    (true ≠ false) ∧ ([0, 1] : List Nat).Nodup ∧ 2 ≤ ([0, 1] : List Nat).length ∧
    (0 : Nat) ∈ ([0, 1] : List Nat) ∧
    (∀ σ : Nat → Bool, ∀ l, l ≠ 0 → runSeq [((1 : Nat), (0 : Nat))] σ l =
      pmove (cycleMoves [0, 1]) σ l) ∧
    ¬ (([0, 1] : List Nat).length + 1 ≤ [((1 : Nat), (0 : Nat))].length) :=
  ⟨by decide, by decide, by decide, by decide,
    fun σ l hl => runSeq_eq_pmove_at_of_id (cycle_lower_bound_needs_tmp_fresh.2.2.2.2.1 l hl) σ,
    by decide⟩

/-- Counterexample (hypothesis "realizes the cycle off `tmp` on every store" of
`cycle_length_add_one_le_of_two_values_of_realizes_off_tmp`). -/
theorem cycle_lower_bound_uniform_needs_realization :
    (true ≠ false) ∧ ([0, 1] : List Nat).Nodup ∧ 2 ≤ ([0, 1] : List Nat).length ∧
    (5 : Nat) ∉ ([0, 1] : List Nat) ∧
    ¬ (∀ σ : Nat → Bool, ∀ l, l ≠ 5 → runSeq ([] : List (Nat × Nat)) σ l =
      pmove (cycleMoves [0, 1]) σ l) ∧
    ¬ (([0, 1] : List Nat).length + 1 ≤ ([] : List (Nat × Nat)).length) :=
  ⟨by decide, by decide, by decide, by decide,
    fun h => absurd (h (fun l => decide (l = 1)) 0 (by decide)) (by decide), by decide⟩

/-- Non-vacuity of `cycle_length_add_one_le_of_two_values_of_realizes_off_tmp`: the scratch
realization of the 2-cycle works on every `Bool` store (and attains the bound). -/
theorem nonvacuity_cycle_lower_bound_uniform :
    (true ≠ false) ∧ ([0, 1] : List Nat).Nodup ∧ 2 ≤ ([0, 1] : List Nat).length ∧
    (2 : Nat) ∉ ([0, 1] : List Nat) ∧
    (∀ σ : Nat → Bool, ∀ l, l ≠ 2 → runSeq (cycleSeqScratch 2 [0, 1]) σ l =
      pmove (cycleMoves [0, 1]) σ l) ∧
    (cycleSeqScratch (2 : Nat) [0, 1]).length = ([0, 1] : List Nat).length + 1 :=
  ⟨by decide, by decide, by decide, by decide,
    fun σ => runSeq_cycleSeqScratch (by decide) (by decide) σ, by decide⟩

/-- Counterexample (hypothesis `a ≠ b` of `cycle_length_sub_one_le_of_two_values_of_runSwaps`). -/
theorem swap_lower_bound_uniform_needs_two_values :
    (∀ a b : Unit, a = b) ∧ ([0, 1] : List Nat).Nodup ∧
    (∀ σ : Nat → Unit, runSwaps ([] : List (Nat × Nat)) σ = pmove (cycleMoves [0, 1]) σ) ∧
    ¬ (([0, 1] : List Nat).length - 1 ≤ ([] : List (Nat × Nat)).length) :=
  ⟨fun _ _ => rfl, by decide, fun _ => funext fun _ => rfl, by decide⟩

/-- Counterexample (hypothesis `Nodup` of `cycle_length_sub_one_le_of_two_values_of_runSwaps`). -/
theorem swap_lower_bound_uniform_needs_nodup :
    (true ≠ false) ∧ ¬ ([0, 1, 0, 1] : List Nat).Nodup ∧
    (∀ σ : Nat → Bool, runSwaps [((0 : Nat), (1 : Nat))] σ = pmove (cycleMoves [0, 1, 0, 1]) σ) ∧
    ¬ (([0, 1, 0, 1] : List Nat).length - 1 ≤ [((0 : Nat), (1 : Nat))].length) :=
  ⟨by decide, by decide, runSwaps_eq_pmove_of_id swap_lower_bound_needs_nodup.2.2.1, by decide⟩

/-- Counterexample (hypothesis "realizes the cycle on every store" of
`cycle_length_sub_one_le_of_two_values_of_runSwaps`). -/
theorem swap_lower_bound_uniform_needs_realization :
    (true ≠ false) ∧ ([0, 1] : List Nat).Nodup ∧
    ¬ (∀ σ : Nat → Bool, runSwaps ([] : List (Nat × Nat)) σ = pmove (cycleMoves [0, 1]) σ) ∧
    ¬ (([0, 1] : List Nat).length - 1 ≤ ([] : List (Nat × Nat)).length) :=
  ⟨by decide, by decide,
    fun h => absurd (congrFun (h (fun l => decide (l = 1))) 0) (by decide), by decide⟩

/-- Non-vacuity of `cycle_length_sub_one_le_of_two_values_of_runSwaps`: the two swaps of the
3-cycle work on every `Bool` store (and attain the bound). -/
theorem nonvacuity_swap_lower_bound_uniform :
    (true ≠ false) ∧ ([0, 1, 2] : List Nat).Nodup ∧
    (∀ σ : Nat → Bool, runSwaps (cycleSwaps [0, 1, 2]) σ = pmove (cycleMoves [0, 1, 2]) σ) ∧
    (cycleSwaps ([0, 1, 2] : List Nat)).length = ([0, 1, 2] : List Nat).length - 1 :=
  ⟨by decide, by decide, fun σ => runSwaps_cycleSwaps (by decide) σ, by decide⟩

/-! #### No topological order for cycles -/

/-- Non-vacuity of `not_topological_of_perm_cycleMoves`. -/
theorem nonvacuity_not_topological_cycle :
    ([0, 1, 2] : List Nat).Nodup ∧ 2 ≤ ([0, 1, 2] : List Nat).length ∧
    (cycleMoves ([0, 1, 2] : List Nat)).Perm (cycleMoves [0, 1, 2]) :=
  ⟨by decide, by decide, List.Perm.refl _⟩

/-! #### `sequentialize` on single cycles (finite check) -/

/-- On single cycles of length 2 to 5 with a fresh scratch location, `sequentialize` emits
exactly `k + 1` moves, matching the lower bound. This is a finite check, not a general theorem. -/
theorem sequentialize_cycle_length_examples :
    (sequentialize (9 : Nat) (cycleMoves [0, 1])).length = 3 ∧
    (sequentialize (9 : Nat) (cycleMoves [0, 1, 2])).length = 4 ∧
    (sequentialize (9 : Nat) (cycleMoves [0, 1, 2, 3])).length = 5 ∧
    (sequentialize (9 : Nat) (cycleMoves [0, 1, 2, 3, 4])).length = 6 := by
  decide +kernel

end Toy.ParMove
