/-
Loose specifications of a function `List Nat → List Nat`: a characterization by
lemmas admits every lawful interpretation, including unintended ones; a
stronger characterization determines the intended function.
-/

namespace Toy.Extension

/-- A weak characterization of a sorting function on `List Nat`: the output is
sorted (every earlier element `≤` every later one) and has the input's length. -/
def WeakSortSpec (f : List Nat → List Nat) : Prop :=
  ∀ l, List.Pairwise (· ≤ ·) (f l) ∧ (f l).length = l.length

/-- A strong characterization: the output is sorted and a permutation of the input. -/
def StrongSortSpec (f : List Nat → List Nat) : Prop :=
  ∀ l, List.Pairwise (· ≤ ·) (f l) ∧ (f l).Perm l

/-- A lawful-but-weird interpretation of the weak characterization. -/
def weirdSort (l : List Nat) : List Nat := List.replicate l.length 0

/-- The intended interpretation: merge sort from the core library. -/
def natSort (l : List Nat) : List Nat := l.mergeSort (fun a b => decide (a ≤ b))

/-- At most one lawful interpretation: any two functions satisfying `Lspec` are
equal. This is uniqueness only; it holds vacuously when `Lspec` is
unsatisfiable (see `false_spec_atMostOneLawful_not_determines`). -/
def AtMostOneLawful {X Y : Type} (Lspec : (X → Y) → Prop) : Prop :=
  ∀ f g, Lspec f → Lspec g → f = g

/-- `Lspec` determines a function: it has a lawful interpretation, and at most
one. -/
def Determines {X Y : Type} (Lspec : (X → Y) → Prop) : Prop :=
  (∃ f, Lspec f) ∧ AtMostOneLawful Lspec

theorem natSort_pairwise (l : List Nat) : List.Pairwise (· ≤ ·) (natSort l) :=
  (List.pairwise_mergeSort (le := fun a b => decide (a ≤ b))
    (fun a b c hab hbc => decide_eq_true (Nat.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc)))
    (fun a b => by
      cases Nat.le_total a b with
      | inl h => simp [h]
      | inr h => simp [h]) l).imp (fun h => of_decide_eq_true h)

/-- Positive example (`StrongSortSpec`): merge sort satisfies it. -/
theorem natSort_strongSortSpec : StrongSortSpec natSort :=
  fun l => ⟨natSort_pairwise l, List.mergeSort_perm l _⟩

/-- Positive example (`WeakSortSpec`): merge sort satisfies it. -/
theorem natSort_weakSortSpec : WeakSortSpec natSort :=
  fun l => ⟨natSort_pairwise l, (List.mergeSort_perm l _).length_eq⟩

/-- Negative example (`WeakSortSpec`): the identity does not sort `[1, 0]`. -/
theorem id_not_weakSortSpec : ¬ WeakSortSpec id := by
  intro h
  exact absurd (h [1, 0]).1 (by decide)

/-- Lawful but unintended: the function `l ↦ replicate l.length 0` satisfies
the weak characterization. -/
theorem weirdSort_weakSortSpec : WeakSortSpec weirdSort := by
  intro l
  refine ⟨List.pairwise_replicate.2 (Or.inr (Nat.le_refl 0)), List.length_replicate⟩

/-- Negative example (`StrongSortSpec`): the weird function is rejected. -/
theorem weirdSort_not_strongSortSpec : ¬ StrongSortSpec weirdSort := by
  intro h
  have hm : (1 : Nat) ∈ weirdSort [1] := ((h [1]).2.mem_iff).2 (List.Mem.head _)
  exact absurd hm (by decide)

/-- Merge sort and the weird function differ (on `[1]`). -/
theorem natSort_ne_weirdSort : natSort ≠ weirdSort := by
  intro e
  have hm : (1 : Nat) ∈ natSort [1] := ((List.mergeSort_perm [1] _).mem_iff).2 (List.Mem.head _)
  rw [e] at hm
  exact absurd hm (by decide)

/-- Positive example (`AtMostOneLawful`, `Determines`): the characterization
"equals merge sort" determines merge sort. -/
theorem eq_natSort_determines : Determines (fun f : List Nat → List Nat => f = natSort) :=
  ⟨⟨natSort, rfl⟩, fun _ _ hf hg => hf.trans hg.symm⟩

/-- Negative example (`Determines`) and the vacuity of `AtMostOneLawful`: the
unsatisfiable characterization has at most one lawful interpretation (none)
but determines nothing. -/
theorem false_spec_atMostOneLawful_not_determines :
    AtMostOneLawful (fun _ : List Nat → List Nat => False) ∧
    ¬ Determines (fun _ : List Nat → List Nat => False) :=
  ⟨fun _ _ h _ => h.elim, fun ⟨⟨_, h⟩, _⟩ => h⟩

/-- **Main result (counterexample).** The weak characterization "the output is
sorted and has the input's length" admits two different lawful
interpretations, merge sort `natSort` and `weirdSort = l ↦ replicate l.length 0`;
hence it does not have at most one lawful interpretation. -/
theorem weakSortSpec_admits_natSort_and_weirdSort :
    WeakSortSpec natSort ∧ WeakSortSpec weirdSort ∧ natSort ≠ weirdSort ∧
    ¬ AtMostOneLawful WeakSortSpec :=
  ⟨natSort_weakSortSpec, weirdSort_weakSortSpec, natSort_ne_weirdSort,
    fun h => natSort_ne_weirdSort (h _ _ natSort_weakSortSpec weirdSort_weakSortSpec)⟩

/-- The weak characterization is satisfiable but does not determine a function
(existence without uniqueness). -/
theorem weakSortSpec_satisfiable_not_determines :
    (∃ f, WeakSortSpec f) ∧ ¬ Determines WeakSortSpec :=
  ⟨⟨natSort, natSort_weakSortSpec⟩, fun h => weakSortSpec_admits_natSort_and_weirdSort.2.2.2 h.2⟩

/-- "Nothing more": the weak characterization does not entail that `[1, 0]`
is sorted to `[0, 1]`; the weird lawful interpretation outputs `[0, 0]`. -/
theorem weakSortSpec_does_not_force_output :
    ¬ ∀ f, WeakSortSpec f → f [1, 0] = [0, 1] := by
  intro h
  exact absurd (h weirdSort weirdSort_weakSortSpec) (by decide)

/-- **Main result.** The strong characterization (sorted by `≤` and a
permutation of the input) determines merge sort: a function
`List Nat → List Nat` satisfies it iff it equals `natSort`. -/
theorem strongSortSpec_iff_eq_natSort (f : List Nat → List Nat) :
    StrongSortSpec f ↔ f = natSort := by
  constructor
  · intro hf
    funext l
    exact List.Perm.eq_of_pairwise (fun a b _ _ hab hba => Nat.le_antisymm hab hba)
      (hf l).1 (natSort_strongSortSpec l).1 ((hf l).2.trans (natSort_strongSortSpec l).2.symm)
  · rintro rfl; exact natSort_strongSortSpec

/-- Corollary: the strong characterization determines a function. -/
theorem strongSortSpec_determines : Determines StrongSortSpec :=
  ⟨⟨natSort, natSort_strongSortSpec⟩, fun f g hf hg =>
    ((strongSortSpec_iff_eq_natSort f).1 hf).trans ((strongSortSpec_iff_eq_natSort g).1 hg).symm⟩

end Toy.Extension
