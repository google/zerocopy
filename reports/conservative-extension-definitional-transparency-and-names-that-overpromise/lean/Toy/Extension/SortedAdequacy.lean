/-
Conditional adequacy of a cheap definition. "Adjacent elements are related"
agrees with "every earlier element is related to every later one" on every
list iff the relation is transitive; for a single list, transitivity on its
elements suffices but is not necessary.
-/

namespace Toy.Extension

variable {α : Type}

/-- Adjacent elements are related: the usual cheap definition of "sorted". -/
def AdjRel (r : α → α → Prop) : List α → Prop
  | [] => True
  | [_] => True
  | a :: b :: l => r a b ∧ AdjRel r (b :: l)

instance decAdjRel (r : α → α → Prop) [DecidableRel r] : (l : List α) → Decidable (AdjRel r l)
  | [] => isTrue trivial
  | [_] => isTrue trivial
  | a :: b :: l =>
    match decAdjRel r (b :: l) with
    | isTrue h => if hab : r a b then isTrue ⟨hab, h⟩ else isFalse (fun h' => hab h'.1)
    | isFalse h => isFalse (fun h' => h h'.2)

/-- The relation is transitive. -/
def TransitiveRel (r : α → α → Prop) : Prop :=
  ∀ a b c, r a b → r b c → r a c

/-- The relation is transitive on the elements of the list `l`: the three
elements range independently over the members of `l` (repetition allowed, list
positions ignored). -/
def TransOn (r : α → α → Prop) (l : List α) : Prop :=
  ∀ a ∈ l, ∀ b ∈ l, ∀ c ∈ l, r a b → r b c → r a c

/-- Positive example (`AdjRel`): `[1, 2, 2, 3]` is adjacently `≤`. -/
theorem adjRel_le_example : AdjRel (· ≤ ·) [1, 2, 2, 3] := by decide

/-- Negative example (`AdjRel`): `[2, 1]` is not adjacently `≤`. -/
theorem adjRel_le_nonexample : ¬ AdjRel (· ≤ ·) [2, 1] := by decide

/-- Positive example (`TransitiveRel`): `≤` on `Nat` is transitive. -/
theorem le_transitiveRel : TransitiveRel (· ≤ · : Nat → Nat → Prop) :=
  fun _ _ _ => Nat.le_trans

/-- Negative example (`TransOn`): `≠` on `Nat` is not transitive on the elements
of `[0, 1]` (take `0, 1, 0`). -/
theorem ne_not_transOn : ¬ TransOn (· ≠ · : Nat → Nat → Prop) [0, 1] := by
  intro h
  exact h 0 (by decide) 1 (by decide) 0 (by decide) (by decide) (by decide) rfl

/-- Negative example (`TransitiveRel`): `≠` on `Nat` is not transitive. -/
theorem ne_not_transitiveRel : ¬ TransitiveRel (· ≠ · : Nat → Nat → Prop) :=
  fun h => h 0 1 0 (by decide) (by decide) rfl

/-- Positive example (`TransOn`): `≤` is transitive on the elements of any list. -/
theorem le_transOn (l : List Nat) : TransOn (· ≤ ·) l :=
  fun _ _ _ _ _ _ => Nat.le_trans

/-! ### Main statements -/

/-- Structural recursion behind `pairwise_implies_adjRel`. -/
theorem pairwise_implies_adjRel_aux (r : α → α → Prop) :
    (l : List α) → List.Pairwise r l → AdjRel r l
  | [], _ => trivial
  | [_], _ => trivial
  | a :: b :: t, h => by
    obtain ⟨ha, hbt⟩ := List.pairwise_cons.1 h
    exact ⟨ha b (List.Mem.head _), pairwise_implies_adjRel_aux r (b :: t) hbt⟩

/-- Proved lemma: "every earlier element is related to every later one"
implies "adjacent elements are related", for every relation and list. -/
theorem pairwise_implies_adjRel (r : α → α → Prop) (l : List α) (hpw : List.Pairwise r l) :
    AdjRel r l :=
  pairwise_implies_adjRel_aux r l hpw

/-- `hpw` in `pairwise_implies_adjRel` is tight (witness class: `≤` on `Nat`
with the two-element list `[2, 1]`): the hypothesis fails and so does the
conclusion. -/
theorem pairwise_implies_adjRel_ce :
    ¬ List.Pairwise (· ≤ · : Nat → Nat → Prop) [2, 1] ∧
    ¬ AdjRel (· ≤ · : Nat → Nat → Prop) [2, 1] :=
  ⟨by decide, adjRel_le_nonexample⟩

/-- Structural recursion behind `adjRel_iff_pairwise_of_transOn`. -/
theorem adjRel_iff_pairwise_of_transOn_aux (r : α → α → Prop) :
    (l : List α) → TransOn r l → (AdjRel r l ↔ List.Pairwise r l)
  | [], _ => ⟨fun _ => .nil, fun _ => trivial⟩
  | [_], _ => ⟨fun _ => .cons (fun _ h => nomatch h) .nil, fun _ => trivial⟩
  | a :: b :: t, htr => by
    have htr' : TransOn r (b :: t) := fun x hx y hy z hz =>
      htr x (.tail _ hx) y (.tail _ hy) z (.tail _ hz)
    constructor
    · rintro ⟨hab, hadj⟩
      have hbt := (adjRel_iff_pairwise_of_transOn_aux r (b :: t) htr').1 hadj
      refine List.pairwise_cons.2 ⟨fun x hx => ?_, hbt⟩
      cases hx with
      | head => exact hab
      | tail _ hxt =>
        have hbx := (List.pairwise_cons.1 hbt).1 x hxt
        exact htr a (.head _) b (.tail _ (.head _)) x (.tail _ (.tail _ hxt)) hab hbx
    · exact pairwise_implies_adjRel_aux r (a :: b :: t)

/-- **Main result.** For a single list, transitivity of the relation on the
list's elements suffices for the two readings to agree. -/
theorem adjRel_iff_pairwise_of_transOn (r : α → α → Prop) (l : List α) (htr : TransOn r l) :
    AdjRel r l ↔ List.Pairwise r l :=
  adjRel_iff_pairwise_of_transOn_aux r l htr

/-- **Main result (characterization).** Adjacent-relatedness and
all-pairs-relatedness agree on every list iff the relation is transitive. -/
theorem adjRel_iff_pairwise_on_all_lists_iff_transitive (r : α → α → Prop) :
    (∀ l : List α, AdjRel r l ↔ List.Pairwise r l) ↔ TransitiveRel r := by
  constructor
  · intro hall a b c hab hbc
    have hp := (hall [a, b, c]).1 ⟨hab, hbc, trivial⟩
    exact (List.pairwise_cons.1 hp).1 c (.tail _ (.head _))
  · intro htr l
    exact adjRel_iff_pairwise_of_transOn r l (fun a _ b _ c _ => htr a b c)

/-! ### Counterexamples -/

/-- `htr` in `adjRel_iff_pairwise_of_transOn` is tight (witness class: `≠` on
`Nat` with the three-element list `[0, 1, 0]`): transitivity on the list fails
and so does the conclusion (adjacently related but not all-pairs related). -/
theorem adjRel_ne_not_pairwise :
    ¬ TransOn (· ≠ · : Nat → Nat → Prop) [0, 1, 0] ∧
    ¬ (AdjRel (· ≠ · : Nat → Nat → Prop) [0, 1, 0] ↔ List.Pairwise (· ≠ ·) [0, 1, 0]) ∧
    AdjRel (· ≠ · : Nat → Nat → Prop) [0, 1, 0] ∧
    ¬ List.Pairwise (· ≠ · : Nat → Nat → Prop) [0, 1, 0] := by
  have hadj : AdjRel (· ≠ · : Nat → Nat → Prop) [0, 1, 0] := by decide
  have hnp : ¬ List.Pairwise (· ≠ · : Nat → Nat → Prop) [0, 1, 0] := by decide
  exact ⟨fun h => h 0 (by decide) 1 (by decide) 0 (by decide) (by decide) (by decide) rfl,
    fun h => hnp (h.1 hadj), hadj, hnp⟩

/-- **Main result (counterexample).** For a single list, transitivity on its elements is not
necessary: for `r = (≠)` and `[0, 1]` the two readings agree although `r` is
not transitive on `{0, 1}`. -/
theorem transOn_not_necessary_for_single_list :
    (AdjRel (· ≠ · : Nat → Nat → Prop) [0, 1] ↔ List.Pairwise (· ≠ ·) [0, 1]) ∧
    ¬ TransOn (· ≠ · : Nat → Nat → Prop) [0, 1] :=
  ⟨⟨fun _ => by decide, fun _ => by decide⟩, ne_not_transOn⟩

/-! ### Non-vacuity -/

/-- Non-vacuity for `adjRel_iff_pairwise_of_transOn` and
`adjRel_iff_pairwise_on_all_lists_iff_transitive`: `≤` on `Nat` is transitive
(hence transitive on every list), and the readings agree on `[1, 2, 2, 3]`. -/
theorem sorted_readings_nonvacuity :
    TransitiveRel (· ≤ · : Nat → Nat → Prop) ∧ TransOn (· ≤ ·) [1, 2, 2, 3] ∧
    AdjRel (· ≤ ·) [1, 2, 2, 3] ∧ List.Pairwise (· ≤ ·) [1, 2, 2, 3] :=
  ⟨le_transitiveRel, le_transOn _, by decide, by decide⟩

end Toy.Extension
