/-
Finite labeled examples and Boolean-valued deciders. Main results: over an
infinite type, a finite example list never singles out a decider within the
unrestricted class of all functions `α → Bool`; two explicit label-built
deciders agree on the examples while one of them misses the intended
predicate. Positive controls: exhaustive examples (finite type), a restricted
class (thresholds on `Nat`), and an equivalence theorem against a reference
definition, which certifies relative to that reference.
-/

namespace Toy.Extension

variable {α : Type}

/-- `d` agrees with the intended predicate `Spec` on the finite example list `E`. -/
def AgreesOn (d : α → Bool) (Spec : α → Prop) (E : List α) : Prop :=
  ∀ x ∈ E, (d x = true ↔ Spec x)

/-- `d` decides `Spec` everywhere. -/
def Decides (d : α → Bool) (Spec : α → Prop) : Prop :=
  ∀ x, (d x = true ↔ Spec x)

/-- `α` is infinite: no finite list exhausts it. -/
def InfiniteType (α : Type) : Prop :=
  ∀ l : List α, ∃ x, x ∉ l

/-- The positive examples lie in `Spec` and the negative examples lie outside it. -/
def LabelsCorrect (Spec : α → Prop) (Pos Neg : List α) : Prop :=
  (∀ x ∈ Pos, Spec x) ∧ ∀ x ∈ Neg, ¬ Spec x

/-- The decider built from the positive labels alone: "is one of the listed
positives". It is built from the list `l` and the supplied `DecidableEq α`
instance and does not consult the intended predicate; it is executable when
that instance is computable. -/
def memDecider [DecidableEq α] (l : List α) : α → Bool := fun x => decide (x ∈ l)

/-- Positive example (`Decides`): on `Bool`, `id` decides `(· = true)`. -/
theorem id_decides_eq_true : Decides (id : Bool → Bool) (· = true) := fun _ => Iff.rfl

/-- Positive and negative example (`AgreesOn`): `id` agrees with `(· = true)` on
`[true, false]`; `not` does not. -/
theorem agreesOn_examples :
    AgreesOn (id : Bool → Bool) (· = true) [true, false] ∧
    ¬ AgreesOn (not : Bool → Bool) (· = true) [true, false] := by
  refine ⟨fun x _ => Iff.rfl, fun h => ?_⟩
  exact absurd ((h true (List.Mem.head _)).2 rfl) (by decide)

/-- Negative example (`LabelsCorrect`): listing `false` as a positive example of
`(· = true)` is a labeling error. -/
theorem labelsCorrect_nonexample : ¬ LabelsCorrect (· = true) [false] ([] : List Bool) :=
  fun h => absurd (h.1 false (List.Mem.head _)) (by decide)

/-- Negative example (`Decides`): `not` does not decide `(· = true)`. -/
theorem not_not_decides_eq_true : ¬ Decides (not : Bool → Bool) (· = true) := by
  intro h
  exact absurd ((h true).2 rfl) (by decide)

/-- Positive example (`InfiniteType`): `Nat` is infinite. -/
theorem nat_infiniteType : InfiniteType Nat := by
  intro l
  refine ⟨l.foldr (· + ·) 0 + 1, fun hm => ?_⟩
  have key : ∀ (l : List Nat), ∀ x ∈ l, x ≤ l.foldr (· + ·) 0 := by
    intro l
    induction l with
    | nil => intro x hx; cases hx
    | cons a t ih =>
      intro x hx
      cases hx with
      | head => exact Nat.le_add_right _ _
      | tail _ h => exact Nat.le_trans (ih x h) (Nat.le_add_left _ _)
  exact absurd (key l _ hm) (by omega)

/-- Negative example (`InfiniteType`): `Bool` is not infinite. -/
theorem bool_not_infiniteType : ¬ InfiniteType Bool := by
  intro h
  obtain ⟨x, hx⟩ := h [true, false]
  cases x <;> exact hx (by decide)

/-! ### Main statements -/

/-- **Main result.** With correct labels and any point `x₀` outside the
examples, the two label-built deciders `memDecider Pos` and
`memDecider (x₀ :: Pos)` both agree with `Spec` on every example, and at least
one of them fails to decide `Spec` (they disagree at `x₀`). -/
theorem label_deciders_agree_on_examples_one_misses_spec [DecidableEq α]
    (Spec : α → Prop) (Pos Neg : List α) (hlab : LabelsCorrect Spec Pos Neg)
    (x₀ : α) (hx₀ : x₀ ∉ Pos ++ Neg) :
    AgreesOn (memDecider Pos) Spec (Pos ++ Neg) ∧
    AgreesOn (memDecider (x₀ :: Pos)) Spec (Pos ++ Neg) ∧
    (¬ Decides (memDecider Pos) Spec ∨ ¬ Decides (memDecider (x₀ :: Pos)) Spec) := by
  have hag1 : AgreesOn (memDecider Pos) Spec (Pos ++ Neg) := by
    intro x hx
    show decide (x ∈ Pos) = true ↔ Spec x
    rw [decide_eq_true_eq]
    rcases List.mem_append.1 hx with hp | hn
    · exact ⟨fun _ => hlab.1 x hp, fun _ => hp⟩
    · exact ⟨fun hp => absurd (hlab.1 x hp) (hlab.2 x hn), fun hs => absurd hs (hlab.2 x hn)⟩
  have hag2 : AgreesOn (memDecider (x₀ :: Pos)) Spec (Pos ++ Neg) := by
    intro x hx
    have hne : x ≠ x₀ := fun e => hx₀ (e ▸ hx)
    show decide (x ∈ x₀ :: Pos) = true ↔ Spec x
    rw [decide_eq_true_eq, List.mem_cons]
    exact ⟨fun h => h.elim (fun e => absurd e hne) (fun hp => (hag1 x hx).1 (decide_eq_true hp)),
           fun hs => Or.inr (of_decide_eq_true ((hag1 x hx).2 hs))⟩
  refine ⟨hag1, hag2, ?_⟩
  by_cases hs : Spec x₀
  · left; intro hd
    have : x₀ ∈ Pos := of_decide_eq_true ((hd x₀).2 hs)
    exact hx₀ (List.mem_append_left _ this)
  · right; intro hd
    have : Spec x₀ := (hd x₀).1 (decide_eq_true (List.Mem.head _))
    exact hs this

/-- **Main result (impossibility).** Over an infinite type, for every intended
predicate `Spec` and every finite example list `E`, some function `d : α → Bool`
from the unrestricted class of all Boolean-valued functions agrees with `Spec`
on `E` but does not decide `Spec`. -/
theorem unrestricted_decider_not_certified_by_finite_examples_of_infinite
    (hinf : InfiniteType α) (Spec : α → Prop) (E : List α) :
    ∃ d : α → Bool, AgreesOn d Spec E ∧ ¬ Decides d Spec := by
  classical
  obtain ⟨x₀, hx₀⟩ := hinf E
  refine ⟨fun x => if x = x₀ then !decide (Spec x₀) else decide (Spec x), ?_, ?_⟩
  · intro x hx
    have hne : x ≠ x₀ := fun e => hx₀ (e ▸ hx)
    simp [hne]
  · intro hd
    have h := hd x₀
    simp at h

/-! ### Tightness counterexamples (canonical form) -/

/-- `hlab` in `label_deciders_agree_on_examples_one_misses_spec` is tight
(witness class: `Bool` with one mislabeled positive example). With
`Spec = (· = true)`, `Pos = [false]`, `Neg = []` and `x₀ = true`, the other
hypothesis `x₀ ∉ Pos ++ Neg` holds and the conclusion fails. -/
theorem label_deciders_ce_labels :
    (true ∉ [false] ++ ([] : List Bool)) ∧
    ¬ (AgreesOn (memDecider [false]) (· = true) ([false] ++ []) ∧
       AgreesOn (memDecider (true :: [false])) (· = true) ([false] ++ []) ∧
       (¬ Decides (memDecider [false]) (· = true) ∨
        ¬ Decides (memDecider (true :: [false])) (· = true))) := by
  refine ⟨by decide, fun h => ?_⟩
  have := (h.1 false (by decide)).1 (by decide)
  exact absurd this (by decide)

/-- `hx₀` in `label_deciders_agree_on_examples_one_misses_spec` is tight
(witness class: `Bool` exhausted by the examples). With `Spec = (· = true)`,
`Pos = [true]`, `Neg = [false]` and `x₀ = true`, the labels are correct and
the conclusion fails: both deciders decide `Spec`. -/
theorem label_deciders_ce_point :
    LabelsCorrect (· = true) [true] [false] ∧
    ¬ (AgreesOn (memDecider [true]) (· = true) ([true] ++ [false]) ∧
       AgreesOn (memDecider (true :: [true])) (· = true) ([true] ++ [false]) ∧
       (¬ Decides (memDecider [true]) (· = true) ∨
        ¬ Decides (memDecider (true :: [true])) (· = true))) := by
  have hd1 : Decides (memDecider [true]) (· = true) := by intro x; cases x <;> decide
  have hd2 : Decides (memDecider (true :: [true])) (· = true) := by intro x; cases x <;> decide
  refine ⟨⟨?_, ?_⟩, fun h => h.2.2.elim (fun h1 => h1 hd1) (fun h2 => h2 hd2)⟩
  · intro x hx
    cases hx with
    | head => rfl
    | tail _ h => cases h
  · intro x hx
    cases hx with
    | head => decide
    | tail _ h => cases h

/-- Neither hypothesis of `label_deciders_agree_on_examples_one_misses_spec` is
necessary in general. On `Nat`: with `Spec = (· = 0)`, `Pos = Neg = [0]` (labels
incorrect) and `x₀ = 1`, the whole conclusion holds; with `Spec = True`,
`Pos = [0]`, `Neg = []` and `x₀ = 0 ∈ Pos`, the whole conclusion holds as well. -/
theorem label_deciders_conclusion_without_hypotheses :
    (¬ LabelsCorrect (· = 0 : Nat → Prop) [0] [0] ∧ ((1 : Nat) ∉ [0] ++ [0]) ∧
      AgreesOn (memDecider [0]) (· = 0 : Nat → Prop) ([0] ++ [0]) ∧
      AgreesOn (memDecider (1 :: [0])) (· = 0 : Nat → Prop) ([0] ++ [0]) ∧
      (¬ Decides (memDecider [0]) (· = 0 : Nat → Prop) ∨
       ¬ Decides (memDecider (1 :: [0])) (· = 0 : Nat → Prop))) ∧
    (LabelsCorrect (fun _ : Nat => True) [0] [] ∧ (0 : Nat) ∈ ([0] ++ ([] : List Nat)) ∧
      AgreesOn (memDecider [0]) (fun _ : Nat => True) ([0] ++ []) ∧
      AgreesOn (memDecider (0 :: [0])) (fun _ : Nat => True) ([0] ++ []) ∧
      (¬ Decides (memDecider [0]) (fun _ : Nat => True) ∨
       ¬ Decides (memDecider (0 :: [0])) (fun _ : Nat => True))) := by
  refine ⟨⟨fun h => h.2 0 (.head _) rfl, by decide, ?_, ?_, Or.inr fun hd => ?_⟩,
    ⟨⟨fun _ _ => trivial, fun _ h => nomatch h⟩, by decide, ?_, ?_, Or.inl fun hd => ?_⟩⟩
  · intro x hx
    cases hx with
    | head => decide
    | tail _ hx => cases hx with | head => decide | tail _ h => cases h
  · intro x hx
    cases hx with
    | head => decide
    | tail _ hx => cases hx with | head => decide | tail _ h => cases h
  · exact absurd ((hd 1).1 (by decide)) (by decide)
  · intro x hx; cases hx with | head => exact ⟨fun _ => trivial, fun _ => by decide⟩ | tail _ h => cases h
  · intro x hx; cases hx with | head => exact ⟨fun _ => trivial, fun _ => by decide⟩ | tail _ h => cases h
  · have h1 : decide ((1 : Nat) ∈ ([0] : List Nat)) = true := (hd 1).2 trivial
    exact absurd h1 (by decide)

/-- `hinf` in `unrestricted_decider_not_certified_by_finite_examples_of_infinite`
is tight (witness class: the finite type `Bool`): with the exhaustive example
list `[true, false]`, every decider agreeing on the examples decides `Spec`. -/
theorem unrestricted_decider_not_certified_ce_finite :
    ¬ InfiniteType Bool ∧
    ¬ ∃ d : Bool → Bool, AgreesOn d (· = true) [true, false] ∧ ¬ Decides d (· = true) := by
  refine ⟨bool_not_infiniteType, ?_⟩
  rintro ⟨d, hag, hnd⟩
  exact hnd (fun x => hag x (by cases x <;> decide))

/-! ### Positive controls and non-vacuity -/

/-- Positive control (finite domain): on a domain exhausted by the examples,
agreement on the examples certifies the decider. -/
theorem exhaustive_examples_certify (d : α → Bool) (Spec : α → Prop) (E : List α)
    (hall : ∀ x, x ∈ E) (hag : AgreesOn d Spec E) : Decides d Spec :=
  fun x => hag x (hall x)

/-- Threshold deciders `x ↦ (k ≤ x)` on `Nat`, a restricted hypothesis class. -/
def thresholdDecider (k : Nat) : Nat → Bool := fun x => decide (k ≤ x)

/-- Positive control (restricted class on an infinite domain): within the
threshold class, agreement with `(k ≤ ·)` on the two examples `k - 1` and `k`
certifies the decider. -/
theorem threshold_examples_certify (j k : Nat)
    (hag : AgreesOn (thresholdDecider j) (fun x => k ≤ x) [k - 1, k]) :
    Decides (thresholdDecider j) (fun x => k ≤ x) := by
  have h1 := hag (k - 1) (List.Mem.head _)
  have h2 := hag k (List.Mem.tail _ (List.Mem.head _))
  simp only [thresholdDecider, decide_eq_true_eq] at h1 h2
  intro x
  simp only [thresholdDecider, decide_eq_true_eq]
  omega

/-- Positive control: an equivalence theorem against a reference definition
`ref` certifies `d` against `Spec` when `ref` matches `Spec`. -/
theorem reference_equivalence_certifies (d : α → Bool) (ref Spec : α → Prop)
    (hd : ∀ x, d x = true ↔ ref x) (href : ∀ x, ref x ↔ Spec x) : Decides d Spec :=
  fun x => (hd x).trans (href x)

/-- Given `d` proved equivalent to a reference `ref`, `d` decides `Spec` iff
`ref` matches `Spec`: the trust moves to `ref`. -/
theorem decides_iff_reference_matches_spec (d : α → Bool) (ref Spec : α → Prop)
    (hd : ∀ x, d x = true ↔ ref x) :
    Decides d Spec ↔ (∀ x, ref x ↔ Spec x) :=
  ⟨fun h x => (hd x).symm.trans (h x), reference_equivalence_certifies d ref Spec hd⟩

/-- The certificate is only relative to the reference: a decider can be proved
equivalent to a wrong reference and still fail to decide the intended `Spec`. -/
theorem reference_equivalence_moves_trust :
    Decides (fun _ : Bool => true) (fun _ => True) ∧
    ¬ Decides (fun _ : Bool => true) (· = true) := by
  refine ⟨fun _ => ⟨fun _ => trivial, fun _ => rfl⟩, fun h => ?_⟩
  exact absurd ((h false).1 rfl) (by decide)

/-- Non-vacuity for `label_deciders_agree_on_examples_one_misses_spec`: on
`Nat` with `Spec = even`, positives `[0, 2]`, negatives `[1]` and `x₀ = 4`, all
hypotheses hold. -/
theorem label_deciders_nonvacuity :
    LabelsCorrect (fun n : Nat => n % 2 = 0) [0, 2] [1] ∧ (4 : Nat) ∉ [0, 2] ++ [1] := by
  refine ⟨⟨fun x hx => ?_, fun x hx => ?_⟩, by decide⟩
  · simp only [List.mem_cons, List.not_mem_nil] at hx
    rcases hx with rfl | rfl | h
    · rfl
    · rfl
    · exact h.elim
  · simp only [List.mem_cons, List.not_mem_nil] at hx
    rcases hx with rfl | h
    · decide
    · exact h.elim

/-- Non-vacuity for `unrestricted_decider_not_certified_by_finite_examples_of_infinite`:
`Nat` is infinite. -/
theorem unrestricted_decider_not_certified_nonvacuity : InfiniteType Nat := nat_infiniteType

/-- Non-vacuity for `threshold_examples_certify`: the threshold `3` agrees with
`(3 ≤ ·)` on `[2, 3]`. -/
theorem threshold_examples_certify_nonvacuity :
    AgreesOn (thresholdDecider 3) (fun x => 3 ≤ x) [3 - 1, 3] := by
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil] at hx
  rcases hx with rfl | rfl | h
  · decide
  · decide
  · exact h.elim

end Toy.Extension
