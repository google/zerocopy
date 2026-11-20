/-
Core definitions for finite test suites, labeled samples, teaching sets,
disagreement sets, minimum teaching-set size, and teaching dimension, together
with the hitting-set characterization of teaching sets.
-/

namespace Toy.Witness

universe u v

/-- A hypothesis class over input domain `X` and output codomain `Y`: a
predicate selecting the admissible candidate implementations `X → Y` (for
example, functions realizable by a bounded-state machine, a restricted Boolean
formula class, or a grammar). -/
abbrev HypothesisClass (X : Type u) (Y : Type v) : Type (max u v) :=
  (X → Y) → Prop

/-- A function `h : X → Y` is consistent with (passes) a finite labeled sample
`S : List (X × Y)` if `h` produces the expected output on every input-output
pair in `S`. -/
def Consistent {X : Type u} {Y : Type v} (S : List (X × Y)) (h : X → Y) : Prop :=
  ∀ p ∈ S, h p.1 = p.2

/-- Label a finite input test suite `inputs : List X` with the outputs of `h`. -/
def labelSample {X : Type u} {Y : Type v} (h : X → Y) (inputs : List X) : List (X × Y) :=
  inputs.map (fun x => (x, h x))

theorem consistent_labelSample {X : Type u} {Y : Type v}
    (h : X → Y) (inputs : List X) :
    Consistent (labelSample h inputs) h := by
  intro p hp
  simp only [labelSample, List.mem_map] at hp
  rcases hp with ⟨x, _, rfl⟩
  rfl

theorem consistent_labelSample_iff {X : Type u} {Y : Type v}
    (h g : X → Y) (inputs : List X) :
    Consistent (labelSample h inputs) g ↔ ∀ x ∈ inputs, g x = h x := by
  constructor
  · intro hcon x hx
    exact hcon (x, h x) (List.mem_map.mpr ⟨x, hx, rfl⟩)
  · intro hall p hp
    simp only [labelSample, List.mem_map] at hp
    rcases hp with ⟨x, hx, rfl⟩
    exact hall x hx

theorem map_fst_labelSample {X : Type u} {Y : Type v}
    (h : X → Y) (inputs : List X) :
    (labelSample h inputs).map Prod.fst = inputs := by
  induction inputs with
  | nil => rfl
  | cons x xs ih =>
    simp only [labelSample, List.map_cons]
    exact congrArg (x :: ·) ih

theorem length_labelSample {X : Type u} {Y : Type v}
    (h : X → Y) (inputs : List X) :
    (labelSample h inputs).length = inputs.length := by
  simp [labelSample]

/-- Every member of hypothesis class `H` that passes labeled sample `S` is
extensionally equal to `h`. Separates the uniqueness/certification clause of
`Teaches` from the membership (`H h`) and self-consistency (`Consistent S h`)
clauses. -/
def UniqueConsistent {X : Type u} {Y : Type v}
    (H : HypothesisClass X Y) (h : X → Y) (S : List (X × Y)) : Prop :=
  ∀ g : X → Y, H g → Consistent S g → g = h

/-- A finite labeled sample `S` teaches `h` within hypothesis class `H` if
`h ∈ H`, `h` passes `S`, and `h` is the unique member of `H` passing `S`.
Captures a complete conformance suite certifying `h` against all rivals in `H`. -/
def Teaches {X : Type u} {Y : Type v}
    (H : HypothesisClass X Y) (h : X → Y) (S : List (X × Y)) : Prop :=
  H h ∧ Consistent S h ∧ UniqueConsistent H h S

theorem teaches_implies_uniqueConsistent {X : Type u} {Y : Type v}
    {H : HypothesisClass X Y} {h : X → Y} {S : List (X × Y)}
    (hT : Teaches H h S) : UniqueConsistent H h S :=
  hT.2.2

/-- The disagreement set of two functions `g, h : X → Y`: inputs `x` where
`g` and `h` produce different outputs. -/
def DisagreementSet {X : Type u} {Y : Type v} (g h : X → Y) (x : X) : Prop :=
  g x ≠ h x

/-- A finite list of test inputs `inputs` hits every disagreement set for `h`
within `H` if every distinct rival `g ∈ H` differs from `h` on at least one
input in `inputs`. -/
def HitsAllDisagreements {X : Type u} {Y : Type v}
    (H : HypothesisClass X Y) (h : X → Y) (inputs : List X) : Prop :=
  ∀ g : X → Y, H g → g ≠ h → ∃ x ∈ inputs, DisagreementSet g h x

/-- `k` is the exact minimum teaching-set size of `h` within `H`: some labeled
sample of length `k` teaches `h` within `H`, and every labeled sample teaching
`h` within `H` has length at least `k`. -/
def HasMinTeachingSize {X : Type u} {Y : Type v}
    (H : HypothesisClass X Y) (h : X → Y) (k : Nat) : Prop :=
  (∃ S : List (X × Y), S.length = k ∧ Teaches H h S) ∧
  (∀ S : List (X × Y), Teaches H h S → k ≤ S.length)

theorem hasMinTeachingSize_unique {X : Type u} {Y : Type v}
    {H : HypothesisClass X Y} {h : X → Y} {k₁ k₂ : Nat}
    (h₁ : HasMinTeachingSize H h k₁) (h₂ : HasMinTeachingSize H h k₂) :
    k₁ = k₂ := by
  rcases h₁ with ⟨⟨S₁, hlen₁, hT₁⟩, hmin₁⟩
  rcases h₂ with ⟨⟨S₂, hlen₂, hT₂⟩, hmin₂⟩
  have hle₁ : k₁ ≤ k₂ := hlen₂ ▸ hmin₁ S₂ hT₂
  have hle₂ : k₂ ≤ k₁ := hlen₁ ▸ hmin₂ S₁ hT₁
  exact Nat.le_antisymm hle₁ hle₂

/-- `d` is the exact teaching dimension of `H` (Goldman and Kearns 1995;
Shinohara and Miyano 1991): every concept in `H` has a teaching set of length
at most `d`, and some concept in `H` requires at least `d` labeled examples.

Edge cases:
- When `H` is empty (`∀ h, ¬ H h`), `HasTeachingDimension H d` holds for no `d`
  (because the second conjunct requires a witness `h ∈ H`), whereas some
  conventions define the supremum over an empty class to be `0`. For a singleton
  class (such as `MonotoneConjunctions 0`), `HasTeachingDimension H 0` holds,
  matching Doliwa et al. (2014).
- When some `h ∈ H` admits no finite teaching set (or minimum teaching-set sizes
  are unbounded across `H`), `HasTeachingDimension H d` holds for no `d`
  (corresponding to infinite teaching dimension). -/
def HasTeachingDimension {X : Type u} {Y : Type v}
    (H : HypothesisClass X Y) (d : Nat) : Prop :=
  (∀ h : X → Y, H h → ∃ S : List (X × Y), S.length ≤ d ∧ Teaches H h S) ∧
  (∃ h : X → Y, H h ∧ ∀ S : List (X × Y), Teaches H h S → d ≤ S.length)

theorem hasTeachingDimension_unique {X : Type u} {Y : Type v}
    {H : HypothesisClass X Y} {d₁ d₂ : Nat}
    (h₁ : HasTeachingDimension H d₁) (h₂ : HasTeachingDimension H d₂) :
    d₁ = d₂ := by
  rcases h₁ with ⟨hub₁, hlb₁⟩
  rcases h₂ with ⟨hub₂, hlb₂⟩
  rcases hlb₁ with ⟨h, hh, hmin₁⟩
  rcases hub₂ h hh with ⟨S, hSlen, hT⟩
  have hle₁ : d₁ ≤ d₂ := Nat.le_trans (hmin₁ S hT) hSlen
  rcases hlb₂ with ⟨h', hh', hmin₂⟩
  rcases hub₁ h' hh' with ⟨S', hS'len, hT'⟩
  have hle₂ : d₂ ≤ d₁ := Nat.le_trans (hmin₂ S' hT') hS'len
  exact Nat.le_antisymm hle₁ hle₂

/-! ### Definition Positive and Negative Examples -/

/-- The two-element hypothesis class of constant Boolean functions on `Bool`. -/
def ConstBoolClass : HypothesisClass Bool Bool :=
  fun f => f = (fun _ => false) ∨ f = (fun _ => true)

theorem consistent_pos_example :
    Consistent [(false, true), (true, false)] Bool.not := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> rfl

theorem consistent_neg_example :
    ¬ Consistent [(false, true), (true, false)] id := by
  intro hcon
  have h := hcon (false, true) (by simp)
  cases h

theorem uniqueConsistent_pos_example :
    UniqueConsistent ConstBoolClass (fun _ => true) [(false, true)] := by
  intro g hg hcon
  rcases hg with rfl | rfl
  · have h := hcon (false, true) (by simp)
    cases h
  · rfl

theorem uniqueConsistent_neg_example :
    ¬ UniqueConsistent (fun (_ : Bool → Bool) => True) (fun _ => true) [(false, true)] := by
  intro hU
  have hcon : Consistent [(false, true)] Bool.not := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl; rfl
  have heq := hU Bool.not trivial hcon
  have hval := congrFun heq true
  cases hval

theorem teaches_pos_example :
    Teaches ConstBoolClass (fun _ => true) [(false, true)] := by
  refine ⟨Or.inr rfl, ?_, uniqueConsistent_pos_example⟩
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl
  rfl

theorem teaches_neg_example :
    ¬ Teaches (fun (_ : Bool → Bool) => True) (fun _ => true) [(false, true)] :=
  fun hT => uniqueConsistent_neg_example hT.2.2

theorem disagreementSet_pos_example :
    DisagreementSet Bool.not id false := by
  intro h; cases h

theorem disagreementSet_neg_example :
    ¬ DisagreementSet id id false := by
  intro h
  exact h rfl

theorem hitsAllDisagreements_pos_example :
    HitsAllDisagreements ConstBoolClass (fun _ => true) [false] := by
  intro g hg hne
  rcases hg with rfl | rfl
  · exact ⟨false, by simp, fun h => by cases h⟩
  · exact absurd rfl hne

theorem hitsAllDisagreements_neg_example :
    ¬ HitsAllDisagreements (fun (_ : Bool → Bool) => True) (fun _ => true) [false] := by
  intro hHit
  have hne : Bool.not ≠ (fun _ => true) := by
    intro heq
    have := congrFun heq true
    cases this
  rcases hHit Bool.not trivial hne with ⟨x, hx, hdiff⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  subst hx
  exact hdiff rfl

theorem hasMinTeachingSize_pos_example :
    HasMinTeachingSize ConstBoolClass (fun _ => true) 1 := by
  constructor
  · exact ⟨[(false, true)], rfl, teaches_pos_example⟩
  · intro S hT
    cases S with
    | nil =>
      have hcon : Consistent ([] : List (Bool × Bool)) (fun _ => false) := by
        intro p hp; cases hp
      have heq := hT.2.2 (fun _ => false) (Or.inl rfl) hcon
      have := congrFun heq false
      cases this
    | cons _ _ =>
      exact Nat.succ_le_succ (Nat.zero_le _)

theorem hasMinTeachingSize_neg_example :
    ¬ HasMinTeachingSize ConstBoolClass (fun _ => true) 0 := by
  intro h0
  have heq := hasMinTeachingSize_unique h0 hasMinTeachingSize_pos_example
  cases heq

theorem hasTeachingDimension_pos_example :
    HasTeachingDimension ConstBoolClass 1 := by
  constructor
  · intro h hh
    rcases hh with rfl | rfl
    · refine ⟨[(false, false)], Nat.le_refl 1, Or.inl rfl, ?_, ?_⟩
      · intro p hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl; rfl
      · intro g hg hcon
        rcases hg with rfl | rfl
        · rfl
        · have := hcon (false, false) (by simp); cases this
    · exact ⟨[(false, true)], Nat.le_refl 1, teaches_pos_example⟩
  · exact ⟨fun _ => true, Or.inr rfl, hasMinTeachingSize_pos_example.2⟩

/-- Non-trivial negative examples for `HasTeachingDimension`: `ConstBoolClass`
has teaching dimension `1`, so neither `0` (too small) nor `2` (too large)
satisfies `HasTeachingDimension ConstBoolClass d`. -/
theorem hasTeachingDimension_neg_example_constBool_0 :
    ¬ HasTeachingDimension ConstBoolClass 0 := fun h =>
  absurd (hasTeachingDimension_unique h hasTeachingDimension_pos_example) (by decide)

theorem hasTeachingDimension_neg_example_constBool_2 :
    ¬ HasTeachingDimension ConstBoolClass 2 := fun h =>
  absurd (hasTeachingDimension_unique h hasTeachingDimension_pos_example) (by decide)

/-- Edge-case negative example: the empty class satisfies `HasTeachingDimension`
for no `d` (in particular not for `0`). -/
theorem hasTeachingDimension_neg_example_empty :
    ¬ HasTeachingDimension (fun (_ : Bool → Bool) => False) 0 := by
  intro hTD
  rcases hTD.2 with ⟨_, hfalse, _⟩
  exact hfalse

/-! ### Result 1: Hitting-Set Characterization of Teaching Sets -/

/-- A labeled sample `S` that is consistent with `h ∈ H` teaches `h` within `H`
if and only if its input coordinates hit the disagreement set `{x | g x ≠ h x}`
of every rival `g ∈ H` distinct from `h`. -/
theorem teaches_iff_hits_disagreement_sets_of_mem_of_consistent
    {X : Type u} {Y : Type v}
    (H : HypothesisClass X Y) (h : X → Y) (S : List (X × Y))
    (hh : H h) (hcon : Consistent S h) :
    Teaches H h S ↔ HitsAllDisagreements H h (S.map Prod.fst) := by
  constructor
  · intro hT g hg hne
    have hnotcon : ¬ Consistent S g := fun hcg => hne (hT.2.2 g hg hcg)
    have hex : ∃ p ∈ S, g p.1 ≠ p.2 := by
      apply Classical.byContradiction
      intro hno
      apply hnotcon
      intro p hp
      apply Classical.byContradiction
      intro hneq
      exact hno ⟨p, hp, hneq⟩
    rcases hex with ⟨p, hp, hneq⟩
    have hhp : h p.1 = p.2 := hcon p hp
    exact ⟨p.1, List.mem_map.mpr ⟨p, hp, rfl⟩, fun heq => hneq (heq.trans hhp)⟩
  · intro hHit
    refine ⟨hh, hcon, ?_⟩
    intro g hg hcg
    apply Classical.byContradiction
    intro hne
    rcases hHit g hg hne with ⟨x, hx, hdiff⟩
    simp only [List.mem_map] at hx
    rcases hx with ⟨p, hp, rfl⟩
    have h1 : g p.1 = p.2 := hcg p hp
    have h2 : h p.1 = p.2 := hcon p hp
    exact hdiff (h1.trans h2.symm)

/-- Non-vacuity witness for
`teaches_iff_hits_disagreement_sets_of_mem_of_consistent`. -/
theorem teaches_iff_hits_disagreement_sets_of_mem_of_consistent_nonvacuity :
    ConstBoolClass (fun _ => true) ∧
    Consistent [(false, true)] (fun _ => true) :=
  ⟨Or.inr rfl, teaches_pos_example.2.1⟩

/-- Tightness counterexample for `hh : H h` in
`teaches_iff_hits_disagreement_sets_of_mem_of_consistent`: `S` is consistent
with `h` and hits every disagreement set in `H`, yet `h ∉ H` so `S` does not
teach `h` within `H`. -/
theorem teaches_iff_hits_disagreement_sets_of_mem_of_consistent_ce_not_in_H :
    let H : HypothesisClass Bool Bool := fun f => f = (fun _ => false)
    let h : Bool → Bool := fun _ => true
    let S : List (Bool × Bool) := [(false, true)]
    ¬ H h ∧
    Consistent S h ∧
    ¬ (Teaches H h S ↔ HitsAllDisagreements H h (S.map Prod.fst)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    have := congrFun heq false
    cases this
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl; rfl
  · intro hiff
    have hHit : HitsAllDisagreements (fun f : Bool → Bool => f = (fun _ => false))
        (fun _ => true) (([(false, true)] : List (Bool × Bool)).map Prod.fst) := by
      intro g hg _
      subst hg
      exact ⟨false, by simp, fun h => by cases h⟩
    have hT := hiff.mpr hHit
    have := congrFun hT.1 false
    cases this

/-- Tightness counterexample for `hcon : Consistent S h` in
`teaches_iff_hits_disagreement_sets_of_mem_of_consistent`: `h ∈ H` and the
inputs of `S` hit every disagreement set in `H`, yet `S` carries the wrong
label for `h`, so `S` does not teach `h`. -/
theorem teaches_iff_hits_disagreement_sets_of_mem_of_consistent_ce_inconsistent :
    let h : Bool → Bool := fun _ => true
    let S : List (Bool × Bool) := [(false, false)]
    ConstBoolClass h ∧
    ¬ Consistent S h ∧
    ¬ (Teaches ConstBoolClass h S ↔
       HitsAllDisagreements ConstBoolClass h (S.map Prod.fst)) := by
  refine ⟨Or.inr rfl, ?_, ?_⟩
  · intro hcon
    have := hcon (false, false) (by simp)
    cases this
  · intro hiff
    have hHit : HitsAllDisagreements ConstBoolClass (fun _ => true)
        (([(false, false)] : List (Bool × Bool)).map Prod.fst) :=
      hitsAllDisagreements_pos_example
    have hT := hiff.mpr hHit
    have := hT.2.1 (false, false) (by simp)
    cases this

end Toy.Witness
