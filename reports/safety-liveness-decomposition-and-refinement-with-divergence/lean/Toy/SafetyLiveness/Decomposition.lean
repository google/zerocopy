import Toy.SafetyLiveness.Core

/-!
# Alpern–Schneider decomposition and the safety/liveness uniqueness edge

This module establishes the topological safety/liveness decomposition of
Alpern and Schneider (1985) over `InfTrace α`:

- Unconditional closure and intersection lemmas holding over arbitrary
  alphabets `α` (including `Empty`): `closure_isSafety`,
  `closure_subset_of_isSafety`, `closure_minimal_of_isSafety`,
  `propInter_closure_livenessPart_eq`, and `eq_univ_of_isSafety_of_isLiveness`.
- `alpernSchneider_decomposition_of_nonempty`: over any nonempty alphabet `α`,
  every trace property `P` equals `PropInter (Closure P) (LivenessPart P)` with
  `IsSafety (Closure P)` and `IsLiveness (LivenessPart P)`.
- `isSafety_iff_closure_eq`: a trace property is a safety property if and only
  if it equals its own prefix closure.
- `isSafety_and_isLiveness_iff_eq_univ_of_nonempty`: over any nonempty alphabet,
  a trace property is both safety and liveness if and only if it equals `UnivProp`.
- Tightness counterexamples for `Nonempty α` on `Empty` (cf. Friedrich, 2004,
  `LList_Topology`), non-vacuity witnesses, and non-uniqueness of components.
-/

namespace Toy.SafetyLiveness

universe u

/-! ### Unconditional closure, minimality, and forward-uniqueness lemmas -/

/-- The prefix closure `Closure P` of any trace property `P` is unconditionally
a safety property (requiring neither `Nonempty α` nor `IsSafety P`). -/
theorem closure_isSafety {α : Type u} (P : TraceProp α) : IsSafety (Closure P) := by
  intro s hs
  have hex : ∃ n : Nat, ¬ ∃ s' : InfTrace α, HasPrefix s' (takePrefix s n) ∧ P s' := by
    apply Classical.byContradiction
    intro h
    apply hs
    intro n
    apply Classical.byContradiction
    intro h'
    exact h ⟨n, h'⟩
  rcases hex with ⟨n, hn⟩
  refine ⟨n, fun s' hpre hcl => hn ?_⟩
  rcases hcl n with ⟨s'', hpre'', hP⟩
  have heq : takePrefix s' n = takePrefix s n := by
    have h := takePrefix_eq_of_hasPrefix hpre
    rwa [takePrefix_length] at h
  rw [heq] at hpre''
  exact ⟨s'', hpre'', hP⟩

/-- Every safety property `P` contains its own prefix closure `Closure P`. -/
theorem closure_subset_of_isSafety {α : Type u} {P : TraceProp α} (hSafe : IsSafety P) :
    ∀ s : InfTrace α, Closure P s → P s := by
  intro s hcl
  apply Classical.byContradiction
  intro hnot
  rcases hSafe s hnot with ⟨n, hn⟩
  rcases hcl n with ⟨s', hpre, hP⟩
  exact hn s' hpre hP

/-- Minimality of `Closure P`: `Closure P` is contained in every safety
property `S` that contains `P` (so `Closure P` is the smallest safety superset
of `P`). -/
theorem closure_minimal_of_isSafety {α : Type u} {P S : TraceProp α}
    (hSafe : IsSafety S) (hSub : ∀ s : InfTrace α, P s → S s) :
    ∀ s : InfTrace α, Closure P s → S s :=
  fun s hcl => closure_subset_of_isSafety hSafe s (closure_mono hSub s hcl)

/-- Unconditional intersection identity of the Alpern–Schneider components:
for every alphabet `α` (including `Empty`) and every `P : TraceProp α`,
`PropInter (Closure P) (LivenessPart P) = P`. -/
theorem propInter_closure_livenessPart_eq {α : Type u} (P : TraceProp α) :
    PropInter (Closure P) (LivenessPart P) = P := by
  funext s
  apply propext
  constructor
  · rintro ⟨hcl, hP | hncl⟩
    · exact hP
    · exact absurd hcl hncl
  · intro hP
    exact ⟨subset_closure hP, Or.inl hP⟩

/-- Forward direction of the safety/liveness uniqueness edge: over any alphabet
`α` (without requiring `Nonempty α`), any trace property that is both safety
and liveness equals `UnivProp`. -/
theorem eq_univ_of_isSafety_of_isLiveness
    {α : Type u} {P : TraceProp α}
    (hSafe : IsSafety P) (hLive : IsLiveness P) :
    P = UnivProp := by
  funext s
  apply propext
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  apply Classical.byContradiction
  intro hnot
  rcases hSafe s hnot with ⟨n, hn⟩
  rcases hLive (takePrefix s n) with ⟨s', hpre, hP⟩
  exact hn s' hpre hP

/-- Liveness of the explicit liveness component: over a nonempty alphabet `α`,
`LivenessPart P` is a liveness property for every `P`. Any finite prefix `w`
either extends to a trace in `P`, or extends (by a constant tail) to a trace
outside `Closure P`. -/
theorem isLiveness_livenessPart_of_nonempty {α : Type u} (hα : Nonempty α) (P : TraceProp α) :
    IsLiveness (LivenessPart P) := by
  rcases hα with ⟨a⟩
  intro w
  by_cases h : ∃ s : InfTrace α, HasPrefix s w ∧ P s
  · rcases h with ⟨s, hs, hP⟩
    exact ⟨s, hs, Or.inl hP⟩
  · refine ⟨appendPrefix w (fun _ => a), hasPrefix_appendPrefix w _, Or.inr ?_⟩
    intro hcl
    rcases hcl w.length with ⟨s', hpre, hP⟩
    rw [takePrefix_eq_of_hasPrefix (hasPrefix_appendPrefix w _)] at hpre
    exact h ⟨s', hpre, hP⟩

/-! ### Decomposition, closure characterization, and uniqueness theorems -/

/-- Alpern–Schneider decomposition: over a nonempty alphabet `α`, every trace
property `P` equals the intersection of its topological closure `Closure P`
(a safety property) and its explicit liveness component `LivenessPart P`
(a liveness property). Note that `IsSafety (Closure P)` and
`PropInter (Closure P) (LivenessPart P) = P` hold unconditionally without
`Nonempty α` via `closure_isSafety` and `propInter_closure_livenessPart_eq`;
`Nonempty α` is needed solely for `IsLiveness (LivenessPart P)`. -/
theorem alpernSchneider_decomposition_of_nonempty
    {α : Type u} (hα : Nonempty α) (P : TraceProp α) :
    IsSafety (Closure P) ∧ IsLiveness (LivenessPart P) ∧
      PropInter (Closure P) (LivenessPart P) = P :=
  ⟨closure_isSafety P, isLiveness_livenessPart_of_nonempty hα P,
    propInter_closure_livenessPart_eq P⟩

/-- Topological characterization of safety: a trace property `P` is a safety
property if and only if it equals its prefix closure `Closure P`. Holds over
any alphabet `α` (including `Empty`). -/
theorem isSafety_iff_closure_eq
    {α : Type u} (P : TraceProp α) :
    IsSafety P ↔ Closure P = P := by
  constructor
  · intro hS
    funext s
    exact propext ⟨closure_subset_of_isSafety hS s, subset_closure⟩
  · intro h
    have := closure_isSafety P
    rwa [h] at this

/-- Safety/liveness uniqueness characterization: over a nonempty alphabet `α`,
a trace property is both safety and liveness if and only if it is `UnivProp`.
(The forward implication `IsSafety P → IsLiveness P → P = UnivProp` holds
without `Nonempty α` via `eq_univ_of_isSafety_of_isLiveness`.) -/
theorem isSafety_and_isLiveness_iff_eq_univ_of_nonempty
    {α : Type u} (hα : Nonempty α) (P : TraceProp α) :
    (IsSafety P ∧ IsLiveness P) ↔ P = UnivProp := by
  constructor
  · rintro ⟨hS, hL⟩
    exact eq_univ_of_isSafety_of_isLiveness hS hL
  · rintro rfl
    exact ⟨univProp_isSafety, univProp_isLiveness hα⟩

/-! ### Class disjointness is not entailment -/

/-- The safety and liveness *classes* meet only in `UnivProp`, but a safety
property can still be *contained in* a nontrivial liveness property. On `Bool`,
the safety property `AlwaysFalse` is contained in the liveness property
`EventuallyFalse`, which is not `UnivProp`; so the system `{constFalse}`, which
satisfies `AlwaysFalse`, also satisfies `EventuallyFalse`. -/
theorem alwaysFalse_safety_entails_nontrivial_liveness_eventuallyFalse :
    IsSafety AlwaysFalse ∧ IsLiveness EventuallyFalse ∧ EventuallyFalse ≠ UnivProp ∧
      (∀ s : InfTrace Bool, AlwaysFalse s → EventuallyFalse s) ∧
      Satisfies (fun s => s = constFalse) AlwaysFalse ∧
      Satisfies (fun s => s = constFalse) EventuallyFalse := by
  refine ⟨alwaysFalse_isSafety, eventuallyFalse_isLiveness, ?_, fun s h => ⟨0, h 0⟩,
    satisfies_pos_constFalse, fun s hs => ⟨0, by subst hs; rfl⟩⟩
  intro h
  have hEv : EventuallyFalse constTrue := (congrFun h constTrue).symm ▸ trivial
  rcases hEv with ⟨i, hi⟩
  simp [constTrue] at hi

/-! ### Non-vacuity witnesses -/

/-- Non-vacuity witness for `alpernSchneider_decomposition_of_nonempty`: on the
nonempty alphabet `Bool`, `StartsTrueAndEventuallyFalse` is a nontrivial
property that is neither safety nor liveness. -/
theorem alpernSchneider_nonvacuity :
    Nonempty Bool ∧
      ¬ IsSafety StartsTrueAndEventuallyFalse ∧
      ¬ IsLiveness StartsTrueAndEventuallyFalse :=
  ⟨⟨false⟩, startsTrueAndEventuallyFalse_neither_safety_nor_liveness⟩

/-- Non-vacuity witness for `isSafety_iff_closure_eq`: on `Bool`, `AlwaysFalse`
is a nontrivial safety property and `EventuallyTrue` is a non-safety property. -/
theorem isSafety_iff_closure_eq_nonvacuity :
    IsSafety AlwaysFalse ∧ ¬ IsSafety EventuallyTrue :=
  ⟨alwaysFalse_isSafety, eventuallyTrue_not_isSafety⟩

/-- Non-vacuity witness for `eq_univ_of_isSafety_of_isLiveness`: on `Bool`,
`UnivProp` satisfies both `IsSafety` and `IsLiveness`. -/
theorem eq_univ_of_isSafety_of_isLiveness_nonvacuity :
    IsSafety (UnivProp : TraceProp Bool) ∧ IsLiveness (UnivProp : TraceProp Bool) :=
  ⟨univProp_isSafety, univProp_isLiveness ⟨false⟩⟩

/-- Non-vacuity witness for `isSafety_and_isLiveness_iff_eq_univ_of_nonempty`:
`Bool` is nonempty, `UnivProp` satisfies both sides, and `AlwaysFalse`
falsifies both sides. -/
theorem isSafety_and_isLiveness_iff_eq_univ_nonvacuity :
    Nonempty Bool ∧
      (IsSafety (UnivProp : TraceProp Bool) ∧ IsLiveness (UnivProp : TraceProp Bool)) ∧
      (¬ IsLiveness AlwaysFalse ∧ AlwaysFalse ≠ UnivProp) := by
  refine ⟨⟨false⟩, ⟨univProp_isSafety, univProp_isLiveness ⟨false⟩⟩,
    alwaysFalse_not_isLiveness, ?_⟩
  intro h
  have h0 := congrFun h constTrue
  have hAll : AlwaysFalse constTrue := h0.symm ▸ trivial
  exact traceProp_neg_alwaysFalse hAll

/-! ### Tightness counterexamples -/

/-- Over `Empty`, no trace property is live because the empty prefix `[]` has
no infinite extension. -/
theorem emptyAlphabet_no_liveness (L : TraceProp Empty) : ¬ IsLiveness L := by
  intro hLive
  rcases hLive [] with ⟨s, _, _⟩
  exact Empty.elim (s 0)

/-- Tightness counterexample for `hα : Nonempty α` in
`alpernSchneider_decomposition_of_nonempty`: on `α = Empty`, the decomposition
conclusion fails for `EmptyProp` because no property over `Empty` is live. -/
theorem emptyAlphabet_tight_alpernSchneider :
    ¬ (IsSafety (Closure (EmptyProp : TraceProp Empty)) ∧
       IsLiveness (LivenessPart (EmptyProp : TraceProp Empty)) ∧
       PropInter (Closure (EmptyProp : TraceProp Empty))
         (LivenessPart (EmptyProp : TraceProp Empty)) = EmptyProp) := by
  rintro ⟨_, hLive, _⟩
  exact emptyAlphabet_no_liveness (LivenessPart EmptyProp) hLive

/-- Tightness counterexample for `hSafe : IsSafety P` in
`eq_univ_of_isSafety_of_isLiveness`: `EventuallyTrue` on `Bool` satisfies
`IsLiveness` yet is not `UnivProp`. -/
theorem eventuallyTrue_tight_safety_of_unique :
    IsLiveness EventuallyTrue ∧ EventuallyTrue ≠ UnivProp := by
  refine ⟨eventuallyTrue_isLiveness, ?_⟩
  intro h
  have h0 := congrFun h constFalse
  have hEv : EventuallyTrue constFalse := h0.symm ▸ trivial
  rcases hEv with ⟨i, hi⟩
  simp [constFalse] at hi

/-- Tightness counterexample for `hLive : IsLiveness P` in
`eq_univ_of_isSafety_of_isLiveness`: `AlwaysFalse` on `Bool` satisfies
`IsSafety` yet is not `UnivProp`. -/
theorem alwaysFalse_tight_liveness_of_unique :
    IsSafety AlwaysFalse ∧ AlwaysFalse ≠ UnivProp := by
  refine ⟨alwaysFalse_isSafety, ?_⟩
  intro h
  have h0 := congrFun h constTrue
  have hAll : AlwaysFalse constTrue := h0.symm ▸ trivial
  exact traceProp_neg_alwaysFalse hAll

/-- Tightness counterexample for `hα : Nonempty α` in
`isSafety_and_isLiveness_iff_eq_univ_of_nonempty`: on `α = Empty`,
`UnivProp = UnivProp` holds trivially, yet `IsLiveness UnivProp` is false. -/
theorem emptyAlphabet_tight_safety_liveness_iff_univ :
    ¬ ((IsSafety (UnivProp : TraceProp Empty) ∧ IsLiveness (UnivProp : TraceProp Empty)) ↔
       (UnivProp : TraceProp Empty) = UnivProp) := by
  intro hIff
  exact emptyAlphabet_no_liveness UnivProp (hIff.mpr rfl).2

/-! ### Non-uniqueness of Alpern–Schneider decompositions -/

/-- A non-universal liveness property used to witness non-uniqueness of the
liveness component of an Alpern–Schneider decomposition: either always `false`,
or two consecutive `true`s occur somewhere. -/
def AlwaysFalseOrTwoTrues : TraceProp Bool :=
  fun s => AlwaysFalse s ∨ ∃ i : Nat, s i = true ∧ s (i + 1) = true

/-- Non-uniqueness witness for Alpern–Schneider decomposition:
1. Even fixing the safety component to `Closure AlwaysFalse = AlwaysFalse`, two
   distinct liveness properties (`UnivProp` and `AlwaysFalseOrTwoTrues`) both
   intersect `AlwaysFalse` to `AlwaysFalse`.
2. Without machine closure, even the safety component is not unique: `StartsTrue`
   equals both `PropInter StartsTrue UnivProp` and
   `PropInter StartsFalseStaysFalse EventuallyTrue`, where both pairs are
   `(safety, liveness)` and `StartsFalseStaysFalse ≠ StartsTrue`. -/
theorem alpernSchneider_nonunique_components :
    (IsSafety AlwaysFalse ∧ IsLiveness (UnivProp : TraceProp Bool) ∧ IsLiveness AlwaysFalseOrTwoTrues ∧
      PropInter AlwaysFalse UnivProp = AlwaysFalse ∧
      PropInter AlwaysFalse AlwaysFalseOrTwoTrues = AlwaysFalse ∧
      (UnivProp : TraceProp Bool) ≠ AlwaysFalseOrTwoTrues) ∧
    (IsSafety StartsTrue ∧ IsSafety StartsFalseStaysFalse ∧ IsLiveness EventuallyTrue ∧
      PropInter StartsTrue UnivProp = StartsTrue ∧
      PropInter StartsFalseStaysFalse EventuallyTrue = StartsTrue ∧
      StartsFalseStaysFalse ≠ StartsTrue) := by
  constructor
  · refine ⟨alwaysFalse_isSafety, univProp_isLiveness ⟨false⟩, ?_, ?_, ?_, ?_⟩
    · intro u
      refine ⟨appendPrefix u constTrue, hasPrefix_appendPrefix u constTrue, Or.inr ⟨u.length, ?_, ?_⟩⟩
      · simp [appendPrefix, constTrue]
      · have hlt : ¬ (u.length + 1 < u.length) := by omega
        simp [appendPrefix, hlt, constTrue]
    · funext s
      exact propext ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩
    · funext s
      exact propext ⟨fun h => h.1, fun h => ⟨h, Or.inl h⟩⟩
    · intro heq
      let s1 : InfTrace Bool := appendPrefix [true] constFalse
      have hmem : AlwaysFalseOrTwoTrues s1 := (congrFun heq s1) ▸ trivial
      rcases hmem with hAll | ⟨i, hi1, hi2⟩
      · have h0 := hAll 0
        simp [s1, appendPrefix] at h0
      · cases i with
        | zero =>
          simp [s1, appendPrefix, constFalse] at hi2
        | succ k =>
          simp [s1, appendPrefix, constFalse] at hi1
  · refine ⟨startsTrue_isSafety, startsFalseStaysFalse_isSafety, eventuallyTrue_isLiveness, ?_, ?_, ?_⟩
    · funext s
      exact propext ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩
    · funext s
      apply propext
      constructor
      · rintro ⟨hS, i, hi⟩
        cases h0 : s 0 with
        | true => exact h0
        | false =>
          have hf := hS h0 i
          rw [hf] at hi
          contradiction
      · intro h0
        refine ⟨fun hf => by rw [h0] at hf; contradiction, 0, h0⟩
    · intro heq
      have hmem : StartsTrue constFalse := (congrFun heq constFalse) ▸ (fun _ => traceProp_pos_alwaysFalse)
      simp [StartsTrue, constFalse] at hmem

end Toy.SafetyLiveness
