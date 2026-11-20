import Toy.SafetyLiveness.Core
import Toy.SafetyLiveness.Decomposition

/-!
# Machine closure of safety/liveness specifications

Following Apt, Francez, and Katz (1988, *feasibility*), Dederichs and Weber
(1990, *relative liveness*), and Abadi and Lamport (1991, §2.3, Lemma 1), a
specification pair `(S, L)` over `InfTrace α` is **machine-closed** when every
finite prefix of an infinite trace in `S` can be extended to an infinite trace
in `PropInter S L` — equivalently, when `S` is a safety property, `L` imposes no
hidden safety constraints beyond `S` (`Closure (PropInter S L) = S`).

Two deliberate modeling distinctions relative to Abadi and Lamport (1991, §§2.2–2.3):
1. Trace properties are not restricted to stuttering-closed predicates.
2. Abadi and Lamport define machine closure for a state machine `M` (whose runs
   can stutter infinitely) as `M = Closure (M ∩ L)` and derive prefix extension
   as Lemma 1; here `MachineClosed S L` is defined directly by prefix extension
   over infinite traces in `S`. Consequently, any deadlocked finite run `u` of a
   transition system that has no infinite continuation in `S` falsifies
   `∃ s, HasPrefix s u ∧ S s` and is invisible to `MachineClosed S L` unless
   deadlocks are modeled via infinite stuttering or explicit finite traces.
-/

namespace Toy.SafetyLiveness

universe u

/-- Machine closure of a specification pair `(S, L)`: every finite prefix of
some infinite trace in `S` can be extended to an infinite trace satisfying both
`S` and `L`. Adopts the prefix-extension formulation (Apt, Francez, and Katz,
1988; Abadi and Lamport, 1991, §2.3, Lemma 1); note that finite prefixes with no
infinite continuation in `S` (such as unmodeled transition-system deadlocks) are
vacuously ignored. -/
def MachineClosed {α : Type u} (S L : TraceProp α) : Prop :=
  ∀ u : List α, (∃ s : InfTrace α, HasPrefix s u ∧ S s) →
    ∃ s' : InfTrace α, HasPrefix s' u ∧ S s' ∧ L s'

/-! ### Positive and negative examples for `MachineClosed` -/

/-- Positive example for `MachineClosed`: `(StartsTrue, EventuallyFalse)` on
`Bool` is machine-closed, with nontrivial safety part `StartsTrue` and
nontrivial liveness part `EventuallyFalse`. -/
theorem startsTrue_eventuallyFalse_machineClosed :
    MachineClosed StartsTrue EventuallyFalse := by
  intro u hu
  rcases hu with ⟨s, hpre, h0⟩
  cases u with
  | nil =>
    refine ⟨appendPrefix [true] constFalse, hasPrefix_nil _, rfl, 1, rfl⟩
  | cons a t =>
    have ha : a = true := by
      have hpre0 := hpre 0 (by simp)
      simp at hpre0
      exact hpre0.symm.trans h0
    subst ha
    refine ⟨appendPrefix (true :: t) constFalse, hasPrefix_appendPrefix _ _, ?_,
      (true :: t).length, ?_⟩
    · simp [StartsTrue, appendPrefix]
    · simp [appendPrefix, constFalse]

/-- Negative example for `MachineClosed`: `(StartsFalseStaysFalse, EventuallyTrue)`
on `Bool` is NOT machine-closed, because the finite prefix `[false]` extends to
`constFalse` in `StartsFalseStaysFalse` yet cannot be extended to satisfy both
`StartsFalseStaysFalse` and `EventuallyTrue`. -/
theorem startsFalseStaysFalse_eventuallyTrue_not_machineClosed :
    ¬ MachineClosed StartsFalseStaysFalse EventuallyTrue := by
  intro hMC
  have hExt : ∃ s : InfTrace Bool, HasPrefix s [false] ∧ StartsFalseStaysFalse s := by
    refine ⟨constFalse, ?_, fun _ => traceProp_pos_alwaysFalse⟩
    intro i hi
    match i with
    | 0 => rfl
    | n + 1 => simp at hi
  rcases hMC [false] hExt with ⟨s', hpre', hS', i, hi⟩
  have h0 : s' 0 = false := hpre' 0 (by simp)
  have hf : s' i = false := hS' h0 i
  rw [hf] at hi
  contradiction

/-! ### Specialization helper lemma under `IsSafety S` -/

/-- Specialization under `IsSafety S`: for any safety property `S` and arbitrary
supplementary property `L` (`IsLiveness L` is not needed), `(S, L)` is
machine-closed if and only if `Closure (PropInter S L) = S`. -/
theorem machineClosed_iff_closure_propInter_eq_of_isSafety
    {α : Type u} {S L : TraceProp α} (hS : IsSafety S) :
    MachineClosed S L ↔ Closure (PropInter S L) = S := by
  constructor
  · intro hMC
    funext s
    apply propext
    constructor
    · intro hcl
      exact closure_minimal_of_isSafety hS (fun _ h => h.1) s hcl
    · intro hs n
      exact hMC (takePrefix s n) ⟨s, hasPrefix_takePrefix s n, hs⟩
  · rintro h u ⟨s, hpre, hs⟩
    have hcl : Closure (PropInter S L) s := (congrFun h s).symm ▸ hs
    rcases hcl u.length with ⟨s', hpre', hSL⟩
    rw [takePrefix_eq_of_hasPrefix hpre] at hpre'
    exact ⟨s', hpre', hSL.1, hSL.2⟩

/-! ### Machine-closure characterization and canonical decomposition -/

/-- Exact hypothesis-free characterization of `Closure (PropInter S L) = S`:
for arbitrary trace properties `S` and `L` over any alphabet `α`,
`Closure (PropInter S L) = S` holds if and only if `S` is a safety property and
`(S, L)` is machine-closed. -/
theorem closure_propInter_eq_iff_isSafety_and_machineClosed
    {α : Type u} (S L : TraceProp α) :
    Closure (PropInter S L) = S ↔ IsSafety S ∧ MachineClosed S L := by
  constructor
  · intro h
    have hS : IsSafety S := by
      have := closure_isSafety (PropInter S L)
      rwa [h] at this
    exact ⟨hS, (machineClosed_iff_closure_propInter_eq_of_isSafety hS).mpr h⟩
  · rintro ⟨hS, hMC⟩
    exact (machineClosed_iff_closure_propInter_eq_of_isSafety hS).mp hMC

/-- The canonical Alpern–Schneider decomposition pair
`(Closure P, LivenessPart P)` is unconditionally machine-closed (for arbitrary
`α` and `P`). -/
theorem alpernSchneider_is_machineClosed
    {α : Type u} (P : TraceProp α) :
    MachineClosed (Closure P) (LivenessPart P) := by
  rintro w ⟨s, hs, hcl⟩
  rcases hcl w.length with ⟨s', hpre, hP⟩
  rw [takePrefix_eq_of_hasPrefix hs] at hpre
  exact ⟨s', hpre, subset_closure hP, Or.inl hP⟩

/-! ### Satisfiable non-machine-closed counterexample and non-conjunction witness -/

/-- Satisfiable non-machine-closed counterexample: `(StartsFalseStaysFalse, EventuallyTrue)`
on `Bool` consists of a safety property and a liveness property whose
conjunction explicitly admits `constTrue`, yet the pair is not machine-closed
and `Closure (PropInter StartsFalseStaysFalse EventuallyTrue) ≠ StartsFalseStaysFalse`. -/
theorem nonMachineClosed_consistent_spec_counterexample :
    IsSafety StartsFalseStaysFalse ∧
      IsLiveness EventuallyTrue ∧
      PropInter StartsFalseStaysFalse EventuallyTrue constTrue ∧
      ¬ MachineClosed StartsFalseStaysFalse EventuallyTrue ∧
      Closure (PropInter StartsFalseStaysFalse EventuallyTrue) ≠ StartsFalseStaysFalse := by
  refine ⟨startsFalseStaysFalse_isSafety, eventuallyTrue_isLiveness, ?_,
    startsFalseStaysFalse_eventuallyTrue_not_machineClosed, ?_⟩
  · refine ⟨?_, 0, rfl⟩
    intro hf
    simp [constTrue] at hf
  · intro heq
    have hInCl : Closure (PropInter StartsFalseStaysFalse EventuallyTrue) constFalse :=
      (congrFun heq constFalse) ▸ (fun _ => traceProp_pos_alwaysFalse)
    rcases hInCl 1 with ⟨s', hpre', hS', i, hi⟩
    have h0 : s' 0 = false := (hasPrefix_takePrefix_iff constFalse s' 1).mp hpre' 0 (by decide)
    have hf : s' i = false := hS' h0 i
    rw [hf] at hi
    contradiction

/-- The effective safety hull of the non-machine-closed pair
`(StartsFalseStaysFalse, EventuallyTrue)` is `StartsTrue`: the conjunction itself
equals `StartsTrue` (a trace starting with `false` must stay `false` and so never
observes `true`), and `StartsTrue` is a safety property, hence its own closure. -/
theorem closure_propInter_startsFalseStaysFalse_eventuallyTrue_eq_startsTrue :
    PropInter StartsFalseStaysFalse EventuallyTrue = StartsTrue ∧
      Closure (PropInter StartsFalseStaysFalse EventuallyTrue) = StartsTrue := by
  have hEq : PropInter StartsFalseStaysFalse EventuallyTrue = StartsTrue := by
    funext s
    apply propext
    constructor
    · rintro ⟨hS, i, hi⟩
      cases h0 : s 0 with
      | false =>
        have hf := hS h0 i
        rw [hf] at hi
        contradiction
      | true => exact h0
    · intro h0
      refine ⟨fun hf => ?_, 0, h0⟩
      have h0' : s 0 = true := h0
      rw [h0'] at hf
      contradiction
  refine ⟨hEq, ?_⟩
  rw [hEq]
  exact (isSafety_iff_closure_eq StartsTrue).mp startsTrue_isSafety

/-- Simpler contradictory non-machine-closed counterexample: `AlwaysFalse`
paired with `EventuallyTrue`. -/
theorem alwaysFalse_eventuallyTrue_not_machineClosed :
    IsSafety AlwaysFalse ∧
      IsLiveness EventuallyTrue ∧
      ¬ MachineClosed AlwaysFalse EventuallyTrue := by
  refine ⟨alwaysFalse_isSafety, eventuallyTrue_isLiveness, ?_⟩
  intro hMC
  rcases hMC [] ⟨constFalse, hasPrefix_nil _, traceProp_pos_alwaysFalse⟩ with ⟨s', _, hAll, i, hi⟩
  have hf := hAll i
  rw [hf] at hi
  contradiction

/-- Tail-liveness property: eventually every step is `true`. -/
def EventuallyAlwaysTrue : TraceProp Bool :=
  fun s => ∃ k : Nat, ∀ i : Nat, k ≤ i → s i = true

/-- Tail-liveness property: eventually every step is `false`. -/
def EventuallyAlwaysFalse : TraceProp Bool :=
  fun s => ∃ k : Nat, ∀ i : Nat, k ≤ i → s i = false

/-- Non-closure of `MachineClosed` (and `IsLiveness`) under conjunction:
`(UnivProp, EventuallyAlwaysTrue)` and `(UnivProp, EventuallyAlwaysFalse)` are
both machine-closed with live liveness parts, yet
`(UnivProp, PropInter EventuallyAlwaysTrue EventuallyAlwaysFalse)` is NOT
machine-closed (its conjunction is empty). -/
theorem machineClosed_not_closed_under_propInter :
    IsLiveness EventuallyAlwaysTrue ∧
      IsLiveness EventuallyAlwaysFalse ∧
      MachineClosed (UnivProp : TraceProp Bool) EventuallyAlwaysTrue ∧
      MachineClosed (UnivProp : TraceProp Bool) EventuallyAlwaysFalse ∧
      ¬ MachineClosed (UnivProp : TraceProp Bool)
          (PropInter EventuallyAlwaysTrue EventuallyAlwaysFalse) := by
  have hL1 : IsLiveness EventuallyAlwaysTrue := by
    intro u
    refine ⟨appendPrefix u constTrue, hasPrefix_appendPrefix u constTrue, u.length, ?_⟩
    intro i hi
    have hlt : ¬ (i < u.length) := by omega
    simp [appendPrefix, hlt, constTrue]
  have hL2 : IsLiveness EventuallyAlwaysFalse := by
    intro u
    refine ⟨appendPrefix u constFalse, hasPrefix_appendPrefix u constFalse, u.length, ?_⟩
    intro i hi
    have hlt : ¬ (i < u.length) := by omega
    simp [appendPrefix, hlt, constFalse]
  refine ⟨hL1, hL2, ?_, ?_, ?_⟩
  · intro u _
    rcases hL1 u with ⟨s', hpre', h1⟩
    exact ⟨s', hpre', trivial, h1⟩
  · intro u _
    rcases hL2 u with ⟨s', hpre', h2⟩
    exact ⟨s', hpre', trivial, h2⟩
  · intro hMC
    rcases hMC [] ⟨constFalse, hasPrefix_nil _, trivial⟩ with ⟨s', _, _, ⟨k1, hk1⟩, ⟨k2, hk2⟩⟩
    let k := k1 + k2
    have ht : s' k = true := hk1 k (Nat.le_add_right k1 k2)
    have hf : s' k = false := hk2 k (Nat.le_add_left k2 k1)
    rw [ht] at hf
    contradiction

/-! ### Non-vacuity witnesses and tightness counterexamples -/

/-- Non-vacuity witness for `machineClosed_iff_closure_propInter_eq_of_isSafety`:
`(StartsTrue, EventuallyFalse)` satisfies `IsSafety StartsTrue` and
`MachineClosed StartsTrue EventuallyFalse`. -/
theorem machineClosed_iff_nonvacuity :
    IsSafety StartsTrue ∧ MachineClosed StartsTrue EventuallyFalse :=
  ⟨startsTrue_isSafety, startsTrue_eventuallyFalse_machineClosed⟩

/-- Tightness counterexample for `hS : IsSafety S` in
`machineClosed_iff_closure_propInter_eq_of_isSafety`: for `S = EventuallyTrue`
(not safety) and `L = UnivProp`, `MachineClosed S L` holds trivially, yet
`Closure (PropInter S L) ≠ S`, falsifying the biconditional. -/
theorem eventuallyTrue_tight_machineClosed_iff :
    ¬ (MachineClosed EventuallyTrue UnivProp ↔
       Closure (PropInter EventuallyTrue UnivProp) = EventuallyTrue) := by
  intro hIff
  have hMC : MachineClosed EventuallyTrue UnivProp := by
    intro u hu
    rcases hu with ⟨s, hpre, hEv⟩
    exact ⟨s, hpre, hEv, trivial⟩
  have heq : Closure (PropInter EventuallyTrue UnivProp) = EventuallyTrue := hIff.mp hMC
  have hInCl : Closure (PropInter EventuallyTrue UnivProp) constFalse := by
    intro n
    rcases eventuallyTrue_isLiveness (takePrefix constFalse n) with ⟨s', hpre', hEv'⟩
    exact ⟨s', hpre', hEv', trivial⟩
  have hEv : EventuallyTrue constFalse := (congrFun heq constFalse) ▸ hInCl
  rcases hEv with ⟨i, hi⟩
  simp [constFalse] at hi

/-- Non-vacuity witness for `closure_propInter_eq_iff_isSafety_and_machineClosed`:
`(StartsTrue, EventuallyFalse)` satisfies the right-hand side and
`(StartsFalseStaysFalse, EventuallyTrue)` falsifies it. -/
theorem closure_propInter_eq_iff_nonvacuity :
    (IsSafety StartsTrue ∧ MachineClosed StartsTrue EventuallyFalse) ∧
      ¬ (IsSafety StartsFalseStaysFalse ∧ MachineClosed StartsFalseStaysFalse EventuallyTrue) :=
  ⟨⟨startsTrue_isSafety, startsTrue_eventuallyFalse_machineClosed⟩,
    fun h => startsFalseStaysFalse_eventuallyTrue_not_machineClosed h.2⟩

/-- Non-vacuity witness for `alpernSchneider_is_machineClosed`: on `Bool`,
`StartsTrueAndEventuallyFalse` is a nontrivial property (neither safety nor
liveness). -/
theorem alpernSchneider_is_machineClosed_nonvacuity :
    ¬ IsSafety StartsTrueAndEventuallyFalse ∧ ¬ IsLiveness StartsTrueAndEventuallyFalse :=
  startsTrueAndEventuallyFalse_neither_safety_nor_liveness

/-- Witness showing `IsLiveness L` is unnecessary for machine closure:
`(AlwaysFalse, AlwaysFalse)` is machine-closed with `IsSafety AlwaysFalse` even
though `AlwaysFalse` is not a liveness property. -/
theorem machineClosed_without_liveness_witness :
    IsSafety AlwaysFalse ∧ ¬ IsLiveness AlwaysFalse ∧ MachineClosed AlwaysFalse AlwaysFalse := by
  refine ⟨alwaysFalse_isSafety, alwaysFalse_not_isLiveness, ?_⟩
  intro u hu
  rcases hu with ⟨s, hpre, hAll⟩
  exact ⟨s, hpre, hAll, hAll⟩

end Toy.SafetyLiveness
