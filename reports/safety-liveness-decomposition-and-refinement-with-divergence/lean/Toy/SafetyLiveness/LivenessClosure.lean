import Toy.SafetyLiveness.Core
import Toy.SafetyLiveness.Decomposition

/-!
# Liveness through the prefix closure, and a conjunction that is neither

Supporting statements for boundary notes on the safety/liveness results:

- `isLiveness_iff_closure_eq_univ_of_nonempty`: over a nonempty alphabet, a
  trace property is a liveness property if and only if its prefix closure is
  `UnivProp`.
- `emptyAlphabet_tight_isLiveness_iff_closure_eq_univ`: over `Empty` that
  equivalence fails, because `Closure EmptyProp = UnivProp` holds vacuously
  (there are no infinite traces over `Empty`) while no property over `Empty` is
  live.
- `propInter_startsTrue_eventuallyFalse_neither_safety_nor_liveness`: the
  conjunction of the safety property `StartsTrue` with the liveness property
  `EventuallyFalse` is neither a safety property nor a liveness property.
-/

namespace Toy.SafetyLiveness

universe u

/-- Over a nonempty alphabet, `P` is a liveness property if and only if its
prefix closure `Closure P` is the universal property. The backward direction
pads an arbitrary finite prefix `u` with a constant tail to obtain a trace whose
closure membership at length `u.length` yields an extension of `u` in `P`. -/
theorem isLiveness_iff_closure_eq_univ_of_nonempty {α : Type u} (hα : Nonempty α)
    (P : TraceProp α) :
    IsLiveness P ↔ Closure P = UnivProp := by
  constructor
  · intro hLive
    funext s
    apply propext
    constructor
    · intro _
      trivial
    · intro _ n
      exact hLive (takePrefix s n)
  · intro hCl u
    obtain ⟨a⟩ := hα
    have ht : Closure P (appendPrefix u (fun _ => a)) := by
      rw [hCl]
      exact True.intro
    obtain ⟨s', hs', hP⟩ := ht u.length
    exact ⟨s', hasPrefix_of_hasPrefix_takePrefix (hasPrefix_appendPrefix u _) hs', hP⟩

/-- Over `Empty`, `Closure EmptyProp = UnivProp` holds vacuously while
`IsLiveness EmptyProp` is false, so the equivalence
`IsLiveness P ↔ Closure P = UnivProp` fails without `Nonempty α`. -/
theorem emptyAlphabet_tight_isLiveness_iff_closure_eq_univ :
    Closure (EmptyProp : TraceProp Empty) = UnivProp ∧
      ¬ IsLiveness (EmptyProp : TraceProp Empty) ∧
      ¬ (IsLiveness (EmptyProp : TraceProp Empty) ↔
          Closure (EmptyProp : TraceProp Empty) = UnivProp) := by
  have hCl : Closure (EmptyProp : TraceProp Empty) = UnivProp := by
    funext s
    exact Empty.elim (s 0)
  exact ⟨hCl, emptyAlphabet_no_liveness EmptyProp,
    fun hIff => emptyAlphabet_no_liveness EmptyProp (hIff.mpr hCl)⟩

/-- The conjunction `PropInter StartsTrue EventuallyFalse` of a safety property
and a liveness property is neither a safety property nor a liveness property
(it coincides with `StartsTrueAndEventuallyFalse`). -/
theorem propInter_startsTrue_eventuallyFalse_neither_safety_nor_liveness :
    IsSafety StartsTrue ∧ IsLiveness EventuallyFalse ∧
      ¬ IsSafety (PropInter StartsTrue EventuallyFalse) ∧
      ¬ IsLiveness (PropInter StartsTrue EventuallyFalse) := by
  have hEq : PropInter StartsTrue EventuallyFalse = StartsTrueAndEventuallyFalse := rfl
  rw [hEq]
  exact ⟨startsTrue_isSafety, eventuallyFalse_isLiveness,
    startsTrueAndEventuallyFalse_neither_safety_nor_liveness.1,
    startsTrueAndEventuallyFalse_neither_safety_nor_liveness.2⟩

end Toy.SafetyLiveness
