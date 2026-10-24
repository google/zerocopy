import AnnealResearch.TreeMemoryPrefixes

/-!
Exact finite-horizon composition for the fixed arbitrary reply-only controller.
Every horizon observes the full configuration through reifyConfig. The only
input admission is ConfigWellSized; every actual successor carries it forward.
Terminal UB/unsupported states occur at their actual horizon and have no later
successor. noChoice is absent on both sides, with no added terminal state.

The resulting NoUB equivalence transports the fixed all-prefix observer; it
does not prove arbitrary controllers safe or imply progress/fairness/termination.
No inverse encoding is needed: both actual iterations start from a reified pair.
-/

namespace AnnealResearch.TreeMemoryPrefixAgreement

universe u

open TreeMemoryClient TreeMemoryPrefixes

theorem rIterate_succ {S : Type u} (controller : Controller S) (count : Nat)
    (initial : RConfig S) :
    rIterate controller (count + 1) initial =
      (rStep controller initial).bind (fun next => rIterate controller count next) := rfl

theorem fIterate_succ {S : Type u} (controller : Controller S) (count : Nat)
    (initial : FConfig S) :
    fIterate controller (count + 1) initial =
      (fStep controller initial).bind (fun next => fIterate controller count next) := rfl

/-- Every reached configuration, including an error residual, remains in the
structural domain. The reached equation is not a successful-command premise. -/
theorem prefix_preserves {S : Type u} (controller : Controller S) (count : Nat)
    (initial reached : FConfig S) (sized : ConfigWellSized initial)
    (reachedAt : fIterate controller count initial = some reached) :
    ConfigWellSized reached := by
  induction count generalizing initial with
  | zero =>
      have same : initial = reached := Option.some.inj reachedAt
      rw [← same]
      exact sized
  | succ count ih =>
      cases first : fStep controller initial with
      | none =>
          have expanded := reachedAt
          rw [fIterate_succ, first] at expanded
          change (none : Option (FConfig S)) = some reached at expanded
          cases expanded
      | some next =>
          have expanded := reachedAt
          rw [fIterate_succ, first] at expanded
          have tail : fIterate controller count next = some reached := expanded
          exact ih next (step_preserves controller initial next sized first) tail

/-- Equality at every exact transition horizon, including zero and error
horizons; terminal states are never repeated to pad a longer execution. -/
theorem prefix_agrees {S : Type u} (controller : Controller S) (count : Nat)
    (initial : FConfig S) (sized : ConfigWellSized initial) :
    rIterate controller count (reifyConfig initial) =
      (fIterate controller count initial).map reifyConfig := by
  induction count generalizing initial with
  | zero => rfl
  | succ count ih =>
      rw [rIterate_succ, fIterate_succ, step_agrees controller initial sized]
      cases first : fStep controller initial with
      | none => rfl
      | some next =>
          change rIterate controller count (reifyConfig next) =
            (fIterate controller count next).map reifyConfig
          exact ih next (step_preserves controller initial next sized first)

theorem related_prefix_agrees {S : Type u} (controller : Controller S) (count : Nat)
    (reference : RConfig S) (initial : FConfig S)
    (related : reference = reifyConfig initial) (sized : ConfigWellSized initial) :
    rIterate controller count reference =
      (fIterate controller count initial).map reifyConfig := by
  rw [related]
  exact prefix_agrees controller count initial sized

/-- Both directions quantify all finite prefixes. Unsupported/absent successors
can satisfy this observer; the theorem is not a progress or safety certificate. -/
theorem noUB_iff {S : Type u} (controller : Controller S) (initial : FConfig S)
    (sized : ConfigWellSized initial) :
    RNoUB controller (reifyConfig initial) ↔ FNoUB controller initial := by
  constructor
  · intro referenceSafe count reached reachedAt bad
    have referenceReached :
        rIterate controller count (reifyConfig initial) = some (reifyConfig reached) := by
      rw [prefix_agrees controller count initial sized, reachedAt] <;> rfl
    exact referenceSafe count (reifyConfig reached) referenceReached ((reify_isUB reached).2 bad)
  · intro factoredSafe count reached reachedAt bad
    have agreement := prefix_agrees controller count initial sized
    rw [reachedAt] at agreement
    cases factoredAt : fIterate controller count initial with
    | none =>
        rw [factoredAt] at agreement
        cases agreement
    | some factored =>
        rw [factoredAt] at agreement
        have same : reached = reifyConfig factored := Option.some.inj agreement
        exact factoredSafe count factored factoredAt ((reify_isUB factored).1 (same ▸ bad))

theorem related_noUB_iff {S : Type u} (controller : Controller S)
    (reference : RConfig S) (initial : FConfig S)
    (related : reference = reifyConfig initial) (sized : ConfigWellSized initial) :
    RNoUB controller reference ↔ FNoUB controller initial := by
  rw [related]
  exact noUB_iff controller initial sized

#print axioms rIterate_succ
#print axioms fIterate_succ
#print axioms prefix_preserves
#print axioms prefix_agrees
#print axioms related_prefix_agrees
#print axioms noUB_iff
#print axioms related_noUB_iff

end AnnealResearch.TreeMemoryPrefixAgreement
