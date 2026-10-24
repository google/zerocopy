import AnnealResearch.TreeChoiceClient

/-!
Exact relational finite-prefix coverage for the separate explicit-candidate
client. Every actual F edge maps at its own candidate. Reverse coverage executes
the actual F successor at the R edge's candidate; it does not cancel reification
or require arbitrary F representatives of an R endpoint to execute.

Only initial ConfigWellSized is operational admission. Every returned successor,
including terminal partial-error memory, preserves it before the next edge.
Exact horizons include zero and the reached error horizon, without terminal
stuttering. NoUB equivalence quantifies all actual finite candidate prefixes;
it proves neither arbitrary-controller safety nor progress, termination,
fairness, candidate existence, source/helper adequacy or an internal cost claim.
-/
namespace AnnealResearch.TreeChoicePrefixes

universe u
open TreeChoiceClient

theorem step_preserves {S : Type u} (controller : Controller S)
    (config successor : FConfig S) (sized : ConfigWellSized config)
    (stepped : FStep controller config successor) : ConfigWellSized successor := by
  obtain ⟨candidate, actual⟩ := stepped
  exact next_preserves controller candidate config successor sized actual

/-- The actual F edge's candidate also witnesses its exact R image. -/
theorem map_step {S : Type u} (controller : Controller S)
    (config successor : FConfig S) (sized : ConfigWellSized config)
    (stepped : FStep controller config successor) :
    RStep controller (reifyConfig config) (reifyConfig successor) := by
  obtain ⟨candidate, actual⟩ := stepped
  refine ⟨candidate, ?_⟩
  rw [next_agrees controller candidate config sized, actual]
  rfl

/-- Reverse coverage at the same explicit candidate. The witness is an actual
F next result, rather than a selected representative of its reification. -/
theorem lift_next {S : Type u} (controller : Controller S) (candidate : Nat)
    (config : FConfig S) (reached : RConfig S) (sized : ConfigWellSized config)
    (stepped : rNext controller candidate (reifyConfig config) = some reached) :
    ∃ actual, fNext controller candidate config = some actual ∧
      reifyConfig actual = reached := by
  have agreement := next_agrees controller candidate config sized
  rw [stepped] at agreement
  cases executed : fNext controller candidate config with
  | none =>
    rw [executed] at agreement
    cases agreement
  | some actual =>
    rw [executed, Option.map_some] at agreement
    exact ⟨actual, rfl, (Option.some.inj agreement).symm⟩

theorem lift_step {S : Type u} (controller : Controller S)
    (config : FConfig S) (reached : RConfig S) (sized : ConfigWellSized config)
    (stepped : RStep controller (reifyConfig config) reached) :
    ∃ actual, FStep controller config actual ∧ reifyConfig actual = reached := by
  obtain ⟨candidate, chosen⟩ := stepped
  obtain ⟨actual, executed, represented⟩ :=
    lift_next controller candidate config reached sized chosen
  exact ⟨actual, ⟨candidate, executed⟩, represented⟩

/-- An actual prefix observes the execution; it does not assume successful
commands, absence of UB, normal completion or candidate existence elsewhere. -/
theorem prefix_preserves {S : Type u} (controller : Controller S) (count : Nat)
    (initial reached : FConfig S) (sized : ConfigWellSized initial)
    (observed : FPrefix controller count initial reached) : ConfigWellSized reached := by
  induction count generalizing initial with
  | zero =>
    change reached = initial at observed
    rw [observed]
    exact sized
  | succ count ih =>
    obtain ⟨middle, first, tail⟩ := observed
    exact ih middle (step_preserves controller initial middle sized first) tail

theorem map_prefix {S : Type u} (controller : Controller S) (count : Nat)
    (initial reached : FConfig S) (sized : ConfigWellSized initial)
    (observed : FPrefix controller count initial reached) :
    RPrefix controller count (reifyConfig initial) (reifyConfig reached) := by
  induction count generalizing initial with
  | zero =>
    change reached = initial at observed
    change reifyConfig reached = reifyConfig initial
    exact congrArg reifyConfig observed
  | succ count ih =>
    obtain ⟨middle, first, tail⟩ := observed
    exact ⟨reifyConfig middle, map_step controller initial middle sized first,
      ih middle (step_preserves controller initial middle sized first) tail⟩

/-- At every edge, lift its own reference candidate and carry the resulting
actual F domain. Equality of reifications never identifies literal F states. -/
theorem lift_prefix {S : Type u} (controller : Controller S) (count : Nat)
    (initial : FConfig S) (reached : RConfig S) (sized : ConfigWellSized initial)
    (observed : RPrefix controller count (reifyConfig initial) reached) :
    ∃ actual, FPrefix controller count initial actual ∧ reifyConfig actual = reached := by
  induction count generalizing initial with
  | zero =>
    change reached = reifyConfig initial at observed
    exact ⟨initial, rfl, observed.symm⟩
  | succ count ih =>
    obtain ⟨middle, first, tail⟩ := observed
    obtain ⟨factoredMiddle, actualFirst, represented⟩ :=
      lift_step controller initial middle sized first
    have tailAt : RPrefix controller count (reifyConfig factoredMiddle) reached := by
      rw [represented]
      exact tail
    obtain ⟨actual, actualTail, finalRepresentation⟩ :=
      ih factoredMiddle
        (step_preserves controller initial factoredMiddle sized actualFirst) tailAt
    exact ⟨actual, ⟨factoredMiddle, actualFirst, actualTail⟩, finalRepresentation⟩

/-- Complete endpoint image at the same exact horizon, including zero, error
prefixes and absence of longer prefixes after terminal configurations. -/
theorem prefix_exact_image {S : Type u} (controller : Controller S) (count : Nat)
    (initial : FConfig S) (reached : RConfig S) (sized : ConfigWellSized initial) :
    RPrefix controller count (reifyConfig initial) reached ↔
      ∃ actual, FPrefix controller count initial actual ∧ reifyConfig actual = reached := by
  constructor
  · exact lift_prefix controller count initial reached sized
  · rintro ⟨actual, actualPrefix, represented⟩
    have mapped := map_prefix controller count initial actual sized actualPrefix
    rw [represented] at mapped
    exact mapped

/-- Both directions retain all actual finite candidate prefixes, including a
bad input at horizon zero. Unsupported/absent behavior can satisfy NoUB, so
this observer equivalence establishes no arbitrary-controller safety/progress. -/
theorem noUB_iff {S : Type u} (controller : Controller S) (initial : FConfig S)
    (sized : ConfigWellSized initial) :
    RNoUB controller (reifyConfig initial) ↔ FNoUB controller initial := by
  constructor
  · intro referenceSafe count reached observed bad
    have mapped := map_prefix controller count initial reached sized observed
    exact referenceSafe count (reifyConfig reached) mapped
      ((TreeMemoryClient.reify_isUB reached).2 bad)
  · intro factoredSafe count reached observed bad
    obtain ⟨actual, actualPrefix, represented⟩ :=
      lift_prefix controller count initial reached sized observed
    have reifiedBad : TreeMemoryClient.RConfig.IsUB (reifyConfig actual) := by
      rw [represented]
      exact bad
    exact factoredSafe count actual actualPrefix
      ((TreeMemoryClient.reify_isUB actual).1 reifiedBad)

#print axioms step_preserves
#print axioms map_step
#print axioms lift_next
#print axioms lift_step
#print axioms prefix_preserves
#print axioms map_prefix
#print axioms lift_prefix
#print axioms prefix_exact_image
#print axioms noUB_iff

end AnnealResearch.TreeChoicePrefixes
