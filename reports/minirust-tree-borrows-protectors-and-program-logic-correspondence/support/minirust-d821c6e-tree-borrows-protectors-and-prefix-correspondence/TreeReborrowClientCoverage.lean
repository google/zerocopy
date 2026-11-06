import AnnealResearch.TreeReborrowPrefixes
import AnnealResearch.TreeReborrowLive
import AnnealResearch.TreeEncodedPrefixes

/-!
Coverage and positive factored matching for the separate reborrow/pointer-reply
client. The old encoder and complete configuration types are reused unchanged.
No new encoder, primitive, controller, iterator or admission is introduced.

Arbitrary-reference operation/prefix/NoUB transport needs only the natural old
reference width domain. Positive matching is separate: the factored prefix
result additionally starts with old FConfigKinds. All terminal residuals remain
exact; noChoice has no successor. No arbitrary-client safety or progress follows.
-/

namespace AnnealResearch.TreeReborrowClientCoverage

universe u
open TreeReborrowClient
open TreeEncodedPrefixes (encodeConfig)

/-- A name for the existing natural reference width domain, not a stronger
admission. Missing pairs/dead records retain the old domain's exact policy. -/
abbrev RConfigWellSized {S : Type u} (config : RConfig S) : Prop :=
  TreeMemoryEncoding.RWellSized config.memory

/-- The new client aliases the old complete configuration types, so the old
encoder's domain equivalence applies directly without a representation change. -/
theorem configWellSized_encode_iff {S : Type u} (config : RConfig S) :
    ConfigWellSized (encodeConfig config) ↔ RConfigWellSized config :=
  TreeEncodedPrefixes.configWellSized_encode_iff config

/-- Encoding does not invent a matching assumption. Its exact reconstruction
transfers the old positive configuration observer independently of width. -/
theorem configKinds_encode_iff {S : Type u} (config : RConfig S) :
    TreeLivePrefixes.FConfigKinds (encodeConfig config) ↔ TreeLivePrefixes.RConfigKinds config := by
  unfold TreeLivePrefixes.FConfigKinds
  rw [TreeEncodedPrefixes.reify_encode_config]

/-- Every actual factored finite prefix has the positive stable-boundary
predicate. UB/unsupported retain exact memory without matching obligations. -/
theorem factored_prefix_preserves {S : Type u} (controller : Controller S) (count : Nat)
    (initial reached : FConfig S) (sized : ConfigWellSized initial)
    (matching : TreeLivePrefixes.FConfigKinds initial)
    (observed : fIterate controller count initial = some reached) :
    TreeLivePrefixes.FConfigKinds reached := by
  have agreement := TreeReborrowPrefixes.prefix_agrees controller count initial sized
  rw [observed, Option.map_some] at agreement
  exact TreeReborrowLive.prefix_preserves controller count (reifyConfig initial)
    (reifyConfig reached) matching agreement

/-- Actual new-client step, with the same pointer replies and continuations.
The supplied reference configuration is arbitrary within the natural width
predicate; no matching, successful-call, valid-path or NoUB premise is added. -/
theorem encoded_step_agrees {S : Type u} (controller : Controller S) (config : RConfig S)
    (sized : RConfigWellSized config) :
    rStep controller config = (fStep controller (encodeConfig config)).map reifyConfig := by
  have agreement := TreeReborrowPrefixes.step_agrees controller (encodeConfig config)
    ((configWellSized_encode_iff config).2 sized)
  simp only [TreeReborrowClient.reifyConfig] at agreement
  rw [TreeEncodedPrefixes.reify_encode_config] at agreement
  exact agreement

/-- Exact full-configuration equality at every finite horizon, including zero,
terminal error horizons and absent successors, using the existing encoder. -/
theorem encoded_prefix_agrees {S : Type u} (controller : Controller S) (count : Nat)
    (config : RConfig S) (sized : RConfigWellSized config) :
    rIterate controller count config =
      (fIterate controller count (encodeConfig config)).map reifyConfig := by
  exact TreeReborrowPrefixes.related_prefix_agrees controller count config
    (encodeConfig config) (TreeEncodedPrefixes.reify_encode_config config).symm
    ((configWellSized_encode_iff config).2 sized)

/-- Transport the new client's all-finite-prefix UB observer in both directions.
This equivalence requires width, not matching, and certifies no arbitrary client
safe: unsupported or absent successors can satisfy this observer. -/
theorem encoded_noUB_iff {S : Type u} (controller : Controller S) (config : RConfig S)
    (sized : RConfigWellSized config) :
    RNoUB controller config ↔ FNoUB controller (encodeConfig config) := by
  exact TreeReborrowPrefixes.related_noUB_iff controller config
    (encodeConfig config) (TreeEncodedPrefixes.reify_encode_config config).symm
    ((configWellSized_encode_iff config).2 sized)

#print axioms configWellSized_encode_iff
#print axioms configKinds_encode_iff
#print axioms factored_prefix_preserves
#print axioms encoded_step_agrees
#print axioms encoded_prefix_agrees
#print axioms encoded_noUB_iff

end AnnealResearch.TreeReborrowClientCoverage
