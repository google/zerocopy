import AnnealResearch.TreeChoicePrefixes
import AnnealResearch.TreeChoiceLive
import AnnealResearch.TreeEncodedPrefixes

/-!
Coverage and separate positive F transfer for the explicit-candidate client.
The old exact configuration encoder is reused unchanged. Execution transport
requires only the existing natural reference width predicate, while F stable
matching additionally requires its separate initial matching predicate.

Every candidate and exact finite horizon remains in the operational relation.
Reverse coverage supplies an actual F endpoint, without assuming F injectivity
or equating that endpoint with an encoding of the reference endpoint. Neither
source reachability, arbitrary-controller safety nor progress is established.
-/
namespace AnnealResearch.TreeChoiceCoverage

universe u

open TreeChoiceClient
open TreeEncodedPrefixes (encodeConfig)

/-- The unchanged natural reference width predicate, with no added admission. -/
abbrev RConfigWellSized {S : Type u} (config : RConfig S) : Prop :=
  TreeMemoryEncoding.RWellSized config.memory

theorem configWidth_encode_iff {S : Type u} (config : RConfig S) :
    ConfigWellSized (encodeConfig config) ↔ RConfigWellSized config :=
  TreeEncodedPrefixes.configWellSized_encode_iff config

/-- Exact reconstruction transports matching independently of the width domain.
Terminal UB/unsupported configurations retain their old vacuous observer. -/
theorem configKinds_encode_iff {S : Type u} (config : RConfig S) :
    TreeLivePrefixes.FConfigKinds (encodeConfig config) ↔ TreeLivePrefixes.RConfigKinds config := by
  unfold TreeLivePrefixes.FConfigKinds
  rw [TreeEncodedPrefixes.reify_encode_config]

private theorem reify_encode {S : Type u} (config : RConfig S) :
    reifyConfig (encodeConfig config) = config :=
  TreeEncodedPrefixes.reify_encode_config config

/-- Actual next for each candidate, with full result/control/memory observation.
No matching, source history, candidate validity or successful-call premise. -/
theorem encoded_next_agrees {S : Type u} (controller : Controller S) (candidate : Nat)
    (config : RConfig S) (sized : RConfigWellSized config) :
    rNext controller candidate config =
      (fNext controller candidate (encodeConfig config)).map reifyConfig := by
  have agreement := TreeChoiceClient.next_agrees controller candidate (encodeConfig config)
    ((configWidth_encode_iff config).2 sized)
  rw [reify_encode] at agreement
  exact agreement

/-- Every owned R initial state is covered at each exact horizon under only
natural width. The reverse witness is an actual F prefix, not arbitrary data
with an equal reification or a claimed inverse F encoding. -/
theorem encoded_prefix_exact_image {S : Type u} (controller : Controller S) (count : Nat)
    (initial reached : RConfig S) (sized : RConfigWellSized initial) :
    RPrefix controller count initial reached ↔
      ∃ actual, FPrefix controller count (encodeConfig initial) actual ∧
        reifyConfig actual = reached := by
  have agreement := TreeChoicePrefixes.prefix_exact_image controller count
    (encodeConfig initial) reached ((configWidth_encode_iff initial).2 sized)
  rw [reify_encode] at agreement
  exact agreement

/-- Both directions quantify every actual finite candidate prefix, including
horizon zero and terminal error horizons. Unsupported/absent behavior can
satisfy this observer; the iff is not arbitrary-controller safety or progress. -/
theorem encoded_noUB_iff {S : Type u} (controller : Controller S) (initial : RConfig S)
    (sized : RConfigWellSized initial) :
    RNoUB controller initial ↔ FNoUB controller (encodeConfig initial) := by
  have agreement := TreeChoicePrefixes.noUB_iff controller (encodeConfig initial)
    ((configWidth_encode_iff initial).2 sized)
  rw [reify_encode] at agreement
  exact agreement

/-- Positive stable matching is a separate transfer. The actual F prefix needs
initial width for correspondence and initial matching for the R invariant.
UB/unsupported retain exact residuals without terminal matching obligations. -/
theorem factored_prefix_preserves {S : Type u} (controller : Controller S) (count : Nat)
    (initial reached : FConfig S) (sized : ConfigWellSized initial)
    (matching : TreeLivePrefixes.FConfigKinds initial)
    (observed : FPrefix controller count initial reached) :
    TreeLivePrefixes.FConfigKinds reached := by
  have mapped := TreeChoicePrefixes.map_prefix controller count initial reached sized observed
  exact TreeChoiceLive.prefix_preserves controller count (reifyConfig initial)
    (reifyConfig reached) matching mapped

#print axioms configWidth_encode_iff
#print axioms configKinds_encode_iff
#print axioms encoded_next_agrees
#print axioms encoded_prefix_exact_image
#print axioms encoded_noUB_iff
#print axioms factored_prefix_preserves

end AnnealResearch.TreeChoiceCoverage
