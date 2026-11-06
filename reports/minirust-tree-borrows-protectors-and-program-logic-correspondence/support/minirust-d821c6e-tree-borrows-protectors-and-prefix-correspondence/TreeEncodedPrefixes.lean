import AnnealResearch.TreeMemoryEncoding
import AnnealResearch.TreeMemoryPrefixAgreement

/-!
Coverage corollaries for the unchanged reply-driven controller and finite-
prefix semantics. Every reference configuration has an encoded representative.
Its constructor, control, result/diagnostic and full reified memory reconstruct
without any domain premise. Execution correspondence retains the natural
reference uniform-width domain through the checked encoding equivalence.

No controller, primitive, noChoice or terminal rule is reimplemented. Actual
factored successors are compared through reifyConfig; no unrestricted reverse
round-trip equality of factored configurations is asserted. No arbitrary-client
safety, progress, termination, fairness or source/Rust adequacy claim is added.
-/

namespace AnnealResearch.TreeEncodedPrefixes

universe u

open TreeMemoryClient

def encodeConfig {S : Type u} : RConfig S → FConfig S
  | .running control memory =>
      .running control (TreeMemoryEncoding.encodeMemory memory)
  | .finished control result memory =>
      .finished control result (TreeMemoryEncoding.encodeMemory memory)
  | .ub control fault memory =>
      .ub control fault (TreeMemoryEncoding.encodeMemory memory)
  | .unsupported control reason memory =>
      .unsupported control reason (TreeMemoryEncoding.encodeMemory memory)

theorem encodeConfig_memory {S : Type u} (config : RConfig S) :
    (encodeConfig config).memory = TreeMemoryEncoding.encodeMemory config.memory := by
  cases config <;> rfl

theorem reify_encode_config {S : Type u} (config : RConfig S) :
    reifyConfig (encodeConfig config) = config := by
  cases config <;> simp only [encodeConfig, reifyConfig,
    TreeMemoryEncoding.reify_encode_memory]

theorem configWellSized_encode_iff {S : Type u} (config : RConfig S) :
    ConfigWellSized (encodeConfig config) ↔ TreeMemoryEncoding.RWellSized config.memory := by
  unfold ConfigWellSized
  rw [encodeConfig_memory]
  exact (TreeMemoryEncoding.wellSized_encode_iff config.memory).symm

/-- The same controller and actual step functions are retained. A noChoice
call is absent on both sides; existing terminal constructors never resume. -/
theorem encoded_step_agrees {S : Type u} (controller : Controller S) (config : RConfig S)
    (sized : TreeMemoryEncoding.RWellSized config.memory) :
    rStep controller config = (fStep controller (encodeConfig config)).map reifyConfig := by
  have agreement := TreeMemoryPrefixes.step_agrees controller (encodeConfig config)
    ((configWellSized_encode_iff config).2 sized)
  rw [reify_encode_config] at agreement
  exact agreement

/-- Equality at every exact finite horizon, including zero, UB/unsupported
residual horizons and absent successors. Terminal states are not padded. -/
theorem encoded_prefix_agrees {S : Type u} (controller : Controller S) (count : Nat)
    (config : RConfig S) (sized : TreeMemoryEncoding.RWellSized config.memory) :
    rIterate controller count config =
      (fIterate controller count (encodeConfig config)).map reifyConfig := by
  exact TreeMemoryPrefixAgreement.related_prefix_agrees controller count config
    (encodeConfig config) (reify_encode_config config).symm
    ((configWellSized_encode_iff config).2 sized)

/-- Both directions retain the existing all-finite-prefix UB observer.
Unsupported or absent successors are allowed; this does not certify safety. -/
theorem encoded_noUB_iff {S : Type u} (controller : Controller S) (config : RConfig S)
    (sized : TreeMemoryEncoding.RWellSized config.memory) :
    RNoUB controller config ↔ FNoUB controller (encodeConfig config) := by
  exact TreeMemoryPrefixAgreement.related_noUB_iff controller config
    (encodeConfig config) (reify_encode_config config).symm
    ((configWellSized_encode_iff config).2 sized)

#print axioms encodeConfig_memory
#print axioms reify_encode_config
#print axioms configWellSized_encode_iff
#print axioms encoded_step_agrees
#print axioms encoded_prefix_agrees
#print axioms encoded_noUB_iff

end AnnealResearch.TreeEncodedPrefixes
