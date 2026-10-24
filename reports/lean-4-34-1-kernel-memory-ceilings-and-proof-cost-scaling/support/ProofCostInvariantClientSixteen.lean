import AnnealResearch.ProofCostInvariant
import AnnealResearch.ProofCostInvariantExtension

/-! Frozen matched client: one fixed repetition scale, all four raw payloads,
all allocator candidates and finite horizons through the exact common claims.
This process checks both base and extension; its time does not isolate them. -/
namespace AnnealResearch.ProofCostInvariantClientSixteen

open ProofCostCommon

theorem base : ∀ payload : Payload, BaseFixtureClaim payload .sixteen :=
  fun payload => ProofCostInvariant.base_suite payload .sixteen

theorem extension : ∀ payload : Payload, ExtensionFixtureClaim payload .sixteen :=
  fun payload => ProofCostInvariantExtension.extension_suite payload .sixteen

#print axioms base
#print axioms extension

end AnnealResearch.ProofCostInvariantClientSixteen
