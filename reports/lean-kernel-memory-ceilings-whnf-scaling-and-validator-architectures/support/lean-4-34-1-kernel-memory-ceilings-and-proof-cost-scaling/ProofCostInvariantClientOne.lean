import AnnealResearch.ProofCostInvariant
import AnnealResearch.ProofCostInvariantExtension

/-! Frozen matched client: one fixed repetition scale, all four raw payloads,
all allocator candidates and finite horizons through the exact common claims.
This process checks both base and extension; its time does not isolate them. -/
namespace AnnealResearch.ProofCostInvariantClientOne

open ProofCostCommon

theorem base : ∀ payload : Payload, BaseFixtureClaim payload .one :=
  fun payload => ProofCostInvariant.base_suite payload .one

theorem extension : ∀ payload : Payload, ExtensionFixtureClaim payload .one :=
  fun payload => ProofCostInvariantExtension.extension_suite payload .one

#print axioms base
#print axioms extension

end AnnealResearch.ProofCostInvariantClientOne
