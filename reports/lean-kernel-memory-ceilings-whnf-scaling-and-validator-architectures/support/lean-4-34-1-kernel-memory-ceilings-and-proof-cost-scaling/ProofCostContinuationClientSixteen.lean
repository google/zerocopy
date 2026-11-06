import AnnealResearch.ProofCostContinuationBase
import AnnealResearch.ProofCostContinuation

/-! Frozen matched client: one fixed repetition scale, all four raw payloads,
all allocator candidates and finite horizons through the exact common claims.
This process checks both base and extension; its time does not isolate them. -/
namespace AnnealResearch.ProofCostContinuationClientSixteen

open ProofCostCommon

theorem base : ∀ payload : Payload, BaseFixtureClaim payload .sixteen :=
  fun payload => ProofCostContinuationBase.base_suite payload .sixteen

theorem extension : ∀ payload : Payload, ExtensionFixtureClaim payload .sixteen :=
  fun payload => ProofCostContinuation.extension_suite payload .sixteen

#print axioms base
#print axioms extension

end AnnealResearch.ProofCostContinuationClientSixteen
