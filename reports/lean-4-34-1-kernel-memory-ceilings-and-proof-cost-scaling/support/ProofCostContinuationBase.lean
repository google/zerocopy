import AnnealResearch.ProofCostCommon

/-!
Base route: specialize the previously checked compositional continuation
theorem to the shared exact SourceStep/Bad claim.  This is cached proof reuse,
not a new safety argument or an execution-path argument.  The parent compiles.
-/
namespace AnnealResearch.ProofCostContinuationBase

open Execution MemoryExecution MiniRustReference MemoryExamples ProofCostCommon

theorem base_claim (bytes : List Byte) (small : bytes.length < sizeLimit) (n : Nat) :
    BaseClaim bytes n :=
  rounds_safe bytes small .spin spin_safe n empty []

theorem base_fixture (payload : Payload) (scale : Scale) : BaseFixtureClaim payload scale :=
  base_claim (payloadBytes payload) (payload_small payload) (repetitions scale)

theorem base_suite : BaseSuite := base_fixture

#print axioms base_claim
#print axioms base_fixture
#print axioms base_suite

end AnnealResearch.ProofCostContinuationBase
