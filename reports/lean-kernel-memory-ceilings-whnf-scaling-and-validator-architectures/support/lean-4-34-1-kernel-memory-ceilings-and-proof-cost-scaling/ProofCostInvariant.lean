import AnnealResearch.ProofCostCommon

/-!
Direct operational phase-invariant route for the exact shared BaseClaim.
The inherited client control definitions are reused, but no inherited round,
program, continuation, or compositional NoUB theorem is invoked. The only shared
semantic helpers used here are allocate_answer, allocate_absent, and
fresh_round_facts, all equations about actual primitive results.

The invariant quantifies over arbitrary memory, trace, and remaining repetition
count. SourceStep still quantifies over every Nat allocator candidate. An absent
candidate has no successor; it is not replaced by success or an allowed stop.
This is finite-prefix NoUB, not allocator progress or termination. No new
semantics, cost model, Rust binding, or architecture decision is introduced.
-/

namespace AnnealResearch.ProofCostInvariant

open Execution MemoryExecution MiniRustReference MemoryExamples

def releasePlan (bytes : List Byte) (p : Ptr) (remaining : Nat) : Plan :=
  .call (.free p .heap bytes.length 1) fun _ => rounds bytes .spin remaining

def readPlan (bytes : List Byte) (p : Ptr) (remaining : Nat) : Plan :=
  .call (.load p bytes.length 1) fun _ => releasePlan bytes p remaining

def writePlan (bytes : List Byte) (p : Ptr) (remaining : Nat) : Plan :=
  .call (.store p bytes 1) fun _ => readPlan bytes p remaining

/-- Pending primitive equations describe the phase's memory. They are not
whole-client safety assumptions; successful phases discharge them one at a time. -/
inductive Phase (bytes : List Byte) : Config State → Prop where
  | boundary (memory : State) (remaining : Nat) (trace : List Event) :
      Phase bytes (.running memory (rounds bytes .spin remaining) trace)
  | write (before written freed : State) (address : Nat)
      (stored : store (freshState before bytes address) (pointer before address) bytes 1 = .ok written)
      (loaded : load written (pointer before address) bytes.length 1 = .ok (bytes, written))
      (released : free written (pointer before address) .heap bytes.length 1 = .ok freed)
      (remaining : Nat) (trace : List Event) :
      Phase bytes (.running (freshState before bytes address)
        (writePlan bytes (pointer before address) remaining) trace)
  | read (written freed : State) (p : Ptr)
      (loaded : load written p bytes.length 1 = .ok (bytes, written))
      (released : free written p .heap bytes.length 1 = .ok freed)
      (remaining : Nat) (trace : List Event) :
      Phase bytes (.running written (readPlan bytes p remaining) trace)
  | release (written freed : State) (p : Ptr)
      (released : free written p .heap bytes.length 1 = .ok freed)
      (remaining : Nat) (trace : List Event) :
      Phase bytes (.running written (releasePlan bytes p remaining) trace)

theorem phase_preserved {bytes : List Byte} (small : bytes.length < sizeLimit)
    {before after : Config State} (phase : Phase bytes before) (edge : SourceStep before after) :
    Phase bytes after := by
  obtain ⟨candidate, successor⟩ := edge
  cases phase with
  | boundary memory remaining trace =>
    cases remaining with
    | zero =>
      change some (Config.running memory .spin (trace ++ [.spin])) = some after at successor
      cases successor
      exact Phase.boundary memory 0 _
    | succ remaining =>
      by_cases valid : AllocationCandidate memory bytes.length 1 candidate
      · have answer := ProofCostCommon.allocate_answer memory bytes candidate small valid
        obtain ⟨written, freed, stored, loaded, released⟩ :=
          ProofCostCommon.fresh_round_facts memory bytes candidate
        simp only [MemoryExecution.next, rounds, oneRound, answer] at successor
        cases successor
        exact Phase.write memory written freed candidate stored loaded released remaining _
      · have answer := ProofCostCommon.allocate_absent memory bytes candidate small valid
        simp only [MemoryExecution.next, rounds, oneRound, answer] at successor
        cases successor
  | write memory written freed address stored loaded released remaining trace =>
    have answer : sourceExecute candidate (freshState memory bytes address)
        (.store (pointer memory address) bytes 1) = .good .unit written := by
      simp only [sourceExecute, stored, liftResult]
    simp only [MemoryExecution.next, writePlan, answer] at successor
    cases successor
    exact Phase.read written freed (pointer memory address) loaded released remaining _
  | read written freed p loaded released remaining trace =>
    have answer : sourceExecute candidate written (.load p bytes.length 1) =
        .good (.bytes bytes) written := by
      simp only [sourceExecute, loaded, liftResult]
    simp only [MemoryExecution.next, readPlan, answer] at successor
    cases successor
    exact Phase.release written freed p released remaining _
  | release written freed p released remaining trace =>
    have answer : sourceExecute candidate written (.free p .heap bytes.length 1) =
        .good .unit freed := by
      simp only [sourceExecute, released, liftResult]
    simp only [MemoryExecution.next, releasePlan, answer] at successor
    cases successor
    exact Phase.boundary freed remaining _

theorem phase_excludes_bad {bytes : List Byte} {config : Config State}
    (phase : Phase bytes config) : ¬ Bad config := by
  cases phase <;> exact id

/-- No finite horizon is selected: all configurations on every finite path
from the exact common initial configuration satisfy the operational invariant. -/
theorem reachable_phase (bytes : List Byte) (small : bytes.length < sizeLimit) (n : Nat)
    {reached : Config State} (path : Reach SourceStep (ProofCostCommon.baseInitial bytes n) reached) :
    Phase bytes reached :=
  invariant_reachable (Phase.boundary empty n []) (phase_preserved small) path

theorem base_claim (bytes : List Byte) (small : bytes.length < sizeLimit) (n : Nat) :
    ProofCostCommon.BaseClaim bytes n := by
  exact invariant_noUB (Phase.boundary empty n []) (phase_preserved small)
    (fun _ phase => phase_excludes_bad phase)

/-- Identical endpoint proposition to the other route; fixture enumeration
instantiates the generic proof and does not bound candidates or path lengths. -/
theorem base_suite : ProofCostCommon.BaseSuite := by
  intro payload scale
  exact base_claim (ProofCostCommon.payloadBytes payload) (ProofCostCommon.payload_small payload)
    (ProofCostCommon.repetitions scale)

#print axioms phase_preserved
#print axioms phase_excludes_bad
#print axioms reachable_phase
#print axioms base_claim
#print axioms base_suite

end AnnealResearch.ProofCostInvariant
