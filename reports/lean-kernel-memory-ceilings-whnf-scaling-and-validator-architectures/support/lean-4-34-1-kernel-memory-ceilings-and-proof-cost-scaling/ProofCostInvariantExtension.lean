import AnnealResearch.ProofCostCommon
import AnnealResearch.ProofCostFrames

/-!
Direct operational invariant for the unchanged two-live-buffer extension.
Every SourceStep allocator candidate and every finite horizon is retained.
Shared framing lemmas are primitive record/result equations, not continuation
or program-safety theorems. No prior round/program NoUB proof is invoked.

A is retained by exact allocation-record equality while B changes. In
particular no positive-size premise on B, whole-memory equality, or selected
allocator address is assumed. No progress, termination, Rust adequacy, physical
running-time, or architecture-ranking conclusion is made.
-/

namespace AnnealResearch.ProofCostInvariantExtension

open Execution MemoryExecution MiniRustReference MemoryExamples

/-- A's current raw obligations and fresh-ID separation. These are primitive
equations, not a NoUB assumption for the client that will use them. -/
structure HeldA (bytesA : List Byte) (memory : State) (pA : Ptr) (idA : Nat) : Prop where
  provenance : pA.provenance = some idA
  different : idA ≠ memory.next
  loaded : load memory pA bytesA.length 1 = .ok (bytesA, memory)
  released : ∃ freed, free memory pA .heap bytesA.length 1 = .ok freed

def releaseAPlan (bytesA bytesB : List Byte) (pA : Ptr) (remaining : Nat) : Plan :=
  .call (.free pA .heap bytesA.length 1) fun _ =>
    ProofCostCommon.twoLiveRounds bytesA bytesB .spin remaining

inductive Phase (bytesA bytesB : List Byte) : Config State → Prop where
  | boundary (memory : State) (remaining : Nat) (trace : List Event) :
      Phase bytesA bytesB (.running memory
        (ProofCostCommon.twoLiveRounds bytesA bytesB .spin remaining) trace)
  | writeA (before written freed : State) (address : Nat)
      (stored : store (freshState before bytesA address) (pointer before address) bytesA 1 = .ok written)
      (loaded : load written (pointer before address) bytesA.length 1 = .ok (bytesA, written))
      (released : free written (pointer before address) .heap bytesA.length 1 = .ok freed)
      (remaining : Nat) (trace : List Event) :
      Phase bytesA bytesB (.running (freshState before bytesA address)
        (ProofCostCommon.useA bytesA bytesB (pointer before address)
          (ProofCostCommon.twoLiveRounds bytesA bytesB .spin remaining)) trace)
  | allocateB (memory : State) (pA : Ptr) (idA : Nat) (held : HeldA bytesA memory pA idA)
      (remaining : Nat) (trace : List Event) :
      Phase bytesA bytesB (.running memory
        (ProofCostCommon.allocateB bytesA bytesB pA
          (ProofCostCommon.twoLiveRounds bytesA bytesB .spin remaining)) trace)
  | writeB (base written freed : State) (pA : Ptr) (idA address : Nat)
      (held : HeldA bytesA base pA idA)
      (stored : store (freshState base bytesB address) (pointer base address) bytesB 1 = .ok written)
      (loaded : load written (pointer base address) bytesB.length 1 = .ok (bytesB, written))
      (released : free written (pointer base address) .heap bytesB.length 1 = .ok freed)
      (remaining : Nat) (trace : List Event) :
      Phase bytesA bytesB (.running (freshState base bytesB address)
        (ProofCostCommon.useB bytesA bytesB pA (pointer base address)
          (ProofCostCommon.twoLiveRounds bytesA bytesB .spin remaining)) trace)
  | readB (base written freed : State) (pA pB : Ptr) (idA : Nat)
      (held : HeldA bytesA base pA idA)
      (provenanceB : pB.provenance = some base.next)
      (sameA : written.allocations idA = base.allocations idA)
      (loaded : load written pB bytesB.length 1 = .ok (bytesB, written))
      (released : free written pB .heap bytesB.length 1 = .ok freed)
      (remaining : Nat) (trace : List Event) :
      Phase bytesA bytesB (.running written
        (ProofCostCommon.loadBThenA bytesA bytesB pA pB
          (ProofCostCommon.twoLiveRounds bytesA bytesB .spin remaining)) trace)
  | releaseB (base written freed : State) (pA pB : Ptr) (idA : Nat)
      (held : HeldA bytesA base pA idA)
      (provenanceB : pB.provenance = some base.next)
      (sameA : written.allocations idA = base.allocations idA)
      (released : free written pB .heap bytesB.length 1 = .ok freed)
      (remaining : Nat) (trace : List Event) :
      Phase bytesA bytesB (.running written
        (ProofCostCommon.freeBThenA bytesA bytesB pA pB
          (ProofCostCommon.twoLiveRounds bytesA bytesB .spin remaining)) trace)
  | readA (memory freed : State) (pA : Ptr)
      (loaded : load memory pA bytesA.length 1 = .ok (bytesA, memory))
      (released : free memory pA .heap bytesA.length 1 = .ok freed)
      (remaining : Nat) (trace : List Event) :
      Phase bytesA bytesB (.running memory
        (ProofCostCommon.finishA bytesA pA
          (ProofCostCommon.twoLiveRounds bytesA bytesB .spin remaining)) trace)
  | releaseA (memory freed : State) (pA : Ptr)
      (released : free memory pA .heap bytesA.length 1 = .ok freed)
      (remaining : Nat) (trace : List Event) :
      Phase bytesA bytesB (.running memory (releaseAPlan bytesA bytesB pA remaining) trace)

theorem phase_preserved {bytesA bytesB : List Byte}
    (smallA : bytesA.length < sizeLimit) (smallB : bytesB.length < sizeLimit)
    {before after : Config State} (phase : Phase bytesA bytesB before)
    (edge : SourceStep before after) : Phase bytesA bytesB after := by
  obtain ⟨candidate, successor⟩ := edge
  cases phase with
  | boundary memory remaining trace =>
    cases remaining with
    | zero =>
      change some (Config.running memory .spin (trace ++ [.spin])) = some after at successor
      cases successor
      exact Phase.boundary memory 0 _
    | succ remaining =>
      by_cases valid : AllocationCandidate memory bytesA.length 1 candidate
      · have answer := ProofCostCommon.allocate_answer memory bytesA candidate smallA valid
        obtain ⟨written, freed, stored, loaded, released⟩ :=
          ProofCostCommon.fresh_round_facts memory bytesA candidate
        simp only [MemoryExecution.next, ProofCostCommon.twoLiveRounds,
          ProofCostCommon.twoLiveRound, answer] at successor
        cases successor
        exact Phase.writeA memory written freed candidate stored loaded released remaining _
      · have answer := ProofCostCommon.allocate_absent memory bytesA candidate smallA valid
        simp only [MemoryExecution.next, ProofCostCommon.twoLiveRounds,
          ProofCostCommon.twoLiveRound, answer] at successor
        cases successor
  | writeA memory written freed address stored loaded released remaining trace =>
    have answer : sourceExecute candidate (freshState memory bytesA address)
        (.store (pointer memory address) bytesA 1) = .good .unit written := by
      simp only [sourceExecute, stored, liftResult]
    have nextEq := ProofCostFrames.store_preserves_next stored
    have different : memory.next ≠ written.next := by
      rw [nextEq]
      change memory.next ≠ memory.next + 1
      omega
    have held : HeldA bytesA written (pointer memory address) memory.next :=
      ⟨rfl, different, loaded, ⟨freed, released⟩⟩
    simp only [MemoryExecution.next, ProofCostCommon.useA, answer] at successor
    cases successor
    exact Phase.allocateB written (pointer memory address) memory.next held remaining _
  | allocateB memory pA idA held remaining trace =>
    by_cases valid : AllocationCandidate memory bytesB.length 1 candidate
    · have answer := ProofCostCommon.allocate_answer memory bytesB candidate smallB valid
      obtain ⟨written, freed, stored, loaded, released⟩ :=
        ProofCostCommon.fresh_round_facts memory bytesB candidate
      simp only [MemoryExecution.next, ProofCostCommon.allocateB, answer] at successor
      cases successor
      exact Phase.writeB memory written freed pA idA candidate held stored loaded released remaining _
    · have answer := ProofCostCommon.allocate_absent memory bytesB candidate smallB valid
      simp only [MemoryExecution.next, ProofCostCommon.allocateB, answer] at successor
      cases successor
  | writeB base written freed pA idA address held stored loaded released remaining trace =>
    have answer : sourceExecute candidate (freshState base bytesB address)
        (.store (pointer base address) bytesB 1) = .good .unit written := by
      simp only [sourceExecute, stored, liftResult]
    have sameA : written.allocations idA = base.allocations idA := by
      calc
        written.allocations idA = (freshState base bytesB address).allocations idA :=
          ProofCostFrames.store_preserves_other rfl held.different stored
        _ = base.allocations idA := by simp [freshState, append, held.different]
    simp only [MemoryExecution.next, ProofCostCommon.useB, answer] at successor
    cases successor
    exact Phase.readB base written freed pA (pointer base address) idA held rfl sameA loaded released remaining _
  | readB base written freed pA pB idA held provenanceB sameA loaded released remaining trace =>
    have answer : sourceExecute candidate written (.load pB bytesB.length 1) =
        .good (.bytes bytesB) written := by
      simp only [sourceExecute, loaded, liftResult]
    simp only [MemoryExecution.next, ProofCostCommon.loadBThenA, answer] at successor
    cases successor
    exact Phase.releaseB base written freed pA pB idA held provenanceB sameA released remaining _
  | releaseB base written freed pA pB idA held provenanceB sameA released remaining trace =>
    have answer : sourceExecute candidate written (.free pB .heap bytesB.length 1) =
        .good .unit freed := by
      simp only [sourceExecute, released, liftResult]
    have afterA : freed.allocations idA = base.allocations idA :=
      (ProofCostFrames.free_preserves_other provenanceB held.different released).trans sameA
    have loadedA : load freed pA bytesA.length 1 = .ok (bytesA, freed) :=
      ProofCostFrames.load_frame held.provenance afterA.symm held.loaded
    obtain ⟨oldFreed, oldRelease⟩ := held.released
    obtain ⟨final, releasedA⟩ := ProofCostFrames.free_frame held.provenance afterA.symm oldRelease
    simp only [MemoryExecution.next, ProofCostCommon.freeBThenA, answer] at successor
    cases successor
    exact Phase.readA freed final pA loadedA releasedA remaining _
  | readA memory freed pA loaded released remaining trace =>
    have answer : sourceExecute candidate memory (.load pA bytesA.length 1) =
        .good (.bytes bytesA) memory := by
      simp only [sourceExecute, loaded, liftResult]
    simp only [MemoryExecution.next, ProofCostCommon.finishA, answer] at successor
    cases successor
    exact Phase.releaseA memory freed pA released remaining _
  | releaseA memory freed pA released remaining trace =>
    have answer : sourceExecute candidate memory (.free pA .heap bytesA.length 1) =
        .good .unit freed := by
      simp only [sourceExecute, released, liftResult]
    simp only [MemoryExecution.next, releaseAPlan, answer] at successor
    cases successor
    exact Phase.boundary freed remaining _

theorem phase_excludes_bad {bytesA bytesB : List Byte} {config : Config State}
    (phase : Phase bytesA bytesB config) : ¬ Bad config := by
  cases phase <;> exact id

theorem reachable_phase (bytesA bytesB : List Byte)
    (smallA : bytesA.length < sizeLimit) (smallB : bytesB.length < sizeLimit) (n : Nat)
    {reached : Config State}
    (path : Reach SourceStep (ProofCostCommon.extensionInitial bytesA bytesB n) reached) :
    Phase bytesA bytesB reached :=
  invariant_reachable (Phase.boundary empty n []) (phase_preserved smallA smallB) path

/-- The new direct operational proof works from arbitrary source memory/trace.
This is route-local setup, not an inherited program-safety theorem. -/
theorem arbitrary_memory_claim (bytesA bytesB : List Byte)
    (smallA : bytesA.length < sizeLimit) (smallB : bytesB.length < sizeLimit)
    (n : Nat) (memory : State) (trace : List Event) :
    NoUB SourceStep Bad (.running memory (ProofCostCommon.twoLiveRounds bytesA bytesB .spin n) trace) :=
  invariant_noUB (Phase.boundary memory n trace) (phase_preserved smallA smallB)
    (fun _ phase => phase_excludes_bad phase)

theorem extension_claim (bytesA bytesB : List Byte)
    (smallA : bytesA.length < sizeLimit) (smallB : bytesB.length < sizeLimit) (n : Nat) :
    ProofCostCommon.ExtensionClaim bytesA bytesB n :=
  arbitrary_memory_claim bytesA bytesB smallA smallB n empty []

theorem extension_suite : ProofCostCommon.ExtensionSuite := by
  intro payload scale
  exact extension_claim ProofCostCommon.sevenBytes (ProofCostCommon.payloadBytes payload)
    (ProofCostCommon.payload_small .initialized) (ProofCostCommon.payload_small payload)
    (ProofCostCommon.repetitions scale)

#print axioms phase_preserved
#print axioms phase_excludes_bad
#print axioms reachable_phase
#print axioms arbitrary_memory_claim
#print axioms extension_claim
#print axioms extension_suite

end AnnealResearch.ProofCostInvariantExtension
