import AnnealResearch.ProgramCostPrimitives

/-!
Continuation assembly for the exact eight-operation common body. The local
rules retain both finite-prefix safety and its normal-completion postcondition.
They do not impose progress, termination, allocator success or global memory WF.
All route-specific setup is contained in this measured source module.
-/
namespace AnnealResearch.ProgramCostContinuation8

open Execution MemoryExecution MiniRustReference ProgramCostCommon ProgramCostPrimitives

private def Ensures (start : Config State) : Prop :=
  NoUB SourceStep Bad start ∧ CompletionNoLive start

private theorem ensures_after_step {start successor : Config State}
    (safe : Ensures start) (edge : SourceStep start successor) : Ensures successor := by
  constructor
  · exact safe.1.after_step edge
  · intro memory trace path
    exact safe.2 memory trace ((Reach.tail (Reach.refl start) edge).trans path)

/-- A local continuation rule: the current state and each actual successor
meet the same safety/postcondition contract. The invariant here contains no
program phase; it only proves the generic one-step reasoning principle. -/
private theorem ensures_of_successors {start : Config State}
    (notBad : ¬ Bad start)
    (completeHere : ∀ memory trace, start = .completed memory trace → NoLive memory)
    (ready : ∀ successor, SourceStep start successor → Ensures successor) :
    Ensures start := by
  have preserved : ∀ {current successor : Config State},
      (current = start ∨ Ensures current) → SourceStep current successor →
        (successor = start ∨ Ensures successor) := by
    intro current successor member edge
    rcases member with rfl | safe
    · exact Or.inr (ready successor edge)
    · exact Or.inr (ensures_after_step safe edge)
  constructor
  · apply invariant_noUB (Invariant := fun current => current = start ∨ Ensures current)
      (Or.inl rfl) preserved
    intro current member
    rcases member with rfl | safe
    · exact notBad
    · exact safe.1 current (Reach.refl current)
  · intro memory trace path
    have member : Config.completed memory trace = start ∨
        Ensures (.completed memory trace) :=
      invariant_reachable (Step := SourceStep)
        (Invariant := fun (current : Config State) => current = start ∨ Ensures current)
        (initial := start) (reached := .completed memory trace)
        (Or.inl rfl) preserved path
    rcases member with same | safe
    · exact completeHere memory trace same.symm
    · exact safe.2 memory trace (Reach.refl _)

private theorem completed_ensures (memory : State) (trace : List Event)
    (dead : NoLive memory) : Ensures (.completed memory trace) := by
  apply ensures_of_successors (by exact id)
  · intro final finalTrace same
    cases same
    exact dead
  · rintro successor ⟨candidate, impossible⟩
    change none = some successor at impossible
    cases impossible

private theorem done_ensures (memory : State) (trace : List Event)
    (dead : NoLive memory) : Ensures (.running memory .done trace) := by
  apply ensures_of_successors (by exact id)
  · intro final finalTrace impossible
    cases impossible
  · rintro successor ⟨candidate, edge⟩
    change some (Config.completed memory trace) = some successor at edge
    cases edge
    exact completed_ensures memory trace dead

/-- Every numeric candidate is examined. An absent allocator branch supplies
no successor. This positive call rule requires UB/unsupported/exit impossible;
it does not reclassify any of those actual outcomes. -/
private theorem call_ensures (memory : State) (op : Op) (k : Reply → Plan)
    (trace : List Event)
    (ready : ∀ candidate,
      match sourceExecute candidate memory op with
      | .good reply after => Ensures
          (.running after (k reply) (trace ++ [.answered op reply]))
      | .noChoice => True
      | .ub _ | .unsupported | .exit _ => False) :
    Ensures (.running memory (.call op k) trace) := by
  apply ensures_of_successors (by exact id)
  · intro final finalTrace impossible
    cases impossible
  · intro successor edge
    obtain ⟨candidate, edge⟩ := edge
    have premise := ready candidate
    simp only [MemoryExecution.next] at edge
    cases answer : sourceExecute candidate memory op with
    | good reply after =>
      rw [answer] at edge premise
      cases edge
      exact premise
    | ub diagnostic =>
      simp [answer] at premise
    | unsupported =>
      simp [answer] at premise
    | noChoice =>
      rw [answer] at edge
      cases edge
    | exit result =>
      simp [answer] at premise

private theorem fixed_call_ensures {memory after : State} {op : Op} {reply : Reply}
    {k : Reply → Plan} {trace : List Event}
    (answer : ∀ candidate, sourceExecute candidate memory op = .good reply after)
    (safe : Ensures (.running after (k reply) (trace ++ [.answered op reply]))) :
    Ensures (.running memory (.call op k) trace) := by
  apply call_ensures
  intro candidate
  rw [answer candidate]
  exact safe

/-- The only allocation wrapper is one actual call. Its continuation consumes
the actual fresh pointer/state, and the guard retains the complete Nat domain. -/
private theorem allocate_one_ensures (memory : State) (k : Reply → Plan)
    (trace : List Event)
    (ready : ∀ candidate, AllocationCandidate memory 1 1 candidate →
      Ensures (.running (append memory (freshAllocation .heap 1 1 candidate))
        (k (.pointer ⟨candidate, some memory.next⟩))
        (trace ++ [.answered (.allocate .heap 1 1)
          (.pointer ⟨candidate, some memory.next⟩)]))) :
    Ensures (.running memory (.call (.allocate .heap 1 1) k) trace) := by
  apply call_ensures
  intro candidate
  have small : (1 : Nat) < sizeLimit := by decide
  by_cases feasible : AllocationCandidate memory 1 1 candidate
  · have answer : sourceExecute candidate memory (.allocate .heap 1 1) =
        .good (.pointer ⟨candidate, some memory.next⟩)
          (append memory (freshAllocation .heap 1 1 candidate)) := by
      simp [sourceExecute, allocateAt, Nat.not_le.mpr small, feasible,
        liftResult, freshAllocation]
    rw [answer]
    exact ready candidate feasible
  · simp [sourceExecute, allocateAt, Nat.not_le.mpr small, feasible, liftResult]

/-- The actual final load and free discharge false live support at done. -/
private theorem finish_A (memory : State) (pA : Ptr) (id : Nat) (value : Byte)
    (trace : List Event) (atA : ByteAt memory pA id value)
    (supported : LiveOnly memory (fun current => current = id)) :
    Ensures (.running memory (base8_s007 pA) trace) := by
  have loaded := byteAt_load atA
  apply fixed_call_ensures (after := memory) (reply := .bytes [value])
  · intro candidate
    simp [sourceExecute, loaded, liftResult]
  · obtain ⟨freed, released, _⟩ := byteAt_free atA
    have removed := free_removes_liveOnly supported atA.1 released
    have falseSupport : LiveOnly freed (fun _ => False) :=
      liveOnly_mono removed (by
        intro current member
        exact member.2 member.1)
    have dead : NoLive freed := (noLive_iff_liveOnly_empty freed).mpr falseSupport
    apply fixed_call_ensures (after := freed) (reply := .unit)
    · intro candidate
      simp [sourceExecute, released, liftResult]
    · exact done_ensures freed _ dead

/-- Exactly the common all-choice, all-finite-prefix safety/resource claim.
Both inputs are quantified; there is no success or well-formedness admission. -/
theorem base8_claim : ∀ q, ProgramCostCommon.Base8Claim q := by
  intro q
  change Ensures (.running empty (base8 q) [])
  apply allocate_one_ensures
  intro addressA feasibleA
  let pA : Ptr := ⟨addressA, some empty.next⟩
  let allocatedA := append empty (freshAllocation .heap 1 1 addressA)
  have atA : ByteAt allocatedA pA 0 .uninit := byteAt_fresh empty addressA
  have supportedA : LiveOnly allocatedA (fun id => id = 0) :=
    liveOnly_mono (append_liveOnly empty_liveOnly (freshAllocation .heap 1 1 addressA))
      (by
        intro id member
        rcases member with same | impossible
        · exact same
        · exact False.elim impossible)
  obtain ⟨writtenA, storedA, atWrittenA⟩ := byteAt_store atA sevenByte
  have writtenSupportA := store_preserves_liveOnly supportedA storedA
  have writtenNextA : writtenA.next = 1 := by
    calc
      writtenA.next = allocatedA.next := ProofCostFrames.store_preserves_next storedA
      _ = 1 := rfl
  apply fixed_call_ensures (after := writtenA) (reply := .unit)
  · intro candidate
    change liftResult (fun (after : State) => (Reply.unit, after))
      (store allocatedA pA [sevenByte] 1) = .good .unit writtenA
    rw [storedA]
    rfl
  · apply allocate_one_ensures
    intro addressB feasibleB
    let pB : Ptr := ⟨addressB, some writtenA.next⟩
    let allocatedB := append writtenA (freshAllocation .heap 1 1 addressB)
    have different : 0 ≠ writtenA.next := by omega
    have atKeptA : ByteAt allocatedB pA 0 sevenByte :=
      byteAt_append_other atWrittenA different (freshAllocation .heap 1 1 addressB)
    have atB : ByteAt allocatedB pB writtenA.next .uninit :=
      byteAt_fresh writtenA addressB
    have supportedAB : LiveOnly allocatedB
        (fun id => id = writtenA.next ∨ id = 0) :=
      append_liveOnly writtenSupportA (freshAllocation .heap 1 1 addressB)
    obtain ⟨writtenB, storedB, atWrittenB⟩ := byteAt_store atB (signalByte q)
    have atKeptWrittenA : ByteAt writtenB pA 0 sevenByte :=
      byteAt_store_other atKeptA atB.1 different storedB
    have writtenSupportAB := store_preserves_liveOnly supportedAB storedB
    apply fixed_call_ensures (after := writtenB) (reply := .unit)
    · intro candidate
      change liftResult (fun (after : State) => (Reply.unit, after))
        (store allocatedB pB [signalByte q] 1) = .good .unit writtenB
      rw [storedB]
      rfl
    · have loadedB := byteAt_load atWrittenB
      apply fixed_call_ensures (after := writtenB) (reply := .bytes [signalByte q])
      · intro candidate
        change liftResult (fun (value : List Byte × State) => (Reply.bytes value.1, value.2))
          (load writtenB pB 1 1) = .good (.bytes [signalByte q]) writtenB
        rw [loadedB]
        rfl
      · obtain ⟨freedB, releasedB, _⟩ := byteAt_free atWrittenB
        have atRemainingA : ByteAt freedB pA 0 sevenByte :=
          byteAt_free_other atKeptWrittenA atWrittenB.1 different releasedB
        have removedB := free_removes_liveOnly writtenSupportAB atWrittenB.1 releasedB
        have remainingSupportA : LiveOnly freedB (fun id => id = 0) :=
          liveOnly_mono removedB (by
            intro id member
            rcases member.1 with atB | atA
            · exact False.elim (member.2 atB)
            · exact atA)
        apply fixed_call_ensures (after := freedB) (reply := .unit)
        · intro candidate
          change liftResult (fun (after : State) => (Reply.unit, after))
            (free writtenB pB .heap 1 1) = .good .unit freedB
          rw [releasedB]
          rfl
        · exact finish_A freedB pA 0 sevenByte _ atRemainingA remainingSupportA

/- Source order follows the local rule setup, the two-call suffix and endpoint.
Small direct wrappers do not add duplicate audit endpoints. -/
#print axioms ensures_of_successors
#print axioms done_ensures
#print axioms call_ensures
#print axioms allocate_one_ensures
#print axioms finish_A
#print axioms base8_claim

end AnnealResearch.ProgramCostContinuation8
