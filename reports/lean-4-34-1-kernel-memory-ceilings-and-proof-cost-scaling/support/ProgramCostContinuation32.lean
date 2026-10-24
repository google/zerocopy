import AnnealResearch.ProgramCostPrimitives

/-!
Continuation assembly for the exact thirty-two-operation common body. The local
rules retain both finite-prefix safety and its normal-completion postcondition.
They do not impose progress, termination, allocator success or global memory WF.
All route-specific setup is contained in this measured source module.
-/
namespace AnnealResearch.ProgramCostContinuation32

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
    Ensures (.running memory (base32_s031 pA) trace) := by
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

/-- One fixed four-call block. The conclusion lists all four operations;
there is no repetition counter, body list or arbitrary-graph validator. -/
private theorem filler_ensures {memory : State} {pA pB : Ptr} {idA idB : Nat}
    {oldA : Byte} {support : Nat → Prop} (newA signal : Byte)
    (continuation : Plan) (trace : List Event)
    (atA : ByteAt memory pA idA oldA) (atB : ByteAt memory pB idB signal)
    (different : idA ≠ idB) (supported : LiveOnly memory support)
    (ready : ∀ after afterTrace,
      ByteAt after pA idA newA → ByteAt after pB idB signal → LiveOnly after support →
        Ensures (.running after continuation afterTrace)) :
    Ensures (.running memory
      (.call (.load pA 1 1) fun reply =>
        match reply with
        | .bytes _ => .call (.store pA [newA] 1) fun reply =>
            match reply with
            | .unit => .call (.store pB [signal] 1) fun reply =>
                match reply with
                | .unit => .call (.load pB 1 1) fun reply =>
                    match reply with
                    | .bytes _ => continuation
                    | _ => .done
                | _ => .done
            | _ => .done
        | _ => .done)
      trace) := by
  have loadedA := byteAt_load atA
  apply fixed_call_ensures (after := memory) (reply := .bytes [oldA])
  · intro candidate
    change liftResult (fun (value : List Byte × State) => (Reply.bytes value.1, value.2))
      (load memory pA 1 1) = .good (.bytes [oldA]) memory
    rw [loadedA]
    rfl
  · obtain ⟨writtenA, storedA, atWrittenA⟩ := byteAt_store atA newA
    have keptB : ByteAt writtenA pB idB signal :=
      byteAt_store_other atB atA.1 (Ne.symm different) storedA
    have supportA := store_preserves_liveOnly supported storedA
    apply fixed_call_ensures (after := writtenA) (reply := .unit)
    · intro candidate
      change liftResult (fun (after : State) => (Reply.unit, after))
        (store memory pA [newA] 1) = .good .unit writtenA
      rw [storedA]
      rfl
    · obtain ⟨writtenB, storedB, atWrittenB⟩ := byteAt_store keptB signal
      have keptA : ByteAt writtenB pA idA newA :=
        byteAt_store_other atWrittenA keptB.1 different storedB
      have supportB := store_preserves_liveOnly supportA storedB
      apply fixed_call_ensures (after := writtenB) (reply := .unit)
      · intro candidate
        change liftResult (fun (after : State) => (Reply.unit, after))
          (store writtenA pB [signal] 1) = .good .unit writtenB
        rw [storedB]
        rfl
      · have loadedB := byteAt_load atWrittenB
        apply fixed_call_ensures (after := writtenB) (reply := .bytes [signal])
        · intro candidate
          change liftResult (fun (value : List Byte × State) => (Reply.bytes value.1, value.2))
            (load writtenB pB 1 1) = .good (.bytes [signal]) writtenB
          rw [loadedB]
          rfl
        · exact ready writtenB _ keptA atWrittenB supportB

/-- The four actual common tail calls: load/free B and load/free A, then done. -/
private theorem finish_AB (memory : State) (pA pB : Ptr) (idA idB : Nat)
    (valueA signal : Byte) (trace : List Event)
    (atA : ByteAt memory pA idA valueA) (atB : ByteAt memory pB idB signal)
    (different : idA ≠ idB)
    (supported : LiveOnly memory (fun id => id = idB ∨ id = idA)) :
    Ensures (.running memory (base32_s029 pA pB) trace) := by
  have loadedB := byteAt_load atB
  apply fixed_call_ensures (after := memory) (reply := .bytes [signal])
  · intro candidate
    change liftResult (fun (value : List Byte × State) => (Reply.bytes value.1, value.2))
      (load memory pB 1 1) = .good (.bytes [signal]) memory
    rw [loadedB]
    rfl
  · obtain ⟨freedB, releasedB, _⟩ := byteAt_free atB
    have remainingA : ByteAt freedB pA idA valueA :=
      byteAt_free_other atA atB.1 different releasedB
    have removedB := free_removes_liveOnly supported atB.1 releasedB
    have supportA : LiveOnly freedB (fun id => id = idA) :=
      liveOnly_mono removedB (by
        intro id member
        rcases member.1 with selectedB | selectedA
        · exact False.elim (member.2 selectedB)
        · exact selectedA)
    apply fixed_call_ensures (after := freedB) (reply := .unit)
    · intro candidate
      change liftResult (fun (after : State) => (Reply.unit, after))
        (free memory pB .heap 1 1) = .good .unit freedB
      rw [releasedB]
      rfl
    · exact finish_A freedB pA idA valueA _ remainingA supportA

/-- Exactly the common all-choice, all-finite-prefix safety/resource claim.
Both inputs are quantified; there is no success or well-formedness admission. -/
theorem base32_claim : ∀ q, ProgramCostCommon.Base32Claim q := by
  intro q
  change Ensures (.running empty (base32 q) [])
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
    · apply filler_ensures sevenByte (signalByte q)
        (base32_s009 q pA pB) _
        atKeptWrittenA atWrittenB different writtenSupportAB
      intro memory1 trace1 atA1 atB1 support1
      apply filler_ensures nineByte (signalByte q)
        (base32_s013 q pA pB) _ atA1 atB1 different support1
      intro memory2 trace2 atA2 atB2 support2
      apply filler_ensures sevenByte (signalByte q)
        (base32_s017 q pA pB) _ atA2 atB2 different support2
      intro memory3 trace3 atA3 atB3 support3
      apply filler_ensures nineByte (signalByte q)
        (base32_s021 q pA pB) _ atA3 atB3 different support3
      intro memory4 trace4 atA4 atB4 support4
      apply filler_ensures sevenByte (signalByte q)
        (base32_s025 q pA pB) _ atA4 atB4 different support4
      intro memory5 trace5 atA5 atB5 support5
      apply filler_ensures nineByte (signalByte q)
        (base32_s029 pA pB) _ atA5 atB5 different support5
      intro memory6 trace6 atA6 atB6 support6
      exact finish_AB memory6 pA pB 0 writtenA.next nineByte (signalByte q) trace6
        atA6 atB6 different support6

/- Copied local-rule setup is charged in this module. Audit the new fixed
block, actual tail and complete endpoint, without duplicating projection audits. -/
#print axioms filler_ensures
#print axioms finish_AB
#print axioms base32_claim

end AnnealResearch.ProgramCostContinuation32
