import AnnealResearch.ProgramCostPrimitives

/-!
Continuation assembly for the exact one-hundred-twenty-eight-operation common body. The local
rules retain both finite-prefix safety and its normal-completion postcondition.
They do not impose progress, termination, allocator success or global memory WF.
All route-specific setup is contained in this measured source module.
-/
namespace AnnealResearch.ProgramCostContinuation128

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
    Ensures (.running memory (base128_s127 pA) trace) := by
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
    Ensures (.running memory (base128_s125 pA pB) trace) := by
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
theorem base128_claim : ∀ q, ProgramCostCommon.Base128Claim q := by
  intro q
  change Ensures (.running empty (base128 q) [])
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
        (base128_s009 q pA pB) _
        atKeptWrittenA atWrittenB different writtenSupportAB
      intro memory1 trace1 atA1 atB1 support1
      apply filler_ensures nineByte (signalByte q)
        (base128_s013 q pA pB) _ atA1 atB1 different support1
      intro memory2 trace2 atA2 atB2 support2
      apply filler_ensures sevenByte (signalByte q)
        (base128_s017 q pA pB) _ atA2 atB2 different support2
      intro memory3 trace3 atA3 atB3 support3
      apply filler_ensures nineByte (signalByte q)
        (base128_s021 q pA pB) _ atA3 atB3 different support3
      intro memory4 trace4 atA4 atB4 support4
      apply filler_ensures sevenByte (signalByte q)
        (base128_s025 q pA pB) _ atA4 atB4 different support4
      intro memory5 trace5 atA5 atB5 support5
      apply filler_ensures nineByte (signalByte q)
        (base128_s029 q pA pB) _ atA5 atB5 different support5
      intro memory6 trace6 atA6 atB6 support6
      apply filler_ensures sevenByte (signalByte q)
        (base128_s033 q pA pB) _ atA6 atB6 different support6
      intro memory7 trace7 atA7 atB7 support7
      apply filler_ensures nineByte (signalByte q)
        (base128_s037 q pA pB) _ atA7 atB7 different support7
      intro memory8 trace8 atA8 atB8 support8
      apply filler_ensures sevenByte (signalByte q)
        (base128_s041 q pA pB) _ atA8 atB8 different support8
      intro memory9 trace9 atA9 atB9 support9
      apply filler_ensures nineByte (signalByte q)
        (base128_s045 q pA pB) _ atA9 atB9 different support9
      intro memory10 trace10 atA10 atB10 support10
      apply filler_ensures sevenByte (signalByte q)
        (base128_s049 q pA pB) _ atA10 atB10 different support10
      intro memory11 trace11 atA11 atB11 support11
      apply filler_ensures nineByte (signalByte q)
        (base128_s053 q pA pB) _ atA11 atB11 different support11
      intro memory12 trace12 atA12 atB12 support12
      apply filler_ensures sevenByte (signalByte q)
        (base128_s057 q pA pB) _ atA12 atB12 different support12
      intro memory13 trace13 atA13 atB13 support13
      apply filler_ensures nineByte (signalByte q)
        (base128_s061 q pA pB) _ atA13 atB13 different support13
      intro memory14 trace14 atA14 atB14 support14
      apply filler_ensures sevenByte (signalByte q)
        (base128_s065 q pA pB) _ atA14 atB14 different support14
      intro memory15 trace15 atA15 atB15 support15
      apply filler_ensures nineByte (signalByte q)
        (base128_s069 q pA pB) _ atA15 atB15 different support15
      intro memory16 trace16 atA16 atB16 support16
      apply filler_ensures sevenByte (signalByte q)
        (base128_s073 q pA pB) _ atA16 atB16 different support16
      intro memory17 trace17 atA17 atB17 support17
      apply filler_ensures nineByte (signalByte q)
        (base128_s077 q pA pB) _ atA17 atB17 different support17
      intro memory18 trace18 atA18 atB18 support18
      apply filler_ensures sevenByte (signalByte q)
        (base128_s081 q pA pB) _ atA18 atB18 different support18
      intro memory19 trace19 atA19 atB19 support19
      apply filler_ensures nineByte (signalByte q)
        (base128_s085 q pA pB) _ atA19 atB19 different support19
      intro memory20 trace20 atA20 atB20 support20
      apply filler_ensures sevenByte (signalByte q)
        (base128_s089 q pA pB) _ atA20 atB20 different support20
      intro memory21 trace21 atA21 atB21 support21
      apply filler_ensures nineByte (signalByte q)
        (base128_s093 q pA pB) _ atA21 atB21 different support21
      intro memory22 trace22 atA22 atB22 support22
      apply filler_ensures sevenByte (signalByte q)
        (base128_s097 q pA pB) _ atA22 atB22 different support22
      intro memory23 trace23 atA23 atB23 support23
      apply filler_ensures nineByte (signalByte q)
        (base128_s101 q pA pB) _ atA23 atB23 different support23
      intro memory24 trace24 atA24 atB24 support24
      apply filler_ensures sevenByte (signalByte q)
        (base128_s105 q pA pB) _ atA24 atB24 different support24
      intro memory25 trace25 atA25 atB25 support25
      apply filler_ensures nineByte (signalByte q)
        (base128_s109 q pA pB) _ atA25 atB25 different support25
      intro memory26 trace26 atA26 atB26 support26
      apply filler_ensures sevenByte (signalByte q)
        (base128_s113 q pA pB) _ atA26 atB26 different support26
      intro memory27 trace27 atA27 atB27 support27
      apply filler_ensures nineByte (signalByte q)
        (base128_s117 q pA pB) _ atA27 atB27 different support27
      intro memory28 trace28 atA28 atB28 support28
      apply filler_ensures sevenByte (signalByte q)
        (base128_s121 q pA pB) _ atA28 atB28 different support28
      intro memory29 trace29 atA29 atB29 support29
      apply filler_ensures nineByte (signalByte q)
        (base128_s125 pA pB) _ atA29 atB29 different support29
      intro memory30 trace30 atA30 atB30 support30
      exact finish_AB memory30 pA pB 0 writtenA.next nineByte (signalByte q) trace30
        atA30 atB30 different support30

/- Copied local rules and fixed-block proof are charged in this module.
Audit the block, actual tail and complete body endpoint, without projection inflation. -/
#print axioms filler_ensures
#print axioms finish_AB
#print axioms base128_claim

end AnnealResearch.ProgramCostContinuation128
