import AnnealResearch.ProgramCostPrimitives

/-!
Direct operational phase-invariant proof for the literal eight-call body.
All route-specific phase and preservation work is in this measured module.
No prior program-safety theorem, control witness, continuation route, graph
validator, or repetition theorem discharges any phase or endpoint.
-/
namespace AnnealResearch.ProgramCostInvariant8

open Execution MemoryExecution MiniRustReference ProgramCostCommon ProgramCostPrimitives

/-- One actual branch of the fixed one-byte allocator call. -/
theorem allocate_one_good (memory : State) (candidate : Nat)
    (valid : AllocationCandidate memory 1 1 candidate) :
    sourceExecute candidate memory (.allocate .heap 1 1) =
      .good (.pointer ⟨candidate, some memory.next⟩)
        (append memory (freshAllocation .heap 1 1 candidate)) := by
  simp [sourceExecute, allocateAt,
    Nat.not_le.mpr (show 1 < sizeLimit from by decide), valid,
    liftResult, freshAllocation]

/-- An invalid candidate contributes no allocation successor. -/
theorem allocate_one_absent (memory : State) (candidate : Nat)
    (invalid : ¬ AllocationCandidate memory 1 1 candidate) :
    sourceExecute candidate memory (.allocate .heap 1 1) = .noChoice := by
  simp [sourceExecute, allocateAt,
    Nat.not_le.mpr (show 1 < sizeLimit from by decide), invalid, liftResult]

/-- Facts are established along the actual execution, not admitted at entry.
The trace remains the actual Config trace; no trace or horizon is selected. -/
inductive Phase (q : Bool) : Config State → Prop where
  | entry (trace : List Event) :
      Phase q (.running empty (base8 q) trace)
  | storeA (memory : State) (pA : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 .uninit)
      (nextOne : memory.next = 1)
      (live : LiveOnly memory (fun id => id = 0)) :
      Phase q (.running memory (base8_s002 q pA) trace)
  | allocB (memory : State) (pA : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 sevenByte)
      (nextOne : memory.next = 1)
      (live : LiveOnly memory (fun id => id = 0)) :
      Phase q (.running memory (base8_s003 q pA) trace)
  | storeB (memory : State) (pA pB : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 sevenByte)
      (atB : ByteAt memory pB 1 .uninit)
      (live : LiveOnly memory (fun id => id = 0 ∨ id = 1)) :
      Phase q (.running memory (base8_s004 q pA pB) trace)
  | loadB (memory : State) (pA pB : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 sevenByte)
      (atB : ByteAt memory pB 1 (signalByte q))
      (live : LiveOnly memory (fun id => id = 0 ∨ id = 1)) :
      Phase q (.running memory (base8_s005 pA pB) trace)
  | freeB (memory : State) (pA pB : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 sevenByte)
      (atB : ByteAt memory pB 1 (signalByte q))
      (live : LiveOnly memory (fun id => id = 0 ∨ id = 1)) :
      Phase q (.running memory (base8_s006 pA pB) trace)
  | loadA (memory : State) (pA : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 sevenByte)
      (live : LiveOnly memory (fun id => id = 0)) :
      Phase q (.running memory (base8_s007 pA) trace)
  | freeA (memory : State) (pA : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 sevenByte)
      (live : LiveOnly memory (fun id => id = 0)) :
      Phase q (.running memory (base8_s008 pA) trace)
  | done (memory : State) (trace : List Event) (dead : NoLive memory) :
      Phase q (.running memory .done trace)
  | completed (memory : State) (trace : List Event) (dead : NoLive memory) :
      Phase q (.completed memory trace)

/-- Every actual candidate-specific edge preserves the phase invariant.
The actual dispatcher determines the pointer and reply constructor; every
successful result is derived internally from facts of the current phase. -/
theorem phase_preserved {q : Bool} {before after : Config State}
    (phase : Phase q before) (edge : SourceStep before after) : Phase q after := by
  obtain ⟨candidate, successor⟩ := edge
  cases phase with
  | entry trace =>
    by_cases valid : AllocationCandidate empty 1 1 candidate
    · have answer := allocate_one_good empty candidate valid
      simp only [MemoryExecution.next, base8, base8_s001, answer] at successor
      cases successor
      have supported : LiveOnly (append empty (freshAllocation .heap 1 1 candidate))
          (fun id => id = 0) := by
        refine liveOnly_mono (second := fun id => id = 0)
          (append_liveOnly empty_liveOnly (freshAllocation .heap 1 1 candidate)) ?_
        intro id member
        rcases member with minted | impossible
        · exact minted
        · exact False.elim impossible
      exact Phase.storeA _ _ _ (byteAt_fresh empty candidate) rfl supported
    · have answer := allocate_one_absent empty candidate valid
      simp only [MemoryExecution.next, base8, base8_s001, answer] at successor
      cases successor
  | storeA memory pA trace atA nextOne live =>
    obtain ⟨written, stored, atWritten⟩ := byteAt_store atA sevenByte
    have stored' : store memory pA sevenBytes 1 = .ok written := stored
    have answer : sourceExecute candidate memory (.store pA sevenBytes 1) =
        .good .unit written := by
      simp only [sourceExecute, stored', liftResult]
    have nextWritten : written.next = 1 :=
      (ProofCostFrames.store_preserves_next stored').trans nextOne
    have supported := store_preserves_liveOnly live stored'
    simp only [MemoryExecution.next, base8_s002, answer] at successor
    cases successor
    exact Phase.allocB written pA _ atWritten nextWritten supported
  | allocB memory pA trace atA nextOne live =>
    by_cases valid : AllocationCandidate memory 1 1 candidate
    · have answer := allocate_one_good memory candidate valid
      have atOld : ByteAt (append memory (freshAllocation .heap 1 1 candidate))
          pA 0 sevenByte := by
        exact byteAt_append_other atA (by rw [nextOne]; decide)
          (freshAllocation .heap 1 1 candidate)
      have atNew : ByteAt (append memory (freshAllocation .heap 1 1 candidate))
          ⟨candidate, some memory.next⟩ 1 Byte.uninit := by
        simpa only [nextOne] using byteAt_fresh memory candidate
      have supported : LiveOnly (append memory (freshAllocation .heap 1 1 candidate))
          (fun id => id = 0 ∨ id = 1) := by
        refine liveOnly_mono (second := fun id => id = 0 ∨ id = 1)
          (append_liveOnly live (freshAllocation .heap 1 1 candidate)) ?_
        intro id member
        rcases member with minted | old
        · exact Or.inr (minted.trans nextOne)
        · exact Or.inl old
      simp only [MemoryExecution.next, base8_s003, answer] at successor
      cases successor
      exact Phase.storeB _ pA _ _ atOld atNew supported
    · have answer := allocate_one_absent memory candidate valid
      simp only [MemoryExecution.next, base8_s003, answer] at successor
      cases successor
  | storeB memory pA pB trace atA atB live =>
    obtain ⟨written, stored, atWritten⟩ := byteAt_store atB (signalByte q)
    have stored' : store memory pB (signalBytes q) 1 = .ok written := stored
    have atOld : ByteAt written pA 0 sevenByte :=
      byteAt_store_other (written := pB) (writtenId := 1)
        atA atB.1 (by decide) stored'
    have supported := store_preserves_liveOnly live stored'
    have answer : sourceExecute candidate memory (.store pB (signalBytes q) 1) =
        .good .unit written := by
      simp only [sourceExecute, stored', liftResult]
    simp only [MemoryExecution.next, base8_s004, answer] at successor
    cases successor
    exact Phase.loadB written pA pB _ atOld atWritten supported
  | loadB memory pA pB trace atA atB live =>
    have loaded : load memory pB 1 1 = .ok (signalBytes q, memory) := byteAt_load atB
    have answer : sourceExecute candidate memory (.load pB 1 1) =
        .good (.bytes (signalBytes q)) memory := by
      simp only [sourceExecute, loaded, liftResult]
    simp only [MemoryExecution.next, base8_s005, answer] at successor
    cases successor
    exact Phase.freeB memory pA pB _ atA atB live
  | freeB memory pA pB trace atA atB live =>
    obtain ⟨freed, released, _⟩ := byteAt_free atB
    have atOld : ByteAt freed pA 0 sevenByte :=
      byteAt_free_other (freed := pB) (freedId := 1)
        atA atB.1 (by decide) released
    have narrowed := free_removes_liveOnly (p := pB) (id := 1) live atB.1 released
    have supported : LiveOnly freed (fun id => id = 0) := by
      refine liveOnly_mono (second := fun id => id = 0) narrowed ?_
      intro id member
      rcases member with ⟨old, notB⟩
      rcases old with isA | isB
      · exact isA
      · exact False.elim (notB isB)
    have answer : sourceExecute candidate memory (.free pB .heap 1 1) =
        .good .unit freed := by
      simp only [sourceExecute, released, liftResult]
    simp only [MemoryExecution.next, base8_s006, answer] at successor
    cases successor
    exact Phase.loadA freed pA _ atOld supported
  | loadA memory pA trace atA live =>
    have loaded : load memory pA 1 1 = .ok (sevenBytes, memory) := byteAt_load atA
    have answer : sourceExecute candidate memory (.load pA 1 1) =
        .good (.bytes sevenBytes) memory := by
      simp only [sourceExecute, loaded, liftResult]
    simp only [MemoryExecution.next, base8_s007, answer] at successor
    cases successor
    exact Phase.freeA memory pA _ atA live
  | freeA memory pA trace atA live =>
    obtain ⟨freed, released, _⟩ := byteAt_free atA
    have narrowed := free_removes_liveOnly (p := pA) (id := 0) live atA.1 released
    have dead : NoLive freed := by
      apply (noLive_iff_liveOnly_empty freed).mpr
      refine liveOnly_mono (second := fun _ => False) narrowed ?_
      intro id member
      exact member.2 member.1
    have answer : sourceExecute candidate memory (.free pA .heap 1 1) =
        .good .unit freed := by
      simp only [sourceExecute, released, liftResult]
    simp only [MemoryExecution.next, base8_s008, answer] at successor
    cases successor
    exact Phase.done freed _ dead
  | done memory trace dead =>
    simp only [MemoryExecution.next] at successor
    cases successor
    exact Phase.completed memory trace dead
  | completed memory trace dead =>
    simp only [MemoryExecution.next] at successor
    cases successor

theorem phase_excludes_bad {q : Bool} {config : Config State}
    (phase : Phase q config) : ¬ Bad config := by
  cases phase <;> exact id

theorem phase_completed_noLive {q : Bool} {memory : State} {trace : List Event}
    (phase : Phase q (.completed memory trace)) : NoLive memory := by
  cases phase
  assumption

/-- Every finite path from the exact common root, including horizon zero. -/
theorem reachable_phase (q : Bool) {reached : Config State}
    (path : Reach SourceStep (initial base8 q) reached) : Phase q reached :=
  invariant_reachable (Invariant := Phase q) (Phase.entry []) phase_preserved path

/-- Exact common all-candidate finite-prefix safety AND normal-completion
resource claim. There is no successful-allocation or termination premise. -/
theorem base8_claim (q : Bool) : ProgramCostCommon.Base8Claim q := by
  constructor
  · exact invariant_noUB (Invariant := Phase q) (Phase.entry []) phase_preserved
      (fun _ phase => phase_excludes_bad phase)
  · intro memory trace path
    exact phase_completed_noLive (reachable_phase q path)

#print axioms allocate_one_good
#print axioms allocate_one_absent
#print axioms phase_preserved
#print axioms phase_excludes_bad
#print axioms phase_completed_noLive
#print axioms reachable_phase
#print axioms base8_claim

end AnnealResearch.ProgramCostInvariant8
