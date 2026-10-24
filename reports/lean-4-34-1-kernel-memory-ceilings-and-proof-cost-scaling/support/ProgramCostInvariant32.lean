import AnnealResearch.ProgramCostPrimitives

/-!
Direct operational phase-invariant proof for the literal thirty-two-call body.
Every site has its own materialized Phase constructor and preservation case.
All route-specific setup is in this measured module; the eight-node route is
not imported or applied. Text generation only expanded these fixed cases.
No evaluator, runtime repetition, graph validator, or cached suite is added.
-/
namespace AnnealResearch.ProgramCostInvariant32

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

/-- Phase facts are derived along actual executions. Each named constructor
contains the corresponding frozen source stage and its current byte facts. -/
inductive Phase (q : Bool) : Config State → Prop where
  | s001 (trace : List Event) :
      Phase q (.running empty (base32 q) trace)
  | s002 (memory : State) (pA : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 .uninit)
      (nextOne : memory.next = 1)
      (live : LiveOnly memory (fun id => id = 0)) :
      Phase q (.running memory (base32_s002 q pA) trace)
  | s003 (memory : State) (pA : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 sevenByte)
      (nextOne : memory.next = 1)
      (live : LiveOnly memory (fun id => id = 0)) :
      Phase q (.running memory (base32_s003 q pA) trace)
  | s004 (memory : State) (pA pB : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 sevenByte)
      (atB : ByteAt memory pB 1 .uninit)
      (live : LiveOnly memory (fun id => id = 0 ∨ id = 1)) :
      Phase q (.running memory (base32_s004 q pA pB) trace)
  | s005 (memory : State) (pA pB : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 sevenByte)
      (atB : ByteAt memory pB 1 (signalByte q))
      (live : LiveOnly memory (fun id => id = 0 ∨ id = 1)) :
      Phase q (.running memory (base32_s005 q pA pB) trace)
  | s006 (memory : State) (pA pB : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 sevenByte)
      (atB : ByteAt memory pB 1 (signalByte q))
      (live : LiveOnly memory (fun id => id = 0 ∨ id = 1)) :
      Phase q (.running memory (base32_s006 q pA pB) trace)
  | s007 (memory : State) (pA pB : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 sevenByte)
      (atB : ByteAt memory pB 1 (signalByte q))
      (live : LiveOnly memory (fun id => id = 0 ∨ id = 1)) :
      Phase q (.running memory (base32_s007 q pA pB) trace)
  | s008 (memory : State) (pA pB : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 sevenByte)
      (atB : ByteAt memory pB 1 (signalByte q))
      (live : LiveOnly memory (fun id => id = 0 ∨ id = 1)) :
      Phase q (.running memory (base32_s008 q pA pB) trace)
  | s009 (memory : State) (pA pB : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 sevenByte)
      (atB : ByteAt memory pB 1 (signalByte q))
      (live : LiveOnly memory (fun id => id = 0 ∨ id = 1)) :
      Phase q (.running memory (base32_s009 q pA pB) trace)
  | s010 (memory : State) (pA pB : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 sevenByte)
      (atB : ByteAt memory pB 1 (signalByte q))
      (live : LiveOnly memory (fun id => id = 0 ∨ id = 1)) :
      Phase q (.running memory (base32_s010 q pA pB) trace)
  | s011 (memory : State) (pA pB : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 nineByte)
      (atB : ByteAt memory pB 1 (signalByte q))
      (live : LiveOnly memory (fun id => id = 0 ∨ id = 1)) :
      Phase q (.running memory (base32_s011 q pA pB) trace)
  | s012 (memory : State) (pA pB : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 nineByte)
      (atB : ByteAt memory pB 1 (signalByte q))
      (live : LiveOnly memory (fun id => id = 0 ∨ id = 1)) :
      Phase q (.running memory (base32_s012 q pA pB) trace)
  | s013 (memory : State) (pA pB : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 nineByte)
      (atB : ByteAt memory pB 1 (signalByte q))
      (live : LiveOnly memory (fun id => id = 0 ∨ id = 1)) :
      Phase q (.running memory (base32_s013 q pA pB) trace)
  | s014 (memory : State) (pA pB : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 nineByte)
      (atB : ByteAt memory pB 1 (signalByte q))
      (live : LiveOnly memory (fun id => id = 0 ∨ id = 1)) :
      Phase q (.running memory (base32_s014 q pA pB) trace)
  | s015 (memory : State) (pA pB : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 sevenByte)
      (atB : ByteAt memory pB 1 (signalByte q))
      (live : LiveOnly memory (fun id => id = 0 ∨ id = 1)) :
      Phase q (.running memory (base32_s015 q pA pB) trace)
  | s016 (memory : State) (pA pB : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 sevenByte)
      (atB : ByteAt memory pB 1 (signalByte q))
      (live : LiveOnly memory (fun id => id = 0 ∨ id = 1)) :
      Phase q (.running memory (base32_s016 q pA pB) trace)
  | s017 (memory : State) (pA pB : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 sevenByte)
      (atB : ByteAt memory pB 1 (signalByte q))
      (live : LiveOnly memory (fun id => id = 0 ∨ id = 1)) :
      Phase q (.running memory (base32_s017 q pA pB) trace)
  | s018 (memory : State) (pA pB : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 sevenByte)
      (atB : ByteAt memory pB 1 (signalByte q))
      (live : LiveOnly memory (fun id => id = 0 ∨ id = 1)) :
      Phase q (.running memory (base32_s018 q pA pB) trace)
  | s019 (memory : State) (pA pB : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 nineByte)
      (atB : ByteAt memory pB 1 (signalByte q))
      (live : LiveOnly memory (fun id => id = 0 ∨ id = 1)) :
      Phase q (.running memory (base32_s019 q pA pB) trace)
  | s020 (memory : State) (pA pB : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 nineByte)
      (atB : ByteAt memory pB 1 (signalByte q))
      (live : LiveOnly memory (fun id => id = 0 ∨ id = 1)) :
      Phase q (.running memory (base32_s020 q pA pB) trace)
  | s021 (memory : State) (pA pB : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 nineByte)
      (atB : ByteAt memory pB 1 (signalByte q))
      (live : LiveOnly memory (fun id => id = 0 ∨ id = 1)) :
      Phase q (.running memory (base32_s021 q pA pB) trace)
  | s022 (memory : State) (pA pB : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 nineByte)
      (atB : ByteAt memory pB 1 (signalByte q))
      (live : LiveOnly memory (fun id => id = 0 ∨ id = 1)) :
      Phase q (.running memory (base32_s022 q pA pB) trace)
  | s023 (memory : State) (pA pB : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 sevenByte)
      (atB : ByteAt memory pB 1 (signalByte q))
      (live : LiveOnly memory (fun id => id = 0 ∨ id = 1)) :
      Phase q (.running memory (base32_s023 q pA pB) trace)
  | s024 (memory : State) (pA pB : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 sevenByte)
      (atB : ByteAt memory pB 1 (signalByte q))
      (live : LiveOnly memory (fun id => id = 0 ∨ id = 1)) :
      Phase q (.running memory (base32_s024 q pA pB) trace)
  | s025 (memory : State) (pA pB : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 sevenByte)
      (atB : ByteAt memory pB 1 (signalByte q))
      (live : LiveOnly memory (fun id => id = 0 ∨ id = 1)) :
      Phase q (.running memory (base32_s025 q pA pB) trace)
  | s026 (memory : State) (pA pB : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 sevenByte)
      (atB : ByteAt memory pB 1 (signalByte q))
      (live : LiveOnly memory (fun id => id = 0 ∨ id = 1)) :
      Phase q (.running memory (base32_s026 q pA pB) trace)
  | s027 (memory : State) (pA pB : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 nineByte)
      (atB : ByteAt memory pB 1 (signalByte q))
      (live : LiveOnly memory (fun id => id = 0 ∨ id = 1)) :
      Phase q (.running memory (base32_s027 q pA pB) trace)
  | s028 (memory : State) (pA pB : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 nineByte)
      (atB : ByteAt memory pB 1 (signalByte q))
      (live : LiveOnly memory (fun id => id = 0 ∨ id = 1)) :
      Phase q (.running memory (base32_s028 pA pB) trace)
  | s029 (memory : State) (pA pB : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 nineByte)
      (atB : ByteAt memory pB 1 (signalByte q))
      (live : LiveOnly memory (fun id => id = 0 ∨ id = 1)) :
      Phase q (.running memory (base32_s029 pA pB) trace)
  | s030 (memory : State) (pA pB : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 nineByte)
      (atB : ByteAt memory pB 1 (signalByte q))
      (live : LiveOnly memory (fun id => id = 0 ∨ id = 1)) :
      Phase q (.running memory (base32_s030 pA pB) trace)
  | s031 (memory : State) (pA : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 nineByte)
      (live : LiveOnly memory (fun id => id = 0)) :
      Phase q (.running memory (base32_s031 pA) trace)
  | s032 (memory : State) (pA : Ptr) (trace : List Event)
      (atA : ByteAt memory pA 0 nineByte)
      (live : LiveOnly memory (fun id => id = 0)) :
      Phase q (.running memory (base32_s032 pA) trace)
  | done (memory : State) (trace : List Event) (dead : NoLive memory) :
      Phase q (.running memory .done trace)
  | completed (memory : State) (trace : List Event) (dead : NoLive memory) :
      Phase q (.completed memory trace)

/-- All thirty-two source sites preserve the operational invariant for every
actual SourceStep, retaining all Nat candidates and exact reply reductions. -/
theorem phase_preserved {q : Bool} {before after : Config State}
    (phase : Phase q before) (edge : SourceStep before after) : Phase q after := by
  obtain ⟨candidate, successor⟩ := edge
  cases phase with
  | s001 trace =>
    by_cases valid : AllocationCandidate empty 1 1 candidate
    · have answer := allocate_one_good empty candidate valid
      simp only [MemoryExecution.next, base32, base32_s001, answer] at successor
      cases successor
      have supported : LiveOnly (append empty (freshAllocation .heap 1 1 candidate))
          (fun id => id = 0) := by
        refine liveOnly_mono (second := fun id => id = 0)
          (append_liveOnly empty_liveOnly (freshAllocation .heap 1 1 candidate)) ?_
        intro id member
        rcases member with minted | impossible
        · exact minted
        · exact False.elim impossible
      exact Phase.s002 _ _ _ (byteAt_fresh empty candidate) rfl supported
    · have answer := allocate_one_absent empty candidate valid
      simp only [MemoryExecution.next, base32, base32_s001, answer] at successor
      cases successor
  | s002 memory pA trace atA nextOne live =>
    obtain ⟨written, stored, atWritten⟩ := byteAt_store atA sevenByte
    have stored' : store memory pA sevenBytes 1 = .ok written := stored
    have answer : sourceExecute candidate memory (.store pA sevenBytes 1) =
        .good .unit written := by
      simp only [sourceExecute, stored', liftResult]
    have nextWritten : written.next = 1 :=
      (ProofCostFrames.store_preserves_next stored').trans nextOne
    have supported := store_preserves_liveOnly live stored'
    simp only [MemoryExecution.next, base32_s002, answer] at successor
    cases successor
    exact Phase.s003 written pA _ atWritten nextWritten supported
  | s003 memory pA trace atA nextOne live =>
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
      simp only [MemoryExecution.next, base32_s003, answer] at successor
      cases successor
      exact Phase.s004 _ pA _ _ atOld atNew supported
    · have answer := allocate_one_absent memory candidate valid
      simp only [MemoryExecution.next, base32_s003, answer] at successor
      cases successor
  | s004 memory pA pB trace atA atB live =>
    obtain ⟨written, stored, atWritten⟩ := byteAt_store atB (signalByte q)
    have stored' : store memory pB (signalBytes q) 1 = .ok written := stored
    have atOld : ByteAt written pA 0 sevenByte :=
      byteAt_store_other (written := pB) (writtenId := 1)
        atA atB.1 (by decide) stored'
    have supported := store_preserves_liveOnly live stored'
    have answer : sourceExecute candidate memory (.store pB (signalBytes q) 1) =
        .good .unit written := by
      simp only [sourceExecute, stored', liftResult]
    simp only [MemoryExecution.next, base32_s004, answer] at successor
    cases successor
    exact Phase.s005 written pA pB _ atOld atWritten supported
  | s005 memory pA pB trace atA atB live =>
    have loaded : load memory pA 1 1 = .ok (sevenBytes, memory) := byteAt_load atA
    have answer : sourceExecute candidate memory (.load pA 1 1) =
        .good (.bytes sevenBytes) memory := by
      simp only [sourceExecute, loaded, liftResult]
    simp only [MemoryExecution.next, base32_s005, answer] at successor
    cases successor
    exact Phase.s006 memory pA pB _ atA atB live
  | s006 memory pA pB trace atA atB live =>
    obtain ⟨written, stored, atWritten⟩ := byteAt_store atA sevenByte
    have stored' : store memory pA sevenBytes 1 = .ok written := stored
    have atOld : ByteAt written pB 1 (signalByte q) :=
      byteAt_store_other (written := pA) (writtenId := 0)
        atB atA.1 (by decide) stored'
    have supported := store_preserves_liveOnly live stored'
    have answer : sourceExecute candidate memory (.store pA sevenBytes 1) =
        .good .unit written := by
      simp only [sourceExecute, stored', liftResult]
    simp only [MemoryExecution.next, base32_s006, answer] at successor
    cases successor
    exact Phase.s007 written pA pB _ atWritten atOld supported
  | s007 memory pA pB trace atA atB live =>
    obtain ⟨written, stored, atWritten⟩ := byteAt_store atB (signalByte q)
    have stored' : store memory pB (signalBytes q) 1 = .ok written := stored
    have atOld : ByteAt written pA 0 sevenByte :=
      byteAt_store_other (written := pB) (writtenId := 1)
        atA atB.1 (by decide) stored'
    have supported := store_preserves_liveOnly live stored'
    have answer : sourceExecute candidate memory (.store pB (signalBytes q) 1) =
        .good .unit written := by
      simp only [sourceExecute, stored', liftResult]
    simp only [MemoryExecution.next, base32_s007, answer] at successor
    cases successor
    exact Phase.s008 written pA pB _ atOld atWritten supported
  | s008 memory pA pB trace atA atB live =>
    have loaded : load memory pB 1 1 = .ok (signalBytes q, memory) := byteAt_load atB
    have answer : sourceExecute candidate memory (.load pB 1 1) =
        .good (.bytes (signalBytes q)) memory := by
      simp only [sourceExecute, loaded, liftResult]
    simp only [MemoryExecution.next, base32_s008, answer] at successor
    cases successor
    exact Phase.s009 memory pA pB _ atA atB live
  | s009 memory pA pB trace atA atB live =>
    have loaded : load memory pA 1 1 = .ok (sevenBytes, memory) := byteAt_load atA
    have answer : sourceExecute candidate memory (.load pA 1 1) =
        .good (.bytes sevenBytes) memory := by
      simp only [sourceExecute, loaded, liftResult]
    simp only [MemoryExecution.next, base32_s009, answer] at successor
    cases successor
    exact Phase.s010 memory pA pB _ atA atB live
  | s010 memory pA pB trace atA atB live =>
    obtain ⟨written, stored, atWritten⟩ := byteAt_store atA nineByte
    have stored' : store memory pA nineBytes 1 = .ok written := stored
    have atOld : ByteAt written pB 1 (signalByte q) :=
      byteAt_store_other (written := pA) (writtenId := 0)
        atB atA.1 (by decide) stored'
    have supported := store_preserves_liveOnly live stored'
    have answer : sourceExecute candidate memory (.store pA nineBytes 1) =
        .good .unit written := by
      simp only [sourceExecute, stored', liftResult]
    simp only [MemoryExecution.next, base32_s010, answer] at successor
    cases successor
    exact Phase.s011 written pA pB _ atWritten atOld supported
  | s011 memory pA pB trace atA atB live =>
    obtain ⟨written, stored, atWritten⟩ := byteAt_store atB (signalByte q)
    have stored' : store memory pB (signalBytes q) 1 = .ok written := stored
    have atOld : ByteAt written pA 0 nineByte :=
      byteAt_store_other (written := pB) (writtenId := 1)
        atA atB.1 (by decide) stored'
    have supported := store_preserves_liveOnly live stored'
    have answer : sourceExecute candidate memory (.store pB (signalBytes q) 1) =
        .good .unit written := by
      simp only [sourceExecute, stored', liftResult]
    simp only [MemoryExecution.next, base32_s011, answer] at successor
    cases successor
    exact Phase.s012 written pA pB _ atOld atWritten supported
  | s012 memory pA pB trace atA atB live =>
    have loaded : load memory pB 1 1 = .ok (signalBytes q, memory) := byteAt_load atB
    have answer : sourceExecute candidate memory (.load pB 1 1) =
        .good (.bytes (signalBytes q)) memory := by
      simp only [sourceExecute, loaded, liftResult]
    simp only [MemoryExecution.next, base32_s012, answer] at successor
    cases successor
    exact Phase.s013 memory pA pB _ atA atB live
  | s013 memory pA pB trace atA atB live =>
    have loaded : load memory pA 1 1 = .ok (nineBytes, memory) := byteAt_load atA
    have answer : sourceExecute candidate memory (.load pA 1 1) =
        .good (.bytes nineBytes) memory := by
      simp only [sourceExecute, loaded, liftResult]
    simp only [MemoryExecution.next, base32_s013, answer] at successor
    cases successor
    exact Phase.s014 memory pA pB _ atA atB live
  | s014 memory pA pB trace atA atB live =>
    obtain ⟨written, stored, atWritten⟩ := byteAt_store atA sevenByte
    have stored' : store memory pA sevenBytes 1 = .ok written := stored
    have atOld : ByteAt written pB 1 (signalByte q) :=
      byteAt_store_other (written := pA) (writtenId := 0)
        atB atA.1 (by decide) stored'
    have supported := store_preserves_liveOnly live stored'
    have answer : sourceExecute candidate memory (.store pA sevenBytes 1) =
        .good .unit written := by
      simp only [sourceExecute, stored', liftResult]
    simp only [MemoryExecution.next, base32_s014, answer] at successor
    cases successor
    exact Phase.s015 written pA pB _ atWritten atOld supported
  | s015 memory pA pB trace atA atB live =>
    obtain ⟨written, stored, atWritten⟩ := byteAt_store atB (signalByte q)
    have stored' : store memory pB (signalBytes q) 1 = .ok written := stored
    have atOld : ByteAt written pA 0 sevenByte :=
      byteAt_store_other (written := pB) (writtenId := 1)
        atA atB.1 (by decide) stored'
    have supported := store_preserves_liveOnly live stored'
    have answer : sourceExecute candidate memory (.store pB (signalBytes q) 1) =
        .good .unit written := by
      simp only [sourceExecute, stored', liftResult]
    simp only [MemoryExecution.next, base32_s015, answer] at successor
    cases successor
    exact Phase.s016 written pA pB _ atOld atWritten supported
  | s016 memory pA pB trace atA atB live =>
    have loaded : load memory pB 1 1 = .ok (signalBytes q, memory) := byteAt_load atB
    have answer : sourceExecute candidate memory (.load pB 1 1) =
        .good (.bytes (signalBytes q)) memory := by
      simp only [sourceExecute, loaded, liftResult]
    simp only [MemoryExecution.next, base32_s016, answer] at successor
    cases successor
    exact Phase.s017 memory pA pB _ atA atB live
  | s017 memory pA pB trace atA atB live =>
    have loaded : load memory pA 1 1 = .ok (sevenBytes, memory) := byteAt_load atA
    have answer : sourceExecute candidate memory (.load pA 1 1) =
        .good (.bytes sevenBytes) memory := by
      simp only [sourceExecute, loaded, liftResult]
    simp only [MemoryExecution.next, base32_s017, answer] at successor
    cases successor
    exact Phase.s018 memory pA pB _ atA atB live
  | s018 memory pA pB trace atA atB live =>
    obtain ⟨written, stored, atWritten⟩ := byteAt_store atA nineByte
    have stored' : store memory pA nineBytes 1 = .ok written := stored
    have atOld : ByteAt written pB 1 (signalByte q) :=
      byteAt_store_other (written := pA) (writtenId := 0)
        atB atA.1 (by decide) stored'
    have supported := store_preserves_liveOnly live stored'
    have answer : sourceExecute candidate memory (.store pA nineBytes 1) =
        .good .unit written := by
      simp only [sourceExecute, stored', liftResult]
    simp only [MemoryExecution.next, base32_s018, answer] at successor
    cases successor
    exact Phase.s019 written pA pB _ atWritten atOld supported
  | s019 memory pA pB trace atA atB live =>
    obtain ⟨written, stored, atWritten⟩ := byteAt_store atB (signalByte q)
    have stored' : store memory pB (signalBytes q) 1 = .ok written := stored
    have atOld : ByteAt written pA 0 nineByte :=
      byteAt_store_other (written := pB) (writtenId := 1)
        atA atB.1 (by decide) stored'
    have supported := store_preserves_liveOnly live stored'
    have answer : sourceExecute candidate memory (.store pB (signalBytes q) 1) =
        .good .unit written := by
      simp only [sourceExecute, stored', liftResult]
    simp only [MemoryExecution.next, base32_s019, answer] at successor
    cases successor
    exact Phase.s020 written pA pB _ atOld atWritten supported
  | s020 memory pA pB trace atA atB live =>
    have loaded : load memory pB 1 1 = .ok (signalBytes q, memory) := byteAt_load atB
    have answer : sourceExecute candidate memory (.load pB 1 1) =
        .good (.bytes (signalBytes q)) memory := by
      simp only [sourceExecute, loaded, liftResult]
    simp only [MemoryExecution.next, base32_s020, answer] at successor
    cases successor
    exact Phase.s021 memory pA pB _ atA atB live
  | s021 memory pA pB trace atA atB live =>
    have loaded : load memory pA 1 1 = .ok (nineBytes, memory) := byteAt_load atA
    have answer : sourceExecute candidate memory (.load pA 1 1) =
        .good (.bytes nineBytes) memory := by
      simp only [sourceExecute, loaded, liftResult]
    simp only [MemoryExecution.next, base32_s021, answer] at successor
    cases successor
    exact Phase.s022 memory pA pB _ atA atB live
  | s022 memory pA pB trace atA atB live =>
    obtain ⟨written, stored, atWritten⟩ := byteAt_store atA sevenByte
    have stored' : store memory pA sevenBytes 1 = .ok written := stored
    have atOld : ByteAt written pB 1 (signalByte q) :=
      byteAt_store_other (written := pA) (writtenId := 0)
        atB atA.1 (by decide) stored'
    have supported := store_preserves_liveOnly live stored'
    have answer : sourceExecute candidate memory (.store pA sevenBytes 1) =
        .good .unit written := by
      simp only [sourceExecute, stored', liftResult]
    simp only [MemoryExecution.next, base32_s022, answer] at successor
    cases successor
    exact Phase.s023 written pA pB _ atWritten atOld supported
  | s023 memory pA pB trace atA atB live =>
    obtain ⟨written, stored, atWritten⟩ := byteAt_store atB (signalByte q)
    have stored' : store memory pB (signalBytes q) 1 = .ok written := stored
    have atOld : ByteAt written pA 0 sevenByte :=
      byteAt_store_other (written := pB) (writtenId := 1)
        atA atB.1 (by decide) stored'
    have supported := store_preserves_liveOnly live stored'
    have answer : sourceExecute candidate memory (.store pB (signalBytes q) 1) =
        .good .unit written := by
      simp only [sourceExecute, stored', liftResult]
    simp only [MemoryExecution.next, base32_s023, answer] at successor
    cases successor
    exact Phase.s024 written pA pB _ atOld atWritten supported
  | s024 memory pA pB trace atA atB live =>
    have loaded : load memory pB 1 1 = .ok (signalBytes q, memory) := byteAt_load atB
    have answer : sourceExecute candidate memory (.load pB 1 1) =
        .good (.bytes (signalBytes q)) memory := by
      simp only [sourceExecute, loaded, liftResult]
    simp only [MemoryExecution.next, base32_s024, answer] at successor
    cases successor
    exact Phase.s025 memory pA pB _ atA atB live
  | s025 memory pA pB trace atA atB live =>
    have loaded : load memory pA 1 1 = .ok (sevenBytes, memory) := byteAt_load atA
    have answer : sourceExecute candidate memory (.load pA 1 1) =
        .good (.bytes sevenBytes) memory := by
      simp only [sourceExecute, loaded, liftResult]
    simp only [MemoryExecution.next, base32_s025, answer] at successor
    cases successor
    exact Phase.s026 memory pA pB _ atA atB live
  | s026 memory pA pB trace atA atB live =>
    obtain ⟨written, stored, atWritten⟩ := byteAt_store atA nineByte
    have stored' : store memory pA nineBytes 1 = .ok written := stored
    have atOld : ByteAt written pB 1 (signalByte q) :=
      byteAt_store_other (written := pA) (writtenId := 0)
        atB atA.1 (by decide) stored'
    have supported := store_preserves_liveOnly live stored'
    have answer : sourceExecute candidate memory (.store pA nineBytes 1) =
        .good .unit written := by
      simp only [sourceExecute, stored', liftResult]
    simp only [MemoryExecution.next, base32_s026, answer] at successor
    cases successor
    exact Phase.s027 written pA pB _ atWritten atOld supported
  | s027 memory pA pB trace atA atB live =>
    obtain ⟨written, stored, atWritten⟩ := byteAt_store atB (signalByte q)
    have stored' : store memory pB (signalBytes q) 1 = .ok written := stored
    have atOld : ByteAt written pA 0 nineByte :=
      byteAt_store_other (written := pB) (writtenId := 1)
        atA atB.1 (by decide) stored'
    have supported := store_preserves_liveOnly live stored'
    have answer : sourceExecute candidate memory (.store pB (signalBytes q) 1) =
        .good .unit written := by
      simp only [sourceExecute, stored', liftResult]
    simp only [MemoryExecution.next, base32_s027, answer] at successor
    cases successor
    exact Phase.s028 written pA pB _ atOld atWritten supported
  | s028 memory pA pB trace atA atB live =>
    have loaded : load memory pB 1 1 = .ok (signalBytes q, memory) := byteAt_load atB
    have answer : sourceExecute candidate memory (.load pB 1 1) =
        .good (.bytes (signalBytes q)) memory := by
      simp only [sourceExecute, loaded, liftResult]
    simp only [MemoryExecution.next, base32_s028, answer] at successor
    cases successor
    exact Phase.s029 memory pA pB _ atA atB live
  | s029 memory pA pB trace atA atB live =>
    have loaded : load memory pB 1 1 = .ok (signalBytes q, memory) := byteAt_load atB
    have answer : sourceExecute candidate memory (.load pB 1 1) =
        .good (.bytes (signalBytes q)) memory := by
      simp only [sourceExecute, loaded, liftResult]
    simp only [MemoryExecution.next, base32_s029, answer] at successor
    cases successor
    exact Phase.s030 memory pA pB _ atA atB live
  | s030 memory pA pB trace atA atB live =>
    obtain ⟨freed, released, _⟩ := byteAt_free atB
    have atOld : ByteAt freed pA 0 nineByte :=
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
    simp only [MemoryExecution.next, base32_s030, answer] at successor
    cases successor
    exact Phase.s031 freed pA _ atOld supported
  | s031 memory pA trace atA live =>
    have loaded : load memory pA 1 1 = .ok (nineBytes, memory) := byteAt_load atA
    have answer : sourceExecute candidate memory (.load pA 1 1) =
        .good (.bytes nineBytes) memory := by
      simp only [sourceExecute, loaded, liftResult]
    simp only [MemoryExecution.next, base32_s031, answer] at successor
    cases successor
    exact Phase.s032 memory pA _ atA live
  | s032 memory pA trace atA live =>
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
    simp only [MemoryExecution.next, base32_s032, answer] at successor
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
    (path : Reach SourceStep (initial base32 q) reached) : Phase q reached :=
  invariant_reachable (Invariant := Phase q) (Phase.s001 []) phase_preserved path

/-- Exact common all-candidate finite-prefix safety AND normal-completion
resource claim. There is no successful-allocation or termination premise. -/
theorem base32_claim (q : Bool) : ProgramCostCommon.Base32Claim q := by
  constructor
  · exact invariant_noUB (Invariant := Phase q) (Phase.s001 []) phase_preserved
      (fun _ phase => phase_excludes_bad phase)
  · intro memory trace path
    exact phase_completed_noLive (reachable_phase q path)

#print axioms allocate_one_good
#print axioms allocate_one_absent
#print axioms phase_preserved
#print axioms phase_excludes_bad
#print axioms phase_completed_noLive
#print axioms reachable_phase
#print axioms base32_claim

end AnnealResearch.ProgramCostInvariant32
