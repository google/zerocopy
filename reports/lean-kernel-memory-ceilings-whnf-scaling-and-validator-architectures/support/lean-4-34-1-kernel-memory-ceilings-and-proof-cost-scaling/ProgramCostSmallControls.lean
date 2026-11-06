import AnnealResearch.ProgramCostPrimitives

/-!
Selected actual executions for the program-specific proof-cost pilot.
These are nonvacuity and all-choice counterexample controls, not either
positive proof route. No whole-program safety theorem is reused here.
Only candidates 16/32 (completion), 2 (the stale-pointer bad prefix), and
0 (an absent allocation edge) are selected; the runtime relation is unchanged.
-/
namespace AnnealResearch.ProgramCostSmallControls

open Execution MemoryExecution MiniRustReference ProgramCostCommon ProgramCostPrimitives

def pointerA : Ptr := ⟨16, some 0⟩
def pointerB : Ptr := ⟨32, some 1⟩
def freshA : Allocation := freshAllocation .heap 1 1 16
def freshB : Allocation := freshAllocation .heap 1 1 32
def allocatedA : State := append empty freshA
def writtenA : State := replace allocatedA 0 (writeByte freshA sevenByte)
def bothAllocated : State := append writtenA freshB

/- These states are given independently of allocator/store return extraction.
Later B-write and free states are existentially supplied by proved actual
primitive equations, never a default or presumed successful branch. -/
theorem selected_candidates :
    AllocationCandidate empty 1 1 16 ∧
    AllocationCandidate writtenA 1 1 32 ∧
    AllocationCandidate empty 1 1 2 := by
  decide

theorem first_allocate : allocateAt empty .heap 1 1 16 = .ok (pointerA, allocatedA) := by
  simp [allocateAt, Nat.not_le.mpr (show 1 < sizeLimit from by decide),
    selected_candidates.1]
  exact ⟨rfl, rfl⟩

theorem second_allocate :
    allocateAt writtenA .heap 1 1 32 = .ok (pointerB, bothAllocated) := by
  simp [allocateAt, Nat.not_le.mpr (show 1 < sizeLimit from by decide),
    selected_candidates.2.1]
  exact ⟨rfl, rfl⟩

theorem storedA_facts :
    store allocatedA pointerA sevenBytes 1 = .ok writtenA ∧
    ByteAt writtenA pointerA 0 sevenByte := by
  constructor
  · exact oneByte_store (memory := allocatedA) (p := pointerA) (id := 0)
      (allocation := freshA) rfl rfl rfl rfl rfl sevenByte
  · refine ⟨rfl, writeByte freshA sevenByte, ?_, rfl, rfl, rfl, rfl, rfl, ?_⟩
    · simp [writtenA, replace]
    · simp [writeByte]

def trace1 : List Event := [.answered (.allocate .heap 1 1) (.pointer pointerA)]
def trace2 : List Event := trace1 ++ [.answered (.store pointerA sevenBytes 1) .unit]
def trace3 : List Event := trace2 ++ [.answered (.allocate .heap 1 1) (.pointer pointerB)]
def trace4 (q : Bool) : List Event :=
  trace3 ++ [.answered (.store pointerB (signalBytes q) 1) .unit]
def trace5 (q : Bool) : List Event :=
  trace4 q ++ [.answered (.load pointerB 1 1) (.bytes (signalBytes q))]
def trace6 (q : Bool) : List Event :=
  trace5 q ++ [.answered (.free pointerB .heap 1 1) .unit]
def trace7 (q : Bool) : List Event :=
  trace6 q ++ [.answered (.load pointerA 1 1) (.bytes sevenBytes)]
def trace8 (q : Bool) : List Event :=
  trace7 q ++ [.answered (.free pointerA .heap 1 1) .unit]

/-- Seven actual calls and normal completion after A's actual pointer reply.
This selected-execution suffix is also used by the non-address-two mutant. -/
theorem base8_suffix_completed (q : Bool) :
    ∃ final,
      Reach SourceStep
        (.running allocatedA (base8_s002 q pointerA) trace1)
        (.completed final (trace8 q)) ∧ NoLive final := by
  have atA : ByteAt writtenA pointerA 0 sevenByte := storedA_facts.2
  have atAWithB : ByteAt bothAllocated pointerA 0 sevenByte :=
    byteAt_append_other atA (by decide) freshB
  have atB : ByteAt bothAllocated pointerB 1 Byte.uninit :=
    byteAt_fresh writtenA 32
  obtain ⟨writtenB, storeB, atBWritten⟩ := byteAt_store atB (signalByte q)
  have storeB' : store bothAllocated pointerB (signalBytes q) 1 = .ok writtenB := storeB
  have atAWritten : ByteAt writtenB pointerA 0 sevenByte :=
    byteAt_store_other (written := pointerB) (writtenId := 1)
      atAWithB rfl (by decide) storeB'
  have loadB : load writtenB pointerB 1 1 = .ok (signalBytes q, writtenB) :=
    byteAt_load atBWritten
  obtain ⟨freedB, freeB, _⟩ := byteAt_free atBWritten
  have atAAfterFreeB : ByteAt freedB pointerA 0 sevenByte :=
    byteAt_free_other (freed := pointerB) (freedId := 1)
      atAWritten rfl (by decide) freeB
  have loadA : load freedB pointerA 1 1 = .ok (sevenBytes, freedB) :=
    byteAt_load atAAfterFreeB
  obtain ⟨final, freeA, _⟩ := byteAt_free atAAfterFreeB

  have firstLive := append_liveOnly empty_liveOnly freshA
  have firstWrittenLive := store_preserves_liveOnly firstLive storedA_facts.1
  have bothLive := append_liveOnly firstWrittenLive freshB
  have writtenLive := store_preserves_liveOnly bothLive storeB'
  have afterB : LiveOnly freedB
      (fun id => (id = writtenA.next ∨ id = empty.next ∨ False) ∧ id ≠ 1) :=
    free_removes_liveOnly (p := pointerB) (id := 1) writtenLive rfl freeB
  have afterA : LiveOnly final
      (fun id => ((id = writtenA.next ∨ id = empty.next ∨ False) ∧ id ≠ 1) ∧ id ≠ 0) :=
    free_removes_liveOnly (p := pointerA) (id := 0) afterB rfl freeA
  have dead : NoLive final := by
    apply (noLive_iff_liveOnly_empty final).mpr
    refine liveOnly_mono (second := fun _ => False) afterA ?_
    intro id member
    rcases member with ⟨⟨which, notB⟩, notA⟩
    rcases which with isB | isA | impossible
    · exact notB isB
    · exact notA isA
    · exact impossible

  have step2 : SourceStep
      (.running allocatedA (base8_s002 q pointerA) trace1)
      (.running writtenA (base8_s003 q pointerA) trace2) := by
    refine ⟨0, ?_⟩
    simp only [MemoryExecution.next, base8_s002, sourceExecute,
      storedA_facts.1, liftResult]
    rfl
  have step3 : SourceStep
      (.running writtenA (base8_s003 q pointerA) trace2)
      (.running bothAllocated (base8_s004 q pointerA pointerB) trace3) := by
    refine ⟨32, ?_⟩
    simp only [MemoryExecution.next, base8_s003, sourceExecute,
      second_allocate, liftResult]
    rfl
  have step4 : SourceStep
      (.running bothAllocated (base8_s004 q pointerA pointerB) trace3)
      (.running writtenB (base8_s005 pointerA pointerB) (trace4 q)) := by
    refine ⟨0, ?_⟩
    simp only [MemoryExecution.next, base8_s004, sourceExecute, storeB', liftResult]
    rfl
  have step5 : SourceStep
      (.running writtenB (base8_s005 pointerA pointerB) (trace4 q))
      (.running writtenB (base8_s006 pointerA pointerB) (trace5 q)) := by
    refine ⟨0, ?_⟩
    simp only [MemoryExecution.next, base8_s005, sourceExecute, loadB, liftResult]
    rfl
  have step6 : SourceStep
      (.running writtenB (base8_s006 pointerA pointerB) (trace5 q))
      (.running freedB (base8_s007 pointerA) (trace6 q)) := by
    refine ⟨0, ?_⟩
    simp only [MemoryExecution.next, base8_s006, sourceExecute, freeB, liftResult]
    rfl
  have step7 : SourceStep
      (.running freedB (base8_s007 pointerA) (trace6 q))
      (.running freedB (base8_s008 pointerA) (trace7 q)) := by
    refine ⟨0, ?_⟩
    simp only [MemoryExecution.next, base8_s007, sourceExecute, loadA, liftResult]
    rfl
  have step8 : SourceStep
      (.running freedB (base8_s008 pointerA) (trace7 q))
      (.running final .done (trace8 q)) := by
    refine ⟨0, ?_⟩
    simp only [MemoryExecution.next, base8_s008, sourceExecute, freeA, liftResult]
    rfl
  have complete : SourceStep (.running final .done (trace8 q))
      (.completed final (trace8 q)) := ⟨0, rfl⟩
  exact ⟨final,
    Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.tail
      (Reach.tail (Reach.tail (Reach.refl _) step2) step3) step4) step5) step6)
      step7) step8) complete,
    dead⟩

/-- For both Bool inputs, the exact base8 body and the address-sensitive
mutant have an actual eight-answer, NoLive normal completion. -/
theorem completion_paths (q : Bool) :
    ∃ final, NoLive final ∧ (trace8 q).length = 8 ∧
      Reach SourceStep (initial base8 q) (.completed final (trace8 q)) ∧
      Reach SourceStep (initial staleChoice8 q) (.completed final (trace8 q)) := by
  obtain ⟨final, suffix, dead⟩ := base8_suffix_completed q
  have baseFirst : SourceStep (initial base8 q)
      (.running allocatedA (base8_s002 q pointerA) trace1) := by
    refine ⟨16, ?_⟩
    simp only [initial, base8, base8_s001, MemoryExecution.next, sourceExecute,
      first_allocate, liftResult]
    rfl
  have mutantFirst : SourceStep (initial staleChoice8 q)
      (.running allocatedA (base8_s002 q pointerA) trace1) := by
    refine ⟨16, ?_⟩
    simp [initial, staleChoice8, MemoryExecution.next, sourceExecute,
      first_allocate, liftResult, pointerA, trace1]
  refine ⟨final, dead, ?_,
    (Reach.tail (Reach.refl _) baseFirst).trans suffix,
    (Reach.tail (Reach.refl _) mutantFirst).trans suffix⟩
  simp [trace8, trace7, trace6, trace5, trace4, trace3, trace2, trace1]

theorem base8_completion (q : Bool) :
    ∃ final, Reach SourceStep (initial base8 q) (.completed final (trace8 q)) ∧
      NoLive final := by
  obtain ⟨final, dead, _, path, _⟩ := completion_paths q
  exact ⟨final, path, dead⟩

theorem staleChoice8_safe_completion (q : Bool) :
    ∃ final, Reach SourceStep (initial staleChoice8 q)
      (.completed final (trace8 q)) ∧ NoLive final := by
  obtain ⟨final, dead, _, _, path⟩ := completion_paths q
  exact ⟨final, path, dead⟩

/- Address two is a different feasible branch of the same initial allocation.
The selected pointer is freed, then actually loaded before the success-only
continuation could spin. The bad configuration has no trace field in this API. -/
def pointerTwo : Ptr := ⟨2, some 0⟩
def freshTwo : Allocation := freshAllocation .heap 1 1 2
def allocatedTwo : State := append empty freshTwo
def freedTwo : State := replace allocatedTwo 0 { freshTwo with live := false }
def twoTrace1 : List Event := [.answered (.allocate .heap 1 1) (.pointer pointerTwo)]
def twoTrace2 : List Event := twoTrace1 ++ [.answered (.free pointerTwo .heap 1 1) .unit]

theorem two_allocate : allocateAt empty .heap 1 1 2 = .ok (pointerTwo, allocatedTwo) := by
  simp [allocateAt, Nat.not_le.mpr (show 1 < sizeLimit from by decide),
    selected_candidates.2.2]
  exact ⟨rfl, rfl⟩

theorem selected_allocation_answers :
    sourceExecute 16 empty (.allocate .heap 1 1) = .good (.pointer pointerA) allocatedA ∧
    sourceExecute 32 writtenA (.allocate .heap 1 1) =
      .good (.pointer pointerB) bothAllocated ∧
    sourceExecute 2 empty (.allocate .heap 1 1) = .good (.pointer pointerTwo) allocatedTwo := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [sourceExecute, first_allocate, liftResult]
  · simp only [sourceExecute, second_allocate, liftResult]
  · simp only [sourceExecute, two_allocate, liftResult]

theorem staleChoice8_bad_prefix (q : Bool) :
    Reach SourceStep (initial staleChoice8 q) (.bad freedTwo .dead) := by
  have freed : free allocatedTwo pointerTwo .heap 1 1 = .ok freedTwo :=
    oneByte_free (memory := allocatedTwo) (p := pointerTwo) (id := 0)
      (allocation := freshTwo) rfl rfl rfl rfl rfl rfl rfl
  have stale : load freedTwo pointerTwo 1 1 = .ub .dead := rfl
  have enter : SourceStep (initial staleChoice8 q)
      (.running allocatedTwo (staleChoice8_free pointerTwo) twoTrace1) := by
    refine ⟨2, ?_⟩
    simp [initial, staleChoice8, MemoryExecution.next, sourceExecute,
      two_allocate, liftResult, pointerTwo, twoTrace1]
  have release : SourceStep
      (.running allocatedTwo (staleChoice8_free pointerTwo) twoTrace1)
      (.running freedTwo (staleChoice8_load pointerTwo) twoTrace2) := by
    refine ⟨0, ?_⟩
    simp only [MemoryExecution.next, staleChoice8_free, sourceExecute, freed, liftResult]
    rfl
  have bad : SourceStep
      (.running freedTwo (staleChoice8_load pointerTwo) twoTrace2)
      (.bad freedTwo .dead) := by
    refine ⟨0, ?_⟩
    simp only [MemoryExecution.next, staleChoice8_load, sourceExecute, stale, liftResult]
  exact Reach.tail (Reach.tail (Reach.tail (Reach.refl _) enter) release) bad

theorem staleChoice8_not_noUB (q : Bool) :
    ¬ NoUB SourceStep Bad (initial staleChoice8 q) :=
  bad_prefix_not_noUB (staleChoice8_bad_prefix q) True.intro

theorem stale_bad_terminal (candidate : Nat) :
    next sourceExecute candidate (.bad freedTwo .dead) = none := rfl

/-- A rejected candidate is absent, even though other candidates have the
completion/bad-prefix witnesses above. It is not a stop or stuttering step. -/
theorem candidate_zero_absent (q : Bool) :
    allocateAt empty .heap 1 1 0 = .noChoice ∧
    next sourceExecute 0 (initial base8 q) = none ∧
    next sourceExecute 0 (initial staleChoice8 q) = none := by
  exact ⟨rfl, rfl, rfl⟩

/- Audit aggregates and substantive controls, not every selected execution edge.
The two convenience projections of completion_paths are intentionally not
printed again. No positive all-prefix NoUB/Claim endpoint is supplied here. -/
#print axioms selected_candidates
#print axioms selected_allocation_answers
#print axioms storedA_facts
#print axioms base8_suffix_completed
#print axioms completion_paths
#print axioms staleChoice8_bad_prefix
#print axioms staleChoice8_not_noUB
#print axioms stale_bad_terminal
#print axioms candidate_zero_absent

end AnnealResearch.ProgramCostSmallControls
