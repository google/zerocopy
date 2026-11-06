import AnnealResearch.MemoryExamples

/-!
Actual enabled executions for the positive raw-memory family. Feasibility is
proved without a safety or correspondence premise: address 1 is available when
all retained allocation records are dead. Each completed round restores that
condition, so any finite number of rounds can execute before actual spinning.
These are existential paths, not fairness or universal termination claims.
-/

namespace AnnealResearch.MemoryWitnesses

open Execution MemoryExecution MiniRustReference MemoryExamples

def liveBit (state : State) (id : Nat) : Bool :=
  match state.allocations id with
  | none => false
  | some allocation => allocation.live

def NoLive (state : State) : Prop := ∀ id, liveBit state id = false

theorem empty_noLive : NoLive empty := by
  intro id
  rfl

theorem noLive_overlap {state : State} (dead : NoLive state) (base size : Nat) :
    liveOverlap state base size = false := by
  apply List.any_eq_false.mpr
  intro id _
  cases found : state.allocations id with
  | none => simp [found]
  | some allocation =>
    have notLive : allocation.live = false := by simpa [liveBit, found] using dead id
    simp [found, notLive]

theorem noLive_candidate_one {state : State} (dead : NoLive state)
    (size : Nat) (small : size < sizeLimit) : AllocationCandidate state size 1 1 := by
  have room : sizeLimit < addressLimit := by decide
  exact ⟨by decide, by simp, by omega, noLive_overlap dead 1 size⟩

/-- Successful byte stores leave every allocation's liveness unchanged. -/
theorem store_liveBit {state after : State} {pointer : Ptr} {bytes : List Byte}
    {align : Nat} (success : store state pointer bytes align = .ok after) (id : Nat) :
    liveBit after id = liveBit state id := by
  by_cases zeroAlign : align = 0
  · simp [store, zeroAlign] at success
  · by_cases misaligned : pointer.addr % align ≠ 0
    · simp [store, zeroAlign, misaligned] at success
    · simp only [store, ite_eq_right zeroAlign, ite_eq_right misaligned] at success
      cases checked : checkPtr state pointer bytes.length with
      | ub error => simp [checked] at success
      | noChoice => simp [checked] at success
      | unsupported => simp [checked] at success
      | ok span =>
        cases span with
        | none =>
          simp only [checked] at success
          have same : state = after := Result.ok.inj success
          cases same
          rfl
        | some span =>
          simp only [checked] at success
          have found := checkPtr_some_lookup checked
          have same := Result.ok.inj success
          rw [← same]
          by_cases equal : id = span.id
          · subst id
            simp [liveBit, replace, found]
          · simp [liveBit, replace, equal]

theorem free_liveBit {state after : State} {pointer : Ptr} {kind : Kind}
    {size align id : Nat} (provenance : pointer.provenance = some id)
    (success : free state pointer kind size align = .ok after) (current : Nat) :
    liveBit after current = if current = id then false else liveBit state current := by
  cases found : state.allocations id with
  | none => simp [free, provenance, found] at success
  | some allocation =>
    simp only [free, provenance, found] at success
    split at success
    · cases success
    · split at success
      · cases success
      · split at success
        · cases success
        · split at success
          · cases success
          · split at success
            · cases success
            · have same := Result.ok.inj success
              rw [← same]
              by_cases equal : current = id <;> simp [liveBit, replace, equal]

theorem fresh_round_noLive {state : State} (dead : NoLive state)
    (bytes : List Byte) (small : bytes.length < sizeLimit) :
    ∃ written freed,
      allocateAt state .heap bytes.length 1 1 =
        .ok (pointer state 1, freshState state bytes 1) ∧
      store (freshState state bytes 1) (pointer state 1) bytes 1 = .ok written ∧
      load written (pointer state 1) bytes.length 1 = .ok (bytes, written) ∧
      free written (pointer state 1) .heap bytes.length 1 = .ok freed ∧ NoLive freed := by
  obtain ⟨written, freed, stored, loaded, released⟩ := fresh_round state bytes 1
  refine ⟨written, freed, ?_, stored, loaded, released, ?_⟩
  · have candidate := noLive_candidate_one dead bytes.length small
    simp [allocateAt, Nat.not_le.mpr small, candidate, pointer, freshState, fresh,
      freshAllocation]
  · intro id
    rw [free_liveBit (provenance := rfl) released id]
    by_cases equal : id = state.next
    · simp [equal]
    · rw [ite_eq_right equal, store_liveBit stored id]
      simpa [liveBit, freshState, append, equal] using dead id

theorem one_round_reach {state : State} (dead : NoLive state) (bytes : List Byte)
    (small : bytes.length < sizeLimit) (finish : Plan) (trace : List Event) :
    ∃ freed finalTrace, NoLive freed ∧
      Reach SourceStep (.running state (oneRound bytes finish) trace)
        (.running freed finish finalTrace) := by
  obtain ⟨written, freed, allocated, stored, loaded, released, freedDead⟩ :=
    fresh_round_noLive dead bytes small
  let p := pointer state 1
  let freePlan : Plan := .call (.free p .heap bytes.length 1) (fun _ => finish)
  let loadPlan : Plan := .call (.load p bytes.length 1) (fun _ => freePlan)
  let storePlan : Plan := .call (.store p bytes 1) (fun _ => loadPlan)
  let t1 := trace ++ [.answered (.allocate .heap bytes.length 1) (.pointer p)]
  let t2 := t1 ++ [.answered (.store p bytes 1) .unit]
  let t3 := t2 ++ [.answered (.load p bytes.length 1) (.bytes bytes)]
  let t4 := t3 ++ [.answered (.free p .heap bytes.length 1) .unit]
  have allocationEdge : SourceStep (.running state (oneRound bytes finish) trace)
      (.running (freshState state bytes 1) storePlan t1) := by
    refine ⟨1, ?_⟩
    simp [next, oneRound, sourceExecute, allocated, liftResult, storePlan, loadPlan,
      freePlan, t1, p]
  have storeEdge : SourceStep (.running (freshState state bytes 1) storePlan t1)
      (.running written loadPlan t2) := by
    refine ⟨1, ?_⟩
    simp [next, storePlan, sourceExecute, p, stored, liftResult, t2]
  have loadEdge : SourceStep (.running written loadPlan t2)
      (.running written freePlan t3) := by
    refine ⟨1, ?_⟩
    simp [next, loadPlan, sourceExecute, p, loaded, liftResult, t3]
  have freeEdge : SourceStep (.running written freePlan t3) (.running freed finish t4) := by
    refine ⟨1, ?_⟩
    simp [next, freePlan, sourceExecute, p, released, liftResult, t4]
  exact ⟨freed, t4, freedDead,
    Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.refl _) allocationEdge)
      storeEdge) loadEdge) freeEdge⟩

theorem rounds_reach {state : State} (dead : NoLive state) (bytes : List Byte)
    (small : bytes.length < sizeLimit) (finish : Plan) (n : Nat) (trace : List Event) :
    ∃ final finalTrace, NoLive final ∧
      Reach SourceStep (.running state (rounds bytes finish n) trace)
        (.running final finish finalTrace) := by
  induction n generalizing state trace with
  | zero => exact ⟨state, trace, dead, Reach.refl _⟩
  | succ n ih =>
    obtain ⟨freed, nextTrace, freedDead, first⟩ :=
      one_round_reach dead bytes small (rounds bytes finish n) trace
    obtain ⟨final, finalTrace, finalDead, rest⟩ := ih freedDead nextTrace
    exact ⟨final, finalTrace, finalDead, first.trans rest⟩

theorem sequence_reach {state : State} (dead : NoLive state)
    (blocks : List (List Byte)) (bounded : ∀ bytes ∈ blocks, bytes.length < sizeLimit)
    (finish : Plan) (trace : List Event) :
    ∃ final finalTrace, NoLive final ∧
      Reach SourceStep (.running state (sequenceRounds blocks finish) trace)
        (.running final finish finalTrace) := by
  induction blocks generalizing state trace with
  | nil => exact ⟨state, trace, dead, Reach.refl _⟩
  | cons bytes rest ih =>
    obtain ⟨freed, nextTrace, freedDead, first⟩ :=
      one_round_reach dead bytes (bounded bytes (by simp)) (sequenceRounds rest finish) trace
    have restBounded : ∀ bytes ∈ rest, bytes.length < sizeLimit := by
      intro block member
      exact bounded block (List.mem_cons_of_mem _ member)
    obtain ⟨final, finalTrace, finalDead, remaining⟩ := ih freedDead restBounded nextTrace
    exact ⟨final, finalTrace, finalDead, first.trans remaining⟩

def spinTrace (trace : List Event) : Nat → List Event
  | 0 => trace
  | n + 1 => spinTrace trace n ++ [.spin]

def spinRun (state : State) (trace : List Event) (n : Nat) : Config State :=
  .running state .spin (spinTrace trace n)

theorem spinRun_steps (state : State) (trace : List Event) (n : Nat) :
    SourceStep (spinRun state trace n) (spinRun state trace (n + 1)) := ⟨0, rfl⟩

/-- For every finite repetition count there is an enabled execution from empty
memory to spin, followed by an actual infinite sequence of enabled spin steps. -/
theorem empty_rounds_reach_spin (bytes : List Byte) (small : bytes.length < sizeLimit)
    (n : Nat) : ∃ final trace,
      Reach SourceStep (.running empty (rounds bytes .spin n) []) (spinRun final trace 0) ∧
      (∀ k, SourceStep (spinRun final trace k) (spinRun final trace (k + 1))) := by
  obtain ⟨final, trace, _, path⟩ := rounds_reach empty_noLive bytes small .spin n []
  exact ⟨final, trace, path, spinRun_steps final trace⟩

theorem empty_sequence_reach_spin (blocks : List (List Byte))
    (bounded : ∀ bytes ∈ blocks, bytes.length < sizeLimit) : ∃ final trace,
      Reach SourceStep (.running empty (sequenceRounds blocks .spin) []) (spinRun final trace 0) ∧
      (∀ k, SourceStep (spinRun final trace k) (spinRun final trace (k + 1))) := by
  obtain ⟨final, trace, _, path⟩ := sequence_reach empty_noLive blocks bounded .spin []
  exact ⟨final, trace, path, spinRun_steps final trace⟩

theorem noLive_exit {state : State} (dead : NoLive state) :
    exit state = .machineStop := by
  unfold MiniRustReference.exit
  split
  · rename_i leaking
    obtain ⟨id, _, hit⟩ := List.any_eq_true.mp leaking
    cases found : state.allocations id with
    | none => simp [found] at hit
    | some allocation =>
      have notLive : allocation.live = false := by simpa [liveBit, found] using dead id
      simp [found, notLive] at hit
  · rfl

/-- A leak-free terminating witness, without asserting universal termination. -/
theorem empty_sequence_reach_exit (blocks : List (List Byte))
    (bounded : ∀ bytes ∈ blocks, bytes.length < sizeLimit) : ∃ final trace,
      Reach SourceStep (.running empty (sequenceRounds blocks exitPlan) [])
        (.terminated final .machineStop (trace ++ [.exited .machineStop])) := by
  obtain ⟨final, trace, dead, path⟩ := sequence_reach empty_noLive blocks bounded exitPlan []
  have finish : SourceStep (.running final exitPlan trace)
      (.terminated final .machineStop (trace ++ [.exited .machineStop])) := by
    refine ⟨0, ?_⟩
    simp [next, exitPlan, sourceExecute, noLive_exit dead]
  exact ⟨final, trace, Reach.tail path finish⟩

#print axioms noLive_candidate_one
#print axioms store_liveBit
#print axioms free_liveBit
#print axioms fresh_round_noLive
#print axioms one_round_reach
#print axioms rounds_reach
#print axioms sequence_reach
#print axioms spinRun_steps
#print axioms empty_rounds_reach_spin
#print axioms empty_sequence_reach_spin
#print axioms noLive_exit
#print axioms empty_sequence_reach_exit

end AnnealResearch.MemoryWitnesses
