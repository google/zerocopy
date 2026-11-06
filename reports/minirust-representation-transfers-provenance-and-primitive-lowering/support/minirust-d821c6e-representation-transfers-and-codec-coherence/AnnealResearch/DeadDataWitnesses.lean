import AnnealResearch.DeadDataExecution
import AnnealResearch.MemoryWitnesses

/-!
Concrete client-family instantiations of the coarser dead-data bridge. The old
MemoryExamples safety proofs and MemoryWitnesses enabled paths are reused,
rather than reproving their allocation/store/load/free protocol. Every finite
sequence of bounded plain raw-byte blocks belongs to the selected family;
Uninit here remains an allowed raw payload, not a successful typed-load claim.

The target spin suffix below is an actual selected infinite sequence of enabled
steps after a reachable boundary. It establishes neither fairness nor universal
progress/termination, and is not an infinite-observation equivalence theorem.
The existing wrapper has no trace field on bad/unsupported configurations; these
witnesses do not strengthen that syntax into a complete failure-event log.
No Rust frontend, destructor, permission-model, or physical-space claim is made.
-/

namespace AnnealResearch.DeadDataWitnesses

open Execution MemoryExecution MemoryExamples DeadDataExecution

abbrev PlainBlocks := List (List (Option (Fin 256)))

def start (blocks : PlainBlocks) (finish : Plan) : Config MiniRustFactored.State :=
  mapCfg DeadData.normalize (mapCfg MiniRustFactored.encode
    (.running MiniRustReference.empty (sequenceRounds (blocks.map plainBytes) finish) []))

private theorem mapped_bounded (blocks : PlainBlocks)
    (bounded : ∀ bytes, bytes ∈ blocks → (plainBytes bytes).length < MiniRustReference.sizeLimit) :
    ∀ bytes ∈ blocks.map plainBytes, bytes.length < MiniRustReference.sizeLimit := by
  intro bytes member
  obtain ⟨original, belongs, rfl⟩ := List.mem_map.mp member
  exact bounded original belongs

/-- Universal safety is inherited from the old arbitrary-block client proof.
Its allocator quantifier still covers every candidate, not the witness's choice. -/
theorem plain_sequence_safe (blocks : PlainBlocks)
    (bounded : ∀ bytes, bytes ∈ blocks → (plainBytes bytes).length < MiniRustReference.sizeLimit)
    (finish : Plan)
    (safeFinish : ∀ memory trace, NoUB SourceStep Bad (.running memory finish trace)) :
    NoUB ErasingStep Bad (start blocks finish) := by
  have sourceSafe := (sequence_plain_blocks_safe blocks bounded finish safeFinish).1
  exact (encoded_normalized_noUB_iff _).mp sourceSafe

private theorem running_shape {sourceMemory : MiniRustReference.State} {plan : Plan}
    {trace : List Event} {target : Config MiniRustFactored.State}
    (related : ReferenceRel (.running sourceMemory plan trace) target) :
    ∃ targetMemory, target = .running targetMemory plan trace := by
  obtain ⟨factored, exactState, related⟩ := related
  cases related with
  | @running first second same currentPlan currentTrace =>
    have fields : sourceMemory = MiniRustFactored.reify first ∧
        plan = currentPlan ∧ trace = currentTrace := by
      simpa only [mapCfg, Config.running.injEq] using exactState
    obtain ⟨_, planEq, traceEq⟩ := fields
    subst currentPlan
    subst currentTrace
    exact ⟨second, rfl⟩
  | bad same diagnostic => simp only [mapCfg] at exactState; cases exactState
  | unsupported same => simp only [mapCfg] at exactState; cases exactState
  | completed same currentTrace => simp only [mapCfg] at exactState; cases exactState
  | terminated same result currentTrace => simp only [mapCfg] at exactState; cases exactState

private theorem terminated_shape {sourceMemory : MiniRustReference.State}
    {result : MiniRustReference.ExitResult} {trace : List Event}
    {target : Config MiniRustFactored.State}
    (related : ReferenceRel (.terminated sourceMemory result trace) target) :
    ∃ targetMemory, target = .terminated targetMemory result trace := by
  obtain ⟨factored, exactState, related⟩ := related
  cases related with
  | running same currentPlan currentTrace => simp only [mapCfg] at exactState; cases exactState
  | bad same diagnostic => simp only [mapCfg] at exactState; cases exactState
  | unsupported same => simp only [mapCfg] at exactState; cases exactState
  | completed same currentTrace => simp only [mapCfg] at exactState; cases exactState
  | @terminated first second same currentResult currentTrace =>
    have fields : sourceMemory = MiniRustFactored.reify first ∧
        result = currentResult ∧ trace = currentTrace := by
      simpa only [mapCfg, Config.terminated.injEq] using exactState
    obtain ⟨_, resultEq, traceEq⟩ := fields
    subst currentResult
    subst currentTrace
    exact ⟨second, rfl⟩

def spinRun (memory : MiniRustFactored.State) (trace : List Event) (n : Nat) :
    Config MiniRustFactored.State :=
  .running memory .spin (MemoryWitnesses.spinTrace trace n)

/-- The existing wrapper's spin controller supplies an actual target edge;
normalization does not alter the selected memory during these spin steps. -/
theorem spinRun_steps (memory : MiniRustFactored.State) (trace : List Event) (n : Nat) :
    ErasingStep (spinRun memory trace n) (spinRun memory trace (n + 1)) := ⟨0, rfl⟩

/-- Nonvacuous safety and an enabled path for an arbitrary finite list of plain
blocks, followed by an actual target spin suffix. The source path is reused. -/
theorem plain_sequence_reach_spin (blocks : PlainBlocks)
    (bounded : ∀ bytes, bytes ∈ blocks → (plainBytes bytes).length < MiniRustReference.sizeLimit) :
    NoUB ErasingStep Bad (start blocks .spin) ∧
    ∃ sourceMemory targetMemory trace,
      Reach SourceStep
        (.running MiniRustReference.empty (sequenceRounds (blocks.map plainBytes) .spin) [])
        (MemoryWitnesses.spinRun sourceMemory trace 0) ∧
      Reach ErasingStep (start blocks .spin) (spinRun targetMemory trace 0) ∧
      ReferenceRel (MemoryWitnesses.spinRun sourceMemory trace 0) (spinRun targetMemory trace 0) ∧
      (∀ n, ErasingStep (spinRun targetMemory trace n) (spinRun targetMemory trace (n + 1))) := by
  refine ⟨plain_sequence_safe blocks bounded .spin spin_safe, ?_⟩
  obtain ⟨sourceMemory, trace, sourcePath, _⟩ :=
    MemoryWitnesses.empty_sequence_reach_spin (blocks.map plainBytes) (mapped_bounded blocks bounded)
  obtain ⟨target, targetPath, related⟩ := reference_forward_prefix
    (encoded_normalized_related
      (.running MiniRustReference.empty (sequenceRounds (blocks.map plainBytes) .spin) [])) sourcePath
  obtain ⟨targetMemory, sameTarget⟩ := running_shape related
  subst target
  exact ⟨sourceMemory, targetMemory, trace, sourcePath, targetPath, related,
    spinRun_steps targetMemory trace⟩

/-- A separate enabled clean-exit witness, with the same machineStop tag and
trace, together with universal NoUB. This is not universal termination. -/
theorem plain_sequence_reach_exit (blocks : PlainBlocks)
    (bounded : ∀ bytes, bytes ∈ blocks → (plainBytes bytes).length < MiniRustReference.sizeLimit) :
    NoUB ErasingStep Bad (start blocks exitPlan) ∧
    ∃ sourceMemory targetMemory trace,
      Reach SourceStep
        (.running MiniRustReference.empty (sequenceRounds (blocks.map plainBytes) exitPlan) [])
        (.terminated sourceMemory .machineStop (trace ++ [.exited .machineStop])) ∧
      Reach ErasingStep (start blocks exitPlan)
        (.terminated targetMemory .machineStop (trace ++ [.exited .machineStop])) ∧
      ReferenceRel (.terminated sourceMemory .machineStop (trace ++ [.exited .machineStop]))
        (.terminated targetMemory .machineStop (trace ++ [.exited .machineStop])) := by
  refine ⟨plain_sequence_safe blocks bounded exitPlan exit_safe, ?_⟩
  obtain ⟨sourceMemory, trace, sourcePath⟩ :=
    MemoryWitnesses.empty_sequence_reach_exit (blocks.map plainBytes) (mapped_bounded blocks bounded)
  obtain ⟨target, targetPath, related⟩ := reference_forward_prefix
    (encoded_normalized_related
      (.running MiniRustReference.empty (sequenceRounds (blocks.map plainBytes) exitPlan) [])) sourcePath
  obtain ⟨targetMemory, sameTarget⟩ := terminated_shape related
  subst target
  exact ⟨sourceMemory, targetMemory, trace, sourcePath, targetPath, related⟩

#print axioms plain_sequence_safe
#print axioms spinRun_steps
#print axioms plain_sequence_reach_spin
#print axioms plain_sequence_reach_exit

end AnnealResearch.DeadDataWitnesses
