import AnnealResearch.DeadData
import AnnealResearch.MemoryExecution

/-!
Relational finite-prefix correspondence for the existing MemoryExecution client
language. The reference/factored kernels and the existing shared Plan/next
controller are reused. The changed target normalizes explicitly dead cells after
successful memory primitives. Its result categories, replies, and allocator
candidates are unchanged.

This relation deliberately permits different dead contents; it is not an exact
mapCfg equation. Every field present in the existing configuration syntax is
related. In particular, bad/unsupported configurations retain memory (and a UB
diagnostic for bad), but that syntax has no trace field. Preceding successful
trace prefixes are covered; no complete failure-event log is claimed.

There are no StateWF or access-success premises. These are finite-prefix/NoUB
theorems for this API, not progress, termination, infinite-observation, Rust
contextual-equivalence, or physical storage theorems.
-/

namespace AnnealResearch.DeadDataExecution

open Execution PrefixTransfer MemoryExecution

abbrev Memory := MiniRustFactored.State

def execute (candidate : Nat) (memory : Memory) : Op → EvalAnswer Memory
  | .allocate kind size align =>
      liftResult (fun value => (.pointer value.1, value.2))
        (DeadData.allocateAt memory kind size align candidate)
  | .load pointer length align =>
      liftResult (fun value => (.bytes value.1, value.2))
        (DeadData.load memory pointer length align)
  | .store pointer bytes align =>
      liftResult (fun nextMemory => (.unit, nextMemory))
        (DeadData.store memory pointer bytes align)
  | .free pointer kind size align =>
      liftResult (fun nextMemory => (.unit, nextMemory))
        (DeadData.free memory pointer kind size align)
  | .deref pointer length =>
      liftResult (fun _ => (.unit, DeadData.normalize memory))
        (MiniRustFactored.dereferenceable memory pointer length)
  | .exit => .exit (MiniRustFactored.exit memory)

inductive AnswerRel : EvalAnswer Memory → EvalAnswer Memory → Prop where
  | good {first second : Memory} (reply : Reply) (same : DeadData.Same first second) :
      AnswerRel (.good reply first) (.good reply second)
  | ub (diagnostic : MiniRustReference.UB) : AnswerRel (.ub diagnostic) (.ub diagnostic)
  | unsupported : AnswerRel .unsupported .unsupported
  | noChoice : AnswerRel .noChoice .noChoice
  | exit (result : MiniRustReference.ExitResult) : AnswerRel (.exit result) (.exit result)

theorem lift_related {A B : Type} {values : A → B → Prop}
    (firstValue : A → Reply × Memory) (secondValue : B → Reply × Memory)
    (compatible : ∀ first second, values first second →
      (firstValue first).1 = (secondValue second).1 ∧
      DeadData.Same (firstValue first).2 (secondValue second).2)
    {first : MiniRustReference.Result A} {second : MiniRustReference.Result B}
    (related : DeadData.ResultRel values first second) :
    AnswerRel (liftResult firstValue first) (liftResult secondValue second) := by
  cases related with
  | ok related =>
    obtain ⟨replyEq, memoryRel⟩ := compatible _ _ related
    simp only [liftResult]
    rw [replyEq]
    exact AnswerRel.good _ memoryRel
  | ub diagnostic => exact AnswerRel.ub diagnostic
  | unsupported => exact AnswerRel.unsupported
  | noChoice => exact AnswerRel.noChoice

/-- The same candidate is matched in both directions, for every Nat candidate.
In particular noChoice is preserved rather than replaced by an error edge. -/
theorem execute_related {first second : Memory} (same : DeadData.Same first second)
    (candidate : Nat) (op : Op) :
    AnswerRel (targetExecute candidate first op) (execute candidate second op) := by
  cases op with
  | allocate kind size align =>
    exact lift_related (values := DeadData.PointerAndState)
      (fun value => (.pointer value.1, value.2))
      (fun value => (.pointer value.1, value.2))
      (fun _ _ related => ⟨congrArg Reply.pointer related.1, related.2⟩)
      (DeadData.allocateAt_agreement same kind size align candidate)
  | load pointer length align =>
    exact lift_related (values := DeadData.BytesAndState)
      (fun value => (.bytes value.1, value.2))
      (fun value => (.bytes value.1, value.2))
      (fun _ _ related => ⟨congrArg Reply.bytes related.1, related.2⟩)
      (DeadData.load_agreement same pointer length align)
  | store pointer bytes align =>
    exact lift_related (values := DeadData.Same)
      (fun memory => (.unit, memory)) (fun memory => (.unit, memory))
      (fun _ _ related => ⟨rfl, related⟩)
      (DeadData.store_agreement same pointer bytes align)
  | free pointer kind size align =>
    exact lift_related (values := DeadData.Same)
      (fun memory => (.unit, memory)) (fun memory => (.unit, memory))
      (fun _ _ related => ⟨rfl, related⟩)
      (DeadData.free_agreement same pointer kind size align)
  | deref pointer length =>
    simp only [targetExecute, execute]
    rw [DeadData.dereferenceable_same same pointer length]
    cases MiniRustFactored.dereferenceable second pointer length with
    | ok value => exact AnswerRel.good .unit (same.trans (DeadData.normalize_same second))
    | ub diagnostic => exact AnswerRel.ub diagnostic
    | unsupported => exact AnswerRel.unsupported
    | noChoice => exact AnswerRel.noChoice
  | exit =>
    simp only [targetExecute, execute]
    rw [DeadData.exit_same same]
    exact AnswerRel.exit _

inductive ConfigRel : Config Memory → Config Memory → Prop where
  | running {first second : Memory} (same : DeadData.Same first second)
      (plan : Plan) (trace : List Event) :
      ConfigRel (.running first plan trace) (.running second plan trace)
  | bad {first second : Memory} (same : DeadData.Same first second)
      (diagnostic : MiniRustReference.UB) :
      ConfigRel (.bad first diagnostic) (.bad second diagnostic)
  | unsupported {first second : Memory} (same : DeadData.Same first second) :
      ConfigRel (.unsupported first) (.unsupported second)
  | completed {first second : Memory} (same : DeadData.Same first second) (trace : List Event) :
      ConfigRel (.completed first trace) (.completed second trace)
  | terminated {first second : Memory} (same : DeadData.Same first second)
      (result : MiniRustReference.ExitResult) (trace : List Event) :
      ConfigRel (.terminated first result trace) (.terminated second result trace)

theorem bad_iff {first second : Config Memory} (related : ConfigRel first second) :
    Bad first ↔ Bad second := by cases related <;> rfl

/-- The observation preserves status, available traces, the UB diagnostic, and
the exit result. ConfigRel preserves the running Plan separately. -/
inductive Observation where
  | running (trace : List Event)
  | bad (diagnostic : MiniRustReference.UB)
  | unsupported
  | completed (trace : List Event)
  | terminated (result : MiniRustReference.ExitResult) (trace : List Event)

def observe : Config Memory → Observation
  | .running _ _ trace => .running trace
  | .bad _ diagnostic => .bad diagnostic
  | .unsupported _ => .unsupported
  | .completed _ trace => .completed trace
  | .terminated _ result trace => .terminated result trace

theorem observations_equal {first second : Config Memory} (related : ConfigRel first second) :
    observe first = observe second := by cases related <;> rfl

inductive OptionRel {A B : Type} (related : A → B → Prop) : Option A → Option B → Prop where
  | none : OptionRel related Option.none Option.none
  | some {first second} (same : related first second) :
      OptionRel related (Option.some first) (Option.some second)

/-- A nondependent presentation of the existing next call branch, used only
to state the answer lemma without elaborating a match on its proof argument. -/
def afterCall (memory : Memory) (op : Op) (continuation : Reply → Plan)
    (trace : List Event) : EvalAnswer Memory → Option (Config Memory)
  | .good reply nextMemory =>
      Option.some (.running nextMemory (continuation reply) (trace ++ [.answered op reply]))
  | .ub diagnostic => Option.some (.bad memory diagnostic)
  | .unsupported => Option.some (.unsupported memory)
  | .noChoice => Option.none
  | .exit result => Option.some (.terminated memory result (trace ++ [.exited result]))

theorem call_related {first second : Memory} (same : DeadData.Same first second)
    (op : Op) (continuation : Reply → Plan) (trace : List Event)
    {firstAnswer secondAnswer : EvalAnswer Memory} (answers : AnswerRel firstAnswer secondAnswer) :
    OptionRel ConfigRel
      (afterCall first op continuation trace firstAnswer)
      (afterCall second op continuation trace secondAnswer) := by
  cases answers with
  | good reply nextSame => exact OptionRel.some (ConfigRel.running nextSame _ _)
  | ub diagnostic => exact OptionRel.some (ConfigRel.bad same diagnostic)
  | unsupported => exact OptionRel.some (ConfigRel.unsupported same)
  | noChoice => exact OptionRel.none
  | exit result => exact OptionRel.some (ConfigRel.terminated same result _)

theorem next_related {first second : Config Memory} (related : ConfigRel first second)
    (candidate : Nat) :
    OptionRel ConfigRel (next targetExecute candidate first) (next execute candidate second) := by
  cases related with
  | @running firstMemory secondMemory same plan trace =>
    cases plan with
    | done => exact OptionRel.some (ConfigRel.completed same trace)
    | spin => exact OptionRel.some (ConfigRel.running same .spin _)
    | call op continuation =>
      cases firstAnswer : targetExecute candidate firstMemory op <;>
        cases secondAnswer : execute candidate secondMemory op
      all_goals
        have answers := execute_related same candidate op
        simp only [firstAnswer, secondAnswer] at answers
        cases answers
      all_goals
        simp only [next, firstAnswer, secondAnswer]
        first
        | exact OptionRel.none
        | exact OptionRel.some (ConfigRel.running (by assumption) _ _)
        | exact OptionRel.some (ConfigRel.bad same _)
        | exact OptionRel.some (ConfigRel.unsupported same)
        | exact OptionRel.some (ConfigRel.terminated same _ _)
  | bad same diagnostic => exact OptionRel.none
  | unsupported same => exact OptionRel.none
  | completed same trace => exact OptionRel.none
  | terminated same result trace => exact OptionRel.none

theorem OptionRel.lift_left {A B : Type} {relation : A → B → Prop}
    {first : Option A} {second : Option B} (related : OptionRel relation first second)
    {successor : A} (edge : first = Option.some successor) :
    ∃ other, second = Option.some other ∧ relation successor other := by
  cases related with
  | none => cases edge
  | some same =>
    cases edge
    exact ⟨_, rfl, same⟩

theorem OptionRel.lift_right {A B : Type} {relation : A → B → Prop}
    {first : Option A} {second : Option B} (related : OptionRel relation first second)
    {successor : B} (edge : second = Option.some successor) :
    ∃ other, first = Option.some other ∧ relation other successor := by
  cases related with
  | none => cases edge
  | some same =>
    cases edge
    exact ⟨_, rfl, same⟩

abbrev ErasingStep := Step execute

theorem forward_step {first successor second : Config Memory}
    (related : ConfigRel first second) (edge : TargetStep first successor) :
    ∃ other, ErasingStep second other ∧ ConfigRel successor other := by
  obtain ⟨candidate, edge⟩ := edge
  obtain ⟨other, otherEdge, otherRel⟩ := (next_related related candidate).lift_left edge
  exact ⟨other, ⟨candidate, otherEdge⟩, otherRel⟩

theorem backward_step {first second successor : Config Memory}
    (related : ConfigRel first second) (edge : ErasingStep second successor) :
    ∃ other, TargetStep first other ∧ ConfigRel other successor := by
  obtain ⟨candidate, edge⟩ := edge
  obtain ⟨other, otherEdge, otherRel⟩ := (next_related related candidate).lift_right edge
  exact ⟨other, ⟨candidate, otherEdge⟩, otherRel⟩

theorem forward_simulation :
    StutteringSimulation TargetStep ErasingStep Bad Bad ConfigRel := by
  constructor
  · intro first successor second related edge
    obtain ⟨other, otherEdge, otherRel⟩ := forward_step related edge
    exact ⟨other, Reach.tail (Reach.refl _) otherEdge, otherRel⟩
  · intro first second related bad
    exact (bad_iff related).mp bad

theorem backward_simulation :
    StutteringSimulation ErasingStep TargetStep Bad Bad (fun second first => ConfigRel first second) := by
  constructor
  · intro second successor first related edge
    obtain ⟨other, otherEdge, otherRel⟩ := backward_step related edge
    exact ⟨other, Reach.tail (Reach.refl _) otherEdge, otherRel⟩
  · intro second first related bad
    exact (bad_iff related).mpr bad

theorem forward_prefix {first second : Config Memory} (related : ConfigRel first second)
    {successor : Config Memory} (path : Reach TargetStep first successor) :
    ∃ other, Reach ErasingStep second other ∧ ConfigRel successor other :=
  reachable_coverage forward_simulation related path

theorem backward_prefix {first second : Config Memory} (related : ConfigRel first second)
    {successor : Config Memory} (path : Reach ErasingStep second successor) :
    ∃ other, Reach TargetStep first other ∧ ConfigRel other successor :=
  reachable_coverage backward_simulation related path

theorem noUB_iff {first second : Config Memory} (related : ConfigRel first second) :
    NoUB TargetStep Bad first ↔ NoUB ErasingStep Bad second := by
  constructor
  · exact sourceSafety backward_simulation related
  · exact sourceSafety forward_simulation related

/-- An existential factored witness bridges the reference representation.
Absent-cell data need not be equal or recoverable by encode/reify. -/
def ReferenceRel (source : Config MiniRustReference.State) (target : Config Memory) : Prop :=
  ∃ factored, source = mapCfg MiniRustFactored.reify factored ∧ ConfigRel factored target

theorem reference_bad_iff {source : Config MiniRustReference.State} {target : Config Memory}
    (related : ReferenceRel source target) : Bad source ↔ Bad target := by
  obtain ⟨factored, rfl, same⟩ := related
  exact (bad_map MiniRustFactored.reify factored).trans (bad_iff same)

/-- Every finite reference prefix, including a bad boundary, has a related
erasing-target prefix. This quantifies over every wrapper continuation. -/
theorem reference_forward_prefix {source : Config MiniRustReference.State} {target : Config Memory}
    (related : ReferenceRel source target) {successor : Config MiniRustReference.State}
    (path : Reach SourceStep source successor) :
    ∃ other, Reach ErasingStep target other ∧ ReferenceRel successor other := by
  obtain ⟨factored, rfl, same⟩ := related
  obtain ⟨factoredAfter, factoredPath, exactEnd⟩ := (memory_prefix_iff factored successor).mp path
  obtain ⟨other, otherPath, otherRel⟩ := forward_prefix same factoredPath
  exact ⟨other, otherPath, factoredAfter, exactEnd.symm, otherRel⟩

/-- The reverse coverage prevents erasure from introducing extra API prefixes.
The claim is relational coverage, not equality of full memory records. -/
theorem reference_backward_prefix {source : Config MiniRustReference.State} {target : Config Memory}
    (related : ReferenceRel source target) {successor : Config Memory}
    (path : Reach ErasingStep target successor) :
    ∃ other, Reach SourceStep source other ∧ ReferenceRel other successor := by
  obtain ⟨factored, rfl, same⟩ := related
  obtain ⟨factoredAfter, factoredPath, otherRel⟩ := backward_prefix same path
  refine ⟨mapCfg MiniRustFactored.reify factoredAfter, ?_, factoredAfter, rfl, otherRel⟩
  exact map_reach MiniRustFactored.reify sourceExecute targetExecute execute_reify factoredPath

theorem reference_noUB_iff {source : Config MiniRustReference.State} {target : Config Memory}
    (related : ReferenceRel source target) :
    NoUB SourceStep Bad source ↔ NoUB ErasingStep Bad target := by
  obtain ⟨factored, rfl, same⟩ := related
  exact (memory_noUB_iff factored).trans (noUB_iff same)

theorem normalize_config_related (config : Config Memory) :
    ConfigRel config (mapCfg DeadData.normalize config) := by
  cases config with
  | running memory plan trace => exact ConfigRel.running (DeadData.normalize_same memory) plan trace
  | bad memory diagnostic => exact ConfigRel.bad (DeadData.normalize_same memory) diagnostic
  | unsupported memory => exact ConfigRel.unsupported (DeadData.normalize_same memory)
  | completed memory trace => exact ConfigRel.completed (DeadData.normalize_same memory) trace
  | terminated memory result trace => exact ConfigRel.terminated (DeadData.normalize_same memory) result trace

theorem encoded_normalized_related (source : Config MiniRustReference.State) :
    ReferenceRel source (mapCfg DeadData.normalize (mapCfg MiniRustFactored.encode source)) :=
  ⟨mapCfg MiniRustFactored.encode source, (reify_encode_config source).symm,
    normalize_config_related _⟩

/-- Every reference configuration has a normalized related initial target.
No structural admission or prior safety of that source is assumed. -/
theorem encoded_normalized_noUB_iff (source : Config MiniRustReference.State) :
    NoUB SourceStep Bad source ↔
      NoUB ErasingStep Bad (mapCfg DeadData.normalize (mapCfg MiniRustFactored.encode source)) :=
  reference_noUB_iff (encoded_normalized_related source)

#print axioms execute_related
#print axioms observations_equal
#print axioms next_related
#print axioms forward_simulation
#print axioms backward_simulation
#print axioms forward_prefix
#print axioms backward_prefix
#print axioms noUB_iff
#print axioms reference_forward_prefix
#print axioms reference_backward_prefix
#print axioms reference_noUB_iff
#print axioms encoded_normalized_noUB_iff

end AnnealResearch.DeadDataExecution
