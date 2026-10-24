import AnnealResearch.MiniRustFactored
import AnnealResearch.PrefixTransfer

/-!
Whole finite-prefix correspondence for an intentional memory-API client language.
This Plan is shared control syntax, not the literal MiniRust AST or Machine. Its
primitives invoke the independently written reference and factored kernels.
The pinned-source transcription/binding remains audited English; no Rust or
complete MiniRust frontend adequacy is claimed. Natural allocator candidates
are quantified at every transition, never replaced by one selected address.
-/
namespace AnnealResearch.MemoryExecution

open Execution PrefixTransfer

inductive Op where
  | allocate (kind : MiniRustReference.Kind) (size align : Nat)
  | load (p : MiniRustReference.Ptr) (len align : Nat)
  | store (p : MiniRustReference.Ptr) (bytes : List MiniRustReference.Byte) (align : Nat)
  | free (p : MiniRustReference.Ptr) (kind : MiniRustReference.Kind) (size align : Nat)
  | deref (p : MiniRustReference.Ptr) (len : Nat)
  | exit
  deriving DecidableEq, Repr
inductive Reply where
  | pointer (p : MiniRustReference.Ptr) | bytes (bytes : List MiniRustReference.Byte) | unit
  deriving DecidableEq, Repr
inductive Plan where
  | done | spin | call (op : Op) (continuation : Reply → Plan)
inductive Event where
  | answered (op : Op) (reply : Reply) | exited (result : MiniRustReference.ExitResult) | spin
  deriving DecidableEq, Repr

inductive EvalAnswer (S : Type) where
  | good (reply : Reply) (memory : S)
  | ub (diagnostic : MiniRustReference.UB)
  | unsupported | noChoice
  | exit (result : MiniRustReference.ExitResult)
def mapAnswer {S T : Type} (f : S → T) : EvalAnswer S → EvalAnswer T
  | .good reply memory => .good reply (f memory)
  | .ub diagnostic => .ub diagnostic
  | .unsupported => .unsupported | .noChoice => .noChoice | .exit result => .exit result
def liftResult {A S : Type} (value : A → Reply × S) : MiniRustReference.Result A → EvalAnswer S
  | .ok a => .good (value a).1 (value a).2
  | .ub diagnostic => .ub diagnostic | .unsupported => .unsupported | .noChoice => .noChoice

/-- One candidate of the reference allocator; all candidates enter Step below. -/
def sourceExecute (candidate : Nat) (memory : MiniRustReference.State) : Op → EvalAnswer MiniRustReference.State
  | .allocate kind size align =>
      liftResult (fun value => (.pointer value.1, value.2))
        (MiniRustReference.allocateAt memory kind size align candidate)
  | .load p len align => liftResult (fun value => (.bytes value.1, value.2)) (MiniRustReference.load memory p len align)
  | .store p bytes align => liftResult (fun next => (.unit, next)) (MiniRustReference.store memory p bytes align)
  | .free p kind size align => liftResult (fun next => (.unit, next)) (MiniRustReference.free memory p kind size align)
  | .deref p len => liftResult (fun _ => (.unit, memory)) (MiniRustReference.dereferenceable memory p len)
  | .exit => .exit (MiniRustReference.exit memory)

/-- Independent target dispatch to the factored implementations. -/
def targetExecute (candidate : Nat) (memory : MiniRustFactored.State) : Op → EvalAnswer MiniRustFactored.State
  | .allocate kind size align =>
      liftResult (fun value => (.pointer value.1, value.2))
        (MiniRustFactored.allocateAt memory kind size align candidate)
  | .load p len align => liftResult (fun value => (.bytes value.1, value.2)) (MiniRustFactored.load memory p len align)
  | .store p bytes align => liftResult (fun next => (.unit, next)) (MiniRustFactored.store memory p bytes align)
  | .free p kind size align => liftResult (fun next => (.unit, next)) (MiniRustFactored.free memory p kind size align)
  | .deref p len => liftResult (fun _ => (.unit, memory)) (MiniRustFactored.dereferenceable memory p len)
  | .exit => .exit (MiniRustFactored.exit memory)

theorem execute_reify (candidate : Nat) (memory : MiniRustFactored.State) (op : Op) :
    sourceExecute candidate (MiniRustFactored.reify memory) op =
      mapAnswer MiniRustFactored.reify (targetExecute candidate memory op) := by
  cases op with
  | allocate kind size align =>
    simp only [sourceExecute, targetExecute]
    rw [MiniRustFactored.allocateAt_reify]
    cases MiniRustFactored.allocateAt memory kind size align candidate <;> rfl
  | load p len align =>
    simp only [sourceExecute, targetExecute]
    rw [MiniRustFactored.load_reify]
    cases MiniRustFactored.load memory p len align <;> rfl
  | store p bytes align =>
    simp only [sourceExecute, targetExecute]
    rw [MiniRustFactored.store_reify]
    cases MiniRustFactored.store memory p bytes align <;> rfl
  | free p kind size align =>
    simp only [sourceExecute, targetExecute]
    rw [MiniRustFactored.free_reify]
    cases MiniRustFactored.free memory p kind size align <;> rfl
  | deref p len =>
    simp only [sourceExecute, targetExecute]
    rw [MiniRustFactored.dereferenceable_reify]
    cases MiniRustFactored.dereferenceable memory p len <;> rfl
  | exit => exact congrArg EvalAnswer.exit (MiniRustFactored.exit_reify memory)

inductive Config (S : Type) where
  | running (memory : S) (plan : Plan) (trace : List Event)
  | bad (memory : S) (diagnostic : MiniRustReference.UB)
  | unsupported (memory : S)
  | completed (memory : S) (trace : List Event)
  | terminated (memory : S) (result : MiniRustReference.ExitResult) (trace : List Event)
def mapCfg {S T : Type} (f : S → T) : Config S → Config T
  | .running memory plan trace => .running (f memory) plan trace
  | .bad memory diagnostic => .bad (f memory) diagnostic
  | .unsupported memory => .unsupported (f memory)
  | .completed memory trace => .completed (f memory) trace
  | .terminated memory result trace => .terminated (f memory) result trace
def Bad {S : Type} : Config S → Prop
  | .bad _ _ => True | _ => False

/-- Candidate-specific successor. noChoice contributes no successor. UB,
unsupported, source Exit, and normal Plan completion remain distinct outcomes.
Error states are terminal: a later continuation cannot erase a bad prefix. -/
def next {S : Type} (eval : Nat → S → Op → EvalAnswer S)
    (candidate : Nat) : Config S → Option (Config S)
  | .running memory (.call op continuation) trace =>
    match eval candidate memory op with
    | .good reply nextMemory =>
        some (.running nextMemory (continuation reply) (trace ++ [.answered op reply]))
    | .ub diagnostic => some (.bad memory diagnostic)
    | .unsupported => some (.unsupported memory)
    | .noChoice => none
    | .exit result => some (.terminated memory result (trace ++ [.exited result]))
  | .running memory .done trace => some (.completed memory trace)
  | .running memory .spin trace => some (.running memory .spin (trace ++ [.spin]))
  | .bad _ _ | .unsupported _ | .completed _ _ | .terminated _ _ _ => none

/-- Every Nat allocator candidate is available, including candidates that
produce UB before candidate checking. No noChoice error/stop edge is added. -/
def Step {S : Type} (eval : Nat → S → Op → EvalAnswer S) (a b : Config S) : Prop :=
  ∃ candidate : Nat, next eval candidate a = some b

section GenericCorrespondence
variable {S T : Type} (f : T → S)
variable (sourceEval : Nat → S → Op → EvalAnswer S) (targetEval : Nat → T → Op → EvalAnswer T)
variable (commutes : ∀ candidate memory op,
  sourceEval candidate (f memory) op = mapAnswer f (targetEval candidate memory op))
include commutes

theorem next_commutes (candidate : Nat) (t : Config T) :
    next sourceEval candidate (mapCfg f t) = (next targetEval candidate t).map (mapCfg f) := by
  cases t with
  | running memory plan trace =>
    cases plan with
    | done => rfl
    | spin => rfl
    | call op continuation =>
      simp only [mapCfg, next, commutes]
      cases targetEval candidate memory op <;> rfl
  | bad memory diagnostic => rfl
  | unsupported memory => rfl
  | completed memory trace => rfl
  | terminated memory result trace => rfl

theorem map_step {t t' : Config T} (edge : Step targetEval t t') :
    Step sourceEval (mapCfg f t) (mapCfg f t') := by
  obtain ⟨candidate, successor⟩ := edge
  refine ⟨candidate, ?_⟩
  rw [next_commutes f sourceEval targetEval commutes, successor]
  rfl

theorem lift_step {t : Config T} {s' : Config S}
    (edge : Step sourceEval (mapCfg f t) s') :
    ∃ t', Step targetEval t t' ∧ mapCfg f t' = s' := by
  obtain ⟨candidate, successor⟩ := edge
  rw [next_commutes f sourceEval targetEval commutes] at successor
  cases targetSuccessor : next targetEval candidate t with
  | none => simp [targetSuccessor] at successor
  | some t' =>
    have same : mapCfg f t' = s' := by
      simpa only [targetSuccessor, Option.map_some, Option.some.injEq] using successor
    exact ⟨t', ⟨candidate, targetSuccessor⟩, same⟩

omit commutes in
theorem bad_map (t : Config T) : Bad (mapCfg f t) ↔ Bad t := by
  cases t <;> rfl

theorem source_simulation :
    StutteringSimulation (Step sourceEval) (Step targetEval) Bad Bad
      (fun s t => s = mapCfg f t) := by
  constructor
  · intro s s' t related edge
    subst s
    obtain ⟨t', targetEdge, same⟩ := lift_step f sourceEval targetEval commutes edge
    exact ⟨t', Reach.tail (Reach.refl _) targetEdge, same.symm⟩
  · intro s t related bad
    subst s
    exact (bad_map f t).mp bad

theorem target_simulation :
    StutteringSimulation (Step targetEval) (Step sourceEval) Bad Bad
      (fun t s => s = mapCfg f t) := by
  constructor
  · intro t t' s related edge
    subst s
    exact ⟨mapCfg f t', Reach.tail (Reach.refl _)
      (map_step f sourceEval targetEval commutes edge), rfl⟩
  · intro t s related bad
    subst s
    exact (bad_map f t).mpr bad

theorem map_reach {t t' : Config T} (path : Reach (Step targetEval) t t') :
    Reach (Step sourceEval) (mapCfg f t) (mapCfg f t') := by
  induction path with
  | refl => exact Reach.refl _
  | tail _ edge ih => exact Reach.tail ih (map_step f sourceEval targetEval commutes edge)

/-- Exact reference prefix coverage. This quantifies over every client
continuation and every allocator branch, including bad finite prefixes. -/
theorem prefix_iff (t : Config T) (s' : Config S) :
    Reach (Step sourceEval) (mapCfg f t) s' ↔
      ∃ t', Reach (Step targetEval) t t' ∧ mapCfg f t' = s' := by
  constructor
  · intro path
    obtain ⟨t', targetPath, related⟩ := PrefixTransfer.reachable_coverage
      (source_simulation f sourceEval targetEval commutes) rfl path
    exact ⟨t', targetPath, related.symm⟩
  · rintro ⟨t', targetPath, rfl⟩
    exact map_reach f sourceEval targetEval commutes targetPath

theorem noUB_iff (t : Config T) :
    NoUB (Step sourceEval) Bad (mapCfg f t) ↔ NoUB (Step targetEval) Bad t := by
  constructor
  · exact PrefixTransfer.sourceSafety (target_simulation f sourceEval targetEval commutes) rfl
  · exact PrefixTransfer.sourceSafety (source_simulation f sourceEval targetEval commutes) rfl

end GenericCorrespondence

abbrev SourceStep := Step sourceExecute
abbrev TargetStep := Step targetExecute

theorem memory_prefix_iff (t : Config MiniRustFactored.State) (s : Config MiniRustReference.State) :
    Reach SourceStep (mapCfg MiniRustFactored.reify t) s ↔
      ∃ t', Reach TargetStep t t' ∧ mapCfg MiniRustFactored.reify t' = s :=
  prefix_iff MiniRustFactored.reify sourceExecute targetExecute execute_reify t s

theorem memory_noUB_iff (t : Config MiniRustFactored.State) :
    NoUB SourceStep Bad (mapCfg MiniRustFactored.reify t) ↔ NoUB TargetStep Bad t :=
  noUB_iff MiniRustFactored.reify sourceExecute targetExecute execute_reify t

theorem reify_encode_config (s : Config MiniRustReference.State) :
    mapCfg MiniRustFactored.reify (mapCfg MiniRustFactored.encode s) = s := by
  cases s <;> simp only [mapCfg, MiniRustFactored.reify_encode]

theorem encoded_noUB_iff (s : Config MiniRustReference.State) :
    NoUB SourceStep Bad s ↔ NoUB TargetStep Bad (mapCfg MiniRustFactored.encode s) := by
  simpa only [reify_encode_config] using memory_noUB_iff (mapCfg MiniRustFactored.encode s)

/-- Stop classification is a policy distinct from absence of UB. In particular
the caller chooses how to classify source Exit's memoryLeak tag. -/
def AllowedStop {S : Type} (allowExit : MiniRustReference.ExitResult → Prop) : Config S → Prop
  | .completed _ _ => True
  | .terminated _ result _ => allowExit result
  | _ => False

theorem unsupported_not_allowed {S : Type} (allowExit : MiniRustReference.ExitResult → Prop) (memory : S) :
    ¬ AllowedStop allowExit (.unsupported memory) := id

/-- Empty allocator choice yields no branch. Conditional safety here cannot
be promoted to a progress or accepted-stop claim. -/
theorem empty_choice_safe_without_progress {S : Type}
    (eval : Nat → S → Op → EvalAnswer S) (memory : S) (op : Op)
    (continuation : Reply → Plan) (trace : List Event) (allowExit : MiniRustReference.ExitResult → Prop)
    (empty : ∀ candidate, eval candidate memory op = .noChoice) :
    NoUB (Step eval) Bad (.running memory (.call op continuation) trace) ∧
    ¬ ReachableProgress (Step eval) (AllowedStop allowExit)
      (.running memory (.call op continuation) trace) := by
  let start : Config S := .running memory (.call op continuation) trace
  have noNext : ¬ ∃ successor, Step eval start successor := by
    rintro ⟨successor, candidate, edge⟩
    change (match eval candidate memory op with
      | .good reply nextMemory => some (Config.running nextMemory (continuation reply)
          (trace ++ [.answered op reply]))
      | .ub diagnostic => some (.bad memory diagnostic)
      | .unsupported => some (.unsupported memory)
      | .noChoice => none
      | .exit result => some (.terminated memory result (trace ++ [.exited result]))) =
        some successor at edge
    rw [empty candidate] at edge
    cases edge
  constructor
  · apply invariant_noUB (Invariant := fun reached => reached = start) rfl
    · intro s t same edge
      subst s
      exact False.elim (noNext ⟨t, edge⟩)
    · intro s same bad
      subst s
      exact bad
  · intro progress
    rcases progress start (Reach.refl _) with allowed | nextState
    · exact allowed
    · exact noNext nextState

#print axioms execute_reify
#print axioms source_simulation
#print axioms target_simulation
#print axioms memory_prefix_iff
#print axioms memory_noUB_iff
#print axioms encoded_noUB_iff
#print axioms empty_choice_safe_without_progress

end AnnealResearch.MemoryExecution
