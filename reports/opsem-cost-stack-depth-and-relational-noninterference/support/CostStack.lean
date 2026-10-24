import AnnealResearch.Execution

/-!
Owned cost/stack observation experiment. This is not Rust, MiniRust, an ISA,
a general compiler, or an independent target implementation.

The finite language is one recursively invoked procedure: `enter n` makes n
nested calls, its base case starts returning, and every invocation returns 0.
A list contains actual pending return frames; call pushes and return pops it.
Depth includes the currently active invocation, including the initial one.
Every source transition costs one. The target elaborates every transition into
one charged administrative step and one core step. Its pending administrative
states are operational configurations and are included in every prefix bound.
Peak depth is an accumulated maximum, including initial and transient frames.

The two mutation controls preserve output and NoUB: charging administration
violates an unadjusted source cost budget; inserting one extra recursive call
pushes and later pops a frame and violates an unadjusted source peak budget.
These are exact observations for this declared metric, not performance data or
claims that a compiler must implement calls this way. Arbitrary bound functions
are transported within this family. Fault/spin controls separately retain an
observable bad finite prefix before an actual infinite enabled continuation.
-/

namespace AnnealResearch.CostStack

open Execution

inductive Core where
  | enter (remaining : Nat) (returns : List Unit)
  | leave (returns : List Unit)
  | done
  | fault
  | bad
  | spin
  deriving DecidableEq, Repr

/-- Suspended returns plus the active invocation; completion has no frame. -/
def depth : Core → Nat
  | .enter _ stack | .leave stack => stack.length + 1
  | .done => 0
  | .fault | .bad | .spin => 1

inductive CoreStep : Core → Core → Prop where
  | call : CoreStep (.enter (n + 1) stack) (.enter n (() :: stack))
  | base : CoreStep (.enter 0 stack) (.leave stack)
  | ret : CoreStep (.leave (() :: stack)) (.leave stack)
  | finish : CoreStep (.leave []) .done
  | fault : CoreStep .fault .bad
  | afterBad : CoreStep .bad .spin
  | spin : CoreStep .spin .spin

/-- A ranking potential for the finite call/return family only. -/
def remaining : Core → Nat
  | .enter n stack => 2 * n + stack.length + 2
  | .leave stack => stack.length + 1
  | _ => 0

def Shape (n : Nat) : Core → Prop
  | .enter r stack => r + stack.length = n
  | .leave stack => stack.length ≤ n
  | .done => True
  | _ => False

def sourceBudget (n : Nat) : Nat := 2 * n + 2

theorem core_progress {n : Nat} {c c' : Core}
    (shape : Shape n c) (edge : CoreStep c c') :
    Shape n c' ∧ remaining c = remaining c' + 1 ∧ depth c' ≤ n + 1 := by
  cases edge <;> simp_all [Shape, remaining, depth] <;> omega

structure SourceState where
  core : Core
  work : Nat
  peak : Nat
  deriving DecidableEq, Repr

inductive SourceStep : SourceState → SourceState → Prop where
  | execute {c c' : Core} {work peak : Nat} (edge : CoreStep c c') :
      SourceStep ⟨c, work, peak⟩
        ⟨c', work + 1, max peak (depth c')⟩

def sourceInitial (n : Nat) : SourceState := ⟨.enter n [], 0, 1⟩
def SourceBad (s : SourceState) : Prop := s.core = .bad
def SourceOutput (s : SourceState) (value : Nat) : Prop :=
  s.core = .done ∧ value = 0

structure SourceInvariant (n : Nat) (s : SourceState) : Prop where
  shape : Shape n s.core
  budget : s.work + remaining s.core = sourceBudget n
  depth_seen : depth s.core ≤ s.peak
  peak_bound : s.peak ≤ n + 1

theorem source_initial_invariant (n : Nat) :
    SourceInvariant n (sourceInitial n) := by
  constructor <;> simp [sourceInitial, Shape, remaining, sourceBudget, depth]

theorem source_preserves {n : Nat} {s s' : SourceState}
    (inv : SourceInvariant n s) (edge : SourceStep s s') :
    SourceInvariant n s' := by
  cases edge with
  | execute coreEdge =>
      obtain ⟨nextShape, remainingEq, depthBound⟩ := core_progress inv.shape coreEdge
      constructor
      · exact nextShape
      · have budget := inv.budget
        dsimp at budget remainingEq ⊢
        omega
      · dsimp
        exact Nat.le_max_right _ _
      · exact Nat.max_le_of_le_of_le inv.peak_bound depthBound

theorem source_reachable {n : Nat} {s : SourceState}
    (path : Reach SourceStep (sourceInitial n) s) : SourceInvariant n s :=
  invariant_reachable (source_initial_invariant n)
    (fun inv edge => source_preserves inv edge) path

/-- Every source prefix, including the initial and completed configurations. -/
theorem source_prefix_bounds {n : Nat} {s : SourceState}
    (path : Reach SourceStep (sourceInitial n) s) :
    s.work ≤ sourceBudget n ∧ depth s.core ≤ s.peak ∧ s.peak ≤ n + 1 := by
  have inv := source_reachable path
  have budget := inv.budget
  exact ⟨by omega, inv.depth_seen, inv.peak_bound⟩

theorem source_noUB (n : Nat) :
    NoUB SourceStep SourceBad (sourceInitial n) := by
  intro reached path bad
  have shape := (source_reachable path).shape
  rw [bad] at shape
  exact shape

/-- Calls and returns really execute; no safety theorem supplies this witness. -/
theorem core_complete (n : Nat) (stack : List Unit) :
    Reach CoreStep (.enter n stack) (.leave stack) := by
  induction n generalizing stack with
  | zero => exact Reach.tail (Reach.refl _) CoreStep.base
  | succ n ih =>
      exact Reach.tail
        ((Reach.tail (Reach.refl _) CoreStep.call).trans (ih (() :: stack)))
        CoreStep.ret

theorem core_unwind (stack : List Unit) : Reach CoreStep (.leave stack) .done := by
  induction stack with
  | nil => exact Reach.tail (Reach.refl _) CoreStep.finish
  | cons frame stack ih =>
      cases frame
      exact (Reach.tail (Reach.refl _) CoreStep.ret).trans ih

theorem core_calls (n : Nat) (stack : List Unit) :
    ∃ peakStack, Reach CoreStep (.enter n stack) (.enter 0 peakStack) ∧
      peakStack.length = n + stack.length := by
  induction n generalizing stack with
  | zero => exact ⟨stack, Reach.refl _, by simp⟩
  | succ n ih =>
      obtain ⟨peakStack, path, length⟩ := ih (() :: stack)
      refine ⟨peakStack, (Reach.tail (Reach.refl _) CoreStep.call).trans path, ?_⟩
      simp only [List.length_cons] at length
      omega

/-- Instrumenting a core path gives an actual charged source path. -/
theorem lift_core {c d : Core} (path : Reach CoreStep c d)
    (s : SourceState) (initialCore : s.core = c) :
    ∃ t, Reach SourceStep s t ∧ t.core = d := by
  induction path with
  | refl => exact ⟨s, Reach.refl _, initialCore⟩
  | tail previous edge ih =>
      obtain ⟨current, currentPath, currentCore⟩ := ih
      have actualEdge := edge
      rw [← currentCore] at actualEdge
      exact ⟨_, Reach.tail currentPath (SourceStep.execute actualEdge), rfl⟩

theorem source_completion (n : Nat) :
    ∃ s, Reach SourceStep (sourceInitial n) s ∧ SourceOutput s 0 ∧
      s.work = sourceBudget n ∧ depth s.core = 0 := by
  have corePath := (core_complete n []).trans (core_unwind [])
  obtain ⟨s, path, done⟩ := lift_core corePath (sourceInitial n) rfl
  have budget := (source_reachable path).budget
  rw [done] at budget
  refine ⟨s, path, ⟨done, rfl⟩, ?_, ?_⟩
  · simpa [remaining] using budget
  · simp [done, depth]

theorem source_peak_witness (n : Nat) :
    ∃ stack s, Reach SourceStep (sourceInitial n) s ∧
      s.core = .enter 0 stack ∧ stack.length = n ∧ s.peak = n + 1 := by
  obtain ⟨stack, corePath, length⟩ := core_calls n []
  obtain ⟨s, path, atPeak⟩ := lift_core corePath (sourceInitial n) rfl
  have inv := source_reachable path
  have seen := inv.depth_seen
  have upper := inv.peak_bound
  simp only [List.length_nil, Nat.add_zero] at length
  rw [atPeak] at seen
  simp only [depth] at seen
  exact ⟨stack, s, path, atPeak, length, by omega⟩

structure TargetState where
  source : SourceState
  armed : Bool
  administrative : Nat
  deriving DecidableEq, Repr

/-- At source boundaries, administrative and useful charged work are equal. -/
def embed (s : SourceState) : TargetState := ⟨s, false, s.work⟩
def targetInitial (n : Nat) : TargetState := embed (sourceInitial n)
def total (t : TargetState) : Nat := t.source.work + t.administrative
def phaseCost (armed : Bool) : Nat := if armed then 1 else 0

def TargetBad (t : TargetState) : Prop := SourceBad t.source
def TargetOutput (t : TargetState) (value : Nat) : Prop := SourceOutput t.source value

inductive TargetStep : TargetState → TargetState → Prop where
  | prepare {s s' : SourceState} {a : Nat} (edge : SourceStep s s') :
      TargetStep ⟨s, false, a⟩ ⟨s, true, a + 1⟩
  | execute {s s' : SourceState} {a : Nat} (edge : SourceStep s s') :
      TargetStep ⟨s, true, a⟩ ⟨s', false, a⟩

/-- Each source transition is covered by a two-step, charged target path. -/
theorem source_edge_target_path {s s' : SourceState} (edge : SourceStep s s') :
    Reach TargetStep (embed s) (embed s') := by
  cases edge with
  | execute coreEdge =>
      exact Reach.tail
        (Reach.tail (Reach.refl _) (TargetStep.prepare (SourceStep.execute coreEdge)))
        (TargetStep.execute (SourceStep.execute coreEdge))

theorem source_path_target {s s' : SourceState} (path : Reach SourceStep s s') :
    Reach TargetStep (embed s) (embed s') := by
  induction path with
  | refl => exact Reach.refl _
  | tail _ edge ih => exact ih.trans (source_edge_target_path edge)

/-- Reverse coverage includes pending administrative states, not just boundaries. -/
theorem target_prefix_projection {s : SourceState} {t : TargetState}
    (path : Reach TargetStep (embed s) t) : Reach SourceStep s t.source := by
  induction path with
  | refl => exact Reach.refl _
  | tail _ edge ih =>
      cases edge with
      | prepare _ => exact ih
      | execute sourceEdge => exact Reach.tail ih sourceEdge

def Accounting (t : TargetState) : Prop :=
  t.administrative = t.source.work + phaseCost t.armed ∧
    (t.armed = true → ∃ next, SourceStep t.source next)

theorem accounting_initial (s : SourceState) : Accounting (embed s) := by
  constructor
  · simp [embed, phaseCost]
  · intro impossible
    cases impossible

theorem accounting_preserves {t t' : TargetState}
    (inv : Accounting t) (edge : TargetStep t t') : Accounting t' := by
  cases edge with
  | prepare sourceEdge =>
      constructor
      · have equation := inv.1
        simp only [phaseCost, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at equation
        simp only [phaseCost, ↓reduceIte]
        omega
      · intro _
        exact ⟨_, sourceEdge⟩
  | execute sourceEdge =>
      cases sourceEdge with
      | execute coreEdge =>
          constructor
          · have equation := inv.1
            simp only [phaseCost, ↓reduceIte] at equation
            simp only [phaseCost, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
            exact equation
          · intro impossible
            cases impossible

theorem target_accounting {s : SourceState} {t : TargetState}
    (path : Reach TargetStep (embed s) t) : Accounting t :=
  invariant_reachable (accounting_initial s)
    (fun inv edge => accounting_preserves inv edge) path

/-- An exact relationship at every target prefix; pending overhead is explicit. -/
theorem target_exact_cost {s : SourceState} {t : TargetState}
    (path : Reach TargetStep (embed s) t) :
    total t = 2 * t.source.work + phaseCost t.armed := by
  have equation := (target_accounting path).1
  dsimp [total]
  omega

theorem source_work_before_step {n : Nat} {s s' : SourceState}
    (inv : SourceInvariant n s) (edge : SourceStep s s') :
    s.work + 1 ≤ sourceBudget n := by
  have budget := (source_preserves inv edge).budget
  cases edge with
  | execute coreEdge =>
      dsimp at budget ⊢
      omega

/-- All intermediate target prefixes satisfy the sharp whole-family bounds. -/
theorem target_prefix_bounds {n : Nat} {t : TargetState}
    (path : Reach TargetStep (targetInitial n) t) :
    total t ≤ 2 * sourceBudget n ∧ depth t.source.core ≤ t.source.peak ∧
      t.source.peak ≤ n + 1 := by
  have projected := target_prefix_projection path
  have inv := source_reachable projected
  have account := target_accounting path
  have exactCost := target_exact_cost path
  have workBound := (source_prefix_bounds projected).1
  refine ⟨?_, inv.depth_seen, inv.peak_bound⟩
  cases phase : t.armed with
  | false =>
      simp only [phase, phaseCost, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at exactCost
      omega
  | true =>
      obtain ⟨next, edge⟩ := account.2 phase
      have before := source_work_before_step inv edge
      simp only [phase, phaseCost, ↓reduceIte] at exactCost
      omega

theorem target_noUB (n : Nat) : NoUB TargetStep TargetBad (targetInitial n) := by
  intro reached path bad
  exact source_noUB n reached.source (target_prefix_projection path) bad

/-- Arbitrary user-supplied time and peak functions bound every source prefix. -/
def SourceBounds (time stack : Nat → Nat) : Prop :=
  ∀ n s, Reach SourceStep (sourceInitial n) s →
    s.work ≤ time n ∧ s.peak ≤ stack n

def TargetBounds (time stack : Nat → Nat) : Prop :=
  ∀ n t, Reach TargetStep (targetInitial n) t →
    total t ≤ time n ∧ t.source.peak ≤ stack n

/-- Coverage and exact accounting suffice for a local 2*time+1 transport. -/
theorem arbitrary_prefix_bound_transport (time stack : Nat → Nat)
    (bound : SourceBounds time stack) :
    TargetBounds (fun n => 2 * time n + 1) stack := by
  intro n t path
  have sourceBound := bound n t.source (target_prefix_projection path)
  have exactCost := target_exact_cost path
  constructor
  · cases phase : t.armed <;> simp [phase, phaseCost] at exactCost <;> dsimp <;> omega
  · exact sourceBound.2

/-- In this completing family, the final source witness removes the +1 slack.
No monotonicity or closed form is assumed of either supplied bound function. -/
theorem arbitrary_bound_transport (time stack : Nat → Nat)
    (bound : SourceBounds time stack) : TargetBounds (fun n => 2 * time n) stack := by
  intro n t path
  obtain ⟨done, donePath, _, exactWork, _⟩ := source_completion n
  have finalBound := (bound n done donePath).1
  rw [exactWork] at finalBound
  have prefixBound := target_prefix_bounds path
  have projectedBound := bound n t.source (target_prefix_projection path)
  exact ⟨by dsimp; omega, projectedBound.2⟩

/-- Target completion is nonvacuous, has exactly twice the source cost, and
ends with no frames. The reached source state's peak is retained literally. -/
theorem target_completion (n : Nat) :
    ∃ s, Reach SourceStep (sourceInitial n) s ∧ SourceOutput s 0 ∧
      Reach TargetStep (targetInitial n) (embed s) ∧ TargetOutput (embed s) 0 ∧
      total (embed s) = 2 * sourceBudget n ∧ depth (embed s).source.core = 0 := by
  obtain ⟨s, path, output, cost, empty⟩ := source_completion n
  refine ⟨s, path, output, source_path_target path, output, ?_, empty⟩
  dsimp [total, embed]
  omega

/-- Output and NoUB do not imply preservation of the unadjusted cost budget. -/
theorem charged_extra_step_counterexample (n : Nat) :
    NoUB SourceStep SourceBad (sourceInitial n) ∧
    NoUB TargetStep TargetBad (targetInitial n) ∧
    ∃ s, Reach SourceStep (sourceInitial n) s ∧ SourceOutput s 0 ∧
      Reach TargetStep (targetInitial n) (embed s) ∧ TargetOutput (embed s) 0 ∧
      sourceBudget n < total (embed s) := by
  obtain ⟨s, sourcePath, sourceOut, targetPath, targetOut, exactCost, _⟩ :=
    target_completion n
  refine ⟨source_noUB n, target_noUB n,
    s, sourcePath, sourceOut, targetPath, targetOut, ?_⟩
  dsimp [sourceBudget] at exactCost ⊢
  omega

/-- Inserting one extra recursive invocation preserves output and safety but
really visits a deeper transient stack, then pops every frame before completion. -/
theorem deeper_stack_counterexample (n : Nat) :
    NoUB SourceStep SourceBad (sourceInitial n) ∧
    NoUB TargetStep TargetBad (targetInitial (n + 1)) ∧
    (∃ s, Reach SourceStep (sourceInitial n) s ∧ SourceOutput s 0 ∧ depth s.core = 0) ∧
    ∃ peakState done,
      Reach TargetStep (targetInitial (n + 1)) (embed peakState) ∧
      Reach TargetStep (embed peakState) (embed done) ∧
      peakState.peak = n + 2 ∧ depth peakState.core = n + 2 ∧
      TargetOutput (embed done) 0 ∧ depth done.core = 0 := by
  obtain ⟨sourceDone, sourcePath, sourceOut, _, sourceEmpty⟩ := source_completion n
  obtain ⟨stack, peakState, peakPath, atPeak, length, exactPeak⟩ :=
    source_peak_witness (n + 1)
  have restCore : Reach CoreStep peakState.core .done := by
    rw [atPeak]
    exact (core_complete 0 stack).trans (core_unwind stack)
  obtain ⟨done, restPath, doneCore⟩ := lift_core restCore peakState rfl
  refine ⟨source_noUB n, target_noUB (n + 1),
    ⟨sourceDone, sourcePath, sourceOut, sourceEmpty⟩,
    peakState, done, source_path_target peakPath, source_path_target restPath,
    ?_, ?_, ⟨doneCore, rfl⟩, ?_⟩
  · omega
  · rw [atPeak]
    simp only [depth]
    omega
  · simp [doneCore, depth]

namespace BadPrefix

def initial : SourceState := ⟨.fault, 0, 1⟩
def failed : SourceState := ⟨.bad, 1, 1⟩
def spinRun (k : Nat) : SourceState := ⟨.spin, k + 2, 1⟩

theorem enter_bad : SourceStep initial failed := SourceStep.execute CoreStep.fault

theorem bad_prefix_visible_in_both :
    ¬ NoUB SourceStep SourceBad initial ∧ ¬ NoUB TargetStep TargetBad (embed initial) := by
  have path : Reach SourceStep initial failed := Reach.tail (Reach.refl _) enter_bad
  constructor
  · exact bad_prefix_not_noUB path rfl
  · exact bad_prefix_not_noUB (source_path_target path) rfl

theorem reaches_infinite_suffix : Reach SourceStep initial (spinRun 0) := by
  exact Reach.tail (Reach.tail (Reach.refl _) enter_bad)
    (SourceStep.execute CoreStep.afterBad)

theorem actual_infinite_steps (k : Nat) : SourceStep (spinRun k) (spinRun (k + 1)) := by
  simpa [spinRun, depth, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (SourceStep.execute (work := k + 2) (peak := 1) CoreStep.spin)

/-- Each finite source segment of the infinite suffix also has target coverage. -/
theorem target_infinite_segments (k : Nat) :
    Reach TargetStep (embed (spinRun k)) (embed (spinRun (k + 1))) :=
  source_edge_target_path (actual_infinite_steps k)

end BadPrefix

#print axioms core_progress
#print axioms source_prefix_bounds
#print axioms source_noUB
#print axioms source_completion
#print axioms source_peak_witness
#print axioms source_path_target
#print axioms target_prefix_projection
#print axioms target_exact_cost
#print axioms target_prefix_bounds
#print axioms target_noUB
#print axioms arbitrary_prefix_bound_transport
#print axioms arbitrary_bound_transport
#print axioms target_completion
#print axioms charged_extra_step_counterexample
#print axioms deeper_stack_counterexample
#print axioms BadPrefix.bad_prefix_visible_in_both
#print axioms BadPrefix.reaches_infinite_suffix
#print axioms BadPrefix.actual_infinite_steps
#print axioms BadPrefix.target_infinite_segments

end AnnealResearch.CostStack
