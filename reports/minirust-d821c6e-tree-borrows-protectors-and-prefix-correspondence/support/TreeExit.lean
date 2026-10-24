import AnnealResearch.TreeMemoryControls

/-!
Explicit bookkeeping for the ordered releases performed by end_call. Supplied
obligations remain recorded; completed counts successful releases. Detaching the
single modeled frame is a separate owned stage, not a proof of Rust Return MIR,
return-value loading, local destruction, or general frame-stack correspondence.
Ordinary release UB retains its partial memory and terminates this controller.
-/
namespace AnnealResearch.TreeExit

open TreeMemory

structure Exiting where
  memory : State
  supplied : List Provenance
  completed : Nat

inductive Config where
  | running (exit : Exiting)
  | done (exit : Exiting)
  | ub (fault : Fault) (exit : Exiting)
  | unsupported (reason : Unsupported) (exit : Exiting)
  | invalidCursor (exit : Exiting)
  | noChoice (exit : Exiting)

def detach (state : State) : Exiting :=
  ⟨{ state with currentFrame := [] }, state.currentFrame, 0⟩

def step (exit : Exiting) : Config :=
  if exit.supplied.length < exit.completed then .invalidCursor exit
  else match exit.supplied[exit.completed]? with
  | none => .done exit
  | some provenance =>
    match release exit.memory provenance with
    | .ok () memory => .running { exit with memory, completed := exit.completed + 1 }
    | .ub fault memory => .ub fault { exit with memory }
    | .unsupported reason memory => .unsupported reason { exit with memory }
    | .noChoice memory => .noChoice { exit with memory }

/-- A finite-prefix observer, not a fuel-bounded operational semantics. step
itself has no horizon; terminal outcomes are never resumed by this observer. -/
def run : Nat → Config → Config
  | 0, config => config
  | count + 1, .running exit => run count (step exit)
  | _ + 1, config => config

theorem ub_never_resumes (count : Nat) (fault : Fault) (exit : Exiting) :
    run count (.ub fault exit) = .ub fault exit := by cases count <;> rfl

theorem detach_retains_obligations (state : State) :
    (detach state).memory.currentFrame = [] ∧
    (detach state).supplied = state.currentFrame ∧ (detach state).completed = 0 := ⟨rfl, rfl, rfl⟩

theorem successful_release_advances_cursor (exit : Exiting) (provenance : Provenance)
    (memory : State) (valid : exit.completed ≤ exit.supplied.length)
    (selected : exit.supplied[exit.completed]? = some provenance)
    (released : release exit.memory provenance = .ok () memory) :
    step exit = .running { exit with memory, completed := exit.completed + 1 } := by
  simp [step, Nat.not_lt.mpr valid, selected, released]

theorem failed_release_keeps_cursor (exit : Exiting) (provenance : Provenance)
    (fault : Fault) (memory : State) (valid : exit.completed ≤ exit.supplied.length)
    (selected : exit.supplied[exit.completed]? = some provenance)
    (released : release exit.memory provenance = .ub fault memory) :
    step exit = .ub fault { exit with memory } := by
  simp [step, Nat.not_lt.mpr valid, selected, released]

def mapFrame (frame : List Provenance) : Result A → Result A
  | .ok value state => .ok value { state with currentFrame := frame }
  | .ub fault state => .ub fault { state with currentFrame := frame }
  | .unsupported reason state => .unsupported reason { state with currentFrame := frame }
  | .noChoice state => .noChoice { state with currentFrame := frame }

theorem release_ignores_frame (state : State) (provenance : Provenance)
    (frame : List Provenance) :
    release { state with currentFrame := frame } provenance =
      mapFrame frame (release state provenance) := by
  rcases provenance with ⟨id, path⟩
  cases allocationFound : state.raw.allocations id <;> cases treeFound : state.trees id
  all_goals simp only [release, allocationFound, treeFound]
  all_goals try rfl
  rename_i allocation tree
  cases converted : TreeReference.unprotectAt tree path with
  | ub fault changed => rfl
  | unsupported reason changed => rfl
  | ok accesses changed =>
    cases live : allocation.live <;> simp only [Bool.not_false, Bool.not_true,
      ite_true, Bool.false_eq_true, ite_false]
    · rfl
    · cases TreeReference.releaseTraverse changed (some path) accesses with
      | ok value next => cases value; rfl
      | ub fault next => rfl
      | unsupported reason next => rfl

namespace Controls

open TreeMemoryControls

def completedWeak : Exiting :=
  ⟨{ deadWeakReleased with currentFrame := [] }, [(0, [0, 0])], 1⟩

theorem weak_exit_first_release : step (detach deadWeak) = .running completedWeak := by
  change step ⟨{ deadWeak with currentFrame := [] }, [(0, [0, 0])], 0⟩ = _
  simp only [step, List.length_singleton, List.getElem?_cons_zero,
    release_ignores_frame, successful_dead_weak_release, mapFrame]
  rfl

theorem weak_exit_completes : run 2 (.running (detach deadWeak)) = .done completedWeak := by
  simp only [run, weak_exit_first_release]
  rfl

theorem completed_weak_exit_has_stale_flag :
    completedWeak.memory.currentFrame = [] ∧
    completedWeak.supplied = [(0, [0, 0])] ∧ completedWeak.completed = 1 ∧
    (TreeReference.findNode treeDeadWeakReleased [0, 0]).map TreeReference.Node.protection =
      some .weak := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  simp [treeDeadWeakReleased, TreeReference.findNode, TreeReference.Node.children,
    TreeReference.Node.protection]

def completedStrong : Exiting :=
  ⟨{ releasedState with currentFrame := [] }, [(0, [0, 0])], 1⟩

theorem strong_exit_first_release : step (detach (writeState .strong)) =
    .running completedStrong := by
  change step ⟨{ writeState .strong with currentFrame := [] }, [(0, [0, 0])], 0⟩ = _
  simp only [step, List.length_singleton, List.getElem?_cons_zero,
    release_ignores_frame, successful_live_release, mapFrame]
  rfl

theorem strong_exit_completes : run 2 (.running (detach (writeState .strong))) =
    .done completedStrong := by
  simp only [run, strong_exit_first_release]
  rfl

def failedLive : Exiting :=
  ⟨{ setTree liveFailure 0 liveFailureConverted with currentFrame := [] }, [(0, [0])], 0⟩

/-- The input uses the separately labeled shape-only live-failure specimen. -/
theorem failed_live_exit_is_terminal : step (detach liveFailure) =
    .ub (.tree .unprotectedLocalWriteFrozen) failedLive := by
  change step ⟨{ liveFailure with currentFrame := [] }, [(0, [0])], 0⟩ = _
  simp only [step, List.length_singleton, List.getElem?_cons_zero,
    release_ignores_frame, live_failed_release_commits_conversion, mapFrame]
  rfl

theorem failure_keeps_detached_obligation :
    failedLive.memory.currentFrame = [] ∧ failedLive.supplied = [(0, [0])] ∧
    failedLive.completed = 0 := ⟨rfl, rfl, rfl⟩

end Controls

#print axioms ub_never_resumes
#print axioms detach_retains_obligations
#print axioms successful_release_advances_cursor
#print axioms failed_release_keeps_cursor
#print axioms release_ignores_frame
#print axioms Controls.weak_exit_first_release
#print axioms Controls.weak_exit_completes
#print axioms Controls.completed_weak_exit_has_stale_flag
#print axioms Controls.strong_exit_first_release
#print axioms Controls.strong_exit_completes
#print axioms Controls.failed_live_exit_is_terminal
#print axioms Controls.failure_keeps_detached_obligation

end AnnealResearch.TreeExit
