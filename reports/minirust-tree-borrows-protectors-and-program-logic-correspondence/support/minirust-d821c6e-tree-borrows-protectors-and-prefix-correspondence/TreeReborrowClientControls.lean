import AnnealResearch.TreeReborrowPrefixes
import AnnealResearch.TreeReborrowPairedControls

/-!
Enabled internal loops and an actual terminal partial-reborrow UB exercise the
new exact-prefix observer. The Disabled-root input is shape-admitted only;
these controls assert no construction history, Rust reachability or valid frame
obligations. A separate successful constructed pointer-consuming client is not
duplicated here.

The factored error memory is obtained from a proved actual primitive-result
witness. There is no default-success extraction, reference-defined F execution,
terminal continuation, fairness, cost or termination-conditional safety claim.
-/

namespace AnnealResearch.TreeReborrowClientControls

open TreeReborrowClient

def loop : Controller Nat := fun control => .internal (control + 1)

theorem floop_prefix (count control : Nat) (memory : TreeFactoredMemory.State) :
    fIterate loop count (.running control memory) = some (.running (control + count) memory) := by
  induction count generalizing control with
  | zero => rfl
  | succ count ih =>
      change fIterate loop count (.running (control + 1) memory) =
        some (.running (control + (count + 1)) memory)
      rw [ih]
      simp [Nat.add_comm, Nat.add_left_comm]

theorem rloop_prefix (count control : Nat) (memory : TreeMemory.State) :
    rIterate loop count (.running control memory) = some (.running (control + count) memory) := by
  induction count generalizing control with
  | zero => rfl
  | succ count ih =>
      change rIterate loop count (.running (control + 1) memory) =
        some (.running (control + (count + 1)) memory)
      rw [ih]
      simp [Nat.add_comm, Nat.add_left_comm]

theorem floop_NoUB (control : Nat) (memory : TreeFactoredMemory.State) :
    FNoUB loop (.running control memory) := by
  intro count reached found
  rw [floop_prefix] at found
  cases found
  exact False.elim

theorem rloop_NoUB (control : Nat) (memory : TreeMemory.State) :
    RNoUB loop (.running control memory) := by
  intro count reached found
  rw [rloop_prefix] at found
  cases found
  exact False.elim

/-- The success continuation would reach control one and halt. Actual UB at
control zero terminates instead; the client cannot execute that continuation. -/
def failing : Controller Nat
  | 0 => .call (.reborrow TreeMemoryControls.root TreeReborrowStateControls.reads) (fun _ => 1)
  | _ => .halt 7

def rinitial : RConfig Nat := .running 0 TreeReborrowStateControls.before
def rfailed : RConfig Nat :=
  .ub 0 (.tree .unprotectedLocalReadDisabled) TreeReborrowStateControls.partialState
def finitial : FConfig Nat := .running 0 TreeReborrowPairedControls.before
def ffailed (changed : TreeFactoredMemory.State) : FConfig Nat :=
  .ub 0 (.tree .unprotectedLocalReadDisabled) changed

theorem initial_sized : ConfigWellSized finitial := TreeReborrowPairedControls.before_sized

theorem reference_failed_step : rStep failing rinitial = some rfailed := by
  simp only [rStep, rinitial, failing, rDispatch,
    TreeReborrowStateControls.actual_partial_initial_failure, TreeMemoryClient.rMap, rResume, rfailed]

theorem reference_failed_prefix : rIterate failing 1 rinitial = some rfailed := by
  change (rStep failing rinitial).bind (fun next => some next) = some rfailed
  rw [reference_failed_step]
  rfl

theorem reference_not_NoUB : ¬ RNoUB failing rinitial := by
  intro safe
  exact safe 1 rfailed reference_failed_prefix (by trivial)

theorem reference_no_resumption (count : Nat) :
    rIterate failing (count + 1) rfailed = none :=
  TreeMemoryClient.iterate_no_successor (rStep failing) rfailed count rfl

theorem reference_later_absent (count : Nat) : rIterate failing (count + 2) rinitial = none := by
  change (rStep failing rinitial).bind
    (fun next => TreeMemoryClient.iterate (rStep failing) (count + 1) next) = none
  rw [reference_failed_step]
  exact reference_no_resumption count

theorem reference_never_finishes (count control result : Nat) (memory : TreeMemory.State) :
    rIterate failing count rinitial ≠ some (.finished control result memory) := by
  cases count with
  | zero => simp [rIterate, TreeMemoryClient.iterate, rinitial]
  | succ count =>
      cases count with
      | zero => rw [reference_failed_prefix]; simp [rfailed]
      | succ count => rw [reference_later_absent]; simp

theorem reference_retained_observations :
    rfailed.memory.raw = TreeReborrowStateControls.before.raw ∧
      rfailed.memory.currentFrame = [(42, [3])] ∧
      rfailed.memory.trees 0 = some TreeReborrowStateControls.partialTree := by
  have retained := TreeReborrowStateControls.failed_birth_retains_partial_tree_and_old_frame
  exact ⟨retained.1, retained.2.1, retained.2.2.1⟩

theorem partial_state_changed :
    TreeReborrowStateControls.partialState ≠ TreeReborrowStateControls.before := by
  intro same
  have treeSame := congrArg (fun state : TreeMemory.State => state.trees 0) same
  have present : TreeReborrowStateControls.before.trees 0 = some TreeReborrowStateControls.rootTree := by
    simp [TreeReborrowStateControls.before, TreeMemory.setTree]
  rw [TreeReborrowStateControls.failed_birth_retains_partial_tree_and_old_frame.2.2.1, present] at treeSame
  have nodes := Option.some.inj treeSame
  have lengths := congrArg (fun node : TreeReference.Node => node.children.length) nodes
  change (1 : Nat) = 0 at lengths
  omega

theorem factored_failed_step (changed : TreeFactoredMemory.State)
    (actual : TreeFactoredMemory.reborrow TreeReborrowPairedControls.before
      TreeMemoryControls.root TreeReborrowStateControls.reads =
        .ub (.tree .unprotectedLocalReadDisabled) changed) :
    fStep failing finitial = some (ffailed changed) := by
  simp only [fStep, finitial, failing, fDispatch, actual, TreeMemoryClient.fMap, fResume, ffailed]

theorem factored_failed_prefix (changed : TreeFactoredMemory.State)
    (actual : TreeFactoredMemory.reborrow TreeReborrowPairedControls.before
      TreeMemoryControls.root TreeReborrowStateControls.reads =
        .ub (.tree .unprotectedLocalReadDisabled) changed) :
    fIterate failing 1 finitial = some (ffailed changed) := by
  change (fStep failing finitial).bind (fun next => some next) = some (ffailed changed)
  rw [factored_failed_step changed actual]
  rfl

theorem factored_no_resumption (changed : TreeFactoredMemory.State) (count : Nat) :
    fIterate failing (count + 1) (ffailed changed) = none :=
  TreeMemoryClient.iterate_no_successor (fStep failing) (ffailed changed) count rfl

theorem factored_later_absent (changed : TreeFactoredMemory.State)
    (actual : TreeFactoredMemory.reborrow TreeReborrowPairedControls.before
      TreeMemoryControls.root TreeReborrowStateControls.reads =
        .ub (.tree .unprotectedLocalReadDisabled) changed) (count : Nat) :
    fIterate failing (count + 2) finitial = none := by
  change (fStep failing finitial).bind
    (fun next => TreeMemoryClient.iterate (fStep failing) (count + 1) next) = none
  rw [factored_failed_step changed actual]
  exact factored_no_resumption changed count

theorem factored_never_finishes (changed : TreeFactoredMemory.State)
    (actual : TreeFactoredMemory.reborrow TreeReborrowPairedControls.before
      TreeMemoryControls.root TreeReborrowStateControls.reads =
        .ub (.tree .unprotectedLocalReadDisabled) changed)
    (count control result : Nat) (memory : TreeFactoredMemory.State) :
    fIterate failing count finitial ≠ some (.finished control result memory) := by
  cases count with
  | zero => simp [fIterate, TreeMemoryClient.iterate, finitial]
  | succ count =>
      cases count with
      | zero => rw [factored_failed_prefix changed actual]; simp [ffailed]
      | succ count => rw [factored_later_absent changed actual]; simp

theorem factored_not_NoUB : ¬ FNoUB failing finitial := by
  obtain ⟨changed, actual, _, _, _⟩ := TreeReborrowPairedControls.actual_partial_result_witness
  intro safe
  exact safe 1 (ffailed changed) (factored_failed_prefix changed actual) (by trivial)

/-- An actual F error result supplies the terminal configuration. Its exact
represented partial tree, raw/frame observations, structural domain and every
later absent horizon are retained. The specimen remains shape-only. -/
theorem actual_factored_terminal_witness :
    ∃ changed,
      TreeFactoredMemory.reborrow TreeReborrowPairedControls.before TreeMemoryControls.root
        TreeReborrowStateControls.reads = .ub (.tree .unprotectedLocalReadDisabled) changed ∧
      fIterate failing 1 finitial = some (ffailed changed) ∧
      TreeFactoredMemory.reify changed = TreeReborrowStateControls.partialState ∧
      changed.raw = TreeReborrowPairedControls.before.raw ∧
      changed.currentFrame = [(42, [3])] ∧
      (changed.trees 0).map TreeCorrespondence.reify = some TreeReborrowStateControls.partialTree ∧
      changed ≠ TreeReborrowPairedControls.before ∧
      ConfigWellSized (ffailed changed) ∧
      (∀ count, fIterate failing (count + 1) (ffailed changed) = none) ∧
      (∀ count control result memory,
        fIterate failing count finitial ≠ some (.finished control result memory)) := by
  obtain ⟨changed, actual, represented, raw, frame⟩ :=
    TreeReborrowPairedControls.actual_partial_result_witness
  have reachedAt := factored_failed_prefix changed actual
  have tree : (changed.trees 0).map TreeCorrespondence.reify =
      some TreeReborrowStateControls.partialTree := by
    change (TreeFactoredMemory.reify changed).trees 0 = _
    rw [represented]
    exact TreeReborrowStateControls.failed_birth_retains_partial_tree_and_old_frame.2.2.1
  have different : changed ≠ TreeReborrowPairedControls.before := by
    intro same
    have observed := represented
    rw [same, TreeReborrowPairedControls.before_reifies] at observed
    exact partial_state_changed observed.symm
  refine ⟨changed, actual, reachedAt, represented, raw, frame, tree, different, ?_, ?_, ?_⟩
  · exact TreeReborrowPrefixes.prefix_preserves failing 1 finitial (ffailed changed) initial_sized reachedAt
  · exact factored_no_resumption changed
  · exact factored_never_finishes changed actual

#print axioms floop_prefix
#print axioms rloop_prefix
#print axioms floop_NoUB
#print axioms rloop_NoUB
#print axioms initial_sized
#print axioms reference_failed_step
#print axioms reference_failed_prefix
#print axioms reference_not_NoUB
#print axioms reference_no_resumption
#print axioms reference_later_absent
#print axioms reference_never_finishes
#print axioms reference_retained_observations
#print axioms partial_state_changed
#print axioms factored_failed_step
#print axioms factored_failed_prefix
#print axioms factored_no_resumption
#print axioms factored_later_absent
#print axioms factored_never_finishes
#print axioms factored_not_NoUB
#print axioms actual_factored_terminal_witness

end AnnealResearch.TreeReborrowClientControls
