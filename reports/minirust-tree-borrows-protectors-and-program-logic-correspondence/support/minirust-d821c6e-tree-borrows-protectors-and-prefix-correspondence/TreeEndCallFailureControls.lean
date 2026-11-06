import AnnealResearch.TreeEndCallProperties
import AnnealResearch.TreeMemoryControls

/-!
Three distinct live allocation IDs distinguish committed success, partial UB
and a meaningful unexecuted suffix. The outer tree shapes reuse the old changing
successful-release specimen; the middle reuses the shape-only live failure.
The explicit product as a whole has no proved source construction history.

The real F fold is observed through exact encoding, width and correspondence.
The three named mutants below are R-only alternative equations. In particular,
the continue mutant is not a continuation of real execution after UB. No helper,
source-frame ownership, Return/unwind, NoUB or Rust adequacy theorem is claimed.
-/
namespace AnnealResearch.TreeEndCallFailureControls

open TreePermissions
open TreeEndCall

def active : TreeReference.Node := TreeMemoryControls.treeWrite .strong
def cleared : TreeReference.Node := TreeMemoryControls.treeReleased
def middle : TreeReference.Node := TreeMemoryControls.liveFailureTree
def converted : TreeReference.Node := TreeMemoryControls.liveFailureConverted

def blockAt (address : Nat) : MiniRustReference.Allocation :=
  { TreeMemoryControls.block 1 with base := address }

def raw : MiniRustReference.State :=
  { next := 3
    allocations := fun id =>
      if id = 0 then some (blockAt 16)
      else if id = 1 then some (blockAt 32)
      else if id = 2 then some (blockAt 48)
      else none }

def registrations : List TreeMemory.Provenance :=
  [(0, [0, 0]), (1, [0]), (2, [0, 0])]

/-- Explicit complete maps. The recorded list is an ordinary supplied value;
the operation's registrations need not equal this memory field in general. -/
def product (first second third : TreeReference.Node) : TreeMemory.State :=
  { raw
    trees := fun id =>
      if id = 0 then some first
      else if id = 1 then some second
      else if id = 2 then some third
      else none
    currentFrame := registrations }

def before : TreeMemory.State := product active middle active
def afterFirst : TreeMemory.State := product cleared middle active
def failed : TreeMemory.State := product cleared converted active
def continued : TreeMemory.State := product cleared converted cleared
def fault : TreeMemory.Fault := .tree .unprotectedLocalWriteFrozen
def extra : SuppliedFrameExtra := ⟨registrations⟩

private theorem set_product_zero (a b c changed : TreeReference.Node) :
    TreeMemory.setTree (product a b c) 0 changed = product changed b c := by
  unfold TreeMemory.setTree product
  congr 1
  funext id
  by_cases zero : id = 0 <;> simp [zero]

private theorem set_product_one (a b c changed : TreeReference.Node) :
    TreeMemory.setTree (product a b c) 1 changed = product a changed c := by
  unfold TreeMemory.setTree product
  congr 1
  funext id
  by_cases zero : id = 0
  · subst id; rfl
  · by_cases one : id = 1 <;> simp [zero, one]

private theorem set_product_two (a b c changed : TreeReference.Node) :
    TreeMemory.setTree (product a b c) 2 changed = product a b changed := by
  unfold TreeMemory.setTree product
  congr 1
  funext id
  by_cases zero : id = 0
  · subst id; rfl
  · by_cases one : id = 1
    · subst id; rfl
    · by_cases two : id = 2 <;> simp [zero, one, two]

attribute [local simp] TreeReference.modifyAt TreeReference.replaceNth
  TreeReference.unprotectAt TreeReference.unprotectPermissions
  TreeReference.releaseTraverse TreeReference.releaseCore TreeReference.releaseChildren
  TreeReference.applyAccesses TreeReference.arraysSized TreeReference.childrenSized
  TreeReference.pathPresent TreeReference.findNode TreeReference.nodeRelation
  TreeReference.childPath TreeReference.Node.permissions TreeReference.Node.children
  TreeReference.Node.protection TreeReference.Result.mapState
  Permission.unprotect PPermission.unprotect Permission.transition
  UPermission.transition UPermission.localRead UPermission.localWrite
  UPermission.foreignRead UPermission.foreignWrite Protected.yes

private theorem good_release_at (memory : TreeMemory.State) (id : Nat)
    (allocation : MiniRustReference.Allocation)
    (allocated : memory.raw.allocations id = some allocation)
    (live : allocation.live = true) (present : memory.trees id = some active) :
    TreeMemory.release memory (id, [0, 0]) =
      .ok () (TreeMemory.setTree memory id cleared) := by
  simp [TreeMemory.release, allocated, live, present, active, cleared,
    TreeMemoryControls.treeWrite, TreeMemoryControls.treeReleased]

private theorem bad_release_at (memory : TreeMemory.State) (id : Nat)
    (allocation : MiniRustReference.Allocation)
    (allocated : memory.raw.allocations id = some allocation)
    (live : allocation.live = true) (present : memory.trees id = some middle) :
    TreeMemory.release memory (id, [0]) =
      .ub fault (TreeMemory.setTree memory id converted) := by
  simp [TreeMemory.release, allocated, live, present, middle, converted, fault,
    TreeMemoryControls.liveFailureTree, TreeMemoryControls.liveFailureConverted]

theorem first_release : TreeMemory.release before (0, [0, 0]) = .ok () afterFirst := by
  have actual := good_release_at before 0 (blockAt 16) rfl rfl rfl
  simpa only [before, afterFirst, set_product_zero] using actual

theorem middle_release : TreeMemory.release afterFirst (1, [0]) = .ub fault failed := by
  have actual := bad_release_at afterFirst 1 (blockAt 32) rfl rfl rfl
  simpa only [afterFirst, failed, set_product_one] using actual

/-- The suffix would make a real, observable change if an alternative policy
ran it from the failing residual. It is not an edge after UB in the real fold. -/
theorem standalone_third_release :
    TreeMemory.release failed (2, [0, 0]) = .ok () continued := by
  have actual := good_release_at failed 2 (blockAt 48) rfl rfl rfl
  simpa only [failed, continued, set_product_two] using actual

theorem actual_fold : rReleaseList before registrations = .ub fault failed := by
  simp only [registrations, rReleaseList, first_release, middle_release]

theorem actual_end_call : rEndCall before extra = .ub fault failed := actual_fold

private theorem product_width (a b c : TreeReference.Node)
    (aw : TreeReference.arraysSized a 1 = true)
    (bw : TreeReference.arraysSized b 1 = true)
    (cw : TreeReference.arraysSized c 1 = true) :
    TreeMemoryEncoding.RWellSized (product a b c) := by
  intro id allocation tree allocated present
  by_cases zero : id = 0
  · subst id
    have sameAllocation : blockAt 16 = allocation := Option.some.inj allocated
    have sameTree : a = tree := Option.some.inj present
    subst allocation
    subst tree
    exact aw
  · by_cases one : id = 1
    · subst id
      have sameAllocation : blockAt 32 = allocation := Option.some.inj allocated
      have sameTree : b = tree := Option.some.inj present
      subst allocation
      subst tree
      exact bw
    · by_cases two : id = 2
      · subst id
        have sameAllocation : blockAt 48 = allocation := Option.some.inj allocated
        have sameTree : c = tree := Option.some.inj present
        subst allocation
        subst tree
        exact cw
      · simp [product, raw, zero, one, two] at allocated

theorem before_width : TreeMemoryEncoding.RWellSized before := by
  apply product_width
  all_goals simp [active, middle, TreeMemoryControls.treeWrite,
    TreeMemoryControls.liveFailureTree]

theorem failed_width : TreeMemoryEncoding.RWellSized failed := by
  apply product_width
  all_goals simp [active, cleared, converted, TreeMemoryControls.treeWrite,
    TreeMemoryControls.treeReleased, TreeMemoryControls.liveFailureConverted]

private theorem active_matching : TreeReference.kindsMatch active = true := by
  simp [active, TreeMemoryControls.treeWrite, TreeReference.kindsMatch,
    TreeReference.childrenMatch, Permission.matchesProtector, Permission.isProt]

theorem initial_matching : TreeLiveKinds.LiveKinds before := by
  intro id allocation tree allocated alive present
  by_cases zero : id = 0
  · subst id
    have same : active = tree := Option.some.inj present
    subst tree
    exact active_matching
  · by_cases one : id = 1
    · subst id
      have same : middle = tree := Option.some.inj present
      subst tree
      exact TreeMemoryControls.live_failure_matching_scope.2.1
    · by_cases two : id = 2
      · subst id
        have same : active = tree := Option.some.inj present
        subst tree
        exact active_matching
      · simp [before, product, zero, one, two] at present

theorem failed_not_matching : ¬ TreeLiveKinds.LiveKinds failed := by
  intro matching
  have forced := matching 1 (blockAt 32) converted rfl rfl rfl
  have mismatch : TreeReference.kindsMatch converted = false :=
    TreeMemoryControls.live_failure_matching_scope.2.2
  rw [mismatch] at forced
  cases forced

/-- All three raw records remain live/nonempty; terminal mismatch is not made
vacuous by removing the middle allocation or marking it dead. -/
theorem real_observations :
    failed.raw = before.raw ∧ failed.currentFrame = registrations ∧
    failed.trees 0 = some cleared ∧ failed.trees 1 = some converted ∧
    failed.trees 2 = some active ∧
    failed.raw.allocations 0 = some (blockAt 16) ∧
    failed.raw.allocations 1 = some (blockAt 32) ∧
    failed.raw.allocations 2 = some (blockAt 48) ∧
    (blockAt 32).live = true ∧ (blockAt 32).size = 1 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Fixed alternative: run the real fold, then restore the operation input on
every non-success, retaining its original constructor and diagnostic. -/
def rollbackWholeOnError (memory : TreeMemory.State)
    (items : List TreeMemory.Provenance) : TreeMemory.Result Unit :=
  match rReleaseList memory items with
  | .ok () after => .ok () after
  | .ub diagnostic _ => .ub diagnostic memory
  | .unsupported reason _ => .unsupported reason memory
  | .noChoice _ => .noChoice memory

/-- Fixed alternative: preserve successes but restore the failing item's input
on any non-success, then skip the remaining suffix. -/
def rollbackFailingItem (memory : TreeMemory.State) :
    List TreeMemory.Provenance → TreeMemory.Result Unit
  | [] => .ok () memory
  | entry :: suffix =>
      match TreeMemory.release memory entry with
      | .ok () after => rollbackFailingItem after suffix
      | .ub diagnostic _ => .ub diagnostic memory
      | .unsupported reason _ => .unsupported reason memory
      | .noChoice _ => .noChoice memory

/-- Fixed alternative only: after the first UB, run the ordinary short-circuit
suffix fold from its partial residual. Keep the first UB diagnostic and the
suffix's actual final residual regardless of that suffix result constructor.
Pre-UB unsupported/noChoice propagate their actual result/residual unchanged. -/
def continueAfterErrorKeepFirst (memory : TreeMemory.State) :
    List TreeMemory.Provenance → TreeMemory.Result Unit
  | [] => .ok () memory
  | entry :: suffix =>
      match TreeMemory.release memory entry with
      | .ok () after => continueAfterErrorKeepFirst after suffix
      | .ub diagnostic after => .ub diagnostic (rResidual (rReleaseList after suffix))
      | .unsupported reason after => .unsupported reason after
      | .noChoice after => .noChoice after

theorem whole_rollback_actual :
    rollbackWholeOnError before registrations = .ub fault before := by
  simp only [rollbackWholeOnError, actual_fold]

theorem item_rollback_actual :
    rollbackFailingItem before registrations = .ub fault afterFirst := by
  simp only [registrations, rollbackFailingItem, first_release, middle_release]

theorem continue_actual :
    continueAfterErrorKeepFirst before registrations = .ub fault continued := by
  simp only [registrations, continueAfterErrorKeepFirst, first_release,
    middle_release, rReleaseList, standalone_third_release, rResidual]

theorem whole_rollback_observations :
    before.trees 0 = some active ∧ before.trees 1 = some middle ∧
    before.trees 2 = some active ∧ before.raw = failed.raw ∧
    before.currentFrame = failed.currentFrame := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem item_rollback_observations :
    afterFirst.trees 0 = some cleared ∧ afterFirst.trees 1 = some middle ∧
    afterFirst.trees 2 = some active ∧ afterFirst.raw = failed.raw ∧
    afterFirst.currentFrame = failed.currentFrame := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem continue_observations :
    continued.trees 0 = some cleared ∧ continued.trees 1 = some converted ∧
    continued.trees 2 = some cleared ∧ continued.raw = failed.raw ∧
    continued.currentFrame = failed.currentFrame := ⟨rfl, rfl, rfl, rfl, rfl⟩

private theorem active_ne_cleared : active ≠ cleared := by
  intro same
  have flag := congrArg (fun tree =>
    (TreeReference.findNode tree [0, 0]).map TreeReference.Node.protection) same
  change (some Protected.strong : Option Protected) = some Protected.no at flag
  cases flag

private theorem middle_ne_converted : middle ≠ converted := by
  intro same
  have query := congrArg TreeReference.kindsMatch same
  have original : TreeReference.kindsMatch middle = true :=
    TreeMemoryControls.live_failure_matching_scope.2.1
  have changed : TreeReference.kindsMatch converted = false :=
    TreeMemoryControls.live_failure_matching_scope.2.2
  rw [original, changed] at query
  cases query

theorem first_and_third_really_change : afterFirst ≠ before ∧ continued ≠ failed := by
  constructor
  · intro same
    have nodes : cleared = active :=
      Option.some.inj (congrArg (fun state : TreeMemory.State => state.trees 0) same)
    exact active_ne_cleared nodes.symm
  · intro same
    have nodes : cleared = active :=
      Option.some.inj (congrArg (fun state : TreeMemory.State => state.trees 2) same)
    exact active_ne_cleared nodes.symm

/-- The diagnostic is identical. Only complete residual memories distinguish
the real fold from each named alternative. -/
theorem whole_rollback_differs :
    rollbackWholeOnError before registrations ≠ rReleaseList before registrations := by
  rw [whole_rollback_actual, actual_fold]
  intro same
  have stateSame := (TreeMemory.Result.ub.inj same).2
  have nodes : active = cleared :=
    Option.some.inj (congrArg (fun state : TreeMemory.State => state.trees 0) stateSame)
  exact active_ne_cleared nodes

theorem item_rollback_differs :
    rollbackFailingItem before registrations ≠ rReleaseList before registrations := by
  rw [item_rollback_actual, actual_fold]
  intro same
  have stateSame := (TreeMemory.Result.ub.inj same).2
  have nodes : middle = converted :=
    Option.some.inj (congrArg (fun state : TreeMemory.State => state.trees 1) stateSame)
  exact middle_ne_converted nodes

theorem continue_differs :
    continueAfterErrorKeepFirst before registrations ≠ rReleaseList before registrations := by
  rw [continue_actual, actual_fold]
  intro same
  have stateSame := (TreeMemory.Result.ub.inj same).2
  exact first_and_third_really_change.2 stateSame

def fBefore : TreeFactoredMemory.State := TreeMemoryEncoding.encodeMemory before

theorem factored_input_width : TreeFactoredMemory.WellSized fBefore :=
  (TreeMemoryEncoding.wellSized_encode_iff before).1 before_width

/-- Actual F execution, with proof transport disclosed. Equality is through
full reification, not literal equality with an encoding of the R residual. -/
theorem factored_actual_fold :
    TreeFactoredMemory.translate (fReleaseList fBefore registrations) = .ub fault failed := by
  rw [← releaseList_agrees fBefore registrations factored_input_width]
  change rReleaseList (TreeFactoredMemory.reify (TreeMemoryEncoding.encodeMemory before))
    registrations = .ub fault failed
  rw [TreeMemoryEncoding.reify_encode_memory]
  exact actual_fold

theorem actual_factored_failure_witness :
    ∃ changed, fReleaseList fBefore registrations = .ub fault changed ∧
      TreeFactoredMemory.reify changed = failed ∧
      TreeFactoredMemory.WellSized changed ∧
      changed.raw = before.raw ∧ changed.currentFrame = before.currentFrame := by
  have observed := factored_actual_fold
  have preserved := fReleaseList_preserves fBefore registrations factored_input_width
  cases actual : fReleaseList fBefore registrations with
  | ok value changed =>
    simp only [actual, TreeFactoredMemory.translate] at observed
    cases observed
  | unsupported reason changed =>
    simp only [actual, TreeFactoredMemory.translate] at observed
    cases observed
  | noChoice changed =>
    simp only [actual, TreeFactoredMemory.translate] at observed
    cases observed
  | ub diagnostic changed =>
    simp only [actual, TreeFactoredMemory.translate] at observed
    obtain ⟨sameFault, represented⟩ := TreeMemory.Result.ub.inj observed
    subst diagnostic
    refine ⟨changed, rfl, represented, ?_, ?_, ?_⟩
    · simpa only [actual, TreeMemoryDomain.ResultWellSized,
        TreeFactoredMemory.Result.residual] using preserved
    · exact congrArg TreeMemory.State.raw represented
    · exact congrArg TreeMemory.State.currentFrame represented

#print axioms first_release
#print axioms middle_release
#print axioms standalone_third_release
#print axioms actual_fold
#print axioms actual_end_call
#print axioms before_width
#print axioms failed_width
#print axioms initial_matching
#print axioms failed_not_matching
#print axioms real_observations
#print axioms whole_rollback_actual
#print axioms item_rollback_actual
#print axioms continue_actual
#print axioms whole_rollback_observations
#print axioms item_rollback_observations
#print axioms continue_observations
#print axioms first_and_third_really_change
#print axioms whole_rollback_differs
#print axioms item_rollback_differs
#print axioms continue_differs
#print axioms factored_input_width
#print axioms factored_actual_fold
#print axioms actual_factored_failure_witness

end AnnealResearch.TreeEndCallFailureControls
