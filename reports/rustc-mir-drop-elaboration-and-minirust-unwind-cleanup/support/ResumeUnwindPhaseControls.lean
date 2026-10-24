import AnnealResearch.ResumeUnwindPhase
import AnnealResearch.TreeEndCallFailureControls

/-!
Owned, assembled shape-only controls. No complete source construction history
is claimed for either phase product. The same reference trees from the earlier
three-ID end-call controls are reused, with a distinct fourth stack allocation
and an empty recorded memory frame. Primary observers are Config memory/stack/PC.
Ghost detached frames are final snapshots only. No NoUB or source-adequacy claim.
-/

namespace AnnealResearch.ResumeUnwindPhaseControls

open ResumeUnwindPhase TreePermissions

def active : TreeReference.Node := TreeEndCallFailureControls.active
def cleared : TreeReference.Node := TreeEndCallFailureControls.cleared
def middle : TreeReference.Node := TreeEndCallFailureControls.middle
def converted : TreeReference.Node := TreeEndCallFailureControls.converted
def fault : TreeMemory.Fault := TreeEndCallFailureControls.fault
def localTree : TreeReference.Node := .mk [.unprot .unique] .no []

def blockAt (address : Nat) : MiniRustReference.Allocation :=
  TreeEndCallFailureControls.blockAt address

def stackBlock (live : Bool) : MiniRustReference.Allocation :=
  { base := 64
    size := 1
    align := 1
    kind := .stack
    live := live
    data := fun _ => .uninit }

/-- Complete independently written raw map; no result/default extraction. -/
def raw (localLive : Bool) : MiniRustReference.State :=
  { next := 4
    allocations := fun id =>
      if id = 0 then some (blockAt 16)
      else if id = 1 then some (blockAt 32)
      else if id = 2 then some (blockAt 48)
      else if id = 3 then some (stackBlock localLive)
      else none }

def memory (first second third : TreeReference.Node) (localLive : Bool) : TreeMemory.State :=
  { raw := raw localLive
    trees := fun id =>
      if id = 0 then some first
      else if id = 1 then some second
      else if id = 2 then some third
      else if id = 3 then some localTree
      else none
    currentFrame := [] }

def initialMemory : TreeMemory.State := memory active middle active true
def freedMemory : TreeMemory.State := memory active middle active false
def positiveMemory : TreeMemory.State := memory cleared middle active false
def failedMemory : TreeMemory.State := memory cleared converted active false
def thirdReleasedMemory : TreeMemory.State := memory cleared converted cleared false

def localPointer : TreeMemory.Pointer := ⟨64, some (3, [])⟩
def slot : Local := ⟨9, localPointer, 1, 1⟩
def emptyExtra : TreeEndCall.SuppliedFrameExtra := ⟨[]⟩
def positiveExtra : TreeEndCall.SuppliedFrameExtra := ⟨[(0, [0, 0])]⟩
def failureExtra : TreeEndCall.SuppliedFrameExtra :=
  ⟨TreeEndCallFailureControls.registrations⟩

def caller : Frame Nat := ⟨⟨5, 7⟩, none, emptyExtra, .bottom, 111⟩
def callerJumped : Frame Nat := ⟨⟨17, 0⟩, none, emptyExtra, .bottom, 111⟩
def callee (extra : TreeEndCall.SuppliedFrameExtra) (target : Option Nat) : Frame Nat :=
  ⟨⟨11, 2⟩, some slot, extra, .backToCaller target, 222⟩
def departed (extra : TreeEndCall.SuppliedFrameExtra) (target : Option Nat) : Frame Nat :=
  ⟨⟨11, 2⟩, none, extra, .backToCaller target, 222⟩

def chosen (extra : TreeEndCall.SuppliedFrameExtra) (target : Option Nat) : Selection Nat :=
  ⟨caller, callee extra target, slot, target⟩

def initial {C : Type} (extra : TreeEndCall.SuppliedFrameExtra) (target : Option Nat)
    (context : C) : RConfig Nat C :=
  ⟨initialMemory, .push (.push .empty caller) (callee extra target), context⟩

def afterError {C : Type} (memory : TreeMemory.State) (context : C) : RConfig Nat C :=
  ⟨memory, .push .empty caller, context⟩
def afterJump {C : Type} (memory : TreeMemory.State) (context : C) : RConfig Nat C :=
  ⟨memory, .push .empty callerJumped, context⟩

/-- These expected snapshots are explicit records, not runs or observers of runs. -/
def positiveExpected {C : Type} (context : C) : Snapshot TreeMemory.State Nat C :=
  ⟨afterJump positiveMemory context, departed positiveExtra (some 17)⟩
def missingExpected {C : Type} (context : C) : Snapshot TreeMemory.State Nat C :=
  ⟨afterError positiveMemory context, departed positiveExtra none⟩
def failureExpected {C : Type} (context : C) : Snapshot TreeMemory.State Nat C :=
  ⟨afterError failedMemory context, departed failureExtra (some 17)⟩
def wrongExpected {C : Type} (context : C) : Snapshot TreeMemory.State Nat C :=
  ⟨afterJump freedMemory context, departed positiveExtra (some 17)⟩

private theorem set_zero (a b c replacement : TreeReference.Node) (live : Bool) :
    TreeMemory.setTree (memory a b c live) 0 replacement = memory replacement b c live := by
  unfold TreeMemory.setTree memory
  congr 1
  funext id
  by_cases zero : id = 0 <;> simp [zero]

private theorem set_one (a b c replacement : TreeReference.Node) (live : Bool) :
    TreeMemory.setTree (memory a b c live) 1 replacement = memory a replacement c live := by
  unfold TreeMemory.setTree memory
  congr 1
  funext id
  by_cases zero : id = 0
  · subst id; rfl
  · by_cases one : id = 1 <;> simp [zero, one]

private theorem set_two (a b c replacement : TreeReference.Node) (live : Bool) :
    TreeMemory.setTree (memory a b c live) 2 replacement = memory a b replacement live := by
  unfold TreeMemory.setTree memory
  congr 1
  funext id
  by_cases zero : id = 0
  · subst id; rfl
  · by_cases one : id = 1
    · subst id; rfl
    · by_cases two : id = 2 <;> simp [zero, one, two]

private theorem set_local_tree (a b c : TreeReference.Node) (live : Bool) :
    TreeMemory.setTree (memory a b c live) 3 localTree = memory a b c live := by
  unfold TreeMemory.setTree memory
  congr 1
  funext id
  by_cases three : id = 3
  · subst id; rfl
  · simp [three]

private theorem replace_local :
    MiniRustReference.replace (raw true) 3 (stackBlock false) = raw false := by
  unfold MiniRustReference.replace raw
  congr 1
  funext id
  by_cases zero : id = 0
  · subst id; rfl
  · by_cases one : id = 1
    · subst id; rfl
    · by_cases two : id = 2
      · subst id; rfl
      · by_cases three : id = 3 <;> simp [zero, one, two, three]

private theorem raw_free :
    MiniRustReference.free (raw true) localPointer.basic .stack 1 1 = .ok (raw false) := by
  have computed : MiniRustReference.free (raw true) localPointer.basic .stack 1 1 =
      .ok (MiniRustReference.replace (raw true) 3 (stackBlock false)) := by
    simp [MiniRustReference.free, TreeMemory.Pointer.basic, localPointer, raw, stackBlock]
  rw [computed, replace_local]

attribute [local simp] TreeReference.modifyAt TreeReference.replaceNth
  TreeReference.unprotectAt TreeReference.unprotectPermissions
  TreeReference.releaseTraverse TreeReference.releaseCore TreeReference.releaseChildren
  TreeReference.applyAccesses TreeReference.arraysSized TreeReference.childrenSized
  TreeReference.pathPresent TreeReference.findNode TreeReference.nodeRelation
  TreeReference.childPath TreeReference.Node.permissions TreeReference.Node.children
  TreeReference.Node.protection TreeReference.Result.mapState TreeReference.Result.bind
  TreeReference.access TreeReference.accessCore TreeReference.accessChildren
  TreeReference.transitionRange TreeReference.transitionPrefix
  TreeReference.containsStrong TreeReference.childrenContainStrong
  Permission.unprotect PPermission.unprotect Permission.transition
  Permission.preventsDeallocation PPermission.preventsDeallocation
  UPermission.transition UPermission.localRead UPermission.localWrite
  UPermission.foreignRead UPermission.foreignWrite UPermission.preventsDeallocation Protected.yes

private theorem free_root (before : TreeMemory.State) (afterRaw : MiniRustReference.State)
    (freed : MiniRustReference.free before.raw localPointer.basic .stack 1 1 = .ok afterRaw)
    (present : before.trees 3 = some localTree) :
    TreeMemory.deallocate before localPointer .stack 1 1 =
      .ok () { TreeMemory.setTree before 3 localTree with raw := afterRaw } := by
  simp only [TreeMemory.deallocate, TreeMemory.freeWith, freed]
  simp only [TreeMemory.hookTarget, localPointer, present, Option.map_some]
  simp [localTree]

theorem actual_local_deallocation :
    TreeMemory.deallocate initialMemory localPointer .stack 1 1 = .ok () freedMemory := by
  have actual := free_root initialMemory (raw false) raw_free rfl
  have treeUnchanged : TreeMemory.setTree initialMemory 3 localTree = initialMemory :=
    set_local_tree active middle active true
  have expected : { TreeMemory.setTree initialMemory 3 localTree with raw := raw false } =
      freedMemory := by
    rw [treeUnchanged]
    rfl
  simpa only [expected] using actual

private theorem good_release_at (before : TreeMemory.State) (id : Nat)
    (allocation : MiniRustReference.Allocation)
    (allocated : before.raw.allocations id = some allocation)
    (live : allocation.live = true) (present : before.trees id = some active) :
    TreeMemory.release before (id, [0, 0]) =
      .ok () (TreeMemory.setTree before id cleared) := by
  simp [TreeMemory.release, allocated, live, present, active, cleared,
    TreeEndCallFailureControls.active, TreeEndCallFailureControls.cleared,
    TreeMemoryControls.treeWrite, TreeMemoryControls.treeReleased]

private theorem bad_release_at (before : TreeMemory.State) (id : Nat)
    (allocation : MiniRustReference.Allocation)
    (allocated : before.raw.allocations id = some allocation)
    (live : allocation.live = true) (present : before.trees id = some middle) :
    TreeMemory.release before (id, [0]) =
      .ub fault (TreeMemory.setTree before id converted) := by
  simp [TreeMemory.release, allocated, live, present, middle, converted, fault,
    TreeEndCallFailureControls.middle, TreeEndCallFailureControls.converted,
    TreeEndCallFailureControls.fault, TreeMemoryControls.liveFailureTree,
    TreeMemoryControls.liveFailureConverted]

theorem actual_first_release : TreeMemory.release freedMemory (0, [0, 0]) =
    .ok () positiveMemory := by
  have actual := good_release_at freedMemory 0 (blockAt 16) rfl rfl rfl
  simpa only [freedMemory, positiveMemory, set_zero] using actual

theorem actual_middle_release : TreeMemory.release positiveMemory (1, [0]) =
    .ub fault failedMemory := by
  have actual := bad_release_at positiveMemory 1 (blockAt 32) rfl rfl rfl
  simpa only [positiveMemory, failedMemory, set_one] using actual

/-- A separate meaningful suffix control, not execution after the real UB. -/
theorem standalone_third_release : TreeMemory.release failedMemory (2, [0, 0]) =
    .ok () thirdReleasedMemory := by
  have actual := good_release_at failedMemory 2 (blockAt 48) rfl rfl rfl
  simpa only [failedMemory, thirdReleasedMemory, set_two] using actual

theorem actual_positive_hook : TreeEndCall.rEndCall freedMemory positiveExtra =
    .ok () positiveMemory := by
  simp only [TreeEndCall.rEndCall, positiveExtra, TreeEndCall.rReleaseList, actual_first_release]

theorem actual_failure_hook : TreeEndCall.rEndCall freedMemory failureExtra =
    .ub fault failedMemory := by
  simp only [TreeEndCall.rEndCall, failureExtra, TreeEndCallFailureControls.registrations,
    TreeEndCall.rReleaseList, actual_first_release, actual_middle_release]

variable {P C : Type}

theorem actual_positive (context : C) :
    runR (initial positiveExtra (some 17) context) = some (.ok (positiveExpected context)) := by
  exact runR_success (initial positiveExtra (some 17) context) (chosen positiveExtra (some 17))
    rfl freedMemory positiveMemory 17 actual_local_deallocation actual_positive_hook rfl

theorem actual_missing_continuation (context : C) :
    runR (initial positiveExtra none context) =
      some (.ub .missingContinuation (missingExpected context)) := by
  exact runR_missingContinuation (initial positiveExtra none context) (chosen positiveExtra none)
    rfl freedMemory positiveMemory actual_local_deallocation actual_positive_hook rfl

theorem actual_partial_failure (context : C) :
    runR (initial failureExtra (some 17) context) =
      some (.ub (.memory fault) (failureExpected context)) := by
  exact runR_endCall_ub (initial failureExtra (some 17) context) (chosen failureExtra (some 17))
    rfl freedMemory failedMemory fault actual_local_deallocation actual_failure_hook

theorem positive_observations (context : C) :
    (positiveExpected context).config.stack = .push .empty callerJumped ∧
    callerJumped.pc = ⟨17, 0⟩ ∧ caller.pc = ⟨5, 7⟩ ∧
    caller.extra.protectors = [] ∧ positiveExtra.protectors = [(0, [0, 0])] ∧
    positiveMemory.currentFrame = [] ∧
    positiveMemory.raw.allocations 3 = some (stackBlock false) ∧
    positiveMemory.trees 0 = some cleared ∧ positiveMemory.trees 1 = some middle ∧
    positiveMemory.trees 2 = some active ∧
    (positiveExpected context).config.context = context := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem failure_observations (context : C) :
    (failureExpected context).config.stack = .push .empty caller ∧
    (failureExpected context).config.context = context ∧
    failedMemory.raw.allocations 3 = some (stackBlock false) ∧
    failedMemory.raw.allocations 1 = some (blockAt 32) ∧
    (blockAt 32).live = true ∧ (stackBlock false).live = false ∧
    failedMemory.trees 0 = some cleared ∧ failedMemory.trees 1 = some converted ∧
    failedMemory.trees 2 = some active ∧ failedMemory.currentFrame = [] ∧
    localPointer.provenance = some (3, []) ∧ (3 : Nat) ≠ 1 ∧ (64 : Nat) ≠ 32 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩ <;> decide

/-- Fixed wrong-list alternative: actual deallocation and hook, shared phase rules.
The actual callee is retained in the ghost; only the supplied hook list differs. -/
def wrongList (extraFor : TreeMemory.State → Selection P → TreeEndCall.SuppliedFrameExtra)
    (before : RConfig P C) : Option (RResult P C) :=
  (pick before.stack).map fun selected =>
    match TreeMemory.deallocate before.memory selected.slot.pointer .stack
        selected.slot.size selected.slot.align with
    | .ok () freed =>
        match TreeEndCall.rEndCall freed (extraFor freed selected) with
        | .ok () released => finish before selected released
        | .ub diagnostic after => .ub (.memory diagnostic) (stopped before selected after)
        | .unsupported reason after => .unsupported reason (stopped before selected after)
        | .noChoice after => .noChoice (stopped before selected after)
    | .ub diagnostic after => .ub (.memory diagnostic) (stopped before selected after)
    | .unsupported reason after => .unsupported reason (stopped before selected after)
    | .noChoice after => .noChoice (stopped before selected after)

def callerExtra (_memory : TreeMemory.State) (selected : Selection P) := selected.caller.extra
def recordedExtra (memory : TreeMemory.State) (_selected : Selection P) :
    TreeEndCall.SuppliedFrameExtra := ⟨memory.currentFrame⟩

theorem wrong_caller_list_actual (context : C) :
    wrongList callerExtra (initial positiveExtra (some 17) context) =
      some (.ok (wrongExpected context)) := by
  simp only [wrongList, initial, pick, callee, slot, Option.map_some,
    actual_local_deallocation, callerExtra, caller, TreeEndCall.rEndCall,
    emptyExtra, TreeEndCall.rReleaseList] <;> rfl

theorem wrong_recorded_list_actual (context : C) :
    wrongList recordedExtra (initial positiveExtra (some 17) context) =
      some (.ok (wrongExpected context)) := by
  simp only [wrongList, initial, pick, callee, slot, Option.map_some,
    actual_local_deallocation, recordedExtra, TreeEndCall.rEndCall,
    freedMemory, memory, TreeEndCall.rReleaseList] <;> rfl

private theorem active_ne_cleared : active ≠ cleared := by
  intro same
  have flag := congrArg (fun tree =>
    (TreeReference.findNode tree [0, 0]).map TreeReference.Node.protection) same
  change (some Protected.strong : Option Protected) = some Protected.no at flag
  cases flag

theorem wrong_list_value_discriminator (context : C) :
    (positiveExpected context).config.stack = (wrongExpected context).config.stack ∧
    (positiveExpected context).config.context = (wrongExpected context).config.context ∧
    (positiveExpected context).detached = (wrongExpected context).detached ∧
    (positiveExpected context).config.memory.trees 0 ≠
      (wrongExpected context).config.memory.trees 0 := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro same
  have trees : cleared = active := Option.some.inj same
  exact active_ne_cleared trees.symm

/-- Explicit delayed-pop residual; not a fallback extraction from a run. -/
def lateStopped (before : RConfig P C) (selected : Selection P) (memory : TreeMemory.State) :
    Snapshot TreeMemory.State P C :=
  ⟨⟨memory, before.stack, before.context⟩, removeLocal selected.callee⟩

/-- Late-pop alternative executes actual primitives. Cleanup failure keeps the
original stored stack; cleanup success uses finish, popping even for absent target. -/
def latePop (before : RConfig P C) : Option (RResult P C) :=
  (pick before.stack).map fun selected =>
    match TreeMemory.deallocate before.memory selected.slot.pointer .stack
        selected.slot.size selected.slot.align with
    | .ok () freed =>
        match TreeEndCall.rEndCall freed selected.callee.extra with
        | .ok () released => finish before selected released
        | .ub diagnostic after => .ub (.memory diagnostic) (lateStopped before selected after)
        | .unsupported reason after => .unsupported reason (lateStopped before selected after)
        | .noChoice after => .noChoice (lateStopped before selected after)
    | .ub diagnostic after => .ub (.memory diagnostic) (lateStopped before selected after)
    | .unsupported reason after => .unsupported reason (lateStopped before selected after)
    | .noChoice after => .noChoice (lateStopped before selected after)

/-- Disclosed reply policy over actual runR: restore Config on each selected
non-success while retaining status/diagnostic and its separate final ghost. -/
def rollbackWholePhaseOnError (before : RConfig P C) : Option (RResult P C) :=
  match runR before with
  | none => none
  | some (.ok after) => some (.ok after)
  | some (.ub diagnostic after) => some (.ub diagnostic ⟨before, after.detached⟩)
  | some (.unsupported reason after) => some (.unsupported reason ⟨before, after.detached⟩)
  | some (.noChoice after) => some (.noChoice ⟨before, after.detached⟩)

def lateExpected (context : C) : Snapshot TreeMemory.State Nat C :=
  ⟨⟨failedMemory, (initial failureExtra (some 17) context).stack, context⟩,
    departed failureExtra (some 17)⟩
def rollbackExpected (context : C) : Snapshot TreeMemory.State Nat C :=
  ⟨initial failureExtra (some 17) context, departed failureExtra (some 17)⟩

theorem late_pop_actual (context : C) :
    latePop (initial failureExtra (some 17) context) =
      some (.ub (.memory fault) (lateExpected context)) := by
  simp only [latePop, initial, pick, callee, slot, Option.map_some,
    actual_local_deallocation, actual_failure_hook] <;> rfl

theorem late_pop_missing_continuation (context : C) :
    latePop (initial positiveExtra none context) =
      some (.ub .missingContinuation (missingExpected context)) := by
  simp only [latePop, initial, pick, callee, slot, Option.map_some,
    actual_local_deallocation, actual_positive_hook] <;> rfl

theorem whole_rollback_actual (context : C) :
    rollbackWholePhaseOnError (initial failureExtra (some 17) context) =
      some (.ub (.memory fault) (rollbackExpected context)) := by
  simp only [rollbackWholePhaseOnError, actual_partial_failure] <;> rfl

theorem late_pop_config_differs (context : C) :
    (failureExpected context).config ≠ (lateExpected context).config := by
  intro same
  have sizes := congrArg (fun config : RConfig Nat C => (view config.stack).length) same
  change (1 : Nat) = 2 at sizes
  omega

theorem rollback_memory_differs (context : C) :
    (failureExpected context).config.memory ≠ (rollbackExpected context).config.memory := by
  intro same
  have life := congrArg (fun state : TreeMemory.State =>
    (state.raw.allocations 3).map MiniRustReference.Allocation.live) same
  change (some false : Option Bool) = some true at life
  cases life

theorem primary_mutants_same_fault_different_configs (context : C) :
    (lateExpected context).config.memory = (failureExpected context).config.memory ∧
    (lateExpected context).config.stack = (initial failureExtra (some 17) context).stack ∧
    (rollbackExpected context).config = initial failureExtra (some 17) context ∧
    (failureExpected context).config ≠ (lateExpected context).config ∧
    (failureExpected context).config ≠ (rollbackExpected context).config := by
  refine ⟨rfl, rfl, rfl, late_pop_config_differs context, ?_⟩
  intro same
  exact rollback_memory_differs context (congrArg Config.memory same)

theorem mutant_results_differ (context : C) :
    latePop (initial failureExtra (some 17) context) ≠
        runR (initial failureExtra (some 17) context) ∧
      rollbackWholePhaseOnError (initial failureExtra (some 17) context) ≠
        runR (initial failureExtra (some 17) context) := by
  constructor
  · rw [late_pop_actual, actual_partial_failure]
    intro same
    have snapshots : lateExpected context = failureExpected context :=
      (PhaseResult.ub.inj (Option.some.inj same)).2
    exact late_pop_config_differs context (congrArg Snapshot.config snapshots.symm)
  · rw [whole_rollback_actual, actual_partial_failure]
    intro same
    have snapshots : rollbackExpected context = failureExpected context :=
      (PhaseResult.ub.inj (Option.some.inj same)).2
    exact rollback_memory_differs context
      (congrArg (fun after => after.config.memory) snapshots.symm)

private theorem memory_width (a b c : TreeReference.Node) (live : Bool)
    (aw : TreeReference.arraysSized a 1 = true)
    (bw : TreeReference.arraysSized b 1 = true)
    (cw : TreeReference.arraysSized c 1 = true) :
    TreeMemoryEncoding.RWellSized (memory a b c live) := by
  intro id allocation tree allocated present
  by_cases zero : id = 0
  · subst id
    have sameAllocation : blockAt 16 = allocation := Option.some.inj allocated
    have sameTree : a = tree := Option.some.inj present
    subst allocation; subst tree
    exact aw
  · by_cases one : id = 1
    · subst id
      have sameAllocation : blockAt 32 = allocation := Option.some.inj allocated
      have sameTree : b = tree := Option.some.inj present
      subst allocation; subst tree
      exact bw
    · by_cases two : id = 2
      · subst id
        have sameAllocation : blockAt 48 = allocation := Option.some.inj allocated
        have sameTree : c = tree := Option.some.inj present
        subst allocation; subst tree
        exact cw
      · by_cases three : id = 3
        · subst id
          have sameAllocation : stackBlock live = allocation := Option.some.inj allocated
          have sameTree : localTree = tree := Option.some.inj present
          subst allocation; subst tree
          simp [localTree, stackBlock]
        · simp [memory, raw, zero, one, two, three] at allocated

theorem initial_width : TreeMemoryEncoding.RWellSized initialMemory := by
  apply memory_width
  all_goals simp [active, middle, TreeEndCallFailureControls.active,
    TreeEndCallFailureControls.middle, TreeMemoryControls.treeWrite,
    TreeMemoryControls.liveFailureTree]

def encodeConfig (before : RConfig P C) : FConfig P C :=
  ⟨TreeMemoryEncoding.encodeMemory before.memory, before.stack, before.context⟩

theorem reify_encoded_config (before : RConfig P C) :
    reifyConfig (encodeConfig before) = before := by
  cases before with
  | mk memory stack context =>
      change Config.mk (TreeFactoredMemory.reify (TreeMemoryEncoding.encodeMemory memory))
        stack context = Config.mk memory stack context
      rw [TreeMemoryEncoding.reify_encode_memory]

private theorem lift_ok (before : RConfig P C) (expected : Snapshot TreeMemory.State P C)
    (width : TreeMemoryEncoding.RWellSized before.memory)
    (observed : runR before = some (.ok expected)) :
    ∃ actual, runF (encodeConfig before) = some (.ok actual) ∧
      mapSnapshot TreeFactoredMemory.reify actual = expected ∧
      TreeFactoredMemory.WellSized actual.config.memory := by
  have domain : TreeFactoredMemory.WellSized (encodeConfig before).memory :=
    (TreeMemoryEncoding.wellSized_encode_iff before.memory).mp width
  have agreement := run_agrees (encodeConfig before) domain
  rw [reify_encoded_config, observed] at agreement
  cases executed : runF (encodeConfig before) with
  | none => simp [executed] at agreement
  | some result =>
      cases result with
      | ub diagnostic after => simp [executed, translate, mapResult] at agreement
      | unsupported reason after => simp [executed, translate, mapResult] at agreement
      | noChoice after => simp [executed, translate, mapResult] at agreement
      | ok after =>
          have same : (PhaseResult.ok expected : RResult P C) =
              .ok (mapSnapshot TreeFactoredMemory.reify after) := by
            apply Option.some.inj
            simpa only [executed, Option.map_some, translate, mapResult] using agreement
          refine ⟨after, rfl, (PhaseResult.ok.inj same).symm, ?_⟩
          simpa only [ResultSized, PhaseResult.residual] using
            runF_preserves (encodeConfig before) (.ok after) domain executed

private theorem lift_ub (before : RConfig P C) (expected : Snapshot TreeMemory.State P C)
    (diagnostic : PhaseFault) (width : TreeMemoryEncoding.RWellSized before.memory)
    (observed : runR before = some (.ub diagnostic expected)) :
    ∃ actual, runF (encodeConfig before) = some (.ub diagnostic actual) ∧
      mapSnapshot TreeFactoredMemory.reify actual = expected ∧
      TreeFactoredMemory.WellSized actual.config.memory := by
  have domain : TreeFactoredMemory.WellSized (encodeConfig before).memory :=
    (TreeMemoryEncoding.wellSized_encode_iff before.memory).mp width
  have agreement := run_agrees (encodeConfig before) domain
  rw [reify_encoded_config, observed] at agreement
  cases executed : runF (encodeConfig before) with
  | none => simp [executed] at agreement
  | some result =>
      cases result with
      | ok after => simp [executed, translate, mapResult] at agreement
      | unsupported reason after => simp [executed, translate, mapResult] at agreement
      | noChoice after => simp [executed, translate, mapResult] at agreement
      | ub other after =>
          have same : (PhaseResult.ub diagnostic expected : RResult P C) =
              .ub other (mapSnapshot TreeFactoredMemory.reify after) := by
            apply Option.some.inj
            simpa only [executed, Option.map_some, translate, mapResult] using agreement
          have faults : diagnostic = other := (PhaseResult.ub.inj same).1
          have snapshots : expected = mapSnapshot TreeFactoredMemory.reify after :=
            (PhaseResult.ub.inj same).2
          subst other
          refine ⟨after, rfl, snapshots.symm, ?_⟩
          simpa only [ResultSized, PhaseResult.residual] using
            runF_preserves (encodeConfig before) (.ub diagnostic after) domain executed

theorem actual_factored_positive (context : C) :
    ∃ actual, runF (encodeConfig (initial positiveExtra (some 17) context)) = some (.ok actual) ∧
      mapSnapshot TreeFactoredMemory.reify actual = positiveExpected context ∧
      TreeFactoredMemory.WellSized actual.config.memory :=
  lift_ok _ _ initial_width (actual_positive context)

theorem actual_factored_failure (context : C) :
    ∃ actual, runF (encodeConfig (initial failureExtra (some 17) context)) =
        some (.ub (.memory fault) actual) ∧
      mapSnapshot TreeFactoredMemory.reify actual = failureExpected context ∧
      TreeFactoredMemory.WellSized actual.config.memory :=
  lift_ub _ _ (.memory fault) initial_width (actual_partial_failure context)

#print axioms actual_local_deallocation
#print axioms actual_first_release
#print axioms actual_middle_release
#print axioms standalone_third_release
#print axioms actual_positive_hook
#print axioms actual_failure_hook
#print axioms actual_positive
#print axioms actual_missing_continuation
#print axioms actual_partial_failure
#print axioms positive_observations
#print axioms failure_observations
#print axioms wrong_caller_list_actual
#print axioms wrong_recorded_list_actual
#print axioms wrong_list_value_discriminator
#print axioms late_pop_actual
#print axioms late_pop_missing_continuation
#print axioms whole_rollback_actual
#print axioms late_pop_config_differs
#print axioms rollback_memory_differs
#print axioms primary_mutants_same_fault_different_configs
#print axioms mutant_results_differ
#print axioms initial_width
#print axioms reify_encoded_config
#print axioms actual_factored_positive
#print axioms actual_factored_failure

end AnnealResearch.ResumeUnwindPhaseControls
