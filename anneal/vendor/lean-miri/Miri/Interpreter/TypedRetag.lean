import Miri.Interpreter.MachineHooks
import Miri.TreeBorrows.FreezeMap

/-! Stateful source driver for tree_borrows/mod.rs NewPermission::new,
tb_retag_ptr_value, tb_retag_place and tb_reborrow. Compiler and pointer leaves
are required effects, rather than precomputed request outcomes. -/
namespace Miri.Interpreter.TypedRetag
open Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures
open Miri.TreeBorrows Miri.TreeBorrows.RetagPolicy
open MachineHooks (State M currentFrame setCurrentFrame)

structure Hooks (K User : Type) where
  typeShape : TyId → M K User RetagPipeline.RetagTypeShape
  builtinDeref : TyId → M K User TyId
  referencePointee : TyId → M K User (TyId × MIR.Mutability)
  isUnpin : TyId → M K User Bool
  isUnsafeUnpin : TyId → M K User Bool
  typeIsFreeze : TyId → M K User Bool
  implicitWrites : M K User Bool
  rustcNoWritable : DefId → M K User Bool
  preciseInteriorMut : M K User Bool
  immPtrToMPlace : RvalueImmTy Provenance → M K User (MPlaceTy Provenance)
  sizeAndAlign : MPlaceTy Provenance → M K User (Option (Size × Align))
  checkPtrAccess : Pointer (Option Provenance) → Size → M K User Unit
  resolveAllocation : Pointer (Option Provenance) → M K User (Option RetagPipeline.ResolvedLocation)
  /-- Diagnostic-only creation logging, called on every reborrow path. A hook
  must retain the source tracked-tag guard before any diagnostic type query. -/
  logCreation : MPlaceTy Provenance → Size → NewPermission → BorTag →
    Option RetagPipeline.ResolvedLocation → M K User Unit
  freeze : FreezeVisitor.Hooks Provenance (State K User)
  ensureTreeExtra : AllocId → M K User Unit
  reconstruct : RvalueImmTy Provenance → MPlaceTy Provenance → M K User (RvalueImmTy Provenance)
  writeUninit : MPlaceTy Provenance → M K User Unit

private def checked (operation : String) (value : Except E A) [Repr E] : M K User A :=
  match value with
  | .ok value => pure value
  | .error error => throw (.invalidProgram s!"{operation}: {reprStr error}")

/-- Compiler queries occur before the pinning early return, and the attribute
lookup is short-circuited by FnEntry and the implicit-writes setting. -/
def newPermission (h : Hooks K User) (pointee : TyId) (kind : ReferenceKind)
    (mode : RetagMode) : M K User (Option NewPermission) := do
  if mode == .None then return none
  let unpin ← h.isUnpin pointee
  let unsafeUnpin ← if unpin then h.isUnsafeUnpin pointee else pure false
  let freeze ← h.typeIsFreeze pointee
  let mut implicitWrites := false
  let mut noWritable := false
  if mode == .FnEntry then
    implicitWrites ← h.implicitWrites
    let defId := (← currentFrame).functionInstance.defId
    if implicitWrites then noWritable ← h.rustcNoWritable defId
  return create ⟨unpin, unsafeUnpin, freeze⟩ kind mode ⟨implicitWrites, noWritable⟩

private def insidePermissions (h : Hooks K User) (budget : Nat)
    (place : MPlaceTy Provenance) (size : Size) (policy : NewPermission) :
    M K User (DedupRangeMap Tree.LocationState) := do
  if !(← h.preciseInteriorMut) then
    let frozen ← h.typeIsFreeze place.layout.ty
    return DedupRangeMap.new size (← checked "initial location" (initialLocationState policy frozen))
  let initial := DedupRangeMap.new size (Tree.LocationState.newAccessed .Disabled .None)
  FreezeMap.visit h.freeze budget place size initial fun range frozen => do
    let location ← match initialLocationState policy frozen with
      | .ok state => pure state
      | .error error => throw (.invalidProgram s!"initial location: {reprStr error}")
    let result := (← get).modifyRange range.start range.size (fun _ _ => location)
    set result.state
    match result.outcome with
    | .ok () => pure ()
    | .error error => throw (.invalidProgram s!"freeze permission range: {reprStr error}")

private def tracker : M K User MachineHooks.BorrowState := do
  match (← get).machine.borrowTracker with
  | some value => return value
  | none => throw (.invalidProgram "Tree Borrows called while disabled")

private def updateTree [DecidableEq K] (allocId : AllocId) (tree : BorrowTree) : M K User Unit := do
  let state ← get
  let some entry := state.machine.memory.live.find? (fun entry => entry.1 == allocId)
    | throw (.invalidProgram "Tree Borrows allocation extra unavailable")
  let memory ← checked "update allocation tree"
    (state.machine.memory.setLiveAllocation allocId (entry.2.allocation.setExtra tree))
  set { state with machine := { state.machine with memory } }

private def getTree (allocId : AllocId) : M K User BorrowTree := do
  let some entry := (← get).machine.memory.live.find? (fun entry => entry.1 == allocId)
    | throw (.invalidProgram "Tree Borrows allocation extra unavailable")
  return entry.2.allocation.extra

private def accessError (status : BorrowTree.BorrowTreeAccessStatus) : StepError :=
  match status with
  | .AccessFailure _ (.TransitionError ..)
  | .WildcardFailure _ (.TransitionError ..)
  | .WildcardFailure _ (.NoValidExposedReferences ..) =>
    .undefinedBehavior s!"Tree Borrows: {reprStr status}"
  | _ => .invalidProgram s!"Tree Borrows invariant: {reprStr status}"

/-- Actual per-segment memory/TB/race transitions, including partially modified
parent trees on failure. The visitor runs after protector registration and
allocation-kind lookup, before get_alloc_extra and every parent access. -/
def reborrow [DecidableEq K] (h : Hooks K User) (budget : Nat)
    (place : MPlaceTy Provenance) (size : Size) (policy : NewPermission) (tag : BorTag) :
    M K User (Option Provenance) := do
  h.checkPtrAccess place.mplace.ptr size
  let location ← h.resolveAllocation place.mplace.ptr
  match location with
  | none =>
    if size.bytes != 0 then throw (.invalidProgram "nonzero reborrow without allocation")
    h.logCreation place size policy tag none
    return place.mplace.ptr.provenance
  | some location =>
    h.logCreation place size policy tag (some location)
    if let some protection := policy.protector then
      let frame ← currentFrame
      let some borrowFrame := frame.extra.borrowTracker
        | throw (.invalidProgram "borrow frame missing")
      let old ← tracker
      let (global, borrowFrame) := old.global.addProtector borrowFrame location.allocId tag protection
      modify fun state => { state with machine := { state.machine with
        borrowTracker := some { old with global } } }
      setCurrentFrame { frame with extra := { frame.extra with borrowTracker := some borrowFrame } }
    let info ← checked "allocation kind" ((← get).machine.memory.getAllocInfo location.allocId)
    let provenance := some (Provenance.concrete location.allocId tag)
    if info.kind != .liveData then
      if size.bytes != 0 then throw (.invalidProgram "nonlive allocation with nonzero reborrow")
      return provenance
    let inside ← insidePermissions h budget place size policy
    h.ensureTreeExtra location.allocId
    for segment in inside.iterAll do
      if let some access := segment.data.permission.associatedAccess then
        if access == .Write then
          let some entry := (← get).machine.memory.live.find? (fun entry => entry.1 == location.allocId)
            | throw (.invalidProgram "missing live allocation mutability")
          if entry.2.allocation.mutability == .Not then
            throw .retagWriteToReadOnly
        let offset ← checked "reborrow offset"
          (Size.add location.baseOffset (Size.ofBytes segment.range.start))
        let length := Size.ofBytes (segment.range.stop - segment.range.start)
        let tree ← getTree location.allocId
        let accessResult := tree.performBorrowAccessRange location.parentProvenance offset length access
          (← tracker).global.protectedTags .VisitChildrenOfAccessed
        updateTree location.allocId accessResult.tree
        if accessResult.status != .Completed then throw (accessError accessResult.status)
        if length.bytes != 0 then
          match access with
          | .Read => MachineHooks.memoryRaceRead location.allocId (allocRange offset length) .Retag
          | .Write => MachineHooks.memoryRaceWrite location.allocId (allocRange offset length) .Retag
    let tree ← getTree location.allocId
    let child := tree.newChild location.baseOffset location.parentProvenance tag inside
      policy.outsidePermission policy.protector.isSome
    updateTree location.allocId child.tree
    checked "reborrow child insertion" child.outcome
    return provenance

/-- The budget limits concrete recursive freeze traversal only; exhaustion is
an explicit resource outcome and does not bound the source semantics. -/
def retagPlace [DecidableEq K] (h : Hooks K User) (budget : Nat)
    (place : MPlaceTy Provenance) (policy : NewPermission) : M K User (MPlaceTy Provenance) := do
  let size := ((← h.sizeAndAlign place).map Prod.fst).getD place.layout.layout.size
  let old ← tracker
  let (global, tag) ← checked "new pointer tag" old.global.newPointerTag
  modify fun state => { state with machine := { state.machine with
    borrowTracker := some { old with global } } }
  let newProvenance ← reborrow h budget place size policy tag
  let provenance ← match place.mplace.ptr.provenance with
    | none => pure none
    | some _ => match newProvenance with
      | some value => pure (some value)
      | none => throw (.invalidProgram "retag lost existing provenance")
  return { place with mplace := { place.mplace with ptr := { place.mplace.ptr with provenance } } }

def retagPtrValue [DecidableEq K] (h : Hooks K User) (budget : Nat)
    (value : RvalueImmTy Provenance) (ty : TyId) (mode : RetagMode) :
    M K User (Option (RvalueImmTy Provenance)) := do
  let shape ← h.typeShape ty
  let policy ← match shape.classify with
    | .globalBox => newPermission h (← h.builtinDeref ty) .Box mode
    | .reference => do
      let (pointee, mutability) ← h.referencePointee ty
      newPermission h pointee (if mutability == .Mut then .Mutable else .Shared) mode
    | .rawPointer => do
      if mode != .Raw then throw (.invalidProgram "raw pointer retag outside Raw mode")
      pure none
    | .customAllocatorBox => pure none
    | .invalidType => throw (.invalidProgram "tb_retag_ptr_value invalid type")
  let some policy := policy | return none
  let place ← h.immPtrToMPlace value
  let place ← retagPlace h budget place policy
  return some (← h.reconstruct value place)

def protectPlace [DecidableEq K] (h : Hooks K User) (budget : Nat)
    (place : MPlaceTy Provenance) : M K User (MPlaceTy Provenance) := do
  retagPlace h budget place MachineHooks.protectionPolicy

/-- machine.rs protection writes uninit after retagging and also when borrow
tracking is disabled. The protected pointer is then discarded. -/
def protectInPlaceFunctionArgument [DecidableEq K] (h : Hooks K User) (budget : Nat)
    (place : MPlaceTy Provenance) : M K User Unit := do
  let place ← if (← get).machine.borrowTracker.isSome then protectPlace h budget place else pure place
  h.writeUninit place

/-- machine.rs disabled-tracker guard and current retag-mode binding. -/
def machineRetagPtrValue [DecidableEq K] (h : Hooks K User) (budget : Nat)
    (value : RvalueImmTy Provenance) (ty : TyId) :
    M K User (Option (RvalueImmTy Provenance)) := do
  match (← get).machine.borrowTracker with
  | none => return none
  | some tracker => retagPtrValue h budget value ty tracker.retagMode

/-- In the imprecise unit profile, the inside permission map is empty. This
uses compiler Freeze and profile facts, with no memory-operation premise. -/
theorem insidePermissions_unit (h : Hooks K User) (budget : Nat)
    (place : MPlaceTy Provenance)
    (precise : h.preciseInteriorMut = pure false)
    (freeze : h.typeIsFreeze place.layout.ty = pure true) :
    insidePermissions h budget place Size.ZERO MachineHooks.protectionPolicy =
      pure (DedupRangeMap.new Size.ZERO
        (⟨.ReservedFrz false, false, .None⟩ : Tree.LocationState)) := by
  unfold insidePermissions
  rw [precise]
  simp only [bind, pure]
  rw [freeze]
  with_unfolding_all rfl

/-- The raw enabled/disabled tracker query, exposed for source-level proofs. -/
theorem tracker_apply (state : State K User) : tracker state =
    match state.machine.borrowTracker with
    | some value => .ok value state
    | none => .error (.invalidProgram "Tree Borrows called while disabled") state := by
  change ((show M K User MachineHooks.BorrowState from match state.machine.borrowTracker with
    | some value => (pure value : M K User MachineHooks.BorrowState)
    | none => throw (.invalidProgram "Tree Borrows called while disabled")) state) = _
  cases state.machine.borrowTracker <;> rfl

/-- The tree query follows the current raw live lookup without effects. -/
theorem getTree_apply (id : AllocId) (state : State K User) : getTree id state =
    match state.machine.memory.live.find? (fun row => row.1 == id) with
    | some entry => .ok entry.2.allocation.extra state
    | none => .error (.invalidProgram "Tree Borrows allocation extra unavailable") state := by
  change ((show M K User BorrowTree from do
    let some entry := state.machine.memory.live.find? (fun row => row.1 == id)
      | throw (.invalidProgram "Tree Borrows allocation extra unavailable")
    pure entry.2.allocation.extra) state) = _
  cases state.machine.memory.live.find? (fun row => row.1 == id) <;> rfl

/-- The exact tree write-back equation retains both failure branches. -/
theorem updateTree_apply [DecidableEq K] (id : AllocId) (tree : BorrowTree) (state : State K User) :
    updateTree id tree state =
    match state.machine.memory.live.find? (fun row => row.1 == id) with
    | none => .error (.invalidProgram "Tree Borrows allocation extra unavailable") state
    | some entry =>
      match state.machine.memory.setLiveAllocation id (entry.2.allocation.setExtra tree) with
      | .error error => .error (.invalidProgram s!"update allocation tree: {reprStr error}") state
      | .ok memory => .ok () {state with machine := {state.machine with memory}} := by
  change ((show M K User Unit from do
    let some entry := state.machine.memory.live.find? (fun row => row.1 == id)
      | throw (.invalidProgram "Tree Borrows allocation extra unavailable")
    let memory ← checked "update allocation tree"
      (state.machine.memory.setLiveAllocation id (entry.2.allocation.setExtra tree))
    set {state with machine := {state.machine with memory}}) state) = _
  cases found : state.machine.memory.live.find? (fun row => row.1 == id) with
  | none => rfl
  | some entry =>
    dsimp only
    cases mutation : state.machine.memory.setLiveAllocation id (entry.2.allocation.setExtra tree) <;>
      simp [checked] <;> with_unfolding_all rfl

/-- Checked pure compiler/memory results preserve the existing error mapping. -/
theorem checked_eq (operation : String) (value : Except E A) [Repr E] :
    (checked operation value : M K User A) =
      match value with
      | .ok result => pure result
      | .error error => throw (.invalidProgram s!"{operation}: {reprStr error}") := by rfl

end Miri.Interpreter.TypedRetag

namespace Miri.Interpreter.TypedRetag
open Miri.ABI Miri.Memory Miri.TreeBorrows
set_option autoImplicit false
/-- A checked tag-counter failure stops before any reborrow effect. -/
theorem retagPlace_tag_failure {K U : Type} [DecidableEq K]
    (h : Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (policy : RetagPolicy.NewPermission) (state : MachineHooks.State K U)
    (old : MachineHooks.BorrowState) (measured : Option (Size × Align))
    (sizeQuery : h.sizeAndAlign place = pure measured)
    (enabled : state.machine.borrowTracker = some old)
    (failure : old.global.newPointerTag = .error (.pointerTagOverflow old.global.nextPointerTag)) :
    ∃ reason, retagPlace h budget place policy state = .error (.invalidProgram reason) state := by
  refine ⟨"new pointer tag" ++ ": " ++ reprStr (.pointerTagOverflow old.global.nextPointerTag : GlobalStateError),?_⟩
  simp [retagPlace,sizeQuery,tracker,checked,enabled,failure,bind,Bind.bind,EStateM.bind,
    pure,Pure.pure,EStateM.pure,get,getThe,MonadStateOf.get,EStateM.get,
    throw,throwThe,MonadExceptOf.throw,EStateM.throw]
  rfl
end Miri.Interpreter.TypedRetag
