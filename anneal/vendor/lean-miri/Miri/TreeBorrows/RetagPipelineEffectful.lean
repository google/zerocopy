import Miri.TreeBorrows.RetagPipeline

/-! Effectful source-ordered Tree Borrows reborrow core. Compiler request values
are shared with the legacy pure fixture API; precomputed `hooks.dataRace`
values are deliberately not consulted by this engine. -/
namespace Miri.TreeBorrows.RetagPipeline.Effectful
open Miri.ABI Miri.DataStructures Miri.Memory

inductive Error (HookError : Type) where
  | core (error : RetagPipeline.Error)
  | hook (error : HookError)
  deriving Repr

/-- A concurrency leaf changes external clock/store state, never the borrowed
Tree Borrows allocation itself. All changes before errors remain available. -/
structure Transition (External HookError : Type) where
  external : External
  outcome : Except HookError Unit

structure Hooks (MachineKind External HookError : Type) where
  /-- None exactly when the allocation has no vector-clock model. A configured
  detector applies its own source race_detecting guard inside the callback. -/
  dataRace : Option (MachineState MachineKind → External → AllocId → AccessKind →
    AllocRange → Transition External HookError)

structure Result (MachineKind External HookError : Type) where
  state : MachineState MachineKind
  external : External
  outcome : Except (Error HookError) (Option Provenance)
  events : Array Event

private def addEvent (result : Result MachineKind External HookError) (event : Event) : Result MachineKind External HookError :=
  { result with events := result.events.push event }

private def fail (result : Result MachineKind External HookError) (error : RetagPipeline.Error) : Result MachineKind External HookError :=
  { result with outcome := .error (.core error) }

private def finish (result : Result MachineKind External HookError) (provenance : Option Provenance) : Result MachineKind External HookError :=
  let result := addEvent result (.reborrowReturned provenance)
  { result with outcome := .ok provenance }

private def finishWithoutRetag (result : Result MachineKind External HookError) : Result MachineKind External HookError :=
  { result with outcome := .ok none }

private def updateTreeExtra [DecidableEq MachineKind]
    (memory : MemoryState Provenance BorrowTree MachineKind) (allocId : AllocId)
    (tree : BorrowTree) : Except AllocationLookupError (MemoryState Provenance BorrowTree MachineKind) := do
  let some liveEntry := memory.live.find? fun entry => entry.1 == allocId
    | throw (.unavailable allocId)
  let allocation := liveEntry.2.allocation.setExtra tree
  memory.setLiveAllocation allocId allocation

private def buildInsidePermissions (policy : RetagPolicy.NewPermission)
    (size : Size) (pointeeIsFreeze preciseInteriorMut : Bool) (hooks : RetagPipeline.Hooks) :
    Except RetagPipeline.Error (DedupRangeMap Tree.LocationState) := do
  if !preciseInteriorMut then
    let state ← (RetagPolicy.initialLocationState policy pointeeIsFreeze)
      |>.mapError RetagPipeline.Error.initialState
    return DedupRangeMap.new size state
  let freezeMap ← hooks.freezeVisitor.mapError RetagPipeline.Error.freezeVisitor
  let mut permissions := DedupRangeMap.new size
    (Tree.LocationState.newAccessed .Disabled .None)
  for segment in freezeMap.iterAll do
    let state ← (RetagPolicy.initialLocationState policy segment.data)
      |>.mapError RetagPipeline.Error.initialState
    let update := permissions.modifyRange (Size.ofBytes segment.range.start)
      (Size.ofBytes (segment.range.stop - segment.range.start)) (fun _ _ => state)
    permissions := update.state
    match update.outcome with
    | .error error => throw (.layoutRangeMap error)
    | .ok () => pure ()
  return permissions

private def accessTreeForReborrow [DecidableEq MachineKind]
    (result : Result MachineKind External HookError) (_request : Request)
    (policy : RetagPolicy.NewPermission) (newTag : BorTag)
    (location : ResolvedLocation) (inside : DedupRangeMap Tree.LocationState)
    (allocationMutability : Mutability) (effects : Hooks MachineKind External HookError) : Result MachineKind External HookError := Id.run do
  let mut current := result
  for segment in inside.iterAll do
    match segment.data.permission.associatedAccess with
    | none => pure ()
    | some kind =>
        if kind == .Write && allocationMutability == .Not then
          return fail current (.writeToReadOnly location.allocId)
        let absoluteOffset? := match Size.add location.baseOffset
            (Size.ofBytes segment.range.start) with
          | .ok offset => some offset
          | .error _ => none
        let some absoluteOffset := absoluteOffset?
          | return fail current (.offsetOverflow location.baseOffset segment.range.start)
        let length := Size.ofBytes (segment.range.stop - segment.range.start)
        let absoluteEnd? := match Size.add absoluteOffset length with
          | .ok endOffset => some endOffset
          | .error _ => none
        let some absoluteEnd := absoluteEnd?
          | return fail current (.rangeEndOverflow absoluteOffset length)
        let range : ByteRange := ⟨absoluteOffset.bytes, absoluteEnd.bytes⟩
        current := addEvent current (.parentTreeAccess kind range)
        let some localEntry := current.state.memory.live.find? fun entry => entry.1 == location.allocId
          | return fail current (.treeExtraUnavailable location.allocId)
        let access := localEntry.2.allocation.extra.performBorrowAccessRange
          location.parentProvenance absoluteOffset length kind
          current.state.global.protectedTags .VisitChildrenOfAccessed
        let nextMemory ← match updateTreeExtra current.state.memory location.allocId access.tree with
          | .ok memory => pure memory
          | .error error => return fail current (.memoryUpdate error)
        current := { current with state := { current.state with memory := nextMemory } }
        if access.status != .Completed then
          return fail current (.treeAccess range access.status)
        if length.bytes != 0 then
          match effects.dataRace with
          | none => pure ()
          | some hook =>
              current := addEvent current (.dataRaceAccess kind range)
              let transition := hook current.state current.external location.allocId kind
                (allocRange absoluteOffset length)
              current := { current with external := transition.external }
              match transition.outcome with
              | .error error => return { current with outcome := .error (.hook error) }
              | .ok () => pure ()
  let some liveEntry := current.state.memory.live.find? fun entry => entry.1 == location.allocId
    | return fail current (.treeExtraUnavailable location.allocId)
  let child := liveEntry.2.allocation.extra.newChild location.baseOffset
    location.parentProvenance newTag inside policy.outsidePermission
    policy.protector.isSome
  let nextMemory ← match updateTreeExtra current.state.memory location.allocId child.tree with
    | .ok memory => pure memory
    | .error error => return fail current (.memoryUpdate error)
  current := { current with state := { current.state with memory := nextMemory } }
  match child.outcome with
  | .error error => return fail current (.childInsert error)
  | .ok () => pure ()
  return addEvent current (.childInserted newTag)

private def runReborrow [DecidableEq MachineKind]
    (state : MachineState MachineKind) (request : Request)
    (policy : RetagPolicy.NewPermission) (ptrSize : Size) (newTag : BorTag)
    (initialEvents : Array Event) (external : External)
    (effects : Hooks MachineKind External HookError) : Result MachineKind External HookError := Id.run do
  let mut result : Result MachineKind External HookError := ⟨state, external, .ok none, initialEvents⟩
  result := addEvent result .pointerAccessChecked
  match request.hooks.pointerAccess with
  | .error message => return fail result (.pointerAccess message)
  | .ok () => pure ()

  let tracked := state.global.isTrackedPointerTag newTag
  let location := request.hooks.allocationResolution
  result := addEvent result (.allocationResolution (location.map (·.allocId)))
  match location with
  | none =>
      if ptrSize.bytes != 0 then
        return fail result (.nonzeroSizeWithoutAllocation ptrSize)
      result := addEvent result (.creationLogCalled newTag none tracked)
      match request.hooks.creationLog with
      | .error message => return fail result (.creationLog message)
      | .ok () => pure ()
      return finish result request.originalProvenance
  | some location =>
      let newProvenance := some (Provenance.concrete location.allocId newTag)
      result := addEvent result (.creationLogCalled newTag (some location.allocId) tracked)
      match request.hooks.creationLog with
      | .error message => return fail result (.creationLog message)
      | .ok () => pure ()

      if let some protector := policy.protector then
        let (global, frame) := state.global.addProtector state.frame
          location.allocId newTag protector
        result := { result with state := { result.state with global := global, frame := frame } }
        result := addEvent result (.protectorRegistered newTag protector)

      let allocationInfo ← match result.state.memory.getAllocInfo location.allocId with
        | .ok info => pure info
        | .error error => return fail result (.allocationLookup error)
      result := addEvent result (.allocationKindChecked location.allocId allocationInfo.kind)
      if allocationInfo.kind != .liveData then
        if ptrSize.bytes != 0 then
          return fail result (.nonLiveAllocationHasBytes allocationInfo.kind ptrSize)
        return finish result newProvenance

      let inside ← match buildInsidePermissions policy ptrSize request.pointeeIsFreeze
          request.preciseInteriorMut request.hooks with
        | .ok permissions => pure permissions
        | .error error => return fail result error
      if request.preciseInteriorMut then result := addEvent result .freezeLayoutVisited
      match request.hooks.allocationExtra with
      | .error message => return fail result (.allocationExtra message)
      | .ok () => pure ()
      let some localEntry := result.state.memory.live.find? fun entry => entry.1 == location.allocId
        | return fail result (.treeExtraUnavailable location.allocId)
      result := addEvent result (.allocationExtraLoaded location.allocId)
      result := accessTreeForReborrow result request policy newTag location inside
        localEntry.2.allocation.mutability effects
      match result.outcome with
      | .error _ => return result
      | .ok _ => pure ()
      return finish result newProvenance

/-- Source `tb_retag_ptr_value` followed by `tb_retag_place` and the
allocation-local portion of `tb_reborrow`. Policy selection precedes place
conversion; the dynamic-size query precedes `new_ptr`; pointer validation
follows tag allocation. Hook failures return the state accumulated up to that
source point, including installed protectors and earlier parent accesses.
-/
def retagPointerValue [DecidableEq MachineKind]
    (state : MachineState MachineKind) (request : Request) (external : External)
    (effects : Hooks MachineKind External HookError) : Result MachineKind External HookError := Id.run do
  let mut result : Result MachineKind External HookError := ⟨state, external, .ok none, #[]⟩
  let maybePolicy ← match request.typeShape.classify with
    | .reference => pure (RetagPolicy.create request.typeFacts request.referenceKind
        request.mode request.config)
    | .globalBox => pure (RetagPolicy.create request.typeFacts .Box
        request.mode request.config)
    | .customAllocatorBox => return finishWithoutRetag result
    | .rawPointer =>
        if request.mode != .Raw then return fail result .rawPointerWrongMode
        return finishWithoutRetag result
    | .invalidType => return fail result .invalidType
  let some policy := maybePolicy | return finishWithoutRetag result
  match request.hooks.placeConversion with
  | .error message => return fail result (.placeConversion message)
  | .ok () => pure ()
  result := addEvent result .placeConverted
  let ptrSize ← match request.hooks.sizeAndAlignOfValue with
    | .error message => return fail result (.sizeQuery message)
    | .ok size => pure (size.getD request.layoutSize)
  result := addEvent result (.reborrowSizeSelected ptrSize)
  let (global, tag) ← match result.state.global.newPointerTag with
    | .error (.pointerTagOverflow tag) => return fail result (.pointerTagOverflow tag)
    | .ok tagResult => pure tagResult
  result := { result with state := { result.state with global } }
  result := addEvent result (.pointerTagAllocated tag)
  let reborrowed := runReborrow result.state request policy ptrSize tag result.events result.external effects
  match reborrowed.outcome with
  | .error _ => return reborrowed
  | .ok provenance =>
      result := addEvent reborrowed (.placeProvenanceReplaced provenance)
      return addEvent result .retaggedValueReconstructed

end Miri.TreeBorrows.RetagPipeline.Effectful
