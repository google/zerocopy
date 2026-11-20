import Miri.TreeBorrows.RetagPolicy
import Miri.TreeBorrows.TreeState
import Miri.Memory.MemoryState

/-!
Source-ordered `tb_retag_ptr_value` / `tb_retag_place` / `tb_reborrow` core.
Rustc type/layout queries, pointer validation/resolution, diagnostics, and data
race operations are explicit hook results. The live allocation's actual
`BorrowTree` is stored in `MemoryState` extra data and updated through the
source allocation API. This module does not claim the interpreter hooks are
implemented.
-/

namespace Miri.TreeBorrows.RetagPipeline

open Miri.ABI
open Miri.DataStructures
open Miri.Memory

structure MachineState (MachineKind : Type) where
  memory : MemoryState Provenance BorrowTree MachineKind
  global : GlobalState
  frame : FrameState

structure ResolvedLocation where
  allocId : AllocId
  baseOffset : Size
  parentProvenance : ProvenanceExtra
  deriving DecidableEq, Repr

/-- The source `tb_retag_ptr_value` type dispatch. Raw pointers and boxes with
custom allocators return before place conversion; only reference types and
global boxes construct a `NewPermission` and call `tb_retag_place`.
-/
inductive RetagInputKind where
  | reference
  | globalBox
  | rawPointer
  | customAllocatorBox
  | invalidType
  deriving DecidableEq, Repr, Inhabited

/-- Predicates supplied by rustc for the source type match. Although Rust's
type constructors are disjoint, `isGlobalBox` is a separate predicate and is
tested before `TyKind`, exactly as in `tb_retag_ptr_value`. Keeping the
predicates explicit lets the Lean caller preserve that guard priority. -/
structure RetagTypeShape where
  isGlobalBox : Bool := false
  isReference : Bool := true
  isRawPointer : Bool := false
  isBox : Bool := false
  deriving DecidableEq, Repr, Inhabited

namespace RetagTypeShape

def classify (shape : RetagTypeShape) : RetagInputKind :=
  if shape.isGlobalBox then .globalBox
  else if shape.isReference then .reference
  else if shape.isRawPointer then .rawPointer
  else if shape.isBox then .customAllocatorBox
  else .invalidType

def reference : RetagTypeShape := {}
def globalBox : RetagTypeShape :=
  { isGlobalBox := true, isReference := false, isRawPointer := false, isBox := true }
def rawPointer : RetagTypeShape :=
  { isGlobalBox := false, isReference := false, isRawPointer := true, isBox := false }
def customAllocatorBox : RetagTypeShape :=
  { isGlobalBox := false, isReference := false, isRawPointer := false, isBox := true }
def invalid : RetagTypeShape :=
  { isGlobalBox := false, isReference := false, isRawPointer := false, isBox := false }

end RetagTypeShape

inductive Event where
  | placeConverted
  | reborrowSizeSelected (size : Size)
  | pointerTagAllocated (tag : BorTag)
  | allocationResolution (location : Option AllocId)
  | pointerAccessChecked
  | creationLogCalled (tag : BorTag) (location : Option AllocId) (tracked : Bool)
  | protectorRegistered (tag : BorTag) (kind : ProtectorKind)
  | allocationKindChecked (allocId : AllocId) (kind : AllocationKind)
  | freezeLayoutVisited
  | allocationExtraLoaded (allocId : AllocId)
  | parentTreeAccess (kind : AccessKind) (range : ByteRange)
  | dataRaceAccess (kind : AccessKind) (range : ByteRange)
  | childInserted (tag : BorTag)
  | reborrowReturned (provenance : Option Provenance)
  | placeProvenanceReplaced (provenance : Option Provenance)
  | retaggedValueReconstructed
  deriving DecidableEq, Repr

inductive Error where
  | placeConversion (message : String)
  | rawPointerWrongMode
  | invalidType
  | sizeQuery (message : String)
  | pointerTagOverflow (tag : BorTag)
  | pointerAccess (message : String)
  | creationLog (message : String)
  | nonzeroSizeWithoutAllocation (size : Size)
  | allocationLookup (error : AllocationLookupError)
  | nonLiveAllocationHasBytes (kind : AllocationKind) (size : Size)
  | freezeVisitor (message : String)
  | initialState (error : RetagPolicy.InitialStateError)
  | layoutRangeMap (error : DedupRangeMapError)
  | allocationExtra (message : String)
  | treeExtraUnavailable (allocId : AllocId)
  | writeToReadOnly (allocId : AllocId)
  | offsetOverflow (baseOffset : Size) (relativeOffset : UInt64)
  | rangeEndOverflow (start length : Size)
  | treeAccess (range : ByteRange) (status : BorrowTree.BorrowTreeAccessStatus)
  | missingDataRaceResult (index : Nat)
  | dataRace (message : String)
  | childInsert (error : BorrowTree.ChildInsertError)
  | memoryUpdate (error : AllocationLookupError)
  deriving DecidableEq, Repr

structure Result (MachineKind : Type) where
  state : MachineState MachineKind
  outcome : Except Error (Option Provenance)
  events : Array Event

/-- Inputs supplied by the rustc/Miri layer around `tb_reborrow`. A failed
hook is kept at the point where the pinned source calls it. `freezeVisitor`
is consulted only when precise interior mutability is enabled; `dataRace`
is `none` when the allocation has no vector-clock model.
-/
structure Hooks where
  placeConversion : Except String Unit := .ok ()
  sizeAndAlignOfValue : Except String (Option Size) := .ok none
  pointerAccess : Except String Unit := .ok ()
  /-- Result of `ptr_try_get_alloc_id(place.ptr(), 0)`, consulted only after
  `check_ptr_access` succeeds. An absent result takes Miri's zero-size path.
  -/
  allocationResolution : Option ResolvedLocation := none
  creationLog : Except String Unit := .ok ()
  freezeVisitor : Except String (DedupRangeMap Bool) := .ok (DedupRangeMap.new Size.ZERO false)
  allocationExtra : Except String Unit := .ok ()
  dataRace : Option (Array (Except String Unit)) := none
  deriving Inhabited

structure Request where
  typeShape : RetagTypeShape := .reference
  typeFacts : RetagPolicy.TypeFacts
  referenceKind : RetagPolicy.ReferenceKind
  mode : RetagPolicy.RetagMode
  config : RetagPolicy.PolicyConfig
  layoutSize : Size
  originalProvenance : Option Provenance
  pointeeIsFreeze : Bool
  preciseInteriorMut : Bool
  hooks : Hooks := {}
  deriving Inhabited

private def addEvent (result : Result MachineKind) (event : Event) : Result MachineKind :=
  { result with events := result.events.push event }

private def fail (result : Result MachineKind) (error : Error) : Result MachineKind :=
  { result with outcome := .error error }

private def finish (result : Result MachineKind) (provenance : Option Provenance) : Result MachineKind :=
  let result := addEvent result (.reborrowReturned provenance)
  { result with outcome := .ok provenance }

private def finishWithoutRetag (result : Result MachineKind) : Result MachineKind :=
  { result with outcome := .ok none }

private def updateTreeExtra [DecidableEq MachineKind]
    (memory : MemoryState Provenance BorrowTree MachineKind) (allocId : AllocId)
    (tree : BorrowTree) : Except AllocationLookupError (MemoryState Provenance BorrowTree MachineKind) := do
  let some liveEntry := memory.live.find? fun entry => entry.1 == allocId
    | throw (.unavailable allocId)
  let allocation := liveEntry.2.allocation.setExtra tree
  memory.setLiveAllocation allocId allocation

private def buildInsidePermissions (policy : RetagPolicy.NewPermission)
    (size : Size) (pointeeIsFreeze preciseInteriorMut : Bool) (hooks : Hooks) :
    Except Error (DedupRangeMap Tree.LocationState) := do
  if !preciseInteriorMut then
    let state ← (RetagPolicy.initialLocationState policy pointeeIsFreeze)
      |>.mapError Error.initialState
    return DedupRangeMap.new size state
  let freezeMap ← hooks.freezeVisitor.mapError Error.freezeVisitor
  let mut permissions := DedupRangeMap.new size
    (Tree.LocationState.newAccessed .Disabled .None)
  for segment in freezeMap.iterAll do
    let state ← (RetagPolicy.initialLocationState policy segment.data)
      |>.mapError Error.initialState
    let update := permissions.modifyRange (Size.ofBytes segment.range.start)
      (Size.ofBytes (segment.range.stop - segment.range.start)) (fun _ _ => state)
    permissions := update.state
    match update.outcome with
    | .error error => throw (.layoutRangeMap error)
    | .ok () => pure ()
  return permissions

private def accessTreeForReborrow [DecidableEq MachineKind]
    (result : Result MachineKind) (request : Request)
    (policy : RetagPolicy.NewPermission) (newTag : BorTag)
    (location : ResolvedLocation) (inside : DedupRangeMap Tree.LocationState)
    (allocationMutability : Mutability) : Result MachineKind := Id.run do
  let mut current := result
  let mut dataRacePosition := 0
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
          match request.hooks.dataRace with
          | none => pure ()
          | some hooks =>
              current := addEvent current (.dataRaceAccess kind range)
              match hooks[dataRacePosition]? with
              | none => return fail current (.missingDataRaceResult dataRacePosition)
              | some (Except.error message) => return fail current (.dataRace message)
              | some (Except.ok ()) => pure ()
              dataRacePosition := dataRacePosition + 1
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
    (initialEvents : Array Event) : Result MachineKind := Id.run do
  let mut result : Result MachineKind := ⟨state, .ok none, initialEvents⟩
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
        localEntry.2.allocation.mutability
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
    (state : MachineState MachineKind) (request : Request) : Result MachineKind := Id.run do
  let mut result : Result MachineKind := ⟨state, .ok none, #[]⟩
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
  let reborrowed := runReborrow result.state request policy ptrSize tag result.events
  match reborrowed.outcome with
  | .error _ => return reborrowed
  | .ok provenance =>
      result := addEvent reborrowed (.placeProvenanceReplaced provenance)
      return addEvent result .retaggedValueReconstructed

end Miri.TreeBorrows.RetagPipeline
