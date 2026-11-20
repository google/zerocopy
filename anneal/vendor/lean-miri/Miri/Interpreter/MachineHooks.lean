import Miri.Interpreter.Call
import Miri.Concurrency.LocalRace
import Miri.TreeBorrows.RetagPipelineEffectful

/-! Pinned Miri machine hooks for frame-local clocks, retag scopes and
protector lifecycle. Compiler/memory leaves remain explicit effects. -/
namespace Miri.Interpreter.MachineHooks
open Miri.ABI Miri.Memory Miri.MIR
open Miri.TreeBorrows.RetagPolicy

structure CatchUnwindData where
  catchFn : Pointer (Option Provenance)
  data : RvalueImmTy Provenance
  dest : MPlaceTy Provenance
  ret : Option BasicBlockId

/-- Semantic FrameExtra fields; profiling-only timing is omitted. -/
structure FrameExtra where
  borrowTracker : Option Miri.TreeBorrows.FrameState
  catchUnwind : Option CatchUnwindData
  userRelevance : UInt8
  dataRace : Option Miri.Concurrency.LocalRace.FrameState

structure BorrowState where
  global : Miri.TreeBorrows.GlobalState
  retagMode : RetagMode

/-- Allocation race extras are keyed by the same canonical AllocId as live
memory; this external index composes with the existing BorrowTree extra type.
Allocation lifecycle adapters must install/remove entries with their allocation. -/
structure MachineState (K User : Type) where
  memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree K
  borrowTracker : Option BorrowState
  dataRace : Option Miri.Concurrency.GlobalState
  threads : Miri.Concurrency.ThreadManager
  raceAllocations : Array (AllocId × Miri.Concurrency.VClockAlloc)
  allocationSpans : Array (AllocId × SpanRef × Option SpanRef)
  user : User

abbrev State (K User : Type) := StepState Provenance LocalLayout FrameExtra (MachineState K User)
abbrev M (K User A : Type) := EStateM StepError (State K User) A

private def fail (operation : String) (error : A) [Repr A] : M K User B :=
  throw (.callback s!"{operation}: {reprStr error}")

def currentFrame : M K User (Frame Provenance LocalLayout FrameExtra) := do
  match (← get).stack.currentFrame? with
  | none => throw (.stack .emptyStack)
  | some frame => pure frame

def setCurrentFrame (frame : Frame Provenance LocalLayout FrameExtra) : M K User Unit := do
  let state ← get
  if state.stack.frames.isEmpty then throw (.stack .emptyStack)
  set { state with stack := ⟨state.stack.frames.pop.push frame⟩ }

private def requireGlobal (machine : MachineState K User) : M K User Miri.Concurrency.GlobalState :=
  match machine.dataRace with
  | none => throw (.invalidProgram "frame has vector clocks but machine does not")
  | some global => pure global

/-- Source machine after_local_read. LocalAccess already skips this hook for
indirect operands and while validation is in progress. -/
def afterLocalRead (localId : LocalId) : M K User Unit := do
  let frame ← currentFrame
  if let some clocks := frame.extra.dataRace then
    let state ← get
    let global ← requireGlobal state.machine
    let result := Miri.Concurrency.LocalRace.localRead clocks global state.machine.threads localId
    set { state with machine := { state.machine with dataRace := some result.global } }
    setCurrentFrame { frame with extra := { frame.extra with dataRace := some result.frame } }
    match result.outcome with
    | .ok () => pure ()
    | .error error => fail "after_local_read" error

/-- Source machine after_local_write. The storage-live bit changes the clock
transition; it is never treated as an ordinary overwrite. -/
def afterLocalWrite (localId : LocalId) (storageLive : Bool) : M K User Unit := do
  let frame ← currentFrame
  if let some clocks := frame.extra.dataRace then
    let state ← get
    let global ← requireGlobal state.machine
    let result := Miri.Concurrency.LocalRace.localWrite clocks global state.machine.threads localId storageLive
    set { state with machine := { state.machine with dataRace := some result.global } }
    setCurrentFrame { frame with extra := { frame.extra with dataRace := some result.frame } }
    match result.outcome with
    | .ok () => pure ()
    | .error error => fail "after_local_write" error

/-- LocalAccess's frame/state callback boundary, preserving the canonical
frame-local clock map instead of copying it into an unrelated side state. -/
def localAccessAfterRead (frame : Frame Provenance LocalLayout FrameExtra)
    (machine : MachineState K User) (localId : LocalId) :
    LocalAccessResult Provenance FrameExtra (MachineState K User) Unit := Id.run do
  match frame.extra.dataRace with
  | none => return ⟨frame, machine, .ok ()⟩
  | some clocks =>
    let global ← match machine.dataRace with
      | none => return ⟨frame, machine, .error (.resolver "frame/machine vector-clock mismatch")⟩
      | some global => pure global
    let result := Miri.Concurrency.LocalRace.localRead clocks global machine.threads localId
    return ⟨{ frame with extra := { frame.extra with dataRace := some result.frame } },
      { machine with dataRace := some result.global }, result.outcome.mapError fun error =>
        .resolver s!"after_local_read: {reprStr error}"⟩

/-- Required layout and stack-memory leaves. Whole-state storage operations
below preserve FrameExtra changes made by afterLocalWrite and allocation. -/
structure StorageHooks (K User : Type) where
  veryTriviallySized : TyId → Except StepError Bool
  layout : LocalId → M K User LocalLayout
  allocateDyn : LocalLayout → MemPlaceMeta Provenance → M K User (MemPlace Provenance)
  deallocateStack : Pointer (Option Provenance) → M K User Unit

private def fromStack (value : Except StackError A) : M K User A :=
  match value with
  | .ok value => pure value
  | .error error => throw (.stack error)

private def deallocateLocal (hooks : StorageHooks K User) (value : LocalValue Provenance) :
    M K User Unit := do
  if let .live (.indirect place) := value then hooks.deallocateStack place.ptr

/-- A successful stack result introduces no machine effect. This public rule
lets client proofs use the storage driver without naming its private adapter. -/
@[simp] theorem storageResult_ok (value : A) :
    fromStack (.ok value) = (pure value : M K User A) := rfl

/-- Dead local storage owns no allocation to deallocate. -/
@[simp] theorem deallocateLocal_dead (hooks : StorageHooks K User) :
    deallocateLocal hooks .dead = (pure () : M K User Unit) := rfl

/-- Canonical whole-state source storage_live_dyn. The generic Frame operation
cannot itself install FrameExtra mutations made by a machine hook; this binding
uses current Frame methods after each hook so local-race/protector state survives. -/
def storageLiveDyn (hooks : StorageHooks K User) (localId : LocalId)
    (metadata : MemPlaceMeta Provenance) : M K User Unit := do
  let frame ← currentFrame
  let _ ← fromStack (frame.getLocal localId)
  let ty ← match frame.body.locals[localId]? with
    | none => throw (.stack (.missingLocalType localId))
    | some ty => pure ty
  let trivial ← match hooks.veryTriviallySized ty with
    | .error error => throw error
    | .ok value => pure value
  let unsizedLayout ← if trivial then pure none else do
    let frame ← currentFrame
    let cached ← fromStack (frame.getLocalLayout localId)
    let layout ← match cached with
      | some layout => pure layout
      | none => do
        let computed ← hooks.layout localId
        let frame ← currentFrame
        let (updated, cached) ← fromStack (frame.getOrCacheLocalLayout localId computed)
        setCurrentFrame updated
        pure cached
    pure (if layout.layout.isSized then none else some layout)
  let value ← match unsizedLayout with
    | some layout => do
      unless metadata.hasMeta do throw (.stack (.unsizedLocalMissingMetadata localId))
      pure (Operand.indirect (← hooks.allocateDyn layout metadata))
    | none => do
      if metadata.hasMeta then throw (.stack (.metadataForSizedLocal localId))
      afterLocalWrite localId true
      pure (Operand.immediate .uninit)
  let frame ← currentFrame
  let old ← fromStack (frame.getLocal localId)
  setCurrentFrame (← fromStack (frame.replaceLocalValue localId (.live value)))
  deallocateLocal hooks old.value

def storageDead (hooks : StorageHooks K User) (localId : LocalId) : M K User Unit := do
  if localId == 0 then throw (.stack .cannotMakeReturnPlaceDead)
  let frame ← currentFrame
  let old ← fromStack (frame.getLocal localId)
  setCurrentFrame (← fromStack (frame.replaceLocalValue localId .dead))
  deallocateLocal hooks old.value

/-- Source init_frame semantic fields. New frames have empty protected-tag and
local-clock sets exactly when their corresponding machine backend is enabled. -/
def initFrame (relevance : Frame Provenance LocalLayout Unit → M K User UInt8)
    (frame : Frame Provenance LocalLayout Unit) :
    M K User (Frame Provenance LocalLayout FrameExtra) := do
  let borrowTracker := (← get).machine.borrowTracker.map fun _ => {}
  let userRelevance ← relevance frame
  let dataRace := (← get).machine.dataRace.map fun _ => {}
  return {
    body := frame.body, bodyIdentity := frame.bodyIdentity
    functionInstance := frame.functionInstance
    extra := {
      borrowTracker, catchUnwind := none, userRelevance, dataRace }
    returnContinuation := frame.returnContinuation, returnPlace := frame.returnPlace
    localsIdentity := frame.localsIdentity
    locals := frame.locals, vaList := frame.vaList, trackCallerArg := frame.trackCallerArg
    location := frame.location }

/-- Source after_local_moved_to_memory records declaration span before fetching
allocation extras, then transfers local timestamps to every byte. -/
def afterLocalMovedToMemory (localId : LocalId) (place : MPlaceTy Provenance)
    (localSpan : Body → LocalId → M K User SpanRef) : M K User Unit := do
  let allocId ← match place.mplace.ptr.provenance with
    | some (.concrete allocId _) => pure allocId
    | _ => throw (.invalidProgram "after_local_moved_to_memory requires fresh concrete allocation")
  let frame ← currentFrame
  let span ← localSpan frame.body localId
  modify fun state => { state with machine := { state.machine with allocationSpans :=
    (state.machine.allocationSpans.filter fun entry => entry.1 != allocId).push (allocId, span, none) } }
  let state ← get
  unless (state.machine.memory.live.any fun entry => entry.1 == allocId) do
    throw (.invalidProgram "fresh local allocation has no allocation extra")
  if let some clocks := frame.extra.dataRace then
    let global ← requireGlobal state.machine
    let allocation ← match state.machine.raceAllocations.find? fun entry => entry.1 == allocId with
      | none => throw (.invalidProgram "local allocation missing vector-clock extra")
      | some entry => pure entry.2
    let result := Miri.Concurrency.LocalRace.localMovedToMemory clocks global state.machine.threads localId allocation
    modify fun state => { state with machine := { state.machine with raceAllocations :=
      (state.machine.raceAllocations.filter fun entry => entry.1 != allocId).push (allocId, result.allocation) } }
    setCurrentFrame { frame with extra := { frame.extra with dataRace := some result.frame } }
    match result.outcome with
    | .ok () => pure ()
    | .error error => fail "after_local_moved_to_memory" error

private def raceSize (size : Size) : Miri.Concurrency.ByteSize :=
  .ofU64 size.bytes.toNat (by have h := UInt64.toNat_lt size.bytes; omega)

/-- Allocation-level vector-clock read/write binding. The outer machine memory
hook must still perform weak-memory invalidation (writes), Tree Borrows and
sync-object access in source order; this function is the data-race stage only. -/
def memoryRaceAccess (machine : MachineState K User) (allocId : AllocId)
    (range : AllocRange) (writeType : Option Miri.Concurrency.NaWriteType)
    (readType : Miri.Concurrency.NaReadType) :
    MachineState K User × Except StepError Unit := Id.run do
  let global ← match machine.dataRace with
    | none => return (machine, .ok ())
    | some global => pure global
  let allocation ← match machine.raceAllocations.find? fun entry => entry.1 == allocId with
    | none => return (machine, .error (.invalidProgram "allocation missing vector-clock extra"))
    | some entry => pure entry.2
  if !global.raceDetecting then return (machine, .ok ())
  let (index, clocks) ← match global.activeThreadState machine.threads with
    | .error error => return (machine, .error (.callback s!"memory race active clock: {reprStr error}"))
    | .ok value => pure value
  let range : Miri.Concurrency.AccessRange := ⟨raceSize range.start, raceSize range.size⟩
  let result := match writeType with
    | none => allocation.readNonAtomic range clocks index readType
    | some writeType => allocation.writeNonAtomic range clocks index writeType
  let global := { global with vectorClocks := global.vectorClocks.set index.toNat result.thread }
  let machine := { machine with
    dataRace := some global
    raceAllocations := (machine.raceAllocations.filter fun entry => entry.1 != allocId).push (allocId, result.allocation) }
  let outcome := match result.result with
    | .ok => .ok ()
    | .race => .error (.undefinedBehavior "DataRace")
    | other => .error (.invalidProgram s!"memory race detector invariant: {reprStr other}")
  return (machine, outcome)

def memoryRaceRead (allocId : AllocId) (range : AllocRange)
    (readType : Miri.Concurrency.NaReadType) : M K User Unit := do
  let state ← get
  let (machine, outcome) := memoryRaceAccess state.machine allocId range none readType
  set { state with machine }
  match outcome with | .ok () => pure () | .error error => throw error

def memoryRaceWrite (allocId : AllocId) (range : AllocRange)
    (writeType : Miri.Concurrency.NaWriteType) : M K User Unit := do
  let state ← get
  let (machine, outcome) := memoryRaceAccess state.machine allocId range (some writeType) .Read
  set { state with machine }
  match outcome with | .ok () => pure () | .error error => throw error

/-- Source with_retag_mode restores the old mode after both success and error.
A disabled borrow tracker runs the body directly, as in machine.rs. -/
def withRetagMode (mode : RetagMode) (action : M K User A) : M K User A := fun state =>
  match state.machine.borrowTracker with
  | none => action state
  | some tracker =>
    let oldMode := tracker.retagMode
    let entered := { state with machine := { state.machine with
      borrowTracker := some { tracker with retagMode := mode } } }
    let restore (state : State K User) : Except StepError (State K User) :=
      match state.machine.borrowTracker with
      | none => .error (.invalidProgram "borrow tracker removed during retag mode scope")
      | some tracker => .ok { state with machine := { state.machine with
          borrowTracker := some { tracker with retagMode := oldMode } } }
    match action entered with
    | .ok value after =>
      match restore after with
      | .ok state => .ok value state
      | .error error => .error error after
    | .error error after =>
      match restore after with
      | .ok state => .error error state
      | .error invariant => .error invariant after

/-- Required typed pointer queries and memory effects around the existing
Tree Borrows core. prepare* returns all explicit RetagPipeline leaf results;
no successful request is generated for missing compiler or pointer facts. -/
structure Hooks (K User : Type) where
  preparePointerRetag : RvalueImmTy Provenance → TyId → RetagMode → M K User Miri.TreeBorrows.RetagPipeline.Request
  reconstructImmediate : RvalueImmTy Provenance → Option Provenance → M K User (RvalueImmTy Provenance)
  preparePlaceProtection : MPlaceTy Provenance → M K User Miri.TreeBorrows.RetagPipeline.Request
  writeUninit : MPlaceTy Provenance → M K User Unit
  /-- Source get_alloc_extra may materialize a compiler global or fail (extern static). -/
  ensureTreeExtra : AllocId → M K User Unit

private def borrowAccessError (status : Miri.TreeBorrows.BorrowTree.BorrowTreeAccessStatus) : StepError :=
  match status with
  | .AccessFailure _ (.TransitionError ..)
  | .WildcardFailure _ (.TransitionError ..)
  | .WildcardFailure _ (.NoValidExposedReferences ..) =>
    .undefinedBehavior s!"Tree Borrows: {reprStr status}"
  | _ => .invalidProgram s!"Tree Borrows invariant: {reprStr status}"

private def applyRetag [DecidableEq K] (request : Miri.TreeBorrows.RetagPipeline.Request) :
    M K User (Option Provenance × Bool) := do
  let state ← get
  let tracker ← match state.machine.borrowTracker with
    | none => throw (.invalidProgram "Tree Borrows core called while disabled")
    | some tracker => pure tracker
  let frame ← currentFrame
  let borrowFrame ← match frame.extra.borrowTracker with
    | none => throw (.invalidProgram "enabled borrow tracker missing frame state")
    | some frame => pure frame
  let effects : Miri.TreeBorrows.RetagPipeline.Effectful.Hooks K (MachineState K User) StepError := {
    dataRace := if state.machine.dataRace.isSome then some fun _ machine allocId kind range =>
      let (machine, outcome) := memoryRaceAccess machine allocId range
        (if kind == .Write then some .Retag else none) .Retag
      ⟨machine, outcome⟩
      else none }
  let result := Miri.TreeBorrows.RetagPipeline.Effectful.retagPointerValue
    ⟨state.machine.memory, tracker.global, borrowFrame⟩ request state.machine effects
  modify fun state => { state with machine := { result.external with
    memory := result.state.memory
    borrowTracker := some { tracker with global := result.state.global } } }
  setCurrentFrame { frame with extra := { frame.extra with borrowTracker := some result.state.frame } }
  match result.outcome with
  | .error (.hook error) => throw error
  | .error (.core (.treeAccess _ status)) => throw (borrowAccessError status)
  | .error (.core (.writeToReadOnly _)) => throw .retagWriteToReadOnly
  | .error (.core error) => fail "Tree Borrows retag" error
  | .ok provenance => return (provenance, result.events.contains .retaggedValueReconstructed)

def retagPtrValue [DecidableEq K] (hooks : Hooks K User)
    (value : RvalueImmTy Provenance) (ty : TyId) : M K User (Option (RvalueImmTy Provenance)) := do
  match (← get).machine.borrowTracker with
  | none => return none
  | some tracker =>
    let request ← hooks.preparePointerRetag value ty tracker.retagMode
    let (provenance, changed) ← applyRetag { request with mode := tracker.retagMode }
    if changed then return some (← hooks.reconstructImmediate value provenance)
    return none

/-- This policy is exactly tb_protect_place's explicit NewPermission. -/
def protectionPolicy : NewPermission :=
  { freezePermission := .ReservedFrz false
    nonfreezePermission := .ReservedFrz false
    outsidePermission := .ReservedFrz false
    protector := some .StrongProtector }

/-- Reuse the existing reborrow core with a policy whose equality to the
source explicit protector policy is kernel checked below. -/
theorem protectionPolicy_eq :
    create ⟨true, true, true⟩ .Mutable .FnEntry ⟨false, false⟩ = some protectionPolicy := rfl

/-- Source protect-place retags first, then writes uninit through the newly
protected tag. Errors retain allocated tags, tree effects and write effects. -/
def protectInPlaceFunctionArgument [DecidableEq K] (hooks : Hooks K User)
    (place : MPlaceTy Provenance) : M K User Unit := do
  let protectedPlace ← if (← get).machine.borrowTracker.isSome then do
    let request ← hooks.preparePlaceProtection place
    let request := { request with
      typeShape := .reference
      typeFacts := ⟨true, true, true⟩
      referenceKind := .Mutable
      mode := .FnEntry
      config := ⟨false, false⟩
      originalProvenance := place.mplace.ptr.provenance }
    let (provenance, changed) ← applyRetag request
    unless changed do throw (.invalidProgram "place protection did not retag")
    -- Source tb_retag_place maps existing provenance: address-only pointers
    -- keep None even when allocation resolution produced a new concrete tag.
    let provenance ← match place.mplace.ptr.provenance with
      | none => pure none
      | some _ => match provenance with
        | some provenance => pure (some provenance)
        | none => throw (.invalidProgram "retag lost existing pointer provenance")
    pure { place with mplace := { place.mplace with ptr := { place.mplace.ptr with provenance } } }
    else pure place
  hooks.writeUninit protectedPlace

/-- Source on_stack_pop releases each live allocation's protector while all
protectors remain registered, commits partial tree mutations on failure, and
only removes global protectors once every release succeeds. -/
def beforeStackPopWithEnsure [DecidableEq K]
    (ensureTreeExtra : AllocId → M K User Unit) : M K User Unit := do
  let state ← get
  if state.machine.borrowTracker.isSome then
    let frame ← currentFrame
    let borrowFrame ← match frame.extra.borrowTracker with
      | none => throw (.invalidProgram "enabled borrow tracker missing frame state")
      | some frame => pure frame
    for (allocId, tag) in borrowFrame.protectedTags do
      let machine := (← get).machine
      let info ← match machine.memory.getAllocInfo allocId with
        | .error error => fail "protector allocation info" error
        | .ok info => pure info
      if info.kind == .liveData then
        ensureTreeExtra allocId
        let machine := (← get).machine
        let entry ← match machine.memory.live.find? fun entry => entry.1 == allocId with
          | none => throw (.invalidProgram "live protected allocation missing Tree Borrows extra")
          | some entry => pure entry.2
        let currentTracker ← match machine.borrowTracker with
          | none => throw (.invalidProgram "borrow tracker removed during protector release")
          | some tracker => pure tracker
        let released := entry.allocation.extra.releaseProtector tag currentTracker.global.protectedTags
        let memory ← match machine.memory.setLiveAllocation allocId (entry.allocation.setExtra released.tree) with
          | .error error => fail "protector tree update" error
          | .ok memory => pure memory
        modify fun state => { state with machine := { state.machine with memory } }
        match released.status with
        | .Released => pure ()
        | .AccessFailure _ status => throw (borrowAccessError status)
        | other => throw (.invalidProgram s!"protector release invariant: {reprStr other}")
    let state ← get
    let tracker ← match state.machine.borrowTracker with
      | none => throw (.invalidProgram "borrow tracker removed during stack pop")
      | some tracker => pure tracker
    set { state with machine := { state.machine with
      borrowTracker := some { tracker with global := tracker.global.endCall borrowFrame } } }

/-- Compatibility entrypoint for legacy request-based fixture dictionaries. -/
def beforeStackPop [DecidableEq K] (hooks : Hooks K User) : M K User Unit :=
  beforeStackPopWithEnsure hooks.ensureTreeExtra

/-- Direct adapters for the Call/Rvalue hooks use these EStateM functions.
This runner retains error-state effects in the canonical StepResult format. -/
def run (action : M K User A) (state : State K User) : StepResult (State K User) A :=
  Call.run action state

end Miri.Interpreter.MachineHooks
