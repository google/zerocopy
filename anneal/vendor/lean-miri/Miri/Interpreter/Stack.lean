import Miri.Interpreter.PlaceTypes
import Miri.Interpreter.BodyIdentity
import Miri.Interpreter.Instance

/-!
Source-shaped stack-frame state and local storage operations from pinned
`rustc_const_eval/src/interpret/stack.rs`. Interpreter callbacks remain
explicit for layout queries, machine hooks, allocation, and deallocation.
-/

namespace Miri.Interpreter

open Miri.ABI Miri.MIR Miri.Memory

variable {Prov Layout Extra State : Type}

inductive FrameLocation where
  | mir (location : MIR.Location)
  | unwinding (span : SpanRef)
  deriving DecidableEq, Repr

/-- Frames and call dispatch share the complete canonical instance identity. -/
abbrev FrameInstance := CallInstance

inductive ReturnContinuation where
  | goto (ret : Option BasicBlockId) (unwind : UnwindAction)
  | stop (cleanup : Bool)
  deriving DecidableEq, Repr

inductive ReturnAction where
  | normal
  | noJump
  | noCleanup
  deriving DecidableEq, Repr

inductive StackError where
  | emptyStack
  | rootFrameCondition (stackWasEmpty : Bool) (continuationIsStop : Bool)
  | invalidLocal (localId : LocalId) (localCount : Nat)
  | invalidLocation (location : MIR.Location)
  | cannotMakeReturnPlaceDead
  | localExpectedLive (localId : LocalId)
  | missingLocalType (localId : LocalId)
  | unsupportedUnexpectedLocalType (localId : LocalId) (ty : TyId)
  | unsizedLocalMissingMetadata (localId : LocalId)
  | metadataForSizedLocal (localId : LocalId)
  | machineHookFailure (message : String)
  | layoutFailure (message : String)
  | allocationFailure (message : String)
  | deallocationFailure (message : String)
  | localHasNoAllocationProvenance (localId : LocalId)
  deriving DecidableEq, Repr

instance : ToString StackError where
  toString
    | .emptyStack => "interpreter stack is empty"
    | .rootFrameCondition wasEmpty isStop =>
        s!"root frame condition failed (stack empty={wasEmpty}, stop continuation={isStop})"
    | .invalidLocal localId count => s!"local {localId} is outside local array of length {count}"
    | .invalidLocation location =>
        s!"MIR location {location.block}[{location.statementIndex}] is outside its body"
    | .cannotMakeReturnPlaceDead => "cannot make MIR return place dead"
    | .localExpectedLive localId => s!"local {localId} is dead"
    | .missingLocalType localId => s!"body has no type entry for local {localId}"
    | .unsupportedUnexpectedLocalType localId ty =>
        s!"local type classifier rejected unexpected type {ty} at local {localId}"
    | .unsizedLocalMissingMetadata localId =>
        s!"unsized local {localId} was made live without metadata"
    | .metadataForSizedLocal localId =>
        s!"sized local {localId} was made live with metadata"
    | .machineHookFailure message => s!"stack machine hook failed: {message}"
    | .layoutFailure message => s!"local layout resolution failed: {message}"
    | .allocationFailure message => s!"stack local allocation failed: {message}"
    | .deallocationFailure message => s!"stack local deallocation failed: {message}"
    | .localHasNoAllocationProvenance localId =>
        s!"indirect local {localId} has no allocation provenance"

structure Frame (Prov Layout Extra : Type) where
  body : MIR.Body
  bodyIdentity : BodyIdentity
  functionInstance : FrameInstance
  extra : Extra
  returnContinuation : ReturnContinuation
  returnPlace : RuntimeStackPlace Prov
  localsIdentity : LocalsIdentity
  locals : Array (LocalState Prov Layout)
  vaList : Array (MemoryOperandPlace Prov)
  trackCallerArg : Option SpanRef
  location : FrameLocation
  deriving DecidableEq, Repr

namespace Frame

/-- The source `push_stack_frame_raw` initialization: one dead, uncached
local state for each MIR local declaration. The other frame fields are
required inputs; no body, return place, instance, or machine extra is
invented here. -/
def create (loadedBody : LoadedBody) (functionInstance : FrameInstance) (extra : Extra)
    (returnContinuation : ReturnContinuation) (returnPlace : RuntimeStackPlace Prov)
    (initialSpan : SpanRef) (localsIdentity : LocalsIdentity) : Frame Prov Layout Extra :=
  { body := loadedBody.body
    bodyIdentity := loadedBody.identity
    functionInstance
    extra
    returnContinuation
    returnPlace
    localsIdentity
    locals := Array.replicate loadedBody.body.locals.size
      ({ value := .dead, layout := none } : LocalState Prov Layout)
    vaList := #[]
    trackCallerArg := none
    location := .unwinding initialSpan }

def currentLoc (self : Frame Prov Layout Extra) : FrameLocation := self.location

def getLocal (self : Frame Prov Layout Extra) (localId : LocalId) :
    Except StackError (LocalState Prov Layout) := do
  if h : localId < self.locals.size then
    return self.locals[localId]
  throw (.invalidLocal localId self.locals.size)

def getLocalOperand (self : Frame Prov Layout Extra) (localId : LocalId) :
    Except StackError (Operand Prov) := do
  let state ← self.getLocal localId
  state.access |>.mapError fun
    | .deadLocal => .localExpectedLive localId

/-- Replace only the `LocalValue`, preserving rustc's memoized layout. -/
def replaceLocalValue (self : Frame Prov Layout Extra) (localId : LocalId)
    (value : LocalValue Prov) : Except StackError (Frame Prov Layout Extra) := do
  if h : localId < self.locals.size then
    let state := self.locals[localId]
    let locals := self.locals.set localId { state with value } h
    return { self with locals }
  throw (.invalidLocal localId self.locals.size)

/-- `access_mut`-style update: dead locals fail, and the cached layout is
retained exactly. Callers performing actual writes must run their hooks first. -/
def setLocalOperand (self : Frame Prov Layout Extra) (localId : LocalId)
    (value : Operand Prov) : Except StackError (Frame Prov Layout Extra) := do
  let _ ← self.getLocalOperand localId
  self.replaceLocalValue localId (.live value)

def getLocalLayout (self : Frame Prov Layout Extra) (localId : LocalId) :
    Except StackError (Option Layout) := do
  return (← self.getLocal localId).layout

/-- Cache the source-computed layout only if no layout was already memoized.
The returned layout is the cached one when present, matching `layout_of_local`. -/
def getOrCacheLocalLayout (self : Frame Prov Layout Extra) (localId : LocalId)
    (computed : Layout) : Except StackError (Frame Prov Layout Extra × Layout) := do
  let state ← self.getLocal localId
  match state.layout with
  | some cached => return (self, cached)
  | none =>
    if h : localId < self.locals.size then
      let locals := self.locals.set localId { state with layout := some computed } h
      return ({ self with locals }, computed)
    throw (.invalidLocal localId self.locals.size)

def setLocation (self : Frame Prov Layout Extra) (location : FrameLocation) :
    Except StackError (Frame Prov Layout Extra) := do
  match location with
  | .unwinding _ => return { self with location }
  | .mir loc =>
    if h : loc.block < self.body.basicBlocks.size then
      let block := self.body.basicBlocks[loc.block]
      if loc.statementIndex ≤ block.statements.size then
        return { self with location }
    throw (.invalidLocation loc)

end Frame

structure Stack (Prov Layout Extra : Type) where
  frames : Array (Frame Prov Layout Extra)
  deriving DecidableEq, Repr

namespace Stack

def empty : Stack Prov Layout Extra := ⟨#[]⟩

def currentFrame? (self : Stack Prov Layout Extra) : Option (Frame Prov Layout Extra) :=
  self.frames.back?

def frameIndex (self : Stack Prov Layout Extra) : Except StackError Nat := do
  if self.frames.isEmpty then throw .emptyStack
  return self.frames.size - 1

def pushFrame (self : Stack Prov Layout Extra) (frame : Frame Prov Layout Extra) :
    Except StackError (Stack Prov Layout Extra) := do
  let wasEmpty := self.frames.isEmpty
  let isStop := match frame.returnContinuation with
    | .stop _ => true
    | .goto .. => false
  if wasEmpty != isStop then throw (.rootFrameCondition wasEmpty isStop)
  return { self with frames := self.frames.push frame }

def popFrame (self : Stack Prov Layout Extra) :
    Except StackError (Stack Prov Layout Extra × Frame Prov Layout Extra) := do
  match self.frames.back? with
  | none => throw .emptyStack
  | some frame => return ({ self with frames := self.frames.pop }, frame)

def updateCurrentLocation (self : Stack Prov Layout Extra) (location : FrameLocation) :
    Except StackError (Stack Prov Layout Extra) := do
  let frame ← match self.frames.back? with
    | none => throw .emptyStack
    | some frame => pure frame
  let updated ← frame.setLocation location
  let index := self.frames.size - 1
  if h : index < self.frames.size then
    return { self with frames := self.frames.set index updated h }
  throw .emptyStack

def getLocal (self : Stack Prov Layout Extra) (localId : LocalId) :
    Except StackError (LocalState Prov Layout) := do
  let frame ← match self.frames.back? with
    | none => throw .emptyStack
    | some frame => pure frame
  frame.getLocal localId

def getLocalOperand (self : Stack Prov Layout Extra) (localId : LocalId) :
    Except StackError (Operand Prov) := do
  let frame ← match self.frames.back? with
    | none => throw .emptyStack
    | some frame => pure frame
  frame.getLocalOperand localId

end Stack

/-- Stateful callback result: effects before an error are never rolled back. -/
structure StackEffect (State α : Type) where
  state : State
  outcome : Except StackError α

/-- Required compiler and machine operations. `veryTriviallySized` must implement
source's recursive type-kind classifier; `layout` includes normalization and
`from_known_layout`. Allocation/deallocation use stack memory kind. -/
structure LocalStorageHooks (Prov Layout Extra State : Type) where
  veryTriviallySized : TyId → Except StackError Bool
  layout : State → Frame Prov Layout Extra → LocalId → StackEffect State Layout
  isSized : Layout → Bool
  afterLocalWrite : State → LocalId → Bool → StackEffect State Unit
  allocateDyn : State → Layout → MemPlaceMeta Prov → StackEffect State (MemPlace Prov)
  deallocateStack : State → Pointer (Option Prov) → StackEffect State Unit

structure LocalStorageResult (Prov Layout Extra State : Type) where
  frame : Frame Prov Layout Extra
  state : State
  outcome : Except StackError Unit

namespace Frame

/-- Source `deallocate_local`: only indirect live locals own an allocation.
The required deallocator validates provenance and allocation identity. -/
def deallocateLocal (hooks : LocalStorageHooks Prov Layout Extra State)
    (state : State) (value : LocalValue Prov) : StackEffect State Unit :=
  match value with
  | .live (.indirect place) => hooks.deallocateStack state place.ptr
  | _ => ⟨state, .ok ()⟩

/-- Source `storage_dead` replaces the value before attempting deallocation. -/
def storageDead (self : Frame Prov Layout Extra) (state : State)
    (hooks : LocalStorageHooks Prov Layout Extra State) (localId : LocalId) :
    LocalStorageResult Prov Layout Extra State := Id.run do
  if localId == 0 then return ⟨self, state, .error .cannotMakeReturnPlaceDead⟩
  match self.getLocal localId with
  | .error error => return ⟨self, state, .error error⟩
  | .ok old =>
    match self.replaceLocalValue localId .dead with
    | .error error => return ⟨self, state, .error error⟩
    | .ok frame =>
      let result := deallocateLocal hooks state old.value
      return ⟨frame, result.state, result.outcome⟩

/-- Source `storage_live_dyn`, including lazy layout caching, allocation or
write hook before replacement, and replacement before old-value deallocation. -/
def storageLiveDyn (self : Frame Prov Layout Extra) (state : State)
    (hooks : LocalStorageHooks Prov Layout Extra State) (localId : LocalId)
    (metadata : MemPlaceMeta Prov) : LocalStorageResult Prov Layout Extra State := Id.run do
  let mut frame := self
  let mut state := state
  let old ← match frame.getLocal localId with
    | .error error => return ⟨frame, state, .error error⟩
    | .ok value => pure value
  let ty ← match frame.body.locals[localId]? with
    | none => return ⟨frame, state, .error (.missingLocalType localId)⟩
    | some ty => pure ty
  let trivial ← match hooks.veryTriviallySized ty with
    | .error error => return ⟨frame, state, .error error⟩
    | .ok value => pure value
  let mut unsizedLayout := none
  if !trivial then
    let layout ← match old.layout with
      | some layout => pure layout
      | none => do
        let result := hooks.layout state frame localId
        state := result.state
        match result.outcome with
        | .error error => return ⟨frame, state, .error error⟩
        | .ok layout =>
          match frame.getOrCacheLocalLayout localId layout with
          | .error error => return ⟨frame, state, .error error⟩
          | .ok (updated, cached) =>
            frame := updated
            pure cached
    if !hooks.isSized layout then unsizedLayout := some layout
  let operand ← match unsizedLayout with
    | some layout => do
      if !metadata.hasMeta then
        return ⟨frame, state, .error (.unsizedLocalMissingMetadata localId)⟩
      let allocated := hooks.allocateDyn state layout metadata
      state := allocated.state
      match allocated.outcome with
      | .error error => return ⟨frame, state, .error error⟩
      | .ok place => pure (Operand.indirect place)
    | none => do
      if metadata.hasMeta then
        return ⟨frame, state, .error (.metadataForSizedLocal localId)⟩
      let written := hooks.afterLocalWrite state localId true
      state := written.state
      match written.outcome with
      | .error error => return ⟨frame, state, .error error⟩
      | .ok () => pure (Operand.immediate .uninit)
  match frame.replaceLocalValue localId (.live operand) with
  | .error error => return ⟨frame, state, .error error⟩
  | .ok updated =>
    let result := deallocateLocal hooks state old.value
    return ⟨updated, result.state, result.outcome⟩

def storageLive (self : Frame Prov Layout Extra) (state : State)
    (hooks : LocalStorageHooks Prov Layout Extra State) (localId : LocalId) :
    LocalStorageResult Prov Layout Extra State :=
  self.storageLiveDyn state hooks localId .none

end Frame

/-- Whole-stack effects keep mutations made by a machine hook even on failure. -/
structure StackRunResult (Prov Layout Extra State α : Type) where
  stack : Stack Prov Layout Extra
  state : State
  outcome : Except StackError α

/-- Compiler-dependent and machine-dependent stages required by the source
frame lifecycle. Required constants and always-live analysis are explicit
obligations because `MIR.Body` does not store their compiler query results. -/
structure StackLifecycleHooks (Prov Layout Extra State : Type) where
  storage : LocalStorageHooks Prov Layout Extra State
  /-- Total ghost instrumentation at locals-buffer creation, not a source machine callback. -/
  freshLocalsIdentity : State → State × LocalsIdentity
  initFrame : State → Frame Prov Layout Unit → StackEffect State (Frame Prov Layout Extra)
  requiredConstants : Stack Prov Layout Extra → State → StackRunResult Prov Layout Extra State Unit
  afterPush : Stack Prov Layout Extra → State → StackRunResult Prov Layout Extra State Unit
  beforePop : Stack Prov Layout Extra → State → StackRunResult Prov Layout Extra State Unit
  afterPop : Stack Prov Layout Extra → State → Frame Prov Layout Extra → Bool →
    StackRunResult Prov Layout Extra State ReturnAction
  alwaysLiveVarsAndTemps : MIR.Body → Except StackError (Array LocalId)
  deallocateVararg : State → MemoryOperandPlace Prov → StackEffect State Unit

namespace Stack

/-- Source `push_stack_frame_raw`: init precedes insertion, while required
constant checks and after-push run with the new frame already on the stack. -/
def pushStackFrameRaw (self : Stack Prov Layout Extra) (state : State)
    (hooks : StackLifecycleHooks Prov Layout Extra State)
    (body : LoadedBody) (functionInstance : FrameInstance)
    (returnContinuation : ReturnContinuation) (returnPlace : RuntimeStackPlace Prov)
    (initialSpan : SpanRef) : StackRunResult Prov Layout Extra State Unit := Id.run do
  let isStop := match returnContinuation with | .stop _ => true | .goto .. => false
  if self.frames.isEmpty != isStop then
    return ⟨self, state, .error (.rootFrameCondition self.frames.isEmpty isStop)⟩
  let (state, localsIdentity) := hooks.freshLocalsIdentity state
  let initialized := hooks.initFrame state
    (Frame.create body functionInstance () returnContinuation returnPlace initialSpan localsIdentity)
  match initialized.outcome with
  | .error error => return ⟨self, initialized.state, .error error⟩
  | .ok frame =>
    let pushed : Stack Prov Layout Extra := ⟨self.frames.push frame⟩
    let checked := hooks.requiredConstants pushed initialized.state
    match checked.outcome with
    | .error error => return ⟨checked.stack, checked.state, .error error⟩
    | .ok () => return hooks.afterPush checked.stack checked.state

/-- Source `pop_stack_frame_raw`: before-pop effects precede removal. -/
def popStackFrameRaw (self : Stack Prov Layout Extra) (state : State)
    (hooks : StackLifecycleHooks Prov Layout Extra State) :
    StackRunResult Prov Layout Extra State (Frame Prov Layout Extra) := Id.run do
  let before := hooks.beforePop self state
  match before.outcome with
  | .error error => return ⟨before.stack, before.state, .error error⟩
  | .ok () =>
    match before.stack.popFrame with
    | .error error => return ⟨before.stack, before.state, .error error⟩
    | .ok (stack, frame) => return ⟨stack, before.state, .ok frame⟩

/-- Source `cleanup_stack_frame`: locals, then varargs, then machine after-pop.
Stop-without-cleanup skips both deallocation and the machine hook. -/
def cleanupStackFrame (self : Stack Prov Layout Extra) (state : State)
    (hooks : StackLifecycleHooks Prov Layout Extra State)
    (unwinding : Bool) (frame : Frame Prov Layout Extra) :
    StackRunResult Prov Layout Extra State ReturnAction := Id.run do
  let cleanup := match frame.returnContinuation with
    | .goto .. => true
    | .stop cleanup => cleanup
  if !cleanup then return ⟨self, state, .ok .noCleanup⟩
  let mut state := state
  for slot in frame.locals do
    let result := Frame.deallocateLocal hooks.storage state slot.value
    state := result.state
    match result.outcome with
    | .error error => return ⟨self, state, .error error⟩
    | .ok () => pure ()
  for arg in frame.vaList do
    let result := hooks.deallocateVararg state arg
    state := result.state
    match result.outcome with
    | .error error => return ⟨self, state, .error error⟩
    | .ok () => pure ()
  let result := hooks.afterPop self state frame unwinding
  match result.outcome with
  | .ok .noCleanup =>
    return ⟨result.stack, result.state,
      .error (.machineHookFailure "after_stack_pop returned NoCleanup during cleanup")⟩
  | _ => return result

/-- Source `push_stack_frame_done`: make return storage and always-live vars
live in source order, preserving each successful update on later failure. -/
def pushStackFrameDone (self : Stack Prov Layout Extra) (state : State)
    (hooks : StackLifecycleHooks Prov Layout Extra State) :
    StackRunResult Prov Layout Extra State Unit := Id.run do
  let mut stack := self
  let mut state := state
  let frame ← match stack.currentFrame? with
    | none => return ⟨stack, state, .error .emptyStack⟩
    | some frame => pure frame
  -- Return place is made live before querying always-live variables.
  let result := frame.storageLive state hooks.storage 0
  state := result.state
  stack := ⟨stack.frames.pop.push result.frame⟩
  match result.outcome with
  | .error error => return ⟨stack, state, .error error⟩
  | .ok () => pure ()
  let locals ← match hooks.alwaysLiveVarsAndTemps frame.body with
    | .error error => return ⟨stack, state, .error error⟩
    | .ok locals => pure locals
  for localId in locals do
    let frame ← match stack.currentFrame? with
      | none => return ⟨stack, state, .error .emptyStack⟩
      | some frame => pure frame
    let result := frame.storageLive state hooks.storage localId
    state := result.state
    stack := ⟨stack.frames.pop.push result.frame⟩
    match result.outcome with
    | .error error => return ⟨stack, state, .error error⟩
    | .ok () => pure ()
  match stack.updateCurrentLocation (.mir .start) with
  | .error error => return ⟨stack, state, .error error⟩
  | .ok updated => return ⟨updated, state, .ok ()⟩

end Stack

end Miri.Interpreter
