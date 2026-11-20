import Miri.Concurrency.WeakMemory
import Miri.Concurrency.DataRace

/-!
# Clock and store-buffer dispatch for atomic accesses

This module composes the source-backed vector-clock and weak-memory state
operations at the same callback boundaries as Miri's
`validate_atomic_op`/`buffered_atomic_*` hooks. It does not implement
`MPlaceTy`, pointer validation, scalar memory, scalar RMW operators, UB
diagnostics, or the interpreter's `allow_data_races_*` callbacks. Those remain
caller obligations. In particular, buffered writes and RMWs are post-memory-
write hooks; their arguments are the values already produced/written by the
interpreter. Atomic loads receive the already-read latest-in-modification-order
value used by Miri's fallback path.

The global state stores an optional per-allocation weak-memory map because Miri
attaches `StoreBufferAlloc` only when that backend is active. SC read metadata
is updated before lookup/choice, SC store metadata after validation, and SC
RMW read/write metadata after validation. Per-byte validation retains partial
cell/clock changes on an error and stops at the first failing byte.
-/

namespace Miri.Concurrency

open Miri.ABI Miri.Memory

/-- Full state slice needed by the pinned atomic clock/store-buffer hooks.
The caller owns interpreter memory and scheduler transitions. `none` means
this allocation has no weak-memory `AllocExtra` payload. -/
structure AtomicState (Value : Type) where
  global : GlobalState
  allocation : VClockAlloc
  weakMemoryAllocation : Option (StoreBufferAlloc Value)

/-- Explicit failures at the atomic clock/store-buffer boundary. -/
inductive AtomicDispatchError where
  | globalState (error : GlobalStateError)
  | validation (error : DataRaceResult)
  | syncClock (error : DataRaceResult)
  | storeBuffer (error : StoreBufferAllocError)
  | weakMemory (error : WeakMemoryError)
  | missingCreatedBuffer
  | syncOperationUnexpectedlySkipped
  deriving Repr

/-- State is returned alongside every success or failure, including an error
after `DedupRangeMap`/per-byte clock mutation. -/
structure AtomicTransition (Value Result : Type) where
  state : AtomicState Value
  outcome : Except AtomicDispatchError Result

/-- A source outdated-load diagnostic request. Rendering the pointer/span and
emitting Miri's non-halting diagnostic remain interpreter callbacks. -/
inductive WeakMemoryDiagnostic where
  | outdatedLoad
  deriving DecidableEq, Repr

/-- Value returned by the source buffered-load hook. `choice = none` denotes
the latest-memory fallback; a buffered `none` value still represents an
uninitialized selected store and is deliberately not coerced to a value. -/
structure AtomicReadResult (Value : Type) where
  value : Option Value
  choice : Option (StoreBuffer.LoadChoice Value)
  diagnostic : Option WeakMemoryDiagnostic

/-- A checked u64 byte count for the data-race allocation-range API. -/
private def dataRaceSize (size : Miri.ABI.Size) : ByteSize :=
  ByteSize.ofU64 size.bytes.toNat (by
    have h := UInt64.toNat_lt size.bytes
    omega)

/-- Convert the same allocation interval between Miri's `AllocRange` and the
data-race module's byte-count view. -/
def accessRangeOfAllocRange (range : AllocRange) : AccessRange :=
  { start := dataRaceSize range.start, size := dataRaceSize range.size }

def allocRangeOfAccessRange (range : AccessRange) : AllocRange :=
  { start := Miri.ABI.Size.ofBytes (UInt64.ofNat range.start.bytes)
    size := Miri.ABI.Size.ofBytes (UInt64.ofNat range.size.bytes) }

private def withGlobal (state : AtomicState Value) (global : GlobalState) :
    AtomicState Value := { state with global := global }

private def withAllocation (state : AtomicState Value) (allocation : VClockAlloc) :
    AtomicState Value := { state with allocation := allocation }

private def withWeakMemoryAllocation (state : AtomicState Value)
    (allocation : Option (StoreBufferAlloc Value)) : AtomicState Value :=
  { state with weakMemoryAllocation := allocation }

private def failure (state : AtomicState Value) (error : AtomicDispatchError) :
    AtomicTransition Value Result := { state := state, outcome := .error error }

private def success (state : AtomicState Value) (result : Result) :
    AtomicTransition Value Result := { state := state, outcome := .ok result }

/-- Run one source `validate_atomic_op` body. Its operation closure is applied
to each byte in increasing offset order by `VClockAlloc.runRange`; successful
operations conservatively increment once through
`GlobalState.maybePerformSyncOperation`. Race/error paths preserve the failed
cell and all earlier byte updates, but do not increment the outer clock. -/
def validateAtomicOp {Value : Type} (state : AtomicState Value)
    (threads : ThreadManager)
    (operation : VClockAlloc → ThreadClockSet → VectorIdx → VClockAlloc.RangeTransition) :
    AtomicTransition Value Unit := Id.run do
  if !state.global.raceDetecting then
    return success state ()
  let wrapped := state.global.maybePerformSyncOperation threads state.allocation
    fun index clocks allocation =>
      let transition := operation allocation clocks index
      let outcome := match transition.result with
        | .ok => .ok (true, ())
        | error => .error error
      { clocks := transition.thread
        external := transition.allocation
        outcome := outcome }
  let updated := { state with global := wrapped.global, allocation := wrapped.external }
  match wrapped.outcome with
  | .ok (some ()) => success updated ()
  | .ok none => failure updated .syncOperationUnexpectedlySkipped
  | .error (.inl error) => failure updated (.globalState error)
  | .error (.inr error) => failure updated (.validation error)

private def runAtomicLoadValidation (state : AtomicState Value)
    (threads : ThreadManager) (range : AccessRange) (ordering : AtomicReadOrd)
    (syncClock : Option VClock) : AtomicTransition Value Unit :=
  validateAtomicOp state threads fun allocation clocks index =>
    allocation.atomicLoad range clocks index range.size ordering syncClock

private def runAtomicStoreValidation (state : AtomicState Value)
    (threads : ThreadManager) (range : AccessRange) (ordering : AtomicWriteOrd) :
    AtomicTransition Value Unit :=
  validateAtomicOp state threads fun allocation clocks index =>
    allocation.atomicStore range clocks index range.size ordering

private def runAtomicRmwValidation (state : AtomicState Value)
    (threads : ThreadManager) (range : AccessRange) (ordering : AtomicRwOrd) :
    AtomicTransition Value Unit :=
  validateAtomicOp state threads fun allocation clocks index =>
    allocation.atomicRmw range clocks index range.size ordering

private def applyScRead (state : AtomicState Value) (threads : ThreadManager) :
    Except AtomicDispatchError (AtomicState Value) := do
  let global ← state.global.scRead threads |>.mapError AtomicDispatchError.globalState
  pure (withGlobal state global)

private def applyScWrite (state : AtomicState Value) (threads : ThreadManager) :
    Except AtomicDispatchError (AtomicState Value) := do
  let global ← state.global.scWrite threads |>.mapError AtomicDispatchError.globalState
  pure (withGlobal state global)

private def stateForStoreBufferTransition (state : AtomicState Value)
    (transition : StoreBufferAllocTransition Value) : AtomicState Value :=
  withWeakMemoryAllocation state (some transition.allocation)

/- The `buffered_atomic_read` hook, with an explicit legal-choice rank in
place of Miri's RNG. If a buffer exists, it chooses first, validates with that
store's synchronization clock, then records first-load metadata using the
post-validation clock. Otherwise it validates with `none` and returns the
caller-provided latest memory value. The source SC-read hook runs before store-buffer lookup when the allocation
has a weak-memory payload, including its missing-buffer fallback. -/
/-- A cut at the actual source RNG operation. SC metadata, buffer lookup and
active-clock errors precede the cut; fallback reads never request a draw. -/
inductive BufferedAtomicReadPlan (Value : Type) where
  | ready (result : AtomicReadResult Value)
  | select (handle : StoreBufferHandle Value) (clocks : ThreadClockSet)

def prepareBufferedAtomicRead {Value : Type} (state : AtomicState Value)
    (threads : ThreadManager) (range : AllocRange) (ordering : AtomicReadOrd)
    (latestInMemory : Value) :
    AtomicTransition Value (BufferedAtomicReadPlan Value) := Id.run do
  let accessRange := accessRangeOfAllocRange range
  let mut working := state
  -- Source sc_read is inside Some(alloc_buffers), but precedes its
  -- get_store_buffer lookup even when that lookup falls back to memory.
  if state.global.raceDetecting && state.global.weakMemory && state.weakMemoryAllocation.isSome && ordering == AtomicReadOrd.SeqCst then
    match applyScRead working threads with
    | .error error => return failure working error
    | .ok next => working := next

  let selectedBuffer : Except StoreBufferAllocError (Option (StoreBufferHandle Value)) :=
    if state.global.raceDetecting && state.global.weakMemory then
    match working.weakMemoryAllocation with
    | none => Except.ok none
    | some buffers => buffers.getStoreBuffer range
  else
    Except.ok none
  match selectedBuffer with
  | .error error => return failure working (.storeBuffer error)
  | .ok none =>
    let validation := runAtomicLoadValidation working threads accessRange ordering none
    match validation.outcome with
    | .error error => return failure validation.state error
    | .ok _ =>
      return success validation.state (.ready {
        value := some latestInMemory
        choice := none
        diagnostic := none })
  | .ok (some handle) =>
    let (_, clocks) ← match working.global.activeThreadState threads with
      | .error error => return failure working (.globalState error)
      | .ok active => pure active
    return success working (.select handle clocks)

/-- Continue the same source operation after selecting a supported store.
Callers commit prepare's state before requesting an effectful choice. -/
def finishBufferedAtomicRead {Value : Type} (working : AtomicState Value)
    (threads : ThreadManager) (range : AllocRange) (ordering : AtomicReadOrd)
    (handle : StoreBufferHandle Value) (clocks : ThreadClockSet) (choiceRank : Nat) :
    AtomicTransition Value (AtomicReadResult Value) := Id.run do
  let accessRange := accessRangeOfAllocRange range
  let choice ← match StoreBuffer.fetchAt handle.buffer
      (ordering == AtomicReadOrd.SeqCst) clocks choiceRank with
    | .error error => return failure working (.weakMemory error)
    | .ok choice => pure choice
  let validation := runAtomicLoadValidation working threads accessRange ordering
    (some choice.element.syncClock)
  match validation.outcome with
  | .error error => return failure validation.state error
  | .ok _ =>
    let (postIndex, postClocks) ← match validation.state.global.activeThreadState threads with
      | .error error => return failure validation.state (.globalState error)
      | .ok active => pure active
    let (buffer, value) ← match StoreBuffer.recordSelectedLoad handle.buffer choice
        postIndex postClocks (ordering == AtomicReadOrd.SeqCst) with
      | .error error => return failure validation.state (.weakMemory error)
      | .ok result => pure result
    let buffers ← match working.weakMemoryAllocation with
      | none => return failure validation.state .missingCreatedBuffer
      | some buffers => pure buffers
    let committed := buffers.commitStoreBuffer { handle with buffer := buffer }
    let nextState := match committed with
      | .ok next => withWeakMemoryAllocation validation.state (some next)
      | .error _ => validation.state
    let diagnostic :=
      if validation.state.global.trackOutdatedLoads &&
          choice.recency == LoadRecency.Outdated then
        some WeakMemoryDiagnostic.outdatedLoad
      else none
    match committed with
    | .error error => return failure nextState (.storeBuffer error)
    | .ok _ =>
      return success nextState {
        value := value
        choice := some choice
        diagnostic := diagnostic }


/-- Deterministic explicit-rank API retained as composition of the exact source
prefix and continuation. No choice is used on a fallback path. -/
def bufferedAtomicRead {Value : Type} (state : AtomicState Value)
    (threads : ThreadManager) (range : AllocRange) (ordering : AtomicReadOrd)
    (latestInMemory : Value) (choiceRank : Nat) : AtomicTransition Value (AtomicReadResult Value) :=
  let prepared := prepareBufferedAtomicRead state threads range ordering latestInMemory
  match prepared.outcome with
  | .error error => ⟨prepared.state,.error error⟩
  | .ok (.ready result) => ⟨prepared.state,.ok result⟩
  | .ok (.select handle clocks) =>
    finishBufferedAtomicRead prepared.state threads range ordering handle clocks choiceRank

/-- Port `weak_memory.rs::perform_read_on_buffered_latest`, used only after a
failed compare-exchange. Unlike ordinary buffered loads it never selects an
older store and does not run a second atomic validation. The source SC-read
mark occurs before the buffer lookup and therefore remains on a missing-buffer
fallback. -/
def performReadOnBufferedLatest {Value : Type} (state : AtomicState Value)
    (threads : ThreadManager) (range : AllocRange) (ordering : AtomicReadOrd) :
    AtomicTransition Value Unit := Id.run do
  let mut working := state
  if ordering == AtomicReadOrd.SeqCst then
    match applyScRead working threads with
    | .error error => return failure working error
    | .ok next => working := next
  if !working.global.weakMemory then return success working ()
  let some buffers := working.weakMemoryAllocation
    | return success working ()
  let handle ← match buffers.getStoreBuffer range with
    | .error error => return failure working (.storeBuffer error)
    | .ok none => return success working ()
    | .ok (some handle) => pure handle
  let (index, clocks) ← match working.global.activeThreadState threads with
    | .error error => return failure working (.globalState error)
    | .ok active => pure active
  let (buffer, _value) ← match StoreBuffer.readFromLastStore handle.buffer index clocks
      (ordering == AtomicReadOrd.SeqCst) with
    | .error error => return failure working (.weakMemory error)
    | .ok result => pure result
  let committed := buffers.commitStoreBuffer { handle with buffer := buffer }
  let nextState := match committed with
    | .ok next => withWeakMemoryAllocation working (some next)
    | .error _ => working
  match committed with
  | .error error => return failure nextState (.storeBuffer error)
  | .ok _ => return success nextState ()

/-- The failed compare-exchange path: source validates an atomic load with no
selected-store override, then records a load from the latest retained buffer
element. -/
def atomicCompareExchangeFailureState {Value : Type} (state : AtomicState Value)
    (threads : ThreadManager) (range : AllocRange) (ordering : AtomicReadOrd) :
    AtomicTransition Value Unit := Id.run do
  let validated := runAtomicLoadValidation state threads
    (accessRangeOfAllocRange range) ordering none
  match validated.outcome with
  | .error error => return failure validated.state error
  | .ok _ => return performReadOnBufferedLatest validated.state threads range ordering

/-- The `buffered_atomic_write` hook. Callers must have completed Miri's
`atomic_access_check`, vanilla memory write, and successful
`validate_atomic_store` before invoking it. The source SC-write mark occurs
before range sync-clock collection and buffer creation. -/
def bufferedAtomicWrite {Value : Type} (state : AtomicState Value)
    (threads : ThreadManager) (range : AllocRange) (ordering : AtomicWriteOrd)
    (value : Value) (initial : Option Value) : AtomicTransition Value Unit := Id.run do
  if !state.global.raceDetecting || !state.global.weakMemory then return success state ()
  let some buffers := state.weakMemoryAllocation
    | return success state ()
  let mut working := state
  if ordering == AtomicWriteOrd.SeqCst then
    match applyScWrite working threads with
    | .error error => return failure working error
    | .ok next => working := next
  let accessRange := accessRangeOfAllocRange range
  let syncClock ← match working.allocation.syncClock accessRange with
    | .error error => return failure working (.syncClock error)
    | .ok syncClock => pure syncClock
  let created := buffers.getOrCreateStoreBuffer range initial
  let createdState := stateForStoreBufferTransition working created
  let handle ← match created.outcome with
    | .error error => return failure createdState (.storeBuffer error)
    | .ok none => return failure createdState .missingCreatedBuffer
    | .ok (some handle) => pure handle
  let (index, clocks) ← match working.global.activeThreadState threads with
    | .error error => return failure createdState (.globalState error)
    | .ok active => pure active
  let nextBuffer := StoreBuffer.bufferedWrite handle.buffer value clocks index
    (ordering == AtomicWriteOrd.SeqCst) syncClock
  let commit := created.allocation.commitStoreBuffer { handle with buffer := nextBuffer }
  let nextState := match commit with
    | .ok next => withWeakMemoryAllocation working (some next)
    | .error _ => createdState
  match commit with
  | .error error => return failure nextState (.storeBuffer error)
  | .ok _ => return success nextState ()

/-- The `buffered_atomic_rmw` hook. Callers supply the already-read old value
and already-computed/written new value after a successful `validate_atomic_rmw`.
The hook marks both SC edges, reads metadata from the latest buffered store,
then appends the new store using the updated allocation sync clock. -/
def bufferedAtomicRmw {Value : Type} (state : AtomicState Value)
    (threads : ThreadManager) (range : AllocRange) (ordering : AtomicRwOrd)
    (oldValue newValue : Value) : AtomicTransition Value Unit := Id.run do
  if !state.global.raceDetecting || !state.global.weakMemory then return success state ()
  let some buffers := state.weakMemoryAllocation
    | return success state ()
  let mut working := state
  if ordering == AtomicRwOrd.SeqCst then
    match applyScRead working threads with
    | .error error => return failure working error
    | .ok next => working := next
    match applyScWrite working threads with
    | .error error => return failure working error
    | .ok next => working := next
  let accessRange := accessRangeOfAllocRange range
  let syncClock ← match working.allocation.syncClock accessRange with
    | .error error => return failure working (.syncClock error)
    | .ok syncClock => pure syncClock
  let created := buffers.getOrCreateStoreBuffer range (some oldValue)
  let createdState := stateForStoreBufferTransition working created
  let handle ← match created.outcome with
    | .error error => return failure createdState (.storeBuffer error)
    | .ok none => return failure createdState .missingCreatedBuffer
    | .ok (some handle) => pure handle
  let (index, clocks) ← match working.global.activeThreadState threads with
    | .error error => return failure createdState (.globalState error)
    | .ok active => pure active
  let (readBuffer, _readValue) ← match StoreBuffer.readFromLastStore handle.buffer
      index clocks (ordering == AtomicRwOrd.SeqCst) with
    | .error error => return failure createdState (.weakMemory error)
    | .ok result => pure result
  let appended := StoreBuffer.bufferedWrite readBuffer newValue clocks index
    (ordering == AtomicRwOrd.SeqCst) syncClock
  let commit := created.allocation.commitStoreBuffer { handle with buffer := appended }
  let nextState := match commit with
    | .ok next => withWeakMemoryAllocation working (some next)
    | .error _ => createdState
  match commit with
  | .error error => return failure nextState (.storeBuffer error)
  | .ok _ => return success nextState ()

/-- Compose Miri's `validate_atomic_store` then `buffered_atomic_write` state
hooks. The interpreter must already have performed its normal memory write;
this function does not create or mutate the scalar memory allocation. -/
def atomicStoreState {Value : Type} (state : AtomicState Value)
    (threads : ThreadManager) (range : AllocRange) (ordering : AtomicWriteOrd)
    (value : Value) (initial : Option Value) : AtomicTransition Value Unit := Id.run do
  let validated := runAtomicStoreValidation state threads (accessRangeOfAllocRange range) ordering
  match validated.outcome with
  | .error error => return failure validated.state error
  | .ok _ => return bufferedAtomicWrite validated.state threads range ordering value initial

/-- Compose Miri's `validate_atomic_rmw` then `buffered_atomic_rmw` state
hooks. Actual memory read, RMW scalar computation, and write remain caller
operations performed before this post-write state transition. -/
def atomicRmwState {Value : Type} (state : AtomicState Value)
    (threads : ThreadManager) (range : AllocRange) (ordering : AtomicRwOrd)
    (oldValue newValue : Value) : AtomicTransition Value Unit := Id.run do
  let validated := runAtomicRmwValidation state threads (accessRangeOfAllocRange range) ordering
  match validated.outcome with
  | .error error => return failure validated.state error
  | .ok _ => return bufferedAtomicRmw validated.state threads range ordering oldValue newValue

end Miri.Concurrency
