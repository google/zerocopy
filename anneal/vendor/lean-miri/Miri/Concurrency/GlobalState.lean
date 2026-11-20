import Miri.Concurrency.DataRace
import Miri.Concurrency.Thread

/-! Ordinary-lifecycle reuse boundary: thread termination publishes the old
release snapshot and then increments its own vector coordinate. Join acquires
only the snapshot, so a live caller can remain one tick behind the terminated
candidate. A synthetic safe candidate tests the hook/predicate, not reachability
through ordinary spawn/join. See MiriTests/DataRace/ThreadClockReuseReachability.lean. -/

/-!
# Pinned Miri global vector-clock state

This module models the `GlobalState` thread/clock bookkeeping and synchronization
hooks in `src/concurrency/data_race.rs`. It preserves the thread-to-vector
mapping, re-use set, termination snapshots, all five per-thread clocks, SC
fence/write clocks, race-detection flags, and configuration bits. A reusable
index is selected through an explicit choice from the exact set of candidates
accepted by Miri's predicate; the source uses `FxHashSet` iteration order,
which is an implementation detail, so this relation exposes every safe member
instead of inventing a stable order.

The methods here do not implement interpreter callbacks, TLS cleanup, atomic
memory-cell validation, allocation metadata, diagnostics, or scheduler actions.
`threadTerminated` is called only after the caller has completed Miri's prior
TLS cleanup and marked the active thread terminated. Such cross-subsystem
actions remain explicit preconditions at the integration boundary.
-/

namespace Miri.Concurrency

/-- Additional source metadata retained for every ever-created ThreadId. -/
structure ThreadExtraState where
  vectorIndex : Option VectorIdx := none
  terminationVectorClock : Option VClock := none
  deriving Repr, Inhabited

inductive GlobalStateError where
  | thread (error : ThreadError)
  | clock (error : ClockError)
  | missingThreadMetadata (thread : ThreadId)
  | missingVectorClock (index : VectorIdx)
  | missingVectorInfo (index : VectorIdx)
  | missingTerminationClock (thread : ThreadId)
  | threadNotTerminated (thread : ThreadId)
  | childIsActiveThread
  | invalidReuseChoice
  deriving Repr

/-- State returned by an operation body executed under Miri's synchronized
operation wrapper. The body may update clocks and external memory before
returning an error, so those states remain available on the error path. -/
structure SyncOperationBodyResult (External Error Value : Type) where
  clocks : ThreadClockSet
  external : External
  outcome : Except Error (Bool × Value)

/-- Pinned Miri fields needed by concurrency synchronization and reuse. -/
structure GlobalState where
  multiThreaded : Bool := false
  ongoingActionDataRaceFree : Bool := false
  vectorClocks : List ThreadClockSet
  vectorInfo : List ThreadId
  threadInfo : List ThreadExtraState
  reuseCandidates : List VectorIdx
  lastScFence : VClock := .default
  lastScWritePerThread : VClock := .default
  trackOutdatedLoads : Bool
  weakMemory : Bool
  deriving Repr

/-- Result of `maybe_perform_sync_operation`. `none` means Miri's
single-threaded fast path skipped the body entirely. -/
structure SyncOperationTransition (Error External Value : Type) where
  global : GlobalState
  external : External
  outcome : Except (Sum GlobalStateError Error) (Option Value)

namespace GlobalState

private def getAt? {α : Type} : List α → Nat → Option α
  | [], _ => none
  | value :: _, 0 => some value
  | _ :: rest, index + 1 => getAt? rest index

private def setAt? {α : Type} : List α → Nat → α → Option (List α)
  | [], _, _ => none
  | _ :: rest, 0, value => some (value :: rest)
  | head :: rest, index + 1, value => do
      let updated ← setAt? rest index value
      pure (head :: updated)

private def containsIndex (indices : List VectorIdx) (index : VectorIdx) : Bool :=
  indices.contains index

def initial (trackOutdatedLoads weakMemory : Bool) : GlobalState :=
  { vectorClocks := [ThreadClockSet.default]
    vectorInfo := [ThreadId.MAIN_THREAD]
    threadInfo := [{ vectorIndex := some (VectorIdx.ofU32 0 (by decide)),
                     terminationVectorClock := none }]
    reuseCandidates := []
    trackOutdatedLoads := trackOutdatedLoads
    weakMemory := weakMemory }

def raceDetecting (state : GlobalState) : Bool :=
  state.multiThreaded && !state.ongoingActionDataRaceFree

def withDataRaceFreeAction (state : GlobalState) (active : Bool) : GlobalState :=
  { state with ongoingActionDataRaceFree := active }

private def threadExtra? (state : GlobalState) (thread : ThreadId) :
    Option ThreadExtraState := getAt? state.threadInfo thread.toNat

private def threadIndex (state : GlobalState) (thread : ThreadId) :
    Except GlobalStateError VectorIdx := do
  let extra ← match threadExtra? state thread with
    | none => .error (.missingThreadMetadata thread)
    | some extra => .ok extra
  match extra.vectorIndex with
  | none => .error (.missingThreadMetadata thread)
  | some index => .ok index

private def clocksAt (state : GlobalState) (index : VectorIdx) :
    Except GlobalStateError ThreadClockSet :=
  match getAt? state.vectorClocks index.toNat with
  | none => .error (.missingVectorClock index)
  | some clocks => .ok clocks

def activeThreadIndex (state : GlobalState) (threads : ThreadManager) :
    Except GlobalStateError VectorIdx := do
  threadIndex state threads.activeThread

def activeThreadState (state : GlobalState) (threads : ThreadManager) :
    Except GlobalStateError (VectorIdx × ThreadClockSet) := do
  let index ← activeThreadIndex state threads
  let clocks ← clocksAt state index
  pure (index, clocks)

/-- Run the same callback boundary as Miri's `maybe_perform_sync_operation`.
The callback is skipped when multithreaded tracking is off. Otherwise its
clock and external-state mutations survive failure, and a normal `true` result
causes one clock increment after the callback. -/
def maybePerformSyncOperation {External Error Value : Type}
    (state : GlobalState) (threads : ThreadManager) (external : External)
    (body : VectorIdx → ThreadClockSet → External →
      SyncOperationBodyResult External Error Value) :
    SyncOperationTransition Error External Value := Id.run do
  if !state.multiThreaded then
    return { global := state, external := external, outcome := .ok none }
  let active ← match activeThreadState state threads with
    | .error error =>
        return { global := state, external := external, outcome := .error (.inl error) }
    | .ok value => pure value
  let (index, clocks) := active
  let bodyResult := body index clocks external
  let stateAfterBody := match setAt? state.vectorClocks index.toNat bodyResult.clocks with
    | none => state
    | some vectorClocks => { state with vectorClocks := vectorClocks }
  if (setAt? state.vectorClocks index.toNat bodyResult.clocks).isNone then
    return ⟨stateAfterBody, bodyResult.external,
      .error (.inl (.missingVectorClock index))⟩
  match bodyResult.outcome with
  | .error error =>
      return ⟨stateAfterBody, bodyResult.external, .error (.inr error)⟩
  | .ok (shouldIncrement, value) =>
      if !shouldIncrement then
        return ⟨stateAfterBody, bodyResult.external, .ok (some value)⟩
      let nextClocks ← match bodyResult.clocks.incrementClock index with
        | .error error =>
            return ⟨stateAfterBody, bodyResult.external, .error (.inl (.clock error))⟩
        | .ok next => pure next
      match setAt? stateAfterBody.vectorClocks index.toNat nextClocks with
      | none =>
          return ⟨stateAfterBody, bodyResult.external,
            .error (.inl (.missingVectorClock index))⟩
      | some vectorClocks =>
          return ⟨{ stateAfterBody with vectorClocks := vectorClocks },
            bodyResult.external, .ok (some value)⟩

private def safeReuseCandidate (state : GlobalState) (candidate : VectorIdx) : Bool :=
  match getAt? state.vectorClocks candidate.toNat with
  | none => false
  | some targetClock =>
    let targetTime := targetClock.clock.index candidate
    state.vectorClocks.zipIdx.all fun (clock, rawIndex) =>
      match VectorIdx.ofNat rawIndex with
      | .error _ => false
      | .ok clockIndex =>
        let caughtUp := targetTime.time ≤ (clock.clock.index candidate).time
        let terminated := containsIndex state.reuseCandidates clockIndex
        caughtUp || terminated

/-- Every candidate accepted by the source's all-clocks predicate, in the
existing collection's order. Selection remains explicit because the original
`FxHashSet` traversal order is not a language-level semantic guarantee. -/
def reusableCandidates (state : GlobalState) : List VectorIdx :=
  state.reuseCandidates.filter (safeReuseCandidate state)

private def growThreadInfo (info : List ThreadExtraState) (length : Nat) :
    List ThreadExtraState :=
  info ++ List.replicate (length - info.length) default

private def removeReuseCandidate (candidates : List VectorIdx) (index : VectorIdx) :
    List VectorIdx := candidates.filter (fun candidate => candidate != index)

/-- Apply Miri's thread-created hook after the `ThreadManager` has created the
child. `reuseChoice` must be a safe candidate when any exist, and must be
`none` when none exist. This preserves Miri's join-before-increment ordering. -/
def threadCreated (state : GlobalState) (threads : ThreadManager)
    (child : ThreadId) (reuseChoice : Option VectorIdx) :
    Except GlobalStateError GlobalState := do
  if child == threads.activeThread then .error .childIsActiveThread
  if (threads.thread? child).isNone then .error (.thread (.invalidId))
  let currentIndex ← threadIndex state threads.activeThread
  let safe := reusableCandidates state
  if safe.isEmpty then
    if reuseChoice.isSome then .error .invalidReuseChoice
  else
    if reuseChoice.isNone then .error .invalidReuseChoice
  match reuseChoice with
  | some selected =>
    if !safe.contains selected then .error .invalidReuseChoice
  | none => pure ()

  let threadInfo := growThreadInfo state.threadInfo (child.toNat + 1)
  let (createdIndex, vectorInfo, vectorClocks, reuseCandidates, threadInfo) ←
    match reuseChoice with
    | some selected =>
      let oldThread? := getAt? state.vectorInfo selected.toNat
      let oldClocks? := getAt? state.vectorClocks selected.toNat
      match oldThread?, oldClocks? with
      | some oldThread, some oldClocks =>
        let oldIndexIncremented ← match oldClocks.incrementClock selected with
          | .error error => .error (.clock error)
          | .ok clocks => .ok clocks
        let vectorInfo ← match setAt? state.vectorInfo selected.toNat child with
          | none => .error (.missingVectorInfo selected)
          | some result => .ok result
        let vectorClocks ← match setAt? state.vectorClocks selected.toNat oldIndexIncremented with
          | none => .error (.missingVectorClock selected)
          | some result => .ok result
        let oldExtra ← match getAt? threadInfo oldThread.toNat with
          | none => .error (.missingThreadMetadata oldThread)
          | some extra => .ok extra
        let threadInfo ← match setAt? threadInfo oldThread.toNat
            { oldExtra with vectorIndex := none } with
          | none => .error (.missingThreadMetadata oldThread)
          | some result => .ok result
        pure (selected, vectorInfo, vectorClocks,
          removeReuseCandidate state.reuseCandidates selected, threadInfo)
      | none, _ => .error (.missingVectorInfo selected)
      | _, none => .error (.missingVectorClock selected)
    | none => do
      let createdIndex ← match VectorIdx.ofNat state.vectorInfo.length with
        | .error error => .error (.clock error)
        | .ok index => .ok index
      pure (createdIndex, state.vectorInfo ++ [child],
        state.vectorClocks ++ [ThreadClockSet.default], state.reuseCandidates, threadInfo)

  let childExtra ← match getAt? threadInfo child.toNat with
    | none => .error (.missingThreadMetadata child)
    | some extra => .ok extra
  let threadInfo ← match setAt? threadInfo child.toNat
      { childExtra with vectorIndex := some createdIndex } with
    | none => .error (.missingThreadMetadata child)
    | some result => .ok result

  if currentIndex == createdIndex then .error .childIsActiveThread
  let current ← match getAt? vectorClocks currentIndex.toNat with
    | none => .error (.missingVectorClock currentIndex)
    | some clocks => .ok clocks
  let created ← match getAt? vectorClocks createdIndex.toNat with
    | none => .error (.missingVectorClock createdIndex)
    | some clocks => .ok clocks
  let created := created.joinWith current
  let current ← match current.incrementClock currentIndex with
    | .error error => .error (.clock error)
    | .ok clocks => .ok clocks
  let created ← match created.incrementClock createdIndex with
    | .error error => .error (.clock error)
    | .ok clocks => .ok clocks
  let vectorClocks ← match setAt? vectorClocks currentIndex.toNat current with
    | none => .error (.missingVectorClock currentIndex)
    | some result => .ok result
  let vectorClocks ← match setAt? vectorClocks createdIndex.toNat created with
    | none => .error (.missingVectorClock createdIndex)
    | some result => .ok result
  pure { state with
    multiThreaded := true
    vectorClocks := vectorClocks
    vectorInfo := vectorInfo
    threadInfo := threadInfo
    reuseCandidates := reuseCandidates }

/-- Acquire a clock into the active thread without incrementing its timestamp. -/
def acquireClock (state : GlobalState) (threads : ThreadManager) (clock : VClock) :
    Except GlobalStateError GlobalState := do
  let (index, current) ← activeThreadState state threads
  let next := { current with clock := current.clock.join clock }
  match setAt? state.vectorClocks index.toNat next with
  | none => .error (.missingVectorClock index)
  | some vectorClocks => .ok { state with vectorClocks := vectorClocks }

/-- Release snapshot: return the old clock and increment the active clock. -/
def releaseClock (state : GlobalState) (threads : ThreadManager) :
    Except GlobalStateError (GlobalState × VClock) := do
  let (index, current) ← activeThreadState state threads
  let snapshot := current.clock
  let next ← match current.incrementClock index with
    | .error error => .error (.clock error)
    | .ok clocks => .ok clocks
  match setAt? state.vectorClocks index.toNat next with
  | none => .error (.missingVectorClock index)
  | some vectorClocks => .ok ({ state with vectorClocks := vectorClocks }, snapshot)

/-- Thread termination hook. The manager must already have marked the active
thread Terminated and completed the preceding TLS cleanup effects. -/
def threadTerminated (state : GlobalState) (threads : ThreadManager) :
    Except GlobalStateError GlobalState := do
  let thread := threads.activeThread
  let active ← match threads.activeThread? with
    | none => .error (.thread (.activeIdOutOfBounds thread))
    | some record => .ok record
  if !active.isTerminated then .error (.threadNotTerminated thread)
  let index ← threadIndex state thread
  let (released, snapshot) ← releaseClock state threads
  let extra ← match getAt? released.threadInfo thread.toNat with
    | none => .error (.missingThreadMetadata thread)
    | some extra => .ok extra
  let threadInfo ← match setAt? released.threadInfo thread.toNat
      { extra with terminationVectorClock := some snapshot } with
    | none => .error (.missingThreadMetadata thread)
    | some result => .ok result
  let reuseCandidates :=
    if containsIndex released.reuseCandidates index then released.reuseCandidates
    else released.reuseCandidates ++ [index]
  pure { released with threadInfo := threadInfo, reuseCandidates := reuseCandidates }

/-- Join a terminated thread. The caller supplies the post-join ThreadManager,
whose live-thread count controls Miri's multi-threaded fast-path disabling. -/
def threadJoined (state : GlobalState) (threadsAfterJoin : ThreadManager)
    (joinee : ThreadId) : Except GlobalStateError GlobalState := do
  let extra ← match threadExtra? state joinee with
    | none => .error (.missingThreadMetadata joinee)
    | some extra => .ok extra
  let joinClock ← match extra.terminationVectorClock with
    | none => .error (.missingTerminationClock joinee)
    | some clock => .ok clock
  let acquired ← acquireClock state threadsAfterJoin joinClock
  match extra.vectorIndex with
  | none => pure acquired
  | some candidateIndex =>
    if threadsAfterJoin.liveThreadCount != 1 then pure acquired
    else
      let current ← clocksAt acquired candidateIndex
      let allTerminationsHappenBefore := acquired.vectorClocks.zipIdx.all fun (clock, rawIndex) =>
        match VectorIdx.ofNat rawIndex with
        | .error _ => false
        | .ok index =>
          (clock.clock.index index).time ≤ (current.clock.index index).time
      if allTerminationsHappenBefore then
        pure { acquired with multiThreaded := false }
      else pure acquired

/-- SC atomic store hook: save the active thread's clock at its own coordinate. -/
def scWrite (state : GlobalState) (threads : ThreadManager) :
    Except GlobalStateError GlobalState := do
  let (index, clocks) ← activeThreadState state threads
  let lastScWritePerThread ← match state.lastScWritePerThread.setAtIndex clocks.clock index with
    | .error error => .error (.clock error)
    | .ok clock => .ok clock
  pure { state with lastScWritePerThread := lastScWritePerThread }

/-- SC atomic load hook: remember the global last-SC-fence clock in this thread. -/
def scRead (state : GlobalState) (threads : ThreadManager) :
    Except GlobalStateError GlobalState := do
  let (index, clocks) ← activeThreadState state threads
  let next := { clocks with readSeqCst := clocks.readSeqCst.join state.lastScFence }
  match setAt? state.vectorClocks index.toNat next with
  | none => .error (.missingVectorClock index)
  | some vectorClocks => .ok { state with vectorClocks := vectorClocks }

/-- Apply the exact GlobalState fence ordering: acquire fence, SeqCst global
RMW-style join, last-SC-write metadata, then release fence. If the source's
multi-threaded flag is false, `maybe_perform_sync_operation` is a no-op. -/
def atomicFence (state : GlobalState) (threads : ThreadManager)
    (ordering : AtomicFenceOrd) : Except GlobalStateError GlobalState := do
  if !state.multiThreaded then pure state
  else
    let (index, clocks) ← activeThreadState state threads
    let mut clocks := clocks
    let mut lastScFence := state.lastScFence
    if ordering != .Release then
      clocks := clocks.applyAcquireFence
    if ordering == .SeqCst then
      lastScFence := lastScFence.join clocks.clock
      clocks := { clocks with clock := clocks.clock.join lastScFence }
      clocks := { clocks with writeSeqCst :=
        clocks.writeSeqCst.join state.lastScWritePerThread }
    if ordering != .Acquire then
      clocks := clocks.applyReleaseFence
    if ordering != .Acquire then
      let nextClocks ← match clocks.incrementClock index with
        | .error error => .error (.clock error)
        | .ok updated => .ok updated
      clocks := nextClocks
    let vectorClocks ← match setAt? state.vectorClocks index.toNat clocks with
      | none => .error (.missingVectorClock index)
      | some vectorClocks => .ok vectorClocks
    pure { state with vectorClocks := vectorClocks, lastScFence := lastScFence }

end GlobalState

end Miri.Concurrency
