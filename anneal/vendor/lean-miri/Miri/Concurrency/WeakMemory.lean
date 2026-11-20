import Miri.Concurrency.GlobalState
import Miri.DataStructures.RangeObjectMap
import Miri.Memory.AllocRange
/-!
# Per-location weak-memory store buffers from pinned Miri

This module ports the local `StoreBuffer` state and operations in the pinned
`upstream/miri-source/src/concurrency/weak_memory.rs` (Miri revision
`7fa591d7d4dd9af8154becbc8332f8096f8323b1`, Git blob
`4838144d1d8625379f28ead9864bcfea72a16cc0`). It preserves modification-order
entries, their per-store synchronization clocks, SC marks, values, and
first-load metadata, plus Miri's 128-entry limit and all `fetch_store`
candidate restrictions.

Miri chooses uniformly at random from the legal candidate set. Lean models
the support of that choice as a finite list and permits an explicit rank to
select any member; it does not model probabilities. Enumerating the list is an
over-approximation of individual source executions by construction: every
selected result is a member of the exact source filter's set, and every source
result lies in that set. No single random seed is used to justify a safety
claim.

Interpreter memory updates, RNG distribution, atomic-access validation
callback, diagnostics, and Miri's complete operation dispatch are outside this
local slice. `bufferedReadAt` accepts the validation transition explicitly and runs
it after selecting an entry but before recording load metadata, matching the
source order. Scalar values are abstracted as a Lean type parameter; `none`
is the source's uninitialized scalar case. This is not a complete Rust or Miri
weak-memory semantics.
-/

namespace Miri.Concurrency

/-- Maximum number of retained modification-order entries in Miri. -/
def STORE_BUFFER_LIMIT : Nat := 128

/-- Whether a selected weak-memory load returned the newest modification-order
entry or an older one. -/
inductive LoadRecency where
  | Latest
  | Outdated
  deriving DecidableEq, Repr, Inhabited

/-- Explicit failures for invalid local buffer/rank operations. Normal buffers
cannot be empty or exceed the source capacity. -/
inductive WeakMemoryError where
  | emptyStoreBuffer
  | bufferTooLong
  | choiceOutOfBounds
  | selectedIndexOutOfBounds
  deriving DecidableEq, Repr, Inhabited

/-- First-load metadata stored on each source store element. The list is a
finite-map representation keyed by `VectorIdx.toNat`; insertion preserves the
first timestamp, as `FxHashMap::try_insert` does. -/
structure LoadInfo where
  timestamps : List (VectorIdx × VTimestamp) := []
  scLoaded : Bool := false
  deriving Repr, Inhabited

namespace LoadInfo

/-- Read the recorded first timestamp for one thread, if present. -/
def timestampFor? (info : LoadInfo) (index : VectorIdx) : Option VTimestamp :=
  match info.timestamps.find? (fun pair => pair.1.toNat == index.toNat) with
  | none => none
  | some pair => some pair.2

/-- Record a load by a thread only if that thread has not loaded this element
before, and remember whether any load was SC. -/
def record (info : LoadInfo) (index : VectorIdx) (clock : VClock)
    (isSeqCst : Bool) : LoadInfo :=
  let timestamps :=
    if (info.timestampFor? index).isSome then info.timestamps
    else info.timestamps ++ [(index, clock.index index)]
  { timestamps := timestamps, scLoaded := info.scLoaded || isSeqCst }

end LoadInfo

/-- One store in a location's modification order. `Value` abstracts Rust's
`Scalar`; `none` is an uninitialized stored value. -/
structure StoreElement (Value : Type) where
  storeThread : VectorIdx
  storeTimestamp : VTimestamp
  syncClock : VClock
  isSeqCst : Bool
  val : Option Value
  loadInfo : LoadInfo := {}

namespace StoreElement

/-- Whether an earlier recorded load from this element happens before the
current store, matching Miri's SC-store closure condition. -/
def hasLoadBefore (element : StoreElement Value) (clock : VClock) : Bool :=
  element.loadInfo.timestamps.any fun pair =>
    decide (pair.2.time ≤ (clock.index pair.1).time)

/-- Apply Miri's ATOMIC LOAD IMPL metadata update and return the stored value. -/
def loadImpl (element : StoreElement Value) (index : VectorIdx)
    (clocks : ThreadClockSet) (isSeqCst : Bool) : StoreElement Value × Option Value :=
  ({ element with loadInfo := element.loadInfo.record index clocks.clock isSeqCst }, element.val)

end StoreElement

/-- A nonempty source store buffer. `oldest` plus `newer` stores the exact
oldest-to-newest modification order; the proof field enforces the source's
128-entry retention bound. -/
structure StoreBuffer (Value : Type) where
  oldest : StoreElement Value
  newer : List (StoreElement Value)
  bounded : newer.length < STORE_BUFFER_LIMIT

namespace StoreBuffer

/-- The retained entries in modification order. -/
def entries (buffer : StoreBuffer Value) : List (StoreElement Value) :=
  buffer.oldest :: buffer.newer

/-- The latest modification-order element. -/
def last (buffer : StoreBuffer Value) : StoreElement Value :=
  match buffer.newer.getLast? with
  | some element => element
  | none => buffer.oldest

/-- Construct the source's initial non-atomic store, which has no acquireable
clock and is not SC. Its thread and timestamp are the source's zero values. -/
def new (initial : Option Value) : StoreBuffer Value :=
  { oldest := {
      storeThread := VectorIdx.ofU32 0 (by decide)
      storeTimestamp := VTimestamp.ZERO
      syncClock := VClock.default
      isSeqCst := false
      val := initial
      loadInfo := {} }
    newer := []
    bounded := by simp [STORE_BUFFER_LIMIT] }

private def indexedEntries : List (StoreElement Value) → Nat → List (Nat × StoreElement Value)
  | [], _ => []
  | element :: rest, index =>
      (index, element) :: indexedEntries rest (index + 1)
termination_by values _index => values.length
decreasing_by simp_wf

/-- Entries in newest-to-oldest order with their positions in `entries`. -/
private def reverseIndexed (buffer : StoreBuffer Value) : List (Nat × StoreElement Value) :=
  (indexedEntries buffer.entries 0).reverse

/-- Exact blocking condition used by Miri's `fetch_store` prefix scan. -/
def blocksEarlier (element : StoreElement Value) (isSeqCst : Bool)
    (clocks : ThreadClockSet) : Bool :=
  decide (element.storeTimestamp.time ≤ (clocks.clock.index element.storeThread).time) ||
  element.loadInfo.timestamps.any (fun pair =>
    decide (pair.2.time ≤ (clocks.clock.index pair.1).time)) ||
  (element.isSeqCst && decide
    (element.storeTimestamp.time ≤ (clocks.writeSeqCst.index element.storeThread).time)) ||
  (isSeqCst && decide
    (element.storeTimestamp.time ≤ (clocks.readSeqCst.index element.storeThread).time)) ||
  (isSeqCst && element.loadInfo.scLoaded)

/-- The inclusive newest-to-oldest prefix examined by source `take_while`:
the first blocking element is included, then older entries are excluded. -/
private def candidatePrefix (isSeqCst : Bool) (clocks : ThreadClockSet) :
    List (Nat × StoreElement Value) → List (Nat × StoreElement Value)
  | [] => []
  | head :: tail =>
      head :: if blocksEarlier head.2 isSeqCst clocks then []
              else candidatePrefix isSeqCst clocks tail
termination_by values => values.length
decreasing_by simp_wf

/-- Keep all non-SC candidates and only the newest SC candidate, exactly as
Miri's post-prefix `.filter` does for an SC load. -/
private def filterSeqCst (isSeqCst foundSc : Bool) :
    List (Nat × StoreElement Value) → List (Nat × StoreElement Value)
  | [] => []
  | head :: tail =>
      if isSeqCst && head.2.isSeqCst then
        if foundSc then filterSeqCst isSeqCst true tail
        else head :: filterSeqCst isSeqCst true tail
      else head :: filterSeqCst isSeqCst foundSc tail
termination_by values => values.length
decreasing_by all_goals (simp_wf <;> simp [List.length_cons])

private theorem candidatePrefix_nonempty (isSeqCst : Bool) (clocks : ThreadClockSet)
    (items : List (Nat × StoreElement Value)) (nonempty : items ≠ []) :
    candidatePrefix isSeqCst clocks items ≠ [] := by
  cases items with
  | nil => contradiction
  | cons _ _ => simp [candidatePrefix]

private theorem filterSeqCst_nonempty (isSeqCst : Bool)
    (items : List (Nat × StoreElement Value)) (nonempty : items ≠ []) :
    filterSeqCst isSeqCst false items ≠ [] := by
  cases items with
  | nil => contradiction
  | cons head tail =>
      by_cases h : isSeqCst && head.2.isSeqCst
      · simp [filterSeqCst, h]
      · simp [filterSeqCst, h]

private theorem map_nonempty {α β : Type} (f : α → β) {items : List α}
    (nonempty : items ≠ []) : items.map f ≠ [] := by
  cases items with
  | nil => exact False.elim (nonempty rfl)
  | cons _ _ => simp

/-- One supported outcome of Miri's randomized `fetch_store`. -/
structure LoadChoice (Value : Type) where
  private mk ::
  position : Nat
  element : StoreElement Value
  recency : LoadRecency

/-- The finite support of Miri `fetch_store`: candidates are presented in
newest-to-oldest order, preserving distinct modification-order entries. -/
def fetchChoices (buffer : StoreBuffer Value) (isSeqCst : Bool)
    (clocks : ThreadClockSet) : List (LoadChoice Value) :=
  let candidates := filterSeqCst isSeqCst false
    (candidatePrefix isSeqCst clocks (reverseIndexed buffer))
  candidates.map fun candidate =>
    { position := candidate.1
      element := candidate.2
      recency := if candidate.1 + 1 = buffer.entries.length then .Latest else .Outdated }

/-- The initial element and inclusive prefix rule ensure at least one legal
candidate for every valid store buffer and clock state. -/
theorem fetchChoices_nonempty (buffer : StoreBuffer Value) (isSeqCst : Bool)
    (clocks : ThreadClockSet) : fetchChoices buffer isSeqCst clocks ≠ [] := by
  dsimp [fetchChoices]
  have hIndexed : indexedEntries buffer.entries 0 ≠ [] := by
    simp [entries, indexedEntries]
  have hReversed : reverseIndexed buffer ≠ [] := by
    unfold reverseIndexed
    exact List.reverse_ne_nil_iff.mpr hIndexed
  have hPrefix := candidatePrefix_nonempty isSeqCst clocks _ hReversed
  have hFiltered := filterSeqCst_nonempty isSeqCst _ hPrefix
  exact map_nonempty _ hFiltered

/-- Select one supported candidate by an explicit rank. This exposes legal
nondeterministic choices without pretending to model Miri's RNG distribution. -/
private def weakMemoryListGet? : List α → Nat → Option α
  | [], _ => none
  | value :: _, 0 => some value
  | _ :: rest, rank + 1 => weakMemoryListGet? rest rank
termination_by values _rank => values.length
decreasing_by simp_wf

def fetchAt (buffer : StoreBuffer Value) (isSeqCst : Bool)
    (clocks : ThreadClockSet) (rank : Nat) : Except WeakMemoryError (LoadChoice Value) :=
  match weakMemoryListGet? (fetchChoices buffer isSeqCst clocks) rank with
  | none => .error .choiceOutOfBounds
  | some choice => .ok choice

private def replaceAt : List α → Nat → α → Option (List α)
  | [], _, _ => none
  | _ :: rest, 0, value => some (value :: rest)
  | head :: rest, index + 1, value => do
      let updated ← replaceAt rest index value
      pure (head :: updated)
termination_by values _index _value => values.length
decreasing_by simp_wf

/-- Rebuild a nonempty buffer after a same-length metadata update. -/
private def fromEntries (values : List (StoreElement Value)) :
    Except WeakMemoryError (StoreBuffer Value) :=
  match values with
  | [] => .error .emptyStoreBuffer
  | oldest :: newer =>
      if h : newer.length < STORE_BUFFER_LIMIT then
        .ok { oldest := oldest, newer := newer, bounded := h }
      else
        .error .bufferTooLong

/-- Record the selected load after external atomic validation has succeeded.
The passed clock is the post-validation thread-clock state, as in Miri. -/
def recordSelectedLoad (buffer : StoreBuffer Value) (choice : LoadChoice Value)
    (index : VectorIdx) (clocksAfterValidation : ThreadClockSet)
    (isSeqCst : Bool) : Except WeakMemoryError (StoreBuffer Value × Option Value) := do
  let (updated, value) := choice.element.loadImpl index clocksAfterValidation isSeqCst
  let entries ← match replaceAt buffer.entries choice.position updated with
    | none => .error .selectedIndexOutOfBounds
    | some entries => .ok entries
  let result ← fromEntries entries
  pure (result, value)

/-- Result of one buffered atomic load, including the selected synchronization
clock, chosen value, recency diagnostic bit, and post-validation thread state. -/
structure BufferedReadResult (Value : Type) where
  buffer : StoreBuffer Value
  value : Option Value
  choice : LoadChoice Value
  clocks : ThreadClockSet

/-- Execute one legal source read choice. Validation observes that entry's
per-element synchronization clock after selection. Load metadata changes only
if validation succeeds, in the same order as the source implementation. -/
def bufferedReadAt {Error : Type} (buffer : StoreBuffer Value) (isSeqCst : Bool)
    (clocksBeforeValidation : ThreadClockSet) (loadIndex : VectorIdx) (rank : Nat)
    (validate : VClock → Except Error ThreadClockSet) :
    Except (Sum Error WeakMemoryError) (BufferedReadResult Value) := do
  let choice ← match fetchAt buffer isSeqCst clocksBeforeValidation rank with
    | .error error => .error (.inr error)
    | .ok choice => .ok choice
  let clocksAfter ← match validate choice.element.syncClock with
    | .error error => .error (.inl error)
    | .ok clocks => .ok clocks
  let (bufferAfter, value) ← match recordSelectedLoad buffer choice loadIndex
      clocksAfter isSeqCst with
    | .error error => .error (.inr error)
    | .ok result => .ok result
  pure { buffer := bufferAfter, value, choice, clocks := clocksAfter }

/-- Perform Miri's RMW-side read from the latest modification-order element.
The RMW does not use randomized stale reads. -/
def readFromLastStore (buffer : StoreBuffer Value) (index : VectorIdx)
    (clocks : ThreadClockSet) (isSeqCst : Bool) :
    Except WeakMemoryError (StoreBuffer Value × Option Value) := do
  let element := buffer.last
  let (updated, value) := element.loadImpl index clocks isSeqCst
  let position := buffer.entries.length - 1
  let entries ← match replaceAt buffer.entries position updated with
  | none => .error .selectedIndexOutOfBounds
  | some entries =>
    .ok entries
  let result ← fromEntries entries
  pure (result, value)

/-- Mark stores that happen-before or are coherence-ordered before an SC store.
The source scans the whole retained buffer, including the newly appended store. -/
private def markBeforeSeqCstStore (element : StoreElement Value)
    (threadClock : VClock) : StoreElement Value :=
  if decide (element.storeTimestamp.time ≤
      (threadClock.index element.storeThread).time) ||
      StoreElement.hasLoadBefore element threadClock then
    { element with isSeqCst := true }
  else element

/-- Add a store, dropping the oldest element when the current buffer is already
at the source limit. SC marking follows the pinned source's two HB/CoWR tests. -/
def storeImpl (buffer : StoreBuffer Value) (value : Value) (index : VectorIdx)
    (threadClock : VClock) (isSeqCst : Bool) (syncClock : VClock) : StoreBuffer Value :=
  let element : StoreElement Value := {
    storeThread := index
    storeTimestamp := threadClock.index index
    syncClock := syncClock
    isSeqCst := isSeqCst
    val := some value
    loadInfo := {} }
  let appended :=
      if h : buffer.newer.length + 1 < STORE_BUFFER_LIMIT then
      { oldest := buffer.oldest
        newer := buffer.newer ++ [element]
        bounded := by
          simp only [List.length_append, List.length_singleton]
          omega }
    else
      match hNewer : buffer.newer with
      | [] => buffer
      | nextOldest :: tail =>
        { oldest := nextOldest
          newer := tail ++ [element]
          bounded := by
            have hBound := buffer.bounded
            rw [hNewer, List.length_cons] at hBound
            simp only [List.length_append, List.length_singleton]
            omega }
  if isSeqCst then
    { appended with
      oldest := markBeforeSeqCstStore appended.oldest threadClock
      newer := appended.newer.map (fun store => markBeforeSeqCstStore store threadClock)
      bounded := by simpa using appended.bounded }
  else appended

/-- Miri's ordinary buffered write: capture the writer's timestamp and the
caller-provided release-sequence clock, then append/trim/SC-mark. -/
def bufferedWrite (buffer : StoreBuffer Value) (value : Value) (thread : ThreadClockSet)
    (index : VectorIdx) (isSeqCst : Bool) (syncClock : VClock) : StoreBuffer Value :=
  storeImpl buffer value index thread.clock isSeqCst syncClock

end StoreBuffer

/-- Allocation-local range map of atomic objects to their store buffers. -/
structure StoreBufferAlloc (Value : Type) where
  storeBuffers : Miri.DataStructures.RangeObjectMap (StoreBuffer Value)

/-- A detached value handle for one perfectly overlapping object. Callers
commit it explicitly after their operation; a changed range map invalidates the
handle instead of silently updating some other object. -/
structure StoreBufferHandle (Value : Type) where
  range : Miri.Memory.AllocRange
  position : Miri.DataStructures.Position
  buffer : StoreBuffer Value

inductive StoreBufferAllocError where
  | rangeMap (error : Miri.DataStructures.RangeObjectMapError)
  | handleInvalidated
  deriving Repr

/-- Pure transition result retains RangeObjectMap's partial mutation on error,
matching its insert-before-check behavior. -/
structure StoreBufferAllocTransition (Value : Type) where
  allocation : StoreBufferAlloc Value
  outcome : Except StoreBufferAllocError (Option (StoreBufferHandle Value))

namespace StoreBufferAlloc

private def mutationResult (allocation : StoreBufferAlloc Value)
    (outcome : Except StoreBufferAllocError (Option (StoreBufferHandle Value))) :
    StoreBufferAllocTransition Value := { allocation := allocation, outcome := outcome }

def newAllocation : StoreBufferAlloc Value :=
  { storeBuffers := Miri.DataStructures.RangeObjectMap.new }

def bufferCount (allocation : StoreBufferAlloc Value) : Nat :=
  allocation.storeBuffers.length

def bufferRanges (allocation : StoreBufferAlloc Value) : Array Miri.Memory.AllocRange :=
  allocation.storeBuffers.ranges

/-- Remove or retain buffered state after a non-atomic write exactly according
to Miri's `ongoing_action_data_race_free` flag and overlap classification. -/
def nonAtomicWrite (allocation : StoreBufferAlloc Value)
    (range : Miri.Memory.AllocRange) (global : GlobalState) :
    StoreBufferAllocTransition Value :=
  if global.ongoingActionDataRaceFree then
    mutationResult allocation (.ok none)
  else
    match allocation.storeBuffers.accessType range with
    | .error error => mutationResult allocation (.error (.rangeMap error))
    | .ok (.perfectlyOverlapping position) =>
      let removed := allocation.storeBuffers.removeFromPos position
      let next := { allocation with storeBuffers := removed.state }
      match removed.outcome with
      | .ok _ => mutationResult next (.ok none)
      | .error error => mutationResult next (.error (.rangeMap error))
    | .ok (.imperfectlyOverlapping positions) =>
      let removed := allocation.storeBuffers.removePosRange positions.start positions.stop
      let next := { allocation with storeBuffers := removed.state }
      match removed.outcome with
      | .ok _ => mutationResult next (.ok none)
      | .error error => mutationResult next (.error (.rangeMap error))
    | .ok (.empty _) => mutationResult allocation (.ok none)

/-- Return a store-buffer handle only for a perfectly overlapping object.
Empty and imperfect overlaps return no buffer, as in Miri. -/
def getStoreBuffer (allocation : StoreBufferAlloc Value)
    (range : Miri.Memory.AllocRange) :
    Except StoreBufferAllocError (Option (StoreBufferHandle Value)) := do
  match allocation.storeBuffers.accessType range with
  | .error error => .error (.rangeMap error)
  | .ok (.perfectlyOverlapping position) =>
    match allocation.storeBuffers.index position with
    | .error error => .error (.rangeMap error)
    | .ok buffer => .ok (some { range := range, position := position, buffer := buffer })
  | .ok (.empty _) | .ok (.imperfectlyOverlapping _) => .ok none

private def handleAt (allocation : StoreBufferAlloc Value)
    (range : Miri.Memory.AllocRange) (position : Nat) :
    Except StoreBufferAllocError (StoreBufferHandle Value) := do
  let buffer ← (allocation.storeBuffers.index position).mapError StoreBufferAllocError.rangeMap
  pure { range := range, position := position, buffer := buffer }

private def insertedHandle (allocation : StoreBufferAlloc Value)
    (range : Miri.Memory.AllocRange) (position : Nat)
    (mutation : Miri.DataStructures.MutationResult
      (Miri.DataStructures.RangeObjectMap (StoreBuffer Value))) :
    StoreBufferAllocTransition Value :=
  let next := { allocation with storeBuffers := mutation.state }
  match mutation.outcome with
  | .error error => mutationResult next (.error (.rangeMap error))
  | .ok _ =>
    match handleAt next range position with
    | .error error => mutationResult next (.error error)
    | .ok handle => mutationResult next (.ok (some handle))

/-- Get an exactly matching buffer or initialize a new one. On imperfect
overlap, the old intersecting buffers are removed before insertion, matching
Miri's range invalidation order. -/
def getOrCreateStoreBuffer (allocation : StoreBufferAlloc Value)
    (range : Miri.Memory.AllocRange) (init : Option Value) :
    StoreBufferAllocTransition Value :=
  match allocation.storeBuffers.accessType range with
  | .error error => mutationResult allocation (.error (.rangeMap error))
  | .ok (.perfectlyOverlapping position) =>
    match handleAt allocation range position with
    | .error error => mutationResult allocation (.error error)
    | .ok handle => mutationResult allocation (.ok (some handle))
  | .ok (.empty position) =>
    let inserted := allocation.storeBuffers.insertAtPos position range
      (StoreBuffer.new init)
    insertedHandle allocation range position inserted
  | .ok (.imperfectlyOverlapping positions) =>
    let removed := allocation.storeBuffers.removePosRange positions.start positions.stop
    let afterRemoval := { allocation with storeBuffers := removed.state }
    match removed.outcome with
    | .error error => mutationResult afterRemoval (.error (.rangeMap error))
    | .ok _ =>
      let inserted := afterRemoval.storeBuffers.insertAtPos positions.start range
        (StoreBuffer.new init)
      insertedHandle afterRemoval range positions.start inserted

/-- Commit a returned buffer handle after the modeled atomic operation. -/
def commitStoreBuffer (allocation : StoreBufferAlloc Value)
    (handle : StoreBufferHandle Value) :
    Except StoreBufferAllocError (StoreBufferAlloc Value) := do
  match allocation.storeBuffers.accessType handle.range with
  | .error error => .error (.rangeMap error)
  | .ok (.perfectlyOverlapping position) =>
    if position != handle.position then .error .handleInvalidated
    else
      let mutation := allocation.storeBuffers.setAtPos position handle.buffer
      match mutation.outcome with
      | .error error => .error (.rangeMap error)
      | .ok _ => .ok { allocation with storeBuffers := mutation.state }
  | .ok (.empty _) | .ok (.imperfectlyOverlapping _) => .error .handleInvalidated

end StoreBufferAlloc

end Miri.Concurrency
