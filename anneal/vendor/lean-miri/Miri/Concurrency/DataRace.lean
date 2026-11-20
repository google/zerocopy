import Miri.Concurrency.VectorClock

/-!
# Data-race clock state from pinned Miri

This module ports the pure ordering, thread-clock, and per-memory-cell clock
transitions in `src/concurrency/data_race.rs` at the pinned Miri revision.
The allocation-level interpreter hooks, MIR integration, `DedupRangeMap`,
diagnostic construction, and weak-memory store buffers are not modeled here.
In particular, these definitions are source-backed state operations, not a
standalone claim that a Rust program has been checked by Miri.

Miri `Span` values occur only in diagnostic attribution for the transitions
ported here. They do not affect the vector-clock ordering or race decision,
and are omitted from the Lean state. Atomic access sizes are represented as
the exact `u64` byte counts used by rustc_abi::Size.
-/

namespace Miri.Concurrency

/-- The five orderings accepted for read/write atomic operations. -/
inductive AtomicOrdering where
  | Relaxed
  | Acquire
  | Release
  | AcqRel
  | SeqCst
  deriving DecidableEq, Repr, Inhabited

/-- An atomic ordering accepted by either a read or a write. -/
inductive AtomicRwOrd where
  | Relaxed
  | Acquire
  | Release
  | AcqRel
  | SeqCst
  deriving DecidableEq, Repr, Inhabited

/-- The ordering subset accepted by atomic loads. -/
inductive AtomicReadOrd where
  | Relaxed
  | Acquire
  | SeqCst
  deriving DecidableEq, Repr, Inhabited

/-- The ordering subset accepted by atomic stores. -/
inductive AtomicWriteOrd where
  | Relaxed
  | Release
  | SeqCst
  deriving DecidableEq, Repr, Inhabited

/-- The ordering subset accepted by atomic fences. -/
inductive AtomicFenceOrd where
  | Acquire
  | Release
  | AcqRel
  | SeqCst
  deriving DecidableEq, Repr, Inhabited

/-- A source-invalid ordering is made explicit where pinned Miri panics. -/
inductive AtomicOrderingError where
  | invalidRead (ordering : AtomicOrdering)
  | invalidWrite (ordering : AtomicOrdering)
  | invalidFence (ordering : AtomicOrdering)
  deriving DecidableEq, Repr

namespace AtomicRwOrd

/-- Total conversion corresponding to `AtomicRwOrd::from`. -/
def ofOrdering : AtomicOrdering → AtomicRwOrd
  | .Relaxed => .Relaxed
  | .Acquire => .Acquire
  | .Release => .Release
  | .AcqRel => .AcqRel
  | .SeqCst => .SeqCst

end AtomicRwOrd

namespace AtomicReadOrd

/-- Checked conversion corresponding to `AtomicReadOrd::from`.
Release and AcqRel are explicit invalid-ordering outcomes, matching the
source panic rather than accepting or weakening them. -/
def ofOrdering : AtomicOrdering → Except AtomicOrderingError AtomicReadOrd
  | .Relaxed => .ok .Relaxed
  | .Acquire => .ok .Acquire
  | .SeqCst => .ok .SeqCst
  | .Release => .error (.invalidRead .Release)
  | .AcqRel => .error (.invalidRead .AcqRel)

end AtomicReadOrd

namespace AtomicWriteOrd

/-- Checked conversion corresponding to `AtomicWriteOrd::from`.
Acquire and AcqRel are explicit invalid-ordering outcomes. -/
def ofOrdering : AtomicOrdering → Except AtomicOrderingError AtomicWriteOrd
  | .Relaxed => .ok .Relaxed
  | .Release => .ok .Release
  | .SeqCst => .ok .SeqCst
  | .Acquire => .error (.invalidWrite .Acquire)
  | .AcqRel => .error (.invalidWrite .AcqRel)

end AtomicWriteOrd

namespace AtomicFenceOrd

/-- Checked conversion corresponding to `AtomicFenceOrd::from`.
Relaxed is an explicit invalid-ordering outcome. -/
def ofOrdering : AtomicOrdering → Except AtomicOrderingError AtomicFenceOrd
  | .Acquire => .ok .Acquire
  | .Release => .ok .Release
  | .AcqRel => .ok .AcqRel
  | .SeqCst => .ok .SeqCst
  | .Relaxed => .error (.invalidFence .Relaxed)

end AtomicFenceOrd

/-- Per-thread vector-clock state, including all Miri fence and SC metadata. -/
structure ThreadClockSet where
  /-- The increasing happens-before clock. -/
  clock : VClock := .default
  /-- Clock to acquire on a later acquire fence. -/
  fenceAcquire : VClock := .default
  /-- Clock released by the most recent release fence. -/
  fenceRelease : VClock := .default
  /-- Per-thread SC-write metadata used by weak-memory emulation. -/
  writeSeqCst : VClock := .default
  /-- Per-thread SC-fence metadata used by weak-memory emulation. -/
  readSeqCst : VClock := .default
  deriving Repr, Inhabited

namespace ThreadClockSet

/-- The source `Default` state: all five clocks are zero. -/
def default : ThreadClockSet :=
  { clock := .default
    fenceAcquire := .default
    fenceRelease := .default
    writeSeqCst := .default
    readSeqCst := .default }

/-- Apply Miri's release-fence effect by copying the happens-before clock. -/
def applyReleaseFence (state : ThreadClockSet) : ThreadClockSet :=
  { state with fenceRelease := state.clock }

/-- Apply Miri's acquire-fence effect by joining the accumulated acquire clock. -/
def applyAcquireFence (state : ThreadClockSet) : ThreadClockSet :=
  { state with clock := state.clock.join state.fenceAcquire }

/-- Increment the known thread coordinate; timestamp overflow remains explicit. -/
def incrementClock (state : ThreadClockSet) (index : VectorIdx) :
    Except ClockError ThreadClockSet := do
  let next ← state.clock.incrementIndex index
  pure { state with clock := next }

/-- Join another thread's happens-before clock, leaving fence/SC metadata intact. -/
def joinWith (state other : ThreadClockSet) : ThreadClockSet :=
  { state with clock := state.clock.join other.clock }

end ThreadClockSet

/-- Byte size from rustc_abi::Size, whose stored representation is `u64`. -/
structure ByteSize where
  private mk ::
  value : Fin 18446744073709551616
  deriving DecidableEq, Repr

namespace ByteSize

/-- Construct a byte size from an exact u64 value. -/
def ofU64 (value : Nat) (h : value < 18446744073709551616) : ByteSize :=
  ⟨⟨value, h⟩⟩

/-- The mathematical byte count. -/
def bytes (size : ByteSize) : Nat := size.value.val

@[simp] theorem bytes_ofU64 (value : Nat) (h : value < 18446744073709551616) :
    (ofU64 value h).bytes = value := rfl

end ByteSize

/-- Result used for the source's `Result<(), DataRace>` cell transitions. -/
inductive DataRaceResult where
  | ok
  | race
  | invalidClockUpdate (error : ClockError)
  | internalInvariantViolation
  | outOfBounds
  deriving DecidableEq, Repr

/-- Per-byte metadata attached to atomic memory. -/
structure AtomicMemoryCellClocks where
  /-- Most recent atomic reads by thread. -/
  readVector : VClock := .default
  /-- Most recent atomic writes by thread. -/
  writeVector : VClock := .default
  /-- Clock released by the current modification/release sequence. -/
  syncVector : VClock := .default
  /-- One uniform size, or `none` after concurrent differently-sized reads. -/
  size : Option ByteSize := none
  deriving Repr, Inhabited

namespace AtomicMemoryCellClocks

/-- Initialize atomic metadata for the first access of a given size. -/
def new (size : ByteSize) : AtomicMemoryCellClocks := { size := some size }

end AtomicMemoryCellClocks

/-- Non-atomic write kinds counted by the detector, including lifetime writes. -/
inductive NaWriteType where
  | Allocate
  | Write
  | Retag
  | Deallocate
  deriving DecidableEq, Repr, Inhabited

/-- Atomic accesses tracked by one memory cell. -/
inductive AtomicAccessType where
  | Load (ordering : AtomicReadOrd)
  | Store
  | Rmw
  deriving DecidableEq, Repr

/-- Access category used by Miri's race classifier. -/
inductive AccessType where
  | NaRead (readType : NaReadType)
  | NaWrite (writeType : NaWriteType)
  | AtomicLoad
  | AtomicStore
  | AtomicRmw
  deriving DecidableEq, Repr

namespace AccessType

def isAtomic : AccessType → Bool
  | .AtomicLoad | .AtomicStore | .AtomicRmw => true
  | .NaRead _ | .NaWrite _ => false

def isRead : AccessType → Bool
  | .AtomicLoad | .NaRead _ => true
  | .NaWrite _ | .AtomicStore | .AtomicRmw => false

def isRetag : AccessType → Bool
  | .NaRead .Retag | .NaWrite .Retag => true
  | .NaRead .Read | .NaWrite .Allocate | .NaWrite .Write | .NaWrite .Deallocate
  | .AtomicLoad | .AtomicStore | .AtomicRmw => false

end AccessType

/-- Per-byte vector-clock state exactly corresponding to `MemoryCellClocks` fields. -/
structure MemoryCellClocks where
  /-- Last non-atomic write thread and timestamp. -/
  write : VectorIdx × VTimestamp
  /-- Kind of the most recent non-atomic write. -/
  writeType : NaWriteType
  /-- Vector clock of non-atomic reads since the last write. -/
  read : VClock := .default
  /-- Additional metadata, lazily created for atomic accesses. -/
  atomicOps : Option AtomicMemoryCellClocks := none
  deriving Repr

namespace MemoryCellClocks

/-- Initialize one byte as a newly allocated non-atomic location. -/
def new (allocationTimestamp : VTimestamp) (allocationIndex : VectorIdx) :
    MemoryCellClocks :=
  { write := (allocationIndex, allocationTimestamp), writeType := .Allocate }

/-- Whether the last non-atomic write happens before the supplied clock. -/
def writeWasBefore (cell : MemoryCellClocks) (clock : VClock) : Bool :=
  decide (cell.write.2.time ≤ (clock.index cell.write.1).time)

/-- Materialize the singleton write clock used by diagnostics. -/
def writeClock (cell : MemoryCellClocks) : VClock :=
  .newWithIndex cell.write.1 cell.write.2

/-- The source's size-state transition for an atomic access. -/
def atomicAccess (cell : MemoryCellClocks) (thread : ThreadClockSet)
    (accessSize : ByteSize) (isWrite : Bool) : Except DataRaceResult AtomicMemoryCellClocks :=
  match cell.atomicOps with
  | none => .ok (AtomicMemoryCellClocks.new accessSize)
  | some atomic =>
    if atomic.size == some accessSize then
      .ok atomic
    else if atomic.readVector.le thread.clock && atomic.writeVector.le thread.clock then
      .ok { atomic with size := some accessSize }
    else if !isWrite && atomic.writeVector.le thread.clock then
      .ok { atomic with size := none }
    else
      .error .race

/-- A cell operation returns mutated states even when a race is detected. This
matches the source's mutation-before-check order; execution then terminates at
the caller. -/
structure Transition where
  cell : MemoryCellClocks
  thread : ThreadClockSet
  result : DataRaceResult
  deriving Repr

private def updateAtomic (cell : MemoryCellClocks) (atomic : AtomicMemoryCellClocks) :
    MemoryCellClocks :=
  { cell with atomicOps := some atomic }

/-- Record an atomic load, then check whether the non-atomic write is ordered. -/
def atomicReadDetect (cell : MemoryCellClocks) (thread : ThreadClockSet)
    (index : VectorIdx) (accessSize : ByteSize) : Transition :=
  match cell.atomicAccess thread accessSize false with
  | .error failure => ⟨cell, thread, failure⟩
  | .ok atomic =>
    match atomic.readVector.setAtIndex thread.clock index with
    | .error failure =>
      ⟨updateAtomic cell atomic, thread, .invalidClockUpdate failure⟩
    | .ok readVector =>
      let changedAtomic := { atomic with readVector := readVector }
      let changedCell := updateAtomic cell changedAtomic
      ⟨changedCell, thread,
        if cell.writeWasBefore thread.clock then .ok else .race⟩

/-- Record an atomic write, then check prior non-atomic writes and reads. -/
def atomicWriteDetect (cell : MemoryCellClocks) (thread : ThreadClockSet)
    (index : VectorIdx) (accessSize : ByteSize) : Transition :=
  match cell.atomicAccess thread accessSize true with
  | .error failure => ⟨cell, thread, failure⟩
  | .ok atomic =>
    match atomic.writeVector.setAtIndex thread.clock index with
    | .error failure =>
      ⟨updateAtomic cell atomic, thread, .invalidClockUpdate failure⟩
    | .ok writeVector =>
      let changedAtomic := { atomic with writeVector := writeVector }
      let changedCell := updateAtomic cell changedAtomic
      let raceFree := cell.writeWasBefore thread.clock && cell.read.le thread.clock
      ⟨changedCell, thread, if raceFree then .ok else .race⟩

/-- Atomic load-acquire: detect the access and then acquire either the supplied
weak-memory synchronization clock or the cell's release-sequence clock. -/
def loadAcquire (cell : MemoryCellClocks) (thread : ThreadClockSet)
    (index : VectorIdx) (accessSize : ByteSize) (syncClock : Option VClock := none) :
    Transition :=
  let access := atomicReadDetect cell thread index accessSize
  if access.result != .ok then access
  else
    let acquired := syncClock.orElse fun () => access.cell.atomicOps.map AtomicMemoryCellClocks.syncVector
    match acquired with
    | none => access
    | some sync => { access with thread := { access.thread with clock := access.thread.clock.join sync } }

/-- Atomic load-relaxed: it accumulates the synchronization clock for a later
acquire fence instead of joining the happens-before clock immediately. -/
def loadRelaxed (cell : MemoryCellClocks) (thread : ThreadClockSet)
    (index : VectorIdx) (accessSize : ByteSize) (syncClock : Option VClock := none) :
    Transition :=
  let access := atomicReadDetect cell thread index accessSize
  if access.result != .ok then access
  else
    let acquired := syncClock.orElse fun () => access.cell.atomicOps.map AtomicMemoryCellClocks.syncVector
    match acquired with
    | none => access
    | some sync =>
      { access with thread := { access.thread with
          fenceAcquire := access.thread.fenceAcquire.join sync } }

/-- Atomic release store publishes the thread's happens-before clock. -/
def storeRelease (cell : MemoryCellClocks) (thread : ThreadClockSet)
    (index : VectorIdx) (accessSize : ByteSize) : Transition :=
  let access := atomicWriteDetect cell thread index accessSize
  if access.result != .ok then access
  else
    match access.cell.atomicOps with
    | none => { access with result := .internalInvariantViolation }
    | some atomic =>
      let updatedAtomic := { atomic with syncVector := thread.clock }
      { access with cell := updateAtomic access.cell updatedAtomic }

/-- Atomic relaxed store breaks the previous release sequence, replacing it
with the thread's release-fence clock. -/
def storeRelaxed (cell : MemoryCellClocks) (thread : ThreadClockSet)
    (index : VectorIdx) (accessSize : ByteSize) : Transition :=
  let access := atomicWriteDetect cell thread index accessSize
  if access.result != .ok then access
  else
    match access.cell.atomicOps with
    | none => { access with result := .internalInvariantViolation }
    | some atomic =>
      let updatedAtomic := { atomic with syncVector := thread.fenceRelease }
      { access with cell := updateAtomic access.cell updatedAtomic }

/-- Release RMW extends (rather than replaces) the prior release sequence. -/
def rmwRelease (cell : MemoryCellClocks) (thread : ThreadClockSet)
    (index : VectorIdx) (accessSize : ByteSize) : Transition :=
  let access := atomicWriteDetect cell thread index accessSize
  if access.result != .ok then access
  else
    match access.cell.atomicOps with
    | none => { access with result := .internalInvariantViolation }
    | some atomic =>
      let updatedAtomic := { atomic with syncVector := atomic.syncVector.join thread.clock }
      { access with cell := updateAtomic access.cell updatedAtomic }

/-- Relaxed RMW extends the release sequence with the current release-fence clock. -/
def rmwRelaxed (cell : MemoryCellClocks) (thread : ThreadClockSet)
    (index : VectorIdx) (accessSize : ByteSize) : Transition :=
  let access := atomicWriteDetect cell thread index accessSize
  if access.result != .ok then access
  else
    match access.cell.atomicOps with
    | none => { access with result := .internalInvariantViolation }
    | some atomic =>
      let updatedAtomic := { atomic with syncVector := atomic.syncVector.join thread.fenceRelease }
      { access with cell := updateAtomic access.cell updatedAtomic }

/-- Non-atomic read: mark the current thread timestamp with the exact read kind,
check non-atomic and atomic writes, and record the read clock. -/
def nonAtomicReadDetect (cell : MemoryCellClocks) (thread : ThreadClockSet)
    (index : VectorIdx) (readType : NaReadType) : Transition :=
  match thread.clock.applyReadType index readType with
  | .error failure => ⟨cell, thread, .invalidClockUpdate failure⟩
  | .ok taggedClock =>
    let taggedThread := { thread with clock := taggedClock }
    let atomicWritesBefore := cell.atomicOps.all fun atomic =>
      atomic.writeVector.le taggedClock
    let raceFree := cell.writeWasBefore taggedClock && atomicWritesBefore
    if !raceFree then
      ⟨cell, taggedThread, .race⟩
    else
      match cell.read.setAtIndex taggedClock index with
      | .error failure => ⟨cell, taggedThread, .invalidClockUpdate failure⟩
      | .ok readClock =>
        let changedCell := { cell with read := readClock }
        ⟨changedCell, taggedThread, .ok⟩

/-- Non-atomic write: check prior writes, reads, and atomic accesses; on success
replace the write timestamp, reset read clocks, and remove atomic metadata. -/
def nonAtomicWriteDetect (cell : MemoryCellClocks) (thread : ThreadClockSet)
    (index : VectorIdx) (writeType : NaWriteType) : Transition :=
  let raceFreeNonAtomic := cell.writeWasBefore thread.clock && cell.read.le thread.clock
  let raceFreeAtomic := cell.atomicOps.all fun atomic =>
    atomic.writeVector.le thread.clock && atomic.readVector.le thread.clock
  if !(raceFreeNonAtomic && raceFreeAtomic) then
    ⟨cell, thread, .race⟩
  else
    let writeTimestamp := thread.clock.index index
    let changedCell := { cell with
      write := (index, writeTimestamp)
      writeType := writeType
      read := .default
      atomicOps := none }
    ⟨changedCell, thread, .ok⟩

end MemoryCellClocks

/-- A memory byte range, using the exact rustc_abi Size byte counts. -/
structure AccessRange where
  start : ByteSize
  size : ByteSize
  deriving DecidableEq, Repr

/-- Sparse representation of `DedupRangeMap<MemoryCellClocks>`.
Unmodified bytes share the allocation's initial cell; changed bytes are stored
as overrides. Range boundaries and deduplication are storage details, while
this representation preserves the per-byte values that the detector reads. -/
structure AllocationRanges where
  length : ByteSize
  initialCell : MemoryCellClocks
  overrides : List (Nat × MemoryCellClocks) := []
  deriving Repr

namespace AllocationRanges

private def findOverride : List (Nat × MemoryCellClocks) → Nat → Option MemoryCellClocks
  | [], _ => none
  | (offset, value) :: rest, wanted =>
      if offset = wanted then some value else findOverride rest wanted
termination_by entries _wanted => entries.length
decreasing_by simp_wf

private def removeOverrides : List (Nat × MemoryCellClocks) → Nat →
    List (Nat × MemoryCellClocks)
  | [], _ => []
  | (offset, value) :: rest, wanted =>
      if offset = wanted then removeOverrides rest wanted
      else (offset, value) :: removeOverrides rest wanted
termination_by entries _wanted => entries.length
decreasing_by
  simp_wf
  simp only [List.length_cons]
  omega

/-- Read one byte; an absent override denotes its original allocation state. -/
def cellAt (ranges : AllocationRanges) (offset : Nat) : Except DataRaceResult MemoryCellClocks :=
  if offset < ranges.length.bytes then
    match findOverride ranges.overrides offset with
    | some value => .ok value
    | none => .ok ranges.initialCell
  else
    .error .outOfBounds

/-- Replace one byte, preserving an explicit bounds failure. -/
def setCell (ranges : AllocationRanges) (offset : Nat) (value : MemoryCellClocks) :
    Except DataRaceResult AllocationRanges :=
  if offset < ranges.length.bytes then
    .ok { ranges with overrides := (offset, value) :: removeOverrides ranges.overrides offset }
  else
    .error .outOfBounds

end AllocationRanges

/-- Allocation-level vector-clock state (`AllocState` in pinned Miri).
The construction input is the allocation timestamp already selected by Miri's
`MemoryKind` classification; that interpreter classification is outside this
pure clock-state module. -/
structure VClockAlloc where
  allocRanges : AllocationRanges
  deriving Repr

abbrev AllocState := VClockAlloc

namespace VClockAlloc

/-- Initialize every byte with the allocation write state, represented lazily. -/
def newAllocation (length : ByteSize) (allocationTimestamp : VTimestamp)
    (allocationIndex : VectorIdx) : VClockAlloc :=
  { allocRanges := {
      length := length
      initialCell := MemoryCellClocks.new allocationTimestamp allocationIndex } }

/-- Read one byte's effective clock state. -/
def cellAt (allocation : VClockAlloc) (offset : Nat) :
    Except DataRaceResult MemoryCellClocks :=
  allocation.allocRanges.cellAt offset

/-- Replace one byte's clock state. -/
def setCell (allocation : VClockAlloc) (offset : Nat) (cell : MemoryCellClocks) :
    Except DataRaceResult VClockAlloc := do
  let ranges ← allocation.allocRanges.setCell offset cell
  pure { allocRanges := ranges }

/-- Result of applying a per-cell race-detection hook to a byte range. -/
structure RangeTransition where
  allocation : VClockAlloc
  thread : ThreadClockSet
  result : DataRaceResult
  deriving Repr

private def runRangeLoop (allocation : VClockAlloc) (thread : ThreadClockSet)
    (action : MemoryCellClocks → ThreadClockSet → MemoryCellClocks.Transition)
    (offset : Nat) : Nat → RangeTransition
  | 0 => ⟨allocation, thread, .ok⟩
  | remaining + 1 =>
    match allocation.cellAt offset with
    | .error failure => ⟨allocation, thread, failure⟩
    | .ok cell =>
      let transition := action cell thread
      match allocation.setCell offset transition.cell with
      | .error failure => ⟨allocation, transition.thread, failure⟩
      | .ok updatedAllocation =>
        if transition.result = .ok then
          runRangeLoop updatedAllocation transition.thread action (offset + 1) remaining
        else
          ⟨updatedAllocation, transition.thread, transition.result⟩

private def joinSyncClocks (allocation : VClockAlloc) (offset remaining : Nat) :
    Except DataRaceResult VClock := do
  match remaining with
  | 0 => pure .default
  | amount + 1 => do
    let cell ← allocation.cellAt offset
    let rest ← joinSyncClocks allocation (offset + 1) amount
    let cellClock : VClock := match cell.atomicOps with
      | none => .default
      | some atomic => atomic.syncVector
    pure (cellClock.join rest)
termination_by remaining
decreasing_by simp_wf

/-- Apply a source per-byte operation over a validated allocation range. Earlier
bytes remain updated if a later byte reports a race, matching Miri's mutable
range iteration order. -/
def runRange (allocation : VClockAlloc) (range : AccessRange) (thread : ThreadClockSet)
    (action : MemoryCellClocks → ThreadClockSet → MemoryCellClocks.Transition) :
    RangeTransition :=
  if range.start.bytes + range.size.bytes ≤ allocation.allocRanges.length.bytes then
    runRangeLoop allocation thread action range.start.bytes range.size.bytes
  else
    ⟨allocation, thread, .outOfBounds⟩

/-- Allocation-level non-atomic read hook, applying the exact per-byte read
detector and preserving regular-read versus retag-read categorization. -/
def readNonAtomic (allocation : VClockAlloc) (range : AccessRange)
    (thread : ThreadClockSet) (index : VectorIdx) (readType : NaReadType) : RangeTransition :=
  runRange allocation range thread fun cell clocks =>
    MemoryCellClocks.nonAtomicReadDetect cell clocks index readType

/-- Allocation-level non-atomic write hook. -/
def writeNonAtomic (allocation : VClockAlloc) (range : AccessRange)
    (thread : ThreadClockSet) (index : VectorIdx) (writeType : NaWriteType) : RangeTransition :=
  runRange allocation range thread fun cell clocks =>
    MemoryCellClocks.nonAtomicWriteDetect cell clocks index writeType

/-- Allocation-level atomic-read race hook. Atomic ordering synchronization is
applied by the corresponding per-cell load transition. -/
def atomicRead (allocation : VClockAlloc) (range : AccessRange)
    (thread : ThreadClockSet) (index : VectorIdx) (accessSize : ByteSize) : RangeTransition :=
  runRange allocation range thread fun cell clocks =>
    MemoryCellClocks.atomicReadDetect cell clocks index accessSize

/-- Allocation-level atomic-write race hook. -/
def atomicWrite (allocation : VClockAlloc) (range : AccessRange)
    (thread : ThreadClockSet) (index : VectorIdx) (accessSize : ByteSize) : RangeTransition :=
  runRange allocation range thread fun cell clocks =>
    MemoryCellClocks.atomicWriteDetect cell clocks index accessSize

/-- Apply the source's ordering-specific atomic-load transition to every byte
in a range. The optional clock overrides the cell's release-sequence clock,
as it does when a weak-memory load selects a particular store. -/
def atomicLoad (allocation : VClockAlloc) (range : AccessRange)
    (thread : ThreadClockSet) (index : VectorIdx) (accessSize : ByteSize)
    (ordering : AtomicReadOrd) (syncClock : Option VClock := none) : RangeTransition :=
  runRange allocation range thread fun cell clocks =>
    match ordering with
    | .Relaxed => MemoryCellClocks.loadRelaxed cell clocks index accessSize syncClock
    | .Acquire | .SeqCst => MemoryCellClocks.loadAcquire cell clocks index accessSize syncClock

/-- Apply Miri's atomic-store ordering to every byte in a range. -/
def atomicStore (allocation : VClockAlloc) (range : AccessRange)
    (thread : ThreadClockSet) (index : VectorIdx) (accessSize : ByteSize)
    (ordering : AtomicWriteOrd) : RangeTransition :=
  runRange allocation range thread fun cell clocks =>
    match ordering with
    | .Relaxed => MemoryCellClocks.storeRelaxed cell clocks index accessSize
    | .Release | .SeqCst => MemoryCellClocks.storeRelease cell clocks index accessSize

/-- Apply one atomic read-modify-write per byte, performing the read half
before the write half and extending the release sequence according to the
source ordering. -/
def atomicRmw (allocation : VClockAlloc) (range : AccessRange)
    (thread : ThreadClockSet) (index : VectorIdx) (accessSize : ByteSize)
    (ordering : AtomicRwOrd) : RangeTransition :=
  runRange allocation range thread fun cell clocks =>
    let read := match ordering with
      | .Relaxed | .Release => MemoryCellClocks.loadRelaxed cell clocks index accessSize none
      | .Acquire | .AcqRel | .SeqCst =>
          MemoryCellClocks.loadAcquire cell clocks index accessSize none
    if read.result != .ok then read
    else match ordering with
      | .Relaxed | .Acquire =>
          MemoryCellClocks.rmwRelaxed read.cell read.thread index accessSize
      | .Release | .AcqRel | .SeqCst =>
          MemoryCellClocks.rmwRelease read.cell read.thread index accessSize

/-- Join the release-sequence clocks attached to every byte in a memory range,
matching `VClockAlloc::sync_clock`. Uninitialized atomic metadata contributes
the zero clock. -/
def syncClock (allocation : VClockAlloc) (range : AccessRange) :
    Except DataRaceResult VClock := do
  let finish := range.start.bytes + range.size.bytes
  if finish > allocation.allocRanges.length.bytes then
    .error .outOfBounds
  else
    joinSyncClocks allocation range.start.bytes range.size.bytes

end VClockAlloc

end Miri.Concurrency
