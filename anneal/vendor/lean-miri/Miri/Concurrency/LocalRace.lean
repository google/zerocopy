import Miri.Concurrency.GlobalState

/-! Frame-local vector clocks and their transfer into addressable memory from
pinned `src/concurrency/data_race.rs:1303–1404`. Diagnostic spans are omitted;
timestamp times and packed read kinds are preserved. -/
namespace Miri.Concurrency.LocalRace

structure LocalClocks where
  write : VTimestamp := .ZERO
  writeType : NaWriteType := .Allocate
  read : VTimestamp := .ZERO
  deriving Repr

structure FrameState where
  localClocks : Array (Nat × LocalClocks) := #[]
  deriving Repr

namespace FrameState

def get (frame : FrameState) (localId : Nat) : LocalClocks :=
  (frame.localClocks.find? fun entry => entry.1 == localId).map Prod.snd |>.getD {}

def set (frame : FrameState) (localId : Nat) (clocks : LocalClocks) : FrameState :=
  ⟨(frame.localClocks.filter fun entry => entry.1 != localId).push (localId, clocks)⟩

def remove (frame : FrameState) (localId : Nat) : FrameState :=
  ⟨frame.localClocks.filter fun entry => entry.1 != localId⟩

end FrameState

inductive Error where
  | global (error : GlobalStateError)
  | clock (error : ClockError)
  | memory (error : DataRaceResult)
  | allocationWriterMismatch (expected actual : VectorIdx)
  deriving Repr

structure Result (A : Type) where
  frame : FrameState
  global : GlobalState
  outcome : Except Error A

/-- Source local_write only records clocks when race_detecting is true.
StorageLive resets the previous read timestamp; ordinary writes retain it. -/
def localWrite (frame : FrameState) (global : GlobalState) (threads : ThreadManager)
    (localId : Nat) (storageLive : Bool) : Result Unit := Id.run do
  if !global.raceDetecting then return ⟨frame, global, .ok ()⟩
  let (index, clocks) ← match global.activeThreadState threads with
    | .error error => return ⟨frame, global, .error (.global error)⟩
    | .ok value => pure value
  let localClocks := if storageLive then
      { write := clocks.clock.index index, writeType := .Allocate, read := .ZERO }
    else { frame.get localId with write := clocks.clock.index index, writeType := .Write }
  return ⟨frame.set localId localClocks, global, .ok ()⟩

/-- Source local_read first sets the active timestamp's packed read type,
then saves that full timestamp into the local map, without incrementing time. -/
def localRead (frame : FrameState) (global : GlobalState) (threads : ThreadManager)
    (localId : Nat) : Result Unit := Id.run do
  if !global.raceDetecting then return ⟨frame, global, .ok ()⟩
  let (index, clocks) ← match global.activeThreadState threads with
    | .error error => return ⟨frame, global, .error (.global error)⟩
    | .ok value => pure value
  let clock ← match clocks.clock.applyReadType index .Read with
    | .error error => return ⟨frame, global, .error (.clock error)⟩
    | .ok value => pure value
  let updated := { clocks with clock }
  let global := { global with vectorClocks := global.vectorClocks.set index.toNat updated }
  let localClocks := { frame.get localId with read := clock.index index }
  return ⟨frame.set localId localClocks, global, .ok ()⟩

structure MaterializeResult where
  frame : FrameState
  allocation : VClockAlloc
  outcome : Except Error Unit

private def transferCell (index : VectorIdx) (clocks : LocalClocks)
    (cell : MemoryCellClocks) : Except Error MemoryCellClocks := do
  unless cell.write.1 == index do throw (.allocationWriterMismatch index cell.write.1)
  return { cell with
    write := (index, clocks.write)
    writeType := clocks.writeType
    read := VClock.newWithIndex index clocks.read }

/-- Transfer *historical* local times, not allocation/materialization time.
Each byte's atomic metadata is retained. The local map entry is removed before
any assertion; earlier bytes remain updated on a later invariant failure. -/
def localMovedToMemory (frame : FrameState) (global : GlobalState) (threads : ThreadManager)
    (localId : Nat) (allocation : VClockAlloc) : MaterializeResult := Id.run do
  if !global.raceDetecting then return ⟨frame, allocation, .ok ()⟩
  let (index, _) ← match global.activeThreadState threads with
    | .error error => return ⟨frame, allocation, .error (.global error)⟩
    | .ok value => pure value
  let clocks := frame.get localId
  let frame := frame.remove localId
  let mut allocation := allocation
  for offset in [:allocation.allocRanges.length.bytes] do
    let cell ← match allocation.cellAt offset with
      | .error error => return ⟨frame, allocation, .error (.memory error)⟩
      | .ok value => pure value
    let transferred ← match transferCell index clocks cell with
      | .error error => return ⟨frame, allocation, .error error⟩
      | .ok value => pure value
    match allocation.setCell offset transferred with
    | .error error => return ⟨frame, allocation, .error (.memory error)⟩
    | .ok value => allocation := value
  return ⟨frame, allocation, .ok ()⟩

end Miri.Concurrency.LocalRace
