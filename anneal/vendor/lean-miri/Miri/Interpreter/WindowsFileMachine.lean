import Miri.Interpreter.WindowsFileDispatch
import Miri.Interpreter.UnixFsMachine
import Miri.Interpreter.TimeShims

/-! Windows handles/files connected to canonical FD ownership, machine threads,
FileDescription effects, shared host open and source OS strings/time helpers. -/
namespace Miri.Interpreter.WindowsFileMachine
open Miri.ABI Miri.Memory Miri.Concurrency Files
abbrev Ref (H D O : Type) := Files.Ref (Description H D O)
private def lift (value : Except StepError A) : MachineHooks.M K U A :=
  match value with | .ok value => pure value | .error error => throw error

def bindHandles (h : ReadinessMachine.Hooks K U H D O) (target : RuntimeTargetDataLayout)
    (threadError : ThreadError → StepError)
    (base : WindowsHandles.Hooks (MachineHooks.State K U) (Ref H D O)) :
    WindowsHandles.Hooks (MachineHooks.State K U) (Ref H D O) := {
  base with
  pointerSize := target.pointerSize
  threads := do return (← get).machine.threads
  detachThread := fun id allowTerminatedJoined => do
    let threads ← lift (((← get).machine.threads.detachThread id allowTerminatedJoined).mapError threadError)
    modify fun state => { state with machine := { state.machine with threads := threads } }
  lookupFd := fun number => do
    let some ref := (h.files.table (← get).machine.user).get number | return none
    return some (← FileMachine.cloneReference h.files ref)
  insertFd := fun ref => do
    let (table,number) ← lift ((h.files.table (← get).machine.user).insert ref)
    modify fun state => { state with machine := { state.machine with user := h.files.setTable table state.machine.user } }
    return number
  removeFd := fun number => do
    let (table,ref) := (h.files.table (← get).machine.user).remove number
    modify fun state => { state with machine := { state.machine with user := h.files.setTable table state.machine.user } }
    return ref
  dropFd := ReadinessMachine.dropFd h }

/-- Default host/file descriptions drop at the call boundary. Custom descriptions
own the transferred reference and typed continuation for real blocked I/O. -/
def readWrite (h : ReadinessMachine.Hooks K U H D O)
    (files : Files.Hooks (MachineHooks.State K U) H D O E HM)
    (ref : Ref H D O) (communicate write : Bool) (pointer : Pointer (Option Provenance))
    (count : Nat) (finish : Files.Finish (MachineHooks.State K U) E) : MachineHooks.M K U Unit := do
  let action := if write then Files.write files ref communicate pointer count finish
    else Files.read files ref communicate pointer count finish
  match ref.value with
  | .other _ => action
  | _ => Files.withDrop action (ReadinessMachine.dropFd h ref)

def bind (h : ReadinessMachine.Hooks K U H D O) (target : RuntimeTargetDataLayout)
    (threadError : ThreadError → StepError)
    (files : Files.Hooks (MachineHooks.State K U) H D O E HM)
    (sharedOpen : UnixOpen.Hooks (MachineHooks.State K U) H D O E HM P)
    (otherMetadata : O → MachineHooks.M K U (Sum (Except (IoError.HostError E) HM) String))
    /- Non-bootstrap identity; bootstrap actual path.canonicalize().unwrap plus fallback. -/
    (prepareDirectory : D → P → MachineHooks.M K U D)
    (base : WindowsPaths.Hooks (MachineHooks.State K U) (Ref H D O) H D P HM T E Kind) :
    WindowsPaths.Hooks (MachineHooks.State K U) (Ref H D O) H D P HM T E Kind :=
  let file := { base.files with
    handles := bindHandles h target threadError base.files.handles
    readWidePath := fun pointer => OsStrings.readPath base.strings pointer true
    openFileOrDir := fun path options => UnixOpen.openFileOrDir sharedOpen none path options
    dropFile := sharedOpen.dropFile
    dropDirectory := sharedOpen.dropDirectory
    insertFile := fun handle readable writable =>
      (UnixFsMachine.insertDescription h (.file handle readable writable)).map Prod.fst
    insertDirectory := fun directory path => do
      let directory ← prepareDirectory directory path
      (UnixFsMachine.insertDescription h (.directory directory)).map Prod.fst
    asFile := fun ref => match ref.value with | .file handle _ writable => some ⟨handle,writable⟩ | _ => none
    metadata := fun ref => do
      match ref.value with
      | .file .. | .directory .. => return .inl (← files.hostMetadata ref.value)
      | .other payload => otherMetadata payload
      | _ => throw (.unsupported "obtaining metadata requires file-backed description")
    seek := fun ref communicate offset => Files.seek files communicate ref.value offset
    readWrite := readWrite h files }
  { base with files := file }

/-- Epoch/tick arithmetic stays canonical TimeShims, including before-epoch and
u64 overflow outcomes, rather than a caller-computed time snapshot. -/
def bindTime (time : TimeShims.Hooks S Host T Zone Stamp)
    (base : WindowsFiles.Hooks S F H D P HM T E) : WindowsFiles.Hooks S F H D P HM T E := {
  base with windowsTicks := fun value => do
    let duration ← TimeShims.systemTimeSinceWindowsEpoch time value
    match TimeShims.windowsTicksFor duration with
    | .ok ticks => return ticks
    | .error error => throw error }
end Miri.Interpreter.WindowsFileMachine
