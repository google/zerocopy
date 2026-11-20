import Miri.Interpreter.UnixFsDispatch
import Miri.Interpreter.UnixFileOperations
import Miri.Interpreter.ReadinessMachine
import Miri.Interpreter.RawMemoryMachine

/-! Canonical filesystem binding: actual FD identities/ownership, real DIR
registry and race/borrow-aware raw output. Host resources/metadata remain leaves. -/
namespace Miri.Interpreter.UnixFsMachine
open Miri.ABI Miri.Memory Files
abbrev Ref (H D O : Type) := Files.Ref (Description H D O)
private def lift (value : Except StepError A) : MachineHooks.M K U A :=
  match value with | .ok value => pure value | .error error => throw error

def bindMetadata (h : ReadinessMachine.Hooks K U H D O)
    (files : Files.Hooks (MachineHooks.State K U) H D O E HM)
    (otherMetadata : O → MachineHooks.M K U (Sum (Except (IoError.HostError E) HM) String))
    (base : UnixFsMetadata.Hooks (MachineHooks.State K U) (Ref H D O) D P HM T E) :
    UnixFsMetadata.Hooks (MachineHooks.State K U) (Ref H D O) D P HM T E := {
  base with
  lookupFd := fun number => do
    let some ref := (h.files.table (← get).machine.user).get number | return none
    return some (← FileMachine.cloneReference h.files ref)
  dropFd := ReadinessMachine.dropFd h
  asDirectory := fun ref => match ref.value with | .directory dir => some dir | _ => none
  fdMetadata := fun ref => do
    match ref.value with
    | .file .. | .directory .. => return .inl (← files.hostMetadata ref.value)
    | .other value => otherMetadata value
    | _ => throw (.unsupported "obtaining metadata requires file-backed description") }

/-- Entire actual owned handle insertion, with stable source descriptor identity. -/
def insertDescription (h : ReadinessMachine.Hooks K U H D O) (description : Description H D O) :
    MachineHooks.M K U (Int32 × FdId) := do
  let ref ← FileMachine.newReference h.files description
  let (table,number) ← lift ((h.files.table (← get).machine.user).insert ref)
  modify fun state => { state with machine := { state.machine with user := h.files.setTable table state.machine.user } }
  return (number,ref.id)
structure DirectoryStore (U R : Type) where
  get : U → UnixDirectories.Table R
  put : UnixDirectories.Table R → U → U

def bindDirectories (h : ReadinessMachine.Hooks K U H D O)
    (store : DirectoryStore U R)
    (readiness : Readiness.Hooks (MachineHooks.State K U) (Ref H D O))
    (fd : UnixFd.Hooks (MachineHooks.State K U) H D O E HM)
    (base : UnixDirectories.Hooks (MachineHooks.State K U) (Ref H D O) D P HM T E Kind R Ent) :
    UnixDirectories.Hooks (MachineHooks.State K U) (Ref H D O) D P HM T E Kind R Ent := {
  base with
  get := do return store.get (← get).machine.user
  put := fun table => modify fun state => { state with machine := { state.machine with user := store.put table state.machine.user } }
  id := Files.Ref.id
  insertDirectory := fun directory => insertDescription h (.directory directory)
  closeFd := UnixFd.close (ReadinessMachine.bindFiles h readiness fd) }
def bindFd (_h : ReadinessMachine.Hooks K U H D O)
    (files : Files.Hooks (MachineHooks.State K U) H D O E HM)
    (base : UnixFsFd.Hooks (MachineHooks.State K U) (Ref H D O) D P HM T E Kind H) :
    UnixFsFd.Hooks (MachineHooks.State K U) (Ref H D O) D P HM T E Kind H := {
  base with
  asFile := fun ref => match ref.value with
    | .file handle readable writable => some ⟨handle,readable,writable⟩
    | _ => none
  seek := fun ref communicate offset => Files.seek files communicate ref.value offset
  isTty := fun ref communicate => Files.isTty files communicate ref.value }

def bindTemporary (h : ReadinessMachine.Hooks K U H D O)
    (base : UnixTempFile.Hooks (MachineHooks.State K U) (Ref H D O) D P HM T E Kind H) :
    UnixTempFile.Hooks (MachineHooks.State K U) (Ref H D O) D P HM T E Kind H := {
  base with insertFile := fun handle readable writable =>
    (insertDescription h (.file handle readable writable)).map Prod.fst }

/-- FileDescription downcast preserves unsupported default flock on other kinds. -/
def bindFlock (host : UnixFileOperations.Hooks S H E)
    (asUnix : Ref H D O → EStateM StepError S Unit)
    (other : O → Bool → UnixFileOperations.LockOp → EStateM StepError S (Except (IoError.HostError E) Unit))
    (ref : Ref H D O) (communicate : Bool) (operation : UnixFileOperations.LockOp) :
    EStateM StepError S (Except (IoError.HostError E) Unit) := do
  asUnix ref
  match ref.value with
  | .file handle .. => UnixFileOperations.flock host handle communicate operation
  | .other payload => other payload communicate operation
  | _ => throw (.unsupported "cannot flock this file description")

/-- Share one canonical metadata/path/FD adapter through every filesystem arm. -/
def bindAll (h : ReadinessMachine.Hooks K U H D O)
    (files : Files.Hooks (MachineHooks.State K U) H D O E HM)
    (otherMetadata : O → MachineHooks.M K U (Sum (Except (IoError.HostError E) HM) String))
    (store : DirectoryStore U R)
    (readiness : Readiness.Hooks (MachineHooks.State K U) (Ref H D O))
    (fd : UnixFd.Hooks (MachineHooks.State K U) H D O E HM)
    (base : UnixFsDispatch.Hooks (MachineHooks.State K U) (Ref H D O) D P HM T E Kind H R Ent) :
    UnixFsDispatch.Hooks (MachineHooks.State K U) (Ref H D O) D P HM T E Kind H R Ent :=
  let paths := { base.directories.paths with
    metadata := bindMetadata h files otherMetadata base.directories.paths.metadata }
  let directories := bindDirectories h store readiness fd { base.directories with paths := paths }
  let file := bindFd h files { base.times.fd with paths := paths }
  let times := { base.times with fd := file }
  let temporary := bindTemporary h { base.temporary with paths := paths }
  { base with directories := directories, times := times, temporary := temporary }

/-- Reuses actual allocation access (race then borrow checks), initialization
and provenance-clearing writes for readlink and generated directory names. -/
def bindRawWrites [DecidableEq K] (access : PlaceMachine.AccessConfig K U)
    (arithmetic : PointerArithmetic)
    (base : UnixFsPaths.Hooks (MachineHooks.State K U) F D P HM T E Kind) :
    UnixFsPaths.Hooks (MachineHooks.State K U) F D P HM T E Kind := {
  base with writeBytes := RawMemoryMachine.writeBytes access arithmetic }

/-- Actual time reader and SystemTime clock; host checked UNIX_EPOCH arithmetic
and set_times remain the typed filesystem host boundary. -/
def bindTimes (time : TimeShims.Hooks S Host T Zone Stamp)
    (base : UnixFsTimes.Hooks S F D P HM T E Kind H) : UnixFsTimes.Hooks S F D P HM T E Kind H := {
  base with systemNow := time.host.systemNow, readTimespec := TimeShims.readTimespec time }

/-- Source DirTable::visit_provenance visits exactly each last-returned entry. -/
def directoryRoots (table : UnixDirectories.Table R) : Array (Pointer (Option Provenance)) :=
  table.streams.filterMap fun (_,stream) => stream.entry.map Prod.fst
end Miri.Interpreter.UnixFsMachine
