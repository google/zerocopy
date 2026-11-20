import Miri.Interpreter.IoError
import Miri.Interpreter.IoCompletionData

/-! Descriptor identities/table and portable FileDescription behavior from
pinned shims/files.rs. Host handles remain real external resources; no virtual
filesystem or readiness-success environment is manufactured. -/
namespace Miri.Interpreter.Files
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
/-- Rust scope drop, including errors. A failing required destructor remains
explicit and keeps its effects; it cannot be silently discarded. -/
def withDrop (action : M S A) (cleanup : M S Unit) : M S A := fun state =>
  match action state with
  | .ok value state =>
    match cleanup state with | .ok _ state => .ok value state | .error error state => .error error state
  | .error error state =>
    match cleanup state with | .ok _ state => .error error state | .error cleanupError state => .error cleanupError state
structure FdId where
  value : Nat
  deriving DecidableEq, Repr
inductive Description (Handle Directory Other : Type) where
  | stdin | stdout | stderr | nullOutput
  | file (handle : Handle) (readable writable : Bool)
  | directory (handle : Directory)
  | other (payload : Other)
structure Ref (Description : Type) where
  id : FdId
  value : Description
instance : BEq (Ref D) := ⟨fun left right => left.id == right.id⟩
structure WeakRef where
  id : FdId
structure Table (Description : Type) where
  fds : Array (Int32 × Ref Description) := #[]
  nextId : Nat := 0

def Table.newRef (table : Table D) (description : D) (hostUsizeBits : Nat) :
    Except StepError (Table D × Ref D) := do
  if table.nextId + 1 >= 2^hostUsizeBits then throw (.invalidProgram "file-description ID strict_add overflow")
  return ({ table with nextId := table.nextId + 1 },⟨⟨table.nextId⟩,description⟩)
def Table.insertWithMin (table : Table D) (ref : Ref D) (minimum : Int32) :
    Except StepError (Table D × Int32) := do
  let sorted := table.fds.qsort (fun a b => a.1 < b.1)
  let mut candidate := minimum
  for (fd,_) in sorted do
    if fd >= minimum then
      if fd == candidate then
        if candidate.toInt == 2^31-1 then throw (.invalidProgram "file descriptor strict_add overflow")
        candidate := Int32.ofInt (candidate.toInt + 1)
      else break
  if table.fds.any (·.1 == candidate) then throw (.invalidProgram "duplicate file descriptor insertion")
  return ({ table with fds := table.fds.push (candidate,ref) },candidate)
def Table.insert (table : Table D) (ref : Ref D) := table.insertWithMin ref 0
def Table.insertNew (table : Table D) (value : D) (hostUsizeBits : Nat) : Except StepError (Table D × Int32) := do
  let (table,ref) ← table.newRef value hostUsizeBits
  table.insert ref
/-- The runtime must retain the returned strong reference (including in pending
callbacks). Table.remove transfers its strong reference rather than duplicating. -/
def Table.get (table : Table D) (fd : Int32) : Option (Ref D) :=
  (table.fds.find? (·.1 == fd)).map (·.2)
def Table.remove (table : Table D) (fd : Int32) : Table D × Option (Ref D) :=
  ({ table with fds := table.fds.filter (·.1 != fd) },table.get fd)
def Table.isFdNum (table : Table D) (fd : Int32) : Bool := table.fds.any (·.1 == fd)
def Table.init (mute : Bool) (hostUsizeBits : Nat) : Except StepError (Table (Description H D O)) := do
  let (table,_) ← ({} : Table (Description H D O)).insertNew .stdin hostUsizeBits
  let (table,first) ← table.insertNew (if mute then .nullOutput else .stdout) hostUsizeBits
  if first != 1 then throw (.invalidProgram "stdout initialization descriptor mismatch")
  let (table,second) ← table.insertNew (if mute then .nullOutput else .stderr) hostUsizeBits
  if second != 2 then throw (.invalidProgram "stderr initialization descriptor mismatch")
  return table

structure Readiness where
  readable : Bool := false
  writable : Bool := false
  readClosed : Bool := false
  writeClosed : Bool := false
  error : Bool := false
  deriving DecidableEq, Repr
inductive SeekFrom where | start (offset : UInt64) | current (offset : Int64) | finish (offset : Int64)
abbrev Result (Host A : Type) := Except (IoError.Error Host) A
abbrev Finish (S Host : Type) := IoCompletionData.Finish S (IoError.Error Host)
structure Hooks (S Handle Directory Other Host Metadata : Type) where
  family : ForeignItems.Family
  hostRead : Description Handle Directory Other → ByteArray → M S (Except (IoError.HostError Host) (Nat × ByteArray))
  hostWrite : Description Handle Directory Other → ByteArray → M S (Except (IoError.HostError Host) Nat)
  hostFlushStdout : M S Unit
  hostSeek : Handle → SeekFrom → M S (Except (IoError.HostError Host) UInt64)
  hostMetadata : Description Handle Directory Other → M S (Except (IoError.HostError Host) Metadata)
  hostIsTerminal : Description Handle Directory Other → M S Bool
  readBytes : Pointer (Option Provenance) → Size → M S ByteArray
  writeBytes : Pointer (Option Provenance) → ByteArray → M S Unit
  permissionDenied : M S (IoError.HostError Host)
  /-- Socket/pipe/event descriptions may block and invoke finish only later.
  Their real readiness/blocking implementation must retain captured strong refs. -/
  otherRead : Ref (Description Handle Directory Other) → Bool → Pointer (Option Provenance) → Nat → Finish S Host → M S Unit
  otherWrite : Ref (Description Handle Directory Other) → Bool → Pointer (Option Provenance) → Nat → Finish S Host → M S Unit
  otherShortOperations : Other → Bool
  otherReadiness : Other → M S (Option Readiness)
  otherHasReadinessWatched : Other → Bool
  otherIsTerminal : Other → Bool → M S Bool

def readFromHost (h : Hooks S H D O E Meta) (description : Description H D O)
    (len : Nat) (pointer : Pointer (Option Provenance)) : M S (Result E Nat) := do
  let initial := ByteArray.mk (Array.replicate len 0)
  match ← h.hostRead description initial with
  | .error error => return .error (.host error)
  | .ok (size,bytes) =>
    if bytes.size != len || size > len then throw (.invalidProgram "host Read violates borrowed buffer bounds")
    h.writeBytes pointer (bytes.extract 0 size)
    return .ok size

def writeToHost (h : Hooks S H D O E Meta) (description : Description H D O)
    (len : Nat) (pointer : Pointer (Option Provenance)) : M S (Result E Nat) := do
  if len >= 2^64 then throw (.invalidProgram "host byte length exceeds u64")
  let bytes ← h.readBytes pointer (Size.ofBytes (UInt64.ofNat len))
  if bytes.size != len then throw (.invalidProgram "machine byte reader returned wrong buffer length")
  return (← h.hostWrite description bytes).mapError .host

def read (h : Hooks S H D O E Meta) (ref : Ref (Description H D O)) (communicate : Bool)
    (pointer : Pointer (Option Provenance)) (len : Nat) (finish : Finish S E) : M S Unit := do
  match ref.value with
  | .stdin =>
    if !communicate then throw (.termination (.unsupportedInIsolation "read from stdin"))
    finish (← readFromHost h ref.value len pointer)
  | .file _ readable _ =>
    if !communicate then throw (.invalidProgram "isolation should prevent opening host file")
    if !readable then
      if h.family == .unix then finish (.error (.libc "EBADF"))
      else finish (.error (.host (← h.permissionDenied)))
    else finish (← readFromHost h ref.value len pointer)
  | .directory _ =>
    if h.family == .unix then finish (.error (.libc "EISDIR"))
    else throw (.unsupported "reading directories unsupported on target")
  | .other _ => h.otherRead ref communicate pointer len finish
  | _ => throw (.unsupported "cannot read from this file description")

def write (h : Hooks S H D O E Meta) (ref : Ref (Description H D O)) (communicate : Bool)
    (pointer : Pointer (Option Provenance)) (len : Nat) (finish : Finish S E) : M S Unit := do
  match ref.value with
  | .stdout =>
    let result ← writeToHost h ref.value len pointer
    h.hostFlushStdout
    finish result
  | .stderr => finish (← writeToHost h ref.value len pointer)
  | .nullOutput => finish (.ok len)
  | .file _ _ writable =>
    if !communicate then throw (.invalidProgram "isolation should prevent opening host file")
    if !writable then
      if h.family == .unix then finish (.error (.libc "EBADF"))
      else finish (.error (.host (← h.permissionDenied)))
    else finish (← writeToHost h ref.value len pointer)
  | .directory _ =>
    if h.family == .unix then finish (.error (.libc "EBADF"))
    else throw (.unsupported "writing directories unsupported on target")
  | .other _ => h.otherWrite ref communicate pointer len finish
  | _ => throw (.unsupported "cannot write to this file description")

def shortOperations (h : Hooks S H D O E Meta) : Description H D O → Bool
  | .file .. => true | .other value => h.otherShortOperations value | _ => false

def readiness (h : Hooks S H D O E Meta) : Description H D O → M S (Option Readiness)
  | .stdin => pure (some { readable := true, writable := true })
  | .stdout | .stderr | .nullOutput => pure (some { writable := true })
  | .file .. | .directory .. => pure none
  | .other value => h.otherReadiness value

def hasReadinessWatched (h : Hooks S H D O E Meta) : Description H D O → Bool
  | .stdin | .stdout | .stderr | .nullOutput => true
  | .file .. | .directory .. => false
  | .other value => h.otherHasReadinessWatched value

def isTty (h : Hooks S H D O E Meta) (communicate : Bool) (description : Description H D O) : M S Bool := do
  match description with
  | .stdin | .stdout | .stderr | .file .. =>
    if communicate then h.hostIsTerminal description else pure false
  | .other value => h.otherIsTerminal value communicate
  | _ => pure false

def seek (h : Hooks S H D O E Meta) (communicate : Bool) (description : Description H D O)
    (offset : SeekFrom) : M S (Result E UInt64) := do
  match description with
  | .file handle .. =>
    if !communicate then throw (.invalidProgram "isolation should prevent opening host file")
    return (← h.hostSeek handle offset).mapError .host
  | _ => throw (.unsupported "cannot seek this file description")
end Miri.Interpreter.Files
