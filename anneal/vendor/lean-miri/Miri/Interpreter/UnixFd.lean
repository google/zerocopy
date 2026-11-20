import Miri.Interpreter.Files

/-! Pinned unix/fd.rs close/dup/dup2/read/write and read_from_fd/write_to_fd;
plus FileHandle positional I/O from unix/fs.rs. Async finish is a real closure. -/
namespace Miri.Interpreter.UnixFd
open Miri.ABI Miri.Memory Files
abbrev M := EStateM StepError
structure Hooks (S H D O E Meta : Type) where
  files : Files.Hooks S H D O E Meta
  errors : IoError.Hooks S E
  os : String
  communicate : Bool
  shortFdOperations : Bool
  targetIsizeMax : UInt64
  hostIsizeMax : UInt64
  table : M S (Files.Table (Description H D O))
  putTable : Files.Table (Description H D O) → M S Unit
  /-- Actual Rc clone/drop semantics. Pending IO owns its transferred strong ref;
  weak-reference liveness must count those owners, not just table entries. -/
  newReference : Description H D O → M S (Files.Ref (Description H D O))
  cloneRef : Files.Ref (Description H D O) → M S (Files.Ref (Description H D O))
  dropRef : Files.Ref (Description H D O) → M S Unit
  asUnix : Files.Ref (Description H D O) → M S Unit
  removeFileNumInterests : Files.Ref (Description H D O) → Int32 → M S Unit
  checkAccess : Pointer (Option Provenance) → Size → M S Unit
  randomShort : M S Bool
  writeInt : Int → MPlaceTy Provenance → M S Unit
  otherPositionalRead : Files.Ref (Description H D O) → UInt64 → Pointer (Option Provenance) → Nat → Finish S E → M S Unit
  otherPositionalWrite : Files.Ref (Description H D O) → UInt64 → Pointer (Option Provenance) → Nat → Finish S E → M S Unit
private def getFd (h : Hooks S H D O E Meta) (number : Int32) : M S (Option (Files.Ref (Description H D O))) := do
  let some ref := (← h.table).get number | return none
  return some (← h.cloneRef ref)
private def lift (r : Except StepError A) : M S A :=
  match r with | .ok value => pure value | .error error => throw error

def close (h : Hooks S H D O E Meta) (number : Int32) : M S Int32 := do
  let (table,ref) := (← h.table).remove number
  h.putTable table
  let some ref := ref | return ← IoError.setErrnoAndReturnNeg1I32 h.errors (.libc "EBADF")
  h.asUnix ref
  if h.os == "illumos" && Files.hasReadinessWatched h.files ref.value then
    h.removeFileNumInterests ref number
  h.dropRef ref
  return 0

def dup (h : Hooks S H D O E Meta) (number : Int32) : M S Int32 := do
  let some ref ← getFd h number | return ← IoError.setErrnoAndReturnNeg1I32 h.errors (.libc "EBADF")
  let (table,number) ← lift ((← h.table).insert ref)
  h.putTable table
  return number

def dup2 (h : Hooks S H D O E Meta) (old new : Int32) : M S Int32 := do
  let some ref ← getFd h old | return ← IoError.setErrnoAndReturnNeg1I32 h.errors (.libc "EBADF")
  if old != new then
    if (← h.table).isFdNum new then
      -- Source get(new).is_some clones/drops one temporary reference.
      let some temporary ← getFd h new | throw (.invalidProgram "FD disappeared during dup2")
      h.dropRef temporary
      if (← close h new) != 0 then throw (.invalidProgram "dup2 close unexpectedly failed")
    let (table,actual) ← lift ((← h.table).insertWithMin ref new)
    h.putTable table
    if actual != new then throw (.invalidProgram "dup2 inserted at wrong FD number")
  else h.dropRef ref
  return new

private def positional (h : Hooks S H D O E Meta) (ref : Files.Ref (Description H D O))
    (pointer : Pointer (Option Provenance)) (len : Nat) (offset : UInt64)
    (write : Bool) (finish : Finish S E) : M S Unit := do
  h.asUnix ref
  match ref.value with
  | .file handle readable writable =>
    if !h.communicate then throw (.invalidProgram "isolation should prevent opening file")
    if (if write then !writable else !readable) then
      finish (.error (.libc "EBADF"))
      return
    let bytes ← if write then h.files.readBytes pointer (Size.ofBytes (UInt64.ofNat len))
      else pure (ByteArray.mk (Array.replicate len 0))
    -- Source stream_position then seek; failure before operation does not restore.
    match ← h.files.hostSeek handle (.current 0) with
    | .error error => finish (.error (.host error))
    | .ok position =>
      match ← h.files.hostSeek handle (.start offset) with
      | .error error => finish (.error (.host error))
      | .ok _ =>
        let result ← if write then
            (h.files.hostWrite ref.value bytes).map fun r => r.map fun size => (size,bytes)
          else h.files.hostRead ref.value bytes
        if let .error _ ← h.files.hostSeek handle (.start position) then
          throw (.invalidProgram "failed to restore file position")
        match result with
        | .error error => finish (.error (.host error))
        | .ok (size,bytes) =>
          if size > len || bytes.size != len then throw (.invalidProgram "host positional IO buffer bounds violated")
          if !write then h.files.writeBytes pointer (bytes.extract 0 size)
          finish (.ok size)
  | .other _ =>
    if write then h.otherPositionalWrite ref offset pointer len finish
    else h.otherPositionalRead ref offset pointer len finish
  | _ => throw (.unsupported "positional IO unsupported for this FD type")

private def transfer (h : Hooks S H D O E Meta) (ref : Files.Ref (Description H D O))
    (pointer : Pointer (Option Provenance)) (len : Nat) (offset : Option Int)
    (write : Bool) (finish : Finish S E) : M S Unit := do
  if len == 0 then Files.withDrop (finish (.ok 0)) (h.dropRef ref); return
  let mut len := len
  if h.shortFdOperations && Files.shortOperations h.files ref.value && len >= 2 then
    if ← h.randomShort then len := len / 2
  if let some offset := offset then
    if offset < 0 || offset >= 2^64 then Files.withDrop (finish (.error (.libc "EINVAL"))) (h.dropRef ref); return
    let action := positional h ref pointer len (UInt64.ofNat offset.toNat) write finish
    match ref.value with
    | .other _ => action
    | _ => Files.withDrop action (h.dropRef ref)
  else
    let action := if write then Files.write h.files ref h.communicate pointer len finish
      else Files.read h.files ref h.communicate pointer len finish
    match ref.value with
    | .other _ => action
    | _ => Files.withDrop action (h.dropRef ref)

/-- Full requested range is checked before count capping and FD lookup. The
finish closure owns all return-value work even if the description blocks. -/
def readWrite (h : Hooks S H D O E Meta) (number : Int32) (pointer : Pointer (Option Provenance))
    (count : UInt64) (offset : Option Int) (write : Bool) (dest : MPlaceTy Provenance) : M S Unit := do
  h.checkAccess pointer (Size.ofBytes count)
  let count := min count (min h.targetIsizeMax h.hostIsizeMax)
  let some ref ← getFd h number | IoError.setErrnoAndReturnNeg1 h.errors (.libc "EBADF") dest; return
  transfer h ref pointer count.toNat offset write (IoCompletionData.Finish.source (.unixScalar count.toNat dest) fun result => do
    match result with
    | .ok size =>
      if size > count.toNat then throw (.invalidProgram "FD returned more bytes than requested")
      h.writeInt (Int.ofNat size) dest
    | .error error => IoError.setErrnoAndReturnNeg1 h.errors error dest)
/-- Source internal read_from_fd/write_to_fd entry: unlike read/write wrappers,
no count capping or pre-lookup range check is inserted here. Ownership of ref
is transferred to the actual operation, including a delayed finish callback. -/
def transferDescription (h : Hooks S H D O E Meta) (ref : Files.Ref (Description H D O))
    (pointer : Pointer (Option Provenance)) (len : Nat) (offset : Option Int)
    (write : Bool) (finish : Finish S E) : M S Unit :=
  transfer h ref pointer len offset write finish
end Miri.Interpreter.UnixFd
