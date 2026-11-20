import Miri.Interpreter.UnixEnvironment

/-! Remaining pinned windows/env.rs host-path operations. Windows environment
storage and buffer-size policy reuse EnvVars rather than another environment. -/
namespace Miri.Interpreter.WindowsEnvironment
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
structure Hooks (S Os E Kind : Type) where
  env : EnvVars.Hooks (Option Provenance) Os S
  strings : OsStrings.Hooks Provenance S Os Kind
  process : EnvVars.ProcessHooks S
  errors : IoError.Hooks S E
  readU32 : OpTy Provenance → M S UInt32
  readPointer : OpTy Provenance → M S (Pointer (Option Provenance))
  readIsize : OpTy Provenance → M S Int
  readPlaceU32 : MPlaceTy Provenance → M S UInt32
  derefU32 : OpTy Provenance → M S (MPlaceTy Provenance)
  writeU32 : UInt32 → MPlaceTy Provenance → M S Unit
  isolationReject : String → M S Bool
  checkNoIsolation : String → M S Unit
  currentDirectory : M S (Except (IoError.HostError E) Os)
  setCurrentDirectory : Os → M S (Except (IoError.HostError E) Unit)
  userHomeDirectory : M S (Option Os)
  temporaryDirectory : M S Os
  windows : String → M S (Scalar Provenance)
private def lift (value : Except StepError A) : M S A :=
  match value with | .ok value => pure value | .error error => throw error
private def denied (h : Hooks S O E K) : M S Unit := do
  IoError.setLastError h.errors (.host (← h.errors.hostFromKind .PermissionDenied))

def getcwd (h : Hooks S O E K) (size buf : OpTy Provenance) : M S UInt32 := do
  let size ← h.readU32 size
  let buf ← h.readPointer buf
  if ← h.isolationReject "`GetCurrentDirectoryW`" then denied h; return 0
  match ← h.currentDirectory with
  | .error error => IoError.setLastError h.errors (.host error); return 0
  | .ok path => lift (EnvVars.windowsBufferSize (← OsStrings.writePath h.strings path buf size.toUInt64 true))

def chdir (h : Hooks S O E K) (path : OpTy Provenance) : M S (Scalar Provenance) := do
  let path ← OsStrings.readPath h.strings (← h.readPointer path) true
  if ← h.isolationReject "`SetCurrentDirectoryW`" then
    denied h
    return ← h.windows "FALSE"
  match ← h.setCurrentDirectory path with
  | .ok () => h.windows "TRUE"
  | .error error => IoError.setLastError h.errors (.host error); h.windows "FALSE"

def profile (h : Hooks S O E K) (token buf size : OpTy Provenance) : M S Bool := do
  h.checkNoIsolation "`GetUserProfileDirectoryW`"
  let token ← h.readIsize token
  let buf ← h.readPointer buf
  let size ← h.derefU32 size
  if token != -4 then throw (.unsupported "GetUserProfileDirectoryW only CURRENT_PROCESS_TOKEN supported")
  match ← h.userHomeDirectory with
  | none =>
    IoError.setLastError h.errors (.raw (← h.windows "ERROR_BAD_USER_PROFILE"))
    return false
  | some home =>
    let available ← if ← h.env.isNull buf then pure 0 else h.readPlaceU32 size
    let (success,length) ← OsStrings.writePath h.strings home buf available.toUInt64 true
    if length >= 2^32 then throw (.invalidProgram "profile required length exceeds u32")
    h.writeU32 (UInt32.ofNat length.toNat) size
    if !success then IoError.setLastError h.errors (.raw (← h.windows "ERROR_INSUFFICIENT_BUFFER"))
    return success

def tempPath (h : Hooks S O E K) (length buf : OpTy Provenance) : M S UInt32 := do
  h.checkNoIsolation "`GetTempPathW`"
  let length ← h.readU32 length
  let buf ← h.readPointer buf
  let path ← h.temporaryDirectory
  lift (EnvVars.windowsBufferSize (← OsStrings.writePath h.strings path buf length.toUInt64 true))
end Miri.Interpreter.WindowsEnvironment
