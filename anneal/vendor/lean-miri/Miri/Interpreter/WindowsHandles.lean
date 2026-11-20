import Miri.Interpreter.Files
import Miri.Concurrency.Thread

/-! Entire pinned windows/handle.rs runtime policy. Packing constants are Miri's
private enum encoding, not guessed Windows ABI constants. -/
namespace Miri.Interpreter.WindowsHandles
open Miri.ABI Miri.Memory Miri.Concurrency
abbrev M := EStateM StepError
inductive Pseudo where | currentThread | currentProcess deriving DecidableEq, Repr
inductive Handle where
  | null | pseudo (value : Pseudo) | thread (id : ThreadId) | file (fd : Int32) | invalid
  deriving DecidableEq, Repr
inductive HandleError where | threadNotFound | invalidHandle deriving DecidableEq, Repr

def packed (handle : Handle) : Except StepError UInt32 := do
  let (disc,data) : UInt32 × UInt32 := match handle with
    | .null => (0,0)
    | .pseudo .currentThread => (1,0)
    | .pseudo .currentProcess => (1,1)
    | .thread id => (2,UInt32.ofNat id.toNat)
    | .file fd => (3,fd.toUInt32)
    | .invalid => (7,0x1fffffff)
  if data >= 0x20000000 then throw (.invalidProgram "handle data exceeds source29bit packing")
  return (disc <<< 29) ||| data

def fromPacked (value : UInt32) : Option Handle :=
  let data := value &&& 0x1fffffff
  match (value >>> 29).toNat with
  | 0 => if data == 0 then some .null else none
  | 1 => if data == 0 then some (.pseudo .currentThread) else if data == 1 then some (.pseudo .currentProcess) else none
  | 2 => some (.thread (ThreadId.ofU32 data.toNat (by exact data.toNat_lt_size)))
  | 3 => some (.file data.toInt32)
  | 7 => some .invalid
  | _ => none

structure Hooks (S F : Type) where
  pointerSize : Size
  readScalar : OpTy Provenance → M S (Scalar Provenance)
  /-- Scalar.to_target_isize includes pointer-to-int/size errors. -/
  targetIsize : Scalar Provenance → M S Int
  readI32 : OpTy Provenance → M S Int32
  readU32 : OpTy Provenance → M S UInt32
  readPointer : OpTy Provenance → M S (Pointer (Option Provenance))
  isNull : Pointer (Option Provenance) → M S Bool
  windows : String → M S (Scalar Provenance)
  scalarI32 : Scalar Provenance → M S Int32
  threads : M S ThreadManager
  detachThread : ThreadId → Bool → M S Unit
  lookupFd : Int32 → M S (Option F)
  /-- Transfers one existing owned reference into actual FD table. -/
  insertFd : F → M S Int32
  removeFd : Int32 → M S (Option F)
  dropFd : F → M S Unit
  derefUsize : OpTy Provenance → M S (MPlaceTy Provenance)
  writeScalar : Scalar Provenance → MPlaceTy Provenance → M S Unit

def toScalar (h : Hooks S F) (handle : Handle) : M S (Scalar Provenance) := do
  let bits ← match packed handle with | .ok bits => pure bits | .error error => throw error
  match Scalar.fromInt bits.toInt32.toInt h.pointerSize with
  | .ok value => return value
  | .error _ => throw (.invalidProgram "handle target-isize construction failed")

def tryFromScalar (h : Hooks S F) (value : Scalar Provenance) : M S (Except HandleError Handle) := do
  let value ← h.targetIsize value
  if value < -2147483648 || value > 2147483647 then return .error .invalidHandle
  match fromPacked (Int32.ofInt value).toUInt32 with
  | none => return .error .invalidHandle
  | some (.thread id) =>
    match (← h.threads).threadIdTryFrom id.toNat with
    | .ok actual => return .ok (.thread actual)
    | .error (.terminated actual) => return .ok (.thread actual)
    | .error _ => return .error .threadNotFound
  | some handle => return .ok handle

def invalid (functionName : String) : M S A :=
  throw (.termination (.abort s!"invalid handle passed to `{functionName}`"))

def read (h : Hooks S F) (value : OpTy Provenance) (functionName : String) : M S Handle := do
  let scalar ← h.readScalar value
  match ← tryFromScalar h scalar with
  | .ok handle => return handle
  | .error error =>
    let value ← h.targetIsize scalar
    let kind := if error == .threadNotFound then "invalid thread ID" else "invalid handle"
    throw (.termination (.abort s!"{kind} {value} passed to {functionName}"))

def stdHandle (h : Hooks S F) (which : OpTy Provenance) : M S (Scalar Provenance) := do
  let which ← h.readI32 which
  let input ← h.scalarI32 (← h.windows "STD_INPUT_HANDLE")
  let output ← h.scalarI32 (← h.windows "STD_OUTPUT_HANDLE")
  let error ← h.scalarI32 (← h.windows "STD_ERROR_HANDLE")
  let fd ← if which == input then pure (0 : Int32) else if which == output then pure 1
    else if which == error then pure 2 else throw (.unsupported "invalid GetStdHandle argument")
  toScalar h (.file fd)

def duplicate (h : Hooks S F) (sourceProcess source targetProcess target access inherit options : OpTy Provenance) :
    M S (Scalar Provenance) := do
  let sourceProcess ← read h sourceProcess "DuplicateHandle"
  let source ← read h source "DuplicateHandle"
  let targetProcess ← read h targetProcess "DuplicateHandle"
  let targetPointer ← h.readPointer target
  let _ ← h.readU32 access
  let _ ← h.readScalar inherit
  let options ← h.readScalar options
  if sourceProcess != .pseudo .currentProcess then throw (.unsupported "DuplicateHandle source process is not current process")
  if targetProcess != .pseudo .currentProcess then throw (.unsupported "DuplicateHandle target process is not current process")
  if ← h.isNull targetPointer then throw (.termination (.abort "DuplicateHandle target must not be null (new handle would leak)"))
  if options != (← h.windows "DUPLICATE_SAME_ACCESS") then throw (.unsupported "DuplicateHandle options must be DUPLICATE_SAME_ACCESS")
  let handle ← match source with
    | .file number => do
      let some fd ← h.lookupFd number | invalid "DuplicateHandle"
      pure (Handle.file (← h.insertFd fd))
    | .thread _ => throw (.unsupported "DuplicateHandle thread handle unsupported")
    | .pseudo _ => throw (.unsupported "DuplicateHandle pseudo handle unsupported")
    | _ => invalid "DuplicateHandle"
  let place ← h.derefUsize target
  h.writeScalar (← toScalar h handle) place
  h.windows "TRUE"

def close (h : Hooks S F) (operand : OpTy Provenance) : M S (Scalar Provenance) := do
  match ← read h operand "CloseHandle" with
  | .thread thread => h.detachThread thread true; h.windows "TRUE"
  | .file number =>
    let some fd ← h.removeFd number | invalid "CloseHandle"
    h.dropFd fd
    h.windows "TRUE"
  | _ => invalid "CloseHandle"
end Miri.Interpreter.WindowsHandles
