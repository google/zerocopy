import Miri.Interpreter.WindowsEnvironment
import Miri.Interpreter.WindowsHandles

/-! Remaining portable Windows foreign-item policies from the pinned source.
Allocation, compiler layouts and host error text are mandatory typed effects. -/
namespace Miri.Interpreter.WindowsPlatform
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
inductive DynamicSymbol where
  | setThreadDescription | getThreadDescription | waitOnAddress | wakeByAddressSingle
  deriving DecidableEq, Repr
namespace DynamicSymbol
def name : DynamicSymbol → String
  | .setThreadDescription => "SetThreadDescription" | .getThreadDescription => "GetThreadDescription"
  | .waitOnAddress => "WaitOnAddress" | .wakeByAddressSingle => "WakeByAddressSingle"
def parse : String → Option DynamicSymbol
  | "SetThreadDescription" => some .setThreadDescription | "GetThreadDescription" => some .getThreadDescription
  | "WaitOnAddress" => some .waitOnAddress | "WakeByAddressSingle" => some .wakeByAddressSingle
  | _ => none
end DynamicSymbol
inductive HeapKind where | heap | local deriving DecidableEq, Repr
structure Hooks (S O E K F : Type) where
  environment : WindowsEnvironment.Hooks S O E K
  handles : WindowsHandles.Hooks S F
  pointerSize : Size
  readUsize : OpTy Provenance → M S UInt64
  readScalar : OpTy Provenance → M S (Scalar Provenance)
  allocate : Size → Align → AllocInit → HeapKind → M S (Pointer (Option Provenance))
  deallocate : Pointer (Option Provenance) → HeapKind → M S Unit
  reallocate : Pointer (Option Provenance) → Size → Align → HeapKind → M S (Pointer (Option Provenance))
  nullPointer : Pointer (Option Provenance)
  /-- fn_ptr(FnVal::Other(...)): source always reserves a fresh identity. -/
  functionPointer : DynamicSymbol → M S (Pointer (Option Provenance))
  readCString : Pointer (Option Provenance) → M S ByteArray
  commandLine : M S (Option (Pointer (Option Provenance)))
  currentExe : M S (Option O)
  derefSystemInfo : OpTy Provenance → M S (MPlaceTy Provenance)
  derefPointer : OpTy Provenance → M S Unit
  projectNamed : MPlaceTy Provenance → String → M S (MPlaceTy Provenance)
  zeroBytes : Pointer (Option Provenance) → UInt64 → M S Unit
  writeInt : Int → MPlaceTy Provenance → M S Unit
  hostErrorDisplay : IoError.HostError E → M S O
  unknownMessageDisplay : Scalar Provenance → M S O
  pageSize : UInt64
  numCpus : UInt32
private def lift (value : Except StepError A) : M S A :=
  match value with | .ok value => pure value | .error error => throw error
private def alignment (h : Hooks S O E K F) : M S Align := do
  let size := h.pointerSize.bytes.toNat * 2
  if size >= 2^64 then throw (.invalidProgram "HeapAlloc alignment strict_mul overflow")
  match Align.fromBytes (UInt64.ofNat size) with
  | .ok align => pure align
  | .error error => throw (.invalidProgram s!"Windows heap alignment: {reprStr error}")

def heapAlloc (h : Hooks S O E K F) (handle flags size : OpTy Provenance) : M S (Pointer (Option Provenance)) := do
  let _ ← h.environment.readIsize handle
  let flags ← h.environment.readU32 flags
  let size ← h.readUsize size
  h.allocate (Size.ofBytes size) (← alignment h) (if flags &&& 8 == 8 then .Zero else .Uninit) .heap

def heapFree (h : Hooks S O E K F) (handle flags pointer : OpTy Provenance) : M S Unit := do
  let _ ← h.environment.readIsize handle
  let _ ← h.environment.readU32 flags
  let ptr ← h.environment.readPointer pointer
  if !(← h.handles.isNull ptr) then h.deallocate ptr .heap

def heapRealloc (h : Hooks S O E K F) (handle flags pointer size : OpTy Provenance) : M S (Pointer (Option Provenance)) := do
  let _ ← h.environment.readIsize handle
  let _ ← h.environment.readU32 flags
  let ptr ← h.environment.readPointer pointer
  let size ← h.readUsize size
  h.reallocate ptr (Size.ofBytes size) (← alignment h) .heap

def localFree (h : Hooks S O E K F) (pointer : OpTy Provenance) : M S Unit := do
  let ptr ← h.environment.readPointer pointer
  if !(← h.handles.isNull ptr) then h.deallocate ptr .local

/-- Literal table in upstream, including fallback ERROR_MR_MID_NOT_FOUND. -/
def ntStatusToDos : UInt32 → UInt32
  | 0xC00000A2 => 19 | 0xC0000098 => 1006 | 0xC000007F => 112
  | 0xC0000185 => 1117 | 0xC0000022 => 5 | _ => 317

def systemInfo (h : Hooks S O E K F) (output : OpTy Provenance) : M S Unit := do
  let output ← h.derefSystemInfo output
  h.zeroBytes output.mplace.ptr output.layout.layout.size.bytes
  h.writeInt (Int.ofNat h.pageSize.toNat) (← h.projectNamed output "dwPageSize")
  h.writeInt (Int.ofNat h.numCpus.toNat) (← h.projectNamed output "dwNumberOfProcessors")

def getProcAddress (h : Hooks S O E K F) (module name : OpTy Provenance) : M S (Pointer (Option Provenance)) := do
  let _ ← h.environment.readIsize module
  let name ← h.readCString (← h.environment.readPointer name)
  let some name := String.fromUTF8? name | return h.nullPointer
  let some symbol := DynamicSymbol.parse name | return h.nullPointer
  h.functionPointer symbol

def moduleFileName (h : Hooks S O E K F) (handle output size : OpTy Provenance)
    (dest : MPlaceTy Provenance) : M S Unit := do
  h.environment.checkNoIsolation "`GetModuleFileNameW`"
  let handle ← WindowsHandles.read h.handles handle "GetModuleFileNameW"
  let output ← h.environment.readPointer output
  let size ← h.environment.readU32 size
  if handle != .null then throw (.unsupported "GetModuleFileNameW only supports NULL handle")
  let some path ← h.currentExe | throw (.unsupported "GetModuleFileNameW requires file-backed Miri execution")
  let path ← lift (OsStrings.convertPath h.environment.strings path .hostToTarget)
  let (complete,needed) ← OsStrings.writeOsWideString h.environment.strings path output size.toUInt64 true
  if complete then
    if needed == 0 then throw (.invalidProgram "module filename strict_sub underflow")
    h.writeInt (Int.ofNat needed.toNat-1) dest
  else
    h.writeInt (Int.ofNat size.toNat) dest
    IoError.setLastError h.environment.errors (.raw (← h.environment.windows "ERROR_INSUFFICIENT_BUFFER"))

def formatMessage (h : Hooks S O E K F) (flags module message language buffer size arguments : OpTy Provenance) : M S UInt64 := do
  let flags ← h.environment.readU32 flags
  let _ ← h.environment.readPointer module
  let message ← h.readScalar message
  let _ ← h.environment.readU32 language
  let buffer ← h.environment.readPointer buffer
  let size ← h.environment.readU32 size
  let _ ← h.environment.readPointer arguments
  if flags != (4096 ||| 512) then throw (.unsupported "FormatMessageW unsupported flags")
  let formatted ← match ← IoError.tryErrnumToHost h.environment.errors message with
    | some error => h.hostErrorDisplay error
    | none => h.unknownMessageDisplay message
  let (complete,length) ← OsStrings.writeOsWideString h.environment.strings formatted buffer size.toUInt64
  if !complete then throw (.unsupported "FormatMessageW buffer not big enough")
  if length == 0 then throw (.invalidProgram "FormatMessageW strict_sub underflow")
  return length - 1

def timer (h : Hooks S O E K F) (attributes name flags access : OpTy Provenance) : M S Unit := do
  let _ ← h.environment.readPointer attributes
  let _ ← h.environment.readPointer name
  let _ ← h.environment.readU32 flags
  let _ ← h.environment.readU32 access
  IoError.setLastError h.environment.errors (.raw (← h.environment.windows "ERROR_NOT_SUPPORTED"))
end Miri.Interpreter.WindowsPlatform
