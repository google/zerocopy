import Miri.Interpreter.WindowsHandles
import Miri.Interpreter.ThreadTls
import Miri.Interpreter.ThreadMachine
import Miri.Interpreter.OsStrings

/-! Complete pinned windows/thread.rs and the TLS/FLS/thread-description arm
family of windows/foreign_items.rs. Handles and TLS are canonical source data. -/
namespace Miri.Interpreter.WindowsThread
open Miri.ABI Miri.Memory Miri.Concurrency
abbrev M := EStateM StepError
structure Hooks (S F : Type) where
  handles : WindowsHandles.Hooks S F
  readPointer : OpTy Provenance → M S (Pointer (Option Provenance))
  readImmediate : OpTy Provenance → M S (RvalueImmTy Provenance)
  readUsize : OpTy Provenance → M S UInt64
  readU32 : OpTy Provenance → M S UInt32
  u32Layout : M S LocalLayout
  dereference : OpTy Provenance → LocalLayout → M S (MPlaceTy Provenance)
  pointerLayout : M S LocalLayout
  windowsU32 : String → M S UInt32
  start : Option (MPlaceTy Provenance) → Pointer (Option Provenance) → RvalueImmTy Provenance → LocalLayout → M S ThreadId
  /-- Non-exclusive join_thread, not pthread join_thread_exclusive. -/
  join : ThreadId → Scalar Provenance → MPlaceTy Provenance → M S Unit
  getTls : M S (ThreadTlsData Provenance)
  putTls : ThreadTlsData Provenance → M S Unit
  tlsError : ThreadTlsError → StepError
  resolveDestructor : Pointer (Option Provenance) → M S TlsDestructor
  readWide : Pointer (Option Provenance) → M S (Array UInt16)
  putThreads : ThreadManager → M S Unit
  /-- bytes_to_os_str followed by alloc_os_str_as_wide_str, WinLocal kind. -/
  allocateName : ByteArray → M S (Pointer (Option Provenance))
  writePointer : Pointer (Option Provenance) → MPlaceTy Provenance → M S Unit
/-- String::from_utf16_lossy: unmatched surrogates each emit U+FFFD. -/
def utf16Lossy (units : Array UInt16) : ByteArray := Id.run do
  let mut pending : Option Nat := none
  let mut chars : Array Char := #[]
  for unit in units do
    let value := unit.toNat
    if let some high := pending then
      pending := none
      if value >= 0xdc00 && value <= 0xdfff then
        chars := chars.push (Char.ofNat (0x10000 + (high - 0xd800)*1024 + value - 0xdc00))
        continue
      chars := chars.push (Char.ofNat 0xfffd)
    if value >= 0xd800 && value <= 0xdbff then pending := some value
    else if value >= 0xdc00 && value <= 0xdfff then chars := chars.push (Char.ofNat 0xfffd)
    else chars := chars.push (Char.ofNat value)
  if pending.isSome then chars := chars.push (Char.ofNat 0xfffd)
  return (String.ofList chars.toList).toUTF8

private def lift (value : Except StepError A) : M S A :=
  match value with | .ok value => pure value | .error error => throw error
private def thread (h : Hooks S F) (handle : WindowsHandles.Handle) (name : String) : M S ThreadId := do
  match handle with
  | .thread id => return id
  | .pseudo .currentThread => return (← h.handles.threads).activeThread
  | _ => WindowsHandles.invalid name

def create (h : Hooks S F) (security stacksize start argument flags output : OpTy Provenance) : M S ThreadId := do
  let security ← h.readPointer security
  let _ ← h.readUsize stacksize
  let routine ← h.readPointer start
  let argument ← h.readImmediate argument
  let flags ← h.readU32 flags
  let output ← if ← h.handles.isNull (← h.readPointer output) then pure none
    else pure (some (← h.dereference output (← h.u32Layout)))
  let reservation ← h.windowsU32 "STACK_SIZE_PARAM_IS_A_RESERVATION"
  if flags != 0 && flags != reservation then throw (.unsupported "unsupported CreateThread dwCreationFlags")
  if !(← h.handles.isNull security) then throw (.unsupported "CreateThread non-null lpThreadAttributes")
  h.start output routine argument (← h.u32Layout)

def wait (h : Hooks S F) (handle timeout : OpTy Provenance) (dest : MPlaceTy Provenance) : M S Unit := do
  let handle ← WindowsHandles.read h.handles handle "WaitForSingleObject"
  let timeout ← h.readU32 timeout
  let joined ← thread h handle "WaitForSingleObject"
  if timeout != (← h.windowsU32 "INFINITE") then throw (.unsupported "WaitForSingleObject non-infinite timeout")
  h.join joined (← h.handles.windows "WAIT_OBJECT_0") dest

def tlsAlloc (h : Hooks S F) (destructor : Option (OpTy Provenance)) (size : Size) : M S (Scalar Provenance) := do
  let destructor ← match destructor with
    | none => pure none
    | some op => do
      let pointer ← h.readPointer op
      if ← h.handles.isNull pointer then pure none else pure (some (← h.resolveDestructor pointer))
  match (← h.getTls).createKey destructor size with
  | .error error data => h.putTls data; throw (h.tlsError error)
  | .ok key data =>
    h.putTls data
    lift (Scalar.fromUInt key size |>.mapError ScalarOps.scalarError)

def tlsGet (h : Hooks S F) (key : OpTy Provenance) : M S (Pointer (Option Provenance)) := do
  let key ← h.readU32 key
  let active := (← h.handles.threads).activeThread
  match (← h.getTls).load (BitVec.ofNat 128 key.toNat) active with
  | .ok value => return value
  | .error error => throw (h.tlsError error)

def tlsSet (h : Hooks S F) (key value : OpTy Provenance) : M S Unit := do
  let key ← h.readU32 key
  let active := (← h.handles.threads).activeThread
  let value ← h.readPointer value
  match (← h.getTls).store (BitVec.ofNat 128 key.toNat) active value with
  | .ok data => h.putTls data
  | .error error => throw (h.tlsError error)

def tlsFree (h : Hooks S F) (fiber : Bool) (key : OpTy Provenance) : M S Unit := do
  let key ← h.readU32 key
  match (← h.getTls).deleteKey (BitVec.ofNat 128 key.toNat) with
  | .error error data => h.putTls data; throw (h.tlsError error)
  | .ok entry data =>
    h.putTls data
    if fiber && !entry.data.isEmpty && entry.destructor.isSome then
      throw (.unsupported "FlsFree on nonempty key with destructor")

def setDescription (h : Hooks S F) (handle name : OpTy Provenance) : M S Unit := do
  let handle ← WindowsHandles.read h.handles handle "SetThreadDescription"
  let name ← h.readWide (← h.readPointer name)
  let id ← thread h handle "SetThreadDescription"
  match (← h.handles.threads).setThreadName id (utf16Lossy name).data.toList with
  | .ok manager => h.putThreads manager
  | .error error => throw (.invalidProgram s!"thread description target missing: {reprStr error}")

def getDescription (h : Hooks S F) (handle output : OpTy Provenance) : M S Unit := do
  let handle ← WindowsHandles.read h.handles handle "GetThreadDescription"
  let output ← h.dereference output (← h.pointerLayout)
  let id ← thread h handle "GetThreadDescription"
  let some record := (← h.handles.threads).thread? id | throw (.invalidProgram "description thread missing")
  let name := record.threadName.getD []
  h.writePointer (← h.allocateName ⟨name.toArray⟩) output

def getId (h : Hooks S F) (handle : Option (OpTy Provenance)) : M S ThreadId := do
  match handle with
  | none => return (← h.handles.threads).activeThread
  | some handle =>
    let handle ← WindowsHandles.read h.handles handle "GetThreadId"
    thread h handle "GetThreadDescription"
end Miri.Interpreter.WindowsThread
