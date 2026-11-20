import Miri.Interpreter.FrameMetadata
import Miri.Interpreter.ForeignItems

/-! Pinned unix/windows foreign_items.rs std-only dispatch arms. These are
source stubs, enabled by the actual frame predicate, never general FFI defaults. -/
namespace Miri.Interpreter.StdOnlyShims
open Miri.ABI Miri.Memory Miri.MIR
open ForeignItems (EmulateItemResult)
abbrev M := EStateM StepError
structure Hooks (P S D MD B I : Type) where
  /-- Only the nonrecursive source core is needed by std-only arms. Keeping
  the full foreign dispatcher out of this record prevents a std-only
  constructor from accepting or capturing an arbitrary platform chain. -/
  foreign : ForeignItems.Core P S D MD (Pointer (Option P)) B I
  frameInStd : M S Bool
  targetEnv : String
  pageSize : UInt64
  stackAddress : UInt64
  stackSize : UInt64
  /-- Exact source compiler layout: usize, unit_ptr_mut or named libc type. -/
  layout : String → M S LocalLayout
  dereference : OpTy P → LocalLayout → M S MD
  pointerOf : MD → Pointer (Option P)
  writeUnsigned : UInt64 → MD → M S Unit
  writeUninit : MD → M S Unit
  projectNamed : MD → String → M S MD
  readU32 : OpTy P → M S UInt32
  checkNoIsolation : String → M S Unit
  homeDirectory : M S String
  writePath : String → Pointer (Option P) → UInt64 → M S Bool
  libcValue : String → M S (Scalar P)
  windowsValue : String → M S (Scalar P)
  writeScalar : Scalar P → MD → M S Unit
  allocateStringDedup : String → M S (Pointer (Option P))
  /-- Exact compiler shim_sig!(extern system ...) ABI for the named source arm. -/
  windowsAbi : String → M S (FnAbi TyId)
  yieldActiveThread : M S Unit
  setLastError : String → M S Unit

private def invalid (message : String) : M S A := throw (.invalidProgram message)
private def arg (args : Array A) (index : Nat) : M S A :=
  match args[index]? with | some value => pure value | none => invalid "std shim checked argument missing"
private def deprecated (h : Hooks P S D MD B I) (name : String) (abi : FnAbi TyId)
    (args : Array (OpTy P)) (count : Nat) : M S Unit := do
  h.foreign.checkSymbolClash name
  if abi.conv != .C then throw (.undefinedBehavior "std shim calling convention mismatch")
  if abi.cVariadic then throw (.undefinedBehavior "std shim called with variadic signature")
  if args.size != count then throw (.undefinedBehavior "std shim argument count mismatch")

private def unixNames : Array String := #["pthread_attr_getguardsize","pthread_attr_init",
  "pthread_attr_destroy","pthread_attr_setstacksize","pthread_attr_getstack","signal",
  "sigaltstack","sigaction","getpwuid_r","__posix_getpwuid_r"]

def unix (h : Hooks P S D MD B I) (name : String) (abi : FnAbi TyId)
    (args : Array (OpTy P)) (dest : MD) : M S EmulateItemResult := do
  let platform := (h.foreign.os == "linux" &&
      #["pthread_getattr_np","gnu_get_libc_version"].contains name) ||
    (h.foreign.os == "freebsd" && name == "pthread_attr_get_np")
  if !unixNames.contains name && !platform then return .NotSupported
  if !(← h.frameInStd) then return .NotSupported
  if name == "gnu_get_libc_version" && h.targetEnv != "gnu" then return .NotSupported
  let count := if name == "pthread_attr_getguardsize" then 2
    else if #["pthread_attr_init","pthread_attr_destroy"].contains name then 1
    else if #["pthread_attr_getstack","sigaction"].contains name then 3
    else if #["getpwuid_r","__posix_getpwuid_r"].contains name then 5
    else if name == "gnu_get_libc_version" then 0 else 2
  deprecated h name abi args count
  if name == "pthread_attr_getguardsize" then
    let place ← h.dereference (← arg args 1) (← h.layout "usize")
    h.writeUnsigned h.pageSize place
    h.foreign.writeNull dest
  else if name == "pthread_attr_getstack" then
    let _ ← h.dereference (← arg args 0) (← h.layout "pthread_attr_t")
    let address ← h.dereference (← arg args 1) (← h.layout "usize")
    let size ← h.dereference (← arg args 2) (← h.layout "usize")
    h.writeUnsigned h.stackAddress address
    h.writeUnsigned h.stackSize size
    h.foreign.writeNull dest
  else if #["getpwuid_r","__posix_getpwuid_r"].contains name then
    h.checkNoIsolation "`getpwuid_r`"
    let uid ← h.readU32 (← arg args 0)
    let pwd ← h.dereference (← arg args 1) (← h.layout "passwd")
    let buffer ← h.foreign.readPointer (← arg args 2)
    let length ← h.foreign.readUsize (← arg args 3)
    let result ← h.dereference (← arg args 4) (← h.layout "unit_ptr_mut")
    if uid != 1000 then throw (.unsupported "`getpwuid_r` on other users is not supported")
    h.writeUninit pwd
    let home ← h.homeDirectory
    let written ← h.writePath home buffer length
    let directory ← h.projectNamed pwd "pw_dir"
    h.foreign.writePointer buffer directory
    if written then
      h.foreign.writePointer (h.pointerOf pwd) result
      h.foreign.writeNull dest
    else
      h.foreign.writeNull result
      h.writeScalar (← h.libcValue "ERANGE") dest
  else if name == "gnu_get_libc_version" then
    h.foreign.writePointer (← h.allocateStringDedup "2.26\x00") dest
  else
    h.foreign.writeNull dest
  return .NeedsReturn

private def windowsNames : Array String := #["NtQueryVolumeInformationFile","GetProcessHeap",
  "GetModuleHandleA","SetConsoleTextAttribute","AddVectoredExceptionHandler",
  "SetThreadStackGuarantee","SwitchToThread","GetFinalPathNameByHandleW"]

set_option autoImplicit false in
/-- Windows uses no Unix path, layout or passwd operations. Keep its source
construction independent of those capabilities. -/
structure WindowsHooks (P S D MD B I : Type) where
  foreign : ForeignItems.Core P S D MD (Pointer (Option P)) B I
  frameInStd : M S Bool
  windowsAbi : String → M S (FnAbi TyId)
  windowsValue : String → M S (Scalar P)
  writeScalar : Scalar P → MD → M S Unit
  writeUnsigned : UInt64 → MD → M S Unit
  yieldActiveThread : M S Unit
  setLastError : String → M S Unit

def windowsCore (h : WindowsHooks P S D MD B I) (name : String) (abi : FnAbi TyId)
    (args : Array (OpTy P)) (dest : MD) : M S EmulateItemResult := do
  if !windowsNames.contains name then return .NotSupported
  if !(← h.frameInStd) then return .NotSupported
  let callee ← h.windowsAbi name
  if callee.cVariadic then invalid "std system shim compiler signature is variadic"
  ForeignItems.Core.checkAbi h.foreign abi callee
  h.foreign.checkSymbolClash name
  if args.size != callee.args.size then invalid "std system shim arguments disagree with ABI"
  let _ ← args.mapIdxM fun index operand => do
    let some expected := callee.args[index]? | invalid "std system shim ABI argument missing"
    h.foreign.transmute operand expected.layout
  if name == "NtQueryVolumeInformationFile" then
    h.writeScalar (← h.windowsValue "STATUS_NOT_IMPLEMENTED") dest
  else if #["GetProcessHeap","GetModuleHandleA","AddVectoredExceptionHandler",
      "SetThreadStackGuarantee"].contains name then
    h.writeUnsigned 1 dest
  else if name == "SwitchToThread" then
    h.yieldActiveThread
    h.foreign.writeNull dest
  else if name == "GetFinalPathNameByHandleW" then
    h.setLastError "ERROR_NOT_SUPPORTED"
    h.foreign.writeNull dest
  else h.foreign.writeNull dest
  return .NeedsReturn

def windows (h : Hooks P S D MD B I) (name : String) (abi : FnAbi TyId)
    (args : Array (OpTy P)) (dest : MD) : M S EmulateItemResult :=
  windowsCore ⟨h.foreign,h.frameInStd,h.windowsAbi,h.windowsValue,
    h.writeScalar,h.writeUnsigned,h.yieldActiveThread,h.setLastError⟩ name abi args dest

/-- Recognized but unavailable std arms fall through to the existing platform
handler, matching source guards rather than claiming a successful stub. -/
def bind (h : Hooks P S D MD B I)
    (base : ForeignItems.Hooks P S D MD (Pointer (Option P)) B I) :
    ForeignItems.Hooks P S D MD (Pointer (Option P)) B I := Id.run do
  let h := {h with foreign := base.toCore}
  return { base with
    unix := fun name abi args dest => do
      let result ← unix h name abi args dest
      if result == .NotSupported then base.unix name abi args dest else pure result
    windows := fun name abi args dest => do
      let result ← windows h name abi args dest
      if result == .NotSupported then base.windows name abi args dest else pure result }

def machine (compiler : FrameMetadata.CompilerHooks K User)
    (base : Hooks Provenance (MachineHooks.State K User) D MD B I) :
    Hooks Provenance (MachineHooks.State K User) D MD B I :=
  { base with frameInStd := FrameMetadata.frameInStd compiler }
end Miri.Interpreter.StdOnlyShims
