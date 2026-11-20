import Miri.Interpreter.MacOsSync
import Miri.Interpreter.UnixEnvironment
import Miri.Interpreter.PthreadSync
import Miri.Interpreter.ShimSignatures
import Miri.Interpreter.RandomMemory

/-! Remaining macOS foreign_items.rs wrappers. Existing stat/directory/time/
thread-name/environment wrappers remain in their canonical common modules. -/
namespace Miri.Interpreter.MacOsForeign
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
structure Hooks (S R Duration Os E Kind : Type) where
  signatures : ShimSignatures.PrimitiveHooks Provenance S
  writePointer : Pointer (Option Provenance) → MPlaceTy Provenance → M S Unit
  signature : String → M S (FnAbi Miri.MIR.TyId)
  sync : MacOsSync.Hooks S R
  pthread : PthreadSync.Hooks S R Duration
  environment : UnixEnvironment.Hooks S Os E Kind
  random : RandomMemory.Hooks S
  closeFd : Int32 → M S Int32
  argc : M S (Option (Pointer Provenance))
  argv : M S (Option (Pointer Provenance))
  currentExe : M S (Option Os)
  derefU32 : OpTy Provenance → M S (MPlaceTy Provenance)
  readPlaceU32 : MPlaceTy Provenance → M S UInt32
  writeInt : Int → MPlaceTy Provenance → M S Unit
  getPtrFnInstance : Pointer (Option Provenance) → M S CallInstance
  addThreadAtexit : CallInstance → Scalar Provenance → M S Unit
  stackAddress : UInt64
  stackSize : UInt64
private def arg (args : Array A) (i : Nat) : M S A :=
  match args[i]? with | some value => pure value | none => throw (.invalidProgram "checked macOS operand missing")
private def count : String → Option (Nat × Bool)
  | "__error" | "_NSGetArgc" | "_NSGetArgv" => some (0,false)
  | "close$NOCANCEL" | "pthread_get_stackaddr_np" | "pthread_get_stacksize_np" => some (1,false)
  | "_NSGetExecutablePath" | "_tlv_atexit" | "CCRandomGenerateBytes" => some (2,false)
  | "confstr" | "pthread_cond_timedwait_relative_np" => some (3,false)
  | "os_sync_wait_on_address" => some (4,false)
  | "os_sync_wait_on_address_with_deadline" | "os_sync_wait_on_address_with_timeout" => some (6,false)
  | "os_sync_wake_by_address_any" | "os_sync_wake_by_address_all" => some (3,false)
  | "os_unfair_lock_lock" | "os_unfair_lock_trylock" | "os_unfair_lock_unlock"
    | "os_unfair_lock_assert_owner" | "os_unfair_lock_assert_not_owner" => some (1,false)
  | "dispatch_semaphore_create" | "dispatch_semaphore_signal" | "dispatch_release" => some (1,true)
  | "dispatch_semaphore_wait" | "dispatch_time" => some (2,true)
  | _ => none

def dynamicSymbol (name : String) : Bool := #["os_sync_wait_on_address","os_sync_wait_on_address_with_deadline",
  "os_sync_wait_on_address_with_timeout","os_sync_wake_by_address_any","os_sync_wake_by_address_all"].contains name

def emulate (h : Hooks S R Duration Os E Kind) (name : String) (abi : FnAbi Miri.MIR.TyId)
    (args : Array (OpTy Provenance)) (dest : MPlaceTy Provenance) : M S (Option ForeignItems.EmulateItemResult) := do
  if h.signatures.os != "macos" then return none
  let some (count,modern) := count name | return none
  let args ← if modern then ShimSignatures.fixedPrimitive h.signatures name (h.signature name) count abi args else do
    h.signatures.checkSymbolClash name
    if abi.conv != .C then throw (.undefinedBehavior "macOS legacy calling convention mismatch")
    if abi.cVariadic then throw (.undefinedBehavior "macOS legacy variadic signature")
    if args.size != count then throw (.undefinedBehavior "macOS legacy argument count mismatch")
    pure args
  let pointer := h.writePointer
  let write := fun (value : Int32) => h.writeInt value.toInt dest
  match name with
  | "__error" => pointer (← IoError.lastErrorPlace h.environment.errors).mplace.ptr dest
  | "close$NOCANCEL" => write (← h.closeFd (← h.environment.readI32 (← arg args 0)))
  | "CCRandomGenerateBytes" =>
    let bytes ← h.environment.readPointer (← arg args 0)
    let count ← h.environment.readUsize (← arg args 1)
    let success ← h.environment.libcI32 "kCCSuccess"
    RandomMemory.generate h.random bytes count
    write success
  | "_NSGetArgc" | "_NSGetArgv" =>
    let value ← if name == "_NSGetArgc" then h.argc else h.argv
    let some value := value | throw (.invalidProgram "macOS argument pointers require initialized machine")
    pointer value.withOptionalProvenance dest
  | "_NSGetExecutablePath" =>
    h.environment.checkNoIsolation "`_NSGetExecutablePath`"
    let buf ← h.environment.readPointer (← arg args 0)
    let size ← h.derefU32 (← arg args 1)
    let some path ← h.currentExe | throw (.unsupported "_NSGetExecutablePath requires file-backed execution")
    let (written,needed) ← OsStrings.writePath h.environment.strings path buf (← h.readPlaceU32 size).toUInt64
    if written then h.writeInt 0 dest
    else
      if needed >= 2^32 then throw (.invalidProgram "executable path required size exceeds u32")
      h.writeInt (Int.ofNat needed.toNat) size
      h.writeInt (-1) dest
  | "_tlv_atexit" =>
    let dtor ← h.getPtrFnInstance (← h.environment.readPointer (← arg args 0))
    let data ← h.environment.readScalar (← arg args 1)
    h.addThreadAtexit dtor data
  | "pthread_get_stackaddr_np" | "pthread_get_stacksize_np" =>
    let _ ← h.environment.readUsize (← arg args 0)
    h.writeInt (Int.ofNat (if name == "pthread_get_stackaddr_np" then h.stackAddress else h.stackSize).toNat) dest
  | "confstr" =>
    IoError.setLastError h.environment.errors (.libc "EINVAL")
    h.writeInt 0 dest
  | "pthread_cond_timedwait_relative_np" => PthreadSync.condTimedwait h.pthread (← arg args 0) (← arg args 1) (← arg args 2) dest true
  | "os_sync_wait_on_address" | "os_sync_wait_on_address_with_deadline" | "os_sync_wait_on_address_with_timeout" =>
    let timeout ← if name == "os_sync_wait_on_address" then pure MacOsSync.Timeout.none
      else if name == "os_sync_wait_on_address_with_deadline" then pure (.absolute (← arg args 4) (← arg args 5))
      else pure (.relative (← arg args 4) (← arg args 5))
    MacOsSync.waitAddress h.sync (← arg args 0) (← arg args 1) (← arg args 2) (← arg args 3) timeout dest
  | "os_sync_wake_by_address_any" | "os_sync_wake_by_address_all" => MacOsSync.wakeAddress h.sync (← arg args 0) (← arg args 1) (← arg args 2) (name == "os_sync_wake_by_address_all") dest
  | "os_unfair_lock_lock" => MacOsSync.lock h.sync (← arg args 0)
  | "os_unfair_lock_trylock" => MacOsSync.tryLock h.sync (← arg args 0) dest
  | "os_unfair_lock_unlock" => MacOsSync.unlock h.sync (← arg args 0)
  | "os_unfair_lock_assert_owner" => MacOsSync.assertOwner h.sync (← arg args 0) true
  | "os_unfair_lock_assert_not_owner" => MacOsSync.assertOwner h.sync (← arg args 0) false
  | "dispatch_semaphore_create" => MacOsSync.semaphoreCreate h.sync (← arg args 0) dest
  | "dispatch_semaphore_wait" => MacOsSync.semaphoreWait h.sync (← arg args 0) (← arg args 1) dest
  | "dispatch_semaphore_signal" => MacOsSync.semaphoreSignal h.sync (← arg args 0) dest
  | "dispatch_release" => MacOsSync.release h.sync (← arg args 0)
  | "dispatch_time" => MacOsSync.dispatchTime h.sync (← arg args 0) (← arg args 1) dest
  | _ => throw (.invalidProgram "macOS operation inventory mismatch")
  return some .NeedsReturn
end Miri.Interpreter.MacOsForeign
