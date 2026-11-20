import Miri.Interpreter.ShimSignatures
import Miri.Interpreter.FunctionPointers
import Miri.Interpreter.MemoryShims
import Miri.Interpreter.ExternStatic

/-! unix/foreign_items.rs::is_dyn_sym, dlsym and _Unwind_RaiseException.
Dynamic symbols remain FnVal::Other; data symbols remain their actual pointers. -/
namespace Miri.Interpreter.UnixDynamic
open Miri.ABI Miri.Memory Miri.MIR
variable {Place : Type}
abbrev M := EStateM StepError
structure Symbol where
  name : String
  deriving DecidableEq, Repr

def isDynamic (os env name : String) : Bool :=
  if #["strlen","signal","getentropy","getrandom","futimens"].contains name then true
  else if (name == "preadv" || name == "pwritev") && os != "solaris" then true
  else if os == "android" then name == "gettid"
  else if os == "linux" then name == "gettid" || name == "statx" ||
    (env == "gnu" && name == "__cxa_thread_atexit_impl")
  else if os == "solaris" || os == "illumos" then name == "pthread_setname_np"
  else if os == "macos" then #["os_sync_wait_on_address","os_sync_wait_on_address_with_deadline",
    "os_sync_wait_on_address_with_timeout","os_sync_wake_by_address_any","os_sync_wake_by_address_all"].contains name
  else false

structure Hooks (S Place B I : Type) where
  signatures : ShimSignatures.PrimitiveHooks Provenance S
  signature : String → M S (FnAbi TyId)
  targetEnv : String
  readUsize : OpTy Provenance → M S UInt64
  readPointer : OpTy Provenance → M S (Pointer (Option Provenance))
  readCString : Pointer (Option Provenance) → M S ByteArray
  functionPointer : Symbol → M S (Pointer (Option Provenance))
  externStatic : String → M S (Option (Pointer (Option Provenance)))
  writePointer : Pointer (Option Provenance) → MPlaceTy Provenance → M S Unit
  writeNull : MPlaceTy Provenance → M S Unit
  startUnwind : OpTy Provenance → M S Unit
private def arg (args : Array A) (index : Nat) : M S A :=
  match args[index]? with
  | some value => pure value
  | none => throw (.invalidProgram "checked dynamic shim argument absent")

def emulate (h : Hooks S Place B I) (name : String) (abi : FnAbi TyId)
    (args : Array (OpTy Provenance)) (dest : MPlaceTy Provenance) :
    M S (Option ForeignItems.EmulateItemResult) := do
  if name == "dlsym" then
    let args ← ShimSignatures.fixedPrimitive h.signatures name (h.signature name) 2 abi args
    let _ ← h.readUsize (← arg args 0)
    let pointer ← h.readPointer (← arg args 1)
    let bytes ← h.readCString pointer
    let some symbol := String.fromUTF8? bytes | throw (.unsupported "dlsym non-UTF-8 symbol")
    if isDynamic h.signatures.os h.targetEnv symbol then
      h.writePointer (← h.functionPointer ⟨symbol⟩) dest
    else if let some pointer ← h.externStatic symbol then h.writePointer pointer dest
    else h.writeNull dest
    return some .NeedsReturn
  if name == "_Unwind_RaiseException" then
    unless #["linux","freebsd","illumos","solaris","android","macos"].contains h.signatures.os do
      throw (.unsupported "_Unwind_RaiseException unavailable on target OS")
    let args ← ShimSignatures.fixedPrimitive h.signatures name (h.signature name) 1 abi args
    h.startUnwind (← arg args 0)
    return some .NeedsUnwind
  return none

def bindStrings (strings : MemoryShims.Hooks Provenance S Place (MPlaceTy Provenance) B I)
    (scanBudget : Nat) (base : Hooks S Place B I) : Hooks S Place B I :=
  {base with readCString := MemoryShims.readCString strings scanBudget}

def bindFunctions (functions : FunctionPointers.Hooks K U Other) (inject : Symbol → Other)
    (base : Hooks (MachineHooks.State K U) Place B I) : Hooks (MachineHooks.State K U) Place B I :=
  {base with functionPointer := fun symbol => do
    let pointer ← FunctionPointers.functionPointer functions (.Other (inject symbol))
    return Pointer.new (some pointer.provenance) pointer.offset}

/-- Actual exported data symbols share the machine's ExternStatic map; the
source checks them only after the dynamic-function whitelist. -/
def bindStatics (statics : U → ExternStatic.State)
    (base : Hooks (MachineHooks.State K U) Place B I) : Hooks (MachineHooks.State K U) Place B I :=
  {base with externStatic := fun name => do
    let entries := (statics (← get).machine.user).symbols.filter (·.1 == name)
    if entries.size > 1 then throw (.invalidProgram "duplicate canonical extern static")
    return entries[0]?.map fun (_,pointer) => pointer.withOptionalProvenance}

def bindUnwind (unwind : Unwind.Hooks K U C Other) (choice : C)
    (base : Hooks (MachineHooks.State K U) Place B I) : Hooks (MachineHooks.State K U) Place B I :=
  {base with startUnwind := Unwind.handleStartUnwind unwind choice}
end Miri.Interpreter.UnixDynamic
