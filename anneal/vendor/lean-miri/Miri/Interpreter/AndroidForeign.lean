import Miri.Interpreter.LinuxForeign

/-! Remaining Android aliases, reusing source off64_t signatures and actual
FD/errno state. Existing lseek64/ftruncate64 and syscall/thread wrappers remain
canonical; no Linux-only GNU/memory/signal wrapper is accepted on Android. -/
namespace Miri.Interpreter.AndroidForeign
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError

def emulate (h : LinuxForeign.Hooks S Place H D O E HM Os B I) (name : String)
    (abi : FnAbi Miri.MIR.TyId) (args : Array (OpTy Provenance))
    (dest : MPlaceTy Provenance) : M S (Option ForeignItems.EmulateItemResult) := do
  if h.signatures.foreign.os != "android" then return none
  if name == "pread64" || name == "pwrite64" then
    LinuxForeign.positional h name abi args dest
    return some .NeedsReturn
  if name != "__errno" && name != "gettid" then return none
  h.signatures.foreign.checkSymbolClash name
  if abi.conv != .C then throw (.undefinedBehavior "Android errno calling convention mismatch")
  if abi.cVariadic then throw (.undefinedBehavior "Android errno variadic signature")
  if !args.isEmpty then throw (.undefinedBehavior "Android errno argument count mismatch")
  if name == "__errno" then h.signatures.foreign.writePointer (← IoError.lastErrorPlace h.errors).mplace.ptr dest
  else h.errors.writeScalar (← h.unixGettid name) dest
  return some .NeedsReturn
end Miri.Interpreter.AndroidForeign
