import Miri.Interpreter.LinuxSyscall

/-! Linux and Android foreign_items.rs syscall/prctl entry arms. The signature
checker in LinuxSyscall owns symbol-clash and ABI checks in source order. -/
namespace Miri.Interpreter.LinuxSyscallDispatch
open Miri.ABI Miri.Memory Miri.MIR
abbrev M := EStateM StepError

def emulate (h : LinuxSyscall.Hooks S R F D B I) (name : String) (abi : FnAbi TyId)
    (args : Array (OpTy Provenance)) (dest : MPlaceTy Provenance) :
    M S (Option ForeignItems.EmulateItemResult) := do
  unless h.signatures.foreign.os == "linux" || h.signatures.foreign.os == "android" do return none
  if name == "syscall" then
    LinuxSyscall.syscall h name abi args dest
    return some .NeedsReturn
  if name == "prctl" then
    LinuxSyscall.prctl h name abi args dest
    return some .NeedsReturn
  return none

def bind (h : LinuxSyscall.Hooks S R F D B I) :
    ForeignItems.Hooks Provenance S D (MPlaceTy Provenance) (Pointer (Option Provenance)) B I :=
  {h.signatures.foreign with unix := fun name abi args dest => do
    if let some result ← emulate h name abi args dest then return result
    h.signatures.foreign.unix name abi args dest}
end Miri.Interpreter.LinuxSyscallDispatch
