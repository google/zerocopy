import Miri.Interpreter.LinuxSyscall

/-! Target gate for the canonical Linux syscall algorithm. Core supplies the
    same algorithm's source branch capabilities, with missing futex/accept4
    effects reported only after their pinned syscall prefixes are checked. -/
namespace Miri.Interpreter.LinuxSyscallPartialDispatch
open Miri.ABI Miri.Memory Miri.MIR
abbrev M := EStateM StepError

structure Hooks (S D MD Ptr B I F : Type) where
  os : String
  syscall : LinuxSyscall.SyscallHooks S D MD Ptr B I F
  prctl : LinuxSyscall.PrctlHooks S D MD Ptr B I

def emulate (h : Hooks S D MD Ptr B I F) (name : String) (abi : FnAbi TyId)
    (args : Array (OpTy Provenance)) (dest : MPlaceTy Provenance) :
    M S (Option ForeignItems.EmulateItemResult) := do
  unless h.os == "linux" || h.os == "android" do return none
  if name == "syscall" then
    LinuxSyscall.syscallCore h.syscall name abi args dest
  else if name == "prctl" then
    LinuxSyscall.prctlCore h.prctl name abi args dest
  else return none
  return some .NeedsReturn

end Miri.Interpreter.LinuxSyscallPartialDispatch
