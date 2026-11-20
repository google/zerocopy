import Miri.Interpreter.LeakCheck

/-! eval.rs::eval_entry final reporting/leak policy. Host diagnostics remain
explicit effects; reachability and thread-leak decisions are actual machine
operations, not caller-provided booleans. -/
namespace Miri.Interpreter.EntryResult
open Miri.Memory
abbrev Leaks := Array (AllocId × LocalAllocation Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
structure Hooks (U : Type) where
  reportResult : StepError → MachineHooks.M MiriMemoryKind U (Option (Int32 × Bool))
  staticRoots : U → Array AllocId
  reportThreadLeak : MachineHooks.M MiriMemoryKind U Unit
  reportLeaks : Leaks → MachineHooks.M MiriMemoryKind U Unit
  ignoreLeaksNote : MachineHooks.M MiriMemoryKind U Unit
  failureCode : Int32

def finishProfiled (profile : Lean.Options)
    (h : Hooks U) (ignoreLeaks : Bool) (outcome : StepError) :
    MachineHooks.M MiriMemoryKind U Int32 := do
  let some (code,leakCheck) ← h.reportResult outcome | return h.failureCode
  if leakCheck then
    if !ignoreLeaks then
      if !(← get).machine.threads.threads.all (·.isTerminated) then
        h.reportThreadLeak
        h.ignoreLeaksNote
        return h.failureCode
      let state ← get
      let state := Lean.profileit "finalization.leak_check.start" profile (fun _ => state)
      let (memory,leaks) ← match Lean.profileit "finalization.leak_check.complete" profile (fun _ =>
          LeakCheck.takeProfiled profile state.machine.memory (h.staticRoots state.machine.user)) with
        | .ok result => pure result | .error error => throw error
      set {state with machine := {state.machine with memory := memory}}
      if !leaks.isEmpty then
        h.reportLeaks leaks
        h.ignoreLeaksNote
        return h.failureCode
  return code

def finish (h : Hooks U) (ignoreLeaks : Bool) (outcome : StepError) :
    MachineHooks.M MiriMemoryKind U Int32 :=
  finishProfiled {} h ignoreLeaks outcome

theorem finishProfiled_eq_finish (profile : Lean.Options)
    (h : Hooks U) (ignoreLeaks : Bool) (outcome : StepError) :
    finishProfiled profile h ignoreLeaks outcome = finish h ignoreLeaks outcome := by
  rfl
end Miri.Interpreter.EntryResult
