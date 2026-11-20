import Miri.Interpreter.RaceMode
import Miri.Concurrency.SyncRuntime
import Miri.Interpreter.ExecutionStateTransport

/-! Canonical source synchronization runtime on the final pointer/validation/
thread composition. Optional clocks and actual thread stacks share the same
machine fields; no synthetic GlobalState is created for disabled tracking. -/
namespace Miri.Interpreter.SyncMachine
open Miri.Memory Miri.Concurrency
abbrev User := ExecutionStateTransport.Inner
abbrev State K U := MachineHooks.State K (User U)

def sourceError : SyncError → StepError
  | error => .invalidProgram s!"synchronization invariant: {reprStr error}"

/-- Select the immutable source backend kind from the canonical machine at the
actual binding point. Compiler/configuration leaves and typed object/callback
stores remain the supplied source records; clock/thread access is replaced. -/
def bind (selection : State K U → Except StepError (RaceMode.Handler B))
    (base : SyncRuntime.Hooks (State K U) R V D) :
    MachineHooks.M K (User U) (SyncRuntime.Hooks (State K U) R V D) := do
  let selected ← match selection (← get) with
    | .ok selected => pure selected | .error error => throw error
  let handler := match selected with | .none => SyncClockHandler.none | .vclocks _ => .vectorClocks
  pure {base with
    handler := handler
    global := do return (← get).machine.dataRace
    putGlobal := fun global => modify fun s => {s with machine := {s.machine with dataRace := global}}
    threads := do return (← get).machine.threads
    putThreads := fun manager => ExecutionStateTransport.reverseAction (ThreadStacks.installManager manager)
    error := sourceError}
end Miri.Interpreter.SyncMachine
