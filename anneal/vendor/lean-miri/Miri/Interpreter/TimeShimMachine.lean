import Miri.Interpreter.TimeShims
import Miri.Interpreter.DeadlineMachine
import Miri.Interpreter.WindowsSync
import Miri.Interpreter.PthreadSync

/-! Canonical Clock/DeadlineMachine bindings for time and synchronization shims.
Registry tokens retain actual typed clock values; they are never timestamps. -/
namespace Miri.Interpreter.TimeShimMachine

def bind (clock : DeadlineMachine.Hooks K U H Y)
    (base : TimeShims.Hooks (MachineHooks.State K U) H Y Z T) :
    TimeShims.Hooks (MachineHooks.State K U) H Y Z T := {
  base with
  host := clock.host
  monotonic := do return clock.clock (← get).machine.user
  encodeDeadline := DeadlineMachine.intern clock
  systemDurationSinceUnix := fun time => clock.systemDurationSince time clock.host.unixEpoch
  runtime := { base.runtime with
    threads := do return (← get).machine.threads
    putThreads := fun threads => modify fun state =>
      { state with machine := { state.machine with threads := threads } } } }

def bindWindows (clock : DeadlineMachine.Hooks K U H Y)
    (base : WindowsSync.Hooks (MachineHooks.State K U) R) :
    WindowsSync.Hooks (MachineHooks.State K U) R := {
  base with monotonicDeadlineMillis := DeadlineMachine.monotonicDeadlineMillis clock }

def bindPthread (clock : DeadlineMachine.Hooks K U H Y)
    (base : PthreadSync.Hooks (MachineHooks.State K U) R Clock.Duration) :
    PthreadSync.Hooks (MachineHooks.State K U) R Clock.Duration := {
  base with timeout := fun kind relative duration => do
    let kind : Clock.TimeoutClock := match kind with | .realTime => .realTime | .monotonic => .monotonic
    let style : Clock.TimeoutStyle := if relative then .relative else .absolute
    DeadlineMachine.timeout clock kind style duration }
/-- DeadlineMachine already selects/restores the callback thread. This executes
only the typed registered closure, avoiding a second restoration. -/
def invokeSyncCallback (runtime : Miri.Concurrency.SyncRuntime.Hooks
    (MachineHooks.State K U) R V D) (token : Nat)
    (kind : Miri.Concurrency.UnblockKind) : MachineHooks.M K U Unit := do
  Miri.Concurrency.SyncRuntime.runCallback runtime token kind
end Miri.Interpreter.TimeShimMachine
