import Miri.Interpreter.MacOsForeign
import Miri.Interpreter.MainMachine
import Miri.Interpreter.DeadlineMachine

namespace Miri.Interpreter.MacOsForeignMachine
open Miri.ABI Miri.Memory

def bindTime (time : TimeShims.Hooks (MachineHooks.State K U) Host System TZ Timestamp)
    (deadline : DeadlineMachine.Hooks K U Host System)
    (base : MacOsSync.Hooks (MachineHooks.State K U) R) : MacOsSync.Hooks (MachineHooks.State K U) R := {
  base with
  timeout := DeadlineMachine.timeout deadline .monotonic
  absoluteDeadline := fun nanos => do
    let duration ← match Clock.Duration.fromNanos nanos.toNat with
      | .ok value => pure value | .error error => throw error
    DeadlineMachine.timeout deadline .monotonic .absolute duration
  timeAfter := fun nanos => do
    let duration ← match Clock.Duration.fromNanos nanos.toNat with
      | .ok value => pure value | .error error => throw error
    let clock ← time.monotonic
    let now ← clock.now time.host
    let after ← now.addLossy time.host duration
    return (← after.durationSince time.host clock.epoch).asNanos }

/-- _tlv_atexit uses full compiler instances and source spans in the same
ThreadTlsData visited by the actual destructor engine, not another TLS map. -/
def bindTls (main : MainMachine.Hooks U C Other X FnABI ArgABI Aff P)
    (base : MacOsForeign.Hooks (MainMachine.State U) R Duration Os E Kind) :
    MacOsForeign.Hooks (MainMachine.State U) R Duration Os E Kind := {
  base with
  argc := return (main.entry (← get).machine.user.user).argc
  argv := return (main.entry (← get).machine.user.user).argv
  getPtrFnInstance := fun pointer => do
    match ← FunctionPointers.getPtrFn main.functions pointer with
    | .Instance fnInstance => pure fnInstance
    | .Other _ => throw (.unsupported "_tlv_atexit destructor is not a compiler instance")
  addThreadAtexit := fun fnInstance data => do
    let active := (← get).machine.threads.activeThread
    let span ← AllocationDriver.currentUserRelevantSpan main.termination.tls.thread.spans
    let tls := main.termination.tls
    modify fun state =>
      let store := tls.data state.machine.user.user
      let values := store.values.addThreadAtexit active ⟨fnInstance,data,span⟩
      let payload := tls.putData state.machine.user.user {store with values}
      {state with machine := {state.machine with user := {state.machine.user with user := payload}}} }
end Miri.Interpreter.MacOsForeignMachine
