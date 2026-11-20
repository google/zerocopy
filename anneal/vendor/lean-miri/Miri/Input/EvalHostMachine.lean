import Miri.Input.MachineConstruction
import Miri.Interpreter.TimeShimMachine

/-! Canonical host-state projections used by deadlines/time shims. The actual
host clock and callback dispatcher remain supplied effects; storage, thread
selection and all source deadline transitions use one actual World. -/
namespace Miri.Input.EvalHostMachine
open Miri.Memory Miri.Interpreter Miri.Concurrency
abbrev Host := HostRuntime.Storage
abbrev User Os R P H D O Aff B Poll Instant System Native Profiler :=
  EvalWorld.User Os R P H D O Aff B (Host Poll Instant System H D O Native Profiler)
abbrev State Os R P H D O Aff B Poll Instant System Native Profiler :=
  MachineHooks.State MiriMemoryKind (User Os R P H D O Aff B Poll Instant System Native Profiler)

def deadlines
    (clock : Clock.HostHooks Instant System (State Os R P H D O Aff B Poll Instant System Native Profiler))
    (communicate : MachineHooks.M MiriMemoryKind (User Os R P H D O Aff B Poll Instant System Native Profiler) Bool)
    (systemDurationSince : System → System → MachineHooks.M MiriMemoryKind
      (User Os R P H D O Aff B Poll Instant System Native Profiler) (Option Clock.Duration))
    (invokeCallback : Nat → UnblockKind → MachineHooks.M MiriMemoryKind
      (User Os R P H D O Aff B Poll Instant System Native Profiler) Unit) :
    DeadlineMachine.Hooks MiriMemoryKind
      (User Os R P H D O Aff B Poll Instant System Native Profiler) Instant System where
  registry := fun u => u.user.payload.payload.host.deadlines
  setRegistry := fun deadlines u => {u with user := {u.user with payload := {u.user.payload with payload :=
    {u.user.payload.payload with host := {u.user.payload.payload.host with deadlines}}}}}
  clock := fun u => u.user.payload.payload.host.clock
  host := clock
  communicate := communicate
  systemDurationSince := systemDurationSince
  selectThread := ThreadStacks.setActiveThread
  invokeCallback := invokeCallback
end Miri.Input.EvalHostMachine
