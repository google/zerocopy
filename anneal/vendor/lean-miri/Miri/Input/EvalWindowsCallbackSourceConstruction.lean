import Miri.Input.EvalCallbackMachine
import Miri.Input.EvalForeignExit
import Miri.Input.EvalTypedSyncMachine
import Miri.Input.EvalWindowsFileConstruction
import Miri.Interpreter.MainMachine
import Miri.Interpreter.ThreadMachine
import Miri.Interpreter.ExecutionStateTransport

/-! Windows callback routing over the canonical Main state. Windows exit
callbacks reuse Main/TLS, while FnOnce wake callbacks are selected from the
single ThreadMachine token supply and dispatched to typed synchronization. Unix
descriptor, futex-registry and socket callback records do not participate. -/
namespace Miri.Input.EvalWindowsCallbackSourceConstruction
open Miri.ABI Miri.Memory Miri.Interpreter Miri.Concurrency

abbrev Payload Os R P H D O Aff B Host :=
  EvalWindowsFileConstruction.Payload Os R P H D O Aff B Host
abbrev State Os R P H D O Aff B Host :=
  EvalWindowsFileConstruction.State Os R P H D O Aff B Host
abbrev User Os R P H D O Aff B Poll Instant System Native Profiler :=
  EvalCallbackMachine.ThreadUser Os R P H D O Aff B Poll Instant System Native Profiler

set_option autoImplicit false in
structure Product (Os R P H D O Aff B Poll Instant System Native Profiler
    C X F A : Type) where
  main : MainMachine.Hooks
    (Payload Os R P H D O Aff B (HostRuntime.Storage Poll Instant System H D O Native Profiler))
    C O X F A Aff ProgramExitPoll
  exit : WindowsExitMachine.Hooks
    (User Os R P H D O Aff B Poll Instant System Native Profiler)
    C O X F A Aff ProgramExitPoll
  invoke : C → Nat → UnblockKind → EStateM StepError
    (State Os R P H D O Aff B (HostRuntime.Storage Poll Instant System H D O Native Profiler)) Unit
  discard : Nat → EStateM StepError
    (State Os R P H D O Aff B (HostRuntime.Storage Poll Instant System H D O Native Profiler)) Unit

private def tokenOwners
    {Os R P H D O Aff B Poll Instant System Native Profiler : Type}
    (state : State Os R P H D O Aff B (HostRuntime.Storage Poll Instant System H D O Native Profiler))
    (token : Nat) : Nat × Nat := Id.run do
  let world := state.machine.user.user.payload.payload
  let joins := world.runtime.threads.joins.filter (·.token == token)
  let sync := world.host.sync.callbacks.filter (·.1 == token)
  return (joins.size,sync.size)

private def route
    {Os R P H D O Aff B Poll Instant System Native Profiler C X F A : Type}
    (main : MainMachine.Hooks
      (Payload Os R P H D O Aff B (HostRuntime.Storage Poll Instant System H D O Native Profiler))
      C O X F A Aff ProgramExitPoll)
    (effects : TypedSyncMachine.Effects
      (EvalTypedSyncMachine.State Os R P H D O Aff B Poll Instant System Native Profiler))
    (choice : C) (token : Nat) (kind : UnblockKind) :
    EStateM StepError
      (State Os R P H D O Aff B (HostRuntime.Storage Poll Instant System H D O Native Profiler)) Unit := do
  let state ← get
  let (joins,sync) := tokenOwners state token
  unless joins + sync == 1 do
    throw (.callback "missing or ambiguous Windows source FnOnce callback")
  if joins == 1 then
    ThreadMachine.resumeJoin main.termination.tls.thread choice token kind
  else if sync == 1 then
    ExecutionStateTransport.action (TypedSyncRuntime.invoke
      (TypedSyncMachine.typed EvalTypedSyncMachine.views effects) token kind)

private def discard
    {Os R P H D O Aff B Poll Instant System Native Profiler C X F A : Type}
    (main : MainMachine.Hooks
      (Payload Os R P H D O Aff B (HostRuntime.Storage Poll Instant System H D O Native Profiler))
      C O X F A Aff ProgramExitPoll)
    (token : Nat) : EStateM StepError
    (State Os R P H D O Aff B (HostRuntime.Storage Poll Instant System H D O Native Profiler)) Unit := do
  let state ← get
  let (joins,sync) := tokenOwners state token
  unless joins + sync == 1 do
    throw (.callback "missing or ambiguous discarded Windows source callback")
  if joins == 1 then
    let _ ← ThreadMachine.takeJoin main.termination.tls.thread token
    pure ()
  else if sync == 1 then
    let _ ← ExecutionStateTransport.action (TypedSyncMachine.take EvalTypedSyncMachine.views token)
    pure ()

/-- Construct Main/TLS and ExitCalled callbacks and the FnOnce dispatcher from
the actual Main hooks and typed synchronization effects. Callback storage and
token ownership remain in their canonical World fields. -/
def fromSource [DecidableEq Os]
    {R P H D O Aff B Poll Instant System Native Profiler C : Type}
    (main : MainMachine.Hooks
      (Payload Os R P H D O Aff B (HostRuntime.Storage Poll Instant System H D O Native Profiler))
      C O ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId) Aff ProgramExitPoll)
    (effects : TypedSyncMachine.Effects
      (EvalTypedSyncMachine.State Os R P H D O Aff B Poll Instant System Native Profiler))
     :
    Except StepError (Product Os R P H D O Aff B Poll Instant System Native Profiler
      C ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId)) := do
  let exit := EvalForeignExit.hooks main
  pure {
    main
    exit
    invoke := route main effects
    discard := discard main }

end Miri.Input.EvalWindowsCallbackSourceConstruction
