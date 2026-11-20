import Miri.Input.EvalExecutable
import Miri.Input.EvalHostMachine
import Miri.Input.EvalRunConstruction
import Miri.Input.EvalSyncPayload
import Miri.Input.EvalSocketStorage
import Miri.Input.EvalWindowsCallbackSourceConstruction
import Miri.Interpreter.ExecutionChoiceBindings
import Miri.Interpreter.ExecutionStateTransport
import Miri.Interpreter.WindowsExitMachine

/-! Windows execution loop over the canonical Main and ExitCalled
callback product. It reuses the interpreter's step and termination
machines, while Windows callback ownership stays in Main/TLS, ExitCalled,
typed synchronization state. Host readiness is inspected on demand and reports
Unsupported only when an actual host-blocked operation requires absent polling. -/
namespace Miri.Input.EvalWindowsRunConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Concurrency

abbrev Payload := EvalSyncPayload.Payload
abbrev Other Raw Listener TcpStream Error :=
  EvalSocketStorage.Other Raw Listener TcpStream Error
abbrev Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler :=
  HostRuntime.Storage Poll Instant System H D (Other Raw Listener TcpStream Error) Native Profiler
abbrev State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalWindowsFileConstruction.State Os R Payload H D (Other Raw Listener TcpStream Error) Aff B
    (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler)
abbrev User Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalWindowsCallbackSourceConstruction.User Os R Payload H D (Other Raw Listener TcpStream Error)
    Aff B Poll Instant System Native Profiler
abbrev World Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalCallbackMachine.World Os R Payload H D (Other Raw Listener TcpStream Error) Aff B
    Poll Instant System Native Profiler

private def getWorld
    (state : State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) :=
  state.machine.user.user.payload.payload

def needsHostIo (blocking : BlockingIo.Manager Poll)
    (readiness : ReadinessMachine.Registry F) (ownership : FileOwnership.Registry D) : Bool := Id.run do
  for (_,source) in blocking.sources do
    if !source.blocked.isEmpty then return true
    if FileOwnership.isClosed ownership source.fd then continue
    if let some (_,watched) := readiness.watched.find? (fun (id,_) => id == source.fd.id) then
      for watcherId in watched.watchers do
        if readiness.watchers.any (fun watcher =>
            watcher.id == watcherId && watcher.strong > 0 && !watcher.value.queue.isEmpty) then
          return true
  return false

private def worldNeedsHostIo
    (world : World Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) : Bool :=
  needsHostIo world.host.blocking world.host.readiness world.runtime.ownership

private def sleepFor
    (clock : Clock.HostHooks Instant System
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (timeout : Nat) : EStateM StepError
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Unit := do
  let duration ← match Clock.Duration.fromNanos timeout with
    | .ok duration => pure duration
    | .error error => throw error
  let state ← get
  let world := getWorld state
  let next ← Clock.Monotonic.sleep clock world.host.clock duration
  let world := {world with host := {world.host with clock := next}}
  set {state with machine := {state.machine with user := {state.machine.user with user :=
    {state.machine.user.user with payload := {state.machine.user.user.payload with payload := world}}}}}

/-- Build the local source scheduler from real deadline state, host clock and
the one Windows callback router. Windows has no host poll binding here, so
delayed readiness and blocked host sources stay explicit demand-local gaps. -/
def scheduler
    (configuration : HostRuntime.Configuration)
    (callbacks : EvalWindowsCallbackSourceConstruction.Product
      Os R Payload H D (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler
      C X F A)
    (choiceAccess : ExecutionChoices.Access
      (ThreadStacks.State MiriMemoryKind
        (User Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)))
    (clock : Clock.HostHooks Instant System
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (systemDurationSince : System → System → EStateM StepError
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (Option Clock.Duration)) :
    C → ThreadStacks.LocalSchedulerHooks MiriMemoryKind
      (User Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) :=
  fun choice => Id.run do
    let communicate := pure configuration.communicate
    let deadline := EvalHostMachine.deadlines clock communicate systemDurationSince
      (callbacks.invoke choice)
    return {
      processDelayedReadiness := do
        let world := getWorld (← get)
        if !world.host.readiness.delayed.isEmpty then
          throw (.unsupported "Windows source scheduler delayed readiness requires a host polling capability")
      communicate
      pollHostIoNonBlocking := do
        let world := getWorld (← get)
        if worldNeedsHostIo world then
          throw (.unsupported "Windows source scheduler host polling is required by blocked readiness state")
      unblockExpiredDeadlines := do
        DeadlineMachine.unblockExpiredDeadlines deadline
      choose := ExecutionChoiceBindings.schedulerChoice choiceAccess
      anyThreadBlockedOnHost := do
        let world := getWorld (← get)
        pure (worldNeedsHostIo world) }

/-- Construct the Windows Main/TLS/ExitCalled loop with the same execution
step, termination, interrupt, process and choice-tape semantics as the
loop. Callback execution is exclusively through WindowsExitMachine. -/
def hooks
    (configuration : HostRuntime.Configuration)
    (callbacks : EvalWindowsCallbackSourceConstruction.Product
      Os R Payload H D (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler
      C ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId))
    (configs : C → Except StepError (EvalExecutable.Core Os R Payload H D
      (Other Raw Listener TcpStream Error) Aff B
      (Host Poll Instant System H D Raw Listener TcpStream Error Native Profiler) C Instant))
    (limits : ExecutionMachine.Limits)
    (choiceAccess : ExecutionChoices.Access
      (ThreadStacks.State MiriMemoryKind
        (User Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)))
    (clock : Clock.HostHooks Instant System
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (systemDurationSince : System → System → EStateM StepError
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (Option Clock.Duration))
    (process : EvalRunConstruction.ProcessEffects
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)) :
    RunLoopHooks
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C WindowsExitMachine.Callback := Id.run do
  let scheduling := scheduler configuration callbacks choiceAccess clock systemDurationSince
  let base : RunLoopHooks
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C WindowsExitMachine.Callback := {
    coreStep := fun choice state =>
      match configs choice with
      | .ok config => ExecutionStateTransport.step config limits choice state
      | .error error => (state,.error error)
    takeStackEmptyCallback := fun state => MachineHooks.run (WindowsExitMachine.take callbacks.exit) state
    invokeStackEmptyCallback := fun choice callback state => MachineHooks.run
      (match callback with
       | .exitHandler handler => WindowsExitMachine.invoke callbacks.exit choice handler
       | .mainOrTls (.main _) => MainMachine.invoke callbacks.main choice
       | .mainOrTls (.tls tlsCallback) => ThreadLoops.invoke
           callbacks.main.termination.tls choice tlsCallback) state
    restoreStackEmptyCallback := fun callback state => MachineHooks.run
      (WindowsExitMachine.restore callbacks.exit callback) state
    terminateActiveThread := fun choice forExit state => MachineHooks.run
      (ThreadTerminationMachine.terminate callbacks.main.termination choice forExit) state
    interrupted := process.interrupted
    handleAbnormalTermination := process.handleAbnormalTermination
    schedule := fun choice state => MachineHooks.run
      (ThreadStacks.scheduleLocal (scheduling choice)) state
    communicate := fun _ => configuration.communicate
    pollAndUnblock := fun _ timeout state =>
      if worldNeedsHostIo (getWorld state) then
        (state,.error (.unsupported "Windows source loop requires a physical host IO poll"))
      else match timeout with
        | some timeout => MachineHooks.run (sleepFor clock timeout) state
        | none => (state,.error (.invalidProgram "Windows scheduler requested an unbounded host poll without a host source"))
    sleep := fun _ timeout state => MachineHooks.run (sleepFor clock timeout) state }
  return WindowsExitMachine.bindLoop callbacks.exit base scheduling

/-- Finite-prefix execution preserves the runner's pending and error
classification. Only a source termination error returns `exited`. -/
def runUntilTerminal
    (loop : RunLoopHooks
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C WindowsExitMachine.Callback)
    (iterationFuel : Nat) (outerChoices : List C)
    (initial : State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) :
    EvalRunConstruction.RunResult
      (State Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) := Id.run do
  let mut state := initial
  let mut fuel := iterationFuel
  let mut iterations := 0
  for choice in outerChoices do
    if fuel == 0 then return .pending state (.iterationFuelExhausted iterations)
    let (after,result) := RunLoop.iteration loop choice state
    state := after
    fuel := fuel - 1
    iterations := iterations + 1
    match result with
    | .error error =>
      if error == .callback "choice input unknown: tape exhausted" then
        return .pending state (.choiceTapeExhausted iterations)
      if let .resourceExhaustion _ := error then
        return .pending state (.sourceResourceExhausted iterations error)
      return EvalRunConstruction.classifyError state error
    | .ok () => pure ()
  return .pending state (.outerChoicesExhausted iterations)

end Miri.Input.EvalWindowsRunConstruction
