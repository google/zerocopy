import Miri.Input.EvalCallbackMachine
import Miri.Input.EvalExecutable
import Miri.Input.HostRuntime
import Miri.Input.EvalForeignExit
import Miri.Interpreter.ExecutionChoiceBindings

/-! Source-owned local scheduler/run-loop construction from the live World.
The local scheduling policy, readiness service, deadlines, clock, active-stack
callbacks and MIR step are assembled here; callers do not supply complete
RunLoopHooks or LocalSchedulerHooks records. Only process interrupt observation
and abnormal host cleanup remain explicit host operations. -/
namespace Miri.Input.EvalRunConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Concurrency

abbrev W := EvalCallbackMachine.World
abbrev User Os R P H D O Aff B Poll Instant System Native Profiler :=
  EvalCallbackMachine.ThreadUser Os R P H D O Aff B Poll Instant System Native Profiler
abbrev State Os R P H D O Aff B Poll Instant System Native Profiler :=
  EvalCallbackMachine.State Os R P H D O Aff B Poll Instant System Native Profiler
abbrev M Os R P H D O Aff B Poll Instant System Native Profiler A :=
  EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler) A

/-! `CTRL_C_RECEIVED` is process-global in Rust, and abnormal profiler cleanup
is an environment operation. Keep only these narrow residuals explicit. -/
structure ProcessEffects (S : Type) where
  interrupted : S → Bool
  handleAbnormalTermination : S → S

private def liftExcept (value : Except StepError A) : M Os R P H D O Aff B Poll Instant System Native Profiler A :=
  match value with | .ok result => pure result | .error error => throw error

private def getWorld (state : State Os R P H D O Aff B Poll Instant System Native Profiler) :
    W Os R P H D O Aff B Poll Instant System Native Profiler :=
  state.machine.user.user.payload.payload

private def putWorld (state : State Os R P H D O Aff B Poll Instant System Native Profiler)
    (world : W Os R P H D O Aff B Poll Instant System Native Profiler) :
    State Os R P H D O Aff B Poll Instant System Native Profiler := Id.run do
  let storage := state.machine.user
  let pointerUser := storage.user
  let control := pointerUser.payload
  let pointerUser := { pointerUser with payload := { control with payload := world } }
  let storage := { storage with user := pointerUser }
  return { state with machine := { state.machine with user := storage } }

private def routedIo (callbacks : EvalCallbackMachine.Hooks Os R P H D O Aff B Poll Instant System Native Profiler C X F A Z T E Iter Raw Listener TcpStream Host AddrIter)
    (choice : C) : M Os R P H D O Aff B Poll Instant System Native Profiler
      (BlockingIo.Hooks (EvalCallbackMachine.Inner Os R P H D O Aff B Poll Instant System Native Profiler)
        (EvalCallbackMachine.FD H D O) Poll Host) :=
  ExecutionStateTransport.action do
    let sourceIo := callbacks.socket.tcp.source.io
    let readiness ← EvalCallbackMachine.innerReadiness callbacks choice sourceIo.readiness
    pure {sourceIo with readiness}

private def pollFor (callbacks : EvalCallbackMachine.Hooks Os R P H D O Aff B Poll Instant System Native Profiler C X F A Z T E Iter Raw Listener TcpStream Host AddrIter)
    (choice : C) (timeout : Option Clock.Duration) : M Os R P H D O Aff B Poll Instant System Native Profiler Unit := do
  let callbacks := EvalCallbackMachine.prepare callbacks choice
  let io ← routedIo callbacks choice
  ExecutionStateTransport.action (BlockingIo.pollAndUnblock callbacks.wakeBudget io timeout)

private def sleepFor (clock : Clock.HostHooks Instant System
    (State Os R P H D O Aff B Poll Instant System Native Profiler))
    (timeout : Nat) : M Os R P H D O Aff B Poll Instant System Native Profiler Unit := do
  let duration ← liftExcept (Clock.Duration.fromNanos timeout)
  let state ← get
  let world := getWorld state
  let next ← Clock.Monotonic.sleep clock world.host.clock duration
  let world := { world with host := { world.host with clock := next } }
  set (putWorld state world)

private def pollDuration (value : Option Nat) : Except StepError (Option Clock.Duration) := do
  match value with
  | none => pure none
  | some nanos => some <$> Clock.Duration.fromNanos nanos

/-! Build the exact local scheduler branch. `communicate` is read from the
same HostRuntime configuration used at startup. The routed IO hook, deadline
registry, ThreadManager and ThreadStacks are all the live World instances. -/
def scheduler
    (configuration : HostRuntime.Configuration)
    (callbacks : EvalCallbackMachine.Hooks Os R P H D O Aff B Poll Instant System Native Profiler C X F A Z T E Iter Raw Listener TcpStream Host AddrIter)
    (choiceAccess : ExecutionChoices.Access
      (ThreadStacks.State MiriMemoryKind
        (User Os R P H D O Aff B Poll Instant System Native Profiler)))
    (clock : Clock.HostHooks Instant System
      (State Os R P H D O Aff B Poll Instant System Native Profiler))
    (systemDurationSince : System → System → M Os R P H D O Aff B Poll Instant System Native Profiler
      (Option Clock.Duration)) :
    C → ThreadStacks.LocalSchedulerHooks MiriMemoryKind
      (User Os R P H D O Aff B Poll Instant System Native Profiler) := fun choice => Id.run do
  let communicate : M Os R P H D O Aff B Poll Instant System Native Profiler Bool :=
    pure configuration.communicate
  let callbacks := EvalCallbackMachine.prepare callbacks choice
  let deadline := EvalCallbackMachine.deadlines callbacks choice clock communicate systemDurationSince
  return {
    processDelayedReadiness := do
      let io ← routedIo callbacks choice
      ExecutionStateTransport.action (Readiness.processDelayed callbacks.wakeBudget io.readiness)
    communicate
    pollHostIoNonBlocking := do
      let io ← routedIo callbacks choice
      ExecutionStateTransport.action
        (BlockingIo.pollAndUnblock callbacks.wakeBudget io (some ⟨0,0,by decide⟩))
    unblockExpiredDeadlines := DeadlineMachine.unblockExpiredDeadlines deadline
    choose := ExecutionChoiceBindings.schedulerChoice choiceAccess
    anyThreadBlockedOnHost := do
      let io ← routedIo callbacks choice
      ExecutionStateTransport.action (BlockingIo.anyThreadBlockedOnHost io) }

/-! Construct a complete source loop. Main/TLS stack-empty callbacks,
thread termination and MIR stepping use their established source machines;
ThreadStacks.bindRunLoop adds source stack-switch synchronization. A finite
choice tape is still a caller-side execution bound and must remain pending when
exhausted; this hook record itself makes no completion claim. -/
def hooks
    (configuration : HostRuntime.Configuration)
    (callbacks : EvalCallbackMachine.Hooks Os R P H D O Aff B Poll Instant System Native Profiler C X F A Z T E Iter Raw Listener TcpStream Host AddrIter)
    (main : MainMachine.Hooks (User Os R P H D O Aff B Poll Instant System Native Profiler)
      C O ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId) Aff P)
    (configs : C → EvalExecutable.Core Os R P H D O Aff B
      (HostRuntime.Storage Poll Instant System H D O Native Profiler) C Instant)
    (limits : ExecutionMachine.Limits)
    (choiceAccess : ExecutionChoices.Access
      (ThreadStacks.State MiriMemoryKind
        (User Os R P H D O Aff B Poll Instant System Native Profiler)))
    (clock : Clock.HostHooks Instant System
      (State Os R P H D O Aff B Poll Instant System Native Profiler))
    (systemDurationSince : System → System → M Os R P H D O Aff B Poll Instant System Native Profiler
      (Option Clock.Duration))
    (process : ProcessEffects (State Os R P H D O Aff B Poll Instant System Native Profiler)) :
    RunLoopHooks (State Os R P H D O Aff B Poll Instant System Native Profiler)
      C MainMachine.Callback := Id.run do
  let scheduling := scheduler configuration callbacks choiceAccess clock systemDurationSince
  let loopBase : RunLoopHooks (State Os R P H D O Aff B Poll Instant System Native Profiler)
      C MainMachine.Callback := {
    coreStep := fun choice => ExecutionStateTransport.step (configs choice) limits choice
    takeStackEmptyCallback := fun state => MachineHooks.run (MainMachine.take main) state
    invokeStackEmptyCallback := fun choice callback state => MachineHooks.run
      (match callback with
       | .main _ => MainMachine.invoke main choice
       | .tls callback => ThreadLoops.invoke main.termination.tls choice callback) state
    restoreStackEmptyCallback := fun callback state => MachineHooks.run
      (MainMachine.restore main callback) state
    terminateActiveThread := fun choice forExit state => MachineHooks.run
      (ThreadTerminationMachine.terminate main.termination choice forExit) state
    interrupted := process.interrupted
    handleAbnormalTermination := process.handleAbnormalTermination
    schedule := fun choice state => MachineHooks.run
      (ThreadStacks.scheduleLocal (scheduling choice)) state
    communicate := fun _ => configuration.communicate
    pollAndUnblock := fun choice timeout state =>
      match pollDuration timeout with
      | .error error => (state,.error error)
      | .ok timeout => MachineHooks.run (pollFor callbacks choice timeout) state
    sleep := fun _ timeout state => MachineHooks.run (sleepFor clock timeout) state }
  return ThreadStacks.bindRunLoop loopBase scheduling

/-! Source Core construction is fallible because compiler and host facts are
queried while building each choice-specific configuration. Preserve those
failures at the step boundary; do not turn them into an arbitrary default
`ExecutionMachine.Config`. -/
def hooksFromSourceParts
    (configuration : HostRuntime.Configuration)
    (callbacks : EvalCallbackMachine.Hooks Os R P H D O Aff B Poll Instant System Native Profiler C X F A Z T E Iter Raw Listener TcpStream Host AddrIter)
    (main : MainMachine.Hooks (User Os R P H D O Aff B Poll Instant System Native Profiler)
      C O ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId) Aff P)
    (configs : C → Except StepError (EvalExecutable.Core Os R P H D O Aff B
      (HostRuntime.Storage Poll Instant System H D O Native Profiler) C Instant))
    (limits : ExecutionMachine.Limits)
    (choiceAccess : ExecutionChoices.Access
      (ThreadStacks.State MiriMemoryKind
        (User Os R P H D O Aff B Poll Instant System Native Profiler)))
    (clock : Clock.HostHooks Instant System
      (State Os R P H D O Aff B Poll Instant System Native Profiler))
    (systemDurationSince : System → System → M Os R P H D O Aff B Poll Instant System Native Profiler
      (Option Clock.Duration))
    (process : ProcessEffects (State Os R P H D O Aff B Poll Instant System Native Profiler)) :
    (RunLoopHooks (State Os R P H D O Aff B Poll Instant System Native Profiler)
      C MainMachine.Callback ×
      (C → ThreadStacks.LocalSchedulerHooks MiriMemoryKind
        (User Os R P H D O Aff B Poll Instant System Native Profiler))) := Id.run do
  let scheduling := scheduler configuration callbacks choiceAccess clock systemDurationSince
  let loopBase : RunLoopHooks (State Os R P H D O Aff B Poll Instant System Native Profiler)
      C MainMachine.Callback := {
    coreStep := fun choice state =>
      match configs choice with
      | .ok config => ExecutionStateTransport.step config limits choice state
      | .error error => (state,.error error)
    takeStackEmptyCallback := fun state => MachineHooks.run (MainMachine.take main) state
    invokeStackEmptyCallback := fun choice callback state => MachineHooks.run
      (match callback with
       | .main _ => MainMachine.invoke main choice
       | .tls callback => ThreadLoops.invoke main.termination.tls choice callback) state
    restoreStackEmptyCallback := fun callback state => MachineHooks.run
      (MainMachine.restore main callback) state
    terminateActiveThread := fun choice forExit state => MachineHooks.run
      (ThreadTerminationMachine.terminate main.termination choice forExit) state
    interrupted := process.interrupted
    handleAbnormalTermination := process.handleAbnormalTermination
    schedule := fun choice state => MachineHooks.run
      (ThreadStacks.scheduleLocal (scheduling choice)) state
    communicate := fun _ => configuration.communicate
    pollAndUnblock := fun choice timeout state =>
      match pollDuration timeout with
      | .error error => (state,.error error)
      | .ok timeout => MachineHooks.run (pollFor callbacks choice timeout) state
    sleep := fun _ timeout state => MachineHooks.run (sleepFor clock timeout) state }
  return ⟨loopBase, scheduling⟩

def hooksFromSource
    (configuration : HostRuntime.Configuration)
    (callbacks : EvalCallbackMachine.Hooks Os R P H D O Aff B Poll Instant System Native Profiler C X F A Z T E Iter Raw Listener TcpStream Host AddrIter)
    (main : MainMachine.Hooks (User Os R P H D O Aff B Poll Instant System Native Profiler)
      C O ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId) Aff P)
    (configs : C → Except StepError (EvalExecutable.Core Os R P H D O Aff B
      (HostRuntime.Storage Poll Instant System H D O Native Profiler) C Instant))
    (limits : ExecutionMachine.Limits)
    (choiceAccess : ExecutionChoices.Access
      (ThreadStacks.State MiriMemoryKind
        (User Os R P H D O Aff B Poll Instant System Native Profiler)))
    (clock : Clock.HostHooks Instant System
      (State Os R P H D O Aff B Poll Instant System Native Profiler))
    (systemDurationSince : System → System → M Os R P H D O Aff B Poll Instant System Native Profiler
      (Option Clock.Duration))
    (process : ProcessEffects (State Os R P H D O Aff B Poll Instant System Native Profiler)) :
    RunLoopHooks (State Os R P H D O Aff B Poll Instant System Native Profiler)
      C WindowsExitMachine.Callback :=
  let (base, scheduling) := hooksFromSourceParts configuration callbacks main configs
    limits choiceAccess clock systemDurationSince process
  EvalForeignExit.loop main base scheduling

/-! Source startup can run `main` before constructing the optional
callback protocol. This scheduler preserves the source's cheap branches: an
enabled active thread returns before host polling, empty delayed/readiness and
blocking registries take their actual empty branches, and no-deadline states
do not read a clock. If execution reaches a branch that needs an unconnected
physical poll, delayed readiness update, timed deadline, or host-source query,
it returns Unsupported. It never treats a missing callback dictionary as an
empty successful result. -/
private def schedulerWithoutCallbacks
    (configuration : HostRuntime.Configuration)
    (choiceAccess : ExecutionChoices.Access
      (ThreadStacks.State MiriMemoryKind
        (User Os R P H D O Aff B Poll Instant System Native Profiler))) :
    C → ThreadStacks.LocalSchedulerHooks MiriMemoryKind
      (User Os R P H D O Aff B Poll Instant System Native Profiler) := fun _ => {
  processDelayedReadiness := do
    let state ← get
    let world := getWorld state
    if !world.host.readiness.delayed.isEmpty then
      throw (.unsupported "source delayed-readiness processing has no attached poll capability")
  communicate := pure configuration.communicate
  pollHostIoNonBlocking := throw (.unsupported
    "source scheduler host polling has no attached physical poll capability")
  unblockExpiredDeadlines := do
    let manager := (← get).machine.threads
    if manager.threads.any (fun thread => match thread.state with
        | .Blocked _ (some _) _ => true
        | _ => false) then
      throw (.unsupported "source scheduler timed-deadline processing has no attached clock dispatcher")
    pure none
  choose := ExecutionChoiceBindings.schedulerChoice choiceAccess
  anyThreadBlockedOnHost := do
    let world := getWorld (← get)
    if !world.host.blocking.sources.isEmpty then
      throw (.unsupported "source scheduler host-blocked query has no attached readiness capability")
    pure false }

def hooksFromSourceWithoutCallbacks
    (configuration : HostRuntime.Configuration)
    (main : MainMachine.Hooks (User Os R P H D O Aff B Poll Instant System Native Profiler)
      C O ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId) Aff P)
    (configs : C → Except StepError (EvalExecutable.Core Os R P H D O Aff B
      (HostRuntime.Storage Poll Instant System H D O Native Profiler) C Instant))
    (limits : ExecutionMachine.Limits)
    (choiceAccess : ExecutionChoices.Access
      (ThreadStacks.State MiriMemoryKind
        (User Os R P H D O Aff B Poll Instant System Native Profiler)))
    (clock : Clock.HostHooks Instant System
      (State Os R P H D O Aff B Poll Instant System Native Profiler))
    (systemDurationSince : System → System → M Os R P H D O Aff B Poll Instant System Native Profiler
      (Option Clock.Duration))
    (process : ProcessEffects (State Os R P H D O Aff B Poll Instant System Native Profiler)) :
    RunLoopHooks (State Os R P H D O Aff B Poll Instant System Native Profiler)
      C MainMachine.Callback := Id.run do
  let scheduling := schedulerWithoutCallbacks configuration choiceAccess
  let loopBase : RunLoopHooks (State Os R P H D O Aff B Poll Instant System Native Profiler)
      C MainMachine.Callback := {
    coreStep := fun choice state =>
      match configs choice with
      | .ok config => ExecutionStateTransport.step config limits choice state
      | .error error => (state,.error error)
    takeStackEmptyCallback := fun state => MachineHooks.run (MainMachine.take main) state
    invokeStackEmptyCallback := fun choice callback state => MachineHooks.run
      (match callback with
       | .main _ => MainMachine.invoke main choice
       | .tls callback => ThreadLoops.invoke main.termination.tls choice callback) state
    restoreStackEmptyCallback := fun callback state => MachineHooks.run
      (MainMachine.restore main callback) state
    terminateActiveThread := fun choice forExit state => MachineHooks.run
      (ThreadTerminationMachine.terminate main.termination choice forExit) state
    interrupted := process.interrupted
    handleAbnormalTermination := process.handleAbnormalTermination
    schedule := fun choice state => MachineHooks.run
      (ThreadStacks.scheduleLocal (scheduling choice)) state
    communicate := fun _ => configuration.communicate
    pollAndUnblock := fun _ _ state =>
      (state,.error (.unsupported
        "source run-loop host polling has no attached physical poll capability"))
    sleep := fun _ _ state =>
      (state,.error (.unsupported
        "source run-loop timed sleep has no attached host clock capability")) }
  return ThreadStacks.bindRunLoop loopBase scheduling

inductive PendingCause where
  | outerChoicesExhausted (iterations : Nat)
  | iterationFuelExhausted (iterations : Nat)
  | choiceTapeExhausted (iterations : Nat)
  | sourceResourceExhausted (iterations : Nat) (error : StepError)
  deriving Repr, DecidableEq

/-! A bounded process driver returns a status only for a source terminal
outcome. Exhausting either external bound is explicitly pending/unknown. -/
inductive RunResult (S : Type) where
  | exited (state : S) (code : Int) (leakCheck : Bool)
  | undefinedBehavior (state : S) (error : StepError)
  | unsupported (state : S) (error : StepError)
  | failed (state : S) (error : StepError)
  | pending (state : S) (cause : PendingCause)
  deriving Repr

def classifyError (state : S) (error : StepError) : RunResult S :=
  if error == .callback "choice input unknown: tape exhausted" then
    .pending state (.choiceTapeExhausted 0)
  else match error with
  | .termination (.exit code leakCheck) => .exited state code leakCheck
  | .unsupported _ => .unsupported state error
  | .resourceExhaustion _ => .pending state (.sourceResourceExhausted 0 error)
  | .termination info =>
    if info.report == .unsupportedOperation then .unsupported state error
    else if RunLoop.reportsUB error then .undefinedBehavior state error
    else .failed state error
  | _ =>
    if RunLoop.reportsUB error then .undefinedBehavior state error
    else .failed state error

/-- Bounded-size diagnostic view: no body, locals or heap serialization.
`running` includes the std start wrapper; it does not certify guest main entry. -/
private def progressLabel
    (state : State Os R P H D O Aff B Poll Instant System Native Profiler) : String := Id.run do
  let main := match (getWorld state).main with
    | none => "absent"
    | some data => match data.stage with
      | .globalConstructors .. => "constructors"
      | .running => "running"
      | .exiting stage _ => s!"exiting_{repr stage}"
  let tls := match (getWorld state).main with
    | none => "absent"
    | some data => match data.tls with
      | .init => "init" | .initForExit => "initForExit"
      | .pthread _ => "pthread" | .afterPthread => "afterPthread"
      | .threadAtexit => "threadAtexit" | .windows .. => "windows" | .done => "done"
  let frame := match state.stack.frames.back? with
    | none => "empty"
    | some frame => s!"def_{frame.functionInstance.kind.defId}.body_{frame.bodyIdentity.index}.loc_{repr frame.location}"
  return s!"thread_{state.machine.user.registry.activeThread.value.val}.depth_{state.stack.frames.size}.main_{main}.tls_{tls}.{frame}"

/-- Profiling is an identity on the state, including failed prefixes. Log the
first 64 iterations, then every 64th; the count is outer scheduler iterations,
not MIR instructions. Labels are evaluated only with profiling enabled. -/
def observeProgress (profile : Lean.Options) (boundary : String) (iteration : Nat)
    (state : State Os R P H D O Aff B Poll Instant System Native Profiler) :=
  if profile.getBool `profiler false && (iteration < 64 || iteration % 64 == 0) then
    Lean.profileit s!"execution.{boundary}.iteration_{iteration}.{(progressLabel state).replace " " "_"}"
      profile (fun _ => state)
  else state

theorem observeProgress_eq (profile : Lean.Options) (boundary : String) (iteration : Nat)
    (state : State Os R P H D O Aff B Poll Instant System Native Profiler) :
    observeProgress profile boundary iteration state = state := by
  unfold observeProgress
  split <;> rfl

/-- Time complete scheduler iterations, retaining their starting frame identity.
Only profiling emits spans; the local threshold defaults to 10ms to avoid
printing every fast iteration. A span includes scheduling and callbacks, not
just the MIR instruction at its starting location. -/
def iterationProfiled (profile : Lean.Options)
    (loop : RunLoopHooks (State Os R P H D O Aff B Poll Instant System Native Profiler)
      C Callback) (choice : C) (iteration : Nat)
    (state : State Os R P H D O Aff B Poll Instant System Native Profiler) :=
  if profile.getBool `profiler false then
    Lean.profileit s!"execution.iteration_{iteration}.{(progressLabel state).replace " " "_"}"
      (profile.set `profiler.threshold (profile.get `leanMiri.iterationThresholdMs (10 : Nat)))
      (fun _ => RunLoop.iteration loop choice state)
  else RunLoop.iteration loop choice state

theorem iterationProfiled_eq (profile : Lean.Options)
    (loop : RunLoopHooks (State Os R P H D O Aff B Poll Instant System Native Profiler)
      C Callback) (choice : C) (iteration : Nat)
    (state : State Os R P H D O Aff B Poll Instant System Native Profiler) :
    iterationProfiled profile loop choice iteration state = RunLoop.iteration loop choice state := by
  unfold iterationProfiled
  split <;> rfl

/-! This reuses RunLoop.iteration directly. No stop predicate can turn a
prefix boundary into process success, and no callback is permitted to claim
completion. A source `TerminationInfo::Exit` is the only successful process
result represented here. -/
def runUntilTerminalProfiled
    (profile : Lean.Options)
    {Callback : Type}
    (loop : RunLoopHooks (State Os R P H D O Aff B Poll Instant System Native Profiler)
      C Callback)
    (iterationFuel : Nat) (outerChoices : List C)
    (initial : State Os R P H D O Aff B Poll Instant System Native Profiler) :
    RunResult (State Os R P H D O Aff B Poll Instant System Native Profiler) := Id.run do
  let mut state := initial
  let mut fuel := iterationFuel
  let mut iterations := 0
  for choice in outerChoices do
    if fuel == 0 then return .pending state (.iterationFuelExhausted iterations)
    state := observeProgress profile "before" iterations state
    let (after,result) := iterationProfiled profile loop choice iterations state
    let after := observeProgress profile "after" iterations after
    state := after
    fuel := fuel - 1
    iterations := iterations + 1
    match result with
    | .error error =>
      if error == .callback "choice input unknown: tape exhausted" then
        return .pending state (.choiceTapeExhausted iterations)
      if let .resourceExhaustion _ := error then
        return .pending state (.sourceResourceExhausted iterations error)
      return classifyError state error
    | .ok () => pure ()
  return .pending state (.outerChoicesExhausted iterations)

/-- Original API, with observation disabled. -/
def runUntilTerminal
    {Callback : Type}
    (loop : RunLoopHooks (State Os R P H D O Aff B Poll Instant System Native Profiler)
      C Callback)
    (iterationFuel : Nat) (outerChoices : List C)
    (initial : State Os R P H D O Aff B Poll Instant System Native Profiler) :=
  runUntilTerminalProfiled {} loop iterationFuel outerChoices initial

/-- Every choice, state mutation and terminal/error/pending result is preserved
for arbitrary profiling options, hooks, bounds and initial states. -/
theorem runUntilTerminalProfiled_eq_runUntilTerminal
    (profile : Lean.Options)
    (loop : RunLoopHooks (State Os R P H D O Aff B Poll Instant System Native Profiler)
      C Callback)
    (fuel : Nat) (choices : List C)
    (initial : State Os R P H D O Aff B Poll Instant System Native Profiler) :
    runUntilTerminalProfiled profile loop fuel choices initial =
      runUntilTerminal loop fuel choices initial := by
  simp only [runUntilTerminal, runUntilTerminalProfiled, observeProgress_eq, iterationProfiled_eq]

end Miri.Input.EvalRunConstruction
