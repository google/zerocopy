import Miri.Input.EvalForeignSocketMachine
import Miri.Input.EvalHostMachine
import Miri.Input.CompilerProviders
import Miri.Input.EvalArchitectureMachine

/-! One concrete source FnOnce dispatcher. Scheduling and deadline wrappers
select the actual target thread before invoking this interpreter. Main/TLS are
FnMut stack-empty callbacks and use MainMachine.take/invoke/restore instead.
No missing-token fallback or function-valued registry is accepted here. -/
namespace Miri.Input.EvalCallbackMachine
open Miri.ABI Miri.Memory Miri.Interpreter Miri.Concurrency
abbrev World := EvalOwnedIoMachine.World
abbrev State := EvalForeignIoMachine.State
abbrev Inner := EvalOwnedIoMachine.State
abbrev ThreadUser Os R P H D O Aff B Poll Instant System Native Profiler :=
  ValidityMachine.UserState (World Os R P H D O Aff B Poll Instant System Native Profiler)
abbrev FD := EvalOwnedIoMachine.FD

private structure UnixTarget where
  facts : CompilerExternStatic.TargetFacts
  arch : String

private def compilerUnixTarget (prepared : CompilerProviders.Prepared) : Except StepError UnixTarget := do
  let facts ← prepared.externStatics.targetFacts.mapError fun reason =>
    StepError.unsupported s!"compiler target facts unavailable for Unix callbacks: {reason}"
  unless facts.families.contains "unix" do
    throw (.invalidProgram s!"Unix callback factory requires a compiler Unix target, got `{facts.os}`")
  let arch ← EvalArchitectureMachine.targetArch prepared.intrinsics |>.mapError fun reason =>
    StepError.unsupported s!"compiler target architecture unavailable for Unix callbacks: {reason}"
  pure ⟨facts,arch⟩

structure Hooks (Os R P H D O Aff B Poll Instant System Native Profiler C X F A Z T E Iter Raw Listener TcpStream Host AddrIter : Type) where
  thread : ThreadMachine.Hooks MiriMemoryKind
    (ThreadUser Os R P H D O Aff B Poll Instant System Native Profiler) C O X F A Aff
  futex : Option (LinuxFutexMachine.Hooks MiriMemoryKind
    (World Os R P H D O Aff B Poll Instant System Native Profiler) C P O B Instant System Z T E)
  io : EvalOwnedIoMachine.Bindings (Inner Os R P H D O Aff B Poll Instant System Native Profiler) (FD H D O) E Iter
  socket : EvalOwnedIoMachine.SocketBindings (Inner Os R P H D O Aff B Poll Instant System Native Profiler) (FD H D O) E Raw Listener TcpStream Poll Host AddrIter
  descriptor : SocketMachine.Descriptor O
  options : SocketOptions.Hooks (Inner Os R P H D O Aff B Poll Instant System Native Profiler) (FD H D O) E AddrIter
  wakeBudget : Nat
  nestedCapacity : Nat
  synchronousResource : Nat
  /-- Registry projections let callback execution suppress pruning until its
  complete nested callback chain has returned. -/
  deadlineRegistry : ThreadStacks.Storage
      (ThreadUser Os R P H D O Aff B Poll Instant System Native Profiler) →
    DeadlineMachine.Registry Instant System
  setDeadlineRegistry : DeadlineMachine.Registry Instant System →
    ThreadStacks.Storage (ThreadUser Os R P H D O Aff B Poll Instant System Native Profiler) →
    ThreadStacks.Storage (ThreadUser Os R P H D O Aff B Poll Instant System Native Profiler)

private def compilerErrorTarget (facts : CompilerExternStatic.TargetFacts) (h : IoError.Hooks S E) :=
  {h with family := ForeignItems.Family.unix, os := facts.os}

private def compilerAddressTarget (target : UnixTarget) (h : SocketAddress.Hooks S E I) :=
  {h with gnu := target.facts.env == "gnu", errors := compilerErrorTarget target.facts h.errors}

private def compilerEnvironmentTarget (target : UnixTarget) (h : UnixEnvironment.Hooks S Os E Kind) := Id.run do
  let facts := target.facts
  let errors := compilerErrorTarget facts h.errors
  let strings := {h.strings with targetWindows := facts.os == "windows"}
  let env := {h.env with family := ForeignItems.Family.unix}
  let process := {h.process with family := ForeignItems.Family.unix, os := facts.os}
  return {h with
    os := facts.os
    targetEnv := facts.env
    strings := strings
    env := env
    process := process
    errors := errors
    architecture := target.arch}

private def compilerPathTarget (target : UnixTarget) (h : UnixFsPaths.Hooks S F D Path HM Time E Kind) :=
  {h with
    metadata := {h.metadata with
      os := target.facts.os
      errors := compilerErrorTarget target.facts h.metadata.errors}
    strings := {h.strings with targetWindows := target.facts.os == "windows"}}

/-- Target-dependent socket policy comes from rustc's parsed target. The host
backend predicates stay in their host-effect dictionaries: `hostWindows` and
`hostEdgeBackend` are intentionally preserved. -/
private def compilerSocketTarget (target : UnixTarget)
    (h : Hooks Os R P H D O Aff B Poll Instant System Native Profiler C X F A Z T E Iter Raw Listener TcpStream Host AddrIter) := Id.run do
  let facts := target.facts
  let optionsAddress := compilerAddressTarget target h.options.address
  let options := {h.options with os := facts.os, address := optionsAddress}
  let virtualSource := {h.socket.virtual.source with
    os := facts.os
    errors := compilerErrorTarget facts h.socket.virtual.source.errors}
  let tcpSource := {h.socket.tcp.source with
    os := facts.os
    errors := compilerErrorTarget facts h.socket.tcp.source.errors}
  let socketAddress := compilerAddressTarget target h.socket.socket.address
  let socketSource := {h.socket.socket with os := facts.os, address := socketAddress}
  let socket := {h.socket with
    virtual := {h.socket.virtual with source := virtualSource}
    tcp := {h.socket.tcp with source := tcpSource}
    socket := socketSource}
  return {h with socket, options}

private def invokeBoundBody (h : Hooks Os R P H D O Aff B Poll Instant System Native Profiler C X F A Z T E Iter Raw Listener TcpStream Host AddrIter)
    (choice : C) (token : Nat) (kind : UnblockKind) :
    EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler) Unit := do
  let w := (← get).machine.user.user.payload.payload
  let joins := w.runtime.threads.joins.filter (·.token == token)
  let futex := w.host.futex.callbacks.filter (·.1 == token)
  let sync := w.host.sync.callbacks.filter (·.1 == token)
  let io := w.host.io.callbacks.filter (·.1 == token)
  if joins.size + futex.size + sync.size + io.size != 1 then
    throw (.callback "missing or ambiguous final source FnOnce callback")
  if !joins.isEmpty then
    ThreadMachine.resumeJoin h.thread choice token kind
  else if !futex.isEmpty then
    match h.futex with
    | some hooks => do
        ExecutionStateTransport.action
          (FutexRuntime.invoke (LinuxFutexMachine.runtime hooks choice) token kind)
    | none => throw (.unsupported "selected futex callback has no source-built capability")
  else if !sync.isEmpty then
    ExecutionStateTransport.action (TypedSyncRuntime.invoke
      (TypedSyncMachine.typed EvalTypedSyncMachine.views h.io.effects) token kind)
  else
    EvalForeignSocketMachine.invoke h.io h.socket h.synchronousResource
      (fun _ _ => throw (.callback "final source IO callback changed ownership during selection")) token kind

private def invokeBound (h : Hooks Os R P H D O Aff B Poll Instant System Native Profiler C X F A Z T E Iter Raw Listener TcpStream Host AddrIter)
    (choice : C) (token : Nat) (kind : UnblockKind) :=
  DeadlineMachine.withPruneSuppressed h.deadlineRegistry h.setDeadlineRegistry
    (invokeBoundBody h choice token kind)

/-- This constructor runs no baseline callback. Every portable wake closure is
captured only after its exact readiness/runtime dictionary points at `run`. -/
private def routeSource
    (h : Hooks Os R P H D O Aff B Poll Instant System Native Profiler C X F A Z T E Iter Raw Listener TcpStream Host AddrIter)
    (run : Nat → UnblockKind → EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler) Unit) :
    Hooks Os R P H D O Aff B Poll Instant System Native Profiler C X F A Z T E Iter Raw Listener TcpStream Host AddrIter := Id.run do
  let innerRun := fun token kind => ExecutionStateTransport.reverseAction (run token kind)
  let runtime := TypedSyncNat.routed EvalTypedSyncMachine.views h.io.effects innerRun
  let ready := {h.socket.tcp.source.io.readiness with
    runtime
    unblock := fun thread reason => ExecutionStateTransport.reverseAction
      (ThreadStacks.unblockThread thread reason run)}
  let event := {h.io.operations.event with
    runtime
    updateReadiness := fun fd => Readiness.updateFd h.wakeBudget ready fd {forceEdge := true}
    unblockThread := fun thread => ready.unblock thread .Eventfd}
  let poll := {h.io.poll with readiness := ready}
  let epoll := {h.io.epoll with poll := {h.io.epoll.poll with readiness := ready}}
  let operations := {h.io.operations with
    event
    dropWatcher := ready.dropWatcher
    pollReady := PollShims.writeReady h.wakeBudget poll
    epollReady := fun fd dest events => do
      let some watcher ← epoll.asEpoll fd | throw (.invalidProgram "final typed epoll callback has wrong descriptor")
      let count ← EpollShims.returnReady h.wakeBudget epoll watcher dest events
      if count < 0 then throw (.invalidProgram "epoll returned negative event count")
      pure count.toInt.toNat
    epollRemoveBlocked := fun fd thread => do
      let some watcher ← epoll.asEpoll fd | throw (.invalidProgram "final typed epoll callback has wrong descriptor")
      Readiness.removeBlockedThread ready watcher thread}
  let io := {h.io with
    operations
    event := OwnedIoMachine.bindEvent EvalOwnedIoMachine.views operations
    poll := OwnedIoMachine.bindPoll EvalOwnedIoMachine.views operations poll
    epoll := OwnedIoMachine.bindEpoll EvalOwnedIoMachine.views operations epoll}
  let virtual := OwnedSocketMachine.virtual EvalOwnedIoMachine.socketViews
    {h.socket.virtual.source with readiness := ready} h.socket.virtual.completion
  let tcp := OwnedSocketMachine.tcp EvalOwnedIoMachine.socketViews
    {h.socket.tcp.source with io := {h.socket.tcp.source.io with readiness := ready}} h.socket.tcp.completion
  let socket := {h.socket with
    virtual,tcp
    socket := {h.socket.socket with
      operations := OwnedSocketOperations.operations EvalOwnedIoMachine.socketViews h.descriptor virtual tcp
        (SocketMachine.bindOptions tcp.source h.options) h.synchronousResource
      newTcp := TcpSocket.newSocket tcp.source
      dropFd := ready.dropFd}}
  return {h with io,socket}

/-- Exhaustion is an Unknown prefix, after consuming the selected source Box and
running its capture drop. Captured scalar/place values have no destructor;
owned descriptor/watchers use their exact source cleanup. -/
private def exhaustedBody
    (h : Hooks Os R P H D O Aff B Poll Instant System Native Profiler C X F A Z T E Iter Raw Listener TcpStream Host AddrIter)
    (choice : C) (token : Nat) :
    EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler) Unit := do
  let w := (← get).machine.user.user.payload.payload
  let joins := w.runtime.threads.joins.filter (·.token == token)
  let futex := w.host.futex.callbacks.filter (·.1 == token)
  let sync := w.host.sync.callbacks.filter (·.1 == token)
  let io := w.host.io.callbacks.filter (·.1 == token)
  if joins.size + futex.size + sync.size + io.size != 1 then
    throw (.callback "missing or ambiguous exhausted source FnOnce callback")
  if !joins.isEmpty then
    let _ ← ThreadMachine.takeJoin h.thread token
    pure ()
  else if !futex.isEmpty then
    match h.futex with
    | some hooks => do
        ExecutionStateTransport.action
          ((LinuxFutexMachine.runtime hooks choice).cancel token)
    | none => throw (.unsupported "selected futex callback has no source-built capability")
  else if !sync.isEmpty then
    let _ ← ExecutionStateTransport.action (TypedSyncMachine.take EvalTypedSyncMachine.views token)
    pure ()
  else
    let capture ← ExecutionStateTransport.action (OwnedSocketMachine.take EvalOwnedIoMachine.socketViews token)
    ExecutionStateTransport.action (match capture with
      | .io capture => OwnedIoRuntime.dropCapture (OwnedIoMachine.hooks EvalOwnedIoMachine.views h.io.operations) capture
      | .virtual capture => OwnedVirtualSocket.dropCapture h.socket.virtual capture
      | .tcp capture => OwnedTcpSocket.dropCapture h.socket.tcp capture
      | .owner fd => Files.withDrop
          (throw (.invalidProgram "socket owner guard is not a runnable callback"))
          (h.socket.tcp.source.io.readiness.dropFd fd))
  throw (.resourceExhaustion "nested source callback execution capacity")

private def exhausted
    (h : Hooks Os R P H D O Aff B Poll Instant System Native Profiler C X F A Z T E Iter Raw Listener TcpStream Host AddrIter)
    (choice : C) (token : Nat) :=
  DeadlineMachine.withPruneSuppressed h.deadlineRegistry h.setDeadlineRegistry
    (exhaustedBody h choice token)

private def runWithin : Nat →
    Hooks Os R P H D O Aff B Poll Instant System Native Profiler C X F A Z T E Iter Raw Listener TcpStream Host AddrIter →
    C → Nat → UnblockKind → EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler) Unit
  | 0,h,choice,token,_ => exhausted h choice token
  | capacity+1,h,choice,token,kind =>
    invokeBound (routeSource h (runWithin capacity h choice)) choice token kind

/-- Concrete source-owned final dictionary factory. Nested execution capacity
belongs only to this transient execution dictionary, never deferred source data.
All event/poll/epoll/socket bodies are reconstructed after routing readiness. -/
def prepare
    (h : Hooks Os R P H D O Aff B Poll Instant System Native Profiler C X F A Z T E Iter Raw Listener TcpStream Host AddrIter)
    (choice : C) :=
  routeSource h (runWithin h.nestedCapacity h choice)

/-- Source blocking-I/O weak-source GC reads the prepared canonical manager;
callbacks are not extra provenance roots in the pinned thread visitor. -/
def blockingIoGc
    (h : Hooks Os R P H D O Aff B Poll Instant System Native Profiler C X F A Z T E Iter Raw Listener TcpStream Host AddrIter)
    (choice : C) : EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler) Unit :=
  ExecutionStateTransport.action (BlockingIo.runGc (prepare h choice).socket.tcp.source.io)

def invoke (h : Hooks Os R P H D O Aff B Poll Instant System Native Profiler C X F A Z T E Iter Raw Listener TcpStream Host AddrIter)
    (choice : C) (token : Nat) (kind : UnblockKind) :
    EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler) Unit :=
  runWithin h.nestedCapacity h choice token kind

def invokeInner (h : Hooks Os R P H D O Aff B Poll Instant System Native Profiler C X F A Z T E Iter Raw Listener TcpStream Host AddrIter)
    (choice : C) (token : Nat) (kind : UnblockKind) :
    EStateM StepError (Inner Os R P H D O Aff B Poll Instant System Native Profiler) Unit :=
  ExecutionStateTransport.reverseAction (invoke h choice token kind)

/-- Source physical IO dictionaries are constructed on Inner; wake callbacks
still perform the complete outer ThreadStacks switch on the same state. -/
def innerReadiness (h : Hooks Os R P H D O Aff B Poll Instant System Native Profiler C X F A Z T E Iter Raw Listener TcpStream Host AddrIter)
    (choice : C)
    (base : Readiness.Hooks (Inner Os R P H D O Aff B Poll Instant System Native Profiler) Fd) :
    EStateM StepError (Inner Os R P H D O Aff B Poll Instant System Native Profiler)
      (Readiness.Hooks (Inner Os R P H D O Aff B Poll Instant System Native Profiler) Fd) := do
  let .typed register _ cancel owns := base.runtime.callbackBackend |
    throw (.invalidProgram "final inner source callback router requires a typed runtime")
  let runtime := {base.runtime with callbackBackend := .typed register (invokeInner h choice) cancel owns}
  pure {base with
    runtime
    unblock := fun thread reason => ExecutionStateTransport.reverseAction
      (ThreadStacks.unblockThread thread reason (invoke h choice))}

/-- Registration/cancellation retain their exact source arena; execution of a
selected token uses the full dispatcher, including IO callbacks. Production
factories call this on their already typed runtime before binding wake helpers. -/
def runtime (h : Hooks Os R P H D O Aff B Poll Instant System Native Profiler C X F A Z T E Iter Raw Listener TcpStream Host AddrIter)
    (choice : C)
    (base : SyncRuntime.Hooks (State Os R P H D O Aff B Poll Instant System Native Profiler) Ref V Dest) :
    EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler)
      (SyncRuntime.Hooks (State Os R P H D O Aff B Poll Instant System Native Profiler) Ref V Dest) := do
  match base.callbackBackend with
  | .legacy .. => throw (.invalidProgram "final source callback router requires a typed runtime")
  | .typed register _ cancel owns =>
    pure {base with callbackBackend := .typed register (invoke h choice) cancel owns}

/-- Uses the full ThreadStacks switch and restores only after successful source
callback execution. A callback error retains the selected target and prefix. -/
def readiness (h : Hooks Os R P H D O Aff B Poll Instant System Native Profiler C X F A Z T E Iter Raw Listener TcpStream Host AddrIter)
    (choice : C)
    (base : Readiness.Hooks (State Os R P H D O Aff B Poll Instant System Native Profiler) Fd) :
    EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler)
      (Readiness.Hooks (State Os R P H D O Aff B Poll Instant System Native Profiler) Fd) := do
  pure {base with
    runtime := ← runtime h choice base.runtime
    unblock := fun thread reason => ThreadStacks.unblockThread thread reason (invoke h choice)}

/-- Canonical source eventfd physical effects close over the routed readiness
view, including readiness wakes caused from another callback. -/
def event (h : Hooks Os R P H D O Aff B Poll Instant System Native Profiler C X F A Z T E Iter Raw Listener TcpStream Host AddrIter)
    (choice : C) (wakeBudget : Nat)
    (ready : Readiness.Hooks (State Os R P H D O Aff B Poll Instant System Native Profiler) Fd)
    (base : EventFd.PhysicalHooks (State Os R P H D O Aff B Poll Instant System Native Profiler) Fd) :
    EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler)
      (EventFd.PhysicalHooks (State Os R P H D O Aff B Poll Instant System Native Profiler) Fd) := do
  let ready ← readiness h choice ready
  pure {base with
    runtime := ready.runtime
    updateReadiness := fun fd => Readiness.updateFd wakeBudget ready fd {forceEdge := true}
    unblockThread := fun thread => ready.unblock thread .Eventfd}

def blocking (h : Hooks Os R P H D O Aff B Poll Instant System Native Profiler C X F A Z T E Iter Raw Listener TcpStream Host AddrIter)
    (choice : C)
    (base : BlockingIo.Hooks (State Os R P H D O Aff B Poll Instant System Native Profiler) Fd Poll HostEffect) :
    EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler)
      (BlockingIo.Hooks (State Os R P H D O Aff B Poll Instant System Native Profiler) Fd Poll HostEffect) := do
  pure {base with readiness := ← readiness h choice base.readiness}

/-- The RunLoop scheduler's delayed readiness and host polling use the same
routed wake operation as deadlines and synchronous descriptor operations. -/
def scheduling (h : Hooks Os R P H D O Aff B Poll Instant System Native Profiler C X F A Z T E Iter Raw Listener TcpStream Host AddrIter)
    (choice : C) (wakeBudget : Nat)
    (io : BlockingIo.Hooks (State Os R P H D O Aff B Poll Instant System Native Profiler) Fd Poll HostEffect)
    (base : ThreadStacks.LocalSchedulerHooks MiriMemoryKind
      (ThreadUser Os R P H D O Aff B Poll Instant System Native Profiler)) :
    EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler)
      (ThreadStacks.LocalSchedulerHooks MiriMemoryKind
        (ThreadUser Os R P H D O Aff B Poll Instant System Native Profiler)) := do
  pure (ReadinessMachine.bindScheduling wakeBudget (← blocking h choice io) base)

/-- Deadline execution uses the same terminal dispatcher; no separate timeout
callback table, token supply, host clock or thread selection is introduced. -/
def deadlines (h : Hooks Os R P H D O Aff B Poll Instant System Native Profiler C X F A Z T E Iter Raw Listener TcpStream Host AddrIter)
    (choice : C)
    (clock : Clock.HostHooks Instant System (State Os R P H D O Aff B Poll Instant System Native Profiler))
    (communicate : EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler) Bool)
    (durationSince : System → System → EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler) (Option Clock.Duration)) :=
  EvalHostMachine.deadlines clock communicate durationSince (invoke h choice)
/-- Final Unix dictionary is assembled from the prepared source-owned IO and
socket bodies. Runtime replacement happens before UnixForeign.bind captures
any handler, and entry polling uses the exact routed BlockingIo source body. -/
def unix
    (prepared : CompilerProviders.Prepared)
    (callbacks : Hooks Os R P H D O Aff B Poll Instant System Native Profiler C X F A Z T E Iter Raw Listener TcpStream Host AddrIter)
    (choice : C)
    (tag : Files.FdId → O) (untag : O → Option Files.FdId)
    (sourceFiles : Files.Hooks (Inner Os R P H D O Aff B Poll Instant System Native Profiler) H D O E HM)
    (objects : ForeignSyncMachine.Objects (State Os R P H D O Aff B Poll Instant System Native Profiler))
    (foreign : UnixForeign.Hooks (State Os R P H D O Aff B Poll Instant System Native Profiler)
      Place H D O Os HM Time E Kind ReadDir DirEntry TypedSyncRuntime.Ref Duration Iter AddrIter Instant System TZ Timestamp Block Instance)
    (base : ForeignItems.Hooks Provenance (State Os R P H D O Aff B Poll Instant System Native Profiler)
      Place TypedSyncRuntime.Dest (Pointer (Option Provenance)) Block Instance) := do
  let target ← match compilerUnixTarget prepared with
    | .ok target => pure target
    | .error error => throw error
  let facts := target.facts
  let callbacks := compilerSocketTarget target callbacks
  let base := {base with family := .unix, os := facts.os, arch := target.arch}
  let environmentSource := compilerEnvironmentTarget target foreign.environment.env
  let environment := {foreign.environment with env := environmentSource}
  let fdSource := {foreign.fd.file.fd with
    os := facts.os
    errors := compilerErrorTarget facts foreign.fd.file.fd.errors
    files := {foreign.fd.file.fd.files with family := .unix}}
  let fd := {foreign.fd with file := {foreign.fd.file with fd := fdSource}}
  let pathsDirs := compilerPathTarget target foreign.fs.directories.paths
  let pathsTimes := compilerPathTarget target foreign.fs.times.fd.paths
  let pathsTemp := compilerPathTarget target foreign.fs.temporary.paths
  let fs := {foreign.fs with
    directories := {foreign.fs.directories with paths := pathsDirs}
    times := {foreign.fs.times with fd := {foreign.fs.times.fd with paths := pathsTimes}}
    temporary := {foreign.fs.temporary with paths := pathsTemp}}
  let socketAddress := compilerAddressTarget target foreign.socket.socket.address
  let socket := {foreign.socket with
    socket := {foreign.socket.socket with os := facts.os, address := socketAddress}
    virtual := {foreign.socket.virtual with
      os := facts.os
      errors := compilerErrorTarget facts foreign.socket.virtual.errors}}
  let netbsdEnvironment := compilerEnvironmentTarget target foreign.netbsd.environment
  let pthreadObjects := {foreign.pthread.pthread.objects with os := facts.os}
  let pthreadSync := {foreign.pthread.pthread with objects := pthreadObjects}
  let pthread := {foreign.pthread with pthread := pthreadSync}
  let foreign := {foreign with
    environment := environment
    fd := fd
    fs := fs
    poll := {foreign.poll with os := facts.os}
    pthread := pthread
    socket
    dynamic := {foreign.dynamic with targetEnv := facts.env}
    linuxPlatform := {foreign.linuxPlatform with targetEnv := facts.env}
    netbsd := {foreign.netbsd with environment := netbsdEnvironment}
    stdOnly := {foreign.stdOnly with
      targetEnv := facts.env
      foreign := {foreign.stdOnly.foreign with family := .unix, os := facts.os, arch := target.arch}}
    time := {foreign.time with time := {foreign.time.time with family := .unix, os := facts.os}}}
  let bound := prepare callbacks choice
  let rt ← runtime callbacks choice objects.runtime
  let objects := {objects with
    runtime := rt
    once := {objects.once with runtime := rt}
    pthread := {objects.pthread with runtime := rt}}
  let foreign := UnixForeignMachine.bindSynchronization objects foreign
  let foreign := EvalForeignSocketMachine.bind bound.io bound.socket bound.descriptor tag untag
    bound.synchronousResource sourceFiles foreign
  let nat ← runtime callbacks choice (TypedSyncNat.outward EvalTypedSyncMachine.views bound.io.effects)
  let ready := OwnedSocketTransport.readiness bound.socket.tcp.source.io.readiness nat
  let pollZero := ExecutionStateTransport.action
    (BlockingIo.pollAndUnblock bound.wakeBudget bound.socket.tcp.source.io (some ⟨0,0,by decide⟩))
  let event := {foreign.event.event with runtime := nat}
  let foreign := {foreign with
    pollAndUnblockZero := pollZero
    event := {foreign.event with event}
    linux := {foreign.linux with event}
    socket := {foreign.socket with
      virtual := OwnedSocketTransport.virtual bound.socket.virtual.source nat foreign.socket.virtual
      pollAndUnblockZero := pollZero}
    poll := {foreign.poll with
      epoll := {foreign.poll.epoll with poll := {foreign.poll.epoll.poll with readiness := ready}}
      pollAndUnblockZero := pollZero}
    time := {foreign.time with time := {foreign.time.time with runtime := nat}}}
  pure (UnixForeign.bind foreign base)

/-- Source-owned final execution assembly. The genuine host clock and choice
leaves stay explicit; no caller callback dispatcher or baseline wake execution
is accepted. Scheduling, deadlines and the exported callback dictionaries all
refer to the same finite nested-execution interpreter. -/
def factory
    (prepared : CompilerProviders.Prepared)
    (h : Hooks Os R P H D O Aff B Poll Instant System Native Profiler C X F A Z T E Iter Raw Listener TcpStream Host AddrIter)
    (choice : C)
    (clock : Clock.HostHooks Instant System (State Os R P H D O Aff B Poll Instant System Native Profiler))
    (communicate : EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler) Bool)
    (durationSince : System → System → EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler) (Option Clock.Duration))
    (base : ThreadStacks.LocalSchedulerHooks MiriMemoryKind
      (ThreadUser Os R P H D O Aff B Poll Instant System Native Profiler)) :
    Except StepError
      (Hooks Os R P H D O Aff B Poll Instant System Native Profiler C X F A Z T E Iter Raw Listener TcpStream Host AddrIter ×
        DeadlineMachine.Hooks MiriMemoryKind
          (EvalHostMachine.User Os R P H D O Aff B Poll Instant System Native Profiler) Instant System ×
        ThreadStacks.LocalSchedulerHooks MiriMemoryKind
          (ThreadUser Os R P H D O Aff B Poll Instant System Native Profiler)) :=
  match compilerUnixTarget prepared with
  | .error error => .error error
  | .ok target =>
    let h := compilerSocketTarget target h
    let callbacksPrepared := prepare h choice
    let deadline := deadlines h choice clock communicate durationSince
    let io := callbacksPrepared.socket.tcp.source.io
    let scheduler := {base with
      communicate
      processDelayedReadiness := ExecutionStateTransport.action (Readiness.processDelayed h.wakeBudget io.readiness)
      pollHostIoNonBlocking := ExecutionStateTransport.action (BlockingIo.pollAndUnblock h.wakeBudget io (some ⟨0,0,by decide⟩))
      anyThreadBlockedOnHost := ExecutionStateTransport.action (BlockingIo.anyThreadBlockedOnHost io)
      unblockExpiredDeadlines := DeadlineMachine.unblockExpiredDeadlines deadline}
    .ok (callbacksPrepared,deadline,scheduler)
end Miri.Input.EvalCallbackMachine
