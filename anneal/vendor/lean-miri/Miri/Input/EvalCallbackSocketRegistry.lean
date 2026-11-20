import Miri.Input.EvalCallbackSocketSeed
import Miri.Input.EvalUnixSourceConstruction
import Miri.Input.EvalUnixIoConstruction
import Miri.Input.EvalUnixNativeFdConstruction
import Miri.Input.EvalUnixFdConstruction
import Miri.Input.EvalOwnedIoMachine
import Miri.Interpreter.EventFd
import Miri.Interpreter.EventFdMachine
import Miri.Interpreter.SourceOther

namespace Miri.Input.EvalCallbackSocketConstruction
open Miri.ABI Miri.Memory Miri.Interpreter

private def eventFinish
    (errorFromKind : IoError.ErrorKind → EStateM StepError S (IoError.Error Error))
    (finish : Files.Finish S Error) : EventFd.Finish S :=
  ⟨fun result => do
    match result with
    | .ok count => finish (.ok count)
    | .error kind => finish (.error (← errorFromKind kind)), finish.capture⟩

/-- Bind source OtherFileEffects after the canonical registry and eventfd
callback have been created. Eventfd uses the real event store, retry and async
finish semantics. The optional socket route must itself come from the source
socket constructor; absent routes fail only when a tagged socket operation is
requested. Other payloads retain the source's nonblocking/nonterminal
defaults. -/
def otherFileEffects
    (seed : RegistrySeed Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    (event : EventFd.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)))
    (socket : Option (SocketFileEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error))
    (retryBudget : Nat)
    (errorFromKind : IoError.ErrorKind → EStateM StepError
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (IoError.Error Error)) :
    EvalUnixIoConstruction.OtherFileEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error := Id.run do
  let events := EvalOwnedIoMachine.eventStore SourceOther.eventTag SourceOther.eventProject
  let isEvent := fun (reference : FD H D (Other Raw Listener TcpStream Error)) =>
    match reference.value with
    | .other payload => (events.untag payload).isSome
    | _ => false
  let isSocket := fun (reference : FD H D (Other Raw Listener TcpStream Error)) =>
    match reference.value with
    | .other payload => (SourceOther.sockets.project payload).isSome
    | _ => false
  let validateReference := fun (reference : FD H D (Other Raw Listener TcpStream Error)) => do
    let ownership := seed.files.ownership (← get).machine.user
    let entries := ownership.entries.filter (·.ref.id == reference.id)
    unless entries.size == 1 do
      throw (.invalidProgram "source OtherFileEffects received an absent or ambiguous descriptor reference")
    let some entry := entries[0]? | throw (.invalidProgram "source descriptor ownership lookup failed")
    unless entry.strong > 0 do
      throw (.invalidProgram "source OtherFileEffects received a stale descriptor reference")
  let read := fun reference communicate pointer length finish => do
    validateReference reference
    if isEvent reference then
      EventFd.read event retryBudget reference pointer length (eventFinish errorFromKind finish)
    else if isSocket reference then
      match socket with
      | some operations => operations.read reference communicate pointer length finish
      | none => throw (.unsupported "source socket read operation has no attached capability")
    else
      throw (.invalidProgram "unrecognized source file-description payload for read")
  let write := fun reference communicate pointer length finish => do
    validateReference reference
    if isEvent reference then
      EventFd.write event retryBudget reference pointer length (eventFinish errorFromKind finish)
    else if isSocket reference then
      match socket with
      | some operations => operations.write reference communicate pointer length finish
      | none => throw (.unsupported "source socket write operation has no attached capability")
    else
      throw (.invalidProgram "unrecognized source file-description payload for write")
  let readiness := fun payload => do
    if (events.untag payload).isSome then
      let some id := events.untag payload | throw (.invalidProgram "eventfd tag changed during readiness lookup")
      let entries := (events.get (← get).machine.user).filter (·.1 == id)
      unless entries.size == 1 do throw (.invalidProgram "eventfd readiness state absent or ambiguous")
      let some (_,value) := entries[0]? | throw (.invalidProgram "eventfd readiness state missing")
      pure (some (EventFd.readiness value))
    else if (SourceOther.sockets.project payload).isSome then
      match socket with
      | some operations => operations.readiness payload
      | none => throw (.unsupported "source socket readiness has no attached capability")
    else
      pure none
  return {
    read
    write
    shortOperations := fun _ => false
    readiness
    hasReadinessWatched := fun payload =>
      (events.untag payload).isSome || (SourceOther.sockets.project payload).isSome
    isTerminal := fun _ _ => pure false }

/-- Pinned UnixFileDescription's default pread/pwrite arms throw Unsupported.
The source currently has no implementations for eventfd or sockets, so retain
that operation-local behavior. -/
def otherPositionalEffects
    (seed : RegistrySeed Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) :
    EvalUnixNativeFdConstruction.OtherPositionalEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error :=
  let unsupported := fun (reference : FD H D (Other Raw Listener TcpStream Error))
      (_offset : UInt64) (_pointer : Pointer (Option Provenance)) (_length : Nat)
      (_finish : Files.Finish
        (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
        Error) => do
    let ownership := seed.files.ownership (← get).machine.user
    let entries := ownership.entries.filter (·.ref.id == reference.id)
    unless entries.size == 1 do
      throw (.invalidProgram "Unix positional IO received an absent or ambiguous descriptor reference")
    let some entry := entries[0]? | throw (.invalidProgram "Unix positional IO ownership lookup failed")
    unless entry.strong > 0 do throw (.invalidProgram "Unix positional IO received a stale descriptor")
    throw (.unsupported "Unix file-description positional IO is unsupported")
  ⟨unsupported,unsupported⟩

/-- Canonical source tags; these remain valid even while optional socket
operations are unavailable. -/
def socketDescriptor (Raw Listener TcpStream Error : Type) :
    SocketMachine.Descriptor (Other Raw Listener TcpStream Error) := SourceOther.sockets

/-- Construct eventfd's physical hooks directly from the pre-poll registry
seed. The passed `physicalReadiness` is the poll/readiness operation object
being assembled for this same source call; descriptor ownership and event
state still use the seed's canonical registries. -/
def eventPhysicalFromSeed
    (seed : RegistrySeed Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    (physicalReadiness : Readiness.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)))
    (wakeBudget : Nat)
    (access : PlaceMachine.AccessConfig MiriMemoryKind
      (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (place : PlaceHooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C MachineHooks.FrameExtra)
    (choice : C)
    (libcI32 : String → EStateM StepError
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Int32)
    (u64Layout : EStateM StepError
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) LocalLayout) :
    EventFd.PhysicalHooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) :=
  EvalOwnedIoMachine.physicalEvent SourceOther.eventTag SourceOther.eventProject
    seed.readiness physicalReadiness wakeBudget access place choice libcI32 u64Layout

/-- Build BlockingIo around the same early readiness seed. `physicalReadiness`
is supplied only after the caller has constructed the current poll readiness
operations; all persistent tables and TCP readiness state remain canonical. -/
def blockingFromSeed
    (seed : RegistrySeed Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    (physicalReadiness : Readiness.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)))
    (host : HostEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Raw Listener TcpStream Error Poll AddrIter) :
    BlockingIo.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) Poll Error := Id.run do
  let base : BlockingIo.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) Poll Error := {
    readiness := physicalReadiness
    get := do return EvalSocketStorage.blocking.get (← get).machine.user
    put := fun manager => modify fun state => {state with machine := {state.machine with
      user := EvalSocketStorage.blocking.put manager state.machine.user}}
    newPoll := host.newPoll
    dropPoll := host.dropPoll
    registerHostSource := host.registerHostSource
    pollHost := host.pollHost
    sourceReadiness := fun reference => do
      let state ← get
      let registry ← match EvalSocketStorage.sockets.get state.machine.user with
        | .ok registry => pure registry
        | .error error => throw error
      let entries := registry.tcp.filter (·.1 == reference.id)
      if entries.size != 1 then throw (.invalidProgram "blocking IO readiness has missing/ambiguous TCP state")
      let some (_,socket) := entries[0]? | throw (.invalidProgram "blocking IO TCP readiness lookup failed")
      pure socket.ready
    setSourceReadiness := fun reference value => do
      let state ← get
      let registry ← match EvalSocketStorage.sockets.get state.machine.user with
        | .ok registry => pure registry
        | .error error => throw error
      let entries := registry.tcp.filter (·.1 == reference.id)
      if entries.size != 1 then throw (.invalidProgram "blocking IO readiness update has missing/ambiguous TCP state")
      let tcp := registry.tcp.map fun (id,socket) => (id,if id == reference.id then {socket with ready := value} else socket)
      let user ← match EvalSocketStorage.sockets.put {registry with tcp} state.machine.user with
        | .ok user => pure user
        | .error error => throw error
      set {state with machine := {state.machine with user}}
    cloneFd := FileMachine.cloneReference seed.readiness.files }
  ReadinessMachine.bindBlocking seed.readiness EvalSocketStorage.blocking base

/-- Build the one canonical descriptor/ownership/readiness registry before
poll and source OtherFileEffects exist. The seed is only the persistent
registry plus its real last-drop cleanup; it creates no partial Files or
readiness operation dictionary. Core can later attach physical readiness and
source event/socket methods to these same views. -/
def registrySeed
    (hostUsizeBits fileReferenceBudget watcherReferenceBudget : Nat)
    (resources : EvalUnixIoConstruction.FileResourceEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error)) :
    RegistrySeed Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error := Id.run do
  let files := EvalUnixIoConstruction.fileRegistry
    (Os := Os) (R := R) (P := P) (H := H) (D := D) (Aff := Aff) (B := B)
    (Poll := Poll) (Instant := Instant) (System := System) (Native := Native)
    (Profiler := Profiler) (Raw := Raw) (Listener := Listener) (TcpStream := TcpStream)
    (Error := Error) hostUsizeBits fileReferenceBudget resources
  let dropDescription := fun (reference : FD H D (Other Raw Listener TcpStream Error)) => do
    match reference.value with
    | .stdin | .stdout | .stderr | .nullOutput => pure ()
    | .file handle _ _ => resources.dropFile handle
    | .directory handle => resources.dropDirectory handle
    | .other payload => resources.dropOther payload
  let readiness := EvalUnixFdConstruction.readiness files watcherReferenceBudget dropDescription
  return ⟨files,readiness⟩

end Miri.Input.EvalCallbackSocketConstruction
