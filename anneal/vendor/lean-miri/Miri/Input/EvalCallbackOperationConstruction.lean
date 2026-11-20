import Miri.Input.EvalCallbackSourceConstruction
import Miri.Input.EvalUnixSourceConstruction
import Miri.Input.CompilerPrimitiveFacts
import Miri.Input.CompilerNamedConstants
import Miri.Input.EvalSocketStorage
import Miri.Interpreter.SourceOther

/-! Callback operations reused from the canonical Unix source dispatchers.
This module owns the structural binding: poll/epoll, vectored IO, descriptor
identity, readiness and event storage are taken from one DispatchComponents
bundle. Only the backend-selected typed-sync scalar/write effects and resource
bound remain supplied by the enclosing source runner. -/
namespace Miri.Input.EvalCallbackOperationConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev Other Raw Listener TcpStream Error :=
  EvalSocketStorage.Other Raw Listener TcpStream Error
abbrev User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalSocketStorage.User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
abbrev State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalSocketStorage.State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
abbrev FD H D O := Files.Ref (Files.Description H D O)

/-- Assemble callback IO operations from the final source native-FD bundle.
This is intentionally separate from the Unix dispatch bundle: callback poll
and epoll must share the final Files/readiness registry and the same host
deadline state, while their readiness route is the genuine source route. -/
def sourceIoOperations [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (nativeFd : EvalUnixNativeFdConstruction.Components
      Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
      Meta Path Place C ClockHost I LoadedBody)
    (effects : TypedSyncMachine.Effects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (access : ValidityMachine.Access MiriMemoryKind
      (EvalCoreMachine.Stored Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D (Other Raw Listener TcpStream Error) Native Profiler)))
    (accessConfig : PlaceMachine.AccessConfig MiriMemoryKind
      (EvalOwnedIoMachine.User Os R P H D (Other Raw Listener TcpStream Error)
        Aff B Poll Instant System Native Profiler))
    (projection : PlaceProjectionHooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C MachineHooks.FrameExtra)
    (place : PlaceHooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C MachineHooks.FrameExtra)
    (choice : C)
    (unitLayout : LocalLayout)
    (readinessRoute : EvalUnixFdConstruction.ReadinessRoute
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (hostClock : Clock.HostHooks Instant System
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (errors : IoError.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Error)
    (wakeBudget iterationBudget : Nat) :
    Except StepError
      (EvalCallbackSourceConstruction.IoOperations Os R P H D
        (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler
        Error EvalUnixFdConstruction.ArrayCursor Meta) := do
  let monotonicMillis : DeadlineMachine.MonotonicMillisHooks MiriMemoryKind
      (EvalOwnedIoMachine.User Os R P H D (Other Raw Listener TcpStream Error)
        Aff B Poll Instant System Native Profiler) Instant System := {
    registry := fun u => u.payload.payload.user.host.deadlines
    setRegistry := fun deadlines u => {u with payload := {u.payload with payload :=
      {u.payload.payload with user := {u.payload.payload.user with host :=
        {u.payload.payload.user.host with deadlines}}}}}
    clock := fun u => u.payload.payload.user.host.clock
    host := hostClock }
  let deadlineMillis := DeadlineMachine.monotonicDeadlineMillisFrom monotonicMillis
  let poll ← EvalUnixFdConstruction.pollWithDeadlineMillis p choice access projection
    unitLayout nativeFd.readiness nativeFd.files readinessRoute deadlineMillis iterationBudget
  let epoll := EvalUnixFdConstruction.epoll p choice access projection poll nativeFd.readiness
    SourceOther.epoll errors
  let u64Layout : EStateM StepError
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      LocalLayout := do
    match p.primitiveLayout "u64" with
    | .ok value => pure value
    | .error reason => throw (.unsupported s!"compiler u64 layout for eventfd: {reason}")
  let libcI32 : String → EStateM StepError
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Int32 :=
    fun name => do
      let scalar : Scalar Provenance ← match CompilerNamedConstants.scalar p.namedConstants name with
        | .ok value => pure value
        | .error reason => throw (.unsupported s!"compiler libc constant `{name}`: {reason}")
      match scalar.toInt32 with
      | .ok value => pure value
      | .error error => throw (ScalarOps.scalarError error)
  let event := EvalOwnedIoMachine.physicalEvent SourceOther.eventTag SourceOther.eventProject
    nativeFd.readiness poll.readiness wakeBudget accessConfig place choice libcI32 u64Layout
  pure { effects, event, poll, epoll, vector := nativeFd.vector.vector, wakeBudget }

private def lift {S : Type} (value : Except StepError A) : EStateM StepError S A :=
  match value with
  | .ok result => pure result
  | .error error => throw error

/-- Derive the callback IO primitives from the very same Unix dispatch bundle
that Core installs for foreign calls. In particular, this does not accept a
second poll or epoll ABI/readiness dictionary, a second vectored-memory
dictionary, or an alternate event-FD tag/store. The caller provides only the
active-backend-dependent typed-sync scalar effects and the callback resource
bound. -/
def ioOperations [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (dispatch : EvalUnixSourceConstruction.DispatchComponents
      Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
      Meta Path Place C ClockHost I)
    (effects : TypedSyncMachine.Effects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (access : PlaceMachine.AccessConfig MiriMemoryKind
      (EvalOwnedIoMachine.User Os R P H D (Other Raw Listener TcpStream Error)
        Aff B Poll Instant System Native Profiler))
    (place : PlaceHooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C MachineHooks.FrameExtra)
    (choice : C) (wakeBudget : Nat) :
    Except StepError
      (EvalCallbackSourceConstruction.IoOperations Os R P H D
        (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler
        Error EvalUnixFdConstruction.ArrayCursor Meta) := do
  -- The dispatch component is parameterized over the actual path/iterator
  -- backend types; recover the host-state `u64` compiler query at use time.
  let u64Layout : EStateM StepError
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      LocalLayout := do
    lift (p.primitiveLayout "u64"
      |>.mapError fun error => .unsupported s!"compiler u64 layout for eventfd: {error}")
  let libcI32 : String → EStateM StepError
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Int32 :=
    fun name => do
      let scalar : Scalar Provenance ← match CompilerNamedConstants.scalar p.namedConstants name with
        | .ok value => pure value
        | .error reason => throw (.unsupported s!"compiler libc constant `{name}`: {reason}")
      lift (scalar.toInt32.mapError ScalarOps.scalarError)
  let poll := dispatch.environmentAndPoll.poll.epoll.poll
  let readiness := dispatch.nativeFd.readiness
  let event := EvalOwnedIoMachine.physicalEvent
    SourceOther.eventTag SourceOther.eventProject readiness poll.readiness wakeBudget
    access place choice libcI32 u64Layout
  pure {
    effects
    event
    poll
    epoll := dispatch.environmentAndPoll.poll.epoll
    vector := dispatch.nativeFd.vector.vector
    wakeBudget }

/-- Replace every socket state/descriptor-owner operation in a socket seed by
the canonical final EvalWorld sources. Protocol and genuine host operations
remain those built by the socket source constructor; callers cannot install a
parallel readiness registry, descriptor table, blocking store, or Unix downcast.
The descriptor encoding is also fixed to SourceOther's exact tagged identity. -/
def bindSocketState
    (dispatch : EvalUnixSourceConstruction.DispatchComponents
      Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
      Meta Path Place C ClockHost I)
    (base : EvalCallbackSourceConstruction.SocketOperations Os R P H D
      (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler
      Raw Listener TcpStream Error Error AddrIter) :
    EvalCallbackSourceConstruction.SocketOperations Os R P H D
      (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler
      Raw Listener TcpStream Error Error AddrIter :=
  { base with
    machine := dispatch.nativeFd.readiness
    store := EvalSocketStorage.sockets
    blocking := EvalSocketStorage.blocking
    asUnix := dispatch.nativeFd.fd.file.fd.asUnix }

def descriptor (Raw Listener TcpStream Error : Type) :
    SocketMachine.Descriptor (Other Raw Listener TcpStream Error) :=
  SourceOther.sockets

end Miri.Input.EvalCallbackOperationConstruction
