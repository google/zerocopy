import Miri.Input.EvalCallbackMachine
import Miri.Input.EvalOwnedIoMachine
import Miri.Input.EvalSyncMachine
import Miri.Interpreter.MainMachine

/-! Canonical callback assembly over the initialized EvalWorld. Main/TLS owns
the thread hook, live backend Effects select the owned IO runtime, and
socket bindings are built from their physical/source operations. Callers never
supply a completed EvalCallbackMachine.Hooks. -/
namespace Miri.Input.EvalCallbackSourceConstruction
open Miri.ABI Miri.Memory Miri.Interpreter Miri.Concurrency

abbrev World := EvalCallbackMachine.World
abbrev State := EvalCallbackMachine.State
abbrev Inner := EvalCallbackMachine.Inner
abbrev User Os R P H D O Aff B Poll Instant System Native Profiler :=
  EvalCallbackMachine.ThreadUser Os R P H D O Aff B Poll Instant System Native Profiler
abbrev FD := EvalCallbackMachine.FD

/-! Physical operations used by the canonical owned event/poll/epoll
constructor. Effects are source OS/synchronization writes; no guest-memory
access or callback storage is supplied here. -/
structure IoOperations
    (Os R P H D O Aff B Poll Instant System Native Profiler E Iter Meta : Type) where
  effects : TypedSyncMachine.Effects
    (Inner Os R P H D O Aff B Poll Instant System Native Profiler)
  event : EventFd.PhysicalHooks
    (Inner Os R P H D O Aff B Poll Instant System Native Profiler)
    (FD H D O)
  poll : PollShims.Hooks
    (Inner Os R P H D O Aff B Poll Instant System Native Profiler)
    (FD H D O) Iter
  epoll : EpollShims.Hooks
    (Inner Os R P H D O Aff B Poll Instant System Native Profiler)
    (FD H D O) Iter
  vector : UnixVectored.Hooks
    (Inner Os R P H D O Aff B Poll Instant System Native Profiler) H D O E Meta
  wakeBudget : Nat

/-! Source policy inputs for the owned socket state machine. These are the
primitive stores, physical source operations, and protocol semantics consumed
by `EvalOwnedIoMachine.prepareSockets`; the resulting SocketBindings record
is never selected by the caller. -/
set_option autoImplicit false in structure SocketOperations
    (Os R P H D O Aff B Poll Instant System Native Profiler Raw Listener TcpStream
      Host E AddrIter : Type) where
  machine : ReadinessMachine.Hooks MiriMemoryKind
    (EvalOwnedIoMachine.User Os R P H D O Aff B Poll Instant System Native Profiler)
    H D O
  store : SocketMachine.Store
    (EvalOwnedIoMachine.User Os R P H D O Aff B Poll Instant System Native Profiler)
    Raw Listener TcpStream E
  blocking : ReadinessMachine.BlockingStore
    (EvalOwnedIoMachine.User Os R P H D O Aff B Poll Instant System Native Profiler)
    Poll
  asUnix : FD H D O → EStateM StepError
    (Inner Os R P H D O Aff B Poll Instant System Native Profiler) Unit
  virtual : VirtualSocket.Hooks
    (Inner Os R P H D O Aff B Poll Instant System Native Profiler)
    (FD H D O) E
  tcp : TcpSocket.Hooks
    (Inner Os R P H D O Aff B Poll Instant System Native Profiler)
    (FD H D O) Raw Listener TcpStream E Poll Host
  options : SocketOptions.Hooks
    (Inner Os R P H D O Aff B Poll Instant System Native Profiler)
    (FD H D O) E AddrIter
  socket : Socket.Hooks
    (Inner Os R P H D O Aff B Poll Instant System Native Profiler)
    (FD H D O) E AddrIter
  finish : OwnedSocketCompletion.Hooks
    (Inner Os R P H D O Aff B Poll Instant System Native Profiler) E AddrIter

structure Components
    (Os R P H D O Aff B Poll Instant System Native Profiler C Z T E Iter Meta
      Raw Listener TcpStream Host AddrIter : Type) where
  futex : Option (LinuxFutexMachine.Hooks MiriMemoryKind
    (World Os R P H D O Aff B Poll Instant System Native Profiler)
    C P O B Instant System Z T E)
  io : IoOperations Os R P H D O Aff B Poll Instant System Native Profiler E Iter Meta
  sockets : SocketOperations Os R P H D O Aff B Poll Instant System Native Profiler
    Raw Listener TcpStream Host E AddrIter
  descriptor : SocketMachine.Descriptor O
  nestedCapacity : Nat
  synchronousResource : Nat

/-- Build and return source callbacks with the exact post-construction state.
`EStateM` itself cannot carry the higher-universe callback dictionary, so the
factory runs the existing IO source constructor explicitly and returns both
its real state prefix and the assembled Hooks. On an error the updated state is
returned alongside the error, preserving source effects. -/
def fromSource
    (main : MainMachine.Hooks
      (User Os R P H D O Aff B Poll Instant System Native Profiler)
      C O ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId) Aff P)
    (components : Components Os R P H D O Aff B Poll Instant System Native Profiler
      C Z T E Iter Meta Raw Listener TcpStream Host AddrIter)
    (state : State Os R P H D O Aff B Poll Instant System Native Profiler) :
    Except
      (StepError × State Os R P H D O Aff B Poll Instant System Native Profiler)
      (EvalCallbackMachine.Hooks Os R P H D O Aff B Poll Instant System Native Profiler
        C ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId) Z T E Iter Raw Listener TcpStream Host AddrIter ×
       State Os R P H D O Aff B Poll Instant System Native Profiler) := do
  match (EvalOwnedIoMachine.prepare components.io.effects components.io.event
      components.io.poll components.io.epoll components.io.vector
      components.io.wakeBudget).run (ExecutionStateTransport.inward state) with
  | .error error after => throw (error,ExecutionStateTransport.outward after)
  | .ok io after =>
    let sockets := EvalOwnedIoMachine.prepareSockets io.effects components.sockets.machine
      components.descriptor components.sockets.store components.sockets.blocking
      components.sockets.asUnix components.sockets.virtual components.sockets.tcp
      components.sockets.options components.sockets.socket components.sockets.finish
      components.synchronousResource
    let hooks : EvalCallbackMachine.Hooks Os R P H D O Aff B Poll Instant System Native Profiler
        C ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId) Z T E Iter Raw Listener TcpStream Host AddrIter := {
      thread := main.termination.tls.thread
      futex := components.futex
      io
      socket := sockets
      descriptor := components.descriptor
      options := components.sockets.options
      wakeBudget := components.io.wakeBudget
      nestedCapacity := components.nestedCapacity
      synchronousResource := components.synchronousResource
      deadlineRegistry := fun u => u.user.payload.payload.host.deadlines
      setDeadlineRegistry := fun deadlines u => {u with user := {u.user with payload := {u.user.payload with payload :=
        {u.user.payload.payload with host := {u.user.payload.payload.host with deadlines}}}}} }
    pure (hooks,ExecutionStateTransport.outward after)

end Miri.Input.EvalCallbackSourceConstruction
