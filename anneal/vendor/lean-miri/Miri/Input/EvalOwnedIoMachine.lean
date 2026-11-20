import Miri.Input.EvalTypedSyncMachine
import Miri.Input.EvalVectoredMachine
import Miri.Interpreter.OwnedIoMachine
import Miri.Interpreter.TypedSyncNat
import Miri.Interpreter.EventFdMachine
import Miri.Interpreter.OwnedSocketOperations

/-! Typed owned IO callbacks on the actual final World. Counters/queues, pending
captures, readiness watchers and callback tokens each have one authoritative
source store. Compiler layouts/host effects reuse their existing dictionaries. -/
namespace Miri.Input.EvalOwnedIoMachine
open Miri.ABI Miri.Memory Miri.Interpreter Miri.Concurrency
abbrev World := EvalTypedSyncMachine.World
abbrev State := EvalTypedSyncMachine.State
abbrev User Os R P H D O Aff B Poll Instant System Native Profiler :=
  ExecutionStateTransport.Inner (World Os R P H D O Aff B Poll Instant System Native Profiler)
abbrev FD H D O := Files.Ref (Files.Description H D O)

def views : OwnedIoMachine.Views (World Os R P H D O Aff B Poll Instant System Native Profiler) (FD H D O) where
  storage := fun w => OwnedIoStore.base w.host.io
  putStorage := fun w io => {w with host := {w.host with io := OwnedIoStore.putBase w.host.io io}}
  nextCallback := fun w => w.runtime.threads.nextCallback
  putNextCallback := fun w nextCallback => {w with runtime := {w.runtime with threads := {w.runtime.threads with nextCallback}}}

def eventStore (tag : Files.FdId → O) (untag : O → Option Files.FdId) :
    EventFdMachine.Store (User Os R P H D O Aff B Poll Instant System Native Profiler) O where
  get := fun u => u.payload.payload.user.host.events
  put := fun events u => {u with payload := {u.payload with payload := {u.payload.payload with user :=
    {u.payload.payload.user with host := {u.payload.payload.user.host with events}}}}}
  tag := tag
  untag := untag

def physicalEvent
    (tag : Files.FdId → O) (untag : O → Option Files.FdId)
    (machine : ReadinessMachine.Hooks MiriMemoryKind
      (User Os R P H D O Aff B Poll Instant System Native Profiler) H D O)
    (ready : Readiness.Hooks (State Os R P H D O Aff B Poll Instant System Native Profiler) (FD H D O))
    (wakeBudget : Nat)
    (access : PlaceMachine.AccessConfig MiriMemoryKind (User Os R P H D O Aff B Poll Instant System Native Profiler))
    (place : PlaceHooks Provenance (State Os R P H D O Aff B Poll Instant System Native Profiler) C MachineHooks.FrameExtra)
    (choice : C)
    (libcI32 : String → EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler) Int32)
    (u64Layout : EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler) LocalLayout) :
    EventFd.PhysicalHooks (State Os R P H D O Aff B Poll Instant System Native Profiler) (FD H D O) :=
  EventFdMachine.physical (eventStore tag untag) machine ready wakeBudget access place choice libcI32 u64Layout

def completion (h : UnixVectored.Hooks S H D O E Meta) : IoCompletion.Hooks S E where
  writeInt := h.fd.writeInt
  writeTargetIsize := h.writeTargetIsize
  errnoNegOne := IoError.setErrnoAndReturnNeg1 h.fd.errors
  deallocateStack := h.deallocateStack
  offsetInbounds := h.offsetInbounds
  copyNonoverlapping := h.copyNonoverlapping

structure Bindings (S F E Iter : Type) where
  effects : TypedSyncMachine.Effects S
  operations : OwnedIoMachine.Operations S F E
  event : EventFd.Hooks S F
  poll : PollShims.Hooks S F Iter
  epoll : EpollShims.Hooks S F Iter

def prepare
    (e : TypedSyncMachine.Effects (State Os R P H D O Aff B Poll Instant System Native Profiler))
    (event : EventFd.PhysicalHooks (State Os R P H D O Aff B Poll Instant System Native Profiler) (FD H D O))
    (poll : PollShims.Hooks (State Os R P H D O Aff B Poll Instant System Native Profiler) (FD H D O) Iter)
    (epoll : EpollShims.Hooks (State Os R P H D O Aff B Poll Instant System Native Profiler) (FD H D O) Iter)
    (vector : UnixVectored.Hooks (State Os R P H D O Aff B Poll Instant System Native Profiler) H D O E Meta)
    (wakeBudget : Nat) :
    EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler)
      (Bindings (State Os R P H D O Aff B Poll Instant System Native Profiler) (FD H D O) E Iter) := do
  let e ← EvalTypedSyncMachine.effects e
  let runtime := TypedSyncNat.runtime EvalTypedSyncMachine.views e
  let event := {event with runtime}
  let poll := {poll with readiness := {poll.readiness with runtime}}
  let epoll := {epoll with poll := {epoll.poll with readiness := {epoll.poll.readiness with runtime}}}
  let operations : OwnedIoMachine.Operations (State Os R P H D O Aff B Poll Instant System Native Profiler) (FD H D O) E := {
    event
    completion := completion vector
    errorFromKind := fun kind => return .host (← vector.fd.errors.hostFromKind kind)
    dropWatcher := poll.readiness.dropWatcher
    pollReady := PollShims.writeReady wakeBudget poll
    writeU32 := poll.writeU32
    epollReady := fun fd dest events => do
      let some watcher ← epoll.asEpoll fd | throw (.invalidProgram "typed epoll callback has wrong descriptor")
      let count ← EpollShims.returnReady wakeBudget epoll watcher dest events
      if count < 0 then throw (.invalidProgram "epoll returned negative event count")
      pure count.toInt.toNat
    epollRemoveBlocked := fun fd thread => do
      let some watcher ← epoll.asEpoll fd | throw (.invalidProgram "typed epoll callback has wrong descriptor")
      Readiness.removeBlockedThread epoll.poll.readiness watcher thread}
  pure {
    effects := e
    operations
    event := OwnedIoMachine.bindEvent views operations
    poll := OwnedIoMachine.bindPoll views operations poll
    epoll := OwnedIoMachine.bindEpoll views operations epoll}

def files
    (store : EventFdMachine.Store (User Os R P H D O Aff B Poll Instant System Native Profiler) O)
    (bound : Bindings (State Os R P H D O Aff B Poll Instant System Native Profiler) (FD H D O) E Iter)
    (base : Files.Hooks (State Os R P H D O Aff B Poll Instant System Native Profiler) H D O E Meta) :=
  EventFdMachine.bindFiles store bound.event 0 bound.operations.errorFromKind base

def invoke
    (bound : Bindings (State Os R P H D O Aff B Poll Instant System Native Profiler) (FD H D O) E Iter)
    (other : Nat → UnblockKind → EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler) Unit)
    (token : Nat) (kind : UnblockKind) : EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler) Unit := do
  if ← OwnedIoMachine.owns views token then
    OwnedIoRuntime.invoke (OwnedIoMachine.hooks views bound.operations) token kind
  else other token kind
/-- Socket callbacks share the exact arena and ThreadMachine token supply used
by eventfd/poll/epoll and synchronization callbacks. -/
def socketViews : OwnedSocketMachine.Views
    (World Os R P H D O Aff B Poll Instant System Native Profiler) (FD H D O) where
  storage := fun w => w.host.io
  putStorage := fun w io => {w with host := {w.host with io}}
  nextCallback := fun w => w.runtime.threads.nextCallback
  putNextCallback := fun w n => {w with runtime := {w.runtime with threads := {w.runtime.threads with nextCallback := n}}}

structure SocketBindings (S F E R L T P H I : Type) where
  virtual : OwnedVirtualSocket.Hooks S F E I
  tcp : OwnedTcpSocket.Hooks S F R L T E P H I
  socket : Socket.Hooks S F E I

def prepareSockets
    (effects : TypedSyncMachine.Effects (State Os R P H D O Aff B Poll Instant System Native Profiler))
    (machine : ReadinessMachine.Hooks MiriMemoryKind (User Os R P H D O Aff B Poll Instant System Native Profiler) H D O)
    (descriptor : SocketMachine.Descriptor O)
    (store : SocketMachine.Store (User Os R P H D O Aff B Poll Instant System Native Profiler) Raw Listener TcpStream E)
    (blocking : ReadinessMachine.BlockingStore (User Os R P H D O Aff B Poll Instant System Native Profiler) Poll)
    (asUnix : FD H D O → EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler) Unit)
    (virtual : VirtualSocket.Hooks (State Os R P H D O Aff B Poll Instant System Native Profiler) (FD H D O) E)
    (tcp : TcpSocket.Hooks (State Os R P H D O Aff B Poll Instant System Native Profiler) (FD H D O) Raw Listener TcpStream E Poll Host)
    (options : SocketOptions.Hooks (State Os R P H D O Aff B Poll Instant System Native Profiler) (FD H D O) E I)
    (socket : Socket.Hooks (State Os R P H D O Aff B Poll Instant System Native Profiler) (FD H D O) E I)
    (finish : OwnedSocketCompletion.Hooks (State Os R P H D O Aff B Poll Instant System Native Profiler) E I)
    (resource : Nat) : SocketBindings (State Os R P H D O Aff B Poll Instant System Native Profiler) (FD H D O) E Raw Listener TcpStream Poll Host I :=
  let runtime := TypedSyncNat.runtime EvalTypedSyncMachine.views effects
  let virtual := {virtual with readiness := {virtual.readiness with runtime}}
  let tcp := {tcp with io := {tcp.io with readiness := {tcp.io.readiness with runtime}}}
  let (virtual,tcp,socket) := SocketMachine.bind machine descriptor store blocking resource asUnix virtual tcp options socket
  let virtual := OwnedSocketMachine.virtual socketViews virtual finish
  let tcp := OwnedSocketMachine.tcp socketViews tcp finish
  {virtual,tcp,socket := {socket with operations := OwnedSocketOperations.operations socketViews descriptor virtual tcp (SocketMachine.bindOptions tcp.source options) resource}}

def socketFiles
    (descriptor : SocketMachine.Descriptor O)
    (bound : SocketBindings (State Os R P H D O Aff B Poll Instant System Native Profiler) (FD H D O) E Raw Listener TcpStream Poll Host I)
    (resource : Nat)
    (base : Files.Hooks (State Os R P H D O Aff B Poll Instant System Native Profiler) H D O E Meta) :=
  OwnedSocketOperations.files descriptor bound.virtual bound.tcp resource base

def invokeSocket
    (bound : SocketBindings (State Os R P H D O Aff B Poll Instant System Native Profiler) (FD H D O) E Raw Listener TcpStream Poll Host I)
    (resource token : Nat) (kind : UnblockKind) :
    EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler) Bool :=
  OwnedSocketMachine.invoke socketViews bound.virtual bound.tcp resource token kind
end Miri.Input.EvalOwnedIoMachine
