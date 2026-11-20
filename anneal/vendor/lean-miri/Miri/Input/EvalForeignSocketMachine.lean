import Miri.Input.EvalForeignIoMachine
import Miri.Input.EvalSocketStorage
import Miri.Interpreter.OwnedSocketTransport

/-! Terminal Unix source dispatcher: owned socket/file IO uses the same final
HostRuntime arena as eventfd, poll and epoll. -/
namespace Miri.Input.EvalForeignSocketMachine
open Miri.ABI Miri.Memory Miri.Interpreter Miri.Concurrency
abbrev State := EvalForeignIoMachine.State
abbrev Inner := EvalOwnedIoMachine.State
abbrev FD := EvalOwnedIoMachine.FD

def bind
    (io : EvalOwnedIoMachine.Bindings (Inner Os R P H D O Aff B Poll Instant System Native Profiler) (FD H D O) E Iter)
    (sockets : EvalOwnedIoMachine.SocketBindings (Inner Os R P H D O Aff B Poll Instant System Native Profiler) (FD H D O) E Raw Listener TcpStream Poll Host AddrIter)
    (descriptor : SocketMachine.Descriptor O)
    (tag : Files.FdId → O) (untag : O → Option Files.FdId)
    (resource : Nat)
    (sourceFiles : Files.Hooks (Inner Os R P H D O Aff B Poll Instant System Native Profiler) H D O E HM)
    (h : UnixForeign.Hooks (State Os R P H D O Aff B Poll Instant System Native Profiler)
      Place H D O Os HM Time E Kind ReadDir DirEntry TypedSyncRuntime.Ref Duration Iter AddrIter Instant System TZ Timestamp Block Instance) := Id.run do
  let h := EvalForeignIoMachine.bind io tag untag h
  let runtime := TypedSyncNat.outward EvalTypedSyncMachine.views io.effects
  let socket := {h.socket with
    socket := OwnedSocketTransport.socket sockets.socket h.socket.socket
    virtual := OwnedSocketTransport.virtual sockets.virtual.source runtime h.socket.virtual}
  let sourceFiles := EvalOwnedIoMachine.files (EvalOwnedIoMachine.eventStore tag untag) io sourceFiles
  let files := OwnedSocketTransport.files
    (EvalOwnedIoMachine.socketFiles descriptor sockets resource sourceFiles) h.fd.file.fd.files
  return {h with socket, fd := {h.fd with file := {h.fd.file with fd := {h.fd.file.fd with files}}}}

def unix
    (io : EvalOwnedIoMachine.Bindings (Inner Os R P H D O Aff B Poll Instant System Native Profiler) (FD H D O) E Iter)
    (sockets : EvalOwnedIoMachine.SocketBindings (Inner Os R P H D O Aff B Poll Instant System Native Profiler) (FD H D O) E Raw Listener TcpStream Poll Host AddrIter)
    (descriptor : SocketMachine.Descriptor O)
    (tag : Files.FdId → O) (untag : O → Option Files.FdId)
    (resource : Nat)
    (sourceFiles : Files.Hooks (Inner Os R P H D O Aff B Poll Instant System Native Profiler) H D O E HM)
    (sync : ForeignSyncMachine.Objects (State Os R P H D O Aff B Poll Instant System Native Profiler))
    (h : UnixForeign.Hooks (State Os R P H D O Aff B Poll Instant System Native Profiler)
      Place H D O Os HM Time E Kind ReadDir DirEntry TypedSyncRuntime.Ref Duration Iter AddrIter Instant System TZ Timestamp Block Instance)
    (base : ForeignItems.Hooks Provenance (State Os R P H D O Aff B Poll Instant System Native Profiler)
      Place TypedSyncRuntime.Dest (Pointer (Option Provenance)) Block Instance) :=
  UnixForeign.bind (bind io sockets descriptor tag untag resource sourceFiles
    (UnixForeignMachine.bindSynchronization sync h)) base

def invoke
    (io : EvalOwnedIoMachine.Bindings (Inner Os R P H D O Aff B Poll Instant System Native Profiler) (FD H D O) E Iter)
    (sockets : EvalOwnedIoMachine.SocketBindings (Inner Os R P H D O Aff B Poll Instant System Native Profiler) (FD H D O) E Raw Listener TcpStream Poll Host AddrIter)
    (resource : Nat)
    (other : Nat → UnblockKind → EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler) Unit)
    (token : Nat) (kind : UnblockKind) : EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler) Unit := do
  if ← ExecutionStateTransport.action (EvalOwnedIoMachine.invokeSocket sockets resource token kind) then return
  EvalForeignIoMachine.invoke io other token kind
end Miri.Input.EvalForeignSocketMachine
