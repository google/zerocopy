import Miri.Input.EvalForeignSyncMachine
import Miri.Input.EvalOwnedIoMachine
import Miri.Interpreter.OwnedIoTransport

/-! The actual Unix foreign chain selects typed owned eventfd/poll/epoll IO.
Existing FD/socket families keep their source dispatch, while these supported
families use the one HostRuntime arena and canonical physical operations. -/
namespace Miri.Input.EvalForeignIoMachine
open Miri.ABI Miri.Memory Miri.Interpreter Miri.Concurrency
abbrev State := EvalForeignSyncMachine.State
abbrev Inner := EvalOwnedIoMachine.State
abbrev FD := EvalOwnedIoMachine.FD
private def action (a : EStateM StepError (Inner Os R P H D O Aff B Poll Instant System Native Profiler) A) :
    EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler) A :=
  ExecutionStateTransport.action a

def bind
    (bound : EvalOwnedIoMachine.Bindings (Inner Os R P H D O Aff B Poll Instant System Native Profiler) (FD H D O) E Iter)
    (tag : Files.FdId → O) (untag : O → Option Files.FdId)
    (h : UnixForeign.Hooks (State Os R P H D O Aff B Poll Instant System Native Profiler)
      Place H D O Os HM Time E Kind ReadDir DirEntry TypedSyncRuntime.Ref Duration Iter AddrIter Instant System TZ Timestamp Block Instance) := Id.run do
  let runtime := OwnedIoMachine.hooks EvalOwnedIoMachine.views bound.operations
  let event := OwnedIoTransport.event EvalTypedSyncMachine.views EvalOwnedIoMachine.views bound.effects bound.operations
  let poll := {h.poll.epoll.poll with
    readiness := {h.poll.epoll.poll.readiness with runtime := event.runtime}
    deferred := .typed fun watcher interests dest deadline =>
      action (OwnedIoRuntime.block runtime (.poll watcher interests dest) .Readiness deadline)}
  let epoll := {h.poll.epoll with
    poll
    deferred := .typed fun fd events dest deadline =>
      action (OwnedIoRuntime.block runtime (.epoll fd events dest) .Readiness deadline)}
  let store := OwnedIoTransport.store (EvalOwnedIoMachine.eventStore tag untag)
  let files := EventFdMachine.bindFiles store event 0
    (fun kind => action (bound.operations.errorFromKind kind)) h.fd.file.fd.files
  return {h with
    event := {h.event with event}
    linux := {h.linux with event}
    poll := {h.poll with epoll}
    fd := {h.fd with file := {h.fd.file with fd := {h.fd.file.fd with files}}}}

/-- Actual terminal Unix foreign dictionary: typed synchronization and owned IO
are installed before the source dispatch captures its hooks. -/
def unix
    (sync : ForeignSyncMachine.Objects (State Os R P H D O Aff B Poll Instant System Native Profiler))
    (bound : EvalOwnedIoMachine.Bindings (Inner Os R P H D O Aff B Poll Instant System Native Profiler) (FD H D O) E Iter)
    (tag : Files.FdId → O) (untag : O → Option Files.FdId)
    (h : UnixForeign.Hooks (State Os R P H D O Aff B Poll Instant System Native Profiler)
      Place H D O Os HM Time E Kind ReadDir DirEntry TypedSyncRuntime.Ref Duration Iter AddrIter Instant System TZ Timestamp Block Instance)
    (base : ForeignItems.Hooks Provenance (State Os R P H D O Aff B Poll Instant System Native Profiler)
      Place TypedSyncRuntime.Dest (Pointer (Option Provenance)) Block Instance) :=
  UnixForeign.bind (bind bound tag untag (UnixForeignMachine.bindSynchronization sync h)) base

def invoke
    (bound : EvalOwnedIoMachine.Bindings (Inner Os R P H D O Aff B Poll Instant System Native Profiler) (FD H D O) E Iter)
    (other : Nat → UnblockKind → EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler) Unit)
    (token : Nat) (kind : UnblockKind) : EStateM StepError (State Os R P H D O Aff B Poll Instant System Native Profiler) Unit := do
  if ← action (OwnedIoMachine.owns EvalOwnedIoMachine.views token) then
    action (OwnedIoRuntime.invoke (OwnedIoMachine.hooks EvalOwnedIoMachine.views bound.operations) token kind)
  else other token kind
end Miri.Input.EvalForeignIoMachine
