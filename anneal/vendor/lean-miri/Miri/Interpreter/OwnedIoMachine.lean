import Miri.Interpreter.OwnedIoRuntime
import Miri.Interpreter.EpollShims
import Miri.Interpreter.TypedSyncMachine

/-! Source IO callback ownership on the actual machine. The one supply is
ThreadMachine.nextCallback via views; IO storage contains only positive data. -/
namespace Miri.Interpreter.OwnedIoMachine
open Miri.ABI Miri.Memory Miri.Concurrency
abbrev State := TypedSyncMachine.State
abbrev M := TypedSyncMachine.M
structure Views (U F : Type) where
  storage : U → OwnedIoRuntime.Storage F
  putStorage : U → OwnedIoRuntime.Storage F → U
  nextCallback : U → Nat
  putNextCallback : U → Nat → U
private def payload : M K U U := return (← get).machine.user.payload.payload.user
private def modifyPayload (f : U → U) : M K U Unit :=
  modify fun s => {s with machine := {s.machine with user := {s.machine.user with payload :=
    {s.machine.user.payload with payload := {s.machine.user.payload.payload with user := f s.machine.user.payload.payload.user}}}}}
private def storage (v : Views U F) : M K U (OwnedIoRuntime.Storage F) := return v.storage (← payload)
private def setStorage (v : Views U F) (data : OwnedIoRuntime.Storage F) : M K U Unit :=
  modifyPayload fun u => v.putStorage u data

def owns (v : Views U F) (token : Nat) : M K U Bool := return (← storage v).callbacks.any (·.1 == token)
def register (v : Views U F) (capture : OwnedIoRuntime.Capture F) : M K U Nat := do
  let token := v.nextCallback (← payload)
  let data ← storage v
  if data.callbacks.any (·.1 == token) then throw (.invalidProgram "shared callback token collision")
  modifyPayload fun u => v.putNextCallback u (token+1)
  setStorage v {data with callbacks := data.callbacks.push (token,capture)}
  pure token
def take (v : Views U F) (token : Nat) : M K U (OwnedIoRuntime.Capture F) := do
  let data ← storage v
  let entries := data.callbacks.filter (·.1 == token)
  unless entries.size == 1 do throw (.callback "missing or ambiguous typed owned IO callback")
  let some (_,capture) := entries[0]? | throw (.invalidProgram "owned IO callback lookup invariant")
  setStorage v {data with callbacks := data.callbacks.filter (·.1 != token)}
  pure capture

structure Operations (S F E : Type) where
  event : EventFd.PhysicalHooks S F
  completion : IoCompletion.Hooks S E
  errorFromKind : IoError.ErrorKind → EStateM StepError S (IoError.Error E)
  dropWatcher : Nat → EStateM StepError S Unit
  pollReady : Nat → Array (Int32 × IoCompletion.Dest) → EStateM StepError S UInt32
  writeU32 : UInt32 → IoCompletion.Dest → EStateM StepError S Unit
  epollReady : F → IoCompletion.Dest → IoCompletion.Dest → EStateM StepError S Nat
  epollRemoveBlocked : F → ThreadId → EStateM StepError S Unit

def hooks (v : Views U F) (h : Operations (State K U) F E) : OwnedIoRuntime.Hooks (State K U) F E where
  event := h.event
  completion := h.completion
  errorFromKind := h.errorFromKind
  register := register v
  take := take v
  dropWatcher := h.dropWatcher
  pollReady := h.pollReady
  writeU32 := h.writeU32
  epollReady := h.epollReady
  epollRemoveBlocked := h.epollRemoveBlocked
/-- Real eventfd FileDescription execution now selects the data interpreter;
no source callback registration consults a legacy Registry S. -/
def bindEvent (v : Views U F) (h : Operations (State K U) F E) : EventFd.Hooks (State K U) F :=
  let runtime := hooks v h
  {toPhysicalHooks := h.event, deferred := .typed (OwnedIoRuntime.readStep runtime) (OwnedIoRuntime.writeStep runtime)}
def bindPoll (v : Views U F) (h : Operations (State K U) F E)
    (poll : PollShims.Hooks (State K U) F Iter) : PollShims.Hooks (State K U) F Iter :=
  {poll with deferred := .typed fun watcher interests dest deadline =>
    OwnedIoRuntime.block (hooks v h) (.poll watcher interests dest) .Readiness deadline}
def bindEpoll (v : Views U F) (h : Operations (State K U) F E)
    (epoll : EpollShims.Hooks (State K U) F Iter) : EpollShims.Hooks (State K U) F Iter :=
  {epoll with
    poll := bindPoll v h epoll.poll
    deferred := .typed fun fd event dest deadline =>
      OwnedIoRuntime.block (hooks v h) (.epoll fd event dest) .Readiness deadline}
end Miri.Interpreter.OwnedIoMachine
