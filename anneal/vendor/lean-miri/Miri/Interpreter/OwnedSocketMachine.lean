import Miri.Interpreter.OwnedIoStore
import Miri.Interpreter.OwnedIoMachine

/-! Single canonical owned-IO store and token supply for TCP and virtual socket
callbacks. Every take consumes source FnOnce data before invoking its body. -/
namespace Miri.Interpreter.OwnedSocketMachine
open Miri.ABI Miri.Memory Miri.Concurrency
abbrev State := TypedSyncMachine.State
abbrev M := TypedSyncMachine.M
structure Views (U F : Type) where
  storage : U → OwnedIoStore.Storage F
  putStorage : U → OwnedIoStore.Storage F → U
  nextCallback : U → Nat
  putNextCallback : U → Nat → U
private def payload : M K U U := return (← get).machine.user.payload.payload.user
private def modifyPayload (f : U → U) : M K U Unit :=
  modify fun s => {s with machine := {s.machine with user := {s.machine.user with payload :=
    {s.machine.user.payload with payload := {s.machine.user.payload.payload with user := f s.machine.user.payload.payload.user}}}}}
private def storage (v : Views U F) : M K U (OwnedIoStore.Storage F) := return v.storage (← payload)
private def setStorage (v : Views U F) (data : OwnedIoStore.Storage F) : M K U Unit :=
  modifyPayload fun u => v.putStorage u data

def register (v : Views U F) (capture : OwnedIoStore.Capture F) : M K U Nat := do
  let data ← storage v
  let token := v.nextCallback (← payload)
  if data.callbacks.any (·.1 == token) then throw (.invalidProgram "shared callback token collision")
  modifyPayload fun u => v.putNextCallback u (token+1)
  setStorage v {data with callbacks := data.callbacks.push (token,capture)}
  pure token
def lookup (v : Views U F) (token : Nat) : M K U (Option (OwnedIoStore.Capture F)) := do
  let entries := (← storage v).callbacks.filter (·.1 == token)
  if entries.size > 1 then throw (.invalidProgram "ambiguous owned callback token")
  pure (entries[0]?.map Prod.snd)
def take (v : Views U F) (token : Nat) : M K U (OwnedIoStore.Capture F) := do
  let some capture ← lookup v token | throw (.callback "missing owned IO callback")
  let data ← storage v
  setStorage v {data with callbacks := data.callbacks.filter (·.1 != token)}
  pure capture
private def takeVirtual (v : Views U F) (token : Nat) : M K U (OwnedVirtualSocket.Capture F) := do
  let .virtual capture ← take v token | throw (.invalidProgram "callback is not a virtual socket FnOnce")
  pure capture
private def takeTcp (v : Views U F) (token : Nat) : M K U (OwnedTcpSocket.Capture F) := do
  let .tcp capture ← take v token | throw (.invalidProgram "callback is not a TCP FnOnce")
  pure capture

def virtual (v : Views U F) (source : VirtualSocket.Hooks (State K U) F E)
    (completion : OwnedSocketCompletion.Hooks (State K U) E I) : OwnedVirtualSocket.Hooks (State K U) F E I where
  source := source
  completion := completion
  register := fun c => register v (.virtual c)
  take := takeVirtual v

def tcp (v : Views U F) (source : TcpSocket.Hooks (State K U) F R L T E P H)
    (completion : OwnedSocketCompletion.Hooks (State K U) E I) : OwnedTcpSocket.Hooks (State K U) F R L T E P H I where
  source := source
  completion := completion
  register := fun c => register v (.tcp c)
  take := takeTcp v

/-- None means this token belongs to another actual source family. IO callbacks
are not treated as synchronization callbacks and are never silently completed. -/
def invoke
    (v : Views U F) (virt : OwnedVirtualSocket.Hooks (State K U) F E I)
    (tcp : OwnedTcpSocket.Hooks (State K U) F R L T E P H I) (resource : Nat)
    (token : Nat) (kind : UnblockKind) : M K U Bool := do
  match ← lookup v token with
  | some (.virtual _) => OwnedVirtualSocket.invoke virt (← takeVirtual v token) kind; pure true
  | some (.tcp _) => OwnedTcpSocket.invoke resource tcp (← takeTcp v token) kind; pure true
  | some (.owner _) =>
    let .owner fd ← take v token | throw (.invalidProgram "source owner token changed kind")
    tcp.source.io.readiness.dropFd fd
    throw (.invalidProgram "socket owner guard is not a runnable callback")
  | _ => pure false
end Miri.Interpreter.OwnedSocketMachine
