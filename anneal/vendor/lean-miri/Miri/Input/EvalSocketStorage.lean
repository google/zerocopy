import Miri.Input.EvalOwnedIoMachine
import Miri.Interpreter.SourceOther

/-! Canonical final SourceOther representation and actual HostRuntime socket
state. Decoder checks are explicit: malformed state tags are never silently
filtered away. The final factory does not accept a replaceable Any embedding. -/
namespace Miri.Input.EvalSocketStorage
open Miri.ABI Miri.Memory Miri.Interpreter Miri.Concurrency
abbrev Other := SourceOther.Value
abbrev World Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalOwnedIoMachine.World Os R P H D (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler
abbrev User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  ExecutionStateTransport.Inner (World Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
abbrev State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  MachineHooks.State MiriMemoryKind (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)

private def decode (values : Array (Files.FdId × Other Raw Listener TcpStream Error)) :
    Except StepError (Array (Files.FdId × TcpSocket.State Raw Listener TcpStream Error)) :=
  values.mapM fun (id,value) => do
    let some state := SourceOther.tcpState.project value |
      throw (.invalidProgram "TCP state table contains a non-state source object")
    pure (id,state)

def sockets : SocketMachine.Store (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    Raw Listener TcpStream Error where
  get := fun u => do
    let host := u.payload.payload.user.host
    pure ⟨host.virtualSockets,← decode host.tcpSockets⟩
  put := fun values u => do
    let _ ← decode u.payload.payload.user.host.tcpSockets
    let host := {u.payload.payload.user.host with
      virtualSockets := values.virtual
      tcpSockets := values.tcp.map fun (id,state) => (id,SourceOther.tcpState.inject state)}
    pure {u with payload := {u.payload with payload := {u.payload.payload with user :=
      {u.payload.payload.user with host}}}}

def blocking : ReadinessMachine.BlockingStore
    (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Poll where
  get := fun u => u.payload.payload.user.host.blocking
  put := fun blocking u => {u with payload := {u.payload with payload := {u.payload.payload with user :=
    {u.payload.payload.user with host := {u.payload.payload.user.host with blocking}}}}}

/-- Actual source FD table and strong ownership, without a duplicate table. -/
def files (hostUsizeBits referenceBudget : Nat)
    (onLastDrop : Files.Description H D (Other Raw Listener TcpStream Error) →
      MachineHooks.M MiriMemoryKind (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Unit) :
    FileMachine.Hooks MiriMemoryKind
      (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) H D (Other Raw Listener TcpStream Error) where
  table := fun u => u.payload.payload.user.runtime.descriptors
  setTable := fun descriptors u => {u with payload := {u.payload with payload := {u.payload.payload with user :=
    {u.payload.payload.user with runtime := {u.payload.payload.user.runtime with descriptors}}}}}
  ownership := fun u => u.payload.payload.user.runtime.ownership
  setOwnership := fun ownership u => {u with payload := {u.payload with payload := {u.payload.payload with user :=
    {u.payload.payload.user with runtime := {u.payload.payload.user.runtime with ownership}}}}}
  hostUsizeBits := hostUsizeBits
  referenceBudget := referenceBudget
  onLastDrop := onLastDrop

def readiness
    (files : FileMachine.Hooks MiriMemoryKind
      (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) H D (Other Raw Listener TcpStream Error))
    (watcherReferenceBudget : Nat)
    (onLastDrop : Files.Ref (Files.Description H D (Other Raw Listener TcpStream Error)) →
      MachineHooks.M MiriMemoryKind (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Unit) :
    ReadinessMachine.Hooks MiriMemoryKind
      (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) H D (Other Raw Listener TcpStream Error) where
  files := files
  registry := fun u => u.payload.payload.user.host.readiness
  setRegistry := fun readiness u => {u with payload := {u.payload with payload := {u.payload.payload with user :=
    {u.payload.payload.user with host := {u.payload.payload.user.host with readiness}}}}}
  watcherReferenceBudget := watcherReferenceBudget
  onLastDrop := onLastDrop
end Miri.Input.EvalSocketStorage
