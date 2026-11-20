import Miri.Interpreter.SocketMachine
import Miri.Interpreter.PollMachine
import Miri.Interpreter.UnixDynamic
import Miri.Interpreter.WindowsPlatform

/-! Library-owned positive representation of source DynSym and dynamic FD
objects. TCP protocol states and descriptor tags are distinct constructors.
No Any payload, string-based descriptor downcast or client fallback is used. -/
namespace Miri.Interpreter.SourceOther
open Miri.Memory
inductive Value (Raw Listener Stream Error : Type) where
  | dynamicSymbol (name : String)
  | eventFd (id : Files.FdId)
  | epoll (watcher : Nat)
  | virtualSocket (id : Files.FdId)
  | tcpSocket (id : Files.FdId)
  | tcpState (value : TcpSocket.State Raw Listener Stream Error)

structure TcpStateEmbedding (Other Raw Listener Stream Error : Type) where
  inject : TcpSocket.State Raw Listener Stream Error → Other
  project : Other → Option (TcpSocket.State Raw Listener Stream Error)
  projectInject : ∀ value, project (inject value) = some value

def tcpState : TcpStateEmbedding (Value R L T E) R L T E where
  inject := .tcpState
  project := fun value => match value with | .tcpState state => some state | _ => none
  projectInject := fun _ => rfl

def sockets : SocketMachine.Descriptor (Value R L T E) where
  inject := fun kind id => match kind with | .virtual => .virtualSocket id | .tcp => .tcpSocket id
  project := fun value => match value with
    | .virtualSocket id => some (.virtual,id) | .tcpSocket id => some (.tcp,id) | _ => none

def eventTag (id : Files.FdId) : Value R L T E := .eventFd id
def eventProject : Value R L T E → Option Files.FdId
  | .eventFd id => some id | _ => none
@[simp] theorem event_roundtrip (id : Files.FdId) : eventProject (eventTag (R:=R) (L:=L) (T:=T) (E:=E) id) = some id := rfl

def epoll : PollMachine.DescriptorHooks (Value R L T E) where
  inject := fun value => .epoll value.watcher
  project := fun value => match value with | .epoll watcher => some ⟨watcher⟩ | _ => none

def unixSymbol (value : UnixDynamic.Symbol) : Value R L T E := .dynamicSymbol value.name
def windowsSymbol (value : WindowsPlatform.DynamicSymbol) : Value R L T E := .dynamicSymbol value.name
def dynamicSymbol : Value R L T E → Except StepError UnixDynamic.Symbol
  | .dynamicSymbol name => .ok ⟨name⟩
  | _ => .error (.invalidProgram "non-DynSym object in source function allocation")
def windowsDynamicSymbol : Value R L T E → Except StepError WindowsPlatform.DynamicSymbol
  | .dynamicSymbol name => match WindowsPlatform.DynamicSymbol.parse name with
    | some symbol => .ok symbol | none => .error (.unsupported "unsupported source Windows dynamic symbol")
  | _ => .error (.invalidProgram "non-DynSym object in source function allocation")
end Miri.Interpreter.SourceOther
