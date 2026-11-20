import Miri.Input.EvalCallbackOperationConstruction
import Miri.Input.EvalUnixSourceConstruction
import Miri.Input.EvalUnixIoConstruction
import Miri.Input.EvalUnixFdConstruction
import Miri.Interpreter.TcpSocket
import Miri.Interpreter.SocketAddress
import Miri.Interpreter.SocketOptions

namespace Miri.Input.EvalCallbackSocketConstruction
open Miri.ABI Miri.Memory Miri.Interpreter

abbrev FD H D O := Files.Ref (Files.Description H D O)
abbrev Other Raw Listener TcpStream Error :=
  EvalUnixSourceConstruction.Other Raw Listener TcpStream Error
abbrev User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalUnixSourceConstruction.User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
abbrev State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalUnixSourceConstruction.State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
abbrev RegistryUser Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalUnixSourceConstruction.User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error

/-! The minimal file-description route for source event/socket operations. -/
structure SocketFileEffects (S H D O Error : Type) where
  read : FD H D O → Bool → Pointer (Option Provenance) → Nat → Files.Finish S Error →
    EStateM StepError S Unit
  write : FD H D O → Bool → Pointer (Option Provenance) → Nat → Files.Finish S Error →
    EStateM StepError S Unit
  readiness : O → EStateM StepError S (Option Files.Readiness)

structure HostEffects (S H D O Raw Listener TcpStream Error Poll AddrIter : Type) where
  /-- Host socket creation and ownership transitions. -/
  newRaw : Socket.Family → EStateM StepError S (Except (IoError.HostError Error) Raw)
  nonblocking : Raw → Bool → EStateM StepError S (Except (IoError.HostError Error) Unit)
  dropRaw : Raw → EStateM StepError S Unit
  rawToListener : Raw → EStateM StepError S Listener
  rawToStream : Raw → EStateM StepError S TcpStream
  /-- Host network operations. Address/state policy remains in TcpSocket. -/
  hostBind : TcpSocket.SocketState Raw Listener TcpStream → SocketAddress.Address →
    EStateM StepError S (Except (IoError.HostError Error) Unit)
  hostListen : TcpSocket.SocketState Raw Listener TcpStream → Int32 →
    EStateM StepError S (Except (IoError.HostError Error) Unit)
  hostConnect : Raw → SocketAddress.Address →
    EStateM StepError S (Except (IoError.HostError Error) Unit)
  hostAccept : Listener →
    EStateM StepError S (Except (IoError.HostError Error) (TcpStream × SocketAddress.Address))
  hostSend : TcpStream → ByteArray → EStateM StepError S (Except (IoError.HostError Error) Nat)
  hostRecv : TcpStream → Nat → Bool → EStateM StepError S (Except (IoError.HostError Error) ByteArray)
  hostLocal : TcpSocket.SocketState Raw Listener TcpStream →
    EStateM StepError S (Except (IoError.HostError Error) SocketAddress.Address)
  hostPeer : TcpStream → EStateM StepError S (Except (IoError.HostError Error) SocketAddress.Address)
  hostShutdown : TcpStream → Socket.Shutdown →
    EStateM StepError S (Except (IoError.HostError Error) Unit)
  hostTakeError : TcpSocket.SocketState Raw Listener TcpStream →
    EStateM StepError S (Except (IoError.HostError Error) (Option (IoError.HostError Error)))
  /-- Actual host option access. Timeout and SO_ERROR state transitions are
  built from the canonical TCP store and are intentionally absent here. -/
  setHostOption : FD H D O → SocketOptions.HostOption → SocketOptions.Value →
    EStateM StepError S (Option (Except (IoError.HostError Error) Unit))
  getHostOption : FD H D O → SocketOptions.HostOption →
    EStateM StepError S (Option (Except (IoError.HostError Error) SocketOptions.Value))
  /-- Host `ToSocketAddrs` iterator operations used by getaddrinfo. -/
  resolve : String → UInt16 → EStateM StepError S (Except (IoError.HostError Error) AddrIter)
  nextAddress : AddrIter → EStateM StepError S (Option (SocketAddress.Address × AddrIter))
  dropIterator : AddrIter → EStateM StepError S Unit
  resolutionDiagnostic : IoError.HostError Error → EStateM StepError S Unit
  /-- Host clock and one-time diagnostic capabilities used by TcpSocket. -/
  deadline : Option Clock.Duration → EStateM StepError S ThreadDeadline
  connectingNameWarningOnce : EStateM StepError S Unit
  /-- Host profile fact from the selected runtime, independent of guest target. -/
  edgeBackend : Bool
  /-- Raw host `mio::Poll` lifecycle. BlockingIo source/manager state is built
  from the canonical readiness and HostRuntime stores by the source binder. -/
  newPoll : EStateM StepError S (Except (IoError.HostError Error) Poll)
  dropPoll : Poll → EStateM StepError S Unit
  registerHostSource : Poll → FD H D O → Files.FdId → BlockingIo.Interest →
    EStateM StepError S (Except (IoError.HostError Error) Unit)
  pollHost : Poll → Option Clock.Duration → Nat →
    EStateM StepError S (Except (IoError.HostError Error) (Array BlockingIo.Event))

structure RegistrySeed (Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error : Type) where
  files : FileMachine.Hooks MiriMemoryKind
    (RegistryUser Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    H D (Other Raw Listener TcpStream Error)
  readiness : ReadinessMachine.Hooks MiriMemoryKind
    (RegistryUser Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    H D (Other Raw Listener TcpStream Error)

end Miri.Input.EvalCallbackSocketConstruction
