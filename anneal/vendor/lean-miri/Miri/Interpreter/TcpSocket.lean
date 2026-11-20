import Miri.Interpreter.Socket
import Miri.Interpreter.BlockingIo

/-! Pinned unix/tcp_socket.rs. Raw/socket2, mio listener and stream ownership
remain separate typed host resources. All portable state/readiness policy is here. -/
namespace Miri.Interpreter.TcpSocket
open Miri.ABI Miri.Memory Miri.Concurrency
abbrev M := EStateM StepError
inductive SocketState (Raw Listener Stream : Type) where
  | initial (raw : Raw) | listening (listener : Listener) | connecting (stream : Stream)
  | connected (stream : Stream) | failed (stream : Stream) | transition
structure State (R L T E : Type) where
  family : Socket.Family
  socket : SocketState R L T
  nonblock : Bool
  bound : Bool := false
  ready : Files.Readiness := { writable := true, writeClosed := true }
  error : Option (IoError.HostError E) := none
  readTimeout : Option Clock.Duration := none
  writeTimeout : Option Clock.Duration := none
structure Hooks (S F R L T E Poll Host : Type) where
  io : BlockingIo.Hooks S F Poll Host
  get : F → M S (State R L T E)
  put : F → State R L T E → M S Unit
  cloneFd : F → M S F
  newFd : State R L T E → M S F
  insert : F → M S Int32
  os : String
  hostWindows : Bool
  hostEdgeBackend : Bool
  errors : IoError.Hooks S E
  newRaw : Socket.Family → M S (Except (IoError.HostError E) R)
  nonblocking : R → Bool → M S (Except (IoError.HostError E) Unit)
  dropRaw : R → M S Unit
  rawToListener : R → M S L
  rawToStream : R → M S T
  hostBind : SocketState R L T → SocketAddress.Address → M S (Except (IoError.HostError E) Unit)
  hostListen : SocketState R L T → Int32 → M S (Except (IoError.HostError E) Unit)
  hostConnect : R → SocketAddress.Address → M S (Except (IoError.HostError E) Unit)
  hostAccept : L → M S (Except (IoError.HostError E) (T × SocketAddress.Address))
  hostSend : T → ByteArray → M S (Except (IoError.HostError E) Nat)
  hostRecv : T → Nat → Bool → M S (Except (IoError.HostError E) ByteArray)
  hostLocal : SocketState R L T → M S (Except (IoError.HostError E) SocketAddress.Address)
  hostPeer : T → M S (Except (IoError.HostError E) SocketAddress.Address)
  hostShutdown : T → Socket.Shutdown → M S (Except (IoError.HostError E) Unit)
  hostTakeError : SocketState R L T → M S (Except (IoError.HostError E) (Option (IoError.HostError E)))
  readBytes : Pointer (Option Provenance) → Nat → M S ByteArray
  writeBytes : Pointer (Option Provenance) → ByteArray → M S Unit
  /-- True -> actual monotonic now; false+duration -> now.add_lossy(duration). -/
  deadline : Option Clock.Duration → M S ThreadDeadline
  connectingNameWarningOnce : M S Unit
  wakeBudget : Nat
private def onError (action : M S A) (cleanup : M S Unit) : M S A := fun state =>
  match action state with
  | .ok value state => .ok value state
  | .error error state => match cleanup state with
    | .ok _ state => .error error state | .error next state => .error next state
private def drop (h : Hooks S F R L T E P H) := h.io.readiness.dropFd
private def cancelIfPresent (h : Hooks S F R L T E P H) (token : Nat) : M S Unit := do
  let runtime := h.io.readiness.runtime
  if (← runtime.callbacks).entries.any (·.1 == token) then SyncRuntime.cancelCallback runtime token
/-- Typed FnOnce capture owner used across both immediate and delayed IO. The
arena takes it before invocation and drops its real FD capture on every exit. -/
private def blockOwned (h : Hooks S F R L T E P H) (fd : F) (interest : BlockingIo.Interest)
    (deadline : Option ThreadDeadline) (body : SyncRuntime.Callback S) : M S Unit := do
  let runtime := h.io.readiness.runtime
  let (registry,token) := (← runtime.callbacks).registerOwned body (drop h fd)
  runtime.putCallbacks registry
  onError (do
    let temporary ← h.cloneFd fd
    BlockingIo.blockThreadForIo h.io temporary interest deadline (SyncRuntime.runCallback runtime token)
  ) (cancelIfPresent h token)
private def ownAction (h : Hooks S F R L T E P H) (fd : F) (body : Bool → M S Unit)
    (start : (Bool → M S Unit) → M S Unit) : M S Unit := do
  let runtime := h.io.readiness.runtime
  let (registry,token) := (← runtime.callbacks).registerOwned (fun kind => body (kind == .Ready)) (drop h fd)
  runtime.putCallbacks registry
  onError (start fun success => SyncRuntime.runCallback runtime token (if success then .Ready else .TimedOut)) (cancelIfPresent h token)
private def communicating (enabled : Bool) : M S Unit := do
  if !enabled then throw (.invalidProgram "cannot have TcpSocket under isolation")
private def validHost : SocketState R L T → M S Unit
  | .transition => throw (.invalidProgram "TCP host socket observed during transition")
  | _ => pure ()
private def family : SocketAddress.Address → Socket.Family
  | .v4 .. => .ipv4 | .v6 .. => .ipv6
private def unspecified : Socket.Family → SocketAddress.Address
  | .ipv4 => .v4 0 0 | .ipv6 => .v6 0 0 0 0

def newSocket (h : Hooks S F R L T E P H) (family : Socket.Family) (nonblock : Bool) : M S (Except (IoError.HostError E) F) := do
  match ← h.newRaw family with
  | .error error => return .error error
  | .ok raw =>
    match ← onError (h.nonblocking raw true) (h.dropRaw raw) with
    | .error error => h.dropRaw raw; return .error error
    | .ok _ => return .ok (← h.newFd { family := family, socket := .initial raw, nonblock := nonblock })

def ensureNotFailed (h : Hooks S F R L T E P H) (fd : F) (name : String) : M S Unit := do
  if let .failed _ := (← h.get fd).socket then
    throw (.unsupported s!"{name}: socket unspecified after failed connect")

def updateLastError (h : Hooks S F R L T E P H) (fd : F) : M S Unit := do
  let value ← h.get fd
  validHost value.socket
  let .ok error ← h.hostTakeError value.socket | throw (.invalidProgram "reading SO_ERROR should not fail")
  if let some error := error then
    let socket := match value.socket with | .connecting stream => .failed stream | state => state
    h.put fd { value with socket := socket, error := some error }

def actionDeadline (h : Hooks S F R L T E P H) (nonblock : Bool) (timeout : Option Clock.Duration) : M S (Option ThreadDeadline) := do
  if nonblock then return some (← h.deadline none)
  match timeout with | none => pure none | some duration => return some (← h.deadline (some duration))

def bind (h : Hooks S F R L T E P H) (fd : F) (communicate : Bool) (address : SocketAddress.Address) : M S (Files.Result E Unit) :=
  Files.withDrop (do
    communicating communicate
    ensureNotFailed h fd "bind"
    let value ← h.get fd
    if value.family != family address then return .error (.libc (if h.os == "linux" || h.os == "android" then "EINVAL" else "EAFNOSUPPORT"))
    validHost value.socket
    match ← h.hostBind value.socket address with
    | .error error => return .error (.host error)
    | .ok _ => h.put fd { value with bound := true }; return .ok ()
  ) (drop h fd)

def listen (h : Hooks S F R L T E P H) (fd : F) (communicate : Bool) (backlog : Int32) : M S (Files.Result E Unit) :=
  Files.withDrop (do
    communicating communicate
    ensureNotFailed h fd "listen"
    let mut value ← h.get fd
    match value.socket with
    | .connecting _ | .connected _ => return .error (.libc "EINVAL")
    | .initial _ | .listening _ => pure ()
    | _ => throw (.invalidProgram "unreachable TCP listen state")
    if h.hostWindows && !value.bound then
      match ← h.hostBind value.socket (unspecified value.family) with
      | .error error => return .error (.host error)
      | .ok _ =>
        value := { value with bound := true }
        h.put fd value
    match ← h.hostListen value.socket backlog with
    | .error error => return .error (.host error)
    | .ok _ => pure ()
    value := { value with bound := true }
    h.put fd value
    if let .listening _ := value.socket then return .ok ()
    let .initial raw := value.socket | throw (.invalidProgram "unreachable listener transition")
    h.put fd { value with socket := .transition }
    let listener ← h.rawToListener raw
    h.put fd { value with socket := .listening listener, ready := {} }
    Readiness.updateFd h.wakeBudget h.io.readiness (← h.cloneFd fd) {}
    BlockingIo.register h.io (← h.cloneFd fd)
    return .ok ()
  ) (drop h fd)

/-- Consumes one owner, preserving source's single readiness-based connection
probe (no invented peer_addr probe and no spurious-wakeup retry). -/
def ensureConnected (h : Hooks S F R L T E P H) (fd : F) (deadline : Option ThreadDeadline)
    (name : String) (action : Bool → M S Unit) : M S Unit := do
  let state ← onError (h.get fd) (drop h fd)
  match state.socket with
  | .connected _ => Files.withDrop (action true) (drop h fd)
  | .connecting _ =>
    blockOwned h fd .write deadline fun reason => do
      BlockingIo.removeBlockedThread h.io (h.io.readiness.id fd) (← h.io.readiness.runtime.threads).activeThread
      if reason == .TimedOut then action false; return
      match (← h.get fd).socket with
      | .connected _ => action true
      | .connecting stream =>
        updateLastError h fd
        let value ← h.get fd
        if value.error.isSome then action false
        else
          h.put fd { value with socket := .transition }
          h.put fd { value with socket := .connected stream }
          action true
      | _ => ensureNotFailed h fd name; action false
  | _ => Files.withDrop (do ensureNotFailed h fd name; action false) (drop h fd)

private def tryAccept (h : Hooks S F R L T E P H) (fd : F) (nonblock : Bool) : M S (Files.Result E (Int32 × SocketAddress.Address)) := do
  let .listening listener := (← h.get fd).socket | throw (.invalidProgram "try_accept requires listening TCP socket")
  match ← h.hostAccept listener with
  | .error error =>
    if error.kind == .WouldBlock then
      let value ← h.get fd
      h.put fd { value with ready := { value.ready with readable := false } }
      Readiness.updateFd h.wakeBudget h.io.readiness (← h.cloneFd fd) {}
    return .error (.host error)
  | .ok (stream,address) =>
    let client ← h.newFd ⟨family address,.connected stream,nonblock,true,{},none,none,none⟩
    BlockingIo.register h.io (← h.cloneFd client)
    let number ← h.insert client
    return .ok (number,address)

private def trySendRecv (h : Hooks S F R L T E P H) (fd : F) (send : Bool)
    (pointer : Pointer (Option Provenance)) (length : Nat) (peek : Bool) : M S (Files.Result E Nat) := do
  let .connected stream := (← h.get fd).socket | throw (.invalidProgram "TCP nonblocking IO requires connected socket")
  let result : Files.Result E Nat ← if send then do
      let bytes ← h.readBytes pointer length
      if bytes.size != length then throw (.invalidProgram "TCP read buffer size mismatch")
      (h.hostSend stream bytes).map (Except.mapError .host)
    else do
      match ← h.hostRecv stream length peek with
      | .error error => pure (.error (.host error))
      | .ok bytes =>
        if bytes.size > length then throw (.invalidProgram "TCP host read exceeds buffer")
        h.writeBytes pointer bytes
        pure (.ok bytes.size)
  if send then
    if result.isOk then
      if (← h.get fd).ready.writeClosed then throw (.invalidProgram "successful TCP write after close")
  match result with
  | .error (.host error) =>
    if error.kind == .NotConnected || error.kind == .WouldBlock then
      let value ← h.get fd
      let ready := if send then { value.ready with writable := false } else { value.ready with readable := false }
      h.put fd { value with ready := ready }
      Readiness.updateFd h.wakeBudget h.io.readiness (← h.cloneFd fd) {}
      return .error (.host (← h.errors.hostFromKind .WouldBlock))
    return result
  | .ok count =>
    if send && count > length then throw (.invalidProgram "TCP host write exceeds buffer")
    let truncate ← if count >= length then pure false else if send then pure true
      else if peek || count == 0 then pure false else do pure (!(← h.get fd).ready.readClosed)
    if truncate then
      if h.hostEdgeBackend then
        let value ← h.get fd
        let ready := if send then { value.ready with writable := false } else { value.ready with readable := false }
        h.put fd { value with ready := ready }
        Readiness.updateFd h.wakeBudget h.io.readiness (← h.cloneFd fd) {}
      else Readiness.updateFd h.wakeBudget h.io.readiness (← h.cloneFd fd) { forceEdge := true }
    return result
  | _ => return result

private def wouldBlock : Files.Result E A → Bool
  | .error (.host error) => error.kind == .WouldBlock
  | _ => false
private def blockAccept (budget : Nat) (h : Hooks S F R L T E P H) (fd : F) (nonblock : Bool)
    (finish : Socket.Finish S E (Int32 × SocketAddress.Address)) : M S Unit := do
  match budget with
  | 0 => Files.withDrop (throw (.resourceExhaustion "TCP accept callback budget")) (drop h fd)
  | budget+1 => blockOwned h fd .read none fun reason => do
    BlockingIo.removeBlockedThread h.io (h.io.readiness.id fd) (← h.io.readiness.runtime.threads).activeThread
    if reason == .TimedOut then finish (.error (.libc "EWOULDBLOCK")); return
    let result ← tryAccept h fd nonblock
    if wouldBlock result then blockAccept budget h (← h.cloneFd fd) nonblock finish
    else finish result
private def blockSendRecv (budget : Nat) (h : Hooks S F R L T E P H) (fd : F)
    (send : Bool) (deadline : Option ThreadDeadline) (pointer : Pointer (Option Provenance))
    (length : Nat) (peek : Bool) (finish : Files.Finish S E) : M S Unit := do
  match budget with
  | 0 => Files.withDrop (throw (.resourceExhaustion "TCP IO callback budget")) (drop h fd)
  | budget+1 => blockOwned h fd (if send then .write else .read) deadline fun reason => do
    BlockingIo.removeBlockedThread h.io (h.io.readiness.id fd) (← h.io.readiness.runtime.threads).activeThread
    if reason == .TimedOut then finish (.error (.libc "EWOULDBLOCK")); return
    let result ← trySendRecv h fd send pointer length peek
    if wouldBlock result then blockSendRecv budget h (← h.cloneFd fd) send deadline pointer length peek finish
    else finish result

def accept (budget : Nat) (h : Hooks S F R L T E P H) (fd : F) (communicate nonblock : Bool)
    (finish : Socket.Finish S E (Int32 × SocketAddress.Address)) : M S Unit := do
  let state ← onError (do
    communicating communicate
    let value ← h.get fd
    let .listening _ := value.socket | throw (.unsupported "accept requires listening TCP socket")
    if !value.nonblock && value.readTimeout.isSome then throw (.unsupported "blocking TCP accept with SO_RCVTIMEO unsupported")
    pure value
  ) (drop h fd)
  if state.nonblock then Files.withDrop (finish (← tryAccept h fd nonblock)) (drop h fd)
  else blockAccept budget h fd nonblock finish

private def startConnect (h : Hooks S F R L T E P H) (fd : F) (communicate : Bool)
    (address : SocketAddress.Address) : M S (Option (Files.Result E Unit)) := do
  communicating communicate
  ensureNotFailed h fd "connect"
  let value ← h.get fd
  let raw ← match value.socket with
    | .initial raw => pure (some raw)
    | .listening _ => pure none
    | .connected _ => pure none
    | .connecting _ => pure none
    | _ => throw (.invalidProgram "unreachable TCP connect state")
  let some raw := raw | return some (.error (.libc (match value.socket with
    | .listening _ => if h.os == "linux" || h.os == "android" then "EISCONN" else "EOPNOTSUPP"
    | .connected _ => "EISCONN" | _ => "EALREADY")))
  let result ← h.hostConnect raw address
  let progress := match result with | .error error => error.kind == .WouldBlock || error.kind == .InProgress | _ => false
  if !progress then
    if let .error error := result then return some (.error (.host error))
  h.put fd { value with socket := .transition }
  let stream ← h.rawToStream raw
  h.put fd { value with socket := .connecting stream, bound := true, ready := {} }
  Readiness.updateFd h.wakeBudget h.io.readiness (← h.cloneFd fd) {}
  BlockingIo.register h.io (← h.cloneFd fd)
  if value.nonblock then return some (if progress then .error (.libc "EINPROGRESS") else .ok ())
  if value.writeTimeout.isSome then throw (.unsupported "blocking TCP connect with SO_SNDTIMEO unsupported")
  return none

def connect (h : Hooks S F R L T E P H) (fd : F) (communicate : Bool)
    (address : SocketAddress.Address) (finish : Socket.Finish S E Unit) : M S Unit := do
  let result ← onError (startConnect h fd communicate address) (drop h fd)
  if let some result := result then Files.withDrop (finish result) (drop h fd)
  else
    ownAction h fd (fun connected => do
      if connected then finish (.ok ())
      else
        let value ← h.get fd
        let some error := value.error | throw (.invalidProgram "connect completion missing stored error")
        h.put fd { value with error := none }
        finish (.error (.host error))
    ) fun action => do ensureConnected h (← h.cloneFd fd) none "connect" action

def sendRecv (budget : Nat) (h : Hooks S F R L T E P H) (fd : F) (communicate send : Bool)
    (pointer : Pointer (Option Provenance)) (length : Nat) (peek nonblock : Bool) (finish : Files.Finish S E) : M S Unit := do
  let (nonblock,deadline) ← onError (do
    communicating communicate
    let value ← h.get fd
    let nonblock := nonblock || value.nonblock
    let deadline ← actionDeadline h nonblock (if send then value.writeTimeout else value.readTimeout)
    pure (nonblock,deadline)
  ) (drop h fd)
  ownAction h fd (fun connected => do
    if !connected then finish (.error (.libc "ENOTCONN")); return
    if nonblock then finish (← trySendRecv h fd send pointer length peek)
    else blockSendRecv budget h (← h.cloneFd fd) send deadline pointer length peek finish
  ) fun action => do ensureConnected h (← h.cloneFd fd) deadline (if send then "send" else "recv") action

def localName (h : Hooks S F R L T E P H) (fd : F) (communicate : Bool) : M S (Files.Result E SocketAddress.Address) :=
  Files.withDrop (do
    communicating communicate
    ensureNotFailed h fd "getsockname"
    let value ← h.get fd
    if !value.bound then return .ok (unspecified value.family)
    validHost value.socket
    if h.hostWindows then
      if let .connecting _ := value.socket then h.connectingNameWarningOnce
    return (← h.hostLocal value.socket).mapError .host
  ) (drop h fd)

def peerName (h : Hooks S F R L T E P H) (fd : F) (communicate : Bool)
    (finish : Socket.Finish S E SocketAddress.Address) : M S Unit := do
  let deadline ← onError (do communicating communicate; h.deadline none) (drop h fd)
  ownAction h fd (fun connected => do
    if !connected then finish (.error (.libc "ENOTCONN")); return
    let .connected stream := (← h.get fd).socket | throw (.invalidProgram "getpeername expected connected stream")
    finish ((← h.hostPeer stream).mapError .host)
  ) fun action => do ensureConnected h (← h.cloneFd fd) (some deadline) "getpeername" action

def shutdown (h : Hooks S F R L T E P H) (fd : F) (communicate : Bool) (how : Socket.Shutdown) : M S (Files.Result E Unit) := do
  let result : Files.Result E Unit ← onError (do
    communicating communicate
    ensureNotFailed h fd "shutdown"
    let value ← h.get fd
    let stream := match value.socket with | .connecting stream | .connected stream => some stream | _ => none
    let some stream := stream | return .error (.libc "ENOTCONN")
    match ← h.hostShutdown stream how with
    | .error error => return .error (.host error)
    | .ok _ =>
      let current ← h.get fd
      let read := how == .read || how == .both
      let ready := { current.ready with readClosed := current.ready.readClosed || read, writeClosed := current.ready.writeClosed || how == .both, readable := current.ready.readable || read }
      h.put fd { current with ready := ready }
      return .ok ()
  ) (drop h fd)
  match result with
  | .error error => drop h fd; return .error error
  | .ok _ => Readiness.updateFd h.wakeBudget h.io.readiness fd {}; return .ok ()

def setTimeout (h : Hooks S F R L T E P H) (fd : F) (write : Bool) (timeout : Option Clock.Duration) : M S Unit := do
  let value ← h.get fd
  h.put fd (if write then { value with writeTimeout := timeout } else { value with readTimeout := timeout })
def getTimeout (h : Hooks S F R L T E P H) (fd : F) (write : Bool) : M S (Option Clock.Duration) := do
  let value ← h.get fd
  return if write then value.writeTimeout else value.readTimeout

def takeError (h : Hooks S F R L T E P H) (fd : F) : M S (Option (IoError.HostError E)) := do
  updateLastError h fd
  let value ← h.get fd
  h.put fd { value with error := none }
  let current ← h.get fd
  h.put fd { current with ready := { current.ready with error := false } }
  Readiness.updateFd h.wakeBudget h.io.readiness (← h.cloneFd fd) {}
  return value.error

/-- SourceFileDescription accepts only registered mio-backed socket states. -/
def sourceState (h : Hooks S F R L T E P H) (fd : F) : M S (SocketState R L T) := do
  let value ← h.get fd
  match value.socket with
  | .listening _ | .connecting _ | .connected _ | .failed _ => return value.socket
  | _ => throw (.invalidProgram "TCP source not backed by mio socket")

def getFlags (h : Hooks S F R L T E P H) (fd : F) (libcI32 : String → M S Int32) : M S Int32 := do
  let flags ← libcI32 "O_RDWR"
  if (← h.get fd).nonblock then return flags ||| (← libcI32 "O_NONBLOCK")
  return flags
def setFlags (h : Hooks S F R L T E P H) (fd : F) (libcI32 : String → M S Int32) (flags : Int32) : M S Int32 := do
  let bit ← libcI32 "O_NONBLOCK"
  let selected := flags &&& bit == bit
  h.put fd { (← h.get fd) with nonblock := selected }
  if (if selected then flags &&& ~~~bit else flags) != 0 then throw (.unsupported "TCP F_SETFL only supports O_NONBLOCK")
  return 0
def ioctl (h : Hooks S F R L T E P H) (fd : F) (communicate : Bool)
    (operation : Scalar Provenance) (libc : String → M S (Scalar Provenance))
    (readArgument : M S Int32) : M S Int32 := do
  communicating communicate
  if operation != (← libc "FIONBIO") then throw (.unsupported "unsupported TCP ioctl operation")
  if !(#["linux","android","macos","freebsd"].contains h.os) then throw (.unsupported "FIONBIO unsupported on target")
  let value ← readArgument
  h.put fd { (← h.get fd) with nonblock := value != 0 }
  return 0

def name : String := "socket"
def shortFdOperations : Bool := false
end Miri.Interpreter.TcpSocket
