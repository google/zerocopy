import Miri.Interpreter.TcpSocket
import Miri.Interpreter.OwnedSocketCompletion
import Miri.Interpreter.OwnedBlockingIo

/-! Source tcp_socket.rs typed connect/send/receive/accept/peer callbacks. Host
socket effects remain the exact typed source leaves in TcpSocket.Hooks. Callback
data, ownership, retries, clock/readiness/order policy execute here. -/
namespace Miri.Interpreter.OwnedTcpSocket
open Miri.ABI Miri.Memory Miri.Concurrency
open TcpSocket (SocketState)
abbrev M := EStateM StepError
inductive Action (F : Type) where
  | connect (fd : F) (finish : OwnedSocketCompletion.Connect)
  | io (fd : F) (send : Bool) (deadline : Option ThreadDeadline)
      (pointer : Pointer (Option Provenance)) (length : Nat) (peek nonblock : Bool) (finish : OwnedSocketCompletion.Bytes)
  | peer (fd : F) (finish : OwnedSocketCompletion.Peer)
inductive Capture (F : Type) where
  | accept (fd : F) (nonblock : Bool) (finish : OwnedSocketCompletion.Accept)
  | io (fd : F) (send : Bool) (deadline : Option ThreadDeadline)
      (pointer : Pointer (Option Provenance)) (length : Nat) (peek : Bool) (finish : OwnedSocketCompletion.Bytes)
  | ensure (fd : F) (name : String) (action : Action F)
structure Hooks (S F R L T E P H I : Type) where
  source : TcpSocket.Hooks S F R L T E P H
  completion : OwnedSocketCompletion.Hooks S E I
  register : Capture F → M S Nat
  take : Nat → M S (Capture F)
private def drop (h : TcpSocket.Hooks S F R L T E P H) := h.io.readiness.dropFd
private def onError (action : M S A) (cleanup : M S Unit) : M S A := fun state =>
  match action state with
  | .ok value state => .ok value state
  | .error error state => match cleanup state with
    | .ok _ state => .error error state | .error next state => .error next state
private def communicating (enabled : Bool) : M S Unit := do
  if !enabled then throw (.invalidProgram "cannot have TcpSocket under isolation")
private def validHost : SocketState R L T → M S Unit
  | .transition => throw (.invalidProgram "TCP host socket observed during transition")
  | _ => pure ()
private def family : SocketAddress.Address → Socket.Family
  | .v4 .. => .ipv4 | .v6 .. => .ipv6
private def unspecified : Socket.Family → SocketAddress.Address
  | .ipv4 => .v4 0 0 | .ipv6 => .v6 0 0 0 0

private def tryAccept (h : TcpSocket.Hooks S F R L T E P H) (fd : F) (nonblock : Bool) : M S (Files.Result E (Int32 × SocketAddress.Address)) := do
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

private def trySendRecv (h : TcpSocket.Hooks S F R L T E P H) (fd : F) (send : Bool)
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
private def startConnect (h : TcpSocket.Hooks S F R L T E P H) (fd : F) (communicate : Bool)
    (address : SocketAddress.Address) : M S (Option (Files.Result E Unit)) := do
  communicating communicate
  TcpSocket.ensureNotFailed h fd "connect"
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

def dropAction (h : Hooks S F R L T E P H I) : Action F → M S Unit
  | .connect fd _ | .io fd .. | .peer fd _ => drop h.source fd
def dropCapture (h : Hooks S F R L T E P H I) : Capture F → M S Unit
  | .accept fd .. | .io fd .. => drop h.source fd
  | .ensure fd _ action => do drop h.source fd; dropAction h action
private def descriptor : Capture F → F
  | .accept fd .. | .io fd .. | .ensure fd .. => fd
private def waiter (h : Hooks S F R L T E P H I) : OwnedBlockingIo.Hooks S F (Capture F) P H :=
  ⟨h.source.io,h.register,h.take,dropCapture h⟩
private def probe (h : TcpSocket.Hooks S F R L T E P H) (fd : F) (name : String) : M S Bool := do
  match (← h.get fd).socket with
  | .connected _ => pure true
  | .connecting stream =>
    TcpSocket.updateLastError h fd
    let state ← h.get fd
    if state.error.isSome then pure false
    else
      h.put fd {state with socket := .transition}
      h.put fd {state with socket := .connected stream}
      pure true
  | _ => TcpSocket.ensureNotFailed h fd name; pure false

/- The resource counts synchronous Rust callback nesting, including immediate
host readiness; no budget is stored in deferred captures. Each permitted queued
callback resumes with a fresh execution resource. Exhaustion is visible Unknown,
never successful IO or a claim that an infinite source retry terminates. -/
mutual
  def invoke : Nat → Hooks S F R L T E P H I → Capture F → UnblockKind → M S Unit
    | 0,h,capture,_ => Files.withDrop (throw (.resourceExhaustion "synchronous owned TCP callback resource")) (dropCapture h capture)
    | fuel+1,h,capture,reason => do
      let source := h.source
      let fd := descriptor capture
      onError (BlockingIo.removeBlockedThread source.io (source.io.readiness.id fd) (← source.io.readiness.runtime.threads).activeThread)
        (dropCapture h capture)
      match capture with
      | .ensure fd name action =>
        let connected ← onError (if reason == .TimedOut then pure false else probe source fd name) (dropCapture h capture)
        Files.withDrop (runAction fuel h action connected) (drop source fd)
      | .accept fd nonblock finish =>
        if reason == .TimedOut then
          Files.withDrop (OwnedSocketCompletion.accept h.completion finish (.error (.libc "EWOULDBLOCK"))) (drop source fd)
        else
          let result ← onError (tryAccept source fd nonblock) (drop source fd)
          if wouldBlock result then wait fuel h capture .read none
          else Files.withDrop (OwnedSocketCompletion.accept h.completion finish result) (drop source fd)
      | .io fd send deadline ptr length peek finish =>
        if reason == .TimedOut then
          Files.withDrop (OwnedSocketCompletion.bytes h.completion finish (.error (.libc "EWOULDBLOCK"))) (drop source fd)
        else
          let result ← onError (trySendRecv source fd send ptr length peek) (drop source fd)
          if wouldBlock result then wait fuel h capture (if send then .write else .read) deadline
          else Files.withDrop (OwnedSocketCompletion.bytes h.completion finish result) (drop source fd)
  def wait : Nat → Hooks S F R L T E P H I → Capture F → BlockingIo.Interest → Option ThreadDeadline → M S Unit
    | 0,h,capture,_,_ => Files.withDrop (throw (.resourceExhaustion "synchronous owned TCP wait resource")) (dropCapture h capture)
    | fuel+1,h,capture,interest,deadline => do
      let fd ← onError (h.source.cloneFd (descriptor capture)) (dropCapture h capture)
      OwnedBlockingIo.block (waiter h) fd interest deadline capture (invoke fuel h)
  def runAction : Nat → Hooks S F R L T E P H I → Action F → Bool → M S Unit
    | 0,h,action,_ => Files.withDrop (throw (.resourceExhaustion "synchronous owned TCP action resource")) (dropAction h action)
    | fuel+1,h,action,connected => do
      let source := h.source
      match action with
      | .connect fd finish => Files.withDrop (do
        if connected then OwnedSocketCompletion.connect h.completion finish (.ok ())
        else
          let value ← source.get fd
          let some error := value.error | throw (.invalidProgram "connect completion missing stored error")
          source.put fd {value with error := none}
          OwnedSocketCompletion.connect h.completion finish (.error (.host error))) (drop source fd)
      | .peer fd finish => Files.withDrop (do
        if !connected then
          OwnedSocketCompletion.peer h.completion finish (.error (.libc "ENOTCONN"))
          return
        let .connected stream := (← source.get fd).socket | throw (.invalidProgram "getpeername expected connected stream")
        OwnedSocketCompletion.peer h.completion finish ((← source.hostPeer stream).mapError .host)) (drop source fd)
      | .io fd send deadline ptr length peek nonblock finish =>
        if !connected then Files.withDrop (OwnedSocketCompletion.bytes h.completion finish (.error (.libc "ENOTCONN"))) (drop source fd)
        else if nonblock then Files.withDrop (do
          OwnedSocketCompletion.bytes h.completion finish (← trySendRecv source fd send ptr length peek)) (drop source fd)
        else wait fuel h (.io fd send deadline ptr length peek finish) (if send then .write else .read) deadline
  def ensure : Nat → Hooks S F R L T E P H I → F → Option ThreadDeadline → String → Action F → M S Unit
    | 0,h,fd,_,_,action => Files.withDrop (throw (.resourceExhaustion "synchronous owned TCP ensure resource")) (do drop h.source fd; dropAction h action)
    | fuel+1,h,fd,deadline,name,action => do
      let value ← onError (h.source.get fd) (do drop h.source fd; dropAction h action)
      match value.socket with
      | .connected _ => Files.withDrop (runAction fuel h action true) (drop h.source fd)
      | .connecting _ => wait fuel h (.ensure fd name action) .write deadline
      | _ =>
        onError (TcpSocket.ensureNotFailed h.source fd name) (do drop h.source fd; dropAction h action)
        Files.withDrop (runAction fuel h action false) (drop h.source fd)
end

def accept (fuel : Nat) (h : Hooks S F R L T E P H I) (fd : F) (communicate nonblock : Bool)
    (finish : OwnedSocketCompletion.Accept) : M S Unit := do
  let source := h.source
  let state ← onError (do
    communicating communicate
    let value ← source.get fd
    let .listening _ := value.socket | throw (.unsupported "accept requires listening TCP socket")
    if !value.nonblock && value.readTimeout.isSome then throw (.unsupported "blocking TCP accept with SO_RCVTIMEO unsupported")
    pure value) (drop source fd)
  if state.nonblock then Files.withDrop (do OwnedSocketCompletion.accept h.completion finish (← tryAccept source fd nonblock)) (drop source fd)
  else wait fuel h (.accept fd nonblock finish) .read none

def connect (fuel : Nat) (h : Hooks S F R L T E P H I) (fd : F) (communicate : Bool)
    (address : SocketAddress.Address) (finish : OwnedSocketCompletion.Connect) : M S Unit := do
  let result ← onError (startConnect h.source fd communicate address) (drop h.source fd)
  if let some result := result then Files.withDrop (OwnedSocketCompletion.connect h.completion finish result) (drop h.source fd)
  else
    let clone ← onError (h.source.cloneFd fd) (drop h.source fd)
    ensure fuel h clone none "connect" (.connect fd finish)

def sendRecv (fuel : Nat) (h : Hooks S F R L T E P H I) (fd : F) (communicate send : Bool)
    (ptr : Pointer (Option Provenance)) (length : Nat) (peek nonblock : Bool) (finish : OwnedSocketCompletion.Bytes) : M S Unit := do
  let (nonblock,deadline) ← onError (do
    communicating communicate
    let value ← h.source.get fd
    let nonblock := nonblock || value.nonblock
    let deadline ← TcpSocket.actionDeadline h.source nonblock (if send then value.writeTimeout else value.readTimeout)
    pure (nonblock,deadline)) (drop h.source fd)
  let clone ← onError (h.source.cloneFd fd) (drop h.source fd)
  ensure fuel h clone deadline (if send then "send" else "recv") (.io fd send deadline ptr length peek nonblock finish)

def peerName (fuel : Nat) (h : Hooks S F R L T E P H I) (fd : F) (communicate : Bool)
    (finish : OwnedSocketCompletion.Peer) : M S Unit := do
  let deadline ← onError (do communicating communicate; h.source.deadline none) (drop h.source fd)
  let clone ← onError (h.source.cloneFd fd) (drop h.source fd)
  ensure fuel h clone (some deadline) "getpeername" (.peer fd finish)
end Miri.Interpreter.OwnedTcpSocket
