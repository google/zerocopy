import Miri.Interpreter.OwnedSocketMachine
import Miri.Interpreter.SocketMachine

/-! Actual source socket/FileDescription operation selection. Transient finish
functions never enter storage; exact data environments select the portable
source callback interpreter. Generic option ownership uses the same typed arena. -/
namespace Miri.Interpreter.OwnedSocketOperations
open Miri.ABI Miri.Memory Miri.Concurrency
abbrev State := TypedSyncMachine.State
abbrev M := TypedSyncMachine.M
private def onError (action : M K U A) (cleanup : M K U Unit) : M K U A := fun state =>
  match action state with
  | .ok value state => .ok value state
  | .error error state => match cleanup state with
    | .ok _ state => .error error state | .error next state => .error next state
private def missing (drop : M K U Unit) : M K U A :=
  Files.withDrop (throw (.callback "socket operation requires its source finish environment")) drop
private def release (v : OwnedSocketMachine.Views U F) (tcp : TcpSocket.Hooks (State K U) F R L T E P H) (token : Nat) : M K U Unit := do
  let some _ ← OwnedSocketMachine.lookup v token | return
  let .owner fd ← OwnedSocketMachine.take v token | throw (.invalidProgram "socket option owner token has wrong kind")
  tcp.io.readiness.dropFd fd
private def withOwner (v : OwnedSocketMachine.Views U F) (tcp : TcpSocket.Hooks (State K U) F R L T E P H)
    (options : SocketOptions.Hooks (State K U) F E I) (fd : F)
    (action : SocketOptions.Hooks (State K U) F E I → M K U A) : M K U A := do
  let token ← onError (OwnedSocketMachine.register v (.owner fd)) (tcp.io.readiness.dropFd fd)
  let release := release v tcp token
  let options := {options with
    setTimeout := fun socket write timeout => do options.setTimeout socket write timeout; release
    getTimeout := fun socket write => do let value ← options.getTimeout socket write; release; pure value
    takeError := fun socket => do let value ← options.takeError socket; release; pure value}
  Files.withDrop (action options) release

def operations
    (v : OwnedSocketMachine.Views U (Files.Ref (Files.Description FH D O)))
    (descriptor : SocketMachine.Descriptor O)
    (virt : OwnedVirtualSocket.Hooks (State K U) (Files.Ref (Files.Description FH D O)) E I)
    (tcp : OwnedTcpSocket.Hooks (State K U) (Files.Ref (Files.Description FH D O)) R L T E P H I)
    (options : SocketOptions.Hooks (State K U) (Files.Ref (Files.Description FH D O)) E I)
    (resource : Nat) : Socket.Operations (State K U) (Files.Ref (Files.Description FH D O)) E :=
  let source := tcp.source
  let defaults := Socket.unsupportedOperations virt.source.readiness.dropFd
  {bind := fun fd communicate addr => if SocketMachine.kind descriptor fd == some .tcp then TcpSocket.bind source fd communicate addr else defaults.bind fd communicate addr
   listen := fun fd communicate backlog => if SocketMachine.kind descriptor fd == some .tcp then TcpSocket.listen source fd communicate backlog else defaults.listen fd communicate backlog
   accept := fun fd communicate nonblock finish => do
    if SocketMachine.kind descriptor fd != some .tcp then
      defaults.accept fd communicate nonblock finish
      return
    let some (.accept capture) := finish.capture | missing (source.io.readiness.dropFd fd)
    OwnedTcpSocket.accept resource tcp fd communicate nonblock capture
   connect := fun fd communicate addr finish => do
    if SocketMachine.kind descriptor fd != some .tcp then
      defaults.connect fd communicate addr finish
      return
    let some (.connect capture) := finish.capture | missing (source.io.readiness.dropFd fd)
    OwnedTcpSocket.connect resource tcp fd communicate addr capture
   send := fun fd communicate pointer length nonblock finish => do
    if (SocketMachine.kind descriptor fd).isNone then
      defaults.send fd communicate pointer length nonblock finish
      return
    let some (.bytes capture) := finish.capture | missing (source.io.readiness.dropFd fd)
    match SocketMachine.kind descriptor fd with
    | some .tcp => OwnedTcpSocket.sendRecv resource tcp fd communicate true pointer length false nonblock capture
    | some .virtual => OwnedVirtualSocket.write virt fd pointer length nonblock capture
    | none => defaults.send fd communicate pointer length nonblock finish
   recv := fun fd communicate pointer length peek nonblock finish => do
    if (SocketMachine.kind descriptor fd).isNone then
      defaults.recv fd communicate pointer length peek nonblock finish
      return
    let some (.bytes capture) := finish.capture | missing (source.io.readiness.dropFd fd)
    match SocketMachine.kind descriptor fd with
    | some .tcp => OwnedTcpSocket.sendRecv resource tcp fd communicate false pointer length peek nonblock capture
    | some .virtual =>
      if peek then Files.withDrop (throw (.unsupported "socketpair peeking unsupported")) (virt.source.readiness.dropFd fd)
      else OwnedVirtualSocket.read virt fd pointer length nonblock capture
    | none => defaults.recv fd communicate pointer length peek nonblock finish
   setOption := fun fd level option ptr length => do
    if SocketMachine.kind descriptor fd != some .tcp then return ← defaults.setOption fd level option ptr length
    withOwner v source options fd fun options => do
      if level == (← options.address.libcI32 "SOL_SOCKET") then SocketOptions.setGeneric options fd option ptr length
      else if level == (← options.address.libcI32 "IPPROTO_IP") then SocketOptions.setIp options fd option ptr length
      else if level == (← options.address.libcI32 "IPPROTO_TCP") then SocketOptions.setTcp options fd option ptr length
      else throw (.unsupported "setsockopt: unsupported level")
   getOption := fun fd level option => do
    if SocketMachine.kind descriptor fd != some .tcp then return ← defaults.getOption fd level option
    withOwner v source options fd fun options => do
      if level == (← options.address.libcI32 "SOL_SOCKET") then SocketOptions.getGeneric options fd option
      else if level == (← options.address.libcI32 "IPPROTO_IP") then SocketOptions.getIp options fd option
      else if level == (← options.address.libcI32 "IPPROTO_TCP") then SocketOptions.getTcp options fd option
      else throw (.unsupported "getsockopt: unsupported level")
   localName := fun fd communicate => if SocketMachine.kind descriptor fd == some .tcp then TcpSocket.localName source fd communicate else defaults.localName fd communicate
   peerName := fun fd communicate finish => do
    if SocketMachine.kind descriptor fd != some .tcp then
      defaults.peerName fd communicate finish
      return
    let some (.peer capture) := finish.capture | missing (source.io.readiness.dropFd fd)
    OwnedTcpSocket.peerName resource tcp fd communicate capture
   shutdown := fun fd communicate how => if SocketMachine.kind descriptor fd == some .tcp then TcpSocket.shutdown source fd communicate how else defaults.shutdown fd communicate how}

def files
    (descriptor : SocketMachine.Descriptor O)
    (virt : OwnedVirtualSocket.Hooks (State K U) (Files.Ref (Files.Description FH D O)) E I)
    (tcp : OwnedTcpSocket.Hooks (State K U) (Files.Ref (Files.Description FH D O)) R L T E P H I)
    (resource : Nat) (base : Files.Hooks (State K U) FH D O E Meta) : Files.Hooks (State K U) FH D O E Meta :=
  let legacyShape := SocketMachine.bindFiles 0 descriptor virt.source tcp.source base
  {legacyShape with
   otherRead := fun fd communicate pointer length finish => do
    match SocketMachine.kind descriptor fd with
    | none => base.otherRead fd communicate pointer length finish
    | some kind =>
      let some capture := finish.capture | missing (virt.source.readiness.dropFd fd)
      match kind with
      | .virtual => OwnedVirtualSocket.read virt fd pointer length false (.file capture)
      | .tcp => OwnedTcpSocket.sendRecv resource tcp fd communicate false pointer length false false (.file capture)
   otherWrite := fun fd communicate pointer length finish => do
    match SocketMachine.kind descriptor fd with
    | none => base.otherWrite fd communicate pointer length finish
    | some kind =>
      let some capture := finish.capture | missing (virt.source.readiness.dropFd fd)
      match kind with
      | .virtual => OwnedVirtualSocket.write virt fd pointer length false (.file capture)
      | .tcp => OwnedTcpSocket.sendRecv resource tcp fd communicate true pointer length false false (.file capture)}
end Miri.Interpreter.OwnedSocketOperations
