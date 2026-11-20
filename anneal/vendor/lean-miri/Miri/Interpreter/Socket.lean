import Miri.Interpreter.SocketOptions
import Miri.Interpreter.OwnedSocketCompletion

/-! unix/socket.rs syscall protocol. Descriptor operations consume owned refs;
concrete TCP/virtual implementations provide real state transitions/callbacks. -/
namespace Miri.Interpreter.Socket
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
inductive Family where | ipv4 | ipv6 deriving DecidableEq, Repr
inductive Shutdown where | read | write | both deriving DecidableEq, Repr
abbrev Finish := OwnedSocketCompletion.Finish
structure Operations (S F E : Type) where
  bind : F → Bool → SocketAddress.Address → M S (Files.Result E Unit)
  listen : F → Bool → Int32 → M S (Files.Result E Unit)
  accept : F → Bool → Bool → Finish S E (Int32 × SocketAddress.Address) → M S Unit
  connect : F → Bool → SocketAddress.Address → Finish S E Unit → M S Unit
  send : F → Bool → Pointer (Option Provenance) → Nat → Bool → Finish S E Nat → M S Unit
  recv : F → Bool → Pointer (Option Provenance) → Nat → Bool → Bool → Finish S E Nat → M S Unit
  setOption : F → Int32 → Int32 → Pointer (Option Provenance) → UInt64 → M S (Files.Result E Unit)
  getOption : F → Int32 → Int32 → M S (Files.Result E (MPlaceTy Provenance))
  localName : F → Bool → M S (Files.Result E SocketAddress.Address)
  peerName : F → Bool → Finish S E SocketAddress.Address → M S Unit
  shutdown : F → Bool → Shutdown → M S (Files.Result E Unit)
structure Hooks (S F E I : Type) where
  address : SocketAddress.Hooks S E I
  operations : Operations S F E
  os : String
  communicate : Bool
  isolationReject : String → M S Bool
  readI32 : OpTy Provenance → M S Int32
  readSizeT : OpTy Provenance → M S Nat
  lookupFd : Int32 → M S (Option F)
  /-- as_unix then checked as_socket, preserving actual same owned description. -/
  asSocket : F → M S Bool
  dropFd : F → M S Unit
  newTcp : Family → Bool → M S (Except (IoError.HostError E) F)
  insert : F → M S Int32
  writeInt : Int → MPlaceTy Provenance → M S Unit
  readLengthPlace : MPlaceTy Provenance → M S Nat
private def onError (action : M S A) (cleanup : M S Unit) : M S A := fun state =>
  match action state with
  | .ok value state => .ok value state
  | .error error state => match cleanup state with
    | .ok _ state => .error error state | .error next state => .error next state
private def fail (h : Hooks S F E I) (name : String) : M S Int32 :=
  IoError.setErrnoAndReturnNeg1I32 h.address.errors (.libc name)
private def finishUnit (h : Hooks S F E I) (result : Files.Result E Unit) : M S Int32 := do
  match result with | .ok _ => return 0 | .error error => IoError.setErrnoAndReturnNeg1I32 h.address.errors error
private def fd (h : Hooks S F E I) (number : Int32) : M S (Files.Result E F) := do
  let some fd ← h.lookupFd number | return .error (.libc "EBADF")
  let socket ← onError (h.asSocket fd) (h.dropFd fd)
  if socket then return .ok fd
  h.dropFd fd
  return .error (.libc "ENOTSOCK")
private def extendedFlags (os : String) : Bool := #["linux","android","freebsd","solaris","illumos"].contains os
private def parseFlags (h : Hooks S F E I) (flags : Int32) : M S (Int32 × Bool) := do
  let mut flags := flags
  let mut nonblock := false
  if extendedFlags h.os then
    let bit ← h.address.libcI32 "SOCK_NONBLOCK"
    let cloexec ← h.address.libcI32 "SOCK_CLOEXEC"
    if flags &&& bit == bit then nonblock := true; flags := flags &&& ~~~bit
    if flags &&& cloexec == cloexec then flags := flags &&& ~~~cloexec
  return (flags,nonblock)

def create (h : Hooks S F E I) (domain kind protocol : OpTy Provenance) : M S Int32 := do
  let domain ← h.readI32 domain
  let flags ← h.readI32 kind
  let protocol ← h.readI32 protocol
  if ← h.isolationReject "`socket`" then return ← fail h "EACCES"
  let (flags,nonblock) ← parseFlags h flags
  let family ← if domain == (← h.address.libcI32 "AF_INET") then pure Family.ipv4
    else if domain == (← h.address.libcI32 "AF_INET6") then pure .ipv6 else throw (.unsupported "socket: only AF_INET/AF_INET6 allowed")
  if flags != (← h.address.libcI32 "SOCK_STREAM") then throw (.unsupported "socket: unsupported socket type")
  if protocol != 0 then
    if protocol != (← h.address.libcI32 "IPPROTO_TCP") then throw (.unsupported "socket: unsupported protocol")
  match ← h.newTcp family nonblock with
  | .error error => IoError.setErrnoAndReturnNeg1I32 h.address.errors (.host error)
  | .ok socket => h.insert socket

def bind (h : Hooks S F E I) (number address length : OpTy Provenance) : M S Int32 := do
  let number ← h.readI32 number
  let result ← SocketAddress.read h.address address length "bind"
  let .ok address := result | match result with | .error error => return ← IoError.setErrnoAndReturnNeg1I32 h.address.errors error | .ok _ => throw (.invalidProgram "address pattern")
  match ← fd h number with
  | .error error => IoError.setErrnoAndReturnNeg1I32 h.address.errors error
  | .ok socket => finishUnit h (← h.operations.bind socket h.communicate address)

def listen (h : Hooks S F E I) (number backlog : OpTy Provenance) : M S Int32 := do
  let number ← h.readI32 number
  let backlog ← h.readI32 backlog
  match ← fd h number with
  | .error error => IoError.setErrnoAndReturnNeg1I32 h.address.errors error
  | .ok socket => finishUnit h (← h.operations.listen socket h.communicate backlog)

def accept4 (h : Hooks S F E I) (number address length : OpTy Provenance) (flags : Option (OpTy Provenance)) (dest : MPlaceTy Provenance) : M S Unit := do
  let number ← h.readI32 number
  let address ← h.address.readPointer address
  let length ← h.address.readPointer length
  let flags ← match flags with | none => pure 0 | some value => h.readI32 value
  match ← fd h number with
  | .error error => IoError.setErrnoAndReturnNeg1 h.address.errors error dest
  | .ok socket =>
    let nonblock ← onError (do
      let (flags,nonblock) ← parseFlags h flags
      if flags != 0 then throw (.unsupported "accept4: unsupported flags")
      pure nonblock
    ) (h.dropFd socket)
    h.operations.accept socket h.communicate nonblock (OwnedSocketCompletion.Finish.source (.accept ⟨address,length,dest⟩) fun result => do
      match result with
      | .error error => IoError.setErrnoAndReturnNeg1 h.address.errors error dest
      | .ok (number,value) =>
        if !h.address.isLiteralNull address then SocketAddress.write h.address value address length "accept4"
        h.writeInt number.toInt dest)

def connect (h : Hooks S F E I) (number address length : OpTy Provenance) (dest : MPlaceTy Provenance) : M S Unit := do
  let number ← h.readI32 number
  match ← SocketAddress.read h.address address length "connect" with
  | .error error => IoError.setErrnoAndReturnNeg1 h.address.errors error dest
  | .ok address =>
    match ← fd h number with
    | .error error => IoError.setErrnoAndReturnNeg1 h.address.errors error dest
    | .ok socket => h.operations.connect socket h.communicate address (OwnedSocketCompletion.Finish.source (.connect ⟨dest⟩) fun result => do
      match result with | .ok _ => h.writeInt 0 dest | .error error => IoError.setErrnoAndReturnNeg1 h.address.errors error dest)

def sendRecv (h : Hooks S F E I) (send : Bool) (number buffer length flags : OpTy Provenance) (dest : MPlaceTy Provenance) : M S Unit := do
  let number ← h.readI32 number
  let pointer ← h.address.readPointer buffer
  let length ← h.readSizeT length
  let flags ← h.readI32 flags
  match ← fd h number with
  | .error error => IoError.setErrnoAndReturnNeg1 h.address.errors error dest
  | .ok socket =>
    let (nonblock,peek) ← onError (do
      let mut flags := flags
      let mut peek := false
      let mut nonblock := false
      if send then
        if extendedFlags h.os then
          let nosignal ← h.address.libcI32 "MSG_NOSIGNAL"
          let dontwait ← h.address.libcI32 "MSG_DONTWAIT"
          if flags &&& nosignal == nosignal then flags := flags &&& ~~~nosignal
          if flags &&& dontwait == dontwait then flags := flags &&& ~~~dontwait; nonblock := true
      else
        let bit ← h.address.libcI32 "MSG_PEEK"
        if flags &&& bit == bit then peek := true; flags := flags &&& ~~~bit
        if #["linux","android","freebsd","illumos"].contains h.os then
          let bit ← h.address.libcI32 "MSG_CMSG_CLOEXEC"
          if flags &&& bit == bit then flags := flags &&& ~~~bit
        if extendedFlags h.os then
          let bit ← h.address.libcI32 "MSG_DONTWAIT"
          if flags &&& bit == bit then flags := flags &&& ~~~bit; nonblock := true
      if flags != 0 then throw (.unsupported "unsupported send/recv flags")
      pure (nonblock,peek)
    ) (h.dropFd socket)
    let finish : Finish S E Nat := OwnedSocketCompletion.Finish.source (.bytes (.socket dest)) fun result => do
      match result with | .ok count => h.writeInt count dest | .error error => IoError.setErrnoAndReturnNeg1 h.address.errors error dest
    if send then h.operations.send socket h.communicate pointer length nonblock finish
    else h.operations.recv socket h.communicate pointer length peek nonblock finish

def setOption (h : Hooks S F E I) (number level option value length : OpTy Provenance) : M S Int32 := do
  let number ← h.readI32 number
  let level ← h.readI32 level
  let option ← h.readI32 option
  let value ← h.address.readPointer value
  let length ← h.address.readSocklen length
  match ← fd h number with
  | .error error => IoError.setErrnoAndReturnNeg1I32 h.address.errors error
  | .ok socket => finishUnit h (← h.operations.setOption socket level option value length)

def getOption (h : Hooks S F E I) (number level option value length : OpTy Provenance) : M S Int32 := do
  let number ← h.readI32 number
  let level ← h.readI32 level
  let option ← h.readI32 option
  let value ← h.address.readPointer value
  let length ← h.address.readPointer length
  match ← fd h number with
  | .error error => IoError.setErrnoAndReturnNeg1I32 h.address.errors error
  | .ok socket =>
    let input ← onError (do
      if h.address.isLiteralNull value || h.address.isLiteralNull length then pure none
      else
        let place := h.address.ptrToPlace length (← h.address.layout "socklen_t")
        pure (some (place,← h.readLengthPlace place))
    ) (h.dropFd socket)
    let some (lengthPlace,length) := input | h.dropFd socket; return ← fail h "EFAULT"
    match ← h.operations.getOption socket level option with
    | .error error => IoError.setErrnoAndReturnNeg1I32 h.address.errors error
    | .ok buffer =>
      let count := min buffer.layout.layout.size.bytes.toNat length
      h.address.memCopy (h.address.pointer buffer) value (Size.ofBytes (UInt64.ofNat count)) true
      h.address.deallocate (h.address.pointer buffer) .stack
      h.address.writeInt count lengthPlace
      return 0

def localName (h : Hooks S F E I) (number address length : OpTy Provenance) : M S Int32 := do
  let number ← h.readI32 number
  let address ← h.address.readPointer address
  let length ← h.address.readPointer length
  match ← fd h number with
  | .error error => IoError.setErrnoAndReturnNeg1I32 h.address.errors error
  | .ok socket =>
    match ← h.operations.localName socket h.communicate with
    | .error error => IoError.setErrnoAndReturnNeg1I32 h.address.errors error
    | .ok result => SocketAddress.write h.address result address length "getsockname"; return 0

def peerName (h : Hooks S F E I) (number address length : OpTy Provenance) (dest : MPlaceTy Provenance) : M S Unit := do
  let number ← h.readI32 number
  let address ← h.address.readPointer address
  let length ← h.address.readPointer length
  match ← fd h number with
  | .error error => IoError.setErrnoAndReturnNeg1 h.address.errors error dest
  | .ok socket => h.operations.peerName socket h.communicate (OwnedSocketCompletion.Finish.source (.peer ⟨address,length,dest⟩) fun result => do
    match result with
    | .error error => IoError.setErrnoAndReturnNeg1 h.address.errors error dest
    | .ok result =>
      SocketAddress.write h.address result address length "getpeername"
      h.writeInt 0 dest)

def shutdown (h : Hooks S F E I) (number how : OpTy Provenance) : M S Int32 := do
  let number ← h.readI32 number
  let how ← h.readI32 how
  match ← fd h number with
  | .error error => IoError.setErrnoAndReturnNeg1I32 h.address.errors error
  | .ok socket =>
    let selected ← onError (do
      let read ← h.address.libcI32 "SHUT_RD"
      let write ← h.address.libcI32 "SHUT_WR"
      let both ← h.address.libcI32 "SHUT_RDWR"
      pure (if how == read then some Shutdown.read else if how == write then some .write else if how == both then some .both else none)
    ) (h.dropFd socket)
    let some selected := selected | h.dropFd socket; return ← fail h "EINVAL"
    finishUnit h (← h.operations.shutdown socket h.communicate selected)

/-- Trait default implementations reject every operation. In particular a
virtual socket does not inherit successful TCP options, bind or shutdown. -/
def unsupportedOperations (drop : F → M S Unit) : Operations S F E where
  bind := fun fd _ _ => Files.withDrop (throw (.unsupported "cannot bind socket type")) (drop fd)
  listen := fun fd _ _ => Files.withDrop (throw (.unsupported "cannot listen on socket type")) (drop fd)
  accept := fun fd _ _ _ => Files.withDrop (throw (.unsupported "cannot accept socket type")) (drop fd)
  connect := fun fd _ _ _ => Files.withDrop (throw (.unsupported "cannot connect socket type")) (drop fd)
  send := fun fd _ _ _ _ _ => Files.withDrop (throw (.unsupported "cannot send socket type")) (drop fd)
  recv := fun fd _ _ _ _ _ _ => Files.withDrop (throw (.unsupported "cannot receive socket type")) (drop fd)
  setOption := fun fd _ _ _ _ => Files.withDrop (throw (.unsupported "cannot set option on socket type")) (drop fd)
  getOption := fun fd _ _ => Files.withDrop (throw (.unsupported "cannot get option on socket type")) (drop fd)
  localName := fun fd _ => Files.withDrop (throw (.unsupported "cannot get local socket name")) (drop fd)
  peerName := fun fd _ _ => Files.withDrop (throw (.unsupported "cannot get peer socket name")) (drop fd)
  shutdown := fun fd _ _ => Files.withDrop (throw (.unsupported "cannot shutdown socket type")) (drop fd)
end Miri.Interpreter.Socket
