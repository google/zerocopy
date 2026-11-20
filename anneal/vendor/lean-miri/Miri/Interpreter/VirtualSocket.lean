import Miri.Interpreter.Readiness

/-! Pinned unix/virtual_socket.rs owned virtual socketpair/pipe protocol. No
host network substitutes these source-local buffers. -/
namespace Miri.Interpreter.VirtualSocket
open Miri.ABI Miri.Memory Miri.Concurrency
abbrev M := EStateM StepError
def capacity : Nat := 0x34000
inductive SocketType where | socketpair | pipeRead | pipeWrite deriving DecidableEq, Repr
structure Buffer where
  bytes : ByteArray := ByteArray.empty
  clock : VClock := .default
structure State where
  readbuf : Option Buffer
  peer : Option Files.WeakRef := none
  peerLostData : Bool := false
  blockedRead : Array ThreadId := #[]
  blockedWrite : Array ThreadId := #[]
  nonblock : Bool
  kind : SocketType
structure Hooks (S F E : Type) where
  readiness : Readiness.Hooks S F
  get : F → M S State
  put : F → State → M S Unit
  newSocket : State → M S F
  insert : F → M S Int32
  readBytes : Pointer (Option Provenance) → Nat → M S ByteArray
  writeBytes : Pointer (Option Provenance) → ByteArray → M S Unit
  libc : String → M S (Scalar Provenance)
  libcI32 : String → M S Int32
  errors : IoError.Hooks S E
  os : String
  readI32 : OpTy Provenance → M S Int32
  derefI32 : OpTy Provenance → M S (MPlaceTy Provenance)
  nextI32 : MPlaceTy Provenance → M S (MPlaceTy Provenance)
  readFieldI32 : MPlaceTy Provenance → M S Int32
  writeInt : Int → MPlaceTy Provenance → M S Unit
  readIoctlArgument : M S (OpTy Provenance)
  wakeBudget : Nat
private def onError (action : M S A) (cleanup : M S Unit) : M S A := fun state =>
  match action state with
  | .ok value state => .ok value state
  | .error error state => match cleanup state with
    | .ok _ state => .error error state | .error next state => .error next state
private def lift (value : Except StepError A) : M S A :=
  match value with | .ok value => pure value | .error error => throw error
private def peer (value : State) : M S Files.WeakRef :=
  match value.peer with | some value => pure value | none => throw (.invalidProgram "virtual socket peer OnceCell uninitialized")
private def clockAcquire (h : Hooks S F E) (clock : VClock) : M S Unit := do
  let runtime := h.readiness.runtime
  match runtime.handler with
  | .none => pure ()
  | .vectorClocks =>
    match SyncClockState.acquire (← runtime.global) (← runtime.threads) clock with
    | .ok global => runtime.putGlobal global
    | .error error => throw (runtime.error (SyncError.ofClock error))
private def clockRelease (h : Hooks S F E) (clock : VClock) (put : VClock → M S Unit) : M S Unit := do
  let runtime := h.readiness.runtime
  match runtime.handler with
  | .none => pure ()
  | .vectorClocks =>
    match SyncClockState.prepareRelease (← runtime.global) (← runtime.threads) with
    | .error error => throw (runtime.error (SyncError.ofClock error))
    | .ok (snapshot,finish) =>
      put (clock.join snapshot)
      match finish with
      | .error error => throw (runtime.error (SyncError.ofClock error))
      | .ok global => runtime.putGlobal global

private def block (h : Hooks S F E) (callback : SyncRuntime.Callback S) : M S Unit := do
  let runtime := h.readiness.runtime
  let (registry,token) := (← runtime.callbacks).register callback
  runtime.putCallbacks registry
  match (← runtime.threads).blockThreadWithRuntimeConstraints .VirtualSocket none token runtime.communicate with
  | .ok threads => runtime.putThreads threads
  | .error error => SyncRuntime.cancelCallback runtime token; throw (runtime.error (.blockThreadSource error))

def name (value : State) : String := if value.kind == .socketpair then "socketpair" else "pipe"
def metadata (value : State) : String := if value.kind == .socketpair then "S_IFSOCK" else "S_IFIFO"
def asSocket (value : State) : Bool := value.kind == .socketpair

def readiness (h : Hooks S F E) (socket : F) : M S Files.Readiness := do
  let value ← h.get socket
  let ready : Files.Readiness := { readable := value.readbuf.all (·.bytes.isEmpty == false) }
  -- Option.all is true for the writing end with no read buffer, as source.
  match ← h.readiness.upgrade (← peer value) with
  | none => return { ready with readable := true, writable := true, readClosed := true, writeClosed := true, error := value.peerLostData }
  | some other =>
    Files.withDrop (do
      let otherValue ← h.get other
      match otherValue.readbuf with
      | none => pure { ready with writable := true }
      | some buffer =>
        if buffer.bytes.size > capacity then throw (.invalidProgram "virtual buffer capacity strict_sub underflow")
        pure { ready with writable := buffer.bytes.size < capacity }
    ) (h.readiness.dropFd other)

/-- Called by actual last-FD drop before dropping its ReadinessWatched field. -/
def dropSocket (h : Hooks S F E) (value : State) : M S Unit := do
  if let some other ← h.readiness.upgrade (← peer value) then
    onError (do
      if value.readbuf.any (fun buffer => !buffer.bytes.isEmpty) then
        let current ← h.get other
        h.put other { current with peerLostData := true }
    ) (h.readiness.dropFd other)
    Readiness.addDelayed h.readiness other

def getFlags (h : Hooks S F E) (socket : F) : M S Int32 := do
  let value ← h.get socket
  let flags ← h.libcI32 (match value.kind with | .socketpair => "O_RDWR" | .pipeRead => "O_RDONLY" | .pipeWrite => "O_WRONLY")
  if value.nonblock then return flags ||| (← h.libcI32 "O_NONBLOCK")
  return flags

def setFlags (h : Hooks S F E) (socket : F) (flags : Int32) : M S Int32 := do
  let bit ← h.libcI32 "O_NONBLOCK"
  let selected := flags &&& bit == bit
  h.put socket { (← h.get socket) with nonblock := selected }
  if (if selected then flags &&& ~~~bit else flags) != 0 then
    throw (.unsupported "fcntl: only O_NONBLOCK supported for socketpair/pipe F_SETFL")
  return 0

def ioctl (h : Hooks S F E) (socket : F) (operation : Scalar Provenance) : M S Int32 := do
  if (← h.get socket).kind != .socketpair then throw (.unsupported "cannot use ioctl on pipe")
  if operation != (← h.libc "FIONBIO") then throw (.unsupported "unsupported socket ioctl operation")
  if !(#["linux","android","macos","freebsd"].contains h.os) then throw (.unsupported "FIONBIO unsupported on target")
  let argument ← h.readIoctlArgument
  let value ← h.readFieldI32 (← h.derefI32 argument)
  h.put socket { (← h.get socket) with nonblock := value != 0 }
  return 0

private inductive WriteStage (F E : Type) where
  | done (result : Files.Result E Nat)
  | peerDone (peer : F) (result : Files.Result E Nat)
  | blocked (peer : F)
  | written (peer : F) (count : Nat)
private def prepareWrite (h : Hooks S F E) (socket : F) (pointer : Pointer (Option Provenance))
    (length : Nat) (nonblock : Bool) : M S (WriteStage F E) := do
  if length == 0 then return .done (.ok 0)
  let current ← h.get socket
  let some other ← h.readiness.upgrade (← peer current)
    | return .done (.error (.host (← h.errors.hostFromKind .BrokenPipe)))
  onError (do
    let otherValue ← h.get other
    let some buffer := otherValue.readbuf | return .peerDone other (.error (.libc "EBADF"))
    if buffer.bytes.size > capacity then throw (.invalidProgram "virtual buffer capacity strict_sub underflow")
    let available := capacity-buffer.bytes.size
    if available == 0 then
      if current.nonblock || nonblock then
        return .peerDone other (.error (.host (← h.errors.hostFromKind .WouldBlock)))
      let current ← h.get socket
      h.put socket { current with blockedWrite := current.blockedWrite.push (← h.readiness.runtime.threads).activeThread }
      return .blocked other
    clockRelease h buffer.clock fun clock =>
      h.put other {otherValue with readbuf := some {buffer with clock := clock}}
    let count := min length available
    let bytes ← h.readBytes pointer count
    if bytes.size != count then throw (.invalidProgram "virtual write_to_host byte count mismatch")
    let currentOther ← h.get other
    let some currentBuffer := currentOther.readbuf | throw (.invalidProgram "virtual peer read buffer disappeared")
    h.put other { currentOther with readbuf := some { currentBuffer with bytes := currentBuffer.bytes ++ bytes }, blockedRead := #[] }
    for thread in currentOther.blockedRead do h.readiness.unblock thread .VirtualSocket
    return .written other count
  ) (h.readiness.dropFd other)

/-- Consumes the actual owned socket ref. Blocking transfers it into the closure;
success transfers both descriptions to readiness in source order. -/
def write (budget : Nat) (h : Hooks S F E) (socket : F) (pointer : Pointer (Option Provenance))
    (length : Nat) (nonblock : Bool) (finish : Files.Finish S E) : M S Unit := do
  match budget with
  | 0 => Files.withDrop (throw (.resourceExhaustion "virtual socket write callback budget")) (h.readiness.dropFd socket)
  | budget+1 =>
    let stage ← onError (prepareWrite h socket pointer length nonblock) (h.readiness.dropFd socket)
    match stage with
    | .done result => Files.withDrop (finish result) (h.readiness.dropFd socket)
    | .peerDone other result => Files.withDrop (Files.withDrop (finish result) (h.readiness.dropFd other)) (h.readiness.dropFd socket)
    | .blocked other =>
      onError (block h fun reason => do
        if reason != .Ready then Files.withDrop (throw (.invalidProgram "virtual socket write timeout impossible")) (h.readiness.dropFd socket)
        else write budget h socket pointer length nonblock finish
      ) (do h.readiness.dropFd other; h.readiness.dropFd socket)
      h.readiness.dropFd other
    | .written other count =>
      onError (Readiness.updateFd h.wakeBudget h.readiness socket {}) (h.readiness.dropFd other)
      Readiness.updateFd h.wakeBudget h.readiness other { forceEdge := true }
      finish (.ok count)

private inductive ReadStage (E : Type) where
  | done (result : Files.Result E Nat)
  | blocked
  | read (count : Nat) (empty : Bool)
private def prepareRead (h : Hooks S F E) (socket : F) (pointer : Pointer (Option Provenance))
    (length : Nat) (nonblock : Bool) : M S (ReadStage E) := do
  if length == 0 then return .done (.ok 0)
  let value ← h.get socket
  let some buffer := value.readbuf | throw (.unsupported "reading from write end of pipe")
  if buffer.bytes.isEmpty then
    let other ← h.readiness.upgrade (← peer value)
    if let some other := other then h.readiness.dropFd other
    if other.isNone then return .done (.ok 0)
    if value.nonblock || nonblock then return .done (.error (.host (← h.errors.hostFromKind .WouldBlock)))
    h.put socket { value with blockedRead := value.blockedRead.push (← h.readiness.runtime.threads).activeThread }
    return .blocked
  clockAcquire h buffer.clock
  let count := min length buffer.bytes.size
  let bytes := buffer.bytes.extract 0 count
  let remaining := buffer.bytes.extract count buffer.bytes.size
  h.put socket { value with readbuf := some { buffer with bytes := remaining } }
  h.writeBytes pointer bytes
  return .read count remaining.isEmpty

def read (budget : Nat) (h : Hooks S F E) (socket : F) (pointer : Pointer (Option Provenance))
    (length : Nat) (nonblock : Bool) (finish : Files.Finish S E) : M S Unit := do
  match budget with
  | 0 => Files.withDrop (throw (.resourceExhaustion "virtual socket read callback budget")) (h.readiness.dropFd socket)
  | budget+1 =>
    let stage ← onError (prepareRead h socket pointer length nonblock) (h.readiness.dropFd socket)
    match stage with
    | .done result => Files.withDrop (finish result) (h.readiness.dropFd socket)
    | .blocked =>
      onError (block h fun reason => do
        if reason != .Ready then Files.withDrop (throw (.invalidProgram "virtual socket read timeout impossible")) (h.readiness.dropFd socket)
        else read budget h socket pointer length nonblock finish
      ) (h.readiness.dropFd socket)
    | .read count empty =>
      let other ← onError (do
        let other ← h.readiness.upgrade (← peer (← h.get socket))
        if let some other := other then
          onError (do
            let value ← h.get other
            h.put other { value with blockedWrite := #[] }
            for thread in value.blockedWrite do h.readiness.unblock thread .VirtualSocket
          ) (h.readiness.dropFd other)
        pure other
      ) (h.readiness.dropFd socket)
      if let some other := other then
        onError (Readiness.updateFd h.wakeBudget h.readiness other { forceEdge := empty }) (h.readiness.dropFd socket)
      Readiness.updateFd h.wakeBudget h.readiness socket {}
      finish (.ok count)

/-- recv rejects PEEK before delegating, unlike actual TCP sockets. -/
def recv (budget : Nat) (h : Hooks S F E) (socket : F) (pointer : Pointer (Option Provenance))
    (length : Nat) (peek nonblock : Bool) (finish : Files.Finish S E) : M S Unit := do
  if peek then Files.withDrop (throw (.unsupported "socketpair peeking unsupported")) (h.readiness.dropFd socket)
  else read budget h socket pointer length nonblock finish

private def createPair (h : Hooks S F E) (pipe nonblock : Bool) (output : MPlaceTy Provenance) : M S Int32 := do
  let first : State := ⟨some {},none,false,#[],#[],nonblock,if pipe then .pipeRead else .socketpair⟩
  let second : State := ⟨if pipe then none else some {},none,false,#[],#[],nonblock,if pipe then .pipeWrite else .socketpair⟩
  let first ← h.newSocket first
  let second ← onError (h.newSocket second) (h.readiness.dropFd first)
  onError (do
    let a ← h.get first
    let b ← h.get second
    if a.peer.isSome || b.peer.isSome then throw (.invalidProgram "virtual socket peer OnceCell already initialized")
    h.put first { a with peer := some (h.readiness.downgrade second) }
    h.put second { b with peer := some (h.readiness.downgrade first) }
  ) (do h.readiness.dropFd second; h.readiness.dropFd first)
  let firstNumber ← h.insert first
  let secondNumber ← h.insert second
  h.writeInt firstNumber.toInt output
  h.writeInt secondNumber.toInt (← h.nextI32 output)
  return 0

def socketpair (h : Hooks S F E) (domain kind protocol output : OpTy Provenance) : M S Int32 := do
  let domain ← h.readI32 domain
  let flags ← h.readI32 kind
  let protocol ← h.readI32 protocol
  let output ← h.derefI32 output
  let mut flags := flags
  let mut nonblock := false
  if #["linux","android","freebsd","solaris","illumos"].contains h.os then
    let bit ← h.libcI32 "SOCK_NONBLOCK"
    let cloexec ← h.libcI32 "SOCK_CLOEXEC"
    if flags &&& bit == bit then nonblock := true; flags := flags &&& ~~~bit
    if flags &&& cloexec == cloexec then flags := flags &&& ~~~cloexec
  let validDomain ← if domain == (← h.libcI32 "AF_UNIX") then pure true else do pure (domain == (← h.libcI32 "AF_LOCAL"))
  if !validDomain then throw (.unsupported "socketpair: only AF_UNIX/AF_LOCAL allowed")
  if flags != (← h.libcI32 "SOCK_STREAM") then throw (.unsupported "socketpair: unsupported socket type flags")
  if protocol != 0 then throw (.unsupported "socketpair: only protocol0 allowed")
  createPair h false nonblock output

def pipe2 (h : Hooks S F E) (output : OpTy Provenance) (flags : Option (OpTy Provenance)) : M S Int32 := do
  let output ← h.derefI32 output
  let mut flags ← match flags with | none => pure (0 : Int32) | some flags => h.readI32 flags
  let cloexec ← h.libcI32 "O_CLOEXEC"
  let bit ← h.libcI32 "O_NONBLOCK"
  let nonblock := flags &&& bit == bit
  if nonblock then flags := flags &&& ~~~bit
  if flags &&& cloexec == cloexec then flags := flags &&& ~~~cloexec
  if flags != 0 then throw (.unsupported "unsupported pipe2 flags")
  createPair h true nonblock output
end Miri.Interpreter.VirtualSocket
