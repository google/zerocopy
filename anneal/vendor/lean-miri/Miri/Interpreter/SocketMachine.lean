import Miri.Interpreter.MemoryShims
import Miri.Interpreter.TcpSocket
import Miri.Interpreter.VirtualSocket
import Miri.Interpreter.ReadinessMachine
import Miri.Interpreter.RawMemoryMachine
import Miri.Interpreter.DeadlineMachine
import Miri.Interpreter.TimeShims

/-! Shared canonical FD/Readiness/BlockingIo bindings for socket descriptions.
Registries store real protocol state under actual allocation identities. -/
namespace Miri.Interpreter.SocketMachine
open Miri.ABI Miri.Memory Miri.Concurrency Files
abbrev Ref (H D O : Type) := Files.Ref (Description H D O)
inductive Kind where | virtual | tcp deriving DecidableEq, Repr
structure Registry (R L T E : Type) where
  virtual : Array (FdId × VirtualSocket.State) := #[]
  tcp : Array (FdId × TcpSocket.State R L T E) := #[]
structure Store (U R L T E : Type) where
  get : U → Except StepError (Registry R L T E)
  put : Registry R L T E → U → Except StepError U
structure Descriptor (O : Type) where
  inject : Kind → FdId → O
  project : O → Option (Kind × FdId)
private def lift (value : Except StepError A) : MachineHooks.M K U A :=
  match value with | .ok value => pure value | .error error => throw error
private def getRegistry (store : Store U R L T E) : MachineHooks.M K U (Registry R L T E) := do
  lift (store.get (← get).machine.user)
private def putRegistry (store : Store U R L T E) (value : Registry R L T E) : MachineHooks.M K U Unit := do
  let state ← get
  let user ← lift (store.put value state.machine.user)
  set {state with machine := {state.machine with user}}

def kind (descriptor : Descriptor O) (ref : Ref H D O) : Option Kind :=
  match ref.value with
  | .other value => (descriptor.project value).bind fun (kind,id) => if id == ref.id then some kind else none
  | _ => none
private def virtualState (store : Store U R L T E) (ref : Ref H D O) : MachineHooks.M K U VirtualSocket.State := do
  let entries := (← getRegistry store).virtual.filter (·.1 == ref.id)
  if entries.size != 1 then throw (.invalidProgram "virtual socket state missing/ambiguous")
  let some (_,value) := entries[0]? | throw (.invalidProgram "virtual socket state missing")
  return value
private def tcpState (store : Store U R L T E) (ref : Ref H D O) : MachineHooks.M K U (TcpSocket.State R L T E) := do
  let entries := (← getRegistry store).tcp.filter (·.1 == ref.id)
  if entries.size != 1 then throw (.invalidProgram "TCP socket state missing/ambiguous")
  let some (_,value) := entries[0]? | throw (.invalidProgram "TCP socket state missing")
  return value
private def putVirtual (store : Store U R L T E) (ref : Ref H D O) (value : VirtualSocket.State) : MachineHooks.M K U Unit := do
  let _ ← virtualState store ref
  let registry ← getRegistry store
  putRegistry store { registry with virtual := registry.virtual.map fun (id,old) => (id,if id == ref.id then value else old) }
private def putTcp (store : Store U R L T E) (ref : Ref H D O) (value : TcpSocket.State R L T E) : MachineHooks.M K U Unit := do
  let _ ← tcpState store ref
  let registry ← getRegistry store
  putRegistry store { registry with tcp := registry.tcp.map fun (id,old) => (id,if id == ref.id then value else old) }
private def newDescription (h : ReadinessMachine.Hooks K U H D O) (descriptor : Descriptor O) (value : Kind) : MachineHooks.M K U (Ref H D O) := do
  let expected : FdId := ⟨(h.files.table (← get).machine.user).nextId⟩
  let payload := descriptor.inject value expected
  if descriptor.project payload != some (value,expected) then throw (.invalidProgram "socket payload injection/downcast mismatch")
  let ref ← FileMachine.newReference h.files (.other payload)
  if ref.id != expected then throw (.invalidProgram "socket payload actual FD identity mismatch")
  return ref
private def newVirtual (h : ReadinessMachine.Hooks K U H D O) (descriptor : Descriptor O)
    (store : Store U R L T E) (value : VirtualSocket.State) : MachineHooks.M K U (Ref H D O) := do
  let ref ← newDescription h descriptor .virtual
  let registry ← getRegistry store
  if registry.virtual.any (·.1 == ref.id) then throw (.invalidProgram "duplicate virtual socket identity")
  putRegistry store { registry with virtual := registry.virtual.push (ref.id,value) }
  ReadinessMachine.initWatched h ref
  return ref
private def newTcp (h : ReadinessMachine.Hooks K U H D O) (descriptor : Descriptor O)
    (store : Store U R L T E) (value : TcpSocket.State R L T E) : MachineHooks.M K U (Ref H D O) := do
  let ref ← newDescription h descriptor .tcp
  let registry ← getRegistry store
  if registry.tcp.any (·.1 == ref.id) then throw (.invalidProgram "duplicate TCP socket identity")
  putRegistry store { registry with tcp := registry.tcp.push (ref.id,value) }
  ReadinessMachine.initWatched h ref
  return ref
private def insert (h : ReadinessMachine.Hooks K U H D O) (ref : Ref H D O) : MachineHooks.M K U Int32 := do
  let (table,number) ← lift ((h.files.table (← get).machine.user).insert ref)
  modify fun state => { state with machine := { state.machine with user := h.files.setTable table state.machine.user } }
  return number

def bindVirtual (h : ReadinessMachine.Hooks K U H D O) (descriptor : Descriptor O)
    (store : Store U R L T E)
    (base : VirtualSocket.Hooks (MachineHooks.State K U) (Ref H D O) E) :
    VirtualSocket.Hooks (MachineHooks.State K U) (Ref H D O) E := {
  base with
  readiness := ReadinessMachine.bind h base.readiness
  get := virtualState store
  put := putVirtual store
  newSocket := newVirtual h descriptor store
  insert := insert h }

/-- Installed on the descriptor's actual last-drop route. TCP host state drops
before ReadinessWatched (struct field order). Virtual peer notification precedes
watched-field drop; it transfers a real upgraded ref to the delayed queue. -/
def dropSocket (h : ReadinessMachine.Hooks K U H D O) (descriptor : Descriptor O)
    (store : Store U R L T E)
    (virtual : VirtualSocket.Hooks (MachineHooks.State K U) (Ref H D O) E)
    (hostDrop : TcpSocket.SocketState R L T → MachineHooks.M K U Unit)
    (ref : Ref H D O) : MachineHooks.M K U Bool := do
  let some value := kind descriptor ref | return false
  match value with
  | .virtual => VirtualSocket.dropSocket virtual (← virtualState store ref)
  | .tcp => hostDrop (← tcpState store ref).socket
  ReadinessMachine.destroyWatched h virtual.readiness ref
  let registry ← getRegistry store
  putRegistry store { registry with virtual := registry.virtual.filter (·.1 != ref.id), tcp := registry.tcp.filter (·.1 != ref.id) }
  return true

/-- Descriptor readiness is protocol state, not an unconditional host-ready bit. -/
def bindReadiness (h : ReadinessMachine.Hooks K U H D O) (descriptor : Descriptor O)
    (store : Store U R L T E)
    (virtual : VirtualSocket.Hooks (MachineHooks.State K U) (Ref H D O) E)
    (base : Readiness.Hooks (MachineHooks.State K U) (Ref H D O)) :
    Readiness.Hooks (MachineHooks.State K U) (Ref H D O) :=
  let canonical := ReadinessMachine.bind h base
  { canonical with
    supportsWatching := fun ref => if (kind descriptor ref).isSome then true else canonical.supportsWatching ref
    readiness := fun ref => do
      match kind descriptor ref with
      | some .virtual => VirtualSocket.readiness virtual ref
      | some .tcp => return (← tcpState store ref).ready
      | none => canonical.readiness ref }

def bindTcp (h : ReadinessMachine.Hooks K U H D O) (descriptor : Descriptor O)
    (store : Store U R L T E)
    (readiness : Readiness.Hooks (MachineHooks.State K U) (Ref H D O))
    (blocking : ReadinessMachine.BlockingStore U Poll)
    (base : TcpSocket.Hooks (MachineHooks.State K U) (Ref H D O) R L T E Poll Host) :
    TcpSocket.Hooks (MachineHooks.State K U) (Ref H D O) R L T E Poll Host := {
  base with
  io := { (ReadinessMachine.bindBlocking h blocking base.io) with
    readiness := readiness
    cloneFd := FileMachine.cloneReference h.files
    sourceReadiness := fun ref => do return (← tcpState store ref).ready
    setSourceReadiness := fun ref ready => do putTcp store ref { (← tcpState store ref) with ready := ready } }
  get := tcpState store
  put := putTcp store
  cloneFd := FileMachine.cloneReference h.files
  newFd := newTcp h descriptor store
  insert := insert h }

/-- Exact host cfg list selecting epoll/kqueue short-I/O readiness clearing. -/
def edgeBackend (hostOs : String) : Bool := #["android","illumos","linux","redox","dragonfly","freebsd","ios","macos","netbsd","openbsd","tvos","visionos","watchos"].contains hostOs

/-- Generic timeout/SO_ERROR helpers move self into a consuming trait method;
its actual FD must drop before the subsequent temporary allocation. Host
SockRef options borrow self and retain ownership until the helper returns. -/
private def withOptionOwner (tcp : TcpSocket.Hooks S F R L T E P H)
    (options : SocketOptions.Hooks S F E I) (fd : F)
    (action : SocketOptions.Hooks S F E I → EStateM StepError S A) : EStateM StepError S A := do
  let runtime := tcp.io.readiness.runtime
  let (registry,token) := (← runtime.callbacks).registerOwned
    (fun _ => throw (.invalidProgram "socket option owner is not a runnable callback"))
    (tcp.io.readiness.dropFd fd)
  runtime.putCallbacks registry
  let release : EStateM StepError S Unit := do
    if (← runtime.callbacks).entries.any (·.1 == token) then SyncRuntime.cancelCallback runtime token
  let ownedOptions := { options with
    setTimeout := fun socket write timeout => do options.setTimeout socket write timeout; release
    getTimeout := fun socket write => do
      let value ← options.getTimeout socket write
      release
      return value
    takeError := fun socket => do
      let value ← options.takeError socket
      release
      return value }
  Files.withDrop (action ownedOptions) release

/-- TCP socket-option policy is shared with the syscall helpers; defaults on
virtual sockets remain Unsupported. This operation consumes the passed owner. -/
private def setOption (tcp : TcpSocket.Hooks S F R L T E P H)
    (options : SocketOptions.Hooks S F E I) (fd : F) (level option : Int32)
    (pointer : Pointer (Option Provenance)) (length : UInt64) : EStateM StepError S (Files.Result E Unit) :=
  withOptionOwner tcp options fd fun options => do
    if level == (← options.address.libcI32 "SOL_SOCKET") then SocketOptions.setGeneric options fd option pointer length
    else if level == (← options.address.libcI32 "IPPROTO_IP") then SocketOptions.setIp options fd option pointer length
    else if level == (← options.address.libcI32 "IPPROTO_TCP") then SocketOptions.setTcp options fd option pointer length
    else throw (.unsupported "setsockopt: unsupported level")
private def getOption (tcp : TcpSocket.Hooks S F R L T E P H)
    (options : SocketOptions.Hooks S F E I) (fd : F) (level option : Int32) :
    EStateM StepError S (Files.Result E (MPlaceTy Provenance)) :=
  withOptionOwner tcp options fd fun options => do
    if level == (← options.address.libcI32 "SOL_SOCKET") then SocketOptions.getGeneric options fd option
    else if level == (← options.address.libcI32 "IPPROTO_IP") then SocketOptions.getIp options fd option
    else if level == (← options.address.libcI32 "IPPROTO_TCP") then SocketOptions.getTcp options fd option
    else throw (.unsupported "getsockopt: unsupported level")

def operations (budget : Nat) (descriptor : Descriptor O)
    (virtual : VirtualSocket.Hooks S (Ref H D O) E)
    (tcp : TcpSocket.Hooks S (Ref H D O) R L T E P Host)
    (options : SocketOptions.Hooks S (Ref H D O) E I) : Socket.Operations S (Ref H D O) E :=
  let defaults := Socket.unsupportedOperations virtual.readiness.dropFd
  { bind := fun fd communicate address => if kind descriptor fd == some .tcp then TcpSocket.bind tcp fd communicate address else defaults.bind fd communicate address
    listen := fun fd communicate backlog => if kind descriptor fd == some .tcp then TcpSocket.listen tcp fd communicate backlog else defaults.listen fd communicate backlog
    accept := fun fd communicate nonblock finish => if kind descriptor fd == some .tcp then TcpSocket.accept budget tcp fd communicate nonblock (fun result => finish result) else defaults.accept fd communicate nonblock (fun result => finish result)
    connect := fun fd communicate address finish => if kind descriptor fd == some .tcp then TcpSocket.connect tcp fd communicate address finish else defaults.connect fd communicate address finish
    send := fun fd communicate pointer length nonblock finish =>
      match kind descriptor fd with
      | some .tcp => TcpSocket.sendRecv budget tcp fd communicate true pointer length false nonblock (fun result => finish result)
      | some .virtual => VirtualSocket.write budget virtual fd pointer length nonblock (fun result => finish result)
      | none => defaults.send fd communicate pointer length nonblock (fun result => finish result)
    recv := fun fd communicate pointer length peek nonblock finish =>
      match kind descriptor fd with
      | some .tcp => TcpSocket.sendRecv budget tcp fd communicate false pointer length peek nonblock (fun result => finish result)
      | some .virtual => VirtualSocket.recv budget virtual fd pointer length peek nonblock (fun result => finish result)
      | none => defaults.recv fd communicate pointer length peek nonblock (fun result => finish result)
    setOption := fun fd level option pointer length => if kind descriptor fd == some .tcp then setOption tcp options fd level option pointer length else defaults.setOption fd level option pointer length
    getOption := fun fd level option => if kind descriptor fd == some .tcp then getOption tcp options fd level option else defaults.getOption fd level option
    localName := fun fd communicate => if kind descriptor fd == some .tcp then TcpSocket.localName tcp fd communicate else defaults.localName fd communicate
    peerName := fun fd communicate finish => if kind descriptor fd == some .tcp then TcpSocket.peerName tcp fd communicate finish else defaults.peerName fd communicate finish
    shutdown := fun fd communicate how => if kind descriptor fd == some .tcp then TcpSocket.shutdown tcp fd communicate how else defaults.shutdown fd communicate how }

def bindOptions (tcp : TcpSocket.Hooks S F R L T E P H)
    (base : SocketOptions.Hooks S F E I) : SocketOptions.Hooks S F E I := {
  base with
  setTimeout := TcpSocket.setTimeout tcp
  getTimeout := TcpSocket.getTimeout tcp
  takeError := TcpSocket.takeError tcp }

def bindSocket (h : ReadinessMachine.Hooks K U H D O) (descriptor : Descriptor O)
    (store : Store U R L T E) (budget : Nat)
    (asUnix : Ref H D O → MachineHooks.M K U Unit)
    (virtual : VirtualSocket.Hooks (MachineHooks.State K U) (Ref H D O) E)
    (tcp : TcpSocket.Hooks (MachineHooks.State K U) (Ref H D O) R L T E P Host)
    (options : SocketOptions.Hooks (MachineHooks.State K U) (Ref H D O) E I)
    (base : Socket.Hooks (MachineHooks.State K U) (Ref H D O) E I) :
    Socket.Hooks (MachineHooks.State K U) (Ref H D O) E I := {
  base with
  operations := operations budget descriptor virtual tcp (bindOptions tcp options)
  lookupFd := fun number => do
    let some ref := (h.files.table (← get).machine.user).get number | return none
    return some (← FileMachine.cloneReference h.files ref)
  asSocket := fun ref => do
    asUnix ref
    match kind descriptor ref with
    | some .tcp => return true
    | some .virtual => return (← virtualState store ref).kind == .socketpair
    | none => return false
  dropFd := ReadinessMachine.dropFd h
  newTcp := TcpSocket.newSocket tcp
  insert := insert h }

/-- Source FileDescription::read/write route also supports virtual pipe ends;
only send/recv go through checked as_socket. Other payloads delegate unchanged. -/
def bindFiles (budget : Nat) (descriptor : Descriptor O)
    (virtual : VirtualSocket.Hooks S (Ref H D O) E)
    (tcp : TcpSocket.Hooks S (Ref H D O) R L T E Poll Host)
    (base : Files.Hooks S H D O E HM) : Files.Hooks S H D O E HM := {
  base with
  otherRead := fun ref communicate pointer length finish =>
    match kind descriptor ref with
    | some .virtual => VirtualSocket.read budget virtual ref pointer length false finish
    | some .tcp => TcpSocket.sendRecv budget tcp ref communicate false pointer length false false finish
    | none => base.otherRead ref communicate pointer length finish
  otherWrite := fun ref communicate pointer length finish =>
    match kind descriptor ref with
    | some .virtual => VirtualSocket.write budget virtual ref pointer length false finish
    | some .tcp => TcpSocket.sendRecv budget tcp ref communicate true pointer length false false finish
    | none => base.otherWrite ref communicate pointer length finish
  otherShortOperations := fun payload => if (descriptor.project payload).isSome then false else base.otherShortOperations payload
  otherHasReadinessWatched := fun payload => if (descriptor.project payload).isSome then true else base.otherHasReadinessWatched payload
  otherReadiness := fun payload => do
    match descriptor.project payload with
    | none => base.otherReadiness payload
    | some (.tcp,id) => return some (← tcp.get ⟨id,.other payload⟩).ready
    | some (.virtual,id) => return some (← VirtualSocket.readiness virtual ⟨id,.other payload⟩) }

/-- Actual monotonic clock and typed registry for nonblocking "now" probes and
relative read/write timeouts; no Nat timestamp approximation. -/
def bindDeadline (deadline : DeadlineMachine.Hooks K U Host System)
    (base : TcpSocket.Hooks (MachineHooks.State K U) F R L T E Poll Error) :
    TcpSocket.Hooks (MachineHooks.State K U) F R L T E Poll Error := {
  base with deadline := fun duration => do
    let now ← (deadline.clock (← get).machine.user).now deadline.host
    let instant ← match duration with | none => pure now | some duration => now.addLossy deadline.host duration
    DeadlineMachine.intern deadline (.monotonic instant) }

def bindRawMemory [DecidableEq K] (access : PlaceMachine.AccessConfig K U) (arithmetic : PointerArithmetic)
    (virtual : VirtualSocket.Hooks (MachineHooks.State K U) F E)
    (tcp : TcpSocket.Hooks (MachineHooks.State K U) F R L T E P H) :
    VirtualSocket.Hooks (MachineHooks.State K U) F E × TcpSocket.Hooks (MachineHooks.State K U) F R L T E P H :=
  let read := fun pointer length => do
    if length >= 2^64 then throw (.invalidProgram "socket memory length exceeds u64")
    RawMemoryMachine.readBytes access arithmetic pointer (UInt64.ofNat length)
  let write := RawMemoryMachine.writeBytes access arithmetic
  ({ virtual with readBytes := read, writeBytes := write }, { tcp with readBytes := read, writeBytes := write })
/-- Final authoritative registry composition; compiler/memory/host leaves from
base remain required. Both socket kinds share the same ownership/readiness view. -/
def bind (h : ReadinessMachine.Hooks K U H D O) (descriptor : Descriptor O)
    (store : Store U R L T E) (blocking : ReadinessMachine.BlockingStore U Poll) (budget : Nat)
    (asUnix : Ref H D O → MachineHooks.M K U Unit)
    (baseVirtual : VirtualSocket.Hooks (MachineHooks.State K U) (Ref H D O) E)
    (baseTcp : TcpSocket.Hooks (MachineHooks.State K U) (Ref H D O) R L T E Poll Host)
    (options : SocketOptions.Hooks (MachineHooks.State K U) (Ref H D O) E I)
    (socket : Socket.Hooks (MachineHooks.State K U) (Ref H D O) E I) :
    VirtualSocket.Hooks (MachineHooks.State K U) (Ref H D O) E ×
      TcpSocket.Hooks (MachineHooks.State K U) (Ref H D O) R L T E Poll Host ×
      Socket.Hooks (MachineHooks.State K U) (Ref H D O) E I :=
  let virtual := bindVirtual h descriptor store baseVirtual
  let readiness := bindReadiness h descriptor store virtual baseTcp.io.readiness
  let virtual := { virtual with readiness := readiness }
  let tcp := bindTcp h descriptor store readiness blocking baseTcp
  (virtual,tcp,bindSocket h descriptor store budget asUnix virtual tcp options socket)

def bindFullStacks
    (virtual : VirtualSocket.Hooks (ThreadStacks.State K U) F E)
    (tcp : TcpSocket.Hooks (ThreadStacks.State K U) F R L T E Poll Host) :
    VirtualSocket.Hooks (ThreadStacks.State K U) F E ×
      TcpSocket.Hooks (ThreadStacks.State K U) F R L T E Poll Host :=
  ({ virtual with readiness := ReadinessMachine.bindThreadStacks virtual.readiness },
    { tcp with io := ReadinessMachine.bindBlockingThreadStacks tcp.io })

/-- Address byte accesses and temporary-buffer copies reuse actual shared memory
operations. Compiler allocation, pointer views and field projections stay typed. -/
def bindAddress [DecidableEq K] (access : PlaceMachine.AccessConfig K U) (arithmetic : PointerArithmetic)
    (memory : MemoryShims.Hooks Provenance (MachineHooks.State K U) D MD B Inst)
    (budget : Nat) (base : SocketAddress.Hooks (MachineHooks.State K U) E I) :
    SocketAddress.Hooks (MachineHooks.State K U) E I := {
  base with
  isLiteralNull := fun pointer => pointer.provenance.isNone && pointer.offset.bytes == 0
  readCString := MemoryShims.readCString memory budget
  readBytes := fun pointer size => RawMemoryMachine.readBytes access arithmetic pointer size.bytes
  writeBytes := RawMemoryMachine.writeBytes access arithmetic
  writeZeros := fun pointer size => RawMemoryMachine.writeRepeatedByte access arithmetic pointer 0 size.bytes
  memCopy := fun source dest size nonoverlap => memory.copy source dest size.bytes nonoverlap }

def bindTimeval (time : TimeShims.Hooks S Host System Zone Stamp)
    (base : SocketOptions.Hooks S F E I) : SocketOptions.Hooks S F E I :=
  { base with readTimeval := TimeShims.readTimeval time }
end Miri.Interpreter.SocketMachine
