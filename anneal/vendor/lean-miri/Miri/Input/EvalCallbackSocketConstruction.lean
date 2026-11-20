import Miri.Input.EvalCallbackOperationConstruction
import Miri.Input.EvalCallbackSocketSeed
import Miri.Input.EvalCallbackSocketRegistry
import Miri.Input.EvalUnixSourceConstruction
import Miri.Input.EvalUnixIoConstruction
import Miri.Input.EvalUnixFdConstruction
import Miri.Input.EvalOwnedIoMachine
import Miri.Interpreter.TcpSocket
import Miri.Interpreter.SocketAddress
import Miri.Interpreter.SocketOptions
import Miri.Interpreter.EventFd
import Miri.Interpreter.EventFdMachine
import Miri.Interpreter.SourceOther
import Miri.Input.CompilerPrimitiveFacts
import Miri.Input.CompilerProviders

/-! Source-built TCP, socket-option, virtual socket, and socket syscall policy
over the canonical callback registry and EvalWorld context. -/
namespace Miri.Input.EvalCallbackSocketConstruction
open Miri.ABI Miri.Memory Miri.Interpreter

/-- Source-backed virtual socket/pipe policy. State, descriptor allocation,
readiness registration, guest bytes, target constants, and pointer projections
are all taken from the selected compiler and final EvalWorld. The ioctl vararg
is intentionally a demand-local residual until ForeignContext exposes the
actual call-site varargs. -/
def virtualFromSource [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (seed : RegistrySeed Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    (physicalReadiness : Readiness.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)))
    (access : PlaceMachine.AccessConfig MiriMemoryKind
      (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (arithmetic : PointerArithmetic)
    (place : PlaceHooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C MachineHooks.FrameExtra)
    (projection : PlaceProjectionHooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C MachineHooks.FrameExtra)
    (choice : C)
    (errors : IoError.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Error)
    (wakeBudget : Nat) :
    Except StepError (VirtualSocket.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) Error) := do
  let target ← p.externStatics.targetFacts |>.mapError StepError.unsupported
  unless target.families.contains "unix" do
    throw (.invalidProgram s!"virtual socket hooks requested on non-Unix target `{target.os}`")
  let i32 ← match p.primitiveLayout "i32" with
    | .ok value => pure ⟨value.ty,value.layout⟩
    | .error reason => throw (.unsupported s!"compiler i32 layout for virtual socket: {reason}")
  let errors := {errors with family := .unix, os := target.os}
  let scalar := fun operand => do
    let immediate ← PlaceMachine.readImmediate access operand
    match immediate.imm.toScalar with
    | .ok value => pure value
    | .error error => throw (ScalarOps.immediateError error)
  let readI32 := fun operand => do
    match (← scalar operand).toInt32 with
    | .ok value => pure value
    | .error error => throw (ScalarOps.scalarError error)
  let libc := fun name => do
    match CompilerNamedConstants.scalar p.namedConstants name with
    | .ok value => pure value
    | .error reason => throw (.unsupported s!"compiler libc constant `{name}`: {reason}")
  let libcI32 := fun name => do
    match (← libc name).toInt32 with
    | .ok value => pure value
    | .error error => throw (ScalarOps.scalarError error)
  let writeInt := fun value destination => do
    let value ← match Scalar.fromInt value destination.layout.layout.size with
      | .ok value => pure value
      | .error error => throw (ScalarOps.scalarError error)
    writePlaceImmediate place choice (.scalar value)
      ⟨.memory destination.mplace,destination.layout⟩
  let base : VirtualSocket.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) Error := {
    readiness := physicalReadiness
    get := fun _ => throw (.invalidProgram "unbound virtual socket state read")
    put := fun _ _ => throw (.invalidProgram "unbound virtual socket state write")
    newSocket := fun _ => throw (.invalidProgram "unbound virtual socket descriptor allocation")
    insert := fun _ => throw (.invalidProgram "unbound virtual socket descriptor insertion")
    readBytes := fun pointer length => do
      if length >= 2^64 then throw (.invalidProgram "virtual socket read length exceeds u64")
      RawMemoryMachine.readBytes access arithmetic pointer (UInt64.ofNat length)
    writeBytes := RawMemoryMachine.writeBytes access arithmetic
    libc
    libcI32
    errors
    os := target.os
    readI32
    derefI32 := fun operand => do
      let immediate ← PlaceMachine.readImmediate access operand
      let (pointerScalar,metadata) ← match immediate.imm.toScalarAndMeta with
        | .ok value => pure value
        | .error error => throw (ScalarOps.immediateError error)
      let pointer ← match pointerScalar.toPointer access.runtime.base with
        | .ok value => pure value
        | .error error => throw (ScalarOps.scalarError error)
      PointerPlaceMachine.withMetadata access pointer metadata i32 false
    nextI32 := fun source => do
      let projected ← PlaceDynamic.offsetWithMeta projection choice
        ⟨.memory source.mplace,source.layout⟩ i32.layout.size .inbounds .none i32
      match projected.ref with
      | .memory memory => pure ⟨memory,projected.layout⟩
      | .local .. => throw (.invalidProgram "virtual socket fd-array projection became a local")
    readFieldI32 := fun source => do
      let immediate ← PlaceMachine.readImmediate access ⟨.indirect source.mplace,source.layout⟩
      let scalar ← match immediate.imm.toScalar with
        | .ok value => pure value
        | .error error => throw (ScalarOps.immediateError error)
      match scalar.toInt32 with
      | .ok value => pure value
      | .error error => throw (ScalarOps.scalarError error)
    writeInt
    readIoctlArgument := throw (.unsupported "virtual socket ioctl requires call-site varargs")
    wakeBudget }
  pure (SocketMachine.bindVirtual seed.readiness SourceOther.sockets EvalSocketStorage.sockets base)

/-- Exact FileDescription read/write/readiness route for the source virtual
socketpair and pipe family. TCP references remain Unsupported until their
host-backed state builder is attached. -/
def virtualFileEffects
    (budget : Nat)
    (virtual : VirtualSocket.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) Error) :
    SocketFileEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error := {
  read := fun reference _communicate pointer length finish => do
    let .other payload := reference.value | throw (.invalidProgram "virtual read received non-other descriptor")
    match SourceOther.sockets.project payload with
    | some (.virtual,_) => VirtualSocket.read budget virtual reference pointer length false finish
    | some (.tcp,_) => throw (.unsupported "TCP file-description read capability is not attached")
    | none => throw (.invalidProgram "virtual read received an unrecognized source descriptor")
  write := fun reference _communicate pointer length finish => do
    let .other payload := reference.value | throw (.invalidProgram "virtual write received non-other descriptor")
    match SourceOther.sockets.project payload with
    | some (.virtual,_) => VirtualSocket.write budget virtual reference pointer length false finish
    | some (.tcp,_) => throw (.unsupported "TCP file-description write capability is not attached")
    | none => throw (.invalidProgram "virtual write received an unrecognized source descriptor")
  readiness := fun payload => do
    match SourceOther.sockets.project payload with
    | some (.virtual,id) =>
      let reference : FD H D (Other Raw Listener TcpStream Error) := ⟨id,.other payload⟩
      return some (← VirtualSocket.readiness virtual reference)
    | some (.tcp,_) => throw (.unsupported "TCP readiness capability is not attached")
    | none => pure none }

/-- Construct TCP protocol hooks from the canonical file/readiness registry,
blocking source manager, compiler target and real host socket operations. The
host profile fact `hostWindows` comes from the runtime host configuration;
target OS remains the prepared compiler fact. -/
def tcpFromSource
    (p : CompilerProviders.Prepared)
    (seed : RegistrySeed Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    (physicalReadiness : Readiness.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)))
    (blocking : BlockingIo.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) Poll Error)
    (host : HostEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Raw Listener TcpStream Error Poll AddrIter)
    (errors : IoError.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Error)
    (hostWindows : Bool)
    (virtual : VirtualSocket.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) Error)
    (access : PlaceMachine.AccessConfig MiriMemoryKind
      (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (arithmetic : PointerArithmetic)
    (wakeBudget : Nat) :
    Except StepError (TcpSocket.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) Raw Listener TcpStream Error Poll Error) := do
  let target ← p.externStatics.targetFacts |>.mapError StepError.unsupported
  unless target.families.contains "unix" do
    throw (.invalidProgram s!"TCP hooks requested on non-Unix target `{target.os}`")
  let errors := {errors with family := .unix, os := target.os}
  let socketReadiness := SocketMachine.bindReadiness seed.readiness
    SourceOther.sockets EvalSocketStorage.sockets virtual physicalReadiness
  let base : TcpSocket.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) Raw Listener TcpStream Error Poll Error := {
    io := blocking
    get := fun _ => throw (.invalidProgram "unbound TCP state read")
    put := fun _ _ => throw (.invalidProgram "unbound TCP state write")
    cloneFd := fun _ => throw (.invalidProgram "unbound TCP descriptor clone")
    newFd := fun _ => throw (.invalidProgram "unbound TCP descriptor allocation")
    insert := fun _ => throw (.invalidProgram "unbound TCP descriptor insertion")
    os := target.os
    hostWindows
    hostEdgeBackend := host.edgeBackend
    errors
    newRaw := host.newRaw
    nonblocking := host.nonblocking
    dropRaw := host.dropRaw
    rawToListener := host.rawToListener
    rawToStream := host.rawToStream
    hostBind := host.hostBind
    hostListen := host.hostListen
    hostConnect := host.hostConnect
    hostAccept := host.hostAccept
    hostSend := host.hostSend
    hostRecv := host.hostRecv
    hostLocal := host.hostLocal
    hostPeer := host.hostPeer
    hostShutdown := host.hostShutdown
    hostTakeError := host.hostTakeError
    readBytes := fun pointer length => do
      if length >= 2^64 then throw (.invalidProgram "TCP buffer length exceeds u64")
      RawMemoryMachine.readBytes access arithmetic pointer (UInt64.ofNat length)
    writeBytes := RawMemoryMachine.writeBytes access arithmetic
    deadline := host.deadline
    connectingNameWarningOnce := host.connectingNameWarningOnce
    wakeBudget }
  pure (SocketMachine.bindTcp seed.readiness SourceOther.sockets EvalSocketStorage.sockets
    socketReadiness EvalSocketStorage.blocking base)

/-- Construct the two source-owned socket protocols together, preventing a
caller from pairing TCP state with a virtual/readiness view from another EvalWorld. -/
def protocolsFromSeed [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (seed : RegistrySeed Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    (physicalReadiness : Readiness.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)))
    (blocking : BlockingIo.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) Poll Error)
    (host : HostEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Raw Listener TcpStream Error Poll AddrIter)
    (errors : IoError.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Error)
    (hostWindows : Bool)
    (access : PlaceMachine.AccessConfig MiriMemoryKind
      (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (arithmetic : PointerArithmetic)
    (place : PlaceHooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C MachineHooks.FrameExtra)
    (projection : PlaceProjectionHooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C MachineHooks.FrameExtra)
    (choice : C) (wakeBudget : Nat) :
    Except StepError
      (VirtualSocket.Hooks
        (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
        (FD H D (Other Raw Listener TcpStream Error)) Error ×
       TcpSocket.Hooks
        (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
        (FD H D (Other Raw Listener TcpStream Error)) Raw Listener TcpStream Error Poll Error) := do
  let virtual ← virtualFromSource p seed physicalReadiness access arithmetic place projection choice errors wakeBudget
  let tcp ← tcpFromSource p seed physicalReadiness blocking host errors hostWindows virtual access arithmetic wakeBudget
  pure (virtual,tcp)

/-- FileDescription operation hooks for both source socket protocols. The
TCP route retains communicate and async finish; virtual pipes/socketpairs use
their owned buffer callback path. -/
def socketFileEffects
    (budget : Nat)
    (virtual : VirtualSocket.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) Error)
    (tcp : TcpSocket.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) Raw Listener TcpStream Error Poll Error) :
    SocketFileEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error := {
  read := fun reference communicate pointer length finish => do
    let .other payload := reference.value | throw (.invalidProgram "socket read received non-other descriptor")
    match SourceOther.sockets.project payload with
    | some (.virtual,_) => VirtualSocket.read budget virtual reference pointer length false finish
    | some (.tcp,_) => TcpSocket.sendRecv budget tcp reference communicate false pointer length false false finish
    | none => throw (.invalidProgram "socket read received unrecognized source descriptor")
  write := fun reference communicate pointer length finish => do
    let .other payload := reference.value | throw (.invalidProgram "socket write received non-other descriptor")
    match SourceOther.sockets.project payload with
    | some (.virtual,_) => VirtualSocket.write budget virtual reference pointer length false finish
    | some (.tcp,_) => TcpSocket.sendRecv budget tcp reference communicate true pointer length false false finish
    | none => throw (.invalidProgram "socket write received unrecognized source descriptor")
  readiness := fun payload => do
    match SourceOther.sockets.project payload with
    | some (.virtual,id) =>
      let reference : FD H D (Other Raw Listener TcpStream Error) := ⟨id,.other payload⟩
      return some (← VirtualSocket.readiness virtual reference)
    | some (.tcp,id) =>
      let reference : FD H D (Other Raw Listener TcpStream Error) := ⟨id,.other payload⟩
      let socket ← tcp.get reference
      return some socket.ready
    | none => pure none }

/-- Source completion rules reuse the canonical vectored-file completion
operations and the same compiler-backed socket address hooks. -/
def completionFromSource
    (vector : UnixVectored.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Metadata)
    (address : SocketAddress.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Error AddrIter)
    (pointerSize : Size) :
    OwnedSocketCompletion.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Error AddrIter := {
  file := EvalOwnedIoMachine.completion vector
  address
  pointerSize }

/-- Construct socket-option operations from compiler libc layouts, the same
source address-memory hooks, TCP-owned timeout/SO_ERROR state, and true host
SockRef option effects. -/
def optionsFromSource
    (p : CompilerProviders.Prepared)
    (address : SocketAddress.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Error AddrIter)
    (host : HostEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Raw Listener TcpStream Error Poll AddrIter)
    (tcp : TcpSocket.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) Raw Listener TcpStream Error Poll Error) :
    Except StepError (SocketOptions.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) Error AddrIter) := do
  let target ← p.externStatics.targetFacts |>.mapError StepError.unsupported
  unless target.families.contains "unix" do
    throw (.invalidProgram s!"socket options requested on non-Unix target `{target.os}`")
  let i32Layout ← match p.primitiveLayout "i32" with
    | .ok value => pure ⟨value.ty,value.layout⟩
    | .error reason => throw (.unsupported s!"compiler i32 layout for socket options: {reason}")
  let u32Layout ← match p.primitiveLayout "u32" with
    | .ok value => pure ⟨value.ty,value.layout⟩
    | .error reason => throw (.unsupported s!"compiler u32 layout for socket options: {reason}")
  let readTimeval := fun timeval => do
    let secondsPlace ← address.field timeval "tv_sec"
    let microsPlace ← address.field timeval "tv_usec"
    let seconds ← address.readSigned secondsPlace secondsPlace.layout.layout.size
    let micros ← address.readSigned microsPlace microsPlace.layout.layout.size
    if secondsNeg : seconds < 0 then
      pure none
    else if secondsLarge : seconds >= 2^64 then
      pure none
    else if microsNeg : micros < 0 then
      pure none
    else if microsLarge : micros >= 1000000 then
      pure none
    else
      have microsNonnegative : 0 ≤ micros := by omega
      have microsLess : micros < 1000000 := by omega
      have microsBound : micros.toNat < 1000000 := by
        have h : (micros.toNat : Int) < 1000000 := by
          rw [Int.toNat_of_nonneg microsNonnegative]
          exact microsLess
        omega
      let nanosValue := micros.toNat * 1000
      have nanosValueBound : nanosValue < 1000000000 := by omega
      let nanos := UInt32.ofNat nanosValue
      have nanosBound : nanos.toNat < 1000000000 := by
        change (BitVec.ofNat 32 nanosValue).toNat < 1000000000
        rw [BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by omega)]
        exact nanosValueBound
      pure (some ⟨UInt64.ofNat seconds.toNat,nanos,nanosBound⟩)
  pure {
    address
    os := target.os
    i32Layout := pure i32Layout
    u32Layout := pure u32Layout
    readI32 := fun value => do
      let scalar ← address.readScalar value
      match scalar.toInt32 with
      | .ok result => pure result
      | .error error => throw (ScalarOps.scalarError error)
    readTimeval
    setTimeout := TcpSocket.setTimeout tcp
    getTimeout := TcpSocket.getTimeout tcp
    takeError := TcpSocket.takeError tcp
    setHost := host.setHostOption
    getHost := host.getHostOption }

/-- Full Unix socket syscall hooks from the source-owned virtual/TCP protocols,
options, canonical descriptor ownership, and address-memory constructor. -/
def socketFromSource [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (seed : RegistrySeed Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    (virtual : VirtualSocket.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) Error)
    (tcp : TcpSocket.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) Raw Listener TcpStream Error Poll Error)
    (options : SocketOptions.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) Error AddrIter)
    (address : SocketAddress.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Error AddrIter)
    (access : PlaceMachine.AccessConfig MiriMemoryKind
      (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (asUnix : FD H D (Other Raw Listener TcpStream Error) → EStateM StepError
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Unit)
    (communicate : Bool)
    (isolationReject : String → EStateM StepError
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Bool)
    (budget : Nat) :
    Except StepError (Socket.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) Error AddrIter) := do
  let target ← p.externStatics.targetFacts |>.mapError StepError.unsupported
  unless target.families.contains "unix" do
    throw (.invalidProgram s!"socket hooks requested on non-Unix target `{target.os}`")
  let readI32 := fun operand => do
    let immediate ← PlaceMachine.readImmediate access operand
    let scalar ← match immediate.imm.toScalar with
      | .ok value => pure value
      | .error error => throw (ScalarOps.immediateError error)
    match scalar.toInt32 with
    | .ok value => pure value
    | .error error => throw (ScalarOps.scalarError error)
  let readSizeT := fun operand => do
    let immediate ← PlaceMachine.readImmediate access operand
    let scalar ← match immediate.imm.toScalar with
      | .ok value => pure value
      | .error error => throw (ScalarOps.immediateError error)
    match scalar.toTargetUsize access.runtime.pointerSize with
    | .ok value => pure value.toNat
    | .error error => throw (ScalarOps.scalarError error)
  let operations := SocketMachine.operations budget SourceOther.sockets virtual tcp options
  let base : Socket.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) Error AddrIter := {
    address
    operations
    os := target.os
    communicate
    isolationReject
    readI32
    readSizeT
    lookupFd := fun _ => throw (.invalidProgram "unbound socket descriptor lookup")
    asSocket := fun _ => throw (.invalidProgram "unbound socket type check")
    dropFd := fun _ => throw (.invalidProgram "unbound socket descriptor release")
    newTcp := fun _ _ => throw (.invalidProgram "unbound TCP socket allocation")
    insert := fun _ => throw (.invalidProgram "unbound socket descriptor insertion")
    writeInt := address.writeInt
    readLengthPlace := fun value => do
      let scalar ← address.readScalar value
      let result ← match scalar.toInt value.layout.layout.size with
        | .ok result => pure result
        | .error error => throw (ScalarOps.scalarError error)
      if result < 0 || result >= 2^64 then
        throw (.invalidProgram "socket option length does not fit host usize")
      pure result.toNat }
  pure (SocketMachine.bindSocket seed.readiness SourceOther.sockets
    EvalSocketStorage.sockets budget asUnix virtual tcp options base)

/-- Assemble final socket operations around protocols already built from the
canonical registry. This separates protocol construction from the vectored
completion dependency so a caller can reuse one protocol/store instance while
obtaining completion hooks from the native-FD source constructor. No socket
registry or host socket state is allocated here. -/
def socketOperationsFromProtocols
    [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (seed : RegistrySeed Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    (virtual : VirtualSocket.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) Error)
    (tcp : TcpSocket.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) Raw Listener TcpStream Error Poll Error)
    (host : HostEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Raw Listener TcpStream Error Poll AddrIter)
    (address : SocketAddress.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Error AddrIter)
    (access : PlaceMachine.AccessConfig MiriMemoryKind
      (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (asUnix : FD H D (Other Raw Listener TcpStream Error) → EStateM StepError
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Unit)
    (communicate : Bool)
    (isolationReject : String → EStateM StepError
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Bool)
    (budget : Nat)
    (vector : UnixVectored.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Metadata) :
    Except StepError (EvalCallbackSourceConstruction.SocketOperations
      Os R P H D (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler
      Raw Listener TcpStream Error Error AddrIter) := do
  let options ← optionsFromSource p address host tcp
  let socket ← socketFromSource p seed virtual tcp options address access asUnix
    communicate isolationReject budget
  let finish := completionFromSource vector address p.runtime.target.pointerSize
  pure ({
    machine := seed.readiness
    store := EvalSocketStorage.sockets
    blocking := EvalSocketStorage.blocking
    asUnix
    virtual
    tcp
    options
    socket
    finish } : EvalCallbackSourceConstruction.SocketOperations
      Os R P H D (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler
      Raw Listener TcpStream Error Error AddrIter)

/-- Build the callback's complete socket operations from one source context.
This is the handoff constructor for the ordinary callback assembly: no
`SocketOperations`, `VirtualSocket.Hooks`, `TcpSocket.Hooks`, `SocketOptions`,
or `Socket.Hooks` record is caller-selected. -/
def sourceSocketOperations [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (seed : RegistrySeed Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
    (physicalReadiness : Readiness.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)))
    (host : HostEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Raw Listener TcpStream Error Poll AddrIter)
    (errors : IoError.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Error)
    (hostWindows : Bool)
    (access : PlaceMachine.AccessConfig MiriMemoryKind
      (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (arithmetic : PointerArithmetic)
    (place : PlaceHooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C MachineHooks.FrameExtra)
    (projection : PlaceProjectionHooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C MachineHooks.FrameExtra)
    (choice : C) (wakeBudget socketBudget : Nat)
    (address : SocketAddress.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Error AddrIter)
    (asUnix : FD H D (Other Raw Listener TcpStream Error) → EStateM StepError
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Unit)
    (communicate : Bool)
    (isolationReject : String → EStateM StepError
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Bool)
    (vector : UnixVectored.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Metadata) :
    Except StepError (EvalCallbackSourceConstruction.SocketOperations
      Os R P H D (Other Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler
      Raw Listener TcpStream Error Error AddrIter) := do
  let blocking := blockingFromSeed seed physicalReadiness host
  let virtual ← virtualFromSource p seed physicalReadiness access arithmetic place projection choice errors wakeBudget
  let tcp ← tcpFromSource p seed physicalReadiness blocking host errors hostWindows virtual access arithmetic wakeBudget
  socketOperationsFromProtocols p seed virtual tcp host address access asUnix
    communicate isolationReject socketBudget vector

/-- Build BlockingIo over the same readiness registry and file ownership as
the Unix FD dispatcher. The source readiness cell belongs to canonical TCP
socket state; it is read and updated by descriptor identity, never by a second
caller-supplied table. -/
def blockingFromDispatch
    (dispatch : EvalUnixSourceConstruction.DispatchComponents
      Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
      Meta Path Place C ClockHost I)
    (host : HostEffects
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Raw Listener TcpStream Error Poll AddrIter) :
    BlockingIo.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) Poll Error := Id.run do
  let readiness := dispatch.nativeFd.readiness
  let physical := dispatch.environmentAndPoll.poll.epoll.poll.readiness
  let base : BlockingIo.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) Poll Error := {
    readiness := physical
    get := do return EvalSocketStorage.blocking.get (← get).machine.user
    put := fun manager => do
      modify fun state => {state with machine := {state.machine with
        user := EvalSocketStorage.blocking.put manager state.machine.user}}
    newPoll := host.newPoll
    dropPoll := host.dropPoll
    registerHostSource := host.registerHostSource
    pollHost := host.pollHost
    sourceReadiness := fun reference => do
      let state ← get
      let registry ← match EvalSocketStorage.sockets.get state.machine.user with
        | .ok registry => pure registry
        | .error error => throw error
      let entries := registry.tcp.filter (·.1 == reference.id)
      if entries.size != 1 then throw (.invalidProgram "blocking IO readiness has missing/ambiguous TCP state")
      let some (_,socket) := entries[0]? | throw (.invalidProgram "blocking IO TCP readiness lookup failed")
      pure socket.ready
    setSourceReadiness := fun reference value => do
      let state ← get
      let registry ← match EvalSocketStorage.sockets.get state.machine.user with
        | .ok registry => pure registry
        | .error error => throw error
      let entries := registry.tcp.filter (·.1 == reference.id)
      if entries.size != 1 then throw (.invalidProgram "blocking IO readiness update has missing/ambiguous TCP state")
      let tcp := registry.tcp.map fun (id,socket) => (id,if id == reference.id then {socket with ready := value} else socket)
      let user ← match EvalSocketStorage.sockets.put {registry with tcp} state.machine.user with
        | .ok user => pure user
        | .error error => throw error
      set {state with machine := {state.machine with user}}
    cloneFd := FileMachine.cloneReference readiness.files }
  return ReadinessMachine.bindBlocking readiness EvalSocketStorage.blocking base

end Miri.Input.EvalCallbackSocketConstruction
