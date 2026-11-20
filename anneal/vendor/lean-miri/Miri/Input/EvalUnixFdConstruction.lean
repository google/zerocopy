import Miri.Input.CompilerCallConstruction
import Miri.Input.CompilerForeignSymbols
import Miri.Input.CompilerLibcTypeLayouts
import Miri.Input.CompilerNamedShimAbi
import Miri.Input.CompilerNamedConstants
import Miri.Input.CompilerNamedFields
import Miri.Input.CompilerBacktraceFacts
import Miri.Input.HostRuntime
import Miri.Input.EvalProjectionMachine
import Miri.Input.EvalSocketStorage
import Miri.Interpreter.ArrayProjection
import Miri.Interpreter.CompilerExecutionProviders
import Miri.Interpreter.DeadlineMachine
import Miri.Interpreter.PointerPlaceMachine
import Miri.Interpreter.PollDispatch
import Miri.Interpreter.PollMachine
import Miri.Interpreter.IoError
import Miri.Concurrency.SyncRuntime

/-! Compiler- and execution-state construction for the Unix descriptor/poll
family. Descriptor and readiness registries are projections of the actual
EvalWorld; target policy and the poll ABI come from rustc metadata. Only the
last-drop resource actions and the already-source-built physical epoll/poll
operations remain inputs. -/
namespace Miri.Input.EvalUnixFdConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev Other Raw Listener TcpStream Error :=
  EvalSocketStorage.Other Raw Listener TcpStream Error
abbrev User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalSocketStorage.User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
abbrev State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalSocketStorage.State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
abbrev FD H D O := Files.Ref (Files.Description H D O)

structure SourceFacts where
  target : CompilerExternStatic.TargetFacts
  /-- Demand-time query results: missing libc names or named ABI rows leave
  only poll unsupported while ordinary FD and filesystem shims remain usable. -/
  pollAbi : Except String (FnAbi TyId)

private def lift (error : String) : StepError := .unsupported error

def sourceFacts (p : CompilerProviders.Prepared) : Except StepError SourceFacts := do
  let target ← p.externStatics.targetFacts |>.mapError lift
  unless target.families.contains "unix" do
    throw (.invalidProgram s!"Unix FD construction on non-Unix target `{target.os}`")
  pure {
    target
    pollAbi := CompilerNamedShimAbi.expectedAbi p.namedAbi "poll"
  }

/-- The canonical descriptor table and Rc registry already contain the three
source stdio descriptors from InitialMachine/HostRuntime construction. This
builder only supplies their state projections and destructor effects; it never
reinitializes or duplicates the table. -/
def files
    (hostUsizeBits referenceBudget : Nat)
    (onLastDrop : Files.Description H D (Other Raw Listener TcpStream Error) →
      MachineHooks.M MiriMemoryKind
        (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Unit) :=
  EvalSocketStorage.files (Os := Os) (R := R) (P := P) (H := H) (D := D)
    (Aff := Aff) (B := B) (Poll := Poll) (Instant := Instant) (System := System)
    (Native := Native) (Profiler := Profiler) (Raw := Raw) (Listener := Listener)
    (TcpStream := TcpStream) (Error := Error) hostUsizeBits referenceBudget onLastDrop

/-- Readiness shares the same descriptor ownership registry. Its last-drop
callback performs watched-metadata cleanup and then the true resource drop. -/
def readiness
    (fileHooks : FileMachine.Hooks MiriMemoryKind
      (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error))
    (watcherReferenceBudget : Nat)
    (onLastDrop : FD H D (Other Raw Listener TcpStream Error) →
      MachineHooks.M MiriMemoryKind
        (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Unit) :=
  EvalSocketStorage.readiness (Os := Os) (R := R) (P := P) (H := H) (D := D)
    (Aff := Aff) (B := B) (Poll := Poll) (Instant := Instant) (System := System)
    (Native := Native) (Profiler := Profiler) (Raw := Raw) (Listener := Listener)
    (TcpStream := TcpStream) (Error := Error) fileHooks watcherReferenceBudget onLastDrop

/-- Install the real registry/weak-liveness semantics underneath a physical
readiness dictionary. The physical access and wake operations remain the
existing canonical source leaves. -/
def bindReadiness
    (registry : ReadinessMachine.Hooks MiriMemoryKind
      (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error))
    (physical : Readiness.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error))) :=
  ReadinessMachine.bind registry physical

/-- Bind FD operations to the actual descriptor and ownership arena, including
the source ReadinessWatched creation/drop hooks. The supplied UnixFd methods
are the physical/source operation leaves; their table and Rc behavior cannot
be substituted by caller-owned state. -/
def bindUnixFd
    (registry : ReadinessMachine.Hooks MiriMemoryKind
      (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error))
    (physicalReadiness : Readiness.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)))
    (base : UnixFd.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) Error Meta) :=
  ReadinessMachine.bindFiles registry (ReadinessMachine.bind registry physicalReadiness) base

/-- Construct the real poll foreign-item hooks around the existing source
poll/epoll implementation. Compiler ABI, C ABI compatibility, symbol-clash
checks, and operand transmutation are rebound here; a missing exact `poll`
query remains an Unsupported result at the source poll call. -/
def bindPoll
    (p : CompilerProviders.Prepared)
    (compatibilityBudget : Nat)
    (choice : C)
    (registry : ReadinessMachine.Hooks MiriMemoryKind
      (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error))
    (place : PlaceHooks Provenance
      (EvalCoreMachine.State Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D
          (Other Raw Listener TcpStream Error) Native Profiler))
      C MachineHooks.FrameExtra)
    (base : PollDispatch.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) Iter) :
    Except StepError (PollDispatch.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) Iter) := do
  let facts ← sourceFacts p
  let symbols ← p.foreignSymbols |>.mapError lift
  let callCompiler := CompilerCallConstruction.compiler p compatibilityBudget
  let poll := {base.epoll.poll with
    readiness := ReadinessMachine.bind registry base.epoll.poll.readiness
    hasRdHup := facts.target.os == "linux" || facts.target.os == "android" ||
      facts.target.os == "freebsd" || facts.target.os == "illumos"}
  let epoll := {base.epoll with poll}
  let projection := place.projection choice
  let transmute (operand : OpTy Provenance) (target : TyAndLayout TyId) := do
    let projection ← projection
    match operand.transmute projection target |>.mapError IntrinsicVectorMachine.projectionError with
    | .ok value => pure value
    | .error error => throw error
  pure {base with
    epoll
    os := facts.target.os
    pollAbi := match facts.pollAbi with
      | .ok abi => pure abi
      | .error error => throw (.unsupported error)
    argumentCompat := callCompiler.checkArgumentCompat choice
    checkSymbolClash := fun name =>
      match CompilerForeignSymbols.checkSymbolClash symbols name with
      | .ok () => pure ()
      | .error error => throw error
    transmute}

structure ArrayCursor where
  iterator : ArrayProjection.Iterator
  next : Nat

/-- The only readiness leaves that need to cross the startup constructor
boundary: typed callback/runtime routing and the source wake operation.
Descriptor policy and current readiness are taken from Files descriptions. -/
structure ReadinessRoute
    (S : Type) where
  runtime : Concurrency.SyncRuntime.Hooks S Nat Int32 (MPlaceTy Provenance)
  debugAssertions : Bool
  unblock : Concurrency.ThreadId → Concurrency.BlockReason → EStateM StepError S Unit

private def noReadinessBase (message : String) : EStateM StepError S A :=
  throw (.invalidProgram s!"unbound ReadinessMachine operation: {message}")

/-- Construct the physical readiness view from the actual source File hooks.
The registry binder below replaces every ownership/state operation; this view
provides only source description classification, callback routing and wakeup. -/
def readinessFromFiles
    (registry : ReadinessMachine.Hooks MiriMemoryKind
      (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error))
    (fileSemantics : Files.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) HostError Metadata)
    (route : ReadinessRoute
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)) :
    Readiness.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) :=
  ReadinessMachine.bind registry {
    runtime := route.runtime
    debugAssertions := route.debugAssertions
    getWatcher := fun _ => noReadinessBase "getWatcher"
    putWatcher := fun _ _ => noReadinessBase "putWatcher"
    upgradeWatcher := fun _ => noReadinessBase "upgradeWatcher"
    dropWatcher := fun _ => noReadinessBase "dropWatcher"
    watcherAlive := fun _ => noReadinessBase "watcherAlive"
    getFd := fun _ => noReadinessBase "getFd"
    id := Files.Ref.id
    downgrade := FileOwnership.downgrade
    upgrade := fun _ => noReadinessBase "upgrade"
    dropFd := fun _ => noReadinessBase "dropFd"
    isClosed := fun _ => noReadinessBase "isClosed"
    supportsWatching := fun reference => Files.hasReadinessWatched fileSemantics reference.value
    getWatched := fun _ => noReadinessBase "getWatched"
    putWatched := fun _ _ => noReadinessBase "putWatched"
    readiness := fun reference => do
      return ((← Files.readiness fileSemantics reference.value).getD {})
    delayed := noReadinessBase "delayed"
    putDelayed := fun _ => noReadinessBase "putDelayed"
    unblock := route.unblock}

private def scalarFromOperand
    (access : ValidityMachine.Access MiriMemoryKind
      (EvalCoreMachine.Stored Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D (Other Raw Listener TcpStream Error) Native Profiler)))
    (operand : OpTy Provenance) :
    EStateM StepError
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (Scalar Provenance) := do
  let value ← ValidityMachine.readImmediate access operand
  match value.imm.toScalar with
  | .ok scalar => pure scalar
  | .error error => throw (ScalarOps.immediateError error)

/-- Build all PollShims operations from exact libc/compiler queries and
canonical physical place/memory operations. `physicalReadiness` supplies only
thread/callback waking; the readiness registry, descriptor lookups, watcher
creation, layout projections, memory reads/writes, and compiler constants are
installed here. The deferred hook is only a construction intermediate:
EvalOwnedIoMachine.prepare replaces it with its typed completion route. -/
def pollWithDeadlineMillis
    (p : CompilerProviders.Prepared)
    (choice : C)
    (access : ValidityMachine.Access MiriMemoryKind
      (EvalCoreMachine.Stored Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D (Other Raw Listener TcpStream Error) Native Profiler)))
    (projection : PlaceProjectionHooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C MachineHooks.FrameExtra)
    (unitLayout : LocalLayout)
    (registry : ReadinessMachine.Hooks MiriMemoryKind
      (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error))
    (fileSemantics : Files.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) HostError Metadata)
    (readinessRoute : ReadinessRoute
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (deadlineMillis : UInt32 → PollShims.M
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Miri.Concurrency.ThreadDeadline)
    (iterationBudget : Nat) :
    Except StepError (PollShims.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) ArrayCursor) := do
  let facts ← sourceFacts p
  let readiness := readinessFromFiles registry fileSemantics readinessRoute
  let immediateScalar := scalarFromOperand access
  pure {
    deferred := .legacy
    readiness
    hasRdHup := facts.target.os == "linux" || facts.target.os == "android" ||
      facts.target.os == "freebsd" || facts.target.os == "illumos"
    libcU16 := fun name => do
      let scalar : Scalar Provenance ← match CompilerNamedConstants.scalar p.namedConstants name with
        | .ok value => pure value
        | .error reason => throw (.unsupported reason)
      match scalar.toUInt16 with
      | .ok value => pure value
      | .error error => throw (ScalarOps.scalarError error)
    readI32 := fun operand => do
      let scalar ← immediateScalar operand
      match scalar.toInt32 with
      | .ok value => pure value
      | .error error => throw (ScalarOps.scalarError error)
    readNfds := fun operand => do
      let nfds ← match CompilerLibcTypeLayouts.layout p.runtime "nfds_t" with
        | .ok layout => pure layout
        | .error reason => throw (.unsupported reason)
      unless operand.layout == nfds do throw (.invalidProgram "poll nfds_t operand layout differs from compiler libc type")
      let scalar ← immediateScalar operand
      match scalar.toTargetUsize nfds.layout.size with
      | .ok value => pure value
      | .error error => throw (ScalarOps.scalarError error)
    derefArray := fun operand typeName length => do
      let element ← match CompilerLibcTypeLayouts.layout p.runtime typeName with
        | .ok layout => pure layout
        | .error reason => throw (.unsupported reason)
      let arrayLayout ← RuntimeArrayQueries.arrayLayout EvalProjectionMachine.arrays element.ty length
      let scalar ← immediateScalar operand
      let pointer ← match scalar.toPointer access.runtime.base with
        | .ok pointer => pure pointer
        | .error error => throw (ScalarOps.scalarError error)
      PointerPlaceMachine.fromPointer access pointer arrayLayout false
    arrayFields := fun base => do
      let iterator ← ArrayProjection.prepare projection choice (pure unitLayout) base
      pure ⟨iterator,0⟩
    nextField := fun cursor => do
      if cursor.next >= cursor.iterator.length.toNat then return none
      let field ← ArrayProjection.get projection choice cursor.iterator cursor.next
      pure (some (field,{cursor with next := cursor.next + 1}))
    namedField := fun base name => do
      let index ← match CompilerNamedFields.fieldIndex p.runtime base.layout name with
        | .ok index => pure index
        | .error error => throw error
      let place ← PlaceDynamic.field projection choice ⟨.memory base.mplace,base.layout⟩ index
      match place.ref with
      | .memory mplace => pure ⟨mplace,place.layout⟩
      | .local .. => throw (.invalidProgram "poll memory field projection produced a local")
    readFieldI32 := fun field => do
      let scalar ← immediateScalar ⟨.indirect field.mplace,field.layout⟩
      match scalar.toInt32 with
      | .ok value => pure value
      | .error error => throw (ScalarOps.scalarError error)
    readFieldU16 := fun field => do
      let scalar ← immediateScalar ⟨.indirect field.mplace,field.layout⟩
      match scalar.toUInt16 with
      | .ok value => pure value
      | .error error => throw (ScalarOps.scalarError error)
    writeU16 := fun value dest => do
      let scalar ← match Scalar.fromUInt (BitVec.ofNat 128 value.toNat) (Size.ofBytes 2) with
        | .ok scalar => pure scalar
        | .error error => throw (ScalarOps.scalarError error)
      writePlaceImmediate projection.place choice (.scalar scalar) ⟨.memory dest.mplace,dest.layout⟩
    writeU32 := fun value dest => do
      let scalar ← match Scalar.fromUInt (BitVec.ofNat 128 value.toNat) (Size.ofBytes 4) with
        | .ok scalar => pure scalar
        | .error error => throw (ScalarOps.scalarError error)
      writePlaceImmediate projection.place choice (.scalar scalar) ⟨.memory dest.mplace,dest.layout⟩
    lookupFd := fun number => do
      match (registry.files.table (← get).machine.user).get number with
      | none => pure none
      | some ref => pure (some (← FileMachine.cloneReference registry.files ref))
    newWatcher := ReadinessMachine.newWatcher registry
    deadlineMillis
    iterationBudget}

/-- Compatibility wrapper retaining the full deadline interface for existing
source constructors. Poll itself only needs monotonic deadline creation, so
new call sites can use `pollWithDeadlineMillis` with the actual narrow action
and avoid constructing scheduler callback capabilities prematurely. -/
def poll
    (p : CompilerProviders.Prepared)
    (choice : C)
    (access : ValidityMachine.Access MiriMemoryKind
      (EvalCoreMachine.Stored Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D (Other Raw Listener TcpStream Error) Native Profiler)))
    (projection : PlaceProjectionHooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C MachineHooks.FrameExtra)
    (unitLayout : LocalLayout)
    (registry : ReadinessMachine.Hooks MiriMemoryKind
      (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error))
    (fileSemantics : Files.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) HostError Metadata)
    (readinessRoute : ReadinessRoute
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (deadline : DeadlineMachine.Hooks MiriMemoryKind
      (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Instant System)
    (iterationBudget : Nat) :
    Except StepError (PollShims.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) ArrayCursor) :=
  pollWithDeadlineMillis p choice access projection unitLayout registry fileSemantics
    readinessRoute (DeadlineMachine.monotonicDeadlineMillis deadline) iterationBudget

/-- Build the Linux/Android epoll hook set from the canonical poll hooks,
compiler event layout/constants, actual guest memory, and the same descriptor
registry. `EvalOwnedIoMachine.prepare` replaces the legacy construction marker
with its source typed deferred completion. -/
def epoll
    (p : CompilerProviders.Prepared)
    (choice : C)
    (access : ValidityMachine.Access MiriMemoryKind
      (EvalCoreMachine.Stored Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D (Other Raw Listener TcpStream Error) Native Profiler)))
    (projection : PlaceProjectionHooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C MachineHooks.FrameExtra)
    (pollHooks : PollShims.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) ArrayCursor)
    (registry : ReadinessMachine.Hooks MiriMemoryKind
      (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error))
    (descriptor : PollMachine.DescriptorHooks (Other Raw Listener TcpStream Error))
    (errors : IoError.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) HostError) :
    EpollShims.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) ArrayCursor := Id.run do
  let immediateScalar := scalarFromOperand access
  let field (base : MPlaceTy Provenance) (index : Nat) := do
    let projected ← PlaceDynamic.field projection choice ⟨.memory base.mplace,base.layout⟩ index
    match projected.ref with
    | .memory mplace => pure ⟨mplace,projected.layout⟩
    | .local .. => throw (.invalidProgram "epoll field projection produced a local")
  let writeScalar (value : Scalar Provenance) (dest : MPlaceTy Provenance) :=
    writePlaceImmediate projection.place choice (.scalar value) ⟨.memory dest.mplace,dest.layout⟩
  let writeU32 := fun (value : UInt32) (dest : MPlaceTy Provenance) => do
    let scalar ← match Scalar.fromUInt (BitVec.ofNat 128 value.toNat) (Size.ofBytes 4) with
      | .ok scalar => pure scalar
      | .error error => throw (ScalarOps.scalarError error)
    writeScalar scalar dest
  let writeU64 := fun (value : UInt64) (dest : MPlaceTy Provenance) => do
    let scalar ← match Scalar.fromUInt (BitVec.ofNat 128 value.toNat) (Size.ofBytes 8) with
      | .ok scalar => pure scalar
      | .error error => throw (ScalarOps.scalarError error)
    writeScalar scalar dest
  return {
    deferred := .legacy
    poll := pollHooks
    libcI32 := fun name => do
      let scalar : Scalar Provenance ← match CompilerNamedConstants.scalar p.namedConstants name with
        | .ok value => pure value
        | .error reason => throw (.unsupported reason)
      match scalar.toInt32 with
      | .ok value => pure value
      | .error error => throw (ScalarOps.scalarError error)
    libcU32 := fun name => do
      let scalar : Scalar Provenance ← match CompilerNamedConstants.scalar p.namedConstants name with
        | .ok value => pure value
        | .error reason => throw (.unsupported reason)
      match scalar.toUInt32 with
      | .ok value => pure value
      | .error error => throw (ScalarOps.scalarError error)
    readImmediate := fun operand => do
      let value ← ValidityMachine.readImmediate access operand
      pure ⟨.immediate value.imm,value.layout⟩
    derefEvent := fun operand => do
      let expected ← match CompilerLibcTypeLayouts.layout p.runtime "epoll_event" with
        | .ok value => pure value
        | .error reason => throw (.unsupported reason)
      let scalar ← immediateScalar operand
      let pointer ← match scalar.toPointer access.runtime.base with
        | .ok pointer => pure pointer
        | .error error => throw (ScalarOps.scalarError error)
      PointerPlaceMachine.fromPointer access pointer expected false
    indexedField := field
    readU32 := fun place => do
      let scalar ← immediateScalar ⟨.indirect place.mplace,place.layout⟩
      match scalar.toUInt32 with
      | .ok value => pure value
      | .error error => throw (ScalarOps.scalarError error)
    readU64 := fun place => do
      let scalar ← immediateScalar ⟨.indirect place.mplace,place.layout⟩
      match scalar.toUInt64 with
      | .ok value => pure value
      | .error error => throw (ScalarOps.scalarError error)
    arrayLength := fun place => do
      return (← PlaceDynamic.length projection choice ⟨.memory place.mplace,place.layout⟩).toNat
    writeEvent := fun place events data => do
      let eventIndex ← match CompilerNamedFields.fieldIndex p.runtime place.layout "events" with
        | .ok value => pure value
        | .error error => throw error
      let dataIndex ← match CompilerNamedFields.fieldIndex p.runtime place.layout "u64" with
        | .ok value => pure value
        | .error error => throw error
      writeU32 events (← field place eventIndex)
      writeU64 data (← field place dataIndex)
    writeI32 := fun value dest => do
      let scalar ← match Scalar.fromInt value.toInt dest.layout.layout.size with
        | .ok scalar => pure scalar
        | .error error => throw (ScalarOps.scalarError error)
      writeScalar scalar dest
    setErrno := fun name => IoError.setLastError errors (.libc name)
    insertEpoll := PollMachine.insertEpoll registry descriptor
    asEpoll := fun ref => pure (match ref.value with
      | .other value => (descriptor.project value).map PollMachine.Epoll.watcher
      | _ => none)}

/-- Assemble the final Unix poll/epoll foreign dispatcher rather than asking an
outer constructor to hand in a completed PollDispatch dictionary. The sole
physical scheduling leaf is the real zero-timeout mio poll operation. -/
def dispatch
    (p : CompilerProviders.Prepared)
    (compatibilityBudget : Nat)
    (choice : C)
    (place : PlaceHooks Provenance
      (EvalCoreMachine.State Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D
          (Other Raw Listener TcpStream Error) Native Profiler))
      C MachineHooks.FrameExtra)
    (epollHooks : EpollShims.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) ArrayCursor)
    (communicate : Bool)
    (entryPollBudget : Nat)
    (io : BlockingIo.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) Poll HostEffect) :
    Except StepError (PollDispatch.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) ArrayCursor) := do
  let facts ← sourceFacts p
  let symbols ← p.foreignSymbols |>.mapError lift
  let callCompiler := CompilerCallConstruction.compiler p compatibilityBudget
  let projection := place.projection choice
  pure {
    epoll := epollHooks
    os := facts.target.os
    communicate
    pollAndUnblockZero := BlockingIo.pollAndUnblock entryPollBudget io (some ⟨0,0,by decide⟩)
    pollAbi := match facts.pollAbi with
      | .ok abi => pure abi
      | .error error => throw (.unsupported error)
    argumentCompat := callCompiler.checkArgumentCompat choice
    checkSymbolClash := fun name =>
      match CompilerForeignSymbols.checkSymbolClash symbols name with
      | .ok () => pure ()
      | .error error => throw error
    transmute := fun operand target => do
      let projection ← projection
      match operand.transmute projection target |>.mapError IntrinsicVectorMachine.projectionError with
      | .ok value => pure value
      | .error error => throw error}

/-- Complete source constructor for Unix poll and Linux/Android epoll. It
connects compiler queries, guest memory, descriptor/watcher ownership,
callback routing, deadlines and the real blocking scheduler into one
PollDispatch value, with no caller-selected poll/epoll implementation. -/
def pollDispatch
    (p : CompilerProviders.Prepared)
    (compatibilityBudget : Nat)
    (choice : C)
    (place : PlaceHooks Provenance
      (EvalCoreMachine.State Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D
          (Other Raw Listener TcpStream Error) Native Profiler))
      C MachineHooks.FrameExtra)
    (projection : PlaceProjectionHooks Provenance
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      C MachineHooks.FrameExtra)
    (access : ValidityMachine.Access MiriMemoryKind
      (EvalCoreMachine.Stored Os R P H D (Other Raw Listener TcpStream Error) Aff B
        (HostRuntime.Storage Poll Instant System H D (Other Raw Listener TcpStream Error) Native Profiler)))
    (unitLayout : LocalLayout)
    (registry : ReadinessMachine.Hooks MiriMemoryKind
      (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error))
    (fileSemantics : Files.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      H D (Other Raw Listener TcpStream Error) HostError Metadata)
    (readinessRoute : ReadinessRoute
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error))
    (deadline : DeadlineMachine.Hooks MiriMemoryKind
      (User Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      Instant System)
    (descriptor : PollMachine.DescriptorHooks (Other Raw Listener TcpStream Error))
    (errors : IoError.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) HostError)
    (communicate : Bool)
    (entryPollBudget iterationBudget : Nat)
    (io : BlockingIo.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) Poll HostEffect) :
    Except StepError (PollDispatch.Hooks
      (State Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
      (FD H D (Other Raw Listener TcpStream Error)) ArrayCursor) := do
  let pollHooks ← poll p choice access projection unitLayout registry fileSemantics
    readinessRoute deadline iterationBudget
  let epollHooks := epoll p choice access projection pollHooks registry descriptor errors
  dispatch p compatibilityBudget choice place epollHooks communicate entryPollBudget io

end Miri.Input.EvalUnixFdConstruction
