import Miri.Interpreter.RaceMode
import Miri.Interpreter.PointerPlaceMachine
import Miri.Interpreter.LinuxFutex
import Miri.Interpreter.ExecutionStateTransport
import Miri.Interpreter.DeadlineMachine
import Miri.Interpreter.IoError
import Miri.Concurrency.FutexRuntime

/-! Linux futex physical/synchronization binding. Futex callbacks are the exact
source FnOnce captures, not arbitrary opaque token completion. None mode never
requires a fabricated GlobalState. Actual stack switching uses ThreadStacks. -/
namespace Miri.Interpreter.LinuxFutexMachine
open Miri.ABI Miri.Memory Miri.MIR Miri.Concurrency
abbrev User := ExecutionStateTransport.Inner
abbrev State K U := MachineHooks.State K (User U)
abbrev M K U A := MachineHooks.M K (User U) A
abbrev Captures := FutexRuntime.Storage (MPlaceTy Provenance)

structure Views (U : Type) where
  storage : U → Captures
  putStorage : U → Captures → U
  /-- The same supply used for TLS/join/source thread callbacks. -/
  nextCallback : U → Nat
  putNextCallback : U → Nat → U
structure Payload (P : Type) where
  inject : FutexRuntime.Ref → P
  project : P → Option FutexRuntime.Ref
  projectInject : ∀ ref, project (inject ref) = some ref
structure Hooks (K U C P O B Host System TZ Timestamp ErrorHost : Type) where
  views : Views U
  payload : Payload P
  access : PlaceMachine.AccessConfig K (User U)
  allocation : PlaceMachine.AllocationConfig K (User U)
  compiler : PlaceMachine.CompilerHooks K (User U) C
  pointers : PointerMachine.Hooks K (ValidityMachine.Control (ThreadStacks.Storage U))
  pointerCompiler : PointerPlaceMachine.Compiler K (ThreadStacks.Storage U) C
  dynamic : DynamicLayoutHooks Provenance (State K U) C
  vtable : VTableHooks Provenance (State K U) C (FnVal O) (FnAbi TyId)
  dynamicFuel : Nat
  atomic : AtomicAccessHooks Provenance (State K U) C (RuntimePlace Provenance)
  backend : State K U → Except StepError (RaceMode.Handler B)

  extras : MemoryExtras.Hooks K (User U) P
  i32Layout : LocalLayout
  /-- Compiler-checked guest timespec reader. This is the only time-shim
  operation consumed by futex; clock/deadline state is carried separately. -/
  readTimespec : MPlaceTy Provenance → M K U (Option Clock.Duration)
  deadline : DeadlineMachine.Hooks K (User U) Host System
  errors : IoError.Hooks (State K U) ErrorHost
  communicate : M K U Bool

/-- The real memory/backend projection needed to construct and use
allocation-local typed synchronization objects. It intentionally excludes
time, deadline, errno, and isolation capabilities: pthread mutexes/attributes
do not need those host effects, while timed operations remain supplied by the
separately constructed dispatch hooks. -/
structure ObjectHooks (K U C P O B : Type) where
  views : Views U
  payload : Payload P
  access : PlaceMachine.AccessConfig K (User U)
  allocation : PlaceMachine.AllocationConfig K (User U)
  compiler : PlaceMachine.CompilerHooks K (User U) C
  pointers : PointerMachine.Hooks K (ValidityMachine.Control (ThreadStacks.Storage U))
  pointerCompiler : PointerPlaceMachine.Compiler K (ThreadStacks.Storage U) C
  dynamic : DynamicLayoutHooks Provenance (State K U) C
  vtable : VTableHooks Provenance (State K U) C (FnVal O) (FnAbi TyId)
  dynamicFuel : Nat
  atomic : AtomicAccessHooks Provenance (State K U) C (RuntimePlace Provenance)
  backend : State K U → Except StepError (RaceMode.Handler B)
  extras : MemoryExtras.Hooks K (User U) P

/-- A full futex capability always contains the same genuine physical fields.
Projecting them supports time-independent pthread object construction without
creating a second memory, backend, atomic, or metadata state. -/
def objectHooks (h : Hooks K U C P O B Host System TZ Timestamp ErrorHost) :
    ObjectHooks K U C P O B := {
  views := h.views
  payload := h.payload
  access := h.access
  allocation := h.allocation
  compiler := h.compiler
  pointers := h.pointers
  pointerCompiler := h.pointerCompiler
  dynamic := h.dynamic
  vtable := h.vtable
  dynamicFuel := h.dynamicFuel
  atomic := h.atomic
  backend := h.backend
  extras := h.extras }

private def lift (value : Except StepError A) : M K U A :=
  match value with | .ok value => pure value | .error error => throw error
private def machineAction (action : PlaceMachine.MachineM K (User U) A) : M K U A := fun s =>
  match action s.machine with
  | .ok value machine => .ok value {s with machine}
  | .error error machine => .error error {s with machine}
private def payload : M K U U := return (← get).machine.user.payload.payload.user
private def modifyPayload (f : U → U) : M K U Unit :=
  modify fun s => {s with machine := {s.machine with user := {s.machine.user with payload :=
    {s.machine.user.payload with payload := {s.machine.user.payload.payload with user := f s.machine.user.payload.payload.user}}}}}
private def readImmediate [DecidableEq K] (h : Hooks K U C P O B H Y Z T E) (operand : OpTy Provenance) : M K U (Scalar Provenance) := do
  let value ← ValidityMachine.readImmediate h.access operand
  lift (value.imm.toScalar |>.mapError ScalarOps.immediateError)
private def writeScalar [DecidableEq K] (h : Hooks K U C P O B H Y Z T E) (choice : C)
    (value : Scalar Provenance) (dest : MPlaceTy Provenance) : M K U Unit :=
  writePlaceImmediate (ValidityMachine.placeHooks h.access h.allocation h.compiler) choice (.scalar value)
    ⟨.memory dest.mplace,dest.layout⟩
private def writeInt [DecidableEq K] (h : Hooks K U C P O B H Y Z T E) (choice : C)
    (value : Int) (dest : MPlaceTy Provenance) : M K U Unit := do
  let scalar ← lift (Scalar.fromInt value dest.layout.layout.size |>.mapError ScalarOps.scalarError)
  writeScalar h choice scalar dest

def ioErrors [DecidableEq K] (h : Hooks K U C P O B H Y Z T E) (choice : C) : IoError.Hooks (State K U) E :=
  {h.errors with
    writeScalar := writeScalar h choice
    readScalar := fun place => readImmediate h ⟨.indirect place.mplace,place.layout⟩
    writeInt := writeInt h choice}

private def storage (h : Hooks K U C P O B H Y Z T E) : M K U Captures := return h.views.storage (← payload)
private def setStorage (h : Hooks K U C P O B H Y Z T E) (value : Captures) : M K U Unit :=
  modifyPayload fun u => h.views.putStorage u value
private def futex (h : Hooks K U C P O B H Y Z T E) (ref : FutexRuntime.Ref) : M K U FutexState := do
  let some value := (← storage h).objects[ref.index]? | throw (.invalidProgram "missing source FutexRef")
  pure value
private def putFutex (h : Hooks K U C P O B H Y Z T E) (ref : FutexRuntime.Ref) (value : FutexState) : M K U Unit := do
  let data ← storage h
  if bound : ref.index < data.objects.size then setStorage h {data with objects := data.objects.set ref.index value}
  else throw (.invalidProgram "missing source FutexRef")

def newFutex (h : Hooks K U C P O B H Y Z T E) : M K U FutexRuntime.Ref := do
  let data ← storage h
  setStorage h {data with objects := data.objects.push {}}
  pure ⟨data.objects.size⟩
private def take (h : Hooks K U C P O B H Y Z T E) (token : Nat) : M K U (FutexRuntime.Callback (MPlaceTy Provenance)) := do
  let data ← storage h
  let entries := data.callbacks.filter (·.1 == token)
  if entries.size != 1 then throw (.callback "missing or ambiguous typed futex callback")
  let some (_,callback) := entries[0]? | throw (.invalidProgram "futex callback lookup invariant")
  setStorage h {data with callbacks := data.callbacks.filter (·.1 != token)}
  pure callback

def sourceError : SyncError → StepError
  | error => .invalidProgram s!"futex synchronization invariant: {reprStr error}"

def runtime [DecidableEq K] (h : Hooks K U C P O B H Y Z T E) (choice : C) :
    FutexRuntime.Hooks (State K U) (MPlaceTy Provenance) where
  handler := do
    match ← lift (h.backend (← get)) with
    | .none => pure .none | .vclocks _ => pure .vectorClocks
  global := return (← get).machine.dataRace
  putGlobal := fun g => modify fun s => {s with machine := {s.machine with dataRace := some g}}
  threads := return (← get).machine.threads
  putThreads := fun manager => ExecutionStateTransport.reverseAction (ThreadStacks.installManager manager)
  communicate := h.communicate
  futex := futex h
  putFutex := putFutex h
  register := fun callback => do
    let token := h.views.nextCallback (← payload)
    let data ← storage h
    if data.callbacks.any (·.1 == token) then throw (.invalidProgram "futex callback token collision")
    modifyPayload fun u => h.views.putNextCallback u (token+1)
    setStorage h {data with callbacks := data.callbacks.push (token,callback)}
    pure token
  take := take h
  cancel := fun token => do let _ ← take h token; pure ()
  unblock := fun id invoke => ExecutionStateTransport.reverseAction
    (ThreadStacks.unblockThread id .Futex (fun token kind => ExecutionStateTransport.action (invoke token kind)))
  ready := writeInt h choice 0
  timedOut := IoError.setErrnoAndReturnNeg1 (ioErrors h choice) (.libc "ETIMEDOUT")
  error := sourceError

/-- Futex metadata's source on_access and provenance visitor are empty. Other
payload variants keep their actual existing synchronization behavior. -/
def onAccess (embedding : Payload P) (other : P → SyncObject.AccessKind → PlaceMachine.MachineM K (User U) Unit)
    (value : P) (kind : SyncObject.AccessKind) : PlaceMachine.MachineM K (User U) Unit :=
  match embedding.project value with | some _ => pure () | none => other value kind

def metadataFromObjectHooks [DecidableEq K] (h : ObjectHooks K U C P O B) :
    SyncObject.MetadataHooks (State K U) FutexRuntime.Ref where
  tryResolve := fun pointer => do
    try
      let some provenance := pointer.provenance | return none
      let result ← PointerMachine.ptrGetAlloc h.pointers (Pointer.new provenance pointer.offset) 0
      pure (result.map fun (id,offset) => ⟨id,offset⟩)
    catch _ => pure none
  resolve := fun pointer => do
    let some provenance := pointer.provenance | throw (.invalidProgram "checked sync pointer has no provenance")
    let some (id,offset) ← PointerMachine.ptrGetAlloc h.pointers (Pointer.new provenance pointer.offset) 0
      | throw (.invalidProgram "checked sync pointer became unresolved")
    -- get_alloc_extra_mut materializes compiler globals before metadata lookup.
    let _ ← AtomicMachine.mutability h.access id
    pure ⟨id,offset⟩
  info := fun id => do
    let info ← match (← get).machine.memory.getAllocInfo id with
      | .ok info => pure info | .error error => throw (.callback s!"sync allocation info: {reprStr error}")
    pure ⟨info.kind == .liveData,info.mutability == .Mut,info.size⟩
  lookup := fun address => do
    let object ← machineAction (MemoryExtras.lookupSync h.extras address)
    pure (object.bind fun object => (h.payload.project object.payload).map fun ref =>
      {payload := ref,deleteOnWrite := object.deleteOnWrite,onAccess := fun _ => pure ()})
  insert := fun address object =>
    machineAction (MemoryExtras.insertSync h.extras address ⟨h.payload.inject object.payload,object.deleteOnWrite,#[]⟩)

def metadata [DecidableEq K] (h : Hooks K U C P O B H Y Z T E) :
    SyncObject.MetadataHooks (State K U) FutexRuntime.Ref :=
  metadataFromObjectHooks (objectHooks h)

def bind [DecidableEq K] (h : Hooks K U C P O B H Y Z T E) (choice : C)
    (base : LinuxFutex.Hooks (State K U) FutexRuntime.Ref) : LinuxFutex.Hooks (State K U) FutexRuntime.Ref :=
  {base with
    readPointer := fun op => do lift ((← readImmediate h op).toPointer h.access.runtime.base |>.mapError ScalarOps.scalarError)
    readI32 := fun op => do pure (Int32.ofInt (← lift ((← readImmediate h op).toInt (Size.ofBytes 4) |>.mapError ScalarOps.scalarError)))
    readU32 := fun op => do pure (UInt32.ofNat (← lift ((← readImmediate h op).toUInt (Size.ofBytes 4) |>.mapError ScalarOps.scalarError)).toNat)
    isNull := fun ptr => do
      let value ← lift (Scalar.fromMaybePointer h.access.runtime.base ptr |>.mapError ScalarOps.scalarError)
      ValidityMachine.scalarMayBeNull value
    i32Place := fun ptr => PointerPlaceMachine.fromPointer h.access ptr h.i32Layout false
    timespecPlace := fun op => PointerPlaceMachine.dereference h.access h.pointerCompiler h.dynamic h.vtable h.dynamicFuel choice op
    readTimespec := h.readTimespec
    timeout := DeadlineMachine.timeout h.deadline
    seqCstFence := do
      match ← lift (h.backend (← get)) with
      | .none | .vclocks _ => IntrinsicAtomic.fence h.atomic .SeqCst false
    readAcquire := fun place => do
      let value ← match ← lift (h.backend (← get)) with
        | .none | .vclocks _ => IntrinsicAtomic.load h.atomic choice ⟨.memory place.mplace,place.layout⟩ .Acquire
      pure (UInt32.ofNat (← lift (value.toUInt (Size.ofBytes 4) |>.mapError ScalarOps.scalarError)).toNat)
    metadata := metadata h
    newFutex := newFutex h
    wait := FutexRuntime.wait (runtime h choice)
    wake := FutexRuntime.wake (runtime h choice)
    errnoNegOne := fun name => IoError.setErrnoAndReturnNeg1 (ioErrors h choice) (.libc name)
    writeInt := writeInt h choice
    writeIsize := fun value dest => do
      let scalar ← lift (Scalar.fromInt value h.access.runtime.pointerSize |>.mapError ScalarOps.scalarError)
      writeScalar h choice scalar dest}

/-- Build the source syscall-facing futex hooks directly from the physical
    futex constructor. The syscall ABI checker and target constants remain
    explicit inputs; all memory, atomic, callback, deadline, and errno effects
    come from this same runtime-owned machine hook record. -/
def bindForSyscall [DecidableEq K] (h : Hooks K U C P O B H Y Z T E)
    (choice : C)
    (takeArgs : Array LinuxFutex.ArgType → ShimSignatures.Varargs Provenance →
      EStateM StepError (State K U) (Array (OpTy Provenance)))
    (libcI32 : String → EStateM StepError (State K U) Int32)
    (hostUsizeBits : Nat) : LinuxFutex.Hooks (State K U) FutexRuntime.Ref := Id.run do
  let base : LinuxFutex.Hooks (State K U) FutexRuntime.Ref := {
    takeArgs
    readPointer := fun op => do
      let scalar ← readImmediate h op
      lift (scalar.toPointer h.access.runtime.base |>.mapError ScalarOps.scalarError)
    readI32 := fun op => do
      let scalar ← readImmediate h op
      pure (Int32.ofInt (← lift (scalar.toInt (Size.ofBytes 4) |>.mapError ScalarOps.scalarError)))
    readU32 := fun op => do
      let scalar ← readImmediate h op
      pure (UInt32.ofNat (← lift (scalar.toUInt (Size.ofBytes 4) |>.mapError ScalarOps.scalarError)).toNat)
    isNull := fun ptr => do
      let value ← lift (Scalar.fromMaybePointer h.access.runtime.base ptr |>.mapError ScalarOps.scalarError)
      ValidityMachine.scalarMayBeNull value
    i32Place := fun ptr => PointerPlaceMachine.fromPointer h.access ptr h.i32Layout false
    libcI32
    timespecPlace := fun op => PointerPlaceMachine.dereference h.access h.pointerCompiler h.dynamic h.vtable h.dynamicFuel choice op
    readTimespec := h.readTimespec
    timeout := DeadlineMachine.timeout h.deadline
    noIsolation := fun name => do
      unless ← h.communicate do throw (.termination (.unsupportedInIsolation name))
    seqCstFence := do
      match ← lift (h.backend (← get)) with
      | .none | .vclocks _ => IntrinsicAtomic.fence h.atomic .SeqCst false
    readAcquire := fun place => do
      let value ← match ← lift (h.backend (← get)) with
        | .none | .vclocks _ => IntrinsicAtomic.load h.atomic choice ⟨.memory place.mplace,place.layout⟩ .Acquire
      pure (UInt32.ofNat (← lift (value.toUInt (Size.ofBytes 4) |>.mapError ScalarOps.scalarError)).toNat)
    metadata := metadata h
    newFutex := newFutex h
    wait := FutexRuntime.wait (runtime h choice)
    wake := FutexRuntime.wake (runtime h choice)
    errnoNegOne := fun name => IoError.setErrnoAndReturnNeg1 (ioErrors h choice) (.libc name)
    writeInt := writeInt h choice
    writeIsize := fun value dest => do
      let scalar ← lift (Scalar.fromInt value h.access.runtime.pointerSize |>.mapError ScalarOps.scalarError)
      writeScalar h choice scalar dest
    hostUsizeBits }
  bind h choice base
end Miri.Interpreter.LinuxFutexMachine
