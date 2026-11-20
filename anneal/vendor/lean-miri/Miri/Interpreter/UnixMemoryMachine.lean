import Miri.Memory.MiriMemoryKind
import Miri.Interpreter.UnixMemory
import Miri.Interpreter.ReallocationDriver
import Miri.Interpreter.RawMemoryMachine
import Miri.Interpreter.IoError
import Miri.Interpreter.FrameMetadataBindings
import Miri.Interpreter.PointerMachineBindings

/-! Concrete unix/mem.rs allocation/access bindings. Global addresses,
allocation extras, provenance and errno use canonical machine state. Exact
libc ABI/constants, imported type layouts, host errors and page configuration
remain required facts, never host-platform guesses. -/
namespace Miri.Interpreter.UnixMemoryMachine
open Miri.ABI Miri.Memory Miri.MIR Miri.Concurrency Miri.Memory.AllocAddresses
abbrev State U := PointerMachine.State MiriMemoryKind U
abbrev M U A := PointerMachine.M MiriMemoryKind U A

structure Hooks (U C Host Payload : Type) where
  allocation : ReallocationDriver.Hooks MiriMemoryKind U Payload
  compiler : PlaceMachine.CompilerHooks MiriMemoryKind (PointerMachine.User U) C
  frame : FrameMetadata.CompilerHooks MiriMemoryKind (PointerMachine.User U)
  errors : IoError.Hooks (State U) Host
  /-- Typed backing for ThreadRecord.lastErrorLocation's canonical AllocId token. -/
  errnoPlaces : U → Array (AllocId × MPlaceTy Provenance)
  putErrnoPlaces : U → Array (AllocId × MPlaceTy Provenance) → U
  u32Layout : LocalLayout
  unitPtrMut : LocalLayout
  pageSize : UInt64
  symbolicAlignment : Bool
  enforceAlignment : Bool

structure Choices where
  allocation : AddressRandomChoices
  reuse : Bool

private def liftResult (value : Except StepError A) : M U A :=
  match value with | .ok value => pure value | .error error => throw error
private def machineAction (action : PlaceMachine.MachineM MiriMemoryKind (PointerMachine.User U) A) : M U A := fun state =>
  match action state.machine with
  | .ok value machine => .ok value {state with machine}
  | .error error machine => .error error {state with machine}
private def kind : ForeignItems.AllocationKind → MiriMemoryKind
  | .rust => .rust | .c => .c | .miri => .miri | .mmap => .mmap

/-- Reuse-pool source distinguishes Stack from every other MemoryKind. -/
def driver (h : Hooks U C Host Payload) : AllocationDriver.Hooks MiriMemoryKind U Payload :=
  {h.allocation.driver with
    addressKind := fun allocationKind => pure (match allocationKind with | .stack => .stack | .callerLocation | .machine _ => .other)}

/-- Physical accesses share the same actual extras installed by allocation. -/
def access (h : Hooks U C Host Payload) :
    PlaceMachine.AccessConfig MiriMemoryKind (PointerMachine.User U) :=
  MemoryExtras.bindAccess h.allocation.driver.allocation.extras h.allocation.access

/-- Source init_allocation records spans after tree/race/weak initialization
only for kinds which request them. The original stack remains valid throughout
these machine-only initialization hooks; post-hook machine state is preserved. -/
def allocationForKind (h : Hooks U C Host Payload) (allocationKind : MiriMemoryKind) :
    M U (ReallocationDriver.Hooks MiriMemoryKind U Payload) := do
  let context ← get
  let config := h.allocation.allocation
  let tail := fun id size align => do
    config.allocationTail id size align
    if allocationKind.shouldSaveAllocationSpan then
      let machine ← get
      let span ← match AllocationDriver.currentUserRelevantSpan h.allocation.driver.spans {context with machine} with
        | .ok span state => set state.machine; pure span
        | .error error state => set state.machine; throw error
      modify fun machine => {machine with allocationSpans :=
        (machine.allocationSpans.filter fun entry => entry.1 != id).push (id,span,none)}
  return {h.allocation with allocation := {config with allocationTail := tail}, driver := driver h}

def writeScalar (h : Hooks U C Host Payload) (choice : C) (value : Scalar Provenance)
    (dest : MPlaceTy Provenance) : M U Unit :=
  writePlaceImmediate (PlaceMachine.placeHooks (access h) h.allocation.allocation h.compiler)
    choice (.scalar value) ⟨.memory dest.mplace,dest.layout⟩

def readScalar (h : Hooks U C Host Payload) (place : MPlaceTy Provenance) : M U (Scalar Provenance) := do
  let value ← PlaceMachine.readImmediate (access h) ⟨.indirect place.mplace,place.layout⟩
  liftResult (value.imm.toScalar.mapError ScalarOps.immediateError)

/-- Canonical shared symbolic-alignment promises, with a cached error instead
of immediate UB, exactly as ptr_to_mplace. No output memory is read here. -/
def misalignment (h : Hooks U C Host Payload) (pointer : Pointer (Option Provenance))
    (required : Align) : M U (Option Misalignment) := do
  let bytes ← liftResult (required.bytes.mapError fun error => .invalidProgram s!"alignment: {reprStr error}")
  if !h.enforceAlignment || bytes == 1 then return none
  let state ← get
  let resolved ← machineAction ((access h).resolvePointer state.machine.memory pointer 0)
  let mut override : Option Misalignment := none
  if let .ok resolved := resolved then
    let memory := (← get).machine.memory
    let info ← liftResult (memory.getAllocInfo resolved.allocId |>.mapError
      fun error => .callback s!"alignment allocation metadata: {reprStr error}")
    let promise := ((← get).machine.user.symbolicAlignment.find? fun entry => entry.1 == resolved.allocId).map
      fun entry => (entry.2.1,entry.2.2)
    override ← liftResult (PointerMachine.symbolicAlignment h.symbolicAlignment info.kind info.align promise resolved.offset required
      |>.mapError fun error => .invalidProgram s!"alignment metadata: {reprStr error}")
  match checkPtrAlign pointer required true (fun _ _ => resolved) (← get).machine.memory.getAllocInfo
      (fun _ _ _ _ _ => override) with
  | .ok () => return none
  | .error (.alignmentCheckFailed error) => return some error
  | .error error => throw (.invalidProgram s!"pointer alignment invariant: {reprStr error}")

def derefPointerOutput (h : Hooks U C Host Payload) (operand : OpTy Provenance) : M U (MPlaceTy Provenance) := do
  let value ← PlaceMachine.readImmediate (access h) operand
  let scalar ← liftResult (value.imm.toScalar.mapError ScalarOps.immediateError)
  let pointer ← liftResult (scalar.toPointer h.allocation.access.runtime.base |>.mapError ScalarOps.scalarError)
  let misaligned ← misalignment h pointer h.unitPtrMut.layout.align.abi
  return ⟨⟨pointer,.none,misaligned⟩,h.unitPtrMut⟩

/-- mprotect/madvise only check bounds, not memory-read/TB/race access. Real
access failures are returned for source remapping; unavailable metadata throws. -/
def checkAccess (h : Hooks U C Host Payload) (pointer : Pointer (Option Provenance))
    (length : UInt64) : M U (Except Unit Unit) := do
  let size := Size.ofBytes length
  let signed ← match sizeAsI64 size with
    | .ok size => pure size | .error _ => return .error ()
  if signed == 0 then return .ok ()
  let resolved ← machineAction ((access h).resolvePointer (← get).machine.memory pointer signed)
  match checkPtrAccess h.allocation.driver.pointer.arithmetic pointer size .memoryAccess
      (fun _ _ => resolved) (← get).machine.memory.getAllocInfo with
  | .ok () => return .ok ()
  | .error (.allocationLookup (.unavailable id)) => throw (.callback s!"missing allocation metadata {id.value}")
  | .error (.malformedAlignment error) => throw (.invalidProgram s!"alignment metadata: {reprStr error}")
  | .error (.pointerArithmetic error) => throw (.invalidProgram s!"pointer arithmetic: {reprStr error}")
  | .error _ => return .error ()

/-- Source Thread::visit_provenance visits last_error, including retained
terminated threads. Only actual thread tokens are roots; stale table entries
are not promoted to roots. The caller can feed these places to its GC visitor. -/
def errnoRootPlaces (h : Hooks U C Host Payload) (state : State U) :
    Except StepError (Array (MPlaceTy Provenance)) := do
  let mut roots := #[]
  for thread in state.machine.threads.threads do
    if let some token := thread.lastErrorLocation then
      let entries := (h.errnoPlaces state.machine.user.payload).filter (fun entry => entry.1.value.toNat == token)
      let some (_,place) := entries[0]? | throw (.invalidProgram "errno root token has no typed pointer")
      unless entries.size == 1 && place.layout == h.u32Layout do throw (.invalidProgram "errno root metadata mismatch")
      roots := roots.push place
  return roots

/-- Actual per-thread errno storage, allocated lazily with Machine ownership.
The side table retains the original full u32 layout and pointer provenance. -/
def errorHooks (h : Hooks U C Host Payload) (choice : C) (choices : Choices) : IoError.Hooks (State U) Host :=
  {h.errors with
    getLastErrorPlace := do
      let state ← get
      let some thread := state.machine.threads.activeThread? | throw (.invalidProgram "errno active thread missing")
      let some token := thread.lastErrorLocation | return none
      let entries := (h.errnoPlaces state.machine.user.payload).filter (fun entry => entry.1.value.toNat == token)
      let some (_,place) := entries[0]? | throw (.invalidProgram "errno token has no typed pointer")
      unless entries.size == 1 && place.layout == h.u32Layout do throw (.invalidProgram "errno pointer metadata mismatch")
      return some place
    setLastErrorPlace := fun place => do
      let some provenance := place.mplace.ptr.provenance |
        throw (.invalidProgram "errno place has no provenance")
      let some id := PointerProvenance.getAllocId provenance |
        throw (.invalidProgram "errno place has no allocation provenance")
      let state ← get
      let manager := state.machine.threads
      let some thread := manager.activeThread? | throw (.invalidProgram "errno active thread missing")
      let thread := {thread with lastErrorLocation := some id.value.toNat}
      let payload := h.putErrnoPlaces state.machine.user.payload
        (((h.errnoPlaces state.machine.user.payload).filter fun entry => entry.1 != id).push (id,place))
      set {state with machine := {state.machine with
        threads := {manager with threads := manager.threads.set manager.activeThread.toNat thread}
        user := {state.machine.user with payload}}}
    allocateU32Machine := do
      unless h.u32Layout.layout.isSized && h.u32Layout.layout.size.bytes == 4 do
        throw (.invalidProgram "compiler u32 layout mismatch")
      let allocation ← allocationForKind h .machine
      let pointer ← ReallocationDriver.allocate allocation h.u32Layout.layout.size h.u32Layout.layout.align.abi
        (.machine .machine) .Uninit choices.allocation
      return ⟨⟨pointer.withOptionalProvenance,.none,none⟩,h.u32Layout⟩
    writeScalar := writeScalar h choice
    readScalar := readScalar h
    writeInt := fun value dest => do
      let scalar ← liftResult (Scalar.fromInt value dest.layout.layout.size |>.mapError ScalarOps.scalarError)
      writeScalar h choice scalar dest
    scalarI32 := fun value => liftResult (value.toInt32.mapError ScalarOps.scalarError)
    scalarU32 := fun value => liftResult (value.toUInt32.mapError ScalarOps.scalarError)}

/-- Concrete foreign allocation operations, preserving the source memory kind
and actual align/old-layout values. All random choices remain explicit inputs. -/
def foreign (h : Hooks U C Host Payload) (choice : C) (choices : Choices)
    (base : ForeignItems.Hooks Provenance (State U) D (MPlaceTy Provenance) (Pointer (Option Provenance)) B I) :=
  let errors := errorHooks h choice choices
  {base with
    readPointer := fun operand => do
      let value ← PlaceMachine.readImmediate (access h) operand
      let scalar ← liftResult (value.imm.toScalar.mapError ScalarOps.immediateError)
      liftResult (scalar.toPointer h.allocation.access.runtime.base |>.mapError ScalarOps.scalarError)
    readUsize := fun operand => do
      let value ← PlaceMachine.readImmediate (access h) operand
      let scalar ← liftResult (value.imm.toScalar.mapError ScalarOps.immediateError)
      liftResult (scalar.toTargetUsize h.allocation.driver.pointer.arithmetic.pointerSize |>.mapError ScalarOps.scalarError)
    readI32 := fun operand => do
      let value ← PlaceMachine.readImmediate (access h) operand
      let scalar ← liftResult (value.imm.toScalar.mapError ScalarOps.immediateError)
      liftResult (scalar.toInt32.mapError ScalarOps.scalarError)
    transmute := fun operand layout => do
      let cx ← h.compiler.projection choice
      liftResult (OpTy.transmute cx operand layout |>.mapError
        fun error => .invalidProgram s!"shim operand transmute: {reprStr error}")
    allocate := fun size align init allocationKind => do
      let allocation ← allocationForKind h (kind allocationKind)
      let pointer ← ReallocationDriver.allocate allocation (Size.ofBytes size) align (.machine (kind allocationKind))
        (match init with | .uninit => .Uninit | .zero => .Zero) choices.allocation
      return pointer.withOptionalProvenance
    deallocate := fun pointer old allocationKind =>
      AllocationDriver.deallocate (driver h) choices.reuse pointer
        (old.map fun (size,align) => (Size.ofBytes size,align)) (.machine (kind allocationKind))
    reallocate := fun pointer old size align allocationKind => do
      let allocation ← allocationForKind h (kind allocationKind)
      let pointer ← ReallocationDriver.reallocate allocation pointer
        (old.map fun (size,align) => (Size.ofBytes size,align)) (Size.ofBytes size) align
        (.machine (kind allocationKind)) .Uninit choices.allocation choices.reuse
      return pointer.withOptionalProvenance
    writePointer := fun pointer dest => do
      let value ← liftResult (Scalar.fromMaybePointer h.allocation.access.runtime.base pointer |>.mapError ScalarOps.scalarError)
      writeScalar h choice value dest
    writeNull := fun dest => do
      let value ← liftResult (Scalar.fromInt 0 dest.layout.layout.size |>.mapError ScalarOps.scalarError)
      writeScalar h choice value dest
    isNull := fun pointer => pure (pointer.offset.bytes == 0)
    setEnomem := IoError.setLastError errors (.libc "ENOMEM")}

/-- Exact ABI/off_t and libc constants stay compiler queries. Pointer-output
places and offset values are obtained from actual operand reads. -/
def bind (h : Hooks U C Host Payload) (choice : C) (choices : Choices)
    (base : UnixMemory.Hooks Provenance (State U) D (MPlaceTy Provenance) B I) :
    M U (UnixMemory.Hooks Provenance (State U) D (MPlaceTy Provenance) B I) := do
  let maximum ← liftResult (h.allocation.driver.pointer.arithmetic.targetIsizeMax |>.mapError
    fun error => .invalidProgram s!"target isize maximum: {reprStr error}")
  let errors := errorHooks h choice choices
  return FrameMetadataBindings.unixMemory h.frame {base with
    foreign := foreign h choice choices base.foreign
    pointerSize := h.allocation.driver.pointer.arithmetic.pointerSize.bytes
    pageSize := h.pageSize
    targetIsizeMax := UInt64.ofInt maximum.toInt
    setErrno := fun name => IoError.setLastError errors (.libc name)
    libcI32 := fun name => do
      let value ← h.errors.libc name
      liftResult (value.toInt32.mapError ScalarOps.scalarError)
    mapFailed := h.errors.libc "MAP_FAILED"
    writeScalar := writeScalar h choice
    writeI32 := fun value dest => do
      let scalar ← liftResult (Scalar.fromInt value.toInt (Size.ofBytes 4) |>.mapError ScalarOps.scalarError)
      writeScalar h choice scalar dest
    derefPointerOutput := derefPointerOutput h
    readOffset := fun operand => do
      let value ← PlaceMachine.readImmediate (access h) operand
      let scalar ← liftResult (value.imm.toScalar.mapError ScalarOps.immediateError)
      liftResult (scalar.toInt operand.layout.layout.size |>.mapError ScalarOps.scalarError)
    checkAccess := checkAccess h}
end Miri.Interpreter.UnixMemoryMachine
