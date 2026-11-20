import Miri.Input.CompilerProviders
import Miri.Input.CompilerNamedShimAbi
import Miri.Input.CompilerPrimitiveFacts
import Miri.Input.CompilerLibcConstants
import Miri.Input.CompilerFrameMetadata
import Miri.Input.EvalHostRuntimeConstruction
import Miri.Interpreter.LinuxMemory
import Miri.Interpreter.UnixMemoryMachine
import Miri.Interpreter.ShimSignatures
import Miri.Interpreter.FrameMetadata
import Miri.Interpreter.UnixEnvironmentDispatch

/-! Build the source Unix/Linux memory shims over the execution's canonical
memory, allocation, provenance, Tree Borrows and errno state. Host resources
do not participate in these operations. -/
namespace Miri.Input.EvalUnixMemoryConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev RuntimeState (U : Type) := EvalHostRuntimeConstruction.RuntimeState U
abbrev M (U A : Type) := EvalHostRuntimeConstruction.RuntimeM U A

private def lift (result : Except StepError A) : M U A :=
  match result with
  | .ok value => pure value
  | .error error => throw error

private def sourceKind : ForeignItems.AllocationKind → MiriMemoryKind
  | .rust => .rust
  | .c => .c
  | .miri => .miri
  | .mmap => .mmap

private def allocationForKind
    (memory : EvalHostRuntimeConstruction.EnvironmentMemory U C Payload)
    (spans : AllocationDriver.SpanHooks) (kind : MiriMemoryKind) :
    M U (PlaceMachine.AllocationConfig MiriMemoryKind (PointerMachine.User U)) := do
  let context ← get
  let config := memory.allocation
  let tail := fun id size align => do
    config.allocationTail id size align
    if kind.shouldSaveAllocationSpan then
      let machine ← get
      let span ← match AllocationDriver.currentUserRelevantSpan spans {context with machine} with
        | .ok span state => set state.machine; pure span
        | .error error state => set state.machine; throw error
      modify fun state => {state with allocationSpans :=
        (state.allocationSpans.filter fun entry => entry.1 != id).push (id,span,none)}
  pure {config with allocationTail := tail}

private def allocationCreation
    (memory : EvalHostRuntimeConstruction.EnvironmentMemory U C Payload)
    (extras : MemoryExtras.Hooks MiriMemoryKind (PointerMachine.User U) Payload)
    (spans : AllocationDriver.SpanHooks) (kind : MiriMemoryKind) :
    M U (ReallocationDriver.CreationHooks MiriMemoryKind U Payload) := do
  let state ← get
  let allocation ← allocationForKind memory spans kind
  pure {
    extras
    allocation
    weakMemory := state.machine.dataRace.any (·.weakMemory)
    globalKind := memory.access.globalKind.map MemoryKind.machine
  }

private def readScalar
    (access : PlaceMachine.AccessConfig MiriMemoryKind (PointerMachine.User U))
    (operand : OpTy Provenance) : M U (Scalar Provenance) := do
  let immediate ← PlaceMachine.readImmediate access operand
  lift (immediate.imm.toScalar.mapError ScalarOps.immediateError)

private def readPointer
    (access : PlaceMachine.AccessConfig MiriMemoryKind (PointerMachine.User U))
    (operand : OpTy Provenance) : M U (Pointer (Option Provenance)) := do
  lift ((← readScalar access operand).toPointer access.runtime.base
    |>.mapError ScalarOps.scalarError)

private def readUsize
    (access : PlaceMachine.AccessConfig MiriMemoryKind (PointerMachine.User U))
    (arithmetic : PointerArithmetic) (operand : OpTy Provenance) : M U UInt64 := do
  lift ((← readScalar access operand).toTargetUsize arithmetic.pointerSize
    |>.mapError ScalarOps.scalarError)

private def readI32
    (access : PlaceMachine.AccessConfig MiriMemoryKind (PointerMachine.User U))
    (operand : OpTy Provenance) : M U Int32 := do
  lift ((← readScalar access operand).toInt32 |>.mapError ScalarOps.scalarError)

private def misalignment
    (access : PlaceMachine.AccessConfig MiriMemoryKind (PointerMachine.User U))
    (symbolicAlignment enforceAlignment : Bool)
    (pointer : Pointer (Option Provenance)) (required : Align) :
    M U (Option Misalignment) := do
  let bytes ← lift (required.bytes.mapError fun error =>
    .invalidProgram s!"alignment: {reprStr error}")
  if !enforceAlignment || bytes == 1 then return none
  let state ← get
  let resolved ← match access.resolvePointer state.machine.memory pointer 0 state.machine with
    | .ok result machine => set {state with machine}; pure result
    | .error error machine => set {state with machine}; throw error
  let mut override : Option Misalignment := none
  if let .ok resolved := resolved then
    let info ← match state.machine.memory.getAllocInfo resolved.allocId with
      | .ok value => pure value
      | .error error => throw (.callback s!"alignment allocation metadata: {reprStr error}")
    let promise := (state.machine.user.symbolicAlignment.find?
      fun entry => entry.1 == resolved.allocId).map fun entry => (entry.2.1,entry.2.2)
    override ← lift (PointerMachine.symbolicAlignment symbolicAlignment info.kind info.align
      promise resolved.offset required |>.mapError fun error =>
        .invalidProgram s!"alignment metadata: {reprStr error}")
  match checkPtrAlign pointer required true (fun _ _ => resolved)
      state.machine.memory.getAllocInfo (fun _ _ _ _ _ => override) with
  | .ok () => return none
  | .error (.alignmentCheckFailed error) => return some error
  | .error error => throw (.invalidProgram s!"pointer alignment invariant: {reprStr error}")

private def checkAccess
    (access : PlaceMachine.AccessConfig MiriMemoryKind (PointerMachine.User U))
    (arithmetic : PointerArithmetic) (pointer : Pointer (Option Provenance))
    (length : UInt64) : M U (Except Unit Unit) := do
  let size := Size.ofBytes length
  let signed ← match sizeAsI64 size with
    | .ok value => pure value
    | .error _ => return .error ()
  if signed == 0 then return .ok ()
  let state ← get
  let resolved ← match access.resolvePointer state.machine.memory pointer signed state.machine with
    | .ok value machine => set {state with machine}; pure value
    | .error error machine => set {state with machine}; throw error
  -- `resolvePointer` is a stateful machine action. Preserve its effects even
  -- when the allocation is invalid, as the Place access path does.
  match resolved with
  | .error _error =>
    return .error ()
  | .ok resolved =>
    match checkPtrAccess arithmetic pointer size .memoryAccess
        (fun _ _ => .ok resolved) (← get).machine.memory.getAllocInfo with
    | .ok () => return .ok ()
    | .error (.allocationLookup (.unavailable id)) =>
      throw (.callback s!"missing allocation metadata {id.value}")
    | .error (.malformedAlignment error) =>
      throw (.invalidProgram s!"alignment metadata: {reprStr error}")
    | .error (.pointerArithmetic error) =>
      throw (.invalidProgram s!"pointer arithmetic: {reprStr error}")
    | .error _ => return .error ()

/-! `fromSource` derives target layouts, constants, frame policy and ABI from
the prepared compiler. The supplied memory bundle is the one used by MIR, so
pointer-output writes and remap allocation retain the live execution state. -/
def fromSource [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (userRelevantCrates : Array Nat)
    (environment : UnixEnvironmentDispatch.Hooks (RuntimeState U) Os E EnvVars.Kind)
    (signatures : ShimSignatures.Hooks Provenance (RuntimeState U) Place
      (MPlaceTy Provenance) (Pointer (Option Provenance)) B I)
    (memory : EvalHostRuntimeConstruction.EnvironmentMemory U C Payload)
    (extras : MemoryExtras.Hooks MiriMemoryKind (PointerMachine.User U) Payload)
    (spans : AllocationDriver.SpanHooks)
    (place : PlaceHooks Provenance (RuntimeState U) C MachineHooks.FrameExtra)
    (choice : C) (pageSize : UInt64) :
    Except StepError (LinuxMemory.Hooks (RuntimeState U) Place B I) := do
  let target ← p.externStatics.targetFacts |>.mapError StepError.unsupported
  unless (target.os == "linux" || target.os == "android") && target.families.contains "unix" do
    throw (.invalidProgram s!"Linux memory hooks requested for `{target.os}`")
  let usize ← p.primitiveLayout "usize" |>.mapError StepError.unsupported
  let isize ← p.primitiveLayout "isize" |>.mapError StepError.unsupported
  let unitPtrMut ← p.primitiveLayout "unit_pointer_mut"
    |>.mapError StepError.unsupported
  let targetIsizeMax ← isize.layout.size.signedIntMax |>.mapError
    (fun error => StepError.unsupported s!"target isize max: {error}")
  let frame := CompilerFrameMetadata.hooks p.lifecycle.frames userRelevantCrates
  let access := MemoryExtras.bindAccess extras memory.access
  let arithmetic := memory.pointers.arithmetic
  let abi := CompilerNamedShimAbi.query p.namedAbi
  let libcI32 := fun name => do
    let scalar : Scalar Provenance ← lift (CompilerLibcConstants.scalar p.namedConstants name
      |>.mapError StepError.unsupported)
    match scalar.toInt32 with
    | .ok value => pure value
    | .error error => throw (ScalarOps.scalarError error)
  let writeScalar := fun scalar destination =>
    writePlaceImmediate place choice (.scalar scalar)
      ⟨.memory destination.mplace,destination.layout⟩
  let writeI32 := fun value destination => do
    let scalar ← lift (Scalar.fromInt value.toInt (Size.ofBytes 4)
      |>.mapError ScalarOps.scalarError)
    writeScalar scalar destination
  let foreign := {signatures.foreign with
    readPointer := readPointer access
    readUsize := readUsize access arithmetic
    readI32 := readI32 access
    transmute := fun operand layout => do
      let cx ← place.projection choice
      lift (OpTy.transmute cx operand layout |>.mapError
        fun error => .invalidProgram s!"shim operand transmute: {reprStr error}")
    allocate := fun size align init allocationKind => do
      let kind := sourceKind allocationKind
      let creation ← allocationCreation memory extras spans kind
      let pointer ← ReallocationDriver.allocateSourceFrom creation (Size.ofBytes size) align
        (.machine kind) (match init with | .uninit => .Uninit | .zero => .Zero)
      return pointer.withOptionalProvenance
    deallocate := fun pointer old allocationKind =>
      memory.deallocate pointer (old.map fun (size,align) => (Size.ofBytes size,align))
        (.machine (sourceKind allocationKind))
    reallocate := fun pointer old size align allocationKind => do
      let kind := sourceKind allocationKind
      let creation ← allocationCreation memory extras spans kind
      let pointer ← ReallocationDriver.reallocateFrom access creation arithmetic
        memory.deallocate pointer (old.map fun (size,align) => (Size.ofBytes size,align))
        (Size.ofBytes size) align (.machine kind) .Uninit
      return pointer.withOptionalProvenance
    writePointer := fun pointer destination => do
      let scalar ← lift (Scalar.fromMaybePointer access.runtime.base pointer
        |>.mapError ScalarOps.scalarError)
      writeScalar scalar destination
    isNull := fun pointer => pure (pointer.provenance.isNone && pointer.offset.bytes == 0)
    setEnomem := IoError.setLastError environment.env.errors (.libc "ENOMEM")}
  let unix : UnixMemory.Hooks Provenance (RuntimeState U) Place
      (MPlaceTy Provenance) B I := {
    foreign
    pointerSize := usize.layout.size.bytes
    pageSize
    targetIsizeMax := UInt64.ofInt targetIsizeMax
    frameInStd := FrameMetadata.frameInStd frame
    libcI32
    setErrno := fun name => IoError.setLastError environment.env.errors (.libc name)
    mapFailed := lift (CompilerLibcConstants.scalar p.namedConstants "MAP_FAILED"
      |>.mapError StepError.unsupported)
    writeScalar
    writeI32
    derefPointerOutput := fun operand => do
      let scalar ← readScalar access operand
      let pointer ← lift (scalar.toPointer access.runtime.base |>.mapError ScalarOps.scalarError)
      let bad ← misalignment access memory.symbolicAlignment memory.enforceAlignment
        pointer unitPtrMut.layout.align.abi
      return ⟨⟨pointer,.none,bad⟩,unitPtrMut⟩
    expectedAbi := abi
    readOffset := fun operand => do
      let offT ← match CompilerPrimitiveFacts.offTLayout p.runtime with
        | .ok value => pure value
        | .error reason => throw (.unsupported s!"compiler off_t layout: {reason}")
      lift ((← readScalar access operand).toInt offT.layout.size
        |>.mapError ScalarOps.scalarError)
    checkAccess := checkAccess access arithmetic }
  let linux := LinuxMemory.Hooks.mk unix (fun pointer oldSize newSize align => do
    let kind := MemoryKind.machine MiriMemoryKind.mmap
    let creation ← allocationCreation memory extras spans .mmap
    let pointer ← ReallocationDriver.reallocateFrom access creation arithmetic
      memory.deallocate pointer (some (oldSize,align)) (newSize) align kind .Zero
    return pointer.withOptionalProvenance)
  pure linux

end Miri.Input.EvalUnixMemoryConstruction
