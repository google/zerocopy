import Miri.Input.RuntimeArrayQueries
import Miri.Input.CompilerExternStatic
import Miri.Interpreter.RawMemoryMachine
import Miri.Interpreter.OsStringMachine
import Miri.Interpreter.EnvVars
import Miri.Interpreter.ExternStatic
import Miri.Interpreter.ReallocationDriver
import Miri.Interpreter.FunctionPointers
import Miri.Interpreter.UnixDynamic
import Miri.Interpreter.WindowsPlatform
import Miri.Memory.MiriMemoryKind

/-! Construct target OS-string operations from the canonical machine memory
and allocation engines. Only host `OsStr` representation/conversion remains a
host capability; target byte/UTF-16 access and array allocation use Miri state.
-/
namespace Miri.Input.EvalHostRuntimeConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev RuntimeState (U : Type) := MachineHooks.State MiriMemoryKind (PointerMachine.User U)
abbrev RuntimeM (U A : Type) := MachineHooks.M MiriMemoryKind (PointerMachine.User U) A

/-! These operations are properties of the actual host `OsStr` implementation.
They are intentionally separate from target memory operations below. -/
structure OsHostEffects (Os : Type) where
  hostWindows : Bool
  hostUnix : Bool
  targetWindows : Bool
  fromUnixBytes : ByteArray → Os
  fromUtf8 : ByteArray → Except StepError Os
  fromWide : Array UInt16 → Except StepError Os
  toWide : Os → Except StepError (Array UInt16)
  encodedBytes : Os → ByteArray
  encodedLength : Os → Nat
  decodeUnixBytes : ByteArray → Except StepError Os
  empty : Os
  concat : Os → Os → Os
  ascii : String → Os
  isEmpty : Os → Bool
  containsEquals : Os → Bool

structure EnvironmentLens (U Os : Type) where
  get : PointerMachine.User U → EnvVars.State (Option Provenance) Os
  set : PointerMachine.User U → EnvVars.State (Option Provenance) Os → PointerMachine.User U

structure ExternStaticLens (U : Type) where
  get : PointerMachine.User U → ExternStatic.State
  set : PointerMachine.User U → ExternStatic.State → PointerMachine.User U

structure ExternStaticTarget where
  os : String
  env : String
  families : Array String

def ExternStaticTarget.fromCompiler (facts : CompilerExternStatic.TargetFacts) : ExternStaticTarget :=
  ⟨facts.os,facts.env,facts.families⟩

structure EnvironmentHostEffects (U : Type) where
  invalidArgument : RuntimeM U Int32
  envVarNotFound : RuntimeM U Unit

structure EnvironmentMemory (U C Payload : Type) where
  access : PlaceMachine.AccessConfig MiriMemoryKind (PointerMachine.User U)
  allocation : PlaceMachine.AllocationConfig MiriMemoryKind (PointerMachine.User U)
  /-- Operation-local source deallocation. This runs in the real MachineHooks
  state so current span, free allocation identity, address reuse, and all
  partial effects observe the active frame instead of a captured startup state. -/
  deallocate : Pointer (Option Provenance) → Option (Size × Align) →
    MemoryKind MiriMemoryKind → RuntimeM U Unit
  pointers : PointerMachine.Hooks MiriMemoryKind U
  projection : PlaceProjectionHooks Provenance (RuntimeState U) C MachineHooks.FrameExtra
  arrays : RuntimeArrayQueries.Access (RuntimeState U)
  symbolicAlignment : Bool
  enforceAlignment : Bool
  stringScanBudget : Nat
  choice : C
  pointerTy : TyId
  pointerLayout : LocalLayout

private def machineKind : EnvVars.Kind → MiriMemoryKind
  | .machine => .machine
  | .externStatic => .externStatic
  | .runtime => .runtime
  | .winLocal => .winLocal

private def memoryKind (kind : EnvVars.Kind) : MemoryKind MiriMemoryKind :=
  .machine (machineKind kind)

private def lift (value : Except StepError A) : RuntimeM U A :=
  match value with | .ok result => pure result | .error error => throw error

private def scanCString [DecidableEq MiriMemoryKind]
    (access : PlaceMachine.AccessConfig MiriMemoryKind (PointerMachine.User U))
    (pointer : PointerMachine.Hooks MiriMemoryKind U)
    (budget : Nat) (base : Pointer (Option Provenance)) : RuntimeM U ByteArray := do
  let rec scan (fuel length : Nat) : RuntimeM U UInt64 := do
    match fuel with
    | 0 => throw (.resourceExhaustion "C string scan budget")
    | fuel + 1 =>
      if length >= 2^64 then throw (.invalidProgram "C string length overflow")
      let location ← match RawMemoryMachine.offset pointer.arithmetic base (UInt64.ofNat length) with
        | .ok value => pure value
        | .error error => throw error
      if (← RawMemoryMachine.readByte access pointer.arithmetic location) == 0 then
        return UInt64.ofNat length
      scan fuel (length + 1)
  let length ← scan budget 0
  let bytes ← RawMemoryMachine.readBytes access pointer.arithmetic base length
  unless bytes.size == length.toNat do throw (.invalidProgram "C string byte-read length mismatch")
  return bytes

/-- Build `OsStrings.Hooks` with the source access and allocation records. The
array type identity is interned in the same persistent runtime-type world used
by EntryArguments; byte-size coincidence never substitutes for `Ty::new_array`.
-/
def osStrings [DecidableEq MiriMemoryKind]
    (host : OsHostEffects Os)
    (access : PlaceMachine.AccessConfig MiriMemoryKind (PointerMachine.User U))
    (allocation : PlaceMachine.AllocationConfig MiriMemoryKind (PointerMachine.User U))
    (pointer : PointerMachine.Hooks MiriMemoryKind U)
    (arrays : RuntimeArrayQueries.Access (RuntimeState U))
    (symbolicAlignment enforceAlignment : Bool)
    (budget : Nat) :
    OsStrings.Hooks Provenance (RuntimeState U) Os EnvVars.Kind := by
  let osPointer : OsStringMachine.Hooks MiriMemoryKind U :=
    ⟨access,pointer,symbolicAlignment,enforceAlignment⟩
  exact {
    hostWindows := host.hostWindows
    hostUnix := host.hostUnix
    targetWindows := host.targetWindows
    fromUnixBytes := host.fromUnixBytes
    fromUtf8 := host.fromUtf8
    fromWide := host.fromWide
    toWide := host.toWide
    encodedBytes := host.encodedBytes
    encodedLength := host.encodedLength
    readCString := scanCString access pointer budget
    readWideString := OsStringMachine.readWideString osPointer budget
    writeCString := RawMemoryMachine.writeCString access pointer.arithmetic
    writeWideString := OsStringMachine.writeWideString osPointer
    arrayLayout := fun wide count => do
      let state ← get
      match RuntimeArrayTypes.osStringArray (arrays.get state) wide count with
      | .error error => throw (.unsupported s!"runtime OS-string array layout: {reprStr error}")
      | .ok (layout,world) =>
        set (arrays.set state world)
        pure layout
    allocate := fun layout kind => do
      unless layout.layout.isSized do throw (.invalidProgram "unsized OS-string array allocation")
      let result ← ReallocationDriver.allocateConfigured allocation layout.layout.size
        layout.layout.align.abi (memoryKind kind) .Uninit
      return result.withOptionalProvenance }

def osStringsFromMemory (host : OsHostEffects Os)
    (memory : EnvironmentMemory U C Payload) :
    OsStrings.Hooks Provenance (RuntimeState U) Os EnvVars.Kind :=
  osStrings host memory.access memory.allocation memory.pointers memory.arrays
    memory.symbolicAlignment memory.enforceAlignment memory.stringScanBudget

/-- Source environment allocation and pointer-cell operations built from the
same canonical access, allocation and projection engines as MIR. State access
is only a lens into `MachineGCRoots.Storage`; no parallel environment map is
created. Host errno/Win32-not-found effects remain explicit. -/
def envVars [DecidableEq MiriMemoryKind]
    (host : OsHostEffects Os)
    (hostEffects : EnvironmentHostEffects U)
    (lens : EnvironmentLens U Os)
    (family : ForeignItems.Family)
    (strings : OsStrings.Hooks Provenance (RuntimeState U) Os EnvVars.Kind)
    (access : PlaceMachine.AccessConfig MiriMemoryKind (PointerMachine.User U))
    (deallocate : Pointer (Option Provenance) → EnvVars.Kind → RuntimeM U Unit)
    (machinePointers : PointerMachine.Hooks MiriMemoryKind U)
    (projection : PlaceProjectionHooks Provenance (RuntimeState U) C MachineHooks.FrameExtra)
    (arrays : RuntimeArrayQueries.Access (RuntimeState U))
    (choice : C) (pointerTy : TyId) (pointerLayout : LocalLayout) :
    EnvVars.Hooks (Option Provenance) Os (RuntimeState U) := by
  let allocateCString := fun (bytes : ByteArray) (kind : EnvVars.Kind) => do
    if bytes.size + 1 >= 2^64 then throw (StepError.invalidProgram "environment C string length overflow")
    let count := UInt64.ofNat (bytes.size + 1)
    let layout ← strings.arrayLayout false count
    let allocated ← strings.allocate layout kind
    RawMemoryMachine.writeBytes access machinePointers.arithmetic allocated ⟨bytes.data.push 0⟩
    pure allocated
  let allocatePointerBuffer := fun (count : Nat) (kind : EnvVars.Kind) => do
    if count >= 2^64 then throw (StepError.invalidProgram "environment pointer array length overflow")
    let layout ← RuntimeArrayQueries.arrayLayout arrays pointerTy (UInt64.ofNat count)
    strings.allocate layout kind
  let projectElement := fun (pointer : Pointer (Option Provenance)) (total index : Nat) => do
    if total >= 2^64 || index >= total then throw (StepError.invalidProgram "environment array index out of bounds")
    let count := UInt64.ofNat total
    let layout ← RuntimeArrayQueries.arrayLayout arrays pointerTy count
    let parent : RuntimePlace Provenance := ⟨.memory ⟨pointer,.none,none⟩,layout⟩
    let element ← PlaceDynamic.index projection choice parent (UInt64.ofNat index)
    match element.ref with
    | .memory place => pure place.ptr
    | .local .. => throw (StepError.invalidProgram "environment pointer array projection became local")
  let readPointer := fun (pointer : Pointer (Option Provenance)) => do
    let operand : OpTy Provenance := ⟨.indirect ⟨pointer,.none,none⟩,pointerLayout⟩
    let value ← PlaceMachine.readImmediate access operand
    let scalar ← match value.imm.toScalar with
      | .ok scalar => pure scalar
      | .error error => throw (ScalarOps.immediateError error)
    match scalar.toPointer access.runtime.base with
    | .ok pointer => pure pointer
    | .error error => throw (ScalarOps.scalarError error)
  -- EnvVars.Hooks.writePointer follows the source helper order
  -- `(value, destination)`: initUnix writes the environment block into the
  -- `environ` cell, and allocEnvironmentBlock writes each value into its slot.
  let writePointer := fun (value pointer : Pointer (Option Provenance)) => do
    let scalar ← match Scalar.fromMaybePointer access.runtime.base value with
      | .ok scalar => pure scalar
      | .error error => throw (ScalarOps.scalarError error)
    let dest : RuntimePlace Provenance := ⟨.memory ⟨pointer,.none,none⟩,pointerLayout⟩
    writePlaceImmediate projection.place choice (.scalar scalar) dest
  exact {
    family
    get := do return lens.get (← get).machine.user
    put := fun value => modify fun state =>
      {state with machine := {state.machine with user := lens.set state.machine.user value}}
    encodeUnix := fun value => pure (host.encodedBytes value)
    decodeUnix := fun bytes => lift (host.decodeUnixBytes bytes)
    emptyOs := host.empty
    concatOs := host.concat
    asciiOs := host.ascii
    isEmpty := host.isEmpty
    containsEquals := host.containsEquals
    nullPointer := Pointer.null
    isNull := fun pointer => pure (pointer.provenance.isNone && pointer.offset.bytes == 0)
    readCString := fun pointer => strings.readCString pointer
    allocCString := allocateCString
    allocPointerCell := fun kind => strings.allocate pointerLayout kind
    allocPointerArray := allocatePointerBuffer
    projectPointerElement := projectElement
    readPointer
    writePointer
    offset := fun ptr amount =>
      match RawMemoryMachine.offset machinePointers.arithmetic ptr amount with
      | .ok pointer => pure pointer
      | .error error => throw error
    deallocate
    invalidArgument := hostEffects.invalidArgument
    readWideString := fun pointer => OsStrings.readOsWideString strings pointer
    writeWideString := fun value pointer capacity => do
      OsStrings.writeOsWideString strings value pointer capacity.toUInt64
    allocWideString := fun value kind => OsStrings.allocOsString strings value kind true
    envVarNotFound := hostEffects.envVarNotFound }

def envVarsFromSource [DecidableEq MiriMemoryKind]
    (host : OsHostEffects Os) (hostEffects : EnvironmentHostEffects U)
    (lens : EnvironmentLens U Os) (family : ForeignItems.Family)
    (memory : EnvironmentMemory U C Payload) :
    EnvVars.Hooks (Option Provenance) Os (RuntimeState U) :=
  envVars host hostEffects lens family (osStringsFromMemory host memory)
    memory.access (fun pointer kind => memory.deallocate pointer none (memoryKind kind))
    memory.pointers memory.projection memory.arrays
    memory.choice memory.pointerTy memory.pointerLayout

private def strictAllocated (pointer : Pointer (Option Provenance)) : RuntimeM U StrictPointer :=
  match pointer.intoPointerOrAddr with
  | .ok pointer => pure pointer
  | .error _ => throw (StepError.invalidProgram "fresh extern-static allocation lacks provenance")

private def sourceDynSym (target : ExternStaticTarget) (name : String) : Bool :=
  if target.os == "windows" then (WindowsPlatform.DynamicSymbol.parse name).isSome
  else UnixDynamic.isDynamic target.os target.env name

/-- Construct `init_extern_statics` from real allocation, typed scalar writes,
the actual environment root, exact source dynamic-symbol allowlists and the
canonical FunctionPointers registry. `dynamicValue` only embeds the source
DynSym value into the caller's concrete `Other` representation. -/
def externStaticsFromSource [DecidableEq MiriMemoryKind]
    (target : ExternStaticTarget)
    (environment : EnvironmentLens U Os)
    (externStatics : ExternStaticLens U)
    (memory : EnvironmentMemory U C Payload)
    (functions : FunctionPointers.Hooks MiriMemoryKind (PointerMachine.User U) Other)
    (dynamicValue : String → Other)
    (u8Layout usizeLayout : LocalLayout) :
    ExternStatic.InitHooks (RuntimeState U) := by
  let allocateValue := fun (kind : ExternStatic.InitialValue) => do
    let layout := match kind with
      | .zeroByte => u8Layout
      | .nullPointer => usizeLayout
    unless layout.layout.isSized do
      throw (StepError.invalidProgram "extern-static value has unsized compiler layout")
    let value ← match kind with
      | .zeroByte =>
        if layout.layout.size.bytes != 1 then
          throw (StepError.invalidProgram "extern-static u8 compiler layout is not one byte")
        match (Scalar.fromInt (Prov := Provenance) 0 layout.layout.size :
            Except ScalarError (Scalar Provenance)) with
        | .ok value => pure value
        | .error error => throw (ScalarOps.scalarError error)
      | .nullPointer =>
        if layout.layout.size != memory.access.runtime.pointerSize then
          throw (StepError.invalidProgram "extern-static usize compiler layout disagrees with target pointer size")
        match Scalar.nullPointer memory.access.runtime.base with
        | .ok value => pure value
        | .error error => throw (ScalarOps.scalarError error)
    let pointer ← ReallocationDriver.allocateConfigured memory.allocation
      layout.layout.size layout.layout.align.abi (.machine .externStatic) .Uninit
    let place : RuntimePlace Provenance := ⟨.memory ⟨pointer.withOptionalProvenance,.none,none⟩,layout⟩
    writePlaceImmediate memory.projection.place memory.choice (.scalar value) place
    strictAllocated pointer.withOptionalProvenance
  let allocatePointerCell := fun (value : StrictPointer) => do
    unless usizeLayout.layout.size == memory.access.runtime.pointerSize do
      throw (StepError.invalidProgram "weak extern pointer cell layout disagrees with target pointer size")
    let pointer ← ReallocationDriver.allocateConfigured memory.allocation
      memory.pointerLayout.layout.size memory.pointerLayout.layout.align.abi
      (.machine .externStatic) .Uninit
    let scalar ← match Scalar.fromMaybePointer memory.access.runtime.base value.withOptionalProvenance with
      | .ok scalar => pure scalar
      | .error error => throw (ScalarOps.scalarError error)
    let place : RuntimePlace Provenance :=
      ⟨.memory ⟨pointer.withOptionalProvenance,.none,none⟩,memory.pointerLayout⟩
    writePlaceImmediate memory.projection.place memory.choice (.scalar scalar) place
    strictAllocated pointer.withOptionalProvenance
  let environ : RuntimeM U StrictPointer := do
    match environment.get (← get).machine.user with
    | .unix state => strictAllocated state.environ
    | .uninit | .windows _ =>
      throw (StepError.invalidProgram "Unix environ requested before Unix EnvVars initialization")
  let functionPointer := fun name => do
    let pointer ← FunctionPointers.functionPointer functions (.Other (dynamicValue name))
    pure pointer
  exact {
    get := do return externStatics.get (← get).machine.user
    put := fun value => modify fun state =>
      {state with machine := {state.machine with user := externStatics.set state.machine.user value}}
    unix := target.families.contains "unix"
    os := target.os
    gnu := target.env == "gnu"
    environ
    allocateValue
    allocatePointerCell
    isDynSym := fun name => pure (sourceDynSym target name)
    functionPointer }

end Miri.Input.EvalHostRuntimeConstruction
