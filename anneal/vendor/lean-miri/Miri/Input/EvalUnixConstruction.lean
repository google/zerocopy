import Miri.Input.CompilerForeignSymbols
import Miri.Input.CompilerCallConstruction
import Miri.Input.CompilerFrameMetadata
import Miri.Input.EvalForeignConstruction
import Miri.Input.EvalArchitectureMachine
import Miri.Input.CompilerNamedFields
import Miri.Input.CompilerLibcConstants
import Miri.Input.CompilerUnixMemoryQueries
import Miri.Input.EvalHostRuntimeConstruction
import Miri.Input.EvalStartupAssembly
import Miri.Input.EvalWorld
import Miri.Interpreter.ExecutionStateTransport
import Miri.Interpreter.RawMemoryMachine
import Miri.Interpreter.PlaceDynamic
import Miri.Interpreter.PointerPlaceMachine
import Miri.Interpreter.OsStringMachine
import Miri.Interpreter.UnixEnvironmentDispatch

/-! Source construction for the Unix environment foreign-item arm. The
compiler ABI recipe and genuine environment/host operations are explicit;
frame relevance, symbol clashes, ABI compatibility, target policy and guest
memory writes are bound to the canonical compiler and execution state. -/
namespace Miri.Input.EvalUnixConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev User := EvalCoreMachine.User
abbrev State := EvalCoreMachine.State
abbrev M Os R P H D O Aff B Host A :=
  MachineHooks.M MiriMemoryKind (User Os R P H D O Aff B Host) A
abbrev Stored := EvalCoreMachine.Stored
abbrev InnerControl (Os R P H D O Aff B Host : Type) :=
  ValidityMachine.Control (Stored Os R P H D O Aff B Host)

inductive RejectOpWith where
  | abort
  | noWarning
  | warning
  | warningWithoutBacktrace
  deriving DecidableEq, Repr

/-- Exact source `MiriConfig.isolated_op` setting. `communicate` is checked
against this value, and shim policy actions are derived below. -/
inductive IsolatedOp where
  | allow
  | reject (mode : RejectOpWith)
  deriving DecidableEq, Repr

/-- Genuine host filesystem/error-display effects plus exact Miri host
configuration values. It contains no target memory, ABI, libc constant,
EnvVars, errno-slot, or policy callback. -/
structure HostConfigEffects (S Os E : Type) where
  communicate : Bool
  isolatedOp : IsolatedOp
  hostPid : EStateM StepError S UInt32
  currentDirectory : EStateM StepError S (Except (IoError.HostError E) Os)
  setCurrentDirectory : Os → EStateM StepError S (Except (IoError.HostError E) Unit)
  pageSize : UInt64
  numCpus : UInt32
  miriVersion : String
  homeDirectory : EStateM StepError S (Option Os)
  hostErrorDisplay : IoError.HostError E → EStateM StepError S Os
  unknownErrorDisplay : Scalar Provenance → EStateM StepError S Os

/-- Native error conversions that cannot be computed from the target compiler
facts. Unix errno/libc lookups and conversion of host errors remain explicit;
the IoError machine, compiler constants, errno memory and scalar access are
constructed here. -/
structure IoHostEffects (S E : Type) where
  hostErrno : String → EStateM StepError S Int32
  hostFromRaw : Int32 → EStateM StepError S (IoError.HostError E)
  hostFromKind : IoError.ErrorKind → EStateM StepError S (IoError.HostError E)

private def lift (value : Except StepError A) : M Os R P H D O Aff B Host A :=
  match value with
  | .ok value => pure value
  | .error error => throw error

private def writeScalar
    (place : PlaceHooks Provenance (State Os R P H D O Aff B Host) C MachineHooks.FrameExtra)
    (choice : C) (scalar : Scalar Provenance) (destination : MPlaceTy Provenance) :
    M Os R P H D O Aff B Host Unit :=
  writePlaceImmediate place choice (.scalar scalar)
    ⟨.memory destination.mplace, destination.layout⟩

private def readScalar
    (access : ValidityMachine.Access MiriMemoryKind
      (Stored Os R P H D O Aff B Host))
    (operand : OpTy Provenance) : M Os R P H D O Aff B Host (Scalar Provenance) := do
  let immediate ← ValidityMachine.readImmediate access operand
  lift (immediate.imm.toScalar.mapError ScalarOps.immediateError)

private def readCString
    (access : PlaceMachine.AccessConfig MiriMemoryKind
      (ValidityMachine.UserState (Stored Os R P H D O Aff B Host)))
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (Stored Os R P H D O Aff B Host)))
    (budget : Nat) (pointer : Pointer (Option Provenance)) :
    M Os R P H D O Aff B Host ByteArray := do
  let rec scan : Nat → Nat → M Os R P H D O Aff B Host Nat
    | 0,_ => throw (.resourceExhaustion "Unix environment C string scan budget")
    | fuel+1,length => do
      if length >= 2^64 then throw (.invalidProgram "Unix environment C string length overflow")
      let current ← lift (RawMemoryMachine.offset pointers.arithmetic pointer (UInt64.ofNat length))
      if (← RawMemoryMachine.readByte access pointers.arithmetic current) == 0 then pure length
      else scan fuel (length+1)
  let length ← scan budget 0
  let bytes ← RawMemoryMachine.readBytes access pointers.arithmetic pointer (UInt64.ofNat length)
  unless bytes.size == length do throw (.invalidProgram "Unix environment C string byte-read length mismatch")
  pure bytes

/-- Replace all pointer/scalar reads, pointer checks, byte writes, named-field
projection, typed pointer-cell dereference, and errno-place writes by the same
canonical access/place drivers used by MIR. `allocateErrno` is separated
because the source IoError helper allocates a global mutable u32 through the
configured allocation lifecycle; it must come from that lifecycle, not from a
captured initial state. String conversion/layout and OS error translation
remain explicit providers in this intermediate source step. -/
private def bindEnvironmentMemory
    (p : CompilerProviders.Prepared)
    (access : ValidityMachine.Access MiriMemoryKind
      (Stored Os R P H D O Aff B Host))
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (Stored Os R P H D O Aff B Host)))
    (place : PlaceHooks Provenance (State Os R P H D O Aff B Host) C MachineHooks.FrameExtra)
    (projection : PlaceProjectionHooks Provenance
      (State Os R P H D O Aff B Host) C MachineHooks.FrameExtra)
    (choice : C)
    (stringBudget : Nat)
    (symbolicAlignment enforceAlignment : Bool)
    (u32Layout : LocalLayout)
    (allocateErrno : M Os R P H D O Aff B Host (MPlaceTy Provenance))
    (source : UnixEnvironment.Hooks (State Os R P H D O Aff B Host)
      Os E EnvVars.Kind) :
    UnixEnvironment.Hooks (State Os R P H D O Aff B Host) Os E EnvVars.Kind := Id.run do
  let readPointer := fun operand => do
    lift ((← readScalar access operand).toPointer access.runtime.base
      |>.mapError ScalarOps.scalarError)
  let readUsize := fun operand => do
    lift ((← readScalar access operand).toTargetUsize pointers.arithmetic.pointerSize
      |>.mapError ScalarOps.scalarError)
  let readI32 := fun operand => do
    lift ((← readScalar access operand).toInt32 |>.mapError ScalarOps.scalarError)
  let readU32 := fun operand => do
    lift ((← readScalar access operand).toUInt32 |>.mapError ScalarOps.scalarError)
  let pointerPlace := fun (operand : OpTy Provenance) (layout : LocalLayout) => do
    let immediate ← ValidityMachine.readImmediate access operand
    let (scalar,metadata) ← lift (immediate.imm.toScalarAndMeta
      |>.mapError ScalarOps.immediateError)
    let pointer ← lift (scalar.toPointer access.runtime.base
      |>.mapError ScalarOps.scalarError)
    PointerPlaceMachine.withMetadata access pointer metadata layout false
  let strings := {source.strings with
    readCString := readCString access pointers stringBudget
    writeCString := RawMemoryMachine.writeCString access pointers.arithmetic
    readWideString := fun pointer => OsStringMachine.readWideString
      ⟨access,pointers,symbolicAlignment,enforceAlignment⟩ stringBudget pointer
    writeWideString := OsStringMachine.writeWideString ⟨access,pointers,symbolicAlignment,enforceAlignment⟩}
  let errors := {source.errors with
    allocateU32Machine := allocateErrno
    getLastErrorPlace := do
      let state ← get
      let some thread := state.machine.threads.activeThread? |
        throw (.invalidProgram "errno active thread missing")
      let some token := thread.lastErrorLocation | return none
      let entries := state.machine.user.payload.payload.user.runtime.errnoPlaces.filter
        (fun (entry : AllocId × MPlaceTy Provenance) => entry.1.value.toNat == token)
      let some (_,place) := entries[0]? |
        throw (.invalidProgram "errno token has no typed pointer")
      unless entries.size == 1 && place.layout == u32Layout do
        throw (.invalidProgram "errno pointer metadata mismatch")
      pure (some place)
    setLastErrorPlace := fun place => do
      let some provenance := place.mplace.ptr.provenance |
        throw (.invalidProgram "errno place has no provenance")
      let some id := PointerProvenance.getAllocId provenance |
        throw (.invalidProgram "errno place has no allocation provenance")
      let state ← get
      let manager := state.machine.threads
      let some thread := manager.activeThread? |
        throw (.invalidProgram "errno active thread missing")
      let thread := {thread with lastErrorLocation := some id.value.toNat}
      let world := state.machine.user.payload.payload.user
      let world := {world with runtime := {world.runtime with errnoPlaces :=
        (world.runtime.errnoPlaces.filter
          (fun (entry : AllocId × MPlaceTy Provenance) => entry.1 != id)).push (id,place)}}
      set {state with machine := {state.machine with
        threads := {manager with threads := manager.threads.set manager.activeThread.toNat thread}
        user := {state.machine.user with payload := {state.machine.user.payload with
          payload := {state.machine.user.payload.payload with user := world}}}}}
    writeScalar := fun scalar dest => writeScalar place choice scalar dest
    readScalar := fun dest => do
      let operand : OpTy Provenance := ⟨.indirect dest.mplace,dest.layout⟩
      readScalar access operand
    scalarI32 := fun value => lift (value.toInt32 |>.mapError ScalarOps.scalarError)
    scalarU32 := fun value => lift (value.toUInt32 |>.mapError ScalarOps.scalarError)
    writeInt := fun value dest => do
      let scalar ← lift (Scalar.fromInt value dest.layout.layout.size
        |>.mapError ScalarOps.scalarError)
      writeScalar place choice scalar dest}
  return {source with
    strings
    errors
    readPointer
    readUsize
    readI32
    readU32
    readScalar := readScalar access
    checkAccess := fun pointer size => ValidityMachine.checkPointerAccess access pointer
      (Size.ofBytes size)
    writeBytes := RawMemoryMachine.writeBytes access pointers.arithmetic
    derefNamed := fun operand name => do
      let layout ← match CompilerPrimitiveFacts.namedLayout p.runtime name with
        | .ok value => pure ⟨value.ty,value.layout⟩
        | .error reason => throw (.unsupported s!"compiler named layout `{name}`: {reason}")
      pointerPlace operand layout
    derefPointerCell := fun operand => do
      let layout ← match p.primitiveLayout "imm_u8_pointer_pointer" with
        | .ok value => pure ⟨value.ty,value.layout⟩
        | .error reason => throw (.unsupported s!"compiler pointer-cell layout: {reason}")
      pointerPlace operand layout
    projectNamed := fun parent name => do
      let index ← match CompilerNamedFields.fieldIndex p.runtime parent.layout name with
        | .ok index => pure index
        | .error error => throw error
      let projected ← PlaceDynamic.field projection choice
        ⟨.memory parent.mplace,parent.layout⟩ index
      match projected.ref with
      | .memory memory => pure ⟨memory,projected.layout⟩
      | .local .. => throw (.invalidProgram "named Unix environment field became a local")
    writeUninit := fun dest => PlaceMachine.writeMemory access (fun _ => false) .uninit dest
    writePointer := fun pointer dest => do
      let scalar ← lift (Scalar.fromMaybePointer access.runtime.base pointer
        |>.mapError ScalarOps.scalarError)
      writeScalar place choice scalar dest}

/-- Source EnvVars backed by the same EvalWorld environment root and real
runtime memory/allocation geometry as startup. The only environment-specific
effects are the actual host OsStr conversions and the two host error outcomes;
all target strings, arrays, reads, writes, allocation kinds and roots come
from `EnvironmentMemory`. -/
def environmentVariablesFromSource [DecidableEq MiriMemoryKind]
    (host : EvalHostRuntimeConstruction.OsHostEffects Os)
    (hostEffects : EvalHostRuntimeConstruction.EnvironmentHostEffects
      (InnerControl Os R P H D O Aff B Host))
    (family : ForeignItems.Family)
    (memory : EvalHostRuntimeConstruction.EnvironmentMemory
      (InnerControl Os R P H D O Aff B Host) C Payload) :
    EnvVars.Hooks (Option Provenance) Os (State Os R P H D O Aff B Host) :=
  EvalHostRuntimeConstruction.envVarsFromSource host hostEffects
    EvalStartupAssembly.environmentLens family memory

/-- Bind compiler-owned facts and canonical writes into the existing Unix
environment implementation. This is an intermediate builder: its `source`
argument is still a full operation dictionary, including memory-access and
projection callbacks. It must not be presented as the completed source
constructor; the next stage constructs that inner dictionary from canonical
access/place/environment state and leaves only genuine host operations plus
unavailable exact libc ABI facts as requirements. -/
private def environment
    (p : CompilerProviders.Prepared)
    (userRelevantCrates : Array Nat)
    (compatibilityBudget : Nat)
    (choice : C)
    (place : PlaceHooks Provenance (State Os R P H D O Aff B Host) C MachineHooks.FrameExtra)
    (access : ValidityMachine.Access MiriMemoryKind
      (Stored Os R P H D O Aff B Host))
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (Stored Os R P H D O Aff B Host)))
    (projection : PlaceProjectionHooks Provenance
      (State Os R P H D O Aff B Host) C MachineHooks.FrameExtra)
    (stringBudget : Nat) (symbolicAlignment enforceAlignment : Bool)
    (allocateErrno : M Os R P H D O Aff B Host (MPlaceTy Provenance))
    (source : UnixEnvironment.Hooks (State Os R P H D O Aff B Host)
      Os E EnvVars.Kind) :
    Except StepError (UnixEnvironmentDispatch.Hooks
      (State Os R P H D O Aff B Host) Os E EnvVars.Kind) := do
  let facts ← p.externStatics.targetFacts |>.mapError fun reason =>
    StepError.unsupported s!"compiler target facts for Unix environment shims: {reason}"
  unless facts.families.contains "unix" do
    throw (.invalidProgram s!"Unix environment construction on non-Unix target `{facts.os}`")
  let arch ← EvalArchitectureMachine.targetArch p.intrinsics |>.mapError fun reason =>
    StepError.unsupported s!"compiler target architecture for Unix environment shims: {reason}"
  let symbols ← p.foreignSymbols |>.mapError fun reason =>
    StepError.unsupported s!"compiler foreign-symbol table for Unix environment shims: {reason}"
  let frame := CompilerFrameMetadata.hooks p.lifecycle.frames userRelevantCrates
  let callCompiler := CompilerCallConstruction.compiler p compatibilityBudget
  let u32Layout ← match p.primitiveLayout "u32" with
    | .ok value => pure ⟨value.ty,value.layout⟩
    | .error reason => throw (.unsupported s!"compiler u32 layout for errno: {reason}")
  let source := bindEnvironmentMemory p access pointers place projection choice
    stringBudget symbolicAlignment enforceAlignment u32Layout allocateErrno source
  let exactErrors := CompilerUnixMemoryQueries.ioErrorHooks p.namedConstants source.errors
  let source := {source with
    os := facts.os
    targetEnv := facts.env
    architecture := arch
    strings := {source.strings with targetWindows := facts.os == "windows"}
    env := {source.env with family := .unix}
    process := {source.process with family := .unix, os := facts.os}
    errors := {exactErrors with family := .unix, os := facts.os}
    libcI32 := fun name => do
      match CompilerLibcConstants.i32 p.namedConstants name with
      | .ok value => pure value
      | .error reason => throw (.unsupported s!"compiler libc constant `{name}`: {reason}")
    libcScalar := fun name => do
      match CompilerLibcConstants.scalar p.namedConstants name with
      | .ok value => pure value
      | .error reason => throw (.unsupported s!"compiler libc scalar `{name}`: {reason}")}
  return {
    env := source
    frameInStd := FrameMetadata.frameInStd frame
    expectedAbi := CompilerNamedShimAbi.query p.namedAbi
    argumentCompat := callCompiler.checkArgumentCompat choice
    checkSymbolClash := fun name =>
      match CompilerForeignSymbols.checkSymbolClash symbols name with
      | .ok () => pure ()
      | .error error => throw error
    transmute := fun operand target => do
      let projection ← place.projection choice
      lift (operand.transmute projection target |>.mapError
        IntrinsicVectorMachine.projectionError)
    writeScalar := writeScalar place choice
    writeInt := fun value destination => do
      let scalar ← lift (Scalar.fromInt value destination.layout.layout.size |>.mapError
        ScalarOps.scalarError)
      writeScalar place choice scalar destination
    writePointer := fun pointer destination => do
      let scalar ← lift (Scalar.fromMaybePointer access.runtime.base pointer |>.mapError
        ScalarOps.scalarError)
      writeScalar place choice scalar destination
  }

/-- Compose Unix environment dispatch from the real runtime memory bundle.
`source` remains only for process/host/isolation policy and host-error display;
its environment, OS-string memory, scalar/pointer access, compiler constants,
typed projections, errno allocation, and errno-place state are all replaced by
the canonical providers. -/
def environmentFromRuntime [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared)
    (userRelevantCrates : Array Nat)
    (compatibilityBudget : Nat)
    (host : EvalHostRuntimeConstruction.OsHostEffects Os)
    (hostEffects : EvalHostRuntimeConstruction.EnvironmentHostEffects
      (InnerControl Os R P H D O Aff B Host))
    (hostConfig : HostConfigEffects (State Os R P H D O Aff B Host) Os E)
    (ioHost : IoHostEffects (State Os R P H D O Aff B Host) E)
    (memory : EvalHostRuntimeConstruction.EnvironmentMemory
      (InnerControl Os R P H D O Aff B Host) C Payload)
    :
    Except StepError (UnixEnvironmentDispatch.Hooks
      (State Os R P H D O Aff B Host) Os E EnvVars.Kind) := do
  unless hostConfig.communicate == (match hostConfig.isolatedOp with
    | .allow => true
    | .reject _ => false) do
    throw (.invalidProgram "Unix communicate flag disagrees with Miri isolated_op policy")
  let u32Layout ← match p.primitiveLayout "u32" with
    | .ok value => pure ⟨value.ty,value.layout⟩
    | .error reason => throw (.unsupported s!"compiler u32 layout for errno: {reason}")
  unless u32Layout.layout.isSized && u32Layout.layout.size.bytes == 4 do
    throw (.invalidProgram "compiler u32 layout mismatch for errno")
  let allocateErrno : M Os R P H D O Aff B Host (MPlaceTy Provenance) := do
    let pointer ← ReallocationDriver.allocateConfigured memory.allocation
      u32Layout.layout.size u32Layout.layout.align.abi (.machine .machine) .Uninit
    pure ⟨⟨pointer.withOptionalProvenance,.none,none⟩,u32Layout⟩
  let facts ← p.externStatics.targetFacts |>.mapError fun reason =>
    StepError.unsupported s!"compiler target facts for Unix environment shims: {reason}"
  unless facts.families.contains "unix" do
    throw (.invalidProgram s!"Unix environment construction on non-Unix target `{facts.os}`")
  let arch ← EvalArchitectureMachine.targetArch p.intrinsics |>.mapError fun reason =>
    StepError.unsupported s!"compiler target architecture for Unix environment shims: {reason}"
  let strings := {EvalHostRuntimeConstruction.osStringsFromMemory host memory with
    targetWindows := facts.os == "windows"}
  let envVariables := environmentVariablesFromSource host hostEffects .unix memory
  let access := memory.access
  let pointers := memory.pointers
  let place := memory.projection.place
  let choice := memory.choice
  let readPointer := fun operand => do
    lift ((← readScalar access operand).toPointer access.runtime.base
      |>.mapError ScalarOps.scalarError)
  let readUsize := fun operand => do
    lift ((← readScalar access operand).toTargetUsize pointers.arithmetic.pointerSize
      |>.mapError ScalarOps.scalarError)
  let readI32 := fun operand => do
    lift ((← readScalar access operand).toInt32 |>.mapError ScalarOps.scalarError)
  let readU32 := fun operand => do
    lift ((← readScalar access operand).toUInt32 |>.mapError ScalarOps.scalarError)
  let pointerPlace := fun (operand : OpTy Provenance) (layout : LocalLayout) => do
    let immediate ← ValidityMachine.readImmediate access operand
    let (scalar,metadata) ← lift (immediate.imm.toScalarAndMeta
      |>.mapError ScalarOps.immediateError)
    let pointer ← lift (scalar.toPointer access.runtime.base
      |>.mapError ScalarOps.scalarError)
    PointerPlaceMachine.withMetadata access pointer metadata layout false
  let readLastErrorPlace := do
    let state ← get
    let some thread := state.machine.threads.activeThread? |
      throw (.invalidProgram "errno active thread missing")
    let some token := thread.lastErrorLocation | return none
    let entries := state.machine.user.payload.payload.user.runtime.errnoPlaces.filter
      (fun (entry : AllocId × MPlaceTy Provenance) => entry.1.value.toNat == token)
    let some (_,place) := entries[0]? |
      throw (.invalidProgram "errno token has no typed pointer")
    unless entries.size == 1 && place.layout == u32Layout do
      throw (.invalidProgram "errno pointer metadata mismatch")
    pure (some place)
  let setLastErrorPlace := fun place => do
    let some provenance := place.mplace.ptr.provenance |
      throw (.invalidProgram "errno place has no provenance")
    let some id := PointerProvenance.getAllocId provenance |
      throw (.invalidProgram "errno place has no allocation provenance")
    let state ← get
    let manager := state.machine.threads
    let some thread := manager.activeThread? |
      throw (.invalidProgram "errno active thread missing")
    let thread := {thread with lastErrorLocation := some id.value.toNat}
    let world := state.machine.user.payload.payload.user
    let world := {world with runtime := {world.runtime with errnoPlaces :=
      (world.runtime.errnoPlaces.filter
        (fun (entry : AllocId × MPlaceTy Provenance) => entry.1 != id)).push (id,place)}}
    set {state with machine := {state.machine with
      threads := {manager with threads := manager.threads.set manager.activeThread.toNat thread}
      user := {state.machine.user with payload := {state.machine.user.payload with
        payload := {state.machine.user.payload.payload with user := world}}}}}
  let errors : IoError.Hooks (State Os R P H D O Aff B Host) E := {
    family := .unix
    os := facts.os
    hostUnix := host.hostUnix
    hostErrno := ioHost.hostErrno
    libc := fun name => match CompilerLibcConstants.scalar p.namedConstants name with
      | .ok value => pure value
      | .error reason => throw (.unsupported s!"compiler libc scalar `{name}`: {reason}")
    windows := fun name => throw (.unsupported s!"Windows error constant `{name}` requested on a Unix target")
    scalarI32 := fun value => lift (value.toInt32 |>.mapError ScalarOps.scalarError)
    scalarU32 := fun value => lift (value.toUInt32 |>.mapError ScalarOps.scalarError)
    hostFromRaw := ioHost.hostFromRaw
    hostFromKind := ioHost.hostFromKind
    getLastErrorPlace := readLastErrorPlace
    setLastErrorPlace
    allocateU32Machine := allocateErrno
    writeScalar := writeScalar place choice
    readScalar := fun dest => readScalar access ⟨.indirect dest.mplace,dest.layout⟩
    writeInt := fun value dest => do
      let scalar ← lift (Scalar.fromInt value dest.layout.layout.size
        |>.mapError ScalarOps.scalarError)
      writeScalar place choice scalar dest }
  let source : UnixEnvironment.Hooks (State Os R P H D O Aff B Host)
      Os E EnvVars.Kind := {
    os := facts.os
    targetEnv := facts.env
    strings
    env := envVariables
    process := {
      communicate := hostConfig.communicate
      family := .unix
      os := facts.os
      hostPid := hostConfig.hostPid
      activeThread := do return UInt32.ofNat (← get).machine.threads.activeThread.toNat
      threadIdTryFrom := fun raw => do
        return ((← get).machine.threads.threadIdTryFrom raw.toNat).toOption.map
          fun id => UInt32.ofNat id.toNat }
    errors
    readPointer
    readUsize
    readI32
    readU32
    readScalar := readScalar access
    isolationReject := fun name => do
      match hostConfig.isolatedOp with
      | .allow => pure false
      | .reject .abort => throw (.termination (.unsupportedInIsolation name))
      | .reject .noWarning | .reject .warning | .reject .warningWithoutBacktrace => pure true
    checkNoIsolation := fun name => do
      if hostConfig.communicate then pure ()
      else throw (.termination (.unsupportedInIsolation name))
    currentDirectory := hostConfig.currentDirectory
    setCurrentDirectory := hostConfig.setCurrentDirectory
    checkAccess := fun pointer size => ValidityMachine.checkPointerAccess access pointer (Size.ofBytes size)
    writeBytes := RawMemoryMachine.writeBytes access pointers.arithmetic
    libcI32 := fun name => match CompilerLibcConstants.i32 p.namedConstants name with
      | .ok value => pure value
      | .error reason => throw (.unsupported s!"compiler libc constant `{name}`: {reason}")
    libcScalar := errors.libc
    pageSize := hostConfig.pageSize
    numCpus := hostConfig.numCpus
    architecture := arch
    miriVersion := hostConfig.miriVersion
    derefNamed := fun operand name => do
      let layout ← match CompilerPrimitiveFacts.namedLayout p.runtime name with
        | .ok value => pure ⟨value.ty,value.layout⟩
        | .error reason => throw (.unsupported s!"compiler named layout `{name}`: {reason}")
      pointerPlace operand layout
    derefPointerCell := fun operand => do
      let layout ← match p.primitiveLayout "imm_u8_pointer_pointer" with
        | .ok value => pure ⟨value.ty,value.layout⟩
        | .error reason => throw (.unsupported s!"compiler pointer-cell layout: {reason}")
      pointerPlace operand layout
    projectNamed := fun parent name => do
      let index ← match CompilerNamedFields.fieldIndex p.runtime parent.layout name with
        | .ok index => pure index
        | .error error => throw error
      let projected ← PlaceDynamic.field memory.projection choice
        ⟨.memory parent.mplace,parent.layout⟩ index
      match projected.ref with
      | .memory result => pure ⟨result,projected.layout⟩
      | .local .. => throw (.invalidProgram "named Unix environment field became a local")
    writeUninit := fun dest => PlaceMachine.writeMemory access (fun _ => false) .uninit dest
    writePointer := fun pointer dest => do
      let scalar ← lift (Scalar.fromMaybePointer access.runtime.base pointer
        |>.mapError ScalarOps.scalarError)
      writeScalar place choice scalar dest
    homeDirectory := hostConfig.homeDirectory
    hostErrorDisplay := hostConfig.hostErrorDisplay
    unknownErrorDisplay := hostConfig.unknownErrorDisplay }
  environment p userRelevantCrates compatibilityBudget memory.choice
    memory.projection.place memory.access memory.pointers memory.projection
    memory.stringScanBudget memory.symbolicAlignment memory.enforceAlignment
    allocateErrno source

end Miri.Input.EvalUnixConstruction
