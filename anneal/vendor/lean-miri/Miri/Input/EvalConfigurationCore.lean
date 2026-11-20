import Miri.Input.EvalConfiguration
import Miri.Interpreter.NativeAllocationLifecycle
import Miri.Interpreter.MemoryErrors
import Miri.Interpreter.ConcurrencyErrors
import Miri.Input.EvalAccessMachine
import Miri.Input.EvalPointerSource
import Miri.Input.CompilerForeignSymbols
import Miri.Input.EvalThreadLocalSource
import Miri.Input.EvalTerminatorMachine
import Miri.Input.CompilerRetagOptions
import Miri.Input.CompilerExecutionBounds
import Miri.Input.EvalCallRuntime
import Miri.Input.EvalPanicMachine
import Miri.Input.EvalPlaceConstruction
import Miri.Input.EvalValidityMachine
import Miri.Input.EvalMathMachine
import Miri.Input.EvalArchitectureMachine
import Miri.Input.CompilerCastQueries
import Miri.Input.CompilerScalarLeaves
import Miri.Input.CompilerPlaceTypes
import Miri.Input.CompilerValidityLeaves
import Miri.Input.CompilerVTableLeaves
import Miri.Input.CompilerSignatureAbi
import Miri.Input.CompilerOperandSites
import Miri.Input.CompilerIntrinsicSymbols
import Miri.Input.CompilerBodySpan
import Miri.Input.CompilerCoreIntrinsic
import Miri.Input.CompilerValueConstants
import Miri.Input.EvalCallerLocationConstruction
import Miri.Input.CompilerCovariance
import Miri.Input.CompilerVarArgsLeaves
import Miri.Input.EvalCallDispatchConstruction
import Miri.Input.EvalPortableForeignRuntime
import Miri.Input.EvalHostRuntimeConstruction
import Miri.Input.EvalSyncObjectAccess
import Miri.Input.EvalSocketAddressConstruction
import Miri.Input.EvalCallbackFutexConstruction
import Miri.Input.EvalUnixPthreadConstruction
import Miri.Input.EvalUnixDynamicConstruction
import Miri.Input.EvalUnixAffinityConstruction
import Miri.Input.EvalUnixSolarishConstruction
import Miri.Input.EvalUnixFreeBsdConstruction
import Miri.Input.EvalUnixMacOsConstruction
import Miri.Input.CompilerNamedShimAbi
import Miri.Interpreter.RandomMemory
import Miri.Interpreter.UnixRandomDispatch
import Miri.Interpreter.EventFdDispatch
import Miri.Interpreter.LinuxSyscallPartialDispatch
import Miri.Input.CompilerLinuxSyscall
import Miri.Input.EvalNativeSourceConstruction

/-! Source-owned execution configuration. Compiler/global-memory, platform and native numerical capabilities remain explicit. Callback capacity is an execution resource, not a safety guarantee. -/

namespace Miri.Input.EvalConfigurationCore
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
abbrev User := EvalCoreMachine.User
abbrev State := EvalCoreMachine.State
abbrev Stored := EvalCoreMachine.Stored
abbrev M Os R P H D O Aff B Host A := MachineHooks.M MiriMemoryKind (User Os R P H D O Aff B Host) A
structure PlaceOptions where
  debugAssertions : Bool
  dynamicFuel : Nat
  validation : ValidityMachine.ValidationMode

structure Options where
  place : PlaceOptions
  limits : ExecutionMachine.Limits
  compatibilityBudget : Nat
  varArgsBudget : Nat
  callbackCapacity : Nat
  floatNondeterministic : Bool
  weakFailureRate : UInt64
  crossCrateInlineAlways : Bool
  userRelevantCrates : Array Nat
  ignoreOptionalOverflowChecks : Bool
  panicUnwinds : Bool
  retag : CompilerRetagOptions.Options
  /-- Bound host write-all retries independently of guest string scans or ABI
  work. Exhaustion is an explicit resource outcome, never successful output. -/
  miriWriteRetryBudget : Nat := 65536

/-- Genuine residual effects and compiler queries. Physical reads/writes,
local storage, retagging, calls/returns and every ordinary MIR operation are
constructed below, rather than independently chosen callbacks. -/
structure Leaves (Os R P H D O Aff B Host C ClockHost : Type) where
  pointerSource : EvalPointerSource.Leaves Os R P H D O Aff B Host C
  sync : P → Miri.Concurrency.SyncObject.AccessKind → PlaceMachine.MachineM MiriMemoryKind (User Os R P H D O Aff B Host) Unit
  storage : Size → Align → Option (Array UInt8)
  spans : AllocationDriver.SpanHooks
  foreign : Option (ForeignItems.Hooks Provenance (State Os R P H D O Aff B Host) (RuntimePlace Provenance)
    (RuntimePlace Provenance) (Pointer (Option Provenance)) LoadedBody CallInstance)
  dynSymName : O → String
  checkLlvmSymbolClash : String → M Os R P H D O Aff B Host Unit
  math : Option (EvalMathMachine.Host (State Os R P H D O Aff B Host) C)
  mathError : Math.ErrorMode
  control : EvalTerminatorMachine.ControlAccess Host ClockHost
  blockingSources : EvalTerminatorMachine.IoSourcesAccess Host

abbrev SourceOther Raw Listener TcpStream Error :=
  EvalUnixSourceConstruction.Other Raw Listener TcpStream Error
abbrev SourceHost Poll Instant System H D Raw Listener TcpStream Error Native Profiler :=
  EvalSyncMachine.Host Poll Instant System H D
    (SourceOther Raw Listener TcpStream Error) Native Profiler
abbrev SourceUser Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  EvalCoreMachine.User Os R P H D (SourceOther Raw Listener TcpStream Error) Aff B
    (SourceHost Poll Instant System H D Raw Listener TcpStream Error Native Profiler)
abbrev SourceState Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  MachineHooks.State MiriMemoryKind
    (SourceUser Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error)
abbrev SourceControl Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error :=
  ValidityMachine.Control (EvalCoreMachine.Stored Os R P H D
    (SourceOther Raw Listener TcpStream Error) Aff B
    (SourceHost Poll Instant System H D Raw Listener TcpStream Error Native Profiler))

/-- Source-route inputs for the specialized production Core path. Unlike the
legacy `Leaves`, this record cannot carry a completed `ForeignItems.Hooks`;
the ordered source resolver is constructed internally from `foreignSource`.
The dimensions match EvalWorld's canonical Unix Other/Host payload exactly. -/
structure SourceLeaves
    (Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error ErrorHost
      Meta Path Place C ClockHost I AddrIter : Type) where
  /-- The actual runtime configuration selected by the source runner.  Foreign
  callback and scheduler bindings project communication/host limits from this
  value; they do not choose an independent mode. -/
  hostConfiguration : HostRuntime.Configuration
  nativeHost : Option (CompilerNativeSignatures.Host MiriMemoryKind
    (SourceControl Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) C)
  /-- Actual native-call backend leaves. The semantic native-call pipeline is
  source-built; this optional record contains only real host operations. -/
  nativeBackend : Option (EvalNativeSourceConstruction.RawHost
    (EvalNativeMachine.U Os R P H D (SourceOther Raw Listener TcpStream Error) Aff B
      Poll Instant System Native Profiler) C Native Nat) := none
  sync : P → Miri.Concurrency.SyncObject.AccessKind → PlaceMachine.MachineM MiriMemoryKind
    (SourceUser Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Unit
  storage : Size → Align → Option (Array UInt8)
  spans : AllocationDriver.SpanHooks
  foreignSource : EvalCallDispatchConstruction.SourceInput
    Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
    ErrorHost Meta Path AddrIter
  dynSymName : SourceOther Raw Listener TcpStream Error → String
  checkLlvmSymbolClash : String → MachineHooks.M MiriMemoryKind
    (SourceUser Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) Unit
  math : Option (EvalMathMachine.Host
    (SourceState Os R P H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error) C)
  mathError : Math.ErrorMode
  control : EvalTerminatorMachine.ControlAccess
    (SourceHost Poll Instant System H D Raw Listener TcpStream Error Native Profiler) ClockHost
  blockingSources : EvalTerminatorMachine.IoSourcesAccess
    (SourceHost Poll Instant System H D Raw Listener TcpStream Error Native Profiler)

private def query (value : Except String A) : M Os R P H D O Aff B Host A :=
  match value with | .ok value => pure value | .error reason => throw (.unsupported reason)
private def physical (value : Except StepError A) : M Os R P H D O Aff B Host A :=
  match value with | .ok value => pure value | .error error => throw error
private def pureQuery (value : Except String A) : Except StepError A := value.mapError StepError.unsupported
private def liftConstruction (value : Except StepError A) : Except StepError (ULift.{1} A) :=
  match value with | .ok value => .ok ⟨value⟩ | .error error => .error error
private def returnToBlock (_ : C) (target : Option BasicBlockId) : M Os R P H D O Aff B Host Unit := fun state =>
  let (after,result) := ControlFlow.returnToBlock target state
  match result with | .ok value => .ok value after | .error error => .error error after

private def discriminant (queries : ExecutionLeaves.Discriminant (State Os R P H D O Aff B Host) C)
    (access : PlaceMachine.AccessConfig MiriMemoryKind (User Os R P H D O Aff B Host))
    (operands : OperandMachine.Hooks MiriMemoryKind (User Os R P H D O Aff B Host) C) :
    DiscriminantHooks Provenance (State Os R P H D O Aff B Host) C (RuntimePlace Provenance) where
  discriminantLayout := queries.discriminantLayout
  tagLayout := queries.tagLayout
  discriminantValue := queries.discriminantValue
  variantForDiscriminant := queries.variantForDiscriminant
  adtVariantCount := queries.adtVariantCount
  scalarMayBeNull := queries.scalarMayBeNull
  runtimeTarget := access.runtime
  projectRead := OperandMachine.field operands
  readImmediate := fun _ => ValidityMachine.readImmediate access
  destLayout := RuntimePlace.layout
  projectWrite := PlaceDynamic.field operands.projection
  writeScalar := fun c value dest => writePlaceImmediate operands.projection.place c (.scalar value) dest
  toOp := placeToOp operands.projection.place

structure ForeignContext (Os R P H D O Aff B Host C ClockHost : Type)
    (Assembly : Type := Unit) where
  prepared : CompilerProviders.Prepared
  hostConfiguration : Option HostRuntime.Configuration
  /-- Rebuild the source foreign assembly against the current live state. The
  same callable is installed as the Core foreign resolver and is exposed to
  startup/callback construction; it does not capture an initial-world copy. -/
  sourceAssembly : Option (Unit → M Os R P H D O Aff B Host
    Assembly)
  validityAccess : ValidityMachine.Access MiriMemoryKind (Stored Os R P H D O Aff B Host)
  /-- The exact visitor built from this configuration's retag/projection and
  source facts. Native calls reuse it rather than rebuilding weaker validation. -/
  validity : ValidityVisitor.Hooks Provenance
    (State Os R P H D O Aff B Host) C MachineHooks.FrameExtra
    (FnVal O) (FnAbi TyId) ValidityMemory.PaddingHandle
  access : PlaceMachine.AccessConfig MiriMemoryKind (User Os R P H D O Aff B Host)
  allocation : PlaceMachine.AllocationConfig MiriMemoryKind (User Os R P H D O Aff B Host)
  compiler : PlaceMachine.CompilerHooks MiriMemoryKind (User Os R P H D O Aff B Host) C
  dynamic : DynamicLayoutHooks Provenance (State Os R P H D O Aff B Host) C
  vtable : VTableHooks Provenance (State Os R P H D O Aff B Host) C
    (FnVal O) (FnAbi TyId)
  dynamicFuel : Nat
  atomics : AtomicAccessHooks Provenance (State Os R P H D O Aff B Host) C
    (RuntimePlace Provenance)
  extras : MemoryExtras.Hooks MiriMemoryKind (User Os R P H D O Aff B Host) P
  deallocationDiagnostic : AllocId → PlaceMachine.MachineM MiriMemoryKind
    (User Os R P H D O Aff B Host) Unit
  nativeDrop : Option (Allocation Provenance Miri.TreeBorrows.BorrowTree →
    MachineHooks.M MiriMemoryKind (User Os R P H D O Aff B Host) Unit)
  pointers : PointerMachine.Hooks MiriMemoryKind
    (ValidityMachine.Control (Stored Os R P H D O Aff B Host))
  /-- The exact per-world function registry used by MIR calls and source
  function-pointer resolution. Foreign source constructors consume this
  registry rather than rebuilding or snapshotting a separate one. -/
  functions : FunctionPointers.Hooks MiriMemoryKind
    (User Os R P H D O Aff B Host) O

  /-- Derived from this configuration and transported to the canonical outer thread state. -/
  threadFunctions : Unit → Except StepError
    (FunctionCalls.Hooks Provenance
      (MachineHooks.State MiriMemoryKind
        (ExecutionStateTransport.Outer (EvalCoreMachine.World Os R P H D O Aff B Host)))
      C MachineHooks.FrameExtra O ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId))
  spans : AllocationDriver.SpanHooks
  projection : PlaceProjectionHooks Provenance (State Os R P H D O Aff B Host)
    C MachineHooks.FrameExtra
  place : PlaceHooks Provenance (State Os R P H D O Aff B Host) C MachineHooks.FrameExtra
  callFunction : C → CallInstance → Array (RvalueImmTy Provenance) → ReturnContinuation →
    M Os R P H D O Aff B Host Unit
  choice : C
  math : Math.Hooks Provenance (State Os R P H D O Aff B Host) C (RuntimePlace Provenance)

/-- Existential source callback package. The host timezone and timestamp
representations are not part of EvalWorld, so a real time-shim dictionary is
carried at the higher-universe factory boundary instead of being erased to
Unit inside EStateM state. -/
structure SourceCallbackProduct
    (Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error C AddrIter : Type)
    : Type 1 where
  Zone : Type
  Timestamp : Type
  hooks : EvalCallbackMachine.Hooks Os R EvalSyncObjectAccess.Payload H D
    (SourceOther Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler C
    ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId) Zone Timestamp Error
    EvalUnixFdConstruction.ArrayCursor Raw Listener TcpStream Error AddrIter
  main : MainMachine.Hooks
    (EvalCallbackMachine.ThreadUser Os R EvalSyncObjectAccess.Payload H D
      (SourceOther Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler)
    C (SourceOther Raw Listener TcpStream Error) ABI.ExternAbi
    (FnAbi TyId) (ArgAbi TyId) Aff EvalSyncObjectAccess.Payload
  objects : ForeignSyncMachine.Objects
    (SourceState Os R EvalSyncObjectAccess.Payload H D Aff B Poll Instant System Native Profiler
      Raw Listener TcpStream Error)
  deadline : DeadlineMachine.Hooks MiriMemoryKind
    (EvalSyncMachine.User Os R EvalSyncObjectAccess.Payload H D
      (SourceOther Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler)
    Instant System
  time : Option (TimeShims.Hooks
    (SourceState Os R EvalSyncObjectAccess.Payload H D Aff B Poll Instant System Native Profiler
      Raw Listener TcpStream Error) Instant System Zone Timestamp)

/-- Higher-universe source callback factory paired with the already-created
configuration and canonical assembly. The builder consumes that exact
assembly and execution config after Main and startup initialization exist; it
does not rerun the source constructors or accept caller-built callbacks. -/
structure SourcePackage
    (Os R H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error ErrorHost
      Meta Path Place C ClockHost AddrIter : Type) where
  execution : ExecutionMachine.Config MiriMemoryKind
    (SourceUser Os R EvalSyncObjectAccess.Payload H D Aff B Poll Instant System Native Profiler
      Raw Listener TcpStream Error)
    C (SourceOther Raw Listener TcpStream Error) ABI.ExternAbi ClockHost
  /-- Panic behavior resolved from the compiler session that produced this
  source program. Source-backed call and catch-unwind hooks use this value;
  the low-level Options API remains caller-controlled. -/
  panicUnwinds : Bool
  context : ForeignContext Os R EvalSyncObjectAccess.Payload H D
    (SourceOther Raw Listener TcpStream Error) Aff B
    (SourceHost Poll Instant System H D Raw Listener TcpStream Error Native Profiler) C ClockHost
    (EvalCallDispatchConstruction.SourceAssembly Os R EvalSyncObjectAccess.Payload H D Aff B
      Poll Instant System Native Profiler Raw Listener TcpStream Error C
      (EvalCallDispatchConstruction.SourceCallbackSeed Os R H D Aff B Poll Instant System Native Profiler
        Raw Listener TcpStream Error Meta Path Place C
        (Clock.HostHooks Instant System
          (SourceState Os R EvalSyncObjectAccess.Payload H D Aff B Poll Instant System Native Profiler
            Raw Listener TcpStream Error))
        CallInstance AddrIter))
  callbackBuilder :
    EvalCallDispatchConstruction.SourceAssembly Os R EvalSyncObjectAccess.Payload H D Aff B
      Poll Instant System Native Profiler Raw Listener TcpStream Error C
      (EvalCallDispatchConstruction.SourceCallbackSeed Os R H D Aff B Poll Instant System Native Profiler
        Raw Listener TcpStream Error Meta Path Place C
        (Clock.HostHooks Instant System
          (SourceState Os R EvalSyncObjectAccess.Payload H D Aff B Poll Instant System Native Profiler
            Raw Listener TcpStream Error))
        CallInstance AddrIter) →
    ExecutionMachine.Config MiriMemoryKind
      (SourceUser Os R EvalSyncObjectAccess.Payload H D Aff B Poll Instant System Native Profiler
        Raw Listener TcpStream Error)
      C (SourceOther Raw Listener TcpStream Error) ABI.ExternAbi ClockHost →
    MainMachine.Hooks
      (EvalCallbackMachine.ThreadUser Os R EvalSyncObjectAccess.Payload H D
        (SourceOther Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler)
      C (SourceOther Raw Listener TcpStream Error) ABI.ExternAbi
      (FnAbi TyId) (ArgAbi TyId) Aff EvalSyncObjectAccess.Payload →
    EvalCallbackMachine.State Os R EvalSyncObjectAccess.Payload H D
      (SourceOther Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler →
    Except
      (StepError × EvalCallbackMachine.State Os R EvalSyncObjectAccess.Payload H D
        (SourceOther Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler)
      (SourceCallbackProduct Os R H D Aff B Poll Instant System Native Profiler
        Raw Listener TcpStream Error C AddrIter ×
       EvalCallbackMachine.State Os R EvalSyncObjectAccess.Payload H D
        (SourceOther Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler)
  /-- Rebind a selected Core's foreign resolver to the callback router built
  from this same package. The resolver still constructs a fresh view of the
  live source assembly at each actual foreign call, then routes its IO through
  these canonical callback hooks. -/
  rebindCallbacks :
    SourceCallbackProduct Os R H D Aff B Poll Instant System Native Profiler
      Raw Listener TcpStream Error C AddrIter →
    ExecutionMachine.Config MiriMemoryKind
      (SourceUser Os R EvalSyncObjectAccess.Payload H D Aff B Poll Instant System Native Profiler
        Raw Listener TcpStream Error)
      C (SourceOther Raw Listener TcpStream Error) ABI.ExternAbi ClockHost →
    ExecutionMachine.Config MiriMemoryKind
      (SourceUser Os R EvalSyncObjectAccess.Payload H D Aff B Poll Instant System Native Profiler
        Raw Listener TcpStream Error)
      C (SourceOther Raw Listener TcpStream Error) ABI.ExternAbi ClockHost

/-- Build startup/foreign environment memory from the exact live Core fields.
This deliberately lives below EvalSyncObjectConstruction: it avoids a module
cycle and does not take a separately assembled execution Config or memory
record. The returned state lens is the same EvalWorld runtime used by MIR. -/
def environmentMemoryFromCore [DecidableEq MiriMemoryKind]
    (prepared : CompilerProviders.Prepared)
    (access : PlaceMachine.AccessConfig MiriMemoryKind (User Os R P H D O Aff B Host))
    (allocation : PlaceMachine.AllocationConfig MiriMemoryKind (User Os R P H D O Aff B Host))
    (extras : MemoryExtras.Hooks MiriMemoryKind (User Os R P H D O Aff B Host) P)
    (deallocationDiagnostic : AllocId → PlaceMachine.MachineM MiriMemoryKind
      (User Os R P H D O Aff B Host) Unit)
    (nativeDrop : Option (Allocation Provenance Miri.TreeBorrows.BorrowTree →
      MachineHooks.M MiriMemoryKind (User Os R P H D O Aff B Host) Unit))
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (Stored Os R P H D O Aff B Host)))
    (spans : AllocationDriver.SpanHooks)
    (projection : PlaceProjectionHooks Provenance (State Os R P H D O Aff B Host)
      C MachineHooks.FrameExtra)
    (choice : C) (alignment : ValidityMachine.AlignmentCheck)
    (stringScanBudget : Nat) : Except StepError
    (EvalHostRuntimeConstruction.EnvironmentMemory
      (ValidityMachine.Control (Stored Os R P H D O Aff B Host)) C P) := do
  let pointer ← (prepared.primitiveLayout "unit_pointer_mut").mapError
    (fun reason => StepError.unsupported s!"compiler pointer layout for environment memory: {reason}")
  let arrays : RuntimeArrayQueries.Access
      (EvalHostRuntimeConstruction.RuntimeState
        (ValidityMachine.Control (Stored Os R P H D O Aff B Host))) := {
    get := fun state => EvalPointerSource.arrays.get state.machine
    set := fun state types => {state with machine := EvalPointerSource.arrays.set state.machine types} }
  let deallocate := fun pointer old kind =>
    EvalAllocationMachine.deallocateWith spans pointers extras deallocationDiagnostic
      nativeDrop pointer old kind
  pure {
    access, allocation, deallocate, pointers, projection, arrays
    symbolicAlignment := alignment == .Symbolic
    enforceAlignment := alignment != .None
    stringScanBudget, choice
    pointerTy := pointer.ty, pointerLayout := ⟨pointer.ty, pointer.layout⟩ }

/-- Internal platform assembly edge. Production platform packages derive this
builder from compiler facts and raw host leaves; this is not an input contract
for client Rust safety claims. -/
abbrev ForeignBuilder (Os R P H D O Aff B Host C ClockHost Assembly : Type) :=
  ForeignContext Os R P H D O Aff B Host C ClockHost Assembly →
    M Os R P H D O Aff B Host
      (ForeignItems.Hooks Provenance (State Os R P H D O Aff B Host)
        (RuntimePlace Provenance) (RuntimePlace Provenance)
        (Pointer (Option Provenance)) LoadedBody CallInstance × Assembly)

/-- Construct a fresh view of the same canonical state. The decreasing count
is consumed only by synchronous visitor/helper/catch re-entry; exhaustion is
an explicit runner resource result. Ordinary frame execution uses Step.step.
Shared internal construction for source-owned platform packages retains
the same live source assembly factory in startup and each recursive call. -/
def makeWithForeignContext {Assembly : Type}
    (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : Options) (leaves : Leaves Os R P H D O Aff B Host C ClockHost) (choice : C)
    (sourceHostConfiguration : Option HostRuntime.Configuration)
    (foreignBuilder : Option (ForeignBuilder Os R P H D O Aff B Host C ClockHost Assembly)) :
    Nat → Except StepError
      (ExecutionMachine.Config MiriMemoryKind (User Os R P H D O Aff B Host) C O ABI.ExternAbi ClockHost ×
        ForeignContext Os R P H D O Aff B Host C ClockHost Assembly)
  | 0 => .error (.resourceExhaustion "execution callback construction capacity")
  | remaining + 1 => do
    let ⟨maximum⟩ ← liftConstruction (CompilerExecutionBounds.maximum p.runtime.target)
    let placeOptions : EvalPlaceConstruction.Options := {
      debugAssertions := options.place.debugAssertions
      maxSizeOfVal := maximum
      dynamicFuel := options.place.dynamicFuel
      validation := options.place.validation }
    let facts := p.lifecycle.calls.symbols.facts
    let context := facts.context
    let compatibility := CompilerCovariance.compatible p options.place.debugAssertions
    let covariance := CompilerCovariance.hook p options.place.debugAssertions
    let intrinsicQueries : CompilerCoreIntrinsic.Queries (State Os R P H D O Aff B Host) C := CompilerCoreIntrinsic.make p
    let extra := EvalCoreMachine.extras leaves.sync ConcurrencyErrors.storeBuffer
    let source := EvalPointerSource.make p image extra leaves.pointerSource choice
    let pointers := source.pointers
    let functions := EvalConfiguration.functions p image options.crossCrateInlineAlways pointers
    let nativeBacking := leaves.pointerSource.nativeHost.map (·.backing)
    -- M::extern_static_pointer is a compiler-owned query over the shared
    -- declaration/export tables and the actual runtime ExternStatic registry.
    -- Keep the lower MachineAddress callback for global-allocation root
    -- conversion, while all MIR constants and constant intrinsics use this
    -- source resolver directly.
    let checkExternStaticClash := fun symbol => do
      let symbols ← match p.foreignSymbols with
        | .ok symbols => pure symbols
        | .error reason => throw (.unsupported s!"compiler foreign-symbol query: {reason}")
      match CompilerForeignSymbols.checkSymbolClash symbols symbol with
      | .ok () => pure ()
      | .error error => throw error
    let externStatic := CompilerExternStatic.resolve p.externStatics image
      checkExternStaticClash functions
      (fun user => EvalWorld.roots.externStatics (ExecutionStateTransport.toOuter user))
    let terminators := EvalTerminatorMachine.genericHooks leaves.control (EvalTerminatorMachine.ioGc leaves.blockingSources)
    let access := EvalAccessMachine.make p image maximum options.place.dynamicFuel source.globals pointers extra
    -- TrackingAlloc (machine.rs975) only emits diagnostics.rs display output.
    let allocation := EvalConfiguration.allocation maximum leaves.storage
      (fun _ _ _ => pure ()) pointers extra
    let allocation := {allocation with
      nativeStorage := some (fun size align init => do
        let state : State Os R P H D O Aff B Host ← get
        if (leaves.pointerSource.nativeLibraryPaths state.machine.user.payload.payload.user.host).isEmpty then
          pure (Allocation.tryNew (Prov := Provenance) size align init leaves.storage)
        else
          match nativeBacking with
          | none => throw (.unsupported "native allocations require actual host byte backing")
          | some backing => NativeAllocationLifecycle.createZeroed (NativeAllocationLifecycle.liftBacking backing) size align init)
      nativeDrop := nativeBacking.map (fun backing => NativeAllocationLifecycle.releaseAllocation (NativeAllocationLifecycle.liftBacking backing))}
    let engine := EvalCompilerMachine.vtables p image functions
    let memoryOffset := fun (_ : C) place amount mode metadataValue => do
      match EvalProjectionMachine.memoryOffset pointers (← get) place amount mode metadataValue with
      | .ok value => pure value
      | .error error => throw (IntrinsicVectorMachine.projectionError error)
    let table := CompilerVTableLeaves.make p image engine memoryOffset
    let nested : Unit → Except StepError (ExecutionMachine.Config MiriMemoryKind (User Os R P H D O Aff B Host) C O ABI.ExternAbi ClockHost) := fun _ =>
      (makeWithForeignContext p image bytes options leaves choice sourceHostConfiguration foreignBuilder remaining).map Prod.fst
    let validate := fun c place => do
      match nested () with
      | .error error => throw error
      | .ok config => ValidityMachine.validateRuntime config.validity c options.limits.validation place true
    let compiler := EvalPlaceConstruction.compiler p placeOptions access pointers table
      (CompilerPlaceTypes.place p options.place.debugAssertions covariance) validate
    let projection := EvalPlaceConstruction.projection p placeOptions access allocation compiler table
    let pointerCompiler := CompilerExecutionProviders.pointerCompiler facts
    let dereference := PointerPlaceMachine.dereference access pointerCompiler projection.dynamic table projection.dynamicFuel
    let operands : OperandMachine.Hooks MiriMemoryKind (User Os R P H D O Aff B Host) C := {
      compiler,projection
      layoutCompatible := compatibility
      checkPlaceType := CompilerPlaceTypes.operand p options.place.debugAssertions covariance
      dereference
      runtimeChecks := CompilerScalarLeaves.runtimeChecks p
      boolLayout := CompilerScalarLeaves.boolLayout p
      constant := fun _ _ _ => throw (.unsupported "constant operand requires an exact structural source site")
      constantAt := fun _ path constant known => do
        let site ← CompilerOperandSites.current path
        CompilerConstantMachine.evalAtBound p.constantBinding site functions pointers.arithmetic
          externStatic MemoryErrors.constant constant known
          (if options.place.debugAssertions then some (fun computed expected => physical (compatibility computed expected)) else none) }
    let callBackend : CallDispatchMachine.Backend (State Os R P H D O Aff B Host) := {
      selection := fun state => do
        match ← EvalBackendMachine.handler state.machine with
        | .none => pure .none
        | .vclocks _ => pure .vclocks }
    let retag := EvalRetagMachine.hooks facts p.lifecycle.calls.runtime (CompilerRetagOptions.make p options.retag) access projection table pointers choice
    let scalarQueries := CompilerScalarLeaves.scalar p
    let floats : FloatOpsHooks Provenance (State Os R P H D O Aff B Host) C := {
      integerKindOf := fun _ ty => physical (CompilerExecutionProviders.integerKind context ty)
      formatOf := fun _ ty => physical (CompilerExecutionProviders.format context ty)
      boolLayout := scalarQueries.boolLayout
      floatNondeterministic := options.floatNondeterministic
      chooseNaN := fun _ => ExecutionChoiceBindings.nanChoice EvalCoreMachine.tape }
    let isRaw := fun (_ : C) ty => do
      let node ← query (p.runtime.node ty |>.mapError toString)
      match node.shapeKind with
      | .unknown _ => throw (.unsupported "raw pointer compiler type kind unavailable")
      | kind => pure (kind == .rawPointer)
    let usize := fun (_ : C) => query (p.primitiveLayout "usize")
    let pointeeLayout := fun (_ : C) ty => do
      let some pointee ← query (CompilerFacts.builtinDeref context ty true)
        | throw (.invalidProgram "pointee layout requested for a non-pointer type")
      query (CompilerFacts.layoutOf context pointee)
    let scalar := ExecutionScalar.hooks scalarQueries access pointers.arithmetic isRaw usize pointeeLayout dereference floats
    let discrQueries := CompilerScalarLeaves.discriminant p (fun _ => ValidityMachine.scalarMayBeNull)
    let discr := discriminant discrQueries access operands
    let validity := EvalValidityMachine.hooks facts p.lifecycle.calls.runtime
      (CompilerValidityLeaves.make p image EvalProjectionMachine.arrays projection pointers)
      access allocation compiler projection (FunctionPointerConsumers.vtable functions table) discr pointers retag options.limits.retag
    let copy := CompilerCopy.hooks p.runtime options.place.debugAssertions compatibility access
      PointerMachine.User.addresses pointers.arithmetic validity options.limits.validation
    let castQueries := CompilerCastLeaves.make p (CompilerCastQueries.required p) table
      (fun _ provenance => PointerMachine.exposeProvenance pointers provenance)
      (fun _ address => PointerMachine.pointerFromExposedAddress pointers address)
      (fun value layout => EvalProjectionMachine.assertAbi p.runtime.target value layout |>.mapError IntrinsicVectorMachine.projectionError)
    let casts := ExecutionCast.hooks castQueries access allocation compiler projection copy retag validity functions floats
      dereference (OperandMachine.field operands) (fun _ _ => ValidityMachine.enforceValidityRecursively)
      options.limits.retag options.limits.validation
    let nativeDrop := nativeBacking.map fun backing => NativeAllocationLifecycle.releaseAllocation
      (NativeAllocationLifecycle.liftBacking backing)
    -- FreedAlloc (machine.rs1801) is the same display-only diagnostic.
    let deallocateStack := fun ptr => EvalAllocationMachine.deallocateWith leaves.spans pointers extra
      (fun _ => pure ()) nativeDrop ptr none .stack
    let callFunction := fun c callee args continuation => do
      match nested () with
      | .error error => throw error
      | .ok config =>
        let helper := ExecutionCalls.helpers config.helpers (ExecutionMachine.callHooks config options.limits)
        FunctionCalls.callFunction helper c callee ABI.ExternAbi.Rust args none continuation
    let unwind := EvalCallRuntime.unwind access projection functions options.panicUnwinds callFunction
    let lifecycle := CompilerCallConstruction.lifecycle p options.userRelevantCrates
      (CompilerStorage.hooks p allocation projection.dynamic projection.dynamicFuel choice deallocateStack)
      EvalConfiguration.identity unwind
    let ⟨math⟩ ← liftConstruction (EvalMathMachine.hooks p (EvalMathMachine.optionalHost leaves.math) leaves.mathError none access projection.place scalar floats returnToBlock)
    let atomics := ExecutionIntrinsic.Atomic.access {
      loadChoiceRank := fun _ count => ExecutionChoices.index EvalCoreMachine.tape .atomicStale count
      weakPolicy := .mayFail
      weakSuccessChoice := fun _ => do
        let rate ← physical (ExecutionChoiceBindings.successRate options.weakFailureRate)
        ExecutionChoices.bernoulli EvalCoreMachine.tape .weakCasSuccess rate
      -- WeakMemoryOutdatedLoad is display-only diagnostics.rs emission.
      diagnostic := fun _ _ => pure ()
      classifyDispatchError := ConcurrencyErrors.atomic
      classifyGlobalError := ConcurrencyErrors.global }
      scalar access projection.place pointers extra
    let foreignContext : ForeignContext Os R P H D O Aff B Host C ClockHost Assembly := {
          prepared := p
          hostConfiguration := sourceHostConfiguration
          sourceAssembly := none
          validityAccess := access
          validity := validity
          access := access
          allocation := allocation
          compiler := compiler
          dynamic := projection.dynamic
          vtable := validity.vtable
          dynamicFuel := projection.dynamicFuel
          atomics := atomics
          extras := extra
          deallocationDiagnostic := fun _ => pure ()
          nativeDrop := nativeDrop
          pointers := pointers
          functions := functions
          threadFunctions := fun _ => do
            let nestedConfig ← nested ()
            let calls := ExecutionMachine.callHooks nestedConfig options.limits
            let helpers := ExecutionCalls.helpers nestedConfig.helpers calls
            pure (ExecutionCallTransport.functions helpers)
          spans := leaves.spans
          projection := projection
          place := projection.place
          callFunction := callFunction
          choice := choice
          math := math }
    let foreignContext := {foreignContext with
      sourceAssembly := foreignBuilder.map fun build => fun _ => do
        let (_,assembly) ← build foreignContext
        pure assembly}
    let foreignOverride := foreignBuilder.map fun build => do
      let assembled ← build foreignContext
      pure assembled.1
    let ⟨boolTy⟩ ← liftConstruction (pureQuery (p.primitiveLayout "bool"))
    let ⟨u8Ty⟩ ← liftConstruction (pureQuery (p.primitiveLayout "u8"))
    let equalRight := fun (_ : C) (_ _ : FloatBits) => do
      if !options.floatNondeterministic then return false
      pure (!(← ExecutionChoices.boolean EvalCoreMachine.tape .floatEqual))
    let fuse := fun (_ : C) => do
      if !options.floatNondeterministic then return false
      ExecutionChoices.boolean EvalCoreMachine.tape .floatFuse
    let varArgs := IntrinsicSymbolsMachine.varArgs (CompilerVarArgsLeaves.make p options.compatibilityBudget)
      EvalConfiguration.symbols access pointers.arithmetic functions operands copy
    let typeId := IntrinsicSymbolsMachine.typeId (CompilerIntrinsicSymbols.typeIdLeaves p image)
      EvalConfiguration.symbols access functions operands copy
    let intrinsics := fun callee =>
      let atomic := ExecutionIntrinsic.Atomic.dispatcher atomics
        (fun _ index => physical (CompilerIntrinsicConstants.ordering p.intrinsics callee index))
        (fun _ index => physical (CompilerIntrinsicConstants.volatile p.intrinsics callee index))
        (fun c op => do let place ← dereference c op; pure ⟨.memory place.mplace,place.layout⟩)
        access projection.place returnToBlock
      let simd := ExecutionIntrinsic.Simd.make {
        boolTy := boolTy.ty
        u8Ty := u8Ty.ty
        isSimd := fun _ ty => query (CompilerArchitectureFacts.isSimd context ty)
        simdSizeAndType := fun _ ty => query (CompilerArchitectureFacts.simdSizeAndType context ty)
        shuffleConst := fun _ index => physical (CompilerIntrinsicConstants.shuffle p.intrinsics callee index)
        alignmentConst := fun _ index => physical (CompilerIntrinsicConstants.alignment p.intrinsics callee index)
        chooseEqualFloatRight := equalRight
        fuseMulAdd := fuse
        mathLane := Math.simdMathLane math }
        scalar floats casts returnToBlock access projection copy pointerCompiler pointers
      let core := ExecutionIntrinsic.Core.make {
        varArgsFuel := options.varArgsBudget
        maxSizeOfVal := maximum
        layoutOf := fun _ ty => RuntimeArrayQueries.layoutOf EvalProjectionMachine.arrays ty
        pointeeType := fun _ ty => do
          let some pointee ← query (CompilerFacts.builtinDeref context ty true)
            | throw (.invalidProgram "intrinsic requires a pointer type")
          pure pointee
        integerKind := fun _ ty => physical (CompilerExecutionProviders.integerKind context ty)
        usizeLayout := usize
        isizeLayout := fun _ => query (p.primitiveLayout "isize")
        applyFloatNondeterminism := fun c value => Math.floatFastError math c value 4
        chooseEqualFloatRight := equalRight
        fuseMulAdd := fuse
        floatFastError := Math.floatFastError math
        variantLayout := fun _ layout index => query (p.runtime.forVariant layout index |>.mapError toString)
        ensureMonomorphic := fun _ ty => do
          unless ← query (CompilerFacts.boolean context ty "is_monomorphic_enough") do
            throw (.invalidProgram "intrinsic type still requires instantiation")
        typeNameConstant := CompilerValueConstants.typeNameHook p functions pointers.arithmetic
          externStatic MemoryErrors.constant (fun a b => physical (compatibility a b))
        needsDrop := intrinsicQueries.needsDrop
        variantCount := intrinsicQueries.variantCount
        callerLocationConstant := EvalCallerLocationConstruction.hook p functions
          (VirtualCalls.callerLocation (ExecutionCalls.virtualHooks
            (CompilerCallConstruction.virtual p table PointerPlaceMachine.controlledAlignment)
            access operands options.place.debugAssertions)
            options.limits.callDispatch)
          (fun ty => CompilerFacts.builtinDeref context ty true)
          MemoryErrors.constant (fun a b => physical (compatibility a b))
        chooseStaticKnown := fun _ => ExecutionChoices.boolean EvalCoreMachine.tape .staticKnown }
        simd atomic typeId varArgs
        (fun c op => OperandMachine.evalOperand operands c op none)
        (fun c path op => OperandMachine.evalOperandAt operands c path op none)
        (fun c op => do let place ← dereference c op; pure ⟨.memory place.mplace,place.layout⟩)
        (fun c value => do let place ← PointerPlaceMachine.fromImmediate access pointerCompiler c value; pure ⟨.indirect place.mplace,place.layout⟩)
        scalar floats (Discriminant.readDiscriminant discr) (Discriminant.discriminantForVariant discr)
        (Unwind.handleCatchUnwind unwind) returnToBlock access allocation extra deallocateStack compiler projection.place copy pointers
        projection.dynamic projection.dynamicFuel validity options.limits.validation
      {core with mathHooks := some math}
    let llvm := fun callee => query (EvalArchitectureMachine.compilerDispatcher context p.intrinsics pointers
      leaves.checkLlvmSymbolClash math access projection (intrinsics callee).simdHooks (fun name os => .unsupported s!"unsupported foreign item {name} on {os}"))
    let ⟨rootSpan⟩ ← liftConstruction (pureQuery (CompilerContextSpan.rootSpan p.program))
    let ⟨helpers⟩ ← liftConstruction (pureQuery (CompilerCallConstruction.helpers p rootSpan (CompilerSignatureAbi.hook p)))
    let config : ExecutionMachine.Config MiriMemoryKind (User Os R P H D O Aff B Host) C O ABI.ExternAbi ClockHost := {
      access,allocation,compiler,projection,copy,retag,validity,lifecycle,functions,atomics,varArgs,intrinsics,floats
      operands := ⟨operands.checkPlaceType,operands.dereference,operands.runtimeChecks,operands.boolLayout,operands.constantAt⟩
      validationRecursive := fun _ _ => ValidityMachine.enforceValidityRecursively
      calls := CompilerCallConstruction.leaves p options.compatibilityBudget
        (foreignOverride.orElse fun _ => leaves.foreign.map pure) callBackend leaves.dynSymName llvm
      virtual := CompilerCallConstruction.virtual p table PointerPlaceMachine.controlledAlignment
      helpers := helpers
      control := ⟨CompilerBodySpan.get p⟩
      panic := EvalCallRuntime.panic p
        (EvalPanicMachine.queries p.program p.runtime bytes functions access) access.runtime.base unwind operands
      unwindTerminateFunction := fun _ reason => physical (CompilerPanicFacts.unwindTerminate p.program reason)
      ignoreOptionalOverflowChecks := options.ignoreOptionalOverflowChecks
      rvalues := CompilerFrameContext.rvalueLeaves p (EvalThreadLocalSource.hook p maximum extra leaves.pointerSource source)
      discriminant := discrQueries
      scalar := scalarQueries
      casts := castQueries
      backend := EvalBackendMachine.dispatcher
      intrinsicName := fun callee => query (CompilerIntrinsicFacts.itemName p.intrinsics callee)
      intrinsicMustOverride := fun callee => query (CompilerIntrinsicFacts.mustOverride p.intrinsics callee)
      intrinsicFallbackIsSpec := fun callee => query (CompilerIntrinsicFacts.fallbackIsSpec p.intrinsics callee)
      addresses := PointerMachine.User.addresses
      arithmetic := pointers.arithmetic
      isRawPointer := isRaw
      usizeLayout := usize
      pointeeLayout := pointeeLayout
      terminators := terminators
      preemptionChoice := fun _ => do
        let state : State Os R P H D O Aff B Host ← get
        let control := terminators.getControl state.machine.user
        ExecutionChoices.bernoulli EvalCoreMachine.tape .preemption control.preemptionRateBits }
    pure (config, foreignContext)

private def makeWithForeign (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : Options)
    (leaves : Leaves Os R P H D O Aff B Host C ClockHost) (choice : C)
    (sourceHostConfiguration : Option HostRuntime.Configuration)
    (foreignBuilder : Option (ForeignBuilder Os R P H D O Aff B Host C ClockHost Unit)) :
    Nat → Except StepError (ExecutionMachine.Config MiriMemoryKind
      (User Os R P H D O Aff B Host) C O ABI.ExternAbi ClockHost) :=
  fun capacity => (makeWithForeignContext p image bytes options leaves choice sourceHostConfiguration
    foreignBuilder capacity).map Prod.fst

/-! The legacy generic entry retains its complete semantic-hook input. The
production source entry below fixes the canonical Unix state dimensions and
constructs the ordered foreign resolver internally. -/
def make (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : Options)
    (leaves : Leaves Os R P H D O Aff B Host C ClockHost) (choice : C) :
    Nat → Except StepError (ExecutionMachine.Config MiriMemoryKind
      (User Os R P H D O Aff B Host) C O ABI.ExternAbi ClockHost) :=
  makeWithForeign p image bytes options leaves choice none none

private def buildSourceCallbacks [DecidableEq MiriMemoryKind] [DecidableEq Os]
    (p : CompilerProviders.Prepared) (image : AllocationImage.Imported) (options : Options)
    (sourceLeaves : SourceLeaves Os R EvalSyncObjectAccess.Payload H D Aff B Poll Instant System Native Profiler
      Raw Listener TcpStream Error ErrorHost Meta Path Place C ClockHost I AddrIter)
    (choice : C)
    (context : ForeignContext Os R EvalSyncObjectAccess.Payload H D
      (SourceOther Raw Listener TcpStream Error) Aff B
      (SourceHost Poll Instant System H D Raw Listener TcpStream Error Native Profiler) C ClockHost
      (EvalCallDispatchConstruction.SourceAssembly Os R EvalSyncObjectAccess.Payload H D Aff B
        Poll Instant System Native Profiler Raw Listener TcpStream Error C
        (EvalCallDispatchConstruction.SourceCallbackSeed Os R H D Aff B Poll Instant System Native Profiler
          Raw Listener TcpStream Error Meta Path Place C
          (Clock.HostHooks Instant System
            (SourceState Os R EvalSyncObjectAccess.Payload H D Aff B Poll Instant System Native Profiler
              Raw Listener TcpStream Error))
          CallInstance AddrIter)))
    (assembly : EvalCallDispatchConstruction.SourceAssembly Os R EvalSyncObjectAccess.Payload H D Aff B
      Poll Instant System Native Profiler Raw Listener TcpStream Error C
      (EvalCallDispatchConstruction.SourceCallbackSeed Os R H D Aff B Poll Instant System Native Profiler
        Raw Listener TcpStream Error Meta Path Place C
        (Clock.HostHooks Instant System
          (SourceState Os R EvalSyncObjectAccess.Payload H D Aff B Poll Instant System Native Profiler
            Raw Listener TcpStream Error))
        CallInstance AddrIter))
    (main : MainMachine.Hooks
      (EvalCallbackMachine.ThreadUser Os R EvalSyncObjectAccess.Payload H D
        (SourceOther Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler)
      C (SourceOther Raw Listener TcpStream Error) ABI.ExternAbi
      (FnAbi TyId) (ArgAbi TyId) Aff EvalSyncObjectAccess.Payload)
    (state : EvalCallbackMachine.State Os R EvalSyncObjectAccess.Payload H D
      (SourceOther Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler) :
    Except
      (StepError × EvalCallbackMachine.State Os R EvalSyncObjectAccess.Payload H D
        (SourceOther Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler)
      (SourceCallbackProduct Os R H D Aff B Poll Instant System Native Profiler
        Raw Listener TcpStream Error C AddrIter ×
       EvalCallbackMachine.State Os R EvalSyncObjectAccess.Payload H D
        (SourceOther Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler) := do
  match assembly.callbackSeed with
  | none => .error (.unsupported "source callback assembly lacks its canonical callback seed",state)
  | some seed =>
    let parts : Except StepError
      (EvalCallbackSourceConstruction.IoOperations Os R EvalSyncObjectAccess.Payload H D
        (SourceOther Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler
        Error EvalUnixFdConstruction.ArrayCursor Meta ×
       EvalCallbackSourceConstruction.SocketOperations Os R EvalSyncObjectAccess.Payload H D
        (SourceOther Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler
        Raw Listener TcpStream Error Error AddrIter) := do
      let unitLayout ← match p.primitiveLayout "unit_pointer_mut" with
        | .ok value => pure ⟨value.ty,value.layout⟩
        | .error reason => throw (.unsupported s!"compiler unit layout for callback IO: {reason}")
      let io ← EvalCallbackOperationConstruction.sourceIoOperations p seed.nativeFd seed.syncEffects
        context.validityAccess context.access context.projection context.place choice unitLayout
        seed.readinessRoute sourceLeaves.foreignSource.host.clock seed.errors
        sourceLeaves.foreignSource.pollBudget sourceLeaves.foreignSource.pollBudget
      let some memory := assembly.memory | throw (.unsupported "source socket-address memory bundle is absent")
      let addressHost : EvalSocketAddressConstruction.HostEffects
          (EvalCallDispatchConstruction.State Os R EvalSyncObjectAccess.Payload H D Aff B Poll Instant System
            Native Profiler Raw Listener TcpStream Error) Error AddrIter := {
        resolve := sourceLeaves.foreignSource.host.socket.resolve
        nextAddress := sourceLeaves.foreignSource.host.socket.nextAddress
        dropIterator := sourceLeaves.foreignSource.host.socket.dropIterator
        resolutionDiagnostic := sourceLeaves.foreignSource.host.socket.resolutionDiagnostic
        listBudget := sourceLeaves.foreignSource.stringScanBudget }
      let address ← match EvalSocketAddressConstruction.callbackFromSource p memory seed.errors addressHost with
        | .ok value => pure value
        | .error error => throw error
      let isolationReject := fun name => do
        match sourceLeaves.foreignSource.host.unixConfig.isolatedOp with
        | .allow => pure false
        | .reject .abort => throw (.termination (.unsupportedInIsolation name))
        | .reject .noWarning | .reject .warning | .reject .warningWithoutBacktrace => pure true
      let sockets ← EvalCallbackSocketConstruction.socketOperationsFromProtocols p seed.registry
        seed.virtual seed.tcp sourceLeaves.foreignSource.host.socket address context.access
        seed.nativeFd.fd.file.fd.asUnix sourceLeaves.hostConfiguration.communicate
        isolationReject sourceLeaves.foreignSource.fileReferenceBudget seed.nativeFd.vector.vector
      pure (io,sockets)
    match parts with
    | .error error => .error (error,state)
    | .ok (io,sockets) => do
      let facts := p.lifecycle.calls.symbols.facts
      let .ok targetFacts := p.externStatics.targetFacts |
        .error (.unsupported "pthread source target facts unavailable",state)
      let targetOs := targetFacts.os
      let .ok u8Value := p.primitiveLayout "u8" |
        .error (.unsupported "compiler u8 layout for pthread source objects unavailable",state)
      let u8Layout : LocalLayout := ⟨u8Value.ty,u8Value.layout⟩
      let checkExternStaticClash := fun symbol => do
        let symbols ← match p.foreignSymbols with
          | .ok symbols => pure symbols
          | .error reason => throw (.unsupported s!"compiler foreign-symbol query: {reason}")
        match CompilerForeignSymbols.checkSymbolClash symbols symbol with
        | .ok () => pure ()
        | .error error => throw error
      let globalMemory : CompilerLinkSections.Memory MiriMemoryKind
          (EvalSyncMachine.User Os R EvalSyncObjectAccess.Payload H D
            (SourceOther Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler)
          (SourceOther Raw Listener TcpStream Error) := {
        functions := context.functions
        externStatic := CompilerExternStatic.resolve p.externStatics image
          checkExternStaticClash context.functions
          (fun user => EvalWorld.roots.externStatics (ExecutionStateTransport.toOuter user))
        projection := context.compiler.projection choice
        readImmediate := PlaceMachine.readImmediate context.access }
      let objectHooks := EvalCallbackSyncConstruction.objectHooksFromSource
        facts context.access context.allocation context.compiler context.dynamic context.vtable
        context.dynamicFuel context.atomics context.extras context.pointers
      let objectResult := (ExecutionStateTransport.action
        (EvalTypedSyncMachine.objectsFromPhysical objectHooks
          EvalSyncObjectAccess.typedEmbedding seed.syncEffects choice u8Layout targetOs
          p.namedGlobals globalMemory)).run state
      match objectResult with
      | .error error afterObjects => .error (error,afterObjects)
      | .ok objects afterObjects =>
        match sourceLeaves.foreignSource.host.time with
        | none => do
          /- Chrono is needed only by `localtime_r`. The remaining Unix time
          shims use the real machine clock and deadline registry, so keep the
          source-built time dictionary installed when the optional chrono
          provider is absent. -/
          let some memory := assembly.memory |
            .error (.unsupported "source time-shim memory bundle is absent",afterObjects)
          let chronoMissing : EvalTimeConstruction.HostEffects
              (EvalTimeConstruction.State Os R EvalSyncObjectAccess.Payload H D
                (SourceOther Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler)
              Unit Unit := {
            utc := ()
            utcTimestamp := fun _ => throw (.unsupported "Unix chrono timestamp capability is absent")
            parseTimezone := fun _ => throw (.unsupported "Unix chrono timezone database is absent")
            withTimezone := fun _ _ => throw (.unsupported "Unix chrono timezone conversion is absent") }
          let timezoneString := fun os =>
            match String.fromUTF8? (sourceLeaves.foreignSource.host.os.encodedBytes os) with
            | some value => Except.ok value
            | none => Except.error ()
          let timeResult : Except StepError (TimeShims.Hooks
              (SourceState Os R EvalSyncObjectAccess.Payload H D Aff B Poll Instant System Native Profiler
                Raw Listener TcpStream Error)
              Instant System Unit Unit) :=
            EvalTimeConstruction.fromSourceWithEnvironment p memory
              sourceLeaves.foreignSource.host.environment sourceLeaves.foreignSource.host.os
              context.functions seed.syncEffects seed.errors sourceLeaves.foreignSource.host.clock
              sourceLeaves.foreignSource.host.systemDurationSince timezoneString
              sourceLeaves.hostConfiguration.communicate chronoMissing
          match timeResult with
          | .error error => .error (error,afterObjects)
          | .ok time => do
            let components : EvalCallbackSourceConstruction.Components Os R EvalSyncObjectAccess.Payload H D
              (SourceOther Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler
              C Unit Unit Error EvalUnixFdConstruction.ArrayCursor Meta Raw Listener TcpStream Error AddrIter := {
              futex := none
              io
              sockets
              descriptor := EvalCallbackSocketConstruction.socketDescriptor Raw Listener TcpStream Error
              nestedCapacity := options.callbackCapacity
              synchronousResource := sourceLeaves.foreignSource.pollBudget }
            match EvalCallbackSourceConstruction.fromSource main components afterObjects with
            | .error (error,after) => .error (error,after)
            | .ok (baseCallbacks,after) => do
              let deadline := EvalSyncMachine.deadlines sourceLeaves.foreignSource.host.clock
                (pure sourceLeaves.hostConfiguration.communicate)
                sourceLeaves.foreignSource.host.systemDurationSince
                (fun token kind => ExecutionStateTransport.reverseAction
                  (EvalCallbackMachine.invoke baseCallbacks choice token kind))
              let futexResult := (ExecutionStateTransport.action
                (EvalCallbackFutexConstruction.fromSource facts context.access context.allocation
                  context.compiler context.dynamic context.vtable options.place.dynamicFuel
                  context.atomics context.extras context.pointers sourceLeaves.hostConfiguration
                  context.projection choice deadline seed.errors)).run after
              match futexResult with
              | .error error afterFutex => .error (error,afterFutex)
              | .ok futex afterFutex =>
                let callbacks := {baseCallbacks with futex := some futex}
                let deadline := EvalSyncMachine.deadlines sourceLeaves.foreignSource.host.clock
                  (pure sourceLeaves.hostConfiguration.communicate)
                  sourceLeaves.foreignSource.host.systemDurationSince
                  (fun token kind => ExecutionStateTransport.reverseAction
                    (EvalCallbackMachine.invoke callbacks choice token kind))
                let product : SourceCallbackProduct Os R H D Aff B Poll Instant System Native Profiler
                    Raw Listener TcpStream Error C AddrIter := {
                  Zone := Unit
                  Timestamp := Unit
                  hooks := callbacks
                  main
                  time := some time
                  objects
                  deadline
                  }
                .ok (product,afterFutex)
        | some timeSource => do
          let some memory := assembly.memory |
            .error (.unsupported "source time-shim memory bundle is absent",afterObjects)
          let timeResult : Except StepError (TimeShims.Hooks
              (SourceState Os R EvalSyncObjectAccess.Payload H D Aff B Poll Instant System Native Profiler
                Raw Listener TcpStream Error)
              Instant System timeSource.Zone timeSource.Timestamp) :=
            EvalTimeConstruction.fromSourceWithEnvironment p memory
              sourceLeaves.foreignSource.host.environment sourceLeaves.foreignSource.host.os
              context.functions seed.syncEffects seed.errors sourceLeaves.foreignSource.host.clock
              sourceLeaves.foreignSource.host.systemDurationSince timeSource.timezoneString
              sourceLeaves.hostConfiguration.communicate timeSource.effects
          match timeResult with
          | .error error => .error (error,afterObjects)
          | .ok time => do
            let components : EvalCallbackSourceConstruction.Components Os R EvalSyncObjectAccess.Payload H D
              (SourceOther Raw Listener TcpStream Error) Aff B Poll Instant System Native Profiler
              C timeSource.Zone timeSource.Timestamp Error EvalUnixFdConstruction.ArrayCursor Meta
              Raw Listener TcpStream Error AddrIter := {
              futex := none
              io
              sockets
              descriptor := EvalCallbackSocketConstruction.socketDescriptor Raw Listener TcpStream Error
              nestedCapacity := options.callbackCapacity
              synchronousResource := sourceLeaves.foreignSource.pollBudget }
            match EvalCallbackSourceConstruction.fromSource main components afterObjects with
            | .error (error,after) => .error (error,after)
            | .ok (baseCallbacks,after) => do
              let deadline := EvalSyncMachine.deadlines sourceLeaves.foreignSource.host.clock
                (pure sourceLeaves.hostConfiguration.communicate)
                sourceLeaves.foreignSource.host.systemDurationSince
                (fun token kind => ExecutionStateTransport.reverseAction
                  (EvalCallbackMachine.invoke baseCallbacks choice token kind))
              let futexResult := (ExecutionStateTransport.action
                (EvalCallbackFutexConstruction.fromSource facts context.access context.allocation
                  context.compiler context.dynamic context.vtable options.place.dynamicFuel
                  context.atomics context.extras context.pointers sourceLeaves.hostConfiguration
                  context.projection choice deadline seed.errors)).run after
              match futexResult with
              | .error error afterFutex => .error (error,afterFutex)
              | .ok futex afterFutex =>
                let callbacks := {baseCallbacks with futex := some futex}
                let deadline := EvalSyncMachine.deadlines sourceLeaves.foreignSource.host.clock
                  (pure sourceLeaves.hostConfiguration.communicate)
                  sourceLeaves.foreignSource.host.systemDurationSince
                  (fun token kind => ExecutionStateTransport.reverseAction
                    (EvalCallbackMachine.invoke callbacks choice token kind))
                let product : SourceCallbackProduct Os R H D Aff B Poll Instant System Native Profiler
                    Raw Listener TcpStream Error C AddrIter := {
                  Zone := timeSource.Zone
                  Timestamp := timeSource.Timestamp
                  hooks := callbacks
                  main
                  time := some time
                  objects
                  deadline
                  }
                .ok (product,afterFutex)

private def sourcePanicUnwinds (p : CompilerProviders.Prepared) : Except StepError Bool := do
  let producer ← (p.program.input.raw.getObjVal? "producer").mapError fun _ =>
    StepError.unsupported "source compiler panic strategy is missing"
  let settings ← (producer.getObjVal? "input_settings").mapError fun _ =>
    StepError.unsupported "source compiler panic strategy is missing"
  let status ← (settings.getObjVal? "status").mapError fun _ =>
    StepError.unsupported "source compiler settings status is missing"
  let status ← status.getStr?.mapError fun _ =>
    StepError.unsupported "source compiler settings status is malformed"
  unless status == "supported" do
    throw (.unsupported "source compiler settings are not supported")
  let strategy ← (settings.getObjVal? "effective_panic_strategy").mapError fun _ =>
    StepError.unsupported "source compiler panic strategy is missing"
  let strategy ← strategy.getStr?.mapError fun _ =>
    StepError.unsupported "source compiler panic strategy is malformed"
  match strategy with
  | "unwind" => pure true
  | "abort" | "immediate-abort" => pure false
  | _ => throw (.unsupported s!"unknown source compiler panic strategy: {strategy}")

/-- Source-owned Core construction for the canonical Unix EvalWorld. This
entry fixes the Other/Host state dimensions, derives native-library paths from
the active HostRuntime, and internally constructs the ordered foreign factory
from typed source components. There is no complete foreign-hook input. -/
def makeFromSourcePackage [DecidableEq Os]
    (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : Options)
    (sourceLeaves : SourceLeaves Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B Poll Instant System Native Profiler
      Raw Listener TcpStream Error ErrorHost Meta Path Place C ClockHost I AddrIter)
    (choice : C) : Nat → Except StepError
      (SourcePackage Os R H D CpuAffinity.Mask B Poll Instant System Native Profiler Raw Listener TcpStream Error
        ErrorHost Meta Path Place C ClockHost AddrIter)
  | 0 => .error (.resourceExhaustion "execution callback construction capacity")
  | remaining + 1 => do
      let panicUnwindsLifted : ULift.{1} Bool ← match sourcePanicUnwinds p with
        | .ok value => .ok ⟨value⟩
        | .error error => .error error
      let panicUnwinds := panicUnwindsLifted.down
      let options := {options with panicUnwinds}
      let other := SourceOther Raw Listener TcpStream Error
      let sourceHost := SourceHost Poll Instant System H D Raw Listener TcpStream Error Native Profiler
      let sourcePointer : EvalPointerSource.Leaves Os R EvalSyncObjectAccess.Payload H D other CpuAffinity.Mask B sourceHost C := {
        nativeLibraryPaths := fun host => host.nativeLibraries.map Prod.fst
        nativeHost := sourceLeaves.nativeHost
         }
      let leaves : Leaves Os R EvalSyncObjectAccess.Payload H D other CpuAffinity.Mask B sourceHost C ClockHost := {
        pointerSource := sourcePointer
        sync := EvalSyncObjectAccess.onAccess
        storage := sourceLeaves.storage
        spans := sourceLeaves.spans
        foreign := none
        dynSymName := sourceLeaves.dynSymName
        checkLlvmSymbolClash := sourceLeaves.checkLlvmSymbolClash
        math := sourceLeaves.math
        mathError := sourceLeaves.mathError
        control := sourceLeaves.control
        blockingSources := sourceLeaves.blockingSources }
      let nativeLibraryPaths := fun (state :
          EvalCallDispatchConstruction.State Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B Poll Instant System Native Profiler Raw Listener TcpStream Error) =>
        state.machine.user.payload.payload.user.host.nativeLibraries.map Prod.fst
      let build : ForeignBuilder Os R EvalSyncObjectAccess.Payload H D other CpuAffinity.Mask B sourceHost C ClockHost
          (EvalCallDispatchConstruction.SourceAssembly Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B
            Poll Instant System Native Profiler Raw Listener TcpStream Error C
            (EvalCallDispatchConstruction.SourceCallbackSeed Os R H D CpuAffinity.Mask B Poll Instant System Native Profiler
              Raw Listener TcpStream Error Meta Path Place C
              (Clock.HostHooks Instant System
                (SourceState Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B Poll Instant System Native Profiler
                  Raw Listener TcpStream Error))
              CallInstance AddrIter)) := fun context => do
        let memory ← match environmentMemoryFromCore p context.access context.allocation context.extras
            context.deallocationDiagnostic context.nativeDrop context.pointers context.spans
            context.projection context.choice sourceLeaves.foreignSource.alignment
            sourceLeaves.foreignSource.stringScanBudget with
          | .ok memory => pure memory
          | .error error => throw error
        unless sourceLeaves.foreignSource.host.unixConfig.communicate ==
            sourceLeaves.hostConfiguration.communicate do
          throw (.invalidProgram "source Unix host config differs from HostRuntime configuration")
        let nativeLifecycleBacking := sourceLeaves.nativeHost.map fun host =>
          NativeAllocationLifecycle.liftBacking host.backing
        let assembled ← EvalCallDispatchConstruction.fromSeedEnvironment p nativeLibraryPaths
          (fun name destination args =>
            EvalNativeSourceConstruction.call
              sourceLeaves.hostConfiguration.hostUsizeBits nativeLifecycleBacking p
              EvalProjectionMachine.arrays sourceLeaves.nativeBackend context.validityAccess
              context.pointers context.validity options.limits.validation
              options.limits.callDispatch context.choice options.compatibilityBudget name
              (RuntimePlace.mk (.memory destination.mplace) destination.layout) args)
          context.validityAccess context.access context.allocation context.compiler
          context.projection context.extras
          context.deallocationDiagnostic context.nativeDrop context.pointers context.spans
          context.functions context.place context.callFunction context.choice context.math
          context.threadFunctions
          sourceLeaves.foreignSource.host sourceLeaves.hostConfiguration
          memory bytes sourceLeaves.foreignSource.geometry
          options.userRelevantCrates options.compatibilityBudget
          sourceLeaves.foreignSource.fileReferenceBudget
          sourceLeaves.foreignSource.watcherReferenceBudget options.place.debugAssertions
          sourceLeaves.hostConfiguration.hostUsizeBits
          sourceLeaves.foreignSource.stringScanBudget
          sourceLeaves.foreignSource.shortFdOperations options.varArgsBudget
        let foreign := EvalForeignConstruction.bindMemory p context.validityAccess context.pointers
          context.place memory.symbolicAlignment memory.enforceAlignment context.choice
          sourceLeaves.foreignSource.stringScanBudget assembled.foreign
        let foreign := EvalPortableForeignRuntime.bindBacktrace p image context.functions
          context.access context.pointers.arithmetic context.projection context.choice
          (2 ^ sourceLeaves.hostConfiguration.hostUsizeBits - 1) foreign
        let assembled := {assembled with foreign}
        pure (foreign, assembled)
      let (execution, context) ← makeWithForeignContext p image bytes options leaves choice
        (some sourceLeaves.hostConfiguration)
        (some build) (Assembly := EvalCallDispatchConstruction.SourceAssembly Os R
          EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B Poll Instant System Native Profiler Raw Listener TcpStream Error C
          (EvalCallDispatchConstruction.SourceCallbackSeed Os R H D CpuAffinity.Mask B Poll Instant System Native Profiler
            Raw Listener TcpStream Error Meta Path Place C
            (Clock.HostHooks Instant System
              (SourceState Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B Poll Instant System Native Profiler
                Raw Listener TcpStream Error))
            CallInstance AddrIter))
        (remaining + 1)
      let callbackBuilder := fun (assembly : EvalCallDispatchConstruction.SourceAssembly Os R
          EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B Poll Instant System Native Profiler
          Raw Listener TcpStream Error C
          (EvalCallDispatchConstruction.SourceCallbackSeed Os R H D CpuAffinity.Mask B Poll Instant System Native Profiler
            Raw Listener TcpStream Error Meta Path Place C
            (Clock.HostHooks Instant System
              (SourceState Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B Poll Instant System Native Profiler
                Raw Listener TcpStream Error))
            CallInstance AddrIter))
          (_execution : ExecutionMachine.Config MiriMemoryKind
            (SourceUser Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B Poll Instant System Native Profiler
              Raw Listener TcpStream Error)
            C (SourceOther Raw Listener TcpStream Error) ABI.ExternAbi ClockHost)
          (main : MainMachine.Hooks
            (EvalCallbackMachine.ThreadUser Os R EvalSyncObjectAccess.Payload H D
              (SourceOther Raw Listener TcpStream Error) CpuAffinity.Mask B Poll Instant System Native Profiler)
            C (SourceOther Raw Listener TcpStream Error) ABI.ExternAbi
            (FnAbi TyId) (ArgAbi TyId) CpuAffinity.Mask EvalSyncObjectAccess.Payload)
          (state : EvalCallbackMachine.State Os R EvalSyncObjectAccess.Payload H D
            (SourceOther Raw Listener TcpStream Error) CpuAffinity.Mask B Poll Instant System Native Profiler) =>
          buildSourceCallbacks p image options sourceLeaves choice context assembly main state
      let rebindCallbacks := fun
          (callbackProduct : SourceCallbackProduct Os R H D CpuAffinity.Mask B Poll Instant System Native Profiler
            Raw Listener TcpStream Error C AddrIter)
          (selectedExecution : ExecutionMachine.Config MiriMemoryKind
            (SourceUser Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B Poll Instant System Native Profiler
              Raw Listener TcpStream Error)
            C (SourceOther Raw Listener TcpStream Error) ABI.ExternAbi ClockHost) => Id.run do
        let selectedChoice := choice
        let callbacks := callbackProduct.hooks
        let callbackForeign : M Os R EvalSyncObjectAccess.Payload H D
            (SourceOther Raw Listener TcpStream Error) CpuAffinity.Mask B
            (SourceHost Poll Instant System H D Raw Listener TcpStream Error Native Profiler)
            (ForeignItems.Hooks Provenance
              (State Os R EvalSyncObjectAccess.Payload H D
                (SourceOther Raw Listener TcpStream Error) CpuAffinity.Mask B
                (SourceHost Poll Instant System H D Raw Listener TcpStream Error Native Profiler))
              (RuntimePlace Provenance) (RuntimePlace Provenance)
              (Pointer (Option Provenance)) LoadedBody CallInstance) := do
          let some buildAssembly := context.sourceAssembly |
            throw (.unsupported "callback-aware foreign resolver lacks the source assembly builder")
          let assembly ← buildAssembly ()
          let some seed := assembly.callbackSeed |
            throw (.unsupported "callback-aware foreign assembly lacks its canonical callback seed")
          let some memory := assembly.memory |
            throw (.unsupported "callback-aware foreign assembly lacks its canonical memory bundle")
          let callbacks := EvalCallbackMachine.prepare callbacks selectedChoice
          let sourceIo := callbacks.socket.tcp.source.io
          let zero : Clock.Duration := ⟨0,0,by decide⟩
          let pollAndUnblockZero : EStateM StepError
              (EvalCallbackMachine.Inner Os R EvalSyncObjectAccess.Payload H D
                (SourceOther Raw Listener TcpStream Error) CpuAffinity.Mask B Poll Instant System Native Profiler) Unit := do
            let readiness ← EvalCallbackMachine.innerReadiness callbacks selectedChoice sourceIo.readiness
            BlockingIo.pollAndUnblock callbacks.wakeBudget {sourceIo with readiness} (some zero)
          let socketFiles := EvalCallbackSocketConstruction.socketFileEffects
            sourceLeaves.foreignSource.fileReferenceBudget
            callbacks.socket.virtual.source callbacks.socket.tcp.source
          let errorFromKind : IoError.ErrorKind → EStateM StepError
              (EvalCallDispatchConstruction.State Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B Poll Instant
                System Native Profiler Raw Listener TcpStream Error)
              (IoError.Error Error) := fun kind => do
            pure (.host (← sourceLeaves.foreignSource.host.ioError.hostFromKind kind))
          let otherFiles := EvalCallbackSocketConstruction.otherFileEffects seed.registry
            callbacks.io.event (some socketFiles)
            sourceLeaves.foreignSource.fileReferenceBudget errorFromKind
          let baseCore := assembly.foreign.toCore
          let pthreadHooks ← EvalUnixPthreadConstruction.fromSource p
            options.compatibilityBudget {
              objects := callbackProduct.objects
              access := context.validityAccess
              projection := context.projection
              place := context.place
              choice := selectedChoice
              deadline := callbackProduct.deadline
              ioError := seed.errors
              noIsolation := fun name => do
                unless sourceLeaves.hostConfiguration.communicate do
                  throw (.termination (.unsupportedInIsolation name))
              checkSymbolClash := baseCore.checkSymbolClash }
          let pthreadHandler : UnixForeign.Handler
              (EvalCallDispatchConstruction.State Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B Poll Instant
                System Native Profiler Raw Listener TcpStream Error) :=
            fun name abi args destination =>
              PthreadDispatch.dispatch sourceLeaves.foreignSource.pollBudget pthreadHooks
                name abi args destination
          let callbackSocketDispatch : SocketDispatch.Hooks
              (EvalCallbackMachine.Inner Os R EvalSyncObjectAccess.Payload H D
                (SourceOther Raw Listener TcpStream Error) CpuAffinity.Mask B Poll Instant System Native Profiler)
              (EvalCallbackMachine.FD H D (SourceOther Raw Listener TcpStream Error)) Error AddrIter := {
            socket := callbacks.socket.socket
            virtual := callbacks.socket.virtual.source
            expectedAbi := fun name => CompilerNamedShimAbi.query p.namedAbi name
            argumentCompat := fun caller callee =>
              (CompilerCallConstruction.compiler p options.compatibilityBudget).checkArgumentCompat
                selectedChoice caller callee
            checkSymbolClash := baseCore.checkSymbolClash
            transmute := fun operand target => do
              let projection ← context.place.projection selectedChoice
              match operand.transmute projection target |>.mapError IntrinsicVectorMachine.projectionError with
              | .ok value => pure value
              | .error error => throw error
            writeScalar := fun scalar destination =>
              writePlaceImmediate context.place selectedChoice (.scalar scalar)
                ⟨.memory destination.mplace,destination.layout⟩
            pollAndUnblockZero }
          let socketHandler : UnixForeign.Handler
              (EvalCallDispatchConstruction.State Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B Poll Instant
                System Native Profiler Raw Listener TcpStream Error) :=
            fun name abi args destination =>
              SocketDispatch.dispatch callbackSocketDispatch name abi args destination
          let callbackPollDispatch : PollDispatch.Hooks
              (EvalCallbackMachine.Inner Os R EvalSyncObjectAccess.Payload H D
                (SourceOther Raw Listener TcpStream Error) CpuAffinity.Mask B Poll Instant System Native Profiler)
              (EvalCallbackMachine.FD H D (SourceOther Raw Listener TcpStream Error))
              EvalUnixFdConstruction.ArrayCursor := {
            epoll := callbacks.io.epoll
            os := assembly.foreign.os
            communicate := sourceLeaves.hostConfiguration.communicate
            pollAndUnblockZero
            pollAbi := CompilerNamedShimAbi.query p.namedAbi "poll"
            argumentCompat := fun caller callee =>
              (CompilerCallConstruction.compiler p options.compatibilityBudget).checkArgumentCompat
                selectedChoice caller callee
            checkSymbolClash := baseCore.checkSymbolClash
            transmute := fun operand target => do
              let projection ← context.place.projection selectedChoice
              match operand.transmute projection target |>.mapError IntrinsicVectorMachine.projectionError with
              | .ok value => pure value
              | .error error => throw error }
          let pollHandler : UnixForeign.Handler
              (EvalCallDispatchConstruction.State Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B Poll Instant
                System Native Profiler Raw Listener TcpStream Error) :=
            fun name abi args destination =>
              PollDispatch.dispatch sourceLeaves.foreignSource.pollBudget callbackPollDispatch
                name abi args destination
          let eventDispatch : EventFdDispatch.SourceHooks
              (EvalCallbackMachine.Inner Os R EvalSyncObjectAccess.Payload H D
                (SourceOther Raw Listener TcpStream Error) CpuAffinity.Mask B Poll Instant System Native Profiler)
              (EvalCallbackMachine.FD H D (SourceOther Raw Listener TcpStream Error)) := {
            event := callbacks.io.event
            os := assembly.foreign.os
            checkSymbolClash := baseCore.checkSymbolClash
            writeI32 := fun value destination => do
              let scalar ← match Scalar.fromInt value.toInt (Size.ofBytes 4) with
                | .ok scalar => pure scalar
                | .error error => throw (ScalarOps.scalarError error)
              writePlaceImmediate context.place selectedChoice (.scalar scalar)
                ⟨.memory destination.mplace,destination.layout⟩ }
          let eventHandler : UnixForeign.OptionalHandler
              (EvalCallDispatchConstruction.State Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B Poll Instant
                System Native Profiler Raw Listener TcpStream Error) :=
            fun name abi args destination =>
              EventFdDispatch.emulateSource eventDispatch name abi args destination
          let choiceTape : ExecutionChoices.Access
              (EvalCallDispatchConstruction.State Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B Poll Instant
                System Native Profiler Raw Listener TcpStream Error) := EvalCoreMachine.tape
          let memoryDestination := fun (destination : RuntimePlace Provenance) => do
            match destination.ref with
            | .memory place => pure (⟨place,destination.layout⟩ : MPlaceTy Provenance)
            | .local .. => throw (.invalidProgram "callback-aware foreign destination was not materialized")
          let unixCore : ForeignItems.Core Provenance
              (EvalCallDispatchConstruction.State Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B Poll Instant
                System Native Profiler Raw Listener TcpStream Error)
              (RuntimePlace Provenance) (MPlaceTy Provenance)
              (Pointer (Option Provenance)) LoadedBody CallInstance := {
            baseCore with
            forceAllocation := fun destination => do
              memoryDestination (← baseCore.forceAllocation destination)
            callNative := fun name destination args =>
              baseCore.callNative name ⟨.memory destination.mplace,destination.layout⟩ args
            writePointer := fun pointer destination =>
              baseCore.writePointer pointer ⟨.memory destination.mplace,destination.layout⟩
            writeNull := fun destination =>
              baseCore.writeNull ⟨.memory destination.mplace,destination.layout⟩
            specialDestination := fun destination => do
              memoryDestination (← baseCore.forceAllocation destination) }
          let dynamicHandler ← match EvalUnixDynamicConstruction.handlerFromSource p memory
              context.functions selectedChoice
              (EvalCallRuntime.unwind context.access context.projection context.functions
                options.panicUnwinds context.callFunction)
              unixCore with
            | .ok handler => pure handler
            | .error error => throw error
          let affinityHandler := match assembly.environment with
            | none => assembly.dispatchers.affinity
            | some environment =>
              EvalUnixAffinityConstruction.handlerFromSource p memory environment
                context.place selectedChoice unixCore
          let solarishHandler : UnixForeign.OptionalHandler
              (EvalCallDispatchConstruction.State Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B Poll Instant
                System Native Profiler Raw Listener TcpStream Error) :=
            if #[("solaris" : String),"illumos"].contains assembly.foreign.os then
              match assembly.environment with
              | none => fun _ _ _ _ => throw (.unsupported "Solarish dispatch lacks the source Unix environment")
              | some environment =>
                match EvalUnixSolarishConstruction.fromSource p environment unixCore
                    context.validityAccess context.projection context.place selectedChoice
                    callbacks.io.epoll callbacks.io.event sourceLeaves.foreignSource.pollBudget
                    sourceLeaves.foreignSource.geometry.stackAddress
                    sourceLeaves.foreignSource.geometry.stackSize with
                | .ok solarish => fun name abi args destination =>
                    SolarishForeign.emulateCore solarish name abi args destination
                | .error error => fun _ _ _ _ => throw error
            else assembly.dispatchers.solarish
          let freebsdHandler : UnixForeign.OptionalHandler
              (EvalCallDispatchConstruction.State Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B Poll Instant
                System Native Profiler Raw Listener TcpStream Error) :=
            match callbacks.futex with
            | none => assembly.dispatchers.freebsd
            | some sourceFutex =>
              let freebsdSync := EvalUnixFreeBsdConstruction.syncFromSource p
                callbackProduct.objects selectedChoice context.projection
                sourceLeaves.hostConfiguration.communicate sourceFutex
              EvalUnixFreeBsdConstruction.handlerFromSource unixCore seed.errors freebsdSync
          let netbsdHandler : UnixForeign.OptionalHandler
              (EvalCallDispatchConstruction.State Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B Poll Instant
                System Native Profiler Raw Listener TcpStream Error) :=
            if assembly.foreign.os == "netbsd" then
              match assembly.environment with
              | none => fun _ _ _ _ => throw (.unsupported "NetBSD dispatch lacks the source Unix environment")
              | some environment =>
                let netbsd : NetBsdForeign.CoreHooks
                    (EvalCallDispatchConstruction.State Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B Poll Instant
                      System Native Profiler Raw Listener TcpStream Error)
                    Os Error EnvVars.Kind
                    (RuntimePlace Provenance) LoadedBody CallInstance := {
                  foreign := unixCore
                  environment := environment.env
                  signature := CompilerNamedShimAbi.query p.namedAbi }
                fun name abi args destination =>
                  NetBsdForeign.emulateCore netbsd name abi args destination
            else assembly.dispatchers.netbsd
          let currentExe : EStateM StepError
              (EvalCallDispatchConstruction.State Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B Poll
                Instant System Native Profiler Raw Listener TcpStream Error) (Option Os) :=
            match sourceLeaves.foreignSource.host.filesystem with
            | none => throw (.unsupported "source host executable-path capability is unavailable")
            | some fsCapability => do
              let path ← fsCapability.effects.currentExe
              pure (path.map fsCapability.osFromPath)
          let hostGetrandom := sourceLeaves.foreignSource.host.getrandom.getD
            (fun _ => pure (.error "source host random fill is unavailable"))
          let macosHandler : UnixForeign.OptionalHandler
              (EvalCallDispatchConstruction.State Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B Poll Instant
                System Native Profiler Raw Listener TcpStream Error) :=
            if assembly.foreign.os == "macos" then
              match assembly.environment, assembly.memory, callbacks.futex with
              | some environment, some memory, some sourceFutex =>
                match EvalUnixMacOsConstruction.handlerFromSource p baseCore environment.env callbackProduct.main memory
                    callbackProduct.objects sourceFutex callbackProduct.time pthreadHooks.pthread
                    seed.nativeFd.fd.file.fd selectedChoice sourceLeaves.hostConfiguration.communicate
                    hostGetrandom choiceTape currentExe sourceLeaves.hostConfiguration.hostUsizeBits
                    sourceLeaves.foreignSource.pollBudget
                    sourceLeaves.foreignSource.geometry.stackAddress
                    sourceLeaves.foreignSource.geometry.stackSize with
                | .ok handler => handler
                | .error error => fun _ _ _ _ => throw error
              | _, _, _ => fun _ _ _ _ =>
                  throw (.unsupported "macOS foreign dispatch lacks a canonical environment, memory, or futex source")
            else assembly.dispatchers.macos
          let random := RandomMemory.machine context.access choiceTape
            sourceLeaves.hostConfiguration.communicate sourceLeaves.hostConfiguration.hostUsizeBits
            hostGetrandom
          let randomDispatch := UnixRandomDispatch.sourceHooks unixCore random
            (CompilerNamedShimAbi.query p.namedAbi)
            (fun name destination => IoError.setErrnoAndReturnNeg1 seed.errors (.libc name) destination)
            (fun value destination => do
              let scalar ← match Scalar.fromUInt (BitVec.ofNat 128 value.toNat)
                  context.access.runtime.pointerSize with
                | .ok scalar => pure scalar
                | .error error => throw (ScalarOps.scalarError error)
              writePlaceImmediate context.place selectedChoice (.scalar scalar)
                ⟨.memory destination.mplace,destination.layout⟩)
          let randomHandler : UnixForeign.OptionalHandler
              (EvalCallDispatchConstruction.State Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B Poll Instant
                System Native Profiler Raw Listener TcpStream Error) :=
            fun name abi args destination =>
              UnixRandomDispatch.emulate randomDispatch name abi args destination
          let timeHandler : UnixForeign.Handler
              (EvalCallDispatchConstruction.State Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B Poll Instant
                System Native Profiler Raw Listener TcpStream Error) :=
            match callbackProduct.time with
            | none => fun name abi args destination =>
                assembly.dispatchers.time name abi args destination
            | some timeHooks =>
              let timeDispatch : TimeShimDispatch.Hooks
                  (EvalCallDispatchConstruction.State Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B Poll Instant
                    System Native Profiler Raw Listener TcpStream Error)
                  Instant System callbackProduct.Zone callbackProduct.Timestamp := {
                time := timeHooks
                expectedAbi := fun name _signature => CompilerNamedShimAbi.query p.namedAbi name
                systemConvention := pure .C
                argumentCompat := fun caller callee =>
                  (CompilerCallConstruction.compiler p options.compatibilityBudget).checkArgumentCompat
                    selectedChoice caller callee
                checkSymbolClash := baseCore.checkSymbolClash
                transmute := fun operand target => do
                  let projection ← context.place.projection selectedChoice
                  match operand.transmute projection target |>.mapError IntrinsicVectorMachine.projectionError with
                  | .ok value => pure value
                  | .error error => throw error }
              fun name abi args destination =>
                TimeShimDispatch.dispatch timeDispatch name abi args destination
          let compilerFacts := p.lifecycle.calls.symbols.facts.context
          let syscallSignatureHooks : ShimSignatures.Hooks Provenance
              (EvalCallDispatchConstruction.State Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B Poll Instant
                System Native Profiler Raw Listener TcpStream Error)
              (RuntimePlace Provenance) (RuntimePlace Provenance)
              (Pointer (Option Provenance)) LoadedBody CallInstance :=
            CompilerShimSignatures.hooks compilerFacts {
              foreign := assembly.foreign
              types := CompilerFacts.compatibilityQueries compilerFacts
              isCVoid := fun ty => match CompilerFacts.boolean compilerFacts ty "is_c_void" with
                | .ok value => pure value
                | .error reason => throw (.unsupported s!"compiler c_void query: {reason}")
              readScalar := fun operand => do
                let immediate ← ValidityMachine.readImmediate memory.access operand
                match immediate.imm.toScalar with
                | .ok value => pure value
                | .error error => throw (ScalarOps.immediateError error)
              hostUsizeBits := sourceLeaves.hostConfiguration.hostUsizeBits }
          let syscallDispatch : LinuxSyscallPartialDispatch.Hooks
              (EvalCallDispatchConstruction.State Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B Poll Instant
                System Native Profiler Raw Listener TcpStream Error)
              (RuntimePlace Provenance) (RuntimePlace Provenance)
              (Pointer (Option Provenance)) LoadedBody CallInstance
              (EvalCallbackMachine.FD H D (SourceOther Raw Listener TcpStream Error)) := {
            os := assembly.foreign.os
            syscall := {
              signatures := syscallSignatureHooks
              signature := CompilerLinuxSyscall.signature p.namedAbi
              argumentTypes := fun types =>
                match CompilerLinuxSyscall.argumentTypes p types with
                | .ok value => pure value
                | .error reason => throw (.unsupported s!"compiler syscall varargs: {reason}")
              typeBudget := sourceLeaves.foreignSource.varArgsBudget
              libcUsize := CompilerLinuxSyscall.libcUsize p.namedConstants
              readUsize := fun operand => do
                match (← syscallSignatureHooks.readScalar operand).toTargetUsize memory.access.runtime.pointerSize with
                | .ok value => pure value
                | .error error => throw (ScalarOps.scalarError error)
              readPointer := fun operand => do
                match (← syscallSignatureHooks.readScalar operand).toPointer memory.access.runtime.base with
                | .ok value => pure value
                | .error error => throw (ScalarOps.scalarError error)
              readI32 := fun operand => do
                match (← syscallSignatureHooks.readScalar operand).toInt32 with
                | .ok value => pure value
                | .error error => throw (ScalarOps.scalarError error)
              writeTargetUsize := fun value destination => do
                let scalar ← match Scalar.fromUInt (BitVec.ofNat 128 value.toNat)
                    memory.access.runtime.pointerSize with
                  | .ok scalar => pure scalar
                  | .error error => throw (ScalarOps.scalarError error)
                writePlaceImmediate context.place selectedChoice (.scalar scalar)
                  ⟨.memory destination.mplace,destination.layout⟩
              writeInt := fun value destination => do
                let scalar ← match Scalar.fromInt value destination.layout.layout.size with
                  | .ok scalar => pure scalar
                  | .error error => throw (ScalarOps.scalarError error)
                writePlaceImmediate context.place selectedChoice (.scalar scalar)
                  ⟨.memory destination.mplace,destination.layout⟩
              writeScalar := fun value destination =>
                writePlaceImmediate context.place selectedChoice (.scalar value)
                  ⟨.memory destination.mplace,destination.layout⟩
              random
              event := callbacks.io.event
              unixGettid := fun name => do
                let some threadTls := assembly.threadTls |
                  throw (.unsupported "source syscall gettid lacks the Unix thread adapter")
                let scalar ← threadTls.thread.unixGettid name
                match scalar.toUInt32 with
                | .ok value => pure value
                | .error error => throw (ScalarOps.scalarError error)
              futex := fun rest destination => do
                let some sourceFutex := callbacks.futex |
                  let typeIds ← match CompilerLinuxSyscall.argumentTypes p
                      #[.u32Pointer,.i32,.u32] with
                    | .ok value => pure value
                    | .error reason => throw (.unsupported s!"compiler syscall varargs: {reason}")
                  let _ ← ShimSignatures.take syscallSignatureHooks
                    sourceLeaves.foreignSource.varArgsBudget (pure typeIds) rest
                  throw (.unsupported "source syscall futex lacks the source-built futex capability")
                let innerTakeArgs := fun types args =>
                  do
                    let typeIds ← match CompilerLinuxSyscall.argumentTypes p types with
                      | .ok value => pure value
                      | .error reason => throw (StepError.unsupported s!"compiler syscall varargs: {reason}")
                    let (values,_) ← ShimSignatures.take syscallSignatureHooks
                      sourceLeaves.foreignSource.varArgsBudget
                      (pure typeIds) args
                    pure values
                let innerLibcI32 := fun name =>
                  match CompilerLibcConstants.i32 p.namedConstants name with
                  | .ok value => pure value
                  | .error reason => throw (.unsupported s!"compiler libc {name}: {reason}")
                let sourceFutex := LinuxFutexMachine.bindForSyscall sourceFutex selectedChoice
                  innerTakeArgs innerLibcI32 sourceLeaves.hostConfiguration.hostUsizeBits
                LinuxFutex.syscall sourceFutex rest destination
              accept4 := fun operands destination => do
                let operand := fun (index : Nat) => match operands[index]? with
                  | some value => pure value
                  | none => throw (.invalidProgram "checked syscall accept4 argument missing")
                SocketDispatch.syscallAccept4 callbackSocketDispatch
                  (← operand 0) (← operand 1) (← operand 2) (← operand 3) destination }
            prctl := {
              signatures := syscallSignatureHooks
              signature := CompilerLinuxSyscall.signature p.namedAbi
              argumentTypes := fun types =>
                match CompilerLinuxSyscall.argumentTypes p types with
                | .ok value => pure value
                | .error reason => throw (.unsupported s!"compiler syscall varargs: {reason}")
              typeBudget := sourceLeaves.foreignSource.varArgsBudget
              libcI32 := fun name => match CompilerLibcConstants.i32 p.namedConstants name with
                | .ok value => pure value
                | .error reason => throw (.unsupported s!"compiler libc {name}: {reason}")
              readI32 := fun operand => do
                match (← syscallSignatureHooks.readScalar operand).toInt32 with
                | .ok value => pure value
                | .error error => throw (ScalarOps.scalarError error)
              writeScalar := fun value destination =>
                writePlaceImmediate context.place selectedChoice (.scalar value)
                  ⟨.memory destination.mplace,destination.layout⟩
              thread := assembly.threadTls.map (·.thread.thread)
              checkAccess := fun pointer size =>
                ValidityMachine.checkPointerAccess memory.access pointer size } }
          let linuxSyscallHandler : UnixForeign.OptionalHandler
              (EvalCallDispatchConstruction.State Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B Poll Instant
                System Native Profiler Raw Listener TcpStream Error) :=
            fun name abi args destination => do
              if let some result ← LinuxSyscallPartialDispatch.emulate syscallDispatch
                  name abi args destination then return some result
              assembly.dispatchers.linux name abi args destination
          let files ← match EvalUnixIoConstruction.filesFromSource p memory.access memory.pointers
              sourceLeaves.foreignSource.host.hostFiles otherFiles with
            | .ok value => pure value
            | .error error => throw error
          let fd := {seed.nativeFd.fd.file.fd with files}
          let nativeFdFile := {seed.nativeFd.fd.file with fd}
          let nativeFdDispatch := {seed.nativeFd.fd with
            file := nativeFdFile
            pollAndUnblockZero}
          let controlFd := {seed.nativeFd.control.control.fd with files}
          let control := {seed.nativeFd.control with
            control := {seed.nativeFd.control.control with fd := controlFd}}
          let vectorFd := {seed.nativeFd.vector.vector.fd with files}
          let vector := {seed.nativeFd.vector with
            vector := {seed.nativeFd.vector.vector with fd := vectorFd}}
          let fsHandler : UnixForeign.Handler
              (EvalCallDispatchConstruction.State Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B Poll Instant
                System Native Profiler Raw Listener TcpStream Error) :=
            fun name abi args destination => do
              match sourceLeaves.foreignSource.host.filesystem with
              | none => assembly.dispatchers.fs name abi args destination
              | some fsCapability => do
                let fsHost := fsCapability.effects
                let fsMemory : EvalHostRuntimeConstruction.EnvironmentMemory
                    (ValidityMachine.Control (EvalCoreMachine.Stored Os R EvalSyncObjectAccess.Payload H D
                      (SourceOther Raw Listener TcpStream Error) CpuAffinity.Mask B
                      (HostRuntime.Storage Poll Instant System H D
                        (SourceOther Raw Listener TcpStream Error) Native Profiler)))
                    C EvalSyncObjectAccess.Payload := memory
                let fsUser := EvalCoreMachine.Stored Os R EvalSyncObjectAccess.Payload H D
                  (SourceOther Raw Listener TcpStream Error) CpuAffinity.Mask B
                  (HostRuntime.Storage Poll Instant System H D
                    (SourceOther Raw Listener TcpStream Error) Native Profiler)
                let strings := EvalUnixFsConstruction.osStringsFromSource
                  sourceLeaves.foreignSource.host.os fsMemory
                let metadata ← match EvalUnixFsConstruction.metadataFromSource p
                    context.validityAccess context.projection selectedChoice strings
                    fsCapability.pathFromOs seed.errors seed.registry.readiness files
                    (fun other => do return .inl (← files.hostMetadata (.other other)))
                    fsHost assembly.foreign.os
                    sourceLeaves.foreignSource.host.unixConfig.isolatedOp with
                  | .ok hooks => pure hooks
                  | .error error => throw error
                let paths ← match EvalUnixFsConstruction.pathsFromSource
                    (U := fsUser) p
                    context.validityAccess fsMemory metadata strings fsCapability.pathFromOs
                    fsCapability.osFromPath fsHost with
                  | .ok hooks => pure hooks
                  | .error error => throw error
                let fsFd := EvalUnixFsConstruction.fdFromSource paths files
                  sourceLeaves.hostConfiguration.communicate fsHost
                let fsState := MachineHooks.State MiriMemoryKind
                  (ValidityMachine.UserState (EvalCoreMachine.Stored Os R EvalSyncObjectAccess.Payload
                    H D (EvalCallbackSocketConstruction.Other Raw Listener TcpStream Error) CpuAffinity.Mask B
                    (HostRuntime.Storage Poll Instant System H D
                      (EvalCallbackSocketConstruction.Other Raw Listener TcpStream Error) Native Profiler)))
                let times : UnixFsTimes.Hooks fsState
                    (Files.Ref (Files.Description H D (SourceOther Raw Listener TcpStream Error)))
                    D Path Meta System Error (MemoryKind MiriMemoryKind) H :=
                  EvalUnixFsConstruction.timesFromSource (U := fsUser) p
                    context.validityAccess context.projection selectedChoice fsMemory fsFd fsHost
                let directoryStore : UnixFsMachine.DirectoryStore
                    (ValidityMachine.UserState
                      (EvalCoreMachine.Stored Os R EvalSyncObjectAccess.Payload H D
                        (SourceOther Raw Listener TcpStream Error) CpuAffinity.Mask B
                        (HostRuntime.Storage Poll Instant System H D
                          (SourceOther Raw Listener TcpStream Error) Native Profiler))) R := {
                  get := fun user => user.payload.payload.user.runtime.directories
                  put := fun table user => {user with payload := {user.payload with payload :=
                    {user.payload.payload with user := {user.payload.payload.user with runtime :=
                      {user.payload.payload.user.runtime with directories := table}}}}} }
                let physicalReadiness := EvalUnixFdConstruction.readinessFromFiles
                  seed.registry.readiness files seed.readinessRoute
                let directories : UnixDirectories.Hooks fsState
                    (Files.Ref (Files.Description H D (SourceOther Raw Listener TcpStream Error)))
                    D Path Meta System Error (MemoryKind MiriMemoryKind) R fsCapability.Entry :=
                  EvalUnixFsConstruction.directoriesFromSource (U := fsUser) p context.access
                    context.projection selectedChoice fsMemory paths seed.registry.readiness
                    physicalReadiness seed.nativeFd.fd.file.fd directoryStore fsHost
                let choose := fun count => ExecutionChoices.index choiceTape .mkstemp count
                let temporary : UnixTempFile.Hooks fsState
                    (Files.Ref (Files.Description H D (SourceOther Raw Listener TcpStream Error)))
                    D Path Meta System Error (MemoryKind MiriMemoryKind) H :=
                  EvalUnixFsConstruction.temporaryFromSource (U := ValidityMachine.UserState fsUser) paths
                  seed.registry.readiness choose fsHost sourceLeaves.foreignSource.fileReferenceBudget
                let fileLockHooks : UnixFileOperations.Hooks fsState H Error := {
                  tryLock := sourceLeaves.foreignSource.host.fileLocks.tryLock
                  unlock := sourceLeaves.foreignSource.host.fileLocks.unlock
                  fromKind := sourceLeaves.foreignSource.host.ioError.hostFromKind
                  libc := fun constant => match CompilerNamedConstants.scalar
                      p.namedConstants constant with
                    | .ok scalar => pure scalar
                    | .error reason => throw (.unsupported s!"compiler libc constant {constant}: {reason}") }
                let flock := fun handle communicate operation =>
                  match handle.value with
                  | .file file .. => UnixFileOperations.flock fileLockHooks file communicate operation
                  | _ => throw (.unsupported "flock requires a file-backed descriptor")
                let readScalar := fun operand => do
                  let immediate ← ValidityMachine.readImmediate context.validityAccess operand
                  match immediate.imm.toScalar with
                  | .ok scalar => pure scalar
                  | .error error => throw (ScalarOps.immediateError error)
                let readSignedAtLayout := fun operand => do
                  let scalar ← readScalar operand
                  match scalar.toInt operand.layout.layout.size with
                  | .ok value => pure value
                  | .error error => throw (ScalarOps.scalarError error)
                let fsHooks : UnixFsDispatch.Hooks
                    (EvalCallDispatchConstruction.State Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B Poll Instant
                      System Native Profiler Raw Listener TcpStream Error)
                    (Files.Ref (Files.Description H D (SourceOther Raw Listener TcpStream Error))) D
                    Path Meta System Error (MemoryKind MiriMemoryKind) H R fsCapability.Entry := {
                  directories, times, temporary
                  expectedAbi := fun symbol _signature => CompilerNamedShimAbi.query p.namedAbi symbol
                  argumentCompat := fun caller callee =>
                    (CompilerCallConstruction.compiler p options.compatibilityBudget).checkArgumentCompat
                      selectedChoice caller callee
                  checkSymbolClash := assembly.foreign.toCore.checkSymbolClash
                  transmute := fun operand target => do
                    let projection ← context.place.projection selectedChoice
                    match operand.transmute projection target |>.mapError IntrinsicVectorMachine.projectionError with
                    | .ok value => pure value
                    | .error error => throw error
                  readSignedAtLayout
                  readI64 := fun operand => do
                    let scalar ← readScalar operand
                    match scalar.toInt64 with
                    | .ok value => pure value
                    | .error error => throw (ScalarOps.scalarError error)
                  writeScalar := fun scalar dest =>
                    writePlaceImmediate context.place selectedChoice (.scalar scalar)
                      ⟨.memory dest.mplace,dest.layout⟩
                  writeUsize := fun value dest => do
                    let scalar ← match Scalar.fromUInt (BitVec.ofNat 128 value.toNat)
                        dest.layout.layout.size with
                      | .ok scalar => pure scalar
                      | .error error => throw (ScalarOps.scalarError error)
                    writePlaceImmediate context.place selectedChoice (.scalar scalar)
                      ⟨.memory dest.mplace,dest.layout⟩
                  flock
                  communicate := sourceLeaves.hostConfiguration.communicate
                  pollAndUnblockZero }
                UnixFsDispatch.dispatch fsHooks name abi args destination
          let dispatchers := {assembly.dispatchers with
            pollAndUnblockZero
            dynamic := dynamicHandler
            affinity := affinityHandler
            fd := UnixFdDispatch.dispatch nativeFdDispatch
            fdControl := fun name abi args destination =>
              UnixFdControlDispatch.emulate control name abi args destination
            vector := fun name abi args destination =>
              UnixVectoredDispatch.emulate vector name abi args destination
            poll := pollHandler
            socket := socketHandler
            event := eventHandler
            linux := linuxSyscallHandler
            random := randomHandler
            time := timeHandler
            pthread := pthreadHandler
            solarish := solarishHandler
            freebsd := freebsdHandler
            netbsd := netbsdHandler
            macos := macosHandler}
          let dispatchers := {dispatchers with fs := fsHandler}
          let unix := fun name abi args destination => do
            match destination.ref with
            | .memory place =>
              UnixForeign.dispatchSource dispatchers unixCore name abi args ⟨place,destination.layout⟩
            | .local .. => throw (.invalidProgram "callback-aware foreign destination was not materialized")
          pure {assembly.foreign with unix}
        let dispatch := {selectedExecution.calls.dispatch with
          foreign := some callbackForeign
          foreignScope := fun action => DeadlineMachine.withPruneSuppressed
            callbackProduct.deadline.registry callbackProduct.deadline.setRegistry action}
        let calls := {selectedExecution.calls with dispatch}
        return {selectedExecution with calls}
      pure ⟨execution,panicUnwinds,context,callbackBuilder,rebindCallbacks⟩

/-- Compatibility projection for callers that need only the executable
configuration. The production startup runner uses `makeFromSourcePackage` so
it can build startup and callback adapters from the exact context paired with
that configuration. -/
def makeFromSource [DecidableEq Os]
    (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : Options)
    (sourceLeaves : SourceLeaves Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B Poll Instant System Native Profiler
      Raw Listener TcpStream Error ErrorHost Meta Path Place C ClockHost I AddrIter)
    (choice : C) : Nat → Except StepError
      (ExecutionMachine.Config MiriMemoryKind
        (SourceUser Os R EvalSyncObjectAccess.Payload H D CpuAffinity.Mask B Poll Instant System Native Profiler Raw Listener TcpStream Error)
        C (SourceOther Raw Listener TcpStream Error) ABI.ExternAbi ClockHost) :=
  fun capacity => (makeFromSourcePackage p image bytes options sourceLeaves choice capacity).map (·.execution)

/-- Source initialization consistency belongs to runner input construction,
not an additional Rust memory-operation check. Call after configuring actual
native libraries/backend and before interpreting the first MIR step. -/
def validateInitialization (leaves : Leaves Os R P H D O Aff B Host C ClockHost) :
    M Os R P H D O Aff B Host Unit :=
  NativeAllocationLifecycle.liftMachineAction (EvalPointerSource.validateMode leaves.pointerSource)

/-- Ordinary exported MIR enters the same fixed small-step interpreter. Unknown
compiler/host/backend effects and resource exhaustion remain error outcomes. -/
def step (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : Options) (leaves : Leaves Os R P H D O Aff B Host C ClockHost) (choice : C)
    (state : MachineHooks.State MiriMemoryKind (ExecutionStateTransport.Outer (EvalWorld.World Os R P H D O Aff B Host))) :
    StepResult (MachineHooks.State MiriMemoryKind (ExecutionStateTransport.Outer (EvalWorld.World Os R P H D O Aff B Host))) Bool :=
  match make p image bytes options leaves choice options.callbackCapacity with
  | .error error => (state,.error error)
  | .ok config => ExecutionStateTransport.step config options.limits choice state
/-- Public proof boundary for the canonical factory. Operational dictionaries
remain exactly those assembled by `makeWithForeignContext`. -/
theorem make_eq_context (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : Options)
    (leaves : Leaves Os R P H D O Aff B Host C ClockHost) (choice : C) (capacity : Nat) :
    make p image bytes options leaves choice capacity =
      (makeWithForeignContext (Assembly := Unit) p image bytes options leaves choice none none capacity).map Prod.fst := rfl

/-- Reveal only the pure construction-error adapter to client proofs. -/
theorem pureQuery_eq {A : Type} (value : Except String A) :
    pureQuery value = value.mapError StepError.unsupported := rfl

/-- Reveal only the universe lift used during factory construction. -/
theorem liftConstruction_eq {A : Type} (value : Except StepError A) :
    liftConstruction value = value.map (fun item => (ULift.up item : ULift.{1} A)) := by
  cases value <;> rfl

end Miri.Input.EvalConfigurationCore
