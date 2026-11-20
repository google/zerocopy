import Miri.Interpreter.Math.Dispatch
import Miri.Input.EvalAllocationMachine
import Miri.Input.EvalForeignExit
import Miri.Input.EvalConfiguration
import Miri.Input.CompilerShimAbi
import Miri.Input.CompilerBodySpan
import Miri.Input.CompilerPanicFacts
import Miri.Input.CompilerCovariance
import Miri.Interpreter.ReallocationDriver
import Miri.Interpreter.MemoryShimMachine
import Miri.Input.CompilerBacktraceSource
import Miri.Interpreter.MiriShims
import Miri.Interpreter.RandomDispatchMachine

/-! Source-owned common foreign operations. This stage has no foreign/platform
interpreter input and no allocator/read/write/control behavior supplied by the
caller. Platform and portable dispatch assembly consumes this constructed
record; it must not be substituted for a complete final foreign dictionary. -/
namespace Miri.Input.EvalForeignConstruction
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
abbrev User := EvalCoreMachine.User
abbrev State := EvalCoreMachine.State
abbrev Stored := EvalCoreMachine.Stored
abbrev M Os R P H D O Aff B Host A := MachineHooks.M MiriMemoryKind (User Os R P H D O Aff B Host) A

structure Options where
  family : ForeignItems.Family
  os : String
  arch : String
  noAllocShimSymbol : String
  compatibilityBudget : Nat
  debugAssertions : Bool

/-- Exact compiler queries which are not yet in the prepared symbol catalog.
Their outcomes are evidence obligations, not arbitrary foreign execution. -/
structure Symbols (S : Type) where
  allocatorSymbol : String → EStateM StepError S (Option (ForeignItems.AllocatorSymbol CallInstance))
  lookupFunction : String → EStateM StepError S (Option (LoadedBody × CallInstance))
  checkSymbolClash : String → EStateM StepError S Unit

/-- Genuine host FFI and OS-error effects. The native destination is known to
be memory because source force_allocation has already run. -/
structure HostEffects (S : Type) where
  nativeLibraryPaths : S → Array String
  callNative : String → MPlaceTy Provenance → Array (OpTy Provenance) → EStateM StepError S Bool
  setEnomem : EStateM StepError S Unit

/-- Constructed common source bodies, deliberately without platform/portable
execution slots. This is a source construction intermediate, not a whole
ForeignItems.Hooks baseline that an external caller may override. -/
structure Common (S : Type) where
  options : Options
  maximumSize : UInt64
  symbols : Symbols S
  native : HostEffects S
  expectedAbi : ForeignItems.Signature → EStateM StepError S (FnAbi TyId)
  argumentCompat : ArgAbi TyId → ArgAbi TyId → EStateM StepError S Bool
  forceAllocation : RuntimePlace Provenance → EStateM StepError S (RuntimePlace Provenance)
  returnToBlock : Option BasicBlockId → EStateM StepError S Unit
  unwindToBlock : UnwindAction → EStateM StepError S Unit
  transmute : OpTy Provenance → LocalLayout → EStateM StepError S (OpTy Provenance)
  readUsize : OpTy Provenance → EStateM StepError S UInt64
  readU32 : OpTy Provenance → EStateM StepError S UInt32
  readPointer : OpTy Provenance → EStateM StepError S (Pointer (Option Provenance))
  readI32 : OpTy Provenance → EStateM StepError S Int32
  allocate : UInt64 → Align → ForeignItems.Init → ForeignItems.AllocationKind → EStateM StepError S (Pointer (Option Provenance))
  deallocate : Pointer (Option Provenance) → Option (UInt64 × Align) → ForeignItems.AllocationKind → EStateM StepError S Unit
  reallocate : Pointer (Option Provenance) → Option (UInt64 × Align) → UInt64 → Align → ForeignItems.AllocationKind → EStateM StepError S (Pointer (Option Provenance))
  writePointer : Pointer (Option Provenance) → RuntimePlace Provenance → EStateM StepError S Unit
  writeNull : RuntimePlace Provenance → EStateM StepError S Unit

private def lift (result : Except StepError A) : MachineHooks.M K U A :=
  match result with | .ok value => pure value | .error error => throw error
private def query (result : Except String A) : MachineHooks.M K U A :=
  lift (result.mapError StepError.unsupported)
private def sourceKind : ForeignItems.AllocationKind → MiriMemoryKind
  | .rust => .rust | .c => .c | .miri => .miri | .mmap => .mmap

/-- init_allocation preserves the source allocation-span cut after canonical
extra initialization. Native backing/drop remain in the existing allocation
configuration; the source-point address and reuse draws happen during use. -/
private def forKind (config : PlaceMachine.AllocationConfig MiriMemoryKind (PointerMachine.User U))
    (spans : AllocationDriver.SpanHooks) (kind : MiriMemoryKind) :
    PointerMachine.M MiriMemoryKind U (PlaceMachine.AllocationConfig MiriMemoryKind (PointerMachine.User U)) := do
  let context ← get
  let tail := fun id size align => do
    config.allocationTail id size align
    if kind.shouldSaveAllocationSpan then
      let machine ← get
      let span ← match AllocationDriver.currentUserRelevantSpan spans {context with machine} with
        | .ok span state => set state.machine; pure span
        | .error error state => set state.machine; throw error
      modify fun machine => {machine with allocationSpans :=
        (machine.allocationSpans.filter (·.1 != id)).push (id,span,none)}
  pure {config with allocationTail := tail}

/-- The common interpreter is assembled from the same source allocation,
place, ABI and pointer dictionaries as MIR execution. `callFunction`
is the internal recursive edge supplied by source Config construction. -/
def common (p : CompilerProviders.Prepared) (options : Options)
    (symbols : Symbols (State Os R P H D O Aff B Host))
    (host : HostEffects (State Os R P H D O Aff B Host))
    (access : ValidityMachine.Access MiriMemoryKind (Stored Os R P H D O Aff B Host))
    (allocation : PlaceMachine.AllocationConfig MiriMemoryKind (User Os R P H D O Aff B Host))
    (extras : MemoryExtras.Hooks MiriMemoryKind (User Os R P H D O Aff B Host) P)
    (deallocationDiagnostic : AllocId → PlaceMachine.MachineM MiriMemoryKind (User Os R P H D O Aff B Host) Unit)
    (nativeDrop : Option (Allocation Provenance Miri.TreeBorrows.BorrowTree →
      MachineHooks.M MiriMemoryKind (User Os R P H D O Aff B Host) Unit))
    (pointer : PointerMachine.Hooks MiriMemoryKind (ValidityMachine.Control (Stored Os R P H D O Aff B Host)))
    (spans : AllocationDriver.SpanHooks)
    (place : PlaceHooks Provenance (State Os R P H D O Aff B Host) C MachineHooks.FrameExtra)
    (callFunction : C → CallInstance → Array (RvalueImmTy Provenance) → ReturnContinuation → M Os R P H D O Aff B Host Unit)
    (choice : C) : Except StepError (Common (State Os R P H D O Aff B Host)) := do
  let abi := p.lifecycle.shim
  let destroy := EvalAllocationMachine.deallocateWith spans pointer extras deallocationDiagnostic nativeDrop
  let readScalar := fun op => do
    let value ← ValidityMachine.readImmediate access op
    lift (value.imm.toScalar.mapError ScalarOps.immediateError)
  let readU32 := fun op => do
    lift ((← readScalar op).toUInt32.mapError ScalarOps.scalarError)
  let writeScalar := fun scalar dest => writePlaceImmediate place choice (.scalar scalar) dest
  let unwindToBlock := fun (target : UnwindAction) (state : State Os R P H D O Aff B Host) =>
    let source : State Os R P H D O Aff B Host → StepResult (State Os R P H D O Aff B Host) Unit := match target with
      | .Cleanup block => ControlFlow.goToBlock block
      | .Unreachable => fun state => (state,.error (.undefinedBehavior "unwinding past a frame that does not allow unwinding"))
      | .Continue | .Terminate _ => fun state =>
        match state.stack.currentFrame? with
        | none => (state,.error (.stack .emptyStack))
        | some frame =>
          match CompilerBodySpan.get p frame with
          | .error error => (state,.error error)
          | .ok span => ControlFlow.setLocation state (.unwinding span)
    let (state,result) := source state
    match result with
    | .error error => .error error state
    | .ok () => match target with
      | .Terminate reason => (do
        let callee ← lift (CompilerPanicFacts.unwindTerminate p.program reason)
        callFunction choice callee #[] (.goto none .Unreachable)) state
      | _ => .ok () state
  pure {
    options,maximumSize := allocation.maximumObjectSize.bytes,symbols,native := host
    expectedAbi := fun signature => query (CompilerShimAbi.expectedAbi abi signature)
    argumentCompat := (CompilerCallConstruction.compiler p options.compatibilityBudget).checkArgumentCompat choice
    forceAllocation := fun dest => do
      let memory ← Miri.Interpreter.forceAllocation place choice dest
      pure ⟨.memory memory.mplace,memory.layout⟩
    returnToBlock := fun target state =>
      let (state,result) := ControlFlow.returnToBlock target state
      match result with | .ok () => .ok () state | .error error => .error error state
    unwindToBlock
    transmute := fun operand target => do
      lift (operand.transmute (← place.projection choice) target |>.mapError IntrinsicVectorMachine.projectionError)
    readUsize := fun op => do lift ((← readScalar op).toTargetUsize pointer.arithmetic.pointerSize |>.mapError ScalarOps.scalarError)
    readU32
    readPointer := fun op => do lift ((← readScalar op).toPointer access.runtime.base |>.mapError ScalarOps.scalarError)
    readI32 := fun op => do lift ((← readScalar op).toInt32 |>.mapError ScalarOps.scalarError)
    allocate := fun size align init kind => do
      let config ← forKind allocation spans (sourceKind kind)
      let pointer ← ReallocationDriver.allocateConfigured config (Size.ofBytes size) align (.machine (sourceKind kind))
        (match init with | .zero => .Zero | .uninit => .Uninit)
      pure pointer.withOptionalProvenance
    deallocate := fun ptr old kind =>
      destroy ptr
        (old.map fun (size,align) => (Size.ofBytes size,align)) (.machine (sourceKind kind))
    reallocate := fun ptr old size align kind => do
      let config ← forKind allocation spans (sourceKind kind)
      let pointer ← ReallocationDriver.reallocateConfiguredFrom access extras pointer.arithmetic config destroy ptr
        (old.map fun (size,align) => (Size.ofBytes size,align)) (Size.ofBytes size) align (.machine (sourceKind kind)) .Uninit
      pure pointer.withOptionalProvenance
    writePointer := fun pointer dest => do
      writeScalar (← lift (Scalar.fromMaybePointer access.runtime.base pointer |>.mapError ScalarOps.scalarError)) dest
    writeNull := fun dest => do writeScalar (← lift (Scalar.fromInt 0 dest.layout.layout.size |>.mapError ScalarOps.scalarError)) dest}
/-- Project source-built primitives into the nonrecursive foreign Core. Exit
replacement reads the actual World and needs only exact source span metadata;
no whole MainMachine or platform interpreter is supplied. Native enablement is
sampled from the actual loaded library list at this construction event. -/
def core (h : Common (State Os R P H D O Aff B Host)) (spans : AllocationDriver.SpanHooks) :
    M Os R P H D O Aff B Host
      (ForeignItems.Core Provenance (State Os R P H D O Aff B Host)
        (RuntimePlace Provenance) (RuntimePlace Provenance)
        (Pointer (Option Provenance)) LoadedBody CallInstance) := do
  let nativeEnabled := !(h.native.nativeLibraryPaths (← get)).isEmpty
  pure {
    family := h.options.family
    os := h.options.os
    arch := h.options.arch
    maximumSize := h.maximumSize
    noAllocShimSymbol := h.options.noAllocShimSymbol
    allocatorSymbol := h.symbols.allocatorSymbol
    lookupFunction := h.symbols.lookupFunction
    forceAllocation := h.forceAllocation
    returnToBlock := h.returnToBlock
    unwindToBlock := h.unwindToBlock
    nativeEnabled
    callNative := fun name dest args => do
      let .memory memory := dest.ref | throw (.invalidProgram "native call destination was not materialized")
      h.native.callNative name ⟨memory,dest.layout⟩ args
    expectedAbi := h.expectedAbi
    argumentCompat := h.argumentCompat
    checkSymbolClash := h.symbols.checkSymbolClash
    transmute := h.transmute
    readUsize := h.readUsize
    readPointer := h.readPointer
    readI32 := h.readI32
    isNull := fun pointer => pure (pointer.offset.bytes == 0)
    allocate := h.allocate
    deallocate := h.deallocate
    reallocate := h.reallocate
    writePointer := h.writePointer
    writeNull := h.writeNull
    setEnomem := h.native.setEnomem
    startExit := EvalForeignExit.startInnerSource spans
    specialDestination := pure}

/-- math.rs uses sig.rs294–331's deprecated check for every exported arm.
Capture this call's actual ABI, preserving symbol-clash before ABI/count checks;
no expected ABI or scalar-layout compatibility check is added to this rule. -/
def math (h : Math.Hooks Provenance (State Os R P H D O Aff B Host) C (RuntimePlace Provenance))
    (foreign : ForeignItems.Core Provenance (State Os R P H D O Aff B Host)
      (RuntimePlace Provenance) (RuntimePlace Provenance) (Pointer (Option Provenance)) LoadedBody CallInstance)
    (choice : C) (name : String) (abi : FnAbi TyId)
    (args : Array (OpTy Provenance)) (dest : RuntimePlace Provenance) :
    M Os R P H D O Aff B Host ForeignItems.EmulateItemResult := do
  let source := {h with checkCSignature := fun _ name _ => do
    foreign.checkSymbolClash name
    if abi.conv != .C then throw (.undefinedBehavior "C math shim calling convention mismatch")
    if abi.cVariadic then throw (.undefinedBehavior "nonvariadic C math shim called c-variadic")}
  if ← Math.evalShim source choice name args dest then return .NeedsReturn
  return .NotSupported

/-- Portable memory/string operations consume only Core. Every byte access,
write, copy and alignment check is constructed from actual MIR operations;
libc::wchar_t remains an exact compiler query. -/
def memoryCore (p : CompilerProviders.Prepared)
    (access : ValidityMachine.Access MiriMemoryKind (Stored Os R P H D O Aff B Host))
    (pointer : PointerMachine.Hooks MiriMemoryKind (ValidityMachine.Control (Stored Os R P H D O Aff B Host)))
    (place : PlaceHooks Provenance (State Os R P H D O Aff B Host) C MachineHooks.FrameExtra)
    (symbolicAlignment enforceAlignment : Bool) (choice : C)
    (foreign : ForeignItems.Core Provenance (State Os R P H D O Aff B Host)
      (RuntimePlace Provenance) (RuntimePlace Provenance) (Pointer (Option Provenance)) LoadedBody CallInstance) :=
  let physical : MemoryShimMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (Stored Os R P H D O Aff B Host)) C MachineHooks.FrameExtra := {
    access,pointer,place,symbolicAlignment,enforceAlignment
    i32Layout := fun _ => query (p.primitiveLayout "i32")
    usizeLayout := fun _ => query (p.primitiveLayout "usize")
    wcharLayout := fun _ => query (CompilerPrimitiveFacts.namedLayout p.runtime "wchar_t")}
  MemoryShimMachine.core physical choice foreign

/-- Bind portable C memory/string calls to the same physical access, pointer
and place machine as MIR. Other portable names retain their existing resolver.
The memory dispatcher checks its source name table before reading operands. -/
def bindMemory (p : CompilerProviders.Prepared)
    (access : ValidityMachine.Access MiriMemoryKind (Stored Os R P H D O Aff B Host))
    (pointer : PointerMachine.Hooks MiriMemoryKind (ValidityMachine.Control (Stored Os R P H D O Aff B Host)))
    (place : PlaceHooks Provenance (State Os R P H D O Aff B Host) C MachineHooks.FrameExtra)
    (symbolicAlignment enforceAlignment : Bool) (choice : C) (stringBudget : Nat)
    (foreign : ForeignItems.Hooks Provenance (State Os R P H D O Aff B Host)
      (RuntimePlace Provenance) (RuntimePlace Provenance)
      (Pointer (Option Provenance)) LoadedBody CallInstance) :
    ForeignItems.Hooks Provenance (State Os R P H D O Aff B Host)
      (RuntimePlace Provenance) (RuntimePlace Provenance)
      (Pointer (Option Provenance)) LoadedBody CallInstance :=
  let memory := memoryCore p access pointer place symbolicAlignment enforceAlignment choice foreign.toCore
  {foreign with otherPortable := fun name abi args destination => do
    if let some result ← MemoryShims.Source.emulate memory stringBudget name abi args destination then
      return some result
    foreign.otherPortable name abi args destination}

/-- Construct the connected Unix entropy family from Common source effects.
ForeignItems uses a typed RuntimePlace, while the Unix shim ABI writes through
an allocated MPlaceTy. The adapter below materializes only at the source
force-allocation boundary and routes every write back through Common's actual
place operations. Isolated bytes use EvalCoreMachine's tape; communicate mode
requires the caller's real host getrandom effect. The signature and errno
providers are the pinned compiler and Unix environment queries respectively. -/
def unixRandom (h : Common (State Os R P H D O Aff B Host))
    (spans : AllocationDriver.SpanHooks)
    (access : PlaceMachine.AccessConfig MiriMemoryKind (User Os R P H D O Aff B Host))
    (tape : ExecutionChoices.Access (State Os R P H D O Aff B Host))
    (place : PlaceHooks Provenance (State Os R P H D O Aff B Host) C MachineHooks.FrameExtra)
    (choice : C) (communicate : Bool) (hostUsizeBits : Nat)
    (hostFill : Nat → M Os R P H D O Aff B Host (Except String ByteArray))
    (signature : String → M Os R P H D O Aff B Host (FnAbi TyId))
    (errnoNegOne : String → MPlaceTy Provenance →
      M Os R P H D O Aff B Host Unit) :
    M Os R P H D O Aff B Host
      (String → FnAbi TyId → Array (OpTy Provenance) → RuntimePlace Provenance →
        M Os R P H D O Aff B Host ForeignItems.EmulateItemResult) := do
  let base ← core h spans
  unless base.family == .unix do throw (.invalidProgram "Unix random constructor requires Unix target")
  let toRuntime (dest : MPlaceTy Provenance) : RuntimePlace Provenance :=
    ⟨.memory dest.mplace, dest.layout⟩
  let toMemory (dest : RuntimePlace Provenance) :
      M Os R P H D O Aff B Host (MPlaceTy Provenance) := do
    match dest.ref with
    | .memory memory => return ⟨memory,dest.layout⟩
    | .local .. => throw (.invalidProgram "Unix foreign destination was not materialized")
  let randomForeign : ForeignItems.Core Provenance
      (State Os R P H D O Aff B Host) (RuntimePlace Provenance) (MPlaceTy Provenance)
      (Pointer (Option Provenance)) LoadedBody CallInstance := {
    family := base.family
    os := base.os
    arch := base.arch
    maximumSize := base.maximumSize
    noAllocShimSymbol := base.noAllocShimSymbol
    allocatorSymbol := base.allocatorSymbol
    lookupFunction := base.lookupFunction
    forceAllocation := fun dest => do toMemory (← base.forceAllocation dest)
    returnToBlock := base.returnToBlock
    unwindToBlock := base.unwindToBlock
    nativeEnabled := base.nativeEnabled
    callNative := fun name dest args => base.callNative name (toRuntime dest) args
    expectedAbi := base.expectedAbi
    argumentCompat := base.argumentCompat
    checkSymbolClash := base.checkSymbolClash
    transmute := base.transmute
    readUsize := base.readUsize
    readPointer := base.readPointer
    readI32 := base.readI32
    isNull := base.isNull
    allocate := base.allocate
    deallocate := base.deallocate
    reallocate := base.reallocate
    writePointer := fun pointer dest => base.writePointer pointer (toRuntime dest)
    writeNull := fun dest => base.writeNull (toRuntime dest)
    setEnomem := base.setEnomem
    startExit := base.startExit
    specialDestination := fun dest => do toMemory (← base.forceAllocation dest)
  }
  let random := RandomMemory.machine access tape communicate hostUsizeBits hostFill
  let source := UnixRandomDispatch.sourceHooks randomForeign random signature errnoNegOne
    (fun value dest => do
      let scalar ← lift (Scalar.fromUInt (BitVec.ofNat 128 value.toNat)
        access.runtime.pointerOffset |>.mapError ScalarOps.scalarError)
      writePlaceImmediate place choice (.scalar scalar) (toRuntime dest))
  let machine := RandomDispatchMachine.unix access tape place choice source
  return fun name abi args dest => do
    let dest ← toMemory dest
    match ← UnixRandomDispatch.emulate machine name abi args dest with
    | some result => return result
    | none => return .NotSupported

/-- Construct the Windows entropy family through the same Common runtime
place materialization and canonical memory access as ordinary MIR. The host
random fill and exact named `System` ABI are required effects; isolated bytes
consume the shared source-choice tape. -/
def windowsRandom (h : Common (State Os R P H D O Aff B Host))
    (spans : AllocationDriver.SpanHooks)
    (access : PlaceMachine.AccessConfig MiriMemoryKind (User Os R P H D O Aff B Host))
    (tape : ExecutionChoices.Access (State Os R P H D O Aff B Host))
    (place : PlaceHooks Provenance (State Os R P H D O Aff B Host) C MachineHooks.FrameExtra)
    (choice : C) (communicate : Bool) (hostUsizeBits : Nat)
    (hostFill : Nat → M Os R P H D O Aff B Host (Except String ByteArray))
    (signature : String → M Os R P H D O Aff B Host (FnAbi TyId)) :
    M Os R P H D O Aff B Host
      (String → FnAbi TyId → Array (OpTy Provenance) → RuntimePlace Provenance →
        M Os R P H D O Aff B Host ForeignItems.EmulateItemResult) := do
  let base ← core h spans
  unless base.family == .windows do throw (.invalidProgram "Windows random constructor requires Windows target")
  let toRuntime (dest : MPlaceTy Provenance) : RuntimePlace Provenance :=
    ⟨.memory dest.mplace, dest.layout⟩
  let toMemory (dest : RuntimePlace Provenance) :
      M Os R P H D O Aff B Host (MPlaceTy Provenance) := do
    match dest.ref with
    | .memory memory => return ⟨memory,dest.layout⟩
    | .local .. => throw (.invalidProgram "Windows foreign destination was not materialized")
  let randomForeign : ForeignItems.Core Provenance
      (State Os R P H D O Aff B Host) (RuntimePlace Provenance) (MPlaceTy Provenance)
      (Pointer (Option Provenance)) LoadedBody CallInstance := {
    family := base.family
    os := base.os
    arch := base.arch
    maximumSize := base.maximumSize
    noAllocShimSymbol := base.noAllocShimSymbol
    allocatorSymbol := base.allocatorSymbol
    lookupFunction := base.lookupFunction
    forceAllocation := fun dest => do toMemory (← base.forceAllocation dest)
    returnToBlock := base.returnToBlock
    unwindToBlock := base.unwindToBlock
    nativeEnabled := base.nativeEnabled
    callNative := fun name dest args => base.callNative name (toRuntime dest) args
    expectedAbi := base.expectedAbi
    argumentCompat := base.argumentCompat
    checkSymbolClash := base.checkSymbolClash
    transmute := base.transmute
    readUsize := base.readUsize
    readPointer := base.readPointer
    readI32 := base.readI32
    isNull := base.isNull
    allocate := base.allocate
    deallocate := base.deallocate
    reallocate := base.reallocate
    writePointer := fun pointer dest => base.writePointer pointer (toRuntime dest)
    writeNull := fun dest => base.writeNull (toRuntime dest)
    setEnomem := base.setEnomem
    startExit := base.startExit
    specialDestination := fun dest => do toMemory (← base.forceAllocation dest)
  }
  let random := RandomMemory.machine access tape communicate hostUsizeBits hostFill
  let outputScalar := fun scalar dest =>
    writePlaceImmediate place choice (.scalar scalar) (toRuntime dest)
  let outputInt := fun value dest => do
    let scalar ← lift (Scalar.fromInt value dest.layout.layout.size |>.mapError ScalarOps.scalarError)
    writePlaceImmediate place choice (.scalar scalar) (toRuntime dest)
  let source := WindowsRandomDispatch.sourceHooks randomForeign random signature h.readU32
    outputScalar outputInt
  let machine := RandomDispatchMachine.windows access tape place choice source
  return fun name abi args dest => do
    let dest ← toMemory dest
    match ← WindowsRandomDispatch.emulate machine name abi args dest with
    | some result => return result
    | none => return .NotSupported

/-- Source portable-extern order from shims/foreign_items.rs: Miri-specific,
backtrace, then C memory/string arms. These three
families all consume the same nonrecursive Core, so a portable shim observes
the canonical state and ABI/pointer checks made by common construction. The
compiler repr(C) query is kept lazy until miri_resolve_frame is selected. -/
def portableOther
    (foreign : ForeignItems.Core Provenance (State Os R P H D O Aff B Host)
      (RuntimePlace Provenance) (RuntimePlace Provenance)
      (Pointer (Option Provenance)) LoadedBody CallInstance)
    (memory : MemoryShims.CoreHooks Provenance (State Os R P H D O Aff B Host)
      (RuntimePlace Provenance) (RuntimePlace Provenance) LoadedBody CallInstance)
    (stringBudget : Nat)
    (miri : MiriShims.CoreHooks Provenance (State Os R P H D O Aff B Host)
      (RuntimePlace Provenance) (RuntimePlace Provenance) LoadedBody CallInstance HostPath)
    (backtrace : Backtrace.CoreHooks Provenance (State Os R P H D O Aff B Host)
      (RuntimePlace Provenance) (RuntimePlace Provenance) LoadedBody CallInstance
      MachineHooks.FrameExtra CompilerBacktraceSource.Position)
    (adtReprC : TyId → M Os R P H D O Aff B Host (Option Bool)) :
    String → FnAbi TyId → Array (OpTy Provenance) → RuntimePlace Provenance →
      M Os R P H D O Aff B Host (Option ForeignItems.EmulateItemResult) :=
  fun name abi args dest => do
    let miri := {miri with foreign := foreign}
    if let some result ← MiriShims.Source.emulate miri name abi args dest then
      return some result
    let backtrace := {backtrace with foreign := foreign}
    if let some result ← Backtrace.Source.emulate backtrace adtReprC name abi args dest then
      return some result
    let memory := {memory with foreign := foreign}
    MemoryShims.Source.emulate memory stringBudget name abi args dest

/-- Close the source dispatcher only after each source family has been
constructed. The platform functions are required values (not a copied baseline
Hook record); callers must pass the actual Unix or Windows source dispatcher
and exact math source. -/
def assemble
    (foreign : ForeignItems.Core Provenance (State Os R P H D O Aff B Host)
      (RuntimePlace Provenance) (RuntimePlace Provenance)
      (Pointer (Option Provenance)) LoadedBody CallInstance)
    (math : String → FnAbi TyId → Array (OpTy Provenance) → RuntimePlace Provenance →
      M Os R P H D O Aff B Host ForeignItems.EmulateItemResult)
    (unix : String → FnAbi TyId → Array (OpTy Provenance) → RuntimePlace Provenance →
      M Os R P H D O Aff B Host ForeignItems.EmulateItemResult)
    (windows : String → FnAbi TyId → Array (OpTy Provenance) → RuntimePlace Provenance →
      M Os R P H D O Aff B Host ForeignItems.EmulateItemResult)
    (otherPortable : String → FnAbi TyId → Array (OpTy Provenance) → RuntimePlace Provenance →
      M Os R P H D O Aff B Host (Option ForeignItems.EmulateItemResult)) :
    ForeignItems.Hooks Provenance (State Os R P H D O Aff B Host)
      (RuntimePlace Provenance) (RuntimePlace Provenance)
      (Pointer (Option Provenance)) LoadedBody CallInstance :=
  { toCore := foreign, math, unix, windows, otherPortable }

end Miri.Input.EvalForeignConstruction
