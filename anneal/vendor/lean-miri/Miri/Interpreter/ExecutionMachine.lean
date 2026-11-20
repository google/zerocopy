import Miri.Interpreter.ExecutionCalls
import Miri.Interpreter.ExecutionControl
import Miri.Interpreter.ExecutionCast
import Miri.Interpreter.ExecutionScalar
import Miri.Interpreter.ExecutionLeaves
import Miri.Interpreter.IntrinsicBackend
import Miri.Interpreter.RawMemoryMachine
import Miri.Interpreter.ValidityMemory
import Miri.Interpreter.OperandMachine
import Miri.Interpreter.CallMachine
import Miri.Interpreter.Aggregate
import Miri.Interpreter.Discriminant
import Miri.Interpreter.FloatOps
import Miri.Interpreter.GlobalMemoryCopyMachine
import Miri.Interpreter.Intrinsics
import Miri.Interpreter.Panic
import Miri.Interpreter.FunctionPointerConsumers
import Miri.Interpreter.TerminatorMachine

/-! One canonical MIR small-step assembly. Records below supply compiler/host
queries and platform dispatch; core operations are replaced by source drivers.
Resource limits govern concrete execution only, not the permitted MIR relation. -/
namespace Miri.Interpreter.ExecutionMachine
open Miri.ABI Miri.Memory Miri.MIR
open MachineHooks (M State FrameExtra)
abbrev Value := RuntimePlace Provenance
abbrev Calls K U C O X := CallHooks Provenance (State K U) C FrameExtra O X (FnAbi TyId) (ArgAbi TyId)
structure Limits where
  callDispatch : Nat
  casts : Nat
  retag : Nat
  validation : Nat
structure Config (K User C Other Extern Host : Type) where
  access : PlaceMachine.AccessConfig K User
  allocation : PlaceMachine.AllocationConfig K User
  compiler : PlaceMachine.CompilerHooks K User C
  projection : PlaceProjectionHooks Provenance (State K User) C FrameExtra
  operands : ExecutionLeaves.Operand (State K User) C
  copy : PlaceCopyHooks Provenance (State K User) C
  retag : TypedRetag.Hooks K User
  validity : ValidityVisitor.Hooks Provenance (State K User) C FrameExtra
    (FnVal Other) (FnAbi TyId) ValidityMemory.PaddingHandle
  validationRecursive : C → LocalLayout → M K User Bool
  lifecycle : CallMachine.Lifecycle K User C
  functions : FunctionPointers.Hooks K User Other
  calls : ExecutionCallLeaves.Hooks (State K User) C Other Extern
  virtual : ExecutionCallLeaves.Virtual K User C
  helpers : ExecutionCallLeaves.Helpers (State K User) C Extern
  control : ExecutionLeaves.Control Provenance LocalLayout FrameExtra
  panic : Panic.Hooks K User C Other
  unwindTerminateFunction : C → UnwindTerminateReason → M K User CallInstance
  ignoreOptionalOverflowChecks : Bool
  rvalues : ExecutionLeaves.Rvalue (State K User) C
  discriminant : ExecutionLeaves.Discriminant (State K User) C
  scalar : ExecutionScalar.Leaves (State K User) C
  floats : FloatOpsHooks Provenance (State K User) C
  casts : ExecutionCast.Leaves (State K User) C
  backend : IntrinsicBackend.Dispatcher (State K User) C Value
  atomics : AtomicAccessHooks Provenance (State K User) C Value
  varArgs : IntrinsicVarArgsHooks Provenance (State K User) C Value
  intrinsics : CallInstance → IntrinsicHooks Provenance (State K User) C Value
  intrinsicName : CallInstance → M K User String
  intrinsicMustOverride : CallInstance → M K User Bool
  intrinsicFallbackIsSpec : CallInstance → M K User Bool
  addresses : User → AllocAddresses.GlobalAddressState
  arithmetic : PointerArithmetic
  isRawPointer : C → TyId → M K User Bool
  usizeLayout : C → M K User LocalLayout
  pointeeLayout : C → TyId → M K User LocalLayout
  terminators : TerminatorMachine.Hooks K User Host
  preemptionChoice : C → M K User Bool

private def lift (result : Except StepError A) : M K U A :=
  match result with | .ok value => pure value | .error error => throw error
private def scalar (value : RvalueImmTy Provenance) : M K U (Scalar Provenance) :=
  lift (value.imm.toScalar.mapError ScalarOps.immediateError)
private def machineAction (action : PlaceMachine.MachineM K U A) : M K U A := fun state =>
  match action state.machine with
  | .ok value machine => .ok value {state with machine}
  | .error error machine => .error error {state with machine}
private def pointerOf (place : Value) : Except StepError (Pointer (Option Provenance)) :=
  match place.ref with
  | .memory place => .ok place.ptr
  | .local .. => .error (.invalidProgram "allocated memory place required")

def scalarHooks (h : Config K U C O X Host) : ScalarOpsHooks Provenance (State K U) C :=
  ExecutionScalar.hooks h.scalar h.access h.arithmetic h.isRawPointer h.usizeLayout h.pointeeLayout
    h.operands.dereference h.floats

/-- Close raw reads, dynamically sized physical copies, and validation with
actual source implementations before constructing any expression dictionary. -/
def withValidation [DecidableEq K] (h : Config K U C O X Host) (limits : Limits) : Config K U C O X Host :=
  let retag := h.retag
  let copy := {h.copy with
    readRaw := fun _ => PlaceMachine.readRaw h.access
    memoryCopy := GlobalMemoryCopyMachine.typedCopy h.access h.addresses h.arithmetic
      h.projection.dynamic h.projection.dynamicFuel h.compiler.debugAssertions}
  let (compiler,copy) := TypedMachineBindings.bindValidation h.compiler copy h.validity retag
    limits.retag limits.validation h.validationRecursive
  {h with compiler,copy,retag}

private def operandBase (h : Config K U C O X Host) : OperandMachine.Hooks K U C where
  compiler := h.compiler
  projection := h.projection
  layoutCompatible := h.copy.compatible
  checkPlaceType := h.operands.checkPlaceType
  dereference := h.operands.dereference
  runtimeChecks := h.operands.runtimeChecks
  boolLayout := h.operands.boolLayout
  constant := fun _ _ _ => throw (.unsupported "constant operand requires an exact structural source site")
  constantAt := h.operands.constantAt

def projectionHooks [DecidableEq K] (h : Config K U C O X Host) :
    PlaceProjectionHooks Provenance (State K U) C FrameExtra :=
  -- The source-owned projection contains the live ghost-mode read/write
  -- scopes. Reconstructing a generic PlaceHooks here would erase them.
  {h.projection with target := h.access.runtime.base}

/-- Projection/place/operand dictionaries share actual frame-local clocks,
canonical layouts and source typed dereference; no read forces allocation. -/
def operandHooks [DecidableEq K] (h : Config K U C O X Host) : OperandMachine.Hooks K U C :=
  {operandBase h with
    projection := projectionHooks h
    checkPlaceType := fun c place value => do
      if h.compiler.debugAssertions then h.operands.checkPlaceType c place value}

private def mutableAccess [DecidableEq K] (h : Config K U C O X Host) (c : C) (dest : Value) : M K U Unit := do
  let .memory memory := dest.ref | throw (.invalidProgram "repeat mutable access requires memory")
  let layout ← DynamicLayout.sizeAndAlignFromMeta h.projection.dynamic c h.projection.dynamicFuel memory.metadata dest.layout
  let (size,align) := layout.getD (dest.layout.layout.size,dest.layout.layout.align.abi)
  let view : MemoryOperandPlace Provenance := ⟨memory,⟨size,align,.Memory (sized := true),some dest.layout.ty⟩⟩
  let state ← get
  let result := getPlaceAllocMut state.machine.memory ⟨state.machine,none⟩ view h.access.runtime h.access.ghostMode
    h.access.globalKind h.access.globalHooks (PlaceMachine.accessHooks h.access) h.access.dynamicLayout
  set {state with machine := h.access.retainTouched {result.hooks.machine with memory := result.memory} result.touched}
  match result.outcome with
  | .ok _ => pure ()
  | .error error => throw (result.hooks.pendingError.getD (h.access.memoryError error))

def discriminantHooks [DecidableEq K] (h : Config K U C O X Host) :
    DiscriminantHooks Provenance (State K U) C Value :=
  let place := (projectionHooks h).place
  {
    discriminantLayout := h.discriminant.discriminantLayout
    tagLayout := h.discriminant.tagLayout
    discriminantValue := h.discriminant.discriminantValue
    variantForDiscriminant := h.discriminant.variantForDiscriminant
    adtVariantCount := h.discriminant.adtVariantCount
    scalarMayBeNull := h.discriminant.scalarMayBeNull
    runtimeTarget := h.access.runtime
    projectRead := OperandMachine.field (operandHooks h)
    readImmediate := fun _ => PlaceMachine.readImmediate h.access
    destLayout := RuntimePlace.layout
    projectWrite := PlaceDynamic.field (projectionHooks h)
    writeScalar := fun c value dest => writePlaceImmediate place c (.scalar value) dest
    toOp := placeToOp place}

def castHooks [DecidableEq K] (h : Config K U C O X Host) (limits : Limits) :
    CastHooks Provenance (State K U) C Value :=
  ExecutionCast.hooks h.casts h.access h.allocation h.compiler (projectionHooks h) h.copy
    h.retag h.validity h.functions h.floats h.operands.dereference
    (OperandMachine.field (operandHooks h)) h.validationRecursive limits.retag limits.validation

/-- Core expression dictionaries. Genuine compiler type/layout predicates and
host/platform leaves in base records survive; operational actions are replaced. -/
def rvalueHooks [DecidableEq K] (h : Config K U C O X Host) (limits : Limits) :
    RvalueHooks Provenance (State K U) C Value :=
  let h := withValidation h limits
  let place := (projectionHooks h).place
  let operands := operandHooks h
  let eval := OperandMachine.evalOperand operands
  let evaluate := PlaceDynamic.evalPlace (projectionHooks h)
  let discr := discriminantHooks h
  let aggregate : AggregateHooks Provenance (State K U) C Value := {
    target := h.access.runtime.base
    placeLayout := RuntimePlace.layout
    evalOperand := eval
    evalOperandAt := OperandMachine.evalOperandAt operands
    readPointer := fun _ op => do lift ((← scalar (← PlaceMachine.readImmediate h.access op)).toPointer h.access.runtime.base |>.mapError ScalarOps.scalarError)
    readScalar := fun _ op => do scalar (← PlaceMachine.readImmediate h.access op)
    projectDowncast := PlaceDynamic.downcast (projectionHooks h)
    projectField := PlaceDynamic.field (projectionHooks h)
    copyOp := fun c op dest => copyRuntimePlace place h.copy c op dest false
    copyOpNoValidate := copyRuntimePlaceNoValidate place h.copy
    writeDiscriminant := Discriminant.writeDiscriminant discr
    enforceValidity := h.compiler.enforceValidity
    validate := h.compiler.validate
    forceAllocation := fun c dest => do
      let allocated ← forceAllocation place c dest
      return ⟨.memory allocated.mplace,allocated.layout⟩
    length := PlaceDynamic.length (projectionHooks h)
    getPlaceAllocMut := mutableAccess h
    projectIndex := PlaceDynamic.index (projectionHooks h)
    placePointer := pointerOf
    wrappingOffset := aggregateWrappingOffset h.arithmetic
    memCopyRepeatedly := fun _ => GlobalMemoryCopyMachine.genericCopy h.access h.addresses h.arithmetic}
  let casts := castHooks h limits
  let retag := h.retag
  {
    placeLayout := RuntimePlace.layout
    evalPlace := evaluate
    readImmediate := fun _ => PlaceMachine.readImmediate h.access
    writeImmediate := writePlaceImmediate place
    writePointer := fun c pointer dest => do
      let value ← lift (Scalar.fromMaybePointer h.access.runtime.base pointer |>.mapError
        fun error => .invalidProgram s!"pointer immediate: {reprStr error}")
      writePlaceImmediate place c (.scalar value) dest
    threadLocalPointer := h.rvalues.threadLocalPointer
    normalize := h.rvalues.normalize
    withRetagMode := fun _ mode body => MachineHooks.withRetagMode mode body
    copyOp := fun c source dest => copyRuntimePlace place h.copy c source dest false
    copyOpAllowTransmute := fun c source dest => copyRuntimePlace place h.copy c source dest true
    forceAllocation := fun c dest => return (← forceAllocation place c dest).mplace
    toRef := fun _ memory => lift (memory.toRef h.access.runtime.base |>.mapError
      fun error => .invalidProgram s!"place reference: {reprStr error}")
    enforceValidity := h.compiler.enforceValidity
    retagPtrValue := fun _ value ty => TypedRetag.machineRetagPtrValue retag limits.retag value ty
    placeBaseRaw := fun c mirPlace => do
      if mirPlace.projection[0]? == some .Deref then
        let frame ← MachineHooks.currentFrame
        let some ty := frame.body.locals[mirPlace.localId]?
          | throw (.invalidProgram "raw place base local missing")
        h.isRawPointer c ty
      else pure false
    evalOperand := eval
    evalOperandAt := OperandMachine.evalOperandAt operands
    evalPlaceToOp := OperandMachine.evalPlaceToOp operands
    binaryOp := ScalarOps.binary (scalarHooks h)
    unaryOp := ScalarOps.unary (scalarHooks h)
    writeAggregate := writeAggregate aggregate
    writeRepeat := writeRepeat aggregate
    cast := fun c op kind ty dest => Cast.cast casts c limits.casts op kind ty dest
    readDiscriminant := Discriminant.readDiscriminant discr
    discriminantForVariant := Discriminant.discriminantForVariant discr}

private def intrinsicHooks [DecidableEq K] (h : Config K U C O X Host) (limits : Limits)
    (context : IntrinsicHooks Provenance (State K U) C Value) :
    IntrinsicHooks Provenance (State K U) C Value :=
  let place := (projectionHooks h).place
  let eval := OperandMachine.evalOperand (operandHooks h)
  {context with
    target := h.access.runtime.base
    pointerOffset := h.access.runtime.pointerOffset
    destLayout := RuntimePlace.layout
    placePointer := pointerOf
    dynamicSizeAlign := fun c => DynamicLayout.sizeAndAlignOfVal h.projection.dynamic c h.projection.dynamicFuel
    vtableSizeAlign := h.projection.dynamic.vtableSizeAndAlign
    readDiscriminant := Discriminant.readDiscriminant (discriminantHooks h)
    floatOps := h.floats
    derefPointer := fun c operand => do
      let memory ← h.operands.dereference c operand
      return ⟨.memory memory.mplace,memory.layout⟩
    allocateStack := fun _ layout => do
      let memory ← PlaceMachine.allocateStack h.allocation layout
      return ⟨.memory memory.mplace,memory.layout⟩
    deallocateStack := fun _ => h.lifecycle.storage.deallocateStack
    enforceValidity := h.compiler.enforceValidity
    enforceValidityRecursively := h.validationRecursive
    validatePlace := fun c dest recursive reset =>
      ValidityVisitor.validatePlace (TypedMachineBindings.bindValidity h.validity h.retag limits.retag)
        c limits.validation dest recursive reset
    writeBytes := fun _ pointer value size => RawMemoryMachine.writeRepeatedByte h.access h.arithmetic pointer value size.bytes
    readBytesStripProvenance := fun _ pointer size => do
      return (← RawMemoryMachine.readBytes h.access h.arithmetic pointer size.bytes).data
    evalOperand := fun c op => eval c op none
    evalOperandAt := fun c path op => OperandMachine.evalOperandAt (operandHooks h) c path op none
    scalarOps := scalarHooks h
    readImmediate := fun _ => PlaceMachine.readImmediate h.access
    writeImmediate := writePlaceImmediate place
    writePointer := fun c pointer dest => do
      let scalar ← lift (Scalar.fromMaybePointer h.access.runtime.base pointer |>.mapError ScalarOps.scalarError)
      writePlaceImmediate place c (.scalar scalar) dest
    copyOp := fun c source dest => copyRuntimePlace place h.copy c source dest false
    placeToOp := placeToOp place
    memCopy := fun _ source dest size nonoverlap =>
      GlobalMemoryCopyMachine.genericCopy h.access h.addresses h.arithmetic source dest size 1 nonoverlap
    returnToBlock := fun _ target state =>
      let (state,result) := ControlFlow.returnToBlock target state
      match result with | .ok value => .ok value state | .error error => .error error state}

/-- Core call expression/terminator adapters share the actual lifecycle and
source intrinsic fallback policy, retaining platform/foreign dispatch leaves. -/
def callHooks [DecidableEq K] (h : Config K U C O X Host) (limits : Limits) : Calls K U C O X :=
  let h := withValidation h limits
  let operands := operandHooks h
  let intrinsic : C → CallInstance → Array (OpTy Provenance) → RuntimeStackPlace Provenance →
      Option BasicBlockId → UnwindAction → M K U (Option CallInstance) := fun c callee args dest ret _ => do
    let name ← h.intrinsicName callee
    let types := callee.args.filterMap fun arg => match arg with | .Type ty => some ty | _ => none
    let context := h.intrinsics callee
    if ← IntrinsicBackend.eval h.backend (intrinsicHooks h limits context) c name types args dest.toRuntimePlace ret then return none
    if ← h.intrinsicMustOverride callee then throw (.unsupported s!"unimplemented intrinsic: {name}")
    unless ← h.intrinsicFallbackIsSpec callee do throw (.unsupported s!"intrinsic fallback is not a specification: {name}")
    return some ⟨.Item callee.defId,callee.args⟩
  let virtual := ExecutionCalls.virtualHooks h.virtual h.access operands h.compiler.debugAssertions
  ExecutionCalls.make h.calls h.lifecycle h.access h.allocation h.compiler h.copy h.retag
    limits.retag limits.callDispatch operands (projectionHooks h) h.functions virtual
    h.varArgs h.arithmetic intrinsic

/-- The same existing small-step Step.step executes the assembled hooks. -/
def stepHooks [DecidableEq K] (h : Config K U C O X Host) (limits : Limits) :
    StepHooks Provenance LocalLayout FrameExtra (MachineHooks.MachineState K U) C Value :=
  let h := withValidation h limits
  let operands := operandHooks h
  let eval := fun c op => OperandMachine.evalOperand operands c op none
  let read := fun c path op => do
    PlaceMachine.readImmediate h.access (← OperandMachine.evalOperandAt operands c path op none)
  let calls := callHooks h limits
  let helpers := ExecutionCalls.helpers h.helpers calls
  let panic := {h.panic with
    evalOperand := eval
    evalOperandAt := fun c path op => OperandMachine.evalOperandAt operands c path op none
    driver := FunctionCalls.bindUnwind h.panic.driver helpers}
  let control := ExecutionControl.hooks h.control.bodySpan h.lifecycle h.access
    (projectionHooks h).place h.copy h.retag helpers h.unwindTerminateFunction
  let discr := discriminantHooks h
  let terminators : TerminatorHooks Provenance LocalLayout FrameExtra (MachineHooks.MachineState K U)
      C (OpTy Provenance) (RvalueImmTy Provenance) := {
    toControlHooks := control
    evalDiscriminant := fun c op => MachineHooks.run (read c (OperandPath.instruction "discriminant") op)
    compareSwitchCase := fun c value bits => MachineHooks.run do
      let caseScalar ← lift (Scalar.fromUInt (BitVec.ofNat 128 bits) value.layout.layout.size |>.mapError ScalarOps.scalarError)
      let result ← ScalarOps.binary (scalarHooks h) c .Eq value ⟨.scalar caseScalar,value.layout⟩
      lift ((← scalar result).toBool.mapError ScalarOps.scalarError)
    call := fun c terminator => MachineHooks.run (Call.evalCallTerminator calls c limits.callDispatch terminator)
    tailCall := fun c terminator => MachineHooks.run (Call.evalTailCallTerminator calls c limits.callDispatch terminator)
    drop := fun c mirPlace target unwind => MachineHooks.run do
      let dest ← PlaceDynamic.evalPlace (projectionHooks h) c mirPlace false
      let callee ← calls.resolveDropGlue c dest.layout.ty
      match callee.kind with
      | .Shim (.DropGlue _ none) =>
        let state ← get
        let (state,outcome) := ControlFlow.goToBlock target state
        set state
        lift outcome
      | _ => Call.initDropInPlaceCall calls c limits.callDispatch dest.stackView callee target unwind
    ignoreOptionalOverflowChecks := fun _ => h.ignoreOptionalOverflowChecks
    readAssertCondition := fun c op => MachineHooks.run do lift ((← scalar (← read c (OperandPath.instruction "condition") op)).toBool.mapError ScalarOps.scalarError)
    assertPanic := fun c message unwind => MachineHooks.run (Panic.assertPanic panic c message unwind) }
  {
    assign := fun c dest value => MachineHooks.run (evalRvalueIntoPlace (rvalueHooks h limits) c value dest)
    evalPlace := fun c dest skip => MachineHooks.run (PlaceDynamic.evalPlace (projectionHooks h) c dest skip)
    writeDiscriminant := fun c variant dest => MachineHooks.run (Discriminant.writeDiscriminant discr c variant dest)
    storageLive := fun _ id => MachineHooks.run (MachineHooks.storageLiveDyn h.lifecycle.storage id .none)
    storageDead := fun _ id => MachineHooks.run (MachineHooks.storageDead h.lifecycle.storage id)
    intrinsic := fun c intrinsic => MachineHooks.run (Intrinsics.evalNondivergingWith {
      target := h.access.runtime.base
      maxSizeOfVal := h.projection.maxSizeOfVal
      layoutOf := h.casts.layoutOf
      pointeeType := fun c ty => do
        let some pointee ← h.casts.builtinDeref c ty true
          | throw (.invalidProgram "copy intrinsic requires a pointer type")
        pure pointee
      readImmediate := fun _ => PlaceMachine.readImmediate h.access
      checkAlign := h.atomics.checkPointerAlign
      memCopy := fun _ source dest size nonoverlap =>
        GlobalMemoryCopyMachine.genericCopy h.access h.addresses h.arithmetic source dest size 1 nonoverlap}
      (fun c path op => OperandMachine.evalOperandAt operands c path op none) c intrinsic)
    -- Pinned Miri inherits rustc's empty counter hook.
    incrementConstEvalCounter := fun _ state => (state,.ok ())
    returnFromCurrentFrame := ControlFlow.returnFromCurrentFrame control
    beforeTerminator := fun c => MachineHooks.run (TerminatorMachine.beforeTerminatorWithChoice h.terminators (h.preemptionChoice c))
    terminator := ControlFlow.evalTerminator terminators }

def step [DecidableEq K] (h : Config K U C O X Host) (limits : Limits) (c : C) (state : State K U) :
    StepResult (State K U) Bool := Step.step (stepHooks h limits) c state

/-- Quantify runner resources as well as source choices. A bounded successful
run alone establishes no unrestricted UB-freedom claim. -/
def AllowedStep [DecidableEq K] (h : Config K U C O X Host) (allowed : State K U → C → Prop)
    (before after : State K U) (outcome : Except StepError Bool) : Prop :=
  ∃ limits choice, allowed before choice ∧ step h limits choice before = (after,outcome)
end Miri.Interpreter.ExecutionMachine
