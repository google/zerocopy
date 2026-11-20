import Miri.Interpreter.IntrinsicMachine
import Miri.Interpreter.IntrinsicVectorMachine

/-! Direct source intrinsic capability construction. Surviving compiler, choice,
math and policy leaves are explicit; no base physical hook dictionary is accepted.
Canonical operations match AtomicMachine.bind (data_race.rs:749–875),
IntrinsicVectorMachine.bindSimd (intrinsics/simd.rs::emulate_simd_intrinsic),
and IntrinsicMachine.bind (intrinsics/mod.rs::emulate_intrinsic_by_name).
Only dictionary construction changes; source event order and partial-state
behavior stay in those same operations. -/
namespace Miri.Interpreter.ExecutionIntrinsic
open Miri.ABI Miri.Memory Miri.MIR Miri.Concurrency
abbrev User := ValidityMachine.UserState
abbrev State K U := ValidityMachine.State K U
abbrev M K U := ValidityMachine.M K U

namespace Atomic
open AtomicMachine
private def memoryPlace (place : RuntimePlace Provenance) : Except StepError (MPlaceTy Provenance) :=
  match place.ref with
  | .memory memory => .ok ⟨memory,place.layout⟩
  | .local .. => .error (.invalidProgram "atomic dereference produced a local place")
private def liftMachine (action : PlaceMachine.MachineM K (User U) A) : M K U A := fun state =>
  match action state.machine with
  | .ok value machine => .ok value {state with machine}
  | .error error machine => .error error {state with machine}
private def liftResult (result : Except StepError A) : M K U A :=
  match result with | .ok value => pure value | .error error => throw error
structure AccessLeaves (P S C V : Type) where
  loadChoiceRank : C → Nat → RvalueM S Nat
  weakPolicy : WeakCasPolicy
  weakSuccessChoice : C → RvalueM S Bool
  diagnostic : C → WeakMemoryDiagnostic → RvalueM S Unit
  classifyDispatchError : AtomicDispatchError → StepError
  classifyGlobalError : GlobalStateError → StepError

structure Leaves (P S C V : Type) extends AccessLeaves P S C V where
  orderingConst : C → Nat → RvalueM S Concurrency.AtomicOrdering
  volatileConst : C → Nat → RvalueM S Unit

def access [DecidableEq K]
    (leaves : AccessLeaves Provenance (State K U) C (RuntimePlace Provenance))
    (scalarOps : ScalarOpsHooks Provenance (State K U) C)
    (access : PlaceMachine.AccessConfig K (User U))
    (places : PlaceHooks Provenance (State K U) C MachineHooks.FrameExtra)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (extras : MemoryExtras.Hooks K (User U) Payload) :
    AtomicAccessHooks Provenance (State K U) C (RuntimePlace Provenance) :=
  let access := MemoryExtras.bindAccess extras access
  {
    scalarOps := scalarOps
    loadChoiceRank := leaves.loadChoiceRank
    weakPolicy := leaves.weakPolicy
    weakSuccessChoice := leaves.weakSuccessChoice
    diagnostic := leaves.diagnostic
    classifyDispatchError := leaves.classifyDispatchError
    classifyGlobalError := leaves.classifyGlobalError

    target := access.runtime.base
    getGlobal := fun state => state.machine.dataRace
    setGlobal := fun state global => {state with machine := {state.machine with dataRace := some global}}
    threads := fun state => state.machine.threads
    getAtomic := fun state id => MemoryExtras.getAtomic extras state.machine id
    setAtomic := fun id atomic => liftMachine (MemoryExtras.commitAtomic extras id atomic)
    placeLayout := RuntimePlace.layout
    placePointer := fun place => do return (← memoryPlace place).mplace.ptr
    physicalRead := fun _ => physicalRead access
    physicalWrite := fun c value place => do
      let _ ← liftResult (memoryPlace place)
      writePlaceImmediate places c value place
    ghostRead := fun _ => ghostRead access
    checkPointerAlign := fun _ => checkAlignment pointers
    resolveAllocation := fun _ => resolve pointers
    mutability := fun _ => mutability access }

/-- Dispatch adds only the actual full-callee constant queries and source MIR
operand/continuation operations to the shared physical atomic engine. -/
def dispatcher [DecidableEq K]
    (physical : AtomicAccessHooks Provenance (State K U) C (RuntimePlace Provenance))
    (ordering : C → Nat → M K U Concurrency.AtomicOrdering)
    (volatile : C → Nat → M K U Unit)
    (deref : C → OpTy Provenance → M K U (RuntimePlace Provenance))
    (accessConfig : PlaceMachine.AccessConfig K (User U))
    (places : PlaceHooks Provenance (State K U) C MachineHooks.FrameExtra)
    (returnToBlock : C → Option BasicBlockId → M K U Unit) :
    IntrinsicAtomicHooks Provenance (State K U) C (RuntimePlace Provenance) where
  toAtomicAccessHooks := physical
  orderingConst := ordering
  volatileConst := volatile
  derefPointer := deref
  readImmediate := fun _ => PlaceMachine.readImmediate accessConfig
  writeImmediate := writePlaceImmediate places
  returnToBlock := returnToBlock

def make [DecidableEq K]
    (leaves : Leaves Provenance (State K U) C (RuntimePlace Provenance))
    (derefPointer : C → OpTy Provenance → M K U (RuntimePlace Provenance))
    (scalarOps : ScalarOpsHooks Provenance (State K U) C)
    (returnToBlock : C → Option BasicBlockId → M K U Unit)
    (accessConfig : PlaceMachine.AccessConfig K (User U))
    (places : PlaceHooks Provenance (State K U) C MachineHooks.FrameExtra)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (extras : MemoryExtras.Hooks K (User U) Payload) :
    IntrinsicAtomicHooks Provenance (State K U) C (RuntimePlace Provenance) :=
  dispatcher (access leaves.toAccessLeaves scalarOps accessConfig places pointers extras)
    leaves.orderingConst leaves.volatileConst derefPointer accessConfig places returnToBlock
end Atomic

namespace Simd
open IntrinsicVectorMachine
private def liftResult (result : Except StepError A) : M K U A :=
  match result with | .ok value => pure value | .error error => throw error
private def memoryPlace (place : RuntimePlace Provenance) : M K U (MPlaceTy Provenance) :=
  match place.ref with
  | .memory value => pure ⟨value,place.layout⟩
  | .local .. => throw (.invalidProgram "SIMD dereference must produce a memory place")
structure Leaves (P S C V : Type) where
  boolTy : TyId
  u8Ty : TyId
  isSimd : C → TyId → RvalueM S Bool
  simdSizeAndType : C → TyId → RvalueM S (UInt64 × TyId)
  shuffleConst : C → Nat → RvalueM S (Array UInt32)
  alignmentConst : C → Nat → RvalueM S Memory.SimdAlignment
  chooseEqualFloatRight : C → FloatBits → FloatBits → RvalueM S Bool
  fuseMulAdd : C → RvalueM S Bool
  mathLane : C → SimdMathOp → OpTy P → V → RvalueM S Unit

def make [DecidableEq K]
    (leaves : Leaves Provenance (State K U) C (RuntimePlace Provenance))
    (scalarOps : ScalarOpsHooks Provenance (State K U) C)
    (floatOps : FloatOpsHooks Provenance (State K U) C)
    (castHooks : CastHooks Provenance (State K U) C (RuntimePlace Provenance))
    (returnToBlock : C → Option BasicBlockId → RvalueM (State K U) Unit)
    (access : PlaceMachine.AccessConfig K (User U))
    (projection : PlaceProjectionHooks Provenance (State K U) C MachineHooks.FrameExtra)
    (copy : PlaceCopyHooks Provenance (State K U) C)
    (pointerCompiler : PointerPlaceMachine.Compiler K U C)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) :
    IntrinsicSimdHooks Provenance (State K U) C (RuntimePlace Provenance) :=
  let places := projection.place
  {
    boolTy := leaves.boolTy
    u8Ty := leaves.u8Ty
    isSimd := leaves.isSimd
    simdSizeAndType := leaves.simdSizeAndType
    shuffleConst := leaves.shuffleConst
    alignmentConst := leaves.alignmentConst
    scalarOps := scalarOps
    floatOps := floatOps
    castHooks := castHooks
    chooseEqualFloatRight := leaves.chooseEqualFloatRight
    fuseMulAdd := leaves.fuseMulAdd
    mathLane := leaves.mathLane
    returnToBlock := returnToBlock

    target := access.runtime.base
    forceAllocation := fun c source => do
      let memory ← forceAllocation places c source
      pure ⟨.memory memory.mplace,memory.layout⟩
    placeLayout := RuntimePlace.layout
    placePointer := fun source => match source.ref with
      | .memory memory => pure memory.ptr
      | .local .. => .error (.invalidProgram "SIMD backing place has not been allocated")
    fieldRead := fun c source index => do
      match source.op with
      | .immediate _ => liftResult (projectField (← places.projection c) source index |>.mapError projectionError)
      | .indirect memory =>
        let projected ← PlaceDynamic.field projection c ⟨.memory memory,source.layout⟩ index
        match projected.ref with
        | .memory memory => pure ⟨.indirect memory,projected.layout⟩
        | .local .. => throw (.invalidProgram "indirect SIMD field projection became local")
    fieldWrite := PlaceDynamic.field projection
    fieldLayout := fun c layout index => do
      let cx ← places.projection c
      liftResult (cx.field layout index |>.mapError projectionError)
    indexRead := fun c source index => do
      match source.op with
      | .immediate _ => liftResult (projectIndex (← places.projection c) source index |>.mapError projectionError)
      | .indirect memory =>
        let projected ← PlaceDynamic.index projection c ⟨.memory memory,source.layout⟩ index
        match projected.ref with
        | .memory memory => pure ⟨.indirect memory,projected.layout⟩
        | .local .. => throw (.invalidProgram "indirect SIMD index projection became local")
    indexWrite := PlaceDynamic.index projection
    readImmediate := fun _ => PlaceMachine.readImmediate access
    writeImmediate := fun c value dest => writePlaceImmediate places c value dest
    copyOp := fun c source dest => copyRuntimePlace places copy c source dest false
    derefImmediate := fun c value => do
      let memory ← PointerPlaceMachine.fromImmediate access pointerCompiler c value
      pure ⟨.memory memory.mplace,memory.layout⟩
    readPlaceImmediate := fun _ source => do
      let memory ← memoryPlace source
      PlaceMachine.readImmediate access ⟨.indirect memory.mplace,memory.layout⟩
    unalignedPlace := fun _ ptr layout => do
      let memory ← PointerPlaceMachine.fromPointer access ptr layout true
      pure ⟨.memory memory.mplace,memory.layout⟩
    checkAlign := fun _ => AtomicMachine.checkAlignment pointers
    readBytes := fun _ ptr size => do
      pure (← RawMemoryMachine.readBytes access pointers.arithmetic ptr size.bytes).data
    writeBytes := fun _ ptr bytes => RawMemoryMachine.writeBytes access pointers.arithmetic ptr ⟨bytes⟩ }

end Simd

namespace Core
open IntrinsicMachine
private def pointer (place : RuntimePlace Provenance) : Except StepError (Pointer (Option Provenance)) :=
  match place.ref with
  | .memory place => .ok place.ptr
  | .local .. => .error (.invalidProgram "memory intrinsic expected an allocated place")
structure Leaves (P S C V : Type) where
  varArgsFuel : Nat
  maxSizeOfVal : Size
  layoutOf : C → TyId → RvalueM S (TyAndLayout TyId)
  pointeeType : C → TyId → RvalueM S TyId
  integerKind : C → TyId → RvalueM S IntegerKind
  usizeLayout : C → RvalueM S (TyAndLayout TyId)
  isizeLayout : C → RvalueM S (TyAndLayout TyId)
  applyFloatNondeterminism : C → RvalueImmTy P → RvalueM S (RvalueImmTy P)
  chooseEqualFloatRight : C → FloatBits → FloatBits → RvalueM S Bool
  fuseMulAdd : C → RvalueM S Bool
  floatFastError : C → RvalueImmTy P → Nat → RvalueM S (RvalueImmTy P)
  variantLayout : C → TyAndLayout TyId → Nat → RvalueM S (TyAndLayout TyId)
  ensureMonomorphic : C → TyId → RvalueM S Unit
  typeNameConstant : C → TyId → TyAndLayout TyId → RvalueM S (OpTy P)
  needsDrop : C → TyId → RvalueM S Bool
  variantCount : C → TyId → RvalueM S Nat
  callerLocationConstant : C → TyAndLayout TyId → RvalueM S (OpTy P)
  chooseStaticKnown : C → RvalueM S Bool

def make [DecidableEq K]
    (leaves : Leaves Provenance (State K U) C (RuntimePlace Provenance))
    (simdHooks : IntrinsicSimdHooks Provenance (State K U) C (RuntimePlace Provenance))
    (atomicHooks : IntrinsicAtomicHooks Provenance (State K U) C (RuntimePlace Provenance))
    (typeIdHooks : IntrinsicTypeIdHooks Provenance (State K U) C (RuntimePlace Provenance))
    (varArgsHooks : IntrinsicVarArgsHooks Provenance (State K U) C (RuntimePlace Provenance))
    (evalOperand : C → MIR.Operand → RvalueM (State K U) (OpTy Provenance))
    (evalOperandAt : C → OperandPath → MIR.Operand → RvalueM (State K U) (OpTy Provenance))
    (derefPointer : C → OpTy Provenance → RvalueM (State K U) (RuntimePlace Provenance))
    (immPointerToPlace : C → RvalueImmTy Provenance → RvalueM (State K U) (OpTy Provenance))
    (scalarOps : ScalarOpsHooks Provenance (State K U) C)
    (floatOps : FloatOpsHooks Provenance (State K U) C)
    (readDiscriminant : C → OpTy Provenance → RvalueM (State K U) VariantIndex)
    (discriminantForVariant : C → TyId → VariantIndex → RvalueM (State K U) (RvalueImmTy Provenance))
    (catchUnwind : C → OpTy Provenance → OpTy Provenance → OpTy Provenance → RuntimePlace Provenance → Option BasicBlockId → RvalueM (State K U) Unit)
    (returnToBlock : C → Option BasicBlockId → RvalueM (State K U) Unit)
    (access : PlaceMachine.AccessConfig K (User U))
    (allocation : PlaceMachine.AllocationConfig K (User U))
    (extras : MemoryExtras.Hooks K (User U) SyncPayload)
    (deallocateStack : Pointer (Option Provenance) → M K U Unit)
    (compiler : PlaceMachine.CompilerHooks K (User U) C)
    (places : PlaceHooks Provenance (State K U) C MachineHooks.FrameExtra)
    (copy : PlaceCopyHooks Provenance (State K U) C)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (dynamic : DynamicLayoutHooks Provenance (State K U) C)
    (dynamicFuel : Nat)
    (validity : ValidityVisitor.Hooks Provenance (State K U) C MachineHooks.FrameExtra F A Padding)
    (validationFuel : Nat) :
    IntrinsicHooks Provenance (State K U) C (RuntimePlace Provenance) :=
  let access := MemoryExtras.bindAccess extras access
  let copy := {copy with
    readRaw := fun _ => PlaceMachine.readRaw access
    memoryCopy := copyMemory access pointers dynamic dynamicFuel compiler.debugAssertions }
  {
    simdHooks := simdHooks
    atomicHooks := atomicHooks
    typeIdHooks := typeIdHooks
    varArgsHooks := varArgsHooks
    varArgsFuel := leaves.varArgsFuel
    maxSizeOfVal := leaves.maxSizeOfVal
    layoutOf := leaves.layoutOf
    pointeeType := leaves.pointeeType
    integerKind := leaves.integerKind
    usizeLayout := leaves.usizeLayout
    isizeLayout := leaves.isizeLayout
    evalOperand := evalOperand
    evalOperandAt := evalOperandAt
    derefPointer := derefPointer
    immPointerToPlace := immPointerToPlace
    scalarOps := scalarOps
    floatOps := floatOps
    applyFloatNondeterminism := leaves.applyFloatNondeterminism
    chooseEqualFloatRight := leaves.chooseEqualFloatRight
    fuseMulAdd := leaves.fuseMulAdd
    floatFastError := leaves.floatFastError
    readDiscriminant := readDiscriminant
    discriminantForVariant := discriminantForVariant
    variantLayout := leaves.variantLayout
    ensureMonomorphic := leaves.ensureMonomorphic
    typeNameConstant := leaves.typeNameConstant
    needsDrop := leaves.needsDrop
    variantCount := leaves.variantCount
    callerLocationConstant := leaves.callerLocationConstant
    chooseStaticKnown := leaves.chooseStaticKnown
    catchUnwind := catchUnwind
    returnToBlock := returnToBlock

    tryAllocId := fun _ pointer => do
      match pointer.provenance with
      | none => return .error pointer.offset.bytes
      | some provenance =>
        match ← PointerMachine.ptrGetAlloc pointers (Pointer.new provenance pointer.offset) 0 with
        | none => return .error pointer.offset.bytes
        | some result => return .ok result
    checkSignedAccess := fun _ pointer size => fun state =>
      match PointerMachine.checkAccessSigned pointers pointer size .inboundsPointerArithmetic state with
      | .ok () state => .ok (.ok ()) state
      | .error error state => .ok (.error error) state
    target := access.runtime.base
    pointerOffset := access.runtime.pointerOffset
    destLayout := RuntimePlace.layout
    readImmediate := fun _ => PlaceMachine.readImmediate access
    writeImmediate := fun c value dest => writePlaceImmediate places c value dest
    writePointer := fun c ptr dest => do
      let value ← match Scalar.fromMaybePointer access.runtime.base ptr with
        | .ok value => pure value | .error error => throw (ScalarOps.scalarError error)
      writePlaceImmediate places c (.scalar value) dest
    copyOp := fun c source dest => copyRuntimePlace places copy c source dest false
    placeToOp := fun c dest => Miri.Interpreter.placeToOp places c dest
    placePointer := pointer
    dynamicSizeAlign := fun c => DynamicLayout.sizeAndAlignOfVal dynamic c dynamicFuel
    checkAlign := fun _ => AtomicMachine.checkAlignment pointers
    memCopy := fun _ source dest size nonoverlapping =>
      GlobalMemoryCopyMachine.copy access pointers.arithmetic source dest size 1 nonoverlapping
    writeBytes := fun _ ptr byte count =>
      RawMemoryMachine.writeRepeatedByte access pointers.arithmetic ptr byte count.bytes
    readBytesStripProvenance := fun _ ptr size => do
      return (← RawMemoryMachine.readBytes access pointers.arithmetic ptr size.bytes).data
    allocateStack := fun _ layout => do
      let memory ← PlaceMachine.allocateStack allocation layout
      pure ⟨.memory memory.mplace,memory.layout⟩
    deallocateStack := fun _ ptr => deallocateStack ptr
    enforceValidity := fun _ _ => ValidityMachine.enforceValidity
    enforceValidityRecursively := fun _ _ => ValidityMachine.enforceValidityRecursively
    validatePlace := fun c dest recursive reset =>
      ValidityVisitor.validatePlace validity c validationFuel dest recursive reset
    vtableSizeAlign := dynamic.vtableSizeAndAlign }
end Core

end Miri.Interpreter.ExecutionIntrinsic
