import Miri.Interpreter.AtomicMachine
import Miri.Interpreter.AllocationMachine
import Miri.Interpreter.GlobalMemoryCopyMachine
import Miri.Interpreter.RawMemoryMachine

/-! Portable intrinsic memory and helper dictionaries on canonical machine
state. Arithmetic dispatch stays in Intrinsics; physical memory callbacks are
closed with the actual allocation, TB, race, weak-memory and sync pipelines. -/
namespace Miri.Interpreter.IntrinsicMachine
open Miri.ABI Miri.Memory Miri.MIR
abbrev User := ValidityMachine.UserState
abbrev State K U := ValidityMachine.State K U
abbrev M K U := ValidityMachine.M K U

private def pointer (place : RuntimePlace Provenance) : Except StepError (Pointer (Option Provenance)) :=
  match place.ref with
  | .memory place => .ok place.ptr
  | .local .. => .error (.invalidProgram "memory intrinsic expected an allocated place")

/-- Full typed-copy memory arm, preserving destination dynamic query before
optional source query, real global materialization, and delayed misalignment. -/
def copyMemory [DecidableEq K] (access : PlaceMachine.AccessConfig K (User U))
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (dynamic : DynamicLayoutHooks Provenance (State K U) C)
    (fuel : Nat) (debugAssertions : Bool) (choice : C)
    (source dest : MPlaceTy Provenance) : M K U Unit :=
  GlobalMemoryCopyMachine.typedCopy access PointerMachine.User.addresses pointers.arithmetic
    dynamic fuel debugAssertions choice source dest

/-- Bind concrete physical helper operations. AllocationConfig and deallocation
hooks must be the owner's already composed lifecycle dictionaries, including
MemoryExtras initialization and cleanup; this never installs them twice.
Compiler type/layout/dereference queries remain the existing source ports. -/
def bind [DecidableEq K]
    (base : IntrinsicHooks Provenance (State K U) C (RuntimePlace Provenance))
    (access : PlaceMachine.AccessConfig K (User U))
    (allocation : PlaceMachine.AllocationConfig K (User U))
    (deallocation : AllocationMachine.DeallocationHooks K (User U) SyncPayload)
    (compiler : PlaceMachine.CompilerHooks K (User U) C)
    (copy : PlaceCopyHooks Provenance (State K U) C)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (dynamic : DynamicLayoutHooks Provenance (State K U) C)
    (dynamicFuel : Nat)
    (validity : ValidityVisitor.Hooks Provenance (State K U) C MachineHooks.FrameExtra F A Padding)
    (validationFuel : Nat) :
    IntrinsicHooks Provenance (State K U) C (RuntimePlace Provenance) :=
  let access := MemoryExtras.bindAccess deallocation.extras access
  let places := PlaceMachine.placeHooks access allocation compiler
  let copy := {copy with
    readRaw := fun _ => PlaceMachine.readRaw access
    memoryCopy := copyMemory access pointers dynamic dynamicFuel compiler.debugAssertions }
  PointerMachine.intrinsicHooks pointers {base with
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
    deallocateStack := fun _ ptr => AllocationMachine.deallocate deallocation ptr none .stack
    enforceValidity := fun _ _ => ValidityMachine.enforceValidity
    enforceValidityRecursively := fun _ _ => ValidityMachine.enforceValidityRecursively
    validatePlace := fun c dest recursive reset =>
      ValidityVisitor.validatePlace validity c validationFuel dest recursive reset
    vtableSizeAlign := dynamic.vtableSizeAndAlign }
end Miri.Interpreter.IntrinsicMachine
