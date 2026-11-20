import Miri.Interpreter.Constant
import Miri.Interpreter.MemoryOperand
import Miri.Interpreter.ScalarOps

/-! Source error classification for operand.rs, memory.rs, and
rustc_middle::mir::interpret::allocation.rs. Allocation's source error enum
classifies pointer-byte reads as Unsupported and uninitialized reads as UB;
raw allocation bounds/mutability assertions are interpreter invariants. The
checked memory-access layer separately reports Rust bounds/read-only UB.
Typed machine/global/dynamic errors are recovered from AccessState.pendingError
before these legacy model-boundary classifications are used. -/
namespace Miri.Interpreter.MemoryErrors
open Miri.ABI Miri.Memory

private def invariant (what : String) (error : α) [Repr α] : StepError :=
  .invalidProgram s!"{what}: {reprStr error}"
private def ub (what : String) (error : α) [Repr α] : StepError :=
  .undefinedBehavior s!"{what}: {reprStr error}"

def allocation : AllocError → StepError
  | .readPointerAsInt _ => .unsupported "ReadPointerAsInt"
  | .readPartialPointer _ => .unsupported "ReadPartialPointer"
  | error@(.invalidUninitBytes _) => ub "InvalidUninitBytes" error
  | error@(.copyRangesOverlap) => ub "overlapping copy_nonoverlapping" error
  | .hostMemoryExhausted => .resourceExhaustion "Miri ran out of memory"
  | .scalar error => ScalarOps.scalarError error
  | error@(.memory _) | error@(.provenance _) | error@(.alignment _)
  | error@(.storageLengthOverflow _) | error@(.storageLengthMismatch ..)
  | error@(.storageBackendNotZeroed ..) | error@(.outOfBounds ..)
  | error@(.invalidSliceEndpoints ..) | error@(.nonEmptyProvenanceWithoutEntry)
  | error@(.readOnlyAllocation) | error@(.pointerSizeMismatch ..)
  | error@(.scalarBytesTooWide _) | error@(.pointerBitsDoNotFitOffset _)
  | error@(.scalarPointerNotTargetSized ..) | error@(.repeatedCopyRequiresNonoverlapping)
  | error@(.singleByteZeroCountCopy) | error@(.allocationHasByteFragmentProvenance)
  | error@(.nativeWriteRangeOutOfBounds ..) => invariant "raw allocation invariant" error

def global : GlobalAccessError → StepError
  | error@(.notFound _) => ub "PointerUseAfterFree" error
  | error@(.dereferenceFunctionPointer _) => ub "DerefFunctionPointer" error
  | error@(.dereferenceVTablePointer _) => ub "DerefVTablePointer" error
  | error@(.dereferenceTypeIdPointer _) => ub "DerefTypeIdPointer" error
  | error@(.unsupportedExternStatic ..) => .unsupported s!"ExternStatic: {reprStr error}"
  | error@(.payloadUnavailable _) => .unsupported s!"compiler global payload unavailable: {reprStr error}"
  | error@(.staticNotAStatic ..) | error@(.threadLocalStatic ..)
  | error@(.payloadKindMismatch ..) => invariant "compiler global invariant" error
  | .hookFailure hook message => .callback s!"{hook}: {message}"

def rawAccess : MemoryAccessError → StepError
  | .globalAccess error => global error
  | error@(.allocationLookup _) => ub "PointerUseAfterFree" error
  | error@(.readOnlyAllocation _) => ub "WriteToReadOnly" error
  | error@(.missingGlobalMachineKind _) => invariant "owned global has no machine kind" error

def access : AccessError → StepError
  | error@(.danglingIntegerPointer ..) => ub "DanglingIntPointer" error
  | error@(.allocationLookup (.deadAllocation _)) => ub "PointerUseAfterFree" error
  | error@(.pointerOutOfBounds ..) => ub "PointerOutOfBounds" error
  | error@(.alignmentCheckFailed _) => ub "AlignmentCheckFailed" error
  | error@(.sizeDoesNotFitI64 _) | error@(.signedSizeOutsideI64 _)
  | error@(.allocationLookup (.unavailable _)) | error@(.pointerArithmetic _)
  | error@(.malformedAlignment _) => invariant "pointer access invariant" error

def pointerAccess : PtrAllocationError → StepError
  | .access error => access error
  | .rawAccess error => rawAccess error
  | .hookFailure hook message => .callback s!"{hook}: {message}"
  | .cacheUpdate error => invariant "allocation cache update" error

def operand : MemoryOperandError → StepError
  | .pointerAccess error => pointerAccess error
  | .allocation error => allocation error
  | .immediate error => ScalarOps.immediateError error
  | .invalidUninitBytes => .undefinedBehavior "InvalidUninitBytes"
  | .dynamicLayoutFailure message => .unsupported s!"dynamic layout: {message}"
  | error@(.runtimeLayout _) | error@(.scalarLayout _) | error@(.memoryRange _)
  | error@(.sourceInvariant _) | error@(.invalidPrimitiveRead) | error@(.rawReadReturnedPlace)
  | error@(.unsizedImmediateWrite) | error@(.immediateAbiMismatch)
  | error@(.immediateSizeMismatch ..) | error@(.immediateCarriesNonPointerProvenance)
  | error@(.memoryUpdate _) => invariant "operand/layout invariant" error

def constant : ConstantError → StepError
  | .metadata message => .unsupported s!"constant compiler metadata: {message}"
  | .query message => .unsupported s!"constant compiler query: {message}"
  | .scalar error => ScalarOps.scalarError error
  | .immediate error => ScalarOps.immediateError error
  | .globalAccess error => global error
  | .memoryAccess error => rawAccess error
  | error@(.tlsConstantPointer _) => invariant "constant cannot point to thread-local static" error
  | .invariant message => .invalidProgram message
end Miri.Interpreter.MemoryErrors
