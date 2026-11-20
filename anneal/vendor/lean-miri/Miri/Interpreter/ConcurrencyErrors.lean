import Miri.Interpreter.Step
import Miri.Concurrency.AtomicDispatch

/-! Outcome classification for the pinned clock/atomic/store-buffer code.
data_race.rs::report_data_race returns TerminationInfo::DataRace: although
upstream transports this as a machine stop, it is a detected Rust UB outcome.
Clock overflow, invalid metadata indices and impossible buffer handles are
source assertions/panics, not races. They remain explicit internal stops.
Sources: concurrency/{data_race,vector_clock,weak_memory}.rs and
data_structures/range_object_map.rs. This does not classify pointer accesses,
atomic alignment, invalid orderings or unsupported atomic sizes; their source
checks happen in the interpreter before these clock/buffer callbacks. -/
namespace Miri.Interpreter.ConcurrencyErrors
open Miri.Concurrency

def global : GlobalStateError → StepError
  | .thread error => .invalidProgram s!"concurrency thread invariant: {reprStr error}"
  | .clock error => .invalidProgram s!"concurrency clock invariant: {reprStr error}"
  | .missingThreadMetadata thread => .invalidProgram s!"missing source thread metadata: {reprStr thread}"
  | .missingVectorClock index => .invalidProgram s!"missing source vector clock: {reprStr index}"
  | .missingVectorInfo index => .invalidProgram s!"missing source vector metadata: {reprStr index}"
  | .missingTerminationClock thread => .invalidProgram s!"missing terminated-thread clock: {reprStr thread}"
  | .threadNotTerminated thread => .invalidProgram s!"termination clock requested for live thread: {reprStr thread}"
  | .childIsActiveThread => .invalidProgram "spawn clock child is the active thread"
  | .invalidReuseChoice => .invalidProgram "clock-index reuse choice outside source candidates"

def storeBuffer : StoreBufferAllocError → StepError
  | .rangeMap error => .invalidProgram s!"store-buffer range-map invariant: {reprStr error}"
  | .handleInvalidated => .invalidProgram "store-buffer handle invalidated during source operation"

def dataRace : DataRaceResult → StepError
  | .ok => .invalidProgram "successful data-race result supplied as an error"
  | .race => .undefinedBehavior "DataRace"
  | .invalidClockUpdate error => .invalidProgram s!"data-race clock invariant: {reprStr error}"
  | .internalInvariantViolation => .invalidProgram "data-race metadata invariant"
  | .outOfBounds => .invalidProgram "data-race metadata range outside allocation"

def weakMemory : WeakMemoryError → StepError
  | .emptyStoreBuffer => .invalidProgram "source store buffer is empty"
  | .bufferTooLong => .invalidProgram "source store-buffer length invariant"
  | .choiceOutOfBounds => .invalidProgram "weak-memory choice outside permitted store-buffer support"
  | .selectedIndexOutOfBounds => .invalidProgram "selected source store-buffer index is absent"

def atomic : AtomicDispatchError → StepError
  | .globalState error => global error
  | .validation error => dataRace error
  | .syncClock error => dataRace error
  | .storeBuffer error => storeBuffer error
  | .weakMemory error => weakMemory error
  | .missingCreatedBuffer => .invalidProgram "source atomic store did not create its buffer"
  | .syncOperationUnexpectedlySkipped => .invalidProgram "source atomic synchronization unexpectedly skipped"
end Miri.Interpreter.ConcurrencyErrors
