import Miri.Concurrency.AtomicDispatch
import Miri.Interpreter.IntegerOps
import Miri.Memory.Allocation
import Miri.OperationalSafety

/-!
# Scalar memory operations around Miri's atomic hooks

This is the concrete scalar-storage layer for one live allocation when the
allocation has no borrow-tracker or synchronization-object payload. It uses
the pinned rustc `Allocation.read_scalar`/`write_scalar` transitions and then
the Miri clock/store-buffer hooks in `AtomicDispatch`, in source order. The
allocation's `Extra` is `Unit`, so this module cannot represent a Miri
allocation with active borrow tracking or synchronization objects. Callers
must not treat this restricted slice as a complete interpreter execution.

`atomicAccessCheck` (place alignment, allocation resolution and read-only
rules), interpreter `before_memory_*` hooks and diagnostics are outside
this module. The concrete Miri path performs `before_memory_*` while
`ongoing_action_data_race_free` is set, so this module mirrors that flag window
around byte access; it does not claim to run the absent borrow/sync hooks.
Every operation here is therefore a component of the dispatch, not a Miri
program-safety result.
-/
namespace Miri.Concurrency

open Miri.ABI Miri.Interpreter Miri.Memory Miri.MIR

/-- Scalar state for one allocation's interpreter bytes and its exact
allocation-local data-race/store-buffer state. -/
structure AtomicScalarMemory (Prov : Type) where
  memory : Allocation Prov Unit
  concurrency : AtomicState (Scalar Prov)

/-- Failures from the concrete scalar-storage and clock/buffer stages. -/
inductive AtomicScalarMemoryError where
  | allocation (error : AllocError)
  | scalar (error : ScalarError)
  | dispatch (error : AtomicDispatchError)
  | integerOperation (error : IntegerOpError)
  | integerTypeSizeMismatch (scalarSize typeSize : Size)
  | nestedAllowDataRaces
  | invalidUninitializedAtomicRead
  | missingWeakMemoryAllocation
  | unexpectedWeakMemoryAllocation
  | unexpectedRmwResult
  deriving Repr

/-- Outcome always carries the post-operation byte and concurrency state,
including write errors after source-ordered partial allocation mutation. The
nonempty `requiredHooks` field prevents the scalar/data-race fragment from
being mistaken for a complete interpreter dispatch. -/
inductive AtomicScalarSourceHook where
  | atomicAccessCheck
  | interpreterBeforeMemoryRead
  | interpreterBeforeMemoryWrite
  deriving DecidableEq, Repr

structure AtomicScalarMemoryTransition (Prov Result : Type) where
  state : AtomicScalarMemory Prov
  outcome : Except AtomicScalarMemoryError Result
  requiredHooks : List AtomicScalarSourceHook

/-- A component error or uncompleted interpreter hook is an obligation, not a
successful terminal result. This adapter deliberately has no UB judgement:
classification requires the actual interpreter hooks and diagnostics. -/
inductive AtomicScalarUnknown where
  | componentError (error : AtomicScalarMemoryError)
  | interpreterHooks (hooks : List AtomicScalarSourceHook)
  deriving Repr

/-- Interpret this component's state as an operational-safety outcome. Since
its access-check and memory-hook obligations have not been discharged by this
module, successful scalar/clock work remains `blocked`; it cannot establish
`Safe` merely because the component returned a value. -/
def AtomicScalarMemoryTransition.asOperationalOutcome
    (transition : AtomicScalarMemoryTransition Prov Result) :
    Miri.OperationalSafety.Outcome Result Unit AtomicScalarUnknown :=
  match transition.outcome with
  | .error error => .blocked (.componentError error)
  | .ok value =>
    if transition.requiredHooks.isEmpty then .returned value
    else .blocked (.interpreterHooks transition.requiredHooks)

private def failure (state : AtomicScalarMemory Prov)
    (error : AtomicScalarMemoryError) : AtomicScalarMemoryTransition Prov Result :=
  { state := state, outcome := .error error, requiredHooks := [] }

private def success (state : AtomicScalarMemory Prov) (result : Result) :
    AtomicScalarMemoryTransition Prov Result :=
  { state := state, outcome := .ok result, requiredHooks := [] }

private def sourceHooks (readAttempted writeAttempted : Bool) :
    List AtomicScalarSourceHook :=
  [.atomicAccessCheck] ++
    (if readAttempted then [.interpreterBeforeMemoryRead] else []) ++
    (if writeAttempted then [.interpreterBeforeMemoryWrite] else [])

private def withGlobal {Prov : Type} (state : AtomicScalarMemory Prov)
    (global : GlobalState) : AtomicScalarMemory Prov :=
  { state with concurrency := { state.concurrency with global := global } }

private def beginDataRaceFreeWindow {Prov : Type} (state : AtomicScalarMemory Prov) :
    Except AtomicScalarMemoryError (AtomicScalarMemory Prov) := do
  if state.concurrency.global.ongoingActionDataRaceFree then
    throw .nestedAllowDataRaces
  pure (withGlobal state
    (GlobalState.withDataRaceFreeAction state.concurrency.global true))

private def endDataRaceFreeWindow {Prov : Type} (state : AtomicScalarMemory Prov) :
    AtomicScalarMemory Prov :=
  withGlobal state (GlobalState.withDataRaceFreeAction state.concurrency.global false)

/-- Execute the source atomic-read's actual allocation byte/scalar read inside
the `allow_data_races_ref` flag window. Miri's later `buffered_atomic_read`
still validates the selected modification-order value. -/
private def readUnderAtomicWindow [DecidableEq Prov] [PointerProvenance Prov]
    (state : AtomicScalarMemory Prov) (layout : TargetDataLayout)
    (range : AllocRange) (readProvenance : Bool) :
    AtomicScalarMemory Prov × Except AtomicScalarMemoryError (Scalar Prov) := Id.run do
  match beginDataRaceFreeWindow state with
  | .error error => return (state, .error error)
  | .ok active =>
    let read := active.memory.readScalar layout range readProvenance
    let finished := endDataRaceFreeWindow active
    return (finished, read.mapError AtomicScalarMemoryError.allocation)

/-- Execute the source atomic-write's actual allocation scalar mutation inside
the `allow_data_races_mut` flag window. The returned allocation is retained on
all `Allocation::write_scalar` failure paths before detector validation. -/
private def writeUnderAtomicWindow [DecidableEq Prov] [PointerProvenance Prov]
    (state : AtomicScalarMemory Prov) (layout : TargetDataLayout)
    (range : AllocRange) (value : Scalar Prov) :
    AtomicScalarMemory Prov × Except AtomicScalarMemoryError Unit := Id.run do
  match beginDataRaceFreeWindow state with
  | .error error => return (state, .error error)
  | .ok active =>
    match Allocation.writeScalar layout range value active.memory with
    | .ok () memory =>
      let updated := endDataRaceFreeWindow { active with memory := memory }
      return (updated, .ok ())
    | .error error memory =>
      let updated := endDataRaceFreeWindow { active with memory := memory }
      return (updated, .error (.allocation error))

private def requireWeakMemoryAllocation {Prov : Type}
    (state : AtomicScalarMemory Prov) :
    Except AtomicScalarMemoryError Unit :=
  if state.concurrency.global.weakMemory &&
      state.concurrency.weakMemoryAllocation.isNone then
    .error .missingWeakMemoryAllocation
  else if !state.concurrency.global.weakMemory &&
      state.concurrency.weakMemoryAllocation.isSome then
    .error .unexpectedWeakMemoryAllocation
  else .ok ()

/-- The scalar-memory and buffered-clock implementation of the body after
`atomic_access_check` in `read_scalar_atomic`. It reads the actual latest
allocation scalar first, then delegates legal finite read choices and their
validation/metadata order to `bufferedAtomicRead`. `choiceRank` is an explicit
member of the exact source candidate set, not a random seed. -/
def atomicScalarLoad [DecidableEq Prov] [PointerProvenance Prov]
    (state : AtomicScalarMemory Prov) (threads : ThreadManager)
    (layout : TargetDataLayout) (range : AllocRange) (readProvenance : Bool)
    (ordering : AtomicReadOrd) (choiceRank : Nat) :
    AtomicScalarMemoryTransition Prov (Scalar Prov) :=
  let (transition, readAttempted) := Id.run do
    match requireWeakMemoryAllocation state with
    | .error error => return (failure state error, false)
    | .ok () => pure ()
    if state.concurrency.global.ongoingActionDataRaceFree then
      return (failure state .nestedAllowDataRaces, false)
    let (readState, latest) := readUnderAtomicWindow state layout range readProvenance
    let latest ← match latest with
      | .error error => return (failure readState error, true)
      | .ok scalar => pure scalar
    let dispatched := bufferedAtomicRead readState.concurrency threads range ordering
      latest choiceRank
    let updated := { readState with concurrency := dispatched.state }
    match dispatched.outcome with
    | .error error => return (failure updated (.dispatch error), true)
    | .ok result =>
      match result.value with
      | none => return (failure updated .invalidUninitializedAtomicRead, true)
      | some scalar => return (success updated scalar, true)
  { transition with requiredHooks := sourceHooks readAttempted false }

/-- Source `write_scalar_atomic`'s local path for the actual allocation
and VClock weak-memory backend. The old scalar is a best-effort ghost read:
its failure becomes an uninitialized initial store, as in Miri. The real write
happens before `validate_atomic_store`; its memory mutation remains present if
validation later fails. -/
def atomicScalarStore [DecidableEq Prov] [PointerProvenance Prov]
    (state : AtomicScalarMemory Prov) (threads : ThreadManager)
    (layout : TargetDataLayout) (range : AllocRange) (readProvenance : Bool)
    (value : Scalar Prov)
    (ordering : AtomicWriteOrd) : AtomicScalarMemoryTransition Prov Unit :=
  let (transition, writeAttempted) := Id.run do
    match requireWeakMemoryAllocation state with
    | .error error => return (failure state error, false)
    | .ok () => pure ()
    if state.concurrency.global.ongoingActionDataRaceFree then
      return (failure state .nestedAllowDataRaces, false)
    let initial := (state.memory.readScalar layout range readProvenance).toOption
    let (writtenState, writeResult) := writeUnderAtomicWindow state layout range value
    match writeResult with
    | .error error => return (failure writtenState error, true)
    | .ok () => pure ()
    let dispatched := atomicStoreState writtenState.concurrency threads range ordering value initial
    let updated := { writtenState with concurrency := dispatched.state }
    match dispatched.outcome with
    | .error error => return (failure updated (.dispatch error), true)
    | .ok () => return (success updated (), true)
  { transition with requiredHooks := sourceHooks false writeAttempted }

/-- The supported source `AtomicRmwOp` forms. These mirror the cases used by
rustc's atomic intrinsics: arithmetic/bitwise MIR operations, signedness-aware
min/max, and scalar swap. -/
inductive AtomicRmwScalarOp where
  | mir (operation : BinOp) (negateResult : Bool)
  | minimum
  | maximum
  | swap
  deriving DecidableEq, Repr

/-- Result of the integer or thin-pointer compare-exchange path. -/
structure AtomicCompareExchangeResult (Prov : Type) where
  oldValue : Scalar Prov
  succeeded : Bool

private def integerValue [PointerProvenance Prov] (value : Scalar Prov)
    (type : IntegerType) : Except AtomicScalarMemoryError IntegerValue := do
  let scalar ← value.toScalarInt |>.mapError
    AtomicScalarMemoryError.scalar
  if scalar.size != type.size then
    throw (.integerTypeSizeMismatch scalar.size type.size)
  pure { scalar := scalar, type := type }

private def scalarFromIntegerResult [PointerProvenance Prov]
    (result : IntegerResult) : Except AtomicScalarMemoryError (Scalar Prov) :=
  match result with
  | .scalar value => .ok (Scalar.fromScalarInt value)
  | .withOverflow _ _ => .error .unexpectedRmwResult
  | .boolean value => .ok (Scalar.fromBool value)
  | .ordering _ => .error .unexpectedRmwResult

/-- Compute the exact `atomic_rmw_op` result for the supported integer
intrinsic operators. `type` is the MIR layout type carried by both `ImmTy`
operands. Swap preserves a pointer scalar without stripping its provenance. -/
private def applyAtomicRmw [PointerProvenance Prov]
    (operation : AtomicRmwScalarOp) (type : IntegerType)
    (left right : Scalar Prov) : Except AtomicScalarMemoryError (Scalar Prov) := do
  match operation with
  | .swap => pure right
  | .mir op negateResult => do
    if !(op == .Add || op == .Sub || op == .BitAnd || op == .BitOr || op == .BitXor) then
      throw (.integerOperation (.invalidBinaryOperator op))
    if negateResult && op != .BitAnd then
      throw (.integerOperation (.invalidUnaryOperator .Not type.signed))
    let l ← integerValue left type
    let r ← integerValue right type
    let result ← (IntegerOps.binary op l r).mapError
      AtomicScalarMemoryError.integerOperation
    if negateResult then
      match result with
      | .scalar value =>
        let inverted ← (IntegerOps.unary .Not { scalar := value, type := type }).mapError
          AtomicScalarMemoryError.integerOperation
        pure (Scalar.fromScalarInt inverted)
      | _ => throw .unexpectedRmwResult
    else
      scalarFromIntegerResult result
  | .minimum | .maximum => do
    let l ← integerValue left type
    let r ← integerValue right type
    let ordering ← (IntegerOps.binary .Lt l r).mapError
      AtomicScalarMemoryError.integerOperation
    let .boolean leftIsLess := ordering | throw .unexpectedRmwResult
    match operation with
    | .minimum => pure (if leftIsLess then left else right)
    | .maximum => pure (if leftIsLess then right else left)
    | _ => throw .unexpectedRmwResult

/-- Source `atomic_rmw`'s local scalar path: checked scalar read, exact
MIR operator calculation, byte/provenance write, atomic RMW validation, then
the store-buffer read of the last modification followed by append. -/
def atomicScalarRmw [DecidableEq Prov] [PointerProvenance Prov]
    (state : AtomicScalarMemory Prov) (threads : ThreadManager)
    (layout : TargetDataLayout) (range : AllocRange) (readProvenance : Bool)
    (operation : AtomicRmwScalarOp) (integerType : IntegerType)
    (rhs : Scalar Prov) (ordering : AtomicRwOrd) :
    AtomicScalarMemoryTransition Prov (Scalar Prov) :=
  let (transition, readAttempted, writeAttempted) := Id.run do
    match requireWeakMemoryAllocation state with
    | .error error => return (failure state error, false, false)
    | .ok () => pure ()
    if state.concurrency.global.ongoingActionDataRaceFree then
      return (failure state .nestedAllowDataRaces, false, false)
    let (readState, old) := readUnderAtomicWindow state layout range readProvenance
    let old ← match old with
      | .error error => return (failure readState error, true, false)
      | .ok scalar => pure scalar
    let value ← match applyAtomicRmw operation integerType old rhs with
      | .error error => return (failure readState error, true, false)
      | .ok scalar => pure scalar
    let (writtenState, writeResult) := writeUnderAtomicWindow readState layout range value
    match writeResult with
    | .error error => return (failure writtenState error, true, true)
    | .ok () => pure ()
    let dispatched := atomicRmwState writtenState.concurrency threads range ordering old value
    let updated := { writtenState with concurrency := dispatched.state }
    match dispatched.outcome with
    | .error error => return (failure updated (.dispatch error), true, true)
    | .ok () => return (success updated old, true, true)
  { transition with requiredHooks := sourceHooks readAttempted writeAttempted }

/-- Miri `operator.rs::binary_ptr_op` compares thin-pointer address bits,
not allocation IDs or borrow tags. Relative CTFE pointers remain an explicit
`readPointerAsInt` error; their offsets are not machine addresses. The integer
type parameter describes only the integer operand case. -/
private def compareExchangeEqual [PointerProvenance Prov]
    (layout : TargetDataLayout) (integerType : IntegerType)
    (old expected : Scalar Prov) : Except AtomicScalarMemoryError Bool := do
  if old.isPointer || expected.isPointer then
    let pointerSize := Size.fromBits layout.pointerWidth.bits
    let left ← old.toBits pointerSize |>.mapError AtomicScalarMemoryError.scalar
    let right ← expected.toBits pointerSize |>.mapError AtomicScalarMemoryError.scalar
    pure (left == right)
  else
    let left ← integerValue old integerType
    let right ← integerValue expected integerType
    match ← (IntegerOps.binary .Eq left right).mapError
        AtomicScalarMemoryError.integerOperation with
    | .boolean value => pure value
    | _ => throw .unexpectedRmwResult

/-- The integer and thin-pointer branches of `atomic_compare_exchange`. For weak CAS,
`spuriousFailureChosen` is the explicit outcome selected from the source RNG;
it only changes an otherwise-successful comparison. On failure, validation is
an atomic load followed by `perform_read_on_buffered_latest`; on success, the
new scalar is written before atomic-RMW validation and buffered-RMW metadata. -/
def atomicScalarCompareExchange [DecidableEq Prov] [PointerProvenance Prov]
    (state : AtomicScalarMemory Prov) (threads : ThreadManager)
    (layout : TargetDataLayout) (range : AllocRange) (readProvenance : Bool)
    (integerType : IntegerType) (expected newValue : Scalar Prov)
    (canFailSpuriously spuriousFailureChosen : Bool)
    (successOrdering : AtomicRwOrd) (failureOrdering : AtomicReadOrd) :
    AtomicScalarMemoryTransition Prov (AtomicCompareExchangeResult Prov) :=
  let (transition, readAttempted, writeAttempted) := Id.run do
    match requireWeakMemoryAllocation state with
    | .error error => return (failure state error, false, false)
    | .ok () => pure ()
    if state.concurrency.global.ongoingActionDataRaceFree then
      return (failure state .nestedAllowDataRaces, false, false)
    let (readState, oldResult) := readUnderAtomicWindow state layout range readProvenance
    let old ← match oldResult with
      | .error error => return (failure readState error, true, false)
      | .ok scalar => pure scalar
    let equality ← match compareExchangeEqual layout integerType old expected with
      | .error error => return (failure readState error, true, false)
      | .ok value => pure value
    let succeeded := equality && !(canFailSpuriously && spuriousFailureChosen)
    if !succeeded then
      let dispatched := atomicCompareExchangeFailureState readState.concurrency threads
        range failureOrdering
      let updated := { readState with concurrency := dispatched.state }
      match dispatched.outcome with
      | .error error => return (failure updated (.dispatch error), true, false)
      | .ok () => return (success updated { oldValue := old, succeeded := false }, true, false)
    let (writtenState, writeResult) :=
      writeUnderAtomicWindow readState layout range newValue
    match writeResult with
    | .error error => return (failure writtenState error, true, true)
    | .ok () => pure ()
    let dispatched := atomicRmwState writtenState.concurrency threads range
      successOrdering old newValue
    let updated := { writtenState with concurrency := dispatched.state }
    match dispatched.outcome with
    | .error error => return (failure updated (.dispatch error), true, true)
    | .ok () => return (success updated { oldValue := old, succeeded := true }, true, true)
  { transition with requiredHooks := sourceHooks readAttempted writeAttempted }

end Miri.Concurrency
