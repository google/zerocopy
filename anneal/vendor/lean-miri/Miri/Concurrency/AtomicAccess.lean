import Miri.Concurrency.DataRace
import Miri.ABI.Align
import Miri.Memory.Access

/-!
# Atomic intrinsic ordering and access checks

This module ports the ordered pre-memory portion of Miri's atomic path:
`machine.rs` converts intrinsic orderings before calling the atomic operation,
and `data_race.rs::atomic_access_check` derives the required alignment from
the access size, checks it, resolves allocation identity, then applies the
read-only-memory rules. The pointer resolver, machine alignment policy, live
allocation lookup, and mutability lookup are explicit callbacks because they
belong to the concrete interpreter state.

This does not perform a scalar load/store, RMW calculation, bounds/permission
hook, or the later race-clock and store-buffer updates. Callers pass callbacks
closed over the actual place and must invoke this check before those effects,
matching Miri's source order.
-/

namespace Miri.Concurrency

open Miri.ABI Miri.Memory

/-- The access class tested by `atomic_access_check`. -/
inductive AtomicAccessKind where
  | load (ordering : AtomicReadOrd)
  | store
  | rmw
  deriving DecidableEq, Repr

/-- The first read-only-memory restriction selected by the source match. -/
inductive ReadOnlyAtomicViolation where
  | storeOrRmw
  | oversizedLoad
  | nonRelaxedLoad
  deriving DecidableEq, Repr

/-- Failures from the source-owned stages of `atomic_access_check`. The
alignment-construction and allocation-expectation variants record the pinned
Rust `unwrap`/`expect` boundaries; they are never treated as successful
accesses. -/
inductive AtomicAccessError (PointerError MutabilityError : Type) where
  | alignmentConstructionPanic (reason : AlignError)
  | pointerAlignment (reason : PointerError)
  | allocationExpectationPanic (reason : PointerError)
  | mutabilityLookup (reason : MutabilityError)
  | undefinedBehavior (violation : ReadOnlyAtomicViolation)
  deriving DecidableEq, Repr

/-- Interpreter-owned callbacks used by the source atomic access check.
`pointerTryGetAllocId` is the `ptr_try_get_alloc_id(ptr, 0)` operation. Its
address error is kept distinct because the pinned source immediately calls
`expect` on this result. -/
structure AtomicAccessOps (AllocId PointerError MutabilityError : Type) where
  checkPtrAlign : Align → Except PointerError Unit
  pointerTryGetAllocId : Except PointerError AllocId
  getAllocMutability : AllocId → Except MutabilityError Mutability

private def readOnlyViolation (size pointerSize : Size)
    (kind : AtomicAccessKind) : Option ReadOnlyAtomicViolation :=
  match kind with
  | .store | .rmw => some .storeOrRmw
  | .load ordering =>
    if size.bytes > pointerSize.bytes then some .oversizedLoad
    else if ordering != .Relaxed then some .nonRelaxedLoad
    else none

/-- Port of `atomic_access_check` after its concrete MPlace callbacks are
supplied. The order is size-to-alignment conversion, pointer alignment,
allocation identity, mutability lookup, and the ordered read-only rules. -/
def atomicAccessCheck {AllocId PointerError MutabilityError : Type}
    (size pointerSize : Size) (kind : AtomicAccessKind)
    (ops : AtomicAccessOps AllocId PointerError MutabilityError) :
    Except (AtomicAccessError PointerError MutabilityError) Unit := do
  let required ← (Align.fromBytes size.bytes).mapError
    AtomicAccessError.alignmentConstructionPanic
  ops.checkPtrAlign required |>.mapError AtomicAccessError.pointerAlignment
  let allocId ← match ops.pointerTryGetAllocId with
    | .error error => throw (.allocationExpectationPanic error)
    | .ok allocId => pure allocId
  let mutability ← (ops.getAllocMutability allocId).mapError
    AtomicAccessError.mutabilityLookup
  if mutability == .Not then
    if let some violation := readOnlyViolation size pointerSize kind then
      throw (.undefinedBehavior violation)
  return ()

/-- Errors before an atomic operation reaches its place access check. Invalid
read/write/fence orderings correspond to the pinned conversion panics and are
kept explicit rather than weakened. -/
inductive AtomicIntrinsicError (PointerError MutabilityError : Type) where
  | invalidOrdering (reason : AtomicOrderingError)
  | accessCheck (reason : AtomicAccessError PointerError MutabilityError)
  deriving DecidableEq, Repr

/-- Machine `atomic_load`: ordering conversion precedes the access check. -/
def prepareAtomicLoad {AllocId PointerError MutabilityError : Type}
    (ordering : AtomicOrdering) (size pointerSize : Size)
    (ops : AtomicAccessOps AllocId PointerError MutabilityError) :
    Except (AtomicIntrinsicError PointerError MutabilityError) AtomicReadOrd := do
  let ordering ← (AtomicReadOrd.ofOrdering ordering).mapError
    AtomicIntrinsicError.invalidOrdering
  (atomicAccessCheck size pointerSize (.load ordering) ops).mapError
    AtomicIntrinsicError.accessCheck
  return ordering

/-- Machine `atomic_store`: ordering conversion precedes the access check. -/
def prepareAtomicStore {AllocId PointerError MutabilityError : Type}
    (ordering : AtomicOrdering) (size pointerSize : Size)
    (ops : AtomicAccessOps AllocId PointerError MutabilityError) :
    Except (AtomicIntrinsicError PointerError MutabilityError) AtomicWriteOrd := do
  let ordering ← (AtomicWriteOrd.ofOrdering ordering).mapError
    AtomicIntrinsicError.invalidOrdering
  (atomicAccessCheck size pointerSize .store ops).mapError
    AtomicIntrinsicError.accessCheck
  return ordering

/-- Machine `atomic_rmw`: its ordering conversion accepts every ordering, then
the shared atomic access check runs before the interpreter reads memory. -/
def prepareAtomicRmw {AllocId PointerError MutabilityError : Type}
    (ordering : AtomicOrdering) (size pointerSize : Size)
    (ops : AtomicAccessOps AllocId PointerError MutabilityError) :
    Except (AtomicIntrinsicError PointerError MutabilityError) AtomicRwOrd := do
  let ordering := AtomicRwOrd.ofOrdering ordering
  (atomicAccessCheck size pointerSize .rmw ops).mapError
    AtomicIntrinsicError.accessCheck
  return ordering

/-- Machine compare-exchange converts the success ordering, then the failure
read ordering, before `atomic_compare_exchange` performs its access check. -/
def prepareAtomicCompareExchange {AllocId PointerError MutabilityError : Type}
    (successOrdering failureOrdering : AtomicOrdering) (size pointerSize : Size)
    (ops : AtomicAccessOps AllocId PointerError MutabilityError) :
    Except (AtomicIntrinsicError PointerError MutabilityError)
      (AtomicRwOrd × AtomicReadOrd) := do
  let success := AtomicRwOrd.ofOrdering successOrdering
  let failure ← (AtomicReadOrd.ofOrdering failureOrdering).mapError
    AtomicIntrinsicError.invalidOrdering
  (atomicAccessCheck size pointerSize .rmw ops).mapError
    AtomicIntrinsicError.accessCheck
  return (success, failure)

/-- A single-thread fence is a source NOP and skips ordering conversion. A
multithread fence uses the checked `AtomicFenceOrd::from` conversion. -/
def prepareAtomicFence (ordering : AtomicOrdering) (singlethread : Bool) :
    Except AtomicOrderingError (Option AtomicFenceOrd) :=
  if singlethread then .ok none
  else (AtomicFenceOrd.ofOrdering ordering).map some

end Miri.Concurrency
