import Miri.Interpreter.UnixTlsDispatch
import Miri.Interpreter.ThreadTlsMachine
import Miri.Interpreter.ExecutionMachine

/-! Physical pthread TLS bindings share ThreadTlsMachine.Data with the existing
TLS destructor loop. No shadow key arena or copied persistent memory is kept. -/
namespace Miri.Interpreter.UnixTlsMachine
open Miri.ABI Miri.Memory Miri.MIR Miri.Concurrency
abbrev M K U A := MachineHooks.M K U A
structure DataAccess (U : Type) where
  get : U → ThreadTlsMachine.Data
  put : U → ThreadTlsMachine.Data → U

/-- Reuse precisely the existing destructor engine's arena accessor. -/
def threadData (h : ThreadTlsMachine.Hooks U C O X F A Aff) :
    DataAccess (ThreadStacks.Storage U) :=
  {get := fun user => h.data user.user
   put := fun user value => {user with user := h.putData user.user value}}

private def lift (result : Except StepError A) : M K U A :=
  match result with | .ok value => pure value | .error error => throw error
private def error (operation : String) : ThreadTlsError → StepError
  | .nonexistentKey key => .undefinedBehavior s!"{operation} a nonexistent TLS key: {key.toNat}"
  | .keySpaceExhausted => .unsupported "we ran out of TLS key space"
  | .keyCounterOverflow => .invalidProgram "TLS key counter overflow"
  | .duplicateKey => .invalidProgram "TLS key counter generated a duplicate"
  | other => .invalidProgram s!"TLS key invariant: {reprStr other}"
private def data (a : DataAccess U) : M K U (ThreadTlsData Provenance) :=
  return (a.get (← get).machine.user).values
private def putData (a : DataAccess U) (values : ThreadTlsData Provenance) : M K U Unit :=
  modify fun state => {state with machine := {state.machine with
    user := a.put state.machine.user {(a.get state.machine.user) with values}}}

/-- The source inserts/increments before checking target key width. Both
mutations survive exhausted-key-space and subsequent destination-write errors. -/
def createKey (a : DataAccess U) (destructor : Option TlsDestructor) (size : Size) : M K U TlsKey := do
  match (← data a).createKey destructor size with
  | .ok key next => putData a next; pure key
  | .error failure next => putData a next; throw (error "creating" failure)
def deleteKey (a : DataAccess U) (key : TlsKey) : M K U Unit := do
  match (← data a).deleteKey key with
  | .ok _ next => putData a next
  | .error failure next => putData a next; throw (error "removing" failure)
def load (a : DataAccess U) (key : TlsKey) (thread : ThreadId) :
    M K U (Pointer (Option Provenance)) :=
  do lift ((← data a).load key thread |>.mapError (error "loading from"))
def store (a : DataAccess U) (key : TlsKey) (thread : ThreadId)
    (pointer : Pointer (Option Provenance)) : M K U Unit := do
  let next ← lift ((← data a).store key thread pointer |>.mapError (error "storing to"))
  putData a next

/-- Genuine source signature/type/alignment capabilities remain explicit;
all scalar, pointer, frame/span and TLS arena operations are source-bound. -/
def hooks [DecidableEq K] (a : DataAccess U)
    (access : PlaceMachine.AccessConfig K U)
    (place : PlaceHooks Provenance (MachineHooks.State K U) C MachineHooks.FrameExtra)
    (choice : C) (functions : FunctionPointers.Hooks K U Other)
    (spans : AllocationDriver.SpanHooks)
    (misalignment : Pointer (Option Provenance) → Align → M K U (Option Misalignment))
    (signatures : ShimSignatures.PrimitiveHooks Provenance (MachineHooks.State K U))
    (signature : String → M K U (FnAbi TyId)) (keyLayout : M K U LocalLayout) :
    UnixTlsDispatch.Hooks (MachineHooks.State K U) D B I :=
  let scalar := fun operand => do
    let value ← PlaceMachine.readImmediate access operand
    lift (value.imm.toScalar.mapError ScalarOps.immediateError)
  let pointer := fun operand => do
    lift ((← scalar operand).toPointer access.runtime.base |>.mapError ScalarOps.scalarError)
  let write := fun value (dest : MPlaceTy Provenance) =>
    writePlaceImmediate place choice (.scalar value) ⟨.memory dest.mplace,dest.layout⟩
  {signatures, signature, keyLayout
   dereference := fun operand layout => do
      let pointer ← pointer operand
      unless layout.layout.isSized do throw (.invalidProgram "deref_pointer_as requires sized pthread_key_t")
      return ⟨⟨pointer,.none,← misalignment pointer layout.layout.align.abi⟩,layout⟩
   readScalar := scalar
   readPointer := pointer
   getPointerFnInstance := fun pointer => do
      match ← FunctionPointers.getPtrFn functions pointer with
      | .Instance fnInstance => pure fnInstance
      | .Other _ => throw (.unsupported "pthread TLS destructor is not a MIR function instance")
   currentUserRelevantSpan := AllocationDriver.currentUserRelevantSpan spans
   activeThread := do return (← get).machine.threads.activeThread
   createKey := createKey a
   deleteKey := deleteKey a
   load := load a
   store := store a
   writeScalar := write
   writePointer := fun pointer dest => do
      write (← lift (Scalar.fromMaybePointer access.runtime.base pointer |>.mapError ScalarOps.scalarError)) dest
   writeNull := fun dest => do
      write (← lift (Scalar.fromUInt (BitVec.ofNat 128 0) dest.layout.layout.size |>.mapError ScalarOps.scalarError)) dest}

def fromExecution [DecidableEq K] (a : DataAccess U)
    (config : ExecutionMachine.Config K U C Other Extern Host) (limits : ExecutionMachine.Limits)
    (choice : C) (spans : AllocationDriver.SpanHooks)
    (misalignment : Pointer (Option Provenance) → Align → M K U (Option Misalignment))
    (signatures : ShimSignatures.PrimitiveHooks Provenance (MachineHooks.State K U))
    (signature : String → M K U (FnAbi TyId)) (keyLayout : M K U LocalLayout) :
    UnixTlsDispatch.Hooks (MachineHooks.State K U) D B I :=
  let config := ExecutionMachine.withValidation config limits
  hooks a config.access (PlaceMachine.placeHooks config.access config.allocation config.compiler)
    choice config.functions spans misalignment signatures signature keyLayout
end Miri.Interpreter.UnixTlsMachine
