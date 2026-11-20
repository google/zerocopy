import Miri.Interpreter.MachineAddress
import Miri.Interpreter.GlobalAllocationMachine

/-! Direct pointer source construction. Global relocation adjustment runs on
actual machine state and never synthesizes a stack. Only external allocation
addresses and extern-static resolution remain genuine external capabilities;
managed address generation, salt choices and borrow root tags are source code.
Human-facing int-to-pointer diagnostics are omitted under the project scope. -/
namespace Miri.Interpreter.PointerSource
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses

private def liftMachine (action : MachineAddress.M K U A) : PointerMachine.M K U A := fun state =>
  match action state.machine with
  | .ok value machine => .ok value {state with machine}
  | .error error machine => .error error {state with machine}

/-- These are internal address invariants/resource stops, never Rust UB. -/
def addressError : AddressStateError → StepError
  | .addressGenerator (.addressSpaceFull next stop) =>
    .resourceExhaustion s!"Miri allocation address space exhausted: {next}/{stop}"
  | .strictIntegerToPointerCast | .strictAddressLookup =>
    .machineStop "Int2PtrWithStrictProvenance"
  | error => .invalidProgram s!"allocation address invariant: {toString error}"

def addressHooks (runtime : RuntimeTargetDataLayout)
    (externalAddress : AllocId → AllocationAddressInfo → MachineAddress.M K U UInt64) : MachineAddress.Hooks K U :=
  ⟨⟨runtime.pointerSize⟩,externalAddress,addressError⟩

/-- Actual lazy materialization is used for exposure; it is not a successful
empty-tree callback. All address operations retain the same canonical maps. -/
def pointers [DecidableEq K] (globalKind : K) (h : MachineAddress.Hooks K U)
    (globals : GlobalAllocationHooks Provenance Miri.TreeBorrows.BorrowTree K
      (PlaceMachine.AccessState K (PointerMachine.User U))) : PointerMachine.Hooks K U where
  arithmetic := h.arithmetic
  externalAddress := fun id info => liftMachine (h.externalAddress id info)
  ensureTreeExtra := GlobalAllocationMachine.ensure globalKind globals
  diagnosticIntToPtr := pure ()
  strictIntToPtr := .machineStop "Int2PtrWithStrictProvenance"
  classifyAddressError := addressError

/-- memory.rs global_root_pointer checks TLS/extern before the machine root
adjustment. Extern statics return their source pointer directly. Root tags are
installed before address assignment, retaining that prefix if assignment fails. -/
def globalRootPointer (choices : ExecutionChoices.Access (MachineAddress.State K U))
    (h : MachineAddress.Hooks K U)
    (externStatic : MIR.DefId → MachineAddress.M K U (Pointer Provenance))
    (pointer : Pointer CtfeProvenance) : MachineAddress.M K U (Pointer Provenance) := do
  let id := pointer.provenance.allocId
  let memory := (← get).memory
  match memory.findGlobal? id with
  | some global =>
    match global.payload with
    | some (.static definition _ tls foreignItem) =>
      if tls then throw (.invalidProgram "global memory cannot point to thread-local static")
      if foreignItem then return ← externStatic definition
    | none =>
      if global.kind == .static then throw (.unsupported "global static compiler predicates unavailable")
    | _ => pure ()
  | none =>
      unless memory.hasExtraFunctionId id || memory.hasVaListId id do
        throw (.invalidProgram "root pointer is neither global, va_list nor machine function")
  let tag ← match (← get).borrowTracker with
    | none => pure Miri.Memory.BorTag.one
    | some tracker =>
      match tracker.global.rootPointerTag id with
      | .error error => throw (.resourceExhaustion s!"global root borrow tag: {reprStr error}")
      | .ok (global,tag) =>
        modify fun state => {state with borrowTracker := some {tracker with global}}
        pure tag
  let base ← MachineAddress.addrFromAllocId choices h id (some .other)
  let root := Pointer.new (Provenance.concrete id tag) (Size.ofBytes base)
  match root.wrappingOffset pointer.offset h.arithmetic with
  | .ok value => pure value
  | .error error => throw (.invalidProgram s!"global root pointer offset: {reprStr error}")
end Miri.Interpreter.PointerSource
