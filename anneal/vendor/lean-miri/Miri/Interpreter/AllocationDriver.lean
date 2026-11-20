import Miri.Interpreter.FrameRelevance
import Miri.Interpreter.AllocationMachine
import Miri.Interpreter.PointerMachine
import Miri.Interpreter.ExecutionAddressChoices

/-! Source allocation driver closure: thread.rs:231–283 and rustc
interpret/stack.rs:312–321 determine the diagnostic span; PointerMachine
executes actual free_alloc_id/address-reuse release-clock operations. -/
namespace Miri.Interpreter.AllocationDriver
open Miri.ABI Miri.Memory Miri.MIR Miri.Memory.AllocAddresses

abbrev ActualFrame := Frame Provenance LocalLayout MachineHooks.FrameExtra

structure SpanHooks where
  /-- Canonical exported DUMMY_SP, used only for an empty actual stack. -/
  dummy : SpanRef
  debugAssertions : Bool

def frameSpan (frame : ActualFrame) : Except StepError SpanRef := do
  match frame.location with
  | .unwinding span => return span
  | .mir location =>
    let some block := frame.body.basicBlocks[location.block]? |
      throw (.stack (.invalidLocation location))
    if let some statement := block.statements[location.statementIndex]? then
      return statement.sourceInfo.span
    if location.statementIndex == block.statements.size then
      return block.terminator.sourceInfo.span
    throw (.stack (.invalidLocation location))

/-- Read the source-maintained cache belonging to the actual active thread. -/
def currentUserRelevantSpan (h : SpanHooks) : MachineHooks.M K User SpanRef :=
  FrameRelevance.currentUserRelevantSpan h.debugAssertions h.dummy

structure Hooks (K U Payload : Type) where
  allocation : AllocationMachine.DeallocationHooks K (PointerMachine.User U) Payload
  pointer : PointerMachine.Hooks K U
  spans : SpanHooks
  /-- Exact machine MemoryKind classification, not allocation-size inference. -/
  addressKind : MemoryKind K → Except StepError AddressMemoryKind

/-- PointerMachine.freeAllocId changes machine state only; use the actual active
stack as its context and retain all post-error machine mutations. It removes
address inverses before the random reuse choice and release clock. -/
private def free (h : Hooks K U Payload) (context : PointerMachine.State K U)
    (choice : Bool) (id : AllocId) (size : Size) (align : Align) (kind : MemoryKind K) :
    PlaceMachine.MachineM K (PointerMachine.User U) Unit := fun machine =>
  match h.addressKind kind with
  | .error error => .error error machine
  | .ok kind =>
    match PointerMachine.freeAllocId h.pointer id size align kind choice {context with machine} with
    | .ok value state => .ok value state.machine
    | .error error state => .error error state.machine

/-- The source span is computed at its original late stage, after sync checks.
No fallback source span is fabricated when a frame location is invalid. -/
def deallocate [DecidableEq K] (h : Hooks K U Payload) (reuseChoice : Bool)
    (pointer : Pointer (Option Provenance)) (oldLayout : Option (Size × Align))
    (kind : MemoryKind K) : PointerMachine.M K U Unit := do
  let context ← get
  let hooks := {h.allocation with
    -- The removed allocation is a source-local owned value. Its final tree is
    -- not reinserted into the machine or a GC-root cache, even on failure.
    retainDetached := fun _ machine => machine
    currentSpan := fun machine =>
      match currentUserRelevantSpan h.spans { context with machine } with
      | .ok span state => .ok span state.machine
      | .error error state => .error error state.machine
    freeAllocId := free h context reuseChoice}
  AllocationMachine.deallocate hooks pointer oldLayout kind
/-- Production deallocation samples address-reuse choices only after source
borrow/race/synchronization checks and inverse-address removal. -/
def deallocateSource [DecidableEq K]
    (choices : ExecutionChoices.Access (PointerMachine.State K U))
    (h : Hooks K U Payload) (pointer : Pointer (Option Provenance))
    (oldLayout : Option (Size × Align)) (kind : MemoryKind K) : PointerMachine.M K U Unit := do
  let context ← get
  let hooks := {h.allocation with
    retainDetached := fun _ machine => machine
    currentSpan := fun machine =>
      match currentUserRelevantSpan h.spans {context with machine} with
      | .ok span state => .ok span state.machine
      | .error error state => .error error state.machine
    freeAllocId := fun id size align kind machine =>
      match h.addressKind kind with
      | .error error => .error error machine
      | .ok kind =>
        match ExecutionAddressChoices.freeAllocId choices h.pointer id size align kind {context with machine} with
        | .ok value state => .ok value state.machine
        | .error error state => .error error state.machine}
  AllocationMachine.deallocate hooks pointer oldLayout kind
end Miri.Interpreter.AllocationDriver
