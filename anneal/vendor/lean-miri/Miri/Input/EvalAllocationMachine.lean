import Miri.Input.EvalBackendMachine
import Miri.Interpreter.ExecutionAddressChoices
import Miri.Interpreter.AllocationDriver

/-! Actual lifecycle closure on EvalWorld. Full-state root addressing and
operation-local deallocation views preserve the real active stack. There is
one address/tape map; inverse removal, reuse choices and release clocks are
performed by ExecutionAddressChoices at their source event cuts. -/
namespace Miri.Input.EvalAllocationMachine
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.Memory.AllocAddresses
abbrev User := EvalBackendMachine.User
abbrev State := EvalBackendMachine.State

def tape : ExecutionChoices.Access (State Os R P H D O Aff B Host) where
  get := fun s => s.machine.user.payload.payload.user.choices
  put := fun s choices => {s with machine := {s.machine with user := {s.machine.user with payload :=
    {s.machine.user.payload with payload := {s.machine.user.payload.payload with user :=
      {s.machine.user.payload.payload.user with choices}}}}}}

private def addressKind : MemoryKind MiriMemoryKind → AddressMemoryKind
  | .stack => .stack | .callerLocation | .machine _ => .other

/-- Tree/race initialization is already PlaceMachine.initStackExtra. This
replaces its tail with source extras creation, using the actual backend flags,
and replaces root addressing with fresh source-point draws on the full state. -/
def allocation
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (ThreadStacks.Storage (EvalWorld.World Os R P H D O Aff B Host))))
    (extras : MemoryExtras.Hooks MiriMemoryKind (User Os R P H D O Aff B Host) P)
    (base : PlaceMachine.AllocationConfig MiriMemoryKind (User Os R P H D O Aff B Host)) :
    PlaceMachine.AllocationConfig MiriMemoryKind (User Os R P H D O Aff B Host) :=
  {base with
    allocationTail := fun id _ _ => do
      let selected ← match EvalBackendMachine.handler (← get) with
        | .ok selected => pure selected | .error error => throw error
      let weak := match selected with | .vclocks global => global.weakMemory | .none => false
      MemoryExtras.initAllocation extras id weak
    adjustRootAddress := fun id tag => do
      let some (_,kind,_) := ((← get).machine.memory.live.map fun (id,entry) => (id,entry.1,entry.2)).find?
        (fun entry => entry.1 == id)
        | throw (.invalidProgram "new root allocation is not live")
      let address ← ExecutionAddressChoices.addrFromAllocId tape pointers id (some (addressKind kind))
      pure (Pointer.new (Provenance.concrete id tag) (Size.ofBytes address))}

/-- Capture the actual active view at this deallocation, not at Config creation.
The source lifecycle callback executes only machine operations, so its active
stack remains this view. Every partial machine/tape effect is returned. -/
def deallocateWith (spans : AllocationDriver.SpanHooks)
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (ThreadStacks.Storage (EvalWorld.World Os R P H D O Aff B Host))))
    (extras : MemoryExtras.Hooks MiriMemoryKind (User Os R P H D O Aff B Host) P)
    (diagnostic : AllocId → PlaceMachine.MachineM MiriMemoryKind (User Os R P H D O Aff B Host) Unit)
    (nativeDrop : Option (Allocation Provenance Miri.TreeBorrows.BorrowTree →
      MachineHooks.M MiriMemoryKind (User Os R P H D O Aff B Host) Unit))
    (ptr : Pointer (Option Provenance)) (old : Option (Size × Align))
    (kind : MemoryKind MiriMemoryKind) : MachineHooks.M MiriMemoryKind (User Os R P H D O Aff B Host) Unit := do
  let context ← get
  let hooks : AllocationMachine.DeallocationHooks MiriMemoryKind (User Os R P H D O Aff B Host) P := {
    extras := extras
    diagnostic := diagnostic
    nativeDrop := nativeDrop
    error := AllocationMachine.deallocationError
    resolvePointer := TypedMemoryProviders.lifecycleResolver pointers
    retainDetached := fun _ machine => machine
    currentSpan := fun machine =>
      match AllocationDriver.currentUserRelevantSpan spans {context with machine} with
      | .ok span after => .ok span after.machine
      | .error error after => .error error after.machine
    freeAllocId := fun id size align kind machine =>
      match ExecutionAddressChoices.freeAllocId tape pointers id size align (addressKind kind) {context with machine} with
      | .ok value after => .ok value after.machine
      | .error error after => .error error after.machine}
  AllocationMachine.deallocate hooks ptr old kind

/-- Compatibility input projects only the genuine diagnostic/native effects;
span, pointer, clock, tree, address and error semantics are source-owned. -/
def deallocate (spans : AllocationDriver.SpanHooks)
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (ThreadStacks.Storage (EvalWorld.World Os R P H D O Aff B Host))))
    (extras : MemoryExtras.Hooks MiriMemoryKind (User Os R P H D O Aff B Host) P)
    (base : AllocationMachine.DeallocationHooks MiriMemoryKind (User Os R P H D O Aff B Host) P)
    (ptr : Pointer (Option Provenance)) (old : Option (Size × Align))
    (kind : MemoryKind MiriMemoryKind) : MachineHooks.M MiriMemoryKind (User Os R P H D O Aff B Host) Unit :=
  deallocateWith spans pointers extras base.diagnostic base.nativeDrop ptr old kind
end Miri.Input.EvalAllocationMachine
