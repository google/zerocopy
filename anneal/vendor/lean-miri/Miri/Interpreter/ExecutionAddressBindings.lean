import Miri.Interpreter.ExecutionAddressChoices
import Miri.Interpreter.FunctionPointers

/-! Lawful embedding of actual address/tape actions into whole interpreter
User records, including ThreadStacks.Storage. Actual stack/memory changes are
preserved; no synthetic stack or second address/tape state is created. -/
namespace Miri.Interpreter.ExecutionAddressBindings
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
open ExecutionChoices

def action (lens : FunctionPointers.AddressLens Whole Payload)
    (inner : PointerMachine.M K Payload A) : MachineHooks.M K Whole A := fun state =>
  let source : PointerMachine.State K Payload := ⟨state.stack,{state.machine with user := lens.get state.machine.user}⟩
  match inner source with
  | .ok result after => .ok result ⟨after.stack,{after.machine with user := lens.put state.machine.user after.machine.user}⟩
  | .error error after => .error error ⟨after.stack,{after.machine with user := lens.put state.machine.user after.machine.user}⟩

/-- The tape remains inside the lawful pointer-user embedding. This lens
updates only the actual nested record and preserves the active stack. -/
def tape (lens : FunctionPointers.AddressLens Whole Payload)
    (inner : Access (PointerMachine.User Payload)) : Access (MachineHooks.State K Whole) := {
  get := fun state => inner.get (lens.get state.machine.user)
  put := fun state value =>
    let user := lens.put state.machine.user (inner.put (lens.get state.machine.user) value)
    {state with machine := {state.machine with user}} }

def pointerTape (inner : Access (PointerMachine.User Payload)) : Access (PointerMachine.State K Payload) := {
  get := fun state => inner.get state.machine.user
  put := fun state value => {state with machine := {state.machine with user := inner.put state.machine.user value}} }

def adjustRootPointer (access : Access (PointerMachine.State K U)) (h : PointerMachine.Hooks K U)
    (id : AllocId) (tag : BorTag) (offset : Size) (kind : AddressMemoryKind) :
    PointerMachine.M K U (Pointer Provenance) := do
  let address ← ExecutionAddressChoices.addrFromAllocId access h id (some kind)
  let ptr := Pointer.new (Provenance.concrete id tag) (Size.ofBytes address)
  match ptr.wrappingOffset offset h.arithmetic with
  | .ok ptr => pure ptr
  | .error error => throw (h.classifyAddressError (.pointerArithmetic error))

/-- Source global/function address assignment uses fresh choices only on an
uncached managed address. Function salt draws remain independently bound by
ExecutionChoiceBindings.functionHooks using the same nested tape. -/
def functionHooks (lens : FunctionPointers.AddressLens Whole Payload)
    (access : Access (PointerMachine.User Payload)) (h : PointerMachine.Hooks K Payload)
    (base : FunctionPointers.Hooks K Whole Other) : FunctionPointers.Hooks K Whole Other :=
  {base with
    ptrGetAlloc := fun ptr => action lens (PointerMachine.ptrGetAlloc h ptr 0)
    adjustRootPointer := fun id tag => action lens (adjustRootPointer (pointerTape access) h id tag .ZERO .other)}
end Miri.Interpreter.ExecutionAddressBindings
