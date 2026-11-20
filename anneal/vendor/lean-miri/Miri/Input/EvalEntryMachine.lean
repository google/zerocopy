import Miri.Input.CompilerLinkSections
import Miri.Input.EvalCompilerMachine
import Miri.Interpreter.ExecutionMemoryTransport
import Miri.Interpreter.ExecutionCallTransport
import Miri.Interpreter.ExecutionMachine
import Miri.Interpreter.ExecutionCalls

/-! Construct Main/Thread/TLS hooks from the fixed execution configuration. Compiler constants and native deallocation remain explicit dependencies. -/

namespace Miri.Input.EvalEntryMachine
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Concurrency
open ExecutionStateTransport
abbrev W := EvalWorld.World
abbrev Payload Os R P H D O Aff B Host := ValidityMachine.UserState (W Os R P H D O Aff B Host)
abbrev InnerUser Os R P H D O Aff B Host := Inner (W Os R P H D O Aff B Host)
abbrev S Os R P H D O Aff B Host := MachineHooks.State MiriMemoryKind (InnerUser Os R P H D O Aff B Host)

structure Layouts where
  arguments : EntryArguments.Layouts
  unitPtrMut : LocalLayout
  unitPtrConst : LocalLayout
  u32 : LocalLayout

def layouts (p : CompilerProviders.Prepared) : Except String Layouts := do
  let get := p.primitiveLayout
  return ⟨⟨← get "isize",← get "u8",← get "u16",← get "imm_u8_pointer",← get "imm_u8_pointer_pointer"⟩,
    ← p.primitiveLayout "unit_pointer_mut",
    ← p.primitiveLayout "unit_pointer_const",← p.primitiveLayout "u32"⟩

/-- These are already assembled source engines, not fallback implementations
for instructions. No source call, memory or cleanup callback is chosen here. -/
structure Physical (Os R P H D O Aff B Host C : Type) where
  access : PlaceMachine.AccessConfig MiriMemoryKind (InnerUser Os R P H D O Aff B Host)
  allocation : PlaceMachine.AllocationConfig MiriMemoryKind (InnerUser Os R P H D O Aff B Host)
  compiler : PlaceMachine.CompilerHooks MiriMemoryKind (InnerUser Os R P H D O Aff B Host) C
  functions : FunctionPointers.Hooks MiriMemoryKind (InnerUser Os R P H D O Aff B Host) O
  helpers : FunctionCalls.Hooks Provenance (S Os R P H D O Aff B Host) C MachineHooks.FrameExtra O ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId)
  deallocationError : MemoryLifecycleError → StepError
  deallocate : Pointer (Option Provenance) → Option (Size × Align) →
    MemoryKind MiriMemoryKind →
      MachineHooks.M MiriMemoryKind (InnerUser Os R P H D O Aff B Host) Unit

private def lift (value : Except String A) : MachineHooks.M K U A :=
  match value with | .ok value => pure value | .error error => throw (.unsupported error)
private def tlsError (deallocation : MemoryLifecycleError → StepError) : TlsExecutionError StepError → StepError
  | .leaf error | .exit (.leaf error) => error
  | .scalar error => ScalarOps.scalarError error
  | .immediate error => ScalarOps.immediateError error
  | .exit (.deallocation error) => deallocation error
  | .exit (.race error) => .callback s!"TLS exit clocks: {reprStr error}"
  | error => .invalidProgram s!"TLS source invariant: {reprStr error}"
private def exactEntry (p : CompilerMain.Prepared) (id : DefId) : Except String CompilerMain.Entry := do
  let entries := p.entries.filter (·.definition == id)
  unless entries.size == 1 do throw "missing or duplicate exact source main entry"
  let some entry := entries[0]? | throw "missing source main entry"
  return entry

def physicalFromExecution
    (execution : ExecutionMachine.Config MiriMemoryKind
      (InnerUser Os R P H D O Aff B Host) C O ABI.ExternAbi ClockHost)
    (limits : ExecutionMachine.Limits)
    (deallocationError : MemoryLifecycleError → StepError)
    (deallocate : Pointer (Option Provenance) → Option (Size × Align) →
      MemoryKind MiriMemoryKind → MachineHooks.M MiriMemoryKind
        (InnerUser Os R P H D O Aff B Host) Unit)
     :
    Physical Os R P H D O Aff B Host C :=
  let calls := ExecutionMachine.callHooks execution limits
  { access := execution.access
    allocation := execution.allocation
    compiler := execution.compiler
    functions := execution.functions
    helpers := ExecutionCalls.helpers execution.helpers calls
    deallocationError
    deallocate
    }

/-- Build source policies against the real current backend selection and single
World storage. All startup/compiler failures preserve their actual prefix. -/
def main (p : CompilerProviders.Prepared) (physical : Physical Os R P H D O Aff B Host C)
    (choice : C) (layout : Layouts) (spans : AllocationDriver.SpanHooks) (platform : TlsPlatform)
    (format : ConstructorBinaryFormat)
    (externStatic : DefId → MachineHooks.M MiriMemoryKind (Outer (W Os R P H D O Aff B Host)) (Pointer Provenance))
    (evalWindows : String → String → MachineHooks.M MiriMemoryKind
      (Outer (W Os R P H D O Aff B Host)) (Scalar Provenance))
    (state : MachineHooks.State MiriMemoryKind (Outer (W Os R P H D O Aff B Host))) :
    Except StepError
      (MainMachine.Hooks (Payload Os R P H D O Aff B Host) C O ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId) Aff P) := do
  let selected := EvalBackendMachine.handler (inward state).machine
  if let .error error := selected then throw error
  let functions := ExecutionCallTransport.pointers physical.functions
  let memory : CompilerLinkSections.Memory MiriMemoryKind (Outer (W Os R P H D O Aff B Host)) O := {
    functions
    externStatic := externStatic
    projection := action (physical.compiler.projection choice)
    readImmediate := fun value => action (PlaceMachine.readImmediate physical.access value) }
  let place := PlaceMachine.placeHooks physical.access physical.allocation physical.compiler
  let thread : ThreadMachine.Hooks MiriMemoryKind (Payload Os R P H D O Aff B Host) C O ABI.ExternAbi
      (FnAbi TyId) (ArgAbi TyId) Aff := {
    runtime := fun u => u.payload.payload.runtime.threads
    putRuntime := fun u threads => {u with payload := {u.payload with payload := {u.payload.payload with runtime := {u.payload.payload.runtime with threads}}}}
    functions := ExecutionCallTransport.functions physical.helpers
    allocation := ExecutionMemoryTransport.allocation physical.allocation
    machineMemoryKind := .machine
    writeScalar := fun choice value dest => action (writePlaceImmediate place choice (.scalar value) ⟨.memory dest.mplace,dest.layout⟩)
    spans
    }
  let tls : ThreadTlsMachine.Hooks (Payload Os R P H D O Aff B Host) C O ABI.ExternAbi (FnAbi TyId) (ArgAbi TyId) Aff := {
    thread
    data := fun u => u.payload.payload.runtime.tls
    putData := fun u tls => {u with payload := {u.payload with payload := {u.payload.payload with runtime := {u.payload.payload.runtime with tls}}}}
    target := p.runtime.target
    platform
    unitPtrMut := layout.unitPtrMut
    unitPtrConst := layout.unitPtrConst
    u32Layout := layout.u32
    lookupLinkSection := fun name => CompilerLinkSections.lookup p.main memory (· == name)
    evalWindows
    abi := fun kind => match kind with | .cNoUnwind => .C false | .systemNoUnwind => .System false
    error := tlsError physical.deallocationError }
  return {
    termination := {
      tls
      deallocationError := physical.deallocationError
      deallocate := fun pointer old kind => action (physical.deallocate pointer old kind)
      }
    functions
    access := ExecutionMemoryTransport.access physical.access
    layouts := layout.arguments
    data := fun u => u.payload.payload.main
    putData := fun u main => {u with payload := {u.payload with payload := {u.payload.payload with main}}}
    entry := fun u => u.payload.payload.runtime.entry
    putEntry := fun u entry => {u with payload := {u.payload with payload := {u.payload.payload with runtime := {u.payload.payload.runtime with entry}}}}
    format
    cNoUnwind := .C false
    lookupLinkSection := CompilerLinkSections.lookup p.main memory
    genericParameters := fun id => lift do return (← exactEntry p.main id).parameters
    entrySignature := fun id => lift do (← exactEntry p.main id).signature
    startLangItem := pure p.main.start
    resolveInstance := fun id args => lift (CompilerMain.resolve p.main id args)
    layoutOf := fun ty => lift (p.runtime.lookup ty |>.mapError toString)
    }

/-- Standard startup assembly from the same fixed interpreter Config. Compiler
entry metadata, full-instance call/return behavior, TLS operations, and main
callbacks are delegated to the source constructors above. -/
def mainFromExecution
    (p : CompilerProviders.Prepared)
    (execution : ExecutionMachine.Config MiriMemoryKind
      (InnerUser Os R P H D O Aff B Host) C O ABI.ExternAbi ClockHost)
    (limits : ExecutionMachine.Limits)
    (deallocationError : MemoryLifecycleError → StepError)
    (deallocate : Pointer (Option Provenance) → Option (Size × Align) →
      MemoryKind MiriMemoryKind → MachineHooks.M MiriMemoryKind
        (InnerUser Os R P H D O Aff B Host) Unit)
    (choice : C) (layout : Layouts) (spans : AllocationDriver.SpanHooks)
    (platform : TlsPlatform) (format : ConstructorBinaryFormat)
    (externStatic : DefId → MachineHooks.M MiriMemoryKind
      (Outer (W Os R P H D O Aff B Host)) (Pointer Provenance))
    (evalWindows : String → String → MachineHooks.M MiriMemoryKind
      (Outer (W Os R P H D O Aff B Host)) (Scalar Provenance))
    (state : MachineHooks.State MiriMemoryKind
      (Outer (W Os R P H D O Aff B Host))) :
    Except StepError
      (MainMachine.Hooks (Payload Os R P H D O Aff B Host) C O ABI.ExternAbi
        (FnAbi TyId) (ArgAbi TyId) Aff P) :=
  main p (physicalFromExecution execution limits deallocationError deallocate)
    choice layout spans platform format externStatic evalWindows state
end Miri.Input.EvalEntryMachine
