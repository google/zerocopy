import Miri.Input.EvalCompilerMachine
import Miri.Input.CompilerCallConstruction
import Miri.Input.CompilerStorage
import Miri.Input.CompilerCopy
import Miri.Input.EvalRetagMachine

/-! Source-owned construction for the one EvalWorld. These constructors accept
actual compiler/host capabilities, never a baseline ExecutionMachine.Config or
placeholder operational records. The remaining top-level assembly is built on
these same persistent registry, address, frame and source-choice stores. -/
namespace Miri.Input.EvalConfiguration
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
abbrev User := EvalCoreMachine.User
abbrev State := EvalCoreMachine.State
abbrev Stored := EvalCoreMachine.Stored
private def lift (value : Except String A) : MachineHooks.M K U A :=
  match value with | .ok value => pure value | .error reason => throw (.unsupported reason)

/-- Exact source machine option; Always short-circuits inline_never just as
FunctionPointers.globalSalt does. No inline classification is inferred. -/
def functions (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (crossCrateInlineAlways : Bool)
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (Stored Os R P H D O Aff B Host))) :
    FunctionPointers.Hooks MiriMemoryKind (User Os R P H D O Aff B Host) O := Id.run do
  let lookup := CompilerVTableRuntime.GlobalLookup.prepare p.lifecycle.calls.symbols
  let inlineLookup := CompilerFunctionPointers.InlineLookup.prepare p.pointers
  return {
    registry := fun user => user.payload.payload.user.functions
    putRegistry := fun user functions => {user with payload := {user.payload with payload :=
      {user.payload.payload with user := {user.payload.payload.user with functions}}}}
    crossCrateInlineAlways := crossCrateInlineAlways
    inlineNever := fun callee => lift do
      let some never := CompilerFunctionPointers.inlineNeverUsing inlineLookup callee
        | throw "exact full-instance inline attribute absent"
      pure never
    chooseSalt := do
      let selected ← ExecutionChoices.index EvalCoreMachine.tape .globalSalt 32
      if valid : selected < 32 then pure ⟨selected,valid⟩
      else throw (.invalidProgram "checked source global salt exceeded support")
    ptrGetAlloc := fun pointer => PointerMachine.ptrGetAlloc pointers pointer 0
    adjustRootPointer := fun id tag => do
      let address ← ExecutionAddressChoices.addrFromAllocId EvalCoreMachine.tape pointers id (some .other)
      pure (Pointer.new (Provenance.concrete id tag) (Size.ofBytes address))
    importedFunction := fun id => do
      lift (CompilerVTableRuntime.globalFunctionUsing p.lifecycle.calls.symbols lookup image (← get).machine.memory id)
  }

/-- Real symbolic memory maps, distinct from function/vtable registries. Empty
initial maps are rustc Memory::new; neither map adds provenance GC roots. -/
def symbols : IntrinsicSymbolsMachine.Access (User Os R P H D O Aff B Host) where
  get := fun user => user.payload.payload.user.symbols
  put := fun user symbols => {user with payload := {user.payload with payload :=
    {user.payload.payload with user := {user.payload.payload.user with symbols}}}}

def identity : ExecutionCallLeaves.IdentityAccess (User Os R P H D O Aff B Host) where
  get := fun user => user.payload.payload.identitySupply
  put := fun user identitySupply => {user with payload := {user.payload with payload :=
    {user.payload.payload with identitySupply}}}

/-- Host byte storage and allocation diagnostics are explicit. Root address
selection, weak-memory extras and actual backend inspection are source code,
not caller supplied successful allocation hooks. -/
def allocation
    (maximumObjectSize : Size) (storage : Size → Align → Option (Array UInt8))
    (diagnostic : AllocId → Size → Align → PlaceMachine.MachineM MiriMemoryKind (User Os R P H D O Aff B Host) Unit)
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (Stored Os R P H D O Aff B Host)))
    (extras : MemoryExtras.Hooks MiriMemoryKind (User Os R P H D O Aff B Host) P) :
    PlaceMachine.AllocationConfig MiriMemoryKind (User Os R P H D O Aff B Host) where
  maximumObjectSize := maximumObjectSize
  zeroedStorage := storage
  diagnostic := diagnostic
  allocationTail := fun id _ _ => do
    let selected ← match EvalBackendMachine.handler (← get) with
      | .ok selected => pure selected | .error error => throw error
    let weak := match selected with | .vclocks global => global.weakMemory | .none => false
    MemoryExtras.initAllocation extras id weak
  adjustRootAddress := fun id tag => do
    let some (_,kind,_) := ((← get).machine.memory.live.map fun (id,entry) => (id,entry.1,entry.2)).find?
      (fun entry => entry.1 == id) | throw (.invalidProgram "new root allocation is not live")
    let kind := match kind with | .stack => AllocAddresses.AddressMemoryKind.stack | .callerLocation | .machine _ => .other
    let address ← ExecutionAddressChoices.addrFromAllocId EvalCoreMachine.tape pointers id (some kind)
    pure (Pointer.new (Provenance.concrete id tag) (Size.ofBytes address))
end Miri.Input.EvalConfiguration
