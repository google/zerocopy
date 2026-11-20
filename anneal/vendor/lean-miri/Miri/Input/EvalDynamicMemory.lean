import Miri.Input.EvalProjectionMachine
import Miri.Input.CompilerProviders

/-! Dynamic memory layout on the actual machine state. Canonical type identity
survives the memory view; symbolic vtable reads need no invented stack or
placeholder full vtable dictionary. Every failing dynamic query retains its
StepError through AccessState.pendingError, including UB classifications. -/
namespace Miri.Input.EvalDynamicMemory
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
abbrev User := EvalProjectionMachine.User
abbrev Machine Os R P H D O Aff B Host := PlaceMachine.Machine MiriMemoryKind (User Os R P H D O Aff B Host)

private def query (value : Except String A) : EStateM StepError S A :=
  match value with | .ok value => pure value | .error error => throw (.unsupported error)
private def project (value : Except ProjectionError A) : EStateM StepError S A :=
  match value with | .ok value => pure value | .error error => throw (IntrinsicVectorMachine.projectionError error)

def arrays : RuntimeArrayQueries.Access (Machine Os R P H D O Aff B Host) where
  get := fun s => s.user.payload.payload.user.types
  set := fun s types => {s with user := {s.user with payload := {s.user.payload with payload :=
    {s.user.payload.payload with user := {s.user.payload.payload.user with types}}}}}

/-- Only source symbolic read operations: resolve identity, look up the actual
registry/imported vtable, compare normalized predicates and query its layout. -/
def vtables (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (ThreadStacks.Storage (EvalWorld.World Os R P H D O Aff B Host)))) :
    VTableReadHooks Provenance (Machine Os R P H D O Aff B Host) Unit where
  resolvePointer := fun _ pointer => do
    match pointer.intoPointerOrAddr with
    | .error _ => pure (.error .danglingInteger)
    | .ok _ =>
      match ← TypedMemoryProviders.resolvePointer pointers (← get).memory pointer 0 with
      | .error _ => pure (.error .danglingInteger)
      | .ok value => pure (.ok (value.allocId,value.offset))
  globalVTable := fun _ id => do
    let state ← get
    if let some entry := state.user.payload.payload.user.vtables.entries.find? (·.allocation == id) then
      return some (entry.typeId,entry.dynamicType)
    if let .ok info := state.memory.getAllocInfo id then
      if info.kind != .vtable then return none
    query (CompilerVTableRuntime.globalVTable p.lifecycle.calls.symbols image state.memory id)
  predicates := fun _ token => query (CompilerVTableFacts.predicates p.lifecycle.calls.symbols.facts token)
  normalizePredicate := fun _ value => query (CompilerVTableFacts.normalizePredicate p.lifecycle.calls.symbols.facts value)
  layoutOf := fun _ ty => RuntimeArrayQueries.layoutOf arrays ty

def dynamic (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (maximum : Size)
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (ThreadStacks.Storage (EvalWorld.World Os R P H D O Aff B Host)))) :
    DynamicLayoutHooks Provenance (Machine Os R P H D O Aff B Host) Unit where
  target := p.runtime.target.base
  maxSizeOfVal := maximum
  classify := fun _ ty => project (EvalProjectionMachine.dynamicKind p.lifecycle.calls.symbols.facts ty)
  field := fun _ layout index => do project (EvalProjectionMachine.field (arrays.get (← get)) layout index)
  packedAlign := fun _ ty => project (EvalProjectionMachine.packed p.runtime ty)
  vtableSizeAndAlign := VTable.getSizeAndAlignRead (vtables p image pointers)

/-- The source operation runs on the real machine carried by the memory
context. No layout-equality search or synthetic interpreter frame is used. -/
def resolver (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (maximum : Size) (fuel : Nat)
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (ThreadStacks.Storage (EvalWorld.World Os R P H D O Aff B Host)))) :
    DynamicLayoutResolver Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
      (PlaceMachine.AccessState MiriMemoryKind (User Os R P H D O Aff B Host)) := fun memory hooks place =>
  let action : EStateM StepError (Machine Os R P H D O Aff B Host) (Option (Size × Align)) := do
    let some ty := place.layout.canonicalType
      | throw (.unsupported "unsized memory view has no canonical compiler type identity")
    let layout ← RuntimeArrayQueries.layoutOf arrays ty
    unless localMemoryLayout layout == place.layout do
      throw (.invalidProgram "canonical dynamic memory layout disagrees with its typed view")
    DynamicLayout.sizeAndAlignFromMeta (dynamic p image maximum pointers) () fuel place.mplace.metadata layout
  match action {hooks.machine with memory} with
  | .ok result machine => ⟨machine.memory,{hooks with machine},.ok result⟩
  | .error error machine =>
    ⟨machine.memory,{hooks with machine, pendingError := some error},.error (reprStr error)⟩
end Miri.Input.EvalDynamicMemory
