import Miri.Input.EvalCoreMachine
import Miri.Input.EvalGlobalAllocationMachine
import Miri.Interpreter.PointerSource
import Miri.Interpreter.NativeAddressSource
import Miri.Input.CompilerNativeSignatures
import Miri.Input.CompilerExternStatic
import Miri.Input.CompilerForeignSymbols

/-! Pointer/global construction on the actual EvalWorld machine. Native libraries and address mode are fixed during initialization; validateMode checks their consistency. Source: alloc_addresses/mod.rs:110–198,415–451. -/

namespace Miri.Input.EvalPointerSource
open Miri.ABI Miri.Memory Miri.Interpreter
open Miri.Memory.AllocAddresses

abbrev User := EvalCoreMachine.User
abbrev Stored := EvalCoreMachine.Stored
abbrev Control Os R P H D O Aff B Host := ValidityMachine.Control (Stored Os R P H D O Aff B Host)
abbrev Machine Os R P H D O Aff B Host := MachineAddress.State MiriMemoryKind (Control Os R P H D O Aff B Host)
abbrev M Os R P H D O Aff B Host A := EStateM StepError (Machine Os R P H D O Aff B Host) A

/-- The exact tape already retained in the shared World, with no stack view. -/
def tape : ExecutionChoices.Access (Machine Os R P H D O Aff B Host) where
  get := fun machine => machine.user.payload.payload.user.choices
  put := fun machine choices => {machine with user := {machine.user with payload :=
    {machine.user.payload with payload := {machine.user.payload.payload with user :=
      {machine.user.payload.payload.user with choices}}}}}

structure Leaves (Os R P H D O Aff B Host C : Type) where
  nativeLibraryPaths : Host → Array String
  nativeHost : Option (CompilerNativeSignatures.Host MiriMemoryKind (Control Os R P H D O Aff B Host) C)

def arrays : RuntimeArrayQueries.Access (Machine Os R P H D O Aff B Host) where
  get := fun machine => machine.user.payload.payload.user.types
  set := fun machine types => {machine with user := {machine.user with payload :=
    {machine.user.payload with payload := {machine.user.payload.payload with user :=
      {machine.user.payload.payload.user with types}}}}}

/-- Full function signatures and ABI/type queries are direct compiler catalog
adapters. The optional host contains only actual backing and libffi effects. -/
def nativeEffects (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (leaves : Leaves Os R P H D O Aff B Host C) :
    Option (NativeAddressSource.Effects MiriMemoryKind (Control Os R P H D O Aff B Host) C) :=
  CompilerNativeSignatures.optionalEffects p image arrays
    (fun user => user.payload.payload.user.functions) leaves.nativeHost

def validateMode (leaves : Leaves Os R P H D O Aff B Host C) : M Os R P H D O Aff B Host Unit := do
  let machine ← get
  let _ ← match EvalBackendMachine.handler machine with
    | .ok selected => pure selected | .error error => throw error
  let native := !(leaves.nativeLibraryPaths machine.user.payload.payload.user.host).isEmpty
  -- bin/miri.rs rejects strict provenance with native libraries as well.
  if native && machine.user.addresses.provenanceMode == .strict then
    throw (.invalidProgram "native libraries are incompatible with strict provenance")
  unless machine.user.addresses.addressMode == AddressSpaceMode.fromFlags native do
    throw (.invalidProgram "source address mode disagrees with initialized native libraries/backend")

def address (p : CompilerProviders.Prepared) (image : AllocationImage.Imported) (leaves : Leaves Os R P H D O Aff B Host C)
    (choice : C) :
    MachineAddress.Hooks MiriMemoryKind (Control Os R P H D O Aff B Host) :=
  PointerSource.addressHooks p.runtime.target fun id info => do
    let selected ← match EvalBackendMachine.handler (← get) with
      | .ok selected => pure selected | .error error => throw error
    match selected with
    | .none | .vclocks _ =>
      let native := !(leaves.nativeLibraryPaths (← get).user.payload.payload.user.host).isEmpty
      unless native do throw (.invalidProgram "external address requested in managed source mode")
      let some effects := nativeEffects p image leaves | throw (.unsupported "native address effects unavailable")
      NativeAddressSource.externalAddress effects choice id info
/-- Source Machine::extern_static_pointer returns a root pointer without a MIR
frame. It performs the same global borrow-root tag and address assignment as
FunctionPointers::rootPointer, directly on the machine-only state. -/
private def staticRootPointer
    (address : MachineAddress.Hooks MiriMemoryKind
      (Control Os R P H D O Aff B Host))
    (id : AllocId) : M Os R P H D O Aff B Host (Pointer Provenance) := do
  let state ← get
  let tag ← match state.borrowTracker with
    | none => pure Miri.Memory.BorTag.one
    | some tracker =>
      match tracker.global.rootPointerTag id with
      | .error error => throw (.resourceExhaustion s!"extern static root tag: {reprStr error}")
      | .ok (global,tag) =>
        set {state with borrowTracker := some {tracker with global}}
        pure tag
  let base ← MachineAddress.addrFromAllocId tape address id (some .other)
  pure (Pointer.new (Provenance.concrete id tag) (Size.ofBytes base))

private def externStatic [DecidableEq MiriMemoryKind]
    (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (address : MachineAddress.Hooks MiriMemoryKind
      (Control Os R P H D O Aff B Host)) :
    MIR.DefId → M Os R P H D O Aff B Host (Pointer Provenance) := fun definition => do
  CompilerExternStatic.resolveOn p.externStatics image
    (fun state => state.memory)
    (fun state => EvalWorld.roots.externStatics (ExecutionStateTransport.toOuter state.user))
    (fun symbol => do
      let symbols ← match p.foreignSymbols with
        | .ok symbols => pure symbols
        | .error reason => throw (.unsupported s!"compiler foreign-symbol query: {reason}")
      match CompilerForeignSymbols.checkSymbolClash symbols symbol with
      | .ok () => pure ()
      | .error error => throw error)
    (staticRootPointer address) definition

def bytes (p : CompilerProviders.Prepared) (image : AllocationImage.Imported) (leaves : Leaves Os R P H D O Aff B Host C)
    (address : MachineAddress.Hooks MiriMemoryKind (Control Os R P H D O Aff B Host)) :
    GlobalAllocationMachine.Bytes MiriMemoryKind (User Os R P H D O Aff B Host) where
  prepare := fun id value align => do
    if (leaves.nativeLibraryPaths (← get).user.payload.payload.user.host).isEmpty then
      return (value,none)
    let some effects := nativeEffects p image leaves | throw (.unsupported "native global backing effects unavailable")
    (NativeAddressSource.globalBytes tape address effects).prepare id value align
  commit := fun owner value align => do
    let some effects := nativeEffects p image leaves | throw (.unsupported "native global commit effects unavailable")
    NativeAllocationLifecycle.commitBytes effects.backing owner value align
  release := fun owner size align => do
    let some effects := nativeEffects p image leaves | throw (.unsupported "native global release effects unavailable")
    NativeAllocationLifecycle.releaseBytes effects.backing owner size align

structure Constructed (Os R P H D O Aff B Host : Type) where
  address : MachineAddress.Hooks MiriMemoryKind (Control Os R P H D O Aff B Host)
  rootPointer : Pointer CtfeProvenance → M Os R P H D O Aff B Host (Pointer Provenance)
  globals : GlobalAllocationHooks Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
    (PlaceMachine.AccessState MiriMemoryKind (User Os R P H D O Aff B Host))
  pointers : PointerMachine.Hooks MiriMemoryKind (Control Os R P H D O Aff B Host)

/-- Address effects do not depend on pointer hooks. This lets global conversion
close first, and ensureTreeExtra then use that real lazy conversion. -/
def make (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (extras : MemoryExtras.Hooks MiriMemoryKind (User Os R P H D O Aff B Host) P)
    (leaves : Leaves Os R P H D O Aff B Host C)
    (choice : C) : Constructed Os R P H D O Aff B Host :=
  let address := address p image leaves choice
  let resolveExternStatic := externStatic p image address
  let root := PointerSource.globalRootPointer tape address resolveExternStatic
  let globals := EvalGlobalAllocationMachine.make p image extras
    {bytes := bytes p image leaves address, globalRootPointer := root
     -- machine.rs:975 TrackingAlloc uses diagnostics.rs display emission;
     -- it does not mutate interpreter state. Human-facing diagnostic output
     -- is omitted under the same project scope as CreatedPointerTag.
     diagnostic := fun _ _ _ => pure ()}
  {address, rootPointer := root, globals, pointers := PointerSource.pointers .global address globals}

end Miri.Input.EvalPointerSource
