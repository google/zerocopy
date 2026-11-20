import Miri.Input.CompilerProviders
import Miri.Input.CompilerVirtualLeaves

/-! Complete symbolic-vtable dictionary without an overwritten baseline.
Only actual memory offsets are supplied by physical consumers. ABI checks
run at call.rs frame initialization, not at vtable identity resolution.
-/
namespace Miri.Input.CompilerVTableLeaves
open Miri.ABI Miri.Interpreter Miri.Memory
private def lift (value : Except String A) : EStateM StepError S A :=
  match value with | .ok value => pure value | .error e => throw (.unsupported e)

def make (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (engine : VTableMachine.Hooks K U Other)
    (memoryOffset : C → MemPlace Provenance → Size → OffsetMode → MemPlaceMeta Provenance →
      MachineHooks.M K U (MemPlace Provenance)) :
    VTableHooks Provenance (MachineHooks.State K U) C CallInstance (FnAbi MIR.TyId) :=
  let facts := p.lifecycle.calls.symbols.facts
  let lookup := CompilerVTableRuntime.GlobalLookup.prepare p.lifecycle.calls.symbols
  let engine := CompilerVTableMachine.hooks p.vtables image engine
  { target := p.runtime.target.base
    isDynamic := fun _ ty => lift (CompilerFacts.boolean facts.context ty "is_dynamic")
    memoryOffset := memoryOffset
    resolvePointer := fun _ pointer => do
      match pointer.intoPointerOrAddr with
      | .error _ => pure (.error .danglingInteger)
      | .ok pointer =>
        match ← engine.functions.ptrGetAlloc pointer with
        | none => pure (.error .danglingInteger)
        | some value => pure (.ok value)
    globalVTable := fun _ id => VTableMachine.globalVTable engine id
    globalFunction := fun _ id => do
      let registry := engine.functions.registry (← get).machine.user
      if registry.extras.any (·.1 == id) then
        throw (.unsupported "FullInstance vtable dictionary cannot represent machine extra function")
      FunctionPointers.globalFunction engine.functions id
    predicates := fun _ token => lift (CompilerVTableFacts.predicates facts token)
    normalizePredicate := fun _ predicate => lift (CompilerVTableFacts.normalizePredicate facts predicate)
    layoutOf := fun _ ty => lift (CompilerFacts.layoutOf facts.context ty)
    eraseAndAnonymize := fun _ ty token => lift (CompilerVTableQueries.eraseAndAnonymize p.vtables.queries ty token)
    ensureMonomorphicType := fun _ ty => lift (CompilerVTableQueries.ensureMonomorphicType p.vtables.queries ty)
    ensureMonomorphicDyn := fun _ token => lift (CompilerVTableQueries.ensureMonomorphicDyn p.vtables.queries token)
    globalSalt := fun _ => return (← engine.functions.chooseSalt).val
    reserveVTable := fun _ ty token salt => do
      if bound : salt < 32 then VTableMachine.reserve engine ty token ⟨salt,bound⟩
      else throw (.invalidProgram "vtable source salt outside 0..32")
    globalRootPointer := fun _ id => return (← FunctionPointers.rootPointer engine.functions id).withOptionalProvenance
    entries := fun _ principal ty => lift
      (CompilerVTableRuntime.entriesUsing p.lifecycle.calls.symbols lookup principal ty)
    assertVirtualInstanceMatches := VirtualCalls.assertConcrete (CompilerVirtualLeaves.make p.lifecycle.calls) }
end Miri.Input.CompilerVTableLeaves
