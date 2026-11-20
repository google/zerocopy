import Miri.Input.CompilerProviders
import Miri.Input.CompilerCtfeValidity
import Miri.Input.CompilerPaths
import Miri.Input.RuntimeArrayFacts
import Miri.Interpreter.ExecutionValidity
import Miri.Interpreter.CompilerExecutionProviders

/-! Direct source validity compiler leaves. Physical Box projection uses the
canonical projection driver; CTFE allocation lookup executes the canonical
pointer/global algorithm and exact compiler static predicates.
No baseline visitor dictionary or successful missing-query defaults are needed. -/
namespace Miri.Input.CompilerValidityLeaves
open Miri.ABI Miri.Interpreter Miri.Memory
private def lift (value : Except String A) : EStateM StepError S A :=
  match value with
  | .ok value => pure value
  | .error reason => throw (.unsupported s!"validity compiler query: {reason}")

def make (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (arrays : RuntimeArrayQueries.Access (ValidityMachine.State K U))
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) :
    ExecutionValidity.Leaves (ValidityMachine.State K U) C :=
  let facts := p.lifecycle.calls.symbols.facts
  let context := facts.context
  let constructed := fun ty => do
    return (arrays.get (← get)).entries.any (·.value.ty == ty)
  { classify := fun _ ty => do
      if ← constructed ty then
        let (_,element) ← match RuntimeArrayTypes.arrayInfo (arrays.get (← get)) ty with
          | .ok value => pure value
          | .error reason => throw (.unsupported s!"runtime array classification: {reprStr reason}")
        pure (.sequence element.ty)
      else lift (CompilerFactAdapters.validityKind facts ty)
    unitLayout := fun _ => lift (CompilerFacts.unitLayout context)
    typeName := fun _ ty => do
      -- A runtime constructor has no compiler-rendered name unless it aliases
      -- an existing source type. Missing diagnostics remain an explicit query.
      pure (← lift (context.runtime.node ty |>.mapError toString)).display
    opsemInhabited := fun _ ty => do
      let world := arrays.get (← get)
      lift (RuntimeArrayFacts.opsemInhabited context world ty (world.entries.size+1))
    isFreeze := fun _ ty => do lift (RuntimeArrayFacts.boolean context (arrays.get (← get)) ty "is_freeze")
    fieldPath := fun _ layout index child => do
      if ← constructed layout.ty then pure (.arrayElem index)
      else lift (CompilerPaths.fieldPath context layout index child)
    variantPath := fun _ layout index => lift (CompilerPaths.variantPath context layout index)
    projectBox := CompilerExecutionProviders.projectBox context p.lifecycle.calls.runtime projection
    metadataTail := fun _ ty => lift (CompilerFactAdapters.metadataTail facts ty)
    ctfePointerLookup := CompilerCtfeValidity.lookup p image pointers }
end Miri.Input.CompilerValidityLeaves
