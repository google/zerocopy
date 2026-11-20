import Miri.Interpreter.PlaceDynamic

/-! Pinned interpret/projection.rs project_array_fields / ArrayIterator for
memory places. The endpoint probe and element-layout query happen once before
iteration; each subsequent projection uses the cached source layout. -/
namespace Miri.Interpreter.ArrayProjection
open Miri.ABI Miri.Memory Miri.MIR
abbrev M := EStateM StepError
structure Iterator where
  base : MPlaceTy Provenance
  length : UInt64
  stride : Size
  field : LocalLayout
private def lift (value : Except SizeError A) : M S A :=
  match value with
  | .ok value => pure value
  | .error error => throw (.invalidProgram s!"source array projection size: {reprStr error}")

def prepare (h : PlaceProjectionHooks Provenance S C E) (choice : C)
    (unitLayout : M S LocalLayout) (base : MPlaceTy Provenance) : M S Iterator := do
  let .Array stride _ := base.layout.layout.fields
    | throw (.invalidProgram "project_array_fields requires array fields")
  let value : RuntimePlace Provenance := ⟨.memory base.mplace,base.layout⟩
  let length ← PlaceDynamic.length h choice value
  let field ← h.field choice base.layout 0
  let endpoint ← lift (Size.mul stride length)
  let _ ← PlaceDynamic.offsetWithMeta h choice value endpoint .inbounds .none (← unitLayout)
  return ⟨base,length,stride,field⟩

def get (h : PlaceProjectionHooks Provenance S C E) (choice : C)
    (iterator : Iterator) (index : Nat) : M S (MPlaceTy Provenance) := do
  unless index < iterator.length.toNat do throw (.invalidProgram "array iterator index outside its source range")
  let offset ← lift (Size.mul iterator.stride (UInt64.ofNat index))
  let value : RuntimePlace Provenance := ⟨.memory iterator.base.mplace,iterator.base.layout⟩
  let result ← PlaceDynamic.offsetWithMeta h choice value offset .inbounds .none iterator.field
  match result.ref with
  | .memory place => pure ⟨place,result.layout⟩
  | .local .. => throw (.invalidProgram "memory array projection produced a local")
end Miri.Interpreter.ArrayProjection
