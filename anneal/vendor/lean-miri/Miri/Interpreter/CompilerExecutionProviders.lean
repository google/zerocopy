import Miri.Input.CompilerPaths
import Miri.Input.CompilerRuntimeQueries
import Miri.Input.CompilerPrimitiveFacts
import Miri.Interpreter.IntrinsicVectorMachine

/-! Ordinary scalar/typed-pointer providers from exact imported rustc facts.
Type identity comes from canonical input IDs and source query evidence, never
layout size, pointer bytes or diagnostic type spelling. -/
namespace Miri.Interpreter.CompilerExecutionProviders
open Miri.ABI Miri.Memory Miri.MIR Miri.Input
abbrev Result := Except StepError
private def query (name : String) (result : Except String A) : Result A :=
  result.mapError fun error => .callback s!"compiler {name}: {error}"
private def metadata (result : Except RuntimeMetadataError A) : Result A :=
  result.mapError fun error => .callback s!"compiler runtime metadata: {toString error}"
private def liftResult (result : Result A) : RvalueM S A :=
  match result with | .ok value => pure value | .error error => throw error
private def node (facts : CompilerFacts.Context) (ty : TyId) : Result TypeNode := do
  let value ← metadata (facts.runtime.node ty)
  unless value.shapeStatus == .supported do throw (.callback "compiler scalar type shape unresolved")
  pure value

def integerKind (facts : CompilerFacts.Context) (ty : TyId) : Result IntegerKind := do
  let value ← node facts ty
  let kind ← match value.shapeKind with
    | .int =>
      let some (.known kind) := value.shapeMetadata.signedKind
        | throw (.callback "compiler signed integer kind missing")
      unless kind.signed do throw (.invalidProgram "compiler int shape has unsigned integer tag")
      pure kind
    | .uint =>
      let some (.known kind) := value.shapeMetadata.unsignedKind
        | throw (.callback "compiler unsigned integer kind missing")
      if kind.signed then throw (.invalidProgram "compiler uint shape has signed integer tag")
      pure kind
    | _ => throw (.invalidProgram "integer operation on non-integer compiler type")
  pure kind

def format (facts : CompilerFacts.Context) (ty : TyId) : Result FloatFormat := do
  let value ← node facts ty
  unless value.shapeKind == .float do throw (.invalidProgram "float operation on non-float compiler type")
  match value.shapeMetadata.floatKind with
  | some .f16 => pure .binary16 | some .f32 => pure .binary32
  | some .f64 => pure .binary64 | some .f128 => pure .binary128
  | _ => throw (.callback "compiler float format unsupported or unresolved")

/-- Source is_any_ptr includes function pointers, while unary PtrMetadata does
not. The separate category prevents the provider from admitting extra MIR. -/
def scalarClass (facts : CompilerFacts.Context) (ty : TyId) : Result ScalarTypeClass := do
  match (← node facts ty).shapeKind with
  | .bool => pure .boolean | .char => pure .character
  | .int | .uint => return .integer (← integerKind facts ty)
  | .float => pure .floating
  | .rawPointer | .reference => pure .pointer
  | .functionPointer => pure .functionPointer
  | _ => throw (.invalidProgram "invalid MIR scalar operand compiler type")

def metadataLayout (facts : CompilerFacts.Context) (pointer : TyId) : Result LocalLayout := do
  let pointee ← query "builtin_deref" (CompilerFacts.requiredType facts pointer "builtin_deref_explicit")
  let ty ← query "ptr_metadata_ty" (CompilerFacts.requiredType facts pointee "pointer_metadata_type")
  query "layout_of metadata" (CompilerFacts.layoutOf facts ty)

def floatHooks (facts : CompilerFacts.Context) (base : FloatOpsHooks P S C) : FloatOpsHooks P S C :=
  {base with
    integerKindOf := fun _ ty => liftResult (integerKind facts ty)
    formatOf := fun _ ty => liftResult (format facts ty)
    boolLayout := fun _ => liftResult (metadata (facts.runtime.findKind .bool))}

/-- The exact Ordering language-item type is a required readonly compiler
query, supplied by CompilerPrimitiveFacts; it cannot be inferred from an enum
name or its three discriminants. All other scalar compiler leaves are closed. -/
def scalarHooks [PointerProvenance P] (facts : CompilerFacts.Context)
    (floats : FloatOpsHooks P S C)
    (base : ScalarOpsHooks P S C) : ScalarOpsHooks P S C :=
  let floats := floatHooks facts floats
  {base with
    classify := fun _ ty => liftResult (scalarClass facts ty)
    boolLayout := fun _ => liftResult (metadata (facts.runtime.findKind .bool))
    orderingLayout := fun _ => liftResult (query "ty_ordering_enum" (CompilerPrimitiveFacts.orderingLayout facts.runtime))
    overflowLayout := fun _ element => liftResult (metadata (facts.runtime.overflowTupleLayout element))
    metadataLayout := fun _ ty => liftResult (metadataLayout facts ty)
    unitLayout := fun _ => liftResult (query "unit layout" (CompilerPrimitiveFacts.unitLayout facts.runtime))
    floatBinary := FloatOps.binary floats
    floatUnary := FloatOps.unary floats}

/-- Compiler classification for pointer→place construction/dereference. The
Box test uses source is_global_box rather than scalar ABI shape. -/
def pointerCompiler (prepared : CompilerFactAdapters.Prepared) : PointerPlaceMachine.Compiler K U C := {
  kind := fun _ ty => liftResult do
    match (← node prepared.context ty).shapeKind with
    | .reference => pure .reference | .rawPointer => pure .raw
    | .adt =>
      if ← query "is_global_box" (CompilerFacts.boolean prepared.context ty "is_global_box") then pure .box else pure .other
    | _ => pure .other
  builtinDeref := fun _ ty => liftResult (query "builtin_deref" (CompilerFacts.builtinDeref prepared.context ty true))
  layoutOf := fun _ ty => liftResult (query "layout_of" (CompilerFacts.layoutOf prepared.context ty))
  structTail := fun _ ty => liftResult do
    let tail ← query "struct_tail_for_codegen" (CompilerFacts.requiredType prepared.context ty "metadata_tail")
    match (← node prepared.context tail).shapeKind with
    | .slice => pure .slice | .str => pure .str | .foreign => pure .foreign
    | .dynamicTraitObject =>
      let .dynamic expected ← query "dynamic predicates" (CompilerFactAdapters.validityKind prepared tail)
        | throw (.invalidProgram "dynamic tail compiler classification mismatch")
      pure (.dynamic expected)
    | _ => pure .other }

/-- Source project_to_ptr_in_box: both field projections precede boxed_ty,
mutable raw-pointer type construction and wrapping transmute. -/
def projectBox (facts : CompilerFacts.Context) (runtime : CompilerRuntimeQueries.Prepared)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (choice : C) (source : RuntimePlace Provenance) :
    ValidityMachine.M K U (RuntimePlace Provenance × RuntimePlace Provenance) := do
  unless source.layout.layout.fields.count == 2 do throw (.invalidProgram "Box must have exactly 2 fields")
  let pointer ← PlaceDynamic.field projection choice source 0
  let allocator ← PlaceDynamic.field projection choice source 1
  let pointee ← liftResult (query "boxed_ty" (CompilerFacts.requiredType facts source.layout.ty "boxed_type"))
  let pointerType ← liftResult (query "mutable pointer type" (CompilerRuntimeQueries.mutPointerType runtime pointee))
  let layout ← liftResult (query "layout_of raw pointer" (CompilerFacts.layoutOf facts pointerType))
  let pointer ← IntrinsicVectorMachine.transmuteWrite projection choice pointer layout
  pure (pointer,allocator)
/-- Complete scalar arithmetic dictionary on the canonical machine: compiler
class/result types, exact FloatOps, real Miri pointers and pointer validity. -/
def machineScalarHooks [DecidableEq K] (prepared : CompilerFactAdapters.Prepared)
    (access : ValidityMachine.Access K U)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (dynamic : DynamicLayoutHooks Provenance (ValidityMachine.State K U) C)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A) (fuel : Nat)
    (floats : FloatOpsHooks Provenance (ValidityMachine.State K U) C)
    (base : ScalarOpsHooks Provenance (ValidityMachine.State K U) C) :
    ScalarOpsHooks Provenance (ValidityMachine.State K U) C :=
  let facts := prepared.context
  let scalar := scalarHooks facts floats base
  let scalar := PointerMachine.scalarOps pointers facts.runtime.target.base scalar
    (fun _ ty => liftResult do pure ((← node facts ty).shapeKind == .rawPointer))
    (fun _ => liftResult (query "usize" (CompilerPrimitiveFacts.usizeLayout facts.runtime)))
    (fun _ ty => liftResult do
      let pointee ← query "builtin_deref" (CompilerFacts.requiredType facts ty "builtin_deref_explicit")
      query "layout_of pointee" (CompilerFacts.layoutOf facts pointee))
  PointerPlaceMachine.bindScalarOps access (pointerCompiler prepared) dynamic vtable fuel scalar

/-- Install exactly that dictionary at the MIR evaluation boundary. Choice,
operand evaluation and source result-layout assertions stay in Rvalue. -/
def rvalueHooks (scalar : ScalarOpsHooks Provenance (ValidityMachine.State K U) C)
    (base : RvalueHooks Provenance (ValidityMachine.State K U) C V) :
    RvalueHooks Provenance (ValidityMachine.State K U) C V :=
  {base with binaryOp := ScalarOps.binary scalar, unaryOp := ScalarOps.unary scalar}

end Miri.Interpreter.CompilerExecutionProviders
