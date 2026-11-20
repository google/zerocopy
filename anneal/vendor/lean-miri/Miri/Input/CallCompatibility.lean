import Miri.Input.RuntimeMetadata
import Miri.Interpreter.LayoutCompat

/-! Internal connection from compiler input records to the source ABI
compatibility port. Missing compiler predicates/normalization are mandatory
query obligations, never heuristic equivalence based on size or debug strings. -/
namespace Miri.Input.CallCompatibility
open Miri.ABI Miri.Interpreter
abbrev Result := Except RuntimeMetadataError
private def require (value : Option A) (path : String) : Result A := RuntimeMetadata.require value path
private def invalid (path message : String) : RuntimeMetadataError := .invalid path message

def attributes (source : AbiAttributes) : Result ArgAttributes := do
  if source.argExtension.status != .supported then
    throw (.unsupported "argument attribute status")
  if source.regularBits >= 2^16 then throw (invalid "regular attributes" "u16 overflow")
  let regular := UInt16.ofNat source.regularBits
  if source.inRegister != (regular &&& 64 == 64) then throw (invalid "InReg" "redundant attribute mismatch")
  let extension ← match source.argExtension.tag with
    | "none" => pure ArgExtension.None
    | "zero_extend" => pure .Zext
    | "sign_extend" => pure .Sext
    | _ => throw (.unsupported "argument extension")
  let align ← source.pointeeAlignBytes.mapM RuntimeMetadata.alignment
  return ⟨regular,extension,← RuntimeMetadata.size source.pointeeSizeBytes,align⟩

private def hintPrimitive (source : TaggedNode) : Result Primitive := do
  let j := source.payload
  match source.tag with
  | "integer" =>
    let integer ← match ← RuntimeMetadata.text j "integer_kind" with
      | "i8" => pure Integer.I8 | "i16" => pure .I16 | "i32" => pure .I32
      | "i64" => pure .I64 | "i128" => pure .I128
      | _ => throw (.unsupported "register hint integer")
    return .Int integer (← RuntimeMetadata.truth j "signed")
  | "float" =>
    let float ← match ← RuntimeMetadata.text j "float_kind" with
      | "f16" => pure ABI.Float.F16 | "f16b" => pure .F16B | "f32" => pure .F32
      | "f64" => pure .F64 | "f128" => pure .F128 | "ppcf128" => pure .PpcF128
      | _ => throw (.unsupported "register hint float")
    return .Float float
  | "pointer" => return .Pointer ⟨← RuntimeMetadata.u32 (← RuntimeMetadata.number j "address_space") "hint address space"⟩
  | _ => throw (.unsupported "register hint primitive")

def register (source : AbiRegister) : Result Reg := do
  let kind ← match source.kind with
    | .integer => pure RegKind.Integer | .float => pure .Float | .ppcF128 => pure .PpcF128
    | .vector => pure (RegKind.Vector (hintVectorElem := ← hintPrimitive (← require source.hintElement "register hint")))
    | .unknown _ => throw (.unsupported "register kind")
  return ⟨kind,Size.fromBits (← RuntimeMetadata.u64 source.sizeBits "register bits")⟩

def castTarget (source : AbiCastTarget) : Result CastTarget := do
  if source.prefixRegisters.size > 8 then throw (invalid "cast prefix" "exceeds source ArrayVec capacity")
  return {
    «prefix» := ← source.prefixRegisters.mapM register
    restOffset := ← source.restOffsetBytes.mapM RuntimeMetadata.size
    rest := ⟨← register source.restRegister,← RuntimeMetadata.size source.restTotalBytes,source.restIsConsecutive⟩
    attrs := ← attributes source.attributes }

def passMode (source : AbiPassMode) : Result PassMode := do
  let expected ← match source.kind with
    | .ignore | .cast => pure 0
    | .direct | .indirect => pure 1
    | .pair | .indirectUnsized => pure 2
    | .unknown _ => throw (.unsupported "pass mode")
  if source.attributes.size != expected then throw (invalid "pass attributes" "arity mismatch")
  let attrsAt (index : Nat) := do attributes (← require source.attributes[index]? s!"pass attributes {index}")
  match source.kind with
  | .ignore => pure .Ignore
  | .direct => return .Direct (← attrsAt 0)
  | .pair => return .Pair (← attrsAt 0) (← attrsAt 1)
  | .cast =>
    let pad ← require source.padI32Count "cast.pad_i32_count"
    if pad >= 256 then throw (invalid "cast padding" "u8 overflow")
    return .Cast (UInt8.ofNat pad) (← castTarget (← require source.castTarget "cast.target"))
  | .indirect =>
    let mode ← require source.indirectMode "indirect mode"
    if mode.status != .supported then throw (.unsupported "indirect mode status")
    let mode ← match mode.tag with
      | "pointer" => pure IndirectMode.Pointer | "on_stack" => pure .OnStack
      | "amdgpu_kernel_argument" => pure .AmdgpuKernelArg
      | _ => throw (.unsupported "indirect mode")
    let space ← source.addressSpace.mapM (fun n => AddressSpace.mk <$> RuntimeMetadata.u32 n "indirect address space")
    return .Indirect (← attrsAt 0) space mode
  | .indirectUnsized => return .IndirectUnsized (← attrsAt 0) (← attrsAt 1)
  | .unknown _ => throw (.unsupported "pass mode")

def argument (runtime : RuntimeMetadata) (source : AbiArgument) : Result (ArgAbi TypeId) := do
  let _ ← runtime.node source.typeId
  let layout ← match source.layout with
    | none => throw (.unsupported "physical compiler FnAbi argument layout is absent (legacy producer schema)")
    | some layout => (RuntimeMetadata.layout runtime.target layout).mapError id
  return ⟨⟨source.typeId,layout⟩,← passMode source.mode⟩

/-- These source compiler queries are absent or only partially represented by
the exporter. Each consumer must supply exact-key evidence or explicit errors.
In particular, item names are not reconstructed from diagnostic def paths. -/
structure Evidence (S : Type) where
  eraseUnsafeBinder : TypeId → Miri.Interpreter.LayoutCompat.M S TypeId
  normalize : TypeId → Miri.Interpreter.LayoutCompat.M S TypeId
  reprEqualUpToSeed : TypeId → TypeId → Miri.Interpreter.LayoutCompat.M S Bool
  itemName : TypeId → Miri.Interpreter.LayoutCompat.M S String
  nonnullOptimizationGuaranteed : TypeId → Miri.Interpreter.LayoutCompat.M S Bool
  isGlobalBox : TypeId → Miri.Interpreter.LayoutCompat.M S Bool
  boxedType : TypeId → Miri.Interpreter.LayoutCompat.M S TypeId
  pointerMetadataType : TypeId → Miri.Interpreter.LayoutCompat.M S TypeId

private def lift (value : Result A) : Miri.Interpreter.LayoutCompat.M S A :=
  match value with | .ok value => pure value | .error e => throw (.unsupported (toString e))
private def shape (runtime : RuntimeMetadata) (id : TypeId) : Result (TypeNode × Lean.Json) := do
  let node ← runtime.node id
  return (node,← RuntimeMetadata.jsonField node.payload "shape")
private def typeRef (j : Lean.Json) : Result TypeId := RuntimeMetadata.number j "type_id"

def kind (runtime : RuntimeMetadata) (id : TypeId) : Result (Miri.Interpreter.LayoutCompat.TypeKind TypeId) := do
  let (node,source) ← shape runtime id
  match node.shapeKind with
  | .tuple => pure .tuple | .never => pure .never | .functionDefinition => pure .functionDefinition
  | .closure => pure .closure | .coroutine => pure .coroutine | .coroutineClosure => pure .coroutineClosure
  | .array => return .array (← typeRef (← RuntimeMetadata.jsonField source "element"))
  | .adt => pure .adt
  | .patternType => return .pattern (← typeRef (← RuntimeMetadata.jsonField source "base"))
  | .unsafeBinder => pure .unsafeBinder
  | .alias => pure .alias
  | .reference => return .reference (← typeRef (← RuntimeMetadata.jsonField source "pointee"))
  | .rawPointer => return .rawPointer (← typeRef (← RuntimeMetadata.jsonField source "pointee"))
  | .functionPointer => pure .functionPointer
  | .int | .uint =>
    let tag ← require (if node.shapeKind == .int then node.shapeMetadata.signedKind else node.shapeMetadata.unsignedKind) "integer type tag"
    let .known tag := tag | throw (.unsupported "unknown integer type tag")
    return .integer tag
  | .char => pure .char
  | .unknown _ => throw (.unsupported "unknown type kind")
  -- These are the known source `_ => false` cases, not a missing-data fallback.
  | .bool | .float | .foreign | .str | .slice | .dynamicTraitObject | .coroutineWitness
  | .parameter | .boundType | .placeholderType | .inferenceType | .errorType => pure .other

def adt (runtime : RuntimeMetadata) (id : TypeId) : Result (Miri.Interpreter.LayoutCompat.AdtInfo TypeId) := do
  let (node,source) ← shape runtime id
  if node.shapeKind != .adt then throw (.unsupported "non-ADT compiler query")
  let kind ← match ← require node.shapeMetadata.adtKind "ADT kind" with
    | .structKind => pure Miri.Interpreter.LayoutCompat.AdtKind.Struct | .unionKind => pure .Union | .enumKind => pure .Enum
    | .unknown _ => throw (.unsupported "unknown ADT kind")
  let repr ← RuntimeMetadata.jsonField source "representation"
  if (← RuntimeMetadata.text repr "status") != "supported" then throw (.unsupported "ADT repr")
  let sourceVariants ← RuntimeMetadata.array source "variants"
  let mut variants := #[]
  for sourceVariant in sourceVariants do
    if (← RuntimeMetadata.number sourceVariant "index") != variants.size then
      throw (invalid "ADT variant" "noncontiguous indices")
    let mut fields := #[]
    for sourceField in ← RuntimeMetadata.array sourceVariant "fields" do
      if (← RuntimeMetadata.number sourceField "index") != fields.size then
        throw (invalid "ADT field" "noncontiguous indices")
      fields := fields.push ({
        name := ← RuntimeMetadata.text sourceField "name"
        ty := ← typeRef (← RuntimeMetadata.jsonField sourceField "type") } : Miri.Interpreter.LayoutCompat.Field TypeId)
    variants := variants.push fields
  return ⟨kind,← RuntimeMetadata.truth repr "transparent",← RuntimeMetadata.truth repr "c",
    ← RuntimeMetadata.truth repr "rust",variants⟩

private def unitLayout (runtime : RuntimeMetadata) : Result (TyAndLayout TypeId) := do
  let mut found := none
  for node in runtime.source.types do
    if node.shapeKind == .tuple then
      let (_,source) ← shape runtime node.id
      if (← RuntimeMetadata.array source "elements").isEmpty then
        if found.isSome then throw (invalid "unit type" "multiple compiler identities")
        found := some node.id
  runtime.lookup (← require found "compiler unit type")

set_option autoImplicit false in
/-- The strict unit query used by source ABI compatibility. Its result retains
the exact scan outcome, including duplicate and malformed metadata failures. -/
structure UnitLayoutCache (runtime : RuntimeMetadata) where
  private mk ::
  value : Result (TyAndLayout TypeId)
  exact : value = unitLayout runtime

def bindUnitLayout (runtime : RuntimeMetadata) : UnitLayoutCache runtime :=
  let value := unitLayout runtime
  ⟨value, rfl⟩

/-- Connect the source algorithm to canonical records while keeping every
missing compiler query explicit and preserving the caller's effect state. -/
def queries (runtime : RuntimeMetadata) (evidence : Evidence S)
    (unitCache : Option (UnitLayoutCache runtime) := none) :
    Miri.Interpreter.LayoutCompat.Queries TypeId S := {
  target := runtime.target
  kind := fun id => lift (kind runtime id)
  adt := fun id => lift (adt runtime id)
  field := fun parent index => lift (runtime.field parent index)
  layoutOf := fun id => lift (runtime.lookup id)
  unitLayout := lift (match unitCache with
    | some cached => cached.value
    | none => unitLayout runtime)
  eraseUnsafeBinder := evidence.eraseUnsafeBinder, normalize := evidence.normalize
  reprEqualUpToSeed := evidence.reprEqualUpToSeed, itemName := evidence.itemName
  nonnullOptimizationGuaranteed := evidence.nonnullOptimizationGuaranteed
  isGlobalBox := evidence.isGlobalBox, boxedType := evidence.boxedType
  pointerMetadataType := evidence.pointerMetadataType }

def checkArgumentCompat (runtime : RuntimeMetadata) (evidence : Evidence S) (fuel : Nat)
    (caller callee : AbiArgument) : Miri.Interpreter.LayoutCompat.M S Bool := do
  let caller ← lift (argument runtime caller)
  let callee ← lift (argument runtime callee)
  Miri.Interpreter.LayoutCompat.checkArgumentCompat (queries runtime evidence) fuel caller callee
end Miri.Input.CallCompatibility
