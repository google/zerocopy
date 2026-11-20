import Miri.Input.RuntimeMetadata

/-! Runtime canonical array constructors, including OsStr and argv arrays.
Sources: rustc_middle ty/sty.rs::Ty::new_array, rustc_type_ir sty/consts.rs
::from_target_usize, rustc_abi layout.rs::layout_of_array_like (182–207).
Runtime IDs are allocations in this explicit interner, never compiler IDs
borrowed by equal layout. Keep one World for the lifetime of an interpreter.
-/
namespace Miri.Input.RuntimeArrayTypes
open Lean Miri.ABI
inductive Element where
  | u8 | u16
  | compiler (id : TypeId)
  deriving DecidableEq, Repr
structure Key where
  element : Element
  count : UInt64
  deriving DecidableEq, Repr
inductive Origin where
  | compiler (id : TypeId)
  | runtimeConstructor
  deriving DecidableEq, Repr
structure Entry where
  key : Key
  value : TyAndLayout TypeId
  origin : Origin
structure World where
  metadata : RuntimeMetadata
  byteLayout : TyAndLayout TypeId
  wideLayout : TyAndLayout TypeId
  entries : Array Entry
  nextId : TypeId
  obligations : Array String
  aliases : Array (Key × TypeId) := #[]
inductive Error where
  | metadata (reason : String)
  | targetUsizeOverflow (count : UInt64)
  | sizeOverflow
  | conflictingCanonicalIdentity
  | compilerLayoutMismatch (id : TypeId)
  | missingRuntimeType (id : TypeId)
  | fieldOutOfBounds (index count : Nat)
  deriving DecidableEq, Repr
private def convert (result : Except String A) : Except Error A :=
  result.mapError Error.metadata
private def metadata (result : Except RuntimeMetadataError A) : Except Error A :=
  result.mapError (Error.metadata ∘ toString)

/-- Exact source layout calculator, including exclusive object-size bound,
first-element niche retention, alignment and wrapping randomization seed. -/
def calculate (target : RuntimeTargetDataLayout) (element : LayoutData)
    (count : UInt64) : Except Error LayoutData := do
  let some size := element.size.checkedMul count target.base | throw .sizeOverflow
  pure {
    variants := .Single 0
    fields := .Array element.size count
    backendRepr := .Memory (sized := true)
    largestNiche := if count != 0 then element.largestNiche else none
    uninhabited := element.uninhabited && count != 0
    align := element.align
    size
    maxReprAlign := none
    unadjustedAbiAlign := element.align.abi
    reprC := element.reprC
    randomizationSeed := element.randomizationSeed + count }
private def primitive (runtime : RuntimeMetadata) (refs : Json) (key : String)
    (kind : Miri.MIR.IntegerKind) : Except Error (TyAndLayout TypeId) := do
  let id ← convert ((refs.getObjVal? key).bind fun value => (value.getObjVal? "type_id").bind Json.getNat?)
  let source ← metadata (runtime.node id)
  unless source.shapeStatus == .supported && source.shapeMetadata.unsignedKind == some (.known kind) do
    throw (.metadata s!"runtime primitive {key} is not the exact compiler unsigned type")
  metadata (runtime.lookup id)
private def elementOfId (world : World) (id : TypeId) : Element :=
  if id == world.byteLayout.ty then .u8
  else if id == world.wideLayout.ty then .u16
  else .compiler id
private def elementLayout (world : World) : Element → Except Error (TyAndLayout TypeId)
  | .u8 => pure world.byteLayout
  | .u16 => pure world.wideLayout
  | .compiler id => do
    let element ← match world.entries.find? (·.value.ty == id) with
      | some entry => pure entry.value
      | none => metadata (world.metadata.lookup id)
    unless element.layout.isSized do throw (.metadata "source array element requires a sized type")
    pure element

/-- Seed exact constructor aliases before computing any layouts. Layout failures
in unrelated compiler catalog entries do not turn World creation into execution
of those types; requesting their constructors still fails explicitly. -/
def create (runtime : RuntimeMetadata) : Except Error World := do
  let refs ← convert (runtime.source.raw.getObjVal? "compiler_runtime_primitives")
  let byte ← primitive runtime refs "u8" .u8
  let wide ← primitive runtime refs "u16" .u16
  let next := runtime.source.types.foldl (fun next node => max next (node.id + 1)) 0
  let mut world : World := {
    metadata := runtime
    byteLayout := byte
    wideLayout := wide
    entries := #[]
    nextId := next
    obligations := #[] }
  for node in runtime.source.types do
    if node.shapeKind == .array then
      let shape ← convert (node.payload.getObjVal? "shape")
      let element ← convert ((shape.getObjVal? "element").bind fun value => (value.getObjVal? "type_id").bind Json.getNat?)
      let evidence := do
        let evidence ← shape.getObjVal? "constructor_identity"
        unless (← (← evidence.getObjVal? "status").getStr?) == "supported" do
          throw "unresolved compiler array constructor identity"
        unless (← (← evidence.getObjVal? "canonical_value_constructor").getBool?) do
          throw "source array is not the canonical value-length constructor"
        let count ← (← evidence.getObjVal? "count").getNat?
        unless count < 2^64 do throw "compiler array count exceeds u64"
        pure (UInt64.ofNat count)
      match evidence with
      | .error reason => world := {world with obligations := world.obligations.push s!"type {node.id}: {reason}"}
      | .ok count =>
        let key : Key := ⟨elementOfId world element,count⟩
        if let some (_,prior) := world.aliases.find? (·.1 == key) then
          unless prior == node.id do throw .conflictingCanonicalIdentity
        else world := {world with aliases := world.aliases.push (key,node.id)}
  -- Arrays may precede their element array in compiler ID order. This bounded
  -- dependency closure materializes only those with actual sized element data.
  for _ in [:world.aliases.size] do
    for (key,id) in world.aliases do
      unless world.entries.any (·.value.ty == id) do
        let computed := do calculate runtime.target (← elementLayout world key.element).layout key.count
        if let .ok computed := computed then
          if let .ok imported := runtime.lookup id then
            unless imported.layout == computed do throw (.compilerLayoutMismatch id)
          world := {world with entries := world.entries.push ⟨key,⟨id,computed⟩,.compiler id⟩}
  for (_,id) in world.aliases do
    unless world.entries.any (·.value.ty == id) do
      world := {world with obligations := world.obligations.push s!"type {id}: canonical array requires unresolved element layout or overflows target bound"}
  pure world

/-- Intern source Ty::new_array(compiler primitive, target-usize value).
The updated World is mandatory: dropping it drops the canonical identity map. -/
def intern (world : World) (element : Element) (count : UInt64) :
    Except Error (TyAndLayout TypeId × World) := do
  unless count.toNat < 2^(world.metadata.target.base.pointerWidth.bits.toNat) do
    throw (.targetUsizeOverflow count)
  let element := match element with
    | .compiler id => elementOfId world id
    | element => element
  let key : Key := ⟨element,count⟩
  if let some prior := world.entries.find? (·.key == key) then return (prior.value,world)
  let layout ← calculate world.metadata.target (← elementLayout world element).layout count
  let (id,origin,next) ← match world.aliases.find? (·.1 == key) with
    | some (_,id) => pure (id,Origin.compiler id,world.nextId)
    | none => do
      unless !(world.metadata.source.types.any (·.id == world.nextId)) &&
          !(world.entries.any (·.value.ty == world.nextId)) do throw .conflictingCanonicalIdentity
      pure (world.nextId,Origin.runtimeConstructor,world.nextId + 1)
  let result : TyAndLayout TypeId := ⟨id,layout⟩
  let updated := { world with
    entries := world.entries.push ⟨key,result,origin⟩
    nextId := next }
  pure (result,updated)

/-- General source array constructor for an actual compiler/runtime element ID.
No supplied layout establishes identity: lookup uses the canonical element ID. -/
def internElement (world : World) (element : TypeId) (count : UInt64) :
    Except Error (TyAndLayout TypeId × World) :=
  intern world (elementOfId world element) count

def osStringArray (world : World) (wide : Bool) (count : UInt64) :
    Except Error (TyAndLayout TypeId × World) :=
  intern world (if wide then .u16 else .u8) count

def lookup (world : World) (id : TypeId) : Except Error (TyAndLayout TypeId) := do
  if let some entry := world.entries.find? (·.value.ty == id) then return entry.value
  metadata (world.metadata.lookup id)

def arrayInfo (world : World) (id : TypeId) : Except Error (Key × TyAndLayout TypeId) := do
  let some entry := world.entries.find? (·.value.ty == id) | throw (.missingRuntimeType id)
  pure (entry.key,← elementLayout world entry.key.element)

def fieldLayout (world : World) (id index : Nat) : Except Error (TyAndLayout TypeId) := do
  let (key,element) ← arrayInfo world id
  unless index < key.count.toNat do throw (.fieldOutOfBounds index key.count.toNat)
  pure element
end Miri.Input.RuntimeArrayTypes
