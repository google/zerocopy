import Miri.Input.RuntimeMetadata

/-! Actual compiler-selected primitive/lang-item/path types. Canonical source
query references establish identity; display spelling or layout equality does
not. In particular Ordering is tcx.ty_ordering_enum, and c_ulong is the source
core::ffi path query, never derived from host or target triple. -/
namespace Miri.Input.CompilerPrimitiveFacts
open Lean Miri.ABI
private def referencedLayout (runtime : RuntimeMetadata) (j : Json) :
    Except String (TyAndLayout TypeId) := do
  let id ← (← j.getObjVal? "type_id").getNat?
  runtime.lookup id |>.mapError toString
private def primitives (runtime : RuntimeMetadata) : Except String Json :=
  runtime.source.raw.getObjVal? "compiler_runtime_primitives"
private def supportedValue (j : Json) : Except String Json := do
  unless (← (← j.getObjVal? "status").getStr?) == "supported" do
    throw s!"compiler type query unavailable: {((j.getObjVal? "reason").bind Json.getStr?).toOption}"
  j.getObjVal? "value"

/-- Read one exact compiler primitive query key; no type-name search occurs. -/
def primitiveLayout (runtime : RuntimeMetadata) (key : String) : Except String (TyAndLayout TypeId) := do
  referencedLayout runtime (← (← primitives runtime).getObjVal? key)

/-- Exact primitive type references and layouts prepared for repeated hooks.
Every entry retains its source-local failure instead of making preparation
fail for an unused primitive. The index is tied to one complete immutable
runtime value by `Bound` below. -/
structure Cache where
  private mk ::
  primitiveLayouts : Std.HashMap String (Except String (TyAndLayout TypeId))
  ordering : Except String (TyAndLayout TypeId)
  callerLocation : Except String TypeId

private def buildCache (runtime : RuntimeMetadata) : Cache := Id.run do
  let mut layouts : Std.HashMap TypeId (Except RuntimeMetadataError (TyAndLayout TypeId)) := {}
  for (id,value) in runtime.layouts do
    if !layouts.contains id then layouts := layouts.insert id value
  let mut nodes : Std.HashMap TypeId TypeNode := {}
  for node in runtime.source.types do
    if !nodes.contains node.id then nodes := nodes.insert node.id node
  let resolveLayout := fun (j : Json) => do
    let id ← (← j.getObjVal? "type_id").getNat?
    match layouts[id]? with
    | some result => result.mapError toString
    | none => runtime.lookup id |>.mapError toString
  let mut values : Std.HashMap String (Except String (TyAndLayout TypeId)) := {}
  if let .ok (.obj entries) := primitives runtime then
    for (key,value) in entries.toList do
      values := values.insert key (resolveLayout value)
  let ordering := do
    resolveLayout (← supportedValue (← (← primitives runtime).getObjVal? "ordering_enum"))
  let callerLocation := do
    let value ← supportedValue (← (← primitives runtime).getObjVal? "caller_location_type")
    let id ← (← value.getObjVal? "type_id").getNat?
    unless nodes.contains id do
      let _ ← runtime.node id |>.mapError toString
    pure id
  return ⟨values,ordering,callerLocation⟩

set_option autoImplicit false in
/-- A prepared primitive table carries an equality certificate to the exact
cache derived from the indexed runtime. A record update to another runtime
cannot reuse this certificate. -/
structure Bound (runtime : RuntimeMetadata) where
  private mk ::
  value : Cache
  exact : value = buildCache runtime

def bind (runtime : RuntimeMetadata) : Bound runtime :=
  let value := buildCache runtime
  ⟨value, rfl⟩

/-- Use cached query outcomes when the requested key was in the source catalog;
malformed or absent catalogs keep the original demand-time behavior. -/
def primitiveLayoutBound (runtime : RuntimeMetadata) (cache : Bound runtime)
    (key : String) : Except String (TyAndLayout TypeId) :=
  match cache.value.primitiveLayouts[key]? with
  | some result => result
  | none => primitiveLayout runtime key

def orderingLayoutBound (runtime : RuntimeMetadata) (cache : Bound runtime) :
    Except String (TyAndLayout TypeId) := cache.value.ordering

def callerLocationTypeBound (runtime : RuntimeMetadata) (cache : Bound runtime) :
    Except String TypeId := cache.value.callerLocation

def u32LayoutBound (runtime : RuntimeMetadata) (cache : Bound runtime) :
    Except String (TyAndLayout TypeId) := primitiveLayoutBound runtime cache "u32"

def usizeLayoutBound (runtime : RuntimeMetadata) (cache : Bound runtime) :
    Except String (TyAndLayout TypeId) := primitiveLayoutBound runtime cache "usize"

def unitLayoutBound (runtime : RuntimeMetadata) (cache : Bound runtime) :
    Except String (TyAndLayout TypeId) := primitiveLayoutBound runtime cache "unit"

def unitPointerConstLayoutBound (runtime : RuntimeMetadata) (cache : Bound runtime) :
    Except String (TyAndLayout TypeId) := primitiveLayoutBound runtime cache "unit_pointer_const"

def unitPointerMutLayoutBound (runtime : RuntimeMetadata) (cache : Bound runtime) :
    Except String (TyAndLayout TypeId) := primitiveLayoutBound runtime cache "unit_pointer_mut"

/-- Read one exact source path/constructor query key from the named catalog. -/
def namedLayout (runtime : RuntimeMetadata) (key : String) : Except String (TyAndLayout TypeId) := do
  let entries ← runtime.source.raw.getObjVal? "compiler_named_types"
  referencedLayout runtime (← supportedValue (← entries.getObjVal? key))

def orderingLayout (runtime : RuntimeMetadata) : Except String (TyAndLayout TypeId) := do
  referencedLayout runtime (← supportedValue (← (← primitives runtime).getObjVal? "ordering_enum"))

/-- Exact tcx.caller_location_ty(): &'static Location<'static>, preserving
both source reference/lifetime construction and canonical compiler identity. -/
def callerLocationType (runtime : RuntimeMetadata) : Except String TypeId := do
  let value ← supportedValue (← (← primitives runtime).getObjVal? "caller_location_type")
  let id ← (← value.getObjVal? "type_id").getNat?
  let _ ← runtime.node id |>.mapError toString
  pure id

def cULongLayout (runtime : RuntimeMetadata) : Except String (TyAndLayout TypeId) := do
  let entries ← runtime.source.raw.getObjVal? "compiler_named_types"
  referencedLayout runtime (← supportedValue (← entries.getObjVal? "c_ulong"))

def offTLayout (runtime : RuntimeMetadata) : Except String (TyAndLayout TypeId) := do
  let entries ← runtime.source.raw.getObjVal? "compiler_named_types"
  referencedLayout runtime (← supportedValue (← entries.getObjVal? "off_t"))

def u32Layout (runtime : RuntimeMetadata) : Except String (TyAndLayout TypeId) := do
  referencedLayout runtime (← (← primitives runtime).getObjVal? "u32")

def usizeLayout (runtime : RuntimeMetadata) : Except String (TyAndLayout TypeId) := do
  referencedLayout runtime (← (← primitives runtime).getObjVal? "usize")

def unitLayout (runtime : RuntimeMetadata) : Except String (TyAndLayout TypeId) := do
  referencedLayout runtime (← (← primitives runtime).getObjVal? "unit")

def unitPointerConstLayout (runtime : RuntimeMetadata) : Except String (TyAndLayout TypeId) := do
  referencedLayout runtime (← (← primitives runtime).getObjVal? "unit_pointer_const")

def unitPointerMutLayout (runtime : RuntimeMetadata) : Except String (TyAndLayout TypeId) := do
  referencedLayout runtime (← (← primitives runtime).getObjVal? "unit_pointer_mut")
end Miri.Input.CompilerPrimitiveFacts
