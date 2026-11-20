import Miri.Input.EvalAllocationMachine
import Miri.Input.RuntimeArrayQueries

/-! Physical projection and canonical type/layout queries on the final World.
Source: interpret/{projection,operand,place}.rs and eval_context.rs. Pure
immediate views are snapshots; indirect/dynamic effects use PlaceDynamic. -/
namespace Miri.Input.EvalProjectionMachine
open Lean Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
abbrev User := EvalBackendMachine.User
abbrev State := EvalBackendMachine.State
private def query (value : Except String A) : Except ProjectionError A :=
  value.mapError ProjectionError.obligation
private def metadataResult (value : Except RuntimeMetadataError A) : Except ProjectionError A :=
  value.mapError fun error => match error with
    | .unsupported reason => .machineError (.unsupported s!"compiler runtime metadata: {reason}")
    | error => .obligation (toString error)
private def arrayResult (value : Except RuntimeArrayTypes.Error A) : Except ProjectionError A :=
  value.mapError (ProjectionError.obligation ∘ reprStr)
private def lift (value : Except ProjectionError A) : EStateM StepError S A :=
  match value with
  | .ok value => pure value
  | .error error => throw (IntrinsicVectorMachine.projectionError error)

def arrays : RuntimeArrayQueries.Access (State Os R P H D O Aff B Host) where
  get := fun s => s.machine.user.payload.payload.user.types
  set := fun s types => {s with machine := {s.machine with user := {s.machine.user with payload :=
    {s.machine.user.payload with payload := {s.machine.user.payload.payload with user :=
      {s.machine.user.payload.payload.user with types}}}}}}

private def shape (runtime : RuntimeMetadata) (ty : TyId) : Except ProjectionError TypeNode := do
  let node ← metadataResult (runtime.node ty)
  unless node.shapeStatus == .supported do throw (.obligation "compiler type shape unavailable")
  pure node

def packed (runtime : RuntimeMetadata) (ty : TyId) : Except ProjectionError (Option Align) := do
  let node ← shape runtime ty
  if node.shapeKind != .adt then return none
  let repr ← query ((node.payload.getObjVal? "shape").bind fun s => s.getObjVal? "representation")
  let status ← query ((repr.getObjVal? "status").bind Json.getStr?)
  unless status == "supported" do throw (.obligation "compiler repr packing unavailable")
  let pack ← query (repr.getObjVal? "pack_bytes")
  if pack == .null then return none
  let bytes ← query pack.getNat?
  if bytes >= 2^64 then throw (.invariant "compiler packing exceeds u64")
  let align ← Align.fromBytes (UInt64.ofNat bytes) |>.mapError ProjectionError.align
  pure (some align)

def field (world : RuntimeArrayTypes.World) (layout : LocalLayout) (index : Nat) :
    Except ProjectionError LocalLayout :=
  if world.entries.any (·.value.ty == layout.ty) then do
    let (_,element) ← arrayResult (RuntimeArrayTypes.arrayInfo world layout.ty)
    pure element
  else metadataResult (world.metadata.field layout index)

/-- Exact source ABI shape assertion, including provenance restriction on
non-pointer scalars. It does not validate initialized scalar values. -/
def assertAbi (target : RuntimeTargetDataLayout) (value : Immediate Provenance) (layout : LayoutData) :
    Except ProjectionError Unit := do
  let check := fun (value : Memory.Scalar Provenance) (abi : ABI.Scalar) => do
    let size ← abi.size target |>.mapError (fun e => ProjectionError.obligation (reprStr e))
    unless value.size == size do throw (.invariant "immediate scalar ABI size mismatch")
    match abi.primitive with
    | .Pointer _ => pure ()
    | _ => if value.isPointer then throw (.invariant "non-pointer ABI scalar carries provenance")
  match value,layout.backendRepr with
  | .scalar v,.Scalar abi => check v abi
  | .scalarPair a b,.ScalarPair (a := abiA) (b := abiB) => check a abiA; check b abiB
  | .uninit,abi => unless abi.isSized do throw (.invariant "unsized immediate")
  | _,_ => throw (.invariant "immediate does not match ABI")

/-- The source metadata guard and signed conversion precede resolution.
Zero offset and wrapping mode never consult the address/allocation maps. -/
def memoryOffset
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (ThreadStacks.Storage (EvalWorld.World Os R P H D O Aff B Host))))
    (snapshot : State Os R P H D O Aff B Host) (place : MemPlace Provenance)
    (offset : Size) (mode : OffsetMode) (metadata : MemPlaceMeta Provenance) :
    Except ProjectionError (MemPlace Provenance) := do
  if metadata.hasMeta && !place.metadata.hasMeta then throw (.offset .addedMetadataToThinPlace)
  let mut resolved := none
  if mode == .inbounds then
    if offset.bytes.toNat >= 2^63 then throw (.offset (.offsetDoesNotFitI64 offset))
    if offset != .ZERO then
      if let some provenance := place.ptr.provenance then
        let hooks : AllocAddresses.AddressLookupHooks := {
          sizeOf := fun id => (snapshot.machine.memory.getAllocInfo id).toOption.map (·.size)
          isLive := fun id => some (snapshot.machine.memory.isAllocLive id) }
        let result ← snapshot.machine.user.addresses.ptrGetAlloc (Pointer.new provenance place.ptr.offset)
          (Int64.ofInt offset.bytes.toNat) hooks pointers.arithmetic
          |>.mapError (ProjectionError.machineError ∘ pointers.classifyAddressError)
        resolved := result.map fun (id,amount) => (⟨id,amount,provenance⟩ : ResolvedPointer Provenance)
  let resolver : PointerResolver Provenance Provenance := fun ptr _ =>
    match resolved with | some r => .ok r | none => .error ptr.offset.bytes
  projectionMemoryOffset pointers.arithmetic resolver snapshot.machine.memory.getAllocInfo place offset mode metadata

private def subsliceKnown (world : RuntimeArrayTypes.World) (base : LocalLayout) (count : UInt64) :
    Except ProjectionError (LocalLayout × MemPlaceMeta Provenance) := do
  if world.entries.any (·.value.ty == base.ty) then
    let (_,element) ← arrayResult (RuntimeArrayTypes.arrayInfo world base.ty)
    let (layout,after) ← arrayResult (RuntimeArrayTypes.internElement world element.ty count)
    if after.nextId != world.nextId then throw (.obligation "subslice constructor requires effectful canonical interning")
    return (layout,.none)
  let node ← shape world.metadata base.ty
  match node.shapeKind with
  | .array =>
    let element ← field world base 0
    let (layout,after) ← arrayResult (RuntimeArrayTypes.internElement world element.ty count)
    if after.nextId != world.nextId then throw (.obligation "subslice constructor requires effectful canonical interning")
    pure (layout,.none)
  | .slice =>
    let scalar ← Memory.Scalar.fromUInt (BitVec.ofNat 128 count.toNat) world.metadata.target.pointerSize
      |>.mapError ProjectionError.scalar
    pure (base,.metadata scalar)
  | _ => throw (.invariant "subslice requires array or slice")

/-- Only immediate operations use this pure snapshot. Dynamic indirect fields,
MIR dereference/local index and constructor-allocating subslices have actual
stateful adapters; trying those effects here is an explicit obligation. -/
def context (prepared : CompilerFactAdapters.Prepared) (maxSizeOfVal : Size) (debug : Bool)
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (ThreadStacks.Storage (EvalWorld.World Os R P H D O Aff B Host))))
    (snapshot : State Os R P H D O Aff B Host) : ProjectionCx Provenance :=
  let world := arrays.get snapshot
  { target := prepared.context.runtime.target.base
    maxSizeOfVal := maxSizeOfVal
    isSliceOrStr := fun ty => do
      let node ← shape world.metadata ty
      pure (node.shapeKind == .slice || node.shapeKind == .str)
    field := field world
    variant := fun layout index => metadataResult (world.metadata.forVariant layout index)
    dynamicAlign := fun _ _ => .error (.obligation "dynamic alignment requires effectful projection")
    packedAlign := packed world.metadata
    immediateOffset := fun v source offset target => projectionImmediateOffset
      (assertAbi prepared.context.runtime.target) v source offset target debug
    memoryOffset := memoryOffset pointers snapshot
    subsliceLayout := subsliceKnown world
    layoutOf := fun ty => arrayResult (RuntimeArrayTypes.lookup world ty)
    deref := fun _ => .error (.obligation "typed dereference requires effectful projection")
    localIndex := fun _ => .error (.obligation "local index requires effectful local read") }

def dynamicKind (prepared : CompilerFactAdapters.Prepared) (ty : TyId) : Except ProjectionError DynamicTypeKind := do
  let node ← shape prepared.context.runtime ty
  match node.shapeKind with
  | .adt =>
    let simd ← query (((node.payload.getObjVal? "shape").bind fun s => s.getObjVal? "representation").bind
      fun r => (r.getObjVal? "simd").bind Json.getBool?)
    pure (.adt simd)
  | .tuple => pure (.tuple false)
  | .dynamicTraitObject =>
    let .dynamic expected ← query (CompilerFactAdapters.validityKind prepared ty)
      | throw (.invariant "dynamic type missing compiler predicates")
    pure (.dynamic expected)
  | .slice => pure .slice | .str => pure .str | .foreign => pure .foreign
  | _ => throw (.invariant "invalid unsized dynamic layout kind")

def dynamic (prepared : CompilerFactAdapters.Prepared)
    (base : DynamicLayoutHooks Provenance (State Os R P H D O Aff B Host) C) :=
  {base with
    target := prepared.context.runtime.target.base
    classify := fun _ ty => lift (dynamicKind prepared ty)
    field := fun _ layout index => do lift (field (arrays.get (← get)) layout index)
    packedAlign := fun _ ty => lift (packed prepared.context.runtime ty)}

/-- Array constructor effects occur after caller bounds/stride checks. Slice
metadata is converted with the actual target pointer width. -/
def subslice (base : LocalLayout) (count : UInt64) : EStateM StepError (State Os R P H D O Aff B Host)
    (LocalLayout × MemPlaceMeta Provenance) := do
  let world := arrays.get (← get)
  if world.entries.any (·.value.ty == base.ty) then
    let (_,element) ← lift (arrayResult (RuntimeArrayTypes.arrayInfo world base.ty))
    return (← RuntimeArrayQueries.arrayLayout arrays element.ty count,.none)
  let node ← lift (shape world.metadata base.ty)
  match node.shapeKind with
  | .array =>
    let element ← lift (field world base 0)
    return (← RuntimeArrayQueries.arrayLayout arrays element.ty count,.none)
  | .slice => lift (subsliceKnown world base count)
  | _ => throw (.invalidProgram "subslice requires array or slice")

def bindCompiler (prepared : CompilerFactAdapters.Prepared) (maxSizeOfVal : Size)
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (ThreadStacks.Storage (EvalWorld.World Os R P H D O Aff B Host))))
    (base : PlaceMachine.CompilerHooks MiriMemoryKind (User Os R P H D O Aff B Host) C) :=
  {base with
    projection := fun _ => do return context prepared maxSizeOfVal base.debugAssertions pointers (← get)
    memoryOffset := fun _ p offset mode metadata => do lift (memoryOffset pointers (← get) p offset mode metadata)
    debugAbiCheck := fun value layout =>
      if base.debugAssertions then lift (assertAbi prepared.context.runtime.target value layout.layout) else pure ()}

def bindProjection (prepared : CompilerFactAdapters.Prepared)
    (base : PlaceProjectionHooks Provenance (State Os R P H D O Aff B Host) C MachineHooks.FrameExtra) :
    PlaceProjectionHooks Provenance (State Os R P H D O Aff B Host) C MachineHooks.FrameExtra :=
  {base with
    target := prepared.context.runtime.target.base
    dynamic := dynamic prepared base.dynamic
    isSliceOrStr := fun _ ty => do
      let node ← lift (shape prepared.context.runtime ty)
      pure (node.shapeKind == .slice || node.shapeKind == .str)
    field := fun _ layout index => do lift (field (arrays.get (← get)) layout index)
    variant := fun _ layout index => lift (metadataResult (prepared.context.runtime.forVariant layout index))
    packedAlign := fun _ ty => lift (packed prepared.context.runtime ty)
    subsliceLayout := fun _ => subslice
    layoutOf := fun _ ty => RuntimeArrayQueries.layoutOf arrays ty}
end Miri.Input.EvalProjectionMachine
