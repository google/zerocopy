import Miri.Interpreter.Place
import Miri.Interpreter.DynamicLayout

/-! Effectful Projectable rules for canonical places. Dynamic field alignment
can execute vtable/compiler/machine queries; those effects are threaded through
the same interpreter state rather than converted into pure ProjectionCx fields.
Source: projection.rs project_field/index/subslice/downcast; place.rs Projectable.
-/
namespace Miri.Interpreter
open Miri.ABI Miri.Memory

structure PlaceProjectionHooks (P S C E : Type) where
  place : PlaceHooks P S C E
  target : TargetDataLayout
  maxSizeOfVal : Size
  dynamic : DynamicLayoutHooks P S C
  dynamicFuel : Nat
  isSliceOrStr : C → MIR.TyId → PlaceM S Bool
  field : C → LocalLayout → Nat → PlaceM S LocalLayout
  variant : C → LocalLayout → Nat → PlaceM S LocalLayout
  packedAlign : C → MIR.TyId → PlaceM S (Option Align)
  subsliceLayout : C → LocalLayout → UInt64 → PlaceM S (LocalLayout × MemPlaceMeta P)
  layoutOf : C → MIR.TyId → PlaceM S LocalLayout
  localIndex : C → MIR.LocalId → PlaceM S UInt64

namespace PlaceDynamic
private def liftResult (value : Except StepError A) : PlaceM S A :=
  match value with | .ok value => pure value | .error error => throw error
private def layoutResult (value : Except LayoutError A) : PlaceM S A :=
  liftResult (value.mapError fun error => .invalidProgram s!"place layout: {repr error}")
private def sizeResult (value : Except SizeError A) : PlaceM S A :=
  liftResult (value.mapError fun error => .invalidProgram s!"place size: {repr error}")

private def metadata (place : RuntimePlace P) : MemPlaceMeta P :=
  match place.ref with | .local .. => .none | .memory mplace => mplace.metadata

/-- Source PlaceTy::offset_with_meta, with actual effectful memory offset and
checked local offset. Local places cannot carry metadata or unsized layouts. -/
def offsetWithMeta (h : PlaceProjectionHooks P S C E) (choice : C)
    (base : RuntimePlace P) (amount : Size) (mode : OffsetMode)
    (metaValue : MemPlaceMeta P) (layout : LocalLayout) : PlaceM S (RuntimePlace P) := do
  match base.ref with
  | .memory mplace => return ⟨.memory (← h.place.memoryOffset choice mplace amount mode metaValue), layout⟩
  | .local frame localId oldOffset identity =>
    if !layout.layout.isSized || metaValue.hasMeta then
      throw (.invalidProgram "local projection cannot store metadata or unsized layout")
    let bound ← sizeResult (amount.add layout.layout.size)
    if bound.bytes > base.layout.layout.size.bytes then throw (.invalidProgram "local projection exceeds enclosing place")
    let offset ← sizeResult ((oldOffset.getD Size.ZERO).add amount)
    return ⟨.local frame localId (some offset) identity, layout⟩

private def sizedOffset (h : PlaceProjectionHooks P S C E) (choice : C)
    (base : RuntimePlace P) (amount : Size) (layout : LocalLayout) : PlaceM S (RuntimePlace P) := do
  if !layout.layout.isSized then throw (.invalidProgram "sized offset requires sized output")
  offsetWithMeta h choice base amount .inbounds .none layout

def length [PointerProvenance P] (h : PlaceProjectionHooks P S C E) (choice : C)
    (base : RuntimePlace P) : PlaceM S UInt64 := do
  if !base.layout.layout.isSized then
    unless ← h.isSliceOrStr choice base.layout.ty do throw (.invalidProgram "length of unsized non-slice")
    let scalar ← liftResult ((metadata base).unwrapMeta.mapError fun e => .invalidProgram (reprStr e))
    liftResult ((scalar.toTargetUsize (Size.fromBits h.target.pointerWidth.bits)).mapError ScalarOps.scalarError)
  else
    match base.layout.layout.fields with
    | .Array _ count => return count
    | _ => throw (.invalidProgram "length of non-array")

def field [PointerProvenance P] (h : PlaceProjectionHooks P S C E) (choice : C)
    (base : RuntimePlace P) (index : Nat) : PlaceM S (RuntimePlace P) := do
  let offset ← layoutResult (base.layout.layout.fields.offset index)
  let layout ← h.field choice base.layout index
  let (metaValue, offset) ← if !layout.layout.isSized then do
      if base.layout.layout.isSized then throw (.invalidProgram "unsized field in sized parent")
      let metaValue := metadata base
      match ← DynamicLayout.alignmentFromMeta h.dynamic choice h.dynamicFuel metaValue layout with
      | some align =>
        let packed ← h.packedAlign choice base.layout.ty
        let align := match packed with | some packed => align.min packed | none => align
        let offset ← liftResult ((offset.alignTo align).mapError fun error => .invalidProgram (toString error))
        pure (metaValue, offset)
      | none =>
        if offset != Size.ZERO then throw (.unsupported "ExternTypeField")
        pure (metaValue, offset)
    else pure (.none, offset)
  offsetWithMeta h choice base offset .inbounds metaValue layout

def downcast (h : PlaceProjectionHooks P S C E) (choice : C) (base : RuntimePlace P)
    (variant : Nat) : PlaceM S (RuntimePlace P) := do
  if (metadata base).hasMeta then throw (.invalidProgram "downcast requires thin place")
  let layout ← h.variant choice base.layout variant
  sizedOffset h choice base .ZERO layout

def index [PointerProvenance P] (h : PlaceProjectionHooks P S C E) (choice : C)
    (base : RuntimePlace P) (index : UInt64) : PlaceM S (RuntimePlace P) := do
  match base.layout.layout.fields with
  | .Array stride _ =>
    let len ← length h choice base
    if index >= len then throw (.undefinedBehavior s!"place index {index} out of bounds for {len}")
    let some offset := IntegerOps.computeSizeInBytes stride index h.maxSizeOfVal
      | throw (.undefinedBehavior "PointerArithOverflow")
    let layout ← h.field choice base.layout 0
    sizedOffset h choice base offset layout
  | _ => throw (.invalidProgram "index on non-array")

def constantIndex [PointerProvenance P] (h : PlaceProjectionHooks P S C E) (choice : C)
    (base : RuntimePlace P) (offset minLength : UInt64) (fromEnd : Bool) : PlaceM S (RuntimePlace P) := do
  let len ← length h choice base
  if len < minLength then throw (.undefinedBehavior "constant index minimum length")
  let idx ← if fromEnd then do
      if offset == 0 || offset > minLength then throw (.invalidProgram "invalid from-end constant index")
      pure (len - offset)
    else do
      if offset >= minLength then throw (.invalidProgram "invalid constant index")
      pure offset
  index h choice base idx

def subslice [PointerProvenance P] (h : PlaceProjectionHooks P S C E) (choice : C)
    (base : RuntimePlace P) (fromIndex to : UInt64) (fromEnd : Bool) : PlaceM S (RuntimePlace P) := do
  let len ← length h choice base
  let actualTo ← if fromEnd then do
      let sum := fromIndex.toNat + to.toNat
      if sum >= 2^64 || sum > len.toNat then throw (.undefinedBehavior "subslice bounds")
      pure (len - to)
    else pure to
  let offset ← match base.layout.layout.fields with
    | .Array stride _ => sizeResult (stride.mul fromIndex)
    | _ => throw (.invalidProgram "subslice on non-array")
  if actualTo < fromIndex then throw (.invalidProgram "subslice length underflow")
  let (layout, metaValue) ← h.subsliceLayout choice base.layout (actualTo - fromIndex)
  offsetWithMeta h choice base offset .inbounds metaValue layout

def project [PointerProvenance P] (h : PlaceProjectionHooks P S C E) (choice : C)
    (base : RuntimePlace P) (elem : MIR.ProjectionElem) : PlaceM S (RuntimePlace P) := do
  match elem with
  | .Field i _ => field h choice base i
  | .Downcast _ variant => downcast h choice base variant
  | .Deref => h.place.deref choice base false
  | .Index localId => index h choice base (← h.localIndex choice localId)
  | .UnwrapUnsafeBinder ty =>
    let layout ← h.layoutOf choice ty
    if !base.layout.layout.isSized || !layout.layout.isSized || base.layout.layout.size != layout.layout.size then
      throw (.invalidProgram "transmute requires equally sized layouts")
    offsetWithMeta h choice base .ZERO .wrapping .none layout
  | .ConstantIndex offset minimum fromEnd =>
    if offset >= 2^64 || minimum >= 2^64 then throw (.invalidProgram "MIR index exceeds u64")
    constantIndex h choice base (UInt64.ofNat offset) (UInt64.ofNat minimum) fromEnd
  | .Subslice fromIndex to fromEnd =>
    if fromIndex >= 2^64 || to >= 2^64 then throw (.invalidProgram "MIR subslice exceeds u64")
    subslice h choice base (UInt64.ofNat fromIndex) (UInt64.ofNat to) fromEnd
  | .OpaqueCast _ => throw (.invalidProgram "OpaqueCast after borrowck")
  | .PhantomDeref => throw (.invalidProgram "PhantomDeref after borrowck")

def evalPlace [PointerProvenance P] (h : PlaceProjectionHooks P S C E) (choice : C)
    (mirPlace : MIR.Place) (skipValidityForSimpleDeref : Bool) : PlaceM S (RuntimePlace P) := do
  let mut place ← localToPlace h.place choice mirPlace.localId
  if skipValidityForSimpleDeref && mirPlace.projection == #[.Deref] then
    return ← h.place.deref choice place true
  for elem in mirPlace.projection do place ← project h choice place elem
  h.place.checkPlaceType choice mirPlace place
  return place

/-- Whole-state dynamic layout adapter for the concrete Place slow-copy path. -/
def memoryCopy [DecidableEq Kind] [PointerProvenance P]
    (dynamic : DynamicLayoutHooks P S C) (choice : C) (fuel : Nat)
    (debugAssertions : Bool) (pointerSize : Size)
    (hooks : MemoryCopyHooks P Extra Kind HookState ProvExtra)
    (getMemory : S → MemoryState P Extra Kind) (getHooks : S → HookState)
    (putMemoryHooks : S → MemoryState P Extra Kind → HookState → S)
    (source dest : MPlaceTy P) : PlaceM S Unit :=
  placeMemoryCopy debugAssertions pointerSize
    (fun place => DynamicLayout.sizeAndAlignFromMeta dynamic choice fuel place.mplace.metadata place.layout)
    hooks getMemory getHooks putMemoryHooks source dest

/-- Dynamic mutable-place access runs effectful metadata layout first, then
uses the resolved size as an operational ABI view for existing allocation
access. Full type identity remains in the input; Foreign uses the source's
fixed-size fallback. The canonical state and touched snapshots are committed
before any allocation/access error is propagated. -/
def mutableAccess [DecidableEq Kind] [DecidableEq P] [PointerProvenance P]
    (dynamic : DynamicLayoutHooks P S C) (choice : C) (fuel : Nat)
    (context : LocalReadContext P Extra Kind HookState ProvExtra)
    (getMemory : S → MemoryState P Extra Kind) (getHooks : S → HookState)
    (putMemoryHooks : S → MemoryState P Extra Kind → HookState → S)
    (putTouched : S → Option (AllocationAccessRef P Extra) → S)
    (place : MPlaceTy P) : PlaceM S Unit := do
  let dynamicLayout ← DynamicLayout.sizeAndAlignFromMeta dynamic choice fuel place.mplace.metadata place.layout
  let (size, align) := dynamicLayout.getD (place.layout.layout.size, place.layout.layout.align.abi)
  let view : MemoryOperandPlace P := ⟨place.mplace, ⟨size, align, .Memory (sized := true),some place.layout.ty⟩⟩
  let state ← get
  let result := getPlaceAllocMut (getMemory state) (getHooks state) view context.runtime context.ghostMode
    context.globalKind context.globalHooks context.accessHooks context.dynamicLayout
  set (putTouched (putMemoryHooks state result.memory result.hooks) result.touched)
  match result.outcome with
  | .error error => throw (.callback s!"dynamic mutable place access: {repr error}")
  | .ok _ => pure ()

/-- Bind symbolic vtable checking and compiler layout lookup to dynamic trait
size/alignment queries; predicate and global-resolution effects stay in S. -/
def withVTable (dynamic : DynamicLayoutHooks P S C) (vtable : VTableHooks P S C F A) :
    DynamicLayoutHooks P S C :=
  { dynamic with vtableSizeAndAlign := VTable.getSizeAndAlign vtable }

end PlaceDynamic
end Miri.Interpreter
