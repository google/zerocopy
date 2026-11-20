import Miri.Interpreter.ScalarOps

/-! Pinned `interpret/discriminant.rs` pipelines. Field access, compiler queries
and CTFE pointer-nullability remain explicit effectful dependencies. -/
namespace Miri.Interpreter
open Miri.ABI Miri.Memory

structure DiscriminantHooks (Prov S C V : Type) where
  runtimeTarget : RuntimeTargetDataLayout
  discriminantLayout : C → MIR.TyId → RvalueM S (TyAndLayout MIR.TyId)
  tagLayout : C → ABI.Scalar → RvalueM S (TyAndLayout MIR.TyId)
  discriminantValue : C → MIR.TyId → Nat → RvalueM S (Option (MIR.TyId × U128))
  variantForDiscriminant : C → MIR.TyId → U128 → RvalueM S (Option Nat)
  adtVariantCount : C → MIR.TyId → RvalueM S Nat
  projectRead : C → OpTy Prov → Nat → RvalueM S (OpTy Prov)
  readImmediate : C → OpTy Prov → RvalueM S (RvalueImmTy Prov)
  destLayout : V → TyAndLayout MIR.TyId
  projectWrite : C → V → Nat → RvalueM S V
  writeScalar : C → Memory.Scalar Prov → V → RvalueM S Unit
  toOp : C → V → RvalueM S (OpTy Prov)
  scalarMayBeNull : C → Memory.Scalar Prov → RvalueM S Bool

namespace Discriminant
private def liftResult (value : Except StepError A) : RvalueM S A :=
  match value with | .ok v => pure v | .error e => throw e
private def invalid (reason : String) : RvalueM S A := throw (.invalidProgram reason)
private def ub (reason : String) : RvalueM S A := throw (.undefinedBehavior reason)
private def scalarOf (value : RvalueImmTy Prov) : RvalueM S (Memory.Scalar Prov) :=
  liftResult (value.imm.toScalar |>.mapError ScalarOps.immediateError)
private def sizeResult (value : Except SizeError A) : RvalueM S A :=
  liftResult (value.mapError (fun e => .invalidProgram (toString e)))
private def scalarBits [PointerProvenance Prov] (scalar : Memory.Scalar Prov) (size : Size) : RvalueM S U128 :=
  liftResult (scalar.toBits size |>.mapError ScalarOps.scalarError)
private def signed (layout : LayoutData) : RvalueM S Bool :=
  match layout.backendRepr.isSigned with
  | .ok value => pure value
  | .error _ => invalid "discriminant requires scalar backend representation"
private def tagSize (h : DiscriminantHooks P S C V) (tag : ABI.Scalar) : RvalueM S Size :=
  match tag.size h.runtimeTarget with
  | .ok value => pure value
  | .error e => invalid s!"tag scalar size: {repr e}"
private def validRange (h : DiscriminantHooks P S C V) (tag : ABI.Scalar) : RvalueM S WrappingRange :=
  match tag.validRange h.runtimeTarget with
  | .ok value => pure value
  | .error e => invalid s!"tag scalar range: {repr e}"

/-- User-visible discriminants differ from both tag bits and declaration indices.
Types without compiler discriminants have only discriminant/index zero. -/
def discriminantForVariant (h : DiscriminantHooks P S C V) (choice : C)
    (ty : MIR.TyId) (variant : Nat) : RvalueM S (RvalueImmTy P) := do
  let layout ← h.discriminantLayout choice ty
  let value ← match ← h.discriminantValue choice ty variant with
    | some (discrTy, bits) => do
      if discrTy != layout.ty then invalid "discriminant type disagrees with layout"
      pure bits
    | none => do
      if variant != 0 then invalid "non-enum discriminant variant must be zero"
      pure (0 : U128)
  let scalar ← liftResult (Memory.Scalar.fromUInt (Prov := P) value layout.layout.size |>.mapError ScalarOps.scalarError)
  return ⟨.scalar scalar, layout⟩

/-- Source tag_for_variant: uninhabited variants fail before all tag queries. -/
def tagForVariant [PointerProvenance P] (h : DiscriminantHooks P S C V) (choice : C)
    (layout : TyAndLayout MIR.TyId) (variant : Nat) : RvalueM S (Option (ScalarInt × Nat)) := do
  if layout.layout.isVariantUninhabited variant then ub s!"UninhabitedEnumVariantWritten({variant})"
  match layout.layout.variants with
  | .Empty => invalid "inhabited empty layout"
  | .Single _ => pure none
  | .Multiple tag .Direct field _ =>
    let discr ← discriminantForVariant h choice layout.ty variant
    let bits ← scalarBits (← scalarOf discr) discr.layout.layout.size
    let size ← tagSize h tag
    let bits ← sizeResult (size.truncate bits)
    let scalar ← liftResult (Memory.Scalar.fromUInt (Prov := P) bits size |>.mapError ScalarOps.scalarError)
    let scalar ← liftResult (scalar.toScalarInt |>.mapError ScalarOps.scalarError)
    pure (some (scalar, field))
  | .Multiple tag (.Niche untagged start last nicheStart) field _ =>
    if variant == untagged then return none
    if variant < start || variant > last then invalid "variant outside niche range"
    if variant >= 2^32 || start >= 2^32 || last >= 2^32 then invalid "variant index exceeds u32"
    let tagLayout ← h.tagLayout choice tag
    let size := tagLayout.layout.size
    -- Source constructs both operands at tag width before its wrapping Add.
    let _ ← liftResult (Memory.Scalar.fromUInt (Prov := P) nicheStart size |>.mapError ScalarOps.scalarError)
    let relative := BitVec.ofNat 128 (variant - start)
    let _ ← liftResult (Memory.Scalar.fromUInt (Prov := P) relative size |>.mapError ScalarOps.scalarError)
    let bits ← sizeResult (size.truncate (relative + nicheStart))
    let scalar ← liftResult (Memory.Scalar.fromUInt (Prov := P) bits size |>.mapError ScalarOps.scalarError)
    let scalar ← liftResult (scalar.toScalarInt |>.mapError ScalarOps.scalarError)
    return some (scalar, field)

/-- Read the discriminant without assuming that an enum's wrapping range is a
complete set of declared tags. Pointer niches retain the CTFE nullability hook. -/
def readDiscriminant [PointerProvenance P] (h : DiscriminantHooks P S C V) (choice : C)
    (op : OpTy P) : RvalueM S Nat := do
  let discrLayout ← h.discriminantLayout choice op.layout.ty
  match op.layout.layout.variants with
  | .Empty => ub "UninhabitedEnumVariantRead(None)"
  | .Single index =>
    if op.layout.layout.isUninhabited then ub s!"UninhabitedEnumVariantRead({index})"
    pure index
  | .Multiple tag encoding field _ =>
    let tagLayout ← h.tagLayout choice tag
    let tagOp ← h.projectRead choice op field
    let tagValue ← h.readImmediate choice tagOp
    if tagLayout.layout.size != tagValue.layout.layout.size then invalid "tag field size mismatch"
    let tagSigned ← signed tagLayout.layout
    let valueSigned ← signed tagValue.layout.layout
    if tagSigned != valueSigned then invalid "tag field signedness mismatch"
    let index ← match encoding with
      | .Direct => do
        let scalar ← scalarOf tagValue
        let integer ← liftResult (scalar.tryToScalarInt |>.mapError ScalarOps.scalarError)
        let .integer bits := integer | ub "InvalidTag(pointer)"
        let bits ← liftResult (bits.toBits tagLayout.layout.size |>.mapError ScalarOps.scalarIntError)
        let range ← validRange h tag
        if !range.contains bits then ub "InvalidTag(outside valid range)"
        -- int_to_int_or_float preserves signed extension before target truncation.
        let extended ← if tagSigned then do
          let integer ← sizeResult (tagLayout.layout.size.signExtend bits)
          pure (BitVec.ofInt 128 integer)
          else pure bits
        let discrBits ← sizeResult (discrLayout.layout.size.truncate extended)
        let some index ← h.variantForDiscriminant choice op.layout.ty discrBits
          | ub "InvalidTag(no declared discriminant)"
        pure index
      | .Niche untagged start last nicheStart => do
        if start >= 2^32 || last >= 2^32 || last < start then invalid "invalid niche variant range"
        let scalar ← scalarOf tagValue
        let integer ← liftResult (scalar.tryToScalarInt |>.mapError ScalarOps.scalarError)
        match integer with
        | .erasedPointer .. =>
          let ptrValid ← if nicheStart == 0 && start == last then do
            pure (!(← h.scalarMayBeNull choice scalar))
            else pure false
          if !ptrValid then ub "InvalidTag(pointer niche)"
          pure untagged
        | .integer integer =>
          let bits ← liftResult (integer.toBits tagLayout.layout.size |>.mapError ScalarOps.scalarIntError)
          let _ ← liftResult (Memory.Scalar.fromUInt (Prov := P) nicheStart tagLayout.layout.size |>.mapError ScalarOps.scalarError)
          let relative ← sizeResult (tagLayout.layout.size.truncate (bits - nicheStart))
          if relative.toNat <= last - start then do
            let index := start + relative.toNat
            if index >= 2^32 then invalid "absolute niche variant index overflow"
            let count ← h.adtVariantCount choice op.layout.ty
            if index >= count then invalid "niche variant outside ADT variant list"
            let range ← validRange h tag
            if !range.contains bits then invalid "niche encoding violates tag valid range"
            if index == untagged then ub "InvalidTag(untagged variant encoded in niche)"
            pure index
          else do
            let range ← validRange h tag
            if !range.contains bits then ub "InvalidTag(outside valid range)"
            pure untagged
    if op.layout.layout.isVariantUninhabited index then ub s!"UninhabitedEnumVariantRead({index})"
    pure index

def writeDiscriminant [PointerProvenance P] (h : DiscriminantHooks P S C V) (choice : C)
    (variant : Nat) (dest : V) : RvalueM S Unit := do
  match ← tagForVariant h choice (h.destLayout dest) variant with
  | some (tag, field) =>
    let tagDest ← h.projectWrite choice dest field
    h.writeScalar choice (.fromScalarInt tag) tagDest
  | none =>
    let op ← h.toOp choice dest
    let actual ← readDiscriminant h choice op
    if actual != variant then ub "InvalidNichedEnumVariantWritten"

end Discriminant
end Miri.Interpreter
