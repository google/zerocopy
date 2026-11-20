import Miri.Interpreter.IntegerCast
import Miri.Interpreter.FloatOps
import Miri.Interpreter.VTable
import Miri.Interpreter.Place

/-! Connected pinned `interpret/cast.rs` dispatcher and recursive unsizing.
Compiler-owned type descriptions are metadata queries, not a program IR.
Machine provenance, memory access/copy and compiler resolution are explicit
stateful leaves; none is replaced by successful approximation. -/
namespace Miri.Interpreter
open Miri.ABI Miri.Memory Miri.MIR

inductive CastTypeInfo where
  | integer (kind : IntegerKind)
  | floating (format : FloatFormat)
  | boolean | character
  | rawPointer (pointee : TyId)
  | reference (pointee : TyId)
  | fnPointer
  | fnDefinition (definition : DefId) (args : Array GenericArg)
  | closure (definition : DefId) (args : Array GenericArg) (upvarCount : Nat)
  | pattern (inner : TyId) (patternId : Nat)
  | adt (definition : DefId)
  | array (element : TyId) (length : UInt64)
  | slice (element : TyId)
  | dynamic (predicates : Nat)
  deriving DecidableEq, Repr

structure CastHooks (P S C V : Type) where
  target : TargetDataLayout
  typeInfo : C → TyId → RvalueM S CastTypeInfo
  layoutOf : C → TyId → RvalueM S (TyAndLayout TyId)
  destLayout : V → TyAndLayout TyId
  readImmediate : C → OpTy P → RvalueM S (RvalueImmTy P)
  writeImmediate : C → Immediate P → V → RvalueM S Unit
  writePointer : C → Pointer (Option P) → V → RvalueM S Unit
  enforceValidity : C → TyAndLayout TyId → RvalueM S Bool
  enforceValidityRecursively : C → TyAndLayout TyId → RvalueM S Bool
  validatePlace : C → V → Bool → Bool → RvalueM S Unit
  derefPointer : C → OpTy P → RvalueM S Unit
  checkFunctionPointer : C → Pointer (Option P) → RvalueM S Unit
  exposeProvenance : C → P → RvalueM S Unit
  pointerFromExposedAddress : C → UInt64 → RvalueM S (Pointer (Option P))
  usizeLayout : C → RvalueM S (TyAndLayout TyId)
  floatOps : FloatOpsHooks P S C
  ensureMonomorphic : C → TyId → RvalueM S Unit
  requireNoBoundVars : C → Array GenericArg → RvalueM S Unit
  resolveFunction : C → DefId → Array GenericArg → RvalueM S (Option CallInstance)
  resolveClosureFnOnce : C → DefId → Array GenericArg → RvalueM S CallInstance
  functionPointer : C → CallInstance → RvalueM S (Pointer (Option P))
  builtinDeref : C → TyId → Bool → RvalueM S (Option TyId)
  boxLayout : C → TyId → RvalueM S (TyAndLayout TyId)
  validateImmediateABI : Immediate P → LayoutData → Except StepError Unit
  copyAllowTransmute : C → OpTy P → V → RvalueM S Unit
  copyNoValidate : C → OpTy P → V → Bool → RvalueM S Unit
  projectRead : C → OpTy P → Nat → RvalueM S (OpTy P)
  projectWrite : C → V → Nat → RvalueM S V
  fieldLayout : C → TyAndLayout TyId → Nat → RvalueM S (TyAndLayout TyId)
  lockstepTails : C → TyId → TyId → RvalueM S (TyId × TyId)
  vtableType : C → Pointer (Option P) → Option Nat → RvalueM S TyId
  vtablePointer : C → TyId → Nat → RvalueM S (Pointer (Option P))
  principal : C → Nat → RvalueM S (Option Nat)
  vtableEntries : C → Option Nat → TyId → RvalueM S (Array (VTableEntry CallInstance))
  supertraitSlot : C → TyId → TyId → RvalueM S (Option Nat)
  eraseSelfTraitRef : C → Nat → RvalueM S Nat
  normalizePrincipal : C → Nat → RvalueM S (Option Nat)

namespace Cast
private def invalid (message : String) : RvalueM S A := throw (.invalidProgram message)
private def liftResult (result : Except StepError A) : RvalueM S A :=
  match result with | .ok value => pure value | .error error => throw error
private def scalarOf (value : RvalueImmTy P) : RvalueM S (Memory.Scalar P) :=
  liftResult (value.imm.toScalar |>.mapError ScalarOps.immediateError)
private def readPointer [PointerProvenance P] (h : CastHooks P S C V) (choice : C)
    (op : OpTy P) : RvalueM S (Pointer (Option P)) := do
  let value ← h.readImmediate choice op
  let scalar ← scalarOf value
  liftResult (scalar.toPointer h.target |>.mapError ScalarOps.scalarError)
private def integerCastError : IntegerCastError → StepError
  | .scalar e => ScalarOps.scalarIntError e
  | .integerToCharTryFromPanicked _ => .invalidProgram "integer-to-char requires a u8 value"
private def isAnyPointer : CastTypeInfo → Bool
  | .rawPointer _ | .reference _ | .fnPointer => true | _ => false

/-- Source cast_from_int_like's u128 intermediate, after typed validity
conversion. Pointer inputs use the existing provenance-aware Scalar conversion;
no pointer address approximation or provenance clearing occurs here. -/
def intLikeValue [PointerProvenance P] (h : CastHooks P S C V) (choice : C)
    (scalar : Memory.Scalar P) (source : TyAndLayout TyId) : RvalueM S (U128 × Bool) := do
  let signed ← match source.layout.backendRepr.isSigned with
    | .ok value => pure value | .error _ => invalid "int-like source requires scalar ABI"
  let bits ← match ← h.typeInfo choice source.ty with
    | .integer kind =>
      if kind.signed then
        pure (BitVec.ofInt 128 (← liftResult (scalar.toInt source.layout.size |>.mapError ScalarOps.scalarError)))
      else liftResult (scalar.toUInt source.layout.size |>.mapError ScalarOps.scalarError)
    | .rawPointer _ | .fnPointer => liftResult (scalar.toUInt source.layout.size |>.mapError ScalarOps.scalarError)
    | .boolean => pure (if ← liftResult (scalar.toBool |>.mapError ScalarOps.scalarError) then 1 else 0)
    | .character => pure (BitVec.ofNat 128 (← liftResult (scalar.toChar |>.mapError ScalarOps.scalarError)).toNat)
    | _ => invalid "invalid int-like cast source type"
  pure (bits, signed)

def castFromIntLike [PointerProvenance P] (h : CastHooks P S C V) (choice : C)
    (scalar : Memory.Scalar P) (source target : TyAndLayout TyId) : RvalueM S (RvalueImmTy P) := do
  let (bits, signed) ← intLikeValue h choice scalar source
  let scalar ← match ← h.typeInfo choice target.ty with
    | .integer kind => do
      let value ← liftResult (IntegerCast.cast (.integer ⟨Size.ofBytes 16, .u128⟩)
        (.ofUInt128 bits) (.integer ⟨target.layout.size, kind⟩) |>.mapError integerCastError)
      pure (.fromScalarInt value)
    | .character => do
      let value ← liftResult (IntegerCast.cast (.integer ⟨Size.ofBytes 16, .u128⟩)
        (.ofUInt128 bits) .character |>.mapError integerCastError)
      pure (.fromScalarInt value)
    | .floating format => do
      let integer := if signed then bits.toInt else Int.ofNat bits.toNat
      let result ← liftResult (FloatBits.fromInteger format integer |>.mapError fun e => .invalidProgram s!"{repr e}")
      if target.layout.size != format.size then invalid "float cast target size mismatch"
      liftResult (Memory.Scalar.fromUInt result.bits format.size |>.mapError ScalarOps.scalarError)
    | _ => invalid "invalid int-like cast destination type"
  pure ⟨.scalar scalar, target⟩

def ptrToPtr [PointerProvenance P] (h : CastHooks P S C V) (choice : C)
    (source : RvalueImmTy P) (target : TyAndLayout TyId) : RvalueM S (RvalueImmTy P) := do
  let sourceKind ← h.typeInfo choice source.layout.ty
  if !isAnyPointer sourceKind then invalid "pointer cast source is not a pointer"
  let .rawPointer _ ← h.typeInfo choice target.ty | invalid "pointer cast target is not raw pointer"
  if source.layout.layout.size == target.layout.size then return ⟨source.imm, target⟩
  let ptrSize := Size.fromBits h.target.pointerWidth.bits
  let pairSize ← liftResult (ptrSize.mul 2 |>.mapError fun e => .invalidProgram (toString e))
  if source.layout.layout.size != pairSize || target.layout.size != ptrSize then invalid "fat-to-thin pointer size mismatch"
  let .rawPointer _ := sourceKind | invalid "fat-to-thin source must be raw pointer"
  match source.imm with
  | .scalarPair data _ => pure ⟨.scalar data, target⟩
  | .scalar _ => invalid "scalar input to fat-to-thin cast"
  | .uninit => throw (.undefinedBehavior "InvalidUninitBytes")

def pointerExposeProvenance [PointerProvenance P] (h : CastHooks P S C V) (choice : C)
    (source : RvalueImmTy P) (target : TyAndLayout TyId) : RvalueM S (RvalueImmTy P) := do
  match ← h.typeInfo choice source.layout.ty with
  | .rawPointer _ | .fnPointer => pure ()
  | _ => invalid "expose provenance source must be raw/function pointer"
  let .integer _ ← h.typeInfo choice target.ty | invalid "expose provenance target must be integral"
  let scalar ← scalarOf source
  let pointer ← liftResult (scalar.toPointer h.target |>.mapError ScalarOps.scalarError)
  if let some provenance := pointer.provenance then h.exposeProvenance choice provenance
  castFromIntLike h choice scalar source.layout target

def pointerWithExposedProvenance [PointerProvenance P] (h : CastHooks P S C V) (choice : C)
    (source : RvalueImmTy P) (target : TyAndLayout TyId) : RvalueM S (RvalueImmTy P) := do
  let .integer _ ← h.typeInfo choice source.layout.ty | invalid "from exposed address source must be integral"
  let .rawPointer _ ← h.typeInfo choice target.ty | invalid "from exposed address target must be raw pointer"
  let scalar ← scalarOf source
  let usizeLayout ← h.usizeLayout choice
  let converted ← castFromIntLike h choice scalar source.layout usizeLayout
  let addr ← liftResult ((← scalarOf converted).toTargetUsize (Size.fromBits h.target.pointerWidth.bits)
    |>.mapError ScalarOps.scalarError)
  let pointer ← h.pointerFromExposedAddress choice addr
  let scalar ← liftResult (Memory.Scalar.fromMaybePointer h.target pointer |>.mapError ScalarOps.scalarError)
  pure ⟨.scalar scalar, target⟩

private def entryEq : VTableEntry CallInstance → VTableEntry CallInstance → Bool
  | .dropInPlace, .dropInPlace | .size, .size | .align, .align | .vacant, .vacant => true
  | .method a, .method b => a == b
  | .traitVPtr a, .traitVPtr b => a == b
  | _, _ => false

/-- Source unsize_into_ptr, including dynamic upcast slot/prefix assertions. -/
def unsizeIntoPointer [PointerProvenance P] (h : CastHooks P S C V) (choice : C)
    (source : OpTy P) (dest : V) (sourceTy targetTy : TyId) : RvalueM S Unit := do
  let (sourceTail, targetTail) ← h.lockstepTails choice sourceTy targetTy
  let sourceKind ← h.typeInfo choice sourceTail
  let targetKind ← h.typeInfo choice targetTail
  match sourceKind, targetKind with
  | .array _ length, .slice _ =>
    let pointer ← readPointer h choice source
    let value ← liftResult (Immediate.newSlice pointer length h.target |>.mapError ScalarOps.immediateError)
    h.writeImmediate choice value dest
  | .dynamic actual, .dynamic expected =>
    let value ← h.readImmediate choice source
    if actual == expected then h.writeImmediate choice value.imm dest
    else do
      let (oldData, oldVptr) ← liftResult (value.imm.toScalarPair |>.mapError ScalarOps.immediateError)
      let oldData ← liftResult (oldData.toPointer h.target |>.mapError ScalarOps.scalarError)
      let oldVptr ← liftResult (oldVptr.toPointer h.target |>.mapError ScalarOps.scalarError)
      let ty ← h.vtableType choice oldVptr (some actual)
      let slot ← h.supertraitSlot choice sourceTail targetTail
      let principal ← h.principal choice actual
      let entries ← h.vtableEntries choice principal ty
      if let some index := slot then
        let some (.traitVPtr traitRef) := entries[index]? | invalid "invalid vtable entry in dyn upcast"
        let erased ← h.eraseSelfTraitRef choice traitRef
        let normalized ← h.normalizePrincipal choice expected
        if normalized != some erased then invalid "dyn upcast principal mismatch"
      else
        let principal ← h.principal choice expected
        let targetEntries ← h.vtableEntries choice principal ty
        if targetEntries.size > entries.size then invalid "dyn upcast target vtable exceeds prefix"
        for index in [:targetEntries.size] do
          let some a := entries[index]? | invalid "missing source vtable prefix entry"
          let some b := targetEntries[index]? | invalid "missing target vtable prefix entry"
          if !entryEq a b then invalid "dyn upcast vtable prefix mismatch"
      let vptr ← h.vtablePointer choice ty expected
      let value ← liftResult (Immediate.newDynTrait oldData vptr h.target |>.mapError ScalarOps.immediateError)
      h.writeImmediate choice value dest
  | _, .dynamic expected =>
    let vtable ← h.vtablePointer choice sourceTail expected
    let pointer ← readPointer h choice source
    let value ← liftResult (Immediate.newDynTrait pointer vtable h.target |>.mapError ScalarOps.immediateError)
    h.writeImmediate choice value dest
  | _, _ =>
    h.ensureMonomorphic choice source.layout.ty
    h.ensureMonomorphic choice targetTy
    invalid "invalid pointer unsizing"

/-- Recursive source aggregate unsizing. Earlier field copies stay committed
when a later field fails, including the second-changing-field invariant. -/
def unsizeInto [PointerProvenance P] (h : CastHooks P S C V) (choice : C) (fuel : Nat)
    (source : OpTy P) (target : TyAndLayout TyId) (dest : V) : RvalueM S Unit := do
  match fuel with
  | 0 => throw (.resourceExhaustion "cast unsizing recursion fuel")
  | fuel + 1 =>
    let sourceKind ← h.typeInfo choice source.layout.ty
    let targetKind ← h.typeInfo choice target.ty
    match sourceKind, targetKind with
    | .pattern _ patternA, .pattern inner patternB =>
      if patternA == patternB then
        let source ← h.projectRead choice source 0
        let dest ← h.projectWrite choice dest 0
        let target ← h.layoutOf choice inner
        unsizeInto h choice fuel source target dest
      else
        h.ensureMonomorphic choice source.layout.ty
        h.ensureMonomorphic choice target.ty
        invalid "invalid pattern unsizing"
    | .reference sourceTy, .reference targetTy
    | .reference sourceTy, .rawPointer targetTy
    | .rawPointer sourceTy, .rawPointer targetTy => unsizeIntoPointer h choice source dest sourceTy targetTy
    | .adt a, .adt b =>
      if a != b then invalid "unsizing requires identical ADT definitions"
      let mut found := false
      for index in [:source.layout.layout.fields.count] do
        let targetField ← h.fieldLayout choice target index
        let sourceField ← h.projectRead choice source index
        let destField ← h.projectWrite choice dest index
        if sourceField.layout.layout.is1zst && targetField.layout.is1zst then pure ()
        else if sourceField.layout.ty == targetField.ty then h.copyNoValidate choice sourceField destField false
        else
          if found then invalid "unsize_into: more than one field to cast"
          found := true
          unsizeInto h choice fuel sourceField targetField destField
    | _, _ =>
      h.ensureMonomorphic choice source.layout.ty
      h.ensureMonomorphic choice target.ty
      invalid "invalid unsizing conversion"

private def transmuteImmediate (h : CastHooks P S C V) (value : RvalueImmTy P)
    (target : TyAndLayout TyId) : RvalueM S (RvalueImmTy P) := do
  if !value.layout.layout.isSized || !target.layout.isSized || value.layout.layout.size != target.layout.size then
    invalid "immediate transmute requires equally sized layouts"
  liftResult (h.validateImmediateABI value.imm value.layout.layout)
  let forget := target.layout.isUninhabited || target.layout.isZst ||
    (match target.layout.backendRepr, target.layout.variants, target.layout.fields with
     | .Memory, .Single _, .Arbitrary fields _ => fields.isEmpty | _, _, _ => false)
  let value := if forget then Immediate.uninit else value.imm
  liftResult (h.validateImmediateABI value target.layout)
  pure ⟨value, target⟩

/-- Full source cast dispatch. Cast layout resolution precedes source validity,
which is skipped exactly for transmute/subtype/box-deref and unsizing. -/
def cast [PointerProvenance P] (h : CastHooks P S C V) (choice : C) (fuel : Nat)
    (source : OpTy P) (kind : CastKind) (castTy : TyId) (dest : V) : RvalueM S Unit := do
  let destLayout := h.destLayout dest
  let target ← if castTy == destLayout.ty then pure destLayout else h.layoutOf choice castTy
  let skipValidity := match kind with
    | .Transmute | .Subtype | .BoxDerefTransmute | .PointerCoercion .Unsize _ => true | _ => false
  unless skipValidity do
    if ← h.enforceValidity choice source.layout then
      match ← h.typeInfo choice source.layout.ty with
      | .rawPointer _ =>
        if (match source.layout.layout.backendRepr with | .ScalarPair => true | _ => false) then h.derefPointer choice source
      | .fnPointer => h.checkFunctionPointer choice (← readPointer h choice source)
      | .closure _ _ upvars => if upvars != 0 then invalid "capturing closure in pointer cast"
      | .integer _ | .floating _ | .boolean | .character | .fnDefinition _ _ => pure ()
      | _ => invalid "unexpected input type in non-transmute/unsize cast"
  match kind with
  | .PointerCoercion .Unsize _ =>
    unsizeInto h choice fuel source target dest
    if ← h.enforceValidity choice destLayout then
      let recursive ← h.enforceValidityRecursively choice destLayout
      h.validatePlace choice dest recursive true
  | .PointerExposeProvenance =>
    let value ← h.readImmediate choice source
    let result ← pointerExposeProvenance h choice value target
    h.writeImmediate choice result.imm dest
  | .PointerWithExposedProvenance =>
    let value ← h.readImmediate choice source
    let result ← pointerWithExposedProvenance h choice value target
    h.writeImmediate choice result.imm dest
  | .IntToInt | .IntToFloat =>
    let value ← h.readImmediate choice source
    let sourceKind ← h.typeInfo choice value.layout.ty
    match sourceKind with
    | .integer _ | .boolean | .character => pure ()
    | _ => invalid "IntToInt/IntToFloat source type is not integer-like"
    match ← h.typeInfo choice target.ty with
    | .integer _ | .floating _ | .character => pure ()
    | _ => invalid "IntToInt/IntToFloat destination type is not integer/float/char"
    let result ← castFromIntLike h choice (← scalarOf value) value.layout target
    h.writeImmediate choice result.imm dest
  | .FloatToFloat | .FloatToInt =>
    let value ← h.readImmediate choice source
    let .floating _ ← h.typeInfo choice value.layout.ty | invalid "float cast source type is not float"
    -- Source converts the input float payload before matching destination kind.
    let bits ← FloatOps.readBits h.floatOps choice value
    let scalar ← match ← h.typeInfo choice target.ty with
      | .floating format => do
        let converted ← liftResult (bits.convert format |>.mapError fun e => .invalidProgram s!"{repr e}")
        let converted ← FloatOps.adjustNaN h.floatOps choice converted [bits]
        if target.layout.size != format.size then invalid "float cast target size mismatch"
        liftResult (Memory.Scalar.fromUInt converted.bits format.size |>.mapError ScalarOps.scalarError)
      | .integer integerKind => do
        let width ← liftResult (target.layout.size.bitsNat |>.mapError fun e => .invalidProgram (toString e))
        let integer ← liftResult (bits.toInteger width integerKind.signed |>.mapError fun e => .invalidProgram s!"{repr e}")
        if integerKind.signed then
          liftResult (Memory.Scalar.fromInt integer target.layout.size |>.mapError ScalarOps.scalarError)
        else liftResult (Memory.Scalar.fromUInt (BitVec.ofInt 128 integer) target.layout.size |>.mapError ScalarOps.scalarError)
      | _ => invalid "invalid float cast destination"
    h.writeImmediate choice (.scalar scalar) dest
  | .FnPtrToPtr | .PtrToPtr =>
    let value ← h.readImmediate choice source
    let result ← ptrToPtr h choice value target
    h.writeImmediate choice result.imm dest
  | .PointerCoercion .MutToConstPointer _ | .PointerCoercion .ArrayToPointer _ =>
    invalid "borrowck-only pointer coercion in runtime MIR"
  | .PointerCoercion (.ReifyFnPointer _) _ =>
    h.ensureMonomorphic choice source.layout.ty
    let .fnDefinition definition args ← h.typeInfo choice source.layout.ty | invalid "reify fn pointer on non-function definition"
    h.requireNoBoundVars choice args
    let some fnInstance ← h.resolveFunction choice definition args | invalid "TooGeneric"
    h.writePointer choice (← h.functionPointer choice fnInstance) dest
  | .PointerCoercion .UnsafeFnPointer _ =>
    let value ← h.readImmediate choice source
    let .fnPointer ← h.typeInfo choice castTy | invalid "unsafe fn pointer target is not fn pointer"
    h.writeImmediate choice value.imm dest
  | .PointerCoercion (.ClosureFnPointer _) _ =>
    h.ensureMonomorphic choice source.layout.ty
    let .closure definition args _ ← h.typeInfo choice source.layout.ty | invalid "closure fn pointer on non-closure"
    let fnInstance ← h.resolveClosureFnOnce choice definition args
    h.writePointer choice (← h.functionPointer choice fnInstance) dest
  | .Transmute | .Subtype | .BoxDerefTransmute =>
    if !source.layout.layout.isSized || !destLayout.layout.isSized then invalid "transmute requires sized types"
    if castTy != destLayout.ty then invalid "transmute target type differs from destination"
    if source.layout.layout.size != destLayout.layout.size then throw (.undefinedBehavior "transmute size mismatch")
    if kind == .BoxDerefTransmute then
      let pointer ← h.readImmediate choice source
      let some pointee ← h.builtinDeref choice castTy true
        | invalid "BoxDerefTransmute target is not dereferenceable"
      let box ← h.boxLayout choice pointee
      let pointer ← transmuteImmediate h pointer box
      h.derefPointer choice ⟨.immediate pointer.imm, pointer.layout⟩
    h.copyAllowTransmute choice source dest

end Cast
end Miri.Interpreter
