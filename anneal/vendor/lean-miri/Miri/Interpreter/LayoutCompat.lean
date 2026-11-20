import Miri.ABI.CallConv
import Miri.Interpreter.Step

/-! Pinned `interpret/call.rs:74–385`: trivial ABI, transparent/NPO unfolding,
C structural equality and argument compatibility. Compiler type queries are
required fallible operations; no unknown predicate becomes false or true.
A depth budget makes recursive compiler queries executable and reports resource
exhaustion explicitly. The budget is not a bound on Rust execution semantics. -/
namespace Miri.Interpreter.LayoutCompat
open Miri.ABI

inductive AdtKind where
  | Struct | Union | Enum
  deriving DecidableEq, Repr
structure Field (Ty : Type) where
  name : String
  ty : Ty
  deriving Repr
structure AdtInfo (Ty : Type) where
  kind : AdtKind
  transparent : Bool
  reprC : Bool
  reprRust : Bool
  /-- Field types are instantiated with the queried type's complete arguments;
  normalization is requested separately at the source sites that require it. -/
  variants : Array (Array (Field Ty))

inductive TypeKind (Ty : Type) where
  | tuple | never | functionDefinition | closure | coroutine | coroutineClosure
  | array (element : Ty)
  | adt
  | pattern (base : Ty)
  | unsafeBinder
  | alias
  | reference (pointee : Ty)
  | rawPointer (pointee : Ty)
  | functionPointer
  | integer (kind : MIR.IntegerKind)
  | char
  | other
  deriving Repr

abbrev M (S A : Type) := EStateM StepError S A
structure Queries (Ty S : Type) where
  target : RuntimeTargetDataLayout
  kind : Ty → M S (TypeKind Ty)
  adt : Ty → M S (AdtInfo Ty)
  field : TyAndLayout Ty → Nat → M S (TyAndLayout Ty)
  layoutOf : Ty → M S (TyAndLayout Ty)
  unitLayout : M S (TyAndLayout Ty)
  eraseUnsafeBinder : Ty → M S Ty
  normalize : Ty → M S Ty
  reprEqualUpToSeed : Ty → Ty → M S Bool
  itemName : Ty → M S String
  nonnullOptimizationGuaranteed : Ty → M S Bool
  isGlobalBox : Ty → M S Bool
  boxedType : Ty → M S Ty
  /-- ptr_metadata_ty must normalize projected unsized-tail types, exactly as
  the source closure does, rather than comparing only top-level pointees. -/
  pointerMetadataType : Ty → M S Ty

private def exhausted : M S A := throw (.resourceExhaustion "ABI type-query recursion budget exhausted")
private def invariant (condition : Bool) (message : String) : M S Unit :=
  unless condition do throw (.invalidProgram message)
private def atIndex (values : Array A) (index : Nat) (message : String) : M S A :=
  match values[index]? with | some value => pure value | none => throw (.invalidProgram message)

def hasTrivialAbi (q : Queries Ty S) : Nat → TyAndLayout Ty → M S Bool
  | 0,_ => exhausted
  | fuel+1,layout => do
    if !layout.layout.is1zst then return false
    match ← q.kind layout.ty with
    | .tuple | .never | .functionDefinition | .closure | .coroutine | .coroutineClosure => pure true
    | .array element => hasTrivialAbi q fuel (← q.layoutOf element)
    | .adt =>
      let info ← q.adt layout.ty
      if info.transparent then
        let mut result := true
        for index in List.range layout.layout.fields.count do
          -- Source try_fold still iterates after false, but && suppresses its queries.
          if result then result ← hasTrivialAbi q fuel (← q.field layout index)
        pure result
      else if info.reprC then pure false
      else
        invariant info.reprRust "non-C, nontransparent 1-ZST ADT is not repr(Rust)"
        pure true
    | .pattern base => hasTrivialAbi q fuel (← q.layoutOf base)
    | .unsafeBinder => hasTrivialAbi q fuel (← q.layoutOf (← q.eraseUnsafeBinder layout.ty))
    | .alias => throw (.invalidProgram "non-normalized alias in has_trivial_abi")
    | _ => pure false

/-- The three source `may_unfold` closures, represented without a second IR. -/
inductive UnfoldPolicy where
  | All | Structs | StructsUntilNpo
  deriving DecidableEq, Repr
private def mayUnfold (q : Queries Ty S) (ty : Ty) (policy : UnfoldPolicy) (info : AdtInfo Ty) : M S Bool :=
  match policy with
  | .All => pure true
  | .Structs => pure (info.kind == .Struct)
  | .StructsUntilNpo => do
    if info.kind != .Struct then return false
    return !(← q.nonnullOptimizationGuaranteed ty)

def unfoldTransparent (q : Queries Ty S) (policy : UnfoldPolicy) :
    Nat → TyAndLayout Ty → M S (TyAndLayout Ty)
  | 0,_ => exhausted
  | fuel+1,layout => do
    match ← q.kind layout.ty with
    | .adt =>
      let info ← q.adt layout.ty
      if !info.transparent then return layout
      if !(← mayUnfold q layout.ty policy info) then return layout
      match layout.layout.variants with
      | .Single _ => pure ()
      | _ => throw (.invalidProgram "transparent ADT is not Single variant")
      let mut found := none
      for index in List.range layout.layout.fields.count do
        let field ← q.field layout index
        if ← hasTrivialAbi q fuel field then continue
        if found.isSome then return layout
        found := some field
      match found with
      | none => q.unitLayout
      | some field => unfoldTransparent q policy fuel field
    | .pattern base => unfoldTransparent q policy fuel (← q.layoutOf base)
    | .unsafeBinder => unfoldTransparent q policy fuel (← q.layoutOf (← q.eraseUnsafeBinder layout.ty))
    | _ => pure layout

private def allFields1zst (q : Queries Ty S) (fields : Array (Field Ty)) : M S Bool := do
  for field in fields do
    let layout ← q.layoutOf field.ty
    if !layout.layout.is1zst then return false
  pure true

def unfoldNpo (q : Queries Ty S) (fuel : Nat) (layout : TyAndLayout Ty) : M S (TyAndLayout Ty) := do
  match fuel with
  | 0 => exhausted
  | fuel+1 =>
    match ← q.kind layout.ty with
    | .adt => pure ()
    | _ => return layout
    let info ← q.adt layout.ty
    if info.variants.size != 2 then return layout
    invariant (info.kind == .Enum) "two-variant ADT is not an enum"
    let first ← atIndex info.variants 0 "missing first enum variant"
    let second ← atIndex info.variants 1 "missing second enum variant"
    let relevant ← if ← allFields1zst q first then pure second
      else if ← allFields1zst q second then pure first else return layout
    if relevant.size != 1 then return layout
    let field ← atIndex relevant 0 "missing NPO field"
    let inner ← q.layoutOf field.ty
    let inner ← unfoldTransparent q .StructsUntilNpo fuel inner
    match ← q.kind inner.ty with
    | .reference _ | .functionPointer => return inner
    | .adt =>
      if ← q.nonnullOptimizationGuaranteed inner.ty then
        return ← unfoldTransparent q .Structs fuel inner
      return layout
    | _ => return layout

def identicalCTypes [DecidableEq Ty] (q : Queries Ty S) : Nat → Ty → Ty → M S Bool
  | 0,_,_ => exhausted
  | fuel+1,caller,callee => do
    if caller == callee then return true
    match ← q.kind caller with | .adt => pure () | _ => return false
    match ← q.kind callee with | .adt => pure () | _ => return false
    let left ← q.adt caller
    let right ← q.adt callee
    if left.kind != .Struct || right.kind != .Struct then return false
    if !left.reprC then return false
    if !(← q.reprEqualUpToSeed caller callee) then return false
    if (← q.itemName caller) != (← q.itemName callee) then return false
    let leftFields ← atIndex left.variants 0 "missing C-struct fields"
    let rightFields ← atIndex right.variants 0 "missing C-struct fields"
    if leftFields.size != rightFields.size then return false
    for index in List.range leftFields.size do
      let first ← atIndex leftFields index "missing C caller field"
      let second ← atIndex rightFields index "missing C callee field"
      if first.name != second.name then return false
      let caller ← q.normalize first.ty
      let callee ← q.normalize second.ty
      if !(← identicalCTypes q fuel caller callee) then return false
    pure true

private def thinPointer (layout : TyAndLayout Ty) : Option AddressSpace :=
  match layout.layout.backendRepr with
  | .Scalar scalar => match scalar.primitive with | .Pointer space => some space | _ => none
  | _ => none
private def pointee (q : Queries Ty S) (ty : Ty) : M S (Option Ty) := do
  match ← q.kind ty with
  | .reference target | .rawPointer target => pure (some target)
  | _ => if ← q.isGlobalBox ty then return some (← q.boxedType ty) else pure none
private def integer (q : Queries Ty S) (ty : Ty) : M S (Option (Integer × Bool)) := do
  match ← q.kind ty with
  | .char => pure (some (.I32,false))
  | .integer tag =>
    let value ← match tag with
      | .i8 | .u8 => pure Integer.I8 | .i16 | .u16 => pure .I16
      | .i32 | .u32 => pure .I32 | .i64 | .u64 => pure .I64
      | .i128 | .u128 => pure .I128
      | .isize | .usize =>
        match q.target.ptrSizedInteger with
        | .ok value => pure value
        | .error e => throw (.unsupported s!"pointer-sized ABI integer: {e}")
    pure (some (value,tag.signed))
  | _ => pure none

def layoutCompat [DecidableEq Ty] (q : Queries Ty S) (fuel : Nat)
    (caller callee : TyAndLayout Ty) : M S Bool := do
  if caller.ty == callee.ty then return true
  if ← hasTrivialAbi q fuel caller then
    if ← hasTrivialAbi q fuel callee then return true
  let unfold (layout : TyAndLayout Ty) := do
    unfoldNpo q fuel (← unfoldTransparent q .All fuel layout)
  let caller ← unfold caller
  let callee ← unfold callee
  if ← identicalCTypes q fuel caller.ty callee.ty then return true
  let left := thinPointer caller
  let right := thinPointer callee
  if let (some left,some right) := (left,right) then return left == right
  -- Rust tuple construction evaluates both pointee queries before matching.
  let left ← pointee q caller.ty
  let right ← pointee q callee.ty
  if let (some left,some right) := (left,right) then
    let left ← q.pointerMetadataType left
    let right ← q.pointerMetadataType right
    return left == right
  let left ← integer q caller.ty
  let right ← integer q callee.ty
  if let (some left,some right) := (left,right) then return left == right
  pure false

def checkArgumentCompat [DecidableEq Ty] (q : Queries Ty S) (fuel : Nat)
    (caller callee : ArgAbi Ty) : M S Bool := do
  if ← layoutCompat q fuel caller.layout callee.layout then
    invariant (caller.eqAbi callee) "check_argument_compat: concrete ArgAbi.eq_abi assertion failed"
    return true
  pure false

end Miri.Interpreter.LayoutCompat
