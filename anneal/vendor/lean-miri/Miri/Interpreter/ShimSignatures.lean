import Miri.Interpreter.ForeignItems
import Miri.Interpreter.LayoutCompat
import Miri.Interpreter.ScalarOps

/-! Pinned shims/sig.rs signature/varargs policies, and rustc
interpret/intrinsics.rs::validate_c_variadic_compatible_ty. Query budgets are
concrete execution resources; their exhaustion is unresolved, never UB/success.
-/
namespace Miri.Interpreter.ShimSignatures
open Miri.ABI Miri.Memory Miri.MIR
abbrev M := EStateM StepError
inductive Compatible where
  | yes | no | castInteger (sourceSigned : Bool)
  deriving DecidableEq, Repr
structure Varargs (P : Type) where
  args : Array (OpTy P)
  alreadyGone : Nat
structure Hooks (P S D MD Ptr B I : Type) where
  foreign : ForeignItems.Hooks P S D MD Ptr B I
  types : LayoutCompat.Queries TyId S
  isCVoid : TyId → M S Bool
  readScalar : OpTy P → M S (Scalar P)
  /-- Width of the host usize used by source strict_add diagnostics. -/
  hostUsizeBits : Nat

/-- Nonrecursive exact-signature effects for fixed shims that do not need
variadic type compatibility. This avoids requiring a complete platform
ForeignItems dispatch merely to validate one source family. -/
structure CoreHooks (P S D MD Ptr B I : Type) where
  foreign : ForeignItems.Core P S D MD Ptr B I

/-- Signature-only projection for source dispatchers that need no recursive
foreign-item fallback. This keeps fixed shim validation tied to the actual
ABI/symbol/transmute primitives while avoiding a dependency on a complete
platform hook record. -/
structure PrimitiveHooks (P S : Type) where
  family : ForeignItems.Family
  os : String
  checkAbi : FnAbi TyId → FnAbi TyId → M S Unit
  checkSymbolClash : String → M S Unit
  transmute : OpTy P → TyAndLayout TyId → M S (OpTy P)

def primitiveView (h : Hooks P S D MD Ptr B I) : PrimitiveHooks P S := {
  family := h.foreign.family
  os := h.foreign.os
  checkAbi := ForeignItems.checkAbi h.foreign
  checkSymbolClash := h.foreign.checkSymbolClash
  transmute := h.foreign.transmute }

private def invariant (condition : Bool) (message : String) : M S Unit :=
  unless condition do throw (.invalidProgram message)
private def argAt (array : Array A) (index : Nat) : M S A :=
  match array[index]? with
  | some value => pure value
  | none => throw (.invalidProgram "source shim argument array index out of bounds")
private def lift (value : Except StepError A) : M S A :=
  match value with | .ok value => pure value | .error error => throw error
private def pointee : LayoutCompat.TypeKind TyId → Option TyId
  | .rawPointer ty | .reference ty => some ty | _ => none
private def isChar (h : Hooks P S D MD Ptr B I) (ty : TyId) : M S Bool := do
  match ← h.types.kind ty with
  | .integer .i8 | .integer .u8 => return true
  | _ => return false

def compatible (h : Hooks P S D MD Ptr B I) : Nat → TyId → TyId → M S Compatible
  | 0,_,_ => throw (.resourceExhaustion "C variadic type recursion budget")
  | fuel+1,caller,callee => do
    if ← LayoutCompat.identicalCTypes h.types (fuel+1) caller callee then return .yes
    let left ← h.types.layoutOf caller
    let right ← h.types.layoutOf callee
    if left.layout.size != right.layout.size then return .no
    let leftKind ← h.types.kind caller
    let rightKind ← h.types.kind callee
    match leftKind,rightKind with
    | .integer left,.integer right =>
      if left.signed == right.signed then return .yes
      return .castInteger left.signed
    | _,_ =>
      if let some left := pointee leftKind then
        if let some right := pointee rightKind then
          if ← h.isCVoid left then
            if ← isChar h right then return .yes
          if ← h.isCVoid right then
            if ← isChar h left then return .yes
          match ← compatible h fuel left right with
          | .no => return .no
          | .yes | .castInteger _ => return .yes
      return .no

/-- The closure has already built the exact compiler signature (source
ShimSig.as_abi); ABI checks precede symbol-clash checks and operand transmutes. -/
def fixed (h : Hooks P S D MD Ptr B I) (name : String)
    (expected : M S (FnAbi TyId)) (count : Nat) (caller : FnAbi TyId)
    (args : Array (OpTy P)) : M S (Array (OpTy P)) := do
  let callee ← expected
  invariant (!callee.cVariadic) "nonvariadic shim signature constructed variadic"
  ForeignItems.checkAbi h.foreign caller callee
  h.foreign.checkSymbolClash name
  let mut result := #[]
  for index in [:count] do
    let operand ← argAt args index
    let expected ← argAt callee.args index
    result := result.push (← h.foreign.transmute operand expected.layout)
  return result

/-- Fixed-signature source path over the nonrecursive foreign primitive core;
the ABI check, symbol clash, then argument transmute order is unchanged. -/
def fixedCore (h : CoreHooks P S D MD Ptr B I) (name : String)
    (expected : M S (FnAbi TyId)) (count : Nat) (caller : FnAbi TyId)
    (args : Array (OpTy P)) : M S (Array (OpTy P)) := do
  let callee ← expected
  invariant (!callee.cVariadic) "nonvariadic shim signature constructed variadic"
  ForeignItems.Core.checkAbi h.foreign caller callee
  h.foreign.checkSymbolClash name
  if args.size != count then throw (.invalidProgram "shim arguments disagree with fixed signature")
  let mut result := #[]
  for index in [:count] do
    let operand ← argAt args index
    let expected ← argAt callee.args index
    result := result.push (← h.foreign.transmute operand expected.layout)
  return result

/-- Fixed shim validation over the minimal source signature primitives. The
source order remains ABI check, symbol clash, then argument transmutation. -/
def fixedPrimitive (h : PrimitiveHooks P S) (name : String)
    (expected : M S (FnAbi TyId)) (count : Nat) (caller : FnAbi TyId)
    (args : Array (OpTy P)) : M S (Array (OpTy P)) := do
  let callee ← expected
  invariant (!callee.cVariadic) "nonvariadic shim signature constructed variadic"
  h.checkAbi caller callee
  h.checkSymbolClash name
  if args.size != count then throw (.invalidProgram "shim arguments disagree with fixed signature")
  let mut result := #[]
  for index in [:count] do
    let operand ← argAt args index
    let expected ← argAt callee.args index
    result := result.push (← h.transmute operand expected.layout)
  return result

def variadic (h : Hooks P S D MD Ptr B I) (name : String)
    (expected : M S (FnAbi TyId)) (count : Nat) (caller : FnAbi TyId)
    (args : Array (OpTy P)) : M S (Array (OpTy P) × Varargs P) := do
  let callee ← expected
  invariant callee.cVariadic "variadic shim signature constructed nonvariadic"
  ForeignItems.checkAbi h.foreign caller callee
  h.foreign.checkSymbolClash name
  invariant (args.size >= count) "variadic shim fixed chunk unwrap"
  let mut result := #[]
  for index in [:count] do
    let expected ← argAt callee.args index
    result := result.push (← h.foreign.transmute (← argAt args index) expected.layout)
  return (result,⟨args.extract count args.size,count⟩)

private def strictAdd (h : Hooks P S D MD Ptr B I) (left right : Nat) : M S Nat := do
  if left+right >= 2^h.hostUsizeBits then throw (.invalidProgram "source usize strict_add overflow")
  return left+right

/-- Check the entire prefix for C type compatibility before transmuting any
operand. Signed/unsigned pairs share source signed-at-width value checking. -/
def take [PointerProvenance P] (h : Hooks P S D MD Ptr B I) (budget : Nat) (types : M S (Array TyId))
    (varargs : Varargs P) : M S (Array (OpTy P) × Varargs P) := do
  let types ← types
  if varargs.args.size < types.size then
    let _ ← strictAdd h varargs.alreadyGone varargs.args.size
    let _ ← strictAdd h varargs.alreadyGone types.size
    throw (.undefinedBehavior "not enough C variadic arguments")
  let now := varargs.args.extract 0 types.size
  for index in [:types.size] do
    let caller ← argAt now index
    match ← compatible h budget caller.layout.ty (← argAt types index) with
    | .yes => pure ()
    | .no =>
      let _ ← strictAdd h (← strictAdd h varargs.alreadyGone index) 1
      throw (.undefinedBehavior "incompatible C variadic argument type")
    | .castInteger _ =>
      let scalar ← h.readScalar caller
      let value ← lift (scalar.toInt caller.layout.layout.size |>.mapError ScalarOps.scalarError)
      if value < 0 then
        let _ ← strictAdd h (← strictAdd h varargs.alreadyGone index) 1
        throw (.undefinedBehavior "C variadic integer not representable in both signednesses")
  let mut result := #[]
  for index in [:types.size] do
    let layout ← h.types.layoutOf (← argAt types index)
    result := result.push (← h.foreign.transmute (← argAt now index) layout)
  let consumed ← strictAdd h varargs.alreadyGone types.size
  return (result,⟨varargs.args.extract types.size varargs.args.size,consumed⟩)

def deprecated (h : Hooks P S D MD Ptr B I) (name : String) (conv : CanonAbi)
    (caller : FnAbi TyId) (args : Array (OpTy P)) (count : Nat) : M S (Array (OpTy P)) := do
  h.foreign.checkSymbolClash name
  if caller.conv != conv then throw (.undefinedBehavior "deprecated shim calling convention mismatch")
  if caller.cVariadic then throw (.undefinedBehavior "deprecated shim variadic signature")
  if args.size != count then throw (.undefinedBehavior "deprecated shim argument count mismatch")
  return args

def llvmIntrinsic (h : Hooks P S D MD Ptr B I) (name : String)
    (args : Array (OpTy P)) (count : Nat) : M S (Array (OpTy P)) := do
  invariant (name.startsWith "llvm.") "LLVM shim name source assertion"
  h.foreign.checkSymbolClash name
  if args.size != count then throw (.undefinedBehavior "LLVM shim argument count mismatch")
  return args
end Miri.Interpreter.ShimSignatures
