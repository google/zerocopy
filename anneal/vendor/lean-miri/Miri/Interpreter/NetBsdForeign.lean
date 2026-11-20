import Miri.Interpreter.ShimSignatures
import Miri.Interpreter.UnixEnvironment

/-! Entire pinned NetBSD foreign_items.rs; no dynamic symbols are exposed. -/
namespace Miri.Interpreter.NetBsdForeign
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
def dynamicSymbol (_name : String) : Bool := false
structure Hooks (S Os E Kind D B I : Type) where
  signatures : ShimSignatures.Hooks Provenance S D (MPlaceTy Provenance) (Pointer (Option Provenance)) B I
  environment : UnixEnvironment.Hooks S Os E Kind
  signature : String → M S (FnAbi Miri.MIR.TyId)

/-- Minimal source adapter for NetBSD's two fixed shims. It consumes the
canonical nonrecursive foreign Core and source Unix environment directly;
unrelated recursive dispatch hooks are not fabricated. -/
structure CoreHooks (S Os E Kind D B I : Type) where
  foreign : ForeignItems.Core Provenance S D (MPlaceTy Provenance) (Pointer (Option Provenance)) B I
  environment : UnixEnvironment.Hooks S Os E Kind
  signature : String → M S (FnAbi Miri.MIR.TyId)

def emulateCore (h : CoreHooks S Os E Kind D B I) (name : String)
    (abi : FnAbi Miri.MIR.TyId) (args : Array (OpTy Provenance))
    (dest : MPlaceTy Provenance) : M S (Option ForeignItems.EmulateItemResult) := do
  if h.foreign.family != .unix || h.foreign.os != "netbsd" ||
      h.environment.os != "netbsd" || !(#["__errno","__unsetenv13"].contains name) then return none
  let count := if name == "__errno" then 0 else 1
  let signatures : ShimSignatures.CoreHooks Provenance S D (MPlaceTy Provenance)
      (Pointer (Option Provenance)) B I := ⟨h.foreign⟩
  let args ← ShimSignatures.fixedCore signatures name (h.signature name) count abi args
  if name == "__errno" then
    let place ← IoError.lastErrorPlace h.environment.errors
    h.foreign.writePointer place.mplace.ptr dest
  else
    let some op := args[0]? | throw (.invalidProgram "checked NetBSD unsetenv operand missing")
    let value ← EnvVars.unsetenv h.environment.env (← h.environment.readPointer op)
    let scalar ← match Scalar.fromInt value.toInt (Size.ofBytes 4) with
      | .ok value => pure value | .error error => throw (ScalarOps.scalarError error)
    h.environment.errors.writeScalar scalar dest
  return some .NeedsReturn

def emulate (h : Hooks S Os E Kind D B I) (name : String) (abi : FnAbi Miri.MIR.TyId)
    (args : Array (OpTy Provenance)) (dest : MPlaceTy Provenance) : M S (Option ForeignItems.EmulateItemResult) := do
  if h.signatures.foreign.os != "netbsd" || !(#["__errno","__unsetenv13"].contains name) then return none
  let args ← ShimSignatures.fixed h.signatures name (h.signature name) (if name == "__errno" then 0 else 1) abi args
  if name == "__errno" then
    h.signatures.foreign.writePointer (← IoError.lastErrorPlace h.environment.errors).mplace.ptr dest
  else
    let some op := args[0]? | throw (.invalidProgram "checked NetBSD unsetenv operand missing")
    let value ← EnvVars.unsetenv h.environment.env (← h.environment.readPointer op)
    let scalar ← match Scalar.fromInt value.toInt (Size.ofBytes 4) with
      | .ok value => pure value | .error error => throw (ScalarOps.scalarError error)
    h.environment.errors.writeScalar scalar dest
  return some .NeedsReturn
end Miri.Interpreter.NetBsdForeign
