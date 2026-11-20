import Miri.Interpreter.UnixVectored
import Miri.Interpreter.ShimSignatures

/-! Common Unix readv/writev/preadv/pwritev wrappers. Exactly one outer
UnixForeign entry poll must already have run; this handler does not poll. -/
namespace Miri.Interpreter.UnixVectoredDispatch
open Miri.ABI Miri.Memory Miri.MIR
variable {Place : Type}
abbrev M := EStateM StepError
structure Hooks (S H D O E Meta Place B I : Type) where
  vector : UnixVectored.Hooks S H D O E Meta
  signatures : ShimSignatures.Hooks Provenance S Place (MPlaceTy Provenance) (Pointer (Option Provenance)) B I
  signature : String → M S (FnAbi TyId)
private def arg (args : Array A) (index : Nat) : M S A :=
  match args[index]? with
  | some value => pure value
  | none => throw (.invalidProgram "checked vectored IO operand absent")

def emulate (h : Hooks S H D O E Meta Place B I) (name : String) (abi : FnAbi TyId)
    (args : Array (OpTy Provenance)) (dest : MPlaceTy Provenance) :
    M S (Option ForeignItems.EmulateItemResult) := do
  unless #["readv","writev","preadv","pwritev"].contains name do return none
  let positional := name == "preadv" || name == "pwritev"
  let args ← ShimSignatures.fixed h.signatures name (h.signature name) (if positional then 4 else 3) abi args
  let position ← if positional then (arg args 3).map some else pure none
  UnixVectored.execute h.vector (← arg args 0) (← arg args 1) (← arg args 2)
    position (name == "writev" || name == "pwritev") dest
  return some .NeedsReturn
end Miri.Interpreter.UnixVectoredDispatch
