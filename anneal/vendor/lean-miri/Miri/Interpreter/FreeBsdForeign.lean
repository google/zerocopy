import Miri.Interpreter.FreeBsdSync
import Miri.Interpreter.ShimSignatures
import Miri.Interpreter.IoError

namespace Miri.Interpreter.FreeBsdForeign
open Miri.ABI Miri.Memory
abbrev M := EStateM StepError
def dynamicSymbol (_name : String) : Bool := false
structure Hooks (S R D E B I : Type) where
  foreign : ForeignItems.Hooks Provenance S D (MPlaceTy Provenance) (Pointer (Option Provenance)) B I
  sync : FreeBsdSync.Hooks S R
  errors : IoError.Hooks S E
private def arg (args : Array A) (i : Nat) : M S A :=
  match args[i]? with | some a => pure a | none => throw (.invalidProgram "checked FreeBSD operand missing")

def emulate (h : Hooks S R D E B I) (name : String) (abi : FnAbi Miri.MIR.TyId)
    (args : Array (OpTy Provenance)) (dest : MPlaceTy Provenance) : M S (Option ForeignItems.EmulateItemResult) := do
  if h.foreign.os != "freebsd" || !(#["__error","_umtx_op"].contains name) then return none
  h.foreign.checkSymbolClash name
  if abi.conv != .C then throw (.undefinedBehavior "FreeBSD legacy calling convention mismatch")
  if abi.cVariadic then throw (.undefinedBehavior "FreeBSD legacy variadic signature")
  if args.size != (if name == "__error" then 0 else 5) then throw (.undefinedBehavior "FreeBSD legacy argument count mismatch")
  if name == "__error" then h.foreign.writePointer (← IoError.lastErrorPlace h.errors).mplace.ptr dest
  else FreeBsdSync.operation h.sync (← arg args 0) (← arg args 1) (← arg args 2) (← arg args 3) (← arg args 4) dest
  return some .NeedsReturn
end Miri.Interpreter.FreeBsdForeign
