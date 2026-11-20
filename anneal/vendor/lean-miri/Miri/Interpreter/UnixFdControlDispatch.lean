import Miri.Interpreter.UnixFdControl

/-! Source unix/foreign_items.rs fcntl/ioctl variadic wrappers. No entry poll:
this handler belongs inside the canonical single-poll Unix foreign chain. -/
namespace Miri.Interpreter.UnixFdControlDispatch
open Miri.ABI Miri.Memory Miri.MIR
variable {Place : Type}
abbrev M := EStateM StepError
structure Hooks (S H D O E Meta Place B I : Type) where
  control : UnixFdControl.Hooks S H D O E Meta
  signatures : ShimSignatures.Hooks Provenance S Place (MPlaceTy Provenance) (Pointer (Option Provenance)) B I
  signature : String → M S (FnAbi TyId)
  i32Type : M S TyId
  typeBudget : Nat
  writeScalar : Scalar Provenance → MPlaceTy Provenance → M S Unit
private def arg (args : Array A) (index : Nat) : M S A :=
  match args[index]? with
  | some value => pure value
  | none => throw (.invalidProgram "checked FD control argument absent")

def emulate (h : Hooks S H D O E Meta Place B I) (name : String) (abi : FnAbi TyId)
    (args : Array (OpTy Provenance)) (dest : MPlaceTy Provenance) :
    M S (Option ForeignItems.EmulateItemResult) := do
  unless name == "fcntl" || name == "ioctl" do return none
  let (fixed,rest) ← ShimSignatures.variadic h.signatures name (h.signature name) 2 abi args
  let control := {h.control with
    readScalar := h.signatures.readScalar
    readI32 := h.signatures.foreign.readI32
    takeI32 := fun _ rest => do
      let (values,_) ← ShimSignatures.take h.signatures h.typeBudget
        (do return #[← h.i32Type]) rest
      arg values 0}
  let result ← if name == "fcntl" then UnixFdControl.fcntl control (← arg fixed 0) (← arg fixed 1) rest
    else UnixFdControl.ioctl control (← arg fixed 0) (← arg fixed 1) rest
  h.writeScalar result dest
  return some .NeedsReturn

def bind (h : Hooks S H D O E Meta Place B I) :
    ForeignItems.Hooks Provenance S Place (MPlaceTy Provenance) (Pointer (Option Provenance)) B I :=
  {h.signatures.foreign with unix := fun name abi args dest => do
    if let some result ← emulate h name abi args dest then return result
    h.signatures.foreign.unix name abi args dest}
end Miri.Interpreter.UnixFdControlDispatch
