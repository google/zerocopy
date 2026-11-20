import Miri.Memory.Access

/-! Source `intrinsics.rs::ptr_offset_inbounds`. Pointer resolution and live
allocation metadata must be supplied by the machine's concrete memory state. -/
namespace Miri.Interpreter

open Miri.Memory

inductive PointerOffsetError where
  | access (reason : AccessError)
  | pointer (reason : PointerError)
  deriving DecidableEq, Repr

def ptrOffsetInbounds {Prov ProvExtra : Type}
    (target : PointerArithmetic) (ptr : Pointer (Option Prov)) (offsetBytes : Int64)
    (resolve : PointerResolver Prov ProvExtra) (lookup : LiveAllocationLookup) :
    Except PointerOffsetError (Pointer (Option Prov)) := do
  checkPtrAccessSigned target ptr offsetBytes .inboundsPointerArithmetic resolve lookup
    |>.mapError .access
  ptr.wrappingSignedOffset offsetBytes target |>.mapError .pointer

end Miri.Interpreter
