/-! Operator tags of the pinned `rustc_middle::mir::syntax` definitions. -/
namespace Miri.MIR

inductive IntegerKind where
  | i8 | i16 | i32 | i64 | i128 | isize
  | u8 | u16 | u32 | u64 | u128 | usize
  deriving DecidableEq, Repr

def IntegerKind.signed : IntegerKind → Bool
  | .i8 | .i16 | .i32 | .i64 | .i128 | .isize => true
  | _ => false

inductive BinOp where
  | Add | AddUnchecked | AddWithOverflow
  | Sub | SubUnchecked | SubWithOverflow
  | Mul | MulUnchecked | MulWithOverflow
  | Div | Rem | BitXor | BitAnd | BitOr
  | Shl | ShlUnchecked | Shr | ShrUnchecked
  | Eq | Lt | Le | Ne | Ge | Gt | Cmp | Offset
  deriving DecidableEq, Repr

inductive UnOp where
  | Not | Neg | PtrMetadata
  deriving DecidableEq, Repr

namespace BinOp

def ofString : String → Option BinOp
  | "Add" => some .Add | "AddUnchecked" => some .AddUnchecked
  | "AddWithOverflow" => some .AddWithOverflow
  | "Sub" => some .Sub | "SubUnchecked" => some .SubUnchecked
  | "SubWithOverflow" => some .SubWithOverflow
  | "Mul" => some .Mul | "MulUnchecked" => some .MulUnchecked
  | "MulWithOverflow" => some .MulWithOverflow
  | "Div" => some .Div | "Rem" => some .Rem
  | "BitXor" => some .BitXor | "BitAnd" => some .BitAnd | "BitOr" => some .BitOr
  | "Shl" => some .Shl | "ShlUnchecked" => some .ShlUnchecked
  | "Shr" => some .Shr | "ShrUnchecked" => some .ShrUnchecked
  | "Eq" => some .Eq | "Lt" => some .Lt | "Le" => some .Le | "Ne" => some .Ne
  | "Ge" => some .Ge | "Gt" => some .Gt | "Cmp" => some .Cmp | "Offset" => some .Offset
  | _ => none

def isOverflowing : BinOp → Bool
  | .AddWithOverflow | .SubWithOverflow | .MulWithOverflow => true
  | _ => false

def isUnchecked : BinOp → Bool
  | .AddUnchecked | .SubUnchecked | .MulUnchecked | .ShlUnchecked | .ShrUnchecked => true
  | _ => false

/-- Pinned rustc_const_eval `util::binop_left_homogeneous`. -/
def leftHomogeneous : BinOp → Bool
  | .Add | .AddUnchecked | .Sub | .SubUnchecked | .Mul | .MulUnchecked
  | .Div | .Rem | .BitXor | .BitAnd | .BitOr | .Offset
  | .Shl | .ShlUnchecked | .Shr | .ShrUnchecked => true
  | .AddWithOverflow | .SubWithOverflow | .MulWithOverflow
  | .Eq | .Ne | .Lt | .Le | .Gt | .Ge | .Cmp => false

/-- Pinned rustc_const_eval `util::binop_right_homogeneous`. -/
def rightHomogeneous : BinOp → Bool
  | .Add | .AddUnchecked | .AddWithOverflow | .Sub | .SubUnchecked | .SubWithOverflow
  | .Mul | .MulUnchecked | .MulWithOverflow | .Div | .Rem | .BitXor | .BitAnd | .BitOr
  | .Eq | .Ne | .Lt | .Le | .Gt | .Ge | .Cmp => true
  | .Offset | .Shl | .ShlUnchecked | .Shr | .ShrUnchecked => false

end BinOp

def UnOp.ofString : String → Option UnOp
  | "Not" => some .Not | "Neg" => some .Neg | "PtrMetadata" => some .PtrMetadata
  | _ => none

/-- Pinned rustc_const_eval `util::unop_homogeneous`. -/
def UnOp.homogeneous : UnOp → Bool
  | .Not | .Neg => true
  | .PtrMetadata => false

end Miri.MIR
