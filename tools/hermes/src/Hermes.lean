import Aeneas
import Aeneas.ScalarTac.ScalarTac
open Aeneas.Std Result

abbrev I8    := Aeneas.Std.I8
abbrev I16   := Aeneas.Std.I16
abbrev I32   := Aeneas.Std.I32
abbrev I64   := Aeneas.Std.I64
abbrev I128  := Aeneas.Std.I128
abbrev U8    := Aeneas.Std.U8
abbrev U16   := Aeneas.Std.U16
abbrev U32   := Aeneas.Std.U32
abbrev U64   := Aeneas.Std.U64
abbrev U128  := Aeneas.Std.U128

-- Helper instances for literals and operators
instance {ty} : Neg (Aeneas.Std.IScalar ty) where
  neg x := ⟨-x.bv⟩

instance {ty} : OfNat (Aeneas.Std.IScalar ty) 0 where
  ofNat := Aeneas.Std.IScalar.ofInt 0 (by cases ty <;> first | decide | scalar_tac)

instance {ty} : OfNat (Aeneas.Std.UScalar ty) 0 where
  ofNat := Aeneas.Std.UScalar.ofNat 0 (by cases ty <;> first | decide | scalar_tac)

namespace Hermes

-- 1. Result checking
-- We use Aeneas.Result

def SpecificationHolds {α : Type} (res : Result α) (post : α → Prop) : Prop :=
  match res with
  | .ok v => post v
  | .fail _ => False  -- A function satisfying spec should not fail
  | .div => False     -- A function satisfying spec should not diverge

-- 2. Struct Invariants
class IsValid (α : Type) where
  is_valid : α → Prop

-- Default: Everything is valid unless said otherwise
instance (priority := low) defaultIsValid {α : Type} : IsValid α where
  is_valid _ := True

-- 3. Trait Safety
-- (No specific helper needed, just a pattern we follow in generation)

end Hermes