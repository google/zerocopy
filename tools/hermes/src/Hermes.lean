import Aeneas
import Aeneas.ScalarTac.ScalarTac
import Lean

open Aeneas.Std Result
open Lean Elab Command Term Meta

-- TODO: Maybe turn thse off and propagate warnings?
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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

-- We use `@[simp]` directly on the `SpecificationHolds` definition.
-- This unrolls the match logic for underlying results without forcing 
-- users to manually type `unfold Hermes.SpecificationHolds` uniformly across all project proofs.
@[simp]
def SpecificationHolds {α : Type} (res : Result α) (post : α → Prop) : Prop :=
  match res with
  | .ok v => post v
  | .fail _ => False  -- A function satisfying spec should not fail
  | .div => False     -- A function satisfying spec should not diverge

-- 2. Struct Invariants
class IsValid (α : Type) where
  isValid : α → Prop

-- Default: Everything is valid unless said otherwise
instance (priority := low) defaultIsValid {α : Type} : IsValid α where
  isValid _ := True

-- 3. Trait Safety
-- (No specific helper needed, just a pattern we follow in generation)

-- 4. Type Layout (Size and Alignment)
-- In Rust, Sized types have a size and an alignment.
-- The alignment is a non-zero power of two, and the size is a multiple of the alignment.

/-- Proof that a number is a valid alignment (a non-zero power of two). -/
def Alignment (n : Nat) : Prop :=
  0 < n ∧ ∃ (k : Nat), n = 2^k

namespace core
namespace marker
/--
  A stub for the `Sized` trait. In the future, this should either hook into
  exactly what Aeneas generates for `core::marker::Sized`, or Aeneas should be
  configured to rely on this definition.
-/
class Sized (α : Type)

instance : Sized Aeneas.Std.U8 := ⟨⟩
instance : Sized Aeneas.Std.U16 := ⟨⟩
instance : Sized Aeneas.Std.U32 := ⟨⟩
instance : Sized Aeneas.Std.U64 := ⟨⟩
instance : Sized Aeneas.Std.U128 := ⟨⟩
instance : Sized Aeneas.Std.Usize := ⟨⟩
instance : Sized Aeneas.Std.I8 := ⟨⟩
instance : Sized Aeneas.Std.I16 := ⟨⟩
instance : Sized Aeneas.Std.I32 := ⟨⟩
instance : Sized Aeneas.Std.I64 := ⟨⟩
instance : Sized Aeneas.Std.I128 := ⟨⟩
instance : Sized Aeneas.Std.Isize := ⟨⟩
instance : Sized Bool := ⟨⟩
instance : Sized Char := ⟨⟩

-- Structural composition
instance [Sized α] [Sized β] : Sized (α × β) := ⟨⟩

-- Metaprogramming derivation for Aeneas-generated nominal types
def deriveSizedCmd (declName : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some info := env.find? declName | throwError "unknown declaration"
  
  match info with
  | ConstantInfo.inductInfo val =>
    let ctorName := val.ctors.head!
    let some (ConstantInfo.ctorInfo ctor) := env.find? ctorName | throwError "unknown constructor"
    
    liftTermElabM do
      forallTelescope ctor.type fun fvars _ => do
        for fvar in fvars do
          let fvarType ← inferType fvar
          let sizedType ← mkAppM ``core.marker.Sized #[fvarType]
          let _inst ← synthInstance sizedType
        return ()

    let cmd ← `(instance : core.marker.Sized $(mkIdent declName) := ⟨⟩)
    elabCommand cmd
  | _ => throwError "only inductive types are supported"

elab "derive_sized " id:ident : command => do
  deriveSizedCmd id.getId

end marker
end core

/-- A valid memory layout for a value. -/
structure LayoutInfo where
  size : Nat
  align : Nat
  validAlignment : Alignment align
  sizeAligned : align ∣ size

/-- All types have a memory layout for their values, which might depend on the specific value (e.g., dynamically sized types like slices). -/
class ValueLayout (α : Type) where
  layout : α → LayoutInfo

/-- For `Sized` types, all values of the type share the same exact layout, so the layout is a property of the type itself. -/
class TypeLayout (α : Type) [core.marker.Sized α] where
  layout : LayoutInfo

instance {α : Type} [core.marker.Sized α] [tl : TypeLayout α] : ValueLayout α where
  layout _ := tl.layout

end Hermes