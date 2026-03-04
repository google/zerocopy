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

/--
  A proof that a number is a valid alignment (a non-zero power of two).
  This reflects Rust's requirement that all layout alignments are non-zero powers
  of two.
-/
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
instance : Sized Unit := ⟨⟩

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

/--
  A valid memory layout for a value.
  A Rust layout is defined by a size and an alignment. The alignment must be a
  power of two, and size must be a multiple of alignment.
-/
structure LayoutInfo where
  size : Nat
  align : Nat
  validAlignment : Alignment align
  sizeAligned : align ∣ size

/--
  The layout for a dynamically sized value.
  Some types in Rust, such as slices and trait objects, do not have a statically
  known size or alignment. Their layout depends on the specific value instance.
  This class provides the layout for a given value of a dynamically sized type.
-/
class ValueLayout (α : Type) where
  layout : α → LayoutInfo

/--
  The layout for a statically sized type.
  Types that implement `core::marker::Sized` have a layout that is known at
  compile time and is identical for all instances of the type. This class
  provides that static layout property.
-/
class TypeLayout (α : Type) [core.marker.Sized α] where
  layout : LayoutInfo

-- Provides a blanket implementation of `ValueLayout` for any type that has a
-- static `TypeLayout`. Because statically sized types share the same layout for
-- all values, the instance value is ignored.
instance {α : Type} [core.marker.Sized α] [tl : TypeLayout α] : ValueLayout α where
  layout _ := tl.layout

@[simp]
instance : TypeLayout Unit where
  layout := {
    size := 0
    align := 1
    validAlignment := ⟨by decide, 0, by rfl⟩
    sizeAligned := by decide
  }

/--
  The specification for `core::mem::size_of`.
  This defines the expected behavior of `size_of`: it returns the static size
  defined by the type's `TypeLayout`.
-/
abbrev size_of_spec (size_of_fun : Type → Result Aeneas.Std.Usize) : Prop :=
  ∀ (T : Type) [core.marker.Sized T] [tl : TypeLayout T],
    size_of_fun T = Result.ok (Aeneas.Std.Usize.ofNatCore tl.layout.size (by sorry))

/--
  The specification for `core::mem::align_of`.
  This defines the expected behavior of `align_of`: it returns the static
  alignment defined by the type's `TypeLayout`.
-/
abbrev align_of_spec (align_of_fun : Type → Result Aeneas.Std.Usize) : Prop :=
  ∀ (T : Type) [core.marker.Sized T] [tl : TypeLayout T],
    align_of_fun T = Result.ok (Aeneas.Std.Usize.ofNatCore tl.layout.align (by sorry))

/--
  Dynamically registers specifications for built-in functions (like `size_of`
  and `align_of`) as `@[simp]` axioms if Aeneas has translated them.
  This macro uses `mkIdent` to construct the identifiers exactly as they appear
  in the Aeneas output environment, bypassing macro hygiene.
-/
elab "inject_builtins" : command => do
  let env ← getEnv
  
  if env.contains `core.mem.size_of then
    let ident := mkIdent `core.mem.size_of
    let cmd ← `(command| @[simp] axiom core_mem_size_of_spec : size_of_spec $ident)
    elabCommand cmd
    
  if env.contains `core.mem.align_of then
    let ident := mkIdent `core.mem.align_of
    let cmd ← `(command| @[simp] axiom core_mem_align_of_spec : align_of_spec $ident)
    elabCommand cmd

end Hermes