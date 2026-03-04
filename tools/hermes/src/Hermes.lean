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

@[simp]
theorem alignment_one : Alignment 1 := ⟨by decide, 0, by rfl⟩

@[simp]
theorem one_divides (n : Nat) : 1 ∣ n := ⟨n, by omega⟩

namespace core
namespace marker
/--
  A stub for the `Sized` trait.
  
  Currently, `Sized` is implemented as a Lean `class` to leverage Lean's
  automatic typeclass resolution for computing memory layouts. However, this is
  a temporary workaround. Aeneas translates Rust traits into explicit dictionary
  `structure`s rather than Lean typeclasses to preserve the deterministic,
  single-implementation coherence of Rust's trait resolution.
  
  Because of this mismatch, Hermes cannot currently generate valid theorem
  signatures for Rust functions that use trait bounds (the generated Lean
  functions expect explicit dictionary arguments that Hermes's typeclass-based
  approach does not supply).
  
  Once Aeneas is updated to emit marker traits like `Sized` as explicit
  dictionaries, this `class` should be removed. Hermes will then accept the
  Aeneas-generated trait dictionaries in its theorems to guarantee soundness,
  while keeping internal mathematical layout proofs (like `TypeLayout`) as
  Lean `class`es to retain automated proof synthesis.

  FIXME(https://github.com/AeneasVerif/aeneas/issues/821): Remove this and
  replace it with the Aeneas-generated trait dictionary once supported.
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
  The alignment properties of a layout.
  This contains the alignment value itself, along with a proof that it is
  a valid Rust alignment.
-/
structure AlignInfo where
  align : Nat
  validAlignment : Alignment align

/--
  A valid memory layout for a value.
  A Rust layout is defined by a size and an alignment. The alignment must be a
  power of two, and size must be a multiple of alignment.
-/
structure LayoutInfo extends AlignInfo where
  size : Nat
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

-- 5. Slice DSTs

/--
  The layout properties that are statically known for all instances of a
  slice dynamically-sized type (Slice DST).
-/
structure SliceDstLayoutInfo extends AlignInfo where
  trailingOffset : Nat
  elementSize : Nat

/--
  Provides the static slice DST layout properties for a given type.
  This is analogous to `TypeLayout`, but for types that are `!Sized`
  and end in a slice.
-/
class SliceDstTypeLayout (α : Type) where
  layout : SliceDstLayoutInfo

/--
  Extracts the dynamic trailing element count for a value of a Slice DST.
-/
class TrailingSlice (α : Type) where
  len : α → Nat

/-- Rounds `val` up to the nearest multiple of `align`. -/
def roundUpToAlign (val align : Nat) : Nat :=
  (val + align - 1) / align * align

/--
  Computes the exact size of a `repr(C)` Slice DST instance given its
  static layout info and its dynamic trailing element count.
-/
def reprCSliceDstSize (info : SliceDstLayoutInfo) (elemCount : Nat) : Nat :=
  let unpaddedSize := info.trailingOffset + elemCount * info.elementSize
  roundUpToAlign unpaddedSize info.align

/-- 
  A theorem stating that our padding function always returns a value perfectly 
  divisible by the alignment.
-/
axiom reprCSliceDstSize_aligned (info : SliceDstLayoutInfo) (elemCount : Nat) :
  info.align ∣ reprCSliceDstSize info elemCount

/-- Marker trait for types that are explicitly `#[repr(C)]`. -/
class ReprC (α : Type)

/--
  Blanket implementation: if a type is a Slice DST, and we can extract its 
  length, AND it is `#[repr(C)]`, then we can definitively compute its `ValueLayout`.
-/
instance {α : Type} [SliceDstTypeLayout α] [ts : TrailingSlice α] [ReprC α] : ValueLayout α where
  layout val :=
    let staticInfo := SliceDstTypeLayout.layout (α := α)
    let elemCount := ts.len val
    let dynamicSize := reprCSliceDstSize staticInfo elemCount
    {
      size := dynamicSize,
      align := staticInfo.align,
      validAlignment := staticInfo.validAlignment,
      sizeAligned := reprCSliceDstSize_aligned staticInfo elemCount
    }

/--
  Raw slices `[T]` are simply Slice DSTs with a trailing offset of 0.
-/
instance {T : Type} [core.marker.Sized T] [tl : TypeLayout T] : SliceDstTypeLayout (Aeneas.Std.Slice T) where
  layout := {
    trailingOffset := 0,
    elementSize := tl.layout.size,
    toAlignInfo := tl.layout.toAlignInfo
  }

/--
  Retrieve the dynamic length of a raw slice value.
-/
instance {T : Type} : TrailingSlice (Aeneas.Std.Slice T) where
  len s := s.val.length

/--
  We consider raw slices to be `#[repr(C)]` so that they can utilize the blanket
  implementation to compute their value layout.
-/
instance {T : Type} : ReprC (Aeneas.Std.Slice T) := ⟨⟩

@[simp]
instance : TypeLayout Unit where
  layout := {
    size := 0
    align := 1
    validAlignment := ⟨by decide, 0, by rfl⟩
    sizeAligned := by decide
  }

-- 1-Byte Primitives

@[simp]
instance : TypeLayout Aeneas.Std.U8 where
  layout := {
    size := 1
    align := 1
    validAlignment := ⟨by decide, 0, by rfl⟩
    sizeAligned := by decide
  }

@[simp]
instance : TypeLayout Aeneas.Std.I8 where
  layout := {
    size := 1
    align := 1
    validAlignment := ⟨by decide, 0, by rfl⟩
    sizeAligned := by decide
  }

@[simp]
instance : TypeLayout Bool where
  layout := {
    size := 1
    align := 1
    validAlignment := ⟨by decide, 0, by rfl⟩
    sizeAligned := by decide
  }

-- Multi-Byte Primitives
-- For multi-byte primitives (and `char`), the alignment is platform-dependent
-- but guaranteed to be a valid alignment that divides the size.

macro "declare_scalar_layout" tyName:ident ty:term "," size:num : command => do
  let alignName := mkIdent $ Name.mkSimple s!"align_{tyName.getId.getString!}"
  let alignValidName := mkIdent $ Name.mkSimple s!"align_{tyName.getId.getString!}_valid"
  let alignDividesName := mkIdent $ Name.mkSimple s!"align_{tyName.getId.getString!}_divides_size"
  `(
    opaque $alignName : Nat
    @[simp] axiom $alignValidName : Alignment $alignName
    @[simp] axiom $alignDividesName : $alignName ∣ $size

    @[simp]
    instance : TypeLayout $ty where
      layout := {
        size := $size
        align := $alignName
        validAlignment := $alignValidName
        sizeAligned := $alignDividesName
      }
  )

declare_scalar_layout u16 Aeneas.Std.U16, 2
declare_scalar_layout i16 Aeneas.Std.I16, 2
declare_scalar_layout u32 Aeneas.Std.U32, 4
declare_scalar_layout i32 Aeneas.Std.I32, 4
declare_scalar_layout u64 Aeneas.Std.U64, 8
declare_scalar_layout i64 Aeneas.Std.I64, 8
declare_scalar_layout u128 Aeneas.Std.U128, 16
declare_scalar_layout i128 Aeneas.Std.I128, 16
declare_scalar_layout char Char, 4

-- Architecture-Dependent Primitives
-- For `usize` and `isize`, both the size and alignment are platform-dependent.
-- However, we know they must have a valid alignment that divides their size.

opaque size_usize : Nat
opaque align_usize : Nat
@[simp] axiom align_usize_valid : Alignment align_usize
@[simp] axiom align_usize_divides_size : align_usize ∣ size_usize

@[simp]
instance : TypeLayout Usize where
  layout := {
    size := size_usize
    align := align_usize
    validAlignment := align_usize_valid
    sizeAligned := align_usize_divides_size
  }

@[simp]
instance : TypeLayout Isize where
  layout := {
    -- We reuse `size_usize` and `align_usize` because `usize` and `isize` are
    -- guaranteed to have the same layout.
    --
    -- FIXME(https://github.com/rust-lang/reference/pull/2200): Cite this once
    -- the Reference is updated.
    size := size_usize
    align := align_usize
    validAlignment := align_usize_valid
    sizeAligned := align_usize_divides_size
  }

-- Raw Pointers
-- A raw pointer (`*const T` or `*mut T`) has the same layout as `usize`.

-- A raw pointer itself is always `Sized`, regardless of whether `T` is `Sized`.
instance {T : Type} {M : Aeneas.Std.Mutability} : core.marker.Sized (Aeneas.Std.RawPtr T M) := ⟨⟩

-- For pointers to sized types (`*const T` where `T: Sized`), the layout is
-- exactly the same as `usize`.
@[simp]
instance {T : Type} [core.marker.Sized T] {M : Aeneas.Std.Mutability} : TypeLayout (Aeneas.Std.RawPtr T M) where
  layout := {
    size := size_usize
    align := align_usize
    validAlignment := align_usize_valid
    sizeAligned := align_usize_divides_size
  }

-- For pointers to unsized types (`*const T` where `T` is not `Sized`), the
-- Rust reference guarantees that the size and alignment are at least those of 
-- a pointer to a sized type.
--
-- FIXME(https://github.com/rust-lang/reference/pull/2201): Cite the Reference
-- once it is updated.

opaque size_raw_ptr_unsized : Nat
opaque align_raw_ptr_unsized : Nat
@[simp] axiom align_raw_ptr_unsized_valid : Alignment align_raw_ptr_unsized
@[simp] axiom align_raw_ptr_unsized_divides_size : align_raw_ptr_unsized ∣ size_raw_ptr_unsized

@[simp] axiom size_raw_ptr_unsized_ge : size_raw_ptr_unsized ≥ size_usize
@[simp] axiom align_raw_ptr_unsized_ge : align_raw_ptr_unsized ≥ align_usize

-- Fallback layout for raw pointers (applies when `T` is not known to be `Sized`).
@[simp]
instance (priority := low) {T : Type} {M : Aeneas.Std.Mutability} : TypeLayout (Aeneas.Std.RawPtr T M) where
  layout := {
    size := size_raw_ptr_unsized
    align := align_raw_ptr_unsized
    validAlignment := align_raw_ptr_unsized_valid
    sizeAligned := align_raw_ptr_unsized_divides_size
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