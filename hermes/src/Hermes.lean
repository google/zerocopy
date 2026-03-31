import Aeneas
import Aeneas.Tactic.Solver.ScalarTac.ScalarTac
import Lean

open Aeneas.Std Result
open Lean Elab Command Term Meta

-- TODO: Maybe turn thse off and propagate warnings?
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
-- Helper instances for literals and operators
instance {ty} : Neg (Aeneas.Std.IScalar ty) where
  neg x := ⟨-x.bv⟩

instance {ty} : OfNat (Aeneas.Std.IScalar ty) 0 where
  ofNat := Aeneas.Std.IScalar.ofInt 0 (by cases ty <;> first | decide | scalar_tac)

instance {ty} : OfNat (Aeneas.Std.UScalar ty) 0 where
  ofNat := Aeneas.Std.UScalar.ofNat 0 (by cases ty <;> first | decide | scalar_tac)

/-- A shorthand macro to instantiate a Usize from a Nat literal and automatically prove its bounds. -/
macro "sz" n:num : term => `(Usize.ofNatCore $n (by scalar_tac))

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

instance [IsValid α] [IsValid β] : IsValid (α × β) where
  isValid
    | (a, b) => IsValid.isValid a ∧ IsValid.isValid b

instance [IsValid α] : IsValid (Option α) where
  isValid
    | none => True
    | some a => IsValid.isValid a

-- A tactic that queries the environment for the `Hermes.allow_sorry` axiom.
-- If it exists, runs `sorry`. If not, fails with the provided error string.
elab "eval_allow_sorry_or_fail" err:term : tactic => do
  let errStr := err.raw.isStrLit?.getD "Fallback verification failed."
  let env ← getEnv
  let has_sorry := env.find? `Hermes.allow_sorry |>.isSome
  if has_sorry then
    Lean.Elab.Tactic.evalTactic (← `(tactic| sorry))
  else
    throwError errStr

/-- The core theorem that mathematically decouples the WP
    into strictly orthogonal Progress and Correctness subgoals. -/
theorem wp_prove_orthogonal {α} {m : Result α} {P : α → Prop} :
  (∃ y, m = .ok y) → (∀ y, m = .ok y → P y) → WP.spec m P := by
  intro ⟨y, hy⟩ hP
  rw [hy]
  exact hP y hy

/-- A macro that evaluates progress automatically, or falls back to sorry/fail if stuck. -/
macro "eval_progress" msg:str fnc:ident : tactic =>
  `(tactic|
    (try unfold $fnc) <;>
    (try split) <;>
    first
    | exact ⟨_, rfl⟩
    | (simp_all; exact ⟨_, rfl⟩; done)
    | eval_allow_sorry_or_fail $msg)

-- A macro that Hermes auto-injects for implicit isValid proofs.
--
-- Tactic Ordering Rationale:
-- We explicitly run `simp_all` *before* attempting `scalar_tac`.
open Lean Elab Tactic in
elab "unfold_h_returns" fnc:ident : tactic => do
  let id := mkIdent `h_returns
  evalTactic (← `(tactic| try unfold $fnc at $id:ident))

open Lean Elab Tactic in
elab "split_h_returns" : tactic => do
  let id := mkIdent `h_returns
  evalTactic (← `(tactic| try split at $id:ident))

-- `simp_all` is significantly faster and aggressively clears out logical noise,
-- which solves the vast majority of trivial bounds instantly. However, `simp_all`
-- can sometimes normalize or destroy specific arithmetic structures that `scalar_tac`
-- expects. If a user finds that an implicit arithmetic bound fails here but succeeds
-- when they manually prove it using just `scalar_tac`, it is likely because the
-- preceding `simp_all` phase destroyed the arithmetic shape.
--
-- If this fallback chain completely fails, the macro intercepts the error and surfaces
-- a friendly diagnostic instructing the user to provide a manual proof via `proof (h_name):`.
macro "verify_is_valid" field:ident fnc:ident : tactic => do
  let err := "This error comes from the implicit `simp_all` proof for `" ++ field.getId.toString ++ "`. Lean cannot automatically prove that this value satisfies the `isValid` type invariant. Consider providing a manual proof via `proof (" ++ field.getId.toString ++ ")`."
  `(tactic|
    unfold_h_returns $fnc <;>
    split_h_returns <;>
    first
    | (simp_all [Hermes.IsValid.isValid]; (try scalar_tac); done)
    | (simp_all [Hermes.IsValid.isValid]; scalar_tac_preprocess; grind; done)
    | eval_allow_sorry_or_fail $(quote err))

-- A macro that Hermes auto-injects for explicit user `ensures` bounds.
-- It attempts to solve the bound automatically using `simp_all` or `scalar_tac`.
-- If compilation fails, it degrades to `sorry` (if `--allow-sorry` is enabled).
macro "verify_user_bound" field:ident fnc:ident : tactic => do
  let err := "Missing explicit proof for named bound `" ++ field.getId.toString ++ "`."
  `(tactic|
    unfold_h_returns $fnc <;>
    split_h_returns <;>
    first
    | (simp_all; done)
    | (simp_all; scalar_tac; done)
    | (simp_all; scalar_tac_preprocess; grind; done)
    | (simp_all; omega; done)
    | (simp_all; decide; done)
    | (simp_all; subst_eqs; simp_all; done)
    | (simp_all; subst_eqs; simp_all; scalar_tac; done)
    | (simp_all; subst_eqs; simp_all; omega; done)
    | (simp_all; subst_eqs; simp_all; decide; done)
    | (simp_all; subst_eqs; simp_all; scalar_tac_preprocess; omega; done)
    | (simp_all; subst_eqs; simp_all; scalar_tac_preprocess; grind; done)
    | eval_allow_sorry_or_fail $(quote err))

-- A macro that Hermes auto-injects for empty postconditions.
-- It attempts `exact ⟨⟩`. If it fails (e.g., due to a stuck weakest precondition), it emits a friendly error
-- instructing the user to provide a manual proof via `proof:`.
macro "verify_empty_post" fnc:ident : tactic => do
  let err := "Missing explicit proof for empty postcondition. The weakest precondition could not be trivially solved by `exact ⟨⟩`. Consider providing a manual proof via `proof:`."
  `(tactic|
    unfold_h_returns $fnc <;>
    split_h_returns <;>
    first
    | exact ⟨⟩
    | (simp_all; scalar_tac_preprocess; grind; done)
    | eval_allow_sorry_or_fail $(quote err))

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
def IsAlignment (n : Nat) : Prop :=
  0 < n ∧ ∃ (k : Nat), n = 2^k

/-- A validated Rust alignment, bundling the value and its proof. -/
structure Alignment where
  val : Usize
  isValid : IsAlignment val.val

@[simp] theorem Usize_ofNatCore_val {n} {h} : (Usize.ofNatCore n h).val = n := rfl
@[simp] theorem Alignment_val {val} {h} : (@Alignment.mk val h).val = val := rfl
@[simp] theorem Alignment_isValid (a : Alignment) : IsAlignment a.val.val := a.isValid

@[simp, grind .]
theorem alignment_one : IsAlignment 1 := ⟨by decide, 0, by rfl⟩

instance : Inhabited Alignment := ⟨⟨sz 1, alignment_one⟩⟩

@[simp, grind .]
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
  while keeping internal mathematical layout proofs (like `HasStaticLayout`) as
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
  A mathematically idealized memory layout for a value.

  This layout is defined by a size and an alignment. It is unbounded by the
  physical constraints of the machine, meaning that its size is not constrained
  to fit within `Usize`. It is used to reason about the layout of values whose
  sizes may exceed the maximum addressable memory.
-/
structure SpecLayout where
  size : Nat
  align : Alignment
  sizeAligned : align.val.val ∣ size

/--
  A valid physical memory layout for a value.

  This layout is defined by a size and an alignment. It is bounded by the
  physical constraints of the machine, meaning that its size is guaranteed to
  fit within the addressable memory bounds of `Usize`. It is used to represent
  the layout of a value that actually exists in physical memory.
-/
structure Layout where
  size : Usize
  align : Alignment
  sizeAligned : align.val.val ∣ size.val

/--
  A proof that a mathematical layout size is small enough to exist in physical
  memory.

  This proof establishes that the size of a mathematical layout fits within
  `Usize.max`, meaning the layout can describe a physical value.
-/
class FitsInUsize (lay : SpecLayout) : Prop where
  fits : lay.size ≤ Usize.max

/--
  Converts a mathematical layout into a physical layout.

  This conversion requires a proof that the mathematical layout fits within
  physical memory.
-/
@[simp]
def SpecLayout.toLayout (lay : SpecLayout) [FitsInUsize lay] : Layout :=
  {
    size := Usize.ofNatCore lay.size (by
      have := FitsInUsize.fits (lay := lay)
      scalar_tac),
    align := lay.align,
    sizeAligned := lay.sizeAligned
  }

/--
  Converts a valid physical layout into its corresponding mathematical layout.

  Because physical memory guarantees a layout's size easily fits within the
  address space, we can inherently prove that the resulting mathematical `SpecLayout`
  also fits in `Usize`.
-/
@[simp]
def Layout.toSpecLayout (lay : Layout) : SpecLayout :=
  { size := lay.size.val, align := lay.align, sizeAligned := lay.sizeAligned }

instance (lay : Layout) : FitsInUsize lay.toSpecLayout where
  fits := by
    dsimp [Layout.toSpecLayout]
    scalar_tac

/--
  The ability to compute a mathematically idealized layout for a runtime value.

  Some types in Rust, such as slices and trait objects, do not have a statically
  known size or alignment. Their layout depends on the specific value instance.
  This class provides the idealized, unbounded layout for a given dynamically
  sized value. Note that `layout` maps from the Lean lowering of a Rust value to
  the layout of the Rust value that it represents, not to the layout of the Lean
  value itself.
-/
class HasSpecLayout (α : Type) where
  layout : α → SpecLayout

/--
  The ability to compute a valid physical layout for a runtime value.

  Some types in Rust, such as slices and trait objects, do not have a statically
  known size or alignment. Their layout depends on the specific value instance.
  This class provides the bounded, physical layout for a given dynamically sized
  value. It requires a proof that the corresponding mathematical layout fits
  within physical memory. Note that `layout` maps from the Lean lowering of a
  Rust value to the layout of the Rust value that it represents, not to the
  layout of the Lean value itself.
-/
class HasLayout (α : Type) [HasSpecLayout α] where
  layout : (val : α) → (h : FitsInUsize (HasSpecLayout.layout val)) → Layout

/--
  A blanket implementation providing a physical layout for any value whose
  mathematical layout fits in memory.
-/
instance {α : Type} [HasSpecLayout α] : HasLayout α where
  layout val h_fits :=
    have : FitsInUsize (HasSpecLayout.layout val) := h_fits
    SpecLayout.toLayout (HasSpecLayout.layout val)

/--
  The mathematically idealized layout for values of a statically sized type.

  Types that implement `core::marker::Sized` have a layout that is known at
  compile time and is identical for all instances of the type. This class
  provides that static, unbounded layout property.
-/
class HasStaticSpecLayout (α : Type) [core.marker.Sized α] where
  layout : SpecLayout

/--
  The valid physical layout for values of a statically sized type.

  Types that implement `core::marker::Sized` have a layout that is known at
  compile time and is identical for all instances of the type. This class
  provides that static, bounded layout property, assuming the corresponding
  mathematical layout fits within physical memory.
-/
class HasStaticLayout (α : Type) [core.marker.Sized α] where
  layout : Layout

namespace HasStaticLayout

@[simp] theorem size_div_align_mul_align_nat {T : Type} [core.marker.Sized T] [l : HasStaticLayout T] :
  l.layout.size.val / l.layout.align.val.val * l.layout.align.val.val = l.layout.size.val :=
  Nat.div_mul_cancel l.layout.sizeAligned

@[simp] theorem size_div_align_mul_align_int {T : Type} [core.marker.Sized T] [l : HasStaticLayout T] :
  (l.layout.size.val : Int) / (l.layout.align.val.val : Int) * (l.layout.align.val.val : Int) = (l.layout.size.val : Int) := by
  exact_mod_cast size_div_align_mul_align_nat

end HasStaticLayout

/--
  A blanket implementation providing a physical static layout for any `Sized`
  type whose mathematical layout fits in memory.
-/
@[simp]
instance {α : Type} [core.marker.Sized α] [HasStaticSpecLayout α] [FitsInUsize (HasStaticSpecLayout.layout (α := α))] : HasStaticLayout α where
  layout := SpecLayout.toLayout (HasStaticSpecLayout.layout (α := α))

/--
  A blanket implementation providing a mathematical value layout for any type
  that has a static mathematical layout.

  Because statically sized types share the same layout for all values, the
  instance value is ignored.
-/
@[simp]
instance {α : Type} [core.marker.Sized α] [tl : HasStaticSpecLayout α] : HasSpecLayout α where
  layout _ := tl.layout

-- 5. Slice DSTs

/--
  The mathematical layout properties that are statically known for all instances
  of a slice-based dynamically-sized type (Slice DST).
-/
structure SpecSliceDstLayout where
  trailingOffset : Nat
  elementSize : Nat
  align : Alignment

/--
  Provides the static slice DST layout properties for a given type.

  This is analogous to `SpecHasStaticLayout`, but for types that are `!Sized`
  and end in a slice. It provides the unbounded, mathematical layout properties.
-/
class SpecSliceDstTypeLayout (α : Type) where
  layout : SpecSliceDstLayout

/--
  Extracts the dynamic trailing element count for a value of a Slice DST.
-/
class TrailingSlice (α : Type) where
  len : α → Nat

/-- Rounds `val` up to the nearest multiple of `align`. -/
def roundUpToAlign (val align : Nat) : Nat :=
  ((val + align - 1) / align) * align

/-- A theorem stating that rounding up always produces a value greater than or equal to the original value. -/
theorem roundUpToAlign_ge (val align : Nat) (h : 0 < align) :
  val ≤ roundUpToAlign val align := by
  dsimp [roundUpToAlign]
  have h1 : ((val + align - 1) / align) * align + (val + align - 1) % align = val + align - 1 := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod _ _
  have h2 : (val + align - 1) % align < align := Nat.mod_lt _ h
  omega

/-- A theorem stating that if the resulting padded value is non-zero, it must be at least the alignment. -/
theorem align_le_roundUpToAlign (val align : Nat) (h_val : 0 < val) (h_align : 0 < align) :
  align ≤ roundUpToAlign val align := by
  dsimp [roundUpToAlign]
  have h_val_align : align ≤ val + align - 1 := by omega
  have h_div_pos : 1 ≤ (val + align - 1) / align := Nat.div_pos h_val_align h_align
  have h_mul : 1 * align ≤ ((val + align - 1) / align) * align := Nat.mul_le_mul_right align h_div_pos
  omega








/--
  Computes the exact mathematical size of a `repr(C)` Slice DST instance.

  This computation uses the static layout information and the dynamic trailing
  element count. It is not constrained by physical memory limits.
-/
def reprCSliceDstSize (info : SpecSliceDstLayout) (elemCount : Nat) : Nat :=
  let unpaddedSize := info.trailingOffset + elemCount * info.elementSize
  roundUpToAlign unpaddedSize info.align.val.val

/--
  A theorem stating that the unpadded size rounded up to the alignment is always
  perfectly divisible by the alignment.
-/
theorem reprCSliceDstSize_aligned (info : SpecSliceDstLayout) (elemCount : Nat) :
  info.align.val.val ∣ reprCSliceDstSize info elemCount := by
  dsimp [reprCSliceDstSize, roundUpToAlign]
  exact ⟨_, Nat.mul_comm _ _⟩

/-- Marker trait for types that are explicitly `#[repr(C)]`. -/
class ReprC (α : Type)

/--
  A blanket implementation providing a mathematical value layout for `#[repr(C)]`
  Slice DSTs.

  If a type is a Slice DST, and we can extract its length, and it is `#[repr(C)]`,
  we can compute its exact mathematical size.
-/
instance {α : Type} [SpecSliceDstTypeLayout α] [ts : TrailingSlice α] [ReprC α] : HasSpecLayout α where
  layout val :=
    let staticInfo := SpecSliceDstTypeLayout.layout (α := α)
    let elemCount := ts.len val
    let dynamicSize := reprCSliceDstSize staticInfo elemCount
    {
      size := dynamicSize,
      align := staticInfo.align,
      sizeAligned := reprCSliceDstSize_aligned staticInfo elemCount
    }

/--
  A blanket implementation providing static slice DST layout properties for
  slices.

  Slices `[T]` are modeled as Slice DSTs with a trailing offset of exactly
  zero.
-/
instance {T : Type} [core.marker.Sized T] [tl : HasStaticSpecLayout T] : SpecSliceDstTypeLayout (Aeneas.Std.Slice T) where
  layout := {
    trailingOffset := 0,
    elementSize := tl.layout.size,
    align := tl.layout.align
  }

/--
  Retrieve the dynamic length of a slice value.
-/
instance {T : Type} : TrailingSlice (Aeneas.Std.Slice T) where
  len s := s.val.length

/--
  We consider slices to be `#[repr(C)]` so that they can utilize the blanket
  implementation to compute their value layout.
-/
instance {T : Type} : ReprC (Aeneas.Std.Slice T) := ⟨⟩

macro "primitive_layout " ty:ident size:num align:num align_pow:num : command => `(
  @[simp] instance : HasStaticSpecLayout $ty where
    layout := { size := $size, align := ⟨sz $align, ⟨by decide, $align_pow, by rfl⟩⟩, sizeAligned := by decide }
  instance : FitsInUsize (HasStaticSpecLayout.layout (α := $ty)) where
    fits := by dsimp [HasStaticSpecLayout.layout]; scalar_tac
)

primitive_layout Unit 0 1 0

-- 1-Byte Primitives

primitive_layout Aeneas.Std.U8 1 1 0
primitive_layout Aeneas.Std.I8 1 1 0
primitive_layout Bool 1 1 0

-- Multi-Byte Primitives
-- For multi-byte primitives (and `char`), the alignment is platform-dependent
-- but guaranteed to be a valid alignment that divides the size.

macro "primitive_multibyte_layout " ty:ident size:num align:ident divides:ident : command => `(
  @[simp] instance : HasStaticSpecLayout $ty where
    layout := { size := $size, align := $align, sizeAligned := $divides }
  instance : FitsInUsize (HasStaticSpecLayout.layout (α := $ty)) where
    fits := by dsimp [HasStaticSpecLayout.layout]; scalar_tac
)

opaque align_u16 : Alignment
@[simp] axiom align_u16_divides : align_u16.val.val ∣ 2
primitive_multibyte_layout U16 2 align_u16 align_u16_divides

opaque align_i16 : Alignment
@[simp] axiom align_i16_divides : align_i16.val.val ∣ 2
primitive_multibyte_layout I16 2 align_i16 align_i16_divides

opaque align_u32 : Alignment
@[simp] axiom align_u32_divides : align_u32.val.val ∣ 4
primitive_multibyte_layout U32 4 align_u32 align_u32_divides

opaque align_i32 : Alignment
@[simp] axiom align_i32_divides : align_i32.val.val ∣ 4
primitive_multibyte_layout I32 4 align_i32 align_i32_divides

opaque align_u64 : Alignment
@[simp] axiom align_u64_divides : align_u64.val.val ∣ 8
primitive_multibyte_layout U64 8 align_u64 align_u64_divides

opaque align_i64 : Alignment
@[simp] axiom align_i64_divides : align_i64.val.val ∣ 8
primitive_multibyte_layout I64 8 align_i64 align_i64_divides

opaque align_u128 : Alignment
@[simp] axiom align_u128_divides : align_u128.val.val ∣ 16
primitive_multibyte_layout U128 16 align_u128 align_u128_divides

opaque align_i128 : Alignment
@[simp] axiom align_i128_divides : align_i128.val.val ∣ 16
primitive_multibyte_layout I128 16 align_i128 align_i128_divides

opaque align_char : Alignment
@[simp] axiom align_char_divides : align_char.val.val ∣ 4
primitive_multibyte_layout Char 4 align_char align_char_divides

def test_has_layout : HasLayout Aeneas.Std.U16 := inferInstance

-- Architecture-Dependent Primitives
-- For `usize` and `isize`, both the size and alignment are platform-dependent.
-- However, we know they must have a valid alignment that divides their size.

opaque size_usize : Usize
opaque align_usize : Usize
@[simp] axiom align_usize_valid : IsAlignment align_usize.val
@[simp] axiom align_usize_divides_size : align_usize.val ∣ size_usize.val

@[simp]
instance : HasStaticLayout Usize where
  layout := {
    size := size_usize
    align := ⟨align_usize, align_usize_valid⟩
    sizeAligned := align_usize_divides_size
  }

@[simp]
instance : HasStaticLayout Isize where
  layout := {
    -- We reuse `size_usize` and `align_usize` because `usize` and `isize` are
    -- guaranteed to have the same layout.
    --
    -- FIXME(https://github.com/rust-lang/reference/pull/2200): Cite this once
    -- the Reference is updated.
    size := size_usize
    align := ⟨align_usize, align_usize_valid⟩
    sizeAligned := align_usize_divides_size
  }

-- Raw Pointers
-- A raw pointer (`*const T` or `*mut T`) has the same layout as `usize`.

-- A raw pointer itself is always `Sized`, regardless of whether `T` is `Sized`.
instance {T : Type} {M : Aeneas.Std.Mutability} : core.marker.Sized (Aeneas.Std.RawPtr T M) := ⟨⟩

-- For pointers to sized types (`*const T` where `T: Sized`), the layout is
-- exactly the same as `usize`.
@[simp]
instance {T : Type} [core.marker.Sized T] {M : Aeneas.Std.Mutability} : HasStaticLayout (Aeneas.Std.RawPtr T M) where
  layout := {
    size := size_usize
    align := ⟨align_usize, align_usize_valid⟩
    sizeAligned := align_usize_divides_size
  }

-- For pointers to unsized types (`*const T` where `T` is not `Sized`), the
-- Rust reference guarantees that the size and alignment are at least those of
-- a pointer to a sized type.
--
-- FIXME(https://github.com/rust-lang/reference/pull/2201): Cite the Reference
-- once it is updated.

opaque size_raw_ptr_unsized : Usize
opaque align_raw_ptr_unsized : Usize
@[simp] axiom align_raw_ptr_unsized_valid : IsAlignment align_raw_ptr_unsized.val
@[simp] axiom align_raw_ptr_unsized_divides_size : align_raw_ptr_unsized.val ∣ size_raw_ptr_unsized.val

@[simp] axiom size_raw_ptr_unsized_ge : size_raw_ptr_unsized.val ≥ size_usize.val
@[simp] axiom align_raw_ptr_unsized_ge : align_raw_ptr_unsized.val ≥ align_usize.val

-- Fallback layout for raw pointers (applies when `T` is not known to be `Sized`).
@[simp]
instance (priority := low) {T : Type} {M : Aeneas.Std.Mutability} : HasStaticLayout (Aeneas.Std.RawPtr T M) where
  layout := {
    size := size_raw_ptr_unsized
    align := ⟨align_raw_ptr_unsized, align_raw_ptr_unsized_valid⟩
    sizeAligned := align_raw_ptr_unsized_divides_size
  }

/--
  The specification for `core::mem::size_of`.
  This defines the expected behavior of `size_of`: it returns the static size
  defined by the type's `HasStaticLayout`.
-/
abbrev size_of_spec (size_of_fun : Type → Result Usize) : Prop :=
  ∀ (T : Type) [core.marker.Sized T] [tl : HasStaticLayout T],
    size_of_fun T = Result.ok tl.layout.size

/--
  The specification for `core::mem::align_of`.
  This defines the expected behavior of `align_of`: it returns the static
  alignment defined by the type's `HasStaticLayout`.
-/
abbrev align_of_spec (align_of_fun : Type → Result Usize) : Prop :=
  ∀ (T : Type) [core.marker.Sized T] [tl : HasStaticLayout T],
    align_of_fun T = Result.ok tl.layout.align.val

/--
  Dynamically registers specifications for built-in functions (like `size_of`
  and `align_of`) as `@[simp]` axioms if Aeneas has translated them.
  This macro uses `mkIdent` to construct the identifiers exactly as they appear
  in the Aeneas output environment, bypassing macro hygiene.
-/
elab "inject_builtins" : command => do
  let env ← getEnv

  let (size_of_name, align_of_name) := env.constants.fold (fun acc n _ =>
    let s := Name.toString n
    let sz' := if s.startsWith "core.mem.size_of" then some n else acc.1
    let al' := if s.startsWith "core.mem.align_of" then some n else acc.2
    (sz', al')
  ) (none, none)

  if let some n := size_of_name then
    let ident := mkIdent n
    let specIdent := mkIdent `core_mem_size_of_spec
    let cmd ← `(command| @[simp] axiom $specIdent : ∀ (T : Type) [core.marker.Sized T] [tl : HasStaticLayout T], $ident T = Result.ok tl.layout.size)
    elabCommand cmd

  if let some n := align_of_name then
    let ident := mkIdent n
    let specIdent := mkIdent `core_mem_align_of_spec
    let cmd ← `(command| @[simp] axiom $specIdent : ∀ (T : Type) [core.marker.Sized T] [tl : HasStaticLayout T], $ident T = Result.ok tl.layout.align.val)
    elabCommand cmd

-- 6. Allocations
-- An allocation is a subset of program memory which is addressable from Rust,
-- and within which pointer arithmetic is possible.

-- We define opaque platform-dependent bounds based on the size of a pointer.
@[simp, grind .] axiom size_usize_ge_2 : size_usize.val ≥ 2

-- The max values for usize and isize are defined in terms of pointer width.
@[simp, grind .] axiom usize_max_eq : Usize.max = 2^(size_usize.val * 8) - 1

@[simp, grind .] theorem Usize.val_le_max_algebraic (u : Aeneas.Std.Usize) :
  u.val ≤ 2 ^ (size_usize.val * 8) - 1 := by
  have h_bound : u.val ≤ Aeneas.Std.Usize.max := by scalar_tac
  have h_max : Aeneas.Std.Usize.max = 2 ^ (size_usize.val * 8) - 1 := usize_max_eq
  omega

@[simp] theorem HasStaticLayout.size_le_max_algebraic {T : Type} [core.marker.Sized T] [l : HasStaticLayout T] :
  l.layout.size.val ≤ 2 ^ (size_usize.val * 8) - 1 :=
  Usize.val_le_max_algebraic l.layout.size

@[simp, grind .] axiom isize_max_eq : Isize.max = 2^(size_usize.val * 8 - 1) - 1
@[simp, grind .] axiom isize_min_eq : Isize.min = -(2^(size_usize.val * 8 - 1))

/--
  Represents a Rust allocation.
  An allocation has a base address, a size, and a set of memory addresses.
  Because there is no guarantee that an allocation is contiguous, `addresses`
  is modeled as an arbitrary `Set Nat` rather than a contiguous range.
-/
structure Allocation where
  base : Usize
  size : Usize
  addresses : Set Nat

  -- `base` is not equal to null (address 0)
  base_not_null : base.val ≠ 0

  -- `size <= isize::MAX`
  size_le_isize_max : size.val ≤ Isize.max

  -- `base + size <= usize::MAX`
  base_add_size_le_usize_max : base.val + size.val ≤ Usize.max

  -- For all addresses `a` in `addresses`, `a` is in the range `base .. (base + size)`
  bounds : ∀ a ∈ addresses, base.val ≤ a ∧ a < base.val + size.val

namespace Allocation

-- Consequence 1: `a - base` does not overflow `isize`
theorem offset_le_isize_max (alloc : Allocation) (a : Nat) (ha : a ∈ alloc.addresses) :
    a - alloc.base.val ≤ Isize.max := by
  have h_bound := alloc.bounds a ha
  have h_lt : a < alloc.base.val + alloc.size.val := h_bound.right
  have h_sub : a - alloc.base.val < alloc.size.val := by omega
  have h_size : alloc.size.val ≤ Isize.max := alloc.size_le_isize_max
  omega

-- Consequence 2: `a - base` is non-negative
-- (This is trivially true in Lean for `Nat` subtraction when `alloc.base ≤ a`,
-- which we prove here to show the offset is well-defined mathematically).
theorem offset_non_negative (alloc : Allocation) (a : Nat) (ha : a ∈ alloc.addresses) :
    alloc.base.val ≤ a :=
  (alloc.bounds a ha).left

-- Consequence 3: `base + o` will not wrap around the address space (overflow `usize`)
-- `o = a - base`, so `base + o` is just `a` if `base <= a` (which we proved above).
theorem address_le_usize_max (alloc : Allocation) (a : Nat) (ha : a ∈ alloc.addresses) :
    a ≤ Usize.max := by
  have h_bound := alloc.bounds a ha
  have h_lt : a < alloc.base.val + alloc.size.val := h_bound.right
  have h_max : alloc.base.val + alloc.size.val ≤ Usize.max := alloc.base_add_size_le_usize_max
  omega

end Allocation

-- 7. Pointer Referents
-- We define a generic representation of the memory range a pointer points to.

/--
  Retrieves the properties of a pointer's referent.
  The referent is the region of memory that the pointer addresses.
-/
structure Referent where
  -- The start address of the referent
  address : Usize
  -- The size of the referent in bytes
  size : Usize
  -- The mathematical set of addresses that make up the referent
  addresses : Set Nat

  bounds : ∀ a ∈ addresses, address.val ≤ a ∧ a < address.val + size.val

  addresses_are_usizes : ∀ a ∈ addresses, a ≤ Usize.max

instance : Nonempty Referent :=
  ⟨{ address := sz 0, size := sz 0, addresses := ∅,
     bounds := by
       intro a h
       simp at h,
     addresses_are_usizes := by
       intro a h
       simp at h }⟩

/--
  A predicate indicating that a referent's set of addresses fills the contiguous
  range `[address, address + size)`. This means every address in that range
  belongs to the referent's addresses.
-/
def Referent.IsContiguous (r : Referent) : Prop :=
  ∀ a, r.address.val ≤ a ∧ a < r.address.val + r.size.val → a ∈ r.addresses

/--
  A predicate indicating that a referent fits entirely within a given allocation.
  This means that all logical addresses of the referent are addresses allocated
  in the allocation, and the contiguous address range of the referent is
  a sub-range of the contiguous address range of the allocation.
-/
def FitsInAllocation (r : Referent) (a : Allocation) : Prop :=
  r.addresses ⊆ a.addresses ∧
  a.base.val ≤ r.address.val ∧ r.address.val + r.size.val ≤ a.base.val + a.size.val

/--
  A helper theorem proving that any address belonging to a referent that
  fits in an allocation is strictly less than the allocation's upper bound.
-/
theorem FitsInAllocation.address_bounds_alloc (r : Referent) (a : Allocation) (h : FitsInAllocation r a) (addr : Nat) (ha : addr ∈ r.addresses) :
  addr < a.base.val + a.size.val := by
  have h_subset := h.left
  have h_addr_in_alloc := h_subset ha
  exact (a.bounds _ h_addr_in_alloc).right

/--
  A class for types that act as pointers with a well-defined referent.
-/
class HasReferent (P : Type) where
  referent : P → Referent

-- We model the referent of a raw pointer via an opaque function since
-- Aeneas's value-semantics model doesn't natively expose physical addresses.
noncomputable opaque raw_ptr_referent {T : Type} {M : Aeneas.Std.Mutability} : Aeneas.Std.RawPtr T M → Referent

noncomputable instance {T : Type} {M : Aeneas.Std.Mutability} : HasReferent (Aeneas.Std.RawPtr T M) where
  referent := raw_ptr_referent

/--
  Extracts the mathematical SpecLayout from a statically sized referent.
  This allows users to immediately map from a pointer's raw referent to
  its type-level mathematical properties.
-/
def Referent.toStaticSpecLayout {T : Type} [core.marker.Sized T] [tl : HasStaticSpecLayout T] (_r : Referent) : SpecLayout :=
  tl.layout

-- 8. Pointer Metadata and Exposing Size

/--
  Extracts the metadata of a pointer.
  `P` is the pointer type.
-/
class HasMetadata (P : Type) (M : outParam Type) where
  metadata : P → M

-- Sized types have `Unit` metadata
instance {T : Type} [core.marker.Sized T] {M : Aeneas.Std.Mutability} : HasMetadata (Aeneas.Std.RawPtr T M) Unit where
  metadata _ := ()

-- A slice DST pointer has `Usize` metadata representing the number of elements
noncomputable opaque raw_slice_dst_ptr_metadata {T : Type} [SpecSliceDstTypeLayout T] {M : Aeneas.Std.Mutability} :
  Aeneas.Std.RawPtr T M → Usize

noncomputable instance {T : Type} [SpecSliceDstTypeLayout T] {M : Aeneas.Std.Mutability} :
  HasMetadata (Aeneas.Std.RawPtr T M) Usize where
  metadata := raw_slice_dst_ptr_metadata

-- Formally equatable raw definition for rewrites
theorem metadata_eq_raw_slice {T : Type} [SpecSliceDstTypeLayout T] {M : Aeneas.Std.Mutability} (val : Aeneas.Std.RawPtr T M) :
  Hermes.HasMetadata.metadata val = Hermes.raw_slice_dst_ptr_metadata val := rfl

-- If a type is Sized, its referent size is fixed
axiom referent_size_sized {T : Type} [core.marker.Sized T] [lay : HasStaticLayout T] {M : Aeneas.Std.Mutability}
  (p : Aeneas.Std.RawPtr T M) :
  (raw_ptr_referent p).size = lay.layout.size

/--
  Intrinsic structural boundary representing the Rust guarantee that an allocation bounded by `isize::MAX`
  cannot overflow `usize::MAX` during intermediate addition logic for padding calculations.
-/
axiom slice_dst_padding_no_overflow {T : Type} [ReprC T] [lay : SpecSliceDstTypeLayout T] {M : Aeneas.Std.Mutability} (val : Aeneas.Std.RawPtr T M) :
  lay.layout.trailingOffset + lay.layout.elementSize * (raw_slice_dst_ptr_metadata val).val + lay.layout.align.val ≤ Aeneas.Std.Usize.max

/--
  A theorem stating the physical size of a `repr(C)` slice DST referent.

  This axiom states that the physical size of the referent is exactly equal to
  the mathematically computed size of the slice DST (its offset plus its length
  times its element size, padded to its alignment). Because this axiom requires
  a proof that the referent fits within a valid physical allocation, it
  implicitly guarantees that the computed mathematical size fits within physical
  memory limits.
-/


axiom referent_size_slice_dst {T : Type} [ReprC T] [lay : SpecSliceDstTypeLayout T] {M : Aeneas.Std.Mutability}
  (alloc : Allocation) [md : HasMetadata (Aeneas.Std.RawPtr T M) Usize]
  (p : Aeneas.Std.RawPtr T M) (h_fits : FitsInAllocation (raw_ptr_referent p) alloc) :
  (raw_ptr_referent p).size.val = reprCSliceDstSize lay.layout (md.metadata p).val

/--
  The referent of a `*const [u8]` is always contiguous in memory.
-/
@[simp]
axiom referent_is_contiguous_slice_dst_u8
  (p : Aeneas.Std.RawPtr (Aeneas.Std.Slice Aeneas.Std.U8) Aeneas.Std.Mutability.Const) : (raw_ptr_referent p).IsContiguous
