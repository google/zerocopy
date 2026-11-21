/-!
# Toy model of packed aggregates: types, layouts, places, alignment criteria

A Mathlib-free toy model. It is meant to capture the alignment side of Rust-style
`repr(packed)` aggregates: a field of a packed aggregate may sit at an address that is not a
multiple of the field type's alignment, and creating a reference to such a field is undefined
behaviour even if the reference is never used. Nothing here mirrors a real compiler's data
structures.

Conventions (degenerate edges stated explicitly):
* "`n` divides `a`" is `n ∣ a` on `Nat`; in particular `0 ∣ a ↔ a = 0` and `1 ∣ a` always. An
  address `a` is aligned for alignment `n` iff `n ∣ a`; with `n = 0` only address `0` is aligned.
* Field offsets come from a given layout function; there is no size or overlap model (fields may
  overlap), and the layout arithmetic of `repr(C)` / `repr(packed)` is not modelled.
* `packed(0)` (`Kind.agg (some 0) fs`) is representable: its fields have effective alignment `0`,
  so a packing-respecting layout puts them at offset `0`; `PowTwoAligns` excludes it.
-/

namespace Toy.Packed

/-- Shapes of toy types.
* `scalar`: plain data without a destructor (e.g. an integer).
* `res obs`: a value with a user destructor (a `Drop` impl) that takes `&mut self`; if `obs` is
  `true` the destructor observes (prints) its own address.
* `box p`: an owning pointer to a heap value of type id `p`; freeing it takes `&mut` to the box.
* `agg pack fs`: a struct with field type ids `fs`; `pack = some n` is `packed(n)`,
  `pack = none` is a non-packed struct. -/
inductive Kind where
  | scalar
  | res (observesAddr : Bool)
  | box (pointee : Nat)
  | agg (pack : Option Nat) (fields : List Nat)
  deriving DecidableEq, Repr

/-- A type-environment entry: alignment, whether the type is sized (can be moved by value to a
temporary of statically known size), and its shape. -/
structure TyInfo where
  align : Nat
  sized : Bool
  kind : Kind
  deriving DecidableEq, Repr

/-- Out-of-range type ids denote a sized scalar of alignment 1. -/
instance : Inhabited TyInfo := ⟨{ align := 1, sized := true, kind := .scalar }⟩

/-- A type environment: type id `t` is entry `t`. -/
abbrev Env := List TyInfo

/-- The entry of type id `t` (the default sized alignment-1 scalar when out of range). -/
def Env.ty (env : Env) (t : Nat) : TyInfo := env.getD t default

/-- The alignment of type id `t`. -/
def Env.align (env : Env) (t : Nat) : Nat := (env.ty t).align

/-- The field type ids of `t` (empty unless `t` is an aggregate). -/
def Env.fields (env : Env) (t : Nat) : List Nat :=
  match (env.ty t).kind with
  | .agg _ fs => fs
  | _ => []

/-- The type id of field `j` of `t`, if any. -/
def Env.field? (env : Env) (t j : Nat) : Option Nat := (env.fields t)[j]?

/-- A layout function: `L t j` is the byte offset of field `j` inside aggregate type `t`. -/
abbrev Layout := Nat → Nat → Nat

/-- Resolve a projection path from base type `t`: the type of the projected place and its total
offset from the base address (the sum of the field offsets along the whole path). `none` if the
path does not follow the types. -/
def resolve (env : Env) (L : Layout) : Nat → List Nat → Option (Nat × Nat)
  | t, [] => some (t, 0)
  | t, j :: rest =>
    match env.field? t j with
    | some f => (resolve env L f rest).map fun r => (r.1, L t j + r.2)
    | none => none

/-- The type of the place reached from base type `t` along `path` (independent of the layout). -/
def typeAt (env : Env) : Nat → List Nat → Option Nat
  | t, [] => some t
  | t, j :: rest =>
    match env.field? t j with
    | some f => typeAt env f rest
    | none => none

/-- Effective alignment of field `j` of aggregate `t` for positioning: `min n (align f)` in a
`packed(n)` parent, `align f` in a non-packed parent, where `f` is the type of field `j`; `0` if
`t` is not an aggregate or has no field `j`. -/
def effAlign (env : Env) (t j : Nat) : Nat :=
  match (env.ty t).kind, env.field? t j with
  | .agg (some n) _, some f => min n (env.align f)
  | .agg none _, some f => env.align f
  | _, _ => 0

/-- Type-based guaranteed alignment of a place, computed along the whole projection path from the
base alignment `g`: each projection caps it at the field's effective alignment, so a `packed(n)`
parent caps it at `n`. It does not look at concrete offsets. -/
def typeGA (env : Env) : Nat → List Nat → Nat → Nat
  | _, [], g => g
  | t, j :: rest, g =>
    match env.field? t j with
    | some f => typeGA env f rest (min g (effAlign env t j))
    | none => g

/-- A place may be misaligned: some base address that is a multiple of the base alignment `A`
puts the place (at offset `o`) at an address that is not a multiple of the required alignment
`n`. -/
def Misalignable (A n o : Nat) : Prop := ∃ a, A ∣ a ∧ ¬ n ∣ a + o

/-- `n` is a power of two (so `n ≥ 1`). -/
def IsPow2 (n : Nat) : Prop := ∃ k, k < n ∧ 2 ^ k = n

instance (n : Nat) : Decidable (IsPow2 n) := by unfold IsPow2; infer_instance

/-- Every alignment and every `packed(n)` parameter in the environment is a power of two. -/
def PowTwoAligns (env : Env) : Prop :=
  ∀ t, t < env.length → IsPow2 (env.align t) ∧
    ∀ n fs, (env.ty t).kind = .agg (some n) fs → IsPow2 n

instance (env : Env) : Decidable (PowTwoAligns env) := by
  unfold PowTwoAligns
  refine @Nat.decidableBallLT _ _ (fun t _ => ?_)
  refine @instDecidableAnd _ _ _ ?_
  cases h : (env.ty t).kind with
  | agg pack fs =>
    cases pack with
    | none => exact isTrue (by intro n fs' h'; cases h')
    | some m =>
      exact decidable_of_iff (IsPow2 m) (by
        constructor
        · intro hm n fs' h'; cases h'; exact hm
        · intro hm; exact hm m fs rfl)
  | scalar => exact isTrue (by intro n fs' h'; cases h')
  | res _ => exact isTrue (by intro n fs' h'; cases h')
  | box _ => exact isTrue (by intro n fs' h'; cases h')

/-- The layout respects packing: every field offset is a multiple of the field's effective
alignment. -/
def RespectsPacking (env : Env) (L : Layout) : Prop :=
  ∀ t, t < env.length → ∀ j, j < (env.fields t).length → effAlign env t j ∣ L t j

instance (env : Env) (L : Layout) : Decidable (RespectsPacking env L) := by
  unfold RespectsPacking; infer_instance

/-- The projection steps `(t, j)` (aggregate type id, field index) taken along `path` from base
type `t`, up to the first step that does not follow the types. -/
def pathSteps (env : Env) : Nat → List Nat → List (Nat × Nat)
  | _, [] => []
  | t, j :: rest =>
    match env.field? t j with
    | some f => (t, j) :: pathSteps env f rest
    | none => []

/-- No projection step `(t, j)` occurs twice along `path` from `t0`. A path-local condition: it
holds for every path when field type ids decrease (`FieldIdsDecreasing`), and it can hold for a
particular path even in an environment whose aggregates contain themselves. -/
def NoRepeatStep (env : Env) (t0 : Nat) (path : List Nat) : Prop := (pathSteps env t0 path).Nodup

instance (env : Env) (t0 : Nat) (path : List Nat) : Decidable (NoRepeatStep env t0 path) := by
  unfold NoRepeatStep; infer_instance

/-- Every field type id of an in-range aggregate is smaller than the aggregate's own id. This is
a sufficient condition for aggregate containment to be acyclic (types listed in topological
order); it rejects acyclic environments listed in another order, and it says nothing about
`box` pointees. -/
def FieldIdsDecreasing (env : Env) : Prop :=
  ∀ t, t < env.length → ∀ f, f ∈ env.fields t → f < t

instance (env : Env) : Decidable (FieldIdsDecreasing env) := by
  unfold FieldIdsDecreasing; infer_instance

/-- Is type id `t` an owning pointer (`box`)? -/
def Env.isBox (env : Env) (t : Nat) : Bool :=
  match (env.ty t).kind with
  | .box _ => true
  | _ => false

end Toy.Packed
