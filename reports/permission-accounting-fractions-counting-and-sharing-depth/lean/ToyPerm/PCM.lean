/-!
# Partial commutative monoids, stated law by law

A *permission algebra* is modelled as a carrier with a partial binary operation
(`none` = undefined composite) and a designated unit. Every algebraic law is a
separate named proposition, so each theorem can name exactly the laws it uses.

This file also defines the derived notions used throughout the package:
iterated composition of a list (`opList`), exclusivity, frame-preserving
updates, and structure-preserving maps between algebras.
-/

namespace Toy.Perm

/-- A partial binary operation `op` (an undefined composite is `none`) together
with a designated unit element. This is only the signature of a partial
commutative monoid; the laws are the separate propositions below. It is meant
to capture the permission algebras of separation logics: elements are
permissions, `op a b` is the permission obtained by pooling `a` and `b`, and
`op a b = none` means that `a` and `b` cannot be held at the same time. -/
structure PartialAlg (α : Type) where
  /-- Partial composition. -/
  op : α → α → Option α
  /-- The empty permission. -/
  unit : α

namespace PartialAlg

variable {α β : Type}

/-- `a` and `b` are compatible: their composite is defined. -/
def Compat (A : PartialAlg α) (a b : α) : Prop := (A.op a b).isSome = true

instance (A : PartialAlg α) (a b : α) : Decidable (A.Compat a b) :=
  inferInstanceAs (Decidable ((A.op a b).isSome = true))

/-- Commutativity of the partial operation (definedness included). -/
def Comm (A : PartialAlg α) : Prop := ∀ a b, A.op a b = A.op b a

/-- Associativity of a partial operation in the strong (Kleene) sense:
`(a·b)·c` is defined iff `a·(b·c)` is defined, and then they are equal. -/
def Assoc (A : PartialAlg α) : Prop :=
  ∀ a b c, (A.op a b).bind (fun ab => A.op ab c) = (A.op b c).bind (fun bc => A.op a bc)

/-- Left unit law: composing with the unit is always defined and changes nothing.
(With `Comm`, this also gives the right unit law.) -/
def UnitLeft (A : PartialAlg α) : Prop := ∀ a, A.op A.unit a = some a

/-- Partial commutative monoid: commutativity, associativity and the unit law. -/
def IsPCM (A : PartialAlg α) : Prop := A.Comm ∧ A.Assoc ∧ A.UnitLeft

/-- Cancellativity: if `a·b` and `a·c` are both defined and equal, then `b = c`. -/
def Cancel (A : PartialAlg α) : Prop :=
  ∀ a b c d, A.op a b = some d → A.op a c = some d → b = c

/-- Positivity (no "anti-permissions"): if `a·b` is the unit, then `a` is the unit.
This is the form used throughout this package. Dockins, Hobor and Appel state
positivity differently (`PositiveDHA` below); the two agree in commutative,
unital, cancellative algebras (`positive_iff_positiveDHA`) but not in general
(`z2UnitAlg_positive_not_positiveDHA`). -/
def Positive (A : PartialAlg α) : Prop := ∀ a b, A.op a b = some A.unit → a = A.unit

/-- Positivity in the form of Dockins, Hobor and Appel (APLAS 2009, axiom (21)):
`a·b = c` and `c·c = c` imply `a·a = a`. -/
def PositiveDHA (A : PartialAlg α) : Prop :=
  ∀ a b c, A.op a b = some c → A.op c c = some c → A.op a a = some a

/-- The disjointness axiom of Dockins, Hobor and Appel (APLAS 2009, axiom (23)):
an element that composes with itself equals the composite, `a·a = b → a = b`.
In a cancellative algebra this says that only the unit is compatible with
itself. -/
def Disjointness (A : PartialAlg α) : Prop := ∀ a b, A.op a a = some b → a = b

/-- `a` is exclusive: the only element compatible with `a` is the unit. This
captures a write (full) permission: whoever holds it knows no other party holds
any permission to the same resource. The notion is intended for unital algebras
with at least one non-unit element: in an algebra in which nothing is compatible
with `a` (for instance one whose operation is never defined) `a` is vacuously
exclusive, and in a one-element algebra the unit is exclusive. -/
def Exclusive (A : PartialAlg α) (a : α) : Prop := ∀ b, A.Compat a b → b = A.unit

/-- Composite of a list of permissions, folding from the right:
`opList [a₁, …, aₙ] = a₁ · (a₂ · (… · (aₙ · unit)))`; `none` if any step is
undefined. It captures "all of these permissions are held simultaneously by
distinct parties, and this is what they pool to". -/
def opList (A : PartialAlg α) : List α → Option α
  | [] => some A.unit
  | a :: as => (A.opList as).bind (A.op a)

/-- A frame-preserving update from `a` to `b`: every element compatible with
`a` is compatible with `b`. A logic built on the algebra can replace `a` by `b`
by a purely local step, whatever the other parties hold. Frames are single
elements composed on the right (the unit stands for the empty frame). Any
notion of frame-preserving update that includes this single-right-frame
condition (for example additionally quantifying over left frames or over
composites of several frames) implies `FramePreserving`, so a proof that an
update is *not* `FramePreserving` refutes such notions as well;
nondeterministic (set-valued) updates are not covered. -/
def FramePreserving (A : PartialAlg α) (a b : α) : Prop := ∀ f, A.Compat a f → A.Compat b f

/-- A map sends the unit to the unit. -/
def PreservesUnit (A : PartialAlg α) (B : PartialAlg β) (f : α → β) : Prop :=
  f A.unit = B.unit

/-- A map sends every defined composite to a defined composite of the images:
`a·b = c` implies `f a · f b = f c`. This is the composition-preservation half of
a morphism of partial algebras (it says nothing about undefined composites). -/
def PreservesOp (A : PartialAlg α) (B : PartialAlg β) (f : α → β) : Prop :=
  ∀ a b c, A.op a b = some c → B.op (f a) (f b) = some (f c)

end PartialAlg

/-! ## Small reference algebras used as examples of the laws -/

/-- The two-point exclusive algebra: `false` is the empty permission, `true` the
full permission, and two full permissions cannot be combined. This is the
"whole-or-nothing" permission model of classical separation logic. -/
def exclAlg : PartialAlg Bool where
  op
    | false, b => some b
    | a, false => some a
    | true, true => none
  unit := false

/-- Addition modulo 3, a total operation with unit `0`. Dockins, Hobor and Appel
use it as their example of a separation algebra with "anti-resources"
(`1 + 2 = 0`), which positivity rules out. -/
def mod3Alg : PartialAlg (Fin 3) where
  op a b := some (a + b)
  unit := 0

/-- Boolean "or" as a total operation with unit `false`. It is idempotent, so it
is not cancellative. -/
def orAlg : PartialAlg Bool where
  op a b := some (a || b)
  unit := false

/-- A left-biased operation on `Nat` with unit `0`: `a · b = a` unless `a = 0`.
Associative with a unit, but not commutative. -/
def leftAlg : PartialAlg Nat where
  op a b := some (if a = 0 then b else a)
  unit := 0

/-- A commutative operation with unit on `Fin 3` that is not associative:
`1·1 = 2`, `2·2 = 2`, but `1·2` is undefined. -/
def nonAssocAlg : PartialAlg (Fin 3) where
  op
    | 0, b => some b
    | a, 0 => some a
    | 1, 1 => some 2
    | 2, 2 => some 2
    | _, _ => none
  unit := 0

/-- An operation that is never defined (unit `0`), violating the unit law. -/
def emptyOpAlg : PartialAlg Nat where
  op _ _ := none
  unit := 0

namespace PartialAlg

/-! ### Positive and negative examples of each law -/

/-- Positive and negative examples of `Compat`: the empty permission is
compatible with the full one; two full permissions are not compatible. -/
theorem exclAlg_compat_examples : exclAlg.Compat true false ∧ ¬ exclAlg.Compat true true := by
  decide

/-- Positive example: the exclusive algebra is commutative. -/
theorem exclAlg_comm : exclAlg.Comm := by
  intro a b; cases a <;> cases b <;> rfl

/-- Negative example: the left-biased algebra is not commutative. -/
theorem leftAlg_not_comm : ¬ leftAlg.Comm := by
  intro h; have := h 1 2; simp [leftAlg] at this

/-- Positive example: the exclusive algebra is associative. -/
theorem exclAlg_assoc : exclAlg.Assoc := by
  intro a b c; cases a <;> cases b <;> cases c <;> rfl

/-- Negative example: `nonAssocAlg` is not associative (`(1·1)·2 = 2` but
`1·(1·2)` is undefined). -/
theorem nonAssocAlg_not_assoc : ¬ nonAssocAlg.Assoc := by
  intro h; have := h 1 1 2; revert this; decide

/-- Positive example: the exclusive algebra satisfies the unit law. -/
theorem exclAlg_unitLeft : exclAlg.UnitLeft := by
  intro a; cases a <;> rfl

/-- Negative example: an operation that is never defined violates the unit law. -/
theorem emptyOpAlg_not_unitLeft : ¬ emptyOpAlg.UnitLeft := by
  intro h; have := h 0; simp [emptyOpAlg] at this

/-- Positive example: the exclusive algebra is a partial commutative monoid. -/
theorem exclAlg_isPCM : exclAlg.IsPCM := ⟨exclAlg_comm, exclAlg_assoc, exclAlg_unitLeft⟩

/-- Negative example: the left-biased algebra is not a partial commutative
monoid (it fails commutativity). -/
theorem leftAlg_not_isPCM : ¬ leftAlg.IsPCM := fun h => leftAlg_not_comm h.1

/-- Positive example: the exclusive algebra is cancellative. -/
theorem exclAlg_cancel : exclAlg.Cancel := by
  intro a b c d hb hc
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [exclAlg]

/-- Negative example: "or" is not cancellative (`true ∨ true = true ∨ false`). -/
theorem orAlg_not_cancel : ¬ orAlg.Cancel := by
  intro h; have := h true true false true rfl rfl; simp at this

/-- Positive example: the exclusive algebra is positive. -/
theorem exclAlg_positive : exclAlg.Positive := by
  intro a b h; cases a <;> cases b <;> simp_all [exclAlg]

/-- Negative example (Dockins–Hobor–Appel): addition modulo 3 is not positive,
since `1 + 2 = 0` with `1 ≠ 0`. -/
theorem mod3Alg_not_positive : ¬ mod3Alg.Positive := by
  intro h; have := h 1 2 rfl; revert this; decide

/-- Positive example: the exclusive algebra satisfies disjointness. -/
theorem exclAlg_disjointness : exclAlg.Disjointness := by
  intro a b h; cases a <;> cases b <;> simp_all [exclAlg]

/-- Negative example: addition modulo 3 violates disjointness (`1 + 1 = 2` with
`1 ≠ 2`). -/
theorem mod3Alg_not_disjointness : ¬ mod3Alg.Disjointness := by
  intro h; have := h 1 2 rfl; revert this; decide

/-- Positive example: `true` (the full permission) is exclusive in `exclAlg`. -/
theorem exclAlg_true_exclusive : exclAlg.Exclusive true := by
  intro b hb; cases b <;> simp_all [Compat, exclAlg]

/-- Negative example: in "or", `true` is not exclusive (it is compatible with
itself). -/
theorem orAlg_true_not_exclusive : ¬ orAlg.Exclusive true := by
  intro h; have := h true rfl; simp [orAlg] at this

/-- Positive example of `opList`: the empty list composes to the unit and a
two-element list composes as expected. -/
theorem opList_examples :
    exclAlg.opList [] = some false ∧ exclAlg.opList [false, true] = some true ∧
      mod3Alg.opList [1, 1, 1] = some 0 := by
  refine ⟨rfl, rfl, ?_⟩; decide

/-- Negative example of `opList`: two full permissions do not compose. -/
theorem opList_exclAlg_true_true : exclAlg.opList [true, true] = none := rfl

/-- Positive example: in `exclAlg`, `true ⇝ false` (giving up the permission) is
frame-preserving. -/
theorem exclAlg_drop_framePreserving : exclAlg.FramePreserving true false := by
  intro f _; cases f <;> rfl

/-- Negative example: in `exclAlg`, `false ⇝ true` (creating a full permission
from nothing) is not frame-preserving: the frame `true` is compatible with
`false` but not with `true`. -/
theorem exclAlg_create_not_framePreserving : ¬ exclAlg.FramePreserving false true := by
  intro h; have := h true rfl; simp [Compat, exclAlg] at this

/-- Positive example: the identity map preserves the unit and composition. -/
theorem id_preserves (A : PartialAlg α) : PreservesUnit A A id ∧ PreservesOp A A id :=
  ⟨rfl, fun _ _ _ h => h⟩

/-- Negative example: the constant map `fun _ => true` from `exclAlg` to itself
preserves neither the unit nor composition. -/
theorem const_true_not_preserves :
    ¬ PreservesUnit exclAlg exclAlg (fun _ => true) ∧
      ¬ PreservesOp exclAlg exclAlg (fun _ => true) := by
  refine ⟨by simp [PreservesUnit, exclAlg], ?_⟩
  intro h; have := h false false false rfl; simp [exclAlg] at this

/-! ### The two forms of positivity -/

/-- In a commutative, unital, cancellative algebra, positivity in the form
`a·b = unit → a = unit` is equivalent to the Dockins–Hobor–Appel form
`a·b = c → c·c = c → a·a = a`. -/
theorem positive_iff_positiveDHA (A : PartialAlg α) (hcomm : A.Comm) (hunit : A.UnitLeft)
    (hcancel : A.Cancel) : A.Positive ↔ A.PositiveDHA := by
  have hunitR : ∀ x, A.op x A.unit = some x := fun x => (hcomm x A.unit).trans (hunit x)
  constructor
  · intro hpos a b c hab hcc
    have hc : c = A.unit := hcancel c c A.unit c hcc (hunitR c)
    subst hc
    have ha : a = A.unit := hpos a b hab
    subst ha
    exact hunit A.unit
  · intro hdha a b hab
    have haa : A.op a a = some a := hdha a b A.unit hab (hunit A.unit)
    exact hcancel a a A.unit a haa (hunitR a)

end PartialAlg

/-- The group `ℤ/2ℤ = {1, 2}` (identity `2`) with a fresh unit `0` adjoined:
`1·1 = 2`, `1·2 = 2·1 = 1`, `2·2 = 2`. A total operation; not cancellative. -/
def z2UnitAlg : PartialAlg (Fin 3) where
  op
    | 0, b => some b
    | a, 0 => some a
    | 1, 1 => some 2
    | 2, 2 => some 2
    | _, _ => some 1
  unit := 0

namespace PartialAlg

/-- Positive example of `PositiveDHA`: the exclusive algebra satisfies it. -/
theorem exclAlg_positiveDHA : exclAlg.PositiveDHA := by
  intro a b c hab hcc; cases a <;> cases b <;> cases c <;> simp_all [exclAlg]

/-- Negative example of `PositiveDHA`, and the reason the two forms of
positivity are kept apart: `z2UnitAlg` is a partial commutative monoid that is
positive in the sense of `Positive` but violates `PositiveDHA` (`1·1 = 2` and
`2·2 = 2`, yet `1·1 ≠ 1`); it is not cancellative, so `positive_iff_positiveDHA`
does not apply. -/
theorem z2UnitAlg_positive_not_positiveDHA :
    z2UnitAlg.IsPCM ∧ z2UnitAlg.Positive ∧ ¬ z2UnitAlg.PositiveDHA ∧ ¬ z2UnitAlg.Cancel := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro a b; revert a b; decide
  · intro a b c; revert a b c; decide
  · intro a; revert a; decide
  · intro a b; revert a b; decide
  · intro h; have := h 1 1 2 rfl rfl; revert this; decide
  · intro h; have := h 1 0 2 1 rfl rfl; revert this; decide

end PartialAlg

end Toy.Perm
