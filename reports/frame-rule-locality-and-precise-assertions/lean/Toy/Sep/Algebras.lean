import Toy.Sep.Basic

/-!
# Two small non-cancellative partial commutative monoids

These satisfy `IsSepAlgebra` (partial commutative monoids with a unit, proved
below) and fail cancellativity. They are separation algebras in the relaxed
sense that omits cancellativity, but not in the sense of definitions that make
cancellativity an axiom. They are used to show that the
cancellativity hypotheses of the precision results cannot be dropped.

* `OrAlg`: booleans under `||`, everything disjoint, unit `false`. Idempotent
  (`true ∘ true = true`), hence not cancellative. Models a "permission bit" that
  can be shared without accounting.
* `Fork`: five elements `e, p, a, b, t` with `p ∘ a = p ∘ b = t` and only the
  combinations with the unit `e` otherwise defined. Not cancellative because
  `p ∘ a = p ∘ b` with `a ≠ b`.
-/

namespace Toy.Sep

open SepStruct

/-! ## `OrAlg` -/

/-- Booleans under disjunction. -/
structure OrAlg where
  /-- The underlying bit. -/
  bit : Bool
  deriving DecidableEq

instance : SepStruct OrAlg where
  disj _ _ := True
  union x y := ⟨x.bit || y.bit⟩

/-- The unit of `OrAlg`. -/
def OrAlg.unit : OrAlg := ⟨false⟩

theorem orAlg_isSepAlgebra : IsSepAlgebra OrAlg OrAlg.unit := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _ _ _; trivial
  · intro ⟨x⟩ ⟨y⟩ _
    show (⟨x || y⟩ : OrAlg) = ⟨y || x⟩
    cases x <;> cases y <;> rfl
  · intro ⟨x⟩ ⟨y⟩ ⟨z⟩ _ _
    refine ⟨trivial, trivial, ?_⟩
    show (⟨(x || y) || z⟩ : OrAlg) = ⟨x || (y || z)⟩
    cases x <;> cases y <;> cases z <;> rfl
  · intro ⟨x⟩
    exact ⟨trivial, by cases x <;> rfl⟩

theorem orAlg_not_rightCancel : ¬ RightCancel OrAlg := by
  intro h
  have := h ⟨false⟩ ⟨true⟩ ⟨true⟩ trivial trivial rfl
  cases this

theorem orAlg_not_leftCancel : ¬ LeftCancel OrAlg := by
  intro h
  have := h ⟨false⟩ ⟨true⟩ ⟨true⟩ trivial trivial rfl
  cases this

/-! ## `Fork` -/

/-- Five-element carrier of the `Fork` algebra. -/
inductive Fork where
  | e | p | a | b | t
  deriving DecidableEq

namespace Fork

/-- Disjointness of `Fork` as a boolean function. -/
def disjB : Fork → Fork → Bool
  | .e, _ => true
  | _, .e => true
  | .p, .a => true
  | .a, .p => true
  | .p, .b => true
  | .b, .p => true
  | _, _ => false

/-- Union of `Fork` (junk value `e` on non-disjoint arguments). -/
def unionF : Fork → Fork → Fork
  | .e, x => x
  | x, .e => x
  | .p, .a => .t
  | .a, .p => .t
  | .p, .b => .t
  | .b, .p => .t
  | _, _ => .e

end Fork

instance : SepStruct Fork where
  disj x y := Fork.disjB x y = true
  union := Fork.unionF

instance (x y : Fork) : Decidable (disj x y) :=
  inferInstanceAs (Decidable (Fork.disjB x y = true))

theorem fork_isSepAlgebra : IsSepAlgebra Fork Fork.e := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y; cases x <;> cases y <;> decide
  · intro x y; cases x <;> cases y <;> decide
  · intro x y z; cases x <;> cases y <;> cases z <;> decide
  · intro x; cases x <;> decide

theorem fork_not_leftCancel : ¬ LeftCancel Fork := by
  intro h
  have := h .a .b .p (by decide) (by decide) (by decide)
  cases this

theorem fork_not_rightCancel : ¬ RightCancel Fork := by
  intro h
  have := h .a .b .p (by decide) (by decide) (by decide)
  cases this

/-- The frame used in the `Fork` counterexample: "the state is `a` or `b`". -/
def forkR : Assn Fork := fun x => x = .a ∨ x = .b

end Toy.Sep
