import ToyUB.Syntax

/-!
# The poison model (with and without `freeze`)

A value is either a `w`-bit integer or the distinguished value `poison`. Arithmetic and the
equality test propagate `poison` (if either operand is `poison` the result is `poison`) and
do not raise undefined behaviour. Branching on `poison` is undefined behaviour.
`freeze` maps `poison` to an arbitrary but fixed integer (any of the `2 ^ w` integers is a
possible outcome) and is the identity on integers. A variable holds one value, so all uses
of a variable agree.

The *poison model* proper is this semantics restricted to freeze-free programs
(`Expr.FreezeFree`); the *poison + freeze model* is the same semantics on all programs.
On freeze-free programs the semantics is deterministic (exactly one outcome). A theorem
stated for all expressions under `semP` is a theorem about the poison + freeze model and,
as a special case, about the freeze-free poison model; cards call this the
"poison(+freeze) model".

This is meant to capture LLVM's `poison` and `freeze` in a memory-free setting. It is not
LLVM IR.
-/

namespace Toy.UB

/-- A value of the poison model. -/
inductive PVal (w : Nat) where
  | poison
  | int (v : BitVec w)
  deriving DecidableEq, Repr

namespace PVal

variable {w : Nat}

/-- Poison-propagating lifting of a binary operation. -/
def lift2 (f : BitVec w → BitVec w → BitVec w) : PVal w → PVal w → PVal w
  | int a, int b => int (f a b)
  | _, _ => poison

/-- Value refinement in the poison model: `poison` in the source may be refined by any
target value; an integer in the source only by the same integer. -/
def Refines : PVal w → PVal w → Prop
  | _, poison => True
  | t, int v => t = int v

instance : DecidableRel (Refines (w := w)) := fun t s =>
  match s with
  | poison => isTrue trivial
  | int v => inferInstanceAs (Decidable (t = int v))

/-- Positive example: an integer refines `poison`, and an integer refines itself. -/
theorem refines_example_pos : Refines (int 3#2) poison ∧ Refines (int 3#2) (int 3#2) := by
  decide

/-- Negative example: `poison` does not refine an integer, and distinct integers do not
refine each other. -/
theorem refines_example_neg : ¬ Refines (poison : PVal 2) (int 3#2) ∧
    ¬ Refines (int 1#2) (int 3#2) := by decide

end PVal

/-- Semantics of the poison model at width `w` in environment `ρ`: the finite set (as a
list) of possible outcomes. -/
def semP (w : Nat) : (Var → PVal w) → Expr → List (Outcome (PVal w))
  | ρ, .var x => [.val (ρ x)]
  | _, .const n => [.val (.int (BitVec.ofNat w n))]
  | ρ, .add a b => bind2 (semP w ρ a) (semP w ρ b) fun u v => [.val (PVal.lift2 (· + ·) u v)]
  | ρ, .mul a b => bind2 (semP w ρ a) (semP w ρ b) fun u v => [.val (PVal.lift2 (· * ·) u v)]
  | ρ, .eq a b => bind2 (semP w ρ a) (semP w ρ b) fun u v => [.val (PVal.lift2 eqBit u v)]
  | ρ, .ite c t e => bind1 (semP w ρ c) fun
      | .poison => [.ub]
      | .int z => if z ≠ 0#w then semP w ρ t else semP w ρ e
  | ρ, .letE x a b => bind1 (semP w ρ a) fun v => semP w (update ρ x v) b
  | ρ, .freeze a => bind1 (semP w ρ a) fun
      | .poison => (allBV w).map fun v => .val (.int v)
      | .int v => [.val (.int v)]
  | _, .ub => [.ub]

/-- Refinement in the poison model at width `w`: `tgt` refines `src` when, for every
environment, the source may reach UB or every target outcome is a value refining some
source value (`poison` in the source is refined by anything). Rewriting `src` to `tgt` is
sound exactly when `RefinesP w tgt src`. Note the argument order: the *target* comes
first. -/
def RefinesP (w : Nat) (tgt src : Expr) : Prop :=
  ∀ ρ : Var → PVal w, OutRef PVal.Refines (semP w ρ tgt) (semP w ρ src)

section examples

/-- The width-2 environment binding variable `0` to `poison` and everything else to `1`. -/
def ρP : Var → PVal 2 := fun v => if v = 0 then .poison else .int 1#2

/-- Positive example: poison propagates through `+` without UB, and branching on it is UB. -/
theorem semP_example_pos :
    semP 2 ρP (.add (.var 0) (.const 1)) = [.val .poison] ∧
    semP 2 ρP (.ite (.add (.var 0) (.const 1)) (.const 1) (.const 2)) = [.ub] := by decide

/-- Negative example: a branch on a defined value is not UB, and `freeze` never returns
`poison`. -/
theorem semP_example_neg :
    ¬ MayUB (semP 2 ρP (.ite (.var 1) (.var 0) (.const 2))) ∧
    (.val .poison) ∉ semP 2 ρP (.freeze (.var 0)) := by decide

/-- Positive example: `freeze poison` can produce every integer; `freeze 1` only `1`. -/
theorem semP_example_freeze :
    semP 2 ρP (.freeze (.var 0)) = [.val (.int 0#2), .val (.int 1#2), .val (.int 2#2),
      .val (.int 3#2)] ∧ semP 2 ρP (.freeze (.var 1)) = [.val (.int 1#2)] := by decide

end examples

end Toy.UB
