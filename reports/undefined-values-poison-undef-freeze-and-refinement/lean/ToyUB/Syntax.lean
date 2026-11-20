/-!
# A toy expression language for undefined values

This module fixes the syntax shared by every value model in this package, together with
the model-independent notions of *outcome*, *may reach undefined behaviour*, and
*outcome-set refinement*.

The language is a first-order expression language over `w`-bit wrapping integers with
`let`, `+`, `*`, an equality test, `if`, an explicit `freeze`, and an explicit
undefined-behaviour construct `ub` (in the spirit of an `unreachable` instruction).
The width `w` is not part of the syntax: the same program is interpreted at every width,
and integer literals are read modulo `2 ^ w`.

Inputs are the free variables of a program; a value model supplies what an input may be
bound to (a set of integers in the undef model, an integer or `poison` in the poison
model). There is no memory, no control flow other than `if`, and no loops.

No operation of the language *creates* an invalid value from valid operands: `+` and `*`
wrap modulo `2 ^ w` (there are no overflow-poison flags such as `nsw`/`nuw`, no shifts,
no division or remainder). Invalid values enter a program only through its inputs, and
undefined behaviour only through `ub` or through branching (in the poison model).
-/

namespace Toy.UB

/-- Variable names. A program's free variables are its inputs. -/
abbrev Var := Nat

/-- Expressions of the toy language.

* `var x` reads variable `x`;
* `const n` is the literal `n` read modulo `2 ^ w`;
* `add`, `mul` are wrapping addition and multiplication;
* `eq a b` is `1` if the two operands are equal and `0` otherwise, both read modulo
  `2 ^ w` (so at width `0`, where every integer is `0`, it always yields `0`);
* `ite c t e` evaluates `t` if `c` is nonzero and `e` if `c` is zero;
* `letE x a b` is `let x := a; b`;
* `freeze a` is the explicit `freeze` operation;
* `ub` is immediate undefined behaviour. -/
inductive Expr where
  | var (x : Var)
  | const (n : Nat)
  | add (a b : Expr)
  | mul (a b : Expr)
  | eq (a b : Expr)
  | ite (c t e : Expr)
  | letE (x : Var) (a b : Expr)
  | freeze (a : Expr)
  | ub
  deriving DecidableEq, Repr

namespace Expr

/-- `freeIn x e` holds when `x` occurs free in `e` (a `letE x` binder shadows `x` in its
body but not in its bound expression). -/
def freeIn (x : Var) : Expr → Bool
  | var y => x == y
  | const _ => false
  | add a b => freeIn x a || freeIn x b
  | mul a b => freeIn x a || freeIn x b
  | eq a b => freeIn x a || freeIn x b
  | ite c t e => freeIn x c || freeIn x t || freeIn x e
  | letE y a b => freeIn x a || (x != y && freeIn x b)
  | freeze a => freeIn x a
  | ub => false

/-- `FreezeFree e` holds when `e` contains no `freeze`. Freeze-free programs are the
programs of the plain poison model (without `freeze`). -/
def FreezeFree : Expr → Bool
  | var _ => true
  | const _ => true
  | add a b => FreezeFree a && FreezeFree b
  | mul a b => FreezeFree a && FreezeFree b
  | eq a b => FreezeFree a && FreezeFree b
  | ite c t e => FreezeFree c && FreezeFree t && FreezeFree e
  | letE _ a b => FreezeFree a && FreezeFree b
  | freeze _ => false
  | ub => true

/-- Positive example: `x` is free in `x + 1`. -/
theorem freeIn_example_pos : freeIn 0 (add (var 0) (const 1)) = true := by decide

/-- Negative example: `x` is not free in `let x := 1; x`, and `x` is not free in `y`. -/
theorem freeIn_example_neg :
    freeIn 0 (letE 0 (const 1) (var 0)) = false ∧ freeIn 0 (var 1) = false := by decide

/-- Positive example: `if x then x + x else 0` is freeze-free. -/
theorem freezeFree_example_pos :
    FreezeFree (ite (var 0) (add (var 0) (var 0)) (const 0)) = true := by decide

/-- Negative example: `1 + freeze x` is not freeze-free. -/
theorem freezeFree_example_neg : FreezeFree (add (const 1) (freeze (var 0))) = false := by
  decide

end Expr

/-- One possible result of evaluating an expression: undefined behaviour, or a value of the
model's value type `V`. -/
inductive Outcome (V : Type) where
  | ub
  | val (v : V)
  deriving DecidableEq, Repr

namespace Outcome

/-- `isUB o` holds when the outcome is undefined behaviour. -/
def isUB : Outcome V → Bool
  | ub => true
  | val _ => false

/-- Lifting of a value refinement relation `R t s` ("target value `t` refines source value
`s`") to single outcomes: a value outcome is related only to a value outcome, and an
undefined-behaviour outcome is related to nothing (source UB is handled one level up, in
`OutRef`). -/
def LeVal (R : V → V → Prop) : Outcome V → Outcome V → Prop
  | val t, val s => R t s
  | _, _ => False

instance (R : V → V → Prop) [DecidableRel R] : DecidableRel (LeVal R) := fun o o' =>
  match o, o' with
  | val t, val s => inferInstanceAs (Decidable (R t s))
  | ub, _ => isFalse (by simp [LeVal])
  | val _, ub => isFalse (by simp [LeVal])

end Outcome

/-- The outcome set `S` (a list read as a finite set) may reach undefined behaviour. -/
def MayUB (S : List (Outcome V)) : Prop := ∃ o ∈ S, o.isUB = true

instance (S : List (Outcome V)) : Decidable (MayUB S) := by
  unfold MayUB; infer_instance

/-- Outcome-set refinement relative to a value refinement relation `R t s`:
the target outcome set `T` refines the source outcome set `S` when either the source may
reach undefined behaviour (then any target is allowed), or every target outcome is a value
that refines some source value (in particular the target cannot reach undefined
behaviour).

"May reach UB" is existential over the source's nondeterministic choices: one UB outcome
in `S` suffices. This is the per-input refinement condition of Lopes et al. (PLDI 2021,
Section 5.2): for every target outcome, some source outcome is UB or is refined by it
(the two formulations are equivalent because the UB disjunct does not depend on the target
outcome).

The definition places no lower bound on `T`: an empty target list refines every source
(`outRef_example_empty_target`). The semantics of this package never produce an empty
outcome list in an admissible environment (`semP_ne_nil`, `semU_ne_nil`), so for every
program refinement coincides with the variant `OutRefNE` that also demands a nonempty target
whenever the source is nonempty (`refinesP_iff_outRefNE`, `refinesU_iff_outRefNE`). -/
def OutRef (R : V → V → Prop) (T S : List (Outcome V)) : Prop :=
  MayUB S ∨ ∀ o ∈ T, ∃ o' ∈ S, Outcome.LeVal R o o'

instance (R : V → V → Prop) [DecidableRel R] (T S : List (Outcome V)) :
    Decidable (OutRef R T S) := by
  unfold OutRef; infer_instance

/-- Outcome-set refinement that additionally forbids an empty target list when the source
list is nonempty and UB-free. Used only to show that the empty-target case of `OutRef` never
arises for the package's semantics (`refinesP_iff_outRefNE`, `refinesU_iff_outRefNE`). -/
def OutRefNE (R : V → V → Prop) (T S : List (Outcome V)) : Prop :=
  MayUB S ∨ ((S ≠ [] → T ≠ []) ∧ ∀ o ∈ T, ∃ o' ∈ S, Outcome.LeVal R o o')

instance (R : V → V → Prop) [DecidableRel R] (T S : List (Outcome V)) :
    Decidable (OutRefNE R T S) := by
  unfold OutRefNE; infer_instance

/-- Positive example: a source that may reach UB is refined by a target that also reaches
UB (with equality as the value relation). -/
theorem outRef_example_pos :
    OutRef (fun a b : Nat => a = b) [Outcome.ub, Outcome.val 7] [Outcome.ub] := by decide

/-- Positive example exercising the value clause: with a UB-free source `{1, 2}`, the
target `{1}` refines it (the target removes a nondeterministic choice). -/
theorem outRef_example_pos_defined :
    OutRef (fun a b : Nat => a = b) [Outcome.val 1] [Outcome.val 1, Outcome.val 2] := by
  decide

/-- Negative example: a target that may reach UB does not refine a UB-free source, and a
target value absent from the source is rejected. -/
theorem outRef_example_neg :
    ¬ OutRef (fun a b : Nat => a = b) [Outcome.ub] [Outcome.val 1] ∧
    ¬ OutRef (fun a b : Nat => a = b) [Outcome.val 2] [Outcome.val 1] := by decide

/-- Documented behaviour: an empty target list refines every source, including a UB-free
one; `OutRefNE` rejects this case. -/
theorem outRef_example_empty_target :
    OutRef (fun a b : Nat => a = b) [] [Outcome.val 1] ∧
    ¬ OutRefNE (fun a b : Nat => a = b) [] [Outcome.val 1] := by decide

/-- Positive and negative examples for `MayUB`. -/
theorem mayUB_examples :
    MayUB [Outcome.val 1, (Outcome.ub : Outcome Nat)] ∧
    ¬ MayUB [Outcome.val 1, (Outcome.val 2 : Outcome Nat)] ∧
    ¬ MayUB ([] : List (Outcome Nat)) := by decide

/-- Positive and negative examples for `Outcome.LeVal`: values are compared with `R`; an
undefined-behaviour outcome is related to nothing. -/
theorem leVal_examples :
    Outcome.LeVal (fun a b : Nat => a = b) (.val 1) (.val 1) ∧
    ¬ Outcome.LeVal (fun a b : Nat => a = b) (.val 1) (.val 2) ∧
    ¬ Outcome.LeVal (fun a b : Nat => a = b) .ub .ub ∧
    ¬ Outcome.LeVal (fun a b : Nat => a = b) (.val 1) .ub := by decide

/-- Sequential evaluation of one operand: undefined behaviour in the operand is an
outcome, and each value outcome is continued with `f`. -/
def bind1 (A : List (Outcome α)) (f : α → List (Outcome β)) : List (Outcome β) :=
  A.flatMap fun
    | .ub => [.ub]
    | .val a => f a

/-- Left-to-right evaluation of two operands. -/
def bind2 (A : List (Outcome α)) (B : List (Outcome β)) (f : α → β → List (Outcome γ)) :
    List (Outcome γ) :=
  bind1 A fun a => bind1 B fun b => f a b

/-- Update of an environment at one variable. -/
def update (ρ : Var → α) (x : Var) (v : α) : Var → α :=
  fun y => if y = x then v else ρ y

/-- All `w`-bit values, as a list (used to enumerate the possible results of `freeze`). -/
def allBV (w : Nat) : List (BitVec w) := (List.range (2 ^ w)).map (BitVec.ofNat w)

theorem mem_allBV {w : Nat} (v : BitVec w) : v ∈ allBV w := by
  unfold allBV
  rw [List.mem_map]
  exact ⟨v.toNat, List.mem_range.mpr v.isLt, by simp⟩

/-- The equality test's result: `1` if equal, `0` otherwise (both modulo `2 ^ w`). -/
def eqBit {w : Nat} (x y : BitVec w) : BitVec w := if x = y then 1#w else 0#w

/-- Examples for `eqBit`: equal operands give `1`, distinct ones `0`; at width `0` the
result is always `0` (because `1` is `0` modulo `2 ^ 0`). -/
theorem eqBit_examples :
    eqBit (1#2) (1#2) = 1#2 ∧ eqBit (1#2) (2#2) = 0#2 ∧ eqBit (0#0) (0#0) = 0#0 := by decide

end Toy.UB
