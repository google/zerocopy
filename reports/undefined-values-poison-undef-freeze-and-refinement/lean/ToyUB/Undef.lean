import ToyUB.Syntax

/-!
# The undef model

A value is a *set* of `w`-bit integers: the integers that a use of the value may observe.
Every use of a variable chooses independently from the variable's set, so `x + x` with `x`
bound to `{0, 1}` may produce `1`. Operations are lifted pointwise to sets
(`{f a b | a ∈ A, b ∈ B}`), and since the two operands of an operation are separate uses
their choices are independent. `if` on a set branches nondeterministically: the
`then`-branch is possible when the set contains a nonzero integer and the `else`-branch is
possible when it contains `0`; branching on such a value is *not* undefined behaviour in
this model. `freeze` picks one element of the set and returns it as a singleton, so all
uses of a frozen value agree. `let x := a; b` binds `x` to the whole set computed by `a`,
so the uses of `x` in `b` still choose independently.

The meaning of an expression is a finite set of outcomes (UB, or a value set), represented
as a list. Nondeterminism between outcomes arises from `freeze` and from branching; the
freedom *within* one value set is the undef freedom.

Two modelling choices are deliberate and matter for the results:

* A value is an arbitrary set of integers (`USet w := BitVec w → Bool`), not a bitwise
  pattern of defined and undefined bits; this matches the power-set reading of undefined
  values in Lopes et al. (PLDI 2021, Figure 2: `P(DefinedValue)`).
* `if` commits to a branch at the level of outcomes: with `c ↦ {0, 1}`,
  `if c then 1 else 0` has the two outcomes `{1}` and `{0}`, not the single value set
  `{0, 1}` (`semU_ite_commits_example`). So `if` behaves like a conditional branch whose
  direction is chosen nondeterministically, not like a dataflow `select` whose result could
  remain an undefined value.

This is meant to capture LLVM's `undef` (each use of an undefined value may yield a
different value) in a memory-free setting. It is not LLVM IR. On branching, the LLVM 19.1.0
Language Reference contains two statements: an example discussion saying that undefined
`select` (and conditional branch) conditions "can go either way", and the rule "Branching on
an undefined value is undefined behavior". This model follows the first reading for `if`
(a nondeterministic choice, never UB); results that depend on it say so.
-/

namespace Toy.UB

/-- A value of the undef model: the set of `w`-bit integers that a use may observe,
as a membership predicate. -/
abbrev USet (w : Nat) := BitVec w → Bool

namespace USet

variable {w : Nat}

/-- The singleton `{c}`: a fully defined value. -/
def single (c : BitVec w) : USet w := fun z => decide (z = c)

/-- The pointwise image `{f a b | a ∈ A, b ∈ B}` with independent choices of `a` and `b`. -/
def map2 (f : BitVec w → BitVec w → BitVec w) (A B : USet w) : USet w :=
  fun z => decide (∃ a b, A a = true ∧ B b = true ∧ f a b = z)

/-- The set contains a nonzero integer (the `then`-branch of an `if` is possible). -/
def HasNonzero (C : USet w) : Bool := decide (∃ z, C z = true ∧ z ≠ 0#w)

/-- Value refinement in the undef model: every integer a use of the target may observe is
one a use of the source may observe. -/
def Sub (t s : USet w) : Prop := ∀ z, t z = true → s z = true

instance (t s : USet w) : Decidable (Sub t s) := by unfold Sub; infer_instance

/-- The set is nonempty. Inputs of the undef model are nonempty sets. -/
def Nonempty (A : USet w) : Prop := ∃ z, A z = true

/-- Positive example: `1 ∈ {0,1} + {0,1}` (independent choices) at width 2. -/
theorem map2_example_pos :
    map2 (· + ·) (fun z : BitVec 2 => z == 0#2 || z == 1#2) (fun z => z == 0#2 || z == 1#2)
      1#2 = true := by decide

/-- Negative example: `1 ∉ {2} * {0,1}` at width 2. -/
theorem map2_example_neg :
    map2 (· * ·) (single 2#2) (fun z : BitVec 2 => z == 0#2 || z == 1#2) 1#2 = false := by
  decide

/-- Positive example: `{1} ⊆ {0,1}`. Negative example: `{0,1} ⊄ {1}`. -/
theorem sub_examples :
    Sub (single 1#2) (fun z : BitVec 2 => z == 0#2 || z == 1#2) ∧
    ¬ Sub (fun z : BitVec 2 => z == 0#2 || z == 1#2) (single 1#2) := by decide

/-- Positive example: `{0,1}` contains a nonzero integer. Negative example: `{0}` does not. -/
theorem hasNonzero_examples :
    HasNonzero (fun z : BitVec 2 => z == 0#2 || z == 1#2) = true ∧
    HasNonzero (single 0#2) = false := by decide

/-- Positive example: `{1}` is nonempty. Negative example: the empty set is not. -/
theorem nonempty_examples :
    Nonempty (single 1#2) ∧ ¬ Nonempty (fun _ : BitVec 2 => false) := by
  refine ⟨⟨1#2, by decide⟩, ?_⟩
  rintro ⟨z, hz⟩
  exact Bool.false_ne_true hz

end USet

/-- Semantics of the undef model at width `w` in environment `ρ`: the finite set (as a
list) of possible outcomes. -/
def semU (w : Nat) : (Var → USet w) → Expr → List (Outcome (USet w))
  | ρ, .var x => [.val (ρ x)]
  | _, .const n => [.val (USet.single (BitVec.ofNat w n))]
  | ρ, .add a b => bind2 (semU w ρ a) (semU w ρ b) fun A B => [.val (USet.map2 (· + ·) A B)]
  | ρ, .mul a b => bind2 (semU w ρ a) (semU w ρ b) fun A B => [.val (USet.map2 (· * ·) A B)]
  | ρ, .eq a b => bind2 (semU w ρ a) (semU w ρ b) fun A B => [.val (USet.map2 eqBit A B)]
  | ρ, .ite c t e => bind1 (semU w ρ c) fun C =>
      (if C.HasNonzero then semU w ρ t else []) ++ (if C 0#w then semU w ρ e else [])
  | ρ, .letE x a b => bind1 (semU w ρ a) fun A => semU w (update ρ x A) b
  | ρ, .freeze a => bind1 (semU w ρ a) fun A =>
      (allBV w).filterMap fun v => if A v then some (.val (USet.single v)) else none
  | _, .ub => [.ub]

/-- An undef-model environment binds every variable to a nonempty set. -/
def UInhabited {w : Nat} (ρ : Var → USet w) : Prop := ∀ x, (ρ x).Nonempty

/-- Positive example: binding every variable to `{0}` is inhabited. Negative example:
binding every variable to the empty set is not. -/
theorem uInhabited_examples :
    UInhabited (fun _ => USet.single 0#2) ∧ ¬ UInhabited (fun _ => fun _ : BitVec 2 => false) := by
  refine ⟨fun _ => ⟨0#2, by simp [USet.single]⟩, ?_⟩
  intro h
  obtain ⟨z, hz⟩ := h 0
  exact Bool.false_ne_true hz

/-- Refinement in the undef model at width `w`: `tgt` refines `src` when, for every
environment of nonempty sets, the source may reach UB or every target outcome is a value
set contained in some source value set. Rewriting `src` to `tgt` is sound exactly when
`RefinesU w tgt src`. Note the argument order: the *target* comes first. -/
def RefinesU (w : Nat) (tgt src : Expr) : Prop :=
  ∀ ρ : Var → USet w, UInhabited ρ → OutRef USet.Sub (semU w ρ tgt) (semU w ρ src)

/-- `ObsU S z`: the integer `z` is observable from the outcome set `S`, i.e. it lies in
some value set of `S`. -/
def ObsU {w : Nat} (S : List (Outcome (USet w))) (z : BitVec w) : Prop :=
  ∃ o ∈ S, (match o with | .val A => A z | .ub => false) = true

instance {w : Nat} (S : List (Outcome (USet w))) (z : BitVec w) : Decidable (ObsU S z) := by
  unfold ObsU; infer_instance

/-- Positive example: `1` is observable from the outcome set `[{0,1}]`. Negative examples:
`2` is not, and nothing is observable from `[UB]`. -/
theorem obsU_examples :
    ObsU [.val (fun z : BitVec 2 => z == 0#2 || z == 1#2)] 1#2 ∧
    ¬ ObsU [.val (fun z : BitVec 2 => z == 0#2 || z == 1#2)] 2#2 ∧
    ¬ ObsU ([.ub] : List (Outcome (USet 2))) 0#2 := by decide

/-- *Observational* refinement in the undef model: compares only the integers a whole
program may produce (and UB), forgetting how they are grouped into value sets. Included to
show that this tempting notion is not a congruence (see `ToyUB.Refinement`); it is not the
package's notion of refinement. -/
def ObsRefinesU (w : Nat) (tgt src : Expr) : Prop :=
  ∀ ρ : Var → USet w, UInhabited ρ →
    MayUB (semU w ρ src) ∨
      (¬ MayUB (semU w ρ tgt) ∧ ∀ z, ObsU (semU w ρ tgt) z → ObsU (semU w ρ src) z)

/-- Positive example: `1` observationally refines `1`. Negative example: `2` does not
observationally refine `1` (width 2, any inhabited environment, e.g. all variables `↦ {0}`). -/
theorem obsRefinesU_examples :
    ObsRefinesU 2 (.const 1) (.const 1) ∧ ¬ ObsRefinesU 2 (.const 2) (.const 1) := by
  refine ⟨fun ρ _ => Or.inr ⟨?_, fun z h => h⟩, fun h => ?_⟩
  · rintro ⟨o, ho, hu⟩
    simp only [semU, List.mem_singleton] at ho
    subst ho
    exact Bool.false_ne_true hu
  · have h' := h (fun _ => USet.single 0#2) (fun _ => ⟨0#2, by simp [USet.single]⟩)
    revert h'
    decide

section examples

/-- The width-2 environment binding variable `0` to `{0,1}` and everything else to `{1}`. -/
def ρ01 : Var → USet 2 := fun v => if v = 0 then (fun z => z == 0#2 || z == 1#2) else USet.single 1#2

/-- Positive example (re-choice at every use): with `x ↦ {0,1}`, `x + x` has a value set
containing the odd integer `1`. -/
theorem semU_example_pos :
    ∃ o ∈ semU 2 ρ01 (.add (.var 0) (.var 0)),
      (match o with | .val A => A 1#2 | .ub => false) = true := by decide

/-- Negative example (a frozen value is fixed): with `x ↦ {0,1}`, no outcome of
`let a := freeze x; a + a` contains `1`. -/
theorem semU_example_neg :
    ∀ o ∈ semU 2 ρ01 (.letE 1 (.freeze (.var 0)) (.add (.var 1) (.var 1))),
      (match o with | .val A => A 1#2 | .ub => true) = false := by decide

/-- Positive example: branching on `{0,1}` is not UB and both branches are possible:
`if x then 1 else 2` has no UB outcome and has outcomes containing `1` and `2`. -/
theorem semU_example_branch :
    ¬ MayUB (semU 2 ρ01 (.ite (.var 0) (.const 1) (.const 2))) ∧
    (∃ o ∈ semU 2 ρ01 (.ite (.var 0) (.const 1) (.const 2)),
      Outcome.LeVal USet.Sub (.val (USet.single 1#2)) o) ∧
    (∃ o ∈ semU 2 ρ01 (.ite (.var 0) (.const 1) (.const 2)),
      Outcome.LeVal USet.Sub (.val (USet.single 2#2)) o) := by
  decide

theorem ρ01_inhabited : UInhabited ρ01 := by
  intro v
  by_cases h : v = 0
  · exact ⟨0#2, by simp [ρ01, h]⟩
  · exact ⟨1#2, by simp [ρ01, h, USet.single]⟩

/-- `if` commits to a branch at the level of outcomes: with `x ↦ {0,1}`, no outcome of
`if x then 1 else 0` contains both `0` and `1`, so rewriting `if x then 1 else 0` to `x`
is not a refinement in the undef model (the target's value set `{0,1}` lies in no single
source value set). A dataflow `select` returning an undefined value would behave
differently; `select` is not part of the language. -/
theorem semU_ite_commits_example :
    (∀ o ∈ semU 2 ρ01 (.ite (.var 0) (.const 1) (.const 0)),
      (match o with | .val A => A 0#2 && A 1#2 | .ub => false) = false) ∧
    ¬ RefinesU 2 (.var 0) (.ite (.var 0) (.const 1) (.const 0)) := by
  refine ⟨by decide, fun h => ?_⟩
  have h' := h ρ01 ρ01_inhabited
  revert h'
  decide

end examples

end Toy.UB
