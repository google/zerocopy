/-!
# Propositional CNF: literals, clauses, formulas, and their semantics

A Mathlib-free toy model of the clausal setting used by SAT solvers and by the
DRAT / LRAT proof formats. Variables are natural numbers, a literal is a variable
together with a polarity, a clause is a list of literals (read as a disjunction),
and a formula is a list of clauses (read as a conjunction). Total assignments are
functions `Nat → Bool`.
-/

namespace Toy.Drat

/-- A literal: a propositional variable `var` with polarity `pos` (`true` means the
positive literal `x`, `false` the negative literal `¬x`). This captures the DIMACS
literal `±(var)` without the "nonzero integer" side condition. -/
structure Lit where
  var : Nat
  pos : Bool
  deriving DecidableEq, Repr

/-- Positive literal of variable `v`. -/
def Lit.p (v : Nat) : Lit := ⟨v, true⟩
/-- Negative literal of variable `v`. -/
def Lit.n (v : Nat) : Lit := ⟨v, false⟩

/-- Complement of a literal (same variable, opposite polarity). -/
def Lit.neg (l : Lit) : Lit := ⟨l.var, !l.pos⟩

/-- A total truth assignment. -/
abbrev Assignment := Nat → Bool

/-- Truth value of a literal under a total assignment. -/
def Lit.eval (a : Assignment) (l : Lit) : Bool := a l.var == l.pos

/-- A clause: a disjunction of literals. -/
abbrev Clause := List Lit

/-- A CNF formula: a conjunction of clauses. -/
abbrev Formula := List Clause

/-- Truth value of a clause: some literal is true. The empty clause is false. -/
def Clause.eval (a : Assignment) (C : Clause) : Bool := C.any (Lit.eval a)

/-- Truth value of a formula: every clause is true. The empty formula is true. -/
def Formula.eval (a : Assignment) (F : Formula) : Bool := F.all (Clause.eval a)

/-- `a` is a model of `F`. -/
def Satisfies (a : Assignment) (F : Formula) : Prop := F.eval a = true

instance (a : Assignment) (F : Formula) : Decidable (Satisfies a F) :=
  inferInstanceAs (Decidable (F.eval a = true))

/-- `F` has a model. -/
def Satisfiable (F : Formula) : Prop := ∃ a, Satisfies a F

/-- Semantic entailment of a clause: every model of `F` satisfies `C`. -/
def Entails (F : Formula) (C : Clause) : Prop :=
  ∀ a, Satisfies a F → C.eval a = true

/-- Logical equivalence of formulas: the same models. -/
def Equivalent (F G : Formula) : Prop := ∀ a, Satisfies a F ↔ Satisfies a G

/-- Equisatisfiability: one is satisfiable iff the other is. -/
def Equisatisfiable (F G : Formula) : Prop := Satisfiable F ↔ Satisfiable G

/-! ## Basic lemmas -/

@[simp] theorem Lit.neg_neg (l : Lit) : l.neg.neg = l := by
  cases l with
  | mk v b => cases b <;> rfl

@[simp] theorem Lit.neg_var (l : Lit) : l.neg.var = l.var := rfl

theorem Lit.neg_ne_self (l : Lit) : l.neg ≠ l := by
  cases l with
  | mk v b => cases b <;> simp [Lit.neg]

theorem Lit.eval_neg (a : Assignment) (l : Lit) : l.neg.eval a = !(l.eval a) := by
  cases l with
  | mk v b =>
    simp only [Lit.eval, Lit.neg]
    cases a v <;> cases b <;> rfl

/-- Two literals over the same variable are equal or complementary. -/
theorem Lit.eq_or_eq_neg_of_var_eq {m p : Lit} (h : m.var = p.var) : m = p ∨ m = p.neg := by
  cases m with
  | mk v b =>
    cases p with
    | mk w c =>
      simp only at h
      subst h
      cases b <;> cases c <;> simp [Lit.neg]

theorem Clause.eval_eq_true_iff (a : Assignment) (C : Clause) :
    C.eval a = true ↔ ∃ l ∈ C, l.eval a = true := by
  simp [Clause.eval, List.any_eq_true]

theorem Clause.eval_eq_false_iff (a : Assignment) (C : Clause) :
    C.eval a = false ↔ ∀ l ∈ C, l.eval a = false := by
  simp [Clause.eval, List.any_eq_false]

theorem Satisfies_iff (a : Assignment) (F : Formula) :
    Satisfies a F ↔ ∀ C ∈ F, C.eval a = true := by
  simp [Satisfies, Formula.eval, List.all_eq_true]

theorem Satisfies_cons (a : Assignment) (C : Clause) (F : Formula) :
    Satisfies a (C :: F) ↔ C.eval a = true ∧ Satisfies a F := by
  simp [Satisfies, Formula.eval]

/-- A model of a formula is a model of any formula whose clauses all occur in it. -/
theorem Satisfies_of_subset {a : Assignment} {F G : Formula}
    (hsub : ∀ C ∈ G, C ∈ F) (h : Satisfies a F) : Satisfies a G := by
  rw [Satisfies_iff] at h ⊢
  exact fun C hC => h C (hsub C hC)

/-- Adding `C` to `F` preserves logical equivalence exactly when `F` entails `C`. This holds for
every `F` and `C`; no propagation notion is involved. -/
theorem equivalent_cons_iff_entails (F : Formula) (C : Clause) :
    Equivalent (C :: F) F ↔ Entails F C := by
  constructor
  · intro heq a ha
    exact ((Satisfies_cons a C F).1 ((heq a).2 ha)).1
  · intro hent a
    rw [Satisfies_cons]
    exact ⟨fun h => h.2, fun ha => ⟨hent a ha, ha⟩⟩

/-- No assignment satisfies a formula containing the empty clause. -/
theorem not_satisfiable_of_nil_mem {F : Formula} (h : [] ∈ F) : ¬ Satisfiable F := by
  rintro ⟨a, ha⟩
  have := (Satisfies_iff a F).1 ha [] h
  simp [Clause.eval] at this

/-! ## Examples -/

section Examples
open Lit

/-- Positive example: `x₀` is true under the all-true assignment. -/
theorem Lit.eval_example_pos : (Lit.p 0).eval (fun _ => true) = true := by decide
/-- Negative example: `¬x₀` is false under the all-true assignment. -/
theorem Lit.eval_example_neg : (Lit.n 0).eval (fun _ => true) = false := by decide
/-- Example: complement swaps polarity. -/
theorem Lit.neg_example : (Lit.p 3).neg = Lit.n 3 := rfl

/-- Positive example: `x₀ ∨ x₁` is satisfied when only `x₁` is true. -/
theorem Clause.eval_example_pos : Clause.eval (fun v => v == 1) [Lit.p 0, Lit.p 1] = true := by
  decide
/-- Negative example: the empty clause is false under every assignment. -/
theorem Clause.eval_nil (a : Assignment) : Clause.eval a [] = false := rfl

/-- Positive example: `(x₀ ∨ x₁) ∧ ¬x₀` is satisfiable (take `x₁` true, `x₀` false). -/
theorem Satisfiable_example_pos : Satisfiable [[Lit.p 0, Lit.p 1], [Lit.n 0]] :=
  ⟨fun v => v == 1, by decide⟩

/-- Negative example: `x₀ ∧ ¬x₀` is unsatisfiable. -/
theorem Satisfiable_example_neg : ¬ Satisfiable [[Lit.p 0], [Lit.n 0]] := by
  rintro ⟨a, ha⟩
  simp only [Satisfies, Formula.eval, Clause.eval, Lit.eval, Lit.p, Lit.n, List.all_cons,
    List.any_cons, List.any_nil, List.all_nil, Bool.or_false, Bool.and_true] at ha
  cases h : a 0 <;> simp [h] at ha

/-- Positive example: `x₀ ∧ (¬x₀ ∨ x₁)` entails `x₁`. -/
theorem Entails_example_pos : Entails [[Lit.p 0], [Lit.n 0, Lit.p 1]] [Lit.p 1] := by
  intro a ha
  simp only [Satisfies, Formula.eval, Clause.eval, Lit.eval, Lit.p, Lit.n, List.all_cons,
    List.any_cons, List.any_nil, List.all_nil, Bool.or_false, Bool.and_true] at ha ⊢
  cases h0 : a 0 <;> cases h1 : a 1 <;> simp_all

/-- Negative example: `x₀ ∨ x₁` does not entail `x₀`. -/
theorem Entails_example_neg : ¬ Entails [[Lit.p 0, Lit.p 1]] [Lit.p 0] := by
  intro h
  have := h (fun v => v == 1) (by decide)
  exact absurd this (by decide)

/-- Positive example: `x₀ ∧ x₀` is equivalent to `x₀`. -/
theorem Equivalent_example_pos : Equivalent [[Lit.p 0], [Lit.p 0]] [[Lit.p 0]] := by
  intro a
  simp [Satisfies, Formula.eval]

/-- Negative example: the empty formula is not equivalent to `x₀` (all-false assignment). -/
theorem Equivalent_example_neg : ¬ Equivalent [] [[Lit.p 0]] := by
  intro h
  have := (h (fun _ => false)).1 rfl
  exact absurd this (by decide)

/-- Positive example: `x₀` and `x₁` are equisatisfiable (both satisfiable) without
being equivalent. -/
theorem Equisatisfiable_example_pos : Equisatisfiable [[Lit.p 0]] [[Lit.p 1]] :=
  ⟨fun _ => ⟨fun _ => true, by decide⟩, fun _ => ⟨fun _ => true, by decide⟩⟩

/-- Negative example: the empty formula and `x₀ ∧ ¬x₀` are not equisatisfiable. -/
theorem Equisatisfiable_example_neg : ¬ Equisatisfiable [] [[Lit.p 0], [Lit.n 0]] := by
  intro h
  exact Satisfiable_example_neg (h.1 ⟨fun _ => true, rfl⟩)

end Examples

end Toy.Drat
