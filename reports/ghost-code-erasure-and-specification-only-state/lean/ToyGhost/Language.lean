/-!
# Toy language with real and ghost state

A small deterministic imperative language. Variables are either *real* (kept by
erasure, observable at run time) or *ghost* (specification-only, removed by erasure).
Statements are real unless they occur inside a `ghost` block or assign a ghost
variable; erasure (see `ToyGhost.Ghost`) deletes exactly those ghost statements.

The model is meant to capture, in miniature, the ghost fragment of deductive
verifiers such as Dafny and Why3: auxiliary variables, ghost assertions (lemma
calls), and ghost loops (inductive lemma proofs), all of which are deleted before
execution. It does not model procedures, recursion, the heap or aliasing, ghost
fields, ghost functions inside specifications, nondeterminism, exceptions or early
exits, `assume` statements, types other than inhabited integers, or concurrency.
Expressions are total: their evaluation cannot fail or diverge.
-/

namespace Toy.Ghost

/-- Program variables. `real i` is an ordinary executable variable; `ghost i` is a
specification-only variable that erasure removes. -/
inductive Var where
  | real (i : Nat)
  | ghost (i : Nat)
  deriving DecidableEq, Repr

/-- A store gives every variable, real or ghost, an integer value. -/
abbrev Store := Var → Int

/-- A real store: the values of the real variables only. This is what an observer
of the erased program can see. -/
abbrev RStore := Nat → Int

/-- The real projection of a store: forget all ghost variables. -/
def realPart (σ : Store) : RStore := fun i => σ (.real i)

/-- Pointwise update of one variable. -/
def Store.update (σ : Store) (x : Var) (v : Int) : Store :=
  fun y => if y = x then v else σ y

/-- Integer expressions. Comparisons return `1` for true and `0` for false; a
condition is true when it evaluates to a nonzero value. -/
inductive Expr where
  | lit (n : Int)
  | var (x : Var)
  | add (a b : Expr)
  | sub (a b : Expr)
  | lt (a b : Expr)
  | eq (a b : Expr)
  deriving Repr

/-- Expression evaluation in a store (total; no run-time errors in expressions). -/
def Expr.eval : Expr → Store → Int
  | .lit n, _ => n
  | .var x, σ => σ x
  | .add a b, σ => a.eval σ + b.eval σ
  | .sub a b, σ => a.eval σ - b.eval σ
  | .lt a b, σ => if a.eval σ < b.eval σ then 1 else 0
  | .eq a b, σ => if a.eval σ = b.eval σ then 1 else 0

/-- `e.ReadsOnlyReal`: the expression mentions no ghost variable (syntactic). -/
def Expr.ReadsOnlyReal : Expr → Prop
  | .lit _ => True
  | .var (.real _) => True
  | .var (.ghost _) => False
  | .add a b => a.ReadsOnlyReal ∧ b.ReadsOnlyReal
  | .sub a b => a.ReadsOnlyReal ∧ b.ReadsOnlyReal
  | .lt a b => a.ReadsOnlyReal ∧ b.ReadsOnlyReal
  | .eq a b => a.ReadsOnlyReal ∧ b.ReadsOnlyReal

/-- The store with real part `r` and every ghost variable `0`. Used to pick one
initial store per real state. -/
def Store.ofReal (r : RStore) : Store
  | .real i => r i
  | .ghost _ => 0

theorem realPart_ofReal (r : RStore) : realPart (Store.ofReal r) = r := rfl

/-- An expression that reads no ghost variable evaluates equally in stores with the
same real part. -/
theorem Expr.eval_congr_of_readsOnlyReal {e : Expr} (he : e.ReadsOnlyReal) {σ τ : Store}
    (h : realPart σ = realPart τ) : e.eval σ = e.eval τ := by
  induction e with
  | lit n => rfl
  | var v =>
    cases v with
    | real i => exact congrFun h i
    | ghost i => exact he.elim
  | add a b iha ihb => simp only [Expr.eval, iha he.1, ihb he.2]
  | sub a b iha ihb => simp only [Expr.eval, iha he.1, ihb he.2]
  | lt a b iha ihb => simp only [Expr.eval, iha he.1, ihb he.2]
  | eq a b iha ihb => simp only [Expr.eval, iha he.1, ihb he.2]

/-- Statements.

* `assert e` fails when `e` evaluates to `0`. Outside a ghost block it models a
  run-time check that survives erasure; inside a ghost block it models a
  specification assertion (for example a lemma call) that erasure deletes.
* `loop c b` is `while c do b`.
* `ghost s` marks `s` (with everything nested in it) as ghost code. In the original
  program a ghost block simply executes `s`. -/
inductive Stmt where
  | skip
  | assign (x : Var) (e : Expr)
  | assert (e : Expr)
  | seq (s t : Stmt)
  | ite (c : Expr) (s t : Stmt)
  | loop (c : Expr) (body : Stmt)
  | ghost (s : Stmt)
  deriving Repr

end Toy.Ghost
