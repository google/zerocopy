/-!
# Syntax of the toy borrow language

A straight-line imperative language over a store of integer locals with
Rust-style mutable borrows:

* `borrow r x`       — `r = &mut x` (mutable borrow of a local);
* `borrowSel r c x y` — `r = if c ≠ 0 { &mut x } else { &mut y }` (a borrow whose
  lender is selected at run time);
* `reborrow s r`     — `s = &mut *r` (reborrow through an existing borrow);
* `write r e`        — `*r = e`;
* `endBorrow r`      — the explicit end of `r`'s lifetime;
* `call s f r`       — `s = f(&mut *r)`: call a function `f` that takes one mutable
  borrow and returns a mutable borrow derived from it.

Callee bodies are lists of `Op` (no nested calls). A callee frame has no integer
locals: its only borrow at entry is its parameter, reference variable `0`, and it
returns the reference variable `ret`. Local operations (`assign`, `borrow`,
`borrowSel`, and reading a local) inside a callee body are stuck in every
semantics of this package.
-/

namespace Toy.Prophecy

/-- Integer local variables are named by natural numbers. -/
abbrev Var := Nat

/-- Reference (borrow) variables are named by natural numbers, in a namespace
separate from integer locals. -/
abbrev RefVar := Nat

/-- A store of integer locals. -/
abbrev Store := Var → Int

/-- Point update of a store. -/
def Store.set (σ : Store) (x : Var) (v : Int) : Store :=
  fun y => if y = x then v else σ y

/-- Expressions: literals, reading a local, reading through a borrow, addition. -/
inductive Expr where
  | lit (n : Int)
  | var (x : Var)
  | deref (r : RefVar)
  | add (a b : Expr)
  deriving Repr, DecidableEq

/-- Basic statements, usable both in the main program and (except for the local
operations) in callee bodies. -/
inductive Op where
  /-- `x = e` -/
  | assign (x : Var) (e : Expr)
  /-- `r = &mut x` -/
  | borrow (r : RefVar) (x : Var)
  /-- `r = if c ≠ 0 { &mut x } else { &mut y }` -/
  | borrowSel (r : RefVar) (c : Expr) (x y : Var)
  /-- `s = &mut *r` -/
  | reborrow (s r : RefVar)
  /-- `*r = e` -/
  | write (r : RefVar) (e : Expr)
  /-- end of the lifetime of `r` -/
  | endBorrow (r : RefVar)
  deriving Repr, DecidableEq

/-- A callee taking one mutable borrow (reference variable `0` of its frame) and
returning the borrow held in reference variable `ret` of its frame at the end of
`body`. -/
structure Callee where
  body : List Op
  ret : RefVar
  deriving Repr, DecidableEq

/-- The parameter of every callee is reference variable `0` of the callee frame. -/
def Callee.param : RefVar := 0

/-- Main-program statements: a basic operation, or `s = f(&mut *r)`. -/
inductive Stmt where
  | op (o : Op)
  | call (s : RefVar) (f : Callee) (r : RefVar)
  deriving Repr, DecidableEq

/-- A main program is a straight-line list of statements. -/
abbrev Prog := List Stmt

end Toy.Prophecy
