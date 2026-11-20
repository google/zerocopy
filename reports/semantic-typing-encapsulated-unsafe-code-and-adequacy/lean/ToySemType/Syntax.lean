/-!
# Syntax of the toy language

A call-by-value lambda calculus with natural-number constants, a comparison,
a conditional, a heap of integer cells (allocation, read, write, heap size),
and one *unsafe* primitive `cast`, which forges a cell reference from a raw
address. Variables use de Bruijn indices.

This module fixes the syntax, the value predicate, closedness, and
capture-free substitution of closed values.
-/

namespace Toy.SemType

/-- Types. `int` stands for machine words (modeled as `Nat`, like `usize`),
`ref` for references to integer cells, `arrow σ τ` for functions. There is no
type of raw pointers: the unsafe primitive `cast` has no typing rule at all. -/
inductive Ty where
  | int
  | ref
  | arrow (σ τ : Ty)
  deriving DecidableEq, Repr

/-- Expressions (de Bruijn indices).

* `var i`, `lam b`, `app f a`: the lambda calculus (call-by-value).
* `num n`: a word constant.
* `lt a b`: evaluates to `num 1` if `a < b` and to `num 0` otherwise.
* `ifz c t e`: evaluates `t` if `c` is `num 0` and `e` otherwise ("if zero").
  Since `lt a b` yields `num 1` when `a < b` and `num 0` otherwise,
  `ifz (lt a b) t e` runs `t` when `a < b` is *false* and `e` when it is true.
* `size`: the number of allocated cells (like a length query).
* `alloc a`: allocates a fresh cell initialized with the word `a`.
* `read a`, `write a b`: read / overwrite the cell referenced by `a`.
* `loc l`: a cell reference (address `l`); a runtime value with no typing rule.
* `cast a`: the unsafe primitive: turns the word `a` into the reference
  `loc a` without any validity check. It has no typing rule. -/
inductive Expr where
  | var (i : Nat)
  | lam (b : Expr)
  | app (f a : Expr)
  | num (n : Nat)
  | lt (a b : Expr)
  | ifz (c t e : Expr)
  | size
  | alloc (a : Expr)
  | read (a : Expr)
  | write (a b : Expr)
  | loc (l : Nat)
  | cast (a : Expr)
  deriving DecidableEq, Repr

namespace Expr

/-- Values: abstractions, word constants, and cell references. -/
def isValue : Expr → Bool
  | lam _ => true
  | num _ => true
  | loc _ => true
  | _ => false

/-- `closedAt n e`: every free de Bruijn index of `e` is `< n`.
`closedAt 0 e` means `e` is closed. -/
def closedAt : Nat → Expr → Bool
  | n, var i => decide (i < n)
  | n, lam b => closedAt (n + 1) b
  | n, app f a => closedAt n f && closedAt n a
  | _, num _ => true
  | n, lt a b => closedAt n a && closedAt n b
  | n, ifz c t e => closedAt n c && closedAt n t && closedAt n e
  | _, size => true
  | n, alloc a => closedAt n a
  | n, read a => closedAt n a
  | n, write a b => closedAt n a && closedAt n b
  | _, loc _ => true
  | n, cast a => closedAt n a

/-- `castFree e`: the unsafe primitive `cast` does not occur in `e`. -/
def castFree : Expr → Bool
  | var _ => true
  | lam b => castFree b
  | app f a => castFree f && castFree a
  | num _ => true
  | lt a b => castFree a && castFree b
  | ifz c t e => castFree c && castFree t && castFree e
  | size => true
  | alloc a => castFree a
  | read a => castFree a
  | write a b => castFree a && castFree b
  | loc _ => true
  | cast _ => false

/-- Simultaneous substitution under `k` binders: index `i < k` is bound and
left alone; index `k + j` is replaced by `γ[j]` when `j < γ.length`; larger
indices are renumbered down by `γ.length`. No shifting is performed on the
substituted expressions, so this is capture-free exactly when they are closed
(which is the only way it is used by the semantic model below). -/
def substAllAt (k : Nat) (γ : List Expr) : Expr → Expr
  | var i =>
    if i < k then var i
    else match γ[i - k]? with
      | some v => v
      | none => var (i - γ.length)
  | lam b => lam (substAllAt (k + 1) γ b)
  | app f a => app (substAllAt k γ f) (substAllAt k γ a)
  | num n => num n
  | lt a b => lt (substAllAt k γ a) (substAllAt k γ b)
  | ifz c t e => ifz (substAllAt k γ c) (substAllAt k γ t) (substAllAt k γ e)
  | size => size
  | alloc a => alloc (substAllAt k γ a)
  | read a => read (substAllAt k γ a)
  | write a b => write (substAllAt k γ a) (substAllAt k γ b)
  | loc l => loc l
  | cast a => cast (substAllAt k γ a)

/-- Closing substitution: `var j ↦ γ[j]`. -/
def substAll (γ : List Expr) (e : Expr) : Expr := substAllAt 0 γ e

/-- Single substitution of `v` for index `k` (used for β-reduction with `k = 0`). -/
def substAt (k : Nat) (v : Expr) (e : Expr) : Expr := substAllAt k [v] e

/-- Substituting the empty list is the identity. -/
theorem substAllAt_nil (k : Nat) (e : Expr) : substAllAt k [] e = e := by
  induction e generalizing k with
  | var i =>
    simp only [substAllAt]
    split
    · rfl
    · simp
  | lam b ih => simp [substAllAt, ih]
  | app f a ihf iha => simp [substAllAt, ihf, iha]
  | num n => rfl
  | lt a b iha ihb => simp [substAllAt, iha, ihb]
  | ifz c t e ihc iht ihe => simp [substAllAt, ihc, iht, ihe]
  | size => rfl
  | alloc a ih => simp [substAllAt, ih]
  | read a ih => simp [substAllAt, ih]
  | write a b iha ihb => simp [substAllAt, iha, ihb]
  | loc l => rfl
  | cast a ih => simp [substAllAt, ih]

theorem substAll_nil (e : Expr) : substAll [] e = e := substAllAt_nil 0 e

end Expr

end Toy.SemType
