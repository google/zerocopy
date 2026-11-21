/-!
# Junk values and the human reading of total arithmetic: syntax and semantics

This file defines a small, intrinsically typed arithmetic language over `Nat` and `Int`
and gives it two kinds of semantics.

* **Total, junk-parameterized semantics** (`evalT`, `evalJ`). Every partial operation
  (natural subtraction below zero, division, remainder, `Int.toNat` of a negative) has a
  fixed *domain* on which its value is the exact mathematical value. Outside that domain
  the value is supplied by a record `J : Junk`. Lean's own operators are one specific
  record, `leanJ` (see `evalT_leanJ` and `evalJ_leanJ_iff`).
* **Human, partial semantics** (`hEvalT`, `hEval`). Terms evaluate exactly into
  `Option Int`; an operation outside its domain is undefined (`none`). Formulas evaluate
  into `Option Bool` (three truth values) under a choice of connective semantics
  (`Conn.kleene` for strong Kleene, `Conn.seq` for left-to-right sequential connectives)
  and a choice of reading of natural subtraction (`SubReading`).

The language is a toy: it models the *elaborated* form of a statement, so every cast is an
explicit `Term.cast` or `Term.toNat` node and every literal carries its sort. Surface-level
coercion insertion and numeral defaulting are outside the model.
-/

namespace Toy.Junk

/-! ## Syntax -/

/-- Sorts of the toy language: natural numbers and integers. -/
inductive Srt
  | nat
  | int
  deriving DecidableEq, Repr

/-- Carrier of a sort in the total semantics. -/
abbrev Srt.denote : Srt → Type
  | .nat => Nat
  | .int => Int

/-- Embedding of a carrier value into `Int`, used to compare total values with human
values and to evaluate relations uniformly. -/
def Srt.toInt : (s : Srt) → s.denote → Int
  | .nat, v => ((v : Nat) : Int)
  | .int, v => v

/-- Terms, indexed by their sort. `cast` is the explicit embedding `Nat → Int`
(Lean's `↑`); `toNat` is `Int.toNat`. There are no implicit coercions. -/
inductive Term : Srt → Type
  | natVar (i : Nat) : Term .nat
  | intVar (i : Nat) : Term .int
  | natLit (n : Nat) : Term .nat
  | intLit (z : Int) : Term .int
  | add {s : Srt} (t u : Term s) : Term s
  | sub {s : Srt} (t u : Term s) : Term s
  | mul {s : Srt} (t u : Term s) : Term s
  | div {s : Srt} (t u : Term s) : Term s
  | mod {s : Srt} (t u : Term s) : Term s
  | cast (t : Term .nat) : Term .int
  | toNat (t : Term .int) : Term .nat
  deriving DecidableEq, Repr

/-- The literal `0` at a given sort. -/
def zeroOf : (s : Srt) → Term s
  | .nat => .natLit 0
  | .int => .intLit 0

/-- Formulas. Atoms compare two terms of the same sort; `dvd d n` is `d ∣ n`.
Quantifiers bind a named variable of the indicated sort (`allNat x φ` is `∀ x : ℕ, φ`). -/
inductive Formula
  | eq {s : Srt} (t u : Term s)
  | le {s : Srt} (t u : Term s)
  | lt {s : Srt} (t u : Term s)
  | dvd {s : Srt} (d n : Term s)
  | not (φ : Formula)
  | and (φ ψ : Formula)
  | or (φ ψ : Formula)
  | imp (φ ψ : Formula)
  | allNat (x : Nat) (φ : Formula)
  | allInt (x : Nat) (φ : Formula)
  | exNat (x : Nat) (φ : Formula)
  | exInt (x : Nat) (φ : Formula)
  deriving DecidableEq, Repr

/-- Bounded universal quantifier `∀ x ≤ t, φ`, as sugar for `∀ x, x ≤ t → φ`.
The bound `t` lies inside the scope of the quantifier, so if `t` mentions `x` then that
occurrence refers to the bound `x`, not to an outer variable. The guard rule
`ballNat_guardedIn_iff_of_not_mentionsNat` assumes `t.mentionsNat x = false`, and
`ce_ballNat_bound_mentions_var` shows the rule fails without it. -/
def ballNat (x : Nat) (t : Term .nat) (φ : Formula) : Formula :=
  .allNat x (.imp (.le (.natVar x) t) φ)

/-- Variable environments: one valuation for natural variables and one for integer
variables. -/
structure Env where
  nat : Nat → Nat
  int : Nat → Int

/-- Rebind natural variable `x` to `v`. -/
def Env.setNat (ρ : Env) (x v : Nat) : Env :=
  ⟨fun i => if i = x then v else ρ.nat i, ρ.int⟩

/-- Rebind integer variable `x` to `v`. -/
def Env.setInt (ρ : Env) (x : Nat) (v : Int) : Env :=
  ⟨ρ.nat, fun i => if i = x then v else ρ.int i⟩

/-- The environment sending every variable to `0`. -/
def Env.zero : Env := ⟨fun _ => 0, fun _ => 0⟩

/-! ## Domains of the partial operations

The same domain predicates are used by the total and the human semantics: on the domain
both semantics compute the exact value; off the domain the total semantics consults the
junk record and the human semantics is undefined. -/

/-- Domain of exact division `n / d` (both sorts, on integer values): `d ≠ 0 ∧ d ∣ n`.
This is the rational reading of `/` restricted to integer results. It is *not* the domain
of floor or Euclidean division (`d ≠ 0`): an inexact quotient with a nonzero divisor, such
as `7 / 2`, lies outside `DivDom`, so the total semantics takes its value from the junk
record and the human semantics leaves it undefined (`inexact_division_is_junk`). -/
def DivDom (n d : Int) : Prop := d ≠ 0 ∧ d ∣ n

instance (n d : Int) : Decidable (DivDom n d) := inferInstanceAs (Decidable (_ ∧ _))

/-- Domain of the remainder `n % d` (both sorts, on integer values): `0 ≤ n ∧ 0 < d`.
On this domain the truncating, flooring and Euclidean remainders coincide
(`rounding_conventions_agree_on_domains`; more generally `remainder_conventions_agree_of_nonneg`).
It is a conservative choice, not the largest such set. Unlike `DivDom`, it contains inexact
cases such as `7 % 2`, so `%` and `/` are treated asymmetrically (`inexact_division_is_junk`). -/
def ModDom (n d : Int) : Prop := 0 ≤ n ∧ 0 < d

instance (n d : Int) : Decidable (ModDom n d) := inferInstanceAs (Decidable (_ ∧ _))

/-! ## Total, junk-parameterized semantics -/

/-- A choice of junk values: the value of each partial operation *outside* its domain.
Natural subtraction `a - b` with `a < b`; natural and integer division outside `DivDom`
(division by zero *and* every inexact quotient, such as `7 / 2`); natural and integer
remainder outside `ModDom`; `Int.toNat z` with `z < 0`. Every field is consulted only outside
the corresponding domain. The records range over all such choices, including ones (such as
`oneJ`) that no proof assistant uses. -/
structure Junk where
  natSub : Nat → Nat → Nat
  natDiv : Nat → Nat → Nat
  natMod : Nat → Nat → Nat
  intDiv : Int → Int → Int
  intMod : Int → Int → Int
  toNat : Int → Nat

/-- Lean's junk values: truncated subtraction, `Nat` floor division and remainder with
`n / 0 = 0` and `n % 0 = n`, the default `Int` operators `/` (`Int.ediv`) and `%`
(`Int.emod`), and `Int.toNat`. -/
def leanJ : Junk where
  natSub a b := a - b
  natDiv a b := a / b
  natMod a b := a % b
  intDiv a b := a / b
  intMod a b := a % b
  toNat z := z.toNat

/-- Truncating (round-toward-zero) integer division and remainder, `Int.tdiv`/`Int.tmod`,
otherwise as `leanJ`. -/
def truncJ : Junk := { leanJ with intDiv := Int.tdiv, intMod := Int.tmod }

/-- Flooring integer division and remainder, `Int.fdiv`/`Int.fmod`, otherwise as `leanJ`. -/
def floorJ : Junk := { leanJ with intDiv := Int.fdiv, intMod := Int.fmod }

/-- A deliberately different junk record: every out-of-domain value is `1`. -/
def oneJ : Junk where
  natSub _ _ := 1
  natDiv _ _ := 1
  natMod _ _ := 1
  intDiv _ _ := 1
  intMod _ _ := 1
  toNat _ := 1

/-- Addition at a sort. -/
def opAdd : (s : Srt) → s.denote → s.denote → s.denote
  | .nat, a, b => (a + b : Nat)
  | .int, a, b => (a + b : Int)

/-- Multiplication at a sort. -/
def opMul : (s : Srt) → s.denote → s.denote → s.denote
  | .nat, a, b => (a * b : Nat)
  | .int, a, b => (a * b : Int)

/-- Subtraction at a sort: exact for `Int`; for `Nat`, exact when `b ≤ a` and junk otherwise. -/
def jSub (J : Junk) : (s : Srt) → s.denote → s.denote → s.denote
  | .nat, a, b => if (b : Nat) ≤ a then (a - b : Nat) else J.natSub a b
  | .int, a, b => (a - b : Int)

/-- Division at a sort: exact on `DivDom`, junk otherwise. -/
def jDiv (J : Junk) : (s : Srt) → s.denote → s.denote → s.denote
  | .nat, a, b => if DivDom ((a : Nat) : Int) ((b : Nat) : Int) then (a / b : Nat) else J.natDiv a b
  | .int, a, b => if DivDom a b then (a / b : Int) else J.intDiv a b

/-- Remainder at a sort: exact on `ModDom`, junk otherwise. -/
def jMod (J : Junk) : (s : Srt) → s.denote → s.denote → s.denote
  | .nat, a, b => if ModDom ((a : Nat) : Int) ((b : Nat) : Int) then (a % b : Nat) else J.natMod a b
  | .int, a, b => if ModDom a b then (a % b : Int) else J.intMod a b

/-- `Int.toNat`: exact on nonnegative arguments, junk otherwise. -/
def jToNat (J : Junk) (z : Int) : Nat := if 0 ≤ z then z.toNat else J.toNat z

/-- Total value of a term under junk record `J` and environment `ρ`. -/
def evalT (J : Junk) (ρ : Env) : {s : Srt} → Term s → s.denote
  | _, .natVar i => ρ.nat i
  | _, .intVar i => ρ.int i
  | _, .natLit n => n
  | _, .intLit z => z
  | s, .add t u => opAdd s (evalT J ρ t) (evalT J ρ u)
  | s, .sub t u => jSub J s (evalT J ρ t) (evalT J ρ u)
  | s, .mul t u => opMul s (evalT J ρ t) (evalT J ρ u)
  | s, .div t u => jDiv J s (evalT J ρ t) (evalT J ρ u)
  | s, .mod t u => jMod J s (evalT J ρ t) (evalT J ρ u)
  | _, .cast t => ((evalT J ρ t : Nat) : Int)
  | _, .toNat t => jToNat J (evalT J ρ t)

open Classical in
/-- Total (two-valued) truth value of a formula under junk record `J`. Relations are
evaluated on the `Int` images of the operands; quantifiers range over all of `ℕ` or `ℤ`
(classically decided). -/
noncomputable def evalJ (J : Junk) : Formula → Env → Bool
  | @Formula.eq s t u, ρ => decide (s.toInt (evalT J ρ t) = s.toInt (evalT J ρ u))
  | @Formula.le s t u, ρ => decide (s.toInt (evalT J ρ t) ≤ s.toInt (evalT J ρ u))
  | @Formula.lt s t u, ρ => decide (s.toInt (evalT J ρ t) < s.toInt (evalT J ρ u))
  | @Formula.dvd s d n, ρ => decide (s.toInt (evalT J ρ d) ∣ s.toInt (evalT J ρ n))
  | .not φ, ρ => !evalJ J φ ρ
  | .and φ ψ, ρ => evalJ J φ ρ && evalJ J ψ ρ
  | .or φ ψ, ρ => evalJ J φ ρ || evalJ J ψ ρ
  | .imp φ ψ, ρ => !evalJ J φ ρ || evalJ J ψ ρ
  | .allNat x φ, ρ => decide (∀ v : Nat, evalJ J φ (ρ.setNat x v) = true)
  | .allInt x φ, ρ => decide (∀ v : Int, evalJ J φ (ρ.setInt x v) = true)
  | .exNat x φ, ρ => decide (∃ v : Nat, evalJ J φ (ρ.setNat x v) = true)
  | .exInt x φ, ρ => decide (∃ v : Int, evalJ J φ (ρ.setInt x v) = true)

/-! ## Lean's reading, written directly with Lean's operators -/

/-- Value of a term computed directly with Lean's core operators at the native sort
(`Nat.sub`, `Nat.div`, `Nat.mod`, `Int.ediv` via `/`, `Int.emod` via `%`, `Int.toNat`). -/
def leanEvalT (ρ : Env) : {s : Srt} → Term s → s.denote
  | _, .natVar i => ρ.nat i
  | _, .intVar i => ρ.int i
  | _, .natLit n => n
  | _, .intLit z => z
  | .nat, .add t u => (leanEvalT ρ t : Nat) + leanEvalT ρ u
  | .int, .add t u => (leanEvalT ρ t : Int) + leanEvalT ρ u
  | .nat, .sub t u => (leanEvalT ρ t : Nat) - leanEvalT ρ u
  | .int, .sub t u => (leanEvalT ρ t : Int) - leanEvalT ρ u
  | .nat, .mul t u => (leanEvalT ρ t : Nat) * leanEvalT ρ u
  | .int, .mul t u => (leanEvalT ρ t : Int) * leanEvalT ρ u
  | .nat, .div t u => (leanEvalT ρ t : Nat) / leanEvalT ρ u
  | .int, .div t u => (leanEvalT ρ t : Int) / leanEvalT ρ u
  | .nat, .mod t u => (leanEvalT ρ t : Nat) % leanEvalT ρ u
  | .int, .mod t u => (leanEvalT ρ t : Int) % leanEvalT ρ u
  | _, .cast t => ((leanEvalT ρ t : Nat) : Int)
  | _, .toNat t => (leanEvalT ρ t : Int).toNat

/-- Native relations at a sort. -/
def Srt.leP : (s : Srt) → s.denote → s.denote → Prop
  | .nat, a, b => (a : Nat) ≤ b
  | .int, a, b => (a : Int) ≤ b

/-- Native strict order at a sort. -/
def Srt.ltP : (s : Srt) → s.denote → s.denote → Prop
  | .nat, a, b => (a : Nat) < b
  | .int, a, b => (a : Int) < b

/-- Native divisibility at a sort. -/
def Srt.dvdP : (s : Srt) → s.denote → s.denote → Prop
  | .nat, a, b => (a : Nat) ∣ b
  | .int, a, b => (a : Int) ∣ b

/-- Truth of a formula read directly as a Lean proposition with Lean's operators and
relations at the native sort. -/
def leanEvalF : Formula → Env → Prop
  | .eq t u, ρ => leanEvalT ρ t = leanEvalT ρ u
  | @Formula.le s t u, ρ => s.leP (leanEvalT ρ t) (leanEvalT ρ u)
  | @Formula.lt s t u, ρ => s.ltP (leanEvalT ρ t) (leanEvalT ρ u)
  | @Formula.dvd s d n, ρ => s.dvdP (leanEvalT ρ d) (leanEvalT ρ n)
  | .not φ, ρ => ¬ leanEvalF φ ρ
  | .and φ ψ, ρ => leanEvalF φ ρ ∧ leanEvalF ψ ρ
  | .or φ ψ, ρ => leanEvalF φ ρ ∨ leanEvalF ψ ρ
  | .imp φ ψ, ρ => leanEvalF φ ρ → leanEvalF ψ ρ
  | .allNat x φ, ρ => ∀ v : Nat, leanEvalF φ (ρ.setNat x v)
  | .allInt x φ, ρ => ∀ v : Int, leanEvalF φ (ρ.setInt x v)
  | .exNat x φ, ρ => ∃ v : Nat, leanEvalF φ (ρ.setNat x v)
  | .exInt x φ, ρ => ∃ v : Int, leanEvalF φ (ρ.setInt x v)

/-! ## Human, partial semantics -/

/-- Two readings of natural subtraction `a - b` with `a < b`:
`partialNat` makes it undefined; `intValued` evaluates it in `ℤ` (a negative value). -/
inductive SubReading
  | partialNat
  | intValued
  deriving DecidableEq, Repr

/-- Connective semantics for three-valued formulas: Kleene's strong three-valued
connectives (`∧` is the minimum and `∨` the maximum in the truth order false < undefined <
true, `kleene_tables`), or left-to-right sequential connectives in the style of McCarthy's
conditional `and`, `or`, `→` (`seq_tables`). -/
inductive Conn
  | kleene
  | seq
  deriving DecidableEq, Repr

/-- Strict lifting of a binary partial operation to optional arguments. -/
def obind2 (x y : Option Int) (f : Int → Int → Option Int) : Option Int :=
  match x, y with
  | some a, some b => f a b
  | _, _ => none

/-- Human subtraction at a sort, on integer values. -/
def hSub (r : SubReading) : Srt → Int → Int → Option Int
  | .nat, a, b =>
    match r with
    | .partialNat => if b ≤ a then some (a - b) else none
    | .intValued => some (a - b)
  | .int, a, b => some (a - b)

/-- Human division: exact quotient on `DivDom`, undefined otherwise. -/
def hDiv (a b : Int) : Option Int := if DivDom a b then some (a / b) else none

/-- Human remainder: defined on `ModDom`, undefined otherwise. -/
def hMod (a b : Int) : Option Int := if ModDom a b then some (a % b) else none

/-- Human `Int.toNat`: identity on nonnegative values, undefined on negative ones. -/
def hToNat (a : Int) : Option Int := if 0 ≤ a then some a else none

/-- Human (exact, partial) value of a term, in `ℤ`. Undefinedness propagates strictly
(so `(a - b) * 0` is undefined whenever `a - b` is). -/
def hEvalT (r : SubReading) (ρ : Env) : {s : Srt} → Term s → Option Int
  | _, .natVar i => some (ρ.nat i : Int)
  | _, .intVar i => some (ρ.int i)
  | _, .natLit n => some (n : Int)
  | _, .intLit z => some z
  | _, .add t u => obind2 (hEvalT r ρ t) (hEvalT r ρ u) fun a b => some (a + b)
  | s, .sub t u => obind2 (hEvalT r ρ t) (hEvalT r ρ u) (hSub r s)
  | _, .mul t u => obind2 (hEvalT r ρ t) (hEvalT r ρ u) fun a b => some (a * b)
  | _, .div t u => obind2 (hEvalT r ρ t) (hEvalT r ρ u) hDiv
  | _, .mod t u => obind2 (hEvalT r ρ t) (hEvalT r ρ u) hMod
  | _, .cast t => hEvalT r ρ t
  | _, .toNat t => (hEvalT r ρ t).bind hToNat

/-- Strict three-valued atom: defined iff both operands are defined. -/
def hAtom (rel : Int → Int → Bool) : Option Int → Option Int → Option Bool
  | some a, some b => some (rel a b)
  | _, _ => none

/-- Three-valued negation. -/
def tvNot (x : Option Bool) : Option Bool := x.map (!·)

/-- Three-valued conjunction. Strong Kleene: false if either side is false, true if both
are true, undefined otherwise. Sequential: undefined if the left side is undefined; false
if the left side is false; otherwise the right side. -/
def tvAnd : Conn → Option Bool → Option Bool → Option Bool
  | .kleene, some false, _ => some false
  | .kleene, _, some false => some false
  | .kleene, some true, some true => some true
  | .kleene, _, _ => none
  | .seq, some false, _ => some false
  | .seq, some true, y => y
  | .seq, none, _ => none

/-- Three-valued disjunction (dual of `tvAnd`). -/
def tvOr : Conn → Option Bool → Option Bool → Option Bool
  | .kleene, some true, _ => some true
  | .kleene, _, some true => some true
  | .kleene, some false, some false => some false
  | .kleene, _, _ => none
  | .seq, some true, _ => some true
  | .seq, some false, y => y
  | .seq, none, _ => none

/-- Three-valued implication, `¬x ∨ y`. Sequentially: undefined if the premise is
undefined, true if it is false, otherwise the conclusion. -/
def tvImp (c : Conn) (x y : Option Bool) : Option Bool := tvOr c (tvNot x) y

open Classical in
/-- Strong Kleene universal quantifier: true if every instance is true, false if some
instance is false, undefined otherwise (`kleene_quantifier_tables`). Used under both
connective semantics. -/
noncomputable def tvAll {α : Type} (f : α → Option Bool) : Option Bool :=
  if ∀ v, f v = some true then some true
  else if ∃ v, f v = some false then some false
  else none

open Classical in
/-- Strong Kleene existential quantifier: true if some instance is true, false if every
instance is false, undefined otherwise (`kleene_quantifier_tables`). -/
noncomputable def tvEx {α : Type} (f : α → Option Bool) : Option Bool :=
  if ∃ v, f v = some true then some true
  else if ∀ v, f v = some false then some false
  else none

/-- Human (three-valued) truth value of a formula: `some true`, `some false`, or `none`
(undefined). -/
noncomputable def hEval (c : Conn) (r : SubReading) : Formula → Env → Option Bool
  | .eq t u, ρ => hAtom (fun a b => decide (a = b)) (hEvalT r ρ t) (hEvalT r ρ u)
  | .le t u, ρ => hAtom (fun a b => decide (a ≤ b)) (hEvalT r ρ t) (hEvalT r ρ u)
  | .lt t u, ρ => hAtom (fun a b => decide (a < b)) (hEvalT r ρ t) (hEvalT r ρ u)
  | .dvd d n, ρ => hAtom (fun a b => decide (a ∣ b)) (hEvalT r ρ d) (hEvalT r ρ n)
  | .not φ, ρ => tvNot (hEval c r φ ρ)
  | .and φ ψ, ρ => tvAnd c (hEval c r φ ρ) (hEval c r ψ ρ)
  | .or φ ψ, ρ => tvOr c (hEval c r φ ρ) (hEval c r ψ ρ)
  | .imp φ ψ, ρ => tvImp c (hEval c r φ ρ) (hEval c r ψ ρ)
  | .allNat x φ, ρ => tvAll fun v : Nat => hEval c r φ (ρ.setNat x v)
  | .allInt x φ, ρ => tvAll fun v : Int => hEval c r φ (ρ.setInt x v)
  | .exNat x φ, ρ => tvEx fun v : Nat => hEval c r φ (ρ.setNat x v)
  | .exInt x φ, ρ => tvEx fun v : Int => hEval c r φ (ρ.setInt x v)

/-! ## Properties of formulas -/

/-- `φ` is junk-independent: its total truth value at every environment is the same for
every junk record. Because junk records also vary every inexact quotient, a formula such as
`7 / 2 = 3` at `Nat` is *not* junk-independent although every rounding convention gives `3`
(`inexact_division_is_junk`). -/
def JunkIndependent (φ : Formula) : Prop :=
  ∀ (J J' : Junk) (ρ : Env), evalJ J φ ρ = evalJ J' φ ρ

/-- The human value of `φ` is defined at every environment. -/
def DefinedEverywhere (c : Conn) (r : SubReading) (φ : Formula) : Prop :=
  ∀ ρ : Env, hEval c r φ ρ ≠ none

/-- Wherever the human value of `φ` is defined, the total value under `J` equals it. -/
def AgreesWhereDefined (c : Conn) (r : SubReading) (J : Junk) (φ : Formula) : Prop :=
  ∀ (ρ : Env) (b : Bool), hEval c r φ ρ = some b → evalJ J φ ρ = b

/-- `φ` is true at every environment in Lean's reading. -/
def LeanValid (φ : Formula) : Prop := ∀ ρ : Env, evalJ leanJ φ ρ = true

/-- `φ` is (defined and) true at every environment in the human reading. -/
def HumanValid (c : Conn) (r : SubReading) (φ : Formula) : Prop :=
  ∀ ρ : Env, hEval c r φ ρ = some true

/-! ## The guard discipline -/

/-- Facts made available by a formula that is known to be true: its top-level conjuncts
that are atoms or negated equalities. -/
def Formula.facts : Formula → List Formula
  | .and φ ψ => φ.facts ++ ψ.facts
  | .eq t u => [.eq t u]
  | .le t u => [.le t u]
  | .lt t u => [.lt t u]
  | .dvd d n => [.dvd d n]
  | .not (.eq t u) => [.not (.eq t u)]
  | _ => []

/-- Every partial operation in `t` is guarded by facts in `Γ`, matched syntactically
(positive examples of every rule: `guarded_pos`, `guarded_branches_pos`):
`a - b` at `Nat` needs `b ≤ a`; `n / d` needs `¬ (d = 0)` and `d ∣ n`; `n % d` at `Nat`
needs `¬ (d = 0)`; `n % d` at `Int` needs `0 < d` and `0 ≤ n`; `Int.toNat t` needs
`0 ≤ t`. -/
def Term.guardedIn (Γ : List Formula) : {s : Srt} → Term s → Bool
  | _, .natVar _ => true
  | _, .intVar _ => true
  | _, .natLit _ => true
  | _, .intLit _ => true
  | _, .add t u => t.guardedIn Γ && u.guardedIn Γ
  | _, .mul t u => t.guardedIn Γ && u.guardedIn Γ
  | .nat, .sub t u => t.guardedIn Γ && u.guardedIn Γ && Γ.contains (.le u t)
  | .int, .sub t u => t.guardedIn Γ && u.guardedIn Γ
  | s, .div t u => t.guardedIn Γ && u.guardedIn Γ &&
      Γ.contains (.not (.eq u (zeroOf s))) && Γ.contains (.dvd u t)
  | .nat, .mod t u => t.guardedIn Γ && u.guardedIn Γ && Γ.contains (.not (.eq u (.natLit 0)))
  | .int, .mod t u => t.guardedIn Γ && u.guardedIn Γ &&
      Γ.contains (.lt (.intLit 0) u) && Γ.contains (.le (.intLit 0) t)
  | _, .cast t => t.guardedIn Γ
  | _, .toNat t => t.guardedIn Γ && Γ.contains (.le (.intLit 0) t)

/-- Natural variable `x` occurs in `t`. -/
def Term.mentionsNat (x : Nat) : {s : Srt} → Term s → Bool
  | _, .natVar i => i == x
  | _, .intVar _ => false
  | _, .natLit _ => false
  | _, .intLit _ => false
  | _, .add t u | _, .sub t u | _, .mul t u | _, .div t u | _, .mod t u =>
      t.mentionsNat x || u.mentionsNat x
  | _, .cast t => t.mentionsNat x
  | _, .toNat t => t.mentionsNat x

/-- Integer variable `x` occurs in `t`. -/
def Term.mentionsInt (x : Nat) : {s : Srt} → Term s → Bool
  | _, .natVar _ => false
  | _, .intVar i => i == x
  | _, .natLit _ => false
  | _, .intLit _ => false
  | _, .add t u | _, .sub t u | _, .mul t u | _, .div t u | _, .mod t u =>
      t.mentionsInt x || u.mentionsInt x
  | _, .cast t => t.mentionsInt x
  | _, .toNat t => t.mentionsInt x

/-- Natural variable `x` occurs in a term of `φ` (binder names are not counted; bound
occurrences are, so this over-approximates free occurrence). -/
def Formula.mentionsNat (x : Nat) : Formula → Bool
  | .eq t u | .le t u | .lt t u | .dvd t u => t.mentionsNat x || u.mentionsNat x
  | .not φ => φ.mentionsNat x
  | .and φ ψ | .or φ ψ | .imp φ ψ => φ.mentionsNat x || ψ.mentionsNat x
  | .allNat _ φ | .allInt _ φ | .exNat _ φ | .exInt _ φ => φ.mentionsNat x

/-- Integer variable `x` occurs in a term of `φ`. -/
def Formula.mentionsInt (x : Nat) : Formula → Bool
  | .eq t u | .le t u | .lt t u | .dvd t u => t.mentionsInt x || u.mentionsInt x
  | .not φ => φ.mentionsInt x
  | .and φ ψ | .or φ ψ | .imp φ ψ => φ.mentionsInt x || ψ.mentionsInt x
  | .allNat _ φ | .allInt _ φ | .exNat _ φ | .exInt _ φ => φ.mentionsInt x

/-- Guard checking with available facts `Γ`. Facts accumulate left to right through the
earlier conjuncts of `∧` and the premise of `→`; `∨` and `¬` add none; a quantifier
discards the facts that mention its bound variable. -/
def Formula.guardedIn : List Formula → Formula → Bool
  | Γ, .eq t u | Γ, .le t u | Γ, .lt t u | Γ, .dvd t u => t.guardedIn Γ && u.guardedIn Γ
  | Γ, .not φ => φ.guardedIn Γ
  | Γ, .and φ ψ => φ.guardedIn Γ && ψ.guardedIn (Γ ++ φ.facts)
  | Γ, .or φ ψ => φ.guardedIn Γ && ψ.guardedIn Γ
  | Γ, .imp φ ψ => φ.guardedIn Γ && ψ.guardedIn (Γ ++ φ.facts)
  | Γ, .allNat x φ | Γ, .exNat x φ => φ.guardedIn (Γ.filter fun f => !f.mentionsNat x)
  | Γ, .allInt x φ | Γ, .exInt x φ => φ.guardedIn (Γ.filter fun f => !f.mentionsInt x)

/-- The decidable guard checker: `φ` is in the guarded fragment. -/
def guarded (φ : Formula) : Bool := φ.guardedIn []

end Toy.Junk
