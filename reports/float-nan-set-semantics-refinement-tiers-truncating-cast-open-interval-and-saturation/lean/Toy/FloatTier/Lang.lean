/-
Toy.FloatTier.Lang
==================

A small floating-point expression language and its observations.

* `FExpr f`: literals (any bit pattern, so a NaN literal models a NaN built
  with `from_bits`), input variables, the set-valued primitives (`prim`), the
  bit-level operations `neg`, `abs`, `copysign`, and a value-level branch
  `selLt a b t e` ("if a < b then t else e").
* `Prog f`: one observation of expressions, returning a natural number:
  value-level observations `isNaN`, `eq` (IEEE `==`), `lt` (IEEE `<`), and
  bit-level observations `signBit` and `toBits`.
* `evalS X ρ e r` / `runS X ρ P n`: the set-valued semantics `S` (relational;
  every primitive node makes its own choice). `evalT τ ρ e` / `runT τ ρ P`: the
  deterministic semantics of a tier `τ`.
* `RefinesS X τ`: expression-level, bit-exact refinement: every result of `τ`
  on every expression and input is (as a bit pattern) a result of `S`.
* `fold τ e`: constant folding with tier `τ`. Every closed subexpression
  (no variables) is replaced by the literal that `τ` computes for it.
* `BitSafe X ρ bad e`: in every execution of `S` from input `ρ`, every
  bit-level use (the sign argument of `copysign`, and the argument of `signBit`
  or `toBits`) receives a value `v` with `bad v = false`. A branch of `selLt` is
  constrained only if some execution of `S` from `ρ` takes it.
* `PrimsOk ok e`: every primitive in `e` satisfies `ok`; `MinMaxFree` is the
  case "no `min`/`max`".
-/
import Toy.FloatTier.Sets

namespace Toy.FloatTier

variable {f : Fmt}

/-- Floating-point expressions over input variables `var i`. -/
inductive FExpr (f : Fmt) where
  | lit (v : V f)
  | var (i : Nat)
  | prim (p : Prim) (a b : FExpr f)
  | neg (a : FExpr f)
  | abs (a : FExpr f)
  | copysign (a b : FExpr f)
  | selLt (a b t e : FExpr f)
  deriving Repr

/-- Programs: one observation of floating-point expressions. -/
inductive Prog (f : Fmt) where
  | isNaN (a : FExpr f)
  | eq (a b : FExpr f)
  | lt (a b : FExpr f)
  | signBit (a : FExpr f)
  | toBits (a : FExpr f)
  deriving Repr

namespace FExpr

/-- Set-valued semantics `S` with extra payloads `X` and input `ρ`:
`evalS X ρ e r` means that `r` is a possible result of `e`. -/
def evalS (X : Extra f) (ρ : Nat → V f) : FExpr f → V f → Prop
  | .lit v, r => r = v
  | .var i, r => r = ρ i
  | .prim p a b, r => ∃ x y, a.evalS X ρ x ∧ b.evalS X ρ y ∧ primSet X p x y r
  | .neg a, r => ∃ x, a.evalS X ρ x ∧ r = x.neg
  | .abs a, r => ∃ x, a.evalS X ρ x ∧ r = x.abs
  | .copysign a b, r => ∃ x y, a.evalS X ρ x ∧ b.evalS X ρ y ∧ r = x.copysign y
  | .selLt a b t e, r => ∃ x y, a.evalS X ρ x ∧ b.evalS X ρ y ∧
      (if Toy.FloatTier.lt x.toFP y.toFP = true then t.evalS X ρ r else e.evalS X ρ r)

/-- Deterministic semantics of tier `τ` on input `ρ`. -/
def evalT (τ : Tier f) (ρ : Nat → V f) : FExpr f → V f
  | .lit v => v
  | .var i => ρ i
  | .prim p a b => τ p (a.evalT τ ρ) (b.evalT τ ρ)
  | .neg a => (a.evalT τ ρ).neg
  | .abs a => (a.evalT τ ρ).abs
  | .copysign a b => (a.evalT τ ρ).copysign (b.evalT τ ρ)
  | .selLt a b t e =>
    if Toy.FloatTier.lt (a.evalT τ ρ).toFP (b.evalT τ ρ).toFP = true then t.evalT τ ρ
    else e.evalT τ ρ

/-- No input variables occur. -/
def closed : FExpr f → Bool
  | .lit _ => true
  | .var _ => false
  | .prim _ a b => a.closed && b.closed
  | .neg a => a.closed
  | .abs a => a.closed
  | .copysign a b => a.closed && b.closed
  | .selLt a b t e => a.closed && b.closed && t.closed && e.closed

/-- Constant folding with tier `τ`: every maximal closed subexpression is
replaced by the literal `τ` computes for it (closed expressions do not depend on
the input; the fixed input `fun _ => V.inf false` is used). -/
def fold (τ : Tier f) (e : FExpr f) : FExpr f :=
  if e.closed then .lit (e.evalT τ fun _ => .inf false) else
  match e with
  | .lit v => .lit v
  | .var i => .var i
  | .prim p a b => .prim p (a.fold τ) (b.fold τ)
  | .neg a => .neg (a.fold τ)
  | .abs a => .abs (a.fold τ)
  | .copysign a b => .copysign (a.fold τ) (b.fold τ)
  | .selLt a b t e => .selLt (a.fold τ) (b.fold τ) (t.fold τ) (e.fold τ)

/-- In every `S`-execution from `ρ`, every bit-level use inside `e` (the sign
argument of `copysign`) receives a value `v` with `bad v = false`. A branch of
`selLt a b t e` is constrained only if some `S`-execution from `ρ` takes it:
`t` when some pair of results of `a`, `b` satisfies `a < b`, and `e` when some
pair does not. -/
def BitSafe (X : Extra f) (ρ : Nat → V f) (bad : V f → Bool) : FExpr f → Prop
  | .lit _ => True
  | .var _ => True
  | .prim _ a b => a.BitSafe X ρ bad ∧ b.BitSafe X ρ bad
  | .neg a => a.BitSafe X ρ bad
  | .abs a => a.BitSafe X ρ bad
  | .copysign a b => a.BitSafe X ρ bad ∧ b.BitSafe X ρ bad ∧
      ∀ y, b.evalS X ρ y → bad y = false
  | .selLt a b t e => a.BitSafe X ρ bad ∧ b.BitSafe X ρ bad ∧
      ((∃ x y, a.evalS X ρ x ∧ b.evalS X ρ y ∧ Toy.FloatTier.lt x.toFP y.toFP = true) →
        t.BitSafe X ρ bad) ∧
      ((∃ x y, a.evalS X ρ x ∧ b.evalS X ρ y ∧ Toy.FloatTier.lt x.toFP y.toFP = false) →
        e.BitSafe X ρ bad)

/-- Every primitive occurring in `e` satisfies `ok`. -/
def PrimsOk (ok : Prim → Bool) : FExpr f → Bool
  | .lit _ => true
  | .var _ => true
  | .prim p a b => ok p && a.PrimsOk ok && b.PrimsOk ok
  | .neg a => a.PrimsOk ok
  | .abs a => a.PrimsOk ok
  | .copysign a b => a.PrimsOk ok && b.PrimsOk ok
  | .selLt a b t e => a.PrimsOk ok && b.PrimsOk ok && t.PrimsOk ok && e.PrimsOk ok

end FExpr

/-- The arithmetic primitives (`add`, `sub`, `mul`), i.e. not `min`/`max`. -/
def Prim.isArith : Prim → Bool
  | .add => true
  | .sub => true
  | .mul => true
  | .min => false
  | .max => false

namespace Prog

/-- Set-valued semantics of an observation. -/
def runS (X : Extra f) (ρ : Nat → V f) : Prog f → Nat → Prop
  | .isNaN a, n => ∃ x, a.evalS X ρ x ∧ n = x.isNaN.toNat
  | .eq a b, n => ∃ x y, a.evalS X ρ x ∧ b.evalS X ρ y ∧ n = (feq x.toFP y.toFP).toNat
  | .lt a b, n => ∃ x y, a.evalS X ρ x ∧ b.evalS X ρ y ∧
      n = (Toy.FloatTier.lt x.toFP y.toFP).toNat
  | .signBit a, n => ∃ x, a.evalS X ρ x ∧ n = x.signBit.toNat
  | .toBits a, n => ∃ x, a.evalS X ρ x ∧ n = x.bits

/-- Deterministic semantics of an observation under tier `τ`. -/
def runT (τ : Tier f) (ρ : Nat → V f) : Prog f → Nat
  | .isNaN a => (a.evalT τ ρ).isNaN.toNat
  | .eq a b => (feq (a.evalT τ ρ).toFP (b.evalT τ ρ).toFP).toNat
  | .lt a b => (Toy.FloatTier.lt (a.evalT τ ρ).toFP (b.evalT τ ρ).toFP).toNat
  | .signBit a => (a.evalT τ ρ).signBit.toNat
  | .toBits a => (a.evalT τ ρ).bits

/-- Constant folding of every expression in the observation. -/
def fold (τ : Tier f) : Prog f → Prog f
  | .isNaN a => .isNaN (a.fold τ)
  | .eq a b => .eq (a.fold τ) (b.fold τ)
  | .lt a b => .lt (a.fold τ) (b.fold τ)
  | .signBit a => .signBit (a.fold τ)
  | .toBits a => .toBits (a.fold τ)

/-- In every `S`-execution from `ρ`, every bit-level use (inside the
expressions, and the argument of `signBit`/`toBits`) receives a value `v` with
`bad v = false`. -/
def BitSafe (X : Extra f) (ρ : Nat → V f) (bad : V f → Bool) : Prog f → Prop
  | .isNaN a => a.BitSafe X ρ bad
  | .eq a b => a.BitSafe X ρ bad ∧ b.BitSafe X ρ bad
  | .lt a b => a.BitSafe X ρ bad ∧ b.BitSafe X ρ bad
  | .signBit a => a.BitSafe X ρ bad ∧ ∀ y, a.evalS X ρ y → bad y = false
  | .toBits a => a.BitSafe X ρ bad ∧ ∀ y, a.evalS X ρ y → bad y = false

/-- Every primitive occurring in the observation satisfies `ok`. -/
def PrimsOk (ok : Prim → Bool) : Prog f → Bool
  | .isNaN a => a.PrimsOk ok
  | .eq a b => a.PrimsOk ok && b.PrimsOk ok
  | .lt a b => a.PrimsOk ok && b.PrimsOk ok
  | .signBit a => a.PrimsOk ok
  | .toBits a => a.PrimsOk ok

/-- No `min`/`max` occurs. -/
def MinMaxFree (P : Prog f) : Bool := P.PrimsOk Prim.isArith

end Prog

/-- Expression-level, bit-exact refinement of `S` by a tier: on every
expression and input, the tier's result (a full bit pattern in `V f`, not a
value-level class) is one of the results allowed by `S` (with extra payloads
`X`). -/
def RefinesS (X : Extra f) (τ : Tier f) : Prop :=
  ∀ (e : FExpr f) (ρ : Nat → V f), e.evalS X ρ (e.evalT τ ρ)

end Toy.FloatTier
