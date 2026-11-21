/-
Toy.Float.Defs
==============

A small, self-contained, decidable model of IEEE 754-style binary
floating-point arithmetic with round-to-nearest-ties-to-even (RNE).

* `Fmt` is a binary format: exponent-field width `e` and precision `p`
  (significand bits including the hidden bit).
* `FP f` is the set of values of format `f`: one quiet NaN (NaN payloads and the
  NaN sign are collapsed), two signed infinities, and the finite values, each
  given by its IEEE fields (sign, biased exponent `E`, trailing significand `M`),
  with subnormals (`E = 0`) and both signed zeros. Equality on `FP f` is equality
  of these fields; `FP.bits` is proved injective for `F33`; the general case is unproved.
* Exact semantics: a finite value is an integer number of *units*, one unit
  being the smallest positive subnormal `2^(-f.qneg)`. Exact sums are integers
  of units; exact products and exact `a*b + c` are integers of units divided by
  `2^f.qneg`. All exact arithmetic is on `Nat`/`Int`.
* `round` is RNE of a nonnegative rational `m / 2^d` (in units) to the format,
  with overflow to infinity.
* `add`, `sub`, `mul`, `fma` are correctly rounded with the IEEE special-value
  and signed-zero rules; `lt`, `le`, `feq` are the IEEE quiet comparisons.
* `Expr`, `Flags`, `ValidMod` model a rewrite `lhs → rhs` and the fast-math
  flags `nnan`, `ninf`, `nsz` (input/result restrictions and a coarser result
  relation) and `reassoc`, `contract` (permissions to evaluate a different,
  reassociated or contracted, form of `lhs`).
-/

namespace Toy.Float

/-! ## Formats -/

/-- A binary floating-point format with exponent-field width `e` and precision
`p` (significand bits including the hidden bit). The bounds `2 ≤ e` and
`2 ≤ p` exclude degenerate formats without normal numbers or without a
fractional significand bit. Captures: the parameters `(w, p)` of an IEEE 754
binary interchange format (binary32 is `e = 8`, `p = 24`). -/
structure Fmt where
  e : Nat
  p : Nat
  two_le_e : 2 ≤ e
  two_le_p : 2 ≤ p

namespace Fmt

variable (f : Fmt)

/-- Exponent bias `2^(e-1) - 1`; `emax = bias`, `emin = 1 - bias`. -/
def bias : Nat := 2 ^ (f.e - 1) - 1

/-- Number of biased-exponent field values used by finite numbers:
`E ∈ [0, 2^e - 2]` (the all-ones field encodes infinities and NaN). -/
def expCount : Nat := 2 ^ f.e - 1

/-- Number of trailing-significand field values, `2^(p-1)`. -/
def fracCount : Nat := 2 ^ (f.p - 1)

/-- One unit (the smallest positive subnormal) is `2^(-qneg)`, where
`qneg = bias + p - 2 = -(emin - p + 1)`. -/
def qneg : Nat := f.bias + f.p - 2

/-- The largest finite magnitude, in units: `(2^p - 1) * 2^(2^e - 3)`. -/
def maxUnits : Nat := (2 ^ f.p - 1) * 2 ^ (2 ^ f.e - 3)

theorem four_le_two_pow_e : 4 ≤ 2 ^ f.e :=
  calc 4 = 2 ^ 2 := rfl
    _ ≤ 2 ^ f.e := Nat.pow_le_pow_right (by decide) f.two_le_e

theorem expCount_pos : 0 < f.expCount := by
  unfold expCount; have := f.four_le_two_pow_e; omega

theorem fracCount_pos : 0 < f.fracCount := Nat.two_pow_pos _

end Fmt

/-! ## Values -/

/-- The values of format `f`, by IEEE fields. `fin neg E M` is the finite value
with sign `neg`, biased exponent `E` (`E = 0`: zero or subnormal) and trailing
significand `M`. There is exactly one NaN (payload and sign collapsed). -/
inductive FP (f : Fmt) where
  | nan : FP f
  | inf (neg : Bool) : FP f
  | fin (neg : Bool) (E : Fin f.expCount) (M : Fin f.fracCount) : FP f
  deriving DecidableEq, Repr

variable {f : Fmt}

/-- Magnitude in units of the finite value with fields `E`, `M`:
`M` if `E = 0`, else `(2^(p-1) + M) * 2^(E-1)`. -/
def unitsOf (f : Fmt) (E M : Nat) : Nat :=
  if E = 0 then M else (f.fracCount + M) * 2 ^ (E - 1)

namespace FP

/-- Magnitude in units (0 for NaN and infinities). -/
def units : FP f → Nat
  | .fin _ E M => unitsOf f E.val M.val
  | _ => 0

/-- Sign bit (`false` for the collapsed NaN). -/
def signBit : FP f → Bool
  | .nan => false
  | .inf s => s
  | .fin s _ _ => s

def isNaN : FP f → Bool
  | .nan => true
  | _ => false

def isInf : FP f → Bool
  | .inf _ => true
  | _ => false

def isFinite : FP f → Bool
  | .fin .. => true
  | _ => false

/-- `±0`. -/
def isZero : FP f → Bool
  | .fin _ E M => E.val == 0 && M.val == 0
  | _ => false

/-- Normal numbers: finite with `E ≠ 0`. -/
def isNormal : FP f → Bool
  | .fin _ E _ => E.val != 0
  | _ => false

/-- IEEE bit pattern (sign, exponent field, trailing significand), with the
collapsed NaN encoded as the canonical positive quiet NaN. -/
def bits : FP f → Nat
  | .nan => (2 ^ f.e - 1) * 2 ^ (f.p - 1) + 2 ^ (f.p - 2)
  | .inf s => (if s then 2 ^ (f.e + f.p - 1) else 0) + (2 ^ f.e - 1) * 2 ^ (f.p - 1)
  | .fin s E M => (if s then 2 ^ (f.e + f.p - 1) else 0) + E.val * 2 ^ (f.p - 1) + M.val

/-- Negation: flips the sign bit (NaN is collapsed, so `neg nan = nan`). -/
def neg : FP f → FP f
  | .nan => .nan
  | .inf s => .inf (!s)
  | .fin s E M => .fin (!s) E M

end FP

/-- Signed zero. -/
def zero (f : Fmt) (neg : Bool) : FP f :=
  .fin neg ⟨0, f.expCount_pos⟩ ⟨0, f.fracCount_pos⟩

/-- `+0.0`. -/
abbrev posZero (f : Fmt) : FP f := zero f false
/-- `-0.0`. -/
abbrev negZero (f : Fmt) : FP f := zero f true

/-! ## Rounding -/

/-- `bitLenAux k n` = number of binary digits of `n`, computed with fuel `k`. -/
def bitLenAux : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, n => if n = 0 then 0 else bitLenAux k (n / 2) + 1

/-- Number of binary digits of `n` (`bitLen 0 = 0`, `bitLen 5 = 3`). -/
def bitLen (n : Nat) : Nat := bitLenAux n n

/-- Round-to-nearest-ties-to-even of the nonnegative rational `m / 2^d` to an
integer. -/
def rneDiv (m d : Nat) : Nat :=
  let q := m / 2 ^ d
  let r := m % 2 ^ d
  if 2 * r > 2 ^ d ∨ (2 * r = 2 ^ d ∧ q % 2 = 1) then q + 1 else q

/-- RNE of the nonnegative rational `m / 2^d` (in units) to the grid of
magnitudes representable with precision `p` and unbounded exponent above:
every integer below `2^p`, and above that every multiple of `2^t` in the
binade `[2^(t+p-1), 2^(t+p))`. -/
def roundUnits (f : Fmt) (m d : Nat) : Nat :=
  let t := bitLen (m / 2 ^ d) - f.p
  rneDiv m (d + t) * 2 ^ t

/-- Biased exponent field of a representable magnitude `n` (in units). -/
def decodeE (f : Fmt) (n : Nat) : Nat :=
  if n < f.fracCount then 0 else bitLen n - f.p + 1

/-- Trailing significand field of a representable magnitude `n` (in units). -/
def decodeM (f : Fmt) (n : Nat) : Nat :=
  if n < f.fracCount then n else n / 2 ^ (bitLen n - f.p) - f.fracCount

/-- The value with sign `neg` and representable magnitude `n` units; `±∞` if
`n` exceeds the largest finite magnitude. (The `%` are no-ops on
representable inputs; they only make the fields well-typed.) -/
def mkFin (f : Fmt) (neg : Bool) (n : Nat) : FP f :=
  if f.maxUnits < n then .inf neg
  else .fin neg ⟨decodeE f n % f.expCount, Nat.mod_lt _ f.expCount_pos⟩
                ⟨decodeM f n % f.fracCount, Nat.mod_lt _ f.fracCount_pos⟩

/-- Correct rounding (RNE, overflow to `±∞`) of the exact value
`±(m / 2^d)` units; the sign `neg` is kept also when the result is zero. -/
def round (f : Fmt) (neg : Bool) (m d : Nat) : FP f :=
  mkFin f neg (roundUnits f m d)

/-- The value nearest to `±m * 2^k` (RNE), e.g. `ofDyadic f false 3 (-1) = 1.5`. -/
def ofDyadic (f : Fmt) (neg : Bool) (m : Nat) (k : Int) : FP f :=
  if 0 ≤ k + f.qneg then round f neg (m * 2 ^ (k + f.qneg).toNat) 0
  else round f neg m (-(k + f.qneg)).toNat

/-- `1.0`. -/
def one (f : Fmt) : FP f := ofDyadic f false 1 0

/-- The largest finite value `(2 - 2^(1-p)) * 2^emax`. -/
def maxFinite (f : Fmt) (neg : Bool) : FP f := mkFin f neg f.maxUnits

/-- Signed integer value in units. -/
def sval (neg : Bool) (u : Nat) : Int := if neg then -(u : Int) else (u : Int)

/-! ## Arithmetic -/

/-- IEEE addition with RNE. NaN in, NaN out; `∞ + (-∞) = NaN`; an exact zero
sum is `+0` unless both operands are `-0` (IEEE 754-2019 §6.3, RNE). -/
def add : FP f → FP f → FP f
  | .nan, _ => .nan
  | .inf _, .nan => .nan
  | .fin .., .nan => .nan
  | .inf s, .inf t => if s = t then .inf s else .nan
  | .inf s, .fin .. => .inf s
  | .fin .., .inf t => .inf t
  | .fin s E M, .fin t E' M' =>
    let v := sval s (unitsOf f E.val M.val) + sval t (unitsOf f E'.val M'.val)
    if v = 0 then zero f (s && t) else round f (decide (v < 0)) v.natAbs 0

/-- IEEE subtraction, `x - y = x + (-y)`. -/
def sub (x y : FP f) : FP f := add x y.neg

/-- IEEE multiplication with RNE. The sign of a non-NaN product is the
exclusive or of the operand signs, also when the result is zero;
`∞ * 0 = NaN`. -/
def mul : FP f → FP f → FP f
  | .nan, _ => .nan
  | .inf _, .nan => .nan
  | .fin .., .nan => .nan
  | .inf s, .inf t => .inf (s != t)
  | .inf s, .fin t E M => if unitsOf f E.val M.val = 0 then .nan else .inf (s != t)
  | .fin s E M, .inf t => if unitsOf f E.val M.val = 0 then .nan else .inf (s != t)
  | .fin s E M, .fin t E' M' =>
    round f (s != t) (unitsOf f E.val M.val * unitsOf f E'.val M'.val) f.qneg

/-- The exact value of `a*b + c` for finite operands, in units of
`2^(-2 * qneg)` (i.e. scaled by `2^qneg` relative to units). -/
def exactFma (f : Fmt) (s : Bool) (ua : Nat) (t : Bool) (ub : Nat) (u : Bool) (uc : Nat) :
    Int :=
  sval (s != t) (ua * ub) + sval u (uc * 2 ^ f.qneg)

/-- Fused multiply-add: `a*b + c` computed exactly and rounded once (RNE).
Special values: NaN if any operand is NaN or if `∞ * 0`; an infinite product
plus an opposite infinity is NaN. An exact zero result is signed by the sum
rule (`-0` only if the product and `c` are both `-0`); a nonzero exact result
that rounds to zero keeps the sign of the exact result. -/
def fma (a b c : FP f) : FP f :=
  match a, b with
  | .nan, _ => .nan
  | .inf _, .nan => .nan
  | .fin .., .nan => .nan
  | .fin s E M, .fin t E' M' =>
    match c with
    | .nan => .nan
    | .inf u => .inf u
    | .fin u E'' M'' =>
      let v := exactFma f s (unitsOf f E.val M.val) t (unitsOf f E'.val M'.val)
        u (unitsOf f E''.val M''.val)
      if v = 0 then zero f ((s != t) && u) else round f (decide (v < 0)) v.natAbs f.qneg
  | a, b =>
    if a.isZero || b.isZero then .nan
    else
      match c with
      | .nan => .nan
      | .inf u => if u = (a.signBit != b.signBit) then .inf u else .nan
      | .fin .. => .inf (a.signBit != b.signBit)

/-! ## Errors of approximations to `a*b + c` -/

/-- Signed value of a finite value in units of `2^(-2 * qneg)` (so that exact
products and exact `a*b + c` are integers); `0` for NaN and infinities, which
`errOf` never uses. -/
def FP.val2 (x : FP f) : Int := sval x.signBit (x.units * 2 ^ f.qneg)

/-- The exact value of `a*b + c`, in units of `2^(-2 * qneg)`, for finite
`a`, `b`, `c` (computed from their fields). -/
def exactMulAdd (a b c : FP f) : Int :=
  exactFma f a.signBit a.units b.signBit b.units c.signBit c.units

/-- Absolute error of `x` as an approximation of the exact value `v` (in units
of `2^(-2 * qneg)`): `some |x - v|` if `x` is finite, `none` (infinite error)
if `x` is NaN or infinite. -/
def errOf (x : FP f) (v : Int) : Option Nat :=
  if x.isFinite then some (x.val2 - v).natAbs else none

/-- Order on errors, with `none` (infinite error) as the top element. -/
def ErrLe : Option Nat → Option Nat → Prop
  | _, none => True
  | none, some _ => False
  | some a, some b => a ≤ b

instance (a b : Option Nat) : Decidable (ErrLe a b) := by
  cases a <;> cases b <;> unfold ErrLe <;> infer_instance

/-! ## Comparisons -/

/-- Order key for non-NaN values: `-∞ < negatives < ±0 < positives < +∞`,
with `key (-0) = key (+0) = 0`. -/
def key : FP f → Int
  | .nan => 0
  | .inf s => sval s (f.maxUnits + 1)
  | .fin s E M => sval s (unitsOf f E.val M.val)

/-- IEEE quiet `<`: false if either operand is NaN. -/
def lt (x y : FP f) : Bool := !x.isNaN && !y.isNaN && decide (key x < key y)
/-- IEEE quiet `≤`: false if either operand is NaN. -/
def le (x y : FP f) : Bool := !x.isNaN && !y.isNaN && decide (key x ≤ key y)
/-- IEEE quiet `>=`. -/
def ge (x y : FP f) : Bool := le y x
/-- IEEE `==`: false if either operand is NaN; `-0 == +0`. -/
def feq (x y : FP f) : Bool := !x.isNaN && !y.isNaN && decide (key x = key y)

/-- `min` defined by `<` as in `x < y ? x : y`. -/
def minLt (x y : FP f) : FP f := if lt x y then x else y
/-- `max` defined by `<` as in `x > y ? x : y`. -/
def maxLt (x y : FP f) : FP f := if lt y x then x else y

/-- Key refining `key` by `-0 < +0` (injective on non-NaN values). -/
def totalKey (x : FP f) : Int := 2 * key x + (if x = posZero f then 1 else 0)

/-- IEEE 754-2019 `minimum`: NaN if either operand is NaN, otherwise the
smaller operand, where `-0` is less than `+0`. -/
def minimum (x y : FP f) : FP f :=
  if x.isNaN || y.isNaN then .nan else if totalKey x ≤ totalKey y then x else y
/-- IEEE 754-2019 `maximum`: NaN if either operand is NaN, otherwise the
larger operand, where `-0` is less than `+0`. -/
def maximum (x y : FP f) : FP f :=
  if x.isNaN || y.isNaN then .nan else if totalKey y ≤ totalKey x then x else y

/-- Identifies `-0` with `+0` and leaves every other value unchanged. -/
def zeroBlind (x : FP f) : FP f := if x.isZero then posZero f else x

/-- Equality up to the sign of zero (the result relation under `nsz`). -/
def EqNsz (x y : FP f) : Prop := zeroBlind x = zeroBlind y

instance (x y : FP f) : Decidable (EqNsz x y) := inferInstanceAs (Decidable (_ = _))

/-! ## Format conversion -/

/-- Conversion from format `g` to format `f`, correctly rounded (RNE). -/
def cvt (g f : Fmt) : FP g → FP f
  | .nan => .nan
  | .inf s => .inf s
  | .fin s E M =>
    let u := unitsOf g E.val M.val
    if g.qneg ≤ f.qneg then round f s (u * 2 ^ (f.qneg - g.qneg)) 0
    else round f s u (g.qneg - f.qneg)

/-- `x + y` evaluated in a wider format `g` and rounded back to `f`. -/
def addVia (g : Fmt) (x y : FP f) : FP f := cvt g f (add (cvt f g x) (cvt f g y))
/-- `x * y` evaluated in a wider format `g` and rounded back to `f`. -/
def mulVia (g : Fmt) (x y : FP f) : FP f := cvt g f (mul (cvt f g x) (cvt f g y))

/-! ## Rewrites and fast-math flags -/

/-- A set of LLVM-style fast-math flags. `nnan`, `ninf`: arguments and results
of every operation in the source expression are assumed not NaN / not
infinite; `nsz`: the sign of a zero result is insignificant; `reassoc`,
`contract`: permission to evaluate a reassociated / contracted form. -/
structure Flags where
  nnan : Bool := false
  ninf : Bool := false
  nsz : Bool := false
  reassoc : Bool := false
  contract : Bool := false
  deriving DecidableEq, Repr

namespace Flags

/-- Flag-set inclusion. -/
def Sub (S T : Flags) : Prop :=
  (S.nnan → T.nnan) ∧ (S.ninf → T.ninf) ∧ (S.nsz → T.nsz) ∧
  (S.reassoc → T.reassoc) ∧ (S.contract → T.contract)

/-- All five flags. -/
def all : Flags := ⟨true, true, true, true, true⟩

end Flags

/-- Floating-point expressions over `n` variables. -/
inductive Expr (f : Fmt) (n : Nat) where
  | var (i : Fin n)
  | lit (c : FP f)
  | neg (a : Expr f n)
  | add (a b : Expr f n)
  | sub (a b : Expr f n)
  | mul (a b : Expr f n)
  | fma (a b c : Expr f n)
  deriving DecidableEq, Repr

namespace Expr

variable {n : Nat}

/-- Evaluation with the flag-free IEEE semantics. -/
def eval (env : Fin n → FP f) : Expr f n → FP f
  | .var i => env i
  | .lit c => c
  | .neg a => (a.eval env).neg
  | .add a b => Toy.Float.add (a.eval env) (b.eval env)
  | .sub a b => Toy.Float.sub (a.eval env) (b.eval env)
  | .mul a b => Toy.Float.mul (a.eval env) (b.eval env)
  | .fma a b c => Toy.Float.fma (a.eval env) (b.eval env) (c.eval env)

/-- Every argument and result occurring in the evaluation: the values of all
nodes (variables, literals and operations). -/
def nodeVals (env : Fin n → FP f) : Expr f n → List (FP f)
  | .var i => [env i]
  | .lit c => [c]
  | .neg a => (Expr.neg a).eval env :: a.nodeVals env
  | .add a b => (Expr.add a b).eval env :: (a.nodeVals env ++ b.nodeVals env)
  | .sub a b => (Expr.sub a b).eval env :: (a.nodeVals env ++ b.nodeVals env)
  | .mul a b => (Expr.mul a b).eval env :: (a.nodeVals env ++ b.nodeVals env)
  | .fma a b c => (Expr.fma a b c).eval env ::
      (a.nodeVals env ++ b.nodeVals env ++ c.nodeVals env)

/-- One reassociation step at an `add` node whose children are `a`, `b`. -/
def reassocAdd (a b : Expr f n) : List (Expr f n) :=
  (match a with | .add x y => [Expr.add x (Expr.add y b)] | _ => []) ++
  (match b with | .add y z => [Expr.add (Expr.add a y) z] | _ => [])

/-- One reassociation step at a `mul` node whose children are `a`, `b`. -/
def reassocMul (a b : Expr f n) : List (Expr f n) :=
  (match a with | .mul x y => [Expr.mul x (Expr.mul y b)] | _ => []) ++
  (match b with | .mul y z => [Expr.mul (Expr.mul a y) z] | _ => [])

/-- Contraction of a product feeding an `add` node: `x*y + b → fma x y b`,
`a + x*y → fma x y a`. -/
def contractAdd (a b : Expr f n) : List (Expr f n) :=
  (match a with | .mul x y => [Expr.fma x y b] | _ => []) ++
  (match b with | .mul x y => [Expr.fma x y a] | _ => [])

/-- Contraction of a product feeding a `sub` node: `x*y - b → fma x y (-b)`,
`a - x*y → fma (-x) y a`. -/
def contractSub (a b : Expr f n) : List (Expr f n) :=
  (match a with | .mul x y => [Expr.fma x y (Expr.neg b)] | _ => []) ++
  (match b with | .mul x y => [Expr.fma (Expr.neg x) y a] | _ => [])

/-- The forms of an expression that the permissions in `S` allow a compiler
to evaluate instead of it: at every node, after choosing forms of the
children, the node itself, plus (if `S.reassoc`) one reassociation step at an
`add`/`mul` node, plus (if `S.contract`) one contraction of a product into an
`add`/`sub` node. With no permissions this is `[e]` (`variants_noPerm`). -/
def variants (S : Flags) : Expr f n → List (Expr f n)
  | .var i => [.var i]
  | .lit c => [.lit c]
  | .neg a => (a.variants S).map .neg
  | .add a b => (a.variants S).flatMap fun a' => (b.variants S).flatMap fun b' =>
      Expr.add a' b' :: ((if S.reassoc then reassocAdd a' b' else []) ++
        (if S.contract then contractAdd a' b' else []))
  | .sub a b => (a.variants S).flatMap fun a' => (b.variants S).flatMap fun b' =>
      Expr.sub a' b' :: (if S.contract then contractSub a' b' else [])
  | .mul a b => (a.variants S).flatMap fun a' => (b.variants S).flatMap fun b' =>
      Expr.mul a' b' :: (if S.reassoc then reassocMul a' b' else [])
  | .fma a b c => (a.variants S).flatMap fun a' => (b.variants S).flatMap fun b' =>
      (c.variants S).map fun c' => Expr.fma a' b' c'

end Expr

variable {n : Nat}

/-- The inputs on which the source expression `e` is defined under the
restrictions in `S` (in LLVM terms: on which it is not poison): with `nnan`,
no argument or result of any node is NaN; with `ninf`, none is infinite. -/
def Admissible (S : Flags) (e : Expr f n) (env : Fin n → FP f) : Prop :=
  ∀ v ∈ e.nodeVals env, (S.nnan = true → v.isNaN = false) ∧ (S.ninf = true → v.isInf = false)

instance (S : Flags) (e : Expr f n) (env : Fin n → FP f) : Decidable (Admissible S e env) :=
  inferInstanceAs (Decidable (∀ v ∈ _, _))

/-- The result relation under `S`: equality of values (`=` on `FP f`), or equality
up to the sign of zero if `S.nsz`. -/
def Rel (S : Flags) (x y : FP f) : Prop := if S.nsz then EqNsz x y else x = y

instance (S : Flags) (x y : FP f) : Decidable (Rel S x y) := by
  unfold Rel; split <;> infer_instance

/-- A rewrite `lhs → rhs` over `n` variables. -/
structure Rewrite (f : Fmt) (n : Nat) where
  lhs : Expr f n
  rhs : Expr f n

/-- `lhs → rhs` is valid modulo `S`: on every input admissible for `lhs` under
`S`, the result of `rhs` is related by `Rel S` to the result of some form of
`lhs` permitted by `S`. -/
def ValidMod (S : Flags) (r : Rewrite f n) : Prop :=
  ∀ env : Fin n → FP f, Admissible S r.lhs env →
    ∃ v ∈ r.lhs.variants S, Rel S (r.rhs.eval env) (v.eval env)

/-- Flag-free validity: `ValidMod` with no flags (equivalent to bitwise
equality on all inputs, `valid_iff_forall_eq`). -/
def Valid (r : Rewrite f n) : Prop := ValidMod {} r

end Toy.Float
