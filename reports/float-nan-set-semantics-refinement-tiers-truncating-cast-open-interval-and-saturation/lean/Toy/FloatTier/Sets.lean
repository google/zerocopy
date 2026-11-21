/-
Toy.FloatTier.Sets
==================

The set-valued (nondeterministic) primitive semantics and its deterministic
refinements ("tiers").

* `Extra f`: a target-specific set of "extra" NaN payloads, which may depend on
  the operand values.
* `NaNChoice X x y r`: `r` is an allowed NaN result of an arithmetic operation
  with operands `x`, `y`: a NaN with any sign whose quiet bit and payload are
  chosen by one of the four rules (preferred, quieting propagation, unchanged
  propagation, target-specific).
* `primSet X p x y r`: `r` is an allowed result of the primitive `p` on `x`,
  `y`. For `add`, `sub`, `mul` the result is the correctly rounded IEEE result
  when that is not NaN, and otherwise any element of `NaNChoice`. For `min`,
  `max`: if exactly one operand is NaN the other is returned; if both are NaN,
  any element of `NaNChoice`; if the operands compare equal (for example `+0`
  and `-0`), either operand.
* `Tier f`: a deterministic choice function for the primitives. It is
  site-independent and context-free: the same primitive on the same operands
  gets the same result at every occurrence. `TierSound X τ`: every choice of
  `τ` is allowed by `primSet X`.
* `tierOf pol`: the tier determined by a `ChoicePolicy` (NaN sign, whether to
  propagate the first NaN operand's payload, which operand `min`/`max` return
  on equal operands). `tierCtfe` and `tierRunA` are two such tiers. They are
  toy examples and are not claimed to be the choices of any real interpreter
  or target.
-/
import Toy.FloatTier.NaNVal

namespace Toy.FloatTier

variable {f : Fmt}

/-- Target-specific extra NaN payloads as a function of the two operands:
`X x y k = true` means payload `k` may be chosen (with the quiet bit set). -/
abbrev Extra (f : Fmt) := V f → V f → Nat → Bool

/-- No extra payloads. -/
def noExtra : Extra f := fun _ _ _ => false

/-- The NaN results allowed for an arithmetic operation with operands `x`,
`y`: `r` is a NaN (any sign) and one of
(1) preferred NaN: quiet bit set, payload `0`;
(2) quieting propagation: quiet bit set, payload of an operand that is a NaN;
(3) unchanged propagation: quiet bit and payload of an operand that is a NaN;
(4) target-specific: quiet bit set, payload `k` with `X x y k`. -/
def NaNChoice (X : Extra f) (x y r : V f) : Prop :=
  r.isNaN = true ∧
    ((r.isQuiet = true ∧ r.payload = 0) ∨
     (∃ z ∈ [x, y], z.isNaN = true ∧ r.isQuiet = true ∧ r.payload = z.payload) ∨
     (∃ z ∈ [x, y], z.isNaN = true ∧ r.isQuiet = z.isQuiet ∧ r.payload = z.payload) ∨
     (r.isQuiet = true ∧ X x y r.payload = true))

instance (X : Extra f) (x y r : V f) : Decidable (NaNChoice X x y r) := by
  unfold NaNChoice; infer_instance

/-- The primitives with set-valued results. -/
inductive Prim where
  | add | sub | mul | min | max
  deriving DecidableEq, Repr

/-- Results allowed for an arithmetic operation whose NaN-collapsed IEEE result
is `c`: exactly `c` if `c` is not NaN, otherwise any allowed NaN. -/
def arithSet (X : Extra f) (c : FP f) (x y r : V f) : Prop :=
  if c.isNaN then NaNChoice X x y r else r = V.ofFP c

/-- Results allowed for `min x y`. -/
def minSet (X : Extra f) (x y r : V f) : Prop :=
  if x.isNaN && y.isNaN then NaNChoice X x y r
  else if x.isNaN then r = y
  else if y.isNaN then r = x
  else if lt x.toFP y.toFP then r = x
  else if lt y.toFP x.toFP then r = y
  else r = x ∨ r = y

/-- Results allowed for `max x y`. -/
def maxSet (X : Extra f) (x y r : V f) : Prop :=
  if x.isNaN && y.isNaN then NaNChoice X x y r
  else if x.isNaN then r = y
  else if y.isNaN then r = x
  else if lt y.toFP x.toFP then r = x
  else if lt x.toFP y.toFP then r = y
  else r = x ∨ r = y

/-- The set-valued primitive semantics `S` with extra payload set `X`. -/
def primSet (X : Extra f) : Prim → V f → V f → V f → Prop
  | .add, x, y, r => arithSet X (add x.toFP y.toFP) x y r
  | .sub, x, y, r => arithSet X (sub x.toFP y.toFP) x y r
  | .mul, x, y, r => arithSet X (mul x.toFP y.toFP) x y r
  | .min, x, y, r => minSet X x y r
  | .max, x, y, r => maxSet X x y r

instance (X : Extra f) (p : Prim) (x y r : V f) : Decidable (primSet X p x y r) := by
  cases p <;> simp only [primSet, arithSet, minSet, maxSet] <;> infer_instance

/-- A deterministic tier: one result for each primitive and pair of operands,
the same at every occurrence (site-independent and context-free). -/
abbrev Tier (f : Fmt) := Prim → V f → V f → V f

/-- Every choice of `τ` lies in the corresponding set of `S` (with extra
payloads `X`). -/
def TierSound (X : Extra f) (τ : Tier f) : Prop := ∀ p x y, primSet X p x y (τ p x y)

/-- A fixed rule for resolving every choice of `S` without extra payloads. -/
structure ChoicePolicy where
  /-- sign bit of every NaN result -/
  nanNeg : Bool
  /-- if an operand is a NaN, quiet-propagate the payload of the first such
  operand (otherwise always return the preferred NaN) -/
  propagate : Bool
  /-- on operands that compare equal, `min`/`max` return the second operand
  (otherwise the first) -/
  eqSecond : Bool
  deriving DecidableEq, Repr

/-- The NaN result chosen by `pol` for operands `x`, `y`. -/
def ChoicePolicy.nanResult (pol : ChoicePolicy) (x y : V f) : V f :=
  if pol.propagate && x.isNaN then V.quieted pol.nanNeg x
  else if pol.propagate && y.isNaN then V.quieted pol.nanNeg y
  else V.prefNaN f pol.nanNeg

/-- The result chosen by `pol` for an arithmetic operation with NaN-collapsed
IEEE result `c`. -/
def ChoicePolicy.arith (pol : ChoicePolicy) (c : FP f) (x y : V f) : V f :=
  if c.isNaN then pol.nanResult x y else V.ofFP c

/-- The tier determined by a policy. -/
def tierOf (pol : ChoicePolicy) : Tier f
  | .add, x, y => pol.arith (add x.toFP y.toFP) x y
  | .sub, x, y => pol.arith (sub x.toFP y.toFP) x y
  | .mul, x, y => pol.arith (mul x.toFP y.toFP) x y
  | .min, x, y =>
    if x.isNaN && y.isNaN then pol.nanResult x y
    else if x.isNaN then y
    else if y.isNaN then x
    else if lt x.toFP y.toFP then x
    else if lt y.toFP x.toFP then y
    else if pol.eqSecond then y else x
  | .max, x, y =>
    if x.isNaN && y.isNaN then pol.nanResult x y
    else if x.isNaN then y
    else if y.isNaN then x
    else if lt y.toFP x.toFP then x
    else if lt x.toFP y.toFP then y
    else if pol.eqSecond then y else x

/-- Example compile-time policy: positive preferred NaN, first operand on ties.
A toy example; not a claim about any real interpreter. -/
def ctfePolicy : ChoicePolicy := ⟨false, false, false⟩

/-- Example run-time policy: negative NaNs, quieting propagation of the first
NaN operand, second operand on ties. A toy example; not a claim about any real
target. -/
def runPolicyA : ChoicePolicy := ⟨true, true, true⟩

/-- The example compile-time tier `T_ctfe`. -/
def tierCtfe : Tier f := tierOf ctfePolicy

/-- The example run-time tier `T_run(A)`. -/
def tierRunA : Tier f := tierOf runPolicyA

end Toy.FloatTier
