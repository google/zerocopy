/-!
# Core definitions for fixed-width machine-integer refinement and overflow obligations

This module models fixed-width unsigned (`u<n>`) and signed two's-complement (`i<n>`)
machine integers using Lean core's `BitVec n` (`toNat` and `toInt`), together with:
- Side-condition predicates (`PosWidth`, `WidthLe`, `ShiftInBounds`, `InUnsignedRange`,
  `InSignedRange`, `Ult`, `Slt`, `NoUAddOverflow`, `NoSAddOverflow`, `NonZeroDiv`,
  `NoSDivOverflow`);
- An explicit failure outcome (`Outcome`) used by `evalPlainU`/`evalPlainS` to model runtime
  panic vs normal return for plain ring operators under overflow-checked execution
  (division/remainder and shifts are modeled separately via `Option`-returning `checked*`
  and total `wrapping*` operations);
- Ring expressions (`RingExpr`), mathematical integer evaluation (`evalInt`), wrapping
  evaluation (`evalWrap`), checked evaluation (`evalCheckedU`, `evalCheckedS`), plain
  panicking evaluation (`evalPlainU`, `evalPlainS`), and per-subexpression range predicates
  (`SubexprsInRange`);
- Checked truncating and Euclidean division/remainder (`checkedUDiv`, `checkedURem`,
  `checkedSDiv`, `checkedSRem`, `sdivEuclid`, `sremEuclid`, `checkedSDivEuclid`,
  `checkedSRemEuclid`);
- Wrapping/masked and checked shifts (`wrappingShl`, `wrappingUShr`, `wrappingSShr`,
  `checkedShl`, `checkedUShr`, `checkedSShr`);
- Numeric `as` casts (`castFromUnsigned`, `castFromSigned`, `reinterpretCast`).
-/

namespace Toy.MachInt

/-! ## Width, shift, and representable-range predicates -/

/-- Positive bitwidth predicate (`n > 0`). Rules out degenerate zero-width bitvectors
    (`BitVec 0`), where `-1#0 = 0#0 = intMin 0` and `(intMin 0).toInt = 0`. -/
def PosWidth (n : Nat) : Prop :=
  0 < n

instance instDecidablePosWidth (n : Nat) : Decidable (PosWidth n) :=
  inferInstanceAs (Decidable (0 < n))

/-- Non-decreasing width predicate (`m ≤ n`), characterizing widening/same-width casts
    versus narrowing (truncating) casts. -/
def WidthLe (m n : Nat) : Prop :=
  m ≤ n

instance instDecidableWidthLe (m n : Nat) : Decidable (WidthLe m n) :=
  inferInstanceAs (Decidable (m ≤ n))

/-- Shift-amount bounds predicate (`k < n`), matching Rust's checked shift precondition
    that a shift count be strictly less than the bitwidth of the shifted type. -/
def ShiftInBounds (n k : Nat) : Prop :=
  k < n

instance instDecidableShiftInBounds (n k : Nat) : Decidable (ShiftInBounds n k) :=
  inferInstanceAs (Decidable (k < n))

/-- Signed minimum representable mathematical integer for width `n`
    (`-(2^(n-1))` for `n > 0`, and `0` for `n = 0`). -/
def sMinVal (n : Nat) : Int :=
  (BitVec.intMin n).toInt

/-- Signed maximum representable mathematical integer for width `n`
    (`2^(n-1) - 1` for `n > 0`, and `0` for `n = 0`). -/
def sMaxVal (n : Nat) : Int :=
  (BitVec.intMax n).toInt

/-- Unsigned representable range for width `n`: `0 ≤ z < 2^n`, capturing the exact image
    of `BitVec.toNat : BitVec n → Nat` embedded into `Int`. -/
def InUnsignedRange (n : Nat) (z : Int) : Prop :=
  0 ≤ z ∧ z < ((2 ^ n : Nat) : Int)

/-- Signed two's-complement representable range for width `n`: `sMinVal n ≤ z ≤ sMaxVal n`,
    capturing the exact image of `BitVec.toInt : BitVec n → Int` (including the edge case `n = 0`
    where the unique value is `0`). -/
def InSignedRange (n : Nat) (z : Int) : Prop :=
  sMinVal n ≤ z ∧ z ≤ sMaxVal n

instance instDecidableInUnsignedRange (n : Nat) (z : Int) :
    Decidable (InUnsignedRange n z) :=
  inferInstanceAs (Decidable (0 ≤ z ∧ z < ((2 ^ n : Nat) : Int)))

instance instDecidableInSignedRange (n : Nat) (z : Int) :
    Decidable (InSignedRange n z) :=
  inferInstanceAs (Decidable (sMinVal n ≤ z ∧ z ≤ sMaxVal n))

/-! ## Explicit failure outcome for plain panicking ring operators -/

/-- Explicit evaluation outcome used by `evalPlainU` and `evalPlainS` for plain Rust ring
    operators when overflow checks are enabled: either a normal value `ok val` or an explicit
    `panic` failure. Models Rust's non-UB overflow-as-error semantics for ring expressions;
    plain division, remainder, and shift operators do not have separate `Outcome` evaluators
    in this module and are modeled via `checked*` and `wrapping*` below. -/
inductive Outcome (α : Type) : Type
  | ok (val : α)
  | panic
  deriving DecidableEq, Repr

/-- Converts an `Option α` from a checked operation into an explicit `Outcome α`,
    mapping `some v` to `Outcome.ok v` and `none` to `Outcome.panic`. -/
def Outcome.ofOption {α : Type} : Option α → Outcome α
  | some v => .ok v
  | none => .panic

/-! ## Ring expressions, wrapping evaluation, and checked/plain evaluation -/

/-- Pure integer/bitvector expression AST over variables, typed integer constants (`lit`),
    unary negation, addition, subtraction, and multiplication. Captures straight-line ring
    expressions in machine-integer programs. Note that `.lit val` represents a typed constant
    value rather than a surface Rust integer literal token: Rust has no negative literal tokens
    (analyzing `-128_i8` as unary `-` applied to `128_i8`, exempted from overflow by
    `[expr.operator.int-overflow.unary-neg]`), rejects out-of-range literals at compile time
    via the deny-by-default `overflowing_literals` lint (or truncates them when allowed), and
    rejects unary `-` on unsigned types with error `E0600`. -/
inductive RingExpr : Type
  | var (idx : Nat)
  | lit (val : Int)
  | neg (e : RingExpr)
  | add (e₁ e₂ : RingExpr)
  | sub (e₁ e₂ : RingExpr)
  | mul (e₁ e₂ : RingExpr)
  deriving DecidableEq, Repr

/-- Evaluates a `RingExpr` in unbounded mathematical integers `Int` under environment `ρ`. -/
def evalInt (ρ : Nat → Int) : RingExpr → Int
  | .var i => ρ i
  | .lit k => k
  | .neg e => -(evalInt ρ e)
  | .add e₁ e₂ => evalInt ρ e₁ + evalInt ρ e₂
  | .sub e₁ e₂ => evalInt ρ e₁ - evalInt ρ e₂
  | .mul e₁ e₂ => evalInt ρ e₁ * evalInt ρ e₂

/-- Mathematical integer ring identity between two `RingExpr`s: they evaluate identically
    under every integer valuation `ρ : Nat → Int`. -/
def IntRingIdentity (e₁ e₂ : RingExpr) : Prop :=
  ∀ ρ : Nat → Int, evalInt ρ e₁ = evalInt ρ e₂

/-- Evaluates a `RingExpr` using fixed-width wrapping arithmetic (`BitVec n`), modeling
    Rust's explicit `wrapping_neg`, `wrapping_add`, `wrapping_sub`, `wrapping_mul`, and
    `Wrapping<T>` modulo `2^n`. (Plain operators wrapping when overflow checks are disabled
    is `rustc` behavior rather than a Rust Reference language guarantee, as non-debug builds
    may either panic or wrap at the implementation's discretion.) Constants are reduced via
    `BitVec.ofInt n`. -/
def evalWrap (n : Nat) (env : Nat → BitVec n) : RingExpr → BitVec n
  | .var i => env i
  | .lit k => BitVec.ofInt n k
  | .neg e => -(evalWrap n env e)
  | .add e₁ e₂ => evalWrap n env e₁ + evalWrap n env e₂
  | .sub e₁ e₂ => evalWrap n env e₁ - evalWrap n env e₂
  | .mul e₁ e₂ => evalWrap n env e₁ * evalWrap n env e₂

/-- Checked unsigned negation: returns `some 0#n` iff `a = 0#n`, and `none` otherwise
    (matching Rust `u<n>::checked_neg`). -/
def checkedUNeg {n : Nat} (a : BitVec n) : Option (BitVec n) :=
  if a == 0#n then some 0#n else none

/-- Checked unsigned addition (`u<n>::checked_add`), returning `none` iff `BitVec.uaddOverflow a b`. -/
def checkedUAdd {n : Nat} (a b : BitVec n) : Option (BitVec n) :=
  if BitVec.uaddOverflow a b then none else some (a + b)

/-- Checked unsigned subtraction (`u<n>::checked_sub`), returning `none` iff `BitVec.usubOverflow a b`. -/
def checkedUSub {n : Nat} (a b : BitVec n) : Option (BitVec n) :=
  if BitVec.usubOverflow a b then none else some (a - b)

/-- Checked unsigned multiplication (`u<n>::checked_mul`), returning `none` iff `BitVec.umulOverflow a b`. -/
def checkedUMul {n : Nat} (a b : BitVec n) : Option (BitVec n) :=
  if BitVec.umulOverflow a b then none else some (a * b)

/-- Checked signed negation (`i<n>::checked_neg`), returning `none` iff `BitVec.negOverflow a`
    (i.e. `a = intMin n` for `n > 0`). -/
def checkedSNeg {n : Nat} (a : BitVec n) : Option (BitVec n) :=
  if BitVec.negOverflow a then none else some (-a)

/-- Checked signed addition (`i<n>::checked_add`), returning `none` iff `BitVec.saddOverflow a b`. -/
def checkedSAdd {n : Nat} (a b : BitVec n) : Option (BitVec n) :=
  if BitVec.saddOverflow a b then none else some (a + b)

/-- Checked signed subtraction (`i<n>::checked_sub`), returning `none` iff `BitVec.ssubOverflow a b`. -/
def checkedSSub {n : Nat} (a b : BitVec n) : Option (BitVec n) :=
  if BitVec.ssubOverflow a b then none else some (a - b)

/-- Checked signed multiplication (`i<n>::checked_mul`), returning `none` iff `BitVec.smulOverflow a b`. -/
def checkedSMul {n : Nat} (a b : BitVec n) : Option (BitVec n) :=
  if BitVec.smulOverflow a b then none else some (a * b)

/-- Evaluates a `RingExpr` with checked unsigned operations (`u<n>`). Variables come from `env`;
    `.lit k` checks `InUnsignedRange n k`; `.neg` models `u<n>::checked_neg` (unary `-` is not
    valid on Rust unsigned types); intermediate operations propagate `none` on overflow. -/
def evalCheckedU (n : Nat) (env : Nat → BitVec n) : RingExpr → Option (BitVec n)
  | .var i => some (env i)
  | .lit k => if InUnsignedRange n k then some (BitVec.ofInt n k) else none
  | .neg e => (evalCheckedU n env e).bind checkedUNeg
  | .add e₁ e₂ => (evalCheckedU n env e₁).bind fun v₁ =>
      (evalCheckedU n env e₂).bind fun v₂ => checkedUAdd v₁ v₂
  | .sub e₁ e₂ => (evalCheckedU n env e₁).bind fun v₁ =>
      (evalCheckedU n env e₂).bind fun v₂ => checkedUSub v₁ v₂
  | .mul e₁ e₂ => (evalCheckedU n env e₁).bind fun v₁ =>
      (evalCheckedU n env e₂).bind fun v₂ => checkedUMul v₁ v₂

/-- Evaluates a `RingExpr` with checked signed two's-complement operations (`i<n>`). Variables come
    from `env`; `.lit k` checks `InSignedRange n k` (modeling typed constants such as `-128_i8`
    via `.lit (-128)`, whereas `.neg (.lit 128)` panics because `128` is out of range and
    `.neg` models runtime negation); intermediate operations propagate `none` on overflow. -/
def evalCheckedS (n : Nat) (env : Nat → BitVec n) : RingExpr → Option (BitVec n)
  | .var i => some (env i)
  | .lit k => if InSignedRange n k then some (BitVec.ofInt n k) else none
  | .neg e => (evalCheckedS n env e).bind checkedSNeg
  | .add e₁ e₂ => (evalCheckedS n env e₁).bind fun v₁ =>
      (evalCheckedS n env e₂).bind fun v₂ => checkedSAdd v₁ v₂
  | .sub e₁ e₂ => (evalCheckedS n env e₁).bind fun v₁ =>
      (evalCheckedS n env e₂).bind fun v₂ => checkedSSub v₁ v₂
  | .mul e₁ e₂ => (evalCheckedS n env e₁).bind fun v₁ =>
      (evalCheckedS n env e₂).bind fun v₂ => checkedSMul v₁ v₂

/-- Plain overflow-checked unsigned evaluation: returns `Outcome.ok v` when every step stays in
    range and `Outcome.panic` when any constant or intermediate operation overflows. Note that
    `.neg` uses `checkedUNeg` (which has no Rust plain-operator counterpart, as unary `-` on
    unsigned types is compile error `E0600`), and out-of-range `.lit` constants yield `panic`
    rather than compile-time rejection. -/
def evalPlainU (n : Nat) (env : Nat → BitVec n) (e : RingExpr) : Outcome (BitVec n) :=
  Outcome.ofOption (evalCheckedU n env e)

/-- Plain overflow-checked signed evaluation: returns `Outcome.ok v` when every step stays in
    range and `Outcome.panic` when any constant or intermediate operation overflows. Out-of-range
    `.lit` constants yield `panic` rather than compile-time rejection, and negated literals such as
    `-128_i8` must be represented as `.lit (-128)` rather than `.neg (.lit 128)`. -/
def evalPlainS (n : Nat) (env : Nat → BitVec n) (e : RingExpr) : Outcome (BitVec n) :=
  Outcome.ofOption (evalCheckedS n env e)

/-- Recursive side condition asserting that `evalInt ρ` satisfies range predicate `P` at the
    root and at every subexpression of `e`. Captures the per-subexpression range predicate
    guaranteeing that no intermediate subexpression overflows. -/
def SubexprsInRange (P : Int → Prop) (ρ : Nat → Int) : RingExpr → Prop
  | .var i => P (ρ i)
  | .lit k => P k
  | .neg e => SubexprsInRange P ρ e ∧ P (evalInt ρ (.neg e))
  | .add e₁ e₂ => SubexprsInRange P ρ e₁ ∧ SubexprsInRange P ρ e₂ ∧ P (evalInt ρ (.add e₁ e₂))
  | .sub e₁ e₂ => SubexprsInRange P ρ e₁ ∧ SubexprsInRange P ρ e₂ ∧ P (evalInt ρ (.sub e₁ e₂))
  | .mul e₁ e₂ => SubexprsInRange P ρ e₁ ∧ SubexprsInRange P ρ e₂ ∧ P (evalInt ρ (.mul e₁ e₂))

instance instDecidableSubexprsInRange {P : Int → Prop} [DecidablePred P] (ρ : Nat → Int) :
    (e : RingExpr) → Decidable (SubexprsInRange P ρ e)
  | .var i => inferInstanceAs (Decidable (P (ρ i)))
  | .lit k => inferInstanceAs (Decidable (P k))
  | .neg e =>
      @instDecidableAnd _ _ (instDecidableSubexprsInRange ρ e)
        (inferInstanceAs (Decidable (P (evalInt ρ (.neg e)))))
  | .add e₁ e₂ =>
      @instDecidableAnd _ _ (instDecidableSubexprsInRange ρ e₁)
        (@instDecidableAnd _ _ (instDecidableSubexprsInRange ρ e₂)
          (inferInstanceAs (Decidable (P (evalInt ρ (.add e₁ e₂))))))
  | .sub e₁ e₂ =>
      @instDecidableAnd _ _ (instDecidableSubexprsInRange ρ e₁)
        (@instDecidableAnd _ _ (instDecidableSubexprsInRange ρ e₂)
          (inferInstanceAs (Decidable (P (evalInt ρ (.sub e₁ e₂))))))
  | .mul e₁ e₂ =>
      @instDecidableAnd _ _ (instDecidableSubexprsInRange ρ e₁)
        (@instDecidableAnd _ _ (instDecidableSubexprsInRange ρ e₂)
          (inferInstanceAs (Decidable (P (evalInt ρ (.mul e₁ e₂))))))

/-! ## Order and addition-overflow predicates -/

/-- Unsigned strict less-than (`a < b` on `u<n>`). -/
def Ult {n : Nat} (a b : BitVec n) : Prop :=
  a.ult b = true

instance instDecidableUlt {n : Nat} (a b : BitVec n) : Decidable (Ult a b) :=
  inferInstanceAs (Decidable (a.ult b = true))

/-- Signed strict less-than (`a < b` on `i<n>`). -/
def Slt {n : Nat} (a b : BitVec n) : Prop :=
  a.slt b = true

instance instDecidableSlt {n : Nat} (a b : BitVec n) : Decidable (Slt a b) :=
  inferInstanceAs (Decidable (a.slt b = true))

/-- Absence of unsigned addition overflow for `a + b`. -/
def NoUAddOverflow {n : Nat} (a b : BitVec n) : Prop :=
  BitVec.uaddOverflow a b = false

instance instDecidableNoUAddOverflow {n : Nat} (a b : BitVec n) : Decidable (NoUAddOverflow a b) :=
  inferInstanceAs (Decidable (BitVec.uaddOverflow a b = false))

/-- Absence of signed addition overflow for `a + b`. -/
def NoSAddOverflow {n : Nat} (a b : BitVec n) : Prop :=
  BitVec.saddOverflow a b = false

instance instDecidableNoSAddOverflow {n : Nat} (a b : BitVec n) : Decidable (NoSAddOverflow a b) :=
  inferInstanceAs (Decidable (BitVec.saddOverflow a b = false))

/-! ## Division and remainder operations and predicates -/

/-- Nonzero divisor predicate (`b ≠ 0#n`), guarding against division-by-zero panic. -/
def NonZeroDiv {n : Nat} (b : BitVec n) : Prop :=
  b ≠ 0#n

instance instDecidableNonZeroDiv {n : Nat} (b : BitVec n) : Decidable (NonZeroDiv b) :=
  inferInstanceAs (Decidable (b ≠ 0#n))

/-- Absence of the unique signed two's-complement division overflow (`a = MIN ∧ b = -1`). -/
def NoSDivOverflow {n : Nat} (a b : BitVec n) : Prop :=
  ¬ (a = BitVec.intMin n ∧ b = -1#n)

instance instDecidableNoSDivOverflow {n : Nat} (a b : BitVec n) : Decidable (NoSDivOverflow a b) :=
  inferInstanceAs (Decidable (¬ (a = BitVec.intMin n ∧ b = -1#n)))

/-- Checked unsigned division (`u<n>::checked_div`), returning `none` iff `b = 0`. -/
def checkedUDiv {n : Nat} (a b : BitVec n) : Option (BitVec n) :=
  if b == 0#n then none else some (a / b)

/-- Checked unsigned remainder (`u<n>::checked_rem`), returning `none` iff `b = 0`. -/
def checkedURem {n : Nat} (a b : BitVec n) : Option (BitVec n) :=
  if b == 0#n then none else some (a % b)

/-- Checked signed truncating division (`i<n>::checked_div`), returning `none` if `b = 0` or
    `a = intMin n ∧ b = -1`. -/
def checkedSDiv {n : Nat} (a b : BitVec n) : Option (BitVec n) :=
  if b == 0#n || (a == BitVec.intMin n && b == -1#n) then none else some (a.sdiv b)

/-- Checked signed truncating remainder (`i<n>::checked_rem`), returning `none` if `b = 0` or
    `a = intMin n ∧ b = -1` (even though `MIN.toInt.tmod (-1) = 0` mathematically fits in `i<n>`). -/
def checkedSRem {n : Nat} (a b : BitVec n) : Option (BitVec n) :=
  if b == 0#n || (a == BitVec.intMin n && b == -1#n) then none else some (a.srem b)

/-- Euclidean signed division on bitvectors, matching Rust `i<n>::div_euclid`: adjusts
    truncating division `q = a.sdiv b` so the accompanying remainder is nonnegative. -/
def sdivEuclid {n : Nat} (a b : BitVec n) : BitVec n :=
  let q := a.sdiv b
  let r := a.srem b
  if r.slt 0#n then
    if (0#n).slt b then q - 1#n else q + 1#n
  else
    q

/-- Euclidean signed remainder on bitvectors, matching Rust `i<n>::rem_euclid`: adjusts
    truncating remainder `r = a.srem b` by `+ |b|` when `r < 0`. -/
def sremEuclid {n : Nat} (a b : BitVec n) : BitVec n :=
  let r := a.srem b
  if r.slt 0#n then r + b.abs else r

/-- Checked Euclidean signed division (`i<n>::checked_div_euclid`), returning `none` if `b = 0`
    or `a = intMin n ∧ b = -1`. -/
def checkedSDivEuclid {n : Nat} (a b : BitVec n) : Option (BitVec n) :=
  if b == 0#n || (a == BitVec.intMin n && b == -1#n) then none else some (sdivEuclid a b)

/-- Checked Euclidean signed remainder (`i<n>::checked_rem_euclid`), returning `none` if `b = 0`
    or `a = intMin n ∧ b = -1`. -/
def checkedSRemEuclid {n : Nat} (a b : BitVec n) : Option (BitVec n) :=
  if b == 0#n || (a == BitVec.intMin n && b == -1#n) then none else some (sremEuclid a b)

/-! ## Shift operations -/

/-- Wrapping left shift (`u<n>::wrapping_shl` / `i<n>::wrapping_shl`): masks shift count `k`
    modulo `n`. Agrees with Rust `core::num`'s `k & (BITS - 1)` mask if and only if `n` is a
    power of two (`n = 2^m`, covering all Rust fixed-width integer types `8`..`128`), and
    diverges at non-power-of-two widths (e.g. `n = 3, k = 4`). -/
def wrappingShl {n : Nat} (x : BitVec n) (k : Nat) : BitVec n :=
  x <<< (k % n)

/-- Wrapping logical right shift (`u<n>::wrapping_shr`): masks shift count `k` modulo `n`.
    Agrees with Rust `core::num`'s `k & (BITS - 1)` mask iff `n` is a power of two. -/
def wrappingUShr {n : Nat} (x : BitVec n) (k : Nat) : BitVec n :=
  x >>> (k % n)

/-- Wrapping arithmetic right shift (`i<n>::wrapping_shr`): masks shift count `k` modulo `n`.
    Agrees with Rust `core::num`'s `k & (BITS - 1)` mask iff `n` is a power of two. -/
def wrappingSShr {n : Nat} (x : BitVec n) (k : Nat) : BitVec n :=
  x.sshiftRight (k % n)

/-- Checked left shift (`u<n>::checked_shl` / `i<n>::checked_shl`), returning `none` when `k ≥ n`. -/
def checkedShl {n : Nat} (x : BitVec n) (k : Nat) : Option (BitVec n) :=
  if k < n then some (x <<< k) else none

/-- Checked logical right shift (`u<n>::checked_shr`), returning `none` when `k ≥ n`. -/
def checkedUShr {n : Nat} (x : BitVec n) (k : Nat) : Option (BitVec n) :=
  if k < n then some (x >>> k) else none

/-- Checked arithmetic right shift (`i<n>::checked_shr`), returning `none` when `k ≥ n`. -/
def checkedSShr {n : Nat} (x : BitVec n) (k : Nat) : Option (BitVec n) :=
  if k < n then some (x.sshiftRight k) else none

/-! ## Numeric `as` casts -/

/-- Numeric `as` cast from an unsigned `n`-bit integer to an `m`-bit integer (`u<n> as u<m>`
    or `u<n> as i<m>`): zero-extends when `n ≤ m` and truncates high bits when `m < n`. -/
def castFromUnsigned {n : Nat} (m : Nat) (x : BitVec n) : BitVec m :=
  x.setWidth m

/-- Numeric `as` cast from a signed `n`-bit integer to an `m`-bit integer (`i<n> as i<m>`
    or `i<n> as u<m>`): sign-extends when `n ≤ m` and truncates high bits when `m < n`. -/
def castFromSigned {n : Nat} (m : Nat) (x : BitVec n) : BitVec m :=
  x.signExtend m

/-- Same-width `as` cast (`i<n> as u<n>` or `u<n> as i<n>`): preserves the raw bit pattern as a
    no-op reinterpretation between unsigned (`toNat`) and two's-complement signed (`toInt`). -/
def reinterpretCast {n : Nat} (x : BitVec n) : BitVec n :=
  x

end Toy.MachInt
