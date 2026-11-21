/-
Toy.FloatTier.NaNVal
====================

Payload-carrying floating-point values `V f`: the values of `FP f`
(`Toy.FloatTier.Base`) with every NaN refined into its sign bit, quiet bit and
payload, as in the IEEE 754 interchange encoding.

* The trailing significand field of a NaN has `p - 1` bits. Its top bit is the
  quiet bit (`1` = quiet, the convention recommended since IEEE 754-2008; targets
  that invert it are not modelled), and the remaining `p - 2` bits are the
  payload, so there are `payCount f = 2^(p-2)` payloads.
* A quiet NaN may have any payload. A signaling NaN must have a nonzero payload,
  because the all-zero trailing significand encodes an infinity. `snan s k`
  therefore stores `k` with payload `k + 1`, and every term of `V f` is a valid
  encoding. In formats with `p = 2` there are no signaling NaNs.
* `V.toFP` forgets the sign, quiet bit and payload of a NaN, giving the
  NaN-collapsed view used by the arithmetic of `Toy.FloatTier.Base`.
* The bit-level operations `neg`, `abs`, `copysign` change only the sign bit,
  also on NaNs. `signBit` and `bits` observe the encoding.
* `ValEq` is equality at the value level: all NaNs are identified, `+0` and
  `-0` are identified, and otherwise values are equal only if identical.
-/
import Toy.FloatTier.Arith

namespace Toy.FloatTier

/-- Number of NaN payloads, `2^(p-2)`: the trailing significand of a NaN has
`p - 1` bits, one of which is the quiet bit. -/
def Fmt.payCount (f : Fmt) : Nat := 2 ^ (f.p - 2)

theorem Fmt.payCount_pos (f : Fmt) : 0 < f.payCount := Nat.two_pow_pos _

/-- Payload-carrying values of format `f`. `qnan s k`: quiet NaN with sign `s`
and payload `k`. `snan s k`: signaling NaN with sign `s` and payload `k + 1`
(a signaling NaN cannot have payload `0`). `inf s`, `fin s E M`: as in `FP f`.
Captures: the IEEE 754 binary interchange encodings of format `f`, one term per
bit pattern (`V.bits` is injective, `V.bits_injective`). -/
inductive V (f : Fmt) where
  | qnan (neg : Bool) (pay : Fin f.payCount)
  | snan (neg : Bool) (k : Fin (f.payCount - 1))
  | inf (neg : Bool)
  | fin (neg : Bool) (E : Fin f.expCount) (M : Fin f.fracCount)
  deriving DecidableEq, Repr

variable {f : Fmt}

namespace V

/-- NaN test (quiet or signaling). -/
def isNaN : V f → Bool
  | .qnan .. => true
  | .snan .. => true
  | _ => false

/-- Quiet bit: `true` for quiet NaNs, `false` for signaling NaNs and for
non-NaN values. -/
def isQuiet : V f → Bool
  | .qnan .. => true
  | _ => false

/-- Payload of a NaN (`k` for `qnan _ k`, `k + 1` for `snan _ k`); `0` for
non-NaN values. -/
def payload : V f → Nat
  | .qnan _ k => k.val
  | .snan _ k => k.val + 1
  | _ => 0

theorem payload_lt (x : V f) : x.payload < f.payCount := by
  cases x with
  | qnan _ k => exact k.isLt
  | snan _ k => have := k.isLt; simp only [payload]; omega
  | inf _ => exact f.payCount_pos
  | fin _ _ _ => exact f.payCount_pos

/-- Sign bit, for every value including NaNs. -/
def signBit : V f → Bool
  | .qnan s _ => s
  | .snan s _ => s
  | .inf s => s
  | .fin s _ _ => s

/-- The value with its sign bit replaced by `b` and every other bit kept. -/
def withSign (x : V f) (b : Bool) : V f :=
  match x with
  | .qnan _ k => .qnan b k
  | .snan _ k => .snan b k
  | .inf _ => .inf b
  | .fin _ E M => .fin b E M

/-- Bit-level negation (`fneg`, unary `-`): flips the sign bit only. -/
def neg (x : V f) : V f := x.withSign (!x.signBit)

/-- Bit-level absolute value (`fabs`): clears the sign bit only. -/
def abs (x : V f) : V f := x.withSign false

/-- Bit-level `copysign x y`: the bits of `x` with the sign bit of `y`. -/
def copysign (x y : V f) : V f := x.withSign y.signBit

/-- IEEE bit pattern: sign, biased exponent field, trailing significand field
(quiet bit, then payload, for NaNs). -/
def bits : V f → Nat
  | .qnan s k => (if s then 2 ^ (f.e + f.p - 1) else 0) + (2 ^ f.e - 1) * 2 ^ (f.p - 1)
      + 2 ^ (f.p - 2) + k.val
  | .snan s k => (if s then 2 ^ (f.e + f.p - 1) else 0) + (2 ^ f.e - 1) * 2 ^ (f.p - 1)
      + (k.val + 1)
  | .inf s => (if s then 2 ^ (f.e + f.p - 1) else 0) + (2 ^ f.e - 1) * 2 ^ (f.p - 1)
  | .fin s E M => (if s then 2 ^ (f.e + f.p - 1) else 0) + E.val * 2 ^ (f.p - 1) + M.val

/-- The NaN-collapsed view: every NaN becomes the single NaN of `FP f`. -/
def toFP : V f → FP f
  | .qnan .. => .nan
  | .snan .. => .nan
  | .inf s => .inf s
  | .fin s E M => .fin s E M

/-- Embedding of NaN-collapsed values; the NaN of `FP f` becomes the positive
preferred quiet NaN. Used only on non-NaN results. -/
def ofFP : FP f → V f
  | .nan => .qnan false ⟨0, f.payCount_pos⟩
  | .inf s => .inf s
  | .fin s E M => .fin s E M

/-- `±0`. -/
def isZero (x : V f) : Bool := x.toFP.isZero

/-- NaN or `±0`: the values whose value-level class (`ValEq`) contains more than
one bit pattern. -/
def isNaNOrZero (x : V f) : Bool := x.isNaN || x.isZero

/-- Preferred quiet NaN with sign `s` (quiet bit set, payload `0`). -/
def prefNaN (f : Fmt) (s : Bool) : V f := .qnan s ⟨0, f.payCount_pos⟩

/-- The quiet NaN with sign `s` and the payload of `z` ("quieting
propagation" of `z`). -/
def quieted (s : Bool) (z : V f) : V f := .qnan s ⟨z.payload, z.payload_lt⟩

/-- Signed zero. -/
def zero (f : Fmt) (s : Bool) : V f := .fin s ⟨0, f.expCount_pos⟩ ⟨0, f.fracCount_pos⟩

end V

/-- Equality at the value level: equality of the NaN-collapsed views up to the
sign of zero (`EqNsz`). It identifies all NaNs with each other and `+0` with
`-0`, and nothing else. Captures: what IEEE comparisons, NaN tests and
arithmetic (without division) can distinguish. -/
def ValEq (x y : V f) : Prop := EqNsz x.toFP y.toFP

instance (x y : V f) : Decidable (ValEq x y) := inferInstanceAs (Decidable (EqNsz _ _))

/-- Sign replacement on the NaN-collapsed view (NaN stays NaN). -/
def FP.setSign (x : FP f) (b : Bool) : FP f :=
  match x with
  | .nan => .nan
  | .inf _ => .inf b
  | .fin _ E M => .fin b E M

end Toy.FloatTier
