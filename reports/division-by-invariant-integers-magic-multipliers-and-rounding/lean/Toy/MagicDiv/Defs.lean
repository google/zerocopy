/-
Toy.MagicDiv.Defs
=================

Definitions for a toy theory of integer division by an invariant (constant)
divisor via multiplication by a "magic" multiplier followed by right shifts.

Model.
* Unsigned `N`-bit values are natural numbers `x < 2^N`; the reference
  quotient is Lean's floor division `x / d` on `Nat`, and the reference
  remainder is `x % d`.
* Signed `N`-bit values are integers `x` with `-2^N ≤ 2 * x < 2^N`
  (`SignedRange`); for `N ≥ 1` this is `-2^(N-1) ≤ x < 2^(N-1)`, and for
  `N = 0` it is `{0}`, matching core `BitVec N`. The reference quotient is
  `Int.tdiv x d` (rounding toward zero) and the reference remainder is
  `Int.tmod x d`.
* Right shift of a natural number is core `Nat.shiftRight` (`>>>`), i.e.
  floor division by a power of two. Arithmetic right shift of an integer is
  core `Int.shiftRight` (`>>>` on `Int`), i.e. floor division by a power of
  two (rounding toward negative infinity). Both are total: a shift by any
  count, including counts at or above a word width, is defined. Machine shift
  instructions and C, C++, Rust or LLVM IR shifts are not total in this way;
  where a result depends on a shift count at or above the word width, its
  statement or card says so.
* Multiplication is exact (unbounded); a machine "multiply-high" is modelled
  by multiplying exactly and then shifting. No statement in this file says
  anything about word-size overflow unless it says so explicitly.
-/

namespace Toy.MagicDiv

/-- Ceiling division on naturals: `ceilDiv a d = ⌈a / d⌉` for `d ≥ 1`.
(For `d = 0` it is `0`, by Lean's `x / 0 = 0` convention.) -/
def ceilDiv (a d : Nat) : Nat := (a + d - 1) / d

/-- Ceiling base-2 logarithm: for `d ≥ 1`, `clog2 d` is the least `ℓ` with
`d ≤ 2^ℓ`. By convention `clog2 0 = 0`. -/
def clog2 (d : Nat) : Nat := if d ≤ 1 then 0 else Nat.log2 (d - 1) + 1

/-- `MulShiftCorrect N d m s`: the multiply-shift `(x * m) >>> s` equals the
unsigned floor quotient `x / d` for every `N`-bit unsigned input `x < 2^N`.
This is the correctness property of replacing `x / d` by a multiplication by
the constant `m` followed by a right shift by `s` (the shift `s` is the total
shift, i.e. the width of the discarded low part of the product). -/
def MulShiftCorrect (N d m s : Nat) : Prop :=
  ∀ x, x < 2 ^ N → (x * m) >>> s = x / d

instance (N d m s : Nat) : Decidable (MulShiftCorrect N d m s) :=
  inferInstanceAs (Decidable (∀ x, x < 2 ^ N → (x * m) >>> s = x / d))

/-- `lastFullBlockEnd N d = 2^N - 2^N % d - 1`: for `1 ≤ d ≤ 2^N`, the largest
`x < 2^N` with `x % d = d - 1`, i.e. the last input that ends a complete run of
`d` consecutive inputs sharing one quotient value. This is the critical input
of the exact criterion (`ExactCriterion`). -/
def lastFullBlockEnd (N d : Nat) : Nat := 2 ^ N - 2 ^ N % d - 1

/-- Exact criterion for a multiply-shift on `N`-bit inputs: the lower bound
`2^s ≤ m * d` and the upper bound `nc * (m * d - 2^s) < 2^s`, where
`nc = lastFullBlockEnd N d`. For `1 ≤ d < 2^N` it is equivalent to
`MulShiftCorrect N d m s` (`mulShiftCorrect_iff_exactCriterion`). -/
def ExactCriterion (N d m s : Nat) : Prop :=
  2 ^ s ≤ m * d ∧ lastFullBlockEnd N d * (m * d - 2 ^ s) < 2 ^ s

instance (N d m s : Nat) : Decidable (ExactCriterion N d m s) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The unsigned multiplier at shift `N + clog2 d`: `⌈2^(N + clog2 d) / d⌉`.
This is the multiplier of the textbook construction that always works but
may need `N + 1` bits. -/
def unsignedMagic (N d : Nat) : Nat := ceilDiv (2 ^ (N + clog2 d)) d

/-- The candidate shift for a single-word (`N`-bit) multiplier:
`N + clog2 d - 1` (one less than the shift of `unsignedMagic`; natural-number
subtraction, so it is `0` when `N + clog2 d = 0`). -/
def singleWordShift (N d : Nat) : Nat := N + clog2 d - 1

/-- The candidate single-word multiplier `⌈2^(singleWordShift N d) / d⌉`. -/
def singleWordMagic (N d : Nat) : Nat := ceilDiv (2 ^ singleWordShift N d) d

/-- The add-and-shift fixup sequence used when the multiplier `2^N + m'`
needs `N + 1` bits: only the low part `m'` is multiplied,
`t = (x * m') >>> N` (the high half of the `2N`-bit product, a multiply-high),
and the quotient is `q = (t + ((x - t) >>> 1)) >>> (ℓ - 1)`.
On an `N`-bit machine, when `x < 2^N` and `m' < 2^N`, the multiply-high output
`t` and every later intermediate (`x - t`, `(x - t) >>> 1`, their sum, and the
result) stay below `2^N`; the averaging step `t + (x - t)/2` replaces the
overflowing sum `x + t`. The product `x * m'` itself is a `2N`-bit value.
Subtraction here is truncated `Nat` subtraction. -/
def fixupQuot (N m' ℓ x : Nat) : Nat :=
  let t := (x * m') >>> N
  (t + ((x - t) >>> 1)) >>> (ℓ - 1)

/-- Signed `N`-bit range: `-2^N ≤ 2 * x < 2^N`. For `N ≥ 1` this is
`-2^(N-1) ≤ x < 2^(N-1)` (`signedRange_iff_of_pos`); for `N = 0` it is `{0}`.
It holds exactly when `x` is the signed value of an `N`-bit two's-complement
bit vector (`signedRange_iff_toInt_ofInt`). -/
def SignedRange (N : Nat) (x : Int) : Prop :=
  -(2 : Int) ^ N ≤ 2 * x ∧ 2 * x < (2 : Int) ^ N

instance (N : Nat) (x : Int) : Decidable (SignedRange N x) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Signed multiply-shift quotient with the negative-dividend correction, in
exact integer arithmetic: `((x * m) >>> k) + (if x < 0 then 1 else 0)`, where
`>>>` on `Int` is the arithmetic (flooring) right shift and `x * m` is the
exact product of `x` with the nonnegative multiplier `m`. This is the value
that the Granlund–Montgomery signed sequence computes; it is not a model of
its machine encoding. On an `N`-bit machine the product is formed with a
signed multiply-high (`MULSH`, which divides by `2^N` and reads the multiplier
as a signed `N`-bit value), so a multiplier `m ≥ 2^(N-1)` is encoded as
`m - 2^N` with `x` added back, and the remaining post-shift is `k - N`; none
of that encoding is modelled here. -/
def sdivMagic (m k : Nat) (x : Int) : Int :=
  ((x * (m : Int)) >>> k) + (if x < 0 then 1 else 0)

/-- The same sequence without the negative-dividend correction:
`(x * m) >>> k` (arithmetic shift). -/
def sdivMagicUncorrected (m k : Nat) (x : Int) : Int :=
  (x * (m : Int)) >>> k

/-- Signed remainder from the corrected multiply-shift quotient:
`x - d * sdivMagic m k x`. -/
def sremMagic (d m k : Nat) (x : Int) : Int := x - (d : Int) * sdivMagic m k x

/-- The signed multiplier for a positive divisor at shift `(N - 1) + clog2 d`:
`⌊2^((N - 1) + clog2 d) / d⌋ + 1` (the choice of Granlund and Montgomery,
which makes `m * d` strictly exceed the power of two; they use
`ℓ = max(clog2 d, 1)`, which differs only at `d = 1`). -/
def signedMagic (N d : Nat) : Nat := 2 ^ (N - 1 + clog2 d) / d + 1

/-- Logical right shift by `s` of the `N`-bit two's-complement bit pattern of
`y` (the pattern is `y mod 2^N`, read as an unsigned number). Total: for
`s ≥ N` the result is `0`. -/
def lsrN (N : Nat) (y : Int) (s : Nat) : Int :=
  (((y % (2 : Int) ^ N).toNat >>> s : Nat) : Int)

/-- The biased dividend of the power-of-two signed division sequence:
`x + ((x >>> (N - 1)) >>>ₗ (N - k))`, where the first shift is arithmetic
(producing `-1` or `0` for in-range `x`) and the second is the logical shift
`lsrN N` of the resulting `N`-bit mask (producing `2^k - 1` or `0`). The sum is
computed exactly (no wrap-around); see `biasDiv_eq_tdiv_of_lt` for the
no-overflow claim. At `k = 0` the logical shift count is `N - 0 = N`, the full
width; `lsrN` returns `0` there only because it is total. -/
def biasSum (N k : Nat) (x : Int) : Int :=
  x + lsrN N (x >>> (N - 1)) (N - k)

/-- Power-of-two signed division by bias-and-shift:
`(x + ((x >>> (N - 1)) >>>ₗ (N - k))) >>> k` (arithmetic final shift). -/
def biasDiv (N k : Nat) (x : Int) : Int := biasSum N k x >>> k

/-- The biased dividend with every shift count reduced modulo `N`, as by
shift instructions that use only the count modulo the operand width:
`x + ((x >>> ((N - 1) % N)) >>>ₗ ((N - k) % N))` (exact sum). -/
def biasSumMasked (N k : Nat) (x : Int) : Int :=
  x + lsrN N (x >>> ((N - 1) % N)) ((N - k) % N)

/-- Bias-and-shift with every shift count reduced modulo `N`:
`biasSumMasked N k x >>> (k % N)`. -/
def biasDivMasked (N k : Nat) (x : Int) : Int := biasSumMasked N k x >>> (k % N)

/-- The same bias-and-shift sequence on core `BitVec N` with wrapping
addition: `(x + ((x.sshiftRight (N - 1)) >>> (N - k))).sshiftRight k`.
Core `BitVec` shifts are total (a logical shift by `≥ N` gives `0`). -/
def biasDivBV {N : Nat} (k : Nat) (x : BitVec N) : BitVec N :=
  (x + ((x.sshiftRight (N - 1)) >>> (N - k))).sshiftRight k

/-- `biasDivBV` with every shift count reduced modulo `N` (wrapping addition):
`(x + ((x.sshiftRight ((N - 1) % N)) >>> ((N - k) % N))).sshiftRight (k % N)`. -/
def biasDivBVMasked {N : Nat} (k : Nat) (x : BitVec N) : BitVec N :=
  (x + ((x.sshiftRight ((N - 1) % N)) >>> ((N - k) % N))).sshiftRight (k % N)

/-- Direct remainder computation (no quotient): keep the low `F` bits of
`x * m`, multiply by `d`, and keep the high part:
`(((x * m) % 2^F) * d) >>> F`. -/
def directRem (F d m x : Nat) : Nat := (((x * m) % 2 ^ F) * d) >>> F

end Toy.MagicDiv
