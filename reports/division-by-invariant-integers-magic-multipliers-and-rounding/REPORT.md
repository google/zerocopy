# Division by invariant integers in Lean 4: magic multipliers, the add-and-shift fixup, and signed rounding

## Summary

This package formalizes, in core Lean 4 without Mathlib, the integer arithmetic behind replacing division of an `N`-bit integer by a constant `d` with a multiplication by a "magic" constant followed by right shifts. It covers sufficient and exact criteria for unsigned (multiplier, shift) pairs, the textbook multiplier and its size, a characterization of when a single-word (`N`-bit) multiplier exists, the add-and-shift fixup used for `(N+1)`-bit multipliers, signed division rounding toward zero and its single overflow case, signed division by a power of two with bias-and-shift (with Lean's total shifts and with shift counts reduced modulo the width), and remainders. The model is a toy model: exact (unbounded) products, `Nat`/`Int` reference division, and Lean's total shifts. These are statements about the toy model; they neither establish nor refute the corresponding claims about any compiler, language or instruction set (proved model–system relation: none proved).

All 20 results are kernel-checked (Lean kernel; no axioms beyond `propext`, `Classical.choice` and `Quot.sound`). Most hold for every width `N`. Results 7 and 17 are stated for one width: result 17 is a kernel evaluation (`decide +kernel`) of all 256 inputs in each stated case, and result 7 combines kernel evaluations of finitely many cases with proved lemmas that extend them to every shift and every multiplier (each card's *Bounded check* gives the details). They neither establish nor refute the corresponding claims for other widths or divisors.

Notation for the sentences below: `l` stands for `ℓ`; `>>>` is a right shift (on `Nat` and `Int`, floor division by a power of two; on `BitVec`, the logical shift); `/` and `mod` are floor division and remainder on natural numbers, with `x / 0 = 0` and `x mod 0 = x`; `ceil(a/d)` is `ceilDiv a d = (a + d - 1) / d`, which is 0 at `d = 0`; `clog2 d` is ⌈log₂ d⌉ for `d ≥ 1` and 0 at `d = 0`; `Int.tdiv`/`Int.tmod` round toward zero. Natural-number `-` is truncated subtraction (`a - b = 0` when `a ≤ b`). The formulas are stated for every `N`, including `N = 0`, with these conventions: at `N = 0`, `N - 1 = 0` (so `(N-1) + l = l`), the unsigned inputs `x < 2^0` are just `x = 0`, and the signed range is `{0}`; `N + clog2 d - 1 = 0` when `N = 0` and `d ≤ 1`; where a statement assumes `k < N`, `N ≥ 1`, so `N - 1` and `N - k` are not truncated.

One sentence per result (hypotheses first):

1. **mulShiftCorrect_of_sandwich** — For all N, l, d, m with 2^(N+l) <= m*d <= 2^(N+l) + 2^l: (x*m) >>> (N+l) = x / d (floor division) for every unsigned N-bit input x < 2^N.
2. **unsignedMagic_sandwich** — For every N and every d >= 1, the multiplier m = unsignedMagic N d = ceil(2^(N + clog2 d)/d), with l = clog2 d = ceil(log2 d), satisfies 2^(N+l) <= m*d <= 2^(N+l) + 2^l.
3. **unsignedMagic_bounds** — For every N (N = 0 included) and every d: (a) if d >= 1, then 2^N <= unsignedMagic N d, so the textbook multiplier at shift N + clog2 d does not fit in N bits (is not below 2^N); (b) if d <= 2^(N+1) (d = 0 included), then unsignedMagic N d < 2^(N+1), so it fits in N + 1 bits; (c) if 1 <= d <= 2^(N+1), then unsignedMagic N d = 2^N + m' with m' = unsignedMagic N d - 2^N < 2^N, so its low part fits in N bits.
4. **single_word_multiplier_exists_iff** — For every N and every d (no hypotheses): some multiplier m < 2^N with some shift s satisfies (x*m) >>> s = x / d for all x < 2^N if and only if the candidate m* = singleWordMagic N d = ceil(2^(N + clog2 d - 1)/d) satisfies it at shift s* = singleWordShift N d = N + clog2 d - 1 (truncated subtraction: s* = 0 when N = 0 and d <= 1). Moreover, if N >= 1 and d <= 2^N, then m* < 2^N.
5. **fixupQuot_eq_wide** — For l >= 1 and m' <= 2^N, the add-and-shift sequence fixupQuot N m' l x = (t + ((x - t) >>> 1)) >>> (l - 1) with t = (x*m') >>> N equals (x*(2^N + m')) >>> (N + l) for every natural number x. Consequently, if moreover (x*(2^N + m')) >>> (N + l) = x / d for every x < 2^N, then fixupQuot N m' l x = x / d for every x < 2^N.
6. **fixupQuot_unsignedMagic_correct** — For every N and every d >= 2 (no upper bound on d), the add-and-shift sequence with m' = unsignedMagic N d - 2^N and l = clog2 d computes x / d for every x < 2^N.
7. **no_single_word_multiplier_u8_div7** — For N = 8 and d = 7: for every multiplier m < 2^8 and every shift s (unbounded), (x*m) >>> s = x / 7 fails for some x < 2^8; and for every shift s <= 10 and every multiplier m (unbounded) it fails, while (m, s) = (293, 11) is correct for all x < 2^8.
8. **mulShiftCorrect_iff_exactCriterion** — (a) For 1 <= d < 2^N and every m, s: (x*m) >>> s = x / d for all x < 2^N if and only if 2^s <= m*d and nc*(m*d - 2^s) < 2^s, where nc = lastFullBlockEnd N d = 2^N - (2^N mod d) - 1. (b) For 2^N <= d and every m, s: it holds if and only if (2^N - 1)*m < 2^s.
9. **exists_mulShiftCorrect_iff_ceilDiv** — For 1 <= d < 2^N and every shift s: some multiplier m satisfies (x*m) >>> s = x / d for all x < 2^N if and only if the ceiling multiplier ceil(2^s/d) does.
10. **mulShiftCorrect_ceilDiv_succ** — For every N, d and s: if the ceiling multiplier ceil(2^s/d) is correct at shift s for all x < 2^N, then the ceiling multiplier ceil(2^(s+1)/d) is correct at shift s + 1.
11. **sdivMagic_eq_tdiv_of_sandwich** — For all N, l, d, m (d, m natural numbers; N - 1 is truncated subtraction, so (N-1)+l = l at N = 0) with 2^((N-1)+l) < m*d <= 2^((N-1)+l) + 2^l: for every signed N-bit x (-2^N <= 2x < 2^N), ((x*m) >>> ((N-1)+l)) + (1 if x < 0 else 0) = Int.tdiv x d, with the exact integer product and the flooring arithmetic shift.
12. **sdivMagicUncorrected_eq_tdiv_sub_one_of_neg** — For all N, l and natural numbers d, m (N - 1 is truncated subtraction, so (N-1)+l = l at N = 0), under the same bounds 2^((N-1)+l) < m*d <= 2^((N-1)+l) + 2^l, for every signed N-bit x with x < 0, omitting the negative-dividend correction gives (x*m) >>> ((N-1)+l) = Int.tdiv x d - 1.
13. **tdiv_signedRange_iff** — For every N, every signed N-bit x (-2^N <= 2x < 2^N; for N = 0 this is x = 0) and every integer d: Int.tdiv x d is again a signed N-bit value if and only if not (x = -2^(N-1) and d = -1), where N - 1 is truncated subtraction (at N = 0 the excluded case reads x = -1, which the signed 0-bit range {0} does not contain).
14. **signedMagic_sandwich** — For every N and every d >= 1 (N - 1 is truncated subtraction, so (N-1) + clog2 d = clog2 d at N = 0), signedMagic N d = floor(2^((N-1) + clog2 d)/d) + 1 satisfies 2^((N-1)+l) < m*d <= 2^((N-1)+l) + 2^l with l = clog2 d (so sdivMagic_eq_tdiv_of_sandwich applies).
15. **int_shiftRight_eq_tdiv_iff** — For every integer x and every k (no hypotheses): the arithmetic shift x >>> k equals Int.tdiv x (2^k) if and only if x >= 0 or 2^k divides x.
16. **biasDiv_eq_tdiv_of_lt** — (a) With Lean's total shifts (a logical shift of an N-bit pattern by N or more gives 0): for every k < N (so N >= 1, and N - 1 and N - k involve no truncation) and every signed N-bit x, the biased dividend x + ((x >>> (N-1)) >>>_logical (N-k)) stays in the signed N-bit range and biasDiv N k x = Int.tdiv x (2^k); at k = 0 this relies on the logical shift by the full width N returning 0. (b) With every shift count reduced modulo N (as by instructions that reduce the count modulo the operand width): for every 1 <= k < N and every signed N-bit x, the same two conclusions hold for biasSumMasked and biasDivMasked (what fails at k = 0 is listed under the non-claims).
17. **biasDivBV_u8** — On core BitVec 8 with wrapping addition: (a) with BitVec's total shifts, for every k < 8 and every x, (biasDivBV k x).toInt = Int.tdiv x.toInt (2^k), and for every k <= 6, biasDivBV k x = BitVec.sdiv x (BitVec.ofNat 8 (2^k)); at k = 0 this relies on the logical shift by 8 returning 0. (b) With all three shift counts reduced modulo 8, (biasDivBVMasked k x).toInt = Int.tdiv x.toInt (2^k) for every 1 <= k < 8 and every x.
18. **mulShift_rem_eq_mod_of_correct** — For all N, d, m, s: if (x*m) >>> s = x / d for every x < 2^N, then x - d*((x*m) >>> s) = x mod d for every x < 2^N (in particular under the sandwich bounds: mulShift_rem_eq_mod_of_sandwich).
19. **sremMagic_eq_tmod_and_sign** — For all N, l and natural numbers d, m (N - 1 is truncated subtraction, so (N-1)+l = l at N = 0), under 2^((N-1)+l) < m*d <= 2^((N-1)+l) + 2^l, for every signed N-bit x: x - d*sdivMagic m ((N-1)+l) x = Int.tmod x d; it lies in [0, d) when x >= 0 and in (-d, 0] when x < 0.
20. **directRem_eq_mod_of_sandwich** — For all N, l, d, m with 2^(N+l) <= m*d <= 2^(N+l) + 2^l: the remainder can be computed without the quotient, (((x*m) mod 2^(N+l)) * d) >>> (N+l) = x mod d, for every x < 2^N (no d < 2^N hypothesis).

Each result's non-claims (what it does not show) are listed first under **Boundaries**; the hypothesis ledgers with tightness counterexamples are under **Findings**.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

## Applicability

### Model fidelity

This is a **toy model**, stated over core Lean types in namespace `Toy.MagicDiv`. It is meant to capture the arithmetic of the division-by-constant lowerings described by Granlund and Montgomery (1994), Warren (*Hacker's Delight*, chapter 10), and Lemire, Kaser and Kurz (2019) / Lemire, Bartlett and Kaser (2021), as used by optimizing compilers. It is not a model of any compiler, language, or instruction set:

- **Unsigned** `N`-bit values are natural numbers `x < 2^N`; the reference quotient and remainder are `Nat` floor division `x / d` and `x % d` (with Lean's convention `x / 0 = 0`).
- **Signed** `N`-bit values are integers with `-2^N ≤ 2x < 2^N` (`SignedRange`), i.e. `-2^(N-1) ≤ x < 2^(N-1)` for `N ≥ 1` and `{0}` for `N = 0`; the reference quotient and remainder are `Int.tdiv` and `Int.tmod` (rounding toward zero).
- **Products are exact** (unbounded). A machine multiply-high is modelled as an exact multiplication followed by a shift. The model does not represent the `2N`-bit product register, the `MULUH`/`MULSH` instruction encodings, or overflow of intermediate values, except where a statement says so: the no-overflow conjuncts of result 16 and the wrapping `BitVec 8` sequences of result 17.
- **Shifts are Lean's total shifts.** `>>>` on `Nat` is floor division by a power of two, on `Int` the flooring arithmetic shift, on `BitVec` the logical shift; a shift by any count, including counts at or above a word width, is defined (a logical shift of an `N`-bit pattern by `N` or more gives 0). Shift instructions and C, C++, Rust and LLVM IR shifts are not total in this way (Findings, *Modeling bridge*, item 4). Where a statement depends on a shift count at or above the width (result 6 for `2^N < d ≤ 2^(N+1)`, part (a) of results 16 and 17 at `k = 0`) the card says so, and `biasSumMasked`/`biasDivMasked`/`biasDivBVMasked` model shifts whose count is reduced modulo the width.
- **Known gaps** (not modelled): the `N`-bit intermediates of the add-and-shift fixup, the signed multiply-high encoding `m - 2^N` with the dividend added back, pre-shifting of even divisors, multiply-add forms beyond one 8-bit instance, floor-rounding signed division, exact division by modular inverses, and language-level behavior of `x / (-1)` and `x % (-1)` at `x = -2^(N-1)`.

The proved model–system relation is `none proved`: no embedding, abstraction or simulation between these definitions and any compiler, language or instruction set is proved, so the theorems neither establish nor refute the corresponding claims about such systems. Any statement connecting a theorem to a real compiler or instruction set is a separate claim with basis `derived (modeling bridge)` (Findings, *Modeling bridge*); "proved" in this report never means "true of a real system".

### Scope of the results

- **Every width `N`:** results 1–6 and 8–16, 18–20 hold for every `N` (including `N = 0` unless a hypothesis excludes it) and for the stated ranges of divisors, multipliers and shifts.
- **One width:** result 7 is stated for `N = 8`, `d = 7`, and result 17 for `BitVec 8`; they neither establish nor refute the corresponding claims for other widths or divisors. The supporting instances `fixupQuot_unsignedMagic_u8`, `fixupQuot_unsignedMagic_u16_div7`, `mulShiftCorrect_iff_exactCriterion_u8`, and the counts `count_no_single_word_u8` (55), `count_single_word_u8` (200) and `count_single_word_u8_directRem_fails` (42) are kernel evaluations over the finite ranges stated with them (`N = 8`, divisors `1 ≤ d ≤ 255`, or `N = 16`, `d = 7`). The counts are stated over the Boolean checkers `correctB` and `directRemB`, which `correctB_iff` and `directRemB_iff` identify with `MulShiftCorrect` and with correctness of `directRem` (Findings, *Supporting declarations*).

### Toolchain and dependencies

Lean `leanprover/lean4:v4.34.1` (core library; **no Mathlib**, no other dependency). The Lake project in `lean/` (package `magic_div`, `lakefile.toml` with one `[[lean_lib]]` named `Toy`) has the modules `Toy.MagicDiv.Defs`, `Lemmas`, `Examples`, `Statements`, `Bounded`, `Counterexamples`, `Witnesses`, `Companions` (two companion lemmas on which no other declaration depends). `lean/Audit.lean` is an axiom audit outside the library target.

### Subjects and how they relate

`REPORT.json` lists the Lean toolchain release that checked every proof; the three papers whose results are restated (Granlund–Montgomery 1994; Lemire–Kaser–Kurz 2019; Lemire–Bartlett–Kaser 2021); and three source repositories at fixed commits whose code is cited for prior art or inspected for the modeling bridge (LLVM, CompCert, and the *Hacker's Delight* companion code). These theorems are statements about the Lean definitions in `Toy.MagicDiv`; they neither establish nor refute the corresponding claims about any compiler, language or instruction set, or about the code in those repositories (proved model–system relation: none proved). The papers and repositories are compared with them, not modelled by them.

### Notation

`>>>` on `Nat` is `Nat.shiftRight`; on `Int` it is `Int.shiftRight`. In Lean, `>>>` binds tighter than `*`, `/`, `%`, which bind tighter than `+`, `-` (the opposite of C, C++, Rust, Java, Python and Go for shifts), so the renderings below parenthesize shifts. Natural-number `-` truncates at 0. In ASCII card text, `l` stands for `ℓ`, `<=`/`>=` for `≤`/`≥`, and `ceil`, `floor`, `log2` have their usual meanings.

## Findings

All Lean names below are in namespace `Toy.MagicDiv`; source paths are relative to the package directory. Every statement block is a verbatim quote of the Lean source at the cited lines (proofs omitted). Every unfolded rendering is a Lean term with the package definitions expanded; it re-elaborates in the theorem's namespace (with `autoImplicit` off) and is definitionally equal to the quoted statement.

### Results at a glance

| # | Result | Kind | Tier | Depth | Lean declarations |
|---|---|---|---|---|---|
| 1 | `mulShiftCorrect_of_sandwich` | theorem | T0 | substantive | `mulShiftCorrect_of_sandwich` |
| 2 | `unsignedMagic_sandwich` | theorem | T0 | shallow | `unsignedMagic_sandwich` |
| 3 | `unsignedMagic_bounds` | theorem | T2 | shallow | `unsignedMagic_ge_two_pow_of_pos`, `unsignedMagic_lt_two_pow_succ_of_le`, `unsignedMagic_eq_two_pow_add_low` |
| 4 | `single_word_multiplier_exists_iff` | characterization | T1 | substantive | `single_word_multiplier_exists_iff`, `singleWordMagic_lt_two_pow` |
| 5 | `fixupQuot_eq_wide` | theorem | T0 | shallow | `fixupQuot_eq_wide`, `fixupQuot_correct` |
| 6 | `fixupQuot_unsignedMagic_correct` | theorem | T0 | shallow | `fixupQuot_unsignedMagic_correct` |
| 7 | `no_single_word_multiplier_u8_div7` | impossibility | T0 | shallow | `no_single_word_multiplier_u8_div7`, `minimal_shift_u8_div7` |
| 8 | `mulShiftCorrect_iff_exactCriterion` | characterization | T0 | substantive | `mulShiftCorrect_iff_exactCriterion`, `mulShiftCorrect_iff_of_two_pow_le` |
| 9 | `exists_mulShiftCorrect_iff_ceilDiv` | characterization | T0 | shallow | `exists_mulShiftCorrect_iff_ceilDiv` |
| 10 | `mulShiftCorrect_ceilDiv_succ` | theorem | T1 | shallow | `mulShiftCorrect_ceilDiv_succ` |
| 11 | `sdivMagic_eq_tdiv_of_sandwich` | theorem | T0 | substantive | `sdivMagic_eq_tdiv_of_sandwich` |
| 12 | `sdivMagicUncorrected_eq_tdiv_sub_one_of_neg` | theorem | T0 | shallow | `sdivMagicUncorrected_eq_tdiv_sub_one_of_neg` |
| 13 | `tdiv_signedRange_iff` | characterization | T0 | shallow | `tdiv_signedRange_iff` |
| 14 | `signedMagic_sandwich` | theorem | T0 | shallow | `signedMagic_sandwich` |
| 15 | `int_shiftRight_eq_tdiv_iff` | characterization | T0 | shallow | `int_shiftRight_eq_tdiv_iff` |
| 16 | `biasDiv_eq_tdiv_of_lt` | theorem | T0 | shallow | `biasDiv_eq_tdiv_of_lt`, `biasDivMasked_eq_tdiv_of_pos_of_lt` |
| 17 | `biasDivBV_u8` | theorem | T0 | shallow | `biasDivBV_u8`, `biasDivBVMasked_u8` |
| 18 | `mulShift_rem_eq_mod_of_correct` | theorem | T0 | shallow | `mulShift_rem_eq_mod_of_correct` |
| 19 | `sremMagic_eq_tmod_and_sign` | theorem | T0 | shallow | `sremMagic_eq_tmod_and_sign` |
| 20 | `directRem_eq_mod_of_sandwich` | theorem | T0 | substantive | `directRem_eq_mod_of_sandwich` |

Grouping: unsigned sufficient criterion and existence (1–3); single-word multipliers and the fixup (4–7); exact characterization and minimal shift (8–10); signed division (11–14); power-of-two signed division (15–17); remainders (18–20).

### Core definitions

Each definition is quoted verbatim. Its intended positive examples (instances it must admit) and negative examples (instances it must reject) are proved in `lean/Toy/MagicDiv/Examples.lean` (by kernel evaluation).

#### `ceilDiv`

```lean
-- lean/Toy/MagicDiv/Defs.lean:34
def ceilDiv (a d : Nat) : Nat := (a + d - 1) / d
```

- Captures: ⌈a/d⌉ for d ≥ 1 (0 for d = 0).
- Positive examples: `ceilDiv_pos_examples`. Negative examples: `ceilDiv_neg_example`.

#### `clog2`

```lean
-- lean/Toy/MagicDiv/Defs.lean:38
def clog2 (d : Nat) : Nat := if d ≤ 1 then 0 else Nat.log2 (d - 1) + 1
```

- Captures: ⌈log₂ d⌉ for d ≥ 1: the least ℓ with d ≤ 2^ℓ (0 for d = 0 and d = 1). It is meant to agree with Mathlib's `Nat.clog 2` (not proved here; Mathlib is not used).
- Positive examples: `clog2_pos_examples`. Negative examples: `clog2_neg_examples`.

#### `MulShiftCorrect`

```lean
-- lean/Toy/MagicDiv/Defs.lean:45-46
def MulShiftCorrect (N d m s : Nat) : Prop :=
  ∀ x, x < 2 ^ N → (x * m) >>> s = x / d
```

- Captures: Correctness of replacing unsigned N-bit `x / d` by multiply-by-`m` then shift-right-by-`s` (`s` is the total shift).
- Positive examples: `mulShiftCorrect_pos_examples`. Negative examples: `mulShiftCorrect_neg_examples`.

#### `lastFullBlockEnd`

```lean
-- lean/Toy/MagicDiv/Defs.lean:55
def lastFullBlockEnd (N d : Nat) : Nat := 2 ^ N - 2 ^ N % d - 1
```

- Captures: For 1 ≤ d ≤ 2^N, the largest x < 2^N with x mod d = d − 1 (the critical input `nc`).
- Positive examples: `lastFullBlockEnd_pos_example`. Negative examples: `lastFullBlockEnd_neg_example`.

#### `ExactCriterion`

```lean
-- lean/Toy/MagicDiv/Defs.lean:61-62
def ExactCriterion (N d m s : Nat) : Prop :=
  2 ^ s ≤ m * d ∧ lastFullBlockEnd N d * (m * d - 2 ^ s) < 2 ^ s
```

- Captures: The closed-form condition equivalent to `MulShiftCorrect` for 1 ≤ d < 2^N (result 8).
- Positive examples: `exactCriterion_pos_examples`. Negative examples: `exactCriterion_neg_examples`.

#### `unsignedMagic`

```lean
-- lean/Toy/MagicDiv/Defs.lean:70
def unsignedMagic (N d : Nat) : Nat := ceilDiv (2 ^ (N + clog2 d)) d
```

- Captures: The textbook multiplier at shift N + ⌈log₂ d⌉. For 1 ≤ d ≤ 2^(N+1) it lies in [2^N, 2^(N+1)) (result 3); it is 0 at d = 0 (`unsignedMagic_zero_right`).
- Positive examples: `magic_pos_examples`. Negative examples: `magic_neg_examples`.

#### `singleWordShift / singleWordMagic`

```lean
-- lean/Toy/MagicDiv/Defs.lean:75
def singleWordShift (N d : Nat) : Nat := N + clog2 d - 1
-- lean/Toy/MagicDiv/Defs.lean:78
def singleWordMagic (N d : Nat) : Nat := ceilDiv (2 ^ singleWordShift N d) d
```

- Captures: The candidate shift N + ⌈log₂ d⌉ − 1 (truncated subtraction) and the ceiling multiplier at that shift, for an N-bit (single-word) multiply-shift.
- Positive examples: `magic_pos_examples`. Negative examples: `magic_neg_examples`, `singleWordShift_neg_example`.

#### `fixupQuot`

```lean
-- lean/Toy/MagicDiv/Defs.lean:89-91
def fixupQuot (N m' ℓ x : Nat) : Nat :=
  let t := (x * m') >>> N
  (t + ((x - t) >>> 1)) >>> (ℓ - 1)
```

- Captures: The add-and-shift sequence for a multiplier 2^N + m'. The multiply-high t = (x·m') >>> N is the high half of a 2N-bit product; natural-number `-` truncates.
- Positive examples: `fixupQuot_pos_examples`. Negative examples: `fixupQuot_neg_example`.

#### `SignedRange`

```lean
-- lean/Toy/MagicDiv/Defs.lean:97-98
def SignedRange (N : Nat) (x : Int) : Prop :=
  -(2 : Int) ^ N ≤ 2 * x ∧ 2 * x < (2 : Int) ^ N
```

- Captures: Signed N-bit two's-complement range: −2^(N−1) ≤ x < 2^(N−1) for N ≥ 1 (`signedRange_iff_of_pos`) and {0} for N = 0 (`signedRange_zero_iff`); exactly the integers x with `(BitVec.ofInt N x).toInt = x` (`signedRange_iff_toInt_ofInt`).
- Positive examples: `signedRange_pos_examples`, `signedRange_zero_examples`. Negative examples: `signedRange_neg_examples`, `signedRange_zero_examples`.

#### `sdivMagic / sdivMagicUncorrected`

```lean
-- lean/Toy/MagicDiv/Defs.lean:113-114
def sdivMagic (m k : Nat) (x : Int) : Int :=
  ((x * (m : Int)) >>> k) + (if x < 0 then 1 else 0)
-- lean/Toy/MagicDiv/Defs.lean:118-119
def sdivMagicUncorrected (m k : Nat) (x : Int) : Int :=
  (x * (m : Int)) >>> k
```

- Captures: Exact signed product and flooring arithmetic shift, with and without adding 1 for a negative dividend: the value of the Granlund–Montgomery signed sequence, not its MULSH encoding.
- Positive examples: `sdivMagic_pos_examples`, `sdivMagicUncorrected_pos_examples`. Negative examples: `sdivMagic_neg_examples`.

#### `sremMagic`

```lean
-- lean/Toy/MagicDiv/Defs.lean:123
def sremMagic (d m k : Nat) (x : Int) : Int := x - (d : Int) * sdivMagic m k x
```

- Captures: Signed remainder from the corrected quotient.
- Positive examples: `sremMagic_pos_examples`. Negative examples: `sremMagic_neg_example`.

#### `signedMagic`

```lean
-- lean/Toy/MagicDiv/Defs.lean:129
def signedMagic (N d : Nat) : Nat := 2 ^ (N - 1 + clog2 d) / d + 1
```

- Captures: Granlund–Montgomery's signed multiplier ⌊2^k/d⌋ + 1 with k = (N − 1) + ⌈log₂ d⌉.
- Positive examples: `signedMagic_pos_examples`. Negative examples: `signedMagic_neg_example`.

#### `lsrN`

```lean
-- lean/Toy/MagicDiv/Defs.lean:134-135
def lsrN (N : Nat) (y : Int) (s : Nat) : Int :=
  (((y % (2 : Int) ^ N).toNat >>> s : Nat) : Int)
```

- Captures: Logical right shift of the N-bit two's-complement pattern of y; total (0 for s ≥ N).
- Positive examples: `lsrN_pos_examples`. Negative examples: `lsrN_neg_example`.

#### `biasSum / biasDiv`

```lean
-- lean/Toy/MagicDiv/Defs.lean:144-145
def biasSum (N k : Nat) (x : Int) : Int :=
  x + lsrN N (x >>> (N - 1)) (N - k)
-- lean/Toy/MagicDiv/Defs.lean:149
def biasDiv (N k : Nat) (x : Int) : Int := biasSum N k x >>> k
```

- Captures: Power-of-two signed division by adding the bias 2^k − 1 to negative dividends (exact sum, total shifts; at k = 0 the logical shift count is N).
- Positive examples: `biasDiv_pos_examples`. Negative examples: `biasDiv_neg_example`, `biasSum_neg_example`.

#### `biasSumMasked / biasDivMasked`

```lean
-- lean/Toy/MagicDiv/Defs.lean:154-155
def biasSumMasked (N k : Nat) (x : Int) : Int :=
  x + lsrN N (x >>> ((N - 1) % N)) ((N - k) % N)
-- lean/Toy/MagicDiv/Defs.lean:159
def biasDivMasked (N k : Nat) (x : Int) : Int := biasSumMasked N k x >>> (k % N)
```

- Captures: The same sequence with every shift count reduced modulo N, as by shift instructions that reduce the count modulo the operand width.
- Positive examples: `biasDivMasked_pos_examples`. Negative examples: `biasDivMasked_neg_examples`.

#### `biasDivBV / biasDivBVMasked`

```lean
-- lean/Toy/MagicDiv/Defs.lean:164-165
def biasDivBV {N : Nat} (k : Nat) (x : BitVec N) : BitVec N :=
  (x + ((x.sshiftRight (N - 1)) >>> (N - k))).sshiftRight k
-- lean/Toy/MagicDiv/Defs.lean:169-170
def biasDivBVMasked {N : Nat} (k : Nat) (x : BitVec N) : BitVec N :=
  (x + ((x.sshiftRight ((N - 1) % N)) >>> ((N - k) % N))).sshiftRight (k % N)
```

- Captures: The same sequences on core `BitVec N` with wrapping addition (total shifts / counts reduced modulo N).
- Positive examples: `biasDivBV_pos_example`, `biasDivMasked_pos_examples`. Negative examples: `biasDivBV_neg_example`, `biasDivMasked_neg_examples`.

#### `directRem`

```lean
-- lean/Toy/MagicDiv/Defs.lean:175
def directRem (F d m x : Nat) : Nat := (((x * m) % 2 ^ F) * d) >>> F
```

- Captures: Remainder without the quotient: the low F bits of x·m, times d, high part.
- Positive examples: `directRem_pos_example`. Negative examples: `directRem_neg_example`.

### 1. `mulShiftCorrect_of_sandwich`

**Kind:** theorem. **Tier:** T0: Granlund-Montgomery Theorem 4.2, already mechanized in Coq (CompCert Zdiv_mul_pos); restated without the redundant d != 0 hypothesis. **Depth:** substantive.

Basis: execution (Lean kernel check)

**Lean statement.**

```lean
-- lean/Toy/MagicDiv/Statements.lean:27-29
theorem mulShiftCorrect_of_sandwich (N ℓ d m : Nat)
    (hlo : 2 ^ (N + ℓ) ≤ m * d) (hhi : m * d ≤ 2 ^ (N + ℓ) + 2 ^ ℓ) :
    MulShiftCorrect N d m (N + ℓ) := by
```

Unfolded rendering of `mulShiftCorrect_of_sandwich` (a Lean term that elaborates in the statement's context and is definitionally equal to it):

```lean
∀ (N ℓ d m : Nat), 2 ^ (N + ℓ) ≤ m * d → m * d ≤ 2 ^ (N + ℓ) + 2 ^ ℓ →
  ∀ x : Nat, x < 2 ^ N → (x * m) >>> (N + ℓ) = x / d
```

**Plain claim.** For all N, l, d, m with 2^(N+l) <= m*d <= 2^(N+l) + 2^l: (x*m) >>> (N+l) = x / d (floor division) for every unsigned N-bit input x < 2^N. No separate d >= 1 hypothesis is needed because the lower bound forces it.

**Hypothesis ledger.**

- `hlo: 2^(N+l) <= m*d` — The approximation m/2^(N+l) of 1/d must not undershoot (otherwise the result is 0 at x = d); it also forces d >= 1 (pos_of_two_pow_le_mul). *Tightness:* tight; counterexample `ce_sandwich_hlo`; witness class: an instance with N = 1, l = 0, d = 1, m = 1 (fails at x = 1).
- `hhi: m*d <= 2^(N+l) + 2^l` — Bounds the overshoot e = m*d - 2^(N+l) by 2^l so that x*e < 2^(N+l) for all x < 2^N. *Tightness:* tight; counterexample `ce_sandwich_hhi`; witness class: an instance with N = 8, l = 2, d = 7, m = 147 (fails at x = 209).
- `input range x < 2^N (inside MulShiftCorrect)` — The overshoot grows with x; the first out-of-range input can already fail. *Tightness:* tight; counterexample `ce_sandwich_input_range`; witness class: an instance with N = 1, l = 0, d = 3, m = 1 (fails at x = 2).

**Non-vacuity witness.** N = 32, l = 3, d = 7, m = ceil(2^35/7) = 4908534053 (m*7 - 2^35 = 3 <= 2^3), x = 200 < 2^32. (`nv_sandwich_u32_div7`, which proves that all hypotheses hold for this instance.)

**Non-claims.** Listed under Boundaries, *Non-claims of result 1*.

**Prior art.**

- Torbjörn Granlund and Peter L. Montgomery, 'Division by Invariant Integers using Multiplication', Proceedings of the ACM SIGPLAN 1994 Conference on Programming Language Design and Implementation (PLDI '94), pp. 61-72, 1994, DOI 10.1145/178243.178249 (also printed in SIGPLAN Notices 29(6):61-72, DOI 10.1145/773473.178249). Theorem 4.2: if d != 0 and 2^(N+l) <= m*d <= 2^(N+l) + 2^l then floor(n/d) = floor(m*n/2^(N+l)) for every integer 0 <= n < 2^N.
- CompCert, repository AbsInt/CompCert, commit 5e4ef44c57b22cdc2e1893770843fd693a5f82e1, file backend/SelectDivproof.v: Lemma Zdiv_mul_pos (Coq proof over Z of Granlund-Montgomery Theorem 4.2, with d > 0); file backend/SelectDiv.vp: divu_mul_params requires 0 <= m < Int.modulus (2^32) in addition to 2^(32+p) <= m*d <= 2^(32+p) + 2^p, so it rejects multipliers of 2^32 or more and the add-and-shift fixup is not used there.
- Daniel Lemire, Owen Kaser, Nathan Kurz, 'Faster Remainder by Direct Computation: Applications to Compilers and Software Libraries', Software: Practice and Experience 49(6):953-970, 2019, DOI 10.1002/spe.2689; arXiv:1902.01961v3. Algorithm 1 (Granlund-Montgomery-Warren, d in [1, 2^N)): line 4 handles powers of two; line 6, for d not a power of two, uses L = floor(log2 d) (which equals ceil(log2 d) - 1 for such d, whereas floor(log2 d) = ceil(log2 d) when d is a power of two) and c = ceil(2^(N+L)/d) and tests c*(2^N - (2^N mod d) - 1) < (2^N div d)*2^(N+L) (then c < 2^N); line 9 pre-shifts even d; line 12 uses L = ceil(log2 d), c = ceil(2^(N+L)/d) > 2^N, c = 2^N + c', and the add-and-shift quotient.
- D. J. Magenheimer, L. Peters, K. W. Pettis, D. Zuras, 'Integer Multiplication and Division on the HP Precision Architecture', IEEE Transactions on Computers 37(8):980-990, 1988, DOI 10.1109/12.2248. Granlund and Montgomery cite the earlier ASPLOS II version (SIGPLAN Notices 22(10):90-99, 1987, DOI 10.1145/36205.36189) as giving the foundation of the general reciprocal approach (content not consulted here).
- R. Alverson, 'Integer Division Using Reciprocals', Proceedings of the 10th IEEE Symposium on Computer Arithmetic (ARITH-10), pp. 186-190, 1991, DOI 10.1109/ARITH.1991.145558. Integer division by multiplication with a reciprocal whose multiplier is computed in floating point (as described by Granlund and Montgomery, Sections 1 and 7; content not consulted here).
- D. Cavagnino and A. E. Werbrouck, 'Efficient Algorithms for Integer Division by Constants Using Multiplication', The Computer Journal 51(4):470-480 (published online 2007), DOI 10.1093/comjnl/bxm082. Cited by Lemire, Bartlett and Kaser as refining Granlund and Montgomery's choice of multiplier and shift, and by Lemire, Kaser and Kurz as the basis of Warren's observation that Granlund and Montgomery choose a slightly suboptimal number of fractional bits for some divisors (content not consulted here).
- Source records, with verbatim quotations where this card relies on a stated theorem or rule: [GM94-T4.2], [CompCert], [LKK19-A1], [GM94-S1], [MPPZ], [Alverson91], [CW] (Evidence, *Primary sources*).

**Design question.** Which (multiplier, shift) pairs are guaranteed to compute unsigned N-bit floor division by a constant d?

### 2. `unsignedMagic_sandwich`

**Kind:** theorem. **Tier:** T0: the choice l = ceil(log2 d) of Granlund-Montgomery Figure 4.1 (with the ceiling instead of floor + 1) and of Lemire-Kaser-Kurz Algorithm 1. **Depth:** shallow.

Basis: execution (Lean kernel check)

**Lean statement.**

```lean
-- lean/Toy/MagicDiv/Statements.lean:54-56
theorem unsignedMagic_sandwich (N d : Nat) (hd : 0 < d) :
    2 ^ (N + clog2 d) ≤ unsignedMagic N d * d ∧
      unsignedMagic N d * d ≤ 2 ^ (N + clog2 d) + 2 ^ clog2 d := by
```

Unfolded rendering of `unsignedMagic_sandwich` (a Lean term that elaborates in the statement's context and is definitionally equal to it):

```lean
∀ (N d : Nat), 0 < d →
  let ℓ : Nat := if d ≤ 1 then 0 else Nat.log2 (d - 1) + 1;
  let m : Nat := (2 ^ (N + ℓ) + d - 1) / d;
  2 ^ (N + ℓ) ≤ m * d ∧ m * d ≤ 2 ^ (N + ℓ) + 2 ^ ℓ
```

**Plain claim.** For every N and every d >= 1, the multiplier m = unsignedMagic N d = ceil(2^(N + clog2 d)/d), with l = clog2 d = ceil(log2 d), satisfies 2^(N+l) <= m*d <= 2^(N+l) + 2^l (so, by mulShiftCorrect_of_sandwich, it is correct for all N-bit inputs at shift N + clog2 d).

**Hypothesis ledger.**

- `hd: 0 < d` — For d = 0 the ceiling multiplier is 0 and the lower bound 2^(N+l) <= 0 fails. *Tightness:* tight; counterexample `ce_unsignedMagic_sandwich_d_zero`; witness class: an instance with N = 0, d = 0.

**Non-vacuity witness.** N = 32, d = 7: unsignedMagic 32 7 = 2^32 + 613566757. (`nv_unsignedMagic_sandwich_div7`, which proves that all hypotheses hold for this instance.)

**Non-claims.** Listed under Boundaries, *Non-claims of result 2*.

**Prior art.**

- Torbjörn Granlund and Peter L. Montgomery, 'Division by Invariant Integers using Multiplication', Proceedings of the ACM SIGPLAN 1994 Conference on Programming Language Design and Implementation (PLDI '94), pp. 61-72, 1994, DOI 10.1145/178243.178249 (also printed in SIGPLAN Notices 29(6):61-72, DOI 10.1145/773473.178249). Figure 4.1 (for 1 <= d < 2^N): l = ceil(log2 d), m' = floor(2^N*(2^l - d)/d) + 1, sh1 = min(l, 1), sh2 = max(l - 1, 0), t1 = MULUH(m', n), q = SRL(t1 + SRL(n - t1, sh1), sh2); the explanation sets m = m' + 2^N = floor(2^(N+l)/d) + 1 and checks Theorem 4.2's hypothesis.
- Daniel Lemire, Owen Kaser, Nathan Kurz, 'Faster Remainder by Direct Computation: Applications to Compilers and Software Libraries', Software: Practice and Experience 49(6):953-970, 2019, DOI 10.1002/spe.2689; arXiv:1902.01961v3. Algorithm 1 (Granlund-Montgomery-Warren, d in [1, 2^N)): line 4 handles powers of two; line 6, for d not a power of two, uses L = floor(log2 d) (which equals ceil(log2 d) - 1 for such d, whereas floor(log2 d) = ceil(log2 d) when d is a power of two) and c = ceil(2^(N+L)/d) and tests c*(2^N - (2^N mod d) - 1) < (2^N div d)*2^(N+L) (then c < 2^N); line 9 pre-shifts even d; line 12 uses L = ceil(log2 d), c = ceil(2^(N+L)/d) > 2^N, c = 2^N + c', and the add-and-shift quotient.
- Henry S. Warren, Jr., Hacker's Delight, 2nd edition, Addison-Wesley, 2012 (electronic ISBN 9780133084993), Chapter 10 'Integer Division By Constants', sections 10-8 'Unsigned Division', 10-9 'Unsigned Division by Divisors >= 1' and 10-10 'Incorporation into a Compiler (Unsigned)' (section titles from the publisher's table of contents; the book text was not consulted).
- Source records, with verbatim quotations where this card relies on a stated theorem or rule: [GM94-F4.1], [LKK19-A1], [HD] (Evidence, *Primary sources*).

**Design question.** Does a correct (multiplier, shift) pair exist for every divisor d >= 1, and which one does the textbook construction pick?

### 3. `unsignedMagic_bounds`

**Kind:** theorem. **Tier:** T2: the textbook size bounds (Granlund-Montgomery Section 4: the low part fits in N bits for 1 <= d < 2^N; Figure 6.2 corollary) restated for the ceiling multiplier with the tight divisor bound d <= 2^(N+1) and tightness counterexamples. **Depth:** shallow.

Basis: execution (Lean kernel check)

**Lean statements.**

```lean
-- lean/Toy/MagicDiv/Statements.lean:65-66
theorem unsignedMagic_ge_two_pow_of_pos (N d : Nat) (hd : 0 < d) :
    2 ^ N ≤ unsignedMagic N d := by
```

Unfolded rendering of `unsignedMagic_ge_two_pow_of_pos` (a Lean term that elaborates in the statement's context and is definitionally equal to it):

```lean
∀ (N d : Nat), 0 < d → 2 ^ N ≤ (2 ^ (N + clog2 d) + d - 1) / d
```

```lean
-- lean/Toy/MagicDiv/Statements.lean:84-85
theorem unsignedMagic_lt_two_pow_succ_of_le (N d : Nat) (hd : d ≤ 2 ^ (N + 1)) :
    unsignedMagic N d < 2 ^ (N + 1) := by
```

Unfolded rendering of `unsignedMagic_lt_two_pow_succ_of_le` (a Lean term that elaborates in the statement's context and is definitionally equal to it):

```lean
∀ (N d : Nat), d ≤ 2 ^ (N + 1) → (2 ^ (N + clog2 d) + d - 1) / d < 2 ^ (N + 1)
```

```lean
-- lean/Toy/MagicDiv/Statements.lean:823-825
theorem unsignedMagic_eq_two_pow_add_low (N d : Nat) (hd0 : 0 < d) (hd : d ≤ 2 ^ (N + 1)) :
    unsignedMagic N d = 2 ^ N + (unsignedMagic N d - 2 ^ N) ∧
      unsignedMagic N d - 2 ^ N < 2 ^ N := by
```

Unfolded rendering of `unsignedMagic_eq_two_pow_add_low` (a Lean term that elaborates in the statement's context and is definitionally equal to it):

```lean
∀ (N d : Nat), 0 < d → d ≤ 2 ^ (N + 1) →
  let u : Nat := (2 ^ (N + clog2 d) + d - 1) / d;
  u = 2 ^ N + (u - 2 ^ N) ∧ u - 2 ^ N < 2 ^ N
```

**Plain claim.** For every N (N = 0 included) and every d: (a) if d >= 1, then 2^N <= unsignedMagic N d, so the textbook multiplier at shift N + clog2 d does not fit in N bits (is not below 2^N); (b) if d <= 2^(N+1) (d = 0 included), then unsignedMagic N d < 2^(N+1), so it fits in N + 1 bits; (c) if 1 <= d <= 2^(N+1), then unsignedMagic N d = 2^N + m' with m' = unsignedMagic N d - 2^N < 2^N, so its low part fits in N bits.

**Hypothesis ledger.**

- `hd0: 0 < d (parts a and c)` — For d = 0 the multiplier is 0 for every N (unsignedMagic_zero_right): it is below 2^N, and 0 is not 2^N + (0 - 2^N) = 2^N. *Tightness:* tight; counterexample `ce_unsignedMagic_ge_two_pow_d_zero`, `ce_unsignedMagic_low_d_zero`; witness class: instances with d = 0 (N = 8 for part a, N = 0 for part c).
- `hd: d <= 2^(N+1) (parts b and c)` — For larger d the multiplier can reach 2^(N+1) (N = 0, d = 3 gives 2), and then the low part 2^N is not below 2^N. At every N, d = 2^(N+1) + 1 gives exactly 2^(N+1) (unsignedMagic_two_pow_succ_add_one). The hypothesis is sufficient, not necessary, for both parts: every power of two above 2^(N+1) gives exactly 2^N (unsignedMagic_two_pow; for part b, unsignedMagic_lt_two_pow_succ_converse_fails), which satisfies both conclusions. *Tightness:* tight; counterexample `ce_unsignedMagic_lt_two_pow_succ`, `ce_unsignedMagic_low_hd`; witness class: an instance with N = 0, d = 3.

**Non-vacuity witness.** N = 32, d = 7 (0 < 7 <= 2^33). (`nv_unsignedMagic_bounds`, which proves that all hypotheses hold for this instance.)

**Non-claims.** Listed under Boundaries, *Non-claims of result 3*.

**Prior art.**

- Torbjörn Granlund and Peter L. Montgomery, 'Division by Invariant Integers using Multiplication', Proceedings of the ACM SIGPLAN 1994 Conference on Programming Language Design and Implementation (PLDI '94), pp. 61-72, 1994, DOI 10.1145/178243.178249 (also printed in SIGPLAN Notices 29(6):61-72, DOI 10.1145/773473.178249). Figure 4.1 (for 1 <= d < 2^N): l = ceil(log2 d), m' = floor(2^N*(2^l - d)/d) + 1, sh1 = min(l, 1), sh2 = max(l - 1, 0), t1 = MULUH(m', n), q = SRL(t1 + SRL(n - t1, sh1), sh2); the explanation sets m = m' + 2^N = floor(2^(N+l)/d) + 1 and checks Theorem 4.2's hypothesis.
- Torbjörn Granlund and Peter L. Montgomery, 'Division by Invariant Integers using Multiplication', Proceedings of the ACM SIGPLAN 1994 Conference on Programming Language Design and Implementation (PLDI '94), pp. 61-72, 1994, DOI 10.1145/178243.178249 (also printed in SIGPLAN Notices 29(6):61-72, DOI 10.1145/773473.178249). Figure 6.2 (CHOOSE_MULTIPLIER, 1 <= d < 2^N) and its corollary: 'If d <= 2^prec, then m < 2^(N+shpost) * (1 + 2^(1-l))/d <= 2^(N+shpost-l+1). Hence m fits in max(prec, N - l) + 1 bits (unsigned).'
- Daniel Lemire, Owen Kaser, Nathan Kurz, 'Faster Remainder by Direct Computation: Applications to Compilers and Software Libraries', Software: Practice and Experience 49(6):953-970, 2019, DOI 10.1002/spe.2689; arXiv:1902.01961v3. Algorithm 1 (Granlund-Montgomery-Warren, d in [1, 2^N)): line 4 handles powers of two; line 6, for d not a power of two, uses L = floor(log2 d) (which equals ceil(log2 d) - 1 for such d, whereas floor(log2 d) = ceil(log2 d) when d is a power of two) and c = ceil(2^(N+L)/d) and tests c*(2^N - (2^N mod d) - 1) < (2^N div d)*2^(N+L) (then c < 2^N); line 9 pre-shifts even d; line 12 uses L = ceil(log2 d), c = ceil(2^(N+L)/d) > 2^N, c = 2^N + c', and the add-and-shift quotient. Line 12 asserts c > 2^N in a branch that line 4 has already restricted to divisors that are not powers of two (for d = 2^K, c = 2^N).
- Source records, with verbatim quotations where this card relies on a stated theorem or rule: [GM94-F4.1], [GM94-F6.2], [LKK19-A1] (Evidence, *Primary sources*).

**Design question.** How many bits does the textbook multiplier need, and when does its low part fit in an N-bit register?

### 4. `single_word_multiplier_exists_iff`

**Kind:** characterization. **Tier:** T1: Lemire-Kaser-Kurz Algorithm 1 (line 6) tests exactly this candidate and LLVM's IsAdd records the same distinction; the equivalence with 'some N-bit multiplier at some shift' over all multipliers and shifts is not stated as a theorem in the sources consulted. **Depth:** substantive.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — That LLVM's `IsAdd` flag marks divisors whose single-word candidate fails, and that a signed multiply-high misreads `m*` as negative, are statements about real code and instructions from source inspection (Modeling bridge, items 1 and 3); neither is proved here.

**Lean statements.**

```lean
-- lean/Toy/MagicDiv/Statements.lean:294-296
theorem single_word_multiplier_exists_iff (N d : Nat) :
    (∃ m s, m < 2 ^ N ∧ MulShiftCorrect N d m s) ↔
      MulShiftCorrect N d (singleWordMagic N d) (singleWordShift N d) := by
```

Unfolded rendering of `single_word_multiplier_exists_iff` (a Lean term that elaborates in the statement's context and is definitionally equal to it):

```lean
∀ (N d : Nat),
  let sw : Nat := N + clog2 d - 1;
  let mw : Nat := (2 ^ sw + d - 1) / d;
  (∃ m s : Nat, m < 2 ^ N ∧ ∀ x : Nat, x < 2 ^ N → (x * m) >>> s = x / d) ↔
    ∀ x : Nat, x < 2 ^ N → (x * mw) >>> sw = x / d
```

```lean
-- lean/Toy/MagicDiv/Statements.lean:233-234
theorem singleWordMagic_lt_two_pow (N d : Nat) (hN : 1 ≤ N) (hdN : d ≤ 2 ^ N) :
    singleWordMagic N d < 2 ^ N := by
```

Unfolded rendering of `singleWordMagic_lt_two_pow` (a Lean term that elaborates in the statement's context and is definitionally equal to it):

```lean
∀ (N d : Nat), 1 ≤ N → d ≤ 2 ^ N → (2 ^ (N + clog2 d - 1) + d - 1) / d < 2 ^ N
```

**Plain claim.** For every N and every d (no hypotheses): some multiplier m < 2^N with some shift s satisfies (x*m) >>> s = x / d for all x < 2^N if and only if the candidate m* = singleWordMagic N d = ceil(2^(N + clog2 d - 1)/d) satisfies it at shift s* = singleWordShift N d = N + clog2 d - 1 (truncated subtraction: s* = 0 when N = 0 and d <= 1). Moreover, if N >= 1 and d <= 2^N, then m* < 2^N.

**Hypothesis ledger.**

- `hN: 1 <= N (hypothesis of singleWordMagic_lt_two_pow, not of single_word_multiplier_exists_iff)` — At N = 0 the candidate for d = 1 is 1, not below 2^0. *Tightness:* tight; counterexample `ce_single_word_hN`; witness class: an instance with N = 0, d = 1.
- `hdN: d <= 2^N (hypothesis of singleWordMagic_lt_two_pow, not of single_word_multiplier_exists_iff)` — For N = 1, d = 3 the candidate is 2, not below 2^1. *Tightness:* tight; counterexample `ce_single_word_hdN`; witness class: an instance with N = 1, d = 3.

**Non-vacuity witness.** N = 8, d = 7 (1 <= 8, 7 <= 2^8): the right-hand side is false (no_single_word_multiplier_u8_div7); N = 8, d = 3: it is true (pc_single_word_shift_fits). The equivalence itself has no hypotheses. (`nv_single_word_u8_div7`, which proves that all hypotheses hold for this instance.)

**Non-claims.** Listed under Boundaries, *Non-claims of result 4*.

**Prior art.**

- Daniel Lemire, Owen Kaser, Nathan Kurz, 'Faster Remainder by Direct Computation: Applications to Compilers and Software Libraries', Software: Practice and Experience 49(6):953-970, 2019, DOI 10.1002/spe.2689; arXiv:1902.01961v3. Algorithm 1 (Granlund-Montgomery-Warren, d in [1, 2^N)): line 4 handles powers of two; line 6, for d not a power of two, uses L = floor(log2 d) (which equals ceil(log2 d) - 1 for such d, whereas floor(log2 d) = ceil(log2 d) when d is a power of two) and c = ceil(2^(N+L)/d) and tests c*(2^N - (2^N mod d) - 1) < (2^N div d)*2^(N+L) (then c < 2^N); line 9 pre-shifts even d; line 12 uses L = ceil(log2 d), c = ceil(2^(N+L)/d) > 2^N, c = 2^N + c', and the add-and-shift quotient.
- Daniel Lemire, Colin Bartlett, Owen Kaser, 'Integer Division by Constants: Optimal Bounds', Heliyon 7(6):e07442, 2021, DOI 10.1016/j.heliyon.2021.e07442; arXiv:2012.12369v3. Section 6 ('Complementarity'), Proposition 3: for d > 0 not a power of two, N + 1 a power of two and m = 2^floor(log2 d)*(N + 1), either c = ceiling(m/d) gives floor(n/d) = floor(c*n/m) for all n in [0, N], or c = floor(m/d) gives floor(n/d) = floor((c*n + c)/m); footnote: 'This result is not novel', citing Robison.
- Arch D. Robison, 'N-Bit Unsigned Division via N-Bit Multiply-Add', 17th IEEE Symposium on Computer Arithmetic (ARITH-17), pp. 131-139, 2005, DOI 10.1109/ARITH.2005.31. The paper reduces any n-bit unsigned division to the upper n bits of an n-bit multiply-add followed by one shift, choosing between rounding the reciprocal up (multiply-shift) and down (multiply-add); its Theorem 8 shows the multiplier is below 2^n.
- Hacker's Delight companion code, repository hcs0/Hackers-Delight, commit 2bcb559da638a97f429c19889e6fd7d8601fd5d2, file magicu.c.txt: nc = -1 - (-d)%d (in 32-bit unsigned arithmetic, 2^32 - 1 - (2^32 mod d)) and the loop condition q1 < delta || (q1 == delta && r1 == 0) with delta = d - 1 - r2; file magicgu.py.txt: nc = ((nmax + 1)//d)*d - 1 and the test 2**p > nc*(d - 1 - (2**p - 1)%d).
- LLVM, repository llvm/llvm-project, commit c312bf3fa94430185410c06c502abd9953f838fa, file llvm/lib/Support/DivisionByConstantInfo.cpp: UnsignedDivisionByConstantInfo::get computes NC, 'the largest dividend such that NC.urem(D) == D-1', and increases the exponent P until the loop condition Q1 < Delta || (Q1 == Delta && R1 == 0) fails, i.e. until 2^P > NC*Delta with Delta = Magic*D - 2^P; it sets IsAdd when the magic number needs an extra bit and then lowers PostShift by one. Basis: source inspection; nothing here is a formal model of this code.
- Torbjörn Granlund and Peter L. Montgomery, 'Division by Invariant Integers using Multiplication', Proceedings of the ACM SIGPLAN 1994 Conference on Programming Language Design and Implementation (PLDI '94), pp. 61-72, 1994, DOI 10.1145/178243.178249 (also printed in SIGPLAN Notices 29(6):61-72, DOI 10.1145/773473.178249). Figure 4.2 and the examples after it: for 32-bit unsigned division by 7 the multiplier exceeds 2^32 and the add-and-shift sequence of Figure 4.1 is used; for even divisors a pre-shift can avoid it.
- Source records, with verbatim quotations where this card relies on a stated theorem or rule: [LKK19-A1], [LBK21-P3], [Robison05], [HD-code], [LLVM] (Evidence, *Primary sources*).

**Design question.** When does division of an N-bit integer by d admit a multiplier that fits in N bits, and which single candidate must be tested?

### 5. `fixupQuot_eq_wide`

**Kind:** theorem. **Tier:** T0: Granlund-Montgomery Figure 4.1 and equation (4.5). **Depth:** shallow.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — That every intermediate of `fixupQuot` stays below `2^N` for `x, m' < 2^N` (so the sequence runs in `N`-bit registers) is derived from the definitions by interval reasoning and is not proved here; the instruction-level reading follows Granlund–Montgomery Figure 4.1 and LLVM's `IsAdd` (Modeling bridge, item 2).

**Lean statements.**

```lean
-- lean/Toy/MagicDiv/Statements.lean:338-339
theorem fixupQuot_eq_wide (N m' ℓ x : Nat) (hℓ : 1 ≤ ℓ) (hm' : m' ≤ 2 ^ N) :
    fixupQuot N m' ℓ x = (x * (2 ^ N + m')) >>> (N + ℓ) := by
```

Unfolded rendering of `fixupQuot_eq_wide` (a Lean term that elaborates in the statement's context and is definitionally equal to it):

```lean
∀ (N m' ℓ x : Nat), 1 ≤ ℓ → m' ≤ 2 ^ N →
  (let t : Nat := (x * m') >>> N; (t + ((x - t) >>> 1)) >>> (ℓ - 1)) =
    (x * (2 ^ N + m')) >>> (N + ℓ)
```

```lean
-- lean/Toy/MagicDiv/Statements.lean:363-365
theorem fixupQuot_correct (N d m' ℓ : Nat) (hℓ : 1 ≤ ℓ) (hm' : m' ≤ 2 ^ N)
    (h : MulShiftCorrect N d (2 ^ N + m') (N + ℓ)) :
    ∀ x, x < 2 ^ N → fixupQuot N m' ℓ x = x / d := by
```

Unfolded rendering of `fixupQuot_correct` (a Lean term that elaborates in the statement's context and is definitionally equal to it):

```lean
∀ (N d m' ℓ : Nat), 1 ≤ ℓ → m' ≤ 2 ^ N →
  (∀ x : Nat, x < 2 ^ N → (x * (2 ^ N + m')) >>> (N + ℓ) = x / d) →
  ∀ x : Nat, x < 2 ^ N →
    (let t : Nat := (x * m') >>> N; (t + ((x - t) >>> 1)) >>> (ℓ - 1)) = x / d
```

**Plain claim.** For l >= 1 and m' <= 2^N, the add-and-shift sequence fixupQuot N m' l x = (t + ((x - t) >>> 1)) >>> (l - 1) with t = (x*m') >>> N equals (x*(2^N + m')) >>> (N + l) for every natural number x. Consequently, if moreover (x*(2^N + m')) >>> (N + l) = x / d for every x < 2^N, then fixupQuot N m' l x = x / d for every x < 2^N.

**Hypothesis ledger.**

- `hl: 1 <= l (both)` — At l = 0 the final shift l - 1 truncates to 0 and the halving step is not undone. *Tightness:* tight; counterexample `ce_fixupQuot_eq_wide_hl`, `ce_fixupQuot_correct_hl`; witness class: instances with N = 1, m' = 0, l = 0 (x = 1; for fixupQuot_correct d = 1).
- `hm': m' <= 2^N (both)` — Ensures t <= x, so x - t is exact and t + (x - t)/2 = (x + t)/2. *Tightness:* tight; counterexample `ce_fixupQuot_eq_wide_hm`, `ce_fixupQuot_correct_hm`; witness class: instances with m' > 2^N (N = 0, m' = 2, l = 1, x = 1; N = 1, d = 1, m' = 4, l = 1).
- `h: MulShiftCorrect N d (2^N + m') (N + l) (hypothesis of fixupQuot_correct, not of fixupQuot_eq_wide)` — The fixup equals the wide multiply-shift for every x (fixupQuot_eq_wide); it cannot repair a wrong multiplier. *Tightness:* tight; counterexample `ce_fixupQuot_correct_h`; witness class: an instance with N = 1, d = 1, m' = 0, l = 1.
- `input range x < 2^N (hypothesis of fixupQuot_correct, not of fixupQuot_eq_wide)` — Correctness of the wide multiply-shift is assumed for N-bit inputs x < 2^N; nothing is assumed about larger x. *Tightness:* tight; counterexample `ce_fixupQuot_correct_input_range`; witness class: an instance with N = 1, d = 3, m' = 1, l = 2 (fails at x = 8).

**Non-vacuity witness.** N = 8, d = 7, m' = 37 (multiplier 293), l = 3, x = 200. (`nv_fixupQuot_correct_u8_div7`, which proves that all hypotheses hold for this instance.)

**Non-claims.** Listed under Boundaries, *Non-claims of result 5*.

**Prior art.**

- Torbjörn Granlund and Peter L. Montgomery, 'Division by Invariant Integers using Multiplication', Proceedings of the ACM SIGPLAN 1994 Conference on Programming Language Design and Implementation (PLDI '94), pp. 61-72, 1994, DOI 10.1145/178243.178249 (also printed in SIGPLAN Notices 29(6):61-72, DOI 10.1145/773473.178249). Figure 4.1 (for 1 <= d < 2^N): l = ceil(log2 d), m' = floor(2^N*(2^l - d)/d) + 1, sh1 = min(l, 1), sh2 = max(l - 1, 0), t1 = MULUH(m', n), q = SRL(t1 + SRL(n - t1, sh1), sh2); the explanation sets m = m' + 2^N = floor(2^(N+l)/d) + 1 and checks Theorem 4.2's hypothesis. Equation (4.5) reduces q to floor((t1 + n)/2^l) using 0 <= t1 <= n.
- LLVM, repository llvm/llvm-project, commit c312bf3fa94430185410c06c502abd9953f838fa, file llvm/lib/Support/DivisionByConstantInfo.cpp: UnsignedDivisionByConstantInfo::get computes NC, 'the largest dividend such that NC.urem(D) == D-1', and increases the exponent P until the loop condition Q1 < Delta || (Q1 == Delta && R1 == 0) fails, i.e. until 2^P > NC*Delta with Delta = Magic*D - 2^P; it sets IsAdd when the magic number needs an extra bit and then lowers PostShift by one. Basis: source inspection; nothing here is a formal model of this code.
- CompCert, repository AbsInt/CompCert, commit 5e4ef44c57b22cdc2e1893770843fd693a5f82e1, file backend/SelectDivproof.v: Lemma Zdiv_mul_pos (Coq proof over Z of Granlund-Montgomery Theorem 4.2, with d > 0); file backend/SelectDiv.vp: divu_mul_params requires 0 <= m < Int.modulus (2^32) in addition to 2^(32+p) <= m*d <= 2^(32+p) + 2^p, so it rejects multipliers of 2^32 or more and the add-and-shift fixup is not used there.
- Source records, with verbatim quotations where this card relies on a stated theorem or rule: [GM94-F4.1], [LLVM], [CompCert] (Evidence, *Primary sources*).

**Design question.** How can a multiplier that needs N + 1 bits be applied with N-bit operations, and what does that sequence compute?

### 6. `fixupQuot_unsignedMagic_correct`

**Kind:** theorem. **Tier:** T0: Granlund-Montgomery Figure 4.1 with the ceiling multiplier; here without the d < 2^N restriction. **Depth:** shallow.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — The statement that a final shift count of `N` is undefined behavior in C and C++ when `N` is at least the width of the promoted left operand (but defined, for example, for a `uint8_t` operand, which is promoted to `int`), poison in LLVM IR at every width, an overflow in Rust at every width, and reduced modulo `N` by 32- and 64-bit register shifts on x86, AArch64 and RISC-V is a documentation claim (Modeling bridge, item 4); the theorem itself uses Lean's total shift.

**Lean statement.**

```lean
-- lean/Toy/MagicDiv/Statements.lean:372-373
theorem fixupQuot_unsignedMagic_correct (N d : Nat) (hd : 2 ≤ d) :
    ∀ x, x < 2 ^ N → fixupQuot N (unsignedMagic N d - 2 ^ N) (clog2 d) x = x / d := by
```

Unfolded rendering of `fixupQuot_unsignedMagic_correct` (a Lean term that elaborates in the statement's context and is definitionally equal to it):

```lean
∀ (N d : Nat), 2 ≤ d →
  let ℓ : Nat := clog2 d;
  let m' : Nat := (2 ^ (N + ℓ) + d - 1) / d - 2 ^ N;
  ∀ x : Nat, x < 2 ^ N →
    (let t : Nat := (x * m') >>> N; (t + ((x - t) >>> 1)) >>> (ℓ - 1)) = x / d
```

**Plain claim.** For every N and every d >= 2 (no upper bound on d), the add-and-shift sequence with m' = unsignedMagic N d - 2^N and l = clog2 d computes x / d for every x < 2^N.

**Hypothesis ledger.**

- `hd: 2 <= d` — At d = 1, l = clog2 1 = 0 and the fixup's halving is not undone. *Tightness:* tight; counterexample `ce_fixupQuot_unsignedMagic_d_one`; witness class: an instance with N = 1, d = 1 (fails at x = 1).
- `input range x < 2^N` — Correctness is stated for N-bit inputs x < 2^N; beyond them the sequence can fail. *Tightness:* tight; counterexample `ce_fixupQuot_unsignedMagic_input_range`; witness class: an instance with N = 0, d = 3 (fails at x = 2).

**Non-vacuity witness.** N = 8, d = 7, x = 200. (`nv_fixupQuot_unsignedMagic`, which proves that all hypotheses hold for this instance.)

**Non-claims.** Listed under Boundaries, *Non-claims of result 6*.

**Prior art.**

- Torbjörn Granlund and Peter L. Montgomery, 'Division by Invariant Integers using Multiplication', Proceedings of the ACM SIGPLAN 1994 Conference on Programming Language Design and Implementation (PLDI '94), pp. 61-72, 1994, DOI 10.1145/178243.178249 (also printed in SIGPLAN Notices 29(6):61-72, DOI 10.1145/773473.178249). Figure 4.1 (for 1 <= d < 2^N): l = ceil(log2 d), m' = floor(2^N*(2^l - d)/d) + 1, sh1 = min(l, 1), sh2 = max(l - 1, 0), t1 = MULUH(m', n), q = SRL(t1 + SRL(n - t1, sh1), sh2); the explanation sets m = m' + 2^N = floor(2^(N+l)/d) + 1 and checks Theorem 4.2's hypothesis.
- Daniel Lemire, Owen Kaser, Nathan Kurz, 'Faster Remainder by Direct Computation: Applications to Compilers and Software Libraries', Software: Practice and Experience 49(6):953-970, 2019, DOI 10.1002/spe.2689; arXiv:1902.01961v3. Algorithm 1 (Granlund-Montgomery-Warren, d in [1, 2^N)): line 4 handles powers of two; line 6, for d not a power of two, uses L = floor(log2 d) (which equals ceil(log2 d) - 1 for such d, whereas floor(log2 d) = ceil(log2 d) when d is a power of two) and c = ceil(2^(N+L)/d) and tests c*(2^N - (2^N mod d) - 1) < (2^N div d)*2^(N+L) (then c < 2^N); line 9 pre-shifts even d; line 12 uses L = ceil(log2 d), c = ceil(2^(N+L)/d) > 2^N, c = 2^N + c', and the add-and-shift quotient.
- Source records, with verbatim quotations where this card relies on a stated theorem or rule: [GM94-F4.1], [LKK19-A1] (Evidence, *Primary sources*).

**Design question.** Is the textbook (N+1)-bit multiplier always usable through the add-and-shift fixup, and for which divisors are all its shift counts below the word width?

### 7. `no_single_word_multiplier_u8_div7`

**Kind:** impossibility. **Tier:** T0: the example magicgu(255, 7) of the Hacker's Delight companion code, proved for all multipliers below 2^8 and all shifts. **Depth:** shallow.

Basis: execution (Lean kernel check)

**Bounded check.** Kernel-checked for N = 8 and d = 7. For `no_single_word_multiplier_u8_div7`, `decide +kernel` evaluates, for every m < 2^8 and every s < 16, that the multiply-shift is wrong at x = 7 or at x = 251; the proved lemma `not_mulShiftCorrect_of_mul_lt` covers every s >= 16 (there m*7 < 2^s, so x = 7 gives 0 instead of 1). For `minimal_shift_u8_div7`, `decide +kernel` evaluates two boundary inequalities for the ceiling multiplier ceil(2^s/7) at each s <= 10, and the proved lemmas `not_mulShiftCorrect_of_mul_lt` and `not_mulShiftCorrect_of_gt_at` extend them to every multiplier m; the pair (293, 11) is evaluated on all 256 inputs. These checks neither establish nor refute the corresponding claims for other N or d.

**Lean statements.**

```lean
-- lean/Toy/MagicDiv/Bounded.lean:236-237
theorem no_single_word_multiplier_u8_div7 :
    ∀ m, m < 2 ^ 8 → ∀ s, ¬ MulShiftCorrect 8 7 m s := by
```

Unfolded rendering of `no_single_word_multiplier_u8_div7` (a Lean term that elaborates in the statement's context and is definitionally equal to it):

```lean
∀ m : Nat, m < 2 ^ 8 → ∀ s : Nat,
  ¬ (∀ x : Nat, x < 2 ^ 8 → (x * m) >>> s = x / 7)
```

```lean
-- lean/Toy/MagicDiv/Bounded.lean:259-260
theorem minimal_shift_u8_div7 :
    (∀ s, s ≤ 10 → ∀ m, ¬ MulShiftCorrect 8 7 m s) ∧ MulShiftCorrect 8 7 293 11 := by
```

Unfolded rendering of `minimal_shift_u8_div7` (a Lean term that elaborates in the statement's context and is definitionally equal to it):

```lean
(∀ s : Nat, s ≤ 10 → ∀ m : Nat, ¬ (∀ x : Nat, x < 2 ^ 8 → (x * m) >>> s = x / 7)) ∧
  (∀ x : Nat, x < 2 ^ 8 → (x * 293) >>> 11 = x / 7)
```

**Plain claim.** For N = 8 and d = 7: for every multiplier m < 2^8 and every shift s (unbounded), (x*m) >>> s = x / 7 fails for some x < 2^8; and for every shift s <= 10 and every multiplier m (unbounded) it fails, while (m, s) = (293, 11) is correct for all x < 2^8.

**Hypothesis ledger.**

- `hm: m < 2^8 (no_single_word_multiplier_u8_div7)` — With a 9-bit multiplier the division is possible. *Tightness:* tight; counterexample `ce_no_single_word_u8_div7_m_bound`; witness class: an instance with m = 293 (correct at s = 11).
- `hs: s <= 10 (minimal_shift_u8_div7, first conjunct)` — At shift 11 the multiplier 293 is correct. *Tightness:* tight; counterexample `ce_minimal_shift_u8_div7_s_bound`; witness class: an instance with s = 11 (m = 293).
- `input range x < 2^8 (inside MulShiftCorrect 8 7 293 11, the second conjunct of minimal_shift_u8_div7)` — The second conjunct is a ground fact about the pair (293, 11) at shift s = 11, and its inner input range x < 2^8 is bounded: the pair computes x / 7 for every x < 685 and fails at x = 685 (ce_minimal_shift_u8_div7_input_range). *Tightness:* tight; counterexample `ce_minimal_shift_u8_div7_input_range`; witness class: an instance with x = 685 (for the pair (293, 11), which is correct for every x < 685).

**Non-vacuity witness.** m = 147 < 2^8; s = 10 <= 10. (`nv_no_single_word_u8_div7`, which proves that all hypotheses hold for this instance.)

**Positive control.** `pc_div7_u8_nine_bit_multiplier`: relaxing the multiplier bound to 9 bits, `(m, s) = (293, 11)` is correct for every `x < 2^8`.

**Non-claims.** Listed under Boundaries, *Non-claims of result 7*.

**Prior art.**

- Hacker's Delight companion code, repository hcs0/Hackers-Delight, commit 2bcb559da638a97f429c19889e6fd7d8601fd5d2, file magicgu.py.txt, lines 14-15: 'Example: magicgu(255, 7) is a 9-bit number, but magicgu(200, 7) is an 8-bit number.'
- Torbjörn Granlund and Peter L. Montgomery, 'Division by Invariant Integers using Multiplication', Proceedings of the ACM SIGPLAN 1994 Conference on Programming Language Design and Implementation (PLDI '94), pp. 61-72, 1994, DOI 10.1145/178243.178249 (also printed in SIGPLAN Notices 29(6):61-72, DOI 10.1145/773473.178249). Figure 4.2 and the examples after it: for 32-bit unsigned division by 7 the multiplier exceeds 2^32 and the add-and-shift sequence of Figure 4.1 is used; for even divisors a pre-shift can avoid it.
- Arch D. Robison, 'N-Bit Unsigned Division via N-Bit Multiply-Add', 17th IEEE Symposium on Computer Arithmetic (ARITH-17), pp. 131-139, 2005, DOI 10.1109/ARITH.2005.31. The paper reduces any n-bit unsigned division to the upper n bits of an n-bit multiply-add followed by one shift, choosing between rounding the reciprocal up (multiply-shift) and down (multiply-add); its Theorem 8 shows the multiplier is below 2^n.
- Source records, with verbatim quotations where this card relies on a stated theorem or rule: [HD-code], [Robison05] (Evidence, *Primary sources*).

**Design question.** Is there a concrete divisor for which no N-bit multiplier works at any shift, so that the fixup or another form is unavoidable?

### 8. `mulShiftCorrect_iff_exactCriterion`

**Kind:** characterization. **Tier:** T0: Lemire-Bartlett-Kaser Theorem 1 specialized to power-of-two denominators (part a), and the zero-quotient regime 2^N <= d (part b), which that theorem excludes. **Depth:** substantive.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — That LLVM's unsigned magic-number search stops at the first shift satisfying the upper half of `ExactCriterion` for the ceiling multiplier is a source-inspection claim (Modeling bridge, item 1); it is not proved here.

**Lean statements.**

```lean
-- lean/Toy/MagicDiv/Statements.lean:389-391
theorem mulShiftCorrect_iff_exactCriterion (N d m s : Nat) (hd : 0 < d)
    (hdN : d < 2 ^ N) :
    MulShiftCorrect N d m s ↔ ExactCriterion N d m s := by
```

Unfolded rendering of `mulShiftCorrect_iff_exactCriterion` (a Lean term that elaborates in the statement's context and is definitionally equal to it):

```lean
∀ (N d m s : Nat), 0 < d → d < 2 ^ N →
  let nc : Nat := 2 ^ N - 2 ^ N % d - 1;
  ((∀ x : Nat, x < 2 ^ N → (x * m) >>> s = x / d) ↔
    (2 ^ s ≤ m * d ∧ nc * (m * d - 2 ^ s) < 2 ^ s))
```

```lean
-- lean/Toy/MagicDiv/Statements.lean:213-214
theorem mulShiftCorrect_iff_of_two_pow_le (N d m s : Nat) (hdN : 2 ^ N ≤ d) :
    MulShiftCorrect N d m s ↔ (2 ^ N - 1) * m < 2 ^ s := by
```

Unfolded rendering of `mulShiftCorrect_iff_of_two_pow_le` (a Lean term that elaborates in the statement's context and is definitionally equal to it):

```lean
∀ (N d m s : Nat), 2 ^ N ≤ d →
  ((∀ x : Nat, x < 2 ^ N → (x * m) >>> s = x / d) ↔ (2 ^ N - 1) * m < 2 ^ s)
```

**Plain claim.** (a) For 1 <= d < 2^N and every m, s: (x*m) >>> s = x / d for all x < 2^N if and only if 2^s <= m*d and nc*(m*d - 2^s) < 2^s, where nc = lastFullBlockEnd N d = 2^N - (2^N mod d) - 1. (b) For 2^N <= d and every m, s: it holds if and only if (2^N - 1)*m < 2^s.

**Hypothesis ledger.**

- `hd: 0 < d (part a)` — At d = 0 every quotient is 0 by convention, so m = 0 is junk-correct while 2^s <= 0 fails. *Tightness:* tight; counterexample `ce_exactCriterion_d_zero`; witness class: an instance with N = 1, d = 0, m = 0, s = 0.
- `hdN: d < 2^N (part a)` — For d >= 2^N every N-bit quotient is 0 and the lower bound 2^s <= m*d is not necessary. *Tightness:* tight; counterexample `ce_exactCriterion_hdN`; witness class: an instance with N = 1, d = 2, m = 0, s = 0.
- `hdN: 2^N <= d (part b)` — Below 2^N some quotients are positive and the criterion of part (a) applies instead. *Tightness:* tight; counterexample `ce_two_pow_le`; witness class: an instance with N = 1, d = 1, m = 2, s = 1.

**Non-vacuity witness.** Part (a): N = 8, d = 7; part (b): N = 8, d = 300. (`nv_exact_u8`, which proves that all hypotheses hold for this instance.)

**Non-claims.** Listed under Boundaries, *Non-claims of result 8*.

**Prior art.**

- Daniel Lemire, Colin Bartlett, Owen Kaser, 'Integer Division by Constants: Optimal Bounds', Heliyon 7(6):e07442, 2021, DOI 10.1016/j.heliyon.2021.e07442; arXiv:2012.12369v3. Theorem 1 (for an integer divisor d > 0 and numerators n in [0, N] with N >= d): floor(n/d) = floor(c*n/m) for all such n iff 1/d <= c/m < (1 + 1/(N - remainder(N + 1, d)))/d. With m = 2^s and N = 2^N' - 1 this is part (a) of the criterion; it assumes N >= d and so does not cover part (b) (2^N' <= d).
- Hacker's Delight companion code, repository hcs0/Hackers-Delight, commit 2bcb559da638a97f429c19889e6fd7d8601fd5d2, file magicu.c.txt: nc = -1 - (-d)%d (in 32-bit unsigned arithmetic, 2^32 - 1 - (2^32 mod d)) and the loop condition q1 < delta || (q1 == delta && r1 == 0) with delta = d - 1 - r2; file magicgu.py.txt: nc = ((nmax + 1)//d)*d - 1 and the test 2**p > nc*(d - 1 - (2**p - 1)%d).
- LLVM, repository llvm/llvm-project, commit c312bf3fa94430185410c06c502abd9953f838fa, file llvm/lib/Support/DivisionByConstantInfo.cpp: UnsignedDivisionByConstantInfo::get computes NC, 'the largest dividend such that NC.urem(D) == D-1', and increases the exponent P until the loop condition Q1 < Delta || (Q1 == Delta && R1 == 0) fails, i.e. until 2^P > NC*Delta with Delta = Magic*D - 2^P; it sets IsAdd when the magic number needs an extra bit and then lowers PostShift by one. Basis: source inspection; nothing here is a formal model of this code.
- Source records, with verbatim quotations where this card relies on a stated theorem or rule: [LBK21-T1], [HD-code], [LLVM] (Evidence, *Primary sources*).

**Design question.** Exactly which (multiplier, shift) pairs compute unsigned N-bit floor division by a constant d?

### 9. `exists_mulShiftCorrect_iff_ceilDiv`

**Kind:** characterization. **Tier:** T0: derived explicitly in Lemire-Bartlett-Kaser Section 4.1 (smallest c is ceiling(m/d)). **Depth:** shallow.

Basis: execution (Lean kernel check)

**Lean statement.**

```lean
-- lean/Toy/MagicDiv/Statements.lean:204-206
theorem exists_mulShiftCorrect_iff_ceilDiv (N d s : Nat) (hd : 0 < d)
    (hdN : d < 2 ^ N) :
    (∃ m, MulShiftCorrect N d m s) ↔ MulShiftCorrect N d (ceilDiv (2 ^ s) d) s := by
```

Unfolded rendering of `exists_mulShiftCorrect_iff_ceilDiv` (a Lean term that elaborates in the statement's context and is definitionally equal to it):

```lean
∀ (N d s : Nat), 0 < d → d < 2 ^ N →
  ((∃ m : Nat, ∀ x : Nat, x < 2 ^ N → (x * m) >>> s = x / d) ↔
    ∀ x : Nat, x < 2 ^ N → (x * ((2 ^ s + d - 1) / d)) >>> s = x / d)
```

**Plain claim.** For 1 <= d < 2^N and every shift s: some multiplier m satisfies (x*m) >>> s = x / d for all x < 2^N if and only if the ceiling multiplier ceil(2^s/d) does.

**Hypothesis ledger.**

- `hd: 0 < d` — Excludes the degenerate divisor; at d = 0 the conclusion still holds by Lean's x / 0 = 0 convention (exists_mulShiftCorrect_iff_ceilDiv_d_zero). *Tightness:* harmless.
- `hdN: d < 2^N` — For N = 1, d = 2, s = 0 the multiplier 0 is correct but the ceiling multiplier 1 is not. *Tightness:* tight; counterexample `ce_exists_ceilDiv_hdN`; witness class: an instance with N = 1, d = 2, s = 0.

**Non-vacuity witness.** N = 8, d = 7. (`nv_exact_u8_div7`, which proves that all hypotheses hold for this instance.)

**Non-claims.** Listed under Boundaries, *Non-claims of result 9*.

**Prior art.**

- Daniel Lemire, Colin Bartlett, Owen Kaser, 'Integer Division by Constants: Optimal Bounds', Heliyon 7(6):e07442, 2021, DOI 10.1016/j.heliyon.2021.e07442; arXiv:2012.12369v3. Section 4.1, paragraph after Remark 1: for fixed m, 'if c is to be as small as possible, we must have that c = ceiling(m/d)'.
- Hacker's Delight companion code, repository hcs0/Hackers-Delight, commit 2bcb559da638a97f429c19889e6fd7d8601fd5d2, file magicu.c.txt: nc = -1 - (-d)%d (in 32-bit unsigned arithmetic, 2^32 - 1 - (2^32 mod d)) and the loop condition q1 < delta || (q1 == delta && r1 == 0) with delta = d - 1 - r2; file magicgu.py.txt: nc = ((nmax + 1)//d)*d - 1 and the test 2**p > nc*(d - 1 - (2**p - 1)%d).
- Source records, with verbatim quotations where this card relies on a stated theorem or rule: [LBK21-S4.1], [HD-code] (Evidence, *Primary sources*).

**Design question.** Given a shift, which multiplier should be tried?

### 10. `mulShiftCorrect_ceilDiv_succ`

**Kind:** theorem. **Tier:** T1: implicit in the shift searches of Warren's magicu and LLVM, which stop at the first working shift; not stated as a theorem in the sources consulted. **Depth:** shallow.

Basis: execution (Lean kernel check)

**Lean statement.**

```lean
-- lean/Toy/MagicDiv/Statements.lean:158-160
theorem mulShiftCorrect_ceilDiv_succ (N d s : Nat)
    (h : MulShiftCorrect N d (ceilDiv (2 ^ s) d) s) :
    MulShiftCorrect N d (ceilDiv (2 ^ (s + 1)) d) (s + 1) := by
```

Unfolded rendering of `mulShiftCorrect_ceilDiv_succ` (a Lean term that elaborates in the statement's context and is definitionally equal to it):

```lean
∀ (N d s : Nat),
  (∀ x : Nat, x < 2 ^ N → (x * ((2 ^ s + d - 1) / d)) >>> s = x / d) →
  ∀ x : Nat, x < 2 ^ N → (x * ((2 ^ (s + 1) + d - 1) / d)) >>> (s + 1) = x / d
```

**Plain claim.** For every N, d and s: if the ceiling multiplier ceil(2^s/d) is correct at shift s for all x < 2^N, then the ceiling multiplier ceil(2^(s+1)/d) is correct at shift s + 1.

**Hypothesis ledger.**

- `h: MulShiftCorrect N d (ceilDiv (2^s) d) s` — Without the premise the conclusion can fail. *Tightness:* tight; counterexample `ce_ceilDiv_succ_premise`; witness class: an instance with N = 8, d = 7, s = 9.

**Non-vacuity witness.** N = 8, d = 7, s = 11. (`nv_ceilDiv_succ_u8_div7`, which proves that all hypotheses hold for this instance.)

**Non-claims.** Listed under Boundaries, *Non-claims of result 10*.

**Prior art.**

- LLVM, repository llvm/llvm-project, commit c312bf3fa94430185410c06c502abd9953f838fa, file llvm/lib/Support/DivisionByConstantInfo.cpp: UnsignedDivisionByConstantInfo::get computes NC, 'the largest dividend such that NC.urem(D) == D-1', and increases the exponent P until the loop condition Q1 < Delta || (Q1 == Delta && R1 == 0) fails, i.e. until 2^P > NC*Delta with Delta = Magic*D - 2^P; it sets IsAdd when the magic number needs an extra bit and then lowers PostShift by one. Basis: source inspection; nothing here is a formal model of this code.
- Hacker's Delight companion code, repository hcs0/Hackers-Delight, commit 2bcb559da638a97f429c19889e6fd7d8601fd5d2, file magicu.c.txt: nc = -1 - (-d)%d (in 32-bit unsigned arithmetic, 2^32 - 1 - (2^32 mod d)) and the loop condition q1 < delta || (q1 == delta && r1 == 0) with delta = d - 1 - r2; file magicgu.py.txt: nc = ((nmax + 1)//d)*d - 1 and the test 2**p > nc*(d - 1 - (2**p - 1)%d).
- Source records, with verbatim quotations where this card relies on a stated theorem or rule: [LLVM], [HD-code] (Evidence, *Primary sources*).

**Design question.** Can the minimal correct shift be found by increasing the shift until the ceiling multiplier works?

### 11. `sdivMagic_eq_tdiv_of_sandwich`

**Kind:** theorem. **Tier:** T0: Granlund-Montgomery Theorem 5.1 for d > 0, mechanized in Coq (CompCert Zquot_mul). **Depth:** substantive.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — How a compiler encodes the signed multiplier (`m - 2^N` with a signed multiply-high and the dividend added back), and the count of LLVM signed pairs outside the sandwich (28 of 126 divisors at width 8, from re-running LLVM's loop outside Lean), are modeling-bridge claims (item 3); of those pairs, the `D = 35` pair is kernel-checked (`signed_sandwich_not_necessary_i8_div35`) and the others are not.

**Lean statement.**

```lean
-- lean/Toy/MagicDiv/Statements.lean:602-604
theorem sdivMagic_eq_tdiv_of_sandwich (N ℓ d m : Nat)
    (hlo : 2 ^ (N - 1 + ℓ) < m * d) (hhi : m * d ≤ 2 ^ (N - 1 + ℓ) + 2 ^ ℓ) :
    ∀ x, SignedRange N x → sdivMagic m (N - 1 + ℓ) x = Int.tdiv x d := by
```

Unfolded rendering of `sdivMagic_eq_tdiv_of_sandwich` (a Lean term that elaborates in the statement's context and is definitionally equal to it):

```lean
∀ (N ℓ d m : Nat), 2 ^ (N - 1 + ℓ) < m * d → m * d ≤ 2 ^ (N - 1 + ℓ) + 2 ^ ℓ →
  ∀ x : Int, (-(2 : Int) ^ N ≤ 2 * x ∧ 2 * x < (2 : Int) ^ N) →
    ((x * (m : Int)) >>> (N - 1 + ℓ)) + (if x < 0 then 1 else 0) = Int.tdiv x (d : Int)
```

**Plain claim.** For all N, l, d, m (d, m natural numbers; N - 1 is truncated subtraction, so (N-1)+l = l at N = 0) with 2^((N-1)+l) < m*d <= 2^((N-1)+l) + 2^l: for every signed N-bit x (-2^N <= 2x < 2^N), ((x*m) >>> ((N-1)+l)) + (1 if x < 0 else 0) = Int.tdiv x d, with the exact integer product and the flooring arithmetic shift.

**Hypothesis ledger.**

- `hlo: 2^((N-1)+l) < m*d (strict)` — Negative multiples of d need a strictly positive overshoot; equality fails at x = -d. *Tightness:* tight; counterexample `ce_sdiv_hlo`; witness class: an instance with N = 8, l = 1, d = 2, m = 128 (fails at x = -2).
- `hhi: m*d <= 2^((N-1)+l) + 2^l` — Bounds the overshoot as in the unsigned case, for |x| <= 2^(N-1). *Tightness:* tight; counterexample `ce_sdiv_hhi`; witness class: an instance with N = 8, l = 2, d = 7, m = 74 (fails at x = -125).
- `hx: SignedRange N x` — The overshoot grows with |x|. *Tightness:* tight; counterexample `ce_sdiv_range`; witness class: an instance with N = 1, l = 0, d = 1, m = 2 (fails at x = 1 and at x = -2).

**Non-vacuity witness.** N = 32, l = 3, d = 7, m = signedMagic 32 7 = 2454267027 (m*7 - 2^34 = 5 <= 2^3), x = -7. (`nv_signed_sandwich_i32_div7`, which proves that all hypotheses hold for this instance.)

**Non-claims.** Listed under Boundaries, *Non-claims of result 11*.

**Prior art.**

- Torbjörn Granlund and Peter L. Montgomery, 'Division by Invariant Integers using Multiplication', Proceedings of the ACM SIGPLAN 1994 Conference on Programming Language Design and Implementation (PLDI '94), pp. 61-72, 1994, DOI 10.1145/178243.178249 (also printed in SIGPLAN Notices 29(6):61-72, DOI 10.1145/773473.178249). Theorem 5.1: if d != 0 and 0 < m*|d| - 2^(N+l-1) <= 2^l, then for -2^(N-1) <= n <= 2^(N-1) - 1 and q0 = floor(m*n/2^(N+l-1)), TRUNC(n/d) = q0 for n >= 0, d > 0 and 1 + q0 for n < 0, d > 0 (with sign changes for d < 0). Section 5 also warns: 'When d < 0, avoid rewriting the quotient as TRUNC((-n)/|d|), which fails for n = -2^(N-1).'
- Torbjörn Granlund and Peter L. Montgomery, 'Division by Invariant Integers using Multiplication', Proceedings of the ACM SIGPLAN 1994 Conference on Programming Language Design and Implementation (PLDI '94), pp. 61-72, 1994, DOI 10.1145/178243.178249 (also printed in SIGPLAN Notices 29(6):61-72, DOI 10.1145/773473.178249). Figure 5.1: l = max(ceil(log2 |d|), 1), m = 1 + floor(2^(N+l-1)/|d|), m0 = m - 2^N, q0 = n + MULSH(m0, n), q0 = SRA(q0, l - 1) - XSIGN(n).
- CompCert, repository AbsInt/CompCert, commit 5e4ef44c57b22cdc2e1893770843fd693a5f82e1, file backend/SelectDivproof.v: Lemma Zquot_mul (Coq proof over Z of Granlund-Montgomery Theorem 5.1 for d > 0, strict lower bound, -2^N <= n < 2^N) and Theorem divs_mul_shift_2 (32-bit: for m >= 2^31 the quotient is computed with mulhs x m plus x); backend/SelectDiv.vp: divs_mul_params checks 2^(32+p) < m*d <= 2^(32+p) + 2^(p+1).
- LLVM, repository llvm/llvm-project, commit c312bf3fa94430185410c06c502abd9953f838fa, file llvm/lib/Support/DivisionByConstantInfo.cpp: SignedDivisionByConstantInfo::get implements Warren's signed search with ANC = T - 1 - T.urem(|D|), T = 2^(W-1) + (D >>> (W-1)); re-running its loop for W = 8 and D = 2..127 gives pairs violating the sandwich hhi of sdivMagic_eq_tdiv_of_sandwich for 28 of the 126 divisors (D = 35: Magic = 59, total shift 11), all of which are nevertheless correct (source inspection and a re-implementation of the loop; not formalized).
- Source records, with verbatim quotations where this card relies on a stated theorem or rule: [GM94-T5.1], [GM94-F5.1], [CompCert], [LLVM] (Evidence, *Primary sources*).

**Design question.** Which multipliers compute signed N-bit division by a positive constant d, rounding toward zero?

### 12. `sdivMagicUncorrected_eq_tdiv_sub_one_of_neg`

**Kind:** theorem. **Tier:** T0: the q0 = TRUNC(n/d) - 1 case of Granlund-Montgomery Theorem 5.1. **Depth:** shallow.

Basis: execution (Lean kernel check)

**Lean statement.**

```lean
-- lean/Toy/MagicDiv/Statements.lean:641-644
theorem sdivMagicUncorrected_eq_tdiv_sub_one_of_neg (N ℓ d m : Nat)
    (hlo : 2 ^ (N - 1 + ℓ) < m * d) (hhi : m * d ≤ 2 ^ (N - 1 + ℓ) + 2 ^ ℓ) :
    ∀ x, SignedRange N x → x < 0 →
      sdivMagicUncorrected m (N - 1 + ℓ) x = Int.tdiv x d - 1 := by
```

Unfolded rendering of `sdivMagicUncorrected_eq_tdiv_sub_one_of_neg` (a Lean term that elaborates in the statement's context and is definitionally equal to it):

```lean
∀ (N ℓ d m : Nat), 2 ^ (N - 1 + ℓ) < m * d → m * d ≤ 2 ^ (N - 1 + ℓ) + 2 ^ ℓ →
  ∀ x : Int, (-(2 : Int) ^ N ≤ 2 * x ∧ 2 * x < (2 : Int) ^ N) → x < 0 →
    (x * (m : Int)) >>> (N - 1 + ℓ) = Int.tdiv x (d : Int) - 1
```

**Plain claim.** For all N, l and natural numbers d, m (N - 1 is truncated subtraction, so (N-1)+l = l at N = 0), under the same bounds 2^((N-1)+l) < m*d <= 2^((N-1)+l) + 2^l, for every signed N-bit x with x < 0, omitting the negative-dividend correction gives (x*m) >>> ((N-1)+l) = Int.tdiv x d - 1.

**Hypothesis ledger.**

- `hlo: 2^((N-1)+l) < m*d (strict)` — As for sdivMagic_eq_tdiv_of_sandwich. *Tightness:* tight; counterexample `ce_uncorr_hlo`; witness class: an instance with N = 8, l = 1, d = 2, m = 128 (fails at x = -2).
- `hhi: m*d <= 2^((N-1)+l) + 2^l` — As for sdivMagic_eq_tdiv_of_sandwich. *Tightness:* tight; counterexample `ce_uncorr_hhi`; witness class: an instance with N = 8, l = 2, d = 7, m = 74 (fails at x = -125).
- `hx: SignedRange N x` — As for sdivMagic_eq_tdiv_of_sandwich. *Tightness:* tight; counterexample `ce_uncorr_range`; witness class: an instance with N = 1, l = 0, d = 1, m = 2 (fails at x = -2).
- `hneg: x < 0` — For x >= 0 the uncorrected sequence is already Int.tdiv x d. *Tightness:* tight; counterexample `ce_uncorr_neg`; witness class: an instance with N = 8, l = 2, d = 3, m = 171 (fails at x = 0).

**Non-vacuity witness.** N = 32, l = 3, d = 7, m = 2454267027, x = -7. (`nv_sdivMagicUncorrected`, which proves that all hypotheses hold for this instance.)

**Non-claims.** Listed under Boundaries, *Non-claims of result 12*.

**Prior art.**

- Torbjörn Granlund and Peter L. Montgomery, 'Division by Invariant Integers using Multiplication', Proceedings of the ACM SIGPLAN 1994 Conference on Programming Language Design and Implementation (PLDI '94), pp. 61-72, 1994, DOI 10.1145/178243.178249 (also printed in SIGPLAN Notices 29(6):61-72, DOI 10.1145/773473.178249). Theorem 5.1: if d != 0 and 0 < m*|d| - 2^(N+l-1) <= 2^l, then for -2^(N-1) <= n <= 2^(N-1) - 1 and q0 = floor(m*n/2^(N+l-1)), TRUNC(n/d) = q0 for n >= 0, d > 0 and 1 + q0 for n < 0, d > 0 (with sign changes for d < 0). Section 5 also warns: 'When d < 0, avoid rewriting the quotient as TRUNC((-n)/|d|), which fails for n = -2^(N-1).'
- CompCert, repository AbsInt/CompCert, commit 5e4ef44c57b22cdc2e1893770843fd693a5f82e1, file backend/SelectDivproof.v: Lemma Zquot_mul (Coq proof over Z of Granlund-Montgomery Theorem 5.1 for d > 0, strict lower bound, -2^N <= n < 2^N) and Theorem divs_mul_shift_2 (32-bit: for m >= 2^31 the quotient is computed with mulhs x m plus x); backend/SelectDiv.vp: divs_mul_params checks 2^(32+p) < m*d <= 2^(32+p) + 2^(p+1).
- Torbjörn Granlund and Peter L. Montgomery, 'Division by Invariant Integers using Multiplication', Proceedings of the ACM SIGPLAN 1994 Conference on Programming Language Design and Implementation (PLDI '94), pp. 61-72, 1994, DOI 10.1145/178243.178249 (also printed in SIGPLAN Notices 29(6):61-72, DOI 10.1145/773473.178249). Section 6 (quotient rounded towards -infinity), equation (6.3) and Figure 6.1: for constant d > 0, floor(n/d) = EOR(nsign, TRUNC(EOR(nsign, n)/d)) with nsign = XSIGN(n), computed with one unsigned multiply-high.
- Source records, with verbatim quotations where this card relies on a stated theorem or rule: [GM94-T5.1], [CompCert], [GM94-S6] (Evidence, *Primary sources*).

**Design question.** What does the signed sequence compute if the negative-dividend correction is omitted?

### 13. `tdiv_signedRange_iff`

**Kind:** characterization. **Tier:** T0: mechanized for bit vectors in the Lean 4 core library (BitVec.sdivOverflow_eq and related lemmas); stated here for Int.tdiv with an arbitrary integer divisor. **Depth:** shallow.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — What particular languages or instruction sets do for `(-2^(N-1)) / (-1)` was not examined (Modeling bridge, item 5); the kernel check covers core `BitVec.sdiv` at `N = 8` (`bitvec_sdiv_intMin_negOne_wraps`) and no language or instruction set.

**Lean statement.**

```lean
-- lean/Toy/MagicDiv/Statements.lean:672-673
theorem tdiv_signedRange_iff (N : Nat) (x d : Int) (hx : SignedRange N x) :
    SignedRange N (Int.tdiv x d) ↔ ¬ (x = -(2 : Int) ^ (N - 1) ∧ d = -1) := by
```

Unfolded rendering of `tdiv_signedRange_iff` (a Lean term that elaborates in the statement's context and is definitionally equal to it):

```lean
∀ (N : Nat) (x d : Int), (-(2 : Int) ^ N ≤ 2 * x ∧ 2 * x < (2 : Int) ^ N) →
  ((-(2 : Int) ^ N ≤ 2 * Int.tdiv x d ∧ 2 * Int.tdiv x d < (2 : Int) ^ N) ↔
    ¬ (x = -(2 : Int) ^ (N - 1) ∧ d = -1))
```

**Plain claim.** For every N, every signed N-bit x (-2^N <= 2x < 2^N; for N = 0 this is x = 0) and every integer d: Int.tdiv x d is again a signed N-bit value if and only if not (x = -2^(N-1) and d = -1), where N - 1 is truncated subtraction (at N = 0 the excluded case reads x = -1, which the signed 0-bit range {0} does not contain).

**Hypothesis ledger.**

- `hx: SignedRange N x` — Out-of-range dividends give out-of-range quotients already for d = 1. *Tightness:* tight; counterexample `ce_tdiv_signedRange_hx`; witness class: an instance with N = 8, x = 128, d = 1.

**Non-vacuity witness.** N = 8, x = -128. (`nv_tdiv_signedRange`, which proves that all hypotheses hold for this instance.)

**Non-claims.** Listed under Boundaries, *Non-claims of result 13*.

**Prior art.**

- Lean 4 core library, toolchain leanprover/lean4:v4.34.1: BitVec.sdivOverflow_eq (Init/Data/BitVec/Bitblast.lean:1321), BitVec.toInt_sdiv_of_ne_or_ne (line 1578), BitVec.intMin_sdiv_neg_one (line 1648), and Int.natAbs_tdiv_le_natAbs (Init/Data/Int/DivMod/Lemmas.lean:1593) mechanize the bit-vector form of the overflow characterization.
- Torbjörn Granlund and Peter L. Montgomery, 'Division by Invariant Integers using Multiplication', Proceedings of the ACM SIGPLAN 1994 Conference on Programming Language Design and Implementation (PLDI '94), pp. 61-72, 1994, DOI 10.1145/178243.178249 (also printed in SIGPLAN Notices 29(6):61-72, DOI 10.1145/773473.178249). 'Overflow detection. The quotient n/d overflows if n = -2^(N-1) and d = -1. The algorithm in Figure 5.1 returns -2^(N-1).'
- Source records, with verbatim quotations where this card relies on a stated theorem or rule: [Lean-core], [GM94-OVF] (Evidence, *Primary sources*).

**Design question.** Which signed N-bit divisions overflow, so that a lowering must treat them specially?

### 14. `signedMagic_sandwich`

**Kind:** theorem. **Tier:** T0: Granlund-Montgomery Figure 5.1's multiplier (with l = clog2 d instead of max(clog2 d, 1)). **Depth:** shallow.

Basis: execution (Lean kernel check)

**Lean statement.**

```lean
-- lean/Toy/MagicDiv/Statements.lean:652-654
theorem signedMagic_sandwich (N d : Nat) (hd : 0 < d) :
    2 ^ (N - 1 + clog2 d) < signedMagic N d * d ∧
      signedMagic N d * d ≤ 2 ^ (N - 1 + clog2 d) + 2 ^ clog2 d := by
```

Unfolded rendering of `signedMagic_sandwich` (a Lean term that elaborates in the statement's context and is definitionally equal to it):

```lean
∀ (N d : Nat), 0 < d →
  let ℓ : Nat := clog2 d;
  let m : Nat := 2 ^ (N - 1 + ℓ) / d + 1;
  2 ^ (N - 1 + ℓ) < m * d ∧ m * d ≤ 2 ^ (N - 1 + ℓ) + 2 ^ ℓ
```

**Plain claim.** For every N and every d >= 1 (N - 1 is truncated subtraction, so (N-1) + clog2 d = clog2 d at N = 0), signedMagic N d = floor(2^((N-1) + clog2 d)/d) + 1 satisfies 2^((N-1)+l) < m*d <= 2^((N-1)+l) + 2^l with l = clog2 d (so sdivMagic_eq_tdiv_of_sandwich applies).

**Hypothesis ledger.**

- `hd: 0 < d` — For d = 0 the strict lower bound fails. *Tightness:* tight; counterexample `ce_signedMagic_d_zero`; witness class: an instance with N = 8, d = 0.

**Non-vacuity witness.** N = 32, d = 7: signedMagic 32 7 = 2454267027. (`nv_signedMagic_sandwich_div7`, which proves that all hypotheses hold for this instance.)

**Non-claims.** Listed under Boundaries, *Non-claims of result 14*.

**Prior art.**

- Torbjörn Granlund and Peter L. Montgomery, 'Division by Invariant Integers using Multiplication', Proceedings of the ACM SIGPLAN 1994 Conference on Programming Language Design and Implementation (PLDI '94), pp. 61-72, 1994, DOI 10.1145/178243.178249 (also printed in SIGPLAN Notices 29(6):61-72, DOI 10.1145/773473.178249). Figure 5.1: l = max(ceil(log2 |d|), 1), m = 1 + floor(2^(N+l-1)/|d|), m0 = m - 2^N, q0 = n + MULSH(m0, n), q0 = SRA(q0, l - 1) - XSIGN(n).
- CompCert, repository AbsInt/CompCert, commit 5e4ef44c57b22cdc2e1893770843fd693a5f82e1, file backend/SelectDivproof.v: Lemma Zquot_mul (Coq proof over Z of Granlund-Montgomery Theorem 5.1 for d > 0, strict lower bound, -2^N <= n < 2^N) and Theorem divs_mul_shift_2 (32-bit: for m >= 2^31 the quotient is computed with mulhs x m plus x); backend/SelectDiv.vp: divs_mul_params checks 2^(32+p) < m*d <= 2^(32+p) + 2^(p+1).
- Henry S. Warren, Jr., Hacker's Delight, 2nd edition, Addison-Wesley, 2012 (electronic ISBN 9780133084993), Chapter 10 'Integer Division By Constants', sections 10-1 'Signed Division by a Known Power of 2' and 10-3 to 10-6 on signed division (section titles from the publisher's table of contents; the book text was not consulted).
- Source records, with verbatim quotations where this card relies on a stated theorem or rule: [GM94-F5.1], [CompCert], [HD] (Evidence, *Primary sources*).

**Design question.** Does a signed multiplier exist for every positive divisor, and which one does the textbook construction pick?

### 15. `int_shiftRight_eq_tdiv_iff`

**Kind:** characterization. **Tier:** T0: an instance of the Lean 4 core lemmas Int.shiftRight_eq_div_pow and Int.tdiv_eq_ediv (also CompCert Zbits Zquot_Zdiv). **Depth:** shallow.

Basis: execution (Lean kernel check)

**Lean statement.**

```lean
-- lean/Toy/MagicDiv/Statements.lean:708-709
theorem int_shiftRight_eq_tdiv_iff (x : Int) (k : Nat) :
    x >>> k = Int.tdiv x (2 ^ k) ↔ (0 ≤ x ∨ (2 : Int) ^ k ∣ x) := by
```

(No package definition occurs in this statement, so it is already fully unfolded.)

**Plain claim.** For every integer x and every k (no hypotheses): the arithmetic shift x >>> k equals Int.tdiv x (2^k) if and only if x >= 0 or 2^k divides x.

**Hypothesis ledger.**

- None: the statement has no hypotheses.

**Non-vacuity witness.** No hypotheses; both truth values occur: -1 >>> 1 = -1 but Int.tdiv (-1) 2 = 0, and -8 >>> 2 = -2 = Int.tdiv (-8) 4. (`nv_int_shiftRight`, which proves that all hypotheses hold for this instance.)

**Non-claims.** Listed under Boundaries, *Non-claims of result 15*.

**Prior art.**

- Lean 4 core library, toolchain leanprover/lean4:v4.34.1: Int.shiftRight_eq_div_pow (Init/Data/Int/Bitwise/Lemmas.lean:44) and Int.tdiv_eq_ediv (Init/Data/Int/DivMod/Lemmas.lean:223: a.tdiv b = a / b + if 0 <= a or b divides a then 0 else sign b); the card is their instance at b = 2^k.
- CompCert, repository AbsInt/CompCert, commit 5e4ef44c57b22cdc2e1893770843fd693a5f82e1, file lib/Zbits.v: Lemma Zquot_Zdiv (line 933: for y > 0, Z.quot x y = if x < 0 then (x + y - 1)/y else x/y) and Lemma Zdiv_shift (line 948).
- Torbjörn Granlund and Peter L. Montgomery, 'Division by Invariant Integers using Multiplication', Proceedings of the ACM SIGPLAN 1994 Conference on Programming Language Design and Implementation (PLDI '94), pp. 61-72, 1994, DOI 10.1145/178243.178249 (also printed in SIGPLAN Notices 29(6):61-72, DOI 10.1145/773473.178249). Figure 5.2 (signed TRUNC(n/d) for constant d != 0) handles |d| = 1 in a separate first branch and, for |d| = 2^l, issues q = SRA(n + SRL(SRA(n, l - 1), N - l), l), then negates q if d < 0; Table 3.1 restricts SLL, SRA and SRL shift counts to 0 <= n <= N - 1. (The paper uses this bias sequence; it does not state the characterization of this card.)
- Source records, with verbatim quotations where this card relies on a stated theorem or rule: [Lean-core], [CompCert], [GM94-F5.2], [GM94-T3.1] (Evidence, *Primary sources*).

**Design question.** When may signed division by 2^k be replaced by a plain arithmetic shift?

### 16. `biasDiv_eq_tdiv_of_lt`

**Kind:** theorem. **Tier:** T0: Granlund-Montgomery Figure 5.2's power-of-two branch; the wrapping word-size-generic version is CompCert's shrx_shr_2. **Depth:** shallow.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — Which real shift semantics correspond to part (a) (total) and part (b) (count modulo the width) is a documentation claim about C, C++, LLVM IR, Rust, x86, AArch64 and RISC-V (Modeling bridge, item 4).

**Lean statements.**

```lean
-- lean/Toy/MagicDiv/Statements.lean:735-736
theorem biasDiv_eq_tdiv_of_lt (N k : Nat) (hk : k < N) (x : Int) (hx : SignedRange N x) :
    SignedRange N (biasSum N k x) ∧ biasDiv N k x = Int.tdiv x (2 ^ k) := by
```

Unfolded rendering of `biasDiv_eq_tdiv_of_lt` (a Lean term that elaborates in the statement's context and is definitionally equal to it):

```lean
∀ (N k : Nat), k < N → ∀ x : Int, (-(2 : Int) ^ N ≤ 2 * x ∧ 2 * x < (2 : Int) ^ N) →
  let b : Int := x + ((((x >>> (N - 1)) % (2 : Int) ^ N).toNat >>> (N - k) : Nat) : Int);
  (-(2 : Int) ^ N ≤ 2 * b ∧ 2 * b < (2 : Int) ^ N) ∧ b >>> k = Int.tdiv x (2 ^ k)
```

```lean
-- lean/Toy/MagicDiv/Statements.lean:784-786
theorem biasDivMasked_eq_tdiv_of_pos_of_lt (N k : Nat) (hk1 : 1 ≤ k) (hk : k < N) (x : Int)
    (hx : SignedRange N x) :
    SignedRange N (biasSumMasked N k x) ∧ biasDivMasked N k x = Int.tdiv x (2 ^ k) := by
```

Unfolded rendering of `biasDivMasked_eq_tdiv_of_pos_of_lt` (a Lean term that elaborates in the statement's context and is definitionally equal to it):

```lean
∀ (N k : Nat), 1 ≤ k → k < N → ∀ x : Int, (-(2 : Int) ^ N ≤ 2 * x ∧ 2 * x < (2 : Int) ^ N) →
  let b : Int := x + ((((x >>> ((N - 1) % N)) % (2 : Int) ^ N).toNat >>> ((N - k) % N) : Nat) : Int);
  (-(2 : Int) ^ N ≤ 2 * b ∧ 2 * b < (2 : Int) ^ N) ∧ b >>> (k % N) = Int.tdiv x (2 ^ k)
```

**Plain claim.** (a) With Lean's total shifts (a logical shift of an N-bit pattern by N or more gives 0): for every k < N (so N >= 1, and N - 1 and N - k involve no truncation) and every signed N-bit x, the biased dividend x + ((x >>> (N-1)) >>>_logical (N-k)) stays in the signed N-bit range and biasDiv N k x = Int.tdiv x (2^k); at k = 0 this relies on the logical shift by the full width N returning 0. (b) With every shift count reduced modulo N (as by instructions that reduce the count modulo the operand width): for every 1 <= k < N and every signed N-bit x, the same two conclusions hold for biasSumMasked and biasDivMasked (what fails at k = 0 is listed under the non-claims).

**Hypothesis ledger.**

- `hk1: 1 <= k (part b; not a hypothesis of part a)` — At k = 0 the count N - 0 = N is reduced to 0, so the whole mask 2^N - 1 is added. *Tightness:* tight; counterexample `ce_biasDivMasked_k_zero`; witness class: every N >= 1 with k = 0, x = -1 (result 2^N - 2).
- `hk: k < N (both)` — For k = N the biased dividend leaves the signed range (it would wrap on an N-bit machine). *Tightness:* tight; counterexample `ce_biasDiv_hk`, `ce_biasDivMasked_hk`; witness class: an instance with N = 2, k = 2, x = -1.
- `hx: SignedRange N x (both)` — Out-of-range dividends leave the range already before the shift. *Tightness:* tight; counterexample `ce_biasDiv_hx`, `ce_biasDivMasked_hx`; witness class: an instance with N = 8, k = 1, x = 128.

**Non-vacuity witness.** N = 8, k = 2 (1 <= 2 < 8), x = -7. (`nv_biasDiv`, which proves that all hypotheses hold for this instance.)

**Non-claims.** Listed under Boundaries, *Non-claims of result 16*.

**Prior art.**

- Torbjörn Granlund and Peter L. Montgomery, 'Division by Invariant Integers using Multiplication', Proceedings of the ACM SIGPLAN 1994 Conference on Programming Language Design and Implementation (PLDI '94), pp. 61-72, 1994, DOI 10.1145/178243.178249 (also printed in SIGPLAN Notices 29(6):61-72, DOI 10.1145/773473.178249). Figure 5.2 (signed TRUNC(n/d) for constant d != 0) handles |d| = 1 in a separate first branch and, for |d| = 2^l, issues q = SRA(n + SRL(SRA(n, l - 1), N - l), l), then negates q if d < 0; Table 3.1 restricts SLL, SRA and SRL shift counts to 0 <= n <= N - 1.
- CompCert, repository AbsInt/CompCert, commit 5e4ef44c57b22cdc2e1893770843fd693a5f82e1, file lib/Integers.v (word-size-generic functor Make): Theorem shrx_shr (line 2362) and Theorem shrx_shr_2 (line 2403): for y < zwordsize - 1, shrx x y = shr (add x (shru (shr x (repr (zwordsize - 1))) (sub iwordsize y))) y, with wrapping add.
- Henry S. Warren, Jr., Hacker's Delight, 2nd edition, Addison-Wesley, 2012 (electronic ISBN 9780133084993), Chapter 10 'Integer Division By Constants', sections 10-1 'Signed Division by a Known Power of 2' and 10-3 to 10-6 on signed division (section titles from the publisher's table of contents; the book text was not consulted).
- Source records, with verbatim quotations where this card relies on a stated theorem or rule: [GM94-F5.2], [GM94-T3.1], [CompCert], [HD] (Evidence, *Primary sources*).

**Design question.** How is signed division by 2^k computed with shifts and an add, and which shift amounts are valid on machines whose shifts are not total?

### 17. `biasDivBV_u8`

**Kind:** theorem. **Tier:** T0: an evaluated 8-bit instance of CompCert's word-size-generic shrx_shr_2 on core BitVec. **Depth:** shallow.

Basis: execution (Lean kernel check)

**Bounded check.** Kernel-checked on `BitVec 8`: `decide +kernel` evaluates the first conjunct of `biasDivBV_u8` on all 256 values of x for each k < 8, the second on all 256 values for each k <= 6, and `biasDivBVMasked_u8` on all 256 values for each 1 <= k < 8. No other width is checked, so these checks neither establish nor refute the corresponding claims at other widths; the general-width statement, in exact arithmetic, is result 16.

Basis: derived (modeling bridge) — As for result 16: the correspondence of the two shift semantics with real languages and instruction sets is a documentation claim (Modeling bridge, item 4).

**Lean statements.**

```lean
-- lean/Toy/MagicDiv/Bounded.lean:281-283
theorem biasDivBV_u8 :
    (∀ k, k < 8 → ∀ x : BitVec 8, (biasDivBV k x).toInt = Int.tdiv x.toInt (2 ^ k)) ∧
    (∀ k, k ≤ 6 → ∀ x : BitVec 8, biasDivBV k x = x.sdiv (BitVec.ofNat 8 (2 ^ k))) := by
```

Unfolded rendering of `biasDivBV_u8` (a Lean term that elaborates in the statement's context and is definitionally equal to it):

```lean
(∀ k : Nat, k < 8 → ∀ x : BitVec 8,
    ((x + ((x.sshiftRight (8 - 1)) >>> (8 - k))).sshiftRight k).toInt = Int.tdiv x.toInt (2 ^ k)) ∧
  (∀ k : Nat, k ≤ 6 → ∀ x : BitVec 8,
    (x + ((x.sshiftRight (8 - 1)) >>> (8 - k))).sshiftRight k = x.sdiv (BitVec.ofNat 8 (2 ^ k)))
```

```lean
-- lean/Toy/MagicDiv/Bounded.lean:306-308
theorem biasDivBVMasked_u8 :
    ∀ k, 1 ≤ k → k < 8 → ∀ x : BitVec 8,
      (biasDivBVMasked k x).toInt = Int.tdiv x.toInt (2 ^ k) := by
```

Unfolded rendering of `biasDivBVMasked_u8` (a Lean term that elaborates in the statement's context and is definitionally equal to it):

```lean
∀ k : Nat, 1 ≤ k → k < 8 → ∀ x : BitVec 8,
  ((x + ((x.sshiftRight ((8 - 1) % 8)) >>> ((8 - k) % 8))).sshiftRight (k % 8)).toInt =
    Int.tdiv x.toInt (2 ^ k)
```

**Plain claim.** On core BitVec 8 with wrapping addition: (a) with BitVec's total shifts, for every k < 8 and every x, (biasDivBV k x).toInt = Int.tdiv x.toInt (2^k), and for every k <= 6, biasDivBV k x = BitVec.sdiv x (BitVec.ofNat 8 (2^k)); at k = 0 this relies on the logical shift by 8 returning 0. (b) With all three shift counts reduced modulo 8, (biasDivBVMasked k x).toInt = Int.tdiv x.toInt (2^k) for every 1 <= k < 8 and every x.

**Hypothesis ledger.**

- `k < 8 (biasDivBV_u8, first conjunct)` — At k = 8 the bias 255 wraps the sum. *Tightness:* tight; counterexample `ce_biasDivBV_width`; witness class: an instance with k = 8, x = -1.
- `k <= 6 (biasDivBV_u8, second conjunct)` — At k = 7, BitVec.ofNat 8 128 is the signed value -128. *Tightness:* tight; counterexample `ce_biasDivBV_sdiv_k7`; witness class: an instance with k = 7, x = -128.
- `1 <= k (biasDivBVMasked_u8)` — At k = 0 the reduced count 0 adds the whole mask. *Tightness:* tight; counterexample `ce_biasDivBVMasked_u8_k_zero`; witness class: an instance with k = 0, x = -1.
- `k < 8 (biasDivBVMasked_u8)` — At k = 8 the reduced counts are 7, 0, 0. *Tightness:* tight; counterexample `ce_biasDivBVMasked_u8_k_eight`; witness class: an instance with k = 8, x = -1.

**Non-vacuity witness.** k = 2 (1 <= 2 < 8, 2 <= 6). (`nv_biasDivBV_u8`, which proves that all hypotheses hold for this instance.)

**Non-claims.** Listed under Boundaries, *Non-claims of result 17*.

**Prior art.**

- CompCert, repository AbsInt/CompCert, commit 5e4ef44c57b22cdc2e1893770843fd693a5f82e1, file lib/Integers.v (word-size-generic functor Make): Theorem shrx_shr (line 2362) and Theorem shrx_shr_2 (line 2403): for y < zwordsize - 1, shrx x y = shr (add x (shru (shr x (repr (zwordsize - 1))) (sub iwordsize y))) y, with wrapping add.
- Torbjörn Granlund and Peter L. Montgomery, 'Division by Invariant Integers using Multiplication', Proceedings of the ACM SIGPLAN 1994 Conference on Programming Language Design and Implementation (PLDI '94), pp. 61-72, 1994, DOI 10.1145/178243.178249 (also printed in SIGPLAN Notices 29(6):61-72, DOI 10.1145/773473.178249). Figure 5.2 (signed TRUNC(n/d) for constant d != 0) handles |d| = 1 in a separate first branch and, for |d| = 2^l, issues q = SRA(n + SRL(SRA(n, l - 1), N - l), l), then negates q if d < 0; Table 3.1 restricts SLL, SRA and SRL shift counts to 0 <= n <= N - 1.
- Source records, with verbatim quotations where this card relies on a stated theorem or rule: [CompCert], [GM94-F5.2] (Evidence, *Primary sources*).

**Design question.** Does the bias-and-shift sequence survive wrap-around arithmetic on a real bit-vector type, and with which shift semantics?

### 18. `mulShift_rem_eq_mod_of_correct`

**Kind:** theorem. **Tier:** T0: the conventional remainder n - (n div d)*d (Lemire-Kaser-Kurz Section 1; CompCert modu_divu). **Depth:** shallow.

Basis: execution (Lean kernel check)

**Lean statement.**

```lean
-- lean/Toy/MagicDiv/Statements.lean:471-472
theorem mulShift_rem_eq_mod_of_correct (N d m s : Nat) (h : MulShiftCorrect N d m s) :
    ∀ x, x < 2 ^ N → x - d * ((x * m) >>> s) = x % d := by
```

Unfolded rendering of `mulShift_rem_eq_mod_of_correct` (a Lean term that elaborates in the statement's context and is definitionally equal to it):

```lean
∀ (N d m s : Nat), (∀ x : Nat, x < 2 ^ N → (x * m) >>> s = x / d) →
  ∀ x : Nat, x < 2 ^ N → x - d * ((x * m) >>> s) = x % d
```

**Plain claim.** For all N, d, m, s: if (x*m) >>> s = x / d for every x < 2^N, then x - d*((x*m) >>> s) = x mod d for every x < 2^N (in particular under the sandwich bounds: mulShift_rem_eq_mod_of_sandwich).

**Hypothesis ledger.**

- `h: MulShiftCorrect N d m s` — The remainder formula is derived from the quotient; with a wrong quotient it can be wrong. *Tightness:* tight; counterexample `ce_rem_correct`; witness class: an instance with N = 1, d = 1, m = 0, s = 0 (fails at x = 1).
- `input range x < 2^N` — The quotient is assumed correct for N-bit inputs x < 2^N; nothing is assumed about larger x. *Tightness:* tight; counterexample `ce_rem_input_range`; witness class: an instance with N = 1, d = 3, m = 1, s = 1 (fails at x = 2).

**Non-vacuity witness.** N = 8, d = 7, (m, s) = (293, 11), x = 200. (`nv_mulShift_rem`, which proves that all hypotheses hold for this instance.)

**Non-claims.** Listed under Boundaries, *Non-claims of result 18*.

**Prior art.**

- Daniel Lemire, Owen Kaser, Nathan Kurz, 'Faster Remainder by Direct Computation: Applications to Compilers and Software Libraries', Software: Practice and Experience 49(6):953-970, 2019, DOI 10.1002/spe.2689; arXiv:1902.01961v3. Section 1 (Introduction): the conventional remainder 'n mod d = n - (n div d) * d' after computing the quotient by multiplication and shift.
- CompCert, repository AbsInt/CompCert, commit 5e4ef44c57b22cdc2e1893770843fd693a5f82e1, file lib/Integers.v: Theorem modu_divu (line 966) and Theorem mods_divs (line 990), remainder as x - (x/y)*y; file backend/SelectDivproof.v: Theorem eval_moduimm (line 574) and Theorem eval_modsimm (line 694).
- Source records, with verbatim quotations where this card relies on a stated theorem or rule: [LKK19-S1], [CompCert] (Evidence, *Primary sources*).

**Design question.** Can the remainder always be recovered from a correct multiply-shift quotient?

### 19. `sremMagic_eq_tmod_and_sign`

**Kind:** theorem. **Tier:** T0: Lean 4 core Int.tmod lemmas combined with sdivMagic_eq_tdiv_of_sandwich (CompCert mods_divs and eval_modsimm for the machine version). **Depth:** shallow.

Basis: execution (Lean kernel check)

Basis: derived (modeling bridge) — Hardware or language behavior of `x % (-1)` at `x = -2^(N-1)` was not examined (Modeling bridge, item 5).

**Lean statement.**

```lean
-- lean/Toy/MagicDiv/Statements.lean:797-802
theorem sremMagic_eq_tmod_and_sign (N ℓ d m : Nat)
    (hlo : 2 ^ (N - 1 + ℓ) < m * d) (hhi : m * d ≤ 2 ^ (N - 1 + ℓ) + 2 ^ ℓ) :
    ∀ x, SignedRange N x →
      sremMagic d m (N - 1 + ℓ) x = Int.tmod x d ∧
      (0 ≤ x → 0 ≤ sremMagic d m (N - 1 + ℓ) x ∧ sremMagic d m (N - 1 + ℓ) x < d) ∧
      (x < 0 → -(d : Int) < sremMagic d m (N - 1 + ℓ) x ∧ sremMagic d m (N - 1 + ℓ) x ≤ 0) := by
```

Unfolded rendering of `sremMagic_eq_tmod_and_sign` (a Lean term that elaborates in the statement's context and is definitionally equal to it):

```lean
∀ (N ℓ d m : Nat), 2 ^ (N - 1 + ℓ) < m * d → m * d ≤ 2 ^ (N - 1 + ℓ) + 2 ^ ℓ →
  ∀ x : Int, (-(2 : Int) ^ N ≤ 2 * x ∧ 2 * x < (2 : Int) ^ N) →
    let r : Int := x - (d : Int) * (((x * (m : Int)) >>> (N - 1 + ℓ)) + (if x < 0 then 1 else 0));
    r = Int.tmod x (d : Int) ∧ (0 ≤ x → 0 ≤ r ∧ r < (d : Int)) ∧ (x < 0 → -(d : Int) < r ∧ r ≤ 0)
```

**Plain claim.** For all N, l and natural numbers d, m (N - 1 is truncated subtraction, so (N-1)+l = l at N = 0), under 2^((N-1)+l) < m*d <= 2^((N-1)+l) + 2^l, for every signed N-bit x: x - d*sdivMagic m ((N-1)+l) x = Int.tmod x d; it lies in [0, d) when x >= 0 and in (-d, 0] when x < 0.

**Hypothesis ledger.**

- `hlo: 2^((N-1)+l) < m*d (strict)` — As for sdivMagic_eq_tdiv_of_sandwich. *Tightness:* tight; counterexample `ce_srem_hlo`; witness class: an instance with N = 8, l = 1, d = 2, m = 128, x = -2.
- `hhi: m*d <= 2^((N-1)+l) + 2^l` — As for sdivMagic_eq_tdiv_of_sandwich. *Tightness:* tight; counterexample `ce_srem_hhi`; witness class: an instance with N = 8, l = 2, d = 7, m = 74, x = -125.
- `hx: SignedRange N x` — As for sdivMagic_eq_tdiv_of_sandwich. *Tightness:* tight; counterexample `ce_srem_range`; witness class: an instance with N = 1, l = 0, d = 1, m = 2, x = 1.

**Non-vacuity witness.** N = 32, l = 3, d = 7, m = 2454267027, x = 7 and x = -7. (`nv_sremMagic_both_signs`, which proves that all hypotheses hold for this instance.)

**Non-claims.** Listed under Boundaries, *Non-claims of result 19*.

**Prior art.**

- Lean 4 core library, toolchain leanprover/lean4:v4.34.1: Int.tmod_def (Init/Data/Int/DivMod/Lemmas.lean:372), Int.tmod_nonneg (1393), Int.tmod_neg (1396), Int.tmod_lt_of_pos (1403), Int.lt_tmod_of_pos (1409).
- CompCert, repository AbsInt/CompCert, commit 5e4ef44c57b22cdc2e1893770843fd693a5f82e1, file lib/Integers.v: Theorem modu_divu (line 966) and Theorem mods_divs (line 990), remainder as x - (x/y)*y; file backend/SelectDivproof.v: Theorem eval_moduimm (line 574) and Theorem eval_modsimm (line 694).
- Torbjörn Granlund and Peter L. Montgomery, 'Division by Invariant Integers using Multiplication', Proceedings of the ACM SIGPLAN 1994 Conference on Programming Language Design and Implementation (PLDI '94), pp. 61-72, 1994, DOI 10.1145/178243.178249 (also printed in SIGPLAN Notices 29(6):61-72, DOI 10.1145/773473.178249). Theorem 5.1: if d != 0 and 0 < m*|d| - 2^(N+l-1) <= 2^l, then for -2^(N-1) <= n <= 2^(N-1) - 1 and q0 = floor(m*n/2^(N+l-1)), TRUNC(n/d) = q0 for n >= 0, d > 0 and 1 + q0 for n < 0, d > 0 (with sign changes for d < 0). Section 5 also warns: 'When d < 0, avoid rewriting the quotient as TRUNC((-n)/|d|), which fails for n = -2^(N-1).'
- Source records, with verbatim quotations where this card relies on a stated theorem or rule: [Lean-core], [CompCert], [GM94-T5.1] (Evidence, *Primary sources*).

**Design question.** Is the signed remainder obtained from the corrected quotient the truncated remainder, with the dividend's sign?

### 20. `directRem_eq_mod_of_sandwich`

**Kind:** theorem. **Tier:** T0: Lemire-Kaser-Kurz Theorem 1, here without their d < 2^N hypothesis. **Depth:** substantive.

Basis: execution (Lean kernel check)

**Lean statement.**

```lean
-- lean/Toy/MagicDiv/Statements.lean:482-484
theorem directRem_eq_mod_of_sandwich (N ℓ d m : Nat)
    (hlo : 2 ^ (N + ℓ) ≤ m * d) (hhi : m * d ≤ 2 ^ (N + ℓ) + 2 ^ ℓ) :
    ∀ x, x < 2 ^ N → directRem (N + ℓ) d m x = x % d := by
```

Unfolded rendering of `directRem_eq_mod_of_sandwich` (a Lean term that elaborates in the statement's context and is definitionally equal to it):

```lean
∀ (N ℓ d m : Nat), 2 ^ (N + ℓ) ≤ m * d → m * d ≤ 2 ^ (N + ℓ) + 2 ^ ℓ →
  ∀ x : Nat, x < 2 ^ N → (((x * m) % 2 ^ (N + ℓ)) * d) >>> (N + ℓ) = x % d
```

**Plain claim.** For all N, l, d, m with 2^(N+l) <= m*d <= 2^(N+l) + 2^l: the remainder can be computed without the quotient, (((x*m) mod 2^(N+l)) * d) >>> (N+l) = x mod d, for every x < 2^N (no d < 2^N hypothesis).

**Hypothesis ledger.**

- `hlo: 2^(N+l) <= m*d` — As for mulShiftCorrect_of_sandwich. *Tightness:* tight; counterexample `ce_directRem_hlo`; witness class: an instance with N = 2, l = 0, d = 2, m = 1 (fails at x = 1).
- `hhi: m*d <= 2^(N+l) + 2^l` — Bounds the overshoot so that x*(m*d - 2^(N+l)) < 2^(N+l). *Tightness:* tight; counterexample `ce_directRem_hhi`; witness class: an instance with N = 8, l = 2, d = 7, m = 147 (fails at x = 205).
- `input range x < 2^N` — As for mulShiftCorrect_of_sandwich. *Tightness:* tight; counterexample `ce_directRem_input_range`; witness class: an instance with N = 1, l = 0, d = 3, m = 1 (fails at x = 2).

**Non-vacuity witness.** N = 32, l = 3, d = 7, m = 4908534053, x = 200. (`nv_sandwich_u32_div7`, which proves that all hypotheses hold for this instance.)

**Non-claims.** Listed under Boundaries, *Non-claims of result 20*.

**Prior art.**

- Daniel Lemire, Owen Kaser, Nathan Kurz, 'Faster Remainder by Direct Computation: Applications to Compilers and Software Libraries', Software: Practice and Experience 49(6):953-970, 2019, DOI 10.1002/spe.2689; arXiv:1902.01961v3. Theorem 1: for d in [1, 2^N) and 2^(N+L) <= c*d <= 2^(N+L) + 2^L, n mod d = (((c*n) mod 2^(N+L))*d) div 2^(N+L) for all n in [0, 2^N).
- Daniel Lemire, Colin Bartlett, Owen Kaser, 'Integer Division by Constants: Optimal Bounds', Heliyon 7(6):e07442, 2021, DOI 10.1016/j.heliyon.2021.e07442; arXiv:2012.12369v3. Theorem 2 (d > 0, numerators n in [0, N] with N >= d): floor(n/d) = floor(c*n/m) AND remainder(n, d) = floor(remainder(c*n, m)*d/m) for all such n iff 1/d <= c/m < (1 + 1/N)/d; it is an exact characterization of simultaneous quotient and direct-remainder correctness. Remark 2 compares it with the sufficient bound of Lemire, Kaser and Kurz (Theorem 1) and shows the two can differ (N = 10, d = 5, m = 2^5) but coincide when m = N + 1 >= 3.
- Daniel Lemire, Owen Kaser, Nathan Kurz, 'Faster Remainder by Direct Computation: Applications to Compilers and Software Libraries', Software: Practice and Experience 49(6):953-970, 2019, DOI 10.1002/spe.2689; arXiv:1902.01961v3. Theorem 2 (signed direct remainder): for d in [1, 2^(N-1)) and 2^(N-1+L) < c*d < 2^(N-1+L) + 2^L (both strict), with mu = floor((lsb_(N-1+L)(c*n)*d)/2^(N-1+L)), n mod d = mu for n in [0, 2^(N-1)) and n mod d = mu - d + 1 for n in [-2^(N-1), 0), where mod is the truncating remainder. (not formalized here).
- Source records, with verbatim quotations where this card relies on a stated theorem or rule: [LKK19-T1], [LBK21-T2], [LBK21-R2], [LKK19-T2] (Evidence, *Primary sources*).

**Design question.** Can the remainder be computed directly from the low bits of x*m, and which multipliers allow it?

### Supporting kernel-evaluated instances (not result cards)

These bounded theorems in `lean/Toy/MagicDiv/Bounded.lean` are special cases of the general results above, kept as independent kernel evaluations (`decide +kernel` over the stated finite ranges). Their hypotheses are listed one by one.

#### `fixupQuot_unsignedMagic_u8`

```lean
-- lean/Toy/MagicDiv/Bounded.lean:208-210
theorem fixupQuot_unsignedMagic_u8 :
    ∀ d, 2 ≤ d → d < 2 ^ 8 → ∀ x, x < 2 ^ 8 →
      fixupQuot 8 (unsignedMagic 8 d - 2 ^ 8) (clog2 d) x = x / d := by
```

Unfolded rendering of `fixupQuot_unsignedMagic_u8` (a Lean term that elaborates in the statement's context and is definitionally equal to it):

```lean
∀ d : Nat, 2 ≤ d → d < 2 ^ 8 →
  let ℓ : Nat := clog2 d;
  let m' : Nat := (2 ^ (8 + ℓ) + d - 1) / d - 2 ^ 8;
  ∀ x : Nat, x < 2 ^ 8 →
    (let t : Nat := (x * m') >>> 8; (t + ((x - t) >>> 1)) >>> (ℓ - 1)) = x / d
```

- Special case of result 6 (N = 8, d < 2^8). Depth: shallow (bounded evaluation over 2 ≤ d ≤ 255 and x < 256). Non-vacuity: `nv_evaluated_instances`.
- Hypothesis ledger:
  - `2 ≤ d` — tight: counterexample `ce_fixupQuot_unsignedMagic_u8_d_one_canonical`; witness class: an instance with d = 1 (fails at x = 1).
  - `d < 2^8` — harmless: `fixupQuot_unsignedMagic_correct` proves the conclusion for every d ≥ 2.
  - `x < 2^8` — tight: counterexample `ce_fixupQuot_unsignedMagic_u8_x_range`; witness class: an instance with d = 15, x = 299 (the fixup gives 20, not 19).

#### `fixupQuot_unsignedMagic_u16_div7`

```lean
-- lean/Toy/MagicDiv/Bounded.lean:224-225
theorem fixupQuot_unsignedMagic_u16_div7 :
    ∀ x, x < 2 ^ 16 → fixupQuot 16 (unsignedMagic 16 7 - 2 ^ 16) (clog2 7) x = x / 7 := by
```

Unfolded rendering of `fixupQuot_unsignedMagic_u16_div7` (a Lean term that elaborates in the statement's context and is definitionally equal to it):

```lean
let ℓ : Nat := clog2 7;
let m' : Nat := (2 ^ (16 + ℓ) + 7 - 1) / 7 - 2 ^ 16;
∀ x : Nat, x < 2 ^ 16 →
  (let t : Nat := (x * m') >>> 16; (t + ((x - t) >>> 1)) >>> (ℓ - 1)) = x / 7
```

- Special case of result 6 (N = 16, d = 7). Depth: shallow (bounded evaluation over x < 2^16). Non-vacuity: `nv_evaluated_instances`.
- Hypothesis ledger:
  - `x < 2^16` — tight: counterexample `ce_fixupQuot_unsignedMagic_u16_div7_x_range`; witness class: an instance with x = 104859 (the fixup gives 14980, not 14979).

#### `mulShiftCorrect_iff_exactCriterion_u8`

```lean
-- lean/Toy/MagicDiv/Bounded.lean:179-181
theorem mulShiftCorrect_iff_exactCriterion_u8 :
    ∀ d, 0 < d → d < 2 ^ 8 → ∀ s, s ≤ 16 → ∀ m,
      MulShiftCorrect 8 d m s ↔ ExactCriterion 8 d m s := by
```

Unfolded rendering of `mulShiftCorrect_iff_exactCriterion_u8` (a Lean term that elaborates in the statement's context and is definitionally equal to it):

```lean
∀ d : Nat, 0 < d → d < 2 ^ 8 → ∀ s : Nat, s ≤ 16 → ∀ m : Nat,
  let nc : Nat := 2 ^ 8 - 2 ^ 8 % d - 1;
  ((∀ x : Nat, x < 2 ^ 8 → (x * m) >>> s = x / d) ↔ (2 ^ s ≤ m * d ∧ nc * (m * d - 2 ^ s) < 2 ^ s))
```

- Special case of result 8 (N = 8, s ≤ 16). Depth: shallow (bounded evaluation over 1 ≤ d ≤ 255 and s ≤ 16; every multiplier m is covered by proved monotonicity lemmas). Non-vacuity: `nv_evaluated_instances`.
- Hypothesis ledger:
  - `0 < d` — tight: counterexample `ce_exactCriterion_u8_d_zero`; witness class: an instance with d = 0, m = 0, s = 0.
  - `d < 2^8` — tight: counterexample `ce_exactCriterion_u8_d_256`; witness class: an instance with d = 256, m = 0, s = 0.
  - `s ≤ 16` — harmless: `mulShiftCorrect_iff_exactCriterion` proves the equivalence for every s.

### Modeling bridge to compilers and instruction sets

Basis: derived (modeling bridge). The items below connect the Lean definitions to real code, documentation and instruction sets. They rest on source inspection, documentation and the reasoning stated with each item; none is kernel-checked, and none is used by any proof.

1. **Unsigned magic-number search (LLVM).** In LLVM's `llvm/lib/Support/DivisionByConstantInfo.cpp` at commit `c312bf3fa94430185410c06c502abd9953f838fa`, `UnsignedDivisionByConstantInfo::get` keeps `Magic = Q2 + 1 = ⌈2^P/D⌉` and `Delta = D − 1 − ((2^P − 1) mod D) = Magic·D − 2^P`, computes `NC`, "the largest dividend such that NC.urem(D) == D-1", and loops while `Q1 < Delta || (Q1 == Delta && R1 == 0)` with `Q1 = ⌊2^P/NC⌋`, `R1 = 2^P mod NC`, i.e. while `2^P ≤ NC·Delta`. It therefore stops at the first `P` with `NC·(Magic·D − 2^P) < 2^P`, the upper half of `ExactCriterion` for the ceiling multiplier, whose lower half holds automatically (`le_ceilDiv_mul`). `NC` is computed against the dividend range implied by `LeadingZeros`, which corresponds to a smaller `N` in this model. Reasoning: source inspection plus the algebra above; the code itself is not modelled.
2. **Fixup encoding (LLVM, Granlund–Montgomery).** In the same function, `IsAdd` marks magic numbers that need an extra bit and `PostShift` is then reduced by one; this matches `fixupQuot` with `ℓ − 1` as the final shift (Granlund–Montgomery Figure 4.1, [GM94-F4.1]). That the fixup's intermediates fit in `N` bits for `x, m' < 2^N` follows from `t ≤ x` (proved inside `fixupQuot_eq_wide`) and `(x − t) >>> 1 ≤ x − t`; it is not proved as a separate statement. Not verified against generated code.
3. **Signed sequence.** Granlund–Montgomery Figure 5.1 ([GM94-F5.1]) computes `⌊m·n/2^(N+ℓ−1)⌋` as `SRA(n + MULSH(m − 2^N, n), ℓ − 1)` and subtracts `XSIGN(n)`; `sdivMagic` models the value of that computation with exact arithmetic, not the encoding. Multipliers produced by `signedMagic` exceed `2^(N−1)` (`two_pow_pred_lt_signedMagic`), which is why the encoding uses `m − 2^N`. LLVM's `SignedDivisionByConstantInfo::get` (same commit) implements Warren's search with `ANC`; re-running its loop for width 8 and divisors 2..127 outside Lean gives pairs outside the signed sandwich for 28 of the 126 divisors (e.g. `D = 35`: `Magic = 59`, total shift 11), all correct by exhaustive evaluation outside Lean; of these, the `D = 35` pair is kernel-checked (`signed_sandwich_not_necessary_i8_div35`) and the other 27 are not.
4. **Shift counts at or above the width.** C ([C11], N1570 §6.5.7p3) and C++ ([C++], [expr.shift]/1): a right operand "greater than or equal to the width of the promoted left operand" gives undefined behavior. LLVM IR ([LLVM], LangRef `lshr`/`ashr`): such a shift "returns a poison value". Rust ([Rust]): `>>` by at least the bit width counts as overflow and panics when compiled in debug mode; `wrapping_shr` masks the amount. x86 `SHR`/`SAR` ([Intel]): "The count is masked to 5 bits (or 6 bits with a 64-bit operand)", so 32- and 64-bit shifts reduce the count modulo the width, while 8- and 16-bit shifts mask it to 5 bits. AArch64 `LSRV`/`ASRV` ([Arm], unofficial mirror): the count is the second register "modulo the register size in bits". RISC-V `SRL`/`SRA` ([RISC-V]): the low 5 bits (RV32I) or 6 bits (RV64I) of `rs2`. Reasoning: on those 32- and 64-bit shifts the count is reduced modulo the width, which is what `biasSumMasked`/`biasDivMasked`/`biasDivBVMasked` model. LLVM IR and Rust do not promote the shifted operand: a count equal to the width `N` is poison in LLVM IR and an overflow in Rust (a panic in debug builds) at every width. C and C++ first promote both operands, so a count equal to `N` is undefined behavior when `N` is at least the width of the promoted left operand (for example `N = 32` or `64` when `int` is 32 bits) but is defined for narrower types: a `uint8_t` operand is promoted to `int`, and a right shift by 8 then gives 0. Hence `biasDiv`'s `k = 0` case (logical shift count `N`) and `fixupQuot`'s final shift `clog2 d − 1 = N` (for `2^N < d ≤ 2^(N+1)`) cannot be written as a single shift by `N` in LLVM IR or Rust at any width, nor in C or C++ for types at least as wide as the promoted operand; the 32- and 64-bit register shifts listed above compute a shift by 0 instead. x86 8- and 16-bit shifts (count masked to 5 bits, not reduced modulo the width) are not covered by this reading. Basis: documentation; no compiler output was examined.
5. **Overflow of signed division.** Core `BitVec.sdiv` returns `-2^(N-1)` for `(-2^(N-1)) / (-1)` (`bitvec_sdiv_intMin_negOne_wraps` checks this at `N = 8`; core `BitVec.intMin_sdiv_neg_one` states it for every width); Granlund and Montgomery state that their Figure 5.1 also returns `−2^(N−1)` ([GM94-OVF]). The behavior of particular languages or instruction sets in this case was not examined.
6. **CompCert.** `backend/SelectDiv.vp` (commit `5e4ef44c57b22cdc2e1893770843fd693a5f82e1`) requires unsigned multipliers to be below `2^32` (so it does not use the add-and-shift fixup) and validates signed and unsigned candidates against the Granlund–Montgomery sandwich bounds; `lib/Integers.v` proves the wrapping power-of-two sequence for every word size (`shrx_shr_2`, for `y < zwordsize − 1`). Basis: source inspection.

### Supporting declarations

Kernel-checked supporting facts and definitions cited by name in the definitions, cards, ledgers and boundaries. Each statement is quoted verbatim (proof omitted; definitions with their bodies). All are fully proved and depend on no axioms beyond `propext`, `Classical.choice` and `Quot.sound` (Evidence). The counterexamples, non-vacuity witnesses and positive control that the cards reference are quoted in the next subsection.

#### `lean/Toy/MagicDiv/Lemmas.lean`

```lean
-- lean/Toy/MagicDiv/Lemmas.lean:17
theorem pos_of_two_pow_le_mul {K m d : Nat} (h : 2 ^ K ≤ m * d) : 0 < d := by
```

```lean
-- lean/Toy/MagicDiv/Lemmas.lean:24
theorem le_ceilDiv_mul (a d : Nat) (hd : 0 < d) : a ≤ ceilDiv a d * d := by
```

```lean
-- lean/Toy/MagicDiv/Lemmas.lean:40
theorem ceilDiv_le_of_le_mul {a d c : Nat} (hd : 0 < d) (h : a ≤ c * d) : ceilDiv a d ≤ c := by
```

```lean
-- lean/Toy/MagicDiv/Lemmas.lean:64
theorem one_le_clog2 {d : Nat} (hd : 2 ≤ d) : 1 ≤ clog2 d := by
```

```lean
-- lean/Toy/MagicDiv/Lemmas.lean:78
theorem succ_le_clog2_of_two_pow_lt {N d : Nat} (hdN : 2 ^ N < d) : N + 1 ≤ clog2 d := by
```

```lean
-- lean/Toy/MagicDiv/Lemmas.lean:114-115
theorem signedRange_iff_of_pos {N : Nat} (hN : 1 ≤ N) (x : Int) :
    SignedRange N x ↔ -(2 : Int) ^ (N - 1) ≤ x ∧ x < (2 : Int) ^ (N - 1) := by
```

```lean
-- lean/Toy/MagicDiv/Lemmas.lean:124
theorem signedRange_zero_iff (x : Int) : SignedRange 0 x ↔ x = 0 := by
```

```lean
-- lean/Toy/MagicDiv/Lemmas.lean:199-200
theorem signedRange_iff_toInt_ofInt (N : Nat) (x : Int) :
    SignedRange N x ↔ (BitVec.ofInt N x).toInt = x := by
```

#### `lean/Toy/MagicDiv/Examples.lean`

```lean
-- lean/Toy/MagicDiv/Examples.lean:16-17
theorem ceilDiv_pos_examples :
    ceilDiv 7 2 = 4 ∧ ceilDiv 8 2 = 4 ∧ ceilDiv (2 ^ 35) 7 = 4908534053 := by decide
```

```lean
-- lean/Toy/MagicDiv/Examples.lean:20
theorem ceilDiv_neg_example : ceilDiv 7 2 ≠ 7 / 2 := by decide
```

```lean
-- lean/Toy/MagicDiv/Examples.lean:26-28
theorem clog2_pos_examples :
    clog2 1 = 0 ∧ clog2 2 = 1 ∧ clog2 7 = 3 ∧ clog2 8 = 3 ∧ clog2 9 = 4 ∧
      7 ≤ 2 ^ clog2 7 ∧ ¬ 7 ≤ 2 ^ (clog2 7 - 1) := by decide
```

```lean
-- lean/Toy/MagicDiv/Examples.lean:32
theorem clog2_neg_examples : clog2 7 ≠ Nat.log2 7 ∧ clog2 8 ≠ Nat.log2 8 + 1 := by decide
```

```lean
-- lean/Toy/MagicDiv/Examples.lean:38-39
theorem mulShiftCorrect_pos_examples :
    MulShiftCorrect 8 3 171 9 ∧ MulShiftCorrect 8 7 293 11 := by decide +kernel
```

```lean
-- lean/Toy/MagicDiv/Examples.lean:44-45
theorem mulShiftCorrect_neg_examples :
    ¬ MulShiftCorrect 8 3 85 8 ∧ ¬ MulShiftCorrect 8 7 147 10 := by
```

```lean
-- lean/Toy/MagicDiv/Examples.lean:53-55
theorem lastFullBlockEnd_pos_example :
    lastFullBlockEnd 8 7 = 251 ∧ 251 % 7 = 6 ∧
      ∀ y, y < 2 ^ 8 → y % 7 = 6 → y ≤ lastFullBlockEnd 8 7 := by decide +kernel
```

```lean
-- lean/Toy/MagicDiv/Examples.lean:58
theorem lastFullBlockEnd_neg_example : lastFullBlockEnd 8 7 ≠ 2 ^ 8 - 1 := by decide
```

```lean
-- lean/Toy/MagicDiv/Examples.lean:64-65
theorem exactCriterion_pos_examples :
    ExactCriterion 8 3 171 9 ∧ ExactCriterion 8 7 293 11 := by decide
```

```lean
-- lean/Toy/MagicDiv/Examples.lean:69-70
theorem exactCriterion_neg_examples :
    ¬ ExactCriterion 8 7 147 10 ∧ ¬ ExactCriterion 8 3 85 8 := by decide
```

```lean
-- lean/Toy/MagicDiv/Examples.lean:77-79
theorem magic_pos_examples :
    unsignedMagic 32 7 = 2 ^ 32 + 613566757 ∧ unsignedMagic 8 7 = 293 ∧
      singleWordShift 8 3 = 9 ∧ singleWordMagic 8 3 = 171 := by decide
```

```lean
-- lean/Toy/MagicDiv/Examples.lean:83-84
theorem magic_neg_examples :
    ¬ unsignedMagic 32 7 < 2 ^ 32 ∧ singleWordMagic 8 7 ≠ unsignedMagic 8 7 := by decide
```

```lean
-- lean/Toy/MagicDiv/Examples.lean:88
theorem singleWordShift_neg_example : singleWordShift 8 8 ≠ 8 + Nat.log2 8 := by decide
```

```lean
-- lean/Toy/MagicDiv/Examples.lean:94-95
theorem fixupQuot_pos_examples :
    fixupQuot 8 37 3 200 = 200 / 7 ∧ fixupQuot 8 37 3 255 = 255 / 7 := by decide
```

```lean
-- lean/Toy/MagicDiv/Examples.lean:99-100
theorem fixupQuot_neg_example :
    fixupQuot 8 37 3 255 ≠ ((255 + (255 * 37) >>> 8) % 2 ^ 8) >>> 3 := by decide
```

```lean
-- lean/Toy/MagicDiv/Examples.lean:105
theorem signedRange_pos_examples : SignedRange 8 (-128) ∧ SignedRange 8 127 := by decide
```

```lean
-- lean/Toy/MagicDiv/Examples.lean:108
theorem signedRange_neg_examples : ¬ SignedRange 8 128 ∧ ¬ SignedRange 8 (-129) := by decide
```

```lean
-- lean/Toy/MagicDiv/Examples.lean:112
theorem signedRange_zero_examples : SignedRange 0 0 ∧ ¬ SignedRange 0 (-1) := by decide
```

```lean
-- lean/Toy/MagicDiv/Examples.lean:125-126
theorem sdivMagic_pos_examples :
    sdivMagic 171 9 (-7) = Int.tdiv (-7) 3 ∧ sdivMagic 171 9 7 = Int.tdiv 7 3 := by decide
```

```lean
-- lean/Toy/MagicDiv/Examples.lean:130-132
theorem sdivMagic_neg_examples :
    sdivMagic 171 9 (-7) ≠ Int.fdiv (-7) 3 ∧
      sdivMagicUncorrected 171 9 (-7) ≠ Int.tdiv (-7) 3 := by decide
```

```lean
-- lean/Toy/MagicDiv/Examples.lean:136-138
theorem sdivMagicUncorrected_pos_examples :
    sdivMagicUncorrected 171 9 7 = Int.tdiv 7 3 ∧
      sdivMagicUncorrected 171 9 (-7) = Int.tdiv (-7) 3 - 1 := by decide
```

```lean
-- lean/Toy/MagicDiv/Examples.lean:144-145
theorem sremMagic_pos_examples :
    sremMagic 3 171 9 (-7) = Int.tmod (-7) 3 ∧ sremMagic 3 171 9 7 = Int.tmod 7 3 := by decide
```

```lean
-- lean/Toy/MagicDiv/Examples.lean:149
theorem sremMagic_neg_example : sremMagic 3 171 9 (-7) ≠ Int.emod (-7) 3 := by decide
```

```lean
-- lean/Toy/MagicDiv/Examples.lean:154-155
theorem signedMagic_pos_examples :
    signedMagic 8 3 = 171 ∧ signedMagic 32 7 = 2454267027 := by decide
```

```lean
-- lean/Toy/MagicDiv/Examples.lean:159
theorem signedMagic_neg_example : signedMagic 8 4 ≠ 2 ^ 9 / 4 := by decide
```

```lean
-- lean/Toy/MagicDiv/Examples.lean:165
theorem lsrN_pos_examples : lsrN 8 (-1) 5 = 7 ∧ lsrN 8 0 5 = 0 := by decide
```

```lean
-- lean/Toy/MagicDiv/Examples.lean:168
theorem lsrN_neg_example : lsrN 8 (-1) 5 ≠ (-1 : Int) >>> 5 := by decide
```

```lean
-- lean/Toy/MagicDiv/Examples.lean:174-176
theorem biasDiv_pos_examples :
    biasSum 8 2 (-7) = -4 ∧ biasDiv 8 2 (-7) = Int.tdiv (-7) 4 ∧
      biasDiv 8 2 7 = Int.tdiv 7 4 := by decide
```

```lean
-- lean/Toy/MagicDiv/Examples.lean:179
theorem biasDiv_neg_example : biasDiv 8 2 (-7) ≠ (-7 : Int) >>> 2 := by decide
```

```lean
-- lean/Toy/MagicDiv/Examples.lean:183
theorem biasSum_neg_example : biasSum 8 2 7 ≠ 7 + (2 ^ 2 - 1) := by decide
```

```lean
-- lean/Toy/MagicDiv/Examples.lean:189-191
theorem biasDivMasked_pos_examples :
    biasSumMasked 8 2 (-7) = -4 ∧ biasDivMasked 8 2 (-7) = Int.tdiv (-7) 4 ∧
      (biasDivBVMasked 2 (BitVec.ofInt 8 (-7))).toInt = -1 := by decide
```

```lean
-- lean/Toy/MagicDiv/Examples.lean:196-198
theorem biasDivMasked_neg_examples :
    biasDivMasked 8 0 (-1) = 254 ∧
      (biasDivBVMasked 0 (BitVec.ofInt 8 (-1))).toInt = -2 := by decide
```

```lean
-- lean/Toy/MagicDiv/Examples.lean:203
theorem biasDivBV_pos_example : (biasDivBV 2 (BitVec.ofInt 8 (-7))).toInt = -1 := by decide
```

```lean
-- lean/Toy/MagicDiv/Examples.lean:207
theorem biasDivBV_neg_example : (biasDivBV 8 (BitVec.ofInt 8 (-1))).toInt ≠ 0 := by decide
```

```lean
-- lean/Toy/MagicDiv/Examples.lean:212
theorem directRem_pos_example : directRem 11 7 293 200 = 200 % 7 := by decide
```

```lean
-- lean/Toy/MagicDiv/Examples.lean:215
theorem directRem_neg_example : directRem 11 7 292 200 ≠ 200 % 7 := by decide
```

#### `lean/Toy/MagicDiv/Statements.lean`

```lean
-- lean/Toy/MagicDiv/Statements.lean:129-130
theorem two_pow_le_mul_of_correct {N d m s : Nat} (hd : 0 < d) (hdN : d < 2 ^ N)
    (h : MulShiftCorrect N d m s) : 2 ^ s ≤ m * d := by
```

```lean
-- lean/Toy/MagicDiv/Statements.lean:522-524
theorem sandwich_iff_directRem_bound (N ℓ d m : Nat) (hℓ : ℓ < N) :
    (2 ^ (N + ℓ) ≤ m * d ∧ m * d ≤ 2 ^ (N + ℓ) + 2 ^ ℓ) ↔
      (2 ^ (N + ℓ) ≤ m * d ∧ (2 ^ N - 1) * (m * d - 2 ^ (N + ℓ)) < 2 ^ (N + ℓ)) := by
```

```lean
-- lean/Toy/MagicDiv/Statements.lean:632-633
theorem sdivMagicUncorrected_eq_sdivMagic_sub_one (m k : Nat) (x : Int) (hx : x < 0) :
    sdivMagicUncorrected m k x = sdivMagic m k x - 1 := by
```

```lean
-- lean/Toy/MagicDiv/Statements.lean:833-835
theorem mulShift_rem_eq_mod_of_sandwich (N ℓ d m : Nat)
    (hlo : 2 ^ (N + ℓ) ≤ m * d) (hhi : m * d ≤ 2 ^ (N + ℓ) + 2 ^ ℓ) :
    ∀ x, x < 2 ^ N → x - d * ((x * m) >>> (N + ℓ)) = x % d :=
```

```lean
-- lean/Toy/MagicDiv/Statements.lean:840-841
theorem fixupQuot_shift_lt_width (N d : Nat) (hd : 2 ≤ d) (hdN : d ≤ 2 ^ N) :
    clog2 d - 1 < N := by
```

```lean
-- lean/Toy/MagicDiv/Statements.lean:848-849
theorem fixupQuot_shift_eq_width (N d : Nat) (hd : 2 ^ N < d) (hdN : d ≤ 2 ^ (N + 1)) :
    clog2 d - 1 = N := by
```

```lean
-- lean/Toy/MagicDiv/Statements.lean:856-857
theorem not_mulShiftCorrect_div_one_of_width_le (N m s : Nat) (hN : 1 ≤ N) (hm : m < 2 ^ N)
    (hs : N ≤ s) : ¬ MulShiftCorrect N 1 m s := by
```

```lean
-- lean/Toy/MagicDiv/Statements.lean:875
theorem two_pow_pred_lt_signedMagic (N d : Nat) (hd : 0 < d) : 2 ^ (N - 1) < signedMagic N d := by
```

```lean
-- lean/Toy/MagicDiv/Statements.lean:886
theorem unsignedMagic_zero_right (N : Nat) : unsignedMagic N 0 = 0 := by
```

```lean
-- lean/Toy/MagicDiv/Statements.lean:891
theorem unsignedMagic_two_pow (N k : Nat) : unsignedMagic N (2 ^ k) = 2 ^ N := by
```

```lean
-- lean/Toy/MagicDiv/Statements.lean:902-903
theorem unsignedMagic_two_pow_succ_add_one (N : Nat) :
    unsignedMagic N (2 ^ (N + 1) + 1) = 2 ^ (N + 1) := by
```

```lean
-- lean/Toy/MagicDiv/Statements.lean:928-929
theorem unsignedMagic_lt_two_pow_succ_converse_fails (N k : Nat) (hk : N + 2 ≤ k) :
    2 ^ (N + 1) < 2 ^ k ∧ unsignedMagic N (2 ^ k) < 2 ^ (N + 1) := by
```

```lean
-- lean/Toy/MagicDiv/Statements.lean:937-940
theorem unsignedMagic_lt_two_pow_succ_above_examples :
    (2 ^ (1 + 1) < 6 ∧ unsignedMagic 1 6 < 2 ^ (1 + 1)) ∧
    (2 ^ (8 + 1) < 768 ∧ unsignedMagic 8 768 < 2 ^ (8 + 1)) ∧
    (2 ^ (32 + 1) < 3 * 2 ^ 32 ∧ unsignedMagic 32 (3 * 2 ^ 32) < 2 ^ (32 + 1)) := by
```

```lean
-- lean/Toy/MagicDiv/Statements.lean:946
theorem singleWordMagic_zero_right (N : Nat) : singleWordMagic N 0 = 0 := by
```

```lean
-- lean/Toy/MagicDiv/Statements.lean:951
theorem singleWordShift_one (N : Nat) : singleWordShift N 1 = N - 1 := by
```

```lean
-- lean/Toy/MagicDiv/Statements.lean:956-958
theorem two_pow_pred_lt_singleWordMagic (N d : Nat)
    (hd : 1 ≤ d) (hdN : d < 2 ^ N) (hnpow : ∀ k : Nat, d ≠ 2 ^ k) :
    2 ^ (N - 1) < singleWordMagic N d := by
```

```lean
-- lean/Toy/MagicDiv/Statements.lean:986-987
theorem fixupQuot_shift_lt_width_iff (N d : Nat) (hd : 2 ≤ d) :
    clog2 d - 1 < N ↔ d ≤ 2 ^ N := by
```

#### `lean/Toy/MagicDiv/Bounded.lean`

The Boolean checkers used by the kernel evaluations, and their adequacy lemmas:

```lean
-- lean/Toy/MagicDiv/Bounded.lean:31-32
def allBelow (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec true (fun i acc => f i && acc) n
```

```lean
-- lean/Toy/MagicDiv/Bounded.lean:34-35
theorem allBelow_iff (n : Nat) (f : Nat → Bool) :
    allBelow n f = true ↔ ∀ x, x < n → f x = true := by
```

```lean
-- lean/Toy/MagicDiv/Bounded.lean:50-51
def correctB (N d m s : Nat) : Bool :=
  allBelow (2 ^ N) (fun x => (x * m) >>> s == x / d)
```

```lean
-- lean/Toy/MagicDiv/Bounded.lean:53
theorem correctB_iff (N d m s : Nat) : correctB N d m s = true ↔ MulShiftCorrect N d m s := by
```

```lean
-- lean/Toy/MagicDiv/Bounded.lean:78-79
theorem not_mulShiftCorrect_of_mul_lt {N d m s : Nat} (hd : 0 < d) (hdN : d < 2 ^ N)
    (h : m * d < 2 ^ s) : ¬ MulShiftCorrect N d m s := by
```

```lean
-- lean/Toy/MagicDiv/Bounded.lean:88-89
theorem not_mulShiftCorrect_of_gt_at {N d m m' s x : Nat} (hx : x < 2 ^ N)
    (h : x / d < (x * m) >>> s) (hm : m ≤ m') : ¬ MulShiftCorrect N d m' s := by
```

```lean
-- lean/Toy/MagicDiv/Bounded.lean:325-326
theorem robison_multiply_add_u8_div7 :
    146 < 2 ^ 8 ∧ ∀ x, x < 2 ^ 8 → (x * 146 + 146) >>> 10 = x / 7 := by
```

```lean
-- lean/Toy/MagicDiv/Bounded.lean:335-336
theorem mulShift_u8_div7_below_209 :
    147 < 2 ^ 8 ∧ (∀ x, x < 209 → (x * 147) >>> 10 = x / 7) ∧ (209 * 147) >>> 10 ≠ 209 / 7 := by
```

```lean
-- lean/Toy/MagicDiv/Bounded.lean:346-347
def directRemB (N F d m : Nat) : Bool :=
  allBelow (2 ^ N) (fun x => directRem F d m x == x % d)
```

```lean
-- lean/Toy/MagicDiv/Bounded.lean:352-354
theorem count_no_single_word_u8 :
    (List.range 255).countP
      (fun i => !correctB 8 (i + 1) (singleWordMagic 8 (i + 1)) (singleWordShift 8 (i + 1))) = 55 := by
```

```lean
-- lean/Toy/MagicDiv/Bounded.lean:359-361
theorem count_single_word_u8 :
    (List.range 255).countP
      (fun i => correctB 8 (i + 1) (singleWordMagic 8 (i + 1)) (singleWordShift 8 (i + 1))) = 200 := by
```

```lean
-- lean/Toy/MagicDiv/Bounded.lean:367-370
theorem count_single_word_u8_directRem_fails :
    (List.range 255).countP
      (fun i => correctB 8 (i + 1) (singleWordMagic 8 (i + 1)) (singleWordShift 8 (i + 1)) &&
        !directRemB 8 (singleWordShift 8 (i + 1)) (i + 1) (singleWordMagic 8 (i + 1))) = 42 := by
```

How the three counts are read. In each, `i` ranges over `0 ≤ i < 255` and stands for the divisor `d = i + 1`, so `d` ranges over `1 ≤ d ≤ 255`; write `m* = singleWordMagic 8 d` and `s* = singleWordShift 8 d`. `count_no_single_word_u8` counts the `d` with `correctB 8 d m* s* = false`, which by `correctB_iff` are the `d` for which `MulShiftCorrect 8 d m* s*` fails, and by `single_word_multiplier_exists_iff` the `d` for which no multiplier `m < 2^8` is correct at any shift. `count_single_word_u8` counts the `d` with `correctB 8 d m* s* = true`, i.e. with `MulShiftCorrect 8 d m* s*`. `count_single_word_u8_directRem_fails` counts the `d` with `MulShiftCorrect 8 d m* s*` and `directRemB 8 s* d m* = false`; by `directRemB_iff` (Companions, below) the latter means that `directRem s* d m* x ≠ x % d` for some `x < 2^8`. Note the argument orders: `directRemB N F d m` takes the input width `N` first, while `directRem F d m x` takes the shift `F` first and the input `x` last.

#### `lean/Toy/MagicDiv/Counterexamples.lean`

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:40-41
theorem sandwich_not_necessary_u8_div35 :
    2 ^ (8 + 5) + 2 ^ 5 < 235 * 35 ∧ MulShiftCorrect 8 35 235 (8 + 5) := by decide +kernel
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:57-59
theorem pc_single_word_shift_fits :
    singleWordMagic 8 3 < 2 ^ 8 ∧
      MulShiftCorrect 8 3 (singleWordMagic 8 3) (singleWordShift 8 3) := by
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:92-93
theorem singleWordShift_not_minimal_u8_div9 :
    singleWordShift 8 9 = 11 ∧ singleWordMagic 8 9 = 228 ∧ MulShiftCorrect 8 9 57 9 := by
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:99-100
theorem mulShiftCorrect_u32_div641_shift32 :
    singleWordShift 32 641 = 41 ∧ 6700417 < 2 ^ 32 ∧ MulShiftCorrect 32 641 6700417 32 :=
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:154
theorem fixupQuot_shift_width_u8_d300 : 2 ^ 8 < 300 ∧ 300 ≤ 2 ^ 9 ∧ clog2 300 - 1 = 8 := by
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:254-260
theorem uncorrected_ne_fdiv_at_negative_multiple :
    (2 ^ (8 - 1 + 2) < 171 * 3 ∧ 171 * 3 ≤ 2 ^ (8 - 1 + 2) + 2 ^ 2) ∧
      SignedRange 8 (-3) ∧
      sdivMagicUncorrected 171 (8 - 1 + 2) (-3) = -2 ∧
      Int.fdiv (-3) 3 = -1 ∧ Int.tdiv (-3) 3 = -1 ∧
      sdivMagicUncorrected 171 (8 - 1 + 2) (-1) = Int.fdiv (-1) 3 ∧
      sdivMagicUncorrected 171 (8 - 1 + 2) (-1) ≠ Int.tdiv (-1) 3 := by decide
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:277-279
theorem bitvec_sdiv_intMin_negOne_wraps :
    BitVec.sdiv (BitVec.ofInt 8 (-128)) (BitVec.ofInt 8 (-1)) = BitVec.ofInt 8 (-128) ∧
      Int.tdiv (-128) (-1) = 128 ∧ ¬ SignedRange 8 (Int.tdiv (-128) (-1)) := by decide
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:333-334
theorem ce_srem_uncorrected_sign :
    (-1 : Int) - 3 * sdivMagicUncorrected 171 (8 - 1 + 2) (-1) = 2 := by decide
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:341-343
theorem ce_directRem_quotient_valid_multiplier :
    singleWordMagic 8 35 = 235 ∧ singleWordShift 8 35 = 13 ∧
      MulShiftCorrect 8 35 235 13 ∧ directRem 13 35 235 255 = 11 ∧ 255 % 35 = 10 := by
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:366-367
theorem ce_exactCriterion_u8_d_zero :
    0 < 2 ^ 8 ∧ 0 ≤ 16 ∧ ¬ (MulShiftCorrect 8 0 0 0 ↔ ExactCriterion 8 0 0 0) := by decide +kernel
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:371-372
theorem ce_exactCriterion_u8_d_256 :
    0 < 256 ∧ 0 ≤ 16 ∧ ¬ (MulShiftCorrect 8 256 0 0 ↔ ExactCriterion 8 256 0 0) := by
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:413-415
theorem ce_fixupQuot_unsignedMagic_u8_x_range :
    2 ≤ 15 ∧ 15 < 2 ^ 8 ∧
      fixupQuot 8 (unsignedMagic 8 15 - 2 ^ 8) (clog2 15) 299 ≠ 299 / 15 := by
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:420-421
theorem ce_fixupQuot_unsignedMagic_u16_div7_x_range :
    fixupQuot 16 (unsignedMagic 16 7 - 2 ^ 16) (clog2 7) 104859 ≠ 104859 / 7 := by
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:426-428
theorem ce_fixupQuot_unsignedMagic_u8_d_one_canonical :
    1 < 2 ^ 8 ∧
      ¬ (∀ x, x < 2 ^ 8 → fixupQuot 8 (unsignedMagic 8 1 - 2 ^ 8) (clog2 1) x = x / 1) :=
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:435-437
theorem ceilDiv_succ_leaves_single_word_u8_div3 :
    ceilDiv (2 ^ 9) 3 = 171 ∧ 171 < 2 ^ 8 ∧ MulShiftCorrect 8 3 171 9 ∧
      ceilDiv (2 ^ 10) 3 = 342 ∧ ¬ 342 < 2 ^ 8 := by
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:446-448
theorem signed_sandwich_not_necessary_i8_div35 :
    2 ^ (8 - 1 + 4) < 59 * 35 ∧ ¬ 59 * 35 ≤ 2 ^ (8 - 1 + 4) + 2 ^ 4 ∧
      ∀ x, SignedRange 8 x → sdivMagic 59 (8 - 1 + 4) x = Int.tdiv x ((35 : Nat) : Int) := by
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:465-467
theorem signedMagic_not_minimal_i8_div3 :
    signedMagic 8 3 = 171 ∧ ¬ 171 < 2 ^ (8 - 1) ∧
      2 ^ (8 - 1 + 1) < 86 * 3 ∧ 86 * 3 ≤ 2 ^ (8 - 1 + 1) + 2 ^ 1 ∧ 86 < 2 ^ (8 - 1) := by
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:531
theorem signedMagic_one_one : signedMagic 1 1 = 2 ^ 1 ∧ clog2 1 = 0 := by decide
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:536-537
theorem exists_mulShiftCorrect_iff_ceilDiv_d_zero (N s : Nat) :
    (∃ m, MulShiftCorrect N 0 m s) ↔ MulShiftCorrect N 0 (ceilDiv (2 ^ s) 0) s := by
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:547-550
theorem biasDivMasked_k_zero_failures :
    (∀ N : Nat, 1 ≤ N → biasDivMasked N 0 (-1) ≠ Int.tdiv (-1) (2 ^ 0)) ∧
    (∀ N : Nat, 2 ≤ N → ¬ SignedRange N (biasSumMasked N 0 (-1))) ∧
    (∀ x : Int, SignedRange 1 x → SignedRange 1 (biasSumMasked 1 0 x)) := by
```

#### `lean/Toy/MagicDiv/Witnesses.lean`

```lean
-- lean/Toy/MagicDiv/Witnesses.lean:108-109
theorem nv_evaluated_instances :
    (2 ≤ 7 ∧ 7 < 2 ^ 8 ∧ 200 < 2 ^ 8) ∧ 200 < 2 ^ 16 ∧ (0 < 7 ∧ 7 < 2 ^ 8 ∧ 11 ≤ 16) := by
```

#### `lean/Toy/MagicDiv/Companions.lean`

Two companion lemmas; no other declaration depends on them. `directRemB_iff` is the adequacy lemma for `directRemB`; `ce_minimal_shift_u8_div7_input_range` is the tightness counterexample for the inner input range of the second conjunct of `minimal_shift_u8_div7` (result 7).

```lean
-- lean/Toy/MagicDiv/Companions.lean:21-22
theorem directRemB_iff (N F d m : Nat) :
    directRemB N F d m = true ↔ ∀ x, x < 2 ^ N → directRem F d m x = x % d := by
```

```lean
-- lean/Toy/MagicDiv/Companions.lean:29-30
theorem ce_minimal_shift_u8_div7_input_range :
    (∀ x, x < 685 → (x * 293) >>> 11 = x / 7) ∧ (685 * 293) >>> 11 ≠ 685 / 7 := by
```

### Counterexamples, non-vacuity witnesses and positive control referenced by the cards

Every counterexample, non-vacuity witness and positive control named in a card's ledger, witness or control line (and in the Evidence table) is quoted here verbatim (proof omitted), in source order. A counterexample states, for the instance in its witness class, that all other hypotheses of the result hold and the conclusion fails; a non-vacuity witness states that all hypotheses of its result hold for one instance.

#### `lean/Toy/MagicDiv/Counterexamples.lean`

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:19-20
theorem ce_sandwich_hlo :
    1 * 1 ≤ 2 ^ (1 + 0) + 2 ^ 0 ∧ ¬ MulShiftCorrect 1 1 1 (1 + 0) :=
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:26-27
theorem ce_sandwich_hhi :
    2 ^ (8 + 2) ≤ 147 * 7 ∧ ¬ MulShiftCorrect 8 7 147 (8 + 2) :=
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:33-35
theorem ce_sandwich_input_range :
    (2 ^ (1 + 0) ≤ 1 * 3 ∧ 1 * 3 ≤ 2 ^ (1 + 0) + 2 ^ 0) ∧
      (2 ^ 1 * 1) >>> (1 + 0) ≠ 2 ^ 1 / 3 := by decide
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:47-49
theorem ce_unsignedMagic_sandwich_d_zero :
    ¬ (2 ^ (0 + clog2 0) ≤ unsignedMagic 0 0 * 0 ∧
        unsignedMagic 0 0 * 0 ≤ 2 ^ (0 + clog2 0) + 2 ^ clog2 0) := by decide
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:52
theorem ce_unsignedMagic_ge_two_pow_d_zero : ¬ 2 ^ 8 ≤ unsignedMagic 8 0 := by decide
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:63
theorem ce_unsignedMagic_lt_two_pow_succ : ¬ unsignedMagic 0 3 < 2 ^ (0 + 1) := by decide
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:67-70
theorem ce_unsignedMagic_low_d_zero :
    0 ≤ 2 ^ (0 + 1) ∧
      ¬ (unsignedMagic 0 0 = 2 ^ 0 + (unsignedMagic 0 0 - 2 ^ 0) ∧
          unsignedMagic 0 0 - 2 ^ 0 < 2 ^ 0) := by decide
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:74-77
theorem ce_unsignedMagic_low_hd :
    0 < 3 ∧
      ¬ (unsignedMagic 0 3 = 2 ^ 0 + (unsignedMagic 0 3 - 2 ^ 0) ∧
          unsignedMagic 0 3 - 2 ^ 0 < 2 ^ 0) := by decide
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:83
theorem ce_single_word_hN : 1 ≤ 2 ^ 0 ∧ ¬ singleWordMagic 0 1 < 2 ^ 0 := by decide
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:87
theorem ce_single_word_hdN : 1 ≤ 1 ∧ ¬ singleWordMagic 1 3 < 2 ^ 1 := by decide
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:106-107
theorem ce_fixupQuot_eq_wide_hl :
    0 ≤ 2 ^ 1 ∧ fixupQuot 1 0 0 1 ≠ (1 * (2 ^ 1 + 0)) >>> (1 + 0) := by decide
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:110-111
theorem ce_fixupQuot_eq_wide_hm :
    1 ≤ 1 ∧ fixupQuot 0 2 1 1 ≠ (1 * (2 ^ 0 + 2)) >>> (0 + 1) := by decide
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:115-117
theorem ce_fixupQuot_correct_hl :
    0 ≤ 2 ^ 1 ∧ MulShiftCorrect 1 1 (2 ^ 1 + 0) (1 + 0) ∧
      ¬ (∀ x, x < 2 ^ 1 → fixupQuot 1 0 0 x = x / 1) :=
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:122-124
theorem ce_fixupQuot_correct_hm :
    1 ≤ 1 ∧ MulShiftCorrect 1 1 (2 ^ 1 + 4) (1 + 1) ∧
      ¬ (∀ x, x < 2 ^ 1 → fixupQuot 1 4 1 x = x / 1) :=
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:129-130
theorem ce_fixupQuot_correct_h :
    1 ≤ 1 ∧ 0 ≤ 2 ^ 1 ∧ ¬ (∀ x, x < 2 ^ 1 → fixupQuot 1 0 1 x = x / 1) :=
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:136-138
theorem ce_fixupQuot_correct_input_range :
    1 ≤ 2 ∧ 1 ≤ 2 ^ 1 ∧ MulShiftCorrect 1 3 (2 ^ 1 + 1) (1 + 2) ∧
      fixupQuot 1 1 2 8 ≠ 8 / 3 :=
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:142-143
theorem ce_fixupQuot_unsignedMagic_d_one :
    ¬ (∀ x, x < 2 ^ 1 → fixupQuot 1 (unsignedMagic 1 1 - 2 ^ 1) (clog2 1) x = x / 1) :=
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:148-149
theorem ce_fixupQuot_unsignedMagic_input_range :
    2 ≤ 3 ∧ fixupQuot 0 (unsignedMagic 0 3 - 2 ^ 0) (clog2 3) 2 ≠ 2 / 3 := by
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:161
theorem pc_div7_u8_nine_bit_multiplier : 293 < 2 ^ 9 ∧ MulShiftCorrect 8 7 293 11 := by
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:166
theorem ce_no_single_word_u8_div7_m_bound : ¬ (∀ s, ¬ MulShiftCorrect 8 7 293 s) :=
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:171
theorem ce_minimal_shift_u8_div7_s_bound : ¬ (∀ m, ¬ MulShiftCorrect 8 7 m 11) :=
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:179-180
theorem ce_exactCriterion_d_zero :
    0 < 2 ^ 1 ∧ ¬ (MulShiftCorrect 1 0 0 0 ↔ ExactCriterion 1 0 0 0) := by decide +kernel
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:184-185
theorem ce_exactCriterion_hdN :
    0 < 2 ∧ ¬ (MulShiftCorrect 1 2 0 0 ↔ ExactCriterion 1 2 0 0) := by decide +kernel
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:188-189
theorem ce_two_pow_le :
    ¬ (MulShiftCorrect 1 1 2 1 ↔ (2 ^ 1 - 1) * 2 < 2 ^ 1) := by decide +kernel
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:193-194
theorem ce_exists_ceilDiv_hdN :
    0 < 2 ∧ ¬ ((∃ m, MulShiftCorrect 1 2 m 0) ↔ MulShiftCorrect 1 2 (ceilDiv (2 ^ 0) 2) 0) :=
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:199-200
theorem ce_ceilDiv_succ_premise :
    ¬ MulShiftCorrect 8 7 (ceilDiv (2 ^ (9 + 1)) 7) (9 + 1) :=
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:207-209
theorem ce_sdiv_hlo :
    128 * 2 ≤ 2 ^ (8 - 1 + 1) + 2 ^ 1 ∧
      ¬ (∀ x, SignedRange 8 x → sdivMagic 128 (8 - 1 + 1) x = Int.tdiv x ((2 : Nat) : Int)) :=
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:214-216
theorem ce_sdiv_hhi :
    2 ^ (8 - 1 + 2) < 74 * 7 ∧
      ¬ (∀ x, SignedRange 8 x → sdivMagic 74 (8 - 1 + 2) x = Int.tdiv x ((7 : Nat) : Int)) :=
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:222-225
theorem ce_sdiv_range :
    (2 ^ (1 - 1 + 0) < 2 * 1 ∧ 2 * 1 ≤ 2 ^ (1 - 1 + 0) + 2 ^ 0) ∧
      sdivMagic 2 (1 - 1 + 0) 1 ≠ Int.tdiv 1 ((1 : Nat) : Int) ∧
      sdivMagic 2 (1 - 1 + 0) (-2) ≠ Int.tdiv (-2) ((1 : Nat) : Int) := by decide
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:231-234
theorem ce_uncorr_hlo :
    128 * 2 ≤ 2 ^ (8 - 1 + 1) + 2 ^ 1 ∧
      ¬ (∀ x, SignedRange 8 x → x < 0 →
        sdivMagicUncorrected 128 (8 - 1 + 1) x = Int.tdiv x ((2 : Nat) : Int) - 1) :=
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:238-241
theorem ce_uncorr_hhi :
    2 ^ (8 - 1 + 2) < 74 * 7 ∧
      ¬ (∀ x, SignedRange 8 x → x < 0 →
        sdivMagicUncorrected 74 (8 - 1 + 2) x = Int.tdiv x ((7 : Nat) : Int) - 1) :=
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:245-247
theorem ce_uncorr_neg :
    (2 ^ (8 - 1 + 2) < 171 * 3 ∧ 171 * 3 ≤ 2 ^ (8 - 1 + 2) + 2 ^ 2) ∧ SignedRange 8 0 ∧
      sdivMagicUncorrected 171 (8 - 1 + 2) 0 ≠ Int.tdiv 0 ((3 : Nat) : Int) - 1 := by decide
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:265-266
theorem ce_tdiv_signedRange_hx :
    ¬ (SignedRange 8 (Int.tdiv 128 1) ↔ ¬ ((128 : Int) = -(2 : Int) ^ (8 - 1) ∧ (1 : Int) = -1)) := by
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:270-272
theorem ce_signedMagic_d_zero :
    ¬ (2 ^ (8 - 1 + clog2 0) < signedMagic 8 0 * 0 ∧
        signedMagic 8 0 * 0 ≤ 2 ^ (8 - 1 + clog2 0) + 2 ^ clog2 0) := by decide
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:294-296
theorem ce_biasDiv_hk :
    SignedRange 2 (-1) ∧
      ¬ (SignedRange 2 (biasSum 2 2 (-1)) ∧ biasDiv 2 2 (-1) = Int.tdiv (-1) (2 ^ 2)) :=
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:300-301
theorem ce_biasDiv_hx :
    1 < 8 ∧ ¬ (SignedRange 8 (biasSum 8 1 128) ∧ biasDiv 8 1 128 = Int.tdiv 128 (2 ^ 1)) :=
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:306-307
theorem ce_biasDivBV_width :
    (biasDivBV 8 (BitVec.ofInt 8 (-1))).toInt ≠ Int.tdiv (BitVec.ofInt 8 (-1)).toInt (2 ^ 8) := by
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:314-315
theorem ce_rem_correct :
    ¬ (∀ x, x < 2 ^ 1 → x - 1 * ((x * 0) >>> 0) = x % 1) :=
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:322-324
theorem ce_srem_hlo :
    128 * 2 ≤ 2 ^ (8 - 1 + 1) + 2 ^ 1 ∧ SignedRange 8 (-2) ∧
      sremMagic 2 128 (8 - 1 + 1) (-2) ≠ Int.tmod (-2) ((2 : Nat) : Int) := by decide
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:327-329
theorem ce_srem_hhi :
    2 ^ (8 - 1 + 2) < 74 * 7 ∧ SignedRange 8 (-125) ∧
      sremMagic 7 74 (8 - 1 + 2) (-125) ≠ Int.tmod (-125) ((7 : Nat) : Int) := by decide
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:347-348
theorem ce_directRem_hlo :
    1 * 2 ≤ 2 ^ (2 + 0) + 2 ^ 0 ∧ ¬ (∀ x, x < 2 ^ 2 → directRem (2 + 0) 2 1 x = x % 2) :=
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:352-353
theorem ce_directRem_hhi :
    2 ^ (8 + 2) ≤ 147 * 7 ∧ ¬ (∀ x, x < 2 ^ 8 → directRem (8 + 2) 7 147 x = x % 7) :=
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:377-379
theorem ce_uncorr_range :
    (2 ^ (1 - 1 + 0) < 2 * 1 ∧ 2 * 1 ≤ 2 ^ (1 - 1 + 0) + 2 ^ 0) ∧ (-2 : Int) < 0 ∧
      sdivMagicUncorrected 2 (1 - 1 + 0) (-2) ≠ Int.tdiv (-2) ((1 : Nat) : Int) - 1 := by decide
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:384-386
theorem ce_biasDivBV_sdiv_k7 :
    biasDivBV 7 (BitVec.ofInt 8 (-128)) ≠
      (BitVec.ofInt 8 (-128)).sdiv (BitVec.ofNat 8 (2 ^ 7)) := by decide
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:391-392
theorem ce_rem_input_range :
    MulShiftCorrect 1 3 1 1 ∧ 2 - 3 * ((2 * 1) >>> 1) ≠ 2 % 3 := by decide +kernel
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:396-398
theorem ce_srem_range :
    (2 ^ (1 - 1 + 0) < 2 * 1 ∧ 2 * 1 ≤ 2 ^ (1 - 1 + 0) + 2 ^ 0) ∧
      sremMagic 1 2 (1 - 1 + 0) 1 ≠ Int.tmod 1 ((1 : Nat) : Int) := by decide
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:402-404
theorem ce_directRem_input_range :
    (2 ^ (1 + 0) ≤ 1 * 3 ∧ 1 * 3 ≤ 2 ^ (1 + 0) + 2 ^ 0) ∧
      directRem (1 + 0) 3 1 2 ≠ 2 % 3 := by decide
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:476-478
theorem ce_biasDivMasked_k_zero (N : Nat) (hN : 1 ≤ N) :
    0 < N ∧ SignedRange N (-1) ∧
      ¬ (SignedRange N (biasSumMasked N 0 (-1)) ∧ biasDivMasked N 0 (-1) = Int.tdiv (-1) (2 ^ 0)) := by
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:502-504
theorem ce_biasDivMasked_hk :
    1 ≤ 2 ∧ SignedRange 2 (-1) ∧
      ¬ (SignedRange 2 (biasSumMasked 2 2 (-1)) ∧ biasDivMasked 2 2 (-1) = Int.tdiv (-1) (2 ^ 2)) := by
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:509-511
theorem ce_biasDivMasked_hx :
    1 ≤ 1 ∧ 1 < 8 ∧
      ¬ (SignedRange 8 (biasSumMasked 8 1 128) ∧ biasDivMasked 8 1 128 = Int.tdiv 128 (2 ^ 1)) := by
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:516-518
theorem ce_biasDivBVMasked_u8_k_zero :
    0 < 8 ∧ (biasDivBVMasked 0 (BitVec.ofInt 8 (-1))).toInt ≠
      Int.tdiv (BitVec.ofInt 8 (-1)).toInt (2 ^ 0) := by
```

```lean
-- lean/Toy/MagicDiv/Counterexamples.lean:524-526
theorem ce_biasDivBVMasked_u8_k_eight :
    1 ≤ 8 ∧ (biasDivBVMasked 8 (BitVec.ofInt 8 (-1))).toInt ≠
      Int.tdiv (BitVec.ofInt 8 (-1)).toInt (2 ^ 8) := by
```

#### `lean/Toy/MagicDiv/Witnesses.lean`

```lean
-- lean/Toy/MagicDiv/Witnesses.lean:17-19
theorem nv_sandwich_u32_div7 :
    2 ^ (32 + 3) ≤ 4908534053 * 7 ∧ 4908534053 * 7 ≤ 2 ^ (32 + 3) + 2 ^ 3 ∧
      200 < 2 ^ 32 := by decide
```

```lean
-- lean/Toy/MagicDiv/Witnesses.lean:23-24
theorem nv_unsignedMagic_sandwich_div7 :
    (0 : Nat) < 7 ∧ unsignedMagic 32 7 = 2 ^ 32 + 613566757 := by decide
```

```lean
-- lean/Toy/MagicDiv/Witnesses.lean:28
theorem nv_unsignedMagic_bounds : (0 : Nat) < 7 ∧ 7 ≤ 2 ^ (32 + 1) := by decide
```

```lean
-- lean/Toy/MagicDiv/Witnesses.lean:32
theorem nv_single_word_u8_div7 : 1 ≤ 8 ∧ 7 ≤ 2 ^ 8 := by decide
```

```lean
-- lean/Toy/MagicDiv/Witnesses.lean:36-37
theorem nv_fixupQuot_correct_u8_div7 :
    1 ≤ 3 ∧ 37 ≤ 2 ^ 8 ∧ MulShiftCorrect 8 7 (2 ^ 8 + 37) (8 + 3) ∧ 200 < 2 ^ 8 := by
```

```lean
-- lean/Toy/MagicDiv/Witnesses.lean:41
theorem nv_fixupQuot_unsignedMagic : 2 ≤ 7 ∧ 200 < 2 ^ 8 := by decide
```

```lean
-- lean/Toy/MagicDiv/Witnesses.lean:45
theorem nv_no_single_word_u8_div7 : 147 < 2 ^ 8 ∧ 10 ≤ 10 := by decide
```

```lean
-- lean/Toy/MagicDiv/Witnesses.lean:49
theorem nv_exact_u8 : 0 < 7 ∧ 7 < 2 ^ 8 ∧ 2 ^ 8 ≤ 300 := by decide
```

```lean
-- lean/Toy/MagicDiv/Witnesses.lean:52
theorem nv_exact_u8_div7 : 0 < 7 ∧ 7 < 2 ^ 8 := by decide
```

```lean
-- lean/Toy/MagicDiv/Witnesses.lean:55
theorem nv_ceilDiv_succ_u8_div7 : MulShiftCorrect 8 7 (ceilDiv (2 ^ 11) 7) 11 := by
```

```lean
-- lean/Toy/MagicDiv/Witnesses.lean:61-64
theorem nv_signed_sandwich_i32_div7 :
    signedMagic 32 7 = 2454267027 ∧
      2 ^ (32 - 1 + 3) < 2454267027 * 7 ∧ 2454267027 * 7 ≤ 2 ^ (32 - 1 + 3) + 2 ^ 3 ∧
      SignedRange 32 (-7) := by
```

```lean
-- lean/Toy/MagicDiv/Witnesses.lean:68-70
theorem nv_sdivMagicUncorrected :
    2 ^ (32 - 1 + 3) < 2454267027 * 7 ∧ 2454267027 * 7 ≤ 2 ^ (32 - 1 + 3) + 2 ^ 3 ∧
      SignedRange 32 (-7) ∧ (-7 : Int) < 0 := by
```

```lean
-- lean/Toy/MagicDiv/Witnesses.lean:74
theorem nv_tdiv_signedRange : SignedRange 8 (-128) := by decide
```

```lean
-- lean/Toy/MagicDiv/Witnesses.lean:78-79
theorem nv_signedMagic_sandwich_div7 :
    (0 : Nat) < 7 ∧ signedMagic 32 7 = 2454267027 := by decide
```

```lean
-- lean/Toy/MagicDiv/Witnesses.lean:83-84
theorem nv_int_shiftRight :
    (-1 : Int) >>> 1 ≠ Int.tdiv (-1) (2 ^ 1) ∧ (-8 : Int) >>> 2 = Int.tdiv (-8) (2 ^ 2) := by
```

```lean
-- lean/Toy/MagicDiv/Witnesses.lean:89
theorem nv_biasDiv : 1 ≤ 2 ∧ 2 < 8 ∧ SignedRange 8 (-7) := by decide
```

```lean
-- lean/Toy/MagicDiv/Witnesses.lean:92
theorem nv_biasDivBV_u8 : 1 ≤ 2 ∧ 2 < 8 ∧ 2 ≤ 6 := by decide
```

```lean
-- lean/Toy/MagicDiv/Witnesses.lean:96
theorem nv_mulShift_rem : MulShiftCorrect 8 7 293 11 ∧ 200 < 2 ^ 8 := by decide +kernel
```

```lean
-- lean/Toy/MagicDiv/Witnesses.lean:100-102
theorem nv_sremMagic_both_signs :
    2 ^ (32 - 1 + 3) < 2454267027 * 7 ∧ 2454267027 * 7 ≤ 2 ^ (32 - 1 + 3) + 2 ^ 3 ∧
      (SignedRange 32 7 ∧ (0 : Int) ≤ 7) ∧ (SignedRange 32 (-7) ∧ (-7 : Int) < 0) := by
```

## Boundaries

### Non-claims

What each result does **not** show. Remarks that point to a failure cite the proved theorem by name or say "not proved here".

#### Non-claims of result 1 (`mulShiftCorrect_of_sandwich`)

- The sandwich is sufficient, not necessary: sandwich_not_necessary_u8_div35 is a correct multiplier (N = 8, d = 35, l = 5, m = 235) with m*d - 2^(N+l) = 33 > 2^l. The necessary and sufficient condition is mulShiftCorrect_iff_exactCriterion.
- Multiplication is exact on unbounded naturals; the result says nothing about how x*m is formed on an N-bit machine (a multiply-high is needed, and m may need N + 1 bits; see the card unsignedMagic_bounds).
- Stated for unsigned inputs x < 2^N; this card neither establishes nor refutes claims about signed inputs (for signed division see sdivMagic_eq_tdiv_of_sandwich).
- It does not pick l or m; existence is unsignedMagic_sandwich, and the ceiling multiplier ceilDiv (2^(N+l)) d satisfies hlo automatically (le_ceilDiv_mul).
- It addresses division of arbitrary x. When d is known to divide x (exact division), Granlund and Montgomery (Section 9) use a single low-half multiplication by the inverse of the odd part of d modulo 2^N instead; that method is not modelled here (not proved here).

#### Non-claims of result 2 (`unsignedMagic_sandwich`)

- It does not say how many bits the multiplier needs ('fits in b bits' below means 'is below 2^b'); card unsignedMagic_bounds does. For every N, N = 0 included, and every d >= 1, 2^N <= unsignedMagic N d, so the multiplier does not fit in N bits (unsignedMagic_ge_two_pow_of_pos); at d = 0, which this card excludes, it is 0 for every N (unsignedMagic_zero_right). For every N and every d <= 2^(N+1), d = 0 included, unsignedMagic N d < 2^(N+1), so it fits in N + 1 bits (unsignedMagic_lt_two_pow_succ_of_le). The bound d <= 2^(N+1) is tight at every N (d = 2^(N+1) + 1 gives exactly 2^(N+1): unsignedMagic_two_pow_succ_add_one) but is sufficient, not necessary: every power of two d = 2^k gives exactly 2^N (unsignedMagic_two_pow), so d = 2^k with k >= N + 2 exceeds 2^(N+1) and still fits in N + 1 bits (unsignedMagic_lt_two_pow_succ_converse_fails), and so do some divisors above 2^(N+1) that are not powers of two (N = 1, d = 6; N = 8, d = 768; N = 32, d = 3*2^32: unsignedMagic_lt_two_pow_succ_above_examples).
- Shift N + clog2 d is not the minimal correct shift in general (for N = 8, d = 3 shift 9 works with multiplier 171 < 2^8; see pc_single_word_shift_fits and exists_mulShiftCorrect_iff_ceilDiv).
- Granlund and Montgomery's Figure 4.1 uses floor(2^(N+l)/d) + 1 rather than the ceiling; for d >= 1 the two are equal when d does not divide 2^(N+l) and differ by 1 when it does (derived, not proved here).

#### Non-claims of result 3 (`unsignedMagic_bounds`)

- Part (a) does not say that no N-bit multiplier exists for d: at the shift one lower, N + clog2 d - 1, an N-bit multiplier may exist (pc_single_word_shift_fits for N = 8, d = 3) or not (no_single_word_multiplier_u8_div7 for N = 8, d = 7); the exact condition is single_word_multiplier_exists_iff.
- Ways to avoid an (N+1)-bit multiplier that this card does not cover: a lower shift (single_word_multiplier_exists_iff), the add-and-shift fixup (fixupQuot_unsignedMagic_correct), an N-bit multiply-add (robison_multiply_add_u8_div7 for N = 8, d = 7; Robison 2005 in general, not proved here), a narrower dividend range (mulShift_u8_div7_below_209), pre-shifting even divisors (not proved here), and powers of two, where a shift suffices (not proved here).
- Part (c) gives a low part below 2^N for 2^N < d <= 2^(N+1) as well, but the fixup that uses it then shifts by clog2 d - 1 = N, the full word width (fixupQuot_shift_eq_width).
- Beyond d <= 2^(N+1) it does not characterize which divisors reach 2^(N+1). Proved facts on both sides: at every N, d = 2^(N+1) + 1 reaches it (unsignedMagic_two_pow_succ_add_one); every power of two d = 2^k, including k >= N + 2, gives exactly 2^N (unsignedMagic_two_pow, unsignedMagic_lt_two_pow_succ_converse_fails); and some divisors above 2^(N+1) that are not powers of two stay below 2^(N+1) (unsignedMagic_lt_two_pow_succ_above_examples, for N = 1, 8, 32).

#### Non-claims of result 4 (`single_word_multiplier_exists_iff`)

- The equivalence is informative for 1 <= d < 2^N; when N = 0, d = 0, or d >= 2^N, both sides hold (the left side with m = 0), so it carries no information there.
- s* = N + clog2 d - 1 is the largest shift whose ceiling multiplier is below 2^N, not the smallest correct shift: for N = 8, d = 9, s* = 11 (m* = 228) while (57, 9) is correct (singleWordShift_not_minimal_u8_div9); for N = 32, d = 641, s* = 41 while (6700417, 32) is correct and needs no shift after a 32-bit multiply-high (mulShiftCorrect_u32_div641_shift32).
- The existential does not require s >= N: for d = 1 and N >= 1, s* = N - 1 < N (singleWordShift_one; at N = 0, s* = 0 = N), which is not a multiply-high followed by a shift; for d = 1 and N >= 1, no m < 2^N is correct at any s >= N (not_mulShiftCorrect_div_one_of_width_le).
- For a non-power-of-two d with 1 <= d < 2^N, 2^(N-1) < m* (two_pow_pred_lt_singleWordMagic) and m* < 2^N (singleWordMagic_lt_two_pow, which applies because 1 <= d < 2^N forces N >= 1), so m* read as a signed N-bit value is negative and a signed multiply-high would misinterpret it (machine encoding not modelled here). The bound needs d >= 1: at d = 0, m* = 0 for every N (singleWordMagic_zero_right).
- The card is stated for the plain multiply-shift form (x*m) >>> s; it neither establishes nor refutes claims about other instruction sequences. Pre-shifting an even dividend and N-bit multiply-add forms can avoid the (N+1)-bit fixup when the right-hand side is false (robison_multiply_add_u8_div7 for N = 8, d = 7; Robison 2005 and Lemire-Bartlett-Kaser Section 6 in general, not proved here).
- For N = 8 exactly 55 of the 255 divisors 1 <= d <= 255 have an incorrect candidate (count_no_single_word_u8, which counts the d with correctB 8 d m* s* = false; correctB_iff identifies correctB N d m s = true with MulShiftCorrect N d m s), hence, by this card's equivalence, no 8-bit multiplier at any shift.
- It is not by itself a cheap test; combine it with mulShiftCorrect_iff_exactCriterion at s = s*.

#### Non-claims of result 5 (`fixupQuot_eq_wide`)

- No machine-level claim: x*m' is a 2N-bit product; that t, x - t, (x - t) >>> 1, the sum, and the result stay below 2^N for x, m' < 2^N is derived, not proved here. An N-bit register needs m' < 2^N, which is stronger than m' <= 2^N.
- The final shift l - 1 must be below N on a machine whose shifts are not total; this card does not constrain it (see fixupQuot_unsignedMagic_correct for the textbook multiplier).
- fixupQuot_correct is a one-line consequence of fixupQuot_eq_wide; the substance is the identity.

#### Non-claims of result 6 (`fixupQuot_unsignedMagic_correct`)

- Among d >= 2, the final shift clog2 d - 1 is below the word width N if and only if d <= 2^N (fixupQuot_shift_lt_width_iff, which combines fixupQuot_shift_lt_width with succ_le_clog2_of_two_pow_lt). For 2^N < d <= 2^(N+1) the final shift is clog2 d - 1 = N (fixupQuot_shift_eq_width; e.g. fixupQuot_shift_width_u8_d300). A right shift by N is undefined behavior in C and C++ when N is at least the width of the promoted left operand (for example N = 32 or 64 when int is 32 bits; a uint8_t operand is promoted to int, so a shift by 8 is defined there and gives 0), poison in LLVM IR at every width iN, an overflow in Rust at every width uN (a panic in debug builds), and reduced modulo N (to a shift by 0) by 32- and 64-bit register shifts on x86, AArch64 and RISC-V (Modeling bridge, item 4; derived, not proved here). This card's equality relies on Lean's total shift there.
- For d > 2^(N+1) the low part m' can equal 2^N and then does not fit in N bits: at every N, d = 2^(N+1) + 1 gives m' = 2^N (unsignedMagic_two_pow_succ_add_one); part (b) of card unsignedMagic_bounds is tight.
- It does not say the fixup is needed: when single_word_multiplier_exists_iff holds an N-bit multiplier suffices.
- Evaluated instances fixupQuot_unsignedMagic_u8 (N = 8, 2 <= d <= 255) and fixupQuot_unsignedMagic_u16_div7 (N = 16, d = 7) are kernel evaluations of special cases; their hypothesis ledgers are listed separately.

#### Non-claims of result 7 (`no_single_word_multiplier_u8_div7`)

- It is stated for one instance (N = 8, d = 7) and the plain multiply-shift form with an exact product; this card neither establishes nor refutes claims about other N, other d, or other instruction sequences (escape hatches proved separately are listed next). For other divisors see single_word_multiplier_exists_iff (for N = 8, 55 of the 255 divisors 1 <= d <= 255 have no 8-bit multiplier at any shift: count_no_single_word_u8, read through correctB_iff and single_word_multiplier_exists_iff).
- Escape hatches that defeat it: an 8-bit multiply-add, (x*146 + 146) >>> 10 = x / 7 for all x < 2^8 (robison_multiply_add_u8_div7); a narrower dividend range, (x*147) >>> 10 = x / 7 for all x < 209, failing at 209 (mulShift_u8_div7_below_209); a multiplier operand of at least 9 bits, (293, 11) (pc_div7_u8_nine_bit_multiplier); the add-and-shift fixup (fixupQuot_unsignedMagic_correct).
- No claim about the cost of these alternatives.

#### Non-claims of result 8 (`mulShiftCorrect_iff_exactCriterion`)

- Exact products are assumed; nothing about the word size of m or of the product (m may exceed 2^N).
- A pair (m, s) satisfying this criterion computes the quotient but need not compute the remainder directly: ce_directRem_quotient_valid_multiplier (N = 8, d = 35, m = 235, s = 13, x = 255). The remainder x - d*q is always correct (mulShift_rem_eq_mod_of_correct).
- The evaluated instance mulShiftCorrect_iff_exactCriterion_u8 (N = 8, 1 <= d <= 255, s <= 16, every m) is a special case; its hypothesis ledger is listed separately.
- That LLVM's unsigned search stops at the first shift satisfying the upper half of this criterion for the ceiling multiplier is a modeling-bridge statement from source inspection, not proved here.

#### Non-claims of result 9 (`exists_mulShiftCorrect_iff_ceilDiv`)

- It does not say the ceiling multiplier is below 2^N, nor which shift to use; the minimal correct shift is the least s at which the right-hand side holds (upward closure: mulShiftCorrect_ceilDiv_succ).
- Every correct multiplier at shift s is at least ceil(2^s/d) (two_pow_le_mul_of_correct with ceilDiv_le_of_le_mul), so the ceiling multiplier is the smallest correct one; this is a supporting fact, not a separate card.

#### Non-claims of result 10 (`mulShiftCorrect_ceilDiv_succ`)

- Upward closure does not preserve a single-word multiplier size: for N = 8, d = 3, ceil(2^9/3) = 171 < 2^8 is correct at shift 9, while ceil(2^10/3) = 342 >= 2^8 (ceilDiv_succ_leaves_single_word_u8_div3).
- It is stated for the ceiling multipliers ceil(2^s/d) and ceil(2^(s+1)/d) with the power-of-two denominators 2^s and 2^(s+1); this card neither establishes nor refutes the corresponding upward closure for other multipliers (such as floor(2^s/d) + 1) or other denominators.

#### Non-claims of result 11 (`sdivMagic_eq_tdiv_of_sandwich`)

- Stated for natural-number divisors d (d >= 1 is forced by hlo); this card neither establishes nor refutes claims about negative divisors. For d < 0 use Int.tdiv x (-d) = -(Int.tdiv x d) (core Int.tdiv_neg): negate the output quotient. Granlund and Montgomery warn against rewriting the quotient as TRUNC((-n)/|d|), which fails for n = -2^(N-1); that machine-level failure is not modelled here.
- The sandwich is sufficient, not necessary: for N = 8, d = 35, (m, shift) = (59, 11) violates hhi (59*35 = 2065 > 2^11 + 2^4) and is correct for every signed 8-bit x (signed_sandwich_not_necessary_i8_div35).
- Stated with exact integer arithmetic; this card neither establishes nor refutes claims about fixed-width machine arithmetic. The machine encoding is not modelled: a signed multiply-high reads the multiplier as a signed N-bit value and divides by 2^N; multipliers produced by signedMagic always exceed 2^(N-1) (two_pow_pred_lt_signedMagic), so that encoding uses m - 2^N and adds x back (derived, not proved here).
- The overflow case x = -2^(N-1), d = -1 is outside this card (d > 0); see tdiv_signedRange_iff.

#### Non-claims of result 12 (`sdivMagicUncorrected_eq_tdiv_sub_one_of_neg`)

- The uncorrected sequence does not round toward negative infinity: it equals floor division on negative non-multiples of d but is one below it on negative multiples (uncorrected_ne_fdiv_at_negative_multiple: N = 8, d = 3, m = 171, shift 9 maps -3 to -2, while Int.fdiv (-3) 3 = Int.tdiv (-3) 3 = -1).
- Floor-rounding signed division by a constant does have its own multiply-based sequence (Granlund and Montgomery, Section 6); it is not modelled here.
- It is a two-line corollary of sdivMagic_eq_tdiv_of_sandwich (sdivMagicUncorrected_eq_sdivMagic_sub_one).

#### Non-claims of result 13 (`tdiv_signedRange_iff`)

- It is about the mathematical quotient Int.tdiv. Core BitVec.sdiv wraps (-2^(N-1)) / (-1) to -2^(N-1) (bitvec_sdiv_intMin_negOne_wraps, at N = 8); what particular languages or instruction sets do in that case was not examined.
- At N = 0 the signed range is {0} (signedRange_zero_iff), so the excluded case does not arise: the right-hand side's -2^(N-1) uses truncated subtraction (N - 1 = 0 at N = 0, so it reads -1 there), and x = 0 is not -1.

#### Non-claims of result 14 (`signedMagic_sandwich`)

- signedMagic N d > 2^(N-1) for every d >= 1 (two_pow_pred_lt_signedMagic): read as a signed N-bit value it is never positive, and at N = 1, d = 1 it is 2 = 2^N (signedMagic_one_one).
- At d = 1 its shift (N-1) + clog2 1 is N - 1, which is below N for N >= 1 (at N = 0 it is 0 = N); Granlund and Montgomery use l = max(ceil(log2 d), 1) instead; with clog2 d in place of ceil(log2 d), max(clog2 d, 1) equals clog2 d for d >= 2 (1 <= clog2 d: one_le_clog2) and is 1 rather than clog2 1 = 0 at d = 1 (signedMagic_one_one).
- It is neither shift-minimal nor size-minimal: for N = 8, d = 3, signedMagic 8 3 = 171 at shift 9, while m = 86 < 2^7 satisfies the signed sandwich at shift 8 (signedMagic_not_minimal_i8_div3).

#### Non-claims of result 15 (`int_shiftRight_eq_tdiv_iff`)

- It does not say how to compute Int.tdiv x (2^k) with shifts; that is biasDiv_eq_tdiv_of_lt.
- Exact integers; no word size.

#### Non-claims of result 16 (`biasDiv_eq_tdiv_of_lt`)

- Part (a) at k = 0 is an artifact of total shifts. In C and C++ a shift count at least the width of the promoted operand is undefined behavior, in LLVM IR it yields poison, and instruction sets that reduce the count modulo the width compute part (b)'s sequence, whose quotient is wrong at k = 0 (biasDivMasked_k_zero_failures). On such targets use 1 <= k < N and treat division by 1 separately.
- Part (b) needs 1 <= k. At k = 0 and x = -1: for every N >= 1 the quotient equation biasDivMasked N 0 (-1) = Int.tdiv (-1) (2^0) fails; for every N >= 2 the biased sum also leaves the signed N-bit range; at N = 1 the biased sum stays in the signed 1-bit range for every signed 1-bit x, so the range conclusion holds there and the quotient equation fails (biasDivMasked_k_zero_failures). The tightness counterexample ce_biasDivMasked_k_zero states that the conjunction of the two conclusions fails, for every N >= 1.
- The sum is exact (no wrap-around); the no-overflow conjunct shows the N-bit sum would not wrap. Wrapping arithmetic is checked on BitVec 8 (biasDivBV_u8).
- Stated for the positive divisors 2^k; this card neither establishes nor refutes claims about the bias-and-shift sequence for d = -2^k (in exact arithmetic, Int.tdiv x (-(2^k)) = -(Int.tdiv x (2^k)) by core Int.tdiv_neg, so negating the quotient handles that divisor).

#### Non-claims of result 17 (`biasDivBV_u8`)

- Evaluated on BitVec 8 (all 256 inputs, by kernel evaluation); this card neither establishes nor refutes claims at other BitVec widths. The general-width statement, in exact arithmetic, is biasDiv_eq_tdiv_of_lt.
- Part (a) at k = 0 relies on total shifts; see biasDiv_eq_tdiv_of_lt for the machine reading.

#### Non-claims of result 18 (`mulShift_rem_eq_mod_of_correct`)

- Unlike directRem_eq_mod_of_sandwich, this works for every quotient-correct pair, including single-word multipliers outside the sandwich.
- Natural-number subtraction is exact here because d*q <= x; no machine-width claim.

#### Non-claims of result 19 (`sremMagic_eq_tmod_and_sign`)

- Stated for natural-number divisors d (d >= 1 is forced by hlo); this card neither establishes nor refutes claims about negative divisors. For a negative divisor the truncated remainder is unchanged: Int.tmod x (-d) = Int.tmod x d (core Int.tmod_neg); it is not negated as the quotient is.
- Using the uncorrected quotient gives a wrongly signed remainder (ce_srem_uncorrected_sign).
- Hardware or language behavior of x % (-1) at x = -2^(N-1) was not examined.

#### Non-claims of result 20 (`directRem_eq_mod_of_sandwich`)

- A multiplier that is correct for the quotient need not compute the remainder directly: for N = 8, d = 35, the single-word pair (m, s) = (235, 13) satisfies MulShiftCorrect 8 35 235 13, yet directRem 13 35 235 255 = 11 != 10 = 255 mod 35 (ce_directRem_quotient_valid_multiplier); among the 200 divisors 1 <= d <= 255 whose single-word candidate is quotient-correct (count_single_word_u8), 42 fail directRem with that candidate (count_single_word_u8_directRem_fails; its Boolean checkers are read through correctB_iff and directRemB_iff).
- For shifts N + l with l < N and N >= 1, the sandwich bounds are equivalent to 2^(N+l) <= m*d and (2^N - 1)*(m*d - 2^(N+l)) < 2^(N+l) (sandwich_iff_directRem_bound), the bound of Lemire, Bartlett and Kaser's Theorem 2 for N-bit inputs; that theorem's necessity direction is not formalized here.
- Stated for unsigned inputs x < 2^N; this card neither establishes nor refutes claims about signed inputs (for example, whether directRem applied to the bit patterns of negative signed dividends gives Int.tmod).
- No machine-width claim: (x*m) mod 2^(N+l) has N + l bits and its product with d more.

### Escape hatches

Result 7 is the one result of kind impossibility in this package. Each of the following defeats it, and each is a kernel-checked theorem:

- a multiplier operand of 9 bits: `(m, s) = (293, 11)` is correct for every `x < 2^8` (`pc_div7_u8_nine_bit_multiplier`, the positive control);
- an 8-bit multiply-add: `(x*146 + 146) >>> 10 = x / 7` for every `x < 2^8` (`robison_multiply_add_u8_div7`);
- a narrower dividend range: `(x*147) >>> 10 = x / 7` for every `x < 209`, failing at `x = 209` (`mulShift_u8_div7_below_209`);
- the add-and-shift fixup with the textbook multiplier `2^8 + m'`, whose low part `m'` fits in 8 bits (results 3 and 6; result 6 holds for every `N` and every `d ≥ 2`).

Dropping the multiplier bound `m < 2^8` (hypothesis `hm`) or the shift bound `s ≤ 10` (hypothesis `hs`) defeats the corresponding part (counterexamples `ce_no_single_word_u8_div7_m_bound`, `ce_minimal_shift_u8_div7_s_bound`).

### Tightness status

Every hypothesis on a result card is `tight` with a named, kernel-checked counterexample stated in canonical form ("all other hypotheses hold and the conclusion fails", with the witness class recorded), except one: `hd: 0 < d` of result 9 is `harmless` (the conclusion also holds at `d = 0`: `exists_mulShiftCorrect_iff_ceilDiv_d_zero`). No hypothesis has tightness `unknown`. For the supporting instances under Findings, the hypotheses `d < 2^8` of `fixupQuot_unsignedMagic_u8` and `s ≤ 16` of `mulShiftCorrect_iff_exactCriterion_u8` are `harmless` (the general results 6 and 8 remove them).

### Not formalized here (considered, not proved)

- The necessity direction of Lemire–Bartlett–Kaser Theorem 2 (simultaneous quotient and direct-remainder correctness); what is proved is its relation to the sandwich bound for shifts `N + ℓ` with `ℓ < N`, `N ≥ 1` (`sandwich_iff_directRem_bound`).
- The signed direct remainder of Lemire–Kaser–Kurz Theorem 2.
- Machine-level models: the `N`-bit intermediates of the fixup, `MULUH`/`MULSH` encodings, pre-shifting even divisors, and the general multiply-add method of Robison (2005) (the single instance `robison_multiply_add_u8_div7` is proved; the general method is not).
- Floor-rounding signed division by a constant (Granlund–Montgomery Section 6) and exact division by a modular inverse (Granlund–Montgomery Section 9).
- Whether `clog2` coincides with Mathlib's `Nat.clog 2` (Mathlib is not used).

### Disproved or dropped statements

None. All 20 results are proved exactly as stated; no statement was found false, weakened, or dropped.

## Evidence

### Kernel-check record

Basis: execution (Lean kernel check). Toolchain `leanprover/lean4:v4.34.1`. The whole library (270 declarations) depends on no axioms other than `propext`, `Classical.choice` and `Quot.sound`; the project contains no `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `implemented_by`, `extern` or `unsafe`. Bounded facts use `decide +kernel` (kernel evaluation, no compiled code).

For each Lean name referenced by `results.json` (the fields `lean`, `lean_names`, `nonvacuity_witness_lean`, `positive_control_lean` and the hypothesis field `counterexample`; `lean_names` lists every other package declaration that `REPORT.md` cites by name, under the card whose text cites it, shown as "cited by card k") the table records its role, its axioms (`Lean.collectAxioms`), the SHA-256 of its statement (the Lean `repr` of its type) and the SHA-256 of its definition closure (the sorted lines `name : repr(type)` plus ` := repr(value)` for non-theorems, joined by newlines, over every package constant reachable from the statement; theorem bodies are excluded). For a definition listed in the table, the statement hash covers its type; its body enters the closure hash of every listed statement that uses it. These values are recorded in `audit/statements.json` and `audit/axioms.json` and are recomputed by `support/revalidate.py` (Revalidation).

| Declaration | Role | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
|---|---|---|---|---|
| `ExactCriterion` | cited by card 8 | none | `868abb6b8074587c902e2fe20404f62ca8939f06001138c7ab4618360802075e` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `MulShiftCorrect` | cited by card 1 | none | `868abb6b8074587c902e2fe20404f62ca8939f06001138c7ab4618360802075e` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `SignedRange` | cited by card 11 | none | `44f1ba5afd657ae1f443327e3152e59207199ee258f4174d4f144bf051199b5a` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `allBelow` | cited by card 4 | none | `78b7a7df3b120ccb8b06030afb8e607fd3215001f3598890898a04fecdce1202` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `allBelow_iff` | cited by card 4 | propext | `d420a48166d1bff8d6cd7d09c1e3332a08ac1d56e9df6f241b4d30b9cdda9d9d` | `90649a88c0f03e0eff7bb0e77ecabf62c15153a081a9d5fdc484a35005fd7ae2` (1) |
| `biasDiv` | cited by card 16 | none | `75a45a7ea89bc298b95be7f01c790e80a909afe789be31f09994c06b4defae06` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `biasDivBV` | cited by card 17 | propext | `9c845670e567d10cf1e1787c25910df128bdb6c5371beb9496caf7e0f42a8f7e` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `biasDivBVMasked` | cited by card 17 | propext | `9c845670e567d10cf1e1787c25910df128bdb6c5371beb9496caf7e0f42a8f7e` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `biasDivBVMasked_u8` | result 17 | Quot.sound, propext | `6309caac0bf326719476a158df00d48347c5f6fa3c66a9f0cb0f056fd333021e` | `0ddf220e983573480e9e87caa040c1c2a8bf88a972516648b87cc48008ca016e` (1) |
| `biasDivBV_neg_example` | cited by card 17 | propext | `1eb4dc99f43f0cecc6b596057780a0a17e9c0642fabc5c8b3d35fa0127fc36c3` | `63830447004e4a346273b678280d4c9b1c9010ce615329f8f16270f2f72e0c6c` (1) |
| `biasDivBV_pos_example` | cited by card 17 | propext | `a294d54c937c747c09618d052ffa81be6f0f628e4a375407f02566d6eb72b61e` | `63830447004e4a346273b678280d4c9b1c9010ce615329f8f16270f2f72e0c6c` (1) |
| `biasDivBV_u8` | result 17 | Quot.sound, propext | `8255a992e346144eb258222188679203adac35ed833226f22ef775b6c537c0c3` | `63830447004e4a346273b678280d4c9b1c9010ce615329f8f16270f2f72e0c6c` (1) |
| `biasDivMasked` | cited by card 16 | none | `75a45a7ea89bc298b95be7f01c790e80a909afe789be31f09994c06b4defae06` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `biasDivMasked_eq_tdiv_of_pos_of_lt` | result 16 | Classical.choice, Quot.sound, propext | `73608427abb05d9ef1b3b2fcea3964fb21e5c8cdde311b1c0ccf6a579dcf8628` | `cd94f221d604d7b9fb7bc4470810c6c405fb763fe070a757ff4d61656f00352a` (4) |
| `biasDivMasked_k_zero_failures` | cited by card 16 | Classical.choice, Quot.sound, propext | `f47b25183dbf7e1959f8771cb823ba9fe70b9c3aea99818489731ca41871a78b` | `cd94f221d604d7b9fb7bc4470810c6c405fb763fe070a757ff4d61656f00352a` (4) |
| `biasDivMasked_neg_examples` | cited by card 16 | propext | `7642842e186da133b3815c392729ffd2da9128bb2d341bffcc530609c68c5a68` | `8f8698d49b6034fc374f17147d07207ae713ea0d6cfacb4c73ba39addac325db` (4) |
| `biasDivMasked_pos_examples` | cited by card 16 | propext | `e4d218a5ffe960d4252593a5e5813691d1ab91b2ebc10384ba13e0a503b9fbdc` | `8f8698d49b6034fc374f17147d07207ae713ea0d6cfacb4c73ba39addac325db` (4) |
| `biasDiv_eq_tdiv_of_lt` | result 16 | Classical.choice, Quot.sound, propext | `98665846976823b0c0246119bc9ce8ec4b8a6467baac5302956faba8938ed093` | `25197ef46f7306d0002d175d4a9e9680c0ff016fa3009fff6a6c5b15a81073da` (4) |
| `biasDiv_neg_example` | cited by card 16 | none | `db9dca07346b705850db58e748b19967b711ddebb4d3fdfd7677f054a64d961c` | `e0c766207d2bb270c6da2cc2b8738e4d9bf5c19de89bd59b6a975609bd5f63b2` (3) |
| `biasDiv_pos_examples` | cited by card 16 | none | `42e2acc6fbc1faafc31933cb6834ee4e376898e1c97377400bf281f19854e570` | `e0c766207d2bb270c6da2cc2b8738e4d9bf5c19de89bd59b6a975609bd5f63b2` (3) |
| `biasSum` | cited by card 16 | none | `75a45a7ea89bc298b95be7f01c790e80a909afe789be31f09994c06b4defae06` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `biasSumMasked` | cited by card 16 | none | `75a45a7ea89bc298b95be7f01c790e80a909afe789be31f09994c06b4defae06` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `biasSum_neg_example` | cited by card 16 | none | `2f1030dc673fb24a2781a8ad4b3c090d37fdd4835c52282d6ec84821ede7e91f` | `163809439b0d98a5dfeab139efaf1f8ae6893eff533d1d8aefdf93af35dae094` (2) |
| `bitvec_sdiv_intMin_negOne_wraps` | cited by card 13 | propext | `0e4bd69e8efca1ec219664cb58a2470902f42ea0786013678c2954b7e1fc7d95` | `64b2c1b756c2b4291994b4dd72ddb5e69416630b3482c06e9af71e6ff16b6cc5` (1) |
| `ce_biasDivBVMasked_u8_k_eight` | counterexample 17 | propext | `e22f7db4c50d3a345debcd1e47ee622077fd5be0be9d1dfc787d217c705062f3` | `0ddf220e983573480e9e87caa040c1c2a8bf88a972516648b87cc48008ca016e` (1) |
| `ce_biasDivBVMasked_u8_k_zero` | counterexample 17 | propext | `aacfae8e362e297d7bdc0943a26502ce06eb332d530d80b9be3f6553eeca971e` | `0ddf220e983573480e9e87caa040c1c2a8bf88a972516648b87cc48008ca016e` (1) |
| `ce_biasDivBV_sdiv_k7` | counterexample 17 | propext | `609ea21712ff726b528dd3d12f2632e433a780eed4ea023107110754135f2271` | `63830447004e4a346273b678280d4c9b1c9010ce615329f8f16270f2f72e0c6c` (1) |
| `ce_biasDivBV_width` | counterexample 17 | propext | `c2bb696e3587df7d18c6b41f2f9cf4a1f33dabcbdbb2c11b05b0fd86b2cf20fd` | `63830447004e4a346273b678280d4c9b1c9010ce615329f8f16270f2f72e0c6c` (1) |
| `ce_biasDivMasked_hk` | counterexample 16 | none | `1a8d3b7e8e1314fd97255a90bc5293fb2ff252244be3db05244c99c40063e278` | `cd94f221d604d7b9fb7bc4470810c6c405fb763fe070a757ff4d61656f00352a` (4) |
| `ce_biasDivMasked_hx` | counterexample 16 | none | `0744da27807901f19a342a33b2dd46b7d66af9d6a068146d5800feadaee75112` | `cd94f221d604d7b9fb7bc4470810c6c405fb763fe070a757ff4d61656f00352a` (4) |
| `ce_biasDivMasked_k_zero` | counterexample 16 | Classical.choice, Quot.sound, propext | `2de92d4789f3d40c8a0c262817014834d99736776a05d82731f2a10ec9a536c5` | `cd94f221d604d7b9fb7bc4470810c6c405fb763fe070a757ff4d61656f00352a` (4) |
| `ce_biasDiv_hk` | counterexample 16 | none | `ee31d17559edbd77eb6a283d4e066d708fbf067e009caad24fdfa03eff3801a4` | `25197ef46f7306d0002d175d4a9e9680c0ff016fa3009fff6a6c5b15a81073da` (4) |
| `ce_biasDiv_hx` | counterexample 16 | none | `d36b1ae93ecdc36112faf88051c25cc5a8a86622cd995efbdc8f05d76bd69ddf` | `25197ef46f7306d0002d175d4a9e9680c0ff016fa3009fff6a6c5b15a81073da` (4) |
| `ce_ceilDiv_succ_premise` | counterexample 10 | none | `2721b65ad14652dd047d2c1f4fec271f73c4e3decacbe1dcc76e37f01611b01e` | `ddc2ee3af60ba428839fe973d4594d581696df9502fd159d5dd7e84d9c69fc0d` (2) |
| `ce_directRem_hhi` | counterexample 20 | none | `77638a3874f9ad205b6322f650a58d75aaaff4802f15d77f1d3f376c3f5c5631` | `2f9d8b923b32013363801826b88acba864c7c7e402af022a26aa772fe72461f2` (1) |
| `ce_directRem_hlo` | counterexample 20 | none | `c44def73e5988bb6d5968bff401dedf4e0ea4446057e54b1b3f52352f64760ee` | `2f9d8b923b32013363801826b88acba864c7c7e402af022a26aa772fe72461f2` (1) |
| `ce_directRem_input_range` | counterexample 20 | none | `19e89b949fea3f056ada5d69060a72f8e3485c083eda733da06beadf25ce7cd2` | `2f9d8b923b32013363801826b88acba864c7c7e402af022a26aa772fe72461f2` (1) |
| `ce_directRem_quotient_valid_multiplier` | cited by card 8 | none | `e7a7f7842afeb151a58fb7645febf741bd97e18e1bb1b3edd79161e4ddd25dcc` | `8df63a68c19ae45158b5802ac6bd66e63cdbe5be815277543204d94be4390f24` (6) |
| `ce_exactCriterion_d_zero` | counterexample 8 | none | `9daf2aab5db84e1762cb977365df57b6cb50ff00edc1fcb269a876f9a111fa3b` | `660ad0cc48e85176c51b5ad14eb0dc75b1e849ac6b9128eb2157bb418647ca11` (3) |
| `ce_exactCriterion_hdN` | counterexample 8 | none | `86f9cfc8773242201991861e3c939b14ba2d212894f8a4c5e8e07d2e8211f4b2` | `660ad0cc48e85176c51b5ad14eb0dc75b1e849ac6b9128eb2157bb418647ca11` (3) |
| `ce_exactCriterion_u8_d_256` | cited by card 8 | none | `a8ffaa59628a28462cd19fe9f41266771d770646fbb9a6cd87dd5f2a1f19a2c8` | `660ad0cc48e85176c51b5ad14eb0dc75b1e849ac6b9128eb2157bb418647ca11` (3) |
| `ce_exactCriterion_u8_d_zero` | cited by card 8 | none | `cdcfc3f44e1a8fbcbe45f9a454b35c21c3888cef18027a16bb8d3db44d863c20` | `660ad0cc48e85176c51b5ad14eb0dc75b1e849ac6b9128eb2157bb418647ca11` (3) |
| `ce_exists_ceilDiv_hdN` | counterexample 9 | none | `32193a7a521b63be57db85ecbec8aaabe6b11b054d7df89466b4f4f60e29f433` | `ddc2ee3af60ba428839fe973d4594d581696df9502fd159d5dd7e84d9c69fc0d` (2) |
| `ce_fixupQuot_correct_h` | counterexample 5 | none | `72660144eaf07728b0f4a57826d8181a2e490ec38af90a9b3a236ee96f62187f` | `b66cfefaa98855b9e4411f9360048497d0449715d2d528924c41467d883c9161` (1) |
| `ce_fixupQuot_correct_hl` | counterexample 5 | none | `8ee972edce3b2577627fa6a32197e7990b651f4a1c6c767ca6c8277d9f785026` | `651a196c9bff2175025f09eecfdad5a5433d5a325abbb83fd6f5cd65b270b57d` (2) |
| `ce_fixupQuot_correct_hm` | counterexample 5 | none | `be33c8ae4fde433df872a36c5957131b3fe290d00870042a0bfd978885916ce6` | `651a196c9bff2175025f09eecfdad5a5433d5a325abbb83fd6f5cd65b270b57d` (2) |
| `ce_fixupQuot_correct_input_range` | counterexample 5 | none | `f73c43d0c78163afe2210fe2731d6b8be4d8a73ac2d7e5bbed83019a5c1d987d` | `651a196c9bff2175025f09eecfdad5a5433d5a325abbb83fd6f5cd65b270b57d` (2) |
| `ce_fixupQuot_eq_wide_hl` | counterexample 5 | none | `aca71706971a0d6bce0f75351c4c5f7b6c02c84065df3d7e698455b54f8052fb` | `b66cfefaa98855b9e4411f9360048497d0449715d2d528924c41467d883c9161` (1) |
| `ce_fixupQuot_eq_wide_hm` | counterexample 5 | none | `7227532b937a26eae4021aa62065f3ea240fec30b8574c927dd0813665f7564f` | `b66cfefaa98855b9e4411f9360048497d0449715d2d528924c41467d883c9161` (1) |
| `ce_fixupQuot_unsignedMagic_d_one` | counterexample 6 | none | `000f17c5debc1643b9eee1ea412df6d0fd9e156f09f7a1e7ce3c864bd6f4bb6f` | `e5f1e1d279216aa35c59ae45ef88ea1a00a84c3b8722c50eaf261bcd1a26fc7e` (4) |
| `ce_fixupQuot_unsignedMagic_input_range` | counterexample 6 | none | `2669885a6c22abb5688313c484054aee70d72b6b5862e0d6f83b6e293dbf34aa` | `e5f1e1d279216aa35c59ae45ef88ea1a00a84c3b8722c50eaf261bcd1a26fc7e` (4) |
| `ce_fixupQuot_unsignedMagic_u16_div7_x_range` | cited by card 6 | none | `e115cf868ea3fe004f9fb8711dc3a18359e26fd345c70f17829ce26121ec9de6` | `e5f1e1d279216aa35c59ae45ef88ea1a00a84c3b8722c50eaf261bcd1a26fc7e` (4) |
| `ce_fixupQuot_unsignedMagic_u8_d_one_canonical` | cited by card 6 | none | `ef4399d6218d6b9536e0510be57f2f78b6092087772543a77f883d892001a6e2` | `e5f1e1d279216aa35c59ae45ef88ea1a00a84c3b8722c50eaf261bcd1a26fc7e` (4) |
| `ce_fixupQuot_unsignedMagic_u8_x_range` | cited by card 6 | none | `4f05004deacedb00ff8e3596d1e045e37ff36237771ffd323ea0a41a46278f9c` | `e5f1e1d279216aa35c59ae45ef88ea1a00a84c3b8722c50eaf261bcd1a26fc7e` (4) |
| `ce_minimal_shift_u8_div7_input_range` | counterexample 7 | Quot.sound, propext | `fdd05113a1c8922e3026a1a6e91f18f0aba1d7dd1d2a5e08e45a407dd12348d6` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `ce_minimal_shift_u8_div7_s_bound` | counterexample 7 | none | `295e0f1931f99eb0415b3f4fde529d35c23aa76bad684dc6b75a724d72de90a0` | `239638794d05a78400a184733b2444262e70466839b7123715ab3bc63eb4e606` (1) |
| `ce_no_single_word_u8_div7_m_bound` | counterexample 7 | none | `6869ce7c0547b5896ad424d7eb31c63fcf82be5ec15187b46ec80f0211a7ba28` | `239638794d05a78400a184733b2444262e70466839b7123715ab3bc63eb4e606` (1) |
| `ce_rem_correct` | counterexample 18 | none | `f832b471d74f736a9d396d750fdee5fd7f37cc4631d869617f90eddd0cec2c3b` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `ce_rem_input_range` | counterexample 18 | none | `0680dd1a283561b98887bb88dd1cbb554a4a02bbc5c88efc923c8b019032fccc` | `239638794d05a78400a184733b2444262e70466839b7123715ab3bc63eb4e606` (1) |
| `ce_sandwich_hhi` | counterexample 1 | none | `126bf15b2781c3d0e744182f7efab6ff0df42639c09bd0a9a7678253a828394f` | `239638794d05a78400a184733b2444262e70466839b7123715ab3bc63eb4e606` (1) |
| `ce_sandwich_hlo` | counterexample 1 | none | `d01c49114a8982e9bd48abe40cac5edaaf07fa845772dd053be2e5774b2d663e` | `239638794d05a78400a184733b2444262e70466839b7123715ab3bc63eb4e606` (1) |
| `ce_sandwich_input_range` | counterexample 1 | none | `7b97d3f15918c3ff14070da4a0ff092a8bef13254410709e71765361ebee80dd` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `ce_sdiv_hhi` | counterexample 11 | none | `d7e624a577744bc8a9c97fb769c46c2ca2181c6e72c825dbbb2c3320f2d79fcf` | `53480c3781894c34e2be13ba88f61f5fdc21620cf56e8e8db5ca604a9a5606f4` (2) |
| `ce_sdiv_hlo` | counterexample 11 | none | `3625c1ea4f45cf29d2852767d02b6de20e6eda7863558fc87ab5ca6d06861896` | `53480c3781894c34e2be13ba88f61f5fdc21620cf56e8e8db5ca604a9a5606f4` (2) |
| `ce_sdiv_range` | counterexample 11 | none | `0c22bdcf8d48de74adb320807424c9781626631fa807ef0ce5c0e94365352bbd` | `47d0b0a7c4cf51460ced7ec29ddff7b76c8459a93f706636c41f83f9101db3b9` (1) |
| `ce_signedMagic_d_zero` | counterexample 14 | none | `d6faed1b8c68c56a7b137dcae1e2d53a89c99bc7f28c3ffe0826c070315f8a96` | `5ac87a04d8095d426edad9ececa6378f2ca069ef0e66997e0ba3b89a309acb4c` (2) |
| `ce_single_word_hN` | counterexample 4 | none | `3d44d38bb76a61cda5fcae4006f2ec08bae1883f3111ea361d827601d84583a5` | `f42cff25440951c26a88a2542ce3c181934d0cc8282e7d48e138174e2beb9b9e` (4) |
| `ce_single_word_hdN` | counterexample 4 | none | `43609f67f144c2c82671e097a1614b7cc86ee8dad3b24249edee886f11b989a4` | `f42cff25440951c26a88a2542ce3c181934d0cc8282e7d48e138174e2beb9b9e` (4) |
| `ce_srem_hhi` | counterexample 19 | none | `fbec9dbe23b6238291fd172da5af309a39bd9d786979184aa4cbcb7c4a38e9b4` | `06bbd1c1d6bf407f617a4300bf3c548615c6e9fb5f025e0c6c81814eb7f85a97` (3) |
| `ce_srem_hlo` | counterexample 19 | none | `77a7281cb8655e99141a109ebbca285dcdef340659a0b807dfe9e3ada29b4540` | `06bbd1c1d6bf407f617a4300bf3c548615c6e9fb5f025e0c6c81814eb7f85a97` (3) |
| `ce_srem_range` | counterexample 19 | none | `d5b673e0fec6286e50c0fe9df7a3ce64133ae2f359fd04ef9322cd1cdd22dbfd` | `8bd9fbb8059d165aa32c8fbdfd3a2996ef44de68b38f689f0ae9e38936e01fcb` (2) |
| `ce_srem_uncorrected_sign` | cited by card 19 | none | `89425b4209da327e51b7ccbf3df059eccbc37a1f36229aac1eaec9a986795717` | `789d09d4b19d01cfea6fd17368a35b5f52bc00139834db84dd1644b859e23c02` (1) |
| `ce_tdiv_signedRange_hx` | counterexample 13 | none | `0700d513537c629eb85dae7eee763b1799762cc3eb0bc87ed227de4f1bf9d652` | `64b2c1b756c2b4291994b4dd72ddb5e69416630b3482c06e9af71e6ff16b6cc5` (1) |
| `ce_two_pow_le` | counterexample 8 | none | `1cf2d3aa60bc7b206ccbd9236abade704cf06a80868af65a271be0dd4f480c27` | `239638794d05a78400a184733b2444262e70466839b7123715ab3bc63eb4e606` (1) |
| `ce_uncorr_hhi` | counterexample 12 | none | `e9d393c3eca79063abb9428e25019c03068aef4785b145d902bc746943f0cacb` | `85fa77043fa85bfb93d680c85c5b2fd9dffb9ed4bfa862bb7982b58095191df7` (2) |
| `ce_uncorr_hlo` | counterexample 12 | none | `0dddf7168d183a70b50111302d017f1c4bcb286e6217a90e66fec0eef501442f` | `85fa77043fa85bfb93d680c85c5b2fd9dffb9ed4bfa862bb7982b58095191df7` (2) |
| `ce_uncorr_neg` | counterexample 12 | none | `f55b47eae1f06f3b1307f3d63def699a5c3c3fe5bd9e440c3b43a4f5da6c285b` | `85fa77043fa85bfb93d680c85c5b2fd9dffb9ed4bfa862bb7982b58095191df7` (2) |
| `ce_uncorr_range` | counterexample 12 | none | `434edbf752ebe0f946dc0cde9482186bf04e113fa260173a43527a833ffcc143` | `789d09d4b19d01cfea6fd17368a35b5f52bc00139834db84dd1644b859e23c02` (1) |
| `ce_unsignedMagic_ge_two_pow_d_zero` | counterexample 3 | none | `7e414c969b87fe49dd26fa19710fa92da16832362cbb0fbbfecbc76622863bb0` | `f3632b6d81782585f6f06cf7e52b9980974f172959a31389f3f9a9e8cf131e0d` (3) |
| `ce_unsignedMagic_low_d_zero` | counterexample 3 | none | `9cf1c12a333ee1ae0693feacc1d99eb122029b2e949270320bcf7317f66396eb` | `f3632b6d81782585f6f06cf7e52b9980974f172959a31389f3f9a9e8cf131e0d` (3) |
| `ce_unsignedMagic_low_hd` | counterexample 3 | none | `eba5e014f10d8b188596c8ac1be835c8ec97d77c274f0b152bbb1e9f0ddc6508` | `f3632b6d81782585f6f06cf7e52b9980974f172959a31389f3f9a9e8cf131e0d` (3) |
| `ce_unsignedMagic_lt_two_pow_succ` | counterexample 3 | none | `31fdc4c65a77865e03d2ede611e685beda9dc51d0c5d0fd9e42bdd33bbc898bd` | `f3632b6d81782585f6f06cf7e52b9980974f172959a31389f3f9a9e8cf131e0d` (3) |
| `ce_unsignedMagic_sandwich_d_zero` | counterexample 2 | none | `159695db316f206ba15bb5e0eb1a98988315096250f749cbe3fdef6ccbdbe0cc` | `f3632b6d81782585f6f06cf7e52b9980974f172959a31389f3f9a9e8cf131e0d` (3) |
| `ceilDiv` | cited by card 1 | none | `481f0060f2f380f36cc958d245a5fdb9f5bc3554271d8070964a26c347c832a8` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `ceilDiv_le_of_le_mul` | cited by card 9 | Quot.sound, propext | `2716aeb5b1dfa2a48c4d44819378941de3573adb4e1d893ca396114746abc39b` | `4f56e9b6ade16689ca7890a92b5056f309cb31303d6efcbcd790065b2ab6e13f` (1) |
| `ceilDiv_neg_example` | cited by card 1 | none | `699477c5dd9086fd9e73cabc92cb03b2d1d551fe49b491404eddcf7d18744459` | `4f56e9b6ade16689ca7890a92b5056f309cb31303d6efcbcd790065b2ab6e13f` (1) |
| `ceilDiv_pos_examples` | cited by card 1 | none | `a080984a859903cc35def6ca1fa162dc48a5e4c5152efd1a443f1e9d3004d56a` | `4f56e9b6ade16689ca7890a92b5056f309cb31303d6efcbcd790065b2ab6e13f` (1) |
| `ceilDiv_succ_leaves_single_word_u8_div3` | cited by card 10 | none | `98601db2f20fdaaff218bda6e2a4ac1f187f530397f827a9cf0991e8bb15b654` | `ddc2ee3af60ba428839fe973d4594d581696df9502fd159d5dd7e84d9c69fc0d` (2) |
| `clog2` | cited by card 2 | none | `57d9f15e0e19cb13841e2eade77ec4269dfa46ea06c3932b6019faa6c5096e11` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `clog2_neg_examples` | cited by card 2 | none | `11b81dc585b2c24e4f0b40c862b959645b6c87df70347115bc10253f010bfa33` | `fc70e1c376ecec941e89c06339c491e93dde37ffd550b7a5bfba2707ad9cfa9a` (1) |
| `clog2_pos_examples` | cited by card 2 | none | `3be00e61b86945fe75f2dad206f956b73da3e5a87138d9dff6f14246098afd92` | `fc70e1c376ecec941e89c06339c491e93dde37ffd550b7a5bfba2707ad9cfa9a` (1) |
| `correctB` | cited by card 4 | none | `21d0de6002e84ce4d012ad414f862ae57aaa134e63c3017a42a8ae61fb8ca692` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `correctB_iff` | cited by card 4 | Quot.sound, propext | `8cfadf48205fab294df60e0f58def05d979d58c7d8325a9a9f9eb9a253907d26` | `214ba0f1480f1732b0cf9744c37e5ddd35642b1e13ebae9d07e15cf5616247c3` (3) |
| `count_no_single_word_u8` | cited by card 4 | none | `cb1d4c93746e411c40d3bd2db8feb3cbd513b95e7bc4efa4ae43f800232d2e71` | `8e4232e90deee2d88f1c2275745869ff64a131ddeba78536ddcb3e9b88706161` (6) |
| `count_single_word_u8` | cited by card 20 | none | `3986545baa38b0e4a2ac9eb2597cb04994aa0cc23bd5354be80ac5fb0ba7dc81` | `8e4232e90deee2d88f1c2275745869ff64a131ddeba78536ddcb3e9b88706161` (6) |
| `count_single_word_u8_directRem_fails` | cited by card 20 | none | `a3818a395c4a77f9e0ed449e3464d615c96a487b90b397eb38ce2507260f71ed` | `aabaaff89218117176b45c30670e90f7f7d233419a869e5d6952c49861feb59c` (8) |
| `directRem` | cited by card 20 | none | `2f88cc0f4fc1b9a6b8877fe15657029736673d3d9f71d61387213e74ec89a07a` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `directRemB` | cited by card 20 | none | `0fd4bd1a0e128b02bc5945e702082920f506105f670b03f72a24d4b6dbd63459` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `directRemB_iff` | cited by card 20 | Quot.sound, propext | `adb6baffe4d823cfbc5fe6763b5e8637776fffb3d4a2cda11e9f10f746452043` | `acc1b1de6d99a04fc2142d6a2c759583f818747cf2ccef2c62c9a084509f22bd` (3) |
| `directRem_eq_mod_of_sandwich` | result 20 | Classical.choice, Quot.sound, propext | `c26c1664a71ced43b751b086bb4ea339cfd9427ee493ec0ccbd0adc70f3c82c2` | `2f9d8b923b32013363801826b88acba864c7c7e402af022a26aa772fe72461f2` (1) |
| `directRem_neg_example` | cited by card 20 | none | `94b63da8ff307d86861757f4966824ae8ecf01f7bcb9805777b87f51331e06bc` | `2f9d8b923b32013363801826b88acba864c7c7e402af022a26aa772fe72461f2` (1) |
| `directRem_pos_example` | cited by card 20 | none | `e7e3cde3f2123aec86caf986f07f0022f9450cdcfa27feb1a2399cf347856ca2` | `2f9d8b923b32013363801826b88acba864c7c7e402af022a26aa772fe72461f2` (1) |
| `exactCriterion_neg_examples` | cited by card 8 | none | `d73f0750e173c8be632444d56fdc45ed350c8e9c5dfad482c74e0d273038d2ba` | `b03cd57f0919cd22b96b9665263486524a4a5d5c8d56cc87520e0200668782fd` (2) |
| `exactCriterion_pos_examples` | cited by card 8 | none | `381775dfd46b3ae47ec03a199e4e9acfc91d71249990ec41b9abebe57515ba17` | `b03cd57f0919cd22b96b9665263486524a4a5d5c8d56cc87520e0200668782fd` (2) |
| `exists_mulShiftCorrect_iff_ceilDiv` | result 9 | Quot.sound, propext | `a43f01c48b84b0e3aa0eebfdf2beab9b23890fd352688cf659482ffbc16edc0a` | `ddc2ee3af60ba428839fe973d4594d581696df9502fd159d5dd7e84d9c69fc0d` (2) |
| `exists_mulShiftCorrect_iff_ceilDiv_d_zero` | cited by card 9 | propext | `693c5d9a56ed3cbd10e7617d9039a66fd53b5262895f4fd0c63bc0de5d217466` | `ddc2ee3af60ba428839fe973d4594d581696df9502fd159d5dd7e84d9c69fc0d` (2) |
| `fixupQuot` | cited by card 5 | none | `0e18d0e90cdcdf5e3b869bac5369f3c2f4e61adccd92c1a6cb7f3e96b8bc5e7f` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `fixupQuot_correct` | result 5 | Quot.sound, propext | `22ed1dc67f78b4787170201b1a04d3d66382241b621d3e8542d22363d76c3125` | `651a196c9bff2175025f09eecfdad5a5433d5a325abbb83fd6f5cd65b270b57d` (2) |
| `fixupQuot_eq_wide` | result 5 | Quot.sound, propext | `1e6841884023fdae0e1a74d482e859b03c81a48ec57306a180ff20119d9223f0` | `b66cfefaa98855b9e4411f9360048497d0449715d2d528924c41467d883c9161` (1) |
| `fixupQuot_neg_example` | cited by card 5 | none | `4b483e99165cd85a9d4e599dac9dd210f294b622591d44dc7cf8aae8c2378120` | `b66cfefaa98855b9e4411f9360048497d0449715d2d528924c41467d883c9161` (1) |
| `fixupQuot_pos_examples` | cited by card 5 | none | `f352144ada0fcb67169a74a5b572eb307681d7615ff33ad4fb399e3d1d2b21c7` | `b66cfefaa98855b9e4411f9360048497d0449715d2d528924c41467d883c9161` (1) |
| `fixupQuot_shift_eq_width` | cited by card 3 | Quot.sound, propext | `76c48239627de441bd3f367c42ba518705f5fc94383d41c63b9cabb53410a3cf` | `fc70e1c376ecec941e89c06339c491e93dde37ffd550b7a5bfba2707ad9cfa9a` (1) |
| `fixupQuot_shift_lt_width` | cited by card 6 | Quot.sound, propext | `f8227fd770eb5dbb26f975e222574776e29fe27c99c570439fb2e6260874b637` | `fc70e1c376ecec941e89c06339c491e93dde37ffd550b7a5bfba2707ad9cfa9a` (1) |
| `fixupQuot_shift_lt_width_iff` | cited by card 6 | Quot.sound, propext | `255afdb3f8ea7bd370f9fcf20ae26682f101925fe52248ff2341d5e56cc4996d` | `fc70e1c376ecec941e89c06339c491e93dde37ffd550b7a5bfba2707ad9cfa9a` (1) |
| `fixupQuot_shift_width_u8_d300` | cited by card 6 | none | `412a5a6aeae31d374acfd7980b88cde7001f2d413cf31b09d1a6e7a021126db8` | `fc70e1c376ecec941e89c06339c491e93dde37ffd550b7a5bfba2707ad9cfa9a` (1) |
| `fixupQuot_unsignedMagic_correct` | result 6 | Classical.choice, Quot.sound, propext | `18404efa641f91ae0fba4a6180b95707d20d69083eb0bbc24c9a6cb304f851f0` | `e5f1e1d279216aa35c59ae45ef88ea1a00a84c3b8722c50eaf261bcd1a26fc7e` (4) |
| `fixupQuot_unsignedMagic_u16_div7` | cited by card 6 | Quot.sound, propext | `871c09deb87d6b2857faca74ceac00351c2233b8f06059dde9a993a15947ad6b` | `e5f1e1d279216aa35c59ae45ef88ea1a00a84c3b8722c50eaf261bcd1a26fc7e` (4) |
| `fixupQuot_unsignedMagic_u8` | cited by card 6 | Quot.sound, propext | `62fd7d1130b43b19100098c81468cc0df84cf2d32de6d05c785f52e1c7dcdd23` | `e5f1e1d279216aa35c59ae45ef88ea1a00a84c3b8722c50eaf261bcd1a26fc7e` (4) |
| `int_shiftRight_eq_tdiv_iff` | result 15 | Classical.choice, Quot.sound, propext | `4c56175263d6e8790d25250f4bd1e9491d048efd36628dfef690c46daf21d60c` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `lastFullBlockEnd` | cited by card 8 | none | `89d358c33069524cef5266c160ae7d5b1cf43b1b2b10526b0483f2468efc9327` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `lastFullBlockEnd_neg_example` | cited by card 8 | none | `b19dc2c7d59a373bbbb75314a82d9eb43d20619d235c5eb3a8003a8775dac123` | `d8980f5d908dbb285d1ab812ee01aeada7effccd6d28c74177e48cbeed67f354` (1) |
| `lastFullBlockEnd_pos_example` | cited by card 8 | none | `0dc339cb6294ee3a8c0983c6d3c122e36f683997df740b0e3dd8fe85c1534c4d` | `d8980f5d908dbb285d1ab812ee01aeada7effccd6d28c74177e48cbeed67f354` (1) |
| `le_ceilDiv_mul` | cited by card 1 | Quot.sound, propext | `d273e9949f1faf02b66ecda3f28fdd1b7e1eca47c06e3e53eb3ab0d81d8eb3b7` | `4f56e9b6ade16689ca7890a92b5056f309cb31303d6efcbcd790065b2ab6e13f` (1) |
| `lsrN` | cited by card 16 | none | `1ac855b5dc2b16b545a392740d6aa68d1d81fea7445db7d0ce8b077e00c21b2a` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `lsrN_neg_example` | cited by card 16 | none | `f6a933027052c57ad7121263c42e665bc6aa33a898410e70bc198ae1e4336610` | `995392a103b216cd5f0927332328c69a414b1033aa5ea7f31a4c97d5dab562f0` (1) |
| `lsrN_pos_examples` | cited by card 16 | none | `f80bd170b0b80ec68ebbd6461bde46b0474ea0941725c2fdbd072ce96dfa4377` | `995392a103b216cd5f0927332328c69a414b1033aa5ea7f31a4c97d5dab562f0` (1) |
| `magic_neg_examples` | cited by card 2 | none | `3a69a83efe57952872fd8a801f86a82451e6f909806e47069a6ecea9a25adee1` | `b0f7399479c8bcd99b7f3bd7c16d886afd06c7874656173cad2394fc140699a7` (5) |
| `magic_pos_examples` | cited by card 2 | none | `314bfb385ba82c7ffa48a2d7de3aa1dace365e5f9eee748b8fbf56cc6d379f7a` | `b0f7399479c8bcd99b7f3bd7c16d886afd06c7874656173cad2394fc140699a7` (5) |
| `minimal_shift_u8_div7` | result 7 | Quot.sound, propext | `2961e0e8c5d7f566115734b6b34fd404b772d411117c067046410fd80d9e865f` | `239638794d05a78400a184733b2444262e70466839b7123715ab3bc63eb4e606` (1) |
| `mulShiftCorrect_ceilDiv_succ` | result 10 | Quot.sound, propext | `9ce5171aabf0f463b6eb4c2fe6356ec6136c07c8ba156a3f233328006379de2d` | `ddc2ee3af60ba428839fe973d4594d581696df9502fd159d5dd7e84d9c69fc0d` (2) |
| `mulShiftCorrect_iff_exactCriterion` | result 8 | Classical.choice, Quot.sound, propext | `ed5d7196b91dad5fcfe672700e962fd979db1e51caac36c675c9bb4817d54f36` | `660ad0cc48e85176c51b5ad14eb0dc75b1e849ac6b9128eb2157bb418647ca11` (3) |
| `mulShiftCorrect_iff_exactCriterion_u8` | cited by card 8 | Quot.sound, propext | `7afe40dfde83173bcd3b88b530ef81f095446511b62225562779cab3af252f69` | `660ad0cc48e85176c51b5ad14eb0dc75b1e849ac6b9128eb2157bb418647ca11` (3) |
| `mulShiftCorrect_iff_of_two_pow_le` | result 8 | Quot.sound, propext | `bf7ff3745ae71adec285f696986ffdd82a30c65fcc6058024ca53a5efc81bcb3` | `239638794d05a78400a184733b2444262e70466839b7123715ab3bc63eb4e606` (1) |
| `mulShiftCorrect_neg_examples` | cited by card 1 | none | `7e8c0fd7e7f78f38e6848512232f31f0f53b2819c6ec76e4cfc25ef44c0b05a6` | `239638794d05a78400a184733b2444262e70466839b7123715ab3bc63eb4e606` (1) |
| `mulShiftCorrect_of_sandwich` | result 1 | Classical.choice, Quot.sound, propext | `b8f5c8e6c730dbe520eda9498a62fc8bc3aedec8df411a497c708850ef7fa6ec` | `239638794d05a78400a184733b2444262e70466839b7123715ab3bc63eb4e606` (1) |
| `mulShiftCorrect_pos_examples` | cited by card 1 | none | `9d0edffd8f94f94d895dd7a6e7bb940e57aaadbef5d5021ade7331a6f18a9c2b` | `239638794d05a78400a184733b2444262e70466839b7123715ab3bc63eb4e606` (1) |
| `mulShiftCorrect_u32_div641_shift32` | cited by card 4 | Classical.choice, Quot.sound, propext | `bab38630f152f44187fd4ada730af3d6be6d90f7805e3132b54eac55107cf7ca` | `37055a21f3a5cca10baeba12a3090140e03aef32b95f625c40dffc875ce729de` (3) |
| `mulShift_rem_eq_mod_of_correct` | result 18 | Quot.sound, propext | `8174954189b320be88515310e8f0a4f0fa01085583fc2fda6baec8fd37b04cdd` | `239638794d05a78400a184733b2444262e70466839b7123715ab3bc63eb4e606` (1) |
| `mulShift_rem_eq_mod_of_sandwich` | cited by card 18 | Classical.choice, Quot.sound, propext | `048545a3851e96274f2cc4738937c1d77593b8edd6db1a9155d6b331fb6a6039` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `mulShift_u8_div7_below_209` | cited by card 3 | Quot.sound, propext | `72066a3bdefa991e800c56e3f2a4f073177cf24b40d7e5a3c651b2f451f3db63` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `no_single_word_multiplier_u8_div7` | result 7 | Quot.sound, propext | `fa43b1e628a57cd4e92a19157af034618551f7a1b591d2227bc8897460302c4e` | `239638794d05a78400a184733b2444262e70466839b7123715ab3bc63eb4e606` (1) |
| `not_mulShiftCorrect_div_one_of_width_le` | cited by card 4 | Quot.sound, propext | `db32ddb2f39415c7ca59f44ad3c32cd3913e63b44253873338f1550d89e644bf` | `239638794d05a78400a184733b2444262e70466839b7123715ab3bc63eb4e606` (1) |
| `not_mulShiftCorrect_of_gt_at` | cited by card 7 | Quot.sound, propext | `809b1e41ac2b27699987e913d944625436e4e293b27ca7a8c5ec3f078f651638` | `239638794d05a78400a184733b2444262e70466839b7123715ab3bc63eb4e606` (1) |
| `not_mulShiftCorrect_of_mul_lt` | cited by card 7 | propext | `852a136ee2905b137187f34fa5eb51da9b33cff939cd5ebda26f02d57d200693` | `239638794d05a78400a184733b2444262e70466839b7123715ab3bc63eb4e606` (1) |
| `nv_biasDiv` | non-vacuity 16 | none | `d8a19ea8a756f5026f599c57880b9c880dc9d31475cc75626407700af8f33f59` | `64b2c1b756c2b4291994b4dd72ddb5e69416630b3482c06e9af71e6ff16b6cc5` (1) |
| `nv_biasDivBV_u8` | non-vacuity 17 | none | `48e94448992c95ce69349f00899d0c46ec87e175872e127c98dd2c1523b80372` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `nv_ceilDiv_succ_u8_div7` | non-vacuity 10 | none | `40b2952755851530c03d850e417ffd245d795d750c49a3acc71a24a197c7374c` | `ddc2ee3af60ba428839fe973d4594d581696df9502fd159d5dd7e84d9c69fc0d` (2) |
| `nv_evaluated_instances` | cited by card 6 | none | `0954d23678eea697be9b62082604f77abed8cec3bcd0777411c268e3e01e0f2e` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `nv_exact_u8` | non-vacuity 8 | none | `33111e1536b0a28782b4634012918c9e23af4c21fef5d9570f9721ecee0f01e0` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `nv_exact_u8_div7` | non-vacuity 9 | none | `47c6ffae1351ac7e97f5b00eb8d1d9e434ef8803e8ba6ace370f84c7d61a62c0` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `nv_fixupQuot_correct_u8_div7` | non-vacuity 5 | none | `6430902910e54b196f9c24570bb1027cee13b53993d3c10d04c2752d845722f9` | `239638794d05a78400a184733b2444262e70466839b7123715ab3bc63eb4e606` (1) |
| `nv_fixupQuot_unsignedMagic` | non-vacuity 6 | none | `37e73ba43260f59408ee140fc3a4fcac78fdfa1b7383fa4e55591f961e7ffc78` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `nv_int_shiftRight` | non-vacuity 15 | none | `ee69eb5dae92a1de171b95e464310271c2cac985fc3a94972f16f91bee7b4841` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `nv_mulShift_rem` | non-vacuity 18 | none | `c5d1dacc5ac76bbf5d491816d0885b94b17f913b9df54e19460a864d97356ebf` | `239638794d05a78400a184733b2444262e70466839b7123715ab3bc63eb4e606` (1) |
| `nv_no_single_word_u8_div7` | non-vacuity 7 | none | `6d09f36cf463a92e8dad192803ae162ee22559027fcc842eebd4037638c0e26d` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `nv_sandwich_u32_div7` | non-vacuity 1; non-vacuity 20 | none | `6219562849201b2aea0eba1fc94375d5f2ef0179e425c812a0ef757cb955e708` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `nv_sdivMagicUncorrected` | non-vacuity 12 | none | `11166bf121c6e679c2bf63d0f69acbe461ad0f4f194bbce7d2c04519463db8e2` | `64b2c1b756c2b4291994b4dd72ddb5e69416630b3482c06e9af71e6ff16b6cc5` (1) |
| `nv_signedMagic_sandwich_div7` | non-vacuity 14 | none | `4b8755109762aa501459c8fbcafb5895b32d56576da7b78cf25dfa018f8f3948` | `5ac87a04d8095d426edad9ececa6378f2ca069ef0e66997e0ba3b89a309acb4c` (2) |
| `nv_signed_sandwich_i32_div7` | non-vacuity 11 | none | `398a81fcf72b9c852fec783abbed6de54e884c4d859ae27a74fcfd8d2e105734` | `728ffa7a87ef1fb96d0b681f19c97a0a25308723d9aaad5ef4b2a2783994654d` (3) |
| `nv_single_word_u8_div7` | non-vacuity 4 | none | `370aa1041be874e3ea4b67053866d371d6e0a46449391a6938f1a5090b949a5e` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `nv_sremMagic_both_signs` | non-vacuity 19 | none | `36b2315d521fb431ee4b8282db2c208cd92c3935a041ae7fc63352ca867ef2d0` | `64b2c1b756c2b4291994b4dd72ddb5e69416630b3482c06e9af71e6ff16b6cc5` (1) |
| `nv_tdiv_signedRange` | non-vacuity 13 | none | `7d81404e8d1a64e6c65557f4a4e43a4c0ee8912fe9d1f1a900011e249be154ca` | `64b2c1b756c2b4291994b4dd72ddb5e69416630b3482c06e9af71e6ff16b6cc5` (1) |
| `nv_unsignedMagic_bounds` | non-vacuity 3 | none | `04763b5dacb93ab3ab96562dd7c15cf82765ae03a9ea64d313ae84a2827d4086` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `nv_unsignedMagic_sandwich_div7` | non-vacuity 2 | none | `6b4392fdb50d2116163d6f2e835462d20d1c4d965638cf9dfe90101e327ac548` | `f3632b6d81782585f6f06cf7e52b9980974f172959a31389f3f9a9e8cf131e0d` (3) |
| `one_le_clog2` | cited by card 14 | Quot.sound, propext | `2e2424b86841e314464a458c3d2858813be716fd6a1c0b9f4a807035820d9dac` | `fc70e1c376ecec941e89c06339c491e93dde37ffd550b7a5bfba2707ad9cfa9a` (1) |
| `pc_div7_u8_nine_bit_multiplier` | positive control 7 | none | `4ff31d6f8b7b6e417d4632ae1a5435c2b11cafc7962f283c9aa895635bcf5187` | `239638794d05a78400a184733b2444262e70466839b7123715ab3bc63eb4e606` (1) |
| `pc_single_word_shift_fits` | cited by card 2 | none | `ea3a72583522e7ae3d97f7632409e4512a80a50bc5ccb53745b98cbfc184f8a3` | `7c81305cf419666eb848f7bb054eecd305c251d33be4ba3686d9923974cb13d6` (5) |
| `pos_of_two_pow_le_mul` | cited by card 1 | none | `6e8752ac164a8b96d14bede159d20ca253720fe1480f94d486ed19b63c4aa34c` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `robison_multiply_add_u8_div7` | cited by card 3 | Quot.sound, propext | `4ad41341e85df87d443d793a8352c7358a12dbf2ca1045f249c96d9858aef1f2` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `sandwich_iff_directRem_bound` | cited by card 20 | Classical.choice, Quot.sound, propext | `c670f79ace7a64226da375f75f7f897b89e640b112117b2b3ddd70ef2bb21e54` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `sandwich_not_necessary_u8_div35` | cited by card 1 | none | `d40a32bd5dbb1c716b8e9749d594e4e8833cb4189005192afd3fd6ae38d86de4` | `239638794d05a78400a184733b2444262e70466839b7123715ab3bc63eb4e606` (1) |
| `sdivMagic` | cited by card 19 | none | `d717c0f9cf64387a67e6e798afeffae58cc29046a534ba4559ca78c0b47e83cb` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `sdivMagicUncorrected` | cited by card 12 | none | `d717c0f9cf64387a67e6e798afeffae58cc29046a534ba4559ca78c0b47e83cb` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `sdivMagicUncorrected_eq_sdivMagic_sub_one` | cited by card 12 | Quot.sound, propext | `f87766b084545d4de9b0ee3b22da274bf3494fbd6943e0f58e8f9f90efe06b4e` | `f1fc2b24226f2bb5c6e720d28b503c9c2606d2fe196732afa3d7b7fad3e34c6d` (2) |
| `sdivMagicUncorrected_eq_tdiv_sub_one_of_neg` | result 12 | Classical.choice, Quot.sound, propext | `10d8fafc26b22907ee7ebd8cc3117dc188eb2cf1bce85335791ad3bef498b96e` | `85fa77043fa85bfb93d680c85c5b2fd9dffb9ed4bfa862bb7982b58095191df7` (2) |
| `sdivMagicUncorrected_pos_examples` | cited by card 12 | none | `c8bc69552ca00fa0aa318548382dc34a1e5f1c130b0d91d9041e957a13a92f32` | `789d09d4b19d01cfea6fd17368a35b5f52bc00139834db84dd1644b859e23c02` (1) |
| `sdivMagic_eq_tdiv_of_sandwich` | result 11 | Classical.choice, Quot.sound, propext | `54175ff7fde1dc4b2e1f8fbd48f763f685b5438a5a3b75b8f201b8eb6d548223` | `53480c3781894c34e2be13ba88f61f5fdc21620cf56e8e8db5ca604a9a5606f4` (2) |
| `sdivMagic_neg_examples` | cited by card 11 | none | `3cbea6ce86d2735b7b66c67729fe26ad0e2aa9b5ae94755d974715d871e07d4b` | `f1fc2b24226f2bb5c6e720d28b503c9c2606d2fe196732afa3d7b7fad3e34c6d` (2) |
| `sdivMagic_pos_examples` | cited by card 11 | none | `3c38dfc96d24994fe8f96c2e7472913e2725183a20cd599054825e7344e95b80` | `47d0b0a7c4cf51460ced7ec29ddff7b76c8459a93f706636c41f83f9101db3b9` (1) |
| `signedMagic` | cited by card 11 | none | `89d358c33069524cef5266c160ae7d5b1cf43b1b2b10526b0483f2468efc9327` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `signedMagic_neg_example` | cited by card 11 | none | `cb0f59840690b53b8d382429eecdc6f9cf4e0eebd887db3c8e301f1b6f3559d4` | `5ac87a04d8095d426edad9ececa6378f2ca069ef0e66997e0ba3b89a309acb4c` (2) |
| `signedMagic_not_minimal_i8_div3` | cited by card 14 | none | `f511a026f8ced52be8774df33ac7590af7ed44aac07ba2be8a078ce060d9de0c` | `5ac87a04d8095d426edad9ececa6378f2ca069ef0e66997e0ba3b89a309acb4c` (2) |
| `signedMagic_one_one` | cited by card 14 | none | `1fc4f256957fc464bfe23c87074e6bb36a4a1813c15d68f2d1eafadacee556b4` | `5ac87a04d8095d426edad9ececa6378f2ca069ef0e66997e0ba3b89a309acb4c` (2) |
| `signedMagic_pos_examples` | cited by card 11 | none | `ef75fea34323fe3a480fe6eb19af7a548e903d60db11261d1c9686fff688f2a3` | `5ac87a04d8095d426edad9ececa6378f2ca069ef0e66997e0ba3b89a309acb4c` (2) |
| `signedMagic_sandwich` | result 14 | Classical.choice, Quot.sound, propext | `25950942928487aab87105e824d4f838fca17b8befcb097a69b3d2b3f753cd9d` | `5ac87a04d8095d426edad9ececa6378f2ca069ef0e66997e0ba3b89a309acb4c` (2) |
| `signedRange_iff_of_pos` | cited by card 11 | Classical.choice, Quot.sound, propext | `dda3ea3235bf3db0a7cc2853d3541c289a44e199aa839f303a86495fdaf7371a` | `64b2c1b756c2b4291994b4dd72ddb5e69416630b3482c06e9af71e6ff16b6cc5` (1) |
| `signedRange_iff_toInt_ofInt` | cited by card 11 | Classical.choice, Quot.sound, propext | `7bffb9d6d8557fad2741420268f7afcdb98c8364b066a9e2682a7c4d188e0357` | `64b2c1b756c2b4291994b4dd72ddb5e69416630b3482c06e9af71e6ff16b6cc5` (1) |
| `signedRange_neg_examples` | cited by card 11 | none | `751118fc0b91225581a75f69249b1d86650728e7ad7cbe91f1e5ec98fe94f3ac` | `64b2c1b756c2b4291994b4dd72ddb5e69416630b3482c06e9af71e6ff16b6cc5` (1) |
| `signedRange_pos_examples` | cited by card 11 | none | `39e6a73de6d75d5a5b3c8db4dcc98115b7d2efce19ef7aa6a56de6c6f964c609` | `64b2c1b756c2b4291994b4dd72ddb5e69416630b3482c06e9af71e6ff16b6cc5` (1) |
| `signedRange_zero_examples` | cited by card 11 | none | `1cc03b8655a298416a66cf62dedb698c196839f33e59975f93b63240a4e98727` | `64b2c1b756c2b4291994b4dd72ddb5e69416630b3482c06e9af71e6ff16b6cc5` (1) |
| `signedRange_zero_iff` | cited by card 13 | Classical.choice, Quot.sound, propext | `83b47558f815a4335b011b5150b5dec0d225a2a2b4e7234bf7d162320fbb84de` | `64b2c1b756c2b4291994b4dd72ddb5e69416630b3482c06e9af71e6ff16b6cc5` (1) |
| `signed_sandwich_not_necessary_i8_div35` | cited by card 11 | Classical.choice, Quot.sound, propext | `315b2600f44334116f6e396e2df1ab9cbf37a4a5cc5960446f2aef6a59f6b7be` | `53480c3781894c34e2be13ba88f61f5fdc21620cf56e8e8db5ca604a9a5606f4` (2) |
| `singleWordMagic` | cited by card 4 | none | `89d358c33069524cef5266c160ae7d5b1cf43b1b2b10526b0483f2468efc9327` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `singleWordMagic_lt_two_pow` | result 4 | Classical.choice, Quot.sound, propext | `4bcfdc3a6731d85845222a82637cb4767fbf59bb1e5e5db255ce62dd7777788d` | `f42cff25440951c26a88a2542ce3c181934d0cc8282e7d48e138174e2beb9b9e` (4) |
| `singleWordMagic_zero_right` | cited by card 4 | propext | `5613f3c4e1eb3fd5f463729622cb7a4081c03850df70b6583e8ed3fc550eb287` | `f42cff25440951c26a88a2542ce3c181934d0cc8282e7d48e138174e2beb9b9e` (4) |
| `singleWordShift` | cited by card 4 | none | `89d358c33069524cef5266c160ae7d5b1cf43b1b2b10526b0483f2468efc9327` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `singleWordShift_neg_example` | cited by card 4 | none | `390254d1c9bc8105ee1704a526a0fdc10e5adf08b689c17aa541c8fc9bdd3b97` | `08e89b3a532d0d51185844b26a3193ef558adb80c3f1d1f1c8be0c012656b97b` (2) |
| `singleWordShift_not_minimal_u8_div9` | cited by card 4 | none | `0323562f6b6a034116421d52c1be10e0edb42de979a264e220ca6a4ec1af6aca` | `7c81305cf419666eb848f7bb054eecd305c251d33be4ba3686d9923974cb13d6` (5) |
| `singleWordShift_one` | cited by card 4 | Quot.sound, propext | `968c8fd28573d7c433407f49ec656528ef443a97695f855af8c4214379a5a0d7` | `08e89b3a532d0d51185844b26a3193ef558adb80c3f1d1f1c8be0c012656b97b` (2) |
| `single_word_multiplier_exists_iff` | result 4 | Classical.choice, Quot.sound, propext | `ded1fad19b72af126e1e6ca758c7ea6f4178f59a0a67068474c213cd281fe8b2` | `7c81305cf419666eb848f7bb054eecd305c251d33be4ba3686d9923974cb13d6` (5) |
| `sremMagic` | cited by card 19 | none | `7640538a2cc1e77d42fd9fb65f215a7d0d58f3cd3271bff288bccc4edea57e68` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `sremMagic_eq_tmod_and_sign` | result 19 | Classical.choice, Quot.sound, propext | `4c243747a260bffab2d40a2c4c15bd79f8427b5986ced5fd1cab10d30bc441ec` | `06bbd1c1d6bf407f617a4300bf3c548615c6e9fb5f025e0c6c81814eb7f85a97` (3) |
| `sremMagic_neg_example` | cited by card 19 | none | `709486a9e10b63a9cf2810b2e0e2bbd90141c01e71df738c711b6891c921aefc` | `8bd9fbb8059d165aa32c8fbdfd3a2996ef44de68b38f689f0ae9e38936e01fcb` (2) |
| `sremMagic_pos_examples` | cited by card 19 | none | `3fbd47356b02b8682fea698e9a789564c505c13b39f354d0c9820b923b68807e` | `8bd9fbb8059d165aa32c8fbdfd3a2996ef44de68b38f689f0ae9e38936e01fcb` (2) |
| `succ_le_clog2_of_two_pow_lt` | cited by card 6 | Quot.sound, propext | `2231945b769bb707d9e8244a2a19fd69ed322469f94711c767317b2f10486485` | `fc70e1c376ecec941e89c06339c491e93dde37ffd550b7a5bfba2707ad9cfa9a` (1) |
| `tdiv_signedRange_iff` | result 13 | Classical.choice, Quot.sound, propext | `c246da26624dce033c3c2d920b1cb8f6ccb37406be6e0a4724eb798f65013111` | `64b2c1b756c2b4291994b4dd72ddb5e69416630b3482c06e9af71e6ff16b6cc5` (1) |
| `two_pow_le_mul_of_correct` | cited by card 9 | propext | `c154bf567919e640ad4e3c6d02fa75fa7eaa51ea3552b3a169ed95ffc8c005b6` | `239638794d05a78400a184733b2444262e70466839b7123715ab3bc63eb4e606` (1) |
| `two_pow_pred_lt_signedMagic` | cited by card 11 | Quot.sound, propext | `832af3667ecab9e4bd5134f7416df80ac20b7ded00be8d0e4c711db2b8aec3aa` | `5ac87a04d8095d426edad9ececa6378f2ca069ef0e66997e0ba3b89a309acb4c` (2) |
| `two_pow_pred_lt_singleWordMagic` | cited by card 4 | Quot.sound, propext | `b806e4dfd9f99ffd1b7a06606be3048b449f02463378b6f9057b590bd1068e45` | `f42cff25440951c26a88a2542ce3c181934d0cc8282e7d48e138174e2beb9b9e` (4) |
| `uncorrected_ne_fdiv_at_negative_multiple` | cited by card 12 | none | `e06062dee9d85bfbae06529b0b9e3f266a5edc4d1531e8a500c15277abad0ecf` | `85fa77043fa85bfb93d680c85c5b2fd9dffb9ed4bfa862bb7982b58095191df7` (2) |
| `unsignedMagic` | cited by card 2 | none | `89d358c33069524cef5266c160ae7d5b1cf43b1b2b10526b0483f2468efc9327` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `unsignedMagic_eq_two_pow_add_low` | result 3 | Classical.choice, Quot.sound, propext | `ca26ad4728a621b9951f3d3e96890e69e2af7126070a9ba63481e46aa7d4c6fa` | `f3632b6d81782585f6f06cf7e52b9980974f172959a31389f3f9a9e8cf131e0d` (3) |
| `unsignedMagic_ge_two_pow_of_pos` | result 3 | Quot.sound, propext | `c6cca047820ef21e88bfe4cf59f994bd2acc59127281333e0dc3f9f2256a45e7` | `f3632b6d81782585f6f06cf7e52b9980974f172959a31389f3f9a9e8cf131e0d` (3) |
| `unsignedMagic_lt_two_pow_succ_above_examples` | cited by card 2 | none | `1164cc77e5dd53cb925800bc2f677f48ae575072578b970c4a47437c0f4646d7` | `f3632b6d81782585f6f06cf7e52b9980974f172959a31389f3f9a9e8cf131e0d` (3) |
| `unsignedMagic_lt_two_pow_succ_converse_fails` | cited by card 2 | Classical.choice, Quot.sound, propext | `636a119e424971832ae47916de9bde03f1e357592a378a25fde36d5d89766dd1` | `f3632b6d81782585f6f06cf7e52b9980974f172959a31389f3f9a9e8cf131e0d` (3) |
| `unsignedMagic_lt_two_pow_succ_of_le` | result 3 | Classical.choice, Quot.sound, propext | `37abb640d0a7aeebf7353e589236ae8dfbd5e9b29569d031c84396cee6ac7917` | `f3632b6d81782585f6f06cf7e52b9980974f172959a31389f3f9a9e8cf131e0d` (3) |
| `unsignedMagic_sandwich` | result 2 | Quot.sound, propext | `3cc920d65b8be2908df60bcebc796ee4e1474acc7353b785743938d8e752eccb` | `f3632b6d81782585f6f06cf7e52b9980974f172959a31389f3f9a9e8cf131e0d` (3) |
| `unsignedMagic_two_pow` | cited by card 2 | Classical.choice, Quot.sound, propext | `ca44ff546b16b2b834d3e48c8caf90c48a536899f03acc384950a1b7c88e239d` | `f3632b6d81782585f6f06cf7e52b9980974f172959a31389f3f9a9e8cf131e0d` (3) |
| `unsignedMagic_two_pow_succ_add_one` | cited by card 2 | Quot.sound, propext | `b6b700128c91578defc08d7b5dd18c249fc0f3c625ef492da8f97000a4523cda` | `f3632b6d81782585f6f06cf7e52b9980974f172959a31389f3f9a9e8cf131e0d` (3) |
| `unsignedMagic_zero_right` | cited by card 2 | propext | `e7b43ee20b4808721443ad1e2923627c4b4432ff3430030e1ecc3055ec0892e0` | `f3632b6d81782585f6f06cf7e52b9980974f172959a31389f3f9a9e8cf131e0d` (3) |

### Toolchain

Lean `leanprover/lean4`, release `v4.34.1` (lightweight tag pointing to commit `5045d0056413266e57c625dcd7c365b10e377c52`), pinned in `lean/lean-toolchain`. Dependencies: the core library; no Mathlib and no other Lake dependency. Every proof is re-elaborated and kernel-checked by `lake build`.

### Primary sources

Each entry records the exact bibliographic or repository coordinates and, where the cards rely on a stated theorem or rule, a verbatim quotation with its section and page. Quotations from PDFs are transcribed from the text layer with mathematical notation restored (superscripts written `^{...}`, floor/ceiling brackets as `⌊ ⌋`/`⌈ ⌉`); `[sic]` marks text reproduced as printed. Content of works marked *not consulted* was not read; statements about them are limited to their bibliographic records and to how the consulted papers describe them. All sources were checked on 2026-11-21.

- **[GM94]** Torbjörn Granlund and Peter L. Montgomery, "Division by Invariant Integers using Multiplication", *Proceedings of the ACM SIGPLAN 1994 Conference on Programming Language Design and Implementation (PLDI '94)*, pp. 61–72, June 1994, DOI 10.1145/178243.178249; also *ACM SIGPLAN Notices* 29(6):61–72, DOI 10.1145/773473.178249. Quoted from the authors' 12-page preprint https://gmplib.org/~tege/divcnst-pldi94.pdf; "p." is the preprint page (the printed version occupies the 12 pages 61–72; a page-for-page correspondence is likely but was not verified).
- **[GM94-S1]** Granlund–Montgomery, Section 1, p. 1: "Multiple authors [2, 11, 15] present algorithms for division by constants, but only when the divisor divides 2^k − 1 for some small k. Magenheimer et al [16, §7] give the foundation of a more general approach, which Alverson [1] implements on the Tera Computing System." Section 7, p. 7: "Alverson [1] uses integer multiplication, but computes the multiplier using floating point arithmetic."
- **[GM94-T3.1]** Granlund–Montgomery, Section 3, Table 3.1, p. 3: "SRA(x, n) Arithmetic right shift of x by n bits (0 ≤ n ≤ N − 1)." and "SRL(x, n) Logical right shift of x by n bits (0 ≤ n ≤ N − 1)."
- **[GM94-T4.2]** Granlund–Montgomery, Section 4, p. 3: "Theorem 4.2 Suppose m, d, ℓ are nonnegative integers such that d ≠ 0 and 2^{N+ℓ} ≤ m ∗ d ≤ 2^{N+ℓ} + 2^ℓ. (4.3) Then ⌊n/d⌋ = ⌊m ∗ n/2^{N+ℓ}⌋ for every integer n with 0 ≤ n < 2^N."
- **[GM94-F4.1]** Granlund–Montgomery, Section 4, Figure 4.1 and its explanation, p. 4. Figure: "Initialization (given uword d with 1 ≤ d < 2^N): int ℓ = ⌈log2 d⌉; /* d ≤ 2^ℓ ≤ 2 ∗ d − 1 */ uword m′ = ⌊2^N ∗ (2^ℓ − d)/d⌋ + 1; /* m′ = ⌊2^{N+ℓ}/d⌋ − 2^N + 1 */ int sh1 = min(ℓ, 1); int sh2 = max(ℓ − 1, 0); /* sh2 = ℓ − sh1 */ For q = n/d, all uword: uword t1 = MULUH(m′, n); q = SRL(t1 + SRL(n − t1, sh1), sh2);". Explanation: "Set m = m′ + 2^N = ⌊2^{N+ℓ}/d⌋ + 1. The hypothesis of Theorem 4.2 is satisfied since 2^{N+ℓ} < m ∗ d ≤ 2^{N+ℓ} + d ≤ 2^{N+ℓ} + 2^ℓ." Equation (4.5): "Since 0 ≤ t1 ≤ n, the formula for q simplifies to q = SRL(t1 + SRL(n − t1, 1), ℓ − 1) = ⌊(t1 + ⌊(n − t1)/2⌋)/2^{ℓ−1}⌋ = ⌊⌊(t1 + n)/2⌋/2^{ℓ−1}⌋ = ⌊(t1 + n)/2^ℓ⌋. (4.5)" (the outer brackets of the display are lost in the text layer and restored here). Next paragraph: "Caution. Conceptually q is SRL(n + t1, ℓ), as in (4.5). Do not compute q this way, since n+t1 may overflow N bits and the shift count may be out of bounds."
- **[GM94-T5.1]** Granlund–Montgomery, Section 5, p. 5: "Theorem 5.1 Suppose m, d, ℓ are integers such that d ≠ 0 and 0 < m ∗ |d| − 2^{N+ℓ−1} ≤ 2^ℓ. Let n be an arbitrary integer such that −2^{N−1} ≤ n ≤ 2^{N−1} − 1. Define q0 = ⌊m ∗ n/2^{N+ℓ−1}⌋. Then TRUNC(n/d) = q0 if n ≥ 0 and d > 0; 1 + q0 if n < 0 and d > 0; −q0 if n ≥ 0 and d < 0; −1 − q0 if n < 0 and d < 0." Same page: "Caution. When d < 0, avoid rewriting the quotient as TRUNC((−n)/|d|), which fails for n = −2^{N−1}."
- **[GM94-F5.1]** Granlund–Montgomery, Section 5, Figure 5.1, p. 5: "Initialization (given constant sword d with d ≠ 0): int ℓ = max(⌈log2 |d|⌉, 1); udword m = 1 + ⌊2^{N+ℓ−1}/|d|⌋; sword m′ = m − 2^N; sword dsign = XSIGN(d); int shpost = ℓ − 1; For q = TRUNC(n/d), all sword: sword q0 = n + MULSH(m′, n); q0 = SRA(q0, shpost) − XSIGN(n); q = EOR(q0, dsign) − dsign;" (the text layer does not distinguish m′ from m₀).
- **[GM94-OVF]** Granlund–Montgomery, Section 5, p. 5: "Overflow detection. The quotient n/d overflows if n = −2^{N−1} and d = −1. The algorithm in Figure 5.1 returns −2^{N−1}. If overflow detection is required, the final subtraction of dsign should check for overflow."
- **[GM94-F5.2]** Granlund–Montgomery, Section 5, Figure 5.2 ("Optimized code generation of signed q = TRUNC(n/d) for constant d ≠ 0"), p. 5: "if |d| = 1 then Issue q = d; [sic] else if |d| = 2^ℓ then Issue q = SRA(n + SRL(SRA(n, ℓ − 1), N − ℓ), ℓ); else if m < 2^{N−1} then … end if if d < 0 then Issue q = −q; end if". (In the |d| = 1 branch the intended value is evidently q = n; the printed text is reproduced as is.)
- **[GM94-S6]** Granlund–Montgomery, Section 6, p. 6, equation (6.3): "If d > 0 is constant, then dsign = 0. Then (6.1) becomes ⌊n/d⌋ = TRUNC((n − nsign)/d) + nsign, where nsign = XSIGN(n). Since TRUNC(−x) = −TRUNC(x) and EOR(−1, n) = −1 − n = −(n + 1), this is equivalent to ⌊n/d⌋ = EOR(nsign, TRUNC(EOR(nsign, n)/d)) (d > 0). (6.3)"
- **[GM94-F6.2]** Granlund–Montgomery, Figure 6.2 ("Selection of multiplier and shift count"), p. 7: "Cmt. Corollary. If d ≤ 2^prec, then m < 2^{N+shpost} ∗ (1 + 2^{1−ℓ})/d ≤ 2^{N+shpost−ℓ+1}. Cmt. Hence m fits in max(prec, N − ℓ) + 1 bits (unsigned)." (for "1 ≤ d < 2^N" and "1 ≤ prec ≤ N").
- **[GM94-S9]** Granlund–Montgomery, Section 9, p. 9: "Suppose we want code for q = n/d, where d is a nonzero constant and n is an expression known to be divisible by d." … "Since n/d_odd = 2^e ∗ q fits in N bits, it must equal the lower half of the product d_inv ∗ n, namely MULL(d_inv, n)."
- **[LKK19]** Daniel Lemire, Owen Kaser and Nathan Kurz, "Faster Remainder by Direct Computation: Applications to Compilers and Software Libraries", *Software: Practice and Experience* 49(6):953–970, 2019, DOI 10.1002/spe.2689; quoted from arXiv:1902.01961v3 (20 Nov 2019), "p." = arXiv v3 page.
- **[LKK19-S1]** Lemire–Kaser–Kurz, Section 1, p. 3: "To compute the remainder by a constant (n mod d), an optimizing compiler might first compute the quotient n div d as a multiplication by c followed by a logical shift by F bits (c ∗ n) div 2^F, and then use the fact that the remainder can be derived using a multiplication and a subtraction as n mod d = n − (n div d) ∗ d."
- **[LKK19-A1]** Lemire–Kaser–Kurz, Section 2, Algorithm 1 ("Granlund-Montgomery-Warren division algorithm by a constant using unsigned integers"), p. 4: "1: Require: fixed integer divisor d ∈ [1, 2^N) 2: Require: runtime integer numerator n ∈ [0, 2^N) 3: Compute: the integer n div d 4: if d is a power of two (d = 2^K) then 5: return n div 2^K 6: else if for L = ⌊log2(d)⌋ and c = ⌈2^{N+L}/d⌉, we have c ∗ (2^N − (2^N mod d) − 1) < (2^N div d) 2^{N+L} then 7: return (c ∗ n) div 2^{N+L} ⊳ c ∈ [0, 2^N) 8: else if d = 2^K d′ for K > 0 then 9: let L = ⌈log2(d′)⌉ and c = ⌈2^{N−K+L}/d′⌉ ⊳ c ∈ [0, 2^N) 10: return c ∗ (n div 2^K) div 2^{N−K+L} 11: else 12: let L = ⌈log2 d⌉ and c = ⌈2^{N+L}/d⌉ ⊳ c > 2^N 13: let c′ be such that c = 2^N + c′ ⊳ c′ ∈ [0, 2^N) 14: return (⌊c′ ∗ n/2^N⌋ + ((n − ⌊c′ ∗ n/2^N⌋) div 2)) div 2^{L−1} 15: end if"
- **[LKK19-T1]** Lemire–Kaser–Kurz, Section 3, p. 6: "Theorem 1. Given d ∈ [1, 2^N), and non-negative integers c, L such that 1/d ≤ c/2^{N+L} ≤ 1/d + (1/d)/2^N then n mod d = (((c ∗ n) mod 2^{N+L}) ∗ d) div 2^{N+L} for all n ∈ [0, 2^N)." (Multiplying through by d·2^{N+L}, the hypothesis is 2^{N+L} ≤ c∗d ≤ 2^{N+L} + 2^L.)
- **[LKK19-T2]** Lemire–Kaser–Kurz, Section 3.1, p. 8: "Theorem 2. Given d ∈ [1, 2^{N−1}), and non-negative integers c, L such that 2^{N−1+L} < c ∗ d < 2^{N−1+L} + 2^L, let μ = ⌊(lsb_{N−1+L}(c ∗ n) ∗ d)/2^{N−1+L}⌋ then • n mod d = μ for all n ∈ [0, 2^{N−1}) • and n mod d = μ − d + 1 for all n ∈ [−2^{N−1}, 0)." (Here mod is the remainder of truncating division.)
- **[LBK21]** Daniel Lemire, Colin Bartlett and Owen Kaser, "Integer Division by Constants: Optimal Bounds", *Heliyon* 7(6):e07442, 2021, DOI 10.1016/j.heliyon.2021.e07442; quoted from arXiv:2012.12369v3 (29 Jun 2021, HTML rendering; section numbers given, page numbers not recorded).
- **[LBK21-T1]** Lemire–Bartlett–Kaser, Section 4.1, Theorem 1: "Consider an integer divisor d > 0 and a range of integer numerators n ∈ [0, N] where N ≥ d is an integer. We have that division(n, d) = division(c ∗ n, m) for all integer numerators n in the range if and only if 1/d ≤ c/m < (1 + 1/(N − remainder(N + 1, d))) 1/d. (7)"
- **[LBK21-S4.1]** Lemire–Bartlett–Kaser, Section 4.1 (after the inequalities are rewritten as m/d ≤ c < (1 + 1/K) m/d): "Thus if c is to be as small as possible, we must have that c = ceiling(m/d)."
- **[LBK21-T2]** Lemire–Bartlett–Kaser, Section 4.2, Theorem 2: "Consider an integer divisor d > 0 and a range of integer numerators n ∈ [0, N] where N ≥ d is an integer. We have that division(n, d) = division(c ∗ n, m) and remainder(n, d) = division(remainder(c ∗ n, m) ∗ d, m) for all integer numerators n in the range if and only if 1/d ≤ c/m < (1 + 1/N) 1/d. (11)"
- **[LBK21-R2]** Lemire–Bartlett–Kaser, Section 4.2, Remark 2: "In previous work [9, Theorem 1], Lemire et al. reported an upper bound of c/m ≤ (1 + 1/(N + 1)) 1/d as a sufficient (but not necessary) condition." … "We can show that if m = N + 1 and m ≥ 3 then the earlier bound is tight." (The remark's example of a gap between the two bounds is N = 10, d = 5, m = 2^5.)
- **[LBK21-P3]** Lemire–Bartlett–Kaser, Section 6, Proposition 3: "Consider an integer divisor d > 0 that is not a power of two. Let N be an integer such that N + 1 is a power of two, then we can compute the quotient of any integer n ∈ [0, N] by d using a constant c ∈ [0, N] as follows. Let m = 2^{floor(log2(d))} ∗ (N + 1). 1. if d − remainder(m, d) < ceiling(m/(N − remainder(N + 1, d))), we let c = ceiling(m/d) and we have division(n, d) = division(c ∗ n, m). 2. Otherwise we let c = floor(m/d) and we have division(n, d) = division(c ∗ n + c, m)." Footnote 2: "This result is not novel [7].", where [7] is Robison (2005).
- **[Robison05]** Arch D. Robison, "N-Bit Unsigned Division via N-Bit Multiply-Add", *17th IEEE Symposium on Computer Arithmetic (ARITH-17)*, pp. 131–139, 2005, DOI 10.1109/ARITH.2005.31 (content not consulted; described here through its title and Lemire–Bartlett–Kaser Section 6).
- **[CW]** Davide Cavagnino and Albert E. Werbrouck, "Efficient Algorithms for Integer Division by Constants Using Multiplication", *The Computer Journal* 51(4):470–480 (published online 2007-09-05), DOI 10.1093/comjnl/bxm082 (content not consulted).
- **[Alverson91]** Robert Alverson, "Integer Division Using Reciprocals", *Proceedings of the 10th IEEE Symposium on Computer Arithmetic (ARITH-10)*, pp. 186–190, 1991, DOI 10.1109/ARITH.1991.145558 (content not consulted).
- **[MPPZ]** Daniel J. Magenheimer, Liz Peters, Karl W. Pettis and Dan Zuras, "Integer Multiplication and Division on the HP Precision Architecture": the version cited by Granlund–Montgomery as [16] is in *ASPLOS II* (1987), *ACM SIGPLAN Notices* 22(10):90–99, DOI 10.1145/36205.36189; a later version appeared in *IEEE Transactions on Computers* 37(8):980–990, 1988, DOI 10.1109/12.2248 (content of neither consulted).
- **[HD]** Henry S. Warren, Jr., *Hacker's Delight*, 2nd edition, Addison-Wesley, 2012 (electronic ISBN 9780133084993), chapter 10 "Integer Division By Constants" (section titles from the publisher's table of contents; the book text was not consulted).
- **[HD-code]** *Hacker's Delight* companion code, repository `hcs0/Hackers-Delight`, commit `2bcb559da638a97f429c19889e6fd7d8601fd5d2`: `magicgu.py.txt` lines 14–15: "Example: magicgu(255, 7) is a 9-bit number, but magicgu(200, 7) is an 8-bit number."; line 24: `nc = ((nmax + 1)//d)*d - 1`; `magicu.c.txt` line 40: `nc = -1 - (-d)%d;       // Unsigned arithmetic here.`; lines 63–64: `} while (p < 64 &&` / `(q1 < delta || (q1 == delta && r1 == 0)));`.
- **[CompCert]** CompCert, repository `AbsInt/CompCert`, commit `5e4ef44c57b22cdc2e1893770843fd693a5f82e1`. `backend/SelectDivproof.v` (section with `Hypothesis d_pos: d > 0.`): line 34 `Lemma Zdiv_mul_pos: forall m l, l >= 0 -> two_p (N+l) <= m * d <= two_p (N+l) + two_p l -> forall n, 0 <= n < two_p N -> Z.div n d = Z.div (m * n) (two_p (N + l)).` (commented "This is theorem 4.2 from Granlund and Montgomery, PLDI 1994."); line 154 `Lemma Zquot_mul: forall m l, l >= 0 -> two_p (N+l) < m * d <= two_p (N+l) + two_p l -> forall n, - two_p N <= n < two_p N -> Z.quot n d = Z.div (m * n) (two_p (N + l)) + (if zlt n 0 then 1 else 0).` (commented as theorem 5.1); line 276 `Theorem divs_mul_shift_2` (for `m >= Int.half_modulus`: `Int.divs x y = Int.add (Int.shr (Int.add (Int.mulhs x (Int.repr m)) x) (Int.repr p)) (Int.shru x (Int.repr 31))`); line 574 `Theorem eval_moduimm`; line 694 `Theorem eval_modsimm`. `backend/SelectDiv.vp`: `divs_mul_params` (line 45) checks `zlt (two_p (32 + p)) (m * d) && zle (m * d) (two_p (32 + p) + two_p (p + 1)) && zle 0 m && zlt m Int.modulus` (lines 53–57); `divu_mul_params` (line 61) checks `zle (two_p (32 + p)) (m * d) && zle (m * d) (two_p (32 + p) + two_p p) && zle 0 m && zlt m Int.modulus` (lines 69–73). `lib/Integers.v`: line 966 `Theorem modu_divu: forall x y, y <> zero -> modu x y = sub x (mul (divu x y) y).`; line 990 `Theorem mods_divs: forall x y, mods x y = sub x (mul (divs x y) y).`; line 2362 `Theorem shrx_shr`; line 2403 `Theorem shrx_shr_2: forall x y, ltu y (repr (zwordsize - 1)) = true -> shrx x y = shr (add x (shru (shr x (repr (zwordsize - 1))) (sub iwordsize y))) y.` `lib/Zbits.v`: line 933 `Lemma Zquot_Zdiv: forall x y, y > 0 -> Z.quot x y = if zlt x 0 then (x + y - 1) / y else x / y.`; line 948 `Lemma Zdiv_shift`.
- **[LLVM]** LLVM, repository `llvm/llvm-project`, commit `c312bf3fa94430185410c06c502abd9953f838fa`. `llvm/lib/Support/DivisionByConstantInfo.cpp`: lines 31–33 `APInt AD = D.abs();` / `APInt T = SignedMin + (D.lshr(D.getBitWidth() - 1));` / `APInt ANC = T - 1 - T.urem(AD);   // absolute value of NC`; line 89 `// Calculate NC, the largest dividend such that NC.urem(D) == D-1.`; line 90 `APInt NC = AllOnes - (AllOnes + 1 - D).urem(D);`; lines 112–113 `if (Q2.uge(SignedMax))` / `Retval.IsAdd = true;`; lines 134–135 `} while (P < D.getBitWidth() * 2 &&` / `(Q1.ult(Delta) || (Q1 == Delta && R1.isZero())));`; lines 149–154 `Retval.PostShift = P - D.getBitWidth(); // resulting shift` / `// Reduce shift amount for IsAdd.` / `if (Retval.IsAdd) {` / `assert(Retval.PostShift > 0 && "Unexpected shift");` / `Retval.PostShift -= 1;` / `}`. `llvm/docs/LangRef.rst`, `lshr` (lines 11106–11108) and `ashr` (lines 11158–11160): "If ``op2`` is (statically or dynamically) equal to or larger than the number of bits in ``op1``, this instruction returns a :ref:`poison value <poisonvalues>`."
- **[Lean-core]** Lean 4 core library, `leanprover/lean4` release `v4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`), `src/lean/`: `Init/Data/BitVec/Bitblast.lean` line 1321 `theorem sdivOverflow_eq {w : Nat} (x y : BitVec w) : (sdivOverflow x y) = (decide (0 < w) && (x = intMin w) && (y = allOnes w))`, line 1578 `theorem toInt_sdiv_of_ne_or_ne (a b : BitVec w) (h : a ≠ intMin w ∨ b ≠ -1#w) : (a.sdiv b).toInt = a.toInt.tdiv b.toInt`, line 1648 `theorem intMin_sdiv_neg_one : (intMin w).sdiv (-1#w) = intMin w`; `Init/Data/Int/DivMod/Lemmas.lean` line 223 `theorem tdiv_eq_ediv {a b : Int} : a.tdiv b = a / b + if 0 ≤ a ∨ b ∣ a then 0 else sign b`, line 372 `theorem tmod_def (a b : Int) : tmod a b = a - b * a.tdiv b`, line 1264 `protected theorem tdiv_neg : ∀ a b : Int, a.tdiv (-b) = -(a.tdiv b)`, line 1393 `theorem tmod_nonneg : ∀ {a : Int} (b : Int), 0 ≤ a → 0 ≤ tmod a b`, line 1396 `theorem tmod_neg (a b : Int) : tmod a (-b) = tmod a b`, line 1403 `theorem tmod_lt_of_pos (a : Int) {b : Int} (H : 0 < b) : tmod a b < b`, line 1409 `theorem lt_tmod_of_pos (a : Int) {b : Int} (H : 0 < b) : -b < tmod a b`, line 1593 `theorem natAbs_tdiv_le_natAbs (a b : Int) : natAbs (a.tdiv b) ≤ natAbs a`; `Init/Data/Int/Bitwise/Lemmas.lean` line 44 `theorem shiftRight_eq_div_pow (m : Int) (n : Nat) : m >>> n = m / ((2 ^ n) : Nat)`.
- **[C11]** ISO/IEC 9899:2011 final committee draft N1570, §6.5.7 paragraph 3 (read in the HTML rendering http://port70.net/~nsz/c/c11/n1570.html#6.5.7p3): "The integer promotions are performed on each of the operands. The type of the result is that of the promoted left operand. If the value of the right operand is negative or is greater than or equal to the width of the promoted left operand, the behavior is undefined."
- **[C++]** C++ working draft, [expr.shift] paragraph 1 (https://eel.is/c++draft/expr.shift, an unversioned rendering of the current draft): "The behavior is undefined ([ub:expr.shift.neg.and.width]) if the right operand is negative, or greater than or equal to the width of the promoted left operand."
- **[Rust]** The Rust Reference, "Operator expressions", section "Overflow" (https://doc.rust-lang.org/reference/expressions/operator-expr.html#overflow, unversioned): "Integer operators will panic when they overflow when compiled in debug mode." and, among the cases that count as overflow, "Using << or >> where the right-hand argument is greater than or equal to the number of bits in the type of the left-hand argument, or is negative." Rust standard library 1.100.0, `u32::wrapping_shr`: "Panic-free bitwise shift-right; yields self >> mask(rhs), where mask removes any high-order bits of rhs that would cause the shift to exceed the bitwidth of the type."
- **[Intel]** Intel 64 and IA-32 Architectures Software Developer's Manual, entry SAL/SAR/SHL/SHR, as reproduced at https://www.felixcloutier.com/x86/sal:sar:shl:shr (an unofficial snapshot dated December 2023; not checked against Intel's own PDF): "The count is masked to 5 bits (or 6 bits with a 64-bit operand). The count range is limited to 0 to 31 (or 63 with a 64-bit operand)."
- **[Arm]** Arm A64 instruction descriptions of LSRV and ASRV, as reproduced at https://www.scs.stanford.edu/~zyedidia/arm64/lsrv.html and …/asrv.html (an unofficial mirror; the official Arm documentation could not be retrieved, so this wording is not verified against Arm's manual): "The value of the second source register modulo the register size in bits gives the number of bits by which the first source register is right-shifted."
- **[RISC-V]** RISC-V unprivileged ISA manual, repository `riscv/riscv-isa-manual`, commit `c05f1725f25526dd8463bac6ca75cfcfbee17d05`: `src/unpriv/rv32.adoc` lines 353–355: "SLL, SRL, and SRA perform logical left, logical right, and arithmetic right shifts on the value in register rs1 by the shift amount held in the lower 5 bits of register rs2."; `src/unpriv/rv64.adoc` lines 118–121: "… by the shift amount held in register rs2. In RV64I, only the low 6 bits of rs2 are considered for the shift amount." (AsciiDoc markup removed.)

### Observation date

All kernel checks, statement hashes and source verifications recorded here were made on 2026-11-21 (the `observed_at` date of `REPORT.json`).

## Revalidation

### Primary check

Requirements: `elan` (the Lean toolchain manager, so that `lake` uses the toolchain pinned in `lean/lean-toolchain`) and `python3`. Run from the package directory:

```bash
python3 support/revalidate.py .
```

`support/revalidate.py` never modifies the package; it copies `lean/` to a temporary directory and then:

1. runs `lake build`, which re-elaborates and kernel-checks every proof;
2. scans every Lean source for `sorry`, `admit`, `native_decide` and `axiom` declarations;
3. runs an audit program embedded in the script that prints, for every declaration of the library, the axioms it depends on (`Lean.collectAxioms`), and, for every Lean name referenced by `results.json` or recorded in `audit/statements.json`, the Lean `repr` of its type and its definition closure (the sorted lines `name : repr(type)`, plus ` := repr(value)` for non-theorems, over every package constant reachable from the statement; theorem bodies are excluded);
4. hashes the statement text and the newline-joined closure text with SHA-256 and compares both, and the closure size, with `audit/statements.json`.

It prints `REVALIDATED` and exits with status 0 if and only if the build succeeds, no banned token occurs, no declaration depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`, and every recorded statement and closure hash matches.

### Manual check

```bash
cd lean
lake build
lake env lean Audit.lean
```

`Audit.lean` (outside the library target) fails if any declaration of the `Toy` library depends on an axiom other than `propext`, `Quot.sound` and `Classical.choice`; otherwise it prints the line `AUDIT OK: 524 declarations checked; only propext, Quot.sound, Classical.choice.` (the program's literal output; this count includes compiler-generated auxiliary constants, and the 270 declarations under Evidence are the non-auxiliary ones).

To inspect a single result (here result 1):

```bash
cd lean
cat > /tmp/magicdiv_check.lean <<'EOF'
import Toy
#check @Toy.MagicDiv.mulShiftCorrect_of_sandwich
#print axioms Toy.MagicDiv.mulShiftCorrect_of_sandwich
EOF
lake env lean /tmp/magicdiv_check.lean
```

### What a passing check establishes

A passing primary check establishes that the quoted Lean statements are kernel-checked under Lean v4.34.1 using no axioms beyond `propext`, `Classical.choice` and `Quot.sound`, and that they are the statements whose hashes are recorded under Evidence: any change to a statement, or to a definition it depends on, changes its recorded hash. It does not re-check the modeling-bridge items, the citations, or any claim about a real compiler or instruction set; for those, re-read the cited sources at the recorded commits, sections and pages.
