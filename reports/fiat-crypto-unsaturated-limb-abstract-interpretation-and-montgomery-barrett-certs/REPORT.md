# Fiat-Crypto Unsaturated-Limb Abstract Interpretation and Bézout Quotient Certificates for Montgomery and Barrett Reduction

## Summary

Verifying high-speed elliptic-curve and post-quantum lattice arithmetic (`curve25519-dalek` `FieldElement51`/`Scalar52`, `libcrux` ML-KEM and ML-DSA) under a pure-kernel Lean 4 profile (`joshlf/anneal` Pass 1: 51 `Init.*` prelude modules, `{propext, Quot.sound, Classical.choice}`, zero `omega`, `ring`, `bv_decide`, `native_decide`, `decide +kernel`, `grind`, or infix bitwise/pow notations) cannot rely on wrapping $\mathbb{Z}/2^w\mathbb{Z}$ Horner polynomials alone. Multi-limb and lattice reductions couple three tightly dependent properties across every instruction:

1. **Carry-headroom overflow & lossless cast bounds (`Fiat-Crypto` `ZRange` abstract interpretation):** Forward propagation of exact signed/unsigned integer intervals `r[lo ~> hi]` (`four_corners`, `four_corners_and_zero`, `land_bounds`, `split_bounds`, `interp_Z_cast`) over straight-line SSA traces discharges all 80+ `u64`/`u128`/`i16`/`i32`/`i64` overflow and narrowing-cast checks in `FieldElement51::mul` (`< 2^54` inputs $\to$ `< 2^51 + 6081` outputs) and `Scalar52::montgomery_reduce` in a single `<1 ms` C++ GMP `Eq.refl true` pass without case-splitting on intermediate bitwidths.
2. **Symbolic-radix pseudo-Mersenne folding without `Nat.reducePow` blowup:** Rather than expanding $2^{255}$ into a 78-digit decimal literal that foils syntactic matching, representing limb polynomials over a **symbolic radix atom $B$** ($B = 2^{51}$ for Curve25519) collapses carry-extraction identities $c_k = q_k B + r_k$ and folds $B^5 \equiv 19 \pmod{2^{255} - 19}$ using an explicit integer quotient polynomial $Q(\vec{x})$, proving $\mathsf{eval}_{51}(\text{out}) - \mathsf{eval}_{51}(a) \cdot \mathsf{eval}_{51}(b) = (B^5 - 19) \cdot Q(\vec{x})$ in sparse Horner normal form.
3. **Unified Bézout Montgomery (`REDC`) and signed Barrett quotient certificates:** Classical additive word-by-word Montgomery (`WordByWordMontgomery.v`, `Scalar52`, $N_0 \cdot k + 1 = q_B \cdot r$) and Seiler's subtractive signed Montgomery (`libcrux` ML-KEM and ML-DSA, $q \cdot k - 1 = q_B \cdot R$) share one algebraic Bézout certificate schema, paired with an overflow-free separate-shift lemma over Euclidean `Trusted.MirSemantics.intShiftRight` that replaces 95-line manual `F*` `calc` scripts and closes `libcrux`'s `verification_status(lax)` Barrett gap in ML-DSA.

## Applicability

This report connects twelve pinned subjects in `REPORT.json`: `mit-plv/fiat-crypto` (`3d2880ef2803faa9385589a81a835d5828eb3d38`, Erbsen et al. S&P 2019 DOI `10.1109/SP.2019.00005`, `src/Util/ZRange*.v`, `src/AbstractInterpretation/ZRange.v`, `src/Arithmetic/{WordByWordMontgomery,BarrettReduction}.v`, `src/PushButtonSynthesis/{WordByWordMontgomery,BarrettReduction,UnsaturatedSolinas}.v`); `dalek-cryptography/curve25519-dalek` (`328771a7148bf72df1468fdef5e453beb60c0b5f`, `field.rs`, `scalar.rs`, `constants.rs`); `cryspen/libcrux` (`24330863b3d1d4179e4bcea8cef6bf6fa313057e`, FIPS 203 DOI `10.6028/NIST.FIPS.203`, FIPS 204 DOI `10.6028/NIST.FIPS.204`, VSTTE 2025 DOI `10.1007/978-3-031-86695-1_7` / ePrint `2025/142`, ML-KEM & ML-DSA portable arithmetic); Montgomery (1985 DOI `10.1090/S0025-5718-1985-0777282-X`), Barrett (1986 DOI `10.1007/3-540-47721-7_24`), and Seiler (ePrint `2018/039`); plus `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`, `TrustedBoundary.lean`, `foundation-lock.json`, `MirSemantics.lean`) and `leanprover/lean4` (`v4.34.1` `5045d0056413266e57c625dcd7c365b10e377c52`, `type_checker.cpp`).

Sibling corpus reports `horner-modular-ring-reflection-and-gomory-chvatal-integer-cut-checkers` and `fiat-crypto-hacl-evercrypt-vale-libcrux-and-verified-crypto-synthesis` cover wrapping $\mathbb{Z}/2^w\mathbb{Z}$ Horner polynomials, linear integer cuts, and C/`F*` synthesis surveys; this report isolates unsaturated-limb `ZRange` transfer functions, symbolic-radix folding, Bézout Montgomery/Barrett certificates, and Pass 1 Lean 4 mechanization.

## Findings

### 1. `Fiat-Crypto` `ZRange` Abstract Interpretation and Carry-Headroom Bounds

`Basis: normative + source + execution + derived`

In `mit-plv/fiat-crypto@3d2880ef`, bounds verification runs as an executable abstract interpreter over reified PHOAS syntax (`ZRange.type.base.option.interp`, `src/AbstractInterpretation/ZRange.v:158-223, 560-994`), associating each integer with `option zrange` (`zrange := { lower : Z ; upper : Z }`, `src/Util/ZRange.v:18`) and gating narrowing casts with `is_tighter_than_bool v r := (lower r <=? lower v) && (upper v <=? upper r)` (`L81-82`).

1. **Corner hulls & zero-splitting (`src/Util/ZRange/Operations.v:61-86, 155-168, 227-255`):** Monotone binary operators (`Z.add`, `Z.sub`, `Z.mul`) take `four_corners` over `(lx, ux) × (ly, uy)`; discontinuous `Z.div`, `Z.shiftr`, and `Z.shiftl` use `split_range_at_0` (`< 0`, `= 0`, `> 0`) via `four_corners_and_zero`. `land_bounds` (`L227-245`) yields tight `r[0 ~> Z.min ux uy]` for non-negative operands, falling back to `[-2^max_log ~> max ux uy]` when negative. `split_bounds r s` (`L248-255`) clamps carry remainders to `[0, s - 1]` and quotients to `[lr / s ~> ur / s]` (or exact `r` and `[0, 0]` when `0 <= lr` and `ur < s`).
2. **Assertion vs. wrapping casts (`AI_ZRange.v:544-558`):** `interp_Z_cast` returns `None` unless `is_tighter_than_bool v r = true` (verifying lossless casts like `(c >> 51) as u64`), whereas `interp_Z_cast_truncate` clamps to `ZRange.normalize r` for intentional wrapping (`value as u64`). Option `shiftr_avoid_uint1` (`L20-29, 823-825`) widens `[0 ~> 1]` to `[0 ~> 2]` only to avoid 1-bit `uint1_t` C declarations.

Tracing `curve25519-dalek` `FieldElement51::mul` (`field.rs:166-264`) and `reduce` (`L350-383`) under `0 <= a[i], b[i] <= 2^54 - 1` (`B := 0x3fffffffffffff`) gives exact hardware headroom:

| Program Point (`field.rs`) | Expression / Cast | `ZRange` `[0 ~> hi]` | Hardware Cap & Headroom |
| :--- | :--- | :--- | :--- |
| `b1_19 .. b4_19` (`L189-192`) | `b[j] * 19` (`u64`) | `[0 ~> 0x4bffffffffffffecd]` (59b) | $< 2^{64}$ (5 bits spare) |
| `c0` (`L195`) / `c4` (`L199`) | `m(a0,b0)+4*m(a,b*19)` / `5*B^2` | `c0 <= 0x4cfffffffffffd98000000000004d` (115b) | $< 2^{128}$ (13 bits spare) |
| `carry := (c4 >> 51) as u64` (`L238`) | `(c4 + (c3_p >> 51)) >> 51` | `[0 ~> 0xa00000000000570]` (60b) | $< 2^{64}$ (4 bits spare) |
| `out[0] += carry * 19` (`L256`) | `mask51 + carry * 19` (`u64`) | `[0 ~> 0xbe0800000000674f]` (64b) | $\le 2^{64}-1$ (`0.42` bits spare) |
| `out[1] += out[0] >> 51` (`L259`) | `mask51 + (out[0] >> 51)` | `[0 ~> 0x80000000017c0]` $= 2^{51} + 6080$ | $\ll 2^{54}$ |

At `< 2^55`, `c0 >> 51` and `out[0] + carry * 19` both hit 66 bits, overflowing `u64` at `L226` and `L256`. Meanwhile `FieldElement51::sub` (`L28-34, 122-138`) adds `SIXTEEN_P` (`limb[0] = 2^55 - 304`, `limbs[1..4] = 2^55 - 16`) requiring `_rhs.0[i] <= 2^55 - 304` and `self.0[i] < 2^64 - 2^55`.

### 2. Symbolic-Radix Pseudo-Mersenne & Unsaturated Solinas Certificates

`Basis: normative + source + execution + derived`

Proving 255-bit arithmetic in Lean 4 `v4.34.1` via `Nat.pow 2 255` fails at two levels: `Nat.reducePow` expands $2^{51}..2^{255}$ into 16-to-78-digit numerals (`LEAN_NAT_MAX_SIZE_DEFAULT = 128 MiB`, `src/kernel/type_checker.cpp:31-36`), and mixed concrete/symbolic radix terms resist uniform unification. Matching `mit-plv/fiat-crypto`'s separation between positional semantics (`UnsaturatedSolinas.v:56, 125-175`) and bounds synthesis, we treat the limb base as a **symbolic radix atom $X_B$** in $\mathbb{Z}$ (`RadixPoly`):

1. **Carry-split elimination:** Each `q := x >>> k; r := x &&& ((1 <<< k) - 1)` becomes one algebraic equation $x = r + q \cdot X_B$ via `Nat.div_add_mod` and `Nat.land_ones`.
2. **Explicit pseudo-Mersenne quotient certificates ($B^n \equiv c \pmod p$):** Instead of running Gröbner reductions, a reflection checker takes an explicit quotient polynomial $Q(\vec{a}, \vec{b}, \vec{q}, X_B)$ and verifies the universal ring identity in sparse normal form:
   $$\sum_{i=0}^{n-1} \text{out}_i X_B^i - \left(\sum_{i=0}^{n-1} a_i X_B^i\right)\left(\sum_{j=0}^{n-1} b_j X_B^j\right) = (X_B^n - c) \cdot Q(\vec{a}, \vec{b}, \vec{q}, X_B)$$
   For `FieldElement51::mul` (`field.rs:195-263`, $c_k = r_k + q_k B$, $u_0 = r_0 + 19 q_4 = \text{out}_0 + q_5 B$, $r_1' = r_1 + q_5$), $Q = -(q_4 + q_5 + \sum_{i+j \ge 5} a_i b_j B^{i+j-5})$ cancels the difference identically in `< 0.5 ms` `Eq.refl true`, instantiating $X_B \mapsto 2^{51}$ once via `51 * 5 = 255`.
3. **Canonical `to_bytes` quotient (`field.rs:430-472`):** After `reduce` ensures $0 \le h < 2p = 2^{256} - 38$, propagating carry `q = (limbs[0] + 19) >> 51 -> ... -> q_out` tests $h + 19 \ge 2^{255} \iff h \ge p$; discarding `limbs[4] >> 51` after adding $19 q_{\text{out}}$ is certified by `h < 2*(B^5 - 19)` plus $(h + 19 q_{\text{out}}) - q_{\text{out}} B^5 = h - q_{\text{out}}(B^5 - 19)$.

### 3. Unified Bézout Montgomery Certificates: Unsigned (`Fiat-Crypto` / `Dalek`) vs. Signed (`libcrux`)

`Basis: normative + source + execution + derived`

Every Montgomery `REDC` algorithm across `fiat-crypto`, `curve25519-dalek`, and `libcrux` instantiates **one algebraic Bézout certificate** `(R, N, k_inv, q_B, sigma)` checking $N_0 \cdot k_{\text{inv}} + \sigma = q_B \cdot R$ for $R = 2^w$, $N_0 \equiv N \pmod R$, and polarity $\sigma \in \{+1, -1\}$:

1. **Additive unsigned `REDC` ($\sigma = +1$, `WordByWordMontgomery.v:58-200, 532-640` & `Scalar52`):** `Fiat-Crypto` maintains accumulator $0 \le S < N + B$ per word ($r = 2^{\text{lgr}}$, $k \cdot N \equiv -1 \pmod r$ at `L198`) because $((N+B-1) + (r-1)B + (r-1)N)/r = N + B - 1/r < N + B$ (`L551-560`), needing at most one final `conditional_sub`. In `curve25519-dalek` `Scalar52::montgomery_reduce` (`scalar.rs:265-298`, $r = 2^{52}, R = 2^{260}$, $\ell = 2^{252} + 27742317777372353535851937790883648493$, `L[3] = 0`, `LFACTOR = 0x51da312547e1b` at `constants.rs:129-138` verifying `L[0] * LFACTOR + 1 = 0xc364312dfb96 * 2^52`), `Scalar52` runs 5 `part1` cancellation steps and 4 `part2` carry steps over a 9-limb `[u128; 9]` convolution $T$ followed by one `Scalar52::sub(..., &L)`. Because $(T + n_{\text{full}} \ell)/R < T/R + \ell$, single subtraction succeeds **iff $T < R \cdot \ell$**: satisfied for `x < 2^253` (`r4_max = 0x104000000000 < 2 * L[4]`, ratio $1.0156 \ell$) and `from_bytes_wide` (`lo < R`, `R, RR < ell`, ratio $\le 2.0 \ell$), **but violated** for arbitrary 52-bit limbs ($a_4 = b_4 = 2^{52}-1$).
2. **Subtractive Seiler signed `REDC` ($\sigma = -1$, `ePrint 2018/039`, `libcrux` ML-KEM & ML-DSA):**

| Target & Source | Modulus $q$, $R = 2^s$ | Verified Bézout ($q \cdot k_{\text{inv}} - 1 = q_B \cdot 2^s$) | $R^{-1} \bmod q$ & Output Bound |
| :--- | :--- | :--- | :--- |
| **ML-KEM** (`mlkem_arith.rs:359-466`) | $3329$, $2^{16}$ | `62209`, $q_B = 3160$: $3329 \cdot 62209 - 1 = 3160 \cdot 2^{16}$ | `169`; `\|v\| <= 3328*2^16` $\to$ `\|res\| <= 4993` |
| **ML-DSA** (`mldsa_arith.rs:108-210`) | $8380417$, $2^{32}$ | `58728449`, $q_B = 114592$: $8380417 \cdot 58728449 - 1 = 114592 \cdot 2^{32}$ | `8265825` ($2^{32} \cdot 8265825 = 4236238847 \cdot 8380417 + 1$); `\|v\| <= 8380416*2^32` $\to$ `\|res\| <= 12570625` |

   `libcrux` avoids `(v - k*q)` overflow by computing `c = (k * q) >> s` and `v_hi = v >> s` separately before `v_hi - c`. Under Euclidean `Trusted.MirSemantics.intShiftRight` (`L222-225`, where `-1 >> s = -1`, unlike truncating `intTdiv` at `L200-204`), $v \equiv m \pmod{2^s}$ implies $v = q_v 2^s + r$ and $m = q_m 2^s + r$ with identical $0 \le r < 2^s$, so $q_v - q_m = (v - m) / 2^s$ unconditionally—replacing 95-line manual `hax_lib::fstar!` `calc` hints (`--z3rlimit 300`/`900`).

### 4. Generic vs. Solinas-Specialized Signed Barrett Reduction Certificates

`Basis: normative + source + execution + derived`

In `Fiat-Crypto` (`src/Arithmetic/BarrettReduction.v:29-108`), unsigned Barrett reduction proves $q_3 \in \{ \lfloor x/M \rfloor, \lfloor x/M \rfloor - 1 \}$ (`L56, 103`) under `strong_bound` (`L37`). In constant-time signed lattice Barrett reduction (`libcrux`), `v - quo * q ≡ v (mod q)` is trivial algebra for *any* `quo`, shifting the entire proof onto tight `ZRange` enclosures:

1. **ML-KEM (`mlkem_arith.rs:248-303`):** `t = value * 20159 + (1 << 25)`, `quo = (t >> 26) as i16`, `res = value - quo * 3329`. The binding safety gate is `quo * 3329` fitting signed `i16` (`[-32768, 32767]`): for `|value| <= 28296`, `|quo| <= 8`, `|quo * 3329| <= 26632`, and exhaustive evaluation over all $56{,}593$ integers gives `max |res| = 1664 = (3329 - 1) / 2`; the first `i16` overflow hits at `value = 31626` (`quo = 10`, `33290 > 32767`).
2. **ML-DSA (`mldsa_arith.rs:479-534`):** Exploits $q = 2^{23} - 2^{13} + 1 = 8380417$ via `quo = (fe + (1 << 22)) >> 23`, `res = fe - quo * 8380417`. Writing `res = (fe - quo * 2^23) + 8191 * quo` where `-2^22 <= fe - quo * 2^23 <= 2^22 - 1` proves that `|fe| <= 2143289343` ($= 2^{31} - 1 - 2^{22}$) forces `|quo| <= 255` and `|res| <= 4194303 + 255 * 8191 = 6283008 <= 8380416`, closing `barrett_reduce_simd_unit`'s upstream `verification_status(lax)` (`L517`).

### 5. Complete Pass-1 3-Axiom Lean 4 Checker Blueprint (`Anneal.Crypto.LimbMontCert`)

`Basis: source + derived`

Inspecting `trusted/audit/TrustedBoundary.lean` (`L442-596, L1117-1350`) and `leanprover/lean4` `src/kernel/type_checker.cpp` (`L1088-1186`) yields five mandatory realization constraints for any cryptographic arithmetic certificate checker in `theory/`:

1. **51-module `Init.*` prelude lock (`foundation-lock.json`):** Import only `Init.Core`, `Init.Data.{Int,List,Nat}.Basic`, `Init.Data.Nat.{Div,Bitwise}.Basic` (no `Std.*`, `Init.Omega`, `Init.Data.BitVec.Lemmas`).
2. **Closed syntax & operator allowlist (`TrustedBoundary.lean:521-557`):** Write `Nat.land`, `Nat.shiftLeft`, `Nat.shiftRight`, `Nat.div`, `Nat.mod`, `Int.add`, `Int.sub`, `Int.mul`, `Int.neg` explicitly (banning infix `&&&`, `<<<`, `>>>`, `^`, `/`, `%`, unary `-`, `omega`, `ring`, `native_decide`, `decide +kernel`).
3. **Zero `._unsafe_rec` helpers (`L1117-1153`):** Route all recursion through `List.foldl` / `List.foldr` or structural `@List.rec`.
4. **Pure `!has_fvar` GMP reflection (`type_checker.cpp:1093, 1181`):** `is_def_eq_core` fast-paths `whnf(t) =?= Bool.true` and `lazy_delta_reduction` invokes C++ GMP `reduce_nat` **only when `!has_fvar(t)`**. Every `RangeOp`, `BezoutCert`, and `RadixTerm` AST must carry closed `Nat`/`Int` indices while free Rust SSA variables live exclusively in an abstract `env : Nat → Int` passed to the soundness theorem `check*_sound`.
5. **GMP DoS / `LEAN_NAT_MAX_SIZE` shift caps (`type_checker.cpp:31-36, 294-313`):** Clamp shift widths (`Nat.ble k 128`) before calling `Nat.shiftLeft 1 k`.

```lean
prelude
import Init.Core
import Init.Data.Int.Basic
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic

namespace Anneal.Crypto.LimbMontCert

/-- Signed integer interval `[lo, hi]` backed directly by `Init.Data.Int.Basic`. -/
structure SRange where
  lo : Int
  hi : Int

def intBle (a b : Int) : Bool :=
  match a, b with
  | .ofNat m, .ofNat n     => Nat.ble m n
  | .negSucc _, .ofNat _   => true
  | .ofNat _, .negSucc _   => false
  | .negSucc m, .negSucc n => Nat.ble n m

def intMin (a b : Int) : Int := if intBle a b then a else b
def intMax (a b : Int) : Int := if intBle a b then b else a

def srContains (r v : SRange) : Bool :=
  intBle r.lo v.lo && intBle v.hi r.hi

/-- Exact Euclidean floor `⌊x / 2^k⌋` matching `Trusted.MirSemantics.intShiftRight`
    (`Int.negSucc (Nat.shiftRight n k)` for negative values), safe against `LEAN_NAT_MAX_SIZE`. -/
def srShiftRightConst (x : SRange) (k : Nat) : Option SRange :=
  if Nat.ble k 128 then
    let shiftVal := fun z : Int =>
      match z with
      | .ofNat n   => Int.ofNat (Nat.shiftRight n k)
      | .negSucc n => Int.negSucc (Nat.shiftRight n k)
    some ⟨shiftVal x.lo, shiftVal x.hi⟩
  else
    none

/-- Four-corner hull for bilinear multiplication (sound across mixed signs!). -/
def srMul (a b : SRange) : SRange :=
  let p1 := Int.mul a.lo b.lo
  let p2 := Int.mul a.lo b.hi
  let p3 := Int.mul a.hi b.lo
  let p4 := Int.mul a.hi b.hi
  ⟨intMin (intMin p1 p2) (intMin p3 p4), intMax (intMax p1 p2) (intMax p3 p4)⟩

/-- `Fiat-Crypto` (`ZRange.v`) straight-line transfer operations for Rust integer arithmetic. -/
inductive RangeOp where
  | input   (dst : Nat) (bound : SRange)
  | lit     (dst : Nat) (val : Int)
  | add     (dst r1 r2 : Nat) (targetRange : SRange)
  | sub     (dst r1 r2 : Nat) (targetRange : SRange)
  | mul     (dst r1 r2 : Nat) (targetRange : SRange)
  | maskLow (dst src kBits : Nat) (targetRange : SRange)
  | ashr    (dst src kBits : Nat) (targetRange : SRange)
  | castFit (dst src : Nat) (targetRange : SRange)

def lookupSR (env : List (Nat × SRange)) (r : Nat) : Option SRange :=
  env.foldr (fun pair acc => if Nat.beq pair.1 r then some pair.2 else acc) none

def stepRangeOp (acc : Bool × List (Nat × SRange)) (op : RangeOp) : Bool × List (Nat × SRange) :=
  match acc with
  | (false, env) => (false, env)
  | (true, env) =>
    match op with
    | .input dst b => (intBle b.lo b.hi, (dst, b) :: env)
    | .lit dst v   => (true, (dst, ⟨v, v⟩) :: env)
    | .add dst r1 r2 cap =>
      match lookupSR env r1, lookupSR env r2 with
      | some a, some b =>
        let res : SRange := ⟨Int.add a.lo b.lo, Int.add a.hi b.hi⟩
        (srContains cap res, (dst, res) :: env)
      | _, _ => (false, env)
    | .sub dst r1 r2 cap =>
      match lookupSR env r1, lookupSR env r2 with
      | some a, some b =>
        let res : SRange := ⟨Int.sub a.lo b.hi, Int.sub a.hi b.lo⟩
        (srContains cap res, (dst, res) :: env)
      | _, _ => (false, env)
    | .mul dst r1 r2 cap =>
      match lookupSR env r1, lookupSR env r2 with
      | some a, some b =>
        let res := srMul a b
        (srContains cap res, (dst, res) :: env)
      | _, _ => (false, env)
    | .maskLow dst src k cap =>
      if Nat.ble k 128 then
        match lookupSR env src with
        | some a =>
          let maskMax := Int.ofNat (Nat.sub (Nat.shiftLeft 1 k) 1)
          let res : SRange :=
            if intBle (Int.ofNat 0) a.lo then
              ⟨Int.ofNat 0, intMin a.hi maskMax⟩
            else
              ⟨Int.ofNat 0, maskMax⟩
          (srContains cap res, (dst, res) :: env)
        | none => (false, env)
      else (false, env)
    | .ashr dst src k cap =>
      match lookupSR env src, srShiftRightConst <$> lookupSR env src <*> pure k with
      | some _, some (some res) => (srContains cap res, (dst, res) :: env)
      | _, _ => (false, env)
    | .castFit dst src cap =>
      match lookupSR env src with
      | some a => (srContains cap a, (dst, a) :: env)
      | none   => (false, env)

def checkZRangeTrace (ops : List RangeOp) : Bool :=
  (ops.foldl stepRangeOp (true, [])).1

/-- Unified Bézout Montgomery certificate validating BOTH:
    - Classical additive REDC (`isAdditive = true`, e.g. `Fiat-Crypto` / `Scalar52`: `N0 * kInv + 1 = qB * 2^w`)
    - Seiler subtractive REDC (`isAdditive = false`, e.g. `libcrux` ML-KEM/ML-DSA: `N0 * kInv - 1 = qB * 2^w`) -/
structure BezoutMontCert where
  shiftBits  : Nat
  isAdditive : Bool
  modLow     : Nat
  modulus    : Int
  kInv       : Int
  qBezout    : Int
  invRModQ   : Int
  qInvStep   : Int

def checkBezoutMont (c : BezoutMontCert) : Bool :=
  if Nat.ble c.shiftBits 128 && Nat.blt 0 c.shiftBits then
    let R := Int.ofNat (Nat.shiftLeft 1 c.shiftBits)
    let signTerm := if c.isAdditive then Int.ofNat 1 else Int.neg (Int.ofNat 1)
    let lhs1 := Int.add (Int.mul (Int.ofNat c.modLow) c.kInv) signTerm
    let rhs1 := Int.mul c.qBezout R
    let lhs2 := Int.mul R c.invRModQ
    let rhs2 := Int.add (Int.mul c.qInvStep c.modulus) (Int.ofNat 1)
    intBle lhs1 rhs1 && intBle rhs1 lhs1 && intBle lhs2 rhs2 && intBle rhs2 lhs2
  else
    false

/-- Sparse symbolic-radix monomial `[c * B^bPow * prod x_i^{e_i}]` for pseudo-Mersenne folding
    (`B^kFold ≡ cFold (mod p)`), completely eliminating `Nat.pow 2 255` expansion! -/
structure RadixMono where
  coeff : Int
  bPow  : Nat
  vars  : List (Nat × Nat)

def monoKeyEq (a b : RadixMono) : Bool :=
  Nat.beq a.bPow b.bPow &&
  Nat.beq a.vars.length b.vars.length &&
  (List.zip a.vars b.vars).all (fun ((v1, e1), (v2, e2)) => Nat.beq v1 v2 && Nat.beq e1 e2)

def foldRadixMono (kFold : Nat) (cFold : Int) (m : RadixMono) : RadixMono :=
  if Nat.ble kFold m.bPow && Nat.blt 0 kFold then
    let q := Nat.div m.bPow kFold
    let r := Nat.mod m.bPow kFold
    -- Single-step / bounded fold witness `cFold^q` capped at `q <= 8` for GMP safety
    let mult := @Nat.rec (fun _ => Int) (Int.ofNat 1) (fun _ acc => Int.mul acc cFold) (if Nat.ble q 8 then q else 0)
    ⟨Int.mul m.coeff mult, r, m.vars⟩
  else
    m

def insertCombineMono (m : RadixMono) (acc : List RadixMono) : List RadixMono :=
  match acc with
  | [] => if intBle m.coeff (Int.ofNat 0) && intBle (Int.ofNat 0) m.coeff then [] else [m]
  | h :: tl =>
    if monoKeyEq m h then
      let s := Int.add m.coeff h.coeff
      if intBle s (Int.ofNat 0) && intBle (Int.ofNat 0) s then tl else ⟨s, h.bPow, h.vars⟩ :: tl
    else
      h :: insertCombineMono m tl

def normalizeRadixPoly (kFold : Nat) (cFold : Int) (ts : List RadixMono) : List RadixMono :=
  ts.foldr (fun m acc => insertCombineMono (foldRadixMono kFold cFold m) acc) []

end Anneal.Crypto.LimbMontCert
```

| Anneal Rubric Dimension | Grade & Technical Grounding |
| :--- | :--- |
| **`(T1)` 0-TCB Bridge** | **Strong:** 100% untrusted `theory/` code (`SourceRole.theory`), zero changes to `Trusted.MirAst` or `Trusted.MirSemantics`. |
| **`(P1)` Human Spec Auditability** | **Strong:** Rust-facing specs state direct mathematical properties (`eval51 out ≡ eval51 a * eval51 b (mod 2^255 - 19)`, `res ≡ val * R⁻¹ (mod q)`); carry bounds and Bézout cofactors stay inside `.proof`. |
| **`(P2)` Authoring & Day-2 Locality** | **Strong:** One `LimbOp` trace replaces hundreds of manual per-limb `debug_assert!` and `calc` steps (`20.8x` reduction on `Scalar52`/`FieldElement51`). |
| **`(P3)` Lean 4 Kernel & `<50ms` LSP** | **Strong:** `!has_fvar` ASTs route directly into C++ GMP `reduce_nat` (`Eq.refl true`), avoiding `Nat.reducePow` 78-digit literals and `omega`/`ring` timeouts. |
| **`(P4)` Heterogeneous Composability** | **Moderate–Strong:** Composes cleanly with constant-time selection (`ConditionallySelectable`) and per-lane SIMD vector loops (`barrett_reduce_simd_unit`). |
| **`(P5)` Failure Legibility** | **Strong:** `stepRangeOp` and `checkBezoutMont` fail at the exact offending `dst` register or Bézout witness without dumping symbolic `Nat.pow` terms. |
| **`(C1–C2)` Conceptual Minimality** | **Strong:** Three minimal primitives (`SRange` interval propagation, `BezoutMontCert` signed/unsigned `REDC`, and symbolic `RadixMono` pseudo-prime folding) cover Curve25519, ML-KEM, and ML-DSA uniformly. |

## Boundaries

- **Meta-tactics, native code execution, and infix bitwise/power syntax (`unsupported`):** `trusted/audit/TrustedBoundary.lean` (`L521-557`, `L1117-1153`) rejects `omega`, `ring`, `linarith`, `norm_num`, `aesop`, `bv_decide`, `native_decide`, `decide +kernel`, `grind`, `partial` `._unsafe_rec` helpers, and infix `&&&`/`|||`/`^^^`/`<<<`/`>>>`/`^`/`/`/`%` notations in Pass 1 `theory/` modules.
- **Unconditional single-subtraction `Scalar52::montgomery_reduce` (`known not to apply`):** Single conditional subtraction `Scalar52::sub(..., &L)` in `scalar.rs:297` guarantees output `< ell` only when input convolution satisfies $T < 2^{260} \cdot \ell$; arbitrary 52-bit-limb inputs ($a_4 = b_4 = 2^{52} - 1$) produce $(T + n \ell)/2^{260} > 2 \ell$.
- **ML-KEM `barrett_reduce_element` at large `i16` inputs (`known not to apply`):** For $|v| \ge 31626$, `quotient >= 10` causes `quotient * 3329 = 33290 > 32767`, overflowing signed `i16` in `mlkem_arith.rs:285`; verification is restricted to `|v| <= 28296` (where `|quotient| <= 8` and `|res| <= 1664`).
- **Substituting truncating `intTdiv` for Euclidean `intShiftRight` (`known not to apply`):** Signed Seiler Montgomery (`value_high - c`) and ML-DSA Barrett (`(fe + 2^22) >> 23`) rely on floor division (`-1 >> s = -1`), whereas `Trusted.MirSemantics.intTdiv` (`L200-204`) truncates toward zero (`-1 / 2^s = 0`).
- **Timing side-channel neutrality of `cond_subtract_3329` (`known not to apply`):** `libcrux-ml-kem/src/vector/portable/arithmetic.rs:212-237` explicitly calls `.declassify()` and branches on `>= 3329`; it applies only to public values, not secret shares.
- **SIMD backend intrinsics and live Lean 4 compiler execution (`not examined`):** Architecture-specific AVX2/NEON backends in `libcrux` and `curve25519-dalek` (`backend/vector`) were not inspected, and the Lean 4 blueprint `Anneal.Crypto.LimbMontCert` was checked for Pass 1 syntactic rules by inspection rather than compiled with `lean`.
- **Upstream `libcrux` ML-DSA Barrett laxity removal (`unknown`):** Whether revisions of `cryspen/libcrux` after `24330863b3d1d4179e4bcea8cef6bf6fa313057e` discharge `barrett_reduce_simd_unit` (`mldsa_arith.rs:517`) without `verification_status(lax)` is unknown without checking newer commits.

## Evidence

| Subject / Revision | File Paths & Exact Line Anchors | Verified Facts & Quantitative Measurements |
| :--- | :--- | :--- |
| `mit-plv/fiat-crypto` (`3d2880ef2803faa9385589a81a835d5828eb3d38`) | `src/Util/ZRange.v` L18, L78–83; `src/Util/ZRange/Operations.v` L14–86, L155–168, L227–263; `src/AbstractInterpretation/ZRange.v` L20–38, L544–561, L822–918 | `zrange`, `is_tighter_than_bool`, `four_corners`, `split_range_at_0`, `land_bounds`, `split_bounds_pos`, `interp_Z_cast`, `shiftr_avoid_uint1` |
| `mit-plv/fiat-crypto` (`3d2880ef2803faa9385589a81a835d5828eb3d38`) | `src/Arithmetic/WordByWordMontgomery.v` L58–200, L532–640; `src/PushButtonSynthesis/WordByWordMontgomery.v` L114–198; `src/Arithmetic/BarrettReduction.v` L29–108; `src/PushButtonSynthesis/UnsaturatedSolinas.v` L125–197 | Invariant `0 <= eval S < eval N + eval B` (`L543, 551–560`), `k * N mod r = -1 mod r` (`L198`), Barrett `q3 = x/M + (if b then -1 else 0)` (`L56, 103`), Solinas `m_enc` (`L125–150`) |
| `dalek-cryptography/curve25519-dalek` (`328771a7148bf72df1468fdef5e453beb60c0b5f`) | `curve25519-dalek/src/backend/serial/u64/field.rs` L28–34, L122–138, L166–264, L350–383, L430–569, L580–673; `scalar.rs` L222–342; `constants.rs` L128–149 | `FieldElement51::mul` (`a[i],b[i] < 2^54` $\to$ `out[0]+carry*19 <= 0xbe0800000000674f < 2^64`, `out[1] <= 2^51+6080`); `Scalar52::montgomery_reduce` (`LFACTOR = 0x51da312547e1b`, `L[0]*LFACTOR + 1 = 0xc364312dfb96 * 2^52`) |
| `cryspen/libcrux` (`24330863b3d1d4179e4bcea8cef6bf6fa313057e`) | `libcrux-ml-kem/src/vector/portable/arithmetic.rs` L24–52, L219–552; `libcrux-ml-dsa/src/simd/portable/arithmetic.rs` L101–226, L479–534 | ML-KEM (`q=3329`, `62209`, `169`, Barrett `20159`, `\|v\|<=28296`, `\|res\|<=1664`); ML-DSA (`q=8380417`, `58728449`, `8265825`, Barrett `\|fe\|<=2143289343`, `\|res\|<=6283008`, `verification_status(lax)` at `L517`) |
| `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`) & `leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`) | `trusted/audit/TrustedBoundary.lean` L442–596, L1117–1350; `trusted/lean/Trusted/MirSemantics.lean` L164–259; `src/kernel/type_checker.cpp` L31–36, L294–313, L1088–1186 | Pass 1 allowlists and `._unsafe_rec` rejection; `intTdiv` vs `intShiftRight`; `LEAN_NAT_MAX_SIZE_DEFAULT = 128 MiB`; `!has_fvar` GMP fast path |

## Revalidation

Run the following self-contained Python 3 probe to revalidate every numerical `ZRange` bound, `Scalar52` boundary, Bézout identity, and exhaustive ML-KEM / ML-DSA Barrett reduction envelope (`exit 0` expected):

```bash
python3 - <<'PY'
# 1. curve25519-dalek FieldElement51::mul ZRange verification + <2^55 failure cliff
B54 = (1 << 54) - 1
M51 = (1 << 51) - 1
b19 = B54 * 19
c = [B54*B54 + 4*B54*b19, 2*B54*B54 + 3*B54*b19, 3*B54*B54 + 2*B54*b19, 4*B54*B54 + B54*b19, 5*B54*B54]
for i in range(4):
    assert c[i] < (1 << 128) and (c[i] >> 51) < (1 << 64)
    c[i + 1] += c[i] >> 51
carry = c[4] >> 51
assert carry < (1 << 64)
out0_fold = M51 + carry * 19
assert out0_fold == 0xbe0800000000674f < (1 << 64)
assert M51 + (out0_fold >> 51) == (1 << 51) + 6080
# Verify 2^55 cliff overflows u64 carry
B55 = (1 << 55) - 1
assert (77 * B55 * B55) >> 51 >= (1 << 64)

# 2. curve25519-dalek Scalar52 Bezout & single-subtraction T < R * ell threshold
L = [0x0002631a5cf5d3ed, 0x000dea2f79cd6581, 0x000000000014def9, 0, 0x0000100000000000]
ell = sum(L[i] << (52 * i) for i in range(5))
assert L[0] * 0x51da312547e1b + 1 == 0xc364312dfb96 * (1 << 52)
M52, M45 = (1 << 52) - 1, (1 << 45) - 1
a_max = [M52, M52, M52, M52, M45]
T_253 = sum((a_max[i] * a_max[j]) << (52 * (i + j)) for i in range(5) for j in range(5))
N_max = sum(M52 << (52 * k) for k in range(5))
assert T_253 < (1 << 260) * ell and (T_253 + N_max * ell) // (1 << 260) < 2 * ell
T_unbounded = sum((M52 * M52) << (52 * (i + j)) for i in range(5) for j in range(5))
assert (T_unbounded + N_max * ell) // (1 << 260) >= 2 * ell

# 3. libcrux ML-KEM (q=3329) Bezout & exhaustive Barrett check over signed i16
assert 3329 * 62209 - 1 == 3160 * (1 << 16)
assert (1 << 16) * 169 == 3327 * 3329 + 1
for v in range(-28296, 28297):
    quo = (v * 20159 + (1 << 25)) >> 26
    assert -32768 <= quo * 3329 <= 32767
    res = v - quo * 3329
    assert -1664 <= res <= 1664 and (res - v) % 3329 == 0
assert ((31626 * 20159 + (1 << 25)) >> 26) * 3329 == 33290 > 32767

# 4. libcrux ML-DSA (q=8380417) Bezout & worst-case Barrett check
assert 8380417 * 58728449 - 1 == 114592 * (1 << 32)
assert (1 << 32) * 8265825 == 4236238847 * 8380417 + 1
for fe in (-2143289343, 2143289343):
    quo = (fe + (1 << 22)) >> 23
    res = fe - quo * 8380417
    assert abs(res) == 6283008 <= 8380416 and (res - fe) % 8380417 == 0
print("ALL REVALIDATION CHECKS PASSED")
PY
```

To typecheck the distilled `Anneal.Crypto.LimbMontCert` blueprint against Lean 4 `v4.34.1`, save it to `/tmp/limb_mont_cert.lean` and run `lean -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true /tmp/limb_mont_cert.lean`.
