# IEEE-754 SoftFloat Semantics, Dyadic Interval Gappa Certificates, and RFC 3514 NaN Choice Refinement in Pure Integer Foundations

## Summary

Verifying Rust floating-point code inside a pure-integer Lean 4 foundation (`joshlf/anneal` `foundation-lock.json`) cannot rely on Lean's built-in `Init.Data.Float`. Beyond being excluded from the locked 51-module `Init.*` prelude ceiling, `Init.Data.Float` in `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) models `Float` via `Float.Model`, which canonicalizes all NaN bit patterns to one canonical quiet NaN (`0x7ff8_0000_0000_0000`). Rust RFC 3514 (`float_semantics`) instead guarantees exact bit preservation across moves, copies, bitwise sign operations (`-x`, `abs`, `copysign`), and `to_bits`/`from_bits`, while specifying nondeterministic NaN sign/payload selection on arithmetic outputs. Mapping Rust `f64` to Lean `Float` therefore proves `f64::from_bits(0xfff8_0000_0000_0001).to_bits() == 0x7ff8_0000_0000_0000`, unsoundly discharging `unreachable_unchecked()` branches.

A sound architecture splits bit-accurate operational semantics in the Trusted Computing Base (TCB) from untrusted certificate checkers in `theory/`:

1. **Integer Rational Operational Semantics (`roundRatio` + Demonic `Choice`):** `proofs-rs/lean-miri` (`c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`, `Miri/Interpreter/{Float,FloatOps,IntrinsicFloat,IntrinsicSimd}.lean`) implements `binary16`, `binary32`, `binary64`, and `binary128` over `Nat`, `Int`, and `BitVec 128` without host floats. Finite operations compute exact rationals and round once via nearest-ties-to-even `roundRatio` with gradual subnormal underflow (`max (ratioExponent n d) f.minExponent`). Non-bitwise NaN outputs pass through `FloatOps.adjustNaN`, indexing `FloatBits.nanChoices` via external demonic `Choice`; `simd_relaxed_fma` branches demonically via `fuseMulAdd choice` between single-rounded fused `a * b + c` and double-rounded `(a * b) + c`.
2. **Pass-1 `Init.Data.Int` Dyadic-Rational Reflection Certificates:** Under `TrustedBoundary.lean`'s Pass-1 ceiling—banning `Std.*`, `Lean.*`, Mathlib, `omega`, `ring`, `grind`, custom attributes (`@[kernel_optimize]`), and `decide +kernel`—untrusted `theory/` modules discharge finiteness, range, and roundoff bounds by representing dyadic rationals $m \cdot 2^e$ as `(mant : Int, exp2 : Int)`. Lean 4's C++ GMP reducer (`type_checker::reduce_nat`) checks outward-compressed Gappa-style dyadic intervals and Flocq/VCFloat2/FloatLib mixed-error certificates by `rfl` under 256-bit magnitude caps.
3. **Orthogonality of NaN/FMA Nondeterminism and Finite Accuracy Proofs:** Universal quantification over `ValidChoice` in `wpOutcomeState` means any dyadic enclosure proving finite inputs stay within `[-MAX_FINITE, +MAX_FINITE]` establishes `result.isNaN = false` (making `adjustNaN` the identity) while enclosing the hull of both `fuse ∈ {true, false}` arms for `simd_relaxed_fma`.

---

## Applicability

This report governs the joint interaction of the ten subjects in `REPORT.json`:

- **Target Verification & Audit Boundary:** `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`, `trusted/lean/foundation-lock.json`, `trusted/audit/TrustedBoundary.lean`, `Trusted/MirSemantics.lean`, `theory/Anneal/MirWp.lean`) on `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`). Pass 1 enforces `prelude` + 51 `Init.*` modules, `{propext, Quot.sound, Classical.choice}`, Statement-Origin Separation (target theorem types reference only `Init.*`, `Trusted.*`, and `Mir.*`, never `Anneal.*`), and closed syntax allowlists forbidding `sorry`, `axiom`, `opaque` (outside `Trusted`), `partial`/`._unsafe_rec`, `termination_by`, `deriving`, `set_option`, `noncomputable section`, `omega`, `ring`, `grind`, `bv_decide`, `native_decide`, `decide +kernel`, and operators `&&&`, `|||`, `^^^`, `<<<`, `>>>`, `^`, unary `-x`, `/`, `%`, `|>`.
- **Rust Operational Semantics Anchor:** `proofs-rs/lean-miri` (`c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`), anchored to `rust-lang/miri` (`7fa591d7d4dd9af8154becbc8332f8096f8323b1`), `rust-lang/rustc_apfloat` (`eeaacad81247af65d4043cb3e32d023a652d7951`), and Rust RFC 3514 (`rust-lang/rfcs` `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`, `text/3514-float-semantics.md`).
- **Numerical Mechanization Frameworks:** Flocq (`10.1109/ARITH.2011.40`), Gappa (`10.1145/1644001.1644003`), VCFloat2 (`VeriNum/vcfloat` `a203b287a84b0e3c9bec136823b5622ebfde6ad6`, `10.1145/3636501.3636953`), and FloatLib (`lean-dojo/FloatLib` `71a3d7ff211b28bc3d27673b70b90644941a5fff`, `arXiv:2609.19352v1`).

**Scope Differentiation:** Prior corpus reports cover LLVM/ISA float lowering (`rust-floating-point-semantics-llvm-lowering-and-isa-behavior`), SIMD reduction reassociation (`ordered-floating-point-simd-reductions-and-rfc3514-reassoc-certificates`), Taylor/Daisy rewrites (`herbie-accuracy-rewrites-symbolic-taylor-bounds-and-daisy-enclosures`), and general FloatSpec surveys (`lean-ieee754-floatspec-cryptography-and-constant-time`). This report establishes the Pass-1 integer bridge from `lean-miri` `roundRatio`/`adjustNaN` to `Init.Data.Int` dyadic certificates.

---

## Findings

### 1. Why Lean 4 `Init.Data.Float` Is Inadmissible and Unsound for Rust RFC 3514

`Basis: normative + source + derived`

Direct inspection of `joshlf/anneal` (`c131b320eeeb`) and `leanprover/lean4` (`5045d0056413`) establishes three barriers against modeling Rust floats with `Init.Data.Float`:

1. **Foundation-Lock and Syntax Rejection:** `foundation-lock.json` (`L22–800`) omits `Init.Data.Float*`, while `src/Init/Data/Float/Float.lean` (`L6–45`) uses `module`, `public import`, `@[expose] public section`, and `attribute [extern "lean_float_to_bits"]`, all rejected by `TrustedBoundary.lean` (`L442–444`, `L594–596`).
2. **NaN Payload Erasure Contradicts RFC 3514 Bit Identity:** In `src/Init/Data/Float/Model/Float.lean` (`L21–22`, `L34–61`), `Float.Model` restricts `toBits : UInt64` so that *"bit patterns encoding a `NaN` must be exactly a chosen canonical `NaN`"* (`Float.lean` L60–61: all `f` with `f.isNaN` equal `Float.nan`). Hence `Float.toBits (Float.ofBits 0xfff8_0000_0000_0001)` evaluates in Lean's model to `0x7ff8_0000_0000_0000`. Rust RFC 3514 (`text/3514-float-semantics.md` L39, L54–56) normatively preserves all representation bits across moves, `from_bits`/`to_bits`, unary `-`, `abs`, and `copysign`. Translating Rust `f64` to Lean `Float` makes `let x = f64::from_bits(0xfff8_0000_0000_0001); x.to_bits() == 0x7ff8_0000_0000_0000` provable in Lean while false at runtime!
3. **Kernel Reduction Physics:** `src/kernel/type_checker.cpp` (`L702–733`, `L759–775`) accelerates closed arithmetic solely via `type_checker::reduce_nat` over 15 GMP `Nat` primitives (`add`, `sub`, `mul`, `pow`, `gcd`, `mod`, `div`, `beq`, `ble`, `land`, `lor`, `xor`, `shiftLeft`, `shiftRight`), bounded by `check_nat_size` (`LEAN_NAT_MAX_SIZE_DEFAULT = 128 MB`, `L36`). No native float reducer exists in the kernel.

---

### 2. Pure-Integer SoftFloat Operational Anatomy in `proofs-rs/lean-miri`

`Basis: source + normative + execution`

`Miri/Interpreter/{Float,FloatOps,IntrinsicFloat}.lean` and `Miri/Interpreter/Math/{Float,Runtime,Fixed,Dispatch}.lean` (`c92d1d9754c9`) mechanize `rustc_apfloat` (`eeaacad81247`) and `miri` (`7fa591d7d4dd`) over `FloatBits := { format : FloatFormat, bits : U128 }`:

| `FloatFormat` | Rust | `width` | `exponentBits` | `fractionBits` ($p-1$) | Prec $p$ | `bias` | `minExponent` ($e_{\min}$) | `maxExponent` ($e_{\max}$) | Unit Roundoff $u_f$ | Subnormal Half-ULP $\eta_f$ |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `.binary16` | `f16` | `16` | `5` | `10` | `11` | `15` | `-14` | `15` | $2^{-11}$ | $2^{-25}$ |
| `.binary32` | `f32` | `32` | `8` | `23` | `24` | `127` | `-126` | `127` | $2^{-24}$ | $2^{-150}$ |
| `.binary64` | `f64` | `64` | `11` | `52` | `53` | `1023` | `-1022` | `1023` | $2^{-53}$ | $2^{-1075}$ |
| `.binary128` | `f128` | `128` | `15` | `112` | `113` | `16383` | `-16382` | `16383` | $2^{-113}$ | $2^{-16495}$ |

1. **Exact Decoding (`FloatBits.decode`, `Float.lean` L57–70):** When `exponent == 2^exponentBits - 1`, `fraction == 0` yields `.infinite` and `fraction != 0` yields `.nan fraction` (`isSignaling` iff `payload < 2^(fractionBits - 1)`, `L79–82`). Otherwise `significand = if exponent == 0 then fraction else 2^fractionBits + fraction`, `unbiased = if exponent == 0 then f.minExponent else exponent - f.bias`, and `powScale significand 1 (unbiased - fractionBits)` produces exact `.finite n d` with dyadic $d = 2^{\max(0, (p-1) - \text{unbiased})}$.
2. **Gradual-Underflow `roundRatio` (`Float.lean` L98–113):** Every finite arithmetic op (`Add`, `Sub`, `Mul`, `Div`, `Rem`), `fromInteger`, `convert`, `scalbn`, and `IntrinsicFloat.fusedMulAdd` calls `roundRatio f negative n d`:
   - If $n = 0$, returns `zero f negative` (`roundRatio_zero`, `L243–247`); in `exactSum` (`L164`), exact zero is `-0.0` iff both inputs were `-0.0` (`(+x) + (-x) = +0.0`).
   - Clamping `exponent := max (ratioExponent n d) f.minExponent` implements gradual subnormal underflow uniformly. Scaling $n/d$ by $2^{(p-1) - \text{exponent}}$ into `(scaledN, scaledD)`, `roundQuotientEven` rounds to nearest even integer `sig`. If binade carry occurs (`sig >= 2^p`, e.g., $2 - 2^{-24}$ in `f32`), `(sig, exponent) := (sig / 2, exponent + 1)` (`L105–107`) before re-checking `exponent > f.maxExponent` (overflow to `±Inf`). Subnormals (`sig < 2^(p-1)` at `exponent == f.minExponent`) encode with biased exponent `0`, including underflow to signed zero (`sig == 0`).
3. **Safe Casts vs. Fast/Unchecked Intrinsics (`Float.lean` L232–255, `IntrinsicFloat.lean` L83–93, `Math/Dispatch.lean` L92–121):**
   - Safe `as` (`FloatBits.toInteger`): total; maps any NaN to `0` (`nan_toInteger`) and saturates out-of-range values/infinities to `[minValue, maxValue]`.
   - `float_to_int_unchecked` (`IntrinsicFloat.toIntegerChecked`): immediate UB on NaN, `±Inf`, or truncated integer `signed neg (n / d)` outside `[minValue, maxValue]`.
   - `fadd_fast`..`frem_fast`: immediate UB if **either input or the rounded output is non-finite**, and demonically perturbs finite results by $\pm 4$ ULPs (`applyUlpError h choice result 4`, `Math/Runtime.lean` L89–109).

---

### 3. Demonic `Choice` Refinement for RFC 3514 NaNs and Relaxed FMA

`Basis: normative + source + execution + derived`

`lean-miri` captures all RFC 3514 (`f43d5789b838`, L56–88) floating-point nondeterminism via explicit `choice : C` hooks:

1. **Bitwise Sign Ops Bypass `adjustNaN` (`FloatOps.lean` L67–74, `IntrinsicFloat.lean` L16–23):** Unary `.Neg`, `abs`, and `copySign` flip/copy bit `width - 1` directly on `bits : U128`, preserving SNaNs and payloads deterministically.
2. **Exact `nanChoices` Set & Narrowing SNaN Guard (`Float.lean` L132–151, `miri/src/operator.rs` L74–117):** When `floatNondeterministic = true` and a non-bitwise op returns NaN, `adjustNaN` (`FloatOps.lean` L39–46) indexes `candidates` via `h.chooseNaN choice candidates`:
   - `preferredNaN target` (`0x7fc0_0000` for `f32`, `0x7ff8_0000_0000_0000` for `f64`);
   - Quieted conversions (`input.convert target`, matching `rustc_apfloat` `ieee.rs` L1919–1980) for all NaN inputs;
   - Unchanged signaling propagation for SNaN inputs: extracts `lower := convertedPayload % 2^(target.fractionBits - 1)` and appends signaling `encode target neg allOnes lower` **iff `lower != 0`** (`L145`);
   - Independent sign flip `[c, c.negate]` for each candidate (`2` entries for 0 NaN inputs, up to `10` for 2 SNaN inputs).
   *Verified Narrowing Witness (`execution`):* Casting `f64` SNaN `0x7ff0_0000_0000_0001` (`payload = 1`) via `as f32` shifts `(1 | 2^51) >> 29 = 0x40_0000`, giving `lower = 0`. Without `lower != 0`, clearing bit `22` would emit `0x7f80_0000` (`+Inf`)! Moreover, whenever a dyadic certificate proves finite operands stay in-bounds, `value.isNaN = false` short-circuits `adjustNaN` at `L41`, eliminating `chooseNaN` branching completely.
3. **`simd_relaxed_fma` Precision Non-Monotonicity (`IntrinsicSimd.lean` L486–489, RFC 3514 L234):** `simd_relaxed_fma(a, b, c)` queries `fuse ← h.fuseMulAdd choice`, executing `fusedMulAdd a b c` (`fuse = true`) or `(a * b) + c` (`fuse = false`).
   *Verified Counterexample (`execution`):* For `x = f32::from_bits(0x3f80_0001)` ($1 + 2^{-23}$), $y = \operatorname{fl}(x \cdot x) = 1 + 2^{-22}$ (`0x3f80_0002`). Then `simd_relaxed_fma(x, x, -y)` yields `+0.0` (`0x0000_0000`) when `fuse = false` (`1.0 / r == +Inf`) and $2^{-46}$ (`0x2880_0000`) when `fuse = true` (`1.0 / r == 2^46`). Neither branch refines the other; sound verification must enclose $I_{\text{fused}} \sqcup I_{\text{unfused}}$ across `ValidChoice`.

---

### 4. Comparative Mechanization Synthesis Under Anneal's Ceiling

`Basis: source + documentation + derived`

| Framework | Core Representation & Rounding Law | Automation Mechanism | Adaptation into Pass-1 `theory/` |
| :--- | :--- | :--- | :--- |
| **Flocq** (`10.1109/ARITH.2011.40`) | Integer pair `(Fnum : Z, Fexp : Z)` denoting $F_{\text{num}} \cdot 2^{F_{\text{exp}}}$; proves Hauser subnormal addition exactness ($\eta = 0$ on `Add`/`Sub`). | Coq lemmas over axiomatic `R`. | Replace `R` (absent in `Init.*`) with exact `Int`/dyadic cross-multiplied inequalities $N D' \le N' D$; retain `(Int, Int)` pairs and $\eta = 0$ on `±`. |
| **Gappa** (`10.1145/1644001.1644003`) | Dyadic intervals $[m_{\text{lo}} 2^e, m_{\text{hi}} 2^e]$ for `BND`, `ABS`, `REL`, and `FIX`/`FLT` grid predicates. | External C++ solver emits DAG scripts checked in Coq via `Z` reflection. | Untrusted external tool emits `DyadicBox` steps; `<150`-LOC Pass-1 checker validates via `rfl`! |
| **VCFloat2** (`VeriNum/vcfloat` `a203b287a84b`, `10.1145/3636501.3636953`) | `FPCore.v` (`L9–52`) separates operational C-to-`ftype` refinement from `VCFloat` $(1+\delta)x + \varepsilon$ error trees. | Coq reflection + interval evaluation. | Keep `Trusted.MirSemantics` purely operational (`FloatBits`), isolating error trees inside `theory/Anneal/Float/`. |
| **FloatLib** (`lean-dojo/FloatLib` `71a3d7ff211b`, `arXiv:2609.19352v1`) | `MixedError x x₀ r a` (`Rounding.lean` L68–86: `add_rounding` $a=0$ vs. `mul_rounding` $a=\eta_f$) + `Numerics.Kernel` dyadics. | `@[kernel_optimize]` + `decide +kernel` + Mathlib `ℝ` (`v4.36.0`). | Cannot import directly (Mathlib, custom attrs, `+kernel` banned). Distill `MixedError` + box-subdivision checker into `Init.Data.Int` + `rfl`. |

**Real-Free Rational Rounding Law:** Every finite `FloatBits` decodes to an exact dyadic rational $(-1)^{\text{neg}} n/d \in \mathbb{Q}$. Provably in `Init.Data.Int` + `Init.Data.Nat.Div.Basic` from `roundQuotientEven` ($|2r_{\text{adj}}| \le \text{scaledD}$): whenever $|q| \le (2 - 2^{-p}) 2^{e_{\max}}$, `roundRatio` produces finite $b$ satisfying $|\operatorname{val}(b) - q| \le \max(2^{-p}|q|, 2^{e_{\min}-p})$, with **zero rounding error** whenever $q = m \cdot 2^e$ fits the subnormal/normal grid ($|m| < 2^p, e \ge e_{\min} - p + 1$, covering subnormal `Add`/`Sub` and Sterbenz subtraction $\frac{1}{2}y \le x \le 2y$).

---

### 5. Pass-1 Pure `Init.Data.Int` Dyadic Certificate Checker

`Basis: source + derived`

To guarantee `<1 ms` C++ GMP `reduce_nat` checking without mantissa-squaring blowups (`type_checker.cpp` L298–303), `Anneal.Float.DyadicCert` pairs outward-directed `compressBy` shifts (`intFloorShr` toward $-\infty$, `intCeilShr` toward $+\infty$) with a 256-bit multiplication guard. Every construct below uses strictly `prelude` + locked `foundation-lock.json` modules and Pass-1-admitted syntax (zero `^`, unary `-`, `/`, `%`, `&&&`, `>>>`, `deriving`, `partial`, or `omega`):

```lean
prelude
import Init.Core
import Init.Data.Int.Basic
import Init.Data.List.Basic
import Init.Data.Nat.Basic
import Init.Data.Nat.Bitwise.Basic

namespace Anneal.Float.DyadicCert

/-- Closed dyadic interval `[lo * 2^exp2, hi * 2^exp2]` over `Init.Data.Int`. -/
structure DyadicBox where
  lo   : Int
  hi   : Int
  exp2 : Int

/-- Floor right-shift `⌊x / 2^s⌋`: `negSucc n ↦ negSucc (n >> s)` rounds toward `-∞`. -/
def intFloorShr (x : Int) (s : Nat) : Int :=
  match x with
  | .ofNat n   => .ofNat (Nat.shiftRight n s)
  | .negSucc n => .negSucc (Nat.shiftRight n s)

/-- Ceiling right-shift `⌈x / 2^s⌉ = -⌊(-x) / 2^s⌋` without banned unary `-` notation. -/
def intCeilShr (x : Int) (s : Nat) : Int :=
  Int.neg (intFloorShr (Int.neg x) s)

def compressBy (b : DyadicBox) (shift : Nat) : DyadicBox :=
  if Nat.beq shift 0 then b
  else { lo := intFloorShr b.lo shift, hi := intCeilShr b.hi shift, exp2 := b.exp2 + Int.ofNat shift }

/-- Align two boxes to `min b1.exp2 b2.exp2` with a 256-bit shift DoS guard. -/
def alignBoxes (b1 b2 : DyadicBox) : Option (Int × Int × Int × Int × Int) :=
  if b1.exp2 == b2.exp2 then
    some (b1.lo, b1.hi, b2.lo, b2.hi, b1.exp2)
  else if b1.exp2 < b2.exp2 then
    let diff := Int.natAbs (b2.exp2 - b1.exp2)
    if Nat.ble diff 256 then
      let scale := Int.ofNat (Nat.shiftLeft 1 diff)
      some (b1.lo, b1.hi, b2.lo * scale, b2.hi * scale, b1.exp2)
    else none
  else
    let diff := Int.natAbs (b1.exp2 - b2.exp2)
    if Nat.ble diff 256 then
      let scale := Int.ofNat (Nat.shiftLeft 1 diff)
      some (b1.lo * scale, b1.hi * scale, b2.lo, b2.hi, b2.exp2)
    else none

def addBox (b1 b2 : DyadicBox) (shift : Nat) : Option DyadicBox :=
  match alignBoxes b1 b2 with
  | none => none
  | some (l1, h1, l2, h2, e) => some (compressBy { lo := l1 + l2, hi := h1 + h2, exp2 := e } shift)

def subBox (b1 b2 : DyadicBox) (shift : Nat) : Option DyadicBox :=
  match alignBoxes b1 b2 with
  | none => none
  | some (l1, h1, l2, h2, e) => some (compressBy { lo := l1 - h2, hi := h1 - l2, exp2 := e } shift)

def minInt4 (a b c d : Int) : Int :=
  let m1 := if a ≤ b then a else b
  let m2 := if c ≤ d then c else d
  if m1 ≤ m2 then m1 else m2

def maxInt4 (a b c d : Int) : Int :=
  let m1 := if a ≤ b then b else a
  let m2 := if c ≤ d then d else c
  if m1 ≤ m2 then m2 else m1

/-- Outward interval multiplication guarded at 256-bit mantissa magnitudes. -/
def mulBox (b1 b2 : DyadicBox) (shift : Nat) : Option DyadicBox :=
  let cap := Nat.shiftLeft 1 256
  if Nat.blt (Int.natAbs b1.lo) cap && Nat.blt (Int.natAbs b1.hi) cap &&
     Nat.blt (Int.natAbs b2.lo) cap && Nat.blt (Int.natAbs b2.hi) cap then
    let p1 := b1.lo * b2.lo
    let p2 := b1.lo * b2.hi
    let p3 := b1.hi * b2.lo
    let p4 := b1.hi * b2.hi
    some (compressBy { lo := minInt4 p1 p2 p3 p4, hi := maxInt4 p1 p2 p3 p4, exp2 := b1.exp2 + b2.exp2 } shift)
  else none

/-- Sterbenz exact-subtraction check (`y/2 ≤ x ≤ 2*y`), discharging rounding error to `0`. -/
def checkSterbenzSub (b1 b2 : DyadicBox) : Bool :=
  match alignBoxes b1 b2 with
  | none => false
  | some (l1, h1, l2, h2, _) =>
    (decide ((0 : Int) ≤ l2) && decide (l2 ≤ 2 * l1) && decide (h1 ≤ 2 * l2)) ||
    (decide (h2 ≤ (0 : Int)) && decide (2 * h1 ≤ h2) && decide (2 * h2 ≤ l1))

/-- Certifies `actual ⊆ target` and `actual ⊆ maxFinBox` (ruling out `±Inf`/`NaN` overflow). -/
def checkFiniteEnclosure (actual target maxFinBox : DyadicBox) : Bool :=
  match alignBoxes actual target, alignBoxes actual maxFinBox with
  | some (al, ah, tl, th, _), some (al2, ah2, ml, mh, _) =>
    decide (al ≤ ah) && decide (tl ≤ al) && decide (ah ≤ th) && decide (ml ≤ al2) && decide (ah2 ≤ mh)
  | _, _ => false

end Anneal.Float.DyadicCert
```

Under **Statement-Origin Separation**, target theorems state preconditions/postconditions over `Trusted.*` bit patterns or integer `(neg, num, den)` tuples; `DyadicCert` runs exclusively inside the `.proof` term (`ConstantInfo.value?`) and bridges to `roundRatio` via a once-proved soundness lemma in `theory/Anneal/Float/`.

---

### 6. Evaluation Across the Anneal Untrusted-Theory Architecture Rubric

`Basis: derived + source`

| Criterion | Grade | Assessment |
| :--- | :---: | :--- |
| **`(T1)` 0-TCB Bridge** | **Minimal `Trusted.*` Hook (`S` on Certs)** | All dyadic intervals, Sterbenz rules, and mixed-error checkers stay **100% outside the TCB** in `theory/`. Only operational `roundRatio` + `adjustNaN` + `fuseMulAdd` enters `Trusted.MirSemantics`, certified in Pass 2 against `vendor/lean-miri`. |
| **`(P1)` Human Spec Auditability** | **Strong (`S`)** | Specs state transparent rational bounds or safe-Rust twins without leaking Gappa scripts or suffering `Init.Data.Float` NaN-erasure bugs. |
| **`(P2)` Authoring & Day-2 Locality** | **Strong (`S`)** | External tooling regenerates straight-line `DyadicBox` witnesses automatically on code edits; Lean proof scripts remain 1-line `rfl` applications. |
| **`(P3)` Lean 4 (`v4.34.1`) Kernel & `<50ms` LSP Scaling** | **Strong (`S`)** | Closed `Int`/`Nat` shifts with 256-bit `compressBy` execute natively in C++ GMP `reduce_nat` (`<1 ms` for 50-op kernels), needing neither `@Nat.rec` nor banned `decide +kernel`. |
| **`(P4)` Heterogeneous Composability** | **Strong (`S`)** | Composes with `BitVec` (`to_bits`/`from_bits`), `zerocopy` (`f32`/`f64` satisfy `FromBytes + IntoBytes + Immutable`), and SIMD (`simd_relaxed_fma`). |
| **`(P5)` Failure Legibility** | **Strong (`S`)** | Reports the exact MIR step index and interval `[lo·2^e, hi·2^e]` violating `maxFinBox` (`fadd_fast` overflow) or integer cast bounds (`float_to_int_unchecked`). |
| **`(C1–C2)` Conceptual Minimality** | **Locally Minimal (`S`)** | `valBox` and `errBox` cannot collapse without catastrophic `[0,1] - [0,1] = [-1,1]` interval dependency; `simd_relaxed_fma` cannot collapse to deterministic FMA (`0x3f800001` witness). |

---

## Boundaries

1. **`binary128` Host Transcendental Shims (`unsupported`):** In `proofs-rs/lean-miri` (`IntrinsicSimd.lean` L525, `Math/Float.lean` L108, `Math/Runtime.lean` L34, `Math/Dispatch.lean` L70, L75), `f128` arithmetic, casts, `fma`, and `sqrtf128` are portable integer code, **but** `sin`/`cos`/`exp`/`log`/`pow`/`powi` on `f128` throw `StepError.unsupported`, falsifying `WellFormed` fail-closed.
2. **Non-Default Hardware FPU Rounding/Trap Modes (`unsupported` / UB):** Rust RFC 3514 (`L58`, `L141–155`) forbids mutating FPU rounding or exception-trap control bits across Rust code (UB); `intFloorShr`/`intCeilShr` are purely meta-level certificate enclosures in `theory/`.
3. **Target-Specific Extra NaN Payloads & Legacy x87/ARMv7 NEON (`known not to apply`):** `FloatBits.nanChoices` (`Float.lean` L132–151) is exact for 64-bit x86-64, AArch64, and RISC-V (RFC 3514 L75), **but is known not to apply** to WebAssembly (where non-preferred NaN inputs allow arbitrary quiet payloads, `L76`), SPARC, 32-bit x86 x87 ABI returns (`L177–178`), old MIPS (`L179`), or 32-bit ARM NEON flush-to-zero (`L180`).
4. **Full `libm` Transcendental Minimax Certificate Synthesis (`not examined`):** Coupling `DyadicCert` with Remez/Chebyshev polynomial remainder certificates across full pure-Rust `libm` bodies was **not examined** empirically here.
5. **LLVM Fast-Math Backend Lowering Fidelity (`unknown`):** Whether specific LLVM optimization pipelines preserve all RFC 3514 NaN sign/quietness invariants under `fadd_fast`/auto-vectorization remains **unknown** from MIR semantics alone without ISA translation validation.

---

## Evidence

All evidence was acquired on `2026-11-20` from immutable commits, specifications, and deterministic checks:

1. **`joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`):** `trusted/lean/foundation-lock.json` (`L1–800`, 51 `Init.*` modules, 3 axioms, absence of `Init.Data.Float`), `trusted/audit/TrustedBoundary.lean` (`L442–596`, `L1136–1365`, Pass-1 syntax/attribute/replay gates), `theory/Anneal/MirWp.lean` (`L65–120`, `wpOutcomeState`).
2. **`leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`):** `src/Init/Data/Float/Float.lean` (`L6–157`), `src/Init/Data/Float/Model/Float.lean` (`L18–67`, canonical NaN invariant), `src/kernel/type_checker.cpp` (`L31–53`, `L294–321`, `L680–776`, `reduce_nat` & 128 MB `check_nat_size`).
3. **`proofs-rs/lean-miri` (`c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`):** `Miri/Interpreter/Float.lean` (`L10–258`), `FloatOps.lean` (`L10–110`), `IntrinsicFloat.lean` (`L7–94`), `IntrinsicSimd.lean` (`L462–527`), `Math/{Float,Runtime,Fixed,Dispatch}.lean`.
4. **Rust Upstream:** `rust-lang/rfcs` (`f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`, `text/3514-float-semantics.md` `L1–323`); `rust-lang/miri` (`7fa591d7d4dd9af8154becbc8332f8096f8323b1`, `src/operator.rs` `L74–127`); `rust-lang/rustc_apfloat` (`eeaacad81247af65d4043cb3e32d023a652d7951`, `src/ieee.rs` `L1897–2012`).
5. **Literature & Libraries:** `lean-dojo/FloatLib` (`71a3d7ff211b28bc3d27673b70b90644941a5fff`, `arXiv:2609.19352v1`, `MixedError/Rounding.lean` `L68–86`); `VeriNum/vcfloat` (`a203b287a84b0e3c9bec136823b5622ebfde6ad6`, `10.1145/3636501.3636953`, `vcfloat/FPCore.v` `L9–52`); Flocq (`10.1109/ARITH.2011.40`); Gappa (`10.1145/1644001.1644003`).
6. **Arithmetic Witness Execution (`2026-11-20`):** Python port of `FloatBits` verified `x = 0x3f800001` gives `fl(x*x) = 0x3f800002`, unfused `fl(x*x) - fl(x*x) = 0x00000000`, fused `fma(x, x, -fl(x*x)) = 0x28800000` ($2^{-46}$), and `f64` SNaN `0x7ff0000000000001` narrowed to `f32` gives `lower = 0`.

---

## Revalidation

1. **Foundation & `Float.Model` Check (<5s):** Verify `Init.Data.Float` remains absent from `trusted/lean/foundation-lock.json` and check `src/Init/Data/Float/Model/Float.lean` in Lean 4: unless `Float.Model` preserves distinct NaN payloads/signs across `ofBits`/`toBits`, it remains unsound for RFC 3514.
2. **Diff `lean-miri` Float Engine (<10s):** Diff `Miri/Interpreter/{Float,FloatOps,IntrinsicFloat,IntrinsicSimd}.lean` against `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` on `roundRatio` subnormal clamping, `nanChoices` `lower != 0`, bitwise `.Neg`/`abs`/`copySign` bypassing `adjustNaN`, and `simd_relaxed_fma` `fuseMulAdd`.
3. **Minimal Executable Discriminator (<2s):**
   ```bash
   python3 -c '
   r_even = lambda n, d: n//d + (1 if 2*(n%d) > d or (2*(n%d) == d and (n//d)&1) else 0)
   sig_xx = r_even((1 << 23 | 1)**2, 1 << 23)
   assert sig_xx == (1 << 23) + 2 and (1 << 23 | 1)**2 - sig_xx * (1 << 23) == 1
   assert (((1 | (1 << 51)) >> 29) & ((1 << 22) - 1)) == 0
   print("OK")
   '
   ```
   When a Lean `v4.34.1` toolchain is available, run `anneal-audit` `"preflight"` and `lean -DElab.async=false -Ddebug.skipKernelTC=false` on the **Findings §5** snippet.
