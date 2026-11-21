# NaN-set semantics, refinement tiers, truncating float-to-integer conversion, open-interval range checks and saturation in a Lean toy model

## Summary

This package is a self-contained, Mathlib-free Lean 4 development of a **toy model** of binary floating-point arithmetic with payload-carrying NaNs. Its centre is a set-valued ("nondeterministic") semantics `S`: every arithmetic primitive whose IEEE result is NaN may return any NaN allowed by NaN rules of the shape documented in Rust RFC 3514 and the LLVM LangRef (the preferred NaN, quieting or unchanged propagation of an operand's payload, or a target-specific extra payload from a set `X`, each with either sign), and `min`/`max` may return either operand when the operands compare equal. Around `S` the package defines deterministic implementations ("tiers": site-independent, context-free choice functions `Tier f`), constant folding of closed subexpressions, a small expression language with value-level observations (`isNaN`, `==`, `<`) and bit-level observations (`signBit`, `toBits`), and float-to-integer conversions: truncation toward zero, unchecked conversions that are undefined outside a range, two range-check guards, and saturating conversions. It answers which tiers refine `S`, when the observations of a program are deterministic despite NaN nondeterminism, what the exact precondition of a truncating conversion is when stated on the floating-point input, which two-comparison guard is exact, and which clauses determine the saturating conversion.

The package contains 14 kernel-checked results: 3 theorems, 6 characterizations (statements with an `↔`) and 5 counterexample results; none is an impossibility result. Every general statement is proved for every format with exponent-field width `e ≥ 2` and precision `p ≥ 2`. Statements about a named concrete format (`F23` with `e = 2`, `p = 3`; `F32` with `e = 3`, `p = 2`; `F33` with `e = 3`, `p = 3`; binary32 `Fbin32` with `e = 8`, `p = 24`) are about that format, and the prose does not generalize them. 9 hypothesis-ledger entries are marked `tight`, each with a named, kernel-checked counterexample in which all other hypotheses hold and the conclusion fails; the class of each counterexample is recorded in its ledger, and `tight` means no more than that the hypothesis cannot be dropped within that class. No ledger entry is `harmless` or `unknown`. Every result has a kernel-checked non-vacuity witness (for a counterexample result the statement is itself an instance), and every counterexample result has a positive control. Three further theorems refute earlier candidate statements; they are listed under **Boundaries → Disproved candidate statements** and are not results of this package. The sentences below are the plain-language claims recorded in `results.json`, verbatim.

1. **`tier-refinement-iff-sound`** (characterization, T1). For every format, every extra-payload set `X` and every tier `τ` (a site-independent, context-free choice function `Tier f`): `τ` refines the set-valued semantics `S` bit-exactly on every expression and input (`RefinesS X τ`) iff every choice of `τ` lies in the corresponding set of `S` (`TierSound X τ`). The same equivalence holds with refinement stated on observations: on every program and input, the observation computed by `τ` is one that `S` allows iff `TierSound X τ` (`Prog.refinesS_iff_tierSound`). In particular, for every `ChoicePolicy` `pol` and every `X`, the policy tier `tierOf pol` refines `S` (`tierOf_refinesS`); the example tiers `tierCtfe` and `tierRunA` are policy tiers.
2. **`sound-tiers-disagree-under-bit-observation`** (counterexample, T1). In every format, for every extra-payload set `X` and every input `ρ`: the tiers `tierCtfe` and `tierRunA` both refine `S` (`RefinesS`), yet on the program `toBits (0.0 * +∞)` `tierCtfe` returns the bits of the positive preferred quiet NaN and `tierRunA` returns the bits of the negative preferred quiet NaN, and these differ. So refinement of `S` does not make two sound tiers agree on bit-level observations: there is a pair of sound tiers (`tierCtfe`, `tierRunA`) and a program (`toBits (0.0 * +∞)`) on which they disagree.
3. **`sound-tier-constant-folding-refines-spec`** (theorem, T1). For every format, extra-payload set `X`, input `ρ`, program `P` and observation `n`, and for every tier `τ` that is sound for the same `X` (`hτ : TierSound X τ`): if `S` allows `n` for the constant-folded program `P.fold τ`, then `S` allows `n` for `P`. Folding replaces every maximal closed subexpression (one without variables) by the literal that `τ` computes for it, also inside the branches of `selLt`. This holds in particular for `τ = tierCtfe`.
4. **`ctfe-folding-not-preserved-by-run-tier`** (counterexample, T1). In every format and for every input `ρ`: constant folding of the open program `toBits (copysign (var 0) (0.0 * +∞))` with `tierCtfe` keeps `var 0` and replaces the closed subexpression `0.0 * +∞` by the literal positive preferred quiet NaN, and on the folded program the run-time tier `tierRunA` computes a different observation than on the original program (the theorem states that the two `toBits` observations differ, not which bit differs; the reason is that `copysign` copies the sign of the folded positive preferred NaN, whereas `tierRunA` computes the negative preferred NaN for `0.0 * +∞`, `sound_tiers_disagree_on_bits`). By `sound-tier-constant-folding-refines-spec` the folded program refines the original under `S`; a check of this folding against the fixed run-time tier `tierRunA` instead of against `S` would reject it.
5. **`observation-determinism-nan-or-zero`** (theorem, T1). For every format, extra-payload set `X`, input `ρ` and program `P`: if, in every execution of `S` from `ρ`, every bit-level use in `P` that the execution reaches (the sign argument of `copysign`, and the argument of `signBit` or `toBits`; inside `selLt a b t e`, a branch counts only if some execution takes it) receives a value that is neither a NaN nor a zero (`hsafe : P.BitSafe X ρ V.isNaNOrZero`), then any two observations that `S` allows for `P` on `ρ` are equal. This covers the value-level observations `isNaN`, `==`, `<` and the bit-level observations `signBit`, `toBits`. Consequently, under the same hypothesis, any two tiers that are both sound for `X` compute the same observation of `P` on `ρ`.
6. **`observation-determinism-minmax-free`** (theorem, T1). For every format, extra-payload set `X`, input `ρ` and program `P`: if `P` contains no `min`/`max` (`hmm : P.MinMaxFree = true`) and, in every execution of `S` from `ρ`, every bit-level use in `P` that the execution reaches (inside `selLt`, a branch counts only if some execution takes it) receives a value that is not a NaN (`hsafe : P.BitSafe X ρ V.isNaN`), then any two observations that `S` allows for `P` on `ρ` are equal, for value-level and bit-level observations alike. Consequently, under the same hypotheses, any two tiers that are both sound for `X` compute the same observation of `P` on `ρ`.
7. **`min-zero-deterministic-up-to-eq-not-under-sign-test`** (counterexample, T1). In every format, for every extra-payload set and input: `S` allows exactly the observation `1` for `min(+0.0, -0.0) == +0.0`, but exactly the observations `0` and `1` for `signBit (min(+0.0, -0.0))`. The sound tiers `tierCtfe` and `tierRunA` compute `0` and `1` for the sign test, although no bit-level use in it receives a NaN.
8. **`copysign-of-nan-breaks-determinism`** (counterexample, T1). In every format, for every extra-payload set and input: the program `0.0 < copysign(1.0, 0.0 * +∞)` has no `min`/`max`, and every bit-level use in it receives a value that is not a zero. Yet the sound tiers `tierCtfe` and `tierRunA` compute `1` and `0`, so `S` allows two different observations, although the final observation is value-level.
9. **`trunc-unsigned-open-interval`** (characterization, T0). For every format, every width `W` and every finite `x` (`hx : x.isFinite = true`): `trunc x` (truncation toward zero, computed by floor division of the magnitude) lies in `[0, 2^W − 1]` iff `InOpenU W x`, that is, iff `−1 < x < 2^W` as an exact comparison (`InOpenU` also requires `x` to be finite). The bound `2^W − 1` is an integer in `Int`; it is at least `0`, so no truncated subtraction occurs.
10. **`trunc-signed-open-interval`** (characterization, T0). For every format, every `k` (signed width `k + 1`; `k = 0` is the 1-bit range `[−1, 0]`) and every finite `x` (`hx : x.isFinite = true`): `trunc x` (truncation toward zero, computed by floor division of the magnitude) lies in `[−2^k, 2^k − 1]` iff `InOpenS k x`, that is, iff `−2^k − 1 < x < 2^k` as an exact comparison (`InOpenS` also requires `x` to be finite).
11. **`unchecked-conversion-undefined-iff`** (characterization, T0). For every format, every width `W` and every value `x`: the unchecked unsigned conversion `cvtU W x` is undefined (`none`) iff `¬ InOpenU W x`, that is, iff `x` is NaN or infinite or `x` lies outside the open interval `(−1, 2^W)`. For every `k` (signed width `k + 1`) and every value `x`: `cvtS k x` is undefined iff `¬ InOpenS k x`, that is, iff `x` is NaN or infinite or outside `(−2^k − 1, 2^k)`. The degenerate widths are included: `cvtU 0 x` is defined exactly when `x` is finite and `−1 < x < 1`, and `cvtS 0 x` exactly when `x` is finite and `−2 < x < 1`.
12. **`two-comparison-range-check-exact`** (characterization, T1). For every format, every width `W` and every value `x`: with `c = twoPowRound f W` (the mathematical integer `2^W` rounded to the format with ties-to-even, overflowing to `+∞`), the guard `x > −1.0 && x < c` (`rangeCheckU c x`, IEEE quiet comparisons in the same format) holds iff the unchecked conversion `cvtU W x` is defined. When `TwoPowFits f W`, `c` is exactly `2^W` (`twoPowRound_of_fits`). Otherwise `c = +∞` (`twoPowRound_of_not_fits`), and the guard is still exact because every finite value is then below `2^W`. The guard needs no separate finiteness test: a NaN fails both comparisons, and `+∞` fails `x < c` also when `c = +∞`. At `W = 0` the guard is `x > −1.0 && x < 1.0`: `TwoPowFits f 0` holds in every format (`two_pow_qneg_le_maxUnits`, as `0 + qneg = qneg`).
13. **`max-as-float-guard-not-exact`** (counterexample, T1). The guard `x > −1.0 && x <= (2^W − 1 as float)` (`naiveCheckU W`; `2^W − 1` is natural-number subtraction, which does not truncate since `2^W ≥ 1`) is not exact for the unchecked unsigned conversion. Each of the following is proved:
    - In `F32` (precision 2) with `W = 3`, `7 as float` rounds up to `8`, so the guard accepts `x = 8.0`, for which `cvtU 3` is undefined.
    - At `(W, format) = (32, binary32)`, `(2^32 − 1) as float = 2^32`, so the guard accepts `x = 2^32`, for which `cvtU 32` is undefined.
    - At `(128, binary32)`, `(2^128 − 1) as float = +∞`, so the guard accepts `+∞`, for which `cvtU 128` is undefined.
    - At `(3, F23)`, where `W` equals the precision `3`, `7 as float` overflows `F23` (largest finite value `3.5`) to `+∞`, so the guard accepts `+∞`.
    - In `F33` with `W = 2`, `3 as float` is exactly `3.0` (`roundNat_F33_three_exact`), and the guard rejects `x = 3.5`, for which `cvtU 2` is defined.
    - In `F23`, for every width `W` there is a value `x` on which the guard disagrees with definedness of `cvtU W x` (`naiveCheckU_inexact_every_width_F23`).

    In each of the first five instances the exact guard of `two-comparison-range-check-exact` decides correctly (the `rangeCheckU` conjuncts of the same theorems).
14. **`saturating-conversion-saturates-and-agrees`** (characterization, T0). For every format, every width `W` and every value `x`: `satU W x` lies in `[0, 2^W − 1]`; it equals `t` whenever `cvtU W x = some t`; NaN gives `0`; `−∞` gives `0`; `+∞` gives `2^W − 1`; `x ≤ −1` gives `0`; and `x ≥ 2^W` gives `2^W − 1` (the last two antecedents are stated on `uval` and imply that `x` is finite, `isFinite_of_uval_bounds`). For every `k` (signed width `k + 1`) and every value `x`: `satS k x` lies in `[−2^k, 2^k − 1]`; it agrees with `cvtS k` where that is defined; NaN gives `0`; `−∞` gives `−2^k`; `+∞` gives `2^k − 1`; `x ≤ −2^k − 1` gives `−2^k`; and `x ≥ 2^k` gives `2^k − 1`. These seven conjuncts characterize the functions: for every `g : FP f → Int`, `g` satisfies them at every input iff `g = satU W` pointwise (`satU_spec_iff`), and likewise for `satS k` (`satS_spec_iff`). At `W = 0`, `satU 0` returns `0` on every input, including `+∞` (`satU_width_zero`).

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust, LLVM, WebAssembly, CompCert, IEEE 754 hardware, or Lean `v4.34.1`'s built-in `Float` and `Float32`, and no representation-equivalence proof to any of them is given. Every connection to a real system is a separate `derived (modeling bridge)` claim, made under **Findings → Modelling bridges** and in the `Basis (real systems)` line of each result. Every result has **non-claims**, listed first under **Boundaries**; read them before relying on a result.

## Applicability

### Model fidelity

All results are about the toy model in namespace `Toy.FloatTier`, defined in `lean/Toy/FloatTier/*.lean` and quoted under **Findings → Model definitions**. It is meant to capture the NaN semantics of IEEE 754 binary floating-point arithmetic as specified, in prose, by Rust RFC 3514 and the LLVM LangRef: an operation whose result is NaN may return one of several NaN bit patterns, and deterministic implementations (compile-time evaluators, interpreters, code generators) each fix one choice. It is also meant to capture float-to-integer conversion as documented for Rust (`to_int_unchecked`, saturating `as`), LLVM (`fptoui`/`fptosi`, `llvm.fptoui.sat`), WebAssembly (`trunc`, `trunc_sat`) and CompCert (`ZofB_range`).

What the model contains:

- Binary formats `Fmt` with exponent-field width `e ≥ 2` and precision `p ≥ 2`; round-to-nearest-ties-to-even arithmetic (`add`, `sub`, `mul`), comparisons and `min`/`max` on the NaN-collapsed values `FP f` (one NaN, no sign, quiet bit or payload), copied from a published package of the same library (see **Findings → Model definitions, 1.1**).
- Payload-carrying values `V f`: every NaN refined into its sign bit, quiet bit and payload as in the IEEE 754 interchange encoding (`qnan`, `snan`), with the bit encoding `V.bits` (injective, `V.bits_injective`).
- The set-valued primitives `primSet X p x y r` (`NaNChoice`, `arithSet`, `minSet`, `maxSet`), parameterized by a target-specific extra-payload set `X : Extra f`; the expression language `FExpr f` (literals, input variables, primitives, the bit-level `neg`, `abs`, `copysign`, and the value-level branch `selLt`) and programs `Prog f` with one final observation; the semantics `FExpr.evalS`, `Prog.runS` (every execution of `S`) and `FExpr.evalT`, `Prog.runT` (one tier).
- Tiers `Tier f`, their soundness `TierSound X τ`, bit-exact refinement `RefinesS X τ`, policy tiers `tierOf pol`, constant folding `FExpr.fold`, `Prog.fold`, and the bit-level-safety predicate `BitSafe`.
- Conversions on `FP f`: the exact scaled value `FP.uval`, `trunc` (truncation toward zero, computed by floor division of the magnitude), the open-interval predicates `InOpenU`, `InOpenS` (each also requiring `x.isFinite = true`), the unchecked conversions `cvtU`, `cvtS` (with `none` for undefined), the saturating conversions `satU`, `satS`, integer-to-float rounding `roundNat`, `twoPowRound`, and the guards `rangeCheckU`, `naiveCheckU`.

Known gaps (each is a difference from the real systems, not a result):

- One rounding mode (round-to-nearest-ties-to-even); no status flags, traps, alternative rounding modes or flush-to-zero.
- The primitives are `add`, `sub`, `mul`, `min`, `max`; with `neg`, `abs`, `copysign`, the comparisons and `selLt`. There is no division, `sqrt`, `mul_add`, remainder, total-order comparison, byte conversion, or float-to-float cast (whose payload truncation and extension rules are therefore not modelled).
- Tiers are site-independent and context-free: the same primitive on the same operands gets the same result at every occurrence. RFC 3514 L130 allows two evaluations of the same expression during compile-time evaluation to give different results; such evaluators are not tiers.
- Programs are expression trees: there is no sharing, `let`, memory, loop or concurrency, so the "stable bit pattern" property of a value used twice (RFC 3514 L85) is not modelled.
- `minSet`/`maxSet` follow the Rust documentation of `f32::min`/`f32::max`. Rust `f32::minimum`, LLVM `llvm.minimum` and LLVM `llvm.minnum` behave differently on signed zeros or signaling NaNs and are not modelled.
- The quiet-bit convention is `1` = quiet; targets with the opposite convention are not modelled. No operation of the toy distinguishes a signaling NaN from a quiet one.
- Conversions act on the NaN-collapsed view and on exact values. `none` stands for both undefined behaviour and a poison result. The IEEE 754 invalid-operation exception, the results that hardware conversion instructions return for out-of-range inputs, evaluation in a wider intermediate precision, and computing `2^W` in a fixed-width integer type are not modelled.

Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about Rust, LLVM, WebAssembly, CompCert or IEEE 754 implementations, and no representation-equivalence proof to any of them is given. Lean's built-in `Float` types are not used.

### Relationship of the subjects

The Lean toolchain listed in `REPORT.json` is the checker of every theorem. The other subjects are the specifications, documentation and prior art against which the definitions and the modelling bridges were compared: Rust RFC 3514, the Rust core library documentation and the Rust Reference, the LLVM LangRef, the WebAssembly specification, the CompCert sources, IEEE 754-2019, and three papers on mechanized floating-point arithmetic and on WebAssembly. None of them is formally connected to the model. The text of IEEE 754-2019 was not accessible; no clause of it is quoted or relied on. For the three papers the bibliographic records were checked; no statement of them is relied on.

### Lean version and project

- Toolchain `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`), core Lean and `Std` without Mathlib and without Lake dependencies (`lean/lakefile.toml` declares one library, `Toy`, and no `[[require]]`).
- Namespace `Toy.FloatTier`. Definitions: `Base.lean` and `Arith.lean` (copied base format and rounding lemmas), `NaNVal.lean` (payload-carrying values), `Sets.lean` (set-valued primitives and tiers), `Lang.lean` (expressions, observations, folding, `BitSafe`), `Cast.lean` (conversions), `Instances.lean` (concrete formats, literals and programs). Results: `Statements.lean` (refinement and folding), `Determinism.lean` (determinism of observations), `CastStatements.lean` (conversions). Supporting files: `Lemmas.lean`, `VLemmas.lean` (auxiliary lemmas), `Counterexamples.lean`, `Examples.lean`, `CastExamples.lean`, `CastCompanion.lean` (counterexamples, positive controls, non-vacuity witnesses, definition examples and companion instances).
- Outside the library target: `lean/checks/BoundedChecks.lean` holds the bounded `#eval` evaluations described under **Evidence** (evaluated, not proved), and `lean/RevalidationAudit.lean` prints the axioms of every recorded declaration (see **Revalidation**).

## Findings

Every Lean block below quotes the source verbatim with its `path:line` range relative to `lean/`; proofs are elided (`:= by …` or `:= …`). Paragraphs that explain a definition in words are prose, not Lean terms. Every theorem quoted below is kernel-checked (`Basis: execution (Lean kernel check)`). Sentences about Rust, LLVM, WebAssembly, CompCert or IEEE 754 are `derived (modeling bridge)` claims that compare the toy definitions with documented behaviour at the pinned sources quoted under **Findings → Modelling bridges**; they are not kernel-checked, and no program was run.

### Model definitions

#### 1.1 Base format (copied)

`Toy/FloatTier/Base.lean` and `Toy/FloatTier/Arith.lean` are verbatim copies, with only the namespace renamed from `Toy.Float` to `Toy.FloatTier`, of parts of the published float-laws package. `Base.lean` copies `lean/Toy/Float/Defs.lean` lines 29–242 and 303–344 (sha256 of the source file `cde6a65729768940710224a3aa69ed4e45c80a505d896ee091ce82af09d62564`). `Arith.lean` copies all proved lemmas of `lean/Toy/Float/Arith.lean`, lines 14–423 (sha256 `251fabd61223d15ee0b72525c4f97e889a7fa1a6051981cfa7d91b02a040eec1`). In this package `FP f` is the **NaN-collapsed view**: one NaN, with no sign, quiet bit or payload.

A format has exponent-field width `e ≥ 2` and precision `p ≥ 2`; binary32 is `e = 8`, `p = 24`. A finite value is an integer number of units `2^-qneg`, where `qneg = bias + p - 2`.

```lean
-- Toy/FloatTier/Base.lean:31-35
structure Fmt where
  e : Nat
  p : Nat
  two_le_e : 2 ≤ e
  two_le_p : 2 ≤ p
```

```lean
-- Toy/FloatTier/Base.lean:74-78
inductive FP (f : Fmt) where
  | nan : FP f
  | inf (neg : Bool) : FP f
  | fin (neg : Bool) (E : Fin f.expCount) (M : Fin f.fracCount) : FP f
  deriving DecidableEq, Repr
```

```lean
-- Toy/FloatTier/Base.lean:84-85
def unitsOf (f : Fmt) (E M : Nat) : Nat :=
  if E = 0 then M else (f.fracCount + M) * 2 ^ (E - 1)
```

```lean
-- Toy/FloatTier/Base.lean:204
def sval (neg : Bool) (u : Nat) : Int := if neg then -(u : Int) else (u : Int)
```

`round f neg m d` is round-to-nearest-ties-to-even of `±(m / 2^d)` units with overflow to `±∞`:

```lean
-- Toy/FloatTier/Base.lean:189-190
def round (f : Fmt) (neg : Bool) (m d : Nat) : FP f :=
  mkFin f neg (roundUnits f m d)
```

```lean
-- Toy/FloatTier/Base.lean:210-219
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
```

```lean
-- Toy/FloatTier/Base.lean:222
def sub (x y : FP f) : FP f := add x y.neg
```

```lean
-- Toy/FloatTier/Base.lean:227-235
def mul : FP f → FP f → FP f
  | .nan, _ => .nan
  | .inf _, .nan => .nan
  | .fin .., .nan => .nan
  | .inf s, .inf t => .inf (s != t)
  | .inf s, .fin t E M => if unitsOf f E.val M.val = 0 then .nan else .inf (s != t)
  | .fin s E M, .inf t => if unitsOf f E.val M.val = 0 then .nan else .inf (s != t)
  | .fin s E M, .fin t E' M' =>
    round f (s != t) (unitsOf f E.val M.val * unitsOf f E'.val M'.val) f.qneg
```

Comparisons use an integer key; `key (-0) = key (+0) = 0`. The copied file also defines `minLt`, `maxLt`, `totalKey`, `minimum` and `maximum` on `FP f` (quoted in **Findings → Other declarations cited by name**); they are not primitives of the expression language of **Findings → Model definitions, 1.5**, and no result here concerns them.

```lean
-- Toy/FloatTier/Base.lean:241-244
def key : FP f → Int
  | .nan => 0
  | .inf s => sval s (f.maxUnits + 1)
  | .fin s E M => sval s (unitsOf f E.val M.val)
```

```lean
-- Toy/FloatTier/Base.lean:247
def lt (x y : FP f) : Bool := !x.isNaN && !y.isNaN && decide (key x < key y)
```

```lean
-- Toy/FloatTier/Base.lean:249
def le (x y : FP f) : Bool := !x.isNaN && !y.isNaN && decide (key x ≤ key y)
```

```lean
-- Toy/FloatTier/Base.lean:253
def feq (x y : FP f) : Bool := !x.isNaN && !y.isNaN && decide (key x = key y)
```

```lean
-- Toy/FloatTier/Base.lean:273
def zeroBlind (x : FP f) : FP f := if x.isZero then posZero f else x
```

```lean
-- Toy/FloatTier/Base.lean:276
def EqNsz (x y : FP f) : Prop := zeroBlind x = zeroBlind y
```

#### 1.2 Payload-carrying values

```lean
-- Toy/FloatTier/NaNVal.lean:30
def Fmt.payCount (f : Fmt) : Nat := 2 ^ (f.p - 2)
```

```lean
-- Toy/FloatTier/NaNVal.lean:39-44
inductive V (f : Fmt) where
  | qnan (neg : Bool) (pay : Fin f.payCount)
  | snan (neg : Bool) (k : Fin (f.payCount - 1))
  | inf (neg : Bool)
  | fin (neg : Bool) (E : Fin f.expCount) (M : Fin f.fracCount)
  deriving DecidableEq, Repr
```

Every term of `V f` is a valid encoding, and distinct terms have distinct bit patterns (`V.bits_injective`, **Findings → Auxiliary lemmas cited by name**). A signaling NaN `snan s k` has payload `k + 1`, because payload `0` with the quiet bit clear would encode an infinity. With `p = 2` there are no signaling NaNs (`ex_no_snan_p2`). The quiet bit is the top bit of the trailing significand with `1` meaning quiet; targets that use the opposite convention are not modelled (**Findings → Modelling bridges**).

```lean
-- Toy/FloatTier/NaNVal.lean:51-54
def isNaN : V f → Bool
  | .qnan .. => true
  | .snan .. => true
  | _ => false
```

```lean
-- Toy/FloatTier/NaNVal.lean:58-60
def isQuiet : V f → Bool
  | .qnan .. => true
  | _ => false
```

```lean
-- Toy/FloatTier/NaNVal.lean:64-67
def payload : V f → Nat
  | .qnan _ k => k.val
  | .snan _ k => k.val + 1
  | _ => 0
```

```lean
-- Toy/FloatTier/NaNVal.lean:77-81
def signBit : V f → Bool
  | .qnan s _ => s
  | .snan s _ => s
  | .inf s => s
  | .fin s _ _ => s
```

```lean
-- Toy/FloatTier/NaNVal.lean:84-89
def withSign (x : V f) (b : Bool) : V f :=
  match x with
  | .qnan _ k => .qnan b k
  | .snan _ k => .snan b k
  | .inf _ => .inf b
  | .fin _ E M => .fin b E M
```

```lean
-- Toy/FloatTier/NaNVal.lean:92
def neg (x : V f) : V f := x.withSign (!x.signBit)
```

```lean
-- Toy/FloatTier/NaNVal.lean:95
def abs (x : V f) : V f := x.withSign false
```

```lean
-- Toy/FloatTier/NaNVal.lean:98
def copysign (x y : V f) : V f := x.withSign y.signBit
```

```lean
-- Toy/FloatTier/NaNVal.lean:102-108
def bits : V f → Nat
  | .qnan s k => (if s then 2 ^ (f.e + f.p - 1) else 0) + (2 ^ f.e - 1) * 2 ^ (f.p - 1)
      + 2 ^ (f.p - 2) + k.val
  | .snan s k => (if s then 2 ^ (f.e + f.p - 1) else 0) + (2 ^ f.e - 1) * 2 ^ (f.p - 1)
      + (k.val + 1)
  | .inf s => (if s then 2 ^ (f.e + f.p - 1) else 0) + (2 ^ f.e - 1) * 2 ^ (f.p - 1)
  | .fin s E M => (if s then 2 ^ (f.e + f.p - 1) else 0) + E.val * 2 ^ (f.p - 1) + M.val
```

```lean
-- Toy/FloatTier/NaNVal.lean:111-115
def toFP : V f → FP f
  | .qnan .. => .nan
  | .snan .. => .nan
  | .inf s => .inf s
  | .fin s E M => .fin s E M
```

```lean
-- Toy/FloatTier/NaNVal.lean:119-122
def ofFP : FP f → V f
  | .nan => .qnan false ⟨0, f.payCount_pos⟩
  | .inf s => .inf s
  | .fin s E M => .fin s E M
```

```lean
-- Toy/FloatTier/NaNVal.lean:125
def isZero (x : V f) : Bool := x.toFP.isZero
```

```lean
-- Toy/FloatTier/NaNVal.lean:129
def isNaNOrZero (x : V f) : Bool := x.isNaN || x.isZero
```

```lean
-- Toy/FloatTier/NaNVal.lean:132
def prefNaN (f : Fmt) (s : Bool) : V f := .qnan s ⟨0, f.payCount_pos⟩
```

```lean
-- Toy/FloatTier/NaNVal.lean:136
def quieted (s : Bool) (z : V f) : V f := .qnan s ⟨z.payload, z.payload_lt⟩
```

```lean
-- Toy/FloatTier/NaNVal.lean:139
def zero (f : Fmt) (s : Bool) : V f := .fin s ⟨0, f.expCount_pos⟩ ⟨0, f.fracCount_pos⟩
```

```lean
-- Toy/FloatTier/NaNVal.lean:147
def ValEq (x y : V f) : Prop := EqNsz x.toFP y.toFP
```

```lean
-- Toy/FloatTier/NaNVal.lean:152-156
def FP.setSign (x : FP f) (b : Bool) : FP f :=
  match x with
  | .nan => .nan
  | .inf _ => .inf b
  | .fin _ E M => .fin b E M
```

#### 1.3 The set-valued semantics `S`

```lean
-- Toy/FloatTier/Sets.lean:38
abbrev Extra (f : Fmt) := V f → V f → Nat → Bool
```

```lean
-- Toy/FloatTier/Sets.lean:41
def noExtra : Extra f := fun _ _ _ => false
```

```lean
-- Toy/FloatTier/Sets.lean:49-54
def NaNChoice (X : Extra f) (x y r : V f) : Prop :=
  r.isNaN = true ∧
    ((r.isQuiet = true ∧ r.payload = 0) ∨
     (∃ z ∈ [x, y], z.isNaN = true ∧ r.isQuiet = true ∧ r.payload = z.payload) ∨
     (∃ z ∈ [x, y], z.isNaN = true ∧ r.isQuiet = z.isQuiet ∧ r.payload = z.payload) ∨
     (r.isQuiet = true ∧ X x y r.payload = true))
```

```lean
-- Toy/FloatTier/Sets.lean:60-62
inductive Prim where
  | add | sub | mul | min | max
  deriving DecidableEq, Repr
```

```lean
-- Toy/FloatTier/Sets.lean:66-67
def arithSet (X : Extra f) (c : FP f) (x y r : V f) : Prop :=
  if c.isNaN then NaNChoice X x y r else r = V.ofFP c
```

```lean
-- Toy/FloatTier/Sets.lean:70-76
def minSet (X : Extra f) (x y r : V f) : Prop :=
  if x.isNaN && y.isNaN then NaNChoice X x y r
  else if x.isNaN then r = y
  else if y.isNaN then r = x
  else if lt x.toFP y.toFP then r = x
  else if lt y.toFP x.toFP then r = y
  else r = x ∨ r = y
```

```lean
-- Toy/FloatTier/Sets.lean:79-85
def maxSet (X : Extra f) (x y r : V f) : Prop :=
  if x.isNaN && y.isNaN then NaNChoice X x y r
  else if x.isNaN then r = y
  else if y.isNaN then r = x
  else if lt y.toFP x.toFP then r = x
  else if lt x.toFP y.toFP then r = y
  else r = x ∨ r = y
```

```lean
-- Toy/FloatTier/Sets.lean:88-93
def primSet (X : Extra f) : Prim → V f → V f → V f → Prop
  | .add, x, y, r => arithSet X (add x.toFP y.toFP) x y r
  | .sub, x, y, r => arithSet X (sub x.toFP y.toFP) x y r
  | .mul, x, y, r => arithSet X (mul x.toFP y.toFP) x y r
  | .min, x, y, r => minSet X x y r
  | .max, x, y, r => maxSet X x y r
```

#### 1.4 Deterministic tiers

A tier is a choice function: it gives one result for each primitive and each pair of operands. It is **site-independent and context-free**: the same primitive applied to the same operands gets the same result at every occurrence in every program. `TierSound X τ` says that every choice lies in the corresponding set of `S`. `S` itself chooses independently at every node, so it allows observations that no tier produces (`exists_runS_not_realized_by_any_tier`, **Findings → Auxiliary lemmas cited by name**).

```lean
-- Toy/FloatTier/Sets.lean:100
abbrev Tier (f : Fmt) := Prim → V f → V f → V f
```

```lean
-- Toy/FloatTier/Sets.lean:104
def TierSound (X : Extra f) (τ : Tier f) : Prop := ∀ p x y, primSet X p x y (τ p x y)
```

```lean
-- Toy/FloatTier/Sets.lean:107-116
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
```

```lean
-- Toy/FloatTier/Sets.lean:119-122
def ChoicePolicy.nanResult (pol : ChoicePolicy) (x y : V f) : V f :=
  if pol.propagate && x.isNaN then V.quieted pol.nanNeg x
  else if pol.propagate && y.isNaN then V.quieted pol.nanNeg y
  else V.prefNaN f pol.nanNeg
```

```lean
-- Toy/FloatTier/Sets.lean:126-127
def ChoicePolicy.arith (pol : ChoicePolicy) (c : FP f) (x y : V f) : V f :=
  if c.isNaN then pol.nanResult x y else V.ofFP c
```

```lean
-- Toy/FloatTier/Sets.lean:130-147
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
```

```lean
-- Toy/FloatTier/Sets.lean:151
def ctfePolicy : ChoicePolicy := ⟨false, false, false⟩
```

```lean
-- Toy/FloatTier/Sets.lean:156
def runPolicyA : ChoicePolicy := ⟨true, true, true⟩
```

```lean
-- Toy/FloatTier/Sets.lean:159
def tierCtfe : Tier f := tierOf ctfePolicy
```

```lean
-- Toy/FloatTier/Sets.lean:162
def tierRunA : Tier f := tierOf runPolicyA
```

`tierCtfe` stands in for a fixed compile-time choice and `tierRunA` for a fixed run-time choice. Both are toy examples: neither is claimed to be the choice made by any real interpreter or target.

#### 1.5 Expressions, observations, folding, bit-level safety

```lean
-- Toy/FloatTier/Lang.lean:35-43
inductive FExpr (f : Fmt) where
  | lit (v : V f)
  | var (i : Nat)
  | prim (p : Prim) (a b : FExpr f)
  | neg (a : FExpr f)
  | abs (a : FExpr f)
  | copysign (a b : FExpr f)
  | selLt (a b t e : FExpr f)
  deriving Repr
```

```lean
-- Toy/FloatTier/Lang.lean:46-52
inductive Prog (f : Fmt) where
  | isNaN (a : FExpr f)
  | eq (a b : FExpr f)
  | lt (a b : FExpr f)
  | signBit (a : FExpr f)
  | toBits (a : FExpr f)
  deriving Repr
```

```lean
-- Toy/FloatTier/Lang.lean:58-66
def evalS (X : Extra f) (ρ : Nat → V f) : FExpr f → V f → Prop
  | .lit v, r => r = v
  | .var i, r => r = ρ i
  | .prim p a b, r => ∃ x y, a.evalS X ρ x ∧ b.evalS X ρ y ∧ primSet X p x y r
  | .neg a, r => ∃ x, a.evalS X ρ x ∧ r = x.neg
  | .abs a, r => ∃ x, a.evalS X ρ x ∧ r = x.abs
  | .copysign a b, r => ∃ x y, a.evalS X ρ x ∧ b.evalS X ρ y ∧ r = x.copysign y
  | .selLt a b t e, r => ∃ x y, a.evalS X ρ x ∧ b.evalS X ρ y ∧
      (if Toy.FloatTier.lt x.toFP y.toFP = true then t.evalS X ρ r else e.evalS X ρ r)
```

```lean
-- Toy/FloatTier/Lang.lean:69-78
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
```

```lean
-- Toy/FloatTier/Lang.lean:146-152
def runS (X : Extra f) (ρ : Nat → V f) : Prog f → Nat → Prop
  | .isNaN a, n => ∃ x, a.evalS X ρ x ∧ n = x.isNaN.toNat
  | .eq a b, n => ∃ x y, a.evalS X ρ x ∧ b.evalS X ρ y ∧ n = (feq x.toFP y.toFP).toNat
  | .lt a b, n => ∃ x y, a.evalS X ρ x ∧ b.evalS X ρ y ∧
      n = (Toy.FloatTier.lt x.toFP y.toFP).toNat
  | .signBit a, n => ∃ x, a.evalS X ρ x ∧ n = x.signBit.toNat
  | .toBits a, n => ∃ x, a.evalS X ρ x ∧ n = x.bits
```

```lean
-- Toy/FloatTier/Lang.lean:155-160
def runT (τ : Tier f) (ρ : Nat → V f) : Prog f → Nat
  | .isNaN a => (a.evalT τ ρ).isNaN.toNat
  | .eq a b => (feq (a.evalT τ ρ).toFP (b.evalT τ ρ).toFP).toNat
  | .lt a b => (Toy.FloatTier.lt (a.evalT τ ρ).toFP (b.evalT τ ρ).toFP).toNat
  | .signBit a => (a.evalT τ ρ).signBit.toNat
  | .toBits a => (a.evalT τ ρ).bits
```

`evalS` is relational. Every primitive node makes its own choice, and expressions are trees with no sharing, so two occurrences of the same subexpression are two separate executions. A NaN literal (`lit (qnan …)` or `lit (snan …)`) models a NaN built from bits.

```lean
-- Toy/FloatTier/Lang.lean:197-198
def RefinesS (X : Extra f) (τ : Tier f) : Prop :=
  ∀ (e : FExpr f) (ρ : Nat → V f), e.evalS X ρ (e.evalT τ ρ)
```

```lean
-- Toy/FloatTier/Lang.lean:81-88
def closed : FExpr f → Bool
  | .lit _ => true
  | .var _ => false
  | .prim _ a b => a.closed && b.closed
  | .neg a => a.closed
  | .abs a => a.closed
  | .copysign a b => a.closed && b.closed
  | .selLt a b t e => a.closed && b.closed && t.closed && e.closed
```

```lean
-- Toy/FloatTier/Lang.lean:93-102
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
```

```lean
-- Toy/FloatTier/Lang.lean:163-168
def fold (τ : Tier f) : Prog f → Prog f
  | .isNaN a => .isNaN (a.fold τ)
  | .eq a b => .eq (a.fold τ) (b.fold τ)
  | .lt a b => .lt (a.fold τ) (b.fold τ)
  | .signBit a => .signBit (a.fold τ)
  | .toBits a => .toBits (a.fold τ)
```

```lean
-- Toy/FloatTier/Lang.lean:109-121
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
```

```lean
-- Toy/FloatTier/Lang.lean:173-178
def BitSafe (X : Extra f) (ρ : Nat → V f) (bad : V f → Bool) : Prog f → Prop
  | .isNaN a => a.BitSafe X ρ bad
  | .eq a b => a.BitSafe X ρ bad ∧ b.BitSafe X ρ bad
  | .lt a b => a.BitSafe X ρ bad ∧ b.BitSafe X ρ bad
  | .signBit a => a.BitSafe X ρ bad ∧ ∀ y, a.evalS X ρ y → bad y = false
  | .toBits a => a.BitSafe X ρ bad ∧ ∀ y, a.evalS X ρ y → bad y = false
```

The bit-level uses are the sign argument of `copysign` and the arguments of `signBit` and `toBits`. `neg`, `abs` and the magnitude argument of `copysign` are bit-level operations too, but they respect value-level equality (`ValEq`), so `BitSafe` does not restrict them. `BitSafe` quantifies over **all `S`-executions** from the given input. A branch of `selLt a b t e` is constrained only if some `S`-execution from that input takes it: `t` is constrained when some results `x` of `a` and `y` of `b` satisfy `x < y`, and `e` when some results do not. So a bit-level use inside a branch that no execution takes is not constrained (`ex_bitSafe_guarded`, **Findings → Auxiliary lemmas cited by name**).

```lean
-- Toy/FloatTier/Lang.lean:124-131
def PrimsOk (ok : Prim → Bool) : FExpr f → Bool
  | .lit _ => true
  | .var _ => true
  | .prim p a b => ok p && a.PrimsOk ok && b.PrimsOk ok
  | .neg a => a.PrimsOk ok
  | .abs a => a.PrimsOk ok
  | .copysign a b => a.PrimsOk ok && b.PrimsOk ok
  | .selLt a b t e => a.PrimsOk ok && b.PrimsOk ok && t.PrimsOk ok && e.PrimsOk ok
```

```lean
-- Toy/FloatTier/Lang.lean:136-141
def Prim.isArith : Prim → Bool
  | .add => true
  | .sub => true
  | .mul => true
  | .min => false
  | .max => false
```

```lean
-- Toy/FloatTier/Lang.lean:181-186
def PrimsOk (ok : Prim → Bool) : Prog f → Bool
  | .isNaN a => a.PrimsOk ok
  | .eq a b => a.PrimsOk ok && b.PrimsOk ok
  | .lt a b => a.PrimsOk ok && b.PrimsOk ok
  | .signBit a => a.PrimsOk ok
  | .toBits a => a.PrimsOk ok
```

```lean
-- Toy/FloatTier/Lang.lean:189
def MinMaxFree (P : Prog f) : Bool := P.PrimsOk Prim.isArith
```

#### 1.6 Float-to-integer conversion

```lean
-- Toy/FloatTier/Cast.lean:36
def FP.uval (x : FP f) : Int := sval x.signBit x.units
```

```lean
-- Toy/FloatTier/Cast.lean:40
def trunc (x : FP f) : Int := sval x.signBit (x.units / 2 ^ f.qneg)
```

`trunc` is truncation toward zero, computed as **floor division** of the magnitude (in units) by `2^qneg`, with the sign applied afterwards. On NaN and infinities it returns the junk value `0` (`trunc_uval_of_not_finite`).

```lean
-- Toy/FloatTier/Cast.lean:44-46
def InOpenU (W : Nat) (x : FP f) : Prop :=
  x.isFinite = true ∧
    -((2 : Int) ^ f.qneg) < x.uval ∧ x.uval < (2 : Int) ^ W * 2 ^ f.qneg
```

```lean
-- Toy/FloatTier/Cast.lean:50-52
def InOpenS (k : Nat) (x : FP f) : Prop :=
  x.isFinite = true ∧
    -(((2 : Int) ^ k + 1) * 2 ^ f.qneg) < x.uval ∧ x.uval < (2 : Int) ^ k * 2 ^ f.qneg
```

The conversions act on the NaN-collapsed view `FP f`. The expression language of **Findings → Model definitions, 1.5** has no conversion construct, so the conversion results and the NaN-set results share the format and the arithmetic and nothing else. `InOpenU W x` and `InOpenS k x` include `x.isFinite = true`, so both are false on NaN, `+∞` and `-∞` (`not_inOpen_of_not_finite`, `ex_inOpenU_F33`, `ex_inOpenS_F33`). Signed targets are parametrized by `k` with width `k + 1`. This avoids truncated subtraction in `W - 1`; there is no signed width 0, and `k = 0` is the 1-bit signed range `[-1, 0]` with interval `(-2, 1)`. The unsigned width `W = 0` is allowed: range `[0, 0]`, interval `(-1, 1)`.

```lean
-- Toy/FloatTier/Cast.lean:59-60
def cvtU (W : Nat) (x : FP f) : Option Int :=
  if x.isFinite = true ∧ 0 ≤ trunc x ∧ trunc x ≤ 2 ^ W - 1 then some (trunc x) else none
```

```lean
-- Toy/FloatTier/Cast.lean:64-65
def cvtS (k : Nat) (x : FP f) : Option Int :=
  if x.isFinite = true ∧ -(2 ^ k) ≤ trunc x ∧ trunc x ≤ 2 ^ k - 1 then some (trunc x) else none
```

```lean
-- Toy/FloatTier/Cast.lean:69-73
def satU (W : Nat) (x : FP f) : Int :=
  match x with
  | .nan => 0
  | .inf s => if s then 0 else 2 ^ W - 1
  | .fin .. => max 0 (min (trunc x) (2 ^ W - 1))
```

```lean
-- Toy/FloatTier/Cast.lean:77-81
def satS (k : Nat) (x : FP f) : Int :=
  match x with
  | .nan => 0
  | .inf s => if s then -(2 ^ k) else 2 ^ k - 1
  | .fin .. => max (-(2 ^ k)) (min (trunc x) (2 ^ k - 1))
```

```lean
-- Toy/FloatTier/Cast.lean:85
def negOne (f : Fmt) : FP f := .fin true ⟨f.bias, f.bias_lt_expCount⟩ ⟨0, f.fracCount_pos⟩
```

```lean
-- Toy/FloatTier/Cast.lean:88
def twoPowRound (f : Fmt) (W : Nat) : FP f := round f false (2 ^ (W + f.qneg)) 0
```

```lean
-- Toy/FloatTier/Cast.lean:91
def roundNat (f : Fmt) (n : Nat) : FP f := round f false (n * 2 ^ f.qneg) 0
```

```lean
-- Toy/FloatTier/Cast.lean:96
def TwoPowFits (f : Fmt) (W : Nat) : Prop := 2 ^ (W + f.qneg) ≤ f.maxUnits
```

```lean
-- Toy/FloatTier/Cast.lean:101
def rangeCheckU (c x : FP f) : Bool := lt (negOne f) x && lt x c
```

```lean
-- Toy/FloatTier/Cast.lean:104
def naiveCheckU (W : Nat) (x : FP f) : Bool := lt (negOne f) x && le x (roundNat f (2 ^ W - 1))
```

```lean
-- Toy/FloatTier/Cast.lean:107
def Fbin32 : Fmt := ⟨8, 24, by decide, by decide⟩
```

#### 1.7 Concrete instances

```lean
-- Toy/FloatTier/Instances.lean:16
def F33 : Fmt := ⟨3, 3, by decide, by decide⟩
```

```lean
-- Toy/FloatTier/Instances.lean:19
def F32 : Fmt := ⟨3, 2, by decide, by decide⟩
```

```lean
-- Toy/FloatTier/Instances.lean:22
def F23 : Fmt := ⟨2, 3, by decide, by decide⟩
```

```lean
-- Toy/FloatTier/Instances.lean:26
def V.one (f : Fmt) : V f := .fin false ⟨f.bias, f.bias_lt_expCount⟩ ⟨0, f.fracCount_pos⟩
```

```lean
-- Toy/FloatTier/Statements.lean:122-123
def progBitsZeroMulInf (f : Fmt) : Prog f :=
  .toBits (.prim .mul (.lit (V.zero f false)) (.lit (.inf false)))
```

```lean
-- Toy/FloatTier/Instances.lean:45-46
def progIsNaNZeroMulInf (f : Fmt) : Prog f :=
  .isNaN (.prim .mul (.lit (V.zero f false)) (.lit (.inf false)))
```

```lean
-- Toy/FloatTier/Statements.lean:257-258
def progBitsCopysignVarNaN (f : Fmt) : Prog f :=
  .toBits (.copysign (.var 0) (.prim .mul (.lit (V.zero f false)) (.lit (.inf false))))
```

```lean
-- Toy/FloatTier/Instances.lean:49-50
def progBitsCopysignVarInfMulNegInf (f : Fmt) : Prog f :=
  .toBits (.copysign (.var 0) (.prim .mul (.lit (.inf false)) (.lit (.inf true))))
```

```lean
-- Toy/FloatTier/Instances.lean:54-56
def progCopysignNaN (f : Fmt) : Prog f :=
  .lt (.lit (V.zero f false))
    (.copysign (.lit (V.one f)) (.prim .mul (.lit (V.zero f false)) (.lit (.inf false))))
```

```lean
-- Toy/FloatTier/Instances.lean:59-60
def progMinZeroSign (f : Fmt) : Prog f :=
  .signBit (.prim .min (.lit (V.zero f false)) (.lit (V.zero f true)))
```

```lean
-- Toy/FloatTier/Instances.lean:63-64
def progMinZeroEq (f : Fmt) : Prog f :=
  .eq (.prim .min (.lit (V.zero f false)) (.lit (V.zero f true))) (.lit (V.zero f false))
```

```lean
-- Toy/FloatTier/Instances.lean:68-70
def progNaNBranchSign (f : Fmt) : Prog f :=
  .signBit (.selLt (.prim .mul (.lit (V.zero f false)) (.lit (.inf false))) (.lit (V.zero f false))
    (.lit (V.one f)) (.prim .mul (.lit (.inf false)) (.lit (.inf true))))
```

```lean
-- Toy/FloatTier/Instances.lean:75-79
def progGuardedDeadCopysign (f : Fmt) : Prog f :=
  .lt (.lit (V.zero f false))
    (.selLt (.prim .mul (.lit (V.zero f false)) (.lit (.inf false))) (.lit (V.zero f false))
      (.copysign (.lit (V.one f)) (.prim .mul (.lit (V.zero f false)) (.lit (.inf false))))
      (.lit (V.one f)))
```

```lean
-- Toy/FloatTier/Instances.lean:83-87
def progGuardedInputCopysign (f : Fmt) : Prog f :=
  .lt (.lit (V.zero f false))
    (.selLt (.lit (V.zero f false)) (.var 0)
      (.copysign (.lit (V.one f)) (.var 0))
      (.lit (V.one f)))
```

```lean
-- Toy/FloatTier/Instances.lean:91-92
def progSignBitAbsNaN (f : Fmt) : Prog f :=
  .signBit (.abs (.prim .mul (.lit (V.zero f false)) (.lit (.inf false))))
```

```lean
-- Toy/FloatTier/Instances.lean:96-97
def progBitsNaNLit (f : Fmt) : Prog f :=
  .toBits (.lit (V.prefNaN f true))
```

```lean
-- Toy/FloatTier/Instances.lean:101-102
def progIsNaNLitAdd (f : Fmt) : Prog f :=
  .isNaN (.prim .add (.lit (V.prefNaN f true)) (.lit (V.one f)))
```

```lean
-- Toy/FloatTier/Instances.lean:106-108
def progSelfEqCopysignNaN (f : Fmt) : Prog f :=
  .eq (.copysign (.lit (V.one f)) (.prim .mul (.lit (V.zero f false)) (.lit (.inf false))))
    (.copysign (.lit (V.one f)) (.prim .mul (.lit (V.zero f false)) (.lit (.inf false))))
```

```lean
-- Toy/FloatTier/Instances.lean:111
def tierBad : Tier f := fun _ _ _ => .inf false
```

```lean
-- Toy/FloatTier/Instances.lean:115-117
def tierExtraPay1 : Tier F23 := fun p x y =>
  if (tierCtfe p x y).isNaN then V.qnan (tierCtfe p x y).signBit ⟨1, by decide⟩
  else tierCtfe p x y
```

```lean
-- Toy/FloatTier/Instances.lean:120
def extraPay1 : Extra F23 := fun _ _ k => k == 1
```

`f33_3p5`, `f33_m3p5`, `f33_m0p5`, `f33_4` and `f33_5` are `3.5`, `-3.5`, `-0.5`, `4.0` and `5.0` in `F33`, given by their fields with the helper `FP.mk'` (quoted in **Findings → Other declarations cited by name**).

#### 1.8 Definition examples (all proved)

| Definition | Positive examples | Negative examples |
| :--- | :--- | :--- |
| `V`, `payload`, `bits` | `ex_snan_payload_F23` (a signaling NaN has payload 1); `ex_bits_prefNaN_binary32` (`0x7FC00000`); `ex_bits_nan_variants_binary32` (`0xFFC00000`, signaling `0x7F800001`) | `ex_no_snan_p2` (no signaling NaN when `p = 2`) |
| `NaNChoice` | `nanChoice_prefNaN` (preferred NaN, either sign, any operands); `ex_nanChoice_propagation_F23` (unchanged and quieting propagation of a signaling operand); `ex_nanChoice_extra_F23` (extra payload) | `ex_nanChoice_rejects_F23` (without NaN operands: no signaling NaN, no nonzero payload without extras, no non-NaN value) |
| `primSet` | `ex_primSet_allows_F23` (`min(+0,-0)` returns either zero; `0·∞` may return a negative NaN) | `ex_primSet_rejects_F23` (`min(1, NaN) ≠ NaN`; `∞ + -∞ ≠ +∞`; `1·1 ≠ -1`) |
| `TierSound` | `ex_tierSound_F23` (`tierCtfe`, `tierRunA`); `tierExtraPay1_sound_extra_not_noExtra` (`tierExtraPay1` for `extraPay1`) | `ex_tierSound_F23`, `not_tierSound_tierBad` (`tierBad`); `tierExtraPay1_sound_extra_not_noExtra` (`tierExtraPay1` for `noExtra`) |
| `ValEq` | `ex_valEq_F23` (`+0 ≈ -0`; any two NaNs) | `ex_valEq_F23` (`+∞ ≉ -∞`, `+0 ≉ 1`, NaN `≉ +∞`) |
| `BitSafe` | `progNaNBranchSign_nonvacuous`, `progMinZeroEq_nonvacuous`, `progIsNaNLitAdd_nonvacuous`; `ex_bitSafe_guarded` (a `copysign` of a NaN in a branch no execution takes; a `copysign` of the input guarded by `0.0 < var 0`, for every input) | `ex_bitSafe_rejects` (`toBits (0·∞)`); `bitSafe_not_necessary` (`signBit (abs (0·∞))`, `toBits` of a NaN literal) |
| `MinMaxFree` | `ex_minMaxFree` | `ex_minMaxFree` |
| `fold` | `runS_of_runS_fold_nonvacuous` (a closed program becomes a literal) | `ex_fold_keeps_var` (a variable is kept) |
| `trunc` | `ex_trunc_F33` (`3.5 ↦ 3`, `-3.5 ↦ -3`, `-0.5 ↦ 0`) | `ex_trunc_F33` (`-3.5 ↦ -3`, not the floor `-4`) |
| `InOpenU`, `InOpenS` | `ex_inOpenU_F33` (`3.5`, `-0.5` in `(-1, 4)`); `ex_inOpenS_F33` (`-3.5`, `3.5` in `(-5, 4)`) | `ex_inOpenU_F33` (`4.0`, `-1.0`, NaN, `+∞`, `-∞` not in `(-1, 4)`); `ex_inOpenS_F33` (`4.0`, NaN, `±∞` not in `(-5, 4)`; `-3.5` not in `(-3, 2)`) |
| `cvtU`, `cvtS` | `ex_cvtU_defined_F33` (`3.5 ↦ 3`, `-0.5 ↦ 0`), `ex_cvtS_F33` (`-3.5 ↦ -3`, `3.5 ↦ 3`) | `ex_cvtU_undefined_F33` (`4.0`, `-1.0`, NaN, `+∞`), `ex_cvtS_F33` (`4.0`) |
| `satU`, `satS` | `ex_satU_F33` (NaN ↦ 0, `+∞` ↦ 3, `-∞` ↦ 0, `-3.5` ↦ 0, `3.5 ↦ 3`), `ex_satS_F33` (NaN ↦ 0, `+∞` ↦ 3, `-∞` ↦ -4, `-3.5 ↦ -3`, `-5.0 ↦ -4`), `satU_width_zero` (`W = 0`: always `0`) | `ex_satU_F33` (`5.0 ↦ 3`, not wrapping to 1); `ex_satS_F33` (`5.0 ↦ 3`) |
| `negOne`, `twoPowRound`, `TwoPowFits` | `ex_negOne_F33`, `ex_twoPowRound_fits_F33`, `ex_twoPowFits_binary32_32` | `ex_twoPowRound_overflow_F33` (`2^4` overflows `F33`) |
| `rangeCheckU` | `ex_rangeCheckU_F33` (accepts `3.5`, `-0.5`) | `ex_rangeCheckU_F33` (rejects `4.0`, `-1.0`, NaN, `+∞`) |

### Results

There are 14 results. Every hypothesis ledger lists all explicit hypotheses of the quoted theorems. Universally quantified parameters (the format `f`, the extra-payload set `X`, the input `ρ`, the program `P`, widths, values, observations) are not hypotheses. "Tight" means that a fully proved theorem gives an instance satisfying all the other hypotheses in which the conclusion fails; the class of that instance is recorded. Results refer to each other by result ID. The non-claims of each result are listed under **Boundaries → Non-claims (per result)**, under the same number and ID.

#### 1. `tier-refinement-iff-sound` (characterization)

```lean
-- Toy/FloatTier/Statements.lean:39
theorem refinesS_iff_tierSound (X : Extra f) (τ : Tier f) : RefinesS X τ ↔ TierSound X τ := by …
```

```lean
-- Toy/FloatTier/Statements.lean:67-68
theorem Prog.refinesS_iff_tierSound (X : Extra f) (τ : Tier f) :
    (∀ (P : Prog f) (ρ : Nat → V f), P.runS X ρ (P.runT τ ρ)) ↔ TierSound X τ := by …
```

```lean
-- Toy/FloatTier/Statements.lean:118
theorem tierOf_refinesS (X : Extra f) (pol : ChoicePolicy) : RefinesS X (tierOf pol) := …
```

**Plain claim.** For every format, every extra-payload set `X` and every tier `τ` (a site-independent, context-free choice function `Tier f`): `τ` refines the set-valued semantics `S` bit-exactly on every expression and input (`RefinesS X τ`) iff every choice of `τ` lies in the corresponding set of `S` (`TierSound X τ`). The same equivalence holds with refinement stated on observations: on every program and input, the observation computed by `τ` is one that `S` allows iff `TierSound X τ` (`Prog.refinesS_iff_tierSound`). In particular, for every `ChoicePolicy` `pol` and every `X`, the policy tier `tierOf pol` refines `S` (`tierOf_refinesS`); the example tiers `tierCtfe` and `tierRunA` are policy tiers.

**Tier.** T1. RFC 3514 says in prose that compile-time evaluation makes "some fixed choices" inside the run-time NaN rules (**Findings → Modelling bridges**). The WebAssembly specification defines NaN results as sets and a deterministic profile that picks one element. The search found no mechanized statement of the refinement relation between such a set-valued semantics and its choice functions.

**Hypothesis ledger.** None. All three statements quantify over every `X`, `τ` and `pol`.

**Depth.** shallow (structural induction for ⇐; instantiation at `prim p (var 0) (var 1)` for ⇒, and for observations at `toBits (prim p (var 0) (var 1))` with injectivity of `V.bits`; for policy tiers, the case analysis `tierOf_sound`).

**Non-vacuity.** `refinesS_iff_tierSound_nonvacuous`: in `F23` with `noExtra`, `tierCtfe` satisfies both sides and `tierBad` satisfies neither.

**Non-claims.** Listed under **Boundaries → Non-claims (per result)**, heading "Non-claims of 1. `tier-refinement-iff-sound`"; read them before relying on this result.

**Prior art.** RFC 3514 (rust-lang/rfcs `text/3514-float-semantics.md` at `f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4`, L18–19 and L91–95): compile-time evaluation is "some deterministic function of the operation's inputs that satisfies the constraints placed on run-time floating point semantics". LLVM LangRef (llvmorg-21.1.0, `3623fe661ae35c6c80ac221f14d85be76aa870f1`, L3831–3848): the NaN rules. WebAssembly specification (`631890ee71035d9903fe5fd3a2b476bb82c76112`, `document/core/exec/numerics.rst` L1044–1054): set-valued NaN propagation and a deterministic profile. Related mechanizations of IEEE 754 arithmetic are listed in **Findings → Modelling bridges**.

**Design question.** Which deterministic, site-independent implementations (constant folders, interpreters, code generators that make one fixed choice per operation and operands) are correct for a nondeterministic NaN specification? Answer in the toy: exactly the tiers whose every choice lies in the specification's sets; in particular every fixed policy such as "positive preferred NaN".

**Basis.** execution (Lean kernel check), for every theorem quoted or cited by name in this result.

**Basis (real systems).** derived (modeling bridge). RFC 3514 (L18–19, L91–95) describes compile-time evaluation as a deterministic choice inside the run-time NaN rules, and the WebAssembly specification (`numerics.rst` L1044–1054) defines NaN results as sets with a deterministic profile that picks one element. `NaNChoice` and `primSet` model those rules, and `Tier f` models one fixed, site-independent, context-free choice. The correspondence rests on comparing the definitions with the quoted text; no implementation was examined, and evaluators whose choices depend on the occurrence (RFC 3514 L130) are outside it.

#### 2. `sound-tiers-disagree-under-bit-observation` (counterexample)

```lean
-- Toy/FloatTier/Statements.lean:153-157
theorem sound_tiers_disagree_on_bits (X : Extra f) (ρ : Nat → V f) :
    RefinesS X (tierCtfe (f := f)) ∧ RefinesS X (tierRunA (f := f)) ∧
      (progBitsZeroMulInf f).runT tierCtfe ρ = (V.prefNaN f false).bits ∧
      (progBitsZeroMulInf f).runT tierRunA ρ = (V.prefNaN f true).bits ∧
      (progBitsZeroMulInf f).runT tierCtfe ρ ≠ (progBitsZeroMulInf f).runT tierRunA ρ := by …
```

**Plain claim.** In every format, for every extra-payload set `X` and every input `ρ`: the tiers `tierCtfe` and `tierRunA` both refine `S` (`RefinesS`), yet on the program `toBits (0.0 * +∞)` `tierCtfe` returns the bits of the positive preferred quiet NaN and `tierRunA` returns the bits of the negative preferred quiet NaN, and these differ. So refinement of `S` does not make two sound tiers agree on bit-level observations: there is a pair of sound tiers (`tierCtfe`, `tierRunA`) and a program (`toBits (0.0 * +∞)`) on which they disagree.

**Tier.** T1. RFC 3514 states this possibility in prose (L18–19, L41–42, L95).

**Hypothesis ledger.** None (a concrete instance over every format, `X` and input).

**Depth.** definitional (computation of `0 * ∞ = NaN` and of two `bits` values).

**Non-vacuity.** The statement is itself an instance.

**Positive control.** `tiers_agree_on_isNaN_zero_mul_inf`: under the value-level observation `isNaN (0.0 * +∞)` the two tiers agree (both give `1`).

**Non-claims.** Listed under **Boundaries → Non-claims (per result)**, heading "Non-claims of 2. `sound-tiers-disagree-under-bit-observation`"; read them before relying on this result.

**Prior art.** RFC 3514 L18–19, L41–42, L91–95; Rust core `primitive_docs.rs` at `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, L1304–1307 ("The result does not have to match what happens when executing the same code at runtime").

**Design question.** May a verifier or optimizer assume that the NaN bit patterns computed by two correct implementations (for example constant evaluation and execution) agree? Not in a semantics with these NaN sets.

**Basis.** execution (Lean kernel check), for every theorem quoted or cited by name in this result.

**Basis (real systems).** derived (modeling bridge). RFC 3514 (L18–19, L41–42, L95) and the Rust core documentation (`primitive_docs.rs` L1304–1307) state in prose that the NaN bit pattern computed at compile time may differ from the one computed at run time. The theorem exhibits the same possibility between two toy tiers that both refine `S`; no compiler or target was run.

#### 3. `sound-tier-constant-folding-refines-spec` (theorem)

```lean
-- Toy/FloatTier/Statements.lean:239-240
theorem Prog.runS_of_runS_fold {X : Extra f} {τ : Tier f} (hτ : TierSound X τ)
    (P : Prog f) (ρ : Nat → V f) (n : Nat) : (P.fold τ).runS X ρ n → P.runS X ρ n := by …
```

**Plain claim.** For every format, extra-payload set `X`, input `ρ`, program `P` and observation `n`, and for every tier `τ` that is sound for the same `X` (`hτ : TierSound X τ`): if `S` allows `n` for the constant-folded program `P.fold τ`, then `S` allows `n` for `P`. Folding replaces every maximal closed subexpression (one without variables) by the literal that `τ` computes for it, also inside the branches of `selLt`. This holds in particular for `τ = tierCtfe`.

**Tier.** T1 (folklore that folding with any allowed choice refines a nondeterministic specification; RFC 3514 prose).

**Hypothesis ledger.**
- `hτ : TierSound X τ`. Purpose: the folded literal must be a result that `S` allows. **Tight**: `fold_unsound_tier_not_refinement` (witness class: every format, every `X`, every input; the program `isNaN (0.0 * +∞)` folded with `tierBad`, which always returns `+∞`, has the observation `0`, which `S` does not allow for the original program).

**Depth.** shallow (structural induction; a closed expression's tier result does not depend on the input, `FExpr.evalT_of_closed`).

**Non-vacuity.** `runS_of_runS_fold_nonvacuous`: `tierCtfe` is sound, folding changes `toBits (0.0 * +∞)` into `toBits (lit (prefNaN false))`, and the folded program has an `S`-observation.

**Non-claims.** Listed under **Boundaries → Non-claims (per result)**, heading "Non-claims of 3. `sound-tier-constant-folding-refines-spec`"; read them before relying on this result.

**Prior art.** RFC 3514 L91–95; Rust core `primitive_docs.rs` L1304–1307.

**Design question.** Is constant folding with an arbitrary fixed NaN choice a correct optimization? Yes, when correctness is judged against the set-valued specification with the same extra-payload set and the choice is allowed by it.

**Basis.** execution (Lean kernel check), for every theorem quoted or cited by name in this result.

**Basis (real systems).** derived (modeling bridge). RFC 3514 (L91–95) allows compile-time evaluation to make any choice that the run-time NaN rules allow. The theorem is the toy counterpart for folding closed subexpressions of expression trees, under the toy's assumptions (one rounding mode, no traps, no undefined behaviour, no shared bindings; RFC 3514 L58 and L143 state the corresponding Rust assumptions about the floating-point environment). No compiler was examined.

#### 4. `ctfe-folding-not-preserved-by-run-tier` (counterexample)

```lean
-- Toy/FloatTier/Statements.lean:267-271
theorem fold_tierCtfe_changes_tierRunA_bits (ρ : Nat → V f) :
    (progBitsCopysignVarNaN f).fold tierCtfe =
        .toBits (.copysign (.var 0) (.lit (V.prefNaN f false))) ∧
      ((progBitsCopysignVarNaN f).fold tierCtfe).runT tierRunA ρ ≠
        (progBitsCopysignVarNaN f).runT tierRunA ρ := by …
```

The program is `progBitsCopysignVarNaN` (**Findings → Model definitions, 1.7**).

**Plain claim.** In every format and for every input `ρ`: constant folding of the open program `toBits (copysign (var 0) (0.0 * +∞))` with `tierCtfe` keeps `var 0` and replaces the closed subexpression `0.0 * +∞` by the literal positive preferred quiet NaN, and on the folded program the run-time tier `tierRunA` computes a different observation than on the original program (the theorem states that the two `toBits` observations differ, not which bit differs; the reason is that `copysign` copies the sign of the folded positive preferred NaN, whereas `tierRunA` computes the negative preferred NaN for `0.0 * +∞`, `sound_tiers_disagree_on_bits`). By `sound-tier-constant-folding-refines-spec` the folded program refines the original under `S`; a check of this folding against the fixed run-time tier `tierRunA` instead of against `S` would reject it.

**Tier.** T1.

**Hypothesis ledger.** None (a concrete program over every format and input).

**Depth.** definitional.

**Non-vacuity.** The statement is itself an instance.

**Positive control.** `fold_tierCtfe_preserves_tierRunA_nan_free`: folding the NaN-free program `toBits (copysign (var 0) (+∞ * -∞))` with `tierCtfe` keeps the variable and does not change the observation computed by `tierRunA`, for every input.

**Non-claims.** Listed under **Boundaries → Non-claims (per result)**, heading "Non-claims of 4. `ctfe-folding-not-preserved-by-run-tier`"; read them before relying on this result.

**Prior art.** RFC 3514 L95 ("there is no guarantee that the choice made in const evaluation is consistent with the choice made at runtime").

**Design question.** Against which semantics must optimizations be justified? Against `S`, not against the observed behaviour of one fixed run-time tier.

**Basis.** execution (Lean kernel check), for every theorem quoted or cited by name in this result.

**Basis (real systems).** derived (modeling bridge). RFC 3514 (L95) states that the compile-time choice need not be consistent with the run-time choice. The theorem shows the toy consequence: a fold that refines `S` changes the observation computed by one fixed toy run-time tier. No compiler or target was examined.

#### 5. `observation-determinism-nan-or-zero` (theorem)

```lean
-- Toy/FloatTier/Determinism.lean:155-157
theorem Prog.runS_unique_of_bitSafe_nanOrZero (X : Extra f) (ρ : Nat → V f) (P : Prog f)
    (hsafe : P.BitSafe X ρ V.isNaNOrZero) :
    ∀ {n₁ n₂ : Nat}, P.runS X ρ n₁ → P.runS X ρ n₂ → n₁ = n₂ := …
```

```lean
-- Toy/FloatTier/Determinism.lean:163-165
theorem Prog.runT_eq_of_tierSound_of_bitSafe_nanOrZero (X : Extra f) {τ₁ τ₂ : Tier f}
    (h₁ : TierSound X τ₁) (h₂ : TierSound X τ₂) (ρ : Nat → V f) (P : Prog f)
    (hsafe : P.BitSafe X ρ V.isNaNOrZero) : P.runT τ₁ ρ = P.runT τ₂ ρ := …
```

**Plain claim.** For every format, extra-payload set `X`, input `ρ` and program `P`: if, in every execution of `S` from `ρ`, every bit-level use in `P` that the execution reaches (the sign argument of `copysign`, and the argument of `signBit` or `toBits`; inside `selLt a b t e`, a branch counts only if some execution takes it) receives a value that is neither a NaN nor a zero (`hsafe : P.BitSafe X ρ V.isNaNOrZero`), then any two observations that `S` allows for `P` on `ρ` are equal. This covers the value-level observations `isNaN`, `==`, `<` and the bit-level observations `signBit`, `toBits`. Consequently, under the same hypothesis, any two tiers that are both sound for `X` compute the same observation of `P` on `ρ`.

**Tier.** T1. RFC 3514 L33 states a related prose condition for the operations listed at its L50. The toy also contains `min`/`max`, whose documented choice between equal operands is why zeros are excluded here (`observation-determinism-minmax-free`, `min-zero-deterministic-up-to-eq-not-under-sign-test`).

**Hypothesis ledger.**
- `hsafe : P.BitSafe X ρ V.isNaNOrZero`, **NaN part**. Purpose: the sign and payload of a NaN are nondeterministic. **Tight**: `copysignNaN_breaks_determinism` (witness class: every format, every `X`, every input; the program `0.0 < copysign(1.0, 0.0 * +∞)` satisfies `BitSafe` for `V.isZero`, and `S` allows the two observations `1` and `0`).
- `hsafe`, **zero part**. Purpose: `min`/`max` may return either of `+0` and `-0`. **Tight**: `minZeroSign_breaks_determinism` (witness class: every format, every `X`, every input; the program `signBit (min(+0.0, -0.0))` satisfies `BitSafe` for `V.isNaN`, and `S` allows the observations `0` and `1`).
- `hsafe` as a whole is a sufficient condition, not a necessary one: `bitSafe_not_necessary` gives two programs, `signBit (abs (0.0 * +∞))` and `toBits` of a NaN literal, that violate it in every format and for which `S` allows exactly one observation.
- In the tier corollary, `h₁ : TierSound X τ₁` and `h₂ : TierSound X τ₂`. **Tight**: `unsound_tier_breaks_agreement` (witness class: every format, every `X`, every input; the program `isNaN (0.0 * +∞)`, which has no bit-level use; `tierBad` against `tierCtfe`).

**Depth.** shallow. It is one induction, but it rests on auxiliary lemmas: IEEE RNE `add`, `sub` and `mul` and the comparisons respect equality up to the sign of zero, and the comparison key is injective up to the sign of zero (**Findings → Auxiliary lemmas cited by name**).

**Non-vacuity.** `progNaNBranchSign_nonvacuous`: `signBit (if 0.0 * +∞ < 0.0 then 1.0 else +∞ * -∞)` produces a NaN, compares it, satisfies the hypothesis, and `S` allows exactly the observation `1`. `progMinZeroEq_nonvacuous`: `min(+0.0, -0.0) == +0.0` satisfies the hypothesis while its `min` node can return either zero, and `S` allows exactly the observation `1`. `ex_bitSafe_guarded`: `progGuardedDeadCopysign`, whose untaken branch applies `copysign` to a NaN, satisfies the hypothesis, and `S` allows exactly the observation `1`.

**Non-claims.** Listed under **Boundaries → Non-claims (per result)**, heading "Non-claims of 5. `observation-determinism-nan-or-zero`"; read them before relying on this result.

**Prior art.** RFC 3514 L33, L50, L56–57; Rust core `f32.rs` at `26bfbf28f5f79dff333ce5a232f131b496ec9cfe`, L1094–1104 (`min`: "either input may be returned non-deterministically").

**Design question.** When can a verifier treat float code as deterministic despite NaN nondeterminism? In the toy, a sufficient condition is that no bit-level use reached by some execution can receive a NaN or a zero.

**Basis.** execution (Lean kernel check), for every theorem quoted or cited by name in this result.

**Basis (real systems).** derived (modeling bridge). RFC 3514 (L33) states in prose that code that never applies the listed bit-level operations to a NaN and does not construct NaNs from bits cannot observe the nondeterminism. `BitSafe` is a toy counterpart for the operations of the toy language; zeros are also excluded because `minSet`/`maxSet` follow the Rust documentation of `f32::min` (`f32.rs` L1094–1104), which allows either operand when they compare equal. NaN literals, which model NaNs built from bits, are allowed in the toy because no toy operation distinguishes a signaling NaN.

#### 6. `observation-determinism-minmax-free` (theorem)

```lean
-- Toy/FloatTier/Determinism.lean:174-176
theorem Prog.runS_unique_of_minMaxFree_of_bitSafe_nan (X : Extra f) (ρ : Nat → V f)
    (P : Prog f) (hmm : P.MinMaxFree = true) (hsafe : P.BitSafe X ρ V.isNaN) :
    ∀ {n₁ n₂ : Nat}, P.runS X ρ n₁ → P.runS X ρ n₂ → n₁ = n₂ := …
```

```lean
-- Toy/FloatTier/Determinism.lean:180-183
theorem Prog.runT_eq_of_tierSound_of_minMaxFree_of_bitSafe_nan (X : Extra f)
    {τ₁ τ₂ : Tier f} (h₁ : TierSound X τ₁) (h₂ : TierSound X τ₂) (ρ : Nat → V f)
    (P : Prog f) (hmm : P.MinMaxFree = true) (hsafe : P.BitSafe X ρ V.isNaN) :
    P.runT τ₁ ρ = P.runT τ₂ ρ := …
```

**Plain claim.** For every format, extra-payload set `X`, input `ρ` and program `P`: if `P` contains no `min`/`max` (`hmm : P.MinMaxFree = true`) and, in every execution of `S` from `ρ`, every bit-level use in `P` that the execution reaches (inside `selLt`, a branch counts only if some execution takes it) receives a value that is not a NaN (`hsafe : P.BitSafe X ρ V.isNaN`), then any two observations that `S` allows for `P` on `ρ` are equal, for value-level and bit-level observations alike. Consequently, under the same hypotheses, any two tiers that are both sound for `X` compute the same observation of `P` on `ρ`.

**Tier.** T1 (the shape of RFC 3514 L33, made precise in the toy for `+`, `-`, `*`, unary `-`, `abs`, `copysign` and comparisons; NaN literals are allowed).

**Hypothesis ledger.**
- `hmm : P.MinMaxFree = true`. Purpose: `min`/`max` choose between `+0` and `-0`. **Tight**: `minZeroSign_breaks_determinism` (witness class: every format, every `X`, every input; `signBit (min(+0.0, -0.0))` satisfies `BitSafe` for `V.isNaN`).
- `hsafe : P.BitSafe X ρ V.isNaN`. Purpose: the sign and payload of a NaN are nondeterministic. **Tight**: `copysignNaN_breaks_determinism` (witness class: every format, every `X`, every input; `0.0 < copysign(1.0, 0.0 * +∞)` is `min`/`max`-free).
- `hsafe` is a sufficient condition, not a necessary one: the two programs of `bitSafe_not_necessary` are `min`/`max`-free, violate it, and have exactly one allowed observation each.
- In the tier corollary, `h₁`, `h₂`. **Tight**: `unsound_tier_breaks_agreement` (witness class: every format, every `X`, every input; the program `isNaN (0.0 * +∞)` is `min`/`max`-free and satisfies `BitSafe` for `V.isNaN`).

**Depth.** shallow (every arithmetic primitive factors through the NaN-collapsed view).

**Non-vacuity.** `progNaNBranchSign_nonvacuous` (`min`/`max`-free, a NaN produced and compared, a bit-level use of `-∞`, exactly the observation `1`); `progIsNaNLitAdd_nonvacuous` (a NaN literal used by `+`, exactly the observation `1`).

**Non-claims.** Listed under **Boundaries → Non-claims (per result)**, heading "Non-claims of 6. `observation-determinism-minmax-free`"; read them before relying on this result.

**Prior art.** RFC 3514 L33, L50.

**Design question.** Is "never apply a bit-level operation to a NaN" enough for determinism? In the toy, it is a sufficient condition for programs without `min`/`max`, and it is not sufficient with them.

**Basis.** execution (Lean kernel check), for every theorem quoted or cited by name in this result.

**Basis (real systems).** derived (modeling bridge). As for `observation-determinism-nan-or-zero`: RFC 3514 (L33, L50) states the prose condition for the operations it lists, and the toy statement covers the toy's `min`/`max`-free programs. No implementation was examined.

#### 7. `min-zero-deterministic-up-to-eq-not-under-sign-test` (counterexample)

```lean
-- Toy/FloatTier/Counterexamples.lean:293-294
theorem minZero_eq_and_signBit_runS (X : Extra f) (ρ : Nat → V f) (n : Nat) :
    ((progMinZeroEq f).runS X ρ n ↔ n = 1) ∧ ((progMinZeroSign f).runS X ρ n ↔ n = 0 ∨ n = 1) := by …
```

```lean
-- Toy/FloatTier/Counterexamples.lean:273-276
theorem minZeroSign_breaks_determinism (X : Extra f) (ρ : Nat → V f) :
    (progMinZeroSign f).BitSafe X ρ V.isNaN ∧ (progMinZeroSign f).MinMaxFree = false ∧
    (progMinZeroSign f).runT tierCtfe ρ = 0 ∧ (progMinZeroSign f).runT tierRunA ρ = 1 ∧
    ¬ (∀ n₁ n₂, (progMinZeroSign f).runS X ρ n₁ → (progMinZeroSign f).runS X ρ n₂ → n₁ = n₂) := by …
```

**Plain claim.** In every format, for every extra-payload set and input: `S` allows exactly the observation `1` for `min(+0.0, -0.0) == +0.0`, but exactly the observations `0` and `1` for `signBit (min(+0.0, -0.0))`. The sound tiers `tierCtfe` and `tierRunA` compute `0` and `1` for the sign test, although no bit-level use in it receives a NaN.

**Tier.** T1 (Rust core `f32::min` documentation states the nondeterminism).

**Hypothesis ledger.** None (concrete instances over every format, extra-payload set and input).

**Depth.** definitional.

**Non-vacuity.** The statements are instances.

**Positive control.** The `==` half of `minZero_eq_and_signBit_runS`, also stated as `progMinZeroEq_nonvacuous`: a value-level observation of the same `min` node is deterministic, as `observation-determinism-nan-or-zero` predicts.

**Non-claims.** Listed under **Boundaries → Non-claims (per result)**, heading "Non-claims of 7. `min-zero-deterministic-up-to-eq-not-under-sign-test`"; read them before relying on this result.

**Prior art.** Rust core `f32.rs` L1094–1104.

**Design question.** Must determinism arguments treat `min`/`max` specially? Yes, when zeros can reach bit-level observations.

**Basis.** execution (Lean kernel check), for every theorem quoted or cited by name in this result.

**Basis (real systems).** derived (modeling bridge). The Rust core documentation of `f32::min` (`f32.rs` L1094–1104) says that either input may be returned when the inputs compare equal; `minSet` models that documented choice. Rust `f32::minimum` and LLVM `llvm.minimum`, documented to order `-0.0` below `+0.0`, are not modelled.

#### 8. `copysign-of-nan-breaks-determinism` (counterexample)

```lean
-- Toy/FloatTier/Counterexamples.lean:242-245
theorem copysignNaN_breaks_determinism (X : Extra f) (ρ : Nat → V f) :
    (progCopysignNaN f).BitSafe X ρ V.isZero ∧ (progCopysignNaN f).MinMaxFree = true ∧
    (progCopysignNaN f).runT tierCtfe ρ = 1 ∧ (progCopysignNaN f).runT tierRunA ρ = 0 ∧
    ¬ (∀ n₁ n₂, (progCopysignNaN f).runS X ρ n₁ → (progCopysignNaN f).runS X ρ n₂ → n₁ = n₂) := by …
```

**Plain claim.** In every format, for every extra-payload set and input: the program `0.0 < copysign(1.0, 0.0 * +∞)` has no `min`/`max`, and every bit-level use in it receives a value that is not a zero. Yet the sound tiers `tierCtfe` and `tierRunA` compute `1` and `0`, so `S` allows two different observations, although the final observation is value-level.

**Tier.** T1 (RFC 3514 L33 lists `copysign` on a NaN among the operations that can observe nondeterminism).

**Hypothesis ledger.** None (a concrete instance over every format, extra-payload set and input).

**Depth.** definitional.

**Non-vacuity.** The statement is an instance.

**Positive control.** `tiers_agree_on_isNaN_zero_mul_inf` (the same NaN observed with `isNaN` gives one observation).

**Non-claims.** Listed under **Boundaries → Non-claims (per result)**, heading "Non-claims of 8. `copysign-of-nan-breaks-determinism`"; read them before relying on this result.

**Prior art.** RFC 3514 L33, L56–57; Rust core `primitive_docs.rs` L1256–1260.

**Design question.** Which bit-level operations leak NaN nondeterminism into value-level results? The sign argument of `copysign` does.

**Basis.** execution (Lean kernel check), for every theorem quoted or cited by name in this result.

**Basis (real systems).** derived (modeling bridge). RFC 3514 (L33) lists `copysign` on a NaN among the operations that can observe the nondeterminism, and the Rust core documentation (`primitive_docs.rs` L1256–1260) says that `copysign` copies the sign bit, also of a NaN; the toy `copysign` does the same. No implementation was examined.

#### 9. `trunc-unsigned-open-interval` (characterization)

```lean
-- Toy/FloatTier/CastStatements.lean:76-77
theorem trunc_mem_unsigned_range_iff (W : Nat) (x : FP f) (hx : x.isFinite = true) :
    (0 ≤ trunc x ∧ trunc x ≤ 2 ^ W - 1) ↔ InOpenU W x := by …
```

**Plain claim.** For every format, every width `W` and every finite `x` (`hx : x.isFinite = true`): `trunc x` (truncation toward zero, computed by floor division of the magnitude) lies in `[0, 2^W − 1]` iff `InOpenU W x`, that is, iff `−1 < x < 2^W` as an exact comparison (`InOpenU` also requires `x` to be finite). The bound `2^W − 1` is an integer in `Int`; it is at least `0`, so no truncated subtraction occurs.

**Tier.** T0. The WebAssembly specification states the definedness condition `−1 < trunc(±q) < 2^N` on the truncated value (**Findings → Modelling bridges**), the forward direction on the float input is mechanized in CompCert (`ZofB_range_nonneg`, `ZofB_range_pos`, `ZofB_range_neg`, `ZofB_range_zero`), and the equivalence on the float input is folklore.

**Hypothesis ledger.**
- `hx : x.isFinite = true`. Purpose: on NaN and `±∞`, `trunc` returns the junk value `0`. **Tight**: `trunc_mem_range_iff_fails_at_inf` (witness class: every format, every `W`; `x = +∞`, where `trunc (+∞) = 0` lies in `[0, 2^W − 1]` and `InOpenU W (+∞)` is false).

**Depth.** shallow (integer arithmetic with floor division).

**Non-vacuity.** `cast_results_nonvacuous` (in `F33`, `3.5` is finite and lies in the interval for `W = 2`; `4.0` is finite and does not); `ex_trunc_F33`; `ex_inOpenU_F33`.

**Non-claims.** Listed under **Boundaries → Non-claims (per result)**, heading "Non-claims of 9. `trunc-unsigned-open-interval`"; read them before relying on this result.

**Prior art.** CompCert `lib/IEEE754_extra.v` at `1670ae76afdb2546402898b6e9064d7229845d24`, L751–752, L758–759, L771–772, L778–779. WebAssembly specification `numerics.rst` L1842–1845 (`trunc_u`). Rust core `f32.rs` L1239–1245 (`to_int_unchecked` Safety). IEEE 754-2019 (DOI 10.1109/IEEESTD.2019.8766229): the text was not accessible and is not quoted.

**Design question.** What is the exact precondition of a truncating conversion to an unsigned type, stated on the floating-point input? `x` finite and in the open interval `(−1, 2^W)`.

**Basis.** execution (Lean kernel check), for every theorem quoted or cited by name in this result.

**Basis (real systems).** derived (modeling bridge). Rust `to_int_unchecked` (`f32.rs` L1239–1245), LLVM `fptoui` (LangRef L12293–12296), WebAssembly `trunc_u` (`numerics.rst` L1842–1845) and CompCert `ZofB_range` state the definedness condition on the truncated value or as integer bounds; the theorem restates it on the floating-point input, in the toy. No hardware conversion was examined.

#### 10. `trunc-signed-open-interval` (characterization)

```lean
-- Toy/FloatTier/CastStatements.lean:100-101
theorem trunc_mem_signed_range_iff (k : Nat) (x : FP f) (hx : x.isFinite = true) :
    (-(2 ^ k) ≤ trunc x ∧ trunc x ≤ 2 ^ k - 1) ↔ InOpenS k x := by …
```

**Plain claim.** For every format, every `k` (signed width `k + 1`; `k = 0` is the 1-bit range `[−1, 0]`) and every finite `x` (`hx : x.isFinite = true`): `trunc x` (truncation toward zero, computed by floor division of the magnitude) lies in `[−2^k, 2^k − 1]` iff `InOpenS k x`, that is, iff `−2^k − 1 < x < 2^k` as an exact comparison (`InOpenS` also requires `x` to be finite).

**Tier.** T0 (as `trunc-unsigned-open-interval`; WebAssembly `trunc_s`, `numerics.rst` L1865–1868).

**Hypothesis ledger.**
- `hx : x.isFinite = true`. Purpose: as in `trunc-unsigned-open-interval`. **Tight**: `trunc_mem_range_iff_fails_at_inf` (witness class: every format, every `k`; `x = +∞`, where `trunc (+∞) = 0` lies in `[−2^k, 2^k − 1]` and `InOpenS k (+∞)` is false).

**Depth.** shallow.

**Non-vacuity.** `cast_results_nonvacuous` (in `F33`, `-3.5` is finite and lies in the interval for `k = 2` and not for `k = 1`); `ex_cvtS_F33`; `ex_inOpenS_F33`.

**Non-claims.** Listed under **Boundaries → Non-claims (per result)**, heading "Non-claims of 10. `trunc-signed-open-interval`"; read them before relying on this result.

**Prior art.** As `trunc-unsigned-open-interval`.

**Design question.** As `trunc-unsigned-open-interval`, for signed targets.

**Basis.** execution (Lean kernel check), for every theorem quoted or cited by name in this result.

**Basis (real systems).** derived (modeling bridge). As for `trunc-unsigned-open-interval`, with LLVM `fptosi` (LangRef L12335–12338) and WebAssembly `trunc_s` (`numerics.rst` L1865–1868).

#### 11. `unchecked-conversion-undefined-iff` (characterization)

```lean
-- Toy/FloatTier/CastStatements.lean:125-126
theorem cvtU_eq_none_iff (W : Nat) (x : FP f) :
    cvtU W x = none ↔ ¬ InOpenU W x := by …
```

```lean
-- Toy/FloatTier/CastStatements.lean:140-141
theorem cvtS_eq_none_iff (k : Nat) (x : FP f) :
    cvtS k x = none ↔ ¬ InOpenS k x := by …
```

**Plain claim.** For every format, every width `W` and every value `x`: the unchecked unsigned conversion `cvtU W x` is undefined (`none`) iff `¬ InOpenU W x`, that is, iff `x` is NaN or infinite or `x` lies outside the open interval `(−1, 2^W)`. For every `k` (signed width `k + 1`) and every value `x`: `cvtS k x` is undefined iff `¬ InOpenS k x`, that is, iff `x` is NaN or infinite or outside `(−2^k − 1, 2^k)`. The degenerate widths are included: `cvtU 0 x` is defined exactly when `x` is finite and `−1 < x < 1`, and `cvtS 0 x` exactly when `x` is finite and `−2 < x < 1`.

**Tier.** T0 (Rust `to_int_unchecked` Safety, LLVM `fptoui`/`fptosi` poison, WebAssembly `trunc_u`/`trunc_s`, and CompCert `ZofB_range`, restated with `trunc-unsigned-open-interval` and `trunc-signed-open-interval`).

**Hypothesis ledger.** None.

**Depth.** shallow.

**Non-vacuity.** `cast_results_nonvacuous` (defined and undefined finite instances of `cvtU` and `cvtS`), `ex_cvtU_defined_F33`, `ex_cvtU_undefined_F33`, `ex_cvtS_F33`.

**Non-claims.** Listed under **Boundaries → Non-claims (per result)**, heading "Non-claims of 11. `unchecked-conversion-undefined-iff`"; read them before relying on this result.

**Prior art.** Rust core `f32.rs` L1239–1245; LLVM LangRef L12293–12296 and L12335–12338; CompCert `ZofB_correct` (L699–701) and `ZofB_range`, `ZofB_range_correct` (L840–851); WebAssembly `numerics.rst` L1842–1845 and L1865–1868.

**Design question.** Which inputs make an unchecked float-to-integer conversion undefined? Exactly NaN, infinities and values outside the open interval.

**Basis.** execution (Lean kernel check), for every theorem quoted or cited by name in this result.

**Basis (real systems).** derived (modeling bridge). `cvtU`/`cvtS` model the Safety section of Rust `to_int_unchecked` (`f32.rs` L1239–1245) and the poison results of LLVM `fptoui`/`fptosi` (LangRef L12293–12296, L12335–12338) by `none`, and the partial WebAssembly conversions `trunc_u`/`trunc_s` (`numerics.rst` L1842–1845, L1865–1868) have the same definedness intervals. The model does not distinguish undefined behaviour from poison. No implementation was examined.

#### 12. `two-comparison-range-check-exact` (characterization)

```lean
-- Toy/FloatTier/CastStatements.lean:187-188
theorem rangeCheckU_twoPowRound_iff (W : Nat) (x : FP f) :
    rangeCheckU (twoPowRound f W) x = true ↔ (cvtU W x).isSome = true := by …
```

**Plain claim.** For every format, every width `W` and every value `x`: with `c = twoPowRound f W` (the mathematical integer `2^W` rounded to the format with ties-to-even, overflowing to `+∞`), the guard `x > −1.0 && x < c` (`rangeCheckU c x`, IEEE quiet comparisons in the same format) holds iff the unchecked conversion `cvtU W x` is defined. When `TwoPowFits f W`, `c` is exactly `2^W` (`twoPowRound_of_fits`). Otherwise `c = +∞` (`twoPowRound_of_not_fits`), and the guard is still exact because every finite value is then below `2^W`. The guard needs no separate finiteness test: a NaN fails both comparisons, and `+∞` fails `x < c` also when `c = +∞`. At `W = 0` the guard is `x > −1.0 && x < 1.0`: `TwoPowFits f 0` holds in every format (`two_pow_qneg_le_maxUnits`, as `0 + qneg = qneg`).

**Tier.** T1. CompCert proves that, assuming `to_intu x = Some n` and `x < 2^31`, also `to_int x = Some n` (`to_intu_to_int_1`); it assumes definedness of the unsigned conversion rather than establishing it with a guard. The general exactness statement with both cases was not found mechanized.

**Hypothesis ledger.** None. Both cases (`2^W` fits or overflows) are covered by one statement.

**Depth.** shallow (rounding a power of two is exact or overflows, using the copied rounding lemmas; finite values are at most the largest finite value).

**Non-vacuity.** `rangeCheckU_twoPowRound_iff_nonvacuous` (in `F33`: `W = 2` with `c = 4.0`, and `W = 4` with `c = +∞`; binary32 with `W = 32`; accepted and rejected inputs in each case); `ex_rangeCheckU_F33`.

**Non-claims.** Listed under **Boundaries → Non-claims (per result)**, heading "Non-claims of 12. `two-comparison-range-check-exact`"; read them before relying on this result.

**Prior art.** CompCert `lib/Floats.v` at `1670ae76afdb2546402898b6e9064d7229845d24`, L536–540 (`to_intu_to_int_1`); `trunc-unsigned-open-interval`, `unchecked-conversion-undefined-iff`.

**Design question.** What guard makes an unchecked unsigned conversion safe without false rejections? `x > −1.0 && x < (2^W rounded to the format)`.

**Basis.** execution (Lean kernel check), for every theorem quoted or cited by name in this result.

**Basis (real systems).** derived (modeling bridge). CompCert `Floats.v` (L536–540, `to_intu_to_int_1`) assumes definedness of the unsigned conversion instead of establishing it with a guard. The guard of this result uses the toy's IEEE quiet comparisons in the same format and the toy's integer-to-float rounding, which follows the Rust Reference's description of integer-to-float `as` (`operator-expr.md` L606–616). No compiler's guard was examined.

#### 13. `max-as-float-guard-not-exact` (counterexample)

```lean
-- Toy/FloatTier/CastExamples.lean:118-122
theorem naiveCheckU_not_exact_small :
    (roundNat F32 7 = twoPowRound F32 3 ∧ naiveCheckU 3 (twoPowRound F32 3) = true ∧
      cvtU 3 (twoPowRound F32 3) = none ∧ rangeCheckU (twoPowRound F32 3) (twoPowRound F32 3) = false) ∧
    (naiveCheckU 2 f33_3p5 = false ∧ cvtU 2 f33_3p5 = some 3 ∧
      rangeCheckU (twoPowRound F33 2) f33_3p5 = true) := by …
```

```lean
-- Toy/FloatTier/CastExamples.lean:128-131
theorem naiveCheckU_accepts_two_pow_32_binary32 :
    roundNat Fbin32 (2 ^ 32 - 1) = twoPowRound Fbin32 32 ∧
    naiveCheckU 32 (twoPowRound Fbin32 32) = true ∧ cvtU 32 (twoPowRound Fbin32 32) = none ∧
    rangeCheckU (twoPowRound Fbin32 32) (twoPowRound Fbin32 32) = false := by …
```

```lean
-- Toy/FloatTier/CastExamples.lean:137-140
theorem naiveCheckU_accepts_inf_binary32_128 :
    roundNat Fbin32 (2 ^ 128 - 1) = .inf false ∧ naiveCheckU 128 (FP.inf false : FP Fbin32) = true ∧
    cvtU 128 (FP.inf false : FP Fbin32) = none ∧
    rangeCheckU (twoPowRound Fbin32 128) (FP.inf false : FP Fbin32) = false := by …
```

```lean
-- Toy/FloatTier/CastExamples.lean:146-149
theorem naiveCheckU_accepts_inf_F23_3 :
    roundNat F23 (2 ^ 3 - 1) = .inf false ∧ naiveCheckU 3 (FP.inf false : FP F23) = true ∧
    cvtU 3 (FP.inf false : FP F23) = none ∧
    rangeCheckU (twoPowRound F23 3) (FP.inf false : FP F23) = false := by …
```

```lean
-- Toy/FloatTier/CastExamples.lean:154-155
theorem naiveCheckU_inexact_every_width_F23 (W : Nat) :
    ∃ x : FP F23, naiveCheckU W x ≠ (cvtU W x).isSome := by …
```

```lean
-- Toy/FloatTier/CastCompanion.lean:17-19
theorem roundNat_F33_three_exact :
    roundNat F33 (2 ^ 2 - 1) = FP.mk' F33 false 4 2 ∧
      (roundNat F33 (2 ^ 2 - 1)).uval = 3 * 2 ^ F33.qneg := by …
```

**Plain claim.** The guard `x > −1.0 && x <= (2^W − 1 as float)` (`naiveCheckU W`; `2^W − 1` is natural-number subtraction, which does not truncate since `2^W ≥ 1`) is not exact for the unchecked unsigned conversion. Each of the following is proved:
- In `F32` (precision 2) with `W = 3`, `7 as float` rounds up to `8`, so the guard accepts `x = 8.0`, for which `cvtU 3` is undefined.
- At `(W, format) = (32, binary32)`, `(2^32 − 1) as float = 2^32`, so the guard accepts `x = 2^32`, for which `cvtU 32` is undefined.
- At `(128, binary32)`, `(2^128 − 1) as float = +∞`, so the guard accepts `+∞`, for which `cvtU 128` is undefined.
- At `(3, F23)`, where `W` equals the precision `3`, `7 as float` overflows `F23` (largest finite value `3.5`) to `+∞`, so the guard accepts `+∞`.
- In `F33` with `W = 2`, `3 as float` is exactly `3.0` (`roundNat_F33_three_exact`), and the guard rejects `x = 3.5`, for which `cvtU 2` is defined.
- In `F23`, for every width `W` there is a value `x` on which the guard disagrees with definedness of `cvtU W x` (`naiveCheckU_inexact_every_width_F23`).

In each of the first five instances the exact guard of `two-comparison-range-check-exact` decides correctly (the `rangeCheckU` conjuncts of the same theorems).

**Tier.** T1 (folklore pitfall; mechanized instances).

**Hypothesis ledger.** None (concrete instances, and one statement over every width in `F23`).

**Depth.** definitional for the instances (kernel evaluation by `decide`); shallow for `naiveCheckU_inexact_every_width_F23` (three small widths by evaluation, and overflow of `2^W − 1` for `W ≥ 3`).

**Non-vacuity.** The statements are instances.

**Positive control.** The `rangeCheckU` conjuncts of the first four theorems: the exact guard of `two-comparison-range-check-exact` at the same points.

**Non-claims.** Listed under **Boundaries → Non-claims (per result)**, heading "Non-claims of 13. `max-as-float-guard-not-exact`"; read them before relying on this result.

**Prior art.** `two-comparison-range-check-exact`; Rust Reference `src/expressions/operator-expr.md` at `5e6c977381e3cb5dcfdef97013bfae3317a181bf`, L606–616 (integer-to-float casts round to nearest with ties to even and overflow to infinity; its example `u128::MAX as f32 == f32::INFINITY`) and L591–595 (saturating `as`).

**Design question.** Is `x <= MAX as float` a safe guard for an unchecked conversion? No: there are formats and widths in which it accepts out-of-range values (including `+∞`), and formats and widths in which it rejects in-range ones.

**Basis.** execution (Lean kernel check), for every theorem quoted or cited by name in this result.

**Basis (real systems).** derived (modeling bridge). The Rust Reference (`operator-expr.md` L606–616) documents that integer-to-float `as` rounds to nearest with ties to even and overflows to infinity, as `roundNat` does; so the binary32 instances are the toy counterparts of `(2^32 − 1) as f32` and `(2^128 − 1) as f32`. No program was run.

#### 14. `saturating-conversion-saturates-and-agrees` (characterization)

```lean
-- Toy/FloatTier/CastStatements.lean:268-275
theorem satU_saturates_and_agrees (W : Nat) (x : FP f) :
    (0 ≤ satU W x ∧ satU W x ≤ 2 ^ W - 1) ∧
    (∀ t, cvtU W x = some t → satU W x = t) ∧
    (x = .nan → satU W x = 0) ∧
    (x = .inf true → satU W x = 0) ∧
    (x = .inf false → satU W x = 2 ^ W - 1) ∧
    (x.uval ≤ -((2 : Int) ^ f.qneg) → satU W x = 0) ∧
    ((2 : Int) ^ W * 2 ^ f.qneg ≤ x.uval → satU W x = 2 ^ W - 1) := by …
```

```lean
-- Toy/FloatTier/CastStatements.lean:347-354
theorem satS_saturates_and_agrees (k : Nat) (x : FP f) :
    (-(2 ^ k) ≤ satS k x ∧ satS k x ≤ 2 ^ k - 1) ∧
    (∀ t, cvtS k x = some t → satS k x = t) ∧
    (x = .nan → satS k x = 0) ∧
    (x = .inf true → satS k x = -(2 ^ k)) ∧
    (x = .inf false → satS k x = 2 ^ k - 1) ∧
    (x.uval ≤ -(((2 : Int) ^ k + 1) * 2 ^ f.qneg) → satS k x = -(2 ^ k)) ∧
    ((2 : Int) ^ k * 2 ^ f.qneg ≤ x.uval → satS k x = 2 ^ k - 1) := by …
```

```lean
-- Toy/FloatTier/CastStatements.lean:425-433
theorem satU_spec_iff (W : Nat) (g : FP f → Int) :
    (∀ x : FP f, (0 ≤ g x ∧ g x ≤ 2 ^ W - 1) ∧
      (∀ t, cvtU W x = some t → g x = t) ∧
      (x = .nan → g x = 0) ∧
      (x = .inf true → g x = 0) ∧
      (x = .inf false → g x = 2 ^ W - 1) ∧
      (x.uval ≤ -((2 : Int) ^ f.qneg) → g x = 0) ∧
      ((2 : Int) ^ W * 2 ^ f.qneg ≤ x.uval → g x = 2 ^ W - 1)) ↔
    ∀ x, g x = satU W x := by …
```

```lean
-- Toy/FloatTier/CastStatements.lean:466-474
theorem satS_spec_iff (k : Nat) (g : FP f → Int) :
    (∀ x : FP f, (-(2 ^ k) ≤ g x ∧ g x ≤ 2 ^ k - 1) ∧
      (∀ t, cvtS k x = some t → g x = t) ∧
      (x = .nan → g x = 0) ∧
      (x = .inf true → g x = -(2 ^ k)) ∧
      (x = .inf false → g x = 2 ^ k - 1) ∧
      (x.uval ≤ -(((2 : Int) ^ k + 1) * 2 ^ f.qneg) → g x = -(2 ^ k)) ∧
      ((2 : Int) ^ k * 2 ^ f.qneg ≤ x.uval → g x = 2 ^ k - 1)) ↔
    ∀ x, g x = satS k x := by …
```

**Plain claim.** For every format, every width `W` and every value `x`: `satU W x` lies in `[0, 2^W − 1]`; it equals `t` whenever `cvtU W x = some t`; NaN gives `0`; `−∞` gives `0`; `+∞` gives `2^W − 1`; `x ≤ −1` gives `0`; and `x ≥ 2^W` gives `2^W − 1` (the last two antecedents are stated on `uval` and imply that `x` is finite, `isFinite_of_uval_bounds`). For every `k` (signed width `k + 1`) and every value `x`: `satS k x` lies in `[−2^k, 2^k − 1]`; it agrees with `cvtS k` where that is defined; NaN gives `0`; `−∞` gives `−2^k`; `+∞` gives `2^k − 1`; `x ≤ −2^k − 1` gives `−2^k`; and `x ≥ 2^k` gives `2^k − 1`. These seven conjuncts characterize the functions: for every `g : FP f → Int`, `g` satisfies them at every input iff `g = satU W` pointwise (`satU_spec_iff`), and likewise for `satS k` (`satS_spec_iff`). At `W = 0`, `satU 0` returns `0` on every input, including `+∞` (`satU_width_zero`).

**Tier.** T0. The WebAssembly specification defines `trunc_sat_u` and `trunc_sat_s` by the same clauses (`numerics.rst` L1891–1894, L1910–1913), LLVM documents the same rules for `llvm.fptoui.sat` (L21046–21054), and the Rust Reference documents saturating `as` (L591–595); agreement with the unchecked conversion follows from the definitions.

**Hypothesis ledger.** None.

**Depth.** shallow.

**Non-vacuity.** No hypotheses; `ex_satU_F33`, `ex_satS_F33` and `satU_width_zero` evaluate the functions on NaN, both infinities, in-range and out-of-range values.

**Non-claims.** Listed under **Boundaries → Non-claims (per result)**, heading "Non-claims of 14. `saturating-conversion-saturates-and-agrees`"; read them before relying on this result.

**Prior art.** Rust Reference `src/expressions/operator-expr.md` at `5e6c977381e3cb5dcfdef97013bfae3317a181bf`, L591–595; WebAssembly `numerics.rst` L1891–1894 and L1910–1913; LLVM LangRef L21046–21054.

**Design question.** Can a saturating `as` replace a guarded unchecked conversion without changing results on the guarded domain? Yes in the toy, and the seven clauses above determine the saturating conversion uniquely.

**Basis.** execution (Lean kernel check), for every theorem quoted or cited by name in this result.

**Basis (real systems).** derived (modeling bridge). The Rust Reference's saturating `as` (`operator-expr.md` L591–595), the WebAssembly definitions of `trunc_sat_u`/`trunc_sat_s` (`numerics.rst` L1891–1894, L1910–1913) and LLVM `llvm.fptoui.sat` (LangRef L21046–21054) document the same clauses as `satU`/`satS`; the correspondence rests on comparing the clauses. No implementation was examined.

### Modelling bridges (`derived (modeling bridge)`, prose, not kernel-checked)

Basis: derived (modeling bridge), from the documentation and normative text quoted below at pinned revisions.

These paragraphs connect the toy definitions to documented behaviour of real systems. They are not kernel-checked, and no program was run. Model–system relation: none proved. The kernel-checked statements neither establish nor refute the corresponding claims about Rust, LLVM or IEEE 754 implementations.

- **NaN sets (`NaNChoice`, `arithSet`).** Modelled on RFC 3514's rules (rust-lang/rfcs `text/3514-float-semantics.md` at `f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4`, L63–83) and on the same rules in the LLVM LangRef (llvmorg-21.1.0, L3831–3848). The model keeps the four options (preferred, quieting propagation, unchanged propagation, target-specific extra payloads that may depend on the operands) and the nondeterministic sign. It omits the payload truncation and extension rules for float-to-float `as` casts, which are not modelled.
- **Bit-level operations.** `neg`, `abs` and `copysign` change only the sign bit, also on NaNs (RFC 3514 L56–57; Rust core `primitive_docs.rs` L1256–1260; LangRef L3826–3829).
- **Compile-time evaluation.** `tierCtfe` illustrates RFC 3514's statement that compile-time evaluation is "*some* deterministic function of the operation's inputs that satisfies the constraints placed on run-time floating point semantics" (L91–95). The specific policy is a toy example. RFC 3514 L130 also allows two evaluations of the same expression during compile-time evaluation to give different results; such an evaluator is not a site-independent tier (`tier-refinement-iff-sound`).
- **`min`/`max`.** `minSet` and `maxSet` follow the Rust core documentation of `f32::min`: a NaN operand is ignored, two NaNs give a NaN by the arithmetic rules, and equal operands may give either operand (`f32.rs` L1094–1104). The documentation also says that the signed-zero handling follows IEEE 754-2008 `minNum`, which was not consulted directly. Other documented operations differ and are not modelled: Rust `f32::minimum` treats `-0.0` as less than `+0.0` and is "fully deterministic for non-NaN inputs" (`f32.rs` L1150–1158); LLVM `llvm.minimum` returns the lesser argument with `-0.0` less than `+0.0` (LangRef L17190–17193); LLVM `llvm.minnum` returns a quiet NaN if either operand is a signaling NaN and warns that arithmetic feeding into it can produce inconsistent results (LangRef L17070–17078).
- **Truncating conversions.** `cvtU`/`cvtS` follow the Safety section of `to_int_unchecked` (`f32.rs` L1239–1245) and the poison results of `fptoui`/`fptosi` (LangRef L12293–12296, L12335–12338), both written as `none`; the WebAssembly specification defines the partial conversions `trunc_u`/`trunc_s` with the same definedness intervals on the truncated value (`numerics.rst` L1842–1845, L1865–1868), and CompCert's `ZofB_range` is a bounded conversion of the same shape (`IEEE754_extra.v` L840–851). `satU`/`satS` follow the Rust Reference "Numeric cast" rules (L591–595), the WebAssembly `trunc_sat_u`/`trunc_sat_s` definitions (`numerics.rst` L1891–1894, L1910–1913) and LLVM `llvm.fptoui.sat` (LangRef L21046–21054). Integer-to-float casts (`roundNat`, `twoPowRound`) round to nearest with ties to even and overflow to infinity, as the Rust Reference documents for `as` (L606–616).
- **binary32.** `Fbin32` uses the IEEE 754 binary32 parameters (`e = 8`, `p = 24`). Its toy arithmetic and comparisons are the copied toy definitions.
- **Quiet bit and payload conventions.** The toy uses quiet bit `1` = quiet. RFC 3514 L179 records that old MIPS uses the opposite convention; such targets are not modelled. RFC 3514 does not count the quiet bit as part of the payload, whereas WebAssembly does (RFC 3514 L296); the toy follows RFC 3514. WebAssembly's non-canonical NaN results are "arithmetic NaNs", whose most significant significand bit is `1` (`numerics.rst` L1044–1054), that is, quiet NaNs; `NaNChoice` also allows unchanged propagation of a signaling operand, so it is not claimed to coincide with WebAssembly's set.
- **Floating-point environment.** `S` has one rounding mode and no status flags or traps. RFC 3514 L58 states that Rust does not support alternative rounding modes or changed control bits, and L143 that observing the exception state gives unspecified results.
- **Related mechanizations** (prior art, not modelling bridges). Flocq, a Coq library of floating-point arithmetic (S. Boldo and G. Melquiond, ARITH 2011, DOI 10.1109/ARITH.2011.40); its use in CompCert for verified compilation of floating-point computations (S. Boldo, J.-H. Jourdan, X. Leroy and G. Melquiond, Journal of Automated Reasoning 54(2), 2015, DOI 10.1007/s10817-014-9317-x); the design and formal semantics of WebAssembly (A. Haas et al., PLDI 2017, DOI 10.1145/3062341.3062363). The bibliographic records were checked; no statement of these works was inspected, and none is relied on.
- **IEEE 754-2019** (DOI 10.1109/IEEESTD.2019.8766229). The text was not accessible. No clause is quoted, and nothing in the model is claimed to follow a specific clause.

Verbatim quotes of the pinned sources:

`rust-lang/rfcs` `text/3514-float-semantics.md@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4:18-19`:

```text
Floating-point operations at compile-time follow the same specification. In particular, since operations involving NaN bit patterns are non-deterministic, the same operation can lead to different NaN bit patterns when executed at compile-time (in a `const` context) vs at run-time.
Of course, the compile-time interpreter is still deterministic. It is entirely possible to implement a non-deterministic language on a deterministic machine, by simply making some fixed choices. However, we will not specify a particular choice, and we will not guarantee it to remain the same in the future.
```

`rust-lang/rfcs` `text/3514-float-semantics.md@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4:33-33`:

```text
if you never use `to_bits`, `copysign`, `is_sign_negative`, or `is_sign_positive` on a NaN, and don't construct a NaN using `from_bits`, nor use any unsafe operations that are equivalent to these safe methods, then your code will not be able to observe any non-determinism and behave according to the IEEE specification.
```

`rust-lang/rfcs` `text/3514-float-semantics.md@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4:41-42`:

```text
When you use a floating-point operation in [`const` context](https://doc.rust-lang.org/reference/const_eval.html#const-context), the same specification applies: NaN bit patterns are non-deterministic.
In particular, the bit pattern produced at compile-time can differ from the bit pattern produced by the same operation at run-time.
```

`rust-lang/rfcs` `text/3514-float-semantics.md@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4:50-50`:

```text
This RFC specifies the behavior of `+`, `-` (unary and binary), `*`, `/`, `%`, `abs`, `copysign`, `mul_add`, `sqrt`, `as`-casts that involve floating-point types, and all comparison operations on floating-point types.
```

`rust-lang/rfcs` `text/3514-float-semantics.md@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4:56-57`:

```text
Exceptions apply when the output of an operation is a NaN, and the operation is not a "bitwise" operation (unary `-`, `abs`, `copysign`).
In that case, we generally follow [the same rules as LLVM](https://llvm.org/docs/LangRef.html#behavior-of-floating-point-nan-values), which differ from the IEEE specification.
```

`rust-lang/rfcs` `text/3514-float-semantics.md@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4:63-76`:

```text
For the operations listed above, the following rules apply when a NaN value is returned:
the result has a non-deterministic sign; the quiet bit and payload are non-deterministically chosen from the following set of options:

- **Preferred NaN**: The quiet bit is set and the payload is all-zero.
- **Quieting NaN propagation**: The quiet bit is set and the payload is copied from any input operand that is a NaN.
  If the inputs and outputs do not have the same payload size (i.e., for `as` casts), then
  - If the output is smaller than the input, low-order bits of the payload get dropped.
  - If the output is larger than the input, the payload gets filled up with 0s in the low-order bits.
- **Unchanged NaN propagation**: The quiet bit and payload are copied from any input operand that is a NaN.
  If the inputs and outputs do not have the same size (i.e., for `as` casts), the same rules as for "quieting NaN propagation" apply, with one caveat: if the output is smaller than the input, droppig the low-order bits may result in a payload of 0; a payload of 0 is not possible with a signaling NaN (the all-0 significand encodes an infinity) so unchanged NaN propagation cannot occur with some inputs.
- **Target-specific NaN**: The quiet bit is set and the payload is picked from a target-specific set of
  "extra" possible NaN payloads. The set can depend on the input operand values.
  This set is empty on x86, ARM, and RISC-V (32bit and 64bit), but can be non-empty on other architectures. Targets where this set is non-empty should document this in a suitable location, e.g. their platform support page.
  (For instance, on wasm, if any input NaN does not have the preferred all-zero   payload or any input NaN is an SNaN, then this set contains all possible payloads; otherwise, it is empty. On SPARC, this set consists of the all-one payload.)
```

`rust-lang/rfcs` `text/3514-float-semantics.md@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4:78-83`:

```text
In particular, if all input NaNs are quiet (or if there are no input NaNs), then
the output NaN is definitely quiet. Signaling NaN outputs can only occur if they
are provided as an input value. For example, "fmul SNaN, 1.0" may be simplified
to SNaN rather than QNaN. Similarly, if all input NaNs are preferred (or if
there are no input NaNs) and the target does not have any "extra" NaN payloads,
then the output NaN is guaranteed to be preferred.
```

`rust-lang/rfcs` `text/3514-float-semantics.md@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4:85-85`:

```text
The non-deterministic choice happens when the operation is executed; i.e., the result of a NaN-producing floating point operation is a stable bit pattern (looking at these bits multiple times will yield consistent results), but running the same operation twice with the same inputs can produce different results.
```

`rust-lang/rfcs` `text/3514-float-semantics.md@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4:87-87`:

```text
Unless noted otherwise, the same rules also apply to NaNs returned by other library functions (e.g. `min`, `minimum`, `max`, `maximum`); other aspects of their semantics and which IEEE 754-2008 operation they correspond to are documented with the respective functions.
```

`rust-lang/rfcs` `text/3514-float-semantics.md@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4:91-95`:

```text
Evaluation of `const` items (and other entry points to CTFE) must necessarily be deterministic to ensure soundness of the type system.
`const` use of floating points does not make any guarantees beyond that:
when a floating-point operation produces a NaN result, the resulting NaN bit pattern is *some* deterministic function of the operation's inputs that satisfies the constraints placed on run-time floating point semantics.
However, the exact function is not specified, and it is allowed to change across targets and Rust versions, and even with compiler flags.
In particular, there is no guarantee that the choice made in const evaluation is consistent with the choice made at runtime.
```

`rust-lang/rust` `library/core/src/primitive_docs.rs@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:1256-1260`:

```text
/// The rules for NaN values differ between *arithmetic* and *non-arithmetic* (or "bitwise")
/// operations. The non-arithmetic operations are unary `-`, `abs`, `copysign`, `signum`,
/// `{to,from}_bits`, `{to,from}_{be,le,ne}_bytes` and `is_sign_{positive,negative}`. These
/// operations are guaranteed to exactly preserve the bit pattern of their input except for possibly
/// changing the sign bit.
```

`rust-lang/rust` `library/core/src/primitive_docs.rs@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:1304-1307`:

```text
/// When an arithmetic floating-point operation is executed in `const` context, the same rules
/// apply: no guarantee is made about which of the NaN bit patterns described above will be
/// returned. The result does not have to match what happens when executing the same code at
/// runtime, and the result can vary depending on factors such as compiler version and flags.
```

`rust-lang/rust` `library/core/src/num/f32.rs@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:1094-1104`:

```text
    /// Returns the minimum of the two numbers, ignoring NaN.
    ///
    /// If exactly one of the arguments is NaN (quiet or signaling), then the other argument is
    /// returned. If both arguments are NaN, the return value is NaN, with the bit pattern picked
    /// using the usual [rules for arithmetic operations](f32#nan-bit-patterns). If the inputs
    /// compare equal (such as for the case of `+0.0` and `-0.0`), either input may be returned
    /// non-deterministically.
    ///
    /// The handling of NaNs follows the IEEE 754-2019 semantics for `minimumNumber`, treating all
    /// NaNs the same way to ensure the operation is associative. The handling of signed zeros
    /// follows the IEEE 754-2008 semantics for `minNum`.
```

`rust-lang/rust` `library/core/src/num/f32.rs@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:1239-1245`:

```text
    /// # Safety
    ///
    /// The value must:
    ///
    /// * Not be `NaN`
    /// * Not be infinite
    /// * Be representable in the return type `Int`, after truncating off its fractional part
```

`rust-lang/reference` `src/expressions/operator-expr.md@5e6c977381e3cb5dcfdef97013bfae3317a181bf:591-595`:

```text
r[expr.as.numeric.float-as-int]
* Casting from a float to an integer will round the float towards zero
    * `NaN` will return `0`
    * Values larger than the maximum integer value, including `INFINITY`, will saturate to the maximum value of the integer type.
    * Values smaller than the minimum integer value, including `NEG_INFINITY`, will saturate to the minimum value of the integer type.
```

`llvm/llvm-project` `llvm/docs/LangRef.rst@3623fe661ae35c6c80ac221f14d85be76aa870f1:3826-3829`:

```text
For the purpose of this section, ``bitcast`` as well as the following operations
are not "floating-point math operations": ``fneg``, ``llvm.fabs``, and
``llvm.copysign``. These operations act directly on the underlying bit
representation and never change anything except possibly for the sign bit.
```

`llvm/llvm-project` `llvm/docs/LangRef.rst@3623fe661ae35c6c80ac221f14d85be76aa870f1:3831-3848`:

```text
Floating-point math operations that return a NaN are an exception from the
general principle that LLVM implements IEEE-754 semantics. Unless specified
otherwise, the following rules apply whenever the IEEE-754 semantics say that a
NaN value is returned: the result has a non-deterministic sign; the quiet bit
and payload are non-deterministically chosen from the following set of options:

- The quiet bit is set and the payload is all-zero. ("Preferred NaN" case)
- The quiet bit is set and the payload is copied from any input operand that is
  a NaN. ("Quieting NaN propagation" case)
- The quiet bit and payload are copied from any input operand that is a NaN.
  ("Unchanged NaN propagation" case)
- The quiet bit is set and the payload is picked from a target-specific set of
  "extra" possible NaN payloads. The set can depend on the input operand values.
  This set is empty on x86 and ARM, but can be non-empty on other architectures.
  (For instance, on wasm, if any input NaN does not have the preferred all-zero
  payload or any input NaN is an SNaN, then this set contains all possible
  payloads; otherwise, it is empty. On SPARC, this set consists of the all-one
  payload.)
```

`llvm/llvm-project` `llvm/docs/LangRef.rst@3623fe661ae35c6c80ac221f14d85be76aa870f1:12293-12296`:

```text
The '``fptoui``' instruction converts its :ref:`floating-point
<t_floating>` operand into the nearest (rounding towards zero)
unsigned integer value. If the value cannot fit in ``ty2``, the result
is a :ref:`poison value <poisonvalues>`.
```

`llvm/llvm-project` `llvm/docs/LangRef.rst@3623fe661ae35c6c80ac221f14d85be76aa870f1:12335-12338`:

```text
The '``fptosi``' instruction converts its :ref:`floating-point
<t_floating>` operand into the nearest (rounding towards zero)
signed integer value. If the value cannot fit in ``ty2``, the result
is a :ref:`poison value <poisonvalues>`.
```

`WebAssembly/spec` `document/core/exec/numerics.rst@631890ee71035d9903fe5fd3a2b476bb82c76112:1044-1054`:

```text
NaN Propagation
...............

When the result of a floating-point operator other than |fneg|, |fabs|, or |fcopysign| is a :ref:`NaN <syntax-nan>`,
then its sign is non-deterministic and the :ref:`payload <syntax-payload>` is computed as follows:

* If the payload of all NaN inputs to the operator is :ref:`canonical <canonical-nan>` (including the case that there are no NaN inputs), then the payload of the output is canonical as well.

* Otherwise the payload is picked non-deterministically among all :ref:`arithmetic NaNs <arithmetic-nan>`; that is, its most significant bit is :math:`1` and all others are unspecified.

* In the :ref:`deterministic profile <profile-deterministic>`, only positive canonical NaN outputs are produced.
```

`AbsInt/CompCert` `lib/IEEE754_extra.v@1670ae76afdb2546402898b6e9064d7229845d24:699-701`:

```text
Theorem ZofB_correct:
  forall f,
  ZofB f = if is_finite _ _ f then Some (Ztrunc (B2R _ _ f)) else None.
```

`AbsInt/CompCert` `lib/IEEE754_extra.v@1670ae76afdb2546402898b6e9064d7229845d24:751-752`:

```text
Theorem ZofB_range_pos:
  forall f n, ZofB f = Some n -> 0 < n -> (IZR n <= B2R _ _ f < IZR (n + 1)%Z)%R.
```

`AbsInt/CompCert` `lib/IEEE754_extra.v@1670ae76afdb2546402898b6e9064d7229845d24:758-759`:

```text
Theorem ZofB_range_neg:
  forall f n, ZofB f = Some n -> n < 0 -> (IZR (n - 1)%Z < B2R _ _ f <= IZR n)%R.
```

`AbsInt/CompCert` `lib/IEEE754_extra.v@1670ae76afdb2546402898b6e9064d7229845d24:771-772`:

```text
Theorem ZofB_range_zero:
  forall f, ZofB f = Some 0 -> (-1 < B2R _ _ f < 1)%R.
```

`AbsInt/CompCert` `lib/IEEE754_extra.v@1670ae76afdb2546402898b6e9064d7229845d24:778-779`:

```text
Theorem ZofB_range_nonneg:
  forall f n, ZofB f = Some n -> 0 <= n -> (-1 < B2R _ _ f < IZR (n + 1)%Z)%R.
```

`AbsInt/CompCert` `lib/Floats.v@1670ae76afdb2546402898b6e9064d7229845d24:536-540`:

```text
Theorem to_intu_to_int_1:
  forall x n,
  cmp Clt x (of_intu ox8000_0000) = true ->
  to_intu x = Some n ->
  to_int x = Some n.
```

`rust-lang/rfcs` `text/3514-float-semantics.md@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4:58-58`:

```text
Furthermore, Rust considers floating-point status bits to not be observable, and Rust does not support executing floating-point operations with alternative rounding modes or otherwise changed floating-point control bits.
```

`rust-lang/rfcs` `text/3514-float-semantics.md@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4:130-130`:

```text
Even running the same expression (such as `0.0 / 0.0`) twice as part of evaluating a given `const` item, or in two different `const` items, may produce different results.
```

`rust-lang/rfcs` `text/3514-float-semantics.md@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4:143-143`:

```text
Furthermore, observing the floating-point exception state yields entirely unspecified results: Rust floating-point operations may or may not be executed at the place in the code where they were originally written, and the floating-point status bits can change even if no floating-point operation exists in the source code.
```

`rust-lang/rfcs` `text/3514-float-semantics.md@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4:179-179`:

```text
- On old MIPS, the interpretation of "signaling" and "quiet" is the opposite of what has been specified above. The effective spec on those targets is that any NaN-producing operation can non-deterministically produce an arbitrary (signaling or quiet) NaN. Currently, LLVM does not have a way of implementing their own NaN semantics for this target, so there's not a lot we can do on the Rust side. [LLVM issue](https://github.com/llvm/llvm-project/issues/60796)
```

`rust-lang/rfcs` `text/3514-float-semantics.md@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4:222-224`:

```text
However, there is one operation in C that can sometimes produce a non-NaN result on *quiet* NaN inputs specifically: [`pow`](https://en.cppreference.com/w/c/numeric/math/pow). For instance, "`pow(+1, exponent)` returns `1` for any `exponent`, even when `exponent` is `NaN`".
C also says "This specification does not define the behavior of signaling NaNs", and in practice, `pow(1, sNaN)` returns a NaN.
In other words, `pow` *does* [make a difference](https://play.rust-lang.org/?version=stable&mode=debug&edition=2021&gist=5a0855c2cb6630256e4407624650c4c9) between quiet and signaling NaN.
```

`rust-lang/rfcs` `text/3514-float-semantics.md@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4:296-296`:

```text
(We are departing from wasm terminology since "canonical" already has a different meaning in the IEEE spec. For similar reasons, we consider the NaN payload to *not* include the quiet/signaling bit, whereas wasm considers the quiet/signaling bit to be part of the payload.)
```

`rust-lang/rust` `library/core/src/num/f32.rs@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:1150-1158`:

```text
    /// If at least one of the arguments is NaN, the return value is NaN, with the bit pattern
    /// picked using the usual [rules for arithmetic operations](f32#nan-bit-patterns). Furthermore,
    /// `-0.0` is considered to be less than `+0.0`, making this function fully deterministic for
    /// non-NaN inputs.
    ///
    /// This is in contrast to [`f32::min`] which only returns NaN when *both* arguments are NaN,
    /// and which does not reliably order `-0.0` and `+0.0`.
    ///
    /// This follows the IEEE 754-2019 semantics for `minimum`.
```

`rust-lang/reference` `src/expressions/operator-expr.md@5e6c977381e3cb5dcfdef97013bfae3317a181bf:606-616`:

````text
r[expr.as.numeric.int-as-float]
* Casting from an integer to float will produce the closest possible float \*
    * if necessary, rounding is according to `roundTiesToEven` mode \*\*\*
    * on overflow, infinity (of the same sign as the input) is produced
    * note: with the current set of numeric types, overflow can only happen on `u128 as f32` for values greater or equal to `f32::MAX + (0.5 ULP)`

  ```rust
  assert_eq!(1337i32 as f32, 1337f32);
  assert_eq!(123_456_789i32 as f32, 123_456_790f32, "Rounded");
  assert_eq!(0xffffffff_ffffffff_ffffffff_ffffffff_u128 as f32, f32::INFINITY);
  ```
````

`llvm/llvm-project` `llvm/docs/LangRef.rst@3623fe661ae35c6c80ac221f14d85be76aa870f1:17070-17078`:

```text
Follows the semantics of minNum in IEEE-754-2008, except that -0.0 < +0.0 for the purposes
of this intrinsic. As for signaling NaNs, per the minNum semantics, if either operand is sNaN,
the result is qNaN. This matches the recommended behavior for the libm
function ``fmin``, although not all implementations have implemented these recommended behaviors.

If either operand is a qNaN, returns the other non-NaN operand. Returns NaN only if both operands are
NaN or if either operand is sNaN. Note that arithmetic on an sNaN doesn't consistently produce a qNaN,
so arithmetic feeding into a minnum can produce inconsistent results. For example,
``minnum(fadd(sNaN, -0.0), 1.0)`` can produce qNaN or 1.0 depending on whether ``fadd`` is folded.
```

`llvm/llvm-project` `llvm/docs/LangRef.rst@3623fe661ae35c6c80ac221f14d85be76aa870f1:17190-17193`:

```text
If either operand is a NaN, returns NaN. Otherwise returns the lesser
of the two arguments. -0.0 is considered to be less than +0.0 for this
intrinsic. Note that these are the semantics specified in the draft of
IEEE 754-2019.
```

`llvm/llvm-project` `llvm/docs/LangRef.rst@3623fe661ae35c6c80ac221f14d85be76aa870f1:21046-21054`:

```text

- If the argument is any NaN, zero is returned.
- If the argument is smaller than zero (this includes negative infinity),
  zero is returned.
- If the argument is larger than the largest representable unsigned integer of
  the result type (this includes positive infinity), the largest representable
  unsigned integer is returned.
- Otherwise, the result of rounding the argument towards zero is returned.

```

`WebAssembly/spec` `document/core/exec/numerics.rst@631890ee71035d9903fe5fd3a2b476bb82c76112:1842-1845`:

```text
   \truncu_{M,N}(\pm \NAN(n)) &=& \{\} \\
   \truncu_{M,N}(\pm \infty) &=& \{\} \\
   \truncu_{M,N}(\pm q) &=& \truncz(\pm q) & (\iff -1 < \truncz(\pm q) < 2^N) \\
   \truncu_{M,N}(\pm q) &=& \{\} & (\otherwise) \\
```

`WebAssembly/spec` `document/core/exec/numerics.rst@631890ee71035d9903fe5fd3a2b476bb82c76112:1865-1868`:

```text
   \truncs_{M,N}(\pm \NAN(n)) &=& \{\} \\
   \truncs_{M,N}(\pm \infty) &=& \{\} \\
   \truncs_{M,N}(\pm q) &=& \truncz(\pm q) & (\iff -2^{N-1} - 1 < \truncz(\pm q) < 2^{N-1}) \\
   \truncs_{M,N}(\pm q) &=& \{\} & (\otherwise) \\
```

`WebAssembly/spec` `document/core/exec/numerics.rst@631890ee71035d9903fe5fd3a2b476bb82c76112:1891-1894`:

```text
   \truncsatu_{M,N}(\pm \NAN(n)) &=& 0 \\
   \truncsatu_{M,N}(- \infty) &=& 0 \\
   \truncsatu_{M,N}(+ \infty) &=& 2^N - 1 \\
   \truncsatu_{M,N}(z) &=& \satu_N(\truncz(z)) \\
```

`WebAssembly/spec` `document/core/exec/numerics.rst@631890ee71035d9903fe5fd3a2b476bb82c76112:1910-1913`:

```text
   \truncsats_{M,N}(\pm \NAN(n)) &=& 0 \\
   \truncsats_{M,N}(- \infty) &=& -2^{N-1} \\
   \truncsats_{M,N}(+ \infty) &=& 2^{N-1}-1 \\
   \truncsats_{M,N}(z) &=& \signed_N^{-1}(\sats_N(\trunc(z))) \\
```

`AbsInt/CompCert` `lib/IEEE754_extra.v@1670ae76afdb2546402898b6e9064d7229845d24:840-851`:

```text
Definition ZofB_range (f: binary_float) (zmin zmax: Z): option Z :=
  match ZofB f with
  | None => None
  | Some z => if Z.leb zmin z && Z.leb z zmax then Some z else None
  end.

Theorem ZofB_range_correct:
  forall f min max,
  let n := Ztrunc (B2R _ _ f) in
  ZofB_range f min max =
  if is_finite _ _ f && Z.leb min n && Z.leb n max then Some n else None.
Proof.
```

### Auxiliary lemmas cited by name

Refinement and folding:

```lean
-- Toy/FloatTier/Statements.lean:21-22
theorem FExpr.evalS_evalT_of_tierSound {X : Extra f} {τ : Tier f} (hτ : TierSound X τ)
    (e : FExpr f) (ρ : Nat → V f) : e.evalS X ρ (e.evalT τ ρ) := by …
```

```lean
-- Toy/FloatTier/Statements.lean:52-53
theorem Prog.runS_runT_of_tierSound {X : Extra f} {τ : Tier f} (hτ : TierSound X τ)
    (P : Prog f) (ρ : Nat → V f) : P.runS X ρ (P.runT τ ρ) := by …
```

```lean
-- Toy/FloatTier/Statements.lean:82
theorem tierOf_sound (X : Extra f) (pol : ChoicePolicy) : TierSound X (tierOf pol) := by …
```

```lean
-- Toy/FloatTier/Statements.lean:163-164
theorem FExpr.evalT_of_closed (τ : Tier f) (e : FExpr f) (he : e.closed = true)
    (ρ ρ' : Nat → V f) : e.evalT τ ρ = e.evalT τ ρ' := by …
```

```lean
-- Toy/FloatTier/Statements.lean:180-181
theorem FExpr.evalS_of_evalS_fold {X : Extra f} {τ : Tier f} (hτ : TierSound X τ)
    (ρ : Nat → V f) : ∀ (e : FExpr f) (r : V f), (e.fold τ).evalS X ρ r → e.evalS X ρ r := by …
```

```lean
-- Toy/FloatTier/VLemmas.lean:209
theorem V.bits_injective : Function.Injective (V.bits (f := f)) := by …
```

```lean
-- Toy/FloatTier/VLemmas.lean:204-205
theorem V.bits_withSign_true (x : V f) :
    (x.withSign true).bits = (x.withSign false).bits + 2 ^ (f.e + f.p - 1) := by …
```

```lean
-- Toy/FloatTier/Counterexamples.lean:413-415
theorem primSet_of_isNaN {X X' : Extra f} {p : Prim} {x y r r' : V f}
    (h : primSet X p x y r) (hr : r.isNaN = true) (h' : NaNChoice X' x y r') :
    primSet X' p x y r' := by …
```

Non-vacuity witnesses, positive controls and counterexamples for the refinement and determinism results:

```lean
-- Toy/FloatTier/Counterexamples.lean:121-123
theorem refinesS_iff_tierSound_nonvacuous :
    (RefinesS (noExtra (f := F23)) tierCtfe ∧ TierSound (noExtra (f := F23)) tierCtfe) ∧
    (¬ RefinesS (noExtra (f := F23)) tierBad ∧ ¬ TierSound (noExtra (f := F23)) tierBad) := by …
```

```lean
-- Toy/FloatTier/Counterexamples.lean:373
theorem not_tierSound_tierBad (X : Extra f) : ¬ TierSound X tierBad := by …
```

```lean
-- Toy/FloatTier/Counterexamples.lean:182-184
theorem exists_runS_not_realized_by_any_tier (X : Extra f) (ρ : Nat → V f) :
    (progSelfEqCopysignNaN f).runS X ρ 0 ∧
    ∀ τ : Tier f, (progSelfEqCopysignNaN f).runT τ ρ = 1 := by …
```

```lean
-- Toy/FloatTier/Counterexamples.lean:463-464
theorem tierExtraPay1_sound_extra_not_noExtra :
    TierSound extraPay1 tierExtraPay1 ∧ ¬ TierSound noExtra tierExtraPay1 := by …
```

```lean
-- Toy/FloatTier/Counterexamples.lean:481-482
theorem tierSound_extra_irrelevant_of_p_eq_two (hp2 : f.p = 2) (X : Extra f) (τ : Tier f) :
    TierSound X τ ↔ TierSound noExtra τ := by …
```

```lean
-- Toy/FloatTier/Counterexamples.lean:133-134
theorem tiers_agree_on_isNaN_zero_mul_inf (ρ : Nat → V f) :
    (progIsNaNZeroMulInf f).runT tierCtfe ρ = 1 ∧ (progIsNaNZeroMulInf f).runT tierRunA ρ = 1 := by …
```

```lean
-- Toy/FloatTier/Counterexamples.lean:143-148
theorem runS_of_runS_fold_nonvacuous (ρ : Nat → V f) :
    TierSound (noExtra (f := f)) tierCtfe ∧
    (progBitsZeroMulInf f).fold tierCtfe = .toBits (.lit (V.prefNaN f false)) ∧
    ((progBitsZeroMulInf f).fold tierCtfe).runS noExtra ρ (V.prefNaN f false).bits ∧
    (progBitsZeroMulInf f).runS noExtra ρ (V.prefNaN f true).bits ∧
    ¬ ((progBitsZeroMulInf f).fold tierCtfe).runS noExtra ρ (V.prefNaN f true).bits := by …
```

```lean
-- Toy/FloatTier/Counterexamples.lean:165-169
theorem fold_tierCtfe_preserves_tierRunA_nan_free (ρ : Nat → V f) :
    (progBitsCopysignVarInfMulNegInf f).fold tierCtfe =
        .toBits (.copysign (.var 0) (.lit (.inf true))) ∧
      ((progBitsCopysignVarInfMulNegInf f).fold tierCtfe).runT tierRunA ρ =
        (progBitsCopysignVarInfMulNegInf f).runT tierRunA ρ := by …
```

```lean
-- Toy/FloatTier/Counterexamples.lean:384-386
theorem fold_unsound_tier_not_refinement (X : Extra f) (ρ : Nat → V f) :
    ¬ TierSound X tierBad ∧ ((progIsNaNZeroMulInf f).fold tierBad).runS X ρ 0 ∧
      ¬ (progIsNaNZeroMulInf f).runS X ρ 0 := by …
```

```lean
-- Toy/FloatTier/Counterexamples.lean:399-404
theorem unsound_tier_breaks_agreement (X : Extra f) (ρ : Nat → V f) :
    ¬ TierSound X tierBad ∧ TierSound X tierCtfe ∧
    (progIsNaNZeroMulInf f).BitSafe X ρ V.isNaNOrZero ∧
    (progIsNaNZeroMulInf f).BitSafe X ρ V.isNaN ∧
    (progIsNaNZeroMulInf f).MinMaxFree = true ∧
    (progIsNaNZeroMulInf f).runT tierBad ρ ≠ (progIsNaNZeroMulInf f).runT tierCtfe ρ := by …
```

```lean
-- Toy/FloatTier/Counterexamples.lean:343-347
theorem progNaNBranchSign_nonvacuous (X : Extra f) (ρ : Nat → V f) :
    (progNaNBranchSign f).MinMaxFree = true ∧
    (progNaNBranchSign f).BitSafe X ρ V.isNaNOrZero ∧
    (progNaNBranchSign f).BitSafe X ρ V.isNaN ∧
    (∀ n, (progNaNBranchSign f).runS X ρ n ↔ n = 1) := by …
```

```lean
-- Toy/FloatTier/Counterexamples.lean:363-367
theorem progMinZeroEq_nonvacuous (X : Extra f) (ρ : Nat → V f) :
    (progMinZeroEq f).BitSafe X ρ V.isNaNOrZero ∧
    (FExpr.prim .min (.lit (V.zero f false)) (.lit (V.zero f true))).evalS X ρ (V.zero f false) ∧
    (FExpr.prim .min (.lit (V.zero f false)) (.lit (V.zero f true))).evalS X ρ (V.zero f true) ∧
    (∀ n, (progMinZeroEq f).runS X ρ n ↔ n = 1) := …
```

```lean
-- Toy/FloatTier/Counterexamples.lean:599-602
theorem progIsNaNLitAdd_nonvacuous (X : Extra f) (ρ : Nat → V f) :
    (progIsNaNLitAdd f).MinMaxFree = true ∧ (progIsNaNLitAdd f).BitSafe X ρ V.isNaN ∧
    (progIsNaNLitAdd f).BitSafe X ρ V.isNaNOrZero ∧
    (∀ n, (progIsNaNLitAdd f).runS X ρ n ↔ n = 1) := by …
```

```lean
-- Toy/FloatTier/Counterexamples.lean:512-516
theorem ex_bitSafe_guarded (X : Extra f) (ρ : Nat → V f) :
    (progGuardedDeadCopysign f).BitSafe X ρ V.isNaNOrZero ∧
    (FExpr.prim .mul (.lit (V.zero f false)) (.lit (.inf false))).evalS X ρ (V.prefNaN f false) ∧
    (∀ n, (progGuardedDeadCopysign f).runS X ρ n ↔ n = 1) ∧
    (progGuardedInputCopysign f).BitSafe X ρ V.isNaNOrZero := by …
```

```lean
-- Toy/FloatTier/Counterexamples.lean:568-572
theorem bitSafe_not_necessary (X : Extra f) (ρ : Nat → V f) :
    ¬ (progSignBitAbsNaN f).BitSafe X ρ V.isNaN ∧ (progSignBitAbsNaN f).MinMaxFree = true ∧
    (∀ n, (progSignBitAbsNaN f).runS X ρ n ↔ n = 0) ∧
    ¬ (progBitsNaNLit f).BitSafe X ρ V.isNaN ∧ (progBitsNaNLit f).MinMaxFree = true ∧
    (∀ n, (progBitsNaNLit f).runS X ρ n ↔ n = (V.prefNaN f true).bits) := by …
```

```lean
-- Toy/FloatTier/Counterexamples.lean:622-623
theorem refuted_value_level_observations_of_sound_tiers_agree (ρ : Nat → V f) :
    ¬ (∀ (a b : FExpr f), (Prog.lt a b).runT tierCtfe ρ = (Prog.lt a b).runT tierRunA ρ) := by …
```

```lean
-- Toy/FloatTier/Counterexamples.lean:637-638
theorem refuted_extra_payload_tier_separates_noExtra_p2 :
    ¬ ∃ (X : Extra F32) (τ : Tier F32), TierSound X τ ∧ ¬ TierSound noExtra τ := by …
```

Conversion lemmas, witnesses and counterexamples:

```lean
-- Toy/FloatTier/CastStatements.lean:33
theorem two_pow_qneg_le_maxUnits (f : Fmt) : 2 ^ f.qneg ≤ f.maxUnits := by …
```

```lean
-- Toy/FloatTier/CastStatements.lean:43-44
theorem twoPowRound_of_fits {W : Nat} (h : TwoPowFits f W) :
    (twoPowRound f W).isFinite = true ∧ key (twoPowRound f W) = ((2 ^ (W + f.qneg) : Nat) : Int) := by …
```

```lean
-- Toy/FloatTier/CastStatements.lean:51
theorem twoPowRound_of_not_fits {W : Nat} (h : ¬ TwoPowFits f W) : twoPowRound f W = .inf false := by …
```

```lean
-- Toy/FloatTier/CastStatements.lean:58-59
theorem trunc_uval_of_not_finite (x : FP f) (hx : x.isFinite = false) :
    trunc x = 0 ∧ x.uval = 0 := by …
```

```lean
-- Toy/FloatTier/CastStatements.lean:66-67
theorem not_inOpen_of_not_finite (W k : Nat) (x : FP f) (hx : x.isFinite = false) :
    ¬ InOpenU W x ∧ ¬ InOpenS k x := by …
```

```lean
-- Toy/FloatTier/CastStatements.lean:152-153
theorem cvtU_isSome_iff (W : Nat) (x : FP f) :
    (cvtU W x).isSome = true ↔ InOpenU W x := by …
```

```lean
-- Toy/FloatTier/CastStatements.lean:165-166
theorem cvtU_eq_some_of_inOpenU {W : Nat} {x : FP f} (h : InOpenU W x) :
    cvtU W x = some (trunc x) := by …
```

```lean
-- Toy/FloatTier/CastStatements.lean:172-173
theorem cvtS_eq_some_of_inOpenS {k : Nat} {x : FP f} (h : InOpenS k x) :
    cvtS k x = some (trunc x) := by …
```

```lean
-- Toy/FloatTier/CastStatements.lean:247-249
theorem isFinite_of_uval_bounds (W : Nat) (x : FP f) :
    (x.uval ≤ -((2 : Int) ^ f.qneg) → x.isFinite = true) ∧
    ((2 : Int) ^ W * 2 ^ f.qneg ≤ x.uval → x.isFinite = true) := by …
```

```lean
-- Toy/FloatTier/CastExamples.lean:74-79
theorem trunc_mem_range_iff_fails_at_inf {f : Fmt} (W k : Nat) :
    (FP.inf false : FP f).isFinite = false ∧
    ¬ ((0 ≤ trunc (FP.inf false : FP f) ∧ trunc (FP.inf false : FP f) ≤ 2 ^ W - 1) ↔
        InOpenU W (FP.inf false : FP f)) ∧
    ¬ ((-(2 ^ k) ≤ trunc (FP.inf false : FP f) ∧ trunc (FP.inf false : FP f) ≤ 2 ^ k - 1) ↔
        InOpenS k (FP.inf false : FP f)) := by …
```

```lean
-- Toy/FloatTier/CastExamples.lean:240-244
theorem cast_results_nonvacuous :
    f33_3p5.isFinite = true ∧ f33_4.isFinite = true ∧ f33_m3p5.isFinite = true ∧
    InOpenU 2 f33_3p5 ∧ ¬ InOpenU 2 f33_4 ∧ InOpenS 2 f33_m3p5 ∧ ¬ InOpenS 1 f33_m3p5 ∧
    cvtU 2 f33_3p5 = some 3 ∧ cvtU 2 f33_4 = none ∧
    cvtS 2 f33_m3p5 = some (-3) ∧ cvtS 1 f33_m3p5 = none := by …
```

```lean
-- Toy/FloatTier/CastExamples.lean:251-261
theorem rangeCheckU_twoPowRound_iff_nonvacuous :
    (TwoPowFits F33 2 ∧ twoPowRound F33 2 = f33_4 ∧
      rangeCheckU (twoPowRound F33 2) f33_3p5 = true ∧ (cvtU 2 f33_3p5).isSome = true ∧
      rangeCheckU (twoPowRound F33 2) f33_4 = false ∧ (cvtU 2 f33_4).isSome = false) ∧
    (¬ TwoPowFits F33 4 ∧ twoPowRound F33 4 = .inf false ∧
      rangeCheckU (twoPowRound F33 4) f33_4 = true ∧ (cvtU 4 f33_4).isSome = true ∧
      rangeCheckU (twoPowRound F33 4) (FP.inf false : FP F33) = false ∧
      (cvtU 4 (FP.inf false : FP F33)).isSome = false) ∧
    (TwoPowFits Fbin32 32 ∧
      rangeCheckU (twoPowRound Fbin32 32) (twoPowRound Fbin32 32) = false ∧
      (cvtU 32 (twoPowRound Fbin32 32)).isSome = false) := by …
```

```lean
-- Toy/FloatTier/CastExamples.lean:228-233
theorem signed_lower_guards_not_exact_F33 :
    (round F33 true (9 * 2 ^ F33.qneg) 0 = FP.mk' F33 true 6 0 ∧
      lt (round F33 true (9 * 2 ^ F33.qneg) 0) (FP.mk' F33 true 6 0) = false ∧
      cvtS 3 (FP.mk' F33 true 6 0) = some (-8)) ∧
    (le (FP.mk' F33 true 4 0) (FP.mk' F33 true 4 1) = false ∧
      cvtS 1 (FP.mk' F33 true 4 1) = some (-2)) := by …
```

```lean
-- Toy/FloatTier/CastExamples.lean:212-213
theorem refuted_naiveCheckU_exact_at_W_eq_p :
    F23.p = 3 ∧ ¬ (∀ x : FP F23, naiveCheckU 3 x = (cvtU 3 x).isSome) := by …
```

```lean
-- Toy/FloatTier/CastExamples.lean:50
theorem satU_width_zero {f : Fmt} (x : FP f) : satU 0 x = 0 := by …
```

The congruence facts behind `observation-determinism-nan-or-zero` and `observation-determinism-minmax-free` are packaged in the auxiliary structure `DetCongr` (`Toy/FloatTier/Determinism.lean`), with the instances `detCongr_valEq` and `detCongr_toFP` and the generic theorems `FExpr.evalS_rel_of_bitSafe` and `Prog.runS_unique_of_detCongr`. Their ingredients are `add_eqNsz_congr`, `sub_eqNsz_congr`, `mul_eqNsz_congr`, `lt_eqNsz_congr`, `feq_eqNsz_congr` and `eqNsz_of_key_eq` (`Toy/FloatTier/Lemmas.lean`), and `primSet_valEq_congr` and `primSet_toFP_congr` (`Toy/FloatTier/VLemmas.lean`):

```lean
-- Toy/FloatTier/Determinism.lean:26-39
structure DetCongr (X : Extra f) (R : V f → V f → Prop) (bad : V f → Bool)
    (ok : Prim → Bool) : Prop where
  refl : ∀ x, R x x
  prim : ∀ p, ok p = true → ∀ {x₁ x₂ y₁ y₂ r₁ r₂ : V f}, R x₁ x₂ → R y₁ y₂ →
    primSet X p x₁ y₁ r₁ → primSet X p x₂ y₂ r₂ → R r₁ r₂
  neg : ∀ {x₁ x₂ : V f}, R x₁ x₂ → R x₁.neg x₂.neg
  abs : ∀ {x₁ x₂ : V f}, R x₁ x₂ → R x₁.abs x₂.abs
  copysign : ∀ {x₁ x₂ : V f} (y : V f), R x₁ x₂ → R (x₁.copysign y) (x₂.copysign y)
  good : ∀ {y₁ y₂ : V f}, R y₁ y₂ → bad y₁ = false → y₁ = y₂
  lt : ∀ {x₁ x₂ y₁ y₂ : V f}, R x₁ x₂ → R y₁ y₂ →
    lt x₁.toFP y₁.toFP = lt x₂.toFP y₂.toFP
  isNaN : ∀ {x₁ x₂ : V f}, R x₁ x₂ → x₁.isNaN = x₂.isNaN
  feq : ∀ {x₁ x₂ y₁ y₂ : V f}, R x₁ x₂ → R y₁ y₂ →
    feq x₁.toFP y₁.toFP = feq x₂.toFP y₂.toFP
```

```lean
-- Toy/FloatTier/Determinism.lean:41-44
theorem FExpr.evalS_rel_of_bitSafe {X : Extra f} {R : V f → V f → Prop} {bad : V f → Bool}
    {ok : Prim → Bool} (hC : DetCongr X R bad ok) (ρ : Nat → V f) :
    ∀ (e : FExpr f), e.PrimsOk ok = true → e.BitSafe X ρ bad →
      ∀ {r₁ r₂ : V f}, e.evalS X ρ r₁ → e.evalS X ρ r₂ → R r₁ r₂ := by …
```

```lean
-- Toy/FloatTier/Determinism.lean:88-91
theorem Prog.runS_unique_of_detCongr {X : Extra f} {R : V f → V f → Prop} {bad : V f → Bool}
    {ok : Prim → Bool} (hC : DetCongr X R bad ok) (ρ : Nat → V f) (P : Prog f)
    (hok : P.PrimsOk ok = true) (hs : P.BitSafe X ρ bad) {n₁ n₂ : Nat}
    (h₁ : P.runS X ρ n₁) (h₂ : P.runS X ρ n₂) : n₁ = n₂ := by …
```

```lean
-- Toy/FloatTier/Determinism.lean:116
theorem detCongr_valEq (X : Extra f) : DetCongr X ValEq V.isNaNOrZero (fun _ => true) := by …
```

```lean
-- Toy/FloatTier/Determinism.lean:129-130
theorem detCongr_toFP (X : Extra f) :
    DetCongr X (fun x y => x.toFP = y.toFP) V.isNaN Prim.isArith := by …
```

```lean
-- Toy/FloatTier/Lemmas.lean:175-176
theorem eqNsz_of_key_eq {x y : FP f} (hx : x.isNaN = false) (hy : y.isNaN = false)
    (h : key x = key y) : EqNsz x y := by …
```

```lean
-- Toy/FloatTier/Lemmas.lean:81-82
theorem add_eqNsz_congr {x x' y y' : FP f} (hx : EqNsz x x') (hy : EqNsz y y') :
    EqNsz (add x y) (add x' y') := by …
```

```lean
-- Toy/FloatTier/Lemmas.lean:104-105
theorem sub_eqNsz_congr {x x' y y' : FP f} (hx : EqNsz x x') (hy : EqNsz y y') :
    EqNsz (sub x y) (sub x' y') := …
```

```lean
-- Toy/FloatTier/Lemmas.lean:132-133
theorem mul_eqNsz_congr {x x' y y' : FP f} (hx : EqNsz x x') (hy : EqNsz y y') :
    EqNsz (mul x y) (mul x' y') := by …
```

```lean
-- Toy/FloatTier/Lemmas.lean:158-159
theorem lt_eqNsz_congr {x x' y y' : FP f} (hx : EqNsz x x') (hy : EqNsz y y') :
    lt x y = lt x' y' := by …
```

```lean
-- Toy/FloatTier/Lemmas.lean:164-165
theorem feq_eqNsz_congr {x x' y y' : FP f} (hx : EqNsz x x') (hy : EqNsz y y') :
    feq x y = feq x' y' := by …
```

```lean
-- Toy/FloatTier/VLemmas.lean:155-157
theorem primSet_valEq_congr {X : Extra f} (p : Prim) {x₁ x₂ y₁ y₂ r₁ r₂ : V f}
    (hx : ValEq x₁ x₂) (hy : ValEq y₁ y₂)
    (h₁ : primSet X p x₁ y₁ r₁) (h₂ : primSet X p x₂ y₂ r₂) : ValEq r₁ r₂ := by …
```

```lean
-- Toy/FloatTier/VLemmas.lean:169-171
theorem primSet_toFP_congr {X : Extra f} (p : Prim) (hp : p.isArith = true)
    {x₁ x₂ y₁ y₂ r₁ r₂ : V f} (hx : x₁.toFP = x₂.toFP) (hy : y₁.toFP = y₂.toFP)
    (h₁ : primSet X p x₁ y₁ r₁) (h₂ : primSet X p x₂ y₂ r₂) : r₁.toFP = r₂.toFP := by …
```

### Other declarations cited by name

Definition examples, literals and the remaining declarations mentioned above, quoted verbatim.

In namespace `Fmt`: `Toy.FloatTier.Fmt.qneg`, a quantity computed from the format.

```lean
-- Toy/FloatTier/Base.lean:53
def qneg : Nat := f.bias + f.p - 2
```

In namespace `FP`: `Toy.FloatTier.FP.mk'`.

```lean
-- Toy/FloatTier/Instances.lean:29-30
def FP.mk' (f : Fmt) (s : Bool) (E M : Nat) (hE : E < f.expCount := by decide)
    (hM : M < f.fracCount := by decide) : FP f := .fin s ⟨E, hE⟩ ⟨M, hM⟩
```

In namespace `Fmt`: `Toy.FloatTier.Fmt.bias`, a quantity computed from the format.

```lean
-- Toy/FloatTier/Base.lean:42
def bias : Nat := 2 ^ (f.e - 1) - 1
```

In namespace `FP`: `Toy.FloatTier.FP.bits`, on the NaN-collapsed view (distinct from `V.bits` on payload-carrying values).

```lean
-- Toy/FloatTier/Base.lean:124-127
def bits : FP f → Nat
  | .nan => (2 ^ f.e - 1) * 2 ^ (f.p - 1) + 2 ^ (f.p - 2)
  | .inf s => (if s then 2 ^ (f.e + f.p - 1) else 0) + (2 ^ f.e - 1) * 2 ^ (f.p - 1)
  | .fin s E M => (if s then 2 ^ (f.e + f.p - 1) else 0) + E.val * 2 ^ (f.p - 1) + M.val
```

```lean
-- Toy/FloatTier/Examples.lean:101-102
theorem ex_bitSafe_rejects (X : Extra f) (ρ : Nat → V f) :
    ¬ (progBitsZeroMulInf f).BitSafe X ρ V.isNaN := by …
```

```lean
-- Toy/FloatTier/Examples.lean:30-32
theorem ex_bits_nan_variants_binary32 :
    (V.prefNaN Fbin32 true).bits = 0xFFC00000 ∧
    (V.snan false ⟨0, by decide⟩ : V Fbin32).bits = 0x7F800001 := by …
```

```lean
-- Toy/FloatTier/Examples.lean:26
theorem ex_bits_prefNaN_binary32 : (V.prefNaN Fbin32 false).bits = 0x7FC00000 := by …
```

```lean
-- Toy/FloatTier/CastExamples.lean:31-32
theorem ex_cvtS_F33 :
    cvtS 2 f33_m3p5 = some (-3) ∧ cvtS 2 f33_3p5 = some 3 ∧ cvtS 2 f33_4 = none := by …
```

```lean
-- Toy/FloatTier/CastExamples.lean:22
theorem ex_cvtU_defined_F33 : cvtU 2 f33_3p5 = some 3 ∧ cvtU 2 f33_m0p5 = some 0 := by …
```

```lean
-- Toy/FloatTier/CastExamples.lean:25-27
theorem ex_cvtU_undefined_F33 :
    cvtU 2 f33_4 = none ∧ cvtU 2 (negOne F33) = none ∧ cvtU 2 (FP.nan : FP F33) = none ∧
      cvtU 2 (FP.inf false : FP F33) = none := by …
```

```lean
-- Toy/FloatTier/Examples.lean:112-115
theorem ex_fold_keeps_var :
    (FExpr.prim .add (.var 0) (.prim .mul (.lit (V.zero f false)) (.lit (.inf false)))).fold
        tierCtfe =
      .prim .add (.var 0) (.lit (V.prefNaN f false)) := by …
```

```lean
-- Toy/FloatTier/CastExamples.lean:65-68
theorem ex_inOpenS_F33 :
    InOpenS 2 f33_m3p5 ∧ InOpenS 2 f33_3p5 ∧ ¬ InOpenS 1 f33_m3p5 ∧ ¬ InOpenS 2 f33_4 ∧
      ¬ InOpenS 2 (FP.nan : FP F33) ∧ ¬ InOpenS 2 (FP.inf false : FP F33) ∧
      ¬ InOpenS 2 (FP.inf true : FP F33) := by …
```

```lean
-- Toy/FloatTier/CastExamples.lean:57-60
theorem ex_inOpenU_F33 :
    InOpenU 2 f33_3p5 ∧ InOpenU 2 f33_m0p5 ∧ ¬ InOpenU 2 f33_4 ∧ ¬ InOpenU 2 (negOne F33) ∧
      ¬ InOpenU 2 (FP.nan : FP F33) ∧ ¬ InOpenU 2 (FP.inf false : FP F33) ∧
      ¬ InOpenU 2 (FP.inf true : FP F33) := by …
```

```lean
-- Toy/FloatTier/Examples.lean:108-109
theorem ex_minMaxFree :
    (progCopysignNaN f).MinMaxFree = true ∧ (progMinZeroEq f).MinMaxFree = false := …
```

```lean
-- Toy/FloatTier/Examples.lean:57-58
theorem ex_nanChoice_extra_F23 :
    NaNChoice (fun _ _ k => k == 1) (V.zero F23 false) (V.inf false) (V.qnan true ⟨1, by decide⟩) := by …
```

```lean
-- Toy/FloatTier/Examples.lean:42-46
theorem ex_nanChoice_propagation_F23 :
    NaNChoice noExtra (V.snan false ⟨0, by decide⟩ : V F23) (V.one F23)
      (V.snan true ⟨0, by decide⟩) ∧
    NaNChoice noExtra (V.snan false ⟨0, by decide⟩ : V F23) (V.one F23)
      (V.qnan false ⟨1, by decide⟩) := by …
```

```lean
-- Toy/FloatTier/Examples.lean:51-54
theorem ex_nanChoice_rejects_F23 :
    ¬ NaNChoice noExtra (V.zero F23 false) (V.inf false) (V.snan false ⟨0, by decide⟩) ∧
    ¬ NaNChoice noExtra (V.zero F23 false) (V.inf false) (V.qnan false ⟨1, by decide⟩) ∧
    ¬ NaNChoice noExtra (V.zero F23 false) (V.inf false) (V.zero F23 false) := by …
```

```lean
-- Toy/FloatTier/CastExamples.lean:87
theorem ex_negOne_F33 : key (negOne F33) = -16 := by …
```

```lean
-- Toy/FloatTier/Examples.lean:21
theorem ex_no_snan_p2 (k : Fin (F32.payCount - 1)) : False := by …
```

```lean
-- Toy/FloatTier/Examples.lean:65-68
theorem ex_primSet_allows_F23 :
    primSet noExtra .min (V.zero F23 false) (V.zero F23 true) (V.zero F23 true) ∧
    primSet noExtra .min (V.zero F23 false) (V.zero F23 true) (V.zero F23 false) ∧
    primSet noExtra .mul (V.zero F23 false) (V.inf false) (V.prefNaN F23 true) := by …
```

```lean
-- Toy/FloatTier/Examples.lean:72-75
theorem ex_primSet_rejects_F23 :
    ¬ primSet noExtra .min (V.one F23) (V.prefNaN F23 false) (V.prefNaN F23 false) ∧
    ¬ primSet noExtra .add (V.inf false : V F23) (V.inf true) (V.inf false) ∧
    ¬ primSet noExtra .mul (V.one F23) (V.one F23) ((V.one F23).neg) := by …
```

```lean
-- Toy/FloatTier/CastExamples.lean:103-107
theorem ex_rangeCheckU_F33 :
    rangeCheckU f33_4 f33_3p5 = true ∧ rangeCheckU f33_4 f33_m0p5 = true ∧
      rangeCheckU f33_4 f33_4 = false ∧ rangeCheckU f33_4 (negOne F33) = false ∧
      rangeCheckU f33_4 (FP.nan : FP F33) = false ∧
      rangeCheckU f33_4 (FP.inf false : FP F33) = false := by …
```

```lean
-- Toy/FloatTier/CastExamples.lean:43-46
theorem ex_satS_F33 :
    satS 2 (FP.nan : FP F33) = 0 ∧ satS 2 (FP.inf false : FP F33) = 3 ∧
      satS 2 (FP.inf true : FP F33) = -4 ∧ satS 2 f33_m3p5 = -3 ∧ satS 2 f33_5 = 3 ∧
      satS 2 (FP.mk' F33 true 5 1) = -4 := by …
```

```lean
-- Toy/FloatTier/CastExamples.lean:36-39
theorem ex_satU_F33 :
    satU 2 (FP.nan : FP F33) = 0 ∧ satU 2 (FP.inf false : FP F33) = 3 ∧
      satU 2 (FP.inf true : FP F33) = 0 ∧ satU 2 f33_m3p5 = 0 ∧ satU 2 f33_3p5 = 3 ∧
      satU 2 f33_5 = 3 := by …
```

```lean
-- Toy/FloatTier/Examples.lean:17
theorem ex_snan_payload_F23 : (V.snan false ⟨0, by decide⟩ : V F23).payload = 1 := by …
```

```lean
-- Toy/FloatTier/Examples.lean:81-83
theorem ex_tierSound_F23 :
    TierSound (noExtra (f := F23)) tierCtfe ∧ TierSound (noExtra (f := F23)) tierRunA ∧
    ¬ TierSound (noExtra (f := F23)) tierBad := …
```

```lean
-- Toy/FloatTier/CastExamples.lean:17-18
theorem ex_trunc_F33 :
    trunc f33_3p5 = 3 ∧ trunc f33_m3p5 = -3 ∧ trunc f33_m0p5 = 0 := by …
```

```lean
-- Toy/FloatTier/CastExamples.lean:99
theorem ex_twoPowFits_binary32_32 : TwoPowFits Fbin32 32 := by …
```

```lean
-- Toy/FloatTier/CastExamples.lean:91
theorem ex_twoPowRound_fits_F33 : TwoPowFits F33 2 ∧ twoPowRound F33 2 = f33_4 := by …
```

```lean
-- Toy/FloatTier/CastExamples.lean:95-96
theorem ex_twoPowRound_overflow_F33 :
    ¬ TwoPowFits F33 4 ∧ twoPowRound F33 4 = .inf false := by …
```

```lean
-- Toy/FloatTier/Examples.lean:90-95
theorem ex_valEq_F23 :
    ValEq (V.zero F23 false) (V.zero F23 true) ∧
    ValEq (V.prefNaN F23 false) (V.snan true ⟨0, by decide⟩) ∧
    ¬ ValEq (V.inf false : V F23) (V.inf true) ∧
    ¬ ValEq (V.zero F23 false) (V.one F23) ∧
    ¬ ValEq (V.prefNaN F23 false) (V.inf false) := by …
```

In namespace `Fmt`: `Toy.FloatTier.Fmt.maxUnits`, a quantity computed from the format.

```lean
-- Toy/FloatTier/Base.lean:56
def maxUnits : Nat := (2 ^ f.p - 1) * 2 ^ (2 ^ f.e - 3)
```

```lean
-- Toy/FloatTier/Instances.lean:33
def f33_3p5 : FP F33 := FP.mk' F33 false 4 3
```

In namespace `FP`: `Toy.FloatTier.FP.isFinite`, on the NaN-collapsed view.

```lean
-- Toy/FloatTier/Base.lean:108-110
def isFinite : FP f → Bool
  | .fin .. => true
  | _ => false
```

```lean
-- Toy/FloatTier/Instances.lean:39
def f33_4 : FP F33 := FP.mk' F33 false 5 0
```

```lean
-- Toy/FloatTier/Instances.lean:41
def f33_5 : FP F33 := FP.mk' F33 false 5 1
```

```lean
-- Toy/FloatTier/Instances.lean:37
def f33_m0p5 : FP F33 := FP.mk' F33 true 2 0
```

```lean
-- Toy/FloatTier/Instances.lean:35
def f33_m3p5 : FP F33 := FP.mk' F33 true 4 3
```

In namespace `FP`: `Toy.FloatTier.FP.isNaN`, on the NaN-collapsed view (distinct from `V.isNaN` on payload-carrying values).

```lean
-- Toy/FloatTier/Base.lean:100-102
def isNaN : FP f → Bool
  | .nan => true
  | _ => false
```

```lean
-- Toy/FloatTier/Base.lean:258
def maxLt (x y : FP f) : FP f := if lt y x then x else y
```

```lean
-- Toy/FloatTier/Base.lean:269-270
def maximum (x y : FP f) : FP f :=
  if x.isNaN || y.isNaN then .nan else if totalKey y ≤ totalKey x then x else y
```

```lean
-- Toy/FloatTier/Base.lean:256
def minLt (x y : FP f) : FP f := if lt x y then x else y
```

```lean
-- Toy/FloatTier/Base.lean:265-266
def minimum (x y : FP f) : FP f :=
  if x.isNaN || y.isNaN then .nan else if totalKey x ≤ totalKey y then x else y
```

```lean
-- Toy/FloatTier/Examples.lean:37-38
theorem nanChoice_prefNaN (X : Extra f) (x y : V f) (s : Bool) :
    NaNChoice X x y (V.prefNaN f s) := …
```

In namespace `FP`: `Toy.FloatTier.FP.neg`, on the NaN-collapsed view (distinct from `V.neg` on payload-carrying values).

```lean
-- Toy/FloatTier/Base.lean:130-133
def neg : FP f → FP f
  | .nan => .nan
  | .inf s => .inf (!s)
  | .fin s E M => .fin (!s) E M
```

In namespace `ValEq`: `Toy.FloatTier.ValEq.refl`.

```lean
-- Toy/FloatTier/VLemmas.lean:64
theorem ValEq.refl (x : V f) : ValEq x x := …
```

In namespace `FP`: `Toy.FloatTier.FP.signBit`, on the NaN-collapsed view (distinct from `V.signBit` on payload-carrying values).

```lean
-- Toy/FloatTier/Base.lean:95-98
def signBit : FP f → Bool
  | .nan => false
  | .inf s => s
  | .fin s _ _ => s
```

```lean
-- Toy/FloatTier/Base.lean:261
def totalKey (x : FP f) : Int := 2 * key x + (if x = posZero f then 1 else 0)
```

```lean
-- Toy/FloatTier/Base.lean:138-139
def zero (f : Fmt) (neg : Bool) : FP f :=
  .fin neg ⟨0, f.expCount_pos⟩ ⟨0, f.fracCount_pos⟩
```

## Boundaries

### Non-claims (per result)

Read these before relying on a result. Each list states what the result does not show; the numbers and IDs are those of **Findings → Results**. Model–system relation: none proved; no result establishes or refutes a claim about a real system, and each list repeats the neither-establish-nor-refute wording for the systems that the result's prose mentions.

#### Non-claims of 1. `tier-refinement-iff-sound`

- `Tier f` is site-independent and context-free: the same primitive on the same operands gets the same result at every occurrence. `S` chooses independently at every node, and there is a program on which `S` allows an observation that no tier produces: for `copysign(1.0, 0.0 * +∞) == copysign(1.0, 0.0 * +∞)`, `S` allows `0` while every tier computes `1` (`exists_runS_not_realized_by_any_tier`). Implementations whose choices depend on the occurrence or the context are not tiers; RFC 3514 L130 allows two evaluations of the same expression during compile-time evaluation to give different results. This result neither establishes nor refutes the correctness of such implementations.
- Refinement is per expression tree: each primitive node chooses independently, and there is no sharing, `let`, memory, loop or concurrency. The RFC's "stable bit pattern" property of a value used twice (RFC 3514 L85) is not modelled.
- `S` has one rounding mode (round-to-nearest-ties-to-even) and no status flags, traps or alternative rounding modes; RFC 3514 L58 states the corresponding assumption for Rust.
- The operations modelled are `add`, `sub`, `mul`, `min`, `max`, the bit-level `neg`, `abs`, `copysign`, comparison, and a value-level branch. Division, `sqrt`, `mul_add`, `%` and float-to-float `as` casts (with their payload truncation and extension rules) are not modelled.
- `TierSound X τ` is relative to `X`. In a format with `p ≥ 3` it can depend on `X`: in `F23` the tier `tierExtraPay1` is sound for `extraPay1` (payload `1` allowed) and not for `noExtra` (`tierExtraPay1_sound_extra_not_noExtra`). In every format with `p = 2` there is exactly one NaN payload, and `TierSound X τ ↔ TierSound noExtra τ` for every `X` and `τ` (`tierSound_extra_irrelevant_of_p_eq_two`); so the statement "a tier that uses extra payloads is sound for an `X` containing them and not for `noExtra`" is false in `F32` (`refuted_extra_payload_tier_separates_noExtra_p2`).
- `RefinesS` compares full bit patterns. A tier whose results agree with those of a sound tier up to `ValEq` need not be sound; by definition `tierExtraPay1` differs from `tierCtfe` in NaN payloads and nowhere else and is not sound for `noExtra` (`tierExtraPay1_sound_extra_not_noExtra`; agreement up to `ValEq` on every expression is not proved here).
- Policy tiers never use extra payloads or unchanged propagation, give every NaN result the same sign, and, when they propagate, copy the payload of the first NaN operand. So there are sound tiers that are not policy tiers, for example a sound tier that copies the sign of a NaN operand (not proved here); the general characterization above covers every tier.
- Refinement of `S` is not equality between tiers (`sound-tiers-disagree-under-bit-observation`).
- Nothing here says which tier any real compiler, interpreter or target implements. Model–system relation: none proved; the statements neither establish nor refute the corresponding claims about Rust, LLVM or IEEE 754 implementations.

#### Non-claims of 2. `sound-tiers-disagree-under-bit-observation`

- It shows one disagreement, in the sign bit. Payload disagreements between sound tiers are possible in formats with `p ≥ 3` (not proved here).
- For value-level observations the situation depends on the program. `isNaN (0.0 * +∞)` gives `1` under both tiers (`tiers_agree_on_isNaN_zero_mul_inf`), and any two sound tiers agree on every program that satisfies `BitSafe X ρ V.isNaNOrZero` (`observation-determinism-nan-or-zero`). Without that hypothesis value-level observations can disagree as well: `0.0 < copysign(1.0, 0.0 * +∞)` gives `1` under `tierCtfe` and `0` under `tierRunA` (`copysign-of-nan-breaks-determinism`), so the unqualified statement "value-level observations of the two tiers agree" is false (`refuted_value_level_observations_of_sound_tiers_agree`).
- The theorem concerns the two toy tiers `tierCtfe` and `tierRunA`. It does not say that every pair of a compile-time tier and a run-time tier disagrees; for example a tier agrees with itself.
- It does not show that any real compiler or target produces different bits; that was not examined, and no programs were run. Model–system relation: none proved; it neither establishes nor refutes the corresponding claim about Rust compile-time evaluation or any target.

#### Non-claims of 3. `sound-tier-constant-folding-refines-spec`

- The conclusion is refinement (inclusion of observation sets), not equality: there is a program, `toBits (0.0 * +∞)`, for which `S` allows the original program an observation that it does not allow the folded program (`runS_of_runS_fold_nonvacuous`).
- `hτ` must hold for the same extra-payload set `X` as the semantics `runS X`. Folding with a tier that is sound for a different extra-payload set, for example that of the compiling host rather than the target, is not covered.
- `hτ` is tight over all programs; for a particular program a weaker condition on `τ` can suffice, for example when the program has no closed NaN-producing or `min`/`max` subexpression (not proved here).
- `S` has one rounding mode, no status flags or traps, no undefined behaviour and no divergence, and `FExpr.fold` also folds closed subexpressions in `selLt` branches that no execution takes. In a language with traps, undefined behaviour or alternative rounding modes such eager folding is not justified by this theorem (not proved here); RFC 3514 L58 and L143 describe the corresponding assumptions for Rust.
- The theorem covers folding of closed subexpressions of expression trees. Common-subexpression elimination, duplication of NaN-producing subexpressions and other rewrites are not examined. In a language with shared bindings, folding one use of a NaN-producing binding while evaluating another use at run time could break the stable-bit-pattern property of RFC 3514 L85 (not proved here).
- It does not say that the folded program behaves like the unfolded program under any particular run-time tier (`ctfe-folding-not-preserved-by-run-tier`).
- Model–system relation: none proved; it neither establishes nor refutes the corresponding claim about Rust or LLVM constant folding.

#### Non-claims of 4. `ctfe-folding-not-preserved-by-run-tier`

- It does not show that folding is incorrect: against `S` it is correct (`sound-tier-constant-folding-refines-spec`).
- It concerns `tierRunA`, a toy tier, not any real target. Model–system relation: none proved; it neither establishes nor refutes the corresponding claim about any compiler or target.

#### Non-claims of 5. `observation-determinism-nan-or-zero`

- The hypothesis quantifies over all executions of `S` from the given input, not over what some tier or real target produces.
- It is a sufficient condition (`bitSafe_not_necessary`). In addition, bit-level uses of zeros produced by `add`, `sub` or `mul` are deterministic in the toy (`observation-determinism-minmax-free` covers programs without `min`/`max`), so excluding zeros is stronger than needed for such programs.
- The conclusion is per input and per single observation. It is not an IEEE-conformance claim: signaling-NaN outputs remain possible in `S` and are invisible to the observations.
- The language has no division, `sqrt`, `mul_add`, `signum`, total-order comparison or byte conversion. An operation that exposes the sign of a zero at the value level, such as division (`1 / ±0 = ±∞`), would require a new statement; with division this theorem as stated would fail (not proved here).
- `minSet` and `maxSet` model the `min`/`max` documented for Rust `f32::min`/`f32::max`, which may return either operand when the operands compare equal. Operations that order `-0.0` below `+0.0` (Rust `f32::minimum`, LLVM `llvm.minimum`) or return a quiet NaN on a signaling-NaN operand (LLVM `llvm.minnum`) are not modelled (**Findings → Modelling bridges**).
- Model–system relation: none proved; the statement neither establishes nor refutes the corresponding claim about Rust, LLVM or IEEE 754 implementations.

#### Non-claims of 6. `observation-determinism-minmax-free`

- It does not cover `min`/`max` (`minZeroSign_breaks_determinism`).
- The pair of hypotheses `P.MinMaxFree = true` and `P.BitSafe X ρ V.isNaN` is a sufficient condition for determinism, not a necessary one. The two programs of `bitSafe_not_necessary`, `signBit (abs (0.0 * +∞))` and `toBits` of a NaN literal, are `min`/`max`-free, violate `P.BitSafe X ρ V.isNaN`, and have exactly one allowed observation each; and the program `min(+0.0, -0.0) == +0.0` violates `P.MinMaxFree = true` (`ex_minMaxFree`) and has exactly one allowed observation (`progMinZeroEq_nonvacuous`).
- It does not say that NaN payloads or signs are deterministic. They are not (`sound-tiers-disagree-under-bit-observation`); under the hypotheses they are unobservable.
- NaN literals, including signaling NaNs, are allowed. They do not break determinism here because no operation of the toy distinguishes a signaling NaN from a quiet one. In a language with an operation whose non-NaN result depends on whether an operand is signaling (RFC 3514 L222–224 gives C `pow` as an example; LLVM `llvm.minnum` returns a quiet NaN when an operand is signaling; see **Findings → Modelling bridges**), a NaN built from bits could make value-level results nondeterministic without any bit-level use (not proved here). The toy says nothing about the IEEE-conformance part of RFC 3514 L33.
- The exclusion concerns `minSet`/`maxSet`. Operations that order `-0.0` below `+0.0`, such as Rust `f32::minimum` and LLVM `llvm.minimum` (**Findings → Modelling bridges**), are not modelled; this result neither establishes nor refutes determinism for programs that use them.
- Model–system relation: none proved; the statement neither establishes nor refutes the corresponding claim about Rust, LLVM or IEEE 754 implementations.

#### Non-claims of 7. `min-zero-deterministic-up-to-eq-not-under-sign-test`

- The theorems state `min` on `(+0, -0)`; `max` on `(+0, -0)` is analogous in the model (not proved here).
- Apart from operands that compare equal and from NaN results when both operands are NaN, `minSet` and `maxSet` allow no other choice (not proved here).
- Value-level determinism of `min(+0.0, -0.0) == +0.0` holds in the toy because the language has no value-level operation that distinguishes `+0` from `-0`, such as division (not proved here).
- The nondeterminism is that of `minSet`/`maxSet`, which follow Rust `f32::min`. Rust `f32::minimum` and LLVM `llvm.minimum` are documented to order `-0.0` below `+0.0` (**Findings → Modelling bridges**); they are not modelled.
- Model–system relation: none proved; the statement neither establishes nor refutes the corresponding claim about Rust's `f32::min` or any target.

#### Non-claims of 8. `copysign-of-nan-breaks-determinism`

- One program. `toBits` on a NaN is `sound-tiers-disagree-under-bit-observation`; `signBit` on a NaN is not stated separately.
- `copysign` with a NaN magnitude and a sign argument that is never a NaN does not break determinism (`observation-determinism-minmax-free` covers it).
- Other bit-observing operations of real systems (total-order comparison, byte conversions, sign tests) are not modelled. Model–system relation: none proved; the statement neither establishes nor refutes the corresponding claim about Rust's `copysign` or any target.

#### Non-claims of 9. `trunc-unsigned-open-interval`

- `trunc` truncates toward zero. It is not floor (`trunc (-3.5) = -3`, `ex_trunc_F33`).
- The degenerate width `W = 0` is covered: range `[0, 0]`, interval `(−1, 1)`.
- On NaN and `±∞` the equivalence fails (`trunc_mem_range_iff_fails_at_inf`); `trunc` is `0` there (`trunc_uval_of_not_finite`) and `InOpenU` is false (`not_inOpen_of_not_finite`).
- This is about exact values in the toy; conversion instructions of real hardware are not examined. Model–system relation: none proved; it neither establishes nor refutes the corresponding claim about Rust, LLVM or any hardware conversion.

#### Non-claims of 10. `trunc-signed-open-interval`

- Signed widths are written `k + 1`; there is no signed width 0. For a signed width `W ≥ 1` the interval `−2^(W−1) − 1 < x < 2^(W−1)` is this statement with `k = W − 1`.
- The lower endpoint `−2^k − 1` need not be representable. No floating-point range check for signed targets is characterized; two natural candidates are not exact in `F33` (`signed_lower_guards_not_exact_F33`, see `two-comparison-range-check-exact`).
- Model–system relation: none proved; it neither establishes nor refutes the corresponding claim about Rust, LLVM or any hardware conversion.

#### Non-claims of 11. `unchecked-conversion-undefined-iff`

- `none` stands for both undefined behaviour (Rust `to_int_unchecked`) and a poison result (LLVM `fptoui`/`fptosi`); the model does not distinguish them. Poison semantics is covered by the published package `undefined-values-poison-undef-freeze-and-refinement`, cited and not repeated.
- The IEEE 754 invalid-operation exception and the concrete results that hardware conversion instructions return for out-of-range inputs are not modelled.
- No statement about how compilers lower these conversions. Model–system relation: none proved; it neither establishes nor refutes the corresponding claim about Rust, LLVM or WebAssembly implementations.

#### Non-claims of 12. `two-comparison-range-check-exact`

- Unsigned targets. A signed range check is not characterized, and two natural signed analogues are not exact: in `F33`, the strict lower bound `x > (−2^3 − 1 as float)` rejects `x = −8.0` because `−9` rounds to `−8.0`, and the bound `x >= −2^1` rejects `x = −2.5`, although `cvtS 3 (−8.0)` and `cvtS 1 (−2.5)` are defined (`signed_lower_guards_not_exact_F33`). Bounded evaluation in `F33` found the strict variant exact for `k ∈ {0, 1, 2, 4, 5, 6, 7}` and inexact at `k = 3` (evaluated, not proved).
- The comparisons are IEEE quiet `<` in the same format: a comparison with a NaN is false, and `+∞ < +∞` is false. Under assumptions that let a compiler treat NaN or infinite operands as impossible (for example LLVM's `nnan`/`ninf` fast-math flags, which the published float-laws package covers), the comparisons may be simplified and the guard need not reject NaN or `+∞` (not proved here).
- `c` is the mathematical integer `2^W` rounded once to the format. Computing `2^W` first in a fixed-width integer type, where it wraps or overflows (for example `1 << 32` in a 32-bit type), gives a different guard and is not examined. Evaluation of the comparison in a wider intermediate precision is not modelled.
- Other rounding modes are not modelled. It does not describe how any compiler implements checked or saturating conversions. Model–system relation: none proved; it neither establishes nor refutes the corresponding claim about any language or compiler.

#### Non-claims of 13. `max-as-float-guard-not-exact`

- Apart from `F23`, these are instances, not a statement about every format. Bounded evaluation for `W < 12` (in `checks/BoundedChecks.lean`; evaluated, not proved) found the guard exact at `W = p` and inexact at every other tested width in the formats `(e, p) = (3, 3)`, `(3, 2)`, `(3, 4)`, and inexact at every tested width in `(2, 3)`. Exactness at `W = p` does not hold in every format: in `F23` the guard is inexact at `W = p = 3` (`naiveCheckU_accepts_inf_F23_3`, `refuted_naiveCheckU_exact_at_W_eq_p`) and at every width (`naiveCheckU_inexact_every_width_F23`).
- Nothing is claimed about real programs or compilers that use such guards. Model–system relation: none proved; it neither establishes nor refutes the corresponding claim about any language or compiler.

#### Non-claims of 14. `saturating-conversion-saturates-and-agrees`

- The two conversions agree exactly on the inputs where the unchecked conversion is defined (the agreement conjunct); on the other inputs the unchecked conversion has no value. On inputs that fail the guard of `two-comparison-range-check-exact` the unchecked unsigned conversion is undefined (`unchecked-conversion-undefined-iff`), so replacing a saturating unsigned conversion by an unchecked one preserves results exactly on the inputs that pass that guard.
- `satU` and `satS` operate on the NaN-collapsed view `FP f`; the sign, quiet bit and payload of a NaN do not affect the result.
- The degenerate widths are covered by the same statements. At `W = 0` the unsigned range is `[0, 0]` and `satU 0` returns `0` on every input, including `+∞` (`satU_width_zero`). At `k = 0` (signed width `k + 1 = 1`) the signed range is `[−1, 0]`: by `satS_saturates_and_agrees` at `k = 0`, `+∞` and every finite `x` with exact value at least `1` give `0 = 2^0 − 1`, and `−∞` and every finite `x` with exact value at most `−2` give `−1 = −2^0` (the theorem states these two antecedents on `uval`). Both ranges are computed in `Int`, so `2 ^ W - 1` and `2 ^ k - 1` involve no truncated subtraction.
- No statement about real compilers' lowering of `as` or of saturating intrinsics. Model–system relation: none proved; it neither establishes nor refutes the corresponding claim about Rust, LLVM or WebAssembly implementations.

### Escape hatches

No result of this package is an impossibility result. Each negative result is a counterexample that depends on a feature of the model; a nearby setting without that feature is a proved positive control:

- `sound-tiers-disagree-under-bit-observation` and `copysign-of-nan-breaks-determinism` depend on a bit-level use (`toBits`, or the sign argument of `copysign`) receiving a NaN. With the value-level observation `isNaN (0.0 * +∞)` the two tiers agree (`tiers_agree_on_isNaN_zero_mul_inf`), and for every input `ρ` and program that satisfy the hypotheses of `observation-determinism-nan-or-zero`, or those of `observation-determinism-minmax-free`, any two tiers that are sound for `X` compute the same observation.
- `min-zero-deterministic-up-to-eq-not-under-sign-test` depends on `minSet` allowing either zero and on a bit-level use of the result. The value-level observation `min(+0.0, -0.0) == +0.0` is deterministic (`progMinZeroEq_nonvacuous`).
- `ctfe-folding-not-preserved-by-run-tier` depends on judging the fold against the fixed run-time tier `tierRunA` instead of against `S`. Against `S` the fold is a refinement (`sound-tier-constant-folding-refines-spec`), and for the NaN-free program `toBits (copysign (var 0) (+∞ * -∞))` the fold does not change the observation computed by `tierRunA` (`fold_tierCtfe_preserves_tierRunA_nan_free`).
- `max-as-float-guard-not-exact` depends on rounding `2^W − 1` to the format. The guard `rangeCheckU (twoPowRound f W)` is exact in every format and at every width (`two-comparison-range-check-exact`).

For the theorems and characterizations, dropping a hypothesis marked `tight` defeats the conclusion within the class recorded in its ledger: `hτ` of `sound-tier-constant-folding-refines-spec`; the NaN part and the zero part of `hsafe` and the tier hypotheses `h₁`, `h₂` of `observation-determinism-nan-or-zero`; `hmm`, `hsafe` and `h₁`, `h₂` of `observation-determinism-minmax-free`; and `hx` of `trunc-unsigned-open-interval` and of `trunc-signed-open-interval`.

### Hypotheses with `unknown` tightness

None: every hypothesis-ledger entry is `tight`. The format invariants `2 ≤ e` and `2 ≤ p` are fields of `Fmt`, not hypotheses of any theorem; formats that violate them are outside the model and were not examined.

### Stronger or adjacent statements not established here

- "Any two sound tiers compute the same observations." Refuted for bit-level observations (`sound_tiers_disagree_on_bits`) and, through the sign argument of `copysign`, for value-level observations (`copysignNaN_breaks_determinism`, `refuted_value_level_observations_of_sound_tiers_agree`).
- "The hypotheses of the determinism theorems are necessary." Not established, and refuted for particular programs: there are programs that violate them and have exactly one allowed observation (`bitSafe_not_necessary`, `progMinZeroEq_nonvacuous`).
- "Excluding NaNs from bit-level uses suffices in the presence of `min`/`max`." Refuted (`minZeroSign_breaks_determinism`).
- "Tier soundness does not depend on the extra-payload set." Refuted in `F23` (`tierExtraPay1_sound_extra_not_noExtra`); in every format with `p = 2` it holds (`tierSound_extra_irrelevant_of_p_eq_two`).
- "Every sound tier is a policy tier," and "sound tiers can disagree in NaN payloads when `p ≥ 3`": neither is stated as a theorem in this package (not proved either way here).
- "A signed range check analogous to `rangeCheckU` is exact." Not characterized. Two natural candidates fail at concrete instances in `F33`: the strict lower bound at `k = 3` and the non-strict bound `x >= −2^1` at `k = 1` (`signed_lower_guards_not_exact_F33`). These are instances, not a statement about other widths or formats; bounded evaluation of the strict candidate at other `k` in `F33` is evaluated, not proved.
- "The guard `naiveCheckU W` is exact when `W` equals the precision `p`." Refuted in `F23` (`refuted_naiveCheckU_exact_at_W_eq_p`); the bounded evaluations in other formats are evaluated, not proved.
- Determinism in a language with division, `llvm.minimum`-style `min`/`max`, signaling-sensitive operations, shared bindings or traps: not examined (not proved either way).
- Anything about real compilers, interpreters or hardware: not examined. Model–system relation: none proved; these statements neither establish nor refute the corresponding claims about Rust, LLVM, WebAssembly, CompCert or IEEE 754 implementations.

### Disproved candidate statements

Three candidate statements considered before the statements above were fixed turned out to be false. Each refutation is a kernel-checked theorem, quoted under **Findings → Auxiliary lemmas cited by name**; none of the three is a result of this package.

- Refutation of the earlier candidate statement "the value-level observations of the two sound tiers `tierCtfe` and `tierRunA` agree on every program": `refuted_value_level_observations_of_sound_tiers_agree` proves, in every format and for every input, that not every comparison program `Prog.lt a b` gets the same observation from both tiers. Counterexample: `0.0 < copysign(1.0, 0.0 * +∞)`, which gives `1` under `tierCtfe` and `0` under `tierRunA` (`copysignNaN_breaks_determinism`).
- Refutation of the earlier candidate statement "a tier that uses an extra payload is sound for an extra-payload set containing it and not for `noExtra`", read as holding in every format: `refuted_extra_payload_tier_separates_noExtra_p2` proves that in `F32` (`p = 2`) there is no extra-payload set `X` and tier `τ` with `TierSound X τ` and `¬ TierSound noExtra τ`. The statement holds in `F23` (`tierExtraPay1_sound_extra_not_noExtra`).
- Refutation of the earlier candidate statement "the guard `naiveCheckU W` is exact at `W = p`": `refuted_naiveCheckU_exact_at_W_eq_p` proves that in `F23`, where `p = 3`, `naiveCheckU 3` disagrees with definedness of `cvtU 3` on some value. Counterexample: `+∞`, accepted by the guard (`naiveCheckU_accepts_inf_F23_3`).

## Evidence

### Kernel-check record

- Build: `lake build` of the library `Toy` under `leanprover/lean4:v4.34.1`, from a clean copy of `lean/` with Lake's artifact cache disabled, finishes without errors or warnings. Lean sources contain no `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `implemented_by`, `extern` or `unsafe`. The concrete binary32 instances are proved with `decide +kernel`.
- Axioms: `Lean.collectAxioms` over all 829 declarations of the library reports, for each, a subset of `propext`, `Classical.choice`, `Quot.sound` (recorded per declaration in `audit/axioms.json`).
- Hashes: for each of the 221 declarations named in the structured fields of `results.json` (results, declarations cited by name, non-vacuity witnesses, positive controls, counterexamples), `audit/statements.json` records the SHA-256 of the statement (the Lean `repr` of the declaration's type) and the SHA-256 of its definition closure: the sorted, newline-joined list of entries `name : repr(type)`, followed by ` := repr(value)` for non-theorems, for every package-local constant reachable from the statement through types, non-theorem values and inductive constructors (theorem bodies excluded). `support/revalidate.py` recomputes both.

The table lists every recorded declaration (namespace prefix `Toy.FloatTier.` omitted) with its kind, its source location relative to `lean/`, the axioms reported for it, and the two hashes as recorded in `audit/statements.json`.

| Declaration | Kind | Source | Axioms | Statement SHA-256 | Closure SHA-256 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `ChoicePolicy` | structure | `Toy/FloatTier/Sets.lean:107` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `DetCongr` | structure | `Toy/FloatTier/Determinism.lean:26` | `Quot.sound`, `propext` | `c1fb45aa583d3e002a6f57588e31c7877a4e82edde89d8ce7c88abd7bacee204` | `78b3c5e60621348fe301e477c75b855b1016d6ac6f0ffa133dc6cd68bfec71a0` |
| `EqNsz` | def | `Toy/FloatTier/Base.lean:276` | `Quot.sound`, `propext` | `b773e9e06232607eef782aa3eccfdb255496fad273d268665cbe5bf13fdceb54` | `69ba67611a67ee13cc743846c8b9325c95fee5e73405e307ae4e8102118353fb` |
| `Extra` | abbrev | `Toy/FloatTier/Sets.lean:38` | none | `1452f8536a7f47da9663e8efd7b5bdcdb40dd4ff25206e8f67a356ee015fb665` | `96b2118ac0d27f7d519d8b3b6ff3fde7da1c469d47c20dcd18a25217a32ee48f` |
| `F23` | def | `Toy/FloatTier/Instances.lean:22` | none | `685909396163a9ba308c17d55d7e5b277ae01aea102cd545c3230bcb9640ff37` | `96b2118ac0d27f7d519d8b3b6ff3fde7da1c469d47c20dcd18a25217a32ee48f` |
| `F32` | def | `Toy/FloatTier/Instances.lean:19` | none | `685909396163a9ba308c17d55d7e5b277ae01aea102cd545c3230bcb9640ff37` | `96b2118ac0d27f7d519d8b3b6ff3fde7da1c469d47c20dcd18a25217a32ee48f` |
| `F33` | def | `Toy/FloatTier/Instances.lean:16` | none | `685909396163a9ba308c17d55d7e5b277ae01aea102cd545c3230bcb9640ff37` | `96b2118ac0d27f7d519d8b3b6ff3fde7da1c469d47c20dcd18a25217a32ee48f` |
| `FExpr` | inductive | `Toy/FloatTier/Lang.lean:35` | none | `1452f8536a7f47da9663e8efd7b5bdcdb40dd4ff25206e8f67a356ee015fb665` | `96b2118ac0d27f7d519d8b3b6ff3fde7da1c469d47c20dcd18a25217a32ee48f` |
| `FExpr.BitSafe` | def | `Toy/FloatTier/Lang.lean:109` | `Quot.sound`, `propext` | `1900ff2427e412d01277a709cbcd048424446f111bafec227ea6964892f98db4` | `b8b3f70edb2943389d962957ce889a02765e073610275783209fe1db967462aa` |
| `FExpr.PrimsOk` | def | `Toy/FloatTier/Lang.lean:124` | none | `c8c8054bd469a689c1ae7d67c90f34675cfe25365cc5bb6b51ab1d417a41be2d` | `9a4401676ef67ebd09f097e51c2f492c4a30fc5933684d333630a6eeff8e44aa` |
| `FExpr.closed` | def | `Toy/FloatTier/Lang.lean:81` | none | `f72ae09485fe6045728e7b5750576b4da6dc37936d0ac0a7c0b0bcad5720e784` | `9a4401676ef67ebd09f097e51c2f492c4a30fc5933684d333630a6eeff8e44aa` |
| `FExpr.evalS` | def | `Toy/FloatTier/Lang.lean:58` | `Quot.sound`, `propext` | `64df18875c02cddf9126bc66303b58c7806669fb00f38cdc185a3645cfd51666` | `b8b3f70edb2943389d962957ce889a02765e073610275783209fe1db967462aa` |
| `FExpr.evalS_evalT_of_tierSound` | theorem | `Toy/FloatTier/Statements.lean:21` | `Quot.sound`, `propext` | `e7790d253de806def2bc79bf9e0249d5754aaaaf802c35904a01ec861441c880` | `895e85f90eb7373a02df747648d796ebfd9cdd0810af6b0d9ddb5f57531d03b7` |
| `FExpr.evalS_of_evalS_fold` | theorem | `Toy/FloatTier/Statements.lean:180` | `Quot.sound`, `propext` | `29e744bebfe68cfcf74237a61641efba0b8ef7f141a9d419a4a338aba3623b8d` | `7103414412955db9181d1bc1ab84d73589724f0f9dae8596d851519b81d4b0e3` |
| `FExpr.evalS_rel_of_bitSafe` | theorem | `Toy/FloatTier/Determinism.lean:41` | `Quot.sound`, `propext` | `5236274f84633479844f6b4db8f5dee2ae8b40a88f364eda3f226ab43d9381ec` | `aacdecac2b2018e95de19840fbda4fee909450869bdb2cbdfac3e1982fded56d` |
| `FExpr.evalT` | def | `Toy/FloatTier/Lang.lean:69` | `propext` | `3320677cc03964d453c9337215807a34a27beabe77f3bd584560b052d10c0c46` | `569975ee8077d4f973a20d8ee15f0c849fe121cb58c6505be5388f1da0fe98ab` |
| `FExpr.evalT_of_closed` | theorem | `Toy/FloatTier/Statements.lean:163` | `propext` | `c3a1d220d8be6323b8027775a24590a667c929e2f8e995279a13dbc105a75ff9` | `dd34be805b6abd98418aec37a506b676a19fc3b5b71e52763ec354501e74ff51` |
| `FExpr.fold` | def | `Toy/FloatTier/Lang.lean:93` | `propext` | `2d39596425c4df64c68ec20bf2c81ff5b38969fb94c689708b1b557322be9c01` | `569975ee8077d4f973a20d8ee15f0c849fe121cb58c6505be5388f1da0fe98ab` |
| `FP` | inductive | `Toy/FloatTier/Base.lean:74` | none | `1452f8536a7f47da9663e8efd7b5bdcdb40dd4ff25206e8f67a356ee015fb665` | `96b2118ac0d27f7d519d8b3b6ff3fde7da1c469d47c20dcd18a25217a32ee48f` |
| `FP.bits` | def | `Toy/FloatTier/Base.lean:124` | none | `5c294e4d2c31f52e06625db160cf967b937ca802cd5f4506caedcd9f732817ca` | `69ba67611a67ee13cc743846c8b9325c95fee5e73405e307ae4e8102118353fb` |
| `FP.isFinite` | def | `Toy/FloatTier/Base.lean:108` | `propext` | `b37b7c7cdc6ff1ec52d31fb5a655e0790b1309a03c4d81fe265a5cdfa2c63cfb` | `69ba67611a67ee13cc743846c8b9325c95fee5e73405e307ae4e8102118353fb` |
| `FP.isNaN` | def | `Toy/FloatTier/Base.lean:100` | `propext` | `b37b7c7cdc6ff1ec52d31fb5a655e0790b1309a03c4d81fe265a5cdfa2c63cfb` | `69ba67611a67ee13cc743846c8b9325c95fee5e73405e307ae4e8102118353fb` |
| `FP.mk'` | def | `Toy/FloatTier/Instances.lean:29` | none | `e4810e316b192e5d5a94a8710ed037067a078e36786c4f5d71f56d9ef434783b` | `19975a350a24662cb6095e0bd68e2715d0673bc4f612d007cf3ef6a2ea69e236` |
| `FP.neg` | def | `Toy/FloatTier/Base.lean:130` | none | `43d195db57d3ca9b751ab22f49e104f341a1696c3bf78914257312d5faf932aa` | `69ba67611a67ee13cc743846c8b9325c95fee5e73405e307ae4e8102118353fb` |
| `FP.signBit` | def | `Toy/FloatTier/Base.lean:95` | none | `b37b7c7cdc6ff1ec52d31fb5a655e0790b1309a03c4d81fe265a5cdfa2c63cfb` | `69ba67611a67ee13cc743846c8b9325c95fee5e73405e307ae4e8102118353fb` |
| `FP.uval` | def | `Toy/FloatTier/Cast.lean:36` | `propext` | `0e6b49e828afd5d7c45cb989d4124f15efcccf55e1bd9c9513a7da237fa8a3b2` | `69ba67611a67ee13cc743846c8b9325c95fee5e73405e307ae4e8102118353fb` |
| `Fbin32` | def | `Toy/FloatTier/Cast.lean:107` | none | `685909396163a9ba308c17d55d7e5b277ae01aea102cd545c3230bcb9640ff37` | `96b2118ac0d27f7d519d8b3b6ff3fde7da1c469d47c20dcd18a25217a32ee48f` |
| `Fmt` | structure | `Toy/FloatTier/Base.lean:31` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Fmt.bias` | def | `Toy/FloatTier/Base.lean:42` | none | `4d022eef4ccb9bcaba458f8bb6c68004198497216c311102670d23d729b8e8af` | `96b2118ac0d27f7d519d8b3b6ff3fde7da1c469d47c20dcd18a25217a32ee48f` |
| `Fmt.maxUnits` | def | `Toy/FloatTier/Base.lean:56` | none | `4d022eef4ccb9bcaba458f8bb6c68004198497216c311102670d23d729b8e8af` | `96b2118ac0d27f7d519d8b3b6ff3fde7da1c469d47c20dcd18a25217a32ee48f` |
| `Fmt.qneg` | def | `Toy/FloatTier/Base.lean:53` | none | `4d022eef4ccb9bcaba458f8bb6c68004198497216c311102670d23d729b8e8af` | `96b2118ac0d27f7d519d8b3b6ff3fde7da1c469d47c20dcd18a25217a32ee48f` |
| `InOpenS` | def | `Toy/FloatTier/Cast.lean:50` | `propext` | `eef78787cac964ed1eaa376760174499e41cf4913974bf4ccc808e955e169531` | `69ba67611a67ee13cc743846c8b9325c95fee5e73405e307ae4e8102118353fb` |
| `InOpenU` | def | `Toy/FloatTier/Cast.lean:44` | `propext` | `8fc09949fac7a3235841f8d96ab0019d6f834818f04a49316a6a4d3797bc47f0` | `69ba67611a67ee13cc743846c8b9325c95fee5e73405e307ae4e8102118353fb` |
| `NaNChoice` | def | `Toy/FloatTier/Sets.lean:49` | `propext` | `d7a03a1d9f2635b8d1f63f2229e44307e2dc40fe78a518afe577144bd663f52e` | `19e76218d8cba1867fd412f90f6ee3e0a031915f46fe69893de79d67c7b97392` |
| `Prim` | inductive | `Toy/FloatTier/Sets.lean:60` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `Prim.isArith` | def | `Toy/FloatTier/Lang.lean:136` | none | `12c9c402afcae592265bfaacd24e772a986d9177f176a5018cf1f7a4e0a4b0ea` | `e8a3c95aa52a3543f6c366c2b26d116e7e2bc96e869779f4fa8272a1bdba883b` |
| `Prog` | inductive | `Toy/FloatTier/Lang.lean:46` | none | `1452f8536a7f47da9663e8efd7b5bdcdb40dd4ff25206e8f67a356ee015fb665` | `96b2118ac0d27f7d519d8b3b6ff3fde7da1c469d47c20dcd18a25217a32ee48f` |
| `Prog.BitSafe` | def | `Toy/FloatTier/Lang.lean:173` | `Quot.sound`, `propext` | `3d1a35405b167e53ea764d412272dfe67b557ef35264d6edc1f977690c959a71` | `2c78df7d079a5462b00bafce9340279367be7baaac0c6fb902b5be69229f0527` |
| `Prog.MinMaxFree` | def | `Toy/FloatTier/Lang.lean:189` | none | `08c913feae7f4ea1e3053c860551cef617e90609885f897b6f0dbfba6d04c729` | `36ba23a4291bf7bee44419caa9295f5811053b67c522df3393b7e20908b50c4d` |
| `Prog.PrimsOk` | def | `Toy/FloatTier/Lang.lean:181` | none | `33c5ca710d06537435ce5aa9efafac74a3cfeaabcc7690e5c2cf9eb46da1ae06` | `36ba23a4291bf7bee44419caa9295f5811053b67c522df3393b7e20908b50c4d` |
| `Prog.fold` | def | `Toy/FloatTier/Lang.lean:163` | `propext` | `a5fa2362d1afbf442c0ddc1c7a2054b72d7ce73dec2fb1f45492c3820da6f190` | `b4ad4619ead965d19d749406ced14c17be300749bb65a5c141b42ebcf70a65f6` |
| `Prog.refinesS_iff_tierSound` | theorem | `Toy/FloatTier/Statements.lean:67` | `Quot.sound`, `propext` | `562d6b923328fc65cda6abb7c1bc8bf18c3212f2cfc8273bae110065e0f7dc96` | `128d27cde38261b4b5d7a050d7a8097637270aa5168f429c908d5d28178a2d28` |
| `Prog.runS` | def | `Toy/FloatTier/Lang.lean:146` | `Quot.sound`, `propext` | `07d510703f1d7bb85014f229d48e56f5900f2246c27843906b621b73420fa5dd` | `2c78df7d079a5462b00bafce9340279367be7baaac0c6fb902b5be69229f0527` |
| `Prog.runS_of_runS_fold` | theorem | `Toy/FloatTier/Statements.lean:239` | `Quot.sound`, `propext` | `a16403d7b0639923b208a63d6364f94793d9d45217b23f3a75f2f658300da0e9` | `676d0aeb4c5bb369ad758e6f9ecd3af1fb2be76e536c8e75ff8c2b1cc8fe60d6` |
| `Prog.runS_runT_of_tierSound` | theorem | `Toy/FloatTier/Statements.lean:52` | `Quot.sound`, `propext` | `5d8152116081f79552a79230a300255423c01dc9415c1b551afe128a043a00d6` | `128d27cde38261b4b5d7a050d7a8097637270aa5168f429c908d5d28178a2d28` |
| `Prog.runS_unique_of_bitSafe_nanOrZero` | theorem | `Toy/FloatTier/Determinism.lean:155` | `Classical.choice`, `Quot.sound`, `propext` | `672779b6fe298cebdfd17eacb46b108dfb46d66f335a06d98d12b2f92b7d5f5c` | `537268344ccb697d88807b80019801d9642bfff210e744a1522c22320a6fd826` |
| `Prog.runS_unique_of_detCongr` | theorem | `Toy/FloatTier/Determinism.lean:88` | `Quot.sound`, `propext` | `b803a71f7abd888888d6b81720fc5f3e5b3c59287ac1e0ddb9d25913190a6c38` | `33799502cc5eae2d87660cd3088a0440ea5cc30ee602aa909f030ce650b8123c` |
| `Prog.runS_unique_of_minMaxFree_of_bitSafe_nan` | theorem | `Toy/FloatTier/Determinism.lean:174` | `Quot.sound`, `propext` | `046788a32eb92e789d37e99bb0e1fe79707590f5af281074d37f0931a2b55745` | `963934b1ab30373170babf569040f89b4b21920167c9d9817d3bd1442826837e` |
| `Prog.runT` | def | `Toy/FloatTier/Lang.lean:155` | `propext` | `907bb4cf88503d69226c4e53499314c4ced6f8206c23436b418f4ca5427728ce` | `b4ad4619ead965d19d749406ced14c17be300749bb65a5c141b42ebcf70a65f6` |
| `Prog.runT_eq_of_tierSound_of_bitSafe_nanOrZero` | theorem | `Toy/FloatTier/Determinism.lean:163` | `Classical.choice`, `Quot.sound`, `propext` | `43965ccd679544f91c749bc13577c6647da300f763dfaf4da2f01f18b2040cc1` | `0c4bafe14fe9f72e94a0ad01facb162b478c6fe6803cfd4dff1115e3e70a345a` |
| `Prog.runT_eq_of_tierSound_of_minMaxFree_of_bitSafe_nan` | theorem | `Toy/FloatTier/Determinism.lean:180` | `Quot.sound`, `propext` | `29f50d4b8459d81d83327e9f163b3a2117f38f2d5bcdf8af79374f75b5816342` | `02f1897310a980f85fef800edf1df3c73764011053e7c0db793bdc456dd8f770` |
| `RefinesS` | def | `Toy/FloatTier/Lang.lean:197` | `Quot.sound`, `propext` | `aecb9b2a1d82ab38f84afc8ac59cf274ff2f34a31f8a67946a501a0c98d64da9` | `cc932a3e8c59742aa3562fbd4ae9b4417e57055e0d58cc4c867e33e61a6d8bb2` |
| `Tier` | abbrev | `Toy/FloatTier/Sets.lean:100` | none | `1452f8536a7f47da9663e8efd7b5bdcdb40dd4ff25206e8f67a356ee015fb665` | `96b2118ac0d27f7d519d8b3b6ff3fde7da1c469d47c20dcd18a25217a32ee48f` |
| `TierSound` | def | `Toy/FloatTier/Sets.lean:104` | `Quot.sound`, `propext` | `aecb9b2a1d82ab38f84afc8ac59cf274ff2f34a31f8a67946a501a0c98d64da9` | `cc932a3e8c59742aa3562fbd4ae9b4417e57055e0d58cc4c867e33e61a6d8bb2` |
| `TwoPowFits` | def | `Toy/FloatTier/Cast.lean:96` | none | `0950c5b565e5d910559deaf2104ce3c579b52ddbd241b28942d5acf5920332da` | `96b2118ac0d27f7d519d8b3b6ff3fde7da1c469d47c20dcd18a25217a32ee48f` |
| `V` | inductive | `Toy/FloatTier/NaNVal.lean:39` | none | `1452f8536a7f47da9663e8efd7b5bdcdb40dd4ff25206e8f67a356ee015fb665` | `96b2118ac0d27f7d519d8b3b6ff3fde7da1c469d47c20dcd18a25217a32ee48f` |
| `V.abs` | def | `Toy/FloatTier/NaNVal.lean:95` | none | `13e959dce5aea44f334aeba5fcd01a82157f7c39080918fbab91011563ad52af` | `605e14a3160a8ea65ee805db3c9225e591837dee5bdfb150ce27eebb2019546f` |
| `V.bits` | def | `Toy/FloatTier/NaNVal.lean:102` | none | `e4462dbe5852ee09ac57f11afca2eca167fa660c9c67df9e56c04c08c8e75e82` | `605e14a3160a8ea65ee805db3c9225e591837dee5bdfb150ce27eebb2019546f` |
| `V.bits_injective` | theorem | `Toy/FloatTier/VLemmas.lean:209` | `Quot.sound`, `propext` | `acc61814339860172c61b417ade0ab777a9fc1d741c24fed94a565365bee2b3f` | `5730e1433daebe7171c47a4e9c4ad798ee1c21c562f21480c2820d73e9334b29` |
| `V.bits_withSign_true` | theorem | `Toy/FloatTier/VLemmas.lean:204` | `Quot.sound`, `propext` | `7efd355cdae7306eceb8347d05257c22aa8535c0ee2a6deb5f3aadfa1ce29b29` | `e22a226e71d09aa819e1539233310ba97c83c55179a7769520c026548e63322c` |
| `V.copysign` | def | `Toy/FloatTier/NaNVal.lean:98` | none | `9542e27a7520d513268cacb76b62d3f2d198958b2d3348f5f15d78b102793bf2` | `605e14a3160a8ea65ee805db3c9225e591837dee5bdfb150ce27eebb2019546f` |
| `V.isNaN` | def | `Toy/FloatTier/NaNVal.lean:51` | `propext` | `d06a8dac3dff819272f822840604572a70518ed61cc4e444a8dd3c20f6008509` | `605e14a3160a8ea65ee805db3c9225e591837dee5bdfb150ce27eebb2019546f` |
| `V.isNaNOrZero` | def | `Toy/FloatTier/NaNVal.lean:129` | `propext` | `8916ea914bf206fc8cafbbe7668cbd74e13d47cecfcf210566f46a47c7a9fe7c` | `605e14a3160a8ea65ee805db3c9225e591837dee5bdfb150ce27eebb2019546f` |
| `V.isZero` | def | `Toy/FloatTier/NaNVal.lean:125` | `propext` | `8916ea914bf206fc8cafbbe7668cbd74e13d47cecfcf210566f46a47c7a9fe7c` | `605e14a3160a8ea65ee805db3c9225e591837dee5bdfb150ce27eebb2019546f` |
| `V.neg` | def | `Toy/FloatTier/NaNVal.lean:92` | none | `13e959dce5aea44f334aeba5fcd01a82157f7c39080918fbab91011563ad52af` | `605e14a3160a8ea65ee805db3c9225e591837dee5bdfb150ce27eebb2019546f` |
| `V.payload` | def | `Toy/FloatTier/NaNVal.lean:64` | `propext` | `e4462dbe5852ee09ac57f11afca2eca167fa660c9c67df9e56c04c08c8e75e82` | `605e14a3160a8ea65ee805db3c9225e591837dee5bdfb150ce27eebb2019546f` |
| `V.prefNaN` | def | `Toy/FloatTier/NaNVal.lean:132` | none | `b6bb72c5d0c1fb3588cf7670dcbd92e7c8168a751b12afefae412b797a696b19` | `605e14a3160a8ea65ee805db3c9225e591837dee5bdfb150ce27eebb2019546f` |
| `V.signBit` | def | `Toy/FloatTier/NaNVal.lean:77` | none | `d06a8dac3dff819272f822840604572a70518ed61cc4e444a8dd3c20f6008509` | `605e14a3160a8ea65ee805db3c9225e591837dee5bdfb150ce27eebb2019546f` |
| `V.toFP` | def | `Toy/FloatTier/NaNVal.lean:111` | none | `4d67ee660bf75fd59c5983f682115d8869be4c9232de8d3e444e7d8320276806` | `8a675c3f37caa9d2ee3dd07643940c88ac3eace6ac370f5608d12b0f3df96eb4` |
| `V.withSign` | def | `Toy/FloatTier/NaNVal.lean:84` | none | `32b22c7301571f8286386499aed195c7bb3c18da9a2e465fec50a22dbad0a2ee` | `605e14a3160a8ea65ee805db3c9225e591837dee5bdfb150ce27eebb2019546f` |
| `V.zero` | def | `Toy/FloatTier/NaNVal.lean:139` | `Quot.sound`, `propext` | `b6bb72c5d0c1fb3588cf7670dcbd92e7c8168a751b12afefae412b797a696b19` | `605e14a3160a8ea65ee805db3c9225e591837dee5bdfb150ce27eebb2019546f` |
| `ValEq` | def | `Toy/FloatTier/NaNVal.lean:147` | `Quot.sound`, `propext` | `759797dcf6de019fb9e76851f0f8b2ff4d20302899948c35cdf7c0f809bf534b` | `605e14a3160a8ea65ee805db3c9225e591837dee5bdfb150ce27eebb2019546f` |
| `ValEq.refl` | theorem | `Toy/FloatTier/VLemmas.lean:64` | `Quot.sound`, `propext` | `402f7b58f73193c318739800efbab8efb64e3ea1c3a66e1eb0ecce327eaef4a6` | `50c66a82b94366b075f2f3244f8a0d92c87a42df60af9cfbbfd3ac3b1cb3b238` |
| `add` | def | `Toy/FloatTier/Base.lean:210` | `Quot.sound`, `propext` | `8215e510187b6e653da266a379b301827349d784ece21405401521467f103934` | `69ba67611a67ee13cc743846c8b9325c95fee5e73405e307ae4e8102118353fb` |
| `add_eqNsz_congr` | theorem | `Toy/FloatTier/Lemmas.lean:81` | `Classical.choice`, `Quot.sound`, `propext` | `d50cd7a8854775a60943a5f1e5007aa2bec43465caa4ad08bd9187e2e8ef696d` | `038eb313164394b165008d9bb4b61cc70189f7a182ee62e03c7e1105cf43b0a4` |
| `arithSet` | def | `Toy/FloatTier/Sets.lean:66` | `propext` | `e057b71d8804f20802a9dd47a788c943ef3ee24b6f0d74a18402e24457c1d410` | `65c99b98c5642d24918d9277ebb056afe3f26e2d1514278bcbc20aeb67ac8b29` |
| `bitSafe_not_necessary` | theorem | `Toy/FloatTier/Counterexamples.lean:568` | `Quot.sound`, `propext` | `76196a5dbd2211f019f860b2141816cf6cbb6e811db7eaef8f44e4fc8338e89a` | `450a3b017431ed321acb66084480c4e1bb95950cb7d387769890666caace2a6b` |
| `cast_results_nonvacuous` | theorem | `Toy/FloatTier/CastExamples.lean:240` | `propext` | `957f66b4971a7f22b4a3b19e4014e06982194954e199f7edac9fca8335f234d5` | `cd5e9a976a923142ce8a75223f787acba88e5affa57b353d4cefbf710375fcad` |
| `copysignNaN_breaks_determinism` | theorem | `Toy/FloatTier/Counterexamples.lean:242` | `Quot.sound`, `propext` | `513532deee27a5409336e8632dc00c87801aab2385621c808ccf1f9b55beb90b` | `8d76b50f529d22670b9052ac02671fdda7c0f3c3de9f814b23151a0c2eba5a02` |
| `cvtS` | def | `Toy/FloatTier/Cast.lean:64` | `propext` | `d0b7909c8ffa0e9cf8b39841cc87deb70296377d7893a40666523b6e569ea66a` | `69ba67611a67ee13cc743846c8b9325c95fee5e73405e307ae4e8102118353fb` |
| `cvtS_eq_none_iff` | theorem | `Toy/FloatTier/CastStatements.lean:140` | `Classical.choice`, `Quot.sound`, `propext` | `e7faed881bcc53b3cee5548cac41bd8ea1fa00e52e93422540bbdaa4b1c17d2e` | `35ad8635371cf1b242cd1e3c09681be28b34f873d7095037914c960a781aee06` |
| `cvtS_eq_some_of_inOpenS` | theorem | `Toy/FloatTier/CastStatements.lean:172` | `Classical.choice`, `Quot.sound`, `propext` | `e33dc792aef6d2cff44baac3a4ed862f2e47e91c8a555539e29b5488097c51a9` | `35ad8635371cf1b242cd1e3c09681be28b34f873d7095037914c960a781aee06` |
| `cvtU` | def | `Toy/FloatTier/Cast.lean:59` | `propext` | `aea5e37e52b881c00335573aad0d3a5e0e201da9d01ef32183b786e33c5bd80e` | `69ba67611a67ee13cc743846c8b9325c95fee5e73405e307ae4e8102118353fb` |
| `cvtU_eq_none_iff` | theorem | `Toy/FloatTier/CastStatements.lean:125` | `Classical.choice`, `Quot.sound`, `propext` | `8719e002a5ae68e5897d30905dab791d3eed773bbf444a0262ecd2c911cdf53d` | `49594357c7c378ccb3fd9434d47fd2b2c4c729956b50d77ece68a35a0d9b4066` |
| `cvtU_eq_some_of_inOpenU` | theorem | `Toy/FloatTier/CastStatements.lean:165` | `Classical.choice`, `Quot.sound`, `propext` | `db6f97571db3bbeb318e8f6f2ca1ca4e52459025de3e97bd6e68cf2a87d32f93` | `49594357c7c378ccb3fd9434d47fd2b2c4c729956b50d77ece68a35a0d9b4066` |
| `cvtU_isSome_iff` | theorem | `Toy/FloatTier/CastStatements.lean:152` | `Classical.choice`, `Quot.sound`, `propext` | `a0e33bf34cfeacf827f6324d9471bdb5f92e2de9a9b62aaeb281157732526c1f` | `49594357c7c378ccb3fd9434d47fd2b2c4c729956b50d77ece68a35a0d9b4066` |
| `detCongr_toFP` | theorem | `Toy/FloatTier/Determinism.lean:129` | `Quot.sound`, `propext` | `14c7304c6bf923186a2ed89c197a105810fa404496505ebde3806058acd94bd4` | `634cb8017eb75fc578c4a8a4c9e88e5c453d44361ff39c2b3e93a98e4be0854d` |
| `detCongr_valEq` | theorem | `Toy/FloatTier/Determinism.lean:116` | `Classical.choice`, `Quot.sound`, `propext` | `43d847c252bc05e484d518c75576890f162d75021499f03f5cfbe72933971be4` | `5e748c690023dfd7838a112962c41aa92c355f3ad4fdaa06c0a895a0233276bb` |
| `eqNsz_of_key_eq` | theorem | `Toy/FloatTier/Lemmas.lean:175` | `Classical.choice`, `Quot.sound`, `propext` | `bb5b8f2bb8539ddcb02ca3e3e455d98974d21caa002c211b0938d0baf60a9e84` | `dfc6713c0e644b0d8ce36e608389ad19ce89fca8fc27682fb46e8e80326ed1c8` |
| `ex_bitSafe_guarded` | theorem | `Toy/FloatTier/Counterexamples.lean:512` | `Classical.choice`, `Quot.sound`, `propext` | `fbfee164297b5db14b7f78a27c9d390c399f5212021a93dc27921e8af5b98b2a` | `ed0471852062fff607721d9680ef0f271b7da111c45c9096c52ac996a85fae90` |
| `ex_bitSafe_rejects` | theorem | `Toy/FloatTier/Examples.lean:101` | `Quot.sound`, `propext` | `a87edd6431b15d7c9daccfa07883a599c428b161599155d173b6826485cdc8e3` | `53e7079a767a31227145dc0b3eb6c4665f59bb88a969e6b1fb1431cfba5eb31e` |
| `ex_bits_nan_variants_binary32` | theorem | `Toy/FloatTier/Examples.lean:30` | none | `cb3dcbf41b10dd5d5ab79365238a911c13acddf8deaa6dbaf5171002324ebe2d` | `f695dfdc54cd3d27f8e6c9e29d08078c6210588c0652fe365c58637aba48a661` |
| `ex_bits_prefNaN_binary32` | theorem | `Toy/FloatTier/Examples.lean:26` | none | `bf5f2e642b2c23b2d13c8e216fc58e9e020b78436a5beaf38fff28a045bac3b6` | `f695dfdc54cd3d27f8e6c9e29d08078c6210588c0652fe365c58637aba48a661` |
| `ex_cvtS_F33` | theorem | `Toy/FloatTier/CastExamples.lean:31` | `propext` | `c9e1e07acdcb00b0b64cea243ed00ab0c7a8be03feefcb9cd31f55f49c02f8fc` | `383b6d7ba61a7d2340cc6edfc6334f7c909c8dd147d358d93c66ba50550c6622` |
| `ex_cvtU_defined_F33` | theorem | `Toy/FloatTier/CastExamples.lean:22` | `propext` | `c1078715c1d622ddc71d49a69052c08dd05c347d837884874d6c798215323165` | `2e6ca6207b7d7142122549917970961e8ff83d53a3054e397fb4e7f738391879` |
| `ex_cvtU_undefined_F33` | theorem | `Toy/FloatTier/CastExamples.lean:25` | `Quot.sound`, `propext` | `30fdb98f44c79cc6af90b1e22a13525b54f075303b3fa3b1f87b84fd9ee3e0a9` | `d434603191c16f74b8cf8ae051f8a5803537e22be3891a83c976c5ea8d20c5e8` |
| `ex_fold_keeps_var` | theorem | `Toy/FloatTier/Examples.lean:112` | `Quot.sound`, `propext` | `7dfb3c9488a6519e0c9d31cce38d518e5a5b9f1d8176f8017b094c539a8ce42a` | `13a2164e96f6a19d26137fa873888656b193b0451d7a8e913983b204f9f871b0` |
| `ex_inOpenS_F33` | theorem | `Toy/FloatTier/CastExamples.lean:65` | `propext` | `38662172f0ff728b3c81813bbc4b6363c2219babc88abb48ad4385a8bd25ddf5` | `4210744d3744f4b303ec599e57c7e5cc3dee37bffd0850415311836f30336e9e` |
| `ex_inOpenU_F33` | theorem | `Toy/FloatTier/CastExamples.lean:57` | `Quot.sound`, `propext` | `ace6f0f8bbe939bf1267137c1d91a15ff2df91f349dceea4cbbea508967592a4` | `fb87c2e480888e843427fda9fc3716add147f88ce17080ae83783d28c9ac77f6` |
| `ex_minMaxFree` | theorem | `Toy/FloatTier/Examples.lean:108` | `Quot.sound`, `propext` | `d020f1e6b4569407e7200a5903b3008fce26f8e9eeeb96926cd90e52f566d166` | `f6780f029b1b68cb12b34febb9ff2c63421a5082439053af92e43e7d2245cec0` |
| `ex_nanChoice_extra_F23` | theorem | `Toy/FloatTier/Examples.lean:57` | `Quot.sound`, `propext` | `9ed79294a4b45cf153df4af3605fd83521fc4e851f9d9b1c56f46c385669a1a7` | `7ebd094f883f58421fba904b35cbdc0294929976e2942ca3906b3c9819973b3b` |
| `ex_nanChoice_propagation_F23` | theorem | `Toy/FloatTier/Examples.lean:42` | `Quot.sound`, `propext` | `3b51104b9b60367489fdbe5512023deb3b2177fb82519c9f5423a9d5ef49a66e` | `118443893b50b26ca113a6dc7c0eac7fa4cceab3946b32ac3d09d4e85d98e682` |
| `ex_nanChoice_rejects_F23` | theorem | `Toy/FloatTier/Examples.lean:51` | `Quot.sound`, `propext` | `c3c26424068b805b58b183dd9dce24c52b41199cf54b729f9b72101093224534` | `cbf648a470e912aa28df36913475db9334ce30d4ed025093198e3108e7dbbd38` |
| `ex_negOne_F33` | theorem | `Toy/FloatTier/CastExamples.lean:87` | `Quot.sound`, `propext` | `67c312236cba076bad320f8acdf265ba0c76c6302892aa5dcbaf83231fe8b561` | `871953fdfb5a32f0ef0f44bfd1ba1b38a6b524ecd3c67f786986de85c47cda9f` |
| `ex_no_snan_p2` | theorem | `Toy/FloatTier/Examples.lean:21` | `Quot.sound`, `propext` | `39ab4e33d9f117cf204393862bd143a0965aa6f0929f58a4516cd21c10b31be8` | `5b5ba8ba64cdb65a70b185372ad87a2478785c94132a3f399d273f45ce0b71f3` |
| `ex_primSet_allows_F23` | theorem | `Toy/FloatTier/Examples.lean:65` | `Quot.sound`, `propext` | `b4bb234faff739688e68b82b53757e3e5c91aa68d92aa16f8bb528abe764f58c` | `a5450c4411f62c1f09c31d92c6149a5970c70674c0d91ff7c3bb9f814d547b65` |
| `ex_primSet_rejects_F23` | theorem | `Toy/FloatTier/Examples.lean:72` | `Quot.sound`, `propext` | `e39f143435baf2af7f8e0b704df5a5da0b837b33026a498266f709d14217cf25` | `9456b73aa829090fa15b4627ed788667eb4de31e6520b3a640ffe032e51a7c0a` |
| `ex_rangeCheckU_F33` | theorem | `Toy/FloatTier/CastExamples.lean:103` | `Quot.sound`, `propext` | `9b4425bbc0e131ec4990c4b4231eb6c8820f91d0094ebf7f92d79f62b73be653` | `dbb620c3275777b8d5bf257accd088956ae3ac4ded868924d4f5f3b5ec61c138` |
| `ex_satS_F33` | theorem | `Toy/FloatTier/CastExamples.lean:43` | `propext` | `7c92561e4ebcf4ee0d72a9ec9e036498b952b487581576044cba45c269e36f95` | `d7cf73e8af2e2cdaf97e792734fc794f2666eeb35714fe8f6d15da12157e637b` |
| `ex_satU_F33` | theorem | `Toy/FloatTier/CastExamples.lean:36` | `propext` | `f46e5304af2c877c23da35f21e5cbbe84820baa45d95c14ab380e9624a041fee` | `0cc4c16460aa3c6517a052787f752129e8d11fdf70db07d67bba93b87b9d603a` |
| `ex_snan_payload_F23` | theorem | `Toy/FloatTier/Examples.lean:17` | `propext` | `e30b2d75c892737ad9e875bc07c620be0d25d7c22b7418175ac3fb465922327b` | `a921dcea6cbce72e39ab6242db79b7cc0e8a8364ff4d8d5f59dbb3f66d87c8ac` |
| `ex_tierSound_F23` | theorem | `Toy/FloatTier/Examples.lean:81` | `Quot.sound`, `propext` | `d192b0ecbf6369c51de64a552a47eee712fc87436f5a137cbfdc77d381b9ae9c` | `c944800e94c06fbe26c64dd903c3a4ab6ebb574934c1d2a7d055359e2dad28bf` |
| `ex_trunc_F33` | theorem | `Toy/FloatTier/CastExamples.lean:17` | `propext` | `68723c06828bbf50bb3fccfb9d25f0080ab262cde7ce52310b9030121c58ea35` | `752f707c99973c0e3c8244b121014cde0d5d3964def4f43c78846caa22540ae3` |
| `ex_twoPowFits_binary32_32` | theorem | `Toy/FloatTier/CastExamples.lean:99` | none | `7b88b647dcdd9b5b769cb61e03ebb973d56fb9e5f60a027b05cfe7a0618707d1` | `074a7967210720adca188bcb4f8dc27f0c4737529e51e37ad10d64ab17e6bfc0` |
| `ex_twoPowRound_fits_F33` | theorem | `Toy/FloatTier/CastExamples.lean:91` | `Quot.sound`, `propext` | `ee43b52ea0a7771bfc60feff0293332e060591b322cc8070a5e1bd6c9959300f` | `c5ae16e50a2b4754a79fdb1ea23d8c4c1844211763b936f5afffb7ba9b8253e4` |
| `ex_twoPowRound_overflow_F33` | theorem | `Toy/FloatTier/CastExamples.lean:95` | `Quot.sound`, `propext` | `7680467f36b2f2f94fd96052c49373bb429a49c4c1591779e0e3b199ad0c265d` | `a14b822becc1eb1830f070a3a0b986a4fa2ff8f48eaba840bc909772cfc4574f` |
| `ex_valEq_F23` | theorem | `Toy/FloatTier/Examples.lean:90` | `Quot.sound`, `propext` | `59ed8bbd427e05da8b30d6d6ebb9e7773ac38b0f9e199a764fc296f8bb94eeae` | `f09a7208a6bd7ff9128ba9c1331f2558733354ab464a28c81b8eabba0be45a81` |
| `exists_runS_not_realized_by_any_tier` | theorem | `Toy/FloatTier/Counterexamples.lean:182` | `Quot.sound`, `propext` | `b6bdb8ce1e9fdffe54fb585ccc5417fc2dd5424bd47d24a3eb01cdda94929070` | `85765a677c74809d5ae24711eb76960b552bf99a4ef1dc8e932664c328a8a681` |
| `extraPay1` | def | `Toy/FloatTier/Instances.lean:120` | none | `c11b1ed1b159ed20a3be7feef26adca9d7e2a5d4e490f4040115e0ee33c28b65` | `5555ca01de7bbf486f87f23ad1004c0a7fceb6b25c6d4d0a28bc9397f9e2cddb` |
| `f33_3p5` | def | `Toy/FloatTier/Instances.lean:33` | none | `d502c39603743e9e61f3d5141a78112b0af3c3359ab19dbc741e7692afda9d1e` | `06a8f9a97088ddc9019a418c9ad2d3f11e2957db4c56b8e6aa02db0c051796f8` |
| `f33_4` | def | `Toy/FloatTier/Instances.lean:39` | none | `d502c39603743e9e61f3d5141a78112b0af3c3359ab19dbc741e7692afda9d1e` | `06a8f9a97088ddc9019a418c9ad2d3f11e2957db4c56b8e6aa02db0c051796f8` |
| `f33_5` | def | `Toy/FloatTier/Instances.lean:41` | none | `d502c39603743e9e61f3d5141a78112b0af3c3359ab19dbc741e7692afda9d1e` | `06a8f9a97088ddc9019a418c9ad2d3f11e2957db4c56b8e6aa02db0c051796f8` |
| `f33_m0p5` | def | `Toy/FloatTier/Instances.lean:37` | none | `d502c39603743e9e61f3d5141a78112b0af3c3359ab19dbc741e7692afda9d1e` | `06a8f9a97088ddc9019a418c9ad2d3f11e2957db4c56b8e6aa02db0c051796f8` |
| `f33_m3p5` | def | `Toy/FloatTier/Instances.lean:35` | none | `d502c39603743e9e61f3d5141a78112b0af3c3359ab19dbc741e7692afda9d1e` | `06a8f9a97088ddc9019a418c9ad2d3f11e2957db4c56b8e6aa02db0c051796f8` |
| `feq` | def | `Toy/FloatTier/Base.lean:253` | `propext` | `84220c1309d421b5ac4b1fe21ca1f277ed13e872a05ffa79563b7ebf6760beab` | `69ba67611a67ee13cc743846c8b9325c95fee5e73405e307ae4e8102118353fb` |
| `feq_eqNsz_congr` | theorem | `Toy/FloatTier/Lemmas.lean:164` | `Classical.choice`, `Quot.sound`, `propext` | `224a6a1649cf9780ff0ff9da011b89b3f1a73f45e3dda6e76b369f26b539632a` | `6002e8b91400b53333d9af803d9e7cbdc660f81edad187dda15ec404677ab31a` |
| `fold_tierCtfe_changes_tierRunA_bits` | theorem | `Toy/FloatTier/Statements.lean:267` | `Quot.sound`, `propext` | `25791dd5043570f1e0fe5c0f9f1720b8461cdd891ef6c41c47bf397236b4e0f0` | `dfe8e44f49decde28feff4935b780f978473d4bfe6c6abac5dc96050137c538d` |
| `fold_tierCtfe_preserves_tierRunA_nan_free` | theorem | `Toy/FloatTier/Counterexamples.lean:165` | `Quot.sound`, `propext` | `49f87882ee9eb19b8c7ea1a010ae95178b9a4d5c2461bf6c43d0f6fbbed8362b` | `c30b45f7ff98ec4f31185c8c0b5f0d2e3274b69df2d28010bbff4a74886ec4b1` |
| `fold_unsound_tier_not_refinement` | theorem | `Toy/FloatTier/Counterexamples.lean:384` | `Quot.sound`, `propext` | `1c8df638145d1e1110bc1bd89b62b59c004bbf17878544d63916b2f32e6d3288` | `fbd6e17b99b8dc42b6920c788cfabcfa09f894dd657bfcc4bfc801eaf7a54654` |
| `isFinite_of_uval_bounds` | theorem | `Toy/FloatTier/CastStatements.lean:247` | `Quot.sound`, `propext` | `3ef9625cbe9900730c70236089bc0ebdb314a05463deee94b8e8ff62fdf5c469` | `4596602a1605edba9b9caf75511bd51a452c103985ac42e98ad1998644521360` |
| `key` | def | `Toy/FloatTier/Base.lean:241` | none | `b2853c555818137ab7b38220bffd2fd4da06d844679996d628815f5c87bd6a4c` | `69ba67611a67ee13cc743846c8b9325c95fee5e73405e307ae4e8102118353fb` |
| `le` | def | `Toy/FloatTier/Base.lean:249` | `propext` | `84220c1309d421b5ac4b1fe21ca1f277ed13e872a05ffa79563b7ebf6760beab` | `69ba67611a67ee13cc743846c8b9325c95fee5e73405e307ae4e8102118353fb` |
| `lt` | def | `Toy/FloatTier/Base.lean:247` | `propext` | `84220c1309d421b5ac4b1fe21ca1f277ed13e872a05ffa79563b7ebf6760beab` | `69ba67611a67ee13cc743846c8b9325c95fee5e73405e307ae4e8102118353fb` |
| `lt_eqNsz_congr` | theorem | `Toy/FloatTier/Lemmas.lean:158` | `Classical.choice`, `Quot.sound`, `propext` | `c28280b85eea61c9891772541c8b37e814523c440d5d6b30e98a1448f0c4da0f` | `32437212602008e3bfd22f5b331e307265f377c1823fa8705b983b9ebf8788e6` |
| `maxLt` | def | `Toy/FloatTier/Base.lean:258` | `propext` | `ad77d1e7f26b111118dd57f8bae31e7260c81c9b8c93f5aca0aa7f76c3239b36` | `69ba67611a67ee13cc743846c8b9325c95fee5e73405e307ae4e8102118353fb` |
| `maxSet` | def | `Toy/FloatTier/Sets.lean:79` | `propext` | `d7a03a1d9f2635b8d1f63f2229e44307e2dc40fe78a518afe577144bd663f52e` | `19e76218d8cba1867fd412f90f6ee3e0a031915f46fe69893de79d67c7b97392` |
| `maximum` | def | `Toy/FloatTier/Base.lean:269` | `Quot.sound`, `propext` | `ad77d1e7f26b111118dd57f8bae31e7260c81c9b8c93f5aca0aa7f76c3239b36` | `69ba67611a67ee13cc743846c8b9325c95fee5e73405e307ae4e8102118353fb` |
| `minLt` | def | `Toy/FloatTier/Base.lean:256` | `propext` | `ad77d1e7f26b111118dd57f8bae31e7260c81c9b8c93f5aca0aa7f76c3239b36` | `69ba67611a67ee13cc743846c8b9325c95fee5e73405e307ae4e8102118353fb` |
| `minSet` | def | `Toy/FloatTier/Sets.lean:70` | `propext` | `d7a03a1d9f2635b8d1f63f2229e44307e2dc40fe78a518afe577144bd663f52e` | `19e76218d8cba1867fd412f90f6ee3e0a031915f46fe69893de79d67c7b97392` |
| `minZeroSign_breaks_determinism` | theorem | `Toy/FloatTier/Counterexamples.lean:273` | `Quot.sound`, `propext` | `28131355d36eca108acca9aa5db9ca77c4a3acd60989e4455875ae0c7b18523b` | `9c9e8e4b4ea739a01a052eedc24ad052bddb26af2b518d45559ee24a7cbb9578` |
| `minZero_eq_and_signBit_runS` | theorem | `Toy/FloatTier/Counterexamples.lean:293` | `Quot.sound`, `propext` | `2387e398932079f7bb5156db3fe35b5aaa4725811d18b4f2cadf263e6af38fb8` | `cb0336c9d1fb81a16fa1f20189edda2e34894eb9fd8d2f6cfc2596aeae63e8f0` |
| `minimum` | def | `Toy/FloatTier/Base.lean:265` | `Quot.sound`, `propext` | `ad77d1e7f26b111118dd57f8bae31e7260c81c9b8c93f5aca0aa7f76c3239b36` | `69ba67611a67ee13cc743846c8b9325c95fee5e73405e307ae4e8102118353fb` |
| `mul` | def | `Toy/FloatTier/Base.lean:227` | `Quot.sound`, `propext` | `8215e510187b6e653da266a379b301827349d784ece21405401521467f103934` | `69ba67611a67ee13cc743846c8b9325c95fee5e73405e307ae4e8102118353fb` |
| `mul_eqNsz_congr` | theorem | `Toy/FloatTier/Lemmas.lean:132` | `Classical.choice`, `Quot.sound`, `propext` | `19087c093971086db641db86498afed4ee98e96f2318287d85d02bdb7030973a` | `b076fee23d096dbb132f179433b1d0a8a7cc864875cb1b3adeac4eb95d4df2c4` |
| `naiveCheckU` | def | `Toy/FloatTier/Cast.lean:104` | `Quot.sound`, `propext` | `c1deedd94c5a1d71e2bac659d07a8603fb010c2d3b2b4ed3eb439f6e986692c0` | `69ba67611a67ee13cc743846c8b9325c95fee5e73405e307ae4e8102118353fb` |
| `naiveCheckU_accepts_inf_F23_3` | theorem | `Toy/FloatTier/CastExamples.lean:146` | `Quot.sound`, `propext` | `efce19b85a86dc2a7b2cc8ac8840cd851923a0258c00c5441d091b6ac8aacb40` | `3da4ab094344e252ee8f5540bee03eb6301dcfb66f3b142fabf169cea6aaf8a5` |
| `naiveCheckU_accepts_inf_binary32_128` | theorem | `Toy/FloatTier/CastExamples.lean:137` | `Quot.sound`, `propext` | `8995cf164fedcd12d125734ebf51b938d71b34b59cbd9881b20fea71d7a49635` | `c8517960379933e34667bbd294266afda0bf93a9f1c9d0c7c2e6f919f306c7ef` |
| `naiveCheckU_accepts_two_pow_32_binary32` | theorem | `Toy/FloatTier/CastExamples.lean:128` | `Quot.sound`, `propext` | `bb307f2cd063d6d90daf6b2129e2fdc35b17f9e3556b9c6d1feb9950d36efda6` | `c8517960379933e34667bbd294266afda0bf93a9f1c9d0c7c2e6f919f306c7ef` |
| `naiveCheckU_inexact_every_width_F23` | theorem | `Toy/FloatTier/CastExamples.lean:154` | `Classical.choice`, `Quot.sound`, `propext` | `8d32abb8fa7875babece83e10a9655beaeb37f155b8a2f4da727fb8d83a92cfc` | `3da8c739a4931b1f5f50e8693e25f9a60b85acd0a3b6326e73d2df5f70566442` |
| `naiveCheckU_not_exact_small` | theorem | `Toy/FloatTier/CastExamples.lean:118` | `Quot.sound`, `propext` | `0c4d45fe14110ff2bb8ff70865c9f0a213363a31a5dd8efabf13e7ae7668725e` | `504417482d2763b4cc7bc8750867a2970dbae674a57986e24d5726a5f376e685` |
| `nanChoice_prefNaN` | theorem | `Toy/FloatTier/Examples.lean:37` | `propext` | `c4b1b134431344e5c2748331dbe03724dc3e468cb1ff59116fc1a00cf0298deb` | `d257d89f30504903c61807f25689ba49a9c92cf764897f9ad4618261eaf12f75` |
| `negOne` | def | `Toy/FloatTier/Cast.lean:85` | `Quot.sound`, `propext` | `2d14d50880339077d4c022d5f6a989cfb44e2cf0d193515cdbd515d4f0c26d04` | `69ba67611a67ee13cc743846c8b9325c95fee5e73405e307ae4e8102118353fb` |
| `noExtra` | def | `Toy/FloatTier/Sets.lean:41` | none | `063f2391ec85c7f0b88374afba3b2bdcb609c63f034ed353cedadc8fd7806db8` | `19e76218d8cba1867fd412f90f6ee3e0a031915f46fe69893de79d67c7b97392` |
| `not_inOpen_of_not_finite` | theorem | `Toy/FloatTier/CastStatements.lean:66` | `propext` | `6b776999aa4188156f16753c7156733fca7ae282c16590e21f6c4fd7d205232f` | `2463b26d1e05bd9065e4ca2097d8dd082ee020f94134fabeadf903734ccccc8f` |
| `not_tierSound_tierBad` | theorem | `Toy/FloatTier/Counterexamples.lean:373` | `Quot.sound`, `propext` | `eaaa9e083d8290fe45ad0649ec737b1f80e03768b82397dc4dc116ff205f9443` | `f94fd6b2d99c96c07eda8f69b2f87b4d1d18d8f1dccefaa7f4191bdbe6bb8908` |
| `primSet` | def | `Toy/FloatTier/Sets.lean:88` | `Quot.sound`, `propext` | `6110af84d9340423a9cee20f7f8f7d18119f9f21a7397fe7fbaf852f48483573` | `78b3c5e60621348fe301e477c75b855b1016d6ac6f0ffa133dc6cd68bfec71a0` |
| `primSet_of_isNaN` | theorem | `Toy/FloatTier/Counterexamples.lean:413` | `Quot.sound`, `propext` | `77894133d51b70380c9c4925eb60d8f6a30d7275ed59dc8e505de30be325aabc` | `82dfbd1c9808a248d69536cdfc5ff642830054c40b16ca5e3fdf7e82e5068666` |
| `primSet_toFP_congr` | theorem | `Toy/FloatTier/VLemmas.lean:169` | `Quot.sound`, `propext` | `de42afab464b0b37a0e8497f3b2f1e94ccafdb37cbde81f8f89327656f792136` | `784b764dfc08e9ae3aaa5259d639c813da0fe8b8f87db31fb3461090c484392d` |
| `primSet_valEq_congr` | theorem | `Toy/FloatTier/VLemmas.lean:155` | `Classical.choice`, `Quot.sound`, `propext` | `1f7362a6a033d8b65e85ab93a7aed6293082ef093e912bf83b5d38eb4e3d46e1` | `9eb06e026fbf305b00990066db1fd41f1afb3945cd7f5516002ec6d50986e49c` |
| `progBitsCopysignVarInfMulNegInf` | def | `Toy/FloatTier/Instances.lean:49` | none | `7e8f3ac05ca3d28983f9b9e1370794d2459965e75bff50bcb3b83671a19c9085` | `36ba23a4291bf7bee44419caa9295f5811053b67c522df3393b7e20908b50c4d` |
| `progBitsCopysignVarNaN` | def | `Toy/FloatTier/Statements.lean:257` | `Quot.sound`, `propext` | `7e8f3ac05ca3d28983f9b9e1370794d2459965e75bff50bcb3b83671a19c9085` | `36ba23a4291bf7bee44419caa9295f5811053b67c522df3393b7e20908b50c4d` |
| `progBitsNaNLit` | def | `Toy/FloatTier/Instances.lean:96` | none | `7e8f3ac05ca3d28983f9b9e1370794d2459965e75bff50bcb3b83671a19c9085` | `36ba23a4291bf7bee44419caa9295f5811053b67c522df3393b7e20908b50c4d` |
| `progBitsZeroMulInf` | def | `Toy/FloatTier/Statements.lean:122` | `Quot.sound`, `propext` | `7e8f3ac05ca3d28983f9b9e1370794d2459965e75bff50bcb3b83671a19c9085` | `36ba23a4291bf7bee44419caa9295f5811053b67c522df3393b7e20908b50c4d` |
| `progCopysignNaN` | def | `Toy/FloatTier/Instances.lean:54` | `Quot.sound`, `propext` | `7e8f3ac05ca3d28983f9b9e1370794d2459965e75bff50bcb3b83671a19c9085` | `36ba23a4291bf7bee44419caa9295f5811053b67c522df3393b7e20908b50c4d` |
| `progGuardedDeadCopysign` | def | `Toy/FloatTier/Instances.lean:75` | `Quot.sound`, `propext` | `7e8f3ac05ca3d28983f9b9e1370794d2459965e75bff50bcb3b83671a19c9085` | `36ba23a4291bf7bee44419caa9295f5811053b67c522df3393b7e20908b50c4d` |
| `progGuardedInputCopysign` | def | `Toy/FloatTier/Instances.lean:83` | `Quot.sound`, `propext` | `7e8f3ac05ca3d28983f9b9e1370794d2459965e75bff50bcb3b83671a19c9085` | `36ba23a4291bf7bee44419caa9295f5811053b67c522df3393b7e20908b50c4d` |
| `progIsNaNLitAdd` | def | `Toy/FloatTier/Instances.lean:101` | `Quot.sound`, `propext` | `7e8f3ac05ca3d28983f9b9e1370794d2459965e75bff50bcb3b83671a19c9085` | `36ba23a4291bf7bee44419caa9295f5811053b67c522df3393b7e20908b50c4d` |
| `progIsNaNLitAdd_nonvacuous` | theorem | `Toy/FloatTier/Counterexamples.lean:599` | `Quot.sound`, `propext` | `43ca377686e8009dac835e723cb8fd709ec36102452e3a7957a39e16c83eaf46` | `d83946654472b4272291d55eb2343e57b07e48d1211149581364f61d59bdad78` |
| `progIsNaNZeroMulInf` | def | `Toy/FloatTier/Instances.lean:45` | `Quot.sound`, `propext` | `7e8f3ac05ca3d28983f9b9e1370794d2459965e75bff50bcb3b83671a19c9085` | `36ba23a4291bf7bee44419caa9295f5811053b67c522df3393b7e20908b50c4d` |
| `progMinZeroEq` | def | `Toy/FloatTier/Instances.lean:63` | `Quot.sound`, `propext` | `7e8f3ac05ca3d28983f9b9e1370794d2459965e75bff50bcb3b83671a19c9085` | `36ba23a4291bf7bee44419caa9295f5811053b67c522df3393b7e20908b50c4d` |
| `progMinZeroEq_nonvacuous` | theorem | `Toy/FloatTier/Counterexamples.lean:363` | `Quot.sound`, `propext` | `f46ba37e4525b9beb6b9905a595b9685951539a18fc9e1bfb89e85ecb60cace5` | `2269950a273f1c17a22fae075e18c153b4babdb8e45a3e1e286502b2d807ea93` |
| `progMinZeroSign` | def | `Toy/FloatTier/Instances.lean:59` | `Quot.sound`, `propext` | `7e8f3ac05ca3d28983f9b9e1370794d2459965e75bff50bcb3b83671a19c9085` | `36ba23a4291bf7bee44419caa9295f5811053b67c522df3393b7e20908b50c4d` |
| `progNaNBranchSign` | def | `Toy/FloatTier/Instances.lean:68` | `Quot.sound`, `propext` | `7e8f3ac05ca3d28983f9b9e1370794d2459965e75bff50bcb3b83671a19c9085` | `36ba23a4291bf7bee44419caa9295f5811053b67c522df3393b7e20908b50c4d` |
| `progNaNBranchSign_nonvacuous` | theorem | `Toy/FloatTier/Counterexamples.lean:343` | `Quot.sound`, `propext` | `b347259b51e8b412ca2ffd0c788e0b99ddaa1a127c46092cc80e9b61130a640c` | `cb8be37fc0db996a0892874dcc2e1e1f1ecf97a13e989c53509f44c03f0a13a4` |
| `progSelfEqCopysignNaN` | def | `Toy/FloatTier/Instances.lean:106` | `Quot.sound`, `propext` | `7e8f3ac05ca3d28983f9b9e1370794d2459965e75bff50bcb3b83671a19c9085` | `36ba23a4291bf7bee44419caa9295f5811053b67c522df3393b7e20908b50c4d` |
| `progSignBitAbsNaN` | def | `Toy/FloatTier/Instances.lean:91` | `Quot.sound`, `propext` | `7e8f3ac05ca3d28983f9b9e1370794d2459965e75bff50bcb3b83671a19c9085` | `36ba23a4291bf7bee44419caa9295f5811053b67c522df3393b7e20908b50c4d` |
| `rangeCheckU` | def | `Toy/FloatTier/Cast.lean:101` | `Quot.sound`, `propext` | `038c6b9350f0d63977dcb5537d249cddd8fc4734c6ceda0226c236587f92f272` | `69ba67611a67ee13cc743846c8b9325c95fee5e73405e307ae4e8102118353fb` |
| `rangeCheckU_twoPowRound_iff` | theorem | `Toy/FloatTier/CastStatements.lean:187` | `Classical.choice`, `Quot.sound`, `propext` | `ef2e782d8febc6d71ede60c609afffac3400a2d697facaca45d6e744b98b6fcb` | `22abd60a8cd9680393e1324fcf64f27f45d9f7851852467f2a0c4960aa1c1d58` |
| `rangeCheckU_twoPowRound_iff_nonvacuous` | theorem | `Toy/FloatTier/CastExamples.lean:251` | `Quot.sound`, `propext` | `648881f3ad62dc9fbc7b5f7b69d95a8fad2f9d23864682486b3cce38ce31b0c7` | `505de6fda1c98559d1bf1dbe365005962c173afcfda1bc0cb26d64fe6dad0dff` |
| `refinesS_iff_tierSound` | theorem | `Toy/FloatTier/Statements.lean:39` | `Quot.sound`, `propext` | `39dbc4853e68ffe434ce650c3940573a4e357cc5edf4bff38f3fa743c9b0b766` | `e6ab73bdb3dd2063cf244977019af6e492c0a95364f5ed9f4cce7a1aba67f998` |
| `refinesS_iff_tierSound_nonvacuous` | theorem | `Toy/FloatTier/Counterexamples.lean:121` | `Quot.sound`, `propext` | `07445f0f87eddba2a8202286c51949059cb977c521bb9603177efc792a45d9f4` | `d1c894996cddf07b07d249131f84f3f70bfc774812f2ac13c3e592db790c5ea3` |
| `refuted_extra_payload_tier_separates_noExtra_p2` | theorem | `Toy/FloatTier/Counterexamples.lean:637` | `Quot.sound`, `propext` | `6188040d0b3f420f9281c9c2458aa25a10f3420f2279a7213c5f5700b83aaf05` | `181d7a41fed8ee96e57de9974a619f82fe6288ae6ace7ac1971ebd393a7ec96a` |
| `refuted_naiveCheckU_exact_at_W_eq_p` | theorem | `Toy/FloatTier/CastExamples.lean:212` | `Quot.sound`, `propext` | `c830ad956554271285aff50f00aaa25f95723c3e7f1197e997f277f452226eef` | `3da8c739a4931b1f5f50e8693e25f9a60b85acd0a3b6326e73d2df5f70566442` |
| `refuted_value_level_observations_of_sound_tiers_agree` | theorem | `Toy/FloatTier/Counterexamples.lean:622` | `Quot.sound`, `propext` | `8962909153e02b3a4e4434226a84d718d42d675b3ccacce02cd85734310de661` | `71dc473625731ee9b2b96664da2272160e2aa8998be657c95799622866b6eb5c` |
| `round` | def | `Toy/FloatTier/Base.lean:189` | `Quot.sound`, `propext` | `c777f5623f8beb42d7aba1b09edfe5284ca3194cd3190882a1e47569472eaa4c` | `69ba67611a67ee13cc743846c8b9325c95fee5e73405e307ae4e8102118353fb` |
| `roundNat` | def | `Toy/FloatTier/Cast.lean:91` | `Quot.sound`, `propext` | `bde57165f0f6c3f0294a6e8881526c657925f8eb5f3d57d15b65f952f95da22c` | `69ba67611a67ee13cc743846c8b9325c95fee5e73405e307ae4e8102118353fb` |
| `roundNat_F33_three_exact` | theorem | `Toy/FloatTier/CastCompanion.lean:17` | `Quot.sound`, `propext` | `fd4d08b41a9fd79f8b1c905e40ca09aeca54612f585f7f96ae021d0362601dfd` | `e0733c7e4872171c2fa16c97131c6dc736a8ab812fc30dbd1ae4d197b011c66e` |
| `runS_of_runS_fold_nonvacuous` | theorem | `Toy/FloatTier/Counterexamples.lean:143` | `Quot.sound`, `propext` | `58191f32ca6af13bdfa8440c548ff9f769c12fbbb3e4d35d5fe4edc31e114a35` | `efab1f12ad6bbc50a0b5abf136c6e584078dfb1c4cda5128b0bfeca5bd1f99b4` |
| `satS` | def | `Toy/FloatTier/Cast.lean:77` | `propext` | `4b0d2c2e4133c2fd0dcc53df0c6e19b084b0fff375643bb1b8bf3cfe066cc7a6` | `69ba67611a67ee13cc743846c8b9325c95fee5e73405e307ae4e8102118353fb` |
| `satS_saturates_and_agrees` | theorem | `Toy/FloatTier/CastStatements.lean:347` | `Classical.choice`, `Quot.sound`, `propext` | `838fa4149278bb63f964a7bd55726eaccf50518b56919b8371d60a98875da941` | `3c56e6517beb1e135dde25dc51be9c033ea7b0d445b4251caf50ec6b6418e8d3` |
| `satS_spec_iff` | theorem | `Toy/FloatTier/CastStatements.lean:466` | `Classical.choice`, `Quot.sound`, `propext` | `9eafd78b083cf5e1d8ef7df6d93ca0e8699ff907d789f3f7099775b7987851b0` | `3c56e6517beb1e135dde25dc51be9c033ea7b0d445b4251caf50ec6b6418e8d3` |
| `satU` | def | `Toy/FloatTier/Cast.lean:69` | `propext` | `4d034adb3d4fff3ab5209256488822ddbf217ebc0258af6fc1d833dd85bb96c8` | `69ba67611a67ee13cc743846c8b9325c95fee5e73405e307ae4e8102118353fb` |
| `satU_saturates_and_agrees` | theorem | `Toy/FloatTier/CastStatements.lean:268` | `Classical.choice`, `Quot.sound`, `propext` | `c3de6edf01fee09119e35a978a7001672365f7e801077e83673ed8baf2086e54` | `3abf30858a7950b4d47fbe7eb8ce4b49cc35c6c36037456c83a7ae40cc4dd588` |
| `satU_spec_iff` | theorem | `Toy/FloatTier/CastStatements.lean:425` | `Classical.choice`, `Quot.sound`, `propext` | `831834d6ea4e3522c906ac84a9bbd9d48aa647b7aa73488c23270d3d5fde8289` | `3abf30858a7950b4d47fbe7eb8ce4b49cc35c6c36037456c83a7ae40cc4dd588` |
| `satU_width_zero` | theorem | `Toy/FloatTier/CastExamples.lean:50` | `Classical.choice`, `Quot.sound`, `propext` | `f207cb5c35d6e3ebd91f6998d6a45580c7c0b3e53819c7cf2dcb29f9fa72dc7d` | `62cb29664e84fc8a307be9da8129379ef475729da6b1f8e999326da00519988d` |
| `signed_lower_guards_not_exact_F33` | theorem | `Toy/FloatTier/CastExamples.lean:228` | `Quot.sound`, `propext` | `02b1f9a95517cf93b78148e5c46be32d00e95685aa575a87735e4ebb828f4677` | `b4f426255a22354b90f1373b171599de141d97a7cb4dba26890fb095bc9ea96f` |
| `sound_tiers_disagree_on_bits` | theorem | `Toy/FloatTier/Statements.lean:153` | `Quot.sound`, `propext` | `0fdfe7978544ea185644ce046aec7945e4be8470403c9fad1bcec68f2f793175` | `11c92b2ec5f67f285c51505fd00a34522e8f972b7d6290a2adf83e20832544b3` |
| `sub` | def | `Toy/FloatTier/Base.lean:222` | `Quot.sound`, `propext` | `ad77d1e7f26b111118dd57f8bae31e7260c81c9b8c93f5aca0aa7f76c3239b36` | `69ba67611a67ee13cc743846c8b9325c95fee5e73405e307ae4e8102118353fb` |
| `sub_eqNsz_congr` | theorem | `Toy/FloatTier/Lemmas.lean:104` | `Classical.choice`, `Quot.sound`, `propext` | `d69c806fa17812cbcac08a8f7fc4ad1e440cd9c821850666d76ab97709ad865c` | `bb7544e84dbdd6b581bd8880b0a911cfb06f07395a76213105cab224f0c53148` |
| `tierBad` | def | `Toy/FloatTier/Instances.lean:111` | none | `717bdca745c1b5b3efb9089fa288f6b2f7aca567e176e1a33c0e5ee024888062` | `bab3623993752c087619e57f76dec4b2307bd716dea34956ed6ba1fb890b4ff7` |
| `tierCtfe` | def | `Toy/FloatTier/Sets.lean:159` | `Quot.sound`, `propext` | `717bdca745c1b5b3efb9089fa288f6b2f7aca567e176e1a33c0e5ee024888062` | `bab3623993752c087619e57f76dec4b2307bd716dea34956ed6ba1fb890b4ff7` |
| `tierExtraPay1` | def | `Toy/FloatTier/Instances.lean:115` | `Quot.sound`, `propext` | `df0da2ddda9412ffee1e65abb1f255981532288104b45450b7877ebf42548787` | `3af469b3e2b00db6958b15a18300b7483a8f11f5435d51ffd3db9b30c3ee1466` |
| `tierExtraPay1_sound_extra_not_noExtra` | theorem | `Toy/FloatTier/Counterexamples.lean:463` | `Quot.sound`, `propext` | `effeba3a34b9c8affec6ebf99d7423a972939a079c672508abe109e7fc6838a6` | `704f5b19d51565ea6aad8220e8becc219d8e953a84547e64f2eaf7a680e36287` |
| `tierOf` | def | `Toy/FloatTier/Sets.lean:130` | `Quot.sound`, `propext` | `7795f25532af70336876eecff85db4df3e4fea34eb29c5adcfe3dfa05beaa68e` | `57a365eafdaabc77973d37a05c936d49d03c5bfe1807d4bb2cd7917bf66f9353` |
| `tierOf_refinesS` | theorem | `Toy/FloatTier/Statements.lean:118` | `Quot.sound`, `propext` | `c48a5e9393ccb367c9239bfdfac41b8b1d1a2953e276d776902dc2580a7d5230` | `e3529f50c4d781e9273503203f54e56d704f43b3a7ecdad994dda123f360f45b` |
| `tierOf_sound` | theorem | `Toy/FloatTier/Statements.lean:82` | `Quot.sound`, `propext` | `44adff907e76755be793b84f8f761eabdaba64a00423b3abd08e4af7c1a94fb0` | `46587bd513765e89202a5f76314fbd35f30a93b81cf8da83ba5982462ab02e82` |
| `tierRunA` | def | `Toy/FloatTier/Sets.lean:162` | `Quot.sound`, `propext` | `717bdca745c1b5b3efb9089fa288f6b2f7aca567e176e1a33c0e5ee024888062` | `bab3623993752c087619e57f76dec4b2307bd716dea34956ed6ba1fb890b4ff7` |
| `tierSound_extra_irrelevant_of_p_eq_two` | theorem | `Toy/FloatTier/Counterexamples.lean:481` | `Quot.sound`, `propext` | `37264dcade574cad508509cb8dc45e5fe019bec0fd738cfc6445d83ba376311b` | `931678e74340137f0e624857846da61b2277e5f081c7ab51cc5d1ad491ebe561` |
| `tiers_agree_on_isNaN_zero_mul_inf` | theorem | `Toy/FloatTier/Counterexamples.lean:133` | `Quot.sound`, `propext` | `49b32285deb715517568552bb62b6cdf64a9b378a985d9050f359d9f05f80864` | `611ec9332a931f8b25ba29daebd427aa6f7ed51ced950d2fc04cba226c4a6643` |
| `totalKey` | def | `Toy/FloatTier/Base.lean:261` | `Quot.sound`, `propext` | `0e6b49e828afd5d7c45cb989d4124f15efcccf55e1bd9c9513a7da237fa8a3b2` | `69ba67611a67ee13cc743846c8b9325c95fee5e73405e307ae4e8102118353fb` |
| `trunc` | def | `Toy/FloatTier/Cast.lean:40` | `propext` | `0e6b49e828afd5d7c45cb989d4124f15efcccf55e1bd9c9513a7da237fa8a3b2` | `69ba67611a67ee13cc743846c8b9325c95fee5e73405e307ae4e8102118353fb` |
| `trunc_mem_range_iff_fails_at_inf` | theorem | `Toy/FloatTier/CastExamples.lean:74` | `Quot.sound`, `propext` | `f4faab9728c54e317dfbbadcb0a5d33ad9b00716d69845210f071ea65203625e` | `ea04215007ae68b0ccf504b6b77a8c042d0599bfb232fd2b0c5b4cc59f0719c4` |
| `trunc_mem_signed_range_iff` | theorem | `Toy/FloatTier/CastStatements.lean:100` | `Classical.choice`, `Quot.sound`, `propext` | `9e1251273b8ed6c68597aac50ecc17ba98e6afe1519a337b78f6ed304a1143cb` | `a4910ba7e007c1ac34bc428632a23b711e42419e87e43bf5c3b7c4e6350046b6` |
| `trunc_mem_unsigned_range_iff` | theorem | `Toy/FloatTier/CastStatements.lean:76` | `Classical.choice`, `Quot.sound`, `propext` | `8f8fd4e8dd7efe417e8cb0f17c20bb9955eeabc2148326373ba2204cd9fe9b48` | `5627e51e16a491ba677094b83b0f6d35f6cf215025ec332f42c7c908a20c4487` |
| `trunc_uval_of_not_finite` | theorem | `Toy/FloatTier/CastStatements.lean:58` | `propext` | `5dc0927d3007ae8cfba55cde7e05c88d27c16817aad474361a9c5a343438c449` | `8d53f2e55c852be622d5e786a6c5c78daef9d3f816f44406118da2025f2b40cf` |
| `twoPowRound` | def | `Toy/FloatTier/Cast.lean:88` | `Quot.sound`, `propext` | `afb89f65c9906fbd320e34fe4686bac060faf7966393150384a8dac41795a5e3` | `69ba67611a67ee13cc743846c8b9325c95fee5e73405e307ae4e8102118353fb` |
| `twoPowRound_of_fits` | theorem | `Toy/FloatTier/CastStatements.lean:43` | `Classical.choice`, `Quot.sound`, `propext` | `62a442becadfaad27fcf9d0d572215a1b663343a519be059975ce65d84948b10` | `2de74178643c82a7965a6a5b4b8dc2fb2e0cf40610b9412b858ae75d1b673a59` |
| `twoPowRound_of_not_fits` | theorem | `Toy/FloatTier/CastStatements.lean:51` | `Classical.choice`, `Quot.sound`, `propext` | `7a39b6420092d0a2b50536c37a4b7eab6b42228e506d9d77fe87b7be7df3c179` | `4826e9b327ed2a93cfde0cbd3fcd7b8547548d50fb2dc077754982a2944ef60f` |
| `two_pow_qneg_le_maxUnits` | theorem | `Toy/FloatTier/CastStatements.lean:33` | `Quot.sound`, `propext` | `5ca5a0fc63c3960b007a4ec430f5ab344fa6df2f8090d41955953744baf05284` | `054ec7470e2b61f7ff3c05ea143b915c5bb6d144a40f8bfd33000b8748fc7796` |
| `unsound_tier_breaks_agreement` | theorem | `Toy/FloatTier/Counterexamples.lean:399` | `Quot.sound`, `propext` | `eeb8dcef589d2823b16ee77ffe6b205ca2969d794d6f7b89157fed3f1a12459c` | `bd3ab555673d266460fe8d91fbf277532a0284621fe1e7ec32bad2c52cb88b9d` |
| `zero` | def | `Toy/FloatTier/Base.lean:138` | `Quot.sound`, `propext` | `8b09a326254d28a66d88ed8b0604b772ee38117e3def78a247b3486b519ef0f5` | `69ba67611a67ee13cc743846c8b9325c95fee5e73405e307ae4e8102118353fb` |

### Bounded evaluations (not proofs)

Before the statements were proved, their main claims were evaluated exhaustively with `#eval` in small formats; the evaluations are preserved in `lean/checks/BoundedChecks.lean`, outside the `Toy` library, and the results rest on the general proofs, not on these evaluations. `trunc-unsigned-open-interval`: formats `(e, p) = (3,3)`, `(3,2)`, `(2,3)`, all values, `W < 8`. `trunc-signed-open-interval`: formats `(3,3)`, `(3,2)`, `(4,3)`, all values, `k < 8`. `InOpenU W` and `InOpenS W` are false on every non-finite value: formats `(3,3)`, `(3,2)`, `(2,3)`, `W < 8`. `two-comparison-range-check-exact`: formats `(3,3)`, `(3,2)`, `(2,3)`, `(4,3)`, `(3,4)`, all values, `W < 12`. `max-as-float-guard-not-exact`: the guard `naiveCheckU W` by width, `W < 12`, in `(3,3)`, `(3,2)`, `(3,4)` and `(2,3)`. `saturating-conversion-saturates-and-agrees`: the seven unsigned conjuncts in `(3,3)`, `(3,2)`, `(2,3)`, `W < 8`. The signed lower-bound guard variants in `(3,3)`, `k < 8`. The congruence used by `observation-determinism-nan-or-zero` (`primSet` up to `ValEq`): format `(2,3)`, all operand pairs, with no extra payloads and with all extra payloads. Tier soundness, with no extra payloads and all operand pairs: `tierCtfe` and `tierRunA` in format `(2,3)`, and `tierRunA` in `(3,3)`. Each evaluation agrees with the corresponding theorem.

### Primary sources

Upstream files, each pinned to a full commit on the repository's default branch (for LLVM, the commit of the release tag `llvmorg-21.1.0`). The verbatim quotes under **Findings → Modelling bridges** cite `path@commit:A-B` line ranges in these files.

| Source | Repository | Commit | Path |
| :--- | :--- | :--- | :--- |
| Rust RFC 3514, float semantics (merged) | `rust-lang/rfcs` | `f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4` | `text/3514-float-semantics.md` |
| Rust core library documentation | `rust-lang/rust` | `26bfbf28f5f79dff333ce5a232f131b496ec9cfe` | `library/core/src/num/f32.rs`; `library/core/src/primitive_docs.rs` |
| The Rust Reference, operator expressions | `rust-lang/reference` | `5e6c977381e3cb5dcfdef97013bfae3317a181bf` | `src/expressions/operator-expr.md` |
| LLVM Language Reference Manual (`llvmorg-21.1.0`) | `llvm/llvm-project` | `3623fe661ae35c6c80ac221f14d85be76aa870f1` | `llvm/docs/LangRef.rst` |
| WebAssembly specification, numerics | `WebAssembly/spec` | `631890ee71035d9903fe5fd3a2b476bb82c76112` | `document/core/exec/numerics.rst` |
| CompCert | `AbsInt/CompCert` | `1670ae76afdb2546402898b6e9064d7229845d24` | `lib/Floats.v`; `lib/IEEE754_extra.v` |

Publications (bibliographic records checked; no statement of them is relied on, and the text of IEEE 754-2019 was not accessible):

- IEEE Standard for Floating-Point Arithmetic, IEEE Std 754-2019, DOI 10.1109/IEEESTD.2019.8766229.
- S. Boldo and G. Melquiond, "Flocq: A Unified Library for Proving Floating-Point Algorithms in Coq", 2011 IEEE 20th Symposium on Computer Arithmetic (ARITH 2011), DOI 10.1109/ARITH.2011.40.
- S. Boldo, J.-H. Jourdan, X. Leroy and G. Melquiond, "Verified Compilation of Floating-Point Computations", Journal of Automated Reasoning 54(2), 2015, DOI 10.1007/s10817-014-9317-x.
- A. Haas, A. Rossberg, D. L. Schuff, B. L. Titzer, M. Holman, D. Gohman et al., "Bringing the Web up to Speed with WebAssembly", Proceedings of the 38th ACM SIGPLAN Conference on Programming Language Design and Implementation (PLDI 2017), DOI 10.1145/3062341.3062363.

The base format files `Base.lean` and `Arith.lean` are copies, with the namespace renamed, of files of the published package `floating-point-algebraic-laws-reassociation-contraction-signed-zero-and-nan` of the same library; the copied ranges and the SHA-256 of the source files are recorded under **Findings → Model definitions, 1.1**. That package is cited for provenance and is neither a subject nor a Lean dependency.

### Observation dates

All evidence was acquired or revalidated on 2026-11-21: the build, the axiom audit and the hash record; the existence of each pinned commit on its repository's default branch (and of the LLVM release tag), checked with the GitHub API; the 42 verbatim quotes, re-compared line by line with the pinned files; and the bibliographic records of the four DOIs.

## Revalidation

Requirements: `elan` (so that `lake` selects the toolchain pinned in `lean/lean-toolchain`, `leanprover/lean4:v4.34.1`) and `python3`. No network access is needed after the toolchain is installed; there are no Lake dependencies.

**Primary check.** From the package directory:

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` never modifies the package: it copies `lean/` to a temporary directory and

1. runs `lake build` (the library `Toy`);
2. rejects any Lean source containing `sorry`, `admit`, `native_decide`, or an `axiom` declaration;
3. computes, with Lean's `collectAxioms`, the axioms of every declaration of the library and fails if any is outside `propext`, `Classical.choice`, `Quot.sound`;
4. for every Lean name referenced by `results.json` (fields `lean`, `lean_names`, `nonvacuity_witness_lean`, `positive_control_lean`, and hypothesis `counterexample`s) and every name recorded in `audit/statements.json`, recomputes the SHA-256 of the statement (the Lean `repr` of the declaration's type) and of its definition closure (for every package-local constant reachable from the statement through types, non-theorem values and inductive constructors: its name, the `repr` of its type, and, for non-theorems, the `repr` of its value; theorem bodies excluded), and compares both with `audit/statements.json`.

It exits 0 if and only if all checks pass, and prints `REVALIDATED`.

**Manual axiom listing.** From `lean/`:

```sh
lake build
lake env lean RevalidationAudit.lean
```

`RevalidationAudit.lean` is outside the `Toy` library target. It prints `#print axioms` output for each of the 221 declarations listed under **Evidence**; each line must report no axioms or a subset of `propext`, `Classical.choice`, `Quot.sound`.

**Bounded evaluations.** From `lean/`, after `lake build`:

```sh
lake env lean checks/BoundedChecks.lean
```

prints the exhaustive small-format evaluations described under **Evidence → Bounded evaluations (not proofs)**. They are evaluations, not proofs.

**Cheaper targeted checks.** To recheck one result after a change, build the library and run `#print axioms Toy.FloatTier.<name>` for that result, its counterexamples, its non-vacuity witnesses and its positive controls, and compare the statement text with the quote under **Findings**. A change to any definition in a result's closure changes its closure hash, which `support/revalidate.py` reports.

**What a passing check establishes.** It establishes that the theorems quoted under **Findings** are kernel-checked under the pinned toolchain with the recorded axioms and that their statements and definition closures are the recorded ones. It does not check the prose, the modelling bridges or the citations. To recheck a modelling bridge against a newer upstream revision, re-read the quoted line ranges of the files listed under **Evidence → Primary sources** at that revision.
