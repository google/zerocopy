<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Lean 4 IEEE-754 Floating-Point Semantics (FloatSpec, fp-lean, RFC 3514) and Cryptographic Constant-Time Verification (VCV-io, SampCert, ArkLib, Cryptol/SAW)

## Summary

Verifying Rust programs that manipulate IEEE-754 floating-point values, enforce
execution-cost or stack-depth bounds, or implement constant-time cryptographic
primitives requires reconciling three distinct semantic layers with Anneal's
small-step prefix refinement architecture (`Trusted.Refinement`,
`Trusted.StepResult`, and `Anneal.FunctionalTranslation`):

1. **Rust RFC 3514 Dual Floating-Point Semantics (`support/FloatProbe.lean`,
   `support/FloatSpecRFC3514Bridge.lean`):** Rust separates *bit-level scalar
   storage* (`f32`/`f64` loads, stores, `transmute`, `to_bits`/`from_bits`,
   `abs`, `neg`, and `copysign`, which must preserve all $2^{32}$ / $2^{64}$
   bit patterns including signaling NaNs and arbitrary NaN payloads) from
   *arithmetic operations* (`+`, `-`, `*`, `/`, `rem`), where non-NaN results
   are deterministic IEEE-754 rounded values while NaN results are demonic
   nondeterministic choices (`StepResult.choice .demonic`) over quiet NaNs with
   arbitrary sign and payload bits. Existing Lean 4 IEEE-754 libraries optimize
   for single-NaN reasoning, either by erasing NaN payloads during unpacking
   (`opencompl/fp-lean`) or by proving arithmetic theorems over a canonical-NaN
   subtype (`Beneficial-AI-Foundation/FloatSpec`'s `BinarySingleNaN`). We prove
   in Lean `v4.34.1` that `FloatSpec`'s two-tier representation (`FullFloat` vs.
   `StandardFloat`) and parameterized `default_nan` quiet-NaN handler bridge
   directly to Anneal's demonic RFC 3514 envelope, that an upstream defect in
   `FloatSpec`'s `Babs` (`F754_nan s pl => F754_nan s pl`, which fails to clear
   the sign bit on negative NaNs) is repaired by `Babs_FF` /
   `binary_float.Babs`, and that any NaN-payload-oblivious specification
   verified against a single-NaN model transfers soundly to the RFC 3514
   demonic-NaN machine whereas specifications asserting a canonical arithmetic
   NaN payload are provably rejected.
2. **Execution Cost, Stack Depth, and Constant-Time 2-Safety over
   `SmallStepMachine` (`support/CostCtProbe.lean`):** Instantiating the
   observation parameter `Obs` of `SmallStepMachine Prog State Obs Val` with a
   structured `StepObs` record (`cost : Nat`, `stackDelta : Int`,
   `leak : LeakEvent`) supports both unary resource bounds (`totalCost` and
   `peakStackDepth` inside `Language.SpecOn`) and relational 2-safety
   constant-time noninterference (`ConstantTime2Safety` over pairs of
   `BehaviorOf M p` prefixes) with **zero changes** to `trusted/lean/`. We
   verify a positive constant-time theorem for branchless selection
   (`ctSelectProg_is_constant_time` / `ctSelectXorBody_is_constant_time`) and a
   negative canary theorem (`branchSelectProg_not_constant_time` /
   `secretBranchBody_not_constant_time`) that rejects an isochronous
   secret-branching program whose instruction count and stack depth are
   identical to the branchless version.
3. **Cryptographic and Probabilistic Verification Bridges (`VCV-io`,
   `SampCert`, `ArkLib`, and `Cryptol`/`SAW`):** Inspecting
   `leanprover/SampCert` (`SLang`, `probWhile`, zCDP), `Verified-zkEVM/VCV-io`
   (`OracleComp`, `CostModel`, `ObservationOracle`, `Relational.Leakage`, and
   `Interop/Rust/Common.lean`'s `RustOracleComp`), `Verified-zkEVM/ArkLib`
   (`MeasuredProgram`), and Galois's `cryptol` / `saw-script` (`crux-mir`
   compositional verification via `CrucibleMethodSpecIR`) shows that Anneal's
   pure functional translation carrier `AeneasRes Val` embeds directly into
   `VCV-io`'s `RustOracleComp` result carrier (`Option (Except Unit Val)`) and
   collapses definitionally to `some (.ok (g s))` whenever Anneal's
   `SafeAndReturns` holds (`liftAeneasToOracle_sound`). Unlike `SAW`/`Cryptol`,
   which translate MIR to `saw-core` and trust external SMT-LIB `FloatingPoint`
   solvers (which enforce single-NaN canonicalization), Anneal discharges
   modular specification overrides (`FuncLang.SpecOn`) and symbolic execution
   (`translatePure` via kernel `rfl`) entirely inside the Lean 4 kernel.

## Applicability

This report governs three areas of Anneal's architecture and verification
roadmap:

- **`trusted/lean/` (`Trusted/Refinement.lean`, `Trusted/StepResult.lean`,
  `Trusted/MirAst.lean`, `Trusted/MirSemantics.lean`):**
  - Confirms that `Trusted.StepResult` (`step`, `choice`, `terminated`,
    `failed`), `Trusted.SmallStepMachine`, `Trusted.ReachesPrefix`, and
    `Trusted.BehaviorOf` require **no structural modifications** to express
    RFC 3514 demonic NaN nondeterminism, per-step instruction cost, call-stack
    depth high-water marks, or side-channel leakage traces.
  - Constrains future `f32`/`f64` additions to `Trusted.MirVal` and
    `Trusted.MirSemantics`: scalar storage (`PackedFloat32`/`PackedFloat64` or
    `BitVec 32`/`BitVec 64`) must retain all $2^{32}$/$2^{64}$ bit patterns for
    loads, stores, `transmute`, `to_bits`/`from_bits`, `abs`, `neg`, and
    `copysign`, while binary arithmetic Rvalues (`+`, `-`, `*`, `/`, `rem`) must
    emit `.choice .demonic` over quiet NaN bit patterns (`isQuietNaN = true`)
    whenever the IEEE-754 result is NaN.
- **`theory/` (`Anneal/FunctionalTranslation.lean` and downstream theory
  libraries):**
  - Guides the adoption of `Beneficial-AI-Foundation/FloatSpec` (and rejection
    of `opencompl/fp-lean` as a trusted dependency due to its inconsistent
    placeholder axioms) for IEEE-754 rounding and error-bound proofs in
    `theory/`, using the `FullFloat` (`FloatSpec.IEEE754.Binary.FullFloat`) <->
    `StandardFloat` (`BinarySingleNaN.binary_float`) bridge and the repaired
    `Babs_FF` / `Bcopysign` sign operations verified in
    `support/FloatSpecRFC3514Bridge.lean`.
  - Establishes the `StepObs` observation algebra (`cost`, `stackDelta`, `leak`)
    and `ConstantTime2Safety` relational predicate in `support/CostCtProbe.lean`
    as the template for `theory/` modules targeting WCET, stack-overflow
    absence, and cryptographic constant-time verification.
  - Defines the zero-axiom adapter (`liftAeneasResToRustOracle` and
    `liftAeneasToOracle_sound`) for lifting Rust functions verified via
    `Anneal.FunctionalTranslation` (`FuncLang`) into `VCV-io` (`OracleComp` /
    `RustOracleComp`) and `SampCert` (`SLang`) game-playing or differential
    privacy proofs.
- **`trusted/audit/` (`anneal-audit`):**
  - Reinforces the requirement that external Lean libraries imported into
    Anneal's proof environment pass `#print axioms` auditing (`propext`,
    `Classical.choice`, `Quot.sound` only, with zero `sorryAx` and zero custom
    axioms).

## Findings

### Finding 1: Rust RFC 3514 Dual Float Contract vs. `FloatSpec` and `fp-lean`

Basis: empirical + source

Rust's floating-point semantics (codified in RFC 3514, *Float Semantics*, and
the Rust Reference `r[expr.arith-logic]`) enforce a strict separation between
**bitwise storage operations** and **arithmetic operations** on `f32` and `f64`:

1. **Bitwise Storage and Sign Manipulation (`#74` Storage Contract):** Values of
   type `f32` and `f64` stored in MIR locals or memory occupy 32 or 64 bits and
   preserve their exact bit patterns across loads, stores,
   `core::mem::transmute`, `f32::to_bits`, `f32::from_bits`, `f32::abs`,
   `f32::neg` (unary `-`), and `f32::copysign`. In particular, `f32::abs`,
   `f32::neg`, and `f32::copysign` are specified as pure bit-manipulation
   operations on the sign bit (bit 31 for `f32`, bit 63 for `f64`) that preserve
   the exponent and all 23 (or 52) mantissa payload bits unchanged, even when
   the input is a signaling NaN or a quiet NaN with a custom payload.
2. **Arithmetic Demonic Quiet-NaN Nondeterminism:** For arithmetic operations
   (`+`, `-`, `*`, `/`, `rem`, `fma`, `sqrt`), if the mathematical IEEE-754
   result under round-to-nearest-ties-to-even (`RNE`) is a finite number or
   $\pm\infty$, the result is deterministic and bit-exact. If the IEEE-754
   result is `NaN` (for example, $0.0 / 0.0$, $\infty - \infty$, or any
   operation with a `NaN` operand), RFC 3514 specifies that the result is a
   **nondeterministic choice** over all quiet `NaN` bit patterns (`exp = 0xFF`,
   quiet bit $m_{22} = 1$, arbitrary sign bit $s \in \{\text{false},
   \text{true}\}$, and arbitrary lower 22-bit payload).

Why does this dual contract break naive use of standard IEEE-754 formalizations?
In `opencompl/fp-lean@c3124f3c23afb5a70efb90983015b99801985058`, the packed
bit-level type `PackedFloat e s` (`Fp/PackedFloat/Basic.lean:10-17`) stores
`sign : Bool`, `ex : BitVec e`, and `sig : BitVec s`, which can represent all
$2^{e+s+1}$ bit patterns. However, arithmetic in `fp-lean` (`PackedFloat.add` in
`Fp/Addition.lean`) first unpacks operands via `PackedFloat.unpack`
(`Fp/Unpacking.lean:88-96`) into `EUnpackedFloat (exponentWidth e s)
(sigWidth e s)`, which collapses all NaNs into a single payload-less constructor
`.NaN` (`Fp/UnpackedFloat/Basic.lean:33-38`), and then repacks via
`EUnpackedFloat.pack` (`Fp/Unpacking.lean:51-85`):

```lean
-- opencompl/fp-lean@c3124f3c23afb5a70efb90983015b99801985058
-- Fp/Unpacking.lean:51-57
def EUnpackedFloat.pack (f : EUnpackedFloat (exponentWidth e s) (sigWidth e s))
  : PackedFloat e s :=
  match f with
  | .NaN => PackedFloat.getNaN e s
```

where `PackedFloat.getNaN` (`Fp/Basic.lean:162-167`) always emits a single
canonical positive quiet NaN (`sign := false`, `ex := allOnes e`,
`sig := 1 <<< (s - 1)`). If Anneal used `EUnpackedFloat` as its runtime scalar
representation, it would violate `#74` (erasing NaN payloads across loads,
stores, and `abs`). Conversely, if Anneal used `EUnpackedFloat.pack` directly as
its arithmetic step relation, users could prove that `(0.0 / 0.0).to_bits() ==
0x7fc00000`, which is unsound in Rust because hardware platforms (x86 SSE/AVX
vs. ARMv8 vs. RISC-V) and LLVM optimizations produce different NaN signs and
payloads under RFC 3514.

In `support/FloatProbe.lean`, we resolve this tension inside Anneal's unmodified
`SmallStepMachine` and `StepResult` framework:

- **Bit-Preserving Storage (`PackedFloat32`):** `PackedFloat32`
  (`support/FloatProbe.lean:297-301`) stores `sign : Bool`, `ex : BitVec 8`, and
  `sig : BitVec 23`, round-tripping bijectively with `BitVec 32`
  (`ofBits_toBits`, `toBits_ofBits`, lines `315-332`). Bitwise operations
  (`PackedFloat32.abs`, `neg`, `copysign`, lines `376-391`) modify only `sign`.
- **Demonic Quiet-NaN Step Semantics (`rfc3514AddStep`, `floatStepFn`):** When
  an arithmetic operation (`FloatInstr.addRfc3514`) produces a NaN in the
  underlying single-NaN IEEE-754 model (`ieee754SingleNaNAdd`), the machine
  emits `.choice .demonic` over `QuietNaNBranch`
  (`support/FloatProbe.lean:458-493`), branching over every `qnan :
  PackedFloat32` satisfying `qnan.isQuietNaN = true`.
- **Kernel-Verified Positive and Negative Theorems
  (`support/FloatProbe.lean`):**
  1. `absProg_preserves_exact_nan_payload` (lines `602-621`): Proves via
     `FloatLang.SpecOn` that `FloatInstr.absBits` preserves the exact 23-bit
     NaN payload (`r.sig = x.sig`), clears the sign bit (`r.sign = false`), and
     preserves quiet/signaling NaN status (`r.isNaN = true`).
  2. `singleNaN_spec_sound_for_rfc3514` (lines `705-744`): Proves that any
     postcondition `Post : PackedFloat32 → PackedFloat32 → PackedFloat32 → Prop`
     satisfying `NaNPayloadOblivious Post` (meaning `Post x y q₁ ↔ Post x y q₂`
     whenever `q₁` and `q₂` are quiet NaNs) transfers automatically from a
     single-NaN IEEE-754 specification (`singleNaNAddSpec`) to the demonic
     RFC 3514 machine (`BehaviorOf floatMachine addProg ≤ FloatLang.SpecOn`).
  3. `rfc3514_rejects_canonical_nan_spec` (lines `772-805`): Negative canary
     theorem (`E-EVAL-02`) proving `¬ (BehaviorOf floatMachine addProg ≤
     canonicalNaNSpec)`: a specification asserting that `NaN + NaN` produces the
     canonical quiet NaN `0x7fc00000` is refuted by exhibiting the demonic
     branch `altQuietNaN32` (`sign := true`, `sig := 0x00400013#23`).

### Finding 2: `FloatSpec` Core, `Babs` Defect, and Lean `v4.34.1` Port

Basis: empirical + source

We audited both candidate Lean 4 floating-point repositories—`opencompl/fp-lean`
(`c3124f3c23afb5a70efb90983015b99801985058`) and
`Beneficial-AI-Foundation/FloatSpec`
(`158263e983ec3925e02b10f5b312498bf414e0f1`)—for soundness, axiom hygiene, and
compatibility with Lean `v4.34.1`:

| Property | `Beneficial-AI-Foundation/FloatSpec` (`158263e9`) | `opencompl/fp-lean` (`c3124f3c`) |
| :--- | :--- | :--- |
| **Theoretical Lineage** | Coq Flocq (`Core`, `Prop`, `IEEE754`, `Calc`) | Lean 4 `BitVec` + SMT-LIB `FloatingPoint` |
| **Upstream Toolchain** | `v4.28.0-rc1` (PR #8 targets `v4.34.0-rc2`) | `nightly-2026-01-14` |
| **Unproved `sorry` Count** | **0** across all 45 `.lean` files | **35** across `Fp/Theorems/` |
| **Custom `axiom` Count** | **0** (only `propext`, `Classical.choice`, `Quot.sound`) | **6**, including inconsistent `{P : Prop} : P` placeholders |
| **NaN Representation** | Two-tier: `FullFloat` (sign + payload) and `StandardFloat` (single NaN) | `PackedFloat` (bit-exact) and `EUnpackedFloat` (single `.NaN`) |

**Why `opencompl/fp-lean` cannot be imported into Anneal's proof environment:**
In `Fp/Theorems/PackedFloat/Packing.lean:15-17`, `fp-lean` declares two
unconditional polymorphic proof-placeholder axioms:

```lean
-- opencompl/fp-lean@c3124f3c23afb5a70efb90983015b99801985058
-- Fp/Theorems/PackedFloat/Packing.lean:15-17
axiom AxOrderEncode {P : Prop} : P
axiom AxRoundPreconditions {P : Prop} : P
```

Because `AxOrderEncode` and `AxRoundPreconditions` inhabit every proposition
`P : Prop` (including `False`), importing `Fp.Theorems.PackedFloat.Packing` into
a Lean environment renders that environment logically inconsistent (and would be
immediately rejected by `anneal-audit`). Four additional axioms in
`Fp/SmtLibSemantics.lean` (`smtLibRNE_unique`, `smtLibRTP_unique`,
`smtLibRTN_unique`, `smtLibRTZ_unique`) axiomatize uniqueness of SMT-LIB
rounding relations without proof. While `fp-lean`'s `PackedFloat` data layout is
useful as a design reference, `fp-lean` must not be added as a dependency.

**How `FloatSpec` models `FullFloat` vs. `StandardFloat`:**
`FloatSpec` (`Beneficial-AI-Foundation/FloatSpec` at commit
`158263e983ec3925e02b10f5b312498bf414e0f1`) contains **zero `sorry`s** and
**zero custom axioms** across its entire 45-file codebase. Its IEEE-754 layer
separates two representations:

1. **`FloatSpec.IEEE754.Binary.FullFloat` (`IEEE754/Binary.lean:28-33`):**
   ```lean
   inductive FullFloat (prec emax : Int) where
     | F754_zero (s : Bool) : FullFloat prec emax
     | F754_infinity (s : Bool) : FullFloat prec emax
     | F754_nan (s : Bool) (m : Pos) : FullFloat prec emax
     | F754_finite (s : Bool) (m : Pos) (e : Int) : FullFloat prec emax
   ```
   `FullFloat` preserves the sign bit `s : Bool` and positive integer payload
   `m : Pos` on `F754_nan s m`. Moreover, `FloatSpec`'s binary operations in
   `Binary.lean` (`Bplus`, `Bminus`, `Bmult`, `Bdiv` at lines `360-650`) are
   parameterized by an explicit NaN-payload selector
   `nan : Bool × Pos` (or a binary NaN handler), which determines the `(s, pl)`
   returned when an arithmetic operation produces `F754_nan`.
2. **`FloatSpec.IEEE754.BinarySingleNaN.StandardFloat` / `binary_float`
   (`FloatSpec/src/IEEE754/BinarySingleNaN.lean:51-101`):**
   Erases NaN sign and payload (`F754_nan : StandardFloat`), and defines
   `FF2B` / `B2FF` coercions (`Binary.lean:205-248`) that inject `StandardFloat`
   into `FullFloat` using a fixed default payload (`default_nan`). All
   high-level rounding, ULP, relative-error (`Prop/Relative.lean`), error-free
   transformation (`Prop/Plus_error.lean`), and Sterbenz (`Prop/Sterbenz.lean`)
   theorems are proved once over the generic format (`Core/Generic_fmt.lean`)
   and `BinarySingleNaN`.

**Upstream `FloatSpec` Defect Discovered and Repaired (`Babs` on `F754_nan`):**
During source inspection of `FloatSpec/src/IEEE754/Binary.lean:51-57`, we
discovered an upstream semantic bug in `FloatSpec`'s `FullFloat` absolute value
function `Babs`:

```lean
-- Beneficial-AI-Foundation/FloatSpec@158263e983ec3925e02b10f5b312498bf414e0f1
-- FloatSpec/src/IEEE754/Binary.lean:51-57
def Babs (prec emax : Int) (x : FullFloat prec emax) : FullFloat prec emax :=
  match x with
  | FullFloat.F754_zero _ => FullFloat.F754_zero false
  | FullFloat.F754_infinity _ => FullFloat.F754_infinity false
  | FullFloat.F754_nan s pl => FullFloat.F754_nan s pl
  | FullFloat.F754_finite _ m e => FullFloat.F754_finite false m e
```

Unlike `Bopp` (`Binary.lean:41-48`), which negates `s` on all four constructors
including `F754_nan (!s) pl`, upstream `Babs` returns `F754_nan s pl` with the
sign bit `s` **unchanged**! This violates IEEE 754-2019 §5.5.1 ("`abs(x)` copies
a floating-point operand `x` to a destination in the same format, setting the
sign bit to 0 (positive) ... even if `x` is a NaN") and Rust RFC 3514 /
`f32::abs`. In `support/FloatSpecRFC3514Bridge.lean` (`lines 586-596`), we prove
`Babs_upstream_fails_on_neg_nan`, demonstrating that upstream `Babs` leaves
`sign_FF (Babs_upstream prec emax (F754_nan true pl)) = true`. We then define
the repaired `Babs_FF` (`F754_nan _ pl => F754_nan false pl`), lift it to the
validity-bundled `binary_float.Babs`, and prove `sign_FF_Babs`,
`Babs_FF_idempotent`, `Babs_Bneg_FF`, `Bneg_FF_involutive`, `sign_FF_Bcopysign`,
and their bundled `binary_float` counterparts (`lines 598-808`).

**Porting `FloatSpec` to Lean `v4.34.1` (`FloatSpecRFC3514Bridge.lean`):**
Although `FloatSpec` depends on Mathlib (`Real`, `Rat`, `omega`/`linarith`), its
bit-level and integer-exponent core (`Core.Defs`, `Core.Zaux`, `Core.Digits`,
and `IEEE754.Binary`) uses only elementary integer and natural-number
arithmetic. When porting `Core.Digits.digits2_Pnat_correct`
(`FloatSpec/src/Core/Digits.lean:77-118`) to standalone Lean `v4.34.1`
(`support/FloatSpecRFC3514Bridge.lean:160-232`), the only compatibility
adjustments required were replacing Mathlib's `Id` monadic `run`/`pure` loop
wrapper and `omega` steps on `2 ^ (d + 1)` with standard Lean `v4.34.1`
`Nat.pow_succ` and `omega`.

Finally, `support/FloatSpecRFC3514Bridge.lean` (`lines 810-1202`) proves the
two-way bridge between `FloatSpec` and Anneal's `PackedFloat32` RFC 3514 model:

- `floatspec_non_nan_deterministic` (`lines 946-959`): Whenever a `FloatSpec`
  arithmetic operation yields a non-NaN result, the result is independent of the
  `default_nan` handler parameter.
- `floatspec_quiet_handler_in_rfc3514_envelope` (`lines 971-989`) and
  `rfc3514_envelope_realized_by_floatspec_handler` (`lines 995-1026`): Every
  quiet `default_nan` handler (`is_quiet_nan_payload prec emax pl = true`)
  falls inside Anneal's demonic RFC 3514 step envelope (`rfc3514_float_step`),
  and conversely every branch of `rfc3514_float_step` is realized by a valid
  `FloatSpec` quiet-NaN handler `(s, pl)`.
- `payload_oblivious_transfers_from_default_handler` (`lines 1038-1064`): Any
  postcondition `P : FullFloat prec emax → Prop` that is invariant across quiet
  NaN payloads (`NaNPayloadObliviousFF P`) holds across **all** branches of
  Anneal's demonic RFC 3514 envelope if and only if it holds for **one** fixed
  `FloatSpec` default quiet-NaN handler (`BinarySingleNaN`).
- `PackedFloat32.toFullFloat_neg`, `toFullFloat_abs`, and
  `toFullFloat_copysign` (`lines 1152-1202`): Commutativity of `PackedFloat32`
  bitwise sign operations with the `toFullFloat` interpretation into
  `FloatSpec`'s repaired `Bneg_FF`, `Babs_FF`, and `Bcopysign_FF`.

### Finding 3: Cost, Stack Depth, and Constant-Time 2-Safety (`CostCtProbe`)

Basis: empirical + inference

Anneal's `SmallStepMachine Prog State Obs Val` (`Trusted/StepResult.lean`) is
parameterized by an arbitrary per-step observation type `Obs : Type`, and
`ReachesPrefix` (`lines 155-184`) accumulates `tr : List Obs` across every
`.step obs s'` transition into `ExecOut Obs Val`. Currently,
`Trusted/MirSemantics.lean` instantiates `Obs` with `Unit`.

In `support/CostCtProbe.lean`, we prove that instantiating `Obs` with a
structured observation record `StepObs` (`lines 256-299`):

```lean
inductive LeakEvent where
  | none
  | branch (cond : Bool)
  | memAccess (addr : Nat)
  | varTimeDiv (divisor : Nat)
  deriving DecidableEq, Repr

structure StepObs where
  cost       : Nat
  stackDelta : Int
  leak       : LeakEvent
  deriving DecidableEq, Repr
```

simultaneously supports three quantitative and security verification domains
without modifying a single line of `Trusted.Refinement` or `Trusted.StepResult`:

1. **Unary Worst-Case Execution Cost (`totalCost`) and Peak Call-Stack Depth
   (`peakStackDepth`):**
   - `totalCost : List StepObs → Nat` sums `e.cost` along a finite prefix trace.
   - `curStackDepth (cur : Int) : List StepObs → Int` and
     `peakStackDepth (init : Int) : List StepObs → Int` track the current and
     high-water-mark stack frame depth across `pushFrame` (`+bytes`) and
     `popFrame` (`-bytes`) transitions.
   - In `boundedStackSelectProg_cost_and_stack_bound`
     (`support/CostCtProbe.lean:517-538`), we verify via `CostCtLang.SpecOn`
     that a 3-instruction subroutine
     (`[.pushFrame 16, .ctSelect, .popFrame 16]`) is safe
     (`out.outcome.isSafe`), terminates with the functional result
     `if init.secretCond then init.secretA else init.secretB`, incurs
     worst-case cost `totalCost out.trace ≤ 3`, never exceeds stack depth
     `peakStackDepth 0 out.trace ≤ 16`, and restores the stack pointer
     (`curStackDepth 0 out.trace = 0`).
2. **Compiler Pass Cost-Scaling Refinement (`compiler_cost_scaling_bound`):**
   - When a compiler pass lowers a source trace `tr_src` with verified cost
     bound `totalCost tr_src ≤ B` to a target trace `tr_tgt` with per-step cost
     expansion factor at most `k` (`totalCost tr_tgt ≤ k * totalCost tr_src`),
     `compiler_cost_scaling_bound` (`support/CostCtProbe.lean:549-554`) bridges
     the bound to `totalCost tr_tgt ≤ k * B`.
3. **Relational 2-Safety Constant-Time Noninterference
   (`ConstantTime2Safety`):**
   - Because constant-time execution is a **2-safety hyperproperty** over pairs
     of traces rather than a unary trace property, it cannot be stated as a
     single `BehaviorOf M p ≤ L.SpecOn pre post` judgment over one `ExecQuery`.
     However, because `BehaviorOf M p` exposes the exact prefix behavior
     `(BehaviorOf M p ⟨s, steps⟩).val hDef out` at every initial state `s` and
     step budget `steps`, we define `ConstantTime2Safety M p` directly over
     `BehaviorOf M p` (`support/CostCtProbe.lean:573-586`): for any two initial
     states `s₁, s₂` satisfying `PubEquiv s₁ s₂` and any step budget `steps`,
     both prefix behaviors are defined (`isSafe`) and every pair of reachable
     outputs `out₁, out₂` satisfies `leakageTrace out₁.trace =
     leakageTrace out₂.trace` and `totalCost out₁.trace = totalCost out₂.trace`.
   - **Positive Constant-Time Theorem (`ctSelectProg_is_constant_time` /
     `ctSelectXorBody_is_constant_time`, `lines 597-643`):** Proves that the
     branchless select program `ctSelectProg` satisfies `ConstantTime2Safety`
     across all step budgets and secret inputs.
   - **Negative Canary Theorem (`branchSelectProg_not_constant_time` /
     `secretBranchBody_not_constant_time`, `lines 663-702`):** Proves
     `¬ ConstantTime2Safety costCtMachine branchSelectProg`. Crucially,
     `branchSelectProg` executes in the **exact same number of steps (`1`)**,
     incurs the **exact same instruction cost (`totalCost = 1`)**, uses the
     **exact same stack depth (`0`)**, and computes the **exact same functional
     result** as `ctSelectProg`. A naive step-count or cost-only notion of
     constant time would falsely accept `branchSelectProg`, whereas
     `ConstantTime2Safety` rejects it because its `leakageTrace` emits
     `[.branch true] ≠ [.branch false]` into the branch predictor /
     instruction-pointer trace.

### Finding 4: Cryptographic Bridges (`VCV-io`, `SampCert`, and `ArkLib`)

Basis: empirical + source

We inspected three active Lean 4 cryptographic and probabilistic verification
repositories to determine how Rust functions verified in Anneal (`MirLang` /
`FuncLang`) can plug into higher-level cryptographic game-playing,
zero-knowledge soundness, or differential privacy proofs:

1. **`Verified-zkEVM/VCV-io@aae1c9cbd6c00311091d691b74f2d0032d76d9bd`
   (`v4.35.0`, 0 `sorry`s, 0 custom axioms in `VCVio/`):**
   - `VCVio/OracleComp/OracleComp.lean` models probabilistic and oracle-querying
     computations as a free monad `OracleComp spec α` (`pure`, `queryBind`),
     interpreted into sub-probability distributions via `evalDist`
     (`VCVio/EvalDist/Monad/Basic.lean`) and stateful oracle handlers via
     `simulateQ` (`VCVio/OracleComp/SimSemantics/SimulateQ.lean`).
   - `VCVio/OracleComp/QueryTracking/CostModel.lean` and
     `ObservationOracle.lean` instrument oracle computations with cost counters
     and side-channel leakage observations, while
     `VCVio/ProgramLogic/Relational/Leakage.lean:56-60` defines relational trace
     noninterference (`TraceNoninterference`), matching our
     `ConstantTime2Safety` predicate in `support/CostCtProbe.lean`.
   - Most importantly for Anneal, `VCV-io` already contains an explicit Rust
     interoperability layer (`Interop/Rust/Common.lean`,
     `Interop/Rust/Run.lean`, `Interop/Hax/Bridge.lean`, and
     `Interop/Aeneas/README.md`). In `Interop/Rust/Common.lean:75-76`, `VCV-io`
     defines:
     ```lean
     -- Verified-zkEVM/VCV-io@aae1c9cbd6c00311091d691b74f2d0032d76d9bd
     -- Interop/Rust/Common.lean:75-76
     abbrev RustOracleComp (spec : OracleSpec ι) (α : Type) : Type :=
       ExceptT Error (OptionT (OracleComp spec)) α
     ```
     where `ExceptT Error (OptionT M) α` has underlying carrier
     `M (Option (Except Error α))`:
     - `.ok v` maps to `pure (some (.ok v))`,
     - runtime panic/assertion failure maps to `pure (some (.error err))`, and
     - non-termination or partiality maps to `pure none` (`OptionT.fail`).
   - In `Interop/Hax/Bridge.lean:87-120`, `VCV-io` bridges Hax's 3-constructor
     `Result α` (`.ok v`, `.fail err`, `.div`) into `RustOracleComp` via
     `liftResult` and proves in `Interop/Hax/CenteredBinomial.lean` that an
     extracted Rust ML-KEM (FIPS 203) centered binomial sampler `cbd2` equals
     the mathematical binomial distribution on `Fin 3329`. Meanwhile,
     `Interop/Aeneas/README.md` notes that the Aeneas backend was left as a
     planned stub awaiting a Lean 4 Aeneas translation bridge.
2. **`leanprover/SampCert@a2c53bb5ff790e729e252958060699b7eff898b9`
   (`v4.34.1`, 0 `sorry`s, 0 custom axioms):**
   - Formalizes probabilistic algorithms in `SLang α := PMF α` (`ENNReal`-valued
     sub-probability mass functions in `SampCert/SLang.lean`), unbounded while
     loops via `probWhile` (`SampCert/Foundations/While.lean`), and pure,
     approximate, and zero-concentrated differential privacy (`zCDP` in
     `SampCert/DifferentialPrivacy/ZeroConcentrated/DP.lean`) for discrete
     Gaussian (`Samplers/GaussianGen/Properties.lean`) and Laplace samplers.
   - Any deterministic Rust function `g : MirState → MirVal` verified as total
     and panic-free in Anneal lifts into `SLang MirVal` as the Dirac point mass
     `SLang.pure (g s)`.
3. **`Verified-zkEVM/ArkLib@bc367f8d53f603a48c5502e1ad7d39b7b3be725c`
   (`v4.34.1`, 0 custom axioms, ~500 `sorry`s in WIP polynomialIOP modules):**
   - Builds interactive oracle reductions (`IOR`) and polynomial IOPs on top of
     `VCV-io`'s `OracleComp`, adding `MeasuredProgram.lean`
     (`ArkLib/Data/OracleComp/MeasuredProgram.lean`) for composing query-cost
     measures across multi-round protocols.

**Kernel-Verified Bridge from `FuncLang` to `VCV-io`'s `RustOracleComp`:**
In `support/CostCtProbe.lean` (`lines 730-807`), we embed Anneal's
`AeneasRes Val` (`.ok v`, `.inapplicable`, `.fail`), `FuncLang`, and `π_func`
from `theory/Anneal/FunctionalTranslation.lean:73-120` and define
`liftAeneasResToRustOracle : AeneasRes α → Option (Except Unit α)`:

```lean
def liftAeneasResToRustOracle {α : Type} : AeneasRes α → Option (Except Unit α)
  | .ok v         => some (.ok v)
  | .fail         => some (.error ())
  | .inapplicable => none
```

We then prove `liftAeneasRes_eq_ok_of_safeAndReturns` /
`liftAeneasToOracle_sound` (`lines 784-802`, depending on **zero axioms**):
whenever a pure functional model `f : MirState → AeneasRes MirVal` produced by
`Anneal.FunctionalTranslation.translate` is proved safe and terminating on input
state `s` (`f s = .ok (g s)`), its `RustOracleComp` lift reduces definitionally
to `some (.ok (g s))`, discharging `VCV-io`'s `OptionT`/`ExceptT` error layers
and yielding a pure computation that composes directly with `VCV-io` oracle
games and `SampCert` `SLang` distributions.

### Finding 5: `Cryptol` and `SAW` (`crux-mir`) Architectural Comparison

Basis: source + inference

We inspected Galois's `cryptol` (`GaloisInc/cryptol` at commit
`76f7fabbec7e3f184f15b408b34619ad37a36ec8`) and `saw-script`
(`GaloisInc/saw-script` at commit `27a7ae98256544b55a7a3ce4ce620c1a7889713b`)
to compare how the Cryptol/SAW toolchain verifies Rust MIR (`mir_verify`) and
models IEEE-754 floating-point arithmetic against Anneal's architecture:

1. **Compositional MIR Verification via `CrucibleMethodSpecIR` vs. Anneal's
   `FuncLang` / `MirLang` Refinement:**
   - In `saw-script` (`saw-central/src/SAWCentral/Crucible/MIR/Builtins.hs`,
     `SAWCentral/Crucible/Common/MethodSpec.hs`, and `crux-mir-comp/DESIGN.md`),
     `mir_verify` symbolically executes `mir-json` CFGs using `crux-mir`
     (Crucible's MIR engine) to build `saw-core` Functional Intermediate
     Representation terms (`SC.Term`), and checks equivalence against a
     Cryptol specification (`{{ f x == ... }}`) by dispatching verification
     conditions through `What4` to external SMT solvers (Z3, CVC5, Yices).
   - Once a Rust function is verified (or assumed via `mir_unsafe_assume_spec`),
     `mir_verify` returns a `MIRMethodSpec` (`CrucibleMethodSpecIR`) containing
     `_csPreState` (points-to and symbolic variable preconditions) and
     `_csPostState` (postconditions and return-value bindings). When verifying a
     caller, the user passes `[callee_spec]` in the `overrides` list of
     `mir_verify`; Crucible matches the callee's `DefId` and replaces symbolic
     execution of the callee's MIR body with the `CrucibleMethodSpecIR` summary
     (`doc/rust-verification-with-saw/`).
   - **How Anneal achieves the same compositional ergonomics without external
     solvers:** In `theory/Anneal/FunctionalTranslation.lean`, Anneal's
     plan-guided shallow evaluator `translatePure (computePlan body) body`
     symbolically executes a `MirBody` inside Lean and reduces on symbolic
     inputs by **kernel `rfl`** (the First Futamura Projection), while
     `evalSym_sound` proves once by structural induction on `plan : TransPlan`
     that `Abstracts FuncLang MirLang π_func (evalSym plan body) body` holds for
     every `plan` and `body`. Compositional callee overrides (`CallPure2` and
     general function calls) substitute the callee's verified `FuncLang`
     behavior directly via monotonicity of `π_func` (`monotone_π_func`) and
     transitivity of `Trusted.Preorder.le_trans`, replacing `saw-script`'s
     unverified Haskell symbolic execution engine + external SMT solver in the
     TCB with Lean's small kernel.
2. **Cryptol's `Float e p` (`lib/Float.cry`) vs. Rust RFC 3514 NaN Semantics:**
   - In `GaloisInc/cryptol`'s `lib/Float.cry` (commit `76f7fabbec7e`),
     Cryptol defines parameterized IEEE-754 floating-point types `primitive type
     Float : # -> # -> *` (`Float32 = Float 8 24`, `Float64 = Float 11 53`)
     backed by What4's SMT-LIB `FloatingPoint` theory (`fpAdd`, `fpSub`,
     `fpMul`, `fpDiv`, `fpFMA`, `fpSqrt`, `fpAbs`).
   - Crucially, `lib/Float.cry:35-38` and `252-265` document two fundamental
     mismatches with Rust's RFC 3514 bitwise/arithmetic contract:
     ```cryptol
     // GaloisInc/cryptol@76f7fabbec7e3f184f15b408b34619ad37a36ec8/lib/Float.cry:35-38
     /** Note that using `==` and `!=` on floating point numbers works a bit
         unintuitively: they specify semantic equality, which means that all
         `NaN` values are considered equal to each other, and before comparing
         the numbers are normalized, so `+0.0` and `-0.0` are equal! ... */

     // lib/Float.cry:253-265
     /** Convert a floating point number into the sequence of bits matching its
         IEEE-754 representation. Since the internal representation of floating
         point numbers does not track exact bit values of NaN payloads, calling
         this function on NaN returns the canonical NaN bit representation, matching
         the definition of `fpNaN`.
         WARNING: Not currently implemented in the symbolic simulator backend. */
     primitive fpToBits : {e, p} (ValidFloat e p) => Float e p -> [e + p]
     ```
   - Because SMT-LIB's `(_ FloatingPoint eb sb)` sort identifies all `NaN`
     values into a single abstract element, Cryptol's `Float e p` cannot track
     NaN sign or payload bits across bitwise operations (`fpAbs`, `fpToBits`,
     `fpFromBits`), and `fpToBits` / `fpFromBits` are not even implemented in
     the symbolic simulator backend! This confirms why Anneal's dual model
     (bit-exact `PackedFloat32`/`FullFloat` for storage + demonic quiet-NaN
     choice bridged to `FloatSpec`'s `BinarySingleNaN` for payload-oblivious
     arithmetic) is strictly more faithful to Rust's RFC 3514 semantics than an
     SMT-LIB `FloatingPoint` encoding.

## Boundaries

To preserve Anneal's `trusted/` minimalism and zero-axiom kernel verification
guarantee (`PRINCIPLES.md`), the following boundaries apply:

1. **No Floating-Point Rounding Machinery in `trusted/lean/`:**
   `trusted/lean/` must only state the primitive operational contract of Rust
   MIR (`PackedFloat32`/`PackedFloat64` bit storage, sign-bit `abs`/`neg`/
   `copysign`, and the RFC 3514 `.choice .demonic` quiet-NaN envelope around
   IEEE-754 rounded arithmetic). All generic floating-point formats, ULP
   algebra, error-free transformations, Sterbenz lemmas, and `FullFloat` <->
   `StandardFloat` transfer proofs (`support/FloatSpecRFC3514Bridge.lean`)
   belong in `theory/`.
2. **Do Not Import `opencompl/fp-lean`:**
   Because `opencompl/fp-lean@c3124f3c23afb5a70efb90983015b99801985058` declares
   inconsistent placeholder axioms (`AxOrderEncode {P : Prop} : P` and
   `AxRoundPreconditions {P : Prop} : P` in
   `Fp/Theorems/PackedFloat/Packing.lean:15-17`), it must never be imported into
   Anneal's `trusted/` or `theory/` Lake packages.
3. **Upstream `FloatSpec` `Babs` Must Not Be Used Unpatched on `FullFloat`:**
   If `Beneficial-AI-Foundation/FloatSpec` is imported or vendored into
   `theory/`, upstream `FloatSpec.IEEE754.Binary.Babs`
   (`FloatSpec/src/IEEE754/Binary.lean:51-57`) must be replaced or wrapped by
   `Babs_FF` (`support/FloatSpecRFC3514Bridge.lean:598-604`) so that `F754_nan s
   pl` maps to `F754_nan false pl` in accordance with IEEE 754-2019 §5.5.1 and
   Rust RFC 3514.
4. **Hardware Microarchitectural Leakage Lies Outside the ISA Step Model:**
   `ConstantTime2Safety` in `support/CostCtProbe.lean` proves constant-time
   noninterference at the MIR / abstract-machine transition level (verifying
   that control-flow branch conditions, memory access addresses, variable-time
   arithmetic operands, and abstract instruction costs are independent of secret
   inputs). Guaranteeing preservation of constant-time noninterference across
   LLVM code generation (`rustc` backend optimizations that might introduce
   branches on `bool` masks) requires either verified assembly inspection or
   compiler-barrier intrinsics (`core::hint::black_box` / inline assembly),
   which lie outside `MirPhase::Runtime(PostCleanup)`.

## Evidence

### Local Kernel-Verified Lean `v4.34.1` Probes

All three standalone Lean `v4.34.1` files in `support/` compile with zero
warnings, zero `sorry`s, and zero custom axioms under Lean `v4.34.1`
(`lean -j1 -M1024`):

| Support File | Lines | Bytes | SHA-256 Digest |
| :--- | ---: | ---: | :--- |
| [`support/FloatProbe.lean`](support/FloatProbe.lean) | 811 | 30,390 | `02fa416ddd585e8e992dd01d9e4515b7d9795c4d55e27c52365010c939d9e840` |
| [`support/FloatSpecRFC3514Bridge.lean`](support/FloatSpecRFC3514Bridge.lean) | 1,210 | 46,730 | `1be6c444642f30b2d0f048874a42c785e7f9399be0c4605bcb62cf930d9bf917` |
| [`support/CostCtProbe.lean`](support/CostCtProbe.lean) | 827 | 31,537 | `aa97fcdeefe2a555293c8ad1b5d240f2f50a5f7643bf830365a6b6581dbd1e64` |

#### 1. Declarations and Theorems in `support/FloatProbe.lean`

| Declaration / Theorem | Lines | Role | `#print axioms` Footprint |
| :--- | :--- | :--- | :--- |
| `Anneal.FloatProbe.PackedFloat32` | `297-301` | 32-bit IEEE-754 storage struct (`sign : Bool`, `ex : BitVec 8`, `sig : BitVec 23`) | Data definition |
| `PackedFloat32.ofBits_toBits`, `toBits_ofBits` | `315-332` | Bijective 32-bit storage round-trip with `BitVec 32` | `[propext, Quot.sound]` |
| `PackedFloat32.abs`, `neg`, `copysign` | `376-391` | Bit-exact sign manipulation preserving exponent and 23-bit NaN payload | Computable definitions |
| `QuietNaNBranch`, `rfc3514AddStep` | `458-493` | RFC 3514 demonic quiet-NaN step relation (`.choice .demonic`) | Definitions |
| `floatMachine_total`, `floatMachine_inhabitedDemonic`, `floatMachine_wellFormed` | `541-583` | `TotalStep`, `InhabitedDemonic` (witnessed by `canonicalQuietNaN32`), and universal `WellFormed` | `[propext, Quot.sound]` |
| `absProg_preserves_exact_nan_payload` | `602-621` | **Positive Theorem 1 (`#74`):** `absBits` preserves custom NaN payload bits and clears sign | `[propext, Quot.sound]` |
| `singleNaN_spec_sound_for_rfc3514` | `705-744` | **Positive Theorem 2 (`A-TYPE-10`):** Any `NaNPayloadOblivious` postcondition transfers from single-NaN `FloatSpec`/`fp-lean` to RFC 3514 demonic-NaN machine | `[propext, Quot.sound]` |
| `rfc3514_rejects_canonical_nan_spec` | `772-805` | **Negative Canary (`E-EVAL-02`):** Refutes `canonicalNaNSpec` on `NaN + NaN` under RFC 3514 | `[propext, Quot.sound]` |

#### 2. Declarations and Theorems in `support/FloatSpecRFC3514Bridge.lean`

| Declaration / Theorem | Lines | Role | `#print axioms` Footprint |
| :--- | :--- | :--- | :--- |
| `Anneal.FloatSpecBridge.Core.Digits.digits2_Pnat_correct` | `189-232` | Ported `FloatSpec` binary digit-width bound $2^d \le n < 2^{d+1}$ (`Core/Digits.lean:77-118`) | `[propext, Classical.choice, Quot.sound]` |
| `FullFloat`, `StandardFloat`, `FF2B`, `B2FF` | `258-464` | Ported `FloatSpec` two-tier IEEE-754 representation (`IEEE754/Binary.lean`, `BinarySingleNaN.lean`) | Definitions |
| `binaryFloatToFullFloat_fullFloatToBinaryFloat`, `fullFloatToBinaryFloat_binaryFloatToFullFloat` | `520-564` | Round-trip theorems between `BinarySingleNaN.binary_float` and `Binary.FullFloat` | `[propext, Quot.sound]` |
| `Babs_upstream_fails_on_neg_nan` | `586-596` | **Upstream Defect Proof:** Demonstrates that upstream `FloatSpec` `Babs` (`Binary.lean:51-54`) leaves `sign_FF = true` on negative NaNs | `[propext]` |
| `Babs_FF`, `sign_FF_Babs`, `Babs_FF_idempotent`, `Babs_Bneg_FF`, `Bneg_FF_involutive`, `sign_FF_Bcopysign` | `598-680` | Repaired `FullFloat` sign operations and algebraic laws on all finite, infinite, and NaN inputs | `[]` / `[propext]` |
| `binary_float.Bsign_Babs`, `Babs_idempotent`, `Babs_Bneg`, `Bneg_involutive`, `Bsign_Bcopysign` | `742-808` | Bundled `binary_float` sign-operation theorems preserving `valid_binary` | `[propext, Quot.sound]` |
| `floatspec_non_nan_deterministic` | `946-959` | Non-NaN `FloatSpec` results are independent of the `default_nan` handler | `[propext]` |
| `floatspec_quiet_handler_in_rfc3514_envelope` | `971-989` | Every quiet `FloatSpec` `default_nan` handler falls inside Anneal's demonic RFC 3514 envelope | `[propext]` |
| `rfc3514_envelope_realized_by_floatspec_handler` | `995-1026` | Every demonic branch of Anneal's RFC 3514 envelope is realized by a valid `FloatSpec` quiet-NaN handler | `[propext]` |
| `payload_oblivious_transfers_from_default_handler` | `1038-1064` | Equivalence between single-handler `FloatSpec` verification and universal RFC 3514 verification for `NaNPayloadObliviousFF` specs | `[propext]` |
| `PackedFloat32.toFullFloat_neg`, `toFullFloat_abs`, `toFullFloat_copysign` | `1152-1202` | Commutativity of `PackedFloat32` bit-level sign operations with `FloatSpec`'s repaired `FullFloat` operations | `[propext, Quot.sound]` |

#### 3. Declarations and Theorems in `support/CostCtProbe.lean`

| Declaration / Theorem | Lines | Role | `#print axioms` Footprint |
| :--- | :--- | :--- | :--- |
| `Anneal.CostCtProbe.LeakEvent`, `StepObs`, `totalCost`, `curStackDepth`, `peakStackDepth`, `leakageTrace` | `256-299` | Observation algebra for instruction cost, call-stack depth delta, and side-channel leakage | Definitions |
| `costCtMachine`, `costCtMachine_total`, `costCtMachine_inhabitedDemonic`, `costCtMachine_wellFormed` | `353-409` | Small-step machine with stack frames and branchless vs. branching select; universal `WellFormed` | `[propext]` |
| `boundedStackSelectProg_cost_and_stack_bound` | `517-538` | **Positive Theorem 1 (`A-BEH-04`–`06`):** Simultaneous proof of functional return, `totalCost ≤ 3`, and `peakStackDepth ≤ 16` via `SpecOn` | `[propext]` |
| `compiler_cost_scaling_bound` | `549-554` | **Positive Theorem 2 (`A-BEH-06`):** Cost-scaling bridge for compiler passes (`totalCost tr_tgt ≤ k * B`) | `[]` |
| `ConstantTime2Safety` | `573-586` | Relational 2-safety constant-time hyperproperty over pairs of `BehaviorOf M p` prefixes | Definition |
| `ctSelectProg_is_constant_time`, `ctSelectXorBody_is_constant_time` | `597-643` | **Positive Theorem 3 (`A-BEH-12`):** Branchless select satisfies `ConstantTime2Safety` for all step budgets | `[propext, Quot.sound]` |
| `branchSelectProg_not_constant_time`, `secretBranchBody_not_constant_time` | `663-702` | **Negative Canary (`E-EVAL-02`):** Rejects isochronous secret-branching select (`[.branch true] ≠ [.branch false]`) | `[propext]` |
| `AeneasRes`, `FuncLang`, `π_func`, `monotone_π_func`, `liftAeneasResToRustOracle` | `730-778` | Embedding of `Anneal.FunctionalTranslation` core and `VCV-io` `RustOracleComp` carrier lift | Definitions / `[]` |
| `liftAeneasRes_eq_ok_of_safeAndReturns`, `liftAeneasToOracle_sound` | `784-802` | **Positive Theorem 4 (`A-BEH-14`, `A-BEH-18`):** `SafeAndReturns` collapses `liftAeneasResToRustOracle` to `some (.ok (g s))` | `[]` |

### External Repository Evidence

Full file inventories and SHA-256 digests are recorded in
[`support/source-manifest.json`](support/source-manifest.json). Key primary
source citations:

| Repository (`Commit`) | Inspected File (`Lines`) | SHA-256 Digest | Cited Fact |
| :--- | :--- | :--- | :--- |
| `Beneficial-AI-Foundation/FloatSpec` (`158263e983ec3925e02b10f5b312498bf414e0f1`) | `FloatSpec/src/IEEE754/Binary.lean:28-57, 205-248, 360-650` | `a2e9031cdc1a5759789271b49e95d4c772bdae482b00b8d00181935e45cb77f8` | `FullFloat` (`F754_nan s m`), upstream `Babs` bug at lines `51-54`, `FF2B`/`B2FF` bridges, and `nan`-parameterized `Bplus`/`Bmult` |
| `Beneficial-AI-Foundation/FloatSpec` (`158263e983ec3925e02b10f5b312498bf414e0f1`) | `FloatSpec/src/IEEE754/BinarySingleNaN.lean:51-101` | `5227e950b14e3a5562d0aff551138ad3e5436dd1ece66f22e8c3cb1a7e756f22` | Canonical single-NaN `StandardFloat` and `binary_float` arithmetic |
| `Beneficial-AI-Foundation/FloatSpec` (`158263e983ec3925e02b10f5b312498bf414e0f1`) | `FloatSpec/src/Core/Digits.lean:77-118` | `62bccb1f2ba2dbb6fd64524f0c9d183940aaf1a6480a6df61434d7b47e88d5f9` | `digits2_Pnat` and `digits2_Pnat_correct` binary digit-width theorems |
| `opencompl/fp-lean` (`c3124f3c23afb5a70efb90983015b99801985058`) | `Fp/Unpacking.lean:51-96` | `4e71deed41d1fb36f150e0ccb7bf740e2b74350b1042cb423b6fea98b85836f7` | `PackedFloat.unpack` -> `EUnpackedFloat.pack` collapses all NaNs to `PackedFloat.getNaN` |
| `opencompl/fp-lean` (`c3124f3c23afb5a70efb90983015b99801985058`) | `Fp/Theorems/PackedFloat/Packing.lean:15-17` | `9ff0d0d4f8f6a362634cc77ea4835b78c0b960aeb136f44f5d3d4958c36888f3` | Inconsistent placeholder axioms `AxOrderEncode {P : Prop} : P` and `AxRoundPreconditions {P : Prop} : P` |
| `Verified-zkEVM/VCV-io` (`aae1c9cbd6c00311091d691b74f2d0032d76d9bd`) | `Interop/Rust/Common.lean:75-76` | `9e77af9c9c3ae507e0996003446533fc0996675745c09b6501a7cbd768736642` | `RustOracleComp spec α := ExceptT Error (OptionT (OracleComp spec)) α` |
| `Verified-zkEVM/VCV-io` (`aae1c9cbd6c00311091d691b74f2d0032d76d9bd`) | `Interop/Hax/Bridge.lean:87-120` | `b09aaa44806578d5ff4e2d838a16b4471edeea52b6a2c3de44f2cecee188e9db` | `liftResult` and `runPure` lifting 3-valued Rust extraction results into `RustOracleComp` |
| `Verified-zkEVM/VCV-io` (`aae1c9cbd6c00311091d691b74f2d0032d76d9bd`) | `VCVio/ProgramLogic/Relational/Leakage.lean:56-60` | `7ef69a90d6d1c1cb9ad50baa76205cc18f307f7a899d2033b78695ce19290485` | `TraceNoninterference` relational side-channel leakage equivalence |
| `leanprover/SampCert` (`a2c53bb5ff790e729e252958060699b7eff898b9`) | `SampCert/SLang.lean:1-160` | `6873dbfb4dfaee440d0262523b0d239b3f76a4cbb82c298ca40fae84a77d00ff` | `SLang α := PMF α` monadic foundation for verified samplers and zCDP |
| `Verified-zkEVM/ArkLib` (`bc367f8d53f603a48c5502e1ad7d39b7b3be725c`) | `ArkLib/Data/OracleComp/MeasuredProgram.lean:1-210` | `19e9fa9ae60e6fd238b4f3f3fa0e8c27f27a4f483c22611410e0a15228623545` | `MeasuredProgram` cost-tracking wrapper over `VCV-io`'s `OracleComp` |
| `GaloisInc/cryptol` (`76f7fabbec7e3f184f15b408b34619ad37a36ec8`) | `lib/Float.cry:35-38, 252-265` | `5fe5864b22f8bba64da12c7aad655c19e5434bbda410970653117f80348e0d7a` | Single-NaN SMT-LIB `Float e p` semantics; `fpToBits` canonicalizes NaNs and is unimplemented in symbolic backend |
| `GaloisInc/saw-script` (`27a7ae98256544b55a7a3ce4ce620c1a7889713b`) | `saw-central/src/SAWCentral/Crucible/MIR/Builtins.hs:1-260` | `c9e9832f6d32ad7ecf03ebd1f3242cfbd024b0fe0f91526a854deaccb17abb53` | `mir_verify`, `mir_unsafe_assume_spec`, and compositional `MIRMethodSpec` override matching |

## Revalidation

Revalidate this package from the package directory
(`reports/lean4-ieee754-floatspec-rfc3514-crypto-and-constant-time-2026/`) by
running:

```bash
/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean -j1 -M1024 support/FloatProbe.lean
/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean -j1 -M1024 support/FloatSpecRFC3514Bridge.lean
/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean -j1 -M1024 support/CostCtProbe.lean
```

Each command must exit with status `0`, emit zero warnings, and print `#print
axioms` outputs containing only standard Lean axioms (`propext`,
`Classical.choice`, `Quot.sound`) or `does not depend on any axioms`.

Revalidate this report when any of the following conditions change:

- Anneal's `Trusted/Refinement.lean`, `Trusted/StepResult.lean`, or
  `Anneal/FunctionalTranslation.lean` modifies `SmallStepMachine`, `StepResult`,
  `ReachesPrefix`, `BehaviorOf`, or `AeneasRes`.
- Anneal adds `f32`/`f64` scalar constructors or floating-point Rvalues to
  `Trusted/MirAst.lean` and `Trusted/MirSemantics.lean`.
- `Beneficial-AI-Foundation/FloatSpec` merges its Lean `v4.34.x` toolchain bump
  (PR #8) or fixes `Babs` (`FloatSpec/src/IEEE754/Binary.lean:51-54`) upstream.
- `Verified-zkEVM/VCV-io` updates its `Interop/Rust` or `Interop/Aeneas` bridge
  beyond commit `aae1c9cbd6c00311091d691b74f2d0032d76d9bd`.
