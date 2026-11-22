# Poison-Bearing Rust Intrinsics, `FloatToInt` Open-Interval Truncation, Fast/Algebraic Float Envelopes, RFC 3514 NaN Nondeterminism, and `f16`/`f128` Boundaries

## Summary

A verified drop-in replacement for `rustc` (covering MIR lowering, CTFE/Miri semantics, and LLVM IR generation) cannot treat Rust's intrinsic and floating-point surface as uniform total arithmetic. Primary-source inspection across `rust-lang/rust` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` and `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), `llvm/llvm-project` (`6dfe1677ab8dffbc6ec13d53a1e0215d75147689`), Rust RFC 3514 (`f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4`), and `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`), paired with live 20-case Miri + 14-function pre-pass LLVM IR execution and a 35-theorem kernel-checked `Lean v4.34.1` formalization (`support/PoisonIntrinsicsAndFloatSemantics.lean`), establishes six governing invariants:

1. **`#[miri::intrinsic_fallback_is_spec]` dual lowering couples `assume` preconditions in `core` to LLVM poison flags under `noundef`.** Intrinsics such as `disjoint_bitor` embed `unsafe { super::assume((self & other) == 0) }; self | other` in `library/core/src/intrinsics/fallback.rs` for CTFE/Miri and `-Zforce-intrinsic-fallback`, while `rustc_codegen_ssa` overrides them to emit LLVM `or disjoint` (`sdiv exact` / `udiv exact` for `exact_div`, `add nsw`/`nuw` for `AddUnchecked`, and unmasked `shl`/`ashr`/`lshr` for `ShlUnchecked`/`ShrUnchecked`) on `noundef`-attributed signatures. For `exact_div`, `rustc_const_eval` evaluates `BinOp::Rem` *before* `BinOp::Div`, catching `b == 0`, signed `T::MIN / -1` remainder overflow, and `a % b != 0`. Meanwhile, `core::intrinsics::select_unpredictable` executes `forget` on the unselected value (`1` drop total), whereas `core::hint::select_unpredictable` drops the unselected value via `drop_in_place` (`2` drops total), lowering identically across `Immediate`, `Pair` (`insertvalue poison` + `select !unpredictable` + `extractvalue`), and `Ref` (`select ptr !unpredictable` + `@llvm.memcpy`).
2. **`float_to_int_unchecked` checks bounds *after* toward-zero truncation, yielding the open rational interval `(T::MIN - 1, T::MAX + 1)`.** Safe `as` casts (`CastKind::FloatToInt`) lower to saturating `@llvm.fptoui.sat` / `@llvm.fptosi.sat` (`NaN -> 0`, `±Inf` clamped). By contrast, `float_to_int_unchecked` lowers to bare `fptoui` / `fptosi` (`poison` on out-of-range/NaN in LLVM IR, turning into immediate UB at `noundef` boundaries) and checks `Round::TowardZero` in CTFE/Miri while ignoring `Status::INEXACT`. Consequently, for `u8`, `float_to_int_unchecked(-0.9999_f32)` is **defined** and returns `0_u8`, whereas `-1.0_f32` and `256.0_f32` are immediate UB; conversely, `float_to_int_unchecked::<f32, i32>(i32::MAX as f32)` is **immediate UB** because `i32::MAX` (`2^31 - 1`) rounds to nearest even `2^31 = 2_147_483_648.0_f32` (`0x4f00_0000`), while `f32::from_bits(0x4eff_ffff)` (`2_147_483_520.0_f32`) is the maximum defined finite `f32` input for `i32`.
3. **`fadd_fast` requires finite inputs AND finite output with `±4 ULP` Miri perturbation, whereas `fadd_algebraic` omits `nnan`/`ninf` and is total and `const`.** `fadd_fast` (`unsafe fn`, non-`const`) emits `fadd fast` (`nnan ninf nsz arcp contract afn reassoc`) and immediately triggers UB in Miri if either operand *or* the computed IEEE sum is non-finite (`fadd_fast(f32::MAX, f32::MAX)` is immediate UB), otherwise perturbing finite non-zero sums by `[-4, +4]` ULP (`apply_random_float_error_ulp(..., 4)`, yielding 9 distinct bit patterns around `3.0_f32`; collapsed to exact rounding under `-Zmiri-deterministic-floats`). By contrast, `fadd_algebraic` (`safe const fn`) emits `fadd reassoc nsz arcp contract`—strictly omitting `nnan`, `ninf`, and `afn`—and remains UB-free on `NaN`, `±Inf`, and finite-to-infinite overflow at both compile time and runtime.
4. **RFC 3514 NaN nondeterminism establishes a strict refinement chain `CTFE ⊆ Miri(-Zmiri-deterministic-floats) ⊆ Miri(default)` with 6-output `sNaN` propagation.** Under CTFE and `-Zmiri-deterministic-floats`, `generate_nan` deterministically yields positive canonical quiet `F2::NAN` (`0x7fc0_0000` for `f32`). Under default Miri (`float_nondet = true`), `generate_nan` draws uniformly from `{preferred_nan = 0x7fc0_0000} ∪ {quiet(in) | in is NaN} ∪ {make_signaling(in) | in is sNaN}` and independently flips the sign bit, producing 2 NaNs for `0.0 / 0.0` and all 6 NaN bit patterns (3 of them signaling!) for `sNaN(0x7f80_0001) + 1.0_f32`.
5. **`f16` and `f128` pass directly in x86-64 SysV vector registers and soft-float through CTFE/Miri arithmetic, but Miri panics (`todo!("f128")`) on host-delegated `f128` math.** Under x86-64 SysV `extern "C"`, `f16` (`half`) and `f128` (`fp128`) are classified `Class::Sse` and passed/returned directly in SSE registers. Miri executes layout, arithmetic, casts, `sqrt`, and `algebraic_*` operations on `f16`/`f128` via `rustc_apfloat`, but panics with `exit code 101` (`not yet implemented: f128`) when calling `powi`, `powf`, or unary transcendentals (`sin`, `cos`, `exp`, `exp2`, `log`, `log10`, `log2`) on `f128`.
6. **Impact on `joshlf/anneal` (`c131b320`).** `Anneal`'s `Trusted.MirAst` and `Trusted.MirSemantics` already model and prove `BinOp.{addUnchecked, subUnchecked, mulUnchecked, shlUnchecked, shrUnchecked}` in lockstep with `rustc_const_eval`, while failing closed with `FaultKind.unsupported` on `TyKind::Float`, `Rvalue::Cast`, `StatementKind::Intrinsic`, and intrinsic `Call` terminators. Admitting floating-point or intrinsic constructs into a verified MIR semantics or verified codegen pipeline requires relational/set-valued nondeterminism for NaNs and algebraic/fast-math ULP envelopes, open-interval `Round::TowardZero` guards for `float_to_int_unchecked`, and explicit drop-count preservation across `intrinsics::select_unpredictable` versus `hint::select_unpredictable`.

---

## Applicability

**Subjects and relationships (`REPORT.json`).** All six subjects are durable upstream commits or specifications examined directly:

- **`rust-lang/rust` at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`1.102.0-nightly`, 2026-11-11, bundled `LLVM 23.1.5`):** Primary source revision audited across `library/core/src/`, `compiler/rustc_codegen_ssa/`, `compiler/rustc_codegen_llvm/`, `compiler/rustc_llvm/`, `compiler/rustc_mir_transform/`, `compiler/rustc_const_eval/`, `compiler/rustc_target/`, and `src/tools/miri/`. Its recorded 20-case Miri and 14-function LLVM 23.1.5 IR output is preserved in `support/recorded_llvm23_miri_1_102_0_nightly.json`.
- **`rust-lang/rust` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`, 2026-05-31, bundled `LLVM 22.1.6`):** Both source-audited (via local `rustc-src` and `rust-src` plus `src/tools/miri` from GitHub) and **live-executed** on `x86_64-unknown-linux-gnu` via `support/probe_poison_float_nan_and_f16_f128.py` to produce `support/probe_results.json`.
- **`llvm/llvm-project` at `6dfe1677ab8dffbc6ec13d53a1e0215d75147689` (`llvmorg-23.1.1`):** Normative LLVM Language Reference (`llvm/docs/LangRef.md`) governing `poison`, `noundef`, `or disjoint`, `sdiv exact`/`udiv exact`, `add nsw`/`nuw`, `fptoui`/`fptosi`, `@llvm.fptoui.sat`/`@llvm.fptosi.sat`, fast-math flags (`fast` vs. `reassoc nsz arcp contract`), and `!unpredictable`.
- **`rust-lang/rfcs` at `f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4` (`text/3514-float-semantics.md`):** Normative Rust specification for IEEE 754-2008 compliance, NaN sign/payload nondeterminism, signaling NaN propagation only from signaling inputs, and non-guaranteed CTFE-vs-runtime bitwise NaN identity.
- **`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`:** Target verified MIR model audited at `trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`, and `trusted/correspondence/Trusted/Correspondence.lean`.
- **`leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`):** Kernel that checked `support/PoisonIntrinsicsAndFloatSemantics.lean`.

**Version differences between `14210df0e` (`1.98.0-nightly`) and `3ef0c22cd` (`1.102.0-nightly`).** All 20 Miri exit codes and all 14 LLVM IR instruction lowerings agree identically across both revisions. Three structural source changes appear between `14210df0e` and `3ef0c22cd`:
1. **`disjoint_bitor` / `exact_div` `const`-ness:** In `14210df0e`, `library/core/src/intrinsics/mod.rs:1854` has `pub const unsafe fn disjoint_bitor` and `L1939` has `pub const unsafe fn exact_div`; line offsets shift to `L1946` and `L2030` in `3ef0c22cd`.
2. **Miri math intrinsic dispatch (`src/tools/miri/src/intrinsics/math.rs`):** In `14210df0e`, unary float ops match typed suffixes (`"powf128" => todo!("f128")`, `"powif128" => todo!("f128")` at `L188, 195, 200`); by `3ef0c22cd`, Rust consolidated typed math intrinsics into generic `"powf"` and `"powi"` intrinsics matching `ty::Float(float_ty)` (`FloatTy::F128 => todo!("f128")` at `L193, 205, 217`), and `apply_random_float_error` vs. `apply_random_float_error_ulp` live in `src/tools/miri/src/math.rs:71-168`.
3. **LLVM `captures(...)` attribute:** On LLVM 23.1.5 (`3ef0c22cd`), `ir_select_unpred_ref_array` emits `captures(address)` on the `sret` and `%a`/`%b` pointer parameters alongside `dead_on_unwind`/`dead_on_return`; on LLVM 22.1.6 (`14210df0e`), `sret` and `%a`/`%b` likewise carry `captures(address)` on `ir_select_unpred_ref_array` (`sret` + pointer operands passed to `select`).

**Configuration of execution and mechanization evidence.**
- **LLVM IR probe:** Compiled with `--edition=2021 -C opt-level=2 -C no-prepopulate-passes --emit=llvm-ir` on `x86_64-unknown-linux-gnu`. Setting `-C opt-level=2` lets MIR optimizations remove redundant staging locals while `-C no-prepopulate-passes` prevents LLVM's middle-end from constant-folding or eliding the raw codegen-emitted flags (`or disjoint`, `sdiv exact`, `fadd fast`, `fadd reassoc nsz arcp contract`, `!unpredictable`, `fpext half ... to fp128`). Results do not directly represent post-`-O3` optimized IR where subsequent passes (`InstCombine`, `SROA`, `VectorCombine`) fold or rewrite instructions.
- **Miri probe:** Executed with the installed `miri` binary against a sysroot built via `cargo miri setup --print-sysroot`, both with default flags (`float_nondet = true`, `float_rounding_error = Random`) and with `-Zmiri-deterministic-floats` (`float_nondet = false`). Multi-trial nondeterminism loops (`96` trials for `fadd_fast`, `48` for `0.0/0.0`, `192` for `sNaN + 1.0`) sample uniformly with high probability rather than exhausting PRNG seeds; determinism is verified with exact source inspection of Miri's candidate sets and RNG ranges.
- **Lean mechanization:** `support/PoisonIntrinsicsAndFloatSemantics.lean` is a standalone model constructed in core Lean `v4.34.1` (only standard axioms `[propext, Quot.sound]`, zero `sorry`, zero `Classical.choice`, zero `omega`/`bv_decide`/`native_decide`). Rational floating-point domain boundaries use exact rationals `num / (denPred + 1)` (`ExtFloat`), avoiding classical real numbers (`ℝ`).

**Related corpus reports.**
- `rustc-intrinsics-simd-and-arch-semantic-sources` inventories all 317 `#[rustc_intrinsic]` declarations and the 5-stage lowering pipeline from THIR to backends.
- `rustc-nondiverging-mir-intrinsics-assume-copynonoverlapping-and-unreachable-propagation` documents `StatementKind::Intrinsic(NonDivergingIntrinsic::{Assume, CopyNonOverlapping})`, which is the mechanism enforcing `disjoint_bitor`'s fallback UB.
- `rustc-postcleanup-mir-and-llvm-poison-freeze-ground-truth-census` measures production prevalence of LLVM `poison`, `noundef`, `nsw`, `nuw`, and `or disjoint` across `libcore`, `zerocopy`, and `anneal`.
- `undefined-values-poison-undef-freeze-and-refinement` formalizes the general LLVM `undef`/`poison`/`freeze` refinement preorder.

---

## Findings

### 1. The `#[miri::intrinsic_fallback_is_spec]` Dual-Lowering Architecture (`disjoint_bitor`, `exact_div`, `unchecked_*`, and `select_unpredictable`)

`Basis: source + execution + normative`

#### 1.1 Dual specification via `#[miri::intrinsic_fallback_is_spec]`

In `library/core/src/intrinsics/mod.rs:15-36` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`), `rustc` distinguishes ordinary *valid* intrinsic fallback bodies (which may omit UB conditions for non-specializing backends) from *spec-equivalent* fallback bodies annotated with `#[miri::intrinsic_fallback_is_spec]`:

> *"In some cases, the fallback body will be **equivalent** to the specification. Note that this is a strong requirement: if the spec says 'UB if input `x` is even', then a valid implementation can just ignore this and do whatever it wants in that case; an **equivalent** implementation needs to actually check this condition and trigger UB in that case (e.g. by using `hint::assert_unchecked()`). ... Intrinsics with such a fallback body that is equivalent to the spec may be marked with `#[miri::intrinsic_fallback_is_spec]`; the fallback body will then also be used by Miri for UB checking."*

At runtime codegen (`compiler/rustc_codegen_ssa/src/mir/intrinsic.rs:64-73`), unless `-Zforce-intrinsic-fallback` is passed (and `!def.must_be_overridden`), `codegen_intrinsic_call` bypasses the fallback body and lowers directly to LLVM instructions with poison-producing attributes. Miri and CTFE, conversely, execute the fallback MIR directly whenever no special `interpret/intrinsics.rs` or Miri override intercepts the symbol.

| Intrinsic | Fallback Spec in `core` (`#[miri::intrinsic_fallback_is_spec]`) | MIR / Codegen Override (`rustc_codegen_ssa` / `rustc_codegen_llvm`) | CTFE / Miri Evaluation Path | UB Condition (Miri / LLVM `noundef`) |
| :--- | :--- | :--- | :--- | :--- |
| `disjoint_bitor` | `unsafe { assume((a & b) == 0) }; a \| b` (`fallback.rs:143-144`) | `bx.or_disjoint(a, b)` -> `or disjoint iN %a, %b` (`intrinsic.rs:273-277`) | Executes fallback MIR (`Assume` -> `eval_nondiverging_intrinsic`) | `(a & b) != 0` (`assume` `false` / `poison`) |
| `exact_div` | Bodyless (`mod.rs:2030`) | `exactsdiv` / `exactudiv` -> `sdiv exact` / `udiv exact` (`intrinsic.rs:278-293`) | `interpret/intrinsics.rs:916-935`: `BinOp::Rem`, check `rem == 0`, `BinOp::Div` | `b == 0` ∨ `a % b != 0` ∨ signed `MIN / -1` |
| `unchecked_add` / `sub` / `mul` | Bodyless (`mod.rs:2082+`) | `LowerIntrinsics` -> `BinOp::{Add,Sub,Mul}Unchecked` -> `nsw` (signed) / `nuw` (unsigned) (`rvalue.rs:902-936`) | `interpret/operator.rs`: signed/unsigned range check | Arithmetic overflow outside `[T::MIN, T::MAX]` |
| `unchecked_shl` / `shr` | Bodyless (`mod.rs:2062-2072`) | `LowerIntrinsics` -> `BinOp::{Shl,Shr}Unchecked` -> unmasked `shl`/`ashr`/`lshr` (`rvalue.rs:975-982`, `base.rs:332-368`) | `interpret/operator.rs:129-168`: `rem_euclid(l_bits) != shift_amount` | `shift < 0` ∨ `shift >= lhs::BITS` |
| `intrinsics::select_unpredictable` | `if b { forget(false_val); true_val } else { forget(true_val); false_val }` (`mod.rs:743-753`) | `select i1 %c, ..., !unpredictable` (`Immediate`, `Pair`, `Ref` + `memcpy`, `intrinsic.rs:207-237`) | Executes fallback MIR (`1` drop for returned value only) | None (safe `const fn`); unselected value leaked |
| `hint::select_unpredictable` | Ordinary `#[inline(always)]` safe wrapper (`hint.rs:832-881`) | Calls `intrinsics::select_unpredictable` on pointers + `drop_in_place` + value select | Executes Rust body (`2` drops: unselected then selected) | None (safe `const fn`; `drop` order deterministic) |

#### 1.2 `disjoint_bitor`: Equivalence of `assume((a & b) == 0)` and `or disjoint`

In `library/core/src/intrinsics/mod.rs:1938-1949` (`3ef0c22cd`; `L1849-1859` at `14210df0e`), `disjoint_bitor` requires `(a & b) == 0` (equivalently `(a | b) == (a + b)`) and delegates to `library/core/src/intrinsics/fallback.rs:120-153`:

```rust
// library/core/src/intrinsics/fallback.rs:138-145 (3ef0c22cd)
unsafe fn disjoint_bitor(self, other: Self) -> Self {
    // Note that the assume here is required for UB detection in Miri!
    // SAFETY: our precondition is that there are no bits in common,
    // so this is just telling that to the backend.
    unsafe { super::assume((self & other) == zero!($t)) };
    self | other
}
```

When `rustc` lowers `disjoint_bitor` normally (`compiler/rustc_codegen_ssa/src/mir/intrinsic.rs:273-277`, `rustc_codegen_llvm/src/builder.rs:597-609`), it calls `LLVMBuildOr` + `LLVMSetIsDisjoint(or, TRUE)`, emitting `%_0 = or disjoint i32 %a, %b` inside a `define noundef i32 @ir_disjoint_bitor_u32(i32 noundef %a, i32 noundef %b)` signature. Per LLVM `LangRef.md`, `or disjoint` evaluates to `poison` if any bit position has `1` in both `%a` and `%b`; returning that `poison` through a `noundef` return type triggers immediate UB in LLVM's operational semantics. In Miri, `disjoint_bitor` executes `StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(false))` on `(0b1010_u32, 0b0010_u32)`, terminating with `error: Undefined Behavior: assume called with false` (`rc = 1`). Thus the fallback MIR and `noundef(or disjoint)` agree identically (mechanized in Lean as `disjointBitOr_fallback_eq_observeNoundef`, plus `bitList_disjoint_implies_add_eq_or_no_carry` proving `(a & b) == 0 → a + b = a | b` with zero carry).

#### 1.3 `exact_div`: Remainder-first ordering catches `y == 0`, `x % y != 0`, and signed `T::MIN / -1`

In `compiler/rustc_const_eval/src/interpret/intrinsics.rs:916-935` (`L961-980` at `14210df0e`), `InterpCx::exact_div` runs **two** MIR binary operators in order:

```rust
// compiler/rustc_const_eval/src/interpret/intrinsics.rs:925-935 (3ef0c22cd)
// Performs an exact division, resulting in undefined behavior where
// `x % y != 0` or `y == 0` or `x == T::MIN && y == -1`.
// First, check x % y != 0 (or if that computation overflows).
let rem = self.binary_op(BinOp::Rem, a, b)?;
// sign does not matter for 0 test, so `to_bits` is fine
if rem.to_scalar().to_bits(a.layout.size)? != 0 {
    throw_ub_format!("exact_div: {a} cannot be divided by {b} without remainder")
}
// `Rem` says this is all right, so we can let `Div` do its job.
let res = self.binary_op(BinOp::Div, a, b)?;
self.write_immediate(*res, dest)
```

Why the explicit `BinOp::Rem` *before* `BinOp::Div`? Because `i8::MIN % (-1_i8)` mathematically equals `0`, yet in Rust MIR (`interpret/operator.rs`) *both* `BinOp::Div` and `BinOp::Rem` fault immediately on `x == T::MIN && y == -1` to mirror x86 `IDIV` hardware `#DE` traps and LLVM `sdiv` UB. Live execution of `exact_div(i8::MIN, -1_i8)` in Miri confirms that `BinOp::Rem` faults first with:
`error: Undefined Behavior: overflow in signed remainder (dividing MIN by -1)` (`rc = 1`), whereas `exact_div(13_u32, 4_u32)` fails at the explicit remainder check (`exact_div: 13_u32 cannot be divided by 4_u32 without remainder`, `rc = 1`). In codegen (`intrinsic.rs:278-293`, `builder.rs:542-544`), signed types emit `sdiv exact` and unsigned types emit `udiv exact`, matching `exactDiv_miri_eq_observeNoundef`.

#### 1.4 `unchecked_*`: `nsw`/`nuw` vs. unmasked shifts and `LowerIntrinsics` `div`/`rem` reduction

In `compiler/rustc_mir_transform/src/lower_intrinsics.rs:97-130`, `LowerIntrinsics` lowers `unchecked_add`, `unchecked_sub`, `unchecked_mul`, `unchecked_shl`, and `unchecked_shr` to `Rvalue::BinaryOp` with `BinOp::{AddUnchecked, SubUnchecked, MulUnchecked, ShlUnchecked, ShrUnchecked}`, while `unchecked_div` and `unchecked_rem` lower directly to ordinary `BinOp::Div` and `BinOp::Rem` (because division/remainder by `0` and signed `MIN / -1` are already MIR UB).

In `compiler/rustc_codegen_ssa/src/mir/rvalue.rs:902-982` (`L791-872` at `14210df0e`):
- **`AddUnchecked` / `SubUnchecked` / `MulUnchecked`:** Signed integers call `bx.unchecked_sadd/ssub/smul` (`LLVMBuildNSWAdd`/`Sub`/`Mul`, emitting `add nsw`, `sub nsw`, `mul nsw`), while unsigned integers call `bx.unchecked_uadd/usub/umul` (`LLVMBuildNUWAdd`/`Sub`/`Mul`, emitting `add nuw`, `sub nuw`, `mul nuw`).
- **`ShlUnchecked` / `ShrUnchecked`:** Call `base::build_shift_expr_rhs(bx, lhs, rhs, is_unchecked = true)` (`compiler/rustc_codegen_ssa/src/base.rs:332-367`). When `is_unchecked` is `false` (checked/wrapping shift `BinOp::Shl`), `build_shift_expr_rhs` emits `and i32 %b, 31` (`mask = shift_mask_val(...)`) before `shl`. When `is_unchecked` is `true`, **no masking instruction is emitted** (and if `rhs_sz > lhs_sz`, `unchecked_utrunc` adds `trunc nuw`), so `ir_unchecked_shl_u32` lowers to bare `%_0 = shl i32 %a, %b`, which LLVM defines to return `poison` whenever `%b >= 32`. Miri enforces the matching check (`shift_amount.rem_euclid(l_bits) != shift_amount` at `interpret/operator.rs:131-168`), aborting on `unchecked_shl(1_u32, 32_u32)` with `error: Undefined Behavior: overflowing shift by 32 in unchecked_shl` (`rc = 1`).

#### 1.5 `select_unpredictable`: Drop divergence (`1` vs. `2`) and three-way backend lowering

`core::intrinsics::select_unpredictable` (`library/core/src/intrinsics/mod.rs:737-753`, `3ef0c22cd`) is safe, `const`, and explicitly documents: *"However unlike the public form, the intrinsic will not drop the value that is not selected"*—because its `#[miri::intrinsic_fallback_is_spec]` body calls `forget` on the unselected argument before returning the selected one. Conversely, the stable public wrapper `core::hint::select_unpredictable` (`library/core/src/hint.rs:832-881`) moves both arguments into `MaybeUninit`, uses two pointer calls to `intrinsics::select_unpredictable` to obtain `(guard, drop)` with a panic-safe `DropOnPanic` guard, invokes `drop.drop_in_place()` on the unselected value, and finally selects between the `MaybeUninit`s so the compiler preserves `!unpredictable` without reading through a pointer (`llvm/llvm-project#82340`). Empirical Miri execution with a `Drop`-counting probe confirms `DROPS intrinsic=1 hint=2` (`rc = 0`).

In `compiler/rustc_codegen_llvm/src/intrinsic.rs:207-237` (`L257-287` at `14210df0e`), codegen dispatches strictly on `OperandValue`:
1. **`OperandValue::Immediate` (`u64`):** Emits `%_0 = select i1 %c, i64 %a, i64 %b, !unpredictable !4`.
2. **`OperandValue::Pair` (`(u64, u64)`):** Calls `immediate_or_packed_pair` to pack both pairs via `insertvalue { i64, i64 } poison`, emits aggregate `select i1 %c, { i64, i64 } %1, { i64, i64 } %3, !unpredictable !4`, unpacks via `extractvalue`, and re-packs for ABI return.
3. **`OperandValue::Ref` (`[u64; 4]`, 32 bytes):** Emits `%0 = select i1 %c, ptr %a, ptr %b, !unpredictable !4` followed by `call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_0, ptr align 8 %0, i64 32, i1 false)` into the `sret([32 x i8])` destination, with `captures(address)` on the `sret` and `%a`/`%b` pointer parameters (because selecting between pointers and copying escapes their addresses into `%0`).
4. **`OperandValue::ZeroSized`:** Returns `OperandValue::ZeroSized` with zero instructions.

---

### 2. `CastKind::FloatToInt` Saturating Casts vs. `float_to_int_unchecked` Open-Interval Truncation UB

`Basis: normative + source + execution`

Safe Rust `x as Int` (`CastKind::FloatToInt`) and `unsafe core::intrinsics::float_to_int_unchecked::<F, Int>(x)` (`f32::to_int_unchecked` / `f64::to_int_unchecked`) lower to fundamentally distinct LLVM operations and CTFE/Miri validators:

- **Safe `CastKind::FloatToInt` (`compiler/rustc_codegen_ssa/src/mir/rvalue.rs:579-617`, `L485` `bx.cast_float_to_int`, `traits/builder.rs:417`, `rustc_codegen_llvm/src/builder.rs:1008-1014`):** Emits `@llvm.fptoui.sat.<iN>.<fM>` (unsigned) or `@llvm.fptosi.sat.<iN>.<fM>` (signed). In CTFE/Miri (`compiler/rustc_const_eval/src/interpret/cast.rs:395-410`), `rustc_apfloat`'s `to_u128` / `to_i128` saturates `NaN` to `0`, `-Inf` to `T::MIN`, `+Inf` to `T::MAX`, and clamps finite out-of-range floats (`SAT_OK 0,255,0,0` for `NaN, +Inf, -Inf, -0.9999_f32` cast to `u8`).
- **Unsafe `float_to_int_unchecked` (`compiler/rustc_codegen_ssa/src/mir/intrinsic.rs:349-395`, `rustc_codegen_llvm/src/builder.rs:1016-1063`):** Emits bare `fptoui` / `fptosi` (`%_0 = fptoui float %x to i8`), which returns LLVM `poison` on `NaN`, `±Inf`, or out-of-range values—becoming immediate UB at `noundef` return/use. In CTFE/Miri (`src/tools/miri/src/intrinsics/math.rs:168-182`, calling `float_to_int_checked(&val, dest.layout, Round::TowardZero)` at `compiler/rustc_const_eval/src/interpret/intrinsics.rs:1310-1365`):

```rust
// compiler/rustc_const_eval/src/interpret/intrinsics.rs:1352-1363 (3ef0c22cd)
if status.intersects(
    rustc_apfloat::Status::INVALID_OP
        | rustc_apfloat::Status::OVERFLOW
        | rustc_apfloat::Status::UNDERFLOW,
) {
    interp_ok(None)
} else {
    // The INEXACT flag is ignored on purpose to allow rounding.
    interp_ok(Some(ImmTy::from_scalar(val, cast_to)))
}
```

Because `Round::TowardZero` truncates fractional parts *before* testing `OVERFLOW`/`UNDERFLOW`, and because `Status::INEXACT` is explicitly ignored, the exact mathematical domain of defined inputs for integer target `[T::MIN, T::MAX]` is the **strictly open interval** `(T::MIN - 1, T::MAX + 1)` (mechanized in Lean by `floatToIntUnchecked_defined_iff_open_interval`).

**Two high-impact specification traps verified empirically and mechanically:**

1. **Unsigned negative-fraction acceptance `(-1.0, 0.0)`:** For `u8` (`[0, 255]`), the defined domain is `(-1.0, 256.0)`, **not** `[0.0, 255.0]` (`ce1_closed_interval_precondition_falsely_rejects_defined_neg_fraction_u8`). In Miri, `float_to_int_unchecked::<f32, u8>(-0.9999_f32)` and `255.9999_f32` succeed (`OPEN_INTERVAL_OK 0,255`, `rc = 0`), whereas `-1.0_f32` and `256.0_f32` fail with immediate UB (`rc = 1`).
2. **`i32::MAX as f32` rounding overflow trap:** `i32::MAX = 2^31 - 1 = 2_147_483_647` requires 31 significand bits, exceeding IEEE binary32's 24-bit precision (at `[2^30, 2^31)`, `1 ULP = 2^7 = 128`). Casting `i32::MAX as f32` rounds to nearest even `2^31 = 2_147_483_648.0_f32` (`0x4f00_0000`), which lies outside `(-2^31 - 1, 2^31)` and causes **immediate UB** in `float_to_int_unchecked::<f32, i32>(i32::MAX as f32)` (`rc = 1`, `2.14748365E+9f32 which cannot be represented in target type i32`). The largest finite `f32` representable in `i32` is `f32::from_bits(0x4eff_ffff) = 2^31 - 128 = 2_147_483_520.0_f32` (`rc = 0`, `MAX_F32_I32_OK 2147483520`).

Table 1 summarizes exact finite `float_to_int_unchecked` boundary values across IEEE `f16` (11-bit significand), `f32` (24-bit), `f64` (53-bit), and `f128` (113-bit):

| Target Int | `[T::MIN, T::MAX]` | Exact Mathematical Open Domain | Max Valid `f32` (`bits` / value) | `T::MAX as f32` Trap? | Max Valid `f64` | `T::MAX as f64` Trap? |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `u8` | `[0, 255]` | `(-1, 256)` | `0x437f_ffff` (`255.99998`) | No (`255.0`) | `< 256.0` (`256.0 - 2^-44`) | No (`255.0`) |
| `i8` | `[-128, 127]` | `(-129, 128)` | `0x42ff_ffff` (`127.99999`) | No (`127.0`) | `< 128.0` (`128.0 - 2^-45`) | No (`127.0`) |
| `u16` | `[0, 65535]` | `(-1, 65536)` | `0x477f_ffff` (`65535.996`) | No (`65535.0`) | `< 65536.0` | No (`65535.0`) |
| `i32` | `[-2^31, 2^31-1]` | `(-2^31-1, 2^31)` | `0x4eff_ffff` (`2^31 - 128`) | **YES** (rounds to `2^31`, UB!) | `2^31 - 2^-21` (exact int `2^31-1` fits) | No (exact) |
| `u32` | `[0, 2^32-1]` | `(-1, 2^32)` | `0x4f7f_ffff` (`2^32 - 256`) | **YES** (rounds to `2^32`, UB!) | `2^32 - 2^-20` | No (exact) |
| `i64` | `[-2^63, 2^63-1]` | `(-2^63-1, 2^63)` | `0x5eff_ffff` (`2^63 - 2^39`) | **YES** (rounds to `2^63`, UB!) | `0x43df_ffff_ffff_ffff` (`2^63 - 1024`) | **YES** (rounds to `2^63`, UB!) |
| `u64` | `[0, 2^64-1]` | `(-1, 2^64)` | `0x5f7f_ffff` (`2^64 - 2^40`) | **YES** (rounds to `2^64`, UB!) | `0x43ef_ffff_ffff_ffff` (`2^64 - 2048`) | **YES** (rounds to `2^64`, UB!) |
| `i128` | `[-2^127, 2^127-1]` | `(-2^127-1, 2^127)` | `2^127 - 2^103` | **YES** (rounds to `2^127`, UB!) | `2^127 - 2^74` (`< 2^127`) | **YES** (rounds to `2^127`, UB!) |

For `f16` (max finite `65504.0`), `i16::MAX as f16` (`32767` with `1 ULP = 16` at `[2^14, 2^15)`) similarly rounds UP to `2^15 = 32768.0_f16`, causing immediate UB on `float_to_int_unchecked::<f16, i16>(i16::MAX as f16)`, while `u16::MAX` (`65535`) overflows `f16::MAX` (`65504`) to `+Inf`, also causing UB. For `f128` (`113` significand bits), `i128::MAX as f128` (`2^127 - 1`, where `1 ULP = 2^14`) likewise rounds UP to `2^127`, causing UB on `float_to_int_unchecked::<f128, i128>`.

---

### 3. `fadd_fast` Poison / `±4 ULP` Envelope vs. `fadd_algebraic` Safe `const` Non-Poison Envelope

`Basis: source + normative + execution + derived`

Rust provides two relaxed floating-point arithmetic families whose LLVM fast-math flags and UB contracts differ sharply:

- **`fadd_fast` (`unsafe fn`, non-`const`, `library/core/src/intrinsics/mod.rs:1637`):**
  - **Codegen (`compiler/rustc_codegen_ssa/src/mir/intrinsic.rs:295-314`, `rustc_codegen_llvm/src/builder.rs:611-622`, `compiler/rustc_llvm/llvm-wrapper/RustWrapper.cpp:606-610`):** Calls `LLVMRustSetFastMath` (`I->setFast(true)`), emitting `%_0 = fadd fast float %a, %b`, which enables *all* seven LLVM fast-math flags: `nnan` (no NaNs -> poison), `ninf` (no Infs -> poison), `nsz`, `arcp`, `contract`, `afn`, and `reassoc`. Because LLVM `nnan` and `ninf` produce `poison` if *either* an operand *or* the result is `NaN` or `±Inf`, returning that result via `noundef float` induces UB even when both inputs are finite!
  - **Miri (`src/tools/miri/src/intrinsics/math.rs:116-166`):** Enforces three checks in sequence: (1) both inputs satisfy `float_finite(&a)` and `float_finite(&b)` (failing with `called with non-finite value as first/second/both parameter(s)`, `rc = 1` on `fadd_fast(1.0, NaN)`), (2) computes IEEE `binary_op(Add, a, b)`, (3) checks `float_finite(&res)` (failing with `produced non-finite value as result`, `rc = 1` on `fadd_fast(f32::MAX, f32::MAX)`!), and (4) calls `math::apply_random_float_error_to_imm(ecx, res, 4)`.
  - **Exact Miri Error Perturbation Bound (`src/tools/miri/src/math.rs:70-168`):** `src/tools/miri/src/math.rs` contains *two* error-injection helpers that must not be conflated:
    - `apply_random_float_error(ecx, val, err_scale)` (`L71-105`) perturbs `val` by a relative scale factor `(-2^err_scale, +2^err_scale)`.
    - `apply_random_float_error_to_imm(ecx, val, max_error)` (`L149-168`, called by `fadd_fast` with `max_error = 4`) delegates to `apply_random_float_error_ulp(ecx, ..., max_error)` (`L108-145`), which skips perturbation when `!float_nondet`, `FloatRoundingErrorMode::None`, `val.is_zero()`, or `!val.is_finite()`, and otherwise picks an integer offset `error ∈ [-4, +4]` (`rng.random_range(-max_error..=max_error)`) and returns `val + error * ulp`.
    In a 96-trial Miri run of `fadd_fast(1.0_f32, 2.0_f32)` (`exact = 3.0_f32 = 0x4040_0000`), default Miri emits all `9` ULP-adjacent values (`distinct=9`, `max_ulp=4`, `[0x403f_fffc .. 0x4040_0004]`), whereas `-Zmiri-deterministic-floats` sets `float_nondet = false` and emits `distinct=1`, `exact=0x40400000`.

- **`fadd_algebraic` (`safe const fn`, `library/core/src/intrinsics/mod.rs:1686`, stabilized as `{f16,f32,f64,f128}::algebraic_add`):**
  - **Codegen (`intrinsic.rs:316-347`, `RustWrapper.cpp:620-627`):** Calls `LLVMRustSetAlgebraicMath`, setting ONLY `AllowReassoc`, `AllowContract`, `AllowReciprocal`, and `NoSignedZeros`, emitting `%_0 = fadd reassoc nsz arcp contract float %a, %b`. **Crucially, `nnan`, `ninf`, and `afn` are omitted**, matching the C++ wrapper comment: *"Note that this does NOT enable any flags which can cause a floating-point operation on well-defined inputs to return poison, and therefore this function can be used to build safe Rust intrinsics"*.
  - **CTFE & Miri (`compiler/rustc_const_eval/src/interpret/intrinsics.rs:319-340`):** Shared directly between CTFE and Miri! Evaluates `self.binary_op(op, &a, &b)?` (which invokes `generate_nan` when needed) and then `M::apply_float_nondet(self, res)?` (identity in CTFE; `apply_random_float_error_to_imm(..., 4)` in Miri, which leaves `NaN`, `±Inf`, and `±0.0` untouched). Live Miri execution verifies `const C_NAN: u32 = fadd_algebraic(f32::NAN, 1.0_f32).to_bits()` (`0x7fc00000`) and runtime `fadd_algebraic(f32::MAX, f32::MAX) == f32::INFINITY` both pass with `rc = 0`.

---

### 4. RFC 3514 NaN Payload/Sign Nondeterminism & `f16`/`f128` ABI / Miri Boundaries

`Basis: normative + source + execution`

#### 4.1 RFC 3514 NaN specification vs. CTFE and Miri `generate_nan`

Under Rust RFC 3514 (`text/3514-float-semantics.md:50-135`, `rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4`), arithmetic operations (`+`, `-`, `*`, `/`, `%`, `sqrt`, `mul_add`, `FloatToFloat` casts) whose output is `NaN` produce a non-deterministic NaN conforming to LLVM's rules:
- If no input is `NaN`, the output is a **quiet** NaN with an unspecified sign (`0x7fc0_0000` or `0xffc0_0000` for `f32`)—a signaling NaN cannot be created out of thin air.
- If an input is `NaN`, the output may be any quieted or (if an input was signaling) unquieted input payload, or the preferred quiet NaN, with arbitrary sign.
- Consequently, RFC 3514 explicitly permits `const C: u32 = (0.0_f32 / 0.0_f32).to_bits()` and runtime `0.0_f32 / black_box(0.0_f32)` to observe different bit patterns (`0x7fc00000` at compile time vs. `{0x7fc00000, 0xffc00000}` at runtime).

In `compiler/rustc_const_eval/src/interpret/machine.rs:294-300` (`L285-291` at `14210df0e`), CTFE uses the trait default `F2::NAN` (canonical positive quiet `0x7fc0_0000`). In Miri (`src/tools/miri/src/operator.rs:74-127`), `generate_nan` branches on `self.machine.float_nondet`:

```rust
// src/tools/miri/src/operator.rs:74-124 (identical at 14210df0e and 3ef0c22cd)
if !ecx.machine.float_nondet { return F2::NAN; }
fn make_signaling<F: Float>(f: F) -> Option<F> {
    let quiet_bit_mask = 1 << (F::PRECISION - 2);
    let f = F::from_bits(f.to_bits() & !quiet_bit_mask);
    if f.is_nan() { Some(f) } else { None }
}
let preferred_nan = F2::qnan(Some(0));
let nans = iter::once(preferred_nan)
    .chain(inputs.iter().filter(|f| f.is_nan()).map(|&f| f.convert(&mut false).value))
    .chain(inputs.iter().filter(|f| f.is_signaling()).filter_map(|&f| make_signaling(f.convert(&mut false).value)));
let nan = nans.choose(&mut *rand).unwrap();
if rand.random() { -nan } else { nan }
```

Note two subtle invariants verified here:
1. **`make_signaling` safety guard (`payload != 0`):** Stripping the quiet bit `1 << (F::PRECISION - 2)` from a NaN with `0` low payload bits would turn its mantissa to `0` (i.e., `±Inf`!), so `if f.is_nan() { Some(f) } else { None }` prevents forging `±Inf` (mechanized as `generateNaN_miriDefault_all_valid_nan`). (An already-signaling NaN by definition already has non-zero low payload bits.)
2. **Six-way `sNaN` fan-out (`0x7f80_0001 + 1.0_f32`):** Because `0x7f80_0001` is signaling (`quiet = 0, payload = 1`), `nans` yields three base candidates (`0x7fc0_0000` preferred qNaN, `0x7fc0_0001` quieted qNaN, `0x7f80_0001` preserved sNaN), and independent random negation expands this to **6 distinct outputs**: `{0x7fc00000, 0xffc00000, 0x7fc00001, 0xffc00001, 0x7f800001, 0xff800001}`, **2 of which remain signaling** (`has_signaling_out = true`). Under `-Zmiri-deterministic-floats`, both `0.0/0.0` and `0x7f80_0001 + 1.0` collapse back to `["0x7fc00000"]`.

#### 4.2 `f16` / `f128` SysV x86-64 ABI & Miri Host-Math Boundary

- **SysV x86-64 ABI (`compiler/rustc_target/src/callconv/x86_64.rs:76-80`):** Every IEEE scalar float `Float::{F16, F32, F64, F128}` maps to `Class::Sse` (only `Float::X87F80` maps to `Class::X87`). Thus `pub extern "C" fn ir_sysv_abi_f16_f128(x: f16, y: f128) -> f128` lowers directly to:
  ```llvm
  define noundef fp128 @ir_sysv_abi_f16_f128(half noundef %x, fp128 noundef %y) unnamed_addr #0 {
    %_3 = fpext half %x to fp128
    %_0 = fadd fp128 %_3, %y
    ret fp128 %_0
  }
  ```
  passing `x` and `y` directly in vector registers without `sret` or stack indirection.
- **Miri soft-float completeness vs. `todo!("f128")` ICE boundary:** Miri evaluates `f16` and `f128` layout (`2` and `16` bytes), arithmetic (`+`, `-`, `*`, `/`, `%`), `as` casts, `sqrt` (`rustc_apfloat::ieee::{Half, Quad}`), `fadd_fast`, and `fadd_algebraic` cleanly (`F16_F128_OK d=13.75`, `rc = 0`). However, host-delegated float intrinsics (`powi`, `powf`, `sin`, `cos`, `exp`, `exp2`, `log`, `log10`, `log2`) in `src/tools/miri/src/intrinsics/math.rs:185-220` (`3ef0c22cd`; `L181-201` at `14210df0e`) rely on host Rust `ToHost`/`ToSoft` conversions (`f16`, `f32`, `f64` only, `src/tools/miri/src/math.rs:10-68`) and hit `FloatTy::F128 => todo!("f128")` (`math.rs:193, 205, 217` at `3ef0c22cd`; `L188, 195, 200` at `14210df0e`), crashing Miri with `exit code 101` (`not yet implemented: f128`) on `2.0_f128.powi(3)`.

---

### 5. Empirical 20-Case Miri & 14-Function Pre-Pass LLVM IR Verification Across Nightly Revisions

`Basis: execution (live probe on 1.98.0-nightly / LLVM 22.1.6 + preserved 1.102.0-nightly / LLVM 23.1.5 baseline)`

#### 5.1 Complete 20-Case Miri Operational Matrix (`probe_results.json` vs. `recorded_llvm23_miri_1_102_0_nightly.json`)

Every one of the 20 Miri cases reproduces the exact same return code (`rc`) and output invariants on `rustc 1.98.0-nightly (14210df0e)` (`probe_results.json`) as in the `1.102.0-nightly (3ef0c22cd)` baseline (`recorded_llvm23_miri_1_102_0_nightly.json`):

| # | Probe Case (`miri_matrix` key) | Flags | `rc` (`1.98` / `1.102`) | Observed `stdout` / Diagnostic Head (`1.98.0-nightly`) |
| ---: | :--- | :--- | :---: | :--- |
| 1 | `float_as_u8_saturating_nan_inf_neg_ok` | default | `0 / 0` | `SAT_OK 0,255,0,0` |
| 2 | `float_to_int_unchecked_u8_neg_0_9999_open_interval_ok` | default | `0 / 0` | `OPEN_INTERVAL_OK 0,255` |
| 3 | `float_to_int_unchecked_u8_neg_1_0_ub` | default | `1 / 1` | `UB: float_to_int_unchecked intrinsic called on -1f32 ... type u8` |
| 4 | `float_to_int_unchecked_u8_256_0_ub` | default | `1 / 1` | `UB: float_to_int_unchecked intrinsic called on 256f32 ... type u8` |
| 5 | `float_to_int_unchecked_i32_max_as_f32_rounds_to_2p31_ub` | default | `1 / 1` | `UB: float_to_int_unchecked intrinsic called on 2.14748365E+9f32 ... type i32` |
| 6 | `float_to_int_unchecked_i32_max_representable_f32_0x4effffff_ok` | default | `0 / 0` | `MAX_F32_I32_OK 2147483520` |
| 7 | `disjoint_bitor_disjoint_ok` | default | `0 / 0` | `assert_eq!(0b1111, 0b1111)` passes (`""`) |
| 8 | `disjoint_bitor_overlapping_bit_ub` | default | `1 / 1` | `UB: assume called with false` |
| 9 | `exact_div_exact_ok` | default | `0 / 0` | `assert_eq!((3, -3), (3, -3))` passes (`""`) |
| 10 | `exact_div_nonzero_remainder_ub` | default | `1 / 1` | `UB: exact_div: 13_u32 cannot be divided by 4_u32 without remainder` |
| 11 | `exact_div_signed_min_div_neg1_overflow_ub` | default | `1 / 1` | `UB: overflow in signed remainder (dividing MIN by -1)` |
| 12 | `select_unpredictable_intrinsic_forgets_vs_hint_drops` | default | `0 / 0` | `DROPS intrinsic=1 hint=2` |
| 13 | `fadd_fast_nan_input_ub` | default | `1 / 1` | `UB: fadd_fast intrinsic called with non-finite value as second parameter` |
| 14 | `fadd_fast_finite_inputs_infinite_output_ub` | default | `1 / 1` | `UB: fadd_fast intrinsic produced non-finite value as result` |
| 15 | `fadd_fast_4ulp_nondeterminism_default_miri` | default | `0 / 0` | `FADD_FAST_NONDET distinct=9 max_ulp=4` |
| 16 | `fadd_fast_deterministic_floats_exact` | `-Zmiri-deterministic-floats` | `0 / 0` | `FADD_FAST_DET distinct=1 exact=0x40400000` |
| 17 | `fadd_algebraic_safe_const_and_runtime_nan_inf_ok` | default | `0 / 0` | `FADD_ALG_OK const_nan=0x7fc00000` |
| 18 | `nan_nondeterminism_ctfe_vs_miri_default` | default | `0 / 0` | `NAN_NONDET ctfe=0x7fc00000 zdivz=["0x7fc00000", "0xffc00000"] snan_prop_count=6 has_signaling_out=true` |
| 19 | `f16_and_f128_layout_arith_and_casts_miri_ok` | default | `0 / 0` | `F16_F128_OK d=13.75` |
| 20 | `f128_powi_miri_todo_boundary` | default | `101 / 101` | `panicked at src/tools/miri/src/intrinsics/math.rs:200:27: not yet implemented: f128` (`:217:38` in `1.102`) |

Four supplementary probes in `probe_results.json` additionally verify: `unchecked_shl(1_u32, 32_u32)` (`rc = 1`, `overflowing shift by 32 in unchecked_shl`), `unchecked_add(i8::MAX, 1_i8)` (`rc = 1`, `arithmetic overflow in unchecked_add`), `unchecked_add(u8::MAX, 1_u8)` (`rc = 1`, `arithmetic overflow in unchecked_add`), and `nan_nondeterminism_miri_deterministic_floats` (`rc = 0`, collapsing both `0.0/0.0` and `0x7f80_0001 + 1.0` to `["0x7fc00000"]`).

#### 5.2 Complete 14-Function Pre-Pass LLVM IR Matrix (`LLVM 22.1.6` and `LLVM 23.1.5`)

Compiled with `-C opt-level=2 -C no-prepopulate-passes --emit=llvm-ir`, all 14 functions emit matching instructions across LLVM 22.1.6 (`14210df0e`) and LLVM 23.1.5 (`3ef0c22cd`):

| # | Function (`llvm_ir_lowering`) | Key Parameter / Return Attributes | Lowered Pre-Pass LLVM Instruction(s) |
| ---: | :--- | :--- | :--- |
| 1 | `ir_float_as_u8_sat` | `noundef i8 (float noundef %x)` | `%_0 = call i8 @llvm.fptoui.sat.i8.f32(float %x)` |
| 2 | `ir_float_to_u8_unchecked` | `noundef i8 (float noundef %x)` | `%_0 = fptoui float %x to i8` |
| 3 | `ir_disjoint_bitor_u32` | `noundef i32 (i32 noundef %a, i32 noundef %b)` | `%_0 = or disjoint i32 %a, %b` |
| 4 | `ir_exact_sdiv_i32` | `noundef i32 (i32 noundef %a, i32 noundef %b)` | `%_0 = sdiv exact i32 %a, %b` |
| 5 | `ir_exact_udiv_u32` | `noundef i32 (i32 noundef %a, i32 noundef %b)` | `%_0 = udiv exact i32 %a, %b` |
| 6 | `ir_unchecked_sadd_i32` | `noundef i32 (i32 noundef %a, i32 noundef %b)` | `%_0 = add nsw i32 %a, %b` |
| 7 | `ir_unchecked_uadd_u32` | `noundef i32 (i32 noundef %a, i32 noundef %b)` | `%_0 = add nuw i32 %a, %b` |
| 8 | `ir_unchecked_shl_u32` | `noundef i32 (i32 noundef %a, i32 noundef %b)` | `%_0 = shl i32 %a, %b` (contrast checked `wrapping_shl`: `%_3 = and i32 %b, 31` then `shl`) |
| 9 | `ir_fadd_fast_f32` | `noundef float (float noundef %a, float noundef %b)` | `%_0 = fadd fast float %a, %b` |
| 10 | `ir_fadd_algebraic_f32` | `noundef float (float noundef %a, float noundef %b)` | `%_0 = fadd reassoc nsz arcp contract float %a, %b` |
| 11 | `ir_select_unpred_scalar` | `noundef i64 (i1 noundef zeroext %c, i64 noundef %a, i64 noundef %b)` | `%_0 = select i1 %c, i64 %a, i64 %b, !unpredictable !4` |
| 12 | `ir_select_unpred_pair` | `{ i64, i64 } (i1 noundef zeroext %c, i64 %a.0, i64 %a.1, i64 %b.0, i64 %b.1)` | `insertvalue { i64, i64 } poison ...` -> `select i1 %c, { i64, i64 } %1, { i64, i64 } %3, !unpredictable !4` -> `extractvalue` |
| 13 | `ir_select_unpred_ref_array` | `void (ptr ... sret([32 x i8]) captures(address) %_0, i1 %c, ptr ... captures(address) %a, ptr ... captures(address) %b)` | `%0 = select i1 %c, ptr %a, ptr %b, !unpredictable !4` -> `call void @llvm.memcpy.p0.p0.i64(ptr align 8 %_0, ptr align 8 %0, i64 32, i1 false)` |
| 14 | `ir_sysv_abi_f16_f128` | `noundef fp128 (half noundef %x, fp128 noundef %y)` | `%_3 = fpext half %x to fp128` -> `%_0 = fadd fp128 %_3, %y` -> `ret fp128 %_0` |

---

### 6. Kernel-Checked `Lean v4.34.1` Mechanization & 4 Constructive Counterexamples

`Basis: derived (kernel-checked Lean v4.34.1 proofs in support/PoisonIntrinsicsAndFloatSemantics.lean)`

`support/PoisonIntrinsicsAndFloatSemantics.lean` formalizes the four semantic subsystems constructively over `BitVec w`, `Int`, exact rationals `ExtFloat.finite (num : Int) (denPred : Nat)`, IEEE `NaNVal` records, and discrete ULP grids `FloatDomain`. Every theorem (all 35 theorems in `support/lean_axioms_all_theorems.txt`) kernel-checks cleanly with `-DwarningAsError=true` using **zero `sorry`**, **zero `Classical.choice`**, **zero `omega`**, **zero `bv_decide`**, **zero `native_decide`**, and **zero `partial def`**, depending exclusively on core Lean axioms (`[]`, `[propext]`, or `[propext, Quot.sound]`).

| Mechanized Theorem / Counterexample | Formal Claim | Axioms |
| :--- | :--- | :--- |
| `disjointBitOr_fallback_eq_observeNoundef` | `observeNoundef (evalDisjointBitOr w a b) = evalDisjointBitOrFallback w a b` | `[propext, Quot.sound]` |
| `disjointBitOr_fallback_iff_no_poison` | `evalDisjointBitOr w a b ≠ .poison ↔ evalDisjointBitOrFallback w a b ≠ .ub` | `[propext, Quot.sound]` |
| `bitList_disjoint_implies_add_eq_or_no_carry` | `allFalse (bitAndList xs ys) = true → addBitsCarry xs ys false = (bitOrList xs ys, false)` | `[propext, Quot.sound]` |
| `exactDiv_miri_eq_observeNoundef` / `exactDiv_miri_iff_no_poison` | `evalExactDivLLVM w signed a b` poison-freedom iff `evalExactDivMiri` (`Rem` then `Div`) non-UB | `[propext]` |
| `exactSDiv_signedMin_neg1_ub` | `evalExactDivMiri 8 true (-128) (-1) = .ub` | `[]` |
| `uncheckedAdd_miri_iff_no_poison` / `uncheckedShl_miri_iff_no_poison` | Unchecked `add nsw/nuw` and unmasked `shl` match Miri `AddUnchecked`/`ShlUnchecked` | `[propext]` |
| `checkedShl_total_while_uncheckedShl_poisons_at_width` | `evalUncheckedShlLLVM 32 1 32 = .poison ∧ evalCheckedShl 32 1 32 = 1` | `[]` |
| `selectUnpredictable_repr_equiv` | `selectImmediate c a b = selectPackedPair c a b ∧ selectPackedPair c a b = selectRefMemcpy c a b` | `[propext]` |
| `floatToIntUnchecked_defined_iff_open_interval` | `floatToIntUnchecked b (.finite num denPred) = .ok q ↔ (minVal - 1) * d < num < (maxVal + 1) * d` | `[propext]` |
| `floatToIntUnchecked_unsigned_admits_neg_open_unit_interval` | For `b.minVal = 0` and `-d < num < 0`, `floatToIntUnchecked b (.finite num denPred) = .ok 0` | `[propext]` |
| `floatToIntSat_refines_floatToIntUnchecked` | `floatToIntUnchecked b x = .ok v → floatToIntSat b x = v` | `[propext]` |
| `i32_max_as_f32_rounds_to_two_pow_31` | `roundF32HighRangeRNE 2147483647 = 2147483648 ∧ roundF32HighRangeRNE 2147483520 = 2147483520` | `[]` |
| `generateNaN_miriDet_subset_miriDefault` | `x ∈ generateNaN_MiriDet inputs → x ∈ generateNaN_MiriDefault inputs` | `[propext, Quot.sound]` |
| `generateNaN_strict_refinement_zero_div_zero` | Negative canonical qNaN (`0xffc0_0000`) ∈ `MiriDefault []` and ∉ `MiriDet []` | `[propext]` |
| `generateNaN_strict_refinement_snan_six_outputs` | `(generateNaN_MiriDefault [sNaN1]).length = 6` with both `±sNaN1` present, absent from `MiriDet` | `[propext]` |
| `generateNaN_miriDefault_all_valid_nan` | Every output in `generateNaN_MiriDefault inputs` satisfies `isValidNaN x = true` (never `±Inf`) | `[propext]` |
| `evalFloatFast_refinement_chain` | `CTFE ⊆ MiriDet ⊆ MiriDefault` (`±4 ULP`, 9 elements) when non-UB | `[propext, Quot.sound]` |
| `evalFloatAlgebraic_total_and_safe_on_nonfinite` | `∀ mode a b op on, evalFloatAlgebraic mode a b op on ≠ .ub` | `[propext]` |
| `ce1_closed_interval_precondition_falsely_rejects_defined_neg_fraction_u8` | Counterexample 1 (`-0.9999` rejected by `[0, 255]` yet `.ok 0`) | `[]` |
| `ce2_i32_max_round_to_f32_overflows_float_to_int_unchecked` | Counterexample 2 (`i32::MAX as f32` rounds to `2^31`, causing UB; `0x4eff_ffff` succeeds) | `[]` |
| `ce3_adding_ninf_to_fadd_algebraic_introduces_unsound_overflow_poison` | Counterexample 3 (`fadd_algebraic(f32::MAX, f32::MAX)` is `.ok [.inf true]` vs. unsound `ninf` `.ub`) | `[propext]` |
| `ce4_intrinsic_vs_hint_select_unpredictable_drop_count_divergence` | Counterexample 4 (`1` drop vs. `2` drops between `intrinsics` and `hint` `select_unpredictable`) | `[]` |

---

### 7. Consequences for `joshlf/anneal` (`c131b320`) and Verified `rustc` Backends

`Basis: source + derived`

Inspecting `trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`, and `trusted/correspondence/Trusted/Correspondence.lean` in `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`:

1. **`BinOp` unchecked operators are already sound and in lockstep with Miri.** `MirAst.BinOp` (`MirAst.lean:400-434`) includes `addUnchecked`, `subUnchecked`, `mulUnchecked`, `shlUnchecked`, and `shrUnchecked`. `Correspondence.toMiriBinOp` (`Correspondence.lean:920-945`) maps each 1-to-1 to `Miri.MIR.BinOp`, while `MirSemantics.evalShiftOp` (`MirSemantics.lean:1034-1047`) checks `intEmod r w.bitWidth != r` before `op.isUnchecked` and `MirSemantics.evalArithOp` (`MirSemantics.lean:1060-1090`) checks `(hostOverflow || lossy) && op.isUnchecked` (plus explicit `r == 0` and `signedMinInt w / -1` UB for `.div`/`.rem`). Thus `BinOp` unchecked arithmetic and shifts already match `rustc_const_eval`'s operational semantics.
2. **Float types, `CastKind::FloatToInt`, `StatementKind::Intrinsic`, and un-lowered intrinsic calls currently fail closed as `.unsupported`.** `MirAst.MirTy` (`MirAst.lean:308-315`) excludes `TyKind::Float` to `.unsupported`; `MirAst.Rvalue` (`MirAst.lean:620-628`) omits `Cast` altogether; `MirAst.StatementKind` omits `Intrinsic` (routing `Assume` in `disjoint_bitor`'s fallback body through `toMiriStatementForDispatch`'s `.unsupported` sentinel at `Correspondence.lean:2026-2028` to `.fault .unsupported`); and un-inlined calls to `exact_div`, `float_to_int_unchecked`, `fadd_fast`, `fadd_algebraic`, or `select_unpredictable` fault fail-closed in the call dispatcher. There is therefore **no soundness bug** at `c131b320`, because unmodeled behavior never silently succeeds.
3. **Requirements for extending a verified MIR semantics or verified LLVM/ISA backend:**
   - **No deterministic float return type for `NaN`/`fadd_algebraic`/`fadd_fast`:** A verified semantics that models `0.0/0.0` or `fadd_algebraic` via deterministic IEEE `F2::NAN` (`CTFE`) will **fail to refine** default Miri or compiled hardware (where `sNaN + 1.0` returns 6 distinct NaN bit patterns and `fadd_algebraic`/`fadd_fast` may perturb finite non-zero sums within fast-math envelopes). Verifiers must either model a relational/set-valued float monad over RFC 3514 NaN sets + fast-math envelopes or explicitly prohibit `to_bits`/sign observation on generated NaNs.
   - **Strict flag discipline in verified LLVM codegen:** Lowering `fadd_algebraic` MUST emit `reassoc nsz arcp contract` without `nnan`/`ninf`/`afn`; lowering `float_to_int_unchecked` MUST guard against the exact open interval `(T::MIN - 1, T::MAX + 1)` rather than closed `[T::MIN, T::MAX]`; lowering `exact_div` MUST verify `y != 0 ∧ x % y == 0 ∧ ¬(x == T::MIN ∧ y == -1)` (checking remainder overflow before division); and inlining/lowering `core::intrinsics::select_unpredictable` MUST preserve the single-drop `forget` semantics distinct from `core::hint::select_unpredictable`'s double-drop semantics.

---

## Boundaries

- **Not examined:**
  - Non-x86-64 ABI lowering for `f16` and `f128` (e.g., soft-float compiler-builtins libcalls `__extendhfsf2` / `__addtf3` on 32-bit targets, Windows x64, AArch64 AAPCS64, or MIPS legacy quiet/signaling NaN inversion).
  - Non-LLVM codegen backends (`rustc_codegen_cranelift` and `rustc_codegen_gcc`) for `fadd_algebraic`, `disjoint_bitor`, and `select_unpredictable`.
  - Post-`-O3` LLVM middle-end optimization rewrites (e.g., InstCombine converting `add nsw` + `fptoui` or deleting dead `fadd fast`). All IR inspections in this report capture pre-pass (`-C no-prepopulate-passes`) frontend IR.
  - Other relaxed float/integer intrinsics outside the core target set (`fmul_fast`, `fdiv_fast`, `frem_fast`, `fsub_algebraic`, `unchecked_funnel_shl`/`shr`, `unchecked_sub`/`mul`, `carrying_mul_add`), though codegen dispatch arms for `f{sub,mul,div,rem}_{fast,algebraic}` appear in the same match blocks.
- **Known not to apply:**
  - Closing the `float_to_int_unchecked` precondition to `[T::MIN, T::MAX]` does **not** hold (`ce1_...`: `-0.9999_f32 as u8` via `float_to_int_unchecked` is defined as `0_u8`).
  - Assuming `T::MAX as f32` or `T::MAX as f64` safely round-trips into `float_to_int_unchecked` does **not** hold whenever `T::BITS` exceeds the float significand precision (`ce2_...`: `i32::MAX as f32 == 2^31` is UB).
  - Assuming `fadd_fast` is safe whenever *inputs* are finite does **not** hold (`fadd_fast(f32::MAX, f32::MAX)` produces non-finite output and triggers immediate UB in Miri and LLVM `ninf`/`noundef`).
  - Assuming `fadd_algebraic` carries LLVM `nnan`/`ninf` or cannot produce `NaN`/`±Inf` does **not** hold (`ce3_...`).
  - Assuming `core::intrinsics::select_unpredictable` and `core::hint::select_unpredictable` agree on destructor counts does **not** hold (`ce4_...`: `1` drop vs. `2` drops).
  - Assuming CTFE's canonical `0x7fc0_0000` NaN is preserved at runtime under RFC 3514 does **not** hold (`0.0 / 0.0` produces `0xffc0_0000` half the time in Miri; `sNaN + 1.0` yields 6 distinct NaN bit patterns, including signaling outputs).
- **Unsupported:**
  - Host-delegated `f128` math intrinsics (`powi`, `powf`, `sin`, `cos`, `exp`, `exp2`, `log`, `log10`, `log2`) explicitly panic in Miri with `todo!("f128")` (`exit code 101`).
  - `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` explicitly rejects `TyKind::Float`, `Rvalue::Cast`, `StatementKind::Intrinsic`, and un-inlined intrinsic `Call`s as `FaultKind.unsupported`.
- **Unknown:**
  - Whether future Miri versions will implement soft-float quad-precision transcendentals (resolving `todo!("f128")`) or refine the `±4 ULP` nondeterministic error model (`apply_random_float_error_ulp`) for fast/algebraic float operations.

---

## Evidence

### Upstream Primary Sources Examined

Line numbers below give `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`1.102.0-nightly`) first, followed by `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`) in parentheses where offsets differ.

| Repository & Revision | File Path | Inspected Items & Exact Lines |
| :--- | :--- | :--- |
| `rust-lang/rust` (`3ef0c22cd` / `14210df0e`) | `library/core/src/intrinsics/mod.rs` | `#[miri::intrinsic_fallback_is_spec]` module spec `L15-49`; `select_unpredictable` `L737-753` (`L478-495`); `fadd_fast` `L1631-1637` (`L1572-1578`); `float_to_int_unchecked` `L1671-1678` (`L1612-1619`); `fadd_algebraic` `L1680-1686` (`L1621-1626`); `disjoint_bitor` `L1936-1949` (`L1854`); `exact_div` `L2023-2030` (`L1939`); `unchecked_shl`/`unchecked_add` `L2062-2082` (`L1971-1991`) |
| `rust-lang/rust` (`3ef0c22cd` / `14210df0e`) | `library/core/src/intrinsics/fallback.rs` | `trait DisjointBitOr` & `unsafe { super::assume((self & other) == zero!($t)) }; self \| other` `L114-153` (`L114-148`) |
| `rust-lang/rust` (`3ef0c22cd` / `14210df0e`) | `library/core/src/hint.rs` | `pub const fn select_unpredictable` with `DropOnPanic` & `drop_in_place` `L788-881` |
| `rust-lang/rust` (`3ef0c22cd` / `14210df0e`) | `compiler/rustc_mir_transform/src/lower_intrinsics.rs` | `sym::unchecked_{add,sub,mul,div,rem,shl,shr}` lowering to `BinOp` `L97-130` |
| `rust-lang/rust` (`3ef0c22cd` / `14210df0e`) | `compiler/rustc_codegen_ssa/src/mir/intrinsic.rs` | `-Zforce-intrinsic-fallback` `L64-73`; `disjoint_bitor` `L273-277` (`L275-279`); `exact_div` `L278-294` (`L280-296`); `f*_fast` `L295-315` (`L297-317`); `f*_algebraic` `L316-347` (`L318-349`); `float_to_int_unchecked` `L349-395` (`L351-397`) |
| `rust-lang/rust` (`3ef0c22cd` / `14210df0e`) | `compiler/rustc_codegen_ssa/src/mir/rvalue.rs` | `cast_immediate` & `CastKind::FloatToInt` `L449-489, 579-617` (`L349-389, 475-513`); `BinOp::AddUnchecked` `L902-908` (`L791-797`); `BinOp::ShlUnchecked`/`ShrUnchecked` `L975-982` (`L865-872`) |
| `rust-lang/rust` (`3ef0c22cd` / `14210df0e`) | `compiler/rustc_codegen_ssa/src/traits/builder.rs` | `cast_float_to_int` -> `fptosi_sat`/`fptoui_sat` `L400-418` |
| `rust-lang/rust` (`3ef0c22cd` / `14210df0e`) | `compiler/rustc_codegen_ssa/src/base.rs` | `build_shift_expr_rhs` mask omission (`!is_unchecked`) & `unchecked_utrunc` `L332-367` |
| `rust-lang/rust` (`3ef0c22cd` / `14210df0e`) | `compiler/rustc_codegen_llvm/src/intrinsic.rs` | `sym::select_unpredictable` across `Ref`, `Immediate`, `Pair`, `ZeroSized` `L207-237` (`L257-287`) |
| `rust-lang/rust` (`3ef0c22cd` / `14210df0e`) | `compiler/rustc_codegen_llvm/src/builder.rs` | `exactsdiv`/`exactudiv` `L542-544`; `unchecked_sadd`/`uadd` `L558-563`; `or_disjoint` `L597-609` (`L521-533`); `set_math_builder_methods!` `L611-622`; `unchecked_utrunc` `L980-990`; `fptoui_sat`/`fptoui`/`fptosi` `L1008-1063` (`L964-1019`); `set_unpredictable` `L1622-1624` (`L1513-1515`) |
| `rust-lang/rust` (`3ef0c22cd` / `14210df0e`) | `compiler/rustc_llvm/llvm-wrapper/RustWrapper.cpp` | `LLVMRustSetFastMath` (`setFast(true)`) `L606-610`; `LLVMRustSetAlgebraicMath` (`AllowReassoc`, `AllowContract`, `AllowReciprocal`, `NoSignedZeros`) `L620-627` |
| `rust-lang/rust` (`3ef0c22cd` / `14210df0e`) | `compiler/rustc_const_eval/src/interpret/{intrinsics,cast,machine,operator}.rs` | `fadd_algebraic` `intrinsics.rs:319-340` (`L315-336`); `exact_div` `L373-377, 916-935` (`L369-373, 961-980`); `float_to_int_checked` `L1310-1365` (`L1316-1371`); `cast_from_float` `cast.rs:384-429`; `generate_nan` & `apply_float_nondet` `machine.rs:294-308` (`L285-299`); shift `rem_euclid` `operator.rs:129-168` |
| `rust-lang/rust` (`3ef0c22cd` / `14210df0e`) | `compiler/rustc_target/src/callconv/x86_64.rs` | `Float::X87F80 => Class::X87`, all other `Primitive::Float(_) => Class::Sse` `L78-79` |
| `rust-lang/rust` (`3ef0c22cd` / `14210df0e`) | `src/tools/miri/src/{operator,math,intrinsics/math}.rs` | Miri `generate_nan` & `make_signaling` `operator.rs:74-127`; `apply_random_float_error*` `math.rs:71-168`; `fadd_fast`, `float_to_int_unchecked`, `todo!("f128")` `intrinsics/math.rs:116-220` (`L113-201`) |
| `rust-lang/rfcs` (`f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4`) | `text/3514-float-semantics.md` | Normative RFC 3514 NaN nondeterminism, `sNaN` rule, CTFE vs. runtime behavior `L50-155` |
| `llvm/llvm-project` (`6dfe1677ab8dffbc6ec13d53a1e0215d75147689`) | `llvm/docs/LangRef.md` | Normative specifications of `noundef`, `or disjoint`, `sdiv exact`/`udiv exact`, `nsw`/`nuw`, `fast` vs. `reassoc nsz arcp contract`, `fptoui`/`fptosi`, `@llvm.fptoui.sat`, `!unpredictable` |
| `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`) | `trusted/lean/Trusted/{MirAst,MirSemantics}.lean`, `trusted/correspondence/Trusted/Correspondence.lean` | `BinOp` `MirAst.lean:400-434`; `MirTy` `L290-315`; `Rvalue` `L620-628`; `evalShiftOp`/`evalArithOp` `MirSemantics.lean:1034-1090`; `toMiriBinOp`/`toMiriStatementForDispatch` `Correspondence.lean:920-945, 2016-2029` |

### Preserved Package Artifacts (`support/`)

- `support/probe_poison_float_nan_and_f16_f128.py` — standalone, zero-dependency Python 3.10+ empirical harness running all 20 Miri cases (+ 4 supplementary Miri probes) and compiling the 15-function pre-pass LLVM IR module (`-C opt-level=2 -C no-prepopulate-passes`), scrubbing host paths and PIDs before emitting JSON.
- `support/probe_results.json` — live execution output captured on `2026-11-22` on `x86_64-unknown-linux-gnu` using `rustc 1.98.0-nightly (14210df0e27ccd7d9e6a05b8085cbd438e4bbc65)`, `LLVM 22.1.6`, and `miri 0.1.0 (14210df0e2)`.
- `support/recorded_llvm23_miri_1_102_0_nightly.json` — scrubbed baseline execution output recorded on `rustc 1.102.0-nightly (3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1)` with `LLVM 23.1.5` across the identical 20 Miri cases and 14 LLVM IR functions.
- `support/PoisonIntrinsicsAndFloatSemantics.lean` — standalone `Lean v4.34.1` formalization (no external Lean dependencies, zero `sorry`, zero `Classical.choice`, zero `omega`/`bv_decide`/`native_decide`).
- `support/lean_check_output.txt` — exact stdout of `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true support/PoisonIntrinsicsAndFloatSemantics.lean` (exit code `0`, 26 `#print axioms` entries listing only `[propext, Quot.sound]`, `[propext]`, or no axioms).
- `support/lean_axioms_all_theorems.txt` — exhaustive `#print axioms` check across all 35 `theorem` declarations (including private helper lemmas), verifying zero forbidden axioms anywhere in the file.

---

## Revalidation

### 1. Re-run the Empirical `rustc` + LLVM IR + Miri Probe

Requires a nightly `rustc` toolchain with the `miri` component configured (`cargo miri setup`):

```bash
python3 support/probe_poison_float_nan_and_f16_f128.py --out fresh_probe_results.json
```

**Discriminating checks:**
1. All 20 `miri_matrix.<case>.miri_rc` values equal `[0, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 101]` in order (in particular, `float_to_int_unchecked_u8_neg_0_9999_open_interval_ok == 0`, `float_to_int_unchecked_i32_max_as_f32_rounds_to_2p31_ub == 1`, `fadd_fast_finite_inputs_infinite_output_ub == 1`, `fadd_algebraic_safe_const_and_runtime_nan_inf_ok == 0`, and `f128_powi_miri_todo_boundary == 101` until Miri implements host-free `f128` `powi`).
2. `select_unpredictable_intrinsic_forgets_vs_hint_drops.stdout == "DROPS intrinsic=1 hint=2"`.
3. `fadd_fast_4ulp_nondeterminism_default_miri.stdout` shows `max_ulp=4` (`distinct` up to `9`), while `fadd_fast_deterministic_floats_exact.stdout == "FADD_FAST_DET distinct=1 exact=0x40400000"`.
4. `nan_nondeterminism_ctfe_vs_miri_default.stdout` shows `ctfe=0x7fc00000`, `zdivz=["0x7fc00000", "0xffc00000"]`, `snan_prop_count=6`, and `has_signaling_out=true`.
5. `llvm_ir_lowering` contains `llvm.fptoui.sat`, `fptoui`, `or disjoint`, `sdiv exact`, `udiv exact`, `add nsw`, `add nuw`, unmasked `shl`, `fadd fast`, `fadd reassoc nsz arcp contract` (no `nnan`/`ninf`), `select ... !unpredictable`, `llvm.memcpy` with `select ptr ... !unpredictable`, and `half noundef %x, fp128 noundef %y` returning `fp128`.

### 2. Re-check the `Lean v4.34.1` Mechanization

```bash
lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
    support/PoisonIntrinsicsAndFloatSemantics.lean
```

Expected: exit code `0`, zero errors or warnings, and every `#print axioms` line reports only `propext` and `Quot.sound` (or no axioms).

### 3. Targeted Upstream Source Diffs

When tracking newer `rust-lang/rust` or `joshlf/anneal` commits, diff only these narrow regions:
- `library/core/src/intrinsics/fallback.rs` (`trait DisjointBitOr`) and `library/core/src/hint.rs` (`pub const fn select_unpredictable`).
- `compiler/rustc_codegen_ssa/src/mir/{intrinsic.rs,rvalue.rs}`, `compiler/rustc_codegen_ssa/src/base.rs` (`build_shift_expr_rhs`), `compiler/rustc_llvm/llvm-wrapper/RustWrapper.cpp` (`LLVMRustSetFastMath`, `LLVMRustSetAlgebraicMath`).
- `compiler/rustc_const_eval/src/interpret/{intrinsics.rs,cast.rs,machine.rs,operator.rs}` and `src/tools/miri/src/{operator.rs,math.rs,intrinsics/math.rs}` (specifically watching whether `FloatTy::F128 => todo!("f128")` is replaced by soft-float `powi`/`powf`/transcendental implementations).
- `joshlf/anneal`: `MirTy`, `Rvalue`, `StatementKind`, `evalShiftOp`, and `evalArithOp` in `trusted/lean/Trusted/{MirAst,MirSemantics}.lean` and `toMiriStatementForDispatch` in `trusted/correspondence/Trusted/Correspondence.lean`.
