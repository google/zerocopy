# Multi-Profile `.anneal-mir` Subsumption Across `overflow-checks`, `debug-assertions`, and `panic=unwind/abort`

## Summary

While `Runtime(PostCleanup)` MIR (`tcx.mir_drops_elaborated_and_const_checked`) in
`rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) is 100% byte-for-byte
invariant across all six optimization levels (`-C opt-level=0, 1, 2, 3, s, z`),
three Cargo profile flags—`-C overflow-checks=on/off`, `-C debug-assertions=on/off`,
and `-C panic=unwind/abort`—alter MIR construction or pre-`PostCleanup` drop/unwind
lowering (`rustc-pre-postcleanup-lowerings-and-minissa-canonicalizer-replacement`).
Combining compiler source inspection of `compiler/rustc_mir_build/src/builder/expr/as_rvalue.rs`
and `compiler/rustc_mir_transform/src/abort_unwinding_calls.rs`, a zero-axiom Lean
`v4.34.1` mechanization
([`support/MirProfileSubsumptionProbe.lean`](support/MirProfileSubsumptionProbe.lean)),
and a $20 \times 8 = 160$-compilation empirical matrix across all $2^3 = 8$
profile combinations in `rustc 1.99.1`
([`support/profile_subsumption_8way_matrix.json`](support/profile_subsumption_8way_matrix.json))
establishes that **a single Anneal verification proof discharged on the strictest
verification profile `P0 (overflow-checks=on, debug-assertions=on, panic=unwind)`
soundly certifies all seven looser profiles—including production release binaries
`P7 (overflow-checks=off, debug-assertions=off, panic=abort)`—when guarded by the
linear-time structural diff checker `checkProfileSubsumption`**:

1. **Exact Pre-`PostCleanup` Lowering Delta Across the Three Profile Axes:**
   - **Axis 1 — `-C overflow-checks=on` vs. `off` (`as_rvalue.rs:102-123, 456-528`):**
     During `mir_built`, `self.check_overflow` lowers `+`, `-`, `*` on integrals to
     `_tmp = Rvalue::BinaryOp(AddWithOverflow | SubWithOverflow | MulWithOverflow,
     (lhs, rhs))` followed by `TerminatorKind::Assert { cond: !(_tmp.1), expected:
     true, msg: Overflow(..), target: bb_next }` and `_res = (_tmp.0)`; lowers
     `<<`, `>>` to `Assert(unsigned_rhs < lhs_bits)` + `BinaryOp(Shl | Shr)`; and
     lowers signed unary `-x` to `Assert(!(x == MIN))` + `UnaryOp(Neg)`. Under
     `-C overflow-checks=off`, those `Assert` terminators are omitted and `+`, `-`,
     `*` emit `Rvalue::BinaryOp(Add | Sub | Mul)` directly (whereas `/` and `%`
     **always** emit `DivisionByZero` and signed `MIN / -1` `Assert`s regardless
     of `-C overflow-checks`, `as_rvalue.rs:529-590`).
   - **Axis 2 — `-C debug-assertions=on` vs. `off` (`simplify_branches.rs:27`):**
     Because `debug_assert!(cond)` expands to `if cfg!(debug_assertions) {
     assert!(cond); }` and `SimplifyConstCondition` only runs during
     `run_optimization_passes` (*after* `Runtime(PostCleanup)`), **both**
     `debug-assertions=on` and `debug-assertions=off` retain the full
     `debug_assert!` CFG diamond `bb0 -> [bb_check, bb_bypass] -> bb_join` at
     `Runtime(PostCleanup)` MIR! They differ only in the guard assignment
     `_c = const true` vs. `_c = const false` before `switchInt(move _c)`.
   - **Axis 3 — `-C panic=unwind` vs. `abort` (`abort_unwinding_calls.rs:133-141`):**
     `AbortUnwindingCalls` (which runs at `Runtime(Initial)` before
     `Runtime(PostCleanup)`) rewrites every `UnwindAction::Cleanup(bb)` and
     `UnwindAction::Continue` on potentially unwinding terminators to
     `UnwindAction::Terminate(UnwindTerminateReason::Abi)` and prunes dead
     `bb (cleanup)` blocks via `remove_dead_blocks`.
2. **Kernel-Checked Cross-Profile Subsumption Theorems in Lean `v4.34.1`
   (`CheckedImpliesWrapping_sound`, `DebugAssertImpliesRelease_sound`,
   `UnwindImpliesAbort_sound`, `MasterProfileSubsumption_sound`):**
   - In Anneal's `Trusted.VerificationResult` (`VerifyNoPanic P Q`), every
     verified function is proven to satisfy all `Assert` conditions and never
     panic on inputs satisfying precondition $P$.
   - When `AddWithOverflow(a, b)` is proven not to overflow (`a + b < 2^W`), its
     checked result and its wrapping result `(a + b) mod 2^W` are bit-for-bit
     identical (`evalNode_subsumption_preserves_ok`,
     [`support/MirProfileSubsumptionProbe.lean:170-236`](support/MirProfileSubsumptionProbe.lean#L170-L236)).
   - When a `debug_assert!` diamond `bb_check -> bb_join` is verified by
     `checkProfileSubsumption` to be **side-effect-free on outer locals and
     memory**, bypassing `bb_check` under `_c = const false` reaches `bb_join`
     in the exact same program state as passing through `bb_check` when the
     assertion holds (`DebugAssertImpliesRelease_sound`,
     [`support/MirProfileSubsumptionProbe.lean:281-291`](support/MirProfileSubsumptionProbe.lean#L281-L291)).
   - When no call or assertion unwinds under $P$, replacing `Cleanup(bb)` with
     `Terminate` leaves all reachable execution traces identical
     (`UnwindImpliesAbort_sound`,
     [`support/MirProfileSubsumptionProbe.lean:296-306`](support/MirProfileSubsumptionProbe.lean#L296-L306)).
3. **`144 / 144` Subsumption Coverage Across Pure Functions and `8 / 8` Rejection
   of Side-Effecting `debug_assert!` / `#[cfg(debug_assertions)]` Hazards:**
   - Across `18` pure functions compiled under all `8` profiles (`144` profile
     pairs in [`support/profile_subsumption_8way_matrix.json`](support/profile_subsumption_8way_matrix.json)),
     `checkProfileSubsumption` certifies **`144 / 144` (`100%`)**.
   - Across the `2` negative soundness tests—`n19_side_effecting_debug_assert`
     (`debug_assert!({ x = x.wrapping_add(1); x > 0 })`, where `bb2` inside the
     `debug_assert!` diamond mutates parameter `_1`) and
     `n20_cfg_debug_assertions_divergent` (`#[cfg(debug_assertions)]` constant
     divergence `100` vs. `200`)—`checkProfileSubsumption` rejects **`8 / 8`
     (`100%`)** of the `debug-assertions=off` targets (`sideEffectingDebugAssert_subsumption_rejected`,
     [`support/MirProfileSubsumptionProbe.lean:328-330`](support/MirProfileSubsumptionProbe.lean#L328-L330)).

## Applicability

This report applies to `rustc 1.99.1`
(`58cf8f9c35b355199727627d07ae34a4e2846d67`), `Lean 4 v4.34.1`
(`5045d0056413266e57c625dcd7c365b10e377c52`), and Anneal
(`joshlf/anneal@7abf0691c404393e3e4fc26eb3d4094e3170b5c7`) when certifying
multi-profile builds (`cargo anneal` vs. `cargo build --release`) across
`overflow-checks`, `debug-assertions`, and `panic` modes.

It extends two corpus reports:
- `rustc-pre-postcleanup-lowerings-and-minissa-canonicalizer-replacement`
- `bidirectional-mir-minissa-refinement-and-anneal-vc-transport`

Created: 2026-11-14 · Updated: 2026-11-14

## Findings

### 1. Exact `Runtime(PostCleanup)` MIR Structural Signatures Across the 8-Profile Lattice

Basis: source + execution

Compiling a function containing `debug_assert!(a < 100)` and `a + 1` (`f01` in
[`support/run_profile_subsumption_probe.py`](support/run_profile_subsumption_probe.py))
at `-Zmir-opt-level=0` (`Runtime(PostCleanup)` MIR) across the 8 profiles
reveals the exact structural correspondence:

| Profile ID | `overflow-checks` | `debug-assertions` | `panic` | `f01` BBs / Asserts / CheckedOps | `f10` (Drop Glue) BBs / Cleanup BBs / Terminate Edges | `n19` (Side-Effect `debug_assert!`) Verdict |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| **`P0_on_on_unwind` (Strictest)** | `on` | `on` | `unwind` | `12` / `1` / `2` | `4` / `1` / `0` | Baseline (`true`) |
| **`P1_on_on_abort`** | `on` | `on` | `abort` | `12` / `1` / `2` | `3` / `0` / `1` | `SUBSUMED_OK` |
| **`P2_on_off_unwind`** | `on` | `off` | `unwind` | `12` / `1` / `2` (`_3 = const false`) | `4` / `1` / `0` | **`REJECTED` (mutates `_1`)** |
| **`P3_on_off_abort`** | `on` | `off` | `abort` | `12` / `1` / `2` (`_3 = const false`) | `3` / `0` / `1` | **`REJECTED` (mutates `_1`)** |
| **`P4_off_on_unwind`** | `off` | `on` | `unwind` | `10` / `0` / `0` (`BinOp::Add`) | `3` / `1` / `0` | `SUBSUMED_OK` |
| **`P5_off_on_abort`** | `off` | `on` | `abort` | `10` / `0` / `0` (`BinOp::Add`) | `2` / `0` / `1` | `SUBSUMED_OK` |
| **`P6_off_off_unwind`** | `off` | `off` | `unwind` | `10` / `0` / `0` (`_3 = const false`) | `3` / `1` / `0` | **`REJECTED` (mutates `_1`)** |
| **`P7_off_off_abort` (Release)** | `off` | `off` | `abort` | `10` / `0` / `0` (`BinOp::Add`, `abort`) | `2` / `0` / `1` | **`REJECTED` (mutates `_1`)** |

Because `Runtime(PostCleanup)` MIR preserves the full `debug_assert!` diamond
`bb0: { _3 = const true/false; switchInt(move _3) -> [0: bb_bypass, otherwise:
bb_check] }` prior to `SimplifyConstCondition` (`simplify_branches.rs:27`),
`checkProfileSubsumption` does not need heuristics to guess which blocks came
from `debug_assert!`: it matches the exact `const true` vs. `const false` diff at
`bb0` and checks that no block reachable from `bb_check` before `bb_join`
writes to any local live at `bb_join` (other than the unit result `_2 = const ()`)
or performs any external side effect.

### 2. Lean `v4.34.1` Mechanization of Cross-Profile Subsumption

Basis: source + execution

All five theorems in
[`support/MirProfileSubsumptionProbe.lean`](support/MirProfileSubsumptionProbe.lean)
are kernel-checked in Lean `v4.34.1` with zero `sorryAx` and zero
`Lean.ofReduceBool`:

| Theorem Name | Lines | Mechanized Property |
| :--- | :---: | :--- |
| `evalNode_subsumption_preserves_ok` | `170-236` | Any single-node transition `.ok st'` under the stricter profile produces the exact same `.ok st'` under the looser profile when `checkNodeSubsumption = true`. |
| `CheckedImpliesWrapping_sound` | `266-276` | `VerifyNoPanic P Q` on `.checkedAdd delta bound` implies `VerifyNoPanic P Q` on `.wrappingAdd delta bound`. |
| `DebugAssertImpliesRelease_sound` | `281-291` | `VerifyNoPanic P Q` on `.pureDebugAssert minVal` implies `VerifyNoPanic P Q` on `.noopDebugAssert`. |
| `UnwindImpliesAbort_sound` | `296-306` | `VerifyNoPanic P Q` on `.callWithUnwind` implies `VerifyNoPanic P Q` on `.callWithTerminate`. |
| `MasterProfileSubsumption_sound` | `314-321` | `checkProfileSubsumption strictProg targetProg = true` transports `VerifyNoPanic P Q strictProg` to `VerifyNoPanic P Q targetProg` across arbitrary multi-node programs. |
| `sideEffectingDebugAssert_subsumption_rejected` | `328-330` | `checkProfileSubsumption` rejects lowering `.sideEffectDebugAssert` to `.noopDebugAssert`. |

### 3. Architectural Comparison: Dual-Profile `checkProfileSubsumption` vs. Parameterized `Runtime(PostCleanup)` MIR

Basis: derived + execution

| Criterion | Option 1: Paired `.anneal-mir` + `checkProfileSubsumption` (Recommended) | Option 2: Parameterized `Runtime(PostCleanup)` MIR |
| :--- | :--- | :--- |
| **Changes to `rustc_mir_build` & `AbortUnwindingCalls`** | **Zero** (`rustc` emits standard per-profile `Runtime(PostCleanup)` MIR). | Invasive: must rewrite `as_rvalue.rs` to gate `+`/`-`/`*` behind `Operand::RuntimeChecks(OverflowChecks)` and keep conditional `cleanup` pads in `AbortUnwindingCalls`. |
| **Handling of `#[cfg(debug_assertions)]` HIR divergence** | **Exact**: structural diff between `mir_strict` and `mir_release` catches any `#[cfg(debug_assertions)]` divergence (`n20`) automatically. | Cannot detect AST-level `#[cfg(debug_assertions)]` divergence without still comparing two HIR/MIR expansions. |
| **Checking Cost in `cargo anneal`** | Linear $O(|B|)$ structural diff (`< 0.2 ms` per function); `0` extra Lean kernel obligations via `MasterProfileSubsumption_sound`. | Increases `MiniSSA` / Anneal symbolic state space with symbolic profile flags. |

## Boundaries

1. **Specifications That Intentionally Assert Panic on Overflow (`known not to apply`):**
   - `CheckedImpliesWrapping_sound` applies to Anneal's standard `NoPanic`
     verification contract (`VerifyNoPanic P Q`, where every `Assert` is proven
     not to fail). If a test or specification instead asserts that a function
     *must panic* when `a + b >= 2^W`, `overflow-checks=on` panics while
     `overflow-checks=off` wraps and returns normally.
2. **Arbitrary `#[cfg(debug_assertions)]` Blocks (`known not to apply`):**
   - User code gated by `#[cfg(debug_assertions)]` that alters function bodies or
     struct layouts beyond pure assertion diamonds is rejected by
     `checkProfileSubsumption` (`n20_cfg_debug_assertions_divergent`) and
     requires profile-specific verification if the release branch differs
     computationally.

## Evidence

1. **Compiler Source Coordinates (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`):**
   - `compiler/rustc_mir_build/src/builder/expr/as_rvalue.rs:102-123, 456-590`
     (`self.check_overflow` lowering of `Neg`, `Add`, `Sub`, `Mul`, `Shl`, `Shr`,
     and unconditional checking of `Div`, `Rem`).
   - `compiler/rustc_mir_transform/src/abort_unwinding_calls.rs:48-141`
     (`AbortUnwindingCalls` rewrite of `UnwindAction::Cleanup` to
     `UnwindAction::Terminate(UnwindTerminateReason::Abi)`).
   - `compiler/rustc_mir_transform/src/simplify_branches.rs:15-98`
     (`SimplifyConstCondition` deferred to `run_optimization_passes`).
2. **Lean `v4.34.1` Mechanization (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`):**
   - [`support/MirProfileSubsumptionProbe.lean`](support/MirProfileSubsumptionProbe.lean)
     (zero `sorryAx`, zero `Lean.ofReduceBool`).
3. **Executable 8-Profile Matrix Probe and Preserved Dataset:**
   - [`support/run_profile_subsumption_probe.py`](support/run_profile_subsumption_probe.py)
   - [`support/profile_subsumption_8way_matrix.json`](support/profile_subsumption_8way_matrix.json)

## Revalidation

```bash
anneal-lean-run --mode file --concurrency 4 -- lake env lean \
  reports/mir-profile-subsumption-overflow-checks-debug-assertions-and-panic-modes/support/MirProfileSubsumptionProbe.lean
python3 reports/mir-profile-subsumption-overflow-checks-debug-assertions-and-panic-modes/support/run_profile_subsumption_probe.py
```
