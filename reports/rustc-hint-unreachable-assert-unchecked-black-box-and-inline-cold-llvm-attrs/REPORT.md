# Lowering, Precondition Checks, and Attribute Semantics for `core::hint::{unreachable_unchecked, assert_unchecked, black_box}` and `#[inline]` / `#[cold]` in `rustc` and LLVM

## Summary

`rustc` lowers `core::hint::unreachable_unchecked`, `core::hint::assert_unchecked`, `core::hint::black_box`, and the function attributes `#[inline]`, `#[inline(always)]`, `#[inline(never)]`, and `#[cold]` across three distinct compiler boundaries (`core` pre-compiled MIR, crate-local MIR optimization passes, and LLVM IR code generation / pass pipelines) rather than via uniform single-pass lowering ([source], [execution]). Consequently, subtle pass-ordering and optimization-level interactions govern runtime abort behavior, cross-crate inlining without Link-Time Optimization (LTO), attribute conflict precedence, and Undefined Behavior (UB) elimination ([source], [execution]).

Six primary findings establish the end-to-end ground truth across `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, LLVM `22.1.6`), comparison revision `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, LLVM `23.1.5`), upstream LLVM (`2fcb2d3403190ac9353eddd23a92716e937e0739`), and `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`):

1. **`core::hint::unreachable_unchecked` traps even at `-C opt-level=0 -C debug-assertions=off -Z ub-checks=no`, whereas `core::hint::assert_unchecked(false)` runs cleanly under `-O0`**: Because `library/core/src/lib.rs` declares `#![rustc_preserve_ub_checks]`, `core`'s own compilation skips `SimplifyUbCheck`, leaving `Operand::RuntimeChecks(UbChecks)` symbolic during MIR optimization of `core` ([source]). Inside `core::hint::unreachable_unchecked`, `UnreachablePropagation` runs *before* `InstSimplify::AfterSimplifyCfg` and prunes arm `0` (`false`) of `switchInt(UbChecks)` because that arm terminates in `intrinsics::unreachable()`, baking `assume(UbChecks); unreachable_unchecked::precondition_check()` unconditionally into `core`'s distributed `optimized_mir` ([source], [execution]). When a downstream crate compiles with `-C opt-level=0` (even with `-Z ub-checks=no`), MIR `Inline` is disabled (`mir_opt_level = 1`), so `unreachable_unchecked` instantiates `core`'s pre-compiled MIR where `codegen_ssa` lowers `UbChecks` to `i1 false`; LLVM `OptLevel::No` suppresses `@llvm.assume(i1 false)` in `Builder::assume`, leaving an unconditional `call` to `unreachable_unchecked::precondition_check`, which aborts with `SIGABRT` (`rc = -6`) ([source], [execution]). By contrast, `core::hint::assert_unchecked(cond)` has a normal `return` on arm `0`, so its `switchInt(UbChecks)` survives in `optimized_mir`; at `-O0 -C debug-assertions=off`, downstream lowers `UbChecks` to `false`, skips `precondition_check`, suppresses `@llvm.assume`, and executes cleanly (`ASSERT_OK`, `rc = 0`) while `AlwaysInlinerPass` still inlines its `#[inline(always)]` body ([source], [execution]).
2. **`@llvm.assume` emission toggles strictly at `OptLevel::No`, driving dead-branch pruning and modular `noundef range` return refinement at `-O1` and above**: In `compiler/rustc_mir_transform/src/lower_intrinsics.rs`, `intrinsics::assume` lowers into `StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(arg.node))` followed by `TerminatorKind::Goto`, and `intrinsics::unreachable` lowers into `TerminatorKind::Unreachable` ([source]). At LLVM codegen (`compiler/rustc_codegen_llvm/src/intrinsic.rs`), `Builder::assume` skips emitting `@llvm.assume` whenever `optimize == OptLevel::No` (`-O0`), yet emits `call void @llvm.assume(i1 ...)` (with `IntrWriteMem`, `IntrInaccessibleMemOnly`, `NoUndef<0>` per `Intrinsics.td`) at `-O1` and `-O2` ([source], [execution]). At `-O1` without MIR `Inline`, `@llvm.assume(i1 false)` before `precondition_check` enables LLVM to collapse `unreachable_unchecked()` to `unreachable`; at `-O2`, MIR `Inline` + `SimplifyUbCheck` + `SimplifyConstCondition` already folds `assume(false)` to `TerminatorKind::Unreachable` in MIR before LLVM ([execution]). For `if x == 0 { unreachable_unchecked() }; x.wrapping_add(1)`, both `-O1` and `-O2` prove `x != 0` via `@llvm.assume`, delete the check branch, and via `CorrelatedValuePropagationPass` annotate the LLVM function return signature with `define noundef range(i32 2, 1) i32` ([execution]). Meanwhile Miri immediately halts on both invalid invocations with `Undefined Behavior: entering unreachable code` and ``Undefined Behavior: `assume` called with `false` `` (`rc = 1`) ([execution]).
3. **`core::hint::black_box` is a semantic value identity usable in `const` and Miri, lowered at runtime to a volatile empty inline-asm memory clobber**: Marked `#[inline]` and `#[rustc_const_stable]`, `core::hint::black_box` delegates to `intrinsics::black_box`, which MIR does *not* lower in `LowerIntrinsics` and MIR `NormalInliner` refuses to inline as a `must_be_overridden` intrinsic ([source]). Const evaluation (`Miri` / CTFE) evaluates `black_box(e)` transparently as the identity (`CONST_BB=7`), whereas `rustc_codegen_llvm`'s `Builder::black_box` stores non-zero-sized values to a destination stack slot and emits `call void asm sideeffect "", "r,~{memory}"(ptr %_1)` (and `tail call void asm sideeffect "", "~{memory}"()` for zero-sized `()`), preventing LLVM constant propagation across `black_box(2) + black_box(3)` ([source], [execution]).
4. **Attribute lowering splits cleanly across `#[inline]`, `#[inline(always)]`, `#[inline(never)]`, `#[cold]`, and `#[optimize(none)]`, with first-wins conflict parsing**: `rustc_codegen_llvm::attributes::inline_attr` maps `InlineAttr::Hint` to `inlinehint`, `InlineAttr::Always | Force` to `alwaysinline` in `14210df0e` (with `3ef0c22cd` adding a downgrade to `inlinehint` if target features are present and LLVM `< 23`), `InlineAttr::Never` to `noinline` (except AmdGpu), and `OptimizeAttr::DoNotOptimize` (`#[optimize(none)]`) to `noinline` + `optnone` ([source], [execution]). `#[cold]` sets LLVM `cold` independently without implying `noinline` ([source], [execution]). When conflicting inline attributes stack (`#[inline(always)] #[inline(never)]` vs `#[inline(never)] #[inline(always)]`), `InlineParser` uses `Single<T>` (`ON_DUPLICATE = WarnButFutureError`), keeping the **first** attribute and emitting `#[warn(unused_attributes)]` (future error, hard error under `-Dwarnings`) on the second; moreover, adding `#[inline(always)]` to an exported `#[unsafe(no_mangle)]` function still lowers `alwaysinline` onto the LLVM definition despite emitting `warning: #[inline] is ignored on externally exported functions` ([source], [execution]).
5. **Cross-crate inlining without LTO is governed by `cross_crate_inlinable` + `CostChecker` (`calls == 0`) rather than attributes alone**: `cross_crate_inlinable` returns `false` for exported symbols (`contains_extern_indicator()`), `#[inline(never)]`, and non-leaf functions with calls (`calls > 0`), and `true` for `#[inline]`, `#[inline(always)]`, and small unannotated leaf functions (`calls == 0 && resumes == 0 && landing_pads == 0 && statements <= threshold`) at `-O2` non-incremental ([source], [execution]). At `-O0`, LLVM's `PassBuilder::buildO0DefaultPipeline` still runs `AlwaysInlinerPass`, inlining cross-crate `#[inline(always)]` while leaving `#[inline]`, `#[cold]`, and unannotated leaves as external `call` instructions ([source], [execution]). Enabling `-C incremental=...` disables MIR `NormalInliner` (`Inline::policy`) cleanly ([source], [execution]).
6. **Anneal boundary & Lean v4.34.1 mechanization**: In `joshlf/anneal` (`c131b320e`), `Trusted.MirAst` and `Trusted.MirSemantics` step `TerminatorKind.unreachable` to `.fault .undefined`, collapse `StatementKind::Intrinsic` (`Assume`) to `.unsupported`, and explicitly leave `Operand::RuntimeChecks` (`ub_checks`) unmodeled so capture must fail closed rather than folding it to a constant ([source]). Our standalone Lean v4.34.1 mechanization (`support/HintAssumeBlackBoxAndInlineAttrsSoundness.lean`, `2,466` LOC, `313` theorems, `485` `noncomputable def`s, `0` `._unsafe_rec`, `0` violations, axioms strictly within `[propext, Quot.sound]`) proves refinement (`abortOnFalse` soundly refines `ubOnFalse`), pre-compiled `core` `-O0` trap asymmetry, `assume`-guided dead-branch pruning soundness (with sharpness counterexamples) and modular `i32` `range(i32 2, 1)` refinement, `black_box` identity plus folding-barrier preservation, and attribute/inlining equivalence ([derived], [execution]).

## Applicability

This report applies to Rust programs compiled with `rustc` and LLVM targeting host and library code on `x86_64-unknown-linux-gnu` using Rust Edition 2024 ([source], [execution]), and to static-verification consumers modeling MIR and LLVM IR lowering boundaries ([source], [derived]).

| Subject Component | Exact Version / Pinned Revision | Role in This Report | Applicability Conditions & Scope Notes |
| --- | --- | --- | --- |
| `rust-lang/rust` (`rustc`, `core`, `miri`) | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`, `2026-05-31`) | Primary source audit **and** live compiler, MIR dump, LLVM IR, native execution, and Miri execution ([source], [execution]) | Default `x86_64-unknown-linux-gnu` target; standard pre-compiled `core` sysroot (`#![rustc_preserve_ub_checks]`) ([source], [execution]). |
| `rust-lang/rust` comparison revision | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`1.102.0-nightly`, `2026-11-11`) | Primary source audit and comparison against local `14210df0e` behavior ([source]) | `hint.rs`, `lower_intrinsics.rs`, `cross_crate_inline.rs`, `inline.rs`, `intrinsic.rs`, and `attributes.rs` fetched directly ([source]); live binaries on this host ran `14210df0e`, while `3ef0c22cd` was not directly executed on this host (`not examined` locally beyond comparison source audit). |
| `rust-lang/llvm-project` (LLVM `22.1.6`) | `08c84e69a84d95936296dfcab0e38b34100725d5` | Embedded LLVM backend executed by `rustc 1.98.0-nightly` ([execution]) | Exact submodule commit resolved from `rust-lang/rust@14210df0e`. |
| `rust-lang/llvm-project` (LLVM `23.1.5`) | `0a5579eb649d3634a9c30ac873300cc2944fa070` | Submodule paired with comparison revision `3ef0c22cd` ([source]) | Exact submodule commit resolved from `rust-lang/rust@3ef0c22cd`. |
| `llvm/llvm-project` (`main` upstream) | `2fcb2d3403190ac9353eddd23a92716e937e0739` | Primary source audit of `AlwaysInliner.cpp`, `InlineCost.cpp`, `PassBuilderPipelines.cpp`, `Intrinsics.td` ([source]) | Upstream C++ pass architecture matches LLVM 22/23 new pass manager pipelines observed in `-print-after-all` ([execution]). |
| `joshlf/anneal` verification boundary | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | Audit of `Trusted.MirAst`, `Trusted.MirSemantics`, and `trusted/rustc-capture/src/driver.rs` ([source]) | Determines which MIR constructs resulting from `core::hint` / `ub_checks` are modeled vs intentionally unmodeled or `.unsupported` in Anneal. |
| `leanprover/lean4` theorem prover | `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Kernel compilation and MetaM purity auditing of `support/HintAssumeBlackBoxAndInlineAttrsSoundness.lean` ([derived], [execution]) | Standalone pure core Lean (`Init` only), verified with `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`. |

**Cross-revision differences verified between `14210df0e` and `3ef0c22cd`:**

- `library/core/src/hint.rs`, `lower_intrinsics.rs`, `cross_crate_inline.rs`, `Builder::assume` (`optimize != OptLevel::No`), `Builder::black_box` (`inline_asm_call`), `Inline::policy` thresholds (`30` / `100` / `50` with `+25%` for `<= 3` blocks), and `AttributeKind::Cold` lowering match functionally between `14210df0e` and `3ef0c22cd` ([source]).
- In `compiler/rustc_codegen_llvm/src/attributes.rs`, `inline_attr` in `14210df0e` (`lines 45-77`) unconditionally maps `InlineAttr::Always | Force` to `AlwaysInline`, whereas comparison revision `3ef0c22cd` (`lines 73-78`) adds a guard downgrading `InlineAttr::Always` to `InlineHint` when `!codegen_fn_attrs.target_features.is_empty() && llvm_util::get_version() < (23, 0, 0)` so LLVM `< 23` does not force-inline a target-featured callee into a caller lacking those features ([source]). Separately, on free functions in `rustc 1.98.0-nightly` (`14210df0e`), combining `#[inline(always)]` with `#[target_feature(enable = "avx2")]` already fails earlier with a hard frontend error (`error: cannot use #[inline(always)] with #[target_feature]`, referencing Rust issue `#145574`), while `#[inline]` + `#[target_feature(enable = "avx2")]` compiles cleanly with `inlinehint` ([execution]).
- Runtime compilation and LLVM IR behavior on `3ef0c22cd` (`1.102.0-nightly`, LLVM `23.1.5`) was not executed locally (`not examined`); all live MIR, LLVM IR (`captures(address, read_provenance)` panic calls, `noundef range(i32 2, 1)`), execution, and Miri findings are observed directly on `14210df0e` (LLVM `22.1.6`) ([execution]).

**Flag and build-profile conditions:**

- When compiling downstream code that uses `#[inline]` on exported `#[unsafe(no_mangle)]` symbols or stacks conflicting `#[inline(...)]` attributes, `rustc` emits `unused_attributes` (warn by default, error with `-Dwarnings`) ([execution]).
- `#[optimize(none)]` (`OptimizeAttr::DoNotOptimize`) requires `#![feature(optimize_attribute)]` on nightly `rustc 1.98.0-nightly` ([source], [execution]).
- Release Undefined Behavior runtime symptoms (e.g., returning normally by fallthrough `REACHED` / `ASSERT_OK` vs trapping with `SIGILL` via `ud2` in standalone `!` functions) depend on surrounding control flow and target codegen; never infer absence of UB from a `rc = 0` release binary output ([normative], [execution]).

## Findings

### 1. Core Hint Intrinsics and the `ub_checks` Runtime/Const Gate

In `library/core/src/hint.rs`, the three intrinsics follow deliberately asymmetric inlining and precondition-checking contracts ([source]):

- **`core::hint::unreachable_unchecked`** (`14210df0e` lines `99-112`, `3ef0c22cd` lines `95-115`): Marked `#[inline]` and `#[track_caller]`. Its body calls `crate::ub_checks::assert_unsafe_precondition!(check_language_ub, "hint::unreachable_unchecked must never be reached", () => false)` followed by `unsafe { intrinsics::unreachable() }` ([source]).
- **`core::hint::assert_unchecked`** (`14210df0e` lines `197-212`, `3ef0c22cd` lines `195-215`): Marked `#[inline(always)]` and `#[track_caller]`. Its body calls `crate::ub_checks::assert_unsafe_precondition!(check_language_ub, "hint::assert_unchecked must never be called when the condition is false", (cond: bool = cond) => cond)` followed by `unsafe { crate::intrinsics::assume(cond) }` ([source]).
- **`core::hint::black_box`** (`14210df0e` lines `487-492`, `3ef0c22cd` lines `485-495`): Marked `#[inline]` and `#[rustc_const_stable]`. Its body simply calls `crate::intrinsics::black_box(dummy)` ([source]).

In `library/core/src/ub_checks.rs` (`14210df0e` lines `53-108`), `assert_unsafe_precondition!` defines an inner helper `const fn precondition_check` annotated `#[rustc_no_mir_inline] #[inline] #[rustc_nounwind] #[track_caller]` that calls `panic_nounwind_fmt(..., /* force_no_backtrace */ false)` ([source]). The macro guards the helper call under `if ::core::ub_checks::$kind() { precondition_check(...) }`. Crucially, `check_language_ub()` uses `const_eval_select!`: in `const` evaluation (`compiletime`), it always returns `false`; at `runtime`, it returns `!cfg!(miri) && intrinsics::ub_checks()` ([source]).

Why `!cfg!(miri)`? Miri runs `rustc_const_eval`'s MIR interpreter directly on MIR, checking `TerminatorKind::Unreachable` (`Undefined Behavior: entering unreachable code`) and `NonDivergingIntrinsic::Assume(false)` (``Undefined Behavior: `assume` called with `false` ``) natively inside `rustc_const_eval/src/interpret/` without needing `precondition_check` panics ([source], [execution]). Meanwhile, native runtime binaries query `intrinsics::ub_checks()`, which reads `Session::ub_checks()` — enabled by explicit `-Zub-checks=yes` or `-Cdebug-assertions=on` unless overridden by `-Zub-checks=no` ([source]).

### 2. Why `unreachable_unchecked()` Aborts at `-O0 -Cdebug-assertions=off -Zub-checks=no` While `assert_unchecked(false)` Runs

Empirical execution reveals a striking asymmetry between `unreachable_unchecked` and `assert_unchecked` under `-C opt-level=0` ([execution]):

| Binary Invocation Case | Opt / Debug / UB Flags | Observed Exit Code (`rc`) | Observed `stdout` / `stderr` | Mechanism Root Cause |
| --- | --- | --- | --- | --- |
| `unreachable_unchecked()` | `-O0 -Cdebug-assertions=on` | `-6` (`SIGABRT`) | `unsafe precondition(s) violated: hint::unreachable_unchecked must never be reached` -> `aborting.` | `UbChecks` lowers to `true`; `precondition_check()` aborts ([source], [execution]). |
| `unreachable_unchecked()` | `-O0 -Cdebug-assertions=off` | `-6` (`SIGABRT`) | Same `panic_nounwind_fmt` abort message | `core` pre-compiled MIR baked `precondition_check()`, and LLVM `-O0` drops `@llvm.assume(false)` ([source], [execution]). |
| `unreachable_unchecked()` | `-O0 -Cdebug-assertions=off -Zub-checks=no` | `-6` (`SIGABRT`) | Same `panic_nounwind_fmt` abort message | Even `-Zub-checks=no` cannot stop the `-O0` trap because `precondition_check()` sits unconditional in `core`'s MIR before `@llvm.assume(false)` ([source], [execution]). |
| `unreachable_unchecked()` | `-O1 -Cdebug-assertions=off -Zub-checks=no` | `0` | `REACHED` (empty stderr) | MIR `Inline` still off, *but* LLVM `-O1` emits `call void @llvm.assume(i1 false)` and folds the unreachable call away ([source], [execution]). |
| `unreachable_unchecked()` | `-O2 -Cdebug-assertions=off -Zub-checks=no` | `0` | `REACHED` (empty stderr) | MIR `Inline` + `SimplifyUbCheck` + `SimplifyConstCondition` removes `precondition_check` in MIR before LLVM ([execution]). |
| `assert_unchecked(false)` | `-O0 -Cdebug-assertions=on` | `-6` (`SIGABRT`) | `unsafe precondition(s) violated: hint::assert_unchecked must never be called when the condition is false` -> `aborting.` | `UbChecks` is `true`, calling `precondition_check(false)` ([source], [execution]). |
| `assert_unchecked(false)` | `-O0 -Cdebug-assertions=off [-Zub-checks=no]` | `0` | `ASSERT_OK` | `switchInt(UbChecks)` stays in `core` MIR; downstream lowers `UbChecks` to `i1 false`, skips check, drops `@llvm.assume` ([source], [execution]). |
| `assert_unchecked(false)` | `-O2 -Cdebug-assertions=off -Zub-checks=no` | `0` | `ASSERT_OK` | Group A binary executes `main` and falls through into `println!("ASSERT_OK")` (`rc = 0`); in Group C, standalone `lower_assume` compiles to `ret void` ([execution]). |
| Guarded safe `compute(x)` (`x=0` early-returns, else `assert_unchecked(x != 0)`) | `-O2 -Cdebug-assertions=off -Zub-checks=no` | `0` | `GUARDED_OK=25,25` | Sound guard before `assert_unchecked(x != 0)` makes runtime execution valid ([execution]). |
| Miri on `unreachable_unchecked()` | `cargo miri run --offline` | `1` | `error: Undefined Behavior: entering unreachable code` | Miri checks MIR `Unreachable` directly (`!cfg!(miri)`) ([source], [execution]). |
| Miri on `assert_unchecked(false)` | `cargo miri run --offline` | `1` | ``error: Undefined Behavior: `assume` called with `false` `` | Miri checks MIR `Assume` directly ([source], [execution]). |
| Miri on `assert_unchecked(true)` | `cargo miri run --offline` | `0` | `MIRI_TRUE_OK` | Valid runtime assumption passes Miri ([execution]). |

Tracing `compiler/rustc_mir_transform/src/` and `library/core/src/lib.rs` explains *exactly* why `unreachable_unchecked` traps at `-O0` even with `-Zub-checks=no` ([source]):

1. **Crate root attribute on `core`**: `library/core/src/lib.rs` line `77` enables `#![rustc_preserve_ub_checks]` ([source]). Inside `InstSimplify` (`compiler/rustc_mir_transform/src/instsimplify.rs` lines `33-36`), `SimplifyUbCheck` refuses to fold `Operand::RuntimeChecks(UbChecks)` to a boolean literal while compiling `core`, preserving the check cleanly for downstream crates ([source]).
2. **MIR pass ordering inside `run_optimization_passes`** (`compiler/rustc_mir_transform/src/lib.rs` lines `707-736`): `rustc` runs `ForceInline` (`707`) -> `Inline` (`709`) -> ... -> `UnreachableEnumBranching` (`720`) -> `UnreachablePropagation` (`721`) -> `o1(SimplifyCfg::AfterUnreachableEnumBranching)` (`722`) -> `InstSimplify::AfterSimplifyCfg` (`727`) -> `o1(SimplifyConstCondition::AfterInstSimplify)` (`736`) ([source]).
3. **`UnreachablePropagation` inside `core` eliminates arm `0` of `unreachable_unchecked` *before* `SimplifyUbCheck`**: When `core` itself is built in release optimization (`-O2`/`-O3`), `Inline` inlines `check_language_ub` into `core::hint::unreachable_unchecked`, producing `switchInt(UbChecks) -> [0: bb_unreach, otherwise: bb_check]` ([source]). Arm `0` goes straight to `bb_unreach: { unreachable; }`. Because `UnreachablePropagation` (`line 721`) runs cleanly *with `UbChecks` still symbolic* (`SimplifyUbCheck` inside `InstSimplify` doesn't simplify UB checks in `core` anyway, and runs later at line `727`), `UnreachablePropagation` proves arm `0` unconditionally reaches `unreachable`, replaces `switchInt(UbChecks)` with `assume(UbChecks)` (witnessed verbatim in downstream `-O2` `probe.lower_unreachable.3-2-004.Inline.after.mir`!), and makes `bb0` call `unreachable_unchecked::precondition_check()` unconditionally ([source], [execution]):
   ```text
   bb0: {
       StorageLive(_1);
       assume(UbChecks);
       _1 = unreachable_unchecked::precondition_check() -> [return: bb1, unwind unreachable];
   }
   ```
4. **Why `assert_unchecked` preserves `switchInt(UbChecks)`**: In `assert_unchecked(cond)`, arm `0` leads to `assume(copy _2); return;` (`probe.lower_assume.3-2-004.Inline.after.mir`), which is reachable rather than `unreachable`, so `UnreachablePropagation` cannot eliminate the branch ([source], [execution]).
5. **Downstream `-O0` (`OptLevel::No`) vs `-O1` (`OptLevel::Less`) vs `-O2` (`OptLevel::More`)**:
   - At `-O0`, `Session::mir_opt_level` returns `1` (`compiler/rustc_session/src/session.rs` lines `617-622`), so `Inline::policy` (`compiler/rustc_mir_transform/src/inline.rs` lines `46-61`) skips `NormalInliner` (`3-2-004.Inline` never runs in `opt0_debug_off_ub_no` MIR dumps!) ([source], [execution]). Downstream code therefore emits an actual `call` to monomorphized `core::hint::unreachable_unchecked`, instantiating `core`'s pre-compiled `optimized_mir` (`assume(UbChecks); precondition_check()`). Codegen lowers `Operand::RuntimeChecks(UbChecks)` to `i1 false` (`rustc_codegen_ssa/src/mir/operand.rs` line `1057`), and `Builder::assume` drops `@llvm.assume(i1 false)` under `OptLevel::No` (`intrinsic.rs` lines `1034-1038`) ([source]). Execution enters `precondition_check()` and aborts (`rc = -6`). By contrast, monomorphizing `#[inline(always)] assert_unchecked` runs `AlwaysInlinerPass` in LLVM (`PassBuilderPipelines.cpp` lines `1225`, `2374`) with `switchInt(false)` branching directly past `precondition_check` and dropping `@llvm.assume` (`ASSERT_OK`, `rc = 0`) ([source], [execution]).
   - At `-O1`, MIR `Inline` is still off (`mir_opt_level = 2`, `OptLevel::Less`), so `lower_unreachable` still lowers `core`'s MIR body, *except* `Builder::assume` now emits `call void @llvm.assume(i1 false)`, which LLVM's `-O1` optimizer folds immediately into `@lower_unreachable() { unreachable }` ([source], [execution]).
   - At `-O2`, MIR `Inline` runs (`3-2-004.Inline`), inlining `unreachable_unchecked` into the downstream body, `InstSimplify::AfterSimplifyCfg` (`SimplifyUbCheck`) replaces `UbChecks` with `const false`, and `SimplifyConstCondition::AfterInstSimplify` folds `assume(const false)` to `unreachable` directly in MIR (`3-2-011.SimplifyConstCondition-after-inst-simplify.after.mir`) *before* LLVM codegen runs ([source], [execution]).

### 3. LLVM `@llvm.assume` Semantics, Dead-Branch Pruning, and `noundef range(i32 2, 1)` Derivation

In `compiler/rustc_mir_transform/src/lower_intrinsics.rs` (`14210df0e` lines `23-25, 80-92`; `3ef0c22cd` lines `22-24, 90-102`), `LowerIntrinsics` transforms `sym::unreachable` into `TerminatorKind::Unreachable` and `sym::assume` into `StatementKind::Intrinsic(Box::new(NonDivergingIntrinsic::Assume(arg.node)))` plus `TerminatorKind::Goto` ([source]). In LLVM IR (`rustc_codegen_llvm/src/intrinsic.rs` lines `1034-1038`), `Builder::assume` emits `@llvm.assume` strictly iff `self.cx.sess().opts.optimize != OptLevel::No` ([source]):

- **At `-O0` (`-C opt-level=0 -C debug-assertions=off -Z ub-checks=no`)**:
  - `@prune_assert_unchecked_branch(i32 %x)` evaluates `%_3 = icmp ne i32 %x, 0`, **discards `@llvm.assume`**, computes `%_0 = icmp eq i32 %x, 0`, and returns `%_0` unpruned ([execution]).
  - `@prune_unreachable_branch(i32 %x)` keeps `br i1 %_2, label %bb1, label %bb2` and `call void @core::hint::unreachable_unchecked` on `%bb1` ([execution]).
- **At `-O1` and `-O2` (with `-C debug-assertions=off -Z ub-checks=no`)**:
  - LLVM declares `declare void @llvm.assume(i1 noundef) #4`, backed by `llvm/include/llvm/IR/Intrinsics.td` lines `1097-1101` (`IntrWriteMem, IntrInaccessibleMemOnly, NoUndef<ArgIndex<0>>`, explaining `memory(inaccessiblemem: write)` in resolved function attributes on `@lower_assume`, `@prune_assert_unchecked_branch`, and `@prune_unreachable_branch` at `-O2`) ([source], [execution]).
  - `@prune_assert_unchecked_branch(i32 noundef %x)` eliminates the contradictory comparison via `@llvm.assume(%x != 0)` and simplifies to `ret i1 false` at both `-O1` and `-O2` ([execution]).
  - `@prune_unreachable_branch(i32 noundef %x)` keeps the assumption `tail call void @llvm.assume(i1 %0)` (or `%_2`), eliminates the `x == 0` branch, computes `add i32 %x, 1`, and is annotated **`define noundef range(i32 2, 1) i32 @prune_unreachable_branch(i32 noundef %x)`** ([execution]). Tracing `-Cllvm-args=-print-after-all -Cllvm-args=-filter-print-funcs=prune_unreachable_branch` empirically identifies **`CorrelatedValuePropagationPass`** (`; *** IR Dump After CorrelatedValuePropagationPass on prune_unreachable_branch ***`) as the first LLVM pass attaching `range(i32 2, 1)` to the return value: excluding `0` mod $2^{32}$ and adding `1` yields the wrapped constant range $[2, 2^{32}-1] \cup [0, 0]$, i.e., `i32` excluding `1` (`range(i32 2, 1)`) ([execution]).
  - Conversely, unguarded `@lower_unreachable()` collapses to a single `unreachable` terminator at both `-O1` and `-O2` (carrying `mustprogress nofree norecurse noreturn nosync nounwind nonlazybind willreturn memory(none)`), whereas at `-O0` it retains the `call` to `core::hint::unreachable_unchecked` before `unreachable` ([execution]).

### 4. `core::hint::black_box`: Compiler-Barrier IR vs `const` and Miri Semantics

Unlike `assume` and `unreachable`, `sym::black_box` is intentionally *not* lowered in `LowerIntrinsics` (`lower_intrinsics.rs`), and MIR `NormalInliner` skips intrinsics (`cross_crate_inline.rs:38-44` explains `RustcIntrinsic` fallback bodies exist, so the MIR inliner never inlines `must_be_overridden` intrinsics) ([source]). Instead, `black_box` divergence splits cleanly between compile-time interpretation and LLVM backend emission:

1. **Const evaluation (`const` / CTFE) and Miri**: `core::hint::black_box` carries `#[rustc_const_stable]`, so `const C: i32 = core::hint::black_box(3 + 4);` evaluates cleanly at compile time to `CONST_BB=7` both natively and under `cargo miri run --offline`, with runtime `black_box(2) + black_box(3)` producing `RT_BB=5` ([source], [execution]).
2. **LLVM codegen (`Builder::black_box`)**: In `compiler/rustc_codegen_llvm/src/intrinsic.rs` (`14210df0e` lines `611-651`, `3ef0c22cd` lines `88-120`), for any non-ZST value `black_box` writes the operand into the destination stack `alloca` (`store i32 2, ptr %_1, align 4`) and executes a volatile inline assembly barrier `call void asm sideeffect "", "r,~{memory}"(ptr nonnull %_1)` (removing `"r,"` to emit `"~{memory}"()` for ZST `()` in `@black_box_zst`), then reloads `%0 = load i32, ptr %_1, align 4, !noundef !5` ([source], [execution]).
3. **Constant-folding barrier vs optimization invariants**: At `-O2`, `@plain_fold()` folds `2 + 3` directly into `ret i32 5` (`memory(none)`), whereas `@black_box_no_fold()` retains both `alloca` slots, both `asm sideeffect "", "r,~{memory}"` barriers, both `load`s, and the runtime `add i32 %1, %0`, dropping `memory(none)` and `willreturn` from `@black_box_no_fold`'s LLVM function attributes (`{ nounwind nonlazybind uwtable ... }`) ([execution]).

### 5. `#[inline]`, `#[inline(always|never)]`, `#[cold]`, and `#[optimize(none)]`: Attribute Precedence, Diagnostics, MIR/LLVM Inlining, and Cross-Crate Semantics

Function optimization attributes pass through four coordinated subsystems across `rustc` and LLVM ([source]):

| Rust Source Attribute(s) | Frontend Parse / Lint Behavior | Cross-Crate MIR Export (`-O2`, non-incr) | Emitted LLVM Fn Attribute(s) (`14210df0e`) | Live `-O0` vs `-O2` Cross-Crate Call Lowering |
| --- | --- | --- | --- | --- |
| *(unannotated leaf)* (`calls == 0`, small MIR) | Clean | `true` (`CostChecker`) | *(none)* | `-O0`: `call`; `-O2`: inlined cross-crate without LTO ([source], [execution]) |
| *(unannotated non-leaf)* (`calls > 0`) | Clean | `false` (`calls == 1`) | *(none)* | `-O0`: `call`; `-O2`: `tail call` cross-crate (`declare` emitted) ([source], [execution]) |
| `#[inline]` (`InlineAttr::Hint`) | Clean (unless exported) | `true` | `inlinehint` | `-O0`: `call`; `-O2`: inlined cross-crate ([source], [execution]) |
| `#[inline(always)]` (`InlineAttr::Always`) | Hard error if paired with `#[target_feature]` on free fn (`14210df0e`) ([execution]) | `true` | `alwaysinline` | **`-O0`: inlined (`AlwaysInlinerPass`)**; `-O2`: inlined ([source], [execution]) |
| `#[inline(never)]` (`InlineAttr::Never`) | Clean (even on `#[no_mangle]`) | `false` | `noinline` (except AmdGpu) | `-O0`: `call`; `-O2`: `tail call` (`declare` emitted) ([source], [execution]) |
| `#[cold]` (`CodegenFnAttrFlags::COLD`) | Clean | Uses `#[inline]` / `CostChecker` (`true` for leaf) | `cold` (does **not** add `noinline`) | `-O0`: `call`; `-O2`: leaf `#[cold]` *inlined* cross-crate (`x + 44`) ([execution]) |
| `#[optimize(none)]` (`DoNotOptimize`) | Requires `#![feature(optimize_attribute)]` | N/A in probe (`Never` via `inline_attr`) | `noinline optnone` | Disables inlining & LLVM optimization ([source], [execution]) |
| `#[inline(always)]` + `#[inline(never)]` | `unused_attributes` future-error warning on line 2 (`#[inline(never)]` ignored; first wins) | Resolves as `Always` | `alwaysinline` ([execution]) | Identical to `#[inline(always)]` (unless `-Dwarnings` / `-D unused-attributes` aborts compilation) ([source], [execution]) |
| `#[inline(never)]` + `#[inline(always)]` | `unused_attributes` future-error warning on line 2 (`#[inline(always)]` ignored; first wins) | Resolves as `Never` | `noinline` ([execution]) | Identical to `#[inline(never)]` ([source], [execution]) |
| `#[inline(always)]` + `#[unsafe(no_mangle)]` | Emits `#[inline]` is ignored on externally exported functions (`UNUSED_ATTRIBUTES`) | `false` (`contains_extern_indicator`) | **`alwaysinline` still emitted on `@exp_always`** ([execution]) | Exported symbol retained globally; LLVM function still carries `alwaysinline` (`InlineAttr::Always`) ([source], [execution]) |

Additional verified nuances across MIR and LLVM inlining:

- **Duplicate attribute precedence (`InlineParser`)**: `compiler/rustc_attr_parsing/src/attributes/inline.rs` parses inline attributes using `Single<T>` with `ON_DUPLICATE = WarnButFutureError`, storing the **first** attribute and emitting an `unused_attributes` future-incompatibility warning (hard error under `-Dwarnings`) for subsequent ones ([source], [execution]). Consequently, placing `#[inline(always)]` *before* `#[inline(never)]` produces `alwaysinline` (and additionally triggers `InlineIgnoredForExported` if `#[no_mangle]` is present, because `check_attr.rs` line `612` checks `kind != &InlineAttr::Never`), whereas placing `#[inline(never)]` first resolves to `noinline` and skips the exported-function warning ([source], [execution]).
- **MIR `NormalInliner` thresholds & incremental skip**: `Inline::policy` (`compiler/rustc_mir_transform/src/inline.rs` lines `46-61`) enables `NormalInliner` only at `mir_opt_level >= 2 && (OptLevel::More || OptLevel::Aggressive) && incremental.is_none()` unless overridden by `-Zinline-mir`. Live MIR dumps (`mir_inline_incremental_vs_non_incremental`) confirm that `helper` is inlined into `caller` at `3-2-004.Inline.after.mir` under `-O2`, whereas passing `-C incremental=...` omits the `Inline` pass completely and leaves `_0 = helper(move _1)` in `3-3-000.runtime-optimized.after.mir` ([source], [execution]). Furthermore, `NormalInliner::try_inlining` selects threshold `30` (`forwarder`), `100` (`cross_crate_inlinable`), or `50` (default) with `+25%` if `<= 3` basic blocks, and *still* enforces that MIR cost bound on `#[inline(always)]` to keep compilation fast, delegating large `#[inline(always)]` bodies to LLVM's `AlwaysInlinerPass` ([source]).
- **Cross-crate inlining without LTO (`CostChecker`)**: `rustc` writes upstream MIR into `.rlib` metadata whenever `cross_crate_inlinable` returns `true` (`#[inline]`, `#[inline(always)]`, or leaf unannotated bodies with `calls == 0`, `resumes == 0`, `landing_pads == 0`, and `statements <= threshold`) ([source]). In our live `-O2` cross-crate test (`up` -> `libup.rlib` -> `down`), `rustc` inlined not only `up_inline_always`, `up_inline_hint`, and `up_unannotated_leaf`, but also **`up_cold_only`** (`x + 44`) and **`up_unannotated_large`** (`64`-iteration loop inlined directly into `call_up_unannotated_large` as loop `bb2`, vectorized/8x-unrolled into `%exitcond.not.7 = icmp eq i32 %16, 64` by LLVM) because both are leaf MIR functions with `calls == 0`; adding a single `#[inline(never)]` helper call inside `up_unannotated_with_call` incremented `checker.calls` to `1`, stopping cross-crate inlining cleanly (`tail call @_RNv...up_unannotated_with_call`) alongside `up_inline_never` ([execution]).
- **LLVM cost model (`AlwaysInliner.cpp` and `InlineCost.cpp`)**: `AlwaysInlinerPass` runs even in `PassBuilder::buildO0DefaultPipeline(InsertLifetimeIntrinsics=false)` (`PassBuilderPipelines.cpp` lines `1225`, `2374`) and inlines whenever `CB->hasFnAttr(Attribute::AlwaysInline) && !CB->getAttributes().hasFnAttr(Attribute::NoInline)` (`AlwaysInliner.cpp` lines `108-118`) ([source]), matching our live `-O0` cross-crate observation (`call_up_inline_always` inlines checked addition IR while `up_inline_hint`, `up_cold_only`, and leaves emit `call` instructions) ([execution]). At higher opt levels, `InlineCost.cpp` lines `2018-2068` boost `InlineHint` callees to `HintThreshold` while blocking inline bonuses and capping `Cold` callees at `ColdThreshold` ([source]).

### 6. Anneal Verification Seam (`joshlf/anneal@c131b320e`)

Auditing `joshlf/anneal` at commit `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`trusted/lean/Trusted/MirAst.lean`, `Trusted/MirSemantics.lean`, and `trusted/rustc-capture/src/driver.rs`) establishes the current verification boundary ([source]):

- `TerminatorKind.unreachable` (`MirAst.lean` line `789`) steps cleanly in `Trusted.MirSemantics` (`lines 1551-1552`) to `.fault .undefined` ([source]).
- `StatementKind::Intrinsic` (`NonDivergingIntrinsic::Assume`, emitted by `core::hint::assert_unchecked` and post-`UnreachablePropagation` `unreachable_unchecked`) is collapsed into `StatementKind.unsupported` in `MirAst.lean` (`lines 643, 654-662`), which steps to `.fault .unsupported` in `MirSemantics.evalStatement` (`line 1427`) ([source]).
- `Operand::RuntimeChecks` (`UbChecks` from `ub_checks::assert_unsafe_precondition!`) is explicitly left unmodeled in `MirAst.Operand` (`MirAst.lean` lines `36, 548-560`), documenting the contract that capture must fail closed rather than folding `RuntimeChecks` into a `.constant` boolean (whereas `trusted/rustc-capture/src/driver.rs` lines `75-84` currently only check version/sysroot and `analysis_reached` without extracting MIR operands yet) ([source]).

Consequently, functions whose optimized MIR retains `assume(...)` or symbolic `UbChecks` cannot currently pass Anneal's MIR semantics/extraction seam without lowering or proof-side abstractions ([source]).

### 7. Standalone Lean v4.34.1 Mechanization (`HintAssumeBlackBoxAndInlineAttrsSoundness.lean`)

`support/HintAssumeBlackBoxAndInlineAttrsSoundness.lean` (`2,466` LOC, `0` forbidden tokens, `313` theorems, `485` `noncomputable def`s, `0` `._unsafe_rec`, `0` violations verified via `support/HintAssumeBlackBoxAndInlineAttrsAudit.lean` and `support/check_lean.py`) formalizes a structured MIR/LLVM-IR abstract machine modeling `UbCheckMode` (`abortOnFalse` vs `ubOnFalse`), `@llvm.assume` emission (`emitAssume : Bool`), `black_box` barriers, `InlineParser` first-wins precedence, cross-crate leaf checks, and function attribute maps ([derived], [execution]). Key mechanized theorems (all depending solely on `[propext]` or `[propext, Quot.sound]`, zero `Classical.choice`):

1. **Refinement & Precompiled `core` `-O0` Trap Boundary**:
   - `abortOnFalse_soundly_refines_ubOnFalse`: For every program `prog`, function table `fns`, fuel, store `st`, and value `v`, `evalProg .ubOnFalse true fns fuel st prog = .ok v → evalProg .abortOnFalse true fns fuel st prog = .ok v` ([derived]).
   - `precompiled_core_o0_vs_opt1_boundary`: Constructively proves that with `preserveUbChecks = true`, `checkedUnreachable true` under `emitAssume = false` (`-O0`) produces `.abort` even in `.ubOnFalse`, whereas `checkedAssume (.lit (.bool false))` produces `.ok (.i32 42)`; enabling `emitAssume = true` (`-O1` or `-O2`) yields `.ub` for both under `.ubOnFalse` ([derived]).
2. **Assume-Guided Dead-Branch Pruning & Modular Range Refinement**:
   - `assume_dead_branch_pruning_prog_sound`: Rewriting `assume p; branchOn g dead live` (or `checkedAssume p; branchOn g dead live`) to execute `live` directly when `exprContradicts p g = true` preserves `evalProg` identically across both `UbCheckMode`s ([derived]).
   - `assume_pruning_without_contradiction_unsound` & `o0_assume_suppression_sharpness`: Constructive counterexamples showing unsoundness if contradiction is dropped (`ok (.i32 999)` vs `ok (.i32 2)`) or if `emitAssume = false` suppresses `assume(false)` ([derived]).
   - `norm32_ne_zero_implies_add_one_ne_one` & `prune_unreachable_branch_range_excludes_one`: Pure constructive `Nat` modular proof (modulo $2^{32} = 4294967296$, without arithmetic automation shortcuts) proving that excluding `0` guarantees `norm32 (x + 1) ≠ 1`, matching LLVM's `noundef range(i32 2, 1)` attribute ([derived]).
3. **`black_box` Observational Identity & Constant-Folding Barrier**:
   - `constFoldExpr_sound` & `constFoldBlock_sound`: Constant folding preserves dynamic semantics identically across nested `blackBox` nodes ([derived]).
   - `boxedAddTwoThree_blocked`, `plainAddTwoThree_folds`, & `blackBox_statement_blocks_fold_while_preserving_outcome`: `plainAddTwoThree` folds to `.lit (.i32 5)` while `boxedAddTwoThree` remains completely unfolded, yet both evaluate to `.ok (.i32 5)` across both `runtime` and `constEval` modes ([derived]).
   - `blackBox_observational_identity`: Stripping all `.blackBox` / `.blackBoxAssign` barriers across `prog` and `fns` leaves `evalProg` unchanged ([derived]).
4. **Attribute Precedence & Observational Equivalence Invariance**:
   - `duplicate_always_then_never_keeps_always`, `duplicate_never_then_always_keeps_never`, `exported_always_then_never_emits_both_diags`, `exported_never_then_always_skips_export_warning`: Formalize exact `InlineParser` first-wins precedence and `check_inline` export diagnostics ([derived]).
   - `fnAttrs_observational_equivalence_invariance`, `inlineCallOnce_sound`, & `end_to_end_opt_and_refinement`: Prove that altering `FnAttrs` (`#[inline]`, `#[inline(always)]`, `#[inline(never)]`, `#[cold]`, `#[optimize(none)]`) and hygienically inlining leaf functions preserves observable outcomes across the composed optimization pipeline ([derived]).

## Boundaries

The scope and negative space of this report are bounded as follows:

- **Formal-model disconnection (`unsupported` / `derived` scope)**: `support/HintAssumeBlackBoxAndInlineAttrsSoundness.lean` formalizes a self-contained operational model of structured MIR/LLVM-IR instructions, attribute precedence, and pass transformations; it is **not** extracted from or linked by refinement proof to `rustc`'s Rust compiler implementation or `joshlf/anneal`'s `Trusted.MirAst` / `Trusted.MirSemantics` definitions. Its soundness guarantees establish internal consistency of the documented compiler rules rather than mechanical bug-freedom of `rustc` or LLVM C++ code ([derived]).
- **LTO / ThinLTO and cross-architecture ABIs (`not examined`)**: All empirical `rustc` builds used `-C opt-level=0/1/2` without `-C lto` on `x86_64-unknown-linux-gnu`; LTO/ThinLTO cross-crate bitcode inlining policies and non-x86 architectures (such as `AmdGpu`'s `noinline` exception seen in `attributes.rs` line `83`) were not executed ([source]).
- **Exact `rustc 1.102.0-nightly` (`3ef0c22cd`) runtime execution on this host (`not examined`)**: Live compiler runs, MIR dumps, LLVM IR dumps, and Miri diagnostics were executed on `rustc 1.98.0-nightly` (`14210df0e`, LLVM `22.1.6`) installed locally; `3ef0c22cd` (`1.102.0-nightly`, LLVM `23.1.5`) was verified directly against upstream GitHub source files (`hint.rs`, `lower_intrinsics.rs`, `cross_crate_inline.rs`, `inline.rs`, `intrinsic.rs`, `attributes.rs`) and matches the structural compiler behavior except for minor LLVM 22 vs LLVM 23 IR attribute syntax (`captures(address, read_provenance)` on LLVM 23 vs absent in `14210df0e` IR; `< (23, 0, 0)` target-feature version gate in `attributes.rs`) ([source], [execution]).
- **Custom sysroot without `#![rustc_preserve_ub_checks]` (`unknown` / `not examined`)**: All live binaries linked the pre-compiled nightly `core` sysroot distributed with toolchain `14210df0e`; custom `-Zbuild-std` builds omitting `#![rustc_preserve_ub_checks]` were not built locally, though `instsimplify.rs` indicates `SimplifyUbCheck` would fold `UbChecks` during `core` compilation if that attribute were absent ([source]).
- **Unsafe target-feature + `#[inline(always)]` downgrade path (`known not to apply` on simple free functions in `14210df0e`)**: Although comparison revision `3ef0c22cd`'s `attributes.rs` adds a fallback downgrading `InlineAttr::Always` with target features on LLVM `< 23` to `InlineHint`, testing `#[inline(always)] #[target_feature(enable = "avx2")]` on a free function in `rustc 1.98.0-nightly` (`14210df0e`) is rejected earlier by a hard frontend error (`error: cannot use #[inline(always)] with #[target_feature]`) ([source], [execution]).
- **Anneal MIR capture & semantics of intrinsics (`unsupported`)**: In `joshlf/anneal@c131b320e`, `StatementKind::Intrinsic` (`Assume`) is collapsed into `.unsupported` (`MirAst.lean:643, 654-662`, stepping to `.fault .unsupported` in `MirSemantics.lean:1427`), `Operand::RuntimeChecks` (`UbChecks`) is intentionally unmodeled in `MirAst.Operand` (`MirAst.lean:36, 548-560`) so capture must fail closed, and `trusted/rustc-capture/src/driver.rs` (`lines 75-84`) does not yet implement MIR extraction (`// No compiler data or verification obligation is extracted here.`); thus functions retaining `assume(...)` or symbolic `UbChecks` cannot currently pass Anneal's MIR pipeline cleanly ([source]).
- **UB runtime behavior generality (`unknown` outside tested shapes)**: Under `-O1`/`-O2 -C debug-assertions=off`, triggering `unreachable_unchecked()` or `assert_unchecked(false)` is UB ([normative]); observed `REACHED` / `ASSERT_OK` outputs in `main` reflect branch fallthrough in that specific caller CFG, whereas isolated diverging `lower_unreachable() -> !` emits bare `unreachable` (typically hardware trap `ud2`), and behavior across other caller structures is `unknown` in general ([execution]).

## Evidence

### 1. Primary-Source File and Line Anchors

| Component | Repository & Pinned Commit | Exact Path & Lines / Symbols | Verified Mechanism |
| --- | --- | --- | --- |
| `unreachable_unchecked` | `rust-lang/rust@14210df0e` (`3ef0c22cd`) | `library/core/src/hint.rs:99-112` | `#[inline] #[track_caller]`, `assert_unsafe_precondition!(check_language_ub, ..., () => false)` + `intrinsics::unreachable()` ([source]). |
| `assert_unchecked` | `rust-lang/rust@14210df0e` (`3ef0c22cd`) | `library/core/src/hint.rs:197-212` | `#[inline(always)] #[track_caller]`, `assert_unsafe_precondition!(check_language_ub, ..., (cond: bool = cond) => cond)` + `intrinsics::assume(cond)` ([source]). |
| `black_box` | `rust-lang/rust@14210df0e` (`3ef0c22cd`) | `library/core/src/hint.rs:487-492` | `#[inline] #[rustc_const_stable]`, calls `intrinsics::black_box(dummy)` ([source]). |
| UB check gate & `core` attr | `rust-lang/rust@14210df0e` | `library/core/src/ub_checks.rs:53-108`, `lib.rs:77` | `precondition_check` (`#[rustc_no_mir_inline]`); `check_language_ub` = `const_eval_select!` (`false` in `const`, `!cfg!(miri)` at runtime) `&& intrinsics::ub_checks()`; `lib.rs:77` `#![rustc_preserve_ub_checks]` ([source]). |
| MIR opt pass ordering | `rust-lang/rust@14210df0e` | `compiler/rustc_mir_transform/src/lib.rs:705-755`, `instsimplify.rs:33-36` | `ForceInline` (`707`) -> `Inline` (`709`) -> `UnreachablePropagation` (`721`) -> `InstSimplify` (`727`, skipping `SimplifyUbCheck` when `#![rustc_preserve_ub_checks]`) -> `o1(SimplifyConstCondition::AfterInstSimplify)` (`736`) ([source]). |
| MIR `LowerIntrinsics` | `rust-lang/rust@14210df0e` (`3ef0c22cd`) | `compiler/rustc_mir_transform/src/lower_intrinsics.rs:23-25,80-92` (`22-24,90-102`) | `sym::unreachable` -> `TerminatorKind::Unreachable`; `sym::assume` -> `StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(arg.node))` + `Goto`; `sym::black_box` untouched ([source]). |
| MIR `Inline` & `mir_opt_level` | `rust-lang/rust@14210df0e` (`3ef0c22cd`) | `compiler/rustc_mir_transform/src/inline.rs:46-59,458` (`46-59,380-448`), `rustc_session/src/session.rs:617-622`, `rustc_codegen_ssa/src/mir/operand.rs:1057` | `Inline` enabled only for `mir_opt_level >= 2 && (More || Aggressive) && incremental.is_none()`; thresholds `30`/`100`/`50` (`+25%` if `<=3` blocks), applied even to `#[inline(always)]`; `UbChecks` lowered at codegen (`operand.rs:1057`) ([source]). |
| Cross-crate MIR export | `rust-lang/rust@14210df0e` (`3ef0c22cd`) | `compiler/rustc_mir_transform/src/cross_crate_inline.rs:18-105,114-187` (`18-117,128-200`) | Exported -> `false`; `Never` -> `false`; `Hint|Always|Force` -> `true`; `CostChecker` exports leaf fns with `calls == 0 && resumes == 0 && landing_pads == 0 && statements <= threshold` ([source]). |
| LLVM intrinsic codegen | `rust-lang/rust@14210df0e` (`3ef0c22cd`) | `compiler/rustc_codegen_llvm/src/intrinsic.rs:611-651,1034-1038` (`88-120,991-995`) | `black_box` emits volatile `inline_asm_call` `""` with `"~{memory}"` or `"r,~{memory}"`; `assume` emits `llvm.assume` iff `optimize != OptLevel::No` ([source]). |
| LLVM attribute mapping | `rust-lang/rust@14210df0e` (`3ef0c22cd`) | `compiler/rustc_codegen_llvm/src/attributes.rs:45-77,458-460` (`51-91,555-557`) | `Hint` -> `InlineHint`, `Always|Force` -> `AlwaysInline` (`3ef0c22cd:73-78` adds `InlineHint` downgrade if target features & LLVM `< 23`), `DoNotOptimize`/`Never` -> `NoInline`, `COLD` -> `AttributeKind::Cold` ([source]). |
| Attribute conflict & export lint | `rust-lang/rust@14210df0e` | `rustc_attr_parsing/src/attributes/mod.rs:123-165`, `inline.rs:10-61`, `rustc_passes/src/check_attr.rs:604-628` | `InlineParser` keeps first attribute (`WarnButFutureError`); `check_inline` emits `UNUSED_ATTRIBUTES` when exported unless `kind == Never` ([source]). |
| LLVM upstream passes | `llvm/llvm-project@2fcb2d340` | `Intrinsics.td:1097-1101`, `PassBuilderPipelines.cpp:1225,2374`, `AlwaysInliner.cpp:108-118`, `InlineCost.cpp:2018-2068` | `int_assume` memory/noundef attrs; `AlwaysInlinerPass` active at `-O0`; `InlineHint` uses `HintThreshold`; `Cold` uses `ColdThreshold` ([source]). |
| Anneal MIR seam | `joshlf/anneal@c131b320e` | `trusted/lean/Trusted/MirAst.lean:36,548-560,654-662,789`, `MirSemantics.lean:1427,1551-1552,1568-1569`, `driver.rs:75-84` | `TerminatorKind.unreachable` -> `.fault .undefined`; `Intrinsic` (`unsupported`) -> `.fault .unsupported`; `Operand::RuntimeChecks` unmodeled; `driver.rs` currently checks version/analysis without extracting MIR ([source]). |

### 2. Live Execution & MIR / LLVM IR Evidence (`support/probe_hint_and_inline_attrs.py` -> `support/probe_results.json`)

Executed locally on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (LLVM `22.1.6`) and `miri 0.1.0 (14210df0e2 2026-05-31)` inside `support/probe_hint_and_inline_attrs.py` (`79,933` byte output JSON):

**Selected verbatim MIR excerpts (`opt2_debug_off_ub_no` vs `opt0_debug_off_ub_no` & `incremental_opt2`):**

```text
// probe.lower_unreachable.3-2-004.Inline.after.mir (-Copt-level=2 -Cdebug-assertions=off -Zub-checks=no)
    bb0: {
        StorageLive(_1);
        assume(UbChecks);
        _1 = unreachable_unchecked::precondition_check() -> [return: bb1, unwind unreachable];
    }
    bb1: {
        unreachable;
    }

// probe.lower_unreachable.3-2-011.SimplifyConstCondition-after-inst-simplify.after.mir (-O2)
    bb0: {
        unreachable;
    }

// incr.caller.3-2-004.Inline.after.mir (-Copt-level=2, non-incremental)
    bb0: {
        StorageLive(_2);
        _2 = copy _1;
        _0 = Add(copy _2, const 7_i32);
        StorageDead(_2);
        return;
    }

// incr.caller.3-3-000.runtime-optimized.after.mir (-Copt-level=2 -Cincremental=<dir>)
    bb0: {
        _0 = helper(move _1) -> [return: bb1, unwind continue];
    }
```

**Selected verbatim LLVM IR excerpts (`1.98.0-nightly`, `14210df0e` / LLVM `22.1.6`):**

```llvm
; -O0 -Cdebug-assertions=off -Zub-checks=no: @llvm.assume suppressed; unreachable_unchecked still calls pre-compiled core stub
define void @lower_assume(i1 zeroext %cond) unnamed_addr #3 {
start:
  ret void
}
define void @lower_unreachable() unnamed_addr #4 {
start:
; call core::hint::unreachable_unchecked
  call void @_RNvNtCs8b4M6GsfcPr_4core4hint21unreachable_uncheckedCsh8INqWOoJ6U_5probe(ptr align 8 @alloc_ffd293008ad77b807859cc28b56a0b87) #9
  unreachable
}

; -O2 -Cdebug-assertions=off -Zub-checks=no: CorrelatedValuePropagationPass derives noundef range(i32 2, 1)
define noundef range(i32 2, 1) i32 @prune_unreachable_branch(i32 noundef %x) unnamed_addr #1 {
start:
  %_2 = icmp ne i32 %x, 0
  tail call void @llvm.assume(i1 %_2)
  %_0 = add i32 %x, 1
  ret i32 %_0
}
declare void @llvm.assume(i1 noundef) #4

; black_box barriers vs plain folding (-O2)
define noundef i32 @black_box_no_fold() unnamed_addr #4 {
start:
  %_2 = alloca [4 x i8], align 4
  %_1 = alloca [4 x i8], align 4
  call void @llvm.lifetime.start.p0(ptr nonnull %_1)
  store i32 2, ptr %_1, align 4
  call void asm sideeffect "", "r,~{memory}"(ptr nonnull %_1) #11, !srcloc !4
  call void @llvm.lifetime.start.p0(ptr nonnull %_2)
  store i32 3, ptr %_2, align 4
  call void asm sideeffect "", "r,~{memory}"(ptr nonnull %_2) #11, !srcloc !4
  %0 = load i32, ptr %_1, align 4, !noundef !5
  %1 = load i32, ptr %_2, align 4, !noundef !5
  %_0 = add i32 %1, %0
  call void @llvm.lifetime.end.p0(ptr nonnull %_2)
  call void @llvm.lifetime.end.p0(ptr nonnull %_1)
  ret i32 %_0
}
define void @black_box_zst() unnamed_addr #4 {
start:
  tail call void asm sideeffect "", "~{memory}"() #11, !srcloc !4
  ret void
}
define noundef i32 @plain_fold() unnamed_addr #9 {
start:
  ret i32 5
}
```

**Observed LLVM attributes & cross-crate IR (`-O2` and `-O0` without LTO):**

- `fn_attr_cold_never`: `cold mustprogress nofree noinline norecurse nosync nounwind nonlazybind willreturn memory(none) uwtable` (`attributes #6`)
- `fn_attr_cold_internal`: `cold mustprogress nofree norecurse nosync nounwind nonlazybind willreturn memory(none) uwtable` without `noinline` (`attributes #1`); cross-crate `call_up_cold_only` at `-O2` inlined cleanly to `%_0.i = add i32 %x, 44; ret i32 %_0.i`
- `fn_attr_hint_internal`: `inlinehint ...` (`attributes #2`)
- `fn_attr_always_internal`: `alwaysinline ...` (`attributes #3`)
- `fn_attr_opt_none`: `noinline nonlazybind optnone uwtable` (`attributes #8`)
- `fn_attr_hint_avx2`: `inlinehint ... "target-features"="+avx,+avx2,..."` (`attributes #0`)
- Cross-crate `up_unannotated_leaf` & `up_unannotated_large`: both inlined at `-O2` (`calls == 0`, with `up_unannotated_large` keeping an 8x-unrolled inlined loop `%exitcond.not.7 = icmp eq i32 %16, 64` inside `call_up_unannotated_large`); `up_unannotated_with_call` stayed `tail call noundef i32 @_RNvCs8UDIQm470yX_2up24up_unannotated_with_call(i32 noundef %x)` (`calls == 1`). At `-O0`, **only** `call_up_inline_always` inlined across crates (`llvm.sadd.with.overflow.i32`) via `AlwaysInlinerPass`.

### 3. Lean v4.34.1 Kernel & MetaM Purity Receipt (`support/lean_check_receipt.json`)

Running `python3 support/check_lean.py` wrapped under `anneal-lean-run --mode file -- lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` on `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)` produced `passed: true` (`wrapper_used: true`) with:

- `loc`: `2466` lines (`source_sha256`: `6152e4e34aab0308189110253f85484e9d3ff7a84977bd72f11415ddd5bcfc58`)
- `forbidden_token_counts`: `0` for all `15` forbidden tokens (`sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `partial`, `implemented_by`, `extern`, `omega`, `bv_decide`, `native_decide`, `Classical.choice`, `_unsafe_rec`, `noncomputable section`, `deriving`)
- `plain_non_noncomputable_defs`: `[]` (`0` plain `def`s)
- `compile`: `exit_code: 0`, `errors: 0`, `warnings: 0`, `wall_seconds: 9.497`, `peak_rss_kb: 669192`, `olean_bytes: 5175408`
- `audit` (`HintAssumeBlackBoxAndInlineAttrsAudit.lean`): `exit_code: 0`, `theorem_count: 313`, `def_count: 485`, `violations: 0`, `violation_lines: []`, `wall_seconds: 3.404`, `peak_rss_kb: 1611164`
- `print_axioms`: All `17` printed top-level theorems in `VerifiedRustcHintInline.*` depend exclusively on Lean core axioms (zero `sorryAx`, zero `Classical.choice`, zero `Lean.ofReduceBool`):
  - `[propext]` (`12` theorems): `constFoldExpr_sound`, `plainAddTwoThree_folds`, `boxedAddTwoThree_blocked`, `plain_and_boxed_same_runtime_value`, `exported_always_then_never_emits_both_diags`, `exported_never_then_always_skips_export_warning`, `abortOnFalse_soundly_refines_ubOnFalse`, `precompiled_core_o0_vs_opt1_boundary`, `assume_pruning_without_contradiction_unsound`, `norm32_ne_zero_implies_add_one_ne_one`, `prune_unreachable_branch_range_excludes_one`, `blackBox_statement_blocks_fold_while_preserving_outcome`
  - `[propext, Quot.sound]` (`5` theorems): `assume_dead_branch_pruning_prog_sound`, `blackBox_observational_identity`, `fnAttrs_observational_equivalence_invariance`, `inlineCallOnce_sound`, `end_to_end_opt_and_refinement`

## Revalidation

Revalidate every primary source anchor, live compiler probe, Lean proof artifact, and corpus schema invariant from the package root and corpus root with:

```bash
# 1. Verify pinned upstream commits resolve identically on GitHub
gh api repos/rust-lang/rust/commits/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65 --jq .sha
gh api repos/rust-lang/rust/commits/3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1 --jq .sha
gh api repos/llvm/llvm-project/commits/2fcb2d3403190ac9353eddd23a92716e937e0739 --jq .sha
gh api repos/joshlf/anneal/commits/c131b320eeeb26ef692e5afd5ec8db49ee518613 --jq .sha
gh api repos/leanprover/lean4/commits/5045d0056413266e57c625dcd7c365b10e377c52 --jq .sha

# 2. Re-run empirical rustc, MIR, LLVM IR, and Miri probe harness (isolated inside tempfile.TemporaryDirectory)
python3 support/probe_hint_and_inline_attrs.py

# 3. Re-run kernel-checked Lean v4.34.1 compilation & MetaM purity audit
python3 support/check_lean.py

# 4. Re-build corpus catalog and run corpus validators from the corpus root
python3 tools/reference.py catalog
python3 tools/reference.py check
python3 -m unittest discover -s tests -v
```
