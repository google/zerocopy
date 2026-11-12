<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# `Const::Unevaluated` Resolution, `ConstValue` / `GlobalAlloc` Layout-Guided Decoding, and `promoted[N]` Constant Promotion in `Runtime(PostCleanup)` MIR

## Summary

When a verification tool intercepts `Runtime(PostCleanup)` MIR (`tcx.mir_drops_elaborated_and_const_checked(def_id)`) inside `rustc_driver::Callbacks::after_analysis`, constant operands in `body.basic_blocks` and `body.required_consts()` appear in three distinct representations that require coordinated CTFE evaluation and layout-guided reconstruction:

1. **`body.required_consts()` vs. `body.basic_blocks` Divergence and Post-Monomorphization Errors (`ErrorHandled`)**:
   - `RequiredConstsVisitor::compute_required_consts` (`compiler/rustc_mir_transform/src/required_consts.rs:9-28`) runs in `mir_promoted` *before* `PromoteTemps` (`compiler/rustc_mir_transform/src/lib.rs:462` in `1.98.0-nightly`, `:473` in `1.101.0-nightly`), walking `traversal::reverse_postorder(&body)` and recording every `ConstOperand` where `is_required_const()` is `true` (`Const::Unevaluated` and non-`Value` `Const::Ty`).
   - Subsequent passes mutate `body.basic_blocks` without re-running `RequiredConstsVisitor`: `PromoteTemps` extracts promoted `Const::Unevaluated` operands out of `body.basic_blocks` into `promoted[p]` (leaving the inner `Const::Unevaluated` on the outer `Body` **only** in `body.required_consts()`, while inserting `Const::Unevaluated(..., promoted: Some(p))` into `body.basic_blocks` without adding it to `body.required_consts()` unless a `TerminatorKind::Call` was promoted), and `InstSimplify-before-inline` folds array-repeat length `Const::Unevaluated` operands into `Const::Val` in `body.basic_blocks` while leaving the original entry in `body.required_consts()`.
   - Under `--emit=metadata` or `-Zno-codegen`, `rustc_interface::passes::run_required_analyses` skips `mir_drops_elaborated_and_const_checked` entirely (`should_codegen() == false`), entering `after_analysis` with zero errors even when a function contains a reachable `const { 1 / 0 }`. Even when a driver queries `tcx.mir_drops_elaborated_and_const_checked(def_id)`, `KnownPanicsLint` (`compiler/rustc_mir_transform/src/known_panics_lint.rs:254, 668-688, 759-770`) constant-propagates `SwitchInt` discriminants (skipping `if false { const { panic!() } }` and `match false { true => const { 1 / 0 }, .. }`) and skips any constant satisfying `c.has_param()` (including an unconditionally failing `Fail::<T>::UNCOND_FAIL = 1 / 0`). Normal `rustc` catches those failures only during codegen monomorphization (`collect_items_of_instance` in `compiler/rustc_monomorphize/src/collector.rs:1349-1353`). A sound verifier must therefore evaluate **both** every entry in `body.required_consts()` and every `Const::Unevaluated` in `body.basic_blocks`, rejecting on `Err(ErrorHandled::Reported(..))`.

2. **Anatomy of `ConstValue` (`ZeroSized`, `Scalar`, `Slice`, `Indirect`) and Layout-Guided `GlobalAlloc` Reconstruction**:
   - `ConstValue` (`compiler/rustc_middle/src/mir/consts.rs:33-71`) is fixed at 24 bytes and intentionally omits a general `ScalarPair` variant. In `op_to_const` (`compiler/rustc_const_eval/src/const_eval/eval_queries.rs:213-293` in `1.98.0-nightly`, `:258-338` in `1.101.0-nightly`), `force_as_immediate` is `true` **only** when `matches!(op.layout.backend_repr, BackendRepr::Scalar(abi::Scalar::Initialized { .. }))`.
   - Consequently, `tcx.const_eval_resolve` lowers every non-ZST composite constant with `BackendRepr::ScalarPair` or `BackendRepr::Memory`—including 2-field structs (`U64Range { min, max }`), padded tuples (`(u8, u32)`), multi-field structs (`U64ScalarValueData::UNINITIALIZED`), arrays (`[u32; 4]`), `Direct`-tagged payload enums (`Option<u64>`, `Result<u32, u8>`), and **even non-trivial `&'static str` and `&'static [u8]` constants** (`!tcx.is_trivial_const(def_id)`)—to **`ConstValue::Indirect { alloc_id, offset }`** backed by `GlobalAlloc::Memory(ConstAllocation)`.
   - `tcx.const_eval_resolve_for_typeck` (`ValTree`) cannot replace `ConstValue` + `ConstAllocation` decoding: it panics on `promoted: Some(p)` (`uv.shrink()` asserts `self.promoted == None`), returns `Ok(Err(NonSupportedType(ty)))` on `fn` pointers and raw pointers with provenance, erases reference provenance identity, and in `1.101.0-nightly` stops before allocation creation (`STOP_AT_ALLOC = true`) for reference types when `adt_const_params` is not enabled.
   - A layout-guided algebraic decoder driven by `tcx.layout_of(typing_env.as_query_input(ty))` and `Allocation::read_scalar` deterministically reconstructs pure typed Lean constants (`PureConst`) without exposing raw endianness, uninitialized padding gaps (`InitMask`), or `AllocId` numbering to proofs.

3. **Constant Promotion (`PromoteTemps` and `tcx.promoted_mir(def_id)`)**:
   - `rustc` has no `DefKind::Promoted`; promoted fragments live in `tcx.promoted_mir(def_id): &IndexVec<Promoted, Body<'tcx>>`, where each `promoted[p]` body is lowered to `MirPhase::Runtime(RuntimePhase::PostCleanup)` (`compiler/rustc_mir_transform/src/lib.rs:820-837` in `1.98.0-nightly`, `:836-851` in `1.101.0-nightly`) and referenced in the parent body via `Const::Unevaluated(UnevaluatedConst { def, args, promoted: Some(p) }, ref_ty)`.
   - Every monomorphic promoted constant (`&0u32`, `&EbpfInstruction(7)`, `&U64Range { min: 0, max: 1 }`, `&U64ScalarValueData::UNINITIALIZED`, `&[1, 2, 3]`, `&mut []`, `&((10u32 / 2u32) + 3u32)`, and the RHS `&0u32` of `assert_eq!(a, 0u32)`), as well as any promoted constant in a generic function whose body does not depend on generic parameters (`promo_generic_independent<T>`), evaluates eagerly via `tcx.const_eval_resolve(typing_env, uv, span)` to `Ok(ConstValue::Scalar(Scalar::Ptr(..)))`. Only promoted bodies whose computation depends on a generic parameter (`&[0u8; N]` or `&core::mem::size_of::<T>()`, promoted because `size_of` is `#[rustc_promotable]`) return `Err(ErrorHandled::TooGeneric(..))` polymorphically and require either monomorphic instantiation or symbolic translation of `tcx.promoted_mir(def_id)[p]`.

## Applicability

The findings, compiler source citations, empirical `rustc_driver` probes, and Lean 4 proofs in this report are pinned to:

| Subject | Repository / Path | Pinned Revision / Version | Role in This Report |
| :--- | :--- | :--- | :--- |
| `rustc` (`R1`) | `rust-lang/rust` | `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (`1.98.0-nightly`, 2026-05-30) | Primary baseline compiler for Anneal and `rustc_driver` probe `probe_1_98` |
| `rustc` (`R2`) | `rust-lang/rust` | `19833af7224424e8b53e288097d56b6af43d5bcf` (`1.101.0-nightly`, 2026-10-20) | Newer nightly compiler for multi-version stability check and `probe_1_101` |
| The Rust Reference | `rust-lang/reference` | `82da570bafd9efed421bdbae0f8603ede8dd308b` | Normative specification for `const` blocks, constant evaluation, and temporary lifetime extension |
| Lean 4 Kernel | `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Kernel checking `support/MirConstAllocationDecoder.lean` (`0` `sorry`, `0` warnings) |
| Anneal | `joshlf/anneal` | `f2bc17e9be87b777d63c785b31f3370ff058d69b` | Target `Runtime(PostCleanup)` MIR capture pipeline (`trusted/rustc-capture/`) |
| Fuchsia Starnix `ebpf_core` | `fuchsia/fuchsia` (`src/starnix/lib/ebpf/core/src`) | `823a15538f191b9dbd9ebafaa6ba23220b87d2e1` | Source of representative composite constants (`EbpfInstruction`, `U64Range`, `U64ScalarValueData::UNINITIALIZED`) |

This report complements [`rustc-const-evaluation-monomorphization-and-pme-capture`](../rustc-const-evaluation-monomorphization-and-pme-capture/REPORT.md), [`rustc-postcleanup-mir-const-placement-layout-folding-and-ub-checks`](../rustc-postcleanup-mir-const-placement-layout-folding-and-ub-checks/REPORT.md), and [`anneal-scalar-mir-differential-execution-and-capture-alignment`](../anneal-scalar-mir-differential-execution-and-capture-alignment/REPORT.md).

## Findings

### 1. `body.required_consts()`, `Const::Unevaluated`, `const_eval_*` Queries, and `ErrorHandled`

#### 1.1 How `RequiredConstsVisitor` Populates `body.required_consts` and How Subsequent Passes Cause Divergence

In `compiler/rustc_middle/src/mir/mod.rs:1084-1091` (`R1`) / `:1088-1095` (`R2`), `mir::Body<'tcx>` stores `pub required_consts: Option<Vec<ConstOperand<'tcx>>>`. It is populated during `mir_promoted` (`compiler/rustc_mir_transform/src/lib.rs:460-477` in `R1`, `:471-488` in `R2`) **before** `PromoteTemps` runs:

```rust
// Collect `required_consts` *before* promotion, so if there are any consts being promoted
// we still add them to the list in the outer MIR body.
RequiredConstsVisitor::compute_required_consts(&mut body);

// What we need to run borrowck etc.
let promote_pass = promote_consts::PromoteTemps::default();
pm::run_passes(
    tcx,
    &mut body,
    &[&promote_pass, &simplify::SimplifyCfg::PromoteConsts, &coverage::InstrumentCoverage],
    Some(MirPhase::Analysis(AnalysisPhase::Initial)),
);
```

`RequiredConstsVisitor::compute_required_consts` (`compiler/rustc_mir_transform/src/required_consts.rs:9-28`, identical in `R1` and `R2`) walks `traversal::reverse_postorder(&body)` and pushes every `ConstOperand` whose `const_.is_required_const()` (`compiler/rustc_middle/src/mir/consts.rs:271-280` in `R1`, `:272-281` in `R2`) is `true`:
- `Const::Unevaluated(..) => true`
- `Const::Ty(_ty, c) => !matches!(c.kind(), ty::ConstKind::Value(_))`
- `Const::Val(..) => false`

When `Analysis(PostCleanup)` transitions to `Runtime(Initial)`, `PostAnalysisNormalize` (`compiler/rustc_mir_transform/src/post_analysis_normalize.rs:46-55`) normalizes both `body.basic_blocks` and `body.required_consts` under `TypingEnv::post_analysis(tcx, body.source.def_id())`, but never recomputes the vector from `body.basic_blocks`. Consequently, in `Runtime(PostCleanup)` MIR (`tcx.mir_drops_elaborated_and_const_checked(def_id)`), `body.required_consts()` and the `Const::Unevaluated` operands in `body.basic_blocks` diverge in two directions:

1. **Constants present in `body.required_consts()` but absent from `body.basic_blocks`**:
   - **Promoted inner constants**: In `part1_promoted_if_false_div_zero` (`if false { let _r: &'static usize = &const { 1 / 0 }; }`), `RequiredConstsVisitor` records `Const::Unevaluated(def=part1_promoted_if_false_div_zero::{constant#0}, promoted=None)` in `body.required_consts()`. Immediately afterward, `PromoteTemps` extracts `{constant#0}` out of the outer `body.basic_blocks` into `promoted[0]` (`promote_consts.rs:1002` in `R1`, `:1015` in `R2`), replacing the outer basic block statement with `Const::Unevaluated(def=part1_promoted_if_false_div_zero, promoted=Some(promoted[0]), ty=&usize)`. Thus `{constant#0}` is **completely absent from `body.basic_blocks`** of the outer function and survives on the outer `Body` solely in `body.required_consts()`.
   - **InstSimplified repeat counts**: In `[0u8; ANON_LEN]`, `RequiredConstsVisitor` records `ANON_LEN` (`DefKind::AnonConst`) in `body.required_consts()`. Later, `InstSimplify-before-inline` folds the repeat count in `body.basic_blocks`, leaving `ANON_LEN` in `body.required_consts()` even though no basic block still mentions it.
2. **Constants present in `body.basic_blocks` but absent from `body.required_consts()`**:
   - When `PromoteTemps` promotes an rvalue borrow (`&0u32`, `&EbpfInstruction(7)`, `&U64Range { min: 0, max: 1 }`), `Promoter::promote_candidate` (`compiler/rustc_mir_transform/src/promote_consts.rs:747-750, 858, 978-980` in `R1`; `:760-763, 871, 991-993` in `R2`) sets `self.add_to_required = true` **if and only if** the promoted fragment contains a `TerminatorKind::Call`. Pure rvalue promotions have `add_to_required == false`, so `Const::Unevaluated(..., promoted: Some(p))` appears in `body.basic_blocks` and is **not** in `body.required_consts()`.

#### 1.2 Why `--emit=metadata`, `-Zno-codegen`, and `KnownPanicsLint` Miss Failing Constants

1. **HIR Typecheck (`rustc_hir_analysis::check_crate`)**:
   - `compiler/rustc_hir_analysis/src/lib.rs:170-186` (`R1`) / `:167-184` (`R2`) and `compiler/rustc_hir_analysis/src/check/check.rs:581-614` (`R1`) / `:575-608` (`R2`) evaluate only `DefKind::Static` items, free `DefKind::Const` items with zero generic parameters (`tcx.generics_of(def_id).is_empty()`), enum discriminants, and struct field defaults.
   - HIR analysis **never** evaluates `const { ... }` inline constant blocks (`DefKind::InlineConst` in `R1`; merged into `DefKind::AnonConst` with `AnonConstKind::NonTypeSystemInline` in `R2`, `compiler/rustc_hir/src/def.rs:137-146, 567-588`) or `DefKind::AssocConst` items (`Fail::<u64>::SIZE_CHECK`).
2. **Skipped Runtime MIR Lowering Under `--emit=metadata` / `-Zno-codegen`**:
   - In `compiler/rustc_interface/src/passes.rs:1170-1180` (`R1`) / `:1187-1197` (`R2`), `run_required_analyses` guards `tcx.ensure_ok().mir_drops_elaborated_and_const_checked(def_id)` behind `if tcx.sess.opts.output_types.should_codegen()`.
   - When a `rustc_driver` tool runs with `--emit=metadata` (`cargo check` mode) or `-Zno-codegen`, `should_codegen()` is `false`, so `Callbacks::after_analysis` is invoked with `tcx.dcx().has_errors() == None` (`err_count == 0`) even when the crate contains reachable `const { 1 / 0 }` or `Fail::<u64>::SIZE_CHECK`!
3. **Why Querying `tcx.mir_drops_elaborated_and_const_checked(def_id)` Still Misses Failing `required_consts`**:
   - Querying `mir_drops_elaborated_and_const_checked` runs `KnownPanicsLint` (`compiler/rustc_mir_transform/src/known_panics_lint.rs:668-688, 759-770`), which overrides `Visitor::visit_body` to walk a worklist of basic blocks while **constant-propagating `SwitchInt` discriminants** (`let target = targets.target_for_value(constant); self.worklist.push(target); return;`).
   - Thus `KnownPanicsLint` never visits the dead branch of `if false { const { panic!() } }`, `if false { const { 1 / 0 } }`, `match false { true => const { 1 / 0 }, false => 42 }`, or `if false { let _r = &const { 1 / 0 }; }`, even though `bb1` is present in `Runtime(PostCleanup)` `body.basic_blocks` and its `Const::Unevaluated` is in `body.required_consts()`!
   - Furthermore, `KnownPanicsLint::eval_constant` (`known_panics_lint.rs:254`) immediately returns `None` when `c.has_param()` is `true`, skipping `Fail::<T>::UNCOND_FAIL = 1 / 0` in `part1_generic_mention_uncond_fail<T>()`.
   - Normal `rustc` only catches these errors when codegen monomorphization runs `collect_items_of_instance` (`compiler/rustc_monomorphize/src/collector.rs:1349-1353, 705-723` in `R1`; `:1374-1380, 712-730` in `R2`), which unconditionally evaluates every entry in `body.required_consts()`.
   - By contrast, in `part1_post_return_div_zero` (`return; let _ = const { 1 / 0 };`), the block after `return` has zero CFG predecessors in `mir_built`, so `traversal::reverse_postorder(&body)` never visits it when `RequiredConstsVisitor` runs and `SimplifyCfg::Initial` deletes the block. It is absent from both `body.required_consts()` and `body.basic_blocks`, and `rustc` accepts it even during full codegen (RFC 2920).

#### 1.3 `const_eval_*` Query Matrix and Multi-Version Diffs (`R1` vs. `R2`)

| Query / Method | Source Location (`R1` / `R2`) | Input Key | Return Type | Semantics & `R1 -> R2` Differences |
| :--- | :--- | :--- | :--- | :--- |
| `mir::Const::eval` | `compiler/rustc_middle/src/mir/consts.rs:306-332` (`R1`), `:307-333` (`R2`) | `(self, tcx: TyCtxt<'tcx>, typing_env: TypingEnv<'tcx>, span: Span)` | `Result<ConstValue, ErrorHandled>` | Evaluates `Const::Ty` via normalization + `valtree_to_const_val`, `Const::Unevaluated(uv, _)` via `tcx.const_eval_resolve(typing_env, uv, span)`, and returns `Ok(val)` for `Const::Val(val, _)`. |
| `tcx.const_eval_resolve` | `compiler/rustc_middle/src/mir/interpret/queries.rs:58-87` (`R1` & `R2`) | `(self, typing_env: TypingEnv<'tcx>, ct: mir::UnevaluatedConst<'tcx>, span: Span)` | `EvalToConstValueResult<'tcx>` (`Result<ConstValue, ErrorHandled>`) | Resolves `(ct.def, ct.args)` via `ty::Instance::try_resolve`. Supports `ct.promoted = Some(p)` by constructing `GlobalId { instance, promoted: ct.promoted }` and calling `const_eval_global_id` -> `tcx.eval_to_const_value_raw`. |
| `tcx.const_eval_resolve_for_typeck` | `compiler/rustc_middle/src/mir/interpret/queries.rs:90-155` (`R1`), `:90-172` (`R2`) | `R1`: `ct: ty::UnevaluatedConst<'tcx>`<br>`R2`: `ct: ty::AliasConst<'tcx>` | `ConstToValTreeResult<'tcx>` (`Result<Result<ValTree<'tcx>, Ty<'tcx>>, ErrorHandled>`) | Requires `promoted == None` (`uv.shrink()` at `consts.rs:470-491` panics if `self.promoted.is_some()`). In `R2`, `ty::UnevaluatedConst` was replaced by `ty::AliasConst` (`AliasConstKind::{Projection, InherentImpl, Free, Anon}`), and `queries.rs:102-103` normalizes `ct.args` via `with_post_analysis_normalized_invalidating_rigid_aliases`. |
| `tcx.const_eval_poly` | `compiler/rustc_middle/src/mir/interpret/queries.rs:19-29` (`R1` & `R2`) | `def_id: DefId` | `EvalToConstValueResult<'tcx>` | Evaluates `GlobalId { instance: Instance::new_raw(def_id, identity_args), promoted: None }` under `TypingEnv::post_analysis(tcx, def_id)`. |
| `tcx.const_eval_poly_to_alloc` | `compiler/rustc_middle/src/mir/interpret/queries.rs:35-46` (`R1` & `R2`) | `def_id: DefId` | `EvalToAllocationRawResult<'tcx>` (`Result<ConstAlloc<'tcx>, ErrorHandled>`) | Same as `const_eval_poly`, but calls `tcx.eval_to_allocation_raw` directly, bypassing `trivial_const` and `op_to_const` to always return `ConstAlloc { alloc_id, ty }`. |
| `tcx.eval_to_const_value_raw` | `compiler/rustc_const_eval/src/const_eval/eval_queries.rs:326-334` (`R1`), `:371-388` (`R2`) | `PseudoCanonicalInput<'tcx, GlobalId<'tcx>>` | `EvalToConstValueResult<'tcx>` | Short-circuits via `tcx.trivial_const(def_id)` when `promoted.is_none()`; otherwise calls `tcx.eval_to_allocation_raw(key).map(|val| turn_into_const_value(tcx, val, key))`. In `R2`, adds `retry_codegen_mode_with_postanalysis` (`eval_queries.rs:339-370`). |

#### 1.4 Empirical Part 1 Verification Matrix (`support/probe_output_1_98.json` & `support/probe_output_1_101.json`)

| Function in `support/probe_target.rs` | `err_count` Before MIR Query | `err_count` After `mir_drops_elaborated_and_const_checked` | `err_count` After Evaluating `required_consts` | In `body.basic_blocks`? | In `body.required_consts()`? | `eval_post_analysis` Result | `eval_mono_u32` / `eval_mono_u64` |
| :--- | :---: | :---: | :---: | :---: | :---: | :--- | :--- |
| `part1_unreachable_if_false_panic` | 0 | 0 (missed by `KnownPanicsLint`) | 1 (`E0080`) | Yes (`bb1[1]`) | Yes (1) | `Err(Reported(allowed_in_infallible=false))` | `null` |
| `part1_unreachable_if_false_div_zero` | 1 | 1 (missed by `KnownPanicsLint`) | 2 (`E0080`) | Yes (`bb1[0]`) | Yes (1) | `Err(Reported(allowed_in_infallible=false))` | `null` |
| `part1_match_false_deleted_bb_div_zero` | 2 | 2 (missed by `KnownPanicsLint`) | 3 (`E0080`) | Yes (`bb2[0]`) | Yes (1) | `Err(Reported(allowed_in_infallible=false))` | `null` |
| `part1_promoted_if_false_div_zero` | 3 | 3 (missed by `KnownPanicsLint`) | 4 (`E0080`) | **No** (`bb1[2]` only has `promoted[0]`) | **Yes (1)** (`{constant#0}`) | `Err(Reported(allowed_in_infallible=false))` | `null` |
| `part1_post_return_div_zero` | 4 | 4 | 4 | **No** (dead block deleted) | **No (0)** (not in RPO) | N/A | N/A |
| `part1_concrete_size_check_u32_ok` | 4 | 4 | 4 | Yes (`bb0[1]`) | Yes (1) | `Ok(ZeroSized -> Unit)` | `null` |
| `part1_concrete_size_check_u64_err` | 4 (missed by `analysis(())` under `--emit=metadata`) | 5 (`KnownPanicsLint` emits `E0080`) | 5 | Yes (`bb0[1]`) | Yes (1) | `Err(Reported(allowed_in_infallible=false))` | `null` |
| `part1_reachable_inline_div_zero` | 5 (missed by `analysis(())` under `--emit=metadata`) | 6 (`KnownPanicsLint` emits `E0080`) | 6 | Yes (`bb0[0]`) | Yes (1) | `Err(Reported(allowed_in_infallible=false))` | `null` |
| `part1_generic_mention_uncond_fail<T>` | 6 | 6 (skipped by `KnownPanicsLint` because `c.has_param()`) | 9 (`E0080` emitted on poly + `u32` + `u64`) | Yes (`bb0[0]`) | Yes (1) | `Err(Reported(allowed_in_infallible=false))` | `u32`: `Err(Reported)`<br>`u64`: `Err(Reported)` |
| `part1_generic_mention_size_check<T>` | 9 | 9 | 9 | Yes (`bb0[1]`) | Yes (1) | `Err(TooGeneric, span_is_dummy=false)` | `u32`: `Ok(ZeroSized)`<br>`u64`: `Err(Reported)` |
| `part1_generic_mention_trait_const<T: AssocConstTrait>` | 9 | 9 | 9 | Yes (`bb0[0]`) | Yes (1) | `Err(TooGeneric, span_is_dummy=true)` | `null` |

Notice the distinction between the two `ErrorHandled::TooGeneric(span)` cases in `compiler/rustc_middle/src/mir/interpret/error.rs:22-96`:
- When `ty::Instance::try_resolve` returns `Ok(None)` (`<T as AssocConstTrait>::TRAIT_C`), `const_eval_resolve` returns `Err(ErrorHandled::TooGeneric(DUMMY_SP))` (`span.is_dummy() == true`).
- When `ty::Instance::try_resolve` returns `Ok(Some(instance))` (`Fail::<T>::SIZE_CHECK` or `Fail::<T>::UNCOND_FAIL`), `const_eval_resolve` executes the constant body in CTFE even while `args` contains `T`: if CTFE fails before touching `T` (`UNCOND_FAIL = 1 / 0`), it returns `Err(ErrorHandled::Reported(..))` immediately; if CTFE reaches an operation that depends on `T` (`size_of::<T>()`), it returns `Err(ErrorHandled::TooGeneric(span))` with the non-dummy span of the generic operation (`span.is_dummy() == false`).

---

### 2. Anatomy of `ConstValue`, Why No General `ScalarPair` Exists, and Layout-Guided `GlobalAlloc` Decoding

#### 2.1 Why `op_to_const` Lowers `BackendRepr::ScalarPair` Composites to `ConstValue::Indirect`

`ConstValue` (`compiler/rustc_middle/src/mir/consts.rs:33-71`) has four variants and a static size assertion of 24 bytes on 64-bit targets:

```rust
pub enum ConstValue {
    Scalar(Scalar),
    ZeroSized,
    Slice { alloc_id: AllocId, meta: u64 },
    Indirect { alloc_id: AllocId, offset: Size },
}
```

In `turn_into_const_value` and `op_to_const` (`compiler/rustc_const_eval/src/const_eval/eval_queries.rs:213-293, 344-366` in `R1`; `:258-338, 390-412` in `R2`), CTFE first interns the constant's stack allocation into `GlobalAlloc::Memory(ConstAllocation)` and constructs an `MPlaceTy` (`Left(mplace)`). Then `op_to_const` decides whether to read an immediate out of `mplace`:

```rust
if op.layout.is_zst() {
    return ConstValue::ZeroSized;
}

let force_as_immediate = match op.layout.backend_repr {
    BackendRepr::Scalar(abi::Scalar::Initialized { .. }) => true,
    // We don't do `ScalarPair` as the `ConstValue::Slice` variant is more Laws-of-Compat
    // than a general mechanism: the `Immediate::ScalarPair` branch below is purely for
    // lowering valtrees cleanly, and struggles with lessons learned from #116226.
    _ => false,
};
let immediate = if force_as_immediate {
    Right(ecx.read_immediate(op).expect("normalization works on validated constants"))
} else {
    op.as_mplace_or_imm()
};
```

Because `op` is `Left(mplace)`, `force_as_immediate` is `false` for **every** `BackendRepr::ScalarPair` and `BackendRepr::Memory` type! As a result:
1. Every 2-field struct (`U64Range { min: u64, max: u64 }`), 2-element tuple (`(u8, u32)`), and `Direct`-tagged payload enum (`Option<u64>`) with `BackendRepr::ScalarPair` evaluates to **`ConstValue::Indirect { alloc_id, offset: Size::ZERO }`**, never a pair of scalars.
2. Even for `&'static str` and `&'static [u8]` (which have `BackendRepr::ScalarPair(ptr, u64)`):
   - When `tcx.is_trivial_const(def_id)` is `true` (`C_20_SLICE_STR_TRIVIAL: &str = "ebpf_verifier"`), `eval_to_const_value_raw` bypasses CTFE and returns the literal `ConstValue::Slice { alloc_id, meta: 13 }` produced by `lit_to_mir_constant` (`compiler/rustc_mir_transform/src/trivial_const.rs:46-117`).
   - When `tcx.is_trivial_const(def_id)` is `false` (`C_21_SLICE_STR_COMPUTED: &str = { let s = "computed_str"; s }` or `C_22_SLICE_U8_COERCED: &[u8] = &[10, 20, 30]`, which contains an `Unsize` coercion), `eval_to_const_value_raw` runs CTFE and `op_to_const` returns **`ConstValue::Indirect { alloc_id, offset: Size::ZERO }`**, where `alloc_id` is a 16-byte `ConstAllocation` holding `(data_ptr: Scalar::Ptr(child_alloc_id), len: 12u64)` in memory! (This is also why `ConstValue::try_get_slice_bytes_for_diagnostics` in `compiler/rustc_middle/src/mir/consts.rs:139-173` explicitly matches both `ConstValue::Slice` and `ConstValue::Indirect`.)

#### 2.2 Empirical Part 2 Matrix: 29 Constant Shapes Across `ConstValue`, `ValTree`, and Layout-Guided Decoding

| Constant (`support/probe_target.rs`) | Type | Size / Align | `BackendRepr` | `is_trivial_const` | `const_eval_resolve` (`ConstValue`) | `const_eval_resolve_for_typeck` (`ValTree`) | Layout-Guided Decoded Value |
| :--- | :--- | :---: | :--- | :---: | :--- | :--- | :--- |
| `C_01_PRIM_U64` | `u64` | 8 / 8 | `Scalar(u64)` | `true` | `Scalar(Int)` | `Ok(ValTree(Leaf(0x123456789abcdef0)))` | `Uint(u64, 1311768467463790320)` |
| `C_02_PRIM_I32_NEG` | `i32` | 4 / 4 | `Scalar(i32)` | `true` | `Scalar(Int)` | `Ok(ValTree(Leaf(0xffffffd6)))` | `Int(i32, -42)` |
| `C_03_NEWTYPE_EBPF_INSN` | `EbpfInstruction(u64)` | 8 / 8 | `Scalar(u64)` | `false` | `Scalar(Int)` | `Ok(ValTree(Branch([Leaf(0x0700000000000095)])))` | `Struct(EbpfInstruction, repr=Scalar, [0: 504403158265495701])` |
| `C_04_STRUCT_U64_RANGE` | `U64Range` | 16 / 8 | `ScalarPair(u64, u64)` | `false` | `Indirect` (`fully_init=true`, 0 ptrs) | `Ok(ValTree(Branch([Leaf(0), Leaf(0xffff...)])))` | `Struct(U64Range, [min@0: 0, max@8: u64::MAX])` |
| `C_05_TUPLE_PADDED` | `(u8, u32)` | 8 / 4 | `ScalarPair(u8, u32)` | `false` | `Indirect` (`fully_init=false`: bytes `[1..4)` uninit!) | `Ok(ValTree(Branch([Leaf(0xaa), Leaf(0x11223344)])))` | `Tuple([Uint(u8, 170)@0, Uint(u32, 287454020)@4])` |
| `C_06_NESTED_SCALAR_DATA` | `U64ScalarValueData` | 48 / 8 | `Memory { sized: true }` | `false` | `Indirect` (`fully_init=true`, 0 ptrs) | `Ok(ValTree(Branch([Branch([0, MAX]), Branch([MIN, MAX]), 0, 0])))` | `Struct(U64ScalarValueData, 4 fields @ 0, 16, 32, 40)` |
| `C_07_ARRAY_U32` | `[u32; 4]` | 16 / 4 | `Memory { sized: true }` | `false` | `Indirect` (`FieldsShape::Array`) | `Ok(ValTree(Branch([Leaf(10), Leaf(20), Leaf(30), Leaf(40)])))` | `Array(u32, len=4, [10, 20, 30, 40])` |
| `C_08_ZST_UNIT` | `()` | 0 / 1 | `Memory { sized: true }` | `false` | `ZeroSized` | `Ok(ValTree(Branch([])))` | `Unit` |
| `C_09_ZST_EMPTY_ARRAY` | `[u8; 0]` | 0 / 1 | `Memory { sized: true }` | `false` | `ZeroSized` | `Ok(ValTree(Branch([])))` | `Array(u8, [])` |
| `C_10_ZST_STRUCT` | `Marker` | 0 / 1 | `Memory { sized: true }` | `false` | `ZeroSized` | `Ok(ValTree(Branch([])))` | `ZeroSizedAdt(Marker)` |
| `C_11_ENUM_FIELDLESS_NEG` | `SimpleEnum` (`#[repr(i8)]`) | 1 / 1 | `Scalar(i8 is -1..=1)` | `false` | `Scalar(Int)` (`0xff` = `-1`) | `Ok(ValTree(Branch([Leaf(0)])))` | `Enum(SimpleEnum::Neg, [])` |
| `C_12_NICHE_OPT_BOOL_NONE` | `Option<bool>` | 1 / 1 | `Scalar(u8 is 0..=2)` | `false` | `Scalar(Int)` (`0x02` = `niche_start`) | `Ok(ValTree(Branch([Leaf(0)])))` | `Enum(Option::None, [])` |
| `C_13_NICHE_OPT_BOOL_SOME` | `Option<bool>` | 1 / 1 | `Scalar(u8 is 0..=2)` | `false` | `Scalar(Int)` (`0x01`) | `Ok(ValTree(Branch([Leaf(1), Leaf(1)])))` | `Enum(Option::Some, [0: Bool(true)])` |
| `C_14_NICHE_OPT_NZ_NONE` | `Option<NonZeroU64>` | 8 / 8 | `Scalar(u64)` | `false` | `Scalar(Int)` (`0x00` = `niche_start`) | `Ok(ValTree(Branch([Leaf(0)])))` | `Enum(Option::None, [])` |
| `C_15_NICHE_OPT_NZ_SOME` | `Option<NonZeroU64>` | 8 / 8 | `Scalar(u64)` | `false` | `Scalar(Int)` (`99`) | `Ok(ValTree(Branch([Leaf(1), Branch([Branch([Leaf(99)])])])))` | `Enum(Option::Some, [NonZero(99)])` |
| `C_16_DIRECT_OPT_U64_NONE` | `Option<u64>` | 16 / 8 | `ScalarPair(u64, union u64)` | `false` | `Indirect` (`fully_init=false`: payload `[8..16)` uninit!) | `Ok(ValTree(Branch([Leaf(0)])))` | `Enum(Option::None, [])` |
| `C_17_DIRECT_OPT_U64_SOME` | `Option<u64>` | 16 / 8 | `ScalarPair(u64, union u64)` | `false` | `Indirect` (`fully_init=true`) | `Ok(ValTree(Branch([Leaf(1), Leaf(0xdeadbeef)])))` | `Enum(Option::Some, [0@8: 3735928559])` |
| `C_18_DIRECT_RESULT_OK` | `Result<u32, u8>` | 8 / 4 | `Memory { sized: true }` | `false` | `Indirect` (`fully_init=false`: padding `[1..4)` uninit!) | `Ok(ValTree(Branch([Leaf(0), Leaf(0x12345678)])))` | `Enum(Result::Ok, [0@4: 305419896])` |
| `C_19_DIRECT_RESULT_ERR` | `Result<u32, u8>` | 8 / 4 | `Memory { sized: true }` | `false` | `Indirect` (`fully_init=false`: tail `[2..8)` uninit!) | `Ok(ValTree(Branch([Leaf(1), Leaf(0xff)])))` | `Enum(Result::Err, [0@1: 255])` |
| `C_20_SLICE_STR_TRIVIAL` | `&'static str` | 16 / 8 | `ScalarPair(ptr, u64)` | **`true`** | **`Slice { alloc_id, meta: 13 }`** | `Ok(ValTree(Branch([Leaf(0x65), ...])))` | `Str(len=13, "ebpf_verifier")` |
| `C_21_SLICE_STR_COMPUTED` | `&'static str` | 16 / 8 | `ScalarPair(ptr, u64)` | **`false`** | **`Indirect`** (16B alloc -> child 12B str alloc) | `Ok(ValTree(Branch([Leaf(0x63), ...])))` | `WideRefInMemory(Str(len=12, "computed_str"))` |
| `C_22_SLICE_U8_COERCED` | `&'static [u8]` | 16 / 8 | `ScalarPair(ptr, u64)` | **`false`** | **`Indirect`** (16B alloc -> child 3B array alloc) | `Ok(ValTree(Branch([Leaf(10), Leaf(20), Leaf(30)])))` | `WideRefInMemory(Slice(u8, [10, 20, 30]))` |
| `C_23_REF_SCALAR_U32` | `&'static u32` | 8 / 8 | `Scalar(ptr)` | `false` | `Scalar(Ptr)` -> `GlobalAlloc::Memory(4B)` | `Ok(ValTree(Leaf(0)))` | `Ref(Not, Uint(u32, 0))` |
| `C_24_REF_ARRAY_U32` | `&'static [u32; 3]` | 8 / 8 | `Scalar(ptr)` | `false` | `Scalar(Ptr)` -> `GlobalAlloc::Memory(12B)` | `Ok(ValTree(Branch([Leaf(1), Leaf(2), Leaf(3)])))` | `Ref(Not, Array(u32, [1, 2, 3]))` |
| `C_25_REF_U64_RANGE` | `&'static U64Range` | 8 / 8 | `Scalar(ptr)` | `false` | `Scalar(Ptr)` -> `GlobalAlloc::Memory(16B)` | `Ok(ValTree(Branch([Leaf(1), Leaf(2)])))` | `Ref(Not, Struct(U64Range, [1, 2]))` |
| `C_26_NESTED_REFS` | `NestedRefs<'static>` | 32 / 8 | `Memory { sized: true }` | `false` | `Indirect` (32B alloc with **3 `ProvenanceMap` entries**!) | `Ok(ValTree(Branch([...])))` | `Struct(NestedRefs, [label@0, nums@16, range@24])` |
| `C_27_RAW_PTR_INT_CAST` | `*const u8` | 8 / 8 | `Scalar(ptr)` | `false` | `Scalar(Int)` (`0x1000`, no provenance) | `Ok(ValTree(Leaf(0x1000)))` | `RawPtr(ConcreteAddr, 0x1000)` |
| `C_28_RAW_PTR_STATIC_PROV` | `*const u32` | 8 / 8 | `Scalar(ptr)` | `false` | `Scalar(Ptr)` -> `GlobalAlloc::Static(STATIC_U32)` | **`Ok(Err(NonSupportedType(*const u32)))`** | `RawPtr(Provenance, Static(STATIC_U32), offset=0)` |
| `C_29_FN_PTR` | `fn(u32) -> u32` | 8 / 8 | `Scalar(ptr)` | `false` | `Scalar(Ptr)` -> `GlobalAlloc::Function(sample_helper_fn)` | **`Ok(Err(NonSupportedType(fn(u32) -> u32)))`** | `FnPtr(sample_helper_fn, offset=0)` |

#### 2.3 Deterministic Layout-Guided `ConstValue` + `ConstAllocation` Reconstruction Algorithm and Lean 4 Mechanization

The layout-guided decoder implemented in `support/const_and_promoted_probe.rs:120-640` and mechanized in `support/MirConstAllocationDecoder.lean:134-437` operates by structural recursion on fuel and `(ConstValue, TyAndLayout<'tcx>)`:

1. **Leaf-Only `InitMask` Checking (Padding & Uninit-Payload Invariance)**:
   - As `C_05_TUPLE_PADDED` (`(u8, u32)`, `fully_init = false`), `C_16_DIRECT_OPT_U64_NONE` (`Option<u64>::None`, `fully_init = false`), `C_18_DIRECT_RESULT_OK` (`Result<u32, u8>::Ok`, `fully_init = false`), and `C_19_DIRECT_RESULT_ERR` (`Result<u32, u8>::Err`, `fully_init = false`) demonstrate, a `ConstAllocation` is **not** fully initialized across `0..layout.size` whenever inter-field alignment padding or unused union payload bytes exist.
   - Instead, the decoder recurses along `layout.fields.offset(i)` (and `layout.for_variant(&layout_cx, variant_idx).fields.offset(i)` for the active enum variant) and checks `InitMask` (`Allocation::read_scalar` in Rust; `checkInitRangeBytes` in Lean) **only** at leaf scalar/tag/pointer byte ranges `[offset, offset + leaf_size)`.
2. **Enum Discriminant & Niche Tag Resolution (`resolve_enum_variant_from_scalar`, matching `InterpCx::read_discriminant` in `compiler/rustc_const_eval/src/interpret/discriminant.rs:94-182`)**:
   - `Variants::Empty`: uninhabited (`DecodeError.invalidEnumDiscriminant`).
   - `Variants::Single { index }`: active variant is `*index` without reading a tag.
   - `Variants::Multiple { tag, tag_encoding, tag_field, .. }`: reads `tag_scalar` of size `tag.size(&tcx)` from `ConstValue::Scalar(s)` (if `BackendRepr::Scalar`) or from memory at `offset + layout.fields.offset(tag_field.as_usize())` (if `ConstValue::Indirect`):
     - `TagEncoding::Direct`: sign-extends `raw_bits` from `tag_size` to `discriminant_ty` size when `matches!(tag.primitive(), Primitive::Int(_, true))` (required for negative `#[repr(i8)]` discriminants like `C_11_ENUM_FIELDLESS_NEG` where `raw_bits = 0xff`), then matches `adt_def.discriminants(tcx)`.
     - `TagEncoding::Niche { untagged_variant, niche_variants, niche_start }`: if `tag_scalar` has pointer provenance, the active variant is `*untagged_variant`; otherwise computes `relative = tag_size.truncate(tag_bits.wrapping_sub(*niche_start))` and selects `VariantIdx::from_u32(niche_variants.start.as_u32() + relative as u32)` when `relative <= (niche_variants.last.as_u32() - niche_variants.start.as_u32()) as u128`, or `*untagged_variant` otherwise, before decoding the active variant's fields via `layout.for_variant(&layout_cx, variant_idx)`.
3. **Provenance Isolation**:
   - Reading an integer, boolean, enum discriminant tag, or slice length metadata requires `noProvenanceInRange = true` (`read_provenance = false` in `Allocation::read_scalar`), rejecting pointer provenance in scalar data bytes.
   - Reading a thin reference `&T` or fat reference `&str` / `&[T]` requires exact pointer provenance at `offset` (`lookupExactProvenance alloc.provenance offset ptr_size = some ptr`) and recursively decodes the target `GlobalAlloc::Memory` at `ptr.offset` with `fuel - 1`.

In `support/MirConstAllocationDecoder.lean` (1,896 lines, Lean `v4.34.1`, `0` `sorry`, `0` warnings under `-DwarningAsError=true`), we prove six families of kernel-checked theorems over this decoder:

| Theorem Family | Key Lean 4 Theorem Names (`support/MirConstAllocationDecoder.lean`) | Verified Property |
| :--- | :--- | :--- |
| **1. Padding-Byte & Uninit-Gap Invariance** | `decodeFromAlloc_struct_padding_invariant` (`L563`), `decodeAllocAt_struct_padding_invariant` (`L580`), `paddedU8U32_uninit_vs_0xAA_eq` (`L1445`) | Any two allocations that agree on active field windows (`AllocAgreeOnWindow`) decode to the identical `PureConst`, regardless of whether padding bytes have `initMask = false` (`0x00`) or `initMask = true` (`0xAA`). |
| **2. `AllocId` Bijection Invariance** | `decodeFromAlloc_remap_invariant` (`L747`), `decodeAllocAt_remap_invariant` (`L842`), `decodeConstValue_remap_invariant` (`L859`) | For any `AllocId` renaming `π : AllocId → AllocId` preserving `AllocEnv` lookups (`∀ id, env2 (π id) = (env1 id).map (remapGlobalAlloc π)`), `decodeConstValue env2 fuel (remapCV π cv) layout = decodeConstValue env1 fuel cv layout`. |
| **3. Provenance-Forgery Rejection** | `decodeAllocAt_int_rejects_provenance` (`L914`), `decodeAllocAt_bool_rejects_provenance` (`L930`), `decodeAllocAt_enum_tag_rejects_provenance` (`L946`) | Any pointer provenance overlapping an integer, boolean, or enum tag byte range fails closed with `.error (.unexpectedProvenanceInScalar _)`. |
| **4. Uninitialized-Scalar Rejection** | `decodeAllocAt_int_rejects_uninit` (`L967`), `decodeAllocAt_bool_rejects_uninit` (`L981`), `decodeAllocAt_niche_tag_rejects_uninit` (`L995`), `decodeAllocAt_ref_rejects_uninit` (`L1011`) | Any `initMask = false` byte inside a read scalar, boolean, niche tag, or reference pointer fails closed with `.error (.uninitializedBytes _)`. |
| **5. Concrete & Symbolic Round-Trip Soundness** | `readLeBytes_writeLeBytes` (`L1057`), `u64Range_symbolic_roundtrip` (`L1338`), `u64ScalarValueDataUninit_encode_decode_roundtrip` (`L1379`), `paddedU8U32_symbolic_roundtrip` (`L1415`), `optionBool_all_roundtrip` (`L1484`), `optionBool_invalid_byte_3_rejected` (`L1491`), `resultBoolUnit_all_roundtrip` (`L1544`), `optionNonZeroU64_some_symbolic_roundtrip` (`L1601`), `promotedU64RangeRef_decode_eq` (`L1630`), `assertEqPromotedPair_decode_eq` (`L1673`) | Proves general little-endian round-trip (`readLeBytes (writeLeBytes val count) 0 count = val % 256^count`) and symbolic/concrete round-trips for Starnix `U64Range`, `U64ScalarValueData::UNINITIALIZED`, padded `(u8, u32)`, niche `Option<bool>`, `Result<bool, ()>`, symbolic `Option<NonZeroU64>::Some(v)` (`0 < v < 2^64`), and promoted references/slices. |
| **6. Promoted MIR Body Execution vs. CTFE Equivalence** | `decodeFromAlloc_env_irrel_of_no_provenance` (`L1229`), `promoted_body_exec_eq_ctfe_decode` (`L1765`), `promotedU64Range_fieldByField_exec_eq_ctfe` (`L1800`), `promotedU64Range_fieldByField_symbolic_eq_ctfe` (`L1818`) | Small-step execution of a `promoted[p]` MIR body (allocating `_1` at `rtAllocId`, writing fields or aggregates, and returning `_0 = &_1`) and decoding its return value yields the exact same `PureConst.ref` as eagerly evaluating `GlobalId { instance, promoted: Some(p) }` at CTFE (`ctfeAllocId`) and decoding its `ConstValue`. |

---

### 3. Constant Promotion (`PromoteTemps`, `promoted[N]`)

#### 3.1 How `PromoteTemps` Validates and Extracts `promoted[N]` Bodies

1. **Representation**:
   - `rustc` has no `DefKind::Promoted` (`compiler/rustc_hir/src/def.rs:110-204`). Instead, `PromoteTemps` (`compiler/rustc_mir_transform/src/promote_consts.rs`) extracts promoted fragments into an `IndexVec<Promoted, Body<'tcx>>` stored in `tcx.resolutions(())` and returned by `tcx.promoted_mir(def_id)`.
   - The `promoted_mir` query (`compiler/rustc_mir_transform/src/lib.rs:820-837` in `R1`, `:836-851` in `R2`) runs `run_analysis_to_runtime_passes(tcx, &mut body)` on every `promoted[p]` body, so every body in `tcx.promoted_mir(def_id)` is in `MirPhase::Runtime(RuntimePhase::PostCleanup)`.
   - In the parent body, `Promoter::promote_candidate` (`promote_consts.rs:889-894` in `R1`, `:902-907` in `R2`) creates a fresh local `promoted_ref: &T`, assigns `promoted_ref = Const::Unevaluated(UnevaluatedConst::new(def_id, args).with_promoted(promoted_id), ref_ty)`, and rewrites the original borrow `_dest = &_temp` into a reborrow `_dest = &(*promoted_ref)` (preserving any outer projections on `_temp` as `(*promoted_ref).proj`).
2. **Candidate Validation Rules (`Collector` and `Validator` in `promote_consts.rs:230-705`)**:
   - Only two candidate roots exist (`enum Candidate` at `promote_consts.rs:76-83`):
     - `Candidate::Ref(Location)`: a shared borrow `&_temp` (or a mutable borrow `&mut _temp` **only** when the pointee type is a 0-length array `[T; 0]`, `promote_consts.rs:300-316`), where `_temp` has `TempState::Defined { uses: 1, .. }`.
     - `Candidate::Repeat(Location)`: the element operand of `[elem; len]` inside a `const` or `static` body when `elem` is not `Copy`.
   - **Implicit Promotion (`explicit == false`, inside `fn` and `const fn`)**:
     - Allows pure literals, structs/tuples/enums/arrays of promotable operands, checked binary arithmetic (`AddWithOverflow`, `SubWithOverflow`, `MulWithOverflow`—whose `Assert` terminator is omitted or promoted alongside the rvalue), and `BinOp::Div` / `BinOp::Rem` **when the divisor is a known non-zero literal constant** (`promote_consts.rs:603-633`, verified by `&((10u32 / 2u32) + 3u32)` -> `promoted[0]` in `promo_accepted_candidates`).
     - Rejects runtime locals, division/remainder by a non-constant or zero divisor, mutable borrows of non-`[T; 0]` types (`&mut 0u32`), shared borrows of types with interior mutability (`!ty.is_freeze(tcx, typing_env)`, e.g. `&Cell::new(0u32)` unless ZST), shared borrows of types requiring drop (`ty.needs_drop(tcx, typing_env)`, e.g. `&NeedsDropType(0u32)`), and all `TerminatorKind::Call` callees **except** functions annotated with `#[rustc_promotable]` (such as `core::mem::size_of` and `core::mem::align_of`).
   - **Explicit Promotion (`explicit == true`, inside `const` and `static` bodies for `'static` borrows, `promote_consts.rs:403-427`)**:
     - Allows calling arbitrary `const fn`s even without `#[rustc_promotable]` (`PROMO_IN_CONST_CALL` and `PROMO_IN_STATIC_CALL`), **provided** `!in_dead_code` (`promote_consts.rs:274-281` sets `in_dead_code = true` after any conditional branch in a `const`/`static` body so dead branches like `if false { let _ = &panicking_const_fn(); }` in `PROMO_IN_CONST_DEAD_BRANCH` are never promoted).

#### 3.2 Empirical Part 3 Matrix: When `promoted[N]` Evaluates Eagerly via CTFE vs. Requires `promoted_mir`

| Item in `support/probe_target.rs` | `promoted_count` | Promoted Bodies (`promoted[N]`) | `tcx.const_eval_resolve(post_analysis)` | `tcx.const_eval_resolve(monomorphized)` | Finding |
| :--- | :---: | :--- | :--- | :--- | :--- |
| `promo_accepted_candidates` | **7** (`promoted[0..=6]`) | `promoted[0]: &u32` (`&((10/2)+3)`)<br>`promoted[1]: &mut [u32; 0]` (`&mut []`)<br>`promoted[2]: &[u32; 3]` (`&[1, 2, 3]`)<br>`promoted[3]: &U64ScalarValueData`<br>`promoted[4]: &U64Range`<br>`promoted[5]: &EbpfInstruction`<br>`promoted[6]: &u32` (`&0u32`) | **All 7 return `Ok(Scalar(Ptr))`** and decode via `ConstAllocation` to exact `Ref` values (`8`, `[]`, `[1,2,3]`, `U64ScalarValueData::UNINITIALIZED`, `U64Range`, `EbpfInstruction(7)`, `0`) | N/A (monomorphic) | Candidates are numbered in reverse source order (`PromoteTemps` pops candidates in reverse). All 7 evaluate eagerly via CTFE without executing `promoted_mir` in the verifier. |
| `promo_assert_eq(a: u32)` (`assert_eq!(a, 0u32)`) | **1** (`promoted[0]`) | `promoted[0]: &u32` (`_1 = const 0_u32; _0 = &_1`) | `Ok(Scalar(Ptr))` -> `Ref(Not, Uint(u32, 0))` | N/A | `assert_eq!(a, 0u32)` promotes the literal RHS `&0u32` to `promoted[0]`, while `&a` stays a local borrow in `body.basic_blocks`. |
| `promo_rejected_candidates(runtime_x: u32)` | **0** | None (all 5 borrows remain `Rvalue::Ref` in `body.basic_blocks`) | N/A | N/A | Rejects `&(runtime_x / 2)`, `&normal_const_fn()`, `&mut 0u32`, `&Cell::new(0u32)`, and `&NeedsDropType(0u32)`. |
| `PROMO_IN_CONST_CALL` / `PROMO_IN_STATIC_CALL` | **1** (`promoted[0]`) | `promoted[0]: &u32` (`_1 = normal_const_fn() -> bb1; _0 = &_1`) | `Ok(Scalar(Ptr))` -> `Ref(Not, Uint(u32, 77))` | N/A | Explicit promotion in `const`/`static` promotes `&normal_const_fn()` and records `promoted[0]` in `required_consts` (`add_to_required = true`). |
| `PROMO_IN_CONST_DEAD_BRANCH` | **0** | None (`unpromoted_borrows` has 1 local borrow in `bb1`) | N/A | N/A | Conditional branch in `const` disables explicit promotion (`in_dead_code = true`), preventing CTFE from evaluating `&panicking_const_fn()`. |
| `promo_generic_independent<T>` | **1** (`promoted[0]`) | `promoted[0]: &U64Range` (`args = [T/#0]`) | **`Ok(Scalar(Ptr))`** -> `Ref(Not, Struct(U64Range, [10, 20]))` | `Ok(Scalar(Ptr))` -> `Ref(Not, Struct(U64Range, [10, 20]))` | Even though `uv.args = [T/#0]`, `tcx.const_eval_resolve(post_analysis)` **succeeds polymorphically** because `promoted[0]`'s body does not depend on `T`. |
| `promo_generic_array_dependent<const N: usize>` (`&[0u8; N]`) | **1** (`promoted[0]`) | `promoted[0]: &[u8; N]` (`_1 = [const 0_u8; N]; _0 = &_1`) | **`Err(TooGeneric)`** | With `N = 4`: **`Ok(Scalar(Ptr))`** -> `Ref(Not, Array(u8, len=4, [0, 0, 0, 0]))` | Polymorphic CTFE returns `Err(TooGeneric)`; resolves to `Ok(Scalar(Ptr))` upon monomorphic instantiation or via `tcx.promoted_mir(def_id)[0]`. |
| `promo_generic_size_of_dependent<T>` (`&size_of::<T>()`) | **1** (`promoted[0]`) | `promoted[0]: &usize` (`_1 = size_of::<T>() -> bb1; _0 = &_1`) | **`Err(TooGeneric)`** | With `T = u64`: **`Ok(Scalar(Ptr))`** -> `Ref(Not, Uint(usize, 8))` | `core::mem::size_of` is `#[rustc_promotable]`, so `&size_of::<T>()` is promoted in a generic `fn` and returns `Err(TooGeneric)` until `T` is instantiated or `promoted_mir(def_id)[0]` is translated. |

## Boundaries

1. **Polymorphic Constants Returning `Err(ErrorHandled::TooGeneric)`**:
   - Eager CTFE evaluation (`tcx.const_eval_resolve` + layout-guided `ConstAllocation` decoding) reduces every monomorphic `Const::Unevaluated` (including `promoted: Some(p)`) and every generic `Const::Unevaluated` whose evaluation does not inspect its type/const parameters (`Fail::<T>::UNCOND_FAIL`, `promo_generic_independent<T>`) to a concrete `ConstValue` or `ErrorHandled::Reported`.
   - When `tcx.const_eval_resolve` returns `Err(ErrorHandled::TooGeneric)`, the constant depends on an uninstantiated type or const generic parameter (`Fail::<T>::SIZE_CHECK`, `<T as AssocConstTrait>::TRAIT_C`, `&[0u8; N]`, `&size_of::<T>()`). A verifier cannot decode a concrete `ConstAllocation` polymorphically; it must either instantiate the function/constant at concrete monomorphic arguments (`TypingEnv::fully_monomorphized()`) or translate the constant/promoted MIR body (`tcx.mir_for_ctfe(def_id)` / `tcx.promoted_mir(def_id)[p]`) symbolically with explicit well-formedness obligations.
2. **Unsized Custom DSTs (`extern type` and Custom Slice-Tailed Structs)**:
   - Our layout-guided decoder (`support/const_and_promoted_probe.rs` and `support/MirConstAllocationDecoder.lean`) covers primitives, pattern types (`TyKind::Pat` / `NonZero<T>`), tuples, structs, arrays, `Single`/`Direct`/`Niche` enums, thin references (`&T`), wide slice/string references (`&str`, `&[T]` in both `ConstValue::Slice` and `ConstValue::Indirect` representations), raw pointers (`ConcreteAddr` and `GlobalAlloc::Static` provenance), and function pointers (`GlobalAlloc::Function`). Custom unsized struct tails and trait-object vtables (`GlobalAlloc::VTable`) are detected and classified in `decode_provenance_target` (`const_and_promoted_probe.rs:399-403, 474`) but are outside the scope of `PureConst` in `MirConstAllocationDecoder.lean`.
3. **Interior Mutability in Statics (`UnsafeCell` / `Atomic*`)**:
   - While shared borrows of `Freeze` constants (`&0u32`, `&U64Range { min: 0, max: 1 }`) point to immutable `GlobalAlloc::Memory(ConstAllocation)` buffers whose values never change at runtime, `GlobalAlloc::Static(def_id)` (`&raw const STATIC_U32`) names a static item identity rather than an inline immutable value if the static has interior mutability or external linkage.

## Evidence

1. **Primary `rustc` Source Citations (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` and `19833af7224424e8b53e288097d56b6af43d5bcf`)**:
   - `compiler/rustc_mir_transform/src/required_consts.rs:9-28` (`RequiredConstsVisitor::compute_required_consts`)
   - `compiler/rustc_mir_transform/src/lib.rs:460-477` (`R1`), `:471-488` (`R2`) (`mir_promoted` pipeline ordering: `RequiredConstsVisitor` before `PromoteTemps`) and `:820-837` (`R1`), `:836-851` (`R2`) (`promoted_mir` lowering to `Runtime(PostCleanup)`)
   - `compiler/rustc_mir_transform/src/known_panics_lint.rs:254, 668-688, 759-770` (`KnownPanicsLint` skipping `c.has_param()` and constant-propagating `SwitchInt` targets)
   - `compiler/rustc_interface/src/passes.rs:1170-1180` (`R1`), `:1187-1197` (`R2`) (`run_required_analyses` skipping `mir_drops_elaborated_and_const_checked` when `!should_codegen()`)
   - `compiler/rustc_monomorphize/src/collector.rs:705-723, 1349-1353` (`R1`), `:712-730, 1374-1380` (`R2`) (`MirUsedCollector::eval_constant` and `collect_items_of_instance` evaluating `body.required_consts()`)
   - `compiler/rustc_middle/src/mir/consts.rs:33-71, 139-173, 271-281, 306-333, 470-491` (`ConstValue`, `try_get_slice_bytes_for_diagnostics`, `is_required_const`, `Const::eval`, `UnevaluatedConst::shrink`)
   - `compiler/rustc_middle/src/mir/interpret/queries.rs:19-164` (`R1`), `:19-181` (`R2`) (`const_eval_poly`, `const_eval_poly_to_alloc`, `const_eval_resolve`, `const_eval_resolve_for_typeck`, `const_eval_instance`)
   - `compiler/rustc_middle/src/mir/interpret/error.rs:22-96` (`ErrorHandled::{Reported, TooGeneric}`)
   - `compiler/rustc_middle/src/mir/interpret/allocation.rs:470-519` (`R1`), `:477-526` (`R2`), `allocation/init_mask.rs:64-150`, and `allocation/provenance_map.rs:78-165` (`Allocation::read_scalar`, `InitMask`, `ProvenanceMap`)
   - `compiler/rustc_const_eval/src/const_eval/eval_queries.rs:213-399` (`R1`), `:258-483` (`R2`) (`op_to_const`, `turn_into_const_value`, `eval_to_const_value_raw`, `eval_to_allocation_raw`)
   - `compiler/rustc_const_eval/src/const_eval/valtrees.rs:19-310` (`R1`), `:19-333` (`R2`) (`VALTREE_MAX_NODES`, `const_to_valtree_inner`, `eval_to_valtree`, `valtree_to_const_value`)
   - `compiler/rustc_const_eval/src/interpret/discriminant.rs:94-182` (`InterpCx::read_discriminant` for `Direct` and `Niche` enum tags)
   - `compiler/rustc_mir_transform/src/promote_consts.rs:76-83, 230-325, 385-705, 747-1015` (`Candidate`, `Collector`, `Validator`, `Promoter`, and `add_to_required`)
2. **Packaged Reproducible Artifacts (`support/`)**:
   - [`support/const_and_promoted_probe.rs`](support/const_and_promoted_probe.rs): Standalone `rustc_driver` probe compiling against both `1.98.0-nightly` (`--cfg rustc_1_98`) and `1.101.0-nightly` (`--cfg rustc_1_101`).
   - [`support/probe_target.rs`](support/probe_target.rs): Self-contained Rust test crate exercising all 11 Part 1 functions, 29 Part 2 constant shapes, and 9 Part 3 promotion items.
   - [`support/probe_output_1_98.json`](support/probe_output_1_98.json) and [`support/probe_output_1_101.json`](support/probe_output_1_101.json): Complete JSON probe receipts for `1.98.0-nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`) and `1.101.0-nightly` (`19833af7224424e8b53e288097d56b6af43d5bcf`).
   - [`support/MirConstAllocationDecoder.lean`](support/MirConstAllocationDecoder.lean), [`support/lean-toolchain`](support/lean-toolchain), and [`support/track2_verification_receipt.json`](support/track2_verification_receipt.json): Self-contained 1,896-line Lean 4 (`v4.34.1`) mechanization (`0` `sorry`, `0` warnings) and theorem audit receipt.

## Revalidation

To revalidate the `rustc_driver` empirical probes across both `rustc 1.98.0-nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`) and `rustc 1.101.0-nightly` (`19833af7224424e8b53e288097d56b6af43d5bcf`), run from this package directory:

```bash
# 1. Compile and run against rustc 1.98.0-nightly (f8a08b688)
SYSROOT_98="$(rustc +nightly-2026-05-31 --print sysroot)"
rustc +nightly-2026-05-31 --edition=2024 --cfg rustc_1_98 \
  support/const_and_promoted_probe.rs -o ./probe_1_98 \
  -C link-arg=-Wl,-rpath,"${SYSROOT_98}/lib"
(./probe_1_98 support/probe_target.rs \
  --crate-type=lib --edition=2024 --emit=metadata || true) \
  | python3 -m json.tool > ./probe_output_1_98.new.json
diff -u support/probe_output_1_98.json ./probe_output_1_98.new.json
rm -f ./probe_1_98 ./probe_output_1_98.new.json

# 2. Compile and run against rustc 1.101.0-nightly (19833af72)
SYSROOT_101="$(rustc +nightly --print sysroot)"
rustc +nightly --edition=2024 --cfg rustc_1_101 \
  support/const_and_promoted_probe.rs -o ./probe_1_101 \
  -C link-arg=-Wl,-rpath,"${SYSROOT_101}/lib"
(./probe_1_101 support/probe_target.rs \
  --crate-type=lib --edition=2024 --emit=metadata || true) \
  | python3 -m json.tool > ./probe_output_1_101.new.json
diff -u support/probe_output_1_101.json ./probe_output_1_101.new.json
rm -f ./probe_1_101 ./probe_output_1_101.new.json
```

To revalidate the Lean 4 (`v4.34.1`) mechanization (`0` `sorry`, `0` warnings, standard axioms only), run:

```bash
cd support && anneal-lean-run --mode file --concurrency 5 -- \
  lean -DwarningAsError=true MirConstAllocationDecoder.lean
```
