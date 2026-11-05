# `rustc` `Runtime(PostCleanup)` MIR Pipeline, `const` Placement, Layout Folding, and UB Check Lowering

## Summary

Basis: `normative`, `source`, `execution`, `derived`

When a formal verification tool extracts Rust Mid-level Intermediate
Representation (MIR) from the `mir_drops_elaborated_and_const_checked` query
(`MirPhase::Runtime(RuntimePhase::PostCleanup)`) under `-Z mir-opt-level=0` and
`-Z mir-preserve-ub`, the resulting IR reflects a specific slice of `rustc`
lowering passes, constant placement rules, layout queries, and runtime check
intrinsics. Inspecting and executing `rust-lang/rust` at commits
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (`1.98.0-nightly`, `2026-05-30`) and
`5c543b0b8c73c7b72bc8284ced4fb22ead15734d` (`1.101.0-nightly`, `2026-09-29`),
together with The Rust Reference (`82da570bafd9efed421bdbae0f8603ede8dd308b`,
bundled with `rustc 1.99.1`), establishes four architectural results:

1. **Pre-optimization MIR pipeline and UB-check passes**: Between THIR lowering
   (`mir_built`) and `mir_drops_elaborated_and_const_checked`
   (`Runtime(PostCleanup)`), `rustc` executes 32 ordered build, analysis, drop
   elaboration, and runtime-lowering steps. Setting `-Z mir-opt-level=0` does
   not disable any pre-optimization pass because `pass_manager::should_run_pass`
   only consults `mir_opt_level()` inside `run_optimization_passes`
   (`optimized_mir`). Up to `Runtime(PostCleanup)`, `-Z mir-preserve-ub` gates
   only two behaviors: it disables `RemovePlaceMention` and keeps
   `preserve_switch_reads = true` in `SimplifyCfg::PreOptimizations`. Pointer
   and enum UB-check passes (`CheckAlignment`, `CheckNull`, `CheckEnums`) and
   `remap_mir_for_const_eval_select` run only after `Runtime(PostCleanup)` (in
   `optimized_mir` and `mir_for_ctfe`), and `CheckAlignment`/`CheckNull`
   furthermore return early without modifying the body whenever
   `LangItem::PanicImpl` is absent (as in `#![no_std]` library crates).
2. **Layout query lowering and premature layout-folding pathways**: `NullaryOp`
   no longer exists on `mir::Rvalue`. Calls to `core::mem::{size_of, align_of,
   size_of_val, align_of_val}` remain uninlined `TerminatorKind::Call` nodes in
   `Runtime(PostCleanup)` and `mir_for_ctfe`, while `core::mem::offset_of!`
   expands to `const { builtin # offset_of(...) }`, producing a
   `Const::Unevaluated` in the enclosing function and a call to
   `core::intrinsics::offset_of` (`LangItem::OffsetOf`) inside the inline
   constant body. Unguaranteed `repr(Rust)` layout choices can still fold into
   concrete literals before or during capture through five specific pathways—most
   notably type-system `ty::Const` evaluation in array lengths and repeat counts
   (`[0u8; size_of::<T>()]`) before `mir_built` finishes, which requires
   filtering `DefKind::AnonConst` by `AnonConstKind::NonTypeSystemInline` when
   upgrading to `1.101.0-nightly`.
3. **`Body.basic_blocks` versus `Body.required_consts` placement**: During
   `mir_promoted`, `RequiredConstsVisitor::compute_required_consts` copies every
   `is_required_const()` operand reachable in reverse postorder into
   `body.required_consts` without removing the `Assign(_ =
   Use(Constant(Const::Unevaluated(..))))` statement from `body.basic_blocks`.
   Consequently, at `Runtime(PostCleanup)`, value `const` blocks, live statement
   `const` blocks, dead `if false { const { ... } }` blocks, and `let _ =
   S::<T>::OK` bindings appear in both `basic_blocks` and `required_consts`,
   whereas post-`return` `const` blocks are deleted by `SimplifyCfg::Initial`
   during `mir_built` before `RequiredConstsVisitor` runs. Evaluating
   `Const::Unevaluated` when control flow reaches its `Assign` statement in
   `basic_blocks` aligns directly with Rust Reference rule
   `r[expr.block.const.evaluation]` without relying on unexecuted dead-branch
   constant evaluation (`r[expr.block.const.not-executed]`),
   `RequiredConstsVisitor`, or `MentionedItems`.
4. **`assert_unsafe_precondition!`, `Operand::RuntimeChecks`, and `Assert`
   unwind handling**: In `library/core`, `slice::from_raw_parts`,
   `ptr::copy_nonoverlapping`, `NonNull::new_unchecked`,
   `hint::unreachable_unchecked`, and `u32::unchecked_add` unconditionally
   expand `assert_unsafe_precondition!(check_language_ub, ...)`, whereas
   `ptr::read` and `ptr::write` gate `assert_unsafe_precondition!` behind
   `#[cfg(debug_assertions)]` (absent in precompiled sysroot `core`). Lowering
   `intrinsics::ub_checks()` via `LowerIntrinsics` produces
   `Operand::RuntimeChecks(RuntimeChecks::UbChecks)`. In any verifier whose
   safety specification permits panicking unwinds while forbidding Undefined
   Behavior, resolving `UbChecks` to `true` while modeling `panic_nounwind_fmt`
   as a normal unwind unsoundly turns language UB into a defined unwind, while
   resolving `UbChecks` to `false` skips `precondition_check` and admits UB
   unless the verifier independently enforces every language and library
   precondition on the subsequent primitive. Furthermore, a MIR extractor that
   maps `TerminatorKind::Assert` to an unconditional abort/UB terminator
   whenever `unwind` is `UnwindAction::Terminate` or `UnwindAction::Unreachable`
   miscompiles the assertion's success branch.

## Applicability

Basis: `normative`, `source`, `execution`

This report applies to:

- **`rust-lang/rust` at `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`**
  (`rustc 1.98.0-nightly (2026-05-30)`, toolchain `nightly-2026-05-31`).
- **`rust-lang/rust` at `5c543b0b8c73c7b72bc8284ced4fb22ead15734d`**
  (`rustc 1.101.0-nightly (2026-09-29)`, toolchain `nightly-2026-09-30`), used
  to bound forward-compatibility changes across MIR pass policies, `DefKind`,
  and `CastKind`.
- **`rust-lang/reference` at `82da570bafd9efed421bdbae0f8603ede8dd308b`**
  (bundled with `rustc 1.99.1 (58cf8f9c35b355199727627d07ae34a4e2846d67
  2026-10-13)`), specifically `const_eval.html` and
  `expressions/block-expr.html` (`r[expr.block.const.eval]`,
  `r[expr.block.const.generic-params]`, `r[expr.block.const.evaluation]`, and
  `r[expr.block.const.not-executed]`).

All execution probes were run on `x86_64-unknown-linux-gnu`. Passes and queries
whose behavior depends on panic strategy (`-C panic=unwind` vs. `-C panic=abort`),
optimization level (`-Z mir-opt-level` and `-C opt-level`), UB preservation
(`-Z mir-preserve-ub`), debug assertions (`-C debug-assertions`), UB checks
(`-Z ub-checks`), or `LangItem::PanicImpl` availability (`#![no_std]` library
crates) are explicitly parameterized in the findings below.

## Findings

### 1. Complete MIR Pipeline from `mir_built` to `Runtime(PostCleanup)`, `mir_for_ctfe`, and Early `optimized_mir`

Basis: `source`, `execution`, `derived`

#### 1.1 Query Progression and Removal of `mir_const`

In both `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (`1.98.0-nightly`) and
`5c543b0b8c73c7b72bc8284ced4fb22ead15734d` (`1.101.0-nightly`), the historical
`mir_const` query no longer exists (`mir_const` appears only in a stale doc
comment at `compiler/rustc_mir_transform/src/lib.rs#L427`). The query pipeline
in `compiler/rustc_mir_transform/src/lib.rs` proceeds through five stages:

1. **`mir_built(def: LocalDefId) -> &Steal<Body>`** (`lib.rs#L381-L416`):
   Calls `tcx.build_mir_inner_impl(def)`
   (`compiler/rustc_mir_build/src/builder/mod.rs#L69-L109`), which steals
   `tcx.thir_body(def)`, constructs the initial MIR body, materializes scope
   drop trees (`builder.build_drop_trees()`), and disconnects uninhabited call
   targets (`builder.lint_and_remove_uninhabited()`, moved to the
   `LintAndRemoveUninhabited` `MirPass` in `1.101.0-nightly`). Unless
   `trivial_const::trivial_const` (`lib.rs#L389-L394`, `trivial_const.rs#L46-L106`)
   short-circuits on a single-block literal constant, `mir_built` runs
   `pm::run_passes` (`lib.rs#L398-L414`) including `SimplifyCfg::Initial` while
   remaining in `MirPhase::Built`.
2. **`mir_const_qualif(def: DefId) -> ConstQualifs`** (`lib.rs#L350-L378`):
   Borrows `tcx.mir_built(def)` read-only and runs
   `rustc_const_eval::check_consts::check::Checker::new(tcx, def, body).check_body()`.
3. **`mir_promoted(def: LocalDefId) -> (&Steal<Body>, &Steal<IndexVec<Promoted, Body>>)`**
   (`lib.rs#L419-L478`): Steals `tcx.mir_built(def)`, runs
   `RequiredConstsVisitor::compute_required_consts(&mut body)` (`lib.rs#L462`)
   in reverse postorder before promotion, and runs `PromoteTemps`,
   `SimplifyCfg::PromoteConsts`, `InstrumentCoverage`, and
   `lint_tail_expr_drop_order::run_lint`, transitioning to
   `MirPhase::Analysis(AnalysisPhase::Initial)`.
4. **`mir_drops_elaborated_and_const_checked(def: LocalDefId) -> &Steal<Body>`**
   (`lib.rs#L513-L565`): Forces `mir_borrowck(def)`, `check_liveness(def)`, and
   `check_well_formed(root)` (plus `check_transmutes(root)` in
   `1.101.0-nightly`), steals `tcx.mir_promoted(def).0`, and invokes
   `run_analysis_to_runtime_passes(tcx, &mut body)` (`lib.rs#L569-L599`) across
   four substages:
   - **Substage 3a (`run_analysis_cleanup_passes`, `lib.rs#L604-L620`)**:
     Transitions `Analysis(Initial)` to `Analysis(PostCleanup)`.
   - **Substage 3b (`const_precise_live_drops`, `lib.rs#L578-L590`)**: Runs only
     when `tcx.hir_body_const_context(def).is_some()`.
   - **Substage 3c (`run_runtime_lowering_passes`, `lib.rs#L623-L647`)**:
     Transitions `Analysis(PostCleanup)` to `Runtime(Initial)`.
   - **Substage 3d (`run_runtime_cleanup_passes`, `lib.rs#L650-L670`)**:
     Transitions `Runtime(Initial)` to `Runtime(PostCleanup)` and clears
     `decl.local_info = ClearCrossCrate::Clear` on every `LocalDecl`
     (`lib.rs#L667-L669`).
5. **`mir_for_ctfe(def_id: DefId)` (`lib.rs#L481-L508`) and
   `inner_optimized_mir` (`lib.rs#L791-L824`)**: Both start from
   `mir_drops_elaborated_and_const_checked` (stolen for constants/statics/fns,
   cloned for `const fn`), run `remap_mir_for_const_eval_select(tcx, body,
   hir::Constness::{Const, NotConst})` (`lib.rs#L234-L304`), and then run either
   `CtfeLimit` (for `mir_for_ctfe`, `lib.rs#L506`) or `run_optimization_passes`
   (for `optimized_mir`, `lib.rs#L673-L789`).

#### 1.2 Why `-Z mir-opt-level=0` Does Not Disable Pre-Optimization Passes

In `1.98.0-nightly`, `pass_manager::should_run_pass`
(`compiler/rustc_mir_transform/src/pass_manager.rs#L140-L148`) checks
`pass.is_enabled(&tcx.sess) && (is_required || tcx.sess.mir_opt_level() > 0)`
only when invoked from `run_optimization_passes` (`optimized_mir`). Every pass
up to `mir_drops_elaborated_and_const_checked` (`Runtime(PostCleanup)`) is
invoked via `pm::run_passes` or `pm::run_passes_no_validate`, which only checks
`pass.is_enabled(&tcx.sess)` (`pass_manager.rs#L116`). In `1.101.0-nightly`,
`MirPass::policy` replaces `is_required`/`is_enabled` with
`PassPolicy::{Required, AlwaysEnabled, Disabled, EnabledAtOptLevel}`
(`pass_manager.rs#L112-L133`), and all `SimplifyCfg` instances prior to
`optimized_mir` carry `PassPolicy::AlwaysEnabled`. Consequently, under
`-Z mir-opt-level=0 -Z mir-preserve-ub`, every non-lint pass between `mir_built`
and `Runtime(PostCleanup)` runs unconditionally except `InstrumentCoverage`
(when `-C instrument-coverage` is off) and `RemovePlaceMention` (disabled by
`-Z mir-preserve-ub`).

#### 1.3 Complete 32-Step Ordered Pass Inventory

The table below catalogs every step from THIR construction through
`Runtime(PostCleanup)`, `mir_for_ctfe`, and the start of `optimized_mir` along
four semantic axes:
- **(a) Eval Order / Drop Schedule**: Commits to an expression evaluation order
  or temporary drop schedule.
- **(b) Synthetic State**: Introduces or rewrites compiler-synthetic locals,
  `Promoted` bodies, dynamic drop flags, `WithRetag::No`, or synthetic casts.
- **(c) Runtime Checks**: Emits or lowers `TerminatorKind::Assert`,
  `Operand::RuntimeChecks`, `CheckAlignment`, `CheckNull`, or `CheckEnums`.
- **(d) Unreachable Block Deletion**: Deletes unreachable blocks
  (`remove_dead_blocks`), disconnects CFG edges, or replaces bodies with
  `TerminatorKind::Unreachable`.

| # | Query / Substage | Pass / Step Name | Exact Source Location (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`) | Phase After Step | Enabled under `-Z mir-opt-level=0 -Z mir-preserve-ub`? | (a) Eval Order / Drop Schedule | (b) Synthetic State | (c) Runtime Checks | (d) Unreachable Block Deletion |
| :- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| 0.1 | `mir_built` | `build_mir_inner_impl` (`construct_fn` / `construct_const`) | `compiler/rustc_mir_build/src/builder/mod.rs#L69-L109, #L454-L609` | `Built` | **Yes** (always) | **Yes**: linearizes THIR expressions into sequential statements in left-to-right operand order (`expr/as_rvalue.rs`, `expr/into.rs`) and fixes temporary scopes (`builder/scope.rs#L1-L1620`). Lowers `intrinsics::write_via_move` and `write_box_via_move` directly to `*ptr = val` without drop (`expr/into.rs#L397-L445`). | **Yes**: creates anonymous temporaries (`LocalDecl`), `FakeRead`, `FakeBorrow`, `BackwardIncompatibleDropHint`, `PlaceMention`, `StorageLive`/`StorageDead`. | **Yes**: emits `TerminatorKind::Assert` for div/rem by zero and `MIN / -1` (`expr/as_rvalue.rs#L529-L605`), bounds checks (`expr/as_place.rs`), and overflow asserts when `check_overflow` holds (`builder/mod.rs#L758-L765`, `expr/as_rvalue.rs#L102-L122, #L456-L528`). | **No** |
| 0.2 | `mir_built` | `builder.build_drop_trees()` | `compiler/rustc_mir_build/src/builder/mod.rs#L549, #L598`, `builder/scope.rs#L1180-L1350` | `Built` | **Yes** (always) | **Yes**: materializes scope-exit and unwind `TerminatorKind::Drop` chains in reverse-declaration (LIFO) order. | **No** | **No** | **No** |
| 0.3 | `mir_built` | `builder.lint_and_remove_uninhabited()` (`1.101.0`: `LintAndRemoveUninhabited`) | `compiler/rustc_mir_build/src/builder/mod.rs#L827-L936` (`1.101.0`: `rustc_mir_transform/src/lint_uninhabited.rs`) | `Built` | **Yes** (always) | **No** | **No** | **No** | **Yes (edges)**: sets `target = None` on `TerminatorKind::Call` when the return type is uninhabited, disconnecting the return successor prior to `SimplifyCfg::Initial`. |
| 1.1 | `mir_built` | `Lint(CheckForceInline)` | `compiler/rustc_mir_transform/src/check_inline.rs#L14-L37` (`lib.rs#L402`) | `Built` | **Yes** (`is_required: true`) | **No** (read-only lint) | **No** | **No** | **No** |
| 1.2 | `mir_built` | `Lint(CheckCallRecursion)` | `compiler/rustc_mir_transform/src/check_call_recursion.rs#L16-L35` (`lib.rs#L403`) | `Built` | **Yes** (`is_required: true`) | **No** (read-only lint) | **No** | **No** | **No** |
| 1.3 | `mir_built` | `Lint(CheckPackedRef)` | `compiler/rustc_mir_transform/src/check_packed_ref.rs#L8-L55` (`lib.rs#L404`) | `Built` | **Yes** (`is_required: true`) | **No** (read-only hard error on unaligned `&packed.field`) | **No** | **No** | **No** |
| 1.4 | `mir_built` | `Lint(CheckConstItemMutation)` | `compiler/rustc_mir_transform/src/check_const_item_mutation.rs#L11-L18` (`lib.rs#L405`) | `Built` | **Yes** (`is_required: true`) | **No** (read-only lint) | **No** | **No** | **No** |
| 1.4b | `mir_built` (`1.101.0` only) | `Lint(CheckMutRestriction)` | `compiler/rustc_mir_transform/src/check_mut_restriction.rs` | `Built` | **Yes** (`PassPolicy::Required`) | **No** (read-only lint) | **No** | **No** | **No** |
| 1.5 | `mir_built` | `Lint(FunctionItemReferences)` | `compiler/rustc_mir_transform/src/function_item_references.rs#L12-L19` (`lib.rs#L406`) | `Built` | **Yes** (`is_required: true`) | **No** (read-only lint) | **No** | **No** | **No** |
| 1.6 | `mir_built` | `SimplifyCfg::Initial` | `compiler/rustc_mir_transform/src/simplify.rs#L48-L104` (`lib.rs#L411`) | `Built` | **Yes** (`PassPolicy::AlwaysEnabled`) | **No** | **No** | **No** | **Yes**: strips `Nop`, threads `Goto` chains, merges single-predecessor `Goto` targets, and deletes unreachable blocks (`remove_dead_blocks`, `simplify.rs#L349-L413`); `preserve_switch_reads = true`. |
| 1.7 | `mir_built` | `Lint(SanityCheck)` | `compiler/rustc_mir_transform/src/sanity_check.rs#L5-L11` (`lib.rs#L412`) | `Built` | **Yes** (`is_required: true`) | **No** (read-only check) | **No** | **No** | **No** |
| 2.0 | `mir_const_qualif` | `Checker::check_body` | `compiler/rustc_mir_transform/src/lib.rs#L350-L378` | `Built` (borrowed) | **Yes** (const contexts) | **No** (read-only const check) | **No** | **No** | **No** |
| 2.1 | `mir_promoted` | `RequiredConstsVisitor::compute_required_consts` | `compiler/rustc_mir_transform/src/required_consts.rs#L9-L51` (`lib.rs#L462`) | `Built` | **Yes** (always) | **Yes**: populates `body.required_consts` in reverse-postorder traversal over the CFG. | **No** | **No** | **No** |
| 2.2 | `mir_promoted` | `PromoteTemps` | `compiler/rustc_mir_transform/src/promote_consts.rs#L37-L67, #L295-L839` (`lib.rs#L469`) | `Built` | **Yes** (`is_required: true`) | **Yes**: extracts promotable rvalue subtrees into `Promoted` constant bodies evaluated at CTFE. | **Yes**: creates `Promoted` bodies in `tcx.promoted_mir(def)` and replaces borrows with `Const::Unevaluated(..., Some(p))`. (`Operand::RuntimeChecks(_)` and `WithRetag::No` are `Err(Unpromotable)`, `promote_consts.rs#L365, #L427`). | **No** | **No** (leaves `Nop`s and disconnected blocks for `SimplifyCfg::PromoteConsts`). |
| 2.3 | `mir_promoted` | `SimplifyCfg::PromoteConsts` | `compiler/rustc_mir_transform/src/simplify.rs#L48-L104` (`lib.rs#L470`) | `Built` | **Yes** (`is_enabled: true`) | **No** | **No** | **No** | **Yes**: strips `Nop`s and dead blocks left by `PromoteTemps` (`remove_dead_blocks`); `preserve_switch_reads = true`. |
| 2.4 | `mir_promoted` | `InstrumentCoverage` | `compiler/rustc_mir_transform/src/coverage/mod.rs#L24-L61` (`lib.rs#L471`) | `Analysis(Initial)` | **No** (`sess.instrument_coverage()`) | **No** | Injects `StatementKind::Coverage` only when `-C instrument-coverage` is enabled. | **No** | **No** |
| 2.5 | `mir_promoted` | `lint_tail_expr_drop_order::run_lint` | `compiler/rustc_mir_transform/src/lint_tail_expr_drop_order.rs#L27-L56` (`lib.rs#L474`) | `Analysis(Initial)` | **Yes** (read-only lint) | **No** | **No** | **No** | **No** |
| 3a.0 | `mir_drops_elaborated_and_const_checked` | `mir_borrowck` / `check_liveness` / `check_well_formed` (+ `check_transmutes` in `1.101.0`) | `compiler/rustc_mir_transform/src/lib.rs#L517-L560` | `Analysis(Initial)` | **Yes** (always) | **No** (read-only analyses) | **No** | **No** | **No** |
| 3a.1 | `run_analysis_cleanup_passes` | `ImpossiblePredicates` (`1.101.0`: `ImpossibleClauses`) | `compiler/rustc_mir_transform/src/impossible_predicates.rs#L37-L77` (`lib.rs#L611`) | `Analysis(Initial)` | **Yes** (`is_required: true`) | **No** | **No** | **No** | **Yes**: if `body.tainted_by_errors.is_some()` or predicates are unsatisfiable, replaces the entire CFG with `bb0: { unreachable; }`. |
| 3a.2 | `run_analysis_cleanup_passes` | `CleanupPostBorrowck` | `compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs#L24-L91` (`lib.rs#L612`) | `Analysis(Initial)` | **Yes** (`is_required: true`) | **No** | **Yes (erasure)**: replaces `AscribeUserType`, `FakeRead`, `BorrowKind::Fake`, `Coverage(BlockMarker \| SpanMarker)`, and `BackwardIncompatibleDropHint` with `Nop`; rewrites `ArrayToPointer`/`MutToConstPointer` to `CastKind::PtrToPtr`; clears `user_ty`. | **No** | **Yes (edges)**: rewrites `FalseEdge` and `FalseUnwind` to `Goto { target: real_target }`, disconnecting borrowck-only edges. |
| 3a.3 | `run_analysis_cleanup_passes` | `RemoveNoopLandingPads` | `compiler/rustc_mir_transform/src/remove_noop_landing_pads.rs#L11-L83` (`lib.rs#L613`) | `Analysis(Initial)` | **Yes** when `sess.panic_strategy().unwinds()`; **No** under `-C panic=abort` | **No** | **No** | **No** | **Yes (unwind edges)**: redirects unwind targets across `Goto` + `Resume` landing pads. |
| 3a.4 | `run_analysis_cleanup_passes` | `SimplifyCfg::PostAnalysis` | `compiler/rustc_mir_transform/src/simplify.rs#L48-L104` (`lib.rs#L614`) | `Analysis(Initial)` | **Yes** (`is_enabled: true`) | **No** | **No** | **No** | **Yes**: deletes dead blocks left by `CleanupPostBorrowck` and `RemoveNoopLandingPads` (`remove_dead_blocks`); `preserve_switch_reads = true`. |
| 3a.5 | `run_analysis_cleanup_passes` | `Derefer` | `compiler/rustc_mir_transform/src/deref_separator.rs#L8-L107` (`lib.rs#L615`) | `Analysis(PostCleanup)` | **Yes** (`is_required: true`) | **No** | **Yes**: splits any `ProjectionElem::Deref` at index `> 0` into a synthetic temporary (`LocalInfo::DerefTemp`) assigned via `Rvalue::CopyForDeref(place)` (`deref_separator.rs#L46-L85`). | **No** | **No** |
| 3b.1 | `const_precise_live_drops` | `RemoveUninitDrops` | `compiler/rustc_mir_transform/src/remove_uninit_drops.rs#L17-L70` (`lib.rs#L583`) | `Analysis(PostCleanup)` | **Conditional**: const contexts only | **Yes**: replaces `Drop` of uninitialized or non-drop places with `Goto`. | **No** | **No** | **Yes (unwind edges)**: disconnects cleanup blocks of elided drops. |
| 3b.2 | `const_precise_live_drops` | `SimplifyCfg::RemoveFalseEdges` | `compiler/rustc_mir_transform/src/simplify.rs#L48-L104` (`lib.rs#L585`) | `Analysis(PostCleanup)` | **Conditional**: const contexts only | **No** | **No** | **No** | **Yes**: deletes cleanup blocks disconnected by `RemoveUninitDrops` (`remove_dead_blocks`). |
| 3b.3 | `const_precise_live_drops` | `Lint(CheckLiveDrops)` | `compiler/rustc_mir_transform/src/post_drop_elaboration.rs#L7-L56` (`lib.rs#L586`) | `Analysis(PostCleanup)` | **Conditional**: const contexts only | **No** (read-only const check) | **No** | **No** | **No** |
| 3c.1 | `run_runtime_lowering_passes` | `CriticalCallEdges` (`AddCallGuards`) | `compiler/rustc_mir_transform/src/add_call_guards.rs#L24-L128` (`lib.rs#L630`) | `Analysis(PostCleanup)` | **Yes** (`is_required: true`) | **No** | **Yes (CFG blocks)**: splits critical edges out of `Call` and `InlineAsm`. | **No** | **No** |
| 3c.2 | `run_runtime_lowering_passes` | `PostAnalysisNormalize` | `compiler/rustc_mir_transform/src/post_analysis_normalize.rs#L9-L86` (`lib.rs#L632`) | `Analysis(PostCleanup)` | **Yes** (`is_required: true`) | **No** | **Yes**: normalizes types/consts in `TypingEnv::post_analysis` (revealing opaque types) and strips `ProjectionElem::OpaqueCast`. | **No** | **No** |
| 3c.3 | `run_runtime_lowering_passes` | `Subtyper` (`AddSubtypingProjections`) | `compiler/rustc_mir_transform/src/add_subtyping_projections.rs#L7-L71` (`lib.rs#L635`) | `Analysis(PostCleanup)` | **Yes** (`is_required: true`) | **No** | **Yes**: inserts `_tmp = rval; place = Cast(CastKind::Subtype, Move(_tmp), place_ty)` where `place_ty != rval_ty`. | **No** | **No** |
| 3c.4 | `run_runtime_lowering_passes` | `ElaborateDrops` | `compiler/rustc_mir_transform/src/elaborate_drops.rs#L48-L355` (`lib.rs#L636`) | `Analysis(PostCleanup)` | **Yes** (`is_required: true`) | **Yes**: expands abstract `Drop` terminators into static, conditional (`SwitchInt` on drop flags), or open field-by-field drop ladders in canonical field declaration order. | **Yes**: allocates synthetic `bool` drop-flag locals (`create_drop_flag`, `elaborate_drops.rs#L309-L315`), inserts `drop_flag = const true/false` updates, and guards drops with `SwitchInt`. | **No** | **Yes**: elides drops of uninitialized/non-`needs_drop` places and calls `remove_dead_blocks(body)` (`elaborate_drops.rs#L92`). |
| 3c.5 | `run_runtime_lowering_passes` | `Lint(CheckDropRecursion)` | `compiler/rustc_mir_transform/src/check_call_recursion.rs#L38-L62` (`lib.rs#L637`) | `Analysis(PostCleanup)` | **Yes** (`is_required: true`) | **No** (read-only lint) | **No** | **No** | **No** |
| 3c.6 | `run_runtime_lowering_passes` | `AbortUnwindingCalls` | `compiler/rustc_mir_transform/src/abort_unwinding_calls.rs#L24-L144` (`lib.rs#L639`) | `Analysis(PostCleanup)` | **Yes** (`is_required: true`) | **Yes (unwind semantics)**: rewrites `UnwindAction::Continue`/`Cleanup` on `Call`, `Drop`, and `Assert` to `UnwindAction::Unreachable` (when callee is `#[rustc_nounwind]`) or `UnwindAction::Terminate(Reason)` (when caller ABI cannot unwind or `-C panic=abort`). | **No** | **No** | **Yes**: calls `simplify::remove_dead_blocks(body)` (`abort_unwinding_calls.rs#L143`) to delete cleanup blocks made unreachable. |
| 3c.7 | `run_runtime_lowering_passes` | `AddMovesForPackedDrops` | `compiler/rustc_mir_transform/src/add_moves_for_packed_drops.rs#L38-L154` (`lib.rs#L640`) | `Analysis(PostCleanup)` | **Yes** (`is_required: true`) | **No** | **Yes**: moves packed fields into a synthetic aligned stack temporary before `Drop` to avoid creating an unaligned `&mut FieldTy`. | **No** | **No** |
| 3c.8 | `run_runtime_lowering_passes` | `EraseDerefTemps` | `compiler/rustc_mir_transform/src/erase_deref_temps.rs#L1-L44` (`lib.rs#L641`) | `Analysis(PostCleanup)` | **Yes** (`is_required: true`) | **No** | **Yes**: rewrites `Rvalue::CopyForDeref(place)` into `Rvalue::Use(Operand::Copy(place), WithRetag::No)` (`erase_deref_temps.rs#L20-L22`). | **No** | **No** |
| 3c.9 | `run_runtime_lowering_passes` | `ElaborateBoxDerefs` | `compiler/rustc_mir_transform/src/elaborate_box_derefs.rs#L1-L167` (`lib.rs#L642`) | `Analysis(PostCleanup)` | **Yes** (`is_required: true`) | **No** | **Yes**: rewrites `*(box_local)` by allocating `_ptr: *const T`, assigning `_ptr = Cast(CastKind::Transmute, Copy(box_local.0.0), *const T)` (`elaborate_box_derefs.rs#L70-L83`; in `1.101.0`, `CastKind::BoxDerefTransmute`), and replacing `*(box_local)` with `(*_ptr)`. | **No** | **No** |
| 3c.10 | `run_runtime_lowering_passes` | `coroutine::StateTransform` | `compiler/rustc_mir_transform/src/coroutine.rs#L1-L1996` (`lib.rs#L643`) | `Analysis(PostCleanup)` | **Yes** (coroutines only) | **Yes**: lowers `Yield` points into a state-machine `SwitchInt`. | **Yes**: packs live-across-yield locals into coroutine state layout. | **No** | **Yes** (rebuilds coroutine CFG). |
| 3c.11 | `run_runtime_lowering_passes` | `Lint(KnownPanicsLint)` | `compiler/rustc_mir_transform/src/known_panics_lint.rs#L27-L61` (`lib.rs#L644`) | `Runtime(Initial)` | **Yes** (read-only lint) | **No** | **No** | **No** | **No** |
| 3d.1 | `run_runtime_cleanup_passes` | `LowerIntrinsics` | `compiler/rustc_mir_transform/src/lower_intrinsics.rs#L10-L344` (`lib.rs#L661`) | `Runtime(Initial)` | **Yes** (`is_required: true`) | **No** | **Yes**: lowers intrinsic calls to `CopyNonOverlapping`, `Assume`, `Unreachable`, `BinaryOp`, `UnaryOp::PtrMetadata`, `CastKind::Transmute`, `AggregateKind::RawPtr`, `Discriminant`, and `read_via_copy` (`Rvalue::Use(Operand::Copy(*ptr), WithRetag::Yes)`). | **Yes**: lowers `core::intrinsics::{ub_checks, overflow_checks, contract_checks}()` into `Assign(*dest, Rvalue::Use(Operand::RuntimeChecks(UbChecks \| OverflowChecks \| ContractChecks), WithRetag::Yes))` (`lower_intrinsics.rs#L26-L43`). | **Yes (edges)**: lowers `intrinsics::unreachable()` and uninhabited `read_via_copy`/`transmute` to `TerminatorKind::Unreachable` (`lower_intrinsics.rs#L172-L176, #L259-L263`). |
| 3d.2 | `run_runtime_cleanup_passes` | `RemovePlaceMention` | `compiler/rustc_mir_transform/src/remove_place_mention.rs#L7-L27` (`lib.rs#L662`) | `Runtime(Initial)` | **No — disabled by `-Z mir-preserve-ub`** (`!sess.opts.unstable_opts.mir_preserve_ub`, `remove_place_mention.rs#L10-L12`) | **No** | When `-Z mir-preserve-ub` is unset, replaces `StatementKind::PlaceMention(_)` with `Nop`. Under `-Z mir-preserve-ub`, `PlaceMention` survives into `Runtime(PostCleanup)`. | **No** | **No** |
| 3d.3 | `run_runtime_cleanup_passes` | `SimplifyCfg::PreOptimizations` | `compiler/rustc_mir_transform/src/simplify.rs#L48-L104` (`lib.rs#L663`) | `Runtime(PostCleanup)` | **Yes** (`is_enabled: true`) | **No** | **No** | **No** | **Yes**: strips `Nop`s, threads `Goto`s formed by `LowerIntrinsics`, and deletes unreachable blocks (`remove_dead_blocks`). Because `body.phase == MirPhase::Runtime(RuntimePhase::Initial)`, `preserve_switch_reads` (`simplify.rs#L129-L130`) is `true` **only** when `-Z mir-preserve-ub` is set. |
| 3d.4 | `run_runtime_cleanup_passes` | Clear `LocalDecl::local_info` | `compiler/rustc_mir_transform/src/lib.rs#L667-L669` | `Runtime(PostCleanup)` | **Yes** (always) | **No** | **Yes (erasure)**: sets `decl.local_info = ClearCrossCrate::Clear` on all locals. | **No** | **No** |
| 4.1 | `mir_for_ctfe` (CTFE only) | `remap_mir_for_const_eval_select(..., Constness::Const)` | `compiler/rustc_mir_transform/src/lib.rs#L234-L304, #L505` | `Runtime(PostCleanup)` | **Yes** in `mir_for_ctfe` (**not** in `Runtime(PostCleanup)`) | **Yes**: rewrites `Call` to `core::intrinsics::const_eval_select(tupled_args, called_in_const, called_at_rt)` into `called_in_const(tupled_args.0, ...)`. | **No** | **No** | **No** |
| 4.2 | `mir_for_ctfe` (CTFE only) | `CtfeLimit` | `compiler/rustc_mir_transform/src/ctfe_limit.rs#L11-L43` (`lib.rs#L506`) | `Runtime(PostCleanup)` | **Yes** in `mir_for_ctfe` | **No** | **Yes**: inserts `StatementKind::ConstEvalCounter` before calls and loop back-edges. | **No** | **No** |
| 5.0 | `inner_optimized_mir` (not captured) | `remap_mir_for_const_eval_select(..., Constness::NotConst)` | `compiler/rustc_mir_transform/src/lib.rs#L234-L304, #L807` | `Runtime(PostCleanup)` | **Yes** in `optimized_mir` (**not** in `Runtime(PostCleanup)`) | **Yes**: rewrites `Call` to `core::intrinsics::const_eval_select(tupled_args, called_in_const, called_at_rt)` into `called_at_rt(tupled_args.0, ...)`. | **No** | **No** | **No** |
| 5.1 | `run_optimization_passes` (not captured) | `CheckAlignment` | `compiler/rustc_mir_transform/src/check_alignment.rs#L12-L147` (`lib.rs#L692`) | `Runtime(PostCleanup)` | **Yes** in `optimized_mir` iff `sess.ub_checks()` and `LangItem::PanicImpl` exists | **No** | **Yes**: inserts `PtrToPtr`, `Transmute` (`*const () as usize`), and alignment mask locals before indirect raw-pointer accesses (`*ptr`). | **Yes**: splits blocks and inserts `TerminatorKind::Assert { msg: AssertKind::MisalignedPointerDereference { required, found }, unwind: UnwindAction::Unreachable }`. | **No** |
| 5.2 | `run_optimization_passes` (not captured) | `CheckNull` | `compiler/rustc_mir_transform/src/check_null.rs#L10-L127` (`lib.rs#L693`) | `Runtime(PostCleanup)` | **Yes** in `optimized_mir` iff `sess.ub_checks()` and `LangItem::PanicImpl` exists | **No** | **Yes**: inserts `PtrToPtr`, `Transmute` (`*const () as usize`), and zero-check locals before indirect raw-pointer accesses (`*ptr`). | **Yes**: splits blocks and inserts `TerminatorKind::Assert { msg: AssertKind::NullPointerDereference, unwind: UnwindAction::Unreachable }`. | **No** |
| 5.3 | `run_optimization_passes` (not captured) | `CheckEnums` | `compiler/rustc_mir_transform/src/check_enums.rs#L15-L114` (`lib.rs#L694`) | `Runtime(PostCleanup)` | **Yes** in `optimized_mir` iff `sess.ub_checks()` | **No** | **Yes**: inserts discriminant load and validity check locals. | **Yes**: splits blocks and inserts `TerminatorKind::Assert { msg: AssertKind::InvalidEnumConstruction(discr), unwind: UnwindAction::Unreachable }`. | **No** |

#### 1.4 Exact Scope of `-Z mir-preserve-ub` and Absence of `CheckAlignment` in `Runtime(PostCleanup)`

1. **`-Z mir-preserve-ub` in `Runtime(PostCleanup)`**:
   Across the entire pipeline up to `mir_drops_elaborated_and_const_checked`,
   `sess.opts.unstable_opts.mir_preserve_ub` is consulted in only two places:
   - `RemovePlaceMention::is_enabled` (`remove_place_mention.rs#L10-L12`)
     evaluates `!sess.opts.unstable_opts.mir_preserve_ub`, so
     `-Z mir-preserve-ub` preserves `StatementKind::PlaceMention(_)`.
   - `SimplifyCfg::preserve_switch_reads` (`simplify.rs#L129-L130`) evaluates
     `body.phase < MirPhase::Runtime(RuntimePhase::Initial) ||
     tcx.sess.opts.unstable_opts.mir_preserve_ub`. The first four `SimplifyCfg`
     invocations (`Initial`, `PromoteConsts`, `PostAnalysis`,
     `RemoveFalseEdges`) run while `body.phase < Runtime(Initial)`, so they
     preserve `SwitchInt` reads regardless. The fifth invocation,
     `SimplifyCfg::PreOptimizations` (`lib.rs#L663`), runs when `body.phase ==
     MirPhase::Runtime(RuntimePhase::Initial)`. Without `-Z mir-preserve-ub`,
     `SimplifyCfg::simplify_Read_only_SwitchInt` (`simplify.rs#L202-L209`)
     folds any `SwitchInt(discr)` whose targets are all identical into
     `TerminatorKind::Goto`, erasing the read of `discr`. With
     `-Z mir-preserve-ub`, it rewrites the targets to
     `[0: target, otherwise: target]` (`simplify.rs#L210-L216`), preserving the
     discriminant read.
2. **Why `CheckAlignment`, `CheckNull`, and `CheckEnums` never appear in
   `Runtime(PostCleanup)`**:
   `CheckAlignment`, `CheckNull`, and `CheckEnums` are registered at the start
   of `run_optimization_passes` (`lib.rs#L692-L694`), which runs only inside
   `inner_optimized_mir` (`optimized_mir`). They never run in
   `mir_drops_elaborated_and_const_checked` (`Runtime(PostCleanup)`). Moreover,
   in `optimized_mir`, `CheckAlignment` and `CheckNull` call `check_pointers`
   (`compiler/rustc_mir_transform/src/check_pointers.rs#L43-L64`), which begins
   with:
   ```rust
   if tcx.lang_items().get(LangItem::PanicImpl).is_none() {
       return;
   }
   ```
   In any `#![no_std]` library crate compiled with `--crate-type=lib` or
   `--crate-type=rlib` without a `#[panic_handler]` definition,
   `LangItem::PanicImpl` is `None`, so `CheckAlignment` and `CheckNull` return
   immediately without inserting any checks even in `optimized_mir`.
   Consequently, any verifier operating on `Runtime(PostCleanup)` MIR must
   enforce alignment and non-nullness directly in its place-dereference
   semantics (`ProjectionElem::Deref`) rather than relying on compiler-inserted
   `CheckAlignment` or `CheckNull` assertions.

---

### 2. Lowering and Folding of Layout Queries, `offset_of!`, and Target Constants Across MIR Stages

Basis: `source`, `execution`, `derived`

#### 2.1 Removal of `NullaryOp` and Lowering of `size_of`, `align_of`, `size_of_val`, `align_of_val`, and `offset_of!`

In both `1.98.0-nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`) and
`1.101.0-nightly` (`5c543b0b8c73c7b72bc8284ced4fb22ead15734d`), `NullaryOp`
(`SizeOf`, `AlignOf`, `OffsetOf`, `UbChecks`) no longer exists on
`mir::Rvalue` (`compiler/rustc_middle/src/mir/syntax.rs#L1363-L1488`). Instead:

1. **`core::mem::size_of` and `core::mem::align_of`**
   (`library/core/src/mem/mod.rs#L373-L375, #L528-L530, #L1372-L1410`):
   Defined as ordinary `const fn`s returning the lang-item associated constants
   `<T as SizedTypeProperties>::SIZE` (`#[lang = "mem_size_const"]`) and
   `<T as SizedTypeProperties>::ALIGN` (`#[lang = "mem_align_const"]`), whose
   bodies call the intrinsics `core::intrinsics::size_of::<Self>()` and
   `core::intrinsics::align_of::<Self>()`
   (`library/core/src/intrinsics/mod.rs#L2042-L2049`).
2. **`core::mem::size_of_val` and `core::mem::align_of_val`**
   (`library/core/src/mem/mod.rs#L401-L404, #L548-L551`):
   Defined as `const fn`s calling `core::intrinsics::size_of_val(val)` and
   `core::intrinsics::align_of_val(val)`.
3. **`core::mem::offset_of!($Container, $($fields)+)`**
   (`library/core/src/mem/mod.rs#L1575-L1578`):
   Expands to `const { builtin # offset_of($Container, $($fields)+) }`. In the
   enclosing function, the `const { ... }` block lowers to
   `mir::Const::Unevaluated(UnevaluatedConst { def: fn::{constant#k}, args,
   promoted: None }, usize)` in both `basic_blocks` and `required_consts`.
   Inside `fn::{constant#k}`, `hir::ExprKind::OffsetOf(container, fields)`
   lowers during THIR construction
   (`compiler/rustc_mir_build/src/thir/cx/expr.rs#L792-L839`) into calls to
   `LangItem::OffsetOf` (`core::intrinsics::offset_of::<Container>(variant_u32,
   field_u32) -> usize`, `library/core/src/intrinsics/mod.rs#L2066`) chained
   with `BinOp::Add` (`AddWithOverflow` in MIR) for nested field paths.

#### 2.2 Stage-by-Stage MIR Representation Matrix

Executing [`support/driver_probe.rs`](support/driver_probe.rs) on
[`support/probe_inputs.rs`](support/probe_inputs.rs) produces
[`support/probe_198_opt0.txt`](support/probe_198_opt0.txt)
(`-Z mir-opt-level=0 -Z mir-preserve-ub`),
[`support/probe_198_opt2.txt`](support/probe_198_opt2.txt)
(`-Z mir-opt-level=2`), and
[`support/probe_198_opt2_O2.txt`](support/probe_198_opt2_O2.txt)
(`-Z mir-opt-level=2 -C opt-level=2`). All `Runtime(PostCleanup)` outputs are
identical between `1.98.0-nightly` and `1.101.0-nightly`:

| Construct | `mir_built` & `mir_promoted` | `Runtime(PostCleanup)` (`mir_drops_elaborated_and_const_checked`) & `mir_for_ctfe` | `optimized_mir` (`-Z mir-opt-level=0 -Z mir-preserve-ub`) | `optimized_mir` (`-Z mir-opt-level=2`, `-C opt-level=0`) | `optimized_mir` (`-Z mir-opt-level=2 -C opt-level=2`) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `size_of::<ReprRustStruct>()` / `align_of::<ReprRustStruct>()` | `TerminatorKind::Call(FnDef(core::mem::size_of / align_of, [ReprRustStruct]))`; `required_consts = []` | Same `TerminatorKind::Call`; `required_consts = []` | Same `TerminatorKind::Call`; `required_consts = []` | Same `TerminatorKind::Call` (`Inline` disabled when `OptLevel < More`) | `Inline` inlines `size_of`/`align_of` (adding `SizedTypeProperties::{SIZE, ALIGN}` to `required_consts`), then `GVN` folds to `Const::Val(8_usize / 4_usize)` |
| `size_of::<T>()` / `align_of::<T>()` | `TerminatorKind::Call(FnDef(core::mem::size_of / align_of, [T/#0]))`; `required_consts = []` | Same `TerminatorKind::Call`; `required_consts = []` | Same `TerminatorKind::Call`; `required_consts = []` | Same `TerminatorKind::Call` | `Inline` inlines `size_of`/`align_of`, leaving `Const::Unevaluated(SizedTypeProperties::{SIZE, ALIGN}, args=[T/#0])` in `bb0` and `required_consts` |
| `size_of_val(v)` / `align_of_val(v)` (`v: &ReprRustStruct`) | `TerminatorKind::Call(FnDef(core::mem::size_of_val / align_of_val, [ReprRustStruct]))`; `required_consts = []` | Same `TerminatorKind::Call`; `required_consts = []` | Same `TerminatorKind::Call`; `required_consts = []` | Same `TerminatorKind::Call` | `Inline` exposes `intrinsics::size_of_val / align_of_val`; `InstSimplify` (`instsimplify.rs#L275-L321`) rewrites to `Const::Unevaluated(SizedTypeProperties::{SIZE, ALIGN})` without updating `required_consts`; `GVN` folds to `8_usize` / `4_usize` |
| `size_of_val(v)` / `align_of_val(v)` (`v: &T`, `T: Sized`) | `TerminatorKind::Call(FnDef(core::mem::size_of_val / align_of_val, [T/#0]))`; `required_consts = []` | Same `TerminatorKind::Call`; `required_consts = []` | Same `TerminatorKind::Call`; `required_consts = []` | Same `TerminatorKind::Call` | `Inline` + `InstSimplify` rewrites to `Const::Unevaluated(SizedTypeProperties::{SIZE, ALIGN}, args=[T/#0])` in `bb0` while `required_consts` remains `[]` |
| `size_of_val(v)` / `align_of_val(v)` (`v: &[ReprRustStruct]`) | `TerminatorKind::Call(FnDef(core::mem::size_of_val / align_of_val, [[ReprRustStruct]]))`; `required_consts = []` | Same `TerminatorKind::Call`; `required_consts = []` | Same `TerminatorKind::Call`; `required_consts = []` | Same `TerminatorKind::Call` | `size_of_val` remains `Call(intrinsics::size_of_val)`; `align_of_val` simplifies via `InstSimplify` (`ty::Slice(elem)`) + `GVN` to `const 4_usize` |
| `offset_of!(ReprRustStruct, b)` / `offset_of!(ReprCStruct, b)` / `offset_of!(NestedRust, inner.b)` | Outer fn: `Assign(_d = Use(Constant(Const::Unevaluated(fn::{constant#k}, ty=usize))))` in `bb0` + `required_consts`. Inner `{constant#k}`: `Call(core::intrinsics::offset_of::<Container>(0_u32, idx_u32))` (+ `AddWithOverflow` for nested fields) | Identical to `mir_promoted` | Identical to `Runtime(PostCleanup)` | `GVN` evaluates `Const::Unevaluated` via CTFE and folds outer `bb0` to `const 0_usize` (`ReprRustStruct.b` reordered before `a`), `const 4_usize` (`ReprCStruct.b`), and `const 0_usize` (`NestedRust.inner.b`) | Identical to `-Z mir-opt-level=2` |
| `offset_of!(Wrapper<T>, field)` (generic) | Outer fn: `Assign(_d = Use(Constant(Const::Unevaluated(fn::{constant#0}, args=[T/#0, usize], ty=usize))))` in `bb0` + `required_consts`. Inner `{constant#0}`: `Call(intrinsics::offset_of::<Wrapper<T>>(0_u32, 1_u32))` | Identical to `mir_promoted` | Identical to `Runtime(PostCleanup)` | Outer `bb0` retains `Const::Unevaluated(fn::{constant#0}, args=[T/#0, usize])` (cannot CTFE-fold polymorphic `T`) | Identical to `-Z mir-opt-level=2` |
| `usize::BITS` & `usize::MAX` | `Assign(_d = Use(Constant(Const::Unevaluated(core::num::<impl usize>::BITS / MAX))))` in `bb0` + `required_consts` | Identical (`Const::Unevaluated` in `bb0` and `required_consts`) | Identical (`Const::Unevaluated` in `bb0` and `required_consts`) | `GVN` folds `bb0` to `const 64_u32` and `const usize::MAX`; `required_consts` retains `BITS` and `MAX` | Identical to `-Z mir-opt-level=2` |
| `cfg!(target_pointer_width = "64")` | Macro-expanded before HIR/THIR to literal `true`: `Assign(_d = Use(Constant(Const::Val(Scalar(0x01), bool))))`; `is_required_const = false` | Identical (`Const::Val(Scalar(0x01), bool)`) | Identical (`Const::Val(Scalar(0x01), bool)`) | Identical (`const true`) | Identical (`const true`) |

#### 2.3 Tracing Runtime `size_of::<ReprRustStruct>()` versus `const { assert!(size_of::<ReprRustStruct>() == 8) }`

1. **Runtime call `let s = core::mem::size_of::<ReprRustStruct>();`**
   ([`support/probe_198_opt0.txt`](support/probe_198_opt0.txt)):
   - In `Runtime(PostCleanup)`, `bb0` contains
     `TerminatorKind::Call(func = Const::Val(ZeroSized, FnDef(core::mem::size_of, [ReprRustStruct])), args = [], dest = _1, target = Some(bb1))`
     and `required_consts = []`.
   - A `Runtime(PostCleanup)` MIR extractor that recognizes `core::mem::size_of`
     can lower this `Call` directly to a dedicated size-query terminator over
     the type argument `ReprRustStruct`, which the verifier's operational
     semantics evaluates against its layout model (failing closed if the type's
     layout is not guaranteed).
2. **Compile-time assertion `const { assert!(core::mem::size_of::<ReprRustStruct>() == 8); }`**
   ([`support/probe_198_opt0.txt`](support/probe_198_opt0.txt)):
   - The outer function's `Runtime(PostCleanup)` body has
     `required_consts = [Const::Unevaluated(def = fn::{constant#0}, args = [()], ty = ())]`
     and `bb0` statement
     `Assign(_0 = Use(Constant(Const::Unevaluated(def = fn::{constant#0}, args = [()], ty = ()))))`.
   - Inside `fn::{constant#0}`, both `Runtime(PostCleanup)` and `mir_for_ctfe`
     contain `bb0: Call(core::mem::size_of::<ReprRustStruct>()) -> bb1`,
     `bb1: _1 = Eq(move _2, const 8_usize); switchInt(move _1) -> [0: bb2, otherwise: bb3]`,
     because `run_optimization_passes` (`compiler/rustc_mir_transform/src/lib.rs#L604-L608`)
     returns early for `Const`/`InlineConst`/`AnonConst` items without running
     `Inline`, `InstSimplify`, or `GVN`.
   - When `rustc` evaluates `fn::{constant#0}` during monomorphization
     (`compiler/rustc_monomorphize/src/collector.rs#L1349`), CTFE (`InterpCx`)
     steps through `core::mem::size_of` → `<ReprRustStruct as SizedTypeProperties>::SIZE`
     → `core::intrinsics::size_of::<ReprRustStruct>()`, where
     `InterpCx::eval_intrinsic` (`compiler/rustc_const_eval/src/interpret/intrinsics.rs#L212-L216`)
     calls `this.layout_of(tp_ty)?` and returns `layout.size.bytes()` (`8`).
   - By contrast, when a verifier captures `fn::{constant#0}`'s own
     `Runtime(PostCleanup)` MIR body rather than calling `rustc` CTFE, the
     inline `const` body retains the uninlined `Call(core::mem::size_of)`
     terminator and evaluates it under the verifier's layout semantics.

#### 2.4 Five Pathways for Premature Layout Folding

An unguaranteed `repr(Rust)` layout choice (`size_of`, `align_of`, `offset_of!`,
or enum niche/discriminant size) can fold into a concrete integer literal before
or during `Runtime(PostCleanup)` MIR extraction through five distinct pathways:

1. **Pathway 1 (Active in `Runtime(PostCleanup)`): Type-system `ty::Const`
   evaluation in repeat counts (`[val; N]`), array lengths (`[T; N]`), and const
   generics (`Foo<{ N }>`)**:
   - In `q2_1_layout_folding_pathways`
     ([`support/probe_inputs.rs`](support/probe_inputs.rs),
     [`support/probe_198_opt0.txt`](support/probe_198_opt0.txt)), writing
     `let arr = [0u8; core::mem::size_of::<ReprRustStruct>()];` creates a
     `DefKind::AnonConst` (`RepeatExprCount`) for the repeat count. During type
     checking and THIR-to-MIR lowering
     (`compiler/rustc_mir_build/src/builder/expr/as_rvalue.rs#L64-L78`), `rustc`
     evaluates the `ty::Const` via CTFE (`tcx.const_eval_resolve_for_typeck`),
     turning it into `ty::ConstKind::Value(8_usize)` before `mir_built`
     completes:
     ```text
     stmt[3]: Assign(_2 = Repeat(Constant(Const::Val(val=Scalar(0x00), ty=u8)), count=8_usize))
     ```
   - Any MIR extractor that reads `ty::Array(_, len)` or `Rvalue::Repeat(_, c)`
     from `ty::ConstKind::Value` observes only the concrete integer `8` without
     any record in the parent body's MIR that `8` came from
     `size_of::<ReprRustStruct>()`. To prevent unguaranteed layout folding via
     repeat counts or array lengths, an extractor must either reject type-system
     `DefKind::AnonConst` body owners in `tcx.hir_body_owners()` or inspect
     their unoptimized HIR/MIR bodies before admitting the constant.
   - **Forward-compatibility requirement in `1.101.0-nightly`**: Between
     `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` and
     `5c543b0b8c73c7b72bc8284ced4fb22ead15734d`, `compiler/rustc_hir/src/def.rs`
     removed `DefKind::InlineConst` and merged it into `DefKind::AnonConst`. In
     `1.101.0-nightly`, inline `const { ... }` blocks have
     `tcx.def_kind(def_id) == DefKind::AnonConst` with
     `tcx.anon_const_kind(def_id) == rustc_middle::ty::AnonConstKind::NonTypeSystemInline`.
     Any extractor that previously matched `DefKind::InlineConst` (both to admit
     inline `const { ... }` body owners and to strip their synthetic trailing
     return-type generic argument via `args.pop()`) must, on `1.101.0-nightly`,
     match `DefKind::AnonConst` gated on
     `tcx.anon_const_kind(def_id) == ty::AnonConstKind::NonTypeSystemInline`
     while continuing to reject type-system `AnonConst` kinds
     (`RepeatExprCount`, `NonTypeSystemAnon`, `GCE`, `MCG`).
2. **Pathway 2 (Single-field `repr(Rust)` struct layout assumption)**:
   - In `compiler/rustc_abi/src/layout.rs#L1283-L1320`, `rustc`'s `univariant`
     layout algorithm places the sole field of a single-field `repr(Rust)`
     struct at offset `0` and rounds the struct size up to the struct's
     alignment (which equals the field's alignment when no `#[repr(align)]` is
     present). However, The Rust Reference (`type-layout.html`, "The `Rust`
     Representation") makes no layout guarantee for `repr(Rust)` structs without
     `#[repr(transparent)]` or `#[repr(C)]`. Any verification semantics that
     equates a single-field `repr(Rust)` struct's size with its field's size is
     therefore encoding a compiler-specific property of `rustc_abi` rather than
     a normative Rust Reference guarantee.
3. **Pathway 3 (Evaluating `mir::Const::Unevaluated` via `tcx.const_eval_resolve`
   during extraction)**:
   - At `Runtime(PostCleanup)`, `offset_of!(ReprRustStruct, b)`, value-producing
     `const { size_of::<ReprRustStruct>() }`, named `const` items, and
     `<ReprRustStruct as SizedTypeProperties>::{SIZE, ALIGN}` are represented as
     `mir::Const::Unevaluated(uv, usize)`.
   - If a MIR extractor were to evaluate `Const::Unevaluated` by calling
     `tcx.const_eval_resolve(TypingEnv::fully_monomorphized(), uv, span)`,
     `rustc` CTFE (`compiler/rustc_const_eval/src/interpret/intrinsics.rs#L212-L243`)
     would invoke `this.layout_of(tp_ty)` and fold `offset_of!(ReprRustStruct, b)`
     to `0_usize` and `size_of::<ReprRustStruct>()` to `8_usize`, erasing their
     dependence on `repr(Rust)` layout. Instead, an extractor must capture the
     constant's `Runtime(PostCleanup)` MIR body and evaluate it under the
     verifier's own semantics, where `core::intrinsics::offset_of` only succeeds
     on containers with guaranteed layouts (such as `#[repr(C)]` or
     `#[repr(transparent)]`) and fails closed on `repr(Rust)` types.
4. **Pathway 4 (Reading `optimized_mir` at `-Z mir-opt-level >= 1`)**:
   - In [`support/probe_198_opt2.txt`](support/probe_198_opt2.txt) and
     [`support/probe_198_opt2_O2.txt`](support/probe_198_opt2_O2.txt), `GVN`
     (at `-Z mir-opt-level=2`) folds `offset_of!(ReprRustStruct, b)` to
     `const 0_usize` (because `rustc` reordered the 4-byte-aligned `b: u32`
     ahead of `a: u8`) and `NAMED_RUST_SIZE` to `const 8_usize`, while `Inline`
     + `InstSimplify` + `GVN` (at `-Z mir-opt-level=2 -C opt-level=2`) folds
     runtime calls to `size_of`, `align_of`, `size_of_val`, and `align_of_val`
     on `ReprRustStruct` into `(8_usize, 4_usize)`. Capturing
     `mir_drops_elaborated_and_const_checked` (`Runtime(PostCleanup)`) with
     `-Z mir-opt-level=0` avoids all `Runtime(Optimized)` folding passes.
5. **Pathway 5 (`cfg!` macro expansion before HIR/THIR)**:
   - Unlike `usize::BITS` and `usize::MAX` (which remain
     `Const::Unevaluated(core::num::<impl usize>::BITS / MAX)` in
     `Runtime(PostCleanup)`), `cfg!(target_pointer_width = "64")` is expanded
     during AST macro expansion into a boolean literal `true`
     (`Const::Val(Scalar(0x01), bool)` with `is_required_const = false`),
     indistinguishable from a source-written `true` by the time HIR or MIR is
     built.

---

### 3. Inline `const { ... }` and Associated Constant Placement in `Body.basic_blocks` versus `Body.required_consts`

Basis: `normative`, `source`, `execution`, `derived`

#### 3.1 How `rustc_mir_build`, `SimplifyCfg::Initial`, and `RequiredConstsVisitor` Populate `basic_blocks` and `required_consts`

1. **THIR-to-MIR lowering (`compiler/rustc_mir_build/src/builder/expr/as_constant.rs#L72-L108`)**:
   Both `ExprKind::NamedConst { def_id, args, user_ty }` (e.g., `S::<T>::OK`,
   `usize::MAX`) and `ExprKind::ConstBlock { did: def_id, args }` (e.g.,
   `const { ... }`) lower to `ConstOperand { span, user_ty, const_:
   Const::Unevaluated(UnevaluatedConst::new(def_id, args), ty) }`. In
   `as_rvalue.rs` / `stmt.rs`:
   - Statement `const { assert!(...); };` lowers to `Assign(_t =
     Use(Constant(ConstOperand)))` on a fresh unit temporary `_t: ()`.
   - Wildcard binding `let _ = S::<T>::OK;` lowers via `as_place` to
     `Assign(_t = Use(Constant(ConstOperand)))` followed by
     `StatementKind::PlaceMention(_t)` (preserved in `Runtime(PostCleanup)` by
     `-Z mir-preserve-ub`).
   - Variable binding `let x = const { ... };` lowers to
     `Assign(_x = Use(Constant(ConstOperand)))` followed by
     `StatementKind::FakeRead(ForLet(None), _x)` (stripped by
     `CleanupPostBorrowck` before `Runtime(PostCleanup)`).
2. **`SimplifyCfg::Initial` in `mir_built` (`compiler/rustc_mir_transform/src/lib.rs#L411`)**:
   Calls `remove_dead_blocks(body)` (`simplify.rs#L84, #L349-L413`), which
   deletes any basic block with zero predecessors in the CFG from `bb0`.
   - For post-`return` constants (`return; const { ... };` or
     `return; let _ = S::<T>::OK;`), the block following `return;` has no
     predecessors and is deleted during `mir_built` before `mir_promoted` runs.
   - For `if false { const { ... }; }`, `rustc_mir_build` lowers the condition to
     `_1 = const false; switchInt(move _1) -> [0: bb2, otherwise: bb1]`. Because
     `SimplifyCfg` only folds `switchInt(Constant(..))` and does not propagate
     local `_1 = const false` into `switchInt(move _1)` (which requires
     `SimplifyConstCondition` in `optimized_mir`), `bb1` remains a reachable
     CFG successor of `bb0` throughout `mir_built`, `mir_promoted`, and
     `Runtime(PostCleanup)`.
3. **`RequiredConstsVisitor` in `mir_promoted`
   (`compiler/rustc_mir_transform/src/required_consts.rs#L1-L32`, `lib.rs#L462`)**:
   Runs in `mir_promoted` before `PromoteTemps`, traversing
   `traversal::reverse_postorder(&body)` and copying every `ConstOperand` where
   `constant.const_.is_required_const()` holds (`Const::Unevaluated(..)` or
   `Const::Ty(_, ty::ConstKind::Unevaluated(_))`,
   `compiler/rustc_middle/src/mir/consts.rs#L204-L210`) into
   `body.required_consts` **without removing or altering the `Assign` statement
   in `body.basic_blocks`**.

#### 3.2 Empirical Placement Matrix Across Live, `if false`, and Post-`return` Control Flow

The table below summarizes the exact `Body.basic_blocks` and
`Body.required_consts` contents observed in
[`support/probe_198_opt0.txt`](support/probe_198_opt0.txt) and
[`support/probe_198_opt2.txt`](support/probe_198_opt2.txt) across both
`1.98.0-nightly` and `1.101.0-nightly`:

| Construct in [`support/probe_inputs.rs`](support/probe_inputs.rs) | In `Body.basic_blocks` at `mir_built` & `mir_promoted`? | In `Body.basic_blocks` at `Runtime(PostCleanup)` (`mir_drops_elaborated_and_const_checked`)? | In `Body.required_consts` at `mir_promoted`, `Runtime(PostCleanup)`, & `optimized_mir`? | In `Body.basic_blocks` at `optimized_mir` (`-Z mir-opt-level=2`)? |
| :--- | :--- | :--- | :--- | :--- |
| **Value `let x: usize = const { 1 + 2 };`** (`q2_2a_value_const_block`) | **Yes** (`bb0`: `Assign(_1 = Use(Constant(Const::Unevaluated({constant#0}, ty=usize))))`) | **Yes** (`bb0`: `Assign(_1 = Use(Constant(Const::Unevaluated({constant#0}, ty=usize))))`) | **Yes** (`len=1`: `[Const::Unevaluated({constant#0}, ty=usize)]`) | Folded by `GVN` to `Assign(_0 = Use(Constant(Const::Val(Scalar(3), usize))))` (remains `Const::Unevaluated` when generic `size_of::<T>() + 1`) |
| **Live statement `const { assert!(size_of::<T>() == 8); };`** (`q2_2b_live_stmt_const_block<T>`) | **Yes** (`bb0`: `Assign(_1 = Use(Constant(Const::Unevaluated({constant#0}, args=[T/#0, ()], ty=()))))`) | **Yes** (`bb0`: `Assign(_1 = Use(Constant(Const::Unevaluated({constant#0}, args=[T/#0, ()], ty=()))))`) | **Yes** (`len=1`: `[Const::Unevaluated({constant#0}, args=[T/#0, ()], ty=())]`) | Stripped from `bb0` (`_1: ()` is a dead ZST), while `required_consts` retains `{constant#0}` |
| **Dead `if false { const { assert!(size_of::<T>() == 8); }; }`** (`q2_2c_if_false_const_block<T>`) | **Yes** (`bb1` reachable from `bb0` `switchInt`: `Assign(_2 = Use(Constant(Const::Unevaluated({constant#0}, args=[T/#0, ()], ty=()))))`) | **Yes** (`bb1`: `Assign(_2 = Use(Constant(Const::Unevaluated({constant#0}, args=[T/#0, ()], ty=()))))`) | **Yes** (`len=1`: `[Const::Unevaluated({constant#0}, args=[T/#0, ()], ty=())]`) | `SimplifyConstCondition` + `SimplifyCfg` deletes `bb1`, leaving `bb0: return`, while `required_consts` retains `{constant#0}` |
| **Post-`return` `return; const { assert!(size_of::<T>() == 8); };`** (`q2_2d_post_return_const_block<T>`) | **No** (unreachable `bb1` deleted by `SimplifyCfg::Initial` in `mir_built`) | **No** (`bb0` has only `return`) | **No** (`len=0`: `required_consts = []`; `{constant#0}` remains an unreferenced body owner in `tcx.hir_body_owners()`) | **No** (`bb0: return`, `required_consts = []`) |
| **Live `let _ = S::<T>::OK;`** (`q2_2e_named_assoc_const_live<T>`) | **Yes** (`bb0`: `Assign(_1 = Use(Constant(Const::Unevaluated(S::<T>::OK, args=[T/#0], ty=()))))` + `PlaceMention(_1)`) | **Yes** (`bb0`: `Assign(_1 = Use(Constant(Const::Unevaluated(S::<T>::OK, args=[T/#0], ty=()))))` + `PlaceMention(_1)`) | **Yes** (`len=1`: `[Const::Unevaluated(S::<T>::OK, args=[T/#0], ty=())]`) | Stripped from `bb0`, while `required_consts` retains `S::<T>::OK` |
| **Dead `if false { let _ = S::<T>::OK; }`** (`q2_2e_named_assoc_const_if_false<T>` & `..._value_bind_dead<T>`) | **Yes** (`bb1`: `Assign(_2 = Use(Constant(Const::Unevaluated(S::<T>::OK, args=[T/#0], ty=()))))` + `PlaceMention(_2)` / `FakeRead`) | **Yes** (`bb1`: `Assign(_2 = Use(Constant(Const::Unevaluated(S::<T>::OK, args=[T/#0], ty=()))))` + `PlaceMention(_2)`) | **Yes** (`len=1`: `[Const::Unevaluated(S::<T>::OK, args=[T/#0], ty=())]`) | `bb1` deleted by `SimplifyConstCondition`, while `required_consts` retains `S::<T>::OK` |
| **Post-`return` `return; let _ = S::<T>::OK;`** (`q2_2e_named_assoc_const_post_return<T>`) | **No** (deleted by `SimplifyCfg::Initial` in `mir_built`) | **No** (`bb0: return`) | **No** (`len=0`: `required_consts = []`) | **No** (`bb0: return`, `required_consts = []`) |

#### 3.3 Normative Reference Rules (`r[expr.block.const]`) versus Upfront `required_consts` and Trace-Reached `basic_blocks` Semantics

In The Rust Reference (`82da570bafd9efed421bdbae0f8603ede8dd308b`,
`expressions/block-expr.html#L735-L790`):

- **`r[expr.block.const.evaluation]`**: *"If the const block expression is
  executed at runtime, then the constant is guaranteed to be evaluated, even if
  its return value is ignored."*
- **`r[expr.block.const.not-executed]`**: *"If the const block expression is not
  executed at runtime, it may or may not be evaluated:
  `if false { const { panic!(); } }`"*

Comparing an upfront `body.required_consts` admission model (where every entry
in `body.required_consts` and every constant required by a syntactically
referenced callee is assumed to succeed at function entry, while unit-typed
`Const::Unevaluated(_, ())` operands in `basic_blocks` are erased to `()`)
against trace-reached `basic_blocks` evaluation reveals three structural
differences:

1. **Reliance on `RequiredConstsVisitor` and `MentionedItems` for unexecuted
   branches**:
   Under an upfront `body.required_consts` model, a function-entry precondition
   assumes that every constant in `body.required_consts` (and in any callee
   referenced in `body.basic_blocks`) evaluates without panicking, even if the
   `const` block or callee call site sits inside an unreached `if false` branch.
   The Rust Reference (`r[expr.block.const.not-executed]`) does not guarantee
   that unexecuted `const` blocks are evaluated; in `rustc`, dead-branch
   evaluation holds only when `SimplifyCfg::Initial` has not deleted the block
   before `RequiredConstsVisitor` (`required_consts.rs#L1-L32`) and
   `MentionedItems` (`compiler/rustc_mir_transform/src/mentioned_items.rs#L1-L120`,
   propagated by `Inline` at `inline.rs#L1030-L1052` and visited by
   `rustc_monomorphize::collector::collect_items_of_instance` at
   `collector.rs#L1347-L1361`) run, and when the enclosing function is actually
   collected as a monomorphization root (note that in `--crate-type=lib` builds
   at `-C opt-level=2`, `reachable_non_generics_provider` at
   `compiler/rustc_codegen_ssa/src/back/symbol_export.rs#L97` omits
   `cross_crate_inlinable` non-generic functions from local `.rlib` roots).
2. **Trace-reached `basic_blocks` evaluation is Reference-sound under
   `r[expr.block.const.evaluation]`**:
   Because `Runtime(PostCleanup)` retains `Assign(dst =
   Use(Constant(Const::Unevaluated(uv, ty))))` at the exact statement where the
   constant expression is evaluated, preserving `Const::Unevaluated` in
   `basic_blocks` as a symbolic constant reference (`(const_def_id, type_args)`)
   and evaluating it when control flow reaches that `Assign` statement relies
   solely on `r[expr.block.const.evaluation]`. An unexecuted
   `if false { const { ... } }` branch is never reached along the runtime trace
   and therefore cannot be used to discharge verification obligations on the
   live path.
3. **Unified treatment of unit-typed PME assertions and value-producing
   constants**:
   Erasing `Const::Unevaluated(_, ())` in `basic_blocks` to a unit literal `()`
   prevents `basic_blocks` from naming which constant produces a non-`()` value
   (`let x: usize = const { ... }`, `offset_of!`, `usize::BITS`, `usize::MAX`).
   Evaluating `Const::Unevaluated` at its `Assign` statement in `basic_blocks`
   handles both unit-typed PME assertions and value-producing constants with a
   single mechanism.

---

### 4. `assert_unsafe_precondition!`, `Operand::RuntimeChecks`, Unlowered `const_eval_select`, and `TerminatorKind::Assert` Unwind Actions

Basis: `source`, `execution`, `derived`

#### 4.1 `Operand::RuntimeChecks` Lowering and Unreachable `ContractChecks`

In `compiler/rustc_middle/src/mir/syntax.rs#L1331-L1336, #L1579-L1600`,
`Operand::RuntimeChecks(RuntimeChecks)` has three variants (`UbChecks`,
`ContractChecks`, `OverflowChecks`), created by `LowerIntrinsics`
(`compiler/rustc_mir_transform/src/lower_intrinsics.rs#L26-L43`) when lowering
calls to `core::intrinsics::{ub_checks, contract_checks, overflow_checks}()`:

- **Why `Operand::RuntimeChecks` remains unresolved in `Runtime(PostCleanup)`**:
  Precompiled sysroot crates (`core`, `alloc`, `std`) are built with
  `ub_checks = false` and `overflow_checks = false`, but carry
  `#![rustc_preserve_ub_checks]` and `#[rustc_inherit_overflow_checks]`. Keeping
  `Operand::RuntimeChecks` unresolved in `Runtime(PostCleanup)` allows generic
  and `#[inline]` functions in `libcore.rlib` to defer resolving
  `RuntimeChecks::value(sess)` until `InstSimplify` (`SimplifyUbCheck`,
  `instsimplify.rs#L452-L473`, which requires `mir-opt-level >= 1`) or codegen
  (`rustc_codegen_ssa/src/mir/operand.rs#L1057`) runs in the downstream user
  crate. In CTFE (`compiler/rustc_const_eval/src/const_eval/machine.rs#L781-L788`),
  `CompileTimeMachine::runtime_checks` unconditionally returns `interp_ok(true)`.
- **Why `RuntimeChecks::ContractChecks` is unreachable in `1.98.0-nightly` and
  `1.101.0-nightly`**: Although `mir::RuntimeChecks::ContractChecks` and its
  `LowerIntrinsics` arm exist, `sym::contract_checks` is missing from
  `check_intrinsic_type`
  (`compiler/rustc_hir_analysis/src/check/intrinsic.rs#L697`), causing `E0093:
  unrecognized intrinsic function: contract_checks` if declared, while
  `#[requires]`/`#[ensures]` AST lowering
  (`compiler/rustc_ast_lowering/src/contract.rs#L186, #L226, #L341`) emits a
  compile-time boolean literal `self.tcx.sess.contract_checks()`.

#### 4.2 `assert_unsafe_precondition!`, `check_language_ub`, and Unlowered `const_eval_select` in `library/core`

In `library/core/src/ub_checks.rs#L52-L108`, `assert_unsafe_precondition!($kind,
$message, (...) => $e)` defines a local `#[rustc_no_mir_inline] #[inline]
#[rustc_nounwind] const fn precondition_check(...)` that calls
`core::panicking::panic_nounwind_fmt` if `!$e`, guarded by
`if ::core::ub_checks::$kind() { precondition_check(...); }`:

- When `$kind` is `check_library_ub` (`pub use intrinsics::ub_checks as
  check_library_ub;`, `ub_checks.rs#L88`), `LowerIntrinsics` lowers the call in
  the enclosing function's `Runtime(PostCleanup)` body directly to
  `_tmp = UbChecks; switchInt(move _tmp) -> [0: skip, otherwise: call
  precondition_check]`.
- When `$kind` is `check_language_ub` (`ub_checks.rs#L96-L108`), the enclosing
  function's `Runtime(PostCleanup)` body contains a `TerminatorKind::Call` to
  `core::ub_checks::check_language_ub()`. Inside `check_language_ub`'s own
  `Runtime(PostCleanup)` body, `bb0` calls
  `core::intrinsics::const_eval_select((), compiletime, runtime) -> bb1`
  (because `remap_mir_for_const_eval_select` only runs in `mir_for_ctfe` and
  `inner_optimized_mir`), and `bb2` evaluates `_0 = UbChecks`.

Inspecting `library/core` at `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` and
executing [`support/probe_q3_2.rs`](support/probe_q3_2.rs) across all four combinations of
`-C debug-assertions={yes,no}` × `-Z ub-checks={yes,no}`
([`support/probe_results.json`](support/probe_results.json)) establishes the exact
`Runtime(PostCleanup)` and `Runtime(Optimized)` (`-Z mir-opt-level=0`) behavior
for each target function:

| Function | Source Location (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`) | Precondition Guard in `library/core` | `Runtime(PostCleanup)` Body (`dbg={yes,no}, ubc={yes,no}`) | `Runtime(Optimized)` Body at `-Z mir-opt-level=0` (`ubc=yes` vs. `ubc=no`) |
| :--- | :--- | :--- | :--- | :--- |
| `slice::from_raw_parts` | `library/core/src/slice/raw.rs#L124-L141` | Unconditional `assert_unsafe_precondition!(check_language_ub, ...)` (`maybe_is_aligned_and_not_null(data, align, false) && is_valid_allocation_size(size, len)`) | **Invariant (`9 bbs`)**: calls `check_language_ub()`, branches to `precondition_check` or skip, then `_12 = slice_from_raw_parts::<T>(_13, _14); _0 = &(*_12);` | **Identical (`9 bbs`)**: `*const [T]` is unsized, so `check_pointers` skips `*_12` (`check_pointers.rs#L209`) |
| `ptr::read` | `library/core/src/ptr/mod.rs#L1694-L1735` | **`#[cfg(debug_assertions)]`** `assert_unsafe_precondition!(check_language_ub, ...)` *(omitted in precompiled sysroot `core`)* | `dbg=yes`: `8 bbs` (`check_language_ub` + `copy (*_10)`); `dbg=no` (sysroot `core`): **`1 bb`** (`_0 = copy (*_2); return;`) | `ubc=yes, dbg=no`: `3 bbs` (`CheckAlignment` + `CheckNull` + `copy (*_2)`); `ubc=no, dbg=no`: `1 bb` |
| `ptr::write` | `library/core/src/ptr/mod.rs#L1910-L1935` | **`#[cfg(debug_assertions)]`** `assert_unsafe_precondition!(check_language_ub, ...)` *(omitted in precompiled sysroot `core`)* | `dbg=yes`: `10 bbs` (`check_language_ub` + `(*_11) = move _2`); `dbg=no` (sysroot `core`): **`1 bb`** (`(*_3) = move _2; return;`) | `ubc=yes, dbg=no`: `3 bbs` (`CheckAlignment` + `CheckNull` + `(*_3) = move _2`); `ubc=no, dbg=no`: `1 bb` |
| `ptr::copy_nonoverlapping` | `library/core/src/ptr/mod.rs#L530-L552` | Unconditional `assert_unsafe_precondition!(check_language_ub, ...)` (`maybe_is_aligned_and_not_null` on `src`/`dst` + `maybe_is_nonoverlapping`) | **Invariant (`8 bbs`)**: `check_language_ub()` → `precondition_check`, then `StatementKind::Intrinsic(CopyNonOverlapping { src, dst, count })` | **Identical (`8 bbs`)** (`CopyNonOverlapping` has no `ProjectionElem::Deref` place) |
| `NonNull::new_unchecked` | `library/core/src/ptr/non_null.rs#L230-L240` | Unconditional `assert_unsafe_precondition!(check_language_ub, ...)` (`!ptr.is_null()`) | **Invariant (`6 bbs`)**: `check_language_ub()` → `precondition_check`, then `_0 = move _7 as NonNull<T> (Transmute)` | **Identical (`6 bbs`)** |
| `hint::unreachable_unchecked` | `library/core/src/hint.rs#L103-L112` | Unconditional `assert_unsafe_precondition!(check_language_ub, ...)` (`false`) | **Invariant (`6 bbs`)**: `check_language_ub()` → `precondition_check`, then `TerminatorKind::Unreachable` | **Identical (`6 bbs`)** |
| `u32::unchecked_add` | `library/core/src/num/uint_macros.rs#L959-L973` | Unconditional `assert_unsafe_precondition!(check_language_ub, ...)` (`!self.overflowing_add(rhs).1`) | **Invariant (`6 bbs`)**: `check_language_ub()` → `precondition_check`, then `_0 = AddUnchecked(move _8, move _9)` | **Identical (`6 bbs`)** |

#### 4.3 The Dual Soundness Trap of Resolving `RuntimeChecks::UbChecks` to `true` or `false`

In any verification framework that distinguishes Undefined Behavior (a
verification failure state) from a defined panic/unwind (which is permitted by
memory-safety obligations, ignored by normal-return postconditions, and treated
as a Post-Monomorphization Error in `const` blocks), resolving
`Operand::RuntimeChecks(RuntimeChecks::UbChecks)` to a boolean creates a dual
soundness trap:

1. **Trap A: Resolving `UbChecks` to `true` while modeling
   `precondition_check` / `panic_nounwind_fmt` as a defined panic/unwind**:
   - When `UbChecks` is `true` and an `unsafe` precondition is violated (e.g.,
     `hint::unreachable_unchecked()`, `NonNull::new_unchecked(ptr::null_mut())`,
     `u32::MAX.unchecked_add(1)`, or `slice::from_raw_parts(unaligned_ptr, 1)`),
     `precondition_check` calls `core::panicking::panic_nounwind_fmt` and
     diverges before reaching the underlying primitive (`Unreachable`,
     `Transmute`, `AddUnchecked`).
   - If `panic_nounwind_fmt` (or an assertion failure inside
     `precondition_check`) is modeled as a normal panic/unwind rather than
     Undefined Behavior, violating an `unsafe` precondition no longer reaches a
     UB failure state: safety verification succeeds on UB code, normal-return
     postconditions hold vacuously on the diverging path, and `const` blocks
     that trigger language UB are misclassified as benign panicking PMEs.
2. **Trap B: Resolving `UbChecks` to `false` (skipping `precondition_check`)**:
   - When `UbChecks` is `false`, control flow skips `precondition_check` and
     executes the underlying primitive (`Transmute` to `NonNull<T>`,
     `&*slice_from_raw_parts(data, len)`, `CopyNonOverlapping`, etc.).
   - Skipping `precondition_check` is unsound unless the verifier's operational
     semantics for the subsequent primitive independently enforces 100% of the
     language and library UB preconditions—including niche validity
     (`#[rustc_layout_scalar_valid_range_start(1)]`) on `CastKind::Transmute` to
     `NonNull<T>`, non-nullness and alignment of `T` plus
     `size_of::<T>() * len <= isize::MAX` on `&*slice_from_raw_parts(data, len)`
     (even when `len == 0`), non-nullness and alignment on 0-count
     `CopyNonOverlapping`, and library-level safety invariants in
     `check_library_ub` callers (such as `str::from_utf8_unchecked`, where the
     subsequent `Transmute` performs no UTF-8 check at all).
3. **Sound semantics requirement**:
   Either `Operand::RuntimeChecks(UbChecks)` must fail closed when stepping raw
   MIR and calls to `core` functions must be verified against soundness-proved
   function contracts that require the exact safety preconditions, **or**
   stepping through `assert_unsafe_precondition!` must both evaluate `UbChecks`
   (and `check_language_ub()`) to `true` **and** step `panic_nounwind_fmt` (and
   any `Call` or `Assert` failure with `UnwindAction::Unreachable`) to the
   Undefined Behavior failure state, never to a defined panic/unwind.

#### 4.4 `TerminatorKind::Assert` Extraction Under `UnwindAction::Terminate` or `UnwindAction::Unreachable`

When lowering `mir::TerminatorKind::Assert { cond, expected, target, unwind, .. }`,
a MIR extractor must not replace the entire `Assert` terminator with an
unconditional abort/UB terminator when `!matches!(unwind,
mir::UnwindAction::Continue)` and no cleanup block is present:

```rust
// INCORRECT pattern:
mir::TerminatorKind::Assert { cond, expected, target, unwind, .. } => {
    let cleanup = extract_unwind_target(unwind);
    if !matches!(unwind, mir::UnwindAction::Continue) && cleanup.is_none() {
        // Bug: discards `cond`, `expected`, and `target`, failing even when
        // `cond == expected`!
        Ok(Terminator::UnwindTerminate)
    } else {
        Ok(Terminator::Assert { cond, expected: *expected, target, cleanup })
    }
}
```

Whenever a function is compiled with `-C panic=abort`, or inside a
`#[rustc_nounwind]` / `extern "C"` function where `AbortUnwindingCalls`
(`compiler/rustc_mir_transform/src/abort_unwinding_calls.rs#L118-L133`) rewrites
an `Assert` terminator's `unwind` from `UnwindAction::Continue` to
`UnwindAction::Terminate(Reason)` (or when an `Assert` carries
`UnwindAction::Unreachable`), `!matches!(unwind, mir::UnwindAction::Continue) &&
cleanup.is_none()` holds. Replacing the conditional `Assert` with an
unconditional abort/UB terminator causes the basic block to fail even when
`cond == expected` (when the assertion succeeds). In MIR semantics, `unwind` on
`TerminatorKind::Assert` governs only the failure branch (`cond != expected`);
when `cond == expected`, execution always transitions to `target`.

## Boundaries

Basis: `source`, `execution`

1. **Higher optimization levels (`-Z mir-opt-level >= 1`) and LLVM codegen**:
   This report inspects `optimized_mir` only to bound why `Runtime(PostCleanup)`
   under `-Z mir-opt-level=0 -Z mir-preserve-ub` is required to prevent
   premature constant/layout folding and where `CheckAlignment`, `CheckNull`,
   `CheckEnums`, `InstSimplify`, `Inline`, and `GVN` run. It does not catalog
   the full schedule of middle-end optimization passes in
   `run_optimization_passes` beyond the early UB-check and layout-folding
   passes.
2. **Coroutine and async state-machine lowering (`coroutine::StateTransform`)**:
   While `coroutine::StateTransform` is inventoried in the pass pipeline (Step
   3c.10), internal layout and state-machine transitions of coroutines and async
   blocks were not empirically probed.
3. **Stacked Borrows / Tree Borrows pointer provenance**: The preservation of
   `WithRetag::No` by `EraseDerefTemps` (Step 3c.8) and `PlaceMention` by
   `-Z mir-preserve-ub` (Step 3d.2) is documented at the MIR syntax and pass
   level, without modeling a full aliasing operational semantics.

## Evidence

Basis: `normative`, `source`, `execution`

### Normative and Documentation Sources

- **The Rust Reference** (`rust-lang/reference` at
  `82da570bafd9efed421bdbae0f8603ede8dd308b`, bundled with `rustc 1.99.1`):
  - `expressions/block-expr.html#L735-L790`: `r[expr.block.const.eval]`,
    `r[expr.block.const.generic-params]`, `r[expr.block.const.evaluation]`, and
    `r[expr.block.const.not-executed]`.
  - `const_eval.html`: Constant evaluation context rules.

### Primary Source Locations (`rust-lang/rust`)

At `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (`1.98.0-nightly`) and
`5c543b0b8c73c7b72bc8284ced4fb22ead15734d` (`1.101.0-nightly`):

- `compiler/rustc_mir_transform/src/lib.rs#L234-L304, #L350-L824`: Query
  definitions (`mir_built`, `mir_const_qualif`, `mir_promoted`, `mir_for_ctfe`,
  `mir_drops_elaborated_and_const_checked`, `inner_optimized_mir`),
  `remap_mir_for_const_eval_select`, and pass pipelines.
- `compiler/rustc_mir_transform/src/pass_manager.rs#L112-L148`: Pass gating
  (`should_run_pass` in `1.98.0-nightly`, `PassPolicy` in `1.101.0-nightly`).
- `compiler/rustc_mir_transform/src/required_consts.rs#L1-L51`:
  `RequiredConstsVisitor::compute_required_consts`.
- `compiler/rustc_mir_transform/src/mentioned_items.rs#L1-L120`,
  `compiler/rustc_mir_transform/src/inline.rs#L1030-L1052`,
  `compiler/rustc_monomorphize/src/collector.rs#L1347-L1361`, and
  `compiler/rustc_codegen_ssa/src/back/symbol_export.rs#L97`: Dead-branch item
  mention tracking, inline propagation of `required_consts`, and `.rlib`
  monomorphization root selection.
- `compiler/rustc_mir_transform/src/simplify.rs#L48-L413`: `SimplifyCfg`,
  `preserve_switch_reads`, and `remove_dead_blocks`.
- `compiler/rustc_mir_transform/src/remove_place_mention.rs#L7-L27`:
  `RemovePlaceMention` gating on `!sess.opts.unstable_opts.mir_preserve_ub`.
- `compiler/rustc_mir_transform/src/check_alignment.rs#L12-L147`,
  `check_null.rs#L10-L127`, `check_enums.rs#L15-L114`, and
  `check_pointers.rs#L43-L245`: Pointer and enum UB check injection in
  `optimized_mir` and early return when `LangItem::PanicImpl` is `None`.
- `compiler/rustc_mir_transform/src/lower_intrinsics.rs#L10-L344`: Lowering of
  `ub_checks`, `overflow_checks`, `contract_checks`, `read_via_copy`,
  `copy_nonoverlapping`, `transmute`, `unreachable`, and unchecked arithmetic.
- `compiler/rustc_mir_transform/src/elaborate_box_derefs.rs#L49-L87`: Box deref
  lowering to `CastKind::Transmute` (`1.98.0-nightly`) and
  `CastKind::BoxDerefTransmute` (`1.101.0-nightly`).
- `compiler/rustc_middle/src/mir/syntax.rs#L1265-L1600` and
  `consts.rs#L112-L210`: `Operand`, `Rvalue`, `RuntimeChecks`, `mir::Const`, and
  `Const::is_required_const`.
- `compiler/rustc_hir/src/def.rs`: Removal of `DefKind::InlineConst` in
  `1.101.0-nightly` in favor of `DefKind::AnonConst` and
  `ty::AnonConstKind::NonTypeSystemInline`.
- `compiler/rustc_mir_build/src/thir/cx/expr.rs#L792-L839`,
  `builder/expr/as_constant.rs#L72-L108`, and
  `builder/expr/as_rvalue.rs#L64-L78`: THIR/MIR lowering of `offset_of!`,
  `ConstBlock`, `NamedConst`, and `Rvalue::Repeat`.
- `compiler/rustc_const_eval/src/interpret/intrinsics.rs#L212-L243` and
  `const_eval/machine.rs#L781-L788`: CTFE evaluation of `size_of`, `align_of`,
  `offset_of`, and `CompileTimeMachine::runtime_checks`.
- `library/core/src/mem/mod.rs#L373-L551, #L1372-L1410, #L1575-L1578`,
  `library/core/src/intrinsics/mod.rs#L2042-L2066`,
  `library/core/src/ub_checks.rs#L52-L202`,
  `library/core/src/slice/raw.rs#L124-L141`,
  `library/core/src/ptr/mod.rs#L530-L552, #L1694-L1735, #L1910-L1935`,
  `library/core/src/ptr/non_null.rs#L230-L240`,
  `library/core/src/hint.rs#L103-L112`, and
  `library/core/src/num/uint_macros.rs#L959-L973`: Standard library definitions
  of layout queries and `assert_unsafe_precondition!` callers.

### Preserved Execution Probes (`support/`)

- [`support/driver_probe.rs`](support/driver_probe.rs): Custom `rustc_driver`
  inspector that dumps in-memory `mir::Body` structures (`phase`,
  `required_consts`, `promoted`, basic-block statements, `Operand::Constant`
  variants, and terminators) at `mir_built`, `mir_promoted`,
  `mir_drops_elaborated_and_const_checked` (`Runtime(PostCleanup)`),
  `mir_for_ctfe`, and `optimized_mir`.
- [`support/probe_inputs.rs`](support/probe_inputs.rs): Probe crate exercising
  monomorphic and generic `size_of`, `align_of`, `size_of_val`, `align_of_val`,
  `offset_of!`, `usize::BITS`/`MAX`, `cfg!`, repeat-count layout folding, inline
  `const { ... }` blocks, and associated constants (`S::<T>::OK`) across live,
  `if false`, and post-`return` control flow.
- [`support/probe_198_opt0.txt`](support/probe_198_opt0.txt),
  [`support/probe_198_opt2.txt`](support/probe_198_opt2.txt), and
  [`support/probe_198_opt2_O2.txt`](support/probe_198_opt2_O2.txt): Complete
  `driver_probe` outputs under `-Z mir-opt-level=0 -Z mir-preserve-ub`,
  `-Z mir-opt-level=2`, and `-Z mir-opt-level=2 -C opt-level=2`.
- [`support/probe_q3_2.rs`](support/probe_q3_2.rs) and
  [`support/probe_results.json`](support/probe_results.json): Reproducible
  probe source and structured 4-way flag matrix
  (`-C debug-assertions={yes,no}` × `-Z ub-checks={yes,no}`) across
  `1.98.0-nightly` and `1.101.0-nightly` for raw pointer dereferences,
  `library/core` `assert_unsafe_precondition!` callers, and
  `Operand::RuntimeChecks`.

## Revalidation

Basis: `execution`

Revalidate this report when upgrading the pinned `rustc` toolchain or modifying
a `Runtime(PostCleanup)` MIR extractor or verification semantics:

1. **Compile and run [`support/driver_probe.rs`](support/driver_probe.rs) against
   [`support/probe_inputs.rs`](support/probe_inputs.rs)**:
   ```bash
   SYSROOT="$(rustc +nightly-2026-05-31 --print sysroot)"
   rustc +nightly-2026-05-31 --edition=2024 support/driver_probe.rs \
     -C link-args="-Wl,-rpath,$SYSROOT/lib" -o /tmp/driver_probe
   /tmp/driver_probe support/probe_inputs.rs --crate-type=lib --edition=2024 \
     --sysroot "$SYSROOT" -Z mir-opt-level=0 -Z mir-preserve-ub
   ```
   Verify that `Runtime(PostCleanup)` retains `TerminatorKind::Call` for
   `size_of`/`align_of`/`size_of_val`/`align_of_val` and `Const::Unevaluated` in
   both `basic_blocks` and `required_consts` for `offset_of!`, `usize::BITS`,
   `usize::MAX`, and live/`if false` `const` blocks, while post-`return` `const`
   blocks are absent from `required_consts`.
2. **Run `-Z dump-mir=all` on [`support/probe_q3_2.rs`](support/probe_q3_2.rs)**
   across `-C debug-assertions={yes,no}` and `-Z ub-checks={yes,no}` with
   `-Z mir-opt-level=0 -Z mir-preserve-ub` and compare against
   [`support/probe_results.json`](support/probe_results.json) to confirm that
   `CheckAlignment`, `CheckNull`, and `CheckEnums` remain confined to
   `optimized_mir` and that `Operand::RuntimeChecks(UbChecks)` and
   `const_eval_select` remain unlowered in `Runtime(PostCleanup)`.
3. **Check `compiler/rustc_mir_transform/src/lib.rs` and
   `compiler/rustc_hir/src/def.rs`** in the target `rustc` revision for any
   added passes in `mir_built`, `mir_promoted`, or
   `run_analysis_to_runtime_passes`, and verify that `DefKind::AnonConst` is
   filtered by `AnonConstKind::NonTypeSystemInline` on toolchains that include
   the `DefKind::InlineConst` removal.
