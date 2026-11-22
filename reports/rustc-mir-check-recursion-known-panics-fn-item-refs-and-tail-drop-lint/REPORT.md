# rustc MIR Semantic and Migration Lints: CheckCallRecursion, CheckDropRecursion, KnownPanicsLint, FunctionItemReferences, and LintTailExprDropOrder

## Summary

Four `rustc_mir_transform` lint subsystems analyze MIR across three distinct compiler phases—`MirPhase::Built` (`CheckCallRecursion`, `FunctionItemReferences`), `mir_promoted` / `MirPhase::Analysis(Initial)` (`lint_tail_expr_drop_order::run_lint`), and `run_runtime_lowering_passes` / `MirPhase::Runtime(Initial)` (`CheckDropRecursion`, `KnownPanicsLint`)—before MIR reaches Anneal's `MirPhase::Runtime(PostCleanup)` capture boundary. Direct primary-source inspection across three `rust-lang/rust` revisions (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, and `ce66487ebbd7541212d22d01c39a808057d69f1f`), live differential execution on `rustc 1.98.0-nightly` (cross-checked against recorded `rustc 1.102.0-nightly` diagnostic traces), and a zero-`sorry`, zero-`Classical.choice`, zero-`._unsafe_rec` Lean `v4.34.1` mechanization (`support/CheckRecursionKnownPanicsAndTailDropLintSoundness.lean`, `1,862` lines, `46` theorems, axioms `≤ [propext]`) establish the following load-bearing behaviors and soundness boundaries:

1. **`CheckCallRecursion` and `CheckDropRecursion` exhibit BOTH a live false negative on terminating loops AND a live false positive on non-recursive explicit tail calls (`become`), alongside a `TailCall` highlighting asymmetry:**
   - **Back-edge false negative (`check_call_recursion.rs:198-201`):** `TriColorDepthFirstSearch` returns `ControlFlow::Break(NonRecursive)` upon encountering ANY CFG back-edge (`Some(NodeStatus::Visited)`), treating a loop back-edge identically to `TerminatorKind::Return`. Consequently, any terminating loop preceding unconditional self-recursion (such as `let mut i = 0u32; while i < 1 { i += 1; }`) **completely suppresses `unconditional_recursion`** in BOTH `CheckCallRecursion` (`bounded_loop_then_recurse`) and `CheckDropRecursion` (`impl Drop for LoopBadDrop`), even though every execution exits the loop in 1 iteration and recurses infinitely.
   - **Sound SCC-condensation contrast:** In the SCC condensation DAG of the pruned CFG, a **closed nontrivial SCC** (no outgoing cross-SCC edge and no internal recursive call, modeling `loop {}`) is an escape sink, whereas a **may-exit SCC** (a cycle with an outgoing cross-SCC edge and no internal escape) is **not** a return sink. Under loop-terminating executions, absence of any reachable escape sink combined with a reachable self-recursive terminator implies unconditional recursion (`sccRecursionCheck_sound_for_loop_terminating_executions`, `sccRecursionCheck_complete_on_terminating_loops`).
   - **`TerminatorKind::TailCall` (`become`) trichotomy (`check_call_recursion.rs:131, 236, 244-254`):** Because `node_examined` returns `ControlFlow::Continue(())` for ALL `TailCall` terminators (which have 0 MIR successors) while `CallRecursion::is_recursive_terminator` matches only `TerminatorKind::Call`, three distinct behaviors arise:
     1. `pure_become` emits **`0` warnings** (`vis.reachable_recursive_calls.is_empty()`).
     2. `mixed_become_and_call(b)` (`if b { become self } else { self }`) **fires `unconditional_recursion`** and highlights **only** the `else` `Call` site, omitting the `become` site.
     3. **`become_other_or_self_call(b)` (`if b { become non_recursive_helper(b, x) } else { become_other_or_self_call(true, x) }`) triggers a live `rustc` false positive**: `rustc` emits `warning[unconditional_recursion]: function cannot return without recursing`, yet the compiled binary exits `0` and prints `R_TRUE=42 R_FALSE=42` (terminating in `≤ 2` calls for all inputs) because `line 236` fails to check whether the `TailCall` callee is `self`.
2. **`KnownPanicsLint` (`known_panics_lint.rs`) runs a single-visit worklist constant propagator over `InterpCx<'tcx, DummyMachine>` without a lattice join, preserving soundness through `CanConstProp`'s 3-tier mode classification and block-exit wiping:**
   - Locals written at most once and never address-taken receive `ConstPropMode::FullConstProp` (surviving across blocks); locals written multiple times are downgraded to `ConstPropMode::OnlyInsideOwnBlock` and wiped via `written_only_inside_own_block_locals` at the end of every basic block (`lines 828-840`); locals that are borrowed, dropped, yielded, unions, `async_drop_in_place` coroutines, or `>= 1024` bytes (`MAX_ALLOC_LIMIT`) receive `ConstPropMode::NoPropagation`.
   - `KnownPanicsLint` skips `AnonConst`, `Const`, and `Static` items (delegated to CTFE/Miri) and skips all coroutines (`tcx.is_coroutine`, `lines 51-54`, avoiding layout query cycles). It catches straight-line `unconditional_panic` (`42 / (1 - 1)`, `arr[3]`, `i32::MIN / -1`), catches `arithmetic_overflow` (`u8::MAX + 1`, `-i8::MIN`, and `x << 32` even with a symbolic/unknown LHS `x`) **even under `-C opt-level=3 -C overflow-checks=off`**, prunes dead constant branches (`if false { 1 / 0 }` emits `0` diagnostics via `SwitchInt` folding), and stays silent on cross-block mutated locals (`if cond { d = 0 } else { d = 0 }; 42 / d`), `Rvalue::Repeat` (`[0u32; 4]`), address-taken locals, unions, and `>= 1024`-byte structs.
   - Across revisions, `14210df0e -> 3ef0c22cd` adds `#[rustc_panics_when_zero]` (`ConstNIsZero`) checking on `TerminatorKind::Call` const-generic arguments (`lines 772-803`), and `3ef0c22cd -> ce66487eb` moves `PostAnalysisNormalize` into `run_analysis_cleanup_passes` (`lib.rs:649-660`), retiring `FIXME(#132279)` in `ConstPropagator::new` (`body.typing_env(tcx)`).
3. **`FunctionItemReferences` (`function_item_references.rs`) detects taking references or raw pointers to zero-sized `FnDef` items where a `fn()` pointer was intended:**
   - Function items are zero-sized (`size_of_val(&fn_alpha) == 0`); passing `&fn_alpha` and `&fn_beta` to `{:p}` (`fmt::Pointer`) or `core::mem::transmute` yields the **identical dangling 1-byte-aligned promoted ZST address `0x1`** (`REF_EQUAL=true`), whereas coercing via `fn_alpha as fn(u32) -> u32` produces distinct 8-byte `.text` code addresses (`PTR_EQUAL=false`).
   - Running in `mir_built` before coercions/inlining, the pass inspects `TerminatorKind::Call` for `sym::transmute` (walking `args[0]`'s type) and for `fmt::Pointer` caller bounds (walking parameter signatures, instantiating with callsite generics, and remapping macro-expanded spans to `span.source_callsite().ctxt()`). Revision `ce66487eb` tightens the trait-clause filter to `ClausePolarity::Positive`.
4. **`LintTailExprDropOrder` (`lint_tail_expr_drop_order.rs`) detects Edition 2021 -> 2024 tail-expression temporary drop reversals using `BackwardIncompatibleDropHint` (BID) markers, `MaybeInitializedPlaces` dataflow, and `DropsReachable` non-cleanup traversal:**
   - Running directly inside `mir_promoted` (`lib.rs:494`) before `CleanupPostBorrowck` replaces `BackwardIncompatibleDropHint` with `Nop` (`cleanup_post_borrowck.rs:36`), the pass traces forward from each BID whose type has a significant destructor (`extract_component_with_significant_dtor`, incorporating `significant_drop_order.rs`'s ecosystem allowlist) across non-cleanup edges to `drop(place)`, collecting every intervening maybe-initialized drop, and excluding `_0`, `ty::CAPTURE_STRUCT_LOCAL`, BID descendants, and trivial destructors.
   - Live differential binary execution confirms Edition 2021 emits `tail_expr_drop_order` and prints `V=42 ORDER=["local", "temp"]`, while Edition 2024 emits `0` warnings (`at_least_rust_2024()`) and prints `V=42 ORDER=["temp", "local"]`.
5. **Pass-policy and Anneal trusted-boundary consequence:** Because `Lint<T>::policy` returns `PassPolicy::optional(true)` (`pass_manager.rs:202-204`), `-Zmir-enable-passes=-CheckCallRecursion,-KnownPanicsLint` disables both passes completely (verified empirically: exit code `0`, `0` diagnostics). In Anneal (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`), verification operates on `Runtime(PostCleanup)` MIR (`Trusted.MirAst` + `Trusted.MirSemantics`), where `BackwardIncompatibleDropHint` is already erased, `Assert` terminators are explicitly checked by operational semantics, and non-termination is tracked explicitly by `Diverges`; none of these four MIR lints can be relied upon as a sound TCB invariant, though each defines concrete MIR invariants and diagnostic seams relevant to a verified `rustc` front-end/mid-end.

## Applicability

### Subjects and Their Relationships

`REPORT.json` pins six durable upstream subjects examined in combination:

1. **Executed `rustc` nightly (`rust-lang/rust` `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, host `x86_64-unknown-linux-gnu`, bundled LLVM `22.1.6`):** All live compiler invocations, JSON diagnostic captures, MIR dumps (`-Zdump-mir=built`, `-Zdump-mir=lint_tail_expr_drop_order`), `-Zmir-enable-passes` toggles, and compiled binary executions in `support/probe_check_recursion_known_panics_and_tail_drop_lint.py` / `support/probe_results.json` were executed on this toolchain on `2026-11-22`, and its installed `rustc-src` tree was diffed line-by-line against later revisions.
2. **Pinned `rust-lang/rust` revision (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)`, LLVM `23.1.5`):** Audited line-by-line across `check_call_recursion.rs`, `known_panics_lint.rs`, `function_item_references.rs`, `lint_tail_expr_drop_order.rs`, `lib.rs`, `pass_manager.rs`, `diagnostics.rs`, `cleanup_post_borrowck.rs`, `compiler/rustc_data_structures/src/graph/iterate/mod.rs`, `compiler/rustc_middle/src/ty/significant_drop_order.rs`, `compiler/rustc_const_eval/src/const_eval/dummy_machine.rs`, and `compiler/rustc_mir_build/src/builder/scope.rs`. Primary line citations throughout **Findings** refer to `3ef0c22cdb86` unless explicitly marked with another revision. Core diagnostic behavior on `3ef0c22cdb86` was also cross-checked against recorded `rustc 1.102.0-nightly` diagnostic outputs for direct recursion, `Drop` recursion, loop back-edge suppression, `KnownPanicsLint` div-by-zero/array-OOB, `FunctionItemReferences`, `mixed_become_and_call`, and Edition 2021 vs. 2024 `tail_expr_drop_order` execution.
3. **Upstream `rust-lang/rust` `main` HEAD on `2026-11-22` (`ce66487ebbd7541212d22d01c39a808057d69f1f`, source audit only, not executed):** Diffed against `3ef0c22cdb86` across all audited files to verify which behaviors are shared and which changed between `2026-11-11` and `2026-11-22`.
4. **The Rust Reference (`rust-lang/reference` `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`):** Supplies normative rules for destructor scopes and Edition 2024 temporary-scope narrowing (`src/destructors.md`, rules `destructors.scope.temporary.enclosing` and `destructors.scope.temporary.edition2024`) and for function item vs. function pointer types (`src/types/function-item.md`, `src/types/function-pointer.md`).
5. **Anneal (`joshlf/anneal` `c131b320eeeb26ef692e5afd5ec8db49ee518613`):** Audited in source (`trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`, `trusted/rustc-capture/src/driver.rs`, `trusted/correspondence/Trusted/Correspondence.lean`) to map the MIR pipeline and trusted-boundary implications of these four lints onto Anneal's `Runtime(PostCleanup)` MIR capture contract.
6. **Lean 4 (`leanprover/lean4` `5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`):** Kernel-checked `support/CheckRecursionKnownPanicsAndTailDropLintSoundness.lean` directly with `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`.

### Version Matrix: Shared vs. Revision-Specific Behavior

| Subsystem / File | `14210df0e27c` (`1.98.0-nightly`, executed + source) | `3ef0c22cdb86` (`1.102.0-nightly`, source + cross-checked) | `ce66487ebbd7` (`main` `2026-11-22`, source only) |
| :--- | :--- | :--- | :--- |
| `check_call_recursion.rs` (`270` / `272` / `272` LOC) | `TriColorDepthFirstSearch` back-edge `NonRecursive`, `TailCall => Continue(())`, `CallRecursion` & `RecursiveDrop`, `ignore_edge` identical semantically. Uses `sort()`, `CallRecursion<'tcx>`. | Refactors `sort_by_key(\|s\| s.lo_hi())`, `CallRecursion<'tcx, 'a>`, `args.no_bound_vars()`, `diagnostics::UnconditionalRecursion`. **Zero algorithmic change.** | **0 lines changed** vs. `3ef0c22cdb86`. |
| `known_panics_lint.rs` (`963` / `994` / `992` LOC) | `ConstPropagator`, `DummyMachine`, `CanConstProp`, `MAX_ALLOC_LIMIT = 1024`, `written_only_inside_own_block_locals`, coroutine/static skip, shift/arith/assert checks identical. Does **not** have `ConstNIsZero` (`#[rustc_panics_when_zero]`); includes `MutatingUseContext::Retag` in `NoPropagation`. | **Adds `TerminatorKind::Call` check for `#[rustc_panics_when_zero]` (`ConstNIsZero`, `lines 772-803`)**; removes `MutatingUseContext::Retag`. Uses `TypingEnv::post_analysis` (`FIXME(#132279)`). | **Moves `PostAnalysisNormalize` to end of `run_analysis_cleanup_passes` (`lib.rs:649-660`)**, simplifying `ConstPropagator::new` to `body.typing_env(tcx)` (`lines 184`). |
| `function_item_references.rs` (`185` / `189` / `187` LOC) | `transmute` + `fmt::Pointer` checks, `is_fn_ref` (`Ref`/`RawPtr` of `FnDef`), macro callsite span rescue, `fn(...)` cast suggestion identical. Uses separate `types().chain(consts())`. | Uses `fn_args.terms()`, `args_ref.no_bound_vars()`, `diagnostics::FnItemRef`. **Zero semantic change.** | Replaces manual `is_pointer_trait` helper with `caller_bounds().trait_clauses(tcx).with_polarity(ClausePolarity::Positive).for_trait(pointer_trait)` (`lines 80-91`), explicitly filtering positive polarity. |
| `lint_tail_expr_drop_order.rs` (`567` / `566` / `566` LOC) & `significant_drop_order.rs` | `DropsReachable`, `MaybeInitializedPlaces`, `BackwardIncompatibleDropHint`, 4 observer exclusions, ecosystem allowlist identical. Uses `lints_that_dont_need_to_run`, matches `async_fut: _` on `Drop`. | Renames `skippable_lints`; removes `async_fut` field; adds `!body.local_decls[local].from_compiler_desugaring()` in `collect_user_names` (`line 468`). | **0 lines changed** in `lint_tail_expr_drop_order.rs`; `significant_drop_order.rs` adds `ty::View(..) => unimplemented!()` (`line 161`). |

### Configuration, Flags, and Model–System Relation

- **Invocation modes tested:** `--edition=2021` and `--edition=2024`; default lint levels (`unconditional_recursion` and `function_item_references` are warn-by-default; `unconditional_panic` and `arithmetic_overflow` are **deny-by-default**; `tail_expr_drop_order` is allow-by-default on Edition 2021 and requires `-W tail-expr-drop-order` or `-W rust-2024-compatibility`); `-W unconditional_panic -W arithmetic_overflow`; `-C overflow-checks=on` vs. `-C opt-level=3 -C overflow-checks=off`; `#![feature(explicit_tail_calls)]`; `-Zmir-enable-passes=-CheckCallRecursion,-KnownPanicsLint`; and `-Zdump-mir={built,lint_tail_expr_drop_order}`.
- **Model–system relation for the Lean 4 mechanization:** `support/CheckRecursionKnownPanicsAndTailDropLintSoundness.lean` is a standalone, zero-import Lean `v4.34.1` formalization modeling the four `rustc` lint algorithms, their concrete MIR counterexamples, and their soundness/completeness criteria. **No mechanized compiler extraction connects `compiler/rustc_mir_transform/src/*.rs` directly to the Lean definitions** (`Model–system relation: derived modeling bridge grounded by line-by-line source inspection and live differential execution`). Every Lean theorem establishes a kernel-checked mathematical property of the faithful model; its correspondence to `rustc` rests on the explicit source-to-model mapping documented in **Findings** and verified by `support/probe_check_recursion_known_panics_and_tail_drop_lint.py`.
- **Relation to nearby corpus packages:** Two existing Lean toy-model packages in the corpus examine adjacent language-semantics topics—`edition-indexed-drop-scopes-tail-and-if-let-temporaries-and-inhabitedness-gated-switches` (expression-level Edition 2021 vs. 2024 drop-scope rules) and `explicit-tail-calls-frame-reuse-pre-jump-drop-order-stack-borrow-rejection-and-inlining` (frame-stack operational semantics of guaranteed tail calls). Neither inspects or executes `rustc_mir_transform`'s four MIR lint passes (`check_call_recursion.rs`, `known_panics_lint.rs`, `function_item_references.rs`, `lint_tail_expr_drop_order.rs`), which are the direct subjects of this report.

## Findings

### 1. MIR Pipeline Placement, Pass Policies, and Anneal `Runtime(PostCleanup)` Trusted Boundary

*Basis: source (`rust-lang/rust` `3ef0c22cdb86` and `ce66487ebbd7`, `joshlf/anneal` `c131b320eeeb`) + execution (`rustc 1.98.0-nightly` `14210df0e27c`) + derived.*

#### 1.1 Exact Pipeline Ordering Across Queries and Phases

In `compiler/rustc_mir_transform/src/lib.rs`, the four lint subsystems execute at **three distinct MIR lowering stages**, strictly before MIR optimization (`inner_optimized_mir`) and strictly before `MirPhase::Runtime(RuntimePhase::PostCleanup)` completes:

| Stage / Query (`lib.rs` at `3ef0c22cdb86`) | MIR Phase Entering Pass | Passes Executed (in Order) | Key Structural Invariants Visible to Lint |
| :--- | :--- | :--- | :--- |
| `mir_built` (`lib.rs:395-433`) | `MirPhase::Built` | `LintAndRemoveUninhabited` -> `Lint(CheckForceInline)` -> **`Lint(CheckCallRecursion)` (`line 421`)** -> `Lint(CheckPackedRef)` -> `Lint(CheckConstItemMutation)` -> `Lint(CheckMutRestriction)` -> **`Lint(FunctionItemReferences)` (`line 425`)** -> `SimplifyCfg::Initial` -> `Lint(SanityCheck)` | Raw built CFG still contains `FalseEdge`, `FalseUnwind`, `BackwardIncompatibleDropHint`, un-elaborated `Drop`s, and original call-site `FnDef` operands prior to promotion/inlining. |
| `mir_promoted` (`lib.rs:436-498`) | `MirPhase::Analysis(AnalysisPhase::Initial)` | `PromoteTemps` -> `SimplifyCfg::PromoteConsts` -> `InstrumentCoverage` -> **`lint_tail_expr_drop_order::run_lint(tcx, def, &body)` (`line 494`)** | Promoted temps extracted; `BackwardIncompatibleDropHint` statements still intact; borrowck and drop elaboration have **not** run yet (so `MaybeInitializedPlaces` dataflow is required). |
| `run_analysis_cleanup_passes` (`lib.rs:642-652`) | `Analysis(Initial)` -> `Analysis(PostCleanup)` | `ImpossibleClauses` -> `CleanupPostBorrowck` -> `RemoveNoopLandingPads` -> `SimplifyCfg::PostAnalysis` -> `Derefer` (plus `PostAnalysisNormalize` appended here in `ce66487ebbd7`, `lib.rs:655`) | **`CleanupPostBorrowck` (`cleanup_post_borrowck.rs:36`) converts `StatementKind::BackwardIncompatibleDropHint` to `Nop`**, permanently erasing Edition 2024 BID markers before runtime MIR. |
| `run_runtime_lowering_passes` (`lib.rs:655-679`) | `Analysis(PostCleanup)` -> `Runtime(Initial)` | `CriticalCallEdges` -> (`PostAnalysisNormalize` in `3ef0c22cdb86`) -> `Subtyper` -> `ElaborateDrops` -> **`Lint(CheckDropRecursion)` (`line 665`)** -> `AbortUnwindingCalls` -> `AddMovesForPackedDrops` -> `EraseDerefTemps` -> `ElaborateBoxDerefs` -> `StateTransform` -> **`Lint(KnownPanicsLint)` (`line 676`)** | `ElaborateDrops` has expanded implicit drops and drop flags, enabling `CheckDropRecursion` to inspect real `TerminatorKind::Drop` sites. `StateTransform` has lowered coroutines, and `KnownPanicsLint` runs immediately before `Runtime(Initial)` validation. |
| `run_runtime_cleanup_passes` (`lib.rs:682-696`) | `Runtime(Initial)` -> **`Runtime(PostCleanup)`** | `LowerIntrinsics` -> `RemovePlaceMention` -> `SimplifyCfg::PreOptimizations` (then clears `decl.local_info = ClearCrossCrate::Clear`) | **Anneal capture boundary** (`Trusted.MirAst` / `Trusted.Correspondence`). All four lints have already executed; `local_info` is cleared; `Assert` terminators remain intact. |

#### 1.2 `MirLint` Wrapper Policy (`PassPolicy::optional(true)`) vs. Direct Query Hook

In `compiler/rustc_mir_transform/src/pass_manager.rs:174-205`, the `MirLint` trait and its `Lint<T>` adapter enforce immutability of `&Body<'tcx>` and suppress MIR dumps (`is_mir_dump_enabled() -> false`), **but declare `PassPolicy::optional(true)` rather than `PassPolicy::Required`**:

```rust
// compiler/rustc_mir_transform/src/pass_manager.rs:190-205 (3ef0c22cdb86)
impl<'tcx, T> MirPass<'tcx> for Lint<T>
where
    T: MirLint<'tcx>,
{
    fn name(&self) -> &'static str { self.0.name() }
    fn run_pass(&self, tcx: TyCtxt<'tcx>, body: &mut Body<'tcx>) { self.0.run_lint(tcx, body) }
    fn is_mir_dump_enabled(&self) -> bool { false }
    fn policy(&self, _ctx: &PassCtx<'_>) -> PassPolicy {
        PassPolicy::optional(true)
    }
}
```

By contrast, `lint_tail_expr_drop_order::run_lint` is **not** wrapped in `Lint<T>` and bypasses `pm::run_passes`; it is called directly at `lib.rs:494`, performs its own `MirDumper::new(tcx, "lint_tail_expr_drop_order", body)` dump (`lint_tail_expr_drop_order.rs:230-232`), and short-circuits via `body.span.edition().at_least_rust_2024() || tcx.skippable_lints(()).contains(&LintId::of(TAIL_EXPR_DROP_ORDER))` (`lines 188-192`).

**Empirical confirmation (`probe_results.json`, `pass_toggle_default` vs. `pass_toggle_disabled`):**
- Compiling `direct_recurse` + `div_zero` with default flags emits `warning[unconditional_recursion]` and `error[unconditional_panic]` (`returncode = 1`).
- Compiling the exact same source with `-Zmir-enable-passes=-CheckCallRecursion,-KnownPanicsLint` emits **`0` diagnostics** and succeeds with **`returncode = 0`**, confirming that `Lint<T>` passes can be silently disabled via `-Zmir-enable-passes`.

#### 1.3 Trusted-Boundary Relationship to Anneal (`joshlf/anneal@c131b320eeeb`)

Inspecting `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`:
- `trusted/lean/Trusted/MirAst.lean:53` and `trusted/correspondence/Trusted/Correspondence.lean:1317` specify `Runtime(PostCleanup)` MIR as Anneal's captured IR phase.
- `trusted/lean/Trusted/MirAst.lean:732-795` lowers `TerminatorKind::Assert` directly to `TerminatorKind.assert` with `AssertKind` variants (`overflow`, `overflowNeg`, `divByZero`, `remByZero`, `boundsCheck`, `misalignedPtrDeref`, `nullPtrDeref`, `unsupported`), while `Drop`, `TailCall`, `UnwindTerminate`, `Yield`, `CoroutineDrop`, `FalseEdge`, `FalseUnwind`, and `InlineAsm` currently lower to `TerminatorKind.unsupported`.
- `trusted/lean/Trusted/MirSemantics.lean:1646-1698` defines `WellFormed` (absence of runtime faults, including failed `Assert` terminators), `Behavior` (terminating outputs), and `Diverges` (infinite step traces) independently of any compiler lint.
- `trusted/rustc-capture/src/driver.rs:25, 75-84` pins the compiler version string and gates on `after_analysis` with `tcx.dcx().has_errors().is_none()`.

**Derived architectural consequence for a verified `rustc` / Anneal TCB:**
1. Because `CheckCallRecursion`, `CheckDropRecursion`, `KnownPanicsLint`, and `FunctionItemReferences` are optional (`PassPolicy::optional(true)`), heuristic (incomplete on loops, cross-block mutations, coroutines, `Repeat`, and mutual recursion), and even unsound in one `TailCall` case (`become_other_or_self_call`), **a verified compiler or Anneal proof pipeline must never rely on these lints as soundness preconditions** (e.g., to discharge `¬ Diverges`, to elide `Assert` checks, or to assume absence of ZST address collapse).
2. Because `KnownPanicsLint` runs at the end of `run_runtime_lowering_passes` and inspects `Assert` terminators before `SimplifyCfg::PreOptimizations` and MIR optimizations, its deny-by-default `unconditional_panic` / `arithmetic_overflow` errors can reject crates during `after_analysis` before Anneal capture—even under `-C overflow-checks=off`—unless explicitly `#[allow(...)]`'d.
3. Because `BackwardIncompatibleDropHint` is erased by `CleanupPostBorrowck` before `Runtime(PostCleanup)`, Edition 2021 vs. Edition 2024 drop-order differences are already baked into the `Drop` terminator sequence present in `Runtime(PostCleanup)` MIR (and therefore into Anneal's captured IR once `TerminatorKind::Drop` is lowered beyond `.unsupported`).

---

### 2. `CheckCallRecursion` & `CheckDropRecursion`: `TriColorDepthFirstSearch` Back-Edge False Negative, SCC Condensation, and `TailCall` (`become`) Trichotomy

*Basis: source (`check_call_recursion.rs`, `graph/iterate/mod.rs`) + execution (`rustc 1.98.0-nightly`, cross-checked against `1.102.0-nightly`) + derived (Lean `v4.34.1` proofs).*

#### 2.1 Algorithm Anatomy (`check_call_recursion.rs:16-272`)

Both `CheckCallRecursion` (scheduled in `mir_built`, `lib.rs:421`) and `CheckDropRecursion` (scheduled immediately after `ElaborateDrops` in `run_runtime_lowering_passes`, `lib.rs:665`) delegate to a single generic driver `check_recursion(tcx, body, classifier)` (`lines 64-93`):

```rust
// compiler/rustc_mir_transform/src/check_call_recursion.rs:64-93 (3ef0c22cdb86)
fn check_recursion<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    classifier: impl TerminatorClassifier<'tcx>,
) {
    let def_id = body.source.def_id().expect_local();
    if let DefKind::Fn | DefKind::AssocFn = tcx.def_kind(def_id) {
        let mut vis = Search { tcx, body, classifier, reachable_recursive_calls: vec![] };
        if let Some(NonRecursive) =
            TriColorDepthFirstSearch::new(&body.basic_blocks).run_from_start(&mut vis)
        {
            return;
        }
        if vis.reachable_recursive_calls.is_empty() {
            return;
        }
        vis.reachable_recursive_calls.sort_by_key(|span| span.lo_hi());
        let sp = tcx.def_span(def_id);
        let hir_id = tcx.local_def_id_to_hir_id(def_id);
        tcx.emit_node_span_lint(
            UNCONDITIONAL_RECURSION, hir_id, sp,
            UnconditionalRecursion { span: sp, call_sites: vis.reachable_recursive_calls },
        );
    }
}
```

The two `TerminatorClassifier` implementations differ solely in which terminators count as self-recursive:
- **`CallRecursion` (`lines 123-172`):** Matches only `TerminatorKind::Call { func, args, .. }`. Rejects immediately if `args.len() != body.arg_count`. Resolves `ty::FnDef(callee, args)` via `try_normalize_erasing_regions` and `Instance::try_resolve`, and returns `callee == caller && &call_args.as_slice()[..self.trait_args.len()] == self.trait_args`. Comparing the trait's generic arguments prevents false positives when a trait default method calls a concrete specialization (e.g., `<u8 as RecurseTrait>::work(&0u8)`). Intra-procedural only (`FIXME(#57965)` at `line 160` notes mutual recursion across function boundaries is not detected).
- **`RecursiveDrop` (`lines 174-186`):** Triggered by `CheckDropRecursion` only on `DefKind::AssocFn` implementing `LangItem::Drop` with `sig.inputs().len() == 1` and `&mut T` receiver (`lines 45-59`). Matches `TerminatorKind::Drop { place, .. }` where `place.ty(body, tcx).ty == self.drop_for`. It must run after `ElaborateDrops` because pre-elaboration MIR contains conditional/uninitialized `Drop` terminators and unexpanded aggregate drops.

The `TriColorVisitor` (`Search`, `lines 188-272`) drives `TriColorDepthFirstSearch::run_from` (`compiler/rustc_data_structures/src/graph/iterate/mod.rs:240-288`), an iterative event-stack DFS pushing `Event { node, becomes: Settled }` followed by `Event { node: succ, becomes: Visited }` for every non-ignored successor:

- **`ignore_edge(bb, target)` (`lines 259-271`):** Ignores (1) a `Cleanup(target)` unwind edge whenever `terminator.successors().count() > 1` (so a normal panicking unwind path does not falsely count as a non-recursive return, while a sole-successor unwind edge is retained), (2) **all** outgoing edges of any terminator classified as recursive (`is_recursive_terminator == true`), so the unreachable `Return` after a recursive call is never visited through that call, and (3) the `imaginary_target` of `TerminatorKind::FalseEdge`.
- **`node_examined(bb, prior_status)` (`lines 193-238`):**
  - **`Some(NodeStatus::Visited)` (`lines 199-201`):** Immediately returns `ControlFlow::Break(NonRecursive)` ("Back-edge in the CFG (loop)").
  - **`UnwindTerminate | CoroutineDrop | UnwindResume | Return | Unreachable | Yield` (`lines 205-210`):** Immediately returns `ControlFlow::Break(NonRecursive)`.
  - **`InlineAsm { targets, .. }` (`lines 214-220`):** `Continue(())` if `!targets.is_empty()`, else `Break(NonRecursive)` (diverging targetless asm).
  - **`Assert | Call | Drop | FalseEdge | FalseUnwind | Goto | SwitchInt` (`lines 223-229`):** `Continue(())`.
  - **`TailCall { .. }` (`line 236`):** Unconditionally returns `ControlFlow::Continue(())`!
- **`node_settled(bb)` (`lines 240-257`):** Records `terminator.source_info.span` in `reachable_recursive_calls` iff `self.classifier.is_recursive_terminator(...)` returns `true`.

#### 2.2 Subtle Behavior 1: Live Back-Edge False Negative on Terminating Loops (`lines 198-201`)

Because `node_examined` breaks with `NonRecursive` on ANY `Some(NodeStatus::Visited)` edge, `TriColorDepthFirstSearch` equates **every CFG cycle** with `TerminatorKind::Return`. In `bounded_loop_then_recurse`:

```rust
pub fn bounded_loop_then_recurse(x: u32) -> u32 {
    let mut i = 0u32;
    while i < 1 {
        i += 1;
    }
    bounded_loop_then_recurse(x.wrapping_add(i))
}
```

Dumping `mir_built` (`rustc -Zdump-mir=built`) confirms the exact CFG seen by `CheckCallRecursion`:
```text
bb0:  goto -> bb1;
bb1:  falseUnwind -> [real: bb2, unwind: ...];
bb2:  switchInt(move _5) -> [0: bb4, otherwise: bb3];
bb3 -> ... -> bb10:  goto -> bb1;   // BACK-EDGE: bb1 has NodeStatus::Visited!
bb4 -> bb6 -> bb11 -> bb12:
      _0 = bounded_loop_then_recurse(move _11) -> [return: bb13, unwind: bb14];
```

During `TriColorDepthFirstSearch::run_from_start`:
1. `bb0` enters (`Visited`), pushes `bb1`.
2. `bb1` enters (`Visited`), pushes `bb2`.
3. `bb2` enters (`Visited`), pushes `bb4` and `bb3` onto the LIFO stack.
4. `bb3` pops first (or even if `bb4` popped first, `bb12`'s recursive `Call` edges are ignored so `bb4` settles cleanly and then `bb3` pops), traverses `bb3 -> ... -> bb10 -> bb1`, and inspects `bb1` while `bb1` is still `NodeStatus::Visited` (gray, not yet settled).
5. `node_examined(bb1, Some(NodeStatus::Visited))` returns `ControlFlow::Break(NonRecursive)`!
6. `check_recursion` returns immediately on `line 76` with **`0` warnings**—and the exact same suppression occurs in `CheckDropRecursion` on `impl Drop for LoopBadDrop` (`let mut i = 0; while i < 1 { i += 1; } let _ = LoopBadDrop(...);`).

**Contrast with Sound SCC-Condensation DAG Reachability:**
Let $G'$ be the pruned CFG (applying `ignore_edge`) and $\mathcal{C}(G')$ its Tarjan/Kosaraju SCC condensation DAG (where cross-SCC edges strictly decrease reverse topological index). Partition every SCC $C \in \mathcal{C}(G')$ into four mutually exclusive topological classes:

| SCC Class | Graph Characterization in $\mathcal{C}(G')$ | `TriColorDepthFirstSearch` Verdict | Sound SCC-Condensation Verdict (Modulo Loop Termination) |
| :--- | :--- | :--- | :--- |
| **Explicit Escape SCC** | Contains `Return`, `UnwindResume`, `UnwindTerminate`, `CoroutineDrop`, `Unreachable`, `Yield`, targetless `InlineAsm`, or **non-recursive** `TailCall(false)` | `NonRecursive` (except `TailCall(false)` bug — see §2.3!) | **Escape sink** (`NonRecursive`) |
| **Closed Nontrivial SCC** (`loop {}`) | Has an intra-SCC edge, **0** outgoing cross-SCC edges, and **0** self-recursive terminators inside $C$ | `NonRecursive` | **Escape sink** (`NonRecursive` — diverges locally without recursing) |
| **May-Exit Loop SCC** (`while i < 1 { i += 1; }`) | Has an intra-SCC edge, **$\ge 1$ outgoing cross-SCC edge**, and no explicit escape inside $C$ | **`NonRecursive` (FALSE NEGATIVE on terminating loops!)** | **NOT an escape sink**: every loop-terminating execution must leave $C$ along an outgoing edge |
| **Acyclic / Recursive-Call SCC** | Trivial SCC with non-escape or self-recursive terminator | `Continue` (if no back-edge elsewhere) | Not an escape sink; marks `hasRecCall` if recursive |

Under this criterion (`SccUnconditionalRecursion` in `CheckRecursionKnownPanicsAndTailDropLintSoundness.lean:665-705`), if **no escape sink is reachable from `compOf(start)`** in $\mathcal{C}(G')$ and **at least one `hasRecCall` SCC is reachable**, then **no finite loop-exiting execution path can ever reach a genuine non-recursive escape** (`sccRecursionCheck_sound_for_loop_terminating_executions`), while `boundedLoopCfg` is accurately flagged (`sccRecursionCheck_complete_on_terminating_loops`) and `loop {}` remains silent (`sccRecursionCheck_silent_on_pure_infinite_loop`).

#### 2.3 Subtle Behavior 2: `TerminatorKind::TailCall` (`become`) Trichotomy — Silence, Asymmetry, and Live False Positive

Inspecting `check_call_recursion.rs:131, 236, 244-254` exposes **three distinct behaviors** under `#![feature(explicit_tail_calls)]`:

1. **Pure self tail-call recursion (`pure_become`) -> `0` warnings:**
   - `bb0` terminates in `TerminatorKind::TailCall { func: pure_become, .. }`.
   - `node_examined` executes `TerminatorKind::TailCall { .. } => ControlFlow::Continue(())` (`line 236`).
   - `TailCall` has `0` MIR successors, so `bb0` immediately settles.
   - `node_settled` calls `CallRecursion::is_recursive_terminator`, which fails `let TerminatorKind::Call { .. } = &terminator.kind else { return false; }` (`line 131`). Thus `reachable_recursive_calls` remains empty `[]`.
   - `check_recursion` hits `if vis.reachable_recursive_calls.is_empty() { return; }` (`line 78`) and stays silent. (Intentional design documented in `FIXME(explicit_tail_calls)` at `lines 246-248`: tail-call loops like `fn g() { become g() }` execute in $O(1)$ stack space and do not overflow the stack.)
2. **Mixed `become` + normal `Call` (`mixed_become_and_call`) -> Asymmetric Warning Highlighting ONLY the `else` `Call`:**
   - In `if b { become mixed_become_and_call(!b, x) } else { mixed_become_and_call(!b, x) }`, the `then` branch terminates in `TailCall` (`Continue(())`, not added to `reachable_recursive_calls`) while the `else` branch terminates in recursive `Call` (`Continue(())`, added to `reachable_recursive_calls`).
   - Because neither branch returned `Break(NonRecursive)` and `reachable_recursive_calls == [else_call_span]` is non-empty, `rustc` emits `warning[unconditional_recursion]` with primary span on the function signature and **a single secondary `"recursive call site"` label on the `else` `Call` line only** (verified identically on `rustc 1.98.0-nightly` line `10`/`14` and recorded `rustc 1.102.0-nightly` line `10`/`14`).
3. **Non-recursive `become helper(...)` + recursive `else` `Call` (`become_other_or_self_call`) -> LIVE `rustc` FALSE POSITIVE:**
   ```rust
   fn non_recursive_helper(_b: bool, x: u32) -> u32 { x + 1 }

   fn become_other_or_self_call(b: bool, x: u32) -> u32 {
       if b {
           become non_recursive_helper(b, x)
       } else {
           become_other_or_self_call(true, x)
       }
   }
   ```
   - **Root cause in `check_call_recursion.rs:236`:** `TerminatorKind::TailCall { .. } => ControlFlow::Continue(())` **never inspects `func`** to distinguish a self-recursive `TailCall` from a tail call to a completely different, non-recursive function (`non_recursive_helper`)!
   - **Live execution proof (`probe_results.json`, `tail_call_fp_bin`):** `rustc 1.98.0-nightly` emits **`warning[unconditional_recursion]: function cannot return without recursing`** on line `8` (`become_other_or_self_call`, labeling line `12` as `"recursive call site"`), yet compiling and running the binary exits `0` and prints **`R_TRUE=42 R_FALSE=42`** (terminating in 1 call for `b = true` and 2 calls for `b = false`, for ALL inputs).
   - **Verified repair:** Checking whether a `TailCall` resolves to `self`—returning `ControlFlow::Break(NonRecursive)` when `callee != caller` (or trait args differ) and `Continue(())` only for self-recursive `TailCall`—eliminates the false positive on `become_other_or_self_call` while keeping `pure_become` silent and `mixed_become_and_call` warning (`fixedTailCallCheck_eliminates_false_positive` in Lean).

#### 2.4 Live Empirical Matrix (`CheckCallRecursion` & `CheckDropRecursion`)

| Test Function / Type (`probe_check_recursion_...py`) | Actual Runtime Behavior | Live `rustc 1.98.0-nightly` (`14210df0e27c`) | Cross-Check `1.102.0-nightly` (`3ef0c22cdb86`) | Classification |
| :--- | :--- | :--- | :--- | :--- |
| `direct_recurse` | Infinite call recursion | **WARN** `unconditional_recursion` (1 call site) | **WARN** `unconditional_recursion` (1 call site) | True positive |
| `bounded_loop_then_recurse` (`while i < 1`) | Loop exits in 1 iter -> infinite recursion | **0 warnings** | **0 warnings** | **False negative (back-edge)** |
| `pure_infinite_loop` (`loop {}`) | Diverges locally without recursing | 0 warnings | 0 warnings | True negative |
| `base_case_recurse` (`if n == 0 { return 0 }`) | Terminates for `n >= 0` | 0 warnings | 0 warnings | True negative |
| `impl Drop for BadDrop` | Infinite `Drop` recursion | **WARN** `unconditional_recursion` (1 call site) | **WARN** `unconditional_recursion` (1 call site) | True positive (`CheckDropRecursion`) |
| `impl Drop for LoopBadDrop` (`while i < 1`) | Loop exits in 1 iter -> infinite `Drop` recursion | **0 warnings** | **0 warnings** | **False negative (back-edge)** |
| `mutual_a` <-> `mutual_b` | Mutual infinite recursion | 0 warnings | — (identical source) | Known intra-procedural limit (`#57965`) |
| `both_branches_recurse` (`if b { f } else { f }`) | Infinite recursion on both branches | **WARN** `unconditional_recursion` (**2** call sites) | — (identical source) | True positive |
| `RecurseTrait::work` calling `<u8 as RecurseTrait>::work` | Terminates via concrete `u8` impl | 0 warnings | — (identical source) | True negative (`trait_args` filter) |
| `pure_become` (`become pure_become(x)`) | Constant-stack tail recursion | 0 warnings | 0 warnings | Intentional silence (`reachable_recursive_calls.is_empty()`) |
| `mixed_become_and_call` (`if b { become f } else { f }`) | Unconditional recursion | **WARN** `unconditional_recursion` (highlights **only** `else` `Call`) | **WARN** `unconditional_recursion` (highlights **only** `else` `Call`) | Asymmetric highlighting (`FIXME(explicit_tail_calls)`) |
| `become_other_or_self_call` (`if b { become helper } else { f(true) }`) | **Terminates in `<= 2` calls (`R_TRUE=42 R_FALSE=42`)** | **WARN** `unconditional_recursion` (line 8 / line 12) | — (`line 236` identical in `3ef0c22cd` and `ce66487eb`) | **Live false positive (non-recursive `TailCall`)** |

---

### 3. `KnownPanicsLint`: `DummyMachine` Constant-Propagation Domain, Soundness Invariants, and Boundaries

*Basis: source (`known_panics_lint.rs`, `dummy_machine.rs`) + execution (`rustc 1.98.0-nightly`, cross-checked against `1.102.0-nightly`) + derived (Lean `v4.34.1` proofs).*

#### 3.1 Entry Gates and `InterpCx<'tcx, DummyMachine>` Configuration

`KnownPanicsLint::run_lint` (`known_panics_lint.rs:31-63`) applies three early exits before constructing `ConstPropagator`:
1. `if body.tainted_by_errors.is_some() { return; }` (`lines 33-35`).
2. `if !is_fn_like && !is_assoc_const { return; }` (`lines 39-47`): runs only on functions, methods, closures, and associated constants; **skips `AnonConst`, `Const`, and `Static` items** because they are evaluated directly by CTFE/Miri.
3. `if tcx.is_coroutine(def_id.to_def_id()) { return; }` (`lines 51-54`): **skips all coroutines (`async fn`, `gen fn`, `#[coroutine]`)** to avoid query cycles when requesting coroutine layouts (`FIXME(welseywiser)`).

For admitted bodies, `ConstPropagator::new` (`lines 182-201`) instantiates `InterpCx<'tcx, DummyMachine>` (`compiler/rustc_const_eval/src/const_eval/dummy_machine.rs:34-213`):
- **`ALL_CONSTS_ARE_PRECHECKED = false`** (`dummy_machine.rs:47`), **`enforce_alignment = false`** (`line 50`), **`enforce_validity = false`** (`line 54`): avoids rejecting speculative evaluation of arbitrary constants or unaligned places during linting.
- **`before_access_global` (`lines 58-77`):** Fails cleanly (`throw_machine_stop_str!`) on any global write (`is_write`) or read from a mutable static (`alloc.inner().mutability.is_mut()`), preventing unsound propagation of mutable runtime globals.
- **`binary_ptr_op` (`lines 134-179`):** Supports only provenance-free integer bit comparisons (`Eq | Ne | Lt | Le | Gt | Ge` via `to_bits(size)?`); rejects pointer arithmetic (`Add | Sub | BitOr | BitAnd | BitXor`) via `throw_machine_stop_str!`.
- **`runtime_checks` (`lines 128-132`):** Explicitly panics if invoked; `ConstPropagator::eval_operand` guards this by returning `None` for `Operand::RuntimeChecks(_)` (`known_panics_lint.rs:289`).
- **Empty frame stack (`lines 196-201`):** `DummyMachine::stack` returns `&[]`; all call/frame/intrinsic hooks are `unimplemented!()` because `ConstPropagator` never interprets calls—it only calls `ecx.eval_mir_constant`, `ecx.binary_op`, `ecx.unary_op`, `ecx.read_immediate`, `ecx.read_scalar`, `ecx.int_to_int_or_float`, `ecx.float_to_float_or_int`, `ecx.read_discriminant`, and `ecx.discriminant_for_variant`.

#### 3.2 `Value` Lattice, `CanConstProp` 3-Tier Classification, and Single-Visit Worklist Soundness

`ConstPropagator` stores per-local abstract state in `locals: IndexVec<Local, Value<'tcx>>` (`lines 73, 80-84`):
- `Value::Immediate(ImmTy<'tcx>)` (scalars; note `ScalarPair` results of overflowing `BinOp` are split into a 2-field `Value::Aggregate` at `lines 567-575`)
- `Value::Aggregate { variant: VariantIdx, fields: IndexVec<FieldIdx, Value<'tcx>> }` (ADTs, arrays from `Rvalue::Aggregate`, tuples)
- `Value::Uninit` (top / unknown value)

Because `ConstPropagator::visit_body` (`lines 669-678`) performs a **single-visit worklist DFS (`if !self.visited_blocks.insert(bb) { continue; }`) with NO path-join/meet operator**, its soundness hinges entirely on `CanConstProp::check` (`lines 874-994`) and block-exit wiping (`lines 822-852`):

1. **Initial per-local type/size filter (`lines 891-916`):** Every local starts as `ConstPropMode::FullConstProp`, EXCEPT:
   - `ty.is_async_drop_in_place_coroutine(tcx)` -> `NoPropagation` (avoids early layout cycle),
   - `ty.is_union()` -> `NoPropagation` (unions lack an active variant tag),
   - `layout_of` fails OR `layout.size >= Size::from_bytes(1024)` (`MAX_ALLOC_LIMIT = 1024`, `line 858`) -> `NoPropagation` (prevents OOM / blowup, `#66397`).
2. **Pre-marking function arguments (`lines 918-920`):** Every argument local is inserted into `found_assignment` before walking the body, so a single write to an argument local inside the body counts as a **second** assignment and downgrades it to `OnlyInsideOwnBlock`.
3. **Use-context scan (`CanConstProp::visit_place` / `visit_local`, `lines 927-993`):**
   - Places starting with `PlaceElem::Deref` rewrite context to `NonMutatingUse(Copy)` (`lines 931-933`), since dereferencing reads only the pointer address stored in `place.local`.
   - `Store | SetDiscriminant | Call | AsmOutput`: inserts `local` into `found_assignment`; if already present, downgrades `FullConstProp -> OnlyInsideOwnBlock` (`lines 949-965`).
   - `SharedBorrow | FakeBorrow | RawBorrow | Borrow | Drop | Yield`: unconditionally sets `NoPropagation` (`lines 976-987`).
4. **Block-exit wipe (`visit_basic_block_data`, `lines 822-851`):** Whenever `access_mut` writes an `OnlyInsideOwnBlock` local (`lines 221-223`), it records the local in `written_only_inside_own_block_locals`. Immediately after finishing the block's statements and terminator, every local in `written_only_inside_own_block_locals` is cleared via `self.remove_const(local)` (setting it back to `Value::Uninit`). Debug builds assert (`ensure_not_propagated`, `lines 528-539, 842-851`) that no `NoPropagation` or `OnlyInsideOwnBlock` non-ZST local survives past a block boundary.
5. **Defensive poisoning inside blocks:**
   - `Rvalue::Ref | RawPtr | Reborrow` (`lines 425-436`): calls `self.remove_const(place.local)` and returns `None` (`check_rvalue`).
   - Failed `eval_rvalue` (`lines 700-717`, including `Rvalue::Repeat` at `lines 604-607`, non-empty `dest.projection` at `line 543`, or unsupported casts at `line 639`): calls `self.remove_const(place.local)` ("nuking the entire site from orbit").
   - `StorageLive` and `StorageDead` (`lines 743-748`): call `self.remove_const(local)`.
   - Failed `Assert` (`lines 483-485`): poisons `cond.place().local` so downstream checks do not cascade on invalid values.

#### 3.3 Checked Panic & Overflow Categories (Debug vs. Release Parity)

`KnownPanicsLint` emits two **deny-by-default** lints through three mechanisms:
1. **`check_unary_op` (`lines 313-337`) -> `arithmetic_overflow`:** Checks `UnOp::Neg` on integral scalars via `0 - arg` (`BinOp::SubWithOverflow`); catches `-i8::MIN` in both debug and release builds.
2. **`check_binary_op` (`lines 339-400`) -> `arithmetic_overflow`:**
   - **Symbolic-LHS shift check (`lines 351-374`):** For `BinOp::Shl | BinOp::Shr`, checks `r_bits >= left_size.bits()` **even when `l` is `None` (unknown/parameter)**! Thus `pub fn shift_overflow_symbolic_lhs(x: u32) -> u32 { x << 32 }` fires `arithmetic_overflow` unconditionally.
   - **Wrapping-to-overflowing normalization (`lines 376-397`):** Normalizes `Add | Sub | Mul` via `op.wrapping_to_overflowing()` and checks `ecx.binary_op(op, &l, &r)` **at the `Rvalue::BinaryOp` assignment site rather than at the `Assert` terminator**, specifically so `u8::MAX + 1` still triggers `arithmetic_overflow` under **`-C opt-level=3 -C overflow-checks=off`** (where MIR emits no `Assert` for `Add`/`Sub`/`Mul`!).
3. **`check_assertion` (`lines 467-526`) -> `unconditional_panic`:** At `TerminatorKind::Assert { expected, msg, cond, .. }`, evaluates `cond` to `value_const`; if `Scalar::from_bool(expected) != value_const`, emits `UNCONDITIONAL_PANIC` for `DivisionByZero`, `RemainderByZero`, `Overflow(Div | Rem)` (signed `MIN / -1`, which is UB in MIR without the assert), and `BoundsCheck { len, index }`. Returns silently for `Overflow(Add|Sub|Mul|Shl|Shr)` and `OverflowNeg` (already handled on the rvalues) and for `_` (e.g., alignment/null pointer UB checks).
4. **Const-generic zero check (`lines 772-803`, added in `14210df0e -> 3ef0c22cd`) -> `unconditional_panic` (`ConstNIsZero`):** At `TerminatorKind::Call`, inspects constant generic arguments whose `param_def.def_id` carries `#[rustc_panics_when_zero]` (`find_attr!(tcx, param_def.def_id, RustcPanicsWhenZero)`) and emits `UNCONDITIONAL_PANIC` whenever `ct.try_to_target_usize(tcx) == Some(0)`.

#### 3.4 Live 16-Case `KnownPanicsLint` Empirical Boundary Matrix

Executed on `rustc 1.98.0-nightly` (`14210df0e27c`) in three configurations (`-C overflow-checks=on`, `-C opt-level=3 -C overflow-checks=off`, and `-W unconditional_panic -W arithmetic_overflow`); **both debug and `-O3 -C overflow-checks=off` produced the exact same 9 diagnostics** (`probe_results.json`):

| Case | Function (`SRC_KNOWN_PANICS`) | Pattern Tested | Debug (`overflow-checks=on`) | Release (`-O3 -C overflow-checks=off`) | Exact Mechanism (`known_panics_lint.rs`) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| K1 | `div_zero_straight` | `let d = 1 - 1; 42 / d` | **ERR** `unconditional_panic` | **ERR** `unconditional_panic` | `check_assertion` (`DivisionByZero`) |
| K2 | `array_oob_straight` | `arr[3]` on `[u32; 3]` | **ERR** `unconditional_panic` | **ERR** `unconditional_panic` | `check_assertion` (`BoundsCheck { 3, 3 }`) |
| K3 | `add_overflow_straight` | `255u8 + 1u8` | **ERR** `arithmetic_overflow` | **ERR** `arithmetic_overflow` | `check_binary_op` (`wrapping_to_overflowing`) |
| K4 | `shift_overflow_symbolic_lhs(x: u32)` | `x << 32u32` (unknown `x`) | **ERR** `arithmetic_overflow` | **ERR** `arithmetic_overflow` | `check_binary_op:351-374` (symbolic LHS) |
| K5 | `neg_overflow_straight` | `-i8::MIN` | **ERR** `arithmetic_overflow` | **ERR** `arithmetic_overflow` | `check_unary_op:316-333` (`0 - arg`) |
| K6 | `div_overflow_signed` | `i32::MIN / -1` | **ERR** `unconditional_panic` | **ERR** `unconditional_panic` | `check_assertion:509-513` (`Overflow(Div)`) |
| K7 | `cross_block_mut_div_zero(cond)` | `if cond { d = 0 } else { d = 0 }; 42 / d` | **0 panic/ovf diags** | **0 panic/ovf diags** | `OnlyInsideOwnBlock` wiped at block exit (`lines 828-840`) |
| K8 | `cross_block_ssa_div_zero(cond)` | Single-write `d = 1 - 1` across `if cond` | **ERR** `unconditional_panic` | **ERR** `unconditional_panic` | `FullConstProp` survives across blocks |
| K9 | `dead_const_branch_div_zero` | `if false { 42 / (1 - 1) } else { 7 }` | **0 diags** | **0 diags** | `SwitchInt` constant folding skips `then` (`lines 759-769`) |
| K10 | `runtime_branch_div_zero(cond)` | `if cond { 42 / (1 - 1) } else { 7 }` | **ERR** `unconditional_panic` | **ERR** `unconditional_panic` | Unknown `discr` pushes all successors (`line 819`) |
| K11 | `async_coro_div_zero` (`async fn`) | `42 / (1 - 1)` inside `async fn` | **0 diags** | **0 diags** | Skipped by `tcx.is_coroutine` (`lines 51-54`) |
| K12 | `repeat_array_div_zero` | `let a = [0u32; 4]; 42 / a[0]` | **0 diags** | **0 diags** | `Rvalue::Repeat` returns `None` (`lines 604-607`) |
| K13 | `aggregate_array_div_zero` | `let a = [0u32, 1, 2, 3]; 42 / a[0]` | **ERR** `unconditional_panic` | **ERR** `unconditional_panic` | `Rvalue::Aggregate` propagates fields (`lines 588-602`) |
| K14 | `addr_taken_div_zero` | `let d = 0; let _r = &d; 42 / d` | **0 diags** | **0 diags** | `SharedBorrow` -> `NoPropagation` (`line 980`) + `remove_const` (`line 434`) |
| K15 | `union_div_zero` | `U { a: 0 }; unsafe { 42 / u.a }` | **0 diags** | **0 diags** | `ty.is_union()` -> `NoPropagation` (`lines 900-904`) |
| K16 | `large_local_div_zero` | `struct Big { d: u32, pad: [u8; 1020] }` (`1024 B`) | **0 diags** | **0 diags** | `layout.size < 1024` strict inequality fails at `1024 B` (`line 907`) |

---

### 4. `FunctionItemReferences`: Zero-Sized `FnDef` Reference vs. `fn()` Pointer Cast

*Basis: normative (`rust-lang/reference` `c9cc32825b03`, `type.fn-item`, `type.fn-pointer`) + source (`function_item_references.rs`) + execution (`rustc 1.98.0-nightly`, cross-checked against `1.102.0-nightly`) + derived (Lean `v4.34.1` proofs).*

#### 4.1 Normative Type Distinction and Runtime Pointer-Identity Collapse

Per the Rust Reference (`src/types/function-item.md` rules `type.fn-item.intro`, `type.fn-item.unique`, `type.fn-item.coercion`, and `src/types/function-pointer.md` rule `type.fn-pointer.intro`):
- Naming a function item (`sample_fn`) yields a **zero-sized value** of a unique anonymous **function item type** (`ty::FnDef(def_id, args)`), carrying function identity purely in the type system with `size == 0` and `align == 1`.
- Taking `&sample_fn` does **not** coerce `sample_fn` to a function pointer; it produces a reference `&fn(u32) -> u32 {sample_fn}` to a zero-sized temporary (typically constant-promoted to a `&'static` ZST reference!).
- Coercing via `sample_fn as fn(u32) -> u32` creates an actual pointer-sized function pointer (`ty::FnPtr`, 8 bytes on `x86_64`) holding the address of `sample_fn`'s machine code in `.text`.

**Live runtime proof (`probe_results.json`, `function_item_addr_bin`):**
Compiling and executing two distinct `#[inline(never)]` functions (`fn_alpha`, `fn_beta`) on `rustc 1.98.0-nightly` (`x86_64-unknown-linux-gnu`) yields:
```text
ZST_SIZE=0 PTR_SIZE=8 REF_EQUAL=true PTR_EQUAL=false
REF_ALPHA=0x1 REF_BETA=0x1
PTR_ALPHA=0x56519ba70070 PTR_BETA=0x56519ba70060
```
Both `&fn_alpha` and `&fn_beta` format identically as **`0x1`** (the canonical non-null 1-byte-aligned dangling ZST pointer address!), completely losing function identity, whereas `fn_alpha as fn(u32) -> u32` and `fn_beta as fn(u32) -> u32` yield distinct `.text` addresses.

#### 4.2 Pass Implementation (`function_item_references.rs:11-189`)

Scheduled in `mir_built` (`lib.rs:425`), `FunctionItemReferences` iterates over every basic block's terminator and inspects `TerminatorKind::Call { func, args, .. }` when `!args.is_empty()` and `func.ty(body, tcx)` is `ty::FnDef(def_id, args_ref)`:

1. **`core::mem::transmute` branch (`lines 50-58`):** When `tcx.is_diagnostic_item(sym::transmute, def_id)` holds, walks every reachable component type in `args[0].node.ty(body, tcx).walk()` and emits `FUNCTION_ITEM_REFERENCES` whenever `is_fn_ref(inner_ty)` succeeds (`ty::Ref(_, ty::FnDef(..), _)` or `ty::RawPtr(ty::FnDef(..), _)` at `lines 127-142`).
2. **`fmt::Pointer` generic-bound branch (`lines 60-65, 73-123`):**
   - In `14210df0e27c` and `3ef0c22cdb86`: iterates `param_env.caller_bounds().all_clauses(tcx)` and checks `is_pointer_trait` (`ClauseKind::Trait` with `tcx.is_diagnostic_item(sym::Pointer, predicate.def_id())`).
   - In HEAD `ce66487ebbd7` (`lines 80-91`): uses `param_env.caller_bounds().trait_clauses(self.tcx).with_polarity(ty::ClausePolarity::Positive).for_trait(pointer_trait)`, explicitly restricting to positive `fmt::Pointer` bounds.
   - For each argument type `arg_def` in the callee's uninstantiated signature, walks `arg_def.walk()`, matches `inner_ty == bound_ty`, instantiates `EarlyBinder::bind(tcx, inner_ty).instantiate(tcx, args_ref)`, and checks `is_fn_ref(instantiated_ty)`.
   - **Macro span rescue (`lines 98-104`):** Because `format!("{:p}", &sample_fn)` expands into `core::fmt::rt::Argument::new_pointer(&&sample_fn)` inside macro-expanded tokens, if `span.from_expansion()` holds, `span = span.with_ctxt(span.source_callsite().ctxt())` restores the user callsite's hygiene context so the lint is not suppressed as macro-internal.
3. **Diagnostic suggestion (`emit_lint`, `lines 148-188`):** Synthesizes `{ident}[::<{params}>] as [unsafe ][extern <abi> ]fn(_, ...[, ...])[ -> _]` (with `Applicability::Unspecified` in `diagnostics.rs:163-172`).

#### 4.3 Live Empirical Matrix (`FunctionItemReferences`)

| Case | Expression (`SRC_FN_ITEM_REFS`) | Live `rustc 1.98.0-nightly` | Code Path (`function_item_references.rs`) |
| :--- | :--- | :--- | :--- |
| F1 | `format!("{:p}", &sample_fn)` | **WARN** `function_item_references` (line 18) | `check_bound_args` (`fmt::Pointer` + macro span rescue) |
| F2 | `format!("{:p}", sample_fn as fn(u32) -> u32)` | 0 warnings | `ty::FnPtr` rejected by `is_fn_ref` |
| F3 | `accept_ptr(&sample_fn)` (`P: fmt::Pointer`) | **WARN** `function_item_references` (line 28) | `check_bound_args` (`fmt::Pointer` positive clause) |
| F4 | `transmute::<&_, usize>(&sample_fn)` | **WARN** `function_item_references` (line 33) | `sym::transmute` -> `is_fn_ref` (`ty::Ref(_, FnDef)`) |
| F5 | `transmute::<fn(u32) -> u32, usize>(sample_fn as ...)` | 0 warnings | `ty::FnPtr` rejected by `is_fn_ref` |
| F6 | `let p: *const _ = &f; transmute::<*const _, usize>(p)` | **WARN** `function_item_references` (line 45) | `sym::transmute` -> `is_fn_ref` (`ty::RawPtr(FnDef)`) |
| F7 | `format!("{:p}", &generic_fn::<u64>)` | **WARN** `function_item_references` (line 50) | `emit_lint` formats turbofish `generic_fn::<u64> as fn(_) -> _` |

---

### 5. `LintTailExprDropOrder`: Edition 2021 -> 2024 `DropsReachable` Dataflow and Significant-Destructor Reversal

*Basis: normative (`rust-lang/reference` `c9cc32825b03`, `destructors.scope.temporary.edition2024`) + source (`lint_tail_expr_drop_order.rs`, `significant_drop_order.rs`, `builder/scope.rs`, `cleanup_post_borrowck.rs`) + execution (`rustc 1.98.0-nightly`, cross-checked against `1.102.0-nightly`) + derived (Lean `v4.34.1` proofs).*

#### 5.1 Normative Edition 2021 vs. Edition 2024 Tail-Expression Rule

Under `rust-lang/reference` (`src/destructors.md:279, 287-289`, rule `destructors.scope.temporary.edition2024`):
- **Edition 2021:** Temporaries created in the tail expression of a block (such as `Guard("temp", log)` in `let _local = Guard("local", log); Guard("temp", log).val()`) live into the enclosing statement/function scope and drop **after** the block's local variables (`ORDER = ["local", "temp"]`).
- **Edition 2024:** The entirety of a block's tail expression forms a temporary scope; temporaries in the tail expression drop **immediately after** the tail expression is evaluated and **before** the block's local variables (`ORDER = ["temp", "local"]`).

#### 5.2 Exact MIR Representation (`BackwardIncompatibleDropHint`) and `DropsReachable` Dataflow

1. **BID Emission in MIR Building (`compiler/rustc_mir_build/src/builder/scope.rs:435, 1177, 1919`):** On pre-2024 editions, MIR building inserts `StatementKind::BackwardIncompatibleDropHint { place, reason: BackwardIncompatibleDropReason::Edition2024 }` at the exact program point where `place` *will* drop in Edition 2024, while leaving the actual `TerminatorKind::Drop { place, .. }` at its Edition 2021 location.
   Live `rustc --edition=2021 -W tail-expr-drop-order -Zdump-mir=lint_tail_expr_drop_order` dump of `f`:
   ```text
   bb1: {
       BackwardIncompatibleDropHint(_3);
       drop(_1) -> [return: bb2, unwind: bb5];
   }
   bb2: {
       drop(_3) -> [return: bb3, unwind: bb6];
   }
   bb3: {
       return;
   }
   bb5 (cleanup): { drop(_1) -> [return: ..., unwind terminate(cleanup)]; }
   bb6 (cleanup): { drop(_3) -> [return: ..., unwind terminate(cleanup)]; }
   ```
   Here `_1` is `_local = Guard("local")` and `_3` is the tail temporary `Guard("temp")`.
2. **Entry Gates (`lint_tail_expr_drop_order.rs:183-228`):**
   - Skips `DefKind::SyntheticCoroutineBody` (`lines 184-187`), Edition `>= 2024` (`body.span.edition().at_least_rust_2024()`), and builds where `TAIL_EXPR_DROP_ORDER` is skippable (`tcx.skippable_lints(())`).
   - Scans every block for `StatementKind::BackwardIncompatibleDropHint { place, .. }`, keeping only BIDs whose `extract_component_with_significant_dtor(tcx, typing_env, ty)` is non-empty (`lines 211-217`), grouping candidates per block in `bid_per_block`.
3. **`MaybeInitializedPlaces` + `DropsReachable` (`lines 240-276, 47-159`):**
   - Computes `MoveData::gather_moves(body, tcx, |_| true)` and iterates `MaybeInitializedPlaces` to fixpoint.
   - For each `(block, place)` in `bid_per_block`, invokes `DropsReachable::visit(block)`:
     - At each visited block `bb`, consults `block_drop_value_info[bb]` (3-state cache: `Unknown | None | Some(MovePathIndex)`). On `Unknown`, if `terminator` is `TerminatorKind::Drop { place: dp, .. }` with a `MovePathIndex` `idx`, seeks `maybe_init.seek_before_primary_effect(Location { block, statement_index: data.statements.len() })` and marks `Some(idx)` iff `MaybeReachable::Reachable(set)` contains `idx` (`lines 76-104`).
     - Propagates `dropped_local_here` to each non-cleanup successor (`if target.is_cleanup { continue; }`, `lines 111-113`), terminating traversal along a successor if `succ == block` or `visited[succ].union(dropped_local_here)` adds no new bits (monotone set convergence on cyclic CFGs, `lines 117-131`).
     - When a successor's terminator is `TerminatorKind::Drop { place: dropped_place, .. }` satisfying `place_has_common_prefix(dropped_place, self.place)` (`lines 132-154`), unions `dropped_local_there` into `collected_drops`, records `drop_span`, and **stops descending past that drop point**.
4. **Observer Exclusions & Ecosystem Allowlist (`lines 278-354` & `significant_drop_order.rs:14-103`):**
   Subtracts from `all_locals_dropped`:
   - **(a) Return place `_0`** (`dropped_local == Local::ZERO`, `lines 293-297`) — moved out to caller, not reordered against tail temporaries;
   - **(b) Closure captures** (`is_closure_like && matches!(dropped_local, ty::CAPTURE_STRUCT_LOCAL)`, `lines 301-305`) — captures drop last by closure-capture lifetime contract;
   - **(c) BID descendants** (`place_descendent_of_bids`, `lines 164-180, 320-324`) — projections of a BID local itself;
   - **(d) Non-significant destructors** (`extract_component_with_significant_dtor` empty, `lines 327-337`), where `true_significant_drop_ty` (`significant_drop_order.rs:41-67`) explicitly treats `syn::*`, `proc_macro2::*`, `{core,std}::task::{wake::,}{LocalWaker,Waker}`, `tracing::instrument::Instrumented`, and `bytes::Bytes` as trivial (`smallvec![]`), and delegates `hashbrown::raw::{RawTable, RawIntoIter, RawDrain}` to their element type `T`;
   - **(e) Same-local BID self-exclusion** (`lines 342-348`): if all BIDs in the block point into one local, excludes that local from `all_locals_dropped`.
   If `all_locals_dropped` remains non-empty, emits `TAIL_EXPR_DROP_ORDER` with fresh `#1`, `#2`, ... names for anonymous temporaries (`assign_observables_names`, `lines 477-499`, filtering out compiler-desugared local names in `3ef0c22cdb86` at `line 468`).

#### 5.3 Live Edition 2021 vs. 2024 Execution & Exclusion Matrix

| Probe (`probe_results.json`) | Edition / Flags | `tail_expr_drop_order` Diagnostics | Binary Execution Output |
| :--- | :--- | :--- | :--- |
| `tail_drop_bin_ed2021` (`f` with `Guard("local")`, `Guard("temp")`) | `--edition=2021 -W tail-expr-drop-order` | **1 warning** (`#1` temp dropped earlier vs. `_local` dropped later; drop span at block closing brace) | `V=42 ORDER=["local", "temp"]` (matches `1.102.0-nightly` verbatim) |
| `tail_drop_bin_ed2024` (same source) | `--edition=2024 -W tail-expr-drop-order` | **0 warnings** (`at_least_rust_2024()`) | `V=42 ORDER=["temp", "local"]` (matches `1.102.0-nightly` verbatim) |
| `E1: sig_temp_and_sig_local` | `--edition=2021 -W tail-expr-drop-order` | **1 warning** (`#1` vs. `_local`) | — (lib) |
| `E2: sig_temp_trivial_local` (`Trivial` local) | `--edition=2021 -W tail-expr-drop-order` | **0 warnings** (excluded by `d)`) | — (lib) |
| `E3: trivial_temp_sig_local` (`Trivial` temp) | `--edition=2021 -W tail-expr-drop-order` | **0 warnings** (BID filtered at `line 214`) | — (lib) |
| `E4: moved_local_no_drop` (local returned via `_0`) | `--edition=2021 -W tail-expr-drop-order` | **0 warnings** (excluded by `a)` + `MaybeInitializedPlaces`) | — (lib) |
| `E5: closure_capture_excluded` (`move \|\|`) | `--edition=2021 -W tail-expr-drop-order` | **0 warnings** (excluded by `b)` `CAPTURE_STRUCT_LOCAL`) | — (lib) |

---

### 6. Kernel-Checked Lean 4 (`v4.34.1`) Mechanization (`support/CheckRecursionKnownPanicsAndTailDropLintSoundness.lean`)

*Basis: derived (kernel-checked Lean `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`).*

The standalone zero-import module `support/CheckRecursionKnownPanicsAndTailDropLintSoundness.lean` (`1,862` total lines, `1,689` non-blank lines, SHA-256 `6ab1f3e7e8484114ee9bcce60598dbe5e093ae948d13443741ec1e3f88b6357c`, `25` inductives, `5` structures, `72` total defs, `46` explicit theorems) compiles with exit code `0` under `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`. Every recursive function is expressed directly via `Nat.rec`, `List.foldr`, or `List.foldl` (zero `partial def`, zero `deriving` on recursive/container inductives), achieving a strictly clean environment audit:

- **`UNSAFE_REC_COUNT = 0`** (zero `._unsafe_rec` constants anywhere in the module)
- **`IS_UNSAFE_COUNT = 0`**, **`IS_PARTIAL_COUNT = 0`**, **`NONCOMPUTABLE_COUNT = 0`**
- **`USED_AXIOMS = [propext]`** (`0` `Classical.choice`, `0` `Quot.sound`, `0` `sorryAx`, `0` `Lean.ofReduceBool`, `0` `Lean.trustCompiler`)
- **`0` occurrences of `sorry`, `omega`, `bv_decide`, `native_decide`, `partial def`, `axiom`, or `admit`** in code.

#### 6.1 Summary Table of Key Mechanized Theorems

| Theorem (`RustcMirLintSoundness.*`, exact line) | Subsystem | Exact Formal Statement Summary | Axioms Used |
| :--- | :--- | :--- | :--- |
| `triColorBackEdge_false_negative_witness` (`L481`) | `CheckCallRecursion` | For every initial counter `i0 : Nat`, `runBoundedLoop 10 0 i0 = .hitSelfRecursion 3`, AND `checkRecursionRustc boundedLoopCfg 30 = some .nonRecursive`. | `[propext]` |
| `triColorBackEdge_drop_false_negative_witness` (`L503`) | `CheckDropRecursion` | `checkRecursionRustc loopBadDropCfg 30 = some .nonRecursive` (same back-edge suppression on `Drop`). | `[propext]` |
| `tailCall_pure_become_silent` (`L554`) | `CheckCallRecursion` (`TailCall`) | `checkRecursionRustc pureBecomeCfg 10 = some .silentNoRecCalls` (`0` warnings). | `[propext]` |
| `tailCall_mixed_become_highlights_only_call` (`L560`) | `CheckCallRecursion` (`TailCall`) | `checkRecursionRustc mixedBecomeAndCallCfg 20 = some (.warn [2])` (only `else` `Call` block `2` highlighted). | `[propext]` |
| `tailCall_nonrecursive_become_false_positive_witness` (`L579`) | `CheckCallRecursion` (`TailCall`) | `∀ b x, evalBecomeOtherOrSelf 2 b x = some (x + 1)` AND `ReachesGenuineEscape becomeOtherOrSelfCallCfg 0` AND `checkRecursionRustc becomeOtherOrSelfCallCfg 20 = some (.warn [2])`. | `[propext]` |
| `sccRecursionCheck_sound_for_loop_terminating_executions` (`L701`) | SCC Condensation | If `SccUnconditionalRecursion scc` holds for valid condensation `scc`, then `¬ ReachesGenuineEscape cfg cfg.startBlock` (no finite loop-exiting path reaches any genuine escape). | `[propext]` |
| `sccRecursionCheck_complete_on_terminating_loops` (`L820`) | SCC Condensation | `SccUnconditionalRecursion boundedLoopScc` holds (detects unconditional recursion through may-exit loop SCC `{bb1, bb2}`). | `[propext]` |
| `sccRecursionCheck_silent_on_pure_infinite_loop` (`L904`) | SCC Condensation | `¬ SccUnconditionalRecursion pureInfiniteLoopScc` (closed nontrivial SCC `loop {}` is an escape sink, staying silent). | `[propext]` |
| `fixedTailCallCheck_eliminates_false_positive` (`L953`) | `TailCall` Repair | `triColorRunFixedTailCall` returns `.nonRecursive` on `becomeOtherOrSelfCallCfg`, `.silentNoRecCalls` on `pureBecomeCfg`, and `.warn [2]` on `mixedBecomeAndCallCfg`. | `[propext]` |
| `absStep_preserves_refinement` (`L1239`) | `KnownPanicsLint` | Every abstract statement transfer (`storageDead`, `refTake` poison, `repeatUnknown` nuke, `use`, `binOp`, `mkPair`, `projField0` gated by `ConstPropMode`) preserves `EnvRefines` and `NoPropIsUninit`. | `[propext]` |
| `knownPanics_constProp_implies_runtime_assert_fail` (`L1371`) | `KnownPanicsLint` | Whenever `checkAssertionLint` fires after propagating a block from an entry state refining `c0`, `RuntimeAssertFails (runConcStmts unk ss c0) cond expected` holds for all concrete executions. | `[propext]` |
| `knownPanics_shift_overflow_symbolic_lhs_sound` (`L1408`) | `KnownPanicsLint` | Whenever `checkShiftOverflowLint widthBits a rhs = true`, `∀ lhs : Int, ConcreteShiftOverflows widthBits lhs (evalConcOp c rhs)` holds regardless of unknown LHS. | `[propext]` |
| `knownPanics_onlyInsideOwnBlock_wipes_join` (`L1429`) | `KnownPanicsLint` | Clearing `writtenOwnBlock` at block exit resets `OnlyInsideOwnBlock` local `1` to `.uninit`, making join-block `checkAssertionLint` return `false`. | `[propext]` |
| `knownPanics_dead_const_branch_pruned` (`L1452`) | `KnownPanicsLint` | Constant `SwitchInt` discriminant `false` / `true` restricts `switchWorklistTargets` to `[bbFalse]` / `[bbTrue]`. | `[propext]` |
| `fnItemRef_loses_identity_fnPtr_preserves_identity` (`L1508`) | `FunctionItemReferences` | For any injective `codeAddr` and `id1 ≠ id2`, `(FnRefTy.fnDef id1).sizeBytes = 0`, `evalPtrAddress codeAddr (.refOfFnDef id1) = evalPtrAddress codeAddr (.refOfFnDef id2)`, and `evalPtrAddress codeAddr (.coercedFnPtr id1) ≠ evalPtrAddress codeAddr (.coercedFnPtr id2)`. | `[]` (0 axioms) |
| `fnItemRefLint_sound_and_complete_on_pointer_and_transmute` (`L1538`) | `FunctionItemReferences` | Fires on `Ref(FnDef)` and `RawPtr(FnDef)` for `transmute` and positive `fmt::Pointer`, and returns `none` for `FnPtr` casts and negative `!fmt::Pointer` bounds. | `[propext]` |
| `dropsReachable_sound_for_significant_dtor_swap` (`L1751`) | `LintTailExprDropOrder` | When `bidPlace` and intervening `pLocal` (`pLocal ≠ bidPlace`, `bidPlace ∉ xs`) both have `hasSigDtor = true`, Edition 2021 satisfies `AppearsBefore pLocal bidPlace`, Edition 2024 satisfies `AppearsBefore bidPlace pLocal`, and the two observable traces are strictly unequal. | `[propext]` |
| `dropsReachable_complete_when_no_intervening_sig_drop` (`L1804`) | `LintTailExprDropOrder` | If every intervening place in `xs` has `hasSigDtor = false`, Edition 2021 and Edition 2024 produce identical observable significant-destructor traces. | `[]` (0 axioms) |
| `dropsReachable_ed2021_vs_ed2024_concrete_witness` (`L1850`) | `LintTailExprDropOrder` | On `concreteTedoBody` (mirroring the dumped MIR of `f`), `lintTailExprDropOrder` returns `[1]` on Edition 2021 and `[]` on Edition 2024, with traces `[1, 3]` vs. `[3, 1]` and `InterveningDrops` witness `[1]`. | `[propext]` |

#### 6.2 Verbatim Key Lean Statements

```lean
-- support/CheckRecursionKnownPanicsAndTailDropLintSoundness.lean:481-483
theorem triColorBackEdge_false_negative_witness :
    (∀ i0 : Nat, runBoundedLoop 10 0 i0 = .hitSelfRecursion 3) ∧
    checkRecursionRustc boundedLoopCfg 30 = some .nonRecursive

-- support/CheckRecursionKnownPanicsAndTailDropLintSoundness.lean:579-582
theorem tailCall_nonrecursive_become_false_positive_witness :
    (∀ b : Bool, ∀ x : Nat, evalBecomeOtherOrSelf 2 b x = some (x + 1)) ∧
    ReachesGenuineEscape becomeOtherOrSelfCallCfg 0 ∧
    checkRecursionRustc becomeOtherOrSelfCallCfg 20 = some (.warn [2])

-- support/CheckRecursionKnownPanicsAndTailDropLintSoundness.lean:701-705
theorem sccRecursionCheck_sound_for_loop_terminating_executions {cfg : RecCfg}
    (scc : SccCondensation cfg)
    (hStart : cfg.startBlock < cfg.numBlocks)
    (hCheck : SccUnconditionalRecursion scc) :
    ¬ ReachesGenuineEscape cfg cfg.startBlock

-- support/CheckRecursionKnownPanicsAndTailDropLintSoundness.lean:820-821
theorem sccRecursionCheck_complete_on_terminating_loops :
    SccUnconditionalRecursion boundedLoopScc

-- support/CheckRecursionKnownPanicsAndTailDropLintSoundness.lean:1371-1377
theorem knownPanics_constProp_implies_runtime_assert_fail
    (modes : Nat → ConstPropMode) (ss : List KPStmt) (st0 : AbsBlockState) (c0 : ConcEnv)
    (unk : ConcVal) (cond : KPOperand) (expected : Bool)
    (href0 : EnvRefines st0.env c0)
    (hnp0 : NoPropIsUninit modes st0.env)
    (hLint : checkAssertionLint (runAbsStmts modes ss st0).env cond expected = true) :
    RuntimeAssertFails (runConcStmts unk ss c0) cond expected

-- support/CheckRecursionKnownPanicsAndTailDropLintSoundness.lean:1751-1761
theorem dropsReachable_sound_for_significant_dtor_swap
    (b : TedoBody) (bidPlace pLocal : Nat) (xs : List Nat)
    (hSigTemp : b.hasSigDtor bidPlace = true)
    (hSigLocal : b.hasSigDtor pLocal = true)
    (hMem : pLocal ∈ xs)
    (hNe : pLocal ≠ bidPlace)
    (hNotInXs : bidPlace ∉ xs) :
    AppearsBefore pLocal bidPlace (filterSigDrops b (ed2021DropSequence xs bidPlace)) ∧
    AppearsBefore bidPlace pLocal (filterSigDrops b (ed2024DropSequence xs bidPlace)) ∧
    filterSigDrops b (ed2021DropSequence xs bidPlace) ≠
      filterSigDrops b (ed2024DropSequence xs bidPlace)
```

## Boundaries

1. **Undecidability of Loop Termination in SCC-Condensation Recursion Detection (`known not to apply` / Rice-theorem boundary):**
   - `sccRecursionCheck_sound_for_loop_terminating_executions` proves absence of finite loop-exiting escapes (`¬ ReachesGenuineEscape`), NOT absence of runtime divergence inside a may-exit loop. For a function whose may-exit loop actually diverges dynamically (`while runtime_always_true() {} recurse()`), the SCC-condensation criterion flags `unconditional_recursion` even though `recurse()` is never reached at runtime. Distinguishing terminating from non-terminating may-exit loops in general is undecidable; `rustc`'s `TriColorDepthFirstSearch` chooses zero false positives on diverging loops at the cost of false negatives on every bounded loop, whereas SCC-condensation chooses completeness on terminating loops at the cost of warning on dynamically diverging may-exit loops unless paired with a loop-termination certificate.
2. **Mutual Recursion and Indirect Calls (`unsupported` in `CheckCallRecursion`):**
   - `CallRecursion` is strictly intra-procedural (`FIXME(#57965)` at `check_call_recursion.rs:160`) and matches only direct `ty::FnDef` callees (`line 145`). Mutual recursion (`mutual_a <-> mutual_b`), recursion through `fn()` pointers, `dyn Fn`, and trait-object drop glue (`dyn Trait`) are **known not to apply** to `CheckCallRecursion` / `CheckDropRecursion`.
3. **Live Execution of `rustc` `ce66487ebbd7` and `#[rustc_panics_when_zero]` (`not examined` dynamically):**
   - Local live execution ran on `rustc 1.98.0-nightly` (`14210df0e27c`), while `3ef0c22cdb86` (`1.102.0-nightly`) was source-audited and cross-checked against recorded diagnostic traces, and `ce66487ebbd7` (`main` on `2026-11-22`) was source-audited only. The `#[rustc_panics_when_zero]` (`ConstNIsZero`) code path (`known_panics_lint.rs:772-803`, added between `14210df0e27c` and `3ef0c22cdb86`) and negative `!fmt::Pointer` polarity filtering (`function_item_references.rs:80-91`, added between `3ef0c22cdb86` and `ce66487ebbd7`) were verified by primary-source inspection only, **not examined** by live compiler execution on `1.102.0-nightly` or `ce66487ebbd7`.
4. **Coroutines, Statics, Consts, and Generic Polymorphic Bodies in `KnownPanicsLint` (`known not to apply` / `unsupported`):**
   - `KnownPanicsLint` explicitly skips `AnonConst`, `Const`, `Static`, and all coroutines (`async fn`, `gen fn`, `#[coroutine]`), and bails out on operands/rvalues containing generic parameters (`has_param()`, `lines 255, 455`) or unsized rvalues (`line 458`). In addition, `knownPanics_constProp_implies_runtime_assert_fail` establishes that reaching a flagged `Assert` implies a runtime panic—**not** that the enclosing function unconditionally executes that branch (e.g., `runtime_branch_div_zero(false)` returns `7` without panicking even though `KnownPanicsLint` rejects the `if cond { 42 / (1 - 1) }` branch).
5. **Unwinding / Cleanup-Pad Reordering and Macro-Span Per-Block Editions in `LintTailExprDropOrder` (`known not to apply` / `not examined`):**
   - `DropsReachable::visit` explicitly skips `target.is_cleanup` blocks (`lint_tail_expr_drop_order.rs:111-113`), so drop-order reversals observable **only** during panic unwinding along cleanup pads are **known not to apply** to `tail_expr_drop_order`.
   - `LintTailExprDropOrder` checks only `tail_expr_drop_order` (`BackwardIncompatibleDropReason::Edition2024` tail expressions); `if let` temporary-scope narrowing (`if_let_rescope`), per-block hygiene across mixed-edition macros, and `dyn Trait` destructor execution were **not examined** empirically in `probe_check_recursion_known_panics_and_tail_drop_lint.py`.
   - The `true_significant_drop_ty` allowlist (`significant_drop_order.rs:41-67`) matches crate/module path names heuristically; a user crate named `bytes` defining `struct Bytes` with a side-effectful `Drop` is silently treated as trivial by the lint (known heuristic boundary of the source implementation; not executed).
6. **Lean Model Boundaries (`known not to apply` to full Rust semantics):**
   - `CheckRecursionKnownPanicsAndTailDropLintSoundness.lean` models integer/boolean scalars and 2-field pairs (no floating-point `NaN`/rounding, no fixed-width wrap-around bitvectors, no heap pointers/aliasing, no unwind stack frames), and models `DropsReachable` on explicit `MaybeInit` boolean tables rather than mechanizing `rustc_mir_dataflow::impls::MaybeInitializedPlaces` fixpoint computation itself. **Attractive stronger conclusion rejected:** passing Lean verification of these four lint models does **not** prove `rustc`'s Rust implementations bug-free or connect them mechanically to `joshlf/anneal`'s `Trusted.MirSemantics`.
7. **Target Architecture Scope (`not examined` beyond `x86_64-unknown-linux-gnu`):**
   - All live `rustc` executions and `REF_ALPHA=0x1` vs. `PTR_ALPHA` measurements ran on `x86_64-unknown-linux-gnu`. While `FnDef` ZST layout (`align = 1`, dangling promoted address `0x1`) is target-independent across Rust targets, `PTR_SIZE = 8` applies specifically to 64-bit targets (`4` on 32-bit targets; not executed on non-`x86_64` hosts).

## Evidence

### Primary Upstream Sources Audited

All commit SHAs below were resolved live against GitHub on `2026-11-22`:

1. **`rust-lang/rust`** (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `2026-05-31`; `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `2026-11-11`; `ce66487ebbd7541212d22d01c39a808057d69f1f`, `2026-11-22`):
   - `compiler/rustc_mir_transform/src/check_call_recursion.rs`: `CheckCallRecursion` (`L16-35`), `CheckDropRecursion` (`L38-62`), `check_recursion` (`L64-93`), `CallRecursion` (`L114-172`), `RecursiveDrop` (`L174-186`), `Search` / `TriColorVisitor` (`L188-272`, specifically back-edge break `L198-201`, `TailCall` `L236` & `FIXME` `L244-254`, `ignore_edge` `L259-271`).
   - `compiler/rustc_data_structures/src/graph/iterate/mod.rs`: `NodeStatus` (`L172-186`), `TriColorDepthFirstSearch::run_from` (`L214-289`), `TriColorVisitor` (`L308-344`).
   - `compiler/rustc_mir_transform/src/known_panics_lint.rs`: `KnownPanicsLint::run_lint` (`L29-63`), `ConstPropagator` & `Value` (`L67-149`), `ConstPropagator::new` (`L182-201`, simplified at `ce66487ebbd7:L184`), `check_unary_op` (`L313-337`), `check_binary_op` (`L339-400`), `check_rvalue` (`L402-465`), `check_assertion` (`L467-526`), `eval_rvalue` (`L542-665`), `Visitor` impl (`L668-853`, including `SwitchInt` `L759-771`, `ConstNIsZero` `L772-803` in `3ef0c22cdb86`/`ce66487ebbd7`, and `written_only_inside_own_block_locals` wipe `L822-852`), `MAX_ALLOC_LIMIT = 1024` (`L858`), `ConstPropMode` & `CanConstProp` (`L862-994`).
   - `compiler/rustc_const_eval/src/const_eval/dummy_machine.rs`: `DummyMachine` (`L34-213`, `ALL_CONSTS_ARE_PRECHECKED = false`, `before_access_global`, `binary_ptr_op`, `runtime_checks`).
   - `compiler/rustc_mir_transform/src/function_item_references.rs`: `FunctionItemReferences` (`L11-20`), `check_terminator` (`L31-69`), `check_bound_args` (`L73-112`, positive-polarity refactor in `ce66487ebbd7:L80-91`), `is_fn_ref` (`L127-142`), `emit_lint` (`L148-188`).
   - `compiler/rustc_mir_transform/src/lint_tail_expr_drop_order.rs`: `place_has_common_prefix` (`L31-34`), `MovePathIndexAtBlock` & `DropsReachable::visit` (`L38-159`), `place_descendent_of_bids` (`L164-180`), `run_lint` (`L183-460`), `collect_user_names` (`L463-474`), `assign_observables_names` (`L477-499`), diagnostic structs (`L501-566`).
   - `compiler/rustc_middle/src/ty/significant_drop_order.rs`: `true_significant_drop_ty` (`L14-71`), `extract_component_raw` (`L76-103`), `extract_component_with_significant_dtor` (`L106-115`), `ty_dtor_span` (`L121-160`).
   - `compiler/rustc_mir_transform/src/lib.rs`: `mir_built` (`L395-433`), `mir_promoted` (`L436-498`, `lint_tail_expr_drop_order::run_lint` at `L494`), `run_analysis_cleanup_passes` (`L642-652`, `PostAnalysisNormalize` moved here at `ce66487ebbd7:L655`), `run_runtime_lowering_passes` (`L655-679`), `run_runtime_cleanup_passes` (`L682-696`).
   - `compiler/rustc_mir_transform/src/pass_manager.rs`: `PassPolicy` (`L88-100`), `MirLint` & `Lint<T>` (`L174-205`).
   - `compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs`: `StatementKind::BackwardIncompatibleDropHint` turned into `Nop` (`L36`).
   - `compiler/rustc_mir_transform/src/diagnostics.rs`: `UnconditionalRecursion` (`L16-21`), `AssertLint` / `AssertLintKind` (`L89-113`), `ConstNIsZero` (`L130-134`), `FnItemRef` (`L163-172`).
   - `compiler/rustc_mir_build/src/builder/scope.rs`: `BackwardIncompatibleDropHint` emission (`L435, L1177, L1919`).
2. **`rust-lang/reference`** (`c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`, `2026-11-17`):
   - `src/destructors.md` (`L261-290`: `destructors.scope.temporary.enclosing`, `destructors.scope.temporary.edition2024`).
   - `src/types/function-item.md` (`L1-54`: `type.fn-item.intro`, `type.fn-item.unique`, `type.fn-item.coercion`).
   - `src/types/function-pointer.md` (`L1-66`: `type.fn-pointer.intro`, `type.fn-pointer.coercion`).
3. **`joshlf/anneal`** (`c131b320eeeb26ef692e5afd5ec8db49ee518613`, `2026-11-19`):
   - `trusted/lean/Trusted/MirAst.lean` (`L53`, `L70-95`, `L732-815`).
   - `trusted/lean/Trusted/MirSemantics.lean` (`L178`, `L1646-1698`).
   - `trusted/correspondence/Trusted/Correspondence.lean` (`L1317`: `phase := .Runtime .PostCleanup`).
   - `trusted/rustc-capture/src/driver.rs` (`L25`, `L75-84`).

### Preserved Package Support Artifacts

All evidence scripts, recorded execution results, and kernel-checked Lean proofs are stored inside this package under `support/`:

| File | Purpose | Size / Metric | SHA-256 |
| :--- | :--- | :--- | :--- |
| `support/probe_check_recursion_known_panics_and_tail_drop_lint.py` | Self-contained Python 3.10+ differential `rustc` probe suite covering all 4 lints, Edition 2021 vs. 2024 binary execution, `&FnDef` vs. `fn()` address execution, `become` false-positive binary execution, and `-Zmir-enable-passes` toggling | Standalone stdlib script (11 probes) | `afb1bc76cd19218b7acb5a82149b5179768229d4151a5bc77c3881722b69dd00` |
| `support/probe_results.json` | Verbatim JSON output of running `probe_check_recursion_known_panics_and_tail_drop_lint.py` on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`x86_64-unknown-linux-gnu`) on `2026-11-22` | 11 probe results (JSON diagnostics + binary stdout) | `716cd9098206d00f140afd9bf677ad69cf40cb8f1be30de795640d7ec105d467` |
| `support/CheckRecursionKnownPanicsAndTailDropLintSoundness.lean` | Zero-import Lean `v4.34.1` formalization of all 4 lint subsystems and 19 headline theorems (`46` explicit theorems, `72` defs, `0` `sorry`, `0` `Classical.choice`, `0` `._unsafe_rec`, `USED_AXIOMS=[propext]`) | `1,862` lines (`1,689` non-blank) | `6ab1f3e7e8484114ee9bcce60598dbe5e093ae948d13443741ec1e3f88b6357c` |

### Exact Verification Transcripts (`2026-11-22`)

1. **Differential `rustc` execution (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`):**
   - Command: `python3 support/probe_check_recursion_known_panics_and_tail_drop_lint.py --out support/probe_results.json` -> exit code `0`.
   - Verified highlights:
     - `recursion_and_drop`: `3` `unconditional_recursion` warnings (`direct_recurse`, `BadDrop`, `both_branches_recurse`); **`0`** warnings on `bounded_loop_then_recurse` and `LoopBadDrop`.
     - `tail_call_recursion` & `tail_call_fp_bin`: `0` warnings on `pure_become`; `1` warning on `mixed_become_and_call` (line `14` only); `1` false-positive warning on `become_other_or_self_call` (line `8`/`12`), whose compiled binary exits `0` printing `R_TRUE=42 R_FALSE=42`.
     - `known_panics_debug` & `known_panics_release_no_overflow_checks`: identical `9` errors (`6` `unconditional_panic`, `3` `arithmetic_overflow`) across both `-C overflow-checks=on` and `-C opt-level=3 -C overflow-checks=off`; `0` panic/overflow diagnostics on `K7`, `K9`, `K11`, `K12`, `K14`, `K15`, `K16`.
     - `function_item_references` & `function_item_addr_bin`: `5` warnings on `F1`, `F3`, `F4`, `F6`, `F7`; `0` warnings on `F2`, `F5`; runtime binary prints `ZST_SIZE=0 PTR_SIZE=8 REF_EQUAL=true PTR_EQUAL=false REF_ALPHA=0x1 REF_BETA=0x1 PTR_ALPHA=0x56519ba70070 PTR_BETA=0x56519ba70060`.
     - `tail_drop_bin_ed2021` vs. `tail_drop_bin_ed2024`: Edition 2021 emits `tail_expr_drop_order` and prints `V=42 ORDER=["local", "temp"]`; Edition 2024 emits `0` warnings and prints `V=42 ORDER=["temp", "local"]`; `tail_drop_exclusions_ed2021` emits `1` warning (`E1` only, `0` on `E2`–`E5`).
     - `pass_toggle_default` (`returncode=1`, `2` diagnostics) vs. `pass_toggle_disabled` (`-Zmir-enable-passes=-CheckCallRecursion,-KnownPanicsLint`, `returncode=0`, `0` diagnostics).
   - Cross-check against recorded `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)` outputs: identical diagnostic codes and messages for `unconditional_recursion` on direct + `Drop` recursion, silence on loop-preceded recursion, `unconditional_panic` on div-by-zero and array-OOB, `function_item_references` on `&sample_fn`, single-callsite highlighting on `mixed_become_and_call`, and `V=42 ORDER=["local", "temp"]` (Edition 2021, `tail_expr_drop_order` emitted) vs. `V=42 ORDER=["temp", "local"]` (Edition 2024, silent).
2. **Lean `v4.34.1` kernel verification and environment purity audit:**
   - Strict check command:
     ```console
     lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
       support/CheckRecursionKnownPanicsAndTailDropLintSoundness.lean
     ```
     Exit code: `0` (zero errors, zero warnings).
   - Environment metaprogramming audit over all `979` constants in `RustcMirLintSoundness.*`:
     ```text
     TOTAL_CONSTANTS_IN_NS=979
     THEOREM_COUNT=249
     UNSAFE_REC_COUNT=0
     IS_UNSAFE_COUNT=0
     IS_PARTIAL_COUNT=0
     NONCOMPUTABLE_COUNT=0
     USED_AXIOMS=[propext]
     DISALLOWED_AXIOM_COUNT=0
     ```

## Revalidation

To revalidate all empirical and mechanized findings against a newer `rustc` nightly or a newer Lean 4 toolchain without repeating the full source crawl:

1. **Rerun the differential `rustc` probe suite (takes ~2 seconds):**
   ```console
   python3 reports/rustc-mir-check-recursion-known-panics-fn-item-refs-and-tail-drop-lint/support/probe_check_recursion_known_panics_and_tail_drop_lint.py \
     --rustc /path/to/rustc --out /tmp/reval_probe_results.json
   ```
   Key discriminating assertions to check in `/tmp/reval_probe_results.json`:
   - `probes.recursion_and_drop.diagnostics`: check whether `bounded_loop_then_recurse` (line `10`) or `LoopBadDrop` (line `41`) starts emitting `unconditional_recursion` (would indicate `TriColorDepthFirstSearch` was replaced with an SCC/loop-aware pass).
   - `probes.tail_call_fp_bin`: check whether `become_other_or_self_call` still emits `unconditional_recursion` while printing `R_TRUE=42 R_FALSE=42` (if `0` warnings, `check_call_recursion.rs:236` was fixed to distinguish non-recursive `TailCall` targets).
   - `probes.tail_call_recursion`: check whether `mixed_become_and_call` gains a second `"recursive call site"` span on the `become` line (would indicate `FIXME(explicit_tail_calls)` was resolved).
   - `probes.known_panics_debug` vs. `probes.known_panics_release_no_overflow_checks`: verify identical diagnostic sets and check whether `cross_block_mut_div_zero`, `async_coro_div_zero`, `repeat_array_div_zero`, or `large_local_div_zero` gain diagnostics (would indicate migration from `ConstPropagator` to a join-capable dataflow pass or coroutine/repeat/size-limit relaxation).
   - `probes.function_item_addr_bin`: check `REF_EQUAL=true`, `REF_ALPHA=0x1`, `PTR_EQUAL=false`.
   - `probes.tail_drop_bin_ed2021` vs. `probes.tail_drop_bin_ed2024`: check `ORDER=["local", "temp"]` + `tail_expr_drop_order` vs. `ORDER=["temp", "local"]` + `0` warnings.
   - `probes.pass_toggle_disabled`: check whether `-Zmir-enable-passes=-CheckCallRecursion,-KnownPanicsLint` still exits `0` with `0` diagnostics (would change if `Lint<T>::policy` switches to `PassPolicy::Required`).

2. **Targeted upstream source diff (fastest check for `rust-lang/rust` drift):**
   ```console
   git diff <old-sha> <new-sha> -- \
     compiler/rustc_mir_transform/src/check_call_recursion.rs \
     compiler/rustc_mir_transform/src/known_panics_lint.rs \
     compiler/rustc_mir_transform/src/function_item_references.rs \
     compiler/rustc_mir_transform/src/lint_tail_expr_drop_order.rs \
     compiler/rustc_mir_transform/src/lib.rs \
     compiler/rustc_mir_transform/src/pass_manager.rs \
     compiler/rustc_middle/src/ty/significant_drop_order.rs
   ```
   Specifically inspect `check_call_recursion.rs` around `NodeStatus::Visited` and `TerminatorKind::TailCall`, `known_panics_lint.rs` around `CanConstProp` / `written_only_inside_own_block_locals` / `is_coroutine`, `function_item_references.rs` around `check_bound_args`, and `lib.rs` around `mir_built` / `mir_promoted` / `run_runtime_lowering_passes`.

3. **Re-verify the Lean 4 mechanization (takes ~4 seconds on Lean `v4.34.1`):**
   ```console
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     reports/rustc-mir-check-recursion-known-panics-fn-item-refs-and-tail-drop-lint/support/CheckRecursionKnownPanicsAndTailDropLintSoundness.lean
   ```
   A passing exit code `0` revalidates all `46` theorems and zero-warning elaboration; re-running the `#eval` constant-map scan (checking `UNSAFE_REC_COUNT == 0`, `IS_UNSAFE_COUNT == 0`, `IS_PARTIAL_COUNT == 0`, and `USED_AXIOMS ⊆ {propext, Quot.sound}`) confirms kernel purity on a newer Lean release.

4. **Re-check Anneal TCB alignment (`joshlf/anneal`):**
   Diff `trusted/lean/Trusted/MirAst.lean` (around `TerminatorKind`) and `trusted/correspondence/Trusted/Correspondence.lean` (around `phase := .Runtime .PostCleanup`). If Anneal lowers `TerminatorKind::Drop` or `TerminatorKind::TailCall` out of `.unsupported`, re-evaluate §1.3 to document how Edition 2021 vs. Edition 2024 `Drop` order and `TailCall` frame reuse enter `Trusted.MirSemantics`.
