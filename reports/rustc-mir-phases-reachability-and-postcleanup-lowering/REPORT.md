# `rustc` MIR Phase Pipeline, `Steal<Body>` Query Hazards, Reachability Filters, Unsafe Lowering, and `Runtime(PostCleanup)` Verification Scaling

## Summary

This report synthesizes six complementary investigations into `rustc`'s Mid-level Intermediate Representation (MIR) pipeline, reachability filtering before Charon extraction, safety-relevant operation lowering, multi-version `rustc` behavioral continuity across `1.96.0-nightly`, `1.98.0-nightly`, `1.98.1`, and `1.101.0-nightly`, and Lean 4 kernel scaling for `Runtime(PostCleanup)` symbolic execution and computational reflection:

1. **Five-Stage `MirPhase` Query Pipeline and `Steal<Body>` Destruction Hazards:** `rustc` transforms each body through five query stages (`mir_built` at `MirPhase::Built`, `mir_const` at `Analysis(Initial)`, `mir_promoted` at `Analysis(PostCleanup)`, `mir_drops_elaborated_and_const_checked` at `Runtime(PostCleanup)`, and `optimized_mir` at `Runtime(Optimized)`), plus on-demand `mir_shims`. Intermediate stages return `&'tcx Steal<Body<'tcx>>`. Calling `tcx.optimized_mir(def_id)` steals the `Runtime(PostCleanup)` body in place (`compiler/rustc_mir_transform/src/lib.rs`, lines 660–661), causing any subsequent `tcx.mir_drops_elaborated_and_const_checked(def_id)` query to panic (`"attempted to read from stolen value: rustc_middle::mir::Body"`). Charon `0.1.210` (`translate_functions_to_ullbc.rs`, lines 296–326) catches `body.is_stolen()` on `mir_promoted` and `mir_drops_elaborated_and_const_checked` and silently falls back to `tcx.optimized_mir(def_id)`, altering the extracted semantics without warning. Furthermore, passive `override_queries` hooks are bypassed on warm incremental compilation caches unless active `after_analysis` demand forces every target query.
2. **Pre-Optimization Reachability and Unreachable-Code Pruning Before Charon:** Charon `0.1.210` hooks `after_expansion`, forces `mir_opt_level = 0` and `mir_preserve_ub = true`, disables `CheckAlignment`, and under its default and `--preset=aeneas` configurations extracts local bodies from `MirLevel::Promoted` (`tcx.mir_promoted`) while reading external dependencies from `optimized_mir` or `mir_for_ctfe`. Three distinct reachability filters occur before Aeneas sees LLBC:
   - `SimplifyCfg::Initial` and `SimplifyCfg::PromoteConsts` (`simplify.rs`, `remove_dead_blocks`) prune basic blocks with no incoming CFG edge from `bb0` (such as statements sequentially following `return` or `loop {}`), while leaving constant-condition branches (`if false { ... }`) intact as two-target `SwitchInt` terminators at `Promoted` and `opt-level=0`.
   - Charon's entry-driven `BodyTransCtx` worklist (`translate_functions_to_ullbc.rs`) translates only blocks reachable from `START_BLOCK` (`bb0`) and maps reachable `TerminatorKind::Unreachable` (from `unreachable_unchecked()` or empty `enum Void {}` matches) to `ullbc_ast::TerminatorKind::Abort(AbortKind::UndefinedBehavior)`.
   - Charon's post-pass `filter_unreachable_blocks` (`remove_unused_locals.rs`) deletes any ULLBC block not reachable from `BlockId::ZERO`.
3. **Safety Context Erasure and Lowering of Unsafe Operations in MIR:** `rustc` checks `unsafe` block obligations before MIR construction (`compiler/rustc_mir_build/src/check_unsafety.rs`) over THIR `BlockSafety` (`Safe`, `BuiltinUnsafe`, `UserUnsafe`) and HIR `BlockCheckMode`. MIR `SourceScopeData` does not retain `BlockSafety`. In MIR, raw pointer borrows (`Rvalue::RawPtr`), inline assembly (`TerminatorKind::InlineAsm`), and static/thread-local references (`LocalInfo::StaticRef`, `Rvalue::ThreadLocalRef`) remain syntactically distinct, whereas raw pointer dereferences (`ProjectionElem::Deref`), union field projections (`ProjectionElem::Field`), and calls to `unsafe fn` or `extern` items (`TerminatorKind::Call`) share their MIR node shapes with safe operations and must be distinguished using local/place types (`Ty::is_raw_ptr()`, `Ty::is_union()`) and callee signatures (`FnSig`). During `Runtime(Initial)` lowering, `LowerIntrinsics` rewrites `copy_nonoverlapping` to `StatementKind::Intrinsic( CopyNonOverlapping )`, `assume` to `Intrinsic(Assume)`, and unchecked arithmetic (`unchecked_add`, `unchecked_sub`, `unchecked_mul`) to `BinOp::AddUnchecked`, `SubUnchecked`, and `MulUnchecked`.
4. **The `-Z mir-preserve-ub` Boundary and `Built`-to-`Runtime(PostCleanup)` Dialect Lowering:** `-Z mir-preserve-ub` (false by default; enabled by Miri and Charon) controls two cleanup behaviors prior to optimization: `RemovePlaceMention` (`remove_place_mention.rs`, lines 26–45) deletes `StatementKind::PlaceMention` unless `preserve_ub` is enabled, and `SimplifyCfg::PreOptimizations` (`simplify.rs`, lines 281–291) collapses single-arm `SwitchInt` terminators (`match *ptr { _ => () }`) into `Goto` unless `preserve_ub` is enabled. By contrast, `let _ = *ptr;` emits `PlaceMention((*_1))` (deleted without `-Z mir-preserve-ub`), while `_ = *ptr;` emits no MIR evaluation of `*_1` in `Built` MIR at all. In Lean `4.34.1`, the four-way dialect boundary (safe value-copy, `FakeRead`/`PlaceMention`, `RemovePlaceMention`, and `WithoutDerefer` raw-pointer aliasing) and the executable `Built`-to-`Runtime(PostCleanup)` lowering validator (`validateBuiltToPostCleanupAdmittedQ1`) are mechanically verified.
5. **Empirical `Runtime(PostCleanup)` Construct Invariants and Lean 4 Reflection Scaling:** Across five Rust construct families (`while` loops, disjoint/nested/two-phase borrows, payload enums, array/slice indexing, and drop elaboration), empirical `Runtime(PostCleanup)` probes establish:
   - Loop-body locals pair `StorageLive` and `StorageDead` along every iteration back-edge while keeping loop-carried state live; explicit reborrows `let a: &mut u64 = &mut p.0` immediately emit `StorageDead` on the intermediate temporary `_3` while `_2 = &mut (*_3)` remains valid; and `BorrowKind::Mut { kind: MutBorrowKind::TwoPhaseBorrow }` survives intact in `Runtime(PostCleanup)` even though the textual `-Z dump-mir` pretty-printer renders all mutable borrows identically as `"mut "`.
   - Payload enum construction in `Runtime(PostCleanup)` uses single-statement `Rvalue::Aggregate(AggregateKind::Adt(...))` (refuting a stale doc comment on `RuntimePhase::Initial` in `mir/syntax.rs`), while `SetDiscriminant` is emitted only by coroutine transforms and shims.
   - `Rvalue::Len` is absent; fixed arrays lower `.len()` to a constant and `arr[i]` to `Assert(BoundsCheck)` + `ProjectionElem::Index`, whereas slices keep `slice::len` as a `TerminatorKind::Call` in `Runtime(PostCleanup)` and lower `s[i]` to `UnOp::PtrMetadata` before `Assert(BoundsCheck)`.
   - In Lean 4 (`v4.28.0-rc1`, `v4.28.0`, and `v4.34.1`), unjoined tree-shaped symbolic execution blows up as $\Theta(2^K)$ ($2K+1$ basic blocks for $K$ sequential `if/else` diamonds), block-modular join verification with `StorageDead` canonicalization scales linearly at $\Theta(K)$ (`651` kernel DAG objects at $K=16$), and total computational reflection via `checkBodySym_sound` yields constant $\Theta(1)$ 30-DAG-object proof terms (`1–4 ms` kernel typechecking through $K=32$), while replacing function-closure state updates ($\Theta(N^2)$ WHNF) with spine-strict association lists (`ListLocals`) reduces kernel scaling to $\Theta(N \cdot L)$.
6. **Multi-Version `rustc` Continuity (`2026-03-19`, `2026-05-31`, `1.98.1`, and `2026-09-30`):**
   - Between `nightly` (`1.96.0-nightly`, `fd0c901b00ee1e08a250039cdb90258603497e20`) and `nightly` (`1.98.0-nightly`, `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`), standalone `StatementKind::Retag` (`AddRetag`) was replaced by `Rvalue::Use(Operand, WithRetag)`, and `Runtime(Optimized)` `InstSimplify` gained reborrow folding (`&mut (*_1)` $\to$ `copy _1` with `WithRetag::Yes` for `MutBorrowKind::Default` vs. `no_retag copy _1` with `WithRetag::No` for `MutBorrowKind::TwoPhaseBorrow`), while `Runtime(PostCleanup)` statement/terminator counts remained identical across all 12 probed functions.
   - Between `nightly` (`1.98.0-nightly`, `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`) and `nightly` (`1.101.0-nightly`, `5c543b0b8c73c7b72bc8284ced4fb22ead15734d`), 12 serial execution runs on the reachability (`SimplifyCfg`) and unsafe-operation MIR fixtures produced **byte-identical** emitted `.mir` files and stage dumps, differing only in numeric pass-index prefixes in `-Zdump-mir` filenames (`1-1-005`/`1-1-008` vs. `1-1-004`/`1-1-007`).
   - Across the 51-package `nightly` cohort reviewed against stable Rust/Cargo `1.98.1` (`48a229ceaefd4985c50990b14116b6d856af0985`), the standard-library `read_volatile` non-atomicity/non-synchronization clause remains documented verbatim at `1.98.1`, the local execution trust-boundary fixture was already pinned to `1.98.1`, and the remaining 49 compiler/tooling claims require matching toolchain execution rather than source-only extrapolation.

---

## Applicability

This report applies to the following pinned toolchains, repositories, and verification environments recorded in `REPORT.json`:

| Component / Subject | Version / Toolchain Date | Commit / Revision | Scope & Role in Report |
| :--- | :--- | :--- | :--- |
| **`rust-lang/rust` (`nightly`)** | `1.96.0-nightly` | `fd0c901b00ee1e08a250039cdb90258603497e20` | Baseline comparison for `Runtime(PostCleanup)` construct probes and `StatementKind::Retag` $\to$ `WithRetag` evolution (`aarch64-apple-darwin`). |
| **`rust-lang/rust` (`nightly` source pin)** | `nightly` | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | Source-audited compiler revision behind the Charon/Aeneas `nightly` pin (`SimplifyCfg`, `check_unsafety.rs`, `LowerIntrinsics`). |
| **`rust-lang/rust` (`nightly` binary)** | `1.98.0-nightly` (`2026-05-30`) | `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` | Executed `rustc` binary on `x86_64-unknown-linux-gnu` (LLVM `22.1.6`) and `aarch64-apple-darwin` (SHA-256 `2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc`) for `MirPhase`, `Steal<Body>`, `-Z mir-preserve-ub`, `Runtime(PostCleanup)`, and reachability/unsafe probes. |
| **`rust-lang/rust` & `rust-lang/cargo` (`1.98.1` stable)** | `1.98.1` | `48a229ceaefd4985c50990b14116b6d856af0985` | Stable release comparison target for the 51-package `nightly` source review and `core::ptr::read_volatile` documentation continuity. |
| **`rust-lang/rust` (`nightly` binary)** | `1.101.0-nightly` (`2026-09-29`) | `5c543b0b8c73c7b72bc8284ced4fb22ead15734d` | Newer nightly execution comparison on `aarch64-apple-darwin` (SHA-256 `29f8ccc9aa7b0d8798eda854fa7f0e4ba3867c8c336b87d52dbb3b24b3f0878d`) for reachability (`SimplifyCfg`) and unsafe-operation MIR lowering. |
| **`AeneasVerif/charon`** | `0.1.210` | `a535e914f74db4fd9e6be7048f4233270d8945c0` / `1e08453924610c19d74c245a7308f17c1008e2db` | Charon driver (`extract.rs`, `translate_functions_to_ullbc.rs`, `remove_unused_locals.rs`) pinned to `nightly`. |
| **`leanprover/lean4`** | `v4.28.0-rc1`, `v4.28.0`, `v4.34.1` | `3b0f2862196c...`, `7e01a1bf5c70...`, `5045d0056413266e57c625dcd7c365b10e377c52` | Mechanized `MirSemanticBoundary`, `MirCaptureDialects`, `PR86AuditRepairs` (`4.34.1`) and kernel symbolic-execution vs. reflection scaling (`4.28.0-rc1`, `4.28.0`, `4.34.1`). |
| **`joshlf/anneal` & `google/zerocopy`** | `main` | `c065b55a3a143ec3f6a4f9c8166bd9e6a4c4633b`, `41f5b37afe7060fd9fe08c00b200672cd76d77b9` | Anneal MIR capture and verification architecture. |

---

## Findings

### 1. The Five-Stage `rustc` `MirPhase` Query Pipeline, `Steal<Body>` Hazards, and Incremental Cache Bypass

`Basis: source, execution, derived`

In `rustc` (`compiler/rustc_middle/src/mir/syntax.rs`, lines 66–142, and `compiler/rustc_mir_transform/src/lib.rs`, lines 269–765 at commit `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`), every MIR body carries a `phase: MirPhase` field updated monotonically by `remap_mir_for_const_eval_select` (`lib.rs`, lines 173–191) and `run_passes` (`lib.rs`, lines 206–264). The pipeline progresses through five primary `TyCtxt` queries plus on-demand shim synthesis:

| Stage | `TyCtxt` Query (`lib.rs`) | Return Type | Resulting `MirPhase` | Ordered Transforms Executed (`rustc_mir_transform`) |
| :--- | :--- | :--- | :--- | :--- |
| **1** | `mir_built` (lines 269–299) | `&'tcx Steal<Body<'tcx>>` | `MirPhase::Built` | `thir::cx::thir_body` $\to$ `build::mir_built` $\to$ `WhenNoOpt(CheckAlignment)` (`alignment.rs`, lines 31–44: runs in `mir_built` when `mir_opt_level == 0`). |
| **2** | `mir_const` (lines 364–384) | `&'tcx Steal<Body<'tcx>>` | `MirPhase::Analysis(AnalysisPhase::Initial)` | Steals `mir_built`; runs `SimplifyCfg::Initial`, `MentionedItems`, `SanityCheck` (under `-Z validate-mir`). |
| **3** | `mir_promoted` (lines 410–464) | `(&'tcx Steal<Body<'tcx>>, &'tcx Steal<IndexVec<Promoted, Body<'tcx>>>)` | `MirPhase::Analysis(AnalysisPhase::PostCleanup)` | Steals `mir_const`; runs `PromoteTemps`, `SimplifyCfg::PromoteConsts`, `CleanupPostBorrowck` (strips `FakeRead`, `AscribeUserType`, `Assign(Fake)`, `BorrowKind::Fake`, `UserTypeProjection`), `RemoveNoopLandingPads`, `SimplifyCfg::PostAnalysis`. |
| **4** | `mir_drops_elaborated_and_const_checked` (lines 515–555) | `&'tcx Steal<Body<'tcx>>` | `MirPhase::Runtime(RuntimePhase::PostCleanup)` | Calls `mir_borrowck` and `check_liveness`; steals `mir_promoted`; runs: (a) `run_analysis_to_runtime_passes` (`Runtime(Initial)`: `ElaborateBoxDerefs`, `ElaborateDrops`, `DeadStoreElimination::Initial`, `SwitchInt` edge splitting); (b) `run_runtime_lowering_passes` (`LowerIntrinsics`, `LowerSliceLenCalls`, `CheckPackedRef`, `CheckNull`, `CheckAlignment`, `CheckEnums`, `Derefer` when `!mir_preserve_ub`, `Deaggregator`, `RevealAll`, `Coroutine` transform); (c) `run_runtime_cleanup_passes` (`Runtime(PostCleanup)`: `AbortUnwindingCalls`, `AddCallGuards::CriticalCallEdges`, `RemovePlaceMention`, `SimplifyCfg::PreOptimizations`, `EraseDerefTemps`). |
| **5** | `optimized_mir` (lines 656–705) | `&'tcx Body<'tcx>` | `MirPhase::Runtime(RuntimePhase::Optimized)` | Steals `mir_drops_elaborated_and_const_checked` (line 661: `let body = tcx.mir_drops_elaborated_and_const_checked(def_id).steal();`); runs `run_optimization_passes` (`ClearCrossCrate::Clear` on `local_info`, `RemoveZsts`, `SimplifyCfg::ElaborateDrops`, `Inline`, `InstSimplify`, `GVN`, `CopyProp`, `JumpThreading`, `RemoveStorageMarkers`, `PreCodegen`). |
| **5b** | `mir_shims` (`shim.rs`, lines 30–145) | `&'tcx Body<'tcx>` | `MirPhase::Runtime(RuntimePhase::Optimized)` | Synthesizes compiler-generated shims (`DropGlue(def_id, Some(ty))`, `ReifyShim`, `ClosureOnceShim`, `ConstructCoroutineInClosureShim`, `VtableShim`, `CloneShim`) directly via `run_Analysis_to_runtime_passes` $\to$ `run_runtime_lowering_passes` $\to$ `run_runtime_cleanup_passes` $\to$ `run_optimization_passes`. |

Two operational capture hazards govern any `rustc_driver` tool that extracts MIR from `TyCtxt`:

1. **Destructive `Steal<Body>` Ordering (`compiler/rustc_data_structures/src/steal.rs`, lines 18–56) and Charon's Silent Fallback:**
   - Calling `.steal()` replaces the interior `RwLock<Option<T>>` with `None`; any subsequent `.borrow()` panics.
   - Standard `--emit=mir` (`compiler/rustc_interface/src/passes.rs`, line 798 $\to$ `compiler/rustc_middle/src/mir/pretty.rs`, lines 192–245) runs inside `tcx.analysis(())` and invokes `tcx.optimized_mir(def_id)` on every `hir_body_owner`, stealing both `mir_promoted` and `mir_drops_elaborated_and_const_checked`.
   - In Charon `0.1.210` (`charon/src/bin/charon-driver/translate/translate_functions_to_ullbc.rs`, lines 296–326, `get_mir`), both `MirLevel::Promoted` and `MirLevel::Elaborated` check `if !body.is_stolen()` and fall through on failure to `Ok(tcx.optimized_mir(def_id).clone())` with a source comment (`// Fall back to optimized MIR, which is never stolen.`). If an earlier callback or `--emit=mir` steals the body, Charon silently translates `Runtime(Optimized)` MIR instead of `Analysis(PostCleanup)` or `Runtime(PostCleanup)` MIR.
   - An in-process extractor targeting `Runtime(PostCleanup)` must either intercept `tcx.mir_drops_elaborated_and_const_checked(def_id).borrow()` before `optimized_mir` runs, or register a `rustc_interface::Config::override_queries` hook (`providers.mir_drops_elaborated_and_const_checked`) that calls `(DEFAULT_MIR_DROPS_ELABORATED)(tcx, def_id)`, clones `&Body<'tcx>` via `body.borrow()`, and returns `body` untouched so downstream `optimized_mir` can still `.steal()` it cleanly.
2. **Warm Incremental Cache Silence on Passive `override_queries` Hooks:**
   - A query provider registered via `override_queries` executes only when `rustc`'s query engine encounters a cache miss. On a warm incremental compilation cache (`-C incremental=...`) or `cargo check` pass where `optimized_mir` is never demanded and `mir_drops_elaborated_and_const_checked` is already cached on disk, a passive provider never fires and emits zero bodies.
   - Capture tools must combine the `override_queries` provider with an active iteration in `Callbacks::after_analysis` over `tcx.hir_body_owners()` (skipping `AnonConst`/`InlineConst` and synthetic coroutine closures) that forces `tcx.mir_drops_elaborated_and_const_checked(def_id)` and falls back to reading `.borrow()` directly if the provider did not run on that session.

---

### 2. Pre-Optimization Reachability and Unreachable-Code Pruning Before Charon (`nightly` and `nightly`)

`Basis: source, execution`

At `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0` (`0.1.210`), `charon-driver` intercepts compilation in `Callbacks::after_expansion` (`charon/src/bin/charon-driver/driver.rs`, lines 173–204) and mutates session flags in `charon/src/bin/charon-driver/translate/extract.rs` (lines 70–81) before MIR queries run:
- `sess.opts.unstable_opts.mir_opt_level = Some(0)`
- `sess.opts.unstable_opts.mir_preserve_ub = true`
- `sess.opts.unstable_opts.mir_enable_passes.push(("CheckAlignment".to_owned(), false))`

Charon's default MIR level is `MirLevel::Promoted` (`charon-lib/src/options.rs`, lines 302–307), which `--preset=aeneas` (`options.rs`, lines 501–513) leaves unchanged. For local crate items (`def_id.as_local().is_some()`), Charon queries `tcx.mir_promoted(local_def_id)`; for foreign crate items, Charon queries `tcx.optimized_mir(def_id)` and `tcx.mir_for_ctfe(def_id)`.

Consequently, unreachable or diverging code passes through three sequential reachability filters before Aeneas receives LLBC:

1. **Graph-Unreachable Block Pruning in `SimplifyCfg::Initial` and `SimplifyCfg::PromoteConsts` (`compiler/rustc_mir_transform/src/simplify.rs`):**
   - Both passes run inside `mir_const` and `mir_promoted` even at `-Z mir-opt-level=0`.
   - `SimplifyCfg::simplify` invokes `remove_dead_blocks`, which computes `traversal::reachable_as_bitset(body)` from `START_BLOCK` (`bb0`) and deletes every basic block with no directed CFG path from `bb0` (for example, source statements written after `return` or after an infinite `loop {}`).
   - However, `SimplifyCfg::Initial` and `SimplifyCfg::PromoteConsts` do **not** fold multi-target `SwitchInt` terminators whose condition happens to be a constant (`if false { ... }`), because `SimplifyCfg::simplify_branches` only collapses a `SwitchInt` when all targets are identical (`targets.all_targets().iter().all(|&t| t == first)`), and constant propagation (`ConstProp` / `GVN` / `SimplifyConstCondition`) does not run before `mir_promoted`. Thus an `if false` branch remains graph-reachable in `Promoted` and `Runtime(PostCleanup)` MIR.
2. **Charon Entry-Driven Block Translation and `TerminatorKind::Unreachable` Lowering (`translate_functions_to_ullbc.rs`, lines 1344–1539):**
   - `BodyTransCtx::translate_body` seeds its worklist strictly with `rustc_middle::mir::START_BLOCK` and enqueues successor blocks only as terminators are translated.
   - When a translated block reaches `mir::TerminatorKind::Unreachable` (emitted by `core::hint::unreachable_unchecked()` or exhaustive matching on an uninhabited enum `enum Void {}`), Charon translates it to `ullbc_ast::TerminatorKind::Abort(AbortKind::UndefinedBehavior)` (`translate_functions_to_ullbc.rs`, lines 1246–1252).
3. **Charon Post-Translation ULLBC Cleanup (`remove_unused_locals.rs`, lines 63–115):**
   - `TransformCtx::Transform` runs `filter_unreachable_blocks`, which traverses `body.body` from `ullbc_ast::BlockId::ZERO` and drops any ULLBC block not visited.

#### Multi-Version Execution Verification (`1.98.0-nightly` vs. `1.101.0-nightly`)

In [`support/rustc-mir-version-followup-r563-r564/`](support/rustc-mir-version-followup-r563-r564/), the reconstructed reachability fixture [`support/rustc-mir-version-followup-r563-r564/fixture/r563.rs`](support/rustc-mir-version-followup-r563-r564/fixture/r563.rs) was executed across `rustc 1.98.0-nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `2026-05-31`) and `rustc 1.101.0-nightly` (`5c543b0b8c73c7b72bc8284ced4fb22ead15734d`, `2026-09-30`) at `-Zmir-opt-level=0`, `-Zmir-opt-level=2`, and with `-Zdump-mir=SimplifyCfg-initial|SimplifyCfg-promote-consts|SimplifyCfg-post-analysis|SimplifyCfg-pre-optimizations`:

| Function in `r563.rs` | `SimplifyCfg-initial.before.mir` | `SimplifyCfg-initial.after.mir` & `opt0.mir` | `opt2.mir` (`-Zmir-opt-level=2`) | `1.98.0-nightly` vs. `1.101.0-nightly` Comparison |
| :--- | :--- | :--- | :--- | :--- |
| `after_return(x: i32) -> i32` | `bb0` (`return`) + disconnected `bb1` (`_0 = const 99_i32`) | `bb1` deleted (`2 -> 1` basic blocks); constant `99_i32` absent | Single `bb0` (`_0 = copy _1; return;`) | Emitted `.mir` and stage dump contents **byte-identical** across both nightlies. |
| `after_diverge(x: i32) -> i32` | Calls `diverges() -> !` (`bb0 -> bb1` with `unreachable;`) + disconnected `bb2`/`bb3` (`77_i32`) | Disconnected `bb2`/`bb3` deleted (`4 -> 2` basic blocks); `bb1: unreachable;` retained | `bb0 -> bb1 (unreachable;)` retained | Emitted `.mir` and stage dump contents **byte-identical** across both nightlies. |
| `constant_branch(x: i32) -> i32` | `if false { x + 55 } else { x + 1 }` (`bb0` with `switchInt(const false) -> [0: bb2, otherwise: bb1]`) | All `4` basic blocks (`bb0..bb3`), `switchInt(const false)`, and `const 55_i32` retained at `opt0` | `switchInt` folded away (`1` basic block, `_0 = Add(_1, const 1_i32)`) | Emitted `.mir` and stage dump contents **byte-identical** across both nightlies. |
| `empty_match(v: Void) -> i32` | `match v {}` | Single `bb0` ending in `unreachable;` | Single `bb0` ending in `unreachable;` | Emitted `.mir` and stage dump contents **byte-identical** across both nightlies. |

The only difference between `1.98.0-nightly` and `1.101.0-nightly` in the `-Zdump-mir` outputs is the pass-numbering prefix in the dump filenames (`1-1-005.SimplifyCfg-initial` and `1-1-008.SimplifyCfg-promote-consts` in `1.98.0-nightly` vs. `1-1-004.SimplifyCfg-initial` and `1-1-007.SimplifyCfg-promote-consts` in `1.101.0-nightly`); the dumped MIR bodies themselves are byte-for-byte identical ([`support/rustc-mir-version-followup-r563-r564/analysis.json`](support/rustc-mir-version-followup-r563-r564/analysis.json)).

---

### 3. Source Safety Checking vs. MIR Representation of Unsafe Operations (`nightly` and `nightly`)

`Basis: source, execution`

In `rustc` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, and `5c543b0b8c73c7b72bc8284ced4fb22ead15734d`), source-level `unsafe { ... }` obligations are checked prior to MIR construction and are **not** preserved as a syntax wrapper on MIR statements or terminators:
- **HIR and THIR safety contexts:** HIR blocks record `hir::BlockCheckMode` (`DefaultBlock`, `UnsafeBlock(UnsafeSource::CompilerGenerated | UserProvided)`), which THIR lowers into `thir::BlockSafety` (`Safe`, `BuiltinUnsafe`, `UserUnsafe`) on `thir::Block` (`compiler/rustc_middle/src/thir.rs`, lines 173–204).
- **Pre-MIR unsafety checking:** `compiler/rustc_mir_build/src/check_unsafety.rs` (`UnsafetyVisitor`) traverses THIR bodies before `mir_built` runs, enforcing the six Rust Reference `unsafe` operations (dereferencing raw pointers, reading/writing mutable or external statics, accessing `union` fields, calling `unsafe` functions/intrinsics/FFI, executing `asm!`, and implementing `unsafe trait`s).
- **Erasure of `BlockSafety` from MIR scopes:** When `Builder::in_scope` lowers THIR into MIR (`compiler/rustc_mir_build/src/builder/scope.rs`), `mir::SourceScopeData` (`compiler/rustc_middle/src/mir/syntax.rs`, lines 318–331) stores only `span`, `parent_scope`, `inlined`, `inlined_parent_scope`, and `local_data` (`ClearCrossCrate<SourceScopeLocalData>` with `lint_root`). `BlockSafety` is not stored in `mir::Body`.

Consequently, a downstream MIR consumer or verification backend must identify safety-relevant operations by combining MIR syntax with place/local types (`TyCtxt`) and callee signatures:

| Safety-Relevant Operation | MIR Representation in `Built` / `Promoted` | Lowered Form in `Runtime(PostCleanup)` / `Optimized` | How a MIR Consumer Distinguishes It from Safe Code |
| :--- | :--- | :--- | :--- |
| **Raw address-of (`&raw const p`, `&raw mut p`)** | `Rvalue::RawPtr(RawPtrKind::Const \| Mut, place)` (`&raw const`/`&raw mut` is safe to construct) | Unchanged (`Rvalue::RawPtr`) | Dedicated `Rvalue::RawPtr` constructor. |
| **Raw pointer dereference (`*p`)** | `PlaceElem::Deref` on a base `Place` of raw-pointer type `*const T` or `*mut T` | Under `-Z mir-opt-level=0` (`!preserve_ub`): preceded by `Assert(NullCheck)` and `Assert(MisalignedPointerDereference)` from `CheckNull`/`CheckAlignment` | Same `ProjectionElem::Deref` as `&T`/`&mut T`/`Box<T>`; requires inspecting the base place's `Ty::is_raw_ptr()`. |
| **Union field read or write (`u.field`)** | `PlaceElem::Field(FieldIdx, Ty)` on a base `Place` whose `Ty::is_union()` is true | Unchanged (`ProjectionElem::Field`) | Same `ProjectionElem::Field` as struct/tuple access; requires inspecting the base ADT (`AdtDef::is_union()`). |
| **Static or thread-local access** | Local with `LocalInfo::StaticRef { def_id, is_thread_local }` dereferenced via `(*_n)`, or `Rvalue::ThreadLocalRef(def_id)` | In `Runtime(Optimized)`, `ClearCrossCrate::Clear` erases `local_info`, leaving `_n = const {allocN: *mut T}` (`ConstOperand`) | At `Promoted`/`PostCleanup`, check `LocalDecl.local_info` (`StaticRef`) or `Rvalue::ThreadLocalRef`; at `Optimized`, inspect global allocation provenance (`GlobalAlloc::Static(def_id)`). |
| **`unsafe fn` or `extern "C"` call** | `TerminatorKind::Call { func, args, destination, target, .. }` | Unchanged (`TerminatorKind::Call`), unless rewritten by `LowerIntrinsics` | Same `TerminatorKind::Call` as safe calls; requires resolving callee `DefId` and checking `FnSig::safety()` / ABI (`ExternAbi`). |
| **Compiler intrinsics (`copy_nonoverlapping`, `assume`, `unchecked_add`)** | `TerminatorKind::Call` to `core::intrinsics::*` in `Built` and `Promoted` MIR | Lowered by `LowerIntrinsics` (`lower_intrinsics.rs`, lines 23–160) in `Runtime(Initial)` to `StatementKind::Intrinsic(NonDivergingIntrinsic::CopyNonOverlapping \| Assume)` and `Rvalue::BinaryOp(BinOp::AddUnchecked \| SubUnchecked \| MulUnchecked, ..)` | Dedicated `StatementKind::Intrinsic` and `BinOp::*Unchecked` variants after `LowerIntrinsics`. |
| **Inline assembly (`core::arch::asm!`)** | `TerminatorKind::InlineAsm { asm_macro, template, operands, options, targets, .. }` | Unchanged (`TerminatorKind::InlineAsm`) | Dedicated `TerminatorKind::InlineAsm` variant. |

Across `rustc 1.98.0-nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`) and `rustc 1.101.0-nightly` (`5c543b0b8c73c7b72bc8284ced4fb22ead15734d`), executing [`support/rustc-mir-version-followup-r563-r564/fixture/r564.rs`](support/rustc-mir-version-followup-r563-r564/fixture/r564.rs) produced **byte-identical** `.mir` files and `LowerIntrinsics.before.mir` / `LowerIntrinsics.after.mir` stage dumps across both functions (`operations` and `copy_one`) at both `-Zmir-opt-level=0` and `-Zmir-opt-level=2` ([`support/rustc-mir-version-followup-r563-r564/analysis.json`](support/rustc-mir-version-followup-r563-r564/analysis.json)).

---

### 4. The `-Z mir-preserve-ub` Boundary, Cleanup Transforms, and Mechanized `Built`-to-`Runtime(PostCleanup)` Dialect Validation

`Basis: source, execution, derived`

In `rustc 1.98.0-nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`), `-Z mir-preserve-ub` (`compiler/rustc_session/src/options.rs`, lines 1872–1874, defaulting to `false`) gates three specific passes across the `Runtime` lowering and cleanup pipeline:

1. **`RemovePlaceMention` (`compiler/rustc_mir_transform/src/remove_place_mention.rs`, lines 26–45):**
   - `is_enabled` returns `!sess.opts.unstable_opts.mir_preserve_ub`.
   - Under default flags (`-Z mir-preserve-ub=false`), every `StatementKind::PlaceMention(place)` generated for `let _ = <place>;` is replaced with `StatementKind::Nop` during `run_runtime_cleanup_passes`.
   - Under `-Z mir-preserve-ub=true`, `PlaceMention(place)` survives into `Runtime(PostCleanup)` and `Runtime(Optimized)` so place-validity checkers (such as Miri) observe the place projection.
2. **`SimplifyCfg::PreOptimizations` (`compiler/rustc_mir_transform/src/simplify.rs`, lines 66–81 and 281–291):**
   - When simplifying a `TerminatorKind::SwitchInt { discr, targets }` whose targets all jump to the same basic block (such as `match *ptr { _ => () }`, which evaluates `_2 = discriminant((*_1))` or inspects `(*_1)` in a single-target `SwitchInt`), `SimplifyCfg::simplify_branches` checks `if !preserve_ub` before replacing the `SwitchInt` with `TerminatorKind::Goto`.
   - Crucially, even when `SimplifyCfg::PreOptimizations` collapses the `SwitchInt` to `Goto` under `-Z mir-preserve-ub=false`, the preceding discriminant evaluation statement (`_2 = discriminant((*_1))`) in `match *ptr { _ => () }` **remains** in `Runtime(PostCleanup)` (`--emit=mir -Z mir-opt-level=0`), and is only eliminated later by `DeadStoreElimination` / `GVN` at `-Z mir-opt-level >= 1`.
3. **`Derefer` (`compiler/rustc_mir_transform/src/derefer.rs`, lines 25–35) and `EraseDerefTemps`:**
   - `Derefer::is_enabled` returns `!sess.opts.unstable_opts.mir_preserve_ub`. When enabled, `Derefer` extracts nested dereferences (`(*(*_1).0)`) into synthetic `LocalInfo::DerefTemp` temporaries initialized via `Rvalue::CopyForDeref(place)`, which `EraseDerefTemps` immediately rewrites in `run_runtime_cleanup_passes` to `Rvalue::Use(Operand::Copy(place), WithRetag::No)` (`derefer.rs`, line 213).

#### Empirical Comparison of Place-Mention Forms (`support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/place_mention_probe.rs`)

Executing `rustc` on [`support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/place_mention_probe.rs`](support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/place_mention_probe.rs) demonstrates that three superficially similar Rust wildcards have distinct MIR representations across `Built`, `Runtime(PostCleanup)`, and `Runtime(Optimized)`:

| Source Expression on `ptr: *const NonZeroU32` | `MirPhase::Built` | `Runtime(PostCleanup)` (`-Z mir-opt-level=0`, default `!preserve_ub`) | `Runtime(PostCleanup)` (`-Z mir-opt-level=0 -Z mir-preserve-ub=true`) | `Runtime(Optimized)` (`-C opt-level=1`, default `!preserve_ub`) |
| :--- | :--- | :--- | :--- | :--- |
| **`let _ = *ptr;`** (`probe_let_underscore_deref`) | `PlaceMention((*_1));` | **Erased** by `RemovePlaceMention` (`bb0: { return; }`) | **Preserved:** `PlaceMention((*_1));` (plus `CheckNull`/`CheckAlignment` asserts) | **Erased** (`bb0: { return; }`) |
| **`match *ptr { _ => () }`** (`probe_match_wildcard_deref`) | `FakeRead(ForMatchedPlace(None), (*_1));` | `FakeRead` stripped by `CleanupPostBorrowck` (`bb0: { return; }`) | `FakeRead` stripped by `CleanupPostBorrowck` | **Erased** |
| **`match *ptr { _ => () }` on `enum Choice`** (`probe_match_wildcard_enum_deref`) | `FakeRead(..., (*_1)); _2 = discriminant((*_1)); switchInt(move _2) -> [0: bb2, 1: bb2, otherwise: bb1];` | `SwitchInt` collapsed to `goto -> bb1` by `SimplifyCfg::PreOptimizations`, **but `_2 = discriminant((*_1));` remains** | Both `_2 = discriminant((*_1));` and `switchInt(move _2)` preserved | `_2 = discriminant((*_1));` eliminated by `DeadStoreElimination-final` |
| **`_ = *ptr;`** (`probe_underscore_assign_deref`) | **No evaluation of `*_1` emitted in `Built` MIR** (`bb0: { return; }`) | `bb0: { return; }` | `bb0: { return; }` | `bb0: { return; }` |

#### Additional Phase-Sensitivity Hazards in `Runtime(PostCleanup)` and `Runtime(Optimized)`

Inspection of [`support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/cleanup_subject.rs`](support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/cleanup_subject.rs) and `rustc_mir_transform` establishes four further invariants:
- **`ElaborateDrops` boolean drop flags (`elaborate_drops.rs`, lines 18–56):** Conditional partial moves introduce synthetic `bool` locals (`_4 = const true; ... _4 = const false;`) tested in cleanup and return blocks (`switchInt(copy _4) -> [0: bb4, otherwise: bb5]`) before calling `TerminatorKind::Drop`.
- **`ClearCrossCrate::Clear` on `LocalDecl.local_info` (`lib.rs`, line 592):** `optimized_mir` unconditionally runs `ClearCrossCrate::Clear` as its first pass, replacing `LocalDecl.local_info` with `ClearCrossCrate::Clear` even at `-Z mir-opt-level=0`. Any tool that relies on `LocalInfo::User(BindingForm)` or `LocalInfo::StaticRef` must inspect `Runtime(PostCleanup)` (`mir_drops_elaborated_and_const_checked`) or earlier.
- **`RemoveStorageMarkers` (`remove_storage_markers.rs`, lines 21–42):** Enabled at `mir_opt_level >= 1` when `emit_lifetime_markers` is false, stripping all `StorageLive` and `StorageDead` statements.
- **Compiler-generated `DropGlue` shims (`shim.rs`, lines 501–605):** Calling `ptr::drop_in_place` or `TerminatorKind::Drop` on an ADT with fields holding `Drop` types resolves at monomorphization to `InstanceKind::DropGlue(def_id, Some(ty))`, whose body is synthesized by `mir_shims` (requiring recursive `tcx.instance_mir(InstanceKind::DropGlue(...))` extraction).

#### Mechanized Four-Way Semantic Boundary and Lowering Validator in Lean `4.34.1`

In [`support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/`](support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/) (verified under Lean `4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`, with receipts in [`support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/r14-lean-revalidation.json`](support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/r14-lean-revalidation.json)), two mechanized developments formalize these phase boundaries:
- **Four-Way Semantic Boundary (`MirSemanticBoundary.lean` and `MirSemanticBoundaryControls.lean`):** Formalizes four distinct operational regimes (`safeValueCopy`, `builtWithFakeRead`, `postCleanupPreserveUb`, and `postCleanupDefaultErase`) and proves `four_way_semantic_boundary_separation` (all six pairwise inequalities hold across concrete execution traces: an uninitialized discriminant triggers UB in `builtWithFakeRead` via `FakeRead` and in `postCleanupPreserveUb` via `PlaceMention`, whereas `postCleanupDefaultErase` steps to `ok` after `RemovePlaceMention` erases `PlaceMention`, while `safeValueCopy` forbids raw-pointer aliasing).
- **`Built`-to-`Runtime(PostCleanup)` Lowering Validator (`PR86AuditRepairs.lean`, `BuiltPhaseControlsR1.lean`, `MirCaptureDialects.lean`, `ClaimCaptureClosure.lean`):** Defines `validateBuiltToPostCleanupAdmittedQ1` and proves `built_to_post_cleanup_lowering_verified_q1` and `q1_r1_joined_built_to_post_cleanup_semantics_verified`, checking statement-by-statement correspondence between `Built` MIR (containing `FakeRead`, `AscribeUserType`, `PlaceMention`, and unelaborated drops) and `Runtime(PostCleanup)` MIR (after `CleanupPostBorrowck`, `ElaborateDrops`, and `RemovePlaceMention`), while rejecting unlowered `FakeRead`/`AscribeUserType` remnants or silent drops of live assignments.

---

### 5. Empirical `Runtime(PostCleanup)` Construct Invariants and Lean 4 Reflection vs. Symbolic Execution Scaling

`Basis: source, execution, derived`

In [`support/rustc-postcleanup-mir-probes-and-lean4-reflection-vs-symexec-scaling-2026/`](support/rustc-postcleanup-mir-probes-and-lean4-reflection-vs-symexec-scaling-2026/), 9 functions across 5 construct families in [`support/rustc-postcleanup-mir-probes-and-lean4-reflection-vs-symexec-scaling-2026/postcleanup_constructs_specimen.rs`](support/rustc-postcleanup-mir-probes-and-lean4-reflection-vs-symexec-scaling-2026/postcleanup_constructs_specimen.rs) were dumped at `MirPhase::Built`, `MirPhase::Analysis(PostCleanup)` (`mir_promoted`), `MirPhase::Runtime(PostCleanup)` (`PreCodegen.before.mir` at `-Z mir-opt-level=0`), and `MirPhase::Runtime(Optimized)` (`-O`) under both `rustc 1.96.0-nightly` (`fd0c901b00ee1e08a250039cdb90258603497e20`, `2026-03-19`) and `rustc 1.98.0-nightly` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `2026-05-31`).

#### Summary of `Runtime(PostCleanup)` Construct Invariants Across `1.96.0-nightly` and `1.98.0-nightly`

| Construct Family & Probe Function | `Runtime(PostCleanup)` Lowering Invariant (`1.96.0-nightly` & `1.98.0-nightly`) | Multi-Version Delta (`1.96.0-nightly` $\to$ `1.98.0-nightly`) |
| :--- | :--- | :--- |
| **1. Loops & Back-Edge Lifetimes** (`while_countdown_sum`, `nested_loop_break_continue`) | `Simplifiable` `FalseUnwind` edges in `Built` MIR (`bb1 -> [real: bb2, unwind: bb4]`) are stripped by `CleanupPostBorrowck` to direct `goto -> bb1` back-edges; loop-body temporaries (`_5.._8`) execute `StorageDead` before every back-edge `goto -> bb1` and re-execute `StorageLive` on the next iteration, while loop-carried state (`_2`, `_3`) stays live across the loop. | **Invariant** at `Runtime(PostCleanup)` (`5` BBs / `35` stmts in `while_countdown_sum`; `11` BBs / `68` stmts in `nested_loop_break_continue`). |
| **2. Disjoint/Nested/Two-Phase Borrows & Raw Projections** (`disjoint_field_borrows`, `nested_reborrow`, `two_phase_method_borrow`, `raw_ptr_projections`) | Explicit `&mut` bindings lower to a temporary borrow `_3 = &mut ((*_1).0)` followed by `_2 = &mut (*_3)` and immediate `StorageDead(_3)` while `_2` stays live. Method-call autoref `v.push(v.len())` retains `BorrowKind::Mut { kind: MutBorrowKind::TwoPhaseBorrow }` in `Runtime(PostCleanup)`, reserving `_3 = &mut (*_1)` before shared borrow `_5 = &(*_1)` (`pretty.rs` prints both `Default` and `TwoPhaseBorrow` as `"mut "`). `&raw const`/`&raw mut` lower directly to `Rvalue::RawPtr`. | `1.96.0-nightly` used standalone `StatementKind::Retag`; `1.98.0-nightly` replaced `AddRetag` with `Rvalue::Use(Operand, WithRetag)`. In `Runtime(Optimized)`, `1.98.0-nightly` `InstSimplify` folds `nested_reborrow` to `_3 = copy _1` (`WithRetag::Yes`) and `two_phase_method_borrow` to `_3 = no_retag copy _1` (`WithRetag::No`). |
| **3. Payload Enums & Downcasts** (`construct_and_match_packet`) | Enum construction (`Packet::Empty`, `Packet::Val(x)`, `Packet::Pair(a, b)`) emits single-statement `Rvalue::Aggregate(AggregateKind::Adt(def_id, variant_idx, ...))` (refuting the stale doc comment on `RuntimePhase::Initial` in `mir/syntax.rs`; `SetDiscriminant` is used only in coroutines/shims). Matching uses `_9 = discriminant(_5)`, `switchInt(move _9)`, and payload extraction via `ProjectionElem::Downcast` + `ProjectionElem::Field` (`((_5 as Val).0: u64)`). | **Invariant** at `Runtime(PostCleanup)` (`9` BBs / `46` stmts in both toolchains). |
| **4. Array/Slice Indexing, `PtrMetadata`, & `slice::len`** (`array_and_slice_ops`) | `Rvalue::Len` is removed. Fixed `[u64; 4]` `.len()` lowers to `_3 = const 4_usize`, while `arr[i]` computes `_7 = PtrMetadata(copy _1)` (`const 4_usize` in `PostCleanup`), `Lt(copy _6, copy _7)`, and `Assert(BoundsCheck)`. For `&[u64]`, `s.len()` remains an unlowered `TerminatorKind::Call` to `core::slice::<impl [T]>::len` in `Runtime(PostCleanup)` (because `LowerSliceLenCalls` only matches calls whose destination local is `LocalInfo::ConstLen`), whereas `s[i]` lowers directly to `_13 = PtrMetadata(copy _2)` + `Assert(BoundsCheck)`. An explicit `let len = arr.len()` binding creates `&raw const (*_1)` with `RawPtrKind::FakeForPtrMetadata` passed to `PtrMetadata`. | **Invariant** at `Runtime(PostCleanup)` (`5` BBs / `35` stmts in both toolchains). |
| **5. Drop Elaboration & Unwind Cleanup** (`early_return_drop_cleanup`, `conditional_move_drop_flags`) | `ElaborateDrops` lowers `TerminatorKind::Drop` on no-op-drop structs to `goto`, retains `TerminatorKind::Drop` on `HasDrop`, splits unwind cleanup paths (`bb4 (cleanup)` ending in `TerminatorKind::Resume`), and inserts stack boolean drop flags (`_12: bool`) with conditional drop-flag test blocks (`bb8`, `bb9`) when a value is conditionally moved before scope exit. | **Invariant** at `Runtime(PostCleanup)` (`6` BBs / `24` stmts and `10` BBs / `42` stmts in both toolchains). |

#### Lean 4 Kernel Scaling: Tree Deduction ($\Theta(2^K)$) vs. Block-Modular Join ($\Theta(K)$) vs. Computational Reflection ($\Theta(1)$)

In [`support/rustc-postcleanup-mir-probes-and-lean4-reflection-vs-symexec-scaling-2026/ReflectionVsSymExecBench.lean`](support/rustc-postcleanup-mir-probes-and-lean4-reflection-vs-symexec-scaling-2026/ReflectionVsSymExecBench.lean), all three verification architectures and both local-environment representations (`ClosureLocals` vs. `ListLocals`) were benchmarked across `leanprover/lean4:v4.28.0-rc1` (`3b0f2862196c...`), `v4.28.0` (`7e01a1bf5c70...`), and `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) (receipts in [`support/rustc-postcleanup-mir-probes-and-lean4-reflection-vs-symexec-scaling-2026/lean_scaling_results.json`](support/rustc-postcleanup-mir-probes-and-lean4-reflection-vs-symexec-scaling-2026/lean_scaling_results.json)):

1. **State Map Representation (`ClosureVsListLocals.lean`):**
   - Representing local variable stores as function closures `Nat -> Option Val` (`ClosureLocals.set l v s := fun l' => if l' == l then some v else s l'`) causes $N$ sequential updates followed by $N$ reads to scale quadratically ($\Theta(N^2)$ WHNF traversals: `26.8 ms` at $N=200$ on `v4.34.1`).
   - Replacing closures with spine-strict association lists (`ListLocals.set` with `let s' := set l v rest; (l', v') :: s'`) scales as $\Theta(N \cdot L)$ where $L$ is the number of distinct live locals (`5.6 ms` at $N=200, L=8$ on `v4.34.1`—a $4.8\times$ speedup).
2. **CFG Diamond Verification Architecture (`DiamondSymExec.lean`, `JoinedBlockModular.lean`, `ComputationalReflection.lean`):**
   - On a CFG of $K$ sequential `if/else` diamonds ($3K + 1$ basic blocks, $2^K$ execution paths), where each branch allocates a fresh temporary `StorageLive(10 + 2*i)` / `StorageLive(11 + 2*i)` and executes `StorageDead` before merging at the join block:

| Verification Architecture | Asymptotic Complexity | Proof Term DAG Size (`Expr.numObjs`) | `K = 4` (`v4.34.1`) | `K = 8` (`v4.34.1`) | `K = 10` (`v4.34.1`) | `K = 16` (`v4.34.1`) | `K = 32` (`v4.34.1`) |
| :--- | :--- | :--- | ---: | ---: | ---: | ---: | ---: |
| **1. Unjoined Tree Deduction (`ReachTree`)** (`DiamondSymExec.lean`) | $\Theta(2^K)$ | `1,303` ($K=4$), `20,759` ($K=8$), `83,019` ($K=10$) | `16.2 ms` | `203.9 ms` | `848.8 ms` | Infeasible ($>65,536$ paths) | Infeasible ($>4 \times 10^9$ paths) |
| **2. Block-Modular Join + `StorageDead` Erasure** (`JoinedBlockModular.lean`) | $\Theta(K)$ | `183` ($K=4$), `339` ($K=8$), `651` ($K=16$) | `4.1 ms` | `8.5 ms` | — | `18.3 ms` | Linear |
| **3. Total Computational Reflection (`checkBodySym_sound`)** (`ComputationalReflection.lean`) | $\Theta(1)$ proof term, $\Theta(|B|)$ kernel reduction | **`30` DAG objects** (constant for all $K$) | `1.1 ms` | `1.4 ms` | — | `2.1 ms` | `3.9 ms` |

   - **Crucial Role of `StorageDead` at Join Points:** Without `StorageDead` before a diamond merge, the left branch state contains `(10 + 2*i, .int v)` while the right branch state contains `(11 + 2*i, .int v)`, so structural state equality `s_then == s_else` at the join block is **false** (`diamondNoStorageDead_join_fails : checkDiamondJoin 1 (diamondNoStorageDead 1) initState = false` in `JoinedBlockModular.lean`). Because `rustc` emits `StorageDead` on branch-local temporaries before jumping to the merge block, modelling `StorageDead` as key deletion (`ListLocals.erase`) canonicalizes both incoming states to the identical association list (`[(1, .sym 0)]`), allowing structural equality `BEq` to succeed at every join block without SMT or AC-unification.

---

### 6. Bounded Source Review of the `nightly` Cohort Against Stable `1.98.1`

`Basis: source, documentation`

In [`support/rust-cargo-nightly-to-1981-source-review/`](support/rust-cargo-nightly-to-1981-source-review/), the 51-package `Rust/Cargo/rustc nightly` cohort (selected in [`support/rust-cargo-nightly-to-1981-source-review/frozen-cohort.csv`](support/rust-cargo-nightly-to-1981-source-review/frozen-cohort.csv) from the package inventory [`support/rust-cargo-nightly-to-1981-source-review/version-inventory-ebcdcad-581.csv`](support/rust-cargo-nightly-to-1981-source-review/version-inventory-ebcdcad-581.csv)) was audited against stable Rust `1.98.1` (`rust-lang/rust@48a229ceaefd4985c50990b14116b6d856af0985`) and Cargo `1.98.1` (`support/rust-cargo-nightly-to-1981-source-review/matrix.json`):
- **Documented continuity of volatile non-atomicity (`rust-volatile-memory-access`):** The claim that `ptr::read_volatile` and `ptr::write_volatile` do not make an access atomic and do not provide inter-thread synchronization (originally tied to `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` `library/core/src/ptr/mod.rs`, blob `ff2c18d685b65832c296731f23f1664779b874f2`) remains documented verbatim in the official `1.98.1` `std::ptr::read_volatile` documentation and commit-pinned source `rust-lang/rust@48a229ceaefd4985c50990b14116b6d856af0985` `library/core/src/ptr/mod.rs`.
- **Already-current local execution fixture (`anneal--trust-evidence-boundary`):** That package's frozen metadata already pinned Rust and Cargo `1.98.1` (`48a229ceaefd4985c50990b14116b6d856af0985`), where `cargo metadata --offline --no-deps` produced no side-effect markers while `cargo check --offline` executed build scripts and proc macros and `lean --json` executed `#eval`/`run_cmd`.
- **Remaining 49 cohort rows:** Because compiler internals, unstable `-Z` flags, and Charon/Aeneas integrations depend on exact compiler commits (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` in 44 subject entries and `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` in 5), source-header inspection at `1.98.1` does not substitute for runtime execution on the remaining 49 rows (two of which—pre-Charon reachability and unsafe MIR operations—were subsequently executed and verified on `1.98.0-nightly` and `1.101.0-nightly` as documented in Findings 2 and 3 above).

---

## Boundaries

1. **Compiler Phase vs. Optimization Level:** `MirPhase::Runtime(PostCleanup)` (`tcx.mir_drops_elaborated_and_const_checked`) is a distinct compiler phase from `MirPhase::Runtime(Optimized)` (`tcx.optimized_mir`), even when `-Z mir-opt-level=0` is passed. In particular, `optimized_mir` always runs `ClearCrossCrate::Clear` on `local_info`, destroying user-binding and `StaticRef` metadata.
2. **Textual `-Z dump-mir` Pretty-Printer Ambiguity:** Because `compiler/rustc_middle/src/mir/pretty.rs` prints `MutBorrowKind::Default`, `MutBorrowKind::TwoPhaseBorrow`, and `MutBorrowKind::ClosureCapture` identically as `"mut "`, textual `.mir` parsers cannot distinguish two-phase borrows from ordinary mutable borrows; an in-process `rustc_driver` consumer must inspect the typed `mir::BorrowKind` AST directly.
3. **Unlowered `slice::len` in `Runtime(PostCleanup)`:** Because `LowerSliceLenCalls` (`lower_slice_len.rs`) only rewrites `slice::len` calls whose destination local carries `LocalInfo::ConstLen`, user calls to `s.len()` on `&[T]` remain `TerminatorKind::Call` in `Runtime(PostCleanup)` and must be handled in verification backends alongside `UnOp::PtrMetadata`.
4. **Toolchain Pin Specificity:** While the `Runtime(PostCleanup)` construct invariants and `SimplifyCfg`/`LowerIntrinsics` outputs are empirically verified across `1.96.0-nightly`, `1.98.0-nightly`, and `1.101.0-nightly`, `rustc`'s internal MIR AST is not stability-guaranteed (as shown by `StatementKind::Retag` $\to$ `Rvalue::Use(Operand, WithRetag)` between `1.96.0-nightly` and `1.98.0-nightly`).

---

## Evidence

All supporting fixtures, raw MIR dumps, Lean 4 proof modules, and JSON verification receipts are preserved under `support/`:

- **MIR Phases, `Steal<Body>`, `-Z mir-preserve-ub`, and Lean 4 Dialect Proofs (`support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/`):**
  - Rust probe sources and compiler revalidation receipt: [`support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/place_mention_probe.rs`](support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/place_mention_probe.rs), [`support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/cleanup_subject.rs`](support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/cleanup_subject.rs), [`support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/r14-compiler-revalidation.json`](support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/r14-compiler-revalidation.json).
  - Lean `4.34.1` modules and verification receipt: [`support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/MirSemanticBoundary.lean`](support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/MirSemanticBoundary.lean), [`support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/MirSemanticBoundaryControls.lean`](support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/MirSemanticBoundaryControls.lean), [`support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/MirCaptureDialects.lean`](support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/MirCaptureDialects.lean), [`support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/MirCaptureDialectControls.lean`](support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/MirCaptureDialectControls.lean), [`support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/BuiltPhaseControlsR1.lean`](support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/BuiltPhaseControlsR1.lean), [`support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/PR86AuditRepairs.lean`](support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/PR86AuditRepairs.lean), [`support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/ClaimCaptureClosure.lean`](support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/ClaimCaptureClosure.lean), [`support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/ClaimCaptureClosureControls.lean`](support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/ClaimCaptureClosureControls.lean), [`support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/r14-lean-revalidation.json`](support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/r14-lean-revalidation.json).
- **Multi-Version Reachability (`SimplifyCfg`) and Unsafe-Operation MIR Comparison (`support/rustc-mir-version-followup-r563-r564/`):**
  - Fixtures and scripts: [`support/rustc-mir-version-followup-r563-r564/fixture/r563.rs`](support/rustc-mir-version-followup-r563-r564/fixture/r563.rs), [`support/rustc-mir-version-followup-r563-r564/fixture/r564.rs`](support/rustc-mir-version-followup-r563-r564/fixture/r564.rs), [`support/rustc-mir-version-followup-r563-r564/check.py`](support/rustc-mir-version-followup-r563-r564/check.py), [`support/rustc-mir-version-followup-r563-r564/probe.py`](support/rustc-mir-version-followup-r563-r564/probe.py).
  - Recorded outputs and analysis: [`support/rustc-mir-version-followup-r563-r564/results.json`](support/rustc-mir-version-followup-r563-r564/results.json), [`support/rustc-mir-version-followup-r563-r564/analysis.json`](support/rustc-mir-version-followup-r563-r564/analysis.json), [`support/rustc-mir-version-followup-r563-r564/raw/old/r563/opt0.mir`](support/rustc-mir-version-followup-r563-r564/raw/old/r563/opt0.mir), [`support/rustc-mir-version-followup-r563-r564/raw/new/r563/opt0.mir`](support/rustc-mir-version-followup-r563-r564/raw/new/r563/opt0.mir), [`support/rustc-mir-version-followup-r563-r564/raw/old/r564/opt0.mir`](support/rustc-mir-version-followup-r563-r564/raw/old/r564/opt0.mir), [`support/rustc-mir-version-followup-r563-r564/raw/new/r564/opt0.mir`](support/rustc-mir-version-followup-r563-r564/raw/new/r564/opt0.mir).
- **`Runtime(PostCleanup)` Construct Probes and Lean 4 Scaling Benchmarks (`support/rustc-postcleanup-mir-probes-and-lean4-reflection-vs-symexec-scaling-2026/`):**
  - Rust probe and dumps across `2026-03-19` and `2026-05-31`: [`support/rustc-postcleanup-mir-probes-and-lean4-reflection-vs-symexec-scaling-2026/postcleanup_constructs_specimen.rs`](support/rustc-postcleanup-mir-probes-and-lean4-reflection-vs-symexec-scaling-2026/postcleanup_constructs_specimen.rs), [`support/rustc-postcleanup-mir-probes-and-lean4-reflection-vs-symexec-scaling-2026/probe_postcleanup_constructs.py`](support/rustc-postcleanup-mir-probes-and-lean4-reflection-vs-symexec-scaling-2026/probe_postcleanup_constructs.py), [`support/rustc-postcleanup-mir-probes-and-lean4-reflection-vs-symexec-scaling-2026/postcleanup_constructs_results.json`](support/rustc-postcleanup-mir-probes-and-lean4-reflection-vs-symexec-scaling-2026/postcleanup_constructs_results.json).
  - Lean 4 scaling benchmark and results: [`support/rustc-postcleanup-mir-probes-and-lean4-reflection-vs-symexec-scaling-2026/ReflectionVsSymExecBench.lean`](support/rustc-postcleanup-mir-probes-and-lean4-reflection-vs-symexec-scaling-2026/ReflectionVsSymExecBench.lean), [`support/rustc-postcleanup-mir-probes-and-lean4-reflection-vs-symexec-scaling-2026/run_lean_scaling_bench.py`](support/rustc-postcleanup-mir-probes-and-lean4-reflection-vs-symexec-scaling-2026/run_lean_scaling_bench.py), [`support/rustc-postcleanup-mir-probes-and-lean4-reflection-vs-symexec-scaling-2026/lean_scaling_results.json`](support/rustc-postcleanup-mir-probes-and-lean4-reflection-vs-symexec-scaling-2026/lean_scaling_results.json).
- **Bounded Source Review Against `1.98.1` (`support/rust-cargo-nightly-to-1981-source-review/`):**
  - [`support/rust-cargo-nightly-to-1981-source-review/matrix.json`](support/rust-cargo-nightly-to-1981-source-review/matrix.json), [`support/rust-cargo-nightly-to-1981-source-review/frozen-cohort.csv`](support/rust-cargo-nightly-to-1981-source-review/frozen-cohort.csv), [`support/rust-cargo-nightly-to-1981-source-review/version-inventory-ebcdcad-581.csv`](support/rust-cargo-nightly-to-1981-source-review/version-inventory-ebcdcad-581.csv), [`support/rust-cargo-nightly-to-1981-source-review/baseline-report-paths.txt`](support/rust-cargo-nightly-to-1981-source-review/baseline-report-paths.txt), [`support/rust-cargo-nightly-to-1981-source-review/check_matrix.py`](support/rust-cargo-nightly-to-1981-source-review/check_matrix.py).

---

## Revalidation

Run the following self-contained commands from this package directory to revalidate the offline checkers, `rustc` MIR phase and `-Z mir-preserve-ub` probes, and Lean 4 proof modules:

```bash
# 1. Verify the multi-version (2026-05-31 vs. 2026-09-30) reachability & unsafe-op MIR artifacts offline
python3 -B support/rustc-mir-version-followup-r563-r564/check.py

# 2. Re-run the `-Z mir-preserve-ub` and PlaceMention probes under rustc +nightly
mkdir -p build/mir-probes
rustc +nightly --edition 2021 --crate-type lib \
  -Z mir-opt-level=0 --emit=mir \
  -o build/mir-probes/default_opt0.mir \
  support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/place_mention_probe.rs
rustc +nightly --edition 2021 --crate-type lib \
  -Z mir-opt-level=0 -Z mir-preserve-ub=true --emit=mir \
  -o build/mir-probes/preserve_ub_opt0.mir \
  support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/place_mention_probe.rs

# 3. Re-check the Lean 4.34.1 semantic boundary and lowering-validator modules
for f in \
  MirSemanticBoundary.lean \
  MirSemanticBoundaryControls.lean \
  MirCaptureDialects.lean \
  MirCaptureDialectControls.lean \
  BuiltPhaseControlsR1.lean \
  PR86AuditRepairs.lean \
  ClaimCaptureClosure.lean \
  ClaimCaptureClosureControls.lean; do
  lean support/rustc-1-98-mir-phases-steal-hazards-and-preserve-ub-boundary/"$f"
done

# 4. Re-check the Lean 4 symbolic execution vs. computational reflection scaling benchmark
anneal-lean-run --mode file --concurrency 2 -- \
  lean support/rustc-postcleanup-mir-probes-and-lean4-reflection-vs-symexec-scaling-2026/ReflectionVsSymExecBench.lean
```
