# rustc MIR Query Steal<Body> Lifetimes, PostCleanup vs. instance_mir Lowering, and Single-Session Dual-Profile Capture

## Summary

A `rustc_driver` verification tool that targets `MirPhase::Runtime(RuntimePhase::PostCleanup)`
faces two architectural design questions when extracting MIR bodies across
build profiles:

1. **Query selection and `Steal<Body>` lifetime management**: Which query
   yields `Runtime(PostCleanup)` MIR without post-cleanup optimization or
   UB-check expansion, which items have their `Steal<Body<'tcx>>` stolen before
   `Callbacks::after_analysis`, and how can a driver capture un-stolen
   `Runtime(PostCleanup)` MIR without process-global `static Mutex` state?
2. **Dual-profile (`--release` vs. `--debug`) divergence and single-session
   capture**: Where do `-C overflow-checks`, `-C debug-assertions`, and
   `-Z ub-checks` alter AST expansion, `LocalDefId` (`DefIndex`) numbering, and
   `Runtime(PostCleanup)` MIR, why does pairing two `rustc_driver::run_compiler`
   runs by `DefIndex` fail, and when can a single `rustc_driver` session capture
   one `Runtime(PostCleanup)` MIR body per item that soundly covers both
   `--release` and `--debug`?

Source inspection and a reproducible 4-experiment `rustc_driver` probe
(`support/probe_mir_steal_and_profiles.rs`, `support/probe_results.json`) on
`rustc 1.98.0-nightly (f8a08b688 2026-05-30)` establish six principal findings:

- **Exact `Steal<Body>` steal set at `Callbacks::after_analysis`**: Only two
  functions in `rustc` ever call `.steal()` on
  `tcx.mir_drops_elaborated_and_const_checked(def)`: `inner_mir_for_ctfe` (for
  `ConstContext::Const` and `ConstContext::Static`, whereas `ConstContext::ConstFn`
  clones via `body.borrow().clone()` without stealing) and `inner_optimized_mir`.
  Consequently, at `Callbacks::after_analysis`, `mir_drops_elaborated_and_const_checked`
  is **never stolen** for non-coroutine functions (`Fn`, `AssocFn`, `Closure`),
  including `const fn` items evaluated at compile time during `check_crate`. It
  is stolen before `after_analysis` only for (a) non-trivial top-level `Const`,
  `Static`, `AnonConst`, and `InlineConst` items, (b) `AssocConst` items
  referenced by non-const functions when `should_codegen()` is true
  (`--emit=link`, or mid-iteration in `after_analysis` under `--emit=metadata`
  once the referencing function's `KnownPanicsLint` pass runs), and (c)
  coroutines (`async fn` closure bodies and `gen` blocks, whose layout
  computation queries `optimized_mir`).
- **Exact equivalence of `mir_for_ctfe` and `mir_drops_elaborated_and_const_checked`
  modulo `ConstEvalCounter`**: For every constant and `const fn` item not
  calling `core::intrinsics::const_eval_select`, `inner_mir_for_ctfe` runs only
  `ctfe_limit::CtfeLimit`, which appends `StatementKind::ConstEvalCounter` to
  call and back-edge blocks without changing `MirPhase::Runtime(RuntimePhase::PostCleanup)`.
  Across all 11 constant and `const fn` items in Experiment 1, stripping
  `StatementKind::ConstEvalCounter` from `tcx.mir_for_ctfe(def)` reproduces the
  exact `mir_drops_elaborated_and_const_checked(def)` body byte-for-byte.
- **Why `tcx.instance_mir` (`optimized_mir`) does not yield `Runtime(PostCleanup)`
  even at `-C opt-level=0`**: First, `Session::mir_opt_level` defaults to `1`
  (not `0`) when `-C opt-level=0` (`OptLevel::No`) is passed without
  `-Z mir-opt-level=0`, running 16+ optimization passes (`RemoveStorageMarkers`,
  `RemoveZsts`, `InstSimplify`, `SimplifyCfg`, `SimplifyConstCondition`,
  `SimplifyLocals`, `CopyProp`, `SingleUseConsts`) that strip storage markers,
  fold `Operand::RuntimeChecks`, and collapse dead branches. Second, even with
  `-Z mir-opt-level=0` or `#[optimize(none)]`, `optimized_mir` still transitions
  `body.phase` to `Runtime(Optimized)` and runs required passes including
  `CheckAlignment`, `CheckNull`, and `CheckEnums` (expanding a 1-block raw
  pointer dereference into 4 basic blocks, 22 locals, and 24 statements when
  `ub_checks` is enabled), `ForceInline`, `RemoveUnneededDrops`, and
  `MentionedItems`.
- **Capturing `Runtime(PostCleanup)` MIR without process-global `Mutex` state**:
  A `rustc_driver` tool can avoid process-global `static Mutex` state in either
  of two ways: (1) a **zero-hook `after_analysis` reader** that borrows
  `tcx.mir_drops_elaborated_and_const_checked(def).borrow()` for functions and
  closures, `tcx.mir_built(def).borrow()` for `tcx.is_trivial_const(def)` items,
  and `tcx.mir_for_ctfe(def)` with `StatementKind::ConstEvalCounter` filtered
  out for non-trivial constants; or (2) a **session-scoped `thread_local!`
  `override_queries` hook** whose `OnceLock` stores only the stateless default
  function pointer while an RAII guard owns the per-thread capture table across
  `rustc_driver::run_compiler`.
- **Fragility of `DefIndex`-keyed dual-session profile merging**: Running
  `rustc_driver::run_compiler` twice (`--release` and `--debug`) and zipping
  captured bodies by `LocalDefId::local_def_index` (`DefIndex`) is unsound
  whenever `#[cfg(debug_assertions)]`, `#[cfg(overflow_checks)]`, or
  `#[cfg(ub_checks)]` gates any AST node that allocates a `DefId` in
  `rustc_resolve::def_collector::DefCollector`—including a private closure or
  `const { ... }` block inside a function body—because `DefCollector` numbers
  definitions sequentially after `#[cfg]` stripping, shifting the `DefIndex` of
  every subsequent item in the crate.
- **Exact `--release` vs. `--debug` divergence boundary and single-session
  capture**: In `rustc_mir_build`, `-C overflow-checks` affects only six integer
  operators (`+`, `-`, `*`, `<<`, `>>`, and unary `-`, plus their compound
  assignment forms), which emit `AssertKind` variants satisfying
  `msg.is_optional_overflow_check() == true`. Integer `/` and `%`, slice bounds
  checks, explicit `wrapping_*` / `checked_*` / `overflowing_*` / `saturating_*`
  / `unchecked_*` calls, `#[rustc_inherit_overflow_checks]` bodies, and all
  `Const` / `Static` / `AssocConst` / `AnonConst` / `InlineConst` items
  (`BodyOwnerKind::Const | Static`, which force `check_overflow = true` in
  `Builder::new`) produce identical `Runtime(PostCleanup)` MIR in both profiles
  (whereas `const fn` uses `BodyOwnerKind::Fn` and therefore diverges between
  profiles even during compile-time CTFE). Furthermore, at `Runtime(PostCleanup)`,
  `core::intrinsics::{ub_checks, overflow_checks}` remain symbolic
  `Operand::RuntimeChecks` operands, and `debug_assert!(cond)` retains its full
  6-block panic CFG under both `-C debug-assertions=off` and `on` (differing
  only in the `const false` vs. `const true` discriminant literal when `cond`
  has no checked arithmetic). Consequently, for crates without AST-level
  profile `#[cfg]` gates, a single `rustc_driver` session compiled with
  `-C overflow-checks=on` captures one `Runtime(PostCleanup)` MIR body per item
  that preserves every optional overflow assertion via
  `AssertKind::is_optional_overflow_check()` and can be verified either
  fail-closed (forbidding overflow in both profiles) or parameterized by
  `(overflowChecks : Bool, ubChecks : Bool)`.

## Applicability

All source citations and empirical probe outputs apply to:

- **Rust toolchain**: `nightly-2026-05-31` (`rustc 1.98.0-nightly`, commit
  `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, commit date `2026-05-30`, target
  `x86_64-unknown-linux-gnu`, LLVM `22.1.6`).
- **Compiler subsystems**:
  - `compiler/rustc_mir_transform/src/{lib.rs,pass_manager.rs,cleanup_post_borrowck.rs,ctfe_limit.rs,trivial_const.rs,simplify.rs,simplify_branches.rs,instsimplify.rs,known_panics_lint.rs}`
  - `compiler/rustc_mir_build/src/builder/{mod.rs,expr/as_rvalue.rs,expr/stmt.rs,expr/into.rs,matches/mod.rs}`
  - `compiler/rustc_interface/src/{passes.rs,interface.rs}`
  - `compiler/rustc_driver_impl/src/lib.rs`
  - `compiler/rustc_hir_analysis/src/lib.rs`
  - `compiler/rustc_resolve/src/def_collector.rs`
  - `compiler/rustc_session/src/{session.rs,config/cfg.rs}`
  - `compiler/rustc_middle/src/{ty/mod.rs,mir/terminator.rs}`
  - `compiler/rustc_const_eval/src/interpret/{operator.rs,step.rs}`
  - `library/core/src/macros/mod.rs`
- **Related reference reports**:
  - `rustc-mir-phases-reachability-and-postcleanup-lowering` (overall MIR phase
    progression and reachability).
  - `rustc-postcleanup-mir-const-placement-layout-folding-and-ub-checks`
    (`Const` placement, layout folding, and `UbChecks` lowering).

## Findings

### Finding 1: Complete `Steal<Body>` Lifecycle Across `DefKind`s and `--emit=metadata` vs. `--emit=link`

In `compiler/rustc_mir_transform/src/lib.rs`, the three-stage MIR pipeline
stores intermediate bodies in `&'tcx Steal<Body<'tcx>>` so downstream stages can
take ownership without cloning when upstream stages no longer need the body:

1. `mir_built(def)` returns `&'tcx Steal<Body<'tcx>>` at `MirPhase::Built`
   (`lib.rs:362-403`). If `tcx.is_trivial_const(def)` is `true` (checked by
   `trivial_const::trivial_const_provider` in `trivial_const.rs:88-116`),
   `mir_built` returns immediately after ` custom_mir` / `pass_manager::dump_mir_for_phase_change`
   without running `run_post_borrowck_cleanup_passes` or later stages.
2. `mir_const(def)` steals `mir_built(def)` (`lib.rs:437`).
3. `mir_promoted(def)` steals `mir_const(def)` (`lib.rs:459`) and returns
   `(&'tcx Steal<Body<'tcx>>, &'tcx Steal<IndexVec<Promoted, Body<'tcx>>>)` at
   `MirPhase::Analysis(AnalysisPhase::PostCleanup)`. Note that `mir_promoted`
   asserts `debug_assert!(!tcx.is_trivial_const(def), ...)` (`lib.rs:453`) and
   `debug_assert!(!tcx.is_constructor(def.to_def_id()), ...)` (`lib.rs:454`).
4. `mir_borrowck(def)` borrows `&mir_promoted(def).0.borrow()` without stealing.
5. `mir_drops_elaborated_and_const_checked(def)` steals `mir_promoted(def).0`
   (`lib.rs:547`), runs `run_analysis_to_runtime_passes` (`lib.rs:569-670`), and
   allocates `&'tcx Steal<Body<'tcx>>` at
   `MirPhase::Runtime(RuntimePhase::PostCleanup)`.
6. `promoted_mir(def)` steals `mir_promoted(def).1` (`lib.rs:677`), runs
   `run_analysis_to_runtime_passes` on each promoted body, and returns an
   un-stealable `&'tcx IndexVec<Promoted, Body<'tcx>>` allocated directly in
   `tcx.arena` (`lib.rs:684`).

Across the entire compiler, only two functions ever call `.steal()` on the
`&'tcx Steal<Body<'tcx>>` returned by `mir_drops_elaborated_and_const_checked`:

- **`inner_mir_for_ctfe`** (`compiler/rustc_mir_transform/src/lib.rs:486-508`):
  Inspects `tcx.hir_body_const_context(def)`. For
  `Some(ConstContext::Const { .. } | ConstContext::Static(_))`, it calls
  `body.steal()` (`lib.rs:497`) because constants and statics do not have a
  separate `optimized_mir` runtime body. For `Some(ConstContext::ConstFn)`, it
  calls `body.borrow().clone()` (`lib.rs:500`) so that the `Steal<Body<'tcx>>`
  remains intact for `inner_optimized_mir`!
- **`inner_optimized_mir`** (`compiler/rustc_mir_transform/src/lib.rs:777-804`):
  If `tcx.hir_body_const_context(did)` is `Some(ConstContext::ConstFn)`, it
  first runs `tcx.ensure_done().mir_for_ctfe(did)` (`lib.rs:789`) so `mir_for_ctfe`
  can clone the un-stolen body, and then steals
  `tcx.mir_drops_elaborated_and_const_checked(did).steal()` (`lib.rs:795`).

In `rustc_driver_impl::run_compiler` (`compiler/rustc_driver_impl/src/lib.rs:326-341`),
`Callbacks::after_analysis(compiler, tcx)` runs immediately after
`tcx.analysis(())` (`compiler/rustc_interface/src/passes.rs:1199-1255`) and
**before** `emit_mir` or `codegen_and_build_linker`. During `tcx.analysis(())`:

- `rustc_hir_analysis::check_crate` (`compiler/rustc_hir_analysis/src/lib.rs:168-187`)
  evaluates every `Static` via `tcx.eval_static_initializer(def_id)` and every
  non-generic top-level `Const` via `tcx. const_eval_poly(def_id)`, both of
  which query `tcx.mir_for_ctfe(def_id)` and steal `mir_drops_elaborated_and_const_checked`
  for non-trivial constants. Type checking also evaluates `[T; N]` array lengths
  and explicit enum discriminants (`DefKind::AnonConst`).
- `run_required_analyses` (`compiler/rustc_interface/src/passes.rs:1166-1197`)
  iterates `tcx.hir_body_owners()`:
  - When `tcx.sess.opts.output_types.should_codegen() || tcx.hir_body_const_context(def_id).is_some()`,
    it runs `tcx.ensure_ok().mir_drops_elaborated_and_const_checked(def_id)`
    (`passes.rs:1174-1178`). Inside `mir_drops_elaborated_and_const_checked`,
    `KnownPanicsLint` (`compiler/rustc_mir_transform/src/known_panics_lint.rs:265-278`)
    evaluates any referenced `InlineConst` or concrete `Const` / `AssocConst`
    operand via `tcx.const_eval_resolve_for_typeck(...)`, which queries
    `mir_for_ctfe` and steals that constant's `Steal<Body>`.
  - For every coroutine (`tcx.is_coroutine(def_id.to_def_id())`), it queries
    `tcx.layout_of(...)` (`passes.rs:1179-1183`), which invokes
    `ordinary_coroutine_layout` (`compiler/rustc_middle/src/ty/mod.rs:1859`) and
    queries `tcx.optimized_mir(def_id)`, stealing the coroutine's
    `mir_drops_elaborated_and_const_checked`.

Experiment 1 (`support/probe_results.json`, `exp1_steal_and_ctfe`) verifies the
exact steal state across all 22 body-owning items in a comprehensive test crate
under both `--emit=metadata` (`should_codegen() == false`) and `--emit=link`
(`should_codegen() == true`):

| Item Kind (`DefKind`) | Example in Probe | `is_trivial_const` | Stolen at `after_analysis` entry (`--emit=metadata`) | Stolen at `after_analysis` entry (`--emit=link`) | Stolen after querying `mir_drops_elaborated` on all functions | Why |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `Fn`, `AssocFn` (non-const) | `regular_fn`, `S::method`, `fn_with_inline_const` | `false` | **`false`** | **`false`** | **`false`** | `optimized_mir` has not run before `after_analysis` |
| `Closure` (non-coroutine) | `fn_with_closure::{closure#0}` | `false` | **`false`** | **`false`** | **`false`** | `optimized_mir` has not run before `after_analysis` |
| `Fn`, `AssocFn` (`const fn`, used in CTFE or unused) | `const_fn_used_in_const`, `const_fn_unused`, `S::const_method` | `false` | **`false`** | **`false`** | **`false`** | `inner_mir_for_ctfe` calls `body.borrow().clone()` for `ConstFn` |
| `Closure` (coroutine: `async fn` body) | `async_fn::{closure#0}` | `false` | **`true`** | **`true`** | **`true`** | `run_required_analyses` computes `layout_of(coroutine)` -> `optimized_mir` |
| `Const` (top-level, non-trivial) | `TOP_CONST_NONTRIVIAL` (`const_fn_used_in_const(10) + 1`) | `false` | **`true`** | **`true`** | **`true`** | `check_crate` evaluates top-level `Const` via `mir_for_ctfe` -> `.steal()` |
| `Static` (non-trivial) | `TOP_STATIC_NONTRIVIAL` | `false` | **`true`** | **`true`** | **`true`** | `check_crate` calls `eval_static_initializer` -> `mir_for_ctfe` -> `.steal()` |
| `AnonConst` (array length, enum discr.) | `arr_len_fn::{constant#0}`, `EnumWithDiscr::V0::{constant#0}` | `false` | **`true`** | **`true`** | **`true`** | Typeck evaluates `[u8; N]` and discriminant via `mir_for_ctfe` -> `.steal()` |
| `InlineConst` (`const { 7 + 8 }`) | `fn_with_inline_const::{constant#0}` | `false` | **`false`** | **`true`** | **`true`** | Evaluated by `KnownPanicsLint` when parent `fn_with_inline_const`'s `mir_drops_elaborated` runs |
| `AssocConst` (used in non-const `fn`) | `S::ASSOC_C_USED` (`5 + 6`) | `false` | **`false`** | **`true`** | **`true`** | Not evaluated by `check_crate`; evaluated by `KnownPanicsLint` when `S::method`'s `mir_drops_elaborated` runs |
| `AssocConst` (unused or generic) | `S::ASSOC_C_UNUSED`, `Gen::<T>::GEN_C_UNUSED` | `false` | **`false`** | **`false`** | **`false`** | Neither `check_crate` nor `KnownPanicsLint` evaluates unreferenced `AssocConst` |
| Trivial `Const` / `Static` / `AnonConst` | `TOP_CONST_TRIVIAL` (`42`), `TOP_STATIC_TRIVIAL`, `EnumWithDiscr::V1::{constant#0}` | `true` | `None` (N/A) | `None` (N/A) | `None` (N/A) | `trivial_const` bypasses `mir_promoted` and `mir_drops_elaborated`; body lives in `mir_built` |
| Tuple-struct `Ctor` | `TupleStruct(u32)` | `false` | `None` (N/A) | `None` (N/A) | `None` (N/A) | `is_constructor` bypasses `mir_promoted`; shim synthesized in `mir_for_ctfe` / `mir_shims` |

Notice the subtle ordering hazard under `--emit=metadata` on `S::ASSOC_C_USED`
and `fn_with_inline_const::{constant#0}`: because `should_codegen()` is `false`
when `--emit=metadata` is passed, `run_required_analyses` does **not** force
`mir_drops_elaborated_and_const_checked` on non-const functions during
`tcx.analysis(())`. When `Callbacks::after_analysis` begins under
`--emit=metadata` and iterates `tcx.hir_body_owners()`, querying
`tcx.mir_drops_elaborated_and_const_checked(S::method)` triggers
`KnownPanicsLint`, which evaluates `S::ASSOC_C_USED` via `mir_for_ctfe` and
steals `S::ASSOC_C_USED` **mid-iteration**!

### Finding 2: Exact Relationship Between `mir_drops_elaborated_and_const_checked`, `mir_for_ctfe`, and `optimized_mir` / `tcx.instance_mir`

#### 2.1 What `mir_drops_elaborated_and_const_checked` (`Runtime(PostCleanup)`) Contains

`run_analysis_to_runtime_passes` (`compiler/rustc_mir_transform/src/lib.rs:569-670`)
advances a body from `MirPhase::Analysis(AnalysisPhase::PostCleanup)` through
`MirPhase::Runtime(RuntimePhase::Initial)` to
`MirPhase::Runtime(RuntimePhase::PostCleanup)`:

1. **`run_Analysis_to_Runtime_Initial`** (`lib.rs:575-626`):
   - `CleanupPostBorrowck` (`cleanup_post_borrowck.rs:25-90`): Deletes all
     `StatementKind::FakeRead` and `StatementKind::AscribeUserType` statements
     (replacing them with `Nop`), converts `BorrowKind::Fake(_)` borrows to
     `BorrowKind::Shared`, clears `user_ty` annotations on `Constant` and
     `LocalDecl`, lowers `CastKind::PointerCoercion(ArrayToPointer | MutToConstPointer)`
     to `CastKind::PtrToPtr`, and simplifies `TerminatorKind::FalseEdge` and
     `TerminatorKind::FalseUnwind` to `Goto`.
   - `Derefer`, `CriticalCallEdges`, `PostAnalysisNormalize`, `Subtyper`,
     `ElaborateDrops`, `AbortUnwindingCalls`, `AddMovesForPackedDrops`.
   -Note that in `rustc 1.98.0-nightly (f8a08b688)`, standalone
     `StatementKind::Retag` no longer exists; Miri retagging is carried by the
     `WithRetag` boolean on `Rvalue::Use(Operand, WithRetag)`.
2. **`run_runtime_cleanup_passes`** (`lib.rs:629-670`):
   - `EraseDerefTemps`, `ElaborateBoxDerefs`, `StateTransform` (coroutine state
     machine transformation), `KnownPanicsLint`, `CheckConstItemMutation`,
     `FunctionItemReferences`, `LowerIntrinsics` (lowers intrinsics such as
     `ub_checks` -> `Operand::RuntimeChecks(RuntimeChecks::UbChecks)` and
     `wrapping_add` -> `BinOp::Add`), `RemovePlaceMention` (strips all
     `StatementKind::PlaceMention`), and `SimplifyCfg::PreOptimizations`
     (strips `StatementKind::Nop` and dead blocks).
   - Finally, `mir_drops_elaborated_and_const_checked` sets
     `decl.local_info = ClearCrossCrate::Clear` on every `LocalDecl` (`lib.rs:572-574`).

#### 2.2 `mir_for_ctfe` vs. `mir_drops_elaborated_and_const_checked`

In `inner_mir_for_ctfe` (`compiler/rustc_mir_transform/src/lib.rs:486-508`),
after obtaining the `mir_drops_elaborated_and_const_checked` body (by stealing
for `Const`/`Static` or cloning for `ConstFn`), `rustc` runs only two steps:

1. `remap_mir_for_const_eval_select(tcx, body, hir::Constness::Const)`
   (`lib.rs:504`), which only modifies calls to
   `core::intrinsics::const_eval_select`.
2. `run_passes_no_validate(tcx, body, &[&ctfe_limit::CtfeLimit], None)`
   (`lib.rs:505`), where `CtfeLimit` (`compiler/rustc_mir_transform/src/ctfe_limit.rs:21-54`)
   appends `StatementKind::ConstEvalCounter` at the end of any basic block that
   terminates in `Call` or `TailCall` or has a control-flow back-edge
   (`target <= index`), with `phase_change = None` (leaving `body.phase` at
   `MirPhase::Runtime(RuntimePhase::PostCleanup)`).

Experiment 1 (`support/probe_results.json`, `exp1_steal_and_ctfe`) compares the
hook-captured `mir_drops_elaborated_and_const_checked` body against
`tcx.mir_for_ctfe(def)` across all 11 non-trivial constant and `const fn` items:
in **11 out of 11 items**, `ctfe_eq_post_mod_counter` is `true`—removing
`StatementKind::ConstEvalCounter` from `tcx.mir_for_ctfe(def)` yields a `Body`
whose basic blocks, statements, terminators, and local declarations are 100%
identical to `mir_drops_elaborated_and_const_checked(def)`.

#### 2.3 Why `tcx.instance_mir` (`optimized_mir`) Diverges Sharply at `-C opt-level=0`

`TyCtxt::instance_mir(InstanceKind::Item(def))`
(`compiler/rustc_middle/src/ty/mod.rs:1754-1771`) routes
`DefKind::Const | Static | AssocConst | Ctor | AnonConst | InlineConst` to
`tcx.mir_for_ctfe(def)` and all other items (`Fn`, `AssocFn`, `Closure`,
**including `const fn`**) to `tcx.optimized_mir(def)`.

Calling `tcx.instance_mir` or `tcx.optimized_mir` at `-C opt-level=0` does
**not** return `Runtime(PostCleanup)` MIR for two distinct reasons:

1. **Trap 1: `-C opt-level=0` leaves `sess.mir_opt_level() == 1`**. In
   `Session::mir_opt_level` (`compiler/rustc_session/src/session.rs:617-622`):
   ```rust
   pub fn mir_opt_level(&self) -> usize {
       self.opts
           .unstable_opts
           .mir_opt_level
           .unwrap_or_else(|| if self.opts.optimize == OptLevel::No { 1 } else { 2 })
   }
   ```
   Because `mir_opt_level` defaults to `1` at `-C opt-level=0`,
   `run_optimization_passes` (`compiler/rustc_mir_transform/src/lib.rs:689-775`)
   runs all `mir_opt_level >= 1` (`o1`) passes in addition to required passes:
   - `CheckAlignment`, `CheckNull`, `CheckEnums` (required passes when
     `sess.ub_checks()` is true),
   - `LowerSliceLenCalls`, `InstSimplify::BeforeInline`, `ForceInline`,
   - `UnreachableEnumBranching`, `SimplifyCfg::AfterUnreachableEnumBranching`,
     `InstSimplify::AfterSimplifyCfg`, `SimplifyConstCondition::AfterInstSimplify`,
   - `RemoveStorageMarkers`, `RemoveZsts`, `SimplifyLocals::BeforeConstProp`,
   - `SimplifyLocals::AfterGVN`, `SingleUseConsts`,
     `SimplifyConstCondition::AfterConstProp`, `RemoveNoopLandingPads`,
     `RemoveUnneededDrops`, `SimplifyConstCondition::Final`,
     `SimplifyCfg::Final`, `CopyProp`, `SimplifyLocals::Final`, and
     `CriticalCallEdges`,
   plus `remap_mir_for_const_eval_select(..., Constness::NotConst)` and
   `MentionedItems` in `inner_optimized_mir` (`lib.rs:796-800`).
2. **Trap 2: Even with `-Z mir-opt-level=0` or `#[optimize(none)]`, required
   passes still mutate the CFG**. In `pass_manager::should_run_pass`
   (`compiler/rustc_mir_transform/src/pass_manager.rs:212-227`), any pass with
   `P::is_required() == true` ignores `-Z mir-opt-level=0` and `#[optimize(none)]`.
   In particular, `CheckAlignment`, `CheckNull`, `CheckEnums`, `ForceInline`,
   `RemoveUnneededDrops`, `SimplifyCfg` (unless `#[optimize(none)]`), and
   `CriticalCallEdges` still run and transition `body.phase` to
   `MirPhase::Runtime(RuntimePhase::Optimized)`.

Experiment 2 (`support/probe_results.json`, `exp2_opt_vs_postcleanup`)
quantifies these differences across `-C opt-level=0` (`mir_opt_level == 1`) and
`-C opt-level=0 -Z mir-opt-level=0`:

| Item | `mir_drops_elaborated` (`PostCleanup`) | `instance_mir` at `-C opt-level=0` (`mir_opt_level=1`) | `instance_mir` at `-C opt-level=0 -Z mir-opt-level=0` | Causes of Divergence |
| :--- | :--- | :--- | :--- | :--- |
| `regular_fn` | 2 BBs, 11 locals, 25 stmts (16 `StorageLive`/`Dead`) | 2 BBs, 7 locals, 5 stmts (0 `StorageLive`/`Dead`) | 2 BBs, 11 locals, 25 stmts (`Runtime(Optimized)`) | `RemoveStorageMarkers`, `SimplifyLocals`, `CopyProp` at `mir_opt_level=1` |
| `const_fn_unused` | 2 BBs, 13 locals, 30 stmts (18 `StorageLive`/`Dead`) | 2 BBs, 7 locals, 8 stmts (0 `StorageLive`/`Dead`) | 2 BBs, 13 locals, 30 stmts (`Runtime(Optimized)`) | `instance_mir` routes `const fn` to `optimized_mir`, not `mir_for_ctfe` |
| `raw_ptr_deref` (`unsafe { *p }`, `ub-checks=on`) | **1 BB, 5 locals, 7 stmts, 0 asserts** | **4 BBs, 13 locals, 15 stmts** (`UbChecks` folded to `true`) | **4 BBs, 22 locals, 24 stmts** (2 `RuntimeChecks(UbChecks)` operands) | `CheckAlignment` + `CheckNull` (`is_required() == true`) inject 3 panic blocks even at `-Z mir-opt-level=0` |
| `no_opt_attr_fn` (`#[optimize(none)]`, `ub-checks=on`) | **1 BB, 11 locals, 18 stmts** | **4 BBs, 28 locals, 35 stmts** | **4 BBs, 28 locals, 35 stmts** | `#[optimize(none)]` suppresses `o1` passes, but required `CheckAlignment` + `CheckNull` still expand `*p` into 4 BBs |
| `TOP_CONST_NONTRIVIAL` | 2 BBs, 6 locals, 6 stmts (0 `ConstEvalCounter`) | 2 BBs, 6 locals, 7 stmts (1 `ConstEvalCounter`) | 2 BBs, 6 locals, 7 stmts (1 `ConstEvalCounter`) | `instance_mir` routes `Const` to `mir_for_ctfe`, which appends `ConstEvalCounter` |

#### 2.4 Capturing Un-Stolen `Runtime(PostCleanup)` MIR Without Process-Global `static Mutex` State

A `rustc_driver` tool has two clean alternatives that eliminate process-global
`static Mutex<BTreeMap<...>>` state:

1. **Zero-Hook Direct `after_analysis` Capture**: Inside
   `Callbacks::after_analysis(compiler, tcx)` (with no `override_queries` hook
   and no static or thread-local state):
   - For non-coroutine `Fn`, `AssocFn`, and `Closure` items (including
     `const fn`), borrow `tcx.mir_drops_elaborated_and_const_checked(def).borrow()`
     directly (guaranteed un-stolen per Finding 1).
   - For trivial constants (`tcx.is_trivial_const(def)`), borrow
     `tcx.mir_built(def).borrow()`.
   - For non-trivial constants and statics (`Const`, `AssocConst`, `AnonConst`,
     `InlineConst`, `Static`), borrow the arena-allocated `tcx.mir_for_ctfe(def)`
     and filter out `StatementKind::ConstEvalCounter` statements (recovering the
     exact `Runtime(PostCleanup)` body for every constant that does not call
     `core::intrinsics::const_eval_select`).
   - For promoted constants on any body owner, borrow `tcx.promoted_mir(def)`
     directly (arena-allocated `&'tcx IndexVec<Promoted, Body<'tcx>>`, never
     wrapped in `Steal`).
2. **Session-Scoped `thread_local!` Query-Provider Hook**: When a tool also
   needs pre-`mir_for_ctfe` bodies for constants calling `const_eval_select` or
   pre-`optimized_mir` bodies for coroutines, `Config::override_queries` takes a
   plain `fn(&Session, &mut Providers)` pointer. The default provider
   (`rustc_mir_transform::mir_drops_elaborated_and_const_checked`) is a
   stateless compile-time function pointer that can be stored once in a
   `OnceLock<fn(TyCtxt<'_>, LocalDefId) -> &Steal<Body<'_>>>` (or called
   directly via `(rustc_interface::DEFAULT_QUERY_PROVIDERS.mir_drops_elaborated_and_const_checked)(tcx, def)`),
   while captured summaries or translated MIR ASTs are written into a
   `thread_local! { static CAPTURED: RefCell<...> }` managed by an RAII scope
   guard around `rustc_driver::run_compiler` (demonstrated in
   `support/probe_mir_steal_and_profiles.rs:143-179`).

### Finding 3: Anatomy of `--release` vs. `--debug` Divergence Across AST, `DefIndex`, and `Runtime(PostCleanup)` MIR

#### 3.1 Session Flags and Built-In `cfg` Predicates

In `compiler/rustc_session/src/session.rs:724-735` and
`compiler/rustc_session/src/config/cfg.rs:194-214, 321-323`, `rustc` derives
three independent boolean checks and built-in `cfg` predicates from the session
options:

| Check / Predicate | Session Accessor (`session.rs`) | Default Fallback | Built-In `cfg(...)` (`cfg.rs`) |
| :--- | :--- | :--- | :--- |
| Debug assertions | `sess.opts.debug_assertions` (`-C debug-assertions=y/n`) | `false` at `-O` / `--release`, `true` otherwise | `cfg(debug_assertions)` (`sym::debug_assertions`) |
| Overflow checks | `sess.overflow_checks()` (`-C overflow-checks=y/n`) | `sess.opts.cg.overflow_checks.unwrap_or(sess.opts.debug_assertions)` | `cfg(overflow_checks)` (`sym::overflow_checks`, `#![feature(cfg_overflow_checks)]`) |
| UB checks | `sess.ub_checks()` (`-Z ub-checks=y/n`) | `sess.opts.unstable_opts.ub_checks.unwrap_or(sess.opts.debug_assertions)` | `cfg(ub_checks)` (`sym::ub_checks`, `#![feature(cfg_ub_checks)]`) |

#### 3.2 How `#[cfg(...)]` Shifts `LocalDefId` (`DefIndex`) and Breaks `DefIndex`-Keyed Merging

During AST resolution, `DefCollector` (`compiler/rustc_resolve/src/def_collector.rs:39-290`)
walks the post-expansion, post-`#[cfg]` AST and calls `create_def` sequentially
for every item, foreign item, trait item, impl item, variant, struct field,
generic parameter, `use` statement, macro definition, closure (`ExprKind::Closure`),
inline `const { ... }` block (`ExprKind::ConstBlock`), and anonymous constant
(`AnonConst`).

Consequently, if a crate uses `#[cfg(debug_assertions)]`,
`#[cfg(overflow_checks)]`, or `#[cfg(ub_checks)]` on **any** definition-creating
AST node—even a private closure inside a function body—the sequential
`DefIndex` of every subsequent item in the crate shifts between `--release` and
`--debug`. Experiment 3B (`support/probe_results.json`,
`exp3b_def_index_shift`) demonstrates this shift on a minimal module:

| Item Path | `DefKind` | `--release` `DefIndex` | `--debug` `DefIndex` | Cause of Shift |
| :--- | :--- | :--- | :--- | :--- |
| `before_cfg` | `Fn` | `3` | `3` | Precedes all `#[cfg]`-gated definitions |
| `contains_cfg_closure` | `Fn` | `4` | `4` | Enclosing function `DefId` allocated before visiting its body |
| `contains_cfg_closure::{closure#0}` | `Closure` | *(absent)* | `5` | `#[cfg(debug_assertions)]` closure inside `contains_cfg_closure` |
| `after_cfg_closure` | `Fn` | **`5`** | **`6`** | Shifted by `+1` because `{closure#0}` took `DefIndex 5` in `--debug` |
| `EXTRA_CONST` | `Const` | *(absent)* | `7` | `#[cfg(overflow_checks)] const EXTRA_CONST: u32 = 99;` |
| `after_cfg_item` | `Fn` | **`6`** | **`8`** | Shifted by `+2` in `--debug` |

A dual-session driver that pairs items across `--release` and `--debug` by
`DefIndex` mismatches `after_cfg_closure` (pairing `--release`
`after_cfg_closure` at `DefIndex 5` with `--debug`
`contains_cfg_closure::{closure#0}` at `DefIndex 5`) and `after_cfg_item`
(pairing `--release` `after_cfg_item` at `DefIndex 6` with `--debug`
`after_cfg_closure` at `DefIndex 6`).

#### 3.3 Exact Operator and Macro Divergence Matrix in `Runtime(PostCleanup)` MIR

In `rustc_mir_build`, `Builder::new`
(`compiler/rustc_mir_build/src/builder/mod.rs:757-765`) initializes
`builder.check_overflow` as follows:

```rust
let check_overflow = tcx.has_attr(def_id, sym::rustc_inherit_overflow_checks)
    || match hir_Owner {
        hir::BodyOwnerKind::Closure | hir::BodyOwnerKind::Fn => tcx.sess.overflow_checks(),
        // Constants always need overflow checks.
        hir::BodyOwnerKind::Const { .. } | hir::BodyOwnerKind::Static(_) => true,
    };
```

Inside `compiler/rustc_mir_build/src/builder/expr/as_rvalue.rs` (`as_rvalue` at
lines `99-125` and `build_binary_op` at lines `444-592`) and `stmt.rs`
(compound assignment operators `+=`, `-=`, `*=`, `<<=`, `>>=` at lines
`80-89`), `self.check_overflow` is consulted for **only six integer operations**:

1. **Integer `BinOp::Add`, `BinOp::Sub`, `BinOp::Mul`** (`as_rvalue.rs:456-481`):
   - When `check_overflow == false`: emits `_0 = BinaryOp(Add | Sub | Mul, l, r)`
     in 1 basic block.
   - When `check_overflow == true`: emits
     `_tmp = BinaryOp(AddWithOverflow | SubWithOverflow | MulWithOverflow, l, r)`
     returning `(T, bool)`, followed by
     `TerminatorKind::Assert { cond: move (_tmp.1: bool), expected: false, msg: AssertKind::Overflow(Add | Sub | Mul, l, r), target: bb1 }`
     and `_0 = move (_tmp.0: T)` in `bb1` (2 basic blocks).
2. **Integer `BinOp::Shl`, `BinOp::Shr`** (`as_rvalue.rs:498-528`):
   - When `check_overflow == false`: emits `_0 = BinaryOp(Shl | Shr, l, r)` in
     1 basic block.
   - When `check_overflow == true`: converts signed RHS to unsigned via
     `CastKind::IntToInt` if needed, computes
     `_inbounds = BinaryOp(Lt, unsigned_rhs, const BITS)`, and emits
     `TerminatorKind::Assert { cond: move _inbounds, expected: true, msg: AssertKind::Overflow(Shl | Shr, l, r), target: bb1 }`
     before `_0 = BinaryOp(Shl | Shr, l, r)` in `bb1` (2 basic blocks).
3. **Signed Integer `UnOp::Neg`** (`as_rvalue.rs:102-122`):
   - When `check_overflow == false`: emits `_0 = UnaryOp(Neg, a)` in 1 basic
     block.
   - When `check_overflow == true`: computes `_is_min = BinaryOp(Eq, a, const MIN)`
     and emits
     `TerminatorKind::Assert { cond: move _is_min, expected: false, msg: AssertKind::OverflowNeg(a), target: bb1 }`
     before `_0 = UnaryOp(Neg, a)` in `bb1` (2 basic blocks).

Crucially, `AssertKind::is_optional_overflow_check`
(`compiler/rustc_middle/src/mir/terminator.rs:164-168`) identifies **precisely**
these six operations:

```rust
pub fn is_optional_overflow_check(&self) -> bool {
    use AssertKind::*;
    use BinOp::*;
    matches!(self, OverflowNeg(..) | Overflow(Add | Sub | Mul | Shl | Shr, ..))
}
```

Experiment 3A (`support/probe_results.json`, `exp3a_divergence_matrix`) tests 24
constructs across all 4 profile combinations (`release`, `debug`,
`overflow_only`, `debug_assert_only`) and confirms the complete invariance and
divergence matrix at `Runtime(PostCleanup)`:

| Construct (`EXP 3A`) | `release` (`dbg=off, ovf=off`) | `debug` (`dbg=on, ovf=on`) | `overflow_only` (`dbg=off, ovf=on`) | `debug_assert_only` (`dbg=on, ovf=off`) | Identical Across All 4 Profiles? |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `add_u32`, `sub_u32`, `mul_u32`, `add_assign_u32` | 1 BB, `BinaryOp(Add/Sub/Mul)`, 0 asserts | 2 BBs, `BinaryOp(*WithOverflow)` + `Assert(Overflow)`, 1 assert | Same as `debug` | Same as `release` | **No** (depends solely on `overflow-checks`) |
| `shl_u32`, `shr_i32` | 1 BB, `BinaryOp(Shl/Shr)`, 0 asserts | 2 BBs, `BinaryOp(Lt, rhs, 32)` + `Assert(Overflow)` + `BinaryOp(Shl/Shr)`, 1 assert | Same as `debug` | Same as `release` | **No** (depends solely on `overflow-checks`) |
| `neg_i32` | 1 BB, `UnaryOp(Neg)`, 0 asserts | 2 BBs, `BinaryOp(Eq, a, i32::MIN)` + `Assert(OverflowNeg)` + `UnaryOp(Neg)`, 1 assert | Same as `debug` | Same as `release` | **No** (depends solely on `overflow-checks`) |
| `div_u32`, `rem_u32` | 2 BBs, `Assert(DivisionByZero / RemainderByZero)` | 2 BBs (100% identical) | 2 BBs (100% identical) | 2 BBs (100% identical) | **Yes** (`Div`/`Rem` checks are unconditional) |
| `div_i32`, `rem_i32` | 3 BBs, `Assert(DivisionByZero / RemainderByZero)` + `Assert(Overflow(Div/Rem))` (`MIN / -1`) | 3 BBs (100% identical) | 3 BBs (100% identical) | 3 BBs (100% identical) | **Yes** (signed `MIN / -1` overflow check is unconditional) |
| `bit_and_or_xor`, `neg_bool` | 1 BB, 0 asserts | 1 BB (100% identical) | 1 BB (100% identical) | 1 BB (100% identical) | **Yes** |
| `wrapping_ops`, `checked_ops`, `overflowing_ops`, `saturating_ops` | `TerminatorKind::Call` to `core::num` method (`wrapping_add` lowered to `BinOp::Add` if intrinsic) | 100% identical | 100% identical | 100% identical | **Yes** |
| `unchecked_add_u32` (`core::intrinsics::unchecked_add`) | 1 BB, `BinaryOp(AddUnchecked)` (lowered by `LowerIntrinsics`) | 1 BB (100% identical) | 1 BB (100% identical) | 1 BB (100% identical) | **Yes** |
| `inherit_ovf_add` (`#[rustc_inherit_overflow_checks]`) | 2 BBs, `AddWithOverflow` + `Assert(Overflow)` | 2 BBs (100% identical) | 2 BBs (100% identical) | 2 BBs (100% identical) | **Yes** (`Builder::new` forces `check_overflow = true`) |
| `slice_index` (`s[i]`) | 2 BBs, `Len` + `Lt` + `Assert(BoundsCheck)` | 2 BBs (100% identical) | 2 BBs (100% identical) | 2 BBs (100% identical) | **Yes** |
| `CONST_ADD` (`const CONST_ADD: u32 = ...;`) | 2 BBs, `AddWithOverflow` + `Assert(Overflow)` | 2 BBs (100% identical) | 2 BBs (100% identical) | 2 BBs (100% identical) | **Yes** (`BodyOwnerKind::Const` forces `check_overflow = true`) |
| `const_fn_add` (`pub const fn const_fn_add(...)`) | **1 BB, `BinaryOp(Add)`, 0 asserts** | **2 BBs, `AddWithOverflow` + `Assert(Overflow)`** | Same as `debug` | Same as `release` | **No** (`const fn` has `BodyOwnerKind::Fn`!) |
| `intrinsic_runtime_checks` (`ub_checks() ^ overflow_checks()`) | 1 BB, `Operand::RuntimeChecks(UbChecks)` + `Operand::RuntimeChecks(OverflowChecks)` | 1 BB (100% identical) | 1 BB (100% identical) | 1 BB (100% identical) | **Yes** (`RuntimeChecks` is not folded until `InstSimplify` in `optimized_mir`) |
| `with_debug_assert_simple` (`debug_assert!(a > 0)`) | **6 BBs**, `_3 = const false`, `SwitchInt(_3)` -> `bb1..bb3` (`panic`) / `bb4` | **6 BBs**, `_3 = const true`, `SwitchInt(_3)` -> `bb1..bb3` (`panic`) / `bb4` | Same as `release` | Same as `debug` | **No** (same 6-BB CFG, differs in `_3 = const false` vs. `const true`) |

Two findings in this matrix merit special emphasis:

1. **`const fn` compile-time CTFE depends on `-C overflow-checks` (`EXP 4`)**:
   Because `const fn` has `BodyOwnerKind::Fn` rather than `BodyOwnerKind::Const`,
   `Builder::new` sets `check_overflow = tcx.sess.overflow_checks()` when
   building a `const fn`. When `mir_for_ctfe` clones that `const fn` body for
   compile-time evaluation, CTFE executes `BinOp::Add` (wrapping!) when
   `-C overflow-checks=off` and `BinOp::AddWithOverflow` + `Assert` (panicking!)
   when `-C overflow-checks=on`. Experiment 4 (`support/probe_results.json`,
   `exp4_ctfe_const_fn_overflow`) confirms that compiling
   `pub const fn cfn_add(a: u32, b: u32) -> u32 { a + b } pub const C: u32 = cfn_add(u32::MAX, 1);`
   **succeeds** under `-C overflow-checks=off` (evaluating `C` to `0`) and
   **fails with `E0080` (`attempt to compute 'u32::MAX + 1_u32', which would overflow`)**
   under `-C overflow-checks=on`!
2. **`debug_assert!` retains its full 6-block panic CFG in `Runtime(PostCleanup)`**:
   In `library/core/src/macros/mod.rs:287-293`, `debug_assert!(cond)` expands to
   `if $crate::cfg!(debug_assertions) { $crate::assert!(cond); }`. In
   `rustc_mir_build`, `if false { ... }` still lowers both branches of the `if`
   around `TerminatorKind::SwitchInt { discr: move _3, targets: [false -> bb4, otherwise -> bb1] }`
   where `_3 = const false`. In `Runtime(PostCleanup)`, `SimplifyCfg::PreOptimizations`
   (`compiler/rustc_mir_transform/src/simplify.rs:306-328`) only collapses a
   `SwitchInt` when **all** target basic blocks are equal; constant-condition
   folding (`SimplifyConstCondition` in `simplify_branches.rs`) only runs in
   `optimized_mir`! Thus, in `Runtime(PostCleanup)`, `with_debug_assert_simple`
   has the exact same 6 basic blocks and panic call under `--release` and
   `--debug`, differing only in `_3 = const false` vs. `_3 = const true`.

### Finding 4: When Single-Session Capture Soundly Covers Both `--release` and `--debug`

Because `rustc` itself uses a single MIR representation for `#[rustc_inherit_overflow_checks]`
functions and resolves optional overflow checks during interpretation
(`compiler/rustc_const_eval/src/interpret/step.rs:623-627`) and codegen
(`compiler/rustc_codegen_ssa/src/mir/block.rs:714-716`) via
`msg.is_optional_overflow_check()`, a verification pipeline does **not** need to
run `rustc_driver::run_compiler` twice or duplicate `BodyId`s for every function
 whose arithmetic differs between `--release` and `--debug`:

1. **Single-Session `-C overflow-checks=on` Capture**:
   When `rustc_driver` runs once with `-C overflow-checks=on`:
   - Every integer `+`, `-`, `*` is lowered to
     `Rvalue::BinaryOp(AddWithOverflow | SubWithOverflow | MulWithOverflow, l, r)`
     followed by `TerminatorKind::Assert { cond, expected: false, msg: AssertKind::Overflow(Add | Sub | Mul, l, r), target }`.
   - Every integer `<<`, `>>` is lowered to a shift-distance bounds check
     followed by `TerminatorKind::Assert { cond, expected: true, msg: AssertKind::Overflow(Shl | Shr, l, r), target }`
     and `Rvalue::BinaryOp(Shl | Shr, l, r)`.
   - Every signed integer unary `-` is lowered to a `lhs == MIN` check followed
     by `TerminatorKind::Assert { cond, expected: false, msg: AssertKind::OverflowNeg(a), target }`
     and `Rvalue::UnaryOp(Neg, a)`.
   - All six assertions carry `msg.is_optional_overflow_check() == true`,
     distinguishing them from unconditional assertions (`DivisionByZero`,
     `RemainderByZero`, `Overflow(Div | Rem, ..)`, `BoundsCheck`,
     `MisalignedPointerDereference`, `NullPointerDereference`, `InvalidEnumConstruction`).
2. **Soundness Under Fail-Closed (No-Overflow / No-Panic) Verification**:
   When a verifier proves that a function's `Runtime(PostCleanup)` MIR body
   captured under `-C overflow-checks=on` never fails any `TerminatorKind::Assert`:
   - Under `--debug` (`overflow-checks=on`), every `Assert` succeeds and branches
     to `target`.
   - Under `--release` (`overflow-checks=off`), because `(AddWithOverflow(l, r)).0`
     equals wrapping `Add(l, r)` (`compiler/rustc_const_eval/src/interpret/operator.rs:84-135`),
     and `Shl`, `Shr`, and `Neg` execute the exact same `BinaryOp(Shl | Shr)` /
     `UnaryOp(Neg)` instruction after the skipped `Assert`, any execution prefix
     that satisfies the `-C overflow-checks=on` assertions produces the **exact
     same values and state transitions** in `--release`.
3. **Soundness Under Profile-Parameterized (`overflowChecks : Bool`, `ubChecks : Bool`) Semantics**:
   If a verifier explicitly models both wrapping (`overflowChecks = false`) and
   panicking (`overflowChecks = true`) semantics on the single captured
   `-C overflow-checks=on` body:
   - `Operand::RuntimeChecks(RuntimeChecks::OverflowChecks)` evaluates to
     `overflowChecks`, and `Operand::RuntimeChecks(RuntimeChecks::UbChecks)`
     evaluates to `ubChecks`.
   - At `TerminatorKind::Assert { cond, expected, msg, target, .. }`, when
     `!overflowChecks && msg.is_optional_overflow_check()` is true, the
     semantics transitions directly to `target` without requiring
     `cond == expected` (matching `InterpCx::terminator` in `step.rs:623-627`
     and `FunctionCx::codegen_assert_terminator` in `block.rs:714-716`), while
     still computing the wrapping low bits in `(_tmp.0: T)` for
     `AddWithOverflow` / `SubWithOverflow` / `MulWithOverflow` and the masked
     shift / wrapping negation for `Shl` / `Shr` / `Neg`.
4. **Conditions Requiring Profile-Specific Handling**:
   A single `-C overflow-checks=on` session suffices for all items in a crate
   **unless** the crate contains:
   - AST-level `#[cfg(debug_assertions)]`, `#[cfg(overflow_checks)]`, or
     `#[cfg(ub_checks)]` attributes (which can alter item definitions, types, or
     statements before MIR construction), or
   - `cfg!(debug_assertions)` / `debug_assert!(...)` / `cfg!(overflow_checks)` /
     `cfg!(ub_checks)` macro expansions (which expand to a `bool` literal in the
     AST before HIR lowering; if a crate uses `debug_assert!`, running with
     `-C debug-assertions=on -C overflow-checks=on` under fail-closed
     verification proves that `debug_assert!` also holds and does not panic,
     which implies the `--release` `const false` no-op branch is also safe
     provided the condition expression `cond` is side-effect-free).

## Boundaries

1. **Coroutines (`async fn`, `gen` blocks)**: Because `run_required_analyses`
   computes `tcx.layout_of(...)` on every coroutine during `tcx.analysis(())`,
   `mir_drops_elaborated_and_const_checked` is always stolen before
   `Callbacks::after_analysis` for coroutine bodies. Capturing `Runtime(PostCleanup)`
   MIR for coroutines requires an `override_queries` hook on
   `mir_drops_elaborated_and_const_checked` (or `mir_for_ctfe` cannot be used
   because coroutines are not constants).
2. **Constants calling `core::intrinsics::const_eval_select`**: For constants
   that invoke `const_eval_select`, `inner_mir_for_ctfe` rewrites the
   `const_eval_select` call target to the compile-time closure via
   `remap_mir_for_const_eval_select(tcx, body, Constness::Const)`. Recovering
   the un-rewritten `Runtime(PostCleanup)` body for such constants requires the
   `override_queries` hook rather than `tcx.mir_for_ctfe`.
3. **Side-effecting `debug_assert!` conditions**: If a `debug_assert!(side_effect())`
   call mutates state inside its condition expression, `--debug` executes
   `side_effect()` while `--release` skips it (`if false { ... }`). Single-session
   `-C debug-assertions=on` capture is sound for `--release` only when
   `debug_assert!` conditions are pure (or when `debug_assert!` divergence is
   detected by checking whether any macro expansion in the function's HIR spans
   originated from `debug_assert!` / `cfg!`).
4. **`-Z validate-mir` flag**: If `rustc` is invoked with `-Z validate-mir`,
   `run_required_analyses` (`compiler/rustc_interface/src/passes.rs:1192-1195`)
   forces `tcx.instance_mir(...)` on all body owners during `tcx.analysis(())`,
   stealing `mir_drops_elaborated_and_const_checked` for all functions before
   `after_analysis`. Standard verification invocations without `-Z validate-mir`
   leave all non-coroutine functions un-stolen.

## Evidence

- **Primary `rustc` source files (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`)**:
  - `compiler/rustc_mir_transform/src/lib.rs:215-838` (`mir_built`, `mir_const`,
    `mir_promoted`, `mir_drops_elaborated_and_const_checked`, `inner_mir_for_ctfe`,
    `run_analysis_to_runtime_passes`, `run_optimization_passes`,
    `inner_optimized_mir`).
  - `compiler/rustc_mir_transform/src/pass_manager.rs:195-228`
    (`should_run_pass`, `is_required()`, `mir_opt_level`).
  - `compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs:25-90`
    (`CleanupPostBorrowck`).
  - `compiler/rustc_mir_transform/src/ctfe_limit.rs:21-54` (`CtfeLimit`).
  - `compiler/rustc_mir_transform/src/trivial_const.rs:88-116`
    (`trivial_const_provider`).
  - `compiler/rustc_mir_transform/src/known_panics_lint.rs:265-278`
    (`KnownPanicsLint::eval_constant`).
  - `compiler/rustc_mir_transform/src/simplify.rs:306-328` (`SimplifyCfg`
    `SwitchInt` target collapsing).
  - `compiler/rustc_mir_transform/src/simplify_branches.rs:18-97`
    (`SimplifyConstCondition`).
  - `compiler/rustc_mir_build/src/builder/mod.rs:757-765` (`Builder::new`
    `check_overflow` initialization).
  - `compiler/rustc_mir_build/src/builder/expr/as_rvalue.rs:99-125, 444-592`
    (unary and binary operator overflow-check lowering).
  - `compiler/rustc_mir_build/src/builder/expr/stmt.rs:80-89` (compound
    assignment overflow-check lowering).
  - `compiler/rustc_interface/src/passes.rs:1166-1255` (`run_required_analyses`
    and `analysis`).
  - `compiler/rustc_driver_impl/src/lib.rs:326-341` (`Callbacks::after_analysis`
    invocation timing).
  - `compiler/rustc_hir_analysis/src/lib.rs:168-187` (`check_crate` static and
    top-level constant evaluation).
  - `compiler/rustc_resolve/src/def_collector.rs:39-290` (`DefCollector`
    sequential `DefIndex` allocation).
  - `compiler/rustc_session/src/session.rs:617-622, 724-735`
    (`Session::mir_opt_level`, `overflow_checks`, `ub_checks`).
  - `compiler/rustc_session/src/config/cfg.rs:194-214, 321-323` (built-in
    `debug_assertions`, `overflow_checks`, and `ub_checks` `cfg` predicates).
  - `compiler/rustc_middle/src/ty/mod.rs:1754-1771, 1855-1865`
    (`TyCtxt::instance_mir` and `ordinary_coroutine_layout`).
  - `compiler/rustc_middle/src/mir/terminator.rs:164-168`
    (`AssertKind::is_optional_overflow_check`).
  - `compiler/rustc_const_eval/src/interpret/step.rs:623-627` and
    `compiler/rustc_codegen_ssa/src/mir/block.rs:714-716` (optional overflow
    assertion skipping).
  - `library/core/src/macros/mod.rs:287-293` (`debug_assert!` expansion).
- **Reproducible probe and machine-readable output**:
  - `support/probe_mir_steal_and_profiles.rs`: Self-contained `rustc_driver`
    probe executing Experiments 1, 2, 3A, 3B, and 4 using a session-scoped
    `thread_local!` `override_queries` hook and asserting all structural
    invariants.
  - `support/probe_results.json`: Exact JSON output across all four experiments.
  - `support/run_probe.sh`: Automated build, execution, and byte-for-byte diff
    verification script.

## Revalidation

Run `support/run_probe.sh` with `nightly-2026-05-31` installed via `rustup`:

```bash
./reports/rustc-mir-steal-lifetimes-and-dual-profile-capture/support/run_probe.sh
```

The script compiles `support/probe_mir_steal_and_profiles.rs` against
`nightly-2026-05-31`, runs all four experiments in an isolated temporary
directory, and verifies via `diff -u` that the generated `probe_results.json`
matches `support/probe_results.json` byte-for-byte.
