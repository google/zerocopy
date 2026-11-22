# `rustc` `#![feature(async_drop)]`, `TerminatorKind::CoroutineDrop`, `future_drop_poll` / `AsyncDropGlue` Shim Synthesis, Cross-Crate Feature-Gate Non-Transitivity, and Live `Miri` Double-Drop Undefined Behavior

## Summary

Under `#![feature(async_drop)]` (unstable tracking issue `rust-lang/rust#126482`), `rustc` lowers asynchronous destruction across five interacting compiler subsystems: `core::future::async_drop` (`library/core/src/future/async_drop.rs:1-58`), HIR destructor coherence (`compiler/rustc_hir_analysis/src/check/mod.rs:125-142`), MIR drop elaboration (`compiler/rustc_mir_transform/src/elaborate_drop.rs`), coroutine state-machine lowering (`compiler/rustc_mir_transform/src/coroutine/{mod.rs,drop.rs}`), and monomorphized drop-shim synthesis (`compiler/rustc_mir_transform/src/shim.rs` and `shim/async_destructor_ctor.rs`). Primary-source audit across `rust-lang/rust` HEAD (`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`), `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, byte-identical across all five audited core/MIR files), and `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), combined with an 11-case empirical `rustc` and `Miri` (`-Zmiri-tree-borrows`) probe suite ([`support/probe_async_drop_and_double_drop_ub.py`](support/probe_async_drop_and_double_drop_ub.py)) and a zero-`sorry`, zero-`Classical.choice`, zero-`._unsafe_rec` Lean `v4.34.1` formalization ([`support/AsyncDropCoroutineStateAndDoubleDropSoundness.lean`](support/AsyncDropCoroutineStateAndDoubleDropSoundness.lean)), establishes six core findings:

1. **Companion Sync `Drop` Mandate and Cleanup-Edge Sync Fallback:**
   - Every `impl AsyncDrop for T` requires a companion `impl Drop for T` (`adt_destructor` emits ``error: `AsyncDrop` impl without `Drop` impl`` at `compiler/rustc_hir_analysis/src/check/mod.rs:125-135`), because synchronous scopes and every unwind cleanup edge (`!is_cleanup` / `!unwind.is_cleanup()` at `elaborate_drop.rs:636, 1249, 1311, 1578`) unconditionally dispatch to synchronous `Drop::drop`.
   - On normal `async` scope exits, `elaborate_drop.rs:227-632` expands each `AsyncDrop` site into a dual `Pin::new_unchecked` + `Future::poll` + `TerminatorKind::Yield { drop: Some(dropline_bb) }` loop wired into a three-track reverse-order drop ladder (`normal_ladder`, `dropline_ladder`, `unwind_ladder`, `elaborate_drop.rs:838-955`), preserving `Pin<&mut Self>` address stability and self-referential raw-pointer validity across `.await` points inside `AsyncDrop::drop` (verified under native execution and `Miri -Zmiri-tree-borrows`, `rc = 0`).
2. **Live `Miri` Heap Use-After-Free Double-Drop Bug in `async_drop_in_place` — Both `UNRESUMED` and `TerminatorKind::CoroutineDrop` Omit `SetDiscriminant(RETURNED)`:**
   - Calling textbook `unsafe { async_drop_in_place(&mut *slot).await; }` inside an `async` block on `slot: ManuallyDrop<Coro>` invokes `Coro::future_drop_poll` **twice**: first inside the `.await` poll loop (`Proxy1 = async_drop_in_place<Coro>::{closure#0}`), and a **second time** when the enclosing `async` block async-drops the `.await` temporary `Proxy1` at the semicolon (`Proxy2 = async_drop_in_place<Proxy1>::{closure#0}`), because `Ty::find_async_drop_impl_coroutine` (`compiler/rustc_middle/src/ty/sty.rs:1558-1575`) unwraps all nested `async_drop_in_place` wrappers directly to `Coro`, causing `build_future_drop_poll_shim` (`async_destructor_ctor.rs:176-194, 200-304`) to re-poll `Coro::future_drop_poll` unconditionally.
   - Neither `insert_clean_drop` (`coroutine/drop.rs:148-174`, entered on `CoroutineArgs::UNRESUMED` when `has_async_drops = true` at `L281` and when `has_async_drops = false` via `create_coroutine_drop_shim_proxy_async` at `L356-408` -> `create_coroutine_drop_shim` at `L196`) **nor** `TerminatorKind::CoroutineDrop` rewriting in `create_coroutine_drop_shim_async` (`coroutine/drop.rs:304-310`) emits `SetDiscriminant(CoroutineArgs::RETURNED)`.
   - Consequently, `Miri -Zmiri-tree-borrows` reports immediate heap use-after-free Undefined Behavior (`rc = 1`, dangling `Box<u32>`) across **four distinct scenarios**: (a) unresumed coroutine with `has_async_drops = true` (`1.98.0-nightly` and `1.102.0-nightly`), (b) unresumed plain-`Box` coroutine with `has_async_drops = false` (`1.102.0-nightly` UAF; `1.98.0-nightly` memory leak due to an earlier missing `make_coroutine_state_argument_pinned` call), (c) **suspended** coroutine whose local's `AsyncDrop::drop` returns `Poll::Ready(())` on the first poll without yielding (`rc = 1` UAF), and (d) **suspended** coroutine whose `AsyncDrop` resource remained an unmoved upvar (`rc = 1` UAF).
   - A suspended coroutine whose local's `AsyncDrop::drop` **yields `Poll::Pending` at least once** passes `Miri -Zmiri-tree-borrows` (`rc = 0`) **only incidentally**: yielding transitions the outer coroutine discriminant to a dropline yield variant (`Suspend_dropline`) storing the nested `async_drop_in_place<T>` sub-future, which reaches `TerminatorKind::Return`, sets its *own* discriminant to `RETURNED`, and returns `Poll::Ready(())` idempotently on re-poll (`coroutine/mod.rs:915-918`). Driving `async_drop_in_place(&mut *slot)` synchronously via `block_on(drop_fut)` (outside an `async` block) also avoids UB (`rc = 0`) because no `Proxy2` temporary drop occurs.
3. **Safe-Rust Unresumed Upvar Sync-Fallback:**
   - `elaborate_coroutine_drops` (`coroutine/drop.rs:85-145`) hardcodes `produce_async_drops: false` at `L103` (annotated `FIXME(async_drop)` at `L100-102`). In 100% safe Rust (zero `unsafe`), implicitly dropping an unresumed `async move` block owning an `AsyncDrop` upvar inside an outer `async` block silently executes synchronous `Drop::drop` rather than `AsyncDrop::drop` (`rc = 0`).
4. **Cross-Crate Feature-Gate Non-Transitivity Contradicting Compiler Warning and Breaking Partial-Move Transparency:**
   - When a downstream crate omits `#![feature(async_drop)]` while linking a dependency containing `AsyncDrop` types, `CStore::report_incompatible_async_drop_feature` (`compiler/rustc_metadata/src/creader.rs:638-656`, diagnostic in `diagnostics.rs:589-603`) warns *"if async drop type will be dropped in a crate without `feature(async_drop)`, sync `Drop` will be used"*.
   - In direct contradiction to that warning, `check_if_can_async_drop` (`elaborate_drop.rs:679-695`) short-circuits with a **shallow, non-transitive top-level check** (`if let ty::Adt(adt_def, _) = drop_ty.kind() { !adt_def.did().is_local() && adt_def.async_destructor(self.tcx()).is_some() } else { false }`) before calling the transitive `Ty::needs_async_drop` query (`compiler/rustc_ty_utils/src/needs_drop.rs:41-63`). Empirically, bare `dep::DepGuard` executes `AsyncDrop::drop` (`1000`), whereas `Some(dep::DepGuard)`, `[dep::DepGuard; 1]`, `(dep::DepGuard,)`, `Box::new(dep::DepGuard)`, `LocalWrap(dep::DepGuard)`, and even `dep::DepWrap(dep::DepGuard)` execute sync `Drop::drop` (`10`). Worse, partially moving an unrelated sibling out of `(dep::DepGuard, String)` triggers `DropStyle::Open` (`elaborate_drop.rs:745-748, 958-972`), flipping the remaining `dep::DepGuard` field from sync `Drop` (`10`) to `AsyncDrop` (`1000`).
5. **Architectural Shift Between `1.98.0-nightly` and `1.102.0-nightly` / HEAD:**
   - Between `14210df0e` (`2026-05-31`) and `3ef0c22cd` (`2026-11-11`, identical through `342d74463` on `2026-11-22`), `rustc` moved `Yield`-loop expansion out of `coroutine/drop.rs` (`expand_async_drops`, removing `TerminatorKind::Drop::async_fut`) upstream into `elaborate_drop.rs:227-632`, and added `make_coroutine_state_argument_pinned` to `create_coroutine_drop_shim_proxy_async` (`coroutine/drop.rs:394`). That fix eliminated a silent memory leak on plain-`Box` coroutines in `1.98.0-nightly`, exposing the latent missing-`RETURNED` double-drop UAF on `1.102.0-nightly`.
6. **Anneal Trusted-Boundary Fail-Closed Status and Mechanized Lean `v4.34.1` Theorems:**
   - At `joshlf/anneal` commit `c131b320eeeb26ef692e5afd5ec8db49ee518613`, `Trusted.MirAst` and `Trusted.MirSemantics` fail closed on all coroutine types (`MirTy.unsupported` at `MirAst.lean:308-321`) and all `Drop`, `Yield`, and `CoroutineDrop` terminators (`TerminatorKind.unsupported` at `MirAst.lean:782-795`; `evalTerminator` yields `.fault .unsupported` at `MirSemantics.lean:1568-1569`).
   - [`support/AsyncDropCoroutineStateAndDoubleDropSoundness.lean`](support/AsyncDropCoroutineStateAndDoubleDropSoundness.lean) formalizes the state-machine idempotence biconditionals (`futureDropPoll_idempotent_iff_marks_returned`, `futureDropPoll_suspended_immediate_idempotent_iff_coroDrop_marks_returned`), accidental yielding safety (`futureDropPoll_suspended_yielding_accidentally_safe`), reverse-order drop-ladder completeness (`async_drop_ladder_exact_once_per_init_field`), cross-crate gate compositionality (`transitive_gate_restores_wrapper_compositionality`), and four constructive sharpness counterexamples (`ce1`, `ce1b`, `ce2`, `ce3`), kernel-checked in Lean `v4.34.1` across all 426 local constants with zero `sorry`, zero `Classical.choice`, zero `Lean.ofReduceBool`, and zero `._unsafe_rec`.

## Applicability

### Covered Subjects and Their Relationships

This report characterizes five durable upstream subjects recorded in `REPORT.json` and their precise relationships:

| Subject | Immutable Identity | Role in This Report |
| :--- | :--- | :--- |
| `rust-lang/rust` HEAD | `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (`2026-11-22`) | Primary upstream compiler and `libcore` source audited across 11 compiler/library source files. |
| `rustc 1.102.0-nightly` + `Miri` | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`2026-11-11`) | Byte-for-byte identical to `342d74463` across all five core `async_drop` implementation files (`async_drop.rs`, `elaborate_drop.rs`, `coroutine/drop.rs`, `coroutine/mod.rs`, `async_destructor_ctor.rs`); cross-checked for `c1`–`c4` execution including `c3b` double-drop UAF. |
| `rustc 1.98.0-nightly` + `Miri` | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`2026-05-31`) | Live local execution host for all 11 probe cases (`support/probe_results_1_98_nightly.json`), full `-Z dump-mir=all` MIR inspection, and comparative version-diff analysis against `3ef0c22cd`/`342d74463`. |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`2026-11-19`) | Audited for fail-closed boundary coverage in `trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`, and `trusted/rustc-capture/src/driver.rs`. |
| `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Kernel type-checker verifying `support/AsyncDropCoroutineStateAndDoubleDropSoundness.lean` with `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`. |

### Shared vs. Version-Specific Behavior Across `1.98.0-nightly` and `1.102.0-nightly` / HEAD

Because `14210df0e` (`1.98.0-nightly`, `2026-05-31`) and `3ef0c22cd`/`342d74463` (`1.102.0-nightly`/HEAD, `2026-11-11`..`2026-11-22`) sit on opposite sides of `rustc`'s async-drop lowering refactor, behaviors partition strictly as follows:

- **Shared identically across `1.98.0-nightly`, `1.102.0-nightly`, and HEAD (`342d74463`):**
  - `library/core/src/future/async_drop.rs` (`58` lines, byte-identical across all three commits).
  - Companion sync `Drop` requirement (`AsyncDropWithoutSyncDrop`).
  - Reverse-order async drop on normal `async` exits, `Pin<&mut Self>` self-referential stability across `.await` under `Miri -Zmiri-tree-borrows`, and sync `Drop` fallback in sync scopes and unwind cleanup pads.
  - Missing `SetDiscriminant(CoroutineArgs::RETURNED)` on both `insert_clean_drop` (`UNRESUMED`) and `TerminatorKind::CoroutineDrop` (`create_coroutine_drop_shim_async`), producing identical `Miri` heap UAF double-drop UB on `c3a`, `c3d`, and `c3e`, accidental safety on `c3c`, and single-poll safety on `c3f`.
  - Hardcoded `produce_async_drops: false` in `elaborate_coroutine_drops` (`c3g` safe-Rust unresumed upvar sync-fallback).
  - Non-transitive shallow foreign-ADT check in `check_if_can_async_drop`, producing identical cross-crate splits (`bare=1000`, wrappers `=10`, `partial_tup=1000`) while emitting the contradicting `AsyncDropTypesInDependency` warning.
- **Version-specific differences between `1.98.0-nightly` (`14210df0e`) and `1.102.0-nightly` / HEAD (`3ef0c22cd` / `342d74463`):**
  - **MIR expansion site:** `1.98.0-nightly` leaves `TerminatorKind::Drop { async_fut: Some(fut), drop: Some(..) }` unexpanded in `elaborate_drop.rs` (`1,424` lines) and expands poll-yield loops during `StateTransform` in `coroutine/drop.rs:255-466` (`758` lines). `1.102.0-nightly` and HEAD expand poll-yield loops directly inside `elaborate_drop.rs:227-632` (`1,671` lines), delete `TerminatorKind::Drop::async_fut`, and shrink `coroutine/drop.rs` to `408` lines.
  - **`create_coroutine_drop_shim_proxy_async` (`has_async_drops = false`, case `c3b`):** In `1.98.0-nightly`, `coroutine/drop.rs:715-758` omits `make_coroutine_state_argument_pinned` (leaving `_1` by-value instead of `Pin<&mut Coro>`), causing `async_drop_in_place(&mut *slot).await` on an unresumed plain-`Box` coroutine to **leak** (`Miri` error: `memory leaked: alloc276`). In `1.102.0-nightly` and HEAD, `coroutine/drop.rs:394` adds `make_coroutine_state_argument_pinned(tcx, &mut body)` (plus `deref_finder` and `transform_async_context`), so the drop executes—and because `create_coroutine_drop_shim` still omits `SetDiscriminant(RETURNED)` on `UNRESUMED`, `c3b` now triggers immediate **dangling-pointer heap UAF double-drop** in `Miri` (`memory access failed: alloc... has been freed, so this pointer is dangling`).
  - **Poisoned-state handling under `-Zasync-panic=false`:** `1.102.0-nightly` / HEAD (`coroutine/drop.rs:290-294`, `coroutine/mod.rs:902-906`) gates `ResumedAfterPanic` / `ResumedAfterReturn` panics on `tcx.sess.opts.unstable_opts.async_panic` (returning `Poll::Pending` when disabled); `1.98.0-nightly` unconditionally emits `insert_panic_block`.

### Configuration, Target, and Model-Fidelity Scope

- **Invocation constraints:** Requires Rust Edition 2024 on nightly `rustc` with `#![feature(async_drop)]` (except downstream crate `main` in case `c4`, which intentionally omits the feature gate), running on `x86_64-unknown-linux-gnu` with `MIRIFLAGS="-Zmiri-tree-borrows"` for Miri runs.
- **Lean model-fidelity boundary:** `support/AsyncDropCoroutineStateAndDoubleDropSoundness.lean` is a standalone Lean `v4.34.1` operational model faithfully encoding the exact control-flow predicates and discriminant state transitions audited in `rust-lang/rust@342d74463`. It does **not** import `joshlf/anneal`'s `Trusted.MirAst` or `Trusted.MirSemantics` and proves no formal refinement/embedding relation between the Lean model and `rustc`'s Rust source code (`model-system relation: none proved`; connections to `rustc` are explicit `source + execution + derived` bridges).
- **Relation to peer corpus reports:** This report complements `rustc-statetransform-coroutines-async-gen-and-pin-mir-semantics` (which documents `StateTransform` layout packing, `!Unpin` Tree Borrows retag exemption, and sync `coroutine_drop` without `async_drop`) and `drop-flag-elaboration-partial-moves-and-unwind-cleanup-exactly-once-destruction` (which models synchronous drop flags and explicitly marks `async_drop` unmodeled).

## Findings

### 1. Core `AsyncDrop` Contract, Companion Sync `Drop` Mandate, and `staged_api` Guard

Basis: source + execution

`library/core/src/future/async_drop.rs:27-58` (identical across `14210df0e`, `3ef0c22cd`, and `342d74463`) defines the two unstable lang items governing asynchronous destruction:

```rust
#[unstable(feature = "async_drop", issue = "126482")]
#[lang = "async_drop"]
pub trait AsyncDrop {
    #[allow(async_fn_in_trait)]
    async fn drop(self: Pin<&mut Self>);
}

#[unstable(feature = "async_drop", issue = "126482")]
#[lang = "async_drop_in_place"]
pub async unsafe fn async_drop_in_place<T: ?Sized>(_to_drop: &mut T) {
    // Code here does not matter - this is replaced by the
    // real implementation by the compiler.
}
```

Three compile-time invariants govern these definitions:

1. **Mandatory Companion Sync `Drop` (`compiler/rustc_hir_analysis/src/check/mod.rs:125-135`):**
   ```rust
   fn adt_destructor(tcx: TyCtxt<'_>, def_id: LocalDefId) -> Option<ty::Destructor> {
       let dtor = tcx.calculate_dtor(def_id, always_applicable::check_drop_impl);
       if dtor.is_none() && tcx.features().async_drop() {
           if let Some(async_dtor) = adt_async_destructor(tcx, def_id) {
               let span = tcx.def_span(async_dtor.impl_did);
               tcx.dcx().emit_err(diagnostics::AsyncDropWithoutSyncDrop { span });
           }
       }
       dtor
   }
   ```
   Compiling a struct with `impl AsyncDrop for OnlyAsync` and no `impl Drop` fails with `rc = 1` on both `1.98.0-nightly` and `1.102.0-nightly`:
   ``error: `AsyncDrop` impl without `Drop` impl`` with help text ``type implementing `AsyncDrop` trait must also implement `Drop` trait to be used in sync context and unwinds`` (probe case `c1_async_drop_without_sync_drop`).
2. **Mutual Exclusion with `Copy`:** Documented in `async_drop.rs:21-26` and enforced alongside `Drop` coherence because `Copy` forbids any destructor.
3. **`staged_api` Anti-Insta-Stability ICE Guard (`check/mod.rs:137-142` and `elaborate_drop.rs:703-709`):** Both `adt_async_destructor` and `check_if_can_async_drop` execute `span_bug!("don't use async drop in libstd, it becomes insta-stable")` whenever `tcx.features().staged_api()` is active on a type requiring async drop. This prevents `core`/`alloc`/`std` types from accidentally leaking unstable async destructors into stable callers.
4. **Signature Shape of `async_drop_in_place`:** Unlike `core::ptr::drop_in_place<T: ?Sized>(to_drop: *mut T)`, `async_drop_in_place<T: ?Sized>(_to_drop: &mut T)` takes an exclusive mutable reference `&mut T` and is declared `pub async unsafe fn`, so its return type is an anonymous compiler-synthesized coroutine (`async_drop_in_place<T>::{closure#0}`) whose body is replaced by MIR shims during monomorphization.

### 2. MIR Drop Elaboration: Dual `Yield` Poll Loops, Reverse-Order Three-Track Ladders, and Unwind Sync Fallback

Basis: source + execution

In `rust-lang/rust` (`342d74463` and `3ef0c22cd`), `compiler/rustc_mir_transform/src/elaborate_drop.rs` lowers every MIR `Drop` terminator inside an `async` / `async gen` body into one of four `DropStyle` cases (`Dead`, `Static`, `Conditional`, `Open`, `L733-750`). At every leaf emission site, `rustc` enforces the exact cleanup guard:

| Emission Site in `elaborate_drop.rs` | Line | Async Guard Predicate | Fallback on Failure |
| :--- | :---: | :--- | :--- |
| `DropCtxt::build_drop` | `L636-637` | `!patch_ref().block(body, bb).is_cleanup && check_if_can_async_drop(drop_ty, false)` | Sync `TerminatorKind::Drop { drop: None }` |
| `DropCtxt::destructor_call_block` | `L1249` | `!unwind.is_cleanup() && check_if_can_async_drop(ty, true)` | Sync `destructor_call_block_sync` (`Drop::drop`) |
| `DropCtxt::drop_loop` (arrays/slices) | `L1311` | `!unwind.is_cleanup() && check_if_can_async_drop(ety, false)` | Sync `TerminatorKind::Drop { drop: None }` |
| `DropCtxt::drop_block` | `L1578` | `!unwind.is_cleanup() && check_if_can_async_drop(drop_ty, false)` | Sync `TerminatorKind::Drop { drop: None }` |

Notice `drop_ladder` (`L924-927`) further asserts `if unwind.is_cleanup() { dropline.is_none() } else { true }`: cleanup pads can never carry a `dropline` continuation and never construct an async drop poll loop.

#### 2.1 Dual Poll-Yield Loops Inside `build_async_drop` (`elaborate_drop.rs:227-632`)

When the guard succeeds, `build_async_drop` (`L227-406`) constructs a temporary `fut` of the return type of either `AsyncDrop::drop` (when `call_destructor_only = true`, taking `Pin::new_unchecked(&mut place)`) or `async_drop_in_place<T>` (when `call_destructor_only = false`, extracting `pin_obj_local.0: &mut T` at `L361`). Because a coroutine can itself be dropped while suspended mid-`AsyncDrop`, `build_async_drop` synthesizes **two** linked poll-yield loops via `build_pin_poll_yield_loop` (`L450-632`):

1. **Mainline loop (`succ_yield_loop`, `L332-347`, emitted when `dropline.is_some()`):**
   - Pins `fut` via `Pin::new_unchecked(&mut fut)` (`L605-629`), reads task context via `GetContext(CTX_ARG)` (`L574-600`), calls `Future::poll(pin_fut, cx)` (`L555-572`), and switches on `Poll` discriminant (`L512-550`):
     * `Poll::Ready(())` -> `succ_with_dead` (`StorageDead(fut); goto succ`).
     * `Poll::Pending` -> `yield_bb` executing `TerminatorKind::Yield { value: (), resume: resume_bb, resume_arg, drop: Some(dropline_bb) }` (`L500-509`).
   - `resume_bb` loops back to mainline `pin_bb` (`L341`), continuing normal execution.
   - `dropline_bb` jumps into the **dropline loop** (`drop_pin_bb`, `L342`) so cancellation continues polling the same in-progress `fut` rather than restarting or abandoning it.
2. **Dropline loop (`drop_pin_bb`, `L313-325`):**
   - Identical `Pin::new_unchecked` -> `Future::poll` -> `SwitchInt` -> `Yield` loop, **except** the `Yield` branches are inverted:
     * `drop` target loops back to `drop_pin_bb` (`L324`), advancing the async destructor across repeated `future_drop_poll` calls;
     * `resume` target jumps to `panic_bb` (`build_resumed_after_drop_abort_block`, `L408-432`), emitting `TerminatorKind::Assert { cond: false, expected: true, msg: ResumedAfterDrop(coroutine_kind) }`;
     * `Poll::Ready(())` jumps to `dropline_with_dead.unwrap_or(succ_with_dead)` (`L320`), continuing down the `dropline_ladder` to `TerminatorKind::CoroutineDrop`.

#### 2.2 Three-Track Reverse-Order Drop Ladder (`elaborate_drop.rs:838-955`)

For aggregates, tuples, and open-dropped locals, `drop_ladder` (`L917-955`) filters out `Dead` and `!needs_drop` fields (`should_retain_for_ladder`, `L867-877`) and invokes `drop_halfladder` (`L838-853`) **three times** over `fields.iter().rev()` (`L846`):

1. **`unwind_ladder` (`L935-940`):** Built with `Unwind::InCleanup` and `dropline = None`, forcing every field dropped after a panic to execute synchronous `Drop::drop` (with `UnwindAction::Terminate(InCleanup)` on double panic).
2. **`dropline_ladder` (`L941-946`):** Built with `unwind = unwind_ladder[i]` and `dropline = None` (already on the drop line), asynchronously dropping remaining fields on cancellation and falling back to `unwind_ladder` if an async destructor panics.
3. **`normal_ladder` (`L948`):** Built with `unwind = unwind_ladder[i]` and `dropline = dropline_ladder[i]`, executing reverse-order async drops on normal exit while wiring each step's panic edge to `unwind_ladder` and each step's `Yield.drop` edge to `dropline_ladder`.

#### 2.3 Empirical Confirmation of Order, Unwind Sync-Fallback, and `Pin<&mut Self>` Self-Referential Stability (`c2`)

Both native compilation (`rustc 1.98.0-nightly` and `1.102.0-nightly`) and `Miri` under Tree Borrows (`MIRIFLAGS="-Zmiri-tree-borrows"`, `rc = 0`) execute `c2_native_pin_order_and_unwind` / `c2_miri_tree_borrows` with identical trace:

```text
C2_LOG=["sync:sync_ctx:1", "async_pre:second:3", "async_post:second:103", "async_pre:first:2", "async_post:first:102", "sync:unwind_cleanup:4"]
```

Inside `Guard::AsyncDrop::drop`, each `PhantomPinned` guard initialized with a self-referential raw pointer `self.self_ptr = &raw const self.val` verifies:
- `(&raw const *self as usize)` before `YieldOnce(false).await` equals `(&raw const *self as usize)` after `.await`;
- `unsafe { *self.self_ptr } == self.val` and `self.self_ptr == &raw const self.val` both before and after `.await`; and
- mutating `this.val += 100` via `Pin::get_unchecked_mut` remains visible through `*self.self_ptr` without triggering Tree Borrows aliasing violations (`rc = 0`).

### 3. `StateTransform` Coroutine Lowering and `AsyncDropGlue` / `FutureDropPoll` Shim Synthesis

Basis: source + execution

#### 3.1 `StateTransform` Async-Drop Classification (`coroutine/mod.rs:1066-1252`, `coroutine/drop.rs:55-408`)

`StateTransform::run_pass` (`coroutine/mod.rs:1066-1252`) transforms every coroutine body (`body.yield_ty().is_some()`) as follows:

1. **Async-drop detection (`has_async_drops`, `coroutine/drop.rs:55-82`, called at `coroutine/mod.rs:1125`):** Performs a reverse-postorder dataflow traversal marking blocks reachable from any `TerminatorKind::Yield { drop: Some(v) }` (skipping `data.is_cleanup` blocks at `L61`). If any marked dropline block itself terminates in a `Yield`, `has_async_drops` is set to `true`.
2. **State remapping (`TransformVisitor`, `coroutine/mod.rs:479-538, 1163-1195`):**
   - Reserves `CoroutineArgs::UNRESUMED = 0`, `RETURNED = 1`, `POISONED = 2`, and assigns suspension points `3, 4, ...`.
   - Rewrites `TerminatorKind::Return` -> stores `Poll::Ready(val)` and emits **`SetDiscriminant(CoroutineArgs::RETURNED)`** (`L491-492`).
   - Rewrites `TerminatorKind::Yield` -> stores `Poll::Pending`, emits `StorageDead` for non-remapped locals, and emits **`SetDiscriminant(SuspendK)`** (`L530-531`).
   - **Crucial omission:** `visit_basic_block_data` hits `_ => {}` (`L534`) for `TerminatorKind::CoroutineDrop`—it emits **no** `SetDiscriminant`.
3. **Unresumed upvar drop synthesis (`coroutine/mod.rs:1216-1225`):**
   - Calls `drop_clean = insert_clean_drop(tcx, body, has_async_drops)` (`coroutine/drop.rs:148-174`), inserting a single block `TerminatorKind::Drop { place: SELF_ARG, target: return_block, drop: None }` where `return_block` is `insert_poll_ready_block` if `has_async_drops` else `TerminatorKind::Return`. **No `SetDiscriminant(CoroutineArgs::RETURNED)` is emitted on `drop_clean` or `return_block`.**
   - Calls `elaborate_coroutine_drops(tcx, body)` (`coroutine/drop.rs:85-145`) with `DropShimElaborator { produce_async_drops: false, .. }` (`L103`), expanding `drop(SELF_ARG)` via `open_drop` (`elaborate_drop.rs:1500`) into synchronous upvar drops.
4. **Coroutine drop-shim selection (`coroutine/mod.rs:1234-1248`):**
   - If `has_async_drops == true`: builds `body.coroutine.coroutine_drop_async` via `create_coroutine_drop_shim_async` (`coroutine/drop.rs:258-352`). Its entry `SwitchInt` dispatches `UNRESUMED (0)` -> `drop_clean` (`L281`), `POISONED (2)` -> panic/pending (`L285-297`), each `SuspendK` -> `point.drop` (`L279`), and `otherwise` (covering `RETURNED (1)`) -> `insert_poll_ready_block` (`L301`). Then `L304-310` rewrites every `TerminatorKind::CoroutineDrop` into `_0 = Poll::Ready(()); return;`—**again without emitting `SetDiscriminant(CoroutineArgs::RETURNED)`!**
   - If `has_async_drops == false`: builds sync `body.coroutine.coroutine_drop` via `create_coroutine_drop_shim` (`coroutine/drop.rs:177-254`, also omitting `SetDiscriminant(RETURNED)` on `UNRESUMED` at `L196` and on `CoroutineDrop` at `L206-208`) AND builds `body.coroutine.coroutine_drop_proxy_async` via `create_coroutine_drop_shim_proxy_async` (`coroutine/drop.rs:356-408`), whose entire body is `drop(_1) -> { _0 = Poll::Ready(()); return; }` (invoking sync `coroutine_drop` and returning `Poll::Ready(())`).
5. **Special `RETURNED` idempotence ONLY for `async_drop_in_place` resume bodies (`coroutine/mod.rs:911-933`):**
   ```rust
   // For `async_drop_in_place<T>::{closure}` we just keep return Poll::Ready,
   // because async drop of such coroutine keeps polling original coroutine
   if tcx.is_async_drop_in_place_coroutine(body.source.def_id()) {
       insert_poll_ready_block(tcx, body)
   }
   ```
   This special case applies **only** to `async_drop_in_place<T>::{closure#0}` bodies whose `Return` set `RETURNED`—not to ordinary user coroutines dropped through `future_drop_poll`.

#### 3.2 Monomorphization and `ShimKind` Dispatch (`instance.rs`, `shim.rs`, `async_destructor_ctor.rs`, `ty/sty.rs`)

Monomorphizing `async_drop_in_place<T>` and its returned coroutine triggers three distinct `ShimKind` variants:

1. **`ShimKind::AsyncDropGlueCtor(def_id, ty)`** (`compiler/rustc_ty_utils/src/instance.rs:67-88`, `shim.rs:172-176`, `async_destructor_ctor.rs:17-42`): Instantiates the generic constructor body of `core::future::async_drop_in_place<T>` returning the coroutine value `{async fn body of async_drop_in_place<T>()}` holding `_to_drop: &mut T` as field `.0`.
2. **`ShimKind::AsyncDropGlue(def_id, ty)`** (`instance.rs:89-91`, `shim.rs:149-170`, `async_destructor_ctor.rs:46-166`): Built for **non-coroutine** `drop_ty` (`assert!(!drop_ty.is_coroutine())` at `L76`). `build_async_drop_shim` runs `elaborate_drop` with `DropShimElaborator { produce_async_drops: true }` (`L138-144`), and `shim.rs:155-166` runs `StateTransform` on the resulting body to turn the elaborated drop ladder into an async state machine.
3. **`ShimKind::FutureDropPoll(def_id, proxy_ty, impl_ty)`** (`shim.rs:131-148`, `async_destructor_ctor.rs:176-433`): Invoked whenever `Future::poll` is called on a `proxy_ty = async_drop_in_place<...>::{closure#0}` wrapping a coroutine! Crucially, `Ty::find_async_drop_impl_coroutine` (`compiler/rustc_middle/src/ty/sty.rs:1558-1575`) recursively strips every outer `async_drop_in_place` coroutine layer:
   ```rust
   pub fn find_async_drop_impl_coroutine<F: FnMut(Ty<'tcx>)>(
       self,
       tcx: TyCtxt<'tcx>,
       mut f: F,
   ) -> Ty<'tcx> {
       assert!(self.is_coroutine());
       let mut cor_ty = self;
       let mut ty = cor_ty;
       loop {
           let ty::Coroutine(def_id, args) = ty.kind() else { return cor_ty };
           cor_ty = ty;
           f(ty);
           if !tcx.is_async_drop_in_place_coroutine(*def_id) {
               return cor_ty;
           }
           ty = args.first().unwrap().expect_ty();
       }
   }
   ```
   `build_future_drop_poll_shim` (`async_destructor_ctor.rs:189-193`) then branches on the unwrapped `impl_ty`:
   - If `impl_ty` is itself an `async_drop_in_place<NonCoro>::{closure#0}` coroutine (`is_async_drop_in_place_coroutine == true`), it calls **`build_adrop_for_adrop_shim`** (`L308-433`), which extracts the reference to `impl_ty` and calls `Future::poll(Pin::new_unchecked(&mut impl_ty), ctx)` (`L405-425`)—continuing `async_drop(T)::poll()`, which is `RETURNED`-idempotent via `coroutine/mod.rs:917-918`.
   - If `impl_ty` is an **ordinary coroutine `Coro`** (`is_async_drop_in_place_coroutine == false`), `find_async_drop_impl_coroutine` unwraps *all* surrounding `async_drop_in_place` layers straight down to `Coro`, and calls **`build_adrop_for_coroutine_shim`** (`L200-304`), which loads `tcx.optimized_mir(def_id).future_drop_poll().unwrap()` (`L226`), projects `_1.0` through every nested proxy pointer down to `&mut Coro` (`L252-277`), and executes **`Coro::future_drop_poll` directly on `Coro`**.

### 4. Root-Cause Dissection of the Live `Miri` Heap Use-After-Free Double-Drop Bug in `async_drop_in_place`

Basis: source + execution + derived

Consider the textbook manual async-drop pattern inside an `async` block:

```rust
let mut slot = ManuallyDrop::new(async move { /* ... */ });
unsafe { async_drop_in_place(&mut *slot).await; }
```

#### 4.1 Why `Coro::future_drop_poll` Executes Twice

Desugaring `.await;` inside an `async` block yields:

```rust
let mut __awaitee = async_drop_in_place::<Coro>(&mut *slot); // type Proxy1
loop {
    match Future::poll(Pin::new_unchecked(&mut __awaitee), cx) {
        Poll::Ready(()) => break,
        Poll::Pending => yield (),
    }
}
// End of statement inside `async` block -> elaborate_drop emits async drop of `__awaitee`!
// Proxy2 = async_drop_in_place::<Proxy1>(&mut __awaitee); poll Proxy2 until Ready.
```

1. **First invocation (during `.await`):** Polling `Proxy1` resolves `FutureDropPoll(_, Proxy1, Coro)` -> `build_adrop_for_coroutine_shim` -> calls **`Coro::future_drop_poll(&mut *slot)`** until `Poll::Ready(())`.
2. **Second invocation (dropping `__awaitee` at `;`):** Because the enclosing block is `async`, `elaborate_drop.rs:634-660` lowers the drop of `__awaitee: Proxy1` into `Proxy2 = async_drop_in_place::<Proxy1>(&mut __awaitee)` and polls `Proxy2` until `Poll::Ready(())`. Because `Proxy1` wraps `Coro`, `Proxy2.find_async_drop_impl_coroutine(tcx)` peels **both** `Proxy2` and `Proxy1` and lands on `impl_ty = Coro`! Thus `Proxy2::poll` resolves `FutureDropPoll(_, Proxy2, Coro)` (literally visible in Miri's stack frame: `dropshim({async fn body of async_drop_in_place<{async fn body of async_drop_in_place<{async block}>()}>()}-{async block})`) and calls **`Coro::future_drop_poll(&mut *slot)` a second time**!
3. **Isolation proof (`c3f_miri_sync_driver_unresumed_control`):** Driving the identical unresumed `async_drop_in_place(&mut *slot)` from a synchronous caller (`let drop_fut = unsafe { async_drop_in_place(&mut *slot) }; block_on(drop_fut);`) never constructs `Proxy2` when dropping `drop_fut` in sync `main`, so `Coro::future_drop_poll` executes only once and `Miri -Zmiri-tree-borrows` passes (`rc = 0`, stdout `SYNC_DROP 42`).

#### 4.2 Why the Second Poll Triggers Heap Use-After-Free Across Four Distinct Cases

Because `Proxy2` re-polls `Coro::future_drop_poll` unconditionally, soundness requires `Coro::future_drop_poll` to be **idempotent after returning `Poll::Ready(())`**. Direct MIR inspection (`-Z dump-mir=all`, `main.main-{closure#0}-{closure#0}.-------.coroutine_drop_async.0.mir`) and live `Miri` execution prove that `rustc` violates idempotence at **two distinct sites**, not one:

1. **Site 1 — `UNRESUMED` (`insert_clean_drop`, `coroutine/drop.rs:148-174`):**
   Look at the actual compiler-emitted MIR for `UNRESUMED (0)` in `coroutine_drop_async`:
   ```mir
   bb0: {
       _45 = discriminant((*_46));
       switchInt(move _45) -> [0: bb24, 2: bb32, 3: bb28, 4: bb29, 5: bb30, 6: bb31, otherwise: bb33];
   }
   bb24: { goto -> bb26; }
   bb26: { drop(((*_46).0: HeapAsyncGuard)) -> [return: bb25, unwind: bb5]; }
   bb25: { goto -> bb23; }
   bb23: { _0 = Poll::<()>::Ready(const ()); return; }
   ```
   `discriminant((*_46))` is **never updated** from `0 (UNRESUMED)` to `1 (RETURNED)`!
   - When `has_async_drops = true` (`c3a_miri_unresumed_with_async_drop`): Poll 1 drops `HeapAsyncGuard(Box::new(42))` (`SYNC_DROP 42`, deallocating the heap `Box<u32>`) and leaves `discriminant == 0`. Poll 2 re-enters `bb24 -> bb26` and dereferences the freed `Box<u32>` -> `Miri` UB (`rc = 1`: `constructing invalid value of type std::boxed::Box<u32>: encountered a dangling box (use-after-free)`).
   - When `has_async_drops = false` (`c3b_miri_unresumed_plain_box_coro`): `create_coroutine_drop_shim_proxy_async` (`coroutine/drop.rs:356-408`) calls sync `create_coroutine_drop_shim` (`L196`), which jumps to `drop_clean` and likewise never updates `discriminant` from `0` to `1`.
     * On `rustc 1.102.0-nightly` (`3ef0c22cd`): Poll 1 deallocates `Box<u32>` (`alloc917`); Poll 2 re-enters `UNRESUMED` and calls `<Box<u32> as Drop>::drop` a second time -> `Miri` UB (`rc = 1`: `memory access failed: alloc917 has been freed, so this pointer is dangling`).
     * On `rustc 1.98.0-nightly` (`14210df0e`): `create_coroutine_drop_shim_proxy_async` (`coroutine/drop.rs:715-758`) had not yet added `make_coroutine_state_argument_pinned` (MIR signature took `_1` by value instead of `Pin<&mut Coro>`), so `Miri` instead fails with `rc = 1` (`memory leaked: alloc276`).
2. **Site 2 — `TerminatorKind::CoroutineDrop` (`create_coroutine_drop_shim_async`, `coroutine/drop.rs:304-310`):**
   Look at `bb3` (the rewritten `TerminatorKind::CoroutineDrop`) in the exact same compiler-emitted MIR:
   ```mir
   bb3: {
       _0 = Poll::<()>::Ready(const ());
       return;
   }
   ```
   **`CoroutineDrop` also never emits `discriminant((*_46)) = 1;` (`RETURNED`)!** This causes two previously under-appreciated suspended-coroutine UB failures that directly refine the naive assumption that polling `slot` once to `Pending` makes `async_drop_in_place(&mut *slot).await` safe:
   - **Suspended + Immediately-Ready `AsyncDrop::drop` (`c3d_miri_suspended_immediate_async_drop`):** Poll `slot` once (`Poll::Pending`, `discriminant == 3 (Suspend0)`). Inside `Suspend0`'s drop path, `ImmediateAsyncGuard::AsyncDrop::drop` returns `Poll::Ready(())` on its **first** poll (zero internal `.await` points), so the outer coroutine never executes `bb19` (`discriminant = 6`), jumps straight to `bb3` (`CoroutineDrop`), and returns `Poll::Ready(())` with `discriminant` still **`3 (Suspend0)`**! Poll 2 (from dropping `__awaitee`) re-enters `3 (Suspend0)`, constructs a fresh `async_drop_in_place::<ImmediateAsyncGuard>`, and **double-drops `Box<u32>`** (`Miri` UB `rc = 1`: `encountered a dangling box (use-after-free)` at `<ImmediateAsyncGuard as AsyncDrop>::drop`)!
   - **Suspended + Unmoved `AsyncDrop` Upvar (`c3e_miri_suspended_unmoved_upvar_async_drop`):** Poll `slot` once (`Poll::Pending`, `discriminant == 3`) when `g: HeapAsyncGuard` was captured as an upvar and not moved into a local before `.await`. `Suspend0`'s drop path runs sync `Drop` on the upvar (`SYNC_DROP 66`), jumps straight to `CoroutineDrop` without updating `discriminant`, and Poll 2 re-enters `3` -> **dangling-box UAF in `Miri` (`rc = 1`)**!
3. **Why Suspended + Yielding `AsyncDrop::drop` (`c3c_miri_suspended_yielding_async_drop`) Passes Incidentally (`rc = 0`):**
   When `HeapAsyncGuard` is a local whose `AsyncDrop::drop` yields `Poll::Pending` once (`YieldOnce(false).await`):
   - Poll 1 of `slot::future_drop_poll` enters `3 (Suspend0)`, prints `ASYNC_PRE 99`, receives `Poll::Pending`, and executes `bb19`: `discriminant((*_46)) = 6;` (`DropYield`).
   - Poll 2 enters `6 (DropYield)`, polls the stored `async_drop_in_place::<HeapAsyncGuard>` sub-future (`((*_46) as variant#6).1`), which prints `ASYNC_POST 99`, reaches `TerminatorKind::Return`, sets **its own** discriminant to `1 (RETURNED)`, and returns `Poll::Ready(())` -> `bb3` returns `Poll::Ready(())` (leaving `slot`'s discriminant at **`6`**, NOT `1`!).
   - Poll 3 (from dropping `__awaitee` via `Proxy2`) re-enters `6 (DropYield)`, re-polls the stored `async_drop_in_place::<HeapAsyncGuard>` sub-future, which is now in state `1 (RETURNED)` and is **accidentally rescued** by `coroutine/mod.rs:917-918` (`is_async_drop_in_place_coroutine` returning `Poll::Ready(())` on `RETURNED`)!

#### 4.3 Summary Matrix of Empirical Execution Outcomes (`1.98.0-nightly` and `1.102.0-nightly`)

| Probe Case | Coroutine State & Resource | `1.98.0-nightly` (`14210df0e`) Miri (`-Zmiri-tree-borrows`) | `1.102.0-nightly` (`3ef0c22cd`) Miri (`-Zmiri-tree-borrows`) | Root Cause Mechanism |
| :--- | :--- | :--- | :--- | :--- |
| `c1` | `impl AsyncDrop` without `impl Drop` | Compile error (`rc = 1`): `` `AsyncDrop` impl without `Drop` impl `` | Compile error (`rc = 1`): identical | `check/mod.rs:125-135` (`adt_destructor`) |
| `c2` (native & Miri) | Sync ctx + pinned self-ref reverse async drop + unwind panic | PASS (`rc = 0`), `sync_ctx`, `second` (103), `first` (102), `unwind_cleanup` | PASS (`rc = 0`), identical log | `elaborate_drop.rs:636, 846, 917-955` |
| `c3a` | Unresumed, `has_async_drops = true`, `.await;` in `async` | **UB (`rc = 1`)**: `SYNC_DROP 42` + dangling `Box<u32>` UAF | **UB (`rc = 1`)**: `SYNC_DROP 42` + dangling `Box<u32>` UAF | `insert_clean_drop` omits `SetDiscriminant(RETURNED)` |
| `c3b` | Unresumed, plain `Box<u32>` (`has_async_drops = false`), `.await;` | **Leak (`rc = 1`)**: `memory leaked: alloc276` | **UB (`rc = 1`)**: `alloc917 has been freed` UAF in `Box::drop` | `1.98`: missing pin in proxy; `1.102`: fixed pin -> exposes missing `RETURNED` in `drop_clean` |
| `c3c` | Suspended (`Pending`), local yielding `AsyncDrop`, `.await;` | PASS (`rc = 0`): `ASYNC_PRE 99`, `ASYNC_POST 99` | PASS (`rc = 0`): `ASYNC_PRE 99`, `ASYNC_POST 99` | Yield sets `discr = DropYield`; inner `async_drop_in_place` is `RETURNED`-idempotent (`coroutine/mod.rs:917`) |
| `c3d` | Suspended (`Pending`), local **immediate** `AsyncDrop`, `.await;` | **UB (`rc = 1`)**: `ASYNC_IMMEDIATE 123` + dangling `Box<u32>` UAF | Not directly executed; source `coroutine/drop.rs:304-310` identical | `TerminatorKind::CoroutineDrop` omits `SetDiscriminant(RETURNED)` |
| `c3e` | Suspended (`Pending`), **unmoved upvar** `AsyncDrop`, `.await;` | **UB (`rc = 1`)**: `SYNC_DROP 66` + dangling `Box<u32>` UAF | Not directly executed; source `coroutine/drop.rs:103, 304-310` identical | Upvar sync fallback (`L103`) + `CoroutineDrop` omits `SetDiscriminant(RETURNED)` |
| `c3f` | Unresumed, `has_async_drops = true`, **sync `block_on`** driver | PASS (`rc = 0`): `SYNC_DROP 42` (once) | Not directly executed; source identical | No outer `async` block -> no `Proxy2` re-poll |
| `c3g` | **100% Safe Rust**, unresumed `async move` owning `AsyncDrop` upvar | PASS (`rc = 0`): `SYNC_DROP 55` (NOT async!) | PASS (`rc = 0`): `SYNC_DROP 55` (NOT async!) | `elaborate_coroutine_drops` hardcodes `produce_async_drops: false` (`L103`) |
| `c4` | Cross-crate (`dep` has feature, `main` omits feature) | PASS (`rc = 0`): warning + `bare=1000`, `wrappers=10`, `partial_tup=1000` | PASS (`rc = 0`): `bare=1000`, `opt=arr=tup=box=wrap=10` | `check_if_can_async_drop` shallow top-level ADT gate (`elaborate_drop.rs:679-688`) |

### 5. Safe-Rust Unresumed Upvar Sync-Fallback

Basis: source + execution

In `compiler/rustc_mir_transform/src/coroutine/drop.rs:85-104` (and identically at `L469-485` in `1.98.0-nightly`):

```rust
let mut elaborator = DropShimElaborator {
    body,
    patch: MirPatch::new(body),
    tcx,
    typing_env,
    // FIXME(async_drop): Drops, produced by insert_clean_drop + elaborate_coroutine_drops, are
    // currently sync only. To allow async for them, flip this flag and fix the related
    // problems.
    produce_async_drops: false,
};
```

Because `insert_clean_drop` (`L148-174`) runs *after* `has_async_drops` (`coroutine/mod.rs:1125`) and `TransformVisitor` (`L1176`), and `elaborate_coroutine_drops` sets `produce_async_drops: false`, **no unresumed coroutine ever runs `AsyncDrop::drop` on its captured upvars**, even when dropped inside an `async` block with `#![feature(async_drop)]` enabled! Case `c3g_miri_safe_unresumed_upvar_sync_fallback` confirms this in 100% safe Rust under `Miri -Zmiri-tree-borrows`: `let _unresumed = async move { YieldOnce(false).await; let _keep = g; };` exits cleanly (`rc = 0`) while printing `SYNC_DROP 55`—silently bypassing `HeapAsyncGuard::AsyncDrop::drop`.

Moreover, as `c3e` demonstrates, even if the coroutine *is* polled once and suspends before moving `g` out of the upvar capture field, dropping the unmoved upvar during cancellation also executes through `elaborate_coroutine_drops` (`produce_async_drops: false`), falling back to sync `Drop::drop` (`SYNC_DROP 66`).

### 6. Cross-Crate Feature-Gate Non-Transitivity Contradicting Compiler Warning and Partial-Move Flip

Basis: source + execution

When crate `main` (without `#![feature(async_drop)]`) links against crate `dep` (compiled with `#![feature(async_drop)]` and exporting `pub struct DepGuard` implementing `Drop` (+10) and `AsyncDrop` (+1000) plus `pub struct DepWrap(pub DepGuard)`), `CStore::report_incompatible_async_drop_feature` (`compiler/rustc_metadata/src/creader.rs:638-656`) emits `AsyncDropTypesInDependency` (`compiler/rustc_metadata/src/diagnostics.rs:589-603`):

```text
warning: found async drop types in dependency `dep`, but async_drop feature is disabled for `main`
  |
  = help: if async drop type will be dropped in a crate without `feature(async_drop)`, sync Drop will be used
```

However, `DropCtxt::check_if_can_async_drop` (`compiler/rustc_mir_transform/src/elaborate_drop.rs:679-701`; `L442-468` in `1.98.0-nightly`) implements a completely different, non-transitive rule:

```rust
let is_async_drop_feature_enabled = if self.tcx().features().async_drop() {
    true
} else {
    // Check if the type needing async drop comes from a dependency crate.
    if let ty::Adt(adt_def, _) = drop_ty.kind() {
        !adt_def.did().is_local() && adt_def.async_destructor(self.tcx()).is_some()
    } else {
        false
    }
};
if !is_async_drop_feature_enabled {
    return false;
}
let needs_async_drop = if call_destructor_only {
    drop_ty.is_async_drop(self.tcx(), self.elaborator.typing_env())
} else {
    drop_ty.needs_async_drop(self.tcx(), self.elaborator.typing_env())
};
```

Notice the exact structural bug: `Ty::needs_async_drop` (`compiler/rustc_ty_utils/src/needs_drop.rs:41-63`) **is** fully transitive across ADT fields, tuples, `Option`, arrays (`filter_array_elements_async`, `L81-92`), and `Box<T>` (`DropTysOptions::default().recurse_into_box_for_async_drop()`, `L55`). Yet `check_if_can_async_drop` short-circuits at `L693-695` based solely on whether the *outermost* `drop_ty` is a non-local `ty::Adt` with its *own* `async_destructor`!

This creates three observable anomalies verified live in case `c4_cross_crate_non_transitive_gate` (`CROSS_CRATE bare=1000 opt=10 arr=10 tup=10 box=10 wrap=10 dep_wrap=10 partial_tup=1000`):

| Drop Expression in Downstream Crate (`!feature(async_drop)`) | `DropStyle` at Scope Exit | Top-Level `drop_ty` Seen by `check_if_can_async_drop` | `!is_local() && async_destructor().is_some()` | Observed Destructor |
| :--- | :--- | :--- | :---: | :--- |
| `let _bare = DepGuard(&BARE);` | `Static` | `dep::DepGuard` (`Adt`, foreign, has `AsyncDrop`) | `true` | **`AsyncDrop` (`1000`)** (contradicts warning!) |
| `let _opt = Some(DepGuard(&OPT));` | `Static` | `core::option::Option<DepGuard>` (`Adt`, foreign, no own `AsyncDrop`) | `false` | Sync `Drop` (`10`) |
| `let _arr = [DepGuard(&ARR)];` | `Static` | `[DepGuard; 1]` (`Array`, not `Adt`) | `false` | Sync `Drop` (`10`) |
| `let _tup = (DepGuard(&TUP),);` | `Static` | `(DepGuard,)` (`Tuple`, not `Adt`) | `false` | Sync `Drop` (`10`) |
| `let _box = Box::new(DepGuard(&BOXED));` | `Static` | `alloc::boxed::Box<DepGuard>` (`Adt`, foreign, no own `AsyncDrop`) | `false` | Sync `Drop` (`10`) |
| `let _wrap = LocalWrap(DepGuard(&WRAP));` | `Static` | `main::LocalWrap` (`Adt`, local) | `false` | Sync `Drop` (`10`) |
| `let _dwrap = DepWrap(DepGuard(&DEP_WRAP));` | `Static` | `dep::DepWrap` (`Adt`, foreign, no own `AsyncDrop`) | `false` | Sync `Drop` (`10`) |
| `let ptup = (DepGuard(&P), String::from("...")); drop(ptup.1);` | **`Open`** | `open_drop_for_tuple` -> field `.0: dep::DepGuard` | **`true`** | **`AsyncDrop` (`1000`)** (partial-move flip!) |

The last row is particularly treacherous for program semantics and compiler verification: moving an unrelated sibling field `ptup.1: String` out of a tuple (or struct) switches drop elaboration from `DropStyle::Static` (whole-tuple sync drop) to `DropStyle::Open` (`open_drop_for_tuple` -> `drop_subpath` on `ptup.0: dep::DepGuard`), silently flipping which destructor implementation (`Drop::drop` vs. `AsyncDrop::drop`) executes on `ptup.0`!

### 7. Implications for Anneal's Trusted MIR Boundary (`joshlf/anneal@c131b320e`)

Basis: source + derived

Direct inspection of `joshlf/anneal` at commit `c131b320eeeb26ef692e5afd5ec8db49ee518613` confirms that Anneal currently **fails closed** against every construct examined in this report:

- **Coroutines rejected at type level (`trusted/lean/Trusted/MirAst.lean:286, 308-321`):** `MirTy.unsupported` absorbs `TyKind::Coroutine`, `TyKind::CoroutineClosure`, `TyKind::CoroutineWitness`, and all non-fieldless-enum `Adt`s, causing `Trusted.MirSemantics` to fail closed with `FaultKind.unsupported`.
- **Drop, Yield, and CoroutineDrop rejected at terminator level (`trusted/lean/Trusted/MirAst.lean:742-795`):** `TerminatorKind.unsupported` absorbs `Drop`, `Yield`, `CoroutineDrop`, `UnwindTerminate`, and indirect `Call`. `evalTerminator` (`trusted/lean/Trusted/MirSemantics.lean:1537-1569`) returns `.fault .unsupported` on `.unsupported`, `.unwindResume`, `.assert`, `.call`, and any `.return_` inside a `cleanup = true` basic block (`if bb.cleanup then .fault .unsupported`, `L1543-1544`).
- **Compiler pin (`trusted/rustc-capture/src/driver.rs:25`):** `anneal-rustc-capture` currently pins `1.98.0-nightly (f8a08b688 2026-05-30)` (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`), which sits on the pre-refactor side of the `1.98 -> 1.102` async-drop transition.

Before any verified `rustc` MIR semantics or Anneal extension admits `#![feature(async_drop)]`, four invariants must be enforced at the capture/verification boundary:

1. **Require Post-`StateTransform` `Runtime(PostCleanup)` MIR + All Synthesized Shims:** Capture must include `AsyncDropGlueCtor`, `AsyncDropGlue`, `FutureDropPoll`, `coroutine_drop`, `coroutine_drop_async`, and `coroutine_drop_proxy_async` bodies as first-class monomorphized `Program.bodies` entries (not opaque external calls).
2. **Enforce `future_drop_poll` Terminal Discriminant Transition (`RETURNED`) or Reject `async_drop_in_place` on Coroutines:** Until upstream `rustc` emits `SetDiscriminant(CoroutineArgs::RETURNED)` on both `insert_clean_drop` (`UNRESUMED`) and `TerminatorKind::CoroutineDrop` (`create_coroutine_drop_shim_async` / `create_coroutine_drop_shim`), a sound verifier **must** accurately flag `async_drop_in_place(&mut *coro).await` inside an `async` block as UB (not assume idempotence).
3. **Model `BasicBlock.cleanup` Sync-Drop Constraint Explicitly:** Every unwind landing pad (`cleanup = true`) must enforce synchronous `Drop::drop` semantics with `UnwindAction::Terminate(InCleanup)` on nested panics and forbid `Yield` / `AsyncDrop` suspension.
4. **Enforce Feature-Gate Consistency Across Crate Boundaries:** Capture metadata must record whether `async_drop` was enabled per crate (or reject mixed-feature dependency graphs) so MIR verification never assumes wrapper compositionality when `rustc`'s non-transitive `check_if_can_async_drop` is active.

### 8. Mechanized Lean `v4.34.1` Formalization (`support/AsyncDropCoroutineStateAndDoubleDropSoundness.lean`)

Basis: source + execution (Lean `v4.34.1` kernel check)

[`support/AsyncDropCoroutineStateAndDoubleDropSoundness.lean`](support/AsyncDropCoroutineStateAndDoubleDropSoundness.lean) formalizes the state machine, three-track drop ladder, cross-crate feature gate, and counterexamples in pure constructive Lean `v4.34.1` (`426` local environment constants audited: `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, `0` `deriving`, `0` `._unsafe_rec`, `0` warnings under `-DwarningAsError=true`).

#### 8.1 Core Definitions (Verbatim Excerpts)

```lean
inductive CoroDiscr where
  | unresumed | returned | poisoned | suspend0 | dropYield

structure LoweringPolicy where
  marksReturnedOnUnresumed : Bool
  marksReturnedOnCoroutineDrop : Bool
  unresumedUpvarsUseAsyncDrop : Bool

noncomputable def rustcHeadPolicy : LoweringPolicy :=
  { marksReturnedOnUnresumed := false
    marksReturnedOnCoroutineDrop := false
    unresumedUpvarsUseAsyncDrop := false }

noncomputable def IdempotentDropRun (pol : LoweringPolicy) (st0 : CoroFrame) : Prop :=
  let stFinal := runAsyncDropInPlaceAwait pol st0
  hasDoubleDropUb stFinal.log = false ∧
  countCompletedDrops st0.resourceId stFinal.log = 1 ∧
  evalFutureDropPoll pol stFinal = (.ready, stFinal)
```

```lean
inductive DropTy where
  | prim
  | adt (isLocal : Bool) (hasOwnAsyncDrop : Bool) (field : DropTy)
  | pair (fst snd : DropTy)
  | option (inner : DropTy)
  | array (inner : DropTy)
  | tuple1 (inner : DropTy)
  | boxed (inner : DropTy)

noncomputable def rustcShallowGate (featureEnabled : Bool) (ty : DropTy) : Bool :=
  let gate :=
    if featureEnabled then true
    else match ty with | .adt false true _ => true | _ => false
  gate && needsAsyncDrop ty

noncomputable def transitiveGate (featureEnabled : Bool) (ty : DropTy) : Bool :=
  let gate := if featureEnabled then true else containsForeignAsyncDrop ty
  gate && needsAsyncDrop ty
```

#### 8.2 Verified Theorem Catalog and Exact Axiom Audit

Every theorem below was verified by `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`Lean 4.34.1`, `5045d0056413266e57c625dcd7c365b10e377c52`) and audited with `#print axioms`:

| Theorem Name | Formal Statement Summary | Exact Axiom Dependencies |
| :--- | :--- | :--- |
| `futureDropPoll_idempotent_iff_marks_returned` | For an unresumed coroutine holding an owned heap upvar (both `upvarAsyncCoro` and `upvarPlainProxy`), `IdempotentDropRun pol (mkUnresumed mode id) ↔ pol.marksReturnedOnUnresumed = true`. | `[propext]` |
| `futureDropPoll_suspended_immediate_idempotent_iff_coroDrop_marks_returned` | For a suspended coroutine (`Suspend0`) with an immediately-ready `AsyncDrop::drop` local or an unmoved upvar, `IdempotentDropRun pol (mkSuspended mode id) ↔ pol.marksReturnedOnCoroutineDrop = true`. | `[propext]` |
| `futureDropPoll_suspended_yielding_accidentally_safe` | Under `rustcHeadPolicy`, a suspended coroutine with a yielding `AsyncDrop::drop` local satisfies `IdempotentDropRun` while ending in `discr = .dropYield` (masking the missing outer `RETURNED` transition via inner `async_drop_in_place` idempotence). | `[propext]` |
| `sync_driver_avoids_double_poll_even_on_unresumed` | Under `rustcHeadPolicy`, driving `async_drop_in_place` synchronously on an unresumed coroutine yields zero UB and 1 drop while leaving `discr = .unresumed`. | `[propext]` |
| `async_drop_ladder_exact_once_per_init_field` | For any `fields : List FieldSpec` with `noDupIds (fields.map FieldSpec.id)` and any `sc : LadderScenario` (`normal`, `cancelAt k`, `panicAt k`, `unwindEntry`), drops occur in exact reverse initialized order, every initialized field is dropped exactly once, every uninitialized field is dropped zero times, and every cleanup drop is strictly synchronous. | `[propext, Quot.sound]` |
| `unwind_cleanup_never_async_drops` | Entering the ladder with `LadderScenario.unwindEntry` produces zero `.async` drop events across any field list. | `[propext]` |
| `transitive_gate_restores_wrapper_compositionality` | For every `featureEnabled : Bool` and `t : DropTy`, `transitiveGate` returns the identical Boolean for `t`, `Option<t>`, `[t; 1]`, `(t,)`, `Box<t>`, `LocalWrap(t)`, `DepWrap(t)`, and `(t, prim)` (eliminating both wrapper split and partial-move flip). | *(none — `[]`)* |
| `strict_warning_policy_agrees_with_diagnostic` | `strictWarningGate false t = false` for all `t : DropTy`, matching `rustc_metadata/src/diagnostics.rs:595`. | *(none — `[]`)* |
| `all_three_gates_agree_when_feature_enabled` | When `featureEnabled = true`, `rustcShallowGate`, `transitiveGate`, and `strictWarningGate` agree extensionally on all `DropTy`. | `[propext]` |
| `ce1_unresumed_missing_returned_transition_causes_double_drop_ub` | Constructive witness: under `rustcHeadPolicy`, both `upvarAsyncCoro` (id 42) and `upvarPlainProxy` (id 77) emit `[.syncDrop id, .ubDoubleDrop id]`. | `[propext]` |
| `ce1b_suspended_immediate_missing_returned_causes_double_drop_ub` | Constructive witness: under `rustcHeadPolicy`, suspended `localImmediateAsync` (id 123) and suspended `upvarAsyncCoro` (id 66) emit `.ubDoubleDrop`. | `[propext]` |
| `ce2_non_transitive_gate_splits_bare_vs_option` | Constructive witness: `rustcShallowGate false depGuard = true`, whereas `option`, `array`, `tuple1`, `boxed`, `LocalWrap`, `DepWrap`, and `(depGuard, prim)` all evaluate to `false`. | `[propext]` |
| `ce3_unresumed_upvar_sync_drop_vs_suspended_async_drop` | Constructive witness: under `rustcHeadPolicy`, unresumed upvar drop emits `[.syncDrop 55]` while suspended local drop emits `[.asyncDropStart 55, .asyncDropFinish 55]`. | *(none — `[]`)* |

## Boundaries

- **`not examined` — `async gen` (`CoroutineDesugaring::AsyncGen`) and `gen` blocks under `async_drop`:** While `elaborate_drop.rs:285-296` and `coroutine/drop.rs:30-46` show `AsyncGenPending` / `FixReturnPendingVisitor` support for `async gen` blocks, no empirical `rustc` or `Miri` probe was run on `async gen` coroutines.
- **`not examined` — Trait-object (`dyn Future` / `dyn AsyncDrop`) vtable async-drop dispatch and custom `Box<T, A>` allocators:** `elaborate_drop.rs:1503` handles `ty::Dynamic(..)` via `complete_drop`, and `needs_drop.rs:55` recurses into `Box`, but dynamic vtable async-drop slot layout, `dyn AsyncDrop` codegen, and non-`Global` `Box` allocators were not empirically probed.
- **`not examined` — Direct local execution of cases `c3d`, `c3e`, `c3f`, and `c4` `dep_wrap`/`partial_tup` on `rustc 1.102.0-nightly` (`3ef0c22cd`):** All 11 cases were executed live on `rustc 1.98.0-nightly` (`14210df0e`), and the original 8 cases (`c1`, `c2` native/Miri, `c3a`, `c3b`, `c3c`, `c3g`, `c4` bare/opt/arr/tup/box/wrap) were also executed on `rustc 1.102.0-nightly` (`3ef0c22cd`). Extension of `c3d`, `c3e`, `c3f`, and `c4` `dep_wrap`/`partial_tup` to `1.102.0-nightly` and HEAD (`342d74463`) is `derived` from line-by-line verification that `coroutine/drop.rs:103, 148-174, 304-310`, `elaborate_drop.rs:679-701, 958-972`, and `async_destructor_ctor.rs:176-304` contain the exact same predicates and missing `SetDiscriminant(RETURNED)` emissions in `3ef0c22cd` and `342d74463`; re-running [`support/probe_async_drop_and_double_drop_ub.py`](support/probe_async_drop_and_double_drop_ub.py) on `1.102.0-nightly` or newer is trivial and recommended before claiming direct execution on those subcases.
- **`not examined` — Multi-field drop-ladder interaction with `catch_unwind` across nested `async` frames and `-Zasync-panic=false`:** `c2` tests `catch_unwind` around `block_on` with default `async_panic` enabled; `-Zasync-panic=false` (`coroutine/drop.rs:290-294`, which returns `Poll::Pending` forever on `POISONED` instead of panicking) was inspected in source only, not executed.
- **`not examined` — `Stacked Borrows` (`-Zmiri-stacked-borrows`) vs. `Tree Borrows` (`-Zmiri-tree-borrows`) on `AsyncDrop::drop`:** All Miri runs in this report used `-Zmiri-tree-borrows`. Behavior of `c2`'s self-referential `Pin<&mut Self>` dereferences inside `AsyncDrop::drop` under legacy Stacked Borrows was not tested.
- **`known not to apply` — Claim that polling `slot` once to `Pending` suffices for `async_drop_in_place(&mut *slot).await` safety:** Falsified by `c3d` (`ImmediateAsyncGuard`, `rc = 1` UAF) and `c3e` (suspended unmoved upvar, `rc = 1` UAF) and formalized in `futureDropPoll_suspended_immediate_idempotent_iff_coroDrop_marks_returned`. Passing `c3c` relies specifically on the inner `AsyncDrop::drop` yielding `Pending` at least once so `slot` enters `DropYield`.
- **`known not to apply` — Formal equivalence between the Lean `v4.34.1` model and `rustc` or `joshlf/anneal`:** `AsyncDropCoroutineStateAndDoubleDropSoundness.lean` is a standalone formalization of the extracted state machine, drop-ladder, and type-gating semantics. It proves no refinement theorem connecting it to `rustc` Rust source or `Trusted.MirSemantics`.
- **`unsupported` — Stable Rust and Anneal `Trusted.MirAst` (`joshlf/anneal@c131b320e`):** `#![feature(async_drop)]` is an incomplete nightly-only language feature (`#126482`) and is explicitly unsupported (fail-closed `.unsupported`) in `joshlf/anneal`'s `Trusted.MirAst` and `Trusted.MirSemantics`.
- **`unknown` — Upstream stabilization timeline and final semantics for cross-crate `async_drop`:** Upstream `rustc` has not settled whether crates without `#![feature(async_drop)]` should strictly force sync `Drop` (matching the existing `AsyncDropTypesInDependency` warning) or transitively invoke `AsyncDrop` across wrappers (matching `transitiveGate`), nor whether `async_drop` will retain the current `async_drop_in_place(&mut T)` design versus an alternative `AsyncDrop::poll_drop` API.

## Evidence

### 1. Audited Primary Upstream Sources

All upstream commits were resolved directly via GitHub API on `2026-11-22`:

- **`rust-lang/rust` HEAD (`342d74463af7dd3018ef6aa04dd5500c2deb5bd1`, `2026-11-22`) and `rustc 1.102.0-nightly` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `2026-11-11` — byte-identical across the five primary async-drop files):**
  - `library/core/src/future/async_drop.rs:1-58` (`AsyncDrop` trait at `L27-41`, `async_drop_in_place` at `L53-58`).
  - `compiler/rustc_hir_analysis/src/check/mod.rs:125-142` (`adt_destructor`, `AsyncDropWithoutSyncDrop`, `adt_async_destructor`, `staged_api` guard).
  - `compiler/rustc_mir_transform/src/elaborate_drop.rs:51-64, 99, 227-712, 733-750, 838-972, 1013-1052, 1242-1330, 1436-1592` (`build_async_drop`, `build_pin_poll_yield_loop`, `build_drop`, `check_if_can_async_drop`, `drop_halfladder`, `drop_ladder`, `open_drop_for_tuple`, `destructor_call_block`, `drop_loop`, `drop_block`).
  - `compiler/rustc_mir_transform/src/elaborate_drops.rs:160-162` (`ElaborateDrops::allow_async_drops -> true`).
  - `compiler/rustc_mir_transform/src/coroutine/drop.rs:1-408` (`FixReturnPendingVisitor`, `has_async_drops` at `L55-82`, `elaborate_coroutine_drops` `produce_async_drops: false` at `L85-145`, `insert_clean_drop` at `L148-174`, `create_coroutine_drop_shim` at `L177-254`, `create_coroutine_drop_shim_async` at `L258-352`, `create_coroutine_drop_shim_proxy_async` at `L356-408`).
  - `compiler/rustc_mir_transform/src/coroutine/mod.rs:357-366, 479-538, 877-986, 990-1062, 1066-1252` (`TransformVisitor`, `is_async_drop_in_place_coroutine` `RETURNED` idempotence at `L915-919`, `StateTransform::run_pass` at `L1066-1252`).
  - `compiler/rustc_mir_transform/src/shim.rs:131-177, 346-360` (`make_shim` for `FutureDropPoll`, `AsyncDropGlue`, `AsyncDropGlueCtor`).
  - `compiler/rustc_mir_transform/src/shim/async_destructor_ctor.rs:17-433` (`build_async_destructor_ctor_shim`, `build_async_drop_shim`, `build_future_drop_poll_shim`, `build_adrop_for_coroutine_shim`, `build_adrop_for_adrop_shim`).
  - `compiler/rustc_middle/src/ty/sty.rs:1558-1575` (`Ty::find_async_drop_impl_coroutine`).
  - `compiler/rustc_ty_utils/src/instance.rs:67-91` (`AsyncDropGlueCtor` and `AsyncDropGlue` instance selection).
  - `compiler/rustc_ty_utils/src/needs_drop.rs:41-92, 337-356` (`needs_async_drop_raw`, `recurse_into_box_for_async_drop`, `filter_array_elements_async`).
  - `compiler/rustc_metadata/src/creader.rs:638-656` and `compiler/rustc_metadata/src/diagnostics.rs:589-603` (`report_incompatible_async_drop_feature`, `AsyncDropTypesInDependency`).
- **`rust-lang/rust` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `rustc 1.98.0-nightly`, `2026-05-31`):**
  - `library/core/src/future/async_drop.rs:1-58` (identical to HEAD).
  - `compiler/rustc_mir_transform/src/elaborate_drop.rs:200-480` (deferred `TerminatorKind::Drop { async_fut: Some(..) }` lowering; identical shallow `check_if_can_async_drop` at `L442-479`).
  - `compiler/rustc_mir_transform/src/coroutine/drop.rs:255-466, 469-758` (`expand_async_drops`, `produce_async_drops: false` at `L484`, `insert_clean_drop` at `L528-557`, `create_coroutine_drop_shim_proxy_async` at `L715-758` missing `make_coroutine_state_argument_pinned`).
- **`joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`, `2026-11-19`):**
  - `trusted/lean/Trusted/MirAst.lean:75-91, 286, 308-321, 742-814` (`MirTy.unsupported`, `TerminatorKind.unsupported`, `BasicBlock.cleanup`, `noncomputable` convention).
  - `trusted/lean/Trusted/MirSemantics.lean:1537-1569` (`evalTerminator` fail-closed clauses).
  - `trusted/rustc-capture/src/driver.rs:25` (pinned `1.98.0-nightly (f8a08b688 2026-05-30)` driver string).

### 2. Empirical Execution Records and Preserved Support Artifacts

All preserved support files live inside this report package under `support/`:

- **[`support/probe_async_drop_and_double_drop_ub.py`](support/probe_async_drop_and_double_drop_ub.py):** Standalone Python 3.10+ (stdlib-only) reproducible harness compiling and running all 11 `rustc` and `Miri` (`-Zmiri-tree-borrows`) probe cases in isolated `TemporaryDirectory` sandboxes and emitting structured JSON results.
- **[`support/probe_results_1_98_nightly.json`](support/probe_results_1_98_nightly.json):** Complete captured JSON output from executing `python3 support/probe_async_drop_and_double_drop_ub.py` on `2026-11-22` with `rustc 1.98.0-nightly (14210df0e 2026-05-31)` and `miri 0.1.0 (14210df0e2 2026-05-31)` on `x86_64-unknown-linux-gnu` (`11 / 11` cases executed; `$HOME` sanitized):
  - `c1_async_drop_without_sync_drop`: `compile_rc = 1`, ``error: `AsyncDrop` impl without `Drop` impl``.
  - `c2_native_pin_order_and_unwind`: `compile_rc = 0`, `run_rc = 0`, `C2_LOG=["sync:sync_ctx:1", "async_pre:second:3", "async_post:second:103", "async_pre:first:2", "async_post:first:102", "sync:unwind_cleanup:4"]`.
  - `c2_miri_tree_borrows`: `miri_rc = 0`, identical `C2_LOG` with verified `Pin<&mut Self>` address invariance and self-referential pointer reads across `.await`.
  - `c3a_miri_unresumed_with_async_drop`: `miri_rc = 1`, `stdout = "SYNC_DROP 42"`, `Undefined Behavior: constructing invalid value of type std::boxed::Box<u32>: encountered a dangling box (use-after-free)` in `<HeapAsyncGuard as Drop>::drop` invoked from `dropshim({async fn body of async_drop_in_place<{async fn body of async_drop_in_place<{async block}>()}>()}-{async block})`.
  - `c3b_miri_unresumed_plain_box_coro`: `miri_rc = 1`, `error: memory leaked: alloc276` on `1.98.0-nightly` (contrasted with `miri_rc = 1`, `Undefined Behavior: memory access failed: alloc917 has been freed, so this pointer is dangling` in `<Box<u32> as Drop>::drop` observed on `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)`).
  - `c3c_miri_suspended_yielding_async_drop`: `miri_rc = 0`, `stdout = "ASYNC_PRE 99\nASYNC_POST 99"`.
  - `c3d_miri_suspended_immediate_async_drop`: `miri_rc = 1`, `stdout = "ASYNC_IMMEDIATE 123"`, `Undefined Behavior: constructing invalid value of type std::boxed::Box<u32>: encountered a dangling box (use-after-free)` in `<ImmediateAsyncGuard as AsyncDrop>::drop::{closure#0}`.
  - `c3e_miri_suspended_unmoved_upvar_async_drop`: `miri_rc = 1`, `stdout = "SYNC_DROP 66"`, `Undefined Behavior: constructing invalid value of type std::boxed::Box<u32>: encountered a dangling box (use-after-free)` in `<HeapAsyncGuard as Drop>::drop`.
  - `c3f_miri_sync_driver_unresumed_control`: `miri_rc = 0`, `stdout = "SYNC_DROP 42"`.
  - `c3g_miri_safe_unresumed_upvar_sync_fallback`: `miri_rc = 0`, `stdout = "SYNC_DROP 55"`.
  - `c4_cross_crate_non_transitive_gate`: `dep_compile_rc = 0`, `main_compile_rc = 0` with `AsyncDropTypesInDependency` warning, `run_rc = 0`, `CROSS_CRATE bare=1000 opt=10 arr=10 tup=10 box=10 wrap=10 dep_wrap=10 partial_tup=1000`.
- **MIR dump evidence (`rustc --edition 2024 -Z dump-mir=all`, `1.98.0-nightly` `14210df0e`):**
  - `coroutine_drop_async.0.mir` confirmed `bb0` `switchInt(move _45) -> [0: bb24, 2: bb32, 3: bb28, 4: bb29, 5: bb30, 6: bb31, otherwise: bb33]`, zero `discriminant(...) = 1` on both `UNRESUMED` (`bb24 -> bb26 -> bb25 -> bb23`) and `CoroutineDrop` (`bb3`), and `discriminant((*_46)) = 6` only inside the yielding `Pending` path (`bb19`).
  - `coroutine_drop_proxy_async.0.mir` confirmed by-value `_1: {async block}` in `1.98.0-nightly` (explaining `c3b`'s leak vs. `1.102.0-nightly`'s `make_coroutine_state_argument_pinned` UAF).
- **[`support/AsyncDropCoroutineStateAndDoubleDropSoundness.lean`](support/AsyncDropCoroutineStateAndDoubleDropSoundness.lean):** Kernel-checked on `2026-11-22` with Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) using:
  ```console
  lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
    support/AsyncDropCoroutineStateAndDoubleDropSoundness.lean
  ```
  Exit code `0`, `0` warnings, `426` local environment constants inspected with `0` `._unsafe_rec`, `0` `partial`/`unsafe` definitions, `0` local axioms, and `#print axioms` confirming only `[]`, `[propext]`, or `[propext, Quot.sound]` across all 13 theorems.

## Revalidation

### 1. Re-Running the Full 11-Case `rustc` + `Miri` Empirical Probe

Against any newer nightly `rustc` + `miri` toolchain (e.g., `1.102.0-nightly` or later), run from this package directory:

```console
python3 support/probe_async_drop_and_double_drop_ub.py --out /tmp/async_drop_reval.json
```

Discriminating indicators to check in `/tmp/async_drop_reval.json`:
- **Has the `UNRESUMED` double-drop bug been fixed?** Check `c3a_miri_unresumed_with_async_drop.miri_rc` and `c3b_miri_unresumed_plain_box_coro.miri_rc`. If both flip from `1` (dangling-box UAF) to `0` while printing at most one drop, inspect `compiler/rustc_mir_transform/src/coroutine/drop.rs` (`insert_clean_drop` and `create_coroutine_drop_shim`) for newly added `SetDiscriminant(CoroutineArgs::RETURNED)`.
- **Has the `TerminatorKind::CoroutineDrop` double-drop bug been fixed?** Check `c3d_miri_suspended_immediate_async_drop.miri_rc` and `c3e_miri_suspended_unmoved_upvar_async_drop.miri_rc`. Both remain `1` until `create_coroutine_drop_shim_async` (`coroutine/drop.rs:304-310`) also emits `SetDiscriminant(CoroutineArgs::RETURNED)`.
- **Has unresumed upvar async-drop landed?** Check `c3g_miri_safe_unresumed_upvar_sync_fallback.stdout`: a flip from `SYNC_DROP 55` to `ASYNC_PRE 55\nASYNC_POST 55` indicates `produce_async_drops` in `elaborate_coroutine_drops` (`coroutine/drop.rs:103`) was flipped to `true` and moved ahead of `has_async_drops`.
- **Has cross-crate feature gating become coherent?** Check `c4_cross_crate_non_transitive_gate.stdout`:
  - All `10` (`bare=10 ... partial_tup=10`) indicates `check_if_can_async_drop` was aligned with the `AsyncDropTypesInDependency` warning (`strictWarningGate`).
  - All `1000` (`bare=1000 ... partial_tup=1000`) indicates `check_if_can_async_drop` was made transitive (`transitiveGate`).
  - Mixed `1000` and `10` (especially `tup=10` vs. `partial_tup=1000`) confirms the non-transitive bug persists.

### 2. Re-Checking Upstream `rust-lang/rust` Implementation Diffs

The cheapest static check against a new `rust-lang/rust` commit `<NEW_SHA>` is diffing the six load-bearing files against `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`:

```console
git diff 342d74463af7dd3018ef6aa04dd5500c2deb5bd1 <NEW_SHA> -- \
  library/core/src/future/async_drop.rs \
  compiler/rustc_mir_transform/src/elaborate_drop.rs \
  compiler/rustc_mir_transform/src/coroutine/drop.rs \
  compiler/rustc_mir_transform/src/coroutine/mod.rs \
  compiler/rustc_mir_transform/src/shim/async_destructor_ctor.rs \
  compiler/rustc_middle/src/ty/sty.rs
```

If that diff is empty, all source-derived findings in Sections 1–6 remain exact without re-reading the compiler.

### 3. Re-Verifying the Lean `v4.34.1` Formalization

From this package directory, verify kernel soundness and warning cleanliness:

```console
lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
  support/AsyncDropCoroutineStateAndDoubleDropSoundness.lean
```

Exit code `0` re-establishes all 13 theorems. To re-check zero `Classical.choice`, `sorryAx`, `Lean.ofReduceBool`, and `._unsafe_rec`, append `#print axioms` commands for the 13 theorems in a temporary scratch copy outside the package and verify no disallowed axioms appear.
