# Edition 2024 `gen` & `async gen` Coroutines: Unpinned Movability (`E0626`), `BitMatrix` `storage_conflicts` Slot Aliasing (`#73137`), and the Live Post-Panic `gen` Fusing Bug

## Summary

Rust's Edition 2024 generator constructs (`gen {}` and `async gen {}` under `#![feature(gen_blocks, async_for_loop, async_iterator)]`) sit on opposite sides of `rustc`'s coroutine movability, ABI, pinning, and aliasing boundaries while sharing `StateTransform`'s `BitMatrix` slot-packing layout and its post-panic resumption machinery. Primary-source inspection across four pinned `rust-lang/rust` revisions (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `49d734536222bf28bb6d07d885b3a81d145981da`, `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, and `342d74463af7dd3018ef6aa04dd5500c2deb5bd1`), live `rustc` + `Miri` (Stacked Borrows and Tree Borrows) execution, an audit of `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, and a constructive `Lean v4.34.1` mechanization establish six core results:

1. **Unique Unpinned ABI & Unconditional `Unpin` for `gen` vs. Pinned `!Unpin` for `async gen` (`hir.rs`, `abi.rs`, `coroutine/mod.rs`, trait solvers):** Among all four `rustc` coroutine kinds (`Coroutine`, `Async`, `Gen`, `AsyncGen`), `CoroutineDesugaring::Gen` is the **sole** desugaring assigned `Movability::Movable` (`hir.rs:1976-1983`) and the **sole** coroutine whose resume ABI (`Iterator::next`) takes unpinned `&mut Self` with no resume parameter (`abi.rs:128-137, 171-182`; `coroutine/mod.rs:946-968, 1198-1200`). Both the classic and next trait solvers grant every `Movability::Movable` coroutine an **unconditional** built-in `Unpin` implementation with zero sub-obligations—even when the generator holds a `!Unpin` `PhantomPinned` local across `yield`—and unconditionally implement `core::iter::FusedIterator` for `gen` blocks (`candidate_assembly.rs:816-828`; `confirmation.rs:243-259`; `trait_goals.rs:579-600, 1450-1466`). By contrast, `AsyncGen` is `Movability::Static` (`!Unpin`, `E0277`), lowers `AsyncIterator::poll_next` to `Pin<&mut Self>` + `&mut Context<'_> -> Poll<Option<T>>`, and accepts self-borrows across both `yield` and `.await` (consumed via `for await`'s synthesized `unsafe { Pin::new_unchecked(&mut iter) }`).
2. **`E0626` (`!place.is_indirect()`) Relocation Soundness and a Live Safe-Rust `Box` + `mem::swap` Stacked Borrows vs. Tree Borrows Divergence (`rustc_borrowck`, Miri):** `MirBorrowckCtxt` enforces mid-yield relocation safety on `Movable` `gen` blocks by running `check_for_local_borrow` at every `TerminatorKind::Yield` (`rustc_borrowck/src/lib.rs:462-463, 1003-1011, 1859-1870`), rejecting any active loan with `borrow_of_local_data(place) = !place.is_indirect()` (`path_utils.rs:124-128`) via **`E0626`**. This rejects borrows of both stack locals (`&x`) and by-value captured upvars (`gen move { let r = &upvar; yield 1; }`, since upvars live inline in the coroutine struct), while **accepting** reborrows through external references (`&ext[0]`) and **`Box<T>` dereferences (`let b = Box::new(v); let r = &*b; yield *r;`)**. While scalar and external-ref mid-yield `core::mem::swap(&mut g1, &mut g2)` executes cleanly and identically under native code, Miri Stacked Borrows, and Miri Tree Borrows (`UNPIN=true`, `SWAP=Some(11),Some(21),Some(22),Some(12)`), a **100% safe Rust** `gen` block holding `b = Box::new(v)` and `r = &*b` across `yield` and swapped mid-yield via `core::mem::swap` **compiles cleanly (`rc = 0`) and passes Miri Tree Borrows (`rc = 0`, `BOX_DEREF_SWAP=Some(11),Some(22),Some(122),Some(111)`)**, yet triggers **immediate Undefined Behavior under Miri Stacked Borrows (`rc = 1`)** when `intrinsics::typed_swap_nonoverlapping` performs a `Unique` retag of `Box<i32>` that pops `r`'s `SharedReadOnly` tag before retagging field `r`.
3. **`BitMatrix` `storage_conflicts`, Early Statement Effects (`#73137`), and `257 B` vs. `513 B` Saved-Local Slot Packing (`coroutine/layout.rs`, `storage_liveness.rs`, `rustc_abi/src/layout/coroutine.rs`):** `rustc` overlaps saved locals from disjoint suspension variants only when they are single-variant and non-conflicting in `storage_conflicts: BitMatrix<CoroutineSavedLocal, CoroutineSavedLocal>`. Crucially, `StorageConflictVisitor` samples `MaybeRequiresStorage` **after early statement effects** (`visit_after_early_statement_effect`), where `Assign((lhs, _))` has already generated `lhs` before `apply_primary_statement_effect` kills a moved-from `rhs` (`storage_liveness.rs:177-241`), and `-Zvalidate-mir` audits this invariant via `EnsureCoroutineFieldAssignmentsNeverAlias` (`coroutine/mod.rs:1136-1144, 1260-1385`, regression guard for `rust-lang/rust#73137`). Live `-Zprint-type-sizes` and `StateTransform` MIR dumps verify a 3-way split: two disjoint-scope `[u8; 256]` locals pack into **`257 B`** (`1 B` discriminant + `256 B` overlapping slot; `BitMatrix(2x2) {(_s0, _s0), (_s1, _s1)}`), two simultaneously live buffers take **`513 B`**, and a **`#73137` assignment handoff** (`let mut b = a;` between two disjoint yields where `Suspend0: [_s0]` and `Suspend1: [_s1]` share zero suspension points) yields the full conflict matrix `BitMatrix(2x2) {(_s0, _s0), (_s0, _s1), (_s1, _s0), (_s1, _s1)}` and **`513 B`** (`Suspend1` emits `256 B` padding before `.b`). All coroutine layouts additionally force `largest_niche: None` (`rustc_abi/src/layout/coroutine.rs:324-330`) to avoid aliasing violations during discriminant reads.
4. **Live Post-Panic `gen` Fusing Bug (`coroutine/mod.rs` vs. `panicking.rs:205`/`206`):** Across every inspected revision (`1.98.0-nightly`, `49d734536`, `1.102.0-nightly`, and `master` HEAD `342d74463`), `create_coroutine_resume_function` routes `CoroutineArgs::RETURNED` (`1`) for both `Gen` and `AsyncGen` to `transform.insert_none_ret_block(body)` (fusing to `Option::None` / `Poll::Ready(None)`), **but routes `CoroutineArgs::POISONED` (`2`) unconditionally to `insert_panic_block(..., ResumedAfterPanic(transform.coroutine_kind))` without matching on `CoroutineDesugaring::Gen`**. Calling `g.next()` after catching an unwinding panic inside a `gen` block therefore violates `gen`'s built-in `FusedIterator` contract and panics at runtime with `library/core/src/panicking.rs`'s own broken-invariant string: ``"`gen fn` should just keep returning `None` after panicking"`` (`LangItem::PanicGenFnNonePanic`). In `3ef0c22cd`/`342d74463`, the `-Zasync-panic=false` branch on `POISONED` additionally invokes `insert_poll_pending_block` unconditionally, emitting a `Poll::Pending` aggregate into a `gen` body whose return type is `Option<Yield>`.
5. **Fail-Closed `joshlf/anneal` Trusted MIR Boundary (`c131b320eeeb26ef692e5afd5ec8db49ee518613`):** `Trusted.MirAst` currently maps `TyKind::{Coroutine, CoroutineClosure, CoroutineWitness}`, `ProjectionElem::Downcast`, `StatementKind::SetDiscriminant`, and `TerminatorKind::{Yield, CoroutineDrop, UnwindResume, UnwindTerminate}` fail-closed to `.unsupported`, establishing the exact five semantic obligations required before a verified MIR interpreter or compiler backend can admit lowered `gen`/`async gen` state machines.
6. **Constructive `Lean v4.34.1` Soundness & Sharpness Proofs (`support/GenAsyncGenMovabilityAndFusingSoundness.lean`):** A 1,386-line standalone Lean `v4.34.1` formalization kernel-checks (`-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`, `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, `0` `._unsafe_rec` across `616` declarations) three main theorems (`movable_gen_no_self_borrow_relocation_bisim`, `conflict_free_slot_coloring_preserves_semantics`, `repaired_gen_poisoned_fuses_to_none`), two corollaries (`movable_gen_mem_swap_interleaving_bisim`, `disjoint_two_phase_coloring_fits_in_one_slot`), and three constructive sharpness counterexamples (`ce1_unpinned_next_with_self_borrow_dangles_after_swap`, `ce2_stmt_lhs_rhs_missing_conflict_self_aliases_issue_73137`, `ce3_unpatched_poisoned_arm_panics_instead_of_fusing`), depending at most on `propext` (and `[]` for `repaired_gen_poisoned_fuses_to_none`).

## Applicability

### Covered Subjects and Their Relationships

This report characterizes upstream `rust-lang/rust` coroutine lowering, layout, borrow-checking, trait selection, and panicking behavior across four pinned revisions, relates those invariants to `joshlf/anneal`'s trusted MIR boundary, and mechanizes the operational invariants in `Lean v4.34.1`:

| Subject | Repository & Full Revision | Role in This Report |
| :--- | :--- | :--- |
| Primary execution & MIR/Miri toolchain | `rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`, `2026-05-31`, LLVM `22.1.6`) | Executed live on `x86_64-unknown-linux-gnu` for all probes in `support/probe_edition2024_gen_async_gen_and_fusing.py`: native binaries, hermetic offline Miri (Stacked Borrows and `-Zmiri-tree-borrows`), 11 compile-time gate tests, `-Zvalidate-mir`, `-Zdump-mir=StateTransform`, and `-Zprint-type-sizes`. Audited source files in `abi.rs`, `coroutine.rs`, `coroutine/drop.rs`, `rustc_abi/src/layout/coroutine.rs`, `storage_liveness.rs`, and `panicking.rs`. |
| Post-split coroutine lowering revision | `rust-lang/rust` @ `49d734536222bf28bb6d07d885b3a81d145981da` | Source comparison point after `coroutine.rs` was split into `coroutine/{mod.rs,layout.rs,drop.rs}` and immediately before `-Zasync-panic` wrapped the `POISONED` arm (`coroutine/mod.rs:888-896`). |
| Newer nightly comparison revision | `rust-lang/rust` @ `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`1.102.0-nightly`, `2026-11-11`) | Full source comparison across `abi.rs`, `coroutine/{mod.rs,layout.rs,drop.rs}`, `rustc_abi/src/layout/coroutine.rs`, `storage_liveness.rs`, `ast_lowering/src/expr.rs`, and `panicking.rs` (including `-Zasync-panic` default `true`). |
| Upstream `master` HEAD audit | `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (`2026-11-22`) | Latest upstream primary-source audit across 20 compiler and `core` source files (HIR, AST lowering, parser, symbol table, borrowck, classic & next trait solvers, ABI, `StateTransform`, dataflow, `rustc_abi` layout, MIR terminators, `core::panicking`, `core::async_iter`, and `rustc_session`). |
| Downstream verified-MIR consumer | `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613` | Audited `trusted/lean/Trusted/MirAst.lean` and `trusted/lean/Trusted/MirSemantics.lean` to determine which lowered coroutine MIR constructs are fail-closed `.unsupported` vs. modeled. |
| Mechanization kernel | `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Kernel-checked `support/GenAsyncGenMovabilityAndFusingSoundness.lean` with `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`. |

### Cross-Revision Continuity and Exact Deltas (`14210df0e` -> `49d734536` -> `3ef0c22cd` -> `342d74463`)

Direct file-by-file comparison across all four `rust-lang/rust` revisions establishes that **every semantic invariant and the post-panic `gen` fusing bug hold continuously across all four revisions**, with four concrete structural changes between `1.98.0-nightly` (`14210df0e`) and `master` (`342d74463`):

1. **Module split (`14210df0e` -> `49d734536`):** The monolithic `compiler/rustc_mir_transform/src/coroutine.rs` at `14210df0e` was refactored into `compiler/rustc_mir_transform/src/coroutine/mod.rs` and `compiler/rustc_mir_transform/src/coroutine/layout.rs` (alongside existing `drop.rs` and `by_move_body.rs`). All algorithms (`locals_live_across_suspend_points`, `compute_storage_conflicts`, `StorageConflictVisitor`, `EnsureCoroutineFieldAssignmentsNeverAlias`, `create_coroutine_resume_function`, `insert_none_ret_block`) remained semantically identical.
2. **Addition of `-Zasync-panic` (`49d734536` -> `3ef0c22cd`):** `create_coroutine_resume_function` wrapped the `CoroutineArgs::POISONED` and `CoroutineArgs::RETURNED` (`Async`/`Coroutine`) `insert_panic_block` calls inside `if tcx.sess.opts.unstable_opts.async_panic { ... } else { insert_poll_pending_block(...) }`, shifting the `POISONED` block from `coroutine/mod.rs:888-896` (`49d734536`) to `coroutine/mod.rs:897-909` (`3ef0c22cd` and `342d74463`). Because `-Zasync-panic` defaults to `true` (`compiler/rustc_session/src/options.rs:2491`), default runtime behavior is unchanged; under `-Zasync-panic=false`, however, the unguarded `POISONED` branch now erroneously emits `Poll::Pending` even for `Gen`.
3. **Coroutine layout packing option stub (`3ef0c22cd` -> `342d74463`):** `342d74463` added `PackCoroutineLayout::{Classic, CapturesOnly}` in `compiler/rustc_abi/src/layout/coroutine.rs:44-51` and set `pack: PackCoroutineLayout::Classic` in `compiler/rustc_mir_transform/src/coroutine/layout.rs:451-452` with an explicit `FIXME(-Zpack-coroutine-layout): Stop ignoring the flag here`, leaving layout packing identical to `3ef0c22cd` and `14210df0e`.
4. **Minor line shift in `library/core/src/panicking.rs` (`3ef0c22cd` -> `342d74463`):** Adding `#[allow(missing_docs)]` on `pub mod panic_const` at `342d74463:185` shifted `panic_const_gen_fn_none_panic` from line `205` (`14210df0e` and `3ef0c22cd`) to line `206` (`342d74463`).

### Edition, Feature Gates, and Execution Configuration

- **Edition 2024 Required for `gen` / `async gen` Syntax:** `kw::Gen` is reserved conditionally for `edition().at_least_rust_2024()` (`compiler/rustc_span/src/symbol.rs:3075-3086`), and `Parser::parse_expr_bottom` parses `gen {}` and `async gen {}` blocks only when `token_uninterpolated_span().at_least_rust_2024()` (`compiler/rustc_parse/src/parser/expr.rs:1402-1405`).
- **Unstable Feature Gates:** `#![feature(gen_blocks)]` is required for `gen {}` and `async gen {}`; `#![feature(async_iterator)]` is required to name `core::async_iter::AsyncIterator`; `#![feature(async_for_loop)]` is required for `for await` loops; `#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]` are required only for the raw `#[coroutine] || { yield ... }` comparison arm in Part B.
- **Panic Strategy:** Post-panic poisoning (`generate_poison_block_and_redirect_unwinds_there`) is emitted only when `tcx.sess.panic_strategy().unwinds()` (`can_unwind`, `coroutine/mod.rs:834-842`); under `-Cpanic=abort`, `can_unwind` is `false` and no `CoroutineArgs::POISONED` switch arm is emitted.

## Findings

### Finding 1: The 4-Way Coroutine Lowering, Movability, Trait, and ABI Matrix (`Coroutine`, `Async`, `Gen`, `AsyncGen`)

`Basis: source + execution`

#### 1.1 HIR Movability Classification (`hir.rs`) and `fn_sig_for_fn_abi` (`abi.rs`)

`rustc` represents all four resumable constructs as `ty::Coroutine(DefId, GenericArgs)` distinguished by `hir::CoroutineKind` (`compiler/rustc_hir/src/hir.rs:1967-2057` at `342d74463`). Movability is determined directly by `CoroutineKind::movability`:

```rust
// rust-lang/rust @ 342d74463af7dd3018ef6aa04dd5500c2deb5bd1
// compiler/rustc_hir/src/hir.rs:1975-1983
impl CoroutineKind {
    pub fn movability(self) -> Movability {
        match self {
            CoroutineKind::Desugared(CoroutineDesugaring::Async, _)
            | CoroutineKind::Desugared(CoroutineDesugaring::AsyncGen, _) => Movability::Static,
            CoroutineKind::Desugared(CoroutineDesugaring::Gen, _) => Movability::Movable,
            CoroutineKind::Coroutine(mov) => mov,
        }
    }
}
```

When computing the runtime call ABI for a coroutine's resume method, `rustc_ty_utils::abi::fn_sig_for_fn_abi` (`compiler/rustc_ty_utils/src/abi.rs:119-215` at `3ef0c22cd`/`342d74463`; `118-214` at `14210df0e`) branches specifically on `CoroutineDesugaring::Gen` to omit `Pin<...>` from the receiver and drop the resume argument entirely:

```rust
// rust-lang/rust @ 342d74463af7dd3018ef6aa04dd5500c2deb5bd1 (identical at 3ef0c22cd)
// compiler/rustc_ty_utils/src/abi.rs:123-137, 171-206
let env_ty = Ty::new_mut_ref(tcx, tcx.lifetimes.re_erased, ty);

let pin_did = tcx.require_lang_item(LangItem::Pin, DUMMY_SP);
let pin_adt_ref = tcx.adt_def(pin_did);
let pin_args = tcx.mk_args(&[env_ty.into()]);
let env_ty = match coroutine_kind {
    hir::CoroutineKind::Desugared(hir::CoroutineDesugaring::Gen, _) => {
        // Iterator::next doesn't accept a pinned argument,
        // unlike for all other coroutine kinds.
        env_ty
    }
    hir::CoroutineKind::Desugared(hir::CoroutineDesugaring::Async, _)
    | hir::CoroutineKind::Desugared(hir::CoroutineDesugaring::AsyncGen, _)
    | hir::CoroutineKind::Coroutine(_) => Ty::new_adt(tcx, pin_adt_ref, pin_args),
};
...
hir::CoroutineKind::Desugared(hir::CoroutineDesugaring::Gen, _) => {
    // The signature should be `Iterator::next(_) -> Option<Yield>`
    let option_did = tcx.require_lang_item(LangItem::Option, DUMMY_SP);
    let option_adt_ref = tcx.adt_def(option_did);
    let option_args = tcx.mk_args(&[sig.yield_ty.into()]);
    let ret_ty = Ty::new_adt(tcx, option_adt_ref, option_args);

    assert_eq!(sig.return_ty, tcx.types.unit);
    assert_eq!(sig.resume_ty, tcx.types.unit);

    (None, ret_ty)
}
hir::CoroutineKind::Desugared(hir::CoroutineDesugaring::AsyncGen, _) => {
    // The signature should be
    // `AsyncIterator::poll_next(_, &mut Context<'_>) -> Poll<Option<Output>>`
    assert_eq!(sig.return_ty, tcx.types.unit);

    // Yield type is already `Poll<Option<yield_ty>>`
    let ret_ty = sig.yield_ty;
    ...
    let context_mut_ref = Ty::new_task_context(tcx);
    (Some(context_mut_ref), ret_ty)
}
```

Correspondingly, `StateTransform::run_pass` (`compiler/rustc_mir_transform/src/coroutine/mod.rs:938-968, 1198-1200` at `3ef0c22cd`/`342d74463`) transforms `Gen` via `make_coroutine_state_argument_indirect` (`_1: &mut Self`, rewriting accesses to `(*_1)`), sets `body.arg_count = 1`, and inserts `CTX_ARG = const ()` at `START_BLOCK[0]`. By contrast, `Async`, `AsyncGen`, and `Coroutine(_)` call `make_coroutine_state_argument_pinned` (`_1: Pin<&mut Self>`, inserting `unpinned_local = copy (_1.0)` at `START_BLOCK[0]` and rewriting state accesses through `(*unpinned_local)`), and `Async`/`AsyncGen` additionally rewrite `ResumeTy` to `&mut Context<'_>` via `transform_async_context` (`mod.rs:616-654, 979-981`).

#### 1.2 Complete 4-Way Coroutine Matrix

| Dimension | Raw `#[coroutine]` (`Coroutine(mov)`) | `async {}` (`Desugared(Async, _)`) | `gen {}` (`Desugared(Gen, _)`) | `async gen {}` (`Desugared(AsyncGen, _)`) |
| :--- | :--- | :--- | :--- | :--- |
| **`Movability`** (`hir.rs:1976-1983`) | Explicit `mov` (`Movable` or `Static`) | `Movability::Static` | **`Movability::Movable`** | `Movability::Static` |
| **Built-in trait(s)** | `Coroutine<R>` | `Future` | **`Iterator` + `FusedIterator`** | `AsyncIterator` |
| **Resume receiver ABI** (`abi.rs:128-137`) | `Pin<&mut Self>` | `Pin<&mut Self>` | **`&mut Self` (unpinned)** | `Pin<&mut Self>` |
| **Resume arg ABI** (`abi.rs:145-215`) | `Some(Resume)` | `Some(&mut Context<'_>)` | **`None`** (`body.arg_count = 1`) | `Some(&mut Context<'_>)` |
| **Return type ABI** (`abi.rs:145-215`) | `CoroutineState<Y, R>` | `Poll<R>` (`yield_ty == ()`) | `Option<Y>` (`return_ty == ()`) | `Poll<Option<Y>>` (`return_ty == ()`) |
| **`Unpin` impl** (classic & next solver) | `Movable`: unconditional `Unpin`; `Static`: `!Unpin` | `!Unpin` (`NoSolution`) | **Unconditional `Unpin` (0 sub-obligations)** | `!Unpin` (`NoSolution`, `E0277`) |
| **Self-borrow across `yield`** | `Movable`: `E0626`; `Static`: allowed | Allowed | **Rejected (`E0626`)** | **Allowed** |
| **Post-`RETURNED` (`1`) resume** (`mod.rs:911-933`) | Panics (`ResumedAfterReturn`) | Panics (`ResumedAfterReturn`) | **Fuses to `Option::None`** | **Fuses to `Poll::Ready(None)`** (`AsyncGenFinished`) |
| **Post-`POISONED` (`2`) resume (unpatched, default `-Zasync-panic=true`)** | Panics (`coroutine resumed after panicking`) | Panics (`` `async fn` resumed after panicking ``) | **BUG: Panics (`` `gen fn` should just keep returning `None` after panicking ``)** | Panics (`` `async gen fn` resumed after panicking ``) |
| **Sync `Drop` shim on `RETURNED`/`POISONED`** (`drop.rs:198-202`) | No-op `Return` | No-op `Return` | No-op `Return` | No-op `Return` |

#### 1.3 Unconditional `Unpin` and `FusedIterator` in Both Trait Solvers, plus `async gen` / `for await` Desugaring

Both the classic selection engine (`compiler/rustc_trait_selection/src/traits/select/candidate_assembly.rs:816-828` and `confirmation.rs:243-259` at `342d74463`) and the next-generation trait solver (`compiler/rustc_next_trait_solver/src/solve/trait_goals.rs:579-600, 1450-1466` at `342d74463`) implement two special built-in rules for `ty::Coroutine(def_id, _)`:

```rust
// rust-lang/rust @ 342d74463af7dd3018ef6aa04dd5500c2deb5bd1
// compiler/rustc_trait_selection/src/traits/select/candidate_assembly.rs:816-828
ty::Coroutine(coroutine_def_id, _) => {
    if self.tcx().is_lang_item(def_id, LangItem::Unpin) {
        match self.tcx().coroutine_movability(coroutine_def_id) {
            hir::Movability::Static => {
                // Immovable coroutines are never `Unpin`, so
                // suppress the normal auto-impl candidate for it.
            }
            hir::Movability::Movable => {
                // Movable coroutines are always `Unpin`, so add an
                // unconditional builtin candidate with no sub-obligations.
                candidates.vec.push(BuiltinCandidate);
            }
        }
    } else { ... }
}
```

Because `confirm_builtin_candidate` returns `ty::Binder::dummy(vec![])` for `LangItem::Unpin` (`confirmation.rs:258-259`) and `trait_goals.rs:1460-1464` returns `Certainty::Yes` with zero nested goals, **a `gen` block implements `Unpin` unconditionally—even when it captures or holds a `!Unpin` field such as `core::marker::PhantomPinned` across a `yield`** (verified empirically in Part A `UNPIN_PP=true` and Part C `gen_with_phantom_pinned_is_unpin_accepted`, `rc = 0`). This does not permit safe self-pinning of that interior `PhantomPinned` across `yield`, because forming a `Pin<&mut PhantomPinned>` requires borrowing the local, which `E0626` rejects across `yield`. Likewise, `LangItem::FusedIterator` is granted unconditionally whenever `coroutine_is_gen(def_id)` holds (`confirmation.rs:243-249`; `trait_goals.rs:579-600`).

For `async gen`, AST lowering (`compiler/rustc_ast_lowering/src/expr.rs:1142-1151, 1678-1745` at `342d74463`) distinguishes two kinds of suspension inside the same coroutine body:
- User `yield expr` desugars to `task_context = yield async_gen_ready(expr)` (producing `Poll::Ready(Some(expr))` via `LangItem::AsyncGenReady`).
- Inner `.await` desugars to `task_context = yield ASYNC_GEN_PENDING` (`LangItem::AsyncGenPending`, producing `Poll::Pending`).
- Normal return from `async gen` assigns `LangItem::AsyncGenFinished` (`Poll::Ready(None)`, `coroutine/mod.rs:227-245, 298-320`).
- Consumer `for await pat in stream { body }` (`ast_lowering/src/expr.rs:1834-1900`) binds `ref mut iter` to `into_async_iter(stream)`, creates `unsafe { Pin::new_unchecked(&mut iter) }`, and polls `AsyncIterator::poll_next` inside a `make_lowered_await(..., FutureKind::AsyncIterator)` loop—pinning the `!Unpin` `async gen` state on the caller's stack for the entire loop without exposing `Pin::new_unchecked` to user code.

---

### Finding 2: `E0626` (`!place.is_indirect()`) Relocation Safety and the Safe-Rust `Box` + `mem::swap` Stacked Borrows vs. Tree Borrows Divergence

`Basis: source + execution + derived`

#### 2.1 Borrowck's `E0626` Predicate (`lib.rs`, `path_utils.rs`, `borrowck_errors.rs`)

When borrow-checking a coroutine body, `rustc_borrowck` computes `movable_coroutine = body.coroutine.is_some() && tcx.coroutine_movability(def.to_def_id()) == hir::Movability::Movable` (`compiler/rustc_borrowck/src/lib.rs:462-463` at `342d74463`). At every `TerminatorKind::Yield`, `MirBorrowckCtxt::visit_after_primary_terminator_effect` (`lib.rs:1003-1011`) inspects all active NLL loans in `state.borrows`:

```rust
// rust-lang/rust @ 342d74463af7dd3018ef6aa04dd5500c2deb5bd1
// compiler/rustc_borrowck/src/lib.rs:1003-1010, 1859-1870
TerminatorKind::Yield { value: _, resume: _, resume_arg: _, drop: _ } => {
    if self.movable_coroutine {
        // Look for any active borrows to locals
        for i in state.borrows.iter() {
            let borrow = &self.borrow_set[i];
            self.check_for_local_borrow(borrow, span);
        }
    }
}
...
fn check_for_local_borrow(&mut self, borrow: &BorrowData<'tcx>, yield_span: Span) {
    if borrow_of_local_data(borrow.borrowed_place) {
        let err = self.cannot_borrow_across_coroutine_yield(
            self.retrieve_borrow_spans(borrow).var_or_use(),
            yield_span,
        );
        self.buffer_error(err);
    }
}
```

And `borrow_of_local_data` (`compiler/rustc_borrowck/src/path_utils.rs:124-128` at `342d74463`) is a single-line structural test on the borrowed `Place`:

```rust
// rust-lang/rust @ 342d74463af7dd3018ef6aa04dd5500c2deb5bd1
// compiler/rustc_borrowck/src/path_utils.rs:124-128
pub(super) fn borrow_of_local_data(place: Place<'_>) -> bool {
    // Reborrow of already borrowed data is ignored
    // Any errors will be caught on the initial borrow
    !place.is_indirect()
}
```

This single predicate (`!place.is_indirect()`, i.e., `place.projection` contains no `ProjectionElem::Deref`) produces four crisp consequences:

1. **Stack locals (`_x`) are rejected (`E0626`):** `let x = 42; let r = &x; yield 1; yield *r;` has `borrowed_place = _x` (not indirect) -> `E0626: borrow may still be in use when gen block yields`.
2. **By-value captured upvars (`(_1.0)`) are rejected (`E0626`):** Inside `gen move { let r = &upvar; yield 1; yield *r; }`, `upvar` is projected via `ProjectionElem::Field(0)` directly off `SELF_ARG` (`_1`) with no `Deref`. Because the upvar resides inline inside the coroutine prefix, relocating the coroutine moves `upvar`; `!place.is_indirect()` is `true` and `rustc` rejects it with `E0626`.
3. **External-reference reborrows (`(*(_1.0))[0]`) are accepted (`rc = 0`):** Reborrowing through a captured `&'a [i32]` passes through `ProjectionElem::Deref`, so `place.is_indirect()` is `true` (`borrow_of_local_data == false`). The pointee resides outside the coroutine frame and remains valid across `mem::swap`.
4. **Owned `Box<T>` deref borrows (`(*_b)`) are accepted (`rc = 0`)—creating a Stacked Borrows vs. Tree Borrows aliasing seam!** Because built-in `Box<T>` dereference lowers in MIR to `ProjectionElem::Deref` (`(*_b)`), `(*_b).is_indirect()` is `true`! Thus `gen move { let b = Box::new(v); let r: &i32 = &*b; yield *r; yield *r + 100; }` passes `E0626` cleanly, placing both `b: Box<i32>` and `r: &i32` as sibling saved locals inside `Suspend0` of an `Unpin` `gen` struct.

#### 2.2 Empirical 11-Case Compile-Time Gate Matrix (`rustc 1.98.0-nightly`)

Running `support/probe_edition2024_gen_async_gen_and_fusing.py` (`part_c_compile_time_soundness_gates`, with `-Zvalidate-mir`) confirms all 11 compile-time boundaries:

| Probe Case | Edition | `rc` | Error Code(s) | Observed Rule Verified |
| :--- | :---: | :---: | :--- | :--- |
| `edition2021_gen_accepted_as_ident` | `2021` | `0` | none | `let gen = 7; gen` remains a valid identifier prior to Edition 2024 (`symbol.rs:3076`). |
| `edition2024_gen_keyword_rejected_as_ident` | `2024` | `1` | parse error | `expected identifier, found reserved keyword gen` (suggests `r#gen`). |
| `gen_non_unit_return_rejected` | `2024` | `1` | `E0308` | `return 99;` inside `gen {}` fails with `expected (), found integer` (`abi.rs:178`). |
| `gen_self_borrow_across_yield_rejected_e0626` | `2024` | `1` | `E0626` | Local borrow `let r = &x;` across `yield` rejected (`lib.rs:1004-1010`). |
| `async_gen_self_borrow_across_yield_accepted` | `2024` | `0` | none | `Movability::Static` skips `check_for_local_borrow` in `async gen {}`. |
| `gen_move_upvar_borrow_across_yield_rejected_e0626` | `2024` | `1` | `E0626` | By-value upvar borrow `&upvar` inside `gen move` has `!place.is_indirect()` -> rejected. |
| `gen_external_ref_reborrow_across_yield_accepted` | `2024` | `0` | none | Reborrow `&ext[0]` through `&'a [i32]` has `place.is_indirect() == true` -> accepted. |
| `gen_box_deref_borrow_across_yield_check` | `2024` | `0` | none | `let b = Box::new(42); let r = &*b; yield *r; yield *r;` passes `E0626` (`(*_b).is_indirect() == true`). |
| `async_gen_is_not_unpin_rejected_e0277` | `2024` | `1` | `E0277` | `assert_unpin(async gen { yield 1; })` fails: `Unpin` not implemented for `{async gen block}`. |
| `gen_with_phantom_pinned_is_unpin_accepted` | `2024` | `0` | none | `gen { let p = PhantomPinned; yield 1; let _ = p; }` satisfies `T: Unpin` unconditionally. |
| `gen_block_is_fused_iterator_accepted` | `2024` | `0` | none | `gen { yield 1; }` satisfies `T: core::iter::FusedIterator` via built-in impl. |

#### 2.3 Empirical Native + Miri (Stacked Borrows & Tree Borrows) Execution Results (Parts A & A2)

In Part A (`part_a_gen_async_gen_swap_for_await_and_miri`), native execution (`rustc 1.98.0-nightly -Zvalidate-mir`), hermetic Miri Stacked Borrows, and hermetic Miri Tree Borrows (`-Zmiri-tree-borrows`) all exit with `rc = 0` and produce **bit-for-bit identical stdout**:

```text
UNPIN=true UNPIN_PP=true FUSED_TRAIT=true SWAP=Some(11),Some(21),Some(22),Some(12) FUSED=(None, None) SZ_DISJOINT=257 SZ_OVERLAP=513 SZ_HANDOFF_73137=513 SUMS=11,10,16 ASYNC_GEN=(184, true) ASYNC_GEN_RETURNED_FUSED=true
```

This verifies dynamically across both aliasing models that:
- Mid-yield `core::mem::swap(&mut g1, &mut g2)` cleanly exchanges two suspended `gen` frames (`g1` yields `Some(11)`, then after swap yields `Some(21), Some(22)` while `g2` yields `Some(12)`), and normal completion fuses indefinitely to `(None, None)`.
- Self-borrowing `async gen` (`let arr = [10u32, 20, 30, 40]; let r: &[u32] = &arr[..];` held across both `yield` and `YieldOnce(false).await`, consumed via `for await`) preserves exact stack address stability across all suspensions (`ASYNC_GEN=(184, true)`) and fuses on normal completion (`ASYNC_GEN_RETURNED_FUSED=true`).

In **Part A2 (`part_a2_box_deref_swap_miri_sb_vs_tb`)**, however, executing the 100% safe Rust `Box` deref generator with mid-yield `core::mem::swap(&mut g1, &mut g2)` exposes a sharp Stacked Borrows vs. Tree Borrows divergence:

```rust
fn make_box_deref_gen(v: i32) -> impl Iterator<Item = i32> + Unpin {
    gen move {
        let b = Box::new(v);
        let r: &i32 = &*b;
        yield *r;
        yield *r + 100;
    }
}
// Caller (zero `unsafe` anywhere):
let mut g1 = make_box_deref_gen(11);
let mut g2 = make_box_deref_gen(22);
let a = g1.next();                // suspends in Suspend0 holding (b: Box<i32>, r: &i32)
core::mem::swap(&mut g1, &mut g2);
```

| Execution Mode (`rustc 1.98.0-nightly`, `14210df0e`) | `rc` | Observed Output / Diagnostic |
| :--- | :---: | :--- |
| Native binary (`-Zvalidate-mir`) | `0` | `BOX_DEREF_SWAP=Some(11),Some(22),Some(122),Some(111)` |
| Miri Tree Borrows (`-Zmiri-tree-borrows`) | `0` | `BOX_DEREF_SWAP=Some(11),Some(22),Some(122),Some(111)` (`stderr = ""`) |
| **Miri Stacked Borrows (default)** | **`1`** | `error: Undefined Behavior: trying to retag from <98> for SharedReadOnly permission at alloc120[0x0], but that tag does not exist in the borrow stack for this location` inside `core::mem::swap` -> `intrinsics::typed_swap_nonoverlapping` while retagging `.coroutine-state(3).<captured-var(1)>`; `<98>` created at `let r: &i32 = &*b;` was invalidated by a **`Unique` retag** of `b: Box<i32>` at `mem::swap(&mut g1, &mut g2)`. |

**Mechanism (`derived`):** `core::mem::swap` executes `intrinsics::typed_swap_nonoverlapping`, which recursively retags every live field of the coroutine's active variant (`Suspend0` = discriminant `3`). Under Stacked Borrows, moving/swapping `b: Box<i32>` performs an eager `Unique` retag on the heap allocation `alloc120`, popping every child `SharedReadOnly` tag (including `r`'s tag `<98>`) off `alloc120`'s borrow stack; retagging the sibling field `r: &i32` immediately afterward observes that `<98>` has been popped and raises immediate UB. Under Tree Borrows, `Box<T>` behaves as a lazily activated two-phase/Reserved pointer whose retag during a move without a write does not invalidate existing `Frozen` shared child borrows, so the swap succeeds cleanly. For any verified compiler or aliasing-model specification that aims to validate safe Edition 2024 `gen` blocks, this proves that **Stacked Borrows is incompatible with `rustc`'s existing `borrow_of_local_data` (`!place.is_indirect()`) + `Unpin` rules for `gen` blocks holding `Box<T>` and `&*b` across `yield`**, whereas Tree Borrows (or weakening `Box`'s move retag / banning `Box` deref borrows in `borrow_of_local_data`) is required.

---

### Finding 3: `BitMatrix` `storage_conflicts`, Early Statement Effects (`#73137`), `EnsureCoroutineFieldAssignmentsNeverAlias`, and `rustc_abi` Variant Packing (`257 B` vs. `513 B`)

`Basis: source + execution + derived`

#### 3.1 Saved-Local Liveness (`Movable` vs. `Static`) and Early-Effect `BitMatrix` Construction (`coroutine/layout.rs`, `storage_liveness.rs`)

`locals_live_across_suspend_points` (`compiler/rustc_mir_transform/src/coroutine/layout.rs:83-184` at `3ef0c22cd`/`342d74463`) computes the saved-local set `saved_locals: CoroutineSavedLocals` and the symmetric conflict matrix `storage_conflicts: BitMatrix<CoroutineSavedLocal, CoroutineSavedLocal>` from four MIR dataflow analyses:
1. `MaybeStorageLive` (upper bound on storage lifetime via `StorageLive`/`StorageDead`, with `always_storage_live_locals` for locals lacking storage markers),
2. `MaybeBorrowedLocals` (locals previously borrowed),
3. `MaybeRequiresStorage` (locals whose storage is currently required because they were written/borrowed and not yet killed by `StorageDead` or a non-borrowed move),
4. `MaybeLiveLocals` (standard backwards liveness ignoring borrows).

At each `TerminatorKind::Yield`, `live_locals` starts from `MaybeLiveLocals`. Crucially, lines `121-134` branch on `movable`:
- If `!movable` (`Async`, `AsyncGen`, `static` coroutines), `live_locals.union(borrowed_locals_cursor.get())` conservatively keeps every previously borrowed local alive across the yield (until `StorageDead`) because self-borrows or raw pointers derived from borrows may still point into it.
- If `movable` (`Gen`, non-`static` coroutines), `borrowed_locals` is **not** unioned, relying directly on `E0626` having ruled out safe borrows across `yield`.
- In both cases, `live_locals.intersect(requires_storage_cursor.get())` and `live_locals.remove(SELF_ARG)` finalize the variant's saved locals.

Next, `compute_storage_conflicts` (`layout.rs:235-341` at `3ef0c22cd`/`342d74463`; `coroutine.rs:860-955` at `14210df0e`) marks all `always_live_locals ∩ saved_locals` as conflicting with every saved local, filters out unreachable blocks and blocks terminating in `TerminatorKind::Unreachable`, and runs `StorageConflictVisitor` over `MaybeRequiresStorage` results **specifically at early effects** (`visit_after_early_statement_effect` and `visit_after_early_terminator_effect`):

```rust
// rust-lang/rust @ 342d74463af7dd3018ef6aa04dd5500c2deb5bd1
// compiler/rustc_mir_dataflow/src/impls/storage_liveness.rs:177-228
fn apply_early_statement_effect(&self, state: &mut Self::Domain, stmt: &Statement<'tcx>, _loc: Location) {
    MaybeBorrowedLocals::gen_statement(state, stmt);
    match &stmt.kind {
        StatementKind::StorageDead(l) => state.kill(*l),
        StatementKind::Assign((place, _)) => { state.gen_(place.local); }
        StatementKind::SetDiscriminant { place, .. } => { state.gen_(place.local); }
        ...
    }
}

fn apply_primary_statement_effect(&self, state: &mut Self::Domain, stmt: &Statement<'tcx>, loc: Location) {
    // If we move from a place then it only stops needing storage *after* that statement.
    self.check_for_move(state, loc);
    match &stmt.kind {
        StatementKind::Assign((place, _)) => { state.gen_(place.local); }
        ...
    }
}
```

**Why Early Effects Prevent `rust-lang/rust#73137` (`derived`):** Consider a MIR move/copy assignment `_dst = move _src` where `_src` is live across `Suspend0` only, `_dst` is live across `Suspend1` only, and `_dst = move _src` is simultaneously the **first definition** of `_dst` and the **last use (move-kill)** of `_src`.
- *Before* `_dst = move _src`, only `_src` is in `MaybeRequiresStorage`.
- *After* the primary effect (`check_for_move`), `_src` has been killed and only `_dst` is in `MaybeRequiresStorage`.
- **Only at the intermediate early-effect point** (`apply_early_statement_effect` having executed `state.gen_(_dst)` before `apply_primary_statement_effect` runs `check_for_move`) are **both `_dst` and `_src` simultaneously present in `state`**!

Consequently, `StorageConflictVisitor::visit_after_early_statement_effect` unions `{_dst, _src}` into `local_conflicts`, preventing `rustc_abi::layout::coroutine::layout` from overlapping `_dst` and `_src` at the same byte offset inside the coroutine struct. Immediately prior to `TransformVisitor` rewriting locals into downcast coroutine fields, `-Zvalidate-mir` runs `EnsureCoroutineFieldAssignmentsNeverAlias` (`coroutine/mod.rs:1136-1144, 1260-1385` at `3ef0c22cd`/`342d74463`; `coroutine.rs:1684-1790` at `14210df0e`), asserting `self.storage_conflicts.contains(lhs, rhs)` for every direct saved-local `Assign((lhs, rhs))`, `Call { destination, func, args }`, and `Yield { value, resume_arg }`.

#### 3.2 `rustc_abi::layout::coroutine::layout` Variant Packing & Niche Suppression

`compiler/rustc_abi/src/layout/coroutine.rs:62-339` (`342d74463`; `42-316` at `14210df0e`) consumes `variant_fields` and `storage_conflicts` in four steps:
1. **Multi-variant promotion (`coroutine.rs:77-96`):** Any saved local appearing in `> 1` suspension variant is immediately marked `SavedLocalEligibility::Ineligible` (promoted to the shared layout prefix).
2. **Greedy conflict resolution (`coroutine.rs:100-125`):** For every pair `(local_a, local_b)` with `storage_conflicts.contains(local_a, local_b)` currently assigned to *different* single variants, the local with higher conflict degree (`conflicts_a > conflicts_b`, ties broken by promoting `local_b`—or the second local in iteration order) is marked `Ineligible` and promoted to the prefix so the two can never overlap.
3. **Prefix + `StructKind::Prefixed` variant layout (`coroutine.rs:178-310`):** Upvars, the `Direct` discriminant tag (`u8` when `variant_fields.len() <= 256`), and all `Ineligible` promoted locals are laid out together as `prefix`. Each suspension variant lays out its remaining single-variant `Assigned(v)` locals starting after `(prefix.size, prefix.align)`, so non-conflicting single-variant locals from distinct variants share the exact same byte offsets (`size = max_v variant[v].size`).
4. **Unconditional niche suppression (`coroutine.rs:324-330`):** Every coroutine `LayoutData` sets `largest_niche: None` (citing `rust-lang/rust#63818`, `rust-lang/miri#3780`, and `#125735`) so discriminant reads never alias a self-borrowed field lacking `UnsafePinned`.

#### 3.3 Empirical 3-Way Proof: `257 B` Disjoint vs. `513 B` `#73137` Handoff vs. `513 B` Overlap

Live `rustc 1.98.0-nightly -O -Zvalidate-mir -Zprint-type-sizes -Zdump-mir=coroutine_resume` execution (Part D) confirms all three regimes verbatim:

| Coroutine Function | `variant_fields` (Captured MIR) | `storage_conflicts` (Captured MIR) | `size_of_val` | `-Zprint-type-sizes` Layout Breakdown |
| :--- | :--- | :--- | :---: | :--- |
| `make_gen_disjoint` (`{ let a=[1;256]; yield ... } { let b=[2;256]; yield ... }`) | `Suspend0(3): [_s0]`, `Suspend2(5): [_s1]` | `BitMatrix(2x2) {(_s0, _s0), (_s1, _s1)}` (diagonal only) | **`257 B`** | `discriminant: 1 B`; `Suspend0: 256 B (.a)`; `Suspend2: 256 B (.b)` (overlapping at offset `1`) |
| **`make_gen_handoff_73137`** (`let a=[1;256]; yield a[0]; let b = a; yield b[1]; yield b[255];`) | `Suspend0(3): [_s0]`, `Suspend1(4): [_s1]` (**disjoint variants!**) | **`BitMatrix(2x2) {(_s0, _s0), (_s0, _s1), (_s1, _s0), (_s1, _s1)}`** | **`513 B`** | `discriminant: 1 B`; `Suspend0: 256 B (.a)` (promoted prefix); **`Suspend1: 512 B (padding: 256 B, .b: 256 B)`** |
| `make_gen_overlap` (`a` and `b` both live across yield 2) | `Suspend0(3): [_s0]`, `Suspend1(4): [_s0, _s1]` | `BitMatrix(2x2) {(_s0, _s0), (_s0, _s1), (_s1, _s0), (_s1, _s1)}` | **`513 B`** | `discriminant: 1 B`; `Suspend0: 256 B (.a)`; `Suspend1: 512 B (.a: 256 B, .b: 256 B)` |

The `make_gen_handoff_73137` measurement is an unusually sharp empirical discriminator: `Suspend0` contains only `_s0` (`a`) and `Suspend1` contains only `_s1` (`b`), so variant-liveness alone would pack the generator into `257 B`. Instead, `MaybeRequiresStorage`'s early effect on `let mut b = a;` populates `(_s0, _s1)` and `(_s1, _s0)` in `BitMatrix(2x2)`, forcing `coroutine_saved_local_eligibility` to promote `.a` into the prefix and insert `256 bytes` of padding before `.b` in `Suspend1` (`513 B`), preserving MIR's non-aliasing assignment invariant.

---

### Finding 4: The Live Post-Panic `gen` Fusing Bug (`coroutine/mod.rs` vs. `panicking.rs:205`/`206`)

`Basis: normative + source + execution + derived`

#### 4.1 Primary-Source Root Cause Across Four Revisions

When a coroutine body can unwind (`can_unwind == true`), `generate_poison_block_and_redirect_unwinds_there` (`compiler/rustc_mir_transform/src/coroutine/mod.rs:845-874` at `3ef0c22cd`/`342d74463`; `827-856` at `49d734536`; `coroutine.rs:1191-1220` at `14210df0e`) creates a cleanup basic block executing `SetDiscriminant(*self, CoroutineArgs::POISONED)` (variant index `2`) followed by `TerminatorKind::UnwindResume`, and redirects every unwinding edge in the coroutine body through it.

Then `create_coroutine_resume_function` constructs the entry `SwitchInt` over `discriminant(*self)`:

```rust
// rust-lang/rust @ 3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1 & 342d74463af7dd3018ef6aa04dd5500c2deb5bd1
// compiler/rustc_mir_transform/src/coroutine/mod.rs:893-933
// (At 49d734536222bf28bb6d07d885b3a81d145981da: mod.rs:884-916, without the `async_panic` if/else;
//  at 14210df0e27ccd7d9e6a05b8085cbd438e4bbc65: coroutine.rs:1239-1271, without the `async_panic` if/else.)

// Jump to the entry point on the unresumed
cases.insert(0, (CoroutineArgs::UNRESUMED, START_BLOCK));

// Panic when resumed on the returned or poisoned state
if can_unwind {
    cases.insert(
        1,
        (
            CoroutineArgs::POISONED,
            if tcx.sess.opts.unstable_opts.async_panic {
                insert_panic_block(tcx, body, ResumedAfterPanic(transform.coroutine_kind))
            } else {
                insert_poll_pending_block(tcx, body, transform.old_ret_ty)
            },
        ),
    );
}

if can_return {
    let block = match transform.coroutine_kind {
        CoroutineKind::Desugared(CoroutineDesugaring::Async, _)
        | CoroutineKind::Coroutine(_) => {
            if tcx.is_async_drop_in_place_coroutine(body.source.def_id()) {
                insert_poll_ready_block(tcx, body)
            } else {
                if tcx.sess.opts.unstable_opts.async_panic {
                    insert_panic_block(tcx, body, ResumedAfterReturn(transform.coroutine_kind))
                } else {
                    insert_poll_pending_block(tcx, body, transform.old_ret_ty)
                }
            }
        }
        CoroutineKind::Desugared(CoroutineDesugaring::AsyncGen, _)
        | CoroutineKind::Desugared(CoroutineDesugaring::Gen, _) => {
            transform.insert_none_ret_block(body)
        }
    };
    cases.insert(1, (CoroutineArgs::RETURNED, block));
}
```

Compare the two arms side by side:
1. On **`CoroutineArgs::RETURNED` (`1`)**, `create_coroutine_resume_function` matches `transform.coroutine_kind` and routes both `Gen` and `AsyncGen` to `transform.insert_none_ret_block(body)` (`mod.rs:207-260`), returning `Option::None` (for `Gen`) or `LangItem::AsyncGenFinished` = `Poll::Ready(None)` (for `AsyncGen`).
2. On **`CoroutineArgs::POISONED` (`2`)**, `create_coroutine_resume_function` **omits the `match transform.coroutine_kind` check entirely** and routes **all four coroutine kinds** unconditionally to `insert_panic_block(tcx, body, ResumedAfterPanic(transform.coroutine_kind))`!
3. `AssertKind::panic_function` (`compiler/rustc_middle/src/mir/terminator.rs:208-217` at `342d74463`) maps `ResumedAfterPanic(CoroutineKind::Desugared(CoroutineDesugaring::Gen, _))` to **`LangItem::PanicGenFnNonePanic`**, which lowers to `core::panicking::panic_const::panic_const_gen_fn_none_panic` in `library/core/src/panicking.rs:205` (`14210df0e` & `3ef0c22cd`) / `:206` (`342d74463`):

```rust
// rust-lang/rust @ 3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1 (library/core/src/panicking.rs:198-206)
// (At 342d74463af7dd3018ef6aa04dd5500c2deb5bd1: lines 199-207)
panic_const_coroutine_resumed = "coroutine resumed after completion",
panic_const_async_fn_resumed = "`async fn` resumed after completion",
panic_const_async_gen_fn_resumed = "`async gen fn` resumed after completion",
panic_const_gen_fn_none = "`gen fn` should just keep returning `None` after completion",
panic_const_coroutine_resumed_panic = "coroutine resumed after panicking",
panic_const_async_fn_resumed_panic = "`async fn` resumed after panicking",
panic_const_async_gen_fn_resumed_panic = "`async gen fn` resumed after panicking",
panic_const_gen_fn_none_panic = "`gen fn` should just keep returning `None` after panicking",
```

Notice the smoking gun in `panicking.rs`'s own wording: while `panic_const_async_gen_fn_resumed_panic` states an ordinary user contract violation (``"`async gen fn` resumed after panicking"``), **both `panic_const_gen_fn_none` and `panic_const_gen_fn_none_panic` are written as internal-invariant-broken messages** (``"`gen fn` should just keep returning `None` after completion"`` / ``"`gen fn` should just keep returning `None` after panicking"``) that were intended to be unreachable! Because `RETURNED` was routed to `insert_none_ret_block`, `panic_const_gen_fn_none` is indeed unreachable; because `POISONED` was **not** routed to `insert_none_ret_block`, `panic_const_gen_fn_none_panic` fires at runtime in safe Rust whenever a caller catches a panic with `std::panic::catch_unwind` and calls `.next()` again on a `gen` block—simultaneously contradicting `panicking.rs` and breaking `gen`'s built-in `core::iter::FusedIterator` guarantee.

#### 4.2 Captured Live `StateTransform` MIR Showing Adjacent `1: RETURNED` and `2: POISONED` Arms

From `support/probe_edition2024_gen_async_gen_and_fusing_results.json` (`part_d_mir_lowering_and_type_sizes`, `make_gen_cond_panic`), `rustc` emits the exact buggy switch right next to the working `RETURNED` fusing block:

```mir
fn make_gen_cond_panic::{closure#0}(_1: &mut {gen block@<TMP>/part_d.rs:4:5: 4:13}) -> Option<i32> {
    bb0: {
        _12 = discriminant((*_1));
        switchInt(move _12) -> [0: bb16, 1: bb14, 2: bb13, 3: bb11, 4: bb12, otherwise: bb15];
    }
    ...
    bb10 (cleanup): {
        discriminant((*_1)) = 2;
        resume;
    }
    ...
    bb13: {
        assert(const false, "`gen fn` should just keep returning `None` after panicking") -> [success: bb13, unwind continue];
    }
    bb14: {
        _0 = Option::<i32>::None;
        return;
    }
    bb15: {
        unreachable;
    }
}
```

#### 4.3 Empirical 4-Way Post-Return and Post-Panic Resumption Matrix

Executing `part_b_post_panic_fusing_4way` live (`rustc 1.98.0-nightly`, `14210df0e`; identical source logic at `49d734536`, `3ef0c22cd`, and `342d74463`) reproduces all four coroutine kinds in one binary:

| Coroutine Kind | Resume After Normal Return (`CoroutineArgs::RETURNED = 1`) | Resume After Caught Unwind (`CoroutineArgs::POISONED = 2`) |
| :--- | :--- | :--- |
| **`gen {}`** | Returns `None` repeatedly (`FUSED=(None, None)`) | **Panics:** ``"`gen fn` should just keep returning `None` after panicking"`` (caught after `STEP1=Some(1)`, `STEP2_PANIC=Some("mid-gen-boom")`) |
| **`async gen {}`** | Returns `Poll::Ready(None)` repeatedly (`ASYNC_GEN_RETURNED_FUSED=true`) | **Panics:** ``"`async gen fn` resumed after panicking"`` (caught after `STEP1=Ready(Some(1))`, `STEP2_PANIC=Some("mid-async-gen-boom")`) |
| **`async {}`** | **Panics:** ``"`async fn` resumed after completion"`` (after `Ready(7)`) | **Panics:** ``"`async fn` resumed after panicking"`` (after `Some("mid-async-boom")`) |
| **Raw `#[coroutine]`** | **Panics:** `"coroutine resumed after completion"` (after `Yielded(1), Complete(99)`) | **Panics:** `"coroutine resumed after panicking"` (after `Yielded(1), Some("mid-coro-boom")`) |

#### 4.4 Secondary Defect Under `-Zasync-panic=false` (`3ef0c22cd` & `342d74463`, `Basis: source + derived`)

Inspecting `coroutine/mod.rs:897-909` at `3ef0c22cd` and `342d74463` reveals a secondary defect introduced alongside `-Zasync-panic`: when `-Zasync-panic=false` is passed on a `gen` block with `can_unwind == true`, the `else` branch invokes `insert_poll_pending_block(tcx, body, transform.old_ret_ty)` (`mod.rs:905`), which constructs `Poll::<()>::Pending` and assigns it to `Place::return_place()` (`mod.rs:792-821`)—even though `Place::return_place()` for a `gen` block has type `Option<Yield>`, not `Poll<...>`! Routing `CoroutineDesugaring::Gen` on `POISONED` to `transform.insert_none_ret_block(body)` (mirroring lines `912-931`) simultaneously eliminates both the live post-panic fusing bug and the `-Zasync-panic=false` return-type mismatch on `gen` blocks. Furthermore, `create_coroutine_drop_shim` (`coroutine/drop.rs:198-202`) already sends both `RETURNED` and `POISONED` to `default_block = Return` (no-op drop), so fusing `POISONED -> None` cannot cause any double-drop: all locals live at the unwinding suspension point were already dropped along the cleanup path prior to `bb10`'s `discriminant((*_1)) = 2; resume;`.

---

### Finding 5: `joshlf/anneal` Trusted MIR Support Boundary (`c131b320eeeb26ef692e5afd5ec8db49ee518613`)

`Basis: source + derived`

Direct inspection of `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`trusted/lean/Trusted/MirAst.lean` and `trusted/lean/Trusted/MirSemantics.lean`) shows that every coroutine-lowering MIR construct currently fails closed to `FaultKind.unsupported`:

| Lowered Coroutine MIR Construct | `joshlf/anneal` `Trusted.MirAst` Status (`c131b320e`) | Exact Coordinate |
| :--- | :--- | :--- |
| `TyKind::{Coroutine, CoroutineClosure, CoroutineWitness}` | Mapped fail-closed to `MirTy.unsupported` | `MirAst.lean:286, 308-311` |
| `ProjectionElem::Downcast(_, VariantIdx)` (used for every saved-local field `((*_1) as Suspend0).0`) | Mapped fail-closed to `ProjectionElem.unsupported` | `MirAst.lean:460, 469-475` |
| `StatementKind::SetDiscriminant { place, variant_index }` (state transitions to `1`, `2`, `3+k`) | Mapped fail-closed to `StatementKind.unsupported` | `MirAst.lean:637, 654-656` |
| `TerminatorKind::{Yield, CoroutineDrop}` (pre-`StateTransform` MIR) | Mapped fail-closed to `TerminatorKind.unsupported` | `MirAst.lean:762, 795` |
| `TerminatorKind::{UnwindResume, UnwindTerminate}` (cleanup poison block `bb10`) | Mapped fail-closed to `TerminatorKind.unsupported` | `MirAst.lean:749-750, 795` |
| `TerminatorKind::Unreachable` (entry `SwitchInt` `otherwise` arm `bb15`) | Modeled first-class; steps to `FaultKind.undefined` | `MirAst.lean:776`; `MirSemantics.lean:87` |
| `Operand.move` deinitialization (`deinitMovedPlace = true`) | Modeled conservatively: deinitializes non-ZST moved local | `MirSemantics.lean:67-69, 140-146` |

**Architectural Consequence (`derived`):** When extending a verified MIR interpreter (such as `Trusted.MirSemantics`) or a verified MIR-to-machine-code compiler to support Edition 2024 `gen` and `async gen` bodies after `StateTransform` (`Runtime(PostCleanup)` MIR), five non-local compiler obligations must be explicitly carried across the trust boundary:
1. **Unpinned relocation soundness (`gen`):** Proving safety of `core::mem::swap` on `PostCleanup` `gen` MIR requires either tracking `E0626` (`NoSelfBorrowAcrossYield`) from pre-`StateTransform` borrowck or validating the absence of interior-frame pointers in all `Suspend*` variants.
2. **`Box` move retagging semantics:** Any aliasing model for safe `gen` blocks must either adopt Tree Borrows semantics for `Box<T>` moves (Part A2 passes under Tree Borrows) or forbid `Box` deref borrows across `yield` in `borrow_of_local_data` (Part A2 fails under Stacked Borrows).
3. **`Downcast` field non-aliasing (`#73137`):** Lowering `Downcast(v).f` into byte offsets requires the `BitMatrix` `storage_conflicts` witness from `MaybeRequiresStorage`'s early effects so `dst = move src` between distinct saved locals never maps to overlapping offsets (especially under `deinitMovedPlace = true`!).
4. **`SetDiscriminant` + `UnwindResume` + `POISONED` dispatch:** Entry `SwitchInt`'s `otherwise: unreachable` requires an inductive invariant that the coroutine tag stays within `{0, 1, 2, 3..3+k-1}`; moreover, any `FusedIterator` specification on `gen` blocks MUST account for `rustc`'s live `POISONED -> panic` bug until patched upstream.
5. **Niche-free discriminant layout (`largest_niche: None`):** Tag reads in `Rvalue::Discriminant((*_1))` rely on `TagEncoding::Direct` outside variant payload regions so reading the tag never reads aliased self-referential fields.

---

### Finding 6: Constructive `Lean v4.34.1` Mechanization (`support/GenAsyncGenMovabilityAndFusingSoundness.lean`)

`Basis: derived + execution`

The standalone Lean `v4.34.1` module `support/GenAsyncGenMovabilityAndFusingSoundness.lean` (`1,386` lines, `58,643` bytes, `616` local declarations) mechanizes the three core soundness properties and three constructive sharpness counterexamples under strict constructive kernel discipline (`-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`, `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, `0` `deriving`, `0` `._unsafe_rec`):

| Theorem / Counterexample | Formal Property Proved | Exact `#print axioms` |
| :--- | :--- | :--- |
| **`movable_gen_no_self_borrow_relocation_bisim`** | For every `FrameProgram` satisfying `ProgNoSelfBorrow` (`E0626`), every `NoSelfBorrowFrame` `f`, every `ext : ExtMem`, every target address `b2 : Addr`, and every step count `n : Nat`, `evalTrace prog ext n (relocateFrame b2 f) = evalTrace prog ext n f` and `TraceNoDanglingUb (evalTrace prog ext n f)`. | `[propext]` |
| **`movable_gen_mem_swap_interleaving_bisim`** | Corollary for `core::mem::swap(&mut g1, &mut g2)` (`memSwapFrames g1 g2`): swapped `E0626`-clean frames yield traces identical to continuing `g2` and `g1` respectively, with zero dangling self-reference UB. | `[propext]` |
| **`conflict_free_slot_coloring_preserves_semantics`** | For every statement trace `stmts`, if `EarlyConflictsCover conflicts live stmts` (capturing `MaybeRequiresStorage::apply_early_statement_effect`), `ValidSlotColoring conflicts color`, and `StoreAgreesOnLive live env slots color`, then `execPacked color live slots stmts = execUnpacked live env stmts` (zero `#73137` `.ubAliasingAssign` faults and zero cross-variant clobbering). | `[propext]` |
| **`disjoint_two_phase_coloring_fits_in_one_slot`** | Constructive witness that a disjoint two-phase trace (`storageDead 0` before writing local `1`) is covered by `diagOnlyConflicts` and admits `singleSlotColor` (`0 ↦ 0, 1 ↦ 0`, modeling `257 B`), yielding `.ok [3, 5]`. | `[propext]` |
| **`repaired_gen_poisoned_fuses_to_none`** | For every `body : CoroBody`, every terminal state `d ∈ {RETURNED, POISONED}`, and every `n : Nat`: `iteratedResume repairedResumeStep .gen body n d = (replicateObs n .returnedNone, d)`, `coroDropStep d = .noopReturn`, and `asyncFn`/`coroutine` still panic on `POISONED`. | `[]` (**zero axioms**) |
| **`ce1_unpinned_next_with_self_borrow_dangles_after_swap`** | Sharpness counterexample: bypassing `E0626` lets a self-borrowing coroutine succeed when unmoved (`obsYield 1`, then `obsYield 42`), whereas relocating from `base = 1` to `base = 2` via `mem::swap` immediately triggers `.obsUbDanglingSelfRef`. | `[propext]` |
| **`ce2_stmt_lhs_rhs_missing_conflict_self_aliases_issue_73137`** | Sharpness counterexample (`#73137`): on `[writeConst 0 7, yieldLocal 0, assignMove 1 0, yieldLocal 1]`, `diagOnlyConflicts` satisfies `BuggyPostPrimaryConflictsCover` and admits `singleSlotColor` -> triggers `.ubAliasingAssign` on `assignMove 1 0`; whereas `EarlyConflictsCover` forces `color 1 ≠ color 0` (`513 B`), under which `execPacked = .ok [7, 7]`. | `[propext]` |
| **`ce3_unpatched_poisoned_arm_panics_instead_of_fusing`** | Sharpness counterexample: on `ce3PanickingGenBody`, call 1 yields `1`, call 2 unwinds to `.poisoned`, and call 3 under `unpatchedResumeStep .gen` evaluates to `.panickedResumed .panicGenFnNonePanic`, whereas `repairedResumeStep .gen` evaluates to `.returnedNone` (`u3.1 ≠ r3.1`). | `[propext]` |

## Boundaries

- **`not examined` — Dynamic execution of `-Zasync-panic=false` on `1.102.0-nightly` / `HEAD`:** The local execution toolchain is `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, which predates the `-Zasync-panic` unstable option. The conclusion that `-Zasync-panic=false` emits `Poll::Pending` into a `gen` block's `Option<Yield>` return place at `3ef0c22cd`/`342d74463` (`coroutine/mod.rs:902-906`) is `source + derived`, not dynamically executed.
- **`unsupported` / `not examined` — `-Zpack-coroutine-layout=captures-only` (`PackCoroutineLayout::CapturesOnly`):** Although `342d74463` introduced `PackCoroutineLayout::CapturesOnly` in `compiler/rustc_abi/src/layout/coroutine.rs:44-51`, `compiler/rustc_mir_transform/src/coroutine/layout.rs:451-452` explicitly hardcodes `PackCoroutineLayout::Classic` (`FIXME(-Zpack-coroutine-layout): Stop ignoring the flag here`). Layout behavior once `CapturesOnly` is wired up is `not examined`.
- **`not examined` — Async drop shims (`#![feature(async_drop)]`, `create_coroutine_drop_shim_async`, `ResumedAfterDrop`):** This report examines synchronous coroutine drop shims (`create_coroutine_drop_shim`, `coroutine/drop.rs:177-254`) and `ResumedAfterReturn`/`ResumedAfterPanic`; async-drop-enabled coroutines (`has_async_drops == true`, `drop.rs:258-340`) were not executed.
- **`unsupported` / `not examined` — `gen` closure syntax and `gen fn` item sugar:** `compiler/rustc_parse/src/parser/expr.rs:1399` notes `// FIXME: (async) gen closures aren't yet parsed` (`unsupported`). Item-level `gen fn` / `async gen fn` lower through the same `CoroutineDesugaring::{Gen, AsyncGen}` with `CoroutineSource::Fn` (and share identical `hir.rs`, `abi.rs`, and `coroutine/mod.rs` dispatch), but empirical probes directly executed `gen {}` / `async gen {}` blocks (`CoroutineSource::Block`).
- **`known not to apply` — `E0626` does not protect user `unsafe` raw-pointer self-borrows inside `gen` blocks:** `MirBorrowckCtxt::check_for_local_borrow` checks only active Rust borrows (`&T` / `&mut T`), and `locals_live_across_suspend_points` skips the `borrowed_locals` union when `movable == true` (`layout.rs:121-134`). Forming `&raw const x` inside an `unsafe` block in a `gen` block and dereferencing it after `core::mem::swap` is user-level `unsafe` UB; `E0626` guarantees relocation safety only for safe Rust (modulo the `Box` Stacked Borrows divergence documented in Finding 2.3).
- **`known not to apply` — Lean formalization is standalone, not a direct `import Trusted.MirSemantics` theorem:** Because `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` maps `Coroutine`, `Downcast`, `SetDiscriminant`, `Yield`, and `UnwindResume` fail-closed to `.unsupported`, `support/GenAsyncGenMovabilityAndFusingSoundness.lean` formalizes faithful first-order models of `rustc`'s coroutine frame relocation, `MaybeRequiresStorage` early-effect `BitMatrix` coloring, and 4-way resume/drop dispatch rather than importing `Trusted.MirSemantics`.
- **`not examined` — Non-`x86_64-unknown-linux-gnu` targets:** All native binaries, Miri executions, and `-Zprint-type-sizes` captures ran on `x86_64-unknown-linux-gnu`; alignment padding for types with alignment `> 1` or non-64-bit targets was not executed.

## Evidence

### Primary-Source Coordinates (All Commit SHAs Resolved Live via GitHub API)

| Repository & Full Commit SHA | File Path & Exact Line Range | Fact Supported |
| :--- | :--- | :--- |
| `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_hir/src/hir.rs:1967-2057` | `CoroutineKind::movability`: `Gen => Movable`, `Async \| AsyncGen => Static`. |
| `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (`3ef0c22cd` identical; `14210df0e`: `:118-214`) | `compiler/rustc_ty_utils/src/abi.rs:119-215` | `Gen` uniquely takes unpinned `&mut Self` (`None` resume arg, `Option<Yield>`); `Async`, `AsyncGen`, `Coroutine` take `Pin<&mut Self>`. |
| `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_span/src/symbol.rs:3075-3086`; `compiler/rustc_parse/src/parser/expr.rs:1395-1408` | Edition 2024 `kw::Gen` reservation and `gen` / `async gen` block parsing. |
| `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_ast_lowering/src/expr.rs:395-415, 867-935, 1142-1151, 1678-1745, 1822-1900` | `gen` / `async gen` HIR lowering, `async_gen_ready` / `ASYNC_GEN_PENDING`, and `for await` `Pin::new_unchecked` desugaring. |
| `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_borrowck/src/lib.rs:462-463, 1003-1011, 1859-1870`; `path_utils.rs:124-128`; `borrowck_errors.rs:382-411` | `movable_coroutine` check at `TerminatorKind::Yield`, `borrow_of_local_data = !place.is_indirect()`, and `E0626` diagnostic. |
| `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` | `compiler/rustc_trait_selection/src/traits/select/{candidate_assembly.rs:816-837, confirmation.rs:243-259}`; `compiler/rustc_next_trait_solver/src/solve/trait_goals.rs:579-600, 1450-1466` | Unconditional built-in `Unpin` for `Movable` coroutines, `NoSolution` for `Static`, and unconditional `FusedIterator` for `Gen`. |
| `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (`3ef0c22cd` identical; `49d734536`: `mod.rs:868-920`; `14210df0e`: `coroutine.rs:1223-1275, 1684-1790`) | `compiler/rustc_mir_transform/src/coroutine/mod.rs:207-260, 551-596, 845-986, 1136-1144, 1198-1200, 1260-1385` | `insert_none_ret_block`, `make_coroutine_state_argument_{indirect,pinned}`, `generate_poison_block_and_redirect_unwinds_there`, buggy `POISONED` arm in `create_coroutine_resume_function`, and `EnsureCoroutineFieldAssignmentsNeverAlias` (`#73137`). |
| `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (`3ef0c22cd`: same except `PackCoroutineLayout`; `14210df0e`: `coroutine.rs:860-955`) | `compiler/rustc_mir_transform/src/coroutine/layout.rs:83-184, 235-341, 446-458`; `compiler/rustc_mir_dataflow/src/impls/storage_liveness.rs:177-241` | `locals_live_across_suspend_points` (`!movable` borrow union), `compute_storage_conflicts`, `StorageConflictVisitor::visit_after_early_statement_effect`, and `MaybeRequiresStorage` early vs. primary effects. |
| `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (`14210df0e`: `:42-316`) | `compiler/rustc_abi/src/layout/coroutine.rs:44-51, 62-339`; `compiler/rustc_ty_utils/src/layout.rs:549-595` | `coroutine_saved_local_eligibility`, greedy promotion, `StructKind::Prefixed` overlap layout, and `largest_niche: None` (`#63818`, `miri#3780`). |
| `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (`3ef0c22cd` identical) | `compiler/rustc_mir_transform/src/coroutine/drop.rs:177-254` | `create_coroutine_drop_shim` maps `RETURNED` and `POISONED` to default no-op `Return`. |
| `rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (`3ef0c22cd` & `14210df0e`: `:201, 205`) | `compiler/rustc_middle/src/mir/terminator.rs:198-230`; `library/core/src/panicking.rs:185-216`; `compiler/rustc_session/src/options.rs:2491-2492` | `ResumedAfterPanic(Gen) -> LangItem::PanicGenFnNonePanic -> panic_const_gen_fn_none_panic` (``"`gen fn` should just keep returning `None` after panicking"``) and `-Zasync-panic` default `true`. |
| `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/Trusted/MirAst.lean:286, 308-311, 460, 469-475, 637, 654-656, 749-762, 776, 795`; `MirSemantics.lean:67-69, 87, 140-146` | Fail-closed `.unsupported` mapping for coroutine types, `Downcast`, `SetDiscriminant`, `Yield`, `CoroutineDrop`, `UnwindResume`; `deinitMovedPlace = true`; `Unreachable -> .fault .undefined`. |
| `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` | `Lean v4.34.1` Release binary (`x86_64-unknown-linux-gnu`) | Kernel-checked `support/GenAsyncGenMovabilityAndFusingSoundness.lean` (`LEAN_EXIT=0`, `UNSAFE_REC_COUNT=0`). |

### Preserved Support Artifacts and Verification Commands (Observed `2026-11-22`)

1. **`support/probe_edition2024_gen_async_gen_and_fusing.py`** and **`support/probe_edition2024_gen_async_gen_and_fusing_results.json`**:
   - Command:
     ```console
     python3 support/probe_edition2024_gen_async_gen_and_fusing.py --out support/probe_edition2024_gen_async_gen_and_fusing_results.json
     ```
   - Toolchain: `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, LLVM `22.1.6`) and bundled `miri` with hermetic offline `core` + `compiler_builtins` + `alloc` sysroot compiled from the active toolchain's `rust-src`.
   - Verified receipts in `probe_edition2024_gen_async_gen_and_fusing_results.json`:
     - Part A: `compile_rc=0`, `native_rc=0`, `miri_sb_rc=0`, `miri_tb_rc=0`, `all_three_outputs_identical=true`, stdout `UNPIN=true UNPIN_PP=true FUSED_TRAIT=true SWAP=Some(11),Some(21),Some(22),Some(12) FUSED=(None, None) SZ_DISJOINT=257 SZ_OVERLAP=513 SZ_HANDOFF_73137=513 SUMS=11,10,16 ASYNC_GEN=(184, true) ASYNC_GEN_RETURNED_FUSED=true`.
     - Part A2 (`Box` deref + `mem::swap`): `compile_rc=0`, `native_rc=0` (`BOX_DEREF_SWAP=Some(11),Some(22),Some(122),Some(111)`), `miri_tb_rc=0` (`BOX_DEREF_SWAP=Some(11),Some(22),Some(122),Some(111)`), `miri_sb_rc=1` (Stacked Borrows UB on `Unique` retag of `Box<i32>` inside `intrinsics::typed_swap_nonoverlapping`).
     - Part B (4-way post-return & post-panic): `compile_rc=0`, `native_rc=0`, exact panic strings captured for `GEN`, `ASYNC_GEN`, `ASYNC`, and `COROUTINE`.
     - Part C (11 compile-time gates): all 11 exit codes and error codes (`E0308`, `E0626`, `E0277`, keyword parse error) recorded verbatim.
     - Part D (`-O -Zvalidate-mir -Zprint-type-sizes -Zdump-mir=StateTransform|coroutine_resume`): `compile_rc=0`, exact `BitMatrix(2x2)` headers, `257 B` / `513 B` / `513 B` type-size layouts, and `make_gen_cond_panic` / `make_async_gen_cond_panic` MIR captured verbatim.
2. **`support/GenAsyncGenMovabilityAndFusingSoundness.lean`**:
   - Command:
     ```console
     LEAN_SYSROOT="$HOME/.elan/toolchains/leanprover--lean4---v4.34.1" \
       ~/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean \
       -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
       support/GenAsyncGenMovabilityAndFusingSoundness.lean
     ```
   - Observed result: exit code `0`, `0` warnings, `0` errors, `0` forbidden tokens (`sorry`, `omega`, `bv_decide`, `native_decide`, `partial def`, `deriving`, `Classical.choice`, `_unsafe_rec`), `TOTAL_LOCAL_DECLS=616`, `UNSAFE_REC_COUNT=0`, and `#print axioms` confirming `[propext]` on 7 theorems and `[]` (zero axioms) on `repaired_gen_poisoned_fuses_to_none`.

## Revalidation

To test whether a newer `rustc` nightly has fixed the post-panic `gen` fusing bug, changed `Box` deref borrow rules under `E0626`, altered `BitMatrix` `storage_conflicts` packing, or wired up `-Zpack-coroutine-layout`:

1. **One-command empirical discriminator (covers ABI, Miri Stacked/Tree Borrows, `257 B`/`513 B` layout, 4-way post-panic bug, 11 compile-time gates, and `StateTransform` MIR):**
   ```console
   python3 support/probe_edition2024_gen_async_gen_and_fusing.py
   ```
   - If `part_b_post_panic_fusing_4way.stdout_lines[0]` changes from `STEP3_PANICKED="\`gen fn\` should just keep returning \`None\` after panicking"` to `STEP3_RETURNED=None`, the upstream `create_coroutine_resume_function` `POISONED` bug has been fixed.
   - If `part_c_compile_time_soundness_gates.gen_box_deref_borrow_across_yield_check.rc` changes from `0` to `1` (`E0626`), or if `part_a2_box_deref_swap_miri_sb_vs_tb.miri_sb_rc` changes from `1` to `0`, the `Box` deref / Stacked Borrows seam has changed.
   - If `SZ_DISJOINT` or `SZ_HANDOFF_73137` diverges from `257` / `513`, inspect `part_d_mir_lowering_and_type_sizes.layout_headers` and `type_size_lines` to check whether `PackCoroutineLayout` or `MaybeRequiresStorage` changed.
2. **Narrow upstream source diff targets:**
   - `git diff <old>..<new> -- compiler/rustc_mir_transform/src/coroutine/mod.rs` (check `create_coroutine_resume_function`'s `CoroutineArgs::POISONED` branch and `-Zasync-panic` handling).
   - `git diff <old>..<new> -- compiler/rustc_mir_transform/src/coroutine/layout.rs compiler/rustc_mir_dataflow/src/impls/storage_liveness.rs compiler/rustc_abi/src/layout/coroutine.rs` (check `StorageConflictVisitor`, `MaybeRequiresStorage`, `PackCoroutineLayout`, and `largest_niche`).
   - `git diff <old>..<new> -- compiler/rustc_borrowck/src/path_utils.rs compiler/rustc_ty_utils/src/abi.rs` (check `borrow_of_local_data` and `CoroutineDesugaring::Gen` receiver ABI).
3. **Kernel re-verification of the Lean mechanization:**
   ```console
   LEAN_SYSROOT="$HOME/.elan/toolchains/leanprover--lean4---v4.34.1" \
     ~/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean \
     -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/GenAsyncGenMovabilityAndFusingSoundness.lean
   ```
   Confirm exit code `0` and that `#print axioms` reports only `[propext]` (or no axioms) for all 8 exported theorems.
