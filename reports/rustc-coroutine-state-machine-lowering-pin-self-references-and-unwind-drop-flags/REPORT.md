# `rustc` Coroutine State-Machine Lowering: `Pin`, Self-References, and Unwind Drop Flags

## Summary

`rustc` lowers `async fn` and `gen` / coroutine bodies after drop elaboration (`ElaborateDrops` -> `coroutine::StateTransform`) into discriminant-indexed enum state machines whose soundness depends jointly on exit-only discriminant updates, variant-overlapped union field layout for cross-suspend liveness and borrows, explicit `Panicked (2)` poisoning on unwind, and suppressing LLVM `noalias` / `nofree` / `dereferenceable(N)` on `&mut Self` / `Pin<&mut Self>` whenever `!Unpin` holds. Live upstream source inspection (`rust-lang/rust` `1.99.1@58cf8f9c` and `1.98.0-nightly@14210df0`), compilation probes on `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, LLVM `22.1.6`), and a zero-`sorry`, zero-`Classical.choice` `Lean v4.34.1` refinement mechanization establish four primary conclusions:

1. **`StateTransform` Structural Refactoring (`1.98` -> `1.99.1`) and Overlap Rules:** `1.99.1` refactored `compiler/rustc_mir_transform/src/coroutine.rs` into `coroutine/{mod.rs, layout.rs, drop.rs, by_move_body.rs}`, added slice-index reload generation (`process_projection_elem`), and preserved the core lowering invariant: when `!movable` (`async fn` and `static` coroutines), `locals_live_across_suspend_points` unions `MaybeLiveLocals` with `MaybeBorrowedLocals`, promotes multi-variant and storage-conflicting locals to a fixed prefix (`StructKind::Prefixed`), and overlaps mutually disjoint suspend-variant locals (`48 B` vs `64 B` array total in `movable_two_yield_coro`; `64 B` vs `>=96 B` in `async_non_self_ref_two_await`). All remapped saved fields lose every `StorageLive`/`StorageDead` marker (`0` remaining post-transform; re-added only on unsaved per-resume temporaries).
2. **`Unpin` Gating of LLVM `noalias`, `nofree`, and `dereferenceable(N)`:** In `rustc_ty_utils::abi` + `rustc_codegen_llvm::abi`, mutable-reference `NoAlias`, `NoFree`, and consequently `dereferenceable(N)` are gated by `ty.is_unpin(...) && ty.is_unsafe_unpin(...)` (while `Movability::Static` suppresses the built-in `Unpin` candidate). Live LLVM IR probes confirm `manual_unpin_fut_poll` and `drive_movable_coro` (`Unpin`) emit `ptr noalias noundef align 8 dereferenceable(16|48)` pre-optimization, whereas all `async fn` (`!Unpin`) `poll` and `drop_in_place` bodies emit `ptr noundef nonnull align 8` (missing `noalias` and `dereferenceable`). Meanwhile `captures(none)` is inferred by LLVM `-O2`/`-O3` only when the frame does not store a self-pointer back into itself (`drive_async_non_self_ref` gets `captures(none)`, whereas `drive_async_self_ref` and `drive_async_nested_drop` remain `captures(none)`-absent).
3. **Unwind Poisoning (`Panicked = 2`), Drop Flags, and Post-Transform Cleanliness:** `generate_poison_block_and_redirect_unwinds_there` rewrites unwind edges to execute `SetDiscriminant(2)` before `UnwindResume`, while `create_coroutine_drop_shim` switches on `0` (`Unresumed`), `3+k` (`Suspendk`), and `otherwise -> Return` (no-op for both `Returned = 1` and `Panicked = 2`). Live binary runs verify `[1, 1, 1, 1]` drop counts under normal completion, early/late conditional drops, unwind panic, re-poll after panic (`"`async fn` resumed after panicking"`), and caller drop after panic. Crucially, `joshlf/anneal@c131b320e` (`Trusted/MirAst.lean:655,783`) currently drops `StatementKind::SetDiscriminant`, `TerminatorKind::Yield`, `TerminatorKind::CoroutineDrop`, and `TerminatorKind::Drop`, blocking direct ingestion of unlowered or lowered coroutine MIR until extended.
4. **Constructive Lean `v4.34.1` Lockstep Refinement and Sharpness Counterexamples:** [CoroutineStateTransformRefinement.lean](support/CoroutineStateTransformRefinement.lean) (`1,399` LOC, `14.3186s` synchronous kernel check, `0` `Classical.choice`, `0` `sorryAx`) proves lockstep trace simulation (`poll_step_lockstep_sim`, `cancel_drop_lockstep_sim`, `execTrace_lockstep_sim`, `no_double_drop_invariant`), plus constructive counterexamples proving that mis-annotating `noalias` on `!Unpin` `Pin<&mut Self>` triggers stale store-load forwarding (`15 != 99`) and LLVM `noalias` UB (`ce1_noalias_on_self_ref_pin_miscompiles`), and omitting `SetDiscriminant(2)` before unwinding causes both caller double-drops (`ce2a_missing_poison_double_drops`, `count = 2`) and caught-unwind re-poll uninitialized-payload faults (`ce2b_missing_poison_repoll_reads_uninit_payload`).

## Applicability

- **Target Compilers & IRs:** Directly characterizes `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`, LLVM `22.1.6`) and upstream source `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67` (`1.99.1`), together with LLVM `captures(none)` / `noalias` rules documented in `llvm/llvm-project@6dfe1677ab8dffbc6ec13d53a1e0215d75147689` (`llvm/docs/LangRef.md`). Applies to verified MIR frontends targeting `Runtime(PostCleanup)` MIR (or earlier MIR) produced with `-C panic=unwind` on `x86_64-unknown-linux-gnu`.
- **Downstream Verification Consumers:** Applies to MIR semantics and translation-validation designs targeting `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`Trusted/MirAst.lean`, `Trusted/MirSemantics.lean`), Miri/Stacked/Tree Borrows aliasing analyses (Jung et al., POPL 2020; Villani et al., PLDI 2025), and RefinedRust-style ownership refinements (Gäher et al., PLDI 2024).
- **Exclusions (`not examined` / `known not to apply`):** Coroutine async-drop shims (`create_coroutine_drop_shim_async` / proxy async drop in `coroutine/drop.rs`), `-Z autodiff` / `-Z sanitize` flags, `-C panic=abort` MIR variants, and `-Z mutable-noalias=no` overrides were not executed in the live compiler probe.

## Findings

### 1. Upstream `rust-lang/rust` Primary-Source Mechanics (`1.99.1` vs `1.98.0-nightly`)

#### 1.1 MIR Pipeline Order, Discriminant Encoding, and `1.98` -> `1.99.1` Refactoring `[source inspection]`

In `compiler/rustc_mir_transform/src/lib.rs` (`L649-678`, `@58cf8f9c`), `StateTransform` executes after drop elaboration (`ElaborateDrops` at `L652`, `AbortUnwindingCalls` at `L658`, `AddMovesForPackedDrops` at `L661`, `EraseDerefTemps` at `L662`, `ElaborateBoxDerefs` at `L663`, `coroutine::StateTransform` at `L664`), and is followed by `run_runtime_cleanup_passes` (`LowerIntrinsics`, `RemovePlaceMention`, `SimplifyCfg::PreOptimizations`) to reach `MirPhase::Runtime(RuntimePhase::PostCleanup)`.

Key primary-source invariants and version deltas between `1.98.0-nightly@14210df0` and `1.99.1@58cf8f9c`:

| Component | `1.98.0-nightly@14210df0` Location | `1.99.1@58cf8f9c` Location | Exact Compiler Behavior |
| :--- | :--- | :--- | :--- |
| Reserved discriminants & naming | `rustc_middle/src/ty/sty.rs` | `compiler/rustc_middle/src/ty/sty.rs:85-141` | `UNRESUMED=0`, `RETURNED=1`, `POISONED=2`, `RESERVED_VARIANTS=3`; `discr_ty` uses `tcx.types.u32` at MIR level while variant names are `"Unresumed"`, `"Returned"`, `"Panicked"`, `"Suspend{v - 3}"`. |
| Layout tag encoding & niche opt-out | `rustc_abi/src/layout/coroutine.rs` | `compiler/rustc_abi/src/layout/coroutine.rs:164-307` | Physical tag uses `Integer::fit_unsigned((variant_fields.len() - 1) as u128)` (`u8` up to `256` variants) with `TagEncoding::Direct`, `StructKind::Prefixed(prefix_size, prefix_align.abi)` (`L231`), and **`largest_niche: None` (`L307`)** (explicitly avoiding invalidating niche optimizations / aliasing invariants, referencing `rust-lang/rust#63818` and `rust-lang/miri#3780`). |
| Module split & index reload fix | Single `src/coroutine.rs` (`1,996` LOC) + `src/coroutine/drop.rs` (`758` LOC) | Split into `coroutine/{mod.rs (1,353), layout.rs (713), drop.rs (376), by_move_body.rs}` | `1.99.1` moves `transform_async_context` (`mod.rs:620`) and `deref_finder` into `create_coroutine_resume_function` (`mod.rs:867-944`), and adds `TransformVisitor::process_projection_elem` (`mod.rs:424-459`) to reload saved `PlaceElem::Index(local)` temporaries before indexing. |
| Cross-suspend liveness & borrows | `src/coroutine.rs:707-809` (`locals_live_across_suspend_points`) | `src/coroutine/layout.rs:82-183` | For `!movable` (`async fn`, `static`), unions `MaybeLiveLocals` with **`MaybeBorrowedLocals`** (`L120-133`), intersects with `MaybeRequiresStorage`, excludes `SELF_ARG`, and marks `always_live_locals` (`L85,172`) as conflicting with every saved local (`compute_storage_conflicts`, `L234-290`), preventing union overlap for prefix/borrowed locals. |
| `StorageLive`/`StorageDead` rewriting | `src/coroutine.rs` (`TransformVisitor`) | `src/coroutine/mod.rs:462-542`, `976-1030` | `TransformVisitor` converts `StorageLive`/`StorageDead` on remapped locals to `Nop` (`stmt.make_nop(true)` at `L467`); at `Yield` (`L515-535`), emits `StorageDead` only for unsaved locals, executes **`SetDiscriminant(3 + k)`**, and returns; `create_cases` (`L976-1030`) emits entry `StorageLive` for unsaved locals and copies `CTX_ARG` (`_2`) into `resume_arg`. |
| Unwind poisoning | `src/coroutine.rs:1191` | `src/coroutine/mod.rs:826-864` (`generate_poison_block_and_redirect_unwinds_there`) | Appends a cleanup block executing `SetDiscriminant(POISONED=2)` followed by `UnwindResume`; rewrites existing non-poison `UnwindResume` terminators to `Goto { target: poison_block }` and `UnwindAction::Continue` edges to `UnwindAction::Cleanup(poison_block)`. |
| Cancellation drop glue | `src/coroutine_drop.rs:528-627` | `src/coroutine/drop.rs:131-227` (`insert_clean_drop`, `create_coroutine_drop_shim`) | Builds `drop_in_place` switching on `discriminant((*_1))`: `0 -> drop_clean` (upvars), `3+k -> point.drop` (drops live locals & elaborated drop flags), and `otherwise -> Return` (idempotent no-op for `Returned=1` and `Panicked=2`). |

#### 1.2 `Unpin` Suppression of LLVM `noalias`, `nofree`, and `dereferenceable(N)` `[source inspection]`

Tracing mutable-reference parameter attributes across four `rustc` crates (`@58cf8f9c`) explains why `!Unpin` simultaneously strips **three** LLVM attributes rather than only `noalias`:

1. **`candidate_assembly.rs:818-839` (`rustc_trait_selection`):** `Movability::Static` provides no auto-impl `Unpin` candidate (unlike `Movability::Movable`, which pushes an unconditional builtin `Unpin` candidate at `L825`), leaving `async fn` (`Static`) coroutines `!Unpin` by construction.
2. **`ty/layout.rs:1065-1085` (`rustc_middle`):** At `OptLevel != No`, `PointerKind::MutableRef { unpin }` sets `unpin = optimize && ty.is_unpin(tcx, typing_env) && ty.is_unsafe_unpin(tcx, typing_env)`.
3. **`ty_utils/abi.rs:365-415` (`rustc_ty_utils`):** Both `ArgAttribute::NoAlias` (`L374`), `ArgAttribute::NoFree` (`L409`), and `-Z llvm-writable` `ArgAttribute::Writable` (`L388`) are guarded by `if unpin`; `CapturesReadOnly` (`L414`) applies only to immutable frozen references (`&T`), never `&mut T`.
4. **`codegen_llvm/abi.rs:48-112` (`rustc_codegen_llvm`):** Emits `llvm::AttributeKind::Dereferenceable` / `DereferenceableOrNull` **only when `regular.contains(ArgAttribute::NoFree)`** (`L82-84`: *"dereferenceable in LLVM currently implies nofree"*). Consequently, `!Unpin` clears both `noalias` and `dereferenceable(N)` on `Pin<&mut Self>` (`poll`) and `&mut Self` (`drop_in_place`). LLVM `LangRef.md` (`@6dfe1677`, `L1509-1521`) defines `noalias` UB whenever a location modified inside the function is also accessed via a pointer not *based* on the argument (which occurs on resumed self-referential coroutine polls holding a prior-activation pointer into `self`), while `captures(...)` (`L1531-1538+`) is inferred downstream by LLVM's middle-end rather than emitted by `rustc` for `&mut`.

---

### 2. Live `rustc 1.98.0-nightly` MIR, LLVM IR, and Runtime Compilation Probes `[real measurement]`

Running [probe_coroutine_lowering.py](support/probe_coroutine_lowering.py) on [coroutine_specimens.rs](support/coroutine_specimens.rs) (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`, commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, LLVM `22.1.6`) yielded complete pre-/post-`StateTransform` MIR dumps, 4-pipeline LLVM IR captures, and native binary execution measurements ([probe_coroutine_results.json](support/probe_coroutine_results.json)):

#### 2.1 Pre-/Post-Transform MIR & Memory Overlap Measurements

| Specimen | Size / Align (B) | `coroutine_before` BBs / Cleanup / `Yield` | `runtime-post-cleanup` BBs / Cleanup / `SetDiscr` | `coroutine_drop` BBs / `Switch` Arms | Saved Frame Fields & Overlapping Variants |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `manual_unpin_two_step` | `16` / `8` | `—` (hand-written enum) | `—` | `—` | Manual `Step::{Start, Mid, Done}`, `Unpin` |
| `make_movable_two_yield_coro` | `48` / `8` | `26` / `10` / `2` | `22` / `7` / `[1, 2, 3, 4]` | `12` / `{0, 3, 4, _}` | `_s0: [u64; 4]`, `_s1: [u64; 4]` (overlapped: `S0=[_s0]`, `S1=[_s1]`, saved `>=16 B`) |
| `async_non_self_ref_two_await` | `64` / `8` | `61` / `28` / `2` | `54` / `25` / `[1, 2, 3, 4]` | `12` / `{0, 3, 4, _}` | `S0=[_s0: [u64; 4], _s1: StepFut]`, `S1=[_s2: [u64; 4], _s3: StepFut]` (overlapped) |
| `async_self_ref_two_await` | `56` / `8` | `49` / `22` / `2` | `41` / `18` / `[1, 2, 3, 4]` | `12` / `{0, 3, 4, _}` | `S0=[_s0: u64, _s1: &u64, _s2: StepFut]`, `S1=[_s0, _s1, _s3: u64, _s4: StepFut]`; `no_retag copy = 3` |
| `inner_guarded_step` | `—` (`sret([48 x i8])`; embedded in `136 B`) | `29` / `12` / `1` | `24` / `9` / `[1, 2, 3]` | `12` / `{0, 3, _}` | `S0=[_s0: DropGuard, _s1: StepFut]` |
| `async_nested_drop_and_unwind` | `136` / `8` | `82` / `35` / `2` | `49` / `19` / `[1, 2, 3, 4]` | `30` / `{0, 3, 4, _}` | `_s0,_s4,_s5: DropGuard`, `_s2,_s3,_s8: bool` (elaborated drop flags!), `_s1: u64`, `_s6: StepFut`, `_s7: inner_guarded_step`; `S0=[_s0,_s1,_s2,_s3,_s4,_s5,_s6,_s8]`, `S1=[_s0,_s1,_s4,_s5,_s7,_s8]` |

Three structural observations hold uniformly across all `5` compiler-lowered coroutine bodies (`4` top-level lowered coroutines plus nested `inner_guarded_step`):
- **Zero remapped `StorageLive`/`StorageDead` overlap:** Across `coroutine_resume`, `coroutine_drop`, and `runtime-post-cleanup`, `storage_live_remapped_fields = 0` and `storage_dead_remapped_fields = 0` in every specimen. All surviving `StorageLive`/`StorageDead` operations (`76`/`122` in `async_non_self_ref`, `52`/`84` in `async_self_ref`, `57`/`89` in `async_nested_drop`, `37`/`52` in `movable_two_yield`) target short-lived function-frame locals rather than promoted state fields (`_s*`).
- **Discriminant updates occur strictly at yield/completion/poison exits:** Exactly one `discriminant((*_1))` read drives the entry `switchInt` (`0, 1, 2, 3, 4` for `async fn`, `{0, 1, 2, 3}` for single-await `inner_guarded_step`), while `coroutine_drop` switches strictly on `{0, 3, 4, otherwise}` (making `Returned=1` and `Panicked=2` fall into the shared no-op `otherwise` block).
- **Elaborated `bool` drop flags promoted into the coroutine enum:** `async_nested_drop_and_unwind` promotes three explicit `bool` drop flags (`_s2`, `_s3`, `_s8`) into variant payloads alongside `DropGuard` (`_s0, _s4, _s5`) so conditional early drops (`drop_scope_early = true` at `Suspend0 -> Suspend1`) remain tracked across suspension points without double-dropping.

#### 2.2 LLVM IR Parameter Attributes Across Optimization Configurations

Capturing `--emit=llvm-ir` across `o2_no_prepopulate` (`-C no-prepopulate-passes`, raw `rustc` emission), `o2_no_mir_inline` (`-Z inline-mir=no`), `o2`, and `o3` directly separates `rustc` ABI emission from LLVM middle-end (`FunctionAttrs`) inference:

| Function Role (`&mut Self` / `Pin<&mut Self>` arg) | `Unpin`? | Pre-opt (`o2_no_prepopulate`) 1st Param Attributes | Post-`-O2` / Post-`-O3` 1st Param Attributes | Diagnostic Meaning |
| :--- | :--- | :--- | :--- | :--- |
| `manual_unpin_fut_poll` / `drive_manual_unpin` | `Unpin` | `ptr noalias noundef align 8 dereferenceable(16)` | `ptr noalias noundef align 8 captures(none) dereferenceable(16)` | Both `noalias` and `dereferenceable(16)` emitted by `rustc`; LLVM infers `captures(none)`. |
| `coro_movable_resume` / `drive_movable_coro` | `Unpin` | `ptr noalias noundef align 8 dereferenceable(48)` | `ptr noalias noundef align 8 captures(none) dereferenceable(48)` (`coro_movable_resume` inlined) | Movable coroutine has `Unpin` (`candidate_assembly.rs:825`), so `noalias` + `dereferenceable(48)` remain active. |
| `drive_async_non_self_ref` / `coro_async_non_self_ref_poll` | `!Unpin` | `ptr noundef nonnull align 8` | `ptr noundef nonnull align 8 captures(none)` (on `drive_async_non_self_ref`; callee inlined) | **`!Unpin` strips both `noalias` and `dereferenceable`**, yet LLVM proves no pointer escape (`captures(none)` at `-O2`/`-O3`). |
| `drive_async_self_ref` / `coro_async_self_ref_poll` | `!Unpin` | `ptr noundef nonnull align 8` | `ptr noundef nonnull align 8` (NO `noalias`, NO `dereferenceable`, **NO `captures(none)`**) | Storing `&u64` back into the coroutine frame inhibits LLVM's `captures(none)` inference in addition to `rustc`'s `!Unpin` attribute suppression. |
| `drive_async_nested_drop` / `drop_glue_async_nested` | `!Unpin` | `ptr noundef nonnull align 8` | `ptr noundef nonnull align 8` (`drive_*`), `ptr noundef nonnull align 8 captures(none)` (`drop_glue_*`) | Even `drop_in_place` omits `noalias`/`dereferenceable`; note `drop_generic_future` takes `f: F` by-value (SysV64 `dead_on_return noalias readonly align 8 captures(address) dereferenceable(136) %f` on caller copy), not `&mut F`. |

*(Note: `o2_no_mir_inline` produces identical attribute summaries to `o2`, showing that inlining of coroutine `poll` into `drive_*` is performed by LLVM's inliner rather than MIR inlining for these `#[inline(never)]` wrapper entrypoints.)*

#### 2.3 Native Binary Lifecycle Drop, Panic-Payload, and Poll Latency Verification `[real measurement]`

Executing the `-O3` specimen binary (`4,445,432` bytes; `2.4141s` compile, `0.0635s` run) confirmed all 8 drop/panic scenarios and the self-referential computation (`self_ref_result = 79`, median `8.71 ns/poll` over 5 trials of `2,000,000` polls: `[6.849, 8.018, 8.71, 11.153, 12.632]` ns/poll):
- Drop counters `[upvar_guard, scope_guard, cond_guard, inner_guard]`:
  - `unresumed_drop = [1, 0, 0, 0]`, `normal_complete = [1, 1, 1, 1]`, `cancel_at_suspend0 = [1, 1, 1, 0]`, `cancel_at_suspend1_early_drop = [1, 1, 1, 1]`, `cancel_at_suspend1_late_drop = [1, 1, 1, 1]`, `after_unwind_poison = [1, 1, 1, 1]`, `after_repoll_panicked = [1, 1, 1, 1]`, `after_drop_panicked = [1, 1, 1, 1]`.
- Exact panic payloads matched `coroutine_resume` `AssertMessage`s: ``"`async fn` resumed after completion"`` and ``"`async fn` resumed after panicking"`` (following caught `"intentional step future panic"`).

---

### 3. Semantic Gap in `joshlf/anneal` (`c131b320e`) MIR Ingestion `[source inspection]`

Inspecting `trusted/lean/Trusted/MirAst.lean` and `trusted/lean/Trusted/MirSemantics.lean` at `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` reveals why existing `Trusted.MirSemantics` can parse `Rvalue::Discriminant` (`MirAst.lean:575,600`) yet **cannot** model either pre- or post-`StateTransform` coroutine MIR:
- `MirAst.lean:637,655` explicitly drops `StatementKind::SetDiscriminant` (`MirAst` fails closed with `.unsupported`);
- `MirAst.lean:762-763,783-784` explicitly drops `TerminatorKind::Yield`, `TerminatorKind::CoroutineDrop`, and `TerminatorKind::Drop` / unwinding edges;
- `MirAst.lean:286,310` rejects `TyKind::Coroutine` and `TyKind::CoroutineWitness`, and `MirAst.lean:709-711` notes `AssertMessage::ResumedAfter{Return,Panic,Drop}`;
- `MirSemantics.lean:921-947` sets `deinitMovedPlace = true`, requiring coroutine lowering proofs that move `_tmp0` out of overlapped union storage (`overlapUnionSlot`) before writing `tmp1` to respect move-deinitialization ordering cleanly.

---

### 4. Kernel-Checked `Lean v4.34.1` Refinement and Two Sharpness Counterexamples `[Lean proof]`

[CoroutineStateTransformRefinement.lean](support/CoroutineStateTransformRefinement.lean) (`1,399` lines, `40` definitions/inductives/structures/abbrevs, `19` theorems) formalizes a 2-suspend-point coroutine source operational semantics (`SrcCoroState`, `stepSrcPoll`, `stepSrcDrop`, tracking pinned locals borrowed across `.await`, conditional drop-guard early drops, cancellation drop, and unwind panics) and its lowered `StateTransform` frame (`LoweredFrame`, `loweredPoll`, `loweredDropGlue`, `DISCR_{UNRESUMED,RETURNED,POISONED,SUSPEND0,SUSPEND1}`, promoted prefix fields `s0..s3`, and overlapped union slot `overlapUnionSlot`). Synchronous single-threaded checking (`~/.local/bin/anneal-lean-run -- lean -DElab.async=false -Ddebug.skipKernelTC=false`) succeeded in `14.3186s` with exit code `0`, `0` forbidden tokens (`sorry`, `Classical.choice`, `omega`, `bv_decide`, `native_decide`, `Lean.ofReduceBool`, `partial def`, `._unsafe_rec`, `namespace Trusted`), and clean `#print axioms`:

| Theorem / Witness | Axioms (`#print axioms`) | Proved Statement |
| :--- | :--- | :--- |
| `init_sim` | `{}` (empty) | Initial states `(initSrc, initLowered)` satisfy `SimRel addr` (including constructive resource accounting). |
| `poll_step_lockstep_sim` | `[propext, Quot.sound]` | Every valid `poll` step (entry, resume across `Suspend0`/`Suspend1`, `Returned`/`Panicked` trap, unwind) matches outcome, avoids `.faultUninitOrAlias`, and preserves `SimRel addr`. |
| `cancel_drop_lockstep_sim` | `[propext]` | `loweredDropGlue` matches `stepSrcDrop` across all states (including discriminant-gated cleanup at `0, 3, 4` and idempotent no-op at `1, 2`). |
| `execTrace_lockstep_sim` | `[propext, Quot.sound]` | Multi-step inductive lockstep simulation over arbitrary safe ownership traces (`ValidActions`), proving identical output, drop log, and `NoDoubleDrop`. |
| `no_double_drop_invariant` | `[propext, Quot.sound]` | Every reachable state from `initLowered` satisfies `NoDoubleDrop` (`countGuard <= 1` for every guard). |
| `moving_suspended_self_ref_frame_faults` | `[propext]` | Relocating a suspended `!Unpin` frame (`addr -> addr + 64`) invalidates `_s1` and triggers `.faultUninitOrAlias` on the next poll (`Pin` necessity witness). |
| **CE1:** `ce1_noalias_on_self_ref_pin_miscompiles` | `[propext]` | Modeling LLVM `LangRef.md` `based_on` provenance (`prov_1 = 1` stored in `_s1` vs fresh poll `prov_2 = 2` on `Pin<&mut Self>`): emitting `noalias` allows alias-blind store-load reordering yielding stale `15` instead of `99` and triggering `noalias` UB. |
| **CE2a:** `ce2a_missing_poison_double_drops` | `[propext]` | Modeling `loweredPollMissingPoison` (omitting `SetDiscriminant(2)` before unwinding): caller stack-unwind `loweredDropGlue` re-enters `Suspend0` cleanup and double-drops `scopeGuard` (`count = 2`, `¬ NoDoubleDrop`), whereas sound `StateTransform` keeps `count = 1`. |
| **CE2b:** `ce2b_missing_poison_repoll_reads_uninit_payload` | `[propext]` | Caught-unwind re-poll after omitting `SetDiscriminant(2)` re-enters `Suspend0` and faults on moved-out `overlapUnionSlot = none` (`.faultUninitOrAlias`), whereas sound `StateTransform` traps cleanly with `.panicked .resumedAfterPanic`. |

---

### 5. Quantitative & Validation Scorecard (`L1`–`L6`, `C1`–`C2`, `V1`–`V4`)

| Dimension | Measured / Observed Value | Basis |
| :--- | :--- | :--- |
| **`L1` Proof & Authoring Effort** | `CoroutineStateTransformRefinement.lean`: `1,399` LOC (`40` defs/types/abbrevs, `19` theorems); `coroutine_specimens.rs`: `590` LOC; `probe_coroutine_lowering.py`: `599` LOC | Source inspection (`wc -l`) |
| **`L2` Toolchain Build / Check Time** | Lean `v4.34.1` synchronous kernel check: `14.3186s`; `rustc` MIR dump compile: `0.7612s`; `-O3` binary compile: `2.4141s`; binary run: `0.0635s` | Execution (`probe_coroutine_lowering.py`) |
| **`L3` MIR Transform / Pass Latency** | Standalone `rustc` `-Z time-passes` `StateTransform` pass latency: **not measured** (`0.7612s` covers full crate MIR dump compile) | Missing pass-isolated measurement |
| **`L4` Generated Code Speed** | `-O3` self-referential `async_self_ref_two_await` poll loop (`2,000,000` polls x `5` trials): `8.71 ns/poll` median (`[6.849, 8.018, 8.71, 11.153, 12.632]`); `-O0` vs `-O3` or forced-`noalias` delta: **not measured** | Execution (probe binary) / partial gap |
| **`L5` Frame Sizes & Overlap Savings** | Sizes `[B, align]`: `manual=[16,8]`, `movable=[48,8]`, `non_self_ref=[64,8]`, `self_ref=[56,8]`, `nested_drop=[136,8]`; `5/5` remapped coroutines exhibit `0` remapped `StorageLive`/`StorageDead` | Execution (`rustc` + binary + MIR parser) |
| **`L6` Footprint (Binary / RAM)** | `-O3` probe executable size: `4,445,432` bytes; peak Lean/rustc RAM RSS: **not measured** | `stat` on binary / RSS omitted |
| **`C1` Spec / TCB Auditability** | `0` `sorryAx`, `0` `Classical.choice`, `0` `Lean.ofReduceBool` (`native_decide`/`bv_decide`), `0` `omega`, `0` `partial def`, `0` `._unsafe_rec`, `0` fake `namespace Trusted`; Lean model is standalone (does not import `joshlf/anneal` `Trusted.MirSemantics`) | Execution (`#print axioms`) + source inspection |
| **`C2` Orthogonality** | Clean separation between source async semantics (`stepSrcPoll`/`stepSrcDrop`), lowered frame machine (`loweredPoll`/`loweredDropGlue`), and `Pin`/LLVM `noalias` sharpness obligations | Theorem decomposition (`CoroutineStateTransformRefinement.lean`) |
| **`V1` Non-Vacuity / Negatives** | `init_sim` inhabits concrete executions; `moving_suspended_self_ref_frame_faults` + `ce1` + `ce2a` + `ce2b` kernel-checked in Lean; all `8` Rust drop/panic traps + `self_ref_result = 79` verified at runtime | Execution (Lean + `-O3` binary) |
| **`V2` Differential Fuzzing / Miri** | Exhaustive finite-specimen lifecycle matrix (`8` scenarios, `5` coroutine types); random property fuzzing and live `cargo miri` execution: **not examined** | Outside probe harness |
| **`V3` Weak Memory / Async Drop** | Single-threaded pinned poll/drop semantics; multi-thread `Send`/`Sync` Future transfer across threads and unstable `async Drop` (`create_coroutine_drop_shim_async`): **not examined** | Outside scope |
| **`V4` Held-Out Crate Coverage** | Tested on self-contained `coroutine_specimens.rs` (`rustc 1.98.0-nightly`); whole-sysroot `core`/crates.io `StateTransform` census (`1.99.1`): **unsupported / not examined** in live probe | Explicit scope boundary |

## Boundaries

- **Toolchain Version Split (`1.98.0-nightly@14210df0` live binary vs `1.99.1@58cf8f9c` upstream audit):** Live `rustc` / LLVM IR probes executed against the installed `rustc 1.98.0-nightly (14210df0e 2026-05-31)` with LLVM `22.1.6`, whereas upstream source-line citations for split `coroutine/{mod.rs, layout.rs, drop.rs}` reflect `rust-lang/rust 1.99.1@58cf8f9c`. Wait-states, poison discriminants, overlap policy, and `Unpin` ABI gating match directly across both revisions, except `1.99.1` refactored `coroutine.rs` and added `process_projection_elem` index-reload emission (`not examined` dynamically on a compiled `1.99.1` binary).
- **Standalone Lean Model Boundary (`unsupported` directly in `joshlf/anneal@c131b320e`):** [CoroutineStateTransformRefinement.lean](support/CoroutineStateTransformRefinement.lean) models the 2-suspend-point coroutine state machine directly inside Lean without importing `joshlf/anneal` `Trusted.MirAst` or `Trusted.MirSemantics`, because `Trusted.MirAst@c131b320e` lacks `SetDiscriminant`, `Drop`, `Yield`, `CoroutineDrop`, and coroutine types (`known not to apply`). Extending `joshlf/anneal` to verify coroutine bodies requires adding `SetDiscriminant`, `Prefixed` union field offsets, and unwind/cleanup edges to `Trusted.MirSemantics`.
- **Single-Threaded & Non-Async-Drop Scope (`not examined`):** Neither the probe nor the Lean proof exercises unstable async destructors (`create_coroutine_drop_shim_async`), LLVM `-Z mutable-noalias=no`, `-C panic=abort` MIR, `UnsafePinned` (`rust-lang/rust#125735`), or cross-thread `Waker` synchronization.
- **Peak Memory RSS & Isolated Pass Timing (`unknown` / `not measured`):** `probe_coroutine_lowering.py` captures wall-clock compile/check durations and executable byte size (`4,445,432` B), but does not wrap child processes with `os.wait4` peak RSS or `-Z time-passes` isolation.

## Evidence

### Preserved Package Artifacts (`support/`)

| Artifact | Purpose | LOC | SHA-256 |
| :--- | :--- | ---: | :--- |
| [coroutine_specimens.rs](support/coroutine_specimens.rs) | Standalone `Unpin`/`!Unpin`, self-referential, nested drop-guard, panic-unwind, and poll-benchmark Rust specimens | `590` | `a979851f87aceb3d1176324d7e487e70f6af3bb4c05f6109639862e63ddebe0b` |
| [probe_coroutine_lowering.py](support/probe_coroutine_lowering.py) | Reproducible runner capturing 4 MIR snapshots, 4 LLVM IR opt configs, runtime lifecycle verification, and Lean kernel audit | `599` | `d8a2e1ebc4d2cddab56237cc4b758d326b753397491b35ed0d0d3348cb532006` |
| [CoroutineStateTransformRefinement.lean](support/CoroutineStateTransformRefinement.lean) | Kernel-checked Lean `v4.34.1` 2-suspend lockstep simulation + `NoDoubleDrop` + CE1/CE2 counterexamples (`0` `sorry`, `0` `Classical.choice`) | `1,399` | `55530ab801db9ab09ba2acb953200b8295acba42a685eb56a414dbfd6e23508d` |
| [probe_coroutine_results.json](support/probe_coroutine_results.json) | Structured probe output backing every numerical table, attribute string, drop log, and `#print axioms` output above | `3,007` | `9ebe6a31e4908680de40ed4647899a043a599372e26eae94687900e70e121a76` |

### Primary Pinned Upstream & Literature References (`2026-11-20`)

- **`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67` (`1.99.1`):**
  - `compiler/rustc_mir_transform/src/lib.rs` (`L649-678` pass ordering around `StateTransform`), `coroutine/mod.rs` (`L424-459` `process_projection_elem`, `L462-542` `TransformVisitor`, `L620` `transform_async_context`, `L826-864` `generate_poison_block_and_redirect_unwinds_there`, `L867-1030` `create_coroutine_resume_function` & `create_cases`, `L1034-1220` `StateTransform::run_pass`), `coroutine/layout.rs` (`L82-183` `locals_live_across_suspend_points`, `L234-290` `compute_storage_conflicts`), `coroutine/drop.rs` (`L131-227` `insert_clean_drop` & `create_coroutine_drop_shim`).
  - `compiler/rustc_abi/src/layout/coroutine.rs` (`L164-307` direct discriminant sizing, `StructKind::Prefixed`, `largest_niche: None`); `compiler/rustc_middle/src/ty/sty.rs` (`L85-141` `CoroutineArgsExt` discriminants `0,1,2,3+k`); `compiler/rustc_middle/src/ty/layout.rs` (`L1065-1085` `PointerKind::MutableRef { unpin }`); `compiler/rustc_ty_utils/src/abi.rs` (`L365-415` `NoAlias`/`NoFree`/`Writable`); `compiler/rustc_codegen_llvm/src/abi.rs` (`L48-112` `dereferenceable` gating on `NoFree`); `compiler/rustc_trait_selection/src/traits/select/candidate_assembly.rs` (`L818-839` `Movability` vs `Unpin`).
- **`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`):** Live compiler executable, plus `compiler/rustc_mir_transform/src/coroutine.rs` (`L707-809`, `L860`, `L1191-1665`) and `coroutine_drop.rs` (`L528-758`).
- **`llvm/llvm-project@6dfe1677ab8dffbc6ec13d53a1e0215d75147689` (`llvmorg-23.1.1`):** `llvm/docs/LangRef.md` (`L1509-1538+` `noalias` `based_on` rules and `captures(...)` semantics).
- **`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`):** Live Lean theorem prover verifying `CoroutineStateTransformRefinement.lean` (`-DElab.async=false -Ddebug.skipKernelTC=false`).
- **`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`:** `trusted/lean/Trusted/MirAst.lean` (`L286,310,575,600,637,655,709-711,762-763,783-784`) and `trusted/lean/Trusted/MirSemantics.lean` (`L921-947` `deinitMovedPlace = true`).
- **Peer-Reviewed Literature:**
  - Neven Villani, Johannes Hostert, Derek Dreyer, and Ralf Jung. *Tree Borrows*. PLDI 2025. DOI: `10.1145/3735592`.
  - Ralf Jung, Hoang-Hai Dang, Jeehoon Kang, and Derek Dreyer. *Stacked Borrows: An Aliasing Model for Rust*. POPL 2020.
  - Lennard Gäher, Michael Sammler, Ralf Jung, Robbert Krebbers, and Derek Dreyer. *RefinedRust: A Type System for High-Assurance Verification of Rust Programs*. PLDI 2024.

## Revalidation

Run from this package directory (`reports/rustc-coroutine-state-machine-lowering-pin-self-references-and-unwind-drop-flags/`) to re-verify all `rustc` MIR/LLVM/runtime measurements and the Lean `v4.34.1` refinement check end-to-end:

```bash
python3 support/probe_coroutine_lowering.py
```

Run the standalone synchronous Lean `v4.34.1` kernel check and forbidden-token check directly:

```bash
lean -DElab.async=false -Ddebug.skipKernelTC=false support/CoroutineStateTransformRefinement.lean
grep -n -E '\b(sorry|Classical\.choice|omega|bv_decide|native_decide|Lean\.ofReduceBool|partial def|\._unsafe_rec|namespace Trusted)\b' support/CoroutineStateTransformRefinement.lean
```

Validate corpus cataloging and structural/schema invariants from the corpus root:

```bash
python3 tools/reference.py catalog
python3 tools/reference.py check
```
