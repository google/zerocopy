# Synthesized MIR Shims, Pass-Pipeline Divergence, and Monomorphization Capture Completeness in rustc

## Summary

A Rust crate's compiled machine code executes substantially more MIR bodies than `tcx.mir_keys(())` or `--emit=mir` enumerates. In `rustc` (`rust-lang/rust` commit `c7d5ba59d8e11ee2e2204b173458eec4cb41c973`), every executable function in a codegen unit is represented by `MonoItem::Fn(Instance<'tcx>)`, where `Instance.def` is an `InstanceKind<'tcx>` whose callable variants split across `InstanceKind::Item(DefId)` (local HIR bodies, local and foreign tuple constructors, and cross-crate instantiated generics or `#[inline]` functions) and `InstanceKind::Shim(ShimKind<'tcx>)` covering **13 compiler-synthesized shim kinds**: `VTable`, `Reify`, `FnPtr`, `ClosureOnce`, `ConstructCoroutineInClosure`, `ThreadLocal`, `FutureDropPoll`, `DropGlue`, `Clone`, `FnAddrAsPtr`, `FnPtrFromPtr`, `AsyncDropGlueCtor`, and `AsyncDropGlue` (represented in `rustc 1.98.0-nightly` commits `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` and `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` as 12 flat `InstanceKind` shim variants prior to splitting `FnPtrAddrShim` into `FnAddrAsPtr` and `FnPtrFromPtr`).

Three structural properties govern whole-crate MIR verification and capture producers such as `anneal-rustc-capture` (`joshlf/anneal` commit `c131b320eeeb26ef692e5afd5ec8db49ee518613`):

1. **Query-routing and enumeration gaps (`mir_keys` vs. `dump_mono_stats` vs. `instance_mir`):**
   - `tcx.mir_keys(())` (`compiler/rustc_mir_transform/src/lib.rs:331-362`) returns `FxIndexSet<LocalDefId>` containing only local HIR body owners (excluding `GlobalAsm`), async-closure by-move bodies, and local free-item tuple struct/variant `Ctor` `DefId`s. It omits **100% of all 13 `ShimKind` variants** and **100% of cross-crate generic, `#[inline]`, and foreign `Ctor` instantiations**.
   - `-Zdump-mono-stats` (`compiler/rustc_monomorphize/src/partitioning.rs:1299-1305`) filters collected codegen-unit items by `MonoItem::is_user_defined()` (`compiler/rustc_middle/src/mono.rs:97-102`), which returns `matches!(instance.def, InstanceKind::Item(..))`. Consequently, `-Zdump-mono-stats` captures foreign generics alongside local items, but still **omits 100% of `InstanceKind::Shim` bodies**.
   - `TyCtxt::instance_mir(instance: InstanceKind<'tcx>)` (`compiler/rustc_middle/src/ty/mod.rs:1996-2035`) is the sole uniform MIR body selector: it routes `InstanceKind::Item(def)` with `DefKind::Ctor(..)` (as well as constants and `const { always: true }` functions) to `tcx.mir_for_ctfe(def)` (backed by `shim::build_adt_ctor`, and the only MIR table encoded in `.rmeta` for foreign constructors), routes other `InstanceKind::Item(def)` callables to `tcx.optimized_mir(def)`, and routes `InstanceKind::Shim(shim)` to `tcx.mir_shims(shim)` (`rustc_mir_transform::shim::make_shim`).
2. **Pass-pipeline divergence and `-Zdump-mir` filename-stem collisions:**
   - Standard local HIR bodies traverse four pass groups (`mir_built` -> `mir_promoted` + `mir_borrowck` -> `run_analysis_to_runtime_passes` including `ElaborateDrops` -> `run_optimization_passes` including `CheckAlignment`, `CheckNull`, `CheckEnums`, `GVN`, `CopyProp`, and `DeadStoreElimination`), producing `96` pass dump snapshots per function in `-Zdump-mir=all`.
   - Standard shims in `make_shim` (`compiler/rustc_mir_transform/src/shim.rs:32-206`) synthesize MIR directly in `MirPhase::Runtime(RuntimePhase::Initial)` with pre-elaborated drop/unwind ladders and execute `pm::run_passes_no_validate` over an abbreviated 8-pass pipeline (`MentionedItems`, `AddMovesForPackedDrops`, `RemoveNoopLandingPads`, `SimplifyCfg::MakeShim`, `InstSimplify::BeforeInline`, `ForceInline`, `AbortUnwindingCalls`, `CriticalCallEdges`; `17` dump snapshots), bypassing borrow checking, `MirValidator`, `ElaborateDrops`, and runtime UB-check insertion passes (`CheckAlignment`, `CheckNull`, `CheckEnums`). Tuple constructors (`build_adt_ctor`, `shim.rs:1011-1091`) run **zero** passes via `run_passes_no_validate(..., &[], Some(Runtime(Optimized)))`.
   - Because `MirDumper` names dump files by `def_path_str(body.source.def_id())`, a `#[track_caller]` item `f` and its `ShimKind::Reify(f, _)` wrapper share the identical dump filename stem `<crate>.<f>.*`; running `make_shim` during monomorphization **overwrites** `<crate>.<f>.3-3-000.runtime-optimized.after.mir` on disk with the 2-block `Reify` shim (`96 + 17 - 1 = 112` files). Any verification frontend that reads `-Zdump-mir` files from disk rather than calling `tcx.instance_mir` in-process silently loses `f`'s body.
3. **Empirical magnitude and mechanized soundness boundary:**
   - On the two-crate `shim_probe` + `dep_generics` specimen (`rustc 1.98.0-nightly`, `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), `collect_and_partition_mono_items` produces `95` total mono items (`92` `MonoItem::Fn` and `3` statics). Only `16/92` (`17.39%`) executable functions belong to `tcx.mir_keys(())`; the remaining **`76/92` (`82.61%`)** consist of `52` cross-crate generic/`#[inline]` instantiations (`56.52%`), `1` foreign `DefKind::Ctor` (`1.09%`), and **`23` synthesized `make_shim` bodies (`25.00%`)** (`10` `DropGlue`, `4` `ClosureOnce`, `3` `Reify`, `2` `VTable`, `2` `FnPtr`, `1` `Clone`, `1` `FnPtrAddr`)—matching `95 - 72 = 23` omitted by `-Zdump-mono-stats`.
   - In `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`), `Trusted.MirSemantics.CrateTheorem` (`trusted/lean/Trusted/MirSemantics.lean:1797-1804`) explicitly delegates whole-crate body completeness to the external capture producer. Kernel-checked `Lean v4.34.1` proofs in `support/MirShimsAndCaptureCompleteness.lean` establish: (a) exact-once forward field destruction and no-double-drop invariants of `buildDropShim` across normal, single-panic unwind, and double-panic `UnwindTerminate(InCleanup)` paths; (b) leak-free reverse-prefix unwind cleanup of `buildCloneShim` upon mid-tuple clone panic; (c) ABI arity resolution and definition-site `Location` binding of `buildReifyTrackCallerShim`; (d) whole-crate call-graph soundness under `CaptureComplete` (`MonoItem` closure); and (e) concrete counterexamples refuting both `mir_keys`-only and `dump_mono_stats`-only capture (`ce1`) and prefix-cleanup-free clone shims (`ce2`).

## Applicability

### Covered Subjects and Cross-Revision Scope

The findings in this report apply to the five immutable artifacts recorded in `REPORT.json`, whose roles and relationships are:

1. **`rust-lang/rust` at `c7d5ba59d8e11ee2e2204b173458eec4cb41c973`** — Primary upstream compiler source defining the nested `InstanceKind::Shim(ShimKind<'tcx>)` representation, all 13 `ShimKind` variants (`compiler/rustc_middle/src/ty/instance.rs:98-205`), `TyCtxt::instance_mir` (`compiler/rustc_middle/src/ty/mod.rs:1996-2035`), `make_shim` / `build_drop_shim` / `build_clone_shim` / `build_call_shim` / `build_adt_ctor` (`compiler/rustc_mir_transform/src/shim.rs:28-1332`), `mir_keys` (`compiler/rustc_mir_transform/src/lib.rs:331-362`), and `collect_and_partition_mono_items` (`compiler/rustc_monomorphize/src/collector.rs` and `partitioning.rs`).
2. **`rust-lang/rust` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`, LLVM `22.1.6`, `x86_64-unknown-linux-gnu`)** — Concrete execution toolchain used to compile, dump MIR/LLVM-IR/mono-items, test `-Zsanitizer=kcfi`, and run the compiled binaries in `support/probe_mir_shims_and_completeness.py`.
3. **`rust-lang/rust` at `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (`rustc 1.98.0-nightly (f8a08b688 2026-05-30)`)** — Exact compiler revision pinned by `COMPILER_VERSION` in `joshlf/anneal`'s `trusted/rustc-capture/src/driver.rs:25`.
4. **`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`** — Consumer verification framework whose `Trusted.MirAst` (`trusted/lean/Trusted/MirAst.lean:862-944`), `Trusted.MirSemantics` (`trusted/lean/Trusted/MirSemantics.lean:1679-1809`), and `anneal-rustc-capture` driver (`trusted/rustc-capture/src/driver.rs:1-152`) define the whole-crate capture completeness contract analyzed here.
5. **`leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52` (`Lean v4.34.1`)** — Kernel proof checker used to verify all definitions, theorems, and counterexamples in `support/MirShimsAndCaptureCompleteness.lean` with `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`.

### Exact Version Deltas Across the Three `rustc` Revisions

Direct diffing of `compiler/rustc_middle/src/ty/{instance.rs,mod.rs}`, `compiler/rustc_mir_transform/src/{lib.rs,shim.rs}`, and `compiler/rustc_monomorphize/src/{collector.rs,partitioning.rs}` across all three `rust-lang/rust` revisions establishes the exact shared invariants and version-specific differences:

| Compiler Surface | `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (`2026-05-30`) | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`2026-05-31`) | `c7d5ba59d8e11ee2e2204b173458eec4cb41c973` |
| :--- | :--- | :--- | :--- |
| `InstanceKind` layout | Flat 15-variant enum (`3` non-shim + `12` shim variants) | Identical flat 15-variant enum (`instance.rs:62-185`) | Nested 5-variant `InstanceKind` (`Item`, `Intrinsic`, `LlvmIntrinsic`, `Virtual`, `Shim(ShimKind)`) with 13-variant `ShimKind` (`instance.rs:62-205`) |
| Function-pointer cast shims | Single `InstanceKind::FnPtrAddrShim(DefId, Ty<'tcx>)` (`std::marker::FnPtr::addr`) | Single `InstanceKind::FnPtrAddrShim(DefId, Ty<'tcx>)` (`instance.rs:172`) | Split into `ShimKind::FnAddrAsPtr(DefId, Ty<'tcx>)` and `ShimKind::FnPtrFromPtr(DefId, Ty<'tcx>)` (`instance.rs:185-192`, `shim.rs:1100-1220`) |
| `ClosureOnce` payload | `ClosureOnceShim { call_once: DefId, track_caller: bool }` | `ClosureOnceShim { call_once: DefId, track_caller: bool }` (`instance.rs:125`) | `ShimKind::ClosureOnce { call_once: DefId, closure: DefId, track_caller: bool }` (`instance.rs:138`) |
| `VTable` `requires_caller_location` | Returns `false` (`_ => false` at `instance.rs:314`) | Returns `false` (`_ => false` at `instance.rs:317`) | Delegates to `def_id` `TRACK_CALLER` flag (`instance.rs:310-311`) |
| `build_drop_shim` visibility & signature | Private `fn build_drop_shim(tcx, def_id, ty)` (`shim.rs:299`) | Public `pub use shim::build_drop_shim` (`lib.rs:55`) taking explicit `typing_env: ty::TypingEnv<'tcx>` (`shim.rs:303-308`) for `rustc_driver` consumers | Public `pub fn build_drop_shim(tcx, def_id, ty, typing_env)` (`shim.rs:258-263`, `lib.rs:56`) |
| `instance_mir` intrinsic/virtual arm | Routes `Intrinsic` and `Virtual` to `mir_shims`, which hits `bug!()` inside `make_shim` (`ty/mod.rs:1774-1785`) | Identical to `f8a08b688c...` (`ty/mod.rs:1774-1785`) | Fails immediately in `instance_mir` with `bug!("intrinsics have no instance MIR")` / `bug!("virtual dispatches have no instance MIR")` (`ty/mod.rs:2021-2025`) |
| `mir_keys`, `make_shim` pass list, `DropGlue`/`Clone` ladders, `collect_crate_mono_items`, `dump_mono_items_stats` | Shared | Shared | Shared |

### Configuration and Flag Qualifications

- **Panic strategy (`-Cpanic=unwind` vs. `-Cpanic=abort`):** Unwind cleanup ladders in `build_drop_shim`, `build_clone_shim`, and `ClosureOnce` are emitted unconditionally during shim construction, then transformed in-place by `AbortUnwindingCalls` (`shim.rs:197`). Under `-Cpanic=unwind` (default on `x86_64-unknown-linux-gnu`), cleanup blocks (`is_cleanup = true`) survive to codegen; under `-Cpanic=abort`, `AbortUnwindingCalls` rewrites `UnwindAction::Cleanup(_)` edges to `UnwindAction::Terminate(UnwindTerminateReason::Abi)` and prunes unreachable cleanup blocks.
- **Collection mode (`Lazy` vs. `Eager`):** `collect_and_partition_mono_items` (`partitioning.rs:1170-1174`) selects `MonoItemCollectionStrategy::Lazy` by default and `MonoItemCollectionStrategy::Eager` only when `tcx.sess.link_dead_code()` (`-Clink-dead-code`) is enabled (or in incremental builds configured accordingly). Under `Lazy` collection, unreferenced private local items in `tcx.mir_keys(())` produce zero `MonoItem`s, while every transitively reachable shim and foreign generic is instantiated.
- **Generic sharing (`-Zshare-generics`):** `Instance::upstream_monomorphization` (`instance.rs:221-261`) can skip local codegen for upstream `InstanceKind::Item` and `ShimKind::DropGlue(_, Some(_))` / `AsyncDropGlueCtor` instances when `-Zshare-generics=yes` (default for debug dylib/incremental workflows when upstream exports monomorphizations, off at `-Copt-level=0` standalone rlib builds without `-Zshare-generics=yes`). Even when `-Zshare-generics=yes` links against an upstream symbol, whole-program verification still requires a verified contract or captured MIR body for that upstream `Instance`.
- **Kernel Control-Flow Integrity (`-Zsanitizer=kcfi`):** `ReifyReason` (`Some(ReifyReason::FnPtr)` vs. `Some(ReifyReason::Vtable)`) inside `ShimKind::Reify(DefId, Option<ReifyReason>)` is `None` in standard builds and populated (`tcx.sess.is_sanitizer_kcfi_enabled().then_some(...)`, `instance.rs:593, 649` in `14210df0e2...`) only when `-Zsanitizer=kcfi` is active.

## Findings

### 3.1 Callable Instance Architecture and the Exhaustive 13-Variant `ShimKind` Taxonomy

`Basis: source + execution`

In `rustc`, monomorphized MIR bodies are never materialized as separate `DefId`s in the HIR table (`compiler/rustc_middle/src/ty/instance.rs:23-27`). Instead, an executable specialization is an `Instance<'tcx>` pairing an `InstanceKind<'tcx>` with `GenericArgs<'tcx>`:

```rust
// rust-lang/rust @ c7d5ba59d8e11ee2e2204b173458eec4cb41c973
// compiler/rustc_middle/src/ty/instance.rs:33-36, 62-96
pub struct Instance<'tcx> {
    pub def: InstanceKind<'tcx>,
    pub args: GenericArgs<'tcx>,
}

pub enum InstanceKind<'tcx> {
    Item(DefId),
    Intrinsic(DefId),
    LlvmIntrinsic(DefId),
    Virtual(DefId, usize),
    Shim(ShimKind<'tcx>),
}
```

Among the five `InstanceKind` variants, `Intrinsic` and `LlvmIntrinsic` have no callable MIR (unless an unreplaced `#[rustc_intrinsic]` fallback body is monomorphized as `Instance::new_raw` -> `InstanceKind::Item`, `collector.rs:1024-1040`), and `Virtual(def_id, vtable_index)` represents dynamic vtable dispatch lowered directly by codegen (`instance_mir` panics if queried on `Virtual`, `ty/mod.rs:2024`). All remaining executable functions in a compiled crate are either `InstanceKind::Item(DefId)` or one of the **13 variants of `ShimKind<'tcx>`** (`compiler/rustc_middle/src/ty/instance.rs:100-205`):

| # | `ShimKind` Variant (`c7d5ba59...`) | Resolution Site | MIR Synthesizer (`shim.rs` / `async_destructor_ctor.rs`) | `has_polymorphic_mir_body` | `requires_caller_location` | `-Zprint-mono-items` Suffix |
| ---: | :--- | :--- | :--- | :--- | :--- | :--- |
| 1 | `VTable(DefId)` | `Instance::expect_resolve_for_vtable` (`unsized_fn_params` by-value `self: Self`) | `build_call_shim(..., Some(Deref { MutPtr }), Direct(def_id))` (`shim.rs:36-39`) | `true` | `TRACK_CALLER` on `def_id` (`true` in `c7d5...`, `false` in `1421...`) | `- shim(vtable)` |
| 2 | `Reify(DefId, Option<ReifyReason>)` | `resolve_for_fn_ptr` & `expect_resolve_for_vtable` (`#[track_caller]`, `Virtual` fn-ptr, KCFI) | `build_call_shim(..., None, Direct(def_id))` (`shim.rs:60-62`) | `true` | `false` | `- shim(reify)` / `- shim(reify-fnptr)` / `- shim(reify-vtable)` |
| 3 | `FnPtr(DefId, Ty<'tcx>)` | `resolve_associated_item` (`<fn(...) as Fn/FnMut/FnOnce>::call*`) | `build_call_shim(..., Some(Identity \| Deref), Indirect(ty))` (`shim.rs:40-54`) | `false` | `false` | `- shim(fn(...) -> ...)` |
| 4 | `ClosureOnce { call_once, closure, track_caller }` | `Instance::resolve_closure` -> `fn_once_adapter_instance` (`Fn`/`FnMut` closure called as `FnOnce`) | `build_call_shim(..., Some(RefMut), Direct(call_mut))` (`shim.rs:63-73`) | `true` | `track_caller` | `- shim` (no parentheses) |
| 5 | `ConstructCoroutineInClosure { coroutine_closure_def_id, receiver_by_ref }` | `resolve_associated_item` (`AsyncFn`/`Fn` coroutine-closure by-move adapter) | `build_construct_coroutine_by_move_shim` (`shim.rs:75-77, 1222-1332`) | `true` | `false` | `- shim(by-move)` / `- shim` |
| 6 | `ThreadLocal(DefId)` | Platform thread-local dylib export accessor | `build_thread_local_shim` (`shim.rs:127, 484-509`) | `false` | `false` | internal thread-local accessor (panics if reified in `collector.rs:1051-1053`) |
| 7 | `FutureDropPoll(DefId, Ty<'tcx>, Ty<'tcx>)` | `resolve_async_drop_poll` (`instance.rs:414-427`) | `build_future_drop_poll_shim` (`shim.rs:131-148`) | `false` | `false` | `- shim(...)` |
| 8 | `DropGlue(DefId, Option<Ty<'tcx>>)` | `Instance::resolve_drop_glue` -> `resolve_instance_raw` (`LangItem::DropGlue`) | Coroutine drop clone (`shim.rs:82-123`) or `build_drop_shim` (`shim.rs:125, 258-372`) | `false` for `Some(T)`; `true` for `None` | `false` | `- shim(Some(T))` / `- shim(None)` |
| 9 | `Clone(DefId, Ty<'tcx>)` | `resolve_associated_item` (`BuiltinImplSource` for `LangItem::Clone`) | `build_clone_shim` (`shim.rs:128, 512-535`) | `false` | `false` | `- shim(T)` |
| 10 | `FnAddrAsPtr(DefId, Ty<'tcx>)` | `resolve_associated_item` (`LangItem::FnAddrAsPtr`; `FnPtrAddrShim` in `1.98.0-nightly`) | `build_fn_addr_as_ptr_shim` (`shim.rs:129, 1100-1185`) | `false` | `false` | `- shim(fn(...) -> ...)` |
| 11 | `FnPtrFromPtr(DefId, Ty<'tcx>)` | `resolve_associated_item` (`LangItem::FnPtrFromPtr`) | `build_fn_ptr_from_ptr_shim` (`shim.rs:130, 1187-1220`) | `false` | `false` | `- shim(fn(...) -> ...)` |
| 12 | `AsyncDropGlueCtor(DefId, Ty<'tcx>)` | `Instance::resolve_async_drop_in_place` (`LangItem::AsyncDropInPlace`) | `build_async_destructor_ctor_shim` (`shim.rs:172-176`, `async_destructor_ctor.rs:17-42`) | `false` | `false` | `- shim(T)` |
| 13 | `AsyncDropGlue(DefId, Ty<'tcx>)` | `resolve_instance_raw` (`is_async_drop_in_place_coroutine`) | `build_async_drop_shim` (`shim.rs:149-170`, `async_destructor_ctor.rs:46-166`) | `false` | `false` | `- shim(T)` |

Two primary-source subtleties in this table require explicit care from MIR verification tools:

1. **Stale upstream doc-comment on `ShimKind::Clone` regarding arrays and `Copy` primitives (`Basis: source + execution`):**
   `compiler/rustc_middle/src/ty/instance.rs:174-175` states: *"For all types that automatically implement `Copy`, a trivial `Clone` impl is provided too. Additionally, arrays, tuples, and closures get a `Clone` shim even if they aren't `Copy`."* Direct inspection of `resolve_associated_item` (`compiler/rustc_ty_utils/src/instance.rs:273-290`) and `build_clone_shim` (`compiler/rustc_mir_transform/src/shim.rs:520-532`) refutes this doc-comment for arrays and primitives:
   - `resolve_associated_item` constructs `ShimKind::Clone` **exclusively** when `BuiltinImplSource` matches `ty::FnDef | ty::FnPtr | ty::Coroutine | ty::CoroutineWitness | ty::Closure | ty::CoroutineClosure | ty::Tuple`.
   - `build_clone_shim` panics (`bug!("clone shim for {:?} which is not Copy and is not an aggregate", self_ty)`) on any `TyKind` outside `FnDef`, `FnPtr`, `Closure`, `CoroutineClosure`, `Tuple`, and `Coroutine`.
   - Fixed-size arrays `[T; N]` use a normal `ImplSource::UserDefined` library implementation in `core::array` (`<[T; N] as Clone>::clone` -> `<T as SpecArrayClone>::clone::<N>` -> `array::try_from_fn` guarded by `core::array::Guard<'_, T>`). Our probe confirms that cloning `[NeedsDrop; 2]` emits `MONO_ITEM fn <NeedsDrop as std::array::SpecArrayClone>::clone::<2>` (`InstanceKind::Item`) plus `MONO_ITEM fn std::ptr::drop_glue::<std::array::Guard<'_, NeedsDrop>> - shim(Some(std::array::Guard<'_, NeedsDrop>))` (`ShimKind::DropGlue`), and **zero** `ShimKind::Clone` bodies for `[NeedsDrop; 2]`.
2. **Pre-substituted vs. polymorphic shim MIR (`has_polymorphic_mir_body`, `Basis: source + execution`):**
   `Instance::args_for_mir_body` (`instance.rs:857-859` in `14210df0e2...`) returns `self.def.has_polymorphic_mir_body().then_some(self.args)`. When a MIR consumer calls `tcx.instance_mir(instance.def)`:
   - For the 5 `true` cases (`VTable`, `Reify`, `ClosureOnce`, `ConstructCoroutineInClosure`, and empty `DropGlue(_, None)`), the returned `Body<'tcx>` still contains uninstantiated generic parameters (`Self`, `Args`, or item type parameters) and **must** be substituted with `instance.args` via `instance.instantiate_mir_and_normalize_erasing_regions(...)`.
   - For the 9 `false` cases (`Clone`, `FnPtr`, `FnAddrAsPtr`, `FnPtrFromPtr`, `DropGlue(_, Some(T))`, `ThreadLocal`, `FutureDropPoll`, `AsyncDropGlue`, `AsyncDropGlueCtor`), `make_shim` has **already** instantiated the concrete monomorphic types directly into `LocalDecls` and `TerminatorKind` operands. Re-substituting `instance.args` onto those bodies is erroneous because any residual generic parameters would belong to an enclosing caller scope (`instance.rs:905-910`), so `Instance::instantiate_mir` applies `instantiate_identity()` instead!

### 3.2 Query Routing Divergence: `tcx.mir_keys(())`, `MonoItem::is_user_defined()`, and `TyCtxt::instance_mir`

`Basis: source + execution`

A naive MIR extractor typically enumerates crate bodies via `tcx.mir_keys(())` (the exact query backing `rustc --emit=mir` and `encode_mir` in `rustc_metadata/src/rmeta/encoder.rs:1946`). Inspection of `compiler/rustc_mir_transform/src/lib.rs:331-362` (`c7d5ba59d8e11ee2e2204b173458eec4cb41c973`) shows why `mir_keys` is strictly a local syntax-owner index rather than a compiled code inventory:

```rust
// rust-lang/rust @ c7d5ba59d8e11ee2e2204b173458eec4cb41c973
// compiler/rustc_mir_transform/src/lib.rs:331-362
fn mir_keys(tcx: TyCtxt<'_>, (): ()) -> FxIndexSet<LocalDefId> {
    let mut set: FxIndexSet<_> = tcx.hir_body_owners().collect();
    set.retain(|&def_id| !matches!(tcx.def_kind(def_id), DefKind::GlobalAsm));

    for body_owner in tcx.hir_body_owners() {
        if let DefKind::Closure = tcx.def_kind(body_owner)
            && tcx.needs_coroutine_by_move_body_def_id(body_owner.to_def_id())
        {
            set.insert(tcx.coroutine_by_move_body_def_id(body_owner).expect_local());
        }
    }

    for item in tcx.hir_crate_items(()).free_items() {
        if let DefKind::Struct | DefKind::Enum = tcx.def_kind(item.owner_id) {
            for variant in tcx.adt_def(item.owner_id).variants() {
                if let Some((CtorKind::Fn, ctor_def_id)) = variant.ctor {
                    set.insert(ctor_def_id.expect_local());
                }
            }
        }
    }
    set
}
```

Every `DefId` in `mir_keys` is a `LocalDefId` (`LOCAL_CRATE`). Consequently, `tcx.mir_keys(())` cannot represent:
- Multiple monomorphic instantiations of a local generic function (`invoke_fn_ref::<fn(u32, u64) -> u64>` vs. `invoke_fn_ref::<OtherClosure>`);
- Any `DefId` in an upstream crate (`core`, `alloc`, `std`, or Cargo dependencies), even when `should_codegen_locally` (`collector.rs:1083-1127`) compiles its monomorphized machine code directly into the current crate's object file;
- Any of the 13 `ShimKind` variants, none of which possess their own `DefId` (`ShimKind::def_id()` borrows the underlying lang-item or target `DefId`, such as `core::ptr::drop_glue` or `core::clone::Clone::clone`, `instance.rs:341-360`).

A second trap affects tools that inspect `-Zdump-mono-stats`: in `compiler/rustc_monomorphize/src/partitioning.rs:1298-1306`, `dump_mono_items_stats` explicitly discards every compiler-synthesized shim via `.filter(|mono_item| mono_item.is_user_defined())`, where `MonoItem::is_user_defined` (`compiler/rustc_middle/src/mono.rs:97-102`) is:

```rust
pub fn is_user_defined(&self) -> bool {
    match *self {
        MonoItem::Fn(instance) => matches!(instance.def, InstanceKind::Item(..)),
        MonoItem::Static(..) | MonoItem::GlobalAsm(..) => true,
    }
}
```

Even among `InstanceKind::Item(def)` entries, **calling `tcx.optimized_mir(def)` directly is not total across reachable `MonoItem::Fn` instances** because of tuple struct and tuple enum-variant constructors (`DefKind::Ctor(_, CtorKind::Fn)`):

- **Local constructors:** Tuple constructors (`pub struct LocalTupleCtor(pub u32, pub u64);`, reified via `let f: fn(u32, u64) -> LocalTupleCtor = LocalTupleCtor;`) have no HIR `BodyId`; `mir_promoted` explicitly asserts `debug_assert!(!tcx.is_constructor(def.to_def_id()))` (`lib.rs:441`). Both `optimized_mir` (`lib.rs:793-799`) and `inner_mir_for_ctfe` (`lib.rs:507-513`) short-circuit to `shim::build_adt_ctor(tcx, def.to_def_id())` (`shim.rs:1011-1091`), emitting a 1-block `Rvalue::Aggregate` body (`_0 = LocalTupleCtor(move _1, move _2); return;`)—which is why `--emit=mir` prints every local tuple constructor **twice** (once for its `optimized_mir` delegation and once under `// MIR FOR CTFE`, accounting for `5 * 2 = 10` of the `25` headers in `shim_probe.mir`).
- **Foreign constructors (`dep_generics::GenericPair`, `core::option::Option::Some`):** In `compiler/rustc_metadata/src/rmeta/encoder.rs:1183-1184`, `should_encode_mir` returns `(encode_const = true, encode_opt = false)` for `DefKind::Ctor(_, _)`, with the explicit comment `// instance_mir uses mir_for_ctfe rather than optimized_mir for constructors`. Consequently, an upstream `.rmeta` file stores foreign constructor MIR **only** in its `mir_for_ctfe` table: `tcx.is_mir_available(foreign_ctor_def_id)` returns `false` (`cstore_impl.rs:332`, necessitating the `!matches!(tcx.def_kind(def_id), DefKind::Ctor(..))` exemption in `should_codegen_locally` at `collector.rs:1118`), and calling `tcx.optimized_mir(foreign_ctor_def_id)` fails on the missing `optimized_mir` metadata table entry.

`TyCtxt::instance_mir` (`compiler/rustc_middle/src/ty/mod.rs:1996-2035`) resolves every one of these cases uniformly:

```rust
// rust-lang/rust @ c7d5ba59d8e11ee2e2204b173458eec4cb41c973
// compiler/rustc_middle/src/ty/mod.rs:1996-2026
pub fn instance_mir(self, instance: ty::InstanceKind<'tcx>) -> &'tcx Body<'tcx> {
    let body = match instance {
        ty::InstanceKind::Item(def) => {
            let def_kind = self.def_kind(def);
            match def_kind {
                DefKind::Const
                | DefKind::Static { .. }
                | DefKind::AssocConst
                | DefKind::Ctor(..)
                | DefKind::AnonConst => self.mir_for_ctfe(def),
                DefKind::Fn | DefKind::AssocFn
                    if matches!(self.constness(def), hir::Constness::Const { always: true }) =>
                {
                    self.mir_for_ctfe(def)
                }
                _ => self.optimized_mir(def),
            }
        }
        ty::InstanceKind::Intrinsic(..) | ty::InstanceKind::LlvmIntrinsic(..) => {
            bug!("intrinsics have no instance MIR")
        }
        ty::InstanceKind::Virtual(..) => bug!("virtual dispatches have no instance MIR"),
        ty::InstanceKind::Shim(shim) => self.mir_shims(shim),
    };
    // Asserts `matches!(body.phase, MirPhase::Runtime(_))`
    body
}
```

### 3.3 Pass-Pipeline Divergence in `make_shim` and the `-Zdump-mir` Stem-Collision Hazard

`Basis: source + execution`

Although `TyCtxt::instance_mir` asserts `matches!(body.phase, MirPhase::Runtime(_))` on all returned bodies (`ty/mod.rs:2028-2032`), bodies returned via `optimized_mir`, `mir_for_ctfe` (`build_adt_ctor`), and `mir_shims` (`make_shim`) have undergone radically different MIR transformation pipelines:

| Pipeline Path | Governing Entry (`rustc_mir_transform`) | Borrowck & `ElaborateDrops`? | `MirValidator` Run? | Runtime UB Check Insertion (`CheckAlignment` / `CheckNull` / `CheckEnums`)? | MIR Optimizations (`RemoveStorageMarkers`, `GVN`, `CopyProp`, `DSE`)? | Observed `-Zdump-mir=all` File Count |
| :--- | :--- | :--- | :--- | :--- | :--- | ---: |
| Standard `Item` (`optimized_mir`) | `mir_built` -> `mir_promoted` -> `mir_drops_elaborated_and_const_checked` -> `inner_optimized_mir` (`lib.rs:395-838`) | **Yes** (`mir_borrowck` + `ElaborateDrops`) | **Yes** (when `-Zvalidate-mir` enabled, except `run_runtime_lowering_passes`) | **Yes** (`lib.rs:711-713`, before `Inline`) | **Yes** (full `run_optimization_passes` list, `lib.rs:700-789`) | `96` (`plain_two_arg`) |
| Standard `Shim` (`VTable`, `FnPtr`, `Reify`, `ClosureOnce`, `ConstructCoroutineInClosure`, non-coroutine `DropGlue`, `ThreadLocal`, `Clone`, `FnAddrAsPtr`, `FnPtrFromPtr`) | `make_shim` fallthrough -> `deref_finder` -> `pm::run_passes_no_validate` (`shim.rs:180-201`) | **No** (ladders emitted pre-elaborated; `new_body` sets `Runtime(Initial)`, `shim.rs:406`) | **No** (`run_passes_no_validate`, `shim.rs:186`, avoiding TAIT `PostAnalysis` param-env errors) | **No** (skips `run_optimization_passes` entirely; stamps `Runtime(Optimized)` directly) | **No** (runs only `MentionedItems`, `AddMovesForPackedDrops`, `RemoveNoopLandingPads`, `SimplifyCfg::MakeShim`, `InstSimplify::BeforeInline`, `ForceInline`, `AbortUnwindingCalls`, `CriticalCallEdges`) | `17` (`core.clone-Clone-clone`) |
| Coroutine `DropGlue` (`ty::Coroutine`) | `make_shim` early return cloning `optimized_mir(coro).coroutine_drop()` (`shim.rs:82-123`) | Inherited from parent coroutine's `StateTransform` | Standard `run_passes` | Inherited if any | Runs only `MentionedItems`, `AbortUnwindingCalls`, `CriticalCallEdges` | `7` |
| `FutureDropPoll` | `make_shim` early return (`shim.rs:131-148`) | Clones `future_drop_poll()` | Standard `run_passes` | **Yes** (calls `run_optimization_passes` at `shim.rs:145`) | **Yes** (`run_optimization_passes`) | Full optimization tail |
| `AsyncDropGlue` | `make_shim` early return (`shim.rs:149-170`) | `DropShimElaborator { produce_async_drops: true }` + `StateTransform` | `run_passes_no_validate` for lowering, then `run_passes` | **Yes** (calls `run_optimization_passes` at `shim.rs:167`) | **Yes** (`run_optimization_passes`) | Lowering + optimization tail |
| `AsyncDropGlueCtor` | `build_async_destructor_ctor_shim` (`async_destructor_ctor.rs:17-42`) | Clones `optimized_mir(async_drop_in_place)` | Standard `run_passes` | Inherited from `async_drop_in_place` | Runs `SimplifyCfg::MakeShim`, `AbortUnwindingCalls`, `CriticalCallEdges` | `7` |
| Tuple `DefKind::Ctor` | `build_adt_ctor` (`shim.rs:1011-1091`) | **No** | **No** (`run_passes_no_validate` with `&[]`) | **No** | **No** (`0` passes; stamps `Runtime(Optimized)`) | `1` (`built.after.mir` only) |

Three operational consequences follow directly from this pipeline divergence:

1. **Absence of `StorageLive`/`StorageDead` and runtime pointer-check assertions in standard shims:** `new_body` (`shim.rs:374-408`) creates temporaries in `local_decls` without `StorageLive` or `StorageDead` statements, and because standard shims skip `run_optimization_passes`, `CheckAlignment` and `CheckNull` never execute on shim pointer dereferences. For example, in `ShimKind::VTable`, `ByValueDyn::consume_val(_1: *mut Self, _2: u32)` executes `move (*_1)` directly without an explicit MIR `AssertKind::MisalignedPointerDereference` or `NullPointerDereference` terminator (`mir_shims_and_completeness_probe.json`, `shim_probe.ByValueDyn-consume_val.3-3-000.runtime-optimized.after.mir`). A verified MIR interpreter or translation validator must therefore treat raw-pointer dereference preconditions on `VTable` shims at the `Rvalue`/`Operand` dereference semantics rather than relying on `CheckNull`/`CheckAlignment` MIR assertions.
2. **Retention of unelaborated `TerminatorKind::Drop` oncontained fields:** Unlike `ElaborateDrops` inside `mir_drops_elaborated_and_const_checked`—which only elaborates `Open` drops when local move-path analysis requires per-field drop flags—`DropShimElaborator::drop_style` (`shim.rs:447-460`) returns `DropStyle::Open` at the root (`DropFlagMode::Deep`) and `DropStyle::Static` for contained fields (`DropFlagMode::Shallow`). Consequently, finalized `Runtime(Optimized)` shim MIR retains `TerminatorKind::Drop { place: ((* _1).i: FieldTy), ... }` terminators (as well as `TerminatorKind::Drop { place: (_0.i), ... }` in `Clone` cleanup blocks and `drop(_1)` in `ClosureOnce` blocks). Any MIR consumer whose operational semantics marks `TerminatorKind::Drop` as `.unsupported` on the assumption that `ElaborateDrops` eliminated all `Drop` terminators will fail on `DropGlue`, `Clone`, and `ClosureOnce` shims (`Trusted/MirAst.lean:782-784`).
3. **The `-Zdump-mir` filename-stem overwrite hazard (verified empirically):** In `shim_probe`, `tracked_standalone` is compiled both as `InstanceKind::Item(tracked_standalone)` (`96` pass snapshots) and—because it is coerced to `fn(u32) -> (u32, u32)`—as `InstanceKind::ReifyShim(tracked_standalone, None)` (`17` pass snapshots). Both instances share `source.def_id() == tracked_standalone`, so `MirDumper` writes both pass streams to `shim_probe.tracked_standalone.*`. Because `make_shim` runs during monomorphization collection *after* `optimized_mir(tracked_standalone)` completes, `make_shim`'s final phase-change dump overwrites `shim_probe.tracked_standalone.3-3-000.runtime-optimized.after.mir` on disk (leaving `96 + 17 - 1 = 112` files), replacing the real 5-block body of `tracked_standalone` with the 2-block `Reify` wrapper:

```text
// shim_probe.tracked_standalone.3-3-000.runtime-optimized.after.mir (clobbered on disk by make_shim!)
fn tracked_standalone(_1: u32) -> (u32, u32) {
    let mut _0: (u32, u32);

    bb0: {
        _0 = tracked_standalone(move _1) -> [return: bb1, unwind continue];
    }

    bb1: {
        return;
    }
}
```

Any offline verification pipeline that reads `*.runtime-optimized.after.mir` files from `-Zdump-mir-dir` misinterprets every reified `#[track_caller]` function as an unconditional 2-block self-recursive loop. In-process extraction through `TyCtxt::instance_mir` keyed by the full `Instance<'tcx>` avoids this collision completely.

### 3.4 Pre-Elaborated Unwind Ladders: `DropGlue` vs. `Clone` Shim Synthesis

`Basis: source + execution`

`ShimKind::DropGlue` and `ShimKind::Clone` synthesize dual unwind cleanup ladders with opposite traversal directions determined by which fields own live resources at each program point.

#### 3.4.1 `DropGlue` (`build_drop_shim` and `elaborate_drop::drop_ladder`)

In `build_drop_shim` (`compiler/rustc_mir_transform/src/shim.rs:258-372`), three structural cases arise for `DropGlue(def_id, Some(ty))`:

1. **Fixed-size arrays `ty::Array(ety, len)` (`shim.rs:306-345`):** Rather than generating an `N`-block unrolled field ladder for every array length `N`, `build_drop_shim` unsizes `_1: &mut [ety; N]` into `_2: &mut [ety]` via `CastKind::PointerCoercion(PointerCoercion::Unsize, Implicit)` and emits a direct `TerminatorKind::Call` to `core::ptr::drop_glue::<[ety]>(move _2)`:
   ```text
   // core.ptr-drop_glue.[NeedsDrop;2].1-1-003.SimplifyCfg-make_shim.after.mir
   fn std::ptr::drop_glue(_1: &mut [NeedsDrop; 2]) -> () {
       let mut _0: ();
       let mut _2: &mut [NeedsDrop];
       bb0: {
           _2 = move _1 as &mut [NeedsDrop] (PointerCoercion(Unsize, Implicit));
           _0 = std::ptr::drop_glue::<[NeedsDrop]>(move _2) -> [return: bb1, unwind continue];
       }
       bb1: { return; }
   }
   ```
2. **ADTs without custom `Drop` (`CompositeDrop3(NeedsDrop, NeedsDrop, NeedsDrop)`):** `DropCtxt::drop_ladder` (`compiler/rustc_mir_transform/src/elaborate_drop.rs:881-965`) constructs two coupled forward-order half-ladders over fields needing drop (`should_retain_for_ladder`, `elaborate_drop.rs:867-877`). Before `SimplifyCfg::MakeShim`, `drop_halfladder` emits an unreachable cleanup head block (`bb6 (cleanup)` dropping `(*_1).0`); `SimplifyCfg::MakeShim` eliminates `bb6` and empty `goto` blocks (`bb0`, `bb3`), leaving the minimal 7-block ladder (`3` mainline drops + `2` cleanup drops + `return` + `resume`):
   ```text
   // core.ptr-drop_glue.CompositeDrop3.1-1-003.SimplifyCfg-make_shim.after.mir
   fn std::ptr::drop_glue(_1: &mut CompositeDrop3) -> () {
       let mut _0: ();
       bb0: { drop(((*_1).0: NeedsDrop)) -> [return: bb6, unwind: bb4]; }
       bb1 (cleanup): { resume; }
       bb2: { return; }
       bb3 (cleanup): { drop(((*_1).2: NeedsDrop)) -> [return: bb1, unwind terminate(cleanup)]; }
       bb4 (cleanup): { drop(((*_1).1: NeedsDrop)) -> [return: bb3, unwind terminate(cleanup)]; }
       bb5: { drop(((*_1).2: NeedsDrop)) -> [return: bb2, unwind continue]; }
       bb6: { drop(((*_1).1: NeedsDrop)) -> [return: bb5, unwind: bb3]; }
   }
   ```
   When `drop((*_1).0)` panics at `bb0`, control transfers to `bb4 -> bb3 -> bb1 (resume)`, dropping `(*_1).1` and `(*_1).2` in **forward** declaration order with `unwind terminate(cleanup)` (`UnwindTerminateReason::InCleanup`, aborting the process if a second destructor panics while already unwinding).
3. **ADTs with custom `Drop` (`CustomPlusFieldsDrop(NeedsDrop, NeedsDrop)`, `elaborate_drop.rs:1035-1048`):** `open_drop_for_adt` emits `<CustomPlusFieldsDrop as Drop>::drop(&mut (*_1))` **first**, wiring its normal target to the mainline field drop ladder (`bb6 -> bb5 -> bb2`) and its **unwind** target directly to the full field cleanup ladder (`bb4 -> bb3 -> bb1`), guaranteeing that all contained fields are still destroyed even when `CustomPlusFieldsDrop::drop` panics:
   ```text
   // core.ptr-drop_glue.CustomPlusFieldsDrop.1-1-003.SimplifyCfg-make_shim.after.mir
   fn std::ptr::drop_glue(_1: &mut CustomPlusFieldsDrop) -> () {
       let mut _0: ();
       let mut _2: &mut CustomPlusFieldsDrop;
       let mut _3: ();
       bb0: {
           _2 = &mut (*_1);
           _3 = <CustomPlusFieldsDrop as Drop>::drop(move _2) -> [return: bb6, unwind: bb4];
       }
       bb1 (cleanup): { resume; }
       bb2: { return; }
       bb3 (cleanup): { drop(((*_1).1: NeedsDrop)) -> [return: bb1, unwind terminate(cleanup)]; }
       bb4 (cleanup): { drop(((*_1).0: NeedsDrop)) -> [return: bb3, unwind terminate(cleanup)]; }
       bb5: { drop(((*_1).1: NeedsDrop)) -> [return: bb2, unwind continue]; }
       bb6: { drop(((*_1).0: NeedsDrop)) -> [return: bb5, unwind: bb3]; }
   }
   ```

#### 3.4.2 `Clone` (`CloneShimBuilder::clone_fields`)

In `CloneShimBuilder::clone_fields` (`compiler/rustc_mir_transform/src/shim.rs:662-709`), the return place `_0` begins completely uninitialized. For a tuple of length $n$, `clone_fields` allocates $2n + 1$ blocks (plus `entry`, `resume`, and `return`), threading the `unwind` target **backward**:
- Iteration $i = 0$ clones `(*_1).0` into `_0.0` with `unwind: bb_resume` (which `RemoveNoopLandingPads` simplifies to `unwind continue`), and creates `bb_cleanup_0` (`drop(_0.0) -> [return: bb_resume, unwind terminate(cleanup)]`).
- Iteration $i = k$ ($k \ge 1$) clones `(*_1).k` into `_0.k` with `unwind: bb_cleanup_{k-1}`, and creates `bb_cleanup_k` (`drop(_0.k) -> [return: bb_cleanup_{k-1}, unwind terminate(cleanup)]`).
- The final cleanup block `bb_cleanup_{n-1}` (`bb8` in `SimplifyCfg-make_shim.before.mir` for `(NeedsDrop, NeedsDrop, u64)`) has zero incoming edges in a tuple shim (though in `coroutine_shim`, `shim.rs:741`, the upvar `unwind` block IS threaded into variant state-field cloning!) and is pruned by `SimplifyCfg::MakeShim`; subsequently, `InstSimplify::BeforeInline` + `ForceInline` inlines `<u64 as Clone>::clone` into `_0.2 = copy (*_4)` (`core.clone-Clone-clone.3-3-000.runtime-optimized.after.mir`), eliminating the unwind edge into `bb5 (drop(_0.1))` because copying `u64` cannot unwind:

```text
// core.clone-Clone-clone.1-1-003.SimplifyCfg-make_shim.after.mir
fn clone(_1: &(NeedsDrop, NeedsDrop, u64)) -> (NeedsDrop, NeedsDrop, u64) {
    let mut _0: (NeedsDrop, NeedsDrop, u64);
    let _2: &NeedsDrop;
    let _3: &NeedsDrop;
    let _4: &u64;
    bb0: {
        _2 = &((*_1).0: NeedsDrop);
        (_0.0: NeedsDrop) = <NeedsDrop as Clone>::clone(move _2) -> [return: bb4, unwind continue];
    }
    bb1 (cleanup): { resume; }
    bb2: { return; }
    bb3 (cleanup): { drop((_0.0: NeedsDrop)) -> [return: bb1, unwind terminate(cleanup)]; }
    bb4: {
        _3 = &((*_1).1: NeedsDrop);
        (_0.1: NeedsDrop) = <NeedsDrop as Clone>::clone(move _3) -> [return: bb6, unwind: bb3];
    }
    bb5 (cleanup): { drop((_0.1: NeedsDrop)) -> [return: bb3, unwind terminate(cleanup)]; }
    bb6: {
        _4 = &((*_1).2: u64);
        (_0.2: u64) = <u64 as Clone>::clone(move _4) -> [return: bb2, unwind: bb5];
    }
}
```

Executing `shim_probe` on `(NeedsDrop(50), NeedsDrop(999), 7_u64)` confirms this cleanup semantics at runtime (`mir_shims_and_completeness_probe.json`, `runtime_execution_verification`): field `0` clones `NeedsDrop(50)` into `_0.0 = NeedsDrop(60)`, field `1` panics inside `<NeedsDrop as Clone>::clone`, `bb3 (cleanup)` drops `_0.0` (`DROP_LOG` increments by `60 + 100 = 160` before `catch_unwind` returns, while `failing_tuple` itself is still live), and neither the failed field `_0.1` nor the unreached field `_0.2` is touched.

### 3.5 Call-Adapter Shims: `Reify` (`#[track_caller]` & KCFI), `VTable`, `FnPtr`, and `ClosureOnce`

`Basis: source + execution`

All four call-adapter shims delegate to `build_call_shim` (`compiler/rustc_mir_transform/src/shim.rs:781-1009`), parameterized by `rcvr_adjustment: Option<Adjustment>` and `call_kind: CallKind<'tcx>`:

1. **How `ShimKind::Reify` injects `&'static core::panic::Location<'static>` without a MIR local (`instance.rs:306-320`, `abi.rs:272-275`, `block.rs:1438-1467`):**
   In MIR dumps, `Reify(tracked_standalone)` appears identical to an identity wrapper (`_0 = tracked_standalone(move _1)`), with **no** `&Location` local in `local_decls`. Primary-source inspection across `rustc_middle`, `rustc_ty_utils`, and `rustc_codegen_ssa` reveals the exact cross-layer mechanism:
   - `InstanceKind::requires_caller_location` (`instance.rs:306-320`) returns `true` for `InstanceKind::Item(tracked_standalone)` (because its `CodegenFnAttrFlags` carries `TRACK_CALLER`), so `FnAbiDesc::for_instance` (`compiler/rustc_ty_utils/src/abi.rs:272-275`) appends `tcx.caller_location_ty()` (`&'static Location<'static>`) as an extra trailing ABI parameter (`fn_abi.args.len() == mir_args + 1`).
   - Conversely, `InstanceKind::requires_caller_location` returns **`false`** for `InstanceKind::Shim(ShimKind::Reify(..))` (`_ => false` at `instance.rs:318`). Thus the `Reify` shim's `FnAbi` has **exact `fn(u32) -> (u32, u32)` ABI arity** (`1` parameter, matching untagged `fn` pointers and untagged trait vtable slots).
   - Inside `build_call_shim` (`shim.rs:853, 959`), the `Reify` shim's `TerminatorKind::Call` targets `CallKind::Direct(def_id)` (`InstanceKind::Item(tracked_standalone)`) with `source_info = SourceInfo::outermost(tcx.def_span(def_id))`—the **definition span** of `tracked_standalone`.
   - When `codegen_call_terminator` (`compiler/rustc_codegen_ssa/src/mir/block.rs:1438-1467`) lowers that direct `Call` inside the `Reify` shim, `instance.def.requires_caller_location(tcx)` evaluates to `true`, asserting `fn_abi.args.len() == mir_args + 1` and passing `self.get_caller_location(bx, source_info)` (materialized at `def_span(tracked_standalone)`) as the trailing LLVM argument!
   - LLVM IR emitted by `shim_probe` (`mir_shims_and_completeness_probe.json`, `llvm_ir_track_caller_vs_reify_blocks`) confirms the exact ABI split:
     ```llvm
     ; Direct item takes 2 ABI args (i32 %x, ptr align 8 %0):
     define internal { i32, i32 } @_RNvCs..._10shim_probe18tracked_standalone(i32 %x, ptr align 8 %0)
     ; Reify shim takes 1 ABI arg (i32 %_1) and supplies static @alloc_af1e039d... (line 82):
     define internal { i32, i32 } @_RNSNvCs..._10shim_probe18tracked_standalone5reifyB3_(i32 %_1) {
     start:
       %0 = call { i32, i32 } @_RNvCs..._10shim_probe18tracked_standalone(i32 %_1, ptr align 8 @alloc_af1e039d0301e5fff9172ae228d37a0a)
     ```
   - Runtime execution of `shim_probe` confirms that `tracked_standalone(1)` called directly at line `189` returns `direct_line = 189`, whereas `(tracked_standalone as fn(u32) -> (u32, u32))(1)` returns `reified_fn_ptr_line = 82` (the definition of `tracked_standalone`). Likewise, calling `recv.act(1)` directly at line `194` returns `direct_trait_line = 194`, whereas `(&recv as &dyn UntrackedAction).act(1)` dispatches through `<TrackedReceiver as UntrackedAction>::act - shim(reify)` and returns `reified_vtable_line = 61` (the `impl` method definition).
   - Under `-Zsanitizer=kcfi` (`kcfi_reify_probe.rs`), taking both a `&dyn DynAction` vtable and a `fn(&Actor, u32) -> u32` pointer for the same `#[track_caller]` method `<Actor as DynAction>::step` emits **two distinct `MonoItem::Fn` instances** (`MONO_ITEM fn <Actor as DynAction>::step - shim(reify-fnptr)` and `MONO_ITEM fn <Actor as DynAction>::step - shim(reify-vtable)`) so KCFI can attach distinct type-hash prefixes to the function pointer and the vtable entry.
2. **`ShimKind::VTable` (`unsized_fn_params` by-value `Self`):** Rewrites `sig.inputs_and_output[0]` from `Self` to `*mut Self` (`shim.rs:844-851`) and dereferences `move (*_1)` into `<Self as ByValueDyn>::consume_val(move (*_1), move _2)`.
3. **`ShimKind::FnPtr` (tuple-argument unpacking + `ExternAbi::RustCall`):** Instantiates `Fn`/`FnMut`/`FnOnce` with `[fnty, Tuple(inputs)]`, sets `body.spread_arg = Some(Local::new(sig.inputs().len()))` (`shim.rs:1004-1006`), dereferences `&fn(...)` / `&mut fn(...)` when called via `Fn::call` / `FnMut::call_mut`, and unpacks the tuple argument local element-by-element:
   ```text
   // core.ops-function-Fn-call.1-1-003.SimplifyCfg-make_shim.after.mir
   fn call(_1: &fn(u32, u64) -> u64, _2: (u32, u64)) -> <fn(u32, u64) -> u64 as FnOnce<(u32, u64)>>::Output {
       let mut _0: <fn(u32, u64) -> u64 as std::ops::FnOnce<(u32, u64)>>::Output;
       bb0: { _0 = move (*_1)(move (_2.0: u32), move (_2.1: u64)) -> [return: bb1, unwind continue]; }
       bb1: { return; }
   }
   ```
4. **`ShimKind::ClosureOnce` (`Adjustment::RefMut` 5-block owned-upvar destruction):** When an `Fn` or `FnMut` closure (whose body takes `&self` or `&mut self` and therefore does *not* consume captured upvars) is invoked through `FnOnce::call_once(self, args)`, `build_call_shim` (`shim.rs:871-890, 953-999`) borrows `_3 = &mut _1`, calls `<Self as FnMut<Args>>::call_mut(move _3, move _2) -> [return: bb1, unwind: bb3]`, and emits `drop(_1)` on **both** the normal return block (`bb1 -> bb2: return`) and the cleanup landing pad (`bb3 (cleanup) -> bb4 (cleanup): resume`), ensuring owned upvars (such as `OwnedHandle` in `closure_once_iso`) are destroyed whether the closure returns or panics.

### 3.6 Empirical Monomorphization Census and Whole-Crate Completeness Gap

`Basis: execution + derived`

Running `support/probe_mir_shims_and_completeness.py` on `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) quantifies the exact completeness gap across `tcx.mir_keys(())`, `-Zdump-mono-stats`, and `collect_and_partition_mono_items` (`-Zprint-mono-items=yes`):

| Metric / `MonoItem` Partition | `shim_probe` + `dep_generics` (`mir_shims_and_completeness_probe.json`) | Share of Executable `MonoItem::Fn` (`N = 92`) | Included in `tcx.mir_keys(())` (`--emit=mir`)? | Included in `-Zdump-mono-stats` (`is_user_defined`)? | Included in `collect_and_partition_mono_items` + `instance_mir`? |
| :--- | ---: | ---: | :--- | :--- | :--- |
| Local HIR function & closure instances (`item_local_hir_body`) | `15` | `16.30%` | **Yes** (unmonomorphized templates) | **Yes** | **Yes** |
| Local tuple struct `DefKind::Ctor` (`LocalTupleCtor`) | `1` | `1.09%` | **Yes** (`build_adt_ctor`) | **Yes** | **Yes** (`mir_for_ctfe`) |
| **Subtotal: Reachable `mir_keys` `MonoItem::Fn`s** | **`16`** | **`17.39%`** | **Yes** | **Yes** | **Yes** |
| Cross-crate generic & `#[inline]` `Item`s (`core`, `alloc`, `std`, `dep_generics`) | `52` | `56.52%` | **No** (`0%`) | **Yes** | **Yes** (`optimized_mir`) |
| Foreign `DefKind::Ctor` (`dep_generics::GenericPair::<u32, u64>`) | `1` | `1.09%` | **No** (`0%`) | **Yes** | **Yes** (`mir_for_ctfe` only!) |
| `ShimKind::DropGlue` (`CompositeDrop3`, `CustomPlusFieldsDrop`, `NeedsDrop`, `(NeedsDrop, NeedsDrop, u64)`, `[NeedsDrop; 2]`, `[NeedsDrop]`, `Guard`, `Box<dyn Any>`, `Result`, `dyn Any`) | `10` | `10.87%` | **No** (`0%`) | **No** (`0%`) | **Yes** (`mir_shims`) |
| `ShimKind::ClosureOnce` (`3` user closures + `lang_start` closure) | `4` | `4.35%` | **No** (`0%`) | **No** (`0%`) | **Yes** (`mir_shims`) |
| `ShimKind::Reify` (`tracked_standalone`, `<TrackedReceiver as UntrackedAction>::act`, `<dyn UntrackedAction>::act`) | `3` | `3.26%` | **No** (`0%`) | **No** (`0%`) | **Yes** (`mir_shims`) |
| `ShimKind::VTable` (`<u32 as ByValueDyn>::consume_val`, `lang_start` vtable) | `2` | `2.17%` | **No** (`0%`) | **No** (`0%`) | **Yes** (`mir_shims`) |
| `ShimKind::FnPtr` (`<fn(u32, u64) -> u64 as Fn>::call`, `<fn() as FnOnce>::call_once`) | `2` | `2.17%` | **No** (`0%`) | **No** (`0%`) | **Yes** (`mir_shims`) |
| `ShimKind::Clone` (`<(NeedsDrop, NeedsDrop, u64) as Clone>::clone`) | `1` | `1.09%` | **No** (`0%`) | **No** (`0%`) | **Yes** (`mir_shims`) |
| `ShimKind::FnAddrAsPtr` / `FnPtrAddrShim` (`<fn(u32, u64) -> u64 as FnPtr>::addr`) | `1` | `1.09%` | **No** (`0%`) | **No** (`0%`) | **Yes** (`mir_shims`) |
| **Subtotal: Synthesized `Shim` `MonoItem::Fn`s** | **`23`** | **`25.00%`** | **No (`0%`)** | **No (`0%`)** | **Yes** |
| **Subtotal: All Non-`mir_keys` Executable `MonoItem::Fn`s** | **`76`** | **`82.61%`** | **No (`0%`)** | Partial (`53/76`) | **Yes (`76/76`)** |
| **Total Executable `MonoItem::Fn` Instances** | **`92`** | **`100.00%`** | `16/92` (`17.39%`) | `69/92` (`75.00%`) | **`92/92` (`100.00%`)** |
| Static allocations (`CLONE_STEP`, `DROP_LOG`, `STATIC_RECV`) | `3` | — | Local statics only | **Yes** (`3`) | **Yes** (`3`) |
| **Grand Total `MonoItem`s (`Fn` + `Static`)** | **`95`** | — | — | **`72`** (`65` distinct `DefId`s) | **`95`** |

Note the exact machine-checked conservation identity enforced by `probe_mir_shims_and_completeness.py`:
$$|\text{PrintMonoItems}| - \sum_{d} \text{DumpMonoStats}[d].\text{instantiation\_count} = 95 - 72 = 23 = |\text{SynthesizedShimMonoItems}|.$$

### 3.7 Closing `Trusted.MirSemantics.CrateTheorem`: Capture Architecture and Lean 4 Mechanization

`Basis: source + execution + derived`

#### 3.7.1 Producer Completeness Contract in `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`)

In `joshlf/anneal` (`trusted/lean/Trusted/MirSemantics.lean:1786-1809`), `ProgramVerified` and `CrateTheorem` are defined as:

```lean
-- joshlf/anneal @ c131b320eeeb26ef692e5afd5ec8db49ee518613
-- trusted/lean/Trusted/MirSemantics.lean:1786-1804
noncomputable def ProgramVerified (p : Program) (specs : Specs) : Prop :=
  Nat.beq p.pointerWidthBits 64 = true ∧
  Nat.beq p.mirProfileVersion 1 = true ∧
  !p.bodies.isEmpty = true ∧
  Nat.blt p.entryDefId p.bodies.length = true ∧
  bodiesHaveUniqueIdentities p.bodies = true ∧
  (∀ (defId : DefId) (body : Body),
    getElem? p.bodies defId = some body →
    BodyVerified p defId body (specs.safety body.identity)) ∧
  specs.property p

noncomputable def CrateTheorem (c : Crate) : Prop :=
  c.program.scope = .crate ∧ ProgramVerified c.program c.specs
```

As documented at `Trusted/MirAst.lean:875-878, 933-936` and `Trusted/MirSemantics.lean:1700-1706, 1798-1801`, `Trusted.MirSemantics` evaluates `ProgramVerified` strictly over the `List Body` supplied in `c.program.bodies` (currently failing closed with `.fault .unsupported` on any reachable `TerminatorKind.call` or `.unsupported` terminator such as `Drop`, `UnwindTerminate`, or indirect `Call`, `Trusted/MirSemantics.lean:1568-1569`). Meanwhile, `trusted/rustc-capture/src/driver.rs:75-84, 148-150` currently implements `AnalysisCallbacks::after_analysis` as a session-integrity scaffold (`anneal-rustc-capture: compiler analysis callback reached; verification not performed`).

To discharge the external producer completeness obligation of `CrateTheorem` when `anneal-rustc-capture` is extended to emit `Program` artifacts (`scope = .crate`), the capture callback must satisfy five exact design requirements derived from Findings 3.1–3.6:

1. **Drive collection via `tcx.collect_and_partition_mono_items(())` (or `collect_crate_mono_items` in `Eager` mode for libraries without exported monomorphic roots), never `tcx.mir_keys(())`:** For pure generic library crates, `Lazy` root collection (`collector.rs:1751-1778`) collects zero roots for uninstantiated `pub fn generic<T>()` items; whole-crate verification of concrete binary/cdylib/staticlib crates uses `collect_and_partition_mono_items(())` (`Lazy` or `-Clink-dead-code` `Eager`), whereas library proof-unit capture (`UnitTheorem`) must resolve each target monomorphic `Instance` and run the `items_of_instance` transitive closure (`collector.rs:1400-1413`).
2. **Fetch every `MonoItem::Fn(instance)` via `tcx.instance_mir(instance.def)`:** Never call `tcx.optimized_mir(instance.def_id())` directly—doing so misses all 13 `ShimKind` variants and panics on foreign `DefKind::Ctor` items (`dep_generics::GenericPair`, `Option::Some`).
3. **Apply `instance.instantiate_mir_and_normalize_erasing_regions` gated by `has_polymorphic_mir_body()`:** Substitute `instance.args` onto `Body` when `instance.def.has_polymorphic_mir_body()` is `true` (`Item`, `VTable`, `Reify`, `ClosureOnce`, `ConstructCoroutineInClosure`, `DropGlue(_, None)`), and apply `instantiate_identity` + `normalize_erasing_regions` when `false` (`Clone`, `FnPtr`, `FnAddrAsPtr`, `FnPtrFromPtr`, `DropGlue(_, Some(T))`, `ThreadLocal`, `FutureDropPoll`, `AsyncDropGlue`, `AsyncDropGlueCtor`).
4. **Assign collision-free canonical `Body.identity` strings keyed by `(InstanceKind, GenericArgs)` (`v0` symbol mangling `tcx.symbol_name(instance)`):** `Trusted/MirAst.lean:851-860` notes that `TyCtxt::def_path_str(def_id)` is neither unique across generic instantiations nor distinct between `Item(f)` and `Reify(f, None)` (nor between `Reify(f, Some(FnPtr))` and `Reify(f, Some(Vtable))` under KCFI). Using `tcx.symbol_name(instance).name` (e.g., `_RNv...tracked_standalone` vs. `_RNSNv...tracked_standalone5reifyB3_`) guarantees `bodiesHaveUniqueIdentities p.bodies = true`, as enforced by `assert_symbols_are_distinct` in `partitioning.rs:1146-1166`.
5. **Lower or elaborate shim-specific constructs before emitting `Trusted.MirAst`:** Because `make_shim` leaves `TerminatorKind::Drop` (shallow static field drops), `UnwindAction::Terminate(InCleanup)`, `Rvalue::Cast(PointerCoercion::Unsize)`, and implicit `#[track_caller]` `CallerLocation` ABI arguments in `Runtime(Optimized)` shim MIR, `anneal-rustc-capture` (or an extended `Trusted.MirSemantics`) must resolve static `TerminatorKind::Drop { place: T }` edges to direct calls to `Instance::resolve_drop_glue(tcx, T)` (`DropGlue` mono items) and materialize implicit `#[track_caller]` `&Location` arguments at `Call` sites where `callee_instance.def.requires_caller_location(tcx)` is `true`.

#### 3.7.2 Kernel-Checked `Lean v4.34.1` Mechanization (`support/MirShimsAndCaptureCompleteness.lean`)

`support/MirShimsAndCaptureCompleteness.lean` (`1,365` lines, zero external imports, zero `Classical.choice`, zero `sorry`, verified under `Lean v4.34.1`) formalizes the 13-variant `ShimTag` and `InstanceId` taxonomy, executable basic-block CFG synthesizers `buildDropShim` and `buildCloneShim`, `buildReifyTrackCallerShim`, and `CaptureComplete`, proving nine core theorems:

| Lean Declaration (`MirShimsAndCaptureCompleteness`) | Mechanized Statement Summary |
| :--- | :--- |
| `no_shim_in_mir_keys` / `no_shim_in_dump_mono_stats` | For all `tag : ShimTag`, `isMirKeysMember (.shim tag) = false` and `isDumpMonoStatsMember (.shim tag) = false`. |
| `buildDropShim_normal_exact_once` | For any `fields : List FieldId`, when `∀ f ∈ fields, dropPanics f = false`, `executeDropShim fields dropPanics = .returned { liveFields := [], droppedLog := fields }`. |
| `buildDropShim_exact_once_and_no_double_drop` | For any `DistinctFields fields` and arbitrary `dropPanics`, execution of the synthesized `DropGlue` CFG either: (1) returns normally with `liveFields = []` and `droppedLog = fields`; (2) unwinds (`UnwindResume`) with `liveFields = []` and `droppedLog = fields` (destroying all suffix fields on single-panic unwind with zero leaks); or (3) aborts deterministically via `UnwindTerminate(InCleanup)` on double-panic with `droppedLog` equal to a `DistinctFields` prefix of `fields` (zero double-drops on any path). |
| `buildCloneShim_leak_free_partial_clone_cleanup` | For any `DistinctFields fields`, when cleanup drops do not double-panic, `executeCloneShim fields clonePanics dropPanics` either returns `.returned { destLive := fields, destDroppedLog := [] }` (all clones succeed) or, at the first panicking field `fields = clonedPrefix ++ (failingField :: uninitSuffix)`, unwinds with `.unwound { destLive := [], destDroppedLog := clonedPrefix.reverse }`—destroying every already-cloned prefix field in exact reverse initialization order and never dropping `failingField` or `uninitSuffix`. |
| `reify_track_caller_resolves_abi_and_binds_def_loc` | Direct calls to `.trackCallerImplicitLoc` pass `callSiteLoc`; raw `.plain` indirect calls fault with `.abiArityFault`; wrapping in `buildReifyTrackCallerShim` restores `.plain` ABI compatibility and binds the callee's observed location to `defLoc`. |
| `whole_crate_soundness_of_capture_complete` | If `CaptureComplete compiled captured` and `CapturedProgramVerified captured` hold, then across arbitrary transitive call/drop/reify/vtable chains from `compiled.roots`, `¬ CrateReachesFault compiled`. |
| `ce1_local_mir_keys_only_capture_misses_drop_or_reify_shim_unsound` | Concrete 3-body crate `ce1Crate` where `.localItem 0` is locally safe (`localStepSafe = true`) and invokes `.shim (.dropGlue 10 (some 1))` (`localStepSafe = false`): **both** `mirKeysOnlyCapture ce1Crate` and `dumpMonoStatsCapture ce1Crate` pass `CapturedProgramVerified`, yet `CrateReachesFault ce1Crate` holds at runtime and neither capture satisfies `CaptureComplete`. |
| `ce2_clone_shim_without_prefix_unwind_cleanup_leaks_cloned_fields` | Concrete 3-tuple `[0, 1, 2]` where cloning field `0` succeeds and cloning field `1` panics: `buildCloneShim [0, 1, 2]` unwinds with `destLive = []` and `destDroppedLog = [0]`, whereas `buildBrokenCloneShimWithoutPrefixCleanup [0, 1, 2]` unwinds with `destLive = [0]` (`destDroppedLog = []`), leaking field `0`'s owned resource. |

## Boundaries

To prevent over-generalization by downstream compiler or verification authors, the negative space of this investigation is classified using the `reference-corpus/1` boundary categories:

- **Known not to apply:**
  1. *`ShimKind::Clone` does not apply to fixed-size arrays `[T; N]` or primitive scalars (`u32`, `bool`, pointers):* Despite the stale doc-comment on `ShimKind::Clone` (`compiler/rustc_middle/src/ty/instance.rs:174-175`), `resolve_associated_item` (`compiler/rustc_ty_utils/src/instance.rs:273-290`) only synthesizes `ShimKind::Clone` for `FnDef`, `FnPtr`, `Coroutine`, `CoroutineWitness`, `Closure`, `CoroutineClosure`, and `Tuple`. Array cloning resolves to `core::array::SpecArrayClone` (`InstanceKind::Item`).
  2. *`-Zdump-mono-stats` does not enumerate compiled mono items:* `dump_mono_items_stats` (`partitioning.rs:1302`) filters out all `InstanceKind::Shim` items via `MonoItem::is_user_defined()`. Passing `-Zdump-mono-stats` passes `ce1` vacuously while missing 100% of `DropGlue`, `Clone`, `Reify`, `VTable`, `FnPtr`, and `ClosureOnce` shims.
  3. *`tcx.optimized_mir(def_id)` does not apply to foreign `DefKind::Ctor` items:* Upstream `.rmeta` files encode `DefKind::Ctor` exclusively in the `mir_for_ctfe` table (`encoder.rs:1184`); only `tcx.instance_mir(InstanceKind::Item(def_id))` (or `tcx.mir_for_ctfe(def_id)`) retrieves foreign tuple struct/variant constructors without panicking.
  4. *`collect_and_partition_mono_items(())` (`Lazy` mode) does not cover uninstantiated polymorphic functions in standalone `rlib` crates:* `RootCollector::is_root` (`collector.rs:1751-1778`) skips items with non-erasable generic parameters (`requires_monomorphization == true`) and private unreachable functions unless `-Clink-dead-code` (`Eager` mode, for monomorphic items) or a concrete monomorphic caller root is present.
- **Unsupported:**
  1. *Current `Trusted.MirSemantics` (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`) marks interprocedural calls, `TerminatorKind::Drop`, indirect `Call`, `UnwindResume`, and `UnwindTerminate` as `.fault .unsupported`:* While `CrateTheorem` and `ProgramVerified` are defined in `Trusted/MirSemantics.lean:1786-1804`, executing multi-body `DropGlue`, `Clone`, `Reify`, or `ClosureOnce` shims inside `Trusted.MirSemantics` requires extending `evalTerminator` (`Trusted/MirSemantics.lean:1537-1570`) beyond single-frame scalar/unit execution and extending `anneal-rustc-capture` beyond its `after_analysis` scaffold (`trusted/rustc-capture/src/driver.rs:75-84`).
  2. *`InstanceKind::Intrinsic`, `InstanceKind::LlvmIntrinsic`, and `InstanceKind::Virtual` have no `instance_mir` body:* Querying `tcx.instance_mir` on any of these three variants triggers an internal compiler error (`ty/mod.rs:2021-2024`). Calls to intrinsics without MIR fallback bodies and dynamic `Virtual(def_id, slot)` dispatches must be modeled directly in caller terminator semantics (with soundness over dynamic dispatch established by verifying every `VtblEntry::Method(instance)` collected at `Unsize` casts in `create_mono_items_for_vtable_methods`, `collector.rs:1244-1290`).
- **Not examined:**
  1. *Runtime execution of unstable `async Drop` shims (`ShimKind::FutureDropPoll`, `ShimKind::AsyncDropGlueCtor`, `ShimKind::AsyncDropGlue`) and `ConstructCoroutineInClosure`:* Their exact query routing and pass pipelines in `shim.rs:75-77, 131-176` and `shim/async_destructor_ctor.rs:17-350` were audited in primary source, but `probe_mir_shims_and_completeness.py` did not execute `#![feature(async_drop)]` coroutines at runtime.
  2. *Cross-platform `ShimKind::ThreadLocal` emission:* Audited in `shim.rs:484-509` (`Rvalue::ThreadLocalRef(def_id)`), which is only emitted when exporting thread-local statics from dynamic libraries on targets lacking native ELF/Mach-O TLS relocation support; not empirically triggered on `x86_64-unknown-linux-gnu` static/executable builds.
  3. *Dynamic library (`dlopen` / `cdylib`) open-world vtables and FFI callbacks:* `CaptureComplete` in `MirShimsAndCaptureCompleteness.lean` models closed-crate `MonoItem` reachability; calls crossing `extern "C"` FFI boundaries or dynamically loaded shared objects introduce uncaptured external code outside `collect_and_partition_mono_items`.
- **Unknown:**
  1. *Whether upstream `rustc` will eventually run `make_shim` passes on coroutine `DropGlue` (`FIXME(#91576)` at `compiler/rustc_mir_transform/src/shim.rs:80-81`):* Upstream explicitly notes uncertainty over why coroutine drop shims run only `MentionedItems`, `AbortUnwindingCalls`, and `CriticalCallEdges` while skipping `AddMovesForPackedDrops`, `RemoveNoopLandingPads`, `SimplifyCfg::MakeShim`, `InstSimplify::BeforeInline`, and `ForceInline`.
- **Attractive stronger conclusions not established:**
  - The `82.61%` non-`mir_keys` share and `25.00%` shim share measured on `shim_probe` are exact measurements of a compact two-crate specimen designed to exercise diverse shim kinds (`std` runtime startup + `catch_unwind` + `dep_generics`); in large application crates with hundreds of local HIR functions, the local `Item` fraction will be higher, whereas in generic-heavy or `serde`/async-heavy crates the non-`mir_keys` fraction can exceed `85%`. What generalizes unconditionally is qualitative: **any** crate using `Drop` types, tuple/closure `Clone`, `dyn Trait`, `#[track_caller]` coercions, `fn` pointers as `Fn*`, or upstream generics has a non-empty set of executable `MonoItem::Fn` bodies absent from `tcx.mir_keys(())`.

## Evidence

### Primary-Source Code Locations Verified at Immutable Revisions

1. **`rust-lang/rust` at `c7d5ba59d8e11ee2e2204b173458eec4cb41c973`:**
   - `compiler/rustc_middle/src/ty/instance.rs:33-205` — `Instance<'tcx>`, `ReifyReason` (`FnPtr`, `Vtable`), `InstanceKind<'tcx>`, and all 13 `ShimKind<'tcx>` variants.
   - `compiler/rustc_middle/src/ty/instance.rs:264-411` — `InstanceKind::requires_caller_location`, `InstanceKind::has_polymorphic_mir_body`, and `ShimKind::{def_id, def_id_if_not_guaranteed_local_codegen, requires_inline, has_polymorphic_mir_body}`.
   - `compiler/rustc_middle/src/ty/mod.rs:1996-2035` — `TyCtxt::instance_mir` routing `Item(def)` (`DefKind::Ctor` -> `mir_for_ctfe`, standard callables -> `optimized_mir`), `Intrinsic`/`LlvmIntrinsic`/`Virtual` -> `bug!`, and `Shim(shim)` -> `mir_shims`.
   - `compiler/rustc_middle/src/mono.rs:97-102` — `MonoItem::is_user_defined` returning `matches!(instance.def, InstanceKind::Item(..))`.
   - `compiler/rustc_ty_utils/src/instance.rs:17-450` — `resolve_instance_raw` and `resolve_associated_item`, including exact builtin `ShimKind::Clone` eligibility (`lines 273-290`), `FnPtrFromPtr` (`lines 298-312`), `FnAddrAsPtr` (`lines 313-331`), `FnPtr` (`lines 353-359, 410-416`), and `ConstructCoroutineInClosure` (`lines 360-405`).
   - `compiler/rustc_ty_utils/src/abi.rs:259-279` — `FnAbiDesc::for_instance` appending `tcx.caller_location_ty()` iff `instance.def.requires_caller_location(tcx)`.
   - `compiler/rustc_codegen_ssa/src/mir/block.rs:1438-1467` — `codegen_call_terminator` asserting `fn_abi.args.len() == mir_args + 1` and passing `get_caller_location(bx, source_info)` on calls to `requires_caller_location` targets.
   - `compiler/rustc_mir_transform/src/lib.rs:331-362, 500-541, 608-789, 792-838` — `mir_keys`, `inner_mir_for_ctfe` (`build_adt_ctor` delegation), `run_analysis_to_runtime_passes`, `run_optimization_passes`, and `optimized_mir`.
   - `compiler/rustc_mir_transform/src/shim.rs:28-206` — `provide` (`mir_shims`), `make_shim`, and abbreviated `pm::run_passes_no_validate` pass lists.
   - `compiler/rustc_mir_transform/src/shim.rs:258-482` — `build_drop_shim`, `[T; N]` -> `&mut [T]` unsizing delegation (`lines 306-345`), `new_body` (`phase = Runtime(Initial)`, `line 406`), and `DropShimElaborator`.
   - `compiler/rustc_mir_transform/src/shim.rs:512-776` — `build_clone_shim` and `CloneShimBuilder::{clone_fields, tuple_like_shim, coroutine_shim}`.
   - `compiler/rustc_mir_transform/src/shim.rs:781-1091` — `build_call_shim` (`VTable`, `FnPtr`, `Reify`, `ClosureOnce`) and `build_adt_ctor`.
   - `compiler/rustc_mir_transform/src/shim.rs:1100-1332` and `compiler/rustc_mir_transform/src/shim/async_destructor_ctor.rs:17-350` — `build_fn_addr_as_ptr_shim`, `build_fn_ptr_from_ptr_shim`, `build_construct_coroutine_by_move_shim`, `build_async_destructor_ctor_shim`, `build_async_drop_shim`, and `build_future_drop_poll_shim`.
   - `compiler/rustc_mir_transform/src/elaborate_drop.rs:838-965, 1013-1067` — `drop_halfladder`, `drop_ladder`, `open_drop_for_adt`, and `open_drop_for_adt_contents`.
   - `compiler/rustc_metadata/src/rmeta/encoder.rs:1175-1205, 1935-1996` and `decoder/cstore_impl.rs:248-253, 332` — `should_encode_mir` (`DefKind::Ctor => (true, false)`), `encode_mir`, and `is_mir_available`.
   - `compiler/rustc_monomorphize/src/collector.rs:750-1466, 1491-1957` and `partitioning.rs:1169-1356` — `MirUsedCollector`, `visit_drop_use`, `visit_fn_use`, `visit_instance_use`, `should_codegen_locally`, `create_mono_items_for_vtable_methods`, `collect_crate_mono_items`, `collect_and_partition_mono_items`, `-Zprint-mono-items`, and `dump_mono_items_stats`.
2. **`rust-lang/rust` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`:**
   - `compiler/rustc_middle/src/ty/instance.rs:62-185, 584-780`, `compiler/rustc_middle/src/ty/mod.rs:1754-1787`, `compiler/rustc_mir_transform/src/lib.rs:51-56`, and `compiler/rustc_mir_transform/src/shim.rs:67-251, 299-405` (verifying the `f8a0` -> `1421` `pub fn build_drop_shim` signature change and flat 12-shim `InstanceKind` layout).
3. **`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`:**
   - `trusted/lean/Trusted/MirAst.lean:782-796, 862-944` — `TerminatorKind`, `Body`, `VerificationScope` (`.unit` vs. `.crate`), and `Program` producer obligations.
   - `trusted/lean/Trusted/MirSemantics.lean:1537-1570, 1685-1809` — `evalTerminator`, `BodyStaticAdmitted`, `BodyVerified`, `ProgramVerified`, `CrateTheorem`, and `UnitTheorem`.
   - `trusted/rustc-capture/src/driver.rs:25-152` — `COMPILER_VERSION` pin (`1.98.0-nightly (f8a08b688 2026-05-30)`) and `AnalysisCallbacks`.

### Preserved Package Support Artifacts (`2026-11-21`)

- `support/probe_mir_shims_and_completeness.py` — Standalone Python 3.10+ empirical harness (stdlib only; uses `tempfile.TemporaryDirectory` and scrubs all temporary paths to `<PROBE_DIR>`) that compiles `dep_generics.rs`, `shim_probe.rs`, `closure_once_iso.rs`, and `kcfi_reify_probe.rs`, executes `shim_probe`, verifies `|print_mono_items| - sum(dump_mono_stats) == |shims|`, and emits deterministic JSON.
- `support/mir_shims_and_completeness_probe.json` — Recorded empirical output from `rustc 1.98.0-nightly (14210df0e27ccd7d9e6a05b8085cbd438e4bbc65)` on `x86_64-unknown-linux-gnu`, preserving full `mir_keys` headers, classified `MonoItem` lists, KCFI `reify-fnptr` / `reify-vtable` mono items, pass-snapshot lists (`96` vs. `17` vs. `112`), LLVM IR `#[track_caller]` vs. `Reify` function definitions, runtime execution JSON (`direct_line: 189`, `reified_fn_ptr_line: 82`, `direct_trait_line: 194`, `reified_vtable_line: 61`, `partial_clone_unwind_caught: true`, `prefix_cleanup_drop_delta: 160`), and golden MIR dumps (`before`/`after` `SimplifyCfg-make_shim` and `runtime-optimized`) for `DropGlue`, `Clone`, `Reify`, `VTable`, `FnPtr`, `FnPtrAddr`, `ClosureOnce`, and `LocalTupleCtor`.
- `support/MirShimsAndCaptureCompleteness.lean` — Standalone `Lean v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) kernel-checked mechanization (`0` `sorry`s, `0` `Classical.choice`, `0` `Lean.ofReduceBool`, `0` `partial def`).

## Revalidation

To revalidate all empirical and mechanized claims on a newer `rustc` nightly or after modifying `anneal-rustc-capture`:

1. **Re-run the standalone `rustc` shim MIR, KCFI, LLVM-IR, and mono-item completeness probe (`~3s`):**
   ```bash
   python3 reports/rustc-synthesized-mir-shims-drop-glue-and-monomorphization-completeness/support/probe_mir_shims_and_completeness.py \
     --out "${TMPDIR:-.}/revalidated_mir_shims_probe.json"
   ```
   A passing exit (`0`) confirms that: (a) all shim archetypes (`DropGlue`, `Clone`, `Reify`, `VTable`, `FnPtr`, `FnPtrAddr`, `ClosureOnce`, local/foreign `Ctor`) compile and execute; (b) the accounting identity `total_mono_items_all_kinds - dump_mono_stats_user_fn_and_static_instantiations == synthesized_shim_fn_mono_items` holds with `shim_other == 0`; and (c) runtime `Location::caller()` binding and mid-tuple clone unwind cleanup (`prefix_cleanup_drop_delta == 160`) behave as specified. Note: if a future `rustc` removes `#![feature(fn_ptr_trait)]` (`FnPtr::addr` was split into `FnAddr::as_ptr` and `FnPtr::from_ptr` in newer nightlies such as `c7d5ba59d8e11ee2e2204b173458eec4cb41c973`), replace `FnPtr::addr(fp)` in `MAIN_CRATE_RS` with the corresponding `FnPtr`/`FnAddr` trait method to test `ShimKind::FnAddrAsPtr` and `ShimKind::FnPtrFromPtr`.

2. **Re-verify the `Lean v4.34.1` formalization and kernel axiom footprint (`~5s`):**
   ```bash
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     reports/rustc-synthesized-mir-shims-drop-glue-and-monomorphization-completeness/support/MirShimsAndCaptureCompleteness.lean
   ```
   To audit axioms explicitly, append `#print axioms` commands in a scratch copy `check_axioms.lean` outside the corpus tree for `buildDropShim_normal_exact_once`, `buildDropShim_exact_once_and_no_double_drop`, `buildCloneShim_leak_free_partial_clone_cleanup`, `reify_track_caller_resolves_abi_and_binds_def_loc`, `whole_crate_soundness_of_capture_complete`, `ce1_local_mir_keys_only_capture_misses_drop_or_reify_shim_unsound`, and `ce2_clone_shim_without_prefix_unwind_cleanup_leaks_cloned_fields`, and confirm that only `propext` and `Quot.sound` (or `'...' does not depend on any axioms`) appear, with zero `sorryAx`, `Classical.choice`, or `Lean.ofReduceBool`.

3. **Targeted primary-source diff check on a newer `rust-lang/rust` commit:**
   Instead of re-auditing the entire compiler, diff the five narrow regions that determine shim completeness and pass-pipeline invariants:
   - `enum InstanceKind` and `enum ShimKind` in `compiler/rustc_middle/src/ty/instance.rs` (check whether any 14th `ShimKind` variant was added or `has_polymorphic_mir_body` / `requires_caller_location` changed);
   - `TyCtxt::instance_mir` in `compiler/rustc_middle/src/ty/mod.rs`;
   - `fn mir_keys` in `compiler/rustc_mir_transform/src/lib.rs`;
   - `fn make_shim`, `build_drop_shim`, `build_clone_shim`, `build_call_shim`, and `build_adt_ctor` in `compiler/rustc_mir_transform/src/shim.rs`;
   - `visit_instance_use` and `should_codegen_locally` in `compiler/rustc_monomorphize/src/collector.rs`.
