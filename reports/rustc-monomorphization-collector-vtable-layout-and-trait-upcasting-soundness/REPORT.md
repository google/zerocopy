# `rustc` monomorphization collector, vtable layout, and `dyn` trait upcasting soundness

## Summary

`rustc` lowers generic and trait-object Rust programs through two tightly coupled post-analysis subsystems: the monomorphization collector (`rustc_monomorphize`), which computes a closed graph of linkable `MonoItem` symbols and partitions them into codegen units (CGUs), and the vtable layout and codegen machinery (`rustc_trait_selection::traits::vtable`, `rustc_middle::ty::vtable`, `rustc_codegen_ssa::meth`, `rustc_codegen_ssa::base`), which lays out constant vtables on demand per CGU and compiles `PointerCoercion::Unsize` trait upcasts. This report audits both subsystems at `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (with source-drift checks against `rust-lang/rust@c7d5ba59d8e11ee2e2204b173458eec4cb41c973`), characterizes them empirically on that exact compiler (`rustc 1.98.0-nightly`, LLVM `22.1.6`) across 38 automated probe checks, and provides a standalone Lean `v4.34.1` formalization (`support/MonomorphVtableUpcastSoundness.lean`) with kernel-checked soundness theorems and sharpness counterexamples. What a later reader should retain:

1. **Vtables are per-CGU private constants, not `MonoItem`s, and use a hybrid prefix-plus-`TraitVPtr` layout.** `VtblEntry` has six variants (`MetadataDropInPlace`, `MetadataSize`, `MetadataAlign`, `Vacant`, `Method(Instance)`, `TraitVPtr(TraitRef)`). Every vtable starts with `[0]=drop_in_place`, `[1]=size`, `[2]=align`. Along the first-supertrait spine, supertrait vtables are embedded as exact prefixes so upcasts reuse the vtable pointer with zero loads; non-principal secondary supertraits emit an extra `TraitVPtr` slot pointing to a separate supertrait vtable allocation, so upcasting performs a single `!invariant.load !nonnull` pointer load. Because `meth::get_vtable` caches per CGU and `static_addr_of_mut` emits `private unnamed_addr constant` globals, vtable pointer addresses are **not unique** across CGUs within one executable or across crates (`same_vtable=false` observed at both `-O0` and `-O2`). `Basis: source + execution`
2. **Three non-obvious vtable invariants confirmed in live LLVM IR:**
   - *Nullable drop slot:* when `!ty.needs_drop`, `vtable_allocation_provider` writes **`null`** (all-zero bytes) into slot `[0]` instead of an empty drop-glue function pointer, and `drop_in_place::<dyn Trait>` emits a runtime `icmp ne ptr %drop_fn, null` guard before calling slot `[0]`.
   - *Empty-marker prefix preservation:* `prepare_vtable_segments_inner` sets `emit_vptr_on_new_entry |= has_entries`, so an empty marker supertrait listed first (`trait SubAfterEmpty: EmptyMarker + SecondSuper`) does **not** force a `TraitVPtr` for `SecondSuper`; upcasting `dyn SubAfterEmpty -> dyn SecondSuper` remains zero-cost prefix reuse.
   - *Vacant slots stay uninitialized:* methods whose `where` clauses are impossible for the concrete type produce `VtblEntry::Vacant`, leaving `[8 x i8] undef` in the LLVM constant global. `Basis: source + execution`
3. **Why `create_mono_items_for_vtable_methods` safely skips `VtblEntry::TraitVPtr`.** When collecting mono-items for `T -> dyn Sub`, `collector.rs` iterates `tcx.vtable_entries(trait_ref)` and intentionally ignores `VtblEntry::TraitVPtr(_)`. This is link-complete because `prepare_vtable_segments_inner` places every transitive supertrait's own method segment inside the subtrait's `vtable_entries` before emitting `TraitVPtr`, and `impl_ty`'s drop glue is shared by the subtrait and every embedded supertrait vtable. Furthermore, `Runtime(PostCleanup)` MIR represents both zero-cost prefix upcasts and indirect `TraitVPtr` upcasts identically as `PointerCoercion(Unsize, Implicit)`; the indirection decision happens solely in codegen (`unsized_info` querying `supertrait_vtable_slot`). `Basis: source + execution + derived`
4. **All five shim `InstanceKind` families are collected on demand, and `Lazy` vs. `Eager` is controlled solely by `-C link-dead-code`.** On `rustc 1.98.0-nightly`, `-Z print-mono-items` takes a boolean (`=yes`/`=no`; `=lazy` is rejected with a CLI error). `partitioning.rs` selects `MonoItemCollectionStrategy::Eager` if and only if `tcx.sess.link_dead_code()` holds (despite a stale doc comment in `collector.rs` referencing incremental compilation), adding unused non-generic functions, unused ADT drop glues, and unused non-generic default trait methods (+6 items in the shim specimen: 50 → 56) while disabling `internalize_symbols` (switching all items to `External`). Reifying `drop_in_place::<T>` as a `fn` pointer forces emission of `DropGlue(_, None)` even for `Copy` types (`is_direct_call == false`), whereas direct drops omit it. `Basis: source + execution`
5. **No `LinkOnceODR` for Rust monomorphizations, and unconditional upstream reuse of `#[inline(never)]` generics.** Across 4-CGU builds (`-O0` and `-O2`), `rustc` emits **zero** `LinkOnceODR` items: `LocalCopy` items (`#[inline(always)]`, optimized generics) get CGU-private `Internal` copies; `GloballyShared` items start as `External` and are demoted to `Internal` by `internalize_symbols` when unused outside their home CGU. In separate compilation (`rlib` + downstream `bin`), `-Z share-generics=yes` reuses upstream `poly_default::<u64>` while `-Z share-generics=no` re-instantiates it locally—**except** for `#[inline(never)]` generics (`poly_inline_never::<u64>`), which reuse upstream monomorphizations even under `-Z share-generics=no` (`instance.rs:211-215`). Similarly, `#![type_length_limit = "..."]` is not enforced by default (`-Z enforce-type-length-limit` defaults to `false`), so exponential type growth hits `recursion_limit` unless that unstable flag is enabled. `Basis: source + execution`
6. **Kernel-checked Lean `v4.34.1` model** (`support/MonomorphVtableUpcastSoundness.lean`, 2,027 lines, 82 top-level `theorem` declarations, 416 kernel theorem constants, axioms `{propext, Quot.sound}` only, `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, `0` `._unsafe_rec`):
   - Proves universal virtual slot dispatch soundness (`virtualMethodSlot_sound`), exact `TraitVPtr` slot correspondence (`supertraitVtableSlot_vptr_sound`), universal `dyn` upcasting dispatch and drop-glue soundness (`upcast_dispatch_and_drop_sound`), supertrait vtable method coverage (`vtableCollectedMethods_covers_supertrait`), `Lazy ⊆ Eager` monotonicity (`monoReachable_monotone_roots`), and fuel-parametric collector link-completeness (`collector_link_complete`);
   - Proves two sharpness counterexamples: **CE1** (reusing the subtrait vtable pointer for secondary supertrait `SuperB` dispatches `SuperB::b_val` to `SuperA::a_val`, and on a 3-supertrait hierarchy reads a `TraitVPtr` data pointer at the method slot); and **CE2** (omitting `ReifyShim` during `#[track_caller]` function-pointer coercion, or omitting `DropGlue` during `dyn Trait` unsizing of a drop-needing type, produces a deterministic `RuntimeFault.missingSymbol` fault at runtime). `Basis: execution (Lean kernel) + derived`
7. **Anneal trusted MIR ingestion boundary** (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`): `Trusted.MirAst` maps `Dynamic`, `FnDef`, `FnPtr`, and `Closure` types to `MirTy.unsupported`, maps `Rvalue::Cast` (covering `Unsize`, `ReifyFnPointer`, and `ClosureFnPointer`) to `Rvalue.unsupported`, and maps `Drop` and indirect `Call` to `TerminatorKind.unsupported` (while direct `.call` faults with `.fault .unsupported` in `Trusted.MirSemantics`). Ingesting monomorphized trait-object code therefore requires extending `Trusted.MirAst` and `Trusted.MirSemantics` with wide-pointer representations, vtable allocations, indirect/virtual dispatch, and drop glue. `Basis: source`

> **Scope caution.** The Lean development is a standalone formalization over its own operational model of trait hierarchies, vtables, shims, and monomorphization edges. It is not a proof about the Rust source code of `rustc_monomorphize` or `rustc_trait_selection`, it does not import `joshlf/anneal`'s `Trusted.*` modules, and it does not model generic associated types with higher-ranked lifetimes, `async` drop shims, KCFI `ReifyReason` separation, or ThinLTO symbol import. See **Boundaries**.

## Applicability

**Subjects and how they relate.**

- `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (committed `2026-05-31`) is the exact `commit-hash` of the live `rustc 1.98.0-nightly` compiler (`host: x86_64-unknown-linux-gnu`, `LLVM version: 22.1.6`) used for every MIR dump, LLVM IR dump, `-Z print-mono-items=yes` trace, and native binary run in this package. All unannotated `compiler/` line ranges refer to this commit so source inspection and execution observe the exact same compiler.
- `rust-lang/rust@c7d5ba59d8e11ee2e2204b173458eec4cb41c973` (committed `2026-11-20`) is a later upstream snapshot inspected strictly to check whether the audited vtable layout and collector invariants drifted over the intervening six months (Finding 10). No binaries were compiled with this revision.
- `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476` is the `src/doc/reference` submodule commit pinned by `rust-lang/rust@14210df0e`; it supplies the language-level coercion rules for unsizing and trait upcasting (`src/type-coercions.md`, `src/types/trait-object.md`).
- `rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07` supplies RFC 3324 (`text/3324-dyn-upcasting.md`), which specifies `dyn` upcasting coercions while explicitly declining to stabilize any vtable layout, and RFC 2580 (`text/2580-ptr-meta.md`) for pointer metadata context.
- `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` is inspected solely to characterize the current MIR ingestion boundary in `Trusted.MirAst` and `Trusted.MirSemantics`.
- `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`, `x86_64-unknown-linux-gnu`, Release) is the Lean compiler and kernel that checked `support/MonomorphVtableUpcastSoundness.lean` and executed `support/MonomorphVtableUpcastAudit.lean`.

**Configuration of measurements.** All Rust specimens were compiled with `--edition=2021` on `x86_64-unknown-linux-gnu` (64-bit pointer size = 8 bytes, ABI alignment = 8 bytes). Specimen 1 (`vtable_diamond_upcast.rs`) and Specimen 2 (`shims_and_mono_collection.rs`) use `-C opt-level=0 -C debuginfo=0` (with Specimen 2 also compiled under `-C link-dead-code=yes` and Specimen 2 opting into `#![feature(unsized_fn_params)]` solely to trigger `InstanceKind::VTableShim` on a user trait alongside `Box<dyn FnOnce>`). Specimen 3 (`multi_cgu_linkage.rs`) runs with `-C codegen-units=4` at both `-C opt-level=0` and `-C opt-level=2`. Specimens 4a/4b (`sep_dep.rs`, `sep_app.rs`) run with `-C opt-level=0` under both `-Z share-generics=yes` and `-Z share-generics=no`. Specimens 5a/5b (`poly_recursion_limit.rs`, `type_length_limit.rs`) test default compilation and `-Z enforce-type-length-limit=yes`.

**What generalizes and why.**

- Vtable slot indices (`[0]=drop_in_place`, `[1]=size`, `[2]=align`, `[3..]` methods/`TraitVPtr`) are target-independent in `rustc_middle::ty::vtable` and `rustc_trait_selection::traits::vtable`; byte offsets scale by `tcx.data_layout.pointer_size()` (so slot 6 is byte offset `48` on 64-bit targets and `24` on 32-bit targets).
- Because RFC 3324 explicitly states that Rust does **not** stabilize vtable layout, Findings 1–3 apply only to compiler revisions that preserve `prepare_vtable_segments_inner` and `vtable_allocation_provider`.
- The collector counts (50 vs. 56 items, 27/16 items across 4 CGUs) describe the synthetic specimens authored to exercise specific code paths; they are not an ecosystem census and must not be extrapolated to crates.io binaries.
- The Lean theorems hold universally over all well-formed models in `MonomorphVtableUpcast`; their connection to `rustc` rests on the structural correspondence checked against concrete compiler outputs in Finding 9.

## Findings

### 1. Monomorphization collector architecture, roots, `Lazy` vs. `Eager`, and `mentioned_items`

`Basis: source + execution`

The top-level entry point `collect_crate_mono_items` (`compiler/rustc_monomorphize/src/collector.rs` L1807–1839) runs in two stages:

1. **Root discovery (`collect_roots`, L1457–1494; `RootCollector`, L1496–1729):** walks HIR free items, impl items, and nested bodies, filters roots through `mono_item.is_instantiable(tcx)` (`compiler/rustc_middle/src/mono.rs` L272–282, discarding non-generic items with impossible `where` predicates), and appends `entry_fn` plus `start_fn::<MainRet>` (`push_extra_entry_roots`, L1690–1728).
2. **Parallel DFS graph walk (`collect_items_root` / `collect_items_rec`, L354–617):** spawns `par_for_each_in` across roots sharing a `SharedState` (`visited`, `mentioned`, `usage_map`), checks `check_normalization_error` (L620–646) and `check_recursion_limit` (L648–679), invokes `tcx.items_of_instance((instance, mode))`, records directed edges in `usage_map`, and finally sorts `visited` by `StableHash` (L1834–1836) to restore determinism.

Three concrete source facts clarify common misconceptions:

- **What actually selects `Eager` vs. `Lazy`:** `collect_and_partition_mono_items` (`compiler/rustc_monomorphize/src/partitioning.rs` L1131–1136) chooses `MonoItemCollectionStrategy::Eager` **if and only if** `tcx.sess.link_dead_code()` is true, and `Lazy` otherwise. Although the module doc comment in `collector.rs` L149–150 still states *"Eager strategy is meant to be used in conjunction with incremental compilation"*, incremental compilation does **not** select `Eager` at this revision.
- **CLI evolution of `-Z print-mono-items`:** at `rustc 1.98.0-nightly`, passing `-Z print-mono-items=lazy` fails immediately (`cli::print_mono_items_requires_bool`: `incorrect value 'lazy' for unstable option 'print-mono-items' - one of: 'y', 'yes', 'on', 'true', 'n', 'no', 'off' or 'false' was expected`). The flag is strictly boolean (`-Z print-mono-items=yes`); selecting eager collection requires `-C link-dead-code=yes`.
- **What `Eager` adds beyond `Lazy`:** `RootCollector` (L1505–1671) adds all non-generic functions (except `#[rustc_force_inline]`), all non-generic ADT `DropGlue` instances (L1506–1544), all non-generic constants (L1563–1580), all non-generic default trait method implementations via `create_mono_items_for_default_impls` (L1582–1586, L1732–1800), and all non-generic closures (L1616–1647). In Specimen 2 (`shims_and_mono_collection.rs`), switching from default (`Lazy`) to `-C link-dead-code=yes` (`Eager`) increased collected mono-items from **50 to 56 (+6)**, adding:
  - `dead_non_generic` (unused non-generic function),
  - `<CopyNoDrop as UnusedDefaultTrait>::unused_default` (unused default trait method),
  - `std::ptr::drop_glue::<UnusedDrop> - shim(Some(UnusedDrop))` (unused ADT drop glue),
  - `<UnusedDrop as std::ops::Drop>::drop` and `std::hint::black_box::<u64>` (transitively reached from that drop glue),
  - `<UnusedDrop as std::ops::Drop>::pin_drop` (default method on `Drop`).
- **Two-mode collection (`CollectionMode::{UsedItems, MentionedItems}`):** to prevent optimization-level-dependent disappearance of post-monomorphization const-evaluation errors (PMEs), `collect_items_of_instance` (L1302–1365) walks `traversal::mono_reachable(body, tcx, instance)` in `UsedItems` mode, always evaluates `body.required_consts()` (L1349–1353), and walks `body.mentioned_items()` (excluding items already recorded in `used_mentioned_items`, L1357–1362) in `MentionedItems` mode—evaluating constants without emitting dead mono-items into codegen (`collector.rs` L568–570, L586–588).
- **What is explicitly excluded from `MonoItem`:** `MonoItem` (`compiler/rustc_middle/src/mono.rs` L56–60) has only three variants: `Fn(Instance)`, `Static(DefId)`, and `GlobalAsm(ItemId)`. As documented at `collector.rs` L23–29, constants, **vtables**, and object shims are not `MonoItem`s; vtables are synthesized locally on demand inside each CGU by codegen. Note also that `compiler/rustc_middle/src/mir/mono.rs` and `compiler/rustc_codegen_llvm/src/meth.rs` do not exist at this revision (both return HTTP 404); their responsibilities live in `compiler/rustc_middle/src/mono.rs`, `compiler/rustc_codegen_ssa/src/meth.rs`, and `compiler/rustc_codegen_llvm/src/consts.rs`.

### 2. `InstanceKind` taxonomy and shim synthesis (`VTableShim`, `ReifyShim`, `ClosureOnceShim`, `FnPtrShim`, `DropGlue`)

`Basis: source + execution`

`Instance<'tcx>` (`compiler/rustc_middle/src/ty/instance.rs` L33–36) pairs a `def: InstanceKind<'tcx>` with `args: GenericArgsRef<'tcx>`. `InstanceKind` has 15 variants at `14210df0e` (L62–185). Only `Intrinsic` and `Virtual` lack standalone callable MIR (L73–74, L109–117); every other callable shim is synthesized by `rustc_mir_transform::shim::make_shim` (`compiler/rustc_mir_transform/src/shim.rs` L67–199) and collected by `visit_instance_use` (`collector.rs` L975–1043).

| `InstanceKind` | Construction site | MIR body (`shim.rs`) | Observed live in Specimen 2 (`-Z print-mono-items=yes`) |
| :--- | :--- | :--- | :--- |
| `Item(DefId)` | Direct `fn`/closure/coroutine/impl item (`ty_utils/instance.rs` L95, L237) | User/impl MIR body | `plain_fn`, `<Payload as DynSpeak>::speak`, `tracked_free`, etc. |
| `Virtual(DefId, usize)` | `resolve_associated_item` on `BuiltinImplSource::Object` (`ty_utils/instance.rs` L239–261): `slot = first_method_vtable_slot + own_offset` | No standalone symbol; codegen loads vtable slot `idx` (`mir/block.rs` L1232–1278) | Dispatched dynamically; never appears as a `MONO_ITEM` (`collector.rs` L1011–1014 asserts `!is_direct_call` would ICE) |
| `VTableShim(DefId)` | `expect_resolve_for_vtable` (`instance.rs` L637–645) when `fn_sig.input(0).is_param(0) && has_self` (by-value `self: Self`, e.g., `FnOnce::call_once` or `#![feature(unsized_fn_params)]`) | `build_call_shim` rewrites `fn(self, ...)` → `fn(self: *mut Self, ...)` and dereferences `*self` (`shim.rs` L72–75, L874–881) | `<Payload as ByValConsume>::consume - shim(vtable)`; `<{closure#1} as FnOnce<(u64,)>>::call_once - shim(vtable)` |
| `ReifyShim(DefId, Option<ReifyReason>)` | (1) `resolve_for_fn_ptr` on `#[track_caller]` `Item` or `Virtual` (`instance.rs` L596–603); (2) `expect_resolve_for_vtable` when impl has `#[track_caller]` absent on trait (`instance.rs` L661–695) or on `Virtual` (L697–700); (3) KCFI separation (`ReifyReason::{FnPtr, Vtable}`) | `build_call_shim(..., None, CallKind::Direct(def_id))` (`shim.rs` L96–98): forwards args and supplies definition-site `&Location` or performs virtual call | All three non-KCFI triggers observed: `tracked_free - shim(reify)`, `<dyn DynSpeak as DynSpeak>::speak - shim(reify)`, `<Payload as DynSpeak>::tracked_on_impl - shim(reify)` |
| `ClosureOnceShim { call_once, track_caller }` | `resolve_closure` when `Fn`/`FnMut` closure is called as `FnOnce` (`instance.rs` L707–719, L755–779, L931–940) | `build_call_shim(..., Some(Adjustment::RefMut), CallKind::Direct(call_mut))` (`shim.rs` L99–109) | `<{closure#0} as FnOnce<(u64,)>>::call_once - shim` |
| `FnPtrShim(DefId, Ty)` | `resolve_associated_item` when `FnDef` or `FnPtr` is called via `Fn`/`FnMut`/`FnOnce` (`ty_utils/instance.rs` L326–329, L376–379) | `build_call_shim` untuples `Args` tuple and calls `ty` (`shim.rs` L76–90, L820–870); `has_polymorphic_mir_body() == false` | `<fn(u64) -> u64 as Fn<(u64,)>>::call - shim(fn(u64) -> u64)` and `<fn(u64) -> u64 {plain_fn} as Fn<(u64,)>>::call - shim(...)` |
| `DropGlue(DefId, Option<Ty>)` | `resolve_instance_raw` on `LangItem::DropGlue` (`ty_utils/instance.rs` L38–67): `Some(ty)` iff `ty.needs_drop`, else `None` | `build_drop_shim` (`shim.rs` L303–405); empty `return` block when `None` | Direct drop of `CopyNoDrop` emits nothing; reifying `drop_in_place::<CopyNoDrop>` emits `std::ptr::drop_in_place::<CopyNoDrop>` (`collector.rs` L1019–1026) |

**Measured LLVM IR and runtime behavior of shims (Specimen 2):**

- `VTableShim` LLVM IR (`support/probe_output/llvm_ir_excerpts.txt` L78–84): takes `(ptr %_1, i64 %_2)`, executes `%0 = load i64, ptr %_1, align 8`, and calls `<Payload as ByValConsume>::consume(i64 %0, i64 %_2)`, returning `vtable_shim=15`.
- `ReifyShim` for `#[track_caller]` (`llvm_ir_excerpts.txt` L87–92): takes `(i64 %_1)` and calls `tracked_free(i64 %_1, ptr align 8 @alloc_d9da8e8a...)`, binding the static definition-site `&Location`. At runtime, direct invocation returns the call-site line (`direct_line=99`), whereas calling through the coerced `fn(u64) -> u32` pointer returns `tracked_free`'s definition line (`reified_line=42`), and calling `dyn_ref.tracked_on_impl()` through the non-`#[track_caller]` trait vtable returns `tracked_on_impl`'s definition line (`vtable_track=35`).

### 3. Vtable entry representation, segment layout algorithm, and `dyn` trait upcasting

`Basis: normative (coercion rules) + source + execution`

`VtblEntry<'tcx>` (`compiler/rustc_middle/src/ty/vtable.rs` L13–26) defines the six slot kinds, with a fixed 3-slot header (`COMMON_VTABLE_ENTRIES`, L45–51):
- slot `0`: `MetadataDropInPlace` (`COMMON_VTABLE_ENTRIES_DROPINPLACE = 0`),
- slot `1`: `MetadataSize` (`COMMON_VTABLE_ENTRIES_SIZE = 1`),
- slot `2`: `MetadataAlign` (`COMMON_VTABLE_ENTRIES_ALIGN = 2`).

`prepare_vtable_segments_inner` (`compiler/rustc_trait_selection/src/traits/vtable.rs` L37–187) linearizes the supertrait DAG of a principal trait into `VtblSegment` slices using an explicit DFS stack and a `PredicateSet` (`visited`, L90) to prevent diamond duplication:

1. Emit `VtblSegment::MetadataDSA` first (L87).
2. Dive along the first unvisited direct supertrait at each level with `emit_vptr_on_new_entry = false` (L89, L121–154).
3. While popping the stack (L157–182), compute `has_entries = supertrait_def_ids(tcx, tr).any(has_own_existential_vtable_entries)` (L162–163), emit `TraitOwnEntries { trait_ref: tr, emit_vptr: emit_vptr && has_entries && !no_trait_vptr }` (L165–168), and set `emit_vptr_on_new_entry |= has_entries` (L172). When advancing to a next sibling supertrait, push `(sibling, emit_vptr_on_new_entry, siblings)` (L177).
4. `vtable_entries` (L234–313) converts each segment's own dyn-compatible non-final methods (`own_existential_vtable_entries_iter`, L203–230) into `VtblEntry::Method(instance)` (via `expect_resolve_for_vtable`) or `VtblEntry::Vacant` when `impossible_predicates` holds (L279–286), followed by `VtblEntry::TraitVPtr(trait_ref)` if `emit_vptr` is true (L301–303).
5. `vtable_allocation_provider` (`rustc_middle/src/ty/vtable.rs` L84–156) allocates `Allocation::new(ptr_size * len, ptr_align, AllocInit::Uninit, ())` (L114), writing:
   - slot `0`: `Pointer::from(fn_alloc_id)` for `resolve_drop_glue(tcx, ty)` if `ty.needs_drop`, else **`Pointer::null()`** (L124–131);
   - slots `1`, `2`: `size` and `align` as pointer-sized unsigned integers (L133–134);
   - `Vacant`: `continue`—leaving the 8-byte slot `Uninit` (`undef` in LLVM IR, L135);
   - `Method(instance)`: function pointer provenance (L136–141);
   - `TraitVPtr(trait_ref)`: recursive `tcx.vtable_allocation((ty, Some(super_trait_ref)))` pointer (L142–147).

**Exact diamond and edge-case vtable tables observed in Specimen 1 LLVM IR (`x86_64-unknown-linux-gnu`, `ptr_size = 8`):**

For `trait Base { fn base_id(&self) -> u64; }`, `trait SuperA: Base { fn a_val(&self) -> u64; }`, `trait SuperB: Base { fn b_val(&self) -> u64; }`, `trait Diamond: SuperA + SuperB { fn d_val(&self) -> u64; }`:

| Slot | Byte offset | `<CopyLeaf as Diamond>` (`@vtable.3`) | `<DropLeaf as Diamond>` (`@vtable.4`) | `<DropLeaf as SuperB>` (`@alloc_dc53af2f...`) |
| :---: | :---: | :--- | :--- | :--- |
| `0` | `+0` | `0x0000000000000000` (`null`, `!needs_drop`) | `ptr @drop_glue::<DropLeaf>` | `ptr @drop_glue::<DropLeaf>` |
| `1` | `+8` | `8` (`size_of::<CopyLeaf>()`) | `16` (`size_of::<DropLeaf>()`) | `16` |
| `2` | `+16` | `8` (`align_of::<CopyLeaf>()`) | `8` (`align_of::<DropLeaf>()`) | `8` |
| `3` | `+24` | `ptr @<CopyLeaf as Base>::base_id` | `ptr @<DropLeaf as Base>::base_id` | `ptr @<DropLeaf as Base>::base_id` |
| `4` | `+32` | `ptr @<CopyLeaf as SuperA>::a_val` | `ptr @<DropLeaf as SuperA>::a_val` | `ptr @<DropLeaf as SuperB>::b_val` |
| `5` | `+40` | `ptr @<CopyLeaf as SuperB>::b_val` | `ptr @<DropLeaf as SuperB>::b_val` | *(end of vtable: 40 B)* |
| `6` | `+48` | `ptr @alloc_dbc5df7f...` (`TraitVPtr(SuperB)`) | `ptr @alloc_dc53af2f...` (`TraitVPtr(SuperB)`) | — |
| `7` | `+56` | `ptr @<CopyLeaf as Diamond>::d_val` | `ptr @<DropLeaf as Diamond>::d_val` | — |

Notice two subtle implementation details surfaced by LLVM IR inspection:
- **Secondary vtables are emitted as `@alloc_<hash>`, not `@vtable.<n>`:** `meth::get_vtable` (`compiler/rustc_codegen_ssa/src/meth.rs` L117) passes `Some("vtable")` to `static_addr_of` only for the top-level vtable constructed at a `T -> dyn Sub` unsizing site; nested `AllocId` pointers written into `TraitVPtr` slots by `vtable_allocation_provider` are lowered by `const_alloc_to_llvm` as anonymous `private unnamed_addr constant` `@alloc_<hash>` globals.
- **`VtblEntry::Vacant` emits literal `[8 x i8] undef`:** for `trait CondVacant<T> { fn always(&self) -> u64; fn only_if_copy(&self) -> u64 where T: Copy; }` instantiated at `CondVacant<String>`, `@vtable.5` is `<{ [24 x i8], ptr, [8 x i8] }> <{ ..., ptr @...always, [8 x i8] undef }>`.

### 4. Codegen of `PointerCoercion::Unsize`, prefix reuse vs. `TraitVPtr` indirection, and null-checked `dyn` drop

`Basis: source + execution`

At `Runtime(PostCleanup)` MIR, zero-cost prefix upcasts and indirect secondary-supertrait upcasts are syntactically identical (`support/probe_output/mir_excerpts.txt`): both `upcast_d_to_a` and `upcast_d_to_b` contain `_3 = move _4 as &dyn <Target> (PointerCoercion(Unsize, Implicit));`. Codegen diverges in `rustc_codegen_ssa::base::unsized_info` (`compiler/rustc_codegen_ssa/src/base.rs` L174–211):

1. **Same principal or principal erasure (`data_a.principal_def_id() == b_principal_def_id || b_principal_def_id.is_none()`, L178–198):** returns `old_info` directly (zero instructions). Confirmed on `upcast_erase_principal(&dyn (Diamond + Send) -> &dyn Send)`: zero loads, `auto_erase_reuses_vptr=true`, and dropping `Box<dyn Send>` still executes `<DropLeaf as Drop>::drop` (`drop_after_upcast_send=15012`).
2. **Prefix-reusable supertrait (`supertrait_vtable_slot((source, target)) == None`, L208–210):** returns `old_info` directly. Confirmed in LLVM IR (zero `getelementptr`, zero `load`) and runtime vtable-pointer equality for all seven prefix cases: `upcast_single_mid`, `upcast_single_base`, `upcast_d_to_a`, `upcast_d_to_base`, `upcast_b_to_base`, `upcast_empty_to_sec` (empty marker supertrait `EmptyMarker` listed before `SecondSuper`!), and `upcast_erase_principal`.
3. **Secondary supertrait (`supertrait_vtable_slot((source, target)) == Some(entry_idx)`, L204–207):** emits `load_vtable(bx, old_info, bx.type_ptr(), entry_idx * ptr_size, source, true)` (`compiler/rustc_codegen_ssa/src/meth.rs` L126–156). Confirmed verbatim in `upcast_d_to_b` (`llvm_ir_excerpts.txt` L26–33):
   ```llvm
   %0 = getelementptr inbounds i8, ptr %d.1, i64 48
   %_0.1 = load ptr, ptr %0, align 8, !invariant.load !5, !nonnull !5
   ```
   Runtime check confirms `diamond_b_uses_secondary_vptr=true`, `diamond_b_to_base_reuses_vptr=true`, exact method dispatch (`diamond_copy_dispatch_ok=true`, `drop_leaf_dispatch_ok=true`), and exact destructor invocation through upcasted `Box<dyn Diamond> -> Box<dyn SuperB>` (`drop_after_concrete=3009`, `drop_after_upcast_b=8010`).
4. **Null-checked virtual drop (`compiler/rustc_codegen_ssa/src/mir/block.rs` L623–690):** `codegen_drop` on `ty::Dynamic` loads slot `0` via `VirtualIndex::from_index(0).get_optional_fn` (`nonnull = false`), emits `icmp ne ptr %1, null`, and branches around the indirect call when slot `0` is null (`llvm_ir_excerpts.txt` L60–73). This matches `vtable_allocation_provider`'s null-slot optimization for `!needs_drop` types and was confirmed by dropping an upcasted `Box<dyn SuperB>` containing `CopyLeaf(200)` (`box_copy_b_val=203`, clean exit).

### 5. CGU partitioning, `Internal` vs. `External` linkage, absence of `LinkOnceODR`, and separate compilation

`Basis: source + execution`

`rustc_monomorphize::partitioning` (`compiler/rustc_monomorphize/src/partitioning.rs`) assigns each `MonoItem` an `InstantiationMode` (`compiler/rustc_middle/src/mono.rs` L29–50, L132–235), places `GloballyShared` roots into module-derived CGUs (L219–260), clones reachable `LocalCopy` items into every CGU that references them with `Linkage::Internal` (L266–280), merges CGUs down to `-C codegen-units=N`, and—unless `-C link-dead-code` is enabled (L177)—runs `internalize_symbols` (L515–601) to demote single-CGU-used hidden `GloballyShared` items from `Linkage::External` to `Linkage::Internal`.

Measured across Specimens 3 and 4:

| Experiment | Measured result (`probe_results.json`) | Source mechanism |
| :--- | :--- | :--- |
| **Multi-CGU `-C codegen-units=4 -O0`** (`multi_cgu_linkage.rs`) | 27 mono-items (`21 External`, `8 Internal` placements; **`0 OnceODR`**). `mod_a::always_inline_helper` placed in BOTH `cgu.1[Internal]` and `cgu.2[Internal]`; `mod_a::private_only_a` internalized to `cgu.1[Internal]`; cross-CGU `mod_a::shared_generic::<u64>` kept `cgu.1[External]`. | `mono.rs` L211–213 (`#[inline(always)]` → `LocalCopy`), `partitioning.rs` L276, L556–599 (`internalize_symbols`), L742–760 (`Linkage::External` default). |
| **Multi-CGU `-C codegen-units=4 -O2`** (`multi_cgu_linkage.rs`) | 16 mono-items (`9 External`, `7 Internal`; **`0 OnceODR`**). `always_inline_helper` inlined away; `private_only_a` stays `Internal`, `shared_generic::<u64>` stays `External`. | Same partitioning rules after MIR/LLVM inlining. |
| **No `LinkOnceODR` in Rust monomorphization** | `0` `OnceODR` entries across all specimens. In `rustc_codegen_llvm/src/mono_item.rs` L91, `LinkOnceODR`/`WeakODR` COMDAT handling is triggered only when an explicit `#[linkage = "..."]` attribute overrides linkage (`mono.rs` L237–245). | `partitioning.rs` L749–759 never produces `LinkOnceODR`; cross-crate symbol collisions for `GloballyShared { may_conflict: true }` are prevented by mangling disambiguators rather than COMDAT. |
| **Intra-crate & cross-crate duplicate vtables** | `same_vtable=false` in `multi_cgu_linkage.rs` (both `-O0` and `-O2`) AND in `sep_app.rs` (`rlib` + `bin`). | `meth::get_vtable` caches per CGU (`meth.rs` L111) and `static_addr_of_mut` sets `PrivateLinkage` + `UnnamedAddr::Global` (`consts.rs` L254–257). |
| **Separate compilation (`-Z share-generics=yes` vs. `no`)** (`sep_dep.rs` + `sep_app.rs`) | Upstream `dep` instantiates `poly_default::<u64>` and `poly_inline_never::<u64>`. Downstream `app` under `share-generics=yes` instantiates **only** `poly_default::<i32>` (reusing both `u64` items); under `share-generics=no`, `app` re-instantiates `poly_default::<u64>` locally **but still reuses upstream `poly_inline_never::<u64>`**. | `Instance::upstream_monomorphization` (`instance.rs` L211–217): `!share_generics() && inline != InlineAttr::Never` returns `None`, exempting `#[inline(never)]` items from local re-instantiation. |

### 6. Polymorphic recursion and `type_length_limit` termination guards

`Basis: source + execution`

Because generic functions can recurse with strictly growing type arguments, monomorphization collection is only semi-decidable without explicit bounds. `rustc` has two distinct bounds:

1. **`check_recursion_limit` (`collector.rs` L648–679):** tracks active DFS recursion depth per `DefId` along the current call chain (halving/quartering via `recursion_depth / 4` specifically for `LangItem::DropGlue`, L659–665) and aborts fatally when `!recursion_limit.value_within_limit(adjusted_recursion_depth)`. Specimen 5a (`poly_recursion_limit.rs`, `#![recursion_limit = "16"]`, `poly_rec::<(T, u8)>`) exits with status `1` and `error: reached the recursion limit while instantiating 'poly_rec::<((((..., u8), u8), u8), u8)>'`.
2. **`type_length_limit` (`instance.rs` L349–380, L529–533, L558–568):** guards against exponential type-size blowup (`(T, T)`) at shallow recursion depth, using a memoized `TypeVisitor` (`type_length`, caching subtrees > 16 nodes). Crucially, `Instance::try_resolve` checks `if tcx.sess.opts.unstable_opts.enforce_type_length_limit && ...` (L529), and `-Z enforce-type-length-limit` defaults to **`false`** on `rustc 1.98.0-nightly`. Specimen 5b (`type_length_limit.rs`, `#![type_length_limit = "1024"]`, `exp_blowup::<(T, T)>`) confirms both branches live:
   - Default flags: hits `reached the recursion limit while instantiating` (ignoring `#![type_length_limit = "1024"]`).
   - With `-Z enforce-type-length-limit=yes`: hits `reached the type-length limit while instantiating` immediately.

### 7. Kernel-checked Lean `v4.34.1` formalization: model and soundness theorems

`Basis: execution (Lean kernel) + derived`

`support/MonomorphVtableUpcastSoundness.lean` (2,027 lines, 82 top-level `theorem` declarations, 95 `def`/`abbrev`, 19 `inductive`/`structure`, zero imports beyond `Init`) formalizes both the vtable layout algorithm and the monomorphization reachability closure without equation-compiler recursion (using `List.foldr` and `Nat.repeat` so Lean emits zero `._unsafe_rec` helpers):

- **Vtable layout (`Section 3`):** `prepareVtableSegments H tr` implements the post-order DFS supertrait traversal (`dfsVisitStep` / `dfsVisitTrait`) with `visited` deduplication, `traitHasEntries`, and `emitVPtrOnNew` state threading; `vtableEntries H R ty tr` renders `[metadataDropInPlace (if ty.needsDrop then some (.dropGlue ty) else none), metadataSize ty.size, metadataAlign ty.align]` followed by each segment's `method`/`vacant` entries and optional `traitVPtr`; `firstMethodVtableSlot`, `virtualMethodSlot`, and `supertraitVtableSlot` mirror `rustc_trait_selection/src/traits/vtable.rs`.
- **Universal vtable and upcast soundness (`Section 4`):**
  - `virtualMethodSlot_sound`: for any `(H, R, ty, dynTr, methodTr, m, slot)`, if `virtualMethodSlot H dynTr methodTr m = some slot`, then `(vtableEntries H R ty dynTr)[slot]?` equals the exact concrete resolution `R ty methodTr m` (`method` or `vacant`).
  - `supertraitVtableSlot_vptr_sound`: whenever `supertraitVtableSlot H srcTr targetTr = some (some idx)`, `(vtableEntries H R ty srcTr)[idx]? = some (VtblEntry.traitVPtr targetTr)`.
  - `prefix_vtable_entries_agree`: whenever `SegmentsPrefix (prepareVtableSegments H targetTr) (prepareVtableSegments H srcTr)`, every slot index valid in `vtable(ty, targetTr)` agrees identically in `vtable(ty, srcTr)`.
  - `upcast_dispatch_and_drop_sound`: for every faithful vtable store, prefix-coherent upcast `srcTr → targetTr`, and target virtual method `m` at `slot`, `upcastVtable` produces a vtable `dstVt` whose `slot` resolves to `R ty methodTr m` and whose slot `0` resolves to `MetadataDropInPlace` (`some (.dropGlue ty)` iff `ty.needsDrop`, else `none`).
- **Supertrait coverage & collector link-completeness (`Sections 5–6`):**
  - `vtableCollectedMethods_covers_supertrait`: whenever `SupertraitSegmentsCovered H srcTr superTr` holds (proved concretely for `Diamond → SuperB` in `diamond_covers_superB_segments`), every `VtblEntry.method inst` in `vtableEntries H R ty superTr` is already contained in `vtableCollectedMethods H R ty srcTr`—mechanizing why `collector.rs` L1235–1238 is sound to skip `VtblEntry::TraitVPtr`.
  - `monoReachable_monotone_roots`: enlarging `roots` (`Lazy ⊆ Eager`) monotonically enlarges `MonoReachable`.
  - `vtableShim_reaches_item`, `reifyShim_reaches_item`, `closureOnceShim_reaches_item`, `fnPtrShim_reaches_item`: every collected compiler shim transitively pulls its underlying concrete `item` into `MonoReachable`.
  - `execStepDec_no_fault` & `collector_link_complete`: over an operational link-checking machine (`execStepDec` / `execStepsDec`) modeling direct calls, `reifyFnPtr` (tracked and untracked), `reifyVirtualFnPtr`, `unsizeToDyn`, `upcastDyn` (both prefix reuse and `TraitVPtr` indirection), `virtualDispatch`, `dropConcrete`, `reifyDropFnPtr`, `dropDyn` (with null-check on slot `0`), `closureAsFnOnce`, and `fnPtrAsFnTrait`, if `ProgramWellTyped P` and `CollectorComplete P L` hold (every `MonoReachable` item is in `L.symbols` and every `VtableReachable` vtable is in `L.vtableOf`), then for **every fuel bound `fuel : Nat`** and well-typed trace (`TraceTyped P L fuel st`), execution never returns `StepOutcome.fault err` (`missingSymbol`, `missingVtable`, or `badSlotEntry`).
- **Concrete diamond & empty-marker theorems (`Section 7`):** `diamond_upcast_to_superA_dispatch_sound`, `diamond_upcast_to_superB_dispatch_sound`, `diamond_upcast_superB_then_base_sound`, and `empty_marker_upcast_zero_cost_sound` hold universally for all `ty : ConcreteTy` (`CopyLeaf` and `DropLeaf` included), and `copyLeaf_diamond_vtable_exact`, `dropLeaf_diamond_vtable_exact`, `dropLeaf_superB_vtable_exact`, `dropLeaf_vacant_vtable_exact` match the live LLVM IR slot tables slot-for-slot.

### 8. Two sharpness counterexamples (CE1 and CE2)

`Basis: execution (Lean kernel) + derived`

Both counterexamples prove that dropping either the `TraitVPtr` upcast indirection or shim/drop-glue collector edges breaks runtime soundness:

- **CE1 — Reusing the subtrait vtable pointer for a non-principal supertrait corrupts dispatch (`Section 8`):**
  - `ce1_superB_method_slot_is_4`: in `vtable(ty, SuperB)`, `SuperB::b_val` resides at slot `4`.
  - `ce1_wrong_prefix_reuse_dispatches_to_superA_not_superB`: for every `ty : ConcreteTy`, passing `buggyUpcastReuseAlways (vtableEntries H R ty trDiamond)` as a `dyn SuperB` vtable causes virtual dispatch at slot `4` to resolve to `VtblEntry.method (.item fnAVal ty.id)` (`SuperA::a_val`), which is provably unequal to `VtblEntry.method (.item fnBVal ty.id)` (`SuperB::b_val`).
  - `ce1b_wrong_prefix_reuse_reads_traitVPtr_slot`: on a 3-supertrait hierarchy `trTri_ce : trA_ce (1 method) + trB_ce (1 method) + trC_ce (3 methods)`, `trC_ce`'s third method `mC2` has `virtualMethodSlot = some 5`, while slot `5` of `vtable(ty, trTri_ce)` holds **`VtblEntry.traitVPtr trB_ce`**—a read-only vtable data pointer rather than a function pointer, causing type/control-flow corruption (`RuntimeFault.badSlotEntry 5`).
- **CE2 — Omitting `ReifyShim` or `DropGlue` from `MonoReachable` causes deterministic `missingSymbol` faults (`Section 8`):**
  - **CE2a (`ReifyShim`):** in `progReifyTrackCaller` (coercing a `#[track_caller]` function item to a `fn` pointer), `ce2a_reify_shim_is_mono_reachable` proves `reifyShim fnTrackedFree 0 locTrackedDef` is in `MonoReachable`, `ce2a_complete_collector_succeeds` proves execution halts cleanly when emitted, and `ce2a_omitting_reify_shim_faults` proves that emitting only the raw `item fnTrackedFree 0` without `reifyShim` faults with `StepOutcome.fault (RuntimeFault.missingSymbol (InstanceKind.reifyShim fnTrackedFree 0 locTrackedDef))`.
  - **CE2b (`DropGlue`):** in `progDynUpcastDrop` (unsizing `tyDropLeaf` to `dyn Diamond`, upcasting to `dyn SuperB`, dispatching slot `4`, and executing `dropDyn`), `ce2b_drop_glue_is_mono_reachable` proves `dropGlue tyDropLeaf` is collected during `unsizeToDyn`, `ce2b_complete_collector_succeeds` proves execution halts cleanly, and `ce2b_omitting_drop_glue_faults_on_upcast_drop` proves that omitting `dropGlue tyDropLeaf` while emitting all trait methods faults on `dropDyn` with `RuntimeFault.missingSymbol (InstanceKind.dropGlue tyDropLeaf)`. By sharp contrast, `copy_dyn_drop_succeeds_without_drop_glue_symbol` proves that `tyCopyLeaf` (`needsDrop = false`) halts cleanly without any `dropGlue` symbol because slot `0` is `null`, while `reify_noop_drop_is_mono_reachable` vs. `direct_noop_drop_emits_no_edge` captures the `collector.rs` L1019–1026 indirect-reification distinction.

### 9. Correspondence between the Lean model and live `rustc`

`Basis: derived (from Findings 1–8)`

| Compiler behavior (`rustc 1.98.0-nightly`) | Empirical witness (`probe_results.json` / `llvm_ir_excerpts.txt`) | Lean theorem (`MonomorphVtableUpcast.DiamondExample`) |
| :--- | :--- | :--- |
| Diamond `<CopyLeaf as Diamond>` 8-slot layout (`null` drop, `8`, `8`, `Base`, `SuperA`, `SuperB`, `TraitVPtr(SuperB)`, `Diamond`) | `@vtable.3` + `@alloc_dbc5df7f...`, `llvm_ir::copy_diamond_vtable_null_drop_and_trait_vptr` | `diamond_segments_exact`, `copyLeaf_diamond_vtable_exact` |
| Diamond `<DropLeaf as Diamond>` 8-slot layout (`drop_glue`, `16`, `8`, ..., `TraitVPtr(SuperB)`, `Diamond`) | `@vtable.4` + `@alloc_dc53af2f...`, `llvm_ir::drop_diamond_vtable_nonnull_drop_and_trait_vptr` | `dropLeaf_diamond_vtable_exact`, `dropLeaf_superB_vtable_exact` |
| Zero-cost prefix reuse for `Diamond → SuperA`, `Diamond → Base`, `SuperB → Base` | `llvm_ir::zero_cost_upcast_d_to_a`, `_d_to_base`, `_b_to_base`; `vtable::diamond_prefix_vs_secondary_vptr` | `diamond_to_superA_prefix_reuse`, `diamond_upcast_to_superA_dispatch_sound`, `diamond_upcast_superB_then_base_sound` |
| Single load at `+48` (`slot 6 * 8`) for `Diamond → SuperB` | `llvm_ir::upcast_d_to_b_loads_offset_48_invariant_nonnull` | `diamond_to_superB_vptr_slot_6`, `diamond_upcast_to_superB_dispatch_sound` |
| Empty marker supertrait preserves zero-cost prefix for `SecondSuper` | `@vtable.2`, `llvm_ir::zero_cost_upcast_empty_to_sec`, `vtable::empty_marker_prefix_reuse` | `subAfterEmpty_segments_exact`, `subAfterEmpty_to_secondSuper_prefix_reuse`, `empty_marker_upcast_zero_cost_sound` |
| `VtblEntry::Vacant` occupies a slot (`[8 x i8] undef`) | `@vtable.5`, `llvm_ir::vacant_slot_is_undef` | `dropLeaf_vacant_vtable_exact` |
| Nullable slot-0 drop check skips call for `!needs_drop` and invokes `drop_glue` for `DropLeaf` | `llvm_ir::dyn_drop_glue_null_checks_slot_0`, `vtable::drop_dispatch_through_upcasted_boxes` | `copy_dyn_drop_succeeds_without_drop_glue_symbol`, `ce2b_complete_collector_succeeds` |
| `ReifyShim` required for `#[track_caller]` fn pointer; reified `drop_in_place::<CopyNoDrop>` collected | `shims::all_instance_kinds_collected_in_lazy`, `shims::runtime_values_and_track_caller_lines` | `ce2a_reify_shim_is_mono_reachable`, `ce2a_omitting_reify_shim_faults`, `reify_noop_drop_is_mono_reachable`, `direct_noop_drop_emits_no_edge` |

There is no automated MIR-to-Lean extractor in this package; the Lean definitions mirror the compiler algorithms and specimen hierarchies by construction.

### 10. Source drift check (`14210df0` → `c7d5ba59`) and Anneal trusted MIR boundary

`Basis: source`

**Later upstream `rust-lang/rust` snapshot (`14210df0e` → `c7d5ba59d`, 2026-05-31 → 2026-11-20):**
- `compiler/rustc_middle/src/ty/vtable.rs`: only a 1-line refactor (`tcx.data_layout.pointer_align().abi` → `tcx.data_layout.pointer_align()`). `VtblEntry`, `COMMON_VTABLE_ENTRIES`, null slot-0 drop optimization, `Vacant` uninit slots, and recursive `TraitVPtr` allocation are **unchanged**.
- `compiler/rustc_trait_selection/src/traits/vtable.rs` (+71/−26 lines): `prepare_vtable_segments_inner` and `supertrait_vtable_slot` retain the identical prefix-reuse + `emit_vptr_on_new_entry |= has_entries` algorithm; `explicit_super_predicates_of` was renamed to `explicit_super_clauses_of`, `impossible_predicates` became `instantiate_and_check_impossible_clauses`, and `first_method_vtable_slot` changed return type from `usize` to `Option<usize>` for error recovery.
- `compiler/rustc_monomorphize/src/collector.rs` (+198/−80 lines) and `partitioning.rs` (+72/−35 lines): active refactoring occurred, so line numbers in Findings 1 and 5 are pinned strictly to `14210df0e`.

**Anneal trusted MIR ingestion boundary (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`):**
- `trusted/lean/Trusted/MirAst.lean` (`inductive MirTy`, L308–320): `FnDef`, `FnPtr`, `Dynamic`, `Closure`, `CoroutineClosure`, and `Coroutine` all map fail-closed to `MirTy.unsupported`.
- `trusted/lean/Trusted/MirAst.lean` (`inductive Rvalue`, L612–628): `Rvalue::Cast` (which carries `PointerCoercion::Unsize`, `PointerCoercion::ReifyFnPointer`, and `PointerCoercion::ClosureFnPointer`) maps to `Rvalue.unsupported`.
- `trusted/lean/Trusted/MirAst.lean` (`inductive TerminatorKind`, L780–795) and `Trusted/MirSemantics.lean` (`evalTerminator`, L1568): `Drop` and indirect `Call` map to `TerminatorKind.unsupported`, and direct `.call` steps to `.fault .unsupported`.

Thus, verifying Rust code that exercises `dyn` dispatch, trait upcasting, or monomorphized shims in Anneal requires extending `Trusted.MirAst` and `Trusted.MirSemantics` with wide-pointer values `(dataPtr, vtablePtr)`, immutable vtable allocations (including nullable slot-0 drop pointers and `TraitVPtr` slots), `PointerCoercion::{Unsize, ReifyFnPointer, ClosureFnPointer}` rvalues, and indirect/virtual `Call` and `Drop` terminators.

### 11. Analytical dimensions scorecard (`L1`–`L6`, `C1`–`C2`, `V1`–`V4`)

| ID | Dimension | Basis | Result |
| :--- | :--- | :--- | :--- |
| `L1` | Authoring and proof velocity | execution (artifact size only) | Elapsed authoring time: **not measured**. Artifact size (`support/MonomorphVtableUpcastSoundness.lean`): 2,027 lines, 90,934 bytes, 82 top-level `theorem`, 95 `def`/`abbrev`, 19 `inductive`/`structure` declarations. |
| `L2` | Toolchain / TCB build time | none | **not measured** (pre-installed released Lean `v4.34.1` and nightly `rustc 1.98.0-nightly` binaries used; zero external Lean library dependencies beyond `Init`). |
| `L3` | Pass / certificate synthesis latency | none | **not measured**: `rustc`'s monomorphization pass runtime was not micro-benchmarked separately, and the Lean model does not synthesize certificates from live MIR dumps. |
| `L4` | Generated code performance | execution (static IR + single-run checks only) | Runtime throughput: **not measured**. Static IR overhead confirmed on `x86_64-unknown-linux-gnu`: `0` loads for prefix-reusable upcasts (`SuperA`, `Base`, `SecondSuper` after empty marker, principal erasure); `1` `gep +8*6` + `!invariant.load !nonnull` load for diamond secondary supertrait `SuperB`; `8` bytes per `TraitVPtr` slot plus `40` bytes for the `<T as SuperB>` secondary vtable allocation. |
| `L5` | Checking latency and throughput | execution | Synchronous Lean `v4.34.1` kernel check (`-DElab.async=false -Ddebug.skipKernelTC=false`): `10.550 s` wall clock (`MonomorphVtableUpcastSoundness.lean`); exhaustive kernel environment audit (`MonomorphVtableUpcastAudit.lean`): `5.246 s` wall clock. Throughput on crate-scale MIR graphs: **not measured**. |
| `L6` | RAM and artifact footprint | execution | Peak resident memory (`os.wait4` `ru_maxrss`): `590,964 kB` (module kernel check) and `1,614,740 kB` (audit importing `Lean`); transient `.olean` size `3,816,840 bytes` (deleted after audit, not shipped). |
| `C1` | Specification and assumption auditability | execution (audit) | `0` imports beyond `Init`; transitive axioms used across all `416` kernel theorem constants: `[propext, Quot.sound]` (`281` of `416` use zero axioms); `0` `axiom`, `0` `opaque`, `0` non-`safe` (`partial`/`unsafe`) definitions, `0` `._unsafe_rec` helpers across all `899` module constants; `0` occurrences of all 13 forbidden source tokens (`sorry`, `admit`, `Classical`, `omega`, `bv_decide`, `native_decide`, `partial def`, `_unsafe_rec`, `axiom`, `opaque`, `unsafe`, `noncomputable`, `@[extern]`). |
| `C2` | Orthogonality and simplicity | derived | One segment builder (`prepareVtableSegments`) drives both `vtableEntries`, `firstMethodVtableSlot`, and `supertraitVtableSlot`; one `MonoProgram` / `opUsedMonoItems` specification drives both `MonoReachable` and the operational fault-checking machine `execStepDec`; zero equation-compiler recursion (`List.foldr` and `Nat.repeat` only). |
| `V1` | Adequacy, mutation and non-vacuity | execution (Lean kernel + live `rustc`) | `38 / 38` automated `rustc` probe checks pass across 7 Rust specimens (native runs, LLVM IR, `Runtime(PostCleanup)` MIR, `-Z print-mono-items=yes`, multi-CGU, separate compilation, negative recursion/type-length compiles). Lean model proves universal soundness theorems plus 3 concrete non-vacuous negative mutants (CE1 wrong prefix reuse on diamond `SuperB`, CE1b `TraitVPtr` data-slot collision on 3-supertrait hierarchy, CE2a missing `ReifyShim`, CE2b missing `DropGlue`) and positive controls (`copy_dyn_drop_succeeds_without_drop_glue_symbol`, `empty_marker_upcast_zero_cost_sound`). |
| `V2` | Differential fuzzing | none | **not measured**: no random trait-DAG or generic-program fuzzer was run; compiler-to-model correspondence rests on 8 hand-authored shapes (Finding 9). |
| `V3` | Weak memory / crash / silicon | derived | **known not to apply** to the monomorphization collector and constant immutable vtable layout (compile-time graph closure and read-only constant tables). Native execution was observed on one `x86_64-unknown-linux-gnu` host only. |
| `V4` | Held-out ecosystem replay | none | **not examined**: no external crates.io crate or sysroot (`core`/`alloc`/`std`) monomorphization census was measured in this package. |

## Boundaries

**Not examined.**

- **KCFI and CFI vtable metadata:** `ReifyReason::{FnPtr, Vtable}` separation under `-Z sanitizer=kcfi` (`instance.rs` L38–58, L593, L604–621, L649), `-Z virtual-function-elimination` with `-C lto=fat` (`meth.rs` L136–146 emitting `llvm.type.checked.load`), and vcall visibility / debuginfo (`meth.rs` L119–120).
- **Async drop and coroutine-closure shims:** `InstanceKind::{ConstructCoroutineInClosureShim, FutureDropPollShim, AsyncDropGlueCtorShim, AsyncDropGlue}`, `ThreadLocalShim`, `CloneShim`, and `FnPtrAddrShim` were inspected in `instance.rs`/`shim.rs` for taxonomy completeness but not exercised in live specimens or modeled in Lean.
- **Custom `CoerceUnsized` smart-pointer fields and composite unsized structs:** `find_tails_for_unsizing` (`collector.rs` L1134–1187) and `unsize_ptr` (`base.rs` L238–263) handle `Rc`/`Arc`/`Pin`/struct-tail unsizing; Specimen 1 exercised `&dyn` and `Box<dyn>` only.
- **CTFE / promoted-constant `GlobalAlloc::VTable` collection:** `collect_alloc` (`collector.rs` L1257–1296) walks provenance pointers inside evaluated `static`/`const` allocations including `GlobalAlloc::VTable`; this path was inspected in source but not probed dynamically.
- **Cross-DSO `cdylib` / `dylib` symbol visibility and ThinLTO cross-CGU importing:** Specimen 4 tested `rlib` + `bin` static linking; `cdylib`/`dlopen` vtable duplication and `-C lto=thin|fat` cross-CGU deduplication were not run here.
- **Non-`x86_64` targets:** 32-bit targets (where slot byte offsets halve from `8*k` to `4*k`), Windows MSVC/GNU linkage details, and `rustc_codegen_cranelift` / `rustc_codegen_gcc` vtable lowering were not executed.

**Unknown.**

- Whether any malformed trait hierarchy or cyclic supertrait bound surviving earlier type-checking errors can trigger the `delayed_bug` fallback in `supertrait_vtable_slot` (`vtable.rs` L434–443) or `first_method_vtable_slot` without an earlier hard error; this was not fuzzed.
- Whether LLVM's `MergeConstants` / linker ICF merges identical `private unnamed_addr constant` vtable globals under `-C lto=fat` or `--icf=safe` on `rust-lld`; our probes ran with default linking and `-C lto=off`.

**Known not to apply.**

- **Vtable pointer identity is not a valid concrete-type identity check:** Specimen 3 (`multi_cgu_linkage.rs`, `-C codegen-units=4` at both `-O0` and `-O2`) and Specimen 4 (`sep_dep.rs` + `sep_app.rs`) empirically falsify vtable uniqueness (`same_vtable=false`). Any compiler optimization or unsafe code assuming two `&dyn Trait` values for the same concrete type `T` share identical vtable addresses is unsound without a whole-program uniqueness guarantee.
- **Vtable layout is not stabilized:** RFC 3324 explicitly reserves the compiler's right to change vtable slot ordering, flat vs. pointer-based layouts, and empty-trait optimizations.
- **The Lean `collector_link_complete` theorem does not apply to ill-typed programs or unclosed collectors:** it requires `ProgramWellTyped P` (in particular `PrefixCoherent` and `SupertraitSegmentsCovered`) and `CollectorComplete P L`, as witnessed by CE1, CE2a, and CE2b.
- **The Lean model does not connect to Anneal's `Trusted.MirSemantics`:** at `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `Dynamic`, `Cast`, `Drop`, and `Call` are `.unsupported` there (Finding 10).

**Unsupported.**

- Passing `-Z print-mono-items=lazy` or `-Z print-mono-items=eager` is rejected by `rustc 1.98.0-nightly` (boolean flag only).
- `#![feature(unsized_fn_params)]`, `-Z print-mono-items`, `-Z dump-mir`, `-Z share-generics`, `-Z enforce-type-length-limit`, and `-Z no-trait-vptr` are unstable nightly-only features/flags.

**Stronger conclusions the evidence does not establish.**

- *"`rustc`'s monomorphization collector and vtable codegen are formally verified."* False: the Lean proof verifies a clean-room model (`MonomorphVtableUpcast`), not the Rust implementation in `compiler/rustc_monomorphize` or `compiler/rustc_codegen_llvm`.
- *"`prepare_vtable_segments_inner` is proved `PrefixCoherent` and `SupertraitSegmentsCovered` for all acyclic trait DAGs."* Not proved universally in Lean: the Lean development proves `upcast_dispatch_and_drop_sound` and `collector_link_complete` *parametrically* over any hierarchy satisfying `PrefixCoherent` and `SupertraitSegmentsCovered`, and discharges those hypotheses concretely for the diamond and empty-marker hierarchies (`diamond_prefix_superA`, `diamond_prefix_base`, `superB_prefix_base`, `diamond_covers_superB_segments`). A general graph-theoretic proof that `dfsVisitTrait` establishes `PrefixCoherent` and `SupertraitSegmentsCovered` for arbitrary finite DAGs remains future work.
- *"Trait upcasting always has negligible binary-size cost."* Not measured on real crates; our measurements cover synthetic specimens only.

## Evidence

**Upstream source, `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`** (commit dated `2026-05-31`, equal to `rustc -Vv` `commit-hash`; verified in `support/pin_receipt.json` on `2026-11-21`):

| Path | Lines | Content |
| :--- | :--- | :--- |
| `compiler/rustc_monomorphize/src/collector.rs` | 1–207, 243–247, 354–679, 726–973, 975–1091, 1134–1296, 1302–1432, 1457–1844 | Collector architecture doc, `MonoItemCollectionStrategy`, `collect_items_rec`, `check_recursion_limit`, `MirUsedCollector`, `visit_fn_use`, `visit_instance_use`, `should_codegen_locally`, `find_tails_for_unsizing`, `create_mono_items_for_vtable_methods`, `collect_alloc`, `collect_items_of_instance`, `RootCollector`, `collect_crate_mono_items` |
| `compiler/rustc_monomorphize/src/partitioning.rs` | 143–310, 515–601, 625–687, 742–957, 1131–1140, 1209–1217 | `partition`, `place_mono_items`, `internalize_symbols`, `characteristic_def_id_of_mono_item`, `mono_item_linkage_and_visibility`, `mono_item_visibility`, `collect_and_partition_mono_items` (`link_dead_code` → `Eager`) |
| `compiler/rustc_middle/src/ty/vtable.rs` | 12–156 | `VtblEntry`, `COMMON_VTABLE_ENTRIES`, `vtable_min_entries`, `vtable_allocation_provider` (nullable slot 0, `Vacant` uninit, recursive `TraitVPtr`) |
| `compiler/rustc_trait_selection/src/traits/vtable.rs` | 18–454 | `VtblSegment`, `prepare_vtable_segments_inner`, `own_existential_vtable_entries_iter`, `vtable_entries`, `first_method_vtable_slot`, `supertrait_vtable_slot` |
| `compiler/rustc_middle/src/ty/instance.rs` | 33–347, 349–380, 500–779, 857–943 | `Instance`, `ReifyReason`, `InstanceKind` (15 variants), `upstream_monomorphization`, `requires_inline`, `requires_caller_location`, `type_length`, `try_resolve`, `resolve_for_fn_ptr`, `expect_resolve_for_vtable`, `resolve_closure`, `resolve_drop_glue` |
| `compiler/rustc_middle/src/mono.rs` | 29–60, 132–282 | `InstantiationMode`, `MonoItem`, `instantiation_mode`, `explicit_linkage`, `is_instantiable` |
| `compiler/rustc_ty_utils/src/instance.rs` | 19–102, 104–413 | `resolve_instance_raw` (`DropGlue` `Some`/`None`), `resolve_associated_item` (`Virtual`, `FnPtrShim`, `ClosureOnceShim`, `CloneShim`) |
| `compiler/rustc_mir_transform/src/shim.rs` | 67–199, 303–405, 811–980 | `make_shim`, `build_drop_shim`, `build_call_shim` (`VTableShim` `*mut Self` rewrite, `ReifyShim`, `ClosureOnceShim`, `FnPtrShim`) |
| `compiler/rustc_codegen_ssa/src/meth.rs` | 10–71, 103–156 | `VirtualIndex::{get_fn, get_optional_fn}`, `get_vtable` (per-CGU cache + `static_addr_of`), `load_vtable` (`!invariant.load`, `!nonnull`, VFE) |
| `compiler/rustc_codegen_ssa/src/base.rs` | 161–315 | `unsized_info` (prefix reuse vs. `supertrait_vtable_slot` load, principal erasure), `unsize_ptr`, `coerce_unsized_into` |
| `compiler/rustc_codegen_ssa/src/mir/rvalue.rs` | 416–455 | `PointerCoercion::{ReifyFnPointer, ClosureFnPointer, Unsize}` codegen |
| `compiler/rustc_codegen_ssa/src/mir/block.rs` | 605–690, 1229–1278 | `codegen_drop` (`dyn` slot-0 `get_optional_fn` + null check `is_not_null`) and `InstanceKind::Virtual` receiver peeling & dispatch |
| `compiler/rustc_codegen_llvm/src/consts.rs` | 236–286, 770–789 | `static_addr_of_mut` (`PrivateLinkage`, `UnnamedAddr::Global`), `static_addr_of_impl`, `static_addr_of` |
| `compiler/rustc_codegen_llvm/src/mono_item.rs` | 59–103 | `predefine_fn`, `predefine_without_aliases` (`LinkOnceODR`/`WeakODR` COMDAT handling) |
| `src/doc/rustc-dev-guide/src/backend/monomorph.md` | 1–79 | Descriptive upstream overview of collector and CGU partitioning |

Absent paths verified HTTP 404 at `14210df0e`: `compiler/rustc_codegen_llvm/src/meth.rs` and `compiler/rustc_middle/src/mir/mono.rs`.

**Later upstream drift snapshot (`rust-lang/rust@c7d5ba59d8e11ee2e2204b173458eec4cb41c973`, dated `2026-11-20`):** diffed against `14210df0e` on `compiler/rustc_middle/src/ty/vtable.rs`, `compiler/rustc_trait_selection/src/traits/vtable.rs`, and `compiler/rustc_monomorphize/src/collector.rs` (Finding 10).

**Specifications and RFCs:**
- `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`: `src/type-coercions.md` (rules `coerce.types.unsize`, `coerce.unsize.trait-object`, `coerce.unsize.trait-upcast`) and `src/types/trait-object.md`.
- `rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`: `text/3324-dyn-upcasting.md` (RFC 3324, hybrid flat+pointer vtable design attributed to Mario Carneiro, implemented in PR `#86461`; explicit non-stabilization of vtable layout) and `text/2580-ptr-meta.md`.

**Anneal trusted MIR (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`):** `trusted/lean/Trusted/MirAst.lean` L308–320, L612–628, L780–795; `trusted/lean/Trusted/MirSemantics.lean` L1568, L1693.

**Preserved execution and formalization artifacts (all generated on `2026-11-21` on `x86_64-unknown-linux-gnu`):**

| File | Content |
| :--- | :--- |
| `support/specimens/vtable_diamond_upcast.rs` | Single-chain, diamond (`CopyLeaf` & `DropLeaf`), empty-marker, auto-trait erasure, `Vacant`, and upcasted `Box<dyn>` drop specimen (sha256 `8c1d4bfc3313e01304ab5b70b6acfc95837b5fd8b500eeda27305e6cc184d459`) |
| `support/specimens/shims_and_mono_collection.rs` | `VTableShim`, 3× `ReifyShim`, `ClosureOnceShim`, 2× `FnPtrShim`, reified `DropGlue(_, None)`, and Lazy vs. Eager delta specimen (sha256 `1e28b06a619e357877fb7031c0e78f707bc391c3362ad08149aa1e72b9328a24`) |
| `support/specimens/multi_cgu_linkage.rs` | 4-CGU linkage (`Internal`/`External`, `0` `LinkOnceODR`) and intra-crate duplicate private vtables specimen (sha256 `f6358a100a9be0c0e453242a1e95c89fbe34154ddbb71aad990d6e4dbc11a927`) |
| `support/specimens/sep_dep.rs`, `support/specimens/sep_app.rs` | Separate-compilation `rlib` + `bin` (`-Z share-generics=yes|no`, `#[inline(never)]` reuse, cross-crate duplicate vtables; sha256 `9955fd55e2562da6ff798ce7f8dec252c41f247659ca495199692dce821f30c0`, `98b3c95a17bd77bee5f59f4f32093456e97b7d35d819d7ded9f230397656056f`) |
| `support/specimens/poly_recursion_limit.rs`, `support/specimens/type_length_limit.rs` | Negative-compile recursion-limit and type-length-limit specimens (sha256 `e58273516309b766e172f12d011ac3ce59ffd646f4c92c0d5884f477ca36f3a9`, `d8405ffc76f63f263e42aa76dc05544a2a6cf38df333293a298c27e065ddf1ee`) |
| `support/probe_monomorph_vtable_upcasting.py` | Standalone Python 3.10+ stdlib-only driver executing all 38 compiler, IR, MIR, and runtime checks |
| `support/probe_output/probe_results.json`, `probe_summary.md` | Machine-readable results (`38 / 38` passed) and markdown table summary |
| `support/probe_output/llvm_ir_excerpts.txt`, `mir_excerpts.txt`, `mono_items_summary.txt` | Verbatim `@vtable.*` / `@alloc_*`, upcast LLVM IR, null-checked `dyn` drop IR, `VTableShim`/`ReifyShim` IR, `Runtime(PostCleanup)` MIR, and mono-item summaries |
| `support/MonomorphVtableUpcastSoundness.lean` | Standalone Lean `v4.34.1` formalization (sha256 `c04e06df5f8221e3c4648e3994c6494906a6953f3a5239eba471722775c65817`) |
| `support/MonomorphVtableUpcastAudit.lean` | Kernel environment auditor checking axioms, safety, opacity, and `_unsafe_rec` helpers (sha256 `7a994daf958cb2d2cee8518f48d2ead19d39beff2fae2856bd8e5d8ad356b68a`) |
| `support/check_lean.py`, `support/lean_check_receipt.json` | Synchronous Lean check + forbidden-token scan + environment audit runner and receipt (`passed: true`, `0` violations, `[Quot.sound, propext]`) |
| `support/verify_pins.py`, `support/pin_receipt.json` | Pin verifier checking all 6 40-hex commits and all 24 upstream file paths (`6/6` commits, `24/24` files verified) |

**Peer-reviewed literature** (context for multiple-inheritance dispatch tables, monomorphization, and Rust formalization; none re-derived here):

- R. Ducournau. "Implementing Statically Typed Object-Oriented Programming Languages." *ACM Computing Surveys* 43(3), Article 18 (April 2011), pp. 18:1–18:48. doi:10.1145/1922649.1922655. Comprehensive taxonomy of single- vs. multiple-inheritance dispatch tables, prefix sharing, and subobject/vptr pointer adjustments.
- T. Ramananandro, G. Dos Reis, X. Leroy. "Formal Verification of Object Layout for C++ Multiple Inheritance." POPL 2011, pp. 67–80. doi:10.1145/1926385.1926395. Mechanized Coq proof of object and vtable layout correctness under non-virtual and diamond virtual inheritance.
- D. Wasserrab, T. Nipkow, G. Snelting, F. Tip. "An Operational Semantics and Type Safety Proof for Multiple Inheritance in C++." OOPSLA 2006, pp. 345–362. doi:10.1145/1167473.1167503. Isabelle/HOL formalization of multiple-inheritance subobject dispatch and cast soundness.
- A. Tolmach, D. Oliva. "From ML to Ada: Strongly-Typed Language Interoperability via Source Translation." *Journal of Functional Programming* 8(4), July 1998, pp. 367–412. doi:10.1017/S0956796898003086. Foundational whole-program monomorphization strategy eliminating parametric polymorphism by specialization over concrete instantiations.
- R. Jung, J.-H. Jourdan, R. Krebbers, D. Dreyer. "RustBelt: Securing the Foundations of the Rust Programming Language." POPL 2018 (PACMPL 2, Article 66). doi:10.1145/3158154. Semantic soundness framework for Rust's type system over $\lambda_{\text{Rust}}$.
- S. Ho, J. Protzenko. "Aeneas: Rust Verification by Functional Translation." ICFP 2022 (PACMPL 6, Article 116). doi:10.1145/3547647. Translation of MIR programs to pure functional verification targets, illustrating the verification gap around dynamic dispatch and monomorphized shims.

## Revalidation

**Cheapest discriminating checks, in order.**

1. *Check compiler identity:* `rustc -Vv` must print `commit-hash: 14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`. For another compiler revision, diff `compiler/rustc_middle/src/ty/vtable.rs`, `compiler/rustc_trait_selection/src/traits/vtable.rs` (`prepare_vtable_segments_inner`, `supertrait_vtable_slot`), `compiler/rustc_codegen_ssa/src/base.rs` (`unsized_info`), and `compiler/rustc_monomorphize/src/{collector.rs,partitioning.rs}` against that commit.
2. *Rerun the 38-check `rustc` probe* (~6 seconds; requires nightly `rustc` and Python 3.10+ stdlib only):
   ```console
   python3 support/probe_monomorph_vtable_upcasting.py --out /tmp/mono_vtable_probe
   ```
   Exits non-zero if any of the 38 checks fails. Key discriminating checks: `llvm_ir::upcast_d_to_b_loads_offset_48_invariant_nonnull` and `llvm_ir::zero_cost_upcast_empty_to_sec` (Findings 3–4), `llvm_ir::dyn_drop_glue_null_checks_slot_0` and `llvm_ir::vacant_slot_is_undef` (Findings 3–4), `shims::all_instance_kinds_collected_in_lazy` and `shims::eager_adds_dead_fn_unused_drop_and_default_trait_method` (Findings 1–2), `cgu::zero_linkonce_odr_emissions`, `cgu::intra_crate_duplicate_private_vtables`, and `sep::share_generics_no_reinstantiates_default_but_still_reuses_inline_never` (Finding 5), and `limits::type_length_limit_not_enforced_by_default` (Finding 6).
3. *Recheck the Lean `v4.34.1` model and axiom audit* (~16 seconds; requires Lean `v4.34.1` on `PATH`):
   ```console
   python3 support/check_lean.py --lean lean --out /tmp/lean_check_receipt.json
   ```
   Scans for all 13 forbidden tokens, runs synchronous kernel typechecking (`-DElab.async=false -Ddebug.skipKernelTC=false`), audits all constants in the compiled `.olean` for zero violations and `{propext, Quot.sound}`-only axioms, and cleans up the `.olean`. A passing run establishes the theorems of Findings 7–8 inside the Lean model; it does not verify `rustc` itself.
4. *Reverify upstream pins* (~5 seconds; requires `curl` and GitHub network access):
   ```console
   python3 support/verify_pins.py --out /tmp/pin_receipt.json
   ```
5. *Check Anneal MIR ingestion drift:* inspect `inductive MirTy`, `inductive Rvalue`, and `inductive TerminatorKind` in `trusted/lean/Trusted/MirAst.lean` at the target `joshlf/anneal` commit; if `Dynamic`, `Cast`/`PointerCoercion`, `Drop`, or indirect `Call` gain dedicated constructors, Finding 10 must be updated.

**What requires manual redoing.** If `rustc` alters `prepare_vtable_segments_inner` (e.g., adopting flat layouts, reordering `TraitVPtr` slots, or changing slot-0 null drop semantics), the Lean definitions in `Section 3` and the correspondence table in Finding 9 must be updated manually against fresh LLVM IR dumps.
