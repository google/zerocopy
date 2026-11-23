# `rustc` Trait Upcasting Coercions, Segmented Vtable Layout, Diamond Supertrait Deduplication, and `Box<dyn Sub> -> Box<dyn Super>` Drop and Deallocation Soundness

## Summary

In `rustc`, trait upcasting coercions (`PointerCoercion::Unsize` from a `dyn Sub` wide pointer to a `dyn Super` wide pointer) operate purely on pointer metadata (the vtable pointer half of a wide pointer) and never modify the data pointer half. `rustc` avoids runtime subtrait-search tables by arranging every concrete type's trait-object vtable as a segmented sequence produced by depth-first search (`prepare_vtable_segments_inner`):

1. **Three-word `MetadataDSA` header at slots `0..2`**: `[MetadataDropInPlace, MetadataSize, MetadataAlign]` (`COMMON_VTABLE_ENTRIES`), describing the **concrete `Sized` implementing type**, never an abstract supertrait.
2. **Primary-supertrait prefix sharing (`emit_vptr = false`)**: The first non-empty supertrait spine (skipping over truly-empty marker traits that transitively declare zero existential vtable entries) lays out its segments contiguously starting right after the header at slot `3`, reusing the subtrait's own vtable prefix. Upcasting along any segment with `emit_vptr = false` causes `supertrait_vtable_slot` to return `Some(None)`, so SSA codegen (`unsized_info`) reuses `old_info` unchanged with zero loads and zero runtime instructions.
3. **Secondary-supertrait `VtblEntry::TraitVPtr` indirection (`emit_vptr = true`)**: Once DFS pops at least one trait whose transitive supertraits have existential vtable entries, subsequent branches set `emit_vptr = true`. Each non-empty secondary supertrait appends a `TraitVPtr(trait_ref)` slot pointing to an independent static `vtable_allocation((concrete_ty, Some(super_trait_ref)))`. `supertrait_vtable_slot` returns `Some(Some(slot_idx))`, and `unsized_info` lowers the coercion to `getelementptr inbounds i8, ptr %vptr, i64 (8 * slot_idx)` followed by an `!invariant.load` + `!nonnull` pointer load (verified on `x86_64` at byte offsets `40` for slot `5`, `48` for slot `6`, `64` for slot `8`, `72` for slot `9`, and `104` for slot `13`).
4. **Diamond deduplication vs. generic ambiguity (`E0308`)**: Two distinct deduplication filters apply. Type-level supertrait elaboration (`util::supertraits` via `Elaborator::extend_deduped`) deduplicates anonymized trait predicates before selection candidate assembly, so a diamond sharing one concrete generic instantiation (`SameGenDia: LeftU8 + RightU8` with `GenRoot<u8>`) yields a single candidate and **accepts** `&dyn GenRoot<_>` inference (`rustc` exit code `0`). Conversely, distinct generic instantiations (`AmbigDia: GenRoot<u8> + GenRoot<u16>`) produce multiple candidates matching `GenRoot<?0>`, triggering `winnow_candidates` ambiguity rejection (`has_non_region_infer = true` returning `None` -> `error[E0308]`) unless pinned concretely. For non-generic diamonds (`Diamond: Left + Right`, `Left: Root`, `Right: Root`), DFS `PredicateSet` emits `Root` once in `Diamond`'s primary prefix while generating a standalone sub-vtable for `TraitVPtr(Right)`; upcasting via `Diamond -> Left -> Root` and `Diamond -> Right -> Root` yields **unequal runtime vtable pointers** (`ROOT_FROM_D_EQ_ROOT_FROM_R=false`) that agree identically on concrete `DSA` metadata and `Root` method dispatch.
5. **Symbolic vtable pointer inequality under `Miri`**: Under native LLVM `-O0`/`-O2`, prefix upcasts preserve physical pointer equality (`VPTR_SUB_EQ_A=true`) and secondary sub-vtables deduplicate to the same constant global (`VPTR_B_EQ_DIRECT_B=true`). Under `Miri` (both Stacked Borrows and `-Zmiri-tree-borrows`), all raw vtable pointer address comparisons return `false` because `rustc`/`Miri` allocate symbolic `AllocId`s backed by `GlobalAlloc::VTable(concrete_ty, existential_trait_ref)` while preserving identical virtual calls, `size_of_val`, `align_of_val`, and drop behavior.
6. **`Box<dyn Sub> -> Box<dyn Super>` drop and deallocation soundness**: `unsize_ptr` and `coerce_unsized_into` recursively peel non-1-ZST wrapper fields (`Box` -> `Unique` -> `NonNull` -> `*const dyn Trait`) and update only the wide pointer metadata. MIR drop elaboration (`elaborate_drop.rs`) special-cases `adt.is_box()` to drop box contents first (running outer concrete destructors before nested field destructors, guarded at runtime in `codegen_drop_terminator` by a nullable load of vtable slot `0`), followed on both return and unwind edges by `<Box<T, A> as Drop>::drop`. `Box::drop` calls `Layout::for_value_raw`, which reads `size` (slot `1`, `!range [0, isize::MAX)`) and `align` (slot `2`, `!range [1, Align::max]`) from the current upcast target's sub-vtable, and calls `self.1.deallocate` whenever `size != 0`. Because every `TraitVPtr` sub-vtable retains the concrete type's `[drop_fn, size, align]` header, arbitrary chains of upcasts preserve exact drop order, skip null destructors for `!needs_drop` types, and pass exact `(size, align)` layouts to the allocator.

All upstream source claims are anchored in `rust-lang/rust` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and upstream `5debe6a1244452beced762385f88a51857a915fc`), `rust-lang/reference` (`c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`), and `rust-lang/rfcs` (`f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`), validated by `17/17` differential native/LLVM-IR/MIR/`Miri` probe checks (`support/probe_trait_upcasting_vtable_segments_and_box_drop.py`) and a `1,724`-line kernel-checked Lean `v4.34.1` mechanization (`support/TraitUpcastingVtableSegmentsAndBoxDropSoundness.lean`) with `0` `sorry`, `0` `Classical.choice`, `0` `._unsafe_rec` constants across `env.constants.map₁`, and `0` audit violations (`support/lean_check_receipt.json`).

---

## Applicability

This report documents the static type-selection rules, MIR representations, vtable layouts, SSA/LLVM IR lowering, `Box` drop/deallocation behavior, and `joshlf/anneal` verification boundary across the six pinned subjects recorded in `REPORT.json`:

| Subject | Immutable Revision | Role in This Report |
| :--- | :--- | :--- |
| `rust-lang/rust` (`1.98.0-nightly`) | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | Executed `rustc` (`LLVM 22.1.6`, `x86_64-unknown-linux-gnu`) and `miri 0.1.0`; baseline compiler, `alloc`, and `core` source inspection |
| `rust-lang/rust` (upstream HEAD snapshot) | `5debe6a1244452beced762385f88a51857a915fc` | Diffed against `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` across all 17 examined compiler, `alloc`, and `core` modules |
| `rust-lang/reference` | `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` | Normative language rules (`r[coerce.unsize.trait-upcast]`, `r[coerce.types.unsize]`, `r[type.trait-object.*]`) |
| `rust-lang/rfcs` | `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07` | RFC 3324 (`text/3324-dyn-upcasting.md`) design contract |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `Trusted.MirAst` and `Trusted.MirSemantics` fail-closed boundary analysis |
| `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` | Lean `v4.34.1` kernel verifying `TraitUpcastingVtableSegmentsAndBoxDropSoundness.lean` |

### Version Continuity and Drift Between `14210df0e` and `5debe6a1`

Direct comparison of all 17 inspected `rust-lang/rust` source files between `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and `5debe6a1244452beced762385f88a51857a915fc` establishes identical algorithmic semantics for segmented vtable construction, trait upcasting selection, MIR drop elaboration, and codegen lowering, with four mechanical refactors in `5debe6a1244452beced762385f88a51857a915fc`:

1. **`compiler/rustc_middle/src/ty/vtable.rs`**: Removed `.abi` chaining on `tcx.data_layout.pointer_align()` when constructing `Allocation::new(...)` (1-line change); `VtblEntry`, `COMMON_VTABLE_ENTRIES`, `vtable_min_entries`, and `vtable_allocation_provider` logic are unchanged.
2. **`compiler/rustc_trait_selection/src/traits/vtable.rs`**: Renamed internal clause helpers (`explicit_super_predicates_of` -> `explicit_super_clauses_of`, `impossible_predicates` -> `instantiate_and_check_impossible_clauses`), added `tcx.debug_assert_fully_normalized(...)` checks, updated `first_method_vtable_slot` return type from `usize` to `Option<usize>` with `delayed_bug` diagnostics on impossible clauses, and clarified doc comments on `VtblSegment` and `vtable_prefix_traits`. `prepare_vtable_segments_inner`, `supertrait_vtable_slot`, and `vtable_entries` slot emission rules are unchanged.
3. **Unchanged codegen, MIR, and `Box::drop` files**: `compiler/rustc_trait_selection/src/traits/select/{candidate_assembly.rs, confirmation.rs, mod.rs}`, `compiler/rustc_type_ir/src/elaborate.rs`, `compiler/rustc_codegen_ssa/src/{base.rs, meth.rs, size_of_val.rs, mir/block.rs}`, `compiler/rustc_mir_transform/src/{mentioned_items.rs, elaborate_drop.rs, shim.rs}`, `library/alloc/src/boxed.rs`, and `library/core/src/alloc/layout.rs` exhibit identical coercion, vtable slot lookup, drop order, and deallocation behavior across both snapshots.

### Target, ABI, and Feature Configuration Constraints

- **Target ABI**: Empirical slot byte offsets (`8 * slot_idx`, e.g., `i64 40`, `48`, `64`, `72`, `104`) and `[24 x i8]` header sizes apply to 64-bit pointer platforms (`x86_64-unknown-linux-gnu` with `ptr_size = 8`, `COMMON_VTABLE_ENTRIES.len() = 3`); on 32-bit targets the slot index formula `COMMON_VTABLE_ENTRIES.len() + ...` is unchanged while byte offsets scale by `4`.
- **Standard edition**: All specimens compile under `--edition=2021` (stable feature set in `1.98.0-nightly`, no `#![feature(...)]` gates) without `-Z no-trait-vptr` (`tcx.sess.opts.unstable_opts.no_trait_vptr = false`).
- **Lean kernel configuration**: Mechanized proofs are compiled with `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` on pure `Init` with `noncomputable def` on every definition, ensuring zero compiler `_unsafe_rec` auxiliary generation.

---

## Findings

### 1. Segmented Vtable Representation and DFS Construction (`prepare_vtable_segments`)

Basis: `normative specification + source + execution + derived`

#### 1.1 `VtblEntry<'tcx>` and Concrete Metadata Header Invariants

In `compiler/rustc_middle/src/ty/vtable.rs` (`14210df0e` / `5debe6a1` lines `12..26` and `44..52`), every trait object vtable slot holds one of six `VtblEntry<'tcx>` variants, led by the fixed 3-slot `COMMON_VTABLE_ENTRIES` header:

```rust
pub enum VtblEntry<'tcx> {
    MetadataDropInPlace,      // slot 0 (COMMON_VTABLE_ENTRIES_DROPINPLACE)
    MetadataSize,             // slot 1 (COMMON_VTABLE_ENTRIES_SIZE)
    MetadataAlign,            // slot 2 (COMMON_VTABLE_ENTRIES_ALIGN)
    Vacant,                   // uninit/undef slot for non-dispatchable methods
    Method(Instance<'tcx>),   // dispatchable method function pointer
    TraitVPtr(TraitRef<'tcx>),// pointer to standalone supertrait vtable
}
```

When `vtable_allocation_provider` materializes `(ty, poly_trait_ref)` (`compiler/rustc_middle/src/ty/vtable.rs` lines `84..156`):

1. **Sizedness & layout assertion**: `ty` MUST be `Sized` (`assert!(layout.is_sized(), "can't create a vtable for an unsized type")`, line `106`); `size = layout.size.bytes()` and `align = layout.align.bytes()` come from `tcx.layout_of(ty::TypingEnv::fully_monomorphized().as_query_input(ty))` (lines `102..108`).
2. **Uninit base allocation**: `Allocation::new(vtable_size, ptr_align, AllocInit::Uninit, ())` creates an uninitialized buffer of `ptr_size * vtable_entries.len()` bytes (`lines 110..114`).
3. **Nullable slot-0 destructor optimization**: Slot `0` (`MetadataDropInPlace`) checks `ty.needs_drop(tcx, ty::TypingEnv::fully_monomorphized())` (lines `123..132`). Only if `true` does it resolve `ty::Instance::resolve_drop_glue(tcx, ty)` and store its function pointer; if `false`, it writes `Scalar::from_maybe_pointer(Pointer::null(), &tcx)` (`0` bytes in LLVM IR, saving relocations for no-op drops as noted in `codegen_ssa/src/mir/block.rs` line `724`).
4. **`Vacant` slot emission (`undef` in LLVM)**: For `VtblEntry::Vacant`, the loop executes `continue;` (line `135`), leaving those `ptr_size` bytes uninitialized (`AllocInit::Uninit`), which lower to `[8 x i8] undef` in LLVM constant globals.
5. **Recursive concrete-type `TraitVPtr` construction**: For `VtblEntry::TraitVPtr(trait_ref)` (lines `142..147`), `rustc` erases `Self` (`let super_trait_ref = ty::ExistentialTraitRef::erase_self_ty(tcx, trait_ref)`) and recursively invokes `tcx.vtable_allocation((ty, Some(super_trait_ref)))`. **Critical invariant**: the first tuple element remains **`ty` (the original concrete `Sized` type)** — never `dyn SuperTrait` — so every secondary sub-vtable has an identical `[drop_in_place::<ty>, size_of::<ty>, align_of::<ty>]` header at slots `0..2`.

#### 1.2 Depth-First Search Segmentation (`prepare_vtable_segments_inner`)

In `compiler/rustc_trait_selection/src/traits/vtable.rs` (`5debe6a1` lines `38..189`), `prepare_vtable_segments_inner` partitions the deduplicated transitive supertrait DAG into non-overlapping prefix slices using an explicit DFS stack:

- **Initialization** (lines `88..95`): Emits `VtblSegment::MetadataDSA`, initializes `emit_vptr_on_new_entry = false`, creates `visited = PredicateSet::new(tcx)`, inserts `trait_ref.upcast(tcx)`, and seeds `stack = [(trait_ref, false, maybe_iter(None))]`.
- **Diving phase (`'diving_in`, lines `122..156`)**: Repeatedly inspects `stack.last()` and takes the **first** direct supertrait not yet in `visited`, pushing `(next_super_trait, emit_vptr_on_new_entry, remaining_direct_supers)` without mutating `emit_vptr_on_new_entry`.
- **Popping phase (`while let Some(...) = stack.pop()`, lines `159..184`)**:
  - Computes `has_entries = ty::elaborate::supertrait_def_ids(tcx, inner_most_trait_ref.def_id).any(|def_id| has_own_existential_vtable_entries(tcx, def_id))` (lines `164..165`).
  - Emits `VtblSegment::TraitOwnEntries { trait_ref: inner_most_trait_ref, emit_vptr: emit_vptr && has_entries && !no_trait_vptr }` (lines `167..170`).
  - Updates `emit_vptr_on_new_entry |= has_entries;` (line `174`).
  - If `siblings` yields another unvisited sibling, pushes `(next_sibling, emit_vptr_on_new_entry, siblings)` and continues `'outer` to dive down that sibling's supertraits first.

Two crucial corollaries follow directly from lines `164..174`:

- **Truly-empty marker trait preservation (`EmptyMarker` rule)**: If a subtrait declares `trait SubAfterEmpty: EmptyMarker + SuperB`, `EmptyMarker` is visited first and has `has_entries = false` (neither `EmptyMarker` nor any supertrait of it has existential entries). Thus popping `EmptyMarker` leaves `emit_vptr_on_new_entry = false`. When DFS moves to sibling `SuperB`, `SuperB` is popped with `emit_vptr = false`, making `&dyn SubAfterEmpty -> &dyn SuperB` a **zero-instruction prefix reuse** just as if `EmptyMarker` were absent (`vtable_prefix_traits` doc comment at `vtable.rs` lines `461..463`). Conversely, if a first supertrait has zero *own* methods yet inherits a non-empty supertrait (`has_entries = true` via `supertrait_def_ids().any(...)`), `emit_vptr_on_new_entry` flips to `true`, so subsequent siblings DO receive `TraitVPtr` slots.
- **Exact `supertrait_vtable_slot` calculation** (`vtable.rs` lines `384..456`): Walking `prepare_vtable_segments`, `vptr_offset` starts at `0`, adds `COMMON_VTABLE_ENTRIES.len()` (`3`) on `MetadataDSA`, and for each `TraitOwnEntries { trait_ref, emit_vptr }` adds `own_existential_vtable_entries(trait_ref.def_id).len()`. If `erase_self_ty(trait_ref) == target_principal`, it immediately returns `Break(Some(vptr_offset))` when `emit_vptr` is `true`, or `Break(None)` when `emit_vptr` is `false`. Otherwise, if `emit_vptr` is `true`, `vptr_offset += 1` skips the emitted `TraitVPtr` pointer slot before continuing. If the source principal is absent (impossible clauses at lines `411..415` or erased target principal at line `400`), `supertrait_vtable_slot` returns `None`.

#### 1.3 Empirical Multi-Supertrait Layouts and LLVM IR Offsets (`Exp A`)

Running `support/specimens/exp_a_multi_supertrait_vtable.rs` (`Impl` with `#[repr(C, align(16))]`, `size=16`, `align=16`, `!needs_drop`) under `rustc 1.98.0-nightly` confirms every slot layout and byte offset in both `-O0` and `-O2` LLVM IR (`support/probe_output/probe_results.json` and `llvm_ir_excerpts.txt`):

```text
@vtable.2 (<Impl as Sub>, Sub: SuperA + SuperB, 7 pointer-sized slots = 56 bytes):
  slot 0 ( +0B): null ptr             (MetadataDropInPlace; Impl !needs_drop)
  slot 1 ( +8B): i64 16               (MetadataSize)
  slot 2 (+16B): i64 16               (MetadataAlign)
  slot 3 (+24B): ptr @Impl::SuperA::a (emit_vptr = false; shared primary prefix)
  slot 4 (+32B): ptr @Impl::SuperB::b (emit_vptr = true on SuperB)
  slot 5 (+40B): ptr @alloc_efdc...   (TraitVPtr(SuperB) -> [DSA(24B), @Impl::SuperB::b])
  slot 6 (+48B): ptr @Impl::Sub::sub  (emit_vptr = false)
```

Exact slot accounting across all four `Exp A` LLVM constant globals (`support/probe_output/llvm_ir_excerpts.txt` lines `79..120`):

- **`@vtable.2` (`Sub: SuperA + SuperB`)**: `<{ [24 x i8], ptr, ptr, ptr, ptr }>` (`3 + 4 = 7` slots = `56` bytes), with `TraitVPtr(SuperB)` at slot `5` (`i64 40`) pointing to standalone `@alloc_efdc6553ec6a3212e83f34d46446f0e5` (`<{ [24 x i8], ptr }>` storing `[0, 16, 16, @Impl::SuperB::b]`).
  - `upcast_to_a` (`-O0` and `-O2`): `insertvalue` x2 + `ret { ptr, ptr }` (zero loads; `VPTR_SUB_EQ_A=true`).
  - `upcast_to_b` (`-O2`): `dereferenceable(48) %r.1`, `%0 = getelementptr inbounds nuw i8, ptr %r.1, i64 40`, `%_0.1 = load ptr, ptr %0, align 8, !invariant.load, !nonnull` (`VPTR_SUB_EQ_B=false`, `VPTR_B_EQ_DIRECT_B=true`).
- **`@vtable.3` (`SubAfterEmpty: EmptyMarker + SuperB`)**: `<{ [24 x i8], ptr, ptr }>` (`3 + 2 = 5` slots): `[DSA(24B), @SuperB::b, @SubAfterEmpty::sub_e]`. No `TraitVPtr` is emitted; `upcast_after_empty_to_b` is a zero-load no-op (`VPTR_AFTER_EMPTY_EQ_B=true`).
- **`@vtable.4` (`Tri: SuperA + SuperB + SuperC`, where `SuperC` has 2 methods `c1, c2`)**: `<{ [24 x i8], ptr, ptr, ptr, ptr, ptr, ptr, ptr }>` (`3 + 7 = 10` slots = `80` bytes):
  - Slots `0..2`: `DSA` (`24B`: `[0, 16, 16]`)
  - Slot `3`: `SuperA::a` -> `upcast_tri_to_a` emits zero loads (`VPTR_TRI_EQ_A=true`)
  - Slot `4`: `SuperB::b`
  - Slot `5` (`i64 40`): `TraitVPtr(SuperB)` (`@alloc_efdc...`) -> `upcast_tri_to_b` loads `i64 40` (`VPTR_TRI_EQ_B=false`)
  - Slots `6..7`: `SuperC::c1`, `SuperC::c2`
  - Slot `8` (`i64 64`): `TraitVPtr(SuperC)` (`@alloc_6a8e...`) -> `upcast_tri_to_c` loads `i64 64` (`VPTR_TRI_EQ_C=false`)
  - Slot `9`: `Tri::tri`
- **`@vtable.1` (`<Impl as CondVacant<NonCopy>>`, where `only_copy` carries `where NonCopy: Copy`)**: `<{ [24 x i8], ptr, [8 x i8] }>`: slots `0..2` = `[0, 16, 16]`, slot `3` = `CondVacant::always`, slot `4` = `[8 x i8] undef` (`VtblEntry::Vacant`).

**Why prefix reuse for a secondary supertrait is unsound**: Calling `(r as &dyn SuperB).b()` dispatches to slot `3` (`+24B`) in `&dyn SuperB`'s vtable contract. Reusing `&dyn Sub`'s vptr (`@vtable.2`) without loading slot `5` (`@alloc_efdc...`) would invoke slot `3` of `@vtable.2`, which holds **`SuperA::a` (`17`) rather than `SuperB::b` (`27`)**. Both our empirical runtime trace (`CALLS=17,27,107,27,27,39,407`) and Lean Theorem `counterexample_wrong_prefix_reuse_dispatches_wrong_method` establish this separation.

---

### 2. MIR Representation, Collection, SSA Lowering, and Miri Divergence

Basis: `source + execution + derived`

1. **MIR Representation (`runtime-post-cleanup` and `runtime-optimized`)**: Both `&dyn Sub -> &dyn Super` (`exp_a`, `exp_b`) and `Box<dyn Sub> -> Box<dyn Super>` (`exp_c`) lower in MIR to `Rvalue::Cast(CastKind::PointerCoercion(PointerCoercion::Unsize, Implicit), operand, target_ty)` (`support/probe_output/mir_excerpts.txt` lines `155`, `1319`, `1336`, `1416..1418`). Chained upcasts (`upcast_chain_3hop`) retain sequential `Unsize` steps in MIR; under `-C opt-level=2`, LLVM inlines the chain (`upcast_chain_3hop` optimizes metadata away when unused downstream in that test helper, while `-O0` preserves all three `getelementptr` steps: `i64 104`, `i64 72`, `i64 40`).
2. **Collection Guarantee (`mentioned_items.rs`)**: `MentionedItemsVisitor::visit_rvalue` (`compiler/rustc_mir_transform/src/mentioned_items.rs` lines `71..96`) inspects every `PointerCoercion::Unsize` cast and pushes `MentionedItem::UnsizeCast { source_ty, target_ty }` whenever `(source_ty.builtin_deref, target_ty.builtin_deref)` is anything other than `Array -> Str | Slice`, ensuring vtable allocations and secondary sub-vtables are reachable in monomorphization collection.
3. **Codegen Lowering (`compiler/rustc_codegen_ssa/src/base.rs` lines `161..313`, `meth.rs` lines `95..103`)**:
   - `unsize_ptr` and `coerce_unsized_into` recursively peel single-field (modulo 1-ZST) ADT wrappers (such as `Box<dyn Sub>` -> `Unique<dyn Sub>` -> `NonNull<dyn Sub>` -> `*const dyn Sub`) and pass the wide pointer pair `(base_data_ptr, old_vtable_info)` into `unsized_info`.
   - `unsized_info` checks `if data_a.principal_def_id() == b_principal_def_id || b_principal_def_id.is_none()` (`base.rs` line `178`): when equal (same principal upcast dropping auto traits or tightening lifetime) or target principal is `None` (e.g., `dyn Sub -> dyn Send`), `debug_assert!(validate_trivial_unsize(...))` runs and `old_info` is returned verbatim.
   - Otherwise, `unsized_info` calls `cx.tcx().supertrait_vtable_slot((source, target))` (line `202`). When `Some(entry_idx)` is returned, `VirtualIndex::from_index(entry_idx).get_data_ptr(bx, old_info, true)` emits an inbounds pointer arithmetic + read-only `!invariant.load` + `!nonnull` pointer load (`meth.rs` lines `95..103`); when `None` is returned, `old_info` is returned directly.
4. **Native LLVM vs. `Miri` Vtable Pointer Equality Divergence**:
   In `Exp A` (`support/specimens/exp_a_multi_supertrait_vtable.rs`) and `Exp B` (`support/specimens/exp_b_diamond_upcast.rs`), `transmute_copy::<&T, (usize, usize)>` extracts the integer representation of the vtable pointer half:
   - **Native `-O0` and `-O2`**: `VPTR_SUB_EQ_A=true`, `VPTR_B_EQ_DIRECT_B=true`, `VPTR_AFTER_EMPTY_EQ_B=true`, `VPTR_TRI_EQ_A=true` (`Exp A`), and `D_EQ_L=true L_EQ_ROOT=true D_EQ_ROOT_FROM_D=true R_EQ_RDIR=true` (`Exp B`). LLVM lowers constant vtable globals canonically and shares exact addresses when prefixes match or sub-vtables instantiate the same `(Concrete, Super)` key.
   - **`Miri` (both default Stacked Borrows and `-Zmiri-tree-borrows`)**: **Every** `VPTR_*_EQ_*` check prints **`false`** (`VPTR_SUB_EQ_A=false`, `VPTR_B_EQ_DIRECT_B=false`, `D_EQ_L=false`, `ASYM_D_EQ_ROOT=false`), while `SUB_DATA_EQ_A=true`, `CALLS`, `SIZES`, `ALIGNS`, and `DEALLOC_LAYOUTS` match native `-O2` 100%!
   - **Root cause (`rustc_middle/src/ty/vtable.rs` lines `80..83` & interpreter model)**: As documented directly above `vtable_allocation_provider`: *"This is an 'internal' `AllocId` that should never be used as a value in the interpreted program. The interpreter should use `AllocId` that refer to a `GlobalAlloc::VTable` instead."* Because Miri checks vtable validity and method lookup semantically via distinct symbolic `AllocId(GlobalAlloc::VTable(Concrete, ExistentialTraitRef))` handles rather than collapsed LLVM constant-pool addresses, raw address comparison of vtable pointers is inherently unreliable across compilation modes even for no-op prefix upcasts.

---

### 3. Diamond Supertrait Deduplication and Generic Ambiguity (`E0308`)

Basis: `source + execution + derived`

#### 3.1 Symmetric & Asymmetric Diamond Path Coherence (`Exp B`)

Consider a symmetric diamond (`Diamond: Left + Right`, `Left: Root`, `Right: Root`, implemented on `Node(100)`):

1. **Deduplicated Vtable Segments**: Running `prepare_vtable_segments_inner` on `(Node, Diamond)` inserts `Diamond`, `Left`, and `Root` into `visited: PredicateSet` along the first DFS branch, emitting `[MetadataDSA, (Root, emit_vptr=false), (Left, emit_vptr=false)]` and flipping `emit_vptr_on_new_entry = true`. When popping back to `Diamond` and entering `Right`, `Root` is **already in `visited`** and is skipped in DFS (`vtable.rs` line `144`), so `Right` emits `(Right, emit_vptr=true)` followed by `(Diamond, emit_vptr=false)`.
   - Observed LLVM IR `@vtable.1` (`exp_b`): `<{ [24 x i8], ptr @Node::Root::root, ptr @Node::Left::left, ptr @Node::Right::right, ptr @alloc_b355..., ptr @Node::Diamond::dia }>`. `Root::root` appears once; `TraitVPtr(Right)` sits at **slot `6` (`i64 48`)** pointing to `@alloc_b355...` = `<{ [24 x i8], ptr @Node::Root::root, ptr @Node::Right::right }>`.
2. **Coherence Without Address Identity**:
   - Upcast path 1 (`Diamond -> Left -> Root`) and direct path (`Diamond -> Root`): both `supertrait_vtable_slot` calls return `Some(None)` (prefix reuse), keeping `%vptr = @vtable.1` (`D_EQ_L=true L_EQ_ROOT=true D_EQ_ROOT_FROM_D=true`).
   - Upcast path 2 (`Diamond -> Right -> Root`): step `Diamond -> Right` loads `@alloc_b355...` (`i64 48`, `R_EQ_RDIR=true`), and step `Right -> Root` returns `Some(None)`, keeping `%vptr = @alloc_b355...`.
   - Crucially, `vptr(@alloc_b355...) ≠ vptr(@vtable.1)` (`ROOT_FROM_D_EQ_ROOT_FROM_R=false`), yet BOTH vtables carry identical `[0, 8, 8]` `DSA` headers and place `Node::Root::root` at **slot `3` (`+24B`)**, returning `CALLS=104,102,103,101,101,101` identically along every path.
3. **Asymmetric Two-Hop Secondary Path (`DiamondAsym: Left + RightSecond`, `RightSecond: Sibling + Root`)**:
   - Here `RightSecond` places `Sibling` first and `Root` second, so `RightSecond` -> `Root` is itself non-primary!
   - LLVM IR `-O0` and `-O2` prove a **two-load path**: `asym_to_right_second` loads `@alloc_13dd...` from `@vtable.3` at **`i64 64` (slot `8`)**, and `right_second_to_root` loads `@vtable.2` (`Root` standalone vtable) from `@alloc_13dd...` at **`i64 40` (slot `5`)**. Meanwhile direct `asym_to_root` is a zero-load no-op using `@vtable.3`'s primary prefix! Still, `ASYM_ROOT_CALLS=101,101` agree unconditionally (`b::diamond_asym_coherent_dispatch = true`).

#### 3.2 Candidate Assembly, `Elaborator` Deduplication, and Generic Ambiguity (`E0308`)

Why does trait upcasting accept an inferred target `&dyn GenRoot<_>` on `SameGenDia: LeftU8 + RightU8` (where both parents inherit `GenRoot<u8>`) while rejecting `&dyn GenRoot<_>` on `AmbigDia: GenRoot<u8> + GenRoot<u16>`? Inspection of `candidate_assembly.rs`, `elaborate.rs`, `confirmation.rs`, and `select/mod.rs` establishes the exact two-stage mechanism:

1. **Stage 1 — Anonymized Supertrait Elaboration (`compiler/rustc_trait_selection/src/traits/select/candidate_assembly.rs` lines `1058..1079` and `compiler/rustc_type_ir/src/elaborate.rs`)**:
   `assemble_candidates_for_unsizing` iterates `(idx, upcast_trait_ref) in util::supertraits(self.tcx(), source_trait_ref).enumerate()` and probes `self.match_upcast_principal(...)` inside `self.infcx.probe(|_| ...)`. Because `util::supertraits` uses `Elaborator::extend_deduped`, whose `visited` set keys on `anonymize_bound_vars(pred)`, **syntactically identical concrete generic predicates coalesce before candidate assembly**:
   - On `SameGenDia: LeftU8 + RightU8`, `GenRoot<u8>` appears only **once** in `util::supertraits` (`candidates.vec.len() == 1`). As shown in `select/mod.rs:371`, a unique candidate returns immediately without ambiguity, and inference resolves `_ = u8` cleanly (`support/specimens/exp_b_neg_same_infer.rs` compiles with exit code `0`!).
2. **Stage 2 — Multiple Distinct Matching Candidates & `winnow_candidates` (`select/mod.rs` lines `1874..1884`, `confirmation.rs` lines `936..972`)**:
   - On `AmbigDia: GenRoot<u8> + GenRoot<u16>`, `GenRoot<u8>` and `GenRoot<u16>` are distinct `PredicateKind` keys, so `util::supertraits` yields both. When coercing to `&dyn GenRoot<_>` (`exp_b_neg_ambig_infer.rs`), `?0` is a **non-region inference variable**, so `infcx.probe` matches *both* `GenRoot<u8>` and `GenRoot<u16>`, pushing two `TraitUpcastingUnsizeCandidate(idx)` entries.
   - `winnow_candidates` (`select/mod.rs` line `1879`) executes:
     ```rust
     .try_reduce(|c1, c2| if has_non_region_infer { None } else { Some(c1.min(c2)) })
     ```
   - Because `has_non_region_infer` is `true`, `try_reduce` returns `Some(None)`, `winnow_candidates` returns `None` (ambiguous), and `rustc` emits `error[E0308]: mismatched types ... expected reference &dyn GenRoot<_> found reference &dyn AmbigDia`.
   - Conversely, when the target is concrete (`&dyn GenRoot<u8>` or `&dyn GenRoot<u16>` in `exp_b_diamond_upcast.rs`), only one `TraitUpcastingUnsizeCandidate(idx)` matches, `ambig_to_u8` is a zero-load prefix no-op, and `ambig_to_u16` loads slot `5` (`i64 40`) pointing to `@alloc_92fc...` (`GEN_TAGS=8,16`). When multiple lifetime-only candidates differ solely in regions (`has_non_region_infer == false`), `try_reduce` deterministically selects `c1.min(c2)` (`confirm_trait_upcasting_unsize_candidate` builds `BuiltinImplSource::TraitUpcasting(idx)`).

---

### 4. `Box<dyn Sub> -> Box<dyn Super>` Drop Order and Heap Deallocation Soundness

Basis: `normative specification + source + execution + derived`

```text
Allocation:   Box::new(val: DropTracker)          // size=32, align=32, needs_drop=true
                  |
Unsize x3:    Box<dyn Tier3> -> Box<dyn Tier2> -> Box<dyn Tier1> -> Box<dyn Tier0>
                  |  [-O0 IR: GEP +104 -> load -> GEP +72 -> load -> GEP +40 -> load]
                  v
Drop(box):    drop((*_6))                         // [elaborate_drop.rs is_box()]
                |-> load vptr[0]                  // MetadataDropInPlace (= drop_glue::<DropTracker>)
                |-> icmp ne %drop_fn, null        // [mir/block.rs codegen_drop_terminator]
                |-> call DropTracker::drop        // logs "drop_outer"
                |-> call InnerDrop::drop          // logs "drop_inner_3hop" (field drops AFTER outer!)
                v
              <Box<dyn Tier0> as Drop>::drop      // [boxed.rs:2128..2145]
                |-> Layout::for_value_raw(ptr)    // [layout.rs:259 -> size_of_val.rs:28..45]
                |-> load vptr[1] -> size  = 32    // MetadataSize  (!range [0, isize::MAX))
                |-> load vptr[2] -> align = 32    // MetadataAlign (!range [1, Align::max])
                |-> if size != 0 { dealloc(ptr, Layout(32, 32)) }
```

The end-to-end soundness of dropping and freeing an arbitrarily upcasted `Box<dyn Super>` rests on four verified compiler and library invariants (`Exp C`, `support/specimens/exp_c_box_upcast_drop_dealloc.rs`):

1. **Box Wrapper Coercion Preserves Pointer and Adjusts Only Vtable Metadata (`base.rs` lines `236..261`, `292..310`)**:
   Both `unsize_ptr` and `coerce_unsized_into` walk structural single-non-1-ZST fields (`Box` -> `Unique` -> `NonNull` -> `*const dyn Sub`) and keep `base` (`_1` data pointer) untouched while setting metadata to `unsized_info(bx, source, target, old_info)`.
2. **Exact MIR Drop Elaboration Order for `Box<T>` (`compiler/rustc_mir_transform/src/elaborate_drop.rs` lines `1035..1048`)**:
   Whereas normal ADTs drop their own `Drop::drop` *first* and then fields, `open_drop_for_adt` checks `if adt.is_box()` and constructs `succ`/`unwind`/`dropline` calling `destructor_call_block_sync` (`<Box<T, A> as Drop>::drop`) **after** `open_drop_for_box_contents`. Both normal return (`bb0 -> bb3`) and cleanup unwind (`bb0 -> bb4`) in `core.ptr-drop_glue.Box_dynSuperB_.3-3-000.runtime-optimized.after.mir` (`mir_excerpts.txt` lines `735..750`) confirm `drop((*_6))` precedes `<Box<dyn SuperB> as Drop>::drop`. Inside `drop_glue::<DropTracker>` (`mir_excerpts.txt` lines `792..816`), `DropTracker::drop` executes first, then `drop(((*_1).2: InnerDrop))`, matching runtime output `DROP_ORDER=["drop_outer", "drop_inner", "after_drop", "drop_outer", "drop_inner_3hop"]`.
3. **Runtime Null-Check Drop Dispatch (`compiler/rustc_codegen_ssa/src/mir/block.rs` lines `684..736`)**:
   In `codegen_drop_terminator`, `ty::Dynamic` sets `maybe_null = true`, loads slot `0` via `VirtualIndex::from_index(COMMON_VTABLE_ENTRIES_DROPINPLACE).get_optional_fn`, and branches `icmp ne ptr %drop_fn, null` before invoking `drop_fn(data_ptr)`. Both `DropTracker` (`@vtable.3` non-null `drop_glue`) and `!needs_drop` `NoDropBig` (`@vtable.5` & `@alloc_3316...` zeroed slot `0`) share identical `drop_glue::<Box<dyn SuperB>>` LLVM IR (`probe_results.json` line `459`: `load ptr, ptr %_6.1` -> `icmp eq ptr %1, null`).
4. **Concrete `Layout` Recovery and Heap Deallocation (`library/alloc/src/boxed.rs` lines `2126..2146`, `library/core/src/alloc/layout.rs` lines `259..264`, `compiler/rustc_codegen_ssa/src/size_of_val.rs` lines `28..45`)**:
   `<Box<T, A> as Drop>::drop` computes `Layout::for_value_raw(ptr.as_ptr())`, which lowers `size_of_val_raw` and `Alignment::of_val_raw` into `size_and_align_of_dst` reads of vtable slot `1` (`MetadataSize`, `+8B`, `!range [0, isize::MAX)`) and slot `2` (`MetadataAlign`, `+16B`, `!range [1, Align::max]`), then conditionally invokes `self.1.deallocate(..., layout)` when `layout.size() != 0`. Under both native `-O0`/`-O2` and `Miri` (Stacked Borrows and `-Zmiri-tree-borrows`), `SpyAlloc::dealloc` records **`DEALLOC_LAYOUTS=[(32, 32), (32, 32), (64, 32)]`**, proving zero size/alignment mismatch across single-hop (`Box<dyn Sub> -> Box<dyn SuperB>`, offset `40`), 3-hop (`Box<dyn Tier3> -> Tier2 -> Tier1 -> Tier0`, offsets `104 -> 72 -> 40`), and `!needs_drop` (`NoDropBig`, `(64, 32)`) coercions.

   Exact observed LLVM IR (`-O2` for `drop_glue::<Box<dyn SuperB>>` and `-O0` for `upcast_chain_3hop`, `support/probe_output/probe_results.json` lines `384` and `459`):

   ```llvm
   ; drop_glue::<Box<dyn SuperB>> (-O2): nullable slot-0 drop, then slot-1 size & slot-2 align dealloc
   %1 = load ptr, ptr %_6.1, align 8, !invariant.load !8
   %.not = icmp eq ptr %1, null
   br i1 %.not, label %bb3, label %is_not_null
   ...
   bb3:
   %2 = getelementptr inbounds nuw i8, ptr %_6.1, i64 8
   %size.i = load i64, ptr %2, align 8, !range !27, !invariant.load !8
   %3 = icmp eq i64 %size.i, 0
   br i1 %3, label %...exit, label %...deallocate.exit.i
   ...
   %4 = getelementptr inbounds nuw i8, ptr %_6.1, i64 16
   %align.i = load i64, ptr %4, align 8, !range !53, !invariant.load !8
   tail call fastcc void @_RNv...SpyAlloc...dealloc(ptr noundef nonnull %ptr.0.i, i64 ... %align.i, i64 ... %size.i)

   ; upcast_chain_3hop (-O0): sequential TraitVPtr loads at slots 13, 9, 5 (bytes 104, 72, 40)
   %0 = getelementptr inbounds i8, ptr %b.1, i64 104
   %b2.1 = load ptr, ptr %0, align 8, !invariant.load !5, !nonnull !5
   %1 = getelementptr inbounds i8, ptr %b2.1, i64 72
   %b1.1 = load ptr, ptr %1, align 8, !invariant.load !5, !nonnull !5
   %2 = getelementptr inbounds i8, ptr %b1.1, i64 40
   %b0.1 = load ptr, ptr %2, align 8, !invariant.load !5, !nonnull !5
   ```

---

### 5. Kernel-Checked Lean `v4.34.1` Formalization

Basis: `source + execution + derived`

`support/TraitUpcastingVtableSegmentsAndBoxDropSoundness.lean` (`1,724` lines, `82,538` bytes, compiled in `16.022s` under `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`) mechanizes all three pillars using pure `Init` with **every definition declared `noncomputable def`**, zero `deriving` clauses, zero forbidden tactics (`0` `sorry`, `0` `admit`, `0` `Classical`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`), and zero compiler `._unsafe_rec` constants across all `208,881` constants in `env.constants.map₁` (`857` module constants, `513` defs, `232` `.thmInfo` declarations, `137` zero-axiom theorems, transitive axioms `[Quot.sound, propext]`, `AUDIT_VIOLATIONS=0`, `support/lean_check_receipt.json`):

| Pillar | Key Formal Theorems in `TraitUpcastingVtableSoundness` | Property Established |
| :--- | :--- | :--- |
| **DFS Segmentation & Deduplication** | `prepareSegments_unique_traits`, `prepareSegments_first_is_dsa` | Universal `NoDupTraits` over arbitrary finite DAGs/fuels (`DFSInvariant` induction) + `.metadataDSA` always at head |
| **Slot Layout & Indirection** | `vtableEntries_header_dsa`, `secondary_vptr_slot_exact`, `primary_prefix_slot_emits_no_vptr` | Slots `0..2` carry concrete `DSAHeader`; every `Some idx` satisfies `3 <= idx` and reads `.traitVPtr target`; `Some none` witnesses `emitVptr = false` |
| **View Coherence & Dispatch** | `upcastViewStep_sound`, `upcastViewChain_wellFormed`, `wellFormedView_dsa_eq`, `wellFormedView_dispatch_eq_direct` | Upcasts of arbitrary chain length preserve `ListPrefix (vtableEntries staticTrait) (vtableEntries vtableTrait)`, concrete `DSA`, and exact method dispatch |
| **Diamond Coherence & Selection** | `diamond_path_coherence`, `selectUpcast_singleton_unique`, `selectUpcast_multi_infer_ambiguous` | Arbitrary left/right/direct diamond paths agree on `DSA` & `Root` dispatch even when `vtableTrait` handles differ; single concrete generic diamond selects uniquely vs. multi-instantiation `?0` ambiguity |
| **Box Drop & Deallocation** | `box_upcast_chain_drop_dealloc_sound` | For arbitrary `ct` and valid upcast chain, `dropBoxDyn` fires `callDrop` iff `needsDrop`, precedes `dealloc`, and passes exact `ct.layout` (`err = HeapError.ok`, block freed) |
| **Empirical Offset & Neg-Space Checks** | `expA_secondary_vptr_slots_exact`, `expB_diamond_paths_agree_despite_distinct_vptrs`, `expB_generic_diamond_sharpness`, `expC_three_hop_vptr_slots_exact`, `expC_box_3hop_and_nodrop_verified`, `counterexample_wrong_prefix_reuse_dispatches_wrong_method`, `counterexample_wrong_supertrait_layout_dealloc_ub` | Kernel `rfl`/constructive witnesses reproducing exact byte/slot numbers (`5, 8, 6, 8, 5, 13, 9, 5`) and proving dispatch/dealloc UB when `TraitVPtr` adjustment or concrete `DSA` metadata is violated |
| **Anneal TCB Boundary** | `anneal_tcb_fail_closed_on_dyn_upcast` | Models `MirTy.unsupportedDyn` fail-closed rejection behavior |

---

### 6. Anneal Trusted Computing Base (`MirAst` / `MirSemantics`) Boundary

Basis: `source + derived`

In `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`:

- `trusted/lean/Trusted/MirAst.lean` maps `TyKind::Dynamic` (along with `FnDef`, `FnPtr`, `Closure`) into `MirTy.unsupported` (lines `308..321`), maps every `Rvalue::Cast` (covering `PointerCoercion::Unsize`) into `Rvalue.unsupported` (lines `612..628`), and maps `TerminatorKind::Drop` and indirect `TerminatorKind::Call` into `TerminatorKind.unsupported` (lines `782..795`).
- `trusted/lean/Trusted/MirSemantics.lean` evaluates `evalRvalue` (`line 1313`) and `evalTerminator` (`lines 1568..1569`) by returning `.error .unsupported` / `.fault .unsupported`.

**Net soundness impact**: Anneal's fail-closed boundary guarantees **soundness by non-admission** (`anneal_tcb_fail_closed_on_dyn_upcast`): it cannot mis-verify a trait-object upcast, indirect vtable call, or `Box<dyn Trait>` drop into a false proof, because any verification item touching `dyn` metadata or `Drop` terminators halts cleanly as `.unsupported`. Extending Anneal to verify safe/unsafe `dyn` upcasts would require adding wide-pointer values carrying `(ptr, VtableId)`, a read-only `GlobalAlloc::VTable(ConcreteTy, PrincipalTrait)` table preserving concrete `DSA`, prefix/secondary `Unsize` transitions matching `supertrait_vtable_slot`, and `Drop` terminator semantics checking nullable slot `0` and concrete `Layout` deallocation.

---

## Boundaries

The following negative space boundaries define what this investigation did not cover, could not resolve from inspection alone, or proved out of scope:

- **Not examined**: Associated-type projection ambiguity when `match_upcast_principal` returns `Ok(None)` (`candidates.ambiguous = true` in `candidate_assembly.rs` line `1074`); higher-ranked trait object bounds (`for<'a> &'a T: Unsize<Trait+'a>`, skipped at line `1006`); unstable `-Z no-trait-vptr` codegen mode; `-C lto=thin` / cross-DSO vtable deduplication across multiple crates or shared libraries; non-64-bit pointer ABIs (`ptr_size != 8`) or packed/custom-aligned wide-pointer targets; unwinding-path (`bb4 (cleanup)`) runtime panic tests during `DropTracker::drop` (unwind MIR edges were verified in `.mir` dumps and LLVM `landingpad`/`resume` IR, not panicking live).
- **Known not to apply**:
  - Single-generic diamond ambiguity rejection: `SameGenDia: LeftU8 + RightU8` coerced to `&dyn GenRoot<_>` is **accepted** (`rustc` exit code `0`, `b::same_gen_diamond_infer_accepted = true`), because `util::supertraits`'s `Elaborator` deduplicates identical anonymized `PredicateKind`s prior to `assemble_candidates_for_unsizing`. Ambiguity (`E0308`) requires *distinct* non-identical generic instantiations (`AmbigDia: GenRoot<u8> + GenRoot<u16>`).
  - Vtable address equality under `Miri`: checking `(r_sub as *const _).cast::<()>() == ...` or raw vptr integers does **not** hold under `Miri` even on primary-prefix upcasts (`VPTR_SUB_EQ_A=false` in both Stacked Borrows and Tree Borrows), unlike native LLVM compilation (`VPTR_SUB_EQ_A=true`).
  - Historic path `compiler/rustc_mir_dataflow/src/elaborate_drops.rs`: returns HTTP `404` at both `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and `5debe6a1244452beced762385f88a51857a915fc`; MIR drop elaboration lives under `compiler/rustc_mir_transform/src/elaborate_drop.rs` (checked and verified in `support/pin_receipt.json`). Similarly `compiler/rustc_codegen_llvm/src/meth.rs` returns `404` (vtable indexing lives in `compiler/rustc_codegen_ssa/src/meth.rs`).
- **Unknown**: Whether external third-party proof backends (Aeneas, Charon, MiniRust, Kani) encode `TraitVPtr` slots uniformly across arbitrary future `-Z` flags (`-Z new-llvm-pass-manager`, cross-crate vtable merging optimizations) without inspecting LLVM post-link tables.
- **Unsupported**: `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` explicitly rejects `TyKind::Dynamic`, `Rvalue::Cast` (`Unsize`), indirect `Call`, and `TerminatorKind::Drop` as `FaultKind.unsupported` in both `MirAst.lean` and `MirSemantics.lean`.

---

## Evidence

### 1. Pinned Primary Sources Verified (`support/pin_receipt.json`: `6/6` commits, `42/42` files)

| Repository & Revision | File Path & Narrowest Anchors | Verified Role |
| :--- | :--- | :--- |
| `rust-lang/rust` (`14210df0e`, `5debe6a1`) | `compiler/rustc_middle/src/ty/vtable.rs` (`12..156`: `VtblEntry`, `COMMON_VTABLE_ENTRIES`, `vtable_min_entries`, `vtable_allocation_provider`) | `DSA` slots 0..2, null drop slot, `Vacant` uninit/undef, recursive `TraitVPtr(ty, Some(super_trait_ref))` |
| `rust-lang/rust` (`14210df0e`, `5debe6a1`) | `compiler/rustc_trait_selection/src/traits/vtable.rs` (`38..189`, `384..499`: `prepare_vtable_segments_inner`, `supertrait_vtable_slot`, `vtable_prefix_traits`) | DFS prefix sharing, `PredicateSet` dedup, `emit_vptr_on_new_entry`, `supertrait_def_ids().any(has_own_existential_vtable_entries)` |
| `rust-lang/rust` (`14210df0e`, `5debe6a1`) | `compiler/rustc_trait_selection/src/traits/select/candidate_assembly.rs` (`990..1085`), `confirmation.rs` (`936..972`), `mod.rs` (`1874..1884`) | `assemble_candidates_for_unsizing`, `confirm_trait_upcasting_unsize_candidate`, `winnow_candidates` `has_non_region_infer` check |
| `rust-lang/rust` (`14210df0e`, `5debe6a1`) | `compiler/rustc_type_ir/src/elaborate.rs` (`Elaborator::extend_deduped`), `compiler/rustc_trait_selection/src/traits/util.rs` (`supertraits`) | Anonymized `PredicateKind` deduplication explaining `SameGenDia -> &dyn GenRoot<_>` acceptance |
| `rust-lang/rust` (`14210df0e`, `5debe6a1`) | `compiler/rustc_codegen_ssa/src/base.rs` (`161..313`), `meth.rs` (`95..103`), `size_of_val.rs` (`14..45`), `mir/block.rs` (`684..750`) | `unsized_info`, `unsize_ptr`, `coerce_unsized_into`, `get_data_ptr`, `size_and_align_of_dst`, nullable `codegen_drop_terminator` |
| `rust-lang/rust` (`14210df0e`, `5debe6a1`) | `compiler/rustc_mir_transform/src/{mentioned_items.rs:71..96, elaborate_drop.rs:1035..1048, shim.rs}` | `MentionedItem::UnsizeCast`, `adt.is_box()` inner-before-outer drop elaboration |
| `rust-lang/rust` (`14210df0e`, `5debe6a1`) | `library/alloc/src/boxed.rs` (`2126..2146`), `library/core/src/alloc/layout.rs` (`259..264`) | `<Box<T, A> as Drop>::drop` -> `Layout::for_value_raw` -> conditional `deallocate` |
| `rust-lang/reference` (`c9cc3282`) | `src/type-coercions.md` (`155..211`), `src/types/trait-object.md` (`1..88`) | Normative unsized coercion and trait object semantics |
| `rust-lang/rfcs` (`f43d5789`) | `text/3324-dyn-upcasting.md` | Trait upcasting stabilization specification |
| `joshlf/anneal` (`c131b320`) | `trusted/lean/Trusted/MirAst.lean` (`308..321`, `612..628`, `782..795`), `MirSemantics.lean` (`1313`, `1568..1569`) | Fail-closed `.unsupported` boundary |

### 2. Differential Compiler, LLVM-IR, MIR, and `Miri` Runs (`17/17` Checks Passing)

Preserved runnable harness `support/probe_trait_upcasting_vtable_segments_and_box_drop.py` executed against `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`LLVM 22.1.6`) and `miri 0.1.0 (14210df0e2 2026-05-31)` yields `support/probe_output/{probe_results.json, llvm_ir_excerpts.txt, mir_excerpts.txt}` across five preserved specimens in `support/specimens/`:

| Experiment & Specimen (`sha256` prefix) | Execution Modes | Observed Outcomes |
| :--- | :--- | :--- |
| **Exp A**: `exp_a_multi_supertrait_vtable.rs` (`e8834dd2`) | Native `-O0`/`-O2`, LLVM IR, MIR (`post-cleanup` + `runtime-optimized`), Miri SB & TB | Native `-O2`: `SUB_DATA_EQ_A=true SUB_DATA_EQ_B=true`, `VPTR_SUB_EQ_A=true VPTR_SUB_EQ_B=false VPTR_B_EQ_DIRECT_B=true`, `VPTR_AFTER_EMPTY_EQ_B=true`, `VPTR_TRI_EQ_A=true VPTR_TRI_EQ_B=false VPTR_TRI_EQ_C=false`, `SIZES=16,16,16 ALIGNS=16,16,16`, `CALLS=17,27,107,27,27,39,407`. Miri SB/TB: `rc=0`, all `VPTR_*_EQ_*=false`, identical calls/sizes/aligns. IR: `GEP +40` (`upcast_to_b`, `upcast_tri_to_b`), `GEP +64` (`upcast_tri_to_c`), zero loads (`upcast_to_a`, `upcast_after_empty_to_b`, `upcast_tri_to_a`), `@vtable.1` `[8 x i8] undef`. |
| **Exp B (pos)**: `exp_b_diamond_upcast.rs` (`cf19389d`) | Native `-O0`/`-O2`, LLVM IR, MIR, Miri SB & TB | Native `-O2`: `D_EQ_L=true L_EQ_ROOT=true D_EQ_ROOT_FROM_D=true R_EQ_RDIR=true ROOT_FROM_R_EQ_DIR=false D_EQ_R=false ROOT_FROM_D_EQ_ROOT_FROM_R=false`, `ASYM_D_EQ_ROOT=true ASYM_D_EQ_R2=false ASYM_R2_EQ_ROOT=false ASYM_ROOT_CALLS=101,101`, `CALLS=104,102,103,101,101,101 GEN_TAGS=8,16`. IR: `dia_to_right` `GEP +48`; `asym_to_right_second` `GEP +64`; `right_second_to_root` `GEP +40`. Miri SB/TB: `rc=0`. |
| **Exp B (neg)**: `exp_b_neg_ambig_infer.rs` (`49b56b33`), `exp_b_neg_same_infer.rs` (`11df765c`) | `rustc --edition=2021` | `AmbigDia -> &dyn GenRoot<_>` fails (`rc=1`, `error[E0308]`); `SameGenDia -> &dyn GenRoot<_>` succeeds (`rc=0`). |
| **Exp C**: `exp_c_box_upcast_drop_dealloc.rs` (`b3d4b07e`) | Native `-O0`/`-O2`, LLVM IR, MIR, Miri SB & TB (`SpyAlloc`) | `CONCRETE=(32,32) SUB=(32,32) B=(32,32) T0=(32,32) ND=(64,32)`, `VALS=2,105,22`, `DROP_ORDER=["drop_outer", "drop_inner", "after_drop", "drop_outer", "drop_inner_3hop"]`, `DEALLOC_LAYOUTS=[(32, 32), (32, 32), (64, 32)]` identically in `-O0`, `-O2`, Miri SB, and Miri `-Zmiri-tree-borrows`. |

### 3. Lean `v4.34.1` Mechanization & MetaM Environment Audit (`support/lean_check_receipt.json`)

- **Module**: `support/TraitUpcastingVtableSegmentsAndBoxDropSoundness.lean` (`1,724` lines, `82,538` bytes, `sha256: 28ab8a20fa597ef99dc004aae5895c543f992378099de1b214155ae5587b0ea3`).
- **Audit module**: `support/TraitUpcastingVtableSegmentsAudit.lean` (`sha256: e61d66178e33021917380726be39c2225efcd6547f476616b039aa0c93687708`).
- **Execution flags & timing**: `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)`), compile `16.022s` (`563,428` KB max RSS, `olean_bytes: 2,396,784`), MetaM audit `5.367s` (`1,579,932` KB max RSS).
- **Environment audit metrics**: `AUDIT_TOTAL_CONSTANTS=857`, `AUDIT_DEFS=513` (`82` explicit `noncomputable def`s, `0` plain `def`s), `AUDIT_INDUCTIVES=31`, `AUDIT_THEOREMS=232` (`61` surface theorem decls, `AUDIT_ZERO_AXIOM_THEOREMS=137`), `AUDIT_MAP1_TOTAL=208881`, `AUDIT_MAP1_MODULE_CONSTS=857`, `AUDIT_MAP1_MODULE_UNSAFE_REC=0`, `AUDIT_AXIOMS=[Quot.sound, propext]`, `AUDIT_VIOLATIONS=0`, `passed: true`.

---

## Revalidation

To revalidate every empirical, formal, source-pin, and structural invariant independently:

1. **Re-run differential `rustc` / LLVM IR / MIR / `Miri` probes** (requires nightly `rustc` + `miri` component):
   ```bash
   python3 support/probe_trait_upcasting_vtable_segments_and_box_drop.py
   ```
   Verify `Probe checks: 17/17 passed` and confirm zero unexpected changes in `support/probe_output/probe_results.json`.
2. **Re-verify the Lean `v4.34.1` kernel formalization and `env.constants.map₁` audit** (optionally via hardware-bounded `anneal-lean-run`):
   ```bash
   python3 support/check_lean.py \
     --wrapper "$HOME/.local/bin/anneal-lean-run" \
     --lean "$HOME/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean"
   ```
   Confirm `"passed": true`, `AUDIT_VIOLATIONS=0`, `AUDIT_MAP1_MODULE_UNSAFE_REC=0`, and `AUDIT_AXIOMS=[Quot.sound, propext]`.
3. **Re-verify all upstream commit SHAs and raw file paths**:
   ```bash
   python3 support/verify_pins.py
   ```
   Confirm `Pin check: 6/6 commits, 42/42 files verified.` and `"all_verified": true` in `support/pin_receipt.json`.
4. **Track upstream compiler drift against a newer `rustc` revision**: Diff `compiler/rustc_middle/src/ty/vtable.rs`, `compiler/rustc_trait_selection/src/traits/vtable.rs`, `compiler/rustc_trait_selection/src/traits/select/{candidate_assembly.rs, mod.rs}`, `compiler/rustc_codegen_ssa/src/base.rs`, `compiler/rustc_mir_transform/src/elaborate_drop.rs`, and `library/alloc/src/boxed.rs` against `5debe6a1244452beced762385f88a51857a915fc` for any change to `prepare_vtable_segments_inner`, `supertrait_vtable_slot`, `unsized_info`, `winnow_candidates`, `adt.is_box()` drop ordering, or `Box::drop` `Layout::for_value_raw`.
5. **Validate corpus catalog integrity**:
   ```bash
   python3 tools/reference.py catalog && python3 tools/reference.py check
   ```
