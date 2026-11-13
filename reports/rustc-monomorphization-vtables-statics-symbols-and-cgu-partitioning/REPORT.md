# Monomorphization, Vtables, Constant Data, Symbol Mangling, and Codegen-Unit Partitioning in rustc 1.99.1

## Summary

Between `Runtime(Optimized)` MIR and backend instruction emission, `rustc`
(`1.99.1`, `58cf8f9c35b355199727627d07ae34a4e2846d67`) resolves polymorphism,
dynamic dispatch, constant data, symbol names, and compilation granularity
through five tightly coupled subsystems:
1. **Monomorphization and shims (`rustc_monomorphize::collector`, `rustc_middle::ty::instance`):**
   `collect_crate_mono_items` discovers `MonoItem<'tcx>` roots (`Fn`, `Static`,
   `GlobalAsm`) and walks their MIR and `mentioned_items` to close the call,
   drop-glue, function-reference, and unsizing-vtable graph over **5
   `InstanceKind` variants** (`Item`, `Intrinsic`, `LlvmIntrinsic`, `Virtual`,
   `Shim`) and **12 `ShimKind` variants** synthesized in
   `compiler/rustc_mir_transform/src/shim.rs`.
2. **Dynamic dispatch, drop glue, and closures (`rustc_middle::ty::vtable`, `elaborate_drops`):**
   Every trait object vtable begins with a 3-word header
   (`MetadataDropInPlace`, `MetadataSize`, `MetadataAlign`) followed by
   supertrait and principal trait `VtblEntry` slots (`Method(Instance)`,
   `TraitVPtr(TraitRef)` for trait upcasting, or `Vacant`), interned via
   `GlobalAlloc::VTable` and `tcx.vtable_allocation`. Conditional drops lower to
   stack-allocated boolean drop flags (`ElaborateDrops`) plus recursive
   `ShimKind::DropGlue(def_id, Some(ty))` ladders (`drop_in_place`).
3. **Constant data and statics (`rustc_middle::mir::interpret`, `rustc_codegen_llvm::consts`):**
   Every constant and static evaluates to an `Allocation` containing raw bytes,
   an `InitMask` (lowered to `[N x i8] undef` chunks when the chunk count is at
   or below `-Zuninit-const-chunk-threshold`, default `16`), and a
   `ProvenanceMap` of pointer relocations targeting the **5 `GlobalAlloc`
   variants** (`Function`, `VTable`, `Static`, `Memory`, `TypeId`).
4. **Symbol mangling, linkage, and visibility (`rustc_symbol_mangling`, `rustc_monomorphize::partitioning`):**
   `SymbolManglingVersion` supports `Legacy`, `V0`, and `Hashed`, incorporating
   `StableCrateId` (a 64-bit hash of crate name, sorted `-Cmetadata`, `is_exe`,
   and `cfg_version`). Visibility (`Default`, `Hidden`, `Protected`) and
   `Linkage` (`Internal`, `External`, `WeakAny`, `WeakODR`, `LinkOnceODR`,
   `Common`, `ExternalWeak`) are computed from reachability (`SymbolExportLevel::C`
   vs `Rust`), generic sharing (`-Zshare-generics`), and CGU internalization.
5. **Codegen-unit partitioning and incremental reuse (`rustc_monomorphize::partitioning`):**
   Each source module is split into a **stable** CGU (non-generic items) and a
   **.volatile** CGU (generic instantiations), merged down to `-Ccodegen-units`
   by size estimate, and named deterministically (base-36 128-bit hashes under
   `-Cincremental` vs `<crate>.<stable_crate_id>-cgu.<N>` in non-incremental
   builds).

## Applicability

All definitions, algorithms, enum variants, and empirical mono-item/CGU outputs
apply to `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`)
and LLVM `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`).

## Findings

### 1. Mono-Item Collection, `InstanceKind`, `ShimKind`, and Generic Sharing

`Basis: source + execution (compiler/rustc_monomorphize/src/collector.rs:1-260, compiler/rustc_middle/src/ty/instance.rs:62-235, support/probe_mono_vtables_symbols_cgus.py)`

1. **Collection strategies and roots (`collector.rs:56-155`):**
   - `MonoItemCollectionStrategy::Lazy` (default for non-incremental builds
     without `-Clink-dead-code`): roots are public non-generic functions, methods,
     and statics, `#[no_mangle]` / `#[export_name]` items, `main` / entry points,
     and non-generic functions referenced by `cross_crate_inlinable` functions.
   - `MonoItemCollectionStrategy::Eager` (enabled by `-Cincremental` or
     `-Clink-dead-code`): treats *every* non-generic function in the crate as a
     root, instantiates drop glue for every droppable type, and instantiates
     default trait method bodies upfront so small edits do not churn the global
     mono-item graph.
2. **All 5 `InstanceKind` and 12 `ShimKind` variants (`instance.rs:62-198`, `shim.rs:34-160`):**
   - `InstanceKind::Item(DefId)`: user-defined `fn`, closure, or coroutine;
     body comes from `optimized_mir` (or `mir_for_ctfe` for tuple/variant
     constructors and const contexts).
   - `InstanceKind::Intrinsic(DefId)`: `#[rustc_intrinsic]` function; lowered
     inline in the caller by `codegen_intrinsic_call` unless moved to
     `fallback_intrinsics`.
   - `InstanceKind::LlvmIntrinsic(DefId)`: `extern "unadjusted"` `link_name = "llvm.*"`
     binding from `core::arch`.
   - `InstanceKind::Virtual(DefId, usize)`: dynamic dispatch call to slot `usize`
     of a trait object vtable.
   - `InstanceKind::Shim(ShimKind<'tcx>)`: synthesized by `make_shim`
     (`compiler/rustc_mir_transform/src/shim.rs:34`):

| `ShimKind` Variant | Generated MIR Body in `shim.rs` |
| :--- | :--- |
| `VTable(DefId)` | Dereferences `*mut Self` receiver for `unsized_fn_params` and calls `DefId` directly |
| `Reify(DefId, Option<ReifyReason>)` | Wraps `InstanceKind::Virtual` or a `#[track_caller]` function (passing its own definition span as implicit `&Location`) so it can be coerced to a `fn()` pointer (`ReifyReason::FnPtr`) or vtable slot (`ReifyReason::Vtable`) |
| `FnPtr(DefId, Ty<'tcx>)` | Implements `<fn() as FnOnce/FnMut/Fn>::call*` by dereferencing `&self` / `&mut self` (if `Fn`/`FnMut`) and making an indirect call |
| `ClosureOnce { call_once, closure, track_caller }` | Implements `<C as FnOnce>::call_once` for an `Fn` or `FnMut` closure `C` by taking `&mut self` on a local stack slot and calling `<C as FnMut>::call_mut` |
| `ConstructCoroutineInClosure { coroutine_closure_def_id, receiver_by_ref }` | Moves upvars out of an `async` closure (`CoroutineClosure`) into its `FnOnce`-flavored coroutine |
| `ThreadLocal(DefId)` | Synthesizes a dylib-exportable accessor function returning `&T` for a `#[thread_local]` static |
| `FutureDropPoll(DefId, Ty<'tcx>, Ty<'tcx>)` | Proxy poll shim for async drop of a future |
| `DropGlue(DefId, Option<Ty<'tcx>>)` | Synthesizes `core::ptr::drop_in_place::<T>(*mut T)` (`build_drop_shim`: calls `T::drop(&mut *self)` if `T: Drop`, then drops fields in declaration order or switches on enum discriminant) |
| `Clone(DefId, Ty<'tcx>)` | Synthesizes `<T as Clone>::clone` for `Copy` types, tuples, arrays, and closures |
| `FnPtrAddr(DefId, Ty<'tcx>)` | Synthesizes `<F as FnPtr>::addr` casting `self` to `*const ()` |
| `AsyncDropGlueCtor(DefId, Ty<'tcx>)` & `AsyncDropGlue(DefId, Ty<'tcx>)` | Constructor and state-machine coroutine poll body for `async_drop_in_place::<T>` |

3. **Cross-crate inlinability and `-Zshare-generics` (`cross_crate_inline.rs`, `instance.rs:214-255`):**
   - A function is `cross_crate_inlinable` if it has an explicit `#[inline]`
     attribute, or if `-Zcross-crate-inline-threshold` (or `-Copt-level` mir
     inlining heuristics) marks its MIR body small and non-exporting.
   - `Session::share_generics` defaults to **enabled** for `-Copt-level=0` /
     `1` / `s` / `z` and incremental builds, and **disabled** for non-incremental
     `-Copt-level=2` / `3` when LTO is not fat. When `share-generics` is active,
     `Instance::upstream_monomorphization` reuses exported monomorphizations from
     upstream `.rlib` crates instead of re-instantiating `LocalCopy` duplicates.

### 2. Dynamic Dispatch, Vtable Layout, Drop Flags, and Closure ABIs

`Basis: source + execution (compiler/rustc_middle/src/ty/vtable.rs:13-155, compiler/rustc_mir_transform/src/elaborate_drop.rs)`

1. **Vtable layout and upcasting (`vtable.rs:13-90`):**
   - Every vtable begins with `TyCtxt::COMMON_VTABLE_ENTRIES`:
     - Index `0`: `VtblEntry::MetadataDropInPlace` (pointer to `drop_in_place::<T>`)
     - Index `1`: `VtblEntry::MetadataSize` (`usize` byte size of `T`)
     - Index `2`: `VtblEntry::MetadataAlign` (`usize` byte alignment of `T`)
   - Subsequent indices follow `elaborate::supertrait_def_ids(tcx, trait_ref.def_id)`:
     dispatchable methods occupy `VtblEntry::Method(Instance<'tcx>)`,
     `where Self: Sized` methods occupy `VtblEntry::Vacant` (omitted from the
     emitted memory allocation), and non-first supertraits with vtable entries
     get a `VtblEntry::TraitVPtr(TraitRef<'tcx>)` slot containing a pointer to a
     separate supertrait vtable. Trait upcasting (`&dyn LoudSpeak as &dyn Speak`
     in `support/probe_mono_vtables_symbols_cgus.py`) either reuses the same
     vtable pointer (when the target supertrait is a prefix at offset `0`) or
     loads the `TraitVPtr` entry from the source vtable.
   - Vtable deduplication: `tcx.vtable_allocation((ty, poly_trait_ref))` is a
     memoized query that constructs one `Allocation` per `(Ty, Option<ExistentialTraitRef>)`
     pair; codegen emits it with `unnamed_addr` constant global linkage so the
     linker can merge identical vtables across CGUs.
2. **Drop elaboration and drop flags (`elaborate_drops.rs`, `elaborate_drop.rs`):**
   - `ElaborateDrops` classifies every `TerminatorKind::Drop { place, .. }` using
     definite-initialization (`MaybeInitializedPlaces` / `MaybeUninitializedPlaces`)
     dataflow:
     - **Statically initialized:** emits a direct call to `drop_in_place::<T>(&mut place)`.
     - **Statically uninitialized:** removes the `Drop` terminator entirely.
     - **Dynamically initialized:** allocates a fresh boolean stack local
       (`LocalDecl` of type `bool`), initializes it to `false` on entry, sets it
       to `true` at assignments and `false` on moves, and branches via
       `SwitchInt` before calling `drop_in_place::<T>`.
3. **Closure ABIs:**
   - All closures use `ExternAbi::RustCall` at the MIR level, where the user
     arguments are packed into a single tuple argument (`args: (A, B, ...)`).
   - `rustc_ty_utils::abi::fn_abi_new_uncached` untuples that final tuple
     argument when computing `FnAbi<'tcx, Ty<'tcx>>`, so at the machine/LLVM ABI
     level a closure's parameters are `(env_ptr, arg_0, arg_1, ...)`.

### 3. Constant Allocations, Provenance Relocations, Statics, and `TypeId`

`Basis: source (compiler/rustc_middle/src/mir/interpret/allocation.rs:95-160, compiler/rustc_middle/src/mir/interpret/mod.rs:254-350, compiler/rustc_codegen_llvm/src/consts.rs:40-190)`

1. **Lowering `Allocation` to globals (`const_alloc_to_llvm`, `consts.rs:40-157`):**
   - An `Allocation` consists of `bytes: Box<[u8]>`, `provenance: ProvenanceMap<CtfeProvenance>`,
     `init_mask: InitMask`, `align: Align`, and `mutability: Mutability`.
   - `const_alloc_to_llvm` iterates through `alloc.provenance().ptrs()` in
     increasing byte-offset order. Each pointer-sized provenance slot at `offset`
     reads the target-endian integer addend `ptr_offset` stored in
     `alloc.bytes[offset .. offset + ptr_size]` and emits a relocation to
     `tcx.global_alloc(prov.alloc_id())` plus `ptr_offset`:
     - `GlobalAlloc::Function { instance }` $\rightarrow$ function symbol address
     - `GlobalAlloc::VTable(ty, dyn_ty)` $\rightarrow$ vtable global address
     - `GlobalAlloc::Static(def_id)` $\rightarrow$ static global symbol address
     - `GlobalAlloc::Memory(const_alloc)` $\rightarrow$ anonymous constant global address
     - `GlobalAlloc::TypeId { ty }` $\rightarrow$ 128-bit `TypeId` hash segment
   - Between provenance entries, `append_chunks_of_init_and_uninit_bytes`
     splits byte ranges using `alloc.init_mask().range_as_init_chunks(...)`:
     `InitChunk::Init(range)` becomes `cx.const_bytes(bytes)` (`[N x i8] c"..."`),
     and `InitChunk::Uninit(range)` becomes `cx.const_undef(cx.type_array(cx.type_i8(), len))`
     (`[N x i8] undef`) unless the chunk count exceeds
     `-Zuninit-const-chunk-threshold` (`16`), in which case uninitialized bytes
     are emitted as concrete `const_bytes` to avoid pathological LLVM constant ASTs.
   - If the entire allocation has no provenance and a single initialized chunk,
     `const_alloc_to_llvm` emits a bare `[N x i8]` array (rather than a packed
     struct `{ ... }`) so LLVM can merge C-string literals.
2. **Statics, interior mutability, sections, and TLS (`interpret/mod.rs:318-346`, `consts.rs:160-420`):**
   - Even an immutable `static S: T` is placed in a writable data section
     (`Mutability::Mut`) if `!T::is_freeze(tcx, typing_env)` (i.e., `T` contains
     `UnsafeCell`).
   - `#[link_section = "..."]` sets the object section; `#[used(compiler)]` appends
     the global to `@llvm.compiler.used`, while `#[used(linker)]` appends it to
     `@llvm.used`.
   - `#[thread_local]` statics set LLVM's `thread_local(localexec / initialexec / localdynamic / generaldynamic)`
     mode according to `CodegenCx::tls_model`.

### 4. Symbol Mangling, `StableCrateId`, Linkage, and Visibility

`Basis: source (compiler/rustc_symbol_mangling/src/lib.rs:1-210, compiler/rustc_span/src/def_id.rs:157-210, compiler/rustc_monomorphize/src/partitioning.rs:900-994)`

1. **Mangling schemes (`SymbolManglingVersion`):**
   - `Legacy` (`_ZN...17h<16-hex-hash>E`): Itanium C++-style length-prefixed path
     segments followed by a 64-bit `SipHash128` hash (`17h...`) of the `DefPath`,
     `StableCrateId`, generic args, and `InstantiationMode`.
   - `V0` (`_RNv...`): Rust RFC 2603 unambiguous reversible grammar encoding
     crate disambiguator (`StableCrateId`), generic arguments, closure/shim kinds,
     and instantiating crate (when `InstantiationMode::LocalCopy` or non-exported
     generic).
   - `Hashed`: compact hash-only mangling.
   - Items marked `#[no_mangle]` or `#[export_name = "foo"]` bypass mangling;
     items marked `#[rustc_std_internal_symbol]` (and weak lang items) use `v0`
     mangling seeded with `rustc`'s version so staticlibs from different compiler
     versions cannot collide silently (`rustc_symbol_mangling/src/lib.rs:192-210`).
2. **Visibility and internalization (`partitioning.rs:900-994`):**
   - `SymbolExportLevel::C` (`#[no_mangle]`, `#[export_name]`, `pub extern "C"`)
     receives `Visibility::Default` (interposable).
   - `SymbolExportLevel::Rust` receives `tcx.sess.default_visibility()` (typically
     `Visibility::Default`, or `Hidden` when `-Zdefault-visibility=hidden`).
   - Unreachable items and `InstantiationMode::LocalCopy` items are placed in
     `internalization_candidates` and given `Linkage::Internal` during
     `internalize_symbols` (unless `-Clink-dead-code` is set or the item is a
     weak lang item / `#[rustc_std_internal_symbol]`).

### 5. Codegen-Unit Partitioning and Incremental Stability

`Basis: source + execution (compiler/rustc_monomorphize/src/partitioning.rs:144-900, support/probe_mono_vtables_symbols_cgus.py, support/mono_and_cgu_probe_results.json)`

`partition` (`partitioning.rs:144-200`) runs in three steps:
1. **`place_mono_items`:** Assigns each `MonoItem` to an initial CGU named after
   its defining module (`<crate>-<mod_path>` for non-generic `GloballyShared`
   items, and `<crate>-<mod_path>.volatile` for generic `GloballyShared` items).
   `InstantiationMode::LocalCopy` items (such as `#[inline]` functions) are placed
   into *every* CGU that calls them with `Linkage::Internal`.
2. **`merge_codegen_units`:**
   - **Non-incremental mode:** Sorts CGUs by `size_estimate` descending, merges
     smallest pairs until `cgus.len() <= max_cgu_count`, and renumbers them
     `<crate>.<stable_crate_id>-cgu.0 .. cgu.<K-1>`.
   - **Incremental mode (`-Cincremental`):** Preserves module-based CGU names
     (hashed to 25-character base-36 strings such as `7yxtcyy69ainp7bv6jy9dua7k`
     for `cgu_probe-mod_a` and `dd77os261oh14ls6peypvgnbb` for
     `cgu_probe-mod_a.volatile`).
3. **Empirical edit stability (`support/mono_and_cgu_probe_results.json`):**
   - Editing the body of `mod_b::fb` (`v1_baseline` $\rightarrow$
     `v2_body_edit_in_mod_b`) modifies only `mod_b`'s CGU (`bjm99ol5210hcww6o7h32dgin`);
     all other CGUs reuse their cached `WorkProduct` object files before LTO.
   - Adding a new generic instantiation `generic_shared::<u64>` inside `mod_c::fc`
     (`v1_baseline` $\rightarrow$ `v3_new_generic_inst_in_mod_c`) modifies only
     `mod_c`'s CGU (`btssh5sfqhk3twxkoqscqxxc1`) and `mod_a`'s `.volatile` CGU
     (`dd77os261oh14ls6peypvgnbb`), while leaving `mod_a`'s non-generic CGU
     (`7yxtcyy69ainp7bv6jy9dua7k`) and `mod_b`'s CGU (`bjm99ol5210hcww6o7h32dgin`)
     untouched!
   - A verified backend that caches per-function or per-CGU correctness
     derivations should key its proof cache by `(Instance, MirBodyDigest, CalleeAbiDigests)`
     or adopt `rustc`'s `(stable, .volatile)` module split so adding a generic
     instantiation in one module never invalidates proofs of non-generic functions
     in the defining module.

## Boundaries

- **Cross-language LTO (`-Clinker-plugin-lto`):** Bitcode-level merging with
  Clang-compiled C/C++ objects occurs inside `lld` after `rustc_codegen_llvm`
  emits bitcode sections and is outside `rustc_monomorphize`'s partitioning graph.

## Evidence

- **Executable probe and results:**
  - `support/probe_mono_vtables_symbols_cgus.py`
  - `support/mono_and_cgu_probe_results.json`
- **Primary source citations (`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`):**
  - `compiler/rustc_middle/src/ty/instance.rs:62-255` (`InstanceKind`, `ShimKind`, `upstream_monomorphization`)
  - `compiler/rustc_mir_transform/src/shim.rs:34-160` (`make_shim`)
  - `compiler/rustc_middle/src/ty/vtable.rs:13-155` (`VtblEntry`, `vtable_allocation_provider`)
  - `compiler/rustc_middle/src/mir/interpret/mod.rs:254-350` (`GlobalAlloc`)
  - `compiler/rustc_middle/src/mir/interpret/allocation.rs:95-160` (`Allocation`, `AllocFlags`)
  - `compiler/rustc_codegen_llvm/src/consts.rs:40-190` (`const_alloc_to_llvm`, `codegen_static_initializer`)
  - `compiler/rustc_symbol_mangling/src/lib.rs:1-210` (`symbol_name_provider`)
  - `compiler/rustc_monomorphize/src/collector.rs:1-260` (`collect_crate_mono_items`)
  - `compiler/rustc_monomorphize/src/partitioning.rs:144-1150` (`partition`, `place_mono_items`, `default_visibility`)

## Revalidation

Run `support/probe_mono_vtables_symbols_cgus.py`:

```bash
python3 reports/rustc-monomorphization-vtables-statics-symbols-and-cgu-partitioning/support/probe_mono_vtables_symbols_cgus.py \
  --toolchain 1.99.1-x86_64-unknown-linux-gnu \
  --out /tmp/mono_and_cgu_probe_results.json
```

Compare `/tmp/mono_and_cgu_probe_results.json` against
`support/mono_and_cgu_probe_results.json` to verify mono-item collection and CGU
partitioning stability.
