# `rustc` monomorphization `Lazy` vs. `Eager` collection, `#[used(compiler)]` vs. `#[used(linker)]`, and `-Z polymorphize` removal with LLVM `MergeFunctions`

## Summary

`rustc` governs code emission, cross-crate inlining deferral, linker garbage collection of static globals, and post-monomorphization code deduplication through three interacting mechanisms across `rustc_monomorphize`, `rustc_codegen_ssa`, `rustc_codegen_llvm`, and LLVM's optimization and object-emission pipeline. Based on source inspection of `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly`, pinned `rust-lang/llvm-project@08c84e69a84d95936296dfcab0e38b34100725d5`, LLVM `22.1.6`), source-drift checks against `rust-lang/rust@f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`, upstream LLVM `llvm/llvm-project@ba1d95e0af43ea608d82a16cc1a9694c6b072c02`, live execution of `rustc 1.98.0-nightly` + GNU `ld 2.47` (`support/probe_mono_collector_used_and_merge.py`, `support/probe_results.json`), and a kernel-checked Lean `v4.34.1` formalization (`support/MonoCollectorReachabilityUsedAndMergeFunctionsSoundness.lean`), a later reader should retain the following invariants:

1. **What selects `Lazy` vs. `Eager` monomorphization collection and how `-Z print-mono-items` behaves.** `collect_and_partition_mono_items` (`compiler/rustc_monomorphize/src/partitioning.rs` L1131–1136) chooses `MonoItemCollectionStrategy::Eager` **if and only if** `tcx.sess.link_dead_code()` (`-C link-dead-code=yes`) is enabled, and `MonoItemCollectionStrategy::Lazy` otherwise. Although the doc comment at `compiler/rustc_monomorphize/src/collector.rs` L149–150 still describes `Eager` as meant for incremental compilation, incremental compilation alone does **not** select `Eager`. On `rustc 1.98.0-nightly`, passing `-Z print-mono-items=lazy` fails immediately (`exit 1`: `error: incorrect value 'lazy' for unstable option 'print-mono-items' - one of: 'y', 'yes', 'on', 'true', 'n', 'no', 'off' or 'false' was expected`); observing `Lazy` vs. `Eager` collections requires `-Z print-mono-items=yes` paired with `-C link-dead-code=no` vs. `-C link-dead-code=yes`. Switching to `Eager` adds dead monomorphic items (bin: `17 → 20`; rlib: `10 → 13` on our specimen) and skips `internalize_symbols` (`partitioning.rs` L177–182), leaving every collected item at `External` linkage instead of internalizing single-CGU private items. `Basis: source + execution`
2. **Uninstantiated generics are never roots—even under `Eager`—and `rlib` `Lazy` defers small `pub` functions via `cross_crate_inlinable`.** Both `Lazy` and `Eager` filter roots through `!tcx.generics_of(def_id).requires_monomorphization(tcx)` (`collector.rs` L1653–1658), so an uninstantiated generic `fn gen_dead<T>(x: T) -> T` is absent from all four `(bin|rlib) × (Lazy|Eager)` collections (`contains_gen_dead: false`). In `Lazy` mode, `RootCollector::process_item` unconditionally emits every `DefKind::Static` and `DefKind::GlobalAsm` (L1545–1556), whereas functions enter via `entry_fn` (`push_extra_entry_roots`, adding `std::rt::lang_start::<()>` for `bin` crates, L1690–1728), `EXTERNALLY_IMPLEMENTABLE_ITEM` / `RUSTC_STD_INTERNAL_SYMBOL`, or `tcx.is_reachable_non_generic(def_id)`. Because `reachable_non_generics_provider` (`compiler/rustc_codegen_ssa/src/back/symbol_export.rs` L96) strips items where `tcx.cross_crate_inlinable(def_id)` returns `true`, and `cross_crate_inlinable` (`compiler/rustc_mir_transform/src/cross_crate_inline.rs` L48–104) returns `true` for small unannotated leaf `pub fn pub_dead_small` at `-C opt-level=2` while returning `false` for `#[inline(never)] pub fn pub_dead_exported`, a `Lazy` `rlib` omits `pub_dead_small` (`10` items total) and collects `pub_dead_exported` (`[External]`). A downstream binary referencing both by `fn()` pointer instantiates `mono::pub_dead_small` locally (`9` items total, `[Internal]`), links `mono::pub_dead_exported` from the `.rlib`, and prints `222`. In a `bin` crate (`crates_export_threshold = SymbolExportLevel::C`), neither `pub_dead_small` nor `pub_dead_exported` clears the `C` threshold, so `Lazy` `bin` omits both (`17` items). `Basis: source + execution`
3. **`#[used(compiler)]`, `#[used(linker)]`, and bare `#[used]` divergence.** In `compiler/rustc_codegen_ssa/src/codegen_attrs.rs` L170–186, `#[used(compiler)]` sets `CodegenFnAttrFlags::USED_COMPILER`, `#[used(linker)]` sets `USED_LINKER`, and bare `#[used]` (`UsedBy::Default`) maps to **`USED_LINKER` on every target except `Os::Illumos`** (where it downgrades to `USED_COMPILER`, tracking issue `rust-lang/rust#146169`). `compiler/rustc_codegen_llvm/src/consts.rs` L511–538 and `base.rs` L150–160 lower `USED_COMPILER` into `@llvm.compiler.used` and `USED_LINKER` into `@llvm.used` (both appending globals in section `"llvm.metadata"`, `llvm_context.rs` L701–708). On ELF, `TargetLoweringObjectFileELF` (`llvm/lib/CodeGen/TargetLoweringObjectFileImpl.cpp` L312–316, L768–775, L955–964, L989–990) inspects **only** `@llvm.used` (`collectUsedGlobalVariables(M, Vec, false)`), placing `@llvm.used` statics into unique sections carrying `ELF::SHF_GNU_RETAIN` (`AR` in `readelf -WS`). `@llvm.compiler.used` prevents LLVM `GlobalDCE` stripping inside the compiler module, emits section flags `A` (`SHF_ALLOC` without `R`), and **is stripped** by GNU `ld --gc-sections` when unreferenced (`used_comp_survives_gc: false`), whereas `#[used(linker)]` (`AR`) **survives** `--gc-sections` (`used_link_survives_gc: true`). `Basis: source + execution`
4. **`-Z polymorphize` was removed upstream; LLVM `-O2` `MergeFunctions` now folds bit-identical monomorphizations.** `rust-lang/rust#133883` (`711c8cc690c70d9b4c0e17e90f21f03d4e9d3ebf`, merged `2024-12-07` via `ca13e9169fbbbb126190631b5a1e3e20053a52c1`, `-2643 / +59` lines) deleted `compiler/rustc_monomorphize/src/polymorphize.rs` and removed `-Z polymorphize`; passing `-Z polymorphize=on` to `rustc 1.98.0-nightly` fails (`exit 1`: `error: unknown unstable option: 'polymorphize'`). By default, `TargetOptions::merge_functions` is `MergeFunctions::Aliases` (`compiler/rustc_target/src/spec/mod.rs` L2910), enabled at `-C opt-level` in `{2, 3, s, z}` (`ssa_write.rs` L244–258, disabled at `0`/`1` and during pre-differentiation AutoDiff IR optimization in `write.rs` L578–590) and lowered via `-mergefunc-use-aliases` (`llvm_util.rs` L101–106). Under default `-O2` `Lazy` (`Internal` discardable linkage), `MergeFunctions::writeThunkOrAliasIfNeeded` (`MergeFunctions.cpp` L914–938, L1174–1205) rewrites calls and erases duplicate `poly_const::<u16>` and `poly_const::<u64>` (`ShouldErase`), collapsing `6` `poly_*` definitions to **`4`** (`poly_const::<u8>` plus distinct `poly_size::<u8,u16,u64>`, which fail structural equality due to `size_of::<T>()` constants and distinct `range(...)` return attributes) with `0` aliases. Under `-Clink-dead-code=yes` (`hidden` `External` linkage, not discardable), `MergeFunctions` emits **`4` `define`s + `2` `hidden unnamed_addr alias` entries** under default `Aliases`, or **`6` `define`s (two tail-call thunks)** under `-Z merge-functions=trampolines`. Symbols listed in `@llvm.used` or `@llvm.compiler.used` are excluded from `MergeFunctions` replacement via `!Used.contains(G)` (`MergeFunctions.cpp` L315–317, L1174). Native binaries preserve output parity (`drive(11) == 146` with `MergeFunctions` on vs. `-Z merge-functions=disabled`). `Basis: source + execution`
5. **Executable, kernel-checked Lean `v4.34.1` formalization.** `support/MonoCollectorReachabilityUsedAndMergeFunctionsSoundness.lean` (`1,850` lines; `67` top-level `theorem` declarations, `243` kernel `thmInfo` constants, `69` `noncomputable def` declarations, `22` inductive/structure definitions; checked strictly in `6.225 s` with `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`; MetaM environment audit passed in `5.729 s` confirming `0` `._unsafe_rec` constants, `0` unsafe/partial definitions, `axioms = [propext]`, `0` `Classical.choice`, `0` `sorryAx`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`) proves: `lazy_root_implies_eager_root`, `lazy_reachability_subset_eager`, `eager_never_roots_generic`, `static_always_root`, `rlib_lazy_defers_small_pub_inline`, `rlib_lazy_collects_inline_never_pub`, `lazy_collection_link_complete`, `rlib_deferral_downstream_link_complete`, `used_linker_survives_llvm_and_linker_gc`, `used_compiler_survives_llvm_but_stripped_by_gc`, `bare_used_is_linker_retain_except_illumos`, `used_list_blocks_merge_functions`, `applyMergeTwo_preserves_observational_equivalence` (uniformly covering `eraseAndRewrite`, `emitAlias`, and `emitThunk`), specimen exactness (`17`/`20`, `10`/`13`, `4` vs. `6`, `4+2` aliases, `2` thunks, `146`), and three explicit sharpness counterexamples (**CE1** omitted exported/used root yielding `.missingSymbol`, **CE2** `USED_COMP` stripped by `--gc-sections`, **CE3** unsound merging of `poly_size::<u64>` into `poly_size::<u8>` corrupting `146 → 139`). `Basis: execution (Lean kernel) + derived`
6. **Anneal whole-crate capture completeness and purity interface.** At `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`trusted/lean/Trusted/MirAst.lean` L75–92, L869–882, L915–936), `Trusted.MirAst` treats whole-crate `bodies` completeness under `VerificationScope.crate` as an explicit **external producer obligation** rather than checking reachability closure in Lean, rejects `partial` / `._unsafe_rec` helpers via per-definition `noncomputable` discipline, and currently maps static globals, dynamic trait calls, and non-`FnDef` indirect calls outside direct `TerminatorKind.call` to `.unsupported`. Ingesting `rustc`-collected programs reliably without missing symbols therefore requires matching `Lazy` crate-type root rules (including `Static` initializers, downstream `cross_crate_inlinable` instantiations, and `used` statics) when synthesizing `.crate` captures. `Basis: source`

> **Scope caution.** Empirical measurements come from one toolchain build (`rustc 1.98.0-nightly` / LLVM `22.1.6` / GNU `ld 2.47` on `x86_64-unknown-linux-gnu`) running targeted synthetic probes, not a crates.io census or cross-linker test across Mach-O/COFF/Wasm/`lld`. The Lean development proves properties over its own operational model of MIR monomorphization graphs, section retention flags, and a single-step `MergeFunctions` AST evaluator; it does not verify `rustc`'s Rust source or LLVM's C++ implementation directly. See **Boundaries**.

## Applicability

### Relationships among subjects in `REPORT.json`

- **`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`** (`1.98.0-nightly`, committed `2026-05-31`, pinning submodule **`rust-lang/llvm-project@08c84e69a84d95936296dfcab0e38b34100725d5`**, LLVM `22.1.6`) is the exact compiler executed in `support/probe_mono_collector_used_and_merge.py` and the primary Rust source baseline for all unannotated line citations.
- **`rust-lang/rust@f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`** (`main` HEAD at observation time, `2026-11-23`) was compared directly against `14210df0e` across all ten inspected Rust source files (`collector.rs`, `partitioning.rs`, `reachable.rs`, `symbol_export.rs`, `cross_crate_inline.rs`, `codegen_attrs.rs`, `ssa_write.rs` / `write.rs`, `llvm_util.rs`, `target_spec_mod.rs`, `consts.rs`) to test six-month drift. Module import moves (`rustc_attr_ir`, `rustc_structures::CrateType`, `crate::diagnostics`), PAC signing helpers (`consts.rs`), `offload` kernel root collection (`collector.rs` L1547–1589), and `const always` handling (`cross_crate_inline.rs` L33–37) landed between May and November 2026, while every invariant reported in Findings 1–4 (`link_dead_code()` -> `Eager`, `is_root` generic check, `cross_crate_inlinable` cost threshold & `#[inline(never)]` exemption, `UsedBy::Default` -> `USED_LINKER` except illumos, `add_compiler_used_global` vs. `add_used_global`, `MergeFunctions::Aliases` default, `-O2` enabling) remained unchanged. No executables were compiled with `f7da9a423`.
- **`rust-lang/rust@711c8cc690c70d9b4c0e17e90f21f03d4e9d3ebf`** (PR `#133883`, merged `2024-12-07T05:48:12Z` at `ca13e9169fbbbb126190631b5a1e3e20053a52c1`) supplies the exact historical removal of `polymorphize.rs` and `-Z polymorphize` prior to `rustc 1.98.0-nightly`.
- **`llvm/llvm-project@ba1d95e0af43ea608d82a16cc1a9694c6b072c02`** (`main` HEAD) was inspected directly for `MergeFunctions.cpp`, `TargetLoweringObjectFileImpl.cpp`, `AsmPrinter.cpp`, and `PassBuilderPipelines.cpp`; all behaviors cited match the LLVM IR and ELF sections emitted by the `1.98.0-nightly` compiler's embedded LLVM `22.1.6`.
- **`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`** defines the downstream verification boundary (`Trusted.MirAst`) interpreted through the `rustc` collector and purity findings.
- **`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`** (`v4.34.1`, `x86_64-unknown-linux-gnu`, Release) is the Lean compiler/kernel that checked `support/MonoCollectorReachabilityUsedAndMergeFunctionsSoundness.lean` and ran the MetaM audit.

### Execution environment and probe configuration

All compiler probes executed on `x86_64-unknown-linux-gnu` using `--edition=2024 -C codegen-units=1` with:
- Host linker `GNU ld (GNU Binutils for Debian) 2.47` (`gcc` driver) and toolchain `llvm-nm` / `readelf -WS`.
- Explicit nightly feature gate `#![feature(used_with_arg)]` solely to observe `#[used(compiler)]` alongside `#[used(linker)]`; bare `#[used]` (`USED_DEFAULT`) was compiled without feature gates.
- `-C opt-level=2` across the collector, `rlib`/`bin` deferral, downstream link, and `#[used]` probes, and `-C opt-level={1, 2}` with `-C link-dead-code={no, yes}` and `-Z merge-functions={disabled, trampolines}` across the `MergeFunctions` matrix (`support/probe_mono_collector_used_and_merge.py`).
- Function pointers (`let f: fn() -> u32 = mono::pub_dead_small; let g: fn() -> u32 = mono::pub_dead_exported;`) in the downstream consumer (`app.rs`) so MIR inlining would not fold away `pub_dead_small` before monomorphization collection in the downstream crate.

### What generalizes vs. specimen-specific quantities

- **Architecture- and source-determined rules:** `Lazy` vs. `Eager` selection via `link_dead_code()`, exclusion of `requires_monomorphization` generics from `RootCollector`, unconditional root inclusion of `DefKind::Static` and `DefKind::GlobalAsm`, `SymbolExportLevel::{Rust, C}` thresholding in `symbol_export.rs`, `@llvm.used` vs. `@llvm.compiler.used` generation, and `MergeFunctions` linkage dispatch (`ShouldErase`/`ShouldAlias`/`ShouldThunk` + `Used` exclusion) apply across compiler revisions preserving those mechanisms. Note target-specific branches established directly in source: bare `#[used]` downgrades to `USED_COMPILER` on `Os::Illumos` (`codegen_attrs.rs` L174–183), ELF requires integrated assembler or binutils `>= 2.36` for `SHF_GNU_RETAIN` (`TargetLoweringObjectFileImpl.cpp` L959–963), Mach-O emits `.no_dead_strip` (`AsmPrinter.cpp` L3718–3721), COFF emits `/INCLUDE:` only for non-local linkage (`TargetLoweringObjectFileImpl.cpp` L2049–2058), Wasm marks `Retain` (`L2331–2430`), and COFF aliases forbid local aliasees (`MergeFunctions.cpp` L858–862).
- **Specimen-specific quantities:** Item counts (`17` vs. `20`, `10` vs. `13`, `9`, `4` vs. `6` `define`s) characterize the four self-contained probe programs in `support/probe_mono_collector_used_and_merge.py`; they must not be cited as universal ratios for arbitrary crates.
- **Lean theorems:** Quantified results hold over all models satisfying the Lean predicates; bridging them to `rustc` rests on structural fidelity plus concrete correspondence theorems checked against probe outputs.

## Findings

### 1. Monomorphization collector control flow, `Lazy` vs. `Eager`, and root criteria

`Basis: source + execution`

`collect_and_partition_mono_items` (`compiler/rustc_monomorphize/src/partitioning.rs` L1131–1156 at `14210df0e`) invokes the monomorphization collector and immediately partitions the resulting sorted vector into codegen units:

```rust
// compiler/rustc_monomorphize/src/partitioning.rs L1131-1138 (14210df0e)
fn collect_and_partition_mono_items(tcx: TyCtxt<'_>, (): ()) -> MonoItemPartitions<'_> {
    let collection_strategy = if tcx.sess.link_dead_code() {
        MonoItemCollectionStrategy::Eager
    } else {
        MonoItemCollectionStrategy::Lazy
    };

    let (items, usage_map) = collector::collect_crate_mono_items(tcx, collection_strategy);
```

No other condition flips `MonoItemCollectionStrategy`. Specifically, the comment at `compiler/rustc_monomorphize/src/collector.rs` L149–154 claiming that the `Eager` strategy is meant for incremental compilation is out of date relative to `partitioning.rs` L1132: passing incremental flags alone leaves `tcx.sess.link_dead_code()` false and keeps `Lazy` collection active. Similarly, on the command line, `-Z print-mono-items` requires a strict boolean flag (`y`/`yes`/`on`/`true`/`n`/`no`/`off`/`false`). Passing `-Z print-mono-items=lazy` to `rustc 1.98.0-nightly` exits `1`:

```text
error: incorrect value `lazy` for unstable option `print-mono-items` - one of: `y`, `yes`, `on`, `true`, `n`, `no`, `off` or `false` was expected
```

Inside `collect_crate_mono_items` (`collector.rs` L1807–1839), collection proceeds in two phases:
1. **`collect_roots` (`collector.rs` L1457–1494):** Creates `RootCollector { tcx, strategy: mode, output, entry_fn }`, traverses `hir_crate_items(())` over `free_items()`, `impl_items()`, and `nested_bodies()`, appends runtime start shims via `push_extra_entry_roots()`, and filters every candidate with `mono_item.is_instantiable(tcx)` before graph walk.
2. **Parallel DFS + deterministic sort (`collector.rs` L1826–1838):** Spawns parallel recursion (`collect_items_root` -> `collect_items_rec`, L381–617) tracking `UsedItems` vs. `MentionedItems`, populates `UsageMap` (directed caller-to-callee edges), and sorts `visited` with `tcx.with_stable_hashing_context(...)`. `MonoItem::Static(def_id)` recursion (`L422–460`) evaluates `eval_static_initializer(def_id)` to collect statically referenced provenances, checks drop glue on the static's type, and emits `InstanceKind::ThreadLocalShim` when `tcx.needs_thread_local_shim(def_id)` holds.

`RootCollector` (`collector.rs` L1503–1671) applies fundamentally asymmetric rules across item kinds and strategies:

| HIR / Item Category | `Lazy` (`-C link-dead-code=no`) | `Eager` (`-C link-dead-code=yes`) | Exact `collector.rs` Guard (`14210df0e`) |
| :--- | :--- | :--- | :--- |
| `DefKind::Static`, `DefKind::GlobalAsm` | **Always root** | **Always root** | `L1545–1556` (no `strategy` branch) |
| Entry `main` + `start_fn::<Ret>` (`lang_start`) | **Root** when `entry_fn` exists | **Root** when `entry_fn` exists (plus already via `process_item`) | `push_extra_entry_roots` (`L1690–1728`) |
| Monomorphic `Fn` / `AssocFn` (`!requires_monomorphization`) | Root iff `entry_fn` or `is_reachable_non_generic(def_id)` or `RUSTC_STD_INTERNAL_SYMBOL \| EXTERNALLY_IMPLEMENTABLE_ITEM` | Root iff `!matches!(inline, InlineAttr::Force { .. })` | `is_root` (`L1653–1671`) |
| Generic `Fn` / `AssocFn` (`requires_monomorphization`) | **Never root** | **Never root** | `!self.tcx.generics_of(def_id).requires_monomorphization(self.tcx)` (`L1654`) |
| `DefKind::Const` (non-type-const, non-generic) | Only collected if referenced (`UsedItems`/`MentionedItems`) | Evaluates `const_eval_poly` and collects referenced values | `L1557–1581` |
| `DefKind::Enum`/`Struct`/`Union` non-generic drop glue | Collected only when drop use occurs | Eagerly visits drop glue (`visit_drop_use`) if predicates satisfiable | `L1506–1544` |
| Trait `impl` default methods | Collected only on concrete call/vtable demand | Eagerly collects non-generic default impls | `L1582–1586`, `L1732–1800` |
| Closures / coroutines | Root only for `pub async fn` coroutines without generics | Root for all non-generic instantiable closures/coroutines | `L1600–1648` |

The critical consequence of line `L1654` (`!self.tcx.generics_of(def_id).requires_monomorphization(self.tcx)`) is that **even `-C link-dead-code=yes` (`Eager`) cannot collect uninstantiated generic functions** (`fn gen_dead<T>(x: T) -> T`), because uninstantiated type parameters leave monomorphization substitutions unconstrained. Conversely, statics cannot be generic in Rust and are pushed unconditionally at `L1552–1556` regardless of `Lazy`/`Eager` or `#[used]` attributes.

### 2. Separate compilation boundary: `reachable_non_generics`, `cross_crate_inlinable`, and `internalize_symbols`

`Basis: source + execution`

Whether a non-generic `pub fn` becomes a root in `Lazy` mode depends on two downstream filters beyond visibility:

1. **Inlineability deferral (`compiler/rustc_codegen_ssa/src/back/symbol_export.rs` L49–97 and `compiler/rustc_mir_transform/src/cross_crate_inline.rs` L18–189):**
   `reachable_non_generics_provider` starts from `tcx.reachable_set(())` (which includes reachable public items in library builds; `compiler/rustc_passes/src/reachable.rs` L480–485) and filters candidate functions with:
   ```rust
   // compiler/rustc_codegen_ssa/src/back/symbol_export.rs L87-96 (14210df0e)
   let generics = tcx.generics_of(def_id);
   if generics.requires_monomorphization(tcx) { return None; }
   if Instance::mono(tcx, def_id.into()).def.requires_inline(tcx) { return None; }
   if tcx.cross_crate_inlinable(def_id) { None } else { Some(def_id) }
   ```
   `cross_crate_inlinable` (`cross_crate_inline.rs` L18–104) returns `false` if the item carries an extern indicator (`L22–24`) or `#[inline(never)]` (`InlineAttr::Never`, `L49`: *"Obey source annotations first; this is important because it means we can use `#[inline(never)]` to force code generation"*). For an unannotated public function at `-C opt-level=2` (and non-incremental compilation with MIR available, `L73–88`), `CostChecker` (`L96–104`, L115–188) checks `calls == 0 && resumes == 0 && landing_pads == 0 && statements <= threshold`. Thus a small pure leaf function like `pub fn pub_dead_small() -> u32 { 99 }` returns `cross_crate_inlinable == true`, drops out of `reachable_non_generics`, and has its codegen deferred to downstream crates, whereas `#[inline(never)] pub fn pub_dead_exported() -> u32 { 123 }` returns `false` and **remains** in `reachable_non_generics`.
2. **Crate-type export thresholding (`symbol_export.rs` L25–47, L154–162):**
   `crate_export_threshold` returns `SymbolExportLevel::Rust` for `Rlib | Dylib | Sdylib`, and `SymbolExportLevel::C` for `Executable | StaticLib | ProcMacro | Cdylib`. `is_reachable_non_generic_provider_local` checks `info.level.is_below_threshold(export_threshold)` (`L158`). Hence a plain Rust `pub fn` marked `#[inline(never)]` (`SymbolExportLevel::Rust`) satisfies the threshold in an `rlib` (`is_reachable_non_generic == true`), **but fails the `SymbolExportLevel::C` threshold in a `bin` crate** (`is_reachable_non_generic == false`). Only `#[unsafe(no_mangle)] pub extern "C"` (`SymbolExportLevel::C`) clears `bin` exports.
3. **CGU internalization (`compiler/rustc_monomorphize/src/partitioning.rs` L177–182, L515–601):**
   Under `Lazy` (`!tcx.sess.link_dead_code()`), `internalize_symbols` rewrites single-CGU non-exported items to `Linkage::Internal` (`L597–598`). Under `Eager` (`-C link-dead-code=yes`), `partitioning.rs` L177 skips `internalize_symbols` completely, so all functions and statics retain `External` (`hidden` in IR when local, `T` / `R` in `llvm-nm`) linkage.

#### Empirical 4-way matrix and downstream `.rlib` execution (`rustc 1.98.0-nightly`)

Running `support/probe_mono_collector_used_and_merge.py` on the specimen containing `USED_COMP`, `USED_LINK`, `poly_const<T>`, `poly_size<T>`, `dead`, `pub_dead_small`, `#[inline(never)] pub_dead_exported`, `gen_dead<T>`, `#[unsafe(no_mangle)] pub extern "C" fn exported_fn`, and `main` produces (`support/probe_results.json` L9–276):

| Build Mode (`-O2 -C codegen-units=1`) | Mono Items | `dead` | `pub_dead_small` | `pub_dead_exported` | `gen_dead` | `main` | `USED_COMP` / `USED_LINK` | Symbol Linkage in Dump |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :--- |
| `bin`, `Lazy` (`-C link-dead-code=no`) | **17** | `false` | `false` | `false` | `false` | `true` | `true` / `true` | Only `main`, `exported_fn`, `lang_start::<()>` `[External]`; rest `[Internal]` |
| `bin`, `Eager` (`-C link-dead-code=yes`) | **20** | `true` | `true` | `true` | `false` | `true` | `true` / `true` | All **20** items `[External]` |
| `rlib`, `Lazy` (`-C link-dead-code=no`) | **10** | `false` | `false` (deferred!) | **`true`** (`#[inline(never)]`) | `false` | `false` | `true` / `true` | `exported_fn`, `pub_dead_exported`, `USED_COMP`, `USED_LINK` `[External]`; 6 `poly_*` `[Internal]` |
| `rlib`, `Eager` (`-C link-dead-code=yes`) | **13** | `true` | `true` | `true` | `false` | `true` | `true` / `true` | All **13** items `[External]` |

In the `rlib` `Lazy` build, `llvm-nm` confirms that only `poly_const::<u8>` survived `-O2` `MergeFunctions` (`poly_const::<u16>` and `poly_const::<u64>` were erased; see Finding 4), while in the `Eager` builds all three `poly_const` symbols exist with `T` (`hidden`) linkage/aliases (`probe_results.json` L53–62, L119–133, L178–186, L236–249).

When downstream `app.rs` links against `libmono_rlib_lazy.rlib` via `let f: fn() -> u32 = mono::pub_dead_small; let g: fn() -> u32 = mono::pub_dead_exported; println!("{}", f().wrapping_add(g()));`, `rustc` collects **9** mono-items locally (`probe_results.json` L258–275):
- `mono::pub_dead_small` **is monomorphized locally** in `app` (`MONO_ITEM fn mono::pub_dead_small @@ app.<hash>-cgu.0[Internal]`, `local_codegen_pub_dead_small: true`), fulfilling the upstream `cross_crate_inlinable` deferral contract;
- `mono::pub_dead_exported` **is omitted** from `app`'s local mono-items (`local_codegen_pub_dead_exported: false`), because upstream `libmono_rlib_lazy.rlib` already exported `_RNvCs45IG44JCuCO_4mono17pub_dead_exported` with external symbol `T` (`probe_results.json` L182);
- executing `app_bin` exits `0` and prints **`222`** (`99 + 123`).

### 3. `#[used(compiler)]`, `#[used(linker)]`, and bare `#[used]` lowering to LLVM IR and ELF sections

`Basis: source + execution`

Rust attribute parsing and LLVM IR/ELF lowering split static retention across three layers:

1. **HIR / Codegen Attribute Resolution (`compiler/rustc_codegen_ssa/src/codegen_attrs.rs` L170–186):**
   ```rust
   // compiler/rustc_codegen_ssa/src/codegen_attrs.rs L170-186 (14210df0e)
   AttributeKind::Used { used_by } => match used_by {
       UsedBy::Compiler => codegen_fn_attrs.flags |= CodegenFnAttrFlags::USED_COMPILER,
       UsedBy::Linker => codegen_fn_attrs.flags |= CodegenFnAttrFlags::USED_LINKER,
       UsedBy::Default => {
           let used_form = if tcx.sess.target.os == Os::Illumos {
               // illumos' `ld` doesn't support a section header that would represent `#[used(linker)]`
               // (issue #146169); downgrade as if `#[used(compiler)]` was requested.
               CodegenFnAttrFlags::USED_COMPILER
           } else {
               CodegenFnAttrFlags::USED_LINKER
           };
           codegen_fn_attrs.flags |= used_form;
       }
   },
   ```
   Consequently, bare `#[used]` defaults to `USED_LINKER` on Linux, macOS, Windows, Wasm, and all non-illumos targets. On `1.98.0-nightly` Linux ELF, compiling bare `#[used] static USED_DEFAULT: [u8; 1] = [9];` without feature gates directly emits `@llvm.used` and ELF section flags `AR` (`probe_results.json` L277–285).
2. **LLVM IR Global Emission (`compiler/rustc_codegen_llvm/src/{consts.rs, context.rs, base.rs}`):**
   When codegenning statics (`consts.rs` L511–538 at `14210df0e`; identical logic at L649–676 on `f7da9a423`), `USED_COMPILER` calls `self.add_compiler_used_global(g)` (`consts.rs` L531) and `USED_LINKER` calls `self.add_used_global(g)` (`consts.rs` L537), asserting mutual exclusion. At CGU module finalization (`base.rs` L150–160), non-empty lists invoke `cx.create_used_variable_impl(c"llvm.used", ...)` and `cx.create_used_variable_impl(c"llvm.compiler.used", ...)` (`context.rs` L701–708), emitting `appending global [N x ptr]` arrays assigned to section `"llvm.metadata"`.
   In live LLVM IR for `bin_lazy` (`probe_results.json` L42–45):
   ```llvm
   @_RNvCsN5BoJIsGHJ_4mono9USED_COMP = internal constant [1 x i8] c"\07", align 1
   @_RNvCsN5BoJIsGHJ_4mono9USED_LINK = internal constant [1 x i8] c"\08", align 1
   @llvm.used = appending global [1 x ptr] [ptr @_RNvCsN5BoJIsGHJ_4mono9USED_LINK], section "llvm.metadata"
   @llvm.compiler.used = appending global [1 x ptr] [ptr @_RNvCsN5BoJIsGHJ_4mono9USED_COMP], section "llvm.metadata"
   ```
   Notice that `@USED_COMP` and `@USED_LINK` remain `[Internal]` in `bin` `Lazy` (and `@USED_COMP`/`@USED_LINK` become `[External]` non-internal constant globals in `rlib` `Lazy`, L166–169), yet LLVM `GlobalDCE` preserves both inside `.o` because LLVM recognizes both `@llvm.compiler.used` and `@llvm.used` during IR optimization (`llvm_nm_obj_symbols` shows `r _RNv...USED_COMP` and `r _RNv...USED_LINK` in every `.o` file, L58–59, L183–184).
3. **LLVM Object Emission Across Object Formats (`TargetLoweringObjectFileImpl.cpp`, `AsmPrinter.cpp`):**
   - **ELF (`TargetLoweringObjectFileELF`):** `initialize` (`TargetLoweringObjectFileImpl.cpp` L312–316) calls `collectUsedGlobalVariables(M, Vec, /*CompilerUsed=*/false)` — intentionally omitting `@llvm.compiler.used` — and inserts each `GlobalObject` into `Used`. `SelectSectionForGlobal` / `selectELFSectionForGlobal` (`L955–964`, L989–990) passes `Retain = Used.count(GO)`, setting `EmitUniqueSection = true` and `Flags |= ELF::SHF_GNU_RETAIN` whenever the integrated assembler or binutils `>= 2.36` is available (or `SHF_SUNW_NODISCARD` on Solaris). Meanwhile, `AsmPrinter::emitSpecialLLVMGlobal` (`AsmPrinter.cpp` L3718–3727) ignores `"llvm.metadata"` sections (skipping `@llvm.compiler.used`).
   - **Mach-O (`AsmPrinter.cpp` L3718–3722, L3788–3796):** `emitSpecialLLVMGlobal` intercepts `GV->getName() == "llvm.used"` and calls `emitLLVMUsedList` emitting `MCSA_NoDeadStrip` (`.no_dead_strip`), while ignoring `@llvm.compiler.used` (`llvm.metadata`).
   - **COFF (`TargetLoweringObjectFileCOFF::emitModuleMetadata`, `TargetLoweringObjectFileImpl.cpp` L2041–2066):** iterates **only** `"llvm.used"`, skipping `GV->hasLocalLinkage()` (because local symbols cannot be referenced across objects via `/INCLUDE:`, L2049–2053), and emits `/INCLUDE:<mangled_sym>` directives into `.drectve`.
   - **Wasm (`TargetLoweringObjectFileWasm::initialize`, `TargetLoweringObjectFileImpl.cpp` L2330–2334, L2427–2430):** calls `collectUsedGlobalVariables(M, Vec, false)` and propagates `Retain` to Wasm custom/data section attributes.

#### Live ELF section flags and GNU `ld --gc-sections` divergence (`probe_results.json` L63–68, L286–299)

On `x86_64-unknown-linux-gnu`, `readelf -WS` on the emitted object files records exact single-letter ELF section flag contrast:

```text
[19] .rodata._RNvCsN5BoJIsGHJ_4mono9USED_COMP PROGBITS 0000000000000000 000177 000001 00   A  0   0  1
[20] .rodata._RNvCsN5BoJIsGHJ_4mono9USED_LINK PROGBITS 0000000000000000 000178 000001 00  AR  0   0  1
Key to Flags: R (retain), ...
```

Linking `mono.rs` (`bin`, `Lazy`) with GNU `ld 2.47` demonstrates the concrete linker GC split:
- With `-C link-arg=-Wl,--gc-sections`: `llvm-nm` on `bin_gc` retains **`_RNv...USED_LINK` only** (`used_link_survives_gc: true`) and discards **`_RNv...USED_COMP`** (`used_comp_survives_gc: false`) and `exported_fn`.
- With `-C link-arg=-Wl,--no-gc-sections`: `llvm-nm` on `bin_nogc` retains **`USED_COMP`, `USED_LINK`, and `exported_fn`** (`used_comp_survives_no_gc: true`, `used_link_survives_no_gc: true`).

### 4. Removal of `-Z polymorphize` and replacement by LLVM `-O2` `MergeFunctions`

`Basis: source + execution`

#### Removal of `-Z polymorphize`

`rust-lang/rust#133883` (`711c8cc690c70d9b4c0e17e90f21f03d4e9d3ebf`, `2024-12-06`, merged `2024-12-07` at `ca13e9169fbbbb126190631b5a1e3e20053a52c1`, referencing `rust-lang/compiler-team#810`) removed MIR/codegen-level polymorphization cleanly from the compiler (`-2643 / +59` diff, deleting `compiler/rustc_monomorphize/src/polymorphize.rs`). On `rustc 1.98.0-nightly`, invoking `rustc ... -Zpolymorphize=on` fails (`exit 1`, `probe_results.json` L301–304):

```text
error: unknown unstable option: `polymorphize`
```

No MIR-level unused-generic-parameter deduplication remains; duplicate elimination across distinct instantiations such as `poly_const::<u8>`, `poly_const::<u16>`, and `poly_const::<u64>` now happens exclusively inside LLVM via `MergeFunctionsPass`.

#### Wiring from `rustc` target spec & `OptLevel` into LLVM `MergeFunctionsPass`

1. **Target default (`compiler/rustc_target/src/spec/mod.rs` L2910):** `TargetOptions::default()` initializes `merge_functions: MergeFunctions::Aliases` (some specialized targets opt out or select trampolines).
2. **`OptLevel` gating (`compiler/rustc_codegen_ssa/src/back/write.rs` L244–258 & `rustc_codegen_llvm/src/back/write.rs` L578–590):** Unless overridden by `-Z merge-functions=<disabled|trampolines|aliases>`, `ModuleConfig.merge_functions` is `true` for `-C opt-level` in `{2, 3, s, z}` (`More`, `Aggressive`, `Size`, `SizeMin`) and **`false` for `-O0` and `-O1`** (`No`, `Less`). Note also `rustc_codegen_llvm/src/back/write.rs` L578–590 disables `merge_functions` during pre-differentiation AutoDiff optimization (`merge_functions = false;`). `PassWrapper.cpp` L620 sets `PTO.MergeFunctions = MergeFunctions`, and `compiler/rustc_codegen_llvm/src/llvm_util.rs` L101–106 appends `-mergefunc-use-aliases` to LLVM's backend args whenever `MergeFunctions::Aliases` is active.
3. **LLVM pass ordering & structural comparison (`llvm/lib/Transforms/IPO/MergeFunctions.cpp`, `PassBuilderPipelines.cpp` L1615–1621):** LLVM inserts `MergeFunctionsPass` immediately after `GlobalDCEPass` and `ConstantMergePass`. At module entry (`MergeFunctions.cpp` L313–317), LLVM collects **both** `@llvm.used` (`CompilerUsed=false`) and `@llvm.compiler.used` (`CompilerUsed=true`) into `MF.getUsed()`, skipping replacement for any `G` in `Used` (`L1174`: `!Used.contains(G)` — preventing replacement of symbols referenced via inline assembly or metadata). Pairs `(F, G)` are compared by `FunctionComparator::compare()` (`L1212`).

#### Three-way lowering rule (`writeThunkOrAliasIfNeeded`, `MergeFunctions.cpp` L914–938, L1169–1205)

When `F` and `G` are structurally identical, not interposable, not preserving debuginfo (`!Opts.mergefunc_preserve_debug_info`), `G` is not in `Used`, and `G->hasGlobalUnnamedAddr()`:
- **Case A — `ShouldErase` (`L915–916, L923–926, L1174–1201`):** After `removeUsers(G); G->replaceAllUsesWith(F);`, if `G->isDiscardableIfUnused()` (e.g., `internal` linkage produced by `rustc` `Lazy` mode) and `G->use_empty()`, **`G->eraseFromParent()` deletes `G` completely** — leaving zero aliases and zero thunks.
- **Case B — `ShouldAlias` (`L839–887, L917, L928–931`):** When `G` has `External` linkage (e.g., `-C link-dead-code=yes` / `Eager` mode, so `!isDiscardableIfUnused()`), `-mergefunc-use-aliases` is enabled, `G->hasGlobalUnnamedAddr()`, and `canBeAliasee(F)` holds, LLVM calls `writeAlias(F, G)`: calls remain redirected to `F`, alignment becomes `max(align(F), align(G))`, and `G` is replaced by a **`GlobalAlias`** preserving `G`'s exported symbol name and linkage.
- **Case C — `ShouldThunk` (`L716–727, L918, L932–935`):** Under `-Z merge-functions=trampolines` with non-discardable `External` `G`, `canCreateAliasFor` is false, so `writeThunk` replaces `G`'s body with a tail call to `F`.

#### Live `rustc 1.98.0-nightly` 5-mode matrix (`support/probe_results.json` L305–498)

Testing `poly.rs` (`poly_const::<u8|u16|u64>` identical bodies `x.wrapping_mul(3).wrapping_add(1)` vs. size-dependent `poly_size::<u8|u16|u64>` `(x as usize).wrapping_add(core::mem::size_of::<T>())`, called from `drive(x)`):

| Compilation Mode | `poly_*` `define`s | `poly_*` `alias`es | Call Targets Inside `drive` | LLVM Mechanism Triggered |
| :--- | :---: | :---: | :--- | :--- |
| `-O2`, `Lazy` (default `Aliases`) | **4** | **0** | 3× `poly_const::<u8>`, 3× distinct `poly_size::<u8,u16,u64>` | `ShouldErase`: internal `poly_const::<u16,u64>` RAUW'd to `::<u8>` & erased |
| `-O2`, `Lazy`, `-Z merge-functions=disabled` | **6** | **0** | All 6 distinct (`poly_const::<u8,u16,u64>` + `poly_size::<u8,u16,u64>`) | Pass disabled cleanly |
| `-O2`, `Eager` (`-C link-dead-code=yes`), default `Aliases` | **4** | **2** | 3× `poly_const::<u8>` (+ inlined `drive(11)` calls) | `ShouldAlias`: `hidden unnamed_addr alias i32 (i32), ptr @...poly_consth...` |
| `-O2`, `Eager`, `-Z merge-functions=trampolines` | **6** (4 bodies + 2 thunks) | **0** | Direct calls redirected to `::<u8>`; `<u16>`/`<u64>` become 1-call tail thunks | `ShouldThunk`: `tail call noundef i32 @_RIN...poly_consth...(i32 noundef %0)` |
| `-O1`, `Lazy` (default) | **6** | **0** | All 6 distinct | `ssa_write.rs` L255 sets `merge_functions: false` below `-O2` |

**Why `poly_size::<u8|u16|u64>` never fold:** In every `-O2` mode (`probe_results.json` L315–317), `rustc` embeds distinct return-value range attributes and `size_of::<T>()` literals directly in IR (`range(i64 1, 4294967297)`, `range(i64 2, 4294967298)`, `range(i64 8, 4294967304)` and `+1`/`+2`/`+8`), causing `FunctionComparator` to keep all three distinct. Binary execution verifies observational equivalence: both default `-O2` (`MergeFunctions` active) and `-O2 -Z merge-functions=disabled` print **`146`** for `drive(11)` (`outputs_identical: true`, `3*(11*3+1) + (11+1) + (11+2) + (11+8) = 102 + 12 + 13 + 19 = 146`).

### 5. Executable Lean `v4.34.1` mechanization

`Basis: execution (Lean kernel) + derived`

The standalone module `support/MonoCollectorReachabilityUsedAndMergeFunctionsSoundness.lean` (`1,850` lines, `76,315` bytes) imports **zero** external libraries beyond Lean `Init` and models all three compiler subsystems in seven sections using constructive structural recursion and pure `noncomputable def` functions (yielding `0` `._unsafe_rec` helpers).

#### Collector, reachability closure, and `#[used]` linker GC theorems

| Theorem Name (`MonoCollectorUsedMerge.*`) | Formal Statement Summary | Compiler / Linker Guarantee |
| :--- | :--- | :--- |
| `eager_never_roots_generic`, `lazy_never_roots_generic` | Generic `ItemDecl` (`hasTypeOrConstParams = true`) satisfies `isRootDecl ... d = false` | Even `Eager` never synthesizes roots for `gen_dead<T>` |
| `static_always_root` | Any `staticVar` decl has `isRootDecl ... = true` across `(ck, opt, strat)` | Statics unconditionally seed `MonoCollector` |
| `lazy_root_implies_eager_root`, `lazy_reachability_subset_eager` | `isRoot ck opt .lazy d = true → isRoot ck opt .eager d = true` (outside `#[inline(always)]`) and `MonoReachable ... .lazy m → MonoReachable ... .eager m` | Collector monotonicity `Lazy ⊆ Eager` |
| `rlib_lazy_defers_small_pub_inline`, `rlib_lazy_collects_inline_never_pub`, `bin_lazy_omits_rust_abi_pub` | Exact root/non-root predicates over `(isExportedC, isPublicRust, inlineAttr, costEligible)` | Formalizes `pub_dead_small` deferral vs. `#[inline(never)] pub_dead_exported` in `rlib`, and omission in `bin` |
| `collectRootList_sound`, `collectRootList_complete`, `collectFuel_sound` | `List` collector matches inductive `isRoot` and finite-hop `MonoReachable` closure | Algorithmic collection corresponds to graph closure |
| `execCallChain_no_missing_if_closed`, `lazy_collection_link_complete` | Under a closed call graph (`GraphClosedOn` + `emittedClosed`), executing any chain from a collected root never returns `.missingSymbol` (`≠ .missingSymbol bad`) | **`Lazy` collection omits zero runtime-reachable transitive callees** |
| `rlib_deferral_downstream_link_complete` | Combining upstream `rlib` `Lazy` items (`pub_dead_exported` emitted) with downstream `app` items (`pub_dead_small` deferred & collected downstream) avoids `.missingSymbol` at final link | Explains why downstream `.rlib` links cleanly (`222`) |
| `bare_used_is_linker_retain_except_illumos`, `used_linker_survives_llvm_and_linker_gc`, `used_compiler_survives_llvm_but_stripped_by_gc`, `unannotated_dead_internal_static_dropped_by_global_dce` | Encodes `TargetOS`, `UsedKind`, ELF `shfGnuRetain`, `llvm.compiler.used` vs. `llvm.used`, and `--gc-sections` reachability | Separates `GlobalDCE` preservation from ELF `AR` linker GC survival |

#### `MergeFunctions` observational equivalence and sharpness counterexamples

For an abstract first-order IR evaluator `evalIrExpr (M : IrModule) (fuel argVal : Nat) (e : IrExpr) : Option Nat` structurally recursive on `fuel`:
- **`IrExpr.eq_true_iff`:** Decidable structural equality `IrExpr.eq bF bG = true` implies propositional identity `bF = bG` (`L1063–1127`).
- **`eval_rewrite_erase_sound` (`L1441`):** Rewriting calls `G.sym ↦ F.sym` and erasing `G` (`ShouldErase`) preserves `evalIrExpr` at equal fuel whenever `F.kind = .defined b`, `G.kind = .defined b`, and `F.sym ≠ G.sym`.
- **`eval_external_alias_or_thunk_entry_sound` (`L1492`):** When `G` is retained as `.aliasTo F.sym` (`ShouldAlias`) or `.thunkTo F.sym` (`ShouldThunk`), invoking `evalIrExpr M' (f + 2) argVal (.call G.sym .arg)` equals `evalIrExpr M (f + 1) argVal (.call G.sym .arg)`, offsetting the single alias/thunk hop by `+1` fuel.
- **`applyMergeTwo_preserves_observational_equivalence` (`L1548`):** Unifies `.eraseAndRewrite`, `.emitAlias`, and `.emitThunk` cleanly (yielding exact equal-fuel agreement for `eraseAndRewrite` and `+1`-fuel agreement when calling through external `alias`/`thunk` shims).
- **`used_list_blocks_merge_functions` (`L1839`):** Proves `F.inUsedList = true ∨ G.inUsedList = true → decideMergeAction opt mode F G = .keepDistinct`.
- **Specimen concretes & sharpness CE1–CE3 (`L1671–1834`):** Kernel `rfl` proves exact root counts matching Section 2 (`17` vs. `20`, `10` vs. `13`), Section 4 `MergeFunctions` outcomes (`4` vs. `6` `define`s, `4+2` aliases, `4+2` thunks, `o1` `6` `define`s), `drive(11) == 146` parity across all modes, plus:
  - **CE1 (`ce1_incomplete_collector_missing_symbol`):** Dropping `exported_fn` from `emitted` yields `.missingSymbol (.fnInst idExported 0)` when stepping `main -> exported_fn`.
  - **CE2 (`ce2_used_compiler_vs_linker_gc_divergence`):** `survivesLinkerGC true false sComp ≠ survivesLinkerGC true false sLink` under `--gc-sections` on ELF.
  - **CE3 (`ce3_poly_size_not_structurally_equal_and_unsound_merge`):** `IrExpr.eq (bodyPolySize 1) (bodyPolySize 8) = false`, and forcibly rewriting `poly_size::<u64>` into `poly_size::<u8>` corrupts `evalIrCall forcedM 10 symDrive 11` from `some 146` to **`some 139`** (`12 + 13 + 12` instead of `12 + 13 + 19`).

#### Verification & MetaM kernel audit

Verified against `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`, `6.225 s` wall clock) with `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`exit 0`, zero warnings), followed by an exhaustive `Environment` MetaM inspection (`5.729 s` wall clock, `trustLevel := 0`, `env.setExporting false`):
- Module counts in `MonoCollectorUsedMerge.*`: `243` kernel `thmInfo` constants (`67` top-level `theorem` declarations), `502` `defnInfo` constants (`69` `noncomputable def` declarations), `23` `inductInfo` constants (`22` top-level `inductive`/`structure` declarations).
- Purity invariants: **`ns_unsafe_rec=0`** (note Lean `Init` itself defines `521` prelude `_unsafe_rec` constants outside the module namespace), **`ns_unsafe_or_partial_defs=0`**, **`axioms=[propext]`**, **`disallowed_axioms=[]`** (`0` `Classical.choice`, `0` `sorryAx`, `0` `Lean.ofReduceBool`, `0` `Lean.trustCompiler`), and `0` source occurrences of `omega`, `bv_decide`, `native_decide`, `partial def`, `sorry`, `noncomputable section`, `deriving`, `axiom`, or `opaque`.

### 6. Anneal trusted MIR ingestion seam and whole-crate capture completeness

`Basis: source`

Inspecting `trusted/lean/Trusted/MirAst.lean` in `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` connects Findings 1–5 directly to verified-Rust capture design:

1. **Whole-crate completeness is an external producer obligation (`MirAst.lean` L869–882, L933–936):** `VerificationScope.crate` distinguishes whole-crate proofs (`Trusted.MirSemantics.CrateTheorem`) from proof-unit claims (`.unit`), explicitly stating: *"when `scope = .crate`, completeness of `bodies` (ensuring every executable body and reachable callee in the crate is included) is an external producer obligation, not checked by `Trusted.MirSemantics` alone."* As Finding 2 demonstrates, compiling an `rlib` under default `Lazy` collection (`-C link-dead-code=no`) **omits** unreferenced functions AND defers `cross_crate_inlinable` public functions such as `pub_dead_small` out of local mono-items; therefore an Anneal crate-capture emitter driving whole-crate theorems must either pull bodies from post-monomorphization / downstream-linked closure or avoid assuming an `rlib`'s local `MonoItem` set contains every public crate function.
2. **Call and global boundary (`MirAst.lean` L780–796):** `TerminatorKind.call` accepts direct `FnDef` calls by `DefId`, while `Drop`, indirect `Call`, `TailCall`, `InlineAsm`, `Yield`, and `CoroutineDrop` map fail-closed to `.unsupported`. Static initializers, ELF section retention (`#[used]`), and post-MIR LLVM `MergeFunctions` rewrites lie strictly downstream of `Trusted.MirAst`.
3. **Zero-`._unsafe_rec` `noncomputable` discipline (`MirAst.lean` L75–92):** Anneal's trusted boundary rejects any compiler-synthesized `partial` `._unsafe_rec` constant via `TrustedBoundary.validateRepoConstant` and forbids `noncomputable section` via `TrustedBoundary.inspectNodeKind`, requiring every term `def` to carry explicit `noncomputable`. Our Lean formalization confirms that explicit `noncomputable def` + pure `Prop`/`Nat`/`Bool` structural recursion eliminates every module-namespace `._unsafe_rec` constant (`0 / 502` definitions) with kernel checking remaining fast (`6.225 s` across `1,850` lines).

### 7. Analytical scorecard

`Basis: execution + derived`

| Dimension | Basis | Observed Result |
| :--- | :--- | :--- |
| Compiler & Linker Probe Coverage | execution | All empirical suites pass cleanly inside `support/probe_mono_collector_used_and_merge.py`: CLI `-Z print-mono-items=lazy` rejection (`exit 1`), `(bin\|rlib) × (Lazy\|Eager)` mono-item counts (`17`/`20`, `10`/`13`), downstream `.rlib` link (`9` items, stdout `222`), bare `#[used]` (`AR`), GNU `ld --gc-sections` vs. `--no-gc-sections` (`USED_LINK` survives, `USED_COMP` stripped), `-Z polymorphize=on` rejection (`exit 1`), `5`-mode `MergeFunctions` IR counts (`4`, `6`, `4+2` aliases, `4+2` thunks, `6`), and native `drive(11) == 146` parity. |
| Lean Artifact Footprint & Latency | execution | `support/MonoCollectorReachabilityUsedAndMergeFunctionsSoundness.lean` (`1,850` LOC, `76,315` bytes, `67` top-level theorems); strict single-file `lean` kernel check `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` completes in **`6.225 s`**; MetaM `Environment` audit (`import Lean`) completes in **`5.729 s`**. |
| Kernel Auditability & Purity | execution (MetaM) | `0` imports beyond `Init`; `243` kernel `thmInfo`, `502` `defnInfo`, `23` `inductInfo` constants; **`0` `._unsafe_rec`**, **`0` unsafe/partial defs**, **`axioms = [propext]`**, **`disallowed_axioms = []`** (`0` `Classical.choice`, `sorryAx`, `ofReduceBool`, `trustCompiler`). |
| Soundness & Sharpness Discrimination | execution + derived | Universal soundness (`Lazy ⊆ Eager`, generic exclusion, transitive reachability link completeness, ELF `SHF_GNU_RETAIN` survival, unified `MergeFunctions` observational equivalence, `UsedList` protection) paired with exact specimen checks and counterexamples **CE1–CE3**. |
| Ecosystem & Hardware Breadth | none | Multi-crate sysroot/crates.io benchmarks, ThinLTO/FatLTO cross-CGU merging, and native non-ELF linker executions (`ld64`, `lld-link`, `wasm-ld`) were not run (recorded under **Boundaries**). |

## Boundaries

Per `FORMAT.md`, negative space is partitioned strictly by epistemic status:

### Not examined

- **Native linker GC execution on Mach-O, COFF, and Wasm:** `TargetLoweringObjectFileImpl.cpp` and `AsmPrinter.cpp` source logic for Mach-O (`MCSA_NoDeadStrip`), COFF (`/INCLUDE:` skipping `hasLocalLinkage()`), Wasm (`Retain`), and Solaris (`SHF_SUNW_NODISCARD`) was read in LLVM source, **not** executed against Apple `ld64`, `lld-link`/`link.exe`, or `wasm-ld`, nor on an `Os::Illumos` target.
- **Cross-CGU FatLTO / ThinLTO `MergeFunctions` and `-C codegen-units > 1` CGU internalization splits:** All compiler probes passed `-C codegen-units=1`. How multi-CGU `UsageMap` boundaries inhibit `internalize_symbols` (`partitioning.rs` L565–583) or how LTO `ThinLTOPhase` interacts with `MergeFunctions` (`PassBuilderPipelines.cpp` L1620–1632) was not executed.
- **Debuginfo preservation, EH personality mismatches, and symbol visibility interactions in `MergeFunctions`:** `MergeFunctions.cpp` L1166–1176 checks `!G->isInterposable()`, `!Opts.mergefunc_preserve_debug_info`, `!hasNonLocalAlias(G) || canBeAliasee(F)`, and `FunctionComparator` checks calling conventions, personality functions, GC strategy, and operand attributes; only `size_of::<T>()` constant + `range(...)` attribute divergence and `-Z merge-functions={aliases, trampolines, disabled}` were tested empirically.
- **`-Z cross-crate-inline-threshold`, `-Z hint-mostly-unused`, and `-Z share-generics=no` interaction on `rlib` deferral:** Only default thresholds at `-O2` were measured (`cross_crate_inline.rs` L57–95).
- **Direct Rust-to-Lean extractor bridge:** Whether a concrete extractor (`anneal-rustc-capture` or future MIR exporter) emits `.crate` captures consistent with `Lazy` `rlib` vs. `bin` collections was not tested because no `MonoItem` capture binary was run.

### Unknown

- **Unannounced post-`f7da9a423` / external target-linker bugs (such as pre-2.36 binutils `SHF_GNU_RETAIN` / `.init_array` interactions):** Source comments in `consts.rs` L658–661 and `TargetLoweringObjectFileImpl.cpp` L771–784 note historical GNU `gold` and binutils `< 2.36` bugs when omitting or emitting `SHF_GNU_RETAIN` and `,unique,`; behavior of specific older system binutils deployments outside `GNU ld 2.47` was not probed.

### Known not to apply

- **Incremental compilation enabling `Eager` collection:** Despite the stale doc comment in `collector.rs` L149–154, source inspection (`partitioning.rs` L1132–1136) establishes that incremental builds keep `Lazy` unless `-C link-dead-code=yes` is explicitly set.
- **`-C link-dead-code=yes` instantiating unreferenced generics (`gen_dead<T>`):** `is_root` (`collector.rs` L1654) rejects any item with `!requires_monomorphization == false`, and live `Eager` runs omit `gen_dead<T>`.
- **`-Z print-mono-items=lazy` / `-Z polymorphize=on` flags on modern nightly `rustc`:** Both CLI options fail fast (`exit 1`) on `rustc 1.98.0-nightly`.
- **`#[used(compiler)]` surviving `--gc-sections` on ELF:** Because `TargetLoweringObjectFileELF` initializes `Used` solely from `@llvm.used` (`CompilerUsed=false`, `TargetLoweringObjectFileImpl.cpp` L313), `@llvm.compiler.used` sections omit `SHF_GNU_RETAIN` (`A`, not `AR`) and are reclaimed by `--gc-sections` when unreferenced.
- **Bare `#[used]` equaling `#[used(compiler)]` on Linux/ELF:** On `14210df0e` and `f7da9a423`, `UsedBy::Default` emits `USED_LINKER` (`@llvm.used`, ELF `AR`) everywhere except `Os::Illumos` (`codegen_attrs.rs` L173–185).
- **Weak memory, concurrency, or hardware fault modeling:** Monomorphization collection, section-flag assignment, and `MergeFunctions` are sequential/deterministic compile- and link-time static program transformations; non-deterministic memory models do not apply.

### Unsupported

- **`UsedBy::Linker` semantics on `Os::Illumos`:** `codegen_attrs.rs` L174–180 explicitly downgrades bare `#[used]` to `USED_COMPILER` due to illumos `ld` section header constraints (`rust-lang/rust#146169`).
- **Anneal `Trusted.MirAst` coverage for statics, ELF section flags, and LLVM IPO passes:** `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`Trusted/MirAst.lean`) models MIR function bodies with direct `FnDef` calls (`L780–795`), leaving static `#[used]` attributes and LLVM `MergeFunctions` outside its AST.

## Evidence

All observations in this report were acquired or directly verified on `2026-11-24`. Note `711c8cc690c70d9b4c0e17e90f21f03d4e9d3ebf` was merged on `2024-12-07`, `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` was committed `2026-05-31`, `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) was tagged `2026-09-24`, and `f7da9a42368f31abb02b8064bb93a11bf9ba9f5e` was committed `2026-11-23`.

### Upstream primary source locations

| Subject Repository & Revision | Path | Exact Symbol / Line Citation | Established Claim |
| :--- | :--- | :--- | :--- |
| `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_monomorphize/src/partitioning.rs` | `collect_and_partition_mono_items` (L1131–1138); CGU `internalize_symbols` call (`!tcx.sess.link_dead_code()`, L177–182); `internalize_symbols` (L515–601) | `Eager` iff `link_dead_code()`; `internalize_symbols` disabled under `Eager` |
| `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_monomorphize/src/collector.rs` | Doc comment (L149–154); `collect_items_rec` static handling (L422–460); `collect_roots` (L1457–1494); `RootCollector::{process_item, process_impl_item, process_nested_body, is_root, push_extra_entry_roots}` (L1503–1729); `collect_crate_mono_items` (L1807–1839) | `Static`/`GlobalAsm` unconditional roots; `!requires_monomorphization` blocking generics; `entry_fn` + `start_fn` roots; `Eager` defaults/ADTs/consts |
| `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_passes/src/reachable.rs` | `reachable_set` seeding (L480–485) | Public items enter `reachable_set` |
| `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_codegen_ssa/src/back/symbol_export.rs` | `crate_export_threshold` (L29–36); `reachable_non_generics_provider` (L49–97); `is_reachable_non_generic_provider_local` (L154–162) | `cross_crate_inlinable` dropped at L96; `bin` uses `SymbolExportLevel::C` vs. `rlib` `SymbolExportLevel::Rust` |
| `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_mir_transform/src/cross_crate_inline.rs` | `cross_crate_inlinable` (L18–104); `CostChecker` (L115–189) | `#[inline(never)]` (`L49`) blocks deferral; small pure leaves defer at `-O2` |
| `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_codegen_ssa/src/codegen_attrs.rs` | `AttributeKind::Used` matching (`UsedBy::{Compiler, Linker, Default}`, L170–186) | `UsedBy::Default` maps to `USED_LINKER` except `Os::Illumos` (`#146169`) |
| `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_codegen_llvm/src/{consts.rs, context.rs, base.rs}` | `consts.rs` L511–549 (`USED_COMPILER`/`USED_LINKER`, `add_used_global`, `add_compiler_used_global`); `context.rs` L701–708 (`create_used_variable_impl`); `base.rs` L150–160 | Lowers to `@llvm.compiler.used` and `@llvm.used` in `"llvm.metadata"` |
| `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_target/src/spec/mod.rs`, `compiler/rustc_codegen_ssa/src/back/write.rs`, `compiler/rustc_codegen_llvm/src/{back/write.rs, llvm_util.rs}`, `PassWrapper.cpp` | `spec/mod.rs` L2910; `ssa/write.rs` L244–258; `llvm/write.rs` L569–590; `llvm_util.rs` L101–106; `PassWrapper.cpp` L620 | Default `MergeFunctions::Aliases` enabled at `-O2`/`-O3`/`-Os`/`-Oz`, `-mergefunc-use-aliases`, AutoDiff bypass |
| `rust-lang/rust@711c8cc690c70d9b4c0e17e90f21f03d4e9d3ebf` | PR `#133883` (merge `ca13e9169fbbbb126190631b5a1e3e20053a52c1`) | `compiler/rustc_monomorphize/src/polymorphize.rs` deleted (`-2643 / +59`) | Upstream removal of `-Z polymorphize` (`compiler-team#810`) |
| `rust-lang/rust@f7da9a42368f31abb02b8064bb93a11bf9ba9f5e` | `collector.rs`, `partitioning.rs`, `reachable.rs`, `symbol_export.rs`, `cross_crate_inline.rs`, `codegen_attrs.rs`, `consts.rs` (`L649–688`), `ssa/write.rs`, `llvm_util.rs`, `spec/mod.rs` | Drift audit across May–Nov 2026 | Confirms semantics unchanged despite `rustc_attr_ir` / PAC / offload additions |
| `llvm/llvm-project@ba1d95e0af43ea608d82a16cc1a9694c6b072c02` | `llvm/lib/Transforms/IPO/MergeFunctions.cpp`, `PassBuilderPipelines.cpp` | `MergeFunctions.cpp` L314–317 (`Used`), L839–887 (`canCreateAliasFor`/`canBeAliasee`/`writeAlias`), L914–938 (`writeThunkOrAliasIfNeeded`), L1169–1205; `PassBuilderPipelines.cpp` L1615–1621 | `MergeFunctions` placement, `Used` exclusion, and `ShouldErase`/`ShouldAlias`/`ShouldThunk` |
| `llvm/llvm-project@ba1d95e0af43ea608d82a16cc1a9694c6b072c02` | `llvm/lib/CodeGen/TargetLoweringObjectFileImpl.cpp`, `AsmPrinter.cpp` | ELF (`L312–316`, `L768–775`, `L955–964`, `L989–990`); Mach-O (`AsmPrinter.cpp` `L3718–3727`, `L3788–3796`); COFF (`L2041–2066`); Wasm (`L2330–2334`, `L2427–2430`) | Target section-retention handling for `@llvm.used` (`SHF_GNU_RETAIN` / `.no_dead_strip` / `/INCLUDE:` / Wasm `Retain`) vs. ignored `@llvm.compiler.used` |
| `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/Trusted/MirAst.lean` | `Declaration Modifiers` (`noncomputable`, L75–92); `TerminatorKind` (`L780–796`); `VerificationScope` & `Program` (`L869–882`, `L915–936`) | Producer completeness contract for `.crate` scope & zero-`._unsafe_rec` policy |

### Package-preserved support material

- **`support/probe_mono_collector_used_and_merge.py`:** Self-contained reproducible Python harness (`with tempfile.TemporaryDirectory():`) driving `rustc 1.98.0-nightly`, `llvm-nm`, `readelf`, and GNU `ld` across all collector, downstream `.rlib`, `#[used]`, `--gc-sections`, `-Z polymorphize`, `MergeFunctions`, and executable parity checks with sanitized `<TMP>` paths.
- **`support/probe_results.json`:** Complete JSON capture (`rustc --version --verbose`, `GNU ld 2.47`, verbatim `MONO_ITEM` lists, LLVM IR highlights, `llvm-nm` symbol tables, `readelf -WS` section headers, `-Z merge-functions` IR call sites and aliases, and executable stdout outputs `222` and `146`).
- **`support/MonoCollectorReachabilityUsedAndMergeFunctionsSoundness.lean`:** Pure `1,850`-line Lean `v4.34.1` development (`67` top-level `theorem`, `69` `noncomputable def`, `22` `inductive`/`structure`; verified with `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` in `6.225 s`; MetaM audit confirming `0` `._unsafe_rec` in namespace, `0` unsafe/partial defs, `axioms=[propext]`, `disallowed_axioms=[]`).

## Revalidation

Every claim in this report can be revalidated directly from the package directory without mutating external workspaces:

1. **Re-run the live `rustc` + ELF + `MergeFunctions` empirical probe suite** (writes fresh JSON to a temporary path for comparison against `support/probe_results.json`):
   ```bash
   python3 support/probe_mono_collector_used_and_merge.py --output /tmp/mono_probe_check.json
   ```
2. **Fast single-command compiler regressions** (all run inside a temporary directory):
   - Verify `-Z print-mono-items=lazy` and `-Z polymorphize=on` remain rejected, or inspect `-Z print-mono-items=yes` counts under `-C link-dead-code=no|yes` on `--crate-type={bin,rlib}`.
   - Verify `readelf -WS` section flag `A` on `#[used(compiler)]` vs. `AR` (`SHF_GNU_RETAIN`) on `#[used(linker)]` / bare `#[used]` (`x86_64-unknown-linux-gnu`), and link with `-C link-arg=-Wl,--gc-sections` to confirm only `USED_LINK` survives in `llvm-nm`.
   - Emit `--emit=llvm-ir` at `-O2` with default flags vs. `-Z merge-functions=disabled`, `-C link-dead-code=yes` (`aliases`), and `-C link-dead-code=yes -Z merge-functions=trampolines` to reconfirm `4` vs. `6` `define`s and `2` `hidden unnamed_addr alias` entries.
3. **Kernel-verify the Lean `v4.34.1` formalization and confirm zero `._unsafe_rec` / disallowed axioms:**
   ```bash
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/MonoCollectorReachabilityUsedAndMergeFunctionsSoundness.lean
   ```
   To re-run the MetaM environment audit, compile `support/MonoCollectorReachabilityUsedAndMergeFunctionsSoundness.lean` to an `.olean` (`-R support -o /tmp/audit_lib/MonoCollectorReachabilityUsedAndMergeFunctionsSoundness.olean`), import it via `Lean.importModules` (`trustLevel := 0`, `env.setExporting false`), and assert `0` constants with `_unsafe_rec` under `MonoCollectorUsedMerge.*`, `0` unsafe/partial definitions, and `Core.CoreM.toIO (Lean.collectAxioms name)` returning only `propext` (or `Quot.sound`) across all declarations.
4. **Check upstream Rust / LLVM source drift before re-anchoring to newer revisions:**
   Inspect diffs in `collector.rs` (`is_root`, `DefKind::Static`), `partitioning.rs` (`collect_and_partition_mono_items`, `internalize_symbols`), `symbol_export.rs` (`reachable_non_generics_provider`), `cross_crate_inline.rs`, `codegen_attrs.rs` (`UsedBy`), `consts.rs` (`add_used_global`/`add_compiler_used_global`), `ssa/back/write.rs` (`merge_functions`), `MergeFunctions.cpp` (`writeThunkOrAliasIfNeeded`, `Used.contains`), and `TargetLoweringObjectFileImpl.cpp` (`collectUsedGlobalVariables`, `SHF_GNU_RETAIN`).
5. **Run corpus structural validation from the repository root:**
   ```bash
   python3 tools/reference.py catalog && python3 tools/reference.py check
   ```
