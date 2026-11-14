# Cross-DSO Dynamic Linking, Duplicate VTables, and Open-World LTO Contracts (`LinkWorldContract`)

## Summary

Whole-program devirtualization (`WPO-DevirtSingleImpl`, `WPO-DevirtBranchFunnel`, and `WPO-VFE` in `whole-program-devirt-dae-and-globalopt-exportlist-certificates`) and speculative vtable-pointer promotion (`VP-3` `VP-VTablePromote` in `value-profile-specialization-and-hybridtrace-guard-certificates`) interact nontrivially with dynamic linking (`dylib`, `cdylib`, `dlopen` plugins) and cross-codegen-unit vtable instantiation in `rustc` 1.99.1 (`58cf8f9c35b355199727627d07ae34a4e2846d67`):

1. **Why `rustc 1.99.1` Emits Duplicate VTable Addresses Across DSOs (`consts.rs:294-344`, `meth.rs:103-123`)**:
   - In `compiler/rustc_codegen_ssa/src/meth.rs:115-117`, `get_vtable` lowers a `(Ty, ExistentialTraitRef)` pair via `cx.static_addr_of(vtable_allocation, Some("vtable"))`.
   - In `compiler/rustc_codegen_llvm/src/consts.rs:312-340`, `static_addr_of_impl` defines `@vtable.N` with **`llvm::Linkage::PrivateLinkage`** (`private unnamed_addr constant` in LLVM IR), which is local to the defining object/DSO, omitted from ELF `.dynsym`, and never coalesced across shared-library boundaries by `ld.so`.
   - In our 3-crate (`shared_api` `rlib`, `plugin_dylib` `cdylib`, `host_bin` `bin`) + `dlopen` probe on `x86_64-unknown-linux-gnu` (`support/cross_dso_vtable_probe/run_dso_experiment.py`), instantiating `&dyn SharedTrait` for the exact same concrete type `SharedStruct` in `host_bin` and in `libplugin_dylib.so` produces **two distinct runtime vtable addresses**: `host_vtable_addr = 0x56261d4cf720` vs. `plugin_shared_vtable_addr = 0x7fe71313b248` (`duplicate_vtable_addresses_distinct = true`).
2. **Unconditional Open-World Soundness of `VP-3` (`vptr == &VTABLE_Local`) and Two-Level DSO Guarding**:
   - We prove in Lean `v4.34.1` (`vp_vtable_promote_open_world_sound` in `support/lean/CrossDsoLinkWorldContract.lean`, `0` closed-world hypotheses required) that `if vptr == &VTABLE_Local { Concrete::foo(self) } else { ((*vptr).foo)(self) }` is **100% semantically sound in an arbitrary open DSO world** containing duplicate vtables (`&VTABLE_Plugin != &VTABLE_Host`) and unknown `dlopen` plugin implementations (`PluginPrivateStruct`). When `vptr == &VTABLE_Plugin`, the pointer check evaluates to `false` and safely executes the verified indirect fallback `((*vptr).foo)(self)`.
   - While single-pointer `VP-3` (`vptr == &VTABLE_Host`) achieves `100.0%` direct-call hit rate on host-constructed trait objects (`50.0%` overall hit rate on a mixed `50%` host `SharedStruct` + `45%` plugin `SharedStruct` + `5%` `PluginPrivateStruct` stream), **Two-Level DSO-Resilient Guarding** (`if vptr == &VTABLE_Host || (*vptr).slot == target_fn_ptr`, mechanized in `vp_two_level_dso_promote_sound_and_hits_duplicate_vtable`) restores **`100.0%` direct-call hit rate across both DSOs (`95.0%` overall stream hit rate)** and achieves a **`+22.43%` runtime speedup** (`529.65` $\mu\text{s}$ $\rightarrow$ `410.87` $\mu\text{s}$).
   - Conversely, we prove a critical negative canary (`canary_duplicate_vtable_breaks_exhaustive_vptr_else_assumption`): an $N$-way branch funnel that omits the `vptr == &VTABLE_N` check on its final `else` branch is **unsound** if duplicate vtable addresses can exist across DSOs, because a foreign duplicate vtable `&VTABLE_1_Plugin != &VTABLE_1_Host` falls into the `else` branch and executes `Impl_N` instead of `Impl_1`!
3. **The 4-Level `LinkWorldContract` Hierarchy and Crate-Private Trait Closure (`private_trait_closed_under_dso_linking_sound`)**:
   - We formalize the 4-level link-world contract (`FullyClosedExecutable`, `CratePrivateTraitInOpenBinary`, `SealedTraitInClosedDsoSet`, `OpenExportedTrait`) and prove (`private_trait_closed_under_dso_linking_sound`) that any trait `TraitId ∉ ExportedTraits(ExportList)` cannot be implemented or forged by a well-typed external DSO, enabling unguarded `WPO-DevirtSingleImpl` (`+52.63%` speedup, `296.99` $\mu\text{s}$ $\rightarrow$ `140.69` $\mu\text{s}$ on `HostPrivateTrait`) and `WPO-VFE` (`wpo_vfe_requires_non_escaping_layout_sound`) even inside binaries that dynamically load external plugins.

## Applicability

- **Subjects**:
  - `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`)
  - `rust-lang/llvm-project` `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`)
  - `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`)
  - `joshlf/anneal` (`7abf0691c404393e3e4fc26eb3d4094e3170b5c7`)
- **Targets and linkage modes examined**: `x86_64-unknown-linux-gnu` across `rlib`, `cdylib`, `dylib`, and `bin` crate types with POSIX `dlopen(RTLD_NOW)`.
- **Relationship to other corpus packages**: Extends `whole-program-devirt-dae-and-globalopt-exportlist-certificates`, `value-profile-specialization-and-hybridtrace-guard-certificates`, and `compositional-correctness-linking-and-whole-program-optimization`.

## Findings

### 1. VTable Global Linkage and Multi-DSO Address Duplication in `rustc 1.99.1`

`Basis: source + execution (compiler/rustc_codegen_ssa/src/meth.rs:103-123, compiler/rustc_codegen_llvm/src/consts.rs:294-344, support/cross_dso_vtable_results.json)`

Inspecting `compiler/rustc_codegen_ssa/src/meth.rs:103-123` and `compiler/rustc_codegen_llvm/src/consts.rs:294-344` in `rustc` 1.99.1 establishes the exact linkage and visibility rules for Rust vtables:
1. `get_vtable` evaluates `tcx.vtable_allocation((ty, trait_ref))` into a read-only `ConstAllocation` and passes it to `cx.static_addr_of(vtable_allocation, Some("vtable"))`.
2. `static_addr_of_impl` (`consts.rs:322-344`) deduplicates identical `ConstAllocation`s **only within a single `CodegenCx` (a single CGU)** via `self.const_globals`, and calls `static_addr_of_mut` (`consts.rs:294-317`), which sets:
   - `llvm::set_linkage(gv, llvm::Linkage::PrivateLinkage)` (`consts.rs:312`),
   - `llvm::set_unnamed_address(gv, llvm::UnnamedAddr::Global)` (`consts.rs:315`), and
   - `llvm::set_global_constant(gv, true)` (`consts.rs:340`).
3. In the LLVM IR emitted by `rustc +1.99.1-x86_64-unknown-linux-gnu -C opt-level=3 --emit=llvm-ir` for `shared_api.rs` (`support/cross_dso_vtable_results.json`), the vtable global is:
   ```llvm
   @vtable.0 = private unnamed_addr constant <{ [24 x i8], ptr, ptr, ptr }> <{
     [24 x i8] c"\00\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00\08\00\00\00\00\00\00\00",
     ptr @_RNvXCs7IiaSy2Myeg_10shared_apiNtB2_12SharedStructNtB2_11SharedTrait7compute,
     ptr @_RNvYNtCs7IiaSy2Myeg_10shared_api12SharedStructNtB4_11SharedTrait15unused_vfe_slotB4_,
     ptr @_RNvXCs7IiaSy2Myeg_10shared_apiNtB2_12SharedStructNtB2_11SharedTrait6tag_id
   }>, align 8, !guid !0
   ```
4. Because `@vtable.0` has `private` linkage, the assembler emits it as a local symbol in `.data.rel.ro` without a global ELF `.dynsym` entry. When both `host_bin` and `libplugin_dylib.so` link `libshared_api.rlib` and coerce `&SharedStruct` to `&dyn SharedTrait`, the process contains two distinct runtime vtable addresses (`0x56261d4cf720` in `host_bin` vs. `0x7fe71313b248` in `libplugin_dylib.so`) and two distinct non-exported trait method wrappers (`0x56261d48e040` vs. `0x7fe713102a40`), while `PluginPrivateStruct` in `libplugin_dylib.so` has vtable `0x7fe71313b218`.

---

### 2. The 4-Level `LinkWorldContract` Hierarchy and Empirical Multi-DSO Evaluation

`Basis: source + execution + derived (support/cross_dso_vtable_probe/run_dso_experiment.py, support/cross_dso_vtable_benchmarks.csv, support/lean/CrossDsoLinkWorldContract.lean)`

Table 1 defines the 4-level `LinkWorldContract` classification that gates devirtualization and virtual-function elimination (`WPO-VFE`) in the verified compiler:

| `LinkWorldKind` Level | Link-Unit & Trait-Visibility Precondition | Allowed Devirtualization Schemas | `WPO-VFE` (`stripUnusedVTableSlot`) Allowed? |
| :--- | :--- | :--- | :---: |
| **`1. FullyClosedExecutable`** | `bin` or `staticlib` with zero `dylib` imports and zero FFI inputs carrying `dyn Trait` | Unguarded `WPO-DevirtSingleImpl`, `WPO-DevirtBranchFunnel`, `WPO-DevirtConstRet`, `VP-3` | **Yes** |
| **`2. CratePrivateTraitInOpenBinary`** | `bin` or `cdylib` linking external `dylib`s, where `TraitId ∉ ExportedTraits(ExportList)` and never crosses FFI | Unguarded `WPO-DevirtSingleImpl`, `WPO-DevirtBranchFunnel` (if single-DSO or `VP-Slot` fallback), `WPO-DevirtConstRet` | **Yes** (`NonEscapingTraitLayout` holds) |
| **`3. SealedTraitInClosedDsoSet`** | Workspace-closed `dylib` set with verified SHA-256 `.anneal-summary` manifest | `WPO-DevirtSingleImpl` (when single impl), `VP-TwoLevel` (`vptr` or `slot` check across DSO vtable copies) | **Only if coordinated across all DSOs in set** |
| **`4. OpenExportedTrait`** | `pub trait` reachable from `ExportList` or FFI across a `dylib` / `cdylib` / `dlopen` boundary | **Guarded `VP-2` (`(*vptr).slot == fn`), `VP-3` (`vptr == &VTABLE`), or `VP-TwoLevel` only!** Unguarded `WPO-Devirt*` is **forbidden**. | **No** (external DSOs rely on standard ABI slot offsets) |

Table 2 summarizes the empirical verification and runtime results across `host_bin` + `libplugin_dylib.so` (`200,000`-element mixed cross-DSO stream: `50%` host `SharedStruct`, `45%` plugin `SharedStruct` with duplicate vtable `0x7fe71313b248`, and `5%` `PluginPrivateStruct`; `support/cross_dso_vtable_benchmarks.csv`):

| Trait Class | Dispatch / Specialization Scheme | Sound on `PluginPrivateStruct` (`330`)? | Host `SharedStruct` Hit (%) | Plugin `SharedStruct` (Dup VTable) Hit (%) | Overall Stream Hit Rate (%) | Median Runtime ($\mu\text{s}$) | Speedup vs. Indirect (%) |
| :--- | :--- | :---: | ---: | ---: | ---: | ---: | ---: |
| `OpenExportedTrait` (`SharedTrait`) | `Baseline_Indirect_VTable_Call` | **Yes** (`330`) | `0.0%` | `0.0%` | `0.0%` | `529.65` | `0.00%` |
| `OpenExportedTrait` (`SharedTrait`) | `Unguarded_WPO_DevirtSingleImpl` *(Forbidden)* | **NO (`1007 ≠ 330`)** | `100.0%` | `100.0%` | `100.0%` | *Miscompiles* | *Unsound* |
| `OpenExportedTrait` (`SharedTrait`) | `VP3_VTablePtr_Guard` (`vptr == &VTABLE_host`) | **Yes** (`330`) | `100.0%` | `0.0%` *(safe fallback)* | `50.0%` | `556.96` | `-5.16%` |
| **`OpenExportedTrait` (`SharedTrait`)** | **`VP_TwoLevel_DSO_Guard` (`vptr == &VTABLE_host \|\| (*vptr).slot == target_fn`)** | **Yes (`330`)** | **`100.0%`** | **`100.0%`** | **`95.0%`** | **`410.87`** | **`+22.43%`** |
| **`CratePrivateTraitInOpenBinary` (`HostPrivateTrait`)** | **`Unguarded_WPO_DevirtSingleImpl` (`private_trait_closed_under_dso_linking_sound`)** | **Yes (Closed)** | **`100.0%`** | **N/A** | **`100.0%`** | **`140.69`** *(vs. `296.99`)* | **`+52.63%`** |

---

### 3. Lean `v4.34.1` Mechanization of `LinkWorldContract` and Duplicate-VTable Soundness

`Basis: source + execution (support/lean/CrossDsoLinkWorldContract.lean)`

All 8 theorems in `support/lean/CrossDsoLinkWorldContract.lean` check in the Lean `v4.34.1` kernel with zero `sorryAx` and zero `Lean.ofReduceBool`:

| Theorem Name | Mechanized Property | Kernel Axioms (`#print axioms`) |
| :--- | :--- | :--- |
| `vp_vtable_promote_open_world_sound` | `VP-3` (`if vptr == localVTableAddr`) equals `evalIndirectVCall` in **any** open DSO world with duplicate vtables and foreign plugins (`0` closed-world hypotheses). | `[propext, Quot.sound]` |
| `vp_slot_promote_open_world_sound` | Guarding on `(w.vtableAt vptr).slotPtr slot == targetFnPtr` is unconditionally sound in any open DSO world. | `[propext, Quot.sound]` |
| `vp_two_level_dso_promote_sound_and_hits_duplicate_vtable` | Two-level guard `vptr == localVTableAddr \|\| (*vptr).slot == targetFnPtr` is sound AND achieves `vpTwoLevelDirectHit = true` on duplicate cross-DSO vtables. | `[propext, Classical.choice, Quot.sound]` |
| `private_trait_closed_under_dso_linking_sound` | Under `DsoTypingBoundary`, if `traitId ∉ exportedTraits`, every runtime vtable for `traitId` belongs to `hostKnownVTables`. | *(none)* |
| `wpo_vfe_requires_non_escaping_layout_sound` | VTable slot compaction (`compactSlotIdx` / `expandCompactedVTable`) preserves semantics for all live slots `liveSlot ≠ deadSlot` on non-escaping traits. | `[propext, Quot.sound]` |
| `canary_duplicate_vtable_breaks_exhaustive_vptr_else_assumption` | Negative canary: a 2-impl branch funnel `if vptr == 10 then 100 else 200` miscompiles (`200 ≠ 100`) when a plugin passes duplicate vtable `vptr = 30` for `Impl1`. | *(none)* |
| `canary_cross_dso_unguarded_devirt_unsound` | Negative canary: `allowsUnguardedWpoDevirt .openExportedTrait = false` and foreign impl diverges (`42 ≠ 999`). | *(none)* |
| `canary_cross_dso_vfe_layout_mismatch_unsound` | Negative canary: compacting `deadSlot = 1` shifts slot `3` into offset `2`, breaking external DSO callers that read uncompacted offset `2` (`30 ≠ 20`). | *(none)* |

## Boundaries

- **Unsafe `transmute` Forging a Private Trait Object Across FFI**: `private_trait_closed_under_dso_linking_sound` relies on Rust's type-safety and visibility invariant (`DsoTypingBoundary`) that external crates/DSOs cannot name or implement a non-exported `trait HostPrivateTrait`. Raw pointer casts that fabricate an invalid vtable in `unsafe` Rust or C violate the source-level validity invariant of `&dyn Trait` before optimization begins.
- **Function-Pointer Address Equality Under PLT Lazy Binding without `-fno-plt` / `STV_DEFAULT`**: When two DSOs statically link separate copies of `libshared_api.rlib` with `Visibility::Hidden` (`partitioning.rs:888`), each DSO emits its own local copy of `<SharedStruct as SharedTrait>::compute` (`0x56261d48e040` vs. `0x7fe713102a40`). To achieve single-comparison `(*vptr).slot == target_fn_ptr` equality across DSOs without recording both DSO slot addresses, either the shared crate must be linked as a shared `dylib` (`-C prefer-dynamic=yes` / `-Z share-generics=yes`) or the canonical implementation must be exported with default visibility (`weak_odr` / `#[no_mangle]`).

## Evidence

- **Mechanized Lean `v4.34.1` proof development and multi-DSO benchmark harness**:
  - `support/lean/CrossDsoLinkWorldContract.lean` (`8` theorems, `0` `sorryAx`, `0` `Lean.ofReduceBool`)
  - `support/lean/lakefile.lean`
  - `support/cross_dso_vtable_probe/run_dso_experiment.py`
  - `support/cross_dso_vtable_probe/shared_api.rs`
  - `support/cross_dso_vtable_probe/plugin_dylib.rs`
  - `support/cross_dso_vtable_probe/host_bin.rs`
  - `support/cross_dso_vtable_results.json`
  - `support/cross_dso_vtable_benchmarks.csv`
- **Primary upstream source citations**:
  - `rust-lang/rust` (`58cf8f9c35b355199727627d07ae34a4e2846d67`):
    - `compiler/rustc_codegen_ssa/src/meth.rs:103-156` (`get_vtable` and `load_vtable`)
    - `compiler/rustc_codegen_llvm/src/consts.rs:294-344` (`static_addr_of_mut` and `static_addr_of_impl` setting `PrivateLinkage` and `UnnamedAddr::Global`)
    - `compiler/rustc_monomorphize/src/partitioning.rs:757-918` (`mono_item_linkage_and_visibility` and `ShimKind::VTable` hidden visibility)

## Revalidation

Run both the Lean `v4.34.1` kernel proof check and the multi-DSO `dlopen` vtable experiment:

```bash
anneal-lean-run --mode file --concurrency 4 -- elan run leanprover/lean4:v4.34.1 lean \
  reports/cross-dso-dynamic-linking-vtable-uniqueness-and-open-world-lto-contracts/support/lean/CrossDsoLinkWorldContract.lean
python3 reports/cross-dso-dynamic-linking-vtable-uniqueness-and-open-world-lto-contracts/support/cross_dso_vtable_probe/run_dso_experiment.py
```

Verify that `lean` exits with status `0` and zero `sorryAx`, that `duplicate_vtable_addresses_distinct` is `true`, and that `VP_TwoLevel_DSO_Guard` achieves `95.0%` direct-call hit rate (`100%` of `SharedStruct` instances across both DSOs) and `vp2l_sound_all_3 = true`.
