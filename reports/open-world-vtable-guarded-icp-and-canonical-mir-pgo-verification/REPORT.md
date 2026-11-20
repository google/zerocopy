# Open-World Vtable-Guarded Indirect-Call Promotion and Canonical MIR PGO Verification

## Summary

`Basis: source + execution + derived`

In `rustc` (`rust-lang/rust` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `1.98.0-nightly`) backed by LLVM (`llvm/llvm-project` at `fc4aad7b5db3fff421df9a9637605b9ca5667881`, `llvmorg-22.1.6`), `dyn Trait` vtables are **not** emitted as deduplicated external COMDAT symbols (`linkonce_odr` / `weak_odr`). Instead, `rustc_codegen_ssa::meth::get_vtable` (`compiler/rustc_codegen_ssa/src/meth.rs:103-123`) calls `CodegenCx::static_addr_of_mut` (`compiler/rustc_codegen_llvm/src/consts.rs:236-259`), emitting each vtable as a per-codegen-unit `private unnamed_addr constant` in `.data.rel.ro`. Moreover, full debuginfo (`-C debuginfo=2`) invokes `create_vtable_di_node` (`compiler/rustc_codegen_llvm/src/debuginfo/metadata.rs:1764-1768`), calling `llvm::set_unnamed_address(vtable, llvm::UnnamedAddr::No)` and preventing LLVM's `ConstantMerge` pass from merging identical vtables **even under closed-world full LTO (`-C lto=fat`)**. Two `&dyn Trait` references backed by the identical concrete type `T` therefore carry distinct runtime vtable addresses (`vptr_a != vptr_b`) across separately compiled `rlib`s, across `-C lto=fat -C debuginfo=2` binaries, and across dynamically loaded shared objects (`dlopen` with `--crate-type=cdylib` or `--crate-type=dylib`).

Stock `rustc` also omits `!type` metadata and `@llvm.type.test` intrinsics unless unstable `-Z virtual-function-elimination -C lto=fat` is active (`meth.rs:136-146`), and even then emits `@llvm.type.checked.load`, which LLVM's `IndirectCallPromotion.cpp` (`llvm/lib/Transforms/Instrumentation/IndirectCallPromotion.cpp:1008-1014`) does not yet recognize for vtable-pointer guards (`tryToPromoteWithVTableCmp`). Consequently, stock `-C profile-use` always falls back to `tryToPromoteWithFuncCmp` (`IndirectCallPromotion.cpp:691-735`, `CallPromotionUtils.cpp:383-395, 567-577`), loading the function pointer from the vtable before comparing. At the profile-key layer, LLVM IR instrumentation PGO (`llvm::getIRPGOFuncName` in `llvm/lib/ProfileData/InstrProf.cpp:391-412`) prefixes `internal`-linkage symbols with `<cgu_source_filename>;` when `!InLTO`; changing `-C codegen-units` or `-C lto={off,thin,fat}` alters CGU names and internalization sets (`compiler/rustc_monomorphize/src/partitioning.rs:515-601`), causing MD5 lookup misses (`UnableToFindTarget`), whereas canonical MIR keys `(StableCrateId, DefPathHash, CanonicalGenericArgs, CallsiteOrdinal)` remain 100% invariant.

Four soundness rules govern verified PGO and `dyn Trait` indirect-call promotion, mechanized in Lean `v4.34.1` (`leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52`, `support/VtableGuardedIcpPgo.lean`, `965` lines, `17` theorems, `0` `sorry`, `0` `bv_decide`, `0` `native_decide`):

1. **Value-guarded ICP (`if vptr == &VTABLE_K { direct_K(data, args) } else { indirect(vptr, data, args) }`) and finite guard cascades are unconditionally sound** (`valueGuardedIcp_exact_equiv`, `multiGuardedIcpCascade_exact_equiv`, `openWorldLink_preserves_guardedIcp`) across stale or adversarial PGO profiles, open-world `dlopen` duplicate vtables, all Tree Borrows receiver states (`&self` `Frozen`/`Cell`, `&mut self` `ReservedFrz`/`Unique` with `FnEntry` `StrongProtector`, and `!Unpin` retag elision), and panic unwinding, given only a local compile-time initializer check (`checkVtableGuardCert`).
2. **Wide-pointer metadata extraction (`UnOp::PtrMetadata`) has zero heap or Tree Borrows effect** (`extractWideVptr_zero_heap_and_tb_effect`), whereas dereferencing raw vtable slots (`*(vptr + offset)`) in Rust source is Undefined Behavior on Miri's zero-sized `GlobalAlloc::VTable` (`tb_05_raw_vtable_deref_abstract_machine_ub`); function-pointer-guarded ICP (`funcPtrGuardedIcp_exact_equiv`) is valid only after codegen lowers `GlobalAlloc::VTable` to concrete globals.
3. **Unguarded PGO devirtualization, closed-world `else unreachable`, peeled 2-impl guards, and negative vtable-inequality alias pruning (`vptr != &VTABLE_K => DynType != K` in `else`) are unsound** under duplicate vtables (`cex_unguardedStalePgo_treeBorrows_ub`, `cex_closedWorldUnreachable_dup_vtable_ub`, `cex_closedWorldPeeledTwoImpl_dup_vtable_ub`, `cex_negativeVtableInequalityAliasForwarding_unsound`), matching live `miri -Zmiri-tree-borrows` failures (`tb_03`, `tb_04`).
4. **Coalescing duplicate vtables into one callee (`if vptr == vt_1 || vptr == vt_2 { direct_m1(...) }`) is sound when `m1` and `m2` share identical runtime state (`rlib`, `-C prefer-dynamic` `dylib`)** (`twoVtableSingleCalleeIcp_sound_of_same_body`), **but breaks unwind equivalence across `--crate-type=cdylib` boundaries** (`cex_crossCdylibTwoVtableSingleCallee_breaks_unwind`) because each `cdylib` embeds its own `library/panic_unwind/src/gcc.rs:48` `static CANARY: u8`, aborting cross-`cdylib` panics via `__rust_foreign_exception()` (`exit -6`) whereas host-redirected panics are caught by `catch_unwind`.

## Applicability

`Basis: source + execution`

This report characterizes the pinned subjects in `REPORT.json`:

- **Rust toolchain (`rust-lang/rust` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):** `rustc 1.98.0-nightly (2026-05-31)` on `x86_64-unknown-linux-gnu`, covering `compiler/rustc_middle/src/ty/vtable.rs`, `compiler/rustc_codegen_ssa/src/meth.rs`, `compiler/rustc_codegen_llvm/src/consts.rs`, `compiler/rustc_codegen_llvm/src/debuginfo/metadata.rs`, `compiler/rustc_monomorphize/src/partitioning.rs`, `compiler/rustc_symbol_mangling/src/lib.rs`, `compiler/rustc_session/src/config.rs`, `library/panic_unwind/src/gcc.rs`, and `miri -Zmiri-tree-borrows`.
- **LLVM PGO and ICP (`llvm/llvm-project` at `fc4aad7b5db3fff421df9a9637605b9ca5667881`, `llvmorg-22.1.6`):** `IndirectCallPromotion.cpp`, `CallPromotionUtils.cpp`, `PGOInstrumentation.cpp`, `InstrProf.cpp`, and `llvm-profdata` (`22.1.6-rust-1.98.0-nightly`).
- **Mechanized semantics (`leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`, and `proofs-rs/lean-miri` at `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`):** Tree Borrows transitions and `FnEntry` retagging in `support/VtableGuardedIcpPgo.lean` follow `Miri/TreeBorrows/Permissions.lean` and `RetagPolicy.lean` and Villani et al. (PLDI 2025, DOI `10.1145/3735592`), alongside guarded ICP (Calder & Grunwald, POPL 1994, DOI `10.1145/174675.177973`), open-world devirtualization (Ishizaki et al., OOPSLA 2000, DOI `10.1145/353171.353191`), AutoFDO (Chen et al., CGO 2016, DOI `10.1145/2854038.2854044`), and separate-compilation verification (Kang et al., POPL 2016, DOI `10.1145/2837614.2837642`).

ELF `.data.rel.ro`, `lld --icf={safe,all}`, `dlopen(..., RTLD_NOW | RTLD_LOCAL)`, and Itanium `_Unwind_RaiseException` observations are specific to Linux ELF (`x86_64-unknown-linux-gnu`); PE/COFF and Mach-O linkers differ in section folding, though `consts.rs:254` `PrivateLinkage` vtable emission is target-independent. Dispatch timings in `experiment_4_guard_microbenchmark` measure a synthetic Rust microbenchmark rather than a modified compiler pass.

## Findings

### 1. Upstream `rustc` Vtable Emission, Linkage, and Deduplication

`Basis: source + execution`

`rust-lang/rust` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`) lowers vtables in two distinct layers:

1. **Middle-IR query allocation (`compiler/rustc_middle/src/ty/vtable.rs:13-52, 80-156`):**
   `vtable_allocation_provider(tcx, (ty, poly_trait_ref))` builds an immutable `Allocation` (`Mutability::Not`, line `154`) prefixed by `COMMON_VTABLE_ENTRIES` (`[MetadataDropInPlace, MetadataSize, MetadataAlign]` at indices `0..3`), followed by `VtblEntry::Method(instance)` and `VtblEntry::TraitVPtr` slots. Lines `80-83` note that Miri/CTFE represent wide-pointer vtable provenance via `GlobalAlloc::VTable` rather than raw dereferenceable bytes.
2. **Per-CGU `PrivateLinkage` LLVM globals (`compiler/rustc_codegen_ssa/src/meth.rs:103-123`, `compiler/rustc_codegen_llvm/src/consts.rs:236-286, 775-784`):**
   Unlike Itanium C++ `_ZTV` globals emitted in `linkonce_odr` COMDAT groups, `meth::get_vtable` caches `(ty, trait_ref)` only inside the current CGU's `cx.vtables()` (`meth.rs:111`) and calls `cx.static_addr_of(vtable_allocation, Some("vtable"))` (`meth.rs:117`). `static_addr_of_mut` (`consts.rs:236-259`) sets `llvm::Linkage::PrivateLinkage` (line `254`) and `llvm::UnnamedAddr::Global` (line `257`) with no external symbol or COMDAT group. Because vtables hold relocated function pointers, ELF places them in `.data.rel.ro` rather than `SHF_MERGE` `.rodata`, preventing cross-archive linker merging without FatLTO `ConstantMerge`.
3. **`-Z share-generics` vs. vtable duplication (`compiler/rustc_session/src/config.rs:1463-1471`, `compiler/rustc_symbol_mangling/src/lib.rs:126-143, 255-262`):**
   `Options::share_generics` defaults to `false` at `-C opt-level={2,3}` (`config.rs:1468`). Enabling `-Z share-generics=yes` shares generic `MonoItem::Fn` symbols across `rlib`s, but every crate performing an unsizing coercion `&Concrete as &dyn Trait` still invokes `meth::get_vtable` locally and emits a separate `private` vtable.
4. **`-C debuginfo=2` blocks FatLTO vtable merging (`compiler/rustc_codegen_llvm/src/debuginfo/metadata.rs:1746-1768`):**
   Under `DebugInfo::Full`, `create_vtable_di_node` calls `llvm::set_unnamed_address(vtable, llvm::UnnamedAddr::No)` (line `1767`) so debuggers can map vtable addresses back to concrete types. Verbatim `--emit=llvm-ir` output on `rustc 1.98.0-nightly` shows `-C debuginfo=0` emits `@vtable.0 = private unnamed_addr constant <{ [24 x i8], ptr }> ...`, whereas `-C debuginfo=2` emits `@vtable.0 = private constant <{ [24 x i8], ptr }> ..., !dbg !0`, forbidding LLVM's FatLTO `ConstantMerge` from deduplicating identical vtables.

**Measured runtime vtable and method pointer equality (`support/probe_results.json`, `experiment_1_vtable_deduplication_matrix`):**

| Configuration | Flags | `SensorAlpha` `vptr_eq` | `SensorAlpha` `fn_eq` | `Generic<u64>` `vptr_eq` | `Generic<u64>` `fn_eq` | Compile (`ms`) |
| :--- | :--- | :---: | :---: | :---: | :---: | ---: |
| `single_cgu1_o2` | `-O2 -C codegen-units=1 -C lto=off -C debuginfo=0` | `true` | `true` | `true` | `true` | `498.92` |
| `single_cgu2_o2` | `-O2 -C codegen-units=2 -C lto=off -C debuginfo=0` | `true` (merged CGU) | `true` | `true` | `true` | `518.57` |
| `single_cgu2_lld_icf_safe` | `-O2 -C codegen-units=2` + `lld --icf=safe` | `true` | `true` | `true` | `true` | `512.52` |
| `single_cgu2_lld_icf_all` | `-O2 -C codegen-units=2` + `lld --icf=all` | `true` | `true` | `true` | `true` | `800.35` |
| `two_rlibs_o2_default` | `provider_a` + `provider_b` `rlib`s, `-O2 -C debuginfo=0` | **`false`** (`0x556596008b58 != ...b18`) | `true` | **`false`** | `true` | `1155.15` |
| `two_rlibs_o2_share_generics` | `provider_a` + `provider_b` `rlib`s, `-O2 -Z share-generics=yes` | **`false`** (`0x5644983dfb58 != ...b18`) | `true` | **`false`** | `true` | `733.43` |
| `two_rlibs_fat_lto_debug0` | `provider_a` + `provider_b` `rlib`s, `-O2 -C lto=fat -C debuginfo=0` | **`true`** (`0x55f11fe6f300`) | `true` | **`true`** | `true` | `12413.19` |
| `two_rlibs_fat_lto_debug2` | `provider_a` + `provider_b` `rlib`s, `-O2 -C lto=fat -C debuginfo=2` | **`false`** (`0x55a7a2841350 != ...390`) | `true` | **`false`** | `true` | `13046.63` |
| `dlopen_cdylib_rtld_local_o2` | Host + `libplugin_b.so` (`cdylib`, `RTLD_LOCAL`), `-O2` | **`false`** (`0x563c2bf05548 != 0x7f0e2857ee18`) | **`false`** | **`false`** | **`false`** | `1559.36` |
| `dlopen_dylib_prefer_dynamic_o2` | Host + `libplugin_b.so` (`dylib`, `-C prefer-dynamic`), `-O2` | **`false`** (`0x55bf9e197d40 != 0x7fa82dea8890`) | **`true`** | **`false`** | **`true`** | `2638.13` |

*(In `single_cgu2_o2`, `merge_codegen_units` in `partitioning.rs:345-382` merges small submodules `unit_a` and `unit_b` into one CGU while `main` forms the second CGU, hitting the intra-CGU `cx.vtables()` cache; placing the coercions in separate `rlib`s immediately produces distinct vtable addresses `0x40` bytes apart in `.data.rel.ro`.)*

---

### 2. LLVM `IndirectCallPromotion` Guard Lowering and CGU-Prefixed IRPGO Fragility

`Basis: source + execution`

#### 2.1 Why Stock `rustc` Never Triggers Vtable-Pointer ICP in LLVM

`IndirectCallPromoter::processFunction` (`llvm/lib/Transforms/Instrumentation/IndirectCallPromotion.cpp:869-911`) chooses between `tryToPromoteWithVTableCmp` (`icmp eq ptr %vptr, @vtable`, sinking the slot load via `tryToSinkInstructions`, lines `313-326, 786-865`) and `tryToPromoteWithFuncCmp` (`icmp eq ptr %loaded_fn, @DirectCallee`, lines `691-735`). However, `computeVirtualCallSiteTypeInfoMap` (`IndirectCallPromotion.cpp:1000-1051`) discovers virtual callsites solely from `@llvm.type.test` intrinsics, noting in a `FIXME` at lines `1008-1010` that `@llvm.type.checked.load` is not yet handled. Stock `rustc` (`meth.rs:136-155`, `metadata.rs:1689-1691`) emits **`0` `@llvm.type.test` calls** in default builds (`0` across all configurations in `experiment_1`) and `@llvm.type.checked.load` under `-Z virtual-function-elimination -C lto=fat`. Thus LLVM always uses `tryToPromoteWithFuncCmp` (`llvm_ir_vtable_ptr_guards == 0` across all 5 PGO modes in `experiment_2`). On `panic=unwind` `invoke` calls, `versionCallSiteWithCond` (`llvm/lib/Transforms/Utils/CallPromotionUtils.cpp:353-373`) clones the `invoke` into `if.true.direct_targ`, retains the indirect `invoke` in `if.false.orig_indirect`, and updates normal/unwind destination phi nodes (`fixupPHINodeForNormalDest` lines `56-64`, `fixupPHINodeForUnwindDest` lines `87-98`).

#### 2.2 CGU-Prefixed IRPGO Symbol Hashes vs. Canonical MIR Keys

LLVM's `FuncPGOInstrumentation` (`PGOInstrumentation.cpp:675-752`) identifies functions by `getIRPGOFuncName(F)` (`InstrProf.cpp:391-412`) and a 60-bit JamCRC32 `FunctionHash`. Whenever `!InLTO && GlobalValue::isLocalLinkage(Linkage)`, `getIRPGONameForGlobalObject` (`InstrProf.cpp:364-368`) prepends `<cgu_source_filename>;` to the symbol name, and value profiling stores the 64-bit MD5 GUID of that string. During `-C profile-use`, `isValidTarget` (`IndirectCallPromotion.cpp:446-491`) rejects candidates missing from `Symtab` (`UnableToFindTarget`) or present only as external declarations (`!ICPAllowDecls && TargetFunction->isDeclaration()`, `NoTargetDef` at line `467`).

In `experiment_2_pgo_cgu_lto_vs_canonical_mir` (training at `-C opt-level=2 -C codegen-units=4 -C lto=off` over `40,000` `dyn StepOp` calls and `40,000` internal indirect `fn` calls):
- `llvm-profdata show --all-functions --ic-targets` records internalized `private_mix` under the CGU-prefixed key `pgo_app.e47e6214e983d8e4-cgu.0;_RNvNtCsjCgwuUOu0Om_7pgo_app12worker_local11private_mix` (`count = 40,000`), alongside external `HotLocalImpl::step` (`38,000`, `95%`) and `ColdExportImpl::step` (`2,000`, `5%`).
- Replaying `.profdata` at matching `cgu=4, lto=off` (`811 ms`) promotes `private_mix` (`llvm_ir_icp_direct_blocks = 1`), but fails to promote cross-CGU `HotLocalImpl::step` because it is an external `declare` in `dispatcher`'s CGU (`NoTargetDef`).
- Switching to `cgu=1, lto=off` (`610 ms`) or adding an unrelated module at `cgu=3, lto=off` (`355 ms`) changes the CGU hash prefix, dropping `llvm_ir_icp_direct_blocks` from **`1` to `0`**.
- Switching to `cgu=4, lto=thin` (`11,227 ms`) emits `remark: <unknown>:0:0: Cannot promote indirect call: target with md5sum 9639049316734959256 not found (count=38000)` during pre-import ICP. Only `cgu=4, lto=fat` (`12,598 ms`) promotes both `StepOp` targets (`promoted_count = 2`, `llvm_ir_func_ptr_guards = 3`, `llvm_ir_vtable_ptr_guards = 0`).
- Conversely, canonical MIR keys `(DefPath, CallsiteOrdinal)` extracted from `--emit=mir` match **`5 / 5` (`100%`)** across `cgu=4`, `cgu=1`, `lto=thin`, `lto=fat`, and `cgu=3` perturbation (`canonical_mir_keys_match_baseline == true` in every mode).

---

### 3. Lean `v4.34.1` Mechanization, Broken `cdylib` Unwind Assumption, and Miri Verification

`Basis: source + execution + derived`

#### 3.1 Kernel-Checked Theorems (`support/VtableGuardedIcpPgo.lean`)

`support/VtableGuardedIcpPgo.lean` (`965` lines, `47,372` bytes, namespace `VrustcPkg.VtableGuardedIcpPgo`) formalizes many-to-one multi-DSO vtable tables (`OpenWorldEnv`), the 6-state Tree Borrows machine (`TbPerm`, `performTbAccess` matching `Permissions.lean:62-112` at `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`), `FnEntry` retagging (`fnEntryRetag` matching `RetagPolicy.lean:68-92`, including `!Unpin` retag skip), and `CanaryDomain`-indexed unwinding (`ExecOutcome`). All `17` theorems pass `lean -DwarningAsError=true` with `0` `sorry`, `0` `bv_decide`, `0` `native_decide`, `0` `partial`, `0` `@[extern]`, and `0` custom `axiom`s:

| Theorem (`VrustcPkg.VtableGuardedIcpPgo.*`) | Lines | Result Proved | Axioms (`#print axioms`) |
| :--- | ---: | :--- | :--- |
| `canonicalMirKey_invariant`, `lookupMirProfile_invariant` | `122–134` | `CanonicalMirKey` and profile lookup are invariant across all `CguView`s | `[]` |
| `cex_llvmIrPgo_breaks_across_cgu_and_lto` | `139–158` | `llvmIrPgoFuncName` misses lookup on `cgu=4 -> cgu=1` and `lto=off -> fat` while MIR lookup hits | `[propext]` |
| `extractWideVptr_zero_heap_and_tb_effect` | `379–382` | Wide-pointer vtable projection (`UnOp::PtrMetadata`) has zero heap or Tree Borrows effect | `[]` |
| `valueGuardedIcp_exact_equiv` | `561–579` | `checkVtableGuardCert env cert = true` implies `evalValueGuardedIcp = evalIndirectDynCall` across all untrusted PGO hints, duplicate DSO vtables, Tree Borrows states, and unwinds | `[propext, Quot.sound]` |
| `multiGuardedIcpCascade_exact_equiv` | `597–620` | Exact equivalence for arbitrary K-candidate certified guard cascades | `[propext, Quot.sound]` |
| `funcPtrGuardedIcp_exact_equiv` | `660–678` | Soundness of codegen function-pointer-guarded ICP (`checkFuncPtrCert`) across shared-fn duplicate vtables | `[propext, Quot.sound]` |
| `twoVtableSingleCalleeIcp_sound_of_same_body` | `695–727` | Two-vtable single-callee coalescing is sound when both vtable methods have identical `MethodBody` (including `canaryDomain`) | `[propext, Quot.sound]` |
| `openWorldLink_preserves_guardedIcp` | `738–761` | `LinkExtends` (`dlopen` adding duplicate vtables) preserves `checkVtableGuardCert` and `ExecOutcome` equality | `[propext, Classical.choice, Quot.sound]` |
| `cex_unguardedStalePgo_treeBorrows_ub` | `815–822` | Unguarded stale-PGO devirtualization of `&FreezeAlpha` into `CellBeta` triggers `.ub .treeBorrowsUb` | `[propext]` |
| `cex_closedWorldUnreachable_dup_vtable_ub` | `835–849` | `else unreachable` triggers `.ub .unreachableExecuted` on duplicate `vtAlphaPlugin != vtAlphaHost` | `[propext]` |
| `cex_closedWorldPeeledTwoImpl_dup_vtable_ub` | `863–870` | 2-impl peeled guard misdispatches duplicate-vtable `FreezeAlpha` to `CellBeta` -> `.ub .treeBorrowsUb` | `[propext]` |
| `cex_negativeVtableInequalityAliasForwarding_unsound` | `895–899` | Forwarding caller state across `else` indirect call under `vptr != vtAlphaHost => DynType != Alpha` yields `some 100 != some 777` | `[propext]` |
| `cex_crossCdylibTwoVtableSingleCallee_breaks_unwind` | `910–928` | Coalescing `cdylib` `vtAlphaPlugin` (`canaryDomain = 1`) into host `methAlphaHost` (`canaryDomain = 0`) turns `.foreignExceptionAbort` into `.unwoundCaught 9` | `[propext]` |
| `mutSelf_protected_reservedFrz_conflict_preserved` | `934–957` | Protected `&mut self` (`ReservedFrz false` + `foreignRead` + `childWrite`) faults `.ub .treeBorrowsUb` identically in guarded and indirect calls | `[propext]` |

*(Plus structural helper lemmas `checkVtableGuardCert_inv` at lines `536–549` and `assocLookup_mem_all` at lines `638–653`.)*

#### 3.2 Broken Assumption Discovered: `cdylib` Split-`libstd` `CANARY` Unwind Non-Equivalence

Testing `dlopen_cdylib_rtld_local_o2` vs. `dlopen_dylib_prefer_dynamic_o2` revealed a critical boundary on multi-vtable guard coalescing (`if vptr == vt_host || vptr == vt_plugin { HostT::f(...) }`):
- `library/panic_unwind/src/gcc.rs:48, 68, 96-103` defines `static CANARY: u8 = 0`, tags every Rust panic with `canary: &CANARY`, and aborts via `super::__rust_foreign_exception()` if `!ptr::eq(canary, &CANARY)` at a `catch_unwind` cleanup pad.
- A `--crate-type=cdylib` plugin links its own private `libstd` (`&host::CANARY != &plugin::CANARY`). On panicking input `u64::MAX`, calling a plugin-created `&dyn TelemetryOp` indirectly invokes `plugin_b`'s `SensorAlpha::sample` and aborts the process (`plugin_unwind_exit_code = -6`, `plugin_unwind_foreign_abort = true`). Single-slot guarded ICP (`vptr == vt_host`) preserves this exact behavior, whereas coalescing `vt_plugin` into `host`'s `SensorAlpha::sample` throws `&host::CANARY`, turning an abort into a caught unwind (`cex_crossCdylibTwoVtableSingleCallee_breaks_unwind`) and bypassing plugin-local statics/allocators.
- Under `--crate-type=dylib -C prefer-dynamic`, vtables remain distinct (`0x55bf9e197d40 != 0x7fa82dea8890`), **but** `libstd-*.so` and `common_types.so` are shared (`alpha_fn_eq = true`, `plugin_unwind_caught_cleanly = true`, `exit 0`), making multi-vtable coalescing sound.

#### 3.3 Differential `miri -Zmiri-tree-borrows` Suite (`experiment_3_miri_tree_borrows_litmus`)

All five `#![no_core]` Miri Tree Borrows tests (`59–95 ms` each) match the Lean theorems:
- `tb_01_guarded_icp_shared_fast_and_fallback_sound` (`exit 0`, `67.74 ms`) and `tb_02_guarded_icp_mut_protector_sound` (`exit 0`, `67.04 ms`) pass with zero UB across hit, duplicate-vtable fallback, `&mut` `StrongProtector`, and `UnsafeCell::get()` interior mutation.
- `tb_03_unguarded_stale_pgo_frozen_write_ub` (`exit 1`, `59.14 ms`) and `tb_04_closed_world_peeled_else_dup_vtable_ub` (`exit 1`, `71.23 ms`) fail with `Undefined Behavior: write access through <36>/<44> at alloc19[0x0] is forbidden` (and in native `dlopen`, `tb_04`'s counterpart corrupts `37` into `62,678,480,394,911,815`).
- `tb_05_raw_vtable_deref_abstract_machine_ub` (`exit 1`, `94.98 ms`) fails on `*fp.vtable` with `attempting to access 32 bytes, but got alloc20 which is at or beyond the end of the allocation of size 0 bytes`, proving source/MIR ICP must compare wide-pointer metadata rather than dereferencing vtable bytes before codegen.

---

### 4. Mandatory Analytical Dimensions (`L1`–`L6`, `C1`–`C2`, `V1`–`V4`)

`Basis: execution + derived`

- **`L1` (Authoring/proof velocity):** `965` LOC (`47,372` bytes), `17` theorems; decidable `assocLookup` reduces all concrete positive and negative witnesses via `rfl` with zero SMT/tactic search loops.
- **`L2` (Toolchain build time):** `not measured` (used prebuilt `rustc 1.98.0-nightly` and `llvm-profdata 22.1.6`).
- **`L3` (Compile/synthesis latency):** Single-crate `-O2` = `499–800 ms`; two-`rlib` `-O2` = `733–1,155 ms`; `dlopen` `cdylib`/`dylib` = `1,559–2,638 ms`; `-C lto={thin,fat}` = `11,227–13,047 ms` (`14x–20x` slower than `cgu=4, lto=off` at `811 ms`). Canonical MIR PGO avoids paying FatLTO compile times solely to stabilize profile keys.
- **`L4` (Generated code execution performance — `Basis: execution (synthetic source-level microbenchmark, not a compiler pass)`):** Over `7` trials × `4,000,000` calls (`rustc -C opt-level=3 -C codegen-units=1`):
  - *Single-DSO (`95%` `vt1`, `5%` `SlowBeta`):* Indirect = `4.22 ns/call`; `fn_ptr` guard (`*(vptr + 24) == target_fn`) = `2.72 ns/call` (`1.55x`); 1-slot `vptr` guard (`vptr == vt1`, zero memory loads + inlining) = **`1.82 ns/call` (`2.32x` over indirect, `1.50x` over `fn_ptr` guard)**.
  - *Split-DSO alternating duplicate vtables (`50%` `vt1`, `45%` `vt2`, `5%` `SlowBeta`):* Indirect = `5.03 ns/call`; 1-slot `vptr` guard (`45%` fallback miss) = `4.02 ns/call`; 2-slot `vptr` guard = `4.11 ns/call`; shared-symbol `fn_ptr` guard (predictable `95%` hit when `fn_eq == true`, as in `rlib`/`dylib`) = **`2.54 ns/call` (`1.98x` over indirect)**.
- **`L5` (Certificate checking & cold-start latency):** Cold `lean -DwarningAsError=true VtableGuardedIcpPgo.lean` = **`7,664.88 ms` median** (`[7,262.44, 7,664.88, 21,389.93] ms`); Miri litmus checks = `59–95 ms` each. Whole-crate binary certificate throughput is `not measured`.
- **`L6` (RAM/disk/binary footprint):** `VtableGuardedIcpPgo.lean` = `47,372` B; `probe_results.json` = `16,723` B; `-C debuginfo=2` retains `8` unmerged non-`unnamed_addr` vtables under FatLTO vs. `0` under `-C debuginfo=0`. Whole-binary `.text`/`.data.rel.ro` delta on external crates is `not measured`.
- **`C1` & `C2` (Comprehensibility & Felleisen expressibility):** `checkVtableGuardCert` inspects three fields of one local `VtableDesc` with zero closed-world or profile-trust assumptions (`C1`); guarded ICP desugars orthogonally into `SwitchInt(PtrMetadata(w) == &VTABLE_K)` without altering `else`-branch alias types (`C2`).
- **`V1`–`V4` (Validation):** `V1` pairs `6` soundness/invariance theorems with `6` counterexamples; `V2` achieves 100% 3-way agreement across native `rustc`/`dlopen`, `miri -Zmiri-tree-borrows`, and `Lean v4.34.1`; `V3` notes speculative branch misprediction (`Spectre-v1` transient type confusion on `data_ptr` before `vptr == &VTABLE_K` resolves) is `not examined` on PMUs; `V4` validates `rlib`/LTO/`dlopen` on `x86_64` Linux while marking hardware LBR AutoFDO and external crates.io benchmarks `not measured`.

## Boundaries

`Basis: source + execution + derived`

- **`known not to apply` — Vtable pointer uniqueness (`vptr_1 != vptr_2 => Type_1 != Type_2`):** Falsified across `dlopen` DSOs, multi-`rlib` `-O2` static links (`two_rlibs_o2_default`, `two_rlibs_o2_share_generics`), and **`-C lto=fat -C debuginfo=2`** (`metadata.rs:1767`). Emitting `else unreachable`, peeling the last vtable guard, or pruning `else`-branch alias sets from `vptr != &VTABLE_K` is unsound.
- **`known not to apply` — Cross-`cdylib` multi-vtable single-callee coalescing under `panic=unwind`:** Redirecting a `cdylib` vtable to a host method body alters `panic_unwind` `CANARY` behavior (`gcc.rs:48, 97`: `SIGABRT` vs. caught unwind) and DSO-local statics/allocators. Valid only across shared-`std` `dylib`s or `nounwind` pure bodies.
- **`known not to apply` — Source/MIR raw vtable dereferencing (`*(vptr + slot)`):** Undefined Behavior in Miri (`GlobalAlloc::VTable` size `0`, `tb_05`); function-pointer guards apply only after codegen lowers vtables to data constants.
- **`unsupported` — Stock `rustc` + LLVM 22.1.6 vtable-pointer ICP:** Stock `rustc` emits zero `@llvm.type.test` calls, and `IndirectCallPromotion.cpp:1008-1010` leaves `@llvm.type.checked.load` unimplemented (`FIXME`).
- **`not examined` — Supertrait upcasting (`VtblEntry::TraitVPtr`), PE/Mach-O ICF, and Spectre-v1 / hardware LBR PMUs:** Multi-vtable subtrait upcasting (`vtable.rs:142-147`), non-ELF linkers, and PMU speculative/LBR measurements were not tested.
- **`unknown` — Optimal guard cascade arity `K` on large polymorphic Rust workspaces:** Sound for all `K`, but I-cache vs. branch-predictor trade-offs on large crates remain `unknown`.

## Evidence

`Basis: source + execution + normative`

1. **`rust-lang/rust` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `rustc 1.98.0-nightly`):**
   - `compiler/rustc_middle/src/ty/vtable.rs:13-52, 80-156` (`VtblEntry`, `GlobalAlloc::VTable`, `vtable_allocation_provider`).
   - `compiler/rustc_codegen_ssa/src/meth.rs:103-156` (`get_vtable`, `load_vtable`, `@llvm.type.checked.load`).
   - `compiler/rustc_codegen_llvm/src/consts.rs:236-286, 775-784` (`PrivateLinkage` + `UnnamedAddr::Global` in `static_addr_of_mut`).
   - `compiler/rustc_codegen_llvm/src/debuginfo/metadata.rs:1681-1768` (`apply_vcall_visibility_metadata`, `UnnamedAddr::No` in `create_vtable_di_node`).
   - `compiler/rustc_monomorphize/src/partitioning.rs:201-281, 345-382, 515-601` (`LocalCopy`, `merge_codegen_units`, `internalize_symbols`).
   - `compiler/rustc_session/src/config.rs:1463-1475` (`share_generics`, `SymbolManglingVersion::V0`) and `compiler/rustc_symbol_mangling/src/lib.rs:126-143, 255-317`.
   - `library/panic_unwind/src/gcc.rs:45-73, 85-112` (`static CANARY: u8`, `__rust_foreign_exception`).
2. **`llvm/llvm-project` (`fc4aad7b5db3fff421df9a9637605b9ca5667881`, `llvmorg-22.1.6`):**
   - `llvm/lib/Transforms/Instrumentation/IndirectCallPromotion.cpp:446-555, 691-735, 786-911, 1000-1051`.
   - `llvm/lib/Transforms/Utils/CallPromotionUtils.cpp:56-98, 287-395, 483-577, 664-683`.
   - `llvm/lib/Transforms/Instrumentation/PGOInstrumentation.cpp:675-752` and `llvm/lib/ProfileData/InstrProf.cpp:344-413`.
3. **`proofs-rs/lean-miri` (`c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`) & `leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`):**
   - `Miri/TreeBorrows/Permissions.lean:19-112` and `Miri/TreeBorrows/RetagPolicy.lean:14-93`.
4. **Peer-Reviewed Papers:** Calder & Grunwald (POPL 1994, `10.1145/174675.177973`); Ishizaki et al. (OOPSLA 2000, `10.1145/353171.353191`); Chen et al. (CGO 2016, `10.1145/2854038.2854044`); Kang et al. (POPL 2016, `10.1145/2837614.2837642`); Villani et al. (PLDI 2025, `10.1145/3735592`).
5. **Package Support Material (`observed_at: 2026-11-20`):** `support/VtableGuardedIcpPgo.lean`, `support/run_vtable_icp_pgo_probe.py`, and `support/probe_results.json`.

## Revalidation

`Basis: execution + source`

1. **Kernel-check the Lean `v4.34.1` proofs (~8s):**
   ```bash
   lean -DwarningAsError=true support/VtableGuardedIcpPgo.lean
   ```
   Verify exit code `0` and confirm `#print axioms` on exported theorems uses only `{propext, Quot.sound, Classical.choice}` (`0` `sorryAx`, `0` `Lean.ofReduceBool`).
2. **Re-execute the `rustc` / `llvm-profdata` / `dlopen` / `miri` probe (~35s):**
   ```bash
   PYTHONDONTWRITEBYTECODE=1 python3 -B support/run_vtable_icp_pgo_probe.py
   ```
   Inspect `support/probe_results.json`: (a) `two_rlibs_o2_default` and `two_rlibs_fat_lto_debug2` test whether `PrivateLinkage` / `UnnamedAddr::No` still prevent static vtable merging; (b) `llvm_ir_vtable_ptr_guards` tests whether `@llvm.type.checked.load` ICP was added upstream; (c) `plugin_unwind_foreign_abort` (`cdylib`) vs. `plugin_unwind_caught_cleanly` (`dylib`) checks `panic_unwind` `CANARY` isolation; and (d) `tb_01`–`tb_05` assert `0` Miri regressions under `-Zmiri-tree-borrows`.
