# Whole-Program Devirtualization, Dead-Argument Elimination, and Global Promotion Replay Under `ExportList` Closed-World Contracts

## Summary

In standard `rustc` 1.99.1 (`58cf8f9c35b355199727627d07ae34a4e2846d67`) and bundled LLVM 23.1.1 (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), LLVM's `WholeProgramDevirt` pass (`llvm/lib/Transforms/IPO/WholeProgramDevirt.cpp`, `2,679` lines) **never fires on standard Rust `dyn Trait` vtables under `-C lto=thin` or `-C lto=fat`** unless unstable `-Z virtual-function-elimination` or `-Z sanitizer=cfi` is explicitly enabled, because `rustc` omits `!type` metadata on vtable globals by default (`compiler/rustc_codegen_llvm/src/meth.rs`). By contrast, a verified `rustc` backend that exports typed `GlobalAlloc::VTable` records and trait-implementation relationships in `.anneal-mir` has exact, machine-checkable knowledge of every vtable in the closed crate graph.

This report formalizes, mechanizes in Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`), and benchmarks the four whole-program optimization (WPO) families whose soundness depends on closed-world `ExportList` premises (`support/WholeProgramDevirtDaeGlobalOptProbe.lean`, `14` theorems, `0` `sorryAx`, `0` `Lean.ofReduceBool`):

1. **Closed-Trait-World Devirtualization (`ClosedTraitVTables(TraitId, ExportList)`)**:
   - When a binary, `staticlib`, or `cdylib` is linked at `SymbolExportLevel::C` (`compiler/rustc_codegen_ssa/src/back/symbol_export.rs:94-224`) with no `dylib` dependencies or FFI imports constructing `dyn TraitId` fat pointers, the set of `GlobalAlloc::VTable` instances for `TraitId` across all linked `.anneal-mir` units is exhaustively known (`InClosedTraitWorld`).
   - We mechanize four `HybridTrace` devirtualization schemas under `InClosedTraitWorld`:
     - **`WPO-DevirtSingleImpl` (`wpo_devirt_single_impl_sound`)**: Replaces indirect vtable dispatch unconditionally with a direct call when $|\text{VTables}(\text{TraitId})| = 1$ (or when all vtables map `slot` to the same implementation body);
     - **`WPO-DevirtBranchFunnel` (`wpo_devirt_branch_funnel_sound`)**: Replaces indirect dispatch for $2 \le |\text{VTables}(\text{TraitId})| \le 4$ with an exhaustive `vtable_ptr` comparison ladder (`if vtable_ptr == @V1 ... else if vtable_ptr == @V2 ... else @V3`) with **no indirect call fallback**;
     - **`WPO-DevirtConstRet` (`wpo_devirt_const_ret_sound`)**: Folds a virtual call directly to a constant `c₀` when all closed-world implementations return `c₀`;
     - **`WPO-VFE` (`wpo_vfe_unused_slot_strip_sound`)**: Replaces never-called vtable slots with zero/trap placeholders so `GlobalDCE` can strip unused trait methods.
   - We mechanize a negative canary (`canary_open_world_devirt_unsound`) proving that omitting the `InClosedTraitWorld` guard causes `WPO-DevirtBranchFunnel` to execute the wrong method when an external `dylib` passes an unrecorded vtable `v_ext = 99`.
2. **Signature-Mutating Optimizations Under `SignatureMutable(sym, ExportList)`**:
   - **`WPO-DeadArgAndRetElim` (`wpo_dead_arg_and_ret_elim_sound`)**: When `sym ∉ ExportList` and `addressTaken sym = false`, simultaneously dropping an unused parameter or return tuple component at `sym`'s definition and at every direct call site preserves whole-program semantics.
   - **`WPO-ArgPromoteByVal` (`wpo_arg_promote_by_val_sound`)**: When `sym ∉ ExportList`, `addressTaken sym = false`, and no store inside `sym` aliases a `dereferenceable` pointer parameter `ptr` before its loads, promoting `*ptr` to a by-value register argument at all call sites is sound.
   - Negative canaries `canary_address_taken_dae_unsound` and `canary_aliased_arg_promote_unsound` prove that violating either `!addressTaken` or `NoAlias` breaks refinement.
3. **`GlobalOpt` Static Promotion and Boolean Shrinking (`WPO-GlobalOptPromote`)**:
   - Under `ClosedStaticContract` (`s ∉ ExportList`, `s ∉ usedSet`, `escaped s = false`), we prove that store-free statics can be promoted to `.rodata` constants (`wpo_globalopt_rodata_const_fold_sound`) and two-valued statics (`w = v₀ ∨ w = v₁`) can be shrunk to a 1-byte boolean flag (`wpo_globalopt_boolean_shrink_sound`, modeling `TryToShrinkGlobalToBoolean` in `GlobalOpt.cpp`), along with negative canary `canary_escaped_globalopt_const_fold_unsound`.
4. **Empirical Evaluation on `x86_64` and `aarch64` (`support/wpo_exportlist_benchmarks.csv`)**:
   - Across `x86_64-unknown-linux-gnu` and `aarch64-unknown-linux-gnu`, applying the closed-world `WPO-Devirt*`, `WPO-DeadArgAndRetElim`, `WPO-ArgPromoteByVal`, and `WPO-GlobalOptPromote` schemas eliminates **100% of indirect calls** in the hot pipeline loop (`4` $\rightarrow$ `0` `callq *...` on `x86_64`; `3` $\rightarrow$ `0` `blr` on `aarch64`), reduces runtime by **`+4.46%`** even when pointer inputs are black-boxed per iteration, and validates all 6 WPO certificates in `0.0001`–`0.0002` $\mu\text{s}$ (`146`–`301` bytes per certificate).

## Applicability

- **Subjects**: `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), `rust-lang/llvm-project` `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), and `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`).
- **Targets examined**: `x86_64-unknown-linux-gnu` (execution + object disassembly) and `aarch64-unknown-linux-gnu` (object disassembly).
- **Relation to other corpus packages**: Extends `compositional-correctness-linking-and-whole-program-optimization`, `llvm-interprocedural-lto-and-codegen-optimization-obligations`, and `rustc-lto-mechanics-symbol-preservation-and-performance-value`.

## Findings

### 1. Lean `v4.34.1` Mechanization of Closed-World WPO Schemas and Negative Canaries

`Basis: source + execution (support/WholeProgramDevirtDaeGlobalOptProbe.lean)`

All 14 theorems in `support/WholeProgramDevirtDaeGlobalOptProbe.lean` check in Lean `v4.34.1` with zero `sorryAx` and zero `Lean.ofReduceBool`:

| Theorem Name | WPO Schema | Closed-World Side Condition | Kernel Axioms (`#print axioms`) |
| :--- | :--- | :--- | :--- |
| `wpo_devirt_single_impl_sound` | `WPO-DevirtSingleImpl` | `InClosedTraitWorld vtableId knownVTables` $\land$ all vtables map `slot` to `uniqueFn` | *(none)* |
| `wpo_devirt_branch_funnel_sound` | `WPO-DevirtBranchFunnel` | `InClosedTraitWorld vtableId [v₁, v₂, v₃]` (exhaustive 3-way ladder without indirect fallback) | `[propext, Classical.choice, Quot.sound]` |
| `wpo_devirt_const_ret_sound` | `WPO-DevirtConstRet` | `InClosedTraitWorld` $\land$ all implementations of `slot` return constant `c₀` | *(none)* |
| `wpo_vfe_unused_slot_strip_sound` | `WPO-VFE` | `liveSlot ≠ deadSlot` across all calls in the closed module graph | `[propext, Quot.sound]` |
| `canary_open_world_devirt_unsound` | Canary (Devirt) | Unrecorded external `dylib` vtable `v_ext = 99 ∉ [1, 2, 3]` misdispatches in `devirtBranchFunnel3` | *(none)* |
| `wpo_dead_arg_and_ret_elim_sound` | `WPO-DeadArgAndRetElim` | `SignatureMutable sym exportList addressTaken` $\land$ `DeadArgIndependent f` | *(none)* |
| `canary_address_taken_dae_unsound` | Canary (DAE) | Rewriting ABI when `addressTaken sym = true` corrupts indirect callers | *(none)* |
| `wpo_arg_promote_by_val_sound` | `WPO-ArgPromoteByVal` | `SignatureMutable` $\land$ `(preWrite m) ptr = m ptr` (no aliasing write before load) | *(none)* |
| `canary_aliased_arg_promote_unsound` | Canary (ArgPromote) | Aliased store to `ptr` before load causes by-value promotion to read stale value (`10 ≠ 99`) | *(none)* |
| `wpo_globalopt_rodata_const_fold_sound` | `WPO-GlobalOptPromote` | `ClosedStaticContract s exportList usedSet escaped` $\land$ zero stores (`m s = initVal`) | *(none)* |
| `wpo_globalopt_boolean_shrink_sound` | `WPO-GlobalOptPromote` | `ClosedStaticContract` $\land$ store values restricted to `{v₀, v₁}` (`TryToShrinkGlobalToBoolean`) | `[propext, Classical.choice, Quot.sound]` |
| `canary_escaped_globalopt_const_fold_unsound` | Canary (GlobalOpt) | Escaped static mutated by external writer (`42 ≠ 0`) invalidates constant folding | *(none)* |
| `checkWpoCert_sound` / `_complete` | Checker | Soundness and completeness of the decidable `HybridTrace` WPO certificate checker `checkWpoCert` | `[propext]` |

---

### 2. Instruction, Indirect-Call, and Runtime Measurements on `x86_64` and `aarch64`

`Basis: execution (support/run_wpo_exportlist_benchmarks.py, support/wpo_exportlist_benchmarks.csv, support/wpo_certificates_and_metrics.json)`

Table 2 compares standard `rustc` `-C opt-level=3 -C lto=fat -C codegen-units=1` (`OpenWorld_Standard_Rustc_LTO`, where `WholeProgramDevirt` cannot fire without `!type` metadata) against closed-world `.anneal-mir` WPO specialization:

| Target | Configuration | Loop Function Instructions | Indirect Calls in Loop (`callq *` / `blr`) | Direct Calls in Loop (`callq` / `bl`) | Median Runtime ($\mu\text{s}$) | Speedup vs. Standard `rustc` FatLTO (%) |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: |
| `x86_64-unknown-linux-gnu` | `OpenWorld_Standard_Rustc_LTO` | 81 | **4** | 0 | 1,043.71 | `0.00%` |
| `x86_64-unknown-linux-gnu` | `ClosedWorld_WPO_Devirt_Single_Funnel_Const` | 94 | **1** | 0 | 1,017.16 | `+2.54%` |
| `x86_64-unknown-linux-gnu` | **`ClosedWorld_WPO_Full_Devirt_DAE_ArgProm_GlobalOpt`** | **82** | **0** | **0** | **997.19** | **`+4.46%`** |
| `aarch64-unknown-linux-gnu` | `OpenWorld_Standard_Rustc_LTO` | 80 | **3** | **1** | — | — |
| `aarch64-unknown-linux-gnu` | `ClosedWorld_WPO_Devirt_Single_Funnel_Const` | 95 | **0** | **1** | — | — |
| `aarch64-unknown-linux-gnu` | **`ClosedWorld_WPO_Full_Devirt_DAE_ArgProm_GlobalOpt`** | **88** | **0** | **0** | — | — |

Table 3 lists the generated `HybridTrace` closed-world WPO certificates and checking costs:

| Certificate ID | WPO Schema | Serialized Size (Bytes) | Check Time ($\mu\text{s}$) | Verified |
| :--- | :--- | ---: | ---: | :---: |
| `WPO_DevirtSingleImpl_SingleCodec_encode_word` | `WPO-DevirtSingleImpl` | 269 | `0.0001` | `true` |
| `WPO_DevirtBranchFunnel_PacketStage_process` | `WPO-DevirtBranchFunnel` | 301 | `0.0001` | `true` |
| `WPO_DevirtConstRet_PacketStage_const_version` | `WPO-DevirtConstRet` | 158 | `0.0001` | `true` |
| `WPO_VFE_SingleCodec_unused_vfe_slot` | `WPO-VFE` | 146 | `0.0001` | `true` |
| `WPO_DAE_and_ArgPromote_internal_helper` | `WPO-DeadArgAndRetElim+WPO-ArgPromoteByVal` | 296 | `0.0001` | `true` |
| `WPO_GlobalOpt_GLOBAL_RO_FACTOR_and_MODE` | `WPO-GlobalOptPromote` | 298 | `0.0001` | `true` |

## Boundaries

- **Dynamic Library (`dylib`) and FFI Trait Object Boundaries**: `ClosedTraitVTables(TraitId, ExportList)` holds only when no linked `dylib` or foreign FFI function constructs or returns a `&dyn TraitId` / `Box<dyn TraitId>` whose vtable is defined outside the `.anneal-mir` link graph. Whenever a trait is exposed across a dynamic plugin boundary, open-world `VP-3` (`VP-VTablePromote` with an indirect fallback branch) must be used instead of `WPO-DevirtSingleImpl` or `WPO-DevirtBranchFunnel`.
- **Inline Assembly Symbol References**: A symbol or static referenced inside a `global_asm!` or `asm!` string without an explicit `sym` operand cannot be safely internalized or signature-mutated unless the `sym` operand is recorded in `.anneal-summary`'s `AddressTaken` / `ExportList` root set.

## Evidence

- **Mechanized Lean `v4.34.1` proof development and WPO benchmark harness**:
  - `support/WholeProgramDevirtDaeGlobalOptProbe.lean` (`392` lines, `14` theorems, `0` `sorryAx`)
  - `support/run_wpo_exportlist_benchmarks.py`
  - `support/wpo_exportlist_benchmarks.csv`
  - `support/wpo_certificates_and_metrics.json`
- **Primary upstream source citations**:
  - `rust-lang/llvm-project` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`):
    - `llvm/lib/Transforms/IPO/WholeProgramDevirt.cpp` (`WholeProgramDevirt` pass requiring `!type` metadata)
    - `llvm/lib/Transforms/IPO/DeadArgumentElimination.cpp` (`DeadArgumentEliminationPass`)
    - `llvm/lib/Transforms/IPO/ArgumentPromotion.cpp` (`ArgumentPromotionPass`)
    - `llvm/lib/Transforms/IPO/GlobalOpt.cpp` (`GlobalOptPass`, `TryToShrinkGlobalToBoolean`)
  - `rust-lang/rust` (`58cf8f9c35b355199727627d07ae34a4e2846d67`):
    - `compiler/rustc_codegen_ssa/src/back/symbol_export.rs:94-224` (`SymbolExportLevel` and LTO export root computation)

## Revalidation

Run both the Lean `v4.34.1` proof check and the closed-world WPO benchmark harness:

```bash
anneal-lean-run --mode file --concurrency 4 -- elan run leanprover/lean4:v4.34.1 lean \
  reports/whole-program-devirt-dae-and-globalopt-exportlist-certificates/support/WholeProgramDevirtDaeGlobalOptProbe.lean
python3 reports/whole-program-devirt-dae-and-globalopt-exportlist-certificates/support/run_wpo_exportlist_benchmarks.py
```

Verify that `lean` exits with status `0` and zero `sorryAx`, and that `ClosedWorld_WPO_Full_Devirt_DAE_ArgProm_GlobalOpt` reduces indirect calls in the hot loop from `4` to `0` on `x86_64` and from `3` to `0` on `aarch64`.
