# Value-Profile Specialization (`IPVK_MemOPSize`, `IPVK_IndirectCallTarget`, `IPVK_VTableTarget`) and Speculative Guard Certificates in `HybridTrace`

## Summary

In `rustc` 1.99.1 (`58cf8f9c35b355199727627d07ae34a4e2846d67`) and LLVM 23.1.1 (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), over `85%` of the runtime speedup achieved by 2-stage Profile-Guided Optimization on Rust workloads comes from value-profile specialization of variable-length memory intrinsics (`IPVK_MemOPSize = 1` in `PGOMemOPSizeOpt.cpp`) and indirect calls or dynamic trait vtables (`IPVK_IndirectCallTarget = 0` and `IPVK_VTableTarget = 2` in `IndirectCallPromotion.cpp`). This report formalizes, mechanizes in Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`), and benchmarks three value-profile specialization schemas for the `HybridTrace` translation-validation and proof-producing compilation pipeline:

1. **Zero-Trust Soundness via Tautological Diamond Splitting**:
   - Specializing a dynamic operation $\text{Op}(x)$ for a profile-predicted constant $c$ by rewriting $\text{Op}(x)$ into `if (x == c) { Op(c) } else { Op(x) }` is a **tautological semantic identity** regardless of whether the profile is accurate, stale, or adversarial. All profile heuristics remain strictly outside the Trusted Computing Base (TCB).
2. **Three Mechanized `HybridTrace` Value-Profile Schemas (`support/ValueProfileSpecializationProofs.lean`, `0` `sorryAx`, `0` `Lean.ofReduceBool`)**:
   - **Schema VP-1 (`VP-MemOpSizeSpecialize`)**: Splits `@llvm.memcpy.p0.p0.i64(dst, src, len, isvolatile=false)` (lowered from `copy_from_slice` / `ptr::copy_nonoverlapping`) into a guarded `SwitchInt(len, [S_1 -> bb_fast_1, ..., otherwise -> bb_fallback])`. We prove (`vp1_memcpy_diamond_sound`, `vp1_multi_size_ladder_sound`) that this preserves byte-level values, poison bits, pointer provenance, and Tree Borrows permissions unconditionally. For non-power-of-two hot sizes $S \in [8, 16]$ (such as $S = 12$), we prove (`vp1_overlapping_head_tail_sound`) that loading the two overlapping 8-byte slices `src[0..8)` and `src[S-8..S)` into register temporaries *before* writing both to `dst[0..8)` and `dst[S-8..S)` is byte-for-byte identical to an $S$-byte `memcpy`, and we mechanize a negative canary (`canary_unbuffered_overlapping_copy_clobbers`) showing that writing the head slice before loading the tail slice corrupts partially overlapping buffers (`dst = src + 2`).
   - **Schema VP-2 (`VP-IndirectCallPromote`)**: Rewrites an indirect function-pointer call `(*fn_ptr)(args...)` into `if (fn_ptr == @HotCallee) { @HotCallee(args...) } else { (*fn_ptr)(args...) }` followed by direct-call inlining (`T04`). We prove (`vp2_indirect_call_promote_sound`) that because function definitions occupy disjoint code addresses (or share an address only when merged by `MergeFunctions` `T12` under alpha-equivalent semantics and identical `FnAbi`), pointer equality soundly justifies direct invocation, and we prove a negative canary (`canary_vp2_abi_mismatch_unsound`) when `FnAbi` compatibility is omitted.
   - **Schema VP-3 (`VP-VTablePromote`)**: Rather than loading `fn_ptr = *(vtable_ptr + slot_offset)` from a Rust `&dyn Trait` fat pointer `(data_ptr, vtable_ptr)` and then comparing `fn_ptr == @HotImpl::method`, Schema VP-3 compares `vtable_ptr == &VTable_HotImpl` directly. Under the read-only `.rodata` global vtable invariant (`RoDataVTableSlotInv`), we prove (`vp3_vtable_promote_sound`, `vp3_multi_method_promote_sound`) that a single `vtable_ptr` comparison breaks the load-to-branch latency chain and simultaneously specializes **multiple** sequential trait method calls on the same fat pointer, and we prove a negative canary (`canary_vp3_writable_vtable_unsound`) if the vtable resides in writable memory.
3. **End-to-End Runtime Performance (`VP-3` Outperforms Standard LLVM 23.1.1 PGO by `13.5%` on `x86_64` and `10.6%` on `i686`)**:
   - On the multi-method `&dyn StagePipeline` (`pre_validate` + `execute`) and dual-size (`16 B` + `12 B`) slice-copy benchmark (`support/value_profile_specialization_benchmarks.csv`), `VP-1` alone achieves a **`+56.94%` speedup** (`2,147.70` $\mu\text{s}$ $\rightarrow$ `924.74` $\mu\text{s}`, capturing `87.7%` of LLVM 23.1.1 PGO's gain on `x86_64`), while combining `VP-1 + VP-3` (`HybridTrace_VP1_plus_VP3_VTablePromote`) reduces runtime to **`650.78` $\mu\text{s}$ (`+69.70%` speedup, `107.3%` of LLVM PGO's gain on `x86_64`)** and **`1,340.56` $\mu\text{s}$ (`+47.39%` speedup, `115.2%` of LLVM PGO's gain on `i686`)**, with certificate checking times of `0.001`–`0.003` $\mu\text{s}$ per site.

## Applicability

- **Subjects**: `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), `rust-lang/llvm-project` `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), and `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`).
- **Targets examined**: `x86_64-unknown-linux-gnu` and `i686-unknown-linux-gnu`.
- **Relation to other corpus packages**: Extends `rustc-pgo-mechanics-heuristics-value-and-ir-portability`, `llvm-o3-derivation-formats-expressiveness-and-checking-cost`, and `lean-derivation-checker-soundness-and-completeness-prototype`.

## Findings

### 1. Lean `v4.34.1` Mechanization of Schemas VP-1, VP-2, and VP-3

`Basis: source + execution (support/ValueProfileSpecializationProofs.lean)`

All 11 positive soundness/completeness and negative canary theorems in `support/ValueProfileSpecializationProofs.lean` elaborate in Lean `v4.34.1` with zero `sorryAx` and zero `Lean.ofReduceBool`:

| Theorem Name | Schema | Statement Summary | Kernel Axioms (`#print axioms`) |
| :--- | :--- | :--- | :--- |
| `vp1_memcpy_diamond_sound` | `VP-1` | `vp1DiamondMemcpy m dst src len S = memcpySem m dst src len` for all `m, dst, src, len, S` (preserving byte values, poison, provenance, and Tree Borrows tags). | `[propext, Quot.sound]` |
| `vp1_multi_size_ladder_sound` | `VP-1` | Multi-target `SwitchInt` size specialization ladder `vp1LadderMemcpy m dst src len sizes = memcpySem m dst src len`. | `[propext, Quot.sound]` |
| `vp1_overlapping_head_tail_sound` | `VP-1` | For $8 \le S \le 16$, buffered 2-load (`[0..8)` and `[S-8..S)`) + 2-store `overlappingHeadTailCopy m dst src S = memcpySem m dst src S`. | `[propext, Classical.choice, Quot.sound]` |
| `canary_unbuffered_overlapping_copy_clobbers` | `VP-1` (Canary) | Storing head `[0..8)` before loading tail `[S-8..S)` when `dst = src + 2, S = 12` overwrites byte `src + 4` (`≠ memcpySem`). | *(none — pure kernel reduction)* |
| `vp2_indirect_call_promote_sound` | `VP-2` | `vp2IndirectCallPromote w callAbi fnPtr hotSym arg = evalIndirectCall w callAbi fnPtr arg`. | `[propext, Quot.sound]` |
| `canary_vp2_abi_mismatch_unsound` | `VP-2` (Canary) | Inlining a promoted target whose `FnAbi` mismatches `callAbi` diverges from `evalIndirectCall` (which traps on ABI mismatch). | *(none)* |
| `vp3_vtable_promote_sound` | `VP-3` | Under `RoDataVTableSlotInv`, comparing `vtablePtr == hotVTableAddr` and calling `hotMethodPtr` refines `evalDynTraitCall`. | `[propext, Quot.sound]` |
| `vp3_multi_method_promote_sound` | `VP-3` | Single `vtablePtr == hotVTableAddr` guard soundly specializes two sequential trait method calls (`slot₁`, `slot₂`) on the same fat pointer. | `[propext, Quot.sound]` |
| `canary_vp3_writable_vtable_unsound` | `VP-3` (Canary) | Mutating a writable vtable slot invalidates `vp3VTablePromote` (`≠ evalDynTraitCall`). | *(none)* |
| `checkVPSpecCert_sound` / `_complete` | Checker | Soundness and completeness of the decidable `HybridTrace` certificate validator `checkVPSpecCert`. | `[propext, Quot.sound]` |

---

### 2. Runtime Comparison: `VP-1`, `VP-2` (`fn_ptr` Check), `VP-3` (`vtable_ptr` Check), and LLVM 23.1.1 PGO

`Basis: execution (support/run_value_profile_specialization.py, support/value_profile_specialization_benchmarks.csv, support/value_profile_certificates_and_metrics.json)`

Table 2 compares the five configurations across `x86_64-unknown-linux-gnu` and `i686-unknown-linux-gnu`:

| Target | Configuration | Median Runtime ($\mu\text{s}$) | Speedup vs. No-PGO Baseline (%) | Share of LLVM 23.1.1 PGO Speedup Captured (%) | Architectural Mechanism |
| :--- | :--- | ---: | ---: | ---: | :--- |
| `x86_64` | `Baseline_NoPGO_Dynamic` | 2,147.70 | `0.00%` | `0.0%` | Unspecialized `llvm.memcpy` call + 2 indirect vtable calls per iteration. |
| `x86_64` | `LLVM_23_1_1_PGO_Full` | 752.73 | `+64.95%` | `100.0%` | LLVM `PGOIndirectCallPromotion` (`IPVK_IndirectCallTarget` per call site) + `PGOMemOPSizeOpt`. |
| `x86_64` | `HybridTrace_VP1_MemOpSize_16B_12B` | 924.74 | `+56.94%` | **`87.7%`** | Specializes `16 B` (single `u128` load/store) and `12 B` (overlapping `2 × u64` head+tail load/store). |
| `x86_64` | `HybridTrace_VP1_plus_VP2_FnPtrPromote` | 932.08 | `+56.60%` | `87.1%` | Loads `fn_ptr_1 = *(vtbl + 24)` and `fn_ptr_2 = *(vtbl + 32)` before comparing each against `@OpFastAdd`. |
| `x86_64` | **`HybridTrace_VP1_plus_VP3_VTablePromote`** | **650.78** | **`+69.70%`** | **`107.3%`** | Compares `vtable_ptr == &VTable_OpFastAdd` **once**, eliminating both vtable loads and fusing `pre_validate` + `execute`! |
| `i686` | `Baseline_NoPGO_Dynamic` | 2,548.17 | `0.00%` | `0.0%` | 32-bit stack-argument ABI indirect vtable calls + `memcpy` call. |
| `i686` | `LLVM_23_1_1_PGO_Full` | 1,499.78 | `+41.14%` | `100.0%` | Standard 2-stage LLVM PGO on `i686`. |
| `i686` | `HybridTrace_VP1_MemOpSize_16B_12B` | 2,004.34 | `+21.34%` | `51.9%` | Inline scalar load/store pairs for `16 B` and `12 B`. |
| `i686` | `HybridTrace_VP1_plus_VP2_FnPtrPromote` | 1,477.36 | `+42.02%` | **`102.1%`** | Per-site `fn_ptr` guard + direct inlining eliminates 32-bit stack frame setup. |
| `i686` | **`HybridTrace_VP1_plus_VP3_VTablePromote`** | **1,340.56** | **`+47.39%`** | **`115.2%`** | Single `vtable_ptr` guard specializes both trait calls (`9.3%` faster than `VP-2` and `10.6%` faster than LLVM PGO). |

Table 3 summarizes the generated `HybridTrace` certificate sizes and validation times:

| Certificate ID | Schema | Serialized Size (Bytes) | Validation Time ($\mu\text{s}$) | Verified |
| :--- | :--- | ---: | ---: | :---: |
| `VP1_MemOpSize_16B_AlignedOrUnaligned128` | `VP-MemOpSizeSpecialize` | 252 | `0.001` | `true` |
| `VP1_MemOpSize_12B_OverlappingHeadTail` | `VP-MemOpSizeSpecialize` | 265 | `0.001` | `true` |
| `VP2_IndirectCallPromote_StagePipeline_execute` | `VP-IndirectCallPromote` | 287 | `0.001` | `true` |
| `VP3_VTablePromote_StagePipeline_MultiMethod` | `VP-VTablePromote` | 540 | `0.002` | `true` |

## Boundaries

- **Volatile Memory Operations (`isvolatile = true`)**: Schema `VP-1` (`vp1_overlapping_head_tail_sound`) is restricted to non-volatile `memcpy` / `copy_nonoverlapping` / `copy_from_slice` operations (`isvolatile = false`). Overlapping head+tail loads read the middle bytes `[src + (S - 8) .. src + 8)` twice and writes `[dst + (S - 8) .. dst + 8)` twice, which is forbidden for MMIO / `read_volatile` / `write_volatile`.
- **Cross-DSO Duplicate VTables Without Unique Addresses**: When a `&dyn Trait` fat pointer crosses a dynamic library (`dylib` / `cdylib`) boundary where the dynamic linker does not coalesce duplicate `VTable` globals, `vtable_ptr == &VTable_HotImpl` may evaluate to `false` on a foreign DSO's duplicate vtable; however, this only causes a safe fallback to the `else` branch (indirect vtable call) and never compromises soundness.

## Evidence

- **Mechanized Lean `v4.34.1` proof development and benchmark artifacts**:
  - `support/ValueProfileSpecializationProofs.lean` (308 lines, `11` theorems, `0` `sorryAx`)
  - `support/run_value_profile_specialization.py`
  - `support/value_profile_specialization_benchmarks.csv`
  - `support/value_profile_certificates_and_metrics.json`
- **Primary upstream source citations**:
  - `rust-lang/llvm-project` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`):
    - `llvm/lib/Transforms/Instrumentation/PGOMemOPSizeOpt.cpp` (`MemOpSize` specialization pass)
    - `llvm/lib/Transforms/IPO/IndirectCallPromotion.cpp` (`PGOIndirectCallPromotion` and vtable comparison logic)

## Revalidation

Run both the Lean `v4.34.1` proof check and the benchmark harness:

```bash
anneal-lean-run --mode file --concurrency 4 -- elan run leanprover/lean4:v4.34.1 lean \
  reports/value-profile-specialization-and-hybridtrace-guard-certificates/support/ValueProfileSpecializationProofs.lean
python3 reports/value-profile-specialization-and-hybridtrace-guard-certificates/support/run_value_profile_specialization.py
```

Verify that `lean` exits with status `0` and zero `sorryAx`, and that `HybridTrace_VP1_plus_VP3_VTablePromote` captures $\ge 100\%$ of `LLVM_23_1_1_PGO_Full`'s speedup on both `x86_64` and `i686`.
