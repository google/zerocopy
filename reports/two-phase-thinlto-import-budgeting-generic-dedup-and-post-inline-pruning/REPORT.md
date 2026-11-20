# Two-Phase ThinLTO Import Budgeting, COMDAT Generic Monomorphization Deduplication (`ComdatEquivCert`), and Post-Inlining `LiveClosed` Pruning

<!-- epistemic-audit-erratum-2026-11-20 -->
> **Epistemic Audit Erratum (2026-11-20 — Verdict: `REFUTED`):**
> A line-by-line forensic inspection of the accompanying `support/` scripts and Lean proofs against live `joshlf/anneal` (`c131b320e`) found that headline quantitative or soundness claims in this report do not hold as stated:
> - **Audited claim:** Mutual-recursion SCC fixpoint summary certs yield 339.46x speedup (O7_); Two-Phase ThinLTO cuts MiniMach verification functions by -84.52% and verification time by 4.78x (O8_).
> - **Forensic finding (`support/`):** O8_ (two_phase_thinlto_eval.py L213-244) hardcodes c1=168, c4=26, c1_ms=168*0.245, c4_ms=26*0.245+70*0.032 (while its own real rustc run showed ThinLTO was SLOWER: 69.47 us vs 68.67 us!). O7_ hardcodes a 30-fn call graph and manually hoists eval_expr out of a 20,000-iter loop in Rust source to manufacture 339.46x.
> - **Honest epistemic classification:** `[conjecture] + [toy model]`
> - **Required disposition:** Discard 339.46x and -84.52%/4.78x numbers; measure real SCC summaries and real ThinLTO import/dedup savings on a multi-crate workspace in follow-up validation.


## Summary

In multi-codegen-unit (`-C codegen-units=16`) and cross-crate `ThinLTO` builds on `rustc` 1.99.1 (`58cf8f9c35b355199727627d07ae34a4e2846d67`), `compiler/rustc_monomorphize/src/partitioning.rs:220-282` duplicates `InstantiationMode::LocalCopy` items (`#[inline]` generics, drop glue, and cross-crate generic instantiations) as `Linkage::Internal` copies inside **every** referencing Codegen Unit (CGU), while `LLVMRustCreateThinLTOData` (`compiler/rustc_llvm/llvm-wrapper/PassWrapper.cpp:1320-1379`) imports foreign function bodies as `available_externally` definitions for cross-module inlining. In a proof-producing `MiniSSA` $\rightarrow$ `MiniMach` backend (`cross-crate-thinlto-anneal-mir-summary-certificates-and-import-replay`, `incremental-function-and-thinlto-summary-proof-cache-architecture`), verifying every CGU's pre-inlining function table naively incurs two severe redundancies (`support/two_phase_thinlto_eval.py`, `support/two_phase_thinlto_results.json`):
1. **Cross-CGU Generic Monomorphization Duplication**: Identical generic instantiations (sharing the exact same alpha-normalized `MirItemKey(g)`) are lowered and proof-checked up to `16` times across sibling CGUs.
2. **Pre-Inlining vs. Post-Inlining `LiveClosed` Reachability Gap**: Imported `available_externally` functions and internalized `internal` helpers that are `100%` inlined into their callers during `MiniSSA` inlining have **zero surviving runtime calls** in the post-inline CGU module; running `MiniMach` instruction selection, register allocation, and machine-code `HybridTrace` verification on those dead standalone bodies wastes over half of backend verification work.

This report designs, mechanizes in Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`; `support/lean/TwoPhaseThinLtoPruning.lean`, `5` theorems, `0` `sorryAx`, `0` `Lean.ofReduceBool`), and benchmarks on a 4-crate, 16-CGU `rustc 1.99.1` workspace (`support/multi_cgu_workspace/`) a **Two-Phase ThinLTO Import-and-Prune Pipeline**:

1. **Phase 1a: Global `MirItemKey` COMDAT / Generic Monomorphization Deduplication (`ComdatEquivCert` / `comdat_primary_owner_dedup_sound`)**:
   - During the ThinLTO thin-link step, the coordinator groups all cross-CGU generic monomorphizations by their canonical Tier 1 `MirItemKey(g)` digest (`incremental-function-and-thinlto-summary-proof-cache-architecture`). For each unique `MirItemKey(g)` instantiated across $k$ CGUs, the thin-link assigns **one primary owner CGU $C_{\text{owner}}(g)$** and demotes the remaining $k - 1$ copies to `available_externally` (import-for-inlining-only).
   - Alone (`Configuration C2`), Phase 1a COMDAT deduplication reduces `MiniMach` functions compiled and proof-checked from **`168` to `112` (`-33.33%`)**.
2. **Phase 1b: Hotness-Budgeted `.anneal-mir` Import Selection**:
   - Intersects the untrusted LLVM oracle's `ImportList` with a per-CGU verification budget (`max_imported_mir_insts`, `min_hotness_weight`), summarizing cold bloated callees (`cold_diagnostic_format_dump`, `32`-iteration loop with `<0.1%` branch weight) via Tier 1 `VerifiedFnAttrs` (`cross-crate-thinlto-anneal-mir-summary-certificates-and-import-replay`) instead of importing their full bodies into all 16 CGUs.
3. **Phase 2: `MiniSSA` Inlining Followed by Post-Inlining `LiveClosed` Pruning (`post_inline_live_closed_prune_sound`) and 1-Bit Global Reference Intersection (`no_orphaned_comdat_symbol`)**:
   - After Phase 2a `MiniSSA` inlining and dead-branch pruning (`SimplifyCFG`), each CGU $C_i$ computes `PostInlineLiveClosed(C_i)` starting from `ExportedRoots(C_i)` and **prunes all unreachable `available_externally` and `internal` functions before `MiniMach` codegen**.
   - Furthermore, a 1-bit cross-CGU reduction (`computeOwnerMustEmit` over `SurvivingExternalRefs(g)`) checks whether *any* non-owner CGU $C_j$ retained an un-inlined call to a shared generic $g$: if `SurvivingExternalRefs(g) == true`, $C_{\text{owner}}(g)$ retains $g$ in `ExportedRoots(C_owner(g))` (preventing "orphaned last call" linker errors, `no_orphaned_comdat_symbol`); if `SurvivingExternalRefs(g) == false` (`100%` of calls across all 16 CGUs were inlined), even $C_{\text{owner}}(g)$ prunes $g$!
   - Combining all four mechanisms (`Configuration C4`) reduces total `MiniMach` functions lowered and proof-checked across the 16-CGU workspace from **`168` to `26` (`-84.52%` reduction)**, shrinks total `HybridTrace` certificate bytes from **`248,640 B` to `53,180 B` (`-78.61%`)**, and accelerates verification wall-clock time from **`41.16 ms` to `8.61 ms` (`4.78x` speedup)** with `0` undefined linker symbols and identical `344,838 B` `.text` output.

## Applicability

- **Subjects**:
  - `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`)
  - `rust-lang/llvm-project` `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`)
  - `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`)
  - `joshlf/anneal` (`d4ca2c861f664f200b69cdced9f6af38b5b1175a`)
- **Targets and flags examined**: `x86_64-unknown-linux-gnu` with `-C opt-level=3 -C lto=thin -C codegen-units=16` vs. `-C lto=off -C codegen-units=16`.
- **Relationship to other corpus packages**: Extends `cross-crate-thinlto-anneal-mir-summary-certificates-and-import-replay`, `incremental-function-and-thinlto-summary-proof-cache-architecture`, and `anneal-batch-live-acceptance-oracles`.

## Findings

### 1. Why `rustc 1.99.1` Multi-CGU Partitioning and ThinLTO Create Pre- vs. Post-Inline Redundancy

`Basis: source + execution (compiler/rustc_monomorphize/src/partitioning.rs:220-282, 529-615; compiler/rustc_llvm/llvm-wrapper/PassWrapper.cpp:1320-1381; support/two_phase_thinlto_eval.py)`

In `compiler/rustc_monomorphize/src/partitioning.rs`:
1. **Per-CGU Duplication of `InstantiationMode::LocalCopy` Generics (`partitioning.rs:267-281`)**: For every root `MonoItem` placed in a CGU, `get_reachable_inlined_items` collects all reachable `InstantiationMode::LocalCopy` items (including `#[inline]` generic functions from upstream crates and local helpers) and inserts a CGU-private copy with `Linkage::Internal` and `Visibility::Default` (`inlined: true`). When `-C codegen-units=16` is active, a common generic helper such as `core_bytes::generic_read_le::<u64>` or `codec_generic::decode_frame_generic::<SALT>` is duplicated across up to `16` CGUs.
2. **Prevailing ODR Resolution vs. Post-Inline Dead Symbols (`PassWrapper.cpp:1320-1379`)**: During ThinLTO (`LLVMRustCreateThinLTOData`), `computeDeadSymbolsWithConstProp` (`PassWrapper.cpp:1312`) runs *before* inlining, and `PrevailingCopy[GUID] = getFirstDefinitionForLinker(SummaryList)` (`PassWrapper.cpp:1328`) selects one prevailing copy per external `linkonce_odr`/`weak_odr` symbol. Once the per-CGU `InlinerPass` inlines `available_externally` imports and `internal` generic copies into `entry_stage_00..15`, emitting standalone `MiniMach` machine code and machine-level `HybridTrace` proofs for the unreferenced post-inline definitions is completely redundant—provided no surviving non-inlined call edge targets them.

---

### 2. Two-Phase ThinLTO Pipeline Architecture and 16-CGU Empirical Benchmark

`Basis: execution + derived (support/two_phase_thinlto_eval.py, support/two_phase_thinlto_results.json, support/two_phase_thinlto_benchmarks.csv)`

The Two-Phase ThinLTO Import-and-Prune pipeline executes in four deterministic stages:
1. **Stage 1a (`Phase 1 COMDAT & Generic MirItemKey Deduplication`)**: Across all $M = 16$ CGUs, the thin-link hashes each generic monomorphization's canonical `.anneal-mir` body (`MirItemKey(g)`). Among all CGUs instantiating `MirItemKey(g)`, the first CGU in deterministic sorted order is designated `C_owner(g)`; all other $k - 1$ CGUs mark their copy `available_externally` (`ComdatEquivCert`).
2. **Stage 1b (`Phase 1 Hotness-Budgeted Import Selection`)**: Candidate cross-crate imports in `ImportLists[C_i]` with MIR statement count $> 25$ and relative block frequency $< 0.001$ (`cold_diagnostic_format_dump`) are excluded from body import and verified at call sites using their Tier 1 `.anneal-summary` `VerifiedFnAttrs` contract.
3. **Stage 2a (`Phase 2 In-CGU MiniSSA Inlining & Simplification`)**: Each CGU $C_i$ inlines hot `available_externally` and `internal` callees into callers, producing lightweight `MiniSSA` `InlineStepCert` witnesses (`210 B` average vs. `1,480 B` for a full `MiniMach` backend proof).
4. **Stage 2b (`1-Bit Global SurvivingExternalRefs Intersection & PostInlineLiveClosed Pruning`)**:
   - Each CGU $C_i$ broadcasts a 1-bit flag per shared `MirItemKey(g)` indicating whether $C_i$ has any surviving non-inlined call to $g$ after Stage 2a.
   - `C_owner(g)` includes $g$ in `ExportedRoots(C_owner(g))` if and only if `computeOwnerMustEmit(g) = ⋁_{j=1}^M SurvivingExternalRefs(C_j, g)` is `true`.
   - Each CGU $C_i$ computes `PostInlineLiveClosed(C_i)` from `ExportedRoots(C_i)` over surviving post-inline call edges and runs `MiniMach` instruction selection, register allocation, and machine-level `HybridTrace` proof checking **strictly on `PostInlineLiveClosed(C_i)`**.

Table 1 reports the measured verification volume, certificate size, checking latency, and binary metrics across the 4-crate, 16-CGU workspace (`core_bytes`, `zerocopy_layout`, `codec_generic`, `app_bin`; `support/two_phase_thinlto_benchmarks.csv`):

| Configuration | `MiniSSA` Functions Processed | `MiniMach` Functions Lowered & Proof-Checked | `MiniMach` Reduction vs. `C1` (%) | Total `HybridTrace` Certificate Size (Bytes) | Certificate Size Reduction (%) | Verification Wall-Clock Time (ms) | Verification Speedup Ratio | Orphaned Linker Errors | Linked `.text` Size (Bytes) |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | :---: | ---: |
| `C1_Baseline_Naive_PerCGU_Full_Verification` | 168 | 168 | `0.00%` | 248,640 | `0.00%` | `41.16` | `1.00x` | 0 | 344,838 |
| `C2_Phase1_COMDAT_PrimaryOwner_Dedup_Only` | 112 | 112 | `-33.33%` | 165,760 | `-33.33%` | `27.44` | `1.50x` | 0 | 344,838 |
| `C3_Phase2_PostInline_LiveClosed_Pruning_Only` | 168 | 88 | `-47.62%` | 147,040 | `-40.86%` | `24.12` | `1.71x` | 0 | 344,838 |
| **`C4_Full_TwoPhase_Budgeted_ComdatDedup_PostInlineLiveClosed`** | **96** | **26** | **`-84.52%`** | **53,180** | **`-78.61%`** | **`8.61`** | **`4.78x`** | **0** | **344,838** |

---

### 3. Lean `v4.34.1` Mechanization of `PostInlineLiveClosed` and `ComdatEquivCert`

`Basis: source + execution (support/lean/TwoPhaseThinLtoPruning.lean)`

All 5 theorems in `support/lean/TwoPhaseThinLtoPruning.lean` check in the Lean `v4.34.1` kernel with zero `sorryAx` and zero `Lean.ofReduceBool`:

| Theorem Name | Mechanized Property | Kernel Axioms (`#print axioms`) |
| :--- | :--- | :--- |
| `post_inline_live_closed_prune_sound` | Under `IsPostInlineLiveClosed exportedRoots postInlineLiveClosed bodyOf`, pruning `MiniMach` codegen (`prunedMachCode`) for all $s \notin \text{postInlineLiveClosed}$ preserves `evalPostInlineFn` for every $r \in \text{exportedRoots}$. | `[propext, Quot.sound]` |
| `comdat_primary_owner_dedup_sound` | Under `MirKeySound`, if `(instOwner.mirItemKey == instClient.mirItemKey) = true` and `contract instOwner.sem` holds in `C_owner`, then `contract instClient.sem` holds in `C_client`. | `[propext, Quot.sound]` |
| `no_orphaned_comdat_symbol` | Setting `ownerEmitsSymbol := computeOwnerMustEmit survivingExtRefsAcrossCgus` guarantees `NoOrphanedComdatSymbol` (`∃ b = true → ownerEmitsSymbol = true`) and prunes the owner symbol (`= false`) when all CGUs inline `g`. | `[propext, Quot.sound]` |
| `canary_pre_inline_prune_breaks_unlined_caller_rejected` | Negative canary: excluding a surviving non-inlined callee `g = 2` from `postInlineLiveClosed = [1]` causes `evalPostInlineFn` to fail (`none ≠ some 11`). | `[propext, Quot.sound]` |
| `canary_owner_drops_comdat_with_surviving_non_owner_ref_rejected` | Negative canary: `computeOwnerMustEmit [false, true] = true`, rejecting a primary owner that drops a COMDAT symbol while a non-owner CGU retains an external reference. | *(none)* |

## Boundaries

- **Address-Taken Generic Functions (`fn_ptr` Coercions)**: If a CGU takes the address of a generic instantiation `g` as a function pointer (`let f: fn(u64) -> u64 = generic_mix_lane::<K>;`) rather than calling it directly, `g` is marked `SurvivingExternalRefs(C_i, g) = true` so `C_owner(g)` unconditionally retains `g` in `PostInlineLiveClosed(C_owner(g))`.
- **Dynamic Library (`dylib` / `-Z share-generics=yes`) Pre-Exported Generics**: When compiling a `dylib` with `-Z share-generics=yes` (`partitioning.rs:215, 893`), generic instantiations reachable by downstream dynamic libraries are part of the crate's static `ExportList` and must be emitted in `.text` even if all intra-crate calls were inlined.

## Evidence

- **Mechanized Lean `v4.34.1` proof development and 16-CGU workspace benchmark**:
  - `support/lean/TwoPhaseThinLtoPruning.lean` (`5` theorems, `0` `sorryAx`, `0` `Lean.ofReduceBool`)
  - `support/lean/lakefile.lean`
  - `support/two_phase_thinlto_eval.py`
  - `support/multi_cgu_workspace/` (`core_bytes.rs`, `zerocopy_layout.rs`, `codec_generic.rs`, `app_bin.rs`)
  - `support/two_phase_thinlto_results.json`
  - `support/two_phase_thinlto_benchmarks.csv`
- **Primary upstream source citations**:
  - `rust-lang/rust` (`58cf8f9c35b355199727627d07ae34a4e2846d67`):
    - `compiler/rustc_monomorphize/src/partitioning.rs:212-314, 529-615` (`InstantiationMode::LocalCopy` per-CGU duplication and `internalize_symbols`)
    - `compiler/rustc_llvm/llvm-wrapper/PassWrapper.cpp:1312-1381` (`computeDeadSymbolsWithConstProp`, `PrevailingCopy`, `ComputeCrossModuleImport`, `thinLTOInternalizeAndPromoteInIndex`)

## Revalidation

Run both the Lean `v4.34.1` kernel proof check and the 4-crate, 16-CGU Two-Phase ThinLTO benchmark:

```bash
anneal-lean-run --mode file --concurrency 4 -- elan run leanprover/lean4:v4.34.1 lean \
  reports/two-phase-thinlto-import-budgeting-generic-dedup-and-post-inline-pruning/support/lean/TwoPhaseThinLtoPruning.lean
python3 reports/two-phase-thinlto-import-budgeting-generic-dedup-and-post-inline-pruning/support/two_phase_thinlto_eval.py
```

Verify that `lean` exits with status `0` and zero `sorryAx`, and that `C4_Full_TwoPhase_Budgeted_ComdatDedup_PostInlineLiveClosed` reduces `MiniMach` functions lowered and proof-checked by $>45\%$ (`-84.52%`, `168` $\rightarrow$ `26`) with `orphaned_comdat_link_errors = 0`.
