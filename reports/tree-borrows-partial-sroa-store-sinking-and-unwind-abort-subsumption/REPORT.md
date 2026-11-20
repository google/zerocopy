# Tree Borrows Partial SROA, Cleanup-Pad Store Sinking, and Unwind-to-Abort Subsumption in Lean 4

## Summary

Aggregate and call-boundary optimizations in a drop-in verified Rust compiler sit directly on the fault line between **Tree Borrows** aliasing permissions (Villani et al., PLDI 2025, DOI `10.1145/3729264`; `rust-lang/miri@7e679961edcfe2c526f19153bb8b03de346efa5c`, `src/borrow_tracker/tree_borrows/perms.rs`) and **exceptional unwinding** (`-C panic=unwind` vs. `-C panic=abort`). Empirical inspection of `rustc 1.99.1` (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`) LLVM IR across `libcore` and `std`-linked binaries (`rustc-postcleanup-mir-and-llvm-poison-freeze-ground-truth-census`) shows that `invoke`/cleanup edges jump from **`0.18%`** of functions in `no_std` `libcore` to **`41.8%`** in `std`-linked `anneal-audit`. Across those call boundaries, three interactions break naive Boolean escape analyses and local-granular SROA passes:

1. **Hybrid Struct Partial SROA Under `UnsafeCell` and Whole-Struct Provenance:** Promoting a scalar field `(a, f)` of a hybrid struct `S { fast: u64, lock: UnsafeCell<u64> }` into an SSA register (either via `.fullSplit` when `(a, f)` is never borrowed or via write-through `.sharedReadPromote` when `&S` / `&s.fast` is shared across external calls) is sound only when `(a, f)` is `Freeze` (`!isUnsafeCell`), no whole-struct raw pointer (`&raw mut s` / `&raw const s`) enables `container_of!`-style cross-field pointer offset into `(a, f)`, and sibling `&UnsafeCell<T>` fields carry Miri's interior-mutable `PermissionPriv::Cell` (`TbPerm.cell`) state so foreign writes through aliased `&UnsafeCell<T>` pointers do not spuriously fault `.tbUb`.
2. **Dead-on-Normal-Return Store Sinking Into Cleanup Landing Pads:** Sinking a store `s.f = v` across a potentially unwinding `Call` into its `panic=unwind` landing pad when the normal return block immediately overwrites `s.f` relies on **asymmetric refinement** (`tgt` may eliminate UB present in `src` when `v` reads an uninitialized register on a non-unwinding execution) and requires proving no pointer to `(a, f)` can be observed by the callee before unwinding.
3. **`-C panic=abort` Subsumption of `-C panic=unwind` Verification Obligations:** Rather than duplicating function contracts across both `PanicMode`s, proving that a body has `noCatchUnwind = true` and side-effect-free cleanup blocks establishes that `panic=abort` preserves exact normal-return traces and return values, introduces zero new errors or Tree Borrows UB, and agrees on pre-abort trace prefixes whenever `panic=unwind` finishes unwinding.

> **Formal Scope (`[kernel-checked proof]`, `VrustcFormal.F1_2`):** In Lean 4 (`support/F1_2_MirTreeBorrows_PartialSroa_Unwind_Proof.lean`, `5,878` lines, `110` theorems = `14` public + `96` private, zero imports beyond `Init`, zero `sorry`, axioms strictly `{propext, Quot.sound}`), we formalize a fuel-indexed core-MIR operational semantics parameterized by `PanicMode` (`unwind` vs. `abort`) with 5-state per-field Tree Borrows permissions (`cell`, `reserved conflicted`, `active`, `frozen`, `disabled`), sub-place `outside_perm` (`ptrInScope`) vs. whole-struct `PtrOffset` provenance, and call-scoped protectors released on both normal return and unwind, and prove soundness of three decidable translation-validation certificate checkers (`partial_sroa_refinement`, `store_sink_to_cleanup_refinement`, and `unwind_to_abort_subsumption`), accompanied by `4` positive non-vacuity canaries and `7` kernel-checked counterexamples and Miri Tree Borrows faithfulness theorems. Independently verified across `Lean 4.28.0-rc1`, `Lean 4.34.1`, `Lean 4.35.0`, and external Rust kernel `nanoda_bin 0.4.19` (`2,505` declarations checked in `1.36s` with `0` errors). See **Honest Scope & Non-Claims (`VrustcFormal.F1_2`)** in `## Boundaries` for exact model boundaries (standalone AST, 2-level borrow tree, zero-initialized `UInt64` fields, scripted non-recursive callees, frame-local `initArgs` assumption, and checker incompleteness).

---

## Applicability

- **Mechanized Proof Artifact:** `support/F1_2_MirTreeBorrows_PartialSroa_Unwind_Proof.lean` (`5,878` lines, `273,686` bytes, SHA-256 `ae2132de4735bf32c44b004ccdf4b28440fd1123406e5920d491fa85d1f2a919`; `262` total declarations = `152` public + `110` private Stage 4 helpers; `110` total theorems = `14` public + `96` private).
- **Frozen Statement Integrity:** Stripping the `110` strictly `private` Stage 4 helper declarations (`L1107–5191`) and replacing the three core theorem proof scripts with `sorry` reproduces the pre-proof frozen contract (`1,689` lines, `72,474` bytes, SHA-256 `b7f148bb350eedb8d6e14d9dfc084b740fc22814516c66f15be9e6b9c5a1d92c` recorded in `support/F1_2_FROZEN.sha256`) byte-for-byte (`72,474 / 72,474` bytes identical).
- **Multi-Kernel Verification:** Verified synchronously (`-DElab.async=false -Ddebug.skipKernelTC=false`) on `Lean 4.28.0-rc1` (`leanprover/lean4@3b0f2862196c6a8af9eb0025ee650252694013dd`), `Lean 4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`), and `Lean 4.35.0` (`leanprover/lean4@eb6cafb7290e8bd5f2937522d8d804f58f02bafc`), and exported via `lean4export` (`leanprover/lean4export@5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe`, format `3.1.0`) into the independent Rust type-checker `nanoda_bin 0.4.19` (`ammkrn/nanoda_lib@0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929`).
- **Semantic Reference Points:** Tree Borrows permission transitions cross-checked against Villani et al. (PLDI 2025, DOI `10.1145/3729264`) and `rust-lang/miri@7e679961edcfe2c526f19153bb8b03de346efa5c` (`src/borrow_tracker/tree_borrows/perms.rs`); purity/axiom constraints aligned with `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`trusted/lean/TrustedBoundary.lean`).

---

## Findings

### 1. Operational Semantics: 5-State Tree Borrows, Sub-Place Provenance, and `PanicMode` Unwinding

`Basis: formal proof (Lean 4 operational model in support/F1_2_MirTreeBorrows_PartialSroa_Unwind_Proof.lean, lines 1–1106)`

To capture the real failure modes that Boolean "borrowed/unborrowed" models erase, `VrustcFormal.F1_2` models struct allocations as arrays of `FieldMeta` cells carrying both scalar storage (`val : UInt64`), `isUnsafeCell : Bool`, and per-field borrow trees (`nodes : List BorrowNode`) under a 5-state permission lattice:

| Component | Mechanized Semantics in `VrustcFormal.F1_2` | Why Simpler Surrogates Fail |
| :--- | :--- | :--- |
| **`TbPerm` (`5` states)** | `.cell` (`&UnsafeCell<T>`), `.reserved (conflicted : Bool)` (`&mut T`), `.active`, `.frozen` (`&T`), `.disabled` | A 4-state automaton omitting `.cell` treats foreign writes through one `&UnsafeCell<T>` as disabling sibling `&UnsafeCell<T>` tags (`B1`), falsely triggering `.tbUb` on valid interior-mutable Rust code. |
| **Protected `&mut UnsafeCell<T>` (`tbForeignStep`)** | Checks `if isProtected then ...` *before* `if isUnsafeCell then some p`: protected `.reserved _` transitions to `.reserved true` on foreign reads and `none` (`.tbUb`) on foreign writes. | Even `&mut UnsafeCell<T>` carries `noalias` while its function-entry protector is live (`Miri` `ReservedFrz`); checking `isUnsafeCell` first silently permits protected aliasing violations (`B2`). |
| **`conflicted` Flag Scope (`tbChildStep`)** | `.write` on `.reserved conflicted` rejects (`none`) when `conflicted && isProtected`, and transitions to `some .active` once `isProtected = false`. | In Miri `perms.rs`, `conflicted` blocks child activation *only* while the protector is active; blocking post-return activation breaks standard two-phase borrow patterns (`B3`). |
| **Sub-Place vs. Root Provenance (`ptrInScope`)** | Field borrows (`takeFieldPtr`) carry `scope := .singleField f` (`ptrInScope` false on sibling fields `f' ≠ f`), whereas `takeRootRawPtr` / `takeRootSharedRef` carry `.wholeAlloc`, allowing `ptrOffset` across fields. | Captures both why `&mut s.lock` never aliases `s.fast` (`outside_perm`) and why `&raw mut s` followed by `ptrOffset` breaks field SROA (`ce_root_raw_ptr_breaks_partial_sroa`). |
| **`PanicMode` (`unwind` vs. `abort`)** | On `callMayUnwind` returning `.calleesUnwound payload`, `releaseProtectors` runs first; `.abort` terminates immediately with `.aborted payload`, whereas `.unwind` branches to `unwindTgt` (or propagates `.unwound payload`). | Models both protector release along exceptional edges and `catchUnwind` recovery vs. cleanup-pad propagation. |

### 2. Statement-First Pre-Freeze Blind Review: Four Real Tree Borrows Faithfulness Defects Caught Before Proving

`Basis: formal proof (independent Stage 2 adversarial review prior to SHA-256 freeze b7f148bb350e)`

Running an independent adversarial review on the statement file *before* freezing its SHA-256 caught four concrete Miri `tree_borrows/perms.rs` faithfulness defects and one theorem-completeness gap—each locked permanently by kernel-checked regression witnesses in the frozen contract:

| Defect ID | Pre-Freeze Bug | Impact If Uncaught | Fix Frozen in `b7f148bb350e` + Regression Witness |
| :--- | :--- | :--- | :--- |
| **`B1` (Critical Vacuity)** | `takeFieldPtr ... .sharedRef` assigned `.reserved false` instead of `.cell` on `isUnsafeCell = true` fields, and `takeRootSharedRef` assigned `.frozen` uniformly even to `UnsafeCell` fields. | Calling a callee twice with `&s` (when `s` contains an `UnsafeCell` sibling) or passing two aliased `&s.cell` pointers faulted `.error .tbUb` in `src`, making `refines` hold *vacuously* on hybrid structs! | Added `TbPerm.cell` (`PermissionPriv::Cell`), used `.cell` on `isUnsafeCell` shared borrows, and proved `canary_b1_cell_aliased_and_two_call_hybrid_ok` (`src` and `tgt` both return `.ok ([7, 108, 9, 109], .ret 49)`). |
| **`B2` (`ReservedFrz` Precedence)** | `tbForeignStep` returned `some p` whenever `isUnsafeCell = true` before checking `isProtected`. | Protected `&mut UnsafeCell<T>` failed to fault `.tbUb` on foreign writes and failed to set `conflicted := true` on foreign reads during a protected call. | Checked `isProtected` before `isUnsafeCell` in `tbForeignStep`; locked by conjuncts 1–2 of `ce_b2_b3_b4_tree_borrows_faithfulness`. |
| **`B3` (`conflicted` Lifetime)** | `tbChildStep .write (.reserved true)` unconditionally returned `none` even after `releaseProtectors` cleared `protector := none`. | Valid post-call writes through a formerly protected two-phase `&mut` borrow spuriously faulted `.tbUb`. | Parameterized `tbChildStep` by `(isProtected : Bool)` so `.reserved true` activates cleanly once `isProtected = false`; locked by conjunct 3 of `ce_b2_b3_b4_tree_borrows_faithfulness`. |
| **`B4` (`ptrInScope` on Activation)** | `activateProtectorOne` ran `tbForeignAccessField .read` across *every* field of `alloc` instead of filtering by `ptrInScope ptr fIdx`. | Passing `&mut s.f0` to a call triggered an implicit foreign read on sibling `s.f1`, freezing active `&mut s.f1` borrows despite sub-place disjointness. | Guarded `activateProtectorOne` with `ptrInScope ptr fIdx`; locked by conjunct 4 of `ce_b2_b3_b4_tree_borrows_faithfulness`. |
| **`N5` (4th Conjunct on Theorem 3)** | `unwind_to_abort_subsumption` stated normal-return iff and unwind-trace agreement, omitting `.abort = .error e → .unwind = .error e`. | Left implicit that `-C panic=abort` never introduces new runtime errors/UB absent from `-C panic=unwind`. | Added explicit 4th error-subsumption conjunct to `unwind_to_abort_subsumption` prior to freeze. |

### 3. The Three Certified Optimizations and Their Invariants (`110` Total Theorems)

`Basis: formal proof (support/F1_2_MirTreeBorrows_PartialSroa_Unwind_Proof.lean, lines 1107–5878)`

1. **Field-Granular Partial SROA (`partial_sroa_refinement`, `L5199`):**
   - `checkPartialSroaCert` validates promotion of a single `(cert.alloc, cert.field)` into fresh scalar register `cert.ssaReg` on an acyclic entry block (`!hasPredecessor src 0`) in two modes:
     - **`.fullSplit`:** Zero pointers can ever target `(alloc, field)` (`noFieldBorrow` and `noRootPtr` across all blocks). Reads/writes to `(alloc, field)` rewrite directly to `ssaReg` copies/assignments, eliminating memory traffic completely.
     - **`.sharedReadPromote`:** Requires `(alloc, field)` to be `Freeze` (`!fMeta.isUnsafeCell`), forbids mutable/raw borrows of `(alloc, field)` and raw root pointers (`&raw s`), while permitting shared `&s` (`takeRootSharedRef`) and `&s.field` (`takeFieldPtr ... .sharedRef`) borrows across unwinding calls! Writes become write-through (`writeField` + `assignReg ssaReg`), while reads come straight from `ssaReg`.
   - **Relational Invariant (`SroaStateRel`):** Connects `src` and `tgt` states via `HeapAgreeExcept`, `FieldNoChildrenInv` (for `.fullSplit`), and `HeapSharedInv` / `SharedChildrenInv` (proving every live child tag on a `.sharedReadPromote` field is `.frozen`, so foreign reads never mutate `val` and foreign writes fault `.tbUb` identically in both `src` and `tgt`!). Unlike store sinking, `partial_sroa_refinement` proves exact `ExecResult` equality (`tgtRes = srcRes`, discharging `refines` via `refines_of_eq`).

2. **Cleanup-Pad Store Sinking Across Potentially-Unwinding Calls (`store_sink_to_cleanup_refinement`, `L5268`):**
   - `checkStoreSinkCert` certifies sinking `s.(alloc, field) = op` at `stmtIdx` in `callBlock` across pure/disjoint suffix statements and `callMayUnwind callee ptrArgs retReg normTgt (some cleanTgt)` into the head of unique-predecessor landing pad `cleanTgt` whenever `normTgt`'s first statement unconditionally overwrites `(alloc, field)` (`writeField alloc field overwriteOp` with `valOpDisjointOptReg retReg overwriteOp` handled cleanly).
   - **Strict Asymmetric Refinement:** Independent Stage 5 kernel probe confirmed that `store_sink_to_cleanup_refinement` genuinely exercises strict `refines` (`tgtRes ≠ srcRes`): if the sunk `op` reads an uninitialized scalar register (`valRegs[r] = none`) and `callee` returns normally, `src` faults `.error .tbUb` before reaching the call whereas certified `tgt` skips the dead store on the normal path and returns `.ok (tr, .ret v)`.

3. **Unwind-to-Abort Verification Subsumption (`unwind_to_abort_subsumption`, `L5315`):**
   - `checkUnwindToAbortCert` verifies partitioning of CFG blocks into `normalBlocks` (`noCatchUnwind`, unwind targets land strictly in `cleanupBlocks`) and `cleanupBlocks` (disjoint from `normalBlocks`, `entry = 0` normal, cleanup statements side-effect-free with zero `emitTrace` and zero `callMayUnwind`, and cleanup terminators never jumping back to `normalBlocks` or returning `.ret`).
   - Proves all four conjuncts across arbitrary `callees`, `args`, and `fuel`:
     1. Exact normal-return equivalence: `execMir .abort ... = .ok (tr, .ret v) ↔ execMir .unwind ... = .ok (tr, .ret v)`.
     2. Panic non-recovery: `execMir .unwind ... = .ok (trU, .unwound p) → ∀ trA v, execMir .abort ... ≠ .ok (trA, .ret v)`.
     3. Trace/payload agreement on completed unwinds: if `.unwind` yields `.ok (trU, .unwound p)` and `.abort` yields `.ok (trA, outA)`, then `outA = .aborted p ∧ trA = trU`.
     4. One-way fault freedom: `execMir .abort ... = .error e → execMir .unwind ... = .error e`.

| # | Public Theorem (`VrustcFormal.F1_2`) | Role | Kernel Axioms |
| :---: | :--- | :--- | :--- |
| 1 | `partial_sroa_refinement` | Core soundness of `.fullSplit` + `.sharedReadPromote` Partial SROA | `[propext, Quot.sound]` |
| 2 | `store_sink_to_cleanup_refinement` | Core soundness of sinking overwritten stores into `panic=unwind` landing pads | `[propext, Quot.sound]` |
| 3 | `unwind_to_abort_subsumption` | Core 4-conjunct `-C panic=abort` ↔ `-C panic=unwind` verification subsumption | `[propext, Quot.sound]` |
| 4 | `canary_partial_sroa_hybrid_struct_accepted` | Non-vacuity: hybrid `{Freeze, UnsafeCell}` struct promoted across shared `&s` call | `[propext, Quot.sound]` |
| 5 | `canary_store_sink_to_cleanup_accepted` | Non-vacuity: store sunk into landing pad agrees on both normal return (`99`) and unwind (`42`) | `[propext, Quot.sound]` |
| 6 | `canary_unwind_to_abort_subsumption_accepted` | Non-vacuity: cleanup-pad body satisfies `checkUnwindToAbortCert = true` | `[propext, Quot.sound]` |
| 7 | `ce_root_raw_ptr_breaks_partial_sroa` | Sharpness: `&raw mut s` + `ptrOffset` cross-field write breaks naive SROA (`check = false`) | `[propext, Quot.sound]` |
| 8 | `ce_unsafecell_breaks_partial_sroa` | Sharpness: `.sharedReadPromote` on `UnsafeCell` field fails (`check = false`, `99 ≠ 10`) | `[propext, Quot.sound]` |
| 9 | `ce_unsound_store_sink_observed_by_callee` | Sharpness: sinking store when callee reads `&s.f` changes observable trace (`[0] ≠ [77]`) | `[propext, Quot.sound]` |
| 10 | `ce_catch_unwind_breaks_abort_subsumption` | Sharpness: `catchUnwind` recovers `.ret 55` under `unwind` vs. `.aborted 9` under `abort` | `[propext, Quot.sound]` |
| 11 | `ce_observable_cleanup_breaks_abort_subsumption` | Sharpness: `emitTrace 999` in cleanup pad breaks trace equality (`[1] ≠ [1, 999]`) | `[propext, Quot.sound]` |
| 12 | `ce_tb_protector_and_subplace_ub` | Tree Borrows witness: protected foreign write faults `.tbUb`; out-of-scope `ptrOffset` faults `.tbUb` | `[propext, Quot.sound]` |
| 13 | `canary_b1_cell_aliased_and_two_call_hybrid_ok` | `B1` regression: aliased `&UnsafeCell` writes + two-call `&s` hybrid struct succeed (`0` `.tbUb`) | `[propext, Quot.sound]` |
| 14 | `ce_b2_b3_b4_tree_borrows_faithfulness` | `B2`–`B4` regression: protected `&mut UnsafeCell`, post-release activation, sub-place protector | `[propext, Quot.sound]` |

### 4. Multi-Kernel Verification Receipts (`Lean 4.28.0-rc1` / `4.34.1` / `4.35.0` + `nanoda_bin 0.4.19`)

`Basis: execution (synchronous single-threaded kernel replay and external NDJSON re-checking)`

| Toolchain / Kernel | Pin | Mode / Workload | Exit | Wall-Clock | Peak RSS |
| :--- | :--- | :--- | :---: | ---: | ---: |
| **Lean 4.28.0-rc1** | `3b0f2862196c` | `lean -DElab.async=false -Ddebug.skipKernelTC=false` (`0` errors, `0` warnings) | `0` | **`32.91 s`** | **`834.4 MiB`** |
| **Lean 4.34.1** | `5045d0056413` | `lean -DElab.async=false -Ddebug.skipKernelTC=false` (`0` errors) | `0` | **`25.09 s`** | **`866.7 MiB`** |
| **Lean 4.35.0** | `eb6cafb7290e` | `lean -DElab.async=false -Ddebug.skipKernelTC=false -o F1_2.olean` (`0` errors) | `0` | **`23.31 s`** | **`914.8 MiB`** |
| **`lean4export 3.1.0`** | `5a9a355dc6c5` | Export all `14` public theorems (`496,922` lines, `26.17 MB` NDJSON) | `0` | **`1.54 s`** | **`752.1 MiB`** |
| **`nanoda_bin 0.4.19`** | `0da9f98feadd` | Independent Rust kernel check: **`Checked 2505 declarations with no errors`** | `0` | **`1.36 s`** | **`55.1 MiB`** |

Across `5,878` lines of Lean (`110` theorems), `nanoda_bin 0.4.19` re-verifies the entire exported proof DAG (`2,505` declarations) in **`1.36 s` and `55.1 MiB` RSS** (`17.1x` faster and `16.6x` leaner than `Lean 4.35.0` elaboration+kernel), confirming that multi-thousand-line compiler translation-validation proofs remain cheap to audit under an independent memory-safe kernel.

---

## Boundaries

### Honest Scope & Non-Claims (`VrustcFormal.F1_2`)

- **What Is Mechanically Proved (`[kernel-checked proof]`):** Within the standalone, zero-import Lean 4 module `VrustcFormal.F1_2` (`5,878` lines; `14` public and `96` private theorems; synchronous Lean 4 kernel check `-DElab.async=false -Ddebug.skipKernelTC=false` and independent external Rust kernel check via `lean4export 3.1.0` + `nanoda_bin 0.4.19`, `2,505` declarations checked with `0` errors; axioms strictly `{propext, Quot.sound}`, zero `sorry`), we formalize a fuel-indexed core-MIR operational semantics parameterized by `PanicMode` (`unwind` vs. `abort`) over per-field struct allocations with 5-state Tree Borrows permissions (`cell`, `reserved conflicted`, `active`, `frozen`, `disabled`), sub-place vs. whole-struct provenance (`outside_perm` vs. `container_of!` `PtrOffset`), and call-scoped protectors released on both normal return and unwind, and prove soundness of three decidable translation-validation certificate checkers:
  1. `partial_sroa_refinement`: field-granular scalar promotion (`fullSplit` and write-through `sharedReadPromote` across `&T`/`&s` borrows, including hybrid structs with mutated `UnsafeCell` sibling fields) preserves exact execution behavior across all `PanicMode`s, external callees, scalar inputs, and fuel bounds with zero new Tree Borrows UB.
  2. `store_sink_to_cleanup_refinement`: sinking a normal-path-overwritten field store across disjoint statements and a potentially-unwinding call into its unique-predecessor landing pad refines source execution under both `panic=unwind` and `panic=abort`.
  3. `unwind_to_abort_subsumption`: under `noCatchUnwind = true` and side-effect-free cleanup blocks, `panic=abort` preserves exact normal-return traces/values, subsumes `panic=unwind` panic traces/payloads without normal-return recovery, and introduces zero new errors or UB (accompanied by `4` positive non-vacuity canaries and `7` kernel-checked counterexample and Tree Borrows faithfulness theorems).
- **Explicit Non-Claims & Model Boundaries:**
  1. *Standalone model & translation validation only:* `VrustcFormal.F1_2` does **not** import or bridge to Anneal's `Trusted.MirSemantics.lean` or `rustc-capture` ASTs, and verifies per-transformation certificate checkers rather than `rustc`'s pass implementations or candidate-selection heuristics (e.g., `PartialSroaCert` promotes one field per certificate on an acyclic entry block).
  2. *2-level borrow tree & call-retag boundary:* Each field models an unprotected owner root (`0`) plus flat derived child tags (`≥ 1`), without arbitrary-depth pointer-to-pointer reborrows (`&mut *p`) or whole-struct `&mut s`; `takeFieldPtr ... .rawMut` and `takeRootRawPtr` conservatively perform an implicit root read on creation; and `callMayUnwind` activates protectors in place on existing child tags rather than creating fresh reborrow tags per duplicate register slot (so duplicate `&mut` arguments `[r, r]` are outside the modeled retag scope).
  3. *Uniform zero-initialized `UInt64` fields & total arithmetic:* Struct allocations live for the entire function activation (no `StorageLive`/`StorageDead`, deallocation, or pointers stored in memory fields) and hold zero-initialized `UInt64` scalars (`applyPartialSroa` initializes `ssaReg := 0` at entry), excluding byte-level `MaybeUninit`/padding poison, unions, enums, coroutines, and faulting arithmetic beyond wrapping `add`/`sub`/`xor`.
  4. *Scripted non-recursive callees:* External callees (`CalleeBody`) are finite, non-branching, non-recursive scripts over passed pointer arguments and trace events; value-dependent callee branching, recursion/reentrancy, heap/global pointer stashing, and shared statics are unmodeled.
  5. *`UnwindToAbortCert` locality, call-free cleanup & one-way fault/divergence subsumption:* Treating `writeField`/`writePtr` in cleanup blocks as side-effect-free relies critically on `MirBody` taking only scalar `initArgs : List UInt64` (no incoming external `&mut`/`*mut` references or statics, so all heap state is frame-local and discarded on unwind); `checkUnwindToAbortCert` forbids all `callMayUnwind` calls inside cleanup blocks (excluding non-inlined `Drop::drop` calls and double panics) and does not enforce cleanup-pad well-formedness or termination (`panic=abort` skips cleanup, so fault preservation is one-way from `abort` to `unwind`).
  6. *Sufficient (incomplete) syntactic certificates:* The checkers are sound sufficient conditions, not complete semantic characterizations; in particular, `fieldIsFreeze` in `checkStoreSinkCert` is conservative/redundant alongside `stmtNoPtrToField` (which already forbids all pointers to the sunk field), so sharpness on `isUnsafeCell` is established for `PartialSroaCert` (`ce_unsafecell_breaks_partial_sroa`), not `StoreSinkToCleanupCert`.

---

## Evidence

| Artifact / Source | Pin / Checksum | Role |
| :--- | :--- | :--- |
| `support/F1_2_MirTreeBorrows_PartialSroa_Unwind_Proof.lean` | SHA-256 `ae2132de4735bf32c44b004ccdf4b28440fd1123406e5920d491fa85d1f2a919` | Complete `5,878`-line, `110`-theorem (`14` public + `96` private) zero-`sorry` Lean 4 proof (`[propext, Quot.sound]`). |
| `support/F1_2_FROZEN.sha256` | SHA-256 `b7f148bb350eedb8d6e14d9dfc084b740fc22814516c66f15be9e6b9c5a1d92c` | Frozen pre-proof statement digest verified byte-identical across all `152` public declarations. |
| Villani et al., PLDI 2025 ("Tree Borrows") & `rust-lang/miri` | DOI `10.1145/3729264` / `7e679961edcfe2c526f19153bb8b03de346efa5c` | Reference semantics for `PermissionPriv::Cell`, `ReservedFrz`, `conflicted` under `is_protected`, and sub-place `outside_perm`. |
| `rust-lang/rust` (`rustc 1.99.1`) | `58cf8f9c35b355199727627d07ae34a4e2846d67` | Upstream compiler motivating hybrid-struct SROA, call-boundary store sinking, and `std` `invoke` (`41.8%`) vs. `panic=abort` subsumption. |
| `joshlf/anneal` (`trusted/lean/TrustedBoundary.lean`) | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | Purity and axiom boundary constraints (`[propext, Quot.sound]`, zero `bv_decide`/`native_decide`/`opaque`/`sorry`). |
| `leanprover/lean4` (`v4.28.0-rc1` / `v4.34.1` / `v4.35.0`) | `3b0f2862196c` / `5045d0056413` / `eb6cafb7290e` | Three Lean 4 kernel versions executing synchronous `-DElab.async=false -Ddebug.skipKernelTC=false` verification. |
| `leanprover/lean4export` & `ammkrn/nanoda_lib` (`nanoda_bin 0.4.19`) | `5a9a355dc6c5` / `0da9f98feadd` | External proof exporter (`3.1.0`) and independent Rust kernel re-checking all `2,505` declarations in `1.36 s`. |

---

## Revalidation

1. **Replay synchronous Lean 4 kernel check (zero external dependencies beyond `Init`):**
   ```bash
   lean -DElab.async=false -Ddebug.skipKernelTC=false \
     support/F1_2_MirTreeBorrows_PartialSroa_Unwind_Proof.lean
   ```
   Confirm exit code `0` and verify via `#print axioms` that all `14` public theorems in `VrustcFormal.F1_2` depend strictly on `[propext, Quot.sound]`.
2. **Replay independent external Rust kernel check (`lean4export` + `nanoda_bin`):**
   Compile `support/F1_2_MirTreeBorrows_PartialSroa_Unwind_Proof.lean` to `.olean`, run `leanexport` over the `14` public theorems, and check with `nanoda_bin` (`nat_extension: true`, `string_extension: true`); confirm `Checked 2505 declarations with no errors`.
3. **Re-audit upon Miri Tree Borrows or Anneal `Trusted.MirSemantics` updates:**
   Revisit whenever `rust-lang/miri` modifies `PermissionPriv` transitions (`Cell`, `ReservedFrz`, or two-phase `conflicted`) or when `joshlf/anneal` extends `Trusted.MirSemantics.lean` with references, interior mutability, and `UnwindAction` cleanup edges.
