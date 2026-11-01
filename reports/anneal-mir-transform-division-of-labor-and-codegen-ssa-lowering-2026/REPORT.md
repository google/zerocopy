<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Adapting `rustc_mir_transform` and `rustc_codegen_ssa` / `rustc_codegen_llvm` for Anneal's `MIR -> AnLLVM` Pipeline

## Executive Summary

A formally verified `MIR -> AnLLVM -> ISA` pipeline in Anneal must answer two
closely coupled front-end design questions against `rust-lang/rust` (audited at
commit `49d734536222bf28bb6d07d885b3a81d145981da`):
1. **The MIR-vs.-`AnLLVM` Division of Labor (`compiler/rustc_mir_transform`,
  34,593 LOC):** Which MIR transformations must run as mandatory lowering
  (`Category M1`), which exploit high-level MIR ownership and projection
  invariants that `AnLLVM`'s middle-end cannot recover once lowered to
  byte-offset pointers (`Category M2`), and which duplicate `AnLLVM` middle-end
  passes while introducing disproportionate verification and soundness surface
  (`Category M3`)?
2. **Adapting `compiler/rustc_codegen_ssa` and `compiler/rustc_codegen_llvm`
  (`MIR -> AnLLVM` Lowering):** How can we preserve `rustc_codegen_ssa`'s
  single-pass reverse-postorder lowering architecture (`FunctionCx`,
  `LocalAnalyzer`, `PlaceRef`, `OperandValue`, `BuilderMethods`) while replacing
  the six workarounds where `rustc` bounces through stack `alloca`s, `!noundef`
  metadata, or `@llvm.assume` chains to compensate for upstream LLVM IR's
  semantic limitations?

This report presents primary-source audits, empirical differential ablations
(`support/run_ablation.py`, `support/ablation_results.json`, and
`support/empirical_probe_opt1_nollvm.ll`), semantic model refinements for
Anneal's `MirSemantics`, and two standalone Lean 4.34.1 mechanizations
(`support/support_mir_transform_adaptation_probe.lean`, `1,446` lines;
`support/support_mir_to_anllvm_lowering_probe.lean`, `1,589` lines; zero
`sorryAx`) establishing five central conclusions:

1. **Three-Tier `rustc_mir_transform` Division of Labor (`Category M1`, `M2`,
  `M3`):**
   - **Category M1 (~6,200 LOC):** Mandatory pre-codegen lowering and cleanup
     (`ElaborateDrops`, `coroutine::StateTransform`, `shim::make_shim`,
     `AbortUnwindingCalls`, `LowerIntrinsics`, `SimplifyCfg`,
     `CleanupPostBorrowck`, `PostAnalysisNormalize`, `AddMovesForPackedDrops`).
     To shrink the pre-capture trust gap for ownership-sensitive code,
     `ElaborateDrops`, `AbortUnwindingCalls`, `LowerIntrinsics`, and
     `SimplifyCfg` are the highest-leverage M1 passes to verify inside Lean
     (`PreDropMirLang -> MirLang`).
   - **Category M2 (~2,450 LOC):** High-value MIR optimizations exploiting typed
     places, destructive `Operand::Move` ownership transfer, and pre-ABI
     uniformity of `_0` (`RETURN_PLACE`): `DestinationPropagation`
     (`dest_prop.rs`, 670 LOC, which subsumes NRVO per `dest_prop.rs:18-20`),
     `CopyProp` + `SsaLocals` (`copy_prop.rs`, 194 LOC + `ssa.rs`, 455 LOC),
     `ScalarReplacementOfAggregates` (`sroa.rs`, 431 LOC), and `Inline` /
     `ForceInline` (`inline.rs`, 917 LOC).
   - **Category M3 (~15,000+ LOC):** Redundant or bug-prone MIR optimizations to
     skip in MIR and delegate to `AnLLVM`: `GVN` (`gvn.rs`, 2,265 LOC),
     `JumpThreading` (`jump_threading.rs`, 1,127 LOC), `DataflowConstProp`
     (`dataflow_const_prop.rs`, 1,071 LOC), `ReferencePropagation`
     (`ref_prop.rs`, 467 LOC), and `InstSimplify` (`instsimplify.rs`, 1,078
     LOC).
2. **Empirical Proof that Category M2 Is Irreplaceable by `opt -O2` While
  Category M3 Degrades CFG Quality (`support/ablation_results.json`):**
   - On a 256-byte aggregate builder (`[u64; 32]`) moving across a diamond
     branch with an external call into a by-value return (`sret`), running `opt
     -passes='default<O2>'` on `-Zmir-opt-level=0` IR (`C1`) fails to eliminate
     **2 stack `alloca`s (192 bytes) and 2 `llvm.memcpy` calls**, because LLVM
     `SROA` cannot split an incoming `sret` pointer parameter and LLVM
     `MemCpyOpt` cannot forward `memset`/`memcpy` into `sret` across a diamond
     CFG with an opaque call. Enabling only the Category M2 MIR passes (`C2`)
     eliminates **100% of `alloca`s (`8 -> 0`) and 100% of `llvm.memcpy` calls
     (`7 -> 0`)** *before `AnLLVM` even runs*.
   - Conversely, on an 8-iteration `Option::map` / `and_then` adapter loop
     (`pattern2_option_adapter_chain`), Category M2 + `opt -O2` (`C2`) compiles
     the loop into a **single branchless basic block (`BBs = 1`, 117
     instructions)**, whereas full `-Zmir-opt-level=2 + opt -O2` (`C3`) degrades
     to **25 basic blocks (119 instructions)** because MIR's Category M3
     `JumpThreading` pass threads `SwitchInt` edges into multi-predecessor
     triangles that defeat LLVM's `SimplifyCFG` if-conversion.
3. **`LocalAnalyzer` (`mir/analyze.rs`) Eliminates Frontend $\phi$-Placement
  from the `MIR -> AnLLVM` Proof Obligation:** In `rustc_codegen_ssa`,
  `analyze::non_ssa_locals` (`mir/analyze.rs:17-56`) partitions MIR locals into
  single-definition dominating SSA operands (`LocalKind::SSA(DefLocation)` ->
  `LocalRef::Operand`) and memory-backed places (`LocalKind::Memory` ->
  `LocalRef::Place`). Because `codegen_mir` (`mir/mod.rs:291, 380`) traverses
  basic blocks in reverse postorder (a topological sort of the dominance
  relation), every `LocalRef::PendingOperand` is overwritten exactly once before
  any use is visited, deferring all $\phi$ placement to `AnLLVM`'s standalone
  verified `Mem2Reg` pass.
4. **Universal Modular Round-Trip Identity for `TagEncoding::Niche`
  (`codegen_get_set_discr_niche_roundtrip`):** `rustc_codegen_ssa` encodes niche
  tags via modular addition `(niche_start + (v - v_start)) mod M`
  (`mir/place.rs:519-521`) and decodes them via wrapping subtraction `rel = (tag
  - niche_start) mod M` followed by an unsigned range check `rel <= v_end -
  v_start` (`mir/operand.rs:577-689`). We mechanize and prove in Lean 4.34.1
  that this encoding/decoding pair is universally sound for all moduli $M > 0$,
  even when the niche range wraps around $0 \pmod M$.
5. **Eliminating `PassMode::Cast` and `Transmute` Memory Bounces and Catching
  `rustc`'s Padding `!noundef` Bug (`support/empirical_probe_opt1_nollvm.ll`):**
  Empirically, `rustc 1.101.0-nightly` lowers `transmute::<Padded, u64>(p)` (at
  `support/empirical_probe_opt1_nollvm.ll:358`) via an `alloca` bounce followed
  by `load i64, ptr %0, align 8, !noundef !14`—attaching `!noundef` to a
  whole-word `i64` load across 3 uninitialized padding bytes—and emits 4
  `alloca`s + 2 `llvm.memcpy`s (19 instructions) for `PassMode::Cast`.
  `AnLLVM`'s `pack_cast_regs`, `unpack_cast_regs`, and `bitcast_bytes` over
  `MaskedWord64` eliminate 100% of these `alloca` bounces in 1 SSA step while
  preserving exact per-byte initialization masks.

---

## 1. Part I: Primary-Source Audit of `compiler/rustc_mir_transform` (`49d734536222bf28bb6d07d885b3a81d145981da`)

### 1.1 Pipeline Phase Architecture in `compiler/rustc_mir_transform/src/lib.rs`

In `compiler/rustc_mir_transform/src/lib.rs` (841 LOC), MIR bodies progress
through three major dialects (`MirPhase::Built`, `MirPhase::Analysis`, and
`MirPhase::Runtime`) governed by six query stages:
1. **`mir_built` (`lib.rs:390-428`):** Constructs initial MIR from HIR/THIR and
  runs `LintAndRemoveUninhabited`, MIR lints, `SimplifyCfg::Initial`, and
  `SanityCheck`.
2. **`mir_promoted` (`lib.rs:431-488`):** Runs `RequiredConstsVisitor`,
  `PromoteTemps`, `SimplifyCfg::PromoteConsts`, and `InstrumentCoverage`,
  transitioning to `MirPhase::Analysis(AnalysisPhase::Initial)`.
3. **`run_analysis_cleanup_passes` (`lib.rs:630-640`):** After `mir_borrowck`,
  runs `ImpossibleClauses`, `CleanupPostBorrowck`, `RemoveNoopLandingPads`,
  `SimplifyCfg::PostAnalysis`, and `Derefer`, transitioning to
  `MirPhase::Analysis(AnalysisPhase::PostCleanup)`.
4. **`run_runtime_lowering_passes` (`lib.rs:643-667`):** Lowers `Analysis` MIR
  into `MirPhase::Runtime(RuntimePhase::Initial)` via `CriticalCallEdges`,
  `PostAnalysisNormalize`, `Subtyper` (`add_subtyping_projections.rs`),
  `ElaborateDrops`, `CheckDropRecursion`, `AbortUnwindingCalls`,
  `AddMovesForPackedDrops`, `EraseDerefTemps`, `ElaborateBoxDerefs`,
  `coroutine::StateTransform`, and `KnownPanicsLint`.
5. **`run_runtime_cleanup_passes` (`lib.rs:670-684`):** Lowers runtime-initial
  MIR into `MirPhase::Runtime(RuntimePhase::PostCleanup)` via `LowerIntrinsics`,
  `RemovePlaceMention`, and `SimplifyCfg::PreOptimizations`. **This
  `Runtime(PostCleanup)` boundary is where `anneal-rustc-capture` currently
  extracts MIR.**
6. **`inner_optimized_mir` & `run_optimization_passes` (`lib.rs:686-822`):**
  Runs `remap_mir_for_const_eval_select`, `MentionedItems`, and the 41-stage
  optimization pipeline ending in `MirPhase::Runtime(RuntimePhase::Optimized)`,
  followed by `deduced_param_attrs` (`deduce_param_attrs.rs:144-239`).

### 1.2 Complete Classification Table of `rustc_mir_transform` Passes

| Pass / Module | File (`rustc_mir_transform/src/`) | LOC | Phase | Default Policy (`mir-opt-level`) | High-Level MIR Invariants Exploited | Historical Soundness Bugs / Hazards | Anneal Category & Recommendation |
| :--- | :--- | ---: | :--- | :--- | :--- | :--- | :--- |
| `ElaborateDrops` | `elaborate_drops.rs` + `elaborate_drop.rs` | 2,217 | `Runtime(Initial)` | `Required` (always) | `MoveData` initialization lattices (`MaybeInitializedPlaces`, `MaybeUninitializedPlaces`), `Place` projection trees, `DropStyle::{Dead, Static, Conditional, Open}`, unwind vs. normal drop paths | Unwind drop-flag desync if flag is not cleared before drop (`elaborate_drop.rs:1556-1581`); packed-field drop alignment (`#46043`) | **M1 (Mandatory Lowering):** Required before `MirSemantics` or `AnLLVM` codegen; highest priority M1 pass to verify in Lean (`PreDropMirLang -> MirLang`). |
| `coroutine::StateTransform` | `coroutine/*.rs` (`mod.rs`, `layout.rs`, `drop.rs`, `by_move_body.rs`) | 2,670 | `Runtime(Initial)` | `Required` (always) | Yield suspension points (`TerminatorKind::Yield`), cross-suspend local liveness (`locals_live_across_suspend_points`), witness struct layout, coroutine drop shims | Query cycles with `JumpThreading`/`DataflowConstProp`; drop-shim pass omission (`FIXME(#91576)` in `shim.rs:82`) | **M1 (Mandatory Pre-Capture):** Keep in `rustc` pre-capture so Anneal captures lowered state-machine `Future::poll` / `Coroutine::resume` MIR. |
| `make_shim` (`MirShims`) | `shim.rs` + `shim/async_destructor_ctor.rs` | 1,781 | On-demand query (`mir_shims`) | `Required` (always) | `ShimKind::{VTable, FnPtr, Reify, ClosureOnce, DropGlue}`, ADT field destructor ordering, `Adjustment::{Identity, Deref, RefMut}` | Coroutine drop-shim pass inconsistency (`#91576`) | **M1 (Mandatory Pre-Capture):** Capture synthesized `DropGlue` and `FnOnce` shims as standard `Runtime(PostCleanup)` MIR bodies. |
| `AbortUnwindingCalls` | `abort_unwinding_calls.rs` | 148 | `Runtime(Initial)` | `Required` (always) | `UnwindAction::{Continue, Unreachable, Terminate, Cleanup}`, caller vs. callee `PanicStrategy::Abort` ABI compatibility | Missing `Terminate(Reason::Abi)` on cross-ABI unwind edges causes UB on panic | **M1 (Mandatory Lowering):** Trivial CFG terminator rewrite; verify in Lean or keep in `PostCleanup` capture. |
| `LowerIntrinsics` | `lower_intrinsics.rs` | 346 | `Runtime(PostCleanup)` | `Required` (always) | `TerminatorKind::Call` to `IntrinsicDef` (`wrapping_add/sub/mul`, `unreachable`, `ub_checks`, `forget`, `copy_nonoverlapping`, `transmute`, `aggregate_raw_ptr`, `ptr_metadata`) | `forget` must use `Operand::Move` to deinitialize argument (`lower_intrinsics.rs:76-82`); `copy_nonoverlapping` overflow check | **M1 (Mandatory Lowering):** Essential bridge turning intrinsic calls into primitive MIR `StatementKind::Intrinsic` / `Rvalue::BinaryOp` / `CastKind::Transmute`. |
| `SimplifyCfg` / `SimplifyLocals` | `simplify.rs` | 538 | All phases (`Initial`..`Final`) | `Optional(true)` for CFG; `>= 1` for `SimplifyLocals` | Dead basic blocks, single-predecessor `Goto` chains, empty switches, unused `LocalDecl` compaction | Must preserve `START_BLOCK` and update `SwitchTargets` consistently | **M1/M2 (Mandatory CFG Cleanup + Local Compaction):** Adapt in Lean to prune unreachable blocks and dead temporaries before `AnLLVM` lowering. |
| `CleanupPostBorrowck` | `cleanup_post_borrowck.rs` | 94 | `Analysis(PostCleanup)` | `Required` (always) | Erases borrowck-only statements (`AscribeUserType`, `FakeRead`, `Assign(Fake)`, `Coverage::BlockMarker`) | Leaving `FakeRead` in runtime MIR causes spurious reads of uninit memory in Miri/codegen | **M1 (Mandatory Pre-Capture):** Pure erasure of borrow-checker ghost statements before `Runtime` phase. |
| `Derefer` / `EraseDerefTemps` / `ElaborateBoxDerefs` | `deref_separator.rs`, `erase_deref_temps.rs`, `elaborate_box_derefs.rs` | 356 | `Analysis` -> `Runtime(Initial)` | `Required` (always) | `DerefTemp` local markers, `Box<T>` unique pointer projection lowering | Debuginfo dangling references after `EraseDerefTemps` | **M1 (Mandatory Pre-Capture):** Normalizes `Box` derefs and temporary chains before `Runtime(PostCleanup)`. |
| `PostAnalysisNormalize` / `Subtyper` / `AddMovesForPackedDrops` / `CriticalCallEdges` | `post_analysis_normalize.rs`, `add_subtyping_projections.rs`, `add_moves_for_packed_drops.rs`, `add_call_guards.rs` | 561 | `Runtime(Initial)` | `Required` (always) | Reveal-all opaque type normalization, variance subtyping projections, aligned temporary copy before dropping `#[repr(packed)]` fields | Dropping unaligned `#[repr(packed)]` field in place is immediate alignment UB (`add_moves_for_packed_drops.rs:1-40`) | **M1 (Mandatory Pre-Capture):** Must run prior to `Runtime(PostCleanup)` capture so types are normalized and packed drops are aligned. |
| `RemovePlaceMention` / `RemoveNoopLandingPads` / `RemoveUninitDrops` / `RemoveUnneededDrops` | `remove_place_mention.rs`, `remove_noop_landing_pads.rs`, `remove_uninit_drops.rs`, `remove_unneeded_drops.rs` | 334 | `Analysis` / `Runtime` | `Required` / `Optional(true)` | Erases `PlaceMention` (unless `-Zmir-preserve-ub`), trivial `Drop`s on `Copy`/uninit types, empty landing pads | None | **M1 (Mandatory Cleanup):** Keep enabled in `PostCleanup`. |
| **`DestinationPropagation`** *(subsumes NRVO)* | `dest_prop.rs` | 670 | `Runtime(Optimized)` (runs twice: `lib.rs:794, 813`) | `mir_opt_level >= 2` | Unifies `dst = move src` across basic blocks when `!borrowed_locals.contains(src)` and `MaybeLiveLocals` ranges of `src` and `dst` are disjoint; **can unify `src` directly with `_0` (`RETURN_PLACE`) before ABI `sret` lowering** (`dest_prop.rs:18-20`) | **`#146383`**: deleting `StorageLive`/`StorageDead` instead of unioning intervals (`dest_prop.rs:273-278`) + interleaved same-statement read/write liveness (`dest_prop.rs:630-656`) | **M2 (High-Value MIR Optimization — Adapt):** Eliminates 256-byte aggregate `alloca`s and `llvm.memcpy`s into `_0` (`sret`) that LLVM `SROA`/`MemCpyOpt` **cannot** eliminate across diamond CFGs with calls (`Pattern 1`). Must fix `StorageLive` interval unioning in Anneal. |
| **`CopyProp` + `SsaLocals`** | `copy_prop.rs` + `ssa.rs` | 649 | `Runtime(Optimized)` (runs twice: `lib.rs:795, 814`) | `mir_opt_level >= 1` | Whole-local pseudo-SSA def-use graph (`SsaLocals`), destructive `Operand::Move` -> `Operand::Copy` conversion when unifying single-assignment chains (`_b = move? _a`), `!borrowed_locals` | If `src` may be `StorageDead` at a propagated use of `dst`, `StorageLive`/`StorageDead` markers must be widened/removed (`copy_prop.rs:59-92`) | **M2 (High-Value MIR Optimization — Adapt):** Eliminates single-assignment aggregate/scalar copy chains in $O(N)$ before `AnLLVM` `alloca` emission; pairs directly with `DestinationPropagation`. |
| **`ScalarReplacementOfAggregates` (`MirSROA`)** | `sroa.rs` | 431 | `Runtime(Optimized)` (`lib.rs:802`) | `mir_opt_level >= 2` | Typed `PlaceElem::Field(idx, ty)` projections on `Variants::Single` (structs/tuples), `Rvalue::Aggregate` decomposition into per-field `Rvalue::Use(op, WithRetag::Yes)`, syntactic `escaping_locals` visitor (`sroa.rs:58-143`) | Must exclude `union`s, `Variants::Multiple` (`enum`s), `#[repr(simd)]`, `#[repr(scalable)]`, and `DynMetadata` (`sroa.rs:163-172`); currently excludes `_0` (`RETURN_PLACE`, `sroa.rs:62`) | **M2 (High-Value MIR Optimization — Adapt):** Replaces typed struct/tuple/closure locals with scalar locals in one linear pass before `AnLLVM` ever creates stack `alloca`s, GEPs, or `memcpy`s. |
| **`Inline` & `ForceInline`** | `inline.rs` + `inline/cycle.rs` | 997 | `Runtime(Optimized)` (`lib.rs:774, 799`) | `ForceInline`: `Required`; `Inline`: `mir_opt_level >= 2` (or `>= 1` with LLVM optimizations) | Monomorphized `Instance` body splicing, closure `SpreadArgs` tuple unpacking (`inline.rs:480-520`), `StorageLive`/`StorageDead` wrapping of callee locals | Must check ABI/target-feature compatibility, unsized RVO params, and call-graph cycles (`inline/cycle.rs`); interacts with `DeduceParamAttrs` | **M2 (High-Value MIR Optimization — Adapt):** Inlines `#[inline]` closures, `Option::map`, and iterator adapters **before** `MirSROA` and `DestinationPropagation`, shrinking emitted LLVM functions by 60% in `Pattern 2`. |
| `RemoveZsts` / `RemoveStorageMarkers` | `remove_zsts.rs`, `remove_storage_markers.rs` | 145 | `Runtime(Optimized)` | `mir_opt_level >= 1` | `Layout::is_zst()` (turns writes to 0-sized types into `Nop`), removes `StorageLive`/`StorageDead` when `!emit_lifetime_markers` | Must not remove write through raw pointer if deref has UB check | **M2 (Lightweight MIR Cleanup — Adapt):** Eliminating ZST assignments in MIR avoids emitting dummy ZST operations into `AnLLVM`. |
| `GVN` (Global Value Numbering) | `gvn.rs` | 2,265 | `Runtime(Optimized)` (`lib.rs:791`) | `mir_opt_level >= 2` | `SsaLocals`, Miri `InterpCx` constant folding, `VnState` value numbering over `Rvalue`s, aggregate field forwarding | **`#120613`**, **`#141038`**, **`#110947`**, **`#118328`**: pointer provenance loss (`PtrToPtr` cast unification), `transmute` padding/uninit byte mishandling, vtable metadata canonicalization, floating-point NaN/signed-zero canonicalization | **M3 (Skip in MIR — Delegate to `AnLLVM`):** Highest bug density in `rustc_mir_transform` (2,265 LOC); 100% subsumed on scalar/pointer arithmetic by `AnLLVM`'s `GVN` + `InstCombine` (`Pattern 4`). |
| `JumpThreading` | `jump_threading.rs` | 1,127 | `Runtime(Optimized)` (`lib.rs:789`) | `mir_opt_level >= 2 && !is_like_gpu` | Backward `ConditionSet` propagation over `SwitchInt`, basic-block duplication (`MAX_COST = 100`) | **`#137086`** (unsound duplication of convergent GPU barriers); in `Pattern 2`, creates multi-predecessor triangle CFGs that **degrade** LLVM `SimplifyCFG` if-conversion (`1 BB -> 25 BBs`) | **M3 (Skip in MIR — Delegate to `AnLLVM`):** Complex 1,127-LOC CFG duplicator that actively interferes with LLVM's `SimplifyCFG` on unrolled adapter loops (`Pattern 2`) and is subsumed on state machines (`Pattern 3`). |
| `DataflowConstProp` | `dataflow_const_prop.rs` | 1,071 | `Runtime(Optimized)` (`lib.rs:771`) | `mir_opt_level >= 3` (not in `-Zmir-opt-level=2`) | `FlatSet<Scalar>` lattice over `rustc_mir_dataflow::value_analysis::Map`, `DummyMachine` `InterpCx` evaluation | Complex interaction with pointer provenance and partial overwrites; capped at `BLOCK_LIMIT = 100` due to cubic transfer cost | **M3 (Skip in MIR — Delegate to `AnLLVM`):** Not enabled at `rustc`'s default `-Zmir-opt-level=2`; completely subsumed by `AnLLVM` `SCCP` + `GVN`. |
| `InstSimplify` + `SimplifyComparisonIntegral` + `MatchBranchSimplification` + `EarlyOtherwiseBranch` | `instsimplify.rs`, `simplify_comparison_integral.rs`, `match_branches.rs`, `early_otherwise_branch.rs` | 1,890 | `Runtime(Optimized)` | `mir_opt_level >= 1` or `>= 2` | Peephole `Rvalue` rewrites, boolean/switch branch merging, enum discriminant equality switches | Duplicate-switch edge bugs when assumptions (`NonDivergingIntrinsic::Assume`) are dropped | **M3 (Skip in MIR — Delegate to `AnLLVM`):** Empirically 100% subsumed by `AnLLVM` `InstCombine` + `SimplifyCFG` (`Patterns 3 & 4`). |
| `ReferencePropagation` | `ref_prop.rs` | 467 | `Runtime(Optimized)` (`lib.rs:790`) | `mir_opt_level >= 2` | Rewrites `*_1` to `_2` when `_1 = &raw? mut? _2`, using `SsaLocals` and `MaybeStorageDead`; mutates all pointer moves into `Operand::Copy` (`ref_prop.rs:88-93`) | **`#63616`** / `deduce_param_attrs` interaction; risks introducing dereferences of `StorageDead` locals unless storage markers on the target local are deleted (`ref_prop.rs:51-55`) | **M3 (Skip in MIR — Delegate to `AnLLVM`):** Once `AnLLVM` `SROA` + `Mem2Reg` promotes stack pointers, local reference propagation happens automatically in SSA without `StorageDead` or `&mut` uniqueness hazards. |
| `DeadStoreElimination` | `dead_store_elimination.rs` | 156 | `Runtime(Optimized)` (`lib.rs:782, 809`) | `mir_opt_level >= 2` | Backward `Liveness` dataflow over `borrowed_locals` | Cannot eliminate stores to any local that has a borrow taken anywhere in the function | **M3 (Optional / Delegate to `AnLLVM`):** Subsumed for scalars by `Mem2Reg`/SSA dead-instruction elimination and for memory by `AnLLVM` `DSE`. |
| `SingleUseConsts` / `SsaRangeProp` / `UnreachablePropagation` / `UnreachableEnumBranching` / `LowerSliceLen` | `single_use_consts.rs`, `ssa_range_prop.rs`, `unreachable_prop.rs`, `unreachable_enum_branching.rs`, `lower_slice_len.rs` | 886 | `Runtime(Optimized)` | `mir_opt_level >= 1` or `>= 2` | Constant operand inlining, `PtrMetadata` range assumptions, unreachable block backward propagation (`Assume` insertion) | `UnreachableEnumBranching` relies on uninhabited variant validity rules | **M3 (Skip in MIR — Delegate to `AnLLVM`):** Subsumed by `AnLLVM` constant propagation and `CorrelatedValuePropagation`. |
| `DeduceParamAttrs` | `deduce_param_attrs.rs` | 239 | Post-`optimized_mir` query (`lib.rs:703`) | `opt_level != No` | Scans final `optimized_mir` to infer `readonly`, `noalias`, `captures(none)` on by-ref parameters (`UsageSummary`) | **Critical Phase-Ordering Hazard (`deduce_param_attrs.rs:8-10, 102-135`):** Marks unmodified by-value parameters as `readonly` assuming `DestinationPropagation`/`CopyProp` will **never** run afterwards | **Post-M2 Boundary Analysis:** Must run **only after** all Category M2 MIR passes (`DestProp`, `CopyProp`, `MirSROA`, `Inline`) have finished, immediately at the `MIR -> AnLLVM` lowering boundary. |

---

## 2. Empirical Differential Ablation: `rustc` `-Zmir-opt-level=0` vs. Category M2 vs. `-Zmir-opt-level=2` + `opt -O2`

### 2.1 Experimental Setup (`support/bench_patterns.rs`, `support/run_ablation.py`, `support/ablation_results.json`)

We evaluate six configurations on `support/bench_patterns.rs` (`#![no_std]`)
using `rustc 1.101.0-nightly` (`-Copt-level=2 -Cno-prepopulate-passes
-Cpanic=abort --emit=llvm-ir`) and `/usr/bin/opt` (LLVM 21.1.8,
`-passes='default<O2>' -S`):
- **`C0` (Pre-`opt` Baseline):** `rustc -Zmir-opt-level=0` (only Category M1
  required passes run).
- **`C2_raw` (Pre-`opt` Category M2 Only):** `rustc -Zmir-opt-level=0
  -Zmir-enable-passes=+DestinationPropagation,+CopyProp,+ScalarReplacementOfAggregates,+Inline`
  (no LLVM `opt`).
- **`C3_raw` (Pre-`opt` Full MIR Opt):** `rustc -Zmir-opt-level=2` (no LLVM
  `opt`).
- **`C1` (No MIR Opt + LLVM `-O2`):** `C0` + `/usr/bin/opt
  -passes='default<O2>'`.
- **`C2` (Category M2 Only + LLVM `-O2`):** `C2_raw` + `/usr/bin/opt
  -passes='default<O2>'`.
- **`C3` (Full `-Zmir-opt-level=2` + LLVM `-O2`):** `C3_raw` + `/usr/bin/opt
  -passes='default<O2>'`.

### 2.2 Per-Function & Whole-Module Ablation Results

#### Table 1: Per-Function LLVM IR Metrics Across `C0..C3`

| Pattern / Function | Config | LLVM Insts | `alloca`s | `llvm.memcpy`s | Basic Blocks | `load`s | `store`s |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| **Pattern 1:** `pattern1_large_aggregate_builder`<br>*(256-byte `[u64; 32]` builder + diamond branch + call)* | `C0` *(M1 only, no `opt`)* | 51 | **8** | **7** | 4 | 2 | 2 |
| | `C2_raw` *(M1 + M2, no `opt`)* | **29** | **0** | **0** | 4 | 3 | 6 |
| | `C3_raw` *(`mir-opt=2`, no `opt`)* | 44 | 1 | 1 | 4 | 3 | 10 |
| | `C1` *(M1 only + `opt -O2`)* | 34 | **2** | **2** | 1 | 0 | 8 |
| | `C2` *(M1 + M2 + `opt -O2`)* | **30** | **0** | **0** | **1** | **0** | **8** |
| | `C3` *(`mir-opt=2` + `opt -O2`)* | **30** | **0** | **0** | **1** | **0** | **8** |
| **Pattern 2:** `pattern2_option_adapter_chain`<br>*(8-iter loop with `Option::map` / `and_then` + `Pair<u64, u64>`)* | `C0` *(M1 only, no `opt`)* | 60 *(+14 callees)* | 7 | 0 | 9 | 9 | 7 |
| | `C2_raw` *(M1 + M2, no `opt`)* | 118 *(inlined)* | 7 | 0 | 25 | 19 | 21 |
| | `C3_raw` *(`mir-opt=2`, no `opt`)* | 100 *(inlined)* | 6 | 0 | 12 | 17 | 19 |
| | `C1` *(M1 only + `opt -O2`)* | 119 | 0 | 0 | 17 | 8 | 0 |
| | `C2` *(M1 + M2 + `opt -O2`)* | **117** | **0** | **0** | **1** | **8** | **0** |
| | `C3` *(`mir-opt=2` + `opt -O2`)* | 119 | 0 | 0 | **25** | 8 | 0 |
| **Pattern 3:** `pattern3_enum_state_machine`<br>*(`StepState` 4-variant enum -> `Result<u64, u32>` match chain)* | `C0` *(M1 only, no `opt`)* | 113 | 3 | 0 | 21 | 16 | 30 |
| | `C2_raw` *(M1 + M2, no `opt`)* | 113 | 3 | 0 | 21 | 16 | 30 |
| | `C3_raw` *(`mir-opt=2`, no `opt`)* | 69 | 3 | 0 | 7 | 9 | 19 |
| | `C1` *(M1 only + `opt -O2`)* | **14** | **0** | **0** | **4** | **0** | **3** |
| | `C2` *(M1 + M2 + `opt -O2`)* | **14** | **0** | **0** | **4** | **0** | **3** |
| | `C3` *(`mir-opt=2` + `opt -O2`)* | **14** | **0** | **0** | **4** | **0** | **3** |
| **Pattern 4:** `pattern4_scalar_cse_loop`<br>*(16-element loop with duplicate `x*k1 + k2` and identity ops)* | `C0` *(M1 only, no `opt`)* | 37 | 2 | 0 | 6 | 6 | 4 |
| | `C2_raw` *(M1 + M2, no `opt`)* | 35 | 2 | 0 | 6 | 6 | 4 |
| | `C3_raw` *(`mir-opt=2`, no `opt`)* | 29 | 2 | 0 | 6 | 6 | 4 |
| | `C1` *(M1 only + `opt -O2`)* | **10** | **0** | **0** | **1** | **1** | **0** |
| | `C2` *(M1 + M2 + `opt -O2`)* | **10** | **0** | **0** | **1** | **1** | **0** |
| | `C3` *(`mir-opt=2` + `opt -O2`)* | **10** | **0** | **0** | **1** | **1** | **0** |
| **Pattern 5:** `pattern5_drop_elaboration`<br>*(Unconditional move + conditional move of `Drop` `Guard`)* | `C0` *(M1 only, no `opt`)* | 39 | 5 | 0 | 6 | 6 | 9 |
| | `C2_raw` *(M1 + M2, no `opt`)* | 37 | 5 | 0 | 6 | 6 | 9 |
| | `C3_raw` *(`mir-opt=2`, no `opt`)* | 30 | 4 | 0 | 4 | 5 | 5 |
| | `C1` *(M1 only + `opt -O2`)* | **23** | **3** | **0** | **4** | **0** | **3** |
| | `C2` *(M1 + M2 + `opt -O2`)* | **23** | **3** | **0** | **4** | **0** | **3** |
| | `C3` *(`mir-opt=2` + `opt -O2`)* | **23** | **3** | **0** | **4** | **0** | **3** |

#### Table 2: Whole-Module Totals (Including Monomorphized Helpers & Closures)

| Config | Description | Emitted Functions | Total Insts | Total `alloca`s | Total `llvm.memcpy`s | Total BBs | Total `load`s | Total `store`s |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `C0` | `-Zmir-opt-level=0` (pre-`opt`) | 20 | 454 | 29 | 11 | 79 | 55 | 78 |
| `C2_raw` | `-Zmir-opt-level=0` + **Category M2** (pre-`opt`) | **8** (`-60%`) | **352** (`-22.5%`) | **18** (`-37.9%`) | **1** (`-90.9%`) | 65 | 51 | 74 |
| `C3_raw` | `-Zmir-opt-level=2` (pre-`opt`) | 7 (`-65%`) | 277 (`-39.0%`) | 16 (`-44.8%`) | 1 (`-90.9%`) | 35 | 41 | 57 |
| `C1` | `-Zmir-opt-level=0` + `opt -O2` | 6 | 203 | 5 | **2** | 28 | 10 | 14 |
| `C2` | `-Zmir-opt-level=0` + **Category M2** + `opt -O2` | **6** | **197** | **3** | **0** | **12** | **10** | **14** |
| `C3` | `-Zmir-opt-level=2` + `opt -O2` | 6 | 199 | 3 | 0 | 36 | 10 | 14 |

### 2.3 Four Semantic Refinements to Anneal's `MirAst` and `MirSemantics`

1. **Refinement R1 — Three-State `LocalSlot` (`.dead`, `.uninit`, `.init v`) +
  Explicit `Operand::Move` Deinitialization + `StorageLive` Unioning:** In
  `rustc`, `dest_prop.rs:273-278` deletes `StorageLive`/`StorageDead` markers
  rather than unioning them (`FIXME: Don't delete storage statements, but
  "merge" the storage ranges instead`), which caused `rust-lang/rust#146383`.
  Refining `MirState.locals` to `Local → LocalSlot` (`.dead | .uninit | .init
  v`) where writing to `.dead` is immediate `.ub` and requiring
  `DestinationPropagation` and `CopyProp` to **union** the
  `StorageLive`..`StorageDead` intervals of `src` and `dst` eliminates `#146383`
  by construction (`destProp_with_live_union_compiles` and
  `canary_destProp_without_live_union_violates_compiles`).
2. **Refinement R2 — Explicit `isAddressTaken : Local → Bool` Declaration
  Invariant + `RETURN_PLACE` Field Forwarding in `MirSROA` / `DestProp`:**
  Recording `isAddressTaken : Local → Bool` directly in `MirBody` allows
  `MirSROA` to be formulated as a projection-tree isomorphism over
  `MirState.locals` for any `Variants::Single` local `l` with `!isAddressTaken
  l`, and decomposing `_0 = Rvalue::Aggregate(Adt, [Move(src)])` into `_0.0 =
  move src` closes the `C3_raw` inlined-constructor gap before `AnLLVM` runs.
3. **Refinement R3 — Two-Stage `PreDropMirLang -> MirLang` Lowering for
  `ElaborateDrops`:** Defining `PreDropMirLang` (where `Terminator.drop place
  target` drops `place` iff its `LocalSlot` is currently `.init`) allows
  `ElaborateDrops` to be verified as a `PassCompiler PreDropMirLang MirLang
  preDropToMirCodec` (`elaborateDrops_compiles` and
  `canary_elaborateDrops_missing_move_clear_unsound`).
4. **Refinement R4 — Phase-Locked `DeduceParamAttrs` at the `MIR -> AnLLVM`
  Lowering Boundary:** Never deduce `readonly`/`noalias`/`captures(none)` on
  intermediate MIR phases; compute them exclusively as part of final `MIR ->
  AnLLVM` lowering after `DestinationPropagation`, `CopyProp`, `MirSROA`, and
  `Inline` have completed.

---

## 3. Part II: Primary-Source Audit & Adaptation of `rustc_codegen_ssa` and `rustc_codegen_llvm`

### 3.1 `FunctionCx`, `LocalRef`, and `LocalAnalyzer` (`mir/mod.rs`, `mir/analyze.rs`, `mir/locals.rs`)

`codegen_mir` (`compiler/rustc_codegen_ssa/src/mir/mod.rs:203-393`) lowers a
function body in five sequential phases:
1. **Reverse-postorder traversal & landing-pad elision (`mir/mod.rs:291-321`):**
  Computes `traversal_order = traversal::mono_reachable_reverse_postorder(mir,
  tcx, instance)` (`mir/mod.rs:291`).
2. **Non-SSA local analysis (`mir/mod.rs:323`):** Calls `let memory_locals =
  analyze::non_ssa_locals(&fx, &traversal_order)` to obtain a
  `DenseBitSet<mir::Local>` of all locals that require a stack `alloca`.
3. **Prologue & argument lowering (`mir/mod.rs:326-332, 457-666`):** Creates a
  prologue basic block `Bx::build(cx, start_llbb)` and invokes
  `arg_local_refs(&mut bx, &fx, &memory_locals)` to bind `mir.args_iter()`
  according to `fn_abi.args`.
4. **Return place & local table initialization (`mir/mod.rs:334-368`):**
  Initializes `RETURN_PLACE` (`_0`) and each variable/temporary in
  `mir.vars_and_temps_iter()` as `LocalRef::Place(PlaceRef::alloca(&mut bx,
  layout))` if `memory_locals.contains(local)` or `LocalRef::PendingOperand` if
  SSA.
5. **Single-pass RPO block lowering (`mir/mod.rs:380-383`):** Iterates `for bb
  in traversal_order { fx.codegen_block(bb); }`. Because reverse postorder
  visits every dominator before any block it strictly dominates, every
  `PendingOperand` is guaranteed to be replaced via `overwrite_local` before any
  dominated use is lowered.

In `analyze::non_ssa_locals` (`mir/analyze.rs:17-407`), `LocalAnalyzer`
maintains `locals: IndexVec<mir::Local, LocalKind>` (`ZST`, `Memory`, `Unused`,
`SSA(DefLocation)`):
- A first assignment to a `Scalar`, `ScalarPair`, or `SimdVector` local
  transitions `Unused -> SSA(location)`; a second assignment or any
  non-dominated read or address-taking use (`Store`, `SetDiscriminant`,
  `Borrow`, `RawBorrow`, `Projection` other than `Field`/single-variant
  `Downcast`) transitions the local to `LocalKind::Memory`.
- If a projection starts with `ProjectionElem::Deref`
  (`is_indirect_first_projection()`, `mir/analyze.rs:120-127`), only the pointer
  base local is read (`COPY_CONTEXT`), allowing the pointer local itself to
  remain `LocalKind::SSA` even when its pointee is mutated or borrowed.

### 3.2 `TagEncoding::Direct` and `TagEncoding::Niche` Discriminant Lowering (`mir/place.rs:478-534`, `mir/operand.rs:458-699`)

- **`codegen_tag_value` (`mir/place.rs:478-534`):**
  - For `TagEncoding::Direct`: returns `Some((tag_field,
    const_uint_big(tag_llty, discr_val)))`.
  - For `TagEncoding::Niche { untagged_variant, niche_variants, niche_start }`:
    if `variant_index == untagged_variant`, returns `Ok(None)` (the payload's
    own valid bit pattern serves as the discriminant); otherwise computes
    `niche_value = ((variant_index - niche_variants.start) as
    u128).wrapping_add(niche_start) & niche_layout.size.unsigned_int_max()` and
    returns `Ok(Some((tag_field, niche_llval)))`.
- **`OperandRef::codegen_get_discr` (`mir/operand.rs:458-699`):**
  - Extracts or loads the tag scalar `tag_op` at `tag_field`.
  - Computes `relative_max = niche_variants.end().as_u32() -
    niche_variants.start().as_u32()`.
  - Computes `relative_discr = bx.sub(tag_llval, niche_start)` (modular wrapping
    subtraction), checks `is_niche` via `IntULE(relative_discr, relative_max)`,
    adds `niche_variants.start()`, and emits `bx.select(is_niche, tagged_discr,
    untagged_variant)` (`mir/operand.rs:689`).

### 3.3 The Six Upstream-LLVM Workarounds & Clean-Slate `AnLLVM` Eliminations

| # | Upstream `rustc_codegen_ssa` / `rustc_codegen_llvm` Workaround | Exact Source Locations (`49d734536222bf28bb6d07d885b3a81d145981da`) | Clean-Slate `AnLLVM` Design |
| :--- | :--- | :--- | :--- |
| **1** | **`PassMode::Cast` Memory Bounce via Temporary `alloca`** | `mir/mod.rs:341-345, 603-606`, `rustc_codegen_llvm/src/abi.rs:251-282, 310-313`, `mir/block.rs:612-648, 2009-2013, 2058-2098, 2474-2586` | `AnLLVM` represents register words as `MaskedWord64` (per-byte/per-bit initialization mask) and provides first-class `pack_cast_regs(op, layout, cast_target)` and `unpack_cast_regs(reg_tuple, cast_target, layout)` instructions. Padding bytes remain `init = false` inside the register word without contaminating adjacent initialized field bytes (`init = true`), eliminating 4 `alloca`s and 2 `llvm.memcpy`s per C-ABI call site. |
| **2** | **`Rvalue::Cast(CastKind::Transmute)` Memory Bounce via `alloca`** | `FunctionCx::codegen_transmute_operand` (`mir/rvalue.rs:332-440`, fallback arm at `421-439`) and `codegen_transmute` (`mir/rvalue.rs:303-327`) | `AnLLVM`'s `bitcast_bytes(op, src_layout, dst_layout)` slices and concatenates `MaskedWord` byte ranges directly in SSA registers (`evalRegisterTransmute`), handling `Scalar <-> ScalarPair` and `Padded <-> u64` in 1 step with zero `alloca`s. |
| **3** | **Entry-Block Untyped `alloca` Hoisting + `llvm.lifetime.start/end`** | `mir/mod.rs:326-369`, `rustc_codegen_llvm/src/builder.rs:670-680, 1462-1468, 1911-1929`, `mir/place.rs:316-322`, `mir/statement.rs:72-85` | `AnLLVM` declares static stack frame slots in the function header (`FrameSlot(slot_id, size, align)`) and lowers `StorageLive(local)` / `StorageDead(local)` 1-to-1 to `AllocaLive(slot_id)` / `AllocaDead(slot_id)`. |
| **4** | **`SwitchInt` on Niche Discriminants and `icmp` + `@llvm.assume` Chains** | `OperandRef::codegen_get_discr` (`mir/operand.rs:458-699`, `llvm-project#134024` workaround at `588-597`), `codegen_switchint_terminator` (`mir/block.rs:429-565`) | `AnLLVM` provides a first-class `decode_niche_discr(tag, NicheConfig)` operation backed by the universal modular round-trip identity (`codegen_get_set_discr_niche_roundtrip`) and native `SwitchInt` across `i8`..`i128`. |
| **5** | **`noalias` / `readonly` / `dereferenceable` / `noundef` Attribute Juggling vs. Tree Borrows** | `rustc_ty_utils/src/abi.rs:322-420, 669-691`, `rustc_codegen_llvm/src/abi.rs:59-113`, `builder.rs:750-785`, `mir/retag.rs:1-536` | `AnLLVM` uses first-class Tree Borrows `BorrowTag` / `ProtectorId` annotations and bitmask `noundef_mask` attributes rather than C99 `restrict` metadata scopes. |
| **6** | **111 `BuilderMethods` Action Methods (`traits/builder.rs:51-690`)** | `compiler/rustc_codegen_ssa/src/traits/{builder.rs,abi.rs,intrinsic.rs,type_.rs,consts.rs}` | Partition cleanly into 8 `AnLLVM` instruction families: (1) CFG & Terminators (15), (2) Integer/Bitwise ALU + Overflow (28), (3) Floating-Point ALU (15), (4) Casts & Byte Pack/Unpack (24 + 3 new), (5) Stack Frame & Memory (23), (6) Atomics & Sync (6), (7) Calls, ABI & Unwinding (17), and (8) Validity & Tree Borrows Retags (13). |

### 3.4 Empirical `rustc --emit=mir,llvm-ir` Measurements (`support/empirical_probe.rs`, `support/empirical_probe_opt1_nollvm.ll`)

| Probe Function (`support/empirical_probe.rs`) | MIR Operation | Upstream `rustc_codegen_llvm` Output (`support/empirical_probe_opt1_nollvm.ll`) | Clean-Slate `AnLLVM` Output | `alloca` Reduction |
| :--- | :--- | :--- | :--- | :--- |
| `probe_pass_mode_cast_caller` | Construct `Padded { a, b }`, pass by value (`PassMode::Cast` `i64`), return result | **4 `alloca`s** (`%0, %1, %2, %_0`), **4 `lifetime.start/end`**, **2 `llvm.memcpy`**, 4 stores, 3 loads, 1 call (19 instructions) | `pack_cast_regs(a, b) -> %arg`, `call @probe_pass_mode_cast_modify(%arg) -> %ret`, `ret %ret` (**3 instructions, 0 `alloca`s**) | **4 -> 0 (-100%)** |
| `probe_pass_mode_cast_construct` | Return `Padded { a, b }` via `PassMode::Cast` (`i64`) | **1 `alloca`** (`%_0`), 2 stores, 1 GEP, 1 widened `load i64, ptr %_0, align 4`, `ret` (6 instructions) | `pack_cast_regs(a, b) -> %0`, `ret %0` (**2 instructions, 0 `alloca`s**) | **1 -> 0 (-100%)** |
| `probe_transmute_pair_to_u64` | `transmute::<(u32, u32), u64>(pair)` | **1 `alloca`** (`%0`), **2 `lifetime.start/end`**, 2 `store i32`, 1 GEP, 1 `load i64`, `ret` (8 instructions) | `bitcast_bytes(pair, Pair32ToU64) -> %0`, `ret %0` (**2 instructions, 0 `alloca`s**) | **1 -> 0 (-100%)** |
| `probe_transmute_u64_to_pair` | `transmute::<u64, (u32, u32)>(bits)` | **1 `alloca`** (`%0`), **2 `lifetime.start/end`**, 1 `store i64`, 2 `load i32`, 1 GEP, 2 `insertvalue`, `ret` (10 instructions) | `bitcast_bytes(bits, U64ToPair32) -> %0`, `ret %0` (**2 instructions, 0 `alloca`s**) | **1 -> 0 (-100%)** |
| `probe_transmute_padded_to_u64` | `transmute::<Padded, u64>(p)` | **1 `alloca`** (`%0`), **2 `lifetime.start/end`**, `store i8`, GEP, `store i32`, `load i64 !noundef`, `ret` (8 instructions; attaches `!noundef` to `load i64` across 3 uninitialized padding bytes at line 358!) | `bitcast_bytes(p, PaddedPairToWord64) -> %0`, `ret %0` (**2 instructions, 0 `alloca`s**, padding bytes explicitly `init = false`) | **1 -> 0 (-100%)** |

---

## 4. Mechanized Lean 4.34.1 Soundness Probes

Both standalone Lean 4.34.1 files in `support/` are verified with:
```bash
/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean \
  -j1 -M1024 -DElab.async=false -Ddebug.skipKernelTC=false <file.lean>
```
with exit code `0`, zero warnings, zero `sorryAx`, and zero `Lean.ofReduceBool`.

### 4.1 `support/support_mir_transform_adaptation_probe.lean` (`1,446` lines, SHA-256 `babfaffbfd0af65b0b9f0019767a793981a33ec378d6f548b22d8f7a007ff1d7`)

| Theorem / Definition | Section | Statement Summary | Axioms (`#print axioms`) |
| :--- | :--- | :--- | :--- |
| `Compiles.refl`, `Compiles.trans_right_id`, `Compiles.trans_id` | Section 1 | Reflexivity and transitivity of `Compiles` across `Language` and `BehaviorCodec`. | `[]` |
| `PassCompiler.compId`, `PassCompiler.thenOpt`, `CertChecker.toPassCompiler` | Section 1 | Verified sequential composition of `BB-8` `PassCompiler`s and `CertChecker`s. | `[]` / `[propext]` |
| `BehaviorOf.of_reachesPrefix` | Section 1 | Fuel-bounded small-step reachability implies relational `BehaviorOf` (`Trusted/StepResult.lean`). | `[]` |
| `mirSroa_compiles` | Section 3 | **Positive Theorem (`MirSROA`):** Flattening non-address-taken aggregate `_2` into scalar leaf locals `_20, _21` satisfies `Compiles MirLang MirLang (idCodec MirLang)` for all `k0, k1 : Int` and all input contexts. | `[propext]` |
| `canary_sroa_on_address_taken_local_unsound` | Section 3 | **Negative Canary (`MirSROA`):** Applying `MirSROA` to an address-taken aggregate (`isAddressTaken 2 = true`) steps to `.ub` on a well-defined source program, violating `Compiles`. | `[propext]` |
| `destProp_with_live_union_compiles` | Section 4 | **Positive Theorem (`DestinationPropagation`):** Coalescing `_3 = move _2` while unioning `StorageLive` intervals satisfies `Compiles MirLang MirLang (idCodec MirLang)` for all `k : Int`. | `[propext]` |
| `canary_destProp_without_live_union_violates_compiles` | Section 4 | **Negative Canary (`rust-lang/rust#146383`):** Coalescing `_3 = move _2` while deleting `StorageLive(2)` instead of unioning `StorageLive(3)` writes to a `.dead` destination local (`.ub`), violating `Compiles`. | `[propext]` |
| `elaborateDrops_compiles` | Section 5 | **Positive Theorem (`ElaborateDrops`):** Lowering `PreDropMirLang` (unconditional move + conditional move of owned `Guard` resources) into `MirLang` with static dead-drop elision and dynamic boolean drop flag `_14` satisfies `Compiles PreDropMirLang MirLang preDropToMirCodec`. | `[propext, Quot.sound]` |
| `canary_elaborateDrops_missing_move_clear_unsound` | Section 5 | **Negative Canary (`ElaborateDrops`):** Omitting the drop-flag clear (`_14 := 0`) on `Operand.move` causes a double-drop (`.ub`) on the early-move branch, violating `Compiles`. | `[propext]` |
| `mirCleanupAndOptPipeline_compiles` | Section 6 | End-to-end composed `PassCompiler` (`ElaborateDrops ∘ MirSROA ∘ DestinationPropagation`) soundness theorem from `PreDropMirLang` to `MirLang`. | `[propext, Quot.sound]` |

### 4.2 `support/support_mir_to_anllvm_lowering_probe.lean` (`1,589` lines, SHA-256 `bd801a91140089fe6bef519fbff256f93c418bb1052eb94d4e37f8d0c79c5d1a`)

| Theorem / Definition Name | Lines | Role & Statement Summary | Axioms |
| :--- | :--- | :--- | :--- |
| `Compiles.execStar_sim` | `160-172` | Lifts lockstep `Compiles L1 L2 S1 S2 codec p1 p2` to multi-step `ExecStar` traces. | `[propext]` |
| `wrappingSubMod_wrappingAddMod_cancel` | `424-454` | Proves `((start + d) mod M + M - (start mod M)) mod M = d` for all $M > 0, d < M$, including when `start + d >= M` wraps around $0$. | `[propext, Quot.sound]` |
| `codegen_get_set_discr_niche_roundtrip` | `536-544` | Full universal round-trip soundness of `TagEncoding::Niche` discriminant encoding and decoding across all tagged and untagged enum values. | `[propext, Quot.sound]` |
| `lowerMirRvalue_correct` | `1070-1109` | Proves that evaluating `lowerMirRvalue kinds rv` in `AnLLVM` matches `evalMirRvalue mirEnv rv` in MIR under `EnvSimRel kinds`. | `[propext]` |
| `analyze_local_ssa_vs_alloca_simulation` | `1190-1263` | Proves single-step lockstep simulation of `lowerMirStmt kinds` across `storageLive`, `storageDead`, `assignSsa`, `storePlace`, `setDiscriminantNiche`, `assertZero`, and `condBranch`. | `[propext, Quot.sound]` |
| `lowerMirToAnLlvm_compiles` | `1304-1348` | Proves `Compiles MirLang AnLLVMLang MirSemantics AnLLVMSemantics (mirToAnLlvmCodec kinds) body (lowerMirStmts kinds body)`. | `[propext, Quot.sound]` |
| `pack_padded_preserves_byte_init_masks` | `1374-1383` | Proves that packing `PaddedReprC.mkInit a b` into `MaskedWord64` preserves `init = true` on bytes `0` and `4..7` and `init = false` on padding bytes `1..3`. | `[]` |
| `register_transmute_and_cast_eliminates_alloca` | `1399-1434` | Proves that `AnLLVM` register-level `bitcastBytes` and `packPaddedToWord64` refine MIR `Transmute` and `PassMode::Cast` in 1 step with zero stack `alloca`s. | `[propext, Quot.sound]` |
| `canary_multi_def_local_as_ssa_without_phi_unsound` | `1506-1560` | **Negative Canary:** Proves that classifying a branched mutating local (`acc`) as `.ssaOperand` in single-pass RPO lowering without `alloca` or $\phi$ placement causes the join block to observe the wrong branch's SSA register (`0 ≠ 13`). | `[propext]` |
