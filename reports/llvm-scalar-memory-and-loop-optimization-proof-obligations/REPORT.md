# LLVM 23.1.1 Scalar, Memory, Loop, and Vectorization Optimizations: Algorithms, Analyses, Bug History, and Proof Obligations

## Summary

To match the runtime performance of `rustc` `1.99.1` (`-O2`/`-O3`) in a verified compiler or certifying LLVM pipeline, an architecture must discharge the proof obligations of 30 parity-critical scalar, memory, loop, and vectorization passes in LLVM 23.1.1 (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`). Direct inspection of their LLVM 23.1.1 implementations (`support/scalar_memory_loop_pass_metrics.json`) establishes that their verification complexity partitions into four distinct proof regimes:

1. **Local Algebraic & Bitvector Rewrite Passes (`InstCombine` `56,238` LOC / `1,559` mutation sites; `AggressiveInstCombine` `3,227` LOC / `92` sites; `Reassociate` `2,533` LOC; `BDCE` `148` LOC; `VectorCombine` `6,631` LOC / `140` sites)**:
   - Driven by worklist-based DAG pattern matching plus `ValueTracking` (`computeKnownBits`, `isKnownNonZero`, `SimplifyDemandedBits`, `9,884` LOC) and `InstructionSimplify` (`7,125` LOC).
   - **Proof obligation**: Forward expression refinement ($e_{\text{src}} \sqsubseteq e_{\text{tgt}}$) under poison/undef lattice semantics (`nuw`, `nsw`, `exact`, `disjoint`, `noundef`). Requires zero loop invariants or global heap invariants; SMT bitvector translation validation (Alive2) or verified rewrite rules (Alive-in-Lean / CompCert `Constprop`) discharge $>98\%$ of rules, while pointer/GEP folds require provenance preservation.

2. **SSA Value Numbering, Range/Constraint Propagation, and CFG Threading (`EarlyCSE` `1,924` LOC; `GVN` `4,073` LOC; `SCCP` `2,718` LOC; `CorrelatedValuePropagation` + `LazyValueInfo` `3,502` LOC; `ConstraintElimination` `1,953` LOC; `JumpThreading` `3,300` LOC; `SimplifyCFG` `9,553` LOC; `ADCE` `748` LOC; `TailRecursionElimination` `1,069` LOC)**:
   - Combine dominator-tree scoped hash tables, abstract interpretation over constant/range lattices, linear integer Fourier-Motzkin / simplex systems (`ConstraintElimination`, which eliminates Rust slice bounds checks), and CFG edge duplication/folding.
   - **Proof obligation**: Relational simulation with path-sensitive predicates and dominance witnesses. Historically a major source of LLVM miscompilations (`GVN` equality propagation across `icmp eq ptr` conflating distinct pointer provenances, `SimplifyCFG` speculating trapping or poison-producing instructions before `freeze`, `JumpThreading` violating loop-header dominance).

3. **Stack Promotion, Aggregate Scalarization, and Memory Store/Copy Elimination (`SROA` `6,422` LOC / `130` sites; `PromoteMemoryToRegister` / `mem2reg` `1,353` LOC; `DeadStoreElimination` `2,520` LOC; `MemCpyOptimizer` `2,284` LOC; `MergedLoadStoreMotion` `384` LOC)**:
   - Rely on `AllocaInst` slice partitioning (`SROA`), iterated dominance frontiers (`PromoteMemToReg`), and backward/forward `MemorySSA` (`2,487` LOC) + `BatchAA` (`BasicAliasAnalysis` `2,175` LOC, `ScopedNoAliasAA` `204` LOC) walks.
   - **Proof obligation**: Memory-injection splitting/shrinking (simulating unescaped `alloca` blocks by pure SSA registers as in Vellvm `Promotable` and CompCert `SimplLocals`) and disjointness/overwrite proofs (`MustAlias` / `NoAlias`) witnessing that eliminated or forwarded stores/copies are unobservable on all normal and unwinding paths.

4. **Loop Canonicalization, `ScalarEvolution`, Loop Transforms, and Vectorization (`LoopSimplify` `885` LOC; `LCSSA` `523` LOC; `LoopRotation` `1,068` LOC; `LICM` `3,064` LOC; `IndVarSimplify` `4,394` LOC; `LoopUnroll` `3,962` LOC; `SimpleLoopUnswitch` `3,814` LOC; `LoopIdiomRecognize` `3,606` LOC; `LoopDeletion` `392` LOC; `LoopStrengthReduce` `7,178` LOC; `ScalarEvolution` `17,453` LOC; `LoopVectorize` + `VPlan` + `LoopAccessAnalysis` `14,007` LOC; `SLPVectorizer` `33,278` LOC)**:
   - Driven by `ScalarEvolution` (`SCEVAddRecExpr` polynomial recurrences $\{\text{start}, +, \text{step}\}_L$ and backedge-taken counts) and `LoopAccessAnalysis` (pointer stride/distance dependence checks and runtime `SCEVPredicate` / pointer-disjointness guards).
   - **Proof obligation**: Relational stuttering/unfolding simulations over CFG loops, induction-variable recurrence equivalence Modulo $2^w$ with `nsw`/`nuw` no-wrap certificates, dead-store/loop-invariant memory promotion with `freeze` insertion (to prevent speculative poison stores in `LICM`), and SIMD lane-lockstep simulation for `LoopVectorize` and `SLPVectorizer`.

## Applicability

These findings apply to LLVM 23.1.1 (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`) as invoked by `rustc` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`). Source line counts, mutation site counts, and analysis queries are measured directly from `llvm/lib/Transforms/` and `llvm/lib/Analysis/` at revision `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145` (`support/scalar_memory_loop_pass_metrics.json`).

## Findings

### 1. Scalar, Algebraic, and CFG Optimizations

**Basis: source + normative + derived**

#### 1.1 `InstCombine` (`lib/Transforms/InstCombine/`, `56,238` LOC, `1,559` mutation sites) & `AggressiveInstCombine` (`3,227` LOC, `92` mutation sites)
- **Algorithm**: `InstCombinePass` (`InstCombineInternal.h`, `InstructionCombining.cpp`) maintains an `InstCombineWorklist` in reverse post-order. For each instruction $I$, it first invokes pure non-mutating simplification (`simplifyInstruction` in `lib/Analysis/InstructionSimplify.cpp`, `7,125` LOC); if that returns a replacement `Value*`, it performs RAUW. Otherwise, `InstCombinerImpl::visit<Opcode>` dispatches across 14 per-opcode visitor files (`InstCombineAddSub.cpp`, `InstCombineAndOrXor.cpp`, `InstCombineCompares.cpp`, `InstCombineCasts.cpp`, `InstCombineLoadStoreAlloca.cpp`, `InstCombineSelect.cpp`, `InstCombineShifts.cpp`, `InstCombineCalls.cpp`, etc.), querying `ValueTracking` (`computeKnownBits`, `SimplifyDemandedBits`, `SimplifyDemandedVectorElts`, `isKnownNonZero`, `haveNoCommonBitsSet`). `AggressiveInstCombine` runs at `-O3` and performs multi-instruction DAG reductions (truncation expression DAGbitwidth shrinking `TruncInstCombine`, popcount/bswap/bitreverse idiom recognition, and load-merge combining).
- **Analyses relied on**: `AssumptionCache` (`@llvm.assume`), `TargetLibraryInfo`, `DominatorTree`, `DataLayout`, `AAResults` (optional, for load/store combines), and `ValueTracking`.
- **Correctness argument**: Local denotational value refinement ($\llbracket I_{\text{tgt}} \rrbracket_\sigma \sqsubseteq \llbracket I_{\text{src}} \rrbracket_\sigma$): in every state $\sigma$, if $I_{\text{src}}$ does not trigger immediate UB, $I_{\text{tgt}}$ does not trigger immediate UB, and whenever $I_{\text{tgt}}$ evaluates to `poison`, $I_{\text{src}}$ also evaluated to `poison` (or `undef` with a compatible bit-choice).
- **Bug history (including Alive2)**: `InstCombine` has the largest bug count of any LLVM pass in Alive2's PLDI 2021 study (>400 bugs reported across LLVM history). Recurring bug classes include:
  1. **Poison introduction from `select` $\rightarrow$ arithmetic/bitwise folds**: Rewriting `select %c, %x, 0` into `and (sext %c), %x` makes the result `poison` when `%x` is `poison` even if `%c == false` (fixed in LLVM by requiring `impliesPoison` or restricting `select` to logical `and`/`or` removal).
  2. **`undef` multi-use correlation**: Rewriting `x + x` (where `x = undef`) into `x << 1` restricts the result to even integers, which is a valid refinement of `undef`, whereas rewriting `(x & 1) ^ ((x & 1) ^ 1)` assuming both occurrences of `x` pick the same bit from `undef` is **unsound** if `x` is `undef`.
  3. **GEP `inbounds` / `nuw` / `nusw` and pointer provenance**: Folding `inttoptr(ptrtoint(p))` to `p` is unsound when `p` is out-of-bounds of its original allocation and aliases an adjacent allocation (`llvm/llvm-project#34548`).
- **Verified precedents**: Alive / Alive2 (Lopes et al., PLDI 2015 / PLDI 2021); CompCert `ConstpropOp` & `CombineOp` (`backend/Constpropproof.v`); Crellvm (`InstCombine` hint emitters for algebraic and bitcast rewrites).
- **Derivation facts needed**: The matched source expression DAG (`k`-step def-use cone, typically $k \le 5$), any `KnownBits` / `NonZero` / `NoWrap` lemmas derived from dominating `@llvm.assume` or branch conditions (with dominance paths), and a finite bitvector SMT or rewrite-rule theorem establishing `src_dag ⊑ tgt_dag`.

#### 1.2 `EarlyCSE` (`1,924` LOC, `12` mutation sites) & `GVN` (`4,073` LOC, `16` mutation sites)
- **Algorithm**:
  - `EarlyCSE` (`lib/Transforms/Scalar/EarlyCSE.cpp`) performs a single preorder traversal of the `DominatorTree` maintaining scoped hash tables (`ScopedHashTable`) for pure scalar expressions, loads (tagged by `MemorySSA` `MemoryAccess` generation or a monotonic store counter when `memssa` is disabled), and calls (`readonly`/`readnone`).
  - `GVN` (`lib/Transforms/Scalar/GVN.cpp`) assigns global value numbers (`LeaderTable`) across basic blocks, performs **Partial Redundancy Elimination (PRE)** (`performPRE` / `PerformLoadPRE`) by inserting loads/expressions on incoming critical edges where a value is available on some but not all predecessors, and propagates branch equality (`propagateEquality`, replacing `%x` with `%y` in the `true` successor of `icmp eq %x, %y`).
- **Analyses relied on**: `DominatorTree`, `AssumptionCache`, `TargetLibraryInfo`, `TargetTransformInfo`, `AAResults`, `MemorySSA` (`EarlyCSE<memssa>`), `MemoryDependenceResults` (`GVN`), `LoopInfo`.
- **Correctness argument**: If instruction $I_1$ dominates $I_2$, both compute pure expression $E$ on identical operand values, and (for loads) no intervening memory write may alias the loaded location $(p, \text{size})$ along any path from $I_1$ to $I_2$, then $\llbracket I_1 \rrbracket = \llbracket I_2 \rrbracket$, provided any intersection of poison-generating flags (`nsw`, `nuw`, `exact`, `inbounds`) and metadata (`!range`, `!nonnull`, `!noundef`) on $I_1$ is relaxed to the intersection of $I_1$ and $I_2$ (`patchReplacementInstruction` in `Local.cpp`).
- **Bug history (including Alive2)**:
  1. **Pointer equality provenance bug (`llvm/llvm-project#35229`, Ralf Jung / Alive2)**: `GVN::propagateEquality` replaced `ptr %p` with `ptr %q` inside a dominated block after `icmp eq ptr %p, %q`. When `%p` is a one-past-the-end pointer of allocation $A$ and `%q` is the base address of adjacent allocation $B$, they have equal integer addresses (`icmp eq` is `true`) but distinct provenances; replacing `%q` with `%p` makes subsequent loads/stores through `%q` UB!
  2. **Missing flag/metadata stripping on dominating leader**: When $I_1$ had `nsw` (producing `poison` on overflow, unused on paths not reaching $I_2$) and $I_2$ did not have `nsw`, replacing $I_2$ with $I_1$ without clearing `nsw` on $I_1$ introduced UB.
  3. **Load PRE critical-edge speculation**: Speculating a load onto a predecessor edge where the pointer could be unaligned or out-of-bounds unless `isSafeToLoadUnconditionally` holds.
- **Verified precedents**: CompCert `CSEproof.v` (value numbering over RTL with `numbering` equations); Crellvm `GVN` / `EarlyCSE` relational post-validator using `propagate_eq` and `nop` hints; Tristan & Leroy Verified Value-Graph Translation Validation (POPL 2008 / PLDI 2009).
- **Derivation facts needed**:
  - For scalar CSE: `(leader_inst_id, eliminated_inst_id, dom_proof, flag_intersection_list)`.
  - For Load CSE: `(load1_id, load2_id, dom_proof, memssa_clobber_free_chain)` where each step in the `MemorySSA` chain has a `NoAlias(store_i, load2)` proof.
  - For Load PRE: the set of predecessor edges where loads were inserted, `AvailableValueInBlock` map, and non-trapping/dereferenceability proof on speculated edges.
  - For equality propagation: proof that the equality is either integer/float (and excludes `-0.0 == +0.0` for `fcmp oeq` unless bit-casts/signs cannot observe the difference) or pointer equality with identical provenance (`SameUnderlyingObject`).

#### 1.3 `SROA` (`6,422` LOC, `130` mutation sites) & `PromoteMemoryToRegister` / `mem2reg` (`1,353` LOC, `24` mutation sites)
- **Algorithm**:
  - `SROA` (`lib/Transforms/Scalar/SROA.cpp`) operates in three phases on each `alloca`:
    1. `AllocaSlices` analysis: scans all uses (GEPs, loads, stores, `llvm.memcpy`/`memset`, `lifetime.start`/`end`, `select`/`phi` speculation) and builds byte-interval slices $[b_{\text{begin}}, b_{\text{end}})$. If any use captures the pointer or uses a variable/non-constant offset that cannot be split, the slice is marked unpromotable.
    2. Partitioning (`partitionSlices`): splits overlapping/adjacent byte intervals into disjoint canonical partitions, rewriting aggregate loads/stores and `memcpy`s into per-field scalar/vector loads and stores (and inserting bitcasts/shifts for unaligned overlapping sub-slices).
    3. SSA Promotion (`promoteAllocas`): invokes `PromoteMemToReg` on all promotable single-value `alloca` partitions.
  - `PromoteMemToReg` (`lib/Transforms/Utils/PromoteMemoryToRegister.cpp`) computes the Iterated Dominance Frontier (`IDFCalculator`) of all blocks storing to an `alloca`, inserts `PHINode`s at dominance frontiers, and performs a single dominator-tree RPO walk renaming loads to the current reaching SSA definition (initializing uninitialized entry paths to `PoisonValue` or `UndefValue`).
- **Analyses relied on**: `DominatorTree`, `AssumptionCache`, `DataLayout`.
- **Correctness argument**: An `alloca` whose address never escapes (`isAllocaPromotable`) is disjoint from all global, heap, and caller stack memory. Its byte range can be bijectively partitioned into independent scalar cells, and standard Cytron et al. SSA construction preserves load-after-store dataflow.
- **Bug history**:
  - Byte-level poison vs value-level poison during sub-slice extraction: in LLVM IR, writing a `poison` `i8` into byte 0 of an `i32` `alloca` and reading the `i32` via `SROA`'s shift-and-OR bit-field reconstruction makes the entire `i32` `poison`, whereas reading byte 1 separately should not be `poison`.
  - Volatile loads/stores or non-byte-sized integers (`i1`, `i19` padding bits) losing or fabricating bits across `SROA` `convertValue` bitcasts.
- **Verified precedents**: Vellvm `Promotable` (`mem2reg` verification in Coq, Zhao et al., POPL 2012 &POPL 2013); CompCert `SimplLocalsproof.v` (lifting non-address-taken stack blocks into `PTree` local variables with a `mem_inject` simulation); Crellvm `SROA`/`mem2reg` hints.
- **Derivation facts needed**:
  - Non-escape witness (`∀ u ∈ uses(alloca), is_direct_load_store_or_dead_lifetime(u)`).
  - Partition map: `[(offset, size, new_alloca_or_ssa_reg)]`.
  - Reaching-definition map per basic block entry/exit (`bb -> ssa_val`) verifying that every `phi` and replaced `load` equals the reaching store along all predecessor edges.

#### 1.4 `SimplifyCFG` (`9,553` LOC across `SimplifyCFGPass.cpp` + `Utils/SimplifyCFG.cpp`, `168` mutation sites)
- **Algorithm**: Iteratively transforms basic blocks until fixpoint:
  1. Removes unreachable blocks (`removeUnreachableBlocks`).
  2. Merges a block into its unique predecessor when the predecessor has a single successor (`MergeBlockIntoPredecessor`).
  3. Folds conditional branches on constants into unconditional branches and threads trivial empty blocks.
  4. Converts two-way branches with small side-effect-free bodies into `select` instructions (`FoldTwoEntryPHINode` / `SpeculativelyExecuteBB`), guarded by `isSafeToSpeculativelyExecute`.
  5. Hoists identical instructions from `then`/`else` successors into the branch block (`HoistThenElseCodeToIf`) and sinks common trailing instructions (`SinkCommonCodeFromPredecessors`).
  6. Converts `switch` instructions into lookup tables (`SwitchToLookupTable` — disabled when `no-switch-to-lookup` is set), bitmask tests, or arithmetic range checks (`ConvertSwitchRangeToICmp`).
- **Analyses relied on**: `TargetTransformInfo` (cost of speculation/lookup tables), `DominatorTree` (updated via `DomTreeUpdater`), `AssumptionCache`, `DataLayout`.
- **Correctness argument**: Graph-structural bisimulation (`MergeBlockIntoPredecessor`, constant branch folding) plus guarded instruction speculation: speculating instruction $I$ across `br i1 %cond` into `select %cond, %v_true, %v_false` is sound iff $I$ cannot trigger immediate UB (e.g., division by zero, trapping load, `unreachable`) and if `%cond` is `poison`, `select` semantics propagate `poison` (or in LLVM's semantics where `br poison` is immediate UB while `select poison, a, b` is `poison`, replacing `br %cond` with `select %cond` is a valid refinement because `select` has *less* UB than `br`!).
- **Bug history (including Alive2)**:
  - **Speculating instructions across `br` when operands may be poison (`select` poison leak)**: While `br poison` is UB, if `%cond` is a valid boolean (`true`), and the untaken branch computes `%y` which is `poison`, `select true, %x, poison` evaluates to `%x` in LLVM IR, *unless* `%y` had an instruction that triggers immediate UB (e.g. `udiv i32 1, 0` or `sdiv i32 INT_MIN, -1` or a dereference of an invalid pointer). Alive2 found multiple cases where `isSafeToSpeculativelyExecute` misclassified trapping/UB operations or where hoisting common loads/stores (`HoistThenElseCodeToIf`) dropped `!nonnull` / `!range` / `inbounds` or speculated past a synchronization action.
- **Verified precedents**: CompCert `Tunnelingproof.v`, `CleanupLabelsproof.v`, and `IfConversion`.
- **Derivation facts needed**: Explicit CFG block mapping $\pi : \text{Block}_{\text{tgt}} \to \mathcal{P}(\text{Block}_{\text{src}})$, proof of `isSafeToSpeculativelyExecute` for every hoisted/select-converted instruction, and `freeze` insertion witness whenever a switch-to-arithmetic or lookup-table transformation duplicates a potentially-poison condition variable.

#### 1.5 `DeadStoreElimination` (`DSE`, `2,520` LOC, `14` mutation sites) & `MemCpyOptimizer` (`2,284` LOC, `29` mutation sites)
- **Algorithm**:
  - `DSE` (`lib/Transforms/Scalar/DeadStoreElimination.cpp`, `DSEState`) uses `MemorySSA` (`MemoryDef` / `MemoryPhi`) to perform two eliminations:
    1. **Overwrite DSE (`eliminateDeadStores`)**: Walks backward through `MemorySSA` from a `KillingDef` store $S_2$ to find earlier `DeadDef` stores $S_1$ such that $S_2$ completely overwrites $S_1$'s byte range (`isCompleteOverwrite` / `isPartialOverwrite` shrinking `memset`/`memcpy` bounds) and no `MemoryUse` (load/call) may read $S_1$ along any path from $S_1$ to $S_2$ (`isOverwrite` + post-dominance check via `PostDominatorTree`).
    2. **End-of-function stack DSE (`handleEndOfFunction`)**: Walks backward from function exit (`ret` / `resume` / `unreachable`) or `llvm.lifetime.end` to delete stores to non-escaped local objects (`alloca`, `byval`, `dead_on_return`, or `dead_on_unwind` parameters) that are never read before deallocation.
  - `MemCpyOptimizer` (`lib/Transforms/Scalar/MemCpyOptimizer.cpp`) performs:
    1. Store-to-`memset` formation (`processStore`: merges adjacent scalar stores of the same byte value into `@llvm.memset`).
    2. `memcpy`-to-`memcpy` forwarding (`processMemCpyMemCpyDependence`: if `memcpy(B, A, n)` is followed by `memcpy(C, B, n)` with no intervening modification of `A` or `B`, rewrites the second copy to `memcpy(C, A, n)` or `memmove(C, A, n)`).
    3. **Call-Slot Optimization (`performCallSlotOptzn`)**: When `call @f(ptr sret(%T) %tmp)` (or a call initializing `%tmp`) is immediately followed by `memcpy(%dest, %tmp, sizeof(%T))`, and `%dest` is `dereferenceable(sizeof(%T))`, aligned, and `NoAlias` with all arguments/globals accessed by `@f`, rewrites the call to write directly into `%dest` (`call @f(ptr sret(%T) %dest)`) and deletes the `memcpy`!
    4. `byval` argument forwarding (`processByValArgument`): if a `readonly` `byval` argument is copied from an unmodified source `%src`, passes `%src` directly if alignment permits.
- **Analyses relied on**: `MemorySSA`, `AAResults` (`BatchAA`), `DominatorTree`, `PostDominatorTree` (`DSE`), `TargetLibraryInfo`, `AssumptionCache`.
- **Correctness argument**: Observational memory equivalence on visible (escaped/returned) memory blocks at function exit and at every external/observable call or volatile access.
- **Bug history (including Alive2)**:
  - **Call-Slot Optimization on unwinding calls (`llvm/llvm-project#50806`)**: If `@f` writes partially to its destination pointer and then unwinds (`invoke`), and the caller inspects `%dest` in the `landingpad` / `cleanuppad`, redirecting `@f` to write directly into `%dest` instead of local `%tmp` makes the partial writes observable on unwind! That exact bug motivated adding the `dead_on_unwind` and `writable` attributes in LLVM (`LangRef.md:1815-1915`).
  - **DSE across potentially non-terminating loops**: If $S_2$ post-dominates $S_1$ in the CFG, but a `mustprogress`-free infinite loop lies between $S_1$ and $S_2$ and another thread or signal handler could observe $S_1$ (or an I/O call inside the loop reads $S_1$), $S_1$ is not dead.
- **Verified precedents**: CompCert `Deadcodeproof.v` (backward `needness` static analysis over `nmem` tracking dead stores to stack/unaliased blocks); Crellvm `DSE` & `MemCpyOpt` Relational post-validators.
- **Derivation facts needed**:
  - For Overwrite DSE: `(S1, S2, MustAlias_offset_interval_proof, PostDom_and_FinitePath_proof, NoInterveningMayRead_MemorySSA_walk)`.
  - For Stack-Exit DSE: `(S1, NonEscapedAlloca_or_DeadOnReturn_proof, NoMayReadUntilExitOrLifetimeEnd_proof)`.
  - For Call-Slot Optimization: `(call_inst, memcpy_inst, dest_deref_align_proof, dest_NoAlias_callee_modref_proof, dead_on_unwind_or_nounwind_proof)`.

#### 1.6 `CorrelatedValuePropagation` (`CVP`, `1,404` LOC, `72` mutation sites) & `LazyValueInfo` (`LVI`, `2,098` LOC)
- **Algorithm**: `LVI` (`lib/Analysis/LazyValueInfo.cpp`, `LazyValueInfoImpl`) computes a demand-driven backwards-cached abstract domain (`ValueLatticeElement`: `unknown`, `undef`, `constant(C)`, `notconstant(C)`, `constantrange( [lo, hi) )`) over integer and pointer values per basic block and CFG edge (`getValueAt`, `getValueInBlock`, `getValueOnEdge`, `getPredicateAt`). `CVP` (`lib/Transforms/Scalar/CorrelatedValuePropagation.cpp`) queries `LVI` to:
  1. Fold `icmp` / `select` / `switch` when edge ranges decide the predicate.
  2. Narrow `sdiv`/`srem` to `udiv`/`urem` when both operands are proved $\ge 0$ (`processSDiv`, `processSRem`), and narrow 64-bit `udiv`/`urem` to 32-bit when operands fit in `u32`.
  3. Attach `nsw` / `nuw` flags to `add`/`sub`/`mul`/`shl`, `nonnull` to loads/call args, and `samesign` to `icmp`.
- **Analyses relied on**: `LazyValueInfo`, `DominatorTree`, `AssumptionCache`.
- **Correctness argument**: Sound abstract interpretation over the product domain of `ConstantRange` ($2^w$-modular intervals) along CFG edges, guarded by `freeze` / non-poison provenance of branch conditions: if `br i1 (icmp slt %x, 10), label %T, label %F` branches to `%T`, then `%x` cannot evaluate to $\ge 10$ without having made the `br` condition `false` or `poison` (which is immediate UB at `br`).
- **Bug history (including Alive2)**:
  - **Correlated range bleed across non-`noundef` values or multiple uses of `undef`/`poison`**: If `%c = icmp ult %x, 10` is combined via bitwise `and`/`or` (rather than `select` or direct `br`) before branching, `%x` being `poison` does not necessarily make the `or` condition `poison` (`or true, poison` can be folded if frozen, or in older LLVM `and false, poison -> false`). `LVI::getEdgeValueLocal` must track whether the branch condition is a *poison-propagating* function of `%x` (`isGuaranteedNotToBeUndefOrPoison`).
- **Derivation facts needed**: For each simplified instruction or added `nsw`/`nuw` flag at program point $p$, the path-condition conjunction $\bigwedge_i (\text{edge}_i : \text{pred}_i(x))$ dominating $p$ and a `ConstantRange` inclusion lemma $\bigcap_i \text{Range}(\text{pred}_i) \subseteq \text{TargetRange}$.

#### 1.7 `ConstraintElimination` (`1,953` LOC, `6` mutation sites) — Bounds-Check Elimination
- **Algorithm**: `ConstraintEliminationPass` (`lib/Transforms/Scalar/ConstraintElimination.cpp`) traverses the `DominatorTree` in DFS order, maintaining two linear constraint systems (`ConstraintSystem`, one for `signed` $\mathbb{Z}$ and one for `unsigned` $\mathbb{N}_0$) using `DFSIn`/`DFSOut` dominance intervals:
  1. Linearizes integer comparisons (`icmp ule/ult/uge/ugt/sle/slt/sge/sgt`) and `GEP` / `add nuw` / `add nsw` / `sub nuw` / `zext` / `sext` expressions into affine inequalities $\sum_{j=1}^k c_j v_j \le b$ (`decompose`).
  2. Pushes inequalities from dominating branch edges (`br i1 %cmp`), `@llvm.assume(%cmp)`, and loop guards onto a priority worklist ordered by `DFSIn`.
  3. For each candidate `icmp` in the current block (most notably Rust slice bounds checks `icmp ult %idx, %len`), queries `ConstraintSystem::isConditionImplied` (which uses exact 64-bit integer Fourier-Motzkin variable elimination) to check whether the active dominating constraints entail the `icmp` (returning `true`) or its negation (returning `false`).
- **Analyses relied on**: `DominatorTree`, `LoopInfo`, `ScalarEvolution`, `OptimizationRemarkEmitter`.
- **Correctness argument**: If affine inequalities $A \vec{v} \le \vec{b}$ hold in exact mathematical integers $\mathbb{Z}$ (which holds for $w$-bit bitvectors whenever every decomposed `add`/`sub`/`mul-by-const`/`gep` in the linear combination carries the required `nuw` or `nsw` no-wrap flag, or has a proven non-wrapping precondition inside the system), then any non-negative linear combination $\vec{\lambda}^T A \vec{v} \le \vec{\lambda}^T \vec{b}$ ($\vec{\lambda} \ge 0$, Farkas' Lemma) also holds.
- **Bug history (including Alive2)**:
  - **2's-complement wraparound during `decompose` (`llvm/llvm-project#58152`, `#61420`)**: Decomposing `gep inbounds ptr %p, i64 %idx` or `zext(add %a, %b)` into $\text{base} + \text{idx}$ in the unsigned constraint system when `%idx` could be negative (signed offset in `gep inbounds` without `nuw`) caused wraparound unsoundness where `ConstraintElimination` folded a live bounds check to `true`.
- **Verified precedents**: Farkas-lemma linear arithmetic certificates (`lia` / `omega` in Coq and Lean 4, where a certificate is simply the non-negative multiplier vector $\vec{\lambda} \in \mathbb{Q}_{\ge 0}^m$!).
- **Derivation facts needed**: This pass admits one of the cleanest proof certificates in the entire compiler: for each eliminated `icmp` $C$, emit the active dominating branch/assume literals $\{L_1, \dots, L_m\}$, the no-wrap decomposition lemmas showing each $L_i$ implies $\vec{a}_i \cdot \vec{v} \le b_i$ in $\mathbb{Z}$, and the Farkas coefficient vector $(\lambda_1, \dots, \lambda_m) \ge 0$! Checking a Farkas certificate in Lean 4 or a standalone checker takes $O(m \cdot k)$ integer multiplications with zero search.

#### 1.8 `JumpThreading` (`3,300` LOC, `29` mutation sites)
- **Algorithm**: `JumpThreadingPass` (`lib/Transforms/Scalar/JumpThreading.cpp`) scans basic blocks `BB` ending in a conditional `br` or `switch` whose condition `%cond` (or an operand feeding `%cond` within `BB` of cost $\le \text{BBDuplicateThreshold} = 6$) is known on at least one incoming edge $P \to \text{BB}$ via `PHINode` incoming constants or `LazyValueInfo::getPredicateOnEdge`. It duplicates the instructions of `BB` onto a new edge block $P \to \text{BB}' \to S_{\text{known}}$, bypassing `BB` and updating `SSAUpdater` and `DomTreeUpdater`.
- **Analyses relied on**: `LazyValueInfo`, `DominatorTree` (`DomTreeUpdater`), `LoopHeaders` (set of loop headers to avoid creating irreducible multi-entry loops), `TargetLibraryInfo`, `AAResults`.
- **Correctness argument**: Finite CFG unrolling/splitting (bisimulation): duplicating block `BB` for predecessor $P$ preserves trace semantics, and folding `BB'`'s terminator follows from the `LVI` edge predicate on $P \to \text{BB}$.
- **Bug history**:
  - **Duplicating `convergent` or `nodup` calls, or duplicating `@llvm.experimental.noalias.scope.decl`**: Duplicating `noalias.scope.decl` intrinsics across jump-threaded paths without cloning the metadata scope falsely asserts that two dynamic executions of the same lexical scope do not alias (`llvm/llvm-project#53608`).
- **Derivation facts needed**: The cloned block's instruction mapping to `BB`, the `LVI` edge proof on $P \to \text{BB}$, and `SSAUpdater` phi reconstruction witnesses.

#### 1.9 Additional Scalar Passes (`SCCP`, `BDCE`, `ADCE`, `Reassociate`, `TailRecursionElimination`)

| Pass (`llvm/lib/Transforms/Scalar/`) | LOC / Muts | Algorithm & Analyses | Proof Obligation & Bug History |
| :--- | ---: | :--- | :--- |
| `SCCP` (`SCCP.cpp` + `Utils/SCCPSolver.cpp`) | `2,718` LOC / `22` muts | Wegman-Zadeck optimistic sparse conditional constant & range propagation over `ValueLatticeElement` + executable CFG edge set (`DomTree`). | Fixed-point inflationary lattice check: verify at the final valuation that all reachable `phi`s/instructions evaluate within their assigned lattice element and unreachable edges have `false` branch conditions. |
| `BDCE` (`BDCE.cpp`) | `148` LOC / `1` mut | Uses `DemandedBits` analysis (`lib/Analysis/DemandedBits.cpp`, `582` LOC) to replace integer instruction operands whose demanded bitmask is `0` with `ConstantInt::getNullValue`, and strips `nsw`/`nuw` if sign/high bits become newly demanded. | Bitmask observational equivalence ($\forall v,\; \text{Demanded}(v) = 0 \implies \text{uses}(v)$ are invariant to $v$, provided `v` is frozen or `noundef`). Alive2 found bugs where replacing a dead operand with `0` failed to strip `nsw` on an upstream instruction whose output bits were partially used. |
| `ADCE` (`ADCE.cpp`) | `748` LOC / `9` muts | Marks instructions with side effects, may-not-return loops (unless `mustprogress` / `willreturn`), and return values as live, then walks data and control dependences (`PostDominatorTree` iterated post-dominance frontier) backward, deleting unmarked instructions and redirecting dead conditional branches to the live post-dominator. | Termination-sensitive backward slicing simulation. Control-dependence redirection is sound only when all bypassed loops are proven terminating or carry `mustprogress` (`llvm/llvm-project#30185`). |
| `Reassociate` (`Reassociate.cpp`) | `2,533` LOC / `15` muts | Assigns RPO ranks to variables (`BuildRankMap`), linearizes associative/commutative expression trees (`add`, `mul`, `and`, `or`, `xor`, `fadd`/`fmul` with `reassoc`), sorts operands by rank to expose constants and common subexpressions (`x + -x -> 0`, `x * c1 + x * c2 -> x * (c1 + c2)`), and drops `nsw`/`nuw` when reordering changes intermediate overflow behavior. | Commutative ring identity in $\mathbb{Z}/2^w\mathbb{Z}$ + mandatory stripping of `nsw`/`nuw` on reordered intermediate nodes (`ClearFlags`). |
| `TailRecursionElimination` (`TailRecursionElimination.cpp`) | `1,069` LOC / `11` muts | Marks non-alloca-capturing calls in tail position with `tail` (`markTails`), and transforms self-recursive tail calls (including accumulator-convertible `ret (op %acc, (call @self(...)))`) into a loop header with `PHINode`s for arguments and accumulators. | Stack-frame non-escape proof (no live `alloca` in the caller is referenced by or after the tail call; `EscapeEnumerator`) + monoid associativity/commutativity for accumulator recursion elimination. |

---

### 2. Loop Canonicalization, `ScalarEvolution`, Loop Optimizations, and Vectorization

**Basis: source + normative + derived**

#### 2.1 Loop Canonicalization: `LoopSimplify` (`885` LOC), `LCSSA` (`523` LOC), and `LoopRotation` (`1,068` LOC)
- **`LoopSimplify` (`lib/Transforms/Utils/LoopSimplify.cpp`)**: Ensures every natural loop $L$ has:
  1. A unique **preheader** (splitting the header's outside incoming edges if $>1$).
  2. A single **backedge / latch** (merging multiple latches into a single latch block).
  3. **Dedicated exit blocks** (every exit block of $L$ has all its predecessors inside $L$).
- **`LCSSA` (Loop-Closed SSA, `lib/Transforms/Utils/LCSSA.cpp`)**: For every value `%v` defined inside loop $L$ and used outside $L$, inserts single-operand (or multi-predecessor) `PHINode`s `%v.lcssa = phi [%v, %exit_pred]` at the top of $L$'s dedicated exit blocks and rewrites all outside uses of `%v` through `%v.lcssa`. This isolates loop mutations (such as unrolling, rotation, or deletion) from outside SSA users.
- **`LoopRotation` (`lib/Transforms/Scalar/LoopRotation.cpp` + `Utils/LoopRotationUtils.cpp`)**: Transforms a `while`-style loop (`preheader -> header (cond) -> body -> latch -> header`) into a `do-while` loop wrapped in a zero-trip guard (`preheader -> guard (cond) -> preheader.split -> body -> latch (cond) -> body`), cloning the original header instructions into the preheader guard and updating SSA via `SSAUpdaterBulk`.
- **Proof obligations**: Pure CFG structural transformations. `LoopSimplify` and `LCSSA` are local block-splitting / trivial-$\phi$ bisimulations; `LoopRotation` is a 1-step loop peeling identity ($L = \text{header};\,(B;\,\text{header})^* \equiv \text{header};\,(B;\,\text{header})^+$ when the first header test succeeds, and $\text{header}$ alone when it fails), requiring only that header instructions cloned before the guard are side-effect-free or executed identically on entry.

#### 2.2 `ScalarEvolution` (`SCEV`, `lib/Analysis/ScalarEvolution.cpp`, `17,453` LOC)
- **Algorithm**: Maps integer and pointer SSA values inside loops to canonical algebraic `SCEV` AST nodes (`SCEVConstant`, `SCEVUnknown`, `SCEVTruncateExpr`, `SCEVZeroExtendExpr`, `SCEVSignExtendExpr`, `SCEVAddExpr`, `SCEVMulExpr`, `SCEVUDivExpr`, `SCEVAddRecExpr`, `SCEVSMaxExpr`/`SCEVUMaxExpr`/`SCEVSMinExpr`/`SCEVUMinExpr`, `SCEVSequentialUMinExpr`, `SCEVPtrToIntExpr`):
  - An induction variable in loop $L$ with initial value $a_0$ and step $s$ is represented as the polynomial recurrence $\{a_0, +, s\}_L$, which evaluates at 0-based iteration $k \in \mathbb{N}$ to $a_0 + k \cdot s \pmod{2^w}$ (or higher-degree $\{c_0, +, c_1, +, c_2\}_L = c_0 + c_1 \binom{k}{1} + c_2 \binom{k}{2}$).
  - Crucially, `SCEVAddRecExpr` nodes carry **No-Wrap Flags** (`FlagNUW`, `FlagNSW`, `FlagNW` = self-no-wrap), inferred either from IR instruction `nuw`/`nsw` flags (only when the instruction **executes on every loop iteration before the latch**, `isGuaranteedToExecuteForEveryIteration`) or from proven loop trip-count bounds (`ProvePredicate`).
  - Computes loop exit counts (`computeBackedgeTakenCount` / `ExitLimit`) by solving $\{\text{start}, +, \text{step}\}_L \;\text{pred}\; \text{rhs}$ for the first iteration $k$ where the latch/header branch exits.
- **Bug history (including Alive2)**:
  - **Poison/No-Wrap Hoisting Bug**: Attaching `FlagNSW` to $\{a_0, +, s\}_L$ from an `add nsw` inside a conditionally executed block inside the loop, and then using that `FlagNSW` to fold an exit condition or widen an induction variable that executes unconditionally on every iteration!
  - **Division-by-stride trip-count overflow**: When `step` is not $\pm 1$ (e.g., `step = 2` or `step` is even), $\{a_0, +, 2\}_L \ne b$ may wrap around $2^w$ infinitely if $b - a_0$ is odd, unless `FlagNW` / `FlagNUW` / `FlagNSW` proves the recurrence cannot wrap before crossing $b$.
- **Derivation facts needed**: Every `SCEV` query consumed by a pass (`IndVarSimplify`, `LoopDeletion`, `LSR`, `LoopVectorize`) translates to an inductive invariant over loop iteration counter $k$:
  $$\text{Inv}(k) \triangleq \big(v^{(k)} = \text{evalSCEV}(S_v, k) \pmod{2^w}\big) \land \big(\forall j < k,\; \text{NoWrap}(S_v, j)\big).$$
  This invariant can be checked by base case ($k=0$ at preheader) + inductive step ($k \to k+1$ across loop latch) without trusting the `17,453` LOC of `ScalarEvolution.cpp`!

#### 2.3 `LICM` with Scalar Promotion (`lib/Transforms/Scalar/LICM.cpp`, `3,064` LOC, `25` mutation sites)
- **Algorithm**: Using `LoopInfo`, `DominatorTree`, `MemorySSA` (`MemorySSAUpdater`), and `AliasSetTracker` / `BatchAA`, `LICM` performs three transformations on loop $L$:
  1. **Sinking (`sinkRegion`)**: Moves instructions inside $L$ whose only uses are outside $L$ down into $L$'s dedicated exit blocks (`LCSSA` $\phi$ nodes), provided they are movable and not clobbered before loop exit.
  2. **Hoisting (`hoistRegion`)**: Moves loop-invariant instructions (whose operands are defined outside $L$) and loop-invariant loads (whose pointer is invariant and whose `MemorySSA` `MemoryUse` is not clobbered by any `MemoryDef` inside $L$) into the loop preheader. If the hoisted instruction does not dominate all loop exits (`!isGuaranteedToExecute`), `LICM` requires `isSafeToExecuteUnconditionally` (dereferenceable + aligned for loads; non-trapping for arithmetic) and **strips poison-generating flags (`nsw`, `nuw`, `exact`, `inbounds`, `disjoint`)** (`dropPoisonGeneratingAnnotations`).
  3. **Scalar Promotion of Memory (`promoteLoopAccessesToScalars`)**: When a loop-invariant address $p$ is loaded and/or stored inside $L$ and `MemorySSA` + `BatchAA` prove $p$ aliases no other memory access in $L$:
     - Loads `*p` once in the preheader (if read or if the store inside $L$ is not guaranteed to execute on every path),
     - Replaces loads and stores inside $L$ with SSA register `PHINode` updates, and
     - Stores the final SSA value back to `*p` in each dedicated exit block!
- **Bug history (including Alive2)**:
  - **Conditional Store Promotion Poison/Race Bug (`llvm/llvm-project#52867`)**: If a loop never executes a store to `*p` at runtime (because the store is inside `if (false)`), promoting `*p` by loading `*p` in the preheader and unconditionally storing it back to `*p` in the exit block:
    1. Introduces a data race in multi-threaded code (banned unless `*p` is thread-local or a store is guaranteed to execute on the taken path), and
    2. If `*p` held `undef` or uninitialized padding bytes, loading and storing without `freeze` could turn `undef` anomalies or trigger MSan/poison issues; LLVM now inserts `freeze` or guards store-back with a boolean flag or `isGuaranteedToExecute` check + `Writable` / `Dereferenceable` proof.
- **Verified precedents**: CompCert `LICM` (loop-invariant code motion in RTL/SSA); Crellvm `LICM` hints (`hoist_inst`, `promote_mem`).
- **Derivation facts needed**:
  - For Hoisting: loop-invariance of operands + (for loads) `NoAlias` proof against all `MemoryDef`s in $L$ + either `DominatesAllLoopExits(I)` or (`SafeToSpeculate(I)` $\land$ `FlagsStripped(I)`).
  - For Scalar Promotion: `MustAlias` equivalence class of promoted accesses $\{A_1, \dots, A_m\}$ at invariant address $p$, `NoAlias` against all other accesses in $L$, `NoCapture` / thread-safety or guaranteed store execution proof (`GuaranteedToExecuteStore`), and `SSAUpdater` phi invariant.

#### 2.4 `IndVarSimplify` (`4,394` LOC), `LoopIdiomRecognize` (`3,606` LOC), `LoopDeletion` (`392` LOC), `SimpleLoopUnswitch` (`3,814` LOC), `LoopUnroll` (`3,962` LOC), and `LoopStrengthReduce` (`7,178` LOC)

| Pass | LOC / Muts | Algorithm & Analyses | Correctness Argument, Bug History & Derivation Facts |
| :--- | ---: | :--- | :--- |
| `IndVarSimplify` (`IndVarSimplify.cpp` + `SimplifyIndVar.cpp`) | `4,394` LOC / `51` muts | Queries `SCEV`: (1) widens narrow `i32` induction variables to `i64` to eliminate `sext`/`zext` (`WidenIV`) when `SCEV` proves `nsw`/`nuw`; (2) rewrites outside `LCSSA` uses of IVs to closed-form `SCEVExpander` exit expressions (`rewriteLoopExitValues`); (3) folds loop-invariant `icmp`s (`simplifyAndExtend`); (4) linearizes exit tests (`linearFunctionTestReplace`). | Inductive `SCEV` recurrence equivalence + no-wrap proof up to backedge-taken count $N$. **Bug history**: `SCEVExpander` hoisting/reusing an existing IR value whose `nsw` flag or `poison` taint was stronger than the expanded `SCEV` expression (`llvm/llvm-project#49779`). **Certificate**: `SCEV` inductive invariant + closed-form evaluation at $k = N$. |
| `LoopIdiomRecognize` (`LoopIdiomRecognize.cpp`) | `3,606` LOC / `74` muts | Recognizes affine stride-1 store loops (`{base, +, elem_size}`) storing a constant byte or copying `{src, +, elem_size}` and replaces them with `@llvm.memset` / `@llvm.memcpy` / `@llvm.memmove` (plus `cttz`/`ctlz`/`popcnt` bit-scan loops). | Bounded memory slice extensionality: over $k \in [0, N)$, store $[b + k\cdot s, b + (k+1)s)$ with no aliasing reads/writes inside the loop equals a bulk `memset`/`memcpy(b, src, N*s)`. For `memcpy`, requires `NoAlias` between `[dst, dst+N*s)` and `[src, src+N*s)`. |
| `LoopDeletion` (`LoopDeletion.cpp`) | `392` LOC / `5` muts | Deletes a loop $L$ if (1) all instructions in $L$ have no observable side effects (no volatile/atomic/escaped stores or calls), (2) all `LCSSA` exit $\phi$s are loop-invariant (`isLoopDead`), and (3) either `SCEV` proves a finite max backedge-taken count OR the function/loop carries `mustprogress` / `willreturn`. | Stuttering termination simulation: a side-effect-free loop that terminates in $N < \infty$ iterations transitions from preheader state $\sigma$ to exit state $\sigma$. **Bug history**: deleting infinite side-effect-free loops in Rust before `mustprogress` semantics were separated from C++ (`rust-lang/rust#28728`). **Certificate**: finite trip-count ranking function from `SCEV` (or `mustprogress` UB witness). |
| `SimpleLoopUnswitch` (`SimpleLoopUnswitch.cpp`) | `3,814` LOC / `37` muts | Hoists loop-invariant branches/switches out of $L$: **trivial unswitching** redirects a header/exiting branch directly out of $L$ without cloning; **non-trivial unswitching** clones $L$ into $L_{\text{true}}$ and $L_{\text{false}}$ guarded by **`freeze(%inv_cond)`** in the preheader! | Distributivity of loop iteration over invariant branch: $\text{while}(E) \{ \text{if}(c) B_1 \text{ else } B_2 \}$ $\equiv$ $\text{let } c' = \text{freeze}(c);\; \text{if}(c') \text{ while}(E) B_1 \text{ else while}(E) B_2$. **Bug history**: before LLVM introduced `freeze`, unswitching on a `poison`/`undef` condition `%c` that was never dynamically reached inside a 0-trip or early-exiting loop caused immediate UB at the hoisted `br i1 %c`! Inserting `freeze` before the hoisted branch fixed this class of miscompilations. |
| `LoopUnroll` (`LoopUnrollPass.cpp` + `Utils/LoopUnroll*.cpp`) | `3,962` LOC / `64` muts | Performs **full unrolling** (when trip count $N$ is a small constant, removing the backedge), **partial unrolling** (duplicating the body $U$ times when $N$ is a multiple of $U$), **runtime unrolling** (`UnrollRuntimeLoopRemainder`, emitting an epilogue or prologue remainder loop for $N \bmod U$), and **loop peeling** (`peelLoop`, peeling the first $k$ iterations). | Unfolding fixed-point identity $\mu X.\, F(X) = F^U(\mu X.\, F(X))$. Requires zero semantic assumptions beyond Euclidean division $N = q U + r$ ($0 \le r < U$) for runtime remainder unrolling. |
| `LoopStrengthReduce` (`LoopStrengthReduce.cpp`) | `7,178` LOC / `14` muts | Runs in the pre-ISel CodeGen pipeline: collects all `IVUsers` (addressing modes and loop exit comparisons), factors common `SCEV` subexpressions (`LSRUse`, `Formula`), and rewrites induction variables so memory accesses map directly to target addressing modes (`[base + reg * scale + imm]`). | Algebraic `SCEV` equivalence modulo $2^w$ + pointer provenance preservation (`SCEVExpander` must anchor pointer-typed induction variables on the original base pointer via `getelementptr` rather than `inttoptr(ptrtoint(base) + offset)`). |

#### 2.5 `LoopVectorize` (`14,007` LOC across `LoopVectorize.cpp` + `VPlan.cpp` + `LoopAccessAnalysis.cpp`, `50` mutation sites)
- **Algorithm**:
  1. **Legality (`LoopVectorizationLegality` + `LoopAccessAnalysis`, `3,560` LOC)**: Checks single-latch canonical loop structure, classifies phis as induction (`InductionDescriptor`), reduction (`RecurrenceDescriptor`), first-order recurrence, or fixed-order recurrence, and analyzes memory dependences across iterations via `MemoryDepChecker`:
     - Uses `ScalarEvolution` to express every load/store pointer as an affine recurrence $\{p_0, +, \text{stride}\}_L$.
     - If two accesses may alias (`AccessAnalysis::canCheckPtrAtRT`) and `SCEV` cannot statically prove a dependence distance $\ge \text{VF} \cdot \text{UF}$ (or backward safe distance), generates **runtime pointer-disjointness checks** (`RuntimePointerChecking`: `icmp ult/uge` comparing `[start_A, end_A)` against `[start_B, end_B)`) and **runtime `SCEVPredicate` no-wrap checks** (up to threshold `VectorizeMemoryCheckThreshold = 128`).
  2. **Cost Model & VPlan (`LoopVectorizationCostModel` + `VPlan`, `1,960` LOC)**: Builds `VPlan` candidate graphs over vectorization factors $\text{VF} \in \{1, 2, 4, 8, 16, \dots, vscale \times k\}$ and interleave counts $\text{IC} \in \{1, 2, 4, \dots\}$, querying `TargetTransformInfo` for vector instruction/gather/scatter/reduction costs.
  3. **Code Generation (`InnerLoopVectorizer::executePlan`)**: Emits:
     - Minimum-iteration check (`N < VF * IC`) + runtime SCEV/alias check block branching to the scalar fallback loop on failure;
     - Vector preheader + vector loop body (`<VF x T>` wide loads, stores, arithmetic, masked predication for tail-folded or if-converted blocks, and vector reduction phis);
     - Reduction horizontal finisher (`@llvm.vector.reduce.add.*` / shuffle tree) in the `middle.block`;
     - Scalar (or Epilogue Vectorized) remainder loop for the $N \bmod (\text{VF} \cdot \text{IC})$ tail iterations!
- **Correctness argument**: Lockstep $W$-iteration unrolling simulation ($W = \text{VF} \cdot \text{IC}$):
  1. On the **fallback path** (when runtime alias or SCEV checks evaluate to `false` or $N < W$), the original scalar loop executes unmodified (reflexive simulation).
  2. On the **vector path** (guarded by the runtime checks $\Phi_{\text{no-overlap}} \land \Phi_{\text{no-wrap}}$), $W$ consecutive scalar iterations have zero loop-carried Read-After-Write (RAW), Write-After-Read (WAR), or Write-After-Write (WAW) memory hazards across lanes $0 \dots W-1$, and associative reductions (`add`, `mul`, `and`, `or`, `xor`, `smin`/`smax`/`umin`/`umax`, or `fadd` with `reassoc`) commute across vector lanes.
- **Bug history (including Alive2)**:
  - **If-conversion poison/UB speculation**: Vectorizing a conditional block inside the loop (`if (c[i]) x = a[i] / b[i]`) by computing `<VF x i32> sdiv` unconditionally and selecting lanes with `select <VF x i1> %c_vec` causes immediate UB if any inactive lane has `b[lane] == 0` or `INT_MIN / -1`! `LoopVectorize` must predicate trapping operations (`div`/`rem` by replacing inactive divisors with `1`, and masked loads/stores `@llvm.masked.load`/`store` for conditional memory accesses).
- **Derivation facts needed**:
  - Guarded equivalence witness: proof that `vector.memcheck` + `vector.scevcheck` conditions imply pairwise disjointness of writable memory intervals across lanes $0 \dots W-1$, plus lane-unrolling equivalence between 1 step of the `VPlan` vector body and $W$ steps of the scalar loop body.

#### 2.6 `SLPVectorizer` (`lib/Transforms/Vectorize/SLPVectorizer.cpp`, `33,278` LOC, `143` mutation sites) & `VectorCombine` (`6,631` LOC, `140` mutation sites)
- **Algorithm**: `SLPVectorizer` (Superword-Level Parallelism, `BoUpSLP`) seeds bottom-up isomorphic expression trees (`TreeEntry`) starting from adjacent stores (`vectorizeStores`), `PHINode`s, reductions (`HorizontalReduction`), or `insertelement` chains. It checks memory scheduling legality within each basic block (`BlockScheduling::tryScheduleBundle`: building a dependence graph of instructions and memory accesses via `BatchAA` so bundled instructions can be scheduled together at a single program point without creating cycles), evaluates `BoUpSLP::getTreeCost` via `TTI`, and replaces scalar instruction bundles with `<N x T>` vector operations (`insertelement`/`shufflevector`/`extractelement` at tree boundaries). `VectorCombine` performs local cost-driven peepholes on vector `extractelement`/`insertelement`/`shufflevector`/load pairs.
- **Correctness argument**: Within a basic block, reordering independent instructions into topological bundle order preserves data and memory dependencies (`BatchAA` `NoAlias` for any load/store moved past another memory access), and each `<N x T>` vector instruction computes the exact Cartesian product of its $N$ scalar lane instructions.
- **Derivation facts needed**:
  - For each `TreeEntry` bundle: the $N$-tuple of scalar instructions $(I_0, \dots, I_{N-1})$, the replacement vector instruction $V$, the topological schedule permutation of the basic block with `NoAlias` proofs for every swapped memory pair, and lane-wise algebraic equivalence (`extractelement(V, lane) ⊑ I_lane`).

---

### 3. Foundational Alias Analyses: `BasicAliasAnalysis` (`2,175` LOC) & `ScopedNoAliasAA` (`204` LOC)

**Basis: source**

Every memory pass above (`EarlyCSE`, `GVN`, `DSE`, `MemCpyOpt`, `LICM`, `LoopIdiomRecognize`, `LoopVectorize`, `SLPVectorizer`) queries `AAResults` (`PassBuilder::buildDefaultAAPipeline`, `PassWrapper.cpp:731`), which chains `BasicAA`, `ScopedNoAliasAA`, `TypeBasedAA`, and `GlobalsAA`:

| Analysis | Source File & LOC | Core Soundness Rules & Proof Obligations |
| :--- | :--- | :--- |
| `BasicAliasAnalysis` | `lib/Analysis/BasicAliasAnalysis.cpp` (`2,175` LOC) | (1) **Distinct Identified Objects (`isIdentifiedObject`)**: two distinct `alloca`s, global variables, `noalias` arguments, or `noalias` call returns are `NoAlias`. (2) **Non-Escaping Object vs Escaped/Call (`isNonEscapingLocalObject`)**: an `alloca` not captured before a call cannot alias the call's accesses or pointer arguments (`PointerMayBeCaptured`). (3) **Linear GEP Decomposition (`DecomposeGEPExpression`)**: decomposes $p = \text{base} + c_0 + \sum_i s_i v_i$ using `Scale` and `VarIndex` modulo $2^w$ (with `nuw`/`nsw` bounds) to prove byte intervals $[p_1, p_1 + sz_1)$ and $[p_2, p_2 + sz_2)$ on the same base object are disjoint (`aliasGEP`) or exact (`MustAlias`). |
| `ScopedNoAliasAA` | `lib/Analysis/ScopedNoAliasAA.cpp` (`204` LOC) | Compares `!alias.scope` and `!noalias` metadata lists on instructions (`mayAliasInScopes`): if access $A$ has `!noalias` scope list $N_A$ and access $B$ has `!alias.scope` list $S_B$ inside the same metadata domain, and $S_B \neq \emptyset \land S_B \subseteq N_A$, returns `NoAlias`. This is the exact mechanism by which inlined Rust `&mut T` / `&T` `noalias` parameters preserve aliasing disjointness after inlining! |

## Boundaries

- **SMT timeout boundaries in bounded translation validation**: While Alive2 (`PLDI 2021`) can automatically discharge loop-free scalar/bitvector rewrites (`InstCombine`, `BDCE`, `Reassociate`, `EarlyCSE`, `CVP`, `JumpThreading`, `SLPVectorizer` on small widths), it uses bounded loop unrolling (default $k=1$ or $k=2$) and timeouts on wide 64-bit multiplication/division trees, floating-point transcendental intrinsics, and unbounded `LoopVectorize` / `IndVarSimplify` `SCEV` recurrences. Unbounded verification of loop passes requires inductive `SCEV` invariants rather than black-box SMT unrolling.
- **`NewGVN` (`4,306` LOC)**: Although present in `llvm/lib/Transforms/Scalar/NewGVN.cpp`, `EnableNewGVN` defaults to `false` in `PassBuilderPipelines.cpp:218`, so `rustc` `1.99.1` never runs `NewGVN` unless explicitly requested via `-C llvm-args=-enable-newgvn`.

## Evidence

- **Primary source files in `rust-lang/llvm-project` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`)**:
  - `llvm/lib/Transforms/InstCombine/InstructionCombining.cpp` and `InstCombine*.cpp` (`56,238` LOC total).
  - `llvm/lib/Transforms/Scalar/EarlyCSE.cpp` (`1,924` LOC), `GVN.cpp` (`4,073` LOC), `SROA.cpp` (`6,422` LOC), `SimplifyCFGPass.cpp` (`413` LOC), `DeadStoreElimination.cpp` (`2,520` LOC), `MemCpyOptimizer.cpp` (`2,284` LOC), `CorrelatedValuePropagation.cpp` (`1,404` LOC), `ConstraintElimination.cpp` (`1,953` LOC), `JumpThreading.cpp` (`3,300` LOC), `SCCP.cpp` (`287` LOC), `BDCE.cpp` (`148` LOC), `ADCE.cpp` (`748` LOC), `Reassociate.cpp` (`2,533` LOC), `TailRecursionElimination.cpp` (`1,069` LOC).
  - `llvm/lib/Transforms/Utils/PromoteMemoryToRegister.cpp` (`1,237` LOC), `SimplifyCFG.cpp` (`9,140` LOC), `SCCPSolver.cpp` (`2,431` LOC), `LoopSimplify.cpp` (`885` LOC), `LCSSA.cpp` (`523` LOC), `LoopRotationUtils.cpp` (`925` LOC), `SimplifyIndVar.cpp` (`2,287` LOC), `LoopUnroll.cpp` (`1,021` LOC), `LoopUnrollRuntime.cpp` (`1,151` LOC).
  - `llvm/lib/Transforms/Scalar/LICM.cpp` (`3,064` LOC), `IndVarSimplify.cpp` (`2,107` LOC), `LoopUnrollPass.cpp` (`1,790` LOC), `SimpleLoopUnswitch.cpp` (`3,814` LOC), `LoopIdiomRecognize.cpp` (`3,606` LOC), `LoopDeletion.cpp` (`392` LOC), `LoopStrengthReduce.cpp` (`7,178` LOC).
  - `llvm/lib/Transforms/Vectorize/LoopVectorize.cpp` (`8,487` LOC), `VPlan.cpp` (`1,960` LOC), `SLPVectorizer.cpp` (`33,278` LOC), `VectorCombine.cpp` (`6,631` LOC).
  - `llvm/lib/Analysis/ScalarEvolution.cpp` (`17,453` LOC), `LoopAccessAnalysis.cpp` (`3,560` LOC), `LazyValueInfo.cpp` (`2,098` LOC), `BasicAliasAnalysis.cpp` (`2,175` LOC), `ScopedNoAliasAA.cpp` (`204` LOC), `MemorySSA.cpp` (`2,487` LOC), `ValueTracking.cpp` (`9,884` LOC), `InstructionSimplify.cpp` (`7,125` LOC).
- **Preserved support artifacts (`reports/llvm-scalar-memory-and-loop-optimization-proof-obligations/support/`)**:
  - `scalar_memory_loop_pass_metrics.json`: Exact LOC, file counts, mutation site counts (`rauw`, `replace_inst`, `erase`, `irbuilder_create`, `cfg_mutate`, `attr_md_mutate`, `ore_remark`), and queried analysis managers for all 60 scalar, memory, loop, vectorization, and analysis modules.

## Revalidation

To recompute the pass LOC, mutation site breakdowns, and analysis queries against a newer LLVM revision, inspect `llvm/lib/Transforms/{InstCombine,Scalar,Utils,Vectorize}` and `llvm/lib/Analysis/` at the target commit and compare against `support/scalar_memory_loop_pass_metrics.json`. To test individual pass transformations on minimal LLVM IR specimens, invoke:

```bash
opt -passes="<pass-name>" -S input.ll -o output.ll
```
