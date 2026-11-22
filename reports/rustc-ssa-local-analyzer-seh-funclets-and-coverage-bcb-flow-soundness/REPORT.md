# `rustc_codegen_ssa::mir::analyze` (`LocalKind`, Windows SEH `CleanupKind` Funclets) and `-C instrument-coverage` Balanced-Flow BCB Lowering

## Summary

Lowering Rust MIR into LLVM IR across `rustc_codegen_ssa` and instrumenting MIR for source-based coverage across `rustc_mir_transform` and `rustc_codegen_llvm` rely on three structural invariants that connect MIR dominance, Windows SEH / Wasm EH funclet isolation, and Kirchhoff flow conservation over Basic Coverage Blocks (BCBs). Primary-source inspection across `rust-lang/rust` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` and `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), `llvm/llvm-project` (`6dfe1677ab8dffbc6ec13d53a1e0215d75147689`), and `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`), paired with live execution on `x86_64-unknown-linux-gnu` (`rustc 1.98.0-nightly`, `LLVM 22.1.6`) plus recorded `LLVM 23.1.5` baselines and a 33-theorem constructive `Lean v4.34.1` formalization ([`support/SsaLocalAnalyzerAndCoverageFlow.lean`](support/SsaLocalAnalyzerAndCoverageFlow.lean)), establishes five governing conclusions:

1. **`rustc_codegen_ssa::mir::analyze::non_ssa_locals` *never* synthesizes SSA $\phi$-nodes for user MIR locals.** Every MIR local begins in `LocalKind::ZST` (if `layout.is_zst()`) or `LocalKind::Unused`. A non-ZST local stays `LocalKind::SSA(DefLocation)`—and lowers to a register-bound `LocalRef::PendingOperand -> LocalRef::Operand` with zero stack `alloca`s—if and only if: (a) its `BackendRepr` is not `BackendRepr::Memory` (i.e., `Scalar`, `ScalarPair`, or SIMD immediate), (b) it has at most one `define` (`DefLocation::{Argument, Assignment, CallReturn}`), where a second definition immediately demotes `SSA(_) -> Memory` (`analyze.rs:93`), (c) `def.dominates(location, dominators)` holds at every `Copy`/`Move`/`Inspect` use (`analyze.rs:227-234`, routing non-dominated potentially uninitialized reads through an `alloca` rather than constructing an invalid SSA dominance graph), (d) no mutating projections, borrows (`Borrow`/`SharedBorrow`/`FakeBorrow`/`RawBorrow`), `SetDiscriminant`, `AsmOutput`, or `type_needs_drop` drops occur (note: even a `ZST` local with `Drop` promotes to `Memory` on `MutatingUseContext::Drop` at `analyze.rs:254-264`), and (e) any read projection consists solely of `PlaceElem::Field` and single-variant `PlaceElem::Downcast` (`maybe_codegen_consume_direct` at `analyze.rs:140-163`, `operand.rs:1072-1116`).
2. **`cleanup_kinds` recovers a strict single-parent funclet tree on MSVC SEH and Wasm EH by promoting shared cleanup joins.** `discover_masters` seeds every non-nop `UnwindAction::Cleanup(target)` entry as `CleanupKind::Funclet`. A reverse-postorder `propagate` pass (`analyze.rs:335-400`) marks single-funclet descendants as `CleanupKind::Internal { funclet }`, promotes any `Internal` block entered from two distinct funclets to `CleanupKind::Funclet` (`L383-396`), records each funclet's unique parent in `funclet_succs` (`span_bug!("funclet {:?} has 2 parents")` on conflict at `L348-354`), and enforces via `llbb_characteristics` (`block.rs:111-127`) that every cross-funclet control transfer lowers as `cleanupret from %pad unwind label %funclet_bbN` rather than an illegal cross-funclet `br`.
3. **`-C instrument-coverage` compresses MIR blocks into `BasicCoverageBlock`s (`BCB`s) and eliminates redundant counters via a Knuth-Stevenson spanning tree over a `BalancedFlowGraph`.** `CoverageGraph::from_mir` (`graph.rs:35-180`) strips unwind/false edges and merges single-successor chains (`is_out_chainable()`) into BCBs. `BalancedFlowGraph::for_graph` (`balanced_flow.rs:56-81`) restores Kirchhoff flow conservation $\text{inflow}(v) = \text{outflow}(v)$ by connecting `!is_out_summable` blocks (returns, `Yield`, diverging calls) and inescapable-loop nodes to a synthetic `sink` with a `sink -> START_BCB` cycle edge. `node_flow_data_for_balanced_graph` unifies each node's successors via Union-Find so node flows become edge flows in a quotient multigraph, and `make_node_flow_priority_list` sorts non-sink nodes by `(is_out_summable, !is_reloop_node, -dom_rank)` so `is_reloop_node` latches (`dominates(succ, node)` on a single out-edge) receive subtraction expressions instead of physical RMWs. On `hot_loop_diamond` (`8` non-cleanup MIR BBs $\to$ `7` BCBs), `rustc` emits only `3` physical counters (`bcb0`, `bcb1`, `bcb3`) pre-pass and reconstructs all `7` execution counts (`1, 101, 100, 25, 75, 100, 1`) exactly.
4. **LLVM lowering emits monotonic `atomicrmw add` increments on `@__profc_*`, preserves per-monomorphization inlined attribution via `scope.inlined_instance`, and exports five instrumentation ELF sections.** Rust passes `Options.Atomic = true` to LLVM's `InstrProfilingLoweringPass` (`PassWrapper.cpp:842-845`), lowering `@llvm.instrprof.increment` into `atomicrmw add ptr @__profc_<sym>, i64 1 monotonic` (`InstrProfiling.cpp:1419-1422`). Across `MIR Inline`, `visit_source_scope_data` preserves the innermost callee in `SourceScopeData::{inlined, inlined_parent_scope}`, so `codegen_coverage` (`coverageinfo.rs:7-18`) resolves `self.monomorphize(inlined)` and `query.rs` attributes counters independently per monomorphization (`generic_inlined::<u32>` = `10`, `generic_inlined::<u64>` = `7`, combined = `17`), stored across `__llvm_prf_names`, `__llvm_prf_cnts`, `__llvm_prf_data`, `__llvm_covfun`, and `__llvm_covmap`.
5. **Consequences for `joshlf/anneal` (`c131b320`).** `Trusted.MirAst` (`MirAst.lean:642, 657-662`) currently folds `StatementKind::Coverage` into `.unsupported` (failing closed in `MirSemantics`), while modeling `BasicBlock.cleanup : Bool` and `UnwindAction.cleanup`. Any verified codegen backend targeting LLVM or native machine code cannot blindly assume `LocalKind::SSA` without enforcing `DefLocation::dominates`, must verify the single-parent funclet partition before emitting Windows SEH `cleanuppad`/`cleanupret`, and may strip or preserve `StatementKind::Coverage(VirtualCounter)` as pure counter-increment side effects orthogonal to program memory semantics when non-panicking control-flow conservation holds.

---

## Applicability

### Examined Subjects and Their Relationships

This report characterizes the interaction among five durable upstream subjects recorded in `REPORT.json`:

- **`rust-lang/rust` at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`1.102.0-nightly`, 2026-11-11, bundled `LLVM 23.1.5`):** Primary source revision audited across `compiler/rustc_codegen_ssa/src/mir/{analyze.rs, block.rs, coverageinfo.rs, locals.rs, mod.rs, operand.rs, place.rs, statement.rs}`, `compiler/rustc_mir_transform/src/{cleanup_post_borrowck.rs, inline.rs, coverage/{mod.rs, counters.rs, counters/balanced_flow.rs, counters/node_flow.rs, expansion.rs, from_mir.rs, graph.rs, hir_info.rs, mappings.rs, query.rs, spans.rs}}`, `compiler/rustc_middle/src/mir/{mod.rs, coverage.rs}`, `compiler/rustc_codegen_llvm/src/coverageinfo/{mod.rs, llvm_cov.rs, mapgen.rs, mapgen/covfun.rs}`, and `compiler/rustc_llvm/llvm-wrapper/{CoverageMappingWrapper.cpp, PassWrapper.cpp}`. Its scrubbed `LLVM 23.1.5` IR and `llvm-cov` baseline output is preserved in [`support/recorded_llvm23_1_102_0_nightly.json`](support/recorded_llvm23_1_102_0_nightly.json).
- **`rust-lang/rust` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`, 2026-05-31, bundled `LLVM 22.1.6`):** Source-audited for cross-revision comparison and **live-executed** on `x86_64-unknown-linux-gnu` (including cross-targeting `x86_64-pc-windows-msvc` IR generation plus `llvm-profdata`, `llvm-cov`, and `llvm-readobj`) via [`support/probe_ssa_analyzer_funclets_and_coverage.py`](support/probe_ssa_analyzer_funclets_and_coverage.py), generating [`support/probe_results.json`](support/probe_results.json).
- **`llvm/llvm-project` at `6dfe1677ab8dffbc6ec13d53a1e0215d75147689` (`llvmorg-23.1.1`):** Audited directly at `llvm/include/llvm/ProfileData/InstrProfData.inc` and `llvm/lib/Transforms/Instrumentation/InstrProfiling.cpp` for `InstrProfilingLoweringPass` atomic counter lowering and object-format section names (ELF vs. COFF vs. Mach-O).
- **`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`:** Target MIR verification model audited at `trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`, and `trusted/correspondence/Trusted/Correspondence.lean`.
- **`leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`):** Kernel that checked all 33 theorems in [`support/SsaLocalAnalyzerAndCoverageFlow.lean`](support/SsaLocalAnalyzerAndCoverageFlow.lean).

### Exact Version Differences Between `14210df0e` (`1.98.0-nightly`) and `3ef0c22cd` (`1.102.0-nightly`)

All `non_ssa_locals` lattice transitions, `cleanup_kinds` propagation rules, Knuth-Stevenson counter-elimination algorithms (`counters.rs` and `node_flow.rs` have zero-line diffs between the two revisions), and runtime coverage execution counts (`hot_loop_diamond`: `[1, 101, 100, 25, 75, 100, 1]`; `generic_inlined::<u32>`: `10`; `generic_inlined::<u64>`: `7`) agree across both revisions. Five concrete implementation differences exist between `14210df0e` and `3ef0c22cd`:

1. **Layout predicate refactor in `LocalAnalyzer` (`compiler/rustc_codegen_ssa/src/mir/analyze.rs`):** In `14210df0e`, `define` (`L87-92`) tests `fx.cx.is_backend_immediate(layout) || fx.cx.is_backend_scalar_pair(layout)` and `process_place` (`L160`) asserts `!self.fx.cx.is_backend_ref(layout)`. By `3ef0c22cd`, `define` (`L87-91`) tests `if let abi::BackendRepr::Memory { .. } = layout.backend_repr`, and `process_place` (`L160`) asserts `layout.is_ssa_standalone()`.
2. **Removal of `MutatingUseContext::Retag` in `LocalAnalyzer`:** In `14210df0e` (`analyze.rs:215-216`), `PlaceContext::MutatingUse(MutatingUseContext::Retag)` is explicitly matched as a no-op alongside `PlaceContext::NonUse(_)` and `PlaceMention`; by `3ef0c22cd` (`analyze.rs:214-215`), standalone `StatementKind::Retag` was removed (folded into `Rvalue::Use`), eliminating the `MutatingUseContext::Retag` match arm.
3. **`nop_landing_pads` filtering in `cleanup_kinds` (`analyze.rs:295-330`):** In `14210df0e` (`L296-318`), `cleanup_kinds(mir)` registers every `UnwindAction::Cleanup(unwind)` as `CleanupKind::Funclet`. In `3ef0c22cd` (`L295-329`), `cleanup_kinds(mir, nop_landing_pads)` takes `&DenseBitSet<mir::BasicBlock>` and skips `nop_landing_pads.contains(unwind)` in `discover_masters`, matching the `codegen_mir` reachability pruning (`mir/mod.rs:298-313`).
4. **HIR-point markers (`CoverageKind::Point`) replacing statement-span heuristics (`from_mir.rs`, `mid_cov`, `cleanup_post_borrowck.rs`):** In `14210df0e`, MIR building emitted `CoverageKind::SpanMarker` only for selected constructs and `coverage/from_mir.rs` extracted raw spans from MIR `Assign`/`FakeRead`/`Call`/`Return` statements (giving `0` markers in `InstrumentCoverage.before.mir` for `hot_loop_diamond`, yet `12` code regions after `SimplifyCfg`/span refinement). By `3ef0c22cd`, MIR building emits explicit `CoverageKind::Point { point_kind: PointKind::{Expr, ImplicitElse, FunctionEnd}, hir_id }` statements (`30` points in `hot_loop_diamond` prior to `InstrumentCoverage`, removed afterward by `CleanupPostBorrowck` via `kind.is_removed_after_analysis()`), and `from_mir.rs:48-65` extracts spans strictly from `CoverageKind::Point` filtered by `hir_info.nodes_to_ignore`. Correspondingly, `mir::Body::function_coverage_info` / `FunctionCoverageInfo` and query `coverage_ids_info` (`14210df0e`) were renamed to `mir::Body::coverage_mir_info` / `CoverageMirInfo` and query `coverage_codegen_info` (`3ef0c22cd`).
5. **Pre-pass vs. post-`-O2` LLVM IR emission for coverage (`probe_results.json`):** Compiling `hot_loop_diamond` with `-C opt-level=2 -C no-prepopulate-passes --emit=llvm-ir` captures the direct 1-to-1 `InstrProfilingLoweringPass` output (**3** `atomicrmw add` instructions indexing `@__profc_...` slots `0`, `1`, `2`), identical in structure to `3ef0c22cd`'s `recorded_llvm23_1_102_0_nightly.json`. Compiling with full `-C opt-level=2` (without `-C no-prepopulate-passes`) runs LLVM's loop unroller (`2x` unroll + epilogue), expanding the textual IR to **7** `atomicrmw add` call sites targeting those same `3` `[3 x i64]` slots.

### Configuration Scope and Related Corpus Reports

- **Host/Target Scope:** Empirical execution ran on `x86_64-unknown-linux-gnu` for `#[custom_mir]` IR (`Part A`) and live `-C instrument-coverage` execution (`Part C`), and cross-compiled to `x86_64-pc-windows-msvc` for SEH funclet LLVM IR (`Part B`).
- **Lean Mechanization Scope:** `support/SsaLocalAnalyzerAndCoverageFlow.lean` uses core Lean `v4.34.1` exclusively (`[propext, Quot.sound]`, `[propext]`, or no axioms; zero `Classical.choice`, `sorryAx`, `omega`, `bv_decide`, `native_decide`, or `partial def`).
- **Related Corpus Reports:** `anssa-block-argument-ssa-mem2reg-and-mir-semantic-hazards-2026` covers block-argument SSA (`AnSSA`) and MIR-to-SSA semantic hazards (`MaybeUninit`/padding/`WithRetag`); `unwinding-on-windows-targets-and-32bit-seh` documents Windows `.pdata`/`.xdata`, `__CxxFrameHandler3` `$cppxdata$`, and 32-bit `fs:[0]` SEH; `rustc-cleanup-post-borrowck-false-edges-and-abort-unwinding-mir-lowering` covers `CleanupPostBorrowck` and `AbortUnwindingCalls`; `rustc-mir-inlining-call-graph-splicing-and-incremental-policy-soundness` documents `MIR Inline` source-scope splicing.

---

## Findings

### 1. `LocalAnalyzer` (`non_ssa_locals`): Why `rustc_codegen_ssa` Never Synthesizes User-Local $\phi$-Nodes

`Basis: source + execution + derived`

#### 1.1 The 4-State `LocalKind` Semilattice and `LocalRef` Representation

When `codegen_mir` (`compiler/rustc_codegen_ssa/src/mir/mod.rs:202-363`) prepares locals for LLVM IR emission, it constructs a dominance-respecting traversal order (`traversal::mono_reachable_reverse_postorder(mir, tcx, instance)`, pruned by reachable blocks excluding `nop_landing_pads` edges at `L283-313`), calls `analyze::non_ssa_locals(&fx, &traversal_order)` (`L315`), and binds each MIR local to one variant of `LocalRef` (`compiler/rustc_codegen_ssa/src/mir/mod.rs:145-161`):

```rust
// compiler/rustc_codegen_ssa/src/mir/analyze.rs:59-68 (3ef0c22cd)
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum LocalKind {
    ZST,
    /// A local that requires an alloca.
    Memory,
    /// A scalar or a scalar pair local that is neither defined nor used.
    Unused,
    /// A scalar or a scalar pair local with a single definition that dominates all uses.
    SSA(DefLocation),
}
```

| `LocalKind` State | Initial Condition & Transition | `codegen_mir` Allocation (`mod.rs:326-361`) | Codegen Assignment (`statement.rs:20-61`) | Codegen Read (`operand.rs:1079-1140`) |
| :--- | :--- | :--- | :--- | :--- |
| `ZST` | `layout.is_zst() == true` (`analyze.rs:30`); preserved by all non-drop uses; **demoted to `Memory` on `MutatingUseContext::Drop` if `type_needs_drop(ty)`** (`L254-264`). | `LocalRef::Operand(OperandRef::zero_sized(layout))` (unless promoted to `Memory` by `Drop` -> `alloca [0 x i8]`). | Re-evaluates RHS operand for side effects; `Operand` branch ignores non-store (`if !op.layout.is_zst() { span_bug! }`). | `codegen_consume` short-circuits on `layout.is_zst()` (`L1129-1131`) to `OperandRef::zero_sized` without loading memory. |
| `Unused` | Initial state when `!layout.is_zst()`; never reached by any `define`, nor any read/borrow. | `LocalRef::PendingOperand` (zero `alloca` emitted). | Never assigned if truly unused; `StorageLive`/`StorageDead` are no-ops on `PendingOperand`. | Impossible on reachable path: any `Copy`/`Move`/`Inspect` on `Unused` demotes it immediately to `Memory` (`analyze.rs:232-234`). |
| `SSA(DefLocation)` | Reached on first `define` when `!matches!(layout.backend_repr, BackendRepr::Memory { .. })` (`Scalar`/`ScalarPair`/SIMD); survives iff zero subsequent `define`s, all reads dominated, no disallowed projections/borrows/drops. | `LocalRef::PendingOperand` (zero `alloca` emitted; arguments start immediately as `LocalRef::Operand` per `arg_local_refs` at `mod.rs:529-558`). | `PendingOperand -> overwrite_local(index, LocalRef::Operand(operand))` (`statement.rs:36-43`, `block.rs:2530` for `CallReturn`). Re-assigning an already populated non-ZST `Operand` triggers `span_bug!("operand {:?} already assigned")`! | `maybe_codegen_consume_direct` (`operand.rs:1072-1116`) extracts scalar or `Pair` field directly (`extract_field`, `for_variant`) with zero `load` instructions. |
| `Memory` | Aggregate `BackendRepr::Memory`, second `define`, non-dominated `Copy`/`Move`/`Inspect`, `Unused` read, disallowed read projection, any mutating projection, any borrow/`AsmOutput`/`SetDiscriminant`, `type_needs_drop` `Drop`, or `intrinsic_call_expects_place_always`. | `LocalRef::Place(PlaceRef::alloca)` (or `UnsizedPlace` / indirect `RETURN_PLACE` `PassMode::{Indirect, Cast}` at `mod.rs:326-349`). | `codegen_rvalue(bx, cg_dest, rvalue)` stores into the stack `alloca` (`store ... ptr %_loc`). | `codegen_place` + `bx.load_operand(place)` emits `load ..., ptr %_loc` (`operand.rs:1139-1140`). |

#### 1.2 Why Non-Dominated Reads and Multi-Def Diamonds Never Synthesize LLVM `phi` Nodes

Classical SSA construction resolves multi-definition joins (`cm_2`) and partially initialized paths (`cm_3`) by inserting $\phi$-nodes at iterated dominance frontiers. `rustc_codegen_ssa` intentionally avoids $\phi$-synthesis for MIR locals (`LocalRef::Operand` holds one immutable backend `OperandRef` updated at most once by `overwrite_local`):

1. **Exact `define` Demotion Rule (`analyze.rs:77-95`):**
   - `non_ssa_locals` first registers every MIR function argument with `analyzer.define(arg, DefLocation::Argument)` (`L37-39`), then visits blocks in `traversal_order` (a topological sort of the dominance partial order so definitions are visited *before* any block they dominate).
   - Inside `define(local, location)`: `Unused` transitions to `SSA(location)` for non-`BackendRepr::Memory` layouts (`L87-91`), while `SSA(_)` unconditionally transitions to `LocalKind::Memory` (`L93`).
   - Consequently, assigning to `_3` in both arms of a conditional diamond (`bb1` and `bb2` in `cm_2_diamond_two_defs_forces_alloca`) executes `define` twice, promoting `_3` to `LocalKind::Memory`. Codegen emits one `alloca`, two `store`s, one `load`, and **zero** `phi` nodes in pre-pass LLVM IR (leaving register promotion to LLVM's downstream `SROA`/`mem2reg` pass).

2. **Exact `DefLocation::dominates` Semantics (`compiler/rustc_middle/src/mir/mod.rs:1680-1708`):**
   ```rust
   pub enum DefLocation {
       Argument,
       Assignment(Location),
       CallReturn { call: BasicBlock, target: Option<BasicBlock> },
   }
   ```
   - **`Argument`**: Dominates every location (`true`).
   - **`Assignment(def)`**: Dominates `location` iff `def.successor_within_block().dominates(location, dominators)` — i.e., either in the same basic block with `def.statement_index + 1 <= location.statement_index` (an assignment cannot dominate a read in the *same* statement or an earlier statement), or `dominators.dominates(def.block, location.block)`.
   - **`CallReturn { call, target: None }`**: Diverging call never returns, so `dominates` returns `false`.
   - **`CallReturn { call, target: Some(target) }`**: Because a MIR `Call` writes its destination *only on the normal-return edge* `call -> target` (not on the `unwind` edge!), `DefLocation::dominates` requires **strict edge dominance**:
     ```rust
     call != target
         && dominators.dominates(call, target)
         && dominators.dominates(target, location.block)
     ```
     If `target` has any other predecessor (such as a loop entry or another incoming branch), `dominators.dominates(call, target)` fails, demoting the call destination to `LocalKind::Memory`. Notice also that `visit_local` checks `intrinsic_call_expects_place_always(intrinsic.name)` (`analyze.rs:207-210`) before `define` and marks such call destinations `Memory` upfront, while non-memory call destinations populate `LocalRef::Operand` via `ReturnDest::DirectOperand` (`block.rs:2530`).

3. **Non-Dominated Reads in Unreachable or Disjoint Paths (`analyze.rs:227-235`):**
   Even when a local has **only one** definition in the entire function (e.g., `bb1` in `cm_3_single_def_nondominating_read_forces_alloca`), if a read in `bb2` is not dominated by that definition (either because `bb0` can jump directly to `bb2` on an infeasible/UB path, or because `traversal_order` visits an uninitialized read before the definition), `LocalKind::SSA(def)` falls through the `if def.dominates(location, self.dominators)` guard (`L227`) to `kind @ (LocalKind::Unused | LocalKind::SSA(_)) => *kind = LocalKind::Memory` (`L232-234`). If `LocalAnalyzer` kept such a local in `LocalKind::SSA`, codegen visiting `bb2` when `PendingOperand` has not yet been overwritten would crash with `bug!("use of {:?} before def", place_ref)` (`operand.rs:1108`, mechanized as `ce1_nondominated_single_def_in_ssa_reads_unbound_vreg`)!

4. **Projection and Context Constraints (`analyze.rs:97-168, 214-267`):**
   - **`PlaceElem::Index(index_local)` (`L109-113`)**: Recorded as a `Copy` read of `index_local` *before* checking whether the base local is already `Memory`.
   - **Indirect `Deref` First Projection (`L121-128`)**: If a place begins with `*` (`is_indirect_first_projection()`), `LocalAnalyzer` only records a `Copy` read of the base pointer local and returns — the pointer itself stays `SSA` while loads/stores operate through its pointer value!
   - **Mutating Projections (`L130-137`)**: Any write to a projected place (`_3.0 = _1` in `cm_5`) visits the base local with `MutatingUseContext::Projection`, demoting `ScalarPair` locals to `LocalKind::Memory` because LLVM SSA values in `LocalRef::Operand` cannot receive in-place sub-field mutations.
   - **Read Projections (`L139-163`)**: Non-mutating reads permit *only* chains of `PlaceElem::Field` and `PlaceElem::Downcast(_, vidx)` where `layout.variants == Variants::Single { index: single_variant }` and `vidx == single_variant`. Any `Index`, `Subslice`, `ConstantIndex`, or multi-variant `Downcast` forces `LocalKind::Memory`. Thus `_1.1` on `_1: (i32, i64)` in `cm_4` stays `LocalKind::SSA(Argument)` and compiles directly to `ret i64 %_1.1`.
   - **Non-Codegen Uses (`L214-216`)**: `PlaceContext::NonUse(_)` (including `StorageLive`, `StorageDead`, `VarDebugInfo`) and `NonMutatingUseContext::PlaceMention` do *not* force `LocalKind::Memory` (`StatementKind::StorageLive`/`StorageDead` check `if let LocalRef::Place(cg_place)` at `statement.rs:73-86` and are complete no-ops on `SSA` locals). Conversely, any borrow (`SharedBorrow`, `FakeBorrow`, `RawBorrow`, `MutatingUseContext::Borrow`, `MutatingUseContext::RawBorrow`) forces `LocalKind::Memory` (`cm_6`).

#### 1.3 Empirical Verification Across Six `#[custom_mir]` Pre-Pass LLVM IR Specimens

Compiling the 6 `#[custom_mir(dialect = "runtime", phase = "optimized")]` functions with `-C opt-level=2 -C no-prepopulate-passes --emit=llvm-ir` produces identical instruction counts across `rustc 1.98.0-nightly` (`LLVM 22.1.6`) and `rustc 1.102.0-nightly` (`LLVM 23.1.5`):

| Specimen | MIR Pattern | `LocalKind` Outcome | Pre-Pass `alloca`s | Pre-Pass `phi`s | `load` / `store` Counts | Key Pre-Pass LLVM IR Shape |
| :--- | :--- | :--- | :---: | :---: | :---: | :--- |
| `cm_1_single_def_dominated` | `_2 = _1 + 5; RET = _2 * 3` | `_2: SSA(Assign(bb0[0]))` | `0` | `0` | `0` / `0` | `%_2 = add i32 %_1, 5; %_0 = mul i32 %_2, 3; ret i32 %_0` |
| `cm_2_diamond_two_defs_forces_alloca` | `_3` assigned in `bb1` & `bb2`, read in `bb3` | `_3: Memory` (`L93`) | `1` | `0` | `1` / `2` | `%_3 = alloca [4 x i8], align 4`, 2 `store`s, 1 `load` in `bb3` |
| `cm_3_single_def_nondominating_read_forces_alloca` | `_3` assigned only in `bb1`, read in `bb2` (also target of `start`) | `_3: Memory` (`L227-234`) | `1` | `0` | `1` / `1` | `%_3 = alloca [4 x i8], align 4`, 1 `store` in `bb1`, 1 `load` in `bb2` |
| `cm_4_scalarpair_field_read_direct_ssa` | `_1: (i32, i64)`, `RET = _1.1` | `_1: SSA(Argument)` (`L145`) | `0` | `0` | `0` / `0` | `ret i64 %_1.1` |
| `cm_5_scalarpair_field_write_forces_alloca` | `_3: (i32, i64)`, `_3.0 = _1; _3.1 = _2; RET = _3.1` | `_3: Memory` (`L130-136`) | `1` | `0` | `1` / `2` | `%_3 = alloca [16 x i8], align 8`, `store i32`, GEP+`store i64`, GEP+`load i64` |
| `cm_6_raw_borrow_forces_alloca` | `_2 = _1 + 1; _3 = &raw const _2; RET = _2` | `_2: Memory` (`L248-252`) | `1` | `0` | `1` / `1` | `%_2 = alloca [4 x i8], align 4`, 1 `store`, 1 `load` |

---

### 2. Windows SEH and Wasm EH Funclet Tree Recovery (`cleanup_kinds`)

`Basis: normative + source + execution`

#### 2.1 LLVM Funclet Constraints and `discover_masters` / RPO `propagate`

Under Windows MSVC structured exception handling (`__CxxFrameHandler3`, enabled when `base::wants_new_eh_instructions(&tcx.sess.target)` is `true`) and Wasm EH, LLVM requires exception-handling cleanup code to form a strict **forest of single-entry funclets**: every `cleanuppad` receives control only via an `invoke ... unwind label` or an outer `cleanupret ... unwind label`, every block executed under a funclet token `%cleanuppad` may branch (`br`) *only* to blocks within the same funclet (never across funclet boundaries), and leaving a funclet must execute `cleanupret from %pad unwind label %parent` (or `unwind to caller`).

In `compiler/rustc_codegen_ssa/src/mir/analyze.rs:275-408` (`3ef0c22cd`), `cleanup_kinds` partitions all MIR basic blocks into `CleanupKind::{NotCleanup, Funclet, Internal { funclet }}`:

1. **`discover_masters` (`L299-333`)**: Initializes every block to `CleanupKind::NotCleanup`, scans `Call`, `InlineAsm`, `Assert`, and `Drop` terminators for `UnwindAction::Cleanup(unwind)`, and (in `3ef0c22cd`, provided `!nop_landing_pads.contains(unwind)`) sets `result[unwind] = CleanupKind::Funclet`.
2. **`propagate` (`L335-400`)**: Maintains `funclet_succs : IndexVec<BasicBlock, Option<BasicBlock>>` mapping each funclet head to its unique parent funclet, with helper `set_successor(funclet, succ)` (`L341-357`) that inserts `Some(succ)` on `None`, leaves identical parents untouched, and aborts compilation with `span_bug!(mir.span, "funclet {:?} has 2 parents - {:?} and {:?}", funclet, s, succ)` whenever one funclet attempts to unwind into two distinct parent funclets.
3. **RPO Edge Transitions (`L359-399`)**: Iterates `(bb, data)` in `traversal::reverse_postorder(mir)` (skipping `NotCleanup` blocks). Let `funclet` be `bb` if `result[bb] == Funclet`, or `f` if `result[bb] == Internal { funclet: f }`. For each successor `succ` of `bb`:
   - **`NotCleanup` $\to$ `Internal { funclet }`** (`L375-377`): Claims `succ` for the current funclet.
   - **`Funclet`** (`L378-382`): If `funclet != succ`, records `set_successor(funclet, succ)`.
   - **`Internal { funclet: succ_funclet }`** (`L383-396`): If `funclet != succ_funclet`, `succ` is a **shared cleanup join block** reachable from two distinct funclets! `propagate` promotes `result[succ] = CleanupKind::Funclet` and links *both* `succ_funclet` and `funclet` to parent `succ` via `set_successor(succ_funclet, succ)` and `set_successor(funclet, succ)`.

#### 2.2 Lowering Through `llbb_characteristics`, `funclet_br`, and `landing_pad_for_uncached`

During MIR-to-LLVM block emission (`compiler/rustc_codegen_ssa/src/mir/block.rs:111-162, 2210-2219`):

- **`llbb_characteristics(self, fx, target)` (`block.rs:111-127`)** computes `(needs_landing_pad, is_cleanupret)` from `(funclet_bb(self.bb), funclet_bb(target))`:
  - `(None, None) => (false, false)` (normal intra-function edge).
  - `(None, Some(_)) => (true, false)` (normal `invoke` entering a cleanup funclet landing pad).
  - `(Some(f), Some(t_f)) => (f != t_f, f != t_f)` (staying in the same funclet emits plain `br`; crossing to a *different* funclet sets both `needs_landing_pad = true` and `is_cleanupret = true`).
  - `(Some(_), None) => span_bug!("{:?} - jump out of cleanup?", ...)` (invariant violation).
- **`landing_pad_for_uncached(bb)` (`block.rs:2210-2219`)**: For `wants_new_eh_instructions`, prepends an LLVM wrapper block `%funclet_bbN` containing `%cleanuppad = cleanuppad within none []` followed by `br label %bbN`, and caches the token in `fx.funclets[bb]`.
- **`funclet_br` (`block.rs:136-162`) & `codegen_resume_terminator` (`block.rs:412-415`)**: When `is_cleanupret` is `true`, emits `cleanupret from %pad unwind label %funclet_bbN` (via `lltarget = fx.landing_pad_for(target)`); on `TerminatorKind::UnwindResume` inside a funclet, emits `cleanupret from %pad unwind to caller`.
- **`UnwindAction::Terminate` inside cleanup (`block.rs:233-245`)**: On MSVC SEH (`L237-242`), `do_call` passes `unwind_block = None` because Windows SEH aborts automatically if an exception attempts to escape a cleanup funclet; on Wasm EH (`L233-236`), Rust constructs a nested `cleanuppad within %outer_pad` to call `panic_in_cleanup`.

#### 2.3 Empirical Evidence: Direct Funclet Chaining vs. True `Internal -> Funclet` Join Promotion

Cross-compiling a `#![no_core]` specimen crate (`--target=x86_64-pc-windows-msvc -C opt-level=2 -C no-prepopulate-passes --emit=llvm-ir`) captures **two** complementary SEH behaviors in `support/probe_results.json`:

1. **`seh_shared_cleanup_promotion` (Direct `Funclet -> Funclet` parent chaining):**
   `let _outer = OuterGuard; may_throw_outer(); { let _inner = InnerGuard; may_throw_inner(); }` places `bb6` (`OuterGuard` drop) as an explicit `UnwindAction::Cleanup` target of `may_throw_outer` (`start`) and inner drop (`bb2`), while `bb5` (`InnerGuard` drop) jumps to `bb6`. Because `discover_masters` already marked `bb6` as `CleanupKind::Funclet`, `L378-381` links `bb5 -> bb6`, yielding `2` `cleanuppad` definitions inside `seh_shared_cleanup_promotion` (`%funclet_bb6`, `%funclet_bb5`) plus `1` terminate pad in `drop_in_place_shim` (5 `cleanuppad` tokens total across the module in `1.98.0-nightly`, and 3 `cleanuppad` tokens across the identical IR in `seh_shared_cleanup_promotion` of `recorded_llvm23_1_102_0_nightly.json`), with exact `cleanupret`:
   ```llvm
   cleanupret from %cleanuppad1 unwind label %funclet_bb6
   ...
   cleanupret from %cleanuppad unwind to caller
   ```

2. **`seh_true_internal_join_promotion` (True `Internal { funclet } -> Funclet` promotion via `L383-396`):**
   When `let outer = OuterGuard;` is `forget(outer)`ed along normal exit paths and only `if branch { let left = InnerGuard; may_throw_left(); forget(left); } else { let right = InnerGuard; may_throw_right(); forget(right); }` can unwind, **zero** normal `invoke` edges target `bb4` (`OuterGuard` drop)! Thus `discover_masters` leaves `bb4` as `NotCleanup`; RPO visits `bb7` (`funclet_bb7`, left inner cleanup) and marks `bb4 = Internal { funclet: bb7 }`; then RPO visits `bb6` (`funclet_bb6`, right inner cleanup) and triggers `analyze.rs:383-396`, promoting `bb4` to `CleanupKind::Funclet` (`%funclet_bb4: %cleanuppad1 = cleanuppad within none []`). In the emitted LLVM IR (`probe_results.json`), `seh_true_internal_join_promotion` contains **3** `= cleanuppad within none []` definitions (`%funclet_bb6`, `%funclet_bb7`, and promoted `%funclet_bb4` with `preds = %bb7, %bb6`) and both inner funclets exit cleanly via:
   ```llvm
   cleanupret from %cleanuppad unwind label %funclet_bb4   ; from bb6
   cleanupret from %cleanuppad2 unwind label %funclet_bb4  ; from bb7
   ```

---

### 3. `-C instrument-coverage`: Kirchhoff Balanced-Flow BCB Counter Elimination and `is_reloop_node` Priority

`Basis: source + execution + derived`

#### 3.1 `CoverageGraph` Contraction and `BalancedFlowGraph` Construction

During MIR passes, `InstrumentCoverage` (`compiler/rustc_mir_transform/src/coverage/mod.rs:33-114`) constructs a simplified CFG `CoverageGraph::from_mir(mir_body)` (`graph.rs:35-180`):

- **Edge Filtering (`bcb_filtered_successors`, `graph.rs:364-404`)**: Strips all unwind edges, `FalseEdge` imaginary targets, `FalseUnwind` unwind edges, and `Unreachable` blocks. Only `SwitchInt`, `Yield`, `Assert`, `Drop`, `FalseEdge`/`FalseUnwind` real targets, `Goto`, `Call { target: Some(t) }`, and `InlineAsm` targets remain.
- **`is_out_summable` vs. `is_out_chainable` (`graph.rs:335-349`)**:
  - `is_out_summable = !is_yield && !targets.is_empty()` (`false` for `Return`, `Yield`, diverging `Call` with `target: None`, `TailCall`, `CoroutineDrop`, `UnwindResume`, `UnwindTerminate`).
  - `is_out_chainable = is_out_summable && targets.len() == 1`. A depth-first traversal (`graph.rs:155-172`) merges any chain `prev -> bb` where `prev` is out-chainable and `bb`'s *only* MIR predecessor is `[prev]` into a single `BasicCoverageBlock` (`BCB`).
- **Kirchhoff Flow Balancing (`BalancedFlowGraph::for_graph`, `balanced_flow.rs:56-81`)**: Imposes strict node-flow conservation ($\text{count}(v) = \sum_{e \in \text{in}(v)} \text{count}(e) = \sum_{e \in \text{out}(v)} \text{count}(e)$) by synthesizing one virtual `sink` node (`index = graph.num_nodes()`) with:
  1. Synthetic in-edges `node -> sink` for every node where `force_sink_edge(node)` (`!graph[node].is_out_summable`) or `graph.successors(node).next().is_none()`,
  2. Synthetic in-edges `node -> sink` for any remaining node *not* reverse-reachable from those sink-edge nodes (covering inescapable infinite loops via `sink_edge_nodes.union_not(dfs.visited_set())`, `L74-75`), and
  3. One closing edge `sink -> START_BCB` (`L117-121`).

#### 3.2 Supernode Quotient, `make_node_flow_priority_list`, and Knuth-Stevenson Spanning Tree

1. **Supernode Reduction (`node_flow_data_for_balanced_graph`, `node_flow.rs:25-50`):** Every real node $u$ in a balanced graph has out-flow equal to the sum of its out-edge flows, $\text{flow}(u) = \sum_{v \in \text{succ}(u)} \text{flow}(u \to v)$. Merging all successors $\{v \in \text{succ}(u)\}$ into one `UnionFind` supernode $S = \text{succ\_supernodes}[u]$ turns node $u$'s total flow $\text{flow}(u)$ into a **single directed edge** $\text{supernodes}[u] \to \text{succ\_supernodes}[u]$ in the quotient multigraph while preserving Kirchhoff conservation at every supernode!
2. **Priority Ordering (`make_node_flow_priority_list`, `counters.rs:45-76`):** `node_flow.rs:198-253` visits nodes in `priority_list` order: earlier nodes claim spanning-tree edges (receiving algebraic **counter expressions** with zero runtime RMWs), while cycle-closing chord nodes receive **physical counters**. The sort guarantees:
   - Index `0` is always `balanced_graph.sink` (never receives a physical counter);
   - Non-sink nodes are sorted ascending by `is_out_summable` (`false` first, so return/yield nodes prefer expressions), then descending by `is_reloop_node` (`true` first, where `is_reloop_node` holds iff `graph.successors[node].as_slice() == &[succ]` and `graph.dominates(succ, node)` at `counters.rs:52-58`), then descending by `dom_rank` (`graph.cmp_in_dominator_order(a, b).reverse()`). Thus loop latches (`is_reloop_node = true`) claim tree edges first and never incur per-iteration atomic counter RMW overhead when a lower-frequency header or branch chord suffices.
   - At codegen query time (`query.rs:94-156`), `coverage_codegen_info` scans the *post-optimization* MIR for surviving non-inlined `CoverageKind::VirtualCounter { bcb }` statements (`bcbs_seen`), pushes `!bcbs_seen.contains(bcb)` nodes to the *back* of `priority_list[1..]` so dead BCBs take physical counters that `transcribe_counters` (`counters.rs:79-125`) immediately replaces with `CovTerm::Zero`, and builds minimized `Expression { lhs, op, rhs }` DAGs (`Op::Add`, `Op::Subtract`) via `SpantreeBuilder::yank_to_spantree_root`.

#### 3.3 Exact End-to-End Trace on `hot_loop_diamond` (`8` MIR BBs $\to$ `7` BCBs $\to$ `3` Physical Counters)

On `hot_loop_diamond(n = 100)`:

1. **MIR-to-BCB Contraction (`InstrumentCoverage.after.mir`, `probe_results.json`):** `hot_loop_diamond` has `9` total MIR basic blocks (`bb0..bb7` plus unreachable `bb8 (cleanup): resume;`). Stripping `bb8` leaves `8` non-cleanup BBs. Because `bb1` ends with `falseUnwind -> [real: bb2]` and `bb2`'s sole predecessor is `bb1`, `CoverageGraph` merges `[bb1, bb2]` into `bcb1`, yielding **7 `VirtualCounter` BCBs**: `bcb0` (`bb0`), `bcb1` (`[bb1, bb2]`), `bcb2` (`bb3`), `bcb3` (`bb4`, `acc += 3`), `bcb5` (`bb5`, `acc += 1`), `bcb4` (`bb6`, latch `i += 1`), and `bcb6` (`bb7`, `return`).
2. **Priority List & Quotient Supernodes:** Only `bcb4` (`succs = [bcb1]`, `dominates(bcb1, bcb4)`) satisfies `is_reloop_node = true`. Union-Find unifies `{bcb2, bcb6}`, `{bcb3, bcb5}`, and `{bcb4}` (leaving `6` supernodes `{0, 1, 6, 5, 4, 7}` across the `8` nodes including `sink = 7`). `make_node_flow_priority_list` yields `[sink(7), bcb6, bcb4, bcb5, bcb3, bcb2, bcb1, bcb0]`.
3. **Kirchhoff Spanning-Tree Elimination & Reconstruction:** `sink`, `bcb6`, `bcb4`, `bcb5`, and `bcb2` claim the `5` tree edges connecting the `6` supernodes (`V - 1 = 5`), leaving **exactly 3 chord nodes (`8 - 5 = 3`)**: `bcb0` (`Counter(0)`), `bcb1` (`Counter(1)`), and `bcb3` (`Counter(2)`). At runtime for `n = 100`, the 3 physical counters record `c0 = 1`, `c1 = 101`, `c2 = 25`, and `llvm-cov` reconstructs all `7` BCB counts and all source-region counts (`[1, 1, 1, 1, 1, 101, 100, 25, 75, 100, 1, 1]` in `1.98.0-nightly`, `[1, 1, 1, 101, 100, 25, 75, 100, 1, 1]` in `1.102.0-nightly`) with zero error:

| BCB | MIR Blocks | Source Role | `is_out_summable` / `is_reloop` | `SpantreeBuilder` Assignment | Formula in `{c0, c1, c2}` | Measured / Reconstructed (`n = 100`) |
| :--- | :--- | :--- | :---: | :--- | :--- | :---: |
| `bcb0` | `bb0` | Entry (`i = 0; acc = 0`) | `true` / `false` | **Physical `Counter(0)`** (`+0`) | $c_0$ | `1` |
| `bcb1` | `bb1, bb2` | Loop header (`while i < n`) | `true` / `false` | **Physical `Counter(1)`** (`+8`) | $c_1$ | `101` |
| `bcb2` | `bb3` | Branch cond (`(i & 3) == 0`) | `true` / `false` | Tree edge (`Expression`) | $c_1 - c_0$ | `100` |
| `bcb3` | `bb4` | `then` branch (`acc += 3`) | `true` / `false` | **Physical `Counter(2)`** (`+16`) | $c_2$ | `25` |
| `bcb4` | `bb6` | Loop latch (`i += 1`) | `true` / **`true`** | Tree edge (`Expression`) | $c_1 - c_0$ | `100` |
| `bcb5` | `bb5` | `else` branch (`acc += 1`) | `true` / `false` | Tree edge (`Expression`) | $(c_1 - c_0) - c_2$ | `75` |
| `bcb6` | `bb7` | Return (`acc`) | **`false`** / `false` | Tree edge (`Expression`) | $c_0$ | `1` |

---

### 4. Atomic `__profc_` Lowering, Per-Monomorphization Inlined Attribution, and the Five Coverage ELF Sections

`Basis: source + execution`

#### 4.1 Codegen Intrinsics and Monotonic `atomicrmw add` Lowering

For every surviving `StatementKind::Coverage(CoverageKind::VirtualCounter { bcb })`, `statement.rs:87-89` calls `FunctionCx::codegen_coverage(bx, kind, statement.source_info.scope)` (`compiler/rustc_codegen_ssa/src/mir/coverageinfo.rs:8-18`), which delegates to `Builder::add_coverage(instance, kind)` (`compiler/rustc_codegen_llvm/src/coverageinfo/mod.rs:87-133`):

- If `cg_info.phys_counter_for_node.get(&bcb)` returns `Some(&id)`, `add_coverage` interns `fn_name = bx.ensure_pgo_func_name_var(instance)` (recording `instance` in `pgo_func_name_var_map`, marking it "used" for `__llvm_covfun` emission) and emits `llvm.instrprof.increment(fn_name, function_source_hash, num_counters, id.as_u32())`.
- If `bcb` was assigned a counter expression (`None` in `phys_counter_for_node`), `add_coverage` emits **zero instructions** (`L131`).
- In LLVM pass pipeline setup (`compiler/rustc_llvm/llvm-wrapper/PassWrapper.cpp:842-845`), `rustc` explicitly sets `Options.Atomic = true;` (*"cargo run tests in multithreading mode by default so use atomics for coverage counters"*) before adding `InstrProfilingLoweringPass(Options, false)`. Inside LLVM (`llvm/lib/Transforms/Instrumentation/InstrProfiling.cpp:1417-1431`), `lowerIncrement` lowers each `llvm.instrprof.increment` into:
  `Builder.CreateAtomicRMW(AtomicRMWInst::Add, Addr, Inc->getStep(), MaybeAlign(), AtomicOrdering::Monotonic)` on `@__profc_<mangled_fn>`.
  Pre-pass LLVM IR for `hot_loop_diamond` exhibits **exactly 3** such instructions (`[3 x i64]` at byte offsets `0`, `8`, `16`), matching `probe_results.json` and `recorded_llvm23_1_102_0_nightly.json`.

#### 4.2 Per-Monomorphization Attribution Across `MIR Inline`

When `MIR Inline` splices a callee body into a caller (`compiler/rustc_mir_transform/src/inline.rs:920-960, 1233-1253`), `Integrator::visit_source_scope_data` preserves the innermost inlined call boundary:
- On the callee's root scope (`parent_scope.is_none()`), it sets `scope_data.parent_scope = Some(callsite.source_info.scope)`, sets `scope_data.inlined = Some((callsite.callee, callsite.source_info.span))`, and copies `inlined_parent_scope` from the callsite (`L1238-1248`).
- On child scopes inside the callee whose `inlined_parent_scope` was `None`, it caches `Some(self.map_scope(OUTERMOST_SOURCE_SCOPE))` (`L1249-1252`).

Consequently, during codegen (`compiler/rustc_codegen_ssa/src/mir/coverageinfo.rs:9-14` and `compiler/rustc_middle/src/mir/mod.rs:1488-1500`):
```rust
let instance = if let Some(inlined) = scope.inlined_instance(&self.mir.source_scopes) {
    self.monomorphize(inlined)
} else {
    self.instance
};
```
`inlined_instance` checks `scope_data.inlined` first and falls back to `inlined_parent_scope`, so deeply nested inlining (`C` into `B` into `A`) always attributes statements to the *innermost* callee instance (`C`), and `self.monomorphize(inlined)` instantiates generic parameters in the caller's environment. Meanwhile, `query::coverage_codegen_info` (`query.rs:104-111, 158-172`) excludes statements where `is_inlined(mir_body, stmt)` is true when computing `bcbs_seen` for the caller itself.

In our live probe (`cov_specimen.rs`), `main` inlines `generic_inlined::<u32>(..., true)` (`10` calls) and `generic_inlined::<u64>(..., false)` (`7` calls): pre-pass LLVM IR for `main` contains `9` `atomicrmw` increments (split across `main` and the two monomorphizations' `@__profc_` globals), and `llvm-cov export` / `llvm-cov show` independently report `generic_inlined::<u32>` = `10` (`[10, 10, 10, 0, 10]`) and `generic_inlined::<u64>` = `7` (`[7, 7, 0, 7, 7]`), summing to `17` on the shared source view.

#### 4.3 Coverage Mapping Format (`Version7`) and Five Binary Sections

At CGU finalization (`compiler/rustc_codegen_llvm/src/coverageinfo/mapgen.rs:26-228` and `covfun.rs:240-311`), `rustc` asserts `CovmapVersion::Version7 = 6` (`L29, 53`), emits one CGU-level `__llvm_covmap` record (4-`u32` header + encoded filename table starting with `base_dir` at index `0`), and emits one packed `__covrec_<func_name_hash:X>u` `LinkOnceODR` COMDAT global in `__llvm_covfun` per used function (`func_name_hash`, `u32` mapping byte length, `function_source_hash`, `filenames_hash`, encoded expressions + regions). Across object formats (`llvm/include/llvm/ProfileData/InstrProfData.inc:823-856`), `llvm-readobj --sections` confirms the exact 5 ELF sections on Linux:

| Role | ELF Section (`x86_64-unknown-linux-gnu`) | COFF Section (Windows) | Mach-O Segment/Section (macOS) | Contents & Emitting Component |
| :--- | :--- | :--- | :--- | :--- |
| Mangled function names | `__llvm_prf_names` | `.lprfn$M` | `__DATA,__llvm_prf_names` | Compressed mangled `Instance` symbol names (`InstrProfiling`) |
| Runtime atomic counters | `__llvm_prf_cnts` | `.lprfc$M` | `__DATA,__llvm_prf_cnts` | `i64` zero-initialized arrays (`@__profc_*`) incremented via `atomicrmw add monotonic` |
| Profile metadata descriptors | `__llvm_prf_data` | `.lprfd$M` | `__DATA,__llvm_prf_data` | `{NameRef, FuncHash, CounterPtr, FunctionPointer, ...}` linking runtime counters to names |
| Per-function coverage maps | `__llvm_covfun` | `.lcovfun$M` | `__LLVM_COV,__llvm_covfun` | Packed `__covrec_<hash>u` records (`CounterExpression`s + `Code`/`Branch` spans, `covfun.rs`) |
| Per-CGU filename tables | `__llvm_covmap` | `.lcovmap$M` | `__LLVM_COV,__llvm_covmap` | 4-`u32` header (`Version7 = 6`) + compressed file path table (`mapgen.rs`) |

---

### 5. Kernel-Checked `Lean v4.34.1` Mechanization and Constructive Counterexamples

`Basis: derived`

[`support/SsaLocalAnalyzerAndCoverageFlow.lean`](support/SsaLocalAnalyzerAndCoverageFlow.lean) formalizes all three subsystems in pure core `Lean v4.34.1` with zero external imports, zero `sorry`, and zero classical or external automation tactics (`0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`). Every theorem is verified by `-DwarningAsError=true -Ddebug.skipKernelTC=false` and exhaustive `#print axioms` (`support/lean_axioms_all_theorems.txt` covers all 33 theorems, recording only `propext` and `Quot.sound`).

| Theorem / Lemma | Formal Statement Summary | Axiom Footprint |
| :--- | :--- | :--- |
| `zst_preserved_non_drop` / `zst_with_drop_promotes_to_memory` | `LocalKind.zst` is preserved under all uses except `Drop(needsDrop=true)`, which promotes it to `.memory` (`alloca [0 x i8]`). | `[propext]` |
| `stepUse_monotone_non_zst` / `second_define_demotes_to_memory` / `non_dominated_read_demotes_to_memory` / `disallowed_proj_demotes_to_memory` | `kindRank` increases monotonically across `unused < ssa < memory`; a second `define`, non-dominated read, or disallowed projection immediately yields `.memory`. | `[propext, Quot.sound]` / `[propext]` |
| `localAnalyzer_ssa_or_memory_simulation_exact` | Whenever a local classified as `.ssa` respects dominance (`validSsaTrace false events = true`) or is demoted to `.memory`, `evalLoweredTrace` never faults (`ssaUseBeforeDef`/`ssaAlreadyAssigned`) and matches `evalMirTrace` read-for-read. | `[propext]` |
| `cm1_single_def_stays_ssa` .. `cm6_raw_borrow_demotes_to_memory` | Exact kernel reduction checking all 6 `#[custom_mir]` specimens (`cm_1`, `cm_4` stay `.ssa`; `cm_2`, `cm_3`, `cm_5`, `cm_6` demote to `.memory`). | `[propext]` |
| `cleanupKinds_no_cross_funclet_internal_edge` / `distinct_funclet_edge_lowers_to_cleanupret` | After `propagateEdge`, no cleanup successor stays `.notCleanup`, no cross-funclet `Internal` target survives, and every `fSrc ≠ fDst` edge lowers via `llbbCharacteristics` as `(true, true)` (`cleanupret`). | `[propext, Quot.sound]` |
| `seh_shared_cleanup_promotion_tree_verified` / `seh_true_internal_join_promotion_tree_verified` / `seh_two_parents_triggers_span_bug` | Decides both MSVC SEH specimens (including `bb4`: `.notCleanup -> .internal 7 -> .funclet` with zero direct `invoke`s) and verifies multi-parent funclets fail with `.twoParents 5 6 7`. | `[]` |
| `bcbFlow_counterExpression_reconstructs_exact` | Universally over **all** `Int` flows satisfying Kirchhoff conservation `IsHotLoopBalancedFlow`, `hotLoopTerms` over 3 physical counters (`c0, c1, c2`) reconstructs all 7 BCB flows (`bcb0..bcb6`) exactly. | `[propext]` |
| `hotLoop_reloop_priority_places_latch_first` / `hotLoop_concrete_100_iters_reconstructs_exact` | Verifies `isReloopPred` selects `bcb4` (`bcb4 -> bcb1`), ranks `sink < bcb6 < bcb4 < bcb5 < bcb3 < bcb2 < bcb1 < bcb0`, and reconstructs `[1, 101, 100, 25, 100, 75, 1]` at `n = 100`. | `[propext]` / `[]` |
| `inlinedInstance_monomorphize_preserves_distinct_counters` | Proves `inlinedInstance` attributes `generic_inlined::<u32>` and `::<u64>` to distinct `(InstanceKey, bcb)` slots while nested inlining (`C` inside `B`) keeps innermost `C`. | `[]` |
| `ce1_nondominated_single_def_in_ssa_reads_unbound_vreg` | **Counterexample 1**: Keeping a non-dominated single-def local (`cm_3`) in `.ssa` fails with `.error .ssaUseBeforeDef`, while `.memory` matches MIR (`uninit`). | `[propext]` |
| `ce2_unpromoted_shared_cleanup_join_violates_seh_funclet_isolation` | **Counterexample 2**: Before `Internal -> Funclet` promotion of `bb4` in `seh_true_internal_join_promotion`, `7 -> 4` emits intra-funclet `br` `(false, false)` while `6 -> 4` emits `cleanupret` `(true, true)`, violating WinEH funclet color uniqueness until `propagateEdge` promotes `bb4`. | `[]` |
| `ce3_non_out_summable_abort_block_breaks_naive_outflow_conservation` | **Counterexample 3**: On a non-out-summable `Yield`/aborting block (`10` entries, `7` resumes), naive outflow conservation errs by `3` whereas `BalancedFlowGraph`'s forced sink edge absorbs the deficit (`7 + 3 = 10`). | `[]` |

---

### 6. Consequences for `joshlf/anneal` (`c131b320`) and Verified `rustc` Backends

`Basis: source + derived`

Inspecting `trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`, and `trusted/correspondence/Trusted/Correspondence.lean` in `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`:

1. **Current Fail-Closed Status of Coverage and Cleanup Statements:** `Trusted.MirAst.StatementKind` (`MirAst.lean:630-662`) explicitly places `Coverage(CoverageKind)` into `.unsupported`, matching `RefStatementKind` in `Correspondence.lean:166-192` so any instrumented MIR body fails closed as `.fault .unsupported` in `MirSemantics`. Likewise, `BasicBlock.cleanup : Bool := false` (`MirAst.lean:813`) and `TerminatorKind.unwindResume` (`MirAst.lean:790`) are faithfully encoded in `MirAst`/`Correspondence` while `evalTerminator` (`MirSemantics.lean:1543-1569`) rejects both `bb.cleanup == true` on `Return` and `.unwindResume` with `.fault .unsupported`. There is thus **zero** unsoundness at `c131b320`.
2. **Requirements for a Verified Drop-In `rustc` Backend:**
   - **MIR-to-SSA Promotion (`non_ssa_locals` vs. Block-Argument SSA):** A verified backend cannot promote MIR locals to $\phi$-free SSA virtual registers using single-definition checks alone (`ce1`): it must either enforce the full `LocalKind::SSA` criteria (`DefLocation::dominates` including edge dominance for `CallReturn`, no mutating projections, no borrows, no `type_needs_drop` drops, and `Field`/single-variant `Downcast` reads only) via a dominance-checked translation validator, or emit full block-argument SSA (`AnSSA`) where joins bind parameters explicitly on edges. In addition, ZST locals with `Drop` must still receive valid distinct/aligned stack allocations if their address can be observed across drop calls (`zst_with_drop_promotes_to_memory`).
   - **Windows MSVC / Wasm Funclet Partition Verification:** A verified backend targeting `x86_64-pc-windows-msvc` or `aarch64-pc-windows-msvc` must verify after `cleanup_kinds` that (i) every cleanup edge `u -> v` satisfies `kinds[u].funclet_bb(u) == kinds[v].funclet_bb(v)` OR `kinds[v] == CleanupKind::Funclet` (`ce2`), (ii) `funclet_succs` forms an acyclic forest (each funclet has $\le 1$ parent funclet), and (iii) no cleanup block branches back to a `NotCleanup` block. Checking this post-pass partition witness in a verified compiler avoids relying on unverified RPO traversal assumptions.
   - **Semantic Transparency of `-C instrument-coverage`:** Because `StatementKind::Coverage(VirtualCounter)` performs only non-aliasing monotonic increments to dedicated `.bss`/`__llvm_prf_cnts` profiler arrays (never read by normal Rust code), a verified optimizer or codegen pass may erase `StatementKind::Coverage` under functional behavioral equivalence while preserving runtime execution semantics, *or* keep counters intact provided counter array pointers stay disjoint from Rust's heap/stack memory model. Any proof claiming reconstructed coverage expressions match execution counts must restrict conservation equations strictly to `is_out_summable` non-panicking paths (`ce3` and `#78544`).

---

## Boundaries

- **Not examined:**
  - Exact assembly or machine-code emission (`x86_64` / `AArch64`) inside LLVM `WinEHPrepare`, `X86WinEHStatePass`, or `COFF` `.lcovmap$M`/`.lcovfun$M` linker GC behavior under `/OPT:REF` on Windows hosts (no native Windows PE/COFF execution environment was used; Part B verified LLVM IR up to `--emit=llvm-ir`).
  - MC/DC (`-C instrument-coverage=mcdc`) bitmap instrumentation (`__llvm_prf_bits` and `AtomicRMWInst::Or` in `InstrProfiling.cpp:1502-1511`).
  - Alternative codegen backends (`rustc_codegen_cranelift` and `rustc_codegen_gcc`), neither of which was compiled or executed in this investigation.
  - Inline assembly (`InlineAsm`) label targets inside `LocalAnalyzer` (`MutatingUseContext::AsmOutput`) and `CoverageGraph::bcb_filtered_successors`.
- **Known not to apply:**
  - Claiming that `rustc_codegen_ssa::mir::analyze::non_ssa_locals` emits SSA $\phi$-nodes for multi-branch or conditionally initialized MIR locals does **not** apply (`cm_2` and `cm_3` both emit stack `alloca`s and zero `phi`s in pre-pass LLVM IR; `analyze.rs:93, 227-234`).
  - Claiming that single-definition locals always stay in SSA does **not** apply (`ce1` and `cm_3`: non-dominated reads and `MutatingUseContext::Borrow`/`RawBorrow` force `LocalKind::Memory`).
  - Claiming that `LocalKind::ZST` locals *never* allocate stack slots does **not** apply: `MutatingUseContext::Drop` promotes any ZST local with `type_needs_drop(ty) == true` to `LocalKind::Memory` (`analyze.rs:254-264`, producing `alloca [0 x i8]` for `OuterGuard`/`InnerGuard` in Part B).
  - Claiming that `cleanup_kinds` promotes shared cleanup blocks *only* when targeted by normal `invoke` edges does **not** apply (`seh_true_internal_join_promotion` and `ce2` prove that RPO `Internal -> Funclet` promotion handles shared joins reached exclusively from other funclets).
  - Claiming that Kirchhoff outflow conservation `flow(u) = sum_{v in succ(u)} flow(u -> v)` holds blindly for all MIR blocks does **not** apply: `Yield`, `Return`, diverging calls, inescapable loops, and panicking calls (`#78544`) break naive outflow equality unless routed to the `BalancedFlowGraph` sink (`ce3`).
- **Unsupported:**
  - `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`) marks `StatementKind::Coverage`, `TerminatorKind::UnwindResume`, and `Return` inside `BasicBlock.cleanup == true` as `FaultKind.unsupported`.
  - `cleanup_kinds` (`analyze.rs:348-354`) and `llbb_characteristics` (`block.rs:124-125`) explicitly reject multi-parent funclet graphs and cleanup-to-normal jumps via `span_bug!` ICEs.
- **Unknown:**
  - Whether future `rust-lang/rust` releases will resolve `#78544` by integrating unwind/catch edges into `CoverageGraph`, or replace `BalancedFlowGraph` counter placement with lightweight profiling/sampling intrinsics.

---

## Evidence

### Upstream Primary Sources Examined

Line numbers below list `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`1.102.0-nightly`) first, followed by `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`) in parentheses where offsets or symbols differ.

| Repository & Revision | File Path | Inspected Items & Exact Lines |
| :--- | :--- | :--- |
| `rust-lang/rust` (`3ef0c22cd` / `14210df0e`) | `compiler/rustc_codegen_ssa/src/mir/analyze.rs` | `non_ssa_locals` `L18-57`; `LocalKind` `L59-68`; `LocalAnalyzer::define` `L77-95` (`L77-96`, `BackendRepr::Memory` vs `is_backend_immediate`); `process_place` `L97-168`; `visit_local` `L194-268` (`L215` `Retag` removed); `CleanupKind` `L275-290`; `cleanup_kinds(mir, nop_landing_pads)` `L295-408` (`L296-403`) |
| `rust-lang/rust` (`3ef0c22cd`) | `compiler/rustc_codegen_ssa/src/mir/mod.rs` | `LocalRef` `L145-197`; `codegen_mir` `nop_landing_pads` pruning, `non_ssa_locals`, and local allocation `L202-363`; `arg_local_refs` `L525-580` |
| `rust-lang/rust` (`3ef0c22cd`) | `compiler/rustc_codegen_ssa/src/mir/{locals.rs, operand.rs, place.rs, statement.rs}` | `Locals` & `overwrite_local` `locals.rs:15-83`; `OperandValue` `operand.rs:28-80`; `maybe_codegen_consume_direct` & `codegen_consume` `operand.rs:1072-1141`; `PlaceRef::alloca` `place.rs:111-170`; `codegen_statement` `statement.rs:12-125` |
| `rust-lang/rust` (`3ef0c22cd`) | `compiler/rustc_codegen_ssa/src/mir/block.rs` | `TerminatorCodegenHelper::{funclet, llbb_with_cleanup, llbb_characteristics, funclet_br}` `L58-162`; `do_call` MSVC SEH vs Wasm `Terminate` `L222-246`; `codegen_resume_terminator` `L412-425`; `ReturnDest` & `store_return` `L2530-2546`; `landing_pad_for_uncached` `L2210-2233` |
| `rust-lang/rust` (`3ef0c22cd` / `14210df0e`) | `compiler/rustc_codegen_ssa/src/mir/coverageinfo.rs` & `compiler/rustc_middle/src/mir/{mod.rs, coverage.rs}` | `codegen_coverage` `coverageinfo.rs:8-18`; `SourceScope::inlined_instance` `mir/mod.rs:1488-1500`; `DefLocation::dominates` `mir/mod.rs:1680-1709`; `CoverageKind::{Point, BlockMarker, VirtualCounter}`, `CoverageMirInfo`, `CoverageCodegenInfo`, `NodeFlowData` `mir/coverage.rs:74-264` (`L74-239` in `14210df0e`) |
| `rust-lang/rust` (`3ef0c22cd` / `14210df0e`) | `compiler/rustc_mir_transform/src/coverage/{mod.rs, counters.rs, balanced_flow.rs, node_flow.rs, graph.rs, from_mir.rs, query.rs}` | `InstrumentCoverage` `mod.rs:25-114`; `prepare_bcb_counters_data`, `make_node_flow_priority_list`, `transcribe_counters` `counters.rs:29-199`; `BalancedFlowGraph::for_graph` `balanced_flow.rs:56-81`; `node_flow_data_for_balanced_graph` & `SpantreeBuilder` `node_flow.rs:25-273`; `CoverageGraph::from_mir` & `bcb_filtered_successors` `graph.rs:35-433`; `CoverageKind::Point` vs statement spans `from_mir.rs:48-65` (`L28-115` in `14210df0e`); `coverage_codegen_info` & `is_inlined` `query.rs:94-172` (`L92-158` in `14210df0e`) |
| `rust-lang/rust` (`3ef0c22cd`) | `compiler/rustc_mir_transform/src/{cleanup_post_borrowck.rs, inline.rs}` & `compiler/rustc_codegen_llvm/src/coverageinfo/{mod.rs, llvm_cov.rs, mapgen.rs, mapgen/covfun.rs}` | `CleanupPostBorrowck` `L39-41`; `Integrator::visit_source_scope_data` `inline.rs:1233-1253`; `add_coverage` `coverageinfo/mod.rs:87-133`; `CovmapVersion::Version7` & `emit_covmap_record` `mapgen.rs:27-228`; `emit_covfun_record` `covfun.rs:240-311` |
| `rust-lang/rust` (`3ef0c22cd`) | `compiler/rustc_llvm/llvm-wrapper/{PassWrapper.cpp, CoverageMappingWrapper.cpp}` | `Options.Atomic = true; InstrProfilingLoweringPass` `PassWrapper.cpp:842-845`; `LLVMRustCoverageWriteFunctionMappingsToBuffer` `CoverageMappingWrapper.cpp` |
| `llvm/llvm-project` (`6dfe1677ab8d`) | `llvm/include/llvm/ProfileData/InstrProfData.inc`, `llvm/lib/Transforms/Instrumentation/InstrProfiling.cpp` | `INSTR_PROF_*_COMMON`/`_COFF` `InstrProfData.inc:823-856`; `AtomicRMWInst::Add` monotonic counter lowering `InstrProfiling.cpp:1417-1431` |
| `joshlf/anneal` (`c131b320`) | `trusted/lean/Trusted/{MirAst, MirSemantics}.lean`, `trusted/correspondence/Trusted/Correspondence.lean` | `StatementKind.unsupported` (`Coverage`), `UnwindAction.cleanup`, `BasicBlock.cleanup` `MirAst.lean:630-814`; `evalTerminator` `MirSemantics.lean:1543-1570`; `RefStatementKind` `Correspondence.lean:166-192` |

### Preserved Package Artifacts (`support/`)

- [`support/probe_ssa_analyzer_funclets_and_coverage.py`](support/probe_ssa_analyzer_funclets_and_coverage.py) — standalone Python 3.10+ empirical harness running all 6 `#[custom_mir]` `LocalAnalyzer` cases, both `#![no_core]` `x86_64-pc-windows-msvc` SEH funclet specimens (`seh_shared_cleanup_promotion` and `seh_true_internal_join_promotion`), and the live `-C instrument-coverage` execution round-trip (`hot_loop_diamond`, `generic_inlined`, `llvm-readobj`, `llvm-profdata`, `llvm-cov`).
- [`support/probe_results.json`](support/probe_results.json) — live execution output captured on `2026-11-22` with `rustc 1.98.0-nightly (14210df0e27ccd7d9e6a05b8085cbd438e4bbc65)` and `LLVM 22.1.6`.
- [`support/recorded_llvm23_1_102_0_nightly.json`](support/recorded_llvm23_1_102_0_nightly.json) — scrubbed execution comparison baseline recorded on `rustc 1.102.0-nightly (3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1)` with `LLVM 23.1.5`.
- [`support/SsaLocalAnalyzerAndCoverageFlow.lean`](support/SsaLocalAnalyzerAndCoverageFlow.lean) — standalone constructive `Lean v4.34.1` formalization (33 theorems total, zero external imports, zero `sorry`, zero `Classical.choice`, zero `omega`/`bv_decide`/`native_decide`).
- [`support/lean_check_output.txt`](support/lean_check_output.txt) — stdout of `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true support/SsaLocalAnalyzerAndCoverageFlow.lean` (`exit code 0`, zero warnings).
- [`support/lean_axioms_all_theorems.txt`](support/lean_axioms_all_theorems.txt) — exhaustive `#print axioms` verification across all 33 `theorem` declarations (including private helper lemmas), confirming only `[propext]` / `[propext, Quot.sound]` / no axioms.

---

## Revalidation

### 1. Re-run the Empirical `rustc` + LLVM IR + Coverage Probe

Requires a nightly `rustc` toolchain with `rust-std-x86_64-pc-windows-msvc` and `llvm-tools` installed:

```bash
python3 support/probe_ssa_analyzer_funclets_and_coverage.py --out fresh_probe_results.json
```

**Discriminating checks on `fresh_probe_results.json`:**
1. `part_a_local_analyzer_ssa_vs_memory`: `cm_1` and `cm_4` report `alloca_count == 0`, `phi_count == 0`, `load_count == 0`, `store_count == 0`; `cm_2`, `cm_3`, `cm_5`, `cm_6` all report `alloca_count == 1` and `phi_count == 0`.
2. `part_b_msvc_seh_funclet_promotion`: `rc == 0`, `seh_shared_cleanup_promotion` contains `cleanupret from %cleanuppad1 unwind label %funclet_bb6`, and `seh_true_internal_join_promotion.cleanuppad_def_count == 3` with both inner funclets unwinding via `cleanupret ... unwind label %funclet_bb4`.
3. `part_c_instrument_coverage_bcb_flow`:
   - `hot_loop_mir_noncleanup_bbs == 8`, `hot_loop_virtual_counters_bcb == 7`, `hot_loop_physical_atomic_increments_in_prepass_llvm_ir == 3` (all `atomicrmw add ptr ... i64 1 monotonic, align 8`), `main_inlined_increment_calls_count_prepass == 9`.
   - `elf_coverage_sections` contains all 5 sections (`__llvm_prf_names`, `__llvm_prf_cnts`, `__llvm_prf_data`, `__llvm_covfun`, `__llvm_covmap`).
   - `llvm_cov_functions` reports `generic_inlined::<u32>` `count == 10` (`[10, 10, 10, 0, 10]`), `generic_inlined::<u64>` `count == 7` (`[7, 7, 0, 7, 7]`), and `hot_loop_diamond` `region_exec_counts` containing `[..., 101, 100, 25, 75, 100, 1, 1]`.

### 2. Re-check the `Lean v4.34.1` Mechanization

```bash
lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
    support/SsaLocalAnalyzerAndCoverageFlow.lean
```

Expected: exit code `0`, zero compiler warnings/errors, and every `#print axioms` entry reports only `[propext]`, `[propext, Quot.sound]`, or no axioms.

### 3. Narrow Upstream Diff Targets

When tracking newer `rust-lang/rust` or `joshlf/anneal` revisions, inspect only:
- `compiler/rustc_codegen_ssa/src/mir/analyze.rs` (`LocalAnalyzer`, `cleanup_kinds`), `block.rs` (`llbb_characteristics`, `funclet_br`), `operand.rs` (`maybe_codegen_consume_direct`), and `coverageinfo.rs` (`codegen_coverage`).
- `compiler/rustc_mir_transform/src/coverage/{mod.rs, counters.rs, counters/balanced_flow.rs, counters/node_flow.rs, graph.rs, query.rs}` and `compiler/rustc_codegen_llvm/src/coverageinfo/{mod.rs, mapgen.rs, mapgen/covfun.rs}`.
- `compiler/rustc_llvm/llvm-wrapper/PassWrapper.cpp` (`Options.Atomic` for `InstrProfilingLoweringPass`).
- `joshlf/anneal`: `StatementKind`, `UnwindAction`, and `BasicBlock.cleanup` in `trusted/lean/Trusted/{MirAst, MirSemantics}.lean` and `trusted/correspondence/Trusted/Correspondence.lean`.
