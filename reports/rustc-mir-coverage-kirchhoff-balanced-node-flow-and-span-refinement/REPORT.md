# rustc MIR InstrumentCoverage: Kirchhoff Flow Conservation, Knuth–Stevenson Spanning-Tree Allocation, Unwind Deficits, and Span Refinement

## Summary

To instrument Rust programs for source-based code coverage with minimal runtime overhead, `rustc_mir_transform::coverage` transforms each eligible function's MIR control-flow graph (`CFG`) into a simplified `CoverageGraph` of `BasicCoverageBlock` (`BCB`) nodes (`graph.rs`), augments it into a synthetic `BalancedFlowGraph` (`balanced_flow.rs`), computes a minimum spanning-tree counter basis via the Knuth–Stevenson algorithm (`node_flow.rs`, `counters.rs`), defers physical counter allocation until after MIR optimizations (`query.rs`), and distills raw HIR/MIR spans into disjoint `__llvm_covmap` / `__llvm_covfun` mapping regions (`spans.rs`, `mapgen/covfun.rs`). Primary-source inspection across `rust-lang/rust` HEAD (`5debe6a1244452beced762385f88a51857a915fc`), `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), `llvm/llvm-project` HEAD (`dd54bc3427332702425782da54fe306cecd3cdb5`), and `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`), paired with an empirical dual-profile `rustc` / `llvm-profdata` / `llvm-cov` probe (`support/probe_coverage_kirchhoff_node_flow_and_spans.py` and `support/probe_results.json`) and a `1,704`-line Lean `v4.34.1` kernel-checked formalization (`support/MirCoverageKirchhoffNodeFlowAndSpansSoundness.lean`), establishes seven principal results:

1. **Exact pipeline placement and Anneal MIR/TCB incompatibility**: `InstrumentCoverage` executes inside `mir_promoted` (producing `MirPhase::Analysis(AnalysisPhase::Initial)`) before borrow checking, inserting `CoverageKind::VirtualCounter { bcb }` into each BCB `leader_bb` alongside analysis-only coverage statements removed later by `CleanupPostBorrowck` (`cleanup_post_borrowck.rs:42-44`). Physical `CounterId` and `CovTerm` allocation is postponed to `tcx.coverage_codegen_info` (at `14210df0e27`: `tcx.coverage_ids_info`), which queries `tcx.instance_mir` (`optimized_mir`) so MIR optimizations can prune dead branches before physical `@__profc_*` counters are allocated. In `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`), `Trusted/MirAst.lean:642-662` collapses `StatementKind::Coverage(_)` to `StatementKind.unsupported`, which `Trusted/MirSemantics.lean:1427` rejects with `.fault .unsupported`. Consequently, `-Cinstrument-coverage` cannot currently execute under Anneal's MIR semantics without ghost-statement erasure, though within Anneal's non-panicking, non-unwinding verified subset, Kirchhoff flow conservation holds unconditionally.
2. **Unwind-edge stripping trades unwinding accuracy for straight-line chaining (`graph.rs`)**: `bcb_filtered_successors` (`graph.rs:366-406`) strips unwind targets on `Assert`, `Drop`, `Call`, and `FalseUnwind`, strips imaginary edges on `FalseEdge`, and omits `Unreachable` blocks, allowing multi-`Call` linear chains to collapse into a single BCB (`is_out_chainable == true`). When a call panics mid-BCB (reproduced in `unwind_mid_bcb`), the post-call statements and functions never execute (`post_call_marker` entry count `0`), yet inherit the pre-call BCB's entry count (`1` in `llvm-cov show` on lines 72–75).
3. **Synthetic `BalancedFlowGraph` closure establishes exact Kirchhoff conservation on terminating executions (`balanced_flow.rs`)**: Adding one synthetic `sink` node receiving edges from (i) nodes with `!is_out_summable` (such as `Yield`), (ii) zero-successor exits (`Return`, diverging `Call`, `UnwindResume`, `UnwindTerminate`, `CoroutineDrop`, `TailCall`), and (iii) inescapable loops identified by `DepthFirstSearch` over `ReversedGraph` + `union_not`, together with the single closing edge `sink -> start_node`, enforces exact in-flow/out-flow conservation across every node (proved in Lean for single paths and arbitrary finite batches of terminating traces). Early unwinds break conservation by an exact measurable deficit (`netFlow(unwindNode) = +1`, `netFlow(startNode) = -1`, `netFlow(sink) = 0`), directly observed in `unwind_loop_deficit` (`acc` return evaluates to `c1 - c2 = 4 - 4 = 0`, hiding 1 unwinding panic).
4. **Knuth–Stevenson supernode contraction minimizes physical counters cleanly, modulo an upstream priority-list sign inversion (`node_flow.rs`, `counters.rs`)**: Merging each node's successors into a `UnionFind` supernode turns multi-way branches into single supernode edges, and `SpantreeBuilder` computes an exact integer cycle basis (`|V_super| - 1` tree edges assigned derived expressions, remaining chords assigned physical counters). However, **`make_node_flow_priority_list` (`counters.rs:64-72`) contains a polarity bug**: line 66 calls `Ord::cmp(&graph[a].is_out_summable, &graph[b].is_out_summable)` **without `.reverse()`** under the comment `// Prefer a physical counter for return/yield nodes.` Because `false < true` in Rust, `Return`/`Yield` nodes (`is_out_summable == false`) sort *earlier* (immediately after `sink`), giving them expressions instead of physical counters, while `is_reloop_node` and `cmp_in_dominator_order` both include `.reverse()` matching their comments. This inversion is directly observed in live `@__covrec_*` records (`unwind_loop_deficit` `Return` -> `e8 = c1 - c2`; `inescapable_branch` `Return` -> `e0 = c0 - c1`).
5. **Post-MIR pruning vs. LLVM loop unrolling (`query.rs`, `opt_level_2`)**: When MIR optimization eliminates a dead branch before `coverage_codegen_info` / `coverage_ids_info` runs, `query.rs` partitions unreachable BCBs late in `priority_list[1..]` and `transcribe_counters` replaces omitted chords with `CovTerm::Zero`, cutting `opt_pruned_branch`'s `@__profc_*` length from `2` to `1` and expressions from `1` (`c0 - c1`) to `0`. Conversely, LLVM backend optimization (`-Copt-level=2`) leaves `@__profc_*` lengths frozen at the MIR count while unrolling/eliminating `atomicrmw add` instructions in IR (`diamond_and_nested_loop`: `profc_len = 6`, `atomicrmw = 31`; `macro_and_match_spans`: `profc_len = 6`, `atomicrmw = 5`).
6. **Signed-to-unsigned wraparound (`18.4E` / `INT64_MAX`) and LLVM `CounterExpressionsMinimizer` orphaned-duplicate emission (`llvm/llvm-project`)**: LLVM evaluates counter expressions in signed `int64_t` (`CoverageMapping.cpp:239`), stores results into a `uint64_t` map (`CoverageMapping.cpp:788`), renders negative deficits `-d` as `2^64 - d` (`18.4E` in `llvm-cov show` for `-1`, reproduced on the unreached `while` body in `unwind_underflow_loop` where `c2 - c0 = 0 - 1 = -1`), and clamps values above `INT64_MAX` (`9223372036854775807`) during `llvm-cov export` (`CoverageExporterJson.cpp:84`). Simultaneously, LLVM's `CounterExpressionsMinimizer` (`CoverageMappingWriter.cpp:74-105`) uses `1` as its "visited-but-unassigned" sentinel in `AdjustedExpressionIDs`, colliding with re-indexed IDs `>= 1` in `UsedExpressions` and re-emitting duplicated orphaned expressions into `__llvm_covfun` (`e1, e3, e4` in `coroutine_yield_once`; `e1, e2, e4, e6, e7` in `fallible_and_panic_paths`; `e1, e7` in `diamond_and_nested_loop`).
7. **Span refinement guarantees cross-BCB disjointness prior to non-empty brace widening (`spans.rs`)**: `extract_refined_covspans` distills bang-macro and `await` expansions via `minmax_bcbs.min` (truncating bang-macro call sites at `'!'` via `span_through_char`), drops compiler-inserted full-body spans and closure/const-eval holes (`discard_spans_overlapping_holes`), runs `remove_unwanted_overlapping_spans` to guarantee strict **cross-BCB** disjointness while allowing same-BCB nesting between `pending` and `refined`, widens empty spans over adjacent `{`/`}` by `BytePos(1)`, and merges adjacent same-BCB spans (`merge_if_eligible`). Mechanized verification proves cross-BCB disjointness for `remove_unwanted_overlapping_spans` and shows why executing `ensure_non_empty_span` strictly before `merge_if_eligible` prevents merging across an intervening distinct-BCB region.

---

## Applicability

These findings apply to four pinned software artifacts and their interfaces:

| Subject | Exact Revision / Version | Examined Subsystems | Role in Report |
| :--- | :--- | :--- | :--- |
| `rust-lang/rust` (HEAD) | `5debe6a1244452beced762385f88a51857a915fc` | `compiler/rustc_mir_transform/src/{lib.rs,cleanup_post_borrowck.rs,coverage/*}`, `compiler/rustc_codegen_llvm/src/coverageinfo/{mod.rs,mapgen/covfun.rs}` | Primary upstream Rust source specification of coverage CFG construction, flow balancing, counter assignment, delayed codegen query, and covfun emission |
| `rust-lang/rust` (installed nightly) | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly`, `2026-05-31`, `x86_64-unknown-linux-gnu`, LLVM `22.1.6`) | Identical `coverage/{graph.rs,counters.rs,counters/balanced_flow.rs,counters/node_flow.rs,spans.rs}`; pre-refactor `query.rs` and MIR instrumentation | Empirical execution target for `-Cinstrument-coverage` under `[-Zmir-opt-level=0, -Copt-level=0]` and `[-Copt-level=2]`, LLVM IR / covrec decoding, and `llvm-profdata`/`llvm-cov` verification |
| `llvm/llvm-project` (HEAD) | `dd54bc3427332702425782da54fe306cecd3cdb5` | `llvm/lib/ProfileData/Coverage/{CoverageMapping.cpp,CoverageMappingWriter.cpp}`, `llvm/tools/llvm-cov/CoverageExporterJson.cpp` | Primary C++ source explaining `__llvm_covfun` encoding/minimization, `int64_t -> uint64_t` counter evaluation, `18.4E` display, and `INT64_MAX` JSON clamping |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/Trusted/{MirAst.lean,MirSemantics.lean}` | Trusted MIR syntax and step semantics determining what `-Cinstrument-coverage` artifacts Anneal can/cannot execute |

### Version Comparison: `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`) vs. `5debe6a1244452beced762385f88a51857a915fc` (HEAD)

Direct source inspection across both revisions establishes exact continuity in all four core algorithmic modules and specific divergence at the HIR-eligibility and MIR-representation boundaries:

- **Shared identically across both revisions (`source`)**:
  - `compiler/rustc_mir_transform/src/coverage/graph.rs`: BCB chaining rules, `bcb_filtered_successors`, dominator rank calculation, and `is_out_summable` computation.
  - `compiler/rustc_mir_transform/src/coverage/counters/balanced_flow.rs`: synthetic `sink`, `Union`/`ReversedGraph` inescapable-loop DFS, and `sink -> start_node`.
  - `compiler/rustc_mir_transform/src/coverage/counters/node_flow.rs`: `UnionFind` supernode contraction and `SpantreeBuilder` algorithm.
  - `compiler/rustc_mir_transform/src/coverage/counters.rs`: `make_node_flow_priority_list` (including the un-reversed `Ord::cmp(&graph[a].is_out_summable, &graph[b].is_out_summable)` at line 66) and `transcribe_counters`.
  - `compiler/rustc_mir_transform/src/coverage/spans.rs`: `extract_refined_covspans`, `single_covspan_for_child_context`, `discard_spans_overlapping_holes`, `remove_unwanted_overlapping_spans`, `ensure_non_empty_span`, and `Covspan::merge_if_eligible`.
- **Specific to `14210df0e27` (`1.98.0-nightly`, `query.rs` and MIR metadata)**:
  - `is_eligible_for_coverage` is registered as `providers.hooks.is_eligible_for_coverage` and checks `!def_kind.is_fn_like()`, `CodegenFnAttrFlags::NAKED`, and `!tcx.coverage_attr_on(def_id)`. It does not exclude comptime-only `const fn` / `const` items.
  - The final query is named `coverage_ids_info` (`providers.queries.coverage_ids_info`), reading `mir_body.function_coverage_info` and returning `CoverageIdsInfo`.
  - Analysis-phase coverage statements removed by `CleanupPostBorrowck` use `SpanMarker`/`BlockMarker` variants rather than HIR-point markers.
- **Specific to `5debe6a12` (HEAD, `query.rs`, `mod.rs`, `covfun.rs`)**:
  - `is_eligible_for_coverage` is promoted to a query (`providers.queries.is_eligible_for_coverage`) and explicitly excludes functions with `DefKind::Fn | DefKind::AssocFn` and `hir::Constness::Const { always: true }` (`query.rs:41-47`), avoiding useless instrumentation of comptime-only functions and preventing ICEs when generating unused-function symbol records.
  - `mir_body.coverage_mir_info: Option<Box<CoverageMirInfo>>` and `tcx.coverage_codegen_info` returning `CoverageCodegenInfo` replace `function_coverage_info` / `CoverageIdsInfo`.
  - `CleanupPostBorrowck` still uses `kind.is_removed_after_analysis()` (`cleanup_post_borrowck.rs:42`), preserving `CoverageKind::VirtualCounter { bcb }` while replacing analysis-only markers with `Nop`.

All Lean `v4.34.1` theorems in `support/MirCoverageKirchhoffNodeFlowAndSpansSoundness.lean` formalize abstract state models extracted directly from these shared algorithms (not importing `joshlf/anneal`'s `Trusted` crate); their scope assumptions are recorded per-theorem in **Findings** and **Boundaries**.

---

## Findings

### 1. MIR Pipeline Placement, CleanupPostBorrowck, and Anneal TCB Boundary

`Basis: source + execution`

In `compiler/rustc_mir_transform/src/lib.rs`, `coverage::InstrumentCoverage` runs as part of `mir_promoted` (following `promote_consts` and `SimplifyCfg::PromoteConsts`), producing `MirPhase::Analysis(AnalysisPhase::Initial)` before borrow checking. Its `PassPolicy` is `PassPolicy::optional(ctx.instrument_coverage())` (`coverage/mod.rs:28`), meaning zero coverage statements are injected unless `-Cinstrument-coverage` (or equivalent coverage flags) is enabled.

When active and `tcx.is_eligible_for_coverage(def_id)` holds with a non-`Unreachable` `START_BLOCK` (`mod.rs:31-51`), `instrument_function_for_coverage` performs four operations (`mod.rs:55-90`):

1. Extracts HIR spans and source hash (`hir_info::extract_hir_info`).
2. Builds `CoverageGraph::from_mir(mir_body)` (`graph.rs`).
3. Refines source mappings (`mappings::extract_mappings_from_mir` -> `spans::extract_refined_covspans`).
4. Computes balanced flow supernodes and priority order (`counters::prepare_bcb_counters_data`), injects `StatementKind::Coverage(CoverageKind::VirtualCounter { bcb })` at statement index `0` of every BCB `leader_bb`, and attaches `CoverageMirInfo` to `mir_body.coverage_mir_info` (at `14210df0e27`: `function_coverage_info`).

Crucially, `CleanupPostBorrowck::run_pass` (`cleanup_post_borrowck.rs:25-70`) transitions MIR to `Runtime(PostCleanup)` (`mir_drops_elaborated_and_const_checked`), turning `FalseEdge` and `FalseUnwind` terminators into unconditional `Goto(real_target)` and converting `StatementKind::Coverage(kind)` to `Nop` **only** if `kind.is_removed_after_analysis()`. Every `CoverageKind::VirtualCounter { bcb }` survives intact through borrowck cleanup and remains inside MIR throughout optimizations. Live MIR dumps at `-Zmir-opt-level=0` confirm that `InstrumentCoverage.before.mir` has zero `VirtualCounter` statements, `InstrumentCoverage.after.mir` inserts one `Coverage::VirtualCounter(bcbN)` at the start of every BCB leader block plus `coverage Code { bcb: ... } => ...` debug headers, and both `CleanupPostBorrowck.before.mir` and `CleanupPostBorrowck.after.mir` preserve the exact same `VirtualCounter` count (`support/probe_results.json`).

**Consequence for Anneal (`joshlf/anneal@c131b320e27`)**: In `trusted/lean/Trusted/MirAst.lean:642-662`, `StatementKind` maps `rustc`'s `StatementKind::Coverage(CoverageKind)` directly to `StatementKind.unsupported`. In `trusted/lean/Trusted/MirSemantics.lean:1427`, stepping `.unsupported` immediately produces `.fault .unsupported`. Furthermore, Anneal's `TerminatorKind` only supports `.goto`, `.switchInt`, and `.ret` without faulting on calls/asserts/drops/unwinds (`MirSemantics.lean` faults on `.assert`, `.call`, `.unwindResume`, and `.unsupported`). Thus:

- Any MIR body captured with `-Cinstrument-coverage` is rejected (`.fault .unsupported`) if fed directly to Anneal's operational semantics.
- Capturing without `-Cinstrument-coverage` (or extending Anneal's extractor/theory with explicit ghost-statement erasure for `StatementKind::Coverage(_)`) is required. Within the panic-free, call-free, unwind-free MIR subset that Anneal executes cleanly, Kirchhoff flow balance holds strictly whenever execution terminates.

---

### 2. Basic Coverage Block Construction and Unwind/False-Edge Stripping (`graph.rs`)

`Basis: source + execution + derived`

`CoverageGraph::compute_basic_coverage_blocks` (`graph.rs:120-182`) collapses straight-line MIR `BasicBlock`s into coarser `BasicCoverageBlock` (`BCB`) nodes by traversing `CoverageRelevantSubgraph` in depth-first order from `mir::START_BLOCK`, filtering out blocks whose terminator is `TerminatorKind::Unreachable` (`graph.rs:157-159`).

`bcb_filtered_successors` (`graph.rs:366-406`) determines both the coverage-relevant successors (`targets`) and whether execution count conservation holds at the block's exit (`is_out_summable`):

| MIR `TerminatorKind` | `targets` Kept in `CoverageRelevantSubgraph` | Stripped Edges | `is_out_summable` | `is_out_chainable` | Source Anchor (`graph.rs`) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `SwitchInt { targets, .. }` | `targets.all_targets()` | None | `!(targets.is_empty())` | `true` iff `targets.len() == 1` | `370, 344-354` |
| `Assert { target, .. }` | `[target]` | `unwind` | `true` | `true` | `378` |
| `Drop { target, .. }` | `[target]` | `unwind` | `true` | `true` | `379` |
| `FalseEdge { real_target, .. }` | `[real_target]` | `imaginary_target` | `true` | `true` | `380` |
| `FalseUnwind { real_target, .. }` | `[real_target]` | `unwind` | `true` | `true` | `381` |
| `Goto { target }` | `[target]` | None | `true` | `true` | `382` |
| `Call { target: Some(t), .. }` | `[t]` | `unwind` | `true` | `true` | `386` |
| `Call { target: None, .. }` | `[]` | `unwind` | `false` | `false` | `386` |
| `Yield { resume, .. }` | `[resume]` | `drop` | `false` | `false` | `372-375` |
| `InlineAsm { targets, .. }` | `&targets` | `unwind` | `!(targets.is_empty())` | `targets.len() == 1` | `390` |
| `Return` / `Unreachable` / `UnwindResume` / `UnwindTerminate` / `CoroutineDrop` / `TailCall` | `[]` | N/A | `false` | `false` | `393-399` |

Two blocks `prev -> bb` chain into the same BCB (`can_chain == true`, `graph.rs:164-165`) if and only if:
1. `subgraph.coverage_successors(prev).is_out_chainable()` is `true` (`is_out_summable() && targets.len() == 1`), AND
2. `mir_body.basic_blocks.predecessors()[bb].as_slice() == &[prev]` in the **full un-filtered MIR CFG**.

Because cleanup/landing-pad blocks (`bb (cleanup)`) are only reachable via stripped `unwind` edges (and never via `targets` except if an explicit branch entered them), DFS on `CoverageRelevantSubgraph` skips cleanup pads completely (`bb_to_bcb[cleanup_bb] == None`), so cleanup pads never receive `VirtualCounter` statements. Meanwhile, a `Call { target: Some(bb_next), unwind: bb_cleanup }` terminator has `is_out_chainable == true`; as long as `bb_next` has `[bb_call]` as its sole MIR predecessor, `bb_next` is absorbed into the **same BCB** as `bb_call` (`bb_call` and `bb_next` share one entry counter at `leader_bb`).

**Empirical verification of intra-BCB post-call phantom counts (`execution`)**:
In `probe_results.json`, `unwind_mid_bcb(true, 4)` executes:
- Line 71–72: calls `may_panic_step(true, 4)`, which panics unconditionally (verified by `post_call_marker` entry count `0` in `llvm-profdata` and `llvm-cov show` lines 66–68 showing `0|`).
- Line 73–75: `let b = post_call_marker(a); b + 1 }`.
- Because `may_panic_step` and `post_call_marker` are non-diverging `Call` terminators merged into a single BCB (`bcb0`), `@__profc_...unwind_mid_bcb` has length `1` (`[1 x i64]`) placed at `bcb0`'s leader block, recording `1` on line 71 and emitting **no** distinct counter for lines 73–75. Consequently, `llvm-cov show` displays `1|` on lines 73, 74, and 75 despite zero runtime executions (`intra_bcb_post_call_phantom_count` in Lean proves the exact discrepancy is `unwinds = 1`).

Note also a subtle edge case in condition (2): checking raw `mir_body.basic_blocks.predecessors()[bb].as_slice() == &[prev]` rather than `CoverageRelevantSubgraph` predecessors means if an unreachable/imaginary edge happens to share target `bb`, chaining refuses to merge `bb` into `prev` even though `graph.predecessors[bcb_next]` only records non-stripped edges.

---

### 3. Synthetic `BalancedFlowGraph` Closure and Conservation Scope (`balanced_flow.rs`)

`Basis: source + execution + derived`

Raw `CoverageGraph`s fail local flow conservation at four classes of nodes (`balanced_flow.rs:4-9`):
- `start_node` (`bcb0`, asserted to have `predecessors[START_BCB].is_empty()` at `graph.rs:115`) has `outFlow > 0` and `inFlow = 0`;
- exit nodes (`Return`, diverging `Call`, etc.) have `inFlow > 0` and zero out-edges;
- `Yield` nodes (`is_out_summable == false`, `balanced_flow.rs` via `force_sink_edge(n) = !graph[n].is_out_summable`) have `resume` as their sole out-edge, which executes strictly fewer times if the coroutine is dropped while suspended (`inFlow >= outFlow`);
- inescapable loops (`loop { ... }` with no path reaching an exit or `Yield`) have `inFlow(SCC) > 0` across entry while zero flow exits to any `Return`.

`BalancedFlowGraph::for_graph(graph, force_sink_edge)` (`balanced_flow.rs:58-82`) constructs a conservative wrapper graph with `num_nodes() = graph.num_nodes() + 1`, where synthetic node `sink = Node::new(graph.num_nodes())` receives incoming edges from `sink_edge_nodes` computed in two stages:

1. **Direct exits and non-summable nodes (`balanced_flow.rs:64-69`)**: Insert every `node` satisfying `force_sink_edge(node) || graph.successors(node).next().is_none()` into `sink_edge_nodes`, and push those nodes as seeds onto `DepthFirstSearch::new(ReversedGraph::new(&graph))`.
2. **Inescapable-loop closure (`balanced_flow.rs:73-74`)**: Call `dfs.complete_search()` backwards from those seeds and execute `sink_edge_nodes.union_not(dfs.visited_set())`. Any reachable node that cannot reach any normal exit or `Yield` (e.g., an infinite `loop {}` arm in `inescapable_branch`) gets a synthetic edge `n -> sink`, allowing finite-time / divergence-edge flow balancing (in practice if an infinite loop never terminates, runtime counters capture only finite observations or process exit never flushes profraw).
3. **Return loop edge (`balanced_flow.rs:114-119`)**: When querying `successors(self.sink)`, yield `Some(self.graph.start_node())`. Thus `outFlow(sink) = flow(sink -> start_node) = executions(entry)`, while `inFlow(sink)` equals the sum of flows leaving all exits and non-resumed `Yield`s.

**Live verification on `coroutine_yield_once` (`Yield`) and `inescapable_branch` (`union_not`) (`execution`)**:
- `coroutine_yield_once(true)` calls `.resume(5)` once (entering the coroutine body once, hitting `yield x + 1`, then returning without resuming the second `yield`). In the closure `_RNCNvCs3MbTHFJrp4v_9cov_probe20coroutine_yield_once0B3_`, `@__profc_` has length `3`, raw `profdata` counts are `[1, 0, 0]`, and `llvm-cov show` displays `1|` on line 148 (`|mut x: i32| {`) and line 149 (`yield x + 1;`), and `0|` on lines 150–153 (`x += 10;`, `yield x + 2;`, `x + 100`, `}`). Because `Yield` sets `is_out_summable = false`, `force_sink_edge` gives the yield BCB a synthetic edge to `sink`, letting the drop-while-suspended deficit (`1 - 0 = 1`) flow directly to `sink` without underflowing post-yield blocks.
- `inescapable_branch(true, 4)` takes the early return (`if take_exit { x + 1 }`) without entering the infinite `else` `loop { ... }`. `BalancedFlowGraph` adds sink edges for the inescapable loop (`union_not`), yielding `profc_len = 7`, raw `profdata` counts `[1, 0, 0, 0, 0, 0, 0]`, and clean `1|` on line 133 (`x + 1`) and `1|` on line 143 (`}`), with `0|` on lines 135–140.

**Mechanized conservation vs. unwind deficit theorems (`Lean v4.34.1`)**:
- `kirchhoff_conservation_on_normal_trace` (`MirCoverageKirchhoffNodeFlowAndSpansSoundness.lean:430-453`): Proves via `path_netFlow_telescope` (`netFlow(p, x) = indicator(dst, x) - indicator(src, x)`) that appending `[(exitNode, bf.sink), (bf.sink, bf.base.startNode)]` to any `ValidPath` starting at `startNode` yields `inFlow = outFlow` at every node `x < bf.totalNodes`.
- `kirchhoff_conservation_aggregate` (lines 475-499): Extends exact Kirchhoff balance to any arbitrary finite list of terminating traces.
- `unwind_trace_deficit_exact` (lines 502-540): Proves that for any execution trace `p` starting at `startNode` and unwinding at `unwindNode != startNode` without reaching `sink`, conservation breaks cleanly: `netFlow(unwindNode) = +1`, `netFlow(startNode) = -1`, and `netFlow(sink) = 0`. Note also that unlike LLVM-IR exception-handling CFGs that model invoke->landingpad flows explicitly, `rustc`'s `BalancedFlowGraph` contains no unwind flow edges, so `-1` net deficits accumulate at every unwinding call site along panicking paths.

---

### 4. Knuth–Stevenson Supernode Contraction, Priority-List Inversion Bug, and Counter Transcription (`node_flow.rs`, `counters.rs`, `query.rs`)

`Basis: source + execution + derived`

#### 4.1 Supernode Contraction (`node_flow.rs:27-52`)

For each node `u`, an out-edge sum constraint has the form `flow(u) = sum_{v in succs(u)} flow(u, v)`. Rather than keeping individual edges as unknowns, `node_flow_data_for_balanced_graph` maintains a `UnionFind` forest over `0..num_nodes` and, for every node `u`, calls `.reduce(|a, b| supernodes.unify(a, b))` across `graph.successors(u)` (requiring `BalancedFlowGraph`'s guarantee that every node has at least one out-edge). After snapshotting canonical representatives (`supernodes[v]`), every node `u` induces a **single directed edge** in the contracted supernode multigraph:

$$\text{superedge}(u) : \text{supernodes}[u] \longrightarrow \text{succ\_supernodes}[u]$$

Because every non-zero edge `u -> v` enforces `supernodes[v] = succ_supernodes[u]`, all flow exiting `u` enters supernode `succ_supernodes[u]` and exits supernode `supernodes[u]`. Consequently, for **every** supernode `s` and **every** boolean cut `S : Nat -> Bool` (`supernode_in_out_balanced` and `supernode_cut_conservation` in `MirCoverageKirchhoffNodeFlowAndSpansSoundness.lean`), the cut-signed sum of node flows vanishes on terminating executions:

$$\sum_{u < n} \text{cutSign}(S, \text{sn}(u), \text{ssn}(u)) \cdot \text{flow}(u) = 0.$$

#### 4.2 Incremental Spanning-Tree Forest Rotation (`SpantreeBuilder`, `node_flow.rs:112-275`)

`make_node_counters` iterates through `priority_list` once, calling `builder.visit_node(this)`:

1. **Yank to root (`yank_to_spantree_root`, `node_flow.rs:163-197`)**: Walks parent pointers from `this_supernode` to its current spanning-tree root and reverses every edge along the path, toggling `is_reversed = !is_reversed` while preserving `claiming_node`. After rotation, `self.span_edges[this_supernode].is_none()`.
2. **Branch on connectivity (`visit_node`, `node_flow.rs:215-261`)**:
   - **Disjoint components (`this_supernode != spantree_root(succ_supernode)`)**: Adds tree edge `this_supernode -> succ_supernode` with `is_reversed = false`, `claiming_node = this`. Node `this` receives **no physical counter**; its `counter_terms[this]` vector will be populated whenever later cycle-closing chords traverse this edge.
   - **Cycle closed (`this_supernode == spantree_root(succ_supernode)`)**: Allocates a **physical counter** for `this` (`counter_terms[this].push({ node: this, op: Op::Add })`), then walks the unique spanning-tree path from `succ_supernode` back to root `this_supernode`. On every edge traversed, appends `{ node: this, op }` to `counter_terms[claiming_node]`, where `op = Op::Subtract` if `is_reversed` else `Op::Add`.

Fundamental-cut duality explains why `is_reversed` yields exact reconstruction (`spantree_cut_reconstruction_exact`): walking from `succ_supernode` (`ssn(c)`) back to root `this_supernode` (`sn(c)`) along tree edge `t` sees `is_reversed == false` when `t` and chord `c` circulate oppositely around the fundamental cycle (so separating `sn(t)` from `ssn(t)` crosses `c` oppositely to `t`, contributing `+flow(c)` to `flow(t)`), and sees `is_reversed == true` when `t` and `c` circulate in the same orientation along the cut (so recovering `flow(t)` requires `-flow(c)`). Verifying this against Knuth & Stevenson's 5-node benchmark (`[3, 1, 2, 0, 4]` -> `[0]: +c0`, `[1]: +c0 +c2 -c4`, `[2]: +c2`, `[3]: +c3`, `[4]: +c4`) yields exact node-flow reconstruction `[7, 5, 4, 12, 6]` matching `node_flow/tests.rs::example_driver` in both Python and Lean kernel `decide`.

#### 4.3 Priority-List `is_out_summable` Inversion Bug (`counters.rs:44-74`)

`make_node_counters`'s doc comment (`node_flow.rs:61-62`) and `make_node_flow_priority_list`'s doc comment (`counters.rs:43-44, 58-59`) establish the traversal invariant:
- **Earlier** nodes in `priority_list` are preferred for **counter expressions** (spanning-tree edges).
- **Later** nodes in `priority_list` are preferred for **physical counters** (chords).

Comparing all four tie-breakers in `make_node_flow_priority_list` (`counters.rs:60-72`) reveals a polarity inversion on line 66:

| Priority Key (`counters.rs:60-72`) | Commented Intent | Actual Comparator Expression | Ordering on Rust `bool` / `Ordering` (`false < true`) | Effect |
| :--- | :--- | :--- | :--- | :--- |
| Position `0` | Sink must never get a physical counter | `balanced_graph.iter_nodes().rev()` (`nodes[0] == sink`) | Always first | Matches comment |
| Primary (`counters.rs:66`) | `// Prefer a physical counter for return/yield nodes.` | `Ord::cmp(&graph[a].is_out_summable, &graph[b].is_out_summable)` **(no `.reverse()`)** | `false` (`Return`/`Yield`) sorts **before** `true` (`Ordering::Less`) | **INVERTED**: puts `Return`/`Yield` *earliest* right after `sink`, giving them **expressions** first! |
| Secondary (`counters.rs:68`) | `// Prefer an expression for reloop nodes` | `Ord::cmp(&is_reloop_node[a], &is_reloop_node[b]).reverse()` | `true` (reloop) sorts **before** `false` | Matches comment |
| Tertiary (`counters.rs:70`) | `// Otherwise, prefer a physical counter for dominating nodes.` | `graph.cmp_in_dominator_order(a, b).reverse()` | Lower dominator rank sorts **later** | Matches comment |

**Live empirical confirmation (`execution`)**:
In `probe_results.json` (`mir_opt_0`), decoded `@__covrec_*` records confirm this directly:
- In `unwind_loop_deficit`, lines `103..104` (`acc` return statement and closing brace, i.e., the `Return` BCB with `is_out_summable == false`) are assigned **`e8 = c1 - c2`** (a compound subtraction expression rather than a physical counter), while the dominating loop header (`c1 = 4`) and panic-branch guard (`c2 = 4`) receive physical counters!
- In `inescapable_branch`, lines `133` (`x + 1` return value) and `143` (`}`) receive **`e0 = c0 - c1`** (`1 - 0 = 1`), while entry `bcb0` (`c0 = 1`) and `else` block `let mut s = x` (`c1 = 0`) receive physical counters.
- In `opt_pruned_branch`, `bb5` (`bcb2`, `return;` line `128`) shares a single-term expression `[+bcb0]` -> `Counter(0)` with `bcb0`, while `bcb1` (`124`) receives `c1` and `bcb3` (`126`) receives `e0 = c0 - c1`.
- Adding `.reverse()` on `counters.rs:66` would flip `is_out_summable == false` late as intended—saving expressions on exit blocks only where cycles permit, though note that placing physical counters directly on `Return` blocks rather than entry/loop-exit headers can trade fewer physical increments when early returns exist vs. increasing hot-exit instrumentation if multiple returns share a sink.

#### 4.4 `transcribe_counters` and Delayed Codegen Pruning (`counters.rs:78-121`, `query.rs:88-153`)

Because `InstrumentCoverage` runs before MIR optimizations, `coverage_codegen_info` (`query.rs:93-153`, `coverage_ids_info` at `14210df0e27`) scans `tcx.instance_mir(instance_def)` (`optimized_mir`) for surviving non-inlined `CoverageKind::VirtualCounter { bcb }` statements (`bcbs_seen`). It then:

1. Marks `bcb_needs_counter` from `mir_info.mappings` (covering `MappingKind::Code { bcb }` and `MappingKind::Branch { true_bcb, false_bcb }`, **not** dead BCBs dropped from all mappings).
2. Re-sorts `priority_list[1..]` via `sort_by_key(|&bcb| !bcbs_seen.contains(bcb))` (`query.rs:140`), moving dead/optimized-away BCBs to the **end** of `priority_list` (keeping relative priority within both partitions).
3. Runs `make_node_counters` on this partitioned priority list so dead BCBs become chords (allocated physical counters) whenever possible, and non-dead tree edges express their counts in terms of `+dead_chord` or `-dead_chord`.
4. Calls `transcribe_counters` (`counters.rs:78-121`), which:
   - Maps any `bcb` with `!bcbs_seen.contains(bcb)` to `CovTerm::Zero`;
   - Filters each surviving BCB's `counter_terms` by `bcbs_seen.contains(term.node)` (substituting `0` for dead BCB chords);
   - Partitions remaining terms into `pos` (`Op::Add`) and `neg` (`Op::Subtract`), sorts `pos` and `neg` canonically (`pos.sort(); neg.sort();`) to maximize expression-table deduplication (`expressions_memo`), allocates dense physical `CounterId`s strictly on demand (`ensure_phys_counter`), and builds `pos - neg` via `make_sum` (`Op::Add` fold) and `make_subtracted_sum` (`Op::Subtract`).

**Empirical comparison: `-Zmir-opt-level=0` vs. `-Copt-level=2` across all 11 probe items (`execution`)**:

| Function / Closure (`cov_probe`) | `@__profc_` len (`mir_opt_0`) | `@__profc_` len (`opt_level_2`) | IR `atomicrmw add` (`mir_opt_0`) | IR `atomicrmw add` (`opt_level_2`) | Covfun Exprs (`mir_opt_0` -> `opt_level_2`) | Cause of Optimization Divergence |
| :--- | :---: | :---: | :---: | :---: | :---: | :--- |
| `opt_pruned_branch` | `2` | **`1`** | `2` | **`1`** | `1 (c0 - c1)` -> **`0` (`Zero` on line 124)** | Constant `flag = false` folded by MIR opts; `bcb1` `VirtualCounter` deleted before `coverage_ids_info` |
| `diamond_and_nested_loop` | `6` | `6` | `6` | **`31`** | `9` -> `9` | MIR kept all 6 BCBs; LLVM loop unrolling duplicated `atomicrmw add` sites |
| `unwind_loop_deficit` | `4` | `4` | `4` | **`11`** | `9` -> `9` | LLVM loop unrolling duplicated in-loop `atomicrmw add` sites |
| `macro_and_match_spans` | `6` | `6` | `6` | **`5`** | `4` -> `4` | `coverage_ids_info` fixed `num_counters = 6`; LLVM backend DCE eliminated 1 unreachable `atomicrmw` |
| `inescapable_branch` | `7` | `7` | `7` | **`1`** | `1` -> `1` | `take_exit` true path known / constant-folded in caller or LLVM backend DCE pruned 6 loop increments while `__profc_` remained length `7` |
| `coroutine_yield_once` | `4` | `4` | `4` | **`2`** | `7` -> `7` | LLVM pruned unreachable second `.resume(0)` counter sites while `num_counters` stayed `4` |
| `coroutine_yield_once::{closure#0}` | `3` | `3` | `3` | **`1`** | `0` -> `0` | LLVM pruned unreachable post-first-`yield` increments |
| `unwind_underflow_loop` | `3` | `3` | `3` | **`2`** | `2` -> `2` | LLVM folded post-unconditional-panic loop increment |
| `ctfe_and_runtime` | `2` | `2` | `2` | **`1`** | `1` -> `1` | Inlined / constant-folded at caller or LLVM DCE |
| `unwind_mid_bcb` | `1` | `1` | `1` | `1` | `0` -> `0` | Single-BCB entry counter survives identically |
| `fallible_and_panic_paths` | `5` | `5` | `5` | `5` | `10` -> `10` | Both `20/4` and `20/0` exercised without constant folding |

In Lean (`transcribeTerms_preserves_int_eval`, `dead_bcb_filtering_sound`, `dead_bcb_wrong_omission_counterexample`), we proved algebraically that filtering/re-associating `pos - neg` preserves exact `Int` semantics whenever every omitted BCB genuinely has `0` runtime executions, and exhibited an explicit counterexample showing silent corruption if a live (`count = 5`) BCB were erroneously filtered.

---

### 5. LLVM Expression Evaluation, Unsigned Underflow Clamping, and `CounterExpressionsMinimizer` Bug (`llvm/llvm-project`)

`Basis: source + execution + derived`

#### 5.1 Signed `int64_t` Evaluation -> Unsigned `uint64_t` -> `18.4E` & `INT64_MAX` Clamping

During `llvm-cov` report generation (`llvm/lib/ProfileData/Coverage/CoverageMapping.cpp`):
1. `CounterMappingContext::evaluate(const Counter &C)` (`CoverageMapping.cpp:194-248`) evaluates expressions using **signed `int64_t`** arithmetic (`LastPoppedValue = E.Kind == CounterExpression::Subtract ? LHS - RHS : LHS + RHS;`, line 239).
2. `CountedRegionEmitter::evaluateAndCacheCounter` (`CoverageMapping.cpp:781-790`) assigns `*ValueOrErr` (`int64_t`) directly into `CounterValues`, whose mapped type is **`uint64_t`** (`CoverageMapping.h`: `std::map<Counter, uint64_t> CounterValues`). Any negative `int64_t` difference `-d` wraps modulo $2^{64}$ to $2^{64} - d$ (e.g., `-1` becomes `18446744073709551615`).
3. `llvm-cov show` formats `uint64_t(2^64 - 1)` in human-readable abbreviated SI units as **`18.4E`**.
4. `llvm-cov export` passes every region, segment, and branch count through `clamp_uint64_to_int64` (`llvm/tools/llvm-cov/CoverageExporterJson.cpp:80-86`):
   ```cpp
   int64_t clamp_uint64_to_int64(uint64_t u) {
     return std::min(u, static_cast<uint64_t>(std::numeric_limits<int64_t>::max()));
   }
   ```
   clamping any wrapped `uint64_t` above $2^{63}-1$ (`9223372036854775807`) down to `9223372036854775807`.

**Live reproduction in `unwind_underflow_loop(3, true, true)` (`execution`)**:
- `cov_probe.unwind_underflow_loop.1-1-009.InstrumentCoverage.after.mir` has entry `bcb0 -> c0` (`1`), call arm `bcb1 -> c1` (`may_panic_step`, `1`), else arm `bcb6 -> e0 = c0 - c1` (`0`), loop header `bcb3 -> c2` (`while i < n`, `0`, never entered), `let acc; let i;` `bcb2 -> c0` (`1`, assigned `c0` via balanced flow conservation assuming `may_panic_step` returned normally!), return `bcb5 -> c0` (`1`), and loop body `bcb4` (`lines 81:17..84:6`) -> **`e1 = c2 - c0`**.
- At runtime, `profdata` records raw counters `[c0, c1, c2] = [1, 1, 0]`.
- `e1 = 0 - 1 = -1` (signed `int64_t`), wrapping in `CounterValues` to **`18446744073709551615`**.
- `llvm-cov show` prints **`18.4E|`** on lines 81–84, phantom **`1|`** on lines 79, 80, 85, and 86, and `llvm-cov export` JSON emits **`9223372036854775807`** on region `[81, 17, 84, 6]`.
- Verified with `0` mismatches against our independent `__covrec_*` evaluator across all 11 focus functions in both `mir_opt_0` and `opt_level_2` (Formalized in Lean by `llvm_eval_nonneg_exact` and `llvm_eval_minus_one_wraparound`).

Conversely, in `unwind_loop_deficit(5, 3)`:
- Raw counters are `[c0, c1, c2, c3] = [1, 4, 4, 2]`: entry `c0 = 1`, loop header `c1 = 4` (`i = 0, 1, 2, 3`), panic-guard block `if i == panic_at` `c2 = 4` (`lines 93:12..25`), `e0 = (c0 + c2) - c1 = (1 + 4) - 4 = 1` (`panic!("loop_unwind_boom")`), `e6 = c1 - c0 = 4 - 1 = 3` (post-if iterations before the unwind at `i = 3`), `c3 = 2` (even arm `i = 0, 2`), `e4 = c1 - (c0 + c3) = 4 - 3 = 1` (odd arm `i = 1`), and `acc` return (`lines 103..104`) evaluates `e8 = c1 - c2 = 4 - 4 = 0`—incidentally `0` only because `c1` (`4`) equaled `c2` (`4`), whereas `llvm-cov` masks any indication on `bcb0`/`bcb1` that `acc` return was bypassed via unwind rather than condition exhaustion.

#### 5.2 LLVM `CounterExpressionsMinimizer` Orphaned-Duplicate Bug (`CoverageMappingWriter.cpp:74-105`)

Decoding raw `@__covrec_*` blobs emitted by `rustc` directly in LLVM IR revealed unexpected "unreferenced" duplicate expressions in four of the eleven probe functions (`unwind_loop_deficit`, `coroutine_yield_once`, `diamond_and_nested_loop`, `fallible_and_panic_paths`):
- `coroutine_yield_once` emits 7 expressions where `e1 = c0 - c2`, `e3 = c0 - (c2 + c3)`, and `e4 = c2 + c3` are NEVER referenced by any region or outer expression, while `e2 = c0 - c2`, `e5 = c0 - (c2 + c3)`, and `e6 = c2 + c3` ARE identical copies immediately adjacent or shifted by 1!
- `fallible_and_panic_paths` emits 10 expressions with 5 unreferenced duplicates (`e1, e2, e4, e6, e7`).
- `diamond_and_nested_loop` emits 9 expressions with 2 unreferenced duplicates (`e1, e7`).
- `unwind_loop_deficit` emits 9 expressions with 3 unreferenced duplicates (`e2, e3, e7`).

Root-cause inspection of `llvm/lib/ProfileData/Coverage/CoverageMappingWriter.cpp:74-105` (`dd54bc3427332702425782da54fe306cecd3cdb5`) proves this is a sentinel-collision bug inside LLVM's own `CounterExpressionsMinimizer`:

```cpp
// CoverageMappingWriter.cpp:74-105
  CounterExpressionsMinimizer(ArrayRef<CounterExpression> Expressions,
                              ArrayRef<CounterMappingRegion> MappingRegions)
      : Expressions(Expressions) {
    AdjustedExpressionIDs.resize(Expressions.size(), 0);
    for (const auto &I : MappingRegions) {
      mark(I.Count);
      mark(I.FalseCount);
    }
    for (const auto &I : MappingRegions) {
      gatherUsed(I.Count);
      gatherUsed(I.FalseCount);
    }
  }

  void mark(Counter C) {
    if (!C.isExpression()) return;
    unsigned ID = C.getExpressionID();
    AdjustedExpressionIDs[ID] = 1;
    mark(Expressions[ID].LHS);
    mark(Expressions[ID].RHS);
  }

  void gatherUsed(Counter C) {
    if (!C.isExpression() || !AdjustedExpressionIDs[C.getExpressionID()])
      return;
    AdjustedExpressionIDs[C.getExpressionID()] = UsedExpressions.size();
    const auto &E = Expressions[C.getExpressionID()];
    UsedExpressions.push_back(E);
    gatherUsed(E.LHS);
    gatherUsed(E.RHS);
  }
```

`AdjustedExpressionIDs` initializes every slot to `0` (`unused`), sets used slots to `1` in `mark()`, and then checks `if (!AdjustedExpressionIDs[ID]) return;` in `gatherUsed()` before **overwriting** `AdjustedExpressionIDs[ID] = UsedExpressions.size()`!
- Only the **very first** expression added (`UsedExpressions.size() == 0`) writes `0` into `AdjustedExpressionIDs[ID]`, accidentally preventing re-visitation!
- For **every subsequent** expression assigned new index `k >= 1`, `AdjustedExpressionIDs[ID] = k` remains **non-zero** (`!k` is `false`), so every second and third mapping region referencing that expression ID passes `!AdjustedExpressionIDs[ID]`, pushes an **orphaned duplicate** into `UsedExpressions`, and overwrites `AdjustedExpressionIDs[ID]` with the final duplicate's index!
- Downstream `llvm-cov` remains sound because region counter adjustment (`Minimizer.adjust`) looks up the latest overwritten index in `AdjustedExpressionIDs`, leaving the earlier copies unreferenced (`"Unreferenced"` in our IR decoder), at the cost of bloating `__llvm_covfun` record payloads whenever an expression is shared across regions or sub-trees (`e1`/`e2`/`e4`/`e6`/`e7` in `fallible_and_panic_paths`).

---

### 6. Span Distillation, Hole Pruning, and Disjoint Partition Refinements (`spans.rs`)

`Basis: source + execution + derived`

`spans::extract_refined_covspans` (`spans.rs:13-125`) converts raw `ExpnTree` span lists into the final emitted `MappingKind::Code` regions through eight sequential passes:

1. **`async fn` short-circuit (`spans.rs:20-29`)**: If `hir_info.is_async_fn`, ignores the desugared future-wrapper body completely and emits only `fn_sig_span -> START_BCB` (the coroutine closure body has its own `DefId` and `InstrumentCoverage` run).
2. **Child macro/desugaring distillation (`single_covspan_for_child_context`, `spans.rs:128-155`)**:
   - For `ExpnKind::Macro(MacroKind::Bang, _)` and `ExpnKind::Desugaring(DesugaringKind::Await)`: selects `minmax_bcbs.min` (earliest BCB in dominator order, i.e., entry into the expansion).
   - For all other child expansions: selects `minmax_bcbs.max` (most-dominated BCB).
   - If the child expansion is a `Bang` macro (`assert!`, `check_step!`, `panic!`), truncates `node.call_site` through the first `'!'` via `source_map().span_through_char(span, '!')` so only the macro name + `!` receives the entry count while inner macro arguments (`if $val > ...`) keep per-branch spans when mapped back to the call site.
3. **Body boundary & hygiene filter (`spans.rs:48-70`)**: Retains only spans satisfying `body_span.contains(covspan_span)`, `body_span.lo_hi() != covspan_span.lo_hi()`, and `body_span.ctxt() == covspan_span.ctxt()`. Appends `fn_sig_span -> START_BCB` (falling back to `body_span.shrink_to_lo()`).
4. **Canonical span sort & dedup (`spans.rs:79-95`)**: Sorts by `(a.lo asc, a.hi desc, dominator_rank(a.bcb) desc)` (`compare_spans`, `spans.rs:245-254`), then runs `dedup_by_key(|a| a.span.lo_hi())` so identical byte ranges retain only the **most-dominated** BCB.
5. **Hole merging and removal (`spans.rs:97-105`, `161-184`)**: Sorts `node.hole_spans` (nested items, closures, inline `const` blocks), merges overlapping/adjacent holes via `overlaps_or_adjacent`, and drops any covspan overlapping a hole in a synchronized two-pointer scan (`discard_spans_overlapping_holes`, proved in `discardSpansOverlappingHoles_sound`).
6. **Cross-BCB overlap elimination (`remove_unwanted_overlapping_spans`, `spans.rs:189-217`)**: Maintains `(pending, refined)` lists in a single linear pass over `lo`-sorted spans. When advancing to `curr`:
   - Any `prev` in `pending` with `prev.span.hi() <= curr.span.lo()` is finished and promoted to `refined`.
   - Any `prev` overlapping `curr` (`prev.span.hi() > curr.span.lo()`) is **dropped** if `prev.bcb != curr.bcb` (evicting enclosing outer BCB spans in favor of nested inner-branch BCBs), and retained in `pending` only if `prev.bcb == curr.bcb`.
   - **Verified invariant (`removeUnwanted_disjoint` & `removeUnwanted_subset`)**: Mechanized induction on `invOrdered` proves that `remove_unwanted_overlapping_spans` never modifies or fabricates spans (`subset`), and produces a list that is **strictly pairwise disjoint across distinct BCBs** (`a.bcb ≠ b.bcb -> a.span.hi ≤ b.span.lo ∨ b.span.hi ≤ a.span.lo`). Crucially, same-BCB nested spans can still remain overlapping in `pending` (for example, when an outer span `[lo0, hi0]` shares a BCB with a strictly nested subspan `[lo1, hi1]` where `lo0 <= lo1` and `hi1 <= hi0`: every element left together in `pending` shares one BCB, whereas every pair across distinct BCBs satisfies `x.hi <= y.lo`).
7. **Empty-span brace enlargement (`ensure_non_empty_span`, `spans.rs:110-116`, `256-277`)**: Drops empty spans unless the byte immediately after `hi` is ASCII `'{'` (enlarged to `[lo, hi + 1]`) or immediately before `lo` (`start > 0`) is ASCII `'}'` (enlarged to `[lo - 1, hi]`). Proved in `expandEmptyBraceSpan_nonempty` to yield `sp.lo < sp.hi` unconditionally.
8. **Adjacent same-BCB merging (`merge_if_eligible`, `spans.rs:119`, `231-241`)**: Runs `dedup_by` to fuse consecutive same-BCB spans satisfying `overlaps_or_adjacent`. Mechanized lemma `mergeAdjacentSameBcb_preserves_cross_bcb_disjoint_aux` reveals the exact ordering dependency between steps (7) and (8): if an intervening distinct-BCB span `c` were empty (`c.lo == c.hi` sitting right at the boundary between adjacent `a` and `b` of the same BCB), merging `a.to(b)` would swallow empty `c`; enlarging/filtering empty spans via `ensure_non_empty_span` (`hcNonEmpty : c.lo < c.hi`) **before** `merge_if_eligible` prevents `mergeAdjacentSameBcb` from ever overlapping another BCB!

**Empirical span-refinement observations (`execution`, `macro_and_match_spans` & `fallible_and_panic_paths`)**:
- In `macro_and_match_spans`, `let adjusted = check_step!(v, 5);` (line 108) expands a bang-macro containing `if $val > $limit { $val - $limit } else { $val + 1 }`. `spans.rs` truncates the macro invocation site to `[108:20..108:31]` (`check_step!`) paired with entry counter `c0 = 3` (`minmax_bcbs.min`), while the macro-expanded usage of `$val` inside one arm maps back to `[108:32..108:33]` (`v` argument, evaluated with `e0 = c0 - c5 = 2`), visibly demonstrating sub-line region splitting inside a single bang-macro call.
- Similarly, in the guarded `match` arm `x if x < 0 => -x` (line 110), `spans.rs` assigns `[110:14..110:15]` (the guard's condition `x`) to entry/guard BCB `c0 = 3` and `[110:9..110:10]`, `[110:18..110:25]` (the arm pattern binding & body) to `c1 = 1`, cleanly separating guard evaluation count from arm entry count.
- In `fallible_and_panic_paths` line 48 (`assert!(x < 10_000, ...)`), the bang-macro rule truncates the span at `'!'` with entry BCB `c0 = 2`, preventing the macro body's internal panic branch from overwriting the call-site span count.

---

## Boundaries

To preserve precise applicability and avoid overclaiming beyond directly checked evidence, negative space is classified explicitly:

1. **MC/DC branch/decision coverage (`CoverageKind::Branch` / `MCDCDecisionRegion` / `MCDCBranchRegion`)**: **Not examined** empirically in `probe_coverage_kirchhoff_node_flow_and_spans.py` (which tests default statement/region `-Cinstrument-coverage` without `-Zcoverage-options=branch` or `-Zcoverage-options=mcdc`). The covfun decoder explicitly handles `Branch` region tag `rkind == 4`, and `query.rs` (`bcb_needs_counter`) marks both `true_bcb` and `false_bcb` of `MappingKind::Branch`, while MC/DC bitmap counters bypass `BalancedFlowGraph` entirely (`query.rs`, `CoverageMappingWriter.cpp:365-380`).
2. **Windows PE/COFF `.lcovfun` / `.lcovmap` emission**: **Not examined** (empirically run on `x86_64-unknown-linux-gnu` ELF sections `__llvm_covfun` / `__llvm_covmap`). Section-name difference is documented in `covfun.rs:5-6`.
3. **Inlining-induced profile counter sharing across callers**: **Unknown** quantitatively beyond noting two static source facts: (a) `query.rs:155-169` (`all_coverage_in_mir_body` + `is_inlined`) explicitly excludes inlined `VirtualCounter` statements (`inlined.is_some() || inlined_parent_scope.is_some()`) so inlining a callee's `VirtualCounter` during MIR inlining does **not** pollute the caller's `bcbs_seen`, and (b) our `probe_results.json` binary functions were marked `#[inline(never)]` specifically to isolate per-function `@__covrec_*` behavior without cross-function LLVM IR inlining.
4. **Cross-CGU unused-function covrec records and `is_used = false`**: **Known not to apply** to our single-crate probe functions (all focus functions had `is_used = true`), though source inspection shows `query.rs:41-47` (`5debe6a12`) excludes `Constness::Const { always: true }` precisely to prevent ICEs on unused comptime function records, and `covfun.rs:64, 211-215` zeros `source_hash` and omits the `'u'` symbol suffix when `is_used == false`.
5. **Gap between AST-agnostic Lean model and live `rustc` Rust data structures**: **Known not to apply** as a full compiler soundness proof. `MirCoverageKirchhoffNodeFlowAndSpansSoundness.lean` proves (1) general Kirchhoff conservation over `BalancedFlowGraph` and finite trace batches, (2) exact unwind deficit, (3) general supernode `BalancedNodeFlow` cut conservation (`supernode_cut_conservation`) and fundamental-cut reconstruction (`spantree_cut_reconstruction_exact`), (4) exact `transcribeTerms` integer preservation and dead-BCB omission soundness, (5) `remove_unwanted_overlapping_spans` cross-BCB disjointness and brace-enlargement / hole-filtering invariants, and (6) concrete `decide` witnesses matching live probe outputs and Knuth–Stevenson (1973). It does **not** prove by general symbolic induction that the imperative `yankToRoot` + `spantreeVisitNode` loop in `node_flow.rs` produces a valid `SpanTreeCutDecomposition` for arbitrary input graphs (though the exact executable `SpantreeBuilder` model *is* formalized in Lean and verified on the Knuth–Stevenson 5-node graph via `decide`), nor does it model `hir_info` span extraction or `llvm::instrprof` cross-thread race conditions.
6. **Anneal execution under `-Cinstrument-coverage`**: **Unsupported** in `joshlf/anneal@c131b320e` (`Trusted/MirAst.lean:642-662`, `Trusted/MirSemantics.lean:1427`): `StatementKind::Coverage` compiles to `.unsupported` and deterministically triggers `.fault .unsupported`.

---

## Evidence

### 1. Upstream & Ecosystem Primary Source Anchors

| Commit / Revision | File & Lines / Symbol | Verified Content |
| :--- | :--- | :--- |
| `rust-lang/rust` `5debe6a1244452beced762385f88a51857a915fc` | `compiler/rustc_mir_transform/src/lib.rs` (`mir_promoted`) | `InstrumentCoverage` runs in `mir_promoted` producing `Analysis(Initial)` before borrowck |
| `rust-lang/rust` `5debe6a1244452beced762385f88a51857a915fc` | `compiler/rustc_mir_transform/src/cleanup_post_borrowck.rs:25-70` | Converts `StatementKind::Coverage(kind)` with `kind.is_removed_after_analysis()` to `Nop`, leaving `VirtualCounter { bcb }` into `Runtime(PostCleanup)` |
| `rust-lang/rust` `5debe6a1244452beced762385f88a51857a915fc` | `compiler/rustc_mir_transform/src/coverage/mod.rs:27-105` | `PassPolicy::optional(ctx.instrument_coverage())`; injects `VirtualCounter { bcb }` at index 0 of each BCB `leader_bb` |
| `rust-lang/rust` `5debe6a1244452beced762385f88a51857a915fc` | `compiler/rustc_mir_transform/src/coverage/graph.rs:120-182, 338-406` | `compute_basic_coverage_blocks`, `CoverageSuccessors`, `bcb_filtered_successors` stripping `unwind` and `FalseEdge`/`FalseUnwind` |
| `rust-lang/rust` `5debe6a1244452beced762385f88a51857a915fc` | `compiler/rustc_mir_transform/src/coverage/counters/balanced_flow.rs:58-127` | Synthetic `sink`, `DepthFirstSearch::new(ReversedGraph::new(&graph))` + `union_not`, back-edge `sink -> start_node` |
| `rust-lang/rust` `5debe6a1244452beced762385f88a51857a915fc` | `compiler/rustc_mir_transform/src/coverage/counters/node_flow.rs:27-68, 112-275` | `UnionFind` supernode merging, `SpantreeBuilder::{yank_to_spantree_root, visit_node, finish}` |
| `rust-lang/rust` `5debe6a1244452beced762385f88a51857a915fc` & `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_mir_transform/src/coverage/counters.rs:43-74, 78-175` | `make_node_flow_priority_list` (line 66 missing `.reverse()`), `transcribe_counters`, `CoverageCounters` |
| `rust-lang/rust` `5debe6a1244452beced762385f88a51857a915fc` & `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_mir_transform/src/coverage/query.rs` (`is_eligible_for_coverage`, `coverage_codegen_info` / `coverage_ids_info`) | Delayed physical counter allocation on `optimized_mir`, `priority_list[1..].sort_by_key(\|&bcb\| !bcbs_seen.contains(bcb))`, `is_inlined` filter; comptime `Constness::Const { always: true }` check added by `5debe6a12` |
| `rust-lang/rust` `5debe6a1244452beced762385f88a51857a915fc` | `compiler/rustc_mir_transform/src/coverage/spans.rs:13-277` | `extract_refined_covspans`, `single_covspan_for_child_context`, `discard_spans_overlapping_holes`, `remove_unwanted_overlapping_spans`, `ensure_non_empty_span`, `merge_if_eligible` |
| `rust-lang/rust` `5debe6a1244452beced762385f88a51857a915fc` | `compiler/rustc_codegen_llvm/src/coverageinfo/mapgen/covfun.rs:54-105, 195-230` | `prepare_covfun_record`, `prepare_expressions`, `emit_covfun_record` (`__covrec_<hash>[u]`) |
| `llvm/llvm-project` `dd54bc3427332702425782da54fe306cecd3cdb5` | `llvm/lib/ProfileData/Coverage/CoverageMapping.cpp:194-248, 781-790` | Signed `int64_t` `CounterMappingContext::evaluate`, unsigned `uint64_t` storage in `CounterValues` |
| `llvm/llvm-project` `dd54bc3427332702425782da54fe306cecd3cdb5` | `llvm/lib/ProfileData/Coverage/CoverageMappingWriter.cpp:74-105` | `CounterExpressionsMinimizer` `0`-vs-`1` sentinel collision emitting orphaned duplicates |
| `llvm/llvm-project` `dd54bc3427332702425782da54fe306cecd3cdb5` | `llvm/tools/llvm-cov/CoverageExporterJson.cpp:80-86` | `clamp_uint64_to_int64` capping wrapped counts to `9223372036854775807` (`INT64_MAX`) |
| `joshlf/anneal` `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/Trusted/MirAst.lean:642-662`, `Trusted/MirSemantics.lean:1427` | `StatementKind::Coverage` mapped to `.unsupported`, failing with `.fault .unsupported` |

### 2. Live `rustc` / `llvm-profdata` / `llvm-cov` Empirical Probe Artifacts

- **Script**: `support/probe_coverage_kirchhoff_node_flow_and_spans.py`
- **Captured Output**: `support/probe_results.json` (`369,355` bytes, sanitized of local/toolchain paths, recorded `2026-11-23`)
- **Toolchain**: `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`), `LLVM version 22.1.6` (`llvm-profdata`, `llvm-cov`), host `x86_64-unknown-linux-gnu`.
- **Profiles Executed**:
  1. `mir_opt_0`: `rustc --edition 2024 -Cinstrument-coverage -Zmir-opt-level=0 -Copt-level=0 --crate-name cov_probe`
  2. `opt_level_2`: `rustc --edition 2024 -Cinstrument-coverage -Copt-level=2 --crate-name cov_probe`
- **Observed stdout on both profiles**: `COV=29,15,99,88,77,52,17,5,6,29`.
- **Key Raw Counter Vectors & Decoded Export Verification (`independent_covfun_eval_check`, `0` mismatches across all 11 items in both profiles)**:
  - `diamond_and_nested_loop`: raw `[2, 1, 9, 7, 18, 3]`, `21` regions, `max_raw_u64 = 18`, `9` encoded expressions (`2` orphaned unreferenced duplicates `e1, e7`).
  - `fallible_and_panic_paths`: raw `[2, 2, 1, 0, 1]`, `19` regions, `10` encoded expressions (`5` orphaned unreferenced duplicates `e1, e2, e4, e6, e7`).
  - `unwind_mid_bcb`: raw `[1]`, `10` regions, `0` expressions; `post_call_marker` entry count `0` while lines `72..75` report `1`.
  - `unwind_underflow_loop`: raw `[1, 1, 0]`, `12` regions, `2` expressions (`e0 = c0 - c1`, `e1 = c2 - c0`); `e1 = -1` -> `raw_u64 = 18446744073709551615` (`18.4E` in `llvm-cov show`), clamped to `9223372036854775807` in `llvm-cov export`.
  - `unwind_loop_deficit`: raw `[1, 4, 4, 2]`, `16` regions, `9` encoded expressions (`3` orphaned duplicates `e2, e3, e7`), return expression `e8 = c1 - c2 = 0` masking 1 unwinding panic.
  - `macro_and_match_spans`: raw `[3, 1, 2, 1, 0, 1]`, `18` regions, `4` expressions (`e0..e3`), reproducing bang-macro span splitting at line 108 (`check_step!` = `3`, argument `v` = `2`) and match-guard splitting at line 110 (`x` pattern = `1`, `x` guard = `3`).
  - `opt_pruned_branch`: `mir_opt_0` raw `[1, 0]`, `2` physical counters (`e0 = c0 - c1`); `opt_level_2` raw `[1]`, `1` physical counter (`0` expressions, dead branch regions mapped directly to `Zero`).
  - `inescapable_branch`: raw `[1, 0, 0, 0, 0, 0, 0]`, `12` regions, `1` expression (`e0 = c0 - c1` on `Return`).
  - `coroutine_yield_once` + `{closure#0}`: outer raw `[1, 0, 1, 0]` (`20` regions, `7` expressions with `e1, e3, e4` unreferenced); closure raw `[1, 0, 0]` (`6` regions, `0` expressions).
  - `ctfe_and_runtime`: raw `[1, 0]`, `5` regions, `1` expression (`e0 = c0 - c1`); `CTFE_VAL = ctfe_and_runtime(25)` excluded from instrumentation (constant item evaluated at compile time, no runtime counter).
- **Knuth–Stevenson (1973) Python Reference Cross-Check (`run_knuth_stevenson_reference_check`)**: Exact reconstruction of node flows `[7, 5, 4, 12, 6]` from expressions `[0]: +c0`, `[1]: +c0 +c2 -c4`, `[2]: +c2`, `[3]: +c3`, `[4]: +c4` (`exact_match: true`).

### 3. Kernel-Checked Lean `v4.34.1` Formalization

- **Module**: `support/MirCoverageKirchhoffNodeFlowAndSpansSoundness.lean` (`1,704` lines, pure Lean `v4.34.1` `Init` only—zero external imports).
- **Verification Command & Kernel Purity Checks**:
  - `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true support/MirCoverageKirchhoffNodeFlowAndSpansSoundness.lean`: **exited `0`** with zero warnings and zero errors.
  - Constant & tactic audit: `0` occurrences of `sorry`, `sorryAx`, `Classical.choice`, `omega`, `bv_decide`, `native_decide`, `Lean.ofReduceBool`, `partial`, `deriving`; environment constant inspection confirmed **`UNSAFE_REC_COUNT = 0`** and **`IS_UNSAFE_COUNT = 0`** (all recursion encoded via primitive `Nat.rec` or `List.foldr` / `List.foldl`, with `evalCovTerm` defined noncomputably via `CovTerm.rec` and kernel-reduced under `decide`).
- **Complete 22-Theorem `#print axioms` Ledger**:

| Theorem | Category | Kernel Axioms |
| :--- | :--- | :--- |
| `bcb_strips_assert_unwind` | BCB unwind stripping | `[]` |
| `kirchhoff_conservation_on_normal_trace` | Single terminating trace Kirchhoff conservation | `[propext, Quot.sound]` |
| `kirchhoff_conservation_aggregate` | Finite batch terminating trace conservation | `[propext, Quot.sound]` |
| `unwind_trace_deficit_exact` | Unwinding deficit characterization (`+1`/`-1`/`0`) | `[propext, Quot.sound]` |
| `intra_bcb_post_call_phantom_count` | Post-call intra-BCB error identity | `[propext]` |
| `supernode_in_out_balanced` | Supernode contraction balance | `[propext, Quot.sound]` |
| `supernode_cut_conservation` | Fundamental supernode cut conservation | `[propext, Quot.sound]` |
| `spantree_cut_reconstruction_exact` | Knuth–Stevenson spanning-tree reconstruction exactness | `[propext, Quot.sound]` |
| `transcribeTerms_preserves_int_eval` | `pos - neg` transcription correctness | `[propext, Quot.sound]` |
| `dead_bcb_filtering_sound` | Safe pruning of zero-count omitted BCBs | `[propext, Quot.sound]` |
| `dead_bcb_wrong_omission_counterexample` | Counterexample for pruning non-zero BCB | `[propext]` |
| `llvm_eval_nonneg_exact` | Non-negative `< 2^63` preservation through export | `[propext]` |
| `llvm_eval_minus_one_wraparound` | `-1 -> 18446744073709551615 -> 9223372036854775807` | `[]` |
| `removeUnwanted_subset` | `remove_unwanted_overlapping_spans` provenance | `[propext]` |
| `removeUnwanted_disjoint` | Strict cross-BCB disjointness invariant | `[propext, Quot.sound]` |
| `discardSpansOverlappingHoles_sound` | Hole-exclusion invariant | `[propext, Quot.sound]` |
| `mergeAdjacentSameBcb_preserves_cross_bcb_disjoint_aux` | Non-empty neighbor guard for `merge_if_eligible` | `[propext]` |
| `expandEmptyBraceSpan_nonempty` | Brace widening strict non-emptiness | `[propext]` |
| `bang_macro_uses_min_dominator_bcb` | Bang/await `minmax_bcbs.min` rule | `[]` |
| `knuth_stevenson_1973_exact` | Executable `spantreeRunPriorityList` kernel check on 5-node witness | `[]` |
| `knuth_stevenson_node1_transcribed_exact` | `transcribeTerms` evaluation on node 1 (`+c0 +c2 -c4 = 5`) | `[propext]` |
| `unwind_underflow_loop_live_witness` | Live `unwind_underflow_loop` wrap/clamp arithmetic witness | `[]` |

---

## Revalidation

1. **Re-run the live compiler, IR decoder, and `llvm-cov` probe** against any installed `rustc` + `llvm-profdata` + `llvm-cov` toolchain (requires nightly `#![feature(coroutines, coroutine_trait, coverage_attribute, stmt_expr_attributes)]`):
   ```bash
   python3 reports/rustc-mir-coverage-kirchhoff-balanced-node-flow-and-span-refinement/support/probe_coverage_kirchhoff_node_flow_and_spans.py \
     --out /tmp/probe_reval.json
   ```
   Confirm:
   - `independent_covfun_eval_check` reports `"mismatches": []` for all focus functions in both profiles;
   - `opt_pruned_branch` still compresses `profc_lengths` (`2 -> 1`) under `-Copt-level=2`;
   - check whether `unwind_loop_deficit` (`acc` return) and `inescapable_branch` still assign compound subtraction expressions rather than physical counters to `Return` BCBs (detecting if `counters.rs:66` `.reverse()` has been patched upstream);
   - check `unref` expression IDs in `fallible_and_panic_paths` / `coroutine_yield_once` to detect if LLVM `CounterExpressionsMinimizer` (`CoverageMappingWriter.cpp:95-99`) has fixed its `0`-vs-`1` sentinel collision.

2. **Re-check the Lean `v4.34.1` kernel proof** with all assertions enabled:
   ```bash
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     reports/rustc-mir-coverage-kirchhoff-balanced-node-flow-and-span-refinement/support/MirCoverageKirchhoffNodeFlowAndSpansSoundness.lean
   ```
   Verify exit code `0`, `0` occurrences of `sorryAx`/`Classical.choice`/`Lean.ofReduceBool` across all `#print axioms` lines, and `0` `_unsafe_rec` constants in the environment.

3. **Targeted upstream diff audit for newer `rust-lang/rust` / `llvm/llvm-project` / `joshlf/anneal` revisions**:
   - In `rust-lang/rust`, diff `compiler/rustc_mir_transform/src/coverage/{graph.rs,counters.rs,counters/balanced_flow.rs,counters/node_flow.rs,query.rs,spans.rs}` against `5debe6a1244452beced762385f88a51857a915fc`—specifically line 66 of `counters.rs` (`is_out_summable` sort comparator) and `query.rs` (`coverage_codegen_info`).
   - In `llvm/llvm-project`, inspect `CounterExpressionsMinimizer::gatherUsed` in `llvm/lib/ProfileData/Coverage/CoverageMappingWriter.cpp` and `clamp_uint64_to_int64` in `llvm/tools/llvm-cov/CoverageExporterJson.cpp` against `dd54bc3427332702425782da54fe306cecd3cdb5`.
   - In `joshlf/anneal`, inspect `StatementKind` in `trusted/lean/Trusted/MirAst.lean` and `MirSemantics.lean` to check whether `StatementKind::Coverage` remains mapped to `.unsupported` or gains ghost-erasure support.
