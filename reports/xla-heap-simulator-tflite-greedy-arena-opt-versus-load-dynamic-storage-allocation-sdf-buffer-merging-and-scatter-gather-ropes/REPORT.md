# Compile-time buffer offset planning: production planners, OPT-versus-LOAD theory, schedule-independent dataflow memory, and segmented buffer representations

## Summary

- **One problem, many encodings.** Every production planner examined here solves the same core problem: given buffers with byte sizes and a *conflict relation* ("these two may be live at the same time"), assign each buffer a base offset so that conflicting buffers occupy disjoint byte ranges, minimizing the arena's high-water mark. When the conflict relation comes from intervals on one total execution order this is classical **dynamic storage allocation (DSA)**. It is strongly NP-hard. The two standard lower bounds are **LOAD**, the maximum total size live at one instant, and, for a general conflict graph, the **maximum-weight clique (MWC)**.
- **Validity is always relative to one conflict relation, and production planners derive it from a fixed order.** XLA's heap simulator states that it "only works for completely sequential instruction sequences" and that "the result is invalid if instructions are not run in exactly this sequence". XLA, the TensorFlow Lite (TFLite) arena planner, TFLite Micro (TFLM), and IREE all build lifetime intervals over one numbering of operations. They handle concurrency by *widening* lifetimes: XLA extends a buffer's interval across an asynchronous start/done window, and IREE gives every local inside a concurrent region the same time point. XLA falls back to pairwise "may interfere" checks when no total order exists. None of the examined planners proves its layout valid. Among the examined files, only TFLM ships an overlap checker, and its header says to use that checker only in tests.
- **Placement is a greedy order × gap rule.** XLA by default runs best-fit in decreasing-size order and best-fit in decreasing-duration order, then keeps the smaller result. The TFLite CPU arena and the TFLite GPU greedy-by-size offset planner use best-fit in decreasing-size order. TFLM uses *first*-fit in decreasing-size order. IREE copies TFLite's best-fit gap rule but packs slices in start-time order. TVM Relax and the TFLite GPU "shared objects" strategies reuse whole storage objects instead of assigning offsets. PyTorch Inductor builds a tree of temporal and spatial splits.
- **Theory.** The best result found in the literature examined is OPT ≤ 3·LOAD (Gergov). Buchsbaum et al. sharpened this to OPT = LOAD + O((h_max/LOAD)^{1/7})·LOAD, gave a (2+ε)-approximation, and constructed instances with OPT ≥ LOAD + c·(h_max/LOAD)^{1/2+ε}·LOAD. Reported neural-network results sit close to LOAD. Pisarchyk–Lee's greedy-by-size offset planner reaches the lower bound on 5 of 6 networks and is 7.7% above it on the sixth. OLLA's ILP removed fragmentation entirely on every training graph it tested.
- **Measured on the upstream TFLM planner** (compiled unmodified; small synthetic instances): OPT equalled LOAD on all 6,000 interval instances. TFLM matched OPT on 73–91% of instances depending on the family and was at worst 1.52× OPT. A 4-buffer instance makes TFLM produce 12 bytes where OPT = LOAD = 9, because equal-size buffers are placed in reverse insertion order. In a fork-join toy model, a layout planned for one sequential schedule was invalid under parallel execution in 1,628 of 2,000 instances. The schedule-independent optimum cost 1.53× the single-schedule optimum on average.
- **Derived structure.** (i) The optimum always equals first-fit placement in *some* order. (ii) Laminar (nested-or-disjoint) lifetimes admit a stack layout of exactly LOAD. (iii) If the conflict graph is a cograph, recursively stacking and overlaying sub-layouts achieves MWC, which is exactly the shape of Inductor's split tree. (iv) Purely sequential lifetimes are general interval instances, so no exact polynomial planner exists for series-parallel lifetimes in general unless P = NP.
- **Segmented data.** Measured on x86-64 Linux: a `bytes::Bytes` handle is 32 B, `Chain<Bytes, Bytes>` is 64 B, `IoSlice` and `struct iovec` are 16 B, `absl::Cord` is 16 B, and Cord B-tree nodes have 6 edges. `Chain::copy_to_bytes` shares the underlying buffer when the request lies within one segment (≈0.07 µs per call). It allocates and copies when the request crosses the boundary (≈65 µs per MiB).

## Applicability

The findings describe the source trees pinned in `REPORT.json`, as fetched on 2026-11-20 (UTC). The pinned revisions are as follows:

- XLA: `openxla/xla` at `47ba51efa78975214e9f94d59fc8b3c64f096dcb`;
- TFLite: `tensorflow/tensorflow` at `05748786aaad511c586be4ddcf67e6597ec08688`;
- TFLM: `tensorflow/tflite-micro` at `38a8f0f87302817ddfa99e6a995c7b71ef7118fe`;
- IREE: `iree-org/iree` at `318812edbe0bc0d937c15609e8d789c211343668`;
- TVM: `apache/tvm` at `05ac00e2efb65778ad9c8a8f04c5f8fa7b296cd6`;
- MLIR: `llvm/llvm-project` at `b33fc9379feaefa311ce3ad406fe472602659299`;
- PyTorch Inductor: `pytorch/pytorch` at `a6ec1fa444f247690030fe73106156341c95fcc3`;
- MiniMalloc: `google/minimalloc` at `9f5cf810fec4494df473c23cffd0567989e81b69`;
- Vélus: `INRIA/velus` at `27ba860c2624ba232816591290c6c119b9ead88a`;
- `bytes` 1.12.2: `tokio-rs/bytes` at `67edc2b999d669eb4f471aff576e213dbcb58871`;
- Abseil: `abseil/abseil-cpp` at `14af6bae5308dd9f690e74ba348786e50f069c47`.

The report compares these planners side by side. It does not study how they interact. The cited papers supply the theory and the published neural-network measurements. Each paper's measurements apply to its own benchmark set and software versions, not to the pinned trees.

**What was executed.** Only these were executed:

1. the upstream TFLM `GreedyMemoryPlanner`, compiled from the pinned sources with three shim headers that supply only a status enum, an empty macro, and a `printf` logger;
2. self-written re-implementations of the best-fit gap rule (labelled **toy model** wherever they appear);
3. the `bytes` crate and Abseil Cord headers, compiled from the pinned trees to measure representation sizes and copy behaviour.

All runs used GCC 15.2.0 and `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)` on an x86-64 Linux virtual machine with 96 vCPUs (Intel Xeon @ 2.60 GHz). XLA, TFLite, IREE, TVM, MLIR, Inductor, MiniMalloc, and Vélus were read as source only, not built or run.

**Input classes.** The synthetic families are random intervals, laminar intervals, chains with skip edges, and a fork-join task model, each with 7–8 buffers of 1–100 bytes. They are small enough to compute exact optima by enumeration. They are not neural-network graphs, and ratios measured on them are not predictions for production models.

**Constraints left out.** Alignment, colocation/in-place constraints, offline-pinned offsets, multi-heap and page limits, and dynamic shapes are discussed from source but excluded from the executed probes, except that TFLM aligns nothing in this path.

## Findings

### 1. Formal problem, lower bounds, and three structural lemmas

An instance consists of buffers *i* with size *sᵢ* > 0 and a symmetric conflict relation *C*. A layout assigns offsets *oᵢ* ≥ 0. It is **valid** iff for every conflicting pair (*i*, *j*) ∈ *C*, [*oᵢ*, *oᵢ*+*sᵢ*) ∩ [*oⱼ*, *oⱼ*+*sⱼ*) = ∅. Its cost is max *oᵢ*+*sᵢ*.

- **Interval DSA.** Lifetimes are intervals on one timeline, and *C* is interval overlap. LOAD = maxₜ Σ_{i live at t} sᵢ, and OPT ≥ LOAD.
- **General conflict graph.** OPT ≥ MWC(*C*). For interval graphs MWC = LOAD, because intervals have the Helly property.
- **Shared-objects variant** (TFLite GPU objects, TVM Relax storage tokens). Each buffer maps to an object, and an object's size is the maximum over its buffers. This is the subclass of offset layouts in which buffers sharing an object share a base offset.

Lemma A, Lemma C, and the series-parallel remark below are short arguments written for this report. No source states them in this form.

**Lemma A (first-fit completeness).** For every instance, some placement order makes first-fit (lowest feasible offset) produce an optimal layout. *Proof.* Sort an optimal layout by offset and run first-fit in that order. By induction, every placed buffer *j* receives *o′ⱼ* ≤ *oⱼ*. For the next buffer *i*, every earlier-placed buffer *j* that conflicts with *i* satisfies *oⱼ* ≤ *oᵢ*, and since the two are disjoint in the optimum, *oⱼ*+*sⱼ* ≤ *oᵢ*. Hence *o′ⱼ*+*sⱼ* ≤ *oᵢ*, so *oᵢ* is feasible, and first-fit picks some offset ≤ *oᵢ*. ∎ The argument never uses interval structure, so it holds for any conflict graph. The probe computes OPT as the minimum of first-fit over all n! orders. Basis: derived.

**Lemma B (laminar lifetimes).** If every pair of intervals is either nested or disjoint, set *oᵢ* to the total size of the intervals that strictly contain *i*. This layout has cost LOAD. *Reason.* The intervals live at time *t* form a chain under containment, and the layout stacks that chain contiguously. Disjoint siblings reuse the same offsets. Stack frames are this case. Basis: derived.

**Lemma C (cograph conflicts).** Suppose the conflict graph is a cograph, so it decomposes recursively into disjoint unions (no conflicts between the parts) and joins (every pair across the parts conflicts). Overlay the sub-layouts of a union at the same base, and stack the sub-layouts of a join. The resulting cost obeys the recursion union → max, join → sum. MWC on cographs obeys the same recursion, so the layout is optimal and OPT = MWC. Basis: derived.

PyTorch Inductor's allocation tree implements this construction:

- `TemporalSplit` is documented as "Contains a list of allocations not overlapping in LiveRanges" (`torch/_inductor/codegen/memory_planning.py` lines 269–275).
- `SpatialSplit` is documented as "Contains two allocations, left and right, that do not overlap in space. Right will be allocated immediately after left in memory" (lines 357–361).

Inductor builds the tree greedily and returns `False` ("TODO … we could try harder") when a block overlaps more than one temporal child (lines 286–291). It therefore realizes only those cograph-shaped layouts that its greedy insertion happens to find. Basis: source + derived.

**Consequence for series-parallel lifetimes.** A program built only from series composition, with buffers that span several steps, yields an arbitrary interval instance. Interval DSA is strongly NP-hard. A first-fit layout over series-parallel lifetimes can therefore be proved *valid* in general, but it cannot be proved *optimal* in general unless P = NP. Exactness is available only for restricted structure, such as laminar lifetimes (Lemma B) or cograph conflicts (Lemma C). Basis: derived from the cited hardness result.

### 2. Hardness, approximation, and OPT versus LOAD

| Result | Statement | Basis |
|---|---|---|
| NP-hardness | DSA is listed as problem SR2 in Garey–Johnson's compendium, NP-complete in the strong sense via a reduction from 3-PARTITION credited to Stockmeyer, and reported to stay hard when every size is in {1, 2}. The TFLM header also calls the problem "NP-Complete" (`greedy_memory_planner.h` line 46). | documentation (secondary bibliographic summaries; the compendium itself was not examined) + source |
| First constant-ratio algorithm | Kierstead, "A polynomial time approximation algorithm for dynamic storage allocation", *Discrete Math.* 88(2–3):231–237, 1991. | documentation (metadata verified; the ratio was not re-read) |
| OPT ≤ 3·LOAD | Gergov, SODA 1999, pp. 907–908: an O(n log n) algorithm. Buchsbaum et al. cite it as "previous work showed that OPT ≤ 3·LOAD". | documentation |
| OPT versus LOAD, asymptotically | OPT = L + O((h_max/L)^{1/7})·L, where h_max is the largest buffer size. For every ε > 0 there are instances with OPT ≥ L + c·(h_max/L)^{1/2+ε}·L. Also a (2+ε)-approximation, and PTASs for "several natural special cases". | documentation (Buchsbaum et al. 2004 abstract) |
| Generalization | Kierstead–Saoub (2014) generalize DSA via online-with-representation colouring of tolerance graphs and obtain a polynomial-time approximation with a linear performance ratio. | documentation (abstract) |
| Practice | Lamprakos et al. (ISMM 2023) treat DSA as two-dimensional bin packing that optimizes makespan. They argue that makespan stays a meaningful metric for statically preallocated embedded memory even though demand paging makes it irrelevant elsewhere. | documentation (abstract only; their numeric results were not examined) |
| Exact search | MiniMalloc (ASPLOS 2023) runs a depth-first search over "canonical solutions" with spatial-inference pruning and dominance elimination, reporting "orders of magnitude" speedups over the prior state of the art. Its lifespans are half-open (`src/minimalloc.h` line 70: `Lifespan lifespan = {0, 0};  // Half-open.`). | documentation + source |

**Practical reading.** When buffers are small relative to LOAD, the theory says OPT approaches LOAD. When a few buffers dominate, as with large activations, gaps above LOAD are possible, but the known worst case is a factor of 3. Basis: derived from the rows above.

### 3. Production planners: lifetime model, placement rule, validity check, lower-bound reporting

| Planner (file) | Lifetime and conflict model | Placement | Validity check after placement | Lower bound reported |
|---|---|---|---|---|
| XLA `HeapSimulator` + `GlobalDecreasingSizeBestFitHeap` (`xla/service/heap_simulator/heap_simulator.{h,cc}`) | Intervals over a flattened total schedule. "It only works for completely sequential instruction sequences" (h:70–72). "The result is invalid if instructions are not run in exactly this sequence" (h:172–175). Asynchronous ops: the live range is extended to the async-done and its start tightened to the first fully bound instruction (`xla/hlo/utils/hlo_live_range.cc` 372–380). Colocated buffers must share an offset, and placement checks the free space against the union of their intervals (`MakeFreeChunksList`, cc:2649–2668). | The default `BEST_OF_SPATIAL_TEMPORAL` runs size-descending (key `(-size, start-end, buffer)`, cc:768) and duration-descending (cc:722–731) and keeps the smaller heap (`ChooseBestHeapAlgorithm::Finish`, cc:3252–3266). The gap rule is "smallest (size, start) free chunk that fits" (cc:2828). Other strategies: `kFastMerge`, `kFastSplit`, `kPhaseWindow`, `kPhaseWindowEnd`, custom comparators, multi-heap size limits (h:586–608, 1107–1126). | No post-placement overlap verification was found in these files. The simulator only error-checks the alloc/free call sequence (h:263–265). | `NoFragmentationStatsHeap` computes "the absolute minimum size for a given instruction sequence" (h:324–327), i.e. LOAD. `fragmentation_size = heap_size − no_frag_result.heap_size` (cc:614–617). Buffer assignment reports total fragmentation against `MinimumMemoryForModule` (`buffer_assignment.cc` 1555–1580). |
| XLA without a total order (`buffer_assignment.cc`) | If `total_order_scheduled()` is false, each pair is checked with `hlo_ordering().MayInterfere(...)` (2433–2442). | First-fit into existing allocations. | Same pairwise predicate. | n/a |
| TFLite CPU `ArenaPlanner` + `SimpleMemoryArena` (`tensorflow/lite/arena_planner.cc`, `simple_memory_arena.cc`) | `alloc_node_`/`dealloc_node_` index the execution plan, and intervals are inclusive `[first_node, last_node]`. In-place reuse requires equal sizes, the same arena, and reference count 1 for ops that modify their input, and subgraph inputs and outputs cannot be shared (arena_planner.cc 151–156). | Whole-inference tensors go first. The rest are sorted "in non-increasing order of their size", with ties broken by allocation time (442–472). The arena picks the smallest fitting gap between time-overlapping allocations, or else places the tensor after the highest one (simple_memory_arena.cc 385–422). | Checked arithmetic only (`CheckedAdd`, `CheckedAlignTo`). | none |
| TFLite GPU (`delegates/gpu/common/memory_management*.{h,cc}`) | Usage records `[first_task, last_task]`. | Shared-object strategies: `NAIVE`, `EQUALITY`, `GREEDY_IN_ORDER`, `GREEDY_BY_BREADTH`, `GREEDY_BY_SIZE`, `GREEDY_BEST`, `MINCOSTFLOW` (memory_management.h 41–74). Offsets: only `GREEDY_BY_SIZE` computes offsets directly (best-fit, size-descending, greedy_by_size_assignment.cc 68–138). Any other strategy converts an objects assignment to offsets by laying the objects out contiguously (memory_management.cc 158–171). | `"Total size is wrong."` internal error on an inconsistent running total (greedy_by_size_assignment.cc 118–122). | "positional maximums" lower bound for shared objects (internal.cc 87–104). |
| TFLM `GreedyMemoryPlanner` (`tensorflow/lite/micro/memory_planner/greedy_memory_planner.{h,cc}`) | Inclusive `[first_time_used, last_time_used]`, offline-pinned offsets placed first. | Size-descending; "The first gap between simultaneously active buffers that the current buffer fits into will be used" (h:30–46). The sort is a bubble sort, "Not time-efficient for large arrays" (cc:40–59). Online buffers are written from the tail before that stable sort (cc:175–189), so **equal-size buffers are processed in reverse insertion order**. | `DoAnyBuffersOverlap()`: "This is an O(N^2) complexity operation, so only use for testing." | none |
| IREE `LayoutSlices` (`compiler/src/iree/compiler/Dialect/Stream/Transforms/LayoutSlices.cpp`) | `stream.resource.pack` slices carry inclusive `[start, end]` lifetimes that are "only used for relative comparisons" (`StreamOps.td` 520–543). Slices are returned "ascending by lifetime interval" (td 614–616). Inside `async.concurrent` regions, locals receive the region's single time point (`ScheduleAllocation.cpp` 217–223, a comment marked "HACK"). | "Packs a set of statically-sized slices by greedy strip packing. This is the same algorithm used in tflite … It's not fantastic and can end up with a significant amount of wastage" (LayoutSlices.cpp 37–44). The best-fit gap rule runs in start-time order (55–127). Dynamic sizes alias only with identical size values (129–131). | none | none |
| TVM Relax `StaticPlanBlockMemory` (`src/relax/transform/static_plan_block_memory.cc`) | Reference-counted storage tokens within one binding block, in program order. | Shared objects, not offsets. `RequestReuse` takes the smallest free token ≥ size within `[size/16, size·16)`, else enlarges the largest smaller token (217–283, `match_range_{16}` at 332). Dynamic sizes are reused only when provably equal (231–246). | ICHECK sanity checks on reference counts | none |
| MLIR One-Shot Bufferize (`mlir/lib/Dialect/Bufferization/Transforms/OneShotAnalysis.cpp`) | Decides in-place versus copy per OpOperand through read-after-write conflict analysis. With parallel regions, a write whose definition lives in a different parallel region "must bufferize out-of-place" (863–893). | Not an offset planner: it decides *aliasing*, and offsets are assigned later, if at all. | The analysis itself is the check. | n/a |
| PyTorch Inductor (`torch/_inductor/codegen/memory_planning.py`) | Live ranges over wrapper-code lines, with buffer groups merged for in-place reuse. | Intermediates sorted by `(-size, -len(live_range))` (830–837) and inserted into a `TemporalSplit`/`SpatialSplit` tree (§1). | The tree invariant holds by construction. | none |

Basis: source, at the cited lines of the pinned revisions.

**Shared design.** Each production planner treats validity as a property of the conflict relation it computes, and it computes that relation from one order. To make a layout survive concurrency, the planner over-approximates the relation:

- XLA and IREE widen intervals over async windows and concurrent regions.
- XLA falls back to a partial-order `MayInterfere` predicate when no total order exists.
- MLIR privatizes buffers across parallel regions.

No examined planner re-validates its layout against an independently specified execution semantics. Basis: source + derived.

### 4. Published gaps to lower bounds on neural networks

Pisarchyk–Lee (2020), Table 2: offset calculation, MB of intermediate tensors, fp32.

| Network | Greedy by Size | Strip packing (Sekiyama et al.) | Lower bound (max operator breadth) | Gap of Greedy by Size |
|---|---|---|---|---|
| MobileNet v1 | 4.594 | 4.594 | 4.594 | 0% |
| MobileNet v2 | 5.742 | 6.029 | 5.742 | 0% |
| DeepLab v3 | 4.653 | 4.321 | 4.320 | 4.653/4.320 = 1.0771 (+7.7%) |
| Inception v3 | 7.914 | 7.914 | 7.914 | 0% |
| PoseNet | 6.271 | 6.271 | 6.271 | 0% |
| BlazeFace | 0.492 | 0.533 | 0.492 | 0% |

Their lower bound "is equal to the maximum among all operator breadths", i.e. LOAD for the fixed order. For shared objects (their Table 1), the best strategies reach the positional-maximum bound on three networks and are "within 16%" on the others. They also report up to 10.5× less memory than naive allocation, and that buffer reuse "can also translate to up to 10% improvement in inference speed". Basis: documentation (arXiv:2001.03288v3 text); the gap column is derived.

Other published results:

- **OLLA** (arXiv:2210.12924v2) formulates node ordering and address generation as one ILP. The authors "noticed empirically that OLLA is always able to fully eliminate memory fragmentation" and therefore split the problem into two subproblems. Reported solve times: node ordering median 1.4 ± 0.2 s, worst 5.2 s excluding EfficientNet; address generation median 5.7 ± 0.6 s. PyTorch's caching allocator showed average fragmentation of 7.9% at batch size 1 and 26.1% at batch size 32. Training used "one-third less memory on average". Basis: documentation.
- **Serenity** (Ahn et al., arXiv:2003.02369) uses dynamic-programming scheduling to reach optimal peak memory for a chosen graph: a 1.68× improvement over TFLite, 1.86× with graph rewriting, at "less than one minute overhead". This is joint scheduling *then* placement. Basis: documentation (abstract).
- **Sekiyama et al.** (arXiv:1804.10001) report up to 49.5% less memory and up to 4× faster training or inference from a strip-packing heuristic. Basis: documentation (abstract).

### 5. Measured behaviour of the upstream TFLM planner against exact optima

The probe source is `support/dsa_probe/dsa_probe.cc`, and its outputs are `support/dsa_probe/out_*.txt`. There are 2,000 instances per family, with sizes uniform in 1..100. TFLM is the real upstream code. BFD (best-fit, size-descending) and BFS (best-fit, start order, as in IREE) are **toy re-implementations** of those gap rules, not the upstream XLA, TFLite, or IREE code.

| Family (n = 8) | OPT = LOAD | TFLM = OPT | TFLM/OPT mean / max | BFD/OPT mean / max | BFS/OPT mean / max |
|---|---|---|---|---|---|
| random intervals, T = 12 | 2000/2000 | 1663 | 1.0158 / 1.4040 | 1.0155 / 1.4040 | 1.0861 / 1.6159 |
| laminar intervals | 2000/2000 | 1822 | 1.0052 / 1.2544 | 1.0049 / 1.2544 | 1.0566 / 1.6387 |
| chain with skip edges | 2000/2000 | 1467 | 1.0407 / 1.5217 | 1.0398 / 1.5217 | 1.1570 / 1.7477 |

Basis: execution (upstream TFLM) + execution (toy model for BFD and BFS).

The table supports four observations:

1. On these small instances the optimum never exceeded LOAD. Every gap came from the heuristic.
2. Size-descending order matters far more than first-fit versus best-fit: BFD and TFLM are nearly identical, while start-order BFS is clearly worse.
3. Laminar instances are optimal by Lemma B, yet the size-descending heuristics still miss the optimum on about 9% of them.
4. The upstream overlap checker reported no overlap on any instance, and an independent pairwise check agreed. Basis: execution.

**A concrete 4/3 instance.** The buffers are (size 6, [5,5]), (4, [1,2]), (3, [2,4]), and (3, [3,5]); LOAD = OPT = 9. TFLM places buffer 3 before buffer 2 because of reverse tie order, at offset 6 and then offset 9, giving 12 (`support/dsa_probe/out_tflm_one.txt`). An optimal layout is 0→0, 1→3, 2→0, 3→6. Validity is preserved; only cost suffers. Basis: execution + source (cc:175–189).

**Planning latency and footprint of TFLM.** These are random intervals with sizes up to 1 MiB, timed in one run each:

| n | plan time | arena/LOAD |
|---|---|---|
| 250 | 0.43 ms | 1.0747 |
| 1,000 | 6.59 ms | 1.0706 |
| 4,000 | 112.44 ms | 1.0550 |

Going from n = 1,000 to 4,000 raised the time 17×, consistent with the quadratic sort and gap scan. `per_buffer_size()` is 40 bytes of planner scratch per buffer on this build; the header comment says "about 36 bytes". Basis: execution + source.

### 6. Schedule independence: a fork-join toy model

The model is a self-written **toy**, not any system's semantics.

- **Task graphs.** Random series-parallel graphs of 6 tasks with 7 buffers; each buffer has a producer task *p* and a last-consumer task *c* that is *p* itself or a successor of *p*.
- **Conflict under parallel execution.** With arbitrary task durations, two buffers conflict iff neither *cᵢ* strictly precedes *pⱼ* nor *cⱼ* strictly precedes *pᵢ*. This is the standard "may-happen-in-parallel" interference.
- **Single-schedule plan.** Pick one random linear extension with atomic tasks, convert the buffers to intervals, and plan them with upstream TFLM.

| Measure (2,000 instances) | Result |
|---|---|
| TFLM single-schedule plan invalid under parallel execution | 1628/2000 |
| OPT_parallel / OPT_one-schedule | mean 1.5304, max 4.1398 |
| OPT_parallel = MWC(parallel conflict graph) | 2000/2000 |
| parallel conflict graph not a cograph (has an induced P4) | 210/2000 |

Basis: execution (toy model; TFLM is upstream code).

Schedule-specific layouts such as XLA's are therefore unsafe to reuse under any other order, in this model. A schedule-independent layout costs substantially more memory, and in this model its optimum still equals the clique bound even where Lemma C does not apply. That last observation is empirical on small instances, not a theorem. Production planners avoid the gap in two ways: they fix the order (XLA states it), or they coarsen time (IREE's concurrent regions, XLA's async windows), which turns concurrency into wider intervals on one timeline.

### 7. Synchronous and dataflow languages: memory valid for every admissible schedule

- **Synchronous dataflow (Lee–Messerschmitt 1987).** SDF fixes token rates per firing, so "nodes can be scheduled statically (at compile time)". The paper introduces "static buffering". Basis: documentation (abstract).
- **Shared buffers in SDF (Murthy–Bhattacharyya 2001).** The authors pick optimally compact looped schedules first and then minimize buffer memory "under the assumption that buffers will be shared", using lifetime analysis. The layout is tied to the chosen looped schedule, which is the same fixed-order-then-pack structure as in §3. Basis: documentation (abstract).
- **Buffer merging (Murthy–Bhattacharyya, ACM TODAES 9(2):212–237, 2004).** Overlays an actor's input and output buffers at token granularity. Only bibliographic data and secondary summaries were examined, and the DOI could not be independently resolved during this investigation (see Boundaries).
- **Clock-directed modular code generation (Biernacki et al. 2008) and Vélus (Bourke et al. 2017).** In Vélus's Obc intermediate language a class carries `c_mems : list (ident * type)` (state variables) and `c_objs : list (ident * ident)` (sub-instances), with `c_nodup : NoDup (map fst c_mems ++ map fst c_objs)` (`src/Obc/ObcSyntax.v` 249–259). Every state variable of every instance therefore has dedicated storage. Method-local temporaries (`m_vars`, 154–167) become locals of the generated code. In this design, schedule-independent persistent memory comes from *never sharing*: one slot per state variable per instance, valid under any intra-step order but larger than a shared layout. Reuse of temporaries is left to the downstream C compiler; Vélus builds on CompCert. Basis: source + documentation.

### 8. Segmented ("multi-segment") data representations

| Representation | Metadata (measured, x86-64 Linux) | Per-segment cost | When it copies |
|---|---|---|---|
| POSIX `struct iovec` / `readv`/`writev` | 16 B per entry; `IOV_MAX` = 1024 on this system | one entry | never, since the kernel gathers |
| Rust `std::io::IoSlice` | 16 B, the same size as `&[u8]` | one entry | never |
| `bytes::Bytes` | 32 B: `ptr`, `len`, `data: AtomicPtr<()>`, `vtable: &'static Vtable` (`src/bytes.rs` 101–107) | a reference-counted view | `clone` is O(1) through the vtable |
| `bytes::buf::Chain<T, U>` | `{ a: T, b: U }` (`src/buf/chain.rs` 30–33); `Chain<Bytes,Bytes>` = 64 B, three levels = 96 B | grows by one handle per level; a static nesting depth | `copy_to_bytes` returns a shared view if the range lies in one segment, and otherwise allocates a `BytesMut` and copies (181–193). `chunks_vectored` exposes both segments without copying (166–178). |
| Abseil `absl::Cord` | handle 16 B, inline up to 15 bytes (`kMaxInline`); `CordRep` 16 B; substring and external nodes 32 B; B-tree node 64 B with `kMaxCapacity = 6` edges | a tree node per edge plus leaf headers | "Prefer copying blocks of at most this size, otherwise reference count", with `kMaxBytesToCopy = 511` (`cord_internal.h` 64–68) |
| Ropes (Boehm–Atkinson–Plass 1995) | a tree of concatenation and leaf nodes | per node | the paper presents ropes as a general-purpose replacement for flat strings |

Basis:

- Sizes: execution (`support/segmented/out_seg_probe.txt`, `out_cord_sizes.txt`).
- Field layouts and copy rules: source.
- Ropes: documentation (abstract).

**Measured copy costs.** These come from three runs with 2,000 iterations each. `copy_to_bytes(512 KiB)` within the first segment took 0.063–0.085 µs per call, and the result aliased the source in 2000/2000 calls. `copy_to_bytes(1 MiB)` across the boundary took 63.8–67.3 µs per call and aliased in 0/2000 calls. Basis: execution.

**Trade-off.** A representation of a k-segment value costs either k × 16–32 B of handles with no copying, or a contiguous copy when the consumer needs one slice. Cord bounds tree depth with B-tree nodes and copies small pieces (≤ 511 B) to keep metadata proportional. `Chain` has no rebalancing: its depth is part of the static type. Basis: derived.

### 9. Cost and footprint across six levels

| Level | Evidence |
|---|---|
| L1 authoring and maintenance | Upstream source sizes, measured with `wc -l` on the pinned files: `heap_simulator.cc` 3313 + `.h` 1328 lines; `buffer_assignment.cc` 4583; `arena_planner.cc` 614 + `simple_memory_arena.cc` 491; TFLM `greedy_memory_planner.cc` 459 + `.h` 176; IREE `LayoutSlices.cpp` 289; TVM `static_plan_block_memory.cc` 1125; Inductor `memory_planning.py` 871; `OneShotAnalysis.cpp` 1707. Person-months, LLM token budgets, and repair cost: not measured. |
| L2 toolchain build | Building the TFLM planner and probe with `g++ -O2` took 1.9 s wall time (measured). Building XLA, TFLite, IREE, TVM, or LLVM: not measured. |
| L3 planning latency | TFLM: 0.43 ms, 6.59 ms, and 112 ms at n = 250, 1,000, and 4,000 (measured). OLLA: median 1.4 s ordering and 5.7 s addressing (cited). Serenity: under one minute (cited). XLA, IREE, and TVM planning time: not measured. Interactive (< 50 ms) responsiveness: only TFLM at n ≤ 1,000 meets it in the measured range. |
| L4 generated code | A static offset is a compile-time constant added to the arena base, so it adds no per-access metadata. Pisarchyk–Lee report up to 10% faster inference from reuse (cited); Sekiyama et al. report up to 4× (cited). Segmented access: 0.063–0.085 µs to share versus 63.8–67.3 µs per MiB to copy (measured). Cycles per byte, p99.9 latency, and WCET of planned code: not measured. |
| L5 validity checking | Pairwise checking is O(n²) (TFLM's "only use for testing" checker). A sweep over intervals takes O(n log n + k) for k reported overlaps (derived). No production planner emits a certificate. Checker throughput: not measured. |
| L6 memory and binary footprint | Planner scratch is 40 B per buffer for TFLM (measured). Arena/LOAD is 1.055–1.075 on large random instances (measured). Published peaks are in §4. Handle sizes are in §8 (measured). OLLA: about one third less memory; PyTorch fragmentation 7.9% and 26.1% (cited). Energy: not measured. |

### 10. Comprehensibility and conceptual simplicity

**C1: what a human must hold in mind.** The validity invariant is local and auditable: conflicting pairs must have disjoint byte ranges. The difficulties lie elsewhere.

1. **Interval conventions differ.** XLA, TFLite, TFLM, and IREE use inclusive endpoints. XLA's overlap test is `top_start <= end && top->end >= start` (heap_simulator.cc 1074). MiniMalloc is half-open. Translating between planners without converting endpoints creates or hides conflicts by one time step.
2. **The conflict relation is computed far from the planner,** in schedule flattening, async-window extension, or concurrent-region coarsening. A reviewer must audit that derivation, not the packing loop.
3. **Tie order is hidden behaviour.** It is the TFLM 12-versus-9 instance.
4. **XLA multiplies concepts:** seven packing strategies, colocations, sliced allocations, multi-heap limits, preferred offsets, fallbacks. Each choice is plausible on its own, and the combination is hard to predict without running it.
5. **Diagnostics.** XLA's `HeapSimulatorTrace` and TFLM's ASCII `PrintMemoryPlan` are the human-facing tools. Neither explains *why* a buffer landed where it did.

Basis: source + derived.

**C2: the minimal universal model.** All examined planners are instances of:

    instance  = (sizes s, conflict graph C, equality constraints E, pinned offsets P, capacity K)
    certificate = offsets o
    valid(o)  ⇔ ∀(i,j)∈C. disjoint([oᵢ,oᵢ+sᵢ), [oⱼ,oⱼ+sⱼ))  ∧  ∀(i,j)∈E. oᵢ=oⱼ  ∧  ∀i∈P. oᵢ=Pᵢ  ∧  max(oᵢ+sᵢ) ≤ K

The model covers each special case as follows:

- in-place reuse and colocation are E;
- offline-planned offsets are P;
- multi-heap and page limits are K applied per heap;
- shared objects are E-classes with size max(s);
- concurrency only changes how C is derived.

Placement heuristics, exact solvers (MiniMalloc), ILPs (OLLA), and split trees (Inductor) are all untrusted producers of `o`. Only `valid` must be trusted. Separating the derivation of C (semantics-bearing) from placement (optimization) puts the special cases in one well-defined slot each, rather than in adapters. The hard part, deriving C soundly from an execution model, is irreducible and must be audited directly. Basis: derived.

### 11. Validation of planners and proposed mechanisms

- **V1 (specification adequacy).** The risk is a conflict relation that misses a real overlap, for example an async op or an alias. None of the examined planners validates C against an independent execution model. The probe cross-checks TFLM's layouts against an independent pairwise check, with 0 disagreements over 6,000 instances. Mutation testing of planners: not examined.
- **V2 (differential testing).** The probe pits an exact enumerator against the upstream heuristic. MiniMalloc could serve as an exact oracle at larger n (not run). Fuzzing of XLA or IREE planners: not examined.
- **V3 (concurrency).** In the toy model, 81% (1628/2000) of single-schedule layouts are invalid under parallel execution. Checking real multi-stream executions, for example with GPU race detectors, was not examined.
- **V4 (field evidence).** The available field evidence is published peaks on six inference networks (Pisarchyk–Lee) and fragmentation in training (OLLA). Lamprakos et al. evaluate on real allocation traces; their results were not examined.

## Boundaries

- **Not examined.**
  - Building or running XLA, TFLite, IREE, TVM, MLIR, Inductor, MiniMalloc, or Vélus. All claims about them are source-level.
  - XLA's memory-space assignment, which was not found at its former path in this revision.
  - TVM's earlier unified static memory planner.
  - Alignment effects on gaps.
  - GPU multi-stream execution.
  - The numeric results of Lamprakos et al. and TelaMalloc (Maas et al., ASPLOS '23 proceedings, published 2022, DOI 10.1145/3567955.3567961), beyond their abstracts.
  - The full texts of Garey–Johnson, Kierstead 1991, Gergov 1999, and Boehm et al.
  - Buffer merging, beyond bibliographic data. Its DOI (listed by DBLP as 10.1145/996563.996567) could not be resolved with the tools available here and is not relied upon.
- **Unknown.**
  - Whether size-descending first-fit or best-fit has a constant worst-case ratio to OPT for offline interval DSA. No such result was found.
  - Whether OPT = MWC holds for all conflict graphs arising from fork-join programs. It held on 2,000 small toy instances, 210 of them non-cographs, but no proof exists.
  - Kierstead's 1991 constant was not re-read.
- **Known not to apply.**
  - "First-fit over series-parallel lifetimes is optimal" cannot hold in general unless P = NP, because the series-only case contains interval DSA (§1).
  - "OPT = LOAD" is false in general: Buchsbaum et al.'s lower-bound family has OPT exceeding LOAD by a term that grows with h_max. No such instance appeared among the probe's 6,000 random instances or the 1.6 million tiny instances searched by `./dsa_probe examples` (3–6 buffers, sizes 1–6, 6 time steps), which shows only that such instances are rare in these distributions.
- **Unsupported.**
  - XLA's heap simulator does not support non-sequential instruction orders; its own comment says so.
  - IREE packs dynamically sized slices only with identical size values.
  - TVM reuses dynamic-shape tokens only when it can prove the shapes equal.
- **Attractive but unestablished.**
  - That production planners are near-optimal on real models in general. The evidence covers six inference networks and selected training graphs from two papers.
  - That toy-model ratios (TFLM within 1.6% of OPT on average) transfer to production graphs.
  - That one fixed schedule's layout is safe under GPU stream concurrency.

## Evidence

**Source.** All files were read at the pinned revisions on 2026-11-20 via `raw.githubusercontent.com/<repo>/<revision>/<path>`:

- XLA:
  - `xla/service/heap_simulator/heap_simulator.h` lines 70–75, 172–175, 263–265, 324–327, 566–608, 1107–1126, 1169–1205;
  - `xla/service/heap_simulator/heap_simulator.cc` lines 614–617, 722–731, 765–769, 1057–1080, 2636–2720, 2784–2830, 3252–3266;
  - `xla/service/buffer_assignment.cc` lines 1555–1580, 2240–2262, 2433–2450, 3519–3602;
  - `xla/hlo/utils/hlo_live_range.cc` lines 205–228, 366–400.
- TFLite: `tensorflow/lite/arena_planner.cc` 150–157 and 442–472; `tensorflow/lite/simple_memory_arena.cc` 370–432; `tensorflow/lite/delegates/gpu/common/memory_management.h` 41–80; `memory_management.cc` 62–72 and 158–171; `memory_management/greedy_by_size_assignment.cc` 68–138; `memory_management/internal.cc` 87–104.
- TFLM: `tensorflow/lite/micro/memory_planner/greedy_memory_planner.h` 26–60 and 100–110; `greedy_memory_planner.cc` 40–59, 120–160, 163–330.
- IREE: `compiler/src/iree/compiler/Dialect/Stream/Transforms/LayoutSlices.cpp` 37–131; `.../Stream/IR/StreamOps.td` 510–548 and 591–616; `.../Stream/IR/StreamOps.cpp` 1981–1992; `.../Stream/Transforms/ScheduleAllocation.cpp` 155–262.
- TVM: `src/relax/transform/static_plan_block_memory.cc` 20–60, 200–300, 332.
- MLIR: `mlir/lib/Dialect/Bufferization/Transforms/OneShotAnalysis.cpp` 1–39 and 855–900.
- PyTorch: `torch/_inductor/codegen/memory_planning.py` 269–295, 357–361, 414–418, 687–705, 812–837.
- MiniMalloc: `src/minimalloc.h` 32–70; `README.md`.
- Vélus: `src/Obc/ObcSyntax.v` 154–167 and 249–259.
- `bytes`: `src/buf/chain.rs` 30–33, 166–193; `src/bytes.rs` 101–125.
- Abseil: `absl/strings/internal/cord_internal.h` 64–68, 204–223, 255–269, 305–338, 444; `absl/strings/internal/cord_rep_btree.h` 92.

**Literature.** Every DOI was checked through the doi.org handle API (response code 1) and matched for title, authors, venue, and year against OpenAlex metadata. Crossref was not reachable from the fetch tool. arXiv identifiers were checked against arXiv abstract pages.

- Buchsbaum, Karloff, Kenyon (now Mathieu), Reingold, Thorup, SIAM J. Comput. 33(3):632–646, 2004, DOI 10.1137/S0097539703423941.
- Kierstead, Discrete Math. 88(2–3):231–237, 1991, DOI 10.1016/0012-365X(91)90011-P.
- Kierstead–Saoub, DMTCS 16(3):253–262, 2014, DOI 10.46298/dmtcs.2083.
- Lamprakos, Xydis, Catthoor, Soudris, ISMM 2023, pp. 58–70, DOI 10.1145/3591195.3595279.
- Moffitt, MiniMalloc, ASPLOS 2023, pp. 238–252, DOI 10.1145/3623278.3624752.
- Maas, Beaugnon, Chauhan, Ilbeyi, TelaMalloc, ASPLOS '23 proceedings (published 2022), pp. 123–137, DOI 10.1145/3567955.3567961.
- Lee–Messerschmitt, Proc. IEEE 75(9):1235–1245, 1987, DOI 10.1109/PROC.1987.13876.
- Murthy–Bhattacharyya, IEEE TCAD 20(2):177–198, 2001, DOI 10.1109/43.908427.
- Biernacki, Colaço, Hamon, Pouzet, LCTES 2008, pp. 121–130, DOI 10.1145/1375657.1375674.
- Bourke, Brun, Dagand, Leroy, Pouzet, Rieg, PLDI 2017, pp. 586–601, DOI 10.1145/3062341.3062358.
- Boehm, Atkinson, Plass, Softw. Pract. Exp. 25(12):1315–1330, 1995, DOI 10.1002/spe.4380251203.
- Pisarchyk–Lee, arXiv:2001.03288v3 (full text read).
- Steiner, Elhoushi, Kahn, Hegarty, OLLA, arXiv:2210.12924v2 (full text read).
- Ahn et al., arXiv:2003.02369 (abstract).
- Sekiyama, Imamichi, Imai, Raymond, arXiv:1804.10001 (abstract).
- Lee et al., "On-Device Neural Net Inference with Mobile GPUs", arXiv:1907.01989 (abstract; source of the "Greedy" and "Min-cost Flow" baselines in Pisarchyk–Lee).
- Gergov, SODA 1999, pp. 907–908 (no DOI; bibliographic data only).
- Garey–Johnson 1979, problem SR2 (secondary summaries only).

**Execution.** All runs took place on 2026-11-20 on an x86-64 Linux VM with 96 vCPUs (Intel Xeon @ 2.60 GHz), using GCC 15.2.0 and rustc 1.102.0-nightly (3ef0c22cd 2026-11-11).

1. **DSA probe.** `support/dsa_probe/fetch_upstream.sh` downloads the TFLM planner files. Their SHA-256 values are 69657905f4def9504acc81f53f16463f9fc5a16ad841c1f39015ae29803d5b32 for `greedy_memory_planner.cc`, 2e16b7ad814160caa9b13769a62641ab6c369011a6f3d8ec66ccbbb21ae09fd7 for `.h`, and a726331f339ac271a3330e44a17a7a7ef0912f1b72f5b341614b59cb448e9b50 for `micro_memory_planner.h`. Build and run:

        g++ -std=c++17 -O2 -Ishim -Iupstream dsa_probe.cc upstream/tensorflow/lite/micro/memory_planner/greedy_memory_planner.cc -o dsa_probe
        ./dsa_probe stats; ./dsa_probe forkjoin; ./dsa_probe examples; ./dsa_probe timing

   The seeds are fixed (splitmix64), so `stats` and `forkjoin` are deterministic. `stats` took 59 s.

2. **TFLM single instance.** `tflm_one.cc` is built the same way and reproduces the 12-versus-9 instance.

3. **Segmented representations.** `support/segmented/seg_probe.rs` is built against `bytes` at the pinned revision:

        rustc --edition 2021 --crate-type rlib --crate-name bytes -O --cfg 'feature="std"' <bytes>/src/lib.rs -o libbytes.rlib
        rustc --edition 2021 -O seg_probe.rs --extern bytes=libbytes.rlib -L .

   `support/segmented/cord_sizes.cc` is compiled with `g++ -std=c++17 -O2 -I<abseil-cpp>` and needs no Abseil libraries at link time.

## Revalidation

- **Planner logic.** Re-diff the cited line ranges at a new revision. The decisive spots are:
  - XLA `GetSpatialBufferIntervalCompare`, the `BEST_OF_SPATIAL_TEMPORAL` default in `buffer_assignment.cc`, and the "only works for completely sequential" comment;
  - the TFLite `CreateTensorAllocationVector` comparator;
  - the TFLM tail-fill loop and `ReverseSortInPlace`;
  - the IREE `packStaticSlicesGreedily` order and the concurrent-region "HACK" in `ScheduleAllocation.cpp`;
  - Inductor's `TemporalSplit._allocate`.
- **TFLM measurements.** Run `fetch_upstream.sh` with the new revision and rerun `./dsa_probe stats` and `./tflm_one`. Identical output lines show that the planner's behaviour on these inputs has not changed. A different 12-versus-9 result shows that tie handling changed.
- **Theory claims.** Re-read the Buchsbaum et al. abstract (DOI above). The only quantitative theory relied on here is the OPT/LOAD bounds and the (2+ε) ratio.
- **Segmented sizes.** Rerun `cord_sizes` and `seg_probe` at the new revisions. Sizes depend on target pointer width, and every figure here is for 64-bit Linux.
- **Not covered.** A passing rerun says nothing about XLA, IREE, TVM, or Inductor behaviour on real models. Revalidating those requires building them and dumping their planned offsets.
