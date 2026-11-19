# ML Graph Compilers, Dynamic Shape Guards, and Verified SPMD Sharding

## Summary

Modern machine learning compilers bridge imperative host languages (Python) and distributed multi-accelerator Single Program, Multiple Data (SPMD) runtimes across four distinct semantic boundaries, each with sharply different soundness guarantees:

1. **Bytecode Capture and Joint Differentiation (`PyTorch 2`):** `TorchDynamo` intercepts CPython frame evaluation via PEP 523 (`_PyInterpreterState_SetEvalFrameFunc`) and symbolically interprets Python bytecode into FX graphs guarded by synthesized runtime checks, emitting resume-function continuations (`create_call_resume_at`) on unsupported control flow or side effects instead of failing whole-program capture. `AOTAutograd` traces forward and backward passes jointly via fake tensors before running a min-cut partitioner (`partition_fn`) to minimize saved activations.
2. **Symbolic Dynamic Shapes (`ShapeEnv` / `SymInt` vs. `StableHLO`):** PyTorch's `ShapeEnv` tracks symbolic dimensions with SymPy expressions, interval `ValueRanges`, and optional Z3 backing, separating *backed* input-derived symbols from *unbacked* data-dependent symbols (`create_unbacked_symint`, e.g., `nonzero`, `.item()`). Default heuristics—`specialize_zero_one=True` and `duck_shape=True`—dramatically simplify guards and codegen but silently specialize size-0/1 dimensions and equate coincident input lengths unless disabled or constrained via `backed_size_oblivious` / deferred runtime assertions. Downstream, `StableHLO` distinguishes *shape polymorphism* (unbounded `?` shapes fully refinable from input shapes via `createStablehloRemoveDynamismPipeline`) from *bounded dynamism* (`#stablehlo.bounds<...>`) for data-dependent shapes.
3. **SPMD Sharding and Rewrite Soundness (`GSPMD`, `Alpa`, `PartIR`, `OpenXLA Shardy`):** `XLA GSPMD` uses a fixed-point sharding propagation pass over `HloSharding` (`TileAssignment`, partial replication, subgroups, manual mode), which lacks formal conflict resolution when annotations disagree. `Alpa` decouples two-level search—an intra-operator ILP over HLO communication/memory costs (`AutoShardingOption`, `run_auto_sharding_pass`) nested inside an inter-operator dynamic programming stage-slicing pass (`cluster_layers_and_slice_mesh`). `PartIR` (ASPLOS 2025) introduces an incremental, monotonic schedule of partitioning tactics (`tile`, `propagate`) over a two-op `PartIR:Core` (`loop`, `slice`) IR with a pen-and-paper structural induction soundness proof for lowering to `PartIR:HLO` under exact arithmetic. `OpenXLA Shardy` merges `GSPMD` and `PartIR` into a unified MLIR dialect (`sdy`) featuring open/closed `DimensionShardingAttr`s, numeric user priorities, factorized `SubAxisInfoAttr` `(m)k` sub-axes, explicit `unreduced_axes` to defer `all_reduce`, and directional `sdy.propagation_barrier` ops.
4. **Collective Runtime Hazards (`NCCL`):** Compiler-level SPMD soundness proofs assume uniform collective participation and associative addition. In `NVIDIA/nccl`, stream-ordered collectives across intersecting communicators deadlock whenever rank call counts diverge (e.g., from a data-dependent graph break) or per-rank communicator submission orders form a cycle in the collective wait-for graph (prevented by uniform canonical ordering or `ncclGroupStart`/`ncclGroupEnd` batching). Furthermore, `bfloat16` (`1-8-7` IEEE-754 RNE) reductions in `src/device/reduce_kernel.h` (`__hadd` / `__float2bfloat16`) are non-associative: our executable micro-probe confirms that switching between `NCCL_ALGO_RING` and `NCCL_ALGO_TREE` changes `29.35%` of outputs at $P=4$ and `48.90%` at $P=8$ on mixed-scale Gaussian tensors, and `Ring` scatter-reduce assigns distinct cyclic rank orders to different tensor chunks—yielding up to `7` distinct bit patterns (`0.0` through `3.0`) from identical per-rank rows across `8` chunks.

## Applicability

This report synthesizes primary-source code inspection, normative/peer-reviewed specifications, and standalone execution probes across the following pinned upstream revisions and papers:

- **Capture and Symbolic Shapes:** `pytorch/pytorch` at commit `8b97977cc95f31857c67ce324523254fffde5e39` interpreted alongside Ansel et al., ASPLOS 2024 (`DOI: 10.1145/3620665.3640366`). Applies to CPython `< 3.15` (see preprocessor guard `#if !IS_PYTHON_3_15_PLUS` in `torch/csrc/dynamo/eval_frame.c`), TorchDynamo eager-to-graph capture, `ShapeEnv` symbolic shape tracing, and `AOTAutograd` joint forward/backward lowering.
- **Portable Graph IR and Dynamism:** `openxla/stablehlo` at commit `6e7d581b2710953eef9f738d8a073ff760df5944` (`docs/spec.md`, `docs/dynamism.md`). Applies to StableHLO MLIR modules exported from JAX, PyTorch/XLA, or TensorFlow targeting XLA/OpenXLA backends.
- **SPMD Sharding Compilers:**
  - `openxla/xla` at commit `c3373894110fdf32dfd45a61d075569692b1b311` (`HloSharding`, `SpmdPartitioner`, `ShardyXLA` integration) and Xu et al. (`arXiv:2105.04663v2`, GSPMD).
  - `alpa-projects/alpa` at commit `b8078a9f75cb4c90cabb4550ee48c99ef394e209` and Zheng et al., OSDI 2022 (`arXiv:2201.12023`). Applies to JAX/XLA-based two-level intra-op and pipeline-parallel training clusters.
  - Alabed et al., ASPLOS 2025 (`DOI: 10.1145/3669940.3707284`, `arXiv:2401.11202v4`, PartIR) and its open-source successor `openxla/shardy` at commit `86f54eeb42d28bf01ade85b48fb7e45062a5cddf` (`docs/sdy_dialect.md`, `docs/overview.md`).
- **Collective Communication Semantics:** `NVIDIA/nccl` at commit `ad2d192c1f279aefcaf340f67e07880b65a1116b` (`src/group.cc`, `src/enqueue/enqueue.cc`, `src/device/all_reduce.h`, `src/device/reduce_kernel.h`). Applies to CUDA GPU multi-rank collective communication over NVLink/NVLS/InfiniBand using `NCCL_ALGO_RING`, `NCCL_ALGO_TREE`, `NCCL_ALGO_NVLS`, and `ncclBfloat16` / `ncclFloat16` reductions.

Results about `bfloat16` non-associativity and collective wait-for deadlock graphs are architecture-independent mathematical properties verified by deterministic Python 3 micro-probes; they apply to any SPMD backend lowering associative mathematical reductions (`stablehlo.all_reduce`, `sdy.all_reduce`) onto IEEE-754 floating-point ring or tree kernels unless fp32 accumulation or deterministic fixed-topology reduction is enforced.

## Findings

### 1. Whole-Graph Capture: TorchDynamo PEP 523 Frame Interception, Bytecode Continuation Synthesis, and AOTAutograd Joint Lowering

Basis: source (`pytorch/pytorch@8b97977c`) + documentation (ASPLOS 2024, `DOI: 10.1145/3620665.3640366`)

Prior Python ML compilers faced an unsoundness-vs.-coverage dilemma: tracer-based capture (`torch.jit.trace`, JAX `jit`) silently bakes Python control flow into a static trace for one input value, while AST-based source compilers (`TorchScript`) reject arbitrary Python idioms and C-extension calls. `TorchDynamo` resolves this by operating at the CPython frame-evaluation boundary:

1. **PEP 523 Frame Interception (`torch/csrc/dynamo/eval_frame.c`, L269–316, L532–548):**
   - `enable_eval_frame_shim(PyThreadState* tstate)` saves `previous_eval_frame = _PyInterpreterState_GetEvalFrameFunc(tstate->interp)` and installs `dynamo_custom_eval_frame_shim` via `_PyInterpreterState_SetEvalFrameFunc`.
   - Per-thread state is stored in a `Py_tss_t` slot (`eval_frame_callback_key`, L26) encoding three execution modes in `dynamo__custom_eval_frame_shim` (L536–547):
     - `Py_None`: bypass directly to `dynamo_eval_frame_default`.
     - `Py_False`: run-only cache dispatch (reuse already-compiled code objects, never compile new frames).
     - Python callable: invoke `dynamo__custom_eval_frame` to check cached guard functions attached to the `PyCodeObject`'s `co_extra` slot; on cache miss, symbolically trace the frame and emit transformed bytecode plus a C++/Python guard function.
   - Note that `torch/csrc/dynamo/eval_frame.c` (L550–585) explicitly stubs out the shim for `#if IS_PYTHON_3_15_PLUS`, documenting CPython version coupling at the PEP 523 C ABI boundary.

2. **Bytecode Symbolic Execution and Graph-Break Continuations (`torch/_dynamo/symbolic_convert.py`, L330–355, L3869–3892):**
   - `InstructionTranslator` abstracts CPython bytecode instructions over symbolic `VariableTracker` objects (tracking tensor proxies, Python containers, globals, closures, and `SymInt`s). Every tensor operation appends a node to an FX graph; every Python-level branch or type/attribute lookup registers a guard on the triggering input source.
   - When an unsupported bytecode, data-dependent Python branch (without symbolic handling), or opaque C-extension side effect triggers `Unsupported` (unless `error_on_graph_break` / `fullgraph=True` is set), Dynamo does **not** abort compilation. Instead, it flushes the prefix FX graph, executes the unsupported instruction eagerly in Python, and synthesizes a *resume function* via `create_call_resume_at(inst, all_stack_locals_metadata)` (L3869–3891).
   - The synthesized continuation expects the CPython evaluation stack to hold serialized frame locals and operand stack entries from deepest frame `N` back to frame `1`:
     ```text
     [frame N locals, frame N-1 stack+locals, ..., frame 1 stack+locals], *(frame N stack post-unsupported)
     ```
     Calling the resume function re-enters PEP 523 interception, allowing the suffix of the function to be captured as a second compiled graph.
   - **Soundness vs. Distributed Safety Trade-Off:** Graph breaks preserve single-rank Python observational equivalence, but in distributed SPMD programs they break the *whole-graph collective visibility* required by SPMD partitioners (`GSPMD`, `Alpa`, `Shardy`) and can introduce per-rank divergence when a data-dependent graph break fires on only a subset of ranks (see Section 6).

3. **Joint Forward-Backward Tracing and Min-Cut Partitioning (`torch/_functorch/aot_autograd.py`, L492, L719–756, L1145–1260, L1931):**
   - `aot_module_simplified` lowers a Dynamo-captured FX graph ahead of backend codegen by tracing both forward and reverse-mode autograd passes simultaneously using `FakeTensor`s (carrying shapes, strides, dtypes, and devices without allocating storage) to produce a single *joint graph* plus a `ViewAndMutationMeta` descriptor capturing input mutations, view aliasing, and subclass metadata.
   - A `partition_fn` (defaulting to `default_partition`, or `min_cut_rematerialization_partition` under Inductor) solves a minimum-cut problem over the joint graph to decide which intermediate activations are saved across the forward/backward boundary vs. recomputed in backward. Because joint tracing happens *after* Dynamo guard acquisition and *before* kernel generation, any hidden in-place mutation or view-aliasing violation outside `ViewAndMutationMeta` compromises autograd soundness.

### 2. Symbolic Dynamic Shapes: SymInt, ValueRanges, 0/1 Specialization, Duck Shaping, and Unbacked Data-Dependent Symbols

Basis: source (`pytorch/pytorch@8b97977c`: `torch/fx/experimental/symbolic_shapes.py`) + documentation (ASPLOS 2024)

Recompiling a separate binary for every batch size or sequence length triggers catastrophic compile-time latency and cache thrashing. PyTorch 2 replaces concrete integer dimensions with `SymInt` nodes managed by `ShapeEnv` (`torch/fx/experimental/symbolic_shapes.py`, L4018–4150), forming a lightweight, guard-synthesizing Presburger/SymPy constraint engine:

| Mechanism | Source Symbol & Location (`symbolic_shapes.py`) | Semantics & Invariant | Soundness / Recompilation Hazard |
| :--- | :--- | :--- | :--- |
| **Backed `SymInt` (`s0, s1, ...`)** | `ShapeEnv`, `self.guards: list[ShapeGuard]` (L4145), `evaluate_expr` (L8813) | Input-derived symbolic integer carrying a concrete runtime `hint`. Evaluating a branch predicate (e.g., `s0 % 2 == 0` or `s0 > 1`) checks SymPy/`ValueRanges` (and Z3 fallback); if undecided, evaluates on the hint and records a `ShapeGuard` for the compiled code cache. | Over-specialized guards cause recompilation storms; missing guards cause silent miscompilation if a backend assumes a stride or contiguity fact not emitted by `produce_guards` (L6214). |
| **0/1 Eager Specialization** | `ShapeEnvSettings.specialize_zero_one: bool = True` (L3986, L4112) | Eagerly specializes any input dimension observed as `0` or `1` to a concrete constant (`0` or `1`), because size-0 tensors (empty) and size-1 tensors (broadcast-eligible, arbitrary stride) change operator semantics and aliasing rules. | As explicitly warned in L2086 (`"NB: Export will often unsoundly assume that a graph works for 0/1"`), a graph traced at `N=4` with `specialize_zero_one=True` implicitly guards `N >= 2`; exporting it without `backed_size_oblivious` (L1598–1599) or explicit range verification can silently fail or misbroadcast when invoked at `N=0` or `N=1`. |
| **Duck Shaping** | `ShapeEnvSettings.duck_shape` (L4115, L4130–4131, default `config.use_duck_shape`) | Assigns the **same** symbol `s0` to distinct input dimensions that happen to share the same concrete hint size during tracing, emitting an equality guard `x.size(0) == y.size(0)`. | Eliminates spurious broadcast/shape-mismatch checks on common architectures (e.g., equal batch/hidden sizes) but triggers guard failures whenever two logically independent dimensions merely coincided on the warmup batch. |
| **Unbacked `SymInt` (`u0, u1, ...`)** | `create_unbacked_symint` (L5705–5723) | Allocates a `SymT.UNBACKED_INT` symbol **without** a concrete hint value for data-dependent output sizes (e.g., `torch.nonzero`, boolean masking, `.item()`). Registers an FX placeholder and Z3 variable with default `ValueRanges`. | Because no hint exists at compile time, branching on an unbacked symbol raises a `GuardOnDataDependentSymNode` error unless the user supplies `torch._check(...)` axioms (`self.axioms`, L4146) or enables `fallback_value` / deferred runtime assertions. |
| **Deferred Runtime Asserts** | `prefer_deferred_runtime_asserts_over_guards` (L4125) | Emits in-graph runtime assertion ops rather than top-level entry guards when a shape condition must hold for any valid execution (avoiding over-constraining exported graphs on error-checking branches). | Moves failure from cache-miss recompilation (Dynamo) to runtime assertion failure inside the exported artifact (`torch.export`). |

**Key Structural Insight (Derived):** `ShapeEnv` does **not** prove general dependent-type safety ahead of time; rather, it uses *trace-time symbolic execution with lazy guard accumulation*. The compiled artifact is sound *relative to the conjunction of emitted guards* (`produce_guards_verbose`, L6221) plus all `ShapeEnv.axioms` injected by `torch._check`. Any discrepancy between `FakeTensor` propagation semantics (e.g., stride/broadcasting assumptions for `s0 >= 2`) and real kernel semantics at `s0 ∈ {0, 1}` breaks soundness unless `backed_size_oblivious=True` forces `ShapeEnv` to treat backed symbols without relying on hint-based `!= 0` / `!= 1` elimination.

### 3. Portable Graph IR and Dynamism Refinement: StableHLO Bounded/Unbounded Dynamism and Collective Semantics

Basis: normative (`openxla/stablehlo@6e7d581b`: `docs/spec.md`, `docs/dynamism.md`)

`StableHLO` serves as the versioned, backward-compatible portability contract between ML frontends (`PyTorch/XLA`, `JAX`, `TensorFlow`) and compiler backends (`OpenXLA XLA`, `IREE`, hardware vendors). Its design makes two explicit formal commitments that directly constrain dynamic shapes and distributed sharding:

1. **Two-Tier Dynamism Taxonomy (`docs/dynamism.md`, L10–95):**
   - **Unbounded Dynamism (Shape Polymorphism):** Unknown dimensions are denoted `?` (e.g., `tensor<16x?xf32>`). Under *shape polymorphism* (L42–58), StableHLO enforces two invariants: (1) every dynamic dimension traces back algebraically to function input arguments, and (2) no dimension depends on tensor *data*. Consequently, once concrete input shapes are supplied at compile/deployment time, the pass pipeline `createStablehloRemoveDynamismPipeline` (L88–95) refines the entire program into a fully static StableHLO module with zero dynamic-shape runtime overhead.
   - **Bounded Dynamism (Data-Dependent Shapes):** Represented via the `#stablehlo.bounds` tensor encoding (e.g., `tensor<?x?xf32, #stablehlo.bounds<16, ?>>`, L20–31). This allows static memory allocation and accelerator padding for data-dependent operators such as `nonzero` (L59–71), at the cost of padded compute/memory up to the declared upper bound. Upstream support is asymmetric: JAX does not trace data-dependent dynamism, while TensorFlow and PyTorch/XLA provide partial bounded-dynamism lowering.

2. **Exact Process-Group Collective Semantics (`docs/spec.md`, L728–835):**
   - StableHLO collectives (`stablehlo.all_gather`, `stablehlo.all_reduce`, `stablehlo.reduce_scatter`, `stablehlo.collective_permute`) formalize participating rank sets through three mutually exclusive addressing modes governed by `channel_id` and `use_global_device_ids`:
     - `cross_replica(replica_groups)`: `channel_id <= 0` and `use_global_device_ids = false` (data-parallel replicas only).
     - `cross_replica_and_partition(replica_groups)`: `channel_id > 0` and `use_global_device_ids = false` (combines replicas and MPMD/SPMD partitions sharing the same `channel_id`).
     - `flattened_ids(replica_groups)`: `channel_id > 0` and `use_global_device_ids = true` (each ID indexes the flattened `(replica_id, partition_id)` global device space).
   - Verifier constraints enforce structural well-formedness: `(C2)` `is_unique(replica_groups)`, `(C4)` `0 <= replica_groups < size(replica_groups)`, `(C5)` `use_global_device_ids = true => channel_id > 0`, and exact dimension scaling (e.g., `all_gather`: `dim(result, all_gather_dim) = dim(operand, all_gather_dim) * dim(process_groups, 1)`).
   - **Critical Specification Omission:** While `stablehlo.all_reduce` specifies a scalar/tensor reduction computation region (e.g., `stablehlo.add`), the StableHLO specification treats reduction over a process group as an *order-unspecified* reduction—it does **not** pin a canonical floating-point reduction tree or ring order. Thus, two spec-conforming backends (or two NCCL algorithms selected by message-size heuristics) may legally produce bit-divergent `bf16`/`fp16`/`fp32` outputs from the exact same StableHLO IR.

### 4. Automated and Compositional SPMD Sharding: XLA GSPMD, Alpa Two-Level ILP/DP, PartIR Rewrite Calculus, and OpenXLA Shardy

Basis: source (`openxla/xla@c3373894`, `alpa-projects/alpa@b8078a9f`, `openxla/shardy@86f54eeb`) + normative/papers (`arXiv:2105.04663v2`, `arXiv:2201.12023`, `DOI: 10.1145/3669940.3707284`)

Scaling models across multi-dimensional accelerator meshes (e.g., `{data: 8, fsdp: 4, tensor: 8}`) requires mapping every tensor dimension to mesh axes and inserting minimal communication collectives (`AllReduce`, `AllGather`, `ReduceScatter`, `AllToAll`, `CollectivePermute`). Four generations of compilers illuminate the trade-off between **automation**, **composability**, and **formal predictability**:

#### 4.1 XLA GSPMD (`openxla/xla`, `arXiv:2105.04663v2`)
- **Representation (`xla/hlo/ir/hlo_sharding.h`, `xla/service/spmd/spmd_partitioner.h`):** `HloSharding` encodes tensor layouts via `TileAssignment` (an integer device-ID array, compactly represented via `iota_tile_assignment` reshape+transpose dimensions), with modes for replicated, maximal (single-device), tiled, partial-tile (`PartialTile` / `ReplicateOnLastTileDim`, L143–150), subgroup shardings (encoding partial/unreduced dimensions), tuple, and `Manual`.
- **Execution Model:** Compilation time is $O(1)$ with respect to device count $N$ because a single SPMD HLO program is emitted and specialized dynamically on `hlo::PartitionId()`.
- **Propagation Weakness:** GSPMD uses a heuristic multi-pass fixed-point propagation algorithm from sparse user `Sharding` custom calls. Because `HloSharding` represents a *complete* device-ID tile assignment rather than open/closed per-axis constraints, conflicting propagation paths from two partial annotations are resolved implicitly by pass visitation order and heuristics, making incremental strategy composition (e.g., layering FSDP onto Megatron tensor parallelism) fragile and opaque to engineers.

#### 4.2 Alpa Two-Level Automated Parallelism (`alpa-projects/alpa`, OSDI 2022)
Alpa separates **intra-operator parallelism** (SPMD sharding within a high-bandwidth device submesh) from **inter-operator parallelism** (pipeline stages across lower-bandwidth cross-node links):
- **Intra-Op ILP Solver (`alpa/shard_parallel/auto_sharding.py`, L49–74, L172–197):** `run_auto_sharding_pass` takes an unoptimized JAX/XLA HLO module, a `LogicalDeviceMesh`, and `AutoShardingOption` (`allow_all_gather`, `allow_all_to_all`, `allow_replicated_parameters`, `force_zero_stage_3`, `prefer_reduce_scatter`, `allow_mixed_mesh_shape`, `memory_budget_per_device`). For each HLO op $v$, it enumerates candidate sharding strategies $S_v$ with compute+communication cost vector $c_v$ and memory vector $m_v$; for each edge $(u, v)$, it builds a resharding communication cost matrix $R_{uv}$ (exact analytical volume divided by mesh-axis bandwidth). It then solves an Integer Linear Program (ILP) minimizing total compute + communication + resharding cost subject to one-hot strategy selection and peak memory constraints, emitting `SHARDING_ANNOTATED` HLO lowered by XLA's GSPMD partitioner.
- **Inter-Op DP Stage Slicing (`alpa/pipeline_parallel/stage_construction.py`, L571–593):** `cluster_layers_and_slice_mesh` clusters operator layers into pipeline stages, slices the physical 2D `VirtualPhysicalMesh` into disjoint submeshes, profiles/queries the intra-op ILP cost of each `(layer_range, submesh_shape)` pair, and runs dynamic programming (`dp_impl`) to minimize pipeline steady-state + bubble latency $T_{\text{pipe}}$.
- **Soundness Boundary:** Alpa's ILP guarantees *optimality relative to its analytical cost model and candidate strategy set*, not semantic equivalence verification; correctness of collective insertion is delegated entirely to XLA's `SpmdPartitioner` (`xla/service/spmd/spmd_partitioner.h`, `dot_handler.cc`).

#### 4.3 PartIR Compositional Rewrite Calculus (`arXiv:2401.11202v4`, ASPLOS 2025)
PartIR decouples partitioning schedules from model code via a small, formally specified intermediate representation and monotonic tactic algebra:
- **`PartIR:Core` Dialect (Paper Sec. 5, L1219–1295):** Extends StableHLO with exactly **two** pure operations:
  1. `loop "<axis>" [#tile<d> | #sum] (%r: range<k>) { ... yield ... }` — parallel iteration over mesh axis `<axis>` of size `k`, assembling slices along dimension `d` (`#tile<d>`) or summing partial results (`#sum`).
  2. `slice <dim> %val[%r]` — extracts the `%r`-th equal contiguous chunk of `%val` along `<dim>`.
  Value tiling `tile<%x, 0, "B">` replaces `%x : tensor<256x8xf32>` with a type-preserving identity loop `%xt = loop "B" [#tile<0>] (%rB: range<4>) { yield (slice 0 %x[%rB]) : tensor<64x8xf32> } : tensor<256x8xf32>`.
- **Tile-Mapping Registry (`TMR`) and Monotonic Tactics (Sec. 5.2, L1333–1735):** Each operator declares local tiling propagation rules, e.g.:
  $$\text{TMR}(\text{matmul}) = \{(\#\text{tile}\langle 0 \rangle, \bot) \mapsto \#\text{tile}\langle 0 \rangle,\; (\bot, \#\text{tile}\langle 1 \rangle) \mapsto \#\text{tile}\langle 1 \rangle,\; (\#\text{tile}\langle 1 \rangle, \#\text{tile}\langle 0 \rangle) \mapsto \#\text{sum}\}$$
  Schedules compose tactics sequentially—e.g., `tile<%x, 0, "B">; propagate` (Batch Parallelism), `tile<%w1, 1, "M">; propagate` (Model Parallelism), `tile<%w1, 0, "B">; tile<%w2, 1, "B">; propagate` (ZeRO-3 / FSDP). Crucially, **every tactic is monotonic**: once an axis/dimension decision is committed, later tactics cannot undo it; conflict ambiguity (such as both LHS dim 0 and RHS dim 1 being tiled on the same axis) is resolved deterministically by tactic ordering in the schedule rather than implicit solver heuristics.
- **Lowering to `PartIR:HLO` and Formal Proof (Sec. 6.1, L1911–2099):** Lowering flattens `PartIR:Core` `loop`/`slice` nests into SPMD `PartIR:HLO` collectives (`all_slice`, `all_gather`, `all_reduce`). The authors provide a pen-and-paper structural induction soundness proof (Appendix C, summarized L2063–2099): abstracting `range<k>` loop variables turns `PartIR:Core` tensor evaluations into maps from device-mesh index tuples to local arrays, matching the target `PartIR:SPMD` denotational semantics. **Caveat:** the proof is *not* mechanized in a proof assistant and assumes exact mathematical addition for `#sum` (`all_reduce`), abstracting away floating-point non-associativity.

#### 4.4 OpenXLA Shardy (`openxla/shardy@86f54eeb` + `openxla/xla@c3373894`)
As documented in `PartIR` (L381) and `openxla/shardy/docs/overview.md`, Shardy merges GSPMD's production XLA backend with PartIR's explicit, predictable propagation semantics into a single MLIR dialect (`sdy`) integrated into XLA via `xla/service/spmd/shardy/shardy_xla_pass.cc`:
- **Open vs. Closed Dimensions and Priorities (`docs/sdy_dialect.md`, L1151–1175):** Each tensor dimension carries a `DimensionShardingAttr(axes, is_closed, priority)` where `is_closed=false` (open `?`) permits propagation to append further sharding axes, `is_closed=true` freezes the dimension, and `priority >= 0` (lower integer = higher priority; omitted = highest) resolves conflicting user annotations deterministically across propagation phases.
- **Factorized Sub-Axes (`SubAxisInfoAttr`, L1441–1475):** Splitting a full mesh axis into `[k_1, ..., k_n]` represents the $i$-th sub-axis as `#sdy.sub_axis_info<pre_size, size>` (`(m)k` where $m = \prod_{j < i} k_j$), with strict MLIR verifier invariants (`pre_size >= 1`, `size > 1`, both divide the full axis size, `size < full_axis_size`, and zero overlap across `dim_shardings`, `replicated_axes`, and `unreduced_axes`).
- **Explicit Deferred Reductions (`TensorShardingAttr`, L1498–1564):** `TensorShardingAttr` explicitly tracks `unreduced_axes` alongside `reduction_op` (`sum | max | min`) and ops `sdy.replicated_to_unreduced` / `sdy.sharded_to_unreduced`. When a contracting `matmul` dimension is sharded on axis `x`, its output stays unreduced along `x` and can flow through linear ops (`stablehlo.add`) before a single deferred `sdy.all_reduce` or `sdy.reduce_scatter`, eliminating redundant intermediate collectives without ad-hoc peephole passes.
- **Controlled Propagation Boundaries:** `sdy.propagation_barrier` (`FORWARD | BACKWARD | NONE`, L650–677) and `sdy.manual_computation` (L492) give users explicit isolation boundaries where compiler propagation stops and hand-written per-shard collectives take over.

### 5. Cross-System Architecture & Soundness Matrix

Basis: source + normative + derived (synthesized from Sections 1–4)

| System | IR / Representation | Dynamic Shapes | Sharding / Partitioning Mechanism | Conflict Resolution | Formal Correctness Claim | Floating-Point / Deadlock Coverage |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **PyTorch 2 (`TorchDynamo` + `AOTAutograd`)** | CPython bytecode -> FX Graph (`SymInt`) | Backed `SymInt` + `ValueRanges` + Unbacked `u_i` (guarded) | External (`DTensor` / `DeviceMesh` / backend lowering) | Guard specialization & recompilation; `create_call_resume_at` graph breaks | Observational equivalence *modulo* guards + `FakeTensor` fidelity | None built-in; data-dependent graph breaks can cause per-rank collective mismatch |
| **OpenXLA `StableHLO`** | Versioned MLIR opset (`stablehlo.*`) | Unbounded `?` (shape polymorphism) + `#stablehlo.bounds` | Explicit collectives (`replica_groups`, `channel_id`, `use_global_device_ids`) | Static MLIR verifier constraints `(C1)-(C6)` | Spec-defined op semantics + backward compatibility guarantee | Reduction order **unspecified**; deadlock freedom not verified by IR verifier |
| **XLA `GSPMD`** | HLO + `HloSharding` (`TileAssignment`) | Bounded dynamism (padded) / static shapes | Fixed-point sharding propagation + `SpmdPartitioner` | Implicit heuristic pass order | Engineering test suite (no formal proof) | Single SPMD binary prevents control-flow rank skew; `bf16` reduction order backend-defined |
| **Alpa** | JAXPR -> XLA HLO + `LogicalDeviceMesh` | Static per-compiled-stage shapes | Two-level: Intra-op ILP (`auto_sharding.py`) + Inter-op DP (`stage_construction.py`) | Cost-model optimal ILP/DP | Analytical optimality w.r.t. cost model; delegates lowering to XLA | No formal deadlock check for inter-stage pipeline sends beyond fixed 1F1B/GPipe schedules |
| **PartIR** | `PartIR:Core` (`loop`, `slice`) -> `PartIR:HLO` | Static (divisible tile shapes) | Schedule of monotonic tactics (`tile`, `propagate`) + `TMR` | Deterministic by tactic order in schedule | Pen-and-paper structural induction (`Core -> SPMD`, exact arithmetic) | Assumes exact associative `+`; does not model IEEE-754 `bf16` drift or multi-comm runtime deadlocks |
| **OpenXLA `Shardy`** | MLIR `sdy` dialect (`TensorShardingAttr`, `SubAxisInfoAttr`) | Static / StableHLO shape refinement | User-priority propagation over open/closed dims + `unreduced_axes` + `propagation_barrier` | Explicit numeric `priority` + closed dims + barriers | Strict MLIR structural/non-overlap verifier; delegates lowering to XLA/SPMD | Tracks `unreduced_axes` algebraically (assumes associativity of `sum`/`max`/`min`); lowers to backend collectives |

### 6. Collective Runtime Hazards: NCCL Multi-Communicator Rank-Ordering Deadlocks and bfloat16 Ring/Tree Non-Associativity Drift

Basis: source (`NVIDIA/nccl@ad2d192c`) + execution (standalone Python 3 micro-probes in `## Evidence`) + derived

Even when a graph compiler emits type-valid, mathematically sound SPMD collectives, two runtime hazards at the GPU collective layer (`NVIDIA/nccl`) routinely violate compiler assumptions:

#### 6.1 Multi-Communicator Rank-Ordering Deadlocks and Asymmetric Launches
- **Source Mechanics (`src/group.cc`, L28, L164–188; `src/enqueue/enqueue.cc`, L188, L319–327, L430–477):**
  - NCCL collectives execute as persistent/cooperative GPU kernels communicating over fixed-size ring/tree FIFO channels (`ProtoSimple`, `ProtoLL`, `ProtoLL128`) and host proxy threads (`proxy.cc`).
  - Within a single communicator, `ncclEnqueue` explicitly enforces uniform task batching across ranks (`enqueue.cc`, L188: *"This enforces uniform batching accross ranks in the communicator and prevents hangs"*), merging channel queues with deterministic tag-bit ordering (`id = (id >> 1 | id << 63)` to order collectives before P2P ops, L327).
  - Across **multiple intersecting communicators** (e.g., 2D mesh communicators `TP_01={0,1}`, `TP_23={2,3}`, `DP_02={0,2}`, `DP_13={1,3}`), each rank submits kernels onto CUDA streams. If collectives are launched outside a single coalesced `ncclGroupStart()`/`ncclGroupEnd()` (tracked via `thread_local int ncclGroupDepth`, `src/group.cc` L28) or on dependent CUDA streams in cyclic rank order, GPU SM occupancy or stream-order serialization blocks every rank waiting for a peer whose required collective is queued behind an unstarted barrier.
- **Formal Deadlock Criterion (Derived + Execution):** Modeling each collective instance as a synchronous barrier vertex `(comm_id, seq_idx)` with directed edges from each participating rank's program/stream order yields a Collective Wait-For Graph (CWFG). A schedule is deadlock-free *only if*:
  1. **Participation Symmetry:** For every communicator $C$, every rank $r \in C$ invokes the exact same sequence of collective operations `(op_type, byte_count, dtype, red_op)` in the same count.
  2. **Acyclicity of the CWFG:** The union of per-rank stream-order edges across all collective barrier vertices forms a DAG.
- **Executable Verification (CWFG Deadlock Probe in `## Evidence`):** Running 3-color DFS cycle detection on a 2×2 `(TP, DP)` device mesh yields:
  - *Uniform TP-then-DP*: `DEADLOCK-FREE (4 collective barriers topologically orderable)`.
  - *Cyclic comm inversion* (`Rank 0: TP_01->DP_02`, `Rank 2: DP_02->TP_23`, `Rank 3: TP_23->DP_13`, `Rank 1: DP_13->TP_01`): `DEADLOCK (circular wait cycle: ('DP_02', 0) -> ('TP_23', 0) -> ('DP_13', 0) -> ('TP_01', 0) -> ('DP_02', 0))`.
  - *Data-dependent graph-break skip* (`Rank 1` skips `TP_01` due to an unguarded local branch or TorchDynamo graph break): `DEADLOCK (asymmetric call count on TP_01: {0: 1, 1: 0})`.
  - **Engineering Mitigation:** Require whole-graph capture (`fullgraph=True`) across collective regions (or lift branch predicates via `all_reduce(MAX)` before branching), assign a global canonical partial order over mesh axes (`TP -> CP -> DP/FSDP`), and batch multi-communicator P2P/collective launches inside `ncclGroupStart`/`ncclGroupEnd`.

#### 6.2 `bfloat16` Ring vs. Tree Reduction Non-Associativity Drift and Chunk-Boundary Heterogeneity
- **Source Mechanics (`src/device/reduce_kernel.h`, L22, L268–276, L451–461; `src/device/all_reduce.h`, L15–115, L237–245, L390–620):**
  - On SM80+ CUDA architectures, NCCL specializes `FuncSum<__nv_bfloat16>` directly to hardware `__hadd(x, y)` / `__hadd2(x, y)` (L451–453), and falls back on older architectures to `__float2bfloat16(__bfloat162float(x) + __bfloat162float(y))` (L461)—both perform **per-step round-to-nearest-even to 7-bit mantissa `bfloat16`** after every binary addition! (Because `bfloat16` has the same 8-bit exponent as `float32` and a 7-bit explicit significand, its machine epsilon is $\varepsilon_{\text{bf16}} = 2^{-7} \approx 7.8125 \times 10^{-3}$, so any operand smaller than half an ULP of the running accumulator—e.g., `< 4.0` when the accumulator is `1024.0`—is completely absorbed!)
  - Meanwhile, `src/device/all_reduce.h` dispatches among radically different reduction topologies depending on message size, rank count, and hardware (`NCCL_ALGO_RING`, `NCCL_ALGO_TREE` via `runTreeUpDown`/`runTreeSplit`, `NCCL_ALGO_COLLNET_DIRECT`, `NCCL_ALGO_NVLS` / `NCCL_ALGO_NVLS_TREE` using NVSwitch multicast reduction).
  - Crucially, in **Ring AllReduce**, a tensor of $N$ elements across $P$ ranks is partitioned into $P$ chunks. During the Reduce-Scatter phase, chunk $c \in \{0, \dots, P-1\}$ begins at rank $(c+1) \bmod P$ and accumulates sequentially forward around the ring until rank $c$ holds the reduced chunk, which is then AllGathered unchanged. Therefore, **different tensor chunks undergo different cyclic addition orders across ranks**, breaking spatial translation invariance even within a single `AllReduce` call!
- **Executable Measurement (`bf16` Reduction Probe in `## Evidence`, IEEE-754 `bf16` RNE):**
  1. **Chunk-Boundary Heterogeneity Witness ($P=8$ ranks):** Supplying the identical per-rank vector `[1024.0, -1024.0, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5]` (exact `fp32` sum = `3.0`) at every element produces:

     | Reduction Topology / Ring Chunk | Accumulation Order | `bf16` Result | Hex Encoding | Error vs. Exact (`3.0`) |
     | :--- | :--- | :--- | :--- | :--- |
     | Sequential (`0..7`, e.g., `TP=1` baseline) | `0->1->2->3->4->5->6->7` | `3.0` | `0x4040` | `0.0` |
     | Balanced Tree (`ALGO_TREE`) | `((0+1)+(2+3))+((4+5)+(6+7))` | `3.0` | `0x4040` | `0.0` |
     | `ALGO_RING` chunk `0` | `1->2->3->4->5->6->7->0` | `0.0` | `0x0000` | `-3.0` (100% signal loss) |
     | `ALGO_RING` chunk `1` | `2->3->4->5->6->7->0->1` | `0.0` | `0x0000` | `-3.0` (100% signal loss) |
     | `ALGO_RING` chunk `2` | `3->4->5->6->7->0->1->2` | `0.5` | `0x3f00` | `-2.5` |
     | `ALGO_RING` chunk `3` | `4->5->6->7->0->1->2->3` | `1.0` | `0x3f80` | `-2.0` |
     | `ALGO_RING` chunk `4` | `5->6->7->0->1->2->3->4` | `1.5` | `0x3fc0` | `-1.5` |
     | `ALGO_RING` chunk `5` | `6->7->0->1->2->3->4->5` | `2.0` | `0x4000` | `-1.0` |
     | `ALGO_RING` chunk `6` | `7->0->1->2->3->4->5->6` | `2.5` | `0x4020` | `-0.5` |
     | `ALGO_RING` chunk `7` | `0->1->2->3->4->5->6->7` | `3.0` | `0x4040` | `0.0` |

     Seven distinct numeric outputs (`0.0, 0.5, 1.0, 1.5, 2.0, 2.5, 3.0`) emerge from identical per-rank rows solely because chunk index $c$ shifts where the large opposing pair `(1024.0, -1024.0)` appears in the cyclic ring sum!

  2. **Mixed-Scale Gaussian Corpus ($N=4096$ elements/rank, rank 0 scaled $\times 10$, seed `20261119`):**

     | Tensor-Parallel Degree $P$ | `Ring != Tree` Bit Divergence | Max Abs Diff `(Ring, Tree)` | `Ring != Seq` Bit Divergence | `Ring != FP32Accum` Bit Divergence |
     | :--- | :--- | :--- | :--- | :--- |
     | $P = 2$ | `0 / 4096` (`0.00%`) | `0.0` | `0 / 4096` (`0.00%`) | `0 / 4096` (`0.00%`) |
     | $P = 4$ | `1202 / 4096` (`29.35%`) | `0.25` | `1035 / 4096` (`25.27%`) | `1163 / 4096` (`28.39%`) |
     | $P = 8$ | `2003 / 4096` (`48.90%`) | `0.50` | `1928 / 4096` (`47.07%`) | `1843 / 4096` (`45.00%`) |

     (Note: signed-integer ULP distance spikes to `15553` only on near-zero sign-crossing cancellations where `Ring` and `Tree` land on opposite sides of `0.0` across subnormal/small-exponent bit patterns.)

  3. **Implication for Verified Sharding & Training Reproducibility:** Changing tensor-parallel degree ($P=1 \to 4 \to 8$), crossing NCCL's message-size threshold from `ALGO_TREE` to `ALGO_RING`, or deferring `AllReduce` across `sdy.unreduced_axes` alters reduction parenthesization and therefore silently alters forward logits and backward gradients in `bf16`. Where bit-reproducible or tight-tolerance sharding equivalence is required, compilers must either (a) upcast reduction buffers to `fp32` (`ncclFloat32`) for `AllReduce`/`ReduceScatter` (reducing rounding error by $2^{16}\times$ from 7-bit to 23-bit mantissa) or (b) pin both topology (`NCCL_ALGO=Tree` / `Ring`) and rank degree $P$ as part of the numerical contract.

### 7. Verification Boundary Invariants for ML Compiler & Distributed Runtime Interfaces

Basis: derived (synthesized from primary source invariants across Sections 1–6)

Any verification harness or FFI/compiler-pass contract bridging frontends, sharding IRs, and GPU collective runtimes must explicitly enforce five boundary invariants:

1. **Guard Completeness (`TorchDynamo` -> Backend):** Every branching or stride/contiguity decision made during `FakeTensor` tracing must map either to an entry guard emitted by `ShapeEnv.produce_guards` or to a sound `backed_size_oblivious` derivation valid for `{0, 1}` as well as `>= 2`.
2. **Whole-Graph Collective Visibility:** SPMD sharding compilers require all collective-bearing control flow to be uniform across ranks (`fullgraph=True` or lifted collective predicates). Any rank-local graph break inside a collective scope voids CWFG participation symmetry.
3. **Sharding Axis Non-Overlap & Divisibility (`Shardy` / `PartIR`):** Every `TensorShardingAttr` must satisfy pairwise disjointness of `AxisRefAttr` / `SubAxisInfoAttr` `(m)k` across `dim_shardings`, `replicated_axes`, and `unreduced_axes`, plus static divisibility (or explicit padding/halo semantics) between sharded tensor dimensions and axis sizes.
4. **Canonical Multi-Communicator Ordering:** Lowering from logical mesh axes (`sdy.all_reduce`, `stablehlo.all_reduce`) to runtime NCCL communicators must preserve a global acyclic partial order in the CWFG across all intersecting communicators and guard multi-communicator batches with `ncclGroupStart`/`ncclGroupEnd`.
5. **Explicit Numerical Tolerance Contract:** Partitioning equivalence theorems (`PartIR:Core -> PartIR:HLO`, `Shardy` `unreduced_axes` deferral) hold over exact real arithmetic ($\mathbb{R}$), *not* bit-exact IEEE-754 `bf16`/`fp16`. Downstream verification must state whether equivalence is up to bounded floating-point error (requiring `fp32` collective accumulation for ill-conditioned residual/LayerNorm reductions) or fixed-topology deterministic execution.

## Boundaries

- **PyTorch Inductor codegen & Triton kernels — not examined:** This report inspects `TorchDynamo`, `ShapeEnv`, and `AOTAutograd` capture/guard boundaries in `pytorch/pytorch@8b97977c`, not Inductor's Triton/C++ scheduling, loop tiling, or kernel fusion passes.
- **JAX `jax.export` and `shard_map` frontend internals — not examined:** While `openxla/stablehlo` and `openxla/shardy` IR contracts are verified directly from source, JAX Python tracing (`jax-ml/jax`) and `pjit`/`shard_map` lowering details were not source-audited in this report.
- **NCCL NVLS / SHARP in-switch hardware reduction rounding — not examined:** `NVIDIA/nccl@ad2d192c` `src/device/all_reduce.h` dispatches to `NCCL_ALGO_NVLS` / `NCCL_ALGO_NVLS_TREE` (NVLink SHARP multimem instructions), whose exact silicon accumulation precision and reduction tree order depend on NVSwitch/Hopper/Blackwell hardware specifications not executed in this environment.
- **PartIR Appendix C full proof derivation — unknown (unmechanized):** The published ASPLOS 2025 paper (`arXiv:2401.11202v4`) describes a pen-and-paper structural induction soundness proof for `PartIR:Core -> PartIR:SPMD` in Appendix C (summarized in Section 6.1, L2063–2099); no public mechanized proof artifact (Coq/Lean/Isabelle) or public PartIR repository was found to audit mechanically.
- **Bit-exact equivalence across sharding degrees in `bf16` — known not to apply:** Probe 1A establishes empirically and mathematically that standard `bf16` `AllReduce` does **not** preserve bit-exact equality across changes in tensor-parallel degree $P \ge 4$ or between `Ring` and `Tree` topologies.
- **Data-dependent dynamic shapes in JAX/PartIR/Alpa — unsupported:** `openxla/stablehlo@6e7d581b` (`docs/dynamism.md`, L70–71) explicitly documents that JAX does not trace data-dependent dynamism, and `PartIR`/`Alpa` assume static divisible tensor dimensions for tiling and ILP cost modeling.

## Evidence

### Git Source Inspection (Observed `2026-11-19`)
- `pytorch/pytorch` @ `8b97977cc95f31857c67ce324523254fffde5e39`:
  - `torch/csrc/dynamo/eval_frame.c` (L26, L269–316, L532–585): PEP 523 `_PyInterpreterState_SetEvalFrameFunc`, `eval_frame_callback_key`, 3-state `dynamo__custom_eval_frame_shim`, `#if !IS_PYTHON_3_15_PLUS`.
  - `torch/_dynamo/symbolic_convert.py` (L330–355, L3869–3892): `InstructionTranslator`, `error_on_graph_break`, `create_call_resume_at` stack/locals continuation layout.
  - `torch/fx/experimental/symbolic_shapes.py` (L1598–1599, L1969, L2086–2092, L3977–4146, L5705–5723, L6214–6232, L8813–8831): `ShapeEnv`, `ShapeEnvSettings` (`specialize_zero_one`, `duck_shape`, `prefer_deferred_runtime_asserts_over_guards`), `backed_size_oblivious`, `create_unbacked_symint`, `produce_guards`, `evaluate_expr`.
  - `torch/_functorch/aot_autograd.py` (L132, L492, L719–756, L1145–1260, L1931): `aot_module_simplified`, `ViewAndMutationMeta`, `partition_fn`.
- `openxla/stablehlo` @ `6e7d581b2710953eef9f738d8a073ff760df5944`:
  - `docs/dynamism.md` (L10–95): bounded `#stablehlo.bounds` vs. unbounded `?` dynamism, shape polymorphism invariants, `createStablehloRemoveDynamismPipeline`.
  - `docs/spec.md` (L728–835): `stablehlo.all_gather` / `stablehlo.all_reduce` process-group modes (`cross_replica`, `cross_replica_and_partition`, `flattened_ids`) and verifier constraints `(C1)-(C6)`.
- `openxla/shardy` @ `86f54eeb42d28bf01ade85b48fb7e45062a5cddf`:
  - `docs/overview.md` (L1–57) and `docs/sdy_dialect.md` (L225–275, L492, L650–720, L1151–1175, L1441–1564): `sdy.propagation_barrier`, `sdy.reduce_scatter`, `DimensionShardingAttr`, `SubAxisInfoAttr`, `TensorShardingAttr` (`unreduced_axes`, `reduction_op`, non-overlap constraints).
- `openxla/xla` @ `c3373894110fdf32dfd45a61d075569692b1b311`:
  - `xla/hlo/ir/hlo_sharding.h` (L143–150): `HloSharding`, `TileAssignment`, `PartialTile`.
  - `xla/service/spmd/spmd_partitioner.h` and `xla/service/spmd/shardy/shardy_xla_pass.cc` (L1–90): XLA SPMD partitioner and Shardy integration pass.
- `alpa-projects/alpa` @ `b8078a9f75cb4c90cabb4550ee48c99ef394e209`:
  - `alpa/shard_parallel/auto_sharding.py` (L49–74, L172–197): `AutoShardingOption`, `run_auto_sharding_pass`.
  - `alpa/pipeline_parallel/stage_construction.py` (L571–593): `cluster_layers_and_slice_mesh` inter-op DP stage slicing.
- `NVIDIA/nccl` @ `ad2d192c1f279aefcaf340f67e07880b65a1116b`:
  - `src/device/reduce_kernel.h` (L22, L268–276, L451–461): `IsFloatingPoint<__nv_bfloat16>`, `FuncSum` specialization using `__hadd`/`__hadd2` and `__float2bfloat16(__bfloat162float(x) + __bfloat162float(y))`.
  - `src/device/all_reduce.h` (L15–115, L237–245, L390–620): `NCCL_ALGO_RING`, `NCCL_ALGO_TREE` (`runTreeUpDown`/`runTreeSplit`), `NCCL_ALGO_NVLS`, `NCCL_ALGO_NVLS_TREE`.
  - `src/group.cc` (L28, L164–188) and `src/enqueue/enqueue.cc` (L188, L319–327, L430–477): `ncclGroupDepth`, `ncclGroupStart`/`ncclGroupEnd`, uniform cross-rank batching invariant, tag-bit collective-before-P2P ordering.

### Peer-Reviewed Papers & Preprints (Verified `2026-11-19`)
- Ansel et al., *"PyTorch 2: Faster Machine Learning Through Dynamic Python Bytecode Transformation and Graph Compilation"*, ASPLOS 2024, `DOI: 10.1145/3620665.3640366`.
- Xu et al., *"GSPMD: General and Scalable Parallelization for ML Computation Graphs"*, `arXiv:2105.04663v2` (`DOI: 10.48550/arXiv.2105.04663`).
- Zheng et al., *"Alpa: Automating Inter- and Intra-Operator Parallelism for Distributed Deep Learning"*, USENIX OSDI 2022, `arXiv:2201.12023`.
- Alabed et al., *"PartIR: Composing SPMD Partitioning Strategies for Machine Learning"*, ASPLOS 2025, Vol. 1, pp. 794–810, `DOI: 10.1145/3669940.3707284`, `arXiv:2401.11202v4` (full PDF text audited: Sec. 5 `PartIR:Core`, Sec. 5.2 `TMR`, Sec. 6.1 `PartIR:HLO` lowering & proof sketch).

### Execution Micro-Probe (Observed `2026-11-19`, Python 3 standard library on Linux)
Standalone probe script (self-contained, zero external dependencies):
```python
import random, struct

def f32_to_bf16(x: float) -> int:
    u = struct.unpack(">I", struct.pack(">f", x))[0]
    if ((u >> 23) & 0xFF) == 0xFF:
        return (((u >> 16) | 0x0040) if (u & 0x7FFFFF) else (u >> 16)) & 0xFFFF
    return ((u + 0x7FFF + ((u >> 16) & 1)) >> 16) & 0xFFFF

def bf16_to_f32(b: int) -> float:
    return struct.unpack(">f", struct.pack(">I", (b & 0xFFFF) << 16))[0]

def bf16_add(a: int, b: int) -> int:
    return f32_to_bf16(bf16_to_f32(a) + bf16_to_f32(b))

def ring_sum(vs, c):
    P = len(vs)
    order = [(c + 1 + s) % P for s in range(P)]
    acc = vs[order[0]]
    for r in order[1:]:
        acc = bf16_add(acc, vs[r])
    return acc

def tree_sum(vs):
    cur = list(vs)
    while len(cur) > 1:
        cur = [bf16_add(cur[i], cur[i+1]) if i+1 < len(cur) else cur[i] for i in range(0, len(cur), 2)]
    return cur[0]

# 1) Chunk heterogeneity on P=8
rv = [f32_to_bf16(x) for x in [1024.0, -1024.0, 0.5, 0.5, 0.5, 0.5, 0.5, 0.5]]
print("ring chunks:", [bf16_to_f32(ring_sum(rv, c)) for c in range(8)], "tree:", bf16_to_f32(tree_sum(rv)))

# 2) Gaussian corpus (N=4096, seed=20261119)
rng = random.Random(20261119)
for P in (2, 4, 8):
    rt = rs = rf = 0
    for i in range(4096):
        vs = [f32_to_bf16(rng.gauss(0.0, 1.0) * (10.0 if r == 0 else 1.0)) for r in range(P)]
        rb, tb = ring_sum(vs, i % P), tree_sum(vs)
        sb = vs[0]
        for v in vs[1:]: sb = bf16_add(sb, v)
        fb = f32_to_bf16(sum(bf16_to_f32(v) for v in vs))
        rt += (rb != tb); rs += (rb != sb); rf += (rb != fb)
    print(f"P={P}: Ring!=Tree {rt}/4096, Ring!=Seq {rs}/4096, Ring!=FP32 {rf}/4096")

# 3) Collective Wait-For Graph (CWFG) deadlock checker on 2x2 (TP, DP) mesh
def check_cwfg(comms, progs):
    for c, ms in comms.items():
        cnts = {r: progs[r].count(c) for r in ms}
        if len(set(cnts.values())) > 1:
            return f"DEADLOCK (asymmetric counts on {c}: {cnts})"
    edges, nodes = {}, set()
    for r, prog in progs.items():
        seen, prev = {c: 0 for c in comms}, None
        for c in prog:
            n = (c, seen[c]); seen[c] += 1; nodes.add(n); edges.setdefault(n, set())
            if prev is not None: edges.setdefault(prev, set()).add(n)
            prev = n
    color = {n: 0 for n in nodes}
    def has_cycle(u):
        color[u] = 1
        for v in sorted(edges.get(u, ())):
            if color[v] == 1 or (color[v] == 0 and has_cycle(v)): return True
        color[u] = 2; return False
    return "DEADLOCK (cycle)" if any(color[n] == 0 and has_cycle(n) for n in sorted(nodes)) else "DEADLOCK-FREE"

comms = {"TP_01": {0, 1}, "DP_02": {0, 2}, "DP_13": {1, 3}, "TP_23": {2, 3}}
print("safe:", check_cwfg(comms, {0:["TP_01","DP_02"], 1:["TP_01","DP_13"], 2:["TP_23","DP_02"], 3:["TP_23","DP_13"]}))
print("inverted:", check_cwfg(comms, {0:["TP_01","DP_02"], 2:["DP_02","TP_23"], 3:["TP_23","DP_13"], 1:["DP_13","TP_01"]}))
print("asym:", check_cwfg(comms, {0:["TP_01","DP_02"], 1:["DP_13"], 2:["TP_23","DP_02"], 3:["TP_23","DP_13"]}))
```
Observed output:
- `ring chunks: [0.0, 0.0, 0.5, 1.0, 1.5, 2.0, 2.5, 3.0] tree: 3.0`
- `P=2: Ring!=Tree 0/4096, Ring!=Seq 0/4096, Ring!=FP32 0/4096`
- `P=4: Ring!=Tree 1202/4096, Ring!=Seq 1035/4096, Ring!=FP32 1163/4096`
- `P=8: Ring!=Tree 2003/4096, Ring!=Seq 1928/4096, Ring!=FP32 1843/4096`
- `safe: DEADLOCK-FREE` / `inverted: DEADLOCK (cycle)` / `asym: DEADLOCK (asymmetric counts on TP_01: {0: 1, 1: 0})`

## Revalidation

1. **PyTorch `ShapeEnv` & PEP 523 Drift Check:** Diff `torch/csrc/dynamo/eval_frame.c` (around `_PyInterpreterState_SetEvalFrameFunc` and `IS_PYTHON_3_15_PLUS`) and `torch/fx/experimental/symbolic_shapes.py` (`ShapeEnvSettings` defaults `specialize_zero_one`, `duck_shape`, `backed_size_oblivious`) against commit `8b97977cc95f31857c67ce324523254fffde5e39`. If `specialize_zero_one` or `backed_size_oblivious` defaults change, re-verify export soundness on size-0 and size-1 inputs.
2. **Shardy & StableHLO Contract Check:** Diff `openxla/shardy/docs/sdy_dialect.md` (`TensorShardingAttr`, `DimensionShardingAttr`, `SubAxisInfoAttr`, `sdy.propagation_barrier`) against `86f54eeb42d28bf01ade85b48fb7e45062a5cddf`, and `openxla/stablehlo/docs/spec.md` (`all_reduce` / `all_gather` reduction semantics) against `6e7d581b2710953eef9f738d8a073ff760df5944` to check whether deterministic floating-point reduction order attributes have been added.
3. **NCCL Reduction Precision Check:** Inspect `NVIDIA/nccl` `src/device/reduce_kernel.h` (`SPECIALIZE_REDUCE(FuncSum, __nv_bfloat16, ...)`) against `ad2d192c1f279aefcaf340f67e07880b65a1116b` to check whether `bf16` reduction kernels still round to `bf16` per step or introduce fp32 intermediate accumulation, and rerun the inline Python 3 probe above to confirm numerical bounds.
4. **Deadlock Graph Static Check:** Run the CWFG 3-color DFS check (Section 6.1) on any extracted multi-communicator collective schedule whenever mesh-axis lowering order changes or `fullgraph=False` permits conditional graph breaks around collective calls.
