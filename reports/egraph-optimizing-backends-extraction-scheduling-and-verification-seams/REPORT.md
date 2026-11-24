# E-Graph-Based Optimizing Compiler Backends: Representations, Extraction, Lowering, and Verification Seams

## Summary

Production and research e-graph optimizing compilers split sharply between
**bounded mid-end sea-of-nodes representations** tuned for fast JIT/AOT compile
budgets and **domain-scoped equality saturation engines** tuned for phase
ordering on pure or structured regions. Across primary sources from 2023–2026,
five architectural conclusions govern optimizing backend design and formal
assurance:

1. **In Production `aegraphs`, the Sea-of-Nodes + CFG Skeleton Drives Nearly All
   Speedup:** In Cranelift (`bytecodealliance/wasmtime` @ `cef75a9fea59`),
   replacing classic GVN/LICM with `EgraphPass` yields `~2%` runtime speedup at
   `+7–8%` compile-time cost on Sightglass WebAssembly workloads, but Chris
   Fallin's April 2026 ablation measures that multi-value `Union` nodes plus DP
   extraction contribute only `~0.1%` execution speedup (at `~0.005%` compile
   time), with a mean e-class size of `1.13` e-nodes because general AC rules
   are prohibited and incoming Wasm is already pre-optimized.
2. **Whole-Function Effectful EqSat Requires Structured Region Encodings and
   Bounded State:** Per-block external-process MLIR bridges (`DialEgg`) skip or
   opaquely erase multi-result operations and pay process/file serialization,
   while in-IR pure dialects (`Tamagoyaki`) explicitly restrict scope to pure,
   straight-line code fragments. `eggcc` encodes reducible CFGs as RVSDGs
   (`If`, `Switch`, `DoWhile` + linear `StateT` edges) and eliminates Peggy's
   ILP bottleneck via `Statewalk DP` (`O(k n^2)` FPT in statewalk width `k`,
   `520x` geometric-mean speedup over Gurobi), **yet** still disables its rich
   `memory` ruleset for `WeaklyLinear` fragility, caps substitution at
   `(repeat 5 ...)`, trails `LLVM-O3-O0` overall (`0.571` vs. `0.326` on
   PolyBench, `0.876` vs. `0.695` on Bril) except on targeted rewrites
   (`6.52x` vs. `LLVM-O3-O3` on Fenwick `lowbit`), and delegates target ISel
   and register allocation to LLVM 18.
3. **No Fast, General Register-Pressure- or Schedule-Aware Extractor Exists:**
   Tree-sum DP (`Cranelift elaborate.rs`, `slotted-egraphs`) ignores DAG
   sharing (`Cost::infinity()` saturation risk on chains) and interference
   coloring, causing live scheduling and duplication regressions; `Statewalk DP`
   sums bag/tree pure `op_cost`; GPU/hybrid extractors (`SmoothE` `4.6–42.4s`,
   `e-boost` up to `3,599s`) target hardware/tensor DAGs at `10^3–10^6x` higher
   latency. A deterministic local probe (`support/probe_egraph_backend.py`)
   shows DAG sharing cuts ops `1.68x` (`47` vs. `79` at `W=8`) while naive DFS
   hits `12` live registers vs. `7` under interleaved scheduling (and `6` vs.
   `8` exact optimal at `W=4`), confirming extraction without scheduling
   misprices interference and rematerialization.
4. **General-Purpose Target ISel Remains Decoupled from Mid-End E-Graphs:**
   Cranelift isolates `aegraph` (`opts/*.isle`) from `VCode` lowering
   (`lower.isle`) via `InstColor` atomic regions and `SinkableLoad`; unifying
   them remains blocked on pass-direction conflicts (`#8529` / `#7321`). EqSat
   succeeds in target lowering primarily for specialized DSP/RTL datapaths
   (`Diospyros`, `ROVER`, `Tamagoyaki`/CIRCT), whereas `Hydride` uses Rosette/Z3
   SMT CEGIS rather than e-graphs.
5. **Verification Must Sit at Post-Extraction Translation Validation + Rule/Alloc
   Checkers:** Rule checkers (`VeriISLE`/`Arrival`, `Lean-MLIR`) prove local
   rewrite soundness while leaving saturation, `elaborate.rs`, and `Statewalk DP`
   in the TCB (and `eggcc/proofs/proofs.v` covers only 4 `Ctx` theorems on a
   toy AST lacking load/store rules). Placing soundness at post-pass
   symbolic/BTL Translation Validation plus kernel-checked rule/regalloc
   checkers decouples the entire e-graph search engine from the TCB.

## Applicability

This report synthesizes observed architecture, code invariants, benchmark
measurements, and verification boundaries across ten pinned subjects:

- **Cranelift (`bytecodealliance/wasmtime` @ `cef75a9fea591317bb076ec04d1f1a99ccfedb63`):**
  Audited `cranelift/codegen/src/egraph/{mod,elaborate,cost}.rs`,
  `cranelift/codegen/src/opts{,/README.md,remat.isle,skeleton.isle,vector.isle}`,
  `cranelift/codegen/src/machinst/lower.rs`, `isa/x64/lower.isle`,
  `cranelift/isle/veri/{README.md,verify.sh,configs/*.args,veri/src/*.rs}`,
  tracked Wasmtime issues `#6159`, `#6260`, `#8529`, `#8959`, and Fallin's
  2026-04-09 `aegraph` ablation study.
- **`eggcc` (`egraphs-good/eggcc` @ `8337bb0dd00b794b118997357fcd9fdd5aff528c`,
  OOPSLA 2026 `arXiv:2609.31887v2`):** Audited Rust RVSDG/egglog driver,
  `schedule.rs`, `mem_simple.egg`, `memory.egg`, `non_weakly_linear.egg`,
  `add_context.rs`, `tiger/{statewalkdp.cpp,greedy.cpp,ilp.cpp}`, `infra/`
  scripts (`nightly.py`, `profile.py`, `macros.py`), `proofs/proofs.v`, and
  published Bril/PolyBench/Fenwick evaluation numbers.
- **MLIR E-Graph Integrations (`DialEgg` @ `4d0d522e98c15becdc5e7d711348cb0891ff0d44`,
  `Tamagoyaki` `arXiv:2602.16707v2`):** Audited `Egglog.cpp`,
  `EqualitySaturationPass.cpp`, `bench/*.py`, and Tamagoyaki's `equivalence`
  dialect paper.
- **Structural Extensions & Non-Linear Extractors:** Audited
  `memoryleak47/slotted-egraphs` (`48cefee5503822224257e4f2e81681fef212ae89`) +
  artifact docs, `Colored E-Graphs` (`arXiv:2305.19203`), `SmoothE`
  (`cornell-zhang/smoothe` @ `8de74ef2b53aabbb35898400cb5eb890d9a07a54` +
  ASPLOS 2025 Tables 2–3), and `e-boost` (`arXiv:2508.13020v2`).
- **Verification & Negative Control (`opencompl/lean-mlir` @ `b8c4a771319a044854a4bbb49b8821381ef86ff8`,
  `akothen/Hydride` @ `0c97d0f9d3f8cd0494e421b9ece4b24488b614e5`):** Audited
  `LeanMLIR/Transforms/Rewrite/Rewrite.lean`, `ScalingTest.lean`, `README.md`,
  and Hydride's `README.md` / Racket synthesis tree.

All findings apply strictly to the pinned revisions, benchmark suites, and
configuration flags documented below; extrapolation to arbitrary unexamined
programs or unreleased compiler versions is explicitly bounded under
**Boundaries**. This report complements `equality-saturation-with-proofs-egraphs-aegraphs-and-refinement-rewriting`
and `isle-aegraphs-btl-symbolic-execution-and-dst-vtable-lowering-2026` by
quantifying whole-backend architectural trade-offs and non-TCB solver behavior.

## Findings

### 1. Cranelift Acyclic E-Graphs (`aegraphs`): Production Bounds and Ablation

Basis: source (`cranelift/codegen/src/egraph/*`, `opts/README.md`) + documentation
(Fallin 2026-04-09 ablation, Wasmtime issues `#6159`, `#6260`, `#8529`, `#8959`).

Cranelift embeds its e-graph directly inside `DataFlowGraph` using immutable
binary `ValueDef::Union` spines paired with a scoped `ScopedHashMap` GVN table
and side-effecting instruction skeleton:

- **Hard Scaling Guards (`cranelift/codegen/src/egraph/mod.rs`):** Saturation
  loops and arbitrary congruence closure are replaced by single-pass domtree
  preorder elaboration with `ECLASS_ENODE_LIMIT = 5`, `MATCHES_LIMIT = 5`,
  `REWRITE_LIMIT = 5` (per `optimize_pure_enode`), and `EXTRACTOR_FUEL = 500`.
  `opts/README.md` bans general commutativity and associativity rules, requiring
  directional canonicalization plus `subsume` whenever a rewrite drops a
  non-constant `Value` dependency (`is_pure_for_egraph` restricts pure nodes to
  single-result ops that are either non-loading/non-trapping or
  `readonly && notrap && can_move`). Side-effecting memory ops run through a
  separate greedy `SkeletonInstSimplification` pass backed by disjoint
  `AliasRegion` abstract domains (`alias_analysis.rs`).
- **Where the Speedup Actually Comes From (Fallin 2026-04-09):** On Sightglass
  Wasm benchmarks comparing `aegraph` against an identical-rules classical
  GVN+LICM pipeline, `aegraph` yields `~2%` runtime speedup at `+7–8%`
  compile-time overhead (having grown from parity in 2023 as ISLE rules expanded).
  Crucially, ablating `ValueDef::Union` (destructively keeping only the single
  lowest-cost rewrite at each step on the sea-of-nodes-with-CFG) isolates the
  e-graph multi-representation contribution to **`~0.1%` execution speedup** at
  **`~0.005%` compile time**, with a post-rewrite average of **`1.13` e-nodes
  per e-class** and only **`2`** missed eager sub-optimalities across `~4M`
  created value nodes (`ireduce`-of-`iadd` in `spidermonkey.wasm`).
- **Elaboration Weaknesses (`elaborate.rs`, open issues):** `compute_best_values`
  performs tree-sum DP over `Cost(u32)` (`Iconst=1`, simple ALU `=3`, `Imul=10`,
  default `=4`, trap/effect `+10`, load `+20`, store `+50`, explicitly warning
  at `elaborate.rs:428-455` that shared DAG chains saturate `u32` cost to
  `Cost::infinity()`). Licensing/hoisting uses `active_loop_depth` / `idom`
  (suppressed on `is_cold` blocks), rematerialization covers only 14 constant/ALU
  rules (`opts/remat.isle`), and demand elaboration lacks register-pressure or
  pipeline scheduling—manifesting in open bugs `#6159` (XNNPACK SIMD inner-loop
  pipeline stalls), `#6260` (scheduling heuristics), and `#8959` (`imul`
  needlessly duplicated across `brif` arms).

### 2. Whole-Function, Control-Flow, Effect, and Binder Encodings

Basis: source + execution metrics (`eggcc`, `Tamagoyaki`, `DialEgg`,
`Slotted E-Graphs`, `Colored E-Graphs`, `Guided Equality Saturation`).

| System / IR | Control Flow & Effects | Key Empirical Strength | Hard Scope / Semantic Boundary |
| :--- | :--- | :--- | :--- |
| **`DialEgg`** (CGO 2025) | Text-serializes MLIR blocks/regions to `(Reg (vec-of (Blk (vec-of ...))))` via temp files and `std::system("egglog ...")` | Dialect-agnostic `egg-opt` prototype over MLIR | `README.md:65` requires `<= 1` result per op; `Egglog.cpp:864-868` logs `"Skipping operation with more than one result"` without `continue`, falling through to `eggifyOpaqueOperation`; per-block IPC serialization |
| **`Tamagoyaki`** (`arXiv:2602.16707v2`) | In-IR MLIR `equivalence.{graph,class,yield}` + `ematch` + `pdl_interp` | `2.38x` multi-pattern e-match speedup; `1.18x` geomean vs. Herbie excluding bytecode load (`0.78x` total); `-11%` delay / `-6%` area on CIRCT `ShiftedFma` | Explicitly limited to **pure, straight-line code fragments** (`Section 4.1:1081`) |
| **`eggcc`** (OOPSLA 2026 `arXiv:2609.31887v2`) | Reducible CFG -> RVSDG (`If`, `Switch`, `DoWhile` + linear `StateT`) + `Assumption` contexts + `Statewalk DP` | `520x` geomean region extraction speedup vs. Gurobi; `94.7%` regions have `k=1` (`98.4% <= 5`); `6.52x` vs. `LLVM-O3-O3` on Fenwick `lowbit` | Rich `memory.egg` disabled (`schedule.rs:101,120`); `mem_simple.egg` comments out load/write commutation for `WeaklyLinear` (while `non_weakly_linear.egg:21-23` runs load-state bypass); `repeat 5` substitution cap; trails `LLVM-O3-O0` overall (`0.571` vs. `0.326` PolyBench); lowers back to LLVM 18 |
| **`Slotted E-Graphs`** (PLDI 2025) | First-class slot binders (`AppliedId`) inside e-classes | Eliminates alpha-renaming blowup in `SDQL`, `RISE`, `lean-egg` (`not_supIrred` `<1s` vs. `egg` OOM; `mathlib4` `6.77` vs. `12.7` binder steps) | Functional/binder IRs; tree-cost `Extractor` (`src/extract/mod.rs`), no imperative effect chains or regalloc model |
| **`Colored E-Graphs`** (`arXiv:2305.19203`) | Shared multi-color equivalence layers per assumption | `~10x` lower relative e-node overhead vs. cloned e-graphs across hundreds of case-split assumptions | Exploratory theorem proving / equality modulo conditions; higher runtime complexity on deep splits |

Two primary-source observations in `eggcc` clarify why full imperative equality
saturation remains difficult even with RVSDGs:

1. **Effect Linearization vs. Alias Rewrites (`WeaklyLinear`):** In `eggcc`,
   full cell/points-to tracking (`memory.egg`) is commented out in `schedule.rs`
   in favor of `mem_simple.egg`, where commuting a load past a non-aliasing
   write and bypassing `Load` state tokens are themselves commented out with
   warnings that they violate the `WeaklyLinear` state-edge invariant when stored
   values depend on loaded values (with `(union (Get load 1) state)` moved to
   `non_weakly_linear.egg`, guarded by `Statewalk DP`).
2. **Whole-Benchmark Code Quality vs. LLVM 18:** `eggcc` compares output binaries
   after running LLVM `sroa`, `-regalloc=greedy`, and `-optimize-regalloc`
   (`eggcc_profile.py:251-269`, OOPSLA 2026 Section 8.2). On PolyBench and Bril
   normalized to `LLVM-O0`, `eggcc` scores `0.571` and `0.876` geomean vs.
   `0.326` and `0.695` for `LLVM-O3-O0` (`0.312` and `0.542` with LLVM
   target-specific optimization enabled), losing mainly on missing scalar
   promotion, generalized loop unrolling, and stack coloring. However, targeted
   domain rules (`hackers_delight.egg`) collapse the Fenwick `lowbit` loop to
   `n & (-n)`, achieving `6.52x` speedup over `LLVM-O3-O3` (`23.01x` over
   `LLVM-O3-O0`). Meanwhile, `statewalk_width` remains small on `98.4%` of
   regions (`<= 5`), yet spikes to `106,259` on `heat-3d` (many independent
   loads/stores), requiring live-state bitmask and satellite-node pruning
   (`SATELLITE_BAR=6`) to remain tractable.

### 3. Cost Models, Extraction Latency, and Register-Pressure Scheduling

Basis: source + paper metrics (`SmoothE`, `e-boost`, `eggcc`) + execution
(`support/probe_egraph_backend.py`, `support/probe_results.txt`).

Extraction engines fall into three non-overlapping classes, none combining
sub-millisecond compiler speed with register-interference awareness:

- **Tree-Sum / Fuel-Bounded (`O(n log n)` / sub-ms):** `Cranelift elaborate.rs`
  and `slotted-egraphs/src/extract/mod.rs` extract fast enough for interactive/JIT
  compilers, but ignore shared sub-DAG reuse and live-range overlap.
- **Effect-Order FPT (`Statewalk DP`):** Eliminates external ILP solver timeouts
  (`CBC` fails/times out across PolyBench; `Gurobi` still hits 5-minute timeouts
  and infeasibilities on large regions) with `520x` speedup, yet prices extracted
  DAGs using static operator bag costs (`SCost` in `tiger/greedy.cpp` and
  `statewalkdp.cpp`) with no model of register count, spilling, or pipeline latency.
- **Non-Linear / DAG GPU & Hybrid ILP (`SmoothE`, `e-boost`):**
  `SmoothE` (ASPLOS 2025) relaxes discrete choices to GPU gradient descent +
  acyclicity penalties on A100 GPUs, taking `4.6±0.0s` (`impress`) to
  `24.4±2.5s` (`tensat` average) on linear models (Table 2) and up to `42.4±0.7s`
  on `NASRNN` (Table 3). `e-boost` (`arXiv:2508.13020v2`) accelerates logic/FV
  DAG extraction `558x` over vanilla ILP and `138x` (`19.04%` cost reduction)
  over ASPLOS'25 SmoothE (though updated `cornell-zhang/smoothe` reports beating
  `e-boost+CPLEX` by `7.8%`/`1.7%` under 60s caps on `boole`/`emorphic`), yet
  still reaches `3,599.09s` (`mul128`, `CP-SAT`) and `3,600.83s` (`mul48`,
  Gurobi) on `73k–1.2M`-node circuits. Neither models CPU register files.
- **Probe B (`[execution]`, `support/probe_egraph_backend.py`):** On a
  parametric $W$-wide shared-expression DAG where each intermediate $s_i$ feeds
  both an additive and XOR reduction (verified bitwise identical across `100/100`
  random 32-bit inputs per $W$):
  - At `W=8`, DAG sharing saves `1.68x` operations (`47` DAG ops vs. `79`
    rematerialized-tree ops).
  - Under naive postorder DFS (analogous to unscheduled demand elaboration), the
    shared DAG reaches **`peak_regs = 12`** (spilling on an 8-register target),
    whereas schedule-aware interleaving holds **`peak_regs = 7`** with `47` ops.
  - Under exact subset-DP optimal scheduling, `W=4` improves from `8` (DFS) ->
    `7` (naive interleaved) -> **`6` (`ExactOpt_DAG_peak`)**, and `W=3` from `6`
    -> `5`. Cost-only DAG/tree extraction without pressure-aware scheduling
    systematically mispredicts spill pressure and rematerialization ROI.

### 4. Phase-Ordering Blowup vs. Bounded Rewriting & Instruction Selection

Basis: source + execution (`Probe A` in `support/probe_egraph_backend.py`) +
literature (`Guided EqSat`, `Diospyros`, `ROVER`, `Hydride`).

- **Probe A (`[execution]`, deterministic across `PYTHONHASHSEED`):** On an
  $n$-term `+` chain saturated under `(a+b)==(b+a)` and `((a+b)+c)==(a+(b+c))`,
  full equality saturation grows exponentially (`n=2`: `3` e-classes / `4`
  e-nodes / `0.08ms` -> `n=5`: `31` / `185` / `18.89ms` -> `n=6`: `63` / `608`
  / `35.92ms` -> `n=7`: **`127` e-classes / `1,939` e-nodes / `max_ec=126` /
  `181.08ms`** for one expression), whereas enforcing Cranelift-like bounds
  (`enode_limit=5, match_limit=5` across rebuild) holds `n=7` at **`49` e-classes
  / `154` e-nodes / `max_ec=5` / `1.29ms`**. Similarly, unguided `egg` consumes
  `>60 GB` on `RISE` array binders without POPL 2024 *Guided Equality Saturation*
  (`<= 3` guides reducing memory to `<1 GB`), and `eggcc` hard-caps substitution
  at `(repeat 5 ...)` because dead terms cause divergence.
- **Instruction Selection & `Hydride` Correction:** General-purpose compilers
  avoid unified mid-end/ISel e-graphs because mid-end dominance elaboration and
  backward machine lowering conflict (`wasmtime#8529`; `#7321` where mid-end
  elaboration undid backend legalizations). Cranelift isolates `aegraph` before
  `lower.isle`, pairing pure `SinkableLoad` / `ProducesFlags` / `ConsumesFlags`
  and `put_in_reg_mem` rules within `InstColor` atomic regions
  (`machinst/lower.rs:37-61`). E-graph ISel thrives in constrained DSP/RTL/SIMD
  subdomains (`Diospyros`, `ROVER`, `Tamagoyaki`/CIRCT). **Negative boundary:**
  direct inspection of `akothen/Hydride` (`README.md`) confirms Hydride uses
  Rosette + Z3 SMT synthesis rather than e-graphs.

### 5. Verification & Certification Seams for Verified Compilers

Basis: source (`cranelift/isle/veri/*`, `eggcc/proofs/proofs.v`,
`opencompl/lean-mlir`).

| Verifier / Seam | What Is Checked | Solver / TCB Basis | Critical Unverified Gaps |
| :--- | :--- | :--- | :--- |
| **`VeriISLE` / `Arrival`** (OOPSLA 2025, `wasmtime`) | Chained ISLE rules (`simplify` mid-end & AArch64 `lower` derived via `ASLp`); `1,054` in-scope / `1,331` total `opt` expansions (`5,134` type instantiations) pass in `~4m`; `2.6x` fewer manual specs | `cvc5` + `z3` (with CI SMT query cache in `verify.sh`) | Unverified SMT solvers; `--default-excludes` skips `vector`, `atomics`, `spectre`, `narrowfloat`, `amode_const`, `i128`, `wasm_category_stack`; `simplify_skeleton` unsupported; CI `verify.sh` runs only `x64-iadd-base-case.args` on x64; global `relax_nan` flag is unsound if a float op feeds an integer result; **zero coverage** of `egraph/mod.rs`, `elaborate.rs`, or `alias_analysis.rs` |
| **`eggcc/proofs/proofs.v`** | 4 Coq 8.19.2 `Theorem`s on inductive `BS` `Ctx` constructors | Coq 8.19.2 kernel (240 LOC) | Toy AST lacking `BS` semantics for `Load`/`Store`, CFG->RVSDG lowering, `mem_simple.egg` (`WeaklyLinear`), and `Statewalk DP` |
| **`Lean-MLIR`** (`opencompl/lean-mlir`) | Region-based SSA peepholes (`denote_rewritePeepholeAt`), `EffectKind`, `SLLVM` (`AliveStatements`) | Lean 4 kernel (`[propext, Classical.choice, Quot.sound]`, zero `sorry`) | Verifies dialect semantics and peephole transforms, not external e-graph search or DAG extraction engines |

**Pareto Synthesis & TCB Seam:** Because verification coverage in `VeriISLE`
stops at individual ISLE rules while subtle backend failures occur in
saturation limits, `WeaklyLinear` effect rewrites, elaboration hoisting/remat,
and scheduling, high-assurance systems compilers partition into three viable
architectures, all anchoring soundness **after** extraction:

1. **Regime A (General-Purpose Fast Compilation):** Bounded `aegraph` (no AC,
   capped fanout) + decoupled `lower.isle` + `regalloc2`. Leave the `aegraph`
   matcher and `Elaborator` completely untrusted; discharge soundness via
   post-pass CFG/symbolic-execution Translation Validation (plus kernel-checked
   `BiEqRule`/`DirRefineRule`/`CongruenceDag` traces and `regalloc2::checker`).
2. **Regime B (Pure/Structured Kernel & SIMD Superoptimization):** Bounded
   `RVSDG` + `Statewalk DP` (`k <= 5`) or `Slotted E-Graphs` + `Guided EqSat`
   invoked selectively on hot pure, SIMD, bit-manipulation, or binder-heavy
   regions (avoiding `DialEgg`'s single-result/IPC bottleneck and `SmoothE`'s GPU
   latency), verified via per-kernel `CongruenceDag` / Lean-MLIR / BTL checks
   prior to native lowering.
3. **Regime C (Hybrid Verified Compiler Backend):** Reject all-in-one whole-function
   `egglog` + GPU DAG extraction + unified `MachInst`/regalloc e-graphs. Keep
   SSA/CFG lowering + pressure-aware scheduling + `regalloc2` as the spine, run
   bounded `aegraph`/ISLE mid-end cleanup + selective bounded superoptimization on
   hot slices, and verify end-to-end via decoupled Translation Validation.

## Boundaries

- **`eggcc` Runtime & Benchmark Coverage:** Bril and PolyBench runtime comparisons
  against `LLVM-O3-O0` (`0.571`/`0.876` vs. `0.326`/`0.695`) reflect the pinned
  OOPSLA 2026 evaluation (using out-of-process `tiger` and Bril's LLVM lowering
  with `sroa` + greedy regalloc, whereas `eggcc` HEAD defaults to in-process
  `effsafe`); arbitrary C/Rust control-flow graphs with unstructured irreducible
  loops are **unsupported** by `eggcc`'s reducible RVSDG frontend.
- **`Arrival` OOPSLA 2025 Full PDF:** The ACM DL paper PDF was not fetched due
  to link access limits (**unknown** internal bug catalog beyond Wasmtime's
  checked-in `cranelift/isle/veri/` tree, `README.md`, `verify.sh`, and
  `configs/*.args`, which were inspected directly).
- **Direct Reproduction of Third-Party GPU/ILP Suites:** `SmoothE` (A100 CUDA),
  `e-boost` (CPLEX/CP-SAT), `eggcc` (Gurobi), `DialEgg` Docker container, and
  `slotted-egraphs` `mathlib4` runs were **not re-executed locally**; cited
  figures rest on primary-source artifact scripts, papers, and checked-in
  result summaries.
- **`Probe A` / `Probe B` Scope:** Our standalone Python probes model minimal
  pure AC `+` chains (`n=2..7`) and symmetric dual-reduction DAGs (`W=3..8`,
  `32`-bit bitwise ops) under a single-cycle 3-address register model; **known
  not to apply** directly as full-ISA SPEC/Wasm benchmark predictors without
  target calling conventions and memory hazards.

## Evidence

- **`bytecodealliance/wasmtime` (`cef75a9fea591317bb076ec04d1f1a99ccfedb63`,
  observed 2026-11-24):** `cranelift/codegen/src/egraph/{mod,elaborate,cost}.rs`,
  `cranelift/codegen/src/opts/README.md`, `remat.isle`, `skeleton.isle`,
  `cranelift/codegen/src/machinst/lower.rs`, `cranelift/codegen/src/isa/x64/lower.isle`,
  `cranelift/isle/veri/{README.md,verify.sh,configs/*.args,veri/src/{lib,veri,expand}.rs}`,
  GitHub issues `#6159`, `#6260`, `#8529`, `#8959` (`state=open`), and Chris
  Fallin's blog post `https://cfallin.org/blog/2026/04/09/aegraph/`.
- **`egraphs-good/eggcc` (`8337bb0dd00b794b118997357fcd9fdd5aff528c`) &
  OOPSLA 2026 (`arXiv:2609.31887v2`, observed 2026-11-24):** `dag_in_context/src/{lib,schedule,add_context}.rs`,
  `dag_in_context/src/optimizations/{memory,mem_simple,non_weakly_linear}.egg`,
  `dag_in_context/src/tiger/{statewalkdp,greedy,ilp}.cpp`,
  `infra/{nightly.py,profile.py,macros.py,graphs.py,simple_table.py}`,
  `proofs/proofs.v`, and `https://rtjoa.com/papers/oopsla26-eggcc.pdf`.
- **`Tamagoyaki` (`arXiv:2602.16707v2`, observed 2026-11-24):** Full arXiv text
  (Section 4.1 straight-line scope, `pdl_interp` matching & CIRCT `ShiftedFma`).
- **`AzizZayed/dialegg-cgo-artifact` (`4d0d522e98c15becdc5e7d711348cb0891ff0d44`,
  observed 2026-11-24):** `README.md`, `src/Egglog.cpp`, `src/EqualitySaturationPass.cpp`,
  `bench/{opt,bench,plot}.py`, `test/timer.py`.
- **`memoryleak47/slotted-egraphs` (`48cefee5503822224257e4f2e81681fef212ae89`)
  & `slotted-egraphs-artifact` (observed 2026-11-24):** `src/extract/mod.rs`,
  `README.md`, `sdql/{slotted/src/main.rs,slotted/bench.sh}`,
  `functional-array-language/plot.py`.
- **`SmoothE` (`cornell-zhang/smoothe` @ `8de74ef2b53aabbb35898400cb5eb890d9a07a54`),
  `e-boost` (`arXiv:2508.13020v2`), `Colored E-Graphs` (`arXiv:2305.19203`),
  `akothen/Hydride` (`0c97d0f9d3f8cd0494e421b9ece4b24488b614e5`), and
  `opencompl/lean-mlir` (`b8c4a771319a044854a4bbb49b8821381ef86ff8`,
  `arXiv:2407.03685`, observed 2026-11-24).**
- **Preserved Probe Execution (`support/probe_egraph_backend.py`,
  `support/probe_results.txt`, observed 2026-11-24):** Deterministic across
  `PYTHONHASHSEED=1` and `PYTHONHASHSEED=999`; `Probe A` verifies `127`
  e-classes / `1,939` e-nodes (`max_ec=126`) vs. `49` / `154` (`max_ec=5`) at
  `n=7`; `Probe B` verifies `100/100` random 32-bit semantic equivalence across
  all `W` and exact peak live-register counts (`W=8`: `47` vs. `79` ops, `12`
  DFS vs. `7` interleaved; `W=4`: `8` DFS -> `7` interleaved -> `6` exact DP).

## Revalidation

1. **Deterministic AC & Schedule/Register-Pressure Micro-Probe (`Probe A/B`):**
   From this package directory, verify seed independence and exact counts:
   ```console
   PYTHONHASHSEED=1 python3 support/probe_egraph_backend.py > /tmp/p1.txt
   PYTHONHASHSEED=999 python3 support/probe_egraph_backend.py > /tmp/p2.txt
   diff -u <(sed 's/[0-9.]*ms/TIME/g' /tmp/p1.txt) <(sed 's/[0-9.]*ms/TIME/g' /tmp/p2.txt)
   diff -u <(sed 's/[0-9.]*ms/TIME/g' support/probe_results.txt) <(sed 's/[0-9.]*ms/TIME/g' /tmp/p1.txt)
   ```
   A zero exit confirms `Probe A` (`49` e-classes / `154` e-nodes capped vs.
   `127` / `1,939` uncapped at `n=7`) and `Probe B` (`100/100` equivalence,
   `peak_regs` divergence across DFS/interleaved/exact schedules). Passing does
   not validate real-ISA register coloring or LLVM/Cranelift pass timings.
2. **Upstream Invariant Drift Checks:**
   - Cranelift `aegraph`/ISel: check `cranelift/codegen/src/egraph/{mod,elaborate}.rs`
     constants (`ECLASS_ENODE_LIMIT`, `Cost`), `cranelift/isle/veri/verify.sh`
     `CONFIGS`, and open status of Wasmtime issues `#6159`, `#6260`, `#8529`,
     `#8959` (e.g., if `#8529` lands, the strict phase separation in Findings §4
     requires re-evaluation).
   - `eggcc` memory/schedule soundness: inspect `dag_in_context/src/schedule.rs`
     (whether `"memory"` remains commented out) and `mem_simple.egg` /
     `non_weakly_linear.egg`.
