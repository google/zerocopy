# Compiler IR Architectures: Sea-of-Nodes, Structured Regions (RVSDG), CPS/ANF/Join Points, Multi-Level Dialects (MLIR), and Acyclic E-Graphs

## Summary

Compiler intermediate representation (IR) architecture governs which invariants hold structurally by construction, which require repeated recomputation, how side effects restrict code motion, and where compile-time latency or miscompilation risk concentrates. Direct inspection of seven pinned compiler codebases (`openjdk/jdk` HotSpot C2, `v8/v8` TurboFan/Turboshaft, `oracle/graal`, `phate/jlm` RVSDG, `ghc/ghc` Core, `llvm/llvm-project` MLIR, and `bytecodealliance/wasmtime` Cranelift), foundational papers, and production retrospectives establishes five core results:

1. **Pure Sea-of-Nodes degrades on effect- and guard-dense dynamic code (V8 `TurboFan` → `Turboshaft`), whereas hybrid fixed/floating backbones (`Graal`, `Cranelift`) retain most of its benefits.** V8's 2025 retrospective documents ~3× average (up to 7× peak) L1 dcache misses, ~1 mutation per 20 bottom-up visits, Load Elimination bailouts (replaced by a CFG pass up to 190× faster), parallel control/effect-chain bugs, and ~2× faster compilation on Turboshaft's flat `OperationBuffer` + `CopyingPhase` CFG pipeline. HotSpot C2 remains Sea-of-Nodes but needs a 4-state `ConstraintCastNode::DependencyType` lattice to stop range-checked loads from floating above guards; Graal pairs a `FixedNode` backbone with `FloatingNode` pure dataflow, `BeginNode`-anchored `GuardNode`s, and `StateSplit`/`FrameState` checkpoints.
2. **Structured acyclic region IRs (`RVSDG`) eliminate CFG invariant-repair churn by construction, trading it for irreducible-CFG restructuring and alias-sensitive state edges.** Reissmann et al. (TECS 2020) found 57 of 266 pass invocations (21%) in LLVM 7.0.1 `-O3` were six structural helper passes plus 14 SSA-restoration passes. RVSDG's acyclic `γ`/`θ`/`λ`/`φ` regions eliminate dominator trees and loop finders, but structuring irreducible CFGs without node duplication (Bahmann et al., TACO 2015; `jlm`) adds synthetic predicates (`#p`, `#q`, `#r`) and dynamic dispatch branches (`2.463×` in our 2-entry loop probe), while a single memory state edge re-creates Sea-of-Nodes' effect-chain bottleneck.
3. **SSA, CPS, ANF, and Direct-Style Join Points are formally inter-translatable yet diverge sharply on β-closure, evaluation order, and commuting conversions.** ANF is not closed under β-reduction (Kennedy, ICFP '07). Full CPS (`letcont`) fixes evaluation order, inhibiting call-by-need let-floating, syntactic CSE, and `{-# RULES #-}` (Maurer et al., PLDI '17 §8). GHC Core's System $F_J$ adds lexically scoped second-class continuations (`JoinId`/`jump`) directly to direct style via `jfloat`/`abort` and six `Core Lint` invariants, eliminating 85.9%–100.0% of allocations on tight `shootout` loops while production GHC restricts calls to strict syntactic tail positions.
4. **Multi-level extensible IRs (`MLIR`) unify block-argument `SSACFG` and single-block `Graph` regions, creating cross-dialect trait-drift and a one-way semantic-erasure cliff.** Because MLIR's verifier enforces syntax and hierarchical dominance without operational semantics, generic CSE/LICM/DCE soundness rests on dialect interfaces—splitting `NoMemoryEffect` (*may still have UB*, e.g., `arith.divsi` using `ConditionallySpeculatable`) from `Pure` (`[AlwaysSpeculatable, NoMemoryEffect]`)—while progressive lowering creates `unrealized_conversion_cast` seams and erases high-level loop/aliasing invariants at the LLVM boundary.
5. **Cranelift's production acyclic e-graphs (`aegraphs`) owe their ~2% execution speedup almost entirely to a transient sea-of-nodes-with-CFG-skeleton, not equality saturation.** Fallin (2026-04-09) reports 23% zero-rewrite round-trip overhead for standalone `egg` (vs. ~10% mid-end share) versus ~2% faster code at +7–8% compile time for Cranelift's in-place `ValueData::Union` aegraph. Ablating union nodes shows multi-representation + tree-DP extraction contributes only **~0.1% speedup** (mean e-class size **1.13 e-nodes**; **2 non-saturation misses in ~4M nodes**). Dropping non-constant operands without `subsume` breaks SSA dominance (`opts/README.md` Rule 2), and ignoring DAG sharing in tree-DP extraction is provably suboptimal via weighted set cover.

## Applicability

This report compares architectural invariants, empirical retrospectives, and verification properties across the 17 primary artifacts in `REPORT.json`:
- **Sea-of-Nodes & Hybrid IRs:** Click & Paleczny (IR '95), Click (PLDI '95), `openjdk/jdk` (`opto/`), `v8/v8` (`src/compiler/`, `turboshaft/`), Mercadier (2025-03-25), Duboscq et al. (VMIL '13), and `oracle/graal`.
- **Structured Regions:** Bahmann et al. (TACO 2015), Reissmann et al. (TECS 2020), and `phate/jlm` (`jlm/rvsdg/`, `ControlFlowRestructuring.{hpp,cpp}`).
- **Functional IRs:** Kennedy (ICFP '07), Maurer et al. (PLDI '17), and `ghc/ghc` (`GHC/Core.hs`, `GHC/Core/Lint.hs`), bridged via Kelsey (1995), Appel (1998), and Cong et al. (2019).
- **Multi-Level IRs & Acyclic E-Graphs:** Lattner et al. (CGO '21), `llvm/llvm-project` (`mlir/`), `bytecodealliance/wasmtime` (`cranelift/codegen/src/egraph/`, `opts/`), and Fallin (2026-04-09).
- **Executable Probe:** `support/verify_ir_transformations.py` (Python 3.10+, stdlib only) checks structural invariants and observational equivalence on an effectful diamond+loop kernel; its counts characterize those modeled IR mechanics, not native compiler benchmarks.

**Adjacent corpus packages (non-duplicating cross-references):**
- Imperative SSA mechanized semantics (`CompCert`, `Vellvm`, `Alive2`, `Crellvm`, `lean-mlir`, `Isabelle-LLVM`, `K-LLVM`), `undef`/`poison`/`freeze`, provenance, and machine frames: `mechanized-compiler-ir-semantics-poison-provenance-and-machine-frames` and `llvm-ir-baseline-formal-semantics-and-ambiguities`.
- Cyclic equality saturation (`egg`, `egglog`), congruence-closure proofs (FMCAD '22), `Lean-Egg`, and verified Cranelift/ISLE rewriting certificates: `equality-saturation-with-proofs-egraphs-aegraphs-and-refinement-rewriting`.

## Findings

### 1. Structural Taxonomy and SSA Flavors (`φ`-Nodes vs. Block Arguments)

*Basis: normative + documentation + source + derived.*

Every optimizing IR encodes three dependency layers: **value dataflow**, **control flow** (execution paths and path conditions), and **effect/memory ordering** (observable mutations, traps, and divergence). Competing IR architectures diverge chiefly in which layers are **enforced by syntax** versus **maintained externally**:

| Paradigm | Representative Systems | Control | Side-Effect / Memory Ordering | SSA / Dominance | Primary Strength | Primary Failure Mode / Cost |
|---|---|---|---|---|---|---|
| **Block-Arg / φ CFG SSA** | V8 `Turboshaft`, LLVM IR, Cranelift `CLIF`, Swift `SIL` | Basic blocks + CFG edges | Block order + MemorySSA / AA | External (`DomTree`, `LoopInfo`) | Cache-friendly flat layout; single-pass forward RPO; direct source/asm map | Pass-ordering coupling; helper-pass churn (`-domtree`, `-lcssa`, SSA repair); stale analyses |
| **Pure Sea-of-Nodes** | Click & Paleczny (1995), HotSpot `C2`, V8 `TurboFan` | `Region`/`If`/`Proj` nodes (`in[0]`) | Explicit `Store`/effect chain + `EffectPhi` + anti-deps | Implicit use-def; pinning via `in[0]` / `CastII` | Free hash-consing GVN; location-free LICM via GCM | Effect/control saturation in dynamic code; ~3–7× L1 dcache misses; lost control-dep trap/OOB bugs |
| **Hybrid Fixed / Floating** | `Graal` (`FixedNode` + `FloatingNode`) | Linked `FixedNode` backbone; floating pure ops | Fixed side effects + `StateSplit`/`FrameState` + `GuardNode`/`PiNode` | Explicit guard + `BeginNode` anchor edges | Decouples guards from deopt sites; coalesces guards via GVN on a CFG backbone | Requires `SchedulePhase`; guard-anchoring and memory-graph complexity |
| **Structured Regions (RVSDG)** | `jlm`, Reissmann et al. (2020) | Nested acyclic `γ`, `θ`, `λ`, `φ` regions | Explicit linear state edges (memory + non-termination) | Intrinsic lexical region boundaries | Zero dominator/loop-finder/SSA-repair passes; local DNE/CNE/PSH | Irreducible-CFG restructuring adds synthetic predicates & branches; coarse state edge serializes loads |
| **Direct-Style + Join Points (vs. CPS/ANF)** | `GHC Core` (System $F_J$), Kennedy `λ_CPS` | Lexical `join`/`jump` or `letcont` | Pure / monadic or effect-typed CPS | Intrinsic lexical scope + `Core Lint` tail/arity checks | Order-independent `case-of-case` without closures; keeps direct-style CSE & rules | Requires separate imperative backend (Cmm/LLVM) for mutable loops & SIMD |
| **Multi-Level Extensible IR** | `MLIR` (`llvm/llvm-project`) | Nested `SSACFG` & single-block `Graph` regions | Dialect `MemoryEffectsOpInterface` + `ConditionallySpeculatable` | Hierarchical dominance + `IsolatedFromAbove` | Progressive lowering across domain dialects (`affine`/`linalg`/`scf`/`llvm`) | No built-in semantics; trait misclassification; `unrealized_conversion_cast` seams; semantic erasure |
| **CFG-Skeleton + Acyclic E-Graph** | `Cranelift aegraphs` (`wasmtime`) | Persistent CFG skeleton + transient pure sea-of-nodes | Side-effect skeleton stays in CFG; pure ops float in DFG | `available_block` + mandatory `subsume` on dropped operands | Fuses GVN, DCE, LICM, remat, and single-pass ISLE rewrites in-place | Tree-DP ignores DAG sharing (NP-hard optimum); multi-rep adds ~0.1% on pre-optimized Wasm |

#### `φ`-Nodes vs. Block Arguments

Modern CFG-SSA designs (`MLIR`, `Cranelift CLIF`, `Swift SIL`) replace traditional **`φ`-nodes** (`LLVM IR`, `HotSpot C2`, `V8`) with **block arguments**:

- **Explicit parallel-copy edge semantics:** In `llvm/llvm-project@f19509b0` (`mlir/docs/LangRef.md` L384–434), `φ` nodes live inside the target block yet execute semantically as parallel copies on incoming edges—requiring special rules (pinning at block top, awkward handling of terminator-defined values like LLVM `invoke`/`callbr` or unsplittable critical edges). Block arguments (`^bb3(%c: i64):` fed by `cf.br ^bb3(%b: i64)`) make edge-scoped parallel copies explicit and unify function arguments, region entry parameters, and merge values (`cranelift/codegen/src/ir/dfg.rs` L693–709: `ValueData::Param { ty, num, block }`).
- **Remaining costs:** Block arguments do not remove the lost-copy/swap problem during SSA destruction—they hand it cleanly to the backend parallel-move resolver (e.g., `regalloc2`). Multi-way terminators (`switch`) with per-edge argument tuples become heavier, and dead-parameter elimination still updates every predecessor terminator. V8's `Turboshaft` (`src/compiler/turboshaft/graph.h` L37–39) retains `Phi` ops (using `OperationBuffer::ReplaceScope` to patch `PendingLoopPhi` in place) for compact flat storage and straightforward lowering from TurboFan/Maglev.

---

### 2. Sea-of-Nodes: Unification, V8's Retreat (`Turboshaft`), and Hybrid Alternatives (`C2` vs. `Graal`)

*Basis: normative + documentation + source + execution + derived.*

#### 2.1 Click & Paleczny (1995) Unification and GCM Scheduling

Click & Paleczny (IR '95, §2.1–2.5) unified CFG and dataflow into a single directed graph of vertices with ordered inputs (`x[0]`, `x[1]`, …) and unordered uses:

- **Control as graph tokens:** Basic blocks become `REGION` nodes merging control edges; branches become `IF` nodes outputting a 2-tuple split by zero-cycle `PROJECTION-TRUE` and `PROJECTION-FALSE` nodes (§2.2, §2.4). A `PHI` node binds `in[0]` to its governing `REGION` so its $i$-th data input aligns with the `REGION`'s $i$-th control input, keeping `PHI` locally compositional (§2.3).
- **Free GVN and Global Code Motion (Click, PLDI '95):** Pure nodes omit `in[0]`, so hash-consing `(opcode, inputs)` performs GVN automatically. Scheduling back to basic blocks (`openjdk/jdk@4f332731`, `src/hotspot/share/opto/gcm.cpp` L308, L1550) runs `schedule_early` (deepest dominator-tree block among inputs and `in(0)`; constants attach to `_root`, L331–335) followed by `schedule_late` (dominator-tree LCA of all uses—evaluating `Phi` uses in predecessor blocks—then walking up to `early` to choose minimum loop depth, giving LICM for free).
- **Memory `STORE` and anti-dependences:** Memory is threaded as a value through `STORE` nodes and memory `PHI`s, while `LOAD` reads `STORE` without producing a new token (§2.5). Allowing loads to reorder creates **anti-dependences** (read-before-write hazards) absent from the dataflow graph. Click & Paleczny treat `STORE` as a unique register with infinite spill cost; HotSpot C2 (`gcm.cpp` L805–860) runs an explicit worklist search over `MergeMem` slices, memory `Phi`s, and stores to raise a load's LCA and insert anti-dependence edges before final placement.

#### 2.2 Why V8 Retreated from Sea-of-Nodes (`TurboFan` → `Turboshaft`)

After a decade running Sea-of-Nodes in TurboFan (adopted in 2013 to escape Crankshaft's inability to introduce control flow during lowering), V8 migrated to **Turboshaft**, a flat CFG SSA IR. Darius Mercadier's 2025-03-25 V8 retrospective and direct inspection of `v8/v8@e88118f6` document nine compounding production failures on JavaScript and WebAssembly:

| Failure Mode | Sea-of-Nodes (`TurboFan`) Pathology | CFG Resolution (`Turboshaft`, `v8/v8@e88118f6`) |
|---|---|---|
| **1. Effect/Control Saturation** | Typical JS (`a.str + b.str`) chains `CheckedTaggedToTaggedPointer` → `CheckMaps` → `LoadField` → `CheckString` → length check → `StringConcat` sequentially on the effect/control chain, leaving few pure nodes free to float. | Intra-block execution order is implicit; no parallel effect-chain edges to maintain. |
| **2. Immobile Memory Ops** | A single effect chain (`Load` → `Load` → split to `Return`s) mirrors CFG splits, preventing loads from sinking into single-use branches without CFG-equivalent alias analysis. Multiple effect chains were rejected as too error-prone and quickly re-merged under JS aliasing. | CFG snapshot-table analyses (`late-load-elimination-reducer.h`, `snapshot-table.h`) reason directly over blocks. |
| **3. Parallel Chain Bugs & Deadness** | Lowerings juggle parallel control and effect chains (`JSNativeContextSpecialization::ReduceNamedAccess` tracked 3 effect chains simultaneously and shipped a wrong-chain bug for months). Deadness propagation must walk forward along the effect chain to the next merge while fixing control edges. | Cutting a dead CFG edge makes dominated blocks unreachable automatically via one topology. |
| **4. Visitation Order & State Tracking** | Pure nodes lack forward roots, forcing bottom-up traversal from `Return` with revisitation of uses: V8 measured **~1 change per 20 node visits**. Stateful passes (Load Elimination, Escape Analysis) cannot discard state early, forcing bailouts on large graphs. | Forward block-order `CopyingPhase` (`copying-phase.h`) optimizes defs before uses in one pass; Turboshaft's CFG Load Elimination benchmarked **up to 190× faster** on large graphs. |
| **5. L1 Data-Cache Pathology** | In-place mutation of bidirectional `Node`s (`Use*` linked lists + inline/outline `ZoneNodePtr`, `src/compiler/node.h` L82–270, L466–553) fragments zone memory: V8 measured **~3× average (up to 7× peak) more L1 dcache misses** (~5% compile time). | `OperationBuffer` (`turboshaft/graph.h` L33–100) packs operations contiguously into append-only 8-byte `OperationStorageSlot`s with bidirectional size tags, rebuilt cleanly by `CopyingPhase` CRTP reducers (`OutputGraphAssembler`, `copying-phase.h` L52–101). |
| **6. Scheduler Duplication Churn** | Pure GVN merges identical `a / b` across `switch` cases 1 and 2; scheduling hoists the division above the `switch` onto cold case 3, forcing `Scheduler::kSplitNodes` (`scheduler.h` L34) to re-duplicate what GVN just merged. | Scoped dominator-tree GVN (`value-numbering-reducer.h`) never merges expressions across non-dominating sibling arms. |
| **7. Flow-Sensitive Typing** | Narrowing `CheckedAdd(x, 1)` under `if (x < 42)` fails if `CheckedAdd` floats; pinning it with a control input recreates CFG constraints on a pure op. | Fixed block placement directly exposes dominating branch predicates. |
| **8. Control-Flow Lowering & Loops** | Lowering a pure floating op (`Int32Max`) into `if/else` cannot locate a control splice point until mid-pipeline scheduling builds a CFG; finding loop-resident floating nodes complicates peeling/unrolling. | Reducers emit new CFG blocks at any stage; explicit loop passes (`loop-finder.h`, `loop-peeling-reducer.h`, `loop-unrolling-reducer.h`). |
| **9. Wasm AOT Schedule Destruction** | Sea-of-Nodes discards AOT register-pressure scheduling from LLVM/Binaryen, forcing a fast JIT scheduler that can increase spilling. | CFG preserves incoming Wasm order unless deliberately transformed. |

**Empirical outcome & pinned repository state (`v8/v8@e88118f6`):** Turboshaft roughly **halved compile time** compared to Sea-of-Nodes. At `e88118f6`, `DEFINE_BOOL(turboshaft, true, ...)` (`src/flags/flag-definitions.h` L1722) enables Turboshaft by default across Wasm, the JS backend, and CSA builtins (`turboshaft/pipelines.cc` L178–195), while `DEFINE_BOOL(turbolev, false, ...)` (`flag-definitions.h` L1795) guards the Maglev-to-Turboshaft JS frontend (`turbolev-frontend-pipeline.cc` L48–105); by default, `src/compiler/pipeline.cc` (L795–821, L2500, L3230–3248) still lowers the JS frontend from Sea-of-Nodes into Turboshaft via `CreateGraphFromTurbofan`.

#### 2.3 Guard-Pinning Failures in HotSpot C2 vs. Graal's Hybrid Backbone

When a node's safety (avoiding division traps, null dereferences, or out-of-bounds loads) depends on a dominating runtime check, losing its control dependency in Sea-of-Nodes causes miscompilation.

**HotSpot C2 (`openjdk/jdk@4f332731`, `src/hotspot/share/opto/castnode.hpp` L34–154):** Because C2 nodes have **at most one control input `in(0)`**, path-sensitive type/bounds narrowing via `ConstraintCastNode` (`CastII`, `CastLL`, `CastPP`) requires a 4-state `DependencyType` lattice (`castnode.hpp` L56–133):
- `FloatingNarrowing`: single range-check cast; may float with its check and be elided if input type is already narrower.
- `FloatingNonNarrowing`: widening casts after loop opts; **cannot be removed even when the input type is narrower**, because dropping the Cast severs the control edge to the range check, allowing dependent array accesses to float above the check and read out of bounds (`castnode.hpp` L114–117).
- `NonFloatingNarrowing`: range-check smearing where an access depends on *multiple* checks; because C2 *"cannot model two control dependencies for a node in the IR"* (`castnode.hpp` L122–123), the Cast must be pinned (`_floating = false`).
- `NonFloatingNonNarrowing`: pins loop-sunk nodes so they cannot float back into a loop (`castnode.hpp` L127–131).

```text
Sound Sea-of-Nodes pinning vs. Lost-Control-Dependency Bug (modeled in support/verify_ir_transformations.py):
  Pinned:   SDiv(ctrl = ProjTrue(b != 0), data = [a + inv, b])  --GCM--> scheduled in bb_then  (safe when b == 0)
  Unpinned: SDiv(ctrl = None,             data = [a + inv, b])  --GCM--> floats to bb_entry    (TRAPS when b == 0 or n == 0!)
```

**Graal's Hybrid IR (`Duboscq et al. VMIL '13`; `oracle/graal@3fd1dcaa`):** Graal was architected as a **hybrid fixed/floating IR** rather than pure Sea-of-Nodes:
- **Fixed backbone + floating pure ops:** Control flow and side effects subclass `FixedNode` / `FixedWithNextNode` (`FixedNode.java`, `FixedWithNextNode.java`); pure computations subclass `FloatingNode` (`calc/FloatingNode.java`) and are placed during `SchedulePhase` (`SchedulePhase.java` L107–180: `EARLIEST`, `EARLIEST_WITH_GUARD_ORDER`, `LATEST`, `LATEST_OUT_OF_LOOPS`, `LATEST_OUT_OF_LOOPS_IMPLICIT_NULL_CHECKS`).
- **Decoupled deoptimization (`StateSplit` + `FrameState`):** Only irreversible side-effecting fixed nodes implementing `StateSplit` (`StateSplit.java` L44–51) carry `FrameState` snapshots (bytecode index `bci`, locals, operand stack, locks, virtualized objects; `FrameState.java` L69–120).
- **Explicit guard evidence (`GuardNode` + `PiNode`):** Speculative checks lower from `FixedGuardNode` to floating `GuardNode extends FloatingAnchoredNode` (`GuardNode.java` L49–88), anchored to the furthest dominating `BeginNode` that still post-dominates the guarded op (Duboscq et al. §4.2). Dependent loads and type narrowings (`PiNode extends FloatingGuardedNode`, `PiNode.java` L76–91) consume the `GuardingNode` as a typed input edge—preventing unsafe hoisting above the guard while letting GVN coalesce guards sharing `(condition, anchor)` without side-effect entanglement.

---

### 3. Structured Region IRs (`RVSDG`): Acyclic Regions, State Edges, and Restructuring Overhead

*Basis: normative + source + execution + derived.*

#### 3.1 Structural Node Taxonomy and Intrinsic Invariants

The Regionalized Value State Dependence Graph (RVSDG; Reissmann et al., ACM TECS 2020; `phate/jlm@b6d2582a`) replaces flat CFGs and `φ`-nodes with **nested, strictly acyclic regions** (`jlm/rvsdg/region.hpp` L32–75). Every region is a DAG whose inputs enter via `RegionArgument` ports and exit via `RegionResult` ports; cross-region edges are unrepresentable, so SSA and dominance hold intrinsically. Five `StructuralNode` kinds compose all control and module structure:
- **$\gamma$-node (`GammaNode`, `gamma.hpp` L64–98):** Conditional / pattern-matching selection over $k$ acyclic subregions (`EntryVar` inputs, `ExitVar` outputs).
- **$\theta$-node (`ThetaNode`, `theta.hpp` L32–125):** Tail-controlled (`do-while`) loop with one acyclic body region, paired `LoopVar` (pre/post) ports, and a repetition predicate result. Head-controlled `while`/`for` loops wrap $\theta$ inside an outer $\gamma$ zero-trip guard.
- **$\lambda$-node (`LambdaNode`, `lambda.hpp` L82–138):** Function abstraction importing free values via explicit `ContextVar` ports.
- **$\phi$-node (`PhiNode`, `Phi.hpp` L45–99):** Mutual recursion binder over `FixVar`s (distinct from SSA $\phi$).
- **$\delta$-node (`delta.hpp`):** Global data object definition.

Side effects are ordered solely via explicit **state edges** threaded through region ports. Reissmann et al. (§7.1) thread two states in `jlm`: one for **memory** and one for **non-terminating loops** (preventing dead-node elimination from deleting infinite loops with unused outputs).

#### 3.2 Eliminating CFG Helper Churn vs. `jlm` Empirical Performance

Reissmann et al. (§2.1 Table 1 & §7.6) audited LLVM 7.0.1's `-O3` pipeline: out of **266 total pass invocations** across **85 passes**, **57 invocations (21%)** were six structural/invariant helper passes (`-loops` 14×, `-domtree` 13×, `-simplifycfg` 8×, `-loop-simplify` 8×, `-lcssa` 7×, `-lcssa-verification` 7×), alongside **14 SSA-restoration passes** and **37 alias-analysis runs** (`-aa` 19×, `-basicaa` 18×). In RVSDG, Dead Node Elimination (`DNE`) is backward reachability from region results, Common Node Elimination (`CNE`) is local DAG congruence, and Node Push-Out (`PSH`) hoists loop-invariant ops out of $\theta$ purely by checking whether `LoopVar` post-ports equal pre-ports—requiring zero dominator trees or loop finders.

In `jlm`'s PolyBench 4.2.1 evaluation (Xeon E5-2695v4, clang/LLVM 7.0.1 baseline; Reissmann et al. §7.2–7.5):
- **Geomean speedup vs. `-O0`:** `jlm` reached **2.70×**, beating `opt -O1` (**2.49×**) while trailing `opt -O3` (**3.22×**), `opt -O3-no-vec` (**2.95×**), and `opt -O3-no-vec-stripped` (**2.91×**).
- **Bottlenecks identified:** Missing vectorization (8 benchmarks), missing loop-load elimination and `memcpy` idiom recognition (`adi`, `durbin`, `seidel-2d`), and—critically on `syrk`—**over-serialization from a single coarse memory state edge**, which prevented `CNE` from recognizing congruent loads separated by distinct state origins (§7.3).
- **Code size & scaling:** Unconditional 4× inner-loop unrolling grew `.text` by ~39% over `-Os`, whereas `jlm -no-unroll` sat between `-O3-no-vec` and `-Os`. Both RVSDG node count and compile time scaled linearly with LLVM instruction count (§7.4–7.5).

#### 3.3 Irreducible CFG Restructuring Cost

Importing arbitrary CFGs (`goto`, multi-exit loops, irreducible multi-entry loops) requires **Control Flow Restructuring (CFR)** (Bahmann et al., TACO 2015; `phate/jlm@b6d2582a`, `jlm/llvm/frontend/ControlFlowRestructuring.{hpp,cpp}` L15–100). To avoid worst-case exponential code blowup from node splitting, `RestructureLoops` and `RestructureBranches` introduce synthetic control variables—continuation selectors (`#p`), loop entry/exit selectors (`#q`), and tail repetition flags (`#r`)—reducing every loop to a single-entry tail-controlled $\theta$ wrapping a $\gamma$ dispatcher.

Our runnable probe (`probe_irreducible_restructuring`) verifies this exact trade-off on a 2-entry irreducible loop (`L1 <-> L2`): **0 duplicated body blocks** and 18/18 exact equivalence, at the cost of **2 synthetic predicates** (`#q`, `#r`) and an increase in dynamic branch executions from **67 to 165 (`2.463×`)**. Additionally, Reissmann et al. (§7.1) note that exceptions and LLVM intrinsics were unsupported in the evaluated `jlm` pipeline; non-local control (`setjmp`, unwinding, computed `goto`, coroutines) maps poorly without explicit state-machine lowering.

---

### 4. Functional IRs and SSA Equivalence: CPS vs. ANF vs. GHC Core Join Points

*Basis: normative + source + derived.*

#### 4.1 Classical Equivalence vs. Optimization Ergonomics

Kelsey (IR '95, DOI `10.1145/202529.202532`) and Appel (SIGPLAN Notices 1998, DOI `10.1145/278283.278285`) proved that SSA basic blocks correspond to lexically nested, tail-called functions (ANF) or continuations (CPS), with the SSA dominator tree matching lexical scope nesting and $\phi$/block arguments matching formal parameters. In practice, however, **ANF**, **CPS**, and **Direct Style with Join Points** behave very differently under inlining, commuting conversions, and lazy evaluation.

#### 4.2 ANF's Non-Closure Under β and Kennedy's Second-Class CPS (`ICFP '07`)

Kennedy (*Compiling with Continuations, Continued*, ICFP '07, §1.2, §2.4, §4–5) established why ANF (Flanagan et al. 1993) is brittle as an optimizer IR:
- **Not closed under β-reduction (§2.4):** Because ANF constrains `let x = R in A` to atomic computations `R`, inlining $(\lambda x. A)\, v \to A[v/x]$ inside a `let` RHS breaks ANF, forcing repeated `CC-LET`/`CC-CASE` commuting re-normalization that causes quadratic blowup on linear reductions and lacks explicit join points to prevent code duplication.
- **Second-class continuations (`letcont`) & O(1) shrinking reductions (§2, §4.1):** Kennedy's `λ_CPS` syntactically separates heap-allocatable functions (`letval`) from stackless local continuations (`letcont`), backed by a doubly-linked term graph with per-binder free-occurrence lists so shrinking reductions run in $O(1)$.
- **Local optimal contification (§5.1):** Because every call passes a continuation argument explicitly, converting a function `f` to a zero-allocation `letcont j` reduces to checking whether all call sites pass the same continuation `k0`, substituting `k0/k`, and sinking `j` into `k0`'s scope (`CONT` rule). Iterating this local rule matches Fluet & Weeks' (2001) optimal dominator-tree contification.

#### 4.3 System $F_J$ and Production GHC Core Join Points (`Maurer et al. PLDI '17`; `ghc/ghc@83038fbe`)

Maurer, Downen, Ariola & Peyton Jones (PLDI '17, §2, §7–9) explained why GHC rejected full CPS and instead extended direct-style Core with explicit **join points**:

- **Why full CPS hurts GHC (Maurer et al. §8):** (1) CPS fixes evaluation order, blocking GHC's aggressive pure `let`-floating and complicating call-by-need semantics; (2) CPS breaks syntactic CSE—`f (g x) (g x)` becomes `letcont k1 xv = letcont k2 yv = f k xv yv in g k2 x in g k1 x`, passing distinct continuations `k1`/`k2` to `g`; and (3) CPS disrupts source-level `{-# RULES #-}` matching nested calls such as `stream (unstream s) = s`.
- **Why direct-style `let` without join points fails (§2, §9):** Pushing an outer `case` through `let j x = BIG in case v of { A -> j 1; B -> j 2; C -> True }` turns `j 1` and `j 2` into non-tail calls `case (j 1) of ...`, simultaneously **forcing heap closure allocation for `j`** and duplicating the outer `case` onto uninformative calls instead of scrutinizing `BIG`. Without join points, commuting conversions are also order-sensitive (Benton et al.'s "useless function" problem).
- **System $F_J$ axioms (`Maurer et al. §7`; `ghc/ghc@83038fbe`, `compiler/GHC/Core.hs` L1020–1198):** Tagging a binder as `JoinId` with `JoinArity` (counting both type and value parameters) adds two Simplifier rules:
  ```haskell
  -- Before case-of-case (outer E[.] = case [.] of { True -> False; False -> True }):
  case (join j x = BIG in case v of { A -> jump j 1; B -> jump j 2; C -> True }) of ...
  -- After jfloat (push E into join RHS, update return type via adjustJoinPointType) + abort (E[jump j n] -> jump j n):
  join j x = case BIG of { True -> False; False -> True }
  in case v of { A -> jump j 1; B -> jump j 2; C -> case True of { True -> False; False -> True } }
  ```
- **Six `Core Lint`-checked invariants (`Core.hs` L1065–1145; `Lint.hs` L202–225, L534–1095):** (1) all occurrences are saturated tail calls of exact `JoinArity` (types + values); (2) for join arity $n$, the RHS and any unfolding begin with $\ge n$ bare lambdas (no casts/ticks); (3) recursive groups are homogeneous (all join points or none); (4) return type is not polymorphic; (5) *relaxed:* unboxed join points (`Int#`) need not be ok-for-speculation; (6) *relaxed:* join RHSes need not have a fixed `RuntimeRep`.
- **Production restriction vs. paper (`Core.hs` L1147–1165, `Note [Join points are less general than the paper]`):** PLDI '17's System $F_J$ permits `(case blah of { True -> j void#; False -> blah }) arg` via its $\Delta$ judgment; production GHC rejects this in `Core Lint`, requiring strict syntactic tail calls to simplify the Simplifier and backend.
- **NoFib allocation impact (Maurer et al. §7, Table 1):** Over a GHC baseline that already compiled backend-recognized join points without closures, preserving join points through Core optimization cut heap allocations by **-0.4% geomean on `spectral`** (to `-8.4%` on `solid`), **-0.2% geomean on `real`** (to `-4.7%` on `rsa`, with inlining-heuristic regressions up to `+3.6%` on `fem`), and **-100.0% on `shootout/n-body`** / **-85.9% on `shootout/k-nucleotide`**, enabling skip-less `unfoldr/destroy` stream fusion without brittle inlining cliffs. (Cong et al., ICFP '19, DOI `10.1145/3341643`, later showed how delimited continuations and answer-type polymorphism unify direct-style join points and CPS.)

---

### 5. Multi-Level Extensible IRs (`MLIR`): Regions, Speculatability Traits, and the Semantic-Erasure Cliff

*Basis: normative + documentation + source + derived.*

#### 5.1 Unified Operation/Region Substrate (`Lattner et al. CGO '21`; `llvm/llvm-project@f19509b0`)

MLIR replaces a single fixed opcode set with extensible dialects hosted over uniform `Operation`s containing zero or more `Region`s of block-argument `Block`s (`mlir/docs/LangRef.md` L353–644). `RegionKindInterface` (`RegionKindInterface.td` L1–67) distinguishes:
- **`RegionKind::SSACFG`** (`LangRef.md` L502–566): sequential basic blocks, Single-Entry-Multiple-Exit terminators, and **generalized hierarchical dominance** (inner ops may reference outer dominating values unless barred by `OpTrait::IsolatedFromAbove`, L472–500).
- **`RegionKind::Graph`** (`LangRef.md` L591–634): unordered concurrent/dataflow graphs where all region values are mutually in scope—permitting **cyclic value definitions** (hardware netlists, dataflow graphs), currently limited to a single basic block (L601–609).

Generic pass reuse across open dialects relies on four mechanisms (Lattner et al. §6.1): (1) **op traits** (`Commutative`, `IsolatedFromAbove`, `NoTerminator`), (2) **privileged hooks** (`fold`, `getCanonicalizationPatterns`), (3) **optimization interfaces** (`DialectInlinerInterface`, `MemoryEffectsOpInterface`, `ConditionallySpeculatable`), and (4) **dialect-specific passes**.

#### 5.2 Cross-Dialect Invariant Drift, Speculatability Splits, and Semantic Erasure

Inspecting `llvm/llvm-project@f19509b0` highlights three structural risks in open multi-level IRs:

1. **Trait/interface accuracy as the entire soundness boundary for generic passes:** MLIR's verifier checks structural syntax and dominance, not operational semantics. In `mlir/include/mlir/Interfaces/SideEffectInterfaces.td` (L26–156), MLIR explicitly splits:
   - `NoMemoryEffect` (L95–96): *"Op has no effect on memory **but may have undefined behavior**."*
   - `ConditionallySpeculatable` (L126–142): op-specific C++ `getSpeculatability()` check.
   - `Pure = TraitList<[AlwaysSpeculatable, NoMemoryEffect]>` (L153–155): *"Always speculatable operation that does not touch memory. These operations are always legal to hoist or sink."*

   In `mlir/include/mlir/Dialect/Arith/IR/ArithOps.td`, `Arith_AndIOp` (L853) is total `Pure`, `Arith_AddIOp` (L271–288) uses `nuw`/`nsw` flags that yield deferred **poison**, and `Arith_DivSIOp` / `Arith_DivUIOp` (L598–680) implement `ConditionallySpeculatable` (NOT `Pure`) because division by zero or `INT_MIN / -1` is immediate UB (including per-lane on vectors/tensors). Misdeclaring `Pure` on a trapping op silently introduces hoisting miscompiles in generic LICM/CSE; omitting interfaces forces conservative optimization barriers.
2. **Mixed-dialect conversion seams (`mlir/include/mlir/Transforms/DialectConversion.h` L1435–1555):** `applyPartialConversion` and `applyFullConversion` mediate type mismatches across coexisting dialects via `TypeConverter` materializations or `builtin.unrealized_conversion_cast` chains later folded by `reconcileUnrealizedCasts` (L1481–1501). Partially lowered mixed-dialect states create a combinatorial test surface, and transactional pattern rollback (`allowPatternRollback = true`, L1445–1464) adds driver complexity and overhead.
3. **The Semantic-Erasure Cliff:** Progressive lowering (`linalg`/`affine`/`scf` → `cf`/`llvm` → LLVM IR) is one-way: structured iteration bounds, no-alias tensor semantics, and domain invariants either disappear or survive only as droppable metadata. Lowering too early forfeits high-level tiling/vectorization; lowering too late blocks scalar canonicalization—re-creating phase ordering at the dialect level. Formal verification tools address slices of this gap—`IRDL` (Fehr et al., PLDI '22, DOI `10.1145/3519939.3523700`) specifies dialect constraints declaratively, *First-Class Verification Dialects for MLIR* (Fehr et al., PLDI '25, DOI `10.1145/3729309`) embeds SMT refinement checks, and `lean-mlir` mechanizes mostly memory-free dialects (see `mechanized-compiler-ir-semantics-poison-provenance-and-machine-frames`)—but upstream MLIR lacks end-to-end cross-dialect refinement certificates.

---

### 6. Phase Ordering, Acyclic E-Graphs (`Cranelift aegraphs`), and Comparative Verification Probe Results

*Basis: normative + documentation + source + execution + derived.*

#### 6.1 Phase-Ordering Limits and Cranelift's Acyclic E-Graph Architecture

Optimal pass ordering is undecidable in general (Touati & Barthou, CF '06, DOI `10.1145/1128022.1128042`), while combined optimistic analyses strictly dominate any finite pass sequence (Click & Cooper, TOPLAS 1995, DOI `10.1145/201059.201061`). Yet standalone cyclic equality saturation (`egg`) proved too heavy for Cranelift's JIT compile budget: Chris Fallin's initial `egg` prototype incurred **23% compile-time overhead with zero rewrites** (down from >2× initially) to replace a mid-end taking only **~10% of compile time** (Fallin, 2026-04-09).

Cranelift's shipped mid-end (`bytecodealliance/wasmtime@3ce22098`, `cranelift/codegen/src/egraph/`) instead implements a **transient Sea-of-Nodes-with-CFG-Skeleton + Acyclic E-Graph (`aegraph`)**:

1. **In-place `ValueData::Union`:** Pure ops (`is_pure_for_egraph`) are detached from the CFG `Layout` while side-effecting ops stay in the CFG skeleton (`egraph/mod.rs` L80–98). Multi-representation lives inside the existing SSA `Value` index space via `ValueData::Union { ty, x, y }` (`ir/dfg.rs` L693–709, L1097–1101)—zero copy cost for singleton e-classes.
2. **Single-pass domtree-preorder eager rewriting with hard bounds:** `EgraphBlockIter` visits the dominator tree in DFS pre-order (`egraph/mod.rs` L32–78), fusing scoped GVN, alias-analysis load forwarding, and ISLE multi-constructor rewrites. Append-only immutable union nodes (no global `rebuild`) preserve **strict acyclicity** by construction, bounded by hardcoded production caps (`egraph/mod.rs` L127–137, L391–393, L457): `MATCHES_LIMIT = 5`, `ECLASS_ENODE_LIMIT = 5`, `REWRITE_LIMIT = 5`, and `EXTRACTOR_FUEL = 500`.
3. **Dominance soundness (`available_block` and mandatory `subsume`):** Merging expressions with unequal dominance scopes (e.g., forwarding a block-local load to `iconst 0`, or `(select 1 x y) => x` where `y` is defined in a narrower block than `x`) would violate SSA dominance if an e-node referencing `y` were extracted in a sibling scope. Cranelift prevents this via `available_block: SecondaryMap<Value, Block>` (`egraph/mod.rs` L147, L328–343, L468) and **Rule 2 of `cranelift/codegen/src/opts/README.md` (L26–45)**: any rewrite dropping a non-constant operand from LHS to RHS **must** wrap its result in `subsume` (`egraph/mod.rs` L433–441), erasing prior e-class members.
4. **Tree-DP extraction and scoped elaboration:** Optimal e-graph extraction with shared subexpressions is NP-hard (Fallin 2026 reduces weighted set cover linearly to shared extraction). Cranelift ignores sharing via single-pass topological bottom-up DP (`egraph/cost.rs` L67–130: `Iconst`/`Uextend`/`Ireduce`=1, `Iadd`/`Band`/`Ishl`=3, default=4, `Imul`=10, trap/side-effect +10, load +20, store +50; 1024× per loop-nest level capped at depth 2; tie-break prefers rewritten e-nodes, `elaborate.rs` L117–120). `Elaborator` (`elaborate.rs` L20–120) then lowers pure nodes back into CFG blocks via an O(1) generation-stamped `ScopedHashMap`, fusing GVN, demand-driven DCE, LICM, and constant rematerialization (noting that demand-driven sinking can occasionally duplicate an expression across sibling branches).

#### 6.2 Fallin's (2026) Sightglass Ablation Results

| Measurement (Fallin 2026-04-09, Sightglass Wasm Benchmarks) | Observed Value | Interpretation |
|---|---|---|
| Standalone `egg` zero-rewrite round-trip overhead | **23%** (initial **>2×**) | Exceeds ~10% total compile-time share of Cranelift's mid-end before any rewrite runs. |
| Full `aegraph` vs. classical CFG pipeline (execution speed) | **~2% faster** | Unmatched even by repeating the classical pipeline 2×–3×; validates fused fine-grained pass interaction. |
| Full `aegraph` vs. classical CFG pipeline (compile time) | **+7–8%** | Grew from ~parity in 2023 as hundreds of ISLE rules accumulated. |
| **`aegraph` vs. `no multivalue` (eager pick, no union nodes)** | **~0.1% faster** (+**~0.005%** compile time) | Multi-representation + cost extraction is near noise on pre-optimized Wasm with directional simplifying rules. |
| Average e-class size after rewriting | **1.13 e-nodes** | Rulesets omit AC/non-simplifying identities (`opts/README.md` Rule 3), leaving most e-classes singletons. |
| Eager non-saturation misses across ~4M value nodes | **2 instances** (`spidermonkey.wasm`) | Both caused by one `ireduce`-of-`iadd` rule intentionally breaking cost monotonicity. |

**Architectural conclusion:** Cranelift's production gain comes from **transient Sea-of-Nodes-with-CFG-Skeleton + fused single-pass rewriting + scoped elaboration**, not equality saturation. Fallin identifies RVSDG (e.g., the `optir` prototype) as the principled path to extend this framework to CFG-mutating rewrites. For cyclic proof-producing equality saturation (`egg`/`egglog`), see `equality-saturation-with-proofs-egraphs-aegraphs-and-refinement-rewriting`.

#### 6.3 Comparative Verification Probe Results (`support/verify_ir_transformations.py`)

`support/verify_ir_transformations.py` translates an effectful diamond+loop kernel (`while i < n: inv = a*2+1; if b != 0 { q = (a+inv)/b; mem[0]+=q; step=q+inv } else { inv2 = a*2+1; mem[1]+=inv2; step=inv2 }`) across CFG SSA, pinned/unpinned Sea-of-Nodes, and RVSDG (`gamma`/`theta`), verifying exact value and store-trace equivalence across 6 test vectors (including `b=0, n=3` and zero-trip `b=0, n=0`), plus irreducible-loop restructuring and aegraph invariants (exit `0`):

| Probe Component | Observed Invariants & Outcomes | Verified Property |
|---|---|---|
| **Block-Arg CFG SSA** | `7` blocks, `20` insts, `6` block params; GVN eliminated `2` ops; LICM hoisted `4` pure ops, blocked `1` trapping `sdiv`; needed `2` CFG analyses (`DomTree`, `NaturalLoopInfo`); **6/6 exact equivalence**. | Explicit block-arg dominance verification + loop analysis keep `sdiv` guarded while hoisting `inv`. |
| **Sea-of-Nodes (Pinned `SDiv`)** | `40` nodes: **`24` CFG/effect/guard-pinned (60%)** + `6` start-bound params/consts (15%) vs. **`10` truly floating pure nodes (25%)**; `2` automatic GVN hits; GCM places `inv1` in `bb_entry`, keeps `SDiv` in `bb_then`; dead `else` folding touches **`6` nodes**; **6/6 exact equivalence**. | Quantifies V8's effect/control saturation in an effectful kernel while confirming free GVN/LICM when guard pins hold. |
| **Sea-of-Nodes (Unpinned `SDiv` Bug)** | Dropping `SDiv.control_in` floats `SDiv` to **`bb_entry`**, triggering **`2` spurious `div_by_zero` traps** on `(10, 0, 3, 1, 5)` and `(10, 0, 0, 7, 9)`. | Reproduces the HotSpot C2 / TurboFan lost-control-dependency miscompile class (`castnode.hpp` L114–123). |
| **RVSDG (`Gamma`/`Theta`)** | `29` nodes in `6` acyclic regions (`lambda` → `gamma(n>0)` → `theta` → `gamma(b!=0)`); `DNE` removed `1` dead node; `PSH` hoisted `6` pure ops from `theta`, blocked `1` trapping `sdiv` inside `gamma`; **`0` CFG analyses**; **6/6 exact equivalence** with checked linear state tokens. | Region structure preserves dominance, loop scope, and guard barriers without dominator trees or loop finders. |
| **Irreducible CFG Restructuring** | 2-entry irreducible loop (`L1 <-> L2`): `0` duplicated body blocks, `2` synthetic predicates (`#q`, `#r`), 18/18 equivalence, dynamic branches **`67 → 165` (`2.463×`)**. | Confirms linear code-size guarantee traded against synthetic predicate dispatch overhead. |
| **Cranelift `aegraph` Invariants** | Shared-DAG (`v0=union(v10,v11)`, `v1=union(v10,v12)`, costs `10,7,7`): tree DP = **`14`** vs. DAG optimum = **`10`**; dropping `%y` in `select(1,%x,%y)=>%x` is illegal (`false`) in sibling `bb2` without `subsume`, legal (`true`) with `subsume`. | Mechanically confirms Fallin's weighted-set-cover extraction gap and `opts/README.md` Rule 2 dominance soundness. |

## Boundaries

- **not examined (local native benchmarking):** Performance, L1 dcache, allocation, and compile-time measurements for V8, `jlm`, GHC, and Cranelift are sourced verbatim from their primary retrospectives and peer-reviewed evaluations rather than re-executed locally on compiled upstream binaries.
- **not examined (post-2020 `jlm` alias-splitting vs. LLVM `MemorySSA`):** Reissmann et al. (TECS 2020 §7.3) documented single-state-edge over-serialization on `syrk`; newer points-to state-edge splitting evaluations across `llvm-test-suite` were not examined.
- **unknown (Cranelift `aegraph` multi-representation value on unoptimized frontends):** Whether the ~0.1% multi-representation gain and 1.13 average e-class size grow materially on non-Wasm frontends (e.g., `rustc_codegen_cranelift`) or expanded algebraic rulesets is left open by Fallin (2026-04-09).
- **unknown (multi-year miscompile shares in LLVM/JDK trackers):** Exact issue-tracker percentages for stale-`PreservedAnalyses` miscompiles or JDK lost-control-dependency bugs (2015–2026) were not tabulated; only the structural mechanisms are verified.
- **known not to apply (V8's Sea-of-Nodes conclusions to pure/typed expression IRs):** V8's retreat reflects dynamic JavaScript's extreme effect/guard density and JIT latency budget. Those trade-offs do not apply identically to pure expression DAGs, hardware graph regions, or statically typed IRs with fine-grained memory slices (HotSpot C2 retains Sea-of-Nodes; Cranelift's transient sea-of-nodes for *pure* ops over a CFG skeleton succeeds).
- **unsupported (multi-block MLIR `Graph` regions):** At `llvm/llvm-project@f19509b0` (`mlir/docs/LangRef.md` L601–609), `RegionKind::Graph` supports only a single basic block.
- **unsupported (exceptions and intrinsics in evaluated `jlm` RVSDG):** Reissmann et al. (TECS 2020 §7.1) explicitly mark exceptions and LLVM intrinsics unsupported in the evaluated `jlm` pipeline.
- **unsupported (non-tail join-point calls in production GHC Core):** Unlike PLDI '17's System $F_J$ ($\Delta$ judgment), production GHC (`ghc/ghc@83038fbe`, `Core.hs` L1147–1165) rejects non-tail join calls in `Core Lint`.

## Evidence

All technical evidence below was acquired and verified on `2026-11-19`.

### Pinned GitHub Source Inspections

1. **`v8/v8` @ `e88118f63dd96f24a9acb8bd0665e7880063f5c0`:**
   - `src/compiler/turboshaft/graph.h` L33–115 (`OperationBuffer`, 8-byte `OperationStorageSlot`, `ReplaceScope`); `copying-phase.h` L52–101 (`OutputGraphAssembler`, `GraphVisitor`); `pipelines.cc` L28–32, L178–199; `turbolev-frontend-pipeline.cc` L48–105; `value-numbering-reducer.h` L1–100.
   - `src/flags/flag-definitions.h` L1722 (`turboshaft = true`), L1737, L1795 (`turbolev = false`); `src/compiler/pipeline.cc` L795–821, L2500, L3230–3248 (`CreateGraphFromTurbofan`).
   - `src/compiler/node.h` L82–270, L466–553 (`Use*` lists, inline/outline `ZoneNodePtr`); `src/compiler/scheduler.h` L31–149 (`kSplitNodes`, `Placement`, `ScheduleEarly`/`ScheduleLate`).
2. **`openjdk/jdk` @ `4f33273115381cd7697082fcb1bb2642dae19043`:**
   - `src/hotspot/share/opto/castnode.hpp` L34–154 (`ConstraintCastNode::DependencyType` 4-state lattice & single-control-edge comments).
   - `src/hotspot/share/opto/gcm.cpp` L304–350 (`schedule_early`), L805–860 (`MergeMem`/store anti-dependence search), L1545–1600 (`schedule_late`).
3. **`oracle/graal` @ `3fd1dcaa85129cc6df8232487f9506d73787a755`:**
   - `compiler/src/jdk.graal.compiler/src/jdk/graal/compiler/nodes/{FixedNode.java,FixedWithNextNode.java,calc/FloatingNode.java,FloatingGuardedNode.java,FloatingAnchoredNode.java}`.
   - `.../nodes/{GuardNode.java L49–95, FixedGuardNode.java L40–100, PiNode.java L76–95, StateSplit.java L40–52, FrameState.java L69–120}`; `.../phases/schedule/SchedulePhase.java` L107–202, L403, L1035.
4. **`phate/jlm` @ `b6d2582a87b180a2d60f9eb06652cff17448618a`:**
   - `jlm/rvsdg/{region.hpp L32–80, structural-node.hpp, gamma.hpp L64–98, theta.hpp L32–125, lambda.hpp L82–138, Phi.hpp L45–99}`.
   - `jlm/llvm/frontend/ControlFlowRestructuring.{hpp,cpp}` L1–100 (`RestructureLoops`, `RestructureBranches`, `#p`/`#q`/`#r` variables).
5. **`ghc/ghc` @ `83038fbee5efea8e3ebd5090b2ff5537462e169d`:**
   - `compiler/GHC/Core.hs` L1020–1198 (`Note [Join points]`, `Note [Invariants on join points]`, `Note [Join points are less general than the paper]`, `Note [The type of a join point]`).
   - `compiler/GHC/Core/Lint.hs` L202–225, L534–555, L628–675, L928–950, L1033–1095 (`lintJoinLams`, `checkJoinOcc`, `lintJoinBndrType`).
6. **`llvm/llvm-project` @ `f19509b0393bc186173b51fe2c9bce751e8d63e6`:**
   - `mlir/docs/LangRef.md` L353–644 (block arguments, `SSACFG` vs. single-block `Graph` regions, `IsolatedFromAbove`); `mlir/include/mlir/IR/RegionKindInterface.td` L1–67.
   - `mlir/include/mlir/Interfaces/SideEffectInterfaces.td` L26–156 (`NoMemoryEffect`, `ConditionallySpeculatable`, `Pure`); `mlir/include/mlir/Dialect/Arith/IR/ArithOps.td` L271–288, L598–680, L853.
   - `mlir/include/mlir/Transforms/DialectConversion.h` L1435–1555 (`unrealized_conversion_cast`, `reconcileUnrealizedCasts`, `allowPatternRollback`, `applyPartialConversion`/`applyFullConversion`).
7. **`bytecodealliance/wasmtime` @ `3ce2209872ccf1ea115914a81e020aef66a10c51`:**
   - `cranelift/codegen/src/egraph/mod.rs` L32–169, L229–260, L328–486 (`EgraphBlockIter`, `MATCHES_LIMIT=5`, `ECLASS_ENODE_LIMIT=5`, `REWRITE_LIMIT=5`, `EXTRACTOR_FUEL=500`, `available_block`, `subsume_values`).
   - `cranelift/codegen/src/egraph/elaborate.rs` L1–120; `cost.rs` L1–179; `ir/dfg.rs` L693–709, L1097–1101 (`ValueData::Union`); `opts/README.md` L1–105 (Rules 1–4).

### Verified Primary Papers & Engineering Retrospectives

- Click & Paleczny (1995), *A Simple Graph-Based Intermediate Representation*, IR '95, pp. 35–49, DOI `10.1145/202529.202534`.
- Click (1995), *Global Code Motion / Global Value Numbering*, PLDI '95, pp. 246–257, DOI `10.1145/207110.207154`.
- Click & Cooper (1995), *Combining Analyses, Combining Optimizations*, ACM TOPLAS 17(2), pp. 181–196, DOI `10.1145/201059.201061`.
- Kelsey (1995), *A Correspondence between Continuation Passing Style and Static Single Assignment Form*, IR '95, pp. 13–22, DOI `10.1145/202529.202532`.
- Appel (1998), *SSA is Functional Programming*, ACM SIGPLAN Notices 33(4), pp. 17–20, DOI `10.1145/278283.278285`.
- Touati & Barthou (2006), *On the Decidability of Phase Ordering Problem in Optimizing Compilation*, CF '06, pp. 147–156, DOI `10.1145/1128022.1128042`.
- Kennedy (2007), *Compiling with Continuations, Continued*, ICFP '07, pp. 177–190, DOI `10.1145/1291151.1291179`.
- Duboscq et al. (2013), *An Intermediate Representation for Speculative Optimizations in a Dynamic Compiler*, VMIL '13, pp. 1–10, DOI `10.1145/2542142.2542143`.
- Bahmann, Reissmann, Jahre & Meyer (2015), *Perfect Reconstructability of Control Flow from Demand Dependence Graphs*, ACM TACO 11(4), Article 59, pp. 1–25, DOI `10.1145/2693261`.
- Maurer, Downen, Ariola & Peyton Jones (2017), *Compiling Without Continuations*, PLDI '17, pp. 482–494, DOI `10.1145/3062341.3062380`.
- Cong, Osvald, Essertel & Rompf (2019), *Compiling with Continuations, or without? Whatever.*, PACMPL (ICFP '19), DOI `10.1145/3341643`.
- Reissmann, Meyer, Bahmann & Själander (2020), *RVSDG: An Intermediate Representation for Optimizing Compilers*, ACM TECS 19(6), pp. 1–28, DOI `10.1145/3391902` (arXiv:1912.05036).
- Lattner et al. (2021), *MLIR: Scaling Compiler Infrastructure for Domain Specific Computation*, CGO '21, pp. 2–14, DOI `10.1109/CGO51591.2021.9370308` (arXiv:2002.11054).
- Fehr et al. (2022), *IRDL: An IR Definition Language for SSA Compilers*, PLDI '22, DOI `10.1145/3519939.3523700`.
- Fehr et al. (2025), *First-Class Verification Dialects for MLIR*, PACMPL (PLDI '25), DOI `10.1145/3729309`.
- Mercadier (2025-03-25), *Land ahoy: leaving the Sea of Nodes*, `https://v8.dev/blog/leaving-the-sea-of-nodes`.
- Fallin (2026-04-09), *The acyclic e-graph: Cranelift's mid-end optimizer*, `https://cfallin.org/blog/2026/04/09/aegraph/`.

### Preserved Support Material & Execution Transcript

- **Script:** `support/verify_ir_transformations.py` (Python 3.10+, stdlib only).
- **Command:** `python3 -B reports/compiler-ir-architectures-sea-of-nodes-rvsdg-cps-and-mlir/support/verify_ir_transformations.py` (exit `0`, Linux x86_64, `2026-11-19`):

```json
{
  "aegraph_invariants": {"dag_optimal_cost": 10, "no_subsume_legal_in_sibling_block": false, "tree_dp_cost": 14, "with_subsume_legal_in_sibling_block": true},
  "cfg_ssa": {"block_params": 6, "blocks": 7, "gvn_eliminated": 2, "insts": 20, "licm_blocked_trapping": 1, "licm_hoisted": 4, "required_analyses": 2},
  "irreducible_cfg_restructuring": {"duplicated_body_blocks": 0, "dynamic_branch_ratio": 2.463, "dynamic_branches_original": 67, "dynamic_branches_restructured": 165, "equivalence_verified": true, "synthetic_predicate_vars": 2},
  "rvsdg": {"dne_removed": 1, "psh_blocked_trapping_in_gamma": 1, "psh_hoisted_from_theta": 6, "required_cfg_analyses": 0, "total_nodes": 29, "total_regions": 6},
  "sea_of_nodes_pinned": {"cfg_effect_or_guard_pinned_nodes": 24, "dead_else_branch_son_nodes_to_patch": 6, "div_block": "bb_then", "gvn_hits": 2, "inv1_block": "bb_entry", "start_bound_params_and_consts": 6, "total_nodes": 40, "truly_floating_pure_nodes": 10},
  "sea_of_nodes_unpinned_bug": {"div_scheduled_block": "bb_entry", "spurious_traps_observed": 2},
  "test_vectors_checked": 6
}
```

## Revalidation

1. **Re-run the comparative probe:** `python3 -B reports/compiler-ir-architectures-sea-of-nodes-rvsdg-cps-and-mlir/support/verify_ir_transformations.py` (exit `0` reconfirms CFG/Sea-of-Nodes/RVSDG equivalence, unpinned-division trap reproduction, irreducible restructuring ratio, and aegraph extraction/`subsume` invariants).
2. **V8 Sea-of-Nodes exit status (`v8/v8`):** Inspect `DEFINE_BOOL(turbolev, ...)` in `src/flags/flag-definitions.h` and callers of `CreateGraphFromTurbofan` in `src/compiler/pipeline.cc` to check whether the remaining Sea-of-Nodes JS frontend has been retired.
3. **HotSpot C2 guard pinning (`openjdk/jdk`):** Diff `ConstraintCastNode::DependencyType` in `src/hotspot/share/opto/castnode.hpp`.
4. **Graal hybrid guards (`oracle/graal`):** Diff `GuardNode.java`, `PiNode.java`, and `SchedulePhase.java` (`SchedulingStrategy`).
5. **GHC Core join-point invariants (`ghc/ghc`):** Diff `Note [Invariants on join points]` and `Note [Join points are less general than the paper]` in `compiler/GHC/Core.hs`.
6. **MLIR region kinds & speculatability (`llvm/llvm-project`):** Diff `mlir/docs/LangRef.md` (`### Graph Regions`), `mlir/include/mlir/Interfaces/SideEffectInterfaces.td` (`Pure` vs. `NoMemoryEffect`), and `mlir/include/mlir/Transforms/DialectConversion.h`.
7. **Cranelift aegraph bounds & ablations (`bytecodealliance/wasmtime`):** Diff `MATCHES_LIMIT`/`ECLASS_ENODE_LIMIT`/`REWRITE_LIMIT`/`EXTRACTOR_FUEL` in `cranelift/codegen/src/egraph/mod.rs` and Rule 2 in `cranelift/codegen/src/opts/README.md`. Checking whether multi-representation exceeds ~0.1% on non-Wasm frontends (`rustc_codegen_cranelift`) requires running fresh `aegraph` vs. `no multivalue` A/B benchmarks on that workload.
