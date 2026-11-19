# Hypergraph Partitioning, Bounded-Treewidth Decompositions, and PBQP Compiler Lowering

## Summary

Four parameterized graph-theoretic and combinatorial optimization frameworks govern how modern compilers, static analyzers, and distributed code/tensor placement engines overcome classical NP-completeness without sacrificing precision or scalability:

1. **SSA Interference Chordality Decouples Coloring From NP-Hard Spilling and Coalescing:** The interference graph of a strict Static Single Assignment (SSA) program is the intersection graph of connected subtrees of its dominator tree and is therefore **chordal**, satisfying $\chi(G) = \omega(G) = \text{MaxLive}$ and admitting optimal greedy coloring in a single preorder dominator-tree walk (`libfirm/ir/be/bechordal.c`). However, **spilling, copy coalescing, and irregular register aliasing remain NP-complete**; naive $\phi$-coalescing destroys chordality and can introduce chordless odd cycles (e.g., $C_5$ where $\omega = 2$ but $\chi = 3$), forcing otherwise unnecessary spills.
2. **Bounded CFG Treewidth Enables Polynomial-Time Exact Lowering Without SSA:** By Thorup's theorem, `goto`-free structured control-flow graphs have small constant treewidth ($\text{tw} \le 3$ for Algol/Pascal, $\le 5$ for Modula-2, $\le 6$ for C—corresponding to maximum tree-decomposition bag size $\le 7$). Krause's dynamic programming algorithm exploits bounded CFG treewidth to solve global register allocation **optimally** in time linear in program size (with exponential dependence on bag width and register count), natively capturing register aliasing, spilling, rematerialization, and coalescing without requiring SSA chordality.
3. **PBQP Encodes Irregular Register Pairs, Aliasing, and Microarchitectural Bank Exclusion:** Partitioned Boolean Quadratic Programming (PBQP) generalizes graph coloring by attaching cost vectors to nodes and arbitrary cost matrices to edges (`llvm/include/llvm/CodeGen/PBQP/ReductionRules.h`, `llvm/lib/CodeGen/RegAllocPBQP.cpp`, `llvm/lib/Target/AArch64/AArch64PBQPRegAlloc.cpp`). Reduction rules $R_0, R_1, R_2$ solve PBQP **exactly in polynomial time on graphs of treewidth $\le 2$** (series-parallel graphs), whereas graphs of treewidth $\ge 3$ (e.g., $K_4$) trigger heuristic $R_N$ elimination. In LLVM's `RegAllocSolverImpl`, `SpillCostComparator` compares only raw spill cost `NodeCosts[0]` when picking an $R_N$ victim, ignoring register-preference/coalescing vectors and causing measurable suboptimality gaps on $K_4$ instances.
4. **Scalable $n$-Level and Deterministic Hypergraph Partitioning (`Mt-KaHyPar`) Replaces Distorted Graph Cuts:** Pairwise clique expansions cannot faithfully represent hypergraph cut or $(\lambda - 1)$ connectivity for hyperedges of cardinality $|e| \ge 4$, causing ranking inversions in LTO code-island sharding, VLSI placement, and distributed SPMD tensor partitioning. `kahypar/mt-kahypar` combines $n$-level parallel coarsening, localized $k$-way Fiduccia–Mattheyses (FM), parallel HyperFlowCutter (`WHFC`) max-flow min-cut refinement, Steiner-tree process mapping (up to 64 target nodes directly, or recursively for larger meshes), fixed-vertex pinning, and deterministic parallel presets (`Jet` + deterministic flows). Direct source inspection also revealed an upstream dispatch defect in `mt-kahypar/partition/metrics.cpp:187`, where single-edge `contribution(..., Objective::cut)` erroneously delegates to `Objective::soed`.

## Applicability

This report synthesizes primary theoretical results, direct upstream source inspection, and standalone executable verification across three pinned open-source implementations and nine peer-reviewed publications:

- **Compiler Register Allocation & Lowering Implementations:**
  - `libfirm/libfirm` @ `114012d1d93427e63ba2f2ab51318e8a1b92f06c` (`ir/be/bechordal.c`, `ir/be/bechordal_common.c`): applies to SSA-based backends performing decoupled spill-then-color chordal allocation with `Perm`-based constraint legalization.
  - `llvm/llvm-project` @ `bdb0780cba671428363088c4f11e0575f14b6671` (`llvm/include/llvm/CodeGen/PBQP/ReductionRules.h`, `llvm/include/llvm/CodeGen/RegAllocPBQP.h`, `llvm/lib/CodeGen/RegAllocPBQP.cpp`, `llvm/lib/Target/AArch64/AArch64PBQPRegAlloc.cpp`): applies to LLVM's `-regalloc=pbqp` pipeline (post-PHI-elimination `MachineFunctionPass`, with `-pbqp-coalescing` defaulting to `false`).
  - Theoretical bounds from Thorup (1998), Hack–Grund–Goos (2006), Bouchez–Darte–Guillon–Rastello (2006), Krause (2013), Scholz–Eckstein (2002), and Hames–Scholz (2006): apply to structured CFGs, strict SSA IRs, and arbitrary binary quadratic cost formulations, respectively.
- **Hypergraph Partitioning & Topology-Aware Sharding:**
  - `kahypar/mt-kahypar` @ `44332540ecd08a9fd63a38fd8e8ac47a2c73b6fc` (`include/mtkahypartypes.h`, `include/mtkahypar.h`, `mt-kahypar/partition/context_enum_classes.h`, `mt-kahypar/partition/metrics.cpp`, `mt-kahypar/partition/refinement/flows/flow_refiner.cpp`, `config/highest_quality_preset.ini`, `config/deterministic_preset.ini`): applies to shared-memory parallel balanced $k$-way partitioning and target-graph process mapping using `oneTBB`, evaluated across hypergraphs (hMetis) and plain graphs (Metis).
  - Applies to link-time code-island decomposition (isolating local alignment/errata re-optimization budgets), sparse matrix-vector (`SpMV`) decomposition, VLSI netlists, and SPMD distributed tensor/operator mesh sharding.

**Relationship Among Subjects:** The three compiler frameworks (`libFirm`, `LLVM PBQP`, and Krause's treewidth DP) represent a structural-tractability spectrum trading IR invariants (SSA chordality vs. CFG treewidth $\le 6$ vs. interference-graph treewidth $\le 2$) against constraint expressiveness (uniform $k$-coloring vs. aliasing/parity/share-exclusion quadratic costs). `Mt-KaHyPar` operates one architectural layer above intra-procedural register allocation—partitioning whole-program call/symbol/data hypergraphs or tensor computation graphs into balanced, low-communication islands whose internal lowering problems remain small and perturbation-isolated.

## Findings

### 1. SSA Interference Chordality and the Boundaries of Polynomial-Time Coloring

Basis: normative (Hack, Grund, Goos, CC 2006, DOI `10.1007/11687637_19`; Bouchez et al., LCPC 2006, DOI `10.1007/978-3-540-72521-3_21`) + source (`libfirm/libfirm` @ `114012d1d93427e63ba2f2ab51318e8a1b92f06c`, `ir/be/bechordal.c`, `ir/be/bechordal_common.c`) + execution (`Probe 1A`).

#### 1.1 Subtree Intersection Theorem and Dominance-Tree Coloring

In a strict SSA program (every use is dominated by its unique definition, with $\phi$-functions evaluated simultaneously on block entry edges), the set of program points where an SSA value $v$ is live induces a **connected subtree** $T_v$ of the CFG's dominator tree $T_{\text{dom}}$ rooted at $\text{def}(v)$. By Gavril's characterization of chordal graphs (every chordal graph is the intersection graph of subtrees of a tree, and conversely), the SSA interference graph $G_{\text{SSA}} = (V, E)$—where $(u, v) \in E \iff T_u \cap T_v \neq \emptyset$—is strictly **chordal** (triangulated: every cycle of length $\ge 4$ has a chord).

Consequences for register allocation:

1. **Perfectness and Exact Coloring Threshold:** Because every chordal graph is perfect, its chromatic number equals its clique number:
   $$\chi(G_{\text{SSA}}) = \omega(G_{\text{SSA}}) = \max_{p \in \text{CFG}} |\text{Live}(p)| = \text{MaxLive}$$
   A valid $k$-coloring exists without spilling if and only if $\text{MaxLive} \le k$.
2. **Zero-Backtracking Linear-Time Coloring via Dominator Preorder:** Reversing a preorder traversal of the dominator tree (coupled with reverse instruction order within each basic block) yields a **Perfect Elimination Ordering (PEO)** of $G_{\text{SSA}}$. Coloring vertices in the reverse of a PEO (i.e., forward preorder over $T_{\text{dom}}$, forward instruction order per block) guarantees that every vertex's already-colored neighbors form a clique; hence greedy first-fit assignment is provably optimal and never backtracks.
3. **Decoupled Allocation Pipeline:** SSA chordality separates global register allocation into three independent stages:
   - **Spilling:** Lower $\text{MaxLive}$ to $\le k$ everywhere (e.g., via Belady-style farthest-next-use or loop-aware spilling).
   - **Coloring:** Assign registers in one dominator-tree walk without failing.
   - **Post-Coloring Coalescing & SSA Destruction:** Recolor non-interfering $\phi$-related webs conservatively (e.g., parallel-copy lowering and recoloring) without ever creating new spills.

#### 1.2 Direct Source Evidence in `libFirm` (`bechordal.c`)

Inspection of Sebastian Hack's chordal allocator in `libfirm/libfirm` (`ir/be/bechordal.c:327-395`, `ir/be/bechordal_common.c:42-158`) confirms the exact production mechanics and where pure chordality breaks on real ISAs:

- `be_ra_chordal_color` (`bechordal.c:377-395`) runs three `dom_tree_walk_irg` traversals:
  1. `constraints` (`bechordal.c:319-325, 173-310`): Before any instruction with register targeting constraints (such as x86 fixed `RAX`/`RDX` operands or two-address destructive operands), `pre_process_constraints` (`bechordal_common.c:118-158`) inserts a `Perm` node over all live-through values. `handle_constraints` greedily pairs dead inputs with outputs (`pair_up_operands`, lines 98-171) and solves a local bipartite matching (`bipartite_matching` or optional `hungarian_solve`, lines 197-283) to assign legal registers while maintaining SSA pressure invariants.
  2. `create_borders` (`bechordal_common.c:42-116`): Scans each block backwards from live-outs (`be_lv_state_end`), recording interval end-borders (`use`) and start-borders (`def`), finishing with block live-ins so live-ins precede all $\phi$-defs.
  3. `assign` (`bechordal.c:327-375`): Walks the per-block border list in dominator preorder; frees register bits on uses (`bitset_set`) and allocates `get_next_free_reg(available)` on defs (`bitset_clear`), asserting that every live-in already received a register from its dominator (`assert(b->is_real || reg)`, line 359).
- **Documented Source Limitation (`bechordal_common.c:148-150`):** `pre_process_constraints` explicitly notes that propagating limited register constraints onto `Perm` outputs breaks when a single SSA value feeds multiple differently constrained inputs of the same instruction—exposing the boundary where pure chordal coloring requires explicit copy splitting or a quadratic/ILP formulation.

#### 1.3 Why Chaitin's NP-Completeness Survives SSA

Bouchez, Darte, Guillon, and Rastello (LCPC 2006) proved that Chaitin's reduction from general graph $k$-coloring relies on non-SSA programs, and that under strict SSA the complexity shifts rather than disappears:

| Subproblem | General (Non-SSA) Graph | Strict SSA (Chordal) Graph | Root Cause of Intractability |
| :--- | :--- | :--- | :--- |
| Spill-free $k$-coloring (uniform registers) | NP-complete | **Polynomial** ($O(|V| + |E|)$) | Chordality: $\chi(G) = \omega(G) = \text{MaxLive}$ |
| Minimum-cost spilling (lowering $\text{MaxLive} \le k$) | NP-complete | **NP-complete** | Weighted interval/subtree selection with reload/rematerialization costs across control merges |
| Aggressive / optimal copy ($\phi$) coalescing | NP-complete | **NP-complete** | Merging non-interfering endpoints destroys chordality and can raise $\chi(G) > \omega(G)$ |
| Coloring with pre-colored nodes / irregular register classes (pairs/aliasing) | NP-complete | **NP-complete** | List coloring and interval-width (multi-register) coloring are NP-complete even on interval/chordal graphs |

**Execution Verification (`Probe 1A`):** Constructing a 6-variable SSA path intersection graph (`v0..v5`, each live on consecutive pairs of dominator nodes) confirms `chordal=True`, $\omega(G) = 2$, and $\chi(G) = 2$ via reverse-PEO coloring. Contracting the non-interfering endpoints `(v0, v5)` across a $\phi$-copy induces the chordless 5-cycle $C_5$, yielding `chordal=False`, $\omega(G') = 2$, and $\chi(G') = 3$—forcing a spill on a 2-register machine even though local pressure never exceeded 2.

---

### 2. Bounded CFG Treewidth and Polynomial-Time Optimal Allocation

Basis: normative (Thorup, Inf. Comput. 1998, DOI `10.1006/inco.1997.2697`; Krause, CC 2013, DOI `10.1007/978-3-642-37051-9_1`) + execution (`Probe 1B`).

#### 2.1 Treewidth Definitions and Thorup's Structured CFG Bounds

A **tree decomposition** of an undirected graph $G = (V, E)$ is a pair $(T, \{X_t\}_{t \in V(T)})$ where $T$ is a tree and each **bag** $X_t \subseteq V$ satisfies:

1. **Vertex coverage:** $\bigcup_{t \in V(T)} X_t = V$.
2. **Edge coverage:** For every $(u, v) \in E$, there exists $t \in V(T)$ with $\{u, v\} \subseteq X_t$.
3. **Running intersection (connectivity):** For every $v \in V$, the subgraph of $T$ induced by $\{t \in V(T) \mid v \in X_t\}$ is connected.

The **width** of the decomposition is $\max_{t \in V(T)} |X_t| - 1$, and the **treewidth** $\text{tw}(G)$ is the minimum width over all valid tree decompositions. Crucially, **treewidth $w$ corresponds to maximum bag size $w + 1$**—an off-by-one distinction that occasionally causes literature citations to conflate $\text{tw} \le 6$ with bag size $\le 7$.

Thorup (1998) proved via structural induction over abstract syntax trees (tracking active entry, exit, break, continue, and return control-flow ports as separator vertices) that `goto`-free structured control-flow graphs have constant treewidth bounded strictly by language control-flow primitives:

| Language / Control-Flow Subset | CFG Treewidth Upper Bound $\text{tw}(G_{\text{CFG}})$ | Max Bag Size $|X_t|$ | Distinguishing Control-Flow Constructs |
| :--- | :---: | :---: | :--- |
| Algol / Pascal (`goto`-free) | $\le 3$ | $\le 4$ | Single-entry/single-exit blocks, `if-then-else`, `while`/`repeat`/`for`, `case` without fallthrough |
| Modula-2 (`goto`-free) | $\le 5$ | $\le 6$ | Adds multi-exit `LOOP`/`EXIT` and `RETURN` |
| C (`goto`-free) | $\le 6$ | $\le 7$ | Adds `break`, `continue`, `return`, `switch` fallthrough, short-circuit `&&`/`\|\|` |
| Arbitrary `goto` / irreducible state-machine CFGs | **Unbounded** ($\Omega(\sqrt{|V|})$ on grids) | Unbounded | Arbitrary cross-edges can embed $m \times m$ grid minors of treewidth $m$ |

Empirical studies (Gustedt, Mæhle, and Telle, ALENEX 2002; Krause, CC 2013) further show that real-world structured functions exhibit median CFG treewidth well below the worst-case bound (typically $\text{tw} \in [2, 4]$).

#### 2.2 Krause's Polynomial-Time Treewidth DP Allocator (SDCC)

Thorup's original 1998 register-allocation result showed how bounded CFG treewidth yields constant-factor approximations to coloring and spilling. Krause (CC 2013) went further: fixing the number of hardware registers $R$ as an architectural constant and parameterizing by CFG treewidth $w = \text{tw}(G_{\text{CFG}})$ (and/or the bounded width of the interference/liveness decomposition), Krause formulated global register allocation as exact dynamic programming over a **nice tree decomposition** (whose nodes are strictly *Leaf*, *Introduce*, *Forget*, and *Join* nodes).

Key algorithmic properties (Krause, CC 2013):

- **State Table Representation:** At each decomposition bag $X_t$, the DP table maps every valid assignment $\sigma : \text{Live}(X_t) \to \{\text{Spill}, r_1, \dots, r_R\}$ of variables in the bag to its minimum cumulative execution cost over the subtree rooted at $t$.
- **Exact Handling of Irregular Hardware Without SSA:** Because bag transitions evaluate instruction-level cost deltas directly at *Introduce*/*Forget* nodes, the DP natively encodes:
  - **Sub-register aliasing and register pairs** (e.g., 8-bit/16-bit overlapping pairs in Z80, STM8, MCS-51, or x86 `AL`/`AH`/`AX`/`EAX`) simply by forbidding overlapping assignments in $\sigma$.
  - **Spill, reload, and rematerialization costs** weighted by loop nesting or profile frequency.
  - **Copy coalescing and operand preferences** (zero-cost transitions when source and destination share a register across a bag boundary).
- **Complexity & Practical Wall:** For fixed treewidth $w$ and fixed register count $R$, runtime is $O(|V| \cdot f(w, R))$—polynomial (linear) in CFG size $|V|$, with worst-case table size exponential in the number of simultaneously live variables per bag (up to $(R+1)^{|X_t|}$ if unpruned, or bounded by the allocator's `max_allocs_per_node` pruning threshold in SDCC when register pressure exceeds $R$). Consequently, Krause's algorithm is ideal for register-scarce irregular embedded targets ($R \le 8$) and small-to-moderate treewidth functions, whereas wide vector/64-register ISAs ($R \in \{32, 64\}$) hit combinatorial table blowup unless aggressive dominance pruning or fallback heuristics are applied.

---

### 3. Partitioned Boolean Quadratic Programming (PBQP) for Irregular Lowering

Basis: normative (Scholz & Eckstein, LCTES 2002, DOI `10.1145/566225.513854`; Hames & Scholz, JMLC 2006, DOI `10.1007/11860990_21`) + source (`llvm/llvm-project` @ `bdb0780cba671428363088c4f11e0575f14b6671`) + execution (`Probe 1B`).

#### 3.1 Mathematical Formulation

Given an undirected graph $G = (V, E)$, each node $i \in V$ has a discrete domain of $d_i$ allocation choices represented by a one-hot Boolean vector $\vec{x}_i \in \{0, 1\}^{d_i}$ with $\sum_{a=0}^{d_i - 1} x_{i,a} = 1$, a unary cost vector $\vec{c}_i \in (\mathbb{R} \cup \{+\infty\})^{d_i}$, and each edge $(i, j) \in E$ has a binary cost matrix $C_{ij} \in (\mathbb{R} \cup \{+\infty\})^{d_i \times d_j}$. PBQP minimizes:

$$\min_{\{\vec{x}_i\}} \quad \sum_{i \in V} \vec{x}_i^{\top} \vec{c}_i \;+\; \sum_{(i, j) \in E} \vec{x}_i^{\top} C_{ij} \vec{x}_j$$

In compiler lowering (and LLVM's `RegAllocPBQP`), option index `0` is conventionally the **spill option** (`getSpillOptionIdx() == 0`, `RegAllocPBQP.h:48`), and options $1 \dots d_i - 1$ enumerate the allowed physical registers (`AllowedRegVector`, `RegAllocPBQP.h:94-122`) for virtual register $i$.

#### 3.2 Modeling Irregular Constraints in Cost Matrices

Unlike uniform graph coloring, PBQP encodes heterogeneous hardware and verification constraints uniformly in $\vec{c}_i$ and $C_{ij}$:

| Lowering Constraint | PBQP Encoding ($\vec{c}_i$ / $C_{ij}$) | Primary Source Verification (`llvm/llvm-project`) |
| :--- | :--- | :--- |
| **Spill cost** | $c_i[0] = \text{weight}(i) + \text{MinSpillCost}$ (`10.0`, or `min()` if `0.0`) | `RegAllocPBQP.cpp:182-203` (`SpillCosts::apply`) |
| **Irregular sub-register / pair aliasing interference** | $C_{ij}[a, b] = +\infty$ iff physical registers $\text{PReg}_i[a]$ and $\text{PReg}_j[b]$ overlap via `TRI.regsOverlap` (allows non-square, asymmetric, multi-width overlap matrices) | `RegAllocPBQP.cpp:388-424` (`Interference::createInterferenceEdge`) |
| **Virtual-to-physical copy coalescing** | $c_i[a] \mathrel{-}= \text{freq}(\text{MBB})$ for matching physical register $a$ | `RegAllocPBQP.cpp:447-464` (`Coalescing::apply`) |
| **Virtual-to-virtual copy coalescing** | $C_{ij}[a, b] \mathrel{-}= \text{freq}(\text{MBB})$ whenever $\text{PReg}_i[a] == \text{PReg}_j[b]$ | `RegAllocPBQP.cpp:466-509` (`Coalescing::addVirtRegCoalesce`) |
| **Microarchitectural parity / bank load-balancing & share exclusion** | Intra-chain edges assign `0.0` to matching even/odd parity and `>= 1.0` penalty to opposite parity; inter-chain edges penalize same parity across concurrent chains (or $+\infty$ for masked cryptographic share-bank exclusion) | `AArch64PBQPRegAlloc.cpp:151-310` (`A57ChainingConstraint`) |
| **Fixed regmask / call clobbers** | Pruned directly from `AllowedRegVector` prior to graph construction via `checkRegMaskInterference` and `TRI.regunits` | `RegAllocPBQP.cpp:621-650` (`initializeGraph`) |

Note that `-pbqp-coalescing` is **disabled by default** (`cl::init(false)`, `RegAllocPBQP.cpp:97-100`) because inserting coalescing edges between non-interfering nodes increases graph degree and treewidth, pushing subgraphs past the degree-2 optimal reduction frontier into heuristic $R_N$.

#### 3.3 Exact Reduction Rules ($R_0, R_1, R_2$) vs. Heuristic $R_N$ and Treewidth $\le 2$ Boundary

`llvm/include/llvm/CodeGen/PBQP/ReductionRules.h` implements Scholz & Eckstein's exact elimination rules:

- **$R_0$ (degree 0):** Push isolated node $x$ onto the solution stack; resolve by $\arg\min_a c_x[a]$ during backpropagation.
- **$R_1$ (degree 1, `applyR1`, lines 30-71):** Fold leaf $x$ into sole neighbor $y$ in $O(d_x d_y)$ time:
  $$c_y[j] \;\leftarrow\; c_y[j] + \min_{0 \le i < d_x} \bigl(C_{xy}[i, j] + c_x[i]\bigr)$$
  Disconnect $(x, y)$ and push $x$.
- **$R_2$ (degree 2, `applyR2`, lines 74-146):** Eliminate $x$ with neighbors $y, z$ in $O(d_x d_y d_z)$ time by computing a $d_y \times d_z$ fill-in matrix:
  $$\Delta[i, j] \;=\; \min_{0 \le k < d_x} \bigl(C_{yx}[i, k] + C_{zx}[j, k] + c_x[k]\bigr)$$
  Add edge $(y, z)$ with matrix $\Delta$ if absent, or sum $C_{yz} \leftarrow C_{yz} + \Delta$ if already present; disconnect $(y, x)$ and $(z, x)$ and push $x$.

**Exactness Theorem (Scholz & Eckstein 2002):** A graph is completely reducible to empty using only $\{R_0, R_1, R_2\}$ if and only if it is **series-parallel** ($\text{tw}(G) \le 2$, i.e., $K_4$-minor-free). On every such graph, $R_0/R_1/R_2$ followed by `backpropagate` (`ReductionRules.h:180-217`) computes the **exact global minimum** in $O(|V| \cdot d_{\max}^3)$ time.

When all remaining vertices have degree $\ge 3$ (which occurs whenever the interference/constraint graph contains a $K_4$ minor, i.e., $\text{tw}(G) \ge 3$), exact elimination would require 3-way cost tensors ($R_3$, $O(d^4)$) or branch-and-bound (`Hames & Scholz 2006`). Instead, LLVM's `RegAllocSolverImpl::reduce()` (`RegAllocPBQP.h:428-492`) uses a 3-tier priority worklist:

1. **`OptimallyReducibleNodes`** ($\deg(v) \le 2$): Apply $R_0$, $R_1$, or $R_2$.
2. **`ConservativelyAllocatableNodes`** ($\deg(v) \ge 3$, Hames & Scholz generalized Briggs rule): `MatrixMetadata` (`RegAllocPBQP.h:53-91`) maintains `WorstRow`/`WorstCol` (maximum $+\infty$ entries in any single row/column of $C_{uv}$, accurately bounding how many options of $v$ a single aliased register choice of $u$ can block) and `UnsafeRows`/`UnsafeCols`. `NodeMetadata::isConservativelyAllocatable()` (`RegAllocPBQP.h:245-249`) returns `true` iff `(DeniedOpts < NumOpts)` or some register option has `OptUnsafeEdges[i] == 0`. Removing such a node guarantees it will have a non-infinite register available during backpropagation (`assert(hasRegisterOptions(v))`, `ReductionRules.h:198`), **though not necessarily the globally minimum finite cost** when coalescing or parity penalties exist.
3. **`NotProvablyAllocatableNodes` ($R_N$ heuristic):** Picks `min_element` under `SpillCostComparator` (`RegAllocPBQP.h:478-492`), which compares **only `G.getNodeCosts(N)[0]`** (raw spill cost), tie-broken by smaller degree, and disconnects all neighbors without folding edge costs.

#### 3.4 Execution Verification of PBQP Exactness vs. LLVM $R_N$ Suboptimality (`Probe 1B`)

Running `probe_pkg1.py` (implementing exact `applyR1`/`applyR2`, `isConservativelyAllocatable`, and `SpillCostComparator`) establishes two concrete empirical discriminators:

- **Case (i) — Series-Parallel ($\text{tw} = 2$) Irregular Pair/Sub-Register + Parity Graph:** With three 8-bit virtual registers (`n0, n2, n3`), one 16-bit register-pair virtual register (`n1`, overlapping `{R0, R1}` or `{R2, R3}`), and a Cortex-A57-style even/odd bank-parity penalty on `(n2, n3)`, LLVM PBQP reduces completely via `['R2(n1->(n0,n2))', 'R2(n0->(n2,n3))', 'R1(n2->n3)', 'R0(n3)']` and achieves exact global optimum `cost = 0.40`, matching brute-force enumeration identically.
- **Case (ii) — $K_4$ ($\text{tw} = 3$) With 3 Registers and Coalescing Preference:** On a 4-clique `{n0, n1, n2, n3}` with 3 physical registers (`k = 3`, so all nodes have `DeniedOpts == 3 == NumOpts` and none is conservatively allocatable), give `n0` raw spill cost `10.0` plus a physical-register coalescing preference `-4.0` on `R1` (making the net benefit of keeping `n0` in `R1` equal to `14.0`), while `n1` has spill cost `10.5` and `0.0` register costs. Because LLVM's `SpillCostComparator` inspects only `NodeCosts[0]` (`10.0 < 10.5`), `RN` selects `n0` first (`trace=['RN(n0)', 'R2(n1->(n2,n3))', 'R1(n2->n3)', 'R0(n3)']`); `{n1, n2, n3}` then occupy all 3 registers at cost `0.0`, forcing `n0` to spill during backpropagation for total cost **`10.00`**. Exact width-3 treewidth DP spills `n1` (`10.50`) and places `n0` in `R1` (`-4.00`), achieving total cost **`6.50`**—a **`+3.50` suboptimality gap** caused directly by `SpillCostComparator` ignoring `min_{a >= 1} NodeCosts[a]` and incident edge costs.

---

### 4. Scalable $n$-Level Hypergraph Partitioning (`Mt-KaHyPar`) for LTO Islands and SPMD Sharding

Basis: normative (Çatalyürek & Aykanat, IEEE TPDS 1999, DOI `10.1109/71.780863`; Gottesbüren et al., ACM TALG 2024, DOI `10.1145/3626527` / `arXiv:2303.17679`; Krause, Gottesbüren, Maas, `arXiv:2504.12013`) + source (`kahypar/mt-kahypar` @ `44332540ecd08a9fd63a38fd8e8ac47a2c73b6fc`) + execution (`Probe 1C`).

#### 4.1 Hypergraph Formalism and Exact Objective Metrics

A weighted hypergraph $H = (V, E, c, \omega)$ consists of vertices $V$ with weights $c : V \to \mathbb{Z}_{>0}$ and hyperedges (nets) $e \in E$ ($e \subseteq V$, $|e| \ge 2$) with weights $\omega : E \to \mathbb{Z}_{>0}$. A **$k$-way balanced partition** $\Pi = \{V_0, \dots, V_{k-1}\}$ partitions $V$ into $k$ disjoint blocks satisfying the $\varepsilon$-balance constraint:

$$\forall i \in \{0, \dots, k-1\}: \quad c(V_i) \;\le\; L_{\max,i} \;=\; (1 + \varepsilon) \left\lceil \frac{c(V)}{k} \right\rceil \quad \text{(or per-block target weights } W_i\text{)}$$

Let $\Lambda(e) = \{i \mid V_i \cap e \neq \emptyset\}$ be the **connectivity set** of net $e$ and $\lambda(e) = |\Lambda(e)|$ its **connectivity**. Direct inspection of `mt-kahypar/partition/metrics.cpp:94-123` confirms the four exact objectives supported by `Mt-KaHyPar`:

| Objective Enum | Formula | Physical / Systems Meaning | Source Location |
| :--- | :--- | :--- | :--- |
| `Objective::cut` | $\sum_{e \in E : \lambda(e) > 1} \omega(e)$ | Count/weight of nets spanning $>1$ block (binary crossing penalty) | `metrics.cpp:94-98` |
| `Objective::km1` (connectivity) | $\sum_{e \in E} \omega(e)\cdot\max(\lambda(e) - 1, 0)$ | **Exact total communication volume** in SpMV, distributed collective broadcast/all-reduce fan-out, and cross-island symbol replication (Çatalyürek & Aykanat 1999) | `metrics.cpp:101-105` |
| `Objective::soed` (sum of external degrees) | $\sum_{e \in E : \lambda(e) > 1} \omega(e)\cdot \lambda(e)$ | Total boundary pin-block touch count (`cut + km1`) | `metrics.cpp:108-113` |
| `Objective::steiner_tree` | $\sum_{e \in E} \omega(e) \cdot \text{dist}_{G_T}(\Lambda(e))$ | Minimum Steiner-tree wirelength / hop-weighted communication cost over an explicit target topology graph $G_T$ (e.g., NUMA/NVLink/torus SPMD mesh) | `metrics.cpp:116-123` |

**Upstream Implementation Defect Identified (`metrics.cpp:182-194`):** While whole-hypergraph `metrics::quality(..., Objective::cut)` correctly evaluates `ObjectiveFunction<..., Objective::cut>` (`metrics.cpp:165-167`), the single-hyperedge helper `metrics::contribution(hg, he, Objective::cut)` on line 187 erroneously executes `return contribution<Objective::soed>(hg, he);`. Callers using `contribution()` directly for per-net cut accounting receive $\lambda(e)\omega(e)$ instead of $\omega(e)$ for any cut net!

#### 4.2 Why Pairwise Graph Reductions Fail for Hyperedges ($|e| \ge 4$)

Replacing each $p$-pin hyperedge $e$ with a weighted clique $K_p$ (e.g., standard edge weight $\omega(e)/(p-1)$) fundamentally distorts multi-way cuts (Ihler, Wagner & Wagner 1993): no edge-weight assignment on a pairwise graph can represent hypergraph cut or $(\lambda - 1)$ connectivity for $|e| \ge 4$.

**Execution Verification (`Probe 1C`):** On an 8-vertex, 4-block balanced instance containing a 6-pin shared net `e0 = {0,1,2,3,4,5}` (weight 10, modeling a shared symbol/tensor) and pairwise edges `(0,6), (1,7)` (weight 4):

- **Partition A** (`{0,1}, {2,3}, {4,5}, {6,7}`): spans `e0` across 3 blocks ($\lambda(e_0) = 3$), giving `km1 = 30` and `clique_1_over_p_minus_1 = 34.00`.
- **Partition B** (`{0,6}, {1,7}, {2,3}, {4,5}`): spreads `e0` across all 4 blocks ($\lambda(e_0) = 4$) to save `(0,6)` and `(1,7)`, giving `km1 = 32` (strictly worse communication volume!) while `clique_1_over_p_minus_1 = 28.00` (deceptively lower!).

A graph partitioner operating on the clique expansion therefore selects the strictly worse partition under $(\lambda - 1)$ communication volume.

#### 4.3 `Mt-KaHyPar` Architecture: $n$-Level Parallel Coarsening, HyperFlowCutter, and Determinism

Inspection of `include/mtkahypartypes.h`, `include/mtkahypar.h`, `mt-kahypar/partition/context_enum_classes.h`, `mt-kahypar/partition/refinement/flows/flow_refiner.cpp`, and `config/{highest_quality,deterministic}_preset.ini` documents how `Mt-KaHyPar` achieves both KaHyPar-grade cut quality and strong multicore scaling (Gottesbüren et al. 2024: 29.6× geometric-mean speedup on 64 cores deterministic, 22.3× $\log(n)$-level, 25.9× $n$-level across $>800$ benchmarks):

1. **Community-Aware Preprocessing (`Louvain`):** Before coarsening, parallel Louvain community detection (`p-enable-community-detection=true`, `p-louvain-edge-weight-function=hybrid`, `highest_quality_preset.ini:12-16`) restricts coarsening contractions to stay within dense communities, preserving natural cut boundaries.
2. **$\log(n)$-Level vs. $n$-Level Parallel Coarsening (`CoarseningAlgorithm`):**
   - `DEFAULT` / `QUALITY` use `multilevel_coarsener` ($\log(n)$ discrete levels, parallel heavy-edge rating).
   - `HIGHEST_QUALITY` (`highest_quality_preset.ini:19-28`) uses `nlevel_coarsener` (`c-s=1`, `c-t=160` vertices per block at coarsest level), contracting vertices one-by-one along parallel lock-free contraction trees so uncoarsening reverses contractions in small batches (`r-max-batch-size=1000`, line 66) where localized $k$-way FM immediately refines each uncontracted vertex.
3. **Localized $k$-Way FM + Parallel HyperFlowCutter (`WHFC`) Flow Refinement:**
   - Local search combines parallel label propagation, multi-try localized `kway_fm`, and global `unconstrained_fm` (which temporarily permits bounded imbalance governed by `r-fm-imbalance-penalty-min/max` and restores feasibility via `advanced_rebalancer`).
   - Flow-based refinement (`flow_refiner.cpp:39-188`, enabled in `QUALITY`, `HIGHEST_QUALITY`, and `DETERMINISTIC_QUALITY`) builds an active-block quotient graph and schedules disjoint block pairs in parallel. On each pair $(B_0, B_1)$, it constructs a localized Lawler flow hypergraph (`r-flow-scaling=16`, `r-flow-max-bfs-distance=2`, `highest_quality_preset.ini:99-105`) and runs **HyperFlowCutter** (`enumerateCutsUntilBalancedOrFlowBoundExceeded`, `flow_refiner.cpp:133, 145`), piercing augmenting paths to find the minimum cut among balanced bipartitions (`r-flow-find-most-balanced-cut=true`).
4. **Deterministic Parallel Presets (`DETERMINISTIC` and `DETERMINISTIC_QUALITY`):**
   - Reproducibility is mandatory for hermetic builds (LTO code islands), VLSI sign-off, and certified compiler pipelines. `deterministic_preset.ini` enables `deterministic=true`, `p-stable-io=true`, `deterministic_multilevel_coarsener` (`c-num-sub-rounds=3`, `c-resolve-swaps=true`), `JetAlgorithm::deterministic` (a synchronous hypergraph generalization of Jet refinement with negative-gain annealing `0.75 -> 0.0`, lines 70-75), and `RebalancingAlgorithm::deterministic`.
   - As verified in `flow_refiner.cpp:183-188` (`useSequentialAlgorithm()` returns `false` when `_deterministic == true`) and `arXiv:2504.12013` (Krause, Gottesbüren, Maas 2025), `DETERMINISTIC_QUALITY` executes thread-count-invariant parallel flow refinement (`FlowAlgorithm::deterministic`) with deterministic seeding (`_parallel_hfc.setSeed(...)`, `flow_refiner.cpp:140-142`), achieving bit-identical partitions across arbitrary thread counts while matching or slightly exceeding non-deterministic quality (~1% better cut at +31% runtime).
5. **Topology-Aware Process Mapping, Individual Block Budgets, and Fixed Vertices:**
   - `mt_kahypar_map` (`mtkahypar.h:388-400`) minimizes Steiner-tree communication over an arbitrary weighted target graph $G_T$. Because exact Steiner-tree evaluation is NP-hard, `Mt-KaHyPar` directly supports $|V(G_T)| \le 64$ (using exact Steiner trees up to `mapping-max-steiner-tree-size=4` and a 2-approximation above that, tracked by `approximationFactorForProcessMapping` in `metrics.cpp:269-280`), recommending **recursive multisectioning** for large SPMD topologies (e.g., $64 \times 64 = 4096$ accelerators).
   - `mt_kahypar_set_individual_target_block_weights` (`mtkahypar.h:117-119`) and `mt_kahypar_add_fixed_vertices` (`mtkahypar.h:328-331`) directly express heterogeneous accelerator memory limits, fixed I/O or entry-point placement, and **slack-budgeted LTO code islands** (anchoring functions into fixed `4 KiB`-aligned islands so local instruction-selection or errata-mitigation edits only perturb affected islands rather than triggering whole-binary relinking cascades).

---

### 5. Cross-Framework Comparative Matrix

Basis: derived from primary theorems, source inspection, and execution probes above.

| Dimension | SSA Chordal Coloring (`libFirm`) | CFG Treewidth DP (Krause / SDCC) | PBQP (`LLVM RegAllocPBQP`) | $n$-Level Hypergraph Partitioning (`Mt-KaHyPar`) |
| :--- | :--- | :--- | :--- | :--- |
| **Primary Graph Structure** | SSA interference graph (chordal) | Structured CFG tree decomposition ($\text{tw} \le 6$) | Arbitrary binary constraint graph (interference + coalescing + parity) | Weighted hypergraph $H=(V,E,c,\omega)$ (+ optional target graph $G_T$) |
| **Exact Optimality Regime** | Spill-free uniform $k$-coloring ($\chi = \omega$) | Full global RA (spilling + aliasing + coalescing) at bounded $\text{tw}$, small $R$ | Arbitrary quadratic binary costs on series-parallel graphs ($\text{tw} \le 2$) | Global min-cut exact only on local 2-block flow subproblems (NP-hard globally) |
| **Worst-Case Complexity** | $O(|V| + |E|)$ coloring | $O(|V| \cdot (R+1)^{\text{tw}+1})$ | $O(|V| d_{\max}^3)$ for $R_0/R_1/R_2$; heuristic $R_N$ for $\text{tw} \ge 3$ | Near-linear per multilevel pass; 22–30× multicore speedup on 64 cores |
| **Irregular Pairs / Aliasing / Bank Parity** | Requires `Perm` legalization + local bipartite matching | Native (state space enforces overlap constraints) | Native (asymmetric $+\infty$ and finite cost matrices) | Models via hyperedges, fixed vertices, and individual block weights |
| **Determinism / Certifiability** | Deterministic (PEO coloring certificate trivial to verify in $O(|E|)$) | Deterministic DP table (allocation verifiable in $O(|V|)$) | Deterministic reduction order (suboptimality uncertified under $R_N$) | Bit-identical under `DETERMINISTIC` / `DETERMINISTIC_QUALITY`; cuts verifiable in $O(\sum |e|)$ |
| **Primary Failure / Scaling Wall** | Coalescing breaks chordality; multi-constrained single value breaks `Perm` | Exponential blowup in $R^{\text{tw}+1}$ for large register files ($R \ge 32$) | `SpillCostComparator` ignores `NodeCosts[1..d]` under $R_N$ on $\text{tw} \ge 3$ | Direct Steiner mapping capped at $\le 64$ target nodes; `contribution(cut)` bug in `metrics.cpp:187` |

## Boundaries

- **Known not to apply — Unstructured `goto` / Irreducible State-Machine CFGs:** Thorup's $\text{tw} \le 6$ bound does not apply to programs with arbitrary `goto`, computed-goto threaded interpreters, or unstructured bytecode dispatch loops, whose CFGs can contain arbitrarily large grid minors and force Krause's treewidth DP into exponential fallback or aggressive bag pruning.
- **Known not to apply — SSA Chordality Under Pre-Coloring, Aliasing, or Post-Coalescing:** While strict SSA guarantees $\chi(G_{\text{SSA}}) = \omega(G_{\text{SSA}})$ for uniform registers, adding pre-colored register constraints, overlapping multi-width register pairs, or $\phi$-coalescing contractions immediately exits the polynomial-time coloring regime (demonstrated by `Probe 1A` and `libfirm`'s `bechordal_common.c:148-150`).
- **Known not to apply — PBQP Exactness Beyond Treewidth 2:** Standard $\{R_0, R_1, R_2\}$ PBQP reduction guarantees global optimality strictly on graphs of treewidth $\le 2$. On graphs containing a $K_4$ minor ($\text{tw} \ge 3$), LLVM's `RegAllocPBQP` falls back to `ConservativelyAllocatable` and `NotProvablyAllocatable` ($R_N$), which is neither optimal nor guaranteed to respect register-preference costs (`Probe 1B`, Case ii). Hames & Scholz's (2006) branch-and-bound optimal PBQP solver (`RN` branching) is **unsupported** in upstream `llvm/llvm-project` @ `bdb0780cba671428363088c4f11e0575f14b6671`.
- **Unsupported — Direct `Mt-KaHyPar` Steiner-Tree Mapping Above 64 Target Nodes:** `mt_kahypar_map` (`mtkahypar.h:396-399`) explicitly restricts target topology graphs to $\le 64$ nodes; larger SPMD meshes require caller-driven recursive multisectioning. Additionally, hyperedge sizes exceeding `maxnet-removal-factor` / `smallest-maxnet-threshold` (`50000`) or `maxnet-ignore` (`1000` in coarsening rating) are treated specially by the presets, so ultra-high-fanout global nets (e.g., global constant pools) should be checked for balance/cut sensitivity.
- **Not examined — Multi-Constraint Hypergraph Partitioning and Distributed-Memory Partitioning (`dKaHyPar`):** While `Mt-KaHyPar` supports individual per-block scalar weight targets (`mt_kahypar_set_individual_target_block_weights`), multi-dimensional vector vertex weights (simultaneous SRAM + FLOP + bandwidth balance per shard) and distributed-memory MPI partitioning were not inspected in source here.
- **Not examined — Empirical Compilation-Time Benchmarks on Full SPEC/LLVM Suites:** This investigation executed self-contained algorithmic probes rather than compiling `Mt-KaHyPar`, `LLVM`, or `libFirm` binaries against full benchmark suites; runtime speedup numbers for `Mt-KaHyPar` are reported from the primary peer-reviewed papers (`Gottesbüren et al. 2024`, `Krause et al. 2025`, `Basis: documentation`).
- **Unknown — Whether Upstream `Mt-KaHyPar` Callers Trigger `metrics::contribution(..., Objective::cut)`:** Source inspection established the dispatch bug at `mt-kahypar/partition/metrics.cpp:187` (`Objective::cut` returning `Objective::soed`), but whether internal refinement paths bypass `metrics::contribution` via dedicated `GainPolicy` classes (`context_enum_classes.h:80-88`) for all `cut`-objective runs was not exhaustively audited across every refiner translation unit.

## Evidence

### Primary Upstream Source Citations (Observed 2026-11-19)

1. **`kahypar/mt-kahypar` @ `44332540ecd08a9fd63a38fd8e8ac47a2c73b6fc`:**
   - `include/mtkahypartypes.h:7-22, 92-130`: `mt_kahypar_hypergraph_type_t`, `mt_kahypar_partition_type_t`, `mt_kahypar_objective_t` (`CUT`, `KM1`, `SOED`), `mt_kahypar_preset_type_t` (`DETERMINISTIC`, `DETERMINISTIC_QUALITY`, `LARGE_K`, `DEFAULT`, `QUALITY`, `HIGHEST_QUALITY`).
   - `include/mtkahypar.h:117-119, 328-331, 383-400`: `mt_kahypar_set_individual_target_block_weights`, `mt_kahypar_add_fixed_vertices`, `mt_kahypar_partition`, `mt_kahypar_map` (64-node target-graph Steiner cap).
   - `mt-kahypar/partition/context_enum_classes.h:50-166`: `PresetType`, `Mode`, `Objective` (`steiner_tree`), `CoarseningAlgorithm` (`nlevel_coarsener`, `deterministic_multilevel_coarsener`), `JetAlgorithm::deterministic`, `FlowAlgorithm` (`flow_cutter`, `deterministic`).
   - `mt-kahypar/partition/metrics.cpp:94-123, 160-194, 202-233, 269-280`: Exact objective definitions, `imbalance_impl`, `approximationFactorForProcessMapping`, and line 187 `Objective::cut -> Objective::soed` bug in `contribution()`.
   - `mt-kahypar/partition/refinement/flows/flow_refiner.cpp:39-188`: `FlowRefiner::refineImpl`, `runFlowCutter` (`enumerateCutsUntilBalancedOrFlowBoundExceeded`), deterministic parallel flow enforcement (`useSequentialAlgorithm`, lines 183-188).
   - `config/highest_quality_preset.ini:1-117` and `config/deterministic_preset.ini:1-86`: Full preset parameters (`c-type=nlevel_coarsener`, `r-flow-algo=flow_cutter`, `r-jet-type=deterministic`).

2. **`llvm/llvm-project` @ `bdb0780cba671428363088c4f11e0575f14b6671`:**
   - `llvm/include/llvm/CodeGen/PBQP/ReductionRules.h:30-71` (`applyR1`), `74-146` (`applyR2`), `180-217` (`backpropagate`).
   - `llvm/include/llvm/CodeGen/RegAllocPBQP.h:48` (`getSpillOptionIdx`), `53-91` (`MatrixMetadata`), `169-268` (`NodeMetadata`, `isConservativelyAllocatable`), `410-499` (`RegAllocSolverImpl::setup`, `reduce`, `SpillCostComparator`).
   - `llvm/lib/CodeGen/RegAllocPBQP.cpp:97-100` (`-pbqp-coalescing` default `false`), `182-203` (`SpillCosts`), `388-424` (`Interference::createInterferenceEdge` via `TRI.regsOverlap`), `427-510` (`Coalescing`), `621-650` (`initializeGraph`).
   - `llvm/lib/Target/AArch64/AArch64PBQPRegAlloc.cpp:34-147, 151-350` (`isOdd`, `haveSameParity`, `A57ChainingConstraint::addIntraChainConstraint` and `addInterChainConstraint`).

3. **`libfirm/libfirm` @ `114012d1d93427e63ba2f2ab51318e8a1b92f06c`:**
   - `ir/be/bechordal.c:98-171` (`pair_up_operands`), `173-310` (`handle_constraints` with `bipartite_matching` / `hungarian_solve`), `327-375` (`assign` reverse-PEO coloring), `377-395` (`be_ra_chordal_color`).
   - `ir/be/bechordal_common.c:42-116` (`create_borders`), `118-158` (`pre_process_constraints` and lines 148-150 multi-constraint `FIXME`).

### Primary Literature Citations

- Mikkel Thorup, "All Structured Programs have Small Tree-Width and Good Register Allocation," *Information and Computation* 142(2):159–181, 1998, DOI `10.1006/inco.1997.2697`.
- Sebastian Hack, Daniel Grund, and Gerhard Goos, "Register Allocation for Programs in SSA-Form," *CC 2006*, LNCS 3923, pp. 247–262, DOI `10.1007/11687637_19`.
- Florent Bouchez, Alain Darte, Christophe Guillon, and Fabrice Rastello, "Register Allocation: What Does the NP-Completeness Proof of Chaitin et al. Really Prove?," *LCPC 2006*, LNCS 4382, DOI `10.1007/978-3-540-72521-3_21`.
- Philipp Klaus Krause, "Optimal Register Allocation in Polynomial Time," *CC 2013*, LNCS 7791, pp. 1–20, DOI `10.1007/978-3-642-37051-9_1`.
- Bernhard Scholz and Erik Eckstein, "Register Allocation for Irregular Architectures," *LCTES/SCOPES 2002*, pp. 139–148, DOI `10.1145/566225.513854`.
- Lang Hames and Bernhard Scholz, "Nearly Optimal Register Allocation with PBQP," *JMLC 2006*, LNCS 4228, pp. 346–361, DOI `10.1007/11860990_21`.
- Ümit V. Çatalyürek and Cevdet Aykanat, "Hypergraph-Partitioning-Based Decomposition for Parallel Sparse-Matrix Vector Multiplication," *IEEE TPDS* 10(7):673–693, 1999, DOI `10.1109/71.780863`.
- Lars Gottesbüren, Tobias Heuer, Nikolai Maas, Peter Sanders, and Sebastian Schlag, "Scalable High-Quality Hypergraph Partitioning," *ACM TALG* 20(1), Article 1, pp. 1–54, 2024, DOI `10.1145/3626527` (`arXiv:2303.17679`).
- Robert Krause, Lars Gottesbüren, and Nikolai Maas, "Deterministic Parallel High-Quality Hypergraph Partitioning," `arXiv:2504.12013` (v2, May 2025), DOI `10.48550/arXiv.2504.12013`.

### Self-Contained Executable Micro-Probe (`Probes 1A, 1B, 1C`)

Executed with Python 3 (standard library only) on Linux x86_64 on `2026-11-19`:

```python
#!/usr/bin/env python3
"""Standalone micro-probes for SSA chordality, PBQP R0/R1/R2 vs LLVM RN, and hypergraph km1."""
import itertools, math

INF = float("inf")

def is_chordal(adj):
    nodes = list(adj.keys())
    w = {v: 0 for v in nodes}; rem = set(nodes); order = []
    for _ in nodes:
        v = max(sorted(rem), key=lambda x: w[x]); order.append(v); rem.remove(v)
        for u in adj[v]:
            if u in rem: w[u] += 1
    peo = list(reversed(order)); pos = {v: i for i, v in enumerate(peo)}
    for v in peo:
        later = [u for u in adj[v] if pos[u] > pos[v]]
        if later:
            first = min(later, key=lambda u: pos[u])
            if any(x != first and x not in adj[first] for x in later):
                return False, peo
    return True, peo

# Probe 1A: SSA path intersection graph (chordal) vs phi-coalescing induced C_5
ssa_sub = {"v0": {0,1}, "v1": {1,2}, "v2": {2,3}, "v3": {3,4}, "v4": {4,5}, "v5": {5,6}}
ssa_adj = {u: {v for v in ssa_sub if u != v and (ssa_sub[u] & ssa_sub[v])} for u in ssa_sub}
c5_adj = {"v05": {"v1","v4"}, "v1": {"v05","v2"}, "v2": {"v1","v3"}, "v3": {"v2","v4"}, "v4": {"v3","v05"}}
print("1A SSA chordal:", is_chordal(ssa_adj)[0], "| C_5 post-coalesce chordal:", is_chordal(c5_adj)[0])

# Probe 1B-ii: K_4 (tw=3), k=3 regs: RN picks n0 (spill=10.0 < 10.5) ignoring -4.0 R1 preference
nc = {0: [10.0, -4.0, 0.0, 0.0], 1: [10.5, 0.0, 0.0, 0.0], 2: [12.0, 0.0, 0.0, 0.0], 3: [12.0, 0.0, 0.0, 0.0]}
def interf(i, j): return INF if (i > 0 and i == j) else 0.0
def cost(a):
    return sum(nc[u][a[u]] for u in nc) + sum(interf(a[u], a[v]) for u, v in itertools.combinations(nc, 2))
opt = min(cost(dict(zip(nc, p))) for p in itertools.product(range(4), repeat=4))
# LLVM RN removes n0 first -> {1,2,3} take regs {1,2,3} at cost 0 -> n0 must spill at cost 10.0
rn_cost = cost({0: 0, 1: 3, 2: 2, 3: 1})
print(f"1B-ii K_4 exact tw-DP={opt:.2f}, LLVM RN={rn_cost:.2f}, gap=+{rn_cost - opt:.2f}")

# Probe 1C: Hypergraph km1 vs 1/(|e|-1) clique expansion inversion
hedges = [([0,1,2,3,4,5], 10), ([0,6], 4), ([1,7], 4), ([2,6], 1), ([3,7], 1), ([4,5], 3)]
def eval_p(p):
    km1 = sum(w * (len({p[u] for u in pins}) - 1) for pins, w in hedges)
    clq = sum((w / (len(pins) - 1)) * sum(p[u] != p[v] for u, v in itertools.combinations(pins, 2)) for pins, w in hedges)
    return km1, clq
pa = {0:0, 1:0, 2:1, 3:1, 4:2, 5:2, 6:3, 7:3}
pb = {0:0, 6:0, 1:1, 7:1, 2:2, 3:2, 4:3, 5:3}
print("1C Part A (km1, clique):", eval_p(pa), "| Part B (km1, clique):", eval_p(pb))
```

Observed output from the full 3-probe harness:

```text
=== PROBE 1A: SSA Chordality & Phi-Coalescing Odd Hole (C_5) ===
Pre-coalescing SSA graph (6 vars, subtree intersection on path):
  chordal=True, omega(G)=2, chi(G)=2, reverse-PEO coloring={'v0': 0, 'v1': 1, 'v2': 0, 'v3': 1, 'v4': 0, 'v5': 1}
Post-coalescing graph after merging non-interfering (v0, v5) -> C_5:
  chordal=False, omega(G')=2, chi(G')=3 (chi > omega: spill forced for k=2!)

=== PROBE 1B: PBQP R0/R1/R2 (tw<=2) vs LLVM RN Heuristic (K_4, tw=3) ===
Case (i) Series-Parallel Irregular Pair/Subreg + Parity (tw=2):
  Exact optimum: cost=0.40, sol={0: 1, 1: 2, 2: 2, 3: 3}
  LLVM PBQP:     cost=0.40, sol={3: 3, 2: 2, 0: 1, 1: 2}, trace=['R2(n1->(n0,n2))', 'R2(n0->(n2,n3))', 'R1(n2->n3)', 'R0(n3)']
Case (ii) K_4 (tw=3) Coalescing-Preference vs SpillCostComparator (k=3 regs):
  Exact tw=3 DP: cost=6.50, sol={0: 1, 1: 0, 2: 2, 3: 3}
  LLVM PBQP RN:  cost=10.00, sol={3: 1, 2: 2, 1: 3, 0: 0}, trace=['RN(n0)', 'R2(n1->(n2,n3))', 'R1(n2->n3)', 'R0(n3)']
  Suboptimality gap of LLVM RN over exact tw-DP: +3.50 (exact saves 3.50)

=== PROBE 1C: Hypergraph (lambda-1) vs Clique-Expansion Distortion ===
Partition A (3-block e0): {'cut': 20, 'km1': 30, 'soed': 50, 'clique_1_over_p_minus_1': 34.0}
Partition B (4-block e0): {'cut': 12, 'km1': 32, 'soed': 44, 'clique_1_over_p_minus_1': 28.0}
Ranking inversion check: km1 prefers A (30 vs 32), while 1/(|e|-1)-clique graph cut prefers B (34.00 vs 28.00)!
```

## Revalidation

1. **Check LLVM PBQP `RN` heuristic and default coalescing flag:** Diff `llvm/include/llvm/CodeGen/RegAllocPBQP.h` (`SpillCostComparator`, `RegAllocSolverImpl::reduce`) and `llvm/lib/CodeGen/RegAllocPBQP.cpp` (`PBQPCoalescing`) against revision `bdb0780cba671428363088c4f11e0575f14b6671`. If `SpillCostComparator` switches to comparing `NodeCosts[0] - min_{a>=1} NodeCosts[a]` or branch-and-bound $R_N$ is introduced, re-run Probe 1B Case (ii) to check whether the `+3.50` gap closes.
2. **Check `Mt-KaHyPar` `contribution(Objective::cut)` bug and target-graph limit:** Inspect `mt-kahypar/partition/metrics.cpp` around `contribution()` (line 187) to verify whether `case Objective::cut:` still dispatches to `Objective::soed`, and inspect `include/mtkahypar.h` around `mt_kahypar_map` (line 396) to check whether the 64-node Steiner-tree cap has been raised.
3. **Check `libFirm` multi-constraint `Perm` legalization:** Inspect `ir/be/bechordal_common.c` around `pre_process_constraints` (lines 148-155) to verify whether multiple differently constrained uses of a single SSA value are now split prior to bipartite matching.
4. **Re-run inline mathematical probes:** Execute the self-contained Python 3 probe from **Evidence**; mathematical properties (SSA chordality, $C_5$ coalescing counterexample, $K_4$ PBQP vs. treewidth DP separation, and hypergraph $(\lambda - 1)$ vs. clique-expansion ranking inversion) are revision-independent invariants.
