# Unfailing Knuth–Bendix Completion, CeTA Rewriting Certificates, and Egglog Cyclic Circuit Extraction

## Summary

Automated equational reasoning, relational equality saturation, and DAG term extraction divide into complementary ordered-rewriting vs. congruence-closure regimes whose soundness and optimality depend on sharply separated proof-search and verification boundaries:

1. **Unfailing Knuth–Bendix completion and ground-joinability (`Twee`):** Classical Knuth–Bendix completion aborts on unorientable axioms such as commutativity ($f(x, y) \approx f(y, x)$). Unfailing completion (`Bachmair, Dershowitz, Plaisted 1989`) in `nick8325/twee` retains unorientable equations for bidirectional paramodulation (`index_all` vs. `index_oriented`) under weighted Knuth–Bendix (`KBO`) or lexicographic path (`LPO`) orderings, while **ground-joinability** (`Twee.Join.groundJoin`) and **connectedness below the overlap peak `cp_top`** (`step3`) discard critical pairs whose every total ground variable instantiation joins strictly below the peak—preserving refutational completeness while containing equational blowup. Internally, `Twee` enforces an LCF-style trusted `certify` boundary (`Twee/Proof.hs`) over `Data.PackedSequence` flatterms.
2. **Dependency-Pair SCCs, matrix/arctic interpretations, and Isabelle/HOL `CPF` verification (`IsaFoR`/`CeTA`):** Proving termination of rewrite systems that defeat syntactic `KBO`/`LPO` orders decomposes defined symbols into Arts–Giesl Dependency Pair (`DP`) strongly connected components (`SCCs`) oriented via linear, matrix, and tropical/arctic ($\max, +$) semiring interpretations. Because solver synthesis (often SAT/SMT-backed) exceeds `50k–200k` LoC, `IsaFoR`/`CeTA` (`v3.9`) isolates solver heuristics from the trusted base by verifying XML `Certification Problem Format` (`CPF`) DAG certificates inside an Isabelle/HOL-verified, code-generated Haskell checker.
3. **Relational congruence closure (`egglog`) and NP-hard cyclic-circuit DAG extraction (`extraction-gym`, `arXiv:2408.17042`):** Rather than destructively orienting rules, `egraphs-good/egglog` stores terms in functional-dependency relations reconciled by lattice `:merge` unions, compiled via hypergraph **hypertree decomposition** and **Free Join** (`core-relations/src/free_join/plan.rs`, `execute.rs`), hybrid incremental/full-scan rebuilding (`rebuild.rs`), and an internal ground-equality `proof_checker.rs`. While minimum **tree-cost** extraction resolves in polynomial time via Bellman–Ford (`egglog/src/extract.rs`), **DAG-cost** extraction (charging shared subterms once) is NP-hard and inapproximable to any constant factor. Iterative cycle-banning ILP (`faster_ilp_cbc.rs`) avoids invalid zero-grounded cycles ($A \to B \to A$) only via repeated CBC restarts (up to `> 36,000 s`), whereas mapping e-graphs to **cyclic monotone Boolean circuits** (`Sun, Zhang, Ni 2024`, `glenn-sun/egg-extraction-gym`) yields $2^{O(w^2)} \mathrm{poly}(w, n)$ exact DP over nice tree decompositions of width $w$—though source audit reveals a subtle self-loop defect in `circuit.rs:69-72` during `contract_edge_remove_out` preprocessing.

## Applicability

This report examines five tightly coupled upstream artifacts spanning equational completion, rewriting proof certification, equality saturation, and DAG extraction:

- **Ordered Equational Completion:** `nick8325/twee` (`9f56b26a9b09ea508ff944702b88d60db48c4cb9`, CADE 2021 `DOI: 10.1007/978-3-030-79876-5_35`), grounded in unfailing completion (`Bachmair, Dershowitz, Plaisted 1989`) and `KBO`/`LPO`.
- **Certified Rewriting Verification:** `IsaFoR / CeTA` release `3.9` (`https://cl-informatik.uibk.ac.at/software/ceta/`, TPHOLs 2009 `DOI: 10.1007/978-3-642-03359-9_31`, `CPF` UITP 2014 `DOI: 10.4204/EPTCS.167.8`) and Arts–Giesl Dependency Pairs (`TCS 2000`, `DOI: 10.1016/S0304-3975(99)00207-8`). Because `IsaFoR`/`CeTA` distributes source archives and verified binaries from the University of Innsbruck rather than an unauthenticated GitHub `HEAD` mirror, its identity is pinned by release version `3.9` and peer-reviewed DOIs rather than a Git commit SHA.
- **Relational E-Graphs & Extraction:** `egraphs-good/egglog` (`d89bc58adc9b9a87a8f571c5b9ad75d686d226e6`, PLDI 2023 `DOI: 10.1145/3591239`), `egraphs-good/extraction-gym` (`903ba0f818b50608fe20ae9e0f03c35cb27bc50a`), and `glenn-sun/egg-extraction-gym` (`8be08032d5cbea021ca1d841c103be0afe02644a`, implementing `arXiv:2408.17042`).
- **Relationship among subjects:** `Twee` and `egglog` solve dual facets of equational reasoning (destructive ordered completion for first-order theorem proving vs. non-destructive bounded saturation for compiler/program optimization); `IsaFoR`/`CeTA` demonstrates how heavy rewriting/termination search produces small machine-checkable `CPF` certificates while `egglog`'s `proof_checker.rs` verifies ground equality witnesses inside an unverified Rust kernel; and `extraction-gym` + `glenn-sun/egg-extraction-gym` solve the post-saturation DAG extraction bottleneck left open by `egglog`'s tree-only `TreeExtractor`. Execution claims (`Basis: execution`) derive from inspecting `extraction-gym/test_data/fuzz/` inputs and running the self-contained Python 3.13.15 probe preserved in **Evidence**.

## Findings

### 1. Unfailing Knuth–Bendix Completion, Model-Relativized KBO/LPO, and Ground-Joinability (`Twee`)

`Basis: normative + source + execution`

Standard Knuth–Bendix completion requires every deduced equation $s \approx t$ to orient strictly under a reduction order $\succ$ ($s \succ t$ or $t \succ s$), failing immediately on permutative axioms such as commutativity ($f(x, y) \approx f(y, x)$) or associativity-commutativity (`AC`) combinations where both sides have identical size and symbol/variable multiset counts.

- **Unfailing Completion (`Bachmair, Dershowitz, Plaisted 1989`; `Twee/CP.hs`, `Twee/Join.hs`):** Rather than aborting on unorientable equations, unfailing completion splits the active set (`RuleIndex` in `Twee.hs:87, 98`) into strictly **oriented rules** (`index_oriented`) and **all equations** (`index_all`, indexing both directions via `BothPos` in `CP.hs:54-59`). Ordered paramodulation (`step2` in `Twee/Join.hs:92-95`) permits rewriting with an unoriented rule $l \approx r$ under substitution $\sigma$ only when $\sigma(l) \succ \sigma(r)$ holds on the **instantiated** redex (`reduces rule sub`) and the equation is simpler than the target equation (`unorient rule simplerThan (t :=: u)`). Provided the reduction order is **ground-total** (total on variable-free ground terms up to a chosen precedence), unfailing completion is **refutationally complete**: any equational consequence $s \approx t$ of the axioms is eventually proved by a rewrite valley once Skolemized constants replace existentially quantified goal variables.
- **Exact `KBO` and `LPO` Realizations (`Twee/KBO.hs:41-154`, `Twee/LPO.hs:10-107`):**
  1. `KBO.lessEq` (`KBO.hs:41-72`) tests $t \preceq_{\mathrm{kbo}} u$ via weighted symbol/variable sizes (`size t < size u`, or `size t == size u` with symbol precedence `f << g`, or identical head symbols compared lexicographically with unification-guarded tail checks `lexLess`), combined with **variable-weight dominance** (`xs lessVars ys`, lines 68–72): no variable $x$ may carry greater weighted multiplicity in $t$ than in $u$. Configurable weight zeros (`--kbo-weight0`, `--kbo-weight0-unary` in `SequentialMain.hs:107-114`) allow one unary symbol weight `0` (useful for group inverse or successor towers) while preserving admissibility.
  2. **Model-Relativized `KBO` (`KBO.lessIn`, `KBO.hs:78-153`):** To check whether $t \prec_{\mathrm{kbo}} u$ holds under a partial total-ordering assumption `Model f` over variables, `sizeLessIn` (`KBO.hs:85-98`) evaluates the linear difference polynomial $\Delta(x_1, \dots, x_m) = k + \sum c_i x_i$ (`size(u) - size(t)`), folding `minimumIn model` over ordered variable groups (`scanr1 (+) coeffs`) against minimal Skolem sizes `size lo` / `size hi` (`lines 100-124`). Similarly, `LPO.lessIn` (`LPO.hs:77-107`) evaluates lexicographic path ordering directly under variable order constraints `lessEqInModel`.
- **Peak Tracking, Connectedness Below Peak, and Ground-Joinability (`Twee/Join.hs:54-249`, `Twee/CP.hs:72-85`):**
  - Every critical overlap records its unifying peak term `overlap_top` / `cp_top` (`CP.hs:82, 180`), feeding `allSteps` (`Join.hs:76-121`):
    1. `step1` normalizes both sides using strictly oriented rules;
    2. `step2` normalizes using all rules whenever simpler and strictly decreasing;
    3. `checkOrder` (`lines 81-87`) **immediately discards any critical pair where `lessEq top t || lessEq top u`** (meaning the rewrite did not stay strictly below the peak);
    4. `step3` (`lines 96-121`) tests **connectedness below `top`** (`normaliseWith (lessThan top)`) in both original and variable-flipped orientations (`flipCP`).
  - If `allSteps` fails to join $t \approx u$ universally, `groundJoin` / `groundJoinFrom` (`Join.hs:173-249`) exhaustively case-splits over total ground variable orderings `ctx` (`Branches`). Whenever a candidate model `model` fails to join $t$ and $u$ below `top`, `optimise weakenModel` (`lines 198-201`) minimizes the counterexample model to the weakest literal conjunction sufficient for non-joinability and adds its negated diagonal `diag (modelToLiterals model')` (`lines 203-207`) to the branch context—splitting the remaining ground instances until either all instances join (discarding the redundant equation) or a non-joinable ground counterexample survives. As confirmed in Probe Part 1 on an Abelian involution monoid, enabling ground-joinability (`ground_join=True`) pruned **`12`** critical pairs mid-search and reduced generated CPs (`108` vs. `114`) and remaining queue backlog (`44` vs. `63`) at `12` active rules compared to `ground_join=False`.
- **Internal LCF Proof Certification (`Twee/Proof.hs:49-127, 549-558`):** `Twee` constructs an opaque `Proof f` type whose sole constructor is `certify :: Derivation f -> Proof f` (`Proof.hs:94-120`), recursively checking `UseLemma`, `UseAxiom`, `Refl`, `Symm`, `Trans`, and `Cong` (`guard (u1 == u2)` at line 113) before emitting human-readable proofs or formal TSTP derivations (`--formal-proof --tstp`, `SequentialMain.hs:95-98`), with `checkProvedGoal` (`Proof.hs:549-558`) verifying Skolem witness instantiations.

### 2. Dependency Pairs, Matrix/Arctic Interpretations, and Isabelle/HOL `CPF` Certification (`IsaFoR` / `CeTA`)

`Basis: normative + documentation`

While `KBO` and `LPO` terminate efficiently in micro-second term comparisons, they require full context monotonicity ($s \succ t \implies f(\dots, s, \dots) \succ f(\dots, t, \dots)$) and syntactic precedence compatibility, failing on self-distributive, nested accumulator, or division/GCD rewrite systems such as `quot(s(x), s(y)) -> ...` or mutual recursion.

- **Dependency Pair (`DP`) Framework (`Arts & Giesl, TCS 2000`, `DOI: 10.1016/S0304-3975(99)00207-8`):** Given a TRS $\mathcal{R}$ partitioned into defined root symbols $\mathcal{D}$ and constructors $\mathcal{C}$, every rule $f(l_1, \dots, l_n) \to r$ generates a dependency pair $f^\sharp(l_1, \dots, l_n) \to g^\sharp(t_1, \dots, t_m)$ for each subterm $g(t_1, \dots, t_m)$ of $r$ with $g \in \mathcal{D}$. Infinite rewrite sequences correspond 1-to-1 with infinite minimal **$\mathcal{R}$-dependency chains**. Decomposing the approximated dependency graph into Tarjan **Strongly Connected Components (`SCCs`)** isolates independent termination subproblems that only require **weakly monotonic** reduction pairs $(\gtrsim, \succ)$ satisfying rule compatibility $\mathcal{R} \subseteq {\gtrsim}$ and strict orientability on at least one pair per SCC cycle—eliminating the subterm property required by `KBO`/`LPO`.
- **Matrix and Arctic Semiring Interpretations (`IsaFoR` / `CeTA` `v3.9`):** Automated termination provers encode reduction pairs into SAT/SMT solvers via algebraic interpretations:
  - **Standard Linear/Matrix Interpretations over $(\mathbb{N}^d, +, \times)$:** Each $k$-ary symbol $f$ maps to $\sum_{i=1}^k M_i \vec{x}_i + \vec{v}_f$ with $M_i \in \mathbb{N}^{d \times d}$ and $\vec{v}_f \in \mathbb{N}^d$. Weak monotonicity holds automatically when all matrix entries are $\ge 0$; strict decrease in the first coordinate holds when $(M_i)_{1,1} \ge 1$ for usable arguments, orienting length/nesting exchanges that defeat single-polynomial or `KBO` weights.
  - **Arctic Matrix Interpretations over $(\mathbb{Z} \cup \{-\infty\}, \max, +)$:** Replacing $(+, \times)$ by the **arctic semiring** $a \oplus b = \max(a, b)$ and $a \otimes b = a + b$ (identity $0$ for $\otimes$, $-\infty$ for $\oplus$, requiring $(M_i)_{1,1} \ge 0$ for weak monotonicity and strict inequality under $>_{-\infty}$) turns matrix multiplication into max-plus linear recurrences. Arctic matrices orient exponential-like or non-polynomial length-preserving string/term systems that standard $\mathbb{N}$-matrices cannot orient at small dimensions ($d \le 3$).
- **Certified `CPF` Replay via `IsaFoR` / `CeTA` (`DOI: 10.1007/978-3-642-03359-9_31`, `DOI: 10.4204/EPTCS.167.8`):** Rather than trusting complex termination provers (`AProVE`, `TTT2`, `NaTT`, `CSI`, or SAT/SMT matrix synthesizers), provers export declarative XML certificates in the **Certification Problem Format (`CPF`)** recording the exact DP graph decomposition, usable rules, synthesized matrices/arctic matrices/KBO precedences, or critical-pair joinability trees for confluence and completion. `CeTA` (`v3.9`) is extracted directly from Isabelle/HOL (`IsaFoR`, including `First_Order_Terms` and `Knuth_Bendix_Order` sessions) via Isabelle's code generator to Haskell (`GHC`). Checking an exported `CPF` file reduces to deterministic algebraic matrix/order inequality checking (comparing $M_1 M_2$ entries and testing overlap joinability), completely excluding SAT/SMT search, heuristic SCC pruning, and C++/OCaml prover bugs from the Trusted Computing Base (`TCB`).

### 3. Relational Congruence Closure, Hypertree Free Join, and Rebuilding (`egglog`)

`Basis: normative + source`

Where `Twee` destructively commits to one term orientation to reach confluence, `egraphs-good/egglog` (`d89bc58a`, `DOI: 10.1145/3591239`) performs **non-destructive equality saturation** unified with Datalog fixed-point evaluation:

- **Tables with Functional Dependencies and Lattice Merges:** Each constructor $f(x_1, \dots, x_k) : S$ is stored as a relational table of `(x_1, ..., x_k, id)` tuples paired with a functional dependency $(x_1, \dots, x_k) \to \mathrm{id}$. Equalities merge output IDs in a disjoint-set union-find table (`core-relations/src/uf`), while lattice-valued relations resolve functional-dependency conflicts monotonically via user-supplied `:merge` functions (`(old, new) -> merged`) rather than equivalence classes alone.
- **Query Planning via Hypertree Decomposition & Free Join (`core-relations/src/free_join/plan.rs:1-46`, `execute.rs:1-200`):** Multi-atom left-hand sides of rewrite rules compile through a two-stage query planner:
  1. **(Hyper)tree Decomposition (`plan.rs:6-26`):** Variables become hypergraph vertices and relation atoms become hyperedges. Min-fill variable elimination (`next_var_to_eliminate`) decomposes cyclic rules into a tree of bags (subqueries), pruning subsumed bags and scheduling inter-bag message materializations unless disabled (`set_no_decomp` in `egglog-bridge/src/rule.rs:116`).
  2. **Free Join Execution (`plan.rs:27-46`, `execute.rs:65-200`):** Inside each bag, `Free Join` generalizes binary hash joins and Worst-Case Optimal Generic Join (`PlanStrategy::Gj` vs. `PureSize`/`MinCover`) by picking a cover sub-atom and probing shared `TrieCache` packed tries allocated in a single `SharedArena` (`execute.rs:179-197`), re-ordering recursive join tails dynamically (`DVO` in `join_tail.rs`) and splitting root scans into work-stealing `TopLevelPartition` shards (`IndexShard`, `IndexRange`, `CoverRange` in `execute.rs:134-148`).
- **Adaptive Incremental Rebuilding (`core-relations/src/table/rebuild.rs:43-250`):** After unions update canonical IDs, e-graphs must restore **congruence** ($a \equiv b \implies f(a) \equiv f(b)$). `SortedWritesTable::do_rebuild` skips index updates below `MIN_INCREMENTAL_REBUILD_ROWS` (`lines 63-65`), compares dirty-ID subset counts against table size using a hysteresis budget (`incremental_rebuild(to_scan.size(), stale, rows, &mut self.full_scan_credit)`, `line 71`), and branches between dirty-ID `rebuild_index` lookups (`rebuild_incremental`, lines 119–206) and coarse `STEP_SIZE = 2048` parallel table scans (`rebuild_nonincremental`, lines 208–250).
- **Ground Proof Checking (`egglog/src/proofs/proof_checker.rs:1-159`):** When proof production is enabled, `egglog` records rule applications and verifies them via `proof_checker.rs`, replaying `Let`, `Union`, `Set`, and `:merge` evaluations (`run_merge`, lines 65–92) and container side conditions (`is_container_side_condition`, lines 27–39) into bidirectional ground `Proposition` equalities. Unlike `CeTA`, `proof_checker.rs` checks ground equality steps inside unverified Rust rather than an LCF proof-assistant kernel.

### 4. NP-Hard E-Graph DAG Extraction: Cycle-Cutting ILP vs. Cyclic Monotone Boolean Circuits & Treewidth DP (`extraction-gym` & `arXiv:2408.17042`)

`Basis: source + execution + derived`

Saturating an e-graph leaves exponentially many equivalent terms encoded compactly across shared e-classes. Selecting an optimal concrete expression exposes a fundamental complexity chasm:

- **Tree Cost vs. DAG Cost:** `egglog`'s built-in `TreeExtractor` (`egglog/src/extract.rs:217-315`) implements Bellman–Ford relaxation over flattened `FuncData` row arrays under `DEFAULT_COST_MODEL` (`TreeCostModelFromDag<AdditiveCostModel>`), solving **minimum tree cost** (counting shared subexpressions once per occurrence) in polynomial time. However, whenever shared DAG nodes (common subexpressions, circuit gates, or tensor factors) are charged **once globally** (`DagCostModel`), optimal DAG extraction becomes **NP-hard** and APX-hard (hard to approximate within any constant factor; `Sun, Zhang, Ni 2024`, `arXiv:2408.17042`), and `TreeExtractor` selects exponentially suboptimal trees ($O(2^d)$ vs. $O(d)$) on shared diamonds.
- **The Zero-Grounded Cycle Paradox & Iterative Cycle-Banning ILP (`extraction-gym/src/extract/faster_ilp_cbc.rs:1-220`):** Formulating DAG extraction as a binary Integer Linear Program introduces binary variables `class.active` and `node.variable` requiring: (i) root classes active, (ii) every active class selects $\ge 1$ node, and (iii) every selected node activates all its child classes. Crucially, these local constraints **admit invalid self-supporting cycles** ($c_a \xrightarrow{n_1} c_b \xrightarrow{n_2} c_a$) disconnected from ground leaves, achieving strictly lower bogus cost than any valid term (verified in Probe Part 2A: naive cyclic cost `2.0` vs. true acyclic DAG cost `16.5` vs. tree cost `31.5`). `faster_ilp_cbc.rs` combats this in two ways:
  1. **E-Graph Preprocessing (`Config`, lines 57–89):** `pull_up_costs`, `remove_self_loops`, `remove_high_cost_nodes`, `remove_more_expensive_subsumed_nodes`, `pull_up_single_parent`, `take_intersection_of_children_in_class`, and `remove_single_zero_cost` shrink the e-graph before solving.
  2. **Incremental Cycle-Banning Cuts (`faster_ilp_cbc.rs:14-46`):** Rather than encoding $O(|V|)$ topological level variables (which inflate LP relaxations), `faster_ilp_cbc.rs` solves the cycle-unconstrained ILP, runs cycle DFS on the extracted subgraph, adds explicit cycle-prohibiting constraints ($\sum_{e \in C} x_e \le |C| - 1$), and re-invokes `coin_cbc::Model` from scratch—noting explicitly (`lines 21-22`) that COIN-OR CBC lacks warm-start incremental cut callbacks, causing severe instances to run past **`> 36,000 s` (10 hours)** (`lines 4, 175`).
- **Equivalence to Cyclic Monotone Boolean Circuits & $2^{O(w^2)} \mathrm{poly}(w, n)$ Treewidth DP (`glenn-sun/egg-extraction-gym` @ `8be08032`, `arXiv:2408.17042`):**
  1. **Circuit Isomorphism (`circuit.rs:8-21`):** An e-graph translates directly into a **cyclic monotone Boolean circuit**: each e-class becomes a `Gate::Or` gate, each multi-child e-node becomes a `Gate::And` gate fed by its child e-class `Or` gates plus a weighted `Gate::Variable` (`cost` in `env.rs:111-133`, adding an $\epsilon = 10^{-5}$ tie-breaking floor to zero-cost variables so redundant zero-cost branches are not gratuitously enabled). Under **well-founded (minimal) monotone circuit evaluation**—requiring every `true` vertex to have an acyclic derivation tree of `true` predecessors down to `Gate::Variable`s—finding the minimum-weight satisfying assignment with `root_id = true` is **exact optimal DAG extraction**.
  2. **Treewidth DP (`treewidth.rs:79-250`, `summary.rs:7-342`):** Converting the undirected circuit graph (`Circuit::to_graph`, `circuit.rs:107-115`) via `arboretum_td` into a rooted **nice tree decomposition** (`NiceBag::{Leaf, Insert, Forget, Join}`) of width $w$, `compute_dpmap_by_group` stores dynamic-programming states `Summary(bag_eval, is_known, transitive_graph)` per bag:
     - `bag_eval`: current Boolean assignment (`T`/`F`) of bag vertices;
     - `is_known` (`KnownTag`, `summary.rs:144-223`): tags whether each `true` vertex in the bag has already witnessed all inputs (`And`) or $\ge 1$ `true` input (`Or`) before leaving the bag at `Forget`;
     - `transitive_graph` (`TransitiveGraph`, `summary.rs:228-341`): maintains transitive reachability among `true` vertices crossing the bag boundary, rejecting any `Insert` or `Join` state where `has_cycle()` detects a back-edge self-loop (`treewidth.rs:154, 229`).
     Because the number of transitive reachability graphs and truth assignments on a bag of size $\le w+1$ is $2^{O(w^2)}$, optimal DAG extraction runs in **$2^{O(w^2)} \mathrm{poly}(w, n)$** time—polynomial in e-graph size $n$ for fixed treewidth $w$!
  3. **Circuit Sweeping & Source-Level Self-Loop Defect (`env.rs:140-423`, `circuit.rs:63-79`):** Before tree decomposition, `Env::simplify` runs fixpoint Boolean circuit sweeping (`remove_unreachable`, `contract_indegree_one`, `contract_same_gate`, `remove_lone_or_loops` breaking cycles containing only a single `Or` gate, `same_gate_is_tree`, `distributivity` factoring common grandinputs, and `collect_variables` merging identical-fanout variable gates). **Source Audit Finding (`Basis: source + execution`):** Inside `Circuit::contract_edge_remove_out(u, v)` (`circuit.rs:63-79`), when contracting `u -> v` into `u`, lines 69–72 read:
     ```rust
     if u != w {
         self.add_edge(u, w);
     }
     self.add_edge(u, w);
     ```
     Line 72 unconditionally calls `self.add_edge(u, w)` even when `u == w`, defeating the `if u != w` guard immediately above it! Whenever a 2-cycle `u -> v -> u` (`outputs(v)` contains `u`) undergoes `contract_indegree_one` or `contract_same_gate`, line 72 injects a spurious self-loop `u -> u` (`Probe Part 2B`), which breaks acyclicity invariants unless `remove_lone_or_loops` subsequently deletes `u` or `TransitiveGraph::insert_vertex` (`summary.rs:257-260`) skips self-loops.

### 5. Cross-System Matrix & Reproducible Execution Probe

`Basis: source + execution`

| Dimension | `Twee` (`9f56b26a`) | `IsaFoR / CeTA` (`v3.9`) | `egglog` (`d89bc58a`) | `extraction-gym` (`903ba0f8`) | `egg-extraction-gym` (`8be08032`) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Core Problem** | Equational refutation / completion | Termination, confluence & completion verification | Relational Datalog + equality saturation | Heuristic & exact ILP DAG extraction | Exact DAG extraction via monotone circuit treewidth |
| **Representation** | Flatterms (`PackedSequence`) + `RuleIndex` | First-order TRS + XML `CPF` proof DAG | Columnar relations + `TrieCache` + union-find | JSON e-graph + `coin_cbc` binary ILP | Cyclic monotone `Circuit` (`Or`/`And`/`Variable`) + `NiceBag` |
| **Ordering / Cost** | `KBO` / `LPO` + `Model`-relativized `lessIn` | DP SCCs + polynomial/matrix/arctic semirings | `:cost` `DefaultCost` (`u64`) + `TreeExtractor` | `Cost` (`NotNan<f64>`) + `FasterCbcExtractor` | `Cost` (`epsilon=1e-5` bias) + `TreewidthExtractor` |
| **Cycle Handling** | Peak-bounded reduction (`< cp_top`) + `groundJoin` | Well-foundedness proven per DP SCC | Non-destructive congruence cycles in union-find | Iterative cycle-banning CBC cuts (no warm start) | Well-founded `KnownTag` + `TransitiveGraph` DP |
| **Assurance Model** | Internal LCF `certify` + TSTP output | Isabelle/HOL-verified Haskell `CeTA` binary | Internal Rust `proof_checker.rs` (ground eqs) | Unverified Rust (`ExtractionResult::check`) | Unverified Rust (`circuit.rs:72` self-loop bug) |

Inspecting `egraphs-good/extraction-gym/test_data/fuzz/` (`Basis: source`) confirms compact cyclic e-graphs typical of extraction benchmarks: e.g. `1.json` (`13` e-classes, `76` e-nodes, `284` child edges), `10.json` (`7`, `38`, `81`), `11.json` (`6`, `24`, `25`), `12.json` (`9`, `32`, `50`), and `13.json` (`6`, `40`, `91`).

Running the self-contained Python 3.13.15 probe (`## Evidence`) produces:
1. **Unfailing Completion (`Abelian Involution Monoid`, `Basis: execution`):** At `12` active rules, `ground_join=False` requires `56` queue pops, generates `114` critical pairs, and leaves `63` queued CPs (`0` ground-joined); enabling `ground_join=True` prunes **`12`** critical pairs via exhaustive variable-ordering joinability below `cp_top`, reducing total generated CPs to `108` (`-5.3%`) and remaining backlog to `44` (`-30.2%`).
2. **Tree vs. Naive-Cyclic vs. Acyclic DAG Extraction (`Basis: execution`):** On a 4-eclass cyclic e-graph (`c_root`, `c_a`, `c_b`, `c_leaf`):
   - Bellman–Ford **tree-cost** optimum = **`31.5`** (double-counting `c_a + c_leaf = 15.0` across `combine(c_a, c_b)` where `c_b -> step_a(c_a)`);
   - Unconstrained **cyclic** minimum = **`2.0`** (selecting the detached cycle `c_a <-> c_b` of weight `0.5 + 0.5 + 1.0`, violating well-foundedness);
   - True optimal **acyclic DAG** cost = **`16.5`** (`c_root -> combine(c_a, c_b)`, `c_b -> step_a(c_a)`, `c_a -> double(c_leaf)`, `c_leaf -> x`).
3. **Self-Loop Bug Reproduction (`Basis: execution`):** Contracting 2-cycle `1 -> 2 -> 1` (with `1 -> 0`) via `contract_edge_remove_out(1, 2)` leaves `inputs[1] = [1]` and `outputs[1] = [0, 1]` (`spurious_self_loop=True`) strictly due to line 72's duplicate `add_edge`.

### 6. Six-Level Performance & Resource Footprint Analysis (L1–L6)

`Basis: source + execution + derived`

| Level | `Twee` (`9f56b26a`) | `IsaFoR / CeTA` (`v3.9`) | `egglog` (`d89bc58a`) | `extraction-gym` ILP & Circuit Treewidth |
| :--- | :--- | :--- | :--- | :--- |
| **(L1) Human & Agent Authoring Velocity** | Very fast problem authoring: declarative TPTP `cnf(..., axiom, ...)` equations with zero manual order hints (`--kbo-weight0` automatic); `Twee` itself is ~4–6 KLoC of Haskell. | Highest formalization cost (`IsaFoR` spans tens of thousands of Isabelle/HOL LoC across `First_Order_Terms`, matrix, arctic, and DP theories), amortized across all external tools exporting `CPF` XML. | Concise declarative rules (`(rewrite ...)`, `(rule ...)` with lattice `:merge`), freeing authors from orienting cyclic algebraic laws (`x + y = y + x`). | Cost models (`DagCostModel`) are 10–30 lines; writing ILP/treewidth extractors is nontrivial (`faster_ilp_cbc.rs` `1,251` lines; `treewidth.rs` `573` + `env.rs` `424` + `summary.rs` `342` lines). |
| **(L2) Framework & Toolchain Build Time** | Cabal/GHC build (`twee.cabal`) compiles in tens of seconds (`-fllvm` optional backend); `--DUSE_LPO` toggles KBO/LPO at compile time (`SequentialMain.hs:22`). | Building full `IsaFoR` Isabelle heap images from AFP + generating Haskell + GHC compiling `CeTA` takes many minutes to ~1 hour cold, mitigated by downloading prebuilt `v3.9` binaries. | Rust Cargo workspace (`egglog` + `core-relations` + `egglog-bridge`); clean release builds compile in `~30–90 s`, incremental rebuilds `<5 s`. | `extraction-gym` builds quickly in Rust once system `libcbc-dev` C++ bindings link (`ilp-cbc` feature); `arboretum_td` is pure Rust. |
| **(L3) Compilation, Elaboration & Synthesis Latency** | Millions of rewrite steps/sec via flatterm indexing; ground-joinability loops over variable-order branches (`cfg_ground_join_limit`) trading per-CP microseconds to avoid queue blowup. | Search occurs *outside* `CeTA` (external SAT/SMT matrix synthesis takes ms–minutes); `CeTA` replays witnesses without backtracking. | `Free Join` + `SharedArena` `TrieCache` + parallel `TopLevelPartition` (`MIN_TOP_COVER_ROWS_PER_PARTITION = 256`, `TOP_INDEX_RANGES_PER_WORKER = 32`) saturate thousands of rules in ms–seconds; `do_rebuild` switches incrementally vs. `STEP_SIZE = 2048` scans. | Greedy DAG heuristics run in ms; `FasterCbcExtractor` hits **`>36,000 s`** (`10 hr`) timeouts on hard cyclic graphs due to non-incremental CBC restarts; `TreewidthExtractor` runs in ms–seconds for $w \le 6\text{--}8$ but hits a $2^{\Theta(w^2)}$ exponential wall once $w \gtrsim 10\text{--}12$. |
| **(L4) Generated Code Execution Performance** | Completed confluent TRSs normalize terms deterministically in $O(\text{steps})$ with zero search; unfailing completion emits static equational lemmas (`Twee/Proof.hs`). | Certified terminating TRSs bound runtime rewrite lengths (e.g., linear/polynomial/exponential bounds from matrix/arctic degrees); `CeTA` itself runs offline and imposes 0 target runtime cost. | `egglog` acts as optimizer/analyzer rather than target runtime; its extracted DAG terms directly reduce target runtime gates, FLOPs, or instruction latency via shared subexpressions. | Optimal DAG extraction directly reduces generated circuit area/instruction count relative to Bellman–Ford `TreeExtractor` (e.g., `16.5` vs `31.5` in Probe Part 2A). |
| **(L5) Proof / Certificate Verification Speed** | Internal `Proof.certify` verifies derivations in milliseconds; `--formal-proof --tstp` emits checkable TSTP steps; `Twee` does not natively emit `CPF` for arbitrary saturation without external conversion. | `CeTA` compiled GHC binary checks `CPF` XML certificates at deterministic polynomial speeds (tens–hundreds of ms for typical DP+matrix/arctic proofs, seconds for huge confluence proofs) with Isabelle/HOL kernel guarantees. | `proof_checker.rs` verifies ground `ProofStore` justifications by re-evaluating actions/merges in Rust; faster than theorem provers, though uncertified (`TCB` includes Rust `proof_checker.rs` + `egglog` AST). | `ExtractionResult::check` (`extraction-gym/src/extract/mod.rs:75-106`) checks root coverage, e-class match, and cycle DFS (`find_cycles`) in $O(|V| + |E|)$ `<1 ms`, verifying **validity** (acyclicity), not optimality! |
| **(L6) RAM, Disk & Binary Footprints** | `Data.PackedSequence` packs rule sequences into strict `ByteString`s (`PackedSequence.hs:17-36`); `How` packs direction+position into 1 `Int32` (`CP.hs:103-118`), keeping active-set RSS small (`tens–hundreds MB`). | Isabelle proof heaps require multi-GB RAM/disk during `IsaFoR` formalization, while released `CeTA` native binaries are compact (`tens of MB`); XML `CPF` files grow to `MB`–`tens of MB` on large proofs. | Columnar `core-relations` buffers + `SharedArena` packed tries minimize pointer chasing; `TrieCache` shares roots across plans (`execute.rs:193-197`) while avoiding `DashMap` overhead on single-plan roots. | `faster_ilp_cbc.rs` duplicates `ClassILP` vectors + `libcbc` branch-and-bound LP trees; `TreewidthExtractor`'s `DPMapByGroup` (`FxHashMap<Evaluation, FxHashMap<Summary, Trace>>`, `treewidth.rs:76`) explodes in RAM as $O(2^w \cdot 2^{w^2})$ when bag size $w+1$ grows. |

### 7. Human Comprehensibility (C1) & Conceptual Simplicity / Model Refinement (C2)

`Basis: source + derived`

- **(C1) Human Comprehensibility & Mental-Model Ergonomics:**
  - *Completion opacity vs. equational proof presentation:* Humans easily read finite oriented rewrite steps (`a * e -> a`), yet unfailing completion's critical-pair queues, model-relativized `KBO` variable-group inequalities (`minimumIn model`), and ground-joinability splitting are notoriously opaque when a problem diverges. `Twee` counteracts this by separating search from presentation: `present` (`Twee/Proof.hs:564-580`) post-processes the `certify`-validated DAG via `flattenDerivation`, lemma generalization, and definition elimination so humans inspect linear equational chains rather than raw `RuleIndex` states.
  - *Certificate & extraction legibility:* Raw XML `CPF` certificates (`>10k` lines of nested `<matrixInterpretation>` tags) are machine-auditable rather than human-readable, whereas `extraction-gym`'s `faster_ilp_cbc.rs` fails silently into `>10`-hour timeouts without explaining *which* symmetric e-graph cycle prevents LP relaxation tightness. By contrast, `glenn-sun/egg-extraction-gym`'s circuit view (`env.rs:55-106` `save_cosmograph` coloring `And` red, `Or` green, `Variable` blue) makes cycle obstructions and gate-sweeping simplifications directly inspectable—though bugs like `circuit.rs:72` highlight how subtle edge-contraction invariants remain error-prone even on small graphs.
- **(C2) Conceptual Simplicity, Orthogonality & Universal Model Refinement:**
  - *Completion vs. Congruence Closure as Two Cuts Through Quotiented Fixpoints:* Unfailing `KBC` and `egglog` optimize opposite sides of the same algebraic problem: computing consequences modulo an equational congruence $\approx_E$. `KBC` serializes $\approx_E$ into a **terminating directed quotient** via a reduction order $\succ$ (paying exponential `CP` orientation complexity to gain linear normal-form uniqueness), whereas `egglog` freezes the **entire cyclic congruence graph** via relational union-find + semi-naive `Free Join` (paying zero orientation complexity up front, deferring term choice to post-saturation extraction).
  - *Minimal Monotone Circuit SAT as the Universal Extraction Model:* Viewing e-graph extraction as **well-founded minimum-weight monotone Boolean circuit satisfaction** (`arXiv:2408.17042`) achieves true conceptual unification (Ousterhout deep-module compression): tree extraction, DAG extraction, common-subexpression sharing, and cycle avoidance collapse into one two-predicate semantics (*monotone gate satisfaction* + *well-founded reachability* via `KnownTag` and `TransitiveGraph`), turning ad-hoc e-graph pruning passes (`faster_ilp_cbc.rs`'s 12 `Config` flags) into standard Boolean gate sweeping (`env.rs`).

## Boundaries

- **Completeness of unfailing `KBC` (`known not to apply` for general decision):** Refutational completeness guarantees finding a proof *if* a ground/Skolemized equation holds, assuming fairness; on unprovable statements or non-terminating equational theories, `Twee` diverges or hits resource limits rather than deciding equivalence.
- **Native Associative-Commutative (`AC`) matching (`unsupported` in `Twee` core):** Unlike AC-unification provers (`E`, `Vampire` AC extensions), `nick8325/twee` handles AC axioms via unfailing completion + `groundJoin` connectedness rather than built-in `AC` term indexing and unification.
- **`CeTA` certification of `egglog` lattice `:merge` or DAG optimality (`unsupported`):** `IsaFoR`/`CeTA` `v3.9` certifies TRS termination, complexity, confluence, and equational completion in `CPF` XML, not `egglog` lattice `:merge` relational programs or optimality guarantees of extracted e-graph DAGs (`egglog`'s internal `proof_checker.rs` checks ground equality validity only, and `ExtractionResult::check` checks validity/acyclicity without optimality proofs).
- **High-treewidth e-graphs (`known not to apply` for fast exact treewidth DP):** The $2^{O(w^2)} \mathrm{poly}(w, n)$ complexity of `glenn-sun/egg-extraction-gym` scales rapidly only when circuit sweeping keeps treewidth $w \le 8\text{--}10$; on dense AC-saturated arithmetic meshes or global crossbar expressions with high treewidth ($w \gtrsim 12$), `DPMapByGroup` exhausts time/RAM and cannot beat ILP or greedy heuristics (`faster_greedy_dag`).
- **Binary execution of `CeTA`, `Twee`, and `extraction-gym` (`not examined`):** All source analyses of `nick8325/twee`, `egraphs-good/egglog`, `egraphs-good/extraction-gym`, and `glenn-sun/egg-extraction-gym` derive from direct source reading (`Basis: source`) paired with the self-contained Python simulation (`Basis: execution`) and inspection of `extraction-gym/test_data/fuzz/` fixtures; live `ghc`/`cargo`/`coin-cbc`/`ceta` binary runs were not executed in this environment.
- **Exact status of `circuit.rs:72` fix upstream (`unknown` outside pinned commit):** Commit `8be08032d5cbea021ca1d841c103be0afe02644a` of `glenn-sun/egg-extraction-gym` exhibits the unconditional duplicate `self.add_edge(u, w)` on line 72; whether later forks or `Treewidth2Extractor` (`treewidth2.rs`) resolve or bypass all downstream self-loop interactions across arbitrary `extraction-gym` benchmarks was not tested by Rust execution (`not examined`).

## Evidence

- **Primary Source Repositories & Exact Citations:**
  - `nick8325/twee` @ `9f56b26a9b09ea508ff944702b88d60db48c4cb9`: `src/Twee.hs` (`Config`, `State` lines 55–185), `src/Twee/KBO.hs` (`lessEqSkolem` 15–38; `lessEq` 41–72; `lessIn`, `sizeLessIn`, `minimumIn`, `lexLessIn` 78–153), `src/Twee/LPO.hs` (`lessEqSkolem` 10–29; `lessEq` 55–75; `lessIn` 77–107), `src/Twee/CP.hs` (`positionsRule` 54–59; `Overlap` 72–85; `overlapAt'` 174–190), `src/Twee/Join.hs` (`joinCriticalPair`, `allSteps`, `step1`–`step3`, `checkOrder`, `groundJoin`, `groundJoinFrom` lines 39–249), `src/Twee/Proof.hs` (`Proof`, `Derivation`, `certify` 49–127; `checkProvedGoal` 549–558; `present` 564–580), `src/Data/PackedSequence.hs` (lines 17–50), `executable/SequentialMain.hs` (`MainFlags` & CLI options lines 50–120; `#ifdef USE_LPO` 22–24).
  - `IsaFoR / CeTA` `v3.9` (`https://cl-informatik.uibk.ac.at/software/ceta/`, `DOI: 10.1007/978-3-642-03359-9_31`, `DOI: 10.4204/EPTCS.167.8`) & AFP entries (`First_Order_Terms`, `Knuth_Bendix_Order`).
  - `egraphs-good/egglog` @ `d89bc58adc9b9a87a8f571c5b9ad75d686d226e6`: `src/extract.rs` (`Cost`, `MonoidCost`, `DagCostModel`, `TreeCostModel`, `DEFAULT_COST_MODEL`, `TreeExtractor` lines 22–360), `src/proofs/proof_checker.rs` (`is_container_side_condition` 27–39; `run_merge` 65–92; `process_actions` 100–159), `core-relations/src/free_join/plan.rs` (hypertree decomposition + Generic Join vs. Free Join lines 1–46), `core-relations/src/free_join/execute.rs` (`top_cover_partitions`, `top_index_range_partitions`, `TopLevelPartition`, `SharedArena`, `TrieCache` lines 65–200), `core-relations/src/table/rebuild.rs` (`do_rebuild`, `rebuild_incremental`, `rebuild_nonincremental`, `STEP_SIZE = 2048` lines 43–250), `egglog-bridge/src/rule.rs` (`Query::no_decomp` lines 95–117).
  - `egraphs-good/extraction-gym` @ `903ba0f818b50608fe20ae9e0f03c35cb27bc50a`: `src/extract/mod.rs` (`EPSILON_ALLOWANCE`, `ExtractionResult::check`, `find_cycles` lines 18–120), `src/extract/faster_ilp_cbc.rs` (cycle-cutting architecture & CBC non-incremental restart note lines 1–46; `Config` flags 57–89; `FasterCbcExtractorWithTimeout` >10 hr timeout comment 4, 173–190), `test_data/fuzz/{1,10,11,12,13}.json` (inspected exact sizes).
  - `glenn-sun/egg-extraction-gym` (`glenn-treewidth`) @ `8be08032d5cbea021ca1d841c103be0afe02644a`: `src/extract/treewidth/circuit.rs` (`Circuit`, `Gate::{Variable, Or, And}` lines 8–21; `contract_edge_remove_out` lines 63–79 showing duplicate `self.add_edge(u, w)` on line 72; `to_graph` 107–115), `src/extract/treewidth/env.rs` (`SimplifyOptions` 4–28; `compute_costs` $\epsilon=10^{-5}$ 111–133; `simplify` sweeping passes 140–423), `src/extract/treewidth/summary.rs` (`Summary`, `Evaluation`, `KnownTag`, `TransitiveGraph` lines 7–342), `src/extract/treewidth.rs` (`NiceBag`, `DPMapByGroup`, `compute_dpmap_by_group` lines 76–250), `src/extract/treewidth2.rs` (`Treewidth2Extractor` lines 1–160).
- **Peer-Reviewed Papers & Preprints:** Bachmair, Dershowitz & Plaisted, *Completion without failure* (1989); Arts & Giesl, *TCS 2000* (`DOI: 10.1016/S0304-3975(99)00207-8`); Thiemann & Sternagel, *TPHOLs 2009* (`DOI: 10.1007/978-3-642-03359-9_31`); Sternagel & Thiemann, *UITP 2014* (`DOI: 10.4204/EPTCS.167.8`); Smallbone, *CADE 2021* (`DOI: 10.1007/978-3-030-79876-5_35`); Zhang et al., *PLDI 2023* (`DOI: 10.1145/3591239`); Sun, Zhang & Ni, *E-Graphs as Circuits, and Optimal Extraction via Treewidth* (`arXiv:2408.17042`).
- **Self-Contained Reproducible Probe (Python 3.13.15, exited `0`):**

```bash
python3 - <<'EOF'
from __future__ import annotations
from dataclasses import dataclass
import itertools, math

@dataclass(frozen=True)
class Var:
    name: str
@dataclass(frozen=True)
class App:
    fn: str; args: tuple[Term, ...]
Term = Var | App
PREC = {"e": 4, "f": 5, "i": 6}

def tvars(t: Term) -> dict[str, int]:
    if isinstance(t, Var): return {t.name: 1}
    r: dict[str, int] = {}
    for a in t.args:
        for k, v in tvars(a).items(): r[k] = r.get(k, 0) + v
    return r

def tsize(t: Term) -> int:
    return 1 if isinstance(t, Var) else 1 + sum(tsize(a) for a in t.args)

def kbo_gt(s: Term, t: Term, sk=None) -> bool:
    if s == t: return False
    if sk is None:
        vs, vt = tvars(s), tvars(t)
        if any(vs.get(v, 0) < c for v, c in vt.items()): return False
    ss, st = tsize(s), tsize(t)
    if ss != st: return ss > st
    if isinstance(s, Var) and isinstance(t, Var):
        return (sk[s.name] > sk[t.name]) if sk is not None else False
    if isinstance(s, Var): return False
    if isinstance(t, Var): return True
    if PREC[s.fn] != PREC[t.fn]: return PREC[s.fn] > PREC[t.fn]
    for a, b in zip(s.args, t.args):
        if a != b: return kbo_gt(a, b, sk)
    return False

def subst(t: Term, s: dict[str, Term]) -> Term:
    return s.get(t.name, t) if isinstance(t, Var) else App(t.fn, tuple(subst(a, s) for a in t.args))

def match(p: Term, t: Term, s: dict[str, Term]) -> dict[str, Term] | None:
    if isinstance(p, Var):
        return (s if s[p.name] == t else None) if p.name in s else {**s, p.name: t}
    if isinstance(t, Var) or p.fn != t.fn or len(p.args) != len(t.args): return None
    c = s
    for a, b in zip(p.args, t.args):
        c = match(a, b, c)
        if c is None: return None
    return c

def unify(t1: Term, t2: Term, s: dict[str, Term]) -> dict[str, Term] | None:
    t1, t2 = subst(t1, s), subst(t2, s)
    if t1 == t2: return s
    if isinstance(t1, Var):
        if t1.name in tvars(t2): return None
        return {**{k: subst(v, {t1.name: t2}) for k, v in s.items()}, t1.name: t2}
    if isinstance(t2, Var): return unify(t2, t1, s)
    if t1.fn != t2.fn or len(t1.args) != len(t2.args): return None
    c = s
    for a, b in zip(t1.args, t2.args):
        c = unify(a, b, c)
        if c is None: return None
    return c

def ren(t: Term, suf: str) -> Term:
    return Var(t.name + suf) if isinstance(t, Var) else App(t.fn, tuple(ren(a, suf) for a in t.args))

def nf(t: Term, eqs, sk=None, top=None) -> Term:
    cur = t
    for _ in range(80):
        def rw(n: Term) -> Term | None:
            for l, r, ori in eqs:
                for lhs, rhs in ([(l, r)] if ori else [(l, r), (r, l)]):
                    m = match(lhs, n, {})
                    if m is not None:
                        cand = subst(rhs, m)
                        if (ori or kbo_gt(n, cand, sk)) and (top is None or kbo_gt(top, cand, sk)):
                            return cand
            if isinstance(n, App):
                for idx, a in enumerate(n.args):
                    na = rw(a)
                    if na is not None:
                        args = list(n.args); args[idx] = na
                        return App(n.fn, tuple(args))
            return None
        nxt = rw(cur)
        if nxt is None: break
        cur = nxt
    return cur

def ground_joinable(s: Term, t: Term, top: Term, eqs) -> bool:
    vs = sorted(set(tvars(s)) | set(tvars(t)) | set(tvars(top)))
    if len(vs) > 4: return False
    orders = [{v: r for v, r in zip(vs, p)} for p in itertools.permutations(range(len(vs)))]
    if len(vs) >= 2: orders.append({v: 0 for v in vs})
    return all(nf(s, eqs, o, top) == nf(t, eqs, o, top) for o in orders)

def run_kbc(use_gj: bool):
    x, y, z = Var("x"), Var("y"), Var("z")
    f, i = (lambda u, v: App("f", (u, v))), (lambda u: App("i", (u,)))
    e = App("e", ())
    q = [(f(e, x), x, None), (i(i(x)), x, None), (f(x, y), f(y, x), None),
         (f(f(x, y), z), f(x, f(y, z)), None), (i(f(x, y)), f(i(x), i(y)), None)]
    act, seen, gj_pruned, dj, cps, pops = [], set(), 0, 0, 0, 0
    while q and pops < 400 and len(act) < 12:
        pops += 1; q.sort(key=lambda it: tsize(it[0]) + tsize(it[1]))
        l, r, top = q.pop(0)
        nl, nr = nf(l, act), nf(r, act)
        if nl == nr: dj += 1; continue
        if use_gj and top is not None and ground_joinable(nl, nr, top, act): gj_pruned += 1; continue
        rule = (nl, nr, True) if kbo_gt(nl, nr) else ((nr, nl, True) if kbo_gt(nr, nl) else (nl, nr, False))
        if (rule[0], rule[1]) in seen or (not rule[2] and (rule[1], rule[0]) in seen): continue
        seen.add((rule[0], rule[1])); act.append(rule); k = len(act)
        for ex in list(act):
            r1, r2 = (ren(rule[0], f"_L{k}"), ren(rule[1], f"_L{k}"), rule[2]), (ren(ex[0], f"_R{k}"), ren(ex[1], f"_R{k}"), ex[2])
            for A, B in ((r1, r2), (r2, r1)):
                for al, ar in ([(A[0], A[1])] if A[2] else [(A[0], A[1]), (A[1], A[0])]):
                    for bl, br in ([(B[0], B[1])] if B[2] else [(B[0], B[1]), (B[1], B[0])]):
                        pos_l = [((), al)] + ([((ix,), a) for ix, a in enumerate(al.args) if isinstance(a, App)] if isinstance(al, App) else [])
                        for pos, sub in pos_l:
                            u = unify(sub, bl, {})
                            if u is not None:
                                pk, lcp = subst(al, u), subst(ar, u)
                                if pos == (): rcp = subst(br, u)
                                else: args = list(pk.args); args[pos[0]] = subst(br, u); rcp = App(pk.fn, tuple(args))
                                if lcp != rcp and tsize(lcp) + tsize(rcp) <= 16:
                                    q.append((lcp, rcp, pk)); cps += 1
    return pops, len(act), cps, dj, gj_pruned, len(q)

for gj in (False, True):
    pops, act, cps, dj, pgj, rem = run_kbc(gj)
    print(f"ground_join={gj}: pops={pops}, active_rules={act}, cps_generated={cps}, direct_joined={dj}, pruned_ground_join={pgj}, queued_remaining={rem}")

@dataclass
class ENode: id: str; op: str; cost: float; ch: tuple[str, ...]
ec = {
    "c_leaf": [ENode("n_x", "x", 10.0, ())],
    "c_a": [ENode("n_a_base", "double", 5.0, ("c_leaf",)), ENode("n_a_cyc", "step_b", 0.5, ("c_b",))],
    "c_b": [ENode("n_b_cyc", "step_a", 0.5, ("c_a",)), ENode("n_b_base", "sq", 4.0, ("c_a",))],
    "c_root": [ENode("n_top_dag", "combine", 1.0, ("c_a", "c_b")), ENode("n_top_alt", "direct", 50.0, ("c_leaf",))],
}
td = {c: math.inf for c in ec}
for _ in ec:
    for c, ns in ec.items():
        for n in ns: td[c] = min(td[c], n.cost + sum(td[k] for k in n.ch))
bn = ba = (math.inf, None)
cns = list(ec)
for combo in itertools.product(*ec.values()):
    sel = dict(zip(cns, combo)); reach, st = set(), ["c_root"]
    while st:
        c = st.pop()
        if c in reach: continue
        reach.add(c); st.extend(sel[c].ch)
    cost = sum(sel[c].cost for c in reach)
    if cost < bn[0]: bn = (cost, {c: sel[c].id for c in reach})
    col, cyc = {}, False
    def dfs(u: str) -> bool:
        col[u] = 1
        found = False
        for v in sel[u].ch:
            if col.get(v) == 1: found = True
            elif col.get(v, 0) == 0 and dfs(v): found = True
        col[u] = 2
        return found
    cyc = dfs("c_root")
    if not cyc and cost < ba[0]: ba = (cost, {c: sel[c].id for c in reach})
print(f"Tree-cost={td['c_root']}, Naive-cyclic={bn}, Acyclic-DAG={ba}")

ins, outs = {0: set(), 1: set(), 2: set()}, {0: set(), 1: set(), 2: set()}
def add_e(u, v): ins[v].add(u); outs[u].add(v)
def rem_e(u, v): ins[v].discard(u); outs[u].discard(v)
add_e(1, 2); add_e(2, 1); add_e(1, 0)
rem_e(1, 2)
for w in list(outs[2]):
    rem_e(2, w)
    if 1 != w: add_e(1, w)
    add_e(1, w)  # circuit.rs:72 duplicate call
for w in list(ins[2]): rem_e(w, 2); add_e(w, 1)
print(f"2-cycle contract_edge_remove_out(1,2): inputs[1]={sorted(ins[1])}, outputs[1]={sorted(outs[1])}, spurious_self_loop={1 in outs[1]}")
EOF
```

## Revalidation

- **Re-run the self-contained Python 3 probe above:** Confirm exit code `0`, `pruned_ground_join=12` (`108` vs. `114` CPs), `Tree-cost=31.5` vs. `Naive-cyclic=2.0` vs. `Acyclic-DAG=16.5`, and `spurious_self_loop=True`.
- **Verify `Twee` completion & `CPF` interoperability:** Execute `twee --formal-proof --tstp` on an AC-monoid benchmark (`nick8325/twee` @ `9f56b26a9b09ea508ff944702b88d60db48c4cb9`) and validate emitted equational proofs via `CeTA` `v3.9` (`ceta --cpf` on TRS termination/confluence `CPF` outputs).
- **Verify `circuit.rs:72` self-loop fix and `extraction-gym` treewidth scaling:** Patch line 72 in `glenn-sun/egg-extraction-gym` (`8be08032d5cbea021ca1d841c103be0afe02644a`) inside `contract_edge_remove_out` (`src/extract/treewidth/circuit.rs`), run `cargo test` and compare `TreewidthExtractor` against `FasterCbcExtractor` across `egraphs-good/extraction-gym/test_data/fuzz/*.json` (`903ba0f818b50608fe20ae9e0f03c35cb27bc50a`) checking `ExtractionResult::check` and wall-clock time vs. treewidth $w$.
- **Verify `egglog` incremental vs. full rebuild crossover:** Run `egraphs-good/egglog` (`d89bc58adc9b9a87a8f571c5b9ad75d686d226e6`) `benches` comparing `TreeExtractor` extraction costs and `SortedWritesTable::do_rebuild` heuristic cutoffs (`MIN_INCREMENTAL_REBUILD_ROWS`, `STEP_SIZE = 2048`).
